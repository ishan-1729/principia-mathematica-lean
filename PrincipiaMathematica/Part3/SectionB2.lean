import PrincipiaMathematica.Defs.Part3

/-!
# Part III, Section B: Addition, multiplication and exponentiation

Volume 2. Numbers: ✱115, ✱116, ✱117.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

/-! ## Helper lemmas (not propositions of PM) -/

section Helpers

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

private theorem null_eq : (Λ : Set α) = ∅ := Null_eq_empty

private theorem pmB2_mem_one {A : Set α} : A ∈ one ↔ ∃ x, A = {x} := Iff.rfl

private theorem pmB2_excl_iff {K : Set (Set α)} :
    K ∈ Cls2excl ↔ ∀ A B x, A ∈ K → B ∈ K → x ∈ A → x ∈ B → A = B := by
  constructor
  · intro h A B x hA hB hxA hxB
    by_contra hne
    have := h A B ⟨⟨hA, hB⟩, hne⟩
    rw [null_eq] at this
    exact (Set.eq_empty_iff_forall_notMem.1 this) x ⟨hxA, hxB⟩
  · intro h A B ⟨⟨hA, hB⟩, hne⟩
    rw [null_eq]
    exact Set.eq_empty_iff_forall_notMem.2 fun x ⟨hxA, hxB⟩ => hne (h A B x hA hB hxA hxB)

private theorem pmB2_mem_sel {P : α → β → Prop} {K : Set β} {R : α → β → Prop} :
    R ∈ sel P K ↔ (∀ x y z, R x z ∧ R y z → x = y) ∧ (∀ x y, R x y → P x y) ∧ codom R = K := by
  rw [mem_sel_iff, mem_arrow_one_Cls]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

private theorem pmB2_sel_ex {P : α → β → Prop} {K : Set β} {R : α → β → Prop} (hR : R ∈ sel P K)
    {y : β} (hy : y ∈ K) : ∃ x, R x y := by
  rw [← (pmB2_mem_sel.1 hR).2.2] at hy; exact hy

private theorem pmB2_sel_codom {P : α → β → Prop} {K : Set β} {R : α → β → Prop} (hR : R ∈ sel P K)
    {x : α} {y : β} (h : R x y) : y ∈ K := by
  rw [← (pmB2_mem_sel.1 hR).2.2]; exact ⟨x, h⟩

/-- The relation of a choice function. -/
private def pmB2_selOf {P : α → β → Prop} {K : Set β} (f : (y : ↥K) → {x // P x y}) : α → β → Prop :=
  fun x y => ∃ h : y ∈ K, x = (f ⟨y, h⟩).1

private theorem pmB2_selOf_mem {P : α → β → Prop} {K : Set β} (f : (y : ↥K) → {x // P x y}) :
    pmB2_selOf f ∈ sel P K := by
  refine pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩
  · rintro x y z ⟨⟨h1, rfl⟩, ⟨h2, rfl⟩⟩; rfl
  · rintro x y ⟨h, rfl⟩; exact (f ⟨y, h⟩).2
  · ext y; exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

/-- Selections are choice functions: `P_Δ'κ` is equivalent to `Π y : κ, {x // P x y}`. -/
private noncomputable def pmB2_selEquiv (P : α → β → Prop) (K : Set β) :
    ↥(sel P K) ≃ ((y : ↥K) → {x // P x y}) where
  toFun R y := ⟨Classical.choose (pmB2_sel_ex R.2 y.2),
    (pmB2_mem_sel.1 R.2).2.1 _ _ (Classical.choose_spec (pmB2_sel_ex R.2 y.2))⟩
  invFun f := ⟨pmB2_selOf f, pmB2_selOf_mem f⟩
  left_inv R := by
    apply Subtype.ext
    funext x y
    apply propext
    constructor
    · rintro ⟨h, rfl⟩
      exact Classical.choose_spec (pmB2_sel_ex R.2 h)
    · intro hxy
      have h : y ∈ K := pmB2_sel_codom R.2 hxy
      exact ⟨h, (pmB2_mem_sel.1 R.2).1 _ _ _ ⟨hxy, Classical.choose_spec (pmB2_sel_ex R.2 h)⟩⟩
  right_inv f := by
    funext y
    apply Subtype.ext
    obtain ⟨h, e⟩ := Classical.choose_spec (pmB2_sel_ex (pmB2_selOf_mem f) y.2)
    exact e

private theorem pmB2_sel_one_one {K : Set (Set α)} (hK : K ∈ Cls2excl) {R : α → Set α → Prop}
    (hR : R ∈ sel memRel K) : R ∈ arrow one one := by
  obtain ⟨h1, h2, h3⟩ := pmB2_mem_sel.1 hR
  refine mem_arrow_one_one.2 ⟨h1, ?_⟩
  rintro x A B ⟨hA, hB⟩
  exact pmB2_excl_iff.1 hK A B x (pmB2_sel_codom hR hA) (pmB2_sel_codom hR hB) (h2 _ _ hA)
    (h2 _ _ hB)

private theorem pmB2_mem_prodK {K : Set (Set α)} {X : Set α} :
    X ∈ prodK K ↔ ∃ R, R ∈ sel memRel K ∧ X = dom R := Iff.rfl

/-- General form of ✱115·101 (helper). -/
private theorem pmB2_mem_prodK_of {K : Set (Set α)} {X : Set α}
    (h1 : ∀ A, A ∈ K → X ∩ A ∈ one) (h2 : X ⊆ sumCls K) : X ∈ prodK K := by
  refine ⟨fun z A => A ∈ K ∧ z ∈ X ∩ A, pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro x y A ⟨⟨hA, hx⟩, ⟨-, hy⟩⟩
    obtain ⟨c, hc⟩ := h1 A hA
    have e1 : x ∈ ι c := by rw [← hc]; exact hx
    have e2 : y ∈ ι c := by rw [← hc]; exact hy
    exact (mem_unitCls.1 e1).trans (mem_unitCls.1 e2).symm
  · rintro x A ⟨-, -, h⟩; exact h
  · ext A
    constructor
    · rintro ⟨x, hA, -⟩; exact hA
    · intro hA
      obtain ⟨c, hc⟩ := h1 A hA
      exact ⟨c, hA, hc ▸ rfl⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨A, hA, hzA⟩ := h2 hz
      exact ⟨A, hA, hz, hzA⟩
    · rintro ⟨A, -, hz, -⟩; exact hz

private theorem pmB2_dom_sel_sub {K : Set (Set α)} {R : α → Set α → Prop} (hR : R ∈ sel memRel K) :
    dom R ⊆ sumCls K := by
  rintro z ⟨A, hzA⟩
  exact ⟨A, pmB2_sel_codom hR hzA, (pmB2_mem_sel.1 hR).2.1 _ _ hzA⟩

/-- Helper form of ✱115·11 (`κ ∈ Cls² excl`). -/
private theorem pmB2_mem_prodK_excl {K : Set (Set α)} (hK : K ∈ Cls2excl) {X : Set α} :
    X ∈ prodK K ↔ (∀ A, A ∈ K → X ∩ A ∈ one) ∧ X ⊆ sumCls K := by
  refine ⟨?_, fun ⟨h1, h2⟩ => pmB2_mem_prodK_of h1 h2⟩
  rintro ⟨R, hR, rfl⟩
  refine ⟨fun A hA => ?_, pmB2_dom_sel_sub hR⟩
  obtain ⟨x, hx⟩ := pmB2_sel_ex hR hA
  refine ⟨x, Set.ext fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨B, hzB⟩, hzA⟩
    have hB := pmB2_sel_codom hR hzB
    have e : B = A := pmB2_excl_iff.1 hK B A z hB hA ((pmB2_mem_sel.1 hR).2.1 _ _ hzB) hzA
    subst e
    exact (pmB2_mem_sel.1 hR).1 _ _ _ ⟨hzB, hx⟩
  · rintro rfl; exact ⟨⟨A, hx⟩, (pmB2_mem_sel.1 hR).2.1 _ _ hx⟩

private theorem pmB2_sel_dom_inj {K : Set (Set α)} (hK : K ∈ Cls2excl) {R S : α → Set α → Prop}
    (hR : R ∈ sel memRel K) (hS : S ∈ sel memRel K) (h : dom R = dom S) : R = S := by
  have key : ∀ R S : α → Set α → Prop, R ∈ sel memRel K → S ∈ sel memRel K → dom R = dom S →
      ∀ x A, R x A → S x A := by
    intro R S hR hS h x A hxA
    have hx : x ∈ dom S := h ▸ ⟨A, hxA⟩
    obtain ⟨B, hxB⟩ := hx
    have e : B = A := pmB2_excl_iff.1 hK B A x (pmB2_sel_codom hS hxB) (pmB2_sel_codom hR hxA)
      ((pmB2_mem_sel.1 hS).2.1 _ _ hxB) ((pmB2_mem_sel.1 hR).2.1 _ _ hxA)
    exact e ▸ hxB
  funext x A
  exact propext ⟨key R S hR hS h x A, key S R hS hR h.symm x A⟩

/-- For `κ ∈ Cls² excl`, `Prod'κ` is equivalent to `∈_Δ'κ` (✱115·12). -/
private noncomputable def pmB2_prodEquiv {K : Set (Set α)} (hK : K ∈ Cls2excl) :
    ↥(prodK K) ≃ ↥(sel memRel K) :=
  (Equiv.ofBijective (fun R : ↥(sel memRel K) => (⟨dom R.1, R.1, R.2, rfl⟩ : ↥(prodK K)))
    ⟨fun R S h => Subtype.ext (pmB2_sel_dom_inj hK R.2 S.2 (congrArg Subtype.val h)),
      fun ⟨_, R, hR, e⟩ => ⟨⟨R, hR⟩, Subtype.ext e.symm⟩⟩).symm

private theorem pmB2_sm_of_equiv {A : Set α} {B : Set β} (e : A ≃ B) : sm A B :=
  sm_iff_nonempty_equiv.2 ⟨e⟩

private theorem pmB2_img_graph (f : β → α) (B : Set β) : graph f ʻʻ B = f '' B := by
  ext x; exact ⟨fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩, fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩⟩

/-- Reindexing a product over an injective image. -/
private noncomputable def pmB2_piImage {X Y : Type*} (f : X → Y) (S : Set X) (hf : Set.InjOn f S)
    (G : Y → Type*) : ((y : ↥(f '' S)) → G y) ≃ ((x : ↥S) → G (f x)) :=
  (Equiv.piCongrLeft (fun y : ↥(f '' S) => G y) (Equiv.Set.imageOfInjOn f S hf)).symm

/-- The members of a class of exclusive classes form a disjoint union. -/
private noncomputable def pmB2_sumClsEquiv {K : Set (Set α)} (hK : K ∈ Cls2excl) :
    ↥(sumCls K) ≃ (Σ A : ↥K, ↥(A : Set α)) :=
  (Equiv.ofBijective (fun p : (Σ A : ↥K, ↥(A : Set α)) => (⟨p.2.1, p.1.1, p.1.2, p.2.2⟩ :
      ↥(sumCls K)))
    ⟨fun ⟨⟨A, hA⟩, ⟨x, hx⟩⟩ ⟨⟨B, hB⟩, ⟨y, hy⟩⟩ h => by
      have h' : x = y := congrArg Subtype.val h
      subst h'
      have e : A = B := pmB2_excl_iff.1 hK A B x hA hB hx hy
      subst e
      rfl,
    fun ⟨x, A, hA, hx⟩ => ⟨⟨⟨A, hA⟩, ⟨x, hx⟩⟩, rfl⟩⟩).symm

end Helpers

section Helpers2

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

private theorem pmB2_mem_clsTimes {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ∈ B ×ₐ A ↔ ∃ x y, (x ∈ A ∧ y ∈ B) ∧ R = x ↓ y := by
  constructor
  · rintro ⟨S, ⟨y, hy, hS⟩, hRS⟩
    have hS' : S = opImg couple A y := hS
    rw [hS'] at hRS
    obtain ⟨x, hx, hR⟩ := hRS
    exact ⟨x, y, ⟨hx, hy⟩, hR⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    exact couple_mem_clsTimes.2 ⟨hx, hy⟩

/-- `β × α` is equivalent to `α × β` (Lean's product type). -/
private noncomputable def pmB2_clsTimesEquiv (A : Set α) (B : Set β) : ↥(B ×ₐ A) ≃ (↥A × ↥B) :=
  (Equiv.ofBijective (fun p : ↥A × ↥B => (⟨p.1.1 ↓ p.2.1,
      couple_mem_clsTimes.2 ⟨p.1.2, p.2.2⟩⟩ : ↥(B ×ₐ A)))
    ⟨fun p q h => by
      have h' := couple_eq_couple_iff.1 (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext h'.1) (Subtype.ext h'.2),
    fun ⟨R, hR⟩ => by
      obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := pmB2_mem_clsTimes.1 hR
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩⟩).symm

private theorem pmB2_fld_couple (x y : α) : fld (x ↓ y) = {x, y} := by
  ext z
  simp only [fld, couple_apply, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, ⟨h, -⟩ | ⟨-, h⟩⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨y, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨x, Or.inr ⟨rfl, h⟩⟩

private theorem pmB2_sm_empty {S : Set α} {T : Set β} (hS : S = ∅) (hT : T = ∅) : sm S T := by
  subst hS; subst hT
  exact sm_iff_nonempty_equiv.2 ⟨Equiv.equivOfIsEmpty _ _⟩

private theorem pmB2_sel_empty_of {K : Set (Set α)} (h : (∅ : Set α) ∈ K) : sel memRel K = ∅ := by
  ext R
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hR
  obtain ⟨x, hx⟩ := pmB2_sel_ex hR h
  exact (pmB2_mem_sel.1 hR).2.1 _ _ hx

private theorem pmB2_prodK_empty_of {K : Set (Set α)} (h : (∅ : Set α) ∈ K) : prodK K = ∅ := by
  ext X
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨R, hR, -⟩
  rw [pmB2_sel_empty_of h] at hR
  exact hR

/-- With choice: a class of non-empty classes has a selection. -/
private theorem pmB2_sel_nonempty {K : Set (Set α)} (h : ∀ A, A ∈ K → A.Nonempty) :
    (sel memRel K).Nonempty :=
  ⟨_, pmB2_selOf_mem (P := memRel) (K := K) fun A => ⟨(h A.1 A.2).some, (h A.1 A.2).some_mem⟩⟩

private theorem pmB2_sel_nonempty_iff {K : Set (Set α)} :
    (sel memRel K).Nonempty ↔ (∅ : Set α) ∉ K := by
  constructor
  · rintro ⟨R, hR⟩ h
    rw [pmB2_sel_empty_of h] at hR; exact hR
  · intro h
    exact pmB2_sel_nonempty fun A hA => Set.nonempty_iff_ne_empty.2 fun e => h (e ▸ hA)

private theorem pmB2_prodK_nonempty_iff {K : Set (Set α)} :
    (prodK K).Nonempty ↔ (sel memRel K).Nonempty :=
  ⟨fun ⟨_, R, hR, _⟩ => ⟨R, hR⟩, fun ⟨R, hR⟩ => ⟨_, R, hR, rfl⟩⟩

private theorem pmB2_excl_subset {K L : Set (Set α)} (hK : K ∈ Cls2excl) (h : L ⊆ K) : L ∈ Cls2excl :=
  pmB2_excl_iff.2 fun A B x hA hB => pmB2_excl_iff.1 hK A B x (h hA) (h hB)

private theorem pmB2_excl_iff' {K : Set (Set α)} :
    K ∈ Cls2excl ↔ ∀ A B, (A ∈ K ∧ B ∈ K) ∧ (A ∩ B).Nonempty → A = B := by
  rw [pmB2_excl_iff]
  exact ⟨fun h A B ⟨⟨hA, hB⟩, x, hxA, hxB⟩ => h A B x hA hB hxA hxB,
    fun h A B x hA hB hxA hxB => h A B ⟨⟨hA, hB⟩, x, hxA, hxB⟩⟩

private theorem pmB2_selRel_img_excl (K : Set (Set (Set α))) :
    selRel memRel ʻʻ K ∈ Cls2excl := by
  rw [pmB2_excl_iff]
  rintro Q Q' R ⟨A, hA, hQ⟩ ⟨B, hB, hQ'⟩ hRQ hRQ'
  have e1 : Q = sel memRel A := hQ
  have e2 : Q' = sel memRel B := hQ'
  rw [e1] at hRQ ⊢; rw [e2] at hRQ' ⊢
  rw [← (pmB2_mem_sel.1 hRQ).2.2, ← (pmB2_mem_sel.1 hRQ').2.2]

private theorem pmB2_mem_selRel_img {K : Set (Set (Set α))} {Q : Set (α → Set α → Prop)} :
    Q ∈ selRel memRel ʻʻ K ↔ ∃ A, A ∈ K ∧ Q = sel memRel A := Iff.rfl

private theorem pmB2_mem_ProdK_img {K : Set (Set (Set α))} {P : Set (Set α)} :
    P ∈ ProdK ʻʻ K ↔ ∃ A, A ∈ K ∧ P = prodK A := Iff.rfl

private theorem pmB2_mem_sumCls_img {K : Set (Set (Set α))} {P : Set α} :
    P ∈ graph sumCls ʻʻ K ↔ ∃ A, A ∈ K ∧ P = sumCls A := Iff.rfl

private theorem pmB2_mem_imgRel_img {T : α → β → Prop} {L : Set (Set β)} {X : Set α} :
    X ∈ imgRel T ʻʻ L ↔ ∃ B, B ∈ L ∧ X = T ʻʻ B := Iff.rfl

end Helpers2

section Exp

private theorem pmB2_coupleImg_excl {α β : Type*} (A : Set α) (B : Set β) :
    coupleImg A ʻʻ B ∈ Cls2excl := by
  rw [pmB2_excl_iff]
  rintro Y Y' R ⟨y, hy, hY⟩ ⟨y', hy', hY'⟩ hR hR'
  have e1 : Y = opImg couple A y := hY
  have e2 : Y' = opImg couple A y' := hY'
  subst e1; subst e2
  obtain ⟨x, hx, rfl⟩ := hR
  obtain ⟨x', hx', e⟩ := hR'
  rw [(couple_eq_couple_iff.1 e).2]

private theorem pmB2_mem_clsExp {α β : Type*} {A : Set α} {B : Set β} {ξ : Set (α → β → Prop)} :
    ξ ∈ clsExp A B ↔ (∀ y, y ∈ B → A ∩ {x | x ↓ y ∈ ξ} ∈ one) ∧ ξ ⊆ B ×ₐ A := by
  rw [show clsExp A B = prodK (coupleImg A ʻʻ B) from rfl,
    pmB2_mem_prodK_excl (pmB2_coupleImg_excl A B)]
  refine and_congr ⟨fun h y hy => ?_, fun h Y hY => ?_⟩ Iff.rfl
  · obtain ⟨c, hc⟩ := h _ ⟨y, hy, rfl⟩
    have hcm : c ∈ ξ ∩ opImg couple A y := by rw [hc]; rfl
    obtain ⟨x₀, hx₀, hcx⟩ := hcm.2
    have hcx' : c = x₀ ↓ y := hcx
    subst hcx'
    refine ⟨x₀, Set.ext fun x => ⟨fun ⟨hx, hxξ⟩ => ?_, fun e => ?_⟩⟩
    · have : x ↓ y ∈ ξ ∩ opImg couple A y := ⟨hxξ, x, hx, rfl⟩
      rw [hc, mem_unitCls] at this
      exact (couple_eq_couple_iff.1 this).1
    · rw [mem_unitCls] at e; subst e; exact ⟨hx₀, hcm.1⟩
  · obtain ⟨y, hy, hY⟩ := hY
    have hY' : Y = opImg couple A y := hY
    subst hY'
    obtain ⟨x₀, hx₀⟩ := h y hy
    have hm : x₀ ∈ A ∩ {x | x ↓ y ∈ ξ} := by rw [hx₀]; rfl
    refine ⟨x₀ ↓ y, Set.ext fun R => ⟨fun ⟨hRξ, x, hx, hR⟩ => ?_, fun e => ?_⟩⟩
    · have hR' : R = x ↓ y := hR
      subst hR'
      have : x ∈ A ∩ {x | x ↓ y ∈ ξ} := ⟨hx, hRξ⟩
      rw [hx₀, mem_unitCls] at this
      rw [this]; rfl
    · rw [mem_unitCls] at e; subst e; exact ⟨hm.2, x₀, hm.1, rfl⟩

/-- `α exp β` is the class of functions from `β` to `α`. -/
private noncomputable def pmB2_clsExpEquiv {α β : Type*} (A : Set α) (B : Set β) :
    ↥(clsExp A B) ≃ (↥B → ↥A) := by
  let Φ : (↥B → ↥A) → Set (α → β → Prop) := fun f => {R | ∃ y : ↥B, R = (f y).1 ↓ y.1}
  have hb : Set.BijOn Φ Set.univ (clsExp A B) := by
    refine ⟨fun f _ => pmB2_mem_clsExp.2 ⟨fun y hy => ⟨(f ⟨y, hy⟩).1, Set.ext fun x =>
      ⟨fun ⟨_, y', e⟩ => ?_, fun e => ?_⟩⟩, ?_⟩, fun f _ g _ e => ?_, fun ξ hξ => ?_⟩
    · obtain ⟨rfl, e2⟩ := couple_eq_couple_iff.1 e
      have : (⟨y, hy⟩ : ↥B) = y' := Subtype.ext e2
      subst this; rfl
    · rw [mem_unitCls] at e; subst e; exact ⟨(f ⟨y, hy⟩).2, ⟨y, hy⟩, rfl⟩
    · rintro R ⟨y, rfl⟩; exact couple_mem_clsTimes.2 ⟨(f y).2, y.2⟩
    · funext y
      have : (f y).1 ↓ y.1 ∈ Φ g := e ▸ ⟨y, rfl⟩
      obtain ⟨y', e'⟩ := this
      obtain ⟨e1, e2⟩ := couple_eq_couple_iff.1 e'
      have : y = y' := Subtype.ext e2
      subst this
      exact Subtype.ext e1
    · obtain ⟨h1, h2⟩ := pmB2_mem_clsExp.1 hξ
      choose g hg using fun y : ↥B => h1 y.1 y.2
      have hgm : ∀ y : ↥B, g y ∈ A ∩ {x | x ↓ y.1 ∈ ξ} := fun y => by rw [hg y]; rfl
      refine ⟨fun y => ⟨g y, (hgm y).1⟩, Set.mem_univ _, Set.ext fun R => ⟨?_, fun hR => ?_⟩⟩
      · rintro ⟨y, rfl⟩; exact (hgm y).2
      · obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := pmB2_mem_clsTimes.1 (h2 hR)
        have : x ∈ A ∩ {x | x ↓ y ∈ ξ} := ⟨hx, hR⟩
        rw [hg ⟨y, hy⟩, mem_unitCls] at this
        exact ⟨⟨y, hy⟩, by rw [this]⟩
  exact ((Equiv.Set.univ _).symm.trans (Set.BijOn.equiv Φ hb)).symm

private theorem pmB2_sm_clsExp {α β γ δ : Type*} {A : Set α} {B : Set β} {A' : Set γ} {B' : Set δ}
    (hA : sm A A') (hB : sm B B') : sm (clsExp A B) (clsExp A' B') := by
  obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 hA
  obtain ⟨eB⟩ := sm_iff_nonempty_equiv.1 hB
  exact pmB2_sm_of_equiv ((pmB2_clsExpEquiv A B).trans ((Equiv.arrowCongr eB eA).trans
    (pmB2_clsExpEquiv A' B').symm))

private theorem pmB2_sm_clsTimes {α β γ δ : Type*} {A : Set α} {B : Set β} {A' : Set γ} {B' : Set δ}
    (hA : sm A A') (hB : sm B B') : sm (A ×ₐ B) (A' ×ₐ B') := by
  obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 hA
  obtain ⟨eB⟩ := sm_iff_nonempty_equiv.1 hB
  exact pmB2_sm_of_equiv ((pmB2_clsTimesEquiv B A).trans ((Equiv.prodCongr eB eA).trans
    (pmB2_clsTimesEquiv B' A').symm))

private theorem pmB2_of_mem_n₀c {α : Type*} {A A' : Set α} (h : n₀c A' = n₀c A) : sm A A' :=
  mem_n₀c.1 (h ▸ self_mem_n₀c A)

/-- `N₀c'α ^ N₀c'β = Nc'(α exp β)` (✱116·222), in any type. -/
private theorem pmB2_n₀c_exp {α β γ : Type*} (A : Set α) (B : Set β) :
    (n₀c A ^ᶜ n₀c B : Set (Set γ)) = nc γ (clsExp A B) := by
  ext ξ
  constructor
  · rintro ⟨A', B', ⟨hA, hB⟩, h⟩
    exact sm_trans h (pmB2_sm_clsExp (pmB2_of_mem_n₀c hA) (pmB2_of_mem_n₀c hB))
  · intro h
    exact ⟨A, B, ⟨rfl, rfl⟩, h⟩

/-- `N₀c'α ×_c N₀c'β = Nc'(α × β)` (✱113·25), in any type. -/
private theorem pmB2_n₀c_mul {α β γ : Type*} (A : Set α) (B : Set β) :
    (n₀c A ×ᶜ n₀c B : Set (Set γ)) = nc γ (A ×ₐ B) := by
  ext ξ
  constructor
  · rintro ⟨A', B', ⟨hA, hB⟩, h⟩
    exact sm_trans h (pmB2_sm_clsTimes (pmB2_of_mem_n₀c hA) (pmB2_of_mem_n₀c hB))
  · intro h
    exact ⟨A, B, ⟨rfl, rfl⟩, h⟩

private theorem pmB2_cardExp_empty {α β γ : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (h : ¬(μ ∈ N₀C ∧ ν ∈ N₀C)) : (μ ^ᶜ ν : Set (Set γ)) = ∅ := by
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨hA, hB⟩, -⟩
  exact h ⟨⟨A, hA⟩, ⟨B, hB⟩⟩

private theorem pmB2_cardMul_empty {α β γ : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (h : ¬(μ ∈ N₀C ∧ ν ∈ N₀C)) : (μ ×ᶜ ν : Set (Set γ)) = ∅ := by
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨hA, hB⟩, -⟩
  exact h ⟨⟨A, hA⟩, ⟨B, hB⟩⟩

private theorem pmB2_cardAdd_empty {α β γ : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (h : ¬(μ ∈ N₀C ∧ ν ∈ N₀C)) : (μ +ᶜ ν : Set (Set γ)) = ∅ := by
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨hA, hB⟩, -⟩
  exact h ⟨⟨A, hA⟩, ⟨B, hB⟩⟩

private theorem pmB2_mem_N₀C_of_nonempty {α β γ : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (h : (μ ^ᶜ ν : Set (Set γ)).Nonempty) : μ ∈ N₀C ∧ ν ∈ N₀C := by
  by_contra h'
  rw [pmB2_cardExp_empty h'] at h
  exact Set.not_nonempty_empty h

private theorem pmB2_n₀c_nonempty_ne {α : Type*} {A : Set α} : n₀c A ≠ ∅ := n₀c_ne_empty A

private theorem pmB2_NC_eq_n₀c {α β : Type*} {μ : Set (Set α)} (hμ : μ ∈ NC β) {X : Set α}
    (hX : X ∈ μ) : μ = n₀c X := by
  obtain ⟨C, rfl⟩ := hμ
  exact nc_eq_n₀c_of_mem hX

private theorem pmB2_NC_ne {α β : Type*} {μ : Set (Set α)} (hμ : μ ∈ NC β \ ι Λ) : ∃ X, μ = n₀c X := by
  obtain ⟨hμ, hne⟩ := hμ
  have : μ.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro e; apply hne; rw [e, mem_unitCls, Null_eq_empty]
  obtain ⟨X, hX⟩ := this
  exact ⟨X, pmB2_NC_eq_n₀c hμ hX⟩

private theorem pmB2_nc_eq_zero {α γ : Type*} {S : Set α} (h : S = ∅) : nc γ S = zero := by
  rw [h, zero_eq_n₀c_empty, n₀c_eq_nc]
  ext X
  rw [mem_nc_iff_equiv, mem_nc_iff_equiv]
  exact ⟨fun ⟨e⟩ => ⟨e.trans (Equiv.equivOfIsEmpty _ _)⟩,
    fun ⟨e⟩ => ⟨e.trans (Equiv.equivOfIsEmpty _ _)⟩⟩

private theorem pmB2_nc_eq_one {α γ : Type*} {S : Set α} [Unique ↥S] : nc γ S = one := by
  ext X
  rw [mem_nc_iff_equiv]
  constructor
  · rintro ⟨e⟩
    refine ⟨(e.symm default : γ), Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
    · have : e ⟨z, hz⟩ = default := Subsingleton.elim _ _
      rw [mem_unitCls]
      exact congrArg Subtype.val (e.symm_apply_eq.2 this.symm).symm
    · rw [mem_unitCls.1 hz]; exact (e.symm default).2
  · rintro ⟨x, rfl⟩
    rw [unitCls_eq_singleton]
    exact ⟨Equiv.ofUnique _ _⟩

/-- Adequacy for `μ^ν` (with a non-empty base type) gives every `Nc'(α exp β)` of the
appropriate types. -/
private theorem pmB2_AdeqExp_nc {α β W : Type*} [Nonempty α] {μ : Set (Set α)} {ν : Set (Set β)}
    (h : AdeqExp W μ ν) (A : Set α) (B : Set β) : (nc W (clsExp A B)).Nonempty := by
  rw [AdeqExp, pmB2_n₀c_exp, nc_nonempty_iff, typ₁, typ₁, typ₀_eq_univ, typ₀_eq_univ] at h
  obtain ⟨f, hf⟩ := h
  obtain ⟨a₀⟩ := ‹Nonempty α›
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    let ext : (↥B → ↥A) → (↥(Set.univ : Set β) → ↥(Set.univ : Set α)) := fun g y =>
      if hy : y.1 ∈ B then ⟨(g ⟨y.1, hy⟩).1, trivial⟩ else ⟨a, trivial⟩
    have hext : Function.Injective ext := by
      intro g g' e
      funext y
      have := congrFun e ⟨y.1, trivial⟩
      simp only [ext, y.2, dite_true] at this
      have h2 := congrArg Subtype.val this
      exact Subtype.ext h2
    refine nc_nonempty_iff.2 ⟨fun ξ => f ((pmB2_clsExpEquiv _ _).symm (ext (pmB2_clsExpEquiv A B ξ))),
      ?_⟩
    exact hf.comp ((pmB2_clsExpEquiv _ _).symm.injective.comp
      (hext.comp (pmB2_clsExpEquiv A B).injective))
  · by_cases hB : B.Nonempty
    · have : IsEmpty ↥A := ⟨fun x => hA ⟨x.1, x.2⟩⟩
      exact nc_nonempty_iff.2 ⟨fun ξ => isEmptyElim ((pmB2_clsExpEquiv A B ξ)
        ⟨hB.some, hB.some_mem⟩), fun ξ => isEmptyElim ((pmB2_clsExpEquiv A B ξ)
          ⟨hB.some, hB.some_mem⟩)⟩
    · let g0 : ↥(Set.univ : Set β) → ↥(Set.univ : Set α) := fun _ => ⟨a₀, trivial⟩
      refine nc_nonempty_iff.2 ⟨fun _ => f ((pmB2_clsExpEquiv _ _).symm g0), fun ξ ξ' _ => ?_⟩
      apply (pmB2_clsExpEquiv A B).injective
      funext y
      exact absurd ⟨y.1, y.2⟩ hB

private theorem pmB2_AdeqMul_nc {α β W : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (h : AdeqMul W μ ν) (A : Set α) (B : Set β) : (nc W (A ×ₐ B)).Nonempty := by
  rw [AdeqMul, pmB2_n₀c_mul, nc_nonempty_iff, typ₁, typ₁, typ₀_eq_univ, typ₀_eq_univ] at h
  obtain ⟨f, hf⟩ := h
  have hsub : ∀ R, R ∈ A ×ₐ B → R ∈ (Set.univ : Set α) ×ₐ (Set.univ : Set β) := by
    intro R hR
    obtain ⟨x, y, -, e⟩ := pmB2_mem_clsTimes.1 hR
    rw [e]; exact couple_mem_clsTimes.2 ⟨trivial, trivial⟩
  exact nc_nonempty_iff.2 ⟨fun R => f ⟨R.1, hsub R.1 R.2⟩,
    fun R R' e => by have h2 := congrArg Subtype.val (hf e); exact Subtype.ext h2⟩

private theorem pmB2_n₀c_mem_NC {α : Type*} (A : Set α) : n₀c A ∈ NC α := ⟨A, n₀c_eq_nc A⟩

private theorem pmB2_exp_prod_exp {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} :
    sm (clsExp A (B ×ₐ G)) (clsExp (clsExp A B) G) :=
  pmB2_sm_of_equiv ((pmB2_clsExpEquiv A (B ×ₐ G)).trans ((Equiv.arrowCongr
    (pmB2_clsTimesEquiv G B) (Equiv.refl _)).trans ((Equiv.curry _ _ _).trans
      ((Equiv.arrowCongr (Equiv.refl _) (pmB2_clsExpEquiv A B).symm).trans
        (pmB2_clsExpEquiv (clsExp A B) G).symm))))

private theorem pmB2_exp_mul {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} :
    sm (clsExp A G ×ₐ clsExp B G) (clsExp (A ×ₐ B) G) :=
  pmB2_sm_of_equiv ((pmB2_clsTimesEquiv _ _).trans (((pmB2_clsExpEquiv B G).prodCongr
    (pmB2_clsExpEquiv A G)).trans ((Equiv.arrowProdEquivProdArrow _ _ _).symm.trans
      ((Equiv.arrowCongr (Equiv.refl _) (pmB2_clsTimesEquiv B A).symm).trans
        (pmB2_clsExpEquiv (A ×ₐ B) G).symm))))

end Exp

section Order

/-- `∃!Cl'α ∩ Nc'β` iff `β` injects into `α`. -/
private theorem pmB2_cl_nc_iff {X Y : Type*} {A : Set X} {B : Set Y} :
    (cl A ∩ nc X B).Nonempty ↔ Nonempty (↥B ↪ ↥A) := by
  constructor
  · rintro ⟨ρ, hρA, hρB⟩
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hρB
    exact ⟨⟨fun b => ⟨(e.symm b).1, hρA (e.symm b).2⟩, fun b b' h =>
      e.symm.injective (Subtype.ext (by have := congrArg Subtype.val h; exact this))⟩⟩
  · rintro ⟨f⟩
    refine ⟨Set.range (fun b => (f b).1), fun x ⟨b, hb⟩ => hb ▸ (f b).2, ?_⟩
    exact sm_symm (pmB2_sm_of_equiv (Equiv.ofInjective (fun b => (f b).1)
      (fun b b' h => f.injective (Subtype.ext h))))

private theorem pmB2_emb_congr {X Y X' Y' : Type*} {A : Set X} {B : Set Y} {A' : Set X'} {B' : Set Y'}
    (hA : sm A A') (hB : sm B B') : Nonempty (↥B ↪ ↥A) ↔ Nonempty (↥B' ↪ ↥A') := by
  obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 hA
  obtain ⟨eB⟩ := sm_iff_nonempty_equiv.1 hB
  exact ⟨fun ⟨f⟩ => ⟨(eB.symm.toEmbedding.trans f).trans eA.toEmbedding⟩,
    fun ⟨f⟩ => ⟨(eB.toEmbedding.trans f).trans eA.symm.toEmbedding⟩⟩

private theorem pmB2_gt_n₀c {X Y : Type*} {A : Set X} {B : Set Y} :
    n₀c A >ᶜ n₀c B ↔ Nonempty (↥B ↪ ↥A) ∧ ¬Nonempty (↥A ↪ ↥B) := by
  constructor
  · rintro ⟨A', B', ⟨⟨hA, hB⟩, h1⟩, h2⟩
    have sA := pmB2_of_mem_n₀c hA
    have sB := pmB2_of_mem_n₀c hB
    rw [pmB2_cl_nc_iff] at h1 h2
    exact ⟨(pmB2_emb_congr sA sB).1 h1, fun h => h2 ((pmB2_emb_congr sB sA).2 h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨A, B, ⟨⟨rfl, rfl⟩, pmB2_cl_nc_iff.2 h1⟩, fun h => h2 (pmB2_cl_nc_iff.1 h)⟩

private theorem pmB2_gt_iff {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ >ᶜ ν ↔ ∃ A B, (μ = n₀c A ∧ ν = n₀c B) ∧ (Nonempty (↥B ↪ ↥A) ∧ ¬Nonempty (↥A ↪ ↥B)) := by
  constructor
  · intro h
    obtain ⟨A, B, ⟨⟨rfl, rfl⟩, _⟩, _⟩ := id h
    exact ⟨A, B, ⟨rfl, rfl⟩, pmB2_gt_n₀c.1 h⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    exact pmB2_gt_n₀c.2 h

private theorem pmB2_ge_n₀c {X Y : Type*} {A : Set X} {B : Set Y} :
    n₀c A ≥ᶜ n₀c B ↔ Nonempty (↥B ↪ ↥A) := by
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact (pmB2_gt_n₀c.1 h).1
    · rw [sm_img_n₀c, n₀c_eq_nc] at h
      have hs : sm A B := (nc_eq_nc_iff ⟨A, self_mem_nc A⟩).1 h
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hs
      exact ⟨e.symm.toEmbedding⟩
  · intro h
    by_cases h' : Nonempty (↥A ↪ ↥B)
    · right
      obtain ⟨f⟩ := h
      obtain ⟨g⟩ := h'
      obtain ⟨e⟩ := Function.Embedding.antisymm g f
      refine ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, ?_⟩
      rw [sm_img_n₀c, n₀c_eq_nc]
      exact nc_eq_nc_of_sm (pmB2_sm_of_equiv e)
    · exact Or.inl (pmB2_gt_n₀c.2 ⟨h, h'⟩)

private theorem pmB2_ge_iff {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ ≥ᶜ ν ↔ ∃ A B, (μ = n₀c A ∧ ν = n₀c B) ∧ Nonempty (↥B ↪ ↥A) := by
  constructor
  · intro h
    have hN : μ ∈ N₀C ∧ ν ∈ N₀C := by
      rcases h with ⟨A, B, ⟨⟨hA, hB⟩, -⟩, -⟩ | ⟨h, -⟩
      · exact ⟨⟨A, hA⟩, ⟨B, hB⟩⟩
      · exact h
    obtain ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩ := hN
    exact ⟨A, B, ⟨rfl, rfl⟩, pmB2_ge_n₀c.1 h⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    exact pmB2_ge_n₀c.2 h

private theorem pmB2_ge_N₀C {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} (h : μ ≥ᶜ ν) :
    μ ∈ N₀C ∧ ν ∈ N₀C := by
  obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := pmB2_ge_iff.1 h
  exact ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩

private theorem pmB2_gt_N₀C {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} (h : μ >ᶜ ν) :
    μ ∈ N₀C ∧ ν ∈ N₀C := by
  obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := pmB2_gt_iff.1 h
  exact ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩

private theorem pmB2_nc_n₀c {X W : Type*} {S : Set X} (h : (nc W S).Nonempty) :
    ∃ S' : Set W, nc W S = n₀c S' ∧ sm S' S := by
  obtain ⟨S', hS'⟩ := h
  exact ⟨S', nc_eq_n₀c_of_mem hS', hS'⟩

/-- Comparison of two existent cardinals `Nc'σ`, `Nc'τ` in any types. -/
private theorem pmB2_ge_nc {X Y W W' : Type*} {S : Set X} {S' : Set Y} (h1 : (nc W S).Nonempty)
    (h2 : (nc W' S').Nonempty) : nc W S ≥ᶜ nc W' S' ↔ Nonempty (↥S' ↪ ↥S) := by
  obtain ⟨A, e1, s1⟩ := pmB2_nc_n₀c h1
  obtain ⟨B, e2, s2⟩ := pmB2_nc_n₀c h2
  rw [e1, e2, pmB2_ge_n₀c]
  exact pmB2_emb_congr s1 s2

private theorem pmB2_gt_nc {X Y W W' : Type*} {S : Set X} {S' : Set Y} (h1 : (nc W S).Nonempty)
    (h2 : (nc W' S').Nonempty) :
    nc W S >ᶜ nc W' S' ↔ Nonempty (↥S' ↪ ↥S) ∧ ¬Nonempty (↥S ↪ ↥S') := by
  obtain ⟨A, e1, s1⟩ := pmB2_nc_n₀c h1
  obtain ⟨B, e2, s2⟩ := pmB2_nc_n₀c h2
  rw [e1, e2, pmB2_gt_n₀c, pmB2_emb_congr s1 s2, pmB2_emb_congr s2 s1]

private theorem pmB2_n₀c_nc {X : Type*} (A : Set X) : (nc X A).Nonempty := ⟨A, self_mem_nc A⟩

private theorem pmB2_nc_nonempty_of_inj {X W : Type*} (f : X → W) (hf : Function.Injective f)
    (A : Set X) : (nc W A).Nonempty :=
  nc_nonempty_iff.2 ⟨fun a => f a, hf.comp Subtype.val_injective⟩

private theorem pmB2_AdeqSm_nc {X W : Type*} {μ : Set (Set X)} (h : AdeqSm W μ) (A : Set X) :
    (nc W A).Nonempty := by
  obtain ⟨f, hf⟩ := adeqSm_iff.1 h
  exact pmB2_nc_nonempty_of_inj f hf A

private theorem pmB2_clsSum_emb {X Y X' Y' : Type*} {A : Set X} {B : Set Y} {A' : Set X'} {B' : Set Y'}
    (f : ↥A ↪ ↥A') (g : ↥B ↪ ↥B') : Nonempty (↥(A +ₐ B) ↪ ↥(A' +ₐ B')) :=
  ⟨((clsSumEquiv A B).toEmbedding.trans (Function.Embedding.sumMap f g)).trans
    (clsSumEquiv A' B').symm.toEmbedding⟩

private theorem pmB2_clsTimes_emb {X Y X' Y' : Type*} {A : Set X} {B : Set Y} {A' : Set X'}
    {B' : Set Y'} (f : ↥A ↪ ↥A') (g : ↥B ↪ ↥B') : Nonempty (↥(A ×ₐ B) ↪ ↥(A' ×ₐ B')) :=
  ⟨((pmB2_clsTimesEquiv B A).toEmbedding.trans (Function.Embedding.prodMap g f)).trans
    (pmB2_clsTimesEquiv B' A').symm.toEmbedding⟩

private theorem pmB2_clsExp_emb_base {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z}
    (f : ↥B ↪ ↥A) : Nonempty (↥(clsExp B G) ↪ ↥(clsExp A G)) :=
  ⟨((pmB2_clsExpEquiv B G).toEmbedding.trans (Function.Embedding.arrowCongrRight f)).trans
    (pmB2_clsExpEquiv A G).symm.toEmbedding⟩

private theorem pmB2_clsExp_emb_exp {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z}
    (hG : G.Nonempty) (f : ↥B ↪ ↥A) : Nonempty (↥(clsExp G B) ↪ ↥(clsExp G A)) := by
  have : Inhabited ↥G := ⟨⟨hG.some, hG.some_mem⟩⟩
  exact ⟨((pmB2_clsExpEquiv G B).toEmbedding.trans (Function.Embedding.arrowCongrLeft f)).trans
    (pmB2_clsExpEquiv G A).symm.toEmbedding⟩

/-- In a type adequate for `μ +_c ν`, `μ +_c ν` is `Nc'(α + β)` and exists. -/
private theorem pmB2_add_val {X Y W : Type*} {A : Set X} {B : Set Y} (h : AdeqAdd W (n₀c A) (n₀c B)) :
    (n₀c A +ᶜ n₀c B : Set (Set W)) = nc W (A +ₐ B) ∧ (nc W (A +ₐ B)).Nonempty :=
  ⟨n₀c_cardAdd_n₀c A B, h.nc_nonempty A B⟩

/-- `Σ'κ` is the disjoint union of the members of `κ`. -/
private noncomputable def pmB2_clsSigmaEquiv {X : Type*} (K : Set (Set X)) :
    ↥(clsSigma K) ≃ (Σ A : ↥K, ↥(A : Set X)) := by
  refine (Equiv.ofBijective (fun p : (Σ A : ↥K, ↥(A : Set X)) => (⟨p.2.1 ↓ p.1.1,
    ⟨memRel ↧ p.1.1, ⟨p.1.1, p.1.2, rfl⟩, p.2.1, p.2.2, rfl⟩⟩ : ↥(clsSigma K))) ⟨?_, ?_⟩).symm
  · rintro ⟨⟨A, hA⟩, ⟨x, hx⟩⟩ ⟨⟨B, hB⟩, ⟨y, hy⟩⟩ h
    have h' := couple_eq_couple_iff.1 (congrArg Subtype.val h)
    obtain ⟨rfl, rfl⟩ := h'
    rfl
  · rintro ⟨Q, Y, ⟨A, hA, hY⟩, hQ⟩
    have hY' : Y = memRel ↧ A := hY
    rw [hY'] at hQ
    obtain ⟨x, hx, rfl⟩ := hQ
    exact ⟨⟨⟨A, hA⟩, ⟨x, hx⟩⟩, rfl⟩

end Order


/-!
## [✱115] Multiplicative classes and arithmetical classes

*(Vol. 2, p. 135)*

> *Summary of* *115.
>
> Whenever \(\kappa\) is a class of mutually exclusive classes, \({\in}_{\Delta}ʻ\kappa\) is similar to \(\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa\); hence \[ \Pi \text{Nc}ʻ\kappa = \text{Nc}ʻ\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa . \]
>
> Now \(\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa\) is of the same type as \(\kappa\); and when \(\kappa\) is a class of mutually exclusive classes, \(\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa\) consists of all classes formed by selecting one representative from each member of \(\kappa\). It often happens that \(\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa\) is easier to deal with than \({\in}_{\Delta}ʻ\kappa\); hence when possible (*i.e.* when \(\kappa \in \text{Cls}^{2} \text{excl})\), it is convenient to use \(\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa\), rather than \({\in}_{\Delta}ʻ\kappa\), as the standard member of \(\Pi\text{Nc}ʻ\kappa\). We therefore put \[ \text{Prod}ʻ\kappa = \text{D}ʻʻ{\in}_{\Delta}ʻ\kappa \quad\text{Df}. \]
>
> We shall call \(\text{Prod}ʻ\kappa\) the "multiplicative class" of \(\kappa\).
>
> …

**Lean reading.** `Prod'κ` is `prodK K` (`D''∈_Δ'κ`, relation `ProdK`), `∈_Δ'κ` is `sel memRel K`,
`Cls³ arithm` is `Cls3arithm` (a conjunction of two `Cls² excl` of different types). Images under
PM's constant relations are written with `graph` of their value functions: `s''κ` is `graph sumCls
ʻʻ K`, `ṡ''…` is `graph sumRel ʻʻ …`, `Prod''κ` is `ProdK ʻʻ K`, `D'''λ` is `D ʻʻʻ L`; `sm sm` is
`smsm`, `κ sm̄ sm̄ λ` is `smbar`-style `smsmbar K L`, `T_∈` is `imgRel T`. In ✱115·6–·63 the
hypothesis `(R''γ) ↿ R, S ↾ γ ∈ 1 → 1` is the conjunction of the two relations' one-oneness (as in
the proof of ✱114·64), and `R'z × S'z` contains two descriptions, the first with the larger scope.
The cardinal propositions are proved through the equivalence of `∈_Δ'κ` with the dependent functions
on `κ` (and of `Prod'κ` with `∈_Δ'κ` for exclusive `κ`); the helper lemmas are private.

**Status.** proved (all propositions; ✱115·35 proved (reading), see its docstring).
-/

/-- ✱115·01 (Df). \(\text{Prod}ʻ\kappa =\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa \quad\text{Df}\) -/
theorem pm115_01 {α : Type*} {K : Set (Set α)} : prodK K = D ʻʻ sel memRel K := rfl

/-- ✱115·02 (Df). \(\text{Cls}^{3}\,\text{arithm}=\hat{\kappa} (\kappa ,sʻ\kappa \in \text{Cls}^{2} \text{excl}) \quad\text{Df}\) -/
theorem pm115_02 {α : Type*} :
    (Cls3arithm : Set (Set (Set (Set α)))) = {K | K ∈ Cls2excl ∧ sumCls K ∈ Cls2excl} := rfl

/-- ✱115·1. \(\vdash .\text{Prod}ʻ\kappa =\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa \quad[(*115·01)]\)

PM states the value of the descriptive function `Prod'κ`, so the statement keeps the
description (Basic §5). -/
theorem pm115_1 {α : Type*} {K : Set (Set α)} : Desc ProdK K (fun X => X = D ʻʻ sel memRel K) :=
  (desc_ProdK K _).2 rfl

/-- ✱115·101. \(\vdash \colon\ldotp \alpha \in \kappa .\supset _{\alpha }.\varpi \cap \alpha \in 1:\varpi \subset sʻ\kappa :\supset .\varpi \in \text{Prod}ʻ\kappa \quad[*84·411]\) -/
theorem pm115_101 {α : Type*} {K : Set (Set α)} {ϖ : Set α} :
    (∀ A, A ∈ K → ϖ ∩ A ∈ one) ∧ ϖ ⊆ sumCls K → ϖ ∈ prodK K :=
  fun ⟨h1, h2⟩ => pmB2_mem_prodK_of h1 h2

/-- ✱115·11. \[\begin{align}&\vdash \colon\colon \kappa \in \text{Cls}^{2} \text{excl}.\supset \colon\ldotp \varpi \in \text{Prod}ʻ\kappa .\equiv :\alpha \in \kappa .\supset _{\alpha }.\varpi \cap \alpha \in 1:\varpi \subset sʻ\kappa\\ &[*84·412]\end{align}\] -/
theorem pm115_11 {α : Type*} {K : Set (Set α)} {ϖ : Set α} :
    K ∈ Cls2excl → (ϖ ∈ prodK K ↔ (∀ A, A ∈ K → ϖ ∩ A ∈ one) ∧ ϖ ⊆ sumCls K) :=
  fun hK => pmB2_mem_prodK_excl hK

/-- ✱115·12. \(\vdash : \kappa \in \text{Cls}^{2} \text{excl} . \supset . \text{Prod}ʻ\kappa \in \Pi \text{Nc}ʻ\kappa . \text{Prod}ʻ\kappa \text{ sm } {\in}_{\Delta}ʻ\kappa \quad[*84·41]\)

`ΠNc'κ` is taken in the type of `Prod'κ` (significance: `Prod'κ ∈ ΠNc'κ`). -/
theorem pm115_12 {α : Type*} {K : Set (Set α)} :
    K ∈ Cls2excl → prodK K ∈ piNc (Set α) K ∧ sm (prodK K) (sel memRel K) := fun hK =>
  ⟨pmB2_sm_of_equiv (pmB2_prodEquiv hK), pmB2_sm_of_equiv (pmB2_prodEquiv hK)⟩

private theorem pmB2_prod_pair {α : Type*} {A B : Set α} : A ≠ B → prodK (ι A ∪ ι B) = C ʻʻ (A ×ₐ B) := by
  intro hAB
  ext X
  constructor
  · rintro ⟨R, hR, rfl⟩
    have hA : A ∈ ι A ∪ ι B := Or.inl rfl
    have hB : B ∈ ι A ∪ ι B := Or.inr rfl
    obtain ⟨a, ha⟩ := pmB2_sel_ex hR hA
    obtain ⟨b, hb⟩ := pmB2_sel_ex hR hB
    obtain ⟨h1, h2, -⟩ := pmB2_mem_sel.1 hR
    refine ⟨b ↓ a, couple_mem_clsTimes.2 ⟨h2 _ _ hb, h2 _ _ ha⟩, ?_⟩
    show dom R = fld (b ↓ a)
    rw [pmB2_fld_couple]
    ext z
    constructor
    · rintro ⟨Y, hzY⟩
      rcases pmB2_sel_codom hR hzY with h | h
      · have h' : Y = A := h
        subst h'
        exact Or.inr (h1 _ _ _ ⟨hzY, ha⟩)
      · have h' : Y = B := h
        subst h'
        exact Or.inl (h1 _ _ _ ⟨hzY, hb⟩)
    · rintro (rfl | rfl)
      · exact ⟨B, hb⟩
      · exact ⟨A, ha⟩
  · rintro ⟨Q, hQ, hXQ⟩
    have hX : X = fld Q := hXQ
    obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := pmB2_mem_clsTimes.1 hQ
    rw [pmB2_fld_couple] at hX
    subst hX
    refine ⟨fun z Y => (Y = A ∧ z = y) ∨ (Y = B ∧ z = x), pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩, ?_⟩
    · rintro u v Y ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), (⟨h, rfl⟩ | ⟨h, rfl⟩)⟩
      · rfl
      · exact absurd h hAB
      · exact absurd h.symm hAB
      · rfl
    · rintro z Y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hy
      · exact hx
    · ext Y
      constructor
      · rintro ⟨z, (⟨rfl, -⟩ | ⟨rfl, -⟩)⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (h | h)
        · exact ⟨y, Or.inl ⟨h, rfl⟩⟩
        · exact ⟨x, Or.inr ⟨h, rfl⟩⟩
    · ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, dom, Set.mem_ofPred_eq]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨B, Or.inr ⟨rfl, rfl⟩⟩
        · exact ⟨A, Or.inl ⟨rfl, rfl⟩⟩
      · rintro ⟨Y, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩
        · exact Or.inr rfl
        · exact Or.inl rfl

/-- ✱115·13. \(\vdash : \alpha \cap \beta = \Lambda . \supset . \text{Prod}ʻ(\iota ʻ\alpha \cup \iota ʻ\beta ) \text{ sm } (\alpha \times \beta ) \quad[*113·152]\) -/
theorem pm115_13 {α : Type*} {A B : Set α} : A ∩ B = Λ → sm (prodK (ι A ∪ ι B)) (A ×ₐ B) := by
  intro h
  rw [Null_eq_empty] at h
  by_cases hAB : A = B
  · subst hAB
    rw [Set.inter_self] at h
    subst h
    refine pmB2_sm_empty (pmB2_prodK_empty_of (Or.inl rfl)) ?_
    ext R
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hR
    obtain ⟨x, y, ⟨hx, -⟩, -⟩ := pmB2_mem_clsTimes.1 hR
    exact hx
  · rw [pmB2_prod_pair hAB]
    show sm (graph fld ʻʻ (A ×ₐ B)) _
    rw [pmB2_img_graph]
    refine sm_symm (pmB2_sm_of_equiv (Equiv.Set.imageOfInjOn fld _ ?_))
    intro R hR R' hR' e
    obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := pmB2_mem_clsTimes.1 hR
    obtain ⟨x', y', ⟨hx', hy'⟩, rfl⟩ := pmB2_mem_clsTimes.1 hR'
    have e' : ({x, y} : Set α) = {x', y'} := by
      rw [← pmB2_fld_couple, ← pmB2_fld_couple]; exact e
    have hdis : ∀ u v, u ∈ B → v ∈ A → u ≠ v := fun u v hu hv huv =>
      (Set.eq_empty_iff_forall_notMem.1 h) u ⟨huv ▸ hv, hu⟩
    have hxm : x ∈ ({x', y'} : Set α) := e' ▸ Or.inl rfl
    have hym : y ∈ ({x', y'} : Set α) := e' ▸ Or.inr rfl
    rcases hxm with hxx | hxy
    · rcases hym with hyx | hyy
      · exact absurd (hyx.trans hxx.symm) (hdis x y hx hy).symm
      · rw [hxx, hyy]
    · exact absurd hxy (hdis x y' hx hy')

/-- ✱115·131. \(\vdash : \alpha \neq \beta . \supset . \text{Prod}ʻ(\iota ʻ\alpha \cup \iota ʻ\beta ) = Cʻʻ(\alpha \times \beta ) \quad[*113·151]\)

`C''(α × β)` is `C ʻʻ (A ×ₐ B)`; `C'R` is `fld R`. -/
theorem pm115_131 {α : Type*} {A B : Set α} : A ≠ B → prodK (ι A ∪ ι B) = C ʻʻ (A ×ₐ B) :=
  pmB2_prod_pair

private theorem pmB2_prodK_union {α : Type*} {K L : Set (Set α)} (h : K ∩ L = ∅) {ϖ : Set α} :
    ϖ ∈ prodK (K ∪ L) ↔ ∃ ρ σ, (ρ ∈ prodK K ∧ σ ∈ prodK L) ∧ ϖ = ρ ∪ σ := by
  have hdis : ∀ A, A ∈ K → A ∈ L → False := fun A hK hL =>
    (Set.eq_empty_iff_forall_notMem.1 h) A ⟨hK, hL⟩
  constructor
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨h1, h2, h3⟩ := pmB2_mem_sel.1 hR
    have hres : ∀ M : Set (Set α), M ⊆ K ∪ L → R ↾ M ∈ sel memRel M := fun M hM =>
      pmB2_mem_sel.2 ⟨fun x y z ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => h1 x y z ⟨hx, hy⟩,
        fun x y ⟨hxy, _⟩ => h2 x y hxy, Set.ext fun A => ⟨fun ⟨_, _, hA⟩ => hA,
          fun hA => by
            obtain ⟨x, hx⟩ := pmB2_sel_ex hR (hM hA)
            exact ⟨x, hx, hA⟩⟩⟩
    refine ⟨dom (R ↾ K), dom (R ↾ L), ⟨⟨_, hres K Set.subset_union_left, rfl⟩,
      ⟨_, hres L Set.subset_union_right, rfl⟩⟩, ?_⟩
    ext z
    constructor
    · rintro ⟨A, hzA⟩
      rcases pmB2_sel_codom hR hzA with hA | hA
      · exact Or.inl ⟨A, hzA, hA⟩
      · exact Or.inr ⟨A, hzA, hA⟩
    · rintro (⟨A, hzA, -⟩ | ⟨A, hzA, -⟩) <;> exact ⟨A, hzA⟩
  · rintro ⟨ρ, σ, ⟨⟨R, hR, rfl⟩, ⟨S, hS, rfl⟩⟩, rfl⟩
    refine ⟨R ⊍ S, pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩, ?_⟩
    · rintro x y A ⟨hx | hx, hy | hy⟩
      · exact (pmB2_mem_sel.1 hR).1 x y A ⟨hx, hy⟩
      · exact (hdis A (pmB2_sel_codom hR hx) (pmB2_sel_codom hS hy)).elim
      · exact (hdis A (pmB2_sel_codom hR hy) (pmB2_sel_codom hS hx)).elim
      · exact (pmB2_mem_sel.1 hS).1 x y A ⟨hx, hy⟩
    · rintro x A (hx | hx)
      · exact (pmB2_mem_sel.1 hR).2.1 x A hx
      · exact (pmB2_mem_sel.1 hS).2.1 x A hx
    · ext A
      constructor
      · rintro ⟨x, hx | hx⟩
        · exact Or.inl (pmB2_sel_codom hR hx)
        · exact Or.inr (pmB2_sel_codom hS hx)
      · rintro (hA | hA)
        · obtain ⟨x, hx⟩ := pmB2_sel_ex hR hA; exact ⟨x, Or.inl hx⟩
        · obtain ⟨x, hx⟩ := pmB2_sel_ex hS hA; exact ⟨x, Or.inr hx⟩
    · ext z
      constructor
      · rintro (⟨A, hz⟩ | ⟨A, hz⟩)
        · exact ⟨A, Or.inl hz⟩
        · exact ⟨A, Or.inr hz⟩
      · rintro ⟨A, hz | hz⟩
        · exact Or.inl ⟨A, hz⟩
        · exact Or.inr ⟨A, hz⟩

/-- ✱115·14. \[\begin{align}\vdash \colon\ldotp &\kappa \cap \lambda = \Lambda . \lor . sʻ\kappa \cap sʻ\lambda = \Lambda : \supset :\\ &\varpi \in \text{Prod}ʻ(\kappa \cup \lambda ) . \equiv . (\exists \rho , \sigma ) . \rho \in \text{Prod}ʻ\kappa . \sigma \in \text{Prod}ʻ\lambda . \varpi = \rho \cup \sigma\\ &[*83·64·641]\end{align}\]

`ρ, σ` are classes of the type of the members of `κ`, `λ`. -/
theorem pm115_14 {α : Type*} {K L : Set (Set α)} {ϖ : Set α} :
    K ∩ L = Λ ∨ sumCls K ∩ sumCls L = Λ →
      (ϖ ∈ prodK (K ∪ L) ↔ ∃ ρ σ, (ρ ∈ prodK K ∧ σ ∈ prodK L) ∧ ϖ = ρ ∪ σ) := by
  intro h
  rw [Null_eq_empty, Null_eq_empty] at h
  by_cases hKL : K ∩ L = ∅
  · exact pmB2_prodK_union hKL
  · have h2 : sumCls K ∩ sumCls L = ∅ := h.resolve_left hKL
    obtain ⟨A, hAK, hAL⟩ := Set.nonempty_iff_ne_empty.2 hKL
    have hA : A = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx =>
      (Set.eq_empty_iff_forall_notMem.1 h2) x ⟨⟨A, hAK, hx⟩, ⟨A, hAL, hx⟩⟩
    subst hA
    rw [pmB2_prodK_empty_of (Or.inl hAK), pmB2_prodK_empty_of hAK]
    simp

/-- ✱115·141. \(\vdash : \exists ! \text{Prod}ʻ\kappa . \supset . sʻ\text{Prod}ʻ\kappa = sʻ\kappa \quad[*83·66]\) -/
theorem pm115_141 {α : Type*} {K : Set (Set α)} :
    (prodK K).Nonempty → sumCls (prodK K) = sumCls K := by
  rintro ⟨_, R₀, hR₀, -⟩
  ext x
  constructor
  · rintro ⟨X, ⟨R, hR, rfl⟩, hx⟩
    exact pmB2_dom_sel_sub hR hx
  · rintro ⟨A, hA, hxA⟩
    classical
    refine ⟨dom (fun z B => (B = A ∧ z = x) ∨ (B ≠ A ∧ R₀ z B)), ⟨_, pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩,
      rfl⟩, ⟨A, Or.inl ⟨rfl, rfl⟩⟩⟩
    · rintro u v B ⟨(⟨e1, hu⟩ | ⟨hB, hu⟩), (⟨e2, hv⟩ | ⟨hB', hv⟩)⟩
      · rw [hu, hv]
      · exact absurd e1 hB'
      · exact absurd e2 hB
      · exact (pmB2_mem_sel.1 hR₀).1 u v B ⟨hu, hv⟩
    · rintro z B (⟨rfl, rfl⟩ | ⟨-, hz⟩)
      · exact hxA
      · exact (pmB2_mem_sel.1 hR₀).2.1 z B hz
    · ext B
      constructor
      · rintro ⟨z, ⟨rfl, -⟩ | ⟨-, hz⟩⟩
        · exact hA
        · exact pmB2_sel_codom hR₀ hz
      · intro hB
        by_cases e : B = A
        · exact ⟨x, Or.inl ⟨e, rfl⟩⟩
        · obtain ⟨z, hz⟩ := pmB2_sel_ex hR₀ hB
          exact ⟨z, Or.inr ⟨e, hz⟩⟩

/-- ✱115·142. \(\vdash . \text{Prod}ʻ\iota ʻ\alpha = \iotaʻʻ\alpha \quad[*83·7]\)

`ι''α` is `iota ʻʻ A`. -/
theorem pm115_142 {α : Type*} {A : Set α} : prodK (ι A) = iota ʻʻ A := by
  ext X
  constructor
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨a, ha⟩ := pmB2_sel_ex hR (rfl : A ∈ ι A)
    refine ⟨a, (pmB2_mem_sel.1 hR).2.1 _ _ ha, ?_⟩
    show dom R = ι a
    ext z
    constructor
    · rintro ⟨Y, hz⟩
      have hY : Y = A := pmB2_sel_codom hR hz
      subst hY
      exact (pmB2_mem_sel.1 hR).1 _ _ _ ⟨hz, ha⟩
    · intro hz
      rw [mem_unitCls.1 hz]
      exact ⟨A, ha⟩
  · rintro ⟨x, hx, hX⟩
    have hX' : X = ι x := hX
    subst hX'
    refine ⟨fun z Y => Y = A ∧ z = x, pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩, ?_⟩
    · rintro u v Y ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
    · rintro z Y ⟨rfl, rfl⟩; exact hx
    · ext Y; exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨x, h, rfl⟩⟩
    · ext z; exact ⟨fun h => ⟨A, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩

/-- ✱115·143. \(\vdash . \text{Prod}ʻ\iotaʻʻ\alpha = \iota ʻ\alpha \quad[*83·71]\) -/
theorem pm115_143 {α : Type*} {A : Set α} : prodK (iota ʻʻ A) = ι A := by
  have key : ∀ R, R ∈ sel memRel (iota ʻʻ A) → dom R = A := by
    intro R hR
    ext z
    constructor
    · rintro ⟨Y, hz⟩
      obtain ⟨x, hx, hY⟩ := pmB2_sel_codom hR hz
      have hY' : Y = ι x := hY
      have : z ∈ Y := (pmB2_mem_sel.1 hR).2.1 _ _ hz
      rw [hY', mem_unitCls] at this
      rw [this]; exact hx
    · intro hz
      obtain ⟨w, hw⟩ := pmB2_sel_ex hR (⟨z, hz, rfl⟩ : ι z ∈ iota ʻʻ A)
      have : w ∈ ι z := (pmB2_mem_sel.1 hR).2.1 _ _ hw
      rw [mem_unitCls.1 this] at hw
      exact ⟨_, hw⟩
  ext X
  constructor
  · rintro ⟨R, hR, rfl⟩
    exact key R hR
  · intro hX
    have hX' : X = A := hX
    subst hX'
    refine ⟨fun z Y => Y ∈ iota ʻʻ X ∧ z ∈ Y, pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩, ?_⟩
    · rintro u v Y ⟨⟨⟨x, -, hY⟩, hu⟩, ⟨-, hv⟩⟩
      have hY' : Y = ι x := hY
      rw [hY', mem_unitCls] at hu hv
      rw [hu, hv]
    · rintro z Y ⟨-, h⟩; exact h
    · ext Y
      constructor
      · rintro ⟨z, h, -⟩; exact h
      · intro h
        obtain ⟨x, -, hY⟩ := id h
        have hY' : Y = ι x := hY
        exact ⟨x, h, by rw [hY']; rfl⟩
    · refine (key _ (pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩)).symm
      · rintro u v Y ⟨⟨⟨x, -, hY⟩, hu⟩, ⟨-, hv⟩⟩
        have hY' : Y = ι x := hY
        rw [hY', mem_unitCls] at hu hv
        rw [hu, hv]
      · rintro z Y ⟨-, h⟩; exact h
      · ext Y
        constructor
        · rintro ⟨z, h, -⟩; exact h
        · intro h
          obtain ⟨x, -, hY⟩ := id h
          have hY' : Y = ι x := hY
          exact ⟨x, h, by rw [hY']; rfl⟩

/-- ✱115·144. \(\vdash : \kappa \subset 1 . \supset . \text{Prod}ʻ\kappa = \iota ʻsʻ\kappa \quad[*83·72]\) -/
theorem pm115_144 {α : Type*} {K : Set (Set α)} : K ⊆ one → prodK K = ι (sumCls K) := by
  intro hK
  ext X
  constructor
  · rintro ⟨R, hR, rfl⟩
    show dom R = sumCls K
    refine Set.Subset.antisymm (pmB2_dom_sel_sub hR) ?_
    rintro z ⟨A, hA, hz⟩
    obtain ⟨a, rfl⟩ := hK hA
    obtain ⟨w, hw⟩ := pmB2_sel_ex hR hA
    have : w ∈ ι a := (pmB2_mem_sel.1 hR).2.1 _ _ hw
    rw [mem_unitCls] at this hz
    rw [hz, ← this]
    exact ⟨_, hw⟩
  · intro hX
    have hX' : X = sumCls K := hX
    subst hX'
    refine pmB2_mem_prodK_of (fun A hA => ?_) le_rfl
    have : sumCls K ∩ A = A := Set.inter_eq_right.2 fun z hz => ⟨A, hA, hz⟩
    rw [this]; exact hK hA

/-- ✱115·145. \[\begin{align}&\vdash \colon\ldotp \kappa \in \text{Cls}^{2} \text{excl} . \alpha \in \kappa . \mu \cap \alpha \in 1 . \supset : \mu - \alpha \in \text{Prod}ʻ(\kappa - \iota ʻ\alpha ) . \equiv . \mu \in \text{Prod}ʻ\kappa\\ &[*84·422]\end{align}\]

`μ` is a class (of the type of the members of `κ`). -/
theorem pm115_145 {α : Type*} {K : Set (Set α)} {A μ : Set α} :
    (K ∈ Cls2excl ∧ A ∈ K) ∧ μ ∩ A ∈ one → (μ \ A ∈ prodK (K \ ι A) ↔ μ ∈ prodK K) := by
  rintro ⟨⟨hK, hA⟩, hμA⟩
  have hK' : K \ ι A ∈ Cls2excl := pmB2_excl_subset hK Set.sdiff_subset
  have hdisj : ∀ B, B ∈ K → B ≠ A → μ \ A ∩ B = μ ∩ B := by
    intro B hB hne
    ext z
    constructor
    · rintro ⟨⟨hz, -⟩, hzB⟩; exact ⟨hz, hzB⟩
    · rintro ⟨hz, hzB⟩
      exact ⟨⟨hz, fun hzA => hne (pmB2_excl_iff.1 hK B A z hB hA hzB hzA)⟩, hzB⟩
  rw [pmB2_mem_prodK_excl hK', pmB2_mem_prodK_excl hK]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun B hB => ?_, fun z hz => ?_⟩
    · by_cases e : B = A
      · rw [e]; exact hμA
      · rw [← hdisj B hB e]; exact h1 B ⟨hB, e⟩
    · by_cases hzA : z ∈ A
      · exact ⟨A, hA, hzA⟩
      · obtain ⟨B, ⟨hB, -⟩, hzB⟩ := h2 ⟨hz, hzA⟩
        exact ⟨B, hB, hzB⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun B ⟨hB, hne⟩ => ?_, fun z ⟨hz, hzA⟩ => ?_⟩
    · rw [hdisj B hB hne]; exact h1 B hB
    · obtain ⟨B, hB, hzB⟩ := h2 hz
      refine ⟨B, ⟨hB, fun e => ?_⟩, hzB⟩
      have e' : B = A := e
      exact hzA (e' ▸ hzB)

/-- ✱115·15. \[\begin{align}&\vdash \colon\ldotp \kappa , \lambda \in \text{Cls}^{2} \text{excl} . sʻ\kappa = sʻ\lambda . \supset : \kappa \subset \text{Prod}ʻ\lambda . \equiv . \lambda \subset \text{Prod}ʻ\kappa \\ &[*84·43]\end{align}\] -/
theorem pm115_15 {α : Type*} {K L : Set (Set α)} :
    (K ∈ Cls2excl ∧ L ∈ Cls2excl) ∧ sumCls K = sumCls L → (K ⊆ prodK L ↔ L ⊆ prodK K) := by
  rintro ⟨⟨hK, hL⟩, e⟩
  have key : ∀ K L : Set (Set α), L ∈ Cls2excl → sumCls K = sumCls L →
      (K ⊆ prodK L ↔ ∀ A B, A ∈ K → B ∈ L → A ∩ B ∈ one) := by
    intro K L hL e
    constructor
    · intro h A B hA hB
      exact ((pmB2_mem_prodK_excl hL).1 (h hA)).1 B hB
    · intro h A hA
      refine (pmB2_mem_prodK_excl hL).2 ⟨fun B hB => h A B hA hB, ?_⟩
      rw [← e]; exact fun z hz => ⟨A, hA, hz⟩
  rw [key K L hL e, key L K hK e.symm]
  exact ⟨fun h A B hA hB => Set.inter_comm A B ▸ h B A hB hA,
    fun h A B hA hB => Set.inter_comm A B ▸ h B A hB hA⟩

/-- ✱115·151. \(\vdash : \kappa \in \text{Cls}^{2} \text{excl} . \supset . {\in}_{\Delta}ʻsʻ\kappa = \dot{s}ʻʻ\text{Prod}ʻ{\in}_{\Delta}ʻʻ\kappa \quad[*85·28]\)

`ṡ''…` is the image under the relation `ṡ` of `ṡ'λ` to `λ`, i.e. `graph sumRel` (its
descriptive function always exists, Basic §5). -/
theorem pm115_151 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls2excl → sel memRel (sumCls K) = graph sumRel ʻʻ prodK (selRel memRel ʻʻ K) := by
  intro hK
  ext R
  constructor
  · intro hR
    have resSel : ∀ A, A ∈ K → R ↾ A ∈ sel memRel A := fun A hA =>
      pmB2_mem_sel.2 ⟨fun x y z ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => (pmB2_mem_sel.1 hR).1 x y z ⟨hx, hy⟩,
        fun x y ⟨h, _⟩ => (pmB2_mem_sel.1 hR).2.1 x y h,
        Set.ext fun Y => ⟨fun ⟨_, _, hY⟩ => hY, fun hY => by
          obtain ⟨x, hx⟩ := pmB2_sel_ex hR (⟨A, hA, hY⟩ : Y ∈ sumCls K)
          exact ⟨x, hx, hY⟩⟩⟩
    refine ⟨{P | ∃ A, A ∈ K ∧ P = R ↾ A}, pmB2_mem_prodK_of ?_ ?_, ?_⟩
    · rintro Q ⟨A, hA, hQ⟩
      have hQ' : Q = sel memRel A := hQ
      refine ⟨R ↾ A, Set.ext fun P => ⟨?_, ?_⟩⟩
      · rintro ⟨⟨B, hB, rfl⟩, hPQ⟩
        rw [hQ'] at hPQ
        have : B = A := by
          rw [← (pmB2_mem_sel.1 (resSel B hB)).2.2, (pmB2_mem_sel.1 hPQ).2.2]
        rw [this]; rfl
      · intro hP
        rw [mem_unitCls] at hP
        subst hP
        exact ⟨⟨A, hA, rfl⟩, hQ' ▸ resSel A hA⟩
    · rintro P ⟨A, hA, rfl⟩
      exact ⟨sel memRel A, ⟨A, hA, rfl⟩, resSel A hA⟩
    · show R = sumRel _
      funext x Y
      apply propext
      constructor
      · intro h
        obtain ⟨A, hA, hY⟩ := pmB2_sel_codom hR h
        exact ⟨R ↾ A, ⟨A, hA, rfl⟩, h, hY⟩
      · rintro ⟨P, ⟨A, hA, rfl⟩, h, -⟩; exact h
  · rintro ⟨X, ⟨S, hS, rfl⟩, hRX⟩
    have hR : R = sumRel (dom S) := hRX
    subst hR
    have hP : ∀ P, P ∈ dom S → ∃ A, A ∈ K ∧ S P (sel memRel A) ∧ P ∈ sel memRel A := by
      rintro P ⟨Q, hPQ⟩
      obtain ⟨A, hA, hQ⟩ := pmB2_sel_codom hS hPQ
      have hQ' : Q = sel memRel A := hQ
      subst hQ'
      exact ⟨A, hA, hPQ, (pmB2_mem_sel.1 hS).2.1 _ _ hPQ⟩
    refine pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩
    · rintro x y Y ⟨⟨P, hPd, hx⟩, ⟨P', hPd', hy⟩⟩
      obtain ⟨A, hA, hSA, hPA⟩ := hP P hPd
      obtain ⟨A', hA', hSA', hPA'⟩ := hP P' hPd'
      have hAA : A = A' := pmB2_excl_iff.1 hK A A' Y hA hA' (pmB2_sel_codom hPA hx)
        (pmB2_sel_codom hPA' hy)
      subst hAA
      have e : P = P' := (pmB2_mem_sel.1 hS).1 _ _ _ ⟨hSA, hSA'⟩
      subst e
      exact (pmB2_mem_sel.1 hPA).1 _ _ _ ⟨hx, hy⟩
    · rintro x Y ⟨P, hPd, hx⟩
      obtain ⟨A, -, -, hPA⟩ := hP P hPd
      exact (pmB2_mem_sel.1 hPA).2.1 _ _ hx
    · ext Y
      constructor
      · rintro ⟨x, P, hPd, hx⟩
        obtain ⟨A, hA, -, hPA⟩ := hP P hPd
        exact ⟨A, hA, pmB2_sel_codom hPA hx⟩
      · rintro ⟨A, hA, hY⟩
        obtain ⟨P, hSP⟩ := pmB2_sel_ex hS (⟨A, hA, rfl⟩ : sel memRel A ∈ selRel memRel ʻʻ K)
        have hPA : P ∈ sel memRel A := (pmB2_mem_sel.1 hS).2.1 _ _ hSP
        obtain ⟨x, hx⟩ := pmB2_sel_ex hPA hY
        exact ⟨x, P, ⟨_, hSP⟩, hx⟩

private theorem pmB2_mem_downCls {α β : Type*} {P : α → β → Prop} {y : β} {Q : α → β → Prop} :
    Q ∈ P ↧ y ↔ ∃ x, P x y ∧ Q = x ↓ y := Iff.rfl

private theorem pmB2_mem_downImg {α β : Type*} {P : α → β → Prop} {A : Set β}
    {Y : Set (α → β → Prop)} : Y ∈ opL downCls P ʻʻ A ↔ ∃ y, y ∈ A ∧ Y = P ↧ y := Iff.rfl

/-- ✱115·152. \(\vdash . P_{\Delta }ʻ\alpha \text{ sm } \text{Prod}ʻP \unicode{x21A7}ʻʻ\alpha \quad[*85·55]\)

`P↧` is the relation `opL downCls P` of `P ↧ y` to `y`, so `P↧''α` is `opL downCls P ʻʻ A`. -/
theorem pm115_152 {α β : Type*} {P : α → β → Prop} {A : Set β} :
    sm (sel P A) (prodK (opL downCls P ʻʻ A)) := by
  let Φ : (α → β → Prop) → Set (α → β → Prop) := fun R => {Q | ∃ x y, R x y ∧ Q = x ↓ y}
  have hmaps : Set.MapsTo Φ (sel P A) (prodK (opL downCls P ʻʻ A)) := by
    intro R hR
    refine pmB2_mem_prodK_of ?_ ?_
    · rintro Y ⟨y, hy, rfl⟩
      obtain ⟨x₀, hx₀⟩ := pmB2_sel_ex hR hy
      refine ⟨x₀ ↓ y, Set.ext fun Q => ⟨?_, ?_⟩⟩
      · rintro ⟨⟨x, y', hR', rfl⟩, ⟨x', -, e⟩⟩
        obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
        rw [(pmB2_mem_sel.1 hR).1 _ _ _ ⟨hR', hx₀⟩]
        rfl
      · intro hQ
        rw [mem_unitCls] at hQ
        subst hQ
        exact ⟨⟨x₀, y, hx₀, rfl⟩, ⟨x₀, (pmB2_mem_sel.1 hR).2.1 _ _ hx₀, rfl⟩⟩
    · rintro Q ⟨x, y, hxy, rfl⟩
      exact ⟨P ↧ y, ⟨y, pmB2_sel_codom hR hxy, rfl⟩, ⟨x, (pmB2_mem_sel.1 hR).2.1 _ _ hxy, rfl⟩⟩
  have hinj : Set.InjOn Φ (sel P A) := by
    have key : ∀ R S, Φ R = Φ S → ∀ x y, R x y → S x y := by
      intro R S e x y h
      have : x ↓ y ∈ Φ S := e ▸ ⟨x, y, h, rfl⟩
      obtain ⟨x', y', h', e'⟩ := this
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e'
      exact h'
    intro R _ S _ e
    funext x y
    exact propext ⟨key R S e x y, key S R e.symm x y⟩
  have hsurj : Set.SurjOn Φ (sel P A) (prodK (opL downCls P ʻʻ A)) := by
    rintro X ⟨T, hT, rfl⟩
    have hsub := pmB2_dom_sel_sub hT
    have hcell : ∀ x y Y, T (x ↓ y) Y → Y = P ↧ y := by
      intro x y Y h
      obtain ⟨y₁, -, hY⟩ := pmB2_sel_codom hT h
      have hY' : Y = P ↧ y₁ := hY
      have hmem : x ↓ y ∈ Y := (pmB2_mem_sel.1 hT).2.1 _ _ h
      rw [hY'] at hmem ⊢
      obtain ⟨x', -, e⟩ := hmem
      rw [(couple_eq_couple_iff.1 e).2]
    refine ⟨fun x y => y ∈ A ∧ x ↓ y ∈ dom T, pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩, ?_⟩
    · rintro x x' y ⟨⟨-, Y, hY⟩, ⟨-, Y', hY'⟩⟩
      have e1 := hcell _ _ _ hY
      have e2 := hcell _ _ _ hY'
      subst e1; subst e2
      exact (couple_eq_couple_iff.1 ((pmB2_mem_sel.1 hT).1 _ _ _ ⟨hY, hY'⟩)).1
    · rintro x y ⟨-, hxy⟩
      obtain ⟨Y, ⟨y₁, -, rfl⟩, ⟨x', hP, e⟩⟩ := hsub hxy
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
      exact hP
    · ext y
      constructor
      · rintro ⟨x, hy, -⟩; exact hy
      · intro hy
        obtain ⟨Q, hQ⟩ := pmB2_sel_ex hT (⟨y, hy, rfl⟩ : P ↧ y ∈ opL downCls P ʻʻ A)
        obtain ⟨x, -, rfl⟩ := (pmB2_mem_sel.1 hT).2.1 _ _ hQ
        exact ⟨x, hy, _, hQ⟩
    · ext Q
      constructor
      · rintro ⟨x, y, ⟨-, h⟩, rfl⟩; exact h
      · intro hQ
        obtain ⟨Y, ⟨y, hy, rfl⟩, ⟨x, -, rfl⟩⟩ := hsub hQ
        exact ⟨x, y, ⟨hy, hQ⟩, rfl⟩
  exact pmB2_sm_of_equiv (Set.BijOn.equiv Φ ⟨hmaps, hinj, hsurj⟩)

/-- ✱115·153. \(\vdash . {\in}_{\Delta}ʻ\kappa \text{ sm } \text{Prod}ʻ\in \unicode{x21A7}ʻʻ\kappa \quad[*115·152]\) -/
theorem pm115_153 {α : Type*} {K : Set (Set α)} :
    sm (sel memRel K) (prodK (opL downCls memRel ʻʻ K)) := pm115_152

/-- ✱115·154. \(\vdash . \text{Prod}ʻ\in \unicode{x21A7}ʻʻ\kappa \in \Pi \text{Nc}ʻ\kappa \quad[*115·153]\)

`ΠNc'κ` is taken in the type of its member `Prod'∈↧''κ` (significance). -/
theorem pm115_154 {α : Type*} {K : Set (Set α)} :
    prodK (opL downCls memRel ʻʻ K) ∈ piNc (Set (α → Set α → Prop)) K := sm_symm pm115_153

/-- ✱115·16. \(\vdash : \kappa \in \text{Cls}^{2} \text{excl} . \supset . \text{Prod}ʻ\kappa \subset \text{Nc}ʻ\kappa \quad[*100·64]\)

`Nc'κ` is taken in the type of the members of `Prod'κ` (significance). -/
theorem pm115_16 {α : Type*} {K : Set (Set α)} : K ∈ Cls2excl → prodK K ⊆ nc α K := by
  rintro hK X ⟨R, hR, rfl⟩
  exact sm_iff.2 ⟨R, ⟨pmB2_sel_one_one hK hR, rfl⟩, (pmB2_mem_sel.1 hR).2.2.symm⟩

/-- ✱115·17. \(\vdash : \exists ! {\in}_{\Delta}ʻ\text{Cl ex}ʻ\alpha . \supset . \text{Prod}ʻ\text{Cl ex}ʻ\alpha = \iota ʻ\alpha\) -/
theorem pm115_17 {α : Type*} {A : Set α} :
    (sel memRel (clEx A)).Nonempty → prodK (clEx A) = ι A := by
  have key : ∀ R, R ∈ sel memRel (clEx A) → dom R = A := by
    intro R hR
    ext x
    constructor
    · rintro ⟨B, hB⟩
      exact (pmB2_sel_codom hR hB).1 ((pmB2_mem_sel.1 hR).2.1 _ _ hB)
    · intro hx
      have hs : ({x} : Set α) ∈ clEx A := ⟨Set.singleton_subset_iff.2 hx, Set.singleton_nonempty x⟩
      obtain ⟨w, hw⟩ := pmB2_sel_ex hR hs
      have : w ∈ ({x} : Set α) := (pmB2_mem_sel.1 hR).2.1 _ _ hw
      rw [Set.mem_singleton_iff.1 this] at hw
      exact ⟨_, hw⟩
  rintro ⟨R₀, hR₀⟩
  ext X
  constructor
  · rintro ⟨R, hR, rfl⟩
    exact key R hR
  · intro hX
    rw [mem_unitCls] at hX
    exact ⟨R₀, hR₀, hX.trans (key R₀ hR₀).symm⟩

/-- ✱115·18. \(\vdash .tʻ\text{Prod}ʻ\kappa = tʻ\kappa \quad[*83·81]\)

A typing statement; both sides are `Set.univ` of the type of `κ`. -/
theorem pm115_18 {α : Type*} {K : Set (Set α)} : typ (prodK K) = typ K := by
  rw [typ_eq_univ, typ_eq_univ]

/-- ✱115·2. \(\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}. \equiv .\kappa ,sʻ\kappa \in \text{Cls}^{2} \text{excl} \quad[(*115·02)]\) -/
theorem pm115_2 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm ↔ K ∈ Cls2excl ∧ sumCls K ∈ Cls2excl := Iff.rfl

/-- ✱115·21. \[\begin{align}\vdash \colon\ldotp \kappa \in \text{Cls}^{3}\,\text{arithm}. \equiv :&\alpha ,\beta \in \kappa .\exists !\alpha \cap \beta .\supset _{\alpha ,\beta }.\alpha = \beta :\\ &\alpha ,\beta \in \kappa .\rho \in \alpha .\sigma \in \beta .\exists !\rho \cap \sigma .\supset _{\alpha ,\beta ,\rho ,\sigma }.\rho = \sigma \\ [*115·2.*84·11]\end{align}\] -/
theorem pm115_21 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm ↔ (∀ A B, (A ∈ K ∧ B ∈ K) ∧ (A ∩ B).Nonempty → A = B) ∧
      (∀ A B ρ σ, (((A ∈ K ∧ B ∈ K) ∧ ρ ∈ A) ∧ σ ∈ B) ∧ (ρ ∩ σ).Nonempty → ρ = σ) := by
  rw [pm115_2, pmB2_excl_iff', pmB2_excl_iff']
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro h A B ρ σ ⟨⟨⟨⟨hA, hB⟩, hρ⟩, hσ⟩, hne⟩
    exact h ρ σ ⟨⟨⟨A, hA, hρ⟩, ⟨B, hB, hσ⟩⟩, hne⟩
  · rintro h ρ σ ⟨⟨⟨A, hA, hρ⟩, ⟨B, hB, hσ⟩⟩, hne⟩
    exact h A B ρ σ ⟨⟨⟨⟨hA, hB⟩, hρ⟩, hσ⟩, hne⟩

/-- ✱115·211. \(\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}.\alpha ,\beta \in \kappa .\rho \in \alpha .\sigma \in \beta .\exists !\rho \cap \sigma .\supset .\alpha = \beta\) -/
theorem pm115_211 {α : Type*} {K : Set (Set (Set α))} {A B : Set (Set α)} {ρ σ : Set α} :
    ((((K ∈ Cls3arithm ∧ (A ∈ K ∧ B ∈ K)) ∧ ρ ∈ A) ∧ σ ∈ B) ∧ (ρ ∩ σ).Nonempty) → A = B := by
  rintro ⟨⟨⟨⟨⟨hK, hsK⟩, ⟨hA, hB⟩⟩, hρ⟩, hσ⟩, hne⟩
  have e : ρ = σ := pmB2_excl_iff'.1 hsK ρ σ ⟨⟨⟨A, hA, hρ⟩, ⟨B, hB, hσ⟩⟩, hne⟩
  subst e
  exact pmB2_excl_iff'.1 hK A B ⟨⟨hA, hB⟩, ρ, hρ, hσ⟩

private theorem pmB2_arithm_sumCls_inj {α : Type*} {K : Set (Set (Set α))} (hK3 : K ∈ Cls3arithm)
    {A B : Set (Set α)} (hA : A ∈ K) (hB : B ∈ K) (h : (sumCls A ∩ sumCls B).Nonempty) :
    A = B := by
  obtain ⟨x, ⟨ρ, hρ, hxρ⟩, ⟨σ, hσ, hxσ⟩⟩ := h
  exact pm115_211 ⟨⟨⟨⟨hK3, ⟨hA, hB⟩⟩, hρ⟩, hσ⟩, x, hxρ, hxσ⟩

/-- ✱115·22. \(\vdash \colon\ldotp \kappa \in \text{Cls}^{3}\,\text{arithm}.\supset :sʻʻ\kappa \in \text{Cls}^{2} \text{excl}:\alpha ,\beta \in \kappa .\exists !sʻ\alpha \cap sʻ\beta .\supset _{\alpha ,\beta }.\alpha = \beta\)

`s''κ` is the image of `κ` under the relation `s` of `s'λ` to `λ`, i.e. `graph sumCls`. -/
theorem pm115_22 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm → graph sumCls ʻʻ K ∈ Cls2excl ∧
      ∀ A B, (A ∈ K ∧ B ∈ K) ∧ (sumCls A ∩ sumCls B).Nonempty → A = B := by
  intro hK3
  refine ⟨pmB2_excl_iff'.2 ?_, fun A B ⟨⟨hA, hB⟩, h⟩ => pmB2_arithm_sumCls_inj hK3 hA hB h⟩
  rintro P P' ⟨⟨⟨A, hA, hP⟩, ⟨B, hB, hP'⟩⟩, hne⟩
  have hP1 : P = sumCls A := hP
  have hP2 : P' = sumCls B := hP'
  subst hP1; subst hP2
  rw [pmB2_arithm_sumCls_inj hK3 hA hB hne]

private theorem pmB2_arithm_prodK_inj {α : Type*} {K : Set (Set (Set α))} (hK3 : K ∈ Cls3arithm)
    {A B : Set (Set α)} (hA : A ∈ K) (hB : B ∈ K) (h : (prodK A ∩ prodK B).Nonempty) :
    A = B := by
  obtain ⟨X, ⟨R, hR, rfl⟩, ⟨S, hS, e⟩⟩ := h
  by_cases hX : (dom R).Nonempty
  · obtain ⟨x, hx⟩ := hX
    have hx' : x ∈ dom S := e ▸ hx
    obtain ⟨ρ, hρ⟩ := hx
    obtain ⟨σ, hσ⟩ := hx'
    exact pm115_211 ⟨⟨⟨⟨hK3, ⟨hA, hB⟩⟩, pmB2_sel_codom hR hρ⟩, pmB2_sel_codom hS hσ⟩, x,
      (pmB2_mem_sel.1 hR).2.1 _ _ hρ, (pmB2_mem_sel.1 hS).2.1 _ _ hσ⟩
  · have hemp : ∀ (C : Set (Set α)) (T : α → Set α → Prop), T ∈ sel memRel C →
        ¬(dom T).Nonempty → C = ∅ := by
      intro C T hT hT'
      refine Set.eq_empty_iff_forall_notMem.2 fun ρ hρ => hT' ?_
      obtain ⟨x, hx⟩ := pmB2_sel_ex hT hρ
      exact ⟨x, ρ, hx⟩
    rw [hemp A R hR hX, hemp B S hS (e ▸ hX)]

/-- ✱115·23. \[\begin{align}\vdash \colon\ldotp \kappa \in &\text{Cls}^{3}\,\text{arithm}.\supset :\\ &\text{Prod}ʻʻ\kappa \in \text{Cls}^{2} \text{excl}:\alpha ,\beta \in \kappa .\exists !\text{Prod}ʻ\alpha \cap \text{Prod}ʻ\beta .\supset _{\alpha ,\beta }.\alpha = \beta\end{align}\]

`Prod''κ` is the image of `κ` under the relation `Prod` (`ProdK`). -/
theorem pm115_23 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm → ProdK ʻʻ K ∈ Cls2excl ∧
      ∀ A B, (A ∈ K ∧ B ∈ K) ∧ (prodK A ∩ prodK B).Nonempty → A = B := by
  intro hK3
  refine ⟨pmB2_excl_iff'.2 ?_, fun A B ⟨⟨hA, hB⟩, h⟩ => pmB2_arithm_prodK_inj hK3 hA hB h⟩
  rintro P P' ⟨⟨⟨A, hA, hP⟩, ⟨B, hB, hP'⟩⟩, hne⟩
  have hP1 : P = prodK A := hP
  have hP2 : P' = prodK B := hP'
  subst hP1; subst hP2
  rw [pmB2_arithm_prodK_inj hK3 hA hB hne]

private theorem pmB2_excl_iff_memRel {α : Type*} {L : Set (Set α)} :
    L ∈ Cls2excl ↔ memRel ↾ L ∈ arrow Cls one := by
  rw [mem_arrow_Cls_one, pmB2_excl_iff]
  exact ⟨fun h x A B ⟨⟨hxA, hA⟩, ⟨hxB, hB⟩⟩ => h A B x hA hB hxA hxB,
    fun h A B x hA hB hxA hxB => h x A B ⟨⟨hxA, hA⟩, ⟨hxB, hB⟩⟩⟩

/-- ✱115·24. \(\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}. \equiv .\in \upharpoonright \kappa ,\in \upharpoonright sʻ\kappa \in \text{Cls}\rightarrow 1 \quad[*115·2.*84·14]\)

`∈ ↾ κ, ∈ ↾ s'κ ∈ Cls → 1`: the two relations are of different types, so it is a conjunction. -/
theorem pm115_24 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm ↔ memRel ↾ K ∈ arrow Cls one ∧ memRel ↾ sumCls K ∈ arrow Cls one := by
  rw [pm115_2, pmB2_excl_iff_memRel, pmB2_excl_iff_memRel]

/-- ✱115·25. \(\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}.\supset .{\in}_{\Delta}ʻ\kappa \subset 1\rightarrow 1.{\in}_{\Delta}ʻsʻ\kappa \subset 1\rightarrow 1 \quad[*84·3.*115·2]\) -/
theorem pm115_25 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm → sel memRel K ⊆ arrow one one ∧ sel memRel (sumCls K) ⊆ arrow one one :=
  fun ⟨hK, hsK⟩ => ⟨fun _ hR => pmB2_sel_one_one hK hR, fun _ hR => pmB2_sel_one_one hsK hR⟩

/-- ✱115·26. \[\begin{align}\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}.&\supset .\\ &{\in}_{\Delta}ʻsʻʻ\kappa \subset 1\rightarrow 1.{\in}_{\Delta}ʻ{\in}_{\Delta}ʻʻ\kappa \subset 1\rightarrow 1.{\in}_{\Delta}ʻ\text{Prod}ʻʻ\kappa \subset 1\rightarrow 1\\ &[*84·3.*115·22.*84·55.*115·23]\end{align}\] -/
theorem pm115_26 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm → (sel memRel (graph sumCls ʻʻ K) ⊆ arrow one one ∧
      sel memRel (selRel memRel ʻʻ K) ⊆ arrow one one) ∧ sel memRel (ProdK ʻʻ K) ⊆ arrow one one :=
  fun hK3 => ⟨⟨fun _ hR => pmB2_sel_one_one (pm115_22 hK3).1 hR,
    fun _ hR => pmB2_sel_one_one (pmB2_selRel_img_excl K) hR⟩,
    fun _ hR => pmB2_sel_one_one (pm115_23 hK3).1 hR⟩

/-- ✱115·27. \(\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}.\supset .\kappa \subset \text{Cls}^{2} \text{excl} \quad[*115·2.*84·25.*40·13]\) -/
theorem pm115_27 {α : Type*} {K : Set (Set (Set α))} : K ∈ Cls3arithm → K ⊆ Cls2excl :=
  fun ⟨_, hsK⟩ A hA => pmB2_excl_subset hsK fun _ hρ => ⟨A, hA, hρ⟩

/-- ✱115·3. \(\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}.R,S\in sʻ{\in}_{\Delta}ʻʻ\kappa .\text{D}ʻR = \text{D}ʻS.\supset .R = S\) -/
theorem pm115_3 {α : Type*} {K : Set (Set (Set α))} {R S : α → Set α → Prop} :
    (K ∈ Cls3arithm ∧ (R ∈ sumCls (selRel memRel ʻʻ K) ∧ S ∈ sumCls (selRel memRel ʻʻ K))) ∧
      dom R = dom S → R = S := by
  rintro ⟨⟨hK3, ⟨Q, ⟨A, hA, hQ⟩, hRQ⟩, ⟨Q', ⟨B, hB, hQ'⟩, hSQ'⟩⟩, e⟩
  have h1 : Q = sel memRel A := hQ
  have h2 : Q' = sel memRel B := hQ'
  subst h1; subst h2
  have hAB : A = B := by
    by_cases hX : (dom R).Nonempty
    · obtain ⟨x, hx⟩ := hX
      have hx' : x ∈ dom S := e ▸ hx
      obtain ⟨ρ, hρ⟩ := hx
      obtain ⟨σ, hσ⟩ := hx'
      exact pm115_211 ⟨⟨⟨⟨hK3, ⟨hA, hB⟩⟩, pmB2_sel_codom hRQ hρ⟩, pmB2_sel_codom hSQ' hσ⟩, x,
        (pmB2_mem_sel.1 hRQ).2.1 _ _ hρ, (pmB2_mem_sel.1 hSQ').2.1 _ _ hσ⟩
    · have hemp : ∀ (C : Set (Set α)) (T : α → Set α → Prop), T ∈ sel memRel C →
          ¬(dom T).Nonempty → C = ∅ := by
        intro C T hT hT'
        refine Set.eq_empty_iff_forall_notMem.2 fun ρ hρ => hT' ?_
        obtain ⟨x, hx⟩ := pmB2_sel_ex hT hρ
        exact ⟨x, ρ, hx⟩
      rw [hemp A R hRQ hX, hemp B S hSQ' (e ▸ hX)]
  subst hAB
  exact pmB2_sel_dom_inj (pm115_27 hK3 hA) hRQ hSQ' e

/-- ✱115·31. \(\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}.\supset .\text{Prod}ʻʻ\kappa \text{ sm }\text{ sm }{\in}_{\Delta}ʻʻ\kappa\)

`sm sm` is the relation `smsm` (✱111·03). -/
theorem pm115_31 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm → smsm (ProdK ʻʻ K) (selRel memRel ʻʻ K) := by
  intro hK3
  refine ⟨fun X R => R ∈ sumCls (selRel memRel ʻʻ K) ∧ X = dom R, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · exact mem_arrow_one_one.2 ⟨fun X Y R ⟨⟨_, hX⟩, ⟨_, hY⟩⟩ => hX.trans hY.symm,
      fun X R S ⟨⟨hR, hX⟩, ⟨hS, hX'⟩⟩ => pm115_3 ⟨⟨hK3, hR, hS⟩, hX.symm.trans hX'⟩⟩
  · show sumCls (selRel memRel ʻʻ K) = codom _
    ext R
    exact ⟨fun h => ⟨dom R, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  · ext P
    constructor
    · rintro ⟨A, hA, hP⟩
      have hP' : P = prodK A := hP
      refine ⟨sel memRel A, ⟨A, hA, rfl⟩, ?_⟩
      show P = _
      rw [hP']
      ext X
      exact ⟨fun ⟨R, hR, hX⟩ => ⟨R, hR, ⟨_, ⟨A, hA, rfl⟩, hR⟩, hX⟩,
        fun ⟨R, hR, _, hX⟩ => ⟨R, hR, hX⟩⟩
    · rintro ⟨Q, ⟨A, hA, hQ⟩, hP⟩
      have hQ' : Q = sel memRel A := hQ
      have hP' : P = _ := hP
      subst hQ'
      refine ⟨A, hA, ?_⟩
      show P = prodK A
      rw [hP']
      ext X
      exact ⟨fun ⟨R, hR, _, hX⟩ => ⟨R, hR, hX⟩,
        fun ⟨R, hR, hX⟩ => ⟨R, hR, ⟨_, ⟨A, hA, rfl⟩, hR⟩, hX⟩⟩

/-- `Π (A : κ), Π (ρ : A), ρ`. -/
private abbrev pmB2_PiPi {α : Type*} (K : Set (Set (Set α))) : Type _ :=
  (A : ↥K) → (ρ : ↥(A : Set (Set α))) → ↥(ρ : Set α)

private noncomputable def pmB2_selE {α : Type*} (K : Set (Set α)) :
    ↥(sel memRel K) ≃ ((A : ↥K) → ↥(A : Set α)) :=
  pmB2_selEquiv memRel K

private noncomputable def pmB2_e1 {α : Type*} {K : Set (Set (Set α))} (hK : K ∈ Cls2excl) :
    ↥(sel memRel (sumCls K)) ≃ pmB2_PiPi K :=
  (pmB2_selE (sumCls K)).trans
    (((Equiv.piCongrLeft (fun ρ : ↥(sumCls K) => ↥(ρ : Set α)) (pmB2_sumClsEquiv hK).symm).symm).trans
      (Equiv.piCurry (fun (A : ↥K) (ρ : ↥(A : Set (Set α))) => ↥(ρ : Set α))))

private theorem pmB2_sel_injOn {α : Type*} {K : Set (Set (Set α))} (hK : K ∈ Cls2excl) :
    Set.InjOn (sel memRel) K := by
  intro A hA B hB e
  by_cases h : (sel memRel A).Nonempty
  · obtain ⟨R, hR⟩ := h
    have hR' : R ∈ sel memRel B := e ▸ hR
    rw [← (pmB2_mem_sel.1 hR).2.2, ← (pmB2_mem_sel.1 hR').2.2]
  · have h' : ¬(sel memRel B).Nonempty := e ▸ h
    rw [pmB2_sel_nonempty_iff, not_not] at h h'
    exact pmB2_excl_iff.1 hK A B ∅ hA hB h h'

private noncomputable def pmB2_e2 {α : Type*} {K : Set (Set (Set α))} (hK : K ∈ Cls2excl) :
    ↥(sel memRel ((sel memRel) '' K)) ≃ pmB2_PiPi K :=
  (pmB2_selE _).trans ((pmB2_piImage (sel memRel) K (pmB2_sel_injOn hK)
    (fun Q => ↥(Q : Set (α → Set α → Prop)))).trans (Equiv.piCongrRight fun A => pmB2_selE (A : Set (Set α))))

private theorem pmB2_prodK_injOn {α : Type*} {K : Set (Set (Set α))} (hK3 : K ∈ Cls3arithm) :
    Set.InjOn prodK K := by
  intro A hA B hB e
  by_cases h : (prodK A).Nonempty
  · exact pmB2_arithm_prodK_inj hK3 hA hB (by rw [← e, Set.inter_self]; exact h)
  · have h' : ¬(prodK B).Nonempty := e ▸ h
    rw [pmB2_prodK_nonempty_iff, pmB2_sel_nonempty_iff, not_not] at h h'
    exact pmB2_excl_iff.1 hK3.1 A B ∅ hA hB h h'

private noncomputable def pmB2_e3 {α : Type*} {K : Set (Set (Set α))} (hK3 : K ∈ Cls3arithm) :
    ↥(sel memRel (prodK '' K)) ≃ pmB2_PiPi K :=
  (pmB2_selE _).trans ((pmB2_piImage prodK K (pmB2_prodK_injOn hK3)
    (fun P => ↥(P : Set (Set α)))).trans (Equiv.piCongrRight fun A =>
      (pmB2_prodEquiv (pm115_27 hK3 A.2)).trans (pmB2_selE (A : Set (Set α)))))

private theorem pmB2_ProdK_img {α : Type*} (K : Set (Set (Set α))) : ProdK ʻʻ K = prodK '' K :=
  pmB2_img_graph prodK K

private theorem pmB2_selRel_img {α : Type*} (K : Set (Set (Set α))) :
    selRel memRel ʻʻ K = (sel memRel) '' K :=
  pmB2_img_graph (sel memRel) K

/-- ✱115·32. \(\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}.\supset .{\in}_{\Delta}ʻ\text{Prod}ʻʻ\kappa \text{ sm }{\in}_{\Delta}ʻ{\in}_{\Delta}ʻʻ\kappa \quad[*115·31.*114·52]\) -/
theorem pm115_32 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm → sm (sel memRel (ProdK ʻʻ K)) (sel memRel (selRel memRel ʻʻ K)) := by
  intro hK3
  rw [pmB2_ProdK_img, pmB2_selRel_img]
  exact pmB2_sm_of_equiv ((pmB2_e3 hK3).trans (pmB2_e2 hK3.1).symm)

/-- ✱115·33. \(\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}.\supset .{\in}_{\Delta}ʻ\text{Prod}ʻʻ\kappa \text{ sm }{\in}_{\Delta}ʻsʻ\kappa \quad[*115·32. *85·44]\) -/
theorem pm115_33 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm → sm (sel memRel (ProdK ʻʻ K)) (sel memRel (sumCls K)) := by
  intro hK3
  rw [pmB2_ProdK_img]
  exact pmB2_sm_of_equiv ((pmB2_e3 hK3).trans (pmB2_e1 hK3.1).symm)

/-- ✱115·34. \[\begin{align}&\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}.\supset .\text{Prod}ʻ\text{Prod}ʻʻ\kappa \text{ sm }\text{Prod}ʻsʻ\kappa .\text{Prod}ʻsʻ\kappa \text{ sm }{\in}_{\Delta}ʻsʻ\kappa\\ &[*115·33·12·23]\end{align}\] -/
theorem pm115_34 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm → sm (prodK (ProdK ʻʻ K)) (prodK (sumCls K)) ∧
      sm (prodK (sumCls K)) (sel memRel (sumCls K)) := by
  intro hK3
  have h4 : sm (prodK (sumCls K)) (sel memRel (sumCls K)) :=
    pmB2_sm_of_equiv (pmB2_prodEquiv hK3.2)
  have h5 : sm (prodK (ProdK ʻʻ K)) (sel memRel (ProdK ʻʻ K)) :=
    pmB2_sm_of_equiv (pmB2_prodEquiv (pm115_23 hK3).1)
  exact ⟨sm_trans h5 (sm_trans (pm115_33 hK3) (sm_symm h4)), h4⟩

/-- ✱115·35. \[\begin{align}&\vdash : \kappa \in \text{Cls}^{3}\,\text{arithm} . \supset .\\ &\text{Nc}ʻ\text{Prod}ʻ\text{Prod}ʻʻ\kappa = \text{Nc}ʻ\text{Prod}ʻsʻ\kappa = \Pi \text{Nc}ʻ\text{Prod}ʻʻ\kappa = \Pi \text{Nc}ʻ{\in}_{\Delta}ʻʻ\kappa = \Pi \text{Nc}ʻsʻk\\ &[*115·34·33·32]\end{align}\]

All the formal numbers of the chain are in one type `γ` (the opposed sides of each equation;
convention IT); the chain is the conjunction of its links.

**Status.** proved (reading): transcription error: the e-text prints `s'k` for `s'κ`. -/
theorem pm115_35 {α γ : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm →
      ((nc γ (prodK (ProdK ʻʻ K)) = nc γ (prodK (sumCls K)) ∧
        nc γ (prodK (sumCls K)) = piNc γ (ProdK ʻʻ K)) ∧
        piNc γ (ProdK ʻʻ K) = piNc γ (selRel memRel ʻʻ K)) ∧
        piNc γ (selRel memRel ʻʻ K) = piNc γ (sumCls K) := by
  intro hK3
  obtain ⟨h1, h2⟩ := pm115_34 hK3
  have h33 := pm115_33 hK3
  have h32 := pm115_32 hK3
  exact ⟨⟨⟨nc_eq_nc_of_sm h1, nc_eq_nc_of_sm (sm_trans h2 (sm_symm h33))⟩,
    nc_eq_nc_of_sm h32⟩, nc_eq_nc_of_sm (sm_trans (sm_symm h32) h33)⟩

private theorem pmB2_prodK_natural {α β : Type*} {T : α → β → Prop} {L : Set (Set β)}
    (h1 : ∀ x x' y, (T x y ∧ y ∈ sumCls L) ∧ (T x' y ∧ y ∈ sumCls L) → x = x')
    (h2 : ∀ x y y', (T x y ∧ y ∈ sumCls L) ∧ (T x y' ∧ y' ∈ sumCls L) → y = y')
    (h3 : sumCls L ⊆ codom T) :
    prodK (T ʻʻʻ L) = T ʻʻʻ prodK L := by
  have imgInj : ∀ B B', B ⊆ sumCls L → B' ⊆ sumCls L → T ʻʻ B = T ʻʻ B' → B ⊆ B' := by
    intro B B' hB hB' e z hz
    obtain ⟨w, hw⟩ := h3 (hB hz)
    have : w ∈ T ʻʻ B' := e ▸ ⟨z, hz, hw⟩
    obtain ⟨z', hz', hw'⟩ := this
    rw [h2 w z z' ⟨⟨hw, hB hz⟩, ⟨hw', hB' hz'⟩⟩]; exact hz'
  have subL : ∀ B, B ∈ L → B ⊆ sumCls L := fun B hB z hz => ⟨B, hB, hz⟩
  ext X
  constructor
  · rintro ⟨R', hR', rfl⟩
    refine ⟨dom (fun y B => B ∈ L ∧ y ∈ B ∧ ∃ x, T x y ∧ R' x (T ʻʻ B)),
      ⟨_, pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩, rfl⟩, ?_⟩
    · rintro y y' B ⟨⟨hB, hy, x, hT, hR⟩, ⟨-, hy', x', hT', hR''⟩⟩
      have e : x = x' := (pmB2_mem_sel.1 hR').1 _ _ _ ⟨hR, hR''⟩
      subst e
      exact h2 x y y' ⟨⟨hT, subL B hB hy⟩, ⟨hT', subL B hB hy'⟩⟩
    · rintro y B ⟨-, hy, -⟩; exact hy
    · ext B
      constructor
      · rintro ⟨y, hB, -⟩; exact hB
      · intro hB
        obtain ⟨x, hx⟩ := pmB2_sel_ex hR' (⟨B, hB, rfl⟩ : T ʻʻ B ∈ T ʻʻʻ L)
        obtain ⟨y, hy, hT⟩ := (pmB2_mem_sel.1 hR').2.1 _ _ hx
        exact ⟨y, hB, hy, x, hT, hx⟩
    · show dom R' = T ʻʻ _
      ext x
      constructor
      · rintro ⟨Y, hxY⟩
        obtain ⟨B, hB, hY⟩ := pmB2_sel_codom hR' hxY
        have hY' : Y = T ʻʻ B := hY
        have hx : x ∈ Y := (pmB2_mem_sel.1 hR').2.1 _ _ hxY
        rw [hY'] at hx hxY
        obtain ⟨y, hy, hT⟩ := hx
        exact ⟨y, ⟨B, hB, hy, x, hT, hxY⟩, hT⟩
      · rintro ⟨y, ⟨B, hB, hy, x₀, hT₀, hR₀⟩, hT⟩
        rw [h1 x x₀ y ⟨⟨hT, subL B hB hy⟩, ⟨hT₀, subL B hB hy⟩⟩]
        exact ⟨_, hR₀⟩
  · rintro ⟨ξ, ⟨R, hR, rfl⟩, hX⟩
    have hX' : X = T ʻʻ dom R := hX
    subst hX'
    refine ⟨fun x Y => ∃ y B, R y B ∧ T x y ∧ Y = T ʻʻ B, pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩, ?_⟩
    · rintro x x' Y ⟨⟨y, B, hR1, hT1, rfl⟩, ⟨y', B', hR2, hT2, e⟩⟩
      have hB := pmB2_sel_codom hR hR1
      have hB' := pmB2_sel_codom hR hR2
      have eB : B = B' := Set.Subset.antisymm (imgInj B B' (subL B hB) (subL B' hB') e)
        (imgInj B' B (subL B' hB') (subL B hB) e.symm)
      subst eB
      have ey : y = y' := (pmB2_mem_sel.1 hR).1 _ _ _ ⟨hR1, hR2⟩
      subst ey
      exact h1 x x' y ⟨⟨hT1, subL B hB ((pmB2_mem_sel.1 hR).2.1 _ _ hR1)⟩,
        ⟨hT2, subL B hB ((pmB2_mem_sel.1 hR).2.1 _ _ hR1)⟩⟩
    · rintro x Y ⟨y, B, hR1, hT, rfl⟩
      exact ⟨y, (pmB2_mem_sel.1 hR).2.1 _ _ hR1, hT⟩
    · ext Y
      constructor
      · rintro ⟨x, y, B, hR1, -, rfl⟩
        exact ⟨B, pmB2_sel_codom hR hR1, rfl⟩
      · rintro ⟨B, hB, hY⟩
        have hY' : Y = T ʻʻ B := hY
        obtain ⟨y, hy⟩ := pmB2_sel_ex hR hB
        obtain ⟨x, hx⟩ := h3 (subL B hB ((pmB2_mem_sel.1 hR).2.1 _ _ hy))
        exact ⟨x, y, B, hy, hx, hY'⟩
    · ext x
      constructor
      · rintro ⟨y, ⟨B, hR1⟩, hT⟩
        exact ⟨_, y, B, hR1, hT, rfl⟩
      · rintro ⟨Y, y, B, hR1, hT, -⟩
        exact ⟨y, ⟨B, hR1⟩, hT⟩

/-- ✱115·4. \(\vdash : T \upharpoonright sʻ\lambda \in 1 \rightarrow 1 . sʻ\lambda \subset \text{ᗡ}ʻT . \supset . \text{Prod}ʻTʻʻʻ\lambda = Tʻʻʻ\text{Prod}ʻ\lambda\)

`T'''λ` is `T ʻʻʻ L`. -/
theorem pm115_4 {α β : Type*} {T : α → β → Prop} {L : Set (Set β)} :
    T ↾ sumCls L ∈ arrow one one ∧ sumCls L ⊆ codom T → prodK (T ʻʻʻ L) = T ʻʻʻ prodK L := by
  rintro ⟨h11, h3⟩
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 h11
  exact pmB2_prodK_natural (fun x x' y h => h1 x x' y h) (fun x y y' h => h2 x y y' h) h3

/-- ✱115·41. \[\begin{align}&\vdash \colon\ldotp R, S \in sʻ\lambda . \text{D}ʻR = \text{D}ʻS . \supset _{R, S} . R = S : \supset . \text{Prod}ʻ\text{D}ʻʻʻ\lambda = \text{D}ʻʻʻ\text{Prod}ʻ\lambda \\ &\left[*115·4 \frac{\text{D}}{T}. *71·55 . *72·13\right]\end{align}\]

`D'''λ` is `D ʻʻʻ L`. -/
theorem pm115_41 {α β : Type*} {L : Set (Set (α → β → Prop))} :
    (∀ R S, (R ∈ sumCls L ∧ S ∈ sumCls L) ∧ dom R = dom S → R = S) →
      prodK (D ʻʻʻ L) = D ʻʻʻ prodK L := by
  intro h
  refine pmB2_prodK_natural (fun x x' y ⟨⟨hx, _⟩, ⟨hx', _⟩⟩ => ?_)
    (fun x R S ⟨⟨hR, hRL⟩, ⟨hS, hSL⟩⟩ => ?_) (fun R _ => ⟨dom R, rfl⟩)
  · have e1 : x = dom y := hx
    have e2 : x' = dom y := hx'
    rw [e1, e2]
  · have e1 : x = dom R := hR
    have e2 : x = dom S := hS
    exact h R S ⟨⟨hRL, hSL⟩, e1.symm.trans e2⟩

/-- ✱115·42. \[\begin{align}\vdash : \kappa \in \text{Cls}^{3}\,\text{arithm} . \supset . \text{Prod}ʻ\text{Prod}ʻʻ\kappa &= \text{D}ʻʻʻ\text{Prod}ʻ{\in}_{\Delta}ʻʻ\kappa\\ &= \text{D}ʻʻʻ\text{D}ʻʻ{\in}_{\Delta}ʻ{\in}_{\Delta}ʻʻ\kappa\end{align}\]

The chain of identities is the conjunction of its links. -/
theorem pm115_42 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm → prodK (ProdK ʻʻ K) = D ʻʻʻ prodK (selRel memRel ʻʻ K) ∧
      D ʻʻʻ prodK (selRel memRel ʻʻ K) = D ʻʻʻ (D ʻʻ sel memRel (selRel memRel ʻʻ K)) := by
  intro hK3
  have hPD : ProdK ʻʻ K = D ʻʻʻ (selRel memRel ʻʻ K) := by
    ext P
    constructor
    · rintro ⟨A, hA, hP⟩
      exact ⟨sel memRel A, ⟨A, hA, rfl⟩, hP⟩
    · rintro ⟨Q, ⟨A, hA, hQ⟩, hP⟩
      have hQ' : Q = sel memRel A := hQ
      subst hQ'
      exact ⟨A, hA, hP⟩
  rw [hPD]
  exact ⟨pm115_41 fun R S ⟨⟨hR, hS⟩, e⟩ => pm115_3 ⟨⟨hK3, hR, hS⟩, e⟩, rfl⟩

private theorem pmB2_dom_sumRel {α β : Type*} (Y : Set (α → β → Prop)) :
    dom (sumRel Y) = sumCls (D ʻʻ Y) := by
  ext x
  constructor
  · rintro ⟨A, P, hP, hx⟩
    exact ⟨dom P, ⟨P, hP, rfl⟩, A, hx⟩
  · rintro ⟨Z, ⟨P, hP, hZ⟩, hxZ⟩
    have hZ' : Z = dom P := hZ
    rw [hZ'] at hxZ
    obtain ⟨A, hx⟩ := hxZ
    exact ⟨A, P, hP, hx⟩

/-- ✱115·43. \(\vdash : \kappa \in \text{Cls}^{2} \text{excl} . \supset . \text{Prod}ʻsʻ\kappa = sʻʻ\text{D}ʻʻʻ\text{D}ʻʻ{\in}_{\Delta}ʻ{\in}_{\Delta}ʻʻ\kappa\)

`s''…` is the image under `graph sumCls`. -/
theorem pm115_43 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls2excl →
      prodK (sumCls K) = graph sumCls ʻʻ (D ʻʻʻ (D ʻʻ sel memRel (selRel memRel ʻʻ K))) := by
  intro hK
  show D ʻʻ sel memRel (sumCls K) = _
  rw [pm115_151 hK]
  ext X
  constructor
  · rintro ⟨R, ⟨Y, hY, hR⟩, hX⟩
    have hR' : R = sumRel Y := hR
    have hX' : X = dom R := hX
    subst hR'
    exact ⟨D ʻʻ Y, ⟨Y, hY, rfl⟩, hX'.trans (pmB2_dom_sumRel Y)⟩
  · rintro ⟨Z, ⟨Y, hY, hZ⟩, hX⟩
    have hZ' : Z = D ʻʻ Y := hZ
    have hX' : X = sumCls Z := hX
    subst hZ'
    exact ⟨sumRel Y, ⟨Y, hY, rfl⟩, hX'.trans (pmB2_dom_sumRel Y).symm⟩

/-- ✱115·44. \(\vdash : \kappa \in \text{Cls}^{3}\,\text{arithm} . \supset . \text{Prod}ʻsʻ\kappa = sʻʻ\text{Prod}ʻ\text{Prod}ʻʻ\kappa \quad[*115·43·42]\) -/
theorem pm115_44 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm → prodK (sumCls K) = graph sumCls ʻʻ prodK (ProdK ʻʻ K) := by
  intro hK3
  rw [(pm115_42 hK3).1, (pm115_42 hK3).2]
  exact pm115_43 hK3.1

/-- ✱115·45. \[\begin{align}\vdash \colon\ldotp \alpha ,\beta \in \kappa .\exists !&sʻ\alpha \cap sʻ\beta .\supset _{\alpha ,\beta }.\alpha =\beta :\supset .\\ &(s\mid \text{D})\upharpoonright {\in}_{\Delta}ʻ\kappa \in 1\rightarrow 1.s\upharpoonright \text{Prod}ʻ\kappa \in 1\rightarrow 1\end{align}\]

`s | D` is `graph sumCls ⨾ D`; `s ↾ Prod'κ` is `graph sumCls ↾ prodK K`. -/
theorem pm115_45 {α : Type*} {K : Set (Set (Set α))} :
    (∀ A B, (A ∈ K ∧ B ∈ K) ∧ (sumCls A ∩ sumCls B).Nonempty → A = B) →
      (graph sumCls ⨾ D) ↾ sel memRel K ∈ arrow one one ∧
        graph sumCls ↾ prodK K ∈ arrow one one := by
  intro H
  have cell : ∀ R, R ∈ sel memRel K → ∀ ξ A, R ξ A → ξ = sumCls (dom R) ∩ sumCls A := by
    intro R hR ξ A hξ
    have hA := pmB2_sel_codom hR hξ
    have hξA : ξ ∈ A := (pmB2_mem_sel.1 hR).2.1 _ _ hξ
    ext x
    constructor
    · intro hx; exact ⟨⟨ξ, ⟨A, hξ⟩, hx⟩, ⟨ξ, hξA, hx⟩⟩
    · rintro ⟨⟨η, ⟨B, hη⟩, hxη⟩, ⟨ζ, hζ, hxζ⟩⟩
      have hB := pmB2_sel_codom hR hη
      have e : B = A := H B A ⟨⟨hB, hA⟩, x, ⟨η, (pmB2_mem_sel.1 hR).2.1 _ _ hη, hxη⟩,
        ⟨ζ, hζ, hxζ⟩⟩
      subst e
      rw [(pmB2_mem_sel.1 hR).1 _ _ _ ⟨hξ, hη⟩]; exact hxη
  have key : ∀ R S, R ∈ sel memRel K → S ∈ sel memRel K →
      sumCls (dom R) = sumCls (dom S) → R = S := by
    have half : ∀ R S, R ∈ sel memRel K → S ∈ sel memRel K →
        sumCls (dom R) = sumCls (dom S) → ∀ ξ A, R ξ A → S ξ A := by
      intro R S hR hS e ξ A hξ
      obtain ⟨ξ', hξ'⟩ := pmB2_sel_ex hS (pmB2_sel_codom hR hξ)
      rw [cell R hR ξ A hξ, e, ← cell S hS ξ' A hξ']
      exact hξ'
    intro R S hR hS e
    funext ξ A
    exact propext ⟨half R S hR hS e ξ A, half S R hS hR e.symm ξ A⟩
  refine ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, mem_arrow_one_one.2 ⟨?_, ?_⟩⟩
  · rintro X X' R ⟨⟨⟨Y, hX, hY⟩, -⟩, ⟨⟨Y', hX', hY'⟩, -⟩⟩
    have e1 : X = sumCls Y := hX
    have e2 : Y = dom R := hY
    have e3 : X' = sumCls Y' := hX'
    have e4 : Y' = dom R := hY'
    rw [e1, e3, e2, e4]
  · rintro X R S ⟨⟨⟨Y, hX, hY⟩, hR⟩, ⟨⟨Y', hX', hY'⟩, hS⟩⟩
    have e1 : X = sumCls Y := hX
    have e2 : Y = dom R := hY
    have e3 : X = sumCls Y' := hX'
    have e4 : Y' = dom S := hY'
    exact key R S hR hS (by rw [← e2, ← e4, ← e1, ← e3])
  · rintro X X' Y ⟨⟨hX, -⟩, ⟨hX', -⟩⟩
    have e1 : X = sumCls Y := hX
    have e2 : X' = sumCls Y := hX'
    rw [e1, e2]
  · rintro X Y Y' ⟨⟨hX, ⟨R, hR, rfl⟩⟩, ⟨hX', ⟨S, hS, rfl⟩⟩⟩
    have e1 : X = sumCls (dom R) := hX
    have e2 : X = sumCls (dom S) := hX'
    rw [key R S hR hS (e1.symm.trans e2)]

/-- ✱115·46. \(\vdash :\kappa \in \text{Cls}^{3}\,\text{arithm}.\supset .s\upharpoonright \text{Prod}ʻ\text{Prod}ʻʻ\kappa \in 1\rightarrow 1\) -/
theorem pm115_46 {α : Type*} {K : Set (Set (Set α))} :
    K ∈ Cls3arithm → graph sumCls ↾ prodK (ProdK ʻʻ K) ∈ arrow one one := by
  intro hK3
  refine (pm115_45 ?_).2
  rintro P P' ⟨⟨⟨A, hA, hP⟩, ⟨B, hB, hP'⟩⟩, x, ⟨ξ, hξ, hxξ⟩, ⟨η, hη, hxη⟩⟩
  have e1 : P = prodK A := hP
  have e2 : P' = prodK B := hP'
  subst e1; subst e2
  obtain ⟨R, hR, rfl⟩ := hξ
  obtain ⟨S, hS, rfl⟩ := hη
  rw [(pm115_22 hK3).2 A B ⟨⟨hA, hB⟩, x, pmB2_dom_sel_sub hR hxξ, pmB2_dom_sel_sub hS hxη⟩]

private theorem pmB2_img_cres {α β : Type*} {T : α → β → Prop} {B C : Set β} (h : B ⊆ C) :
    (T ↾ C) ʻʻ B = T ʻʻ B := by
  ext x
  exact ⟨fun ⟨y, hy, hT, _⟩ => ⟨y, hy, hT⟩, fun ⟨y, hy, hT⟩ => ⟨y, hy, hT, h hy⟩⟩

private theorem pmB2_smsmbar_prodK {α β : Type*} {T : α → β → Prop} {K : Set (Set α)}
    {L : Set (Set β)} (h : T ↾ sumCls L ∈ smsmbar K L) :
    prodK K = imgRel (T ↾ sumCls L) ʻʻ prodK L := by
  obtain ⟨⟨h11, hcod⟩, hK⟩ := h
  have hcod' : sumCls L = codom (T ↾ sumCls L) := hcod
  have hK' : K = imgRel (T ↾ sumCls L) ʻʻ L := hK
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 h11
  rw [hK']
  exact pmB2_prodK_natural (fun x x' y ⟨⟨hx, _⟩, ⟨hx', _⟩⟩ => h1 x x' y ⟨hx, hx'⟩)
    (fun x y y' ⟨⟨hy, _⟩, ⟨hy', _⟩⟩ => h2 x y y' ⟨hy, hy'⟩) (fun y hy => hcod' ▸ hy)

/-- ✱115·5. \(\vdash :T\upharpoonright sʻ\lambda \in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda .\supset .\text{Prod}ʻ\kappa =T_{\in }ʻʻ\text{Prod}ʻ\lambda \quad[*115·4.*111·14]\)

`T_∈''Prod'λ` is `imgRel T ʻʻ prodK L`. -/
theorem pm115_5 {α β : Type*} {T : α → β → Prop} {K : Set (Set α)} {L : Set (Set β)} :
    T ↾ sumCls L ∈ smsmbar K L → prodK K = imgRel T ʻʻ prodK L := by
  intro h
  rw [pmB2_smsmbar_prodK h]
  ext X
  constructor
  · rintro ⟨ξ, hξ, hX⟩
    have hX' : X = (T ↾ sumCls L) ʻʻ ξ := hX
    obtain ⟨R, hR, rfl⟩ := hξ
    exact ⟨dom R, ⟨R, hR, rfl⟩, hX'.trans (pmB2_img_cres (pmB2_dom_sel_sub hR))⟩
  · rintro ⟨ξ, hξ, hX⟩
    have hX' : X = T ʻʻ ξ := hX
    obtain ⟨R, hR, rfl⟩ := hξ
    exact ⟨dom R, ⟨R, hR, rfl⟩, hX'.trans (pmB2_img_cres (pmB2_dom_sel_sub hR)).symm⟩

/-- ✱115·501. \[\begin{align}&\vdash :T\upharpoonright sʻ\lambda \in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda .\exists !\text{Prod}ʻ\lambda .\supset .T\upharpoonright sʻ\lambda \in (\text{Prod}ʻ\kappa )\,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, (\text{Prod}ʻ\lambda )\\ &[*115·5·141.*111·14]\end{align}\] -/
theorem pm115_501 {α β : Type*} {T : α → β → Prop} {K : Set (Set α)} {L : Set (Set β)} :
    T ↾ sumCls L ∈ smsmbar K L ∧ (prodK L).Nonempty →
      T ↾ sumCls L ∈ smsmbar (prodK K) (prodK L) := by
  rintro ⟨h, hne⟩
  have hP := pmB2_smsmbar_prodK h
  obtain ⟨⟨h11, hcod⟩, -⟩ := h
  refine ⟨⟨h11, ?_⟩, hP⟩
  show sumCls (prodK L) = codom _
  rw [pm115_141 hne]
  exact hcod

/-- ✱115·502. \(\vdash :T\upharpoonright sʻ\lambda \in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda .\supset .T\upharpoonright sʻ\text{Prod}ʻ\lambda \in (\text{Prod}ʻ\kappa )\,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, (\text{Prod}ʻ\lambda )\) -/
theorem pm115_502 {α β : Type*} {T : α → β → Prop} {K : Set (Set α)} {L : Set (Set β)} :
    T ↾ sumCls L ∈ smsmbar K L → T ↾ sumCls (prodK L) ∈ smsmbar (prodK K) (prodK L) := by
  intro h
  by_cases hne : (prodK L).Nonempty
  · rw [pm115_141 hne]; exact pm115_501 ⟨h, hne⟩
  · have hL : prodK L = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    have hK : prodK K = ∅ := by
      rw [pmB2_smsmbar_prodK h, hL]
      ext X; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨ξ, hξ, -⟩; exact hξ
    have hs : sumCls (prodK L) = ∅ := by
      rw [hL]; ext x; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨A, hA, -⟩; exact hA
    refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rintro x y z ⟨⟨-, hz⟩, -⟩; rw [hs] at hz; exact hz.elim
    · rintro x y z ⟨⟨-, hy⟩, -⟩; rw [hs] at hy; exact hy.elim
    · show sumCls (prodK L) = codom _
      rw [hs]; ext y; simp only [Set.mem_empty_iff_false, false_iff]
      rintro ⟨x, -, hy⟩; exact hy
    · show prodK K = _
      rw [hK, hL]
      ext X; simp only [Set.mem_empty_iff_false, false_iff]
      rintro ⟨ξ, hξ, -⟩; exact hξ

/-- ✱115·51. \(\vdash : \kappa \text{ sm } \text{ sm } \lambda . \supset . \text{Prod}ʻ\kappa \text{ sm } \text{ sm } \text{Prod}ʻ\lambda \quad[*115·502]\) -/
theorem pm115_51 {α β : Type*} {K : Set (Set α)} {L : Set (Set β)} :
    smsm K L → smsm (prodK K) (prodK L) := by
  rintro ⟨T, hT⟩
  have hcod : sumCls L = codom T := hT.1.2
  have hres : T ↾ sumCls L = T := by
    funext x y
    exact propext ⟨fun h => h.1, fun h => ⟨h, hcod ▸ ⟨x, h⟩⟩⟩
  have hT' : T ↾ sumCls L ∈ smsmbar K L := by rw [hres]; exact hT
  exact ⟨_, pm115_502 hT'⟩

/-- The value `R'z` when it exists (the union of the referents of `z`). -/
private def pmB2_rv {α δ : Type*} (R : Set α → δ → Prop) (z : δ) : Set α := sumCls (refs R z)

private theorem pmB2_rv_spec {α δ : Type*} {R : Set α → δ → Prop} {G : Set δ}
    (hu : ∀ a a' z, z ∈ G → R a z → R a' z → a = a') (h3 : G ⊆ codom R) {z : δ} (hz : z ∈ G) :
    R (pmB2_rv R z) z ∧ ∀ a, R a z → a = pmB2_rv R z := by
  obtain ⟨a, ha⟩ := h3 hz
  have e : pmB2_rv R z = a := by
    ext x
    constructor
    · rintro ⟨a', ha', hx⟩
      rw [hu a' a z hz ha' ha] at hx; exact hx
    · intro hx; exact ⟨a, ha, hx⟩
  rw [e]
  exact ⟨ha, fun a' ha' => hu a' a z hz ha' ha⟩

private theorem pmB2_rv_inj {α δ : Type*} {R : Set α → δ → Prop} {G : Set δ}
    (hu : ∀ a a' z, z ∈ G → R a z → R a' z → a = a')
    (hi : ∀ a z z', z ∈ G → z' ∈ G → R a z → R a z' → z = z') (h3 : G ⊆ codom R) :
    Set.InjOn (pmB2_rv R) G := by
  intro z hz z' hz' e
  have h1 := (pmB2_rv_spec hu h3 hz).1
  have h2 := (pmB2_rv_spec hu h3 hz').1
  rw [e] at h1
  exact hi _ z z' hz hz' h1 h2

private theorem pmB2_rv_img {α δ : Type*} {R : Set α → δ → Prop} {G : Set δ}
    (hu : ∀ a a' z, z ∈ G → R a z → R a' z → a = a') (h3 : G ⊆ codom R) :
    R ʻʻ G = pmB2_rv R '' G := by
  ext X
  constructor
  · rintro ⟨z, hz, hX⟩
    exact ⟨z, hz, ((pmB2_rv_spec hu h3 hz).2 X hX).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (pmB2_rv_spec hu h3 hz).1⟩

private theorem pmB2_rv_desc {α δ : Type*} {R : Set α → δ → Prop} {G : Set δ}
    (hu : ∀ a a' z, z ∈ G → R a z → R a' z → a = a') (h3 : G ⊆ codom R) {z : δ} (hz : z ∈ G)
    (ψ : Set α → Prop) : Desc R z ψ ↔ ψ (pmB2_rv R z) := by
  obtain ⟨h1, h2⟩ := pmB2_rv_spec hu h3 hz
  exact TheIs_iff_of_unique fun a => ⟨h2 a, fun e => e ▸ h1⟩

/-- The hypothesis of ✱114·64, ✱115·6–·63, unfolded. -/
private structure pmB2_Hyp6 {α β δ : Type*} (R : Set α → δ → Prop) (S : Set β → δ → Prop) (G : Set δ) :
    Prop where
  uR : ∀ a a' z, z ∈ G → R a z → R a' z → a = a'
  iR : ∀ a z z', z ∈ G → z' ∈ G → R a z → R a z' → z = z'
  uS : ∀ a a' z, z ∈ G → S a z → S a' z → a = a'
  iS : ∀ a z z', z ∈ G → z' ∈ G → S a z → S a z' → z = z'
  cR : G ⊆ codom R
  cS : G ⊆ codom S

private theorem pmB2_hyp6_of {α β δ : Type*} {R : Set α → δ → Prop} {S : Set β → δ → Prop} {G : Set δ}
    (h : (((R ʻʻ G) ◁ R ∈ arrow one one ∧ S ↾ G ∈ arrow one one) ∧ G ⊆ codom R) ∧
      G ⊆ codom S) : pmB2_Hyp6 R S G := by
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨a1, b1⟩ := mem_arrow_one_one.1 h1
  obtain ⟨a2, b2⟩ := mem_arrow_one_one.1 h2
  exact ⟨fun a a' z hz ha ha' => a1 a a' z ⟨⟨⟨z, hz, ha⟩, ha⟩, ⟨⟨z, hz, ha'⟩, ha'⟩⟩,
    fun a z z' hz _ ha ha' => b1 a z z' ⟨⟨⟨z, hz, ha⟩, ha⟩, ⟨⟨z, hz, ha⟩, ha'⟩⟩,
    fun a a' z hz ha ha' => a2 a a' z ⟨⟨ha, hz⟩, ⟨ha', hz⟩⟩,
    fun a z z' hz hz' ha ha' => b2 a z z' ⟨⟨ha, hz⟩, ⟨ha', hz'⟩⟩, h3, h4⟩

private theorem pmB2_M_eq {α β δ : Type*} {R : Set α → δ → Prop} {S : Set β → δ → Prop} {G : Set δ}
    (H : pmB2_Hyp6 R S G) :
    {μ | ∃ z, z ∈ G ∧ Desc R z (fun a => Desc S z (fun b => μ = a ×ₐ b))} =
      (fun z => pmB2_rv R z ×ₐ pmB2_rv S z) '' G := by
  ext μ
  constructor
  · rintro ⟨z, hz, h⟩
    rw [pmB2_rv_desc H.uR H.cR hz, pmB2_rv_desc H.uS H.cS hz] at h
    exact ⟨z, hz, h.symm⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [pmB2_rv_desc H.uR H.cR hz, pmB2_rv_desc H.uS H.cS hz]

private theorem pmB2_clsTimes_empty {α β : Type*} {A : Set α} {B : Set β} (h : A = ∅ ∨ B = ∅) :
    B ×ₐ A = ∅ := by
  ext R
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hR
  obtain ⟨x, y, ⟨hx, hy⟩, -⟩ := pmB2_mem_clsTimes.1 hR
  rcases h with rfl | rfl
  · exact hx
  · exact hy

/-- The selections from `μ̂{(∃z) . z ∈ γ . μ = R'z × S'z}` (all factors non-empty). -/
private noncomputable def pmB2_selM {α β δ : Type*} {R : Set α → δ → Prop} {S : Set β → δ → Prop}
    {G : Set δ} (H : pmB2_Hyp6 R S G) (_hne : ∀ z, z ∈ G → (pmB2_rv R z).Nonempty)
    (hne' : ∀ z, z ∈ G → (pmB2_rv S z).Nonempty) :
    ↥(sel memRel ((fun z => pmB2_rv R z ×ₐ pmB2_rv S z) '' G)) ≃
      ((z : ↥G) → ↥(pmB2_rv S z)) × ((z : ↥G) → ↥(pmB2_rv R z)) := by
  have hinj : Set.InjOn (fun z => pmB2_rv R z ×ₐ pmB2_rv S z) G := by
    intro z hz z' hz' e
    apply pmB2_rv_inj H.uR H.iR H.cR hz hz'
    have key : ∀ z z', z ∈ G → (pmB2_rv R z ×ₐ pmB2_rv S z = pmB2_rv R z' ×ₐ pmB2_rv S z') →
        pmB2_rv R z ⊆ pmB2_rv R z' := by
      intro z z' hz e y hy
      obtain ⟨x, hx⟩ := hne' z hz
      have : x ↓ y ∈ pmB2_rv R z' ×ₐ pmB2_rv S z' := e ▸ couple_mem_clsTimes.2 ⟨hx, hy⟩
      exact (couple_mem_clsTimes.1 this).2
    exact Set.Subset.antisymm (key z z' hz e) (key z' z hz' e.symm)
  exact (pmB2_selE _).trans ((pmB2_piImage _ G hinj (fun μ => ↥(μ : Set (β → α → Prop)))).trans
    ((Equiv.piCongrRight fun z : ↥G => pmB2_clsTimesEquiv (pmB2_rv S z) (pmB2_rv R z)).trans
      (show ((z : ↥G) → ↥(pmB2_rv S z) × ↥(pmB2_rv R z)) ≃
          ((z : ↥G) → ↥(pmB2_rv S z)) × ((z : ↥G) → ↥(pmB2_rv R z)) from
        { toFun := fun f => (fun z => (f z).1, fun z => (f z).2)
          invFun := fun p z => (p.1 z, p.2 z)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl })))

/-- ✱115·6. \[\begin{align}\vdash : &(Rʻʻ\gamma ) \upharpoonleft R, S \upharpoonright \gamma \in 1 \rightarrow 1 . \gamma \subset \text{ᗡ}ʻR . \gamma \subset \text{ᗡ}ʻS . Rʻʻ\gamma , Sʻʻ\gamma \in \text{Cls}^{2} \text{excl} . \supset .\\ &\text{Prod}ʻRʻʻ\gamma \times \text{Prod}ʻSʻʻ\gamma \text{ sm } {\in}_{\Delta}ʻ\hat{\mu} \{(\exists z) . z \in \gamma . \mu = Rʻz \times Sʻz\}\end{align}\]

`(R''γ) ↿ R, S ↾ γ ∈ 1 → 1` is the conjunction of `(R ʻʻ G) ◁ R ∈ 1 → 1` and `S ↾ G ∈ 1 → 1`
(two relations; cf. the proof of ✱114·64); `R''γ, S''γ ∈ Cls² excl` likewise. `R'z × S'z`
contains two descriptions, the first with the larger scope (Basic §5); they exist by the
hypothesis. `γ` is `G : Set δ`. -/
theorem pm115_6 {α β δ : Type*} {R : Set α → δ → Prop} {S : Set β → δ → Prop} {G : Set δ} :
    ((((R ʻʻ G) ◁ R ∈ arrow one one ∧ S ↾ G ∈ arrow one one) ∧ G ⊆ codom R) ∧ G ⊆ codom S) ∧
        (R ʻʻ G ∈ Cls2excl ∧ S ʻʻ G ∈ Cls2excl) →
      sm (prodK (R ʻʻ G) ×ₐ prodK (S ʻʻ G))
        (sel memRel {μ | ∃ z, z ∈ G ∧ Desc R z (fun a => Desc S z (fun b => μ = a ×ₐ b))}) := by
  rintro ⟨h, hRe, hSe⟩
  have H := pmB2_hyp6_of h
  rw [pmB2_M_eq H]
  by_cases hne : (∀ z, z ∈ G → (pmB2_rv R z).Nonempty) ∧ ∀ z, z ∈ G → (pmB2_rv S z).Nonempty
  · obtain ⟨hne, hne'⟩ := hne
    have eR : ↥(prodK (R ʻʻ G)) ≃ ((z : ↥G) → ↥(pmB2_rv R z)) := by
      refine (pmB2_prodEquiv hRe).trans ((pmB2_selE _).trans ?_)
      rw [pmB2_rv_img H.uR H.cR]
      exact pmB2_piImage _ G (pmB2_rv_inj H.uR H.iR H.cR) (fun X => ↥(X : Set α))
    have eS : ↥(prodK (S ʻʻ G)) ≃ ((z : ↥G) → ↥(pmB2_rv S z)) := by
      refine (pmB2_prodEquiv hSe).trans ((pmB2_selE _).trans ?_)
      rw [pmB2_rv_img H.uS H.cS]
      exact pmB2_piImage _ G (pmB2_rv_inj H.uS H.iS H.cS) (fun X => ↥(X : Set β))
    exact pmB2_sm_of_equiv (((pmB2_clsTimesEquiv _ _).trans (Equiv.prodCongr eS eR)).trans
      (pmB2_selM H hne hne').symm)
  · rw [not_and_or] at hne
    have hz : ∃ z, z ∈ G ∧ (pmB2_rv R z = ∅ ∨ pmB2_rv S z = ∅) := by
      rcases hne with h | h <;> push Not at h <;> obtain ⟨z, hz, h⟩ := h
      · exact ⟨z, hz, Or.inl h⟩
      · exact ⟨z, hz, Or.inr h⟩
    obtain ⟨z, hz, h0⟩ := hz
    refine pmB2_sm_empty (pmB2_clsTimes_empty ?_) (pmB2_sel_empty_of ⟨z, hz, ?_⟩)
    · rcases h0 with h0 | h0
      · right
        refine pmB2_prodK_empty_of ?_
        rw [pmB2_rv_img H.uR H.cR, ← h0]
        exact ⟨z, hz, rfl⟩
      · left
        refine pmB2_prodK_empty_of ?_
        rw [pmB2_rv_img H.uS H.cS, ← h0]
        exact ⟨z, hz, rfl⟩
    · exact pmB2_clsTimes_empty (h0.symm.imp id id)

/-- ✱115·601. \[\begin{align}\vdash : (Rʻʻ\gamma ) &\upharpoonleft R, S \upharpoonright \gamma \in 1 \rightarrow 1 . \gamma \subset \text{ᗡ}ʻR . \gamma \subset \text{ᗡ}ʻS . Rʻʻ\gamma \in \text{Cls}^{2} \text{excl} . \supset .\\ &\hat{\mu} \{(\exists z) . z \in \gamma . \mu = Rʻz \times Sʻz\} \in \text{Cls}^{2} \text{excl}\end{align}\] -/
theorem pm115_601 {α β δ : Type*} {R : Set α → δ → Prop} {S : Set β → δ → Prop} {G : Set δ} :
    ((((R ʻʻ G) ◁ R ∈ arrow one one ∧ S ↾ G ∈ arrow one one) ∧ G ⊆ codom R) ∧ G ⊆ codom S) ∧
        R ʻʻ G ∈ Cls2excl →
      {μ | ∃ z, z ∈ G ∧ Desc R z (fun a => Desc S z (fun b => μ = a ×ₐ b))} ∈ Cls2excl := by
  rintro ⟨h, hRe⟩
  have H := pmB2_hyp6_of h
  rw [pmB2_M_eq H, pmB2_excl_iff]
  rintro _ _ c ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩ hc hc'
  obtain ⟨x, y, ⟨-, hy⟩, rfl⟩ := pmB2_mem_clsTimes.1 hc
  have hy' := (couple_mem_clsTimes.1 hc').2
  rw [pmB2_rv_img H.uR H.cR] at hRe
  have e := pmB2_excl_iff.1 hRe _ _ y ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩ hy hy'
  rw [pmB2_rv_inj H.uR H.iR H.cR hz hz' e]

/-- ✱115·602. \[\begin{align}\vdash : &(Rʻʻ\gamma ) \upharpoonleft R, S \upharpoonright \gamma \in 1 \rightarrow 1 . \gamma \subset \text{ᗡ}ʻR . \gamma \subset \text{ᗡ}ʻS . Sʻʻ\gamma \in \text{Cls}^{2} \text{excl} . \supset .\\ &\hat{\mu} \{(\exists z) . z \in \gamma . \mu = Rʻz \times Sʻz\} \in \text{Cls}^{2} \text{excl}\\ &[\text{Proof as in *115·601}]\end{align}\] -/
theorem pm115_602 {α β δ : Type*} {R : Set α → δ → Prop} {S : Set β → δ → Prop} {G : Set δ} :
    ((((R ʻʻ G) ◁ R ∈ arrow one one ∧ S ↾ G ∈ arrow one one) ∧ G ⊆ codom R) ∧ G ⊆ codom S) ∧
        S ʻʻ G ∈ Cls2excl →
      {μ | ∃ z, z ∈ G ∧ Desc R z (fun a => Desc S z (fun b => μ = a ×ₐ b))} ∈ Cls2excl := by
  rintro ⟨h, hSe⟩
  have H := pmB2_hyp6_of h
  rw [pmB2_M_eq H, pmB2_excl_iff]
  rintro _ _ c ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩ hc hc'
  obtain ⟨x, y, ⟨hx, -⟩, rfl⟩ := pmB2_mem_clsTimes.1 hc
  have hx' := (couple_mem_clsTimes.1 hc').1
  rw [pmB2_rv_img H.uS H.cS] at hSe
  have e := pmB2_excl_iff.1 hSe _ _ x ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩ hx hx'
  rw [pmB2_rv_inj H.uS H.iS H.cS hz hz' e]

/-- ✱115·61. \[\begin{align}\vdash \colon\ldotp &(Rʻʻ\gamma ) \upharpoonleft R, S \upharpoonright \gamma \in 1 \rightarrow 1 . \gamma \subset \text{ᗡ}ʻR . \gamma \subset \text{ᗡ}ʻS . Rʻʻ\gamma \cap Sʻʻ\gamma = \Lambda :\\ &Rʻʻ\gamma \in \text{Cls}^{2} \text{excl} . \lor . Sʻʻ\gamma \in \text{Cls}^{2} \text{excl} : \supset .\\ &{\in}_{\Delta}ʻ(Rʻʻ\gamma \cup Sʻʻ\gamma ) \text{ sm } \text{Prod}ʻ\hat{\mu} \{(\exists z) . z \in \gamma . \mu = Rʻz \times Sʻz\}\\ &[*115·601·602·12 . *114·65]\end{align}\]

Here `R''γ ∪ S''γ` makes `R` and `S` of one type. -/
theorem pm115_61 {α δ : Type*} {R S : Set α → δ → Prop} {G : Set δ} :
    (((((R ʻʻ G) ◁ R ∈ arrow one one ∧ S ↾ G ∈ arrow one one) ∧ G ⊆ codom R) ∧ G ⊆ codom S) ∧
        R ʻʻ G ∩ S ʻʻ G = Λ) ∧ (R ʻʻ G ∈ Cls2excl ∨ S ʻʻ G ∈ Cls2excl) →
      sm (sel memRel (R ʻʻ G ∪ S ʻʻ G))
        (prodK {μ | ∃ z, z ∈ G ∧ Desc R z (fun a => Desc S z (fun b => μ = a ×ₐ b))}) := by
  rintro ⟨⟨h, hdis⟩, hex⟩
  have hMe : {μ | ∃ z, z ∈ G ∧ Desc R z (fun a => Desc S z (fun b => μ = a ×ₐ b))} ∈
      Cls2excl := by
    rcases hex with hex | hex
    · exact pm115_601 ⟨h, hex⟩
    · exact pm115_602 ⟨h, hex⟩
  have H := pmB2_hyp6_of h
  rw [pmB2_M_eq H] at hMe ⊢
  rw [Null_eq_empty, pmB2_rv_img H.uR H.cR, pmB2_rv_img H.uS H.cS] at hdis
  rw [pmB2_rv_img H.uR H.cR, pmB2_rv_img H.uS H.cS]
  by_cases hne : (∀ z, z ∈ G → (pmB2_rv R z).Nonempty) ∧ ∀ z, z ∈ G → (pmB2_rv S z).Nonempty
  · obtain ⟨hne, hne'⟩ := hne
    have hd : ∀ z z', z ∈ G → z' ∈ G → pmB2_rv R z ≠ pmB2_rv S z' := fun z z' hz hz' e =>
      (Set.eq_empty_iff_forall_notMem.1 hdis) _ ⟨⟨z, hz, rfl⟩, ⟨z', hz', e.symm⟩⟩
    let g : ↥G ⊕ ↥G → ↥(pmB2_rv R '' G ∪ pmB2_rv S '' G) :=
      Sum.elim (fun z => ⟨pmB2_rv R z, Or.inl ⟨z, z.2, rfl⟩⟩)
        (fun z => ⟨pmB2_rv S z, Or.inr ⟨z, z.2, rfl⟩⟩)
    have hg : Function.Bijective g := by
      constructor
      · rintro (z | z) (z' | z') e
        · have e' : pmB2_rv R z = pmB2_rv R z' := congrArg Subtype.val e
          exact congrArg Sum.inl (Subtype.ext (pmB2_rv_inj H.uR H.iR H.cR z.2 z'.2 e'))
        · have e' : pmB2_rv R z = pmB2_rv S z' := congrArg Subtype.val e
          exact (hd z z' z.2 z'.2 e').elim
        · have e' : pmB2_rv S z = pmB2_rv R z' := congrArg Subtype.val e
          exact (hd z' z z'.2 z.2 e'.symm).elim
        · have e' : pmB2_rv S z = pmB2_rv S z' := congrArg Subtype.val e
          exact congrArg Sum.inr (Subtype.ext (pmB2_rv_inj H.uS H.iS H.cS z.2 z'.2 e'))
      · rintro ⟨X, ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩⟩
        · exact ⟨Sum.inl ⟨z, hz⟩, rfl⟩
        · exact ⟨Sum.inr ⟨z, hz⟩, rfl⟩
    have e1 : ↥(sel memRel (pmB2_rv R '' G ∪ pmB2_rv S '' G)) ≃
        ((z : ↥G) → ↥(pmB2_rv S z)) × ((z : ↥G) → ↥(pmB2_rv R z)) :=
      (pmB2_selE _).trans (((Equiv.piCongrLeft (fun X : ↥(pmB2_rv R '' G ∪ pmB2_rv S '' G) =>
        ↥(X : Set α)) (Equiv.ofBijective g hg)).symm.trans
          (Equiv.sumPiEquivProdPi _)).trans (Equiv.prodComm _ _))
    exact pmB2_sm_of_equiv (e1.trans ((pmB2_selM H hne hne').symm.trans
      (pmB2_prodEquiv hMe).symm))
  · rw [not_and_or] at hne
    have hz : ∃ z, z ∈ G ∧ (pmB2_rv R z = ∅ ∨ pmB2_rv S z = ∅) := by
      rcases hne with h | h <;> push Not at h <;> obtain ⟨z, hz, h⟩ := h
      · exact ⟨z, hz, Or.inl h⟩
      · exact ⟨z, hz, Or.inr h⟩
    obtain ⟨z, hz, h0⟩ := hz
    refine pmB2_sm_empty (pmB2_sel_empty_of ?_) (pmB2_prodK_empty_of ⟨z, hz, ?_⟩)
    · rcases h0 with h0 | h0
      · exact Or.inl ⟨z, hz, h0⟩
      · exact Or.inr ⟨z, hz, h0⟩
    · exact pmB2_clsTimes_empty (h0.symm.imp id id)

/-- ✱115·62. \[\begin{align}\vdash : &(Rʻʻ\gamma ) \upharpoonleft R, S \upharpoonright \gamma \in 1 \rightarrow 1 . \gamma \subset \text{ᗡ}ʻR . \gamma \subset \text{ᗡ}ʻS . Rʻʻ\gamma \cap Sʻʻ\gamma = \Lambda .\\ &(Rʻʻ\gamma \cup Sʻʻ\gamma ) \in \text{Cls}^{2} \text{excl} . \supset .\\ &\text{Prod}ʻ(Rʻʻ\gamma \cup Sʻʻ\gamma ) \text{ sm } \text{Prod}ʻ\hat{\mu} \{(\exists z) . z \in \gamma . \mu = Rʻz \times Sʻz\}\\ &[*115·61·12 . *84·25]\end{align}\] -/
theorem pm115_62 {α δ : Type*} {R S : Set α → δ → Prop} {G : Set δ} :
    (((((R ʻʻ G) ◁ R ∈ arrow one one ∧ S ↾ G ∈ arrow one one) ∧ G ⊆ codom R) ∧ G ⊆ codom S) ∧
        R ʻʻ G ∩ S ʻʻ G = Λ) ∧ (R ʻʻ G ∪ S ʻʻ G) ∈ Cls2excl →
      sm (prodK (R ʻʻ G ∪ S ʻʻ G))
        (prodK {μ | ∃ z, z ∈ G ∧ Desc R z (fun a => Desc S z (fun b => μ = a ×ₐ b))}) := by
  rintro ⟨h, hex⟩
  exact sm_trans (pmB2_sm_of_equiv (pmB2_prodEquiv hex))
    (pm115_61 ⟨h, Or.inl (pmB2_excl_subset hex Set.subset_union_left)⟩)

/-- ✱115·63. \[\begin{align}&\vdash : (Rʻʻ\gamma ) \upharpoonleft R, S \upharpoonright \gamma \in 1 \rightarrow 1 . \gamma \subset \text{ᗡ}ʻR . \gamma \subset \text{ᗡ}ʻS . Rʻʻ\gamma , Sʻʻ\gamma \in \text{Cls}^{2} \text{excl} . \supset .\\ &\text{Prod}ʻRʻʻ\gamma \times \text{Prod}ʻSʻʻ\gamma \text{ sm } \text{Prod}ʻ\hat{\mu}\{(\exists z) . z \in \gamma . \mu = Rʻz \times Sʻz\}\\ &[*115·6·601·12]\end{align} \] -/
theorem pm115_63 {α β δ : Type*} {R : Set α → δ → Prop} {S : Set β → δ → Prop} {G : Set δ} :
    ((((R ʻʻ G) ◁ R ∈ arrow one one ∧ S ↾ G ∈ arrow one one) ∧ G ⊆ codom R) ∧ G ⊆ codom S) ∧
        (R ʻʻ G ∈ Cls2excl ∧ S ʻʻ G ∈ Cls2excl) →
      sm (prodK (R ʻʻ G) ×ₐ prodK (S ʻʻ G))
        (prodK {μ | ∃ z, z ∈ G ∧ Desc R z (fun a => Desc S z (fun b => μ = a ×ₐ b))}) := by
  rintro ⟨h, hRe, hSe⟩
  exact sm_trans (pm115_6 ⟨h, hRe, hSe⟩)
    (sm_symm (pmB2_sm_of_equiv (pmB2_prodEquiv (pm115_601 ⟨h, hRe⟩))))

/-!
## [✱116] Exponentiation

*(Vol. 2, p. 143)*

> *Summary of* *116.
>
> In this number, we define "\(\alpha\, \,\text{exp}\,\, \beta\)," meaning "\(\alpha\) to the exponent \(\beta\)," where \(\alpha\) and \(\beta\) are classes, as \[ \text{Prod}ʻ\alpha \downarrow_{,,}ʻʻ\beta . \] Now \(\text{Prod}ʻ\alpha \downarrow_{,,}ʻʻ\beta\) consists of all ways of selecting one each from the members of \(\alpha\downarrow_{,,}ʻʻ\beta\), *i.e.* from the classes \(\downarrow yʻʻ\alpha\), where \(y\in \beta\). Thus to get a member of \(\text{Prod}ʻ\alpha \downarrow_{,,}ʻʻ\beta\), take a set of couples \(x\downarrow y\), where \(x\) is always an \(\alpha\), and there is only one \(x\) for a given \(y\), and \(y\) is each member of \(\beta\) in succession. Thus for each member of \(\beta\), we have \(\text{Nc}ʻ\alpha\) possible referents; hence it is plain that the number of possible sets of couples consists of \(\text{Nc}ʻ\beta\) factors each equal to \(\text{Nc}ʻ\alpha\), and is therefore fit to be taken as defining \((\text{Nc}ʻ\alpha )^{\text{Nc}ʻ\beta}\).
>
> …

**Lean reading.** `α exp β` is `clsExp A B` (`Prod'α↓,,''β`), `μ^ν` is `μ ^ᶜ ν` with its actual type
implicit and fixed by an ascription; by the Dfs ✱116·03·04 an argument `Nc'α` of `^` is `n₀c A`
(normal adjustment), and `ΣNc'κ`, `ΠNc'κ` in an argument of `^` are read through their Dfs ✱112·02,
✱114·01 and normally adjusted. By convention IIT every other arithmetical component (`μ^ν`, `ν +_c
ϖ`, `μ ×_c ν`, `2^μ`, …) has its own type parameter with an adequacy hypothesis (`AdeqExp`,
`AdeqAdd`, `AdeqMul`), and every constant `0`, `1`, `2` its own type in which it exists; since
`AdeqExp` holds vacuously when the base type is empty while `Λ^Λ = 1` then fails, the formal laws
✱116·52·55·63·64 take the base types non-empty (PM assumes every type has a member). The converse
domain of `NC` (left ambiguous) is taken where the proposition requires it (the types of the members
of `μ`, `ν`; `Set T` in ✱116·23). Relations defined by hypotheses (`W`, `U`, `M`, `T`) are given by
equations, and `M'z`, `R'z` are descriptions (`Desc`). `R†` (Dft ✱116·529) is `dagger R`; `↓z` is
`coupleR z`, `x↓` is `coupleL x`, `α↓,,` is `coupleImg A`, `|S` is `relProdR S`, `↾γ` is `opR cres
G`. ✱116·331 is the entry of the Summary of ✱116 (the text's ✱116·311 is the same proposition).

**Status.** proved (all propositions;
✱116·13·22·23·201·202·203·204·24·25·251·3·301·31·32·321·33·311·331·34·35·411·52·55·63·64·653·655·661·67·675·68·7·71·715·72·83·9·901·91·92
proved (reading), see their docstrings).
-/

private theorem pmB2_one_exp {X W T : Type*} [Nonempty W] (Y : Set X) :
    ((one : Set (Set W)) ^ᶜ n₀c Y : Set (Set T)) = one := by
  obtain ⟨w⟩ := ‹Nonempty W›
  rw [one_eq_n₀c_singleton w, pmB2_n₀c_exp]
  have : Unique ↥(clsExp ({w} : Set W) Y) := (pmB2_clsExpEquiv _ _).unique
  exact pmB2_nc_eq_one

/-- ✱116·331. \(\vdash :\mu \in \text{NC} - \iota ʻ\Lambda .\supset .1^\mu = 1\)

This entry is ✱116·331 of the Summary of ✱116 (the text has it as ✱116·311, after ✱116·33).
The base `1` is an arithmetical constant: by convention IIT it is taken in a type `W` in which it
exists (`[Nonempty W]`, Defs/Part3, decision 6); the equation is in a free type `T`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the constant `1` in the
base is taken in a type in which it exists (`[Nonempty W]`). -/
theorem pm116_331 {X W T β : Type*} [Nonempty W] {μ : Set (Set X)} :
    μ ∈ NC β \ ι Λ → ((one : Set (Set W)) ^ᶜ μ : Set (Set T)) = one := by
  intro h
  obtain ⟨Y, rfl⟩ := pmB2_NC_ne h
  exact pmB2_one_exp Y

/-- ✱116·01 (Df). \(\alpha \,\text{exp}\,\,\beta = \text{Prod}ʻ\alpha \downarrow_{,,}ʻʻ\beta \quad\text{Df}\) -/
theorem pm116_01 {α β : Type*} {A : Set α} {B : Set β} :
    clsExp A B = prodK (coupleImg A ʻʻ B) := rfl

/-- ✱116·02 (Df). \(\mu ^\nu =\hat{\gamma}\{(\exists \alpha ,\beta ).\mu = \text{N}_{0}\text{c}ʻ\alpha .\nu = \text{N}_{0}\text{c}ʻ\beta .\gamma \text{ sm }(\alpha \,\text{exp}\,\,\beta )\} \quad\text{Df}\) -/
theorem pm116_02 {α β γ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ^ᶜ ν : Set (Set γ)) =
      {G | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm G (clsExp A B)} := rfl

/-- ✱116·03 (Df). \((\text{Nc}ʻ\alpha )^\nu = (\text{N}_{0}\text{c}ʻ\alpha )^\nu \quad\text{Df}\)

A rule of translation (normal adjustment): an argument `Nc'α` of `^` is written `n₀c A`. -/
theorem pm116_03 {α β γ : Type*} {A : Set α} {ν : Set (Set β)} :
    (n₀c A ^ᶜ ν : Set (Set γ)) = n₀c A ^ᶜ ν := rfl

/-- ✱116·04 (Df). \(\mu ^{\text{Nc}ʻ\beta } = \mu ^{\text{N}_{0}\text{c}ʻ\beta } \quad\text{Df}\)

A rule of translation (normal adjustment), as ✱116·03. -/
theorem pm116_04 {α β γ : Type*} {μ : Set (Set α)} {B : Set β} :
    (μ ^ᶜ n₀c B : Set (Set γ)) = μ ^ᶜ n₀c B := rfl

/-- ✱116·1. \[\begin{align}&\vdash :\xi \in (\alpha \,\text{exp}\,\, \beta ). \equiv .(\exists R).R\in {\in}_{\Delta}ʻ\alpha \downarrow_{,,}ʻʻ\beta .\xi = \text{D}ʻR\\ &[*115·1.(*116·01)]\end{align}\] -/
theorem pm116_1 {α β : Type*} {A : Set α} {B : Set β} {ξ : Set (α → β → Prop)} :
    ξ ∈ clsExp A B ↔ ∃ R, R ∈ sel memRel (coupleImg A ʻʻ B) ∧ ξ = dom R := Iff.rfl

/-- ✱116·11. \(\vdash \colon\ldotp \xi \in (\alpha \,\text{exp}\,\, \beta ). \equiv :y\in \beta .\supset _{y}.\alpha \cap \hat{x} (x\downarrow y\in \xi )\in 1:\xi \subset \beta \times \alpha \) -/
theorem pm116_11 {α β : Type*} {A : Set α} {B : Set β} {ξ : Set (α → β → Prop)} :
    ξ ∈ clsExp A B ↔ (∀ y, y ∈ B → A ∩ {x | x ↓ y ∈ ξ} ∈ one) ∧ ξ ⊆ B ×ₐ A :=
  pmB2_mem_clsExp

/-- ✱116·12. \(\vdash .(\alpha \uparrow \beta )_{\Delta }ʻ\beta = \hat{R} \{R\in 1\rightarrow \text{Cls}.\text{D}ʻR\subset \alpha .\text{ᗡ}ʻR = \beta\}\)

`α ↑ β` is `cross A B`; `(α ↑ β)_Δ'β` is `sel (cross A B) B`. -/
theorem pm116_12 {α β : Type*} {A : Set α} {B : Set β} :
    sel (cross A B) B = {R | (R ∈ arrow one Cls ∧ dom R ⊆ A) ∧ codom R = B} := by
  ext R
  rw [mem_sel_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, fun x ⟨y, hxy⟩ => (h2 x y hxy).1⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, fun x y hxy => ⟨h2 ⟨y, hxy⟩, h3 ▸ ⟨x, hxy⟩⟩⟩, h3⟩

private theorem pmB2_sumRel_couples {α β : Type*} {A : Set α} {B : Set β} {ξ : Set (α → β → Prop)}
    (h : ξ ⊆ B ×ₐ A) (x : α) (y : β) : sumRel ξ x y ↔ x ↓ y ∈ ξ := by
  constructor
  · rintro ⟨P, hP, hPxy⟩
    obtain ⟨x', y', -, rfl⟩ := pmB2_mem_clsTimes.1 (h hP)
    obtain ⟨rfl, rfl⟩ := (couple_apply _ _ _ _).1 hPxy
    exact hP
  · intro hxy
    exact ⟨x ↓ y, hxy, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩⟩

/-- ✱116·13. \(\vdash .sʻʻ(\alpha \,\text{exp}\,\, \beta ) = (\alpha\uparrow \beta )_{\Delta }ʻ\beta\)

The e-text prints `s''` for `ṡ''` (the Summary of ✱116: "this class is equal to
`ṡ''(α exp β)` (as is proved in ✱116·13)"). `ṡ''` is the image under `graph sumRel`.

**Status.** proved (reading): transcription error: `s''(α exp β)` is read `ṡ''(α exp β)`, as
the Summary of ✱116 states. -/
theorem pm116_13 {α β : Type*} {A : Set α} {B : Set β} :
    graph sumRel ʻʻ clsExp A B = sel (cross A B) B := by
  ext R
  constructor
  · rintro ⟨ξ, hξ, hR⟩
    have hR' : R = sumRel ξ := hR
    subst hR'
    obtain ⟨h1, h2⟩ := pmB2_mem_clsExp.1 hξ
    refine pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩
    · intro x x' y ⟨hx, hx'⟩
      rw [pmB2_sumRel_couples h2] at hx hx'
      have hy := (couple_mem_clsTimes.1 (h2 hx)).2
      obtain ⟨c, hc⟩ := h1 y hy
      have e1 : x ∈ A ∩ {x | x ↓ y ∈ ξ} := ⟨(couple_mem_clsTimes.1 (h2 hx)).1, hx⟩
      have e2 : x' ∈ A ∩ {x | x ↓ y ∈ ξ} := ⟨(couple_mem_clsTimes.1 (h2 hx')).1, hx'⟩
      rw [hc, mem_unitCls] at e1 e2
      rw [e1, e2]
    · intro x y hxy
      rw [pmB2_sumRel_couples h2] at hxy
      exact couple_mem_clsTimes.1 (h2 hxy)
    · ext y
      constructor
      · rintro ⟨x, hxy⟩
        rw [pmB2_sumRel_couples h2] at hxy
        exact (couple_mem_clsTimes.1 (h2 hxy)).2
      · intro hy
        obtain ⟨c, hc⟩ := h1 y hy
        have : c ∈ A ∩ {x | x ↓ y ∈ ξ} := by rw [hc]; rfl
        exact ⟨c, (pmB2_sumRel_couples h2 c y).2 this.2⟩
  · intro hR
    obtain ⟨h1, h2, h3⟩ := pmB2_mem_sel.1 hR
    have hsub : {P | ∃ x y, R x y ∧ P = x ↓ y} ⊆ B ×ₐ A := by
      rintro P ⟨x, y, hxy, rfl⟩
      exact couple_mem_clsTimes.2 (h2 x y hxy)
    refine ⟨{P | ∃ x y, R x y ∧ P = x ↓ y}, pmB2_mem_clsExp.2 ⟨fun y hy => ?_, hsub⟩, ?_⟩
    · obtain ⟨x, hx⟩ : y ∈ codom R := h3 ▸ hy
      refine ⟨x, Set.ext fun z => ⟨fun ⟨_, z', y', hR', e⟩ => ?_, fun e => ?_⟩⟩
      · obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
        exact h1 _ _ _ ⟨hR', hx⟩
      · rw [mem_unitCls] at e; subst e
        exact ⟨(h2 _ _ hx).1, z, y, hx, rfl⟩
    · show R = sumRel _
      funext x y
      rw [pmB2_sumRel_couples hsub]
      exact propext ⟨fun h => ⟨x, y, h, rfl⟩, fun ⟨x', y', h, e⟩ => by
        obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e; exact h⟩

/-- ✱116·131. \(\vdash .\dot{s} \upharpoonright (\alpha \,\,\text{exp}\,\, \beta )\in \{(\alpha \uparrow \beta )_{\Delta }ʻ\beta\} \,\overline{\text{ sm }}\, (\alpha \,\,\text{exp}\,\, \beta )\)

`ṡ ↾ (α exp β)` is `graph sumRel ↾ clsExp A B`; `{(α↑β)_Δ'β} sm̄ (α exp β)` is `smbar`. -/
theorem pm116_131 {α β : Type*} {A : Set α} {B : Set β} :
    graph sumRel ↾ clsExp A B ∈ smbar (sel (cross A B) B) (clsExp A B) := by
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro R R' ξ ⟨⟨h, -⟩, ⟨h', -⟩⟩
    have e1 : R = sumRel ξ := h
    have e2 : R' = sumRel ξ := h'
    rw [e1, e2]
  · rintro R ξ ξ' ⟨⟨h, hξ⟩, ⟨h', hξ'⟩⟩
    have e : sumRel ξ = sumRel ξ' := (show R = sumRel ξ from h).symm.trans h'
    have s1 := (pmB2_mem_clsExp.1 hξ).2
    have s2 := (pmB2_mem_clsExp.1 hξ').2
    ext P
    constructor
    · intro hP
      obtain ⟨x, y, -, rfl⟩ := pmB2_mem_clsTimes.1 (s1 hP)
      rw [← pmB2_sumRel_couples s2, ← e, pmB2_sumRel_couples s1]; exact hP
    · intro hP
      obtain ⟨x, y, -, rfl⟩ := pmB2_mem_clsTimes.1 (s2 hP)
      rw [← pmB2_sumRel_couples s1, e, pmB2_sumRel_couples s2]; exact hP
  · show sel (cross A B) B = dom _
    rw [← pm116_13]
    ext R
    exact ⟨fun ⟨ξ, hξ, h⟩ => ⟨ξ, h, hξ⟩, fun ⟨ξ, h, hξ⟩ => ⟨ξ, hξ, h⟩⟩
  · show clsExp A B = codom _
    ext ξ
    exact ⟨fun h => ⟨sumRel ξ, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩

/-- ✱116·14. \(\vdash .(\alpha \,\,\text{exp}\,\, \beta )\text{ sm }{\in}_{\Delta} ʻ\alpha \downarrow_{,,}ʻʻ\beta \quad[*115·12.*113·111]\) -/
theorem pm116_14 {α β : Type*} {A : Set α} {B : Set β} :
    sm (clsExp A B) (sel memRel (coupleImg A ʻʻ B)) :=
  pmB2_sm_of_equiv (pmB2_prodEquiv (pmB2_coupleImg_excl A B))

/-- ✱116·15. \(\vdash .(\alpha \,\,\text{exp}\,\, \beta )\text{ sm }(\alpha \uparrow \beta )_{\Delta }ʻ\beta \quad[*116·131]\) -/
theorem pm116_15 {α β : Type*} {A : Set α} {B : Set β} :
    sm (clsExp A B) (sel (cross A B) B) := sm_symm ⟨_, pm116_131⟩

/-- ✱116·151. \( \vdash :x \in \alpha .\supset .x\downarrow \mid \text{Cnv}ʻ(\alpha \downarrow_{,,}\upharpoonright \beta ) \in {\in}_{\Delta}ʻ\alpha \downarrow_{,,}ʻʻ\beta\)

`x↓` is `coupleL x`; `α↓,, ↾ β` is `coupleImg A ↾ B`, and `Cnv'(…)` is its converse `(…)˘`. -/
theorem pm116_151 {α β : Type*} {A : Set α} {B : Set β} {x : α} :
    x ∈ A → coupleL x ⨾ (coupleImg A ↾ B)˘ ∈ sel memRel (coupleImg A ʻʻ B) := by
  intro hx
  refine pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩
  · rintro R R' Y ⟨⟨y, hR, hY, -⟩, ⟨y', hR', hY', -⟩⟩
    have e1 : R = x ↓ y := hR
    have e2 : R' = x ↓ y' := hR'
    have e3 : Y = opImg couple A y := hY
    have e4 : Y = opImg couple A y' := hY'
    have : x ↓ y ∈ opImg couple A y' := e4 ▸ e3 ▸ ⟨x, hx, rfl⟩
    obtain ⟨x', -, e⟩ := this
    rw [e1, e2, (couple_eq_couple_iff.1 e).2]
  · rintro R Y ⟨y, hR, hY, -⟩
    have e1 : R = x ↓ y := hR
    have e3 : Y = opImg couple A y := hY
    rw [e1, e3]; exact ⟨x, hx, rfl⟩
  · ext Y
    constructor
    · rintro ⟨R, y, -, hY, hy⟩; exact ⟨y, hy, hY⟩
    · rintro ⟨y, hy, hY⟩; exact ⟨x ↓ y, y, rfl, hY, hy⟩

/-- ✱116·152. \(\vdash :x \in \alpha .\supset .x\downarrowʻʻ\beta \in (\alpha \,\,\text{exp}\,\,\beta )\)

`x↓''β` is `coupleL x ʻʻ B`. -/
theorem pm116_152 {α β : Type*} {A : Set α} {B : Set β} {x : α} :
    x ∈ A → coupleL x ʻʻ B ∈ clsExp A B := by
  intro hx
  refine pmB2_mem_clsExp.2 ⟨fun y hy => ⟨x, Set.ext fun z => ⟨fun ⟨_, y', _, e⟩ => ?_,
    fun e => ?_⟩⟩, ?_⟩
  · have e' : z ↓ y = x ↓ y' := e
    exact (couple_eq_couple_iff.1 e').1
  · rw [mem_unitCls] at e; subst e; exact ⟨hx, y, hy, rfl⟩
  · rintro R ⟨y, hy, hR⟩
    have e : R = x ↓ y := hR
    rw [e]; exact couple_mem_clsTimes.2 ⟨hx, hy⟩

private theorem pmB2_cnv_couple {α β : Type*} (y : β) (x : α) : (y ↓ x)˘ = x ↓ y := by
  funext a b
  exact propext ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

/-- ✱116·16. \(\vdash .\text{Cnv}ʻʻʻ\beta \downarrow_{,,}ʻʻ\alpha \subset \alpha \,\,\text{exp}\,\,\beta\)

`Cnv'''β↓,,''α` is `Cnv ʻʻʻ (coupleImg B ʻʻ A)` (`Cnv` the relation of ✱31·01). -/
theorem pm116_16 {α β : Type*} {A : Set α} {B : Set β} :
    Cnv ʻʻʻ (coupleImg B ʻʻ A) ⊆ clsExp A B := by
  rintro Z ⟨Y, ⟨x, hx, hY⟩, hZ⟩
  have e1 : Y = opImg couple B x := hY
  have e2 : Z = Cnv ʻʻ Y := hZ
  subst e1; subst e2
  convert pm116_152 (B := B) hx using 1
  ext R
  constructor
  · rintro ⟨Q, ⟨y, hy, hQ⟩, hRQ⟩
    have e : Q = y ↓ x := hQ
    subst e
    rw [Cnv_iff, pmB2_cnv_couple] at hRQ
    exact ⟨y, hy, hRQ⟩
  · rintro ⟨y, hy, hR⟩
    have e : R = x ↓ y := hR
    subst e
    refine ⟨y ↓ x, ⟨y, hy, rfl⟩, ?_⟩
    rw [Cnv_iff, pmB2_cnv_couple]

/-- ✱116·17. \(\vdash :\exists !\beta \downarrow_{,,}ʻʻ\alpha .\supset .\exists !\alpha \,\,\text{exp}\,\,\beta \quad[*116·16.*37·47]\) -/
theorem pm116_17 {α β : Type*} {A : Set α} {B : Set β} :
    (coupleImg B ʻʻ A).Nonempty → (clsExp A B).Nonempty := by
  rintro ⟨Y, x, hx, -⟩
  exact ⟨_, pm116_152 hx⟩

/-- ✱116·171. \(\vdash \colon\ldotp \exists !\alpha .\lor.\beta =\Lambda :\supset .\exists !\alpha \,\,\text{exp}\,\,\beta\) -/
theorem pm116_171 {α β : Type*} {A : Set α} {B : Set β} :
    A.Nonempty ∨ B = Λ → (clsExp A B).Nonempty := by
  rintro (⟨x, hx⟩ | hB)
  · exact ⟨_, pm116_152 hx⟩
  · rw [Null_eq_empty] at hB
    subst hB
    refine ⟨∅, pmB2_mem_clsExp.2 ⟨fun y hy => hy.elim, Set.empty_subset _⟩⟩

/-- ✱116·172. \(\vdash \colon\ldotp \exists !\alpha \,\,\text{exp}\,\,\beta .\supset :\exists !\alpha .\lor.\beta =\Lambda\) -/
theorem pm116_172 {α β : Type*} {A : Set α} {B : Set β} :
    (clsExp A B).Nonempty → A.Nonempty ∨ B = Λ := by
  rintro ⟨ξ, hξ⟩
  rw [Null_eq_empty]
  by_cases hB : B = ∅
  · exact Or.inr hB
  · obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hB
    obtain ⟨c, hc⟩ := (pmB2_mem_clsExp.1 hξ).1 y hy
    have : c ∈ A ∩ {x | x ↓ y ∈ ξ} := by rw [hc]; rfl
    exact Or.inl ⟨c, this.1⟩

/-- ✱116·18. \(\vdash \colon\ldotp \exists !\alpha .\lor.\beta =\Lambda :\equiv .\exists !\alpha \,\,\text{exp}\,\,\beta \quad[*116·171·172]\) -/
theorem pm116_18 {α β : Type*} {A : Set α} {B : Set β} :
    (A.Nonempty ∨ B = Λ) ↔ (clsExp A B).Nonempty := ⟨pm116_171, pm116_172⟩

/-- ✱116·181. \(\vdash .\alpha \,\,\text{exp}\,\,\Lambda =\iota ʻ\Lambda\)

The `Λ` of `ι'Λ` is the null class of the type of `α exp Λ`'s members. -/
theorem pm116_181 {α β : Type*} {A : Set α} : clsExp A (Λ : Set β) = ι Λ := by
  ext ξ
  rw [pmB2_mem_clsExp, mem_unitCls, Null_eq_empty, Null_eq_empty]
  constructor
  · rintro ⟨-, h⟩
    refine Set.eq_empty_iff_forall_notMem.2 fun R hR => ?_
    obtain ⟨x, y, ⟨-, hy⟩, -⟩ := pmB2_mem_clsTimes.1 (h hR)
    exact hy
  · rintro rfl
    exact ⟨fun y hy => hy.elim, Set.empty_subset _⟩

/-- ✱116·182. \(\vdash : \exists ! \beta . \supset . \Lambda \,\,\text{exp}\,\, \beta = \Lambda \quad[*113·112 . *83·11]\) -/
theorem pm116_182 {α β : Type*} {B : Set β} : B.Nonempty → clsExp (Λ : Set α) B = Λ := by
  intro hB
  rw [Null_eq_empty, Null_eq_empty]
  refine Set.eq_empty_iff_forall_notMem.2 fun ξ hξ => ?_
  rcases pm116_172 ⟨ξ, hξ⟩ with ⟨x, hx⟩ | hB'
  · exact hx
  · rw [Null_eq_empty] at hB'
    exact Set.not_nonempty_empty (hB' ▸ hB)

/-- ✱116·183. \(\vdash . sʻ(\alpha \,\,\text{exp}\,\, \beta ) = \beta \times \alpha\) -/
theorem pm116_183 {α β : Type*} {A : Set α} {B : Set β} : sumCls (clsExp A B) = B ×ₐ A := by
  ext R
  constructor
  · rintro ⟨ξ, hξ, hR⟩
    exact (pmB2_mem_clsExp.1 hξ).2 hR
  · intro hR
    obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := pmB2_mem_clsTimes.1 hR
    exact ⟨_, pm116_152 hx, y, hy, rfl⟩

/-- The facts about a correlator `R ↾ γ ∈ α sm̄ γ` used below. -/
private structure pmB2_Corr {α γ : Type*} (R : α → γ → Prop) (A : Set α) (G : Set γ) : Prop where
  ex : ∀ g, g ∈ G → ∃ a, R a g
  uniq : ∀ a a' g, g ∈ G → R a g → R a' g → a = a'
  inj : ∀ a g g', g ∈ G → g' ∈ G → R a g → R a g' → g = g'
  dom_ex : ∀ a, a ∈ A → ∃ g, g ∈ G ∧ R a g
  mem : ∀ a g, g ∈ G → R a g → a ∈ A

private theorem pmB2_corr_of {α γ : Type*} {R : α → γ → Prop} {A : Set α} {G : Set γ}
    (h : R ↾ G ∈ smbar A G) : pmB2_Corr R A G := by
  obtain ⟨⟨h11, hA⟩, hG⟩ := h
  have hA' : A = dom (R ↾ G) := hA
  have hG' : G = codom (R ↾ G) := hG
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 h11
  refine ⟨fun g hg => ?_, fun a a' g hg ha ha' => h1 a a' g ⟨⟨ha, hg⟩, ⟨ha', hg⟩⟩,
    fun a g g' hg hg' ha ha' => h2 a g g' ⟨⟨ha, hg⟩, ⟨ha', hg'⟩⟩, fun a ha => ?_,
    fun a g hg ha => ?_⟩
  · rw [hG'] at hg; obtain ⟨a, ha, -⟩ := hg; exact ⟨a, ha⟩
  · rw [hA'] at ha; obtain ⟨g, hag, hg⟩ := ha; exact ⟨g, hg, hag⟩
  · rw [hA']; exact ⟨g, ha, hg⟩

private theorem pmB2_corr_couple {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop}
    {A : Set α} {G : Set γ} {B : Set β} {H : Set δ} (cR : pmB2_Corr R A G)
    (cS : pmB2_Corr S B H) {g : γ} {h : δ} (hg : g ∈ G) (hh : h ∈ H) {a : α} {b : β}
    (ha : R a g) (hb : S b h) : R ⨾ ((g ↓ h) ⨾ S˘) = a ↓ b := by
  funext u v
  apply propext
  constructor
  · rintro ⟨c, hu, d, ⟨rfl, rfl⟩, hv⟩
    exact ⟨cR.uniq u a c hg hu ha, cS.uniq v b d hh hv hb⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨g, ha, h, ⟨rfl, rfl⟩, hb⟩

private theorem pmB2_corr_T {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop}
    {A : Set α} {G : Set γ} {B : Set β} {H : Set δ} (cR : pmB2_Corr R A G)
    (cS : pmB2_Corr S B H) (P : α → β → Prop) (Q : γ → δ → Prop) :
    ((R ∥ S˘) ↾ (H ×ₐ G)) P Q ↔
      ∃ a b g h, ((R a g ∧ g ∈ G) ∧ (S b h ∧ h ∈ H)) ∧ P = a ↓ b ∧ Q = g ↓ h := by
  constructor
  · rintro ⟨hPQ, hQ⟩
    obtain ⟨g, h, ⟨hg, hh⟩, rfl⟩ := pmB2_mem_clsTimes.1 hQ
    obtain ⟨a, ha⟩ := cR.ex g hg
    obtain ⟨b, hb⟩ := cS.ex h hh
    rw [dpar_iff, pmB2_corr_couple cR cS hg hh ha hb] at hPQ
    exact ⟨a, b, g, h, ⟨⟨ha, hg⟩, ⟨hb, hh⟩⟩, hPQ, rfl⟩
  · rintro ⟨a, b, g, h, ⟨⟨ha, hg⟩, ⟨hb, hh⟩⟩, rfl, rfl⟩
    refine ⟨?_, couple_mem_clsTimes.2 ⟨hg, hh⟩⟩
    rw [dpar_iff, pmB2_corr_couple cR cS hg hh ha hb]

private theorem pmB2_corr_img_mem {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop}
    {A : Set α} {G : Set γ} {B : Set β} {H : Set δ} (cR : pmB2_Corr R A G)
    (cS : pmB2_Corr S B H) (ξ : Set (γ → δ → Prop)) (x : α) (y : β) :
    x ↓ y ∈ ((R ∥ S˘) ↾ (H ×ₐ G)) ʻʻ ξ ↔
      ∃ g h, ((R x g ∧ g ∈ G) ∧ (S y h ∧ h ∈ H)) ∧ g ↓ h ∈ ξ := by
  constructor
  · rintro ⟨Q, hQ, hT⟩
    obtain ⟨a, b, g, h, hh, e, rfl⟩ := (pmB2_corr_T cR cS _ _).1 hT
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    exact ⟨g, h, hh, hQ⟩
  · rintro ⟨g, h, hh, hQ⟩
    exact ⟨g ↓ h, hQ, (pmB2_corr_T cR cS _ _).2 ⟨x, y, g, h, hh, rfl, rfl⟩⟩

private theorem pmB2_corr_img_sub {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop}
    {A : Set α} {G : Set γ} {B : Set β} {H : Set δ} (cR : pmB2_Corr R A G)
    (cS : pmB2_Corr S B H) (ξ : Set (γ → δ → Prop)) :
    ((R ∥ S˘) ↾ (H ×ₐ G)) ʻʻ ξ ⊆ B ×ₐ A := by
  rintro P ⟨Q, -, hT⟩
  obtain ⟨a, b, g, h, ⟨⟨ha, hg⟩, ⟨hb, hh⟩⟩, rfl, rfl⟩ := (pmB2_corr_T cR cS _ _).1 hT
  exact couple_mem_clsTimes.2 ⟨cR.mem a g hg ha, cS.mem b h hh hb⟩

private theorem pmB2_corr_M1 {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop}
    {A : Set α} {G : Set γ} {B : Set β} {H : Set δ} (cR : pmB2_Corr R A G)
    (cS : pmB2_Corr S B H) {ξ : Set (γ → δ → Prop)} (hξ : ξ ∈ clsExp G H) :
    ((R ∥ S˘) ↾ (H ×ₐ G)) ʻʻ ξ ∈ clsExp A B := by
  obtain ⟨h1, h2⟩ := pmB2_mem_clsExp.1 hξ
  refine pmB2_mem_clsExp.2 ⟨fun y hy => ?_, pmB2_corr_img_sub cR cS ξ⟩
  obtain ⟨h₀, hh₀, hyh₀⟩ := cS.dom_ex y hy
  obtain ⟨g₀, hg₀⟩ := h1 h₀ hh₀
  have hm : g₀ ∈ G ∩ {g | g ↓ h₀ ∈ ξ} := by rw [hg₀]; rfl
  obtain ⟨a₀, ha₀⟩ := cR.ex g₀ hm.1
  refine ⟨a₀, Set.ext fun x => ⟨fun ⟨hx, hxy⟩ => ?_, fun e => ?_⟩⟩
  · obtain ⟨g, h, ⟨⟨hxg, hg⟩, ⟨hyh, hh⟩⟩, hgh⟩ := (pmB2_corr_img_mem cR cS ξ x y).1 hxy
    have e1 : h = h₀ := cS.inj y h h₀ hh hh₀ hyh hyh₀
    subst e1
    have : g ∈ G ∩ {g | g ↓ h ∈ ξ} := ⟨hg, hgh⟩
    rw [hg₀, mem_unitCls] at this
    subst this
    exact cR.uniq x a₀ g hg hxg ha₀
  · rw [mem_unitCls] at e; subst e
    exact ⟨cR.mem _ _ hm.1 ha₀, (pmB2_corr_img_mem cR cS ξ x y).2
      ⟨g₀, h₀, ⟨⟨ha₀, hm.1⟩, ⟨hyh₀, hh₀⟩⟩, hm.2⟩⟩

private theorem pmB2_corr_M2 {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop}
    {A : Set α} {G : Set γ} {B : Set β} {H : Set δ} (cR : pmB2_Corr R A G)
    (cS : pmB2_Corr S B H) {ζ : Set (α → β → Prop)} (hζ : ζ ∈ clsExp A B) :
    ∃ ξ, ξ ∈ clsExp G H ∧ ζ = ((R ∥ S˘) ↾ (H ×ₐ G)) ʻʻ ξ := by
  obtain ⟨h1, h2⟩ := pmB2_mem_clsExp.1 hζ
  refine ⟨{Q | ∃ g h, Q = g ↓ h ∧ ∃ a b, ((R a g ∧ g ∈ G) ∧ (S b h ∧ h ∈ H)) ∧ a ↓ b ∈ ζ},
    pmB2_mem_clsExp.2 ⟨fun h hh => ?_, ?_⟩, ?_⟩
  · obtain ⟨b, hb⟩ := cS.ex h hh
    have hbB := cS.mem b h hh hb
    obtain ⟨a₀, ha₀⟩ := h1 b hbB
    have hm : a₀ ∈ A ∩ {x | x ↓ b ∈ ζ} := by rw [ha₀]; rfl
    obtain ⟨g₀, hg₀, hag₀⟩ := cR.dom_ex a₀ hm.1
    refine ⟨g₀, Set.ext fun g => ⟨fun ⟨hg, hgh⟩ => ?_, fun e => ?_⟩⟩
    · obtain ⟨g', h', e, a, b', ⟨⟨hag, hg'⟩, ⟨hbh, hh'⟩⟩, hab⟩ := hgh
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
      have e2 : b' = b := cS.uniq b' b h hh hbh hb
      subst e2
      have : a ∈ A ∩ {x | x ↓ b' ∈ ζ} := ⟨cR.mem a g hg hag, hab⟩
      rw [ha₀, mem_unitCls] at this
      subst this
      exact cR.inj a g g₀ hg hg₀ hag hag₀
    · rw [mem_unitCls] at e; subst e
      exact ⟨hg₀, g, h, rfl, a₀, b, ⟨⟨hag₀, hg₀⟩, ⟨hb, hh⟩⟩, hm.2⟩
  · rintro Q ⟨g, h, rfl, a, b, ⟨⟨-, hg⟩, ⟨-, hh⟩⟩, -⟩
    exact couple_mem_clsTimes.2 ⟨hg, hh⟩
  · ext P
    constructor
    · intro hP
      obtain ⟨a, b, ⟨ha, hb⟩, rfl⟩ := pmB2_mem_clsTimes.1 (h2 hP)
      obtain ⟨g, hg, hag⟩ := cR.dom_ex a ha
      obtain ⟨h, hh, hbh⟩ := cS.dom_ex b hb
      exact (pmB2_corr_img_mem cR cS _ a b).2 ⟨g, h, ⟨⟨hag, hg⟩, ⟨hbh, hh⟩⟩,
        g, h, rfl, a, b, ⟨⟨hag, hg⟩, ⟨hbh, hh⟩⟩, hP⟩
    · intro hP
      obtain ⟨a, b, -, rfl⟩ := pmB2_mem_clsTimes.1 (pmB2_corr_img_sub cR cS _ hP)
      obtain ⟨g, h, ⟨⟨hag, hg⟩, ⟨hbh, hh⟩⟩, g', h', e, a', b', ⟨⟨hag', -⟩, ⟨hbh', -⟩⟩, hab⟩ :=
        (pmB2_corr_img_mem cR cS _ a b).1 hP
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
      rw [cR.uniq a a' g hg hag hag', cS.uniq b b' h hh hbh hbh']
      exact hab

private theorem pmB2_corr_M3 {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop}
    {A : Set α} {G : Set γ} {B : Set β} {H : Set δ} (cR : pmB2_Corr R A G)
    (cS : pmB2_Corr S B H) {ξ ξ' : Set (γ → δ → Prop)} (hξ : ξ ⊆ H ×ₐ G)
    (_hξ' : ξ' ⊆ H ×ₐ G)
    (e : ((R ∥ S˘) ↾ (H ×ₐ G)) ʻʻ ξ = ((R ∥ S˘) ↾ (H ×ₐ G)) ʻʻ ξ') : ξ ⊆ ξ' := by
  intro Q hQ
  obtain ⟨g, h, ⟨hg, hh⟩, rfl⟩ := pmB2_mem_clsTimes.1 (hξ hQ)
  obtain ⟨a, ha⟩ := cR.ex g hg
  obtain ⟨b, hb⟩ := cS.ex h hh
  have : a ↓ b ∈ ((R ∥ S˘) ↾ (H ×ₐ G)) ʻʻ ξ' :=
    e ▸ (pmB2_corr_img_mem cR cS ξ a b).2 ⟨g, h, ⟨⟨ha, hg⟩, ⟨hb, hh⟩⟩, hQ⟩
  obtain ⟨g', h', ⟨⟨ha', hg'⟩, ⟨hb', hh'⟩⟩, hQ'⟩ := (pmB2_corr_img_mem cR cS ξ' a b).1 this
  rw [cR.inj a g g' hg hg' ha ha', cS.inj b h h' hh hh' hb hb']
  exact hQ'

private theorem pmB2_exp_corr {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop}
    {A : Set α} {G : Set γ} {B : Set β} {H : Set δ} :
    R ↾ G ∈ smbar A G ∧ S ↾ H ∈ smbar B H →
      (R ∥ S˘) ↾ (H ×ₐ G) ∈ smsmbar (clsExp A B) (clsExp G H) ∧
        imgRel (R ∥ S˘) ↾ clsExp G H ∈ smbar (clsExp A B) (clsExp G H) := by
  rintro ⟨hR, hS⟩
  have cR := pmB2_corr_of hR
  have cS := pmB2_corr_of hS
  have hsub : ∀ ξ, ξ ∈ clsExp G H → ξ ⊆ H ×ₐ G := fun ξ hξ => (pmB2_mem_clsExp.1 hξ).2
  have himg : ∀ ξ, ξ ∈ clsExp G H → (R ∥ S˘) ʻʻ ξ = ((R ∥ S˘) ↾ (H ×ₐ G)) ʻʻ ξ :=
    fun ξ hξ => (pmB2_img_cres (hsub ξ hξ)).symm
  refine ⟨⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩, ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
  · intro P P' Q ⟨hP, hP'⟩
    obtain ⟨a, b, g, h, ⟨⟨ha, hg⟩, ⟨hb, hh⟩⟩, rfl, rfl⟩ := (pmB2_corr_T cR cS _ _).1 hP
    obtain ⟨a', b', g', h', ⟨⟨ha', -⟩, ⟨hb', -⟩⟩, rfl, e⟩ := (pmB2_corr_T cR cS _ _).1 hP'
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    rw [cR.uniq a a' g hg ha ha', cS.uniq b b' h hh hb hb']
  · intro P Q Q' ⟨hQ, hQ'⟩
    obtain ⟨a, b, g, h, ⟨⟨ha, hg⟩, ⟨hb, hh⟩⟩, rfl, rfl⟩ := (pmB2_corr_T cR cS _ _).1 hQ
    obtain ⟨a', b', g', h', ⟨⟨ha', hg'⟩, ⟨hb', hh'⟩⟩, e, rfl⟩ := (pmB2_corr_T cR cS _ _).1 hQ'
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    rw [cR.inj a g g' hg hg' ha ha', cS.inj b h h' hh hh' hb hb']
  · show sumCls (clsExp G H) = codom _
    rw [pm116_183]
    ext Q
    constructor
    · intro hQ
      obtain ⟨g, h, ⟨hg, hh⟩, rfl⟩ := pmB2_mem_clsTimes.1 hQ
      obtain ⟨a, ha⟩ := cR.ex g hg
      obtain ⟨b, hb⟩ := cS.ex h hh
      exact ⟨a ↓ b, (pmB2_corr_T cR cS _ _).2 ⟨a, b, g, h, ⟨⟨ha, hg⟩, ⟨hb, hh⟩⟩, rfl, rfl⟩⟩
    · rintro ⟨P, -, hQ⟩; exact hQ
  · ext ζ
    constructor
    · intro hζ
      obtain ⟨ξ, hξ, rfl⟩ := pmB2_corr_M2 cR cS hζ
      exact ⟨ξ, hξ, rfl⟩
    · rintro ⟨ξ, hξ, hζ⟩
      have hζ' : ζ = _ := hζ
      rw [hζ']; exact pmB2_corr_M1 cR cS hξ
  · rintro ζ ζ' ξ ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    exact (show ζ = _ from h1).trans (show ζ' = _ from h2).symm
  · rintro ζ ξ ξ' ⟨⟨h1, hξ⟩, ⟨h2, hξ'⟩⟩
    have e : ((R ∥ S˘) ↾ (H ×ₐ G)) ʻʻ ξ = ((R ∥ S˘) ↾ (H ×ₐ G)) ʻʻ ξ' := by
      rw [← himg ξ hξ, ← himg ξ' hξ']
      exact (show ζ = _ from h1).symm.trans h2
    exact Set.Subset.antisymm (pmB2_corr_M3 cR cS (hsub ξ hξ) (hsub ξ' hξ') e)
      (pmB2_corr_M3 cR cS (hsub ξ' hξ') (hsub ξ hξ) e.symm)
  · show clsExp A B = dom _
    ext ζ
    constructor
    · intro hζ
      obtain ⟨ξ, hξ, rfl⟩ := pmB2_corr_M2 cR cS hζ
      exact ⟨ξ, (himg ξ hξ).symm, hξ⟩
    · rintro ⟨ξ, hζ, hξ⟩
      have hζ' : ζ = _ := hζ
      rw [hζ', himg ξ hξ]; exact pmB2_corr_M1 cR cS hξ
  · show clsExp G H = codom _
    ext ξ
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩

private theorem pmB2_cres_codom {α γ : Type*} {R : α → γ → Prop} {A : Set α} {G : Set γ}
    (h : R ∈ smbar A G) : R ↾ G ∈ smbar A G := by
  have hG : G = codom R := h.2
  have : R ↾ G = R := by
    funext a g
    exact propext ⟨fun h => h.1, fun h' => ⟨h', hG ▸ ⟨a, h'⟩⟩⟩
  rw [this]; exact h

/-- ✱116·19. \(\vdash : \alpha \text{ sm } \gamma . \beta \text{ sm } \delta . \supset . (\alpha \,\,\text{exp}\,\, \beta ) \text{ sm } \text{ sm } (\gamma \,\,\text{exp}\,\, \delta )\)

`sm sm` is `smsm` (✱111·03). -/
theorem pm116_19 {α β γ δ : Type*} {A : Set α} {B : Set β} {G : Set γ} {H : Set δ} :
    sm A G ∧ sm B H → smsm (clsExp A B) (clsExp G H) := by
  rintro ⟨⟨R, hR⟩, ⟨S, hS⟩⟩
  exact ⟨_, (pmB2_exp_corr ⟨pmB2_cres_codom hR, pmB2_cres_codom hS⟩).1⟩

/-- ✱116·191. \[\begin{align}\vdash : R \in \alpha \overline{\text{ sm }} \gamma . S \in \beta \,\overline{\text{ sm }}\, \delta . \supset . &(R \parallel \breve{S} ) \upharpoonright (\delta \times \gamma ) \in (\alpha \,\,\text{exp}\,\, \beta ) \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, (\gamma \,\,\text{exp}\,\, \delta ) .\\ &(R \parallel \breve{S} )_{\in}ʻʻ(\gamma \,\,\text{exp}\,\, \delta ) = \alpha \,\,\text{exp}\,\, \beta \\ [*113·127 . *115·502 . *116·183]\end{align}\]

`R ∈ α sm̄ γ` is `R ∈ smbar A G`; `(R ‖ S̆)_∈''(γ exp δ)` is `imgRel (R ∥ S˘) ʻʻ clsExp G H`. -/
theorem pm116_191 {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop}
    {A : Set α} {G : Set γ} {B : Set β} {H : Set δ} :
    R ∈ smbar A G ∧ S ∈ smbar B H →
      (R ∥ S˘) ↾ (H ×ₐ G) ∈ smsmbar (clsExp A B) (clsExp G H) ∧
        imgRel (R ∥ S˘) ʻʻ clsExp G H = clsExp A B := by
  rintro ⟨hR, hS⟩
  have h := pmB2_exp_corr ⟨pmB2_cres_codom hR, pmB2_cres_codom hS⟩
  refine ⟨h.1, ?_⟩
  have hdom : clsExp A B = dom (imgRel (R ∥ S˘) ↾ clsExp G H) := h.2.1.2
  rw [hdom]
  ext ζ
  exact ⟨fun ⟨ξ, hξ, hζ⟩ => ⟨ξ, hζ, hξ⟩, fun ⟨ξ, hζ, hξ⟩ => ⟨ξ, hξ, hζ⟩⟩

/-- ✱116·192. \[\begin{align}\vdash : R \upharpoonright \gamma \in \alpha \,\overline{\text{ sm }}\, \gamma . S \upharpoonright \delta \in \beta &\,\overline{\text{ sm }}\, \delta . \supset .\\ &(R \parallel \breve{S} ) \upharpoonright (\delta \times \gamma ) \in (\alpha \,\,\text{exp}\,\, \beta ) \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, (\gamma \,\,\text{exp}\,\, \delta ) .\\ &(R \parallel \breve{S} )_{\in } \upharpoonright (\gamma \,\,\text{exp}\,\, \delta ) \in (\alpha \,\,\text{exp}\,\, \beta ) \,\overline{\text{ sm }}\, (\gamma \,\,\text{exp}\,\, \delta )\\ &[*113·127 . *115·502 . *116·183 . *111·15]\end{align}\]

`R ↾ γ ∈ α sm̄ γ` is `R ↾ G ∈ smbar A G`; `R ‖ S̆` is `R ∥ S˘`; `δ × γ` is `H ×ₐ G`;
`(R ‖ S̆)_∈ ↾ (γ exp δ)` is `imgRel (R ∥ S˘) ↾ clsExp G H`. -/
theorem pm116_192 {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop}
    {A : Set α} {G : Set γ} {B : Set β} {H : Set δ} :
    R ↾ G ∈ smbar A G ∧ S ↾ H ∈ smbar B H →
      (R ∥ S˘) ↾ (H ×ₐ G) ∈ smsmbar (clsExp A B) (clsExp G H) ∧
        imgRel (R ∥ S˘) ↾ clsExp G H ∈ smbar (clsExp A B) (clsExp G H) := pmB2_exp_corr

/-- ✱116·194. \[\begin{align}\vdash : R \upharpoonright \gamma \in \alpha \,\overline{\text{ sm }}\, \gamma . &S \upharpoonright \delta \in \beta \,\overline{\text{ sm }}\, \delta . \supset .\\ &(R \parallel \breve{S} ) \upharpoonright {(\gamma \uparrow \delta )_{\Delta }ʻ\delta } \in {(\alpha \uparrow \beta )_{\Delta }ʻ\beta } \,\overline{\text{ sm }}\, {(\gamma \uparrow \delta )_{\Delta }ʻ\delta }\end{align}\]

`(α ↑ β)_Δ'β` is `sel (cross A B) B`. -/
theorem pm116_194 {α β γ δ : Type*} {R : α → γ → Prop} {S : β → δ → Prop}
    {A : Set α} {G : Set γ} {B : Set β} {H : Set δ} :
    R ↾ G ∈ smbar A G ∧ S ↾ H ∈ smbar B H →
      (R ∥ S˘) ↾ sel (cross G H) H ∈ smbar (sel (cross A B) B) (sel (cross G H) H) := by
  rintro ⟨hR, hS⟩
  have cR := pmB2_corr_of hR
  have cS := pmB2_corr_of hS
  have img : ∀ Q, Q ∈ sel (cross G H) H → R ⨾ (Q ⨾ S˘) ∈ sel (cross A B) B := by
    intro Q hQ
    obtain ⟨q1, q2, q3⟩ := pmB2_mem_sel.1 hQ
    refine pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩
    · rintro a a' b ⟨⟨g, hag, h, hgh, hbh⟩, ⟨g', hag', h', hgh', hbh'⟩⟩
      have hh := (q2 g h hgh).2
      have hh' := (q2 g' h' hgh').2
      have e1 : h = h' := cS.inj b h h' hh hh' hbh hbh'
      subst e1
      have e2 : g = g' := q1 g g' h ⟨hgh, hgh'⟩
      subst e2
      exact cR.uniq a a' g (q2 g h hgh).1 hag hag'
    · rintro a b ⟨g, hag, h, hgh, hbh⟩
      exact ⟨cR.mem a g (q2 g h hgh).1 hag, cS.mem b h (q2 g h hgh).2 hbh⟩
    · ext b
      constructor
      · rintro ⟨a, g, hag, h, hgh, hbh⟩
        exact cS.mem b h (q2 g h hgh).2 hbh
      · intro hb
        obtain ⟨h, hh, hbh⟩ := cS.dom_ex b hb
        obtain ⟨g, hgh⟩ : h ∈ codom Q := q3 ▸ hh
        obtain ⟨a, hag⟩ := cR.ex g (q2 g h hgh).1
        exact ⟨a, g, hag, h, hgh, hbh⟩
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro P P' Q ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    rw [dpar_iff] at h1 h2
    rw [h1, h2]
  · rintro P Q Q' ⟨⟨h1, hQ⟩, ⟨h2, hQ'⟩⟩
    rw [dpar_iff] at h1 h2
    have e : R ⨾ (Q ⨾ S˘) = R ⨾ (Q' ⨾ S˘) := h1.symm.trans h2
    have key : ∀ Q Q', Q ∈ sel (cross G H) H → Q' ∈ sel (cross G H) H →
        R ⨾ (Q ⨾ S˘) = R ⨾ (Q' ⨾ S˘) → ∀ g h, Q g h → Q' g h := by
      intro Q Q' hQ hQ' e g h hgh
      have hgH := (pmB2_mem_sel.1 hQ).2.1 g h hgh
      obtain ⟨a, hag⟩ := cR.ex g hgH.1
      obtain ⟨b, hbh⟩ := cS.ex h hgH.2
      have : (R ⨾ (Q' ⨾ S˘)) a b := e ▸ ⟨g, hag, h, hgh, hbh⟩
      obtain ⟨g', hag', h', hgh', hbh'⟩ := this
      have hgH' := (pmB2_mem_sel.1 hQ').2.1 g' h' hgh'
      rw [cR.inj a g g' hgH.1 hgH'.1 hag hag', cS.inj b h h' hgH.2 hgH'.2 hbh hbh']
      exact hgh'
    funext g h
    exact propext ⟨key Q Q' hQ hQ' e g h, key Q' Q hQ' hQ e.symm g h⟩
  · show sel (cross A B) B = dom _
    ext P
    constructor
    · intro hP
      obtain ⟨p1, p2, p3⟩ := pmB2_mem_sel.1 hP
      let Q : γ → δ → Prop := fun g h => g ∈ G ∧ h ∈ H ∧ ∃ a b, R a g ∧ S b h ∧ P a b
      have hQ : Q ∈ sel (cross G H) H := by
        refine pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩
        · rintro g g' h ⟨⟨hg, hh, a, b, hag, hbh, hab⟩, ⟨hg', -, a', b', hag', hbh', hab'⟩⟩
          have e1 : b = b' := cS.uniq b b' h hh hbh hbh'
          subst e1
          have e2 : a = a' := p1 a a' b ⟨hab, hab'⟩
          subst e2
          exact cR.inj a g g' hg hg' hag hag'
        · rintro g h ⟨hg, hh, -⟩; exact ⟨hg, hh⟩
        · ext h
          constructor
          · rintro ⟨g, -, hh, -⟩; exact hh
          · intro hh
            obtain ⟨b, hbh⟩ := cS.ex h hh
            obtain ⟨a, hab⟩ : b ∈ codom P := p3 ▸ cS.mem b h hh hbh
            obtain ⟨g, hg, hag⟩ := cR.dom_ex a (p2 a b hab).1
            exact ⟨g, hg, hh, a, b, hag, hbh, hab⟩
      refine ⟨Q, ?_, hQ⟩
      rw [dpar_iff]
      funext a b
      apply propext
      constructor
      · intro hab
        obtain ⟨g, hg, hag⟩ := cR.dom_ex a (p2 a b hab).1
        obtain ⟨h, hh, hbh⟩ := cS.dom_ex b (p2 a b hab).2
        exact ⟨g, hag, h, ⟨hg, hh, a, b, hag, hbh, hab⟩, hbh⟩
      · rintro ⟨g, hag, h, ⟨hg, hh, a', b', hag', hbh', hab'⟩, hbh⟩
        rw [cR.uniq a a' g hg hag hag', cS.uniq b b' h hh hbh hbh']
        exact hab'
    · rintro ⟨Q, hPQ, hQ⟩
      rw [dpar_iff] at hPQ
      rw [hPQ]; exact img Q hQ
  · show sel (cross G H) H = codom _
    ext Q
    exact ⟨fun h => ⟨R ⨾ (Q ⨾ S˘), (dpar_iff _ _ _ _).2 rfl, h⟩, fun ⟨_, _, h⟩ => h⟩

/-- ✱116·2. \(\vdash : \xi \in \mu ^\nu . \equiv . (\exists \alpha , \beta ) . \mu = \text{N}_{0}\text{c}ʻ\alpha . \nu = \text{N}_{0}\text{c}ʻ\beta . \xi \text{ sm } (\alpha \,\,\text{exp}\,\, \beta ) \quad[(*116·02)]\) -/
theorem pm116_2 {α β γ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ξ : Set γ} :
    ξ ∈ (μ ^ᶜ ν : Set (Set γ)) ↔
      ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm ξ (clsExp A B) := Iff.rfl

private theorem pmB2_n₀c_not_mem_iota {Z : Type*} (C : Set Z) : n₀c C ∉ ι (Λ : Set (Set Z)) := by
  intro h'; rw [mem_unitCls, Null_eq_empty] at h'; exact n₀c_ne_empty C h'

/-- ✱116·201. \[\begin{align}&\vdash \colon\ldotp \xi \in \mu ^\nu . \equiv : \mu , \nu \in \text{NC} : (\exists \alpha , \beta ) . \alpha \in \mu . \beta \in \nu . \xi \text{ sm } (\alpha \,\,\text{exp}\,\, \beta )\\ &[*116·2 . *103·27]\end{align}\]

`μ, ν ∈ NC` is `μ ∈ NC X ∧ ν ∈ NC Y`, the converse domains of the two `NC`s taken in the types of
the members of `μ` and `ν` (the types in which `μ = N₀c'α`, `ν = N₀c'β` by ✱116·2).

**Status.** proved (reading): the type of the converse domain of `NC` (left ambiguous by PM,
Defs/Part3, decision 3) is taken to be the type of the members of `μ`, `ν`; for an arbitrary type
the implication from left to right would fail. -/
theorem pm116_201 {X Y T : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {ξ : Set T} :
    ξ ∈ (μ ^ᶜ ν : Set (Set T)) ↔
      (μ ∈ NC X ∧ ν ∈ NC Y) ∧ ∃ A B, (A ∈ μ ∧ B ∈ ν) ∧ sm ξ (clsExp A B) := by
  constructor
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    exact ⟨⟨pmB2_n₀c_mem_NC A, pmB2_n₀c_mem_NC B⟩, A, B, ⟨self_mem_n₀c A, self_mem_n₀c B⟩, h⟩
  · rintro ⟨⟨hμ, hν⟩, A, B, ⟨hA, hB⟩, h⟩
    exact ⟨A, B, ⟨pmB2_NC_eq_n₀c hμ hA, pmB2_NC_eq_n₀c hν hB⟩, h⟩

/-- ✱116·202. \[\begin{align}&\vdash \colon\ldotp \xi \in \mu ^\nu . \equiv :\exists !\mu .\exists !\nu :(\exists \alpha ,\beta ).\mu = \text{Nc}ʻ\alpha .\nu = \text{Nc}ʻ\beta .\xi \text{ sm } (\alpha \,\,\text{exp}\,\, \beta )\\ &[\text{Proof as in}\, *113·202]\end{align}\]

The apparent variables `α`, `β` are classes of the types of the members of `μ`, `ν`.

**Status.** proved (reading): the types of the apparent variables `α`, `β` (left ambiguous) are
taken to be the types of the members of `μ`, `ν`. -/
theorem pm116_202 {X Y T : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {ξ : Set T} :
    ξ ∈ (μ ^ᶜ ν : Set (Set T)) ↔ (μ.Nonempty ∧ ν.Nonempty) ∧
      ∃ (A : Set X) (B : Set Y), (μ = nc X A ∧ ν = nc Y B) ∧ sm ξ (clsExp A B) := by
  constructor
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    exact ⟨⟨n₀c_nonempty A, n₀c_nonempty B⟩, A, B, ⟨n₀c_eq_nc A, n₀c_eq_nc B⟩, h⟩
  · rintro ⟨-, A, B, ⟨hA, hB⟩, h⟩
    exact ⟨A, B, ⟨hA.trans (n₀c_eq_nc A).symm, hB.trans (n₀c_eq_nc B).symm⟩, h⟩

/-- ✱116·203. \(\vdash :\exists !\mu ^\nu .\supset .\mu ,\nu \in \text{NC}-\iota ʻ\Lambda .\mu ,\nu \in \text{N}_0\text{C} \quad[*116·201·202·2]\)

**Status.** proved (reading): the converse domains of the `NC`s are in the types of the members
of `μ`, `ν` (as in ✱116·201). -/
theorem pm116_203 {X Y T : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    (μ ^ᶜ ν : Set (Set T)).Nonempty →
      (μ ∈ NC X \ ι Λ ∧ ν ∈ NC Y \ ι Λ) ∧ (μ ∈ N₀C ∧ ν ∈ N₀C) := by
  intro h
  obtain ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩ := pmB2_mem_N₀C_of_nonempty h
  exact ⟨⟨⟨pmB2_n₀c_mem_NC A, pmB2_n₀c_not_mem_iota A⟩, ⟨pmB2_n₀c_mem_NC B,
    pmB2_n₀c_not_mem_iota B⟩⟩, ⟨A, rfl⟩, ⟨B, rfl⟩⟩

/-- ✱116·204. \(\vdash \colon\ldotp \mu = \Lambda .\lor.\nu = \Lambda .\lor.{\sim}(\mu ,\nu \in \text{NC}):\supset .\mu ^\nu = \Lambda \quad[*116·203]\)

**Status.** proved (reading): the converse domains of the `NC`s are in the types of the members
of `μ`, `ν` (as in ✱116·201). -/
theorem pm116_204 {X Y T : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    (μ = Λ ∨ ν = Λ) ∨ ¬(μ ∈ NC X ∧ ν ∈ NC Y) → (μ ^ᶜ ν : Set (Set T)) = Λ := by
  intro h
  rw [Null_eq_empty]
  by_contra hne
  obtain ⟨⟨⟨hμ, hμΛ⟩, ⟨hν, hνΛ⟩⟩, -⟩ := pm116_203 (Set.nonempty_iff_ne_empty.2 hne)
  rcases h with (h | h) | h
  · exact hμΛ (by rw [h]; rfl)
  · exact hνΛ (by rw [h]; rfl)
  · exact h ⟨hμ, hν⟩

/-- ✱116·205. \(\vdash :{\sim}(\mu ,\nu \in \text{N}_0\text{C}).\supset .\mu ^\nu = \Lambda \quad [*116·203]\) -/
theorem pm116_205 {X Y T : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    ¬(μ ∈ N₀C ∧ ν ∈ N₀C) → (μ ^ᶜ ν : Set (Set T)) = Λ := by
  intro h; rw [Null_eq_empty]; exact pmB2_cardExp_empty h

/-- ✱116·22. \[\begin{align}&\vdash :\xi \in {\text{Nc}(\eta )ʻ\gamma }^{\text{Nc}(\zeta )ʻ^\delta }. \equiv .\exists !\text{Nc}(\eta )ʻ\gamma .\exists !\text{Nc}(\zeta )ʻ\delta .\xi \text{ sm } (\gamma \,\,\text{exp}\,\, \delta )\\ &[\text{Proof as in *113·22, using *116·19 in place of *113·13}]\end{align}\]

`Nc(η)'γ` is the typically definite `nc Tη G` (`η : Set Tη`, ✱65·04); its type is indicated
expressly, so it is an ascription (no normal adjustment, no adequacy hypothesis). The e-text prints
`Nc(ζ)'^δ` for `Nc(ζ)'δ`.

**Status.** proved (reading): transcription error `Nc(ζ)'^δ` read `Nc(ζ)'δ`; the explicitly typed
`Nc(η)'γ`, `Nc(ζ)'δ` are taken in their indicated types. -/
theorem pm116_22 {α β Tη Tζ T : Type*} {G : Set α} {H : Set β} {ξ : Set T} :
    ξ ∈ (nc Tη G ^ᶜ nc Tζ H : Set (Set T)) ↔
      ((nc Tη G).Nonempty ∧ (nc Tζ H).Nonempty) ∧ sm ξ (clsExp G H) := by
  constructor
  · rintro ⟨A, B, ⟨hA, hB⟩, h⟩
    have hA' : A ∈ nc Tη G := hA ▸ self_mem_n₀c A
    have hB' : B ∈ nc Tζ H := hB ▸ self_mem_n₀c B
    exact ⟨⟨⟨A, hA'⟩, ⟨B, hB'⟩⟩, sm_trans h (pmB2_sm_clsExp hA' hB')⟩
  · rintro ⟨⟨⟨A, hA⟩, ⟨B, hB⟩⟩, h⟩
    exact ⟨A, B, ⟨nc_eq_n₀c_of_mem hA, nc_eq_n₀c_of_mem hB⟩,
      sm_trans h (pmB2_sm_clsExp (sm_symm hA) (sm_symm hB))⟩

/-- ✱116·221. \[\begin{align}&\vdash :\exists !\text{Nc}(\eta )ʻ\gamma .\exists !\text{Nc}(\zeta )ʻ\delta .\supset .{\text{Nc}(\eta )ʻ\gamma }^{\text{Nc}(\zeta )ʻ\delta } = \text{Nc}ʻ(\gamma \,\,\text{exp}\,\, \delta )\\ &[*116·22]\end{align}\]

`Nc(η)'γ`, `Nc(ζ)'δ` as in ✱116·22; the equation is in a free type `T`. -/
theorem pm116_221 {α β Tη Tζ T : Type*} {G : Set α} {H : Set β} :
    (nc Tη G).Nonempty ∧ (nc Tζ H).Nonempty →
      (nc Tη G ^ᶜ nc Tζ H : Set (Set T)) = nc T (clsExp G H) := by
  intro h
  ext ξ
  rw [pm116_22]
  exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩

/-- ✱116·222. \(\vdash .(\text{N}_0\text{c}ʻ\gamma )^{\text{N}_0\text{c}ʻ\delta } = \text{Nc}ʻ(\gamma \,\,\text{exp}\,\, \delta ) \quad[\text{Proof as in *113·222}]\) -/
theorem pm116_222 {α β T : Type*} {G : Set α} {H : Set β} :
    (n₀c G ^ᶜ n₀c H : Set (Set T)) = nc T (clsExp G H) := pmB2_n₀c_exp G H

private theorem pmB2_nc_univ_set {T : Type*} : nc T (Set.univ : Set (Set T)) = ∅ := by
  ext Y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hY
  obtain ⟨e⟩ := mem_nc_iff_equiv.1 hY
  exact Function.cantor_injective (fun s : Set T => ((e.symm ⟨s, trivial⟩ : ↥Y) : T))
    (fun s t h => by
      have := e.symm.injective (Subtype.ext h)
      exact congrArg Subtype.val this)

private theorem pmB2_nc_mem_NC_set {Z T : Type*} (C : Set Z) : nc T C ∈ NC (Set T) := by
  by_cases h : (nc T C).Nonempty
  · obtain ⟨X, hX⟩ := h
    refine ⟨(fun x => ({x} : Set T)) '' X, ?_⟩
    rw [nc_eq_n₀c_of_mem hX, n₀c_eq_nc]
    apply nc_eq_nc_of_sm
    exact pmB2_sm_of_equiv (Equiv.Set.image _ X (fun a b e => Set.singleton_injective e))
  · rw [Set.not_nonempty_iff_eq_empty] at h
    exact ⟨Set.univ, h.trans pmB2_nc_univ_set.symm⟩

/-- ✱116·23. \(\vdash .\mu ^\nu \in \text{NC} \quad[\text{Proof as in *113·23}]\)

**Status.** proved (reading): the converse domain of `NC` (left ambiguous by PM) is taken in the
type `Set T` of classes of members of the type `T` of `μ^ν`'s members, where every existent
cardinal of type `T` and also `Λ` (as `Nc'` of the whole type `Set T`, by Cantor) are numbers of
classes; in the type `T` itself `Λ` is not a number of any class. -/
theorem pm116_23 {X Y T : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    (μ ^ᶜ ν : Set (Set T)) ∈ NC (Set T) := by
  by_cases h : μ ∈ N₀C ∧ ν ∈ N₀C
  · obtain ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩ := h
    rw [pmB2_n₀c_exp]
    exact pmB2_nc_mem_NC_set _
  · rw [pmB2_cardExp_empty h]
    exact ⟨Set.univ, pmB2_nc_univ_set.symm⟩

/-- ✱116·24. \(\vdash .(\text{Nc}ʻ\gamma )^{\text{Nc}ʻ\delta } = (\text{N}_0\text{c}ʻ\gamma )^{\text{N}_0\text{c}ʻ\delta } \quad[(*116·03·04)]\)

By the Dfs ✱116·03·04 the arithmetical occurrences `Nc'γ`, `Nc'δ` are `N₀c'γ`, `N₀c'δ`, so the
two sides are the same.

**Status.** proved (reading): by the translation rules ✱116·03·04 (normal adjustment) the two
sides are identical. -/
theorem pm116_24 {α β T : Type*} {G : Set α} {H : Set β} :
    (n₀c G ^ᶜ n₀c H : Set (Set T)) = n₀c G ^ᶜ n₀c H := rfl

/-- ✱116·25. \(\vdash .(\text{Nc}ʻ\gamma )^{\text{Nc}ʻ\delta } = \text{Nc}ʻ(\gamma \,\,\text{exp}\,\, \delta ) \quad[*116·24·222]\)

**Status.** proved (reading): the arguments `Nc'γ`, `Nc'δ` of `^` are `N₀c'γ`, `N₀c'δ`
(✱116·03·04); the equation is in a free type `T`. -/
theorem pm116_25 {α β T : Type*} {G : Set α} {H : Set β} :
    (n₀c G ^ᶜ n₀c H : Set (Set T)) = nc T (clsExp G H) := pmB2_n₀c_exp G H

/-- ✱116·251. \(\vdash .(\gamma \,\,\text{exp}\,\, \delta )\in (\text{Nc}ʻ\gamma )^{\text{Nc}ʻ\delta } \quad[*116·25.*100·3]\)

**Status.** proved (reading): the arguments `Nc'γ`, `Nc'δ` of `^` are `N₀c'γ`, `N₀c'δ`
(✱116·03·04); `(Nc'γ)^{Nc'δ}` is in the type of `γ exp δ` (significance). -/
theorem pm116_251 {α β : Type*} {G : Set α} {H : Set β} :
    clsExp G H ∈ (n₀c G ^ᶜ n₀c H : Set (Set (Set (α → β → Prop)))) := by
  rw [pmB2_n₀c_exp]; exact self_mem_nc _

/-- ✱116·26. \[\begin{align}&\vdash :\mu ,\nu \in \text{NC}.\exists !\text{ sm }_\eta ʻʻ\mu .\exists !\text{ sm }_\zetaʻʻ\nu .\supset .\mu ^\nu = (\text{ sm }_\eta ʻʻ\mu )^{\text{ sm }_\zetaʻʻ\nu }\\ &[\text{Proof as in *113·26}]\end{align}\]

`sm_η''μ` is the typically definite `(sm ʻʻ μ : Set (Set Tη))` (an ascription). -/
theorem pm116_26 {X Y β₁ β₂ Tη Tζ T : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    ((μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ (sm ʻʻ μ : Set (Set Tη)).Nonempty) ∧
        (sm ʻʻ ν : Set (Set Tζ)).Nonempty →
      (μ ^ᶜ ν : Set (Set T)) = (sm ʻʻ μ : Set (Set Tη)) ^ᶜ (sm ʻʻ ν : Set (Set Tζ)) := by
  rintro ⟨⟨⟨hμ, hν⟩, ⟨Z, A, hA, hZ⟩⟩, ⟨Z', B, hB, hZ'⟩⟩
  have h1 : (nc Tη A).Nonempty := ⟨Z, sm_trans hZ (mem_n₀c.1 (pmB2_NC_eq_n₀c hμ hA ▸ hA))⟩
  have h2 : (nc Tζ B).Nonempty := ⟨Z', sm_trans hZ' (mem_n₀c.1 (pmB2_NC_eq_n₀c hν hB ▸ hB))⟩
  rw [pmB2_NC_eq_n₀c hμ hA, pmB2_NC_eq_n₀c hν hB, sm_img_n₀c, sm_img_n₀c]
  rw [pm116_221 ⟨h1, h2⟩, pmB2_n₀c_exp]

private theorem pmB2_NC_cases {X β : Type*} {μ : Set (Set X)} (h : μ ∈ NC β) :
    μ = ∅ ∨ ∃ A, μ = n₀c A := by
  rcases μ.eq_empty_or_nonempty with e | ⟨A, hA⟩
  · exact Or.inl e
  · exact Or.inr ⟨A, pmB2_NC_eq_n₀c h hA⟩

private theorem pmB2_sm_img_n₀c_inj {X Z : Type*} (f : X → Z) (hf : Function.Injective f) (A : Set X) :
    (sm ʻʻ n₀c A : Set (Set Z)) = n₀c (f '' A) := by
  rw [sm_img_n₀c, n₀c_eq_nc]
  exact nc_eq_nc_of_sm (pmB2_sm_of_equiv (Equiv.Set.image f A hf))

private theorem pmB2_up1_eq {Z : Type*} (μ : Set (Set Z)) : up1 μ = sm ʻʻ μ := by
  rw [up1, typ_eq_univ, Set.inter_univ]

private theorem pmB2_down00_eq {Z : Type*} (μ : Set (Set Z)) : down00 μ = sm ʻʻ μ := by
  rw [down00, typ_eq_univ, Set.inter_univ]

private theorem pmB2_sm_img_empty {Z W : Type*} : (sm ʻʻ (∅ : Set (Set Z)) : Set (Set W)) = ∅ := by
  ext x; simp only [Set.mem_empty_iff_false, iff_false]; rintro ⟨y, hy, -⟩; exact hy

private theorem pmB2_empty_not_N₀C {Z : Type*} : (∅ : Set (Set Z)) ∉ N₀C :=
  fun ⟨C, hC⟩ => n₀c_ne_empty C hC.symm

private theorem pmB2_singleton_inj {Z : Type*} : Function.Injective (fun x : Z => ({x} : Set Z)) :=
  fun _ _ e => Set.singleton_injective e

private theorem pmB2_diag_inj {Z : Type*} : Function.Injective (fun x : Z => x ↓ x) :=
  fun _ _ e => (couple_eq_couple_iff.1 e).1

/-- ✱116·261. \(\vdash :\mu ,\nu \in \text{NC}.\supset .\mu ^\nu = \{\mu ^{(1)}\}^{\nu ^{(1)}} = \{\mu _{(00)}\}^{\nu _{(00)}} = etc. \quad[\text{Proof as in *113·261}]\)

`μ^{(1)}` is `up1 μ`, `μ_{(00)}` is `down00 μ`. The chain is the conjunction of its two printed
links (PM's "etc." continues it with the other ascending and descending forms). -/
theorem pm116_261 {X Y β₁ β₂ T : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ ∈ NC β₁ ∧ ν ∈ NC β₂ →
      (μ ^ᶜ ν : Set (Set T)) = up1 μ ^ᶜ up1 ν ∧
        (up1 μ ^ᶜ up1 ν : Set (Set T)) = down00 μ ^ᶜ down00 ν := by
  rintro ⟨hμ, hν⟩
  rw [pmB2_up1_eq, pmB2_up1_eq, pmB2_down00_eq, pmB2_down00_eq]
  rcases pmB2_NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [pmB2_sm_img_empty, pmB2_sm_img_empty,
      pmB2_cardExp_empty (fun h => pmB2_empty_not_N₀C h.1),
      pmB2_cardExp_empty (fun h => pmB2_empty_not_N₀C h.1),
      pmB2_cardExp_empty (fun h => pmB2_empty_not_N₀C h.1)]
    exact ⟨rfl, rfl⟩
  rcases pmB2_NC_cases hν with rfl | ⟨B, rfl⟩
  · rw [pmB2_sm_img_empty, pmB2_sm_img_empty,
      pmB2_cardExp_empty (fun h => pmB2_empty_not_N₀C h.2),
      pmB2_cardExp_empty (fun h => pmB2_empty_not_N₀C h.2),
      pmB2_cardExp_empty (fun h => pmB2_empty_not_N₀C h.2)]
    exact ⟨rfl, rfl⟩
  rw [pmB2_sm_img_n₀c_inj _ pmB2_singleton_inj, pmB2_sm_img_n₀c_inj _ pmB2_singleton_inj,
    pmB2_sm_img_n₀c_inj _ pmB2_diag_inj, pmB2_sm_img_n₀c_inj _ pmB2_diag_inj, pmB2_n₀c_exp,
    pmB2_n₀c_exp, pmB2_n₀c_exp]
  have sA1 := pmB2_sm_of_equiv (Equiv.Set.image _ A pmB2_singleton_inj)
  have sB1 := pmB2_sm_of_equiv (Equiv.Set.image _ B pmB2_singleton_inj)
  have sA2 := pmB2_sm_of_equiv (Equiv.Set.image _ A pmB2_diag_inj)
  have sB2 := pmB2_sm_of_equiv (Equiv.Set.image _ B pmB2_diag_inj)
  exact ⟨nc_eq_nc_of_sm (pmB2_sm_clsExp sA1 sB1),
    nc_eq_nc_of_sm (pmB2_sm_clsExp (sm_trans (sm_symm sA1) sA2) (sm_trans (sm_symm sB1) sB2))⟩

/-- ✱116·27. \[\begin{align}&\vdash .\mu ^\nu = \hat{\xi} \{(\exists \alpha ,\beta ).\mu = \text{N}_0\text{c}ʻ\alpha .\nu = \text{N}_0\text{c}ʻ\beta .\xi \text{ sm } (\alpha \uparrow \beta )_{\Delta }ʻ\beta\}\\ &[*116·15.*73·37.(*116·02)]\end{align}\]

`(α ↑ β)_Δ'β` is `sel (cross A B) B`. -/
theorem pm116_27 {X Y T : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    (μ ^ᶜ ν : Set (Set T)) =
      {ξ | ∃ (A : Set X) (B : Set Y), (μ = n₀c A ∧ ν = n₀c B) ∧ sm ξ (sel (cross A B) B)} := by
  ext ξ
  exact ⟨fun ⟨A, B, h, h'⟩ => ⟨A, B, h, sm_trans h' pm116_15⟩,
    fun ⟨A, B, h, h'⟩ => ⟨A, B, h, sm_trans h' (sm_symm pm116_15)⟩⟩

/-- ✱116·271. \(\vdash :\mu ,\nu \in \text{NC}.\alpha \in \mu .\beta \in \nu .\supset .(\alpha \,\,\text{exp}\,\, \beta )\in \mu ^\nu \quad[*116·21]\)

`μ^ν` is taken in the type of `α exp β` (significance). -/
theorem pm116_271 {X Y β₁ β₂ : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {A : Set X}
    {B : Set Y} :
    ((μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ A ∈ μ) ∧ B ∈ ν →
      clsExp A B ∈ (μ ^ᶜ ν : Set (Set (Set (X → Y → Prop)))) := by
  rintro ⟨⟨⟨hμ, hν⟩, hA⟩, hB⟩
  rw [pmB2_NC_eq_n₀c hμ hA, pmB2_NC_eq_n₀c hν hB, pmB2_n₀c_exp]
  exact self_mem_nc _

private theorem pmB2_exp_zero {X W T : Type*} (A : Set X) :
    (n₀c A ^ᶜ (zero : Set (Set W)) : Set (Set T)) = one := by
  rw [zero_eq_n₀c_empty, pmB2_n₀c_exp]
  have : Unique ↥(clsExp A (∅ : Set W)) := (pmB2_clsExpEquiv _ _).unique
  exact pmB2_nc_eq_one

/-- ✱116·3. \(\vdash .(\text{Nc}ʻ\alpha )^{0} = 1\)

**Status.** proved (reading): the argument `Nc'α` of `^` is `N₀c'α` (✱116·03); the exponent `0`
is an arithmetical constant, taken in a type `W` of its own (convention IIT; `0` exists in every
type, so no hypothesis is needed); the equation is in a free type `T`. -/
theorem pm116_3 {X W T : Type*} {A : Set X} :
    (n₀c A ^ᶜ (zero : Set (Set W)) : Set (Set T)) = one := pmB2_exp_zero A

/-- ✱116·301. \(\vdash :\mu \in \text{NC}-\iota ʻ\Lambda .\supset .\mu ^{0} = 1 \quad[\text{Proof as in *113·601}]\)

**Status.** proved (reading): the exponent `0` is taken in a type `W` of its own (convention
IIT; no hypothesis is needed for `0`). -/
theorem pm116_301 {X W T β : Type*} {μ : Set (Set X)} :
    μ ∈ NC β \ ι Λ → (μ ^ᶜ (zero : Set (Set W)) : Set (Set T)) = one := by
  intro h
  obtain ⟨A, rfl⟩ := pmB2_NC_ne h
  exact pmB2_exp_zero A

/-- ✱116·31. \(\vdash :\beta \neq \Lambda .\supset .0^{\text{Nc}ʻ\beta } = 0\)

**Status.** proved (reading): the argument `Nc'β` of `^` is `N₀c'β` (✱116·04); the base `0` is
taken in a type `W` of its own (convention IIT; no hypothesis is needed for `0`). -/
theorem pm116_31 {X W T : Type*} {B : Set X} :
    B ≠ Λ → ((zero : Set (Set W)) ^ᶜ n₀c B : Set (Set T)) = zero := by
  intro hB
  rw [Null_eq_empty] at hB
  rw [zero_eq_n₀c_empty (α := W), pmB2_n₀c_exp, ← Null_eq_empty (α := W),
    pm116_182 (Set.nonempty_iff_ne_empty.2 hB)]
  exact pmB2_nc_eq_zero Null_eq_empty

private theorem pmB2_exp_one {X W T : Type*} [Nonempty W] (A : Set X) :
    (n₀c A ^ᶜ (one : Set (Set W)) : Set (Set T)) = nc T A := by
  obtain ⟨w⟩ := ‹Nonempty W›
  rw [one_eq_n₀c_singleton w, pmB2_n₀c_exp]
  exact nc_eq_nc_of_sm (pmB2_sm_of_equiv ((pmB2_clsExpEquiv A {w}).trans (Equiv.funUnique _ _)))

/-- ✱116·32. \(\vdash .(\text{Nc}ʻ\alpha )^{1}=\text{Nc}ʻ\alpha\)

**Status.** proved (reading): the argument `Nc'α` of `^` is `N₀c'α` (✱116·03); the exponent `1`
is taken in a type `W` in which it exists (`[Nonempty W]`, convention IIT). -/
theorem pm116_32 {X W T : Type*} [Nonempty W] {A : Set X} :
    (n₀c A ^ᶜ (one : Set (Set W)) : Set (Set T)) = nc T A := pmB2_exp_one A

/-- ✱116·321. \(\vdash .\mu \in \text{NC}-\iota ʻ\Lambda .\supset .\mu ^{1}=\text{ sm }ʻʻ\mu \quad[*116·32]\)

**Status.** proved (reading): the exponent `1` is taken in a type `W` in which it exists
(`[Nonempty W]`, convention IIT). -/
theorem pm116_321 {X W T β : Type*} [Nonempty W] {μ : Set (Set X)} :
    μ ∈ NC β \ ι Λ → (μ ^ᶜ (one : Set (Set W)) : Set (Set T)) = sm ʻʻ μ := by
  intro h
  obtain ⟨A, rfl⟩ := pmB2_NC_ne h
  rw [pmB2_exp_one, sm_img_n₀c]

/-- ✱116·33. \(\vdash .1^{\text{Nc}ʻ\beta }=1\)

**Status.** proved (reading): the argument `Nc'β` of `^` is `N₀c'β` (✱116·04); the base `1` is
taken in a type `W` in which it exists (`[Nonempty W]`, convention IIT). -/
theorem pm116_33 {X W T : Type*} [Nonempty W] {B : Set X} :
    ((one : Set (Set W)) ^ᶜ n₀c B : Set (Set T)) = one := pmB2_one_exp B

/-- ✱116·311. \(\vdash :\mu \in \text{NC}-\iota ʻ\Lambda .\supset .1^{\mu }=1\)

(The same proposition as ✱116·331 of the Summary.)

**Status.** proved (reading): the base `1` is taken in a type `W` in which it exists
(`[Nonempty W]`, convention IIT). -/
theorem pm116_311 {X W T β : Type*} [Nonempty W] {μ : Set (Set X)} :
    μ ∈ NC β \ ι Λ → ((one : Set (Set W)) ^ᶜ μ : Set (Set T)) = one := pm116_331

private theorem pmB2_pair_sm {W V : Type*} {a b : W} {x y : V} (hab : a ≠ b) (hxy : x ≠ y) :
    sm ({x, y} : Set V) ({a, b} : Set W) := by
  classical
  refine pmB2_sm_of_equiv
    { toFun := fun z => if z.1 = x then ⟨a, Or.inl rfl⟩ else ⟨b, Or.inr rfl⟩
      invFun := fun z => if z.1 = a then ⟨x, Or.inl rfl⟩ else ⟨y, Or.inr rfl⟩
      left_inv := ?_, right_inv := ?_ }
  · rintro ⟨z, hz | hz⟩ <;> subst hz
    · simp
    · simp [hxy.symm, hab.symm]
  · rintro ⟨z, hz | hz⟩ <;> subst hz
    · simp
    · simp [hab.symm, hxy.symm]

private theorem pmB2_two_eq {W : Type*} (h : (two : Set (Set W)).Nonempty) :
    ∃ a b : W, a ≠ b ∧ (two : Set (Set W)) = n₀c {a, b} := by
  obtain ⟨X, hX⟩ := h
  obtain ⟨a, b, hab, rfl⟩ := mem_two_iff.1 hX
  refine ⟨a, b, hab, ?_⟩
  ext Y
  rw [mem_two_iff, mem_n₀c]
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact pmB2_pair_sm hab hxy
  · intro h
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
    refine ⟨(e.symm ⟨a, Or.inl rfl⟩).1, (e.symm ⟨b, Or.inr rfl⟩).1, fun h' => hab ?_, ?_⟩
    · have := e.symm.injective (Subtype.ext h'); exact congrArg Subtype.val this
    · ext z
      constructor
      · intro hz
        rcases (e ⟨z, hz⟩).2 with h1 | h1
        · left
          have : e ⟨z, hz⟩ = ⟨a, Or.inl rfl⟩ := Subtype.ext h1
          rw [← this, Equiv.symm_apply_apply]
        · right
          have h1' : ((e ⟨z, hz⟩ : ↥({a, b} : Set W)) : W) = b := h1
          have : e ⟨z, hz⟩ = ⟨b, Or.inr rfl⟩ := Subtype.ext h1'
          show z = _
          rw [← this, Equiv.symm_apply_apply]
      · rintro (rfl | rfl)
        · exact (e.symm _).2
        · exact (e.symm _).2

/-- ✱116·34. \(\vdash .\mu ^{2}=\mu \times _{c}\mu\)

**Status.** proved (reading): the exponent `2` is taken in a type `W` in which it exists
(convention IIT: `(two : Set (Set W)).Nonempty`); the equation is in a free type `T`. -/
theorem pm116_34 {X W T : Type*} {μ : Set (Set X)} (h2 : (two : Set (Set W)).Nonempty) :
    (μ ^ᶜ (two : Set (Set W)) : Set (Set T)) = μ ×ᶜ μ := by
  obtain ⟨a, b, hab, e2⟩ := pmB2_two_eq h2
  by_cases hμ : μ ∈ N₀C
  · obtain ⟨A, rfl⟩ := hμ
    rw [e2, pmB2_n₀c_exp, pmB2_n₀c_mul]
    apply nc_eq_nc_of_sm
    classical
    refine pmB2_sm_of_equiv ((pmB2_clsExpEquiv A {a, b}).trans (Equiv.trans ?_
      (pmB2_clsTimesEquiv A A).symm))
    exact { toFun := fun f => (f ⟨a, Or.inl rfl⟩, f ⟨b, Or.inr rfl⟩)
            invFun := fun p z => if z.1 = a then p.1 else p.2
            left_inv := fun f => by
              funext ⟨z, hz⟩
              rcases hz with hz | hz <;> subst hz <;> simp [hab.symm]
            right_inv := fun p => by simp [hab.symm] }
  · rw [pmB2_cardExp_empty (fun h => hμ h.1), pmB2_cardMul_empty (fun h => hμ h.1)]

/-- ✱116·35. \(\vdash :\mu ^{\nu }=0.\equiv .\mu =0.\nu \in \text{NC}-\iota ʻ0-\iota ʻ\Lambda\)

`0` on the left is in the type `T` of the equation, `μ = 0` in the type of `μ`, `ι'0` in the
type of `ν`.

**Status.** proved (reading): the converse domain of `NC` is taken in the type of the members of
`ν` (as in ✱116·201). -/
theorem pm116_35 {X Y T : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    (μ ^ᶜ ν : Set (Set T)) = zero ↔ μ = zero ∧ ν ∈ (NC Y \ ι zero) \ ι Λ := by
  constructor
  · intro h
    have hne : (μ ^ᶜ ν : Set (Set T)).Nonempty := by rw [h, zero_eq]; exact ⟨∅, rfl⟩
    obtain ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩ := pmB2_mem_N₀C_of_nonempty hne
    rw [pmB2_n₀c_exp, ← pmB2_nc_eq_zero (α := T) (S := (∅ : Set T)) rfl] at h
    have hs : sm (clsExp A B) (∅ : Set T) :=
      (nc_eq_nc_iff (γ := T) (by rw [h, ← n₀c_eq_nc]; exact n₀c_nonempty _)).1 h
    have he : clsExp A B = ∅ := by
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hs
      exact Set.eq_empty_iff_forall_notMem.2 fun ξ hξ => (e ⟨ξ, hξ⟩).2
    have h18 := mt (pm116_171 (A := A) (B := B)) (by rw [he]; exact Set.not_nonempty_empty)
    rw [not_or, Set.not_nonempty_iff_eq_empty, Null_eq_empty] at h18
    obtain ⟨hA, hB⟩ := h18
    subst hA
    refine ⟨zero_eq_n₀c_empty.symm, ⟨⟨pmB2_n₀c_mem_NC B, fun h' => ?_⟩, fun h' => ?_⟩⟩
    · rw [mem_unitCls, zero_eq_n₀c_empty, n₀c_eq_n₀c_iff] at h'
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h'
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hB
      exact (e ⟨y, hy⟩).2
    · rw [mem_unitCls, Null_eq_empty] at h'; exact n₀c_ne_empty B h'
  · rintro ⟨rfl, ⟨⟨hν, hν0⟩, hνΛ⟩⟩
    obtain ⟨B, rfl⟩ := pmB2_NC_ne ⟨hν, hνΛ⟩
    have hB : B.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro rfl
      exact hν0 (by rw [mem_unitCls, zero_eq_n₀c_empty])
    rw [zero_eq_n₀c_empty (α := X), pmB2_n₀c_exp, ← Null_eq_empty (α := X), pm116_182 hB]
    exact pmB2_nc_eq_zero Null_eq_empty

private theorem pmB2_piNc_empty {X T : Type*} : piNc T (∅ : Set (Set X)) = one := by
  have : Unique ↥(sel memRel (∅ : Set (Set X))) := (pmB2_selE ∅).unique
  exact pmB2_nc_eq_one

/-- ✱116·351. \[\begin{align}&\vdash :\mu \in \text{NC}-\iota ʻ\Lambda .\kappa =\Lambda .\nu =0.\supset .\mu ^\nu =\Pi \text{Nc}ʻ\kappa =1\\ &[*116·301.*114·2]\end{align}\]

`κ` is a class of classes of any type `X`; the chain is the conjunction of its links, in one type
`T`. -/
theorem pm116_351 {X Y Z T β : Type*} {μ : Set (Set Y)} {K : Set (Set X)} {ν : Set (Set Z)} :
    (μ ∈ NC β \ ι Λ ∧ K = Λ) ∧ ν = zero →
      (μ ^ᶜ ν : Set (Set T)) = piNc T K ∧ piNc T K = one := by
  rintro ⟨⟨hμ, hK⟩, rfl⟩
  rw [Null_eq_empty] at hK
  subst hK
  rw [pm116_301 hμ, pmB2_piNc_empty]
  exact ⟨rfl, rfl⟩

/-- ✱116·352. \[\begin{align}&\vdash :\mu =0.\nu \in \text{NC}-\iota ʻ\Lambda .\kappa \in \nu .\Lambda \in \kappa .\supset .\mu ^\nu =\Pi \text{Nc}ʻ\kappa =0\\ &[*116·311.*114·23]\end{align}\]

`κ ∈ ν`: `ν` is a cardinal of classes of classes. -/
theorem pm116_352 {X Y T β : Type*} {μ : Set (Set Y)} {ν : Set (Set (Set X))}
    {K : Set (Set X)} :
    ((μ = zero ∧ ν ∈ NC β \ ι Λ) ∧ K ∈ ν) ∧ (Λ : Set X) ∈ K →
      (μ ^ᶜ ν : Set (Set T)) = piNc T K ∧ piNc T K = zero := by
  rintro ⟨⟨⟨rfl, hν⟩, hK⟩, hΛ⟩
  rw [Null_eq_empty] at hΛ
  have hpi : piNc T K = zero := pmB2_nc_eq_zero (pmB2_sel_empty_of hΛ)
  rw [hpi, pmB2_NC_eq_n₀c hν.1 hK, zero_eq_n₀c_empty (α := Y), pmB2_n₀c_exp,
    ← Null_eq_empty (α := Y), pm116_182 ⟨∅, hΛ⟩]
  exact ⟨pmB2_nc_eq_zero Null_eq_empty, rfl⟩

/-- ✱116·353. \(\vdash :\mu =0.\nu \in \text{NC}-\iota ʻ\Lambda .\kappa \in \nu \cap \text{Cl}ʻ\mu .\supset .\mu ^\nu =\Pi \text{Nc}ʻ\kappa\)

`κ ∈ Cl'μ` makes `κ` a class of classes of the type of `μ`'s members. -/
theorem pm116_353 {X T β : Type*} {μ : Set (Set X)} {ν : Set (Set (Set X))}
    {K : Set (Set X)} :
    (μ = zero ∧ ν ∈ NC β \ ι Λ) ∧ K ∈ ν ∩ cl μ → (μ ^ᶜ ν : Set (Set T)) = piNc T K := by
  rintro ⟨⟨rfl, hν⟩, hKν, hKμ⟩
  rw [pmB2_NC_eq_n₀c hν.1 hKν, zero_eq_n₀c_empty (α := X), pmB2_n₀c_exp]
  rw [mem_cl, zero_eq] at hKμ
  rcases Set.subset_singleton_iff_eq.1 hKμ with rfl | rfl
  · rw [pmB2_piNc_empty]
    have : Unique ↥(clsExp (∅ : Set X) (∅ : Set (Set X))) :=
      (pmB2_clsExpEquiv _ _).unique
    exact pmB2_nc_eq_one
  · rw [← Null_eq_empty (α := X), pm116_182 ⟨Λ, rfl⟩, pmB2_nc_eq_zero Null_eq_empty]
    exact (pmB2_nc_eq_zero (pmB2_sel_empty_of (by rw [← Null_eq_empty]; rfl))).symm

/-- ✱116·36. \(\vdash \colon\ldotp \text{Mult ax}.\supset :\mu ,\nu \in \text{NC}-\iota ʻ\Lambda .\kappa \in \nu \cap \text{Cl}ʻ\mu .\supset .\Pi \text{Nc}ʻ\kappa =\mu ^\nu\)

`Mult ax` is taken at the type of the members of the members of `κ` (`κ ⊆ μ`, classes of `X`);
the hypothesis is kept as PM has it (it is a theorem of Lean, Basic §4, and is not used). -/
theorem pm116_36 {X T β₁ β₂ : Type*} {μ : Set (Set X)} {ν : Set (Set (Set X))}
    {K : Set (Set X)} :
    MultAx X → (μ ∈ NC β₁ \ ι Λ ∧ ν ∈ NC β₂ \ ι Λ) ∧ K ∈ ν ∩ cl μ →
      piNc T K = (μ ^ᶜ ν : Set (Set T)) := by
  rintro - ⟨⟨hμ, hν⟩, hKν, hKμ⟩
  obtain ⟨A, rfl⟩ := pmB2_NC_ne hμ
  rw [pmB2_NC_eq_n₀c hν.1 hKν, pmB2_n₀c_exp]
  apply nc_eq_nc_of_sm
  exact pmB2_sm_of_equiv ((pmB2_selE K).trans ((Equiv.piCongrRight fun Y : ↥K =>
    Classical.choice (sm_iff_nonempty_equiv.1 (mem_n₀c.1 (hKμ Y.2)))).trans
      (pmB2_clsExpEquiv A K).symm))

/-- ✱116·361. \(\vdash \colon\ldotp \text{Mult ax} . \supset : \mu , \nu \in \text{NC} - \iota ʻ\Lambda . \kappa \in \nu \cap \text{Cl excl}ʻ\mu . \supset . \text{Prod}ʻ\kappa \in \mu ^\nu\)

`Cl excl'μ` is `clExcl μ`; `μ^ν` is taken in the type of `Prod'κ` (significance). `Mult ax` as in
✱116·36. -/
theorem pm116_361 {X β₁ β₂ : Type*} {μ : Set (Set X)} {ν : Set (Set (Set X))}
    {K : Set (Set X)} :
    MultAx X → (μ ∈ NC β₁ \ ι Λ ∧ ν ∈ NC β₂ \ ι Λ) ∧ K ∈ ν ∩ clExcl μ →
      prodK K ∈ (μ ^ᶜ ν : Set (Set (Set X))) := by
  rintro hM ⟨⟨hμ, hν⟩, hKν, hKex, hKμ⟩
  rw [← pm116_36 (T := Set X) hM ⟨⟨hμ, hν⟩, hKν, hKμ⟩]
  exact pmB2_sm_of_equiv (pmB2_prodEquiv hKex)

private theorem pmB2_smsm_sm {α β : Type*} {K : Set (Set α)} {L : Set (Set β)} (h : smsm K L) :
    sm K L := by
  obtain ⟨T, ⟨⟨h11, hcod⟩, hK⟩⟩ := h
  have hcod' : sumCls L = codom T := hcod
  have hK' : K = imgRel T ʻʻ L := hK
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 h11
  have hinj : Set.InjOn (fun Y => T ʻʻ Y) L := by
    have sub : ∀ Y Y', Y ∈ L → Y' ∈ L → T ʻʻ Y = T ʻʻ Y' → Y ⊆ Y' := by
      intro Y Y' hY hY' e z hz
      obtain ⟨w, hw⟩ : z ∈ codom T := hcod' ▸ ⟨Y, hY, hz⟩
      have : w ∈ T ʻʻ Y' := e ▸ ⟨z, hz, hw⟩
      obtain ⟨z', hz', hw'⟩ := this
      rw [h2 w z z' ⟨hw, hw'⟩]; exact hz'
    intro Y hY Y' hY' e
    exact Set.Subset.antisymm (sub Y Y' hY hY' e) (sub Y' Y hY' hY e.symm)
  have hKL : K = (fun Y => T ʻʻ Y) '' L := by
    rw [hK']; ext X; exact ⟨fun ⟨Y, hY, e⟩ => ⟨Y, hY, e.symm⟩, fun ⟨Y, hY, e⟩ => ⟨Y, hY, e.symm⟩⟩
  rw [hKL]
  exact sm_symm (pmB2_sm_of_equiv (Equiv.Set.imageOfInjOn _ _ hinj))

private theorem pmB2_smsm_trans {α β γ : Type*} {A : Set (Set α)} {B : Set (Set β)} {C : Set (Set γ)}
    (h₁ : smsm A B) (h₂ : smsm B C) : smsm A C := by
  obtain ⟨T₁, ⟨⟨a11, acod⟩, hA⟩⟩ := h₁
  obtain ⟨T₂, ⟨⟨b11, bcod⟩, hB⟩⟩ := h₂
  have acod' : sumCls B = codom T₁ := acod
  have bcod' : sumCls C = codom T₂ := bcod
  have hA' : A = imgRel T₁ ʻʻ B := hA
  have hB' : B = imgRel T₂ ʻʻ C := hB
  obtain ⟨a1, a2⟩ := mem_arrow_one_one.1 a11
  obtain ⟨b1, b2⟩ := mem_arrow_one_one.1 b11
  refine ⟨T₁ ⨾ T₂, ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
  · rintro x x' z ⟨⟨y, h1, h2⟩, ⟨y', h1', h2'⟩⟩
    rw [b1 y y' z ⟨h2, h2'⟩] at h1
    exact a1 x x' y' ⟨h1, h1'⟩
  · rintro x z z' ⟨⟨y, h1, h2⟩, ⟨y', h1', h2'⟩⟩
    rw [a2 x y y' ⟨h1, h1'⟩] at h2
    exact b2 y' z z' ⟨h2, h2'⟩
  · show sumCls C = codom _
    ext z
    constructor
    · intro hz
      obtain ⟨Y, hY, hzY⟩ := hz
      obtain ⟨y, hy⟩ : z ∈ codom T₂ := bcod' ▸ ⟨Y, hY, hzY⟩
      obtain ⟨x, hx⟩ : y ∈ codom T₁ := acod' ▸ ⟨T₂ ʻʻ Y, hB' ▸ ⟨Y, hY, rfl⟩, z, hzY, hy⟩
      exact ⟨x, y, hx, hy⟩
    · rintro ⟨x, y, -, hy⟩
      rw [bcod']; exact ⟨y, hy⟩
  · show A = imgRel (T₁ ⨾ T₂) ʻʻ C
    rw [hA', hB']
    ext X
    constructor
    · rintro ⟨Y', ⟨Y, hY, hY'⟩, hX⟩
      have e1 : Y' = T₂ ʻʻ Y := hY'
      have e2 : X = T₁ ʻʻ Y' := hX
      subst e1; subst e2
      refine ⟨Y, hY, ?_⟩
      show T₁ ʻʻ (T₂ ʻʻ Y) = (T₁ ⨾ T₂) ʻʻ Y
      ext x
      exact ⟨fun ⟨y, ⟨z, hz, hyz⟩, hxy⟩ => ⟨z, hz, y, hxy, hyz⟩,
        fun ⟨z, hz, y, hxy, hyz⟩ => ⟨y, ⟨z, hz, hyz⟩, hxy⟩⟩
    · rintro ⟨Y, hY, hX⟩
      have e2 : X = (T₁ ⨾ T₂) ʻʻ Y := hX
      subst e2
      refine ⟨T₂ ʻʻ Y, ⟨Y, hY, rfl⟩, ?_⟩
      show (T₁ ⨾ T₂) ʻʻ Y = T₁ ʻʻ (T₂ ʻʻ Y)
      ext x
      exact ⟨fun ⟨z, hz, y, hxy, hyz⟩ => ⟨y, ⟨z, hz, hyz⟩, hxy⟩,
        fun ⟨y, ⟨z, hz, hyz⟩, hxy⟩ => ⟨z, hz, y, hxy, hyz⟩⟩

private theorem pmB2_desc_one_one {X Y : Type*} {R : X → Y → Prop} (h : R ∈ arrow one one) {z : Y}
    (hz : z ∈ codom R) (x : X) : Desc R z (fun a => x = a) ↔ R x z := by
  obtain ⟨h1, -⟩ := mem_arrow_one_one.1 h
  obtain ⟨a, ha⟩ := hz
  show TheIs (fun c => R c z) (fun a => x = a) ↔ _
  rw [TheIs_iff_of_unique (b := a) (fun c => ⟨fun hc => h1 c a z ⟨hc, ha⟩, fun e => e ▸ ha⟩)]
  exact ⟨fun e => e ▸ ha, fun hx => h1 x a z ⟨hx, ha⟩⟩

/-- The hypothesis of ✱116·4, ✱116·41, ✱116·42, unfolded. -/
private structure pmB2_HL {X Y : Type*} (L : Set (X → Y → Prop)) (G : Set Y) : Prop where
  oo : L ⊆ arrow one one
  dj : ∀ R S, (R ∈ L ∧ S ∈ L) ∧ (dom R ∩ dom S).Nonempty → R = S
  cd : ∀ R, R ∈ L → codom R = G

private theorem pmB2_HL_of {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y} (h1 : L ⊆ arrow one one)
    (h2 : ∀ R S, (R ∈ L ∧ S ∈ L) ∧ (dom R ∩ dom S).Nonempty → R = S)
    (h3 : Dcnv ʻʻ L ⊆ ι G) : pmB2_HL L G :=
  ⟨h1, h2, fun R hR => mem_unitCls.1 (h3 ⟨R, hR, rfl⟩)⟩

private theorem pmB2_W_iff {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y} (H : pmB2_HL L G)
    (x : X) (P : (X → Y → Prop) → Y → Prop) :
    (∃ R z, (R ∈ L ∧ Desc R z (fun a => x = a)) ∧ P = R ↓ z) ↔
      ∃ R z, (R ∈ L ∧ R x z) ∧ P = R ↓ z := by
  constructor
  · rintro ⟨R, z, ⟨hR, hd⟩, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hd
    exact ⟨R, z, ⟨hR, (hb x).2 rfl⟩, rfl⟩
  · rintro ⟨R, z, ⟨hR, hx⟩, rfl⟩
    exact ⟨R, z, ⟨hR, (pmB2_desc_one_one (H.oo hR) ⟨x, hx⟩ x).2 hx⟩, rfl⟩

private theorem pmB2_W_props {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y} (H : pmB2_HL L G)
    {W : X → ((X → Y → Prop) → Y → Prop) → Prop}
    (hW : ∀ x P, W x P ↔ ∃ R z, (R ∈ L ∧ R x z) ∧ P = R ↓ z) :
    (W ∈ arrow one one ∧ codom W = G ×ₐ L) ∧ dom W = dom (sumRel L) := by
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro x x' P ⟨h, h'⟩
    obtain ⟨R, z, ⟨hR, hx⟩, rfl⟩ := (hW _ _).1 h
    obtain ⟨R', z', ⟨-, hx'⟩, e⟩ := (hW _ _).1 h'
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    exact (mem_arrow_one_one.1 (H.oo hR)).1 x x' z ⟨hx, hx'⟩
  · intro x P P' ⟨h, h'⟩
    obtain ⟨R, z, ⟨hR, hx⟩, rfl⟩ := (hW _ _).1 h
    obtain ⟨S, w, ⟨hS, hx'⟩, rfl⟩ := (hW _ _).1 h'
    have e : R = S := H.dj R S ⟨⟨hR, hS⟩, x, ⟨z, hx⟩, ⟨w, hx'⟩⟩
    subst e
    rw [(mem_arrow_one_one.1 (H.oo hR)).2 x z w ⟨hx, hx'⟩]
  · ext P
    constructor
    · rintro ⟨x, h⟩
      obtain ⟨R, z, ⟨hR, hx⟩, rfl⟩ := (hW _ _).1 h
      exact couple_mem_clsTimes.2 ⟨hR, H.cd R hR ▸ ⟨x, hx⟩⟩
    · intro hP
      obtain ⟨R, z, ⟨hR, hz⟩, rfl⟩ := pmB2_mem_clsTimes.1 hP
      obtain ⟨x, hx⟩ : z ∈ codom R := (H.cd R hR).symm ▸ hz
      exact ⟨x, (hW _ _).2 ⟨R, z, ⟨hR, hx⟩, rfl⟩⟩
  · ext x
    constructor
    · rintro ⟨P, h⟩
      obtain ⟨R, z, ⟨hR, hx⟩, -⟩ := (hW _ _).1 h
      exact ⟨z, R, hR, hx⟩
    · rintro ⟨z, R, hR, hx⟩
      exact ⟨R ↓ z, (hW _ _).2 ⟨R, z, ⟨hR, hx⟩, rfl⟩⟩

/-- ✱116·4. \[\begin{align}\vdash \colon\ldotp \lambda \subset 1&\rightarrow 1:R,S\in \lambda .\exists !\text{D}ʻR\cap \text{D}ʻS.\supset _{R,S}.R=S:\\ &\text{ᗡ}ʻʻ\lambda \subset \iota ʻ\gamma .W=\hat{x} \hat{P} \{(\exists R,z).R\in \lambda .x=Rʻz.P=R\downarrow z\}:\\ &\supset .W\in 1\rightarrow 1.\text{ᗡ}ʻW=\gamma \times \lambda .\text{D}ʻW=\text{D}ʻ\dot{s} ʻ\lambda\end{align}\]

`ᗡ''λ ⊂ ι'γ` is `Dcnv ʻʻ L ⊆ ι G`; `x = R'z` is a description (`Desc R z (fun a => x = a)`);
`γ × λ` is `G ×ₐ L`; `D'ṡ'λ` is `dom (sumRel L)`. The hypothesis `W = …` is an equation. -/
theorem pm116_4 {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y}
    {W : X → ((X → Y → Prop) → Y → Prop) → Prop} :
    (L ⊆ arrow one one ∧ ∀ R S, (R ∈ L ∧ S ∈ L) ∧ (dom R ∩ dom S).Nonempty → R = S) ∧
        (Dcnv ʻʻ L ⊆ ι G ∧
          W = fun x P => ∃ R z, (R ∈ L ∧ Desc R z (fun a => x = a)) ∧ P = R ↓ z) →
      (W ∈ arrow one one ∧ codom W = G ×ₐ L) ∧ dom W = dom (sumRel L) := by
  rintro ⟨⟨h1, h2⟩, h3, rfl⟩
  have H := pmB2_HL_of h1 h2 h3
  exact pmB2_W_props H (fun x P => pmB2_W_iff H x P)

private theorem pmB2_W_img {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y}
    {W : X → ((X → Y → Prop) → Y → Prop) → Prop}
    (hW : ∀ x P, W x P ↔ ∃ R z, (R ∈ L ∧ R x z) ∧ P = R ↓ z) :
    Rfwd (sumRel L) ʻʻ G = imgRel W ʻʻ (coupleImg L ʻʻ G) := by
  have key : ∀ z, refs (sumRel L) z = W ʻʻ opImg couple L z := by
    intro z
    ext x
    constructor
    · rintro ⟨R, hR, hx⟩
      exact ⟨R ↓ z, ⟨R, hR, rfl⟩, (hW _ _).2 ⟨R, z, ⟨hR, hx⟩, rfl⟩⟩
    · rintro ⟨P, ⟨R, hR, hP⟩, h⟩
      have hP' : P = R ↓ z := hP
      subst hP'
      obtain ⟨R', z', ⟨hR', hx⟩, e⟩ := (hW _ _).1 h
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
      exact ⟨R, hR, hx⟩
  ext Q
  constructor
  · rintro ⟨z, hz, hQ⟩
    exact ⟨opImg couple L z, ⟨z, hz, rfl⟩, (show Q = _ from hQ).trans (key z)⟩
  · rintro ⟨Y', ⟨z, hz, hY⟩, hQ⟩
    have hY' : Y' = opImg couple L z := hY
    subst hY'
    exact ⟨z, hz, (show Q = _ from hQ).trans (key z).symm⟩

/-- ✱116·401. \(\vdash : \text{Hp} *116·4 . T = \dot{s} ʻ\lambda . \supset . \overrightarrow{T}ʻʻ\gamma = W_{\in }ʻʻ\lambda \downarrow_{,,} ʻʻ\gamma\)

"Hp ✱116·4" is the hypothesis of ✱116·4; `T⃗''γ` is `Rfwd T ʻʻ G`; `W_∈''λ↓,,''γ` is
`imgRel W ʻʻ (coupleImg L ʻʻ G)`. -/
theorem pm116_401 {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y}
    {W : X → ((X → Y → Prop) → Y → Prop) → Prop} {T : X → Y → Prop} :
    ((L ⊆ arrow one one ∧ ∀ R S, (R ∈ L ∧ S ∈ L) ∧ (dom R ∩ dom S).Nonempty → R = S) ∧
        (Dcnv ʻʻ L ⊆ ι G ∧
          W = fun x P => ∃ R z, (R ∈ L ∧ Desc R z (fun a => x = a)) ∧ P = R ↓ z)) ∧
        T = sumRel L →
      Rfwd T ʻʻ G = imgRel W ʻʻ (coupleImg L ʻʻ G) := by
  rintro ⟨⟨⟨h1, h2⟩, h3, rfl⟩, rfl⟩
  have H := pmB2_HL_of h1 h2 h3
  exact pmB2_W_img (fun x P => pmB2_W_iff H x P)

private theorem pmB2_sel_rfwd {X Y : Type*} {T : X → Y → Prop} (hT : T ∈ arrow Cls one) (G : Set Y) :
    sm (sel memRel (Rfwd T ʻʻ G)) (sel T G) := by
  by_cases h0 : ∃ z, z ∈ G ∧ refs T z = ∅
  · obtain ⟨z, hz, h⟩ := h0
    refine pmB2_sm_empty (pmB2_sel_empty_of ⟨z, hz, h.symm⟩) ?_
    ext R
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hR
    obtain ⟨x, hx⟩ := pmB2_sel_ex hR hz
    have : x ∈ refs T z := (pmB2_mem_sel.1 hR).2.1 x z hx
    rw [h] at this; exact this
  · push Not at h0
    have hinj : Set.InjOn (refs T) G := by
      intro z hz w _ e
      obtain ⟨x, hx⟩ := h0 z hz
      have hx' : x ∈ refs T w := e ▸ hx
      exact (mem_arrow_Cls_one.1 hT) x z w ⟨hx, hx'⟩
    rw [show Rfwd T ʻʻ G = refs T '' G from pmB2_img_graph (refs T) G]
    exact pmB2_sm_of_equiv ((pmB2_selE _).trans ((pmB2_piImage (refs T) G hinj
      (fun Y => ↥(Y : Set X))).trans (pmB2_selEquiv T G).symm))

private theorem pmB2_core41 {X Y Tt : Type*} {L : Set (X → Y → Prop)} {G : Set Y} (H : pmB2_HL L G) :
    (((smsm (Rfwd (sumRel L) ʻʻ G) (coupleImg L ʻʻ G) ∧ sm (sumRel L ʻʻ G) (G ×ₐ L)) ∧
        sumRel L ∈ arrow Cls one) ∧ Rfwd (sumRel L) ʻʻ G ∈ Cls2excl) ∧
      (((nc Tt (sel memRel (Rfwd (sumRel L) ʻʻ G)) = nc Tt (sel (sumRel L) G) ∧
          nc Tt (sel (sumRel L) G) = nc Tt (prodK (Rfwd (sumRel L) ʻʻ G))) ∧
          nc Tt (prodK (Rfwd (sumRel L) ʻʻ G)) = nc Tt (clsExp L G)) ∧
        nc Tt (clsExp L G) = (n₀c L ^ᶜ n₀c G : Set (Set Tt))) := by
  let W : X → ((X → Y → Prop) → Y → Prop) → Prop :=
    fun x P => ∃ R z, (R ∈ L ∧ R x z) ∧ P = R ↓ z
  have hW : ∀ x P, W x P ↔ ∃ R z, (R ∈ L ∧ R x z) ∧ P = R ↓ z := fun _ _ => Iff.rfl
  obtain ⟨⟨w11, wcod⟩, wdom⟩ := pmB2_W_props H hW
  have hTG : sumRel L ʻʻ G = dom (sumRel L) := by
    ext x
    constructor
    · rintro ⟨z, -, h⟩; exact ⟨z, h⟩
    · rintro ⟨z, R, hR, hx⟩; exact ⟨z, H.cd R hR ▸ ⟨x, hx⟩, R, hR, hx⟩
  have hsmsm : smsm (Rfwd (sumRel L) ʻʻ G) (coupleImg L ʻʻ G) :=
    ⟨W, ⟨⟨w11, wcod.symm⟩, pmB2_W_img hW⟩⟩
  have hT1 : sumRel L ∈ arrow Cls one := by
    refine mem_arrow_Cls_one.2 fun x z w ⟨⟨R, hR, hx⟩, ⟨S, hS, hx'⟩⟩ => ?_
    have e : R = S := H.dj R S ⟨⟨hR, hS⟩, x, ⟨z, hx⟩, ⟨w, hx'⟩⟩
    subst e
    exact (mem_arrow_one_one.1 (H.oo hR)).2 x z w ⟨hx, hx'⟩
  have hex : Rfwd (sumRel L) ʻʻ G ∈ Cls2excl := by
    refine pmB2_excl_iff.2 ?_
    rintro Q Q' x ⟨z, -, hQ⟩ ⟨w, -, hQ'⟩ hx hx'
    have e1 : Q = refs (sumRel L) z := hQ
    have e2 : Q' = refs (sumRel L) w := hQ'
    subst e1; subst e2
    rw [(mem_arrow_Cls_one.1 hT1) x z w ⟨hx, hx'⟩]
  have s1 := pmB2_sel_rfwd hT1 G
  have s2 : sm (prodK (Rfwd (sumRel L) ʻʻ G)) (clsExp L G) := pmB2_smsm_sm (pm115_51 hsmsm)
  have s3 : sm (prodK (Rfwd (sumRel L) ʻʻ G)) (sel memRel (Rfwd (sumRel L) ʻʻ G)) :=
    pmB2_sm_of_equiv (pmB2_prodEquiv hex)
  refine ⟨⟨⟨⟨hsmsm, ?_⟩, hT1⟩, hex⟩, ⟨⟨⟨nc_eq_nc_of_sm s1, nc_eq_nc_of_sm
    (sm_trans (sm_symm s1) (sm_symm s3))⟩, nc_eq_nc_of_sm s2⟩, (pmB2_n₀c_exp L G).symm⟩⟩
  rw [hTG, ← wdom]
  exact sm_iff.2 ⟨W, ⟨w11, rfl⟩, wcod.symm⟩

/-- ✱116·41. \[\begin{align}&\vdash \colon\ldotp \lambda \subset 1 \rightarrow 1 . \text{ᗡ}ʻʻ\lambda \subset \iota ʻ\gamma : R, S \in \lambda . \exists ! \text{D}ʻR \cap \text{D}ʻS . \supset _{R, S} . R = S : T = \dot{s} ʻ\lambda :\\ &\supset . \overrightarrow{T}ʻʻ\gamma \text{ sm } \text{ sm } \lambda \downarrow_{,,} ʻʻ\gamma . Tʻʻ\gamma \text{ sm } \gamma \times \lambda . T \in \text{Cls} \rightarrow 1 . \overrightarrow{T}ʻʻ\gamma \in \text{Cls}^{2} \text{excl} .\\ &\text{Nc}ʻ{\in}_{\Delta}ʻ\overrightarrow{T}ʻʻ\gamma = \text{Nc}ʻT_{\Delta }ʻ\gamma = \text{Nc}ʻ\text{Prod}ʻ\overrightarrow{T}ʻʻ\gamma = \text{Nc}ʻ(\lambda \,\,\text{exp}\,\, \gamma ) = (\text{Nc}ʻ\lambda )^{\text{Nc}ʻ\gamma }\end{align}\]

`T''γ` is `T ʻʻ G`; `T_Δ'γ` is `sel T G`; the arithmetical occurrences `Nc'λ`, `Nc'γ` are
`N₀c'λ`, `N₀c'γ` (✱116·03·04); the chain of identities (one type `Tt`) is the conjunction of its
links. -/
theorem pm116_41 {X Y Tt : Type*} {L : Set (X → Y → Prop)} {G : Set Y} {T : X → Y → Prop} :
    ((L ⊆ arrow one one ∧ Dcnv ʻʻ L ⊆ ι G) ∧
        (∀ R S, (R ∈ L ∧ S ∈ L) ∧ (dom R ∩ dom S).Nonempty → R = S)) ∧ T = sumRel L →
      (((smsm (Rfwd T ʻʻ G) (coupleImg L ʻʻ G) ∧ sm (T ʻʻ G) (G ×ₐ L)) ∧
          T ∈ arrow Cls one) ∧ Rfwd T ʻʻ G ∈ Cls2excl) ∧
        (((nc Tt (sel memRel (Rfwd T ʻʻ G)) = nc Tt (sel T G) ∧
            nc Tt (sel T G) = nc Tt (prodK (Rfwd T ʻʻ G))) ∧
            nc Tt (prodK (Rfwd T ʻʻ G)) = nc Tt (clsExp L G)) ∧
          nc Tt (clsExp L G) = (n₀c L ^ᶜ n₀c G : Set (Set Tt))) := by
  rintro ⟨⟨⟨h1, h3⟩, h2⟩, rfl⟩
  exact pmB2_core41 (pmB2_HL_of h1 h2 h3)

/-- A correlation of `λ` with `κ` gives `λ↓,,''γ sm sm κ↓,,''γ`. -/
private theorem pmB2_smsm_coupleImg {α β Y : Type*} {L : Set α} {K : Set β} {Φ : α → β → Prop}
    (hΦ : Φ ∈ smbar L K) (G : Set Y) : smsm (coupleImg L ʻʻ G) (coupleImg K ʻʻ G) := by
  obtain ⟨⟨h11, hL⟩, hK⟩ := hΦ
  have hL' : L = dom Φ := hL
  have hK' : K = codom Φ := hK
  obtain ⟨p1, p2⟩ := mem_arrow_one_one.1 h11
  refine ⟨fun P Q => ∃ R A z, (Φ R A ∧ z ∈ G) ∧ P = R ↓ z ∧ Q = A ↓ z,
    ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
  · rintro P P' Q ⟨⟨R, A, z, ⟨h, -⟩, rfl, rfl⟩, ⟨R', A', z', ⟨h', -⟩, rfl, e⟩⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    rw [p1 R R' A ⟨h, h'⟩]
  · rintro P Q Q' ⟨⟨R, A, z, ⟨h, -⟩, rfl, rfl⟩, ⟨R', A', z', ⟨h', -⟩, e, rfl⟩⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    rw [p2 R A A' ⟨h, h'⟩]
  · show G ×ₐ K = codom _
    ext Q
    constructor
    · intro hQ
      obtain ⟨A, z, ⟨hA, hz⟩, rfl⟩ := pmB2_mem_clsTimes.1 hQ
      obtain ⟨R, hR⟩ : A ∈ codom Φ := hK' ▸ hA
      exact ⟨R ↓ z, R, A, z, ⟨hR, hz⟩, rfl, rfl⟩
    · rintro ⟨P, R, A, z, ⟨hR, hz⟩, -, rfl⟩
      exact couple_mem_clsTimes.2 ⟨hK' ▸ ⟨R, hR⟩, hz⟩
  · ext S
    constructor
    · rintro ⟨z, hz, hS⟩
      have hS' : S = opImg couple L z := hS
      subst hS'
      refine ⟨opImg couple K z, ⟨z, hz, rfl⟩, ?_⟩
      show opImg couple L z = _
      ext P
      constructor
      · rintro ⟨R, hR, hP⟩
        have hP' : P = R ↓ z := hP
        subst hP'
        obtain ⟨A, hA⟩ : R ∈ dom Φ := hL' ▸ hR
        exact ⟨A ↓ z, ⟨A, hK' ▸ ⟨R, hA⟩, rfl⟩, R, A, z, ⟨hA, hz⟩, rfl, rfl⟩
      · rintro ⟨Q, hQ, R, A, z', ⟨hRA, -⟩, rfl, rfl⟩
        obtain ⟨A', -, hQ'⟩ := hQ
        have e : A ↓ z' = A' ↓ z := hQ'
        obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
        exact ⟨R, hL' ▸ ⟨_, hRA⟩, rfl⟩
    · rintro ⟨Q', ⟨z, hz, hQ'⟩, hS⟩
      have e1 : Q' = opImg couple K z := hQ'
      subst e1
      refine ⟨z, hz, (show S = _ from hS).trans ?_⟩
      ext P
      constructor
      · rintro ⟨Q, ⟨A, hA, hQ⟩, R, A', z', ⟨hRA, -⟩, rfl, e⟩
        have hQ'' : Q = A ↓ z := hQ
        rw [hQ''] at e
        obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
        exact ⟨R, hL' ▸ ⟨_, hRA⟩, rfl⟩
      · rintro ⟨R, hR, hP⟩
        have hP' : P = R ↓ z := hP
        subst hP'
        obtain ⟨A, hA⟩ : R ∈ dom Φ := hL' ▸ hR
        exact ⟨A ↓ z, ⟨A, hK' ▸ ⟨R, hA⟩, rfl⟩, R, A, z, ⟨hA, hz⟩, rfl, rfl⟩

/-- ✱116·411. \[\begin{align}&\vdash \colon\ldotp \kappa \in \text{Cls}^{2} \text{excl} : \alpha \in \kappa . \supset _{\alpha } . Mʻ\alpha \in \alpha \,\overline{\text{ sm }}\, \gamma : T = \dot{s} ʻMʻʻ\kappa ʻʻ: \supset .\\ &\overrightarrow{T}ʻʻ\gamma \text{ sm } \text{ sm } \kappa \downarrow_{,,} ʻʻ\gamma . Tʻʻ\gamma \text{ sm } \gamma \times \kappa . T \in \text{Cls} \rightarrow 1 . \overrightarrow{T}ʻʻ\gamma \in \text{Cls}^{2} \text{excl} .\\ &\text{Nc}ʻ{\in}_{\Delta}ʻ\overrightarrow{T}ʻʻ\gamma = \text{Nc}ʻT_{\Delta }ʻ\gamma = \text{Nc}ʻ\text{Prod}ʻ\overrightarrow{T}ʻʻ\gamma = \text{Nc}ʻ(\kappa \,\,\text{exp}\,\, \gamma ) = (\text{Nc}ʻ\kappa )^{\text{Nc}ʻ\gamma }\end{align}\]

`M'α ∈ α sm̄ γ` is `Desc M A (fun R => R ∈ smbar A G)`; the e-text prints `T = ṡ'M''κ''` with a
stray `''`: `T = ṡ'M''κ` (the proof uses `M''κ` for `λ` in ✱116·41).

**Status.** proved (reading): transcription error: `ṡ'M''κ''` is read `ṡ'M''κ`. -/
theorem pm116_411 {X Y Tt : Type*} {K : Set (Set X)} {G : Set Y}
    {M : (X → Y → Prop) → Set X → Prop} {T : X → Y → Prop} :
    (K ∈ Cls2excl ∧ ∀ A, A ∈ K → Desc M A (fun R => R ∈ smbar A G)) ∧ T = sumRel (M ʻʻ K) →
      (((smsm (Rfwd T ʻʻ G) (coupleImg K ʻʻ G) ∧ sm (T ʻʻ G) (G ×ₐ K)) ∧
          T ∈ arrow Cls one) ∧ Rfwd T ʻʻ G ∈ Cls2excl) ∧
        (((nc Tt (sel memRel (Rfwd T ʻʻ G)) = nc Tt (sel T G) ∧
            nc Tt (sel T G) = nc Tt (prodK (Rfwd T ʻʻ G))) ∧
            nc Tt (prodK (Rfwd T ʻʻ G)) = nc Tt (clsExp K G)) ∧
          nc Tt (clsExp K G) = (n₀c K ^ᶜ n₀c G : Set (Set Tt))) := by
  rintro ⟨⟨hK, hM⟩, rfl⟩
  have uniq : ∀ A, A ∈ K → ∀ R, M R A → R ∈ smbar A G := by
    intro A hA R hR
    obtain ⟨b, hb, hb'⟩ := hM A hA
    rw [(hb R).1 hR]; exact hb'
  have uniq2 : ∀ A, A ∈ K → ∀ R S, M R A → M S A → R = S := by
    intro A hA R S hR hS
    obtain ⟨b, hb, -⟩ := hM A hA
    exact ((hb R).1 hR).trans ((hb S).1 hS).symm
  have domA : ∀ A R, A ∈ K → M R A → dom R = A := fun A R hA hR =>
    ((uniq A hA R hR).1.2 : A = dom R).symm
  have H : pmB2_HL (M ʻʻ K) G := by
    refine ⟨?_, ?_, ?_⟩
    · rintro R ⟨A, hA, hR⟩; exact (uniq A hA R hR).1.1
    · rintro R S ⟨⟨⟨A, hA, hR⟩, ⟨B, hB, hS⟩⟩, hne⟩
      rw [domA A R hA hR, domA B S hB hS] at hne
      have e : A = B := pmB2_excl_iff'.1 hK A B ⟨⟨hA, hB⟩, hne⟩
      subst e
      exact uniq2 A hA R S hR hS
    · rintro R ⟨A, hA, hR⟩
      exact ((uniq A hA R hR).2 : G = codom R).symm
  have hΦ : (fun R A => A ∈ K ∧ M R A) ∈ smbar (M ʻʻ K) K := by
    refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rintro R S A ⟨⟨hA, hR⟩, ⟨-, hS⟩⟩; exact uniq2 A hA R S hR hS
    · rintro R A B ⟨⟨hA, hR⟩, ⟨hB, hR'⟩⟩; rw [← domA A R hA hR, ← domA B R hB hR']
    · show M ʻʻ K = dom _
      ext R
      exact ⟨fun ⟨A, hA, hR⟩ => ⟨A, hA, hR⟩, fun ⟨A, hA, hR⟩ => ⟨A, hA, hR⟩⟩
    · show K = codom _
      ext A
      constructor
      · intro hA
        obtain ⟨b, hb, -⟩ := hM A hA
        exact ⟨b, hA, (hb b).2 rfl⟩
      · rintro ⟨R, hA, -⟩; exact hA
  have hsm : sm (M ʻʻ K) K := ⟨_, hΦ⟩
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, ⟨⟨⟨c5, c6⟩, c7⟩, -⟩⟩ := pmB2_core41 (Tt := Tt) H
  have e8 : nc Tt (clsExp (M ʻʻ K) G) = nc Tt (clsExp K G) :=
    nc_eq_nc_of_sm (pmB2_sm_clsExp hsm (sm_refl G))
  refine ⟨⟨⟨⟨pmB2_smsm_trans c1 (pmB2_smsm_coupleImg hΦ G), sm_trans c2 ?_⟩, c3⟩, c4⟩,
    ⟨⟨⟨c5, c6⟩, c7.trans e8⟩, (pmB2_n₀c_exp K G).symm⟩⟩
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hsm
  exact pmB2_sm_of_equiv ((pmB2_clsTimesEquiv _ _).trans ((e.prodCongr (Equiv.refl _)).trans
    (pmB2_clsTimesEquiv _ _).symm))

private theorem pmB2_U_iff {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y} (H : pmB2_HL L G)
    (x : X) (P : Y → (X → Y → Prop) → Prop) :
    (∃ R z, (R ∈ L ∧ Desc R z (fun a => x = a)) ∧ P = z ↓ R) ↔
      ∃ R z, (R ∈ L ∧ R x z) ∧ P = z ↓ R := by
  constructor
  · rintro ⟨R, z, ⟨hR, hd⟩, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hd
    exact ⟨R, z, ⟨hR, (hb x).2 rfl⟩, rfl⟩
  · rintro ⟨R, z, ⟨hR, hx⟩, rfl⟩
    exact ⟨R, z, ⟨hR, (pmB2_desc_one_one (H.oo hR) ⟨x, hx⟩ x).2 hx⟩, rfl⟩

private theorem pmB2_U_props {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y} (H : pmB2_HL L G)
    {U : X → (Y → (X → Y → Prop) → Prop) → Prop}
    (hU : ∀ x P, U x P ↔ ∃ R z, (R ∈ L ∧ R x z) ∧ P = z ↓ R) :
    U ∈ smbar (sumCls (D ʻʻ L)) (L ×ₐ G) ∧ D ʻʻ L = imgRel U ʻʻ (coupleImg G ʻʻ L) := by
  refine ⟨⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro x x' P ⟨h, h'⟩
    obtain ⟨R, z, ⟨hR, hx⟩, rfl⟩ := (hU _ _).1 h
    obtain ⟨R', z', ⟨-, hx'⟩, e⟩ := (hU _ _).1 h'
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    exact (mem_arrow_one_one.1 (H.oo hR)).1 x x' z ⟨hx, hx'⟩
  · intro x P P' ⟨h, h'⟩
    obtain ⟨R, z, ⟨hR, hx⟩, rfl⟩ := (hU _ _).1 h
    obtain ⟨S, w, ⟨hS, hx'⟩, rfl⟩ := (hU _ _).1 h'
    have e : R = S := H.dj R S ⟨⟨hR, hS⟩, x, ⟨z, hx⟩, ⟨w, hx'⟩⟩
    subst e
    rw [(mem_arrow_one_one.1 (H.oo hR)).2 x z w ⟨hx, hx'⟩]
  · show sumCls (D ʻʻ L) = dom U
    ext x
    constructor
    · rintro ⟨Q, ⟨R, hR, hQ⟩, hxQ⟩
      have hQ' : Q = dom R := hQ
      rw [hQ'] at hxQ
      obtain ⟨z, hx⟩ := hxQ
      exact ⟨z ↓ R, (hU _ _).2 ⟨R, z, ⟨hR, hx⟩, rfl⟩⟩
    · rintro ⟨P, h⟩
      obtain ⟨R, z, ⟨hR, hx⟩, -⟩ := (hU _ _).1 h
      exact ⟨dom R, ⟨R, hR, rfl⟩, z, hx⟩
  · show L ×ₐ G = codom U
    ext P
    constructor
    · intro hP
      obtain ⟨z, R, ⟨hz, hR⟩, rfl⟩ := pmB2_mem_clsTimes.1 hP
      obtain ⟨x, hx⟩ : z ∈ codom R := (H.cd R hR).symm ▸ hz
      exact ⟨x, (hU _ _).2 ⟨R, z, ⟨hR, hx⟩, rfl⟩⟩
    · rintro ⟨x, h⟩
      obtain ⟨R, z, ⟨hR, hx⟩, rfl⟩ := (hU _ _).1 h
      exact couple_mem_clsTimes.2 ⟨H.cd R hR ▸ ⟨x, hx⟩, hR⟩
  · ext Q
    constructor
    · rintro ⟨R, hR, hQ⟩
      have hQ' : Q = dom R := hQ
      refine ⟨opImg couple G R, ⟨R, hR, rfl⟩, (show Q = _ from hQ'.trans ?_)⟩
      ext x
      constructor
      · rintro ⟨z, hx⟩
        exact ⟨z ↓ R, ⟨z, H.cd R hR ▸ ⟨x, hx⟩, rfl⟩, (hU _ _).2 ⟨R, z, ⟨hR, hx⟩, rfl⟩⟩
      · rintro ⟨P, ⟨z, -, hP⟩, h⟩
        have hP' : P = z ↓ R := hP
        subst hP'
        obtain ⟨R', z', ⟨-, hx⟩, e⟩ := (hU _ _).1 h
        obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
        exact ⟨z, hx⟩
    · rintro ⟨Y', ⟨R, hR, hY⟩, hQ⟩
      have hY' : Y' = opImg couple G R := hY
      subst hY'
      refine ⟨R, hR, (show Q = _ from hQ).trans ?_⟩
      show U ʻʻ opImg couple G R = dom R
      ext x
      constructor
      · rintro ⟨P, ⟨z, -, hP⟩, h⟩
        have hP' : P = z ↓ R := hP
        subst hP'
        obtain ⟨R', z', ⟨-, hx⟩, e⟩ := (hU _ _).1 h
        obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
        exact ⟨z, hx⟩
      · rintro ⟨z, hx⟩
        exact ⟨z ↓ R, ⟨z, H.cd R hR ▸ ⟨x, hx⟩, rfl⟩, (hU _ _).2 ⟨R, z, ⟨hR, hx⟩, rfl⟩⟩

/-- ✱116·412. \[\begin{align}&\vdash \colon\ldotp \lambda \subset 1 \rightarrow 1 : R, S \in \lambda . \exists ! \text{D}ʻR \cap \text{D}ʻS . \supset _{R, S} . R = S : \text{ᗡ}ʻʻ\lambda \subset \iota ʻ\gamma :\\ &U = \hat{x} \hat{P}\{(\exists R, z) . R \in \lambda . x = Rʻz . P = z \downarrow R\} :\\ &\supset . U \in (sʻ\text{D}ʻʻ\lambda ) \,\overline{\text{ sm }}\, (\lambda \times \gamma ) \quad[\text{Proof as in *116·4}]\end{align}\]

`U` relates `x` to `z ↓ R` (couples in the order of PM's `z ↓ R`); `s'D''λ` is
`sumCls (D ʻʻ L)`; `λ × γ` is `L ×ₐ G`. -/
theorem pm116_412 {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y}
    {U : X → (Y → (X → Y → Prop) → Prop) → Prop} :
    ((L ⊆ arrow one one ∧ ∀ R S, (R ∈ L ∧ S ∈ L) ∧ (dom R ∩ dom S).Nonempty → R = S) ∧
        Dcnv ʻʻ L ⊆ ι G) ∧
        U = (fun x P => ∃ R z, (R ∈ L ∧ Desc R z (fun a => x = a)) ∧ P = z ↓ R) →
      U ∈ smbar (sumCls (D ʻʻ L)) (L ×ₐ G) := by
  rintro ⟨⟨⟨h1, h2⟩, h3⟩, rfl⟩
  have H := pmB2_HL_of h1 h2 h3
  exact (pmB2_U_props H (fun x P => pmB2_U_iff H x P)).1

/-- ✱116·413. \(\vdash : \text{Hp} *116·412 . \supset . \text{D}ʻʻ\lambda = U_{\in}ʻʻ\gamma \downarrow_{,,}ʻʻ\lambda \quad[\text{Proof as in *116·401}]\)

`γ↓,,''λ` is `coupleImg G ʻʻ L`. -/
theorem pm116_413 {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y}
    {U : X → (Y → (X → Y → Prop) → Prop) → Prop} :
    ((L ⊆ arrow one one ∧ ∀ R S, (R ∈ L ∧ S ∈ L) ∧ (dom R ∩ dom S).Nonempty → R = S) ∧
        Dcnv ʻʻ L ⊆ ι G) ∧
        U = (fun x P => ∃ R z, (R ∈ L ∧ Desc R z (fun a => x = a)) ∧ P = z ↓ R) →
      D ʻʻ L = imgRel U ʻʻ (coupleImg G ʻʻ L) := by
  rintro ⟨⟨⟨h1, h2⟩, h3⟩, rfl⟩
  have H := pmB2_HL_of h1 h2 h3
  exact (pmB2_U_props H (fun x P => pmB2_U_iff H x P)).2

/-- ✱116·414. \[\begin{align}&\vdash : \text{Hp} *116·412 . \supset . U \in (\text{D}ʻʻ\lambda ) \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, (\gamma \downarrow_{,,}ʻʻ\lambda ) . (\text{D}ʻʻ\lambda ) \text{ sm } \text{ sm } (\gamma \downarrow_{,,}ʻʻ\lambda )\\ &[*116·412·413]\end{align}\] -/
theorem pm116_414 {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y}
    {U : X → (Y → (X → Y → Prop) → Prop) → Prop} :
    ((L ⊆ arrow one one ∧ ∀ R S, (R ∈ L ∧ S ∈ L) ∧ (dom R ∩ dom S).Nonempty → R = S) ∧
        Dcnv ʻʻ L ⊆ ι G) ∧
        U = (fun x P => ∃ R z, (R ∈ L ∧ Desc R z (fun a => x = a)) ∧ P = z ↓ R) →
      U ∈ smsmbar (D ʻʻ L) (coupleImg G ʻʻ L) ∧ smsm (D ʻʻ L) (coupleImg G ʻʻ L) := by
  intro h
  have h412 := pm116_412 h
  have h413 := pm116_413 h
  have hU : U ∈ smsmbar (D ʻʻ L) (coupleImg G ʻʻ L) :=
    ⟨⟨h412.1.1, h412.2⟩, h413⟩
  exact ⟨hU, ⟨U, hU⟩⟩

private theorem pmB2_core42 {X Y : Type*} {L : Set (X → Y → Prop)} {G : Set Y} (H : pmB2_HL L G) :
    smsm (D ʻʻ L) (coupleImg G ʻʻ L) ∧ sm (dom (sumRel L)) (L ×ₐ G) ∧
      sm (sel memRel (D ʻʻ L)) (clsExp G L) ∧ D ʻʻ L ∈ Cls2excl := by
  let U : X → (Y → (X → Y → Prop) → Prop) → Prop :=
    fun x P => ∃ R z, (R ∈ L ∧ R x z) ∧ P = z ↓ R
  obtain ⟨hU1, hU2⟩ := pmB2_U_props H (U := U) (fun _ _ => Iff.rfl)
  have hsmsm : smsm (D ʻʻ L) (coupleImg G ʻʻ L) := ⟨U, ⟨⟨hU1.1.1, hU1.2⟩, hU2⟩⟩
  have hdom : dom (sumRel L) = sumCls (D ʻʻ L) := by
    ext x
    constructor
    · rintro ⟨z, R, hR, hx⟩; exact ⟨dom R, ⟨R, hR, rfl⟩, z, hx⟩
    · rintro ⟨Q, ⟨R, hR, hQ⟩, hxQ⟩
      have hQ' : Q = dom R := hQ
      rw [hQ'] at hxQ
      obtain ⟨z, hx⟩ := hxQ
      exact ⟨z, R, hR, hx⟩
  have hex : D ʻʻ L ∈ Cls2excl := by
    refine pmB2_excl_iff.2 ?_
    rintro Q Q' x ⟨R, hR, hQ⟩ ⟨S, hS, hQ'⟩ hx hx'
    have e1 : Q = dom R := hQ
    have e2 : Q' = dom S := hQ'
    subst e1; subst e2
    rw [H.dj R S ⟨⟨hR, hS⟩, x, hx, hx'⟩]
  refine ⟨hsmsm, ?_, sm_trans (sm_symm (pmB2_sm_of_equiv (pmB2_prodEquiv hex)))
    (pmB2_smsm_sm (pm115_51 hsmsm)), hex⟩
  rw [hdom]; exact ⟨U, hU1⟩

/-- ✱116·42. \[\begin{align}&\vdash \colon\ldotp \lambda \subset 1 \rightarrow 1 : R, S \in \lambda . \exists ! \text{D}ʻR \cap \text{D}ʻS . \supset _{R,S} . R = S : \text{ᗡ}ʻʻ\lambda \subset \iota ʻ\gamma :\\ &\supset . \text{D}ʻʻ\lambda \text{ sm } \text{ sm } (\gamma \downarrow_{,,}ʻʻ\lambda ) . (\text{D}ʻ\dot{s} ʻ\lambda ) \text{ sm } (\lambda \times \gamma ) . ({\in}_{\Delta}ʻ\text{D}ʻʻ\lambda ) \text{ sm } (\gamma \,\,\text{exp}\,\, \lambda ) .\\ &\text{Nc}ʻ\text{Prod}ʻ\text{D}ʻʻ\lambda = \Pi \text{Nc}ʻ\text{D}ʻʻ\lambda = (\text{Nc}ʻ\gamma )^{\text{Nc}ʻ\lambda }\\ &[*116·414·25 . *115·51 . *111·44 . *41·43]\end{align}\]

`D'ṡ'λ` is `dom (sumRel L)`; `(Nc'γ)^{Nc'λ}` has its arguments normally adjusted (✱116·03·04);
the chain (one type `T`) is the conjunction of its links. -/
theorem pm116_42 {X Y T : Type*} {L : Set (X → Y → Prop)} {G : Set Y} :
    (L ⊆ arrow one one ∧ ∀ R S, (R ∈ L ∧ S ∈ L) ∧ (dom R ∩ dom S).Nonempty → R = S) ∧
        Dcnv ʻʻ L ⊆ ι G →
      ((smsm (D ʻʻ L) (coupleImg G ʻʻ L) ∧ sm (dom (sumRel L)) (L ×ₐ G)) ∧
          sm (sel memRel (D ʻʻ L)) (clsExp G L)) ∧
        (nc T (prodK (D ʻʻ L)) = piNc T (D ʻʻ L) ∧
          piNc T (D ʻʻ L) = (n₀c G ^ᶜ n₀c L : Set (Set T))) := by
  rintro ⟨⟨h1, h2⟩, h3⟩
  obtain ⟨c1, c2, c3, hex⟩ := pmB2_core42 (pmB2_HL_of h1 h2 h3)
  exact ⟨⟨⟨c1, c2⟩, c3⟩, nc_eq_nc_of_sm (pmB2_sm_of_equiv (pmB2_prodEquiv hex)),
    (nc_eq_nc_of_sm c3).trans (pmB2_n₀c_exp G L).symm⟩

/-- A correlation of `λ` with `κ` gives `γ↓,,''λ sm sm γ↓,,''κ`. -/
private theorem pmB2_smsm_coupleImg' {α β Y : Type*} {L : Set α} {K : Set β} {Φ : α → β → Prop}
    (hΦ : Φ ∈ smbar L K) (G : Set Y) : smsm (coupleImg G ʻʻ L) (coupleImg G ʻʻ K) := by
  obtain ⟨⟨h11, hL⟩, hK⟩ := hΦ
  have hL' : L = dom Φ := hL
  have hK' : K = codom Φ := hK
  obtain ⟨p1, p2⟩ := mem_arrow_one_one.1 h11
  refine ⟨fun P Q => ∃ R A z, (Φ R A ∧ z ∈ G) ∧ P = z ↓ R ∧ Q = z ↓ A,
    ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
  · rintro P P' Q ⟨⟨R, A, z, ⟨h, -⟩, rfl, rfl⟩, ⟨R', A', z', ⟨h', -⟩, rfl, e⟩⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    rw [p1 R R' A ⟨h, h'⟩]
  · rintro P Q Q' ⟨⟨R, A, z, ⟨h, -⟩, rfl, rfl⟩, ⟨R', A', z', ⟨h', -⟩, e, rfl⟩⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    rw [p2 R A A' ⟨h, h'⟩]
  · show K ×ₐ G = codom _
    ext Q
    constructor
    · intro hQ
      obtain ⟨z, A, ⟨hz, hA⟩, rfl⟩ := pmB2_mem_clsTimes.1 hQ
      obtain ⟨R, hR⟩ : A ∈ codom Φ := hK' ▸ hA
      exact ⟨z ↓ R, R, A, z, ⟨hR, hz⟩, rfl, rfl⟩
    · rintro ⟨P, R, A, z, ⟨hR, hz⟩, -, rfl⟩
      exact couple_mem_clsTimes.2 ⟨hz, hK' ▸ ⟨R, hR⟩⟩
  · ext S
    constructor
    · rintro ⟨R, hR, hS⟩
      have hS' : S = opImg couple G R := hS
      subst hS'
      obtain ⟨A, hA⟩ : R ∈ dom Φ := hL' ▸ hR
      refine ⟨opImg couple G A, ⟨A, hK' ▸ ⟨R, hA⟩, rfl⟩, ?_⟩
      show opImg couple G R = _
      ext P
      constructor
      · rintro ⟨z, hz, hP⟩
        have hP' : P = z ↓ R := hP
        subst hP'
        exact ⟨z ↓ A, ⟨z, hz, rfl⟩, R, A, z, ⟨hA, hz⟩, rfl, rfl⟩
      · rintro ⟨Q, hQ, R', A', z', ⟨hRA, hz'⟩, rfl, rfl⟩
        obtain ⟨z'', -, hQ'⟩ := hQ
        have e : z' ↓ A' = z'' ↓ A := hQ'
        obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
        rw [p1 R' R A' ⟨hRA, hA⟩]
        exact ⟨z', hz', rfl⟩
    · rintro ⟨Q', ⟨A, hA, hQ'⟩, hS⟩
      have e1 : Q' = opImg couple G A := hQ'
      subst e1
      obtain ⟨R, hR⟩ : A ∈ codom Φ := hK' ▸ hA
      refine ⟨R, hL' ▸ ⟨A, hR⟩, (show S = _ from hS).trans ?_⟩
      ext P
      constructor
      · rintro ⟨Q, ⟨z, hz, hQ⟩, R', A', z', ⟨hRA, -⟩, rfl, e⟩
        have hQ'' : Q = z ↓ A := hQ
        rw [hQ''] at e
        obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
        rw [p1 R' R _ ⟨hRA, hR⟩]
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, hP⟩
        have hP' : P = z ↓ R := hP
        subst hP'
        exact ⟨z ↓ A, ⟨z, hz, rfl⟩, R, A, z, ⟨hR, hz⟩, rfl, rfl⟩

private theorem pmB2_core422 {X Y Vt : Type*} {N : (X → Y → Prop) → Vt → Prop} {δ : Set Vt} {G : Set Y}
    (hex : ∀ w, w ∈ δ → ∃ R, N R w) (huniq : ∀ w R S, w ∈ δ → N R w → N S w → R = S)
    (hoo : ∀ w R, w ∈ δ → N R w → R ∈ arrow one one ∧ codom R = G)
    (hinj : ∀ w v R, w ∈ δ → v ∈ δ → N R w → N R v → w = v)
    (hdj : ∀ w v R S, w ∈ δ → v ∈ δ → N R w → N S v → (dom R ∩ dom S).Nonempty → w = v) :
    smsm (D ʻʻ (N ʻʻ δ)) (coupleImg G ʻʻ δ) ∧ D ʻʻ (N ʻʻ δ) ∈ Cls2excl := by
  have H : pmB2_HL (N ʻʻ δ) G := by
    refine ⟨fun R ⟨w, hw, hR⟩ => (hoo w R hw hR).1, ?_, fun R ⟨w, hw, hR⟩ => (hoo w R hw hR).2⟩
    rintro R S ⟨⟨⟨w, hw, hR⟩, ⟨v, hv, hS⟩⟩, hne⟩
    have e := hdj w v R S hw hv hR hS hne
    subst e
    exact huniq w R S hw hR hS
  have hΦ : (fun R w => w ∈ δ ∧ N R w) ∈ smbar (N ʻʻ δ) δ := by
    refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rintro R S w ⟨⟨hw, hR⟩, ⟨-, hS⟩⟩; exact huniq w R S hw hR hS
    · rintro R w v ⟨⟨hw, hR⟩, ⟨hv, hR'⟩⟩; exact hinj w v R hw hv hR hR'
    · show N ʻʻ δ = dom _
      ext R
      exact ⟨fun ⟨w, hw, hR⟩ => ⟨w, hw, hR⟩, fun ⟨w, hw, hR⟩ => ⟨w, hw, hR⟩⟩
    · show δ = codom _
      ext w
      exact ⟨fun hw => let ⟨R, hR⟩ := hex w hw; ⟨R, hw, hR⟩, fun ⟨_, hw, _⟩ => hw⟩
  obtain ⟨c1, -, -, hexc⟩ := pmB2_core42 H
  exact ⟨pmB2_smsm_trans c1 (pmB2_smsm_coupleImg' hΦ G), hexc⟩

private theorem pmB2_hyp422 {X Y Vt : Type*} {M : (X → Y → Prop) → Vt → Prop} {δ : Set Vt} {G : Set Y}
    (h : (M ↾ δ ∈ arrow one one ∧
        ∀ w v, (w ∈ δ ∧ v ∈ δ) ∧
          Desc M w (fun R => Desc M v (fun S => (dom R ∩ dom S).Nonempty)) → w = v) ∧
        ∀ w, w ∈ δ → Desc M w (fun R => R ∈ arrow one one) ∧
          Desc M w (fun R => codom R = G)) :
    smsm (D ʻʻ (M ʻʻ δ)) (coupleImg G ʻʻ δ) ∧ D ʻʻ (M ʻʻ δ) ∈ Cls2excl := by
  obtain ⟨⟨h11, hdj⟩, hw⟩ := h
  have hu : ∀ w, w ∈ δ → ∃ b, (∀ R, M R w ↔ R = b) ∧ b ∈ arrow one one ∧ codom b = G := by
    intro w hwδ
    obtain ⟨⟨b, hb, h1⟩, ⟨b', hb', h2⟩⟩ := hw w hwδ
    have e : b' = b := (hb b').1 ((hb' b').2 rfl)
    subst e
    exact ⟨b', hb, h1, h2⟩
  refine pmB2_core422 (fun w hwδ => ?_) (fun w R S hwδ hR hS => ?_) (fun w R hwδ hR => ?_)
    (fun w v R hwδ hvδ hR hR' => (mem_arrow_one_one.1 h11).2 R w v ⟨⟨hR, hwδ⟩, ⟨hR', hvδ⟩⟩)
    (fun w v R S hwδ hvδ hR hS hne => hdj w v ⟨⟨hwδ, hvδ⟩, ?_⟩)
  · obtain ⟨b, hb, -⟩ := hu w hwδ; exact ⟨b, (hb b).2 rfl⟩
  · obtain ⟨b, hb, -⟩ := hu w hwδ; exact ((hb R).1 hR).trans ((hb S).1 hS).symm
  · obtain ⟨b, hb, h1, h2⟩ := hu w hwδ; rw [(hb R).1 hR]; exact ⟨h1, h2⟩
  · obtain ⟨b, hb, -⟩ := hu w hwδ
    obtain ⟨b', hb', -⟩ := hu v hvδ
    refine ⟨b, hb, b', hb', ?_⟩
    rw [← (hb R).1 hR, ← (hb' S).1 hS]; exact hne

/-- ✱116·422. \[\begin{align}&\vdash \colon\ldotp M \upharpoonright \delta \in 1 \rightarrow 1 : w, v \in \delta . \exists ! \text{D}ʻMʻw \cap \text{D}ʻMʻv . \supset _{w,v} . w = v :\\ &w \in \delta . \supset _{w} . Mʻw \in 1 \rightarrow 1 . \text{ᗡ}ʻMʻw = \gamma : \supset . \text{D}ʻʻMʻʻ\delta \text{ sm } \text{ sm } \gamma \downarrow_{,,}ʻʻ\delta\end{align}\]

`M ↾ δ ∈ 1 → 1`; `∃!D'M'w ∩ D'M'v` has two descriptions (the first with the larger scope);
`M'w ∈ 1 → 1 . ᗡ'M'w = γ` are two propositions, each with its description. -/
theorem pm116_422 {X Y Vt : Type*} {M : (X → Y → Prop) → Vt → Prop} {δ : Set Vt} {G : Set Y} :
    (M ↾ δ ∈ arrow one one ∧
        ∀ w v, (w ∈ δ ∧ v ∈ δ) ∧
          Desc M w (fun R => Desc M v (fun S => (dom R ∩ dom S).Nonempty)) → w = v) ∧
        (∀ w, w ∈ δ → Desc M w (fun R => R ∈ arrow one one) ∧
          Desc M w (fun R => codom R = G)) →
      smsm (D ʻʻ (M ʻʻ δ)) (coupleImg G ʻʻ δ) :=
  fun h => (pmB2_hyp422 h).1

/-- ✱116·43. \[\begin{align}&\vdash \colon\ldotp M\upharpoonright \delta \in 1\rightarrow 1:w,v\in \delta .\exists !\text{D}ʻMʻw\cap \text{D}ʻMʻv.\supset _{w,v}.w = v:\\ &w\in \delta .\supset _{w}.Mʻw\in 1\rightarrow 1.\text{ᗡ}ʻMʻw = \gamma :\\ &\supset .\text{Prod}ʻ\text{D}ʻʻMʻʻ\delta \text{ sm }\text{ sm }(\gamma \,\,\text{exp}\,\,\delta ).\Pi \text{Nc}ʻ\text{D}ʻʻMʻʻ\delta = (\text{Nc}ʻ\gamma )^{\text{Nc}ʻ\delta }\end{align}\]

`ΠNc'D''M''δ` is `piNc T (D ʻʻ (M ʻʻ δ))`; the arguments of `^` are normally adjusted
(✱116·03·04); the equation is in a free type `T`. -/
theorem pm116_43 {X Y Vt T : Type*} {M : (X → Y → Prop) → Vt → Prop} {δ : Set Vt} {G : Set Y} :
    (M ↾ δ ∈ arrow one one ∧
        ∀ w v, (w ∈ δ ∧ v ∈ δ) ∧
          Desc M w (fun R => Desc M v (fun S => (dom R ∩ dom S).Nonempty)) → w = v) ∧
        (∀ w, w ∈ δ → Desc M w (fun R => R ∈ arrow one one) ∧
          Desc M w (fun R => codom R = G)) →
      smsm (prodK (D ʻʻ (M ʻʻ δ))) (clsExp G δ) ∧
        piNc T (D ʻʻ (M ʻʻ δ)) = (n₀c G ^ᶜ n₀c δ : Set (Set T)) := by
  intro h
  obtain ⟨h1, hex⟩ := pmB2_hyp422 h
  have h2 : smsm (prodK (D ʻʻ (M ʻʻ δ))) (clsExp G δ) := pm115_51 h1
  refine ⟨h2, ?_⟩
  rw [pmB2_n₀c_exp]
  exact nc_eq_nc_of_sm (sm_trans (sm_symm (pmB2_sm_of_equiv (pmB2_prodEquiv hex)))
    (pmB2_smsm_sm h2))

private theorem pmB2_hyp44 {X Y Vt : Type*} {M : (X → Y → Prop) → Vt → Prop} {δ : Set Vt} {G : Set Y}
    (hG : G.Nonempty)
    (hz : ∀ z, Desc M z (fun R => R ∈ arrow one one) ∧ Desc M z (fun R => codom R = V))
    (hw : ∀ w v, (w ∈ δ ∧ v ∈ δ) ∧
      Desc M w (fun R => Desc M v (fun S => ((R ʻʻ G) ∩ (S ʻʻ G)).Nonempty)) → w = v) :
    smsm (D ʻʻ (opR cres G ʻʻ (M ʻʻ δ))) (coupleImg G ʻʻ δ) ∧
      D ʻʻ (opR cres G ʻʻ (M ʻʻ δ)) ∈ Cls2excl := by
  have hu : ∀ z, ∃ b, (∀ R, M R z ↔ R = b) ∧ b ∈ arrow one one ∧ codom b = Set.univ := by
    intro z
    obtain ⟨⟨b, hb, h1⟩, ⟨b', hb', h2⟩⟩ := hz z
    have e : b' = b := (hb b').1 ((hb' b').2 rfl)
    subst e
    exact ⟨b', hb, h1, h2.trans V_eq_univ⟩
  let N : (X → Y → Prop) → Vt → Prop := fun R w => ∃ R', M R' w ∧ R = R' ↾ G
  have hN : opR cres G ʻʻ (M ʻʻ δ) = N ʻʻ δ := by
    ext R
    constructor
    · rintro ⟨R', ⟨w, hwδ, hR'⟩, hR⟩
      exact ⟨w, hwδ, R', hR', hR⟩
    · rintro ⟨w, hwδ, R', hR', hR⟩
      exact ⟨R', ⟨w, hwδ, hR'⟩, hR⟩
  have meet : ∀ w v R' S', w ∈ δ → v ∈ δ → M R' w → M S' v →
      ((R' ʻʻ G) ∩ (S' ʻʻ G)).Nonempty → w = v := by
    intro w v R' S' hwδ hvδ hR' hS' hne
    obtain ⟨b, hb, -⟩ := hu w
    obtain ⟨b', hb', -⟩ := hu v
    refine hw w v ⟨⟨hwδ, hvδ⟩, b, hb, b', hb', ?_⟩
    rw [← (hb R').1 hR', ← (hb' S').1 hS']; exact hne
  rw [hN]
  refine pmB2_core422 (fun w _ => ?_) (fun w R S _ hR hS => ?_) (fun w R _ hR => ?_)
    (fun w v R hwδ hvδ hR hR' => ?_) (fun w v R S hwδ hvδ hR hS hne => ?_)
  · obtain ⟨b, hb, -⟩ := hu w; exact ⟨b ↾ G, b, (hb b).2 rfl, rfl⟩
  · obtain ⟨R', h1, rfl⟩ := hR
    obtain ⟨S', h2, rfl⟩ := hS
    obtain ⟨b, hb, -⟩ := hu w
    rw [(hb R').1 h1, (hb S').1 h2]
  · obtain ⟨R', h1, rfl⟩ := hR
    obtain ⟨b, hb, b11, bcod⟩ := hu w
    rw [(hb R').1 h1]
    obtain ⟨p1, p2⟩ := mem_arrow_one_one.1 b11
    refine ⟨mem_arrow_one_one.2 ⟨fun x y z ⟨⟨h, _⟩, ⟨h', _⟩⟩ => p1 x y z ⟨h, h'⟩,
      fun x y z ⟨⟨h, _⟩, ⟨h', _⟩⟩ => p2 x y z ⟨h, h'⟩⟩, ?_⟩
    ext y
    constructor
    · rintro ⟨x, -, hy⟩; exact hy
    · intro hy
      obtain ⟨x, hx⟩ : y ∈ codom b := bcod ▸ Set.mem_univ y
      exact ⟨x, hx, hy⟩
  · obtain ⟨R', h1, rfl⟩ := hR
    obtain ⟨R'', h2, e⟩ := hR'
    obtain ⟨g, hg⟩ := hG
    obtain ⟨b, hb, -, bcod⟩ := hu w
    rw [(hb R').1 h1] at e
    obtain ⟨x, hx⟩ : g ∈ codom b := bcod ▸ Set.mem_univ g
    have hx' : (R'' ↾ G) x g := e ▸ ⟨hx, hg⟩
    exact meet w v b R'' hwδ hvδ ((hb b).2 rfl) h2 ⟨x, ⟨g, hg, hx⟩, ⟨g, hg, hx'.1⟩⟩
  · obtain ⟨R', h1, rfl⟩ := hR
    obtain ⟨S', h2, rfl⟩ := hS
    obtain ⟨x, ⟨g, hx, hg⟩, ⟨g', hx', hg'⟩⟩ := hne
    exact meet w v R' S' hwδ hvδ h1 h2 ⟨x, ⟨g, hg, hx⟩, ⟨g', hg', hx'⟩⟩

/-- ✱116·44. \[\begin{align}&\vdash \colon\ldotp \exists !\gamma :(z).Mʻz\in 1\rightarrow 1.\text{ᗡ}ʻMʻz = \text{V}:\\ &w,v\in \delta .\exists !(Mʻw)ʻʻ\gamma \cap (Mʻv)ʻʻ\gamma .\supset _{w,v}.w = v:\\ &\supset .\text{D}ʻʻ\upharpoonright \gammaʻʻMʻʻ\delta \text{ sm }\text{ sm }\gamma \downarrow_{,,}ʻʻ\delta .\text{Prod}ʻ\text{D}ʻʻ\upharpoonright \gamma ʻʻMʻʻ\delta \text{ sm }\text{ sm }(\gamma \,\,\text{exp}\,\,\delta )\end{align}\]

`D''↾γ''M''δ` is `D ʻʻ (opR cres G ʻʻ (M ʻʻ δ))` (`↾γ` the relation of `R ↾ γ` to `R`, ✱38);
`(z) . M'z ∈ 1 → 1 . ᗡ'M'z = V` is `∀ z` of two propositions with their descriptions. -/
theorem pm116_44 {X Y Vt : Type*} {M : (X → Y → Prop) → Vt → Prop} {δ : Set Vt} {G : Set Y} :
    (G.Nonempty ∧ ∀ z, Desc M z (fun R => R ∈ arrow one one) ∧ Desc M z (fun R => codom R = V)) ∧
        (∀ w v, (w ∈ δ ∧ v ∈ δ) ∧
          Desc M w (fun R => Desc M v (fun S => ((R ʻʻ G) ∩ (S ʻʻ G)).Nonempty)) → w = v) →
      smsm (D ʻʻ (opR cres G ʻʻ (M ʻʻ δ))) (coupleImg G ʻʻ δ) ∧
        smsm (prodK (D ʻʻ (opR cres G ʻʻ (M ʻʻ δ)))) (clsExp G δ) := by
  rintro ⟨⟨hG, hz⟩, hw⟩
  obtain ⟨h1, -⟩ := pmB2_hyp44 hG hz hw
  exact ⟨h1, pm115_51 h1⟩

/-- ✱116·45. \[\begin{align}&\vdash \colon\ldotp (z).Mʻz\in 1\rightarrow 1.\text{ᗡ}ʻMʻz = \text{V}:\\ &w,v\in \delta .\exists !(Mʻw)ʻʻ\gamma \cap (Mʻv)ʻʻ\gamma .\supset _{w,v}.w\\ & = v:\supset .\text{Prod}ʻ\text{D}ʻʻ\upharpoonright \gamma ʻʻMʻʻ\delta \text{ sm }(\gamma \,\,\text{exp}\,\,\delta )\end{align}\] -/
theorem pm116_45 {X Y Vt : Type*} {M : (X → Y → Prop) → Vt → Prop} {δ : Set Vt} {G : Set Y} :
    (∀ z, Desc M z (fun R => R ∈ arrow one one) ∧ Desc M z (fun R => codom R = V)) ∧
        (∀ w v, (w ∈ δ ∧ v ∈ δ) ∧
          Desc M w (fun R => Desc M v (fun S => ((R ʻʻ G) ∩ (S ʻʻ G)).Nonempty)) → w = v) →
      sm (prodK (D ʻʻ (opR cres G ʻʻ (M ʻʻ δ)))) (clsExp G δ) := by
  rintro ⟨hz, hw⟩
  by_cases hG : G.Nonempty
  · exact pmB2_smsm_sm (pm116_44 ⟨⟨hG, hz⟩, hw⟩).2
  · rw [Set.not_nonempty_iff_eq_empty] at hG
    subst hG
    by_cases hδ : δ.Nonempty
    · refine pmB2_sm_empty (pmB2_prodK_empty_of ?_) ?_
      · obtain ⟨w, hw⟩ := hδ
        obtain ⟨⟨b, hb, -⟩, -⟩ := hz w
        refine ⟨b ↾ ∅, ⟨b, ⟨w, hw, (hb b).2 rfl⟩, rfl⟩, ?_⟩
        show ∅ = dom (b ↾ ∅)
        ext x; simp only [Set.mem_empty_iff_false, false_iff]
        rintro ⟨y, -, hy⟩; exact hy
      · rw [← Null_eq_empty (α := Y), pm116_182 hδ, Null_eq_empty]
    · rw [Set.not_nonempty_iff_eq_empty] at hδ
      subst hδ
      have e1 : D ʻʻ (opR cres (∅ : Set Y) ʻʻ (M ʻʻ (∅ : Set Vt))) = ∅ := by
        ext Q; simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨R, ⟨R', ⟨w, hw, -⟩, -⟩, -⟩; exact hw
      have e3 : clsExp (∅ : Set Y) (∅ : Set Vt) = ι ∅ := by
        rw [← Null_eq_empty (α := Vt), pm116_181, Null_eq_empty]
      rw [e1, e3]
      have e2 : prodK (∅ : Set (Set X)) = ι ∅ := by
        rw [pm115_144 (Set.empty_subset _)]
        congr 1; ext x; simp only [Set.mem_empty_iff_false, iff_false]; rintro ⟨A, hA, -⟩; exact hA
      rw [e2, unitCls_eq_singleton, unitCls_eq_singleton]
      exact pmB2_sm_of_equiv (Equiv.ofUnique _ _)

/-- ✱116·5. \(\vdash : \beta \cap \gamma = \Lambda . \supset . (\alpha \,\,\text{exp}\,\, \beta ) \times (\alpha \,\,\text{exp}\,\, \gamma ) \text{ sm } \alpha \,\,\text{exp}\,\, (\beta \cup \gamma )\)

`(α exp β) × (α exp γ)` is `clsExp A B ×ₐ clsExp A G`; `β`, `γ` are of one type (`β ∩ γ`). -/
theorem pm116_5 {X Y : Type*} {A : Set X} {B G : Set Y} :
    B ∩ G = Λ → sm (clsExp A B ×ₐ clsExp A G) (clsExp A (B ∪ G)) := by
  intro h
  rw [Null_eq_empty] at h
  classical
  have hd : Disjoint B G := Set.disjoint_iff_inter_eq_empty.2 h
  exact pmB2_sm_of_equiv ((pmB2_clsTimesEquiv _ _).trans
    ((Equiv.prodComm _ _).trans (((pmB2_clsExpEquiv A B).prodCongr
      (pmB2_clsExpEquiv A G)).trans ((Equiv.sumArrowEquivProdArrow _ _ _).symm.trans
        ((Equiv.arrowCongr (Equiv.Set.union hd).symm (Equiv.refl _)).trans
          (pmB2_clsExpEquiv A (B ∪ G)).symm)))))

/-- ✱116·51. \(\vdash . (\alpha \,\,\text{exp}\,\, \beta ) \times (\alpha \,\,\text{exp}\,\, \gamma ) \text{ sm } \alpha \,\,\text{exp}\,\, (\beta + \gamma )\)

`β + γ` is the class-sum `B +ₐ G` (`β`, `γ` of any types). -/
theorem pm116_51 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} :
    sm (clsExp A B ×ₐ clsExp A G) (clsExp A (B +ₐ G)) :=
  pmB2_sm_of_equiv ((pmB2_clsTimesEquiv _ _).trans
    ((Equiv.prodComm _ _).trans (((pmB2_clsExpEquiv A B).prodCongr
      (pmB2_clsExpEquiv A G)).trans ((Equiv.sumArrowEquivProdArrow _ _ _).symm.trans
        ((Equiv.arrowCongr (clsSumEquiv B G).symm (Equiv.refl _)).trans
          (pmB2_clsExpEquiv A (B +ₐ G)).symm)))))

private theorem pmB2_AdeqExp_nc' {α β W : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (h : AdeqExp W μ ν) (A : Set α) (B : Set β) (hB : B.Nonempty) :
    (nc W (clsExp A B)).Nonempty := by
  by_cases hα : Nonempty α
  · exact pmB2_AdeqExp_nc h A B
  · have : IsEmpty α := not_nonempty_iff.1 hα
    refine nc_nonempty_iff.2 ⟨fun ξ => isEmptyElim ((pmB2_clsExpEquiv A B ξ)
      ⟨hB.some, hB.some_mem⟩).1, fun ξ => isEmptyElim ((pmB2_clsExpEquiv A B ξ)
        ⟨hB.some, hB.some_mem⟩).1⟩

/-- ✱116·52. \(\vdash .\mu ^\nu \times _{c} \mu ^{\varpi } = \mu ^{v +_{c}\varpi }\)

The e-text prints `v +_c ϖ` for `ν +_c ϖ`. By convention IIT the arithmetical components `μ^ν`,
`μ^ϖ`, `ν +_c ϖ` have their own types, adequate (`AdeqExp`, `AdeqAdd`); the equation is in a
free type `T`. Since `AdeqExp` holds vacuously when the base type is empty (while `Λ^Λ = 1` then
has no member), the base type is taken non-empty, as PM assumes of every type.

**Status.** proved (reading): transcription error (`v` for `ν`); convention IIT (Prefatory
Statement, IV); `[Nonempty X]` for the type of the members of `μ`'s members (PM assumes every
type has a member, Introduction, Ch. I). -/
theorem pm116_52 {X Y Z W₁ W₂ W₃ T : Type*} [Nonempty X] {μ : Set (Set X)} {ν : Set (Set Y)}
    {ϖ : Set (Set Z)} (h₁ : AdeqExp W₁ μ ν) (h₂ : AdeqExp W₂ μ ϖ) (h₃ : AdeqAdd W₃ ν ϖ) :
    ((μ ^ᶜ ν : Set (Set W₁)) ×ᶜ (μ ^ᶜ ϖ : Set (Set W₂)) : Set (Set T)) =
      μ ^ᶜ (ν +ᶜ ϖ : Set (Set W₃)) := by
  by_cases hN : (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ϖ ∈ N₀C
  · obtain ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, ⟨C, rfl⟩⟩ := hN
    obtain ⟨S₁, e₁, s₁⟩ := pmB2_nc_n₀c (pmB2_AdeqExp_nc h₁ A B)
    obtain ⟨S₂, e₂, s₂⟩ := pmB2_nc_n₀c (pmB2_AdeqExp_nc h₂ A C)
    obtain ⟨S₃, e₃, s₃⟩ := pmB2_nc_n₀c (h₃.nc_nonempty B C)
    rw [pmB2_n₀c_exp A B, e₁, pmB2_n₀c_exp A C, e₂, n₀c_cardAdd_n₀c B C, e₃,
      pmB2_n₀c_mul, pmB2_n₀c_exp]
    apply nc_eq_nc_of_sm
    obtain ⟨f₁⟩ := sm_iff_nonempty_equiv.1 s₁
    obtain ⟨f₂⟩ := sm_iff_nonempty_equiv.1 s₂
    obtain ⟨f₃⟩ := sm_iff_nonempty_equiv.1 s₃
    exact pmB2_sm_of_equiv ((pmB2_clsTimesEquiv S₂ S₁).trans ((Equiv.prodComm _ _).trans
      (((f₁.trans (pmB2_clsExpEquiv A B)).prodCongr (f₂.trans (pmB2_clsExpEquiv A C))).trans
        ((Equiv.sumArrowEquivProdArrow _ _ _).symm.trans ((Equiv.arrowCongr
          ((clsSumEquiv B C).symm.trans f₃.symm) (Equiv.refl _)).trans
            (pmB2_clsExpEquiv A S₃).symm)))))
  · have hL : ((μ ^ᶜ ν : Set (Set W₁)) ×ᶜ (μ ^ᶜ ϖ : Set (Set W₂)) : Set (Set T)) = ∅ := by
      by_cases h1 : μ ∈ N₀C ∧ ν ∈ N₀C
      · have h2 : ¬(μ ∈ N₀C ∧ ϖ ∈ N₀C) := fun h => hN ⟨h1, h.2⟩
        rw [pmB2_cardExp_empty h2]
        exact pmB2_cardMul_empty fun h => pmB2_empty_not_N₀C h.2
      · rw [pmB2_cardExp_empty h1]
        exact pmB2_cardMul_empty fun h => pmB2_empty_not_N₀C h.1
    have hR : (μ ^ᶜ (ν +ᶜ ϖ : Set (Set W₃)) : Set (Set T)) = ∅ := by
      by_cases h1 : ν ∈ N₀C ∧ ϖ ∈ N₀C
      · exact pmB2_cardExp_empty fun h => hN ⟨⟨h.1, h1.1⟩, h1.2⟩
      · rw [pmB2_cardAdd_empty h1]
        exact pmB2_cardExp_empty fun h => pmB2_empty_not_N₀C h.2
    rw [hL, hR]

/-- ✱116·529. \(R\dagger = R\parallel \breve{R} \quad\text{Dft}[*116]\)

A temporary definition (Dft) for ✱116 (made permanent in ✱150), printed in the e-text as a
proposition.

**Status.** definition: the Dft `R† = R ‖ R̆` holds by `rfl`. -/
theorem pm116_529 {X Y : Type*} {R : X → Y → Prop} : dagger R = R ∥ R˘ := rfl

private theorem pmB2_coupleR_img {X Z : Type*} (z : Z) (A : Set X) :
    coupleR z ʻʻ A = (fun x => x ↓ z) '' A := by
  ext R; exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩

private theorem pmB2_coupleR_inj {X Z : Type*} (z : Z) : Function.Injective (fun x : X => x ↓ z) :=
  fun _ _ e => (couple_eq_couple_iff.1 e).1

private noncomputable def pmB2_coupleR_equiv {X Z : Type*} (z : Z) (A : Set X) :
    ↥(coupleR z ʻʻ A) ≃ ↥A :=
  (Set.equivOfEq (pmB2_coupleR_img z A)).trans (Equiv.Set.image _ A (pmB2_coupleR_inj z)).symm

/-- The selections from `μ̂{(∃z) . z ∈ γ . μ = ↓z''α × ↓z''β}`. -/
private noncomputable def pmB2_selM53 {X Y Z : Type*} {A : Set X} {B : Set Y} (G : Set Z)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ↥(sel memRel ((fun z => (coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B)) '' G)) ≃ (↥G → ↥B × ↥A) := by
  have hinj : Set.InjOn (fun z => (coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B)) G := by
    intro z _ w _ e
    obtain ⟨x, hx⟩ := hA
    obtain ⟨y, hy⟩ := hB
    have e' : (coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B) = (coupleR w ʻʻ A) ×ₐ (coupleR w ʻʻ B) := e
    have : (y ↓ z) ↓ (x ↓ z) ∈ (coupleR w ʻʻ A) ×ₐ (coupleR w ʻʻ B) := by
      rw [← e']; exact couple_mem_clsTimes.2 ⟨⟨y, hy, rfl⟩, ⟨x, hx, rfl⟩⟩
    obtain ⟨⟨y', -, e'⟩, -⟩ := couple_mem_clsTimes.1 this
    exact (couple_eq_couple_iff.1 e').2
  exact (pmB2_selE _).trans ((pmB2_piImage _ G hinj (fun μ => ↥(μ : Set _))).trans
    (Equiv.piCongrRight fun z : ↥G => (pmB2_clsTimesEquiv _ _).trans
      ((pmB2_coupleR_equiv z.1 B).prodCongr (pmB2_coupleR_equiv z.1 A))))

private theorem pmB2_M53_eq {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} :
    {μ | ∃ z, z ∈ G ∧ μ = (coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B)} =
      (fun z => (coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B)) '' G := by
  ext μ; exact ⟨fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩, fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩⟩

/-- ✱116·53. \[\begin{align}\vdash :\exists !&\alpha .\exists !\beta .\supset .\\ &(\alpha \,\,\text{exp}\,\,\gamma ) \times (\beta \,\,\text{exp}\,\,\gamma )\text{ sm }{\in}_{\Delta}ʻ\hat{\mu} \{(\exists z).z\in \gamma .\mu = \downarrow zʻʻ\alpha \times \downarrow zʻʻ\beta\}\end{align}\]

`↓z''α` is `coupleR z ʻʻ A`. -/
theorem pm116_53 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} :
    A.Nonempty ∧ B.Nonempty →
      sm (clsExp A G ×ₐ clsExp B G)
        (sel memRel {μ | ∃ z, z ∈ G ∧ μ = (coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B)}) := by
  rintro ⟨hA, hB⟩
  rw [pmB2_M53_eq]
  exact pmB2_sm_of_equiv ((pmB2_clsTimesEquiv _ _).trans (((pmB2_clsExpEquiv B G).prodCongr
    (pmB2_clsExpEquiv A G)).trans ((Equiv.arrowProdEquivProdArrow _ _ _).symm.trans
      (pmB2_selM53 G hA hB).symm)))

private theorem pmB2_dag_couple {X Z : Type*} (z : Z) (x y : X) :
    coupleR z ⨾ ((x ↓ y) ⨾ (coupleR z)˘) = (x ↓ z) ↓ (y ↓ z) := by
  funext U W
  apply propext
  constructor
  · rintro ⟨v, hU, w, ⟨rfl, rfl⟩, hW⟩
    exact ⟨hU, hW⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨x, rfl, y, ⟨rfl, rfl⟩, rfl⟩

private theorem pmB2_dag_apply {X Z : Type*} {A B : Set X} (z : Z) (P : (X → Z → Prop) → (X → Z → Prop) → Prop)
    (Q : X → X → Prop) :
    (dagger (coupleR z) ↾ (A ×ₐ B)) P Q ↔
      ∃ x y, (x ∈ B ∧ y ∈ A) ∧ Q = x ↓ y ∧ P = (x ↓ z) ↓ (y ↓ z) := by
  constructor
  · rintro ⟨hPQ, hQ⟩
    obtain ⟨x, y, hxy, rfl⟩ := pmB2_mem_clsTimes.1 hQ
    rw [dagger, dpar_iff, pmB2_dag_couple] at hPQ
    exact ⟨x, y, hxy, rfl, hPQ⟩
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    exact ⟨by rw [dagger, dpar_iff, pmB2_dag_couple], couple_mem_clsTimes.2 hxy⟩

private theorem pmB2_dag_one_one {X Z : Type*} {A B : Set X} (z : Z) :
    dagger (coupleR z) ↾ (A ×ₐ B) ∈ arrow one one := by
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro P P' Q ⟨h, h'⟩
    obtain ⟨x, y, -, rfl, rfl⟩ := (pmB2_dag_apply z _ _).1 h
    obtain ⟨x', y', -, e, rfl⟩ := (pmB2_dag_apply z _ _).1 h'
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    rfl
  · rintro P Q Q' ⟨h, h'⟩
    obtain ⟨x, y, -, rfl, rfl⟩ := (pmB2_dag_apply z _ _).1 h
    obtain ⟨x', y', -, rfl, e⟩ := (pmB2_dag_apply z _ _).1 h'
    obtain ⟨e1, e2⟩ := couple_eq_couple_iff.1 e
    rw [(couple_eq_couple_iff.1 e1).1, (couple_eq_couple_iff.1 e2).1]

private theorem pmB2_dag_codom {X Z : Type*} {A B : Set X} (z : Z) :
    codom (dagger (coupleR z) ↾ (A ×ₐ B)) = A ×ₐ B := by
  ext Q
  constructor
  · rintro ⟨P, -, hQ⟩; exact hQ
  · intro hQ
    obtain ⟨x, y, hxy, rfl⟩ := pmB2_mem_clsTimes.1 hQ
    exact ⟨_, (pmB2_dag_apply z _ _).2 ⟨x, y, hxy, rfl, rfl⟩⟩

private theorem pmB2_dag_dom {X Z : Type*} {A B : Set X} (z : Z) :
    dom (dagger (coupleR z) ↾ (A ×ₐ B)) = (coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B) := by
  ext P
  constructor
  · rintro ⟨Q, h⟩
    obtain ⟨x, y, ⟨hx, hy⟩, rfl, rfl⟩ := (pmB2_dag_apply z _ _).1 h
    exact couple_mem_clsTimes.2 ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
  · intro hP
    obtain ⟨U, W, ⟨⟨x, hx, hU⟩, ⟨y, hy, hW⟩⟩, rfl⟩ := pmB2_mem_clsTimes.1 hP
    have hU' : U = x ↓ z := hU
    have hW' : W = y ↓ z := hW
    subst hU'; subst hW'
    exact ⟨x ↓ y, (pmB2_dag_apply z _ _).2 ⟨x, y, ⟨hx, hy⟩, rfl, rfl⟩⟩

private theorem pmB2_M531_desc {X Z : Type*} {A B : Set X} {G : Set Z} {z : Z} (hz : z ∈ G)
    (ψ : (((X → Z → Prop) → (X → Z → Prop) → Prop) → (X → X → Prop) → Prop) → Prop) :
    Desc (fun R z => z ∈ G ∧ R = dagger (coupleR z) ↾ (A ×ₐ B)) z ψ ↔
      ψ (dagger (coupleR z) ↾ (A ×ₐ B)) :=
  TheIs_iff_of_unique fun _ => ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

/-- ✱116·531. \[\begin{align}\vdash \colon\ldotp &M = \hat{R} \hat{z} \{z\in \gamma .R = (\downarrow z)\dagger \upharpoonright (\alpha \times \beta )\}.\supset :\\ &z\in \gamma .\supset _{z}.Mʻz = (\downarrow z)\dagger \upharpoonright (\alpha \times \beta ).Mʻz\in 1\rightarrow 1.\text{ᗡ}ʻMʻz = \alpha \times \beta \end{align}\]

`(↓z)†` is `dagger (coupleR z)` (✱116·529); `α × β` makes `α`, `β` of one type (the Dft `†` is
homogeneous). The hypothesis is the equation defining `M`; `M'z` is a description. -/
theorem pm116_531 {X Z : Type*} {A B : Set X} {G : Set Z}
    {M : (((X → Z → Prop) → (X → Z → Prop) → Prop) → (X → X → Prop) → Prop) → Z → Prop} :
    M = (fun R z => z ∈ G ∧ R = dagger (coupleR z) ↾ (A ×ₐ B)) →
      ∀ z, z ∈ G → (Desc M z (fun R => R = dagger (coupleR z) ↾ (A ×ₐ B)) ∧
        Desc M z (fun R => R ∈ arrow one one)) ∧ Desc M z (fun R => codom R = A ×ₐ B) := by
  rintro rfl z hz
  rw [pmB2_M531_desc hz, pmB2_M531_desc hz, pmB2_M531_desc hz]
  exact ⟨⟨rfl, pmB2_dag_one_one z⟩, pmB2_dag_codom z⟩

/-- ✱116·532. \(\vdash :\text{Hp}*116·531.\exists !\alpha .\exists !\beta .\supset .M\in 1\rightarrow 1.\text{ᗡ}ʻM = \gamma\)

"Hp ✱116·531" is the equation defining `M`. -/
theorem pm116_532 {X Z : Type*} {A B : Set X} {G : Set Z}
    {M : (((X → Z → Prop) → (X → Z → Prop) → Prop) → (X → X → Prop) → Prop) → Z → Prop} :
    (M = (fun R z => z ∈ G ∧ R = dagger (coupleR z) ↾ (A ×ₐ B)) ∧ A.Nonempty) ∧ B.Nonempty →
      M ∈ arrow one one ∧ codom M = G := by
  rintro ⟨⟨rfl, ⟨y, hy⟩⟩, ⟨x, hx⟩⟩
  refine ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩
  · rintro _ _ z ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
  · rintro _ z w ⟨⟨-, rfl⟩, ⟨-, e⟩⟩
    have h1 : (dagger (coupleR z) ↾ (A ×ₐ B)) ((x ↓ z) ↓ (y ↓ z)) (x ↓ y) :=
      (pmB2_dag_apply z _ _).2 ⟨x, y, ⟨hx, hy⟩, rfl, rfl⟩
    rw [e] at h1
    obtain ⟨x', y', -, e1, e2⟩ := (pmB2_dag_apply w _ _).1 h1
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e1
    exact (couple_eq_couple_iff.1 (couple_eq_couple_iff.1 e2).1).2
  · ext z
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

/-- ✱116·533. \[\begin{align}\vdash \colon\ldotp \text{Hp}*116·531.\supset :\text{D}ʻʻMʻʻ\gamma = \hat{\mu} \{(\exists z).z\in \gamma .\mu = \downarrow zʻʻ\alpha \times \downarrow zʻʻ\beta\}:\\ z,w\in \gamma .\exists !\text{D}ʻMʻz\cap \text{D}ʻMʻw.\supset _{z,w}.z = w\end{align}\]

`D''M''γ` is `D ʻʻ (M ʻʻ G)`; `∃!D'M'z ∩ D'M'w` has two descriptions, the first with the larger
scope. -/
theorem pm116_533 {X Z : Type*} {A B : Set X} {G : Set Z}
    {M : (((X → Z → Prop) → (X → Z → Prop) → Prop) → (X → X → Prop) → Prop) → Z → Prop} :
    M = (fun R z => z ∈ G ∧ R = dagger (coupleR z) ↾ (A ×ₐ B)) →
      D ʻʻ (M ʻʻ G) = {μ | ∃ z, z ∈ G ∧ μ = (coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B)} ∧
        ∀ z w, (z ∈ G ∧ w ∈ G) ∧
          Desc M z (fun R => Desc M w (fun S => (dom R ∩ dom S).Nonempty)) → z = w := by
  rintro rfl
  refine ⟨?_, ?_⟩
  · ext μ
    constructor
    · rintro ⟨R, ⟨z, hz, -, rfl⟩, hμ⟩
      exact ⟨z, hz, (show μ = dom _ from hμ).trans (pmB2_dag_dom z)⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, ⟨z, hz, hz, rfl⟩, (pmB2_dag_dom z).symm⟩
  · rintro z w ⟨⟨hz, hw⟩, h⟩
    rw [pmB2_M531_desc hz, pmB2_M531_desc hw, pmB2_dag_dom, pmB2_dag_dom] at h
    obtain ⟨P, h1, h2⟩ := h
    obtain ⟨U, W, ⟨⟨x, -, hU⟩, -⟩, rfl⟩ := pmB2_mem_clsTimes.1 h1
    obtain ⟨U', W', ⟨⟨x', -, hU'⟩, -⟩, e⟩ := pmB2_mem_clsTimes.1 h2
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    have e1 : U = x ↓ z := hU
    have e2 : U = x' ↓ w := hU'
    exact (couple_eq_couple_iff.1 (e1.symm.trans e2)).2

/-- ✱116·534. \(\vdash :\text{Hp}*116·532.\supset .{\in}_{\Delta}ʻ\text{D}ʻʻMʻʻ\gamma \text{ sm }(\alpha \times \beta )\,\,\text{exp}\,\,\gamma\)

"Hp ✱116·532" is the hypothesis of ✱116·532. -/
theorem pm116_534 {X Z : Type*} {A B : Set X} {G : Set Z}
    {M : (((X → Z → Prop) → (X → Z → Prop) → Prop) → (X → X → Prop) → Prop) → Z → Prop} :
    (M = (fun R z => z ∈ G ∧ R = dagger (coupleR z) ↾ (A ×ₐ B)) ∧ A.Nonempty) ∧ B.Nonempty →
      sm (sel memRel (D ʻʻ (M ʻʻ G))) (clsExp (A ×ₐ B) G) := by
  rintro ⟨⟨hM, hA⟩, hB⟩
  rw [(pm116_533 hM).1, pmB2_M53_eq]
  exact pmB2_sm_of_equiv ((pmB2_selM53 G hA hB).trans ((Equiv.arrowCongr (Equiv.refl _)
    (pmB2_clsTimesEquiv B A).symm).trans (pmB2_clsExpEquiv (A ×ₐ B) G).symm))

/-- ✱116·535. \[\begin{align}&\vdash :\exists !\alpha .\exists !\beta .\supset .(\alpha \,\,\text{exp}\,\,\gamma ) \times (\beta \,\,\text{exp}\,\,\gamma )\text{ sm }(\alpha \times \beta )\,\,\text{exp}\,\,\gamma\\ &[*116·53·533·534]\end{align}\] -/
theorem pm116_535 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} :
    A.Nonempty ∧ B.Nonempty → sm (clsExp A G ×ₐ clsExp B G) (clsExp (A ×ₐ B) G) :=
  fun _ => pmB2_exp_mul

/-- ✱116·54. \(\vdash .(\alpha \,\,\text{exp}\,\,\gamma ) \times (\beta \,\,\text{exp}\,\,\gamma )\text{ sm }(\alpha \times \beta )\,\,\text{exp}\,\,\gamma \)

`(α exp γ) × (β exp γ)` and `(α × β) exp γ` (`α`, `β`, `γ` of any types). -/
theorem pm116_54 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} :
    sm (clsExp A G ×ₐ clsExp B G) (clsExp (A ×ₐ B) G) := pmB2_exp_mul

/-- ✱116·55. \(\vdash .\mu ^{\varpi } \times _{c} \nu ^{\varpi } = (\mu \times _{c} \nu )^{\varpi }\)

By convention IIT `μ^ϖ`, `ν^ϖ`, `μ ×_c ν` have their own adequate types; the base types are
taken non-empty (as in ✱116·52).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV); `[Nonempty X]`,
`[Nonempty Y]` for the base types (PM assumes every type has a member, Introduction, Ch. I). -/
theorem pm116_55 {X Y Z W₁ W₂ W₃ T : Type*} [Nonempty X] [Nonempty Y] {μ : Set (Set X)}
    {ν : Set (Set Y)} {ϖ : Set (Set Z)} (h₁ : AdeqExp W₁ μ ϖ) (h₂ : AdeqExp W₂ ν ϖ)
    (h₃ : AdeqMul W₃ μ ν) :
    ((μ ^ᶜ ϖ : Set (Set W₁)) ×ᶜ (ν ^ᶜ ϖ : Set (Set W₂)) : Set (Set T)) =
      (μ ×ᶜ ν : Set (Set W₃)) ^ᶜ ϖ := by
  by_cases hN : (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ϖ ∈ N₀C
  · obtain ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, ⟨C, rfl⟩⟩ := hN
    obtain ⟨S₁, e₁, s₁⟩ := pmB2_nc_n₀c (pmB2_AdeqExp_nc h₁ A C)
    obtain ⟨S₂, e₂, s₂⟩ := pmB2_nc_n₀c (pmB2_AdeqExp_nc h₂ B C)
    obtain ⟨S₃, e₃, s₃⟩ := pmB2_nc_n₀c (pmB2_AdeqMul_nc h₃ A B)
    rw [pmB2_n₀c_exp A C, e₁, pmB2_n₀c_exp B C, e₂, pmB2_n₀c_mul A B, e₃,
      pmB2_n₀c_mul, pmB2_n₀c_exp]
    apply nc_eq_nc_of_sm
    obtain ⟨f₁⟩ := sm_iff_nonempty_equiv.1 s₁
    obtain ⟨f₂⟩ := sm_iff_nonempty_equiv.1 s₂
    obtain ⟨f₃⟩ := sm_iff_nonempty_equiv.1 s₃
    exact pmB2_sm_of_equiv ((pmB2_clsTimesEquiv S₂ S₁).trans
      (((f₂.trans (pmB2_clsExpEquiv B C)).prodCongr (f₁.trans (pmB2_clsExpEquiv A C))).trans
        ((Equiv.arrowProdEquivProdArrow _ _ _).symm.trans ((Equiv.arrowCongr (Equiv.refl _)
          ((pmB2_clsTimesEquiv B A).symm.trans f₃.symm)).trans (pmB2_clsExpEquiv S₃ C).symm))))
  · have hL : ((μ ^ᶜ ϖ : Set (Set W₁)) ×ᶜ (ν ^ᶜ ϖ : Set (Set W₂)) : Set (Set T)) = ∅ := by
      by_cases h1 : μ ∈ N₀C ∧ ϖ ∈ N₀C
      · have h2 : ¬(ν ∈ N₀C ∧ ϖ ∈ N₀C) := fun h => hN ⟨⟨h1.1, h.1⟩, h1.2⟩
        rw [pmB2_cardExp_empty h2]
        exact pmB2_cardMul_empty fun h => pmB2_empty_not_N₀C h.2
      · rw [pmB2_cardExp_empty h1]
        exact pmB2_cardMul_empty fun h => pmB2_empty_not_N₀C h.1
    have hR : ((μ ×ᶜ ν : Set (Set W₃)) ^ᶜ ϖ : Set (Set T)) = ∅ := by
      by_cases h1 : μ ∈ N₀C ∧ ν ∈ N₀C
      · exact pmB2_cardExp_empty fun h => hN ⟨h1, h.2⟩
      · rw [pmB2_cardMul_empty h1]
        exact pmB2_cardExp_empty fun h => pmB2_empty_not_N₀C h.1
    rw [hL, hR]

private theorem pmB2_K3_sum {X Y Z : Type*} (A : Set X) (B : Set Y) (G : Set Z) :
    sumCls (coupleImg A ʻʻʻ (coupleImg B ʻʻ G)) = coupleImg A ʻʻ (G ×ₐ B) := by
  ext Q
  constructor
  · rintro ⟨S, ⟨Y', ⟨z, hz, hY⟩, hS⟩, hQ⟩
    have hY' : Y' = opImg couple B z := hY
    have hS' : S = coupleImg A ʻʻ Y' := hS
    subst hY'; subst hS'
    obtain ⟨P, ⟨y, hy, hP⟩, hQP⟩ := hQ
    have hP' : P = y ↓ z := hP
    subst hP'
    exact ⟨y ↓ z, couple_mem_clsTimes.2 ⟨hy, hz⟩, hQP⟩
  · rintro ⟨P, hP, hQP⟩
    obtain ⟨y, z, ⟨hy, hz⟩, rfl⟩ := pmB2_mem_clsTimes.1 hP
    exact ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, y ↓ z, ⟨y, hy, rfl⟩, hQP⟩

private theorem pmB2_K3_arithm {X Y Z : Type*} {A : Set X} (hA : A.Nonempty) (B : Set Y) (G : Set Z) :
    coupleImg A ʻʻʻ (coupleImg B ʻʻ G) ∈ Cls3arithm := by
  refine ⟨pmB2_excl_iff.2 ?_, ?_⟩
  · rintro S S' Q ⟨Y₁, ⟨z, hz, hY₁⟩, hS⟩ ⟨Y₂, ⟨w, hw, hY₂⟩, hS'⟩ hQ hQ'
    have e1 : Y₁ = opImg couple B z := hY₁
    have e2 : Y₂ = opImg couple B w := hY₂
    have e3 : S = coupleImg A ʻʻ Y₁ := hS
    have e4 : S' = coupleImg A ʻʻ Y₂ := hS'
    subst e1; subst e2; subst e3; subst e4
    obtain ⟨P, ⟨y, hy, hP⟩, hQP⟩ := hQ
    obtain ⟨P', ⟨y', hy', hP'⟩, hQP'⟩ := hQ'
    have hP1 : P = y ↓ z := hP
    have hP2 : P' = y' ↓ w := hP'
    have hQ1 : Q = opImg couple A P := hQP
    have hQ2 : Q = opImg couple A P' := hQP'
    obtain ⟨x, hx⟩ := hA
    have : x ↓ P ∈ opImg couple A P' := hQ2 ▸ hQ1 ▸ ⟨x, hx, rfl⟩
    obtain ⟨x', -, e⟩ := this
    have := (couple_eq_couple_iff.1 e).2
    rw [hP1, hP2] at this
    rw [(couple_eq_couple_iff.1 this).2]
  · rw [pmB2_K3_sum]
    exact pmB2_coupleImg_excl A _

/-- ✱116·6. \[\begin{align}\vdash :\exists !\alpha .\supset .\alpha \,\,\text{exp}\,\,(\beta \times \gamma )\text{ sm } \text{Prod}ʻ\text{Prod}ʻʻ&\alpha \downarrow_{,,}ʻʻʻ\beta \downarrow_{,,}ʻʻ\gamma .\\ &\alpha \downarrow_{,,}ʻʻʻ\beta \downarrow_{,,}ʻʻ\gamma \in \text{Cls}^{3}\,\text{arithm}\end{align}\]

`α↓,,'''β↓,,''γ` is `coupleImg A ʻʻʻ (coupleImg B ʻʻ G)`; `Prod''` is `ProdK ʻʻ`. -/
theorem pm116_6 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} :
    A.Nonempty →
      sm (clsExp A (B ×ₐ G)) (prodK (ProdK ʻʻ (coupleImg A ʻʻʻ (coupleImg B ʻʻ G)))) ∧
        coupleImg A ʻʻʻ (coupleImg B ʻʻ G) ∈ Cls3arithm := by
  intro hA
  have h3 := pmB2_K3_arithm hA B G
  refine ⟨?_, h3⟩
  obtain ⟨h1, h2⟩ := pm115_34 h3
  rw [pmB2_K3_sum] at h1 h2
  refine sm_trans ?_ (sm_symm (sm_trans h1 h2))
  refine sm_trans (pmB2_sm_clsExp (sm_refl A) ?_) pm116_14
  exact pmB2_sm_of_equiv ((pmB2_clsTimesEquiv G B).trans ((Equiv.prodComm _ _).trans
    (pmB2_clsTimesEquiv B G).symm))

/-- ✱116·601. \(\vdash .\mid (\text{Cnv}ʻ\downarrow z)\in 1\rightarrow 1 \quad[*74·774.*72·184]\)

`|(Cnv'↓z)` is the relation `relProdR (coupleR z)˘` of `R | (↓z)˘` to `R` (✱38 with
`♀ = |`); the relations `R` are of any type `X → Y → Prop`. -/
theorem pm116_601 {X Y Z : Type*} {z : Z} :
    (relProdR ((coupleR z)˘ : Y → (Y → Z → Prop) → Prop) :
      (X → (Y → Z → Prop) → Prop) → (X → Y → Prop) → Prop) ∈ arrow one one := by
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro U U' R ⟨h, h'⟩
    rw [relProdR_apply] at h h'
    rw [h, h']
  · rintro U R R' ⟨h, h'⟩
    rw [relProdR_apply] at h h'
    funext x y
    have e := congrFun (congrFun (h.symm.trans h') x) (y ↓ z)
    apply propext
    constructor
    · intro hxy
      have : (R ⨾ (coupleR z)˘) x (y ↓ z) := ⟨y, hxy, rfl⟩
      rw [e] at this
      obtain ⟨y', h1, h2⟩ := this
      have h2' : y ↓ z = y' ↓ z := h2
      rw [(couple_eq_couple_iff.1 h2').1]; exact h1
    · intro hxy
      have : (R' ⨾ (coupleR z)˘) x (y ↓ z) := ⟨y, hxy, rfl⟩
      rw [← e] at this
      obtain ⟨y', h1, h2⟩ := this
      have h2' : y ↓ z = y' ↓ z := h2
      rw [(couple_eq_couple_iff.1 h2').1]; exact h1

/-- `|(Cnv'↓z)`, on relations of type `X → Y → Prop`. -/
private abbrev pmB2_Sz (X : Type*) {Y Z : Type*} (z : Z) :
    (X → (Y → Z → Prop) → Prop) → (X → Y → Prop) → Prop :=
  relProdR ((coupleR z)˘ : Y → (Y → Z → Prop) → Prop)

private theorem pmB2_couple_comp {X Y Z : Type*} (z : Z) (x : X) (y : Y) :
    (x ↓ y) ⨾ ((coupleR z)˘ : Y → (Y → Z → Prop) → Prop) = x ↓ (y ↓ z) := by
  funext u v
  apply propext
  constructor
  · rintro ⟨w, ⟨rfl, rfl⟩, hv⟩; exact ⟨rfl, hv⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨y, ⟨rfl, rfl⟩, rfl⟩

private theorem pmB2_Sz_img {X Y Z : Type*} {A : Set X} {B : Set Y} (z : Z) {ξ : Set (X → Y → Prop)}
    (hξ : ξ ⊆ B ×ₐ A) (P : X → (Y → Z → Prop) → Prop) :
    P ∈ pmB2_Sz X z ʻʻ ξ ↔ ∃ x y, x ↓ y ∈ ξ ∧ P = x ↓ (y ↓ z) := by
  constructor
  · rintro ⟨Q, hQ, h⟩
    replace h : P = Q ⨾ ((coupleR z)˘ : Y → (Y → Z → Prop) → Prop) := (relProdR_apply _ _ _).1 h
    obtain ⟨x, y, -, rfl⟩ := pmB2_mem_clsTimes.1 (hξ hQ)
    rw [pmB2_couple_comp] at h
    exact ⟨x, y, hQ, h⟩
  · rintro ⟨x, y, h, rfl⟩
    exact ⟨x ↓ y, h, (relProdR_apply _ _ _).2 (pmB2_couple_comp z x y).symm⟩

private theorem pmB2_Sz_couple {X Y Z : Type*} {A : Set X} {B : Set Y} (z : Z) {ξ : Set (X → Y → Prop)}
    (hξ : ξ ⊆ B ×ₐ A) (x : X) (y : Y) : x ↓ (y ↓ z) ∈ pmB2_Sz X z ʻʻ ξ ↔ x ↓ y ∈ ξ := by
  rw [pmB2_Sz_img z hξ]
  constructor
  · rintro ⟨x', y', h, e⟩
    obtain ⟨rfl, e2⟩ := couple_eq_couple_iff.1 e
    rw [(couple_eq_couple_iff.1 e2).1]; exact h
  · intro h; exact ⟨x, y, h, rfl⟩

private theorem pmB2_Sz_mem {X Y Z : Type*} {A : Set X} {B : Set Y} (z : Z) {ξ : Set (X → Y → Prop)}
    (hξ : ξ ∈ clsExp A B) : pmB2_Sz X z ʻʻ ξ ∈ clsExp A (opImg couple B z) := by
  obtain ⟨h1, h2⟩ := pmB2_mem_clsExp.1 hξ
  refine pmB2_mem_clsExp.2 ⟨fun P hP => ?_, fun P hP => ?_⟩
  · obtain ⟨y, hy, hP'⟩ := hP
    have hP'' : P = y ↓ z := hP'
    subst hP''
    have : A ∩ {x | x ↓ (y ↓ z) ∈ pmB2_Sz X z ʻʻ ξ} = A ∩ {x | x ↓ y ∈ ξ} := by
      ext x; exact and_congr Iff.rfl (pmB2_Sz_couple z h2 x y)
    rw [this]; exact h1 y hy
  · obtain ⟨x, y, h, rfl⟩ := (pmB2_Sz_img z h2 P).1 hP
    obtain ⟨hx, hy⟩ := couple_mem_clsTimes.1 (h2 h)
    exact couple_mem_clsTimes.2 ⟨hx, y, hy, rfl⟩

private theorem pmB2_Sz_onto {X Y Z : Type*} {A : Set X} {B : Set Y} (z : Z)
    {η : Set (X → (Y → Z → Prop) → Prop)} (hη : η ∈ clsExp A (opImg couple B z)) :
    ∃ ξ, ξ ∈ clsExp A B ∧ η = pmB2_Sz X z ʻʻ ξ := by
  obtain ⟨h1, h2⟩ := pmB2_mem_clsExp.1 hη
  have hsub : {Q | ∃ x y, x ↓ (y ↓ z) ∈ η ∧ Q = x ↓ y} ⊆ B ×ₐ A := by
    rintro Q ⟨x, y, h, rfl⟩
    obtain ⟨hx, y', hy', e⟩ := couple_mem_clsTimes.1 (h2 h)
    have e' : y ↓ z = y' ↓ z := e
    rw [(couple_eq_couple_iff.1 e').1]
    exact couple_mem_clsTimes.2 ⟨hx, hy'⟩
  have key : ∀ x y, x ↓ y ∈ {Q | ∃ x y, x ↓ (y ↓ z) ∈ η ∧ Q = x ↓ y} ↔ x ↓ (y ↓ z) ∈ η := by
    intro x y
    constructor
    · rintro ⟨x', y', h, e⟩
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e; exact h
    · intro h; exact ⟨x, y, h, rfl⟩
  refine ⟨_, pmB2_mem_clsExp.2 ⟨fun y hy => ?_, hsub⟩, ?_⟩
  · have : A ∩ {x | x ↓ y ∈ {Q | ∃ x y, x ↓ (y ↓ z) ∈ η ∧ Q = x ↓ y}} =
        A ∩ {x | x ↓ (y ↓ z) ∈ η} := by
      ext x; exact and_congr Iff.rfl (key x y)
    rw [this]; exact h1 (y ↓ z) ⟨y, hy, rfl⟩
  · ext P
    constructor
    · intro hP
      obtain ⟨x, Q, ⟨hx, y, hy, hQ⟩, rfl⟩ := pmB2_mem_clsTimes.1 (h2 hP)
      have hQ' : Q = y ↓ z := hQ
      subst hQ'
      exact (pmB2_Sz_couple z hsub x y).2 ((key x y).2 hP)
    · intro hP
      obtain ⟨x, y, h, rfl⟩ := (pmB2_Sz_img z hsub P).1 hP
      exact (key x y).1 h

private theorem pmB2_Sz_inj {X Y Z : Type*} {A : Set X} {B : Set Y} (z : Z) {ξ ξ' : Set (X → Y → Prop)}
    (hξ : ξ ⊆ B ×ₐ A) (hξ' : ξ' ⊆ B ×ₐ A) (e : pmB2_Sz X z ʻʻ ξ = pmB2_Sz X z ʻʻ ξ') :
    ξ = ξ' := by
  ext Q
  constructor
  · intro hQ
    obtain ⟨x, y, -, rfl⟩ := pmB2_mem_clsTimes.1 (hξ hQ)
    rw [← pmB2_Sz_couple z hξ', ← e, pmB2_Sz_couple z hξ]; exact hQ
  · intro hQ
    obtain ⟨x, y, -, rfl⟩ := pmB2_mem_clsTimes.1 (hξ' hQ)
    rw [← pmB2_Sz_couple z hξ, e, pmB2_Sz_couple z hξ']; exact hQ

private theorem pmB2_Rz_one_one {X Y Z : Type*} {A : Set X} {B : Set Y} (z : Z) :
    imgRel (pmB2_Sz X z) ↾ clsExp A B ∈ arrow one one := by
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro η η' ξ ⟨⟨h, -⟩, ⟨h', -⟩⟩
    exact (show η = _ from h).trans (show η' = _ from h').symm
  · rintro η ξ ξ' ⟨⟨h, hξ⟩, ⟨h', hξ'⟩⟩
    exact pmB2_Sz_inj z (pmB2_mem_clsExp.1 hξ).2 (pmB2_mem_clsExp.1 hξ').2
      ((show η = _ from h).symm.trans h')

private theorem pmB2_Rz_codom {X Y Z : Type*} {A : Set X} {B : Set Y} (z : Z) :
    codom (imgRel (pmB2_Sz X z) ↾ clsExp A B) = clsExp A B := by
  ext ξ
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

private theorem pmB2_Rz_dom {X Y Z : Type*} {A : Set X} {B : Set Y} (z : Z) :
    dom (imgRel (pmB2_Sz X z) ↾ clsExp A B) = clsExp A (opImg couple B z) := by
  ext η
  constructor
  · rintro ⟨ξ, h, hξ⟩
    rw [show η = _ from h]; exact pmB2_Sz_mem z hξ
  · intro hη
    obtain ⟨ξ, hξ, rfl⟩ := pmB2_Sz_onto z hη
    exact ⟨ξ, rfl, hξ⟩

private theorem pmB2_M602_desc {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} {z : Z} (hz : z ∈ G)
    (ψ : (Set (X → (Y → Z → Prop) → Prop) → Set (X → Y → Prop) → Prop) → Prop) :
    Desc (fun R z => z ∈ G ∧ R = imgRel (pmB2_Sz X z) ↾ clsExp A B) z ψ ↔
      ψ (imgRel (pmB2_Sz X z) ↾ clsExp A B) :=
  TheIs_iff_of_unique fun _ => ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

/-- ✱116·602. \[\begin{align}\vdash \colon\ldotp M = \hat{R} \hat{z} &[z\in \gamma .R = \{\mid (\text{Cnv}ʻ\downarrow z)\}_{\in }\upharpoonright (\alpha \,\,\text{exp}\,\,\beta )].\supset :\\ &z\in \gamma .\supset .Mʻz = \{\mid (\text{Cnv}ʻ\downarrow z)\}_{\in }\upharpoonright (\alpha \,\,\text{exp}\,\,\beta ):\text{ᗡ}ʻM = \gamma \end{align}\]

`{|(Cnv'↓z)}_∈ ↾ (α exp β)` is `imgRel (relProdR (coupleR z)˘) ↾ clsExp A B`; the hypothesis is
the equation defining `M`; `z` in the first clause is a real variable. -/
theorem pm116_602 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} {z : Z}
    {M : (Set (X → (Y → Z → Prop) → Prop) → Set (X → Y → Prop) → Prop) → Z → Prop} :
    M = (fun R z => z ∈ G ∧
        R = imgRel (relProdR ((coupleR z)˘ : Y → (Y → Z → Prop) → Prop)) ↾ clsExp A B) →
      (z ∈ G → Desc M z (fun R =>
          R = imgRel (relProdR ((coupleR z)˘ : Y → (Y → Z → Prop) → Prop)) ↾ clsExp A B)) ∧
        codom M = G := by
  rintro rfl
  refine ⟨fun hz => (pmB2_M602_desc hz _).2 rfl, ?_⟩
  ext w
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

/-- ✱116·603. \[\begin{align}&\vdash \colon\ldotp \text{Hp}*116·602.\supset :z\in \gamma .\supset .\text{ᗡ}ʻMʻz = \alpha \,\,\text{exp}\,\,\beta \\ &[*116·602.*37·231.*35·65]\end{align}\]

"Hp ✱116·602" is the equation defining `M`. -/
theorem pm116_603 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} {z : Z}
    {M : (Set (X → (Y → Z → Prop) → Prop) → Set (X → Y → Prop) → Prop) → Z → Prop} :
    M = (fun R z => z ∈ G ∧
        R = imgRel (relProdR ((coupleR z)˘ : Y → (Y → Z → Prop) → Prop)) ↾ clsExp A B) →
      (z ∈ G → Desc M z (fun R => codom R = clsExp A B)) := by
  rintro rfl hz
  exact (pmB2_M602_desc hz _).2 (pmB2_Rz_codom z)

/-- ✱116·604. \(\vdash \colon\ldotp \text{Hp}*116·602.\supset :z\in \gamma .\supset .\text{D}ʻMʻz = \text{Prod}ʻ\alpha \downarrow_{,,}ʻʻ\beta \downarrow_{,,}z\)

`α↓,,''β↓,,z` is `coupleImg A ʻʻ opImg couple B z`. -/
theorem pm116_604 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} {z : Z}
    {M : (Set (X → (Y → Z → Prop) → Prop) → Set (X → Y → Prop) → Prop) → Z → Prop} :
    M = (fun R z => z ∈ G ∧
        R = imgRel (relProdR ((coupleR z)˘ : Y → (Y → Z → Prop) → Prop)) ↾ clsExp A B) →
      (z ∈ G → Desc M z (fun R => dom R = prodK (coupleImg A ʻʻ opImg couple B z))) := by
  rintro rfl hz
  exact (pmB2_M602_desc hz _).2 (pmB2_Rz_dom z)

/-- ✱116·605. \(\vdash \colon\ldotp \text{Hp}*116·602.\supset :z\in \gamma .\supset .Mʻz\in 1\rightarrow 1\) -/
theorem pm116_605 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} {z : Z}
    {M : (Set (X → (Y → Z → Prop) → Prop) → Set (X → Y → Prop) → Prop) → Z → Prop} :
    M = (fun R z => z ∈ G ∧
        R = imgRel (relProdR ((coupleR z)˘ : Y → (Y → Z → Prop) → Prop)) ↾ clsExp A B) →
      (z ∈ G → Desc M z (fun R => R ∈ arrow one one)) := by
  rintro rfl hz
  exact (pmB2_M602_desc hz _).2 (pmB2_Rz_one_one z)

private theorem pmB2_dom_inj_z {X Y Z : Type*} {A : Set X} {B : Set Y} (hA : A.Nonempty)
    (hB : B.Nonempty) {z w : Z} (h : clsExp A (opImg couple B z) = clsExp A (opImg couple B w)) :
    z = w := by
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := hB
  have h1 : coupleL x ʻʻ opImg couple B z ∈ clsExp A (opImg couple B w) := h ▸ pm116_152 hx
  have h2 : x ↓ (y ↓ z) ∈ coupleL x ʻʻ opImg couple B z := ⟨y ↓ z, ⟨y, hy, rfl⟩, rfl⟩
  obtain ⟨-, y', -, e⟩ := couple_mem_clsTimes.1 ((pmB2_mem_clsExp.1 h1).2 h2)
  exact (couple_eq_couple_iff.1 (show y ↓ z = y' ↓ w from e)).2

/-- ✱116·606. \[\begin{align}\vdash \colon\ldotp \text{Hp}*116·602.&\exists !\alpha .\exists !\beta .\supset :\\ &M\in 1\rightarrow 1:z,w\in \gamma .\text{D}ʻMʻz = \text{D}ʻMʻw.\supset _{z,w}.z = w\end{align}\]

`∃!α . ∃!β` with the equation defining `M`; `D'M'z = D'M'w` has two descriptions, the first
with the larger scope. -/
theorem pm116_606 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z}
    {M : (Set (X → (Y → Z → Prop) → Prop) → Set (X → Y → Prop) → Prop) → Z → Prop} :
    (M = (fun R z => z ∈ G ∧
        R = imgRel (relProdR ((coupleR z)˘ : Y → (Y → Z → Prop) → Prop)) ↾ clsExp A B) ∧
        A.Nonempty) ∧ B.Nonempty →
      M ∈ arrow one one ∧
        ∀ z w, (z ∈ G ∧ w ∈ G) ∧ Desc M z (fun R => Desc M w (fun S => dom R = dom S)) →
          z = w := by
  rintro ⟨⟨rfl, hA⟩, hB⟩
  refine ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩
  · rintro _ _ z ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
  · rintro _ z w ⟨⟨hz, rfl⟩, ⟨hw, e⟩⟩
    apply pmB2_dom_inj_z hA hB
    rw [← pmB2_Rz_dom z, ← pmB2_Rz_dom w, e]
  · rintro z w ⟨⟨hz, hw⟩, h⟩
    rw [pmB2_M602_desc hz, pmB2_M602_desc hw, pmB2_Rz_dom, pmB2_Rz_dom] at h
    exact pmB2_dom_inj_z hA hB h

/-- ✱116·607. \[\begin{align}&\vdash \colon\ldotp \text{Hp}*116·602.\exists !\alpha .\exists !\beta .\supset :\\ &M\in 1\rightarrow 1.\text{D}ʻʻMʻʻ\gamma = \text{Prod}ʻʻ\alpha \downarrow_{,,}ʻʻʻ\beta \downarrow_{,,}ʻʻ\gamma :\\ &z,w\in \gamma .\text{D}ʻMʻz = \text{D}ʻMʻw.\supset _{z,w}.z = w:\\ &z\in \gamma .\supset _{z}.Mʻz\in 1\rightarrow 1.\text{ᗡ}ʻMʻz = \alpha \,\,\text{exp}\,\,\beta \quad[*116·606·604·605·603]\end{align}\]

`D''M''γ` is `D ʻʻ (M ʻʻ G)`; `Prod''α↓,,'''β↓,,''γ` is
`ProdK ʻʻ (coupleImg A ʻʻʻ (coupleImg B ʻʻ G))`. -/
theorem pm116_607 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z}
    {M : (Set (X → (Y → Z → Prop) → Prop) → Set (X → Y → Prop) → Prop) → Z → Prop} :
    (M = (fun R z => z ∈ G ∧
        R = imgRel (relProdR ((coupleR z)˘ : Y → (Y → Z → Prop) → Prop)) ↾ clsExp A B) ∧
        A.Nonempty) ∧ B.Nonempty →
      ((M ∈ arrow one one ∧ D ʻʻ (M ʻʻ G) = ProdK ʻʻ (coupleImg A ʻʻʻ (coupleImg B ʻʻ G))) ∧
        ∀ z w, (z ∈ G ∧ w ∈ G) ∧ Desc M z (fun R => Desc M w (fun S => dom R = dom S)) →
          z = w) ∧
        ∀ z, z ∈ G → Desc M z (fun R => R ∈ arrow one one) ∧
          Desc M z (fun R => codom R = clsExp A B) := by
  intro h
  obtain ⟨h1, h2⟩ := pm116_606 h
  obtain ⟨⟨hM, -⟩, -⟩ := h
  subst hM
  refine ⟨⟨⟨h1, ?_⟩, h2⟩, fun z hz => ⟨(pmB2_M602_desc hz _).2 (pmB2_Rz_one_one z),
    (pmB2_M602_desc hz _).2 (pmB2_Rz_codom z)⟩⟩
  ext P
  constructor
  · rintro ⟨R, ⟨z, hz, -, rfl⟩, hP⟩
    have hP' : P = dom _ := hP
    rw [hP', pmB2_Rz_dom]
    exact ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨Q, ⟨Y', ⟨z, hz, hY'⟩, hQ⟩, hP⟩
    have e1 : Y' = opImg couple B z := hY'
    have e2 : Q = coupleImg A ʻʻ Y' := hQ
    have e3 : P = prodK Q := hP
    subst e1; subst e2; subst e3
    exact ⟨_, ⟨z, hz, hz, rfl⟩, (pmB2_Rz_dom z).symm⟩

/-- ✱116·61. \[\begin{align}&\vdash :\exists !\alpha .\exists !\beta .\supset .\text{Prod}ʻ\text{Prod}ʻʻ\alpha \downarrow_{,,}ʻʻʻ\beta \downarrow_{,,}ʻʻ\gamma \text{ sm }(\alpha \,\,\text{exp}\,\,\beta )\,\,\text{exp}\,\,\gamma \\ &[*116·607·43]\end{align}\] -/
theorem pm116_61 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} :
    A.Nonempty ∧ B.Nonempty →
      sm (prodK (ProdK ʻʻ (coupleImg A ʻʻʻ (coupleImg B ʻʻ G)))) (clsExp (clsExp A B) G) :=
  fun ⟨hA, _⟩ => sm_trans (sm_symm (pm116_6 hA).1) pmB2_exp_prod_exp

/-- ✱116·611. \(\vdash :\exists !\alpha .\exists !\beta .\supset .\alpha \,\,\text{exp}\,\,(\beta \times \gamma )\text{ sm }(\alpha \,\,\text{exp}\,\,\beta )\,\,\text{exp}\,\,\gamma \quad[116·6·61]\) -/
theorem pm116_611 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} :
    A.Nonempty ∧ B.Nonempty → sm (clsExp A (B ×ₐ G)) (clsExp (clsExp A B) G) :=
  fun _ => pmB2_exp_prod_exp

/-- ✱116·62. \(\vdash .\alpha \,\,\text{exp}\,\,(\beta \times \gamma )\text{ sm }(\alpha \,\,\text{exp}\,\,\beta )\,\,\text{exp}\,\,\gamma\)

`β × γ` is `B ×ₐ G`. -/
theorem pm116_62 {X Y Z : Type*} {A : Set X} {B : Set Y} {G : Set Z} :
    sm (clsExp A (B ×ₐ G)) (clsExp (clsExp A B) G) := pmB2_exp_prod_exp

/-- ✱116·63. \(\vdash . \mu ^{\nu \times _{c} \varpi } = (\mu ^\nu )^{\varpi }\)

By convention IIT `ν ×_c ϖ` and `μ^ν` have their own adequate types; the base type of `μ` is
non-empty (as in ✱116·52).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV); `[Nonempty X]` for the
base type (PM assumes every type has a member, Introduction, Ch. I). -/
theorem pm116_63 {X Y Z W₁ W₂ T : Type*} [Nonempty X] {μ : Set (Set X)} {ν : Set (Set Y)}
    {ϖ : Set (Set Z)} (h₁ : AdeqMul W₁ ν ϖ) (h₂ : AdeqExp W₂ μ ν) :
    (μ ^ᶜ (ν ×ᶜ ϖ : Set (Set W₁)) : Set (Set T)) = (μ ^ᶜ ν : Set (Set W₂)) ^ᶜ ϖ := by
  by_cases hN : (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ϖ ∈ N₀C
  · obtain ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, ⟨C, rfl⟩⟩ := hN
    obtain ⟨S₁, e₁, s₁⟩ := pmB2_nc_n₀c (pmB2_AdeqMul_nc h₁ B C)
    obtain ⟨S₂, e₂, s₂⟩ := pmB2_nc_n₀c (pmB2_AdeqExp_nc h₂ A B)
    rw [pmB2_n₀c_mul B C, e₁, pmB2_n₀c_exp A B, e₂, pmB2_n₀c_exp, pmB2_n₀c_exp]
    apply nc_eq_nc_of_sm
    exact sm_trans (pmB2_sm_clsExp (sm_refl A) s₁) (sm_trans pmB2_exp_prod_exp
      (pmB2_sm_clsExp (sm_symm s₂) (sm_refl C)))
  · have hL : (μ ^ᶜ (ν ×ᶜ ϖ : Set (Set W₁)) : Set (Set T)) = ∅ := by
      by_cases h1 : ν ∈ N₀C ∧ ϖ ∈ N₀C
      · exact pmB2_cardExp_empty fun h => hN ⟨⟨h.1, h1.1⟩, h1.2⟩
      · rw [pmB2_cardMul_empty h1]
        exact pmB2_cardExp_empty fun h => pmB2_empty_not_N₀C h.2
    have hR : ((μ ^ᶜ ν : Set (Set W₂)) ^ᶜ ϖ : Set (Set T)) = ∅ := by
      by_cases h1 : μ ∈ N₀C ∧ ν ∈ N₀C
      · exact pmB2_cardExp_empty fun h => hN ⟨h1, h.2⟩
      · rw [pmB2_cardExp_empty h1]
        exact pmB2_cardExp_empty fun h => pmB2_empty_not_N₀C h.1
    rw [hL, hR]

/-- ✱116·64. \(\vdash . (\mu ^\nu )^{\varpi } = (\mu ^{\varpi })^\nu \quad[*116·63 . *113·27]\)

By convention IIT the inner powers have their own adequate types (non-empty base type, as in
✱116·52).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV); `[Nonempty X]` for the
base type (PM assumes every type has a member, Introduction, Ch. I). -/
theorem pm116_64 {X Y Z W₁ W₂ T : Type*} [Nonempty X] {μ : Set (Set X)} {ν : Set (Set Y)}
    {ϖ : Set (Set Z)} (h₁ : AdeqExp W₁ μ ν) (h₂ : AdeqExp W₂ μ ϖ) :
    ((μ ^ᶜ ν : Set (Set W₁)) ^ᶜ ϖ : Set (Set T)) = (μ ^ᶜ ϖ : Set (Set W₂)) ^ᶜ ν := by
  by_cases hN : (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ϖ ∈ N₀C
  · obtain ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, ⟨C, rfl⟩⟩ := hN
    obtain ⟨S₁, e₁, s₁⟩ := pmB2_nc_n₀c (pmB2_AdeqExp_nc h₁ A B)
    obtain ⟨S₂, e₂, s₂⟩ := pmB2_nc_n₀c (pmB2_AdeqExp_nc h₂ A C)
    rw [pmB2_n₀c_exp A B, e₁, pmB2_n₀c_exp A C, e₂, pmB2_n₀c_exp, pmB2_n₀c_exp]
    apply nc_eq_nc_of_sm
    obtain ⟨f₁⟩ := sm_iff_nonempty_equiv.1 s₁
    obtain ⟨f₂⟩ := sm_iff_nonempty_equiv.1 s₂
    exact pmB2_sm_of_equiv ((pmB2_clsExpEquiv S₁ C).trans ((Equiv.arrowCongr (Equiv.refl _)
      (f₁.trans (pmB2_clsExpEquiv A B))).trans ((Equiv.curry _ _ _).symm.trans
        ((Equiv.arrowCongr (Equiv.prodComm _ _) (Equiv.refl _)).trans
          ((Equiv.curry _ _ _).trans ((Equiv.arrowCongr (Equiv.refl _)
            (f₂.trans (pmB2_clsExpEquiv A C)).symm).trans (pmB2_clsExpEquiv S₂ B).symm))))))
  · have hL : ((μ ^ᶜ ν : Set (Set W₁)) ^ᶜ ϖ : Set (Set T)) = ∅ := by
      by_cases h1 : μ ∈ N₀C ∧ ν ∈ N₀C
      · exact pmB2_cardExp_empty fun h => hN ⟨h1, h.2⟩
      · rw [pmB2_cardExp_empty h1]
        exact pmB2_cardExp_empty fun h => pmB2_empty_not_N₀C h.1
    have hR : ((μ ^ᶜ ϖ : Set (Set W₂)) ^ᶜ ν : Set (Set T)) = ∅ := by
      by_cases h1 : μ ∈ N₀C ∧ ϖ ∈ N₀C
      · exact pmB2_cardExp_empty fun h => hN ⟨⟨h1.1, h.2⟩, h1.2⟩
      · rw [pmB2_cardExp_empty h1]
        exact pmB2_cardExp_empty fun h => pmB2_empty_not_N₀C h.1
    rw [hL, hR]

private theorem pmB2_sel_sel_excl {α β : Type*} {P : α → β → Prop} {F : Set (Set β)}
    (hF : F ∈ Cls2excl) : sm (sel memRel (selRel P ʻʻ F)) (sel P (sumCls F)) := by
  by_cases h0 : ∃ b, b ∈ sumCls F ∧ ¬∃ a, P a b
  · obtain ⟨b, ⟨B, hB, hb⟩, hna⟩ := h0
    refine pmB2_sm_empty (pmB2_sel_empty_of ⟨B, hB, ?_⟩) ?_
    · ext R
      simp only [Set.mem_empty_iff_false, false_iff]
      intro hR
      obtain ⟨a, ha⟩ := pmB2_sel_ex hR hb
      exact hna ⟨a, (pmB2_mem_sel.1 hR).2.1 a b ha⟩
    · ext R
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hR
      obtain ⟨a, ha⟩ := pmB2_sel_ex hR ⟨B, hB, hb⟩
      exact hna ⟨a, (pmB2_mem_sel.1 hR).2.1 a b ha⟩
  · push Not at h0
    have hne : ∀ B, B ∈ F → (sel P B).Nonempty := by
      intro B hB
      have : ∀ y : ↥B, ∃ a, P a y := fun y => h0 y ⟨B, hB, y.2⟩
      choose f hf using this
      exact ⟨_, pmB2_selOf_mem (P := P) (K := B) fun y => ⟨f y, hf y⟩⟩
    have hinj : Set.InjOn (sel P) F := by
      intro B hB B' _ e
      obtain ⟨R, hR⟩ := hne B hB
      have hR' : R ∈ sel P B' := e ▸ hR
      rw [← (pmB2_mem_sel.1 hR).2.2, ← (pmB2_mem_sel.1 hR').2.2]
    rw [show selRel P ʻʻ F = sel P '' F from pmB2_img_graph (sel P) F]
    exact pmB2_sm_of_equiv ((pmB2_selE _).trans ((pmB2_piImage (sel P) F hinj
      (fun S => ↥(S : Set (α → β → Prop)))).trans ((Equiv.piCongrRight fun B : ↥F =>
        pmB2_selEquiv P (B : Set β)).trans ((Equiv.piCurry
          (fun (B : ↥F) (y : ↥(B : Set β)) => {a // P a y})).symm.trans
            ((Equiv.piCongrLeft (fun y : ↥(sumCls F) => {a // P a y})
              (pmB2_sumClsEquiv hF).symm).trans (pmB2_selEquiv P (sumCls F)).symm)))))

/-- ✱116·651. \(\vdash : Q \in \text{Cls} \rightarrow 1 . \kappa \in \text{Cls}^{2} \text{excl} . \supset . {\in}_{\Delta}ʻP_{\Delta }ʻʻQʻʻʻ\kappa \text{ sm } P_{\Delta }ʻQʻʻsʻ\kappa \)

`Q'''κ` is `Q ʻʻʻ K`; `P_Δ''…` is `selRel P ʻʻ …`; `Q''s'κ` is `Q ʻʻ sumCls K`. -/
theorem pm116_651 {α β γ : Type*} {P : α → β → Prop} {Q : β → γ → Prop} {K : Set (Set γ)} :
    Q ∈ arrow Cls one ∧ K ∈ Cls2excl →
      sm (sel memRel (selRel P ʻʻ (Q ʻʻʻ K))) (sel P (Q ʻʻ sumCls K)) := by
  rintro ⟨hQ, hK⟩
  have hF : Q ʻʻʻ K ∈ Cls2excl := by
    refine pmB2_excl_iff.2 ?_
    rintro S S' x ⟨A, hA, hS⟩ ⟨B, hB, hS'⟩ hx hx'
    have e1 : S = Q ʻʻ A := hS
    have e2 : S' = Q ʻʻ B := hS'
    subst e1; subst e2
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hxb⟩ := hx'
    have e : a = b := (mem_arrow_Cls_one.1 hQ) x a b ⟨hxa, hxb⟩
    subst e
    rw [pmB2_excl_iff.1 hK A B a hA hB ha hb]
  have hs : sumCls (Q ʻʻʻ K) = Q ʻʻ sumCls K := by
    ext x
    constructor
    · rintro ⟨S, ⟨A, hA, hS⟩, hx⟩
      have e1 : S = Q ʻʻ A := hS
      rw [e1] at hx
      obtain ⟨a, ha, hxa⟩ := hx
      exact ⟨a, ⟨A, hA, ha⟩, hxa⟩
    · rintro ⟨a, ⟨A, hA, ha⟩, hxa⟩
      exact ⟨Q ʻʻ A, ⟨A, hA, rfl⟩, a, ha, hxa⟩
  rw [← hs]
  exact pmB2_sel_sel_excl hF

/-- ✱116·652. \[\begin{align}&\vdash : Q \in \text{Cls} \rightarrow 1 . \kappa \in \text{Cls}^{2} \text{excl} . \supset . {\in}_{\Delta}ʻ{\in}_{\Delta}ʻʻQʻʻʻ\kappa \text{ sm } {\in}_{\Delta}ʻQʻʻsʻ\kappa \\ &\left[*116·651 \frac{\in}{P}\right]\end{align}\]

`P` of ✱116·651 is the relation `∈` (`memRel`). -/
theorem pm116_652 {β γ : Type*} {Q : Set β → γ → Prop} {K : Set (Set γ)} :
    Q ∈ arrow Cls one ∧ K ∈ Cls2excl →
      sm (sel memRel (selRel memRel ʻʻ (Q ʻʻʻ K))) (sel memRel (Q ʻʻ sumCls K)) :=
  pm116_651

private theorem pmB2_coupleImg3_arithm {X Y : Type*} (A : Set X) {K : Set (Set Y)} (hK : K ∈ Cls2excl) :
    coupleImg A ʻʻʻ K ∈ Cls3arithm := by
  refine ⟨pmB2_excl_iff.2 ?_, pmB2_excl_iff.2 ?_⟩
  · rintro S S' Q ⟨B, hB, hS⟩ ⟨B', hB', hS'⟩ hQ hQ'
    have e1 : S = coupleImg A ʻʻ B := hS
    have e2 : S' = coupleImg A ʻʻ B' := hS'
    subst e1; subst e2
    obtain ⟨y, hy, hQy⟩ := hQ
    obtain ⟨y', hy', hQy'⟩ := hQ'
    have e3 : Q = opImg couple A y := hQy
    have e4 : Q = opImg couple A y' := hQy'
    by_cases hA : A.Nonempty
    · obtain ⟨x, hx⟩ := hA
      have : x ↓ y ∈ opImg couple A y' := e4 ▸ e3 ▸ ⟨x, hx, rfl⟩
      obtain ⟨x', -, e⟩ := this
      have hyy : y = y' := (couple_eq_couple_iff.1 e).2
      subst hyy
      rw [pmB2_excl_iff.1 hK B B' y hB hB' hy hy']
    · rw [Set.not_nonempty_iff_eq_empty] at hA
      subst hA
      have hE : ∀ w : Y, opImg couple (∅ : Set X) w = ∅ := fun w => by
        ext R; simp only [Set.mem_empty_iff_false, iff_false]; rintro ⟨x, hx, -⟩; exact hx
      have key : ∀ C : Set Y, C.Nonempty → coupleImg (∅ : Set X) ʻʻ C = {∅} := by
        intro C ⟨c, hc⟩
        ext Q'
        constructor
        · rintro ⟨w, -, hw⟩; exact (show Q' = _ from hw).trans (hE w)
        · intro h; exact ⟨c, hc, (Set.mem_singleton_iff.1 h).trans (hE c).symm⟩
      rw [key B ⟨y, hy⟩, key B' ⟨y', hy'⟩]
  · rintro S S' R ⟨T, ⟨B, hB, hT⟩, hS⟩ ⟨T', ⟨B', hB', hT'⟩, hS'⟩ hR hR'
    have e1 : T = coupleImg A ʻʻ B := hT
    have e2 : T' = coupleImg A ʻʻ B' := hT'
    subst e1; subst e2
    obtain ⟨y, -, hSy⟩ := hS
    obtain ⟨y', -, hSy'⟩ := hS'
    have e3 : S = opImg couple A y := hSy
    have e4 : S' = opImg couple A y' := hSy'
    subst e3; subst e4
    obtain ⟨x, -, hx⟩ := hR
    obtain ⟨x', -, hx'⟩ := hR'
    have e : x ↓ y = x' ↓ y' := (show R = _ from hx).symm.trans hx'
    rw [(couple_eq_couple_iff.1 e).2]

/-- ✱116·653. \(\vdash : \kappa \in \text{Cls}^{2} \text{excl} . \supset . \alpha \downarrow_{,,}ʻʻʻ\kappa \in \text{Cls}^{2} \text{arithm}\)

The e-text prints `Cls² arithm` for `Cls³ arithm` (✱115·02; `α↓,,'''κ` is a class of classes of
classes).

**Status.** proved (reading): transcription error: `Cls² arithm` is read `Cls³ arithm`. -/
theorem pm116_653 {X Y : Type*} {A : Set X} {K : Set (Set Y)} :
    K ∈ Cls2excl → coupleImg A ʻʻʻ K ∈ Cls3arithm :=
  fun hK => pmB2_coupleImg3_arithm A hK

private theorem pmB2_clsExp_proj {X Y : Type*} {A : Set X} {B : Set Y} {ξ : Set (X → Y → Prop)}
    (hξ : ξ ∈ clsExp A B) : {y | ∃ x, x ↓ y ∈ ξ} = B := by
  obtain ⟨h1, h2⟩ := pmB2_mem_clsExp.1 hξ
  ext y
  constructor
  · rintro ⟨x, hx⟩; exact (couple_mem_clsTimes.1 (h2 hx)).2
  · intro hy
    obtain ⟨c, hc⟩ := h1 y hy
    have : c ∈ A ∩ {x | x ↓ y ∈ ξ} := by rw [hc]; rfl
    exact ⟨c, this.2⟩

private theorem pmB2_clsExp_disj {X Y : Type*} {A : Set X} {B G : Set Y}
    (h : (clsExp A B ∩ clsExp A G).Nonempty) : B = G := by
  obtain ⟨ξ, h1, h2⟩ := h
  rw [← pmB2_clsExp_proj h1, ← pmB2_clsExp_proj h2]

private theorem pmB2_clsExp_img_excl {X Y : Type*} (A : Set X) (K : Set (Set Y)) :
    graph (clsExp A) ʻʻ K ∈ Cls2excl := by
  refine pmB2_excl_iff.2 ?_
  rintro S S' ξ ⟨B, -, hS⟩ ⟨B', -, hS'⟩ h h'
  have e1 : S = clsExp A B := hS
  have e2 : S' = clsExp A B' := hS'
  subst e1; subst e2
  rw [pmB2_clsExp_disj ⟨ξ, h, h'⟩]

private theorem pmB2_exp_sum {X Y : Type*} (A : Set X) {K : Set (Set Y)} (hK : K ∈ Cls2excl) :
    sm (prodK (graph (clsExp A) ʻʻ K)) (clsExp A (sumCls K)) := by
  by_cases h0 : ∃ B, B ∈ K ∧ clsExp A B = ∅
  · obtain ⟨B, hB, e⟩ := h0
    refine pmB2_sm_empty (pmB2_prodK_empty_of ⟨B, hB, e.symm⟩) ?_
    have hB' : B.Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      subst hc
      have : clsExp A (∅ : Set Y) = ι ∅ := by
        rw [← Null_eq_empty (α := Y), pm116_181, Null_eq_empty]
      rw [this] at e
      exact (Set.eq_empty_iff_forall_notMem.1 e) ∅ rfl
    have hA : ¬A.Nonempty := fun hA => by
      obtain ⟨ξ, hξ⟩ := pm116_171 (A := A) (B := B) (Or.inl hA)
      rw [e] at hξ; exact hξ
    rw [Set.not_nonempty_iff_eq_empty] at hA
    subst hA
    have hs : (sumCls K).Nonempty := let ⟨y, hy⟩ := hB'; ⟨y, B, hB, hy⟩
    rw [← Null_eq_empty (α := X), pm116_182 hs, Null_eq_empty]
  · push Not at h0
    have hinj : Set.InjOn (clsExp A) K := by
      intro B _ B' _ e
      obtain ⟨ξ, hξ⟩ := h0 B ‹_›
      exact pmB2_clsExp_disj ⟨ξ, hξ, e ▸ hξ⟩
    rw [pmB2_img_graph]
    have hF : clsExp A '' K ∈ Cls2excl := by
      rw [← pmB2_img_graph]; exact pmB2_clsExp_img_excl A K
    exact pmB2_sm_of_equiv ((pmB2_prodEquiv hF).trans ((pmB2_selE _).trans
      ((pmB2_piImage (clsExp A) K hinj (fun S => ↥(S : Set (Set (X → Y → Prop))))).trans
        ((Equiv.piCongrRight fun B : ↥K => pmB2_clsExpEquiv A (B : Set Y)).trans
          ((Equiv.piCurry (fun (B : ↥K) (_ : ↥(B : Set Y)) => ↥A)).symm.trans
            ((Equiv.arrowCongr (pmB2_sumClsEquiv hK).symm (Equiv.refl _)).trans
              (pmB2_clsExpEquiv A (sumCls K)).symm))))))

/-- ✱116·654. \(\vdash :\kappa \in \text{Cls}^{2} \text{excl}.\supset .\{\text{Prod}ʻ(\alpha \,\,\text{exp}\,\,)ʻʻ\kappa \}\text{ sm }\{\alpha \,\,\text{exp}\,\,(sʻ\kappa )\}\)

`(α exp)` is the relation of `α exp β` to `β`, `graph (clsExp A)`. -/
theorem pm116_654 {X Y : Type*} {A : Set X} {K : Set (Set Y)} :
    K ∈ Cls2excl → sm (prodK (graph (clsExp A) ʻʻ K)) (clsExp A (sumCls K)) :=
  fun hK => pmB2_exp_sum A hK

private theorem pmB2_sigma_sm_sum {X : Type*} {K : Set (Set X)} (hK : K ∈ Cls2excl) :
    sm (sumCls K) (clsSigma K) :=
  pmB2_sm_of_equiv ((pmB2_sumClsEquiv hK).trans (pmB2_clsSigmaEquiv K).symm)

/-- ✱116·655. \(\vdash :\kappa \in \text{Cls}^{2} \text{excl}.\supset .\Pi \text{Nc}ʻ(\alpha \,\,\text{exp}\,\,)ʻʻ\kappa = (\text{Nc}ʻ\alpha )^{\Sigma \text{Nc}ʻ\kappa } \quad[*116·654]\)

`ΣNc'κ` as an argument of `^` is read through its Df ✱112·02 as `Nc'Σ'κ`, normally adjusted
(✱116·04) to `N₀c'Σ'κ`; the equation is in a free type `T`.

**Status.** proved (reading): `ΣNc'κ` in the exponent is read `N₀c'Σ'κ` (✱112·02 with the
normal adjustment ✱116·04), and `Nc'α` is `N₀c'α` (✱116·03). -/
theorem pm116_655 {X Y T : Type*} {A : Set X} {K : Set (Set Y)} :
    K ∈ Cls2excl →
      piNc T (graph (clsExp A) ʻʻ K) = (n₀c A ^ᶜ n₀c (clsSigma K) : Set (Set T)) := by
  intro hK
  rw [pmB2_n₀c_exp]
  exact nc_eq_nc_of_sm (sm_trans (sm_symm (pmB2_sm_of_equiv (pmB2_prodEquiv
    (pmB2_clsExp_img_excl A K)))) (sm_trans (pmB2_exp_sum A hK)
      (pmB2_sm_clsExp (sm_refl A) (pmB2_sigma_sm_sum hK))))

/-- ✱116·656. \(\vdash :\exists !\alpha \,\,\text{exp}\,\,\beta \cap \alpha \,\,\text{exp}\,\,\gamma .\supset .\beta = \gamma \) -/
theorem pm116_656 {X Y : Type*} {A : Set X} {B G : Set Y} :
    (clsExp A B ∩ clsExp A G).Nonempty → B = G := pmB2_clsExp_disj

/-- ✱116·657. \(\vdash .(\alpha \,\,\text{exp}\,\,)ʻʻ\kappa \in \text{Cls}^{2} \text{excl} \quad[*116·656]\) -/
theorem pm116_657 {X Y : Type*} {A : Set X} {K : Set (Set Y)} :
    graph (clsExp A) ʻʻ K ∈ Cls2excl := pmB2_clsExp_img_excl A K

private theorem pmB2_downCls_eq {Y : Type*} (B : Set Y) : memRel ↧ B = opImg couple B B := by
  ext R; exact Iff.rfl

private theorem pmB2_exp_down {X Y : Type*} (A : Set X) (B : Set Y) :
    clsExp A (memRel ↧ B) =
      imgRel (relProdR ((coupleR B)˘ : Y → (Y → Set Y → Prop) → Prop)) ʻʻ clsExp A B := by
  rw [pmB2_downCls_eq]
  ext η
  constructor
  · intro hη
    obtain ⟨ξ, hξ, rfl⟩ := pmB2_Sz_onto (X := X) B hη
    exact ⟨ξ, hξ, rfl⟩
  · rintro ⟨ξ, hξ, hη⟩
    rw [show η = _ from hη]
    exact pmB2_Sz_mem B hξ

/-- ✱116·658. \(\vdash .\alpha \,\,\text{exp}\,\, (\in \unicode{x21A7}\beta ) = {\mid (\text{Cnv}ʻ\downarrow \beta )}_{\in}ʻʻ(\alpha \,\,\text{exp}\,\, \beta )\)

`∈↧β` is `memRel ↧ B`; `{|(Cnv'↓β)}_∈''(α exp β)` is
`imgRel (relProdR (coupleR B)˘) ʻʻ clsExp A B`. -/
theorem pm116_658 {X Y : Type*} {A : Set X} {B : Set Y} :
    clsExp A (memRel ↧ B) =
      imgRel (relProdR ((coupleR B)˘ : Y → (Y → Set Y → Prop) → Prop)) ʻʻ clsExp A B :=
  pmB2_exp_down A B

private theorem pmB2_T659 {X Y : Type*} {A : Set X} {K : Set (Set Y)} :
    (fun ν μ => ∃ B, (B ∈ K ∧ μ ∈ clsExp A B) ∧
        ν = relProdR ((coupleR B)˘ : Y → (Y → Set Y → Prop) → Prop) ʻʻ μ) ∈
      smsmbar (graph (clsExp A) ʻʻ (opL downCls memRel ʻʻ K)) (graph (clsExp A) ʻʻ K) := by
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro ν ν' μ ⟨⟨B, ⟨-, hμ⟩, rfl⟩, ⟨B', ⟨-, hμ'⟩, rfl⟩⟩
    rw [pmB2_clsExp_disj ⟨μ, hμ, hμ'⟩]
  · rintro ν μ μ' ⟨⟨B, ⟨-, hμ⟩, rfl⟩, ⟨B', ⟨-, hμ'⟩, e⟩⟩
    have s1 := (pmB2_mem_clsExp.1 hμ).2
    have s2 := (pmB2_mem_clsExp.1 hμ').2
    by_cases hne : μ.Nonempty
    · obtain ⟨Q, hQ⟩ := hne
      obtain ⟨x, y, -, rfl⟩ := pmB2_mem_clsTimes.1 (s1 hQ)
      have h1 : x ↓ (y ↓ B) ∈ pmB2_Sz X B ʻʻ μ := (pmB2_Sz_couple B s1 x y).2 hQ
      have h1' : x ↓ (y ↓ B) ∈ pmB2_Sz X B' ʻʻ μ' := e ▸ h1
      obtain ⟨x', y', -, e'⟩ := (pmB2_Sz_img B' s2 _).1 h1'
      have hBB : B = B' := (couple_eq_couple_iff.1 (couple_eq_couple_iff.1 e').2).2
      subst hBB
      exact pmB2_Sz_inj B s1 s2 e
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      subst hne
      have : pmB2_Sz X B' ʻʻ μ' = ∅ := by
        rw [← e]; ext P; simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨Q, hQ, -⟩; exact hQ
      ext Q
      simp only [Set.mem_empty_iff_false, false_iff]
      intro hQ
      obtain ⟨x, y, -, rfl⟩ := pmB2_mem_clsTimes.1 (s2 hQ)
      have h := (pmB2_Sz_couple B' s2 x y).2 hQ
      rw [this] at h; exact h
  · show sumCls (graph (clsExp A) ʻʻ K) = codom _
    ext μ
    constructor
    · rintro ⟨S, ⟨B, hB, hS⟩, hμ⟩
      have e : S = clsExp A B := hS
      rw [e] at hμ
      exact ⟨_, B, ⟨hB, hμ⟩, rfl⟩
    · rintro ⟨ν, B, ⟨hB, hμ⟩, -⟩
      exact ⟨clsExp A B, ⟨B, hB, rfl⟩, hμ⟩
  · ext S
    constructor
    · rintro ⟨Q, ⟨B, hB, hQ⟩, hS⟩
      have e1 : Q = memRel ↧ B := hQ
      have e2 : S = clsExp A Q := hS
      subst e1; subst e2
      refine ⟨clsExp A B, ⟨B, hB, rfl⟩, ?_⟩
      show clsExp A (memRel ↧ B) = _
      rw [pmB2_exp_down]
      ext ν
      constructor
      · rintro ⟨μ, hμ, hν⟩
        exact ⟨μ, hμ, B, ⟨hB, hμ⟩, hν⟩
      · rintro ⟨μ, hμ, B', ⟨-, hμ'⟩, hν⟩
        rw [pmB2_clsExp_disj ⟨μ, hμ, hμ'⟩]
        exact ⟨μ, hμ', hν⟩
    · rintro ⟨S', ⟨B, hB, hS'⟩, hS⟩
      have e1 : S' = clsExp A B := hS'
      subst e1
      refine ⟨memRel ↧ B, ⟨B, hB, rfl⟩, ?_⟩
      show S = clsExp A (memRel ↧ B)
      rw [show S = _ from hS, pmB2_exp_down]
      ext ν
      constructor
      · rintro ⟨μ, hμ, B', ⟨-, hμ'⟩, hν⟩
        rw [← pmB2_clsExp_disj ⟨μ, hμ, hμ'⟩] at hν
        exact ⟨μ, hμ, hν⟩
      · rintro ⟨μ, hμ, hν⟩
        exact ⟨μ, hμ, B, ⟨hB, hμ⟩, hν⟩

/-- ✱116·659. \[\begin{align}T = \hat{\nu} \hat{\mu}\{(\exists \beta ).\beta \in \kappa .\mu \in \alpha \,\,\text{exp}\,\,\beta .&\nu = \mid (\text{Cnv}ʻ\downarrow \beta )ʻʻ\mu\}.\supset .\\ &T\in (\alpha \,\,\text{exp}\,\,)ʻʻ\in \unicode{x21A7}ʻʻ\kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, (\alpha \,\,\text{exp}\,\,)ʻʻ\kappa\end{align}\]

`(α exp)''∈↧''κ` is `graph (clsExp A) ʻʻ (opL downCls memRel ʻʻ K)`; `|(Cnv'↓β)''μ` is
`relProdR (coupleR B)˘ ʻʻ μ`; the hypothesis is the equation defining `T`. -/
theorem pm116_659 {X Y : Type*} {A : Set X} {K : Set (Set Y)}
    {T : Set (X → (Y → Set Y → Prop) → Prop) → Set (X → Y → Prop) → Prop} :
    T = (fun ν μ => ∃ B, (B ∈ K ∧ μ ∈ clsExp A B) ∧
        ν = relProdR ((coupleR B)˘ : Y → (Y → Set Y → Prop) → Prop) ʻʻ μ) →
      T ∈ smsmbar (graph (clsExp A) ʻʻ (opL downCls memRel ʻʻ K)) (graph (clsExp A) ʻʻ K) := by
  rintro rfl
  exact pmB2_T659

private theorem pmB2_down_excl {Y : Type*} (K : Set (Set Y)) : opL downCls memRel ʻʻ K ∈ Cls2excl := by
  refine pmB2_excl_iff.2 ?_
  rintro S S' R ⟨B, -, hS⟩ ⟨B', -, hS'⟩ hR hR'
  have e1 : S = memRel ↧ B := hS
  have e2 : S' = memRel ↧ B' := hS'
  subst e1; subst e2
  obtain ⟨y, -, h⟩ := hR
  obtain ⟨y', -, h'⟩ := hR'
  have e : y ↓ B = y' ↓ B' := (show R = _ from h).symm.trans h'
  rw [(couple_eq_couple_iff.1 e).2]

private theorem pmB2_exp_sigma {X Y : Type*} (A : Set X) (K : Set (Set Y)) :
    sm (prodK (graph (clsExp A) ʻʻ K)) (clsExp A (clsSigma K)) :=
  sm_trans (sm_symm (pmB2_smsm_sm (pm115_51 ⟨_, pmB2_T659⟩))) (pmB2_exp_sum A (pmB2_down_excl K))

/-- ✱116·66. \(\vdash .\text{Prod}ʻ(\alpha \,\,\text{exp}\,)ʻʻ\kappa \text{ sm } \{\alpha \,\,\text{exp}\,\, (\Sigma ʻ\kappa )\}\)

`Σ'κ` is `clsSigma K`. -/
theorem pm116_66 {X Y : Type*} {A : Set X} {K : Set (Set Y)} :
    sm (prodK (graph (clsExp A) ʻʻ K)) (clsExp A (clsSigma K)) := pmB2_exp_sigma A K

/-- ✱116·661. \(\vdash .\Pi \text{Nc}ʻ(\alpha \,\,\text{exp}\,\,)ʻʻ\kappa = (\text{Nc}ʻ\alpha )^{\Sigma \text{Nc}ʻ\kappa } \quad[*116·66·657.*115·12.*112·101]\)

`ΣNc'κ` in the exponent is `N₀c'Σ'κ`, as in ✱116·655.

**Status.** proved (reading): `ΣNc'κ` in the exponent is read `N₀c'Σ'κ` (✱112·02 with the
normal adjustment ✱116·04), and `Nc'α` is `N₀c'α` (✱116·03). -/
theorem pm116_661 {X Y T : Type*} {A : Set X} {K : Set (Set Y)} :
    piNc T (graph (clsExp A) ʻʻ K) = (n₀c A ^ᶜ n₀c (clsSigma K) : Set (Set T)) := by
  rw [pmB2_n₀c_exp]
  exact nc_eq_nc_of_sm (sm_trans (sm_symm (pmB2_sm_of_equiv (pmB2_prodEquiv
    (pmB2_clsExp_img_excl A K)))) (pmB2_exp_sigma A K))

/-- ✱116·67. \(\vdash \colon\ldotp \rho = \hat{\lambda} \{(\exists \alpha ).\alpha \in \kappa .\lambda = \alpha \downarrow ʻʻ\gamma\}.\supset :\kappa \in \text{Cls}^{2} \text{excl}.\supset .\rho \in \text{Cls}^{3}\,\text{arithm}\)

The e-text prints `α↓''γ` for `α↓,,''γ` (the demonstration uses `α↓,,''γ`). `ρ = λ̂{…}` is an
equation (the hypothesis).

**Status.** proved (reading): transcription error: `α↓''γ` is read `α↓,,''γ`. -/
theorem pm116_67 {X Z : Type*} {K : Set (Set X)} {G : Set Z}
    {ρ : Set (Set (Set (X → Z → Prop)))} :
    ρ = {L | ∃ A, A ∈ K ∧ L = coupleImg A ʻʻ G} → (K ∈ Cls2excl → ρ ∈ Cls3arithm) := by
  rintro rfl hK
  refine ⟨pmB2_excl_iff.2 ?_, pmB2_excl_iff.2 ?_⟩
  · rintro L L' S ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩ hS hS'
    obtain ⟨z, -, hz⟩ := hS
    obtain ⟨w, -, hw⟩ := hS'
    have e : opImg couple A z = opImg couple B w := (show S = _ from hz).symm.trans hw
    by_cases hA' : A.Nonempty
    · obtain ⟨x, hx⟩ := hA'
      have : x ↓ z ∈ opImg couple B w := e ▸ ⟨x, hx, rfl⟩
      obtain ⟨x', hx', e'⟩ := this
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e'
      rw [pmB2_excl_iff.1 hK A B x hA hB hx hx']
    · rw [Set.not_nonempty_iff_eq_empty] at hA'
      subst hA'
      have hB' : B = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
        have : y ↓ w ∈ opImg couple (∅ : Set X) z := e ▸ ⟨y, hy, rfl⟩
        obtain ⟨x, hx, -⟩ := this
        exact hx
      rw [hB']
  · rintro S S' R ⟨L, ⟨A, hA, rfl⟩, hS⟩ ⟨L', ⟨B, hB, rfl⟩, hS'⟩ hR hR'
    obtain ⟨z, -, hz⟩ := hS
    obtain ⟨w, -, hw⟩ := hS'
    have e1 : S = opImg couple A z := hz
    have e2 : S' = opImg couple B w := hw
    subst e1; subst e2
    obtain ⟨x, hx, hRx⟩ := hR
    obtain ⟨x', hx', hRx'⟩ := hR'
    have e : x ↓ z = x' ↓ w := (show R = _ from hRx).symm.trans hRx'
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    rw [pmB2_excl_iff.1 hK A B x hA hB hx hx']

private theorem pmB2_s671 {X Z : Type*} {K : Set (Set X)} {G : Set Z} :
    sumCls {L | ∃ A, A ∈ K ∧ L = coupleImg A ʻʻ G} =
      sumCls {μ | ∃ z, z ∈ G ∧ μ = coupleR z ʻʻʻ K} := by
  ext S
  constructor
  · rintro ⟨L, ⟨A, hA, rfl⟩, z, hz, hS⟩
    exact ⟨_, ⟨z, hz, rfl⟩, A, hA, hS⟩
  · rintro ⟨μ, ⟨z, hz, rfl⟩, A, hA, hS⟩
    exact ⟨_, ⟨A, hA, rfl⟩, z, hz, hS⟩

/-- ✱116·671. \(\vdash \colon\ldotp \sigma = \hat{\mu} \{(\exists z) . z \in \gamma . \mu = \downarrow zʻʻʻ\kappa\} . \supset : \text{Hp} *116·67 . \supset . sʻ\rho = sʻ\sigma\)

`↓z'''κ` is `coupleR z ʻʻʻ K`; the hypotheses are the equations defining `σ` and (Hp ✱116·67)
`ρ`. -/
theorem pm116_671 {X Z : Type*} {K : Set (Set X)} {G : Set Z}
    {ρ σ : Set (Set (Set (X → Z → Prop)))} :
    σ = {μ | ∃ z, z ∈ G ∧ μ = coupleR z ʻʻʻ K} →
      (ρ = {L | ∃ A, A ∈ K ∧ L = coupleImg A ʻʻ G} → sumCls ρ = sumCls σ) := by
  rintro rfl rfl
  exact pmB2_s671

private theorem pmB2_sigma_excl {X Z : Type*} {K : Set (Set X)} {G : Set Z} (hΛ : (Λ : Set X) ∉ K) :
    {μ | ∃ z, z ∈ G ∧ μ = coupleR z ʻʻʻ K} ∈ Cls2excl := by
  refine pmB2_excl_iff.2 ?_
  rintro μ μ' S ⟨z, -, rfl⟩ ⟨w, -, rfl⟩ hS hS'
  obtain ⟨A, hA, hSA⟩ := hS
  obtain ⟨B, -, hSB⟩ := hS'
  have e : coupleR z ʻʻ A = coupleR w ʻʻ B := (show S = _ from hSA).symm.trans hSB
  have hA' : A.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl; exact hΛ (by rw [Null_eq_empty]; exact hA)
  obtain ⟨x, hx⟩ := hA'
  have : x ↓ z ∈ coupleR w ʻʻ B := e ▸ ⟨x, hx, rfl⟩
  obtain ⟨x', -, e'⟩ := this
  have e'' : x ↓ z = x' ↓ w := e'
  rw [(couple_eq_couple_iff.1 e'').2]

/-- ✱116·672. \(\vdash : \text{Hp} *116·671 . \kappa \in \text{Cls}^{2} \text{excl} . \Lambda {\sim} \in \kappa . \supset . \sigma \in \text{Cls}^{2} \text{excl}\)

"Hp ✱116·671" is the conjunction of the equations defining `σ` and `ρ`. -/
theorem pm116_672 {X Z : Type*} {K : Set (Set X)} {G : Set Z}
    {ρ σ : Set (Set (Set (X → Z → Prop)))} :
    ((σ = {μ | ∃ z, z ∈ G ∧ μ = coupleR z ʻʻʻ K} ∧
        ρ = {L | ∃ A, A ∈ K ∧ L = coupleImg A ʻʻ G}) ∧ K ∈ Cls2excl) ∧ (Λ : Set X) ∉ K →
      σ ∈ Cls2excl := by
  rintro ⟨⟨⟨rfl, -⟩, -⟩, hΛ⟩
  exact pmB2_sigma_excl hΛ

/-- ✱116·673. \(\vdash : \text{Hp} *116·672 . \supset . {\in}_{\Delta}ʻ(\,\,\text{exp}\,\, \gamma )ʻʻ\kappa \text{ sm } {\in}_{\Delta}ʻ{\in}_{\Delta}ʻʻ\sigma\)

`(exp γ)''κ` is `graph (fun B => clsExp B G) ʻʻ K` (the relation of `α exp γ` to `α`). -/
theorem pm116_673 {X Z : Type*} {K : Set (Set X)} {G : Set Z}
    {ρ σ : Set (Set (Set (X → Z → Prop)))} :
    ((σ = {μ | ∃ z, z ∈ G ∧ μ = coupleR z ʻʻʻ K} ∧
        ρ = {L | ∃ A, A ∈ K ∧ L = coupleImg A ʻʻ G}) ∧ K ∈ Cls2excl) ∧ (Λ : Set X) ∉ K →
      sm (sel memRel (graph (fun B => clsExp B G) ʻʻ K)) (sel memRel (selRel memRel ʻʻ σ)) := by
  rintro ⟨⟨⟨rfl, rfl⟩, hK⟩, hΛ⟩
  have h3 := pm116_67 (G := G) rfl hK
  have hP : graph (fun B => clsExp B G) ʻʻ K =
      ProdK ʻʻ {L | ∃ A, A ∈ K ∧ L = coupleImg A ʻʻ G} := by
    ext S
    constructor
    · rintro ⟨B, hB, hS⟩
      exact ⟨_, ⟨B, hB, rfl⟩, hS⟩
    · rintro ⟨L, ⟨B, hB, rfl⟩, hS⟩
      exact ⟨B, hB, hS⟩
  rw [hP]
  refine sm_trans (pm115_33 h3) ?_
  rw [pmB2_s671]
  exact sm_symm (pmB2_sel_sel_excl (pmB2_sigma_excl hΛ))

/-- The relation `(↓z) ‖ Cnv'(↓z)_∈` of ✱116·674. -/
private abbrev pmB2_Nz {X Z : Type*} (z : Z) :
    ((X → Z → Prop) → Set (X → Z → Prop) → Prop) → (X → Set X → Prop) → Prop :=
  coupleR z ∥ (imgRel (coupleR z))˘

private theorem pmB2_zimg_inj {X Z : Type*} (z : Z) {A A' : Set X} (e : coupleR z ʻʻ A = coupleR z ʻʻ A') :
    A = A' := by
  rw [pmB2_coupleR_img, pmB2_coupleR_img] at e
  exact (Set.image_injective.2 (pmB2_coupleR_inj z)) e

private theorem pmB2_Nz_apply {X Z : Type*} (z : Z) (P : (X → Z → Prop) → Set (X → Z → Prop) → Prop)
    (Q : X → Set X → Prop) :
    pmB2_Nz z P Q ↔ ∀ u Y, P u Y ↔ ∃ x A, Q x A ∧ u = x ↓ z ∧ Y = coupleR z ʻʻ A := by
  rw [pmB2_Nz, dpar_iff]
  constructor
  · rintro rfl u Y
    constructor
    · rintro ⟨x, hu, A, hQ, hY⟩
      exact ⟨x, A, hQ, hu, hY⟩
    · rintro ⟨x, A, hQ, hu, hY⟩
      exact ⟨x, hu, A, hQ, hY⟩
  · intro h
    funext u Y
    apply propext
    rw [h]
    constructor
    · rintro ⟨x, A, hQ, hu, hY⟩
      exact ⟨x, hu, A, hQ, hY⟩
    · rintro ⟨x, hu, A, hQ, hY⟩
      exact ⟨x, A, hQ, hu, hY⟩

private theorem pmB2_Nz_ex {X Z : Type*} (z : Z) (Q : X → Set X → Prop) :
    ∃ P, pmB2_Nz z P Q := ⟨_, (dpar_iff _ _ _ _).2 rfl⟩

private theorem pmB2_Nz_one_one {X Z : Type*} (z : Z) :
    (pmB2_Nz z : ((X → Z → Prop) → Set (X → Z → Prop) → Prop) → (X → Set X → Prop) → Prop) ∈
      arrow one one := by
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro P P' Q ⟨h, h'⟩
    rw [pmB2_Nz, dpar_iff] at h h'
    rw [h, h']
  · rintro P Q Q' ⟨h, h'⟩
    rw [pmB2_Nz_apply] at h h'
    funext x A
    apply propext
    constructor
    · intro hQ
      obtain ⟨x', A', hQ', e1, e2⟩ := (h' (x ↓ z) (coupleR z ʻʻ A)).1 ((h _ _).2 ⟨x, A, hQ, rfl, rfl⟩)
      rw [(couple_eq_couple_iff.1 e1).1, pmB2_zimg_inj z e2]; exact hQ'
    · intro hQ
      obtain ⟨x', A', hQ', e1, e2⟩ := (h (x ↓ z) (coupleR z ʻʻ A)).1 ((h' _ _).2 ⟨x, A, hQ, rfl, rfl⟩)
      rw [(couple_eq_couple_iff.1 e1).1, pmB2_zimg_inj z e2]; exact hQ'

private theorem pmB2_Nz_dom {X Z : Type*} (z : Z) (K : Set (Set X)) :
    dom ((pmB2_Nz z : ((X → Z → Prop) → Set (X → Z → Prop) → Prop) → (X → Set X → Prop) → Prop) ↾
      sel memRel K) = sel memRel (coupleR z ʻʻʻ K) := by
  ext P
  constructor
  · rintro ⟨Q, h, hQ⟩
    rw [pmB2_Nz_apply] at h
    obtain ⟨q1, q2, q3⟩ := pmB2_mem_sel.1 hQ
    refine pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩
    · rintro u u' Y ⟨hu, hu'⟩
      obtain ⟨x, A, hQA, rfl, rfl⟩ := (h _ _).1 hu
      obtain ⟨x', A', hQA', rfl, e⟩ := (h _ _).1 hu'
      have e' := pmB2_zimg_inj z e
      subst e'
      rw [q1 x x' A ⟨hQA, hQA'⟩]
    · rintro u Y hu
      obtain ⟨x, A, hQA, rfl, rfl⟩ := (h _ _).1 hu
      exact ⟨x, q2 x A hQA, rfl⟩
    · ext Y
      constructor
      · rintro ⟨u, hu⟩
        obtain ⟨x, A, hQA, -, rfl⟩ := (h _ _).1 hu
        exact ⟨A, pmB2_sel_codom hQ hQA, rfl⟩
      · rintro ⟨A, hA, hY⟩
        have hY' : Y = coupleR z ʻʻ A := hY
        obtain ⟨x, hx⟩ := pmB2_sel_ex hQ hA
        exact ⟨x ↓ z, (h _ _).2 ⟨x, A, hx, rfl, hY'⟩⟩
  · intro hP
    obtain ⟨p1, p2, p3⟩ := pmB2_mem_sel.1 hP
    refine ⟨fun x A => A ∈ K ∧ P (x ↓ z) (coupleR z ʻʻ A), ?_, pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩⟩
    · rw [pmB2_Nz_apply]
      intro u Y
      constructor
      · intro hu
        obtain ⟨A, hA, hY⟩ := pmB2_sel_codom hP hu
        have hY' : Y = coupleR z ʻʻ A := hY
        subst hY'
        obtain ⟨x, -, hx⟩ := p2 u _ hu
        have hx' : u = x ↓ z := hx
        subst hx'
        exact ⟨x, A, ⟨hA, hu⟩, rfl, rfl⟩
      · rintro ⟨x, A, ⟨-, h⟩, rfl, rfl⟩; exact h
    · rintro x x' A ⟨⟨-, h⟩, ⟨-, h'⟩⟩
      exact (couple_eq_couple_iff.1 (p1 _ _ _ ⟨h, h'⟩)).1
    · rintro x A ⟨-, h⟩
      obtain ⟨x', hx', e⟩ := p2 _ _ h
      have e' : x ↓ z = x' ↓ z := e
      rw [(couple_eq_couple_iff.1 e').1]; exact hx'
    · ext A
      constructor
      · rintro ⟨x, hA, -⟩; exact hA
      · intro hA
        obtain ⟨u, hu⟩ := pmB2_sel_ex hP (⟨A, hA, rfl⟩ : coupleR z ʻʻ A ∈ coupleR z ʻʻʻ K)
        obtain ⟨x, -, hx⟩ := p2 u _ hu
        have hx' : u = x ↓ z := hx
        subst hx'
        exact ⟨x, hA, hu⟩

private theorem pmB2_M674_desc {X Z : Type*} {z : Z}
    (ψ : (((X → Z → Prop) → Set (X → Z → Prop) → Prop) → (X → Set X → Prop) → Prop) → Prop) :
    Desc (fun R z => R = pmB2_Nz z) z ψ ↔ ψ (pmB2_Nz z) :=
  TheIs_iff_of_unique fun _ => Iff.rfl

/-- ✱116·674. \[\begin{align}\vdash \colon\ldotp &M = \hat{R} \hat{z} \{R = (\downarrow z) \parallel \text{Cnv}ʻ(\downarrow z)_{\in }\} . \supset :\\ &(z) . Mʻz \in 1 \rightarrow 1 . \text{D}ʻ(Mʻz) \upharpoonright {\in}_{\Delta}ʻ\kappa = {\in}_{\Delta}ʻ \downarrow zʻʻʻ\kappa\end{align}\]

`M'z` is `(↓z) ‖ Cnv'(↓z)_∈`, i.e. `coupleR z ∥ (imgRel (coupleR z))˘`; `D'(M'z) ↾ ∈_Δ'κ` is
read `D'{(M'z) ↾ ∈_Δ'κ}`, as the demonstration has it. -/
theorem pm116_674 {X Z : Type*} {K : Set (Set X)}
    {M : (((X → Z → Prop) → Set (X → Z → Prop) → Prop) → (X → Set X → Prop) → Prop) → Z → Prop} :
    M = (fun R z => R = coupleR z ∥ (imgRel (coupleR z))˘) →
      ∀ z, Desc M z (fun R => R ∈ arrow one one) ∧
        Desc M z (fun R => dom (R ↾ sel memRel K) = sel memRel (coupleR z ʻʻʻ K)) := by
  rintro rfl z
  rw [show (fun (R : ((X → Z → Prop) → Set (X → Z → Prop) → Prop) → (X → Set X → Prop) → Prop)
      (z : Z) => R = coupleR z ∥ (imgRel (coupleR z))˘) = (fun R z => R = pmB2_Nz z) from rfl,
    pmB2_M674_desc, pmB2_M674_desc]
  exact ⟨pmB2_Nz_one_one z, pmB2_Nz_dom z K⟩

/-- ✱116·675. \(\vdash \colon\ldotp \text{Hp} *116·674 . \exists ! sʻ\kappa . \supset : \exists ! (Mʻw)ʻʻ{\in}_{\Delta}ʻ\kappa \cap (Mʻ\nu )ʻʻ{\in}_{\Delta}ʻ\kappa . \supset . w = v\)

(This proposition is printed in the e-text but is missing from `data/principia.json`, where it
stands inside the text after ✱116·674.) "Hp ✱116·674" is the equation defining `M`; `w`, `v` are
real variables; `∃!(M'w)''∈_Δ'κ ∩ (M'v)''∈_Δ'κ` has two descriptions, the first with the larger
scope. The e-text prints `M'ν` for `M'v` (the demonstration has `M'v`).

**Status.** proved (reading): transcription error: `M'ν` is read `M'v`. -/
theorem pm116_675 {X Z : Type*} {K : Set (Set X)} {w v : Z}
    {M : (((X → Z → Prop) → Set (X → Z → Prop) → Prop) → (X → Set X → Prop) → Prop) → Z → Prop} :
    M = (fun R z => R = coupleR z ∥ (imgRel (coupleR z))˘) ∧ (sumCls K).Nonempty →
      (Desc M w (fun R => Desc M v (fun S =>
          ((R ʻʻ sel memRel K) ∩ (S ʻʻ sel memRel K)).Nonempty)) → w = v) := by
  rintro ⟨rfl, ⟨x₀, A₀, hA₀, -⟩⟩ h
  have hM : (fun (R : ((X → Z → Prop) → Set (X → Z → Prop) → Prop) → (X → Set X → Prop) → Prop)
      (z : Z) => R = coupleR z ∥ (imgRel (coupleR z))˘) = (fun R z => R = pmB2_Nz z) := rfl
  rw [hM, pmB2_M674_desc, pmB2_M674_desc] at h
  obtain ⟨P, ⟨Q, hQ, hP⟩, ⟨Q', -, hP'⟩⟩ := h
  rw [pmB2_Nz_apply] at hP hP'
  obtain ⟨x, hx⟩ := pmB2_sel_ex hQ hA₀
  obtain ⟨x', A', -, e1, -⟩ := (hP' _ _).1 ((hP _ _).2 ⟨x, A₀, hx, rfl, rfl⟩)
  exact (couple_eq_couple_iff.1 e1).2

/-- ✱116·676. \[\begin{align}\vdash : \text{Hp} *116·672·675 . \supset . \text{Prod}ʻ&\text{D}ʻʻ\upharpoonright ({\in}_{\Delta}ʻ\kappa )ʻʻMʻʻ\gamma \text{ sm } ({\in}_{\Delta}ʻ\kappa ) \,\,\text{exp}\,\, \gamma .\\ &\text{D}ʻʻ \upharpoonright ({\in}_{\Delta}ʻ\kappa )ʻʻMʻʻ\gamma = {\in}_{\Delta}ʻʻ\sigma\end{align}\]

"Hp ✱116·672·675" is the hypothesis of ✱116·672 together with that of ✱116·675 (the equation
defining `M` of ✱116·674 and `∃!s'κ`); `D''↾(∈_Δ'κ)''M''γ` is
`D ʻʻ (opR cres (sel memRel K) ʻʻ (M ʻʻ G))`. -/
theorem pm116_676 {X Z : Type*} {K : Set (Set X)} {G : Set Z}
    {ρ σ : Set (Set (Set (X → Z → Prop)))}
    {M : (((X → Z → Prop) → Set (X → Z → Prop) → Prop) → (X → Set X → Prop) → Prop) → Z → Prop} :
    (((σ = {μ | ∃ z, z ∈ G ∧ μ = coupleR z ʻʻʻ K} ∧
        ρ = {L | ∃ A, A ∈ K ∧ L = coupleImg A ʻʻ G}) ∧ K ∈ Cls2excl) ∧ (Λ : Set X) ∉ K) ∧
        (M = (fun R z => R = coupleR z ∥ (imgRel (coupleR z))˘) ∧ (sumCls K).Nonempty) →
      sm (prodK (D ʻʻ (opR cres (sel memRel K) ʻʻ (M ʻʻ G)))) (clsExp (sel memRel K) G) ∧
        D ʻʻ (opR cres (sel memRel K) ʻʻ (M ʻʻ G)) = selRel memRel ʻʻ σ := by
  rintro ⟨⟨⟨⟨rfl, -⟩, -⟩, -⟩, ⟨rfl, ⟨x₀, A₀, hA₀, hx₀⟩⟩⟩
  have hM : (fun (R : ((X → Z → Prop) → Set (X → Z → Prop) → Prop) → (X → Set X → Prop) → Prop)
      (z : Z) => R = coupleR z ∥ (imgRel (coupleR z))˘) = (fun R z => R = pmB2_Nz z) := rfl
  rw [hM]
  refine ⟨pm116_45 ⟨fun z => ?_, fun w v ⟨_, h⟩ => ?_⟩, ?_⟩
  · rw [pmB2_M674_desc, pmB2_M674_desc, V_eq_univ]
    refine ⟨pmB2_Nz_one_one z, Set.eq_univ_of_forall fun Q => ?_⟩
    obtain ⟨P, hP⟩ := pmB2_Nz_ex z Q
    exact ⟨P, hP⟩
  · rw [pmB2_M674_desc, pmB2_M674_desc] at h
    obtain ⟨P, ⟨Q, hQ, hP⟩, ⟨Q', hQ', hP'⟩⟩ := h
    rw [pmB2_Nz_apply] at hP hP'
    obtain ⟨x, hx⟩ := pmB2_sel_ex hQ hA₀
    obtain ⟨x', A', -, e1, -⟩ := (hP' _ _).1 ((hP _ _).2 ⟨x, A₀, hx, rfl, rfl⟩)
    exact (couple_eq_couple_iff.1 e1).2
  · ext S
    constructor
    · rintro ⟨R, ⟨R', ⟨z, hz, rfl⟩, hR⟩, hS⟩
      have e1 : R = pmB2_Nz z ↾ sel memRel K := hR
      have e2 : S = dom R := hS
      subst e1; subst e2
      exact ⟨_, ⟨z, hz, rfl⟩, (pmB2_Nz_dom z K)⟩
    · rintro ⟨μ, ⟨z, hz, rfl⟩, hS⟩
      have e : S = sel memRel (coupleR z ʻʻʻ K) := hS
      subst e
      exact ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, (pmB2_Nz_dom z K).symm⟩

/-- ✱116·68. \[\begin{align}\vdash : \kappa \in \text{Cls}^{2} \text{excl} . \supset . {\in}_{\Delta}ʻ(\text{exp}\,\, \gamma )ʻʻ\kappa \text{ sm } &({\in}_{\Delta}ʻ\kappa ) \,\,\text{exp}\,\, \gamma .\\ &\Pi \text{Nc}ʻ(\text{exp}\,\, \gamma )ʻʻ\kappa = (\Pi \text{Nc}ʻ\kappa )^{\text{Nc}ʻ\gamma }\end{align}\]

`(exp γ)''κ` is `graph (fun B => clsExp B G) ʻʻ K`; `ΠNc'κ` in the base is read through its Df
✱114·01 as `Nc'∈_Δ'κ`, normally adjusted (✱116·03) to `N₀c'∈_Δ'κ`; `Nc'γ` is `N₀c'γ`
(✱116·04); the equation is in a free type `T`.

**Status.** proved (reading): `ΠNc'κ` as an argument of `^` is read `N₀c'∈_Δ'κ` (✱114·01 with
the normal adjustment ✱116·03). -/
theorem pm116_68 {X Z T : Type*} {K : Set (Set X)} {G : Set Z} :
    K ∈ Cls2excl →
      sm (sel memRel (graph (fun B => clsExp B G) ʻʻ K)) (clsExp (sel memRel K) G) ∧
        piNc T (graph (fun B => clsExp B G) ʻʻ K) =
          (n₀c (sel memRel K) ^ᶜ n₀c G : Set (Set T)) := by
  intro hK
  have key : sm (sel memRel (graph (fun B => clsExp B G) ʻʻ K)) (clsExp (sel memRel K) G) := by
    rw [pmB2_img_graph]
    by_cases hG : G.Nonempty
    · by_cases h0 : (∅ : Set X) ∈ K
      · refine pmB2_sm_empty (pmB2_sel_empty_of ⟨∅, h0, ?_⟩) ?_
        · show clsExp (∅ : Set X) G = ∅
          rw [← Null_eq_empty (α := X), pm116_182 hG, Null_eq_empty]
        · rw [pmB2_sel_empty_of h0, ← Null_eq_empty (α := X → Set X → Prop), pm116_182 hG,
            Null_eq_empty]
      · have hinj : Set.InjOn (fun B => clsExp B G) K := by
          intro B hB B' hB' e
          obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 (fun h => h0 (h ▸ hB))
          have e' : clsExp B G = clsExp B' G := e
          have h1 : coupleL b ʻʻ G ∈ clsExp B' G := by rw [← e']; exact pm116_152 hb
          obtain ⟨g, hg⟩ := hG
          have h2 : b ↓ g ∈ coupleL b ʻʻ G := ⟨g, hg, rfl⟩
          have hb' := (couple_mem_clsTimes.1 ((pmB2_mem_clsExp.1 h1).2 h2)).1
          exact pmB2_excl_iff.1 hK B B' b hB hB' hb hb'
        exact pmB2_sm_of_equiv ((pmB2_selE _).trans ((pmB2_piImage _ K hinj
          (fun S => ↥(S : Set (Set (X → Z → Prop))))).trans ((Equiv.piCongrRight
            fun B : ↥K => pmB2_clsExpEquiv (B : Set X) G).trans ((Equiv.piComm _).trans
              ((Equiv.arrowCongr (Equiv.refl _) (pmB2_selE K).symm).trans
                (pmB2_clsExpEquiv (sel memRel K) G).symm)))))
    · rw [Set.not_nonempty_iff_eq_empty] at hG
      subst hG
      have hE1 : ∀ B : Set X, clsExp B (∅ : Set Z) = {∅} := fun B => by
        rw [← Null_eq_empty (α := Z), pm116_181, Null_eq_empty, unitCls_eq_singleton]
      have hE2 : clsExp (sel memRel K) (∅ : Set Z) = {∅} := by
        rw [← Null_eq_empty (α := Z), pm116_181, Null_eq_empty, unitCls_eq_singleton]
      have hS : ∀ S : ↥((fun B => clsExp B (∅ : Set Z)) '' K),
          (S : Set (Set (X → Z → Prop))) = {∅} := by
        rintro ⟨S, B, -, rfl⟩; exact hE1 B
      have : ∀ S : ↥((fun B => clsExp B (∅ : Set Z)) '' K),
          Unique ↥(S : Set (Set (X → Z → Prop))) := fun S => (Set.equivOfEq (hS S)).unique
      have hL : Unique ↥(sel memRel ((fun B => clsExp B (∅ : Set Z)) '' K)) :=
        (pmB2_selE _).unique
      have hR : Unique ↥(clsExp (sel memRel K) (∅ : Set Z)) := (Set.equivOfEq hE2).unique
      exact pmB2_sm_of_equiv (Equiv.ofUnique _ _)
  refine ⟨key, ?_⟩
  rw [pmB2_n₀c_exp]
  exact nc_eq_nc_of_sm key

private theorem pmB2_LV_ne {Z : Type*} [Nonempty Z] : (Λ : Set Z) ≠ V := by
  rw [Null_eq_empty, V_eq_univ]
  exact (Set.empty_ne_univ)

private theorem pmB2_LV_eq {Z : Type*} : (ι (Λ : Set Z) ∪ ι V) = ({Λ, V} : Set (Set Z)) := by
  rw [unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]

private theorem pmB2_two_val {X W T : Type*} (h2 : (two : Set (Set W)).Nonempty) (A : Set X) :
    ∃ a b : W, a ≠ b ∧
      ((two : Set (Set W)) ^ᶜ n₀c A : Set (Set T)) = nc T (clsExp ({a, b} : Set W) A) := by
  obtain ⟨a, b, hab, e2⟩ := pmB2_two_eq h2
  exact ⟨a, b, hab, by rw [e2, pmB2_n₀c_exp]⟩

/-- ✱116·7. \(\vdash . \text{Nc}ʻ\{(\iota ʻ\Lambda \cup \iota ʻ\text{V}) \uparrow \alpha \}_{\Delta }ʻ\alpha = 2^{\text{Nc}ʻ\alpha }\)

`ι'Λ ∪ ι'V` is a class of two classes of a type `Z` (PM: "solely as a known class consisting of
two terms"), which PM assumes non-empty (else `Λ = V`); `{…}_Δ'α` is `sel (cross … A) A`. The
argument `Nc'α` of `^` is `N₀c'α` (✱116·04) and the base `2` is in a type `W` in which it exists
(IIT); the equation is in a free type `T`.

**Status.** proved (reading): `[Nonempty Z]` (PM assumes every type has a member, Introduction,
Ch. I; in an empty type `ι'Λ ∪ ι'V` has one member); convention IIT for the constant `2`. -/
theorem pm116_7 {X Z W T : Type*} [Nonempty Z] {A : Set X} (h2 : (two : Set (Set W)).Nonempty) :
    nc T (sel (cross (ι (Λ : Set Z) ∪ ι V) A) A) = ((two : Set (Set W)) ^ᶜ n₀c A : Set (Set T)) := by
  obtain ⟨a, b, hab, e⟩ := pmB2_two_val (T := T) h2 A
  rw [e]
  apply nc_eq_nc_of_sm
  rw [pmB2_LV_eq]
  exact sm_trans (sm_symm pm116_15) (pmB2_sm_clsExp (pmB2_pair_sm hab pmB2_LV_ne) (sm_refl A))

private theorem pmB2_sel_LV {X Z : Type*} [Nonempty Z] {A : Set X} {R : Set Z → X → Prop}
    (hR : R ∈ sel (cross (ι (Λ : Set Z) ∪ ι V) A) A) (x : X) (hx : x ∈ A) :
    (R Λ x ∧ ¬R V x) ∨ (R V x ∧ ¬R Λ x) := by
  obtain ⟨h1, h2, h3⟩ := pmB2_mem_sel.1 hR
  obtain ⟨Y, hY⟩ : x ∈ codom R := h3 ▸ hx
  have hne := pmB2_LV_ne (Z := Z)
  rcases (h2 Y x hY).1 with e | e
  · have e' : Y = Λ := e
    subst e'
    exact Or.inl ⟨hY, fun h => hne (h1 _ _ _ ⟨hY, h⟩)⟩
  · have e' : Y = V := e
    subst e'
    exact Or.inr ⟨hY, fun h => hne (h1 _ _ _ ⟨h, hY⟩)⟩

/-- ✱116·71. \(\vdash : R \in \{(\iota ʻ\Lambda \cup \iota ʻ\text{V}) \uparrow \alpha\}_{\Delta }ʻ\alpha . \supset . \overleftarrow{R}ʻ\text{V} = \alpha - \overleftarrow{R}ʻ\Lambda \)

`R⃖'V` is `rels R V`; the type `Z` of `Λ`, `V` is non-empty, as in ✱116·7.

**Status.** proved (reading): `[Nonempty Z]` (PM assumes every type has a member; in an empty
type `Λ = V` and the proposition fails). -/
theorem pm116_71 {X Z : Type*} [Nonempty Z] {A : Set X} {R : Set Z → X → Prop} :
    R ∈ sel (cross (ι (Λ : Set Z) ∪ ι V) A) A → rels R V = A \ rels R Λ := by
  intro hR
  obtain ⟨-, h2, h3⟩ := pmB2_mem_sel.1 hR
  ext x
  constructor
  · intro hx
    have hxA : x ∈ A := h3 ▸ ⟨V, hx⟩
    rcases pmB2_sel_LV hR x hxA with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd hx h
    · exact ⟨hxA, h⟩
  · rintro ⟨hxA, hx⟩
    rcases pmB2_sel_LV hR x hxA with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hx
    · exact h

/-- ✱116·711. \(\vdash : R, S \in \{(\iota ʻ\Lambda \cup \iota ʻ\text{V}) \uparrow \alpha\}_{\Delta }ʻ\alpha . \overleftarrow{R}ʻ\Lambda = \overleftarrow{S}ʻ\Lambda . \supset . R = S\)

(No hypothesis on the type `Z` is needed: in an empty type `ι'Λ ∪ ι'V` has one member, and the
selection is unique.) -/
theorem pm116_711 {X Z : Type*} {A : Set X} {R S : Set Z → X → Prop} :
    (R ∈ sel (cross (ι (Λ : Set Z) ∪ ι V) A) A ∧ S ∈ sel (cross (ι (Λ : Set Z) ∪ ι V) A) A) ∧
        rels R Λ = rels S Λ → R = S := by
  rintro ⟨⟨hR, hS⟩, e⟩
  have key : ∀ R S : Set Z → X → Prop, R ∈ sel (cross (ι (Λ : Set Z) ∪ ι V) A) A →
      S ∈ sel (cross (ι (Λ : Set Z) ∪ ι V) A) A → rels R Λ = rels S Λ →
        ∀ Y x, R Y x → S Y x := by
    intro R S hR hS e Y x h
    obtain ⟨r1, r2, -⟩ := pmB2_mem_sel.1 hR
    obtain ⟨-, s2, s3⟩ := pmB2_mem_sel.1 hS
    have hxA : x ∈ A := (r2 Y x h).2
    obtain ⟨Y', hY'⟩ : x ∈ codom S := s3 ▸ hxA
    rcases (r2 Y x h).1 with hY | hY
    · have hY0 : Y = Λ := hY
      subst hY0
      exact (show x ∈ rels S Λ from e ▸ h)
    · have hYV : Y = V := hY
      subst hYV
      rcases (s2 Y' x hY').1 with h' | h'
      · have h0 : Y' = Λ := h'
        subst h0
        have hRΛ : R Λ x := (show x ∈ rels R Λ from e.symm ▸ hY')
        have hΛV : (Λ : Set Z) = V := r1 _ _ _ ⟨hRΛ, h⟩
        rw [← hΛV]
        exact hY'
      · have h0 : Y' = V := h'
        subst h0
        exact hY'
  funext Y x
  exact propext ⟨key R S hR hS e Y x, key S R hS hR e.symm Y x⟩

/-- ✱116·712. \[\begin{align}&\vdash \colon\ldotp T = \hat{\mu} \hat{R} [R \in \{(\iota ʻ\Lambda \cup \iota ʻ\text{V}) \uparrow \alpha \}_{\Delta }ʻ\alpha . \mu = \overleftarrow{R}ʻ\Lambda ] . \supset :\\ &R \in \{(\iota ʻ\Lambda \cup \iota ʻ\text{V}) \uparrow \alpha\}_{\Delta }ʻ\alpha . \supset . TʻR = \overleftarrow{R}ʻ\Lambda :\text{ᗡ}ʻT = \{(\iota ʻ\Lambda \cup \iota ʻ\text{V}) \uparrow \alpha\}_{\Delta }ʻ\alpha\end{align}\]

`T'R` is the description `Desc T R …`; `R` in the second clause is a real variable. -/
theorem pm116_712 {X Z : Type*} {A : Set X} {R : Set Z → X → Prop}
    {T : Set X → (Set Z → X → Prop) → Prop} :
    T = (fun μ R => R ∈ sel (cross (ι (Λ : Set Z) ∪ ι V) A) A ∧ μ = rels R Λ) →
      (R ∈ sel (cross (ι (Λ : Set Z) ∪ ι V) A) A → Desc T R (fun μ => μ = rels R Λ)) ∧
        codom T = sel (cross (ι (Λ : Set Z) ∪ ι V) A) A := by
  rintro rfl
  refine ⟨fun hR => ⟨rels R Λ, fun μ => ⟨fun h => h.2, fun h => ⟨hR, h⟩⟩, rfl⟩, ?_⟩
  ext S
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

/-- ✱116·713. \(\vdash : \text{Hp} *116·712 . \supset . T \in 1 \rightarrow 1\)

"Hp ✱116·712" is the equation defining `T`. (No hypothesis on the type `Z` is needed, as in
✱116·711.) -/
theorem pm116_713 {X Z : Type*} {A : Set X}
    {T : Set X → (Set Z → X → Prop) → Prop} :
    T = (fun μ R => R ∈ sel (cross (ι (Λ : Set Z) ∪ ι V) A) A ∧ μ = rels R Λ) →
      T ∈ arrow one one := by
  rintro rfl
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro μ ν R ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
  · rintro μ R S ⟨⟨hR, e1⟩, ⟨hS, e2⟩⟩
    exact pm116_711 ⟨⟨hR, hS⟩, e1.symm.trans e2⟩

/-- ✱116·715. \(\vdash :\text{Hp}*116·712.\supset .\text{D}ʻT=\text{Cl}ʻ\alpha \)

**Status.** proved (reading): `[Nonempty Z]`, as ✱116·71. -/
theorem pm116_715 {X Z : Type*} [Nonempty Z] {A : Set X}
    {T : Set X → (Set Z → X → Prop) → Prop} :
    T = (fun μ R => R ∈ sel (cross (ι (Λ : Set Z) ∪ ι V) A) A ∧ μ = rels R Λ) →
      dom T = cl A := by
  rintro rfl
  ext μ
  constructor
  · rintro ⟨R, hR, rfl⟩
    intro x hx
    exact ((pmB2_mem_sel.1 hR).2.1 _ _ hx).2
  · intro hμ
    classical
    let R : Set Z → X → Prop := fun Y x => x ∈ A ∧ (Y = Λ ∧ x ∈ μ ∨ Y = V ∧ x ∉ μ)
    have hne := pmB2_LV_ne (Z := Z)
    refine ⟨R, pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩, ?_⟩
    · rintro Y Y' x ⟨⟨-, ⟨rfl, h1⟩ | ⟨rfl, h1⟩⟩, ⟨-, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩⟩
      · rfl
      · exact absurd h1 h2
      · exact absurd h2 h1
      · rfl
    · rintro Y x ⟨hx, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
      · exact ⟨Or.inl rfl, hx⟩
      · exact ⟨Or.inr rfl, hx⟩
    · ext x
      constructor
      · rintro ⟨Y, hx, -⟩; exact hx
      · intro hx
        by_cases h : x ∈ μ
        · exact ⟨Λ, hx, Or.inl ⟨rfl, h⟩⟩
        · exact ⟨V, hx, Or.inr ⟨rfl, h⟩⟩
    · ext x
      constructor
      · intro hx; exact ⟨hμ hx, Or.inl ⟨rfl, hx⟩⟩
      · rintro ⟨-, ⟨-, h⟩ | ⟨e, -⟩⟩
        · exact h
        · exact absurd e hne

private theorem pmB2_prop_univ : ({True, False} : Set Prop) = Set.univ :=
  Set.eq_univ_of_forall fun p => by
    by_cases h : p
    · exact Or.inl (eq_true h)
    · exact Or.inr (Set.mem_singleton_iff.2 (eq_false h))

/-- `Cl'α` is similar to `α exp 2` for any class `2` of two members. -/
private theorem pmB2_cl_sm_exp {X W : Type*} {a b : W} (hab : a ≠ b) (A : Set X) :
    sm (cl A) (clsExp ({a, b} : Set W) A) := by
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (pmB2_pair_sm (V := Prop) hab (x := True) (y := False)
    (by simp))
  let e' : (↥A → Prop) ≃ (↥A → ↥({a, b} : Set W)) :=
    Equiv.arrowCongr (Equiv.refl ↥A) (((Equiv.Set.univ Prop).symm.trans
      (Set.equivOfEq pmB2_prop_univ.symm)).trans e)
  exact pmB2_sm_of_equiv ((Equiv.Set.powerset A).trans (Set.memEquiv.trans
    (e'.trans (pmB2_clsExpEquiv _ A).symm)))

/-- ✱116·72. \(\vdash .\text{Nc}ʻ\text{Cl}ʻ\alpha =2^{\text{Nc}ʻ\alpha}\)

The argument `Nc'α` of `^` is `N₀c'α` and the base `2` is in a type `W` in which it exists.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV) for the constant `2`; the
equation is in a free type `T`. -/
theorem pm116_72 {X W T : Type*} {A : Set X} (h2 : (two : Set (Set W)).Nonempty) :
    nc T (cl A) = ((two : Set (Set W)) ^ᶜ n₀c A : Set (Set T)) := by
  obtain ⟨a, b, hab, e⟩ := pmB2_two_val (T := T) h2 A
  rw [e]
  exact nc_eq_nc_of_sm (pmB2_cl_sm_exp hab A)

/-- ✱116·8. \(\vdash .\text{Rl}ʻ(\rho \uparrow \sigma )=\dot{s} ʻʻ\text{Cl}ʻ(\sigma \times \rho )\)

`Rl'(ρ ↑ σ)` is `rl (cross ρ σ)`; `ṡ''Cl'(σ × ρ)` is `graph sumRel ʻʻ cl (σ ×ₐ ρ)`. -/
theorem pm116_8 {X Y : Type*} {ρ : Set X} {σ : Set Y} :
    rl (cross ρ σ) = graph sumRel ʻʻ cl (σ ×ₐ ρ) := by
  ext R
  constructor
  · intro hR
    have hsub : {P | ∃ x y, R x y ∧ P = x ↓ y} ⊆ σ ×ₐ ρ := by
      rintro P ⟨x, y, hxy, rfl⟩
      exact couple_mem_clsTimes.2 (hR x y hxy)
    refine ⟨_, hsub, ?_⟩
    show R = sumRel _
    funext x y
    rw [pmB2_sumRel_couples hsub]
    exact propext ⟨fun h => ⟨x, y, h, rfl⟩, fun ⟨x', y', h, e⟩ => by
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e; exact h⟩
  · rintro ⟨L, hL, hR⟩
    have hR' : R = sumRel L := hR
    subst hR'
    intro x y h
    rw [pmB2_sumRel_couples hL] at h
    exact couple_mem_clsTimes.1 (hL h)

/-- ✱116·81. \(\vdash .\dot{s} \upharpoonright \text{Cl}ʻ(\sigma \times \rho )\in 1\rightarrow 1\) -/
theorem pm116_81 {X Y : Type*} {ρ : Set X} {σ : Set Y} :
    graph sumRel ↾ cl (σ ×ₐ ρ) ∈ arrow one one := by
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro R R' L ⟨⟨h, -⟩, ⟨h', -⟩⟩
    exact (show R = sumRel L from h).trans (show R' = sumRel L from h').symm
  · rintro R L L' ⟨⟨h, hL⟩, ⟨h', hL'⟩⟩
    have e : sumRel L = sumRel L' := (show R = sumRel L from h).symm.trans h'
    ext P
    constructor
    · intro hP
      obtain ⟨x, y, -, rfl⟩ := pmB2_mem_clsTimes.1 (hL hP)
      rw [← pmB2_sumRel_couples hL', ← e, pmB2_sumRel_couples hL]; exact hP
    · intro hP
      obtain ⟨x, y, -, rfl⟩ := pmB2_mem_clsTimes.1 (hL' hP)
      rw [← pmB2_sumRel_couples hL, e, pmB2_sumRel_couples hL']; exact hP

/-- ✱116·82. \(\vdash .\text{Rl}ʻ(\rho \uparrow \sigma )\text{ sm } \text{Cl}ʻ(\sigma \times \rho ) \quad[*116·8·81]\) -/
theorem pm116_82 {X Y : Type*} {ρ : Set X} {σ : Set Y} :
    sm (rl (cross ρ σ)) (cl (σ ×ₐ ρ)) := by
  rw [pm116_8, pmB2_img_graph]
  refine sm_symm (pmB2_sm_of_equiv (Equiv.Set.imageOfInjOn _ _ ?_))
  intro L hL L' hL' e
  exact (mem_arrow_one_one.1 pm116_81).2 _ L L' ⟨⟨rfl, hL⟩, ⟨e, hL'⟩⟩

private theorem pmB2_sm_cl {X Y : Type*} {A : Set X} {B : Set Y} (h : sm A B) : sm (cl A) (cl B) := by
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
  exact pmB2_sm_of_equiv ((Equiv.Set.powerset A).trans ((Equiv.setCongr e).trans
    (Equiv.Set.powerset B).symm))

/-- ✱116·83. \(\vdash .\text{Nc}ʻ\text{Rl}ʻ(\rho \uparrow \sigma )=2^{\text{Nc}ʻ\rho \times _{c}\text{Nc}ʻ\sigma } \quad[*116·82·72 .*113·25]\)

The exponent `Nc'ρ ×_c Nc'σ` is an arithmetical formal number with its own adequate type `W'`
(IIT), whose arguments are `N₀c'ρ`, `N₀c'σ` (✱113·04·05); the base `2` is in a type `W` in which
it exists.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV) (`AdeqMul`, and `2`
existent in its type); the equation is in a free type `T`. -/
theorem pm116_83 {X Y W W' T : Type*} {ρ : Set X} {σ : Set Y} (h2 : (two : Set (Set W)).Nonempty)
    (h : AdeqMul W' (n₀c ρ) (n₀c σ)) :
    nc T (rl (cross ρ σ)) =
      ((two : Set (Set W)) ^ᶜ (n₀c ρ ×ᶜ n₀c σ : Set (Set W')) : Set (Set T)) := by
  obtain ⟨S, eS, sS⟩ := pmB2_nc_n₀c (pmB2_AdeqMul_nc h ρ σ)
  rw [pmB2_n₀c_mul, eS]
  obtain ⟨a, b, hab, e⟩ := pmB2_two_val (T := T) h2 S
  rw [e]
  apply nc_eq_nc_of_sm
  refine sm_trans pm116_82 (sm_trans (pmB2_sm_cl ?_) (pmB2_cl_sm_exp hab S))
  exact sm_trans (pmB2_sm_of_equiv ((pmB2_clsTimesEquiv ρ σ).trans ((Equiv.prodComm _ _).trans
    (pmB2_clsTimesEquiv σ ρ).symm))) (sm_symm sS)

/-- ✱116·9. \(\vdash :\text{Nc}ʻtʻx=\mu .\supset .\text{Nc}ʻt^{2}ʻx=2^\mu \quad[*116·72.*63·66]\)

`μ` is taken in the type of the classes of the type of `x` (where `Nc't'x` exists: in a type in
which `Nc't'x = Λ` the equation `Nc't²'x = 2^Λ = Λ` would fail); the base `2` is in a type in which
it exists (IIT).

**Status.** proved (reading): the real variable `μ` is taken in the type `t²'x` of `Nc't'x`'s
members; convention IIT for the constant `2`. -/
theorem pm116_9 {X W T : Type*} {x : X} {μ : Set (Set X)} (h2 : (two : Set (Set W)).Nonempty) :
    nc X (typ x) = μ → nc T (typ2 x) = ((two : Set (Set W)) ^ᶜ μ : Set (Set T)) := by
  rintro rfl
  rw [← n₀c_eq_nc, ← pm116_72 h2]
  simp only [typ2, typ_eq_univ]
  congr 1
  exact (Set.eq_univ_of_forall fun _ => Set.subset_univ _).symm

/-- ✱116·901. \(\vdash :\text{Nc}ʻt_{0}ʻ\alpha =\mu .\supset .\text{Nc}ʻtʻ\alpha =2^\mu \quad[*116·72.*63·65]\)

**Status.** proved (reading): `μ` is taken in the type of `t₀'α`'s classes, as in ✱116·9;
convention IIT for the constant `2`. -/
theorem pm116_901 {X W T : Type*} {A : Set X} {μ : Set (Set X)}
    (h2 : (two : Set (Set W)).Nonempty) :
    nc X (typ₀ A) = μ → nc T (typ A) = ((two : Set (Set W)) ^ᶜ μ : Set (Set T)) := by
  rintro rfl
  rw [← n₀c_eq_nc, ← pm116_72 h2, typ_eq_univ, typ₀_eq_univ]
  congr 1
  exact (Set.eq_univ_of_forall fun _ => Set.subset_univ _).symm

/-- ✱116·91. \(\vdash :\text{Nc}ʻt_{0}ʻ\alpha =\mu .\supset .\text{Nc}ʻt_{00}ʻ\alpha =2^{\mu ^{2}} \quad[*116·83.*64·5·11]\)

`μ^2` is the inner power, an arithmetical component with its own adequate type `W'`; each `2` is
in a type in which it exists (IIT); `μ` as in ✱116·9.

**Status.** proved (reading): `μ` is taken in the type of `t₀'α`'s classes, as in ✱116·9;
convention IIT (Prefatory Statement, IV) for the constants `2` and the component `μ^2`. -/
theorem pm116_91 {X W₁ W₂ W' T : Type*} {A : Set X} {μ : Set (Set X)}
    (h₁ : (two : Set (Set W₁)).Nonempty) (h₂ : (two : Set (Set W₂)).Nonempty)
    (h : AdeqExp W' μ (two : Set (Set W₂))) :
    nc X (typ₀ A) = μ →
      nc T (typ₀₀ A) =
        ((two : Set (Set W₁)) ^ᶜ (μ ^ᶜ (two : Set (Set W₂)) : Set (Set W')) : Set (Set T)) := by
  rintro rfl
  obtain ⟨c, d, hcd, e2⟩ := pmB2_two_eq h₂
  rw [← n₀c_eq_nc (typ₀ A), e2, pmB2_n₀c_exp]
  obtain ⟨S, eS, sS⟩ := pmB2_nc_n₀c (pmB2_AdeqExp_nc' h (typ₀ A) ({c, d} : Set W₂)
    ⟨c, Or.inl rfl⟩)
  rw [eS]
  obtain ⟨a, b, hab, e⟩ := pmB2_two_val (T := T) h₁ S
  rw [e, typ₀₀, typ_eq_univ]
  apply nc_eq_nc_of_sm
  refine sm_trans ?_ (sm_trans (sm_symm (pmB2_sm_cl sS)) (pmB2_cl_sm_exp hab S))
  obtain ⟨e₂⟩ := sm_iff_nonempty_equiv.1 (pmB2_pair_sm (V := Bool) hcd (x := true) (y := false)
    (by simp))
  have hB : ({true, false} : Set Bool) = Set.univ := Set.eq_univ_of_forall fun t => by
    cases t <;> simp
  let eB : Bool ≃ ↥({c, d} : Set W₂) :=
    ((Equiv.Set.univ Bool).symm.trans (Set.equivOfEq hB.symm)).trans e₂
  let eX : X ≃ ↥(typ₀ A) := (Equiv.Set.univ X).symm.trans (Set.equivOfEq (typ₀_eq_univ A).symm)
  let e' : X × X ≃ ↥(clsExp (typ₀ A) ({c, d} : Set W₂)) :=
    (Equiv.boolArrowEquivProd X).symm.trans ((Equiv.arrowCongr eB eX).trans
      (pmB2_clsExpEquiv _ _).symm)
  exact pmB2_sm_of_equiv ((Equiv.Set.univ _).trans ((Equiv.curry _ _ _).symm.trans
    ((Equiv.arrowCongr e' (Equiv.refl Prop)).trans (Set.memEquiv.symm.trans
      (Equiv.Set.powerset (clsExp (typ₀ A) ({c, d} : Set W₂))).symm))))

private theorem pmB2_exp2_equiv {X W : Type*} {c d : W} (hcd : c ≠ d) (B : Set X) :
    Nonempty (↥(clsExp ({c, d} : Set W) B) ≃ Set ↥B) := by
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (pmB2_cl_sm_exp hcd B)
  exact ⟨e.symm.trans (Equiv.Set.powerset B)⟩

private theorem pmB2_two_pow_val {X W W' : Type*} {B : Set X} (h2 : (two : Set (Set W)).Nonempty)
    (h : AdeqExp W' (two : Set (Set W)) (n₀c B)) :
    ∃ S : Set W', ((two : Set (Set W)) ^ᶜ n₀c B : Set (Set W')) = n₀c S ∧
      Nonempty (↥S ≃ Set ↥B) := by
  obtain ⟨c, d, hcd, e2⟩ := pmB2_two_eq h2
  have : Nonempty W := ⟨c⟩
  rw [e2] at h ⊢
  rw [pmB2_n₀c_exp]
  obtain ⟨S, eS, sS⟩ := pmB2_nc_n₀c (pmB2_AdeqExp_nc h ({c, d} : Set W) B)
  obtain ⟨f⟩ := sm_iff_nonempty_equiv.1 sS
  obtain ⟨g⟩ := pmB2_exp2_equiv hcd B
  exact ⟨S, eS, ⟨f.trans g⟩⟩

private theorem pmB2_two_pow_eq {Q T W W' : Type*} {S : Set W'} {U : Set Q} {P : Type*}
    (h2 : (two : Set (Set W)).Nonempty) (eS : ↥S ≃ P) (eU : ↥U ≃ Set P) :
    nc T U = ((two : Set (Set W)) ^ᶜ n₀c S : Set (Set T)) := by
  obtain ⟨a, b, hab, e⟩ := pmB2_two_val (T := T) h2 S
  rw [e]
  obtain ⟨g⟩ := pmB2_exp2_equiv hab S
  exact nc_eq_nc_of_sm (pmB2_sm_of_equiv (eU.trans ((Equiv.setCongr eS).symm.trans g.symm)))

/-- ✱116·92. \[\begin{align}&\vdash :\text{Nc}ʻt_{0}ʻ\alpha =\mu .\supset .\text{Nc}ʻt_{0}^{1}ʻ\alpha =2^{\mu \times _{c}2^\mu }.\text{Nc}ʻt^{11}ʻ\alpha =2^{2^\mu \times _{c}2^\mu }.\text{etc}.\\ &[*116·83.*64·16.*116·901]\end{align}\]

The chain "etc." is represented by its two printed members, a conjunction. Every constant `2`
is in a type in which it exists, and every arithmetical component (`2^μ`, `μ ×_c 2^μ`,
`2^μ ×_c 2^μ`) in an adequate type of its own (IIT); `μ` as in ✱116·9. The two equations are in
free types `T₁`, `T₂`.

**Status.** proved (reading): `μ` is taken in the type of `t₀'α`'s classes, as in ✱116·9;
convention IIT (Prefatory Statement, IV) for the constants `2` and for the arithmetical
components. -/
theorem pm116_92 {X W₁ W₂ W₃ W₄ W₅ W₆ W₇ W₈ W₉ W₁₀ T₁ T₂ : Type*} {A : Set X}
    {μ : Set (Set X)} (h₁ : (two : Set (Set W₁)).Nonempty) (h₃ : (two : Set (Set W₃)).Nonempty)
    (h₄ : AdeqExp W₄ (two : Set (Set W₃)) μ) (h₂ : AdeqMul W₂ μ (Λ : Set (Set W₄)))
    (h₅ : (two : Set (Set W₅)).Nonempty) (h₆ : (two : Set (Set W₆)).Nonempty)
    (h₇ : AdeqExp W₇ (two : Set (Set W₆)) μ) (h₈ : (two : Set (Set W₈)).Nonempty)
    (h₉ : AdeqExp W₉ (two : Set (Set W₈)) μ)
    (h₁₀ : AdeqMul W₁₀ (Λ : Set (Set W₇)) (Λ : Set (Set W₉))) :
    nc X (typ₀ A) = μ →
      nc T₁ (typ₀1 A) = ((two : Set (Set W₁)) ^ᶜ
          (μ ×ᶜ ((two : Set (Set W₃)) ^ᶜ μ : Set (Set W₄)) : Set (Set W₂)) : Set (Set T₁)) ∧
        nc T₂ (typ11 A) = ((two : Set (Set W₅)) ^ᶜ
          (((two : Set (Set W₆)) ^ᶜ μ : Set (Set W₇)) ×ᶜ
            ((two : Set (Set W₈)) ^ᶜ μ : Set (Set W₉)) : Set (Set W₁₀)) : Set (Set T₂)) := by
  rintro rfl
  rw [← n₀c_eq_nc] at *
  obtain ⟨S₄, e₄, f₄⟩ := pmB2_two_pow_val h₃ h₄
  obtain ⟨S₇, e₇, f₇⟩ := pmB2_two_pow_val h₆ h₇
  obtain ⟨S₉, e₉, f₉⟩ := pmB2_two_pow_val h₈ h₉
  obtain ⟨f₄⟩ := f₄
  obtain ⟨f₇⟩ := f₇
  obtain ⟨f₉⟩ := f₉
  rw [e₄, e₇, e₉, pmB2_n₀c_mul, pmB2_n₀c_mul]
  obtain ⟨S₂, e₂, s₂⟩ := pmB2_nc_n₀c (pmB2_AdeqMul_nc h₂ (typ₀ A) S₄)
  obtain ⟨S₁₀, e₁₀, s₁₀⟩ := pmB2_nc_n₀c (pmB2_AdeqMul_nc h₁₀ S₇ S₉)
  obtain ⟨g₂⟩ := sm_iff_nonempty_equiv.1 s₂
  obtain ⟨g₁₀⟩ := sm_iff_nonempty_equiv.1 s₁₀
  rw [e₂, e₁₀]
  have eX : ↥(typ₀ A) ≃ X := (Set.equivOfEq (typ₀_eq_univ A)).trans (Equiv.Set.univ X)
  constructor
  · refine pmB2_two_pow_eq h₁ (g₂.trans ((pmB2_clsTimesEquiv S₄ (typ₀ A)).trans
      (((f₄.trans (Equiv.setCongr eX)).prodCongr eX).trans (Equiv.prodComm _ _)))) ?_
    rw [typ₀1, typ_eq_univ]
    exact (Equiv.Set.univ _).trans ((Equiv.curry _ _ _).symm.trans Set.memEquiv.symm)
  · refine pmB2_two_pow_eq h₅ (g₁₀.trans ((pmB2_clsTimesEquiv S₉ S₇).trans
      (((f₉.trans (Equiv.setCongr eX)).prodCongr (f₇.trans (Equiv.setCongr eX))).trans
        (Equiv.prodComm _ _)))) ?_
    rw [typ11, typ_eq_univ]
    exact (Equiv.Set.univ _).trans ((Equiv.curry _ _ _).symm.trans Set.memEquiv.symm)

/-!
## [✱117] Greater and less

*(Vol. 2, p. 171)*

> *Summary of* *117.
>
> A cardinal \(\mu\) is said to be greater than another cardinal \(\nu\) when there is a class \(\alpha\) which has \(\mu\) terms and has a part which has \(\nu\) terms, while there is no class \(\beta\) which has \(\nu\) terms and has a part which has \(\mu\) terms. The relation "greater than" is transitive and asymmetrical; and by the Schröder-Bernstein theorem, if \(\mu\) is greater than or equal to \(\nu\), and \(\nu\) is greater than or equal to \(\mu\), then \(\mu = \nu\). But we cannot prove that of any two cardinals one must be the greater, unless we assume the multiplicative axiom. The proof then follows from Zermelo's theorem that on that assumption every class can be well-ordered. This subject will be dealt with at a later stage.
>
> The form of the definitions is so arranged as to allow of the inequality of two cardinals in different types. The relevant considerations are the same as for the definitions of addition, multiplication and exponentiation.
>
> Our definition of "\(\mu \gt \nu\)" is
>
> …

**Lean reading.** `>`, `<`, `≥`, `≤` are `>ᶜ`, `<ᶜ`, `≥ᶜ`, `≤ᶜ` (✱117·01–·06); a side `Nc'α` is `n₀c
A` (✱117·02·03 and PM's note after ✱117·06), and `ΠNc'κ`, `ΣNc'κ`, `Nc'∈_Δ'κ` at a side are normally
adjusted through their Dfs. PM applies convention AT to all of ✱117: every equation (or inequation)
between pure arithmetical formal numbers is in a type adequate for both sides (`AdeqNc`, `AdeqSm`,
`AdeqAdd`, `AdeqExp`); every other formal number at a side of `>`, `≥` (`sm''μ`, `μ +_c ϖ`, `μ^ϖ`,
…) has its own adequate type (IIT), and constants `0`, `1`, `2` at a side are in types in which they
exist. `∃!Cl'α ∩ Nc'β` is shown equivalent to an injection of `β` into `α`, and the
Schröder–Bernstein theorem (`Function.Embedding.antisymm`) gives ✱117·21·211·23·25. ✱117·632 is
false as printed (PM's `T` is not one-one) and is corrected; ✱117·633·64 do not depend on it.

**Status.** proved (all propositions; ✱117·632 proved (corrected);
✱117·101·102·106·107·108·16·21·211·23·244·25·26·27·3·31·5·501·51·511·52·53·531·54·55·551·56·561·57·571·58·581·59·591·592·6·61·62·63·631·633·64·651·652·661
proved (reading); see their docstrings).
-/

/-- ✱117·01 (Df). \[\begin{align}\mu \gt \nu . = . (\exists \alpha , \beta ) . &\mu = \text{N}_{0}\text{c}ʻ\alpha . \nu = \text{N}_{0}\text{c}ʻ\beta .\\ &\exists ! \text{Cl}ʻ\alpha \cap \text{Nc}ʻ\beta . {\sim} \exists ! \text{Cl}ʻ\beta \cap \text{Nc}ʻ\alpha \quad\text{Df}\end{align}\] -/
theorem pm117_01 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ >ᶜ ν ↔ ∃ (A : Set X) (B : Set Y),
      ((μ = n₀c A ∧ ν = n₀c B) ∧ (cl A ∩ nc X B).Nonempty) ∧ ¬(cl B ∩ nc Y A).Nonempty :=
  Iff.rfl

/-- ✱117·02 (Df). \(\mu \gt \text{Nc}ʻ\alpha . = . \mu \gt \text{N}_{0}\text{c}ʻ\alpha \quad\text{Df}\)

A rule of translation (normal adjustment): a side `Nc'α` of `>` is written `n₀c A`. -/
theorem pm117_02 {X Y : Type*} {μ : Set (Set X)} {A : Set Y} : μ >ᶜ n₀c A ↔ μ >ᶜ n₀c A :=
  Iff.rfl

/-- ✱117·03 (Df). \(\text{Nc}ʻ\alpha \gt \nu . = . \text{N}_{0}\text{c}ʻ\alpha \gt \nu \quad\text{Df}\)

A rule of translation (normal adjustment), as ✱117·02. -/
theorem pm117_03 {X Y : Type*} {A : Set X} {ν : Set (Set Y)} : n₀c A >ᶜ ν ↔ n₀c A >ᶜ ν :=
  Iff.rfl

/-- ✱117·04 (Df). \(\mu \lt \nu . = . \nu \gt \mu \quad\text{Df}\) -/
theorem pm117_04 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} : μ <ᶜ ν ↔ ν >ᶜ μ := Iff.rfl

/-- ✱117·05 (Df). \(\mu \geq \nu . = : \mu \gt \nu . \lor . \mu , \nu \in \text{N}_{0}\text{C} .\mu = \text{ sm }ʻʻ\nu \quad\text{Df}\) -/
theorem pm117_05 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ ≥ᶜ ν ↔ μ >ᶜ ν ∨ ((μ ∈ N₀C ∧ ν ∈ N₀C) ∧ μ = sm ʻʻ ν) := Iff.rfl

/-- ✱117·06 (Df). \(\mu \leq \nu . = . \nu \geq \mu \quad\text{Df}\) -/
theorem pm117_06 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} : μ ≤ᶜ ν ↔ ν ≥ᶜ μ := Iff.rfl

/-- ✱117·1. \[\begin{align}\vdash : \mu \gt \nu . &\equiv . (\exists \alpha , \beta ) . \mu = \text{N}_{0}\text{c}ʻ\alpha . \nu = \text{N}_{0}\text{c}ʻ\beta .\\ &\exists ! \text{Cl}ʻ\alpha \cap \text{Nc}ʻ\beta . {\sim} \exists ! \text{Cl}ʻ\beta \cap \text{Nc}ʻ\alpha \quad[(*117·01)]\end{align}\]

`Cl'α ∩ Nc'β` puts `Nc'β` in the type of `α` (`nc X B`); `Cl'β ∩ Nc'α` gives `nc Y A`. -/
theorem pm117_1 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ >ᶜ ν ↔ ∃ (A : Set X) (B : Set Y),
      ((μ = n₀c A ∧ ν = n₀c B) ∧ (cl A ∩ nc X B).Nonempty) ∧ ¬(cl B ∩ nc Y A).Nonempty :=
  Iff.rfl

/-- ✱117·101. \(\vdash : \mu \gt \text{Nc}ʻ\beta . \equiv . \mu \gt \text{N}_{0}\text{c}ʻ\beta \quad[(*117·02)]\)

**Status.** proved (reading): by the Df ✱117·02 (normal adjustment) the side `Nc'β` is
`N₀c'β`, so the two sides are the same. -/
theorem pm117_101 {X Y : Type*} {μ : Set (Set X)} {B : Set Y} : μ >ᶜ n₀c B ↔ μ >ᶜ n₀c B :=
  Iff.rfl

/-- ✱117·102. \(\vdash : \text{Nc}ʻ\alpha > \nu . \equiv . \text{N}_{0}\text{c}ʻ\alpha > \nu \quad[(*117·03)]\)

**Status.** proved (reading): by the Df ✱117·03 (normal adjustment) the side `Nc'α` is
`N₀c'α`, so the two sides are the same. -/
theorem pm117_102 {X Y : Type*} {A : Set X} {ν : Set (Set Y)} : n₀c A >ᶜ ν ↔ n₀c A >ᶜ ν :=
  Iff.rfl

/-- ✱117·103. \(\vdash : \mu \mu \quad[(*117·04)]\)

The formula of `data/principia.json` is garbled by its extraction (the text between `<` and `>`
was dropped as an HTML tag); the e-text itself (`.lake-local/src/78255-src.htm`) prints
\(\vdash : \mu < \nu . \equiv . \nu > \mu \quad[(*117·04)]\), which is formalized as printed. -/
theorem pm117_103 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} : μ <ᶜ ν ↔ ν >ᶜ μ :=
  Iff.rfl

/-- ✱117·104. \(\vdash \colon\ldotp \mu \geq \nu . \equiv : \mu > \nu . \lor . \mu , \nu \in \text{N}_{0}\text{C} . \mu = \text{ sm }ʻʻ\nu \quad[(*117·05)]\) -/
theorem pm117_104 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ ≥ᶜ ν ↔ μ >ᶜ ν ∨ ((μ ∈ N₀C ∧ ν ∈ N₀C) ∧ μ = sm ʻʻ ν) := Iff.rfl

/-- ✱117·105. \(\vdash : \mu \leq \nu . \equiv . \nu \geq \mu \quad[(*117·06)]\) -/
theorem pm117_105 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} : μ ≤ᶜ ν ↔ ν ≥ᶜ μ :=
  Iff.rfl

/-- ✱117·106. \(\vdash : \text{Nc}ʻ\alpha > \text{Nc}ʻ\beta . \equiv . \text{N}_{0}\text{c}ʻ\alpha > \text{N}_{0}\text{c}ʻ\beta \quad [*117·101·102]\)

**Status.** proved (reading): by ✱117·02·03 (normal adjustment) both sides are
`N₀c'α > N₀c'β`. -/
theorem pm117_106 {X Y : Type*} {A : Set X} {B : Set Y} : n₀c A >ᶜ n₀c B ↔ n₀c A >ᶜ n₀c B :=
  Iff.rfl

/-- ✱117·107. \(\vdash : \text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta . \equiv . \text{N}_{0}\text{c}ʻ\alpha \geq \text{N}_{0}\text{c}ʻ\beta\)

**Status.** proved (reading): by the analogues of ✱117·02·03 for `≥` (PM's note after ✱117·06)
both sides are `N₀c'α ≥ N₀c'β`. -/
theorem pm117_107 {X Y : Type*} {A : Set X} {B : Set Y} : n₀c A ≥ᶜ n₀c B ↔ n₀c A ≥ᶜ n₀c B :=
  Iff.rfl

/-- ✱117·108. \[\begin{align}&\vdash \colon\ldotp \text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta .\equiv :\text{Nc}ʻ\alpha \gt \text{Nc}ʻ\beta .\lor.\text{Nc}ʻ\alpha =\text{Nc}ʻ\beta \\ &[*117·107·106·104. *103·16·4]\end{align}\]

The worked example of Defs/Part3: the sides of `≥`, `>` are `n₀c A`, `n₀c B`; the equation is in
a type `γ` adequate for both sides (AT).

**Status.** proved (reading): convention AT (Prefatory Statement, VI); the arithmetical
occurrences of `Nc'α`, `Nc'β` are `N₀c'α`, `N₀c'β` by ✱117·02·03. -/
theorem pm117_108 {X Y γ : Type*} {A : Set X} {B : Set Y} (hA : AdeqNc γ A) (_hB : AdeqNc γ B) :
    n₀c A ≥ᶜ n₀c B ↔ n₀c A >ᶜ n₀c B ∨ nc γ A = nc γ B := by
  have key : n₀c A = sm ʻʻ n₀c B ↔ nc γ A = nc γ B := by
    rw [sm_img_n₀c, n₀c_eq_nc, nc_eq_nc_iff ⟨A, self_mem_nc A⟩,
      nc_eq_nc_iff (hA.nc_nonempty A)]
  exact or_congr Iff.rfl ⟨fun h => key.1 h.2, fun h => ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, key.2 h⟩⟩

/-- ✱117·11. \(\vdash \colon\ldotp \alpha \text{ sm } \alpha'.\beta \text{ sm } \beta'. \supset : \exists !\text{Cl}ʻ\alpha \cap \text{Nc}ʻ\beta .\equiv .\exists !\text{Cl}ʻ\alpha'\cap \text{Nc}ʻ\beta'\)

`α'`, `β'` are written `A'`, `B'`. -/
theorem pm117_11 {X Y X' Y' : Type*} {A : Set X} {B : Set Y} {A' : Set X'} {B' : Set Y'} :
    sm A A' ∧ sm B B' → ((cl A ∩ nc X B).Nonempty ↔ (cl A' ∩ nc X' B').Nonempty) := by
  rintro ⟨hA, hB⟩
  rw [pmB2_cl_nc_iff, pmB2_cl_nc_iff]
  exact pmB2_emb_congr hA hB

/-- ✱117·12. \[\begin{align}\vdash \colon\ldotp \mu >&\nu .\equiv :\mu ,\nu \in \text{N}_{0}\text{C}:\\ &\gamma \in \mu .\delta \in \nu .\supset _{\gamma ,\delta }.\exists !\text{Cl}ʻ\gamma \cap \text{Nc}ʻ\delta .{\sim}\exists !\text{Cl}ʻ\delta \cap \text{Nc}ʻ\gamma\end{align}\] -/
theorem pm117_12 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ >ᶜ ν ↔ (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ∀ G H, G ∈ μ ∧ H ∈ ν →
      (cl G ∩ nc X H).Nonempty ∧ ¬(cl H ∩ nc Y G).Nonempty := by
  constructor
  · intro h
    obtain ⟨A, B, ⟨rfl, rfl⟩, h1, h2⟩ := pmB2_gt_iff.1 h
    refine ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, fun G H ⟨hG, hH⟩ => ?_⟩
    rw [pmB2_cl_nc_iff, pmB2_cl_nc_iff, pmB2_emb_congr (mem_n₀c.1 hG) (mem_n₀c.1 hH),
      pmB2_emb_congr (mem_n₀c.1 hH) (mem_n₀c.1 hG)]
    exact ⟨h1, h2⟩
  · rintro ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, h⟩
    obtain ⟨h1, h2⟩ := h A B ⟨self_mem_n₀c A, self_mem_n₀c B⟩
    exact ⟨A, B, ⟨⟨rfl, rfl⟩, h1⟩, h2⟩

/-- ✱117·121. \[\begin{align}\vdash \colon\ldotp \mu >&\nu .\equiv :\mu ,\nu \in \text{N}_{0}\text{C}:\\ &\alpha \in \mu .\supset _{\alpha }.(\exists \beta ).\beta \in \nu .\exists !\text{Cl}ʻ\alpha \cap \text{Nc}ʻ\beta .{\sim}\exists !\text{Cl}ʻ\beta \cap \text{Nc}ʻ\alpha \end{align}\] -/
theorem pm117_121 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ >ᶜ ν ↔ (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ∀ A, A ∈ μ →
      ∃ B, (B ∈ ν ∧ (cl A ∩ nc X B).Nonempty) ∧ ¬(cl B ∩ nc Y A).Nonempty := by
  rw [pm117_12]
  constructor
  · rintro ⟨⟨hμ, ⟨B, rfl⟩⟩, h⟩
    exact ⟨⟨hμ, ⟨B, rfl⟩⟩, fun A hA => ⟨B, ⟨self_mem_n₀c B, (h A B ⟨hA, self_mem_n₀c B⟩).1⟩,
      (h A B ⟨hA, self_mem_n₀c B⟩).2⟩⟩
  · rintro ⟨⟨hμ, hν⟩, h⟩
    refine ⟨⟨hμ, hν⟩, fun G H ⟨hG, hH⟩ => ?_⟩
    obtain ⟨B, ⟨hB, h1⟩, h2⟩ := h G hG
    obtain ⟨C, rfl⟩ := hν
    have sB : sm B H := sm_trans (mem_n₀c.1 hB) (sm_symm (mem_n₀c.1 hH))
    rw [pmB2_cl_nc_iff] at h1 h2 ⊢
    rw [pmB2_cl_nc_iff]
    exact ⟨(pmB2_emb_congr (sm_refl G) sB).1 h1,
      fun h' => h2 ((pmB2_emb_congr sB (sm_refl G)).2 h')⟩

/-- ✱117·13. \(\vdash :\text{Nc}ʻ\alpha >\text{Nc}ʻ\beta .\equiv .\exists !\text{Cl}ʻ\alpha \cap \text{Nc}ʻ\beta .{\sim}\exists !\text{Cl}ʻ\beta \cap \text{Nc}ʻ\alpha\)

The sides `Nc'α`, `Nc'β` are `N₀c'α`, `N₀c'β` (✱117·02·03). -/
theorem pm117_13 {X Y : Type*} {A : Set X} {B : Set Y} :
    n₀c A >ᶜ n₀c B ↔ (cl A ∩ nc X B).Nonempty ∧ ¬(cl B ∩ nc Y A).Nonempty := by
  rw [pmB2_gt_n₀c, pmB2_cl_nc_iff, pmB2_cl_nc_iff]

/-- ✱117·14. \[\begin{align}&\vdash :\mu \gt \nu .\equiv .(\exists \alpha ,\beta ).\mu =\text{N}_{0}\text{c}ʻ\alpha .\nu =\text{N}_{0}\text{c}ʻ\beta .\text{Nc}ʻ\alpha \gt \text{Nc}ʻ\beta \\ &[*117·1·13]\end{align}\] -/
theorem pm117_14 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ >ᶜ ν ↔ ∃ (A : Set X) (B : Set Y), (μ = n₀c A ∧ ν = n₀c B) ∧ n₀c A >ᶜ n₀c B := by
  constructor
  · intro h
    obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := pmB2_gt_iff.1 h
    exact ⟨A, B, ⟨rfl, rfl⟩, h⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩; exact h

private theorem pmB2_key15 {X Y : Type*} (A : Set X) (B : Set Y) :
    (sumCls (Cl ʻʻ n₀c A) ∩ sm ʻʻ n₀c B).Nonempty ↔ Nonempty (↥B ↪ ↥A) := by
  rw [sm_img_n₀c, ← pmB2_cl_nc_iff]
  constructor
  · rintro ⟨ρ, ⟨P, ⟨A', hA', hP⟩, hρ⟩, hρB⟩
    have hP' : P = cl A' := hP
    rw [hP'] at hρ
    rw [pmB2_cl_nc_iff, ← pmB2_emb_congr (mem_n₀c.1 hA') (sm_refl B), ← pmB2_cl_nc_iff]
    exact ⟨ρ, hρ, hρB⟩
  · rintro ⟨ρ, hρ, hρB⟩
    exact ⟨ρ, ⟨cl A, ⟨A, self_mem_n₀c A, rfl⟩, hρ⟩, hρB⟩

/-- ✱117·15. \(\vdash :\mu \gt \nu .\equiv .\mu ,\nu \in \text{N}_{0}\text{C}.\exists !sʻ\text{Cl}ʻʻ\mu \cap \text{ sm }ʻʻ\nu .{\sim}\exists !sʻ\text{Cl}ʻʻ\nu \cap \text{ sm }ʻʻ\mu\)

`s'Cl''μ` is `sumCls (Cl ʻʻ μ)`; `sm''ν` is in the type of `s'Cl''μ`'s members (significance). -/
theorem pm117_15 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ >ᶜ ν ↔ ((μ ∈ N₀C ∧ ν ∈ N₀C) ∧ (sumCls (Cl ʻʻ μ) ∩ sm ʻʻ ν).Nonempty) ∧
      ¬(sumCls (Cl ʻʻ ν) ∩ sm ʻʻ μ).Nonempty := by
  constructor
  · intro h
    obtain ⟨A, B, ⟨rfl, rfl⟩, h1, h2⟩ := pmB2_gt_iff.1 h
    exact ⟨⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, (pmB2_key15 A B).2 h1⟩, fun h' => h2 ((pmB2_key15 B A).1 h')⟩
  · rintro ⟨⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, h1⟩, h2⟩
    exact pmB2_gt_n₀c.2 ⟨(pmB2_key15 A B).1 h1, fun h' => h2 ((pmB2_key15 B A).2 h')⟩

/-- ✱117·16. \[\begin{align}&\vdash \colon\ldotp \mu ,\nu \in \text{N}_{0}\text{C}.\supset :\mu \gt \nu .\equiv .\text{ sm }ʻʻ\mu \gt \nu .\equiv .\mu >\text{ sm }ʻʻ\nu .\equiv .\text{ sm }ʻʻ\mu >\text{ sm }ʻʻ\nu \\ &[*117·14.*103·4]\end{align}\]

`sm''μ` at a side of `>` is an arithmetical formal number other than `Nc'α`: by convention IIT
each occurrence has its own type with the adequacy hypothesis `AdeqSm` (the occurrence `sm''μ > ν`
of the second and third members of the chain is one formula). The chain of `≡` is the
conjunction of its links.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
occurrences of `sm''μ`, `sm''ν` are adequate (`AdeqSm`). -/
theorem pm117_16 {X Y W₁ W₂ W₃ W₄ : Type*} {μ : Set (Set X)} {ν : Set (Set Y)}
    (h₁ : AdeqSm W₁ μ) (h₂ : AdeqSm W₂ ν) (h₃ : AdeqSm W₃ μ) (h₄ : AdeqSm W₄ ν) :
    μ ∈ N₀C ∧ ν ∈ N₀C →
      ((μ >ᶜ ν ↔ (sm ʻʻ μ : Set (Set W₁)) >ᶜ ν) ∧
        ((sm ʻʻ μ : Set (Set W₁)) >ᶜ ν ↔ μ >ᶜ (sm ʻʻ ν : Set (Set W₂)))) ∧
        (μ >ᶜ (sm ʻʻ ν : Set (Set W₂)) ↔
          (sm ʻʻ μ : Set (Set W₃)) >ᶜ (sm ʻʻ ν : Set (Set W₄))) := by
  rintro ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩
  rw [sm_img_n₀c, sm_img_n₀c, sm_img_n₀c, sm_img_n₀c, n₀c_eq_nc A, n₀c_eq_nc B,
    pmB2_gt_nc (pmB2_n₀c_nc A) (pmB2_n₀c_nc B),
    pmB2_gt_nc (pmB2_AdeqSm_nc h₁ A) (pmB2_n₀c_nc B),
    pmB2_gt_nc (pmB2_n₀c_nc A) (pmB2_AdeqSm_nc h₂ B),
    pmB2_gt_nc (pmB2_AdeqSm_nc h₃ A) (pmB2_AdeqSm_nc h₄ B)]
  exact ⟨⟨Iff.rfl, Iff.rfl⟩, Iff.rfl⟩

private theorem pmB2_gt_iff_ge {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ >ᶜ ν ↔ μ ≥ᶜ ν ∧ ¬(ν ≥ᶜ μ) := by
  constructor
  · intro h
    obtain ⟨A, B, ⟨rfl, rfl⟩, h1, h2⟩ := pmB2_gt_iff.1 h
    rw [pmB2_ge_n₀c, pmB2_ge_n₀c]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨A, B, ⟨rfl, rfl⟩, h⟩ := pmB2_ge_iff.1 h1
    rw [pmB2_ge_n₀c] at h2
    exact pmB2_gt_n₀c.2 ⟨h, h2⟩

/-- ✱117·21. \[\begin{align}&\vdash :\exists !\text{Cl}ʻ\alpha \cap \text{Nc}ʻ\beta .\exists !\text{Cl}ʻ\beta \cap \text{Nc}ʻ\alpha .\supset .\text{Nc}ʻ\alpha =\text{Nc}ʻ\beta \\ &[*117·2.*100·321]\end{align}\]

The equation `Nc'α = Nc'β` is between pure arithmetical formal numbers: by convention AT it is in
a type `γ` adequate for both sides (here the implication holds in any type).

**Status.** proved (reading): convention AT (Prefatory Statement, VI). -/
theorem pm117_21 {X Y γ : Type*} {A : Set X} {B : Set Y} (_hA : AdeqNc γ A) (_hB : AdeqNc γ B) :
    (cl A ∩ nc X B).Nonempty ∧ (cl B ∩ nc Y A).Nonempty → nc γ A = nc γ B := by
  rintro ⟨h1, h2⟩
  rw [pmB2_cl_nc_iff] at h1 h2
  obtain ⟨f⟩ := h1
  obtain ⟨g⟩ := h2
  obtain ⟨e⟩ := Function.Embedding.antisymm g f
  exact nc_eq_nc_of_sm (pmB2_sm_of_equiv e)

/-- ✱117·211. \(\vdash :\exists !\text{Cl}ʻ\alpha \cap \text{Nc}ʻ\beta .\exists !\text{Cl}ʻ\beta \cap \text{Nc}ʻ\alpha .\equiv .\text{Nc}ʻ\alpha =\text{Nc}ʻ\beta\)

**Status.** proved (reading): convention AT (Prefatory Statement, VI): the equation is in a type
`γ` adequate for both sides. -/
theorem pm117_211 {X Y γ : Type*} {A : Set X} {B : Set Y} (hA : AdeqNc γ A) (hB : AdeqNc γ B) :
    (cl A ∩ nc X B).Nonempty ∧ (cl B ∩ nc Y A).Nonempty ↔ nc γ A = nc γ B := by
  refine ⟨pm117_21 hA hB, fun h => ?_⟩
  have hs : sm A B := (nc_eq_nc_iff (hA.nc_nonempty A)).1 h
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hs
  rw [pmB2_cl_nc_iff, pmB2_cl_nc_iff]
  exact ⟨⟨e.symm.toEmbedding⟩, ⟨e.toEmbedding⟩⟩

/-- ✱117·22. \(\vdash :\exists !\text{Cl}ʻ\alpha \cap \text{Nc}ʻ\beta .\equiv .\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta\) -/
theorem pm117_22 {X Y : Type*} {A : Set X} {B : Set Y} :
    (cl A ∩ nc X B).Nonempty ↔ n₀c A ≥ᶜ n₀c B := by
  rw [pmB2_ge_n₀c, pmB2_cl_nc_iff]

/-- ✱117·221. \(\vdash :\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta .\equiv .(\exists \rho ).\rho \subset \alpha .\rho \text{ sm }\beta \quad[*117·22.*60·2.*100·1]\) -/
theorem pm117_221 {X Y : Type*} {A : Set X} {B : Set Y} :
    n₀c A ≥ᶜ n₀c B ↔ ∃ ρ, ρ ⊆ A ∧ sm ρ B := by
  rw [← pm117_22]
  exact ⟨fun ⟨ρ, h1, h2⟩ => ⟨ρ, h1, h2⟩, fun ⟨ρ, h1, h2⟩ => ⟨ρ, h1, h2⟩⟩

/-- ✱117·222. \(\vdash :\beta \subset \alpha .\supset .\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta \quad[*117·221]\) -/
theorem pm117_222 {X : Type*} {A B : Set X} : B ⊆ A → n₀c A ≥ᶜ n₀c B :=
  fun h => pm117_221.2 ⟨B, h, sm_refl B⟩

/-- ✱117·23. \(\vdash :\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta .\text{Nc}ʻ\beta \geq \text{Nc}ʻ\alpha .\equiv .\text{Nc}ʻ\alpha =\text{Nc}ʻ\beta \quad[*117·211·22]\)

**Status.** proved (reading): convention AT (Prefatory Statement, VI): the equation is in a type
`γ` adequate for both sides. -/
theorem pm117_23 {X Y γ : Type*} {A : Set X} {B : Set Y} (hA : AdeqNc γ A) (hB : AdeqNc γ B) :
    n₀c A ≥ᶜ n₀c B ∧ n₀c B ≥ᶜ n₀c A ↔ nc γ A = nc γ B := by
  rw [← pm117_22, ← pm117_22]
  exact pm117_211 hA hB

/-- ✱117·24. \(\vdash :\mu \geq \nu .\equiv .(\exists \alpha ,\beta ).\mu =\text{N}_{0}\text{c}ʻ\alpha .\nu =\text{N}_{0}\text{c}ʻ\beta .\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta\) -/
theorem pm117_24 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ ≥ᶜ ν ↔ ∃ (A : Set X) (B : Set Y), (μ = n₀c A ∧ ν = n₀c B) ∧ n₀c A ≥ᶜ n₀c B := by
  constructor
  · intro h
    obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := pmB2_ge_iff.1 h
    exact ⟨A, B, ⟨rfl, rfl⟩, h⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩; exact h

/-- ✱117·241. \[\begin{align}&\vdash :\mu \geq \nu .\equiv .(\exists \alpha ,\beta ).\mu =\text{N}_{0}\text{c}ʻ\alpha .\nu =\text{N}_{0}\text{c}ʻ\beta .\exists !\text{Cl}ʻ\alpha \cap \text{Nc}ʻ\beta \\ &[*117·24·22]\end{align}\] -/
theorem pm117_241 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ ≥ᶜ ν ↔ ∃ (A : Set X) (B : Set Y), (μ = n₀c A ∧ ν = n₀c B) ∧ (cl A ∩ nc X B).Nonempty := by
  rw [pm117_24]
  simp only [pm117_22]

/-- ✱117·242. \[\begin{align}&\vdash \colon\ldotp \mu ,\nu \in \text{NC}.\supset :\mu \geq \nu .\equiv .(\exists \alpha ,\beta ).\alpha \in \mu .\beta \in \nu .\exists !\text{Cl}ʻ\alpha \cap \text{Nc}ʻ\beta \\ &[*117·241.*103·26]\end{align}\]

`μ, ν ∈ NC` is `μ ∈ NC β₁ ∧ ν ∈ NC β₂` (independent types, Prefatory Statement, V). -/
theorem pm117_242 {X Y β₁ β₂ : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ ∈ NC β₁ ∧ ν ∈ NC β₂ →
      (μ ≥ᶜ ν ↔ ∃ (A : Set X) (B : Set Y), (A ∈ μ ∧ B ∈ ν) ∧ (cl A ∩ nc X B).Nonempty) := by
  rintro ⟨hμ, hν⟩
  rw [pm117_241]
  constructor
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    exact ⟨A, B, ⟨self_mem_n₀c A, self_mem_n₀c B⟩, h⟩
  · rintro ⟨A, B, ⟨hA, hB⟩, h⟩
    exact ⟨A, B, ⟨pmB2_NC_eq_n₀c hμ hA, pmB2_NC_eq_n₀c hν hB⟩, h⟩

/-- ✱117·243. \[\begin{align}&\vdash \colon\ldotp \mu \geq \nu .\equiv :(\exists \alpha ,\beta ):\mu =\text{N}_{0}\text{c}ʻ\alpha .\nu =\text{N}_{0}\text{c}ʻ\beta :(\exists \rho ).\rho \subset \alpha .\rho \text{ sm }\beta \\ &[*117·24·221]\end{align}\] -/
theorem pm117_243 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ ≥ᶜ ν ↔ ∃ (A : Set X) (B : Set Y), (μ = n₀c A ∧ ν = n₀c B) ∧ ∃ ρ, ρ ⊆ A ∧ sm ρ B := by
  rw [pm117_24]
  simp only [pm117_221]

/-- ✱117·244. \[\begin{align}\vdash \colon\ldotp \mu ,\nu \in \text{N}_{0}\text{C}.\supset :\mu \geq \nu .\equiv .&\text{ sm }ʻʻ\mu \geq \nu .\equiv .\mu \geq \text{ sm }ʻʻ\nu .\equiv .\\ &\text{ sm }ʻʻ\mu \geq \text{ sm }ʻʻ\nu \quad[*117·24.*103·4]\end{align}\]

As ✱117·16, with `≥`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
occurrences of `sm''μ`, `sm''ν` are adequate (`AdeqSm`). -/
theorem pm117_244 {X Y W₁ W₂ W₃ W₄ : Type*} {μ : Set (Set X)} {ν : Set (Set Y)}
    (h₁ : AdeqSm W₁ μ) (h₂ : AdeqSm W₂ ν) (h₃ : AdeqSm W₃ μ) (h₄ : AdeqSm W₄ ν) :
    μ ∈ N₀C ∧ ν ∈ N₀C →
      ((μ ≥ᶜ ν ↔ (sm ʻʻ μ : Set (Set W₁)) ≥ᶜ ν) ∧
        ((sm ʻʻ μ : Set (Set W₁)) ≥ᶜ ν ↔ μ ≥ᶜ (sm ʻʻ ν : Set (Set W₂)))) ∧
        (μ ≥ᶜ (sm ʻʻ ν : Set (Set W₂)) ↔
          (sm ʻʻ μ : Set (Set W₃)) ≥ᶜ (sm ʻʻ ν : Set (Set W₄))) := by
  rintro ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩
  rw [sm_img_n₀c, sm_img_n₀c, sm_img_n₀c, sm_img_n₀c, n₀c_eq_nc A, n₀c_eq_nc B,
    pmB2_ge_nc (pmB2_n₀c_nc A) (pmB2_n₀c_nc B),
    pmB2_ge_nc (pmB2_AdeqSm_nc h₁ A) (pmB2_n₀c_nc B),
    pmB2_ge_nc (pmB2_n₀c_nc A) (pmB2_AdeqSm_nc h₂ B),
    pmB2_ge_nc (pmB2_AdeqSm_nc h₃ A) (pmB2_AdeqSm_nc h₄ B)]
  exact ⟨⟨Iff.rfl, Iff.rfl⟩, Iff.rfl⟩

/-- ✱117·25. \(\vdash :\mu \geq \nu .\nu \geq \mu .\equiv .\mu ,\nu \in \text{N}_{0}\text{C}.\text{ sm }ʻʻ\mu =\text{ sm }ʻʻ\nu\)

The equation `sm''μ = sm''ν` is between arithmetical formal numbers: by convention AT it is in a
type adequate for both sides (`AdeqSm`).

**Status.** proved (reading): convention AT (Prefatory Statement, VI). -/
theorem pm117_25 {X Y T : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} (hμ : AdeqSm T μ)
    (_hν : AdeqSm T ν) :
    μ ≥ᶜ ν ∧ ν ≥ᶜ μ ↔ (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ (sm ʻʻ μ : Set (Set T)) = sm ʻʻ ν := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨A, B, ⟨rfl, rfl⟩, f⟩ := pmB2_ge_iff.1 h1
    obtain ⟨g⟩ := pmB2_ge_n₀c.1 h2
    obtain ⟨f⟩ := f
    obtain ⟨e⟩ := Function.Embedding.antisymm g f
    refine ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, ?_⟩
    rw [sm_img_n₀c, sm_img_n₀c]
    exact nc_eq_nc_of_sm (pmB2_sm_of_equiv e)
  · rintro ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, h⟩
    rw [sm_img_n₀c, sm_img_n₀c] at h
    have hs : sm A B := (nc_eq_nc_iff (pmB2_AdeqSm_nc hμ A)).1 h
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hs
    rw [pmB2_ge_n₀c, pmB2_ge_n₀c]
    exact ⟨⟨e.symm.toEmbedding⟩, ⟨e.toEmbedding⟩⟩

/-- ✱117·26. \(\vdash :\text{Nc}ʻ\alpha >\text{Nc}ʻ\beta .\equiv .\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta .\text{Nc}ʻ\alpha \neq \text{Nc}ʻ\beta\)

**Status.** proved (reading): convention AT (Prefatory Statement, VI): the (negated) equation
`Nc'α = Nc'β` is in a type `γ` adequate for both sides. -/
theorem pm117_26 {X Y γ : Type*} {A : Set X} {B : Set Y} (hA : AdeqNc γ A) (hB : AdeqNc γ B) :
    n₀c A >ᶜ n₀c B ↔ n₀c A ≥ᶜ n₀c B ∧ nc γ A ≠ nc γ B := by
  rw [pmB2_gt_iff_ge, Ne, ← pm117_23 hA hB]
  tauto

/-- ✱117·27. \[\begin{align}&\vdash :\text{Nc}ʻ\alpha <\text{Nc}ʻ\beta .\equiv .\text{Nc}ʻ\alpha \leq \text{Nc}ʻ\beta .\text{Nc}ʻ\alpha \neq \text{Nc}ʻ\beta \\ &[*117·26·103·105]\end{align}\]

**Status.** proved (reading): convention AT (Prefatory Statement, VI), as ✱117·26. -/
theorem pm117_27 {X Y γ : Type*} {A : Set X} {B : Set Y} (hA : AdeqNc γ A) (hB : AdeqNc γ B) :
    n₀c A <ᶜ n₀c B ↔ n₀c A ≤ᶜ n₀c B ∧ nc γ A ≠ nc γ B := by
  rw [pm117_04, pm117_06, pm117_26 hB hA]
  exact and_congr Iff.rfl (not_congr eq_comm)

/-- ✱117·28. \[\begin{align}&\vdash :\text{Nc}ʻ\alpha >\text{Nc}ʻ\beta .\equiv .\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta .{\sim}(\text{Nc}ʻ\beta \geq \text{Nc}ʻ\alpha )\\ &[*117·22·13]\end{align}\] -/
theorem pm117_28 {X Y : Type*} {A : Set X} {B : Set Y} :
    n₀c A >ᶜ n₀c B ↔ n₀c A ≥ᶜ n₀c B ∧ ¬(n₀c B ≥ᶜ n₀c A) := pmB2_gt_iff_ge

/-- ✱117·2. \(\vdash :\mu >\nu .\equiv .\mu \geq \nu .{\sim}(\nu \geq \mu ) \quad[*117·14·28·24]\) -/
theorem pm117_2 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ >ᶜ ν ↔ μ ≥ᶜ ν ∧ ¬(ν ≥ᶜ μ) := pmB2_gt_iff_ge

/-- ✱117·29. \(\vdash :\text{Nc}ʻ\alpha <\text{Nc}ʻ\beta .\equiv .\text{Nc}ʻ\alpha \leq \text{Nc}ʻ\beta .{\sim}(\text{Nc}ʻ\beta \leq \text{Nc}ʻ\alpha ) \quad[*117·28]\) -/
theorem pm117_29 {X Y : Type*} {A : Set X} {B : Set Y} :
    n₀c A <ᶜ n₀c B ↔ n₀c A ≤ᶜ n₀c B ∧ ¬(n₀c B ≤ᶜ n₀c A) := pm117_2

/-- ✱117·291. \(\vdash :\mu <\nu .\equiv .\mu \leq \nu .{\sim}(\nu \leq \mu ) \quad[*117·281]\)

(PM's reference `✱117·281` is to ✱117·28·29.) -/
theorem pm117_291 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ <ᶜ ν ↔ μ ≤ᶜ ν ∧ ¬(ν ≤ᶜ μ) := pm117_2

private theorem pmB2_ge_sum {X Y : Type*} {A : Set X} {B : Set Y} (f : ↥B ↪ ↥A) :
    sm A (B +ₐ (A \ Set.range (fun b => (f b).1))) := by
  classical
  let ρ : Set X := Set.range (fun b => (f b).1)
  have hρA : ρ ⊆ A := fun x ⟨b, hb⟩ => hb ▸ (f b).2
  have e1 : ↥ρ ≃ ↥B := (Equiv.ofInjective (fun b => (f b).1)
    (fun b b' h => f.injective (Subtype.ext h))).symm
  refine sm_symm (pmB2_sm_of_equiv ((clsSumEquiv _ _).trans ?_))
  exact ((e1.symm.sumCongr (Equiv.refl _)).trans (Equiv.Set.union
    (Set.disjoint_sdiff_right)).symm).trans (Set.equivOfEq (Set.union_sdiff_cancel hρA))

/-- ✱117·3. \(\vdash :\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta .\equiv .(\exists \varpi ).\varpi \in \text{NC}.\text{Nc}ʻ\alpha =\text{Nc}ʻ\beta +_{c}\varpi\)

The sides of `≥` are `N₀c'α`, `N₀c'β` (✱117·02·03), and `Nc'β` as an argument of `+_c` is
`N₀c'β` (✱110·04). The apparent variable `ϖ` is taken in the type of `α`, with `NC`'s converse
domain in that type (PM's proof by ✱110·72 takes `ϖ = Nc'(α − δ)`). The equation is between
arithmetical formal numbers: by AT it is in a type `γ` adequate for both sides (`AdeqNc γ A`,
`AdeqAdd γ (n₀c B) ϖ`, the latter stated for any `ϖ` of its type).

**Status.** proved (reading): convention AT (Prefatory Statement, VI); the apparent variable `ϖ`
and the converse domain of `NC` are in the type of `α`, as in PM's proof (✱110·72). -/
theorem pm117_3 {X Y γ : Type*} {A : Set X} {B : Set Y} (hA : AdeqNc γ A)
    (_hB : AdeqAdd γ (n₀c B) (Λ : Set (Set X))) :
    n₀c A ≥ᶜ n₀c B ↔ ∃ ϖ : Set (Set X), ϖ ∈ NC X ∧ nc γ A = n₀c B +ᶜ ϖ := by
  rw [pmB2_ge_n₀c]
  constructor
  · rintro ⟨f⟩
    refine ⟨n₀c (A \ Set.range (fun b => (f b).1)), pmB2_n₀c_mem_NC _, ?_⟩
    rw [n₀c_cardAdd_n₀c]
    exact nc_eq_nc_of_sm (pmB2_ge_sum f)
  · rintro ⟨ϖ, hϖ, h⟩
    obtain ⟨C, hC⟩ := mem_NC.1 hϖ
    rw [hC, ← n₀c_eq_nc C, n₀c_cardAdd_n₀c] at h
    have hs : sm A (B +ₐ C) := (nc_eq_nc_iff (hA.nc_nonempty A)).1 h
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hs
    exact ⟨((Function.Embedding.inl.trans (clsSumEquiv B C).symm.toEmbedding).trans
      e.symm.toEmbedding)⟩

/-- ✱117·31. \(\vdash \colon\ldotp \mu \geq \nu .\equiv :\mu ,\nu \in \text{N}_{0}\text{C}:(\exists \varpi ).\varpi \in \text{NC}.\mu =\nu +_{c}\varpi\)

The equation `μ = ν +_c ϖ` is in the type of `μ`; `ϖ` and the converse domain of `NC` are in that
type, as in ✱117·3.

**Status.** proved (reading): the apparent variable `ϖ` and the converse domain of `NC` are in
the type of the members of `μ` (as in ✱117·3). -/
theorem pm117_31 {X Y : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} :
    μ ≥ᶜ ν ↔ (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ∃ ϖ : Set (Set X), ϖ ∈ NC X ∧ μ = ν +ᶜ ϖ := by
  constructor
  · intro h
    obtain ⟨A, B, ⟨rfl, rfl⟩, ⟨f⟩⟩ := pmB2_ge_iff.1 h
    refine ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, n₀c (A \ Set.range (fun b => (f b).1)),
      pmB2_n₀c_mem_NC _, ?_⟩
    rw [n₀c_cardAdd_n₀c, n₀c_eq_nc]
    exact nc_eq_nc_of_sm (pmB2_ge_sum f)
  · rintro ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, ϖ, hϖ, h⟩
    obtain ⟨C, hC⟩ := mem_NC.1 hϖ
    rw [hC, ← n₀c_eq_nc C, n₀c_cardAdd_n₀c, n₀c_eq_nc] at h
    have hs : sm A (B +ₐ C) := (nc_eq_nc_iff (pmB2_n₀c_nc A)).1 h
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hs
    exact pmB2_ge_n₀c.2 ⟨((Function.Embedding.inl.trans (clsSumEquiv B C).symm.toEmbedding).trans
      e.symm.toEmbedding)⟩

/-- ✱117·32. \(\vdash :\mu \geq \nu .\exists !\text{ sm }ʻʻ\mu \cap tʻ\alpha .\supset .\exists !\text{ sm }ʻʻ\nu \cap tʻ\alpha\)

`t'α` is `typ A` (`A : Set W`), which puts `sm''μ`, `sm''ν` in the type of `α`. -/
theorem pm117_32 {X Y W : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {A : Set W} :
    μ ≥ᶜ ν ∧ ((sm ʻʻ μ : Set (Set W)) ∩ typ A).Nonempty →
      ((sm ʻʻ ν : Set (Set W)) ∩ typ A).Nonempty := by
  rintro ⟨h, hne⟩
  obtain ⟨A', B, ⟨rfl, rfl⟩, ⟨f⟩⟩ := pmB2_ge_iff.1 h
  rw [typ_eq_univ, Set.inter_univ, sm_img_n₀c] at hne ⊢
  obtain ⟨Z, hZ⟩ := hne
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hZ
  exact nc_nonempty_iff.2 ⟨fun b => (e.symm (f b)).1,
    fun b b' h => f.injective (e.symm.injective (Subtype.ext h))⟩

private theorem pmB2_ge_trans {X Y Z : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {ϖ : Set (Set Z)}
    (h1 : μ ≥ᶜ ν) (h2 : ν ≥ᶜ ϖ) : μ ≥ᶜ ϖ := by
  obtain ⟨A, B, ⟨rfl, rfl⟩, ⟨f⟩⟩ := pmB2_ge_iff.1 h1
  obtain ⟨B', C, ⟨hB, rfl⟩, ⟨g⟩⟩ := pmB2_ge_iff.1 h2
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (pmB2_of_mem_n₀c hB)
  exact pmB2_ge_n₀c.2 ⟨(g.trans e.toEmbedding).trans f⟩

/-- ✱117·4. \(\vdash :\mu \geq \nu .\nu \geq \varpi .\supset .\mu \geq \varpi\) -/
theorem pm117_4 {X Y Z : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {ϖ : Set (Set Z)} :
    μ ≥ᶜ ν ∧ ν ≥ᶜ ϖ → μ ≥ᶜ ϖ := fun ⟨h1, h2⟩ => pmB2_ge_trans h1 h2

/-- ✱117·41. \(\vdash :\mu \leq \nu .\nu \leq \varpi .\supset .\mu \leq \varpi \quad[*117·4]\) -/
theorem pm117_41 {X Y Z : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {ϖ : Set (Set Z)} :
    μ ≤ᶜ ν ∧ ν ≤ᶜ ϖ → μ ≤ᶜ ϖ := fun ⟨h1, h2⟩ => pmB2_ge_trans h2 h1

/-- ✱117·42. \(\vdash :{\sim}(\mu >\mu ).{\sim}(\mu <\mu )\) -/
theorem pm117_42 {X : Type*} {μ : Set (Set X)} : ¬(μ >ᶜ μ) ∧ ¬(μ <ᶜ μ) := by
  have : ¬(μ >ᶜ μ) := by
    intro h
    obtain ⟨A, B, ⟨hA, hB⟩, h1, h2⟩ := pmB2_gt_iff.1 h
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (pmB2_of_mem_n₀c (hA.symm.trans hB))
    exact h2 ⟨e.symm.toEmbedding⟩
  exact ⟨this, this⟩

/-- ✱117·43. \(\vdash :\mu \geq \nu .{\sim}(\mu \geq \varpi ).\supset .{\sim}(\nu \geq \varpi ) \quad[*117·4.\text{Transp}]\) -/
theorem pm117_43 {X Y Z : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {ϖ : Set (Set Z)} :
    μ ≥ᶜ ν ∧ ¬(μ ≥ᶜ ϖ) → ¬(ν ≥ᶜ ϖ) := fun ⟨h1, h2⟩ h3 => h2 (pmB2_ge_trans h1 h3)

/-- ✱117·44. \(\vdash :\nu \geq \varpi .{\sim}(\mu \geq \varpi ).\supset .{\sim}(\mu \geq \nu ) \quad[*117·4.\text{Transp}]\) -/
theorem pm117_44 {X Y Z : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {ϖ : Set (Set Z)} :
    ν ≥ᶜ ϖ ∧ ¬(μ ≥ᶜ ϖ) → ¬(μ ≥ᶜ ν) := fun ⟨h1, h2⟩ h3 => h2 (pmB2_ge_trans h3 h1)

/-- ✱117·45. \(\vdash :\mu \geq \nu .\nu >\varpi .\supset .\mu >\varpi\) -/
theorem pm117_45 {X Y Z : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {ϖ : Set (Set Z)} :
    μ ≥ᶜ ν ∧ ν >ᶜ ϖ → μ >ᶜ ϖ := by
  rintro ⟨h1, h2⟩
  rw [pm117_2] at h2 ⊢
  exact ⟨pmB2_ge_trans h1 h2.1, fun h => h2.2 (pmB2_ge_trans h h1)⟩

/-- ✱117·46. \(\vdash :\mu >\nu .\nu \geq \varpi .\supset .\mu >\varpi \quad[\text{Proof as in *117·45}]\) -/
theorem pm117_46 {X Y Z : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {ϖ : Set (Set Z)} :
    μ >ᶜ ν ∧ ν ≥ᶜ ϖ → μ >ᶜ ϖ := by
  rintro ⟨h1, h2⟩
  rw [pm117_2] at h1 ⊢
  exact ⟨pmB2_ge_trans h1.1 h2, fun h => h1.2 (pmB2_ge_trans h2 h)⟩

/-- ✱117·47. \(\vdash :\mu >\nu .\nu >\varpi .\supset .\mu >\varpi \quad[*117·45·104]\) -/
theorem pm117_47 {X Y Z : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {ϖ : Set (Set Z)} :
    μ >ᶜ ν ∧ ν >ᶜ ϖ → μ >ᶜ ϖ := by
  rintro ⟨h1, h2⟩
  exact pm117_45 ⟨(pm117_2.1 h1).1, h2⟩

/-- ✱117·471. \(\vdash :\mu <\nu .\nu <\varpi .\supset .\mu <\varpi \quad[*117·47·103]\) -/
theorem pm117_471 {X Y Z : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} {ϖ : Set (Set Z)} :
    μ <ᶜ ν ∧ ν <ᶜ ϖ → μ <ᶜ ϖ := fun ⟨h1, h2⟩ => pm117_47 ⟨h2, h1⟩

private theorem pmB2_ge_zero {X W : Type*} {μ : Set (Set X)} :
    μ ∈ N₀C ↔ μ ≥ᶜ (zero : Set (Set W)) := by
  constructor
  · rintro ⟨A, rfl⟩
    rw [zero_eq_n₀c_empty, pmB2_ge_n₀c]
    exact ⟨⟨fun x => absurd x.2 id, fun x => absurd x.2 id⟩⟩
  · exact fun h => (pmB2_ge_N₀C h).1

/-- ✱117·5. \(\vdash :\mu \in \text{N}_{0}\text{C}.\supset .\mu \geq 0\)

The constant `0` at a side of `≥` is taken in a type `W` of its own (convention IIT; no
hypothesis is needed for `0`).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV) for the constant `0`. -/
theorem pm117_5 {X W : Type*} {μ : Set (Set X)} : μ ∈ N₀C → μ ≥ᶜ (zero : Set (Set W)) :=
  pmB2_ge_zero.1

/-- ✱117·501. \(\vdash :\mu \in \text{N}_{0}\text{C}.\equiv .\mu \geq 0 \quad[*117·5·104]\)

**Status.** proved (reading): convention IIT for the constant `0`, as ✱117·5. -/
theorem pm117_501 {X W : Type*} {μ : Set (Set X)} : μ ∈ N₀C ↔ μ ≥ᶜ (zero : Set (Set W)) :=
  pmB2_ge_zero

private theorem pmB2_gt_zero {X W : Type*} {μ : Set (Set X)} :
    μ ∈ N₀C \ ι zero ↔ μ >ᶜ (zero : Set (Set W)) := by
  constructor
  · rintro ⟨⟨A, rfl⟩, h0⟩
    rw [zero_eq_n₀c_empty, pmB2_gt_n₀c]
    refine ⟨⟨⟨fun x => absurd x.2 id, fun x => absurd x.2 id⟩⟩, fun ⟨f⟩ => h0 ?_⟩
    rw [mem_unitCls, zero_eq_n₀c_empty, n₀c_eq_n₀c_iff]
    exact sm_iff_nonempty_equiv.2 ⟨⟨fun a => absurd (f a).2 id, fun x => absurd x.2 id,
      fun a => absurd (f a).2 id, fun x => absurd x.2 id⟩⟩
  · intro h
    obtain ⟨A, B, ⟨rfl, hB⟩, -, h2⟩ := pmB2_gt_iff.1 h
    refine ⟨⟨A, rfl⟩, fun h0 => h2 ?_⟩
    rw [mem_unitCls, zero_eq_n₀c_empty, n₀c_eq_n₀c_iff] at h0
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h0
    exact ⟨⟨fun a => absurd (e a).2 id, fun a => absurd (e a).2 id⟩⟩

/-- ✱117·51. \(\vdash :\mu \in \text{N}_{0}\text{C}-\iota ʻ0.\supset .\mu >0\)

**Status.** proved (reading): convention IIT for the constant `0` at a side of `>`; `ι'0` is in
the type of `μ`. -/
theorem pm117_51 {X W : Type*} {μ : Set (Set X)} :
    μ ∈ N₀C \ ι zero → μ >ᶜ (zero : Set (Set W)) := pmB2_gt_zero.1

/-- ✱117·511. \(\vdash :\mu \in \text{N}_{0}\text{C}-\iota ʻ0.\equiv .\mu >0 \quad[*117·51·15·42]\)

**Status.** proved (reading): convention IIT for the constant `0`, as ✱117·51. -/
theorem pm117_511 {X W : Type*} {μ : Set (Set X)} :
    μ ∈ N₀C \ ι zero ↔ μ >ᶜ (zero : Set (Set W)) := pmB2_gt_zero

private theorem pmB2_single_emb {X W : Type*} {A : Set X} (w : W) (hA : A.Nonempty) :
    Nonempty (↥({w} : Set W) ↪ ↥A) :=
  ⟨⟨fun _ => ⟨hA.some, hA.some_mem⟩, fun a b _ => Subsingleton.elim a b⟩⟩

/-- ✱117·52. \(\vdash :\exists !\xi .\supset .\text{Nc}ʻ\xi \geq 1\)

The constant `1` at a side of `≥` is taken in a type `W` in which it exists (convention IIT,
`[Nonempty W]`); `Nc'ξ` is `N₀c'ξ` (✱117·02·03).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the `1` is in a type in
which it exists (`[Nonempty W]`). -/
theorem pm117_52 {X W : Type*} [Nonempty W] {ξ : Set X} :
    ξ.Nonempty → n₀c ξ ≥ᶜ (one : Set (Set W)) := by
  intro h
  obtain ⟨w⟩ := ‹Nonempty W›
  rw [one_eq_n₀c_singleton w, pmB2_ge_n₀c]
  exact pmB2_single_emb w h

private theorem pmB2_ne_zero {X : Type*} {A : Set X} (h : n₀c A ∉ ι zero) : A.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  exact h (by rw [mem_unitCls, zero_eq_n₀c_empty])

/-- ✱117·53. \(\vdash :\mu \in \text{N}_{0}\text{C}-\iota ʻ0.\supset .\mu \geq 1\)

**Status.** proved (reading): convention IIT: the `1` is in a type in which it exists
(`[Nonempty W]`). -/
theorem pm117_53 {X W : Type*} [Nonempty W] {μ : Set (Set X)} :
    μ ∈ N₀C \ ι zero → μ ≥ᶜ (one : Set (Set W)) := by
  rintro ⟨⟨A, rfl⟩, h0⟩
  exact pm117_52 (pmB2_ne_zero h0)

/-- ✱117·531. \(\vdash :\mu \in \text{N}_{0}\text{C}-\iota ʻ0.\equiv .\mu \geq 1\)

**Status.** proved (reading): convention IIT: the `1` is in a type in which it exists
(`[Nonempty W]`). -/
theorem pm117_531 {X W : Type*} [Nonempty W] {μ : Set (Set X)} :
    μ ∈ N₀C \ ι zero ↔ μ ≥ᶜ (one : Set (Set W)) := by
  refine ⟨pm117_53, fun h => ?_⟩
  obtain ⟨A, B, ⟨rfl, hB⟩, ⟨f⟩⟩ := pmB2_ge_iff.1 h
  obtain ⟨w⟩ := ‹Nonempty W›
  rw [one_eq_n₀c_singleton w] at hB
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (pmB2_of_mem_n₀c hB)
  refine ⟨⟨A, rfl⟩, fun h0 => ?_⟩
  rw [mem_unitCls, zero_eq_n₀c_empty, n₀c_eq_n₀c_iff] at h0
  obtain ⟨e'⟩ := sm_iff_nonempty_equiv.1 h0
  exact (e' (f (e.symm ⟨w, rfl⟩))).2

private theorem pmB2_le_one_iff {X W : Type*} [Nonempty X] {A : Set X} (w : W) :
    Nonempty (↥A ↪ ↥({w} : Set W)) ↔ n₀c A = zero ∨ n₀c A = one := by
  constructor
  · rintro ⟨f⟩
    by_cases hA : A.Nonempty
    · right
      rw [one_eq_n₀c_singleton hA.some, n₀c_eq_n₀c_iff]
      refine sm_iff_nonempty_equiv.2 ⟨⟨fun _ => ⟨hA.some, rfl⟩, fun _ => ⟨hA.some, hA.some_mem⟩,
        fun a => f.injective (Subsingleton.elim _ _), fun b => Subsingleton.elim _ _⟩⟩
    · left
      rw [Set.not_nonempty_iff_eq_empty] at hA
      rw [hA, zero_eq_n₀c_empty]
  · rintro (h | h)
    · rw [zero_eq_n₀c_empty, n₀c_eq_n₀c_iff] at h
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
      exact ⟨⟨fun a => absurd (e a).2 id, fun a => absurd (e a).2 id⟩⟩
    · obtain ⟨x⟩ := ‹Nonempty X›
      rw [one_eq_n₀c_singleton x, n₀c_eq_n₀c_iff] at h
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
      exact ⟨⟨fun _ => ⟨w, rfl⟩, fun a b _ => e.injective (Subsingleton.elim _ _)⟩⟩

/-- ✱117·54. \(\vdash \colon\ldotp 1\geq \mu .\equiv :\mu =0.\lor.\mu =1\)

The `1` at the side of `≥` is in a type `W` in which it exists (IIT); `μ = 0`, `μ = 1` are in the
type of `μ`, which PM assumes non-empty.

**Status.** proved (reading): convention IIT (`[Nonempty W]`); `[Nonempty X]`: PM assumes every
type has a member (Introduction, Ch. I); in an empty type `1 = Λ` and `1 ≥ Λ` fails. -/
theorem pm117_54 {X W : Type*} [Nonempty W] [Nonempty X] {μ : Set (Set X)} :
    (one : Set (Set W)) ≥ᶜ μ ↔ μ = zero ∨ μ = one := by
  obtain ⟨w⟩ := ‹Nonempty W›
  constructor
  · intro h
    obtain ⟨B, A, ⟨hB, rfl⟩, f⟩ := pmB2_ge_iff.1 h
    rw [one_eq_n₀c_singleton w] at hB
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (pmB2_of_mem_n₀c hB)
    obtain ⟨f⟩ := f
    exact (pmB2_le_one_iff w).1 ⟨f.trans e.toEmbedding⟩
  · intro h
    have hN : μ ∈ N₀C := by
      rcases h with rfl | rfl
      · exact ⟨∅, zero_eq_n₀c_empty⟩
      · obtain ⟨x⟩ := ‹Nonempty X›; exact ⟨{x}, one_eq_n₀c_singleton x⟩
    obtain ⟨A, rfl⟩ := hN
    rw [one_eq_n₀c_singleton w, pmB2_ge_n₀c]
    exact (pmB2_le_one_iff w).2 h

/-- ✱117·55. \(\vdash : \mu > 1 . \equiv . \mu \in \text{N}_{0}\text{C} - \iota ʻ0 - \iota ʻ1\)

**Status.** proved (reading): convention IIT: the `1` at the side of `>` is in a type in which it
exists (`[Nonempty W]`); `ι'0`, `ι'1` are in the type of `μ`. -/
theorem pm117_55 {X W : Type*} [Nonempty W] {μ : Set (Set X)} :
    μ >ᶜ (one : Set (Set W)) ↔ μ ∈ (N₀C \ ι zero) \ ι one := by
  obtain ⟨w⟩ := ‹Nonempty W›
  constructor
  · intro h
    obtain ⟨A, B, ⟨rfl, hB⟩, h1, h2⟩ := pmB2_gt_iff.1 h
    rw [one_eq_n₀c_singleton w] at hB
    have sB := pmB2_of_mem_n₀c hB
    replace h1 : Nonempty (↥({w} : Set W) ↪ ↥A) := (pmB2_emb_congr (sm_refl A) sB).1 h1
    replace h2 : ¬Nonempty (↥A ↪ ↥({w} : Set W)) :=
      fun h => h2 ((pmB2_emb_congr (sm_symm sB) (sm_refl A)).1 h)
    have hA : A.Nonempty := by
      obtain ⟨f⟩ := h1; exact ⟨(f ⟨w, rfl⟩).1, (f ⟨w, rfl⟩).2⟩
    have : Nonempty X := ⟨hA.some⟩
    refine ⟨⟨⟨A, rfl⟩, fun h0 => ?_⟩, fun h0 => h2 ((pmB2_le_one_iff w).2 (Or.inr h0))⟩
    rw [mem_unitCls, zero_eq_n₀c_empty, n₀c_eq_n₀c_iff] at h0
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h0
    exact (e ⟨hA.some, hA.some_mem⟩).2
  · rintro ⟨⟨⟨A, rfl⟩, h0⟩, h1⟩
    have hA := pmB2_ne_zero h0
    have : Nonempty X := ⟨hA.some⟩
    rw [one_eq_n₀c_singleton w, pmB2_gt_n₀c]
    refine ⟨pmB2_single_emb w hA, fun hf => ?_⟩
    rcases (pmB2_le_one_iff w).1 hf with h | h
    · exact h0 (by rw [mem_unitCls]; exact h)
    · exact h1 (by rw [mem_unitCls]; exact h)

private theorem pmB2_two_emb {X W : Type*} {A : Set X} {a b : W} (hab : a ≠ b) :
    Nonempty (↥({a, b} : Set W) ↪ ↥A) ↔ ∃ x y, (x ∈ A ∧ y ∈ A) ∧ x ≠ y := by
  constructor
  · rintro ⟨f⟩
    refine ⟨(f ⟨a, Or.inl rfl⟩).1, (f ⟨b, Or.inr rfl⟩).1, ⟨(f _).2, (f _).2⟩, fun h => hab ?_⟩
    have := f.injective (Subtype.ext h)
    exact congrArg Subtype.val this
  · rintro ⟨x, y, ⟨hx, hy⟩, hxy⟩
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (pmB2_pair_sm hab hxy)
    have hsub : ({x, y} : Set X) ⊆ A := Set.insert_subset_iff.2 ⟨hx, Set.singleton_subset_iff.2 hy⟩
    exact ⟨e.symm.toEmbedding.trans ⟨Set.inclusion hsub, Set.inclusion_injective hsub⟩⟩

/-- ✱117·551. \[\begin{align}\vdash \colon\ldotp \mu \in \text{N}_{0}\text{C} - \iota ʻ0 - &\iota ʻ1 . \equiv :\\ &(\exists \alpha ) : \mu = \text{N}_{0}\text{c}ʻ\alpha : (\exists x, y) . x, y \in \alpha . x \neq y : \equiv . \mu \geq 2\end{align}\]

The chain of `≡` is the conjunction of its links; the `2` at the side of `≥` is in a type `W` in
which it exists (convention IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): `(two : Set (Set W))`
is non-empty. -/
theorem pm117_551 {X W : Type*} {μ : Set (Set X)} (h2 : (two : Set (Set W)).Nonempty) :
    (μ ∈ (N₀C \ ι zero) \ ι one ↔
        ∃ A, μ = n₀c A ∧ ∃ x y, (x ∈ A ∧ y ∈ A) ∧ x ≠ y) ∧
      ((∃ A, μ = n₀c A ∧ ∃ x y, (x ∈ A ∧ y ∈ A) ∧ x ≠ y) ↔ μ ≥ᶜ (two : Set (Set W))) := by
  obtain ⟨a, b, hab, e2⟩ := pmB2_two_eq h2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨⟨⟨A, rfl⟩, h0⟩, h1⟩
    obtain ⟨x, hx⟩ := pmB2_ne_zero h0
    refine ⟨A, rfl, ?_⟩
    by_contra hc
    push Not at hc
    apply h1
    rw [mem_unitCls, one_eq_n₀c_singleton x, n₀c_eq_n₀c_iff]
    refine sm_iff_nonempty_equiv.2 ⟨⟨fun _ => ⟨x, rfl⟩, fun _ => ⟨x, hx⟩, fun z => ?_,
      fun z => Subsingleton.elim _ _⟩⟩
    exact Subtype.ext (hc x z.1 ⟨hx, z.2⟩)
  · rintro ⟨A, rfl, x, y, ⟨hx, hy⟩, hxy⟩
    refine ⟨⟨⟨A, rfl⟩, fun h0 => ?_⟩, fun h1 => ?_⟩
    · rw [mem_unitCls, zero_eq_n₀c_empty, n₀c_eq_n₀c_iff] at h0
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h0
      exact (e ⟨x, hx⟩).2
    · rw [mem_unitCls, one_eq_n₀c_singleton x, n₀c_eq_n₀c_iff] at h1
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h1
      exact hxy (congrArg Subtype.val (e.injective (Subsingleton.elim (e ⟨x, hx⟩) (e ⟨y, hy⟩))))
  · rintro ⟨A, rfl, h⟩
    rw [e2, pmB2_ge_n₀c]
    exact (pmB2_two_emb hab).2 h
  · intro h
    obtain ⟨A, B, ⟨rfl, hB⟩, ⟨f⟩⟩ := pmB2_ge_iff.1 h
    rw [e2] at hB
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (pmB2_of_mem_n₀c hB)
    exact ⟨A, rfl, (pmB2_two_emb hab).1 ⟨e.symm.toEmbedding.trans f⟩⟩

/-- ✱117·56. \(\vdash : \text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta . \supset . \text{Nc}ʻ\alpha +_{c} \text{Nc}ʻ\gamma \geq \text{Nc}ʻ\beta +_{c} \text{Nc}ʻ\gamma\)

The sides `Nc'α +_c Nc'γ`, `Nc'β +_c Nc'γ` of `≥` are arithmetical formal numbers: by convention
IIT each has its own type, adequate (`AdeqAdd`); the arguments `Nc'α`, … are `N₀c'α`, …
(✱110·03·04, ✱117·02·03).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
two sums are adequate. -/
theorem pm117_56 {X Y Z W₁ W₂ : Type*} {A : Set X} {B : Set Y} {G : Set Z}
    (h₁ : AdeqAdd W₁ (n₀c A) (n₀c G)) (h₂ : AdeqAdd W₂ (n₀c B) (n₀c G)) :
    n₀c A ≥ᶜ n₀c B →
      (n₀c A +ᶜ n₀c G : Set (Set W₁)) ≥ᶜ (n₀c B +ᶜ n₀c G : Set (Set W₂)) := by
  intro h
  obtain ⟨f⟩ := pmB2_ge_n₀c.1 h
  rw [n₀c_cardAdd_n₀c, n₀c_cardAdd_n₀c, pmB2_ge_nc (h₁.nc_nonempty A G) (h₂.nc_nonempty B G)]
  exact pmB2_clsSum_emb f (Function.Embedding.refl _)

/-- ✱117·561. \(\vdash : \mu \geq \nu . \varpi \in \text{N}_{0}\text{C} . \supset . \mu +_{c} \varpi \geq \nu +_{c} \varpi \quad[*117·56]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
two sums are adequate (`AdeqAdd`). -/
theorem pm117_561 {X Y Z W₁ W₂ : Type*} {μ : Set (Set X)} {ν : Set (Set Y)}
    {ϖ : Set (Set Z)} (h₁ : AdeqAdd W₁ μ ϖ) (h₂ : AdeqAdd W₂ ν ϖ) :
    μ ≥ᶜ ν ∧ ϖ ∈ N₀C → (μ +ᶜ ϖ : Set (Set W₁)) ≥ᶜ (ν +ᶜ ϖ : Set (Set W₂)) := by
  rintro ⟨h, ⟨C, rfl⟩⟩
  obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := pmB2_ge_iff.1 h
  exact pm117_56 h₁ h₂ h

/-- ✱117·57. \(\vdash : \text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta . \supset . \text{Nc}ʻ\alpha \times _{c} \text{Nc}ʻ\gamma \geq \text{Nc}ʻ\beta \times _{c} \text{Nc}ʻ\gamma\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
two products are adequate (`AdeqMul`). -/
theorem pm117_57 {X Y Z W₁ W₂ : Type*} {A : Set X} {B : Set Y} {G : Set Z}
    (h₁ : AdeqMul W₁ (n₀c A) (n₀c G)) (h₂ : AdeqMul W₂ (n₀c B) (n₀c G)) :
    n₀c A ≥ᶜ n₀c B →
      (n₀c A ×ᶜ n₀c G : Set (Set W₁)) ≥ᶜ (n₀c B ×ᶜ n₀c G : Set (Set W₂)) := by
  intro h
  obtain ⟨f⟩ := pmB2_ge_n₀c.1 h
  rw [pmB2_n₀c_mul, pmB2_n₀c_mul, pmB2_ge_nc (pmB2_AdeqMul_nc h₁ A G) (pmB2_AdeqMul_nc h₂ B G)]
  exact pmB2_clsTimes_emb f (Function.Embedding.refl _)

/-- ✱117·571. \(\vdash .\mu \geq \nu .\varpi \in \text{N}_{0}\text{C}.\supset .\mu \times _{c}\varpi \geq \nu \times _{c}\varpi \quad[*117·57]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
two products are adequate (`AdeqMul`). -/
theorem pm117_571 {X Y Z W₁ W₂ : Type*} {μ : Set (Set X)} {ν : Set (Set Y)}
    {ϖ : Set (Set Z)} (h₁ : AdeqMul W₁ μ ϖ) (h₂ : AdeqMul W₂ ν ϖ) :
    μ ≥ᶜ ν ∧ ϖ ∈ N₀C → (μ ×ᶜ ϖ : Set (Set W₁)) ≥ᶜ (ν ×ᶜ ϖ : Set (Set W₂)) := by
  rintro ⟨h, ⟨C, rfl⟩⟩
  obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := pmB2_ge_iff.1 h
  exact pm117_57 h₁ h₂ h

/-- ✱117·58. \(\vdash :\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta .\supset .(\text{Nc}ʻ\alpha )^{\text{Nc}ʻ\gamma }\geq (\text{Nc}ʻ\beta )^{\text{Nc}ʻ\gamma }\)

The two powers have their own adequate types (IIT, `AdeqExp`); since an empty base type makes
`AdeqExp` hold vacuously while `Λ^Λ = 1` has no member in an empty type, the base types are
taken non-empty, as PM assumes of every type.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV), with `[Nonempty X]`,
`[Nonempty Y]` for the base types (PM assumes every type has a member, Introduction, Ch. I). -/
theorem pm117_58 {X Y Z W₁ W₂ : Type*} [Nonempty X] [Nonempty Y] {A : Set X} {B : Set Y}
    {G : Set Z} (h₁ : AdeqExp W₁ (n₀c A) (n₀c G)) (h₂ : AdeqExp W₂ (n₀c B) (n₀c G)) :
    n₀c A ≥ᶜ n₀c B →
      (n₀c A ^ᶜ n₀c G : Set (Set W₁)) ≥ᶜ (n₀c B ^ᶜ n₀c G : Set (Set W₂)) := by
  intro h
  obtain ⟨f⟩ := pmB2_ge_n₀c.1 h
  rw [pmB2_n₀c_exp, pmB2_n₀c_exp, pmB2_ge_nc (pmB2_AdeqExp_nc h₁ A G) (pmB2_AdeqExp_nc h₂ B G)]
  exact pmB2_clsExp_emb_base f

/-- ✱117·581. \(\vdash :\mu \geq \nu .\varpi \in \text{N}_{0}\text{C}.\supset .\mu ^{\varpi }\geq \nu ^{\varpi } \quad[*117·58]\)

**Status.** proved (reading): convention IIT, with non-empty base types, as ✱117·58. -/
theorem pm117_581 {X Y Z W₁ W₂ : Type*} [Nonempty X] [Nonempty Y] {μ : Set (Set X)}
    {ν : Set (Set Y)} {ϖ : Set (Set Z)} (h₁ : AdeqExp W₁ μ ϖ) (h₂ : AdeqExp W₂ ν ϖ) :
    μ ≥ᶜ ν ∧ ϖ ∈ N₀C → (μ ^ᶜ ϖ : Set (Set W₁)) ≥ᶜ (ν ^ᶜ ϖ : Set (Set W₂)) := by
  rintro ⟨h, ⟨C, rfl⟩⟩
  obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := pmB2_ge_iff.1 h
  exact pm117_58 h₁ h₂ h

/-- ✱117·582. \[\begin{align}\vdash :\exists !\gamma .\beta \subset \alpha .\sigma \in \gamma \,\,\text{exp}\,\,(\alpha -\beta ).\supset .&(\cup \sigma )\upharpoonright (\gamma \,\,\text{exp}\,\,\beta )\in 1\rightarrow 1.\\ &(\cup \sigma )ʻʻ(\gamma \,\,\text{exp}\,\,\beta )\subset \gamma \,\,\text{exp}\,\,\alpha \end{align}\]

`∪σ` is the relation of `τ ∪ σ` to `τ` (✱38, `opR (· ∪ ·) σ`). -/
theorem pm117_582 {X Z : Type*} {G : Set Z} {A B : Set X} {σ : Set (Z → X → Prop)} :
    (G.Nonempty ∧ B ⊆ A) ∧ σ ∈ clsExp G (A \ B) →
      opR (fun ρ τ : Set (Z → X → Prop) => ρ ∪ τ) σ ↾ clsExp G B ∈ arrow one one ∧
        opR (fun ρ τ : Set (Z → X → Prop) => ρ ∪ τ) σ ʻʻ clsExp G B ⊆ clsExp G A := by
  rintro ⟨⟨-, hBA⟩, hσ⟩
  obtain ⟨s1, s2⟩ := pmB2_mem_clsExp.1 hσ
  have hcut : ∀ τ, τ ∈ clsExp G B → ∀ x y, x ↓ y ∈ τ ∪ σ → (y ∈ B ↔ x ↓ y ∈ τ) := by
    intro τ hτ x y h
    have t2 := (pmB2_mem_clsExp.1 hτ).2
    constructor
    · intro hy
      rcases h with h | h
      · exact h
      · exact absurd hy (couple_mem_clsTimes.1 (s2 h)).2.2
    · intro h'; exact (couple_mem_clsTimes.1 (t2 h')).2
  refine ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩
  · rintro ρ ρ' τ ⟨⟨h, -⟩, ⟨h', -⟩⟩
    exact (show ρ = τ ∪ σ from h).trans (show ρ' = τ ∪ σ from h').symm
  · rintro ρ τ τ' ⟨⟨h, hτ⟩, ⟨h', hτ'⟩⟩
    have e : τ ∪ σ = τ' ∪ σ := (show ρ = τ ∪ σ from h).symm.trans h'
    ext P
    constructor
    · intro hP
      obtain ⟨x, y, ⟨-, hy⟩, rfl⟩ := pmB2_mem_clsTimes.1 ((pmB2_mem_clsExp.1 hτ).2 hP)
      have : x ↓ y ∈ τ' ∪ σ := e ▸ Or.inl hP
      exact (hcut τ' hτ' x y this).1 hy
    · intro hP
      obtain ⟨x, y, ⟨-, hy⟩, rfl⟩ := pmB2_mem_clsTimes.1 ((pmB2_mem_clsExp.1 hτ').2 hP)
      have : x ↓ y ∈ τ ∪ σ := e ▸ Or.inl hP
      exact (hcut τ hτ x y this).1 hy
  · rintro ρ ⟨τ, hτ, hρ⟩
    have hρ' : ρ = τ ∪ σ := hρ
    subst hρ'
    obtain ⟨t1, t2⟩ := pmB2_mem_clsExp.1 hτ
    refine pmB2_mem_clsExp.2 ⟨fun y hy => ?_, ?_⟩
    · by_cases hyB : y ∈ B
      · have : G ∩ {x | x ↓ y ∈ τ ∪ σ} = G ∩ {x | x ↓ y ∈ τ} := by
          ext x; exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (hcut τ hτ x y h2).1 hyB⟩,
            fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩⟩
        rw [this]; exact t1 y hyB
      · have : G ∩ {x | x ↓ y ∈ τ ∪ σ} = G ∩ {x | x ↓ y ∈ σ} := by
          ext x
          refine ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, Or.inr h2⟩⟩
          rcases h2 with h2 | h2
          · exact absurd ((couple_mem_clsTimes.1 (t2 h2)).2) hyB
          · exact h2
        rw [this]; exact s1 y ⟨hy, hyB⟩
    · rintro P (hP | hP)
      · obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := pmB2_mem_clsTimes.1 (t2 hP)
        exact couple_mem_clsTimes.2 ⟨hx, hBA hy⟩
      · obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := pmB2_mem_clsTimes.1 (s2 hP)
        exact couple_mem_clsTimes.2 ⟨hx, hy.1⟩

/-- ✱117·583. \(\vdash :\beta \subset \alpha .\exists !\gamma .\supset .(\exists \tau ).\tau \subset \gamma \,\,\text{exp}\,\,\alpha .\tau \text{ sm }(\gamma \,\,\text{exp}\,\,\beta )\) -/
theorem pm117_583 {X Z : Type*} {G : Set Z} {A B : Set X} :
    B ⊆ A ∧ G.Nonempty → ∃ τ, τ ⊆ clsExp G A ∧ sm τ (clsExp G B) := by
  rintro ⟨hBA, hG⟩
  obtain ⟨f⟩ := pmB2_clsExp_emb_exp (G := G) hG
    (⟨Set.inclusion hBA, Set.inclusion_injective hBA⟩ : ↥B ↪ ↥A)
  obtain ⟨τ, h1, h2⟩ := pmB2_cl_nc_iff.2 ⟨f⟩
  exact ⟨τ, h1, h2⟩

/-- ✱117·59. \(\vdash :\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta .\exists !\gamma .\supset .(\text{Nc}ʻ\gamma )^{\text{Nc}ʻ\alpha }\geq (\text{Nc}ʻ\gamma )^{\text{Nc}ʻ\beta }\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the two powers have
their own adequate types (`AdeqExp`). -/
theorem pm117_59 {X Y Z W₁ W₂ : Type*} {A : Set X} {B : Set Y} {G : Set Z}
    (h₁ : AdeqExp W₁ (n₀c G) (n₀c A)) (h₂ : AdeqExp W₂ (n₀c G) (n₀c B)) :
    n₀c A ≥ᶜ n₀c B ∧ G.Nonempty →
      (n₀c G ^ᶜ n₀c A : Set (Set W₁)) ≥ᶜ (n₀c G ^ᶜ n₀c B : Set (Set W₂)) := by
  rintro ⟨h, hG⟩
  have : Nonempty Z := ⟨hG.some⟩
  obtain ⟨f⟩ := pmB2_ge_n₀c.1 h
  rw [pmB2_n₀c_exp, pmB2_n₀c_exp, pmB2_ge_nc (pmB2_AdeqExp_nc h₁ G A) (pmB2_AdeqExp_nc h₂ G B)]
  exact pmB2_clsExp_emb_exp hG f

/-- ✱117·591. \(\vdash :\mu \geq \nu .\varpi \in \text{N}_{0}\text{C}-\iota ʻ0.\supset .\varpi ^{\mu } \geq \varpi ^{\nu } \quad[*117·59]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the two powers have
their own adequate types (`AdeqExp`). -/
theorem pm117_591 {X Y Z W₁ W₂ : Type*} {μ : Set (Set X)} {ν : Set (Set Y)}
    {ϖ : Set (Set Z)} (h₁ : AdeqExp W₁ ϖ μ) (h₂ : AdeqExp W₂ ϖ ν) :
    μ ≥ᶜ ν ∧ ϖ ∈ N₀C \ ι zero → (ϖ ^ᶜ μ : Set (Set W₁)) ≥ᶜ (ϖ ^ᶜ ν : Set (Set W₂)) := by
  rintro ⟨h, ⟨⟨C, rfl⟩, h0⟩⟩
  obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := pmB2_ge_iff.1 h
  exact pm117_59 h₁ h₂ ⟨h, pmB2_ne_zero h0⟩

private theorem pmB2_two_of_not {X : Type*} {A : Set X} (hA : A ∉ (zero : Set (Set X)) ∪ one) :
    ∃ a b, (a ∈ A ∧ b ∈ A) ∧ a ≠ b := by
  have h0 : A ≠ ∅ := fun h => hA (Or.inl (by rw [zero_eq, h]; rfl))
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 h0
  by_contra hc
  push Not at hc
  exact hA (Or.inr ⟨a, Set.ext fun x => ⟨fun hx => hc x a ⟨hx, ha⟩, fun e => by
    rw [mem_unitCls] at e; rw [e]; exact ha⟩⟩)

private theorem pmB2_ne_one {X : Type*} {A : Set X} (h1 : n₀c A ∉ ι one) (h0 : n₀c A ∉ ι zero) :
    ∃ a b, (a ∈ A ∧ b ∈ A) ∧ a ≠ b := by
  obtain ⟨a, ha⟩ := pmB2_ne_zero h0
  by_contra hc
  push Not at hc
  apply h1
  rw [mem_unitCls, one_eq_n₀c_singleton a, n₀c_eq_n₀c_iff]
  exact sm_iff_nonempty_equiv.2 ⟨⟨fun _ => ⟨a, rfl⟩, fun _ => ⟨a, ha⟩,
    fun z => Subtype.ext (hc a z.1 ⟨ha, z.2⟩), fun z => Subsingleton.elim _ _⟩⟩

/-- ✱117·592. \(\vdash :\alpha ^{\delta } = 1.\alpha \neq 0.\alpha \neq 1.\supset .\delta = 0\)

In this proposition PM's `α`, `δ` are cardinals (written `μ`, `ν`). The equation `α^δ = 1` is
between arithmetical formal numbers: by convention AT it is in a type `T` adequate for both sides
(`AdeqExp T μ ν`, and `[Nonempty T]` for `1`); `α ≠ 0`, `α ≠ 1`, `δ = 0` are in the types of
`μ`, `ν`.

**Status.** proved (reading): convention AT (Prefatory Statement, VI): the equation `α^δ = 1` is
in a type adequate for both sides; in an empty type both sides are `Λ`. -/
theorem pm117_592 {X Y T : Type*} [Nonempty T] {μ : Set (Set X)} {ν : Set (Set Y)}
    (_h : AdeqExp T μ ν) :
    ((μ ^ᶜ ν : Set (Set T)) = one ∧ μ ≠ zero) ∧ μ ≠ one → ν = zero := by
  rintro ⟨⟨h1, h0⟩, h1'⟩
  obtain ⟨t⟩ := ‹Nonempty T›
  have hne : (μ ^ᶜ ν : Set (Set T)).Nonempty := by
    rw [h1, one_eq_n₀c_singleton t]; exact n₀c_nonempty _
  obtain ⟨⟨A, rfl⟩, ⟨D, rfl⟩⟩ := pmB2_mem_N₀C_of_nonempty hne
  obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := pmB2_ne_one (fun h => h1' (mem_unitCls.1 h))
    (fun h => h0 (mem_unitCls.1 h))
  rw [pmB2_n₀c_exp, one_eq_n₀c_singleton t, n₀c_eq_nc] at h1
  have hs : sm (clsExp A D) ({t} : Set T) :=
    (nc_eq_nc_iff (by rw [h1]; exact pmB2_n₀c_nc _)).1 h1
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hs
  rw [zero_eq_n₀c_empty, n₀c_eq_n₀c_iff]
  by_contra hD
  have hD' : D.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hD (sm_refl _)
  obtain ⟨d, hd⟩ := hD'
  let f1 := (pmB2_clsExpEquiv A D).symm (fun _ => ⟨a, ha⟩)
  let f2 := (pmB2_clsExpEquiv A D).symm (fun _ => ⟨b, hb⟩)
  have : f1 = f2 := e.injective (Subsingleton.elim _ _)
  have := congrFun ((pmB2_clsExpEquiv A D).symm.injective this) ⟨d, hd⟩
  exact hab (congrArg Subtype.val this)

/-- ✱117·6. \(\vdash :\mu ,\nu \in \text{N}_{0}\text{C}.\supset .\mu +_{c}\nu \geq \mu .\mu +_{c}\nu \geq \nu\)

The two occurrences of `μ +_c ν` at sides of `≥` have their own adequate types (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV) (`AdeqAdd`). -/
theorem pm117_6 {X Y W₁ W₂ : Type*} {μ : Set (Set X)} {ν : Set (Set Y)}
    (h₁ : AdeqAdd W₁ μ ν) (h₂ : AdeqAdd W₂ μ ν) :
    μ ∈ N₀C ∧ ν ∈ N₀C → (μ +ᶜ ν : Set (Set W₁)) ≥ᶜ μ ∧ (μ +ᶜ ν : Set (Set W₂)) ≥ᶜ ν := by
  rintro ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩
  rw [n₀c_cardAdd_n₀c, n₀c_cardAdd_n₀c, n₀c_eq_nc A, n₀c_eq_nc B,
    pmB2_ge_nc (h₁.nc_nonempty A B) (pmB2_n₀c_nc A),
    pmB2_ge_nc (h₂.nc_nonempty A B) (pmB2_n₀c_nc B)]
  exact ⟨⟨Function.Embedding.inl.trans (clsSumEquiv A B).symm.toEmbedding⟩,
    ⟨Function.Embedding.inr.trans (clsSumEquiv A B).symm.toEmbedding⟩⟩

/-- ✱117·61. \(\vdash :\nu > \mu .\supset .\mu +_{c} \nu > \mu \quad[*117·6·45]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): `μ +_c ν` is in an
adequate type (`AdeqAdd`). -/
theorem pm117_61 {X Y W : Type*} {μ : Set (Set X)} {ν : Set (Set Y)} (h : AdeqAdd W μ ν) :
    ν >ᶜ μ → (μ +ᶜ ν : Set (Set W)) >ᶜ μ := by
  intro hgt
  obtain ⟨B, A, ⟨rfl, rfl⟩, -, h2⟩ := pmB2_gt_iff.1 hgt
  rw [n₀c_cardAdd_n₀c, n₀c_eq_nc A, pmB2_gt_nc (h.nc_nonempty A B) (pmB2_n₀c_nc A)]
  exact ⟨⟨Function.Embedding.inl.trans (clsSumEquiv A B).symm.toEmbedding⟩, fun ⟨f⟩ =>
    h2 ⟨(Function.Embedding.inr.trans (clsSumEquiv A B).symm.toEmbedding).trans f⟩⟩

/-- ✱117·62. \(\vdash :\mu ,\nu \in \text{N}_{0}\text{C}-\iota ʻ0.\supset .\mu \times _{c}\nu \geq \mu .\mu \times _{c}\nu \geq \nu\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV) (`AdeqMul`). -/
theorem pm117_62 {X Y W₁ W₂ : Type*} {μ : Set (Set X)} {ν : Set (Set Y)}
    (h₁ : AdeqMul W₁ μ ν) (h₂ : AdeqMul W₂ μ ν) :
    μ ∈ N₀C \ ι zero ∧ ν ∈ N₀C \ ι zero →
      (μ ×ᶜ ν : Set (Set W₁)) ≥ᶜ μ ∧ (μ ×ᶜ ν : Set (Set W₂)) ≥ᶜ ν := by
  rintro ⟨⟨⟨A, rfl⟩, hA⟩, ⟨⟨B, rfl⟩, hB⟩⟩
  obtain ⟨a, ha⟩ := pmB2_ne_zero hA
  obtain ⟨b, hb⟩ := pmB2_ne_zero hB
  rw [pmB2_n₀c_mul, pmB2_n₀c_mul, n₀c_eq_nc A, n₀c_eq_nc B,
    pmB2_ge_nc (pmB2_AdeqMul_nc h₁ A B) (pmB2_n₀c_nc A),
    pmB2_ge_nc (pmB2_AdeqMul_nc h₂ A B) (pmB2_n₀c_nc B)]
  exact ⟨⟨(⟨fun x => (⟨b, hb⟩, x), fun x y h => (Prod.ext_iff.1 h).2⟩ : ↥A ↪ ↥B × ↥A).trans
      (pmB2_clsTimesEquiv B A).symm.toEmbedding⟩,
    ⟨(⟨fun y => (y, ⟨a, ha⟩), fun x y h => (Prod.ext_iff.1 h).1⟩ : ↥B ↪ ↥B × ↥A).trans
      (pmB2_clsTimesEquiv B A).symm.toEmbedding⟩⟩

private theorem pmB2_sum_emb_prod {X Y : Type*} {A : Set X} {B : Set Y} {a₀ a₁ : X} {b₀ b₁ : Y}
    (ha₀ : a₀ ∈ A) (ha₁ : a₁ ∈ A) (hb₀ : b₀ ∈ B) (hb₁ : b₁ ∈ B) (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    Nonempty (↥A ⊕ ↥B ↪ ↥B × ↥A) := by
  classical
  refine ⟨⟨fun p => match p with
    | Sum.inl x => (⟨b₀, hb₀⟩, x)
    | Sum.inr y => if y.1 = b₀ then (⟨b₁, hb₁⟩, ⟨a₁, ha₁⟩) else (y, ⟨a₀, ha₀⟩), ?_⟩⟩
  rintro (x | y) (x' | y') h
  · exact congrArg Sum.inl (Prod.ext_iff.1 h).2
  · simp only at h
    split_ifs at h with h'
    · exact absurd (congrArg Subtype.val (Prod.ext_iff.1 h).1) hb
    · exact absurd (congrArg Subtype.val (Prod.ext_iff.1 h).1).symm h'
  · simp only at h
    split_ifs at h with h'
    · exact absurd (congrArg Subtype.val (Prod.ext_iff.1 h).1).symm hb
    · exact absurd (congrArg Subtype.val (Prod.ext_iff.1 h).1) h'
  · simp only at h
    split_ifs at h with h1 h2 h2
    · exact congrArg Sum.inr (Subtype.ext (h1.trans h2.symm))
    · exact absurd (congrArg Subtype.val (Prod.ext_iff.1 h).2).symm ha
    · exact absurd (congrArg Subtype.val (Prod.ext_iff.1 h).2) ha
    · exact congrArg Sum.inr (Prod.ext_iff.1 h).1

/-- ✱117·63. \(\vdash :\alpha ,\beta {\sim}\in 0\cup 1.\supset .\text{Nc}ʻ\alpha \times _{c}\text{Nc}ʻ\beta \geq \text{Nc}ʻ\alpha +_{c}\text{Nc}ʻ\beta\)

`α, β ∼∈ 0 ∪ 1` is `A ∉ 0 ∪ 1 ∧ B ∉ 0 ∪ 1`; the sides are arithmetical formal numbers with their
own adequate types (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV) (`AdeqMul`, `AdeqAdd`). -/
theorem pm117_63 {X Y W₁ W₂ : Type*} {A : Set X} {B : Set Y}
    (h₁ : AdeqMul W₁ (n₀c A) (n₀c B)) (h₂ : AdeqAdd W₂ (n₀c A) (n₀c B)) :
    A ∉ (zero : Set (Set X)) ∪ one ∧ B ∉ (zero : Set (Set Y)) ∪ one →
      (n₀c A ×ᶜ n₀c B : Set (Set W₁)) ≥ᶜ (n₀c A +ᶜ n₀c B : Set (Set W₂)) := by
  rintro ⟨hA, hB⟩
  obtain ⟨a₀, a₁, ⟨ha₀, ha₁⟩, ha⟩ := pmB2_two_of_not hA
  obtain ⟨b₀, b₁, ⟨hb₀, hb₁⟩, hb⟩ := pmB2_two_of_not hB
  rw [pmB2_n₀c_mul, n₀c_cardAdd_n₀c,
    pmB2_ge_nc (pmB2_AdeqMul_nc h₁ A B) (h₂.nc_nonempty A B)]
  obtain ⟨f⟩ := pmB2_sum_emb_prod ha₀ ha₁ hb₀ hb₁ ha hb
  exact ⟨((clsSumEquiv A B).toEmbedding.trans f).trans
    (pmB2_clsTimesEquiv B A).symm.toEmbedding⟩

/-- ✱117·631. \(\vdash :\mu ,\nu \in \text{N}_{0}\text{C}-\iota ʻ0-\iota ʻ1.\supset .\mu \times _{c}\nu \geq \mu +_{c}\nu \quad[*117·63]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV) (`AdeqMul`, `AdeqAdd`). -/
theorem pm117_631 {X Y W₁ W₂ : Type*} {μ : Set (Set X)} {ν : Set (Set Y)}
    (h₁ : AdeqMul W₁ μ ν) (h₂ : AdeqAdd W₂ μ ν) :
    μ ∈ (N₀C \ ι zero) \ ι one ∧ ν ∈ (N₀C \ ι zero) \ ι one →
      (μ ×ᶜ ν : Set (Set W₁)) ≥ᶜ (μ +ᶜ ν : Set (Set W₂)) := by
  rintro ⟨⟨⟨⟨A, rfl⟩, hA0⟩, hA1⟩, ⟨⟨⟨B, rfl⟩, hB0⟩, hB1⟩⟩
  obtain ⟨a₀, a₁, ⟨ha₀, ha₁⟩, ha⟩ := pmB2_ne_one hA1 hA0
  obtain ⟨b₀, b₁, ⟨hb₀, hb₁⟩, hb⟩ := pmB2_ne_one hB1 hB0
  rw [pmB2_n₀c_mul, n₀c_cardAdd_n₀c,
    pmB2_ge_nc (pmB2_AdeqMul_nc h₁ A B) (h₂.nc_nonempty A B)]
  obtain ⟨f⟩ := pmB2_sum_emb_prod ha₀ ha₁ hb₀ hb₁ ha hb
  exact ⟨((clsSumEquiv A B).toEmbedding.trans f).trans
    (pmB2_clsTimesEquiv B A).symm.toEmbedding⟩

/-- A sum of classes each with two distinguished members injects into their product. -/
private theorem pmB2_sigma_emb_pi {I : Type*} {F : I → Type*} (z o : ∀ i, F i)
    (hzo : ∀ i, z i ≠ o i) : Nonempty ((Σ i, F i) ↪ ((i : I) → F i)) := by
  classical
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · exact ⟨⟨fun p => isEmptyElim p.1, fun p => isEmptyElim p.1⟩⟩
  let g : (Σ i, F i) → ((i : I) → F i) := fun p =>
    if p.1 = i₀ ∨ p.2 ≠ z p.1 then Function.update z p.1 p.2
    else if ∃ k, k ≠ i₀ ∧ k ≠ p.1 then Function.update o p.1 (z p.1) else o
  have us : ∀ (f : ∀ i, F i) (i : I) (v : F i), Function.update f i v i = v :=
    fun f i v => Function.update_self i v f
  have un : ∀ (f : ∀ i, F i) (i k : I) (v : F i), k ≠ i → Function.update f i v k = f k :=
    fun f i k v h => Function.update_of_ne h v f
  -- each value of `g` is of one of three kinds
  have kU : ∀ i j (a : F i) (b : F j), (i = i₀ ∨ a ≠ z i) → (j = i₀ ∨ b ≠ z j) →
      Function.update z i a = Function.update z j b → (⟨i, a⟩ : Σ i, F i) = ⟨j, b⟩ := by
    intro i j a b c d h
    by_cases hij : i = j
    · subst hij
      have := congrFun h i
      rw [us, us] at this
      rw [this]
    · have e1 := congrFun h i
      have e2 := congrFun h j
      rw [us, un _ _ _ _ hij] at e1
      rw [us, un _ _ _ _ (Ne.symm hij)] at e2
      have hi : i = i₀ := c.resolve_right (not_not.2 e1)
      have hj : j = i₀ := d.resolve_right (not_not.2 e2.symm)
      exact absurd (hi.trans hj.symm) hij
  have kUR : ∀ i j (a : F i), (i = i₀ ∨ a ≠ z i) → j ≠ i₀ → (∃ k, k ≠ i₀ ∧ k ≠ j) →
      Function.update z i a ≠ Function.update o j (z j) := by
    intro i j a c hj ⟨k, hk0, hkj⟩ h
    by_cases hki : k = i
    · subst hki
      have := congrFun h i₀
      rw [un _ _ _ _ (Ne.symm hk0), un _ _ _ _ (Ne.symm hj)] at this
      exact hzo i₀ this
    · have := congrFun h k
      rw [un _ _ _ _ hki, un _ _ _ _ hkj] at this
      exact hzo k this
  have kUS : ∀ i j (a : F i), j ≠ i₀ → (∀ k, k = i₀ ∨ k = j) →
      Function.update z i a ≠ o := by
    intro i j a hj hk h
    by_cases hi : i = i₀
    · subst hi
      have := congrFun h j
      rw [un _ _ _ _ hj] at this
      exact hzo j this
    · have := congrFun h i₀
      rw [un _ _ _ _ (Ne.symm hi)] at this
      exact hzo i₀ this
  have kRR : ∀ i j, Function.update o i (z i) = Function.update o j (z j) → i = j := by
    intro i j h
    by_contra hij
    have := congrFun h i
    rw [us, un _ _ _ _ hij] at this
    exact hzo i this
  have neg2 : ∀ j, ¬(∃ k, k ≠ i₀ ∧ k ≠ j) → ∀ k, k = i₀ ∨ k = j := by
    intro j h k
    by_cases hk : k = i₀
    · exact Or.inl hk
    · exact Or.inr (by by_contra hkj; exact h ⟨k, hk, hkj⟩)
  refine ⟨⟨g, ?_⟩⟩
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  simp only [g] at h
  by_cases c1 : i = i₀ ∨ a ≠ z i
  · rw [ite_eq_left c1] at h
    by_cases d1 : j = i₀ ∨ b ≠ z j
    · rw [ite_eq_left d1] at h; exact kU i j a b c1 d1 h
    · rw [ite_eq_right d1] at h
      simp only [not_or, not_not] at d1
      by_cases d2 : ∃ k, k ≠ i₀ ∧ k ≠ j
      · rw [ite_eq_left d2] at h; exact absurd h (kUR i j a c1 d1.1 d2)
      · rw [ite_eq_right d2] at h; exact absurd h (kUS i j a d1.1 (neg2 j d2))
  · rw [ite_eq_right c1] at h
    simp only [not_or, not_not] at c1
    obtain ⟨hi, rfl⟩ := c1
    by_cases d1 : j = i₀ ∨ b ≠ z j
    · rw [ite_eq_left d1] at h
      by_cases c2 : ∃ k, k ≠ i₀ ∧ k ≠ i
      · rw [ite_eq_left c2] at h; exact absurd h.symm (kUR j i b d1 hi c2)
      · rw [ite_eq_right c2] at h; exact absurd h.symm (kUS j i b hi (neg2 i c2))
    · rw [ite_eq_right d1] at h
      simp only [not_or, not_not] at d1
      obtain ⟨hj, rfl⟩ := d1
      by_cases c2 : ∃ k, k ≠ i₀ ∧ k ≠ i
      · rw [ite_eq_left c2] at h
        by_cases d2 : ∃ k, k ≠ i₀ ∧ k ≠ j
        · rw [ite_eq_left d2] at h
          have := kRR i j h
          subst this; rfl
        · obtain ⟨k, hk0, hki⟩ := c2
          have hij : i = j := (neg2 j d2 i).resolve_left hi
          exact absurd ((neg2 j d2 k).resolve_left hk0) (hij ▸ hki)
      · by_cases d2 : ∃ k, k ≠ i₀ ∧ k ≠ j
        · obtain ⟨k, hk0, hkj⟩ := d2
          have hji : j = i := (neg2 i c2 j).resolve_left hj
          exact absurd ((neg2 i c2 k).resolve_left hk0) (hji ▸ hkj)
        · have hji : j = i := (neg2 i c2 j).resolve_left hj
          subst hji; rfl

private theorem pmB2_two_sel {X : Type*} {K : Set (Set X)} (hK : K ∈ Cls2excl) {ρ σ : Set X}
    (hρ : ρ ∈ prodK K) (hσ : σ ∈ prodK K) (hdis : ρ ∩ σ = Λ) :
    ∃ z o : (A : ↥K) → ↥(A : Set X), ∀ A, z A ≠ o A := by
  obtain ⟨h1, -⟩ := (pmB2_mem_prodK_excl hK).1 hρ
  obtain ⟨h1', -⟩ := (pmB2_mem_prodK_excl hK).1 hσ
  choose zf hzf using fun A : ↥K => h1 A.1 A.2
  choose of hof using fun A : ↥K => h1' A.1 A.2
  have hz : ∀ A : ↥K, zf A ∈ ρ ∩ (A : Set X) := fun A => by rw [hzf A]; rfl
  have ho : ∀ A : ↥K, of A ∈ σ ∩ (A : Set X) := fun A => by rw [hof A]; rfl
  refine ⟨fun A => ⟨zf A, (hz A).2⟩, fun A => ⟨of A, (ho A).2⟩, fun A h => ?_⟩
  have e : zf A = of A := congrArg Subtype.val h
  have : zf A ∈ ρ ∩ σ := ⟨(hz A).1, e ▸ (ho A).1⟩
  rw [hdis, Null_eq_empty] at this
  exact this

/-- ✱117·632. \[\begin{align}&\vdash :\kappa \in \text{Cls}^{2} \text{excl}.\kappa {\sim}\in 0\cup 1.\rho ,\sigma \in \text{Prod}ʻ\kappa .\rho \cap \sigma =\Lambda .\\ &T=\hat{\mu} \hat{x} \{(\exists \alpha ,\beta ).\alpha ,\beta \in \kappa .\alpha \neq \beta .x\in \beta .\mu =(\rho -\alpha -\beta )\cup (\sigma \cap \alpha )\cup \iota ʻx\}.\\ &\supset .T\in 1\rightarrow 1.\text{D}ʻT\subset \text{Prod}ʻ\kappa .\text{ᗡ}ʻT=sʻ\kappa\end{align}\]

As printed the proposition is false: the relation `T` defined there is not one-one. If `κ` has
two members `α`, `β` and `x` is the member of `σ` in `β`, then `μ T x` with
`μ = (ρ − α − β) ∪ (σ ∩ α) ∪ ι'x = σ`; and if `x'` is the member of `σ` in `α`, then likewise
`σ T x'` (with `α`, `β` interchanged), though `x ≠ x'`; with three members, a given `x` is related
to several `μ`s (one for each `α ≠ β`). (The demonstration's steps (6), (7) fail.) What ✱117·633
needs is a one-one `T` with `D'T ⊂ Prod'κ` and `ᗡ'T = s'κ`, which exists under the hypothesis
(with the hypothesis on `T` dropped): the corrected statement asserts its existence.

**Status.** proved (corrected): the `T` defined by PM is not one-one (counterexample above, proved
as `pm117_632_printed_false`); the existence of a one-one `T` with `D'T ⊂ Prod'κ . ᗡ'T = s'κ`, which
is what ✱117·633 uses, is proved. -/
theorem pm117_632 {X : Type*} {K : Set (Set X)} {ρ σ : Set X} :
    ((K ∈ Cls2excl ∧ K ∉ (zero : Set (Set (Set X))) ∪ one) ∧ (ρ ∈ prodK K ∧ σ ∈ prodK K)) ∧
        ρ ∩ σ = Λ →
      ∃ T : Set X → X → Prop, (T ∈ arrow one one ∧ dom T ⊆ prodK K) ∧ codom T = sumCls K := by
  rintro ⟨⟨⟨hK, -⟩, ⟨hρ, hσ⟩⟩, hdis⟩
  obtain ⟨z, o, hzo⟩ := pmB2_two_sel hK hρ hσ hdis
  obtain ⟨f⟩ := pmB2_sigma_emb_pi z o hzo
  let φ : ↥(sumCls K) ↪ ↥(prodK K) := (((pmB2_sumClsEquiv hK).toEmbedding.trans f).trans
    (pmB2_selE K).symm.toEmbedding).trans (pmB2_prodEquiv hK).symm.toEmbedding
  refine ⟨fun X x => ∃ h : x ∈ sumCls K, X = (φ ⟨x, h⟩).1, ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro X Y x ⟨⟨h, rfl⟩, ⟨h', rfl⟩⟩; rfl
  · rintro X x x' ⟨⟨h, rfl⟩, ⟨h', e⟩⟩
    exact congrArg Subtype.val (φ.injective (Subtype.ext e))
  · rintro X ⟨x, h, rfl⟩; exact (φ ⟨x, h⟩).2
  · ext x
    exact ⟨fun ⟨X, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

/-- The proposition ✱117·632 as printed is false: with `κ = {{0, 1}, {2, 3}}`, `ρ = {0, 2}`, `σ = {1, 3}` (in
`Fin 4`), PM's relation `T` relates `σ` both to `3` and to `1`, so it is not one-one. -/
theorem pm117_632_printed_false :
    ¬ ∀ (K : Set (Set (Fin 4))) (ρ σ : Set (Fin 4)) (T : Set (Fin 4) → Fin 4 → Prop),
      ((((K ∈ Cls2excl ∧ K ∉ (zero : Set (Set (Set (Fin 4)))) ∪ one) ∧
          (ρ ∈ prodK K ∧ σ ∈ prodK K)) ∧ ρ ∩ σ = Λ) ∧
        T = fun μ x => ∃ A B, (((A ∈ K ∧ B ∈ K) ∧ A ≠ B) ∧ x ∈ B) ∧
          μ = (((ρ \ A) \ B) ∪ (σ ∩ A)) ∪ ι x) →
        (T ∈ arrow one one ∧ dom T ⊆ prodK K) ∧ codom T = sumCls K := by
  intro h
  let S01 : Set (Fin 4) := {0, 1}
  let S23 : Set (Fin 4) := {2, 3}
  let K : Set (Set (Fin 4)) := {S01, S23}
  let ρ : Set (Fin 4) := {0, 2}
  let σ : Set (Fin 4) := {1, 3}
  have hne : S01 ≠ S23 := by
    intro e
    have : (0 : Fin 4) ∈ S23 := e ▸ (Or.inl rfl : (0 : Fin 4) ∈ S01)
    simp [S23] at this
  have memK : ∀ A, A ∈ K ↔ A = S01 ∨ A = S23 := fun A => Iff.rfl
  have hexcl : K ∈ Cls2excl := by
    rw [pmB2_excl_iff]
    intro A B x hA hB hxA hxB
    rcases (memK A).1 hA with rfl | rfl <;> rcases (memK B).1 hB with rfl | rfl
    · rfl
    · simp [S01, S23] at hxA hxB; omega
    · simp [S01, S23] at hxA hxB; omega
    · rfl
  have hK01 : K ∉ (zero : Set (Set (Set (Fin 4)))) ∪ one := by
    rintro (h0 | ⟨S, hS⟩)
    · rw [zero_eq] at h0
      have h1 : S01 ∈ (∅ : Set (Set (Fin 4))) ∨ False := by
        rw [Set.mem_singleton_iff] at h0
        have : S01 ∈ K := Or.inl rfl
        rw [h0] at this; exact absurd this (by simp)
      simp at h1
    · have h1 : S01 ∈ ι S := hS ▸ (Or.inl rfl : S01 ∈ K)
      have h2 : S23 ∈ ι S := hS ▸ (Or.inr rfl : S23 ∈ K)
      exact hne ((mem_unitCls.1 h1).trans (mem_unitCls.1 h2).symm)
  have sel : ∀ ρ : Set (Fin 4), ρ ⊆ S01 ∪ S23 → (∃ a, ρ ∩ S01 = ι a) → (∃ b, ρ ∩ S23 = ι b) →
      ρ ∈ prodK K := by
    intro ρ hρ ha hb
    refine pmB2_mem_prodK_of (fun A hA => ?_) (fun x hx => ?_)
    · rcases (memK A).1 hA with rfl | rfl
      · exact ha
      · exact hb
    · rcases hρ hx with h | h
      · exact ⟨S01, Or.inl rfl, h⟩
      · exact ⟨S23, Or.inr rfl, h⟩
  have hρ : ρ ∈ prodK K := by
    refine sel ρ (fun x hx => ?_) ⟨0, ?_⟩ ⟨2, ?_⟩
    · simp [ρ, S01, S23] at hx ⊢; omega
    · ext x; simp [ρ, S01, unitCls_eq_singleton]; omega
    · ext x; simp [ρ, S23, unitCls_eq_singleton]; omega
  have hσ : σ ∈ prodK K := by
    refine sel σ (fun x hx => ?_) ⟨1, ?_⟩ ⟨3, ?_⟩
    · simp [σ, S01, S23] at hx ⊢; omega
    · ext x; simp [σ, S01, unitCls_eq_singleton]; omega
    · ext x; simp [σ, S23, unitCls_eq_singleton]; omega
  have hdis : ρ ∩ σ = Λ := by
    rw [Null_eq_empty]; ext x; simp [ρ, σ]; omega
  obtain ⟨⟨h11, -⟩, -⟩ := h K ρ σ _ ⟨⟨⟨⟨hexcl, hK01⟩, ⟨hρ, hσ⟩⟩, hdis⟩, rfl⟩
  have t1 : (fun μ x => ∃ A B, (((A ∈ K ∧ B ∈ K) ∧ A ≠ B) ∧ x ∈ B) ∧
      μ = (((ρ \ A) \ B) ∪ (σ ∩ A)) ∪ ι x) σ 3 := by
    refine ⟨S01, S23, ⟨⟨⟨Or.inl rfl, Or.inr rfl⟩, hne⟩, by simp [S23]⟩, ?_⟩
    ext x; simp [ρ, σ, S01, S23, unitCls_eq_singleton]; omega
  have t2 : (fun μ x => ∃ A B, (((A ∈ K ∧ B ∈ K) ∧ A ≠ B) ∧ x ∈ B) ∧
      μ = (((ρ \ A) \ B) ∪ (σ ∩ A)) ∪ ι x) σ 1 := by
    refine ⟨S23, S01, ⟨⟨⟨Or.inr rfl, Or.inl rfl⟩, hne.symm⟩, by simp [S01]⟩, ?_⟩
    ext x; simp [ρ, σ, S01, S23, unitCls_eq_singleton]; omega
  exact absurd ((mem_arrow_one_one.1 h11).2 σ 3 1 ⟨t1, t2⟩) (by decide)

/-- ✱117·633. \[\begin{align}&\vdash \colon\ldotp \kappa \in \text{Cls}^{2} \text{excl}.\kappa {\sim}\in 0\cup 1:(\exists \rho ,\sigma ).\rho ,\sigma \in \text{Prod}ʻ\kappa .\rho \cap \sigma =\Lambda :\supset .\\ &\Pi \text{Nc}ʻ\kappa \geq \Sigma \text{Nc}ʻ\kappa\end{align}\]

`ΠNc'κ`, `ΣNc'κ` are by their Dfs `Nc'∈_Δ'κ`, `Nc'Σ'κ` (✱114·01, ✱112·02); as sides of `≥` they
are `N₀c'∈_Δ'κ`, `N₀c'Σ'κ` (normal adjustment, ✱117·02·03). (Reading them instead as other formal
numbers under IIT would be vacuous for `ΠNc`: `AdeqPiNc` holds in every type, since `Λ ∈ t₀'κ`
makes `ΠNc't₀'κ = 0`, and the proposition would fail in an empty type.)

**Status.** proved (reading): `ΠNc'κ`, `ΣNc'κ` at the sides of `≥` are read through their Dfs
✱114·01, ✱112·02 as `Nc'∈_Δ'κ`, `Nc'Σ'κ`, normally adjusted (✱117·02·03) to `N₀c'∈_Δ'κ`,
`N₀c'Σ'κ`. -/
theorem pm117_633 {X : Type*} {K : Set (Set X)} :
    (K ∈ Cls2excl ∧ K ∉ (zero : Set (Set (Set X))) ∪ one) ∧
        (∃ ρ σ, (ρ ∈ prodK K ∧ σ ∈ prodK K) ∧ ρ ∩ σ = Λ) →
      n₀c (sel memRel K) ≥ᶜ n₀c (clsSigma K) := by
  rintro ⟨⟨hK, -⟩, ρ, σ, ⟨hρ, hσ⟩, hdis⟩
  obtain ⟨z, o, hzo⟩ := pmB2_two_sel hK hρ hσ hdis
  obtain ⟨f⟩ := pmB2_sigma_emb_pi z o hzo
  exact pmB2_ge_n₀c.2 ⟨((pmB2_clsSigmaEquiv K).toEmbedding.trans f).trans
    (pmB2_selE K).symm.toEmbedding⟩

/-- ✱117·64. \[\begin{align}\vdash \colon\ldotp \kappa \in \text{Cls}^{2} \text{excl}:(\exists \rho ,\sigma ).\rho ,\sigma \in \text{Prod}ʻ\kappa .\rho \cap \sigma =&\Lambda :\supset .\\ &\Pi \text{Nc}ʻ\kappa \geq \Sigma \text{Nc}ʻ\kappa\end{align}\]

`ΠNc'κ`, `ΣNc'κ` as in ✱117·633.

**Status.** proved (reading): `ΠNc'κ`, `ΣNc'κ` at the sides of `≥` are read through their Dfs
✱114·01, ✱112·02 and normally adjusted (✱117·02·03), as in ✱117·633. -/
theorem pm117_64 {X : Type*} {K : Set (Set X)} :
    K ∈ Cls2excl ∧ (∃ ρ σ, (ρ ∈ prodK K ∧ σ ∈ prodK K) ∧ ρ ∩ σ = Λ) →
      n₀c (sel memRel K) ≥ᶜ n₀c (clsSigma K) := by
  rintro ⟨hK, ρ, σ, ⟨hρ, hσ⟩, hdis⟩
  obtain ⟨z, o, hzo⟩ := pmB2_two_sel hK hρ hσ hdis
  obtain ⟨f⟩ := pmB2_sigma_emb_pi z o hzo
  exact pmB2_ge_n₀c.2 ⟨((pmB2_clsSigmaEquiv K).toEmbedding.trans f).trans
    (pmB2_selE K).symm.toEmbedding⟩

private theorem pmB2_prod_emb_exp {X Y : Type*} {A : Set X} {B : Set Y} (hA : A ∉ (zero : Set (Set X)) ∪ one) :
    Nonempty (↥(A ×ₐ B) ↪ ↥(clsExp A B)) := by
  obtain ⟨a₀, a₁, ⟨ha₀, ha₁⟩, ha⟩ := pmB2_two_of_not hA
  obtain ⟨f⟩ := pmB2_sigma_emb_pi (F := fun _ : ↥B => ↥A) (fun _ => ⟨a₀, ha₀⟩)
    (fun _ => ⟨a₁, ha₁⟩) (fun _ h => ha (congrArg Subtype.val h))
  exact ⟨(((pmB2_clsTimesEquiv B A).trans (Equiv.sigmaEquivProd ↥B ↥A).symm).toEmbedding.trans
    f).trans (pmB2_clsExpEquiv A B).symm.toEmbedding⟩

/-- ✱117·651. \(\vdash :\alpha {\sim}\in 0\cup 1.\supset .(\text{Nc}ʻ\alpha )^{\text{Nc}ʻ\beta }\geq \text{Nc}ʻ\alpha x_{c}\text{Nc}ʻ\beta\)

The e-text prints `x_c` for `×_c`. The sides are arithmetical formal numbers with their own
adequate types (IIT).

**Status.** proved (reading): transcription error (`x_c` for `×_c`); convention IIT (Prefatory
Statement, IV) (`AdeqExp`, `AdeqMul`). -/
theorem pm117_651 {X Y W₁ W₂ : Type*} {A : Set X} {B : Set Y}
    (h₁ : AdeqExp W₁ (n₀c A) (n₀c B)) (h₂ : AdeqMul W₂ (n₀c A) (n₀c B)) :
    A ∉ (zero : Set (Set X)) ∪ one →
      (n₀c A ^ᶜ n₀c B : Set (Set W₁)) ≥ᶜ (n₀c A ×ᶜ n₀c B : Set (Set W₂)) := by
  intro hA
  obtain ⟨a₀, -, ⟨ha₀, -⟩, -⟩ := pmB2_two_of_not hA
  have : Nonempty X := ⟨a₀⟩
  rw [pmB2_n₀c_exp, pmB2_n₀c_mul,
    pmB2_ge_nc (pmB2_AdeqExp_nc h₁ A B) (pmB2_AdeqMul_nc h₂ A B)]
  exact pmB2_prod_emb_exp hA

/-- ✱117·652. \(\vdash :\mu \in \text{N}_{0}\text{C}-\iota ʻ0-\iota ʻ1.\nu \in \text{N}_{0}\text{C}.\supset .\mu ^\nu \geq \mu \times _{c} \nu \quad[*117·651]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV) (`AdeqExp`, `AdeqMul`). -/
theorem pm117_652 {X Y W₁ W₂ : Type*} {μ : Set (Set X)} {ν : Set (Set Y)}
    (h₁ : AdeqExp W₁ μ ν) (h₂ : AdeqMul W₂ μ ν) :
    μ ∈ (N₀C \ ι zero) \ ι one ∧ ν ∈ N₀C →
      (μ ^ᶜ ν : Set (Set W₁)) ≥ᶜ (μ ×ᶜ ν : Set (Set W₂)) := by
  rintro ⟨⟨⟨⟨A, rfl⟩, hA0⟩, hA1⟩, ⟨B, rfl⟩⟩
  obtain ⟨a₀, a₁, ⟨ha₀, ha₁⟩, ha⟩ := pmB2_ne_one hA1 hA0
  refine pm117_651 h₁ h₂ fun h => ?_
  rcases h with h | ⟨x, hx⟩
  · rw [zero_eq] at h
    have : a₀ ∈ (∅ : Set X) := by rw [← Set.mem_singleton_iff.1 h]; exact ha₀
    exact this
  · rw [hx, mem_unitCls] at ha₀ ha₁
    exact ha (ha₀.trans ha₁.symm)

private theorem pmB2_cl_not_emb {X : Type*} (A : Set X) : ¬Nonempty (↥(cl A) ↪ ↥A) := by
  rintro ⟨f⟩
  exact Function.cantor_injective (fun S : Set ↥A => (f ⟨Subtype.val '' S,
    fun _ ⟨y, _, e⟩ => e ▸ y.2⟩ : ↥A))
    (fun S T h => Subtype.val_injective.image_injective (congrArg Subtype.val (f.injective h)))

/-- ✱117·66. \(\vdash .\text{Nc}ʻ\text{Cl}ʻ\alpha >\text{Nc}ʻ\alpha\) -/
theorem pm117_66 {X : Type*} {A : Set X} : n₀c (cl A) >ᶜ n₀c A := by
  rw [pmB2_gt_n₀c]
  exact ⟨⟨⟨fun a => ⟨{a.1}, Set.singleton_subset_iff.2 a.2⟩,
    fun a b h => Subtype.ext (Set.singleton_injective (congrArg Subtype.val h))⟩⟩,
    pmB2_cl_not_emb A⟩

/-- ✱117·661. \(\vdash :\mu \in \text{N}_{0}\text{C}.\supset .2^\mu >\mu \quad[*117·66.*116·72]\)

The base `2` is in a type `W` in which it exists, and the power `2^μ` at the side of `>` in an
adequate type `W₁` (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): `2` exists in its type
and `2^μ` is in an adequate type (`AdeqExp`). -/
theorem pm117_661 {X W W₁ : Type*} {μ : Set (Set X)} (h2 : (two : Set (Set W)).Nonempty)
    (h : AdeqExp W₁ (two : Set (Set W)) μ) :
    μ ∈ N₀C → ((two : Set (Set W)) ^ᶜ μ : Set (Set W₁)) >ᶜ μ := by
  rintro ⟨A, rfl⟩
  obtain ⟨a, b, hab, e2⟩ := pmB2_two_eq h2
  have : Nonempty W := ⟨a⟩
  have hne := pmB2_AdeqExp_nc (e2 ▸ h) ({a, b} : Set W) A
  rw [e2, pmB2_n₀c_exp, n₀c_eq_nc A, pmB2_gt_nc hne (pmB2_n₀c_nc A)]
  classical
  have ha : a ∈ ({a, b} : Set W) := Or.inl rfl
  have hb : b ∈ ({a, b} : Set W) := Or.inr rfl
  let ind : Set ↥A → (↥A → ↥({a, b} : Set W)) := fun S x => if x ∈ S then ⟨a, ha⟩ else ⟨b, hb⟩
  have hind : Function.Injective ind := by
    intro S T h
    ext x
    have := congrFun h x
    simp only [ind] at this
    by_cases hS : x ∈ S <;> by_cases hT : x ∈ T
    · exact ⟨fun _ => hT, fun _ => hS⟩
    · rw [ite_eq_left hS, ite_eq_right hT] at this; exact absurd (congrArg Subtype.val this) hab
    · rw [ite_eq_right hS, ite_eq_left hT] at this; exact absurd (congrArg Subtype.val this).symm hab
    · exact ⟨fun h => absurd h hS, fun h => absurd h hT⟩
  refine ⟨⟨(⟨fun x => {x}, fun x y e => Set.singleton_injective e⟩ : ↥A ↪ Set ↥A).trans
    ((⟨ind, hind⟩ : Set ↥A ↪ _).trans (pmB2_clsExpEquiv _ A).symm.toEmbedding)⟩, ?_⟩
  rintro ⟨f⟩
  exact Function.cantor_injective (fun S => f ((pmB2_clsExpEquiv _ A).symm (ind S)))
    (fun S T e => hind ((pmB2_clsExpEquiv _ A).symm.injective (f.injective e)))

/-- ✱117·67. \(\vdash :\kappa \in \text{Cls}^{2} \text{excl}.\exists !\text{Prod}ʻ\kappa .\supset .\text{Nc}ʻsʻ\kappa \geq \text{Nc}ʻ\kappa\)

`Nc's'κ`, `Nc'κ` at the sides of `≥` are `N₀c's'κ`, `N₀c'κ` (✱117·02·03). -/
theorem pm117_67 {X : Type*} {K : Set (Set X)} :
    K ∈ Cls2excl ∧ (prodK K).Nonempty → n₀c (sumCls K) ≥ᶜ n₀c K := by
  rintro ⟨hK, hP⟩
  obtain ⟨R, hR⟩ := pmB2_prodK_nonempty_iff.1 hP
  let e := pmB2_selE K ⟨R, hR⟩
  refine pmB2_ge_n₀c.2 ⟨⟨fun A => ⟨(e A).1, A.1, A.2, (e A).2⟩, fun A B h => ?_⟩⟩
  have h' : (e A).1 = (e B).1 := congrArg Subtype.val h
  exact Subtype.ext (pmB2_excl_iff.1 hK A B (e A).1 A.2 B.2 (e A).2 (h' ▸ (e B).2))

/-- ✱117·68. \[\begin{align}\vdash :R,S\in {\in}_{\Delta}ʻ\kappa .R\dot{\cap} S=\dot{\Lambda} .T=\hat{P} &\hat{\rho} \{\rho \in \kappa .P=R\upharpoonright -\iota ʻ\rho \unicode{x228d} S\upharpoonright \iota ʻ\rho\}.\\ &\supset .T\in 1\rightarrow 1.\text{D}ʻT\subset {\in}_{\Delta}ʻ\kappa .\text{ᗡ}ʻT=\kappa\end{align}\]

`R ↾ −ι'ρ ∪̇ S ↾ ι'ρ` is `R ↾ (ι ρ)ᶜ ⊍ S ↾ ι ρ` (`↾` binds tighter than `∪̇`); `Λ̇` is `rNull`;
the hypothesis `T = P̂ρ̂{…}` is an equation. -/
theorem pm117_68 {X : Type*} {K : Set (Set X)} {R S : X → Set X → Prop}
    {T : (X → Set X → Prop) → Set X → Prop} :
    ((R ∈ sel memRel K ∧ S ∈ sel memRel K) ∧ R ⩀ S = rNull) ∧
        T = (fun P ρ => ρ ∈ K ∧ P = R ↾ (ι ρ)ᶜ ⊍ S ↾ ι ρ) →
      (T ∈ arrow one one ∧ dom T ⊆ sel memRel K) ∧ codom T = K := by
  rintro ⟨⟨⟨hR, hS⟩, hRS⟩, rfl⟩
  obtain ⟨r1, r2, r3⟩ := pmB2_mem_sel.1 hR
  obtain ⟨s1, s2, s3⟩ := pmB2_mem_sel.1 hS
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro P P' ρ ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
  · rintro P ρ ρ' ⟨⟨hρ, rfl⟩, ⟨-, e⟩⟩
    by_contra hne
    obtain ⟨x, hx⟩ := pmB2_sel_ex hS hρ
    have h1 : (R ↾ (ι ρ)ᶜ ⊍ S ↾ ι ρ) x ρ := Or.inr ⟨hx, rfl⟩
    rw [e] at h1
    rcases h1 with ⟨hRx, -⟩ | ⟨-, h2⟩
    · have : (R ⩀ S) x ρ := ⟨hRx, hx⟩
      rw [hRS] at this
      exact rNull_apply _ _ this
    · exact hne (mem_unitCls.1 h2)
  · rintro P ⟨ρ, hρ, rfl⟩
    refine pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩
    · rintro x y A ⟨hx | hx, hy | hy⟩
      · exact r1 x y A ⟨hx.1, hy.1⟩
      · exact absurd (mem_unitCls.1 hy.2) hx.2
      · exact absurd (mem_unitCls.1 hx.2) hy.2
      · exact s1 x y A ⟨hx.1, hy.1⟩
    · rintro x A (hx | hx)
      · exact r2 x A hx.1
      · exact s2 x A hx.1
    · ext A
      constructor
      · rintro ⟨x, hx | hx⟩
        · exact pmB2_sel_codom hR hx.1
        · exact pmB2_sel_codom hS hx.1
      · intro hA
        by_cases e : A = ρ
        · subst e
          obtain ⟨x, hx⟩ := pmB2_sel_ex hS hA
          exact ⟨x, Or.inr ⟨hx, rfl⟩⟩
        · obtain ⟨x, hx⟩ := pmB2_sel_ex hR hA
          exact ⟨x, Or.inl ⟨hx, e⟩⟩
  · ext ρ
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

/-- ✱117·681. \(\vdash :(\exists R,S).R,S\in {\in}_{\Delta}ʻ\kappa .R\dot{\cap} S=\dot{\Lambda} .\supset .\text{Nc}ʻ{\in}_{\Delta}ʻ\kappa \geq \text{Nc}ʻ\kappa \quad [*117·68·22]\)

`Nc'∈_Δ'κ`, `Nc'κ` at the sides of `≥` are `N₀c'∈_Δ'κ`, `N₀c'κ` (✱117·02·03). -/
theorem pm117_681 {X : Type*} {K : Set (Set X)} :
    (∃ R S, (R ∈ sel memRel K ∧ S ∈ sel memRel K) ∧ R ⩀ S = rNull) →
      n₀c (sel memRel K) ≥ᶜ n₀c K := by
  rintro ⟨R, S, hRS, h0⟩
  obtain ⟨⟨h11, hdom⟩, -⟩ := pm117_68 (T := fun P ρ => ρ ∈ K ∧ P = R ↾ (ι ρ)ᶜ ⊍ S ↾ ι ρ)
    ⟨⟨hRS, h0⟩, rfl⟩
  obtain ⟨-, h2⟩ := mem_arrow_one_one.1 h11
  refine pmB2_ge_n₀c.2 ⟨⟨fun ρ => ⟨R ↾ (ι ρ.1)ᶜ ⊍ S ↾ ι ρ.1, hdom ⟨ρ.1, ρ.2, rfl⟩⟩,
    fun ρ ρ' h => Subtype.ext (h2 _ _ _ ⟨⟨ρ.2, rfl⟩, ⟨ρ'.2, ?_⟩⟩)⟩⟩
  have := congrArg Subtype.val h
  exact this

private theorem pmB2_sel_sub {X : Type*} {K L : Set (Set X)} (h : K ⊆ L) {R : X → Set X → Prop}
    (hR : R ∈ sel memRel L) : R ↾ K ∈ sel memRel K := by
  obtain ⟨r1, r2, -⟩ := pmB2_mem_sel.1 hR
  refine pmB2_mem_sel.2 ⟨fun x y A ⟨hx, hy⟩ => r1 x y A ⟨hx.1, hy.1⟩, fun x A hx => r2 x A hx.1,
    Set.ext fun A => ⟨fun ⟨_, _, hA⟩ => hA, fun hA => ?_⟩⟩
  obtain ⟨x, hx⟩ := pmB2_sel_ex hR (h hA)
  exact ⟨x, hx, hA⟩

/-- ✱117·682. \(\vdash :\kappa \subset \lambda .\exists !{\in}_{\Delta}ʻ(\lambda -\kappa ).\supset .\text{Nc}ʻ{\in}_{\Delta}ʻ\lambda \geq \text{Nc}ʻ{\in}_{\Delta}ʻ\kappa\) -/
theorem pm117_682 {X : Type*} {K L : Set (Set X)} :
    K ⊆ L ∧ (sel memRel (L \ K)).Nonempty → n₀c (sel memRel L) ≥ᶜ n₀c (sel memRel K) := by
  rintro ⟨hKL, S₀, hS₀⟩
  have mem : ∀ R, R ∈ sel memRel K → R ⊍ S₀ ∈ sel memRel L := by
    intro R hR
    refine pmB2_mem_sel.2 ⟨?_, ?_, ?_⟩
    · rintro x y A ⟨hx | hx, hy | hy⟩
      · exact (pmB2_mem_sel.1 hR).1 x y A ⟨hx, hy⟩
      · exact absurd (pmB2_sel_codom hR hx) (pmB2_sel_codom hS₀ hy).2
      · exact absurd (pmB2_sel_codom hR hy) (pmB2_sel_codom hS₀ hx).2
      · exact (pmB2_mem_sel.1 hS₀).1 x y A ⟨hx, hy⟩
    · rintro x A (hx | hx)
      · exact (pmB2_mem_sel.1 hR).2.1 x A hx
      · exact (pmB2_mem_sel.1 hS₀).2.1 x A hx
    · ext A
      constructor
      · rintro ⟨x, hx | hx⟩
        · exact hKL (pmB2_sel_codom hR hx)
        · exact (pmB2_sel_codom hS₀ hx).1
      · intro hA
        by_cases hK : A ∈ K
        · obtain ⟨x, hx⟩ := pmB2_sel_ex hR hK; exact ⟨x, Or.inl hx⟩
        · obtain ⟨x, hx⟩ := pmB2_sel_ex hS₀ ⟨hA, hK⟩; exact ⟨x, Or.inr hx⟩
  refine pmB2_ge_n₀c.2 ⟨⟨fun R => ⟨R.1 ⊍ S₀, mem R.1 R.2⟩, fun R R' h => ?_⟩⟩
  have e : R.1 ⊍ S₀ = R'.1 ⊍ S₀ := congrArg Subtype.val h
  have key : ∀ (R R' : ↥(sel memRel K)), R.1 ⊍ S₀ = R'.1 ⊍ S₀ → ∀ x A, R.1 x A → R'.1 x A := by
    intro R R' e x A hx
    have : (R'.1 ⊍ S₀) x A := e ▸ Or.inl hx
    rcases this with h | h
    · exact h
    · exact absurd (pmB2_sel_codom R.2 hx) (pmB2_sel_codom hS₀ h).2
  apply Subtype.ext
  funext x A
  exact propext ⟨key R R' e x A, key R' R e.symm x A⟩

/-- ✱117·683. \[\begin{align}\vdash \colon\ldotp \kappa \subset \lambda .\exists !{\in}_{\Delta}ʻ(\lambda -\kappa ):(\exists R,S).&R,S\in {\in}_{\Delta}ʻ\kappa .R\dot{\cap} S=\dot{\Lambda} :\supset .\\ &\text{Nc}ʻ{\in}_{\Delta}ʻ\lambda \geq \text{Nc}ʻ\kappa \quad[*117·681·682]\end{align}\] -/
theorem pm117_683 {X : Type*} {K L : Set (Set X)} :
    (K ⊆ L ∧ (sel memRel (L \ K)).Nonempty) ∧
        (∃ R S, (R ∈ sel memRel K ∧ S ∈ sel memRel K) ∧ R ⩀ S = rNull) →
      n₀c (sel memRel L) ≥ᶜ n₀c K :=
  fun ⟨h1, h2⟩ => pmB2_ge_trans (pm117_682 h1) (pm117_681 h2)

/-- ✱117·684. \[\begin{align}\vdash :\kappa \subset \lambda .\exists !{\in}_{\Delta}ʻ\lambda :(\exists R,S).&R,S\in {\in}_{\Delta}ʻ\kappa .R\dot{\cap} S=\dot{\Lambda} :\supset .\\ &\text{Nc}ʻ{\in}_{\Delta}ʻ\lambda \geq \text{Nc}ʻ\kappa \quad[*117·683.*88·22]\end{align}\] -/
theorem pm117_684 {X : Type*} {K L : Set (Set X)} :
    (K ⊆ L ∧ (sel memRel L).Nonempty) ∧
        (∃ R S, (R ∈ sel memRel K ∧ S ∈ sel memRel K) ∧ R ⩀ S = rNull) →
      n₀c (sel memRel L) ≥ᶜ n₀c K := by
  rintro ⟨⟨hKL, R₀, hR₀⟩, h2⟩
  exact pm117_683 ⟨⟨hKL, R₀ ↾ (L \ K), pmB2_sel_sub Set.sdiff_subset hR₀⟩, h2⟩

end PrincipiaMathematica
