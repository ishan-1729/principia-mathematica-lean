import PrincipiaMathematica.Defs.Part3

/-!
# Part III, Section B: Addition, multiplication and exponentiation

Volume 2. Numbers: ✱110, ✱111, ✱112, ✱113, ✱114.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w u' v' w'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'} {ε : Type v'} {ζ : Type w'}

/-! ### Helper lemmas (not propositions of PM)

Similarity is handled through `sm_iff_nonempty_equiv`; the arithmetical class-sum, class-product,
`Σ'κ` and `∈_Δ'κ` are compared with Lean's `⊕`, `×`, `Σ` and `Π` types. -/

section Helpers

private theorem sm_of_equiv {A : Set α} {B : Set β} (e : A ≃ B) : sm A B :=
  sm_iff_nonempty_equiv.2 ⟨e⟩

/-- A class which is the injective image of `A` is similar to `A`. -/
private theorem sm_of_injOn {A : Set α} {S : Set δ} (f : α → δ)
    (hf : ∀ x y, x ∈ A → y ∈ A → f x = f y → x = y) (hS : ∀ z, z ∈ S ↔ ∃ x, x ∈ A ∧ z = f x) :
    sm S A := by
  refine sm_of_equiv (Equiv.ofBijective (fun a : A => (⟨f a, (hS _).2 ⟨a, a.2, rfl⟩⟩ : S))
    ⟨fun a b h => Subtype.ext (hf a b a.2 b.2 (congrArg Subtype.val h)), fun s => ?_⟩).symm
  obtain ⟨x, hx, e⟩ := (hS s).1 s.2
  exact ⟨⟨x, hx⟩, Subtype.ext e.symm⟩

private theorem inter_eq_null_iff {G H : Set γ} : G ∩ H = Λ ↔ Disjoint G H := by
  rw [Null_eq_empty, Set.disjoint_iff_inter_eq_empty]

private noncomputable def unionEquivOfNull {G H : Set γ} (h : G ∩ H = Λ) : ↥(G ∪ H) ≃ G ⊕ H := by
  classical
  exact Equiv.Set.union (inter_eq_null_iff.1 h)

private theorem cardAdd_of {μ : Set (Set α)} {ν : Set (Set β)} {A : Set α} {B : Set β}
    (hμ : μ = n₀c A) (hν : ν = n₀c B) : (μ +ᶜ ν : Set (Set γ)) = nc γ (A +ₐ B) := by
  subst hμ hν; exact n₀c_cardAdd_n₀c A B

private theorem empty_cardAdd (ν : Set (Set β)) : ((∅ : Set (Set α)) +ᶜ ν : Set (Set γ)) = ∅ :=
  cardAdd_eq_empty_of_left (fun A h => n₀c_ne_empty A h.symm) ν

private theorem cardAdd_empty (μ : Set (Set α)) : (μ +ᶜ (∅ : Set (Set β)) : Set (Set γ)) = ∅ :=
  cardAdd_eq_empty_of_right μ (fun A h => n₀c_ne_empty A h.symm)

private theorem sm_img_empty : (sm ʻʻ (∅ : Set (Set α)) : Set (Set γ)) = ∅ := by
  ext X; simp [img]

private theorem mem_sm_img_n₀c {A : Set α} {G : Set γ} : G ∈ sm ʻʻ n₀c A ↔ sm G A := by
  rw [sm_img_n₀c]; exact Iff.rfl

/-- A member of `NC` is `Λ` or a homogeneous cardinal. -/
private theorem NC_cases {μ : Set (Set α)} (h : μ ∈ NC β) : μ = ∅ ∨ ∃ A, μ = n₀c A := by
  obtain ⟨A', rfl⟩ := h
  rcases Set.eq_empty_or_nonempty (nc α A') with h0 | ⟨X, hX⟩
  · exact Or.inl h0
  · exact Or.inr ⟨X, nc_eq_n₀c_of_mem hX⟩

/-- `Nc(ξ)'α` is `Λ` or the homogeneous cardinal of a member. -/
private theorem nc_cases (E : Type*) (A : Set α) :
    nc E A = ∅ ∨ ∃ P : Set E, sm P A ∧ nc E A = n₀c P := by
  rcases Set.eq_empty_or_nonempty (nc E A) with h0 | ⟨X, hX⟩
  · exact Or.inl h0
  · exact Or.inr ⟨X, hX, nc_eq_n₀c_of_mem hX⟩

private theorem n₀c_mem_NC (A : Set α) : n₀c A ∈ NC α := ⟨A, n₀c_eq_nc A⟩

/-- Splitting a class equivalent to `A ⊕ B` into two exclusive parts. -/
private theorem split_of_equiv {X : Set γ} {A : Set α} {B : Set β} (e : X ≃ A ⊕ B) :
    ∃ G H : Set γ, ((sm G A ∧ sm H B) ∧ G ∩ H = Λ) ∧ X = G ∪ H := by
  let f : A → γ := fun a => (e.symm (Sum.inl a) : γ)
  let g : B → γ := fun b => (e.symm (Sum.inr b) : γ)
  have hf : Function.Injective f := fun a a' h =>
    Sum.inl_injective (e.symm.injective (Subtype.ext h))
  have hg : Function.Injective g := fun b b' h =>
    Sum.inr_injective (e.symm.injective (Subtype.ext h))
  refine ⟨Set.range f, Set.range g, ⟨⟨sm_of_equiv (Equiv.ofInjective f hf).symm,
    sm_of_equiv (Equiv.ofInjective g hg).symm⟩, ?_⟩, ?_⟩
  · rw [inter_eq_null_iff, Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact Sum.inr_ne_inl (e.symm.injective (Subtype.ext hb))
  · ext x
    constructor
    · intro hx
      rcases h : e ⟨x, hx⟩ with a | b
      · exact Or.inl ⟨a, by simp [f, ← h]⟩
      · exact Or.inr ⟨b, by simp [g, ← h]⟩
    · rintro (⟨a, rfl⟩ | ⟨b, rfl⟩)
      · exact (e.symm (Sum.inl a)).2
      · exact (e.symm (Sum.inr b)).2

/-- `ξ ∈ Nc'(α + β)` iff `ξ` splits into exclusive parts similar to `α` and `β` (✱110·152). -/
private theorem mem_nc_clsSum {A : Set α} {B : Set β} {X : Set γ} :
    X ∈ nc γ (A +ₐ B) ↔ ∃ G H : Set γ, ((sm G A ∧ sm H B) ∧ G ∩ H = Λ) ∧ X = G ∪ H := by
  constructor
  · intro h
    obtain ⟨e⟩ := mem_nc_iff_equiv.1 h
    exact split_of_equiv (e.trans (clsSumEquiv A B))
  · rintro ⟨G, H, ⟨⟨hG, hH⟩, hGH⟩, rfl⟩
    obtain ⟨eG⟩ := sm_iff_nonempty_equiv.1 hG
    obtain ⟨eH⟩ := sm_iff_nonempty_equiv.1 hH
    exact sm_of_equiv ((unionEquivOfNull hGH).trans ((eG.sumCongr eH).trans (clsSumEquiv A B).symm))

private theorem zero_eq_nc_empty : (zero : Set (Set γ)) = nc γ (∅ : Set α) := by
  ext X
  rw [mem_nc_iff_equiv, zero_eq, Set.mem_singleton_iff]
  constructor
  · rintro rfl; exact ⟨Equiv.equivOfIsEmpty _ _⟩
  · rintro ⟨e⟩; exact Set.eq_empty_iff_forall_notMem.2 fun x hx => (e ⟨x, hx⟩).2

private theorem one_eq_nc_unitCls (x : α) : (one : Set (Set γ)) = nc γ (ι x) := by
  ext X
  rw [mem_nc_iff_equiv, unitCls_eq_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    rw [unitCls_eq_singleton]; exact ⟨Equiv.ofUnique _ _⟩
  · rintro ⟨e⟩
    refine ⟨(e.symm ⟨x, rfl⟩ : γ), Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
    · have : e ⟨z, hz⟩ = ⟨x, rfl⟩ := Subsingleton.elim _ _
      exact congrArg Subtype.val (e.symm_apply_eq.2 this.symm).symm
    · rw [mem_unitCls.1 hz]
      exact (e.symm ⟨x, rfl⟩).2

private theorem two_eq_nc_pair {a b : α} (hab : a ≠ b) : (two : Set (Set γ)) = nc γ ({a, b} : Set α) := by
  have hc : Nat.card ↥({a, b} : Set α) = 2 := by rw [Nat.card_coe_set_eq, Set.ncard_pair hab]
  have hfin : Finite ↥({a, b} : Set α) := Set.toFinite _
  ext X
  rw [mem_nc_iff_equiv]
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    rw [unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]
    have : Finite ↥({x, y} : Set γ) := Set.toFinite _
    apply Finite.card_eq.1
    rw [Nat.card_coe_set_eq, Set.ncard_pair hxy, hc]
  · rintro ⟨e⟩
    have h2 : X.ncard = 2 := by rw [← Nat.card_coe_set_eq, Nat.card_congr e, hc]
    obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.1 h2
    exact ⟨x, y, hxy, by rw [unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]⟩

private theorem nc_eq_of_sm {A : Set α} {B : Set β} (h : sm A B) : nc γ A = nc γ B := nc_eq_nc_of_sm h

private theorem sm_clsSum_empty (A : Set α) : sm (A +ₐ (∅ : Set β)) A :=
  sm_of_equiv ((clsSumEquiv A ∅).trans (Equiv.sumEmpty _ _))

private theorem sm_empty_clsSum (B : Set β) : sm ((∅ : Set α) +ₐ B) B :=
  sm_of_equiv ((clsSumEquiv ∅ B).trans (Equiv.emptySum _ _))

private theorem sm_clsSum_comm (A : Set α) (B : Set β) : sm (A +ₐ B) (B +ₐ A) :=
  sm_of_equiv ((clsSumEquiv A B).trans ((Equiv.sumComm _ _).trans (clsSumEquiv B A).symm))

/-- There is a one-one map of `γ ⊕ γ` into `Set γ` (used for ✱110·17). -/
private theorem exists_inj_sum_set (γ : Type w) : ∃ f : γ ⊕ γ → Set γ, Function.Injective f := by
  classical
  rcases isEmpty_or_nonempty γ with h | ⟨⟨a⟩⟩
  · exact ⟨fun _ => ∅, fun x => by rcases x with x | x <;> exact isEmptyElim x⟩
  · refine ⟨Sum.elim (fun x => {x}) (fun y => if y = a then ∅ else {a, y}), ?_⟩
    rintro (x | y) (x' | y') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [Set.singleton_eq_singleton_iff.1 h]
    · exfalso
      split_ifs at h with hy
      · exact Set.singleton_ne_empty _ h
      · have h1 : a ∈ ({x} : Set γ) := h ▸ Set.mem_insert a _
        have h2 : y' ∈ ({x} : Set γ) := h ▸ Set.mem_insert_of_mem a rfl
        exact hy (h2.trans h1.symm)
    · exfalso
      split_ifs at h with hy
      · exact Set.singleton_ne_empty _ h.symm
      · have h1 : a ∈ ({x'} : Set γ) := h ▸ Set.mem_insert a _
        have h2 : y ∈ ({x'} : Set γ) := h ▸ Set.mem_insert_of_mem a rfl
        exact hy (h2.trans h1.symm)
    · split_ifs at h with hy hy'
      · rw [hy, hy']
      · exact absurd h.symm (Set.insert_nonempty _ _).ne_empty
      · exact absurd h (Set.insert_nonempty _ _).ne_empty
      · have : y ∈ ({a, y'} : Set γ) := h ▸ Set.mem_insert_of_mem a rfl
        rcases this with h' | h'
        · exact absurd h' hy
        · rw [h']

private theorem nc_set_clsSum_nonempty (A B : Set γ) : (nc (Set γ) (A +ₐ B)).Nonempty := by
  obtain ⟨f, hf⟩ := exists_inj_sum_set γ
  exact nc_nonempty_iff.2 ⟨fun r => f (Sum.map Subtype.val Subtype.val (clsSumEquiv A B r)),
    hf.comp ((Sum.map_injective.2 ⟨Subtype.val_injective, Subtype.val_injective⟩).comp
      (clsSumEquiv A B).injective)⟩

private theorem nc_up_nonempty (A : Set α) : (nc (Set α) A).Nonempty :=
  nc_nonempty_iff.2 ⟨fun a => {a.1}, fun a b h => Subtype.ext (Set.singleton_eq_singleton_iff.1 h)⟩

private theorem nc_rel_nonempty (A : Set α) : (nc (α → α → Prop) A).Nonempty :=
  nc_nonempty_iff.2 ⟨fun a => (a.1 ↓ a.1 : α → α → Prop),
    fun a b h => Subtype.ext (couple_eq_couple_iff.1 h).1⟩

private theorem up1_eq (μ : Set (Set α)) : up1 μ = sm ʻʻ μ := by
  rw [up1, typ_eq_univ, Set.inter_univ]

private theorem down00_eq (μ : Set (Set α)) : down00 μ = sm ʻʻ μ := by
  rw [down00, typ_eq_univ, Set.inter_univ]

private theorem n1c_eq (A : Set α) : n1c A = nc (Set α) A := by
  rw [n1c, typ_eq_univ, Set.inter_univ]

private theorem n₀₀c_eq (A : Set α) : n₀₀c A = nc (α → α → Prop) A := by
  rw [n₀₀c, typ_eq_univ, Set.inter_univ]

private theorem couple_cnv (x : α) (y : β) : (x ↓ y)˘ = y ↓ x := by
  funext a b; simp [cnv, couple_apply, and_comm]

private theorem two_eq_n₀c_pair {x y : α} (h : x ≠ y) :
    (two : Set (Set α)) = n₀c ({x, y} : Set α) := by
  rw [two_eq_nc_pair h, n₀c_eq_nc]

end Helpers

section Helpers111

private theorem mem_smbar_iff {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ∈ smbar A B ↔ (R ∈ arrow one one ∧ A = dom R) ∧ B = codom R := Iff.rfl

private theorem mem_smsmbar_iff {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop} :
    T ∈ smsmbar K L ↔ (T ∈ arrow one one ∧ sumCls L = codom T) ∧ K = imgRel T ʻʻ L := Iff.rfl

private theorem mem_imgRel_img {T : α → β → Prop} {L : Set (Set β)} {u : Set α} :
    u ∈ imgRel T ʻʻ L ↔ ∃ B, B ∈ L ∧ u = T ʻʻ B := Iff.rfl

private theorem oneone_cnv {R : α → β → Prop} : R ∈ arrow one one ↔ R˘ ∈ arrow one one := by
  rw [mem_arrow_one_one, mem_arrow_one_one]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun x y z h => h2 z x y h, fun x y z h => h1 y z x h⟩,
    fun ⟨h1, h2⟩ => ⟨fun x y z h => h2 z x y h, fun x y z h => h1 y z x h⟩⟩

private theorem oneone_relProd {S : α → β → Prop} {T : β → γ → Prop} (hS : S ∈ arrow one one)
    (hT : T ∈ arrow one one) : S ⨾ T ∈ arrow one one := by
  obtain ⟨s1, s2⟩ := mem_arrow_one_one.1 hS
  obtain ⟨t1, t2⟩ := mem_arrow_one_one.1 hT
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro x y z ⟨⟨u, hxu, huz⟩, ⟨v, hyv, hvz⟩⟩
    have : u = v := t1 u v z ⟨huz, hvz⟩
    subst this
    exact s1 x y u ⟨hxu, hyv⟩
  · rintro x y z ⟨⟨u, hxu, huy⟩, ⟨v, hxv, hvz⟩⟩
    have : u = v := s2 x u v ⟨hxu, hxv⟩
    subst this
    exact t2 u y z ⟨huy, hvz⟩

private theorem oneone_cres {T : α → β → Prop} (hT : T ∈ arrow one one) (B : Set β) :
    T ↾ B ∈ arrow one one := by
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hT
  exact mem_arrow_one_one.2 ⟨fun x y z ⟨hx, hy⟩ => h1 x y z ⟨hx.1, hy.1⟩,
    fun x y z ⟨hy, hz⟩ => h2 x y z ⟨hy.1, hz.1⟩⟩

private theorem dom_cres {T : α → β → Prop} {B : Set β} : dom (T ↾ B) = T ʻʻ B := by
  ext x; exact ⟨fun ⟨y, hxy, hy⟩ => ⟨y, hy, hxy⟩, fun ⟨y, hy, hxy⟩ => ⟨y, hxy, hy⟩⟩

private theorem codom_cres {T : α → β → Prop} {B : Set β} (hB : B ⊆ codom T) :
    codom (T ↾ B) = B := by
  ext y
  exact ⟨fun ⟨_, _, hy⟩ => hy, fun hy => let ⟨x, hx⟩ := hB hy; ⟨x, hx, hy⟩⟩

private theorem cres_mem_smbar {T : α → β → Prop} {B : Set β} (hT : T ∈ arrow one one)
    (hB : B ⊆ codom T) : T ↾ B ∈ smbar (T ʻʻ B) B :=
  ⟨⟨oneone_cres hT B, dom_cres.symm⟩, (codom_cres hB).symm⟩

private theorem sm_img_of_oneone {T : α → β → Prop} {B : Set β} (hT : T ∈ arrow one one)
    (hB : B ⊆ codom T) : sm (T ʻʻ B) B :=
  ⟨T ↾ B, cres_mem_smbar hT hB⟩

private theorem img_inj {T : α → β → Prop} (hT : T ∈ arrow one one) {B B' : Set β}
    (hB : B ⊆ codom T) (hB' : B' ⊆ codom T) (h : T ʻʻ B = T ʻʻ B') : B = B' := by
  obtain ⟨-, h2⟩ := mem_arrow_one_one.1 hT
  have key : ∀ {B B' : Set β}, B ⊆ codom T → T ʻʻ B = T ʻʻ B' → B ⊆ B' := by
    intro B B' hB h y hy
    obtain ⟨x, hx⟩ := hB hy
    have : x ∈ T ʻʻ B' := h ▸ ⟨y, hy, hx⟩
    obtain ⟨y', hy', hxy'⟩ := this
    rw [h2 x y y' ⟨hx, hxy'⟩]; exact hy'
  exact Set.Subset.antisymm (key hB h) (key hB' h.symm)

private theorem img_codom (T : α → β → Prop) : T ʻʻ codom T = dom T := by
  ext x; exact ⟨fun ⟨y, _, h⟩ => ⟨y, h⟩, fun ⟨y, h⟩ => ⟨y, ⟨x, h⟩, h⟩⟩

private theorem subset_sumCls {L : Set (Set β)} {B : Set β} (h : B ∈ L) : B ⊆ sumCls L :=
  fun _ hy => ⟨B, h, hy⟩

private theorem sumCls_imgRel_img (T : α → β → Prop) (L : Set (Set β)) :
    sumCls (imgRel T ʻʻ L) = T ʻʻ sumCls L := by
  ext x
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, y, hy, hxy⟩; exact ⟨y, ⟨B, hB, hy⟩, hxy⟩
  · rintro ⟨y, ⟨B, hB, hy⟩, hxy⟩; exact ⟨T ʻʻ B, ⟨B, hB, rfl⟩, y, hy, hxy⟩

private theorem dom_imgRel_cres (T : α → β → Prop) (L : Set (Set β)) :
    dom (imgRel T ↾ L) = imgRel T ʻʻ L := dom_cres

private theorem codom_imgRel_cres (T : α → β → Prop) (L : Set (Set β)) :
    codom (imgRel T ↾ L) = L :=
  codom_cres fun B _ => ⟨T ʻʻ B, rfl⟩

private theorem imgRel_cres_oneone {T : α → β → Prop} {L : Set (Set β)} (hT : T ∈ arrow one one)
    (hL : sumCls L ⊆ codom T) : imgRel T ↾ L ∈ arrow one one := by
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro u v B ⟨⟨hu, -⟩, ⟨hv, -⟩⟩
    exact (show u = _ from hu).trans (show v = _ from hv).symm
  · rintro u B B' ⟨⟨hB, hBL⟩, ⟨hB', hB'L⟩⟩
    exact img_inj hT ((subset_sumCls hBL).trans hL) ((subset_sumCls hB'L).trans hL)
      ((show u = _ from hB).symm.trans (show u = _ from hB'))

private theorem imgRel_cres_mem_smbar {T : α → β → Prop} {L : Set (Set β)}
    (hT : T ∈ arrow one one) (hL : sumCls L ⊆ codom T) :
    imgRel T ↾ L ∈ smbar (imgRel T ʻʻ L) L :=
  ⟨⟨imgRel_cres_oneone hT hL, (dom_imgRel_cres T L).symm⟩, (codom_imgRel_cres T L).symm⟩

private theorem mem_Cnv_img {X : Set (β → α → Prop)} {R : α → β → Prop} :
    R ∈ Cnv ʻʻ X ↔ R˘ ∈ X :=
  ⟨fun ⟨P, hP, h⟩ => by rw [Cnv_iff.1 h]; exact hP, fun h => ⟨R˘, h, Cnv_iff.2 rfl⟩⟩

private theorem mem_smbar_cnv {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ∈ smbar A B ↔ R˘ ∈ smbar B A := by
  rw [mem_smbar_iff, mem_smbar_iff, ← oneone_cnv]
  have h1 : dom R˘ = codom R := rfl
  have h2 : codom R˘ = dom R := rfl
  rw [h1, h2]
  tauto

private theorem smbar_eq_Cnv_img (A : Set α) (B : Set β) : smbar A B = Cnv ʻʻ smbar B A := by
  ext R; rw [mem_Cnv_img]; exact mem_smbar_cnv

/-- `ψ(R'y)` when `y` has exactly the referent `a`. -/
private theorem desc_of_unique {R : α → β → Prop} {y : β} {a : α} (h : ∀ x, R x y ↔ x = a)
    {ψ : α → Prop} : Desc R y ψ ↔ ψ a :=
  TheIs_iff_of_unique h

private theorem edesc_of_desc {R : α → β → Prop} {y : β} {ψ : α → Prop} (h : Desc R y ψ) :
    EDesc R y := let ⟨b, hb, _⟩ := h; ⟨b, hb⟩

private theorem unique_of_oneCls {S : α → β → Prop} (hS : S ∈ arrow one Cls) {a : α} {y : β}
    (h : S a y) : ∀ x, S x y ↔ x = a :=
  fun x => ⟨fun hx => mem_arrow_one_Cls.1 hS x a y ⟨hx, h⟩, fun e => e ▸ h⟩

private theorem oneCls_of_oneone {S : α → β → Prop} (hS : S ∈ arrow one one) : S ∈ arrow one Cls :=
  mem_arrow_one_Cls.2 (mem_arrow_one_one.1 hS).1

/-- The union of a family of correlators, one for each `β ∈ λ`, of `S'β` with `β`. -/
private theorem union_corr {S : Set α → Set β → Prop} {L : Set (Set β)}
    {Ps : Set (α → β → Prop)} (hL : L ∈ Cls2excl) (hSL : S ʻʻ L ∈ Cls2excl)
    (hS : S ∈ arrow one one)
    (h1 : ∀ P, P ∈ Ps → ∃ A B, (B ∈ L ∧ S A B) ∧ P ∈ smbar A B)
    (h2 : ∀ B, B ∈ L → ∃ A P, (S A B ∧ P ∈ Ps) ∧ P ∈ smbar A B)
    (h3 : ∀ P P', P ∈ Ps → P' ∈ Ps → codom P = codom P' → P = P') :
    sumRel Ps ∈ smbar (sumCls (S ʻʻ L)) (sumCls L) ∧ ∀ P, P ∈ Ps → sumRel Ps ↾ codom P = P := by
  obtain ⟨s1, s2⟩ := mem_arrow_one_one.1 hS
  have hexcl : ∀ (B B' : Set β) (y : β), B ∈ L → B' ∈ L → y ∈ B → y ∈ B' → B = B' := by
    intro B B' y hB hB' hy hy'
    by_contra hne
    have := hL B B' ⟨⟨hB, hB'⟩, hne⟩
    have hy2 : y ∈ B ∩ B' := ⟨hy, hy'⟩
    rw [this, Null_eq_empty] at hy2; exact hy2
  have hexcl' : ∀ (A A' : Set α) (x : α), A ∈ S ʻʻ L → A' ∈ S ʻʻ L → x ∈ A → x ∈ A' → A = A' := by
    intro A A' x hA hA' hx hx'
    by_contra hne
    have := hSL A A' ⟨⟨hA, hA'⟩, hne⟩
    have hx2 : x ∈ A ∩ A' := ⟨hx, hx'⟩
    rw [this, Null_eq_empty] at hx2; exact hx2
  -- `P` is determined by any relatum
  have hsame : ∀ P P' y, P ∈ Ps → P' ∈ Ps → y ∈ codom P → y ∈ codom P' → P = P' := by
    intro P P' y hP hP' hy hy'
    obtain ⟨A, B, ⟨hB, -⟩, hPs⟩ := h1 P hP
    obtain ⟨A', B', ⟨hB', -⟩, hP's⟩ := h1 P' hP'
    apply h3 P P' hP hP'
    rw [← hPs.2, ← hP's.2] at *
    exact hexcl B B' y hB hB' hy hy'
  have hsame' : ∀ P P' x, P ∈ Ps → P' ∈ Ps → x ∈ dom P → x ∈ dom P' → P = P' := by
    intro P P' x hP hP' hx hx'
    obtain ⟨A, B, ⟨hB, hAB⟩, hPs⟩ := h1 P hP
    obtain ⟨A', B', ⟨hB', hAB'⟩, hP's⟩ := h1 P' hP'
    rw [← hPs.1.2] at hx; rw [← hP's.1.2] at hx'
    have hAA : A = A' := hexcl' A A' x ⟨B, hB, hAB⟩ ⟨B', hB', hAB'⟩ hx hx'
    subst hAA
    have hBB : B = B' := s2 A B B' ⟨hAB, hAB'⟩
    subst hBB
    exact h3 P P' hP hP' (hPs.2.symm.trans hP's.2)
  refine ⟨⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨P, hP, hxz⟩, ⟨P', hP', hyz⟩⟩
    have := hsame P P' z hP hP' ⟨x, hxz⟩ ⟨y, hyz⟩
    subst this
    obtain ⟨A, B, -, hPs⟩ := h1 P hP
    exact (mem_arrow_one_one.1 hPs.1.1).1 x y z ⟨hxz, hyz⟩
  · rintro x y z ⟨⟨P, hP, hxy⟩, ⟨P', hP', hxz⟩⟩
    have := hsame' P P' x hP hP' ⟨y, hxy⟩ ⟨z, hxz⟩
    subst this
    obtain ⟨A, B, -, hPs⟩ := h1 P hP
    exact (mem_arrow_one_one.1 hPs.1.1).2 x y z ⟨hxy, hxz⟩
  · ext x
    constructor
    · rintro ⟨A, ⟨B, hB, hAB⟩, hx⟩
      obtain ⟨A', P, ⟨hA'B, hP⟩, hPs⟩ := h2 B hB
      have : A = A' := (mem_arrow_one_one.1 hS).1 A A' B ⟨hAB, hA'B⟩
      subst this
      rw [hPs.1.2] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, P, hP, hy⟩
    · rintro ⟨y, P, hP, hxy⟩
      obtain ⟨A, B, ⟨hB, hAB⟩, hPs⟩ := h1 P hP
      exact ⟨A, ⟨B, hB, hAB⟩, by rw [hPs.1.2]; exact ⟨y, hxy⟩⟩
  · ext y
    constructor
    · rintro ⟨B, hB, hy⟩
      obtain ⟨A', P, ⟨-, hP⟩, hPs⟩ := h2 B hB
      rw [hPs.2] at hy
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, P, hP, hx⟩
    · rintro ⟨x, P, hP, hxy⟩
      obtain ⟨A, B, ⟨hB, -⟩, hPs⟩ := h1 P hP
      exact ⟨B, hB, by rw [hPs.2]; exact ⟨x, hxy⟩⟩
  · intro P hP
    funext x y
    apply propext
    constructor
    · rintro ⟨⟨P', hP', hxy⟩, hy⟩
      rw [hsame P' P y hP' hP ⟨x, hxy⟩ hy] at hxy
      exact hxy
    · intro hxy
      exact ⟨⟨P, hP, hxy⟩, ⟨x, hxy⟩⟩

/-- The facts about a selection `R` from `Crp(S)''λ` used by `union_corr`. -/
private theorem crp_sel_facts {S : Set α → Set β → Prop} {L : Set (Set β)}
    {R : (α → β → Prop) → Set (α → β → Prop) → Prop} (hR : R ∈ sel memRel (Crp S ʻʻ L)) :
    (∀ P, P ∈ dom R → ∃ A B, (B ∈ L ∧ S A B) ∧ P ∈ smbar A B) ∧
    (∀ P P', P ∈ dom R → P' ∈ dom R → codom P = codom P' → P = P') ∧
    (∀ B A, B ∈ L → (∀ x, S x B ↔ x = A) → ∃ P, P ∈ dom R ∧ R P (smbar A B)) := by
  obtain ⟨⟨hR1, hR2⟩, hR3⟩ := mem_sel_iff.1 hR
  have hU : ∀ P U, R P U → ∃ A B, ((B ∈ L ∧ ∀ x, S x B ↔ x = A) ∧ U = smbar A B) ∧ P ∈ U := by
    intro P U h
    have hU : U ∈ codom R := ⟨P, h⟩
    rw [hR3] at hU
    obtain ⟨B, hB, A, hA, rfl⟩ := hU
    exact ⟨A, B, ⟨⟨hB, hA⟩, rfl⟩, hR2 P _ h⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro P ⟨U, hPU⟩
    obtain ⟨A, B, ⟨⟨hB, hA⟩, rfl⟩, hP⟩ := hU P U hPU
    exact ⟨A, B, ⟨hB, (hA A).2 rfl⟩, hP⟩
  · rintro P P' ⟨U, hPU⟩ ⟨U', hPU'⟩ hc
    obtain ⟨A, B, ⟨⟨hB, hA⟩, rfl⟩, hP⟩ := hU P U hPU
    obtain ⟨A', B', ⟨⟨hB', hA'⟩, rfl⟩, hP'⟩ := hU P' U' hPU'
    have hBB : B = B' := hP.2.trans (hc.trans hP'.2.symm)
    subst hBB
    have hAA : A' = A := (hA A').1 ((hA' A').2 rfl)
    subst hAA
    exact mem_arrow_one_Cls.1 hR1 P P' _ ⟨hPU, hPU'⟩
  · intro B A hB hA
    have : smbar A B ∈ codom R := by rw [hR3]; exact ⟨B, hB, A, hA, rfl⟩
    obtain ⟨P, hP⟩ := this
    exact ⟨P, ⟨_, hP⟩, hP⟩

/-- A selection from a class of existent classes. -/
private theorem sel_memRel_nonempty {K : Set (Set δ)} (h : ∀ U, U ∈ K → U.Nonempty) :
    (sel memRel K).Nonempty := by
  choose f hf using h
  refine ⟨fun P U => ∃ hU : U ∈ K, P = f U hU, mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩⟩
  · rintro x y z ⟨⟨h1, rfl⟩, ⟨h2, rfl⟩⟩; rfl
  · rintro x U ⟨hU, rfl⟩; exact hf U hU
  · ext U; exact ⟨fun ⟨_, hU, _⟩ => hU, fun hU => ⟨f U hU, hU, rfl⟩⟩

/-- The counterexample to ✱111·31·311·313·32·321·46 as printed (without `λ ⊂ ᗡ'S`): `S = Λ̇`,
`λ = ι'V`; then `Crp(S)''λ = Λ` and `Λ̇ ∈ ∈_Δ'Λ`. -/
private theorem crp_counter_facts :
    (rNull : Set Unit → Set Unit → Prop) ∈ arrow one one ∧
    ({Set.univ} : Set (Set Unit)) ∈ Cls2excl ∧
    (rNull ʻʻ ({Set.univ} : Set (Set Unit)) : Set (Set Unit)) ∈ Cls2excl ∧
    (rNull : (Unit → Unit → Prop) → Set (Unit → Unit → Prop) → Prop) ∈
      sel memRel (Crp (rNull : Set Unit → Set Unit → Prop) ʻʻ {Set.univ}) := by
  refine ⟨mem_arrow_one_one.2 ⟨fun _ _ _ h => absurd h.1 (rNull_apply _ _),
    fun _ _ _ h => absurd h.1 (rNull_apply _ _)⟩, ?_, ?_, ?_⟩
  · rintro A B ⟨⟨hA, hB⟩, hne⟩
    rw [Set.mem_singleton_iff] at hA hB
    exact absurd (hA.trans hB.symm) hne
  · rintro A B ⟨⟨⟨_, _, hA⟩, -⟩, -⟩; exact absurd hA (rNull_apply _ _)
  · refine mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 fun _ _ _ h => absurd h.1 (rNull_apply _ _),
      fun _ _ h => absurd h (rNull_apply _ _)⟩, ?_⟩
    ext U
    simp only [codom, rNull_apply, exists_false, Set.ofPred_false, Set.mem_empty_iff_false,
      false_iff]
    rintro ⟨_, -, A, hA, -⟩
    exact rNull_apply _ _ ((hA A).2 rfl)

private theorem sumRel_dom_rNull :
    sumRel (dom (rNull : (Unit → Unit → Prop) → Set (Unit → Unit → Prop) → Prop)) = rNull := by
  funext x y; apply propext
  exact ⟨fun ⟨_, ⟨_, h⟩, _⟩ => absurd h (rNull_apply _ _), fun h => absurd h (rNull_apply _ _)⟩

end Helpers111

/-!
## [✱110] The arithmetical sum of two classes and of two cardinals

*(Vol. 2, p. 75)*

> *Summary of* *110.
>
> In this number, we start from the definition:
>
> *110·01. \(\alpha +\beta =\downarrow (\Lambda \cap \beta )ʻʻ\iotaʻʻ\alpha \cup (\Lambda \cap \alpha )\downarrow ʻʻ\iotaʻʻ\beta \quad\text{Df}\)
>
> \(\alpha +\beta\) is called the "arithmetical class-sum" of \(\alpha\) and \(\beta\). The definition is framed so as to give two mutually exclusive classes respectively similar to \(\alpha\) and \(\beta\), so that the number of terms in the logical sum of these two classes is the arithmetical sum of the numbers of terms in \(\alpha\) and \(\beta\) respectively. \(\alpha +\beta\) is significant whenever \(\alpha\) and \(\beta\) are classes, whatever their types may be.
>
> By means of \(\alpha +\beta\), we define the arithmetical sum of two cardinals as follows:
>
> *110·02. \(\mu +_{\text{c}} \nu =\hat{\xi} \{(\exists \alpha ,\beta ).\mu =\text{N}_{0}\text{c}ʻ\alpha .\nu =\text{N}_{0}\text{c}ʻ\beta .\xi \text{ sm }(\alpha +\beta )\} \quad\text{Df}\)
>
> …

**Lean reading.** (Conventions: `Defs/Part3.lean`, "Encoding decisions: types".) The class-sum
`α + β` is `A +ₐ B` (`clsSum`), a class of relations between classes of the types of `α` and
`β`; it is compared with Lean's `A ⊕ B` (`clsSumEquiv`). `μ +_c ν` is `μ +ᶜ ν`, whose actual
type is implicit and fixed by an equation, a membership or an ascription. The arguments
`Nc'α` of `+_c` are written `n₀c A` (normal adjustment, ✱110·03·04), `Nc(η)'α` is `nc E A`
with the type of `η` explicit, `sm_η''μ` is an ascribed `sm ʻʻ μ`. The real variables have
independent types; an inner arithmetical sum (✱110·54–·57) and the constants `0`, `1`, `2` as
arguments of `+_c` have their own types with the adequacy hypotheses of IIT (none for `0`).
PM's ambiguous `NC` is `NC β`: as a hypothesis with a free `β`; as a conclusion in the type in
which PM's proof puts it (`NC^α(α)` by ✱103·27 in ✱110·201·4·7·72, `NC^{t'ξ}(ξ)` by ✱102·74
in ✱110·42). The e-text's `ν = N₀c'α` in ✱110·2 is read `ν = N₀c'β` (✱110·02). AT is applied
in ✱110·71·72, where PM applies it.

**Status.** proved (all propositions; ✱110·2·201·3·4·42·44·54·541·55·551·56·57·63·631·632·641·642·643·7·71·72 proved (reading), see their docstrings)
-/

/-- ✱110·01 (Df). \(\alpha +\beta = \downarrow (\Lambda \cap \beta )ʻʻ\iota ʻʻ\alpha \cup (\Lambda \cap \alpha ) \downarrow ʻʻ\iota ʻʻ\beta \quad\text{Df}\) -/
theorem pm110_01 {A : Set α} {B : Set β} :
    A +ₐ B = coupleR (Λ ∩ B) ʻʻ iota ʻʻ A ∪ coupleL (Λ ∩ A) ʻʻ iota ʻʻ B := rfl

/-- ✱110·02 (Df). \(\mu +_{\text{c}}\nu = \hat{\xi} \{(\exists \alpha ,\beta ).\mu = \text{N}_{0}\text{c}ʻ\alpha .\nu = \text{N}_{0}\text{c}ʻ\beta .\xi \text{ sm }(\alpha +\beta )\} \quad\text{Df}\) -/
theorem pm110_02 {μ : Set (Set α)} {ν : Set (Set β)} : (μ +ᶜ ν : Set (Set γ)) =
    {ξ | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm ξ (A +ₐ B)} := rfl

/-- ✱110·03 (Df). \(\text{Nc}ʻ\alpha +_{\text{c}}\mu = \text{N}_{0}\text{c}ʻ\alpha +_{\text{c}}\mu \quad\text{Df}\)

A rule of translation (normal adjustment): an argument `Nc'α` of `+_c` is written `n₀c A`; the
target is the identity of the two readings. -/
theorem pm110_03 {A : Set α} {μ : Set (Set β)} : (n₀c A +ᶜ μ : Set (Set γ)) = n₀c A +ᶜ μ := rfl

/-- ✱110·04 (Df). \(\mu +_{\text{c}}\text{Nc}ʻ\alpha = \mu +_{\text{c}}\text{N}_{0}\text{c}ʻ\alpha \quad\text{Df}\)

A rule of translation (normal adjustment), as ✱110·03. -/
theorem pm110_04 {A : Set α} {μ : Set (Set δ)} : (μ +ᶜ n₀c A : Set (Set γ)) = μ +ᶜ n₀c A := rfl

/-- ✱110·1. \[\begin{aligned}\vdash \colon\ldotp R\in \alpha +\beta .\equiv :&(\exists x).x\in \alpha .R = (\iota ʻx)\downarrow (\Lambda \cap \beta ).\lor.\\ &(\exists y).y\in \beta .R = (\Lambda \cap \alpha )\downarrow (\iota ʻy)\\ &[*38·13·131 .(*110·01)]\end{aligned}\] -/
theorem pm110_1 {A : Set α} {B : Set β} {R : Set α → Set β → Prop} :
    R ∈ A +ₐ B ↔ (∃ x, x ∈ A ∧ R = ι x ↓ (Λ ∩ B)) ∨ (∃ y, y ∈ B ∧ R = (Λ ∩ A) ↓ ι y) :=
  mem_clsSum

/-- ✱110·101. \(\vdash .(\iota ʻx)\downarrow (\Lambda \cap \beta ) \neq (\Lambda \cap \alpha )\downarrow (\iota ʻy)\) -/
theorem pm110_101 {A : Set α} {B : Set β} {x : α} {y : β} : ι x ↓ (Λ ∩ B) ≠ (Λ ∩ A) ↓ ι y := by
  intro h
  have e := (couple_eq_couple_iff.1 h).1
  have hx : x ∈ Λ ∩ A := by rw [← e]; exact mem_unitCls.2 rfl
  rw [Null_eq_empty] at hx
  exact hx.1

/-- ✱110·11. \(\vdash .\downarrow (\Lambda \cap \beta )ʻʻ\iotaʻʻ\alpha \cap (\Lambda \cap \alpha )\downarrow ʻʻ\iotaʻʻ\beta = \Lambda\) -/
theorem pm110_11 {A : Set α} {B : Set β} :
    coupleR (Λ ∩ B) ʻʻ iota ʻʻ A ∩ coupleL (Λ ∩ A) ʻʻ iota ʻʻ B = Λ := by
  ext R
  rw [Null_eq_empty (α := Set α → Set β → Prop)]
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨u, ⟨x, hx, rfl⟩, h1⟩ ⟨v, ⟨y, hy, rfl⟩, h2⟩
  exact pm110_101 ((show R = _ from h1).symm.trans (show R = _ from h2))

/-- ✱110·12. \(\vdash .\downarrow (\Lambda \cap \beta )ʻʻ\iotaʻʻ\alpha \text{ sm }\alpha .(\Lambda \cap \alpha )\downarrow ʻʻ\iotaʻʻ\beta \text{ sm }\beta \quad[*73·41·61·611]\) -/
theorem pm110_12 {A : Set α} {B : Set β} :
    sm (coupleR (Λ ∩ B) ʻʻ iota ʻʻ A) A ∧ sm (coupleL (Λ ∩ A) ʻʻ iota ʻʻ B) B := by
  constructor
  · refine sm_of_injOn (fun x => ι x ↓ (Λ ∩ B)) (fun x y _ _ h =>
      unitCls_injective (couple_eq_couple_iff.1 h).1) fun R => ⟨?_, ?_⟩
    · rintro ⟨u, ⟨x, hx, rfl⟩, h⟩; exact ⟨x, hx, h⟩
    · rintro ⟨x, hx, h⟩; exact ⟨ι x, ⟨x, hx, rfl⟩, h⟩
  · refine sm_of_injOn (fun y => (Λ ∩ A) ↓ ι y) (fun x y _ _ h =>
      unitCls_injective (couple_eq_couple_iff.1 h).2) fun R => ⟨?_, ?_⟩
    · rintro ⟨u, ⟨x, hx, rfl⟩, h⟩; exact ⟨x, hx, h⟩
    · rintro ⟨x, hx, h⟩; exact ⟨ι x, ⟨x, hx, rfl⟩, h⟩

/-- ✱110·13. \(\vdash :\gamma \text{ sm }\alpha .\delta \text{ sm }\beta .\gamma \cap \delta = \Lambda .\supset .\gamma \cup \delta \text{ sm }(\alpha +\beta)\) -/
theorem pm110_13 {A : Set α} {B : Set β} {G H : Set γ} :
    (sm G A ∧ sm H B) ∧ G ∩ H = Λ → sm (G ∪ H) (A +ₐ B) :=
  fun h => mem_nc_clsSum.2 ⟨G, H, h, rfl⟩

/-- ✱110·14. \(\vdash :\alpha \cap \beta = \Lambda .\supset .\alpha \cup \beta \text{ sm }(\alpha +\beta ) \quad[*110·13.*73·3]\) -/
theorem pm110_14 {A B : Set α} : A ∩ B = Λ → sm (A ∪ B) (A +ₐ B) :=
  fun h => pm110_13 ⟨⟨sm_refl A, sm_refl B⟩, h⟩

/-- ✱110·15. \(\vdash :\gamma \text{ sm }\alpha .\delta \text{ sm }\beta .\supset .\gamma +\delta \text{ sm }\alpha +\beta\) -/
theorem pm110_15 {A : Set α} {B : Set β} {G : Set γ} {H : Set δ} :
    sm G A ∧ sm H B → sm (G +ₐ H) (A +ₐ B) :=
  fun h => sm_clsSum h.1 h.2

/-- ✱110·151. \(\vdash \colon\ldotp \alpha \cap \beta = \Lambda .\supset :\xi \text{ sm }(\alpha \cup \beta ).\equiv .(\exists \gamma ,\delta ).\gamma \text{ sm }\alpha .\delta \text{ sm }\beta .\gamma \cap \delta = \Lambda .\xi = \gamma \cup \delta\) -/
theorem pm110_151 {A B : Set α} {X : Set γ} : A ∩ B = Λ →
    (sm X (A ∪ B) ↔ ∃ G H : Set γ, ((sm G A ∧ sm H B) ∧ G ∩ H = Λ) ∧ X = G ∪ H) := by
  intro h
  refine Iff.trans ?_ mem_nc_clsSum
  exact ⟨fun hX => sm_trans hX (pm110_14 h), fun hX => sm_trans hX (sm_symm (pm110_14 h))⟩

/-- ✱110·152. \(\vdash :\xi \text{ sm } (\alpha +\beta ). \equiv .(\exists \gamma ,\delta ).\gamma \text{ sm } \alpha .\delta \text{ sm } \beta .\gamma \cap \delta = \Lambda .\xi = \gamma \cup \delta\) -/
theorem pm110_152 {A : Set α} {B : Set β} {X : Set γ} :
    sm X (A +ₐ B) ↔ ∃ G H : Set γ, ((sm G A ∧ sm H B) ∧ G ∩ H = Λ) ∧ X = G ∪ H :=
  mem_nc_clsSum

/-- ✱110·16. \[\begin{aligned}&\vdash .\text{Nc}ʻ(\alpha +\beta ) = \hat{\xi} \{(\exists \gamma ,\delta ).\gamma \text{ sm } \alpha .\delta \text{ sm } \beta .\gamma \cap \delta = \Lambda .\xi = \gamma \cup \delta \}\\ &[*110·152.*100·1]\end{aligned}\]

`Nc'(α + β)` is in the type `γ` of the classes `ξ` (significance). -/
theorem pm110_16 {A : Set α} {B : Set β} :
    nc γ (A +ₐ B) = {X | ∃ G H : Set γ, ((sm G A ∧ sm H B) ∧ G ∩ H = Λ) ∧ X = G ∪ H} :=
  Set.ext fun _ => mem_nc_clsSum

/-- ✱110·17. \(\vdash :\alpha \in tʻ\beta .\supset .\exists !\text{Nc}(tʻ\alpha )ʻ(\alpha +\beta )\)

`α ∈ t'β` puts `α` and `β` in one type (`Set γ`); `Nc(t'α)'(α + β)` is the cardinal taken among
the classes of the type of `t'α`, i.e. classes of classes of `γ`-things. -/
theorem pm110_17 {A B : Set γ} : A ∈ typ B → (nc (Set γ) (A +ₐ B)).Nonempty :=
  fun _ => nc_set_clsSum_nonempty A B

/-- ✱110·18. \(\vdash .\alpha +\beta \in tʻtʻ(tʻ\alpha \uparrow tʻ\beta)\) -/
theorem pm110_18 {A : Set α} {B : Set β} : A +ₐ B ∈ typ (typ (cross (typ A) (typ B))) := by
  rw [typ_eq_univ]; exact Set.mem_univ _

/-- ✱110·2. \[\begin{aligned}&\vdash :\xi \in \mu +_{\text{c}}\nu . \equiv .(\exists \alpha ,\beta ).\mu = \text{N}_{0}\text{c}ʻ\alpha .\nu = \text{N}_{0}\text{c}ʻ\alpha .\xi \text{ sm } (\alpha +\beta )\\ &[(*110·02)]\end{aligned}\]

**Status.** proved (reading): transcription error: the e-text prints `ν = N₀c'α` for `ν = N₀c'β`
(the definiens of ✱110·02, which is the reference given). -/
theorem pm110_2 {μ : Set (Set α)} {ν : Set (Set β)} {X : Set γ} :
    X ∈ (μ +ᶜ ν : Set (Set γ)) ↔
      ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm X (A +ₐ B) := Iff.rfl

/-- ✱110·201. \[\begin{aligned}&\vdash \colon\ldotp \xi \in \mu +_{\text{c}}\nu . \equiv :\mu ,\nu \in \text{NC}:(\exists \alpha ,\beta ).\alpha \in \mu .\beta \in \nu .\xi \text{ sm } (\alpha +\beta )\\ &[*103·27.*110·2]\end{aligned}\]

**Status.** proved (reading): `μ, ν ∈ NC` is `μ ∈ NC α ∧ ν ∈ NC β`, the ambiguous `NC` being
taken, as in ✱103·27 (the reference), with the classes whose numbers are in question in the
types of the members of `μ` and `ν` (with another type the equivalence can fail, e.g. in an empty
type). -/
theorem pm110_201 {μ : Set (Set α)} {ν : Set (Set β)} {X : Set γ} :
    X ∈ (μ +ᶜ ν : Set (Set γ)) ↔
      (μ ∈ NC α ∧ ν ∈ NC β) ∧ ∃ A B, (A ∈ μ ∧ B ∈ ν) ∧ sm X (A +ₐ B) := by
  constructor
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    exact ⟨⟨n₀c_mem_NC A, n₀c_mem_NC B⟩, A, B, ⟨self_mem_n₀c A, self_mem_n₀c B⟩, h⟩
  · rintro ⟨⟨⟨A', rfl⟩, ⟨B', rfl⟩⟩, A, B, ⟨hA, hB⟩, h⟩
    exact ⟨A, B, ⟨nc_eq_n₀c_of_mem hA, nc_eq_n₀c_of_mem hB⟩, h⟩

/-- ✱110·202. \[\begin{aligned}\vdash \colon\ldotp \xi \in &\mu +_{\text{c}}\nu . \equiv :\\ &\exists !\mu .\exists !\nu :(\exists \gamma ,\delta ).\mu = \text{Nc}ʻ\gamma .\nu = \text{Nc}ʻ\delta .\gamma \cap \delta = \Lambda .\xi = \gamma \cup \delta\end{aligned}\]

`μ = Nc'γ` is in the type of the members of `μ` (meaning). -/
theorem pm110_202 {μ : Set (Set α)} {ν : Set (Set β)} {X : Set γ} :
    X ∈ (μ +ᶜ ν : Set (Set γ)) ↔ (μ.Nonempty ∧ ν.Nonempty) ∧
      ∃ G H : Set γ, ((μ = nc α G ∧ ν = nc β H) ∧ G ∩ H = Λ) ∧ X = G ∪ H := by
  constructor
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    obtain ⟨G, H, ⟨⟨hG, hH⟩, hGH⟩, rfl⟩ := mem_nc_clsSum.1 h
    exact ⟨⟨n₀c_nonempty A, n₀c_nonempty B⟩, G, H, ⟨⟨(n₀c_eq_nc A).trans
      (nc_eq_nc_of_sm (sm_symm hG)), (n₀c_eq_nc B).trans (nc_eq_nc_of_sm (sm_symm hH))⟩, hGH⟩, rfl⟩
  · rintro ⟨⟨⟨A, hA⟩, ⟨B, hB⟩⟩, G, H, ⟨⟨hμ, hν⟩, hGH⟩, rfl⟩
    have hA' : sm A G := by rw [hμ] at hA; exact hA
    have hB' : sm B H := by rw [hν] at hB; exact hB
    refine ⟨A, B, ⟨?_, ?_⟩, mem_nc_clsSum.2 ⟨G, H, ⟨⟨sm_symm hA', sm_symm hB'⟩, hGH⟩, rfl⟩⟩
    · rw [hμ, n₀c_eq_nc]; exact nc_eq_nc_of_sm (sm_symm hA')
    · rw [hν, n₀c_eq_nc]; exact nc_eq_nc_of_sm (sm_symm hB')

/-- ✱110·211. \[\begin{aligned}\vdash \colon\ldotp \mu ,\nu \in \text{NC}.\supset :\xi &\in \mu +_{\text{c}}\nu .\equiv .\\ &(\exists \gamma ,\delta ).\gamma \in \text{ sm }ʻʻ\mu .\delta \in \text{ sm }ʻʻ\nu .\gamma \cap \delta =\Lambda .\xi =\gamma \cup \delta\end{aligned}\]

`μ, ν ∈ NC` is `μ ∈ NC β₁ ∧ ν ∈ NC β₂` with independent types (Prefatory Statement, V). -/
theorem pm110_211 {β₁ : Type*} {β₂ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {X : Set γ} :
    μ ∈ NC β₁ ∧ ν ∈ NC β₂ → (X ∈ (μ +ᶜ ν : Set (Set γ)) ↔
      ∃ G H : Set γ, ((G ∈ sm ʻʻ μ ∧ H ∈ sm ʻʻ ν) ∧ G ∩ H = Λ) ∧ X = G ∪ H) := by
  rintro ⟨hμ, hν⟩
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [empty_cardAdd, sm_img_empty]; simp
  rcases NC_cases hν with rfl | ⟨B, rfl⟩
  · rw [cardAdd_empty, sm_img_empty]; simp
  rw [n₀c_cardAdd_n₀c, mem_nc_clsSum]
  simp only [mem_sm_img_n₀c]

/-- ✱110·212. \(\vdash \colon\ldotp \mu ,\nu \in \text{NC}.\supset :\xi \in \mu +_{\text{c}}\nu .\equiv .(\exists \gamma ).\gamma \in \text{ sm }ʻʻ\mu .\gamma \subset \xi .\xi -\gamma \in \text{ sm }ʻʻ\nu\) -/
theorem pm110_212 {β₁ : Type*} {β₂ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {X : Set γ} :
    μ ∈ NC β₁ ∧ ν ∈ NC β₂ → (X ∈ (μ +ᶜ ν : Set (Set γ)) ↔
      ∃ G : Set γ, (G ∈ sm ʻʻ μ ∧ G ⊆ X) ∧ X \ G ∈ sm ʻʻ ν) := by
  intro h
  rw [pm110_211 h]
  constructor
  · rintro ⟨G, H, ⟨⟨hG, hH⟩, hGH⟩, rfl⟩
    refine ⟨G, ⟨hG, Set.subset_union_left⟩, ?_⟩
    rwa [Set.union_sdiff_cancel_left (by rw [hGH, Null_eq_empty])]
  · rintro ⟨G, ⟨hG, hGX⟩, hH⟩
    refine ⟨G, X \ G, ⟨⟨hG, hH⟩, ?_⟩, (Set.union_sdiff_cancel hGX).symm⟩
    rw [inter_eq_null_iff]; exact Set.disjoint_sdiff_right

/-- ✱110·22. \(\vdash .\text{N}_{0}\text{c}ʻ\alpha +_{\text{c}}\text{N}_{0}\text{c}ʻ\beta = \text{Nc}ʻ(\alpha + \beta )\) -/
theorem pm110_22 {A : Set α} {B : Set β} :
    (n₀c A +ᶜ n₀c B : Set (Set γ)) = nc γ (A +ₐ B) := n₀c_cardAdd_n₀c A B

/-- ✱110·221. \(\vdash :\xi \in \text{Nc}(\eta )ʻ\alpha +_{\text{c}}\text{Nc}(\zeta )ʻ\beta .\equiv .\exists !\text{Nc}(\eta )ʻ\alpha .\exists !\text{Nc}(\zeta )ʻ\beta .\xi \in \text{Nc}ʻ(\alpha +\beta )\)

`Nc(η)'α` is `nc E A` with `η : Set E`; `Nc'(α + β)` is in the type of `ξ`. -/
theorem pm110_221 {E : Type*} {Z : Type*} {A : Set α} {B : Set β} {X : Set γ} :
    X ∈ (nc E A +ᶜ nc Z B : Set (Set γ)) ↔
      ((nc E A).Nonempty ∧ (nc Z B).Nonempty) ∧ X ∈ nc γ (A +ₐ B) := by
  rcases nc_cases E A with h0 | ⟨P, hP, hPe⟩
  · rw [h0, empty_cardAdd]; simp
  rcases nc_cases Z B with h0 | ⟨Q, hQ, hQe⟩
  · rw [h0, cardAdd_empty]; simp
  rw [hPe, hQe, n₀c_cardAdd_n₀c, nc_eq_nc_of_sm (sm_clsSum hP hQ)]
  simp [n₀c_nonempty]

/-- ✱110·23. \[\begin{aligned}\vdash :&\exists !\text{Nc}(\eta )ʻ\alpha .\exists !\text{Nc}(\zeta )ʻ\beta .\supset .\\ &\text{Nc}(\eta )ʻ\alpha +_{\text{c}}\text{Nc}(\zeta )ʻ\beta =\text{Nc}ʻ(\alpha +\beta )=\text{N}_{0}\text{c}ʻ\alpha +_{\text{c}}\text{N}_{0}\text{c}ʻ\beta \quad[*110·221·22]\end{aligned}\] -/
theorem pm110_23 {E : Type*} {Z : Type*} {A : Set α} {B : Set β} :
    (nc E A).Nonempty ∧ (nc Z B).Nonempty →
      (nc E A +ᶜ nc Z B : Set (Set γ)) = nc γ (A +ₐ B) ∧
        nc γ (A +ₐ B) = (n₀c A +ᶜ n₀c B : Set (Set γ)) := by
  intro h
  refine ⟨Set.ext fun X => ?_, (n₀c_cardAdd_n₀c A B).symm⟩
  rw [pm110_221]
  exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩

/-- ✱110·231. \[\begin{aligned}&\vdash \colon\ldotp \text{Nc}(\eta )ʻ\alpha =\Lambda .\lor.\text{Nc}(\zeta )ʻ\beta =\Lambda :\supset .\text{Nc}(\eta )ʻ\alpha +_{\text{c}}\text{Nc}(\zeta )ʻ\beta =\Lambda\\ &[*110·221]\end{aligned}\] -/
theorem pm110_231 {E : Type*} {Z : Type*} {A : Set α} {B : Set β} :
    nc E A = Λ ∨ nc Z B = Λ → (nc E A +ᶜ nc Z B : Set (Set γ)) = Λ := by
  rw [Null_eq_empty, Null_eq_empty, Null_eq_empty]
  rintro (h | h)
  · rw [h, empty_cardAdd]
  · rw [h, cardAdd_empty]

/-- ✱110·24. \(\vdash :\eta \text{ sm }\alpha .\zeta \text{ sm }\beta .\supset .\text{N}_{0}\text{c}ʻ\eta +_{\text{c}}\text{N}_{0}\text{c}ʻ\zeta =\text{N}_{0}\text{c}ʻ\alpha +_{\text{c}}\text{N}_{0}\text{c}ʻ\beta\) -/
theorem pm110_24 {A : Set α} {B : Set β} {E1 : Set δ} {Z1 : Set ε} :
    sm E1 A ∧ sm Z1 B → (n₀c E1 +ᶜ n₀c Z1 : Set (Set γ)) = n₀c A +ᶜ n₀c B := by
  rintro ⟨h1, h2⟩
  rw [n₀c_cardAdd_n₀c, n₀c_cardAdd_n₀c]
  exact nc_eq_nc_of_sm (sm_clsSum h1 h2)

/-- ✱110·25. \(\vdash :\mu ,\nu \in \text{NC}.\exists ! \text{ sm }_{\eta }ʻʻ\mu .\exists ! \text{ sm }_{\zeta }ʻʻ\nu .\supset .\mu +_{\text{c}}\nu = \text{ sm }_{\eta }ʻʻ\mu +_{\text{c}} \text{ sm }_{\zeta }ʻʻ\nu\)

`sm_η''μ` is the ascribed `(sm ʻʻ μ : Set (Set E))` (`η : Set E`), a type PM indicates
expressly (no adequacy hypothesis); `μ, ν ∈ NC` have independent types. -/
theorem pm110_25 {β₁ β₂ E Z : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    ((μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ (sm ʻʻ μ : Set (Set E)).Nonempty) ∧
        (sm ʻʻ ν : Set (Set Z)).Nonempty →
      (μ +ᶜ ν : Set (Set γ)) = (sm ʻʻ μ : Set (Set E)) +ᶜ (sm ʻʻ ν : Set (Set Z)) := by
  rintro ⟨⟨⟨hμ, hν⟩, h1⟩, h2⟩
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [sm_img_empty] at h1; exact absurd h1 Set.not_nonempty_empty
  rcases NC_cases hν with rfl | ⟨B, rfl⟩
  · rw [sm_img_empty] at h2; exact absurd h2 Set.not_nonempty_empty
  rw [sm_img_n₀c] at h1 h2 ⊢
  rw [sm_img_n₀c]
  have := pm110_23 (γ := γ) ⟨h1, h2⟩
  exact (this.1.trans this.2).symm

/-- ✱110·251. \(\vdash :\mu ,\nu \in \text{NC}.\supset .\mu ^{(1)}+_{\text{c}}\nu ^{(1)} = \mu +_{\text{c}}\nu\) -/
theorem pm110_251 {β₁ β₂ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NC β₁ ∧ ν ∈ NC β₂ → (up1 μ +ᶜ up1 ν : Set (Set γ)) = μ +ᶜ ν := by
  rintro ⟨hμ, hν⟩
  rw [up1_eq, up1_eq]
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [sm_img_empty, empty_cardAdd, empty_cardAdd]
  rcases NC_cases hν with rfl | ⟨B, rfl⟩
  · rw [sm_img_empty, cardAdd_empty, cardAdd_empty]
  refine (pm110_25 ⟨⟨⟨n₀c_mem_NC A, n₀c_mem_NC B⟩, ?_⟩, ?_⟩).symm
  · rw [sm_img_n₀c]; exact nc_up_nonempty A
  · rw [sm_img_n₀c]; exact nc_up_nonempty B

/-- ✱110·252. \(\vdash :\mu ,\nu \in \text{NC}.\supset .\mu _{(00)}+_{\text{c}}\nu _{(00)} = \mu +_{\text{c}}\nu \quad[\text{Proof as in *110·251}]\) -/
theorem pm110_252 {β₁ β₂ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NC β₁ ∧ ν ∈ NC β₂ → (down00 μ +ᶜ down00 ν : Set (Set γ)) = μ +ᶜ ν := by
  rintro ⟨hμ, hν⟩
  rw [down00_eq, down00_eq]
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [sm_img_empty, empty_cardAdd, empty_cardAdd]
  rcases NC_cases hν with rfl | ⟨B, rfl⟩
  · rw [sm_img_empty, cardAdd_empty, cardAdd_empty]
  refine (pm110_25 ⟨⟨⟨n₀c_mem_NC A, n₀c_mem_NC B⟩, ?_⟩, ?_⟩).symm
  · rw [sm_img_n₀c]; exact nc_rel_nonempty A
  · rw [sm_img_n₀c]; exact nc_rel_nonempty B

/-- ✱110·3. \(\vdash .\text{Nc}ʻ\alpha +_{\text{c}}\text{Nc}ʻ\beta = \text{N}_{0}\text{c}ʻ\alpha +_{\text{c}}\text{N}_{0}\text{c}ʻ\beta = \text{Nc}ʻ(\alpha +\beta ) \quad[*110·22.(*110·03·04)]\)

(Normal adjustment, encoding decision 5.) The arguments `Nc'α`, `Nc'β` of `+_c` are `n₀c A`,
`n₀c B` by ✱110·03·04; the sides of the equation are in one type `γ`, otherwise free.

**Status.** proved (reading): by the Dfs ✱110·03·04 the arguments Nc'α, Nc'β of +_c are read
N₀c'α, N₀c'β, so the first equation is the identity of the two readings -/
theorem pm110_3 {A : Set α} {B : Set β} :
    (n₀c A +ᶜ n₀c B : Set (Set γ)) = n₀c A +ᶜ n₀c B ∧
      (n₀c A +ᶜ n₀c B : Set (Set γ)) = nc γ (A +ₐ B) :=
  ⟨rfl, n₀c_cardAdd_n₀c A B⟩

/-- ✱110·31. \(\vdash :\gamma \text{ sm } \alpha .\delta \text{ sm } \beta .\supset .\text{Nc}ʻ\gamma +_{\text{c}}\text{Nc}ʻ\delta = \text{Nc}ʻ\alpha +_{\text{c}}\text{Nc}ʻ\beta \quad[*110·24·3]\)

The arguments `Nc'γ`, … of `+_c` are written `n₀c G`, … (✱110·03·04). -/
theorem pm110_31 {A : Set α} {B : Set β} {G : Set δ} {H : Set ε} :
    sm G A ∧ sm H B → (n₀c G +ᶜ n₀c H : Set (Set γ)) = n₀c A +ᶜ n₀c B :=
  pm110_24

/-- ✱110·32. \(\vdash :\alpha \cap \beta = \Lambda .\supset .\text{Nc}ʻ\alpha +_{\text{c}}\text{Nc}ʻ\beta = \text{Nc}ʻ(\alpha \cup \beta ) \quad[*110·3·14]\) -/
theorem pm110_32 {A B : Set α} : A ∩ B = Λ → (n₀c A +ᶜ n₀c B : Set (Set γ)) = nc γ (A ∪ B) := by
  intro h
  rw [n₀c_cardAdd_n₀c]
  exact nc_eq_nc_of_sm (sm_symm (pm110_14 h))

/-- ✱110·33. \[\begin{aligned}&\vdash :\xi \in \text{Nc}ʻ\alpha +_{\text{c}}\text{Nc}ʻ\beta . \equiv .(\exists \gamma ,\delta ).\gamma \text{ sm } \alpha .\delta \text{ sm } \beta .\gamma \cap \delta = \Lambda .\xi = \gamma \cup \delta \\ &[*110·3·16]\end{aligned}\] -/
theorem pm110_33 {A : Set α} {B : Set β} {X : Set γ} :
    X ∈ (n₀c A +ᶜ n₀c B : Set (Set γ)) ↔
      ∃ G H : Set γ, ((sm G A ∧ sm H B) ∧ G ∩ H = Λ) ∧ X = G ∪ H := by
  rw [n₀c_cardAdd_n₀c]; exact mem_nc_clsSum

/-- ✱110·331. \(\vdash .\text{Nc}ʻ\alpha +_{\text{c}}\text{Nc}ʻ\beta =\hat{\xi} \{(\exists \gamma ).\gamma \text{ sm }\alpha .\xi -\gamma \text{ sm }\beta .\gamma \subset \xi\}\) -/
theorem pm110_331 {A : Set α} {B : Set β} :
    (n₀c A +ᶜ n₀c B : Set (Set γ)) = {X | ∃ G : Set γ, (sm G A ∧ sm (X \ G) B) ∧ G ⊆ X} := by
  ext X
  rw [pm110_33]
  constructor
  · rintro ⟨G, H, ⟨⟨hG, hH⟩, hGH⟩, rfl⟩
    refine ⟨G, ⟨hG, ?_⟩, Set.subset_union_left⟩
    rwa [Set.union_sdiff_cancel_left (by rw [hGH, Null_eq_empty])]
  · rintro ⟨G, ⟨hG, hH⟩, hGX⟩
    refine ⟨G, X \ G, ⟨⟨hG, hH⟩, ?_⟩, (Set.union_sdiff_cancel hGX).symm⟩
    rw [inter_eq_null_iff]; exact Set.disjoint_sdiff_right

/-- ✱110·34. \[\begin{aligned}&\vdash :\exists !\text{Nc}(\eta )ʻ\alpha .\exists !\text{Nc}(\zeta )ʻ\beta .\supset .\text{Nc}(\eta )ʻ\alpha +_{\text{c}} \text{Nc}(\zeta )ʻ\beta =\text{Nc}ʻ\alpha +_{\text{c}} \text{Nc}ʻ\beta \\ &[*110·23·3]\end{aligned}\] -/
theorem pm110_34 {E : Type*} {Z : Type*} {A : Set α} {B : Set β} :
    (nc E A).Nonempty ∧ (nc Z B).Nonempty →
      (nc E A +ᶜ nc Z B : Set (Set γ)) = n₀c A +ᶜ n₀c B := by
  intro h
  have := pm110_23 (γ := γ) h
  exact this.1.trans this.2

/-- ✱110·35. \(\vdash .\text{N}^{1}\text{c}ʻ\alpha +_{\text{c}} \text{N}^{1}\text{c}ʻ\beta =\text{Nc}ʻ\alpha +_{\text{c}} \text{Nc}ʻ\beta \quad[*104·102·21.*110·34]\) -/
theorem pm110_35 {A : Set α} {B : Set β} :
    (n1c A +ᶜ n1c B : Set (Set γ)) = n₀c A +ᶜ n₀c B := by
  rw [n1c_eq, n1c_eq]
  exact pm110_34 ⟨nc_up_nonempty A, nc_up_nonempty B⟩

/-- ✱110·351. \(\vdash .\text{N}_{00}\text{c}ʻ\alpha +_{\text{c}} \text{N}_{00}\text{c}ʻ\beta =\text{Nc}ʻ\alpha +_{\text{c}} \text{Nc}ʻ\beta \quad[*106·21.*110·34]\) -/
theorem pm110_351 {A : Set α} {B : Set β} :
    (n₀₀c A +ᶜ n₀₀c B : Set (Set γ)) = n₀c A +ᶜ n₀c B := by
  rw [n₀₀c_eq, n₀₀c_eq]
  exact pm110_34 ⟨nc_rel_nonempty A, nc_rel_nonempty B⟩

/-- ✱110·4. \(\vdash :\exists !\mu +_{\text{c}} \nu .\supset .\mu ,\nu \in \text{NC}-\iota ʻ\Lambda .\mu ,\nu \in \text{N}_{0}\text{C} \quad[*110·201·202·2]\)

**Status.** proved (reading): the ambiguous `NC` of the conclusion is taken, as in ✱103·27
(the reference ✱110·201), with the classes whose numbers are in question in the types of the
members of `μ` and `ν` (`NC^α(α)`). -/
theorem pm110_4 {μ : Set (Set α)} {ν : Set (Set β)} : (μ +ᶜ ν : Set (Set γ)).Nonempty →
    (μ ∈ NC α \ ι Λ ∧ ν ∈ NC β \ ι Λ) ∧ (μ ∈ N₀C ∧ ν ∈ N₀C) := by
  rintro ⟨X, A, B, ⟨rfl, rfl⟩, -⟩
  refine ⟨⟨⟨n₀c_mem_NC A, ?_⟩, ⟨n₀c_mem_NC B, ?_⟩⟩, ⟨A, rfl⟩, ⟨B, rfl⟩⟩
  · rw [mem_unitCls, Null_eq_empty]; exact n₀c_ne_empty A
  · rw [mem_unitCls, Null_eq_empty]; exact n₀c_ne_empty B

/-- ✱110·401. \(\vdash :\mu =\text{N}_{0}\text{c}ʻ\alpha .\nu =\text{N}_{0}\text{c}ʻ\beta .\supset .\alpha + \beta \in tʻtʻ(\mu \uparrow \nu )\) -/
theorem pm110_401 {μ : Set (Set α)} {ν : Set (Set β)} {A : Set α} {B : Set β} :
    μ = n₀c A ∧ ν = n₀c B → A +ₐ B ∈ typ (typ (cross μ ν)) := by
  intro _; rw [typ_eq_univ]; exact Set.mem_univ _

/-- ✱110·402. \(\vdash :\mu ,\nu \in \text{N}_{0}\text{C}.\supset .\exists !(\mu +_{\text{c}} \nu )\cap tʻtʻ(\mu \uparrow \nu )\) -/
theorem pm110_402 {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ N₀C ∧ ν ∈ N₀C → ((μ +ᶜ ν) ∩ typ (typ (cross μ ν))).Nonempty := by
  rintro ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩
  exact ⟨A +ₐ B, by rw [n₀c_cardAdd_n₀c]; exact self_mem_nc _, pm110_401 ⟨rfl, rfl⟩⟩

/-- ✱110·403. \(\vdash :\mu ,\nu \in \text{N}_{0}\text{C}.\equiv .\exists !(\mu +_{\text{c}} \nu )\cap tʻtʻ(\mu \uparrow \nu ) \quad[*110·402·4]\) -/
theorem pm110_403 {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ N₀C ∧ ν ∈ N₀C ↔ ((μ +ᶜ ν) ∩ typ (typ (cross μ ν))).Nonempty :=
  ⟨pm110_402, fun ⟨X, hX, _⟩ => (pm110_4 ⟨X, hX⟩).2⟩

/-- ✱110·404. \(\vdash .\exists !(\text{Nc}ʻ\alpha +_{\text{c}} \text{Nc}ʻ\beta )\cap tʻtʻ(tʻ\alpha \uparrow tʻ\beta ) \quad[*110·18·3.*100·3]\) -/
theorem pm110_404 {A : Set α} {B : Set β} :
    ((n₀c A +ᶜ n₀c B) ∩ typ (typ (cross (typ A) (typ B)))).Nonempty :=
  ⟨A +ₐ B, by rw [n₀c_cardAdd_n₀c]; exact self_mem_nc _, by rw [typ_eq_univ]; exact Set.mem_univ _⟩

/-- ✱110·41. \(\vdash :\mu ,\nu \in \text{N}_{0}\text{C}.tʻ\mu = tʻ\nu .\supset .\exists !(\mu +_{\text{c}}\nu )\cap tʻ\mu \)

`t'μ = t'ν` puts `μ` and `ν` in one type; `(μ +_c ν) ∩ t'μ` puts the sum among the classes of
the type of `t₀'μ` (classes of classes of `α`-things). -/
theorem pm110_41 {μ ν : Set (Set α)} :
    (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ typ μ = typ ν → ((μ +ᶜ ν) ∩ typ μ).Nonempty := by
  rintro ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, -⟩
  obtain ⟨X, hX⟩ := nc_set_clsSum_nonempty A B
  exact ⟨X, by rw [n₀c_cardAdd_n₀c]; exact hX, by rw [typ_eq_univ]; exact Set.mem_univ _⟩

/-- ✱110·411. \[\begin{aligned}&\vdash :tʻ\alpha = tʻ\beta .\supset .\exists !(\text{Nc}ʻ\alpha +_{\text{c}}\text{Nc}ʻ\beta )\cap tʻtʻ\alpha .\exists !\text{Nc}(tʻ\alpha )ʻ(\alpha +\beta )\\ &[*110·17·3]\end{aligned}\] -/
theorem pm110_411 {A B : Set γ} : typ A = typ B →
    ((n₀c A +ᶜ n₀c B) ∩ typ (typ A)).Nonempty ∧ (nc (Set γ) (A +ₐ B)).Nonempty := by
  intro _
  obtain ⟨X, hX⟩ := nc_set_clsSum_nonempty A B
  exact ⟨⟨X, by rw [n₀c_cardAdd_n₀c]; exact hX, by rw [typ_eq_univ]; exact Set.mem_univ _⟩, X, hX⟩

/-- ✱110·42. \(\vdash .\mu +_{\text{c}}\nu \in \text{NC}\)

**Status.** proved (reading): the ambiguous `NC` is taken as `NC^{t'ξ}(ξ)` for the classes `ξ` of
the sum (`NC (Set γ)`), the type in which PM's proof puts it by ✱102·74 (`Λ ∈ NC^{t'α}(α)`); in
some other determinations of `NC` the proposition fails (e.g. `NC` of the classes of an empty
type contains only `0`). -/
theorem pm110_42 {μ : Set (Set α)} {ν : Set (Set β)} : (μ +ᶜ ν : Set (Set γ)) ∈ NC (Set γ) := by
  rcases Set.eq_empty_or_nonempty (μ +ᶜ ν : Set (Set γ)) with h | ⟨X, hX⟩
  · refine ⟨Set.univ, ?_⟩
    rw [h]
    ext Y
    simp only [Set.mem_empty_iff_false, false_iff]
    intro hY
    obtain ⟨e⟩ := mem_nc_iff_equiv.1 hY
    exact Function.cantor_injective (fun S : Set γ => ((e.symm ⟨S, trivial⟩ : Y) : γ))
      (fun a b hab => by
        have := e.symm.injective (Subtype.ext hab)
        exact congrArg Subtype.val this)
  · obtain ⟨A, B, ⟨rfl, rfl⟩, h⟩ := hX
    refine ⟨iota ʻʻ X, ?_⟩
    rw [n₀c_cardAdd_n₀c, ← nc_eq_nc_of_sm h]
    refine nc_eq_nc_of_sm (sm_symm (sm_of_injOn (fun x => ι x) (fun x y _ _ e => unitCls_injective e)
      fun S => ⟨?_, ?_⟩))
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

/-- ✱110·43. \(\vdash :\mu +_{\text{c}}\nu = \text{N}_{0}\text{c}ʻ\eta . \equiv .\eta \in \mu +_{\text{c}}\nu \quad[*110·42.*103·26]\) -/
theorem pm110_43 {μ : Set (Set α)} {ν : Set (Set β)} {X : Set γ} :
    (μ +ᶜ ν : Set (Set γ)) = n₀c X ↔ X ∈ (μ +ᶜ ν : Set (Set γ)) := by
  constructor
  · intro h; rw [h]; exact self_mem_n₀c X
  · rintro hX
    obtain ⟨A, B, ⟨rfl, rfl⟩, h⟩ := hX
    rw [n₀c_cardAdd_n₀c]
    exact nc_eq_n₀c_of_mem h

/-- ✱110·44. \(\vdash .\text{ sm }ʻʻ(\mu +_{\text{c}}\nu ) = \mu +_{\text{c}}\nu\)

The argument `μ +_c ν` of `sm''` and the right-hand side are in independent types (convention IT:
with an argumental occurrence, the equational one is free). PM's demonstration takes for the
argument a type in which `α + β` has its number (`η sm (α + β)` with `η` given), and PM's comment
says that the proposition "depends upon the fact that `μ +_c ν` is typically ambiguous": the
argument is taken in an adequate type, `AdeqAdd γ μ ν`.

**Status.** proved (reading): the argument `μ +_c ν` of `sm''` is taken in a type adequate for it
(Prefatory Statement, II); without this it fails (`pm110_44_aux_adequacy`). -/
theorem pm110_44 {μ : Set (Set α)} {ν : Set (Set β)} (h : AdeqAdd γ μ ν) :
    (sm ʻʻ (μ +ᶜ ν : Set (Set γ)) : Set (Set δ)) = μ +ᶜ ν := by
  by_cases hμ : ∃ A, μ = n₀c A
  · by_cases hν : ∃ B, ν = n₀c B
    · obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν
      obtain ⟨X, hX⟩ := h.nc_nonempty A B
      rw [n₀c_cardAdd_n₀c, n₀c_cardAdd_n₀c, nc_eq_n₀c_of_mem hX, sm_img_n₀c]
      exact nc_eq_nc_of_sm hX
    · push Not at hν
      rw [cardAdd_eq_empty_of_right _ hν, cardAdd_eq_empty_of_right _ hν, sm_img_empty]
  · push Not at hμ
    rw [cardAdd_eq_empty_of_left hμ, cardAdd_eq_empty_of_left hμ, sm_img_empty]

/-- The proposition ✱110·44 fails when the argument `μ +_c ν` of `sm''` is in an inadequate type: with
`μ = 1`, `ν = 0` (classes of `Unit`) and the argument in the empty type, `sm''(μ +_c ν) = Λ`,
while `μ +_c ν` among classes of `Unit` is `1`. -/
theorem pm110_44_aux_adequacy : ¬ ∀ μ ν : Set (Set Unit),
    (sm ʻʻ (μ +ᶜ ν : Set (Set Empty)) : Set (Set Unit)) = μ +ᶜ ν := by
  intro h
  have e := h (n₀c Set.univ) (n₀c ∅)
  rw [n₀c_cardAdd_n₀c, n₀c_cardAdd_n₀c,
    nc_eq_empty_of_isEmpty ⟨_, ((clsSumEquiv _ _).symm (Sum.inl ⟨(), trivial⟩)).2⟩,
    sm_img_empty] at e
  have : (Set.univ : Set Unit) ∈ nc Unit ((Set.univ : Set Unit) +ₐ (∅ : Set Unit)) :=
    sm_symm (sm_trans (sm_clsSum_empty _) (sm_refl _))
  rw [← e] at this
  exact this

/-- ✱110·5. \(\vdash .\beta +\alpha = \text{Cnv}ʻʻ(\alpha +\beta)\) -/
theorem pm110_5 {A : Set α} {B : Set β} : B +ₐ A = Cnv ʻʻ (A +ₐ B) := by
  ext Q
  constructor
  · intro hQ
    refine ⟨Q˘, ?_, Cnv_iff.2 rfl⟩
    rcases mem_clsSum.1 hQ with ⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩
    · exact mem_clsSum.2 (Or.inr ⟨y, hy, couple_cnv _ _⟩)
    · exact mem_clsSum.2 (Or.inl ⟨x, hx, couple_cnv _ _⟩)
  · rintro ⟨P, hP, hQ⟩
    rw [Cnv_iff.1 hQ]
    rcases mem_clsSum.1 hP with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · exact mem_clsSum.2 (Or.inr ⟨x, hx, couple_cnv _ _⟩)
    · exact mem_clsSum.2 (Or.inl ⟨y, hy, couple_cnv _ _⟩)

/-- ✱110·501. \(\vdash .\beta + \alpha \text{ sm }\alpha + \beta \quad[*110·5.*73·4]\) -/
theorem pm110_501 {A : Set α} {B : Set β} : sm (B +ₐ A) (A +ₐ B) := sm_clsSum_comm B A

/-- ✱110·51. \(\vdash .\mu +_{\text{c}} \nu =\nu +_{\text{c}} \mu \quad[*110·2·501.*73·37]\) -/
theorem pm110_51 {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ +ᶜ ν : Set (Set γ)) = ν +ᶜ μ := by
  ext X
  constructor
  · rintro ⟨A, B, ⟨hA, hB⟩, h⟩; exact ⟨B, A, ⟨hB, hA⟩, sm_trans h (sm_clsSum_comm A B)⟩
  · rintro ⟨B, A, ⟨hB, hA⟩, h⟩; exact ⟨A, B, ⟨hA, hB⟩, sm_trans h (sm_clsSum_comm B A)⟩

/-- ✱110·52. \[\begin{aligned}\vdash :\xi \text{ sm }(\alpha + \beta ) + \gamma .&\equiv .(\exists \pi ,\rho ,\sigma ).\pi \text{ sm }\alpha .\rho \text{ sm }\beta .\sigma \text{ sm }\gamma .\\ &\pi \cap \rho =\Lambda .\pi \cap \sigma =\Lambda .\rho \cap \sigma =\Lambda .\xi =\pi \cup \rho \cup \sigma\end{aligned}\] -/
theorem pm110_52 {A : Set α} {B : Set β} {G : Set γ} {X : Set δ} :
    sm X (A +ₐ B +ₐ G) ↔ ∃ P Q S : Set δ, (((((sm P A ∧ sm Q B) ∧ sm S G) ∧ P ∩ Q = Λ) ∧
      P ∩ S = Λ) ∧ Q ∩ S = Λ) ∧ X = P ∪ Q ∪ S := by
  show X ∈ nc δ (A +ₐ B +ₐ G) ↔ _
  rw [mem_nc_clsSum]
  constructor
  · rintro ⟨Y, S, ⟨⟨hY, hS⟩, hYS⟩, rfl⟩
    obtain ⟨P, Q, ⟨⟨hP, hQ⟩, hPQ⟩, rfl⟩ := mem_nc_clsSum.1 hY
    rw [inter_eq_null_iff, Set.disjoint_union_left] at hYS
    exact ⟨P, Q, S, ⟨⟨⟨⟨⟨hP, hQ⟩, hS⟩, hPQ⟩, inter_eq_null_iff.2 hYS.1⟩,
      inter_eq_null_iff.2 hYS.2⟩, rfl⟩
  · rintro ⟨P, Q, S, ⟨⟨⟨⟨⟨hP, hQ⟩, hS⟩, hPQ⟩, hPS⟩, hQS⟩, rfl⟩
    refine ⟨P ∪ Q, S, ⟨⟨mem_nc_clsSum.2 ⟨P, Q, ⟨⟨hP, hQ⟩, hPQ⟩, rfl⟩, hS⟩, ?_⟩, rfl⟩
    rw [inter_eq_null_iff, Set.disjoint_union_left]
    exact ⟨inter_eq_null_iff.1 hPS, inter_eq_null_iff.1 hQS⟩

/-- ✱110·521. \[\begin{aligned}\vdash :&\xi \text{ sm }\alpha + (\beta + \gamma ).\equiv .(\exists \pi ,\rho ,\sigma ).\pi \text{ sm }\alpha .\rho \text{ sm }\beta .\sigma \text{ sm }\gamma .\\ &\pi \cap \rho =\Lambda .\pi \cap \sigma =\Lambda .\rho \cap \sigma =\Lambda .\xi =\pi \cup \rho \cup \sigma \quad[*110·501·52]\end{aligned}\] -/
theorem pm110_521 {A : Set α} {B : Set β} {G : Set γ} {X : Set δ} :
    sm X (A +ₐ (B +ₐ G)) ↔ ∃ P Q S : Set δ, (((((sm P A ∧ sm Q B) ∧ sm S G) ∧ P ∩ Q = Λ) ∧
      P ∩ S = Λ) ∧ Q ∩ S = Λ) ∧ X = P ∪ Q ∪ S := by
  rw [← pm110_52]
  exact ⟨fun h => sm_trans h (sm_symm (sm_clsSum_assoc A B G)),
    fun h => sm_trans h (sm_clsSum_assoc A B G)⟩

/-- ✱110·53. \(\vdash .(\alpha + \beta )+ \gamma \text{ sm }\alpha + (\beta + \gamma ) \quad[*110·52·521]\) -/
theorem pm110_53 {A : Set α} {B : Set β} {G : Set γ} : sm (A +ₐ B +ₐ G) (A +ₐ (B +ₐ G)) :=
  sm_clsSum_assoc A B G

/-- ✱110·531 (Df). \(\alpha + \beta + \gamma =(\alpha + \beta ) + \gamma \quad\text{Df}\) -/
theorem pm110_531 {A : Set α} {B : Set β} {G : Set γ} : A +ₐ B +ₐ G = (A +ₐ B) +ₐ G := rfl

/-- ✱110·54. \(\vdash .(\text{Nc}ʻ\alpha +_{\text{c}} \text{Nc}ʻ\beta ) +_{\text{c}} \text{Nc}ʻ\gamma =\text{Nc}ʻ(\alpha + \beta + \gamma )\)

The inner sum is an arithmetical component (IIT): its type `W` is a parameter with the
hypothesis that it is adequate. The arguments `Nc'α`, … of `+_c` are `n₀c A`, … (✱110·03·04).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component Nc'α +_c Nc'β is adequate -/
theorem pm110_54 {W : Type*} {A : Set α} {B : Set β} {G : Set δ}
    (h : AdeqAdd W (n₀c A) (n₀c B)) :
    ((n₀c A +ᶜ n₀c B : Set (Set W)) +ᶜ n₀c G : Set (Set γ)) = nc γ (A +ₐ B +ₐ G) := by
  obtain ⟨X, hX⟩ := h.nc_nonempty A B
  rw [n₀c_cardAdd_n₀c, nc_eq_n₀c_of_mem hX, n₀c_cardAdd_n₀c]
  exact nc_eq_nc_of_sm (sm_clsSum hX (sm_refl G))

/-- ✱110·541. \(\vdash .\text{Nc}ʻ\alpha +_{\text{c}} (\text{Nc}ʻ\beta +_{\text{c}} \text{Nc}ʻ\gamma )=\text{Nc}ʻ(\alpha + \beta + \gamma )\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component Nc'β +_c Nc'γ is adequate -/
theorem pm110_541 {W : Type*} {A : Set α} {B : Set β} {G : Set δ}
    (h : AdeqAdd W (n₀c B) (n₀c G)) :
    (n₀c A +ᶜ (n₀c B +ᶜ n₀c G : Set (Set W)) : Set (Set γ)) = nc γ (A +ₐ B +ₐ G) := by
  obtain ⟨X, hX⟩ := h.nc_nonempty B G
  rw [n₀c_cardAdd_n₀c, nc_eq_n₀c_of_mem hX, n₀c_cardAdd_n₀c]
  exact nc_eq_nc_of_sm (sm_trans (sm_clsSum (sm_refl A) hX) (sm_symm (sm_clsSum_assoc A B G)))

/-- ✱110·55. \(\vdash .(\text{Nc}ʻ\alpha +_{\text{c}} \text{Nc}ʻ\beta ) +_{\text{c}} \text{Nc}ʻ\gamma =\text{Nc}ʻ\alpha +_{\text{c}} (\text{Nc}ʻ\beta +_{\text{c}} \text{Nc}ʻ\gamma ) \quad[*110·54·541]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components are adequate -/
theorem pm110_55 {W₁ W₂ : Type*} {A : Set α} {B : Set β} {G : Set δ}
    (h₁ : AdeqAdd W₁ (n₀c A) (n₀c B)) (h₂ : AdeqAdd W₂ (n₀c B) (n₀c G)) :
    ((n₀c A +ᶜ n₀c B : Set (Set W₁)) +ᶜ n₀c G : Set (Set γ)) =
      n₀c A +ᶜ (n₀c B +ᶜ n₀c G : Set (Set W₂)) :=
  (pm110_54 h₁).trans (pm110_541 h₂).symm

/-- ✱110·551. \[\begin{aligned}&\vdash .(\text{N}_{0}\text{c}ʻ\alpha +_{\text{c}} \text{N}_{0}\text{c}ʻ\beta ) +_{\text{c}} \text{N}_{0}\text{c}ʻ\gamma =\text{N}_{0}\text{c}ʻ\alpha +_{\text{c}} (\text{N}_{0}\text{c}ʻ\beta +_{\text{c}} \text{N}_{0}\text{c}ʻ\gamma )\\ &[*110·55.(*110·03·04)]\end{aligned}\]

(After normal adjustment this is the statement of ✱110·55.)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components are adequate -/
theorem pm110_551 {W₁ W₂ : Type*} {A : Set α} {B : Set β} {G : Set δ}
    (h₁ : AdeqAdd W₁ (n₀c A) (n₀c B)) (h₂ : AdeqAdd W₂ (n₀c B) (n₀c G)) :
    ((n₀c A +ᶜ n₀c B : Set (Set W₁)) +ᶜ n₀c G : Set (Set γ)) =
      n₀c A +ᶜ (n₀c B +ᶜ n₀c G : Set (Set W₂)) :=
  pm110_55 h₁ h₂

/-- ✱110·56. \(\vdash .(\mu +_{\text{c}} \nu ) +_{\text{c}} \varpi =\mu +_{\text{c}} (\nu +_{\text{c}} \varpi )\)

(Convention IIT, encoding decision 6.) The real variables `μ`, `ν`, `ϖ` have independent types;
the inner sums are arithmetical components, each with its own adequate type.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components μ +_c ν and ν +_c ϖ are adequate -/
theorem pm110_56 {α₁ α₂ α₃ W₁ W₂ : Type*} {μ : Set (Set α₁)} {ν : Set (Set α₂)} {ϖ : Set (Set α₃)}
    (h₁ : AdeqAdd W₁ μ ν) (h₂ : AdeqAdd W₂ ν ϖ) :
    ((μ +ᶜ ν : Set (Set W₁)) +ᶜ ϖ : Set (Set γ)) = μ +ᶜ (ν +ᶜ ϖ : Set (Set W₂)) := by
  by_cases hμ : ∃ A, μ = n₀c A
  · by_cases hν : ∃ B, ν = n₀c B
    · by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν; obtain ⟨C, rfl⟩ := hϖ
        exact pm110_55 h₁ h₂
      · push Not at hϖ
        rw [cardAdd_eq_empty_of_right _ hϖ, cardAdd_eq_empty_of_right (ν := ϖ) _ hϖ,
          cardAdd_empty]
    · push Not at hν
      rw [cardAdd_eq_empty_of_right (ν := ν) _ hν, cardAdd_eq_empty_of_left (μ := ν) hν,
        empty_cardAdd, cardAdd_empty]
  · push Not at hμ
    rw [cardAdd_eq_empty_of_left (μ := μ) hμ, cardAdd_eq_empty_of_left (μ := μ) hμ,
      empty_cardAdd]

/-- Without IIT ✱110·56 is false: with the inner sum `1 +_c 0` in a type with no members it is
`Λ`, while `1 +_c (0 +_c 0)` (all in `Bool`) is not. -/
theorem pm110_56_aux_IIT : ¬ ∀ {μ ν ϖ : Set (Set Bool)},
    ((μ +ᶜ ν : Set (Set Empty)) +ᶜ ϖ : Set (Set Bool)) = μ +ᶜ (ν +ᶜ ϖ : Set (Set Bool)) := by
  intro h
  have e := @h (n₀c {true}) (n₀c ∅) (n₀c ∅)
  rw [n₀c_cardAdd_n₀c, nc_eq_empty_of_isEmpty ⟨_, ((clsSumEquiv _ _).symm (Sum.inl ⟨true, rfl⟩)).2⟩,
    empty_cardAdd] at e
  have hin : ({true} : Set Bool) ∈ (n₀c ({true} : Set Bool) +ᶜ
      (n₀c (∅ : Set Bool) +ᶜ n₀c (∅ : Set Bool) : Set (Set Bool)) : Set (Set Bool)) := by
    rw [n₀c_cardAdd_n₀c (A := (∅ : Set Bool)),
      nc_eq_n₀c_of_mem (sm_iff_nonempty_equiv.2 ⟨((clsSumEquiv (∅ : Set Bool)
        (∅ : Set Bool)).trans (Equiv.sumEmpty _ _)).symm⟩ :
          (∅ : Set Bool) ∈ nc Bool ((∅ : Set Bool) +ₐ (∅ : Set Bool))),
      n₀c_cardAdd_n₀c]
    exact sm_iff_nonempty_equiv.2 ⟨((clsSumEquiv _ _).trans (Equiv.sumEmpty _ _)).symm⟩
  rw [← e] at hin
  exact hin

/-- ✱110·561 (Df). \(\mu +_{\text{c}} \nu +_{\text{c}} \varpi = (\mu +_{\text{c}} \nu ) +_{\text{c}} \varpi \quad\text{Df}\)

Realized by `infixl`; the inner sum is an arithmetical component, so its type is a separate
parameter `W` (IIT). -/
theorem pm110_561 {W : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set δ)} :
    ((μ +ᶜ ν : Set (Set W)) +ᶜ ϖ : Set (Set γ)) = ((μ +ᶜ ν : Set (Set W)) +ᶜ ϖ : Set (Set γ)) := rfl

/-- ✱110·57. \(\vdash .(\mu +_{\text{c}} \nu ) +_{\text{c}} (\varpi +_{\text{c}} \rho ) = \mu +_{\text{c}} \nu +_{\text{c}} \varpi +_{\text{c}} \rho \quad[*110·56.(*110·561)]\)

The right-hand side is `((μ +_c ν) +_c ϖ) +_c ρ` (✱110·561); each inner sum has its own
adequate type (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components are adequate -/
theorem pm110_57 {α₁ α₂ α₃ α₄ W₁ W₂ W₃ W₄ : Type*} {μ : Set (Set α₁)} {ν : Set (Set α₂)}
    {ϖ : Set (Set α₃)} {ρ : Set (Set α₄)} (h₁ : AdeqAdd W₁ μ ν) (h₂ : AdeqAdd W₂ ϖ ρ)
    (h₃ : AdeqAdd W₃ μ ν) (h₄ : AdeqAdd W₄ (μ +ᶜ ν : Set (Set W₃)) ϖ) :
    ((μ +ᶜ ν : Set (Set W₁)) +ᶜ (ϖ +ᶜ ρ : Set (Set W₂)) : Set (Set γ)) =
      (((μ +ᶜ ν : Set (Set W₃)) +ᶜ ϖ : Set (Set W₄)) +ᶜ ρ : Set (Set γ)) := by
  by_cases hμ : ∃ A, μ = n₀c A
  swap
  · push Not at hμ
    rw [cardAdd_eq_empty_of_left (μ := μ) hμ, cardAdd_eq_empty_of_left (μ := μ) hμ,
      empty_cardAdd, empty_cardAdd, empty_cardAdd]
  by_cases hν : ∃ B, ν = n₀c B
  swap
  · push Not at hν
    rw [cardAdd_eq_empty_of_right (ν := ν) _ hν, cardAdd_eq_empty_of_right (ν := ν) _ hν,
      empty_cardAdd, empty_cardAdd, empty_cardAdd]
  by_cases hϖ : ∃ C, ϖ = n₀c C
  swap
  · push Not at hϖ
    rw [cardAdd_eq_empty_of_left (μ := ϖ) hϖ, cardAdd_eq_empty_of_right (ν := ϖ) _ hϖ,
      cardAdd_empty, empty_cardAdd]
  by_cases hρ : ∃ E, ρ = n₀c E
  swap
  · push Not at hρ
    rw [cardAdd_eq_empty_of_right (ν := ρ) _ hρ, cardAdd_eq_empty_of_right (ν := ρ) _ hρ,
      cardAdd_empty]
  obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν; obtain ⟨C, rfl⟩ := hϖ; obtain ⟨E, rfl⟩ := hρ
  obtain ⟨X₁, hX₁⟩ := h₁.nc_nonempty A B
  obtain ⟨X₂, hX₂⟩ := h₂.nc_nonempty C E
  obtain ⟨X₃, hX₃⟩ := h₃.nc_nonempty A B
  obtain ⟨X₄, hX₄⟩ := h₄.nc_nonempty X₃ C
  rw [n₀c_cardAdd_n₀c (γ := W₁), nc_eq_n₀c_of_mem hX₁, n₀c_cardAdd_n₀c (γ := W₂),
    nc_eq_n₀c_of_mem hX₂, n₀c_cardAdd_n₀c, n₀c_cardAdd_n₀c (γ := W₃), nc_eq_n₀c_of_mem hX₃,
    n₀c_cardAdd_n₀c (γ := W₄), nc_eq_n₀c_of_mem hX₄, n₀c_cardAdd_n₀c]
  apply nc_eq_nc_of_sm
  refine sm_trans (sm_clsSum hX₁ hX₂) (sm_trans ?_ (sm_symm (sm_clsSum hX₄ (sm_refl E))))
  refine sm_trans (sm_symm (sm_clsSum_assoc (A +ₐ B) C E)) ?_
  exact sm_clsSum (sm_clsSum (sm_symm hX₃) (sm_refl C)) (sm_refl E)

/-- ✱110·6. \(\vdash :\mu \in \text{NC}.\supset .\mu +_{\text{c}} 0 = \text{ sm }ʻʻ\mu\)

`0` is an arithmetical argument with its own type `W` (IIT; no hypothesis is needed for `0`). -/
theorem pm110_6 {β' W : Type*} {μ : Set (Set α)} :
    μ ∈ NC β' → (μ +ᶜ (zero : Set (Set W)) : Set (Set γ)) = sm ʻʻ μ := by
  intro hμ
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [empty_cardAdd, sm_img_empty]
  rw [zero_eq_n₀c_empty, n₀c_cardAdd_n₀c, sm_img_n₀c]
  exact nc_eq_nc_of_sm (sm_clsSum_empty A)

/-- ✱110·61. \(\vdash .\text{Nc}ʻ\alpha +_{\text{c}} 0=\text{Nc}ʻ\alpha\) -/
theorem pm110_61 {W : Type*} {A : Set α} :
    (n₀c A +ᶜ (zero : Set (Set W)) : Set (Set γ)) = nc γ A := by
  rw [pm110_6 (n₀c_mem_NC A), sm_img_n₀c]

/-- ✱110·62. \(\vdash :\mu +_{\text{c}} \nu =0.\equiv .\mu =0.\nu =0\)

`μ = 0` and `ν = 0` are in the types of `μ` and `ν`, and the `0` of the left-hand side in the
type of the sum. -/
theorem pm110_62 {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ +ᶜ ν : Set (Set γ)) = zero ↔ μ = zero ∧ ν = zero := by
  constructor
  · intro h
    have h0 : (∅ : Set γ) ∈ (μ +ᶜ ν : Set (Set γ)) := by rw [h, zero_eq]; rfl
    obtain ⟨A, B, ⟨rfl, rfl⟩, hs⟩ := h0
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hs
    have hA : A = ∅ := Set.eq_empty_iff_forall_notMem.2 fun a ha =>
      (e.symm ((clsSumEquiv A B).symm (Sum.inl ⟨a, ha⟩))).2
    have hB : B = ∅ := Set.eq_empty_iff_forall_notMem.2 fun b hb =>
      (e.symm ((clsSumEquiv A B).symm (Sum.inr ⟨b, hb⟩))).2
    rw [hA, hB, zero_eq_n₀c_empty, zero_eq_n₀c_empty]
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rw [zero_eq_n₀c_empty, zero_eq_n₀c_empty, n₀c_cardAdd_n₀c, zero_eq_nc_empty (α := α)]
    exact nc_eq_nc_of_sm (sm_clsSum_empty ∅)

/-- ✱110·63. \(\vdash .\text{Nc}ʻ\alpha +_{\text{c}} 1=\hat{\xi} \{(\exists \gamma ,y).\gamma \text{ sm }\alpha .y{\sim}\in \gamma .\xi =\gamma \cup \iota ʻy\}\)

The constant `1` is an arithmetical argument with its own type `W`, in which it exists (IIT:
`∃!1`, i.e. `[Nonempty W]`).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the `1` is taken in a type
in which it exists -/
theorem pm110_63 {W : Type*} [Nonempty W] {A : Set α} :
    (n₀c A +ᶜ (one : Set (Set W)) : Set (Set γ)) =
      {X | ∃ (G : Set γ) (y : γ), (sm G A ∧ y ∉ G) ∧ X = G ∪ ι y} := by
  obtain ⟨w⟩ := ‹Nonempty W›
  rw [one_eq_n₀c_singleton w, n₀c_cardAdd_n₀c]
  ext X
  rw [mem_nc_clsSum]
  constructor
  · rintro ⟨G, H, ⟨⟨hG, hH⟩, hGH⟩, rfl⟩
    have hH1 : H ∈ (one : Set (Set γ)) := by
      rw [one_eq_nc_unitCls w, unitCls_eq_singleton]; exact hH
    obtain ⟨y, rfl⟩ := hH1
    refine ⟨G, y, ⟨hG, fun hy => ?_⟩, rfl⟩
    have : y ∈ G ∩ ι y := ⟨hy, rfl⟩
    rw [hGH, Null_eq_empty] at this
    exact this
  · rintro ⟨G, y, ⟨hG, hy⟩, rfl⟩
    refine ⟨G, ι y, ⟨⟨hG, ?_⟩, ?_⟩, rfl⟩
    · have : ι y ∈ (one : Set (Set γ)) := ⟨y, rfl⟩
      rw [one_eq_nc_unitCls w, unitCls_eq_singleton] at this
      exact this
    · rw [inter_eq_null_iff, Set.disjoint_right]
      intro z hz hzG
      rw [mem_unitCls.1 hz] at hzG
      exact hy hzG

/-- ✱110·631. \(\vdash :\mu \in \text{NC}.\supset \mu +_{\text{c}}1=\hat{\xi} \{(\exists \gamma ,y).\gamma \in \text{ sm }ʻʻ\mu .y{\sim}\in \gamma .\xi =\gamma \cup \iota ʻy\}\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the `1` is taken in a type
in which it exists -/
theorem pm110_631 {β' W : Type*} [Nonempty W] {μ : Set (Set α)} :
    μ ∈ NC β' → (μ +ᶜ (one : Set (Set W)) : Set (Set γ)) =
      {X | ∃ (G : Set γ) (y : γ), (G ∈ sm ʻʻ μ ∧ y ∉ G) ∧ X = G ∪ ι y} := by
  intro hμ
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [empty_cardAdd, sm_img_empty]; ext X; simp
  rw [pm110_63]
  simp only [mem_sm_img_n₀c]

/-- ✱110·632. \(\vdash :\mu \in \text{NC}.\supset .\mu +_{\text{c}} 1=\hat{\xi} \{(\exists y).y\in \xi .\xi -\iota ʻy\in \text{ sm }ʻʻ\mu \}\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the `1` is taken in a type
in which it exists -/
theorem pm110_632 {β' W : Type*} [Nonempty W] {μ : Set (Set α)} :
    μ ∈ NC β' → (μ +ᶜ (one : Set (Set W)) : Set (Set γ)) =
      {X | ∃ y, y ∈ X ∧ X \ ι y ∈ sm ʻʻ μ} := by
  intro hμ
  rw [pm110_631 hμ]
  ext X
  constructor
  · rintro ⟨G, y, ⟨hG, hy⟩, rfl⟩
    refine ⟨y, Or.inr rfl, ?_⟩
    rwa [Set.union_sdiff_cancel_right]
    rw [Set.subset_empty_iff, ← Set.disjoint_iff_inter_eq_empty, unitCls_eq_singleton,
      Set.disjoint_singleton_right]
    exact hy
  · rintro ⟨y, hy, hX⟩
    refine ⟨X \ ι y, y, ⟨hX, fun h => h.2 rfl⟩, ?_⟩
    rw [Set.sdiff_union_self, Set.union_eq_self_of_subset_right]
    rw [unitCls_eq_singleton]; exact Set.singleton_subset_iff.2 hy

/-- ✱110·64. \(\vdash .0 +_{\text{c}} 0=0 \quad[*110·62]\)

The two `0`s are arithmetical occurrences with their own types (IIT; no hypothesis is needed for
`0`). -/
theorem pm110_64 {W₁ W₂ : Type*} :
    ((zero : Set (Set W₁)) +ᶜ (zero : Set (Set W₂)) : Set (Set γ)) = zero :=
  (pm110_62).2 ⟨rfl, rfl⟩

/-- ✱110·641. \(\vdash .1 +_{\text{c}} 0=0 +_{\text{c}} 1=1 \quad[*110·51·61.*101·2]\)

A chain: the conjunction of its links; each constant argument has its own type (IIT), and the
`1`s are taken in types in which they exist.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the 1s are taken in types
in which they exist (PM assumes every type has a member, Introduction, Ch. I) -/
theorem pm110_641 {W₁ W₂ W₃ W₄ : Type*} [Nonempty W₁] [Nonempty W₄] :
    ((one : Set (Set W₁)) +ᶜ (zero : Set (Set W₂)) : Set (Set γ)) =
        (zero : Set (Set W₃)) +ᶜ (one : Set (Set W₄)) ∧
      ((zero : Set (Set W₃)) +ᶜ (one : Set (Set W₄)) : Set (Set γ)) = one := by
  obtain ⟨a⟩ := ‹Nonempty W₁›
  obtain ⟨b⟩ := ‹Nonempty W₄›
  have h2 : ((zero : Set (Set W₃)) +ᶜ (one : Set (Set W₄)) : Set (Set γ)) = one := by
    rw [zero_eq_n₀c_empty, one_eq_n₀c_singleton b, n₀c_cardAdd_n₀c, one_eq_nc_unitCls b,
      unitCls_eq_singleton]
    exact nc_eq_nc_of_sm (sm_empty_clsSum _)
  refine ⟨?_, h2⟩
  rw [h2, pm110_51, zero_eq_n₀c_empty, one_eq_n₀c_singleton a, n₀c_cardAdd_n₀c,
    one_eq_nc_unitCls a, unitCls_eq_singleton]
  exact nc_eq_nc_of_sm (sm_empty_clsSum _)

/-- ✱110·642. \(\vdash .2 +_{\text{c}} 0=0 +_{\text{c}} 2=2 \quad[*110·51·61.*101·31]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the 2s are taken in types
in which they exist -/
theorem pm110_642 {W₁ W₂ W₃ W₄ : Type*} (h₁ : (two : Set (Set W₁)).Nonempty)
    (h₄ : (two : Set (Set W₄)).Nonempty) :
    ((two : Set (Set W₁)) +ᶜ (zero : Set (Set W₂)) : Set (Set γ)) =
        (zero : Set (Set W₃)) +ᶜ (two : Set (Set W₄)) ∧
      ((zero : Set (Set W₃)) +ᶜ (two : Set (Set W₄)) : Set (Set γ)) = two := by
  obtain ⟨_, a, a', haa', rfl⟩ := h₁
  obtain ⟨_, b, b', hbb', rfl⟩ := h₄
  have h2 : ((zero : Set (Set W₃)) +ᶜ (two : Set (Set W₄)) : Set (Set γ)) = two := by
    rw [zero_eq_n₀c_empty, two_eq_n₀c_pair hbb', n₀c_cardAdd_n₀c, two_eq_nc_pair hbb']
    exact nc_eq_nc_of_sm (sm_empty_clsSum _)
  refine ⟨?_, h2⟩
  rw [h2, pm110_51, zero_eq_n₀c_empty, two_eq_n₀c_pair haa', n₀c_cardAdd_n₀c, two_eq_nc_pair haa']
  exact nc_eq_nc_of_sm (sm_empty_clsSum _)

/-- ✱110·643. \(\vdash .1 +_{\text{c}} 1=2\)

(Constant formal numbers under IIT.) The two `1`s are arithmetical occurrences (IT does not bind
them): each has its own type, with the IIT hypothesis `∃!1` (`[Nonempty W]`); the equation is in
a free type `γ` (in which `2` may be `Λ`, and then so is `1 +_c 1`).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the 1s are taken in types
in which they exist (PM assumes every type has a member, Introduction, Ch. I) -/
theorem pm110_643 {W₁ W₂ : Type*} [Nonempty W₁] [Nonempty W₂] :
    ((one : Set (Set W₁)) +ᶜ (one : Set (Set W₂)) : Set (Set γ)) = two := by
  obtain ⟨a⟩ := ‹Nonempty W₁›
  obtain ⟨b⟩ := ‹Nonempty W₂›
  rw [one_eq_n₀c_singleton a, one_eq_n₀c_singleton b, n₀c_cardAdd_n₀c]
  have hc : Nat.card ↥(({a} : Set W₁) +ₐ ({b} : Set W₂)) = 2 := by
    rw [Nat.card_congr (clsSumEquiv _ _), Nat.card_sum]; simp
  have hfin : Finite ↥(({a} : Set W₁) +ₐ ({b} : Set W₂)) :=
    Finite.of_equiv _ (clsSumEquiv _ _).symm
  ext X
  rw [mem_nc_iff_equiv]
  constructor
  · rintro ⟨e⟩
    have h2 : X.ncard = 2 := by rw [← Nat.card_coe_set_eq, Nat.card_congr e, hc]
    obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.1 h2
    exact ⟨x, y, hxy, by rw [unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]⟩
  · rintro ⟨x, y, hxy, rfl⟩
    rw [unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]
    have : Finite ↥({x, y} : Set γ) := Set.toFinite _
    apply Finite.card_eq.1
    rw [Nat.card_coe_set_eq, Set.ncard_pair hxy, hc]

/-- ✱110·7. \(\vdash :\beta \subset \alpha .\supset .(\exists \mu ).\mu \in \text{NC}.\text{Nc}ʻ\alpha =\text{Nc}ʻ\beta +_{\text{c}} \mu\)

`Nc'β` is written `n₀c B` (✱110·04); the equation is in a free type `γ`. The apparent variable
`μ` ranges over the cardinals of classes of the type of `α` (PM's `μ` is `Nc'(α − β)`), and its
`NC` is `NC^α(α)`.

**Status.** proved (reading): the type of the apparent variable `μ` and of its `NC` (left
ambiguous by PM) is that of `Nc'(α − β)` in PM's demonstration, the type of `α` -/
theorem pm110_7 {A B : Set α} :
    B ⊆ A → ∃ μ : Set (Set α), μ ∈ NC α ∧ nc γ A = (n₀c B +ᶜ μ : Set (Set γ)) := by
  intro h
  refine ⟨n₀c (A \ B), n₀c_mem_NC _, ?_⟩
  rw [n₀c_cardAdd_n₀c]
  apply nc_eq_nc_of_sm
  have hd : B ∩ (A \ B) = Λ := by rw [inter_eq_null_iff]; exact Set.disjoint_sdiff_right
  have := pm110_14 hd
  rwa [Set.union_sdiff_cancel h] at this

/-- ✱110·71. \(\vdash :(\exists \mu ).\text{Nc}ʻ\alpha =\text{Nc}ʻ\beta +_{\text{c}} \mu .\supset .(\exists \delta ).\delta \text{ sm }\beta .\delta \subset \alpha\)

Convention AT (PM applies it here): the equation `Nc'α = Nc'β +_c μ` is in a type `γ` adequate
for both sides; the type `W` of the apparent variable `μ` is free, and the adequacy of `γ` for
`Nc'β +_c μ` is stated for any term of the type of `μ` (`Λ`). The argument `Nc'β` of `+_c` is
`n₀c B` (✱110·04).

**Status.** proved (reading): convention AT (Prefatory Statement, VI): the equation
Nc'α = Nc'β +_c μ is taken in a type adequate for both sides -/
theorem pm110_71 {W : Type*} {A : Set α} {B : Set β}
    (hA : AdeqNc γ A) (_hB : AdeqAdd γ (n₀c B) (Λ : Set (Set W))) :
    (∃ μ : Set (Set W), nc γ A = (n₀c B +ᶜ μ : Set (Set γ))) → ∃ H : Set α, sm H B ∧ H ⊆ A := by
  rintro ⟨μ, hμ⟩
  obtain ⟨X, hX⟩ := hA.nc_nonempty A
  have hXA : sm X A := hX
  rw [hμ] at hX
  obtain ⟨B', C, ⟨hB', -⟩, hs⟩ := hX
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (sm_trans (sm_symm hXA) hs)
  obtain ⟨f⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 hB')
  let g : B → α := fun b => (e.symm ((clsSumEquiv B' C).symm (Sum.inl (f b))) : α)
  have hg : Function.Injective g := fun b b' h => f.injective (Sum.inl_injective
    ((clsSumEquiv B' C).symm.injective (e.symm.injective (Subtype.ext h))))
  refine ⟨Set.range g, sm_of_equiv (Equiv.ofInjective g hg).symm, ?_⟩
  rintro _ ⟨b, rfl⟩
  exact (e.symm _).2

/-- ✱110·72. \(\vdash :(\exists \delta ).\delta \text{ sm }\beta .\delta \subset \alpha .\equiv .(\exists \mu ).\mu \in \text{NC}.\text{Nc}ʻ\alpha =\text{Nc}ʻ\beta +_{\text{c}} \mu\)

As ✱110·71 (convention AT); the apparent variable `μ` ranges over the cardinals of classes of the
type of `α`, with its `NC` as in ✱110·7.

**Status.** proved (reading): convention AT (Prefatory Statement, VI): the equation
Nc'α = Nc'β +_c μ is taken in a type adequate for both sides; the type of `μ` is that of ✱110·7 -/
theorem pm110_72 {A : Set α} {B : Set β}
    (hA : AdeqNc γ A) (hB : AdeqAdd γ (n₀c B) (Λ : Set (Set α))) :
    (∃ H : Set α, sm H B ∧ H ⊆ A) ↔
      ∃ μ : Set (Set α), μ ∈ NC α ∧ nc γ A = (n₀c B +ᶜ μ : Set (Set γ)) := by
  constructor
  · rintro ⟨H, hH, hHA⟩
    refine ⟨n₀c (A \ H), n₀c_mem_NC _, ?_⟩
    rw [n₀c_cardAdd_n₀c]
    apply nc_eq_nc_of_sm
    have hd : H ∩ (A \ H) = Λ := by rw [inter_eq_null_iff]; exact Set.disjoint_sdiff_right
    have := pm110_14 hd
    rw [Set.union_sdiff_cancel hHA] at this
    exact sm_trans this (sm_clsSum hH (sm_refl _))
  · rintro ⟨μ, -, h⟩
    exact pm110_71 hA (W := α) hB ⟨μ, h⟩

/-!
## [✱111] Double similarity

*(Vol. 2, p. 88)*

> *Summary of* *111.
>
> …

**Lean reading.** `κ sm̄ sm̄ λ` is `smsmbar K L` (`K : Set (Set α)`, `L : Set (Set β)`), the
double correlators `T : α → β → Prop`; `T_∈` is `imgRel T` (so `T_∈''λ` is `imgRel T ʻʻ L`,
`T_∈ ↾ λ` is `imgRel T ↾ L`); `κ sm sm λ` is `smsm K L`. `Crp(S)'β` contains the description
`S'β`, which may fail to exist: `Crp S` is a relation and `ψ(Crp(S)'β)` is `Desc (Crp S) B ψ`
(`desc_Crp`); `R'Crp(S)'β` is `Desc2 R (Crp S) B ψ`. `ṡ''`, `D''` are images under `graph sumRel`
and `D`; `α sm̄''λ` is `opL smbar A ʻʻ L` (✱38·01). The e-text prints `ᗡ'''sm` for `Rl'sm`
(the class of relations contained in `sm`, `rl sm`) in ✱111·112·5; the Summary has `Rl'sm`. `Mult
ax` is taken at the type of the classes `Crp(S)'β` whose selections are used (`MultAx (α → β →
Prop)`); it is a theorem of Lean but is kept as a hypothesis. ✱111·31·311·313·32·321·46 are false
as printed when `λ` has members outside `ᗡ'S` (or `S'β` does not exist): PM's demonstrations use
`β ∈ λ . ≡ . R'Crp(S)'β ∈ Crp(S)'β`, which needs `E!S'β`; the corrected forms add `λ ⊂ ᗡ'S`
(`E!S'β` in ✱111·313), and the counterexample `S = Λ̇`, `λ = ι'V` is proved.

**Status.** proved (all propositions; ✱111·112·5·51 proved (reading), ✱111·31·311·313·32·321·46 proved (corrected), see their docstrings)
-/

/-- ✱111·01 (Df). \(\kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda = (1\rightarrow 1)\cap \overleftarrow{\text{ᗡ}}ʻsʻ\lambda \cap \hat{T} (\kappa = T_{\in }ʻʻ\lambda ) \quad\text{Df}\) -/
theorem pm111_01 {K : Set (Set α)} {L : Set (Set β)} :
    smsmbar K L = arrow one one ∩ rels Dcnv (sumCls L) ∩ {T | K = imgRel T ʻʻ L} := rfl

/-- ✱111·02 (Df). \(\text{Crp}(S)ʻ\beta = (Sʻ\beta ) \,\overline{\text{ sm }}\, \beta \quad \text{Df}\)

`Crp(S)'β` contains the description `S'β`, so the Df defines the relation `Crp S` of
`(S'β) sm̄ β` to `β` (Basic §5): `ψ(Crp(S)'β)` is `Desc (Crp S) B ψ` (`desc_Crp`). -/
theorem pm111_02 {S : Set α → Set β → Prop} :
    Crp S = fun U B => Desc S B (fun A => U = smbar A B) := rfl

/-- ✱111·03 (Df). \(\text{ sm } \text{ sm } = \hat{\kappa} \hat{\lambda} (\exists ! \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda ) \quad\text{Df}\) -/
theorem pm111_03 : (smsm : Set (Set α) → Set (Set β) → Prop) = fun K L => (smsmbar K L).Nonempty :=
  rfl

/-- ✱111·1. \(\vdash :T\in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda . \equiv .T\in 1\rightarrow 1.\text{ᗡ}ʻT= sʻ\lambda .\kappa = T_{\in }ʻʻ\lambda \quad [(*111·01)]\) -/
theorem pm111_1 {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop} :
    T ∈ smsmbar K L ↔ (T ∈ arrow one one ∧ codom T = sumCls L) ∧ K = imgRel T ʻʻ L := by
  rw [mem_smsmbar_iff, eq_comm (a := sumCls L)]

/-- ✱111·11. \(\vdash :T\in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda . \equiv .T\in (sʻ\kappa ).\,\overline{\text{ sm }}\, (sʻ\lambda ).T_{\in }\upharpoonright \lambda \in \kappa \,\overline{\text{ sm }}\, \lambda \) -/
theorem pm111_11 {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop} :
    T ∈ smsmbar K L ↔ T ∈ smbar (sumCls K) (sumCls L) ∧ imgRel T ↾ L ∈ smbar K L := by
  constructor
  · intro h
    obtain ⟨⟨hT, hL⟩, hK⟩ := mem_smsmbar_iff.1 h
    subst hK
    refine ⟨mem_smbar_iff.2 ⟨⟨hT, ?_⟩, hL⟩, imgRel_cres_mem_smbar hT hL.le⟩
    rw [sumCls_imgRel_img, hL, img_codom]
  · rintro ⟨h1, h2⟩
    obtain ⟨⟨hT, -⟩, hL⟩ := mem_smbar_iff.1 h1
    obtain ⟨⟨-, hK⟩, -⟩ := mem_smbar_iff.1 h2
    exact mem_smsmbar_iff.2 ⟨⟨hT, hL⟩, hK.trans (dom_imgRel_cres T L)⟩

/-- ✱111·111. \(\vdash :T\in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda .\supset .T_{\in }\upharpoonright \lambda \,\unicode{x2abd}\, \text{ sm }\) -/
theorem pm111_111 {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop} :
    T ∈ smsmbar K L → imgRel T ↾ L ⪽ sm := by
  intro h u B ⟨hu, hB⟩
  obtain ⟨⟨hT, hL⟩, -⟩ := mem_smsmbar_iff.1 h
  rw [show u = T ʻʻ B from hu]
  exact sm_img_of_oneone hT ((subset_sumCls hB).trans hL.le)

/-- ✱111·112. \(\vdash :T\in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda .\supset .T_{\in }\upharpoonright \lambda \in \kappa \,\overline{\text{ sm }}\, \lambda \cap \text{ᗡ}ʻʻʻ\text{ sm } \quad[*111·11·111]\)

**Status.** proved (reading): transcription error: the e-text prints `ᗡ'''sm` for `Rl'sm` (the
relations contained in `sm`), as the Summary of ✱111 ("`T_∈ ↾ λ ∈ κ sm̄ λ ∩ Rl'sm`") and the
references ✱111·11·111 show. -/
theorem pm111_112 {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop} :
    T ∈ smsmbar K L → imgRel T ↾ L ∈ smbar K L ∩ rl sm :=
  fun h => ⟨(pm111_11.1 h).2, pm111_111 h⟩

/-- ✱111·12. \(\vdash :sʻ\lambda \subset \alpha .\supset .(T\upharpoonright \alpha )_{\in }ʻʻ\lambda = T_{\in }ʻʻ\lambda .(T\upharpoonright \alpha )_{\in }\upharpoonright \lambda = T_{\in }\upharpoonright \lambda\) -/
theorem pm111_12 {L : Set (Set β)} {A : Set β} {T : α → β → Prop} :
    sumCls L ⊆ A → imgRel (T ↾ A) ʻʻ L = imgRel T ʻʻ L ∧ imgRel (T ↾ A) ↾ L = imgRel T ↾ L := by
  intro h
  have key : ∀ B, B ∈ L → (T ↾ A) ʻʻ B = T ʻʻ B := by
    intro B hB
    ext x
    exact ⟨fun ⟨y, hy, hxy, _⟩ => ⟨y, hy, hxy⟩,
      fun ⟨y, hy, hxy⟩ => ⟨y, hy, hxy, h (subset_sumCls hB hy)⟩⟩
  constructor
  · ext u
    exact ⟨fun ⟨B, hB, hu⟩ => ⟨B, hB, (show u = _ from hu).trans (key B hB)⟩,
      fun ⟨B, hB, hu⟩ => ⟨B, hB, (show u = _ from hu).trans (key B hB).symm⟩⟩
  · funext u B
    apply propext
    exact ⟨fun ⟨hu, hB⟩ => ⟨(show u = _ from hu).trans (key B hB), hB⟩,
      fun ⟨hu, hB⟩ => ⟨(show u = _ from hu).trans (key B hB).symm, hB⟩⟩

/-- ✱111·121. \(\vdash .(T\upharpoonright sʻ\lambda )_{\in }ʻʻ\lambda = T_{\in }ʻʻ\lambda = (T_{\in }\upharpoonright \lambda )ʻʻ\lambda .(T\upharpoonright sʻ\lambda )_{\in }\upharpoonright \lambda = T_{\in }\upharpoonright \lambda\)

The chain `A = B = C` with a further equation: `(A = B ∧ B = C) ∧ D = E`. -/
theorem pm111_121 {L : Set (Set β)} {T : α → β → Prop} :
    (imgRel (T ↾ sumCls L) ʻʻ L = imgRel T ʻʻ L ∧ imgRel T ʻʻ L = (imgRel T ↾ L) ʻʻ L) ∧
      imgRel (T ↾ sumCls L) ↾ L = imgRel T ↾ L := by
  obtain ⟨h1, h2⟩ := pm111_12 (T := T) (le_refl (sumCls L))
  refine ⟨⟨h1, ?_⟩, h2⟩
  ext u
  exact ⟨fun ⟨B, hB, hu⟩ => ⟨B, hB, hu, hB⟩, fun ⟨B, hB, hu, _⟩ => ⟨B, hB, hu⟩⟩

/-- ✱111·13. \(\vdash .I\upharpoonright sʻ\lambda \in \lambda \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda\) -/
theorem pm111_13 {L : Set (Set β)} : I ↾ sumCls L ∈ smsmbar L L := by
  have hI : (I : β → β → Prop) ∈ arrow one one :=
    mem_arrow_one_one.2 ⟨fun x y z ⟨h1, h2⟩ => (show x = z from h1).trans (show y = z from h2).symm,
      fun x y z ⟨h1, h2⟩ => (show x = y from h1).symm.trans (show x = z from h2)⟩
  refine ⟨⟨oneone_cres hI _, (codom_cres fun y _ => ⟨y, rfl⟩).symm⟩, ?_⟩
  show L = imgRel (I ↾ sumCls L) ʻʻ L
  rw [(pm111_12 (T := I) (le_refl (sumCls L))).1]
  ext B
  constructor
  · intro hB
    refine ⟨B, hB, ?_⟩
    ext x
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hxy⟩ => (show x = y from hxy) ▸ hy⟩
  · rintro ⟨B', hB', rfl⟩
    convert hB' using 1
    ext x
    exact ⟨fun ⟨y, hy, hxy⟩ => (show x = y from hxy) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

private theorem smsmbar_cnv_aux {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop}
    (h : T ∈ smsmbar K L) : T˘ ∈ smsmbar L K := by
  obtain ⟨⟨⟨hT, hK⟩, hL⟩, -⟩ := pm111_11.1 h
  obtain ⟨⟨-, hLc⟩, hKL⟩ := mem_smsmbar_iff.1 h
  refine mem_smsmbar_iff.2 ⟨⟨oneone_cnv.1 hT, hK⟩, ?_⟩
  have hinv : ∀ B, B ⊆ codom T → T˘ ʻʻ (T ʻʻ B) = B := by
    intro B hB
    obtain ⟨-, h2⟩ := mem_arrow_one_one.1 hT
    ext y
    constructor
    · rintro ⟨x, ⟨y', hy', hxy'⟩, hxy⟩
      rw [h2 x y y' ⟨hxy, hxy'⟩]; exact hy'
    · intro hy
      obtain ⟨x, hx⟩ := hB hy
      exact ⟨x, ⟨y, hy, hx⟩, hx⟩
  ext B
  constructor
  · intro hB
    exact ⟨T ʻʻ B, by rw [hKL]; exact ⟨B, hB, rfl⟩, (hinv B ((subset_sumCls hB).trans hLc.le)).symm⟩
  · rintro ⟨u, hu, rfl⟩
    rw [hKL] at hu
    obtain ⟨B, hB, rfl⟩ := hu
    rw [hinv B ((subset_sumCls hB).trans hLc.le)]; exact hB

/-- ✱111·131. \(\vdash :T\in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda . \equiv .\breve{T} \in \lambda \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \kappa\) -/
theorem pm111_131 {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop} :
    T ∈ smsmbar K L ↔ T˘ ∈ smsmbar L K := by
  exact ⟨smsmbar_cnv_aux, smsmbar_cnv_aux⟩

/-- ✱111·132. \(\vdash : S \in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda . T \in \lambda \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \mu .\supset . S \mid T \in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \mu\) -/
theorem pm111_132 {K : Set (Set α)} {L : Set (Set β)} {M : Set (Set γ)} {S : α → β → Prop}
    {T : β → γ → Prop} : S ∈ smsmbar K L ∧ T ∈ smsmbar L M → S ⨾ T ∈ smsmbar K M := by
  rintro ⟨hS, hT⟩
  have hTd : sumCls L = dom T := (mem_smbar_iff.1 (pm111_11.1 hT).1).1.2
  obtain ⟨⟨hS1, hSc⟩, hK⟩ := mem_smsmbar_iff.1 hS
  obtain ⟨⟨hT1, hTc⟩, hL⟩ := mem_smsmbar_iff.1 hT
  refine mem_smsmbar_iff.2 ⟨⟨oneone_relProd hS1 hT1, ?_⟩, ?_⟩
  · rw [hTc]
    ext z
    constructor
    · rintro ⟨y, hyz⟩
      have : y ∈ dom T := ⟨z, hyz⟩
      rw [← hTd, hSc] at this
      obtain ⟨x, hxy⟩ := this
      exact ⟨x, y, hxy, hyz⟩
    · rintro ⟨x, y, -, hyz⟩; exact ⟨y, hyz⟩
  · have himg : ∀ G : Set γ, (S ⨾ T) ʻʻ G = S ʻʻ (T ʻʻ G) := by
      intro G; ext x
      exact ⟨fun ⟨z, hz, y, hxy, hyz⟩ => ⟨y, ⟨z, hz, hyz⟩, hxy⟩,
        fun ⟨y, ⟨z, hz, hyz⟩, hxy⟩ => ⟨z, hz, y, hxy, hyz⟩⟩
    rw [hK, hL]
    ext u
    constructor
    · rintro ⟨_, ⟨G, hG, rfl⟩, rfl⟩; exact ⟨G, hG, (himg G).symm⟩
    · rintro ⟨G, hG, rfl⟩; exact ⟨T ʻʻ G, ⟨G, hG, rfl⟩, himg G⟩

/-- ✱111·14. \(\vdash : T \upharpoonright sʻ\lambda \in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda . \equiv . T \upharpoonright sʻ\lambda \in 1 \rightarrow 1 . sʻ\lambda \subset \text{ᗡ}ʻT . \kappa = T_{\in }ʻʻ\lambda\) -/
theorem pm111_14 {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop} :
    T ↾ sumCls L ∈ smsmbar K L ↔
      (T ↾ sumCls L ∈ arrow one one ∧ sumCls L ⊆ codom T) ∧ K = imgRel T ʻʻ L := by
  rw [pm111_1, (pm111_121 (T := T)).1.1]
  have : codom (T ↾ sumCls L) = sumCls L ↔ sumCls L ⊆ codom T :=
    ⟨fun h y hy => by rw [← h] at hy; obtain ⟨x, hx, -⟩ := hy; exact ⟨x, hx⟩, codom_cres⟩
  rw [this]

/-- ✱111·15. \(\vdash : T \upharpoonright sʻ\lambda \in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda . \equiv . T \upharpoonright sʻ\lambda \in (sʻ\kappa ) \,\overline{\text{ sm }}\, (sʻ\lambda ) . T_{\in } \upharpoonright \lambda \in \kappa \,\overline{\text{ sm }}\, \lambda\) -/
theorem pm111_15 {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop} :
    T ↾ sumCls L ∈ smsmbar K L ↔
      T ↾ sumCls L ∈ smbar (sumCls K) (sumCls L) ∧ imgRel T ↾ L ∈ smbar K L := by
  rw [pm111_11, (pm111_121 (T := T)).2]

/-- ✱111·16. \(\vdash : \exists ! \alpha \,\overline{\text{ sm }}\, \beta \cap \gamma \,\overline{\text{ sm }}\, \delta . \supset . \alpha = \gamma . \beta = \delta\) -/
theorem pm111_16 {A G : Set α} {B H : Set β} :
    (smbar A B ∩ smbar G H).Nonempty → A = G ∧ B = H := by
  rintro ⟨R, ⟨⟨-, h1⟩, h2⟩, ⟨⟨-, h3⟩, h4⟩⟩
  exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩

/-- ✱111·18. \(\vdash . \alpha \,\overline{\text{ sm }}\, \beta \subset (\alpha \uparrow \beta )_{\Delta }ʻ\beta\) -/
theorem pm111_18 {A : Set α} {B : Set β} : smbar A B ⊆ sel (cross A B) B := by
  rintro R ⟨⟨hR, hA⟩, hB⟩
  refine mem_sel_iff.2 ⟨⟨oneCls_of_oneone hR, fun x y h => ⟨?_, ?_⟩⟩, hB.symm⟩
  · rw [hA]; exact ⟨y, h⟩
  · rw [hB]; exact ⟨x, h⟩

/-- ✱111·2. \(\vdash :\text{E}!Sʻ\beta .\supset .\text{Crp}(S)ʻ\beta = (Sʻ\beta )\,\overline{\text{ sm }}\, \beta \quad[*14·28.(*111·02)]\)

`Crp(S)'β = (S'β) sm̄ β` contains two descriptions; the first, `Crp(S)'β`, has the larger scope. -/
theorem pm111_2 {S : Set α → Set β → Prop} {B : Set β} :
    EDesc S B → Desc (Crp S) B (fun U => Desc S B (fun A => U = smbar A B)) := by
  rintro ⟨A, hA⟩
  rw [desc_Crp, desc_of_unique hA, desc_of_unique hA]

/-- ✱111·201. \(\vdash :f\{\text{Crp}(S)ʻ\beta\}. \equiv .f\{(Sʻ\beta )\,\overline{\text{ sm }}\, \beta\} \quad[*4·2.(*111·02)]\) -/
theorem pm111_201 {S : Set α → Set β → Prop} {B : Set β} {f : Set (α → β → Prop) → Prop} :
    Desc (Crp S) B f ↔ Desc S B (fun A => f (smbar A B)) := desc_Crp S B f

/-- ✱111·202. \[\begin{aligned}\vdash :R\in \text{Crp}(S)ʻ\beta . \equiv .R\in 1\rightarrow 1.\text{D}ʻR = &Sʻ\beta .\text{ᗡ}ʻR = \beta \\ &[*111·201.*73·03]\end{aligned}\]

The description `S'β` has the smallest scope, `D'R = S'β`. -/
theorem pm111_202 {S : Set α → Set β → Prop} {B : Set β} {R : α → β → Prop} :
    Desc (Crp S) B (fun U => R ∈ U) ↔
      (R ∈ arrow one one ∧ Desc S B (fun A => dom R = A)) ∧ codom R = B := by
  rw [desc_Crp]
  by_cases hE : EDesc S B
  · obtain ⟨A, hA⟩ := hE
    rw [desc_of_unique hA, desc_of_unique hA, mem_smbar_iff, eq_comm (a := A), eq_comm (a := B)]
  · exact ⟨fun h => absurd (edesc_of_desc h) hE, fun h => absurd (edesc_of_desc h.1.2) hE⟩

/-- ✱111·21. \(\vdash :\exists !\text{Crp}(S)ʻ\beta . \equiv .Sʻ\beta \text{ sm }\beta \quad[*111·201.*73·04]\) -/
theorem pm111_21 {S : Set α → Set β → Prop} {B : Set β} :
    Desc (Crp S) B (fun U => U.Nonempty) ↔ Desc S B (fun A => sm A B) := desc_Crp S B _

/-- ✱111·211. \(\vdash :\exists !\text{Crp}(S)ʻ\beta .\supset .\text{E}!Sʻ\beta .\beta \in \text{ᗡ}ʻS \quad[*111·21.*14·21.*33·43]\) -/
theorem pm111_211 {S : Set α → Set β → Prop} {B : Set β} :
    Desc (Crp S) B (fun U => U.Nonempty) → EDesc S B ∧ B ∈ codom S := by
  intro h
  rw [desc_Crp] at h
  obtain ⟨A, hA, -⟩ := h
  exact ⟨⟨A, hA⟩, A, (hA A).2 rfl⟩

/-- ✱111·22. \(\vdash \colon\ldotp \beta \in \text{ᗡ}ʻS.\supset _{\beta }.\exists !\text{Crp}(S)ʻ\beta : \equiv .S\in 1\rightarrow \text{Cls}.S\,\unicode{x2abd}\, \text{ sm }\) -/
theorem pm111_22 {S : Set α → Set β → Prop} :
    (∀ B, B ∈ codom S → Desc (Crp S) B (fun U => U.Nonempty)) ↔ S ∈ arrow one Cls ∧ S ⪽ sm := by
  constructor
  · intro h
    refine ⟨mem_arrow_one_Cls.2 fun x y z ⟨hx, hy⟩ => ?_, fun A B hAB => ?_⟩
    · obtain ⟨b, hb, -⟩ := (desc_Crp _ _ _).1 (h z ⟨x, hx⟩)
      exact ((hb x).1 hx).trans ((hb y).1 hy).symm
    · obtain ⟨b, hb, hsm⟩ := (desc_Crp _ _ _).1 (h B ⟨A, hAB⟩)
      rw [(hb A).1 hAB]; exact hsm
  · rintro ⟨h1, h2⟩ B ⟨A, hAB⟩
    rw [desc_Crp, desc_of_unique (unique_of_oneCls h1 hAB)]
    exact h2 A B hAB

/-- ✱111·221. \(\vdash \colon\ldotp S\in 1\rightarrow \text{Cls}.S\,\unicode{x2abd}\, \text{ sm }.\supset :\exists !\text{Crp}(S)ʻ\beta . \equiv .\beta \in \text{ᗡ}ʻS\) -/
theorem pm111_221 {S : Set α → Set β → Prop} {B : Set β} :
    S ∈ arrow one Cls ∧ S ⪽ sm → (Desc (Crp S) B (fun U => U.Nonempty) ↔ B ∈ codom S) :=
  fun h => ⟨fun h' => (pm111_211 h').2, fun hB => pm111_22.2 h B hB⟩

/-- ✱111·23. \(\vdash :S\in 1\rightarrow 1.\beta \in \text{ᗡ}ʻS.\supset .\text{Crp}(S)ʻ\beta = \text{Cnv}ʻʻ\text{Crp}(\breve{S} )ʻSʻ\beta\)

`Crp(S)'β` (first description, larger scope) and `Crp(S̆)'S'β` (a double description, `S'β`
eliminated first, ✱30·02). `Cnv''` is the image under the relation `Cnv` (✱31·01). -/
theorem pm111_23 {S : Set α → Set β → Prop} {B : Set β} :
    S ∈ arrow one one ∧ B ∈ codom S →
      Desc (Crp S) B (fun U => Desc2 (Crp S˘) S B (fun V => U = Cnv ʻʻ V)) := by
  rintro ⟨hS, A, hAB⟩
  have hA := unique_of_oneCls (oneCls_of_oneone hS) hAB
  have hB : ∀ x, S˘ x A ↔ x = B := unique_of_oneCls (oneCls_of_oneone (oneone_cnv.1 hS)) hAB
  rw [desc_Crp, desc_of_unique hA, desc2_iff, desc_of_unique hA, desc_Crp, desc_of_unique hB]
  exact smbar_eq_Cnv_img A B

/-- ✱111·24. \(\vdash :S\in 1\rightarrow \text{Cls}.\lambda \subset \text{ᗡ}ʻS.\supset .\text{Crp}(S)ʻʻ\lambda \in \text{Cls}^{2} \text{excl}\) -/
theorem pm111_24 {S : Set α → Set β → Prop} {L : Set (Set β)} :
    S ∈ arrow one Cls ∧ L ⊆ codom S → Crp S ʻʻ L ∈ Cls2excl := by
  rintro ⟨hS, -⟩ U U' ⟨⟨⟨B, hB, A, hA, rfl⟩, ⟨B', hB', A', hA', rfl⟩⟩, hne⟩
  rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro P ⟨hP, hP'⟩
  apply hne
  have hBB : B = B' := hP.2.trans hP'.2.symm
  subst hBB
  rw [(hA A').1 ((hA' A').2 rfl)]

/-- ✱111·25. \[\begin{aligned}&\vdash :S\in 1\rightarrow \text{Cls}.S\,\unicode{x2abd}\, \text{ sm }.\lambda \subset \text{ᗡ}ʻS.\supset .\text{Crp}(S)ʻʻ\lambda \in \text{Cls ex}^{2}\,\text{excl}\\ &[*111·24·22]\end{aligned}\] -/
theorem pm111_25 {S : Set α → Set β → Prop} {L : Set (Set β)} :
    (S ∈ arrow one Cls ∧ S ⪽ sm) ∧ L ⊆ codom S → Crp S ʻʻ L ∈ ClsEx2excl := by
  rintro ⟨⟨hS, hsm⟩, hL⟩
  refine ⟨pm111_24 ⟨hS, hL⟩, ?_⟩
  rintro ⟨B, hB, A, hA, h⟩
  have hAB : S A B := (hA A).2 rfl
  obtain ⟨P, hP⟩ := hsm A B hAB
  rw [Null_eq_empty] at h
  rw [← h] at hP
  exact hP

/-- ✱111·3. \(\vdash : \lambda \in \text{Cls ex}^{2}\,\text{excl} . \supset . \dot{s} ʻʻ\text{D}ʻʻ {\in}_{\Delta} ʻ\alpha \,\overline{\text{ sm }}\, ʻʻ\lambda \subset (\alpha \uparrow sʻ\lambda )_{\Delta }ʻsʻ\lambda\)

`ṡ''D''∈_Δ'α sm̄''λ` is `graph sumRel ʻʻ (D ʻʻ sel memRel (opL smbar A ʻʻ L))`: `α sm̄` is the
relation of `α sm̄ β` to `β` (✱38·01), `ṡ` the relation of `ṡ'λ` to `λ`. -/
theorem pm111_3 {A : Set α} {L : Set (Set β)} :
    L ∈ ClsEx2excl →
      graph sumRel ʻʻ (D ʻʻ sel memRel (opL smbar A ʻʻ L)) ⊆ sel (cross A (sumCls L)) (sumCls L) := by
  rintro ⟨hL, -⟩ Q ⟨_, ⟨R, hR, rfl⟩, rfl⟩
  obtain ⟨⟨hR1, hR2⟩, hR3⟩ := mem_sel_iff.1 hR
  have hU : ∀ P U, R P U → ∃ B, (B ∈ L ∧ U = smbar A B) ∧ P ∈ U := by
    intro P U h
    have : U ∈ codom R := ⟨P, h⟩
    rw [hR3] at this
    obtain ⟨B, hB, rfl⟩ := this
    exact ⟨B, ⟨hB, rfl⟩, hR2 P _ h⟩
  refine mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨P, ⟨U, hPU⟩, hxz⟩, ⟨P', ⟨U', hPU'⟩, hyz⟩⟩
    obtain ⟨B, ⟨hB, rfl⟩, hP⟩ := hU P U hPU
    obtain ⟨B', ⟨hB', rfl⟩, hP'⟩ := hU P' U' hPU'
    have hz : z ∈ B := by rw [hP.2]; exact ⟨x, hxz⟩
    have hz' : z ∈ B' := by rw [hP'.2]; exact ⟨y, hyz⟩
    have hBB : B = B' := by
      by_contra hne
      have h0 := hL B B' ⟨⟨hB, hB'⟩, hne⟩
      have : z ∈ B ∩ B' := ⟨hz, hz'⟩
      rw [h0, Null_eq_empty] at this; exact this
    subst hBB
    have := mem_arrow_one_Cls.1 hR1 P P' _ ⟨hPU, hPU'⟩
    subst this
    exact (mem_arrow_one_one.1 hP.1.1).1 x y z ⟨hxz, hyz⟩
  · rintro x y ⟨P, ⟨U, hPU⟩, hxy⟩
    obtain ⟨B, ⟨hB, rfl⟩, hP⟩ := hU P U hPU
    refine ⟨by rw [hP.1.2]; exact ⟨y, hxy⟩, B, hB, by rw [hP.2]; exact ⟨x, hxy⟩⟩
  · ext y
    constructor
    · rintro ⟨x, P, ⟨U, hPU⟩, hxy⟩
      obtain ⟨B, ⟨hB, rfl⟩, hP⟩ := hU P U hPU
      exact ⟨B, hB, by rw [hP.2]; exact ⟨x, hxy⟩⟩
    · rintro ⟨B, hB, hy⟩
      have : smbar A B ∈ codom R := by rw [hR3]; exact ⟨B, hB, rfl⟩
      obtain ⟨P, hP⟩ := this
      have hPm : P ∈ smbar A B := hR2 P _ hP
      rw [hPm.2] at hy
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, P, ⟨_, hP⟩, hx⟩

/-- ✱111·31. \[\begin{aligned}\vdash : \lambda , Sʻʻ\lambda \in \text{Cls}^{2} \text{excl} . S \in 1 \rightarrow 1 . R \in {\in}_{\Delta}ʻ\text{Crp} &(S)ʻʻ\lambda . \supset .\\ &\dot{s} ʻ\text{D}ʻR \in (sʻSʻʻ\lambda ) \,\overline{\text{ sm }}\, (sʻ\lambda )\end{aligned}\]

`λ, S''λ ∈ Cls² excl` is a conjunction (the two classes are of different types).

**Status.** proved (corrected): as printed the proposition is false when `λ` has a member outside
`ᗡ'S` (PM's demonstration uses `β ∈ λ . ≡ . R'Crp(S)'β ∈ Crp(S)'β`, which needs `E!S'β`): with
`S = Λ̇` and `λ = ι'V`, `Crp(S)''λ = Λ`, `R = Λ̇ ∈ ∈_Δ'Λ` and `ṡ'D'R = Λ̇` is not a correlator of
`Λ` with `V` (`pm111_31_printed_false`). The hypothesis `λ ⊂ ᗡ'S` (present in ✱111·33, where the
proposition is used) is added. -/
theorem pm111_31 {S : Set α → Set β → Prop} {L : Set (Set β)}
    {R : (α → β → Prop) → Set (α → β → Prop) → Prop} :
    (((L ∈ Cls2excl ∧ S ʻʻ L ∈ Cls2excl) ∧ S ∈ arrow one one) ∧ R ∈ sel memRel (Crp S ʻʻ L)) ∧
        L ⊆ codom S →
      sumRel (dom R) ∈ smbar (sumCls (S ʻʻ L)) (sumCls L) := by
  rintro ⟨⟨⟨⟨hL, hSL⟩, hS⟩, hR⟩, hLS⟩
  obtain ⟨f1, f3, f2⟩ := crp_sel_facts hR
  refine (union_corr hL hSL hS f1 ?_ f3).1
  intro B hB
  obtain ⟨A, hAB⟩ := hLS hB
  obtain ⟨P, hP, hPR⟩ := f2 B A hB (unique_of_oneCls (oneCls_of_oneone hS) hAB)
  exact ⟨A, P, ⟨hAB, hP⟩, (mem_sel_iff.1 hR).1.2 P _ hPR⟩

/-- The printed form of ✱111·31 is false. -/
theorem pm111_31_printed_false : ¬ ∀ (S : Set Unit → Set Unit → Prop) (L : Set (Set Unit))
    (R : (Unit → Unit → Prop) → Set (Unit → Unit → Prop) → Prop),
    ((L ∈ Cls2excl ∧ S ʻʻ L ∈ Cls2excl) ∧ S ∈ arrow one one) ∧ R ∈ sel memRel (Crp S ʻʻ L) →
      sumRel (dom R) ∈ smbar (sumCls (S ʻʻ L)) (sumCls L) := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := crp_counter_facts
  have := h rNull {Set.univ} rNull ⟨⟨⟨h2, h3⟩, h1⟩, h4⟩
  rw [sumRel_dom_rNull] at this
  have hc : sumCls ({Set.univ} : Set (Set Unit)) = codom rNull := this.2
  have : () ∈ codom (rNull : Unit → Unit → Prop) := hc ▸ ⟨Set.univ, rfl, trivial⟩
  obtain ⟨x, hx⟩ := this
  exact rNull_apply _ _ hx

/-- ✱111·311. \[\begin{aligned}&\vdash : \lambda , Sʻʻ\lambda \in \text{Cls}^{2} \text{excl} . S \in 1 \rightarrow 1 . \exists ! {\in}_{\Delta}ʻ\text{Crp} (S)ʻʻ\lambda . \supset · sʻSʻʻ\lambda \text{ sm } sʻ\lambda\\ &[*111·31 . *73·04]\end{aligned}\]

**Status.** proved (corrected): as ✱111·31, the hypothesis `λ ⊂ ᗡ'S` is added; as printed it is
false (`pm111_311_printed_false`: `S = Λ̇`, `λ = ι'V`, and `s'S''λ = Λ` is not similar to `V`). -/
theorem pm111_311 {S : Set α → Set β → Prop} {L : Set (Set β)} :
    (((L ∈ Cls2excl ∧ S ʻʻ L ∈ Cls2excl) ∧ S ∈ arrow one one) ∧
        (sel memRel (Crp S ʻʻ L)).Nonempty) ∧ L ⊆ codom S →
      sm (sumCls (S ʻʻ L)) (sumCls L) := by
  rintro ⟨⟨h, R, hR⟩, hLS⟩
  exact ⟨_, pm111_31 ⟨⟨h, hR⟩, hLS⟩⟩

/-- The printed form of ✱111·311 is false. -/
theorem pm111_311_printed_false : ¬ ∀ (S : Set Unit → Set Unit → Prop) (L : Set (Set Unit)),
    ((L ∈ Cls2excl ∧ S ʻʻ L ∈ Cls2excl) ∧ S ∈ arrow one one) ∧
        (sel memRel (Crp S ʻʻ L)).Nonempty →
      sm (sumCls (S ʻʻ L)) (sumCls L) := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := crp_counter_facts
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (h rNull {Set.univ} ⟨⟨⟨h2, h3⟩, h1⟩, _, h4⟩)
  obtain ⟨A, ⟨_, -, hA⟩, -⟩ := (e.symm ⟨(), Set.univ, rfl, trivial⟩).2
  exact rNull_apply _ _ hA

/-- ✱111·313. \[\begin{aligned}\vdash : \lambda \in \text{Cls}^{2} \text{excl} . R \in &{\in}_{\Delta }ʻ\text{Crp} (S)ʻʻ\lambda . \beta \in \lambda . M = \dot{s} ʻ\text{D}ʻR . \supset .\\ &M \upharpoonright \beta = Rʻ\text{Crp} (S)ʻ\beta . M \upharpoonright \beta \in \text{Crp} (S)ʻ\beta\end{aligned}\]

`M ↾ β = R'Crp(S)'β` is the double description `Desc2 R (Crp S) B`, and `M ↾ β ∈ Crp(S)'β` has
the description `Crp(S)'β` with the smallest scope.

**Status.** proved (corrected): as printed it is false when `S'β` does not exist (then
`R'Crp(S)'β` does not exist): with `S = Λ̇`, `λ = ι'V`, `β = V`, `R = Λ̇`
(`pm111_313_printed_false`). The hypothesis `E!S'β` is added. -/
theorem pm111_313 {S : Set α → Set β → Prop} {L : Set (Set β)} {B : Set β}
    {R : (α → β → Prop) → Set (α → β → Prop) → Prop} {M : α → β → Prop} :
    (((L ∈ Cls2excl ∧ R ∈ sel memRel (Crp S ʻʻ L)) ∧ B ∈ L) ∧ M = sumRel (dom R)) ∧
        EDesc S B →
      Desc2 R (Crp S) B (fun P => M ↾ B = P) ∧ Desc (Crp S) B (fun U => M ↾ B ∈ U) := by
  rintro ⟨⟨⟨⟨hL, hR⟩, hB⟩, rfl⟩, A, hA⟩
  obtain ⟨f1, f3, f2⟩ := crp_sel_facts hR
  obtain ⟨⟨hR1, hR2⟩, hR3⟩ := mem_sel_iff.1 hR
  obtain ⟨P, hPd, hPR⟩ := f2 B A hB hA
  have hPm : P ∈ smbar A B := hR2 P _ hPR
  have hres : sumRel (dom R) ↾ B = P := by
    funext x y
    apply propext
    constructor
    · rintro ⟨⟨P', hP', hxy⟩, hy⟩
      obtain ⟨A', B', ⟨hB', -⟩, hP's⟩ := f1 P' hP'
      have hBB : B' = B := by
        by_contra hne
        have h0 := hL B' B ⟨⟨hB', hB⟩, hne⟩
        have : y ∈ B' ∩ B := ⟨by rw [hP's.2]; exact ⟨x, hxy⟩, hy⟩
        rw [h0, Null_eq_empty] at this; exact this
      have := f3 P' P hP' hPd (hP's.2.symm.trans (hBB.trans hPm.2))
      rw [this] at hxy; exact hxy
    · intro hxy
      exact ⟨⟨P, hPd, hxy⟩, by rw [hPm.2]; exact ⟨x, hxy⟩⟩
  have hU : ∀ x, R x (smbar A B) ↔ x = P := fun x =>
    ⟨fun h => mem_arrow_one_Cls.1 hR1 x P _ ⟨h, hPR⟩, fun e => e ▸ hPR⟩
  refine ⟨?_, ?_⟩
  · rw [desc2_iff, desc_Crp, desc_of_unique hA, desc_of_unique hU]; exact hres
  · rw [desc_Crp, desc_of_unique hA, hres]; exact hPm

/-- The printed form of ✱111·313 is false. -/
theorem pm111_313_printed_false : ¬ ∀ (S : Set Unit → Set Unit → Prop) (L : Set (Set Unit))
    (B : Set Unit) (R : (Unit → Unit → Prop) → Set (Unit → Unit → Prop) → Prop)
    (M : Unit → Unit → Prop),
    ((L ∈ Cls2excl ∧ R ∈ sel memRel (Crp S ʻʻ L)) ∧ B ∈ L) ∧ M = sumRel (dom R) →
      Desc2 R (Crp S) B (fun P => M ↾ B = P) ∧ Desc (Crp S) B (fun U => M ↾ B ∈ U) := by
  intro h
  obtain ⟨-, h2, -, h4⟩ := crp_counter_facts
  have := (h rNull {Set.univ} Set.univ rNull _ ⟨⟨⟨h2, h4⟩, rfl⟩, rfl⟩).2
  rw [desc_Crp] at this
  obtain ⟨A, hA, -⟩ := this
  exact rNull_apply _ _ ((hA A).2 rfl)

/-- ✱111·32. \[\begin{aligned}\vdash :\lambda ,Sʻʻ\lambda \in &\text{Cls}^{2} \text{excl}.S\in 1\rightarrow 1.R\in {\in}_{\Delta}ʻ\text{Crp}(S)ʻʻ\lambda .M = \dot{s} ʻ\text{D}ʻR.\supset .\\ &M\in 1\rightarrow 1.\text{ᗡ}ʻM = sʻ\lambda .Sʻʻ\lambda = M_{\in }ʻʻ\lambda .S\upharpoonright \lambda = M_{\in }\upharpoonright \lambda\end{aligned}\]

**Status.** proved (corrected): as ✱111·31, the hypothesis `λ ⊂ ᗡ'S` is added; as printed it is
false (`pm111_32_printed_false`: with `S = Λ̇`, `λ = ι'V`, `ᗡ'M = Λ ≠ s'λ`). -/
theorem pm111_32 {S : Set α → Set β → Prop} {L : Set (Set β)}
    {R : (α → β → Prop) → Set (α → β → Prop) → Prop} {M : α → β → Prop} :
    ((((L ∈ Cls2excl ∧ S ʻʻ L ∈ Cls2excl) ∧ S ∈ arrow one one) ∧ R ∈ sel memRel (Crp S ʻʻ L)) ∧
        M = sumRel (dom R)) ∧ L ⊆ codom S →
      ((M ∈ arrow one one ∧ codom M = sumCls L) ∧ S ʻʻ L = imgRel M ʻʻ L) ∧
        S ↾ L = imgRel M ↾ L := by
  rintro ⟨⟨⟨⟨⟨hL, hSL⟩, hS⟩, hR⟩, rfl⟩, hLS⟩
  obtain ⟨f1, f3, f2⟩ := crp_sel_facts hR
  have hR2 := (mem_sel_iff.1 hR).1.2
  have h2 : ∀ B, B ∈ L → ∃ A P, (S A B ∧ P ∈ dom R) ∧ P ∈ smbar A B := by
    intro B hB
    obtain ⟨A, hAB⟩ := hLS hB
    obtain ⟨P, hP, hPR⟩ := f2 B A hB (unique_of_oneCls (oneCls_of_oneone hS) hAB)
    exact ⟨A, P, ⟨hAB, hP⟩, hR2 P _ hPR⟩
  obtain ⟨hM, hres⟩ := union_corr hL hSL hS f1 h2 f3
  -- `M''β = S'β`
  have himg : ∀ B A, B ∈ L → S A B → sumRel (dom R) ʻʻ B = A := by
    intro B A hB hAB
    obtain ⟨A', P, ⟨hA'B, hP⟩, hPs⟩ := h2 B hB
    have : A = A' := (mem_arrow_one_one.1 hS).1 A A' B ⟨hAB, hA'B⟩
    subst this
    have e := hres P hP
    rw [← hPs.2] at e
    rw [← dom_cres, e, hPs.1.2]
  refine ⟨⟨⟨hM.1.1, hM.2.symm⟩, ?_⟩, ?_⟩
  · ext A
    constructor
    · rintro ⟨B, hB, hAB⟩; exact ⟨B, hB, (himg B A hB hAB).symm⟩
    · rintro ⟨B, hB, rfl⟩
      obtain ⟨A, hAB⟩ := hLS hB
      exact ⟨B, hB, by rw [himg B A hB hAB]; exact hAB⟩
  · funext A B
    apply propext
    constructor
    · rintro ⟨hAB, hB⟩; exact ⟨(himg B A hB hAB).symm, hB⟩
    · rintro ⟨hA, hB⟩
      obtain ⟨A', hAB⟩ := hLS hB
      rw [show A = _ from hA, himg B A' hB hAB]; exact ⟨hAB, hB⟩

/-- The printed form of ✱111·32 is false. -/
theorem pm111_32_printed_false : ¬ ∀ (S : Set Unit → Set Unit → Prop) (L : Set (Set Unit))
    (R : (Unit → Unit → Prop) → Set (Unit → Unit → Prop) → Prop) (M : Unit → Unit → Prop),
    (((L ∈ Cls2excl ∧ S ʻʻ L ∈ Cls2excl) ∧ S ∈ arrow one one) ∧ R ∈ sel memRel (Crp S ʻʻ L)) ∧
        M = sumRel (dom R) →
      ((M ∈ arrow one one ∧ codom M = sumCls L) ∧ S ʻʻ L = imgRel M ʻʻ L) ∧
        S ↾ L = imgRel M ↾ L := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := crp_counter_facts
  have := (h rNull {Set.univ} rNull _ ⟨⟨⟨⟨h2, h3⟩, h1⟩, h4⟩, rfl⟩).1.1.2
  rw [sumRel_dom_rNull] at this
  have : () ∈ codom (rNull : Unit → Unit → Prop) := this ▸ ⟨Set.univ, rfl, trivial⟩
  obtain ⟨x, hx⟩ := this
  exact rNull_apply _ _ hx

/-- ✱111·321. \[\begin{aligned}\vdash :\lambda ,&Sʻʻ\lambda \in \text{Cls}^{2} \text{excl}.S\in 1\rightarrow 1.\exists !{\in}_{\Delta}ʻ\text{Crp}(S)ʻʻ\lambda .\supset .\\ &(\exists M).M\in 1\rightarrow 1.\text{ᗡ}ʻM = sʻ\lambda .Sʻʻ\lambda = M_{\in }ʻʻ\lambda .S\upharpoonright \lambda = M_{\in }\upharpoonright \lambda\\ &[*111·32]\end{aligned}\]

**Status.** proved (corrected): as ✱111·32, the hypothesis `λ ⊂ ᗡ'S` is added; as printed it is
false (`pm111_321_printed_false`). -/
theorem pm111_321 {S : Set α → Set β → Prop} {L : Set (Set β)} :
    (((L ∈ Cls2excl ∧ S ʻʻ L ∈ Cls2excl) ∧ S ∈ arrow one one) ∧
        (sel memRel (Crp S ʻʻ L)).Nonempty) ∧ L ⊆ codom S →
      ∃ M : α → β → Prop, ((M ∈ arrow one one ∧ codom M = sumCls L) ∧ S ʻʻ L = imgRel M ʻʻ L) ∧
        S ↾ L = imgRel M ↾ L := by
  rintro ⟨⟨h, R, hR⟩, hLS⟩
  exact ⟨_, pm111_32 ⟨⟨⟨h, hR⟩, rfl⟩, hLS⟩⟩

/-- The printed form of ✱111·321 is false. -/
theorem pm111_321_printed_false : ¬ ∀ (S : Set Unit → Set Unit → Prop) (L : Set (Set Unit)),
    ((L ∈ Cls2excl ∧ S ʻʻ L ∈ Cls2excl) ∧ S ∈ arrow one one) ∧
        (sel memRel (Crp S ʻʻ L)).Nonempty →
      ∃ M : Unit → Unit → Prop, ((M ∈ arrow one one ∧ codom M = sumCls L) ∧
        S ʻʻ L = imgRel M ʻʻ L) ∧ S ↾ L = imgRel M ↾ L := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := crp_counter_facts
  obtain ⟨M, ⟨⟨-, hM⟩, hSL⟩, -⟩ := h rNull {Set.univ} ⟨⟨⟨h2, h3⟩, h1⟩, _, h4⟩
  have h0 : (rNull ʻʻ ({Set.univ} : Set (Set Unit)) : Set (Set Unit)) = ∅ := by
    ext A; exact ⟨fun ⟨_, _, h⟩ => absurd h (rNull_apply _ _), fun h => h.elim⟩
  have : M ʻʻ Set.univ ∈ imgRel M ʻʻ ({Set.univ} : Set (Set Unit)) := ⟨Set.univ, rfl, rfl⟩
  rw [← hSL, h0] at this
  exact this

/-- ✱111·322. \[\begin{aligned}\vdash :\kappa ,\lambda \in \text{Cls}^{2} \text{excl}.&S\in \kappa \,\overline{\text{ sm }}\, \lambda .R\in {\in}_{\Delta}ʻ\text{Crp}(S)ʻʻ\lambda .M = \dot{s} ʻ\text{D}ʻR.\supset .\\ &M\in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda .S = M_{\in }\upharpoonright \lambda \quad[*111·32·1.*35·66.*73·03]\end{aligned}\] -/
theorem pm111_322 {K : Set (Set α)} {L : Set (Set β)} {S : Set α → Set β → Prop}
    {R : (α → β → Prop) → Set (α → β → Prop) → Prop} {M : α → β → Prop} :
    (((K ∈ Cls2excl ∧ L ∈ Cls2excl) ∧ S ∈ smbar K L) ∧ R ∈ sel memRel (Crp S ʻʻ L)) ∧
        M = sumRel (dom R) →
      M ∈ smsmbar K L ∧ S = imgRel M ↾ L := by
  rintro ⟨⟨⟨⟨hK, hL⟩, ⟨⟨hS, hKd⟩, hLc⟩⟩, hR⟩, hM⟩
  have hSL : S ʻʻ L = K := by rw [hLc, img_codom, hKd]
  have hLS : L ⊆ codom S := hLc.le
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := pm111_32 ⟨⟨⟨⟨⟨hL, hSL ▸ hK⟩, hS⟩, hR⟩, hM⟩, hLS⟩
  refine ⟨⟨⟨h1, h2.symm⟩, hSL.symm.trans h3⟩, ?_⟩
  rw [← h4]
  funext A B
  apply propext
  exact ⟨fun h => ⟨h, hLc ▸ ⟨A, h⟩⟩, fun h => h.1⟩

/-- ✱111·33. \[\begin{aligned}\vdash \colon\ldotp \text{Mult ax}.\supset :S\in 1\rightarrow 1.S\,\unicode{x2abd}\, \text{ sm }.&\kappa ,\lambda \in \text{Cls}^{2} \text{excl}.\kappa =Sʻʻ\lambda .\lambda \subset \text{ᗡ}ʻS.\supset .\\ &sʻ\kappa \text{ sm }sʻ\lambda\end{aligned}\]

`Mult ax` is at the type of the members of the classes `Crp(S)'β` (relations between `α`- and
`β`-things), whose selection it provides (✱88·37). -/
theorem pm111_33 {K : Set (Set α)} {L : Set (Set β)} {S : Set α → Set β → Prop} :
    MultAx (α → β → Prop) →
      (((S ∈ arrow one one ∧ S ⪽ sm) ∧ (K ∈ Cls2excl ∧ L ∈ Cls2excl)) ∧ K = S ʻʻ L) ∧
          L ⊆ codom S →
        sm (sumCls K) (sumCls L) := by
  rintro - ⟨⟨⟨⟨hS, hsm⟩, ⟨hK, hL⟩⟩, rfl⟩, hLS⟩
  have hex := (pm111_25 ⟨⟨oneCls_of_oneone hS, hsm⟩, hLS⟩).2
  refine pm111_311 ⟨⟨⟨⟨hL, hK⟩, hS⟩, sel_memRel_nonempty fun U hU => ?_⟩, hLS⟩
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  exact hex (by rw [Null_eq_empty]; exact hU)

/-- ✱111·34. \[\begin{aligned}\vdash \colon\ldotp &\text{Mult ax}.\supset :\\ &(\exists S).S\in 1\rightarrow 1.S\,\unicode{x2abd}\, \text{ sm }.\text{D}ʻS=\kappa .\text{ᗡ}ʻS = \lambda .\kappa ,\lambda \in \text{Cls}^{2} \text{excl}.\supset .\\ &(\exists M).M\in 1\rightarrow 1.\text{ᗡ}ʻM = sʻ\lambda .\kappa = M_{\in }ʻʻ\lambda\end{aligned}\]

The prefix `(∃S)` extends to `κ, λ ∈ Cls² excl` (Group II dots), and stops at `⊃`. -/
theorem pm111_34 {K : Set (Set α)} {L : Set (Set β)} :
    MultAx (α → β → Prop) →
      (∃ S : Set α → Set β → Prop, ((((S ∈ arrow one one ∧ S ⪽ sm) ∧ dom S = K) ∧
          codom S = L) ∧ (K ∈ Cls2excl ∧ L ∈ Cls2excl))) →
        ∃ M : α → β → Prop, (M ∈ arrow one one ∧ codom M = sumCls L) ∧ K = imgRel M ʻʻ L := by
  rintro - ⟨S, ⟨⟨⟨hS, hsm⟩, hKd⟩, hLc⟩, ⟨hK, hL⟩⟩
  have hLS : L ⊆ codom S := hLc.ge
  have hSL : S ʻʻ L = K := by rw [← hLc, img_codom, hKd]
  have hex := (pm111_25 ⟨⟨oneCls_of_oneone hS, hsm⟩, hLS⟩).2
  have hne : (sel memRel (Crp S ʻʻ L)).Nonempty := sel_memRel_nonempty fun U hU => by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hex (by rw [Null_eq_empty]; exact hU)
  obtain ⟨M, ⟨⟨h1, h2⟩, h3⟩, -⟩ := pm111_321 ⟨⟨⟨⟨hL, hSL ▸ hK⟩, hS⟩, hne⟩, hLS⟩
  exact ⟨M, ⟨h1, h2⟩, hSL.symm.trans h3⟩

/-- ✱111·4. \[\begin{aligned}&\vdash :\kappa \text{ sm } \text{ sm }\lambda . \equiv .(\exists T).T\in 1\rightarrow 1.\text{ᗡ}ʻT = sʻ\lambda .\kappa = T_{\in }ʻʻ\lambda . \equiv .\exists !\kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda \\ &[*111·1.(*111·03)]\end{aligned}\]

A chain of two equivalences, the conjunction of its links. -/
theorem pm111_4 {K : Set (Set α)} {L : Set (Set β)} :
    (smsm K L ↔ ∃ T : α → β → Prop,
        (T ∈ arrow one one ∧ codom T = sumCls L) ∧ K = imgRel T ʻʻ L) ∧
      ((∃ T : α → β → Prop, (T ∈ arrow one one ∧ codom T = sumCls L) ∧ K = imgRel T ʻʻ L) ↔
        (smsmbar K L).Nonempty) := by
  have : (smsmbar K L).Nonempty ↔ ∃ T : α → β → Prop,
      (T ∈ arrow one one ∧ codom T = sumCls L) ∧ K = imgRel T ʻʻ L :=
    ⟨fun ⟨T, hT⟩ => ⟨T, pm111_1.1 hT⟩, fun ⟨T, hT⟩ => ⟨T, pm111_1.2 hT⟩⟩
  exact ⟨this, this.symm⟩

/-- ✱111·401. \(\vdash :\kappa \text{ sm } \text{ sm } \lambda . \equiv .(\exists T).T\in 1\rightarrow 1.sʻ\lambda \subset \text{ᗡ}ʻT.\kappa = T_{\in }ʻʻ\lambda\) -/
theorem pm111_401 {K : Set (Set α)} {L : Set (Set β)} :
    smsm K L ↔ ∃ T : α → β → Prop,
      (T ∈ arrow one one ∧ sumCls L ⊆ codom T) ∧ K = imgRel T ʻʻ L := by
  constructor
  · rintro ⟨T, ⟨hT, hL⟩, hK⟩; exact ⟨T, ⟨hT, hL.le⟩, hK⟩
  · rintro ⟨T, ⟨hT, hL⟩, hK⟩
    exact ⟨T ↾ sumCls L, pm111_14.2 ⟨⟨oneone_cres hT _, hL⟩, hK⟩⟩

/-- ✱111·402. \[\begin{aligned}&\vdash :\kappa \text{ sm } \text{ sm } \lambda . \equiv .(\exists T).T\upharpoonright sʻ\lambda \in 1\rightarrow 1.sʻ\lambda \subset \text{ᗡ}ʻT.\kappa = T_{\in }ʻʻ\lambda\\ &[*111·14·1·121]\end{aligned}\] -/
theorem pm111_402 {K : Set (Set α)} {L : Set (Set β)} :
    smsm K L ↔ ∃ T : α → β → Prop,
      (T ↾ sumCls L ∈ arrow one one ∧ sumCls L ⊆ codom T) ∧ K = imgRel T ʻʻ L := by
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨⟨hT1, hL⟩, hK⟩ := hT
    exact ⟨T, ⟨oneone_cres hT1 _, hL.le⟩, hK⟩
  · rintro ⟨T, h⟩; exact ⟨T ↾ sumCls L, pm111_14.2 h⟩

/-- ✱111·43. \[\begin{aligned}&\vdash :\kappa \text{ sm } \text{ sm } \lambda .\supset .(\exists S).S\in 1\rightarrow 1.S\,\unicode{x2abd}\, \text{ sm }.\text{D}ʻS = \kappa .\text{ᗡ}ʻS = \lambda \\ &[*111·11·111]\end{aligned}\] -/
theorem pm111_43 {K : Set (Set α)} {L : Set (Set β)} :
    smsm K L → ∃ S : Set α → Set β → Prop,
      (((S ∈ arrow one one ∧ S ⪽ sm) ∧ dom S = K) ∧ codom S = L) := by
  rintro ⟨T, hT⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := pm111_112 hT
  exact ⟨imgRel T ↾ L, ⟨⟨⟨h1, h4⟩, h2.symm⟩, h3.symm⟩⟩

/-- ✱111·44. \(\vdash :\kappa \text{ sm } \text{ sm } \lambda .\supset .\kappa \text{ sm } \lambda .sʻ\kappa \text{ sm } sʻ\lambda \quad[*111·11·4.*73·03]\) -/
theorem pm111_44 {K : Set (Set α)} {L : Set (Set β)} :
    smsm K L → sm K L ∧ sm (sumCls K) (sumCls L) := by
  rintro ⟨T, hT⟩
  obtain ⟨h1, h2⟩ := pm111_11.1 hT
  exact ⟨⟨_, h2⟩, ⟨_, h1⟩⟩

/-- ✱111·45. \(\vdash .\lambda \text{ sm } \text{ sm } \lambda \quad[*111·13·4]\) -/
theorem pm111_45 {L : Set (Set β)} : smsm L L := ⟨_, pm111_13⟩

/-- ✱111·451. \(\vdash :\kappa \text{ sm } \text{ sm } \lambda . \equiv .\lambda \text{ sm } \text{ sm } \kappa \quad[*111·131·4]\) -/
theorem pm111_451 {K : Set (Set α)} {L : Set (Set β)} : smsm K L ↔ smsm L K :=
  ⟨fun ⟨T, h⟩ => ⟨T˘, pm111_131.1 h⟩, fun ⟨T, h⟩ => ⟨T˘, pm111_131.1 h⟩⟩

/-- ✱111·452. \(\vdash :\kappa \text{ sm } \text{ sm } \lambda .\lambda \text{ sm } \text{ sm } \mu .\supset .\kappa \text{ sm } \text{ sm } \mu \quad[*111·132·4]\) -/
theorem pm111_452 {K : Set (Set α)} {L : Set (Set β)} {M : Set (Set γ)} :
    smsm K L ∧ smsm L M → smsm K M :=
  fun ⟨⟨S, hS⟩, ⟨T, hT⟩⟩ => ⟨S ⨾ T, pm111_132 ⟨hS, hT⟩⟩

/-- ✱111·46. \[\begin{aligned}&\vdash :\lambda ,Sʻʻ\lambda \in \text{Cls}^{2} \text{excl}.S\in 1\rightarrow 1.\exists !{\in}_{\Delta}ʻ\text{Crp}(S)ʻʻ\lambda .\supset .Sʻʻ\lambda \text{ sm } \text{ sm } \lambda \\ &[*111·32·4]\end{aligned}\]

**Status.** proved (corrected): as ✱111·32, the hypothesis `λ ⊂ ᗡ'S` is added; as printed it is
false (`pm111_46_printed_false`: `S = Λ̇`, `λ = ι'V`, and `Λ sm sm ι'V` fails). -/
theorem pm111_46 {S : Set α → Set β → Prop} {L : Set (Set β)} :
    (((L ∈ Cls2excl ∧ S ʻʻ L ∈ Cls2excl) ∧ S ∈ arrow one one) ∧
        (sel memRel (Crp S ʻʻ L)).Nonempty) ∧ L ⊆ codom S →
      smsm (S ʻʻ L) L := by
  intro h
  obtain ⟨M, ⟨⟨h1, h2⟩, h3⟩, -⟩ := pm111_321 h
  exact ⟨M, pm111_1.2 ⟨⟨h1, h2⟩, h3⟩⟩

/-- The printed form of ✱111·46 is false. -/
theorem pm111_46_printed_false : ¬ ∀ (S : Set Unit → Set Unit → Prop) (L : Set (Set Unit)),
    ((L ∈ Cls2excl ∧ S ʻʻ L ∈ Cls2excl) ∧ S ∈ arrow one one) ∧
        (sel memRel (Crp S ʻʻ L)).Nonempty →
      smsm (S ʻʻ L) L := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := crp_counter_facts
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (pm111_44 (h rNull {Set.univ} ⟨⟨⟨h2, h3⟩, h1⟩, _, h4⟩)).1
  obtain ⟨_, -, hA⟩ := (e.symm ⟨Set.univ, rfl⟩).2
  exact rNull_apply _ _ hA

private theorem smsm_excl_aux {K : Set (Set α)} {L : Set (Set β)} (h : smsm K L)
    (hL : L ∈ Cls2excl) : K ∈ Cls2excl := by
  obtain ⟨T, hT'⟩ := h
  obtain ⟨⟨hT, -⟩, hK⟩ := mem_smsmbar_iff.1 hT'
  rw [hK]
  rintro _ _ ⟨⟨⟨B, hB, rfl⟩, ⟨B', hB', rfl⟩⟩, hne⟩
  have hBB : B ≠ B' := fun h => hne (h ▸ rfl)
  have h0 := hL B B' ⟨⟨hB, hB'⟩, hBB⟩
  rw [Null_eq_empty] at h0 ⊢
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨y, hy, hxy⟩, ⟨y', hy', hxy'⟩⟩
  have := (mem_arrow_one_one.1 hT).2 x y y' ⟨hxy, hxy'⟩
  subst this
  have : y ∈ B ∩ B' := ⟨hy, hy'⟩
  rw [h0] at this; exact this

/-- ✱111·47. \(\vdash \colon\ldotp \kappa \text{ sm } \text{ sm } \lambda .\supset :\kappa \in \text{Cls}^{2} \text{excl}. \equiv .\lambda \in \text{Cls}^{2} \text{excl}\) -/
theorem pm111_47 {K : Set (Set α)} {L : Set (Set β)} :
    smsm K L → (K ∈ Cls2excl ↔ L ∈ Cls2excl) := by
  exact fun h => ⟨fun hK => smsm_excl_aux (pm111_451.1 h) hK, smsm_excl_aux h⟩

/-- ✱111·5. \[\begin{aligned}&\vdash \colon\colon \text{Mult ax}.\supset \colon\ldotp \kappa ,\lambda \in \text{Cls}^{2} \text{excl}.\supset :\\ &\kappa \text{ sm } \text{ sm } \lambda . \equiv .(\exists S).S\in 1\rightarrow 1.S\,\unicode{x2abd}\, \text{ sm }.\text{D}ʻS = \kappa .\text{ᗡ}ʻS = \lambda .\\ &\equiv .\exists !\kappa \,\overline{\text{ sm }}\, \lambda \cap \text{ᗡ}ʻʻʻ\text{ sm } \quad[*111·34·43·4]\end{aligned}\]

The prefix `(∃S)` extends to the second `≡` (Group II dots); the chain is the conjunction of its
links. `Mult ax` is at the type of the relations `M` it yields (✱111·34).

**Status.** proved (reading): transcription error: the e-text prints `ᗡ'''sm` for `Rl'sm`, as the
Summary of ✱111 shows (`∃!κ sm̄ λ ∩ Rl'sm`). -/
theorem pm111_5 {K : Set (Set α)} {L : Set (Set β)} :
    MultAx (α → β → Prop) → (K ∈ Cls2excl ∧ L ∈ Cls2excl) →
      (smsm K L ↔ ∃ S : Set α → Set β → Prop,
          ((S ∈ arrow one one ∧ S ⪽ sm) ∧ dom S = K) ∧ codom S = L) ∧
        ((∃ S : Set α → Set β → Prop, ((S ∈ arrow one one ∧ S ⪽ sm) ∧ dom S = K) ∧ codom S = L) ↔
          (smbar K L ∩ rl sm).Nonempty) := by
  intro hM hKL
  refine ⟨⟨pm111_43, fun ⟨S, hS⟩ => ?_⟩, ?_⟩
  · obtain ⟨M, h1, h2⟩ := pm111_34 hM ⟨S, hS, hKL⟩
    exact ⟨M, pm111_1.2 ⟨h1, h2⟩⟩
  · constructor
    · rintro ⟨S, ⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨S, ⟨⟨h1, h3.symm⟩, h4.symm⟩, h2⟩
    · rintro ⟨S, ⟨⟨h1, h3⟩, h4⟩, h2⟩; exact ⟨S, ⟨⟨h1, h2⟩, h3.symm⟩, h4.symm⟩

/-- ✱111·51. \[\begin{aligned}&\vdash \colon\ldotp \text{Mult ax}.\supset :\kappa ,\lambda \in \text{Cls}^{2} \text{excl}.\exists !\kappa \,\overline{\text{ sm }}\, \lambda \cap \text{ᗡ}ʻʻʻ\text{ sm }.\supset .sʻ\kappa \text{ sm }sʻ\lambda \\ &[*111·5·44]\end{aligned}\]

**Status.** proved (reading): transcription error: `ᗡ'''sm` is read `Rl'sm` (as ✱111·5). -/
theorem pm111_51 {K : Set (Set α)} {L : Set (Set β)} :
    MultAx (α → β → Prop) →
      (K ∈ Cls2excl ∧ L ∈ Cls2excl) ∧ (smbar K L ∩ rl sm).Nonempty → sm (sumCls K) (sumCls L) := by
  rintro hM ⟨hKL, h⟩
  have := pm111_5 hM hKL
  exact (pm111_44 (this.1.2 (this.2.2 h))).2

/-- ✱111·52. \(\vdash :\mu ,\nu \in \text{NC}.\kappa ,\lambda \in \mu \cap \text{Cl}ʻ\nu .\supset .\exists !\kappa \,\overline{\text{ sm }}\, \lambda \cap \text{Rl}ʻ\text{ sm }\)

`μ, ν ∈ NC` is `μ ∈ NC β₁ ∧ ν ∈ NC β₂`; `κ, λ ∈ μ ∩ Cl'ν` puts `κ` and `λ` in one type. -/
theorem pm111_52 {β₁ β₂ : Type*} {μ : Set (Set (Set α))} {ν : Set (Set α)}
    {K L : Set (Set α)} :
    (μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ (K ∈ μ ∩ cl ν ∧ L ∈ μ ∩ cl ν) → (smbar K L ∩ rl sm).Nonempty := by
  rintro ⟨⟨⟨A₁, rfl⟩, ⟨A₂, rfl⟩⟩, ⟨⟨hK, hKν⟩, ⟨hL, hLν⟩⟩⟩
  obtain ⟨S, hS⟩ := sm_trans hK (sm_symm hL)
  refine ⟨S, hS, fun A B hAB => ?_⟩
  have hA : A ∈ K := by rw [hS.1.2]; exact ⟨B, hAB⟩
  have hB : B ∈ L := by rw [hS.2]; exact ⟨A, hAB⟩
  exact sm_trans (hKν hA) (sm_symm (hLν hB))

/-- ✱111·53. \[\begin{aligned}&\vdash \colon\ldotp \text{Mult ax}.\supset :\mu ,\nu \in \text{NC}.\kappa ,\lambda \in \mu \cap \text{Cl excl}ʻ\nu .\supset .\kappa \text{ sm } \text{ sm } \lambda\\ &[*111·52·5]\end{aligned}\] -/
theorem pm111_53 {β₁ β₂ : Type*} {μ : Set (Set (Set α))} {ν : Set (Set α)}
    {K L : Set (Set α)} :
    MultAx (α → α → Prop) →
      (μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ (K ∈ μ ∩ clExcl ν ∧ L ∈ μ ∩ clExcl ν) → smsm K L := by
  rintro hM ⟨hμν, ⟨⟨hK, hKe, hKν⟩, ⟨hL, hLe, hLν⟩⟩⟩
  have h := pm111_52 ⟨hμν, ⟨⟨hK, hKν⟩, ⟨hL, hLν⟩⟩⟩
  have := pm111_5 hM ⟨hKe, hLe⟩
  exact this.1.2 (this.2.2 h)

section Helpers112

private theorem mem_downCls {A : Set α} {R : α → Set α → Prop} :
    R ∈ memRel ↧ A ↔ ∃ x, x ∈ A ∧ R = x ↓ A := Iff.rfl

private theorem mem_downImg {K : Set (Set α)} {u : Set (α → Set α → Prop)} :
    u ∈ opL downCls memRel ʻʻ K ↔ ∃ A, A ∈ K ∧ u = memRel ↧ A := Iff.rfl

private theorem mem_clsSigma {K : Set (Set α)} {R : α → Set α → Prop} :
    R ∈ clsSigma K ↔ ∃ A x, (A ∈ K ∧ x ∈ A) ∧ R = x ↓ A := by
  constructor
  · rintro ⟨_, ⟨A, hA, rfl⟩, x, hx, h⟩; exact ⟨A, x, ⟨hA, hx⟩, h⟩
  · rintro ⟨A, x, ⟨hA, hx⟩, h⟩; exact ⟨memRel ↧ A, ⟨A, hA, rfl⟩, x, hx, h⟩

private theorem couple_mem_clsSigma {K : Set (Set α)} {x : α} {A : Set α} :
    x ↓ A ∈ clsSigma K ↔ A ∈ K ∧ x ∈ A := by
  rw [mem_clsSigma]
  constructor
  · rintro ⟨A', x', ⟨hA, hx⟩, h⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 h
    exact ⟨hA, hx⟩
  · rintro ⟨hA, hx⟩; exact ⟨A, x, ⟨hA, hx⟩, rfl⟩

private theorem downCls_sm (A : Set α) : sm (memRel ↧ A) A :=
  sm_of_injOn (fun x => x ↓ A) (fun x y _ _ h => (couple_eq_couple_iff.1 h).1)
    fun _ => Iff.rfl

private theorem downCls_disjoint {A B : Set α} (h : A ≠ B) : memRel ↧ A ∩ memRel ↧ B = Λ := by
  rw [inter_eq_null_iff, Set.disjoint_left]
  rintro _ ⟨x, -, rfl⟩ ⟨y, -, e⟩
  exact h (couple_eq_couple_iff.1 e).2

private theorem downCls_inj {A B : Set α} (h : memRel ↧ A = memRel ↧ B) : A = B := by
  by_contra hne
  have h0 := downCls_disjoint hne
  rw [h, Set.inter_self, Null_eq_empty] at h0
  have hA : A = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have : x ↓ A ∈ memRel ↧ A := ⟨x, hx, rfl⟩
    rw [h, h0] at this; exact this
  have hB : B = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have : x ↓ B ∈ memRel ↧ B := ⟨x, hx, rfl⟩
    rw [h0] at this; exact this
  exact hne (hA.trans hB.symm)

private theorem clsSigma_eq_sumCls (K : Set (Set α)) :
    clsSigma K = sumCls (opL downCls memRel ʻʻ K) := rfl

private theorem clsSigma_union (K L : Set (Set α)) : clsSigma (K ∪ L) = clsSigma K ∪ clsSigma L := by
  ext R
  simp only [Set.mem_union, mem_clsSigma]
  constructor
  · rintro ⟨A, x, ⟨hA | hA, hx⟩, h⟩
    · exact Or.inl ⟨A, x, ⟨hA, hx⟩, h⟩
    · exact Or.inr ⟨A, x, ⟨hA, hx⟩, h⟩
  · rintro (⟨A, x, ⟨hA, hx⟩, h⟩ | ⟨A, x, ⟨hA, hx⟩, h⟩)
    · exact ⟨A, x, ⟨Or.inl hA, hx⟩, h⟩
    · exact ⟨A, x, ⟨Or.inr hA, hx⟩, h⟩

private theorem clsSigma_unitCls (A : Set α) : clsSigma (ι A) = memRel ↧ A := by
  ext R
  rw [mem_clsSigma]
  constructor
  · rintro ⟨A', x, ⟨rfl, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨A, x, ⟨rfl, hx⟩, rfl⟩

private theorem clsSigma_disjoint {K L : Set (Set α)} (h : K ∩ L = Λ) :
    clsSigma K ∩ clsSigma L = Λ := by
  rw [inter_eq_null_iff, Set.disjoint_left]
  intro R hK hL
  obtain ⟨A, x, ⟨hA, hx⟩, rfl⟩ := mem_clsSigma.1 hK
  have := (couple_mem_clsSigma.1 hL).1
  have h2 : A ∈ K ∩ L := ⟨hA, this⟩
  rw [h, Null_eq_empty] at h2; exact h2

/-- The double correlator of `∈↧''κ` with `κ` for exclusive `κ` (✱112·14). -/
private theorem downImg_smsm {K : Set (Set α)} (hK : K ∈ Cls2excl) :
    smsm (opL downCls memRel ʻʻ K) K := by
  have hex : ∀ A B x, A ∈ K → B ∈ K → x ∈ A → x ∈ B → A = B := by
    intro A B x hA hB hx hx'
    by_contra hne
    have h0 := hK A B ⟨⟨hA, hB⟩, hne⟩
    have : x ∈ A ∩ B := ⟨hx, hx'⟩
    rw [h0, Null_eq_empty] at this; exact this
  refine ⟨fun R x => ∃ A, (A ∈ K ∧ x ∈ A) ∧ R = x ↓ A, mem_smsmbar_iff.2 ⟨⟨?_, ?_⟩, ?_⟩⟩
  · refine mem_arrow_one_one.2 ⟨?_, ?_⟩
    · rintro R R' x ⟨⟨A, ⟨hA, hx⟩, rfl⟩, ⟨B, ⟨hB, hx'⟩, rfl⟩⟩
      rw [hex A B x hA hB hx hx']
    · rintro R x y ⟨⟨A, -, rfl⟩, ⟨B, -, e⟩⟩
      exact (couple_eq_couple_iff.1 e).1
  · ext x
    exact ⟨fun ⟨A, hA, hx⟩ => ⟨_, A, ⟨hA, hx⟩, rfl⟩, fun ⟨_, A, ⟨hA, hx⟩, _⟩ => ⟨A, hA, hx⟩⟩
  · ext u
    constructor
    · rintro ⟨A, hA, rfl⟩
      refine ⟨A, hA, ?_⟩
      ext R
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, A, ⟨hA, hx⟩, rfl⟩
      · rintro ⟨x, hx, B, ⟨hB, hx'⟩, rfl⟩
        rw [← hex A B x hA hB hx hx']; exact ⟨x, hx, rfl⟩
    · rintro ⟨A, hA, rfl⟩
      refine ⟨A, hA, ?_⟩
      ext R
      constructor
      · rintro ⟨x, hx, B, ⟨hB, hx'⟩, rfl⟩
        rw [← hex A B x hA hB hx hx']; exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, A, ⟨hA, hx⟩, rfl⟩

private theorem downImg_excl (K : Set (Set α)) : opL downCls memRel ʻʻ K ∈ Cls2excl := by
  rintro _ _ ⟨⟨⟨A, -, rfl⟩, ⟨B, -, rfl⟩⟩, hne⟩
  exact downCls_disjoint fun h => hne (h ▸ rfl)

private theorem sumCls_mem_sigmaNc {K : Set (Set α)} (hK : K ∈ Cls2excl) :
    sumCls K ∈ sigmaNc α K :=
  sm_symm (pm111_44 (downImg_smsm hK)).2

private theorem sigmaNc_eq_nc_sumCls {K : Set (Set α)} (hK : K ∈ Cls2excl) :
    sigmaNc γ K = nc γ (sumCls K) :=
  nc_eq_nc_of_sm (pm111_44 (downImg_smsm hK)).2

private theorem adeqSigmaNc_nonempty {W : Type*} {K : Set (Set α)} (h : AdeqSigmaNc W K)
    (K' : Set (Set α)) : (sigmaNc W K').Nonempty := by
  obtain ⟨f, hf⟩ := nc_nonempty_iff.1 h
  have hsub : clsSigma K' ⊆ clsSigma (typ₀ K) := by
    intro R hR
    obtain ⟨A, x, ⟨-, hx⟩, rfl⟩ := mem_clsSigma.1 hR
    exact couple_mem_clsSigma.2 ⟨by rw [typ₀_eq_univ]; trivial, hx⟩
  exact nc_nonempty_iff.2 ⟨f ∘ Set.inclusion hsub, hf.comp (Set.inclusion_injective hsub)⟩

end Helpers112

/-!
## [✱112] The arithmetical sum of a class of classes

*(Vol. 2, p. 97)*

> *Summary of* *112.
>
> In this number, we return to the arithmetical operations. The definition of addition in *110 was only applicable to a finite number of summands, because the summands had to be enumerated. In the present number, we define the arithmetical sum of a class of classes, so that the summands are given as the members of a class, and do not require to be enumerated. Hence the definition in this number is as applicable to an infinite number of summands as to a finite number.
>
> …

**Lean reading.** `Σ'κ` is `clsSigma K`, the couples `x ↓ α` with `x ∈ α ∈ κ`; `∈↧` is
`opL downCls memRel` (✱85·5, ✱38·01), so `∈↧α` is `memRel ↧ A` and `∈↧''κ` is
`opL downCls memRel ʻʻ K`; the relation `Σ` is `ClsSigma`. `ΣNc'κ` is `sigmaNc γ K` with its type
explicit; an attributive occurrence `β ∈ ΣNc'κ` is in the type of `β`, equational occurrences in
a type parameter. As arguments of `+_c`, `ΣNc'κ` and inner sums get adequate types (IIT), `Nc'α`
is `n₀c A` (✱110·03·04). `T̆_∈` is `imgRelCnv T`, `T ‖ S` is `T ∥ S`. `Mult ax` is at the type
of the classes whose selections ✱111 uses. The e-text prints `ᗡ'''sm` for `Rl'sm` (✱112·22·231),
drops the `=` of `ΣNc'κ = ΣNc'λ` in ✱112·17, prints `κ ∩ Λ` for `κ ∩ λ` in ✱112·303, and omits
`⊢` in ✱112·151·153 (immaterial). The erratum to ✱112·23 (dots) is already incorporated in the
e-text.

**Status.** proved (all propositions; ✱112·17·22·231·303·311·341·35 proved (reading), see their docstrings)
-/

/-- ✱112·01 (Df). \(\Sigma ʻ\kappa = sʻ\in \unicode{x21A7} ʻʻ\kappa \quad\text{Df}\) -/
theorem pm112_01 {K : Set (Set α)} : clsSigma K = sumCls (opL downCls memRel ʻʻ K) := rfl

/-- ✱112·02 (Df). \(\Sigma \text{Nc}ʻ\kappa = \text{Nc}ʻ\Sigma ʻ\kappa \quad\text{Df}\) -/
theorem pm112_02 {K : Set (Set α)} : sigmaNc γ K = nc γ (clsSigma K) := rfl

/-- ✱112·1. \(\vdash .\Sigma ʻ\kappa = sʻ\in \unicode{x21A7} ʻʻ\kappa \quad[*20·2. (*112·01)]\)

PM gives the value of the descriptive function `Σ'κ`, so the statement keeps the description
(Basic §5). -/
theorem pm112_1 {K : Set (Set α)} :
    Desc ClsSigma K (fun S => S = sumCls (opL downCls memRel ʻʻ K)) :=
  (desc_ClsSigma K _).2 rfl

/-- ✱112·101. \(\vdash .\Sigma \text{Nc}ʻ\kappa = \text{Nc}ʻ\Sigma ʻ\kappa = \text{Nc}ʻsʻ\in \unicode{x21A7}ʻʻ\kappa \quad[*20·2. *112·1. (*112*02)]\)

The first link keeps the description `ΣNc'κ` (its value is what PM gives); the equational
occurrences are in one type `γ`. -/
theorem pm112_101 {K : Set (Set α)} :
    Desc (SigmaNc : Set (Set γ) → Set (Set α) → Prop) K (fun X => X = nc γ (clsSigma K)) ∧
      nc γ (clsSigma K) = nc γ (sumCls (opL downCls memRel ʻʻ K)) :=
  ⟨(desc_SigmaNc K _).2 rfl, rfl⟩

/-- ✱112·102. \(\vdash .\Sigma ʻ\kappa = \hat{R} \{(\exists \alpha ,x).\alpha \in \kappa .x\in \alpha .R=x\downarrow \alpha\}\) -/
theorem pm112_102 {K : Set (Set α)} :
    clsSigma K = {R | ∃ A x, (A ∈ K ∧ x ∈ A) ∧ R = x ↓ A} :=
  Set.ext fun _ => mem_clsSigma

/-- ✱112·103. \(\vdash .\Sigma ʻ\kappa = sʻ\hat{\mu} \{(\exists \alpha ).\alpha \in \kappa .\mu =\downarrow \alpha ʻʻ\alpha\} \quad[*112·1. *85·6]\)

`↓α''α` is `coupleR A ʻʻ A`. -/
theorem pm112_103 {K : Set (Set α)} :
    clsSigma K = sumCls {M | ∃ A, A ∈ K ∧ M = coupleR A ʻʻ A} := rfl

/-- ✱112·11. \(\vdash :\beta \in \Sigma \text{Nc}ʻ\kappa .\equiv . \beta \text{ sm } sʻ\in \unicode{x21A7}ʻʻ\kappa \quad[*112·101]\)

`β ∈ ΣNc'κ` is in the type of `β`. -/
theorem pm112_11 {K : Set (Set α)} {B : Set γ} :
    B ∈ sigmaNc γ K ↔ sm B (sumCls (opL downCls memRel ʻʻ K)) := Iff.rfl

/-- ✱112·12. \(\vdash .sʻ\in \unicode{x21A7}ʻʻ\kappa \in \Sigma \text{Nc}ʻ\kappa \quad[*112·11]\) -/
theorem pm112_12 {K : Set (Set α)} :
    sumCls (opL downCls memRel ʻʻ K) ∈ sigmaNc (α → Set α → Prop) K := sm_refl _

/-- ✱112·13. \(\vdash :\lambda \text{ sm } \text{ sm } \in \unicode{x21A7}ʻʻ\kappa . \supset . sʻ\lambda \in \Sigma \text{Nc}ʻ\kappa \quad[*111·44. *112·11]\) -/
theorem pm112_13 {K : Set (Set α)} {L : Set (Set δ)} :
    smsm L (opL downCls memRel ʻʻ K) → sumCls L ∈ sigmaNc δ K :=
  fun h => (pm111_44 h).2

/-- ✱112·14. \(\vdash :\kappa \in \text{Cls}^{2} \text{excl}. \supset . \in \unicode{x21A7} ʻʻ\kappa \text{ sm } \text{ sm } \kappa\) -/
theorem pm112_14 {K : Set (Set α)} : K ∈ Cls2excl → smsm (opL downCls memRel ʻʻ K) K :=
  downImg_smsm

/-- ✱112·15. \(\vdash :\kappa \in \text{Cls}^{2} \text{excl}. \supset . sʻ\kappa \in \Sigma \text{Nc}ʻ\kappa \quad[*112·14·11. *111·44]\) -/
theorem pm112_15 {K : Set (Set α)} : K ∈ Cls2excl → sumCls K ∈ sigmaNc α K :=
  sumCls_mem_sigmaNc

/-- ✱112·151. \(sʻ\in \unicode{x21A7}ʻʻ\lambda = \hat{R} \{(\exists \alpha ,x).\alpha \in \lambda .x\in \alpha .R = x\downarrow \alpha \}.\dot{s} ʻsʻ\in \unicode{x21A7}ʻʻ\lambda = \in \upharpoonright \lambda\)

(The e-text omits the assertion-sign.) The two equations are a product. -/
theorem pm112_151 {L : Set (Set α)} :
    sumCls (opL downCls memRel ʻʻ L) = {R | ∃ A x, (A ∈ L ∧ x ∈ A) ∧ R = x ↓ A} ∧
      sumRel (sumCls (opL downCls memRel ʻʻ L)) = memRel ↾ L := by
  refine ⟨Set.ext fun _ => mem_clsSigma, ?_⟩
  funext y B
  apply propext
  constructor
  · rintro ⟨R, hR, hyB⟩
    obtain ⟨A, x, ⟨hA, hx⟩, rfl⟩ := mem_clsSigma.1 hR
    obtain ⟨rfl, rfl⟩ := (couple_apply x A y B).1 hyB
    exact ⟨hx, hA⟩
  · rintro ⟨hy, hB⟩
    exact ⟨y ↓ B, couple_mem_clsSigma.2 ⟨hB, hy⟩, (couple_apply y B y B).2 ⟨rfl, rfl⟩⟩

/-- ✱112·152. \(\vdash :T\in 1\rightarrow Cls.\beta \subset \text{ᗡ}ʻT.\supset .(T\parallel \breve{T} _{\in })ʻʻ\in \unicode{x21A7}\beta = \in \unicode{x21A7}(Tʻʻ\beta )\)

`T̆_∈` is `imgRelCnv T` (`= (imgRel T)˘`, ✱37·03), and `∈↧β` is `memRel ↧ B`. -/
theorem pm112_152 {T : α → β → Prop} {B : Set β} :
    T ∈ arrow one Cls ∧ B ⊆ codom T → (T ∥ imgRelCnv T) ʻʻ (memRel ↧ B) = memRel ↧ (T ʻʻ B) := by
  rintro ⟨hT, hB⟩
  have key : ∀ x y, T x y → T ⨾ ((y ↓ B) ⨾ imgRelCnv T) = x ↓ (T ʻʻ B) := by
    intro x y hxy
    funext a z
    apply propext
    constructor
    · rintro ⟨y', hay', w, hw, hwz⟩
      obtain ⟨rfl, rfl⟩ := (couple_apply y B y' w).1 hw
      exact ⟨mem_arrow_one_Cls.1 hT a x y' ⟨hay', hxy⟩, hwz⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨y, hxy, B, ⟨rfl, rfl⟩, rfl⟩
  ext P
  constructor
  · rintro ⟨Q, ⟨y, hy, rfl⟩, hP⟩
    obtain ⟨x, hxy⟩ := hB hy
    rw [(dpar_iff _ _ _ _).1 hP, key x y hxy]
    exact ⟨x, ⟨y, hy, hxy⟩, rfl⟩
  · rintro ⟨x, ⟨y, hy, hxy⟩, rfl⟩
    exact ⟨y ↓ B, ⟨y, hy, rfl⟩, (dpar_iff _ _ _ _).2 (key x y hxy).symm⟩

/-- ✱112·153. \(T\in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda .\supset .(T\parallel \breve{T} _{\in })\upharpoonright sʻ\in \unicode{x21A7}ʻʻ\lambda \in (\in \unicode{x21A7}ʻʻ\kappa )\,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, (\in \unicode{x21A7}ʻʻ\lambda )\)

(The e-text omits the assertion-sign.) -/
theorem pm112_153 {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop} :
    T ∈ smsmbar K L →
      (T ∥ imgRelCnv T) ↾ sumCls (opL downCls memRel ʻʻ L) ∈
        smsmbar (opL downCls memRel ʻʻ K) (opL downCls memRel ʻʻ L) := by
  intro h
  obtain ⟨⟨hT, hLc⟩, hK⟩ := mem_smsmbar_iff.1 h
  have hT1 := oneCls_of_oneone hT
  have hsub : ∀ B, B ∈ L → B ⊆ codom T := fun B hB => (subset_sumCls hB).trans hLc.le
  have key : ∀ x y B, T x y → T ⨾ ((y ↓ B) ⨾ imgRelCnv T) = x ↓ (T ʻʻ B) := by
    intro x y B hxy
    funext a z
    apply propext
    constructor
    · rintro ⟨y', hay', w, hw, hwz⟩
      obtain ⟨rfl, rfl⟩ := (couple_apply y B y' w).1 hw
      exact ⟨mem_arrow_one_Cls.1 hT1 a x y' ⟨hay', hxy⟩, hwz⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨y, hxy, B, ⟨rfl, rfl⟩, rfl⟩
  refine mem_smsmbar_iff.2 ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro P P' Q ⟨⟨hP, -⟩, ⟨hP', -⟩⟩
    rw [(dpar_iff _ _ _ _).1 hP, (dpar_iff _ _ _ _).1 hP']
  · rintro P Q Q' ⟨⟨hP, hQ⟩, ⟨hP', hQ'⟩⟩
    obtain ⟨B, y, ⟨hB, hy⟩, rfl⟩ := mem_clsSigma.1 hQ
    obtain ⟨B', y', ⟨hB', hy'⟩, rfl⟩ := mem_clsSigma.1 hQ'
    obtain ⟨x, hxy⟩ := hsub B hB hy
    obtain ⟨x', hxy'⟩ := hsub B' hB' hy'
    have e := ((dpar_iff _ _ _ _).1 hP).symm.trans ((dpar_iff _ _ _ _).1 hP')
    rw [key x y B hxy, key x' y' B' hxy'] at e
    obtain ⟨rfl, e2⟩ := couple_eq_couple_iff.1 e
    have hBB := img_inj hT (hsub B hB) (hsub B' hB') e2
    subst hBB
    rw [(mem_arrow_one_one.1 hT).2 x y y' ⟨hxy, hxy'⟩]
  · ext Q
    constructor
    · intro hQ
      exact ⟨T ⨾ (Q ⨾ imgRelCnv T), (dpar_iff _ _ _ _).2 rfl, hQ⟩
    · rintro ⟨P, -, hQ⟩; exact hQ
  · rw [hK]
    have himg : ∀ B, B ∈ L →
        ((T ∥ imgRelCnv T) ↾ sumCls (opL downCls memRel ʻʻ L)) ʻʻ (memRel ↧ B) =
          memRel ↧ (T ʻʻ B) := by
      intro B hB
      rw [← (pm112_152 (T := T) ⟨hT1, hsub B hB⟩)]
      ext P
      constructor
      · rintro ⟨Q, hQ, hPQ, -⟩; exact ⟨Q, hQ, hPQ⟩
      · rintro ⟨Q, hQ, hPQ⟩
        exact ⟨Q, hQ, hPQ, ⟨memRel ↧ B, ⟨B, hB, rfl⟩, hQ⟩⟩
    ext u
    constructor
    · rintro ⟨_, ⟨B, hB, rfl⟩, rfl⟩
      exact ⟨memRel ↧ B, ⟨B, hB, rfl⟩, (himg B hB).symm⟩
    · rintro ⟨_, ⟨B, hB, rfl⟩, rfl⟩
      exact ⟨T ʻʻ B, ⟨B, hB, rfl⟩, himg B hB⟩

/-- ✱112·16. \(\vdash : \kappa \text{ sm } \text{ sm } \lambda . \supset . \in \unicode{x21A7} ʻʻ\kappa \text{ sm } \text{ sm } \in \unicode{x21A7} ʻʻ\lambda \quad[*112·153 . *111·4]\) -/
theorem pm112_16 {K : Set (Set α)} {L : Set (Set β)} :
    smsm K L → smsm (opL downCls memRel ʻʻ K) (opL downCls memRel ʻʻ L) :=
  fun ⟨T, hT⟩ => ⟨_, pm112_153 hT⟩

/-- ✱112·17. \(\vdash : \kappa \text{ sm } \text{ sm } \lambda . \supset . \Sigma \text{Nc}ʻ\kappa . \Sigma \text{Nc}ʻ\lambda . \Sigma ʻ\kappa \text{ sm } \Sigma ʻ\lambda\)

The equation `ΣNc'κ = ΣNc'λ` is in a free type `γ`.

**Status.** proved (reading): transcription error: the e-text prints `ΣNc'κ . ΣNc'λ` for
`ΣNc'κ = ΣNc'λ` (the Summary of ✱112 has the `=`). -/
theorem pm112_17 {K : Set (Set α)} {L : Set (Set β)} :
    smsm K L → sigmaNc γ K = sigmaNc γ L ∧ sm (clsSigma K) (clsSigma L) := by
  intro h
  have h2 := (pm111_44 (pm112_16 h)).2
  exact ⟨nc_eq_nc_of_sm h2, h2⟩

/-- ✱112·18. \(\vdash . \Sigma \text{Nc}ʻ\kappa = \Sigma \text{Nc}ʻ\in \unicode{x21A7} ʻʻ\kappa\) -/
theorem pm112_18 {K : Set (Set α)} : sigmaNc γ K = sigmaNc γ (opL downCls memRel ʻʻ K) :=
  (sigmaNc_eq_nc_sumCls (downImg_excl K)).symm

/-- ✱112·2. \[\begin{aligned}\vdash : S \in 1 \rightarrow 1 . \text{D}ʻS = \in &\unicode{x21A7} ʻʻ\kappa . \text{ᗡ}ʻS = \in \unicode{x21A7} ʻʻ\lambda . \exists ! {\in}_{\Delta} ʻ\text{Crp} (S)ʻʻ\lambda .\\ &\supset . \Sigma \text{Nc}ʻ\kappa = \Sigma \text{Nc}ʻ\lambda . \Sigma ʻ\kappa \text{ sm } \Sigma ʻ\lambda\end{aligned}\] -/
theorem pm112_2 {K : Set (Set α)} {L : Set (Set β)}
    {S : Set (α → Set α → Prop) → Set (β → Set β → Prop) → Prop} :
    ((S ∈ arrow one one ∧ dom S = opL downCls memRel ʻʻ K) ∧ codom S = opL downCls memRel ʻʻ L) ∧
        (sel memRel (Crp S ʻʻ (opL downCls memRel ʻʻ L))).Nonempty →
      sigmaNc γ K = sigmaNc γ L ∧ sm (clsSigma K) (clsSigma L) := by
  rintro ⟨⟨⟨hS, hd⟩, hc⟩, hR⟩
  have hSL : S ʻʻ (opL downCls memRel ʻʻ L) = opL downCls memRel ʻʻ K := by
    rw [← hc, img_codom, hd]
  have h2 := pm111_311 ⟨⟨⟨⟨downImg_excl L, hSL ▸ downImg_excl K⟩, hS⟩, hR⟩, hc.ge⟩
  rw [hSL] at h2
  exact ⟨nc_eq_nc_of_sm h2, h2⟩

/-- ✱112·21. \[\begin{aligned}\vdash \colon\ldotp \text{Mult ax} . \supset : (\exists S) . S \in 1 \rightarrow 1 . &S \,\unicode{x2abd}\, \text{ sm } . \text{D}ʻS = \in \unicode{x21A7} ʻʻ\kappa . \text{ᗡ}ʻS = \in \unicode{x21A7} ʻʻ\lambda .\\ &\equiv . \in \unicode{x21A7} ʻʻ\kappa \text{ sm } \text{ sm } \in \unicode{x21A7} ʻʻ\lambda \quad[*111·5 . *85·61]\end{aligned}\]

`Mult ax` at the type of the classes `Crp(S)'β` of ✱111·5 (relations between the members of
`∈↧''κ` and of `∈↧''λ`). -/
theorem pm112_21 {K : Set (Set α)} {L : Set (Set β)} :
    MultAx ((α → Set α → Prop) → (β → Set β → Prop) → Prop) →
      ((∃ S : Set (α → Set α → Prop) → Set (β → Set β → Prop) → Prop,
          ((S ∈ arrow one one ∧ S ⪽ sm) ∧ dom S = opL downCls memRel ʻʻ K) ∧
            codom S = opL downCls memRel ʻʻ L) ↔
        smsm (opL downCls memRel ʻʻ K) (opL downCls memRel ʻʻ L)) :=
  fun hM => ((pm111_5 hM ⟨downImg_excl K, downImg_excl L⟩).1).symm

/-- ✱112·22. \[\begin{aligned}\vdash \colon\ldotp \text{Mult ax} . \supset : \exists ! (\in \unicode{x21A7} ʻʻ\kappa ) \,\overline{\text{ sm }}\, (\in \unicode{x21A7} ʻʻ\lambda \cap \text{ᗡ}ʻʻ ʻ\text{ sm } . \supset .\\ \Sigma \text{Nc}ʻ\kappa = \Sigma \text{Nc}ʻ\lambda \quad[*112·17·18·21]\end{aligned}\]

The equation is in a free type `γ`.

**Status.** proved (reading): transcription error: the e-text prints `ᗡ'''sm` for `Rl'sm` (and
drops a bracket), as the Summary of ✱112 shows. -/
theorem pm112_22 {K : Set (Set α)} {L : Set (Set β)} :
    MultAx ((α → Set α → Prop) → (β → Set β → Prop) → Prop) →
      (smbar (opL downCls memRel ʻʻ K) (opL downCls memRel ʻʻ L) ∩ rl sm).Nonempty →
        sigmaNc γ K = sigmaNc γ L := by
  intro hM h
  have := pm111_5 hM ⟨downImg_excl K, downImg_excl L⟩
  rw [pm112_18 (K := K), pm112_18 (K := L)]
  exact (pm112_17 (this.1.2 (this.2.2 h))).1

/-- ✱112·23. \[\begin{aligned}\vdash \colon\ldotp \text{Mult ax} . \supset : \kappa , \lambda \in \text{Cls}^{2} \text{excl} . \exists ! \kappa &\,\overline{\text{ sm }}\, \lambda \cap \text{Rl}ʻ\text{ sm } . \supset .\\ &sʻ\kappa , sʻ\lambda \in \Sigma \text{Nc}ʻ\kappa . \Sigma \text{Nc}ʻ\kappa = \Sigma \text{Nc}ʻ\lambda\end{aligned}\]

`s'κ, s'λ ∈ ΣNc'κ`: attributive occurrences, each in the type of its class; the equation in a
free type `γ`. `Mult ax` is at the type of ✱111·51. (The erratum to the dots, Additional Errata,
p. 101, is already incorporated in the e-text.) -/
theorem pm112_23 {K : Set (Set α)} {L : Set (Set β)} :
    MultAx (α → β → Prop) →
      (K ∈ Cls2excl ∧ L ∈ Cls2excl) ∧ (smbar K L ∩ rl sm).Nonempty →
        (sumCls K ∈ sigmaNc α K ∧ sumCls L ∈ sigmaNc β K) ∧ sigmaNc γ K = sigmaNc γ L := by
  rintro hM ⟨⟨hK, hL⟩, h⟩
  have hs := pm111_51 hM ⟨⟨hK, hL⟩, h⟩
  refine ⟨⟨sumCls_mem_sigmaNc hK, sm_trans (sm_symm hs) (sumCls_mem_sigmaNc hK)⟩, ?_⟩
  rw [sigmaNc_eq_nc_sumCls hK, sigmaNc_eq_nc_sumCls hL]
  exact nc_eq_nc_of_sm hs

/-- ✱112·231. \(\vdash : S \in \kappa \,\overline{\text{ sm }}\, \lambda \cap \text{ᗡ}ʻʻ ʻ\text{ sm } . \supset . \in \unicode{x21A7} \mid S\mid \text{Cnv}ʻ\in \unicode{x21A7} \in (\in \unicode{x21A7} ʻʻ\kappa ) \,\overline{\text{ sm }}\, ( \in \unicode{x21A7} ʻʻ\lambda ) \cap \text{Rl} ʻ\text{ sm }\)

`∈↧ | S | Cnv'∈↧` is `opL downCls memRel ⨾ S ⨾ (opL downCls memRel)˘` (`Cnv'P` is `P˘`).

**Status.** proved (reading): transcription error: the e-text prints `ᗡ'''sm` for `Rl'sm` in the
hypothesis (the conclusion has `Rl'sm`). -/
theorem pm112_231 {K : Set (Set α)} {L : Set (Set β)} {S : Set α → Set β → Prop} :
    S ∈ smbar K L ∩ rl sm →
      opL downCls memRel ⨾ S ⨾ (opL downCls memRel)˘ ∈
        smbar (opL downCls memRel ʻʻ K) (opL downCls memRel ʻʻ L) ∩ rl sm := by
  rintro ⟨hS, hsm⟩
  obtain ⟨⟨hS1, hK⟩, hL⟩ := mem_smbar_iff.1 hS
  obtain ⟨s1, s2⟩ := mem_arrow_one_one.1 hS1
  have hrel : ∀ u v, (opL downCls memRel ⨾ S ⨾ (opL downCls memRel)˘) u v ↔
      ∃ A B, S A B ∧ u = memRel ↧ A ∧ v = memRel ↧ B := by
    intro u v
    constructor
    · rintro ⟨B, ⟨A, hu, hAB⟩, hv⟩; exact ⟨A, B, hAB, hu, hv⟩
    · rintro ⟨A, B, hAB, hu, hv⟩; exact ⟨B, ⟨A, hu, hAB⟩, hv⟩
  refine ⟨mem_smbar_iff.2 ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro u u' v ⟨h1, h2⟩
    obtain ⟨A, B, hAB, rfl, rfl⟩ := (hrel _ _).1 h1
    obtain ⟨A', B', hAB', rfl, e⟩ := (hrel _ _).1 h2
    rw [s1 A A' B ⟨hAB, (downCls_inj e) ▸ hAB'⟩]
  · intro u v v' ⟨h1, h2⟩
    obtain ⟨A, B, hAB, rfl, rfl⟩ := (hrel _ _).1 h1
    obtain ⟨A', B', hAB', e, rfl⟩ := (hrel _ _).1 h2
    rw [s2 A B B' ⟨hAB, (downCls_inj e) ▸ hAB'⟩]
  · rw [hK]
    ext u
    constructor
    · rintro ⟨A, ⟨B, hAB⟩, rfl⟩; exact ⟨_, (hrel _ _).2 ⟨A, B, hAB, rfl, rfl⟩⟩
    · rintro ⟨v, h⟩
      obtain ⟨A, B, hAB, rfl, rfl⟩ := (hrel _ _).1 h
      exact ⟨A, ⟨B, hAB⟩, rfl⟩
  · rw [hL]
    ext v
    constructor
    · rintro ⟨B, ⟨A, hAB⟩, rfl⟩; exact ⟨_, (hrel _ _).2 ⟨A, B, hAB, rfl, rfl⟩⟩
    · rintro ⟨u, h⟩
      obtain ⟨A, B, hAB, rfl, rfl⟩ := (hrel _ _).1 h
      exact ⟨B, ⟨A, hAB⟩, rfl⟩
  · intro u v h
    obtain ⟨A, B, hAB, rfl, rfl⟩ := (hrel _ _).1 h
    exact sm_trans (downCls_sm A) (sm_trans (hsm A B hAB) (sm_symm (downCls_sm B)))

/-- ✱112·24. \(\vdash \colon\ldotp \text{Mult ax}.\supset :\mu ,\nu \in \text{NC}.\kappa ,\lambda \in \mu \cap \text{Cl}ʻ\nu .\supset .\Sigma \text{Nc}ʻ\kappa = \Sigma \text{Nc}ʻ\lambda\)

`Mult ax` at the type used in PM's demonstration (✱111·51 applied to `∈↧''κ`, `∈↧''λ`). -/
theorem pm112_24 {β₁ β₂ : Type*} {μ : Set (Set (Set α))} {ν : Set (Set α)} {K L : Set (Set α)} :
    MultAx ((α → Set α → Prop) → (α → Set α → Prop) → Prop) →
      (μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ (K ∈ μ ∩ cl ν ∧ L ∈ μ ∩ cl ν) → sigmaNc γ K = sigmaNc γ L := by
  rintro hM h
  have h1 := pm112_231 (pm111_52 h).some_mem
  have h2 := pm111_51 hM ⟨⟨downImg_excl K, downImg_excl L⟩, ⟨_, h1⟩⟩
  rw [pm112_18 (K := K), pm112_18 (K := L), sigmaNc_eq_nc_sumCls (downImg_excl K),
    sigmaNc_eq_nc_sumCls (downImg_excl L)]
  exact nc_eq_nc_of_sm h2

/-- ✱112·3. \(\vdash .\Sigma ʻ\Lambda = \Lambda \quad[*37·29.*40·21.*112·1]\) -/
theorem pm112_3 : clsSigma (Λ : Set (Set α)) = Λ := by
  rw [Null_eq_empty, Null_eq_empty]
  ext R; simp [mem_clsSigma]

/-- ✱112·301. \(\vdash .\Sigma ʻ\iota ʻ\Lambda = \Lambda\) -/
theorem pm112_301 : clsSigma (ι (Λ : Set α)) = Λ := by
  rw [clsSigma_unitCls, Null_eq_empty, Null_eq_empty]
  ext R; simp [mem_downCls]

/-- ✱112·302. \(\vdash .\Sigma ʻ\kappa = \Sigma ʻ(\kappa -\iota ʻ\Lambda )\) -/
theorem pm112_302 {K : Set (Set α)} : clsSigma K = clsSigma (K \ ι Λ) := by
  ext R
  rw [mem_clsSigma, mem_clsSigma]
  constructor
  · rintro ⟨A, x, ⟨hA, hx⟩, rfl⟩
    refine ⟨A, x, ⟨⟨hA, fun h => ?_⟩, hx⟩, rfl⟩
    rw [mem_unitCls, Null_eq_empty] at h
    rw [h] at hx; exact hx
  · rintro ⟨A, x, ⟨⟨hA, -⟩, hx⟩, rfl⟩; exact ⟨A, x, ⟨hA, hx⟩, rfl⟩

/-- ✱112·303. \(\vdash : \kappa \cap \Lambda = \Lambda . \supset . \Sigma ʻ\kappa \cap \Sigma ʻ\lambda = \Lambda\)

**Status.** proved (reading): transcription error: the e-text prints `κ ∩ Λ = Λ` for
`κ ∩ λ = Λ`, as the demonstration (`∃!κ ∩ λ`, Transp) and the use in ✱112·311 show; as printed
the proposition would be false (`κ = λ = ι'α` with `∃!α`). -/
theorem pm112_303 {K L : Set (Set α)} : K ∩ L = Λ → clsSigma K ∩ clsSigma L = Λ :=
  clsSigma_disjoint

/-- ✱112·304. \(\vdash :\Sigma ʻ\kappa = \Lambda . \equiv .sʻ\kappa = \Lambda\) -/
theorem pm112_304 {K : Set (Set α)} : clsSigma K = Λ ↔ sumCls K = Λ := by
  rw [Null_eq_empty, Null_eq_empty, Set.eq_empty_iff_forall_notMem,
    Set.eq_empty_iff_forall_notMem]
  constructor
  · rintro h x ⟨A, hA, hx⟩; exact h (x ↓ A) (couple_mem_clsSigma.2 ⟨hA, hx⟩)
  · rintro h R hR
    obtain ⟨A, x, ⟨hA, hx⟩, -⟩ := mem_clsSigma.1 hR
    exact h x ⟨A, hA, hx⟩

/-- ✱112·31. \(\vdash .\Sigma ʻ(\kappa \cup \lambda ) = \Sigma ʻ\kappa \cup \Sigma ʻ\lambda\) -/
theorem pm112_31 {K L : Set (Set α)} : clsSigma (K ∪ L) = clsSigma K ∪ clsSigma L :=
  clsSigma_union K L

/-- ✱112·311. \(\vdash : \kappa \cap \lambda = \Lambda . \supset . \Sigma \text{Nc}ʻ(\kappa \cup \lambda ) = \Sigma \text{Nc}ʻ\kappa +_{c} \Sigma \text{Nc}ʻ\lambda\)

The arguments `ΣNc'κ`, `ΣNc'λ` of `+_c` are arithmetical occurrences of formal numbers of the
primary group: by IIT their types `W₁`, `W₂` are adequate; the equation is in a free type `γ`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components ΣNc'κ, ΣNc'λ are adequate -/
theorem pm112_311 {W₁ W₂ : Type*} {K L : Set (Set α)} (h₁ : AdeqSigmaNc W₁ K)
    (h₂ : AdeqSigmaNc W₂ L) :
    K ∩ L = Λ → sigmaNc γ (K ∪ L) = (sigmaNc W₁ K +ᶜ sigmaNc W₂ L : Set (Set γ)) := by
  intro h
  obtain ⟨X, hX⟩ := adeqSigmaNc_nonempty h₁ K
  obtain ⟨Y, hY⟩ := adeqSigmaNc_nonempty h₂ L
  rw [show sigmaNc W₁ K = n₀c X from nc_eq_n₀c_of_mem hX,
    show sigmaNc W₂ L = n₀c Y from nc_eq_n₀c_of_mem hY, n₀c_cardAdd_n₀c, sigmaNc, clsSigma_union]
  apply nc_eq_nc_of_sm
  exact sm_trans (pm110_14 (clsSigma_disjoint h)) (sm_clsSum (sm_symm hX) (sm_symm hY))

/-- ✱112·32. \(\vdash . \Sigma ʻ\iota ʻ\alpha = \in \unicode{x21A7} \alpha\) -/
theorem pm112_32 {A : Set α} : clsSigma (ι A) = memRel ↧ A := clsSigma_unitCls A

/-- ✱112·321. \(\vdash . \Sigma \text{Nc}ʻ\iota ʻ\alpha = \text{Nc}ʻ\alpha \quad[*112·32·101 . *85·601]\) -/
theorem pm112_321 {A : Set α} : sigmaNc γ (ι A) = nc γ A := by
  rw [sigmaNc, clsSigma_unitCls]; exact nc_eq_nc_of_sm (downCls_sm A)

/-- ✱112·33. \(\vdash . \Sigma ʻ(\iota ʻ\alpha \cup \iota ʻ\beta ) = \in \unicode{x21A7} \alpha \cup \in \unicode{x21A7} \beta \quad[*112·32·31]\) -/
theorem pm112_33 {A B : Set α} : clsSigma (ι A ∪ ι B) = memRel ↧ A ∪ memRel ↧ B := by
  rw [clsSigma_union, clsSigma_unitCls, clsSigma_unitCls]

/-- ✱112·331. \(\vdash . \Sigma ʻ(\kappa \cup \iota ʻ\beta ) = \Sigma ʻ\kappa \cup \in \unicode{x21A7} \beta \quad[*112·31·32]\) -/
theorem pm112_331 {K : Set (Set α)} {B : Set α} :
    clsSigma (K ∪ ι B) = clsSigma K ∪ memRel ↧ B := by
  rw [clsSigma_union, clsSigma_unitCls]

/-- ✱112·34. \(\vdash : \alpha \neq \beta . \supset . \Sigma \text{Nc}ʻ(\iota ʻ\alpha \cup \iota ʻ\beta ) = \text{Nc}ʻ\alpha +_{c} \text{Nc}ʻ\beta\)

The arguments `Nc'α`, `Nc'β` of `+_c` are `n₀c A`, `n₀c B` (✱110·03·04). -/
theorem pm112_34 {A B : Set α} :
    A ≠ B → sigmaNc γ (ι A ∪ ι B) = (n₀c A +ᶜ n₀c B : Set (Set γ)) := by
  intro h
  rw [sigmaNc, pm112_33, n₀c_cardAdd_n₀c]
  exact nc_eq_nc_of_sm (sm_trans (pm110_14 (downCls_disjoint h))
    (sm_clsSum (downCls_sm A) (downCls_sm B)))

/-- ✱112·341. \(\vdash : \beta {\sim} \in \kappa . \supset . \Sigma \text{Nc}ʻ(\kappa \cup \iota ʻ\beta ) = \Sigma \text{Nc}ʻ\kappa +_{c} \text{Nc}ʻ\beta\)

The argument `ΣNc'κ` of `+_c` has an adequate type (IIT); `Nc'β` is `n₀c B`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component ΣNc'κ is adequate -/
theorem pm112_341 {W : Type*} {K : Set (Set α)} {B : Set α} (hW : AdeqSigmaNc W K) :
    B ∉ K → sigmaNc γ (K ∪ ι B) = (sigmaNc W K +ᶜ n₀c B : Set (Set γ)) := by
  intro hB
  obtain ⟨X, hX⟩ := adeqSigmaNc_nonempty hW K
  have hd : K ∩ ι B = Λ := by
    rw [inter_eq_null_iff, Set.disjoint_left]
    intro A hA hA'
    rw [mem_unitCls.1 hA'] at hA; exact hB hA
  rw [show sigmaNc W K = n₀c X from nc_eq_n₀c_of_mem hX, n₀c_cardAdd_n₀c, sigmaNc, clsSigma_union,
    clsSigma_unitCls]
  apply nc_eq_nc_of_sm
  have hd' : clsSigma K ∩ memRel ↧ B = Λ := by
    rw [← clsSigma_unitCls]; exact clsSigma_disjoint hd
  exact sm_trans (pm110_14 hd') (sm_clsSum (sm_symm hX) (downCls_sm B))

/-- ✱112·35. \(\vdash : \alpha \neq \beta . \alpha \neq \gamma . \beta \neq \gamma . \supset . \Sigma \text{Nc}ʻ(\iota ʻ\alpha \cup \iota ʻ\beta \cup \iota ʻ\gamma ) = \text{Nc}ʻ\alpha +_{c} \text{Nc}ʻ\beta +_{c} \text{Nc}ʻ\gamma\)

The inner sum is an arithmetical component with an adequate type `W` (IIT); the arguments
`Nc'α`, … of `+_c` are `n₀c A`, … (✱110·03·04, ✱110·561).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component Nc'α +_c Nc'β is adequate -/
theorem pm112_35 {W : Type*} {A B G : Set α} (hW : AdeqAdd W (n₀c A) (n₀c B)) :
    (A ≠ B ∧ A ≠ G) ∧ B ≠ G →
      sigmaNc γ (ι A ∪ ι B ∪ ι G) = ((n₀c A +ᶜ n₀c B : Set (Set W)) +ᶜ n₀c G : Set (Set γ)) := by
  rintro ⟨⟨hAB, hAG⟩, hBG⟩
  rw [pm110_54 hW, sigmaNc, clsSigma_union, clsSigma_union, clsSigma_unitCls, clsSigma_unitCls,
    clsSigma_unitCls]
  apply nc_eq_nc_of_sm
  have hd : (memRel ↧ A ∪ memRel ↧ B) ∩ memRel ↧ G = Λ := by
    rw [inter_eq_null_iff, Set.disjoint_union_left]
    exact ⟨inter_eq_null_iff.1 (downCls_disjoint hAG), inter_eq_null_iff.1 (downCls_disjoint hBG)⟩
  refine sm_trans (pm110_14 hd) (sm_clsSum ?_ (downCls_sm G))
  exact sm_trans (pm110_14 (downCls_disjoint hAB)) (sm_clsSum (downCls_sm A) (downCls_sm B))

/-- ✱112·4. \(\vdash :sʻ\kappa ,sʻʻ\kappa \in \text{Cls}^{2} \text{excl}.\supset .\Sigma \text{Nc}ʻsʻ\kappa = \Sigma \text{Nc}ʻsʻʻ\kappa\)

`s''κ` is the image under the relation `s` (`graph sumCls`); `s'κ, s''κ ∈ Cls² excl` is a
product; the equation is in a free type `γ`. -/
theorem pm112_4 {K : Set (Set (Set α))} :
    sumCls K ∈ Cls2excl ∧ graph sumCls ʻʻ K ∈ Cls2excl →
      sigmaNc γ (sumCls K) = sigmaNc γ (graph sumCls ʻʻ K) := by
  rintro ⟨h1, h2⟩
  rw [sigmaNc_eq_nc_sumCls h1, sigmaNc_eq_nc_sumCls h2]
  congr 1
  ext x
  constructor
  · rintro ⟨A, ⟨M, hM, hA⟩, hx⟩; exact ⟨sumCls M, ⟨M, hM, rfl⟩, A, hA, hx⟩
  · rintro ⟨_, ⟨M, hM, rfl⟩, A, hA, hx⟩; exact ⟨A, ⟨M, hM, hA⟩, hx⟩

/-- ✱112·41. \(\vdash .sʻ\Sigma ʻʻ\lambda = \Sigma ʻsʻ\lambda\)

`Σ''λ` is the image under the relation `Σ` (`ClsSigma`). -/
theorem pm112_41 {L : Set (Set (Set α))} : sumCls (ClsSigma ʻʻ L) = clsSigma (sumCls L) := by
  ext R
  rw [mem_clsSigma]
  constructor
  · rintro ⟨_, ⟨K, hK, rfl⟩, hR⟩
    obtain ⟨A, x, ⟨hA, hx⟩, rfl⟩ := mem_clsSigma.1 hR
    exact ⟨A, x, ⟨⟨K, hK, hA⟩, hx⟩, rfl⟩
  · rintro ⟨A, x, ⟨⟨K, hK, hA⟩, hx⟩, rfl⟩
    exact ⟨clsSigma K, ⟨K, hK, rfl⟩, couple_mem_clsSigma.2 ⟨hA, hx⟩⟩

/-- ✱112·42. \(\vdash :\lambda \in \text{Cls}^{2} \text{excl}.\supset .\Sigma ʻʻ\lambda \in \text{Cls}^{2} \text{excl}\) -/
theorem pm112_42 {L : Set (Set (Set α))} : L ∈ Cls2excl → ClsSigma ʻʻ L ∈ Cls2excl := by
  rintro hL _ _ ⟨⟨⟨K, hK, rfl⟩, ⟨K', hK', rfl⟩⟩, hne⟩
  exact clsSigma_disjoint (hL K K' ⟨⟨hK, hK'⟩, fun h => hne (h ▸ rfl)⟩)

/-- ✱112·43. \(\vdash :\lambda \in \text{Cls}^{2} \text{excl}.\supset .\text{Nc}ʻ\Sigma ʻ\Sigma ʻʻ\lambda = \text{Nc}ʻ\Sigma ʻsʻ\lambda\)

Both `Nc'` are in one free type `γ` (meaning). -/
theorem pm112_43 {L : Set (Set (Set α))} :
    L ∈ Cls2excl → nc γ (clsSigma (ClsSigma ʻʻ L)) = nc γ (clsSigma (sumCls L)) := by
  intro h
  rw [← pm112_41]
  exact sigmaNc_eq_nc_sumCls (pm112_42 h)

section Helpers113

private theorem mem_clsTimes {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ∈ B ×ₐ A ↔ ∃ x y, (x ∈ A ∧ y ∈ B) ∧ R = x ↓ y := by
  constructor
  · rintro ⟨S, ⟨y, hy, hS⟩, hR⟩
    rw [show S = opImg couple A y from hS] at hR
    obtain ⟨x, hx, h⟩ := hR
    exact ⟨x, y, ⟨hx, hy⟩, h⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩; exact couple_mem_clsTimes.2 ⟨hx, hy⟩

private noncomputable def clsTimesEquiv (B : Set β) (A : Set α) : ↥(B ×ₐ A) ≃ A × B :=
  (Equiv.ofBijective
    (fun p : A × B => (⟨p.1.1 ↓ p.2.1, couple_mem_clsTimes.2 ⟨p.1.2, p.2.2⟩⟩ : ↥(B ×ₐ A)))
    ⟨fun p q h => by
      obtain ⟨h1, h2⟩ := couple_eq_couple_iff.1 (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2),
     fun ⟨R, hR⟩ => by
      obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 hR
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩⟩).symm

private theorem sm_clsTimes {A : Set α} {B : Set β} {A' : Set γ} {B' : Set δ} (hA : sm A A')
    (hB : sm B B') : sm (B ×ₐ A) (B' ×ₐ A') := by
  obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 hA
  obtain ⟨eB⟩ := sm_iff_nonempty_equiv.1 hB
  exact sm_of_equiv ((clsTimesEquiv B A).trans ((eA.prodCongr eB).trans (clsTimesEquiv B' A').symm))

private theorem sm_clsTimes_comm (A : Set α) (B : Set β) : sm (A ×ₐ B) (B ×ₐ A) :=
  sm_of_equiv ((clsTimesEquiv A B).trans ((Equiv.prodComm _ _).trans (clsTimesEquiv B A).symm))

private theorem n₀c_cardMul_n₀c (A : Set α) (B : Set β) :
    (n₀c A ×ᶜ n₀c B : Set (Set γ)) = nc γ (A ×ₐ B) := by
  ext ξ
  constructor
  · rintro ⟨A', B', ⟨hA, hB⟩, h⟩
    have hA' : sm A A' := n₀c_eq_n₀c_iff.1 hA
    have hB' : sm B B' := n₀c_eq_n₀c_iff.1 hB
    exact sm_trans h (sm_clsTimes (sm_symm hB') (sm_symm hA'))
  · intro h; exact ⟨A, B, ⟨rfl, rfl⟩, h⟩

private theorem cardMul_eq_empty_of_left {μ : Set (Set α)} (h : ∀ A, μ ≠ n₀c A)
    (ν : Set (Set β)) : (μ ×ᶜ ν : Set (Set γ)) = ∅ := by
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨hA, -⟩, -⟩
  exact h A hA

private theorem cardMul_eq_empty_of_right (μ : Set (Set α)) {ν : Set (Set β)}
    (h : ∀ B, ν ≠ n₀c B) : (μ ×ᶜ ν : Set (Set γ)) = ∅ := by
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨-, hB⟩, -⟩
  exact h B hB

private theorem empty_cardMul (ν : Set (Set β)) : ((∅ : Set (Set α)) ×ᶜ ν : Set (Set γ)) = ∅ :=
  cardMul_eq_empty_of_left (fun A h => n₀c_ne_empty A h.symm) ν

private theorem cardMul_empty (μ : Set (Set α)) : (μ ×ᶜ (∅ : Set (Set β)) : Set (Set γ)) = ∅ :=
  cardMul_eq_empty_of_right μ (fun A h => n₀c_ne_empty A h.symm)

private theorem adeqMul_nonempty {W : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (h : AdeqMul W μ ν) (A : Set α) (B : Set β) : (nc W (A ×ₐ B)).Nonempty := by
  rw [AdeqMul, n₀c_cardMul_n₀c] at h
  obtain ⟨f, hf⟩ := nc_nonempty_iff.1 h
  have hsub : A ×ₐ B ⊆ typ₁ μ ×ₐ typ₁ ν := by
    intro R hR
    obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 hR
    exact couple_mem_clsTimes.2 ⟨by rw [typ₁, typ₀_eq_univ]; trivial,
      by rw [typ₁, typ₀_eq_univ]; trivial⟩
  exact nc_nonempty_iff.2 ⟨f ∘ Set.inclusion hsub, hf.comp (Set.inclusion_injective hsub)⟩

private noncomputable def clsSigmaEquiv (K : Set (Set δ)) :
    ↥(clsSigma K) ≃ Σ X : K, ↥(X : Set δ) :=
  (Equiv.ofBijective (fun p : Σ X : K, ↥(X : Set δ) =>
      (⟨p.2.1 ↓ p.1.1, couple_mem_clsSigma.2 ⟨p.1.2, p.2.2⟩⟩ : ↥(clsSigma K)))
    ⟨fun p q h => by
      obtain ⟨h1, h2⟩ := couple_eq_couple_iff.1 (congrArg Subtype.val h)
      exact Sigma.subtype_ext (Subtype.ext h2) h1,
     fun ⟨R, hR⟩ => by
      obtain ⟨X, x, ⟨hX, hx⟩, rfl⟩ := mem_clsSigma.1 hR
      exact ⟨⟨⟨X, hX⟩, ⟨x, hx⟩⟩, rfl⟩⟩).symm

/-- `Σ'κ sm β × α` when `κ` has `Nc'β` members each with `Nc'α` members (by choice). -/
private theorem clsSigma_sm_clsTimes {K : Set (Set δ)} {A : Set α} {B : Set β}
    (hK : sm K B) (hA : ∀ X, X ∈ K → sm X A) : sm (clsSigma K) (A ×ₐ B) := by
  obtain ⟨eK⟩ := sm_iff_nonempty_equiv.1 hK
  have e : ∀ X : K, ↥(X : Set δ) ≃ A := fun X =>
    Classical.choice (sm_iff_nonempty_equiv.1 (hA X.1 X.2))
  exact sm_of_equiv ((clsSigmaEquiv K).trans ((Equiv.sigmaCongrRight e).trans
    ((Equiv.sigmaEquivProd _ _).trans ((eK.prodCongr (Equiv.refl _)).trans
      (clsTimesEquiv A B).symm))))

private theorem cardMul_of {μ : Set (Set α)} {ν : Set (Set β)} {A : Set α} {B : Set β}
    (hμ : μ = n₀c A) (hν : ν = n₀c B) : (μ ×ᶜ ν : Set (Set γ)) = nc γ (A ×ₐ B) := by
  subst hμ hν; exact n₀c_cardMul_n₀c A B

private theorem relProd_couple_apply {R : γ → α → Prop} {S : δ → β → Prop} {x : α} {y : β}
    (p : γ) (q : δ) : (R ⨾ ((x ↓ y) ⨾ S˘)) p q ↔ R p x ∧ S q y := by
  constructor
  · rintro ⟨m, hpm, n, hmn, hnq⟩
    obtain ⟨rfl, rfl⟩ := (couple_apply x y m n).1 hmn
    exact ⟨hpm, hnq⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x, h1, y, (couple_apply x y x y).2 ⟨rfl, rfl⟩, h2⟩

private theorem dpar_couple {R : γ → α → Prop} {S : δ → β → Prop} {x : α} {y : β} {a : γ} {b : δ}
    (ha : ∀ a', R a' x ↔ a' = a) (hb : ∀ b', S b' y ↔ b' = b) :
    R ⨾ ((x ↓ y) ⨾ S˘) = a ↓ b := by
  funext p q
  apply propext
  rw [relProd_couple_apply, ha, hb]
  exact (couple_apply a b p q).symm

private theorem desc_dpar {R : α → β → Prop} {S : γ → δ → Prop} {Q : β → γ → Prop}
    {ψ : (α → δ → Prop) → Prop} : Desc (R ∥ S) Q ψ ↔ ψ (R ⨾ (Q ⨾ S)) :=
  desc_of_unique fun P => dpar_iff R S P Q

private theorem fld_couple (x y : α) : fld (x ↓ y) = ι x ∪ ι y := by
  ext z
  simp only [fld, couple_apply, Set.mem_ofPred_eq, Set.mem_union, mem_unitCls]
  constructor
  · rintro ⟨w, ⟨h, -⟩ | ⟨-, h⟩⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨y, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨x, Or.inr ⟨rfl, h⟩⟩

private theorem dom_couple (x : α) (y : β) : dom (x ↓ y) = ι x := by
  ext z; exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨y, h, rfl⟩⟩

private theorem codom_couple (x : α) (y : β) : codom (x ↓ y) = ι y := by
  ext z; exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨x, rfl, h⟩⟩

private theorem cres_eq_of_smbar {T : α → β → Prop} {X : Set α} {Y : Set β} (hT : T ∈ smbar X Y) :
    T ↾ Y = T := by
  funext x y; apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, by rw [(mem_smbar_iff.1 hT).2]; exact ⟨x, h⟩⟩⟩

private theorem dom_rcup_couple (x y : α) (A B : Set α) : dom (x ↓ A ⊍ y ↓ B) = ι x ∪ ι y := by
  ext z
  constructor
  · rintro ⟨w, ⟨h, -⟩ | ⟨h, -⟩⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨A, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨B, Or.inr ⟨h, rfl⟩⟩

private theorem exists_disjoint_copies (A B : Set α) :
    ∃ G H : Set (Set α), (sm G A ∧ sm H B) ∧ G ∩ H = Λ := by
  obtain ⟨f, hf⟩ := exists_inj_sum_set α
  refine ⟨(f ∘ Sum.inl) '' A, (f ∘ Sum.inr) '' B, ⟨?_, ?_⟩, ?_⟩
  · exact sm_of_injOn (f ∘ Sum.inl) (fun x y _ _ h => Sum.inl_injective (hf h))
      fun z => ⟨fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩⟩
  · exact sm_of_injOn (f ∘ Sum.inr) (fun x y _ _ h => Sum.inr_injective (hf h))
      fun z => ⟨fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩⟩
  · rw [inter_eq_null_iff, Set.disjoint_left]
    rintro _ ⟨x, -, rfl⟩ ⟨y, -, e⟩
    exact Sum.inr_ne_inl (hf e)

private theorem clsTimes_sub_left {A A' : Set α} {B B' : Set β} (h : A ×ₐ B ⊆ A' ×ₐ B')
    (hA : A.Nonempty) : B ⊆ B' := by
  intro x hx
  obtain ⟨y, hy⟩ := hA
  exact (couple_mem_clsTimes.1 (h (couple_mem_clsTimes.2 ⟨hx, hy⟩))).1

private theorem clsTimes_sub_right {A A' : Set α} {B B' : Set β} (h : A ×ₐ B ⊆ A' ×ₐ B')
    (hB : B.Nonempty) : A ⊆ A' := by
  intro y hy
  obtain ⟨x, hx⟩ := hB
  exact (couple_mem_clsTimes.1 (h (couple_mem_clsTimes.2 ⟨hx, hy⟩))).2

private theorem inner_add_eq {W : Type*} {A : Set α} {B : Set β} (h : AdeqAdd W (n₀c A) (n₀c B)) :
    ∃ X : Set W, sm X (A +ₐ B) ∧ (n₀c A +ᶜ n₀c B : Set (Set W)) = n₀c X := by
  obtain ⟨X, hX⟩ := h.nc_nonempty A B
  exact ⟨X, hX, by rw [n₀c_cardAdd_n₀c]; exact nc_eq_n₀c_of_mem hX⟩

private theorem inner_mul_eq {W : Type*} {A : Set α} {B : Set β} (h : AdeqMul W (n₀c A) (n₀c B)) :
    ∃ X : Set W, sm X (A ×ₐ B) ∧ (n₀c A ×ᶜ n₀c B : Set (Set W)) = n₀c X := by
  obtain ⟨X, hX⟩ := adeqMul_nonempty h A B
  exact ⟨X, hX, by rw [n₀c_cardMul_n₀c]; exact nc_eq_n₀c_of_mem hX⟩

private theorem sm_clsTimes_distrib (A : Set α) (B : Set β) (G : Set δ) :
    sm ((B +ₐ G) ×ₐ A) ((B ×ₐ A) +ₐ (G ×ₐ A)) :=
  sm_of_equiv ((clsTimesEquiv (B +ₐ G) A).trans (((Equiv.refl _).prodCongr
    (clsSumEquiv B G)).trans ((Equiv.prodSumDistrib _ _ _).trans
      (((clsTimesEquiv B A).symm.sumCongr (clsTimesEquiv G A).symm).trans
        (clsSumEquiv _ _).symm))))

private theorem sm_clsTimes_assoc (A : Set α) (B : Set β) (G : Set δ) :
    sm (A ×ₐ B ×ₐ G) (A ×ₐ (B ×ₐ G)) :=
  sm_of_equiv ((clsTimesEquiv (A ×ₐ B) G).trans (((Equiv.refl _).prodCongr
    (clsTimesEquiv A B)).trans ((Equiv.prodAssoc _ _ _).symm.trans
      (((clsTimesEquiv B G).symm.prodCongr (Equiv.refl _)).trans
        (clsTimesEquiv A (B ×ₐ G)).symm))))

private theorem coupleR_img_sm (z : δ) (A : Set α) : sm (coupleR z ʻʻ A) A :=
  sm_of_injOn (fun x => x ↓ z) (fun x y _ _ h => (couple_eq_couple_iff.1 h).1) fun _ => Iff.rfl

private theorem clsTimes_unit_sm (A : Set α) (z : δ) : sm (ι z ×ₐ A) A :=
  sm_of_equiv ((clsTimesEquiv (ι z) A).trans (by
    rw [unitCls_eq_singleton]; exact (Equiv.prodCongr (Equiv.refl _) (Equiv.Set.singleton.{1} z)).trans
      (Equiv.prodPUnit.{0} _)))

private theorem clsTimes_empty (A : Set α) : A ×ₐ (∅ : Set β) = ∅ := by
  ext R
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨x, y, ⟨hx, -⟩, -⟩ := mem_clsTimes.1 h
  exact hx

private theorem coupleR_cres_oneCls (z : δ) (X : Set α) :
    (coupleR z : (α → δ → Prop) → α → Prop) ↾ X ∈ arrow one Cls :=
  mem_arrow_one_Cls.2 fun u v x ⟨⟨hu, _⟩, ⟨hv, _⟩⟩ =>
    (show u = _ from hu).trans (show v = _ from hv).symm

private theorem subset_codom_coupleR (z : δ) (X : Set α) :
    X ⊆ codom (coupleR z : (α → δ → Prop) → α → Prop) :=
  fun x _ => ⟨x ↓ z, rfl⟩

end Helpers113

/-!
## [✱113] On the arithmetical product of two classes or of two cardinals

*(Vol. 2, p. 105)*

> *Summary of* *113.
>
> In this number, we give a definition of multiplication which can be extended to any finite number of factors, but not to an infinite number of factors. We define first the arithmetical class-product of two classes \(\alpha\) and \(\beta\), and thence the product of two cardinals \(\mu\) and \(\nu\) as the number of terms in the product of \(\alpha\) and \(\beta\) when \(\alpha\) has \(\mu\) terms and \(\beta\) has \(\nu\) terms. In *114, we shall give a definition of multiplication which is not restricted to a finite number of factors. The advantages of the definition to be given in this number are, that it does not require the factors to be of the same type, and that it enables us to multiply a class by itself without (as in logical addition and multiplication) simply reproducing the class in question. The disadvantage of the definition in this number is the impossibility of extending it to an infinite number of factors.
>
> …

**Lean reading.** `β × α` is `B ×ₐ A` (`clsTimes`, PM's order: the couples `x ↓ y` with `x ∈ α`,
`y ∈ β`), compared with Lean's `A × B` (`clsTimesEquiv`); `α ↓,,` is the relation `coupleImg A`
and `α ↓,, y` is `opImg couple A y`; `↓z''α` is `coupleR z ʻʻ A`; `×α`, `α×` are the relations
`graph (· ×ₐ A)`, `graph (A ×ₐ ·)`; `R ‖ S̆` is `R ∥ S˘`. `μ ×_c ν` is `μ ×ᶜ ν` with its actual type
implicit; the arguments `Nc'α` of `×_c` and `+_c` are `n₀c A` (✱113·04·05, ✱110·03·04);
inner arithmetical components and the constants `1`, `2` get adequate types (IIT), `0` none;
the descriptions `R'z`, `S'w`, `(R ‖ S̆)'(z ↓ w)`, … are kept with `Desc`. `NC` is treated as in
✱110. `Mult ax` is at the type of the correlators used by PM's demonstration (✱112·24). In
✱113·33·34 the real variables `μ`, `ν` occur in two relative types; the second occurrences are
`sm''μ`, `sm''ν`. The e-text prints `Hp ✱133·144` (✱113·147), `β × a` (✱113·15),
`γ x δ` (✱113·221) and `x α` (✱113·44); these are read as transcription errors. ✱113·31·32 are
false as printed when `μ = Λ` (then `κ = Λ`); the hypothesis
`∃!μ` is added and the counterexample is proved.

**Status.** proved (all propositions; ✱113·147·15·201·203·204·221·23·24·261·33·34·42·421·43·44·47·491·52·53·531·54·602·62·621·66·67·671 proved (reading), ✱113·31·32 proved (corrected), see their docstrings)
-/

/-- ✱113·02 (Df). \(\beta \times \alpha = sʻ\alpha \downarrow_{,,} ʻʻ\beta \quad\text{Df}\)

`β × α` is `B ×ₐ A` (PM's order), the couples `x ↓ y` with `x ∈ α`, `y ∈ β`; `α ↓,,` is the
relation `coupleImg A` of `α ↓,, y` to `y`. -/
theorem pm113_02 {A : Set α} {B : Set β} : B ×ₐ A = sumCls (coupleImg A ʻʻ B) := rfl

/-- ✱113·03 (Df). \(\mu \times _{c} \nu = \hat{\xi} \{(\exists \alpha , \beta ) . \mu = \text{N}_{0}\text{c}ʻ\alpha . \nu \text{N}_{0}\text{c}ʻ\beta . \xi \text{ sm } (\alpha \times \beta )\} \quad\text{Df}\)

(The e-text omits the `=` of `ν = N₀c'β`: a transcription error.) -/
theorem pm113_03 {μ : Set (Set α)} {ν : Set (Set β)} : (μ ×ᶜ ν : Set (Set γ)) =
    {ξ | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm ξ (A ×ₐ B)} := rfl

/-- ✱113·04 (Df). \(\text{Nc}ʻ\beta \times _{c} \mu = \text{N}_{0}\text{c}ʻ\beta \times _{c} \mu \quad\text{Df}\)

A rule of translation (normal adjustment): an argument `Nc'β` of `×_c` is written `n₀c B`. -/
theorem pm113_04 {B : Set β} {μ : Set (Set α)} : (n₀c B ×ᶜ μ : Set (Set γ)) = n₀c B ×ᶜ μ := rfl

/-- ✱113·05 (Df). \(\mu \times _{c} \text{Nc}ʻ\alpha = \mu \times _{c} \text{N}_{0}\text{c}ʻ\alpha \quad\text{Df}\)

A rule of translation (normal adjustment), as ✱113·04. -/
theorem pm113_05 {A : Set α} {μ : Set (Set β)} : (μ ×ᶜ n₀c A : Set (Set γ)) = μ ×ᶜ n₀c A := rfl

/-- ✱113·1. \(\vdash . \beta \times \alpha = sʻ\alpha \downarrow_{,,} ʻʻ\beta \quad[(*113·02)]\) -/
theorem pm113_1 {A : Set α} {B : Set β} : B ×ₐ A = sumCls (coupleImg A ʻʻ B) := rfl

/-- ✱113·101. \(\vdash : R \in \beta \times \alpha . \equiv . (\exists x, y) . x \in \alpha . y \in \beta . R = x\downarrow y \quad[*40·7 . *113·1]\) -/
theorem pm113_101 {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ∈ B ×ₐ A ↔ ∃ x y, (x ∈ A ∧ y ∈ B) ∧ R = x ↓ y := mem_clsTimes

/-- ✱113·102. \(\vdash : y \in \beta . \supset . \alpha \downarrow_{,,} y = (\alpha \uparrow \beta )_{\Delta }ʻ\iota ʻy\)

`α ↓,, y` is `opImg couple A y` (✱38·03), `(α ↑ β)_Δ'ι'y` is `sel (cross A B) (ι y)`. -/
theorem pm113_102 {A : Set α} {B : Set β} {y : β} :
    y ∈ B → opImg couple A y = sel (cross A B) (ι y) := by
  intro hy
  ext M
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, codom_couple x y⟩
    · rintro a b z ⟨h1, h2⟩; exact h1.1.trans h2.1.symm
    · rintro a b ⟨rfl, rfl⟩; exact ⟨hx, hy⟩
  · intro h
    obtain ⟨⟨h1, h2⟩, h3⟩ := mem_sel_iff.1 h
    have : y ∈ codom M := by rw [h3]; rfl
    obtain ⟨x, hxy⟩ := this
    refine ⟨x, (h2 x y hxy).1, ?_⟩
    funext a b
    apply propext
    constructor
    · intro hab
      have hb : b ∈ codom M := ⟨a, hab⟩
      rw [h3] at hb
      have hb' : b = y := hb
      subst hb'
      exact ⟨mem_arrow_one_Cls.1 h1 a x b ⟨hab, hxy⟩, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact hxy

/-- ✱113·103. \(\vdash . \alpha \downarrow_{,,} ʻʻ\beta = (\alpha \uparrow \beta )_{\Delta }ʻʻ\iotaʻʻ\beta = (\alpha \uparrow \beta ) \unicode{x21A7} ʻʻ\beta \quad[*113·102 . *85·52]\)

`(α ↑ β)_Δ''ι''β` is `selRel (cross A B) ʻʻ (iota ʻʻ B)`, `(α ↑ β)↧''β` is
`opL downCls (cross A B) ʻʻ B`; the chain is the conjunction of its links. -/
theorem pm113_103 {A : Set α} {B : Set β} :
    (coupleImg A ʻʻ B : Set (Set (α → β → Prop))) = selRel (cross A B) ʻʻ (iota ʻʻ B) ∧
      selRel (cross A B) ʻʻ (iota ʻʻ B) = opL downCls (cross A B) ʻʻ B := by
  have h1 : ∀ y, y ∈ B → cross A B ↧ y = opImg couple A y := by
    intro y hy
    show coupleR y ʻʻ refs (cross A B) y = opR couple y ʻʻ A
    congr 1
    ext x; exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩
  constructor
  · ext u
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨ι y, ⟨y, hy, rfl⟩, pm113_102 hy⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, (pm113_102 hy).symm⟩
  · ext u
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, ((h1 y hy).trans (pm113_102 hy)).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨ι y, ⟨y, hy, rfl⟩, (h1 y hy).trans (pm113_102 hy)⟩

/-- ✱113·104. \(\vdash . \text{E}! \alpha \downarrow_{,,} ʻy \quad[*38·12]\)

PM proves that the descriptive function exists, so the statement keeps `E!` (Basic §5). -/
theorem pm113_104 {A : Set α} {y : β} :
    EDesc (coupleImg A : Set (α → β → Prop) → β → Prop) y := EDesc_graph _ _

/-- ✱113·105. \(\vdash : \exists ! \alpha . \supset . \alpha \downarrow_{,,} \in 1 \rightarrow 1\) -/
theorem pm113_105 {A : Set α} :
    A.Nonempty → (coupleImg A : Set (α → β → Prop) → β → Prop) ∈ arrow one one := by
  rintro ⟨a, ha⟩
  refine mem_arrow_one_one.2 ⟨fun u v y ⟨h1, h2⟩ => (show u = _ from h1).trans
    (show v = _ from h2).symm, fun u y y' ⟨h1, h2⟩ => ?_⟩
  have : a ↓ y ∈ u := by rw [show u = _ from h1]; exact ⟨a, ha, rfl⟩
  rw [show u = _ from h2] at this
  obtain ⟨b, -, e⟩ := this
  exact (couple_eq_couple_iff.1 e).2

/-- ✱113·106. \(\vdash : x \in \alpha . y \in \beta . \supset . x \downarrow y \in \beta \times \alpha \quad[*113·101]\) -/
theorem pm113_106 {A : Set α} {B : Set β} {x : α} {y : β} :
    x ∈ A ∧ y ∈ B → x ↓ y ∈ B ×ₐ A := couple_mem_clsTimes.2

/-- ✱113·107. \(\vdash : \exists ! \alpha . \exists ! \beta . \supset . \exists ! \beta \times \alpha \quad [*113·106]\) -/
theorem pm113_107 {A : Set α} {B : Set β} : A.Nonempty ∧ B.Nonempty → (B ×ₐ A).Nonempty :=
  fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ => ⟨x ↓ y, couple_mem_clsTimes.2 ⟨hx, hy⟩⟩

/-- ✱113·11. \(\vdash : \exists ! \alpha . \supset . \alpha \downarrow_{,,}ʻʻ\beta \in \text{Nc}ʻ\beta : (y) . \alpha \downarrow_{,,} y \in \text{Nc}ʻ\alpha\)

The colon makes the proposition a product: `∃!α ⊃ α↓,,''β ∈ Nc'β`, and `(y) . α↓,,y ∈ Nc'α`.
The attributive `Nc'β`, `Nc'α` are in the types of `α↓,,''β` and `α↓,,y`. -/
theorem pm113_11 {A : Set α} {B : Set β} :
    (A.Nonempty → (coupleImg A ʻʻ B : Set (Set (α → β → Prop))) ∈ nc (Set (α → β → Prop)) B) ∧
      ∀ y : β, opImg couple A y ∈ nc (α → β → Prop) A := by
  refine ⟨fun hA => ?_, fun y => ?_⟩
  · have h1 := mem_arrow_one_one.1 (pm113_105 (β := β) hA)
    exact sm_of_injOn (fun y => opImg couple A y) (fun y y' _ _ h => h1.2 _ y y' ⟨rfl, h⟩)
      fun _ => Iff.rfl
  · exact sm_of_injOn (fun x => x ↓ y) (fun x x' _ _ h => (couple_eq_couple_iff.1 h).1)
      fun _ => Iff.rfl

/-- ✱113·111. \(\vdash . \alpha \downarrow_{,,} ʻʻ\beta \in \text{Cls}^{2} \text{excl} \quad[*113·103 . *85·55]\) -/
theorem pm113_111 {A : Set α} {B : Set β} :
    (coupleImg A ʻʻ B : Set (Set (α → β → Prop))) ∈ Cls2excl := by
  rintro _ _ ⟨⟨⟨y, hy, rfl⟩, ⟨y', hy', rfl⟩⟩, hne⟩
  rw [inter_eq_null_iff, Set.disjoint_left]
  rintro _ ⟨x, -, rfl⟩ ⟨x', -, e⟩
  obtain ⟨-, rfl⟩ := couple_eq_couple_iff.1 e
  exact hne rfl

/-- ✱113·112. \(\vdash : \alpha = \Lambda . \exists ! \beta . \supset . \alpha \downarrow_{,,} ʻʻ\beta = \iota ʻ\Lambda\) -/
theorem pm113_112 {A : Set α} {B : Set β} :
    A = Λ ∧ B.Nonempty → (coupleImg A ʻʻ B : Set (Set (α → β → Prop))) = ι Λ := by
  rintro ⟨rfl, ⟨y, hy⟩⟩
  ext u
  rw [mem_unitCls, Null_eq_empty, Null_eq_empty]
  constructor
  · rintro ⟨y', -, rfl⟩
    ext R; exact ⟨fun ⟨x, hx, _⟩ => hx.elim, fun h => h.elim⟩
  · rintro rfl
    refine ⟨y, hy, ?_⟩
    ext R; exact ⟨fun h => h.elim, fun ⟨x, hx, _⟩ => hx.elim⟩

/-- ✱113·113. \(\vdash : \beta = \Lambda . \supset . \alpha \downarrow_{,,} ʻʻ\beta = \Lambda \quad[*37·29]\) -/
theorem pm113_113 {A : Set α} {B : Set β} :
    B = Λ → (coupleImg A ʻʻ B : Set (Set (α → β → Prop))) = Λ := by
  rintro rfl
  rw [Null_eq_empty, Null_eq_empty]
  ext u; exact ⟨fun ⟨_, h, _⟩ => h.elim, fun h => h.elim⟩

/-- ✱113·114. \(\vdash \colon\ldotp \alpha = \Lambda .\lor.\beta = \Lambda : \equiv .\beta \times \alpha = \Lambda \quad[*113·1·112·113·107.*53·24]\) -/
theorem pm113_114 {A : Set α} {B : Set β} : A = Λ ∨ B = Λ ↔ B ×ₐ A = Λ := by
  rw [Null_eq_empty, Null_eq_empty, Null_eq_empty]
  constructor
  · rintro (rfl | rfl) <;> ext R <;> simp only [mem_clsTimes, Set.mem_empty_iff_false,
      iff_false] <;> rintro ⟨x, y, ⟨hx, hy⟩, -⟩
    · exact hx
    · exact hy
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hne
    have : x ↓ y ∈ B ×ₐ A := couple_mem_clsTimes.2 ⟨hx, hy⟩
    rw [h] at this; exact this

/-- ✱113·115. \(\vdash . \dot{s} ʻ(\beta \times \alpha ) = \alpha \uparrow \beta\) -/
theorem pm113_115 {A : Set α} {B : Set β} : sumRel (B ×ₐ A) = cross A B := by
  funext x y
  apply propext
  constructor
  · rintro ⟨R, hR, hxy⟩
    obtain ⟨a, b, ⟨ha, hb⟩, rfl⟩ := mem_clsTimes.1 hR
    obtain ⟨rfl, rfl⟩ := (couple_apply a b x y).1 hxy
    exact ⟨ha, hb⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x ↓ y, couple_mem_clsTimes.2 ⟨hx, hy⟩, (couple_apply x y x y).2 ⟨rfl, rfl⟩⟩

/-- ✱113·116. \[\begin{aligned}&\vdash : \exists ! \beta . \supset . sʻ\text{D}ʻʻ(\beta \times \alpha ) = \alpha : \exists ! \alpha . \supset . sʻ\text{ᗡ}ʻʻ(\beta \times \alpha ) = \beta \\ &[*113·115 . *41·43·44. *35·85·86]\end{aligned}\]

The colon makes the proposition a product of two implications. -/
theorem pm113_116 {A : Set α} {B : Set β} :
    (B.Nonempty → sumCls (D ʻʻ (B ×ₐ A)) = A) ∧ (A.Nonempty → sumCls (Dcnv ʻʻ (B ×ₐ A)) = B) := by
  constructor
  · rintro ⟨y, hy⟩
    ext x
    constructor
    · rintro ⟨_, ⟨R, hR, rfl⟩, hx⟩
      obtain ⟨a, b, ⟨ha, -⟩, rfl⟩ := mem_clsTimes.1 hR
      rw [dom_couple] at hx; rw [mem_unitCls.1 hx]; exact ha
    · intro hx
      exact ⟨_, ⟨x ↓ y, couple_mem_clsTimes.2 ⟨hx, hy⟩, rfl⟩, by rw [dom_couple]; rfl⟩
  · rintro ⟨x, hx⟩
    ext y
    constructor
    · rintro ⟨_, ⟨R, hR, rfl⟩, hy⟩
      obtain ⟨a, b, ⟨-, hb⟩, rfl⟩ := mem_clsTimes.1 hR
      rw [codom_couple] at hy; rw [mem_unitCls.1 hy]; exact hb
    · intro hy
      exact ⟨_, ⟨x ↓ y, couple_mem_clsTimes.2 ⟨hx, hy⟩, rfl⟩, by rw [codom_couple]; rfl⟩

/-- ✱113·117. \[\begin{aligned}&\vdash \colon\ldotp \alpha = \Lambda . \lor . \beta = \Lambda : \supset . sʻ\text{D}ʻʻ(\beta \times \alpha ) = \Lambda . sʻ\text{ᗡ}ʻʻ(\beta \times \alpha ) = \Lambda\\ &[*113·115 . *41·43·44. *35·88]\end{aligned}\] -/
theorem pm113_117 {A : Set α} {B : Set β} :
    A = Λ ∨ B = Λ → sumCls (D ʻʻ (B ×ₐ A)) = Λ ∧ sumCls (Dcnv ʻʻ (B ×ₐ A)) = Λ := by
  intro h
  rw [pm113_114.1 h]
  simp only [Null_eq_empty]
  refine ⟨?_, ?_⟩ <;> rw [Set.eq_empty_iff_forall_notMem] <;> rintro x ⟨_, ⟨R, hR, -⟩, -⟩ <;>
    exact hR

/-- ✱113·118. \(\vdash . sʻ\text{D}ʻʻ(\beta \times \alpha ) \subset \alpha . sʻ\text{ᗡ}ʻʻ(\beta \times \alpha ) \subset \beta \quad[*113·116·117]\) -/
theorem pm113_118 {A : Set α} {B : Set β} :
    sumCls (D ʻʻ (B ×ₐ A)) ⊆ A ∧ sumCls (Dcnv ʻʻ (B ×ₐ A)) ⊆ B := by
  constructor
  · rintro x ⟨_, ⟨R, hR, rfl⟩, hx⟩
    obtain ⟨a, b, ⟨ha, -⟩, rfl⟩ := mem_clsTimes.1 hR
    rw [dom_couple] at hx; rw [mem_unitCls.1 hx]; exact ha
  · rintro y ⟨_, ⟨R, hR, rfl⟩, hy⟩
    obtain ⟨a, b, ⟨-, hb⟩, rfl⟩ := mem_clsTimes.1 hR
    rw [codom_couple] at hy; rw [mem_unitCls.1 hy]; exact hb

/-- ✱113·12. \(\vdash : \exists ! \alpha . \supset . \alpha \downarrow_{,,} ʻʻ\beta \in \text{Nc}ʻ\beta \cap \text{Cl excl}ʻ\text{Nc}ʻ\alpha \quad[*113·11·111]\)

`Cl excl'Nc'α`: the `Nc'α` is in the type of the members of `α↓,,''β` (significance). -/
theorem pm113_12 {A : Set α} {B : Set β} :
    A.Nonempty → (coupleImg A ʻʻ B : Set (Set (α → β → Prop))) ∈
      nc (Set (α → β → Prop)) B ∩ clExcl (nc (α → β → Prop) A) := by
  intro hA
  refine ⟨(pm113_11.1 hA), pm113_111, ?_⟩
  rintro _ ⟨y, -, rfl⟩
  exact (pm113_11 (B := B)).2 y

/-- ✱113·121. \(\vdash . \Sigma ʻ\alpha \downarrow_{,,} ʻʻ\beta \text{ sm } \beta \times \alpha \quad[*112·15 . *113·111·1]\) -/
theorem pm113_121 {A : Set α} {B : Set β} : sm (clsSigma (coupleImg A ʻʻ B)) (B ×ₐ A) := by
  let P : Set (α × β) := {p | p.1 ∈ A ∧ p.2 ∈ B}
  have h1 : sm (clsSigma (coupleImg A ʻʻ B)) P := by
    refine sm_of_injOn (fun p : α × β => (p.1 ↓ p.2) ↓ opImg couple A p.2) ?_ ?_
    · intro p q _ _ h
      obtain ⟨h1, -⟩ := couple_eq_couple_iff.1 h
      obtain ⟨e1, e2⟩ := couple_eq_couple_iff.1 h1
      exact Prod.ext e1 e2
    · intro R
      rw [mem_clsSigma]
      constructor
      · rintro ⟨_, _, ⟨⟨y, hy, rfl⟩, x, hx, rfl⟩, rfl⟩
        exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
        exact ⟨_, _, ⟨⟨y, hy, rfl⟩, x, hx, rfl⟩, rfl⟩
  have h2 : sm (B ×ₐ A) P := by
    refine sm_of_injOn (fun p : α × β => p.1 ↓ p.2) ?_ ?_
    · intro p q _ _ h
      obtain ⟨e1, e2⟩ := couple_eq_couple_iff.1 h
      exact Prod.ext e1 e2
    · intro R
      rw [mem_clsTimes]
      constructor
      · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨x, y, ⟨hx, hy⟩, rfl⟩
  exact sm_trans h1 (sm_symm h2)

/-- ✱113·122. \[\begin{aligned}&\vdash : R \upharpoonright \gamma , S \upharpoonright \delta \in \text{Cls} \rightarrow 1 . \gamma \subset \text{ᗡ}ʻR . \delta \subset \text{ᗡ}ʻS . \supset . (R \parallel \breve{S} ) \upharpoonright (\delta \times \gamma ) \in 1 \rightarrow 1\\ &[*74·773. *113·118]\end{aligned}\]

`R ↾ γ, S ↾ δ ∈ Cls → 1` is a product (the two relations are of different types). `S̆` is `S˘`. -/
theorem pm113_122 {R : γ → α → Prop} {S : δ → β → Prop} {G : Set α} {H : Set β} :
    ((R ↾ G ∈ arrow Cls one ∧ S ↾ H ∈ arrow Cls one) ∧ G ⊆ codom R) ∧ H ⊆ codom S →
      (R ∥ S˘) ↾ (H ×ₐ G) ∈ arrow one one := by
  rintro ⟨⟨⟨hR, hS⟩, hG⟩, hH⟩
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro P P' Q ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    rw [(dpar_iff _ _ _ _).1 h1, (dpar_iff _ _ _ _).1 h2]
  · rintro P Q Q' ⟨⟨h1, hQ⟩, ⟨h2, hQ'⟩⟩
    obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 hQ
    obtain ⟨x', y', ⟨hx', hy'⟩, rfl⟩ := mem_clsTimes.1 hQ'
    have e := ((dpar_iff _ _ _ _).1 h1).symm.trans ((dpar_iff _ _ _ _).1 h2)
    obtain ⟨p, hp⟩ := hG hx
    obtain ⟨q, hq⟩ := hH hy
    have hpq : (R ⨾ ((x ↓ y) ⨾ S˘)) p q := (relProd_couple_apply p q).2 ⟨hp, hq⟩
    rw [e, relProd_couple_apply] at hpq
    have ex : x = x' := mem_arrow_Cls_one.1 hR p x x' ⟨⟨hp, hx⟩, ⟨hpq.1, hx'⟩⟩
    have ey : y = y' := mem_arrow_Cls_one.1 hS q y y' ⟨⟨hq, hy⟩, ⟨hpq.2, hy'⟩⟩
    rw [ex, ey]

/-- ✱113·123. \[\begin{aligned}\vdash : R \upharpoonright \gamma , S \upharpoonright \delta \in 1 \rightarrow \text{Cls}. \gamma &\subset \text{ᗡ}ʻR . \delta \subset \text{ᗡ}ʻS . z \in \gamma . w \in \delta . \supset .\\ &(R \parallel \breve{S} )ʻ(z \downarrow w) = (Rʻz) \downarrow (Sʻw) \quad[*55·61]\end{aligned}\]

`(R ‖ S̆)'(z ↓ w) = (R'z) ↓ (S'w)`: three descriptions, the first with the largest scope. -/
theorem pm113_123 {R : γ → α → Prop} {S : δ → β → Prop} {G : Set α} {H : Set β} {z : α} {w : β} :
    ((((R ↾ G ∈ arrow one Cls ∧ S ↾ H ∈ arrow one Cls) ∧ G ⊆ codom R) ∧ H ⊆ codom S) ∧ z ∈ G) ∧
        w ∈ H →
      Desc (R ∥ S˘) (z ↓ w) (fun P => Desc R z (fun a => Desc S w (fun b => P = a ↓ b))) := by
  rintro ⟨⟨⟨⟨⟨hR, hS⟩, hG⟩, hH⟩, hz⟩, hw⟩
  obtain ⟨a, ha⟩ := hG hz
  obtain ⟨b, hb⟩ := hH hw
  have ua : ∀ a', R a' z ↔ a' = a := fun a' =>
    ⟨fun h => mem_arrow_one_Cls.1 hR a' a z ⟨⟨h, hz⟩, ⟨ha, hz⟩⟩, fun e => e ▸ ha⟩
  have ub : ∀ b', S b' w ↔ b' = b := fun b' =>
    ⟨fun h => mem_arrow_one_Cls.1 hS b' b w ⟨⟨h, hw⟩, ⟨hb, hw⟩⟩, fun e => e ▸ hb⟩
  rw [desc_dpar, desc_of_unique ua, desc_of_unique ub]
  exact dpar_couple ua ub

/-- ✱113·124. \[\begin{aligned}\vdash : R \upharpoonright \gamma , S \upharpoonright \delta \in 1 \rightarrow \text{Cls}. \gamma &\subset \text{ᗡ}ʻR . \delta \subset \text{ᗡ}ʻS . w \in \delta . \supset .\\ &(R \parallel \breve{S} )ʻʻ\gamma \downarrow_{,,} w = (Rʻʻ\gamma ) \downarrow_{,,} (Sʻw)\end{aligned}\]

`(R ‖ S̆)''γ↓,,w = (R''γ) ↓,, (S'w)`; the description `S'w` has the smallest scope. -/
theorem pm113_124 {R : γ → α → Prop} {S : δ → β → Prop} {G : Set α} {H : Set β} {w : β} :
    ((((R ↾ G ∈ arrow one Cls ∧ S ↾ H ∈ arrow one Cls) ∧ G ⊆ codom R) ∧ H ⊆ codom S) ∧ w ∈ H) →
      Desc S w (fun b => (R ∥ S˘) ʻʻ opImg couple G w = opImg couple (R ʻʻ G) b) := by
  rintro ⟨⟨⟨⟨hR, hS⟩, hG⟩, hH⟩, hw⟩
  obtain ⟨b, hb⟩ := hH hw
  have ub : ∀ b', S b' w ↔ b' = b := fun b' =>
    ⟨fun h => mem_arrow_one_Cls.1 hS b' b w ⟨⟨h, hw⟩, ⟨hb, hw⟩⟩, fun e => e ▸ hb⟩
  have ua : ∀ x, x ∈ G → ∀ a, R a x → ∀ a', R a' x ↔ a' = a := fun x hx a ha a' =>
    ⟨fun h => mem_arrow_one_Cls.1 hR a' a x ⟨⟨h, hx⟩, ⟨ha, hx⟩⟩, fun e => e ▸ ha⟩
  rw [desc_of_unique ub]
  ext P
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hP⟩
    obtain ⟨a, ha⟩ := hG hx
    rw [(dpar_iff _ _ _ _).1 hP, dpar_couple (ua x hx a ha) ub]
    exact ⟨a, ⟨x, hx, ha⟩, rfl⟩
  · rintro ⟨a, ⟨x, hx, ha⟩, rfl⟩
    exact ⟨x ↓ w, ⟨x, hx, rfl⟩, (dpar_iff _ _ _ _).2 (dpar_couple (ua x hx a ha) ub).symm⟩

/-- ✱113·125. \[\begin{aligned}\vdash : R \upharpoonright \gamma , S \upharpoonright \delta \in 1 \rightarrow &\text{Cls}. \gamma \subset \text{ᗡ}ʻR . \delta \subset \text{ᗡ}ʻS . \supset .\\ &(R \parallel \breve{S} )_{\in }ʻʻ\gamma \downarrow_{,,} ʻʻ\delta = (Rʻʻ\gamma ) \downarrow_{,,} ʻʻ(Sʻʻ\delta ) \quad[*113·124]\end{aligned}\] -/
theorem pm113_125 {R : γ → α → Prop} {S : δ → β → Prop} {G : Set α} {H : Set β} :
    ((R ↾ G ∈ arrow one Cls ∧ S ↾ H ∈ arrow one Cls) ∧ G ⊆ codom R) ∧ H ⊆ codom S →
      imgRel (R ∥ S˘) ʻʻ (coupleImg G ʻʻ H) = coupleImg (R ʻʻ G) ʻʻ (S ʻʻ H) := by
  rintro ⟨⟨⟨hR, hS⟩, hG⟩, hH⟩
  have key : ∀ w, w ∈ H → ∃ b, S b w ∧
      (R ∥ S˘) ʻʻ opImg couple G w = opImg couple (R ʻʻ G) b := by
    intro w hw
    obtain ⟨b, hb⟩ := hH hw
    have := pm113_124 (R := R) ⟨⟨⟨⟨hR, hS⟩, hG⟩, hH⟩, hw⟩
    have ub : ∀ b', S b' w ↔ b' = b := fun b' =>
      ⟨fun h => mem_arrow_one_Cls.1 hS b' b w ⟨⟨h, hw⟩, ⟨hb, hw⟩⟩, fun e => e ▸ hb⟩
    rw [desc_of_unique ub] at this
    exact ⟨b, hb, this⟩
  ext u
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨b, hb, e⟩ := key w hw
    exact ⟨b, ⟨w, hw, hb⟩, e⟩
  · rintro ⟨b, ⟨w, hw, hb⟩, rfl⟩
    obtain ⟨b', hb', e⟩ := key w hw
    have : b = b' := mem_arrow_one_Cls.1 hS b b' w ⟨⟨hb, hw⟩, ⟨hb', hw⟩⟩
    subst this
    exact ⟨_, ⟨w, hw, rfl⟩, e.symm⟩

/-- ✱113·126. \(\vdash : \text{Hp} *113·125 . \supset . (R \parallel \breve{S} )ʻʻ(\delta \times \gamma ) = (Sʻʻ\delta ) \times (Rʻʻ\gamma )\)

`Hp ✱113·125` is its hypothesis. -/
theorem pm113_126 {R : γ → α → Prop} {S : δ → β → Prop} {G : Set α} {H : Set β} :
    ((R ↾ G ∈ arrow one Cls ∧ S ↾ H ∈ arrow one Cls) ∧ G ⊆ codom R) ∧ H ⊆ codom S →
      (R ∥ S˘) ʻʻ (H ×ₐ G) = (S ʻʻ H) ×ₐ (R ʻʻ G) := by
  rintro ⟨⟨⟨hR, hS⟩, hG⟩, hH⟩
  have ua : ∀ x, x ∈ G → ∀ a, R a x → ∀ a', R a' x ↔ a' = a := fun x hx a ha a' =>
    ⟨fun h => mem_arrow_one_Cls.1 hR a' a x ⟨⟨h, hx⟩, ⟨ha, hx⟩⟩, fun e => e ▸ ha⟩
  have ub : ∀ y, y ∈ H → ∀ b, S b y → ∀ b', S b' y ↔ b' = b := fun y hy b hb b' =>
    ⟨fun h => mem_arrow_one_Cls.1 hS b' b y ⟨⟨h, hy⟩, ⟨hb, hy⟩⟩, fun e => e ▸ hb⟩
  ext P
  rw [mem_clsTimes]
  constructor
  · rintro ⟨Q, hQ, hP⟩
    obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 hQ
    obtain ⟨a, ha⟩ := hG hx
    obtain ⟨b, hb⟩ := hH hy
    rw [(dpar_iff _ _ _ _).1 hP, dpar_couple (ua x hx a ha) (ub y hy b hb)]
    exact ⟨a, b, ⟨⟨x, hx, ha⟩, ⟨y, hy, hb⟩⟩, rfl⟩
  · rintro ⟨a, b, ⟨⟨x, hx, ha⟩, ⟨y, hy, hb⟩⟩, rfl⟩
    exact ⟨x ↓ y, couple_mem_clsTimes.2 ⟨hx, hy⟩,
      (dpar_iff _ _ _ _).2 (dpar_couple (ua x hx a ha) (ub y hy b hb)).symm⟩

/-- ✱113·127. \[\begin{aligned}\vdash : R \upharpoonright \gamma \in \alpha &\,\overline{\text{ sm }}\, \gamma . S \upharpoonright \delta \in \beta \,\overline{\text{ sm }}\, \delta . \supset .\\ &(R \parallel \breve{S} ) \upharpoonright (\delta \times \gamma ) \in (\alpha \downarrow_{,,} ʻʻ\beta ) \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, (\gamma \downarrow_{,,} ʻʻ\delta )\\ &[*113·122·125 . *43·302 . *73·142 . *111·14]\end{aligned}\] -/
theorem pm113_127 {R : γ → α → Prop} {S : δ → β → Prop} {A : Set γ} {B : Set δ} {G : Set α}
    {H : Set β} :
    R ↾ G ∈ smbar A G ∧ S ↾ H ∈ smbar B H →
      (R ∥ S˘) ↾ (H ×ₐ G) ∈ smsmbar (coupleImg A ʻʻ B) (coupleImg G ʻʻ H) := by
  rintro ⟨hRs, hSs⟩
  obtain ⟨⟨hR1, hA⟩, hGc⟩ := mem_smbar_iff.1 hRs
  obtain ⟨⟨hS1, hB⟩, hHc⟩ := mem_smbar_iff.1 hSs
  have hG : G ⊆ codom R := fun x hx => by
    rw [hGc] at hx; obtain ⟨a, ha, -⟩ := hx; exact ⟨a, ha⟩
  have hH : H ⊆ codom S := fun y hy => by
    rw [hHc] at hy; obtain ⟨b, hb, -⟩ := hy; exact ⟨b, hb⟩
  have hA' : A = R ʻʻ G := hA.trans dom_cres
  have hB' : B = S ʻʻ H := hB.trans dom_cres
  have hRc : R ↾ G ∈ arrow one Cls := oneCls_of_oneone hR1
  have hSc : S ↾ H ∈ arrow one Cls := oneCls_of_oneone hS1
  have hRm : R ↾ G ∈ arrow Cls one := mem_arrow_Cls_one.2 (mem_arrow_one_one.1 hR1).2
  have hSm : S ↾ H ∈ arrow Cls one := mem_arrow_Cls_one.2 (mem_arrow_one_one.1 hS1).2
  refine mem_smsmbar_iff.2 ⟨⟨pm113_122 ⟨⟨⟨hRm, hSm⟩, hG⟩, hH⟩, ?_⟩, ?_⟩
  · ext Q
    constructor
    · intro hQ; exact ⟨_, (dpar_iff _ _ _ _).2 rfl, hQ⟩
    · rintro ⟨P, -, hQ⟩; exact hQ
  · rw [hA', hB', ← pm113_125 ⟨⟨⟨hRc, hSc⟩, hG⟩, hH⟩]
    ext u
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
      ext P
      constructor
      · rintro ⟨Q, hQ, hP⟩; exact ⟨Q, hQ, hP, ⟨opImg couple G w, ⟨w, hw, rfl⟩, hQ⟩⟩
      · rintro ⟨Q, hQ, hP, -⟩; exact ⟨Q, hQ, hP⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
      ext P
      constructor
      · rintro ⟨Q, hQ, hP, -⟩; exact ⟨Q, hQ, hP⟩
      · rintro ⟨Q, hQ, hP⟩; exact ⟨Q, hQ, hP, ⟨opImg couple G w, ⟨w, hw, rfl⟩, hQ⟩⟩

/-- ✱113·128. \[\begin{aligned}\vdash : \text{Hp} &*113·127 . \supset . (R \parallel \breve{S} ) \upharpoonright (\delta \times \gamma ) \in (\beta \times \alpha ) \,\overline{\text{ sm }}\, (\delta \times \gamma ).\\ &(R \parallel \breve{S} )_{\in } \upharpoonright (\gamma \downarrow_{,,} ʻʻ\delta ) \in (\alpha \downarrow_{,,} ʻʻ\beta ) \,\overline{\text{ sm }}\, (\gamma \downarrow_{,,} ʻʻ\delta ) \quad[*113·127 . *111·15]\end{aligned}\]

`Hp ✱113·127` is its hypothesis. -/
theorem pm113_128 {R : γ → α → Prop} {S : δ → β → Prop} {A : Set γ} {B : Set δ} {G : Set α}
    {H : Set β} :
    R ↾ G ∈ smbar A G ∧ S ↾ H ∈ smbar B H →
      (R ∥ S˘) ↾ (H ×ₐ G) ∈ smbar (B ×ₐ A) (H ×ₐ G) ∧
        imgRel (R ∥ S˘) ↾ (coupleImg G ʻʻ H) ∈ smbar (coupleImg A ʻʻ B) (coupleImg G ʻʻ H) := by
  intro h
  exact (pm111_15 (T := R ∥ S˘) (L := coupleImg G ʻʻ H) (K := coupleImg A ʻʻ B)).1
    (pm113_127 h)

/-- ✱113·13. \[\begin{aligned}&\vdash : \alpha \text{ sm } \gamma . \beta \text{ sm } \delta . \supset . \alpha \downarrow_{,,} ʻʻ\beta \text{ sm } \text{ sm } \gamma \downarrow_{,,} ʻʻ\delta . (\beta \times \alpha ) \text{ sm } (\delta \times \gamma )\\ &[*113·127 . *111·4·44 . *113·1]\end{aligned}\] -/
theorem pm113_13 {A : Set α} {B : Set β} {G : Set γ} {H : Set δ} :
    sm A G ∧ sm B H →
      smsm (coupleImg A ʻʻ B : Set (Set (α → β → Prop))) (coupleImg G ʻʻ H : Set (Set (γ → δ → Prop)))
        ∧ sm (B ×ₐ A) (H ×ₐ G) := by
  rintro ⟨⟨R, hR⟩, ⟨S, hS⟩⟩
  have h := pm113_127 (R := R) (S := S)
    ⟨(cres_eq_of_smbar hR).symm ▸ hR, (cres_eq_of_smbar hS).symm ▸ hS⟩
  exact ⟨⟨_, h⟩, (pm111_44 ⟨_, h⟩).2⟩

/-- ✱113·14. \(\vdash . \alpha \times \beta = \text{Cnv}ʻʻ(\beta \times \alpha ) \quad[*113·101 . *55·14]\) -/
theorem pm113_14 {A : Set α} {B : Set β} : A ×ₐ B = Cnv ʻʻ (B ×ₐ A) := by
  ext R
  rw [mem_Cnv_img, mem_clsTimes, mem_clsTimes]
  constructor
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩; exact ⟨y, x, ⟨hy, hx⟩, couple_cnv x y⟩
  · rintro ⟨y, x, ⟨hy, hx⟩, h⟩
    refine ⟨x, y, ⟨hx, hy⟩, ?_⟩
    rw [← couple_cnv y x, ← h]; rfl

/-- ✱113·141. \(\vdash . \text{Nc}ʻ(\alpha \times \beta ) = \text{Nc}ʻ(\beta \times \alpha ) \quad[*113·14 . *73·4]\)

Both `Nc'` are in one free type `γ`. -/
theorem pm113_141 {A : Set α} {B : Set β} : nc γ (A ×ₐ B) = nc γ (B ×ₐ A) :=
  nc_eq_nc_of_sm (sm_clsTimes_comm A B)

/-- ✱113·142. \(\vdash : \exists ! \beta . \supset . \text{D}ʻʻ(\beta \times \alpha ) = \iotaʻʻ\alpha : \exists ! \alpha . \supset . \text{ᗡ}ʻʻ(\beta \times \alpha ) = \iotaʻʻ\beta \) -/
theorem pm113_142 {A : Set α} {B : Set β} :
    (B.Nonempty → D ʻʻ (B ×ₐ A) = iota ʻʻ A) ∧ (A.Nonempty → Dcnv ʻʻ (B ×ₐ A) = iota ʻʻ B) := by
  constructor
  · rintro ⟨y, hy⟩
    ext u
    constructor
    · rintro ⟨R, hR, rfl⟩
      obtain ⟨x, b, ⟨hx, -⟩, rfl⟩ := mem_clsTimes.1 hR
      exact ⟨x, hx, (dom_couple x b)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x ↓ y, couple_mem_clsTimes.2 ⟨hx, hy⟩, (dom_couple x y).symm⟩
  · rintro ⟨x, hx⟩
    ext u
    constructor
    · rintro ⟨R, hR, rfl⟩
      obtain ⟨a, y, ⟨-, hy⟩, rfl⟩ := mem_clsTimes.1 hR
      exact ⟨y, hy, (codom_couple a y)⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨x ↓ y, couple_mem_clsTimes.2 ⟨hx, hy⟩, (codom_couple x y).symm⟩

/-- ✱113·143. \[\begin{aligned}\vdash :\alpha \neq \beta .P = x\downarrow y.&R = x\downarrow \alpha \unicode{x228d} y\downarrow \beta .\supset .\\ &P = (Rʻ\alpha )\downarrow (Rʻ\beta ).R = \text{D}ʻP\uparrow \iota ʻ\alpha \unicode{x228d} \text{ᗡ}ʻP\uparrow \iota ʻ\beta\end{aligned}\]

`α ≠ β` puts `α`, `β` in one type; `x ↓ α ⊍ y ↓ β` relates individuals to classes. `R'α`,
`R'β` are descriptions (the first with the larger scope); `D'P`, `ᗡ'P` always exist. -/
theorem pm113_143 {A B : Set α} {x y : α} {P : α → α → Prop} {R : α → Set α → Prop} :
    (A ≠ B ∧ P = x ↓ y) ∧ R = x ↓ A ⊍ y ↓ B →
      Desc R A (fun a => Desc R B (fun b => P = a ↓ b)) ∧
        R = cross (dom P) (ι A) ⊍ cross (codom P) (ι B) := by
  rintro ⟨⟨hAB, rfl⟩, rfl⟩
  have hA : ∀ a, (x ↓ A ⊍ y ↓ B) a A ↔ a = x := fun a =>
    ⟨fun h => h.elim (fun h => h.1) (fun h => absurd h.2 hAB), fun e => Or.inl ⟨e, rfl⟩⟩
  have hB : ∀ b, (x ↓ A ⊍ y ↓ B) b B ↔ b = y := fun b =>
    ⟨fun h => h.elim (fun h => absurd h.2.symm hAB) (fun h => h.1), fun e => Or.inr ⟨e, rfl⟩⟩
  refine ⟨by rw [desc_of_unique hA, desc_of_unique hB], ?_⟩
  rw [dom_couple, codom_couple]
  rfl

/-- ✱113·144. \[\begin{aligned}\vdash :\alpha &\neq \beta .T = \hat{P} \hat{R} \{(\exists x,y).x\in \alpha .y\in \beta .P = x\downarrow y.R = x\downarrow \alpha \unicode{x228d} y\downarrow \beta\}.\\ &\supset .T\in 1\rightarrow 1.\text{D}ʻT = \beta \times \alpha .\text{ᗡ}ʻT = {\in}_{\Delta}ʻ(\iota ʻ\alpha \cup \iota ʻ\beta )\end{aligned}\]

`T` is given by its definition as a hypothesis (the product of four in its definiens is
bracketed to the left); `∈_Δ'(ι'α ∪ ι'β)` is `sel memRel (ι A ∪ ι B)`. -/
theorem pm113_144 {A B : Set α} {T : (α → α → Prop) → (α → Set α → Prop) → Prop} :
    A ≠ B ∧ T = (fun P R => ∃ x y, ((x ∈ A ∧ y ∈ B) ∧ P = x ↓ y) ∧ R = x ↓ A ⊍ y ↓ B) →
      (T ∈ arrow one one ∧ dom T = B ×ₐ A) ∧ codom T = sel memRel (ι A ∪ ι B) := by
  rintro ⟨hAB, rfl⟩
  have hR : ∀ x y x' y', (x ↓ A ⊍ y ↓ B : α → Set α → Prop) = x' ↓ A ⊍ y' ↓ B → x = x' ∧ y = y' := by
    intro x y x' y' h
    have h1 : (x' ↓ A ⊍ y' ↓ B) x A := h ▸ Or.inl ⟨rfl, rfl⟩
    have h2 : (x' ↓ A ⊍ y' ↓ B) y B := h ▸ Or.inr ⟨rfl, rfl⟩
    exact ⟨h1.elim (fun h => h.1) (fun h => absurd h.2 hAB),
      h2.elim (fun h => absurd h.2.symm hAB) (fun h => h.1)⟩
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro P P' R ⟨⟨x, y, ⟨-, rfl⟩, rfl⟩, ⟨x', y', ⟨-, rfl⟩, e⟩⟩
    obtain ⟨rfl, rfl⟩ := hR _ _ _ _ e; rfl
  · rintro P R R' ⟨⟨x, y, ⟨-, rfl⟩, rfl⟩, ⟨x', y', ⟨-, e⟩, rfl⟩⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e; rfl
  · ext P
    rw [mem_clsTimes]
    constructor
    · rintro ⟨R, x, y, ⟨⟨hx, hy⟩, rfl⟩, -⟩; exact ⟨x, y, ⟨hx, hy⟩, rfl⟩
    · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩; exact ⟨_, x, y, ⟨⟨hx, hy⟩, rfl⟩, rfl⟩
  · ext R
    constructor
    · rintro ⟨P, x, y, ⟨⟨hx, hy⟩, -⟩, rfl⟩
      refine mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩
      · rintro a b X ⟨h1 | h1, h2 | h2⟩
        · exact h1.1.trans h2.1.symm
        · exact absurd (h1.2.symm.trans h2.2) hAB
        · exact absurd (h2.2.symm.trans h1.2) hAB
        · exact h1.1.trans h2.1.symm
      · rintro a X (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hx
        · exact hy
      · ext X
        constructor
        · rintro ⟨a, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨x, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨y, Or.inr ⟨rfl, rfl⟩⟩
    · intro h
      obtain ⟨⟨h1, h2⟩, h3⟩ := mem_sel_iff.1 h
      have hA : A ∈ codom R := by rw [h3]; exact Or.inl rfl
      have hB : B ∈ codom R := by rw [h3]; exact Or.inr rfl
      obtain ⟨x, hx⟩ := hA
      obtain ⟨y, hy⟩ := hB
      refine ⟨x ↓ y, x, y, ⟨⟨h2 x A hx, h2 y B hy⟩, rfl⟩, ?_⟩
      funext a X
      apply propext
      constructor
      · intro haX
        have hX : X ∈ codom R := ⟨a, haX⟩
        rw [h3] at hX
        rcases hX with rfl | rfl
        · exact Or.inl ⟨mem_arrow_one_Cls.1 h1 a x X ⟨haX, hx⟩, rfl⟩
        · exact Or.inr ⟨mem_arrow_one_Cls.1 h1 a y X ⟨haX, hy⟩, rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hx
        · exact hy

/-- ✱113·145. \(\vdash :\alpha \neq \beta .\supset .\beta \times \alpha \text{ sm }{\in}_{\Delta}ʻ(\iota ʻ\alpha \cup \iota ʻ\beta ) \quad[*113·144]\) -/
theorem pm113_145 {A B : Set α} : A ≠ B → sm (B ×ₐ A) (sel memRel (ι A ∪ ι B)) := by
  intro h
  obtain ⟨⟨h1, h2⟩, h3⟩ := pm113_144 (A := A) (B := B) ⟨h, rfl⟩
  exact ⟨_, mem_smbar_iff.2 ⟨⟨h1, h2.symm⟩, h3.symm⟩⟩

/-- ✱113·146. \(\vdash :\alpha \neq \beta .\supset .\alpha \times \beta \text{ sm } {\in}_{\Delta}ʻ(\iota ʻ\alpha \cup \iota ʻ\beta ) \quad[*113·141·145]\) -/
theorem pm113_146 {A B : Set α} : A ≠ B → sm (A ×ₐ B) (sel memRel (ι A ∪ ι B)) :=
  fun h => sm_trans (sm_clsTimes_comm A B) (pm113_145 h)

/-- ✱113·147. \[\begin{aligned}\vdash :\text{Hp}*133·144.&\beta \times \alpha = \mu .\supset .\\ &T = \hat{P} \hat{R} \{P\in \mu .R = \text{D}ʻP\uparrow \iota ʻsʻ\text{D}ʻʻ\mu \unicode{x228d} \text{ᗡ}ʻP\uparrow \iota ʻsʻ\text{ᗡ}ʻʻ\mu \}\end{aligned}\]

`Hp ✱113·144` (the e-text prints `✱133·144`) is the hypothesis of ✱113·144; `μ` is a class of
relations (`M`).

**Status.** proved (reading): transcription error: `Hp ✱133·144` is read `Hp ✱113·144` (the
references of the demonstration are to ✱113·101·143·144). -/
theorem pm113_147 {A B : Set α} {T : (α → α → Prop) → (α → Set α → Prop) → Prop}
    {M : Set (α → α → Prop)} :
    (A ≠ B ∧ T = (fun P R => ∃ x y, ((x ∈ A ∧ y ∈ B) ∧ P = x ↓ y) ∧ R = x ↓ A ⊍ y ↓ B)) ∧
        B ×ₐ A = M →
      T = fun P R => P ∈ M ∧
        R = cross (dom P) (ι (sumCls (D ʻʻ M))) ⊍ cross (codom P) (ι (sumCls (Dcnv ʻʻ M))) := by
  rintro ⟨⟨hAB, rfl⟩, rfl⟩
  funext P R
  apply propext
  constructor
  · rintro ⟨x, y, ⟨⟨hx, hy⟩, rfl⟩, rfl⟩
    rw [(pm113_116.1 ⟨y, hy⟩), (pm113_116.2 ⟨x, hx⟩)]
    exact ⟨couple_mem_clsTimes.2 ⟨hx, hy⟩, ((pm113_143 ⟨⟨hAB, rfl⟩, rfl⟩).2)⟩
  · rintro ⟨hP, rfl⟩
    obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 hP
    rw [(pm113_116.1 ⟨y, hy⟩), (pm113_116.2 ⟨x, hx⟩)]
    exact ⟨x, y, ⟨⟨hx, hy⟩, rfl⟩, ((pm113_143 ⟨⟨hAB, rfl⟩, rfl⟩).2).symm⟩

/-- ✱113·148. \(\vdash :\alpha \cap \beta = \Lambda .\supset .C\upharpoonright (\alpha \times \beta )\in 1\rightarrow 1\)

`C` (the field) needs a homogeneous relation, so `α`, `β` are of one type. -/
theorem pm113_148 {A B : Set α} : A ∩ B = Λ → C ↾ (A ×ₐ B) ∈ arrow one one := by
  intro h
  refine mem_arrow_one_one.2 ⟨fun u v R ⟨⟨h1, _⟩, ⟨h2, _⟩⟩ =>
    (show u = fld R from h1).trans (show v = fld R from h2).symm, ?_⟩
  rintro u R R' ⟨⟨h1, hR⟩, ⟨h2, hR'⟩⟩
  obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 hR
  obtain ⟨x', y', ⟨hx', hy'⟩, rfl⟩ := mem_clsTimes.1 hR'
  have e : fld (x ↓ y) = fld (x' ↓ y') := (show u = _ from h1).symm.trans (show u = _ from h2)
  rw [fld_couple, fld_couple] at e
  rw [inter_eq_null_iff, Set.disjoint_left] at h
  have hx2 : x ∈ ι x' ∪ ι y' := e ▸ Or.inl rfl
  have hy2 : y ∈ ι x' ∪ ι y' := e ▸ Or.inr rfl
  rcases hx2 with hx2 | hx2
  · rcases hy2 with hy2 | hy2
    · rw [mem_unitCls.1 hx2] at hx; rw [mem_unitCls.1 hy2] at hy; exact absurd hx (h hy)
    · rw [mem_unitCls.1 hx2, mem_unitCls.1 hy2]
  · rw [mem_unitCls.1 hx2] at hx; exact absurd hx (h hy')

/-- ✱113·15. \(\vdash .Cʻʻ(\alpha \times \beta ) = Cʻʻ(\beta \times a) = \hat{\xi} \{(\exists x,y).x\in \alpha .y\in \beta .\xi = \iota ʻx\cup \iota ʻy\}\)

A chain of two equations (`C''` is the image under the relation `C`, homogeneous, so `α`, `β`
are of one type).

**Status.** proved (reading): transcription error: the e-text prints `β × a` for `β × α`. -/
theorem pm113_15 {A B : Set α} :
    C ʻʻ (A ×ₐ B) = C ʻʻ (B ×ₐ A) ∧
      C ʻʻ (B ×ₐ A) = {X | ∃ x y, (x ∈ A ∧ y ∈ B) ∧ X = ι x ∪ ι y} := by
  have key : ∀ {A B : Set α}, C ʻʻ (B ×ₐ A) = {X | ∃ x y, (x ∈ A ∧ y ∈ B) ∧ X = ι x ∪ ι y} := by
    intro A B
    ext X
    constructor
    · rintro ⟨R, hR, rfl⟩
      obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 hR
      exact ⟨x, y, ⟨hx, hy⟩, fld_couple x y⟩
    · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
      exact ⟨x ↓ y, couple_mem_clsTimes.2 ⟨hx, hy⟩, (fld_couple x y).symm⟩
  refine ⟨?_, key⟩
  rw [key, key]
  ext X
  constructor
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩; exact ⟨y, x, ⟨hy, hx⟩, Set.union_comm _ _⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩; exact ⟨y, x, ⟨hy, hx⟩, Set.union_comm _ _⟩

/-- ✱113·151. \(\vdash :\alpha \neq \beta .\supset .Cʻʻ(\alpha \times \beta ) = \text{D}ʻʻ{\in}_{\Delta}ʻ(\iota ʻ\alpha \cup \iota ʻ\beta ) \quad[*113·15.*80·92]\) -/
theorem pm113_151 {A B : Set α} : A ≠ B → C ʻʻ (A ×ₐ B) = D ʻʻ sel memRel (ι A ∪ ι B) := by
  intro hAB
  obtain ⟨-, h3⟩ := pm113_144 (A := A) (B := B) ⟨hAB, rfl⟩
  rw [← h3, pm113_15.1, pm113_15.2]
  ext X
  constructor
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    exact ⟨x ↓ A ⊍ y ↓ B, ⟨x ↓ y, x, y, ⟨⟨hx, hy⟩, rfl⟩, rfl⟩, (dom_rcup_couple x y A B).symm⟩
  · rintro ⟨R, ⟨P, x, y, ⟨⟨hx, hy⟩, -⟩, rfl⟩, rfl⟩
    exact ⟨x, y, ⟨hx, hy⟩, dom_rcup_couple x y A B⟩

/-- ✱113·152. \(\vdash :\alpha \cap \beta = \Lambda .\supset .Cʻʻ(\alpha \times \beta )\text{ sm }(\alpha \times \beta ).\text{D}ʻʻ{\in}_{\Delta}ʻ(\iota ʻ\alpha \cup \iota ʻ\beta )\text{ sm }(\alpha \times \beta )\) -/
theorem pm113_152 {A B : Set α} :
    A ∩ B = Λ → sm (C ʻʻ (A ×ₐ B)) (A ×ₐ B) ∧ sm (D ʻʻ sel memRel (ι A ∪ ι B)) (A ×ₐ B) := by
  intro h
  have h1 : sm (C ʻʻ (A ×ₐ B)) (A ×ₐ B) :=
    ⟨C ↾ (A ×ₐ B), mem_smbar_iff.2 ⟨⟨pm113_148 h, dom_cres.symm⟩,
      (codom_cres fun R _ => ⟨fld R, rfl⟩).symm⟩⟩
  refine ⟨h1, ?_⟩
  by_cases hAB : A = B
  · subst hAB
    have hA : A = ∅ := by rw [Set.inter_self, Null_eq_empty] at h; exact h
    subst hA
    have e1 : (sel memRel (ι (∅ : Set α) ∪ ι ∅) : Set (α → Set α → Prop)) = ∅ := by
      ext M
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hM
      obtain ⟨⟨-, h2⟩, h3⟩ := mem_sel_iff.1 hM
      have : (∅ : Set α) ∈ codom M := by rw [h3]; exact Or.inl rfl
      obtain ⟨x, hx⟩ := this
      exact h2 x ∅ hx
    have e2 : (∅ : Set α) ×ₐ (∅ : Set α) = ∅ := clsTimes_empty ∅
    rw [e1, e2]
    exact ⟨rNull, mem_smbar_iff.2 ⟨⟨mem_arrow_one_one.2 ⟨fun _ _ _ h => absurd h.1 (rNull_apply _ _),
      fun _ _ _ h => absurd h.1 (rNull_apply _ _)⟩, by ext x; simp [img, D, graph, dom, rNull_apply]⟩,
      by ext x; simp [codom, rNull_apply]⟩⟩
  · rw [← pm113_151 hAB]; exact h1

/-- ✱113·153. \(\vdash :\dot{s} ʻ\lambda \dot{\cap} \dot{s} ʻ\mu = \dot{\Lambda} .\supset .\dot{s} \mid C\upharpoonright (\lambda \times \mu )\in (sʻ\lambda \unicode{x228d}_{,,}ʻʻ\mu )\,\overline{\text{ sm }}\, (\lambda \times \mu ).sʻ\lambda \unicode{x228d}_{,,}ʻʻ\mu \text{ sm }\lambda \times \mu\)

`ṡ | C ↾ (λ × μ)` is `(graph sumRel ⨾ C) ↾ (L ×ₐ Mu)` (✱35·25), `s'λ ⊍,,''μ` is
`sumCls (graph (opImg rcup L) ʻʻ Mu)` (`λ ⊍,,` is the relation of `λ ⊍,, T` to `T`, ✱38·03);
`λ`, `μ` are classes of relations (`L`, `Mu`). -/
theorem pm113_153 {L Mu : Set (α → β → Prop)} :
    sumRel L ⩀ sumRel Mu = rNull →
      (graph sumRel ⨾ C) ↾ (L ×ₐ Mu) ∈ smbar (sumCls (graph (opImg rcup L) ʻʻ Mu)) (L ×ₐ Mu) ∧
        sm (sumCls (graph (opImg rcup L) ʻʻ Mu)) (L ×ₐ Mu) := by
  intro h0
  have hsum : ∀ T S : α → β → Prop, sumRel (fld (T ↓ S)) = T ⊍ S := by
    intro T S
    rw [fld_couple]
    funext x y; apply propext
    constructor
    · rintro ⟨R, (rfl | rfl), hR⟩
      · exact Or.inl hR
      · exact Or.inr hR
    · rintro (h | h)
      · exact ⟨T, Or.inl rfl, h⟩
      · exact ⟨S, Or.inr rfl, h⟩
  have hdisj : ∀ x y, sumRel L x y → sumRel Mu x y → False := fun x y h1 h2 => by
    have : (sumRel L ⩀ sumRel Mu) x y := ⟨h1, h2⟩
    rw [h0] at this; exact rNull_apply _ _ this
  have hrel : ∀ M R, ((graph sumRel ⨾ C) ↾ (L ×ₐ Mu)) M R ↔ M = sumRel (fld R) ∧ R ∈ L ×ₐ Mu := by
    intro M R
    constructor
    · rintro ⟨⟨X, hM, hX⟩, hR⟩; exact ⟨(show M = _ from hM).trans (by rw [show X = fld R from hX]), hR⟩
    · rintro ⟨rfl, hR⟩; exact ⟨⟨fld R, rfl, rfl⟩, hR⟩
  have hinj : ∀ T S T' S', T ∈ Mu → S ∈ L → T' ∈ Mu → S' ∈ L → S ⊍ T = S' ⊍ T' →
      S = S' ∧ T = T' := by
    intro T S T' S' hT hS hT' hS' e
    have key : ∀ (S S' T T' : α → β → Prop), S ∈ L → T' ∈ Mu → S ⊍ T = S' ⊍ T' →
        ∀ x y, S x y → S' x y := by
      intro S S' T T' hS hT' e x y hxy
      have : (S' ⊍ T') x y := e ▸ Or.inl hxy
      exact this.resolve_right fun h => hdisj x y ⟨S, hS, hxy⟩ ⟨T', hT', h⟩
    have key' : ∀ (S S' T T' : α → β → Prop), T ∈ Mu → S' ∈ L → S ⊍ T = S' ⊍ T' →
        ∀ x y, T x y → T' x y := by
      intro S S' T T' hT hS' e x y hxy
      have : (S' ⊍ T') x y := e ▸ Or.inr hxy
      exact this.resolve_left fun h => hdisj x y ⟨S', hS', h⟩ ⟨T, hT, hxy⟩
    refine ⟨funext fun x => funext fun y => propext ⟨key S S' T T' hS hT' e x y,
      key S' S T' T hS' hT e.symm x y⟩, funext fun x => funext fun y => propext
      ⟨key' S S' T T' hT hS' e x y, key' S' S T' T hT' hS e.symm x y⟩⟩
  have hone : (graph sumRel ⨾ C) ↾ (L ×ₐ Mu) ∈ arrow one one := by
    refine mem_arrow_one_one.2 ⟨fun M M' R ⟨h1, h2⟩ => ((hrel _ _).1 h1).1.trans
      ((hrel _ _).1 h2).1.symm, fun M R R' ⟨h1, h2⟩ => ?_⟩
    obtain ⟨e1, hR⟩ := (hrel _ _).1 h1
    obtain ⟨e2, hR'⟩ := (hrel _ _).1 h2
    obtain ⟨T, S, ⟨hT, hS⟩, rfl⟩ := mem_clsTimes.1 hR
    obtain ⟨T', S', ⟨hT', hS'⟩, rfl⟩ := mem_clsTimes.1 hR'
    rw [hsum] at e1 e2
    have e : T ⊍ S = T' ⊍ S' := e1.symm.trans e2
    obtain ⟨rfl, rfl⟩ := hinj T S T' S' hT hS hT' hS' (by
      rw [show S ⊍ T = T ⊍ S from funext fun _ => funext fun _ => propext or_comm,
        show S' ⊍ T' = T' ⊍ S' from funext fun _ => funext fun _ => propext or_comm]; exact e)
    rfl
  have hdom : sumCls (graph (opImg rcup L) ʻʻ Mu) = dom ((graph sumRel ⨾ C) ↾ (L ×ₐ Mu)) := by
    ext M
    constructor
    · rintro ⟨_, ⟨T, hT, rfl⟩, S, hS, rfl⟩
      refine ⟨T ↓ S, (hrel _ _).2 ⟨?_, couple_mem_clsTimes.2 ⟨hT, hS⟩⟩⟩
      rw [hsum]; funext x y; exact propext or_comm
    · rintro ⟨R, hR⟩
      obtain ⟨rfl, hR2⟩ := (hrel _ _).1 hR
      obtain ⟨T, S, ⟨hT, hS⟩, rfl⟩ := mem_clsTimes.1 hR2
      refine ⟨_, ⟨T, hT, rfl⟩, S, hS, ?_⟩
      show sumRel (fld (T ↓ S)) = S ⊍ T
      rw [hsum]; funext x y; exact propext or_comm
  have hcod : L ×ₐ Mu = codom ((graph sumRel ⨾ C) ↾ (L ×ₐ Mu)) := by
    ext R
    exact ⟨fun hR => ⟨_, (hrel _ _).2 ⟨rfl, hR⟩⟩, fun ⟨M, hM⟩ => ((hrel _ _).1 hM).2⟩
  have h := mem_smbar_iff.2 ⟨⟨hone, hdom⟩, hcod⟩
  exact ⟨h, ⟨_, h⟩⟩

/-- ✱113·16. \[\begin{aligned}\vdash :&tʻ\alpha = tʻ\beta .\supset .\text{Nc}ʻ(\alpha \times \beta ) =\\ &\hat{\xi} \{(\exists \gamma ,\delta ).\gamma \in \text{N}^{1}\text{c}ʻ\alpha .\delta \in \text{N}^{1}\text{c}ʻ\beta .\gamma \cap \delta = \Lambda .\xi \text{ sm }\text{D}ʻʻ{\in}_{\Delta}ʻ(\iota ʻ\gamma \cup \iota ʻ\delta )\}\end{aligned}\]

`t'α = t'β` puts `α`, `β` in one type; `N¹c'α` is `n1c A`; `ξ` and the `Nc'(α × β)` are in a
free type `γ`. -/
theorem pm113_16 {A B : Set α} : typ A = typ B →
    nc γ (A ×ₐ B) = {X | ∃ G H : Set (Set α), ((G ∈ n1c A ∧ H ∈ n1c B) ∧ G ∩ H = Λ) ∧
      sm X (D ʻʻ sel memRel (ι G ∪ ι H))} := by
  intro _
  ext X
  rw [n1c_eq, n1c_eq]
  constructor
  · intro hX
    obtain ⟨G, H, ⟨hG, hH⟩, hGH⟩ := exists_disjoint_copies A B
    refine ⟨G, H, ⟨⟨hG, hH⟩, hGH⟩, sm_trans hX ?_⟩
    exact sm_trans (sm_clsTimes (sm_symm hH) (sm_symm hG)) (sm_symm (pm113_152 hGH).2)
  · rintro ⟨G, H, ⟨⟨hG, hH⟩, hGH⟩, hX⟩
    exact sm_trans hX (sm_trans (pm113_152 hGH).2 (sm_clsTimes hH hG))

/-- ✱113·17. \(\vdash .\beta \times \alpha \in tʻtʻ(\alpha \uparrow \beta)\) -/
theorem pm113_17 {A : Set α} {B : Set β} : B ×ₐ A ∈ typ (typ (cross A B)) := by
  rw [typ_eq_univ]; exact Set.mem_univ _

/-- ✱113·171. \(\vdash :\alpha \cap \beta = \Lambda .\supset .\exists !\text{Nc}(tʻ\alpha )ʻ(\alpha \times \beta )\)

`Nc(t'α)` is the cardinal among the classes of the type of `t'α` (classes of `α`-things). -/
theorem pm113_171 {A B : Set α} : A ∩ B = Λ → (nc (Set α) (A ×ₐ B)).Nonempty :=
  fun h => ⟨_, (pm113_152 h).1⟩

/-- ✱113·172. \(\vdash :\alpha \in tʻ\beta .\supset .\exists !\text{Nc}(t^{2}ʻ\alpha )ʻ(\alpha \times \beta )\)

`α ∈ t'β` puts `α`, `β` in one type; `Nc(t²'α)` is among the classes of the type of `t²'α`. -/
theorem pm113_172 {A B : Set α} : A ∈ typ B → (nc (Set (Set α)) (A ×ₐ B)).Nonempty := by
  intro _
  obtain ⟨G, H, ⟨hG, hH⟩, hGH⟩ := exists_disjoint_copies A B
  exact ⟨_, sm_trans (pm113_152 hGH).2 (sm_clsTimes hH hG)⟩

/-- ✱113·18. \(\vdash :\exists !\alpha .\exists !\beta .\alpha \times \beta = \alpha' \times \beta'.\supset .\alpha = \alpha'.\beta = \beta'\) -/
theorem pm113_18 {A A' : Set α} {B B' : Set β} :
    (A.Nonempty ∧ B.Nonempty) ∧ A ×ₐ B = A' ×ₐ B' → A = A' ∧ B = B' := by
  rintro ⟨⟨hA, hB⟩, h⟩
  have hBB' := clsTimes_sub_left h.le hA
  have hAA' := clsTimes_sub_right h.le hB
  have hA' : A'.Nonempty := hA.mono hAA'
  have hB' : B'.Nonempty := hB.mono hBB'
  exact ⟨hAA'.antisymm (clsTimes_sub_right h.ge hB'), hBB'.antisymm (clsTimes_sub_left h.ge hA')⟩

/-- ✱113·181. \(\vdash :\exists !\alpha .\exists !\alpha'.\alpha \times \beta = \alpha' \times \beta'.\supset .\beta = \beta'\) -/
theorem pm113_181 {A A' : Set α} {B B' : Set β} :
    (A.Nonempty ∧ A'.Nonempty) ∧ A ×ₐ B = A' ×ₐ B' → B = B' :=
  fun ⟨⟨hA, hA'⟩, h⟩ => (clsTimes_sub_left h.le hA).antisymm (clsTimes_sub_left h.ge hA')

/-- ✱113·182. \[\begin{aligned}\vdash :&\exists !\beta .\exists !\beta'.\alpha \times \beta = \alpha' \times \beta'.\supset .\alpha = \alpha'\\ &[\text{Proof as in *113·181}]\end{aligned}\] -/
theorem pm113_182 {A A' : Set α} {B B' : Set β} :
    (B.Nonempty ∧ B'.Nonempty) ∧ A ×ₐ B = A' ×ₐ B' → A = A' :=
  fun ⟨⟨hB, hB'⟩, h⟩ => (clsTimes_sub_right h.le hB).antisymm (clsTimes_sub_right h.ge hB')

/-- ✱113·183. \(\vdash :\exists !\alpha .\exists !\beta .\supset .Fʻʻ(\alpha \times \beta ) = sʻCʻʻ(\alpha \times \beta ) = \alpha \cup \beta\)

`F''`, `C''` are images under the relations `F`, `C` (homogeneous: `α`, `β` of one type). The
chain is the conjunction of its links. -/
theorem pm113_183 {A B : Set α} :
    A.Nonempty ∧ B.Nonempty →
      F ʻʻ (A ×ₐ B) = sumCls (C ʻʻ (A ×ₐ B)) ∧ sumCls (C ʻʻ (A ×ₐ B)) = A ∪ B := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  constructor
  · ext x
    constructor
    · rintro ⟨R, hR, hx⟩; exact ⟨fld R, ⟨R, hR, rfl⟩, hx⟩
    · rintro ⟨_, ⟨R, hR, rfl⟩, hx⟩; exact ⟨R, hR, hx⟩
  · ext x
    constructor
    · rintro ⟨_, ⟨R, hR, rfl⟩, hx⟩
      obtain ⟨y, z, ⟨hy, hz⟩, rfl⟩ := mem_clsTimes.1 hR
      rw [fld_couple] at hx
      rcases hx with hx | hx
      · rw [mem_unitCls.1 hx]; exact Or.inr hy
      · rw [mem_unitCls.1 hx]; exact Or.inl hz
    · rintro (hx | hx)
      · exact ⟨fld (b ↓ x), ⟨b ↓ x, couple_mem_clsTimes.2 ⟨hb, hx⟩, rfl⟩,
          by rw [fld_couple]; exact Or.inr rfl⟩
      · exact ⟨fld (x ↓ a), ⟨x ↓ a, couple_mem_clsTimes.2 ⟨hx, ha⟩, rfl⟩,
          by rw [fld_couple]; exact Or.inl rfl⟩

/-- ✱113·19. \(\vdash :\exists !(\alpha \times \beta )\cap (\gamma \times \delta ). \equiv .\exists !\alpha \cap \gamma .\exists !\beta \cap \delta\) -/
theorem pm113_19 {A G : Set α} {B H : Set β} :
    ((A ×ₐ B) ∩ (G ×ₐ H)).Nonempty ↔ (A ∩ G).Nonempty ∧ (B ∩ H).Nonempty := by
  constructor
  · rintro ⟨R, h1, h2⟩
    obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 h1
    obtain ⟨hx', hy'⟩ := couple_mem_clsTimes.1 h2
    exact ⟨⟨y, hy, hy'⟩, ⟨x, hx, hx'⟩⟩
  · rintro ⟨⟨y, hy, hy'⟩, ⟨x, hx, hx'⟩⟩
    exact ⟨x ↓ y, couple_mem_clsTimes.2 ⟨hx, hy⟩, couple_mem_clsTimes.2 ⟨hx', hy'⟩⟩

/-- ✱113·191. \(\vdash \colon\ldotp \exists !\alpha .\supset :\exists !\alpha \downarrow_{,,}ʻʻ\beta \cap \alpha \downarrow_{,,}ʻʻ\gamma . \equiv .\exists !\beta \cap \gamma\) -/
theorem pm113_191 {A : Set α} {B G : Set β} :
    A.Nonempty → (((coupleImg A ʻʻ B : Set (Set (α → β → Prop))) ∩ coupleImg A ʻʻ G).Nonempty ↔
      (B ∩ G).Nonempty) := by
  intro hA
  have h1 := mem_arrow_one_one.1 (pm113_105 (β := β) hA)
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, ⟨y', hy', e⟩⟩
    have : y = y' := h1.2 _ y y' ⟨rfl, e⟩
    subst this
    exact ⟨y, hy, hy'⟩
  · rintro ⟨y, hy, hy'⟩
    exact ⟨_, ⟨y, hy, rfl⟩, ⟨y, hy', rfl⟩⟩

/-- ✱113·2. \[\begin{aligned}&\vdash :\xi \in \mu \times _{c} \nu . \equiv .(\exists \alpha ,\beta ).\mu = \text{N}_{0}\text{c}ʻ\alpha .\nu = \text{N}_{0}\text{c}ʻ\beta .\xi \text{ sm }(\alpha \times \beta )\\ &[(*113·03)]\end{aligned}\] -/
theorem pm113_2 {μ : Set (Set α)} {ν : Set (Set β)} {X : Set γ} :
    X ∈ (μ ×ᶜ ν : Set (Set γ)) ↔
      ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm X (A ×ₐ B) := Iff.rfl

/-- ✱113·201. \[\begin{aligned}&\vdash \colon\ldotp \xi \in \mu \times _{c} \nu . \equiv :\mu ,\nu \in \text{NC}:(\exists \alpha ,\beta ).\alpha \in \mu .\beta \in \nu .\xi \text{ sm }(\alpha \times \beta )\\ &[*113·2.*103·27]\end{aligned}\]

**Status.** proved (reading): `μ, ν ∈ NC` is `μ ∈ NC α ∧ ν ∈ NC β`, the ambiguous `NC` being
taken as in ✱103·27 (the reference), as in ✱110·201. -/
theorem pm113_201 {μ : Set (Set α)} {ν : Set (Set β)} {X : Set γ} :
    X ∈ (μ ×ᶜ ν : Set (Set γ)) ↔
      (μ ∈ NC α ∧ ν ∈ NC β) ∧ ∃ A B, (A ∈ μ ∧ B ∈ ν) ∧ sm X (A ×ₐ B) := by
  constructor
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    exact ⟨⟨n₀c_mem_NC A, n₀c_mem_NC B⟩, A, B, ⟨self_mem_n₀c A, self_mem_n₀c B⟩, h⟩
  · rintro ⟨⟨⟨A', rfl⟩, ⟨B', rfl⟩⟩, A, B, ⟨hA, hB⟩, h⟩
    exact ⟨A, B, ⟨nc_eq_n₀c_of_mem hA, nc_eq_n₀c_of_mem hB⟩, h⟩

/-- ✱113·202. \(\vdash \colon\ldotp \xi \in \mu \times _{c} \nu . \equiv :\exists !\mu .\exists !\nu :(\exists \gamma ,\delta ).\mu = \text{Nc}ʻ\gamma .\nu = \text{Nc}ʻ\delta .\xi \text{ sm }(\gamma \times \delta )\)

`μ = Nc'γ` is in the type of the members of `μ`, and the apparent `γ` is taken there. -/
theorem pm113_202 {μ : Set (Set α)} {ν : Set (Set β)} {X : Set γ} :
    X ∈ (μ ×ᶜ ν : Set (Set γ)) ↔ (μ.Nonempty ∧ ν.Nonempty) ∧
      ∃ (G : Set α) (H : Set β), (μ = nc α G ∧ ν = nc β H) ∧ sm X (G ×ₐ H) := by
  constructor
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    exact ⟨⟨n₀c_nonempty A, n₀c_nonempty B⟩, A, B, ⟨n₀c_eq_nc A, n₀c_eq_nc B⟩, h⟩
  · rintro ⟨-, G, H, ⟨rfl, rfl⟩, h⟩
    exact ⟨G, H, ⟨(n₀c_eq_nc G).symm, (n₀c_eq_nc H).symm⟩, h⟩

/-- ✱113·203. \(\vdash :\exists !\mu \times _{c} \nu .\supset .\mu ,\nu \in \text{NC} - \iota ʻ\Lambda .\mu ,\nu \in \text{N}_{0}\text{C} \quad[*113·201·202·2]\)

**Status.** proved (reading): the ambiguous `NC` of the conclusion is taken as in ✱110·4
(`NC^α(α)`, ✱103·27). -/
theorem pm113_203 {μ : Set (Set α)} {ν : Set (Set β)} : (μ ×ᶜ ν : Set (Set γ)).Nonempty →
    (μ ∈ NC α \ ι Λ ∧ ν ∈ NC β \ ι Λ) ∧ (μ ∈ N₀C ∧ ν ∈ N₀C) := by
  rintro ⟨X, A, B, ⟨rfl, rfl⟩, -⟩
  refine ⟨⟨⟨n₀c_mem_NC A, ?_⟩, ⟨n₀c_mem_NC B, ?_⟩⟩, ⟨A, rfl⟩, ⟨B, rfl⟩⟩
  · rw [mem_unitCls, Null_eq_empty]; exact n₀c_ne_empty A
  · rw [mem_unitCls, Null_eq_empty]; exact n₀c_ne_empty B

/-- ✱113·204. \(\vdash \colon\ldotp \mu = \Lambda .\lor.\nu = \Lambda .\lor.{\sim}(\mu ,\nu \in \text{NC}):\supset .\mu \times _{c} \nu = \Lambda \quad[*113·203]\)

**Status.** proved (reading): the ambiguous `NC` is taken as in ✱113·203 (`NC^α(α)`); with a
free type for `NC` the hypothesis `∼(μ, ν ∈ NC)` would not exclude a homogeneous cardinal. -/
theorem pm113_204 {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ = Λ ∨ ν = Λ) ∨ ¬(μ ∈ NC α ∧ ν ∈ NC β) → (μ ×ᶜ ν : Set (Set γ)) = Λ := by
  intro h
  rw [Null_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  intro hne
  obtain ⟨⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩, -⟩ := pm113_203 hne
  rcases h with (rfl | rfl) | h
  · exact h1' rfl
  · exact h2' rfl
  · exact h ⟨h1, h2⟩

/-- ✱113·205. \(\vdash :{\sim}(\mu ,\nu \in \text{N}_{0}\text{C}).\supset .\mu \times _{c} \nu = \Lambda \quad[*113·203]\) -/
theorem pm113_205 {μ : Set (Set α)} {ν : Set (Set β)} :
    ¬(μ ∈ N₀C ∧ ν ∈ N₀C) → (μ ×ᶜ ν : Set (Set γ)) = Λ := by
  intro h
  rw [Null_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  exact fun hne => h (pm113_203 hne).2

/-- ✱113·21. \[\begin{aligned}&\vdash \colon\ldotp \mu ,\nu \in \text{NC}.\supset :\xi \in \mu \times _{c} \nu . \equiv .(\exists \alpha ,\beta ).\alpha \in \mu .\beta \in \nu .\xi \text{ sm }(\alpha \times \beta )\\ &[*113·201]\end{aligned}\] -/
theorem pm113_21 {β₁ β₂ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {X : Set γ} :
    μ ∈ NC β₁ ∧ ν ∈ NC β₂ →
      (X ∈ (μ ×ᶜ ν : Set (Set γ)) ↔ ∃ A B, (A ∈ μ ∧ B ∈ ν) ∧ sm X (A ×ₐ B)) := by
  rintro ⟨⟨A', rfl⟩, ⟨B', rfl⟩⟩
  constructor
  · rintro ⟨A, B, ⟨hA, hB⟩, h⟩
    exact ⟨A, B, ⟨hA ▸ self_mem_n₀c A, hB ▸ self_mem_n₀c B⟩, h⟩
  · rintro ⟨A, B, ⟨hA, hB⟩, h⟩
    exact ⟨A, B, ⟨nc_eq_n₀c_of_mem hA, nc_eq_n₀c_of_mem hB⟩, h⟩

/-- ✱113·22. \(\vdash :\xi \in \text{Nc}(\eta )ʻ\gamma \times _{c} \text{Nc}(\zeta )ʻ\delta . \equiv .\exists !\text{Nc}(\eta )ʻ\gamma .\exists !\text{Nc}(\zeta )ʻ\delta .\xi \text{ sm }(\gamma \times \delta )\) -/
theorem pm113_22 {E Z : Type*} {G : Set α} {H : Set β} {X : Set γ} :
    X ∈ (nc E G ×ᶜ nc Z H : Set (Set γ)) ↔
      ((nc E G).Nonempty ∧ (nc Z H).Nonempty) ∧ sm X (G ×ₐ H) := by
  rcases nc_cases E G with h0 | ⟨P, hP, hPe⟩
  · rw [h0, empty_cardMul]; simp
  rcases nc_cases Z H with h0 | ⟨Q, hQ, hQe⟩
  · rw [h0, cardMul_empty]; simp
  rw [hPe, hQe, n₀c_cardMul_n₀c, nc_eq_nc_of_sm (sm_clsTimes hQ hP)]
  simp only [n₀c_nonempty, and_self, true_and]; exact Iff.rfl

/-- ✱113·221. \[\begin{aligned}&\vdash :\exists !\text{Nc}(\eta )ʻ\gamma .\exists !\text{Nc}(\zeta )ʻ\delta .\supset .\text{Nc}(\eta )ʻ\gamma \times _{c} \text{Nc}(\zeta )ʻ\delta = \text{Nc}ʻ(\gamma x \delta )\\ &[*113·22]\end{aligned}\]

**Status.** proved (reading): transcription error: the e-text prints `γ x δ` for `γ × δ`
(the reference ✱113·22 has `γ × δ`). -/
theorem pm113_221 {E Z : Type*} {G : Set α} {H : Set β} :
    (nc E G).Nonempty ∧ (nc Z H).Nonempty →
      (nc E G ×ᶜ nc Z H : Set (Set γ)) = nc γ (G ×ₐ H) := by
  intro h
  ext X
  rw [pm113_22]
  exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩

/-- ✱113·222. \(\vdash .\text{N}_{0}\text{c}ʻ\gamma \times _{c} \text{N}_{0}\text{c}ʻ\delta = \text{Nc}ʻ(\gamma \times \delta )\) -/
theorem pm113_222 {G : Set α} {H : Set β} :
    (n₀c G ×ᶜ n₀c H : Set (Set γ)) = nc γ (G ×ₐ H) := n₀c_cardMul_n₀c G H

/-- ✱113·23. \(\vdash .\mu \times _{c} \nu \in \text{NC}\)

**Status.** proved (reading): the ambiguous `NC` is taken as `NC^{t'ξ}(ξ)` for the classes `ξ`
of the product (`NC (Set γ)`), as in ✱110·42 (✱102·74). -/
theorem pm113_23 {μ : Set (Set α)} {ν : Set (Set β)} : (μ ×ᶜ ν : Set (Set γ)) ∈ NC (Set γ) := by
  rcases Set.eq_empty_or_nonempty (μ ×ᶜ ν : Set (Set γ)) with h | ⟨X, hX⟩
  · refine ⟨Set.univ, ?_⟩
    rw [h]
    ext Y
    simp only [Set.mem_empty_iff_false, false_iff]
    intro hY
    obtain ⟨e⟩ := mem_nc_iff_equiv.1 hY
    exact Function.cantor_injective (fun S : Set γ => ((e.symm ⟨S, trivial⟩ : Y) : γ))
      (fun a b hab => by
        have := e.symm.injective (Subtype.ext hab)
        exact congrArg Subtype.val this)
  · obtain ⟨A, B, ⟨rfl, rfl⟩, h⟩ := hX
    refine ⟨iota ʻʻ X, ?_⟩
    rw [n₀c_cardMul_n₀c, ← nc_eq_nc_of_sm h]
    refine nc_eq_nc_of_sm (sm_symm (sm_of_injOn (fun x => ι x) (fun x y _ _ e => unitCls_injective e)
      fun S => ⟨?_, ?_⟩))
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

/-- ✱113·24. \(\vdash .\text{Nc}ʻ\gamma \times _{c} \text{Nc}ʻ\delta = \text{N}_{0}\text{c}ʻ\gamma \times _{c} \text{N}_{0}\text{c}ʻ\delta \quad[(*113·04·05)]\)

**Status.** proved (reading): by the Dfs ✱113·04·05 the arguments `Nc'γ`, `Nc'δ` of `×_c` are
read `N₀c'γ`, `N₀c'δ`, so the equation is the identity of the two readings. -/
theorem pm113_24 {G : Set α} {H : Set β} :
    (n₀c G ×ᶜ n₀c H : Set (Set γ)) = n₀c G ×ᶜ n₀c H := rfl

/-- ✱113·25. \(\vdash .\text{Nc}ʻ\gamma \times _{c} \text{Nc}ʻ\delta = \text{Nc}ʻ(\gamma \times \delta )\quad [*113·24·222]\)

The arguments `Nc'γ`, `Nc'δ` of `×_c` are `n₀c G`, `n₀c H` (✱113·04·05). -/
theorem pm113_25 {G : Set α} {H : Set β} :
    (n₀c G ×ᶜ n₀c H : Set (Set γ)) = nc γ (G ×ₐ H) := n₀c_cardMul_n₀c G H

/-- ✱113·251. \(\vdash .\gamma \times \delta \in \text{Nc}ʻ\gamma \times _{c} \text{Nc}ʻ\delta \quad[*113·25.*100·3]\)

`γ × δ ∈ …` is an attributive occurrence: the product is in the type of `γ × δ`. -/
theorem pm113_251 {G : Set α} {H : Set β} : G ×ₐ H ∈ (n₀c G ×ᶜ n₀c H : Set (Set (β → α → Prop))) := by
  rw [n₀c_cardMul_n₀c]; exact self_mem_nc _

/-- ✱113·26. \(\vdash :\mu ,\nu \in \text{NC}.\exists !\text{ sm }_{\eta }ʻʻ\mu .\exists !\text{ sm }_{\zeta }ʻʻ\nu .\supset .\mu \times _{c} \nu = \text{ sm }_{\eta }ʻʻ\mu \times _{c} \text{ sm }_{\zeta }ʻʻ\nu\)

As ✱110·25: `sm_η''μ` is ascribed to the type of `η` (no adequacy hypothesis). -/
theorem pm113_26 {β₁ β₂ E Z : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    ((μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ (sm ʻʻ μ : Set (Set E)).Nonempty) ∧
        (sm ʻʻ ν : Set (Set Z)).Nonempty →
      (μ ×ᶜ ν : Set (Set γ)) = (sm ʻʻ μ : Set (Set E)) ×ᶜ (sm ʻʻ ν : Set (Set Z)) := by
  rintro ⟨⟨⟨hμ, hν⟩, h1⟩, h2⟩
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [sm_img_empty] at h1; exact absurd h1 Set.not_nonempty_empty
  rcases NC_cases hν with rfl | ⟨B, rfl⟩
  · rw [sm_img_empty] at h2; exact absurd h2 Set.not_nonempty_empty
  rw [sm_img_n₀c] at h1 h2 ⊢
  rw [sm_img_n₀c, pm113_221 ⟨h1, h2⟩, n₀c_cardMul_n₀c]

/-- ✱113·261. \(\vdash :\mu ,\nu \in \text{NC}.\supset .\mu \times _{c} \nu = \mu ^{(1)} \times _{c} \nu ^{(1)} = \mu _{(00)} \times _{c} \nu _{(00}) = \text{etc}.\)

The chain is stated for its two printed links; "etc." (the other ascending derivatives, which
PM leaves to analogy) is not a formula.

**Status.** proved (reading): the "etc." of the enunciation is not formalized; the links for
`μ^{(1)}` and `μ_{(00)}` are proved. -/
theorem pm113_261 {β₁ β₂ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NC β₁ ∧ ν ∈ NC β₂ →
      (μ ×ᶜ ν : Set (Set γ)) = up1 μ ×ᶜ up1 ν ∧
        (up1 μ ×ᶜ up1 ν : Set (Set γ)) = down00 μ ×ᶜ down00 ν := by
  rintro ⟨hμ, hν⟩
  rw [up1_eq, up1_eq, down00_eq, down00_eq]
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · simp [sm_img_empty, empty_cardMul]
  rcases NC_cases hν with rfl | ⟨B, rfl⟩
  · simp [sm_img_empty, cardMul_empty]
  have e1 := pm113_26 (γ := γ) ⟨⟨⟨n₀c_mem_NC A, n₀c_mem_NC B⟩,
    by rw [sm_img_n₀c]; exact nc_up_nonempty A⟩, by rw [sm_img_n₀c]; exact nc_up_nonempty B⟩
  have e2 := pm113_26 (γ := γ) ⟨⟨⟨n₀c_mem_NC A, n₀c_mem_NC B⟩,
    by rw [sm_img_n₀c]; exact nc_rel_nonempty A⟩, by rw [sm_img_n₀c]; exact nc_rel_nonempty B⟩
  exact ⟨e1, e1.symm.trans e2⟩

/-- ✱113·27. \(\vdash .\mu \times _{c} \nu = \nu \times _{c} \mu\) -/
theorem pm113_27 {μ : Set (Set α)} {ν : Set (Set β)} : (μ ×ᶜ ν : Set (Set γ)) = ν ×ᶜ μ := by
  ext X
  constructor
  · rintro ⟨A, B, ⟨hA, hB⟩, h⟩; exact ⟨B, A, ⟨hB, hA⟩, sm_trans h (sm_clsTimes_comm A B)⟩
  · rintro ⟨B, A, ⟨hB, hA⟩, h⟩; exact ⟨A, B, ⟨hA, hB⟩, sm_trans h (sm_clsTimes_comm B A)⟩

/-- ✱113·3. \(\vdash \colon\ldotp \text{Mult ax}.\supset :\kappa \in \text{Nc}ʻ\beta \cap \text{Cl}ʻ\text{Nc}ʻ\alpha .\supset .\Sigma ʻ\kappa \in \text{Nc}ʻ\alpha \times _{c} \text{Nc}ʻ\beta\)

`κ ∈ Nc'β ∩ Cl'Nc'α`: the attributive `Nc'β` is in the type of `κ` and `Nc'α` in the type of
its members; `Σ'κ ∈ Nc'α ×_c Nc'β` puts the product in the type of `Σ'κ`, its arguments
normally adjusted (✱113·04·05). `Mult ax` is taken at the type of the correlators used in PM's
demonstration (✱112·24 applied to `κ` and `α↓,,''β`). -/
theorem pm113_3 {A : Set α} {B : Set β} {K : Set (Set δ)} :
    MultAx ((δ → Set δ → Prop) → ((α → β → Prop) → Set (α → β → Prop) → Prop) → Prop) →
      K ∈ nc (Set δ) B ∩ cl (nc δ A) →
        clsSigma K ∈ (n₀c A ×ᶜ n₀c B : Set (Set (δ → Set δ → Prop))) := by
  rintro - ⟨hK, hKA⟩
  rw [n₀c_cardMul_n₀c]
  exact clsSigma_sm_clsTimes hK fun X hX => hKA hX

/-- ✱113·31. \(\vdash \colon\ldotp \text{Mult ax}.\supset :\mu ,\nu \in \text{NC}.\kappa \in \nu \cap \text{Cl}ʻ\mu .\supset .\Sigma ʻ\kappa \in \mu \times _{c} \nu \quad[*113·3]\)

`μ, ν ∈ NC` with independent types; `Σ'κ ∈ μ ×_c ν` puts the product in the type of `Σ'κ`.

**Status.** proved (corrected): as printed it is false when `μ = Λ` (which is a member of `NC` in
suitable types, ✱102·74): then `κ = Λ`, `ν = 0`, `Σ'κ = Λ` and `μ ×_c ν = Λ`
(`pm113_31_printed_false`). The hypothesis `∃!μ` is added (it holds whenever `∃!κ`). -/
theorem pm113_31 {β₁ β₂ : Type*} {μ : Set (Set δ)} {ν : Set (Set (Set δ))} {K : Set (Set δ)} :
    MultAx ((δ → Set δ → Prop) → ((δ → Set δ → Prop) → Set (δ → Set δ → Prop) → Prop) → Prop) →
      ((μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ K ∈ ν ∩ cl μ) ∧ μ.Nonempty →
        clsSigma K ∈ (μ ×ᶜ ν : Set (Set (δ → Set δ → Prop))) := by
  rintro - ⟨⟨⟨⟨A', rfl⟩, ⟨B', rfl⟩⟩, hK, hKμ⟩, ⟨X, hX⟩⟩
  rw [show (refs sm A' : Set (Set δ)) = n₀c X from nc_eq_n₀c_of_mem hX,
    show (refs sm B' : Set (Set (Set δ))) = n₀c K from nc_eq_n₀c_of_mem hK, n₀c_cardMul_n₀c]
  exact clsSigma_sm_clsTimes (sm_refl K) fun Y hY => sm_trans (hKμ hY) (sm_symm hX)

/-- The printed form of ✱113·31 (without `∃!μ`) is false. -/
theorem pm113_31_printed_false : ¬ ∀ (μ : Set (Set Unit)) (ν : Set (Set (Set Unit)))
    (K : Set (Set Unit)), (μ ∈ NC (Set Unit) ∧ ν ∈ NC (Set Unit)) ∧ K ∈ ν ∩ cl μ →
      clsSigma K ∈ (μ ×ᶜ ν : Set (Set (Unit → Set Unit → Prop))) := by
  intro h
  have hμ : (∅ : Set (Set Unit)) ∈ NC (Set Unit) := by
    refine ⟨Set.univ, ?_⟩
    ext Y
    simp only [Set.mem_empty_iff_false, false_iff]
    intro hY
    obtain ⟨e⟩ := mem_nc_iff_equiv.1 hY
    exact Function.cantor_injective (fun S : Set Unit => ((e.symm ⟨S, trivial⟩ : Y) : Unit))
      (fun a b hab => congrArg Subtype.val (e.symm.injective (Subtype.ext hab)))
  have := h ∅ zero ∅ ⟨⟨hμ, ⟨∅, zero_eq_nc_empty⟩⟩, ⟨by rw [zero_eq]; rfl, Set.empty_subset _⟩⟩
  rw [empty_cardMul] at this
  exact this

/-- ✱113·32. \[\begin{aligned}&\vdash \colon\ldotp \text{Mult ax}.\supset :\mu ,\nu \in \text{NC}.\kappa \in \nu \cap \text{Cl excl}ʻ\mu .\supset .sʻ\kappa \in \mu \times _{c} \nu \\ &[*112·15.*113·31·23]\end{aligned}\]

**Status.** proved (corrected): as ✱113·31 (false as printed for `μ = κ = Λ`, `ν = 0`:
`pm113_32_printed_false`); the hypothesis `∃!μ` is added. -/
theorem pm113_32 {β₁ β₂ : Type*} {μ : Set (Set δ)} {ν : Set (Set (Set δ))} {K : Set (Set δ)} :
    MultAx ((δ → Set δ → Prop) → ((δ → Set δ → Prop) → Set (δ → Set δ → Prop) → Prop) → Prop) →
      ((μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ K ∈ ν ∩ clExcl μ) ∧ μ.Nonempty →
        sumCls K ∈ (μ ×ᶜ ν : Set (Set δ)) := by
  rintro hM ⟨⟨hNC, hK, hKe, hKμ⟩, hμ⟩
  have h := pm113_31 hM ⟨⟨hNC, hK, hKμ⟩, hμ⟩
  obtain ⟨⟨A', rfl⟩, ⟨B', rfl⟩⟩ := hNC
  obtain ⟨X, hX⟩ := hμ
  rw [show (refs sm A' : Set (Set δ)) = n₀c X from nc_eq_n₀c_of_mem hX,
    show (refs sm B' : Set (Set (Set δ))) = n₀c K from nc_eq_n₀c_of_mem hK, n₀c_cardMul_n₀c] at h ⊢
  exact sm_trans (sumCls_mem_sigmaNc hKe) h

/-- The printed form of ✱113·32 (without `∃!μ`) is false. -/
theorem pm113_32_printed_false : ¬ ∀ (μ : Set (Set Unit)) (ν : Set (Set (Set Unit)))
    (K : Set (Set Unit)), (μ ∈ NC (Set Unit) ∧ ν ∈ NC (Set Unit)) ∧ K ∈ ν ∩ clExcl μ →
      sumCls K ∈ (μ ×ᶜ ν : Set (Set Unit)) := by
  intro h
  have hμ : (∅ : Set (Set Unit)) ∈ NC (Set Unit) := by
    refine ⟨Set.univ, ?_⟩
    ext Y
    simp only [Set.mem_empty_iff_false, false_iff]
    intro hY
    obtain ⟨e⟩ := mem_nc_iff_equiv.1 hY
    exact Function.cantor_injective (fun S : Set Unit => ((e.symm ⟨S, trivial⟩ : Y) : Unit))
      (fun a b hab => congrArg Subtype.val (e.symm.injective (Subtype.ext hab)))
  have hex : (∅ : Set (Set Unit)) ∈ Cls2excl := fun A _ h => absurd h.1.1 (Set.notMem_empty A)
  have := h ∅ zero ∅ ⟨⟨hμ, ⟨∅, zero_eq_nc_empty⟩⟩, ⟨by rw [zero_eq]; rfl, hex, Set.empty_subset _⟩⟩
  rw [empty_cardMul] at this
  exact this

/-- ✱113·33. \[\begin{aligned}\vdash \colon\ldotp \text{Mult ax} .\supset :\mu ,\nu \in &\text{NC}.\kappa \in \nu \cap \text{Cl}ʻ\mu .\lambda\in \mu \cap \text{Cl}ʻ\nu .\supset .\\ &\Sigma \text{Nc}ʻ\kappa = \Sigma \text{Nc}ʻ\lambda = \mu \times _{c} \nu \quad[*113·31·27·23]\end{aligned}\]

`μ` and `ν` occur in two relative types: in `κ ∈ ν ∩ Cl'μ` (with `κ` a class of classes of
`δ`-things) and in `λ ∈ μ ∩ Cl'ν` (with `λ` a class of classes of `ε`-things). The second
occurrences are "the same cardinals in the other type", `sm''μ` and `sm''ν` with the types
`λ` requires (cf. ✱104·03, ✱110·25). The equations are in a free type `γ`.

**Status.** proved (reading): the occurrences of `μ`, `ν` in `λ ∈ μ ∩ Cl'ν` are in other types,
read as `sm''μ`, `sm''ν` in those types (typical ambiguity of the real variables `μ`, `ν`). -/
theorem pm113_33 {β₁ β₂ : Type*} {μ : Set (Set δ)} {ν : Set (Set (Set δ))} {K : Set (Set δ)}
    {L : Set (Set ε)} :
    MultAx ((δ → Set δ → Prop) → ((δ → Set δ → Prop) → Set (δ → Set δ → Prop) → Prop) → Prop) →
      ((μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ K ∈ ν ∩ cl μ) ∧
          L ∈ (sm ʻʻ μ : Set (Set (Set ε))) ∩ cl (sm ʻʻ ν : Set (Set ε)) →
        sigmaNc γ K = sigmaNc γ L ∧ sigmaNc γ L = (μ ×ᶜ ν : Set (Set γ)) := by
  rintro - ⟨⟨⟨⟨A', rfl⟩, ⟨B', rfl⟩⟩, hK, hKμ⟩, ⟨X, hX, hLX⟩, hLν⟩
  rw [show (refs sm A' : Set (Set δ)) = n₀c X from nc_eq_n₀c_of_mem hX,
    show (refs sm B' : Set (Set (Set δ))) = n₀c K from nc_eq_n₀c_of_mem hK, n₀c_cardMul_n₀c]
  have h1 : sm (clsSigma K) (X ×ₐ K) :=
    clsSigma_sm_clsTimes (sm_refl K) fun Y hY => sm_trans (hKμ hY) (sm_symm hX)
  have h2 : sm (clsSigma L) (K ×ₐ X) := by
    refine clsSigma_sm_clsTimes hLX fun Y hY => ?_
    obtain ⟨Z, hZ, hYZ⟩ := hLν hY
    exact sm_trans hYZ (sm_trans hZ (sm_symm hK))
  have h3 : sm (clsSigma L) (X ×ₐ K) := sm_trans h2 (sm_clsTimes_comm K X)
  exact ⟨nc_eq_nc_of_sm (sm_trans h1 (sm_symm h3)), nc_eq_nc_of_sm h3⟩

/-- ✱113·34. \[\begin{aligned}\vdash \colon\ldotp \text{Mult ax} .\supset :\mu ,\nu \in &\text{NC}.\kappa \in \nu \cap \text{Cl excl}ʻ\mu .\lambda \in \mu \cap \text{Cl excl}ʻ\nu .\supset .\\ &\text{Nc}ʻsʻ\kappa = \text{Nc}ʻsʻ\lambda = \mu \times _{c} \nu \quad[*113·32·27]\end{aligned}\]

As ✱113·33 (the second occurrences of `μ`, `ν` are `sm''μ`, `sm''ν`).

**Status.** proved (reading): the occurrences of `μ`, `ν` in `λ ∈ μ ∩ Cl excl'ν` are in other
types, read as `sm''μ`, `sm''ν` in those types (typical ambiguity of the real variables `μ`, `ν`). -/
theorem pm113_34 {β₁ β₂ : Type*} {μ : Set (Set δ)} {ν : Set (Set (Set δ))} {K : Set (Set δ)}
    {L : Set (Set ε)} :
    MultAx ((δ → Set δ → Prop) → ((δ → Set δ → Prop) → Set (δ → Set δ → Prop) → Prop) → Prop) →
      ((μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ K ∈ ν ∩ clExcl μ) ∧
          L ∈ (sm ʻʻ μ : Set (Set (Set ε))) ∩ clExcl (sm ʻʻ ν : Set (Set ε)) →
        nc γ (sumCls K) = nc γ (sumCls L) ∧ nc γ (sumCls L) = (μ ×ᶜ ν : Set (Set γ)) := by
  rintro hM ⟨⟨hNC, hK, hKe, hKμ⟩, hL, hLe, hLν⟩
  have := pm113_33 (γ := γ) hM ⟨⟨hNC, hK, hKμ⟩, hL, hLν⟩
  rw [← sigmaNc_eq_nc_sumCls hKe, ← sigmaNc_eq_nc_sumCls hLe]
  exact this

/-- ✱113·4. \(\vdash .(\beta \cup \gamma ) \times \alpha = (\beta \times \alpha )\cup (\gamma \times \alpha )\) -/
theorem pm113_4 {A : Set α} {B G : Set β} : (B ∪ G) ×ₐ A = (B ×ₐ A) ∪ (G ×ₐ A) := by
  ext R
  simp only [Set.mem_union, mem_clsTimes]
  constructor
  · rintro ⟨x, y, ⟨hx, hy | hy⟩, rfl⟩
    · exact Or.inl ⟨x, y, ⟨hx, hy⟩, rfl⟩
    · exact Or.inr ⟨x, y, ⟨hx, hy⟩, rfl⟩
  · rintro (⟨x, y, ⟨hx, hy⟩, rfl⟩ | ⟨x, y, ⟨hx, hy⟩, rfl⟩)
    · exact ⟨x, y, ⟨hx, Or.inl hy⟩, rfl⟩
    · exact ⟨x, y, ⟨hx, Or.inr hy⟩, rfl⟩

/-- ✱113·401. \(\vdash :\beta \cap \gamma = \Lambda .\supset .(\beta \times \alpha )\cap (\gamma \times \alpha ) = \Lambda \quad[*113·19.\text{Transp}]\) -/
theorem pm113_401 {A : Set α} {B G : Set β} : B ∩ G = Λ → (B ×ₐ A) ∩ (G ×ₐ A) = Λ := by
  intro h
  rw [Null_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  intro hne
  have := (pm113_19.1 hne).1
  rw [h, Null_eq_empty] at this
  exact Set.not_nonempty_empty this

/-- ✱113·41. \[\begin{aligned}\vdash .\text{Nc}ʻ(\beta + \gamma ) \times _{c} \text{Nc}ʻ\alpha = \text{Nc}ʻ\{(\beta + \gamma ) \times \alpha\} &= \text{Nc}ʻ\{(\beta \times \alpha ) + (\gamma \times \alpha )\}\\ &= \text{Nc}ʻ(\beta \times \alpha ) +_{c} \text{Nc}ʻ(\gamma \times \alpha )\end{aligned}\]

A chain of three equations; the arguments `Nc'(β + γ)`, `Nc'α`, … of `×_c`, `+_c` are
`n₀c (B +ₐ G)`, `n₀c A`, … (✱110·03·04, ✱113·04·05); all in one free type `γ'`. -/
theorem pm113_41 {A : Set α} {B : Set β} {G : Set δ} :
    ((n₀c (B +ₐ G) ×ᶜ n₀c A : Set (Set γ)) = nc γ ((B +ₐ G) ×ₐ A) ∧
        nc γ ((B +ₐ G) ×ₐ A) = nc γ ((B ×ₐ A) +ₐ (G ×ₐ A))) ∧
      nc γ ((B ×ₐ A) +ₐ (G ×ₐ A)) = (n₀c (B ×ₐ A) +ᶜ n₀c (G ×ₐ A) : Set (Set γ)) :=
  ⟨⟨n₀c_cardMul_n₀c _ _, nc_eq_nc_of_sm (sm_clsTimes_distrib A B G)⟩,
    (n₀c_cardAdd_n₀c _ _).symm⟩

/-- ✱113·42. \[\begin{aligned}\vdash .(\text{Nc}ʻ\beta +_{c} \text{Nc}ʻ\gamma ) \times _{c} \text{Nc}ʻ\alpha &= \text{Nc}ʻ(\beta + \gamma ) \times _{c} \text{Nc}ʻ\alpha \\ &= (\text{Nc}ʻ\beta \times _{c} \text{Nc}ʻ\alpha ) +_{c} (\text{Nc}ʻ\gamma \times _{c} \text{Nc}ʻ\alpha )\\ [*110·3.*113·25.*113·41]\end{aligned}\]

The inner sum and products are arithmetical components with adequate types (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components are adequate -/
theorem pm113_42 {W₁ W₂ W₃ : Type*} {A : Set α} {B : Set β} {G : Set δ}
    (h₁ : AdeqAdd W₁ (n₀c B) (n₀c G)) (h₂ : AdeqMul W₂ (n₀c B) (n₀c A))
    (h₃ : AdeqMul W₃ (n₀c G) (n₀c A)) :
    ((n₀c B +ᶜ n₀c G : Set (Set W₁)) ×ᶜ n₀c A : Set (Set γ)) = (n₀c (B +ₐ G) ×ᶜ n₀c A) ∧
      (n₀c (B +ₐ G) ×ᶜ n₀c A : Set (Set γ)) =
        ((n₀c B ×ᶜ n₀c A : Set (Set W₂)) +ᶜ (n₀c G ×ᶜ n₀c A : Set (Set W₃))) := by
  obtain ⟨X, hX, e1⟩ := inner_add_eq h₁
  obtain ⟨Y, hY, e2⟩ := inner_mul_eq h₂
  obtain ⟨Z, hZ, e3⟩ := inner_mul_eq h₃
  rw [e1, e2, e3, n₀c_cardMul_n₀c, n₀c_cardMul_n₀c, n₀c_cardAdd_n₀c]
  refine ⟨nc_eq_nc_of_sm (sm_clsTimes (sm_refl A) hX), nc_eq_nc_of_sm ?_⟩
  exact sm_trans (sm_clsTimes_distrib A B G) (sm_clsSum (sm_symm hY) (sm_symm hZ))

/-- ✱113·421. \[\begin{aligned}\vdash . \text{Nc}ʻ\alpha \times _{c} (\text{Nc}ʻ\beta &+_{c} \text{Nc}ʻ\gamma ) = \text{Nc}ʻ\alpha \times _{c} \text{Nc}ʻ(\beta + \gamma )\\ &= (\text{Nc}ʻ\alpha \times _{c} \text{Nc}ʻ\beta ) +_{c} (\text{Nc}ʻ\alpha \times _{c} \text{Nc}ʻ\gamma ) \quad[*113·42·27]\end{aligned}\]

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components are adequate -/
theorem pm113_421 {W₁ W₂ W₃ : Type*} {A : Set α} {B : Set β} {G : Set δ}
    (h₁ : AdeqAdd W₁ (n₀c B) (n₀c G)) (h₂ : AdeqMul W₂ (n₀c A) (n₀c B))
    (h₃ : AdeqMul W₃ (n₀c A) (n₀c G)) :
    (n₀c A ×ᶜ (n₀c B +ᶜ n₀c G : Set (Set W₁)) : Set (Set γ)) = (n₀c A ×ᶜ n₀c (B +ₐ G)) ∧
      (n₀c A ×ᶜ n₀c (B +ₐ G) : Set (Set γ)) =
        ((n₀c A ×ᶜ n₀c B : Set (Set W₂)) +ᶜ (n₀c A ×ᶜ n₀c G : Set (Set W₃))) := by
  obtain ⟨X, hX, e1⟩ := inner_add_eq h₁
  obtain ⟨Y, hY, e2⟩ := inner_mul_eq h₂
  obtain ⟨Z, hZ, e3⟩ := inner_mul_eq h₃
  rw [e1, e2, e3, n₀c_cardMul_n₀c, n₀c_cardMul_n₀c, n₀c_cardAdd_n₀c]
  refine ⟨nc_eq_nc_of_sm (sm_clsTimes hX (sm_refl A)), nc_eq_nc_of_sm ?_⟩
  refine sm_trans (sm_clsTimes_comm A (B +ₐ G)) (sm_trans (sm_clsTimes_distrib A B G) ?_)
  exact sm_clsSum (sm_trans (sm_clsTimes_comm B A) (sm_symm hY))
    (sm_trans (sm_clsTimes_comm G A) (sm_symm hZ))

/-- ✱113·43. \(\vdash .(\nu +_{c} \varpi ) \times _{c} \mu = \mu \times _{c} (\nu +_{c} \varpi ) = (\mu \times _{c} \nu ) +_{c} (\mu \times _{c} \varpi )\)

The inner sums and products are arithmetical components with adequate types (IIT); the
chain is the conjunction of its links, in a free type `γ`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components are adequate -/
theorem pm113_43 {α₁ α₂ α₃ W₁ W₂ W₃ W₄ : Type*} {μ : Set (Set α₁)} {ν : Set (Set α₂)}
    {ϖ : Set (Set α₃)} (h₁ : AdeqAdd W₁ ν ϖ) (h₂ : AdeqAdd W₂ ν ϖ) (h₃ : AdeqMul W₃ μ ν)
    (h₄ : AdeqMul W₄ μ ϖ) :
    ((ν +ᶜ ϖ : Set (Set W₁)) ×ᶜ μ : Set (Set γ)) = μ ×ᶜ (ν +ᶜ ϖ : Set (Set W₂)) ∧
      (μ ×ᶜ (ν +ᶜ ϖ : Set (Set W₂)) : Set (Set γ)) =
        ((μ ×ᶜ ν : Set (Set W₃)) +ᶜ (μ ×ᶜ ϖ : Set (Set W₄))) := by
  by_cases hμ : ∃ A, μ = n₀c A
  swap
  · push Not at hμ
    rw [cardMul_eq_empty_of_right (ν := μ) _ hμ, cardMul_eq_empty_of_left (μ := μ) hμ,
      cardMul_eq_empty_of_left (μ := μ) hμ, cardMul_eq_empty_of_left (μ := μ) hμ, empty_cardAdd]
    exact ⟨rfl, rfl⟩
  by_cases hν : ∃ B, ν = n₀c B
  swap
  · push Not at hν
    rw [cardAdd_eq_empty_of_left (μ := ν) hν, cardAdd_eq_empty_of_left (μ := ν) hν,
      cardMul_eq_empty_of_right (ν := ν) _ hν, empty_cardMul, cardMul_empty, empty_cardAdd]
    exact ⟨rfl, rfl⟩
  by_cases hϖ : ∃ G, ϖ = n₀c G
  swap
  · push Not at hϖ
    rw [cardAdd_eq_empty_of_right (ν := ϖ) _ hϖ, cardAdd_eq_empty_of_right (ν := ϖ) _ hϖ,
      cardMul_eq_empty_of_right (ν := ϖ) _ hϖ, empty_cardMul, cardMul_empty, cardAdd_empty]
    exact ⟨rfl, rfl⟩
  obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν; obtain ⟨G, rfl⟩ := hϖ
  obtain ⟨X, hX, e1⟩ := inner_add_eq h₁
  obtain ⟨X', hX', e2⟩ := inner_add_eq h₂
  obtain ⟨Y, hY, e3⟩ := inner_mul_eq h₃
  obtain ⟨Z, hZ, e4⟩ := inner_mul_eq h₄
  rw [e1, e2, e3, e4, n₀c_cardMul_n₀c, n₀c_cardMul_n₀c, n₀c_cardAdd_n₀c]
  refine ⟨nc_eq_nc_of_sm (sm_trans (sm_clsTimes_comm X A) (sm_clsTimes (sm_trans hX
    (sm_symm hX')) (sm_refl A))), nc_eq_nc_of_sm ?_⟩
  refine sm_trans (sm_clsTimes hX' (sm_refl A)) (sm_trans (sm_clsTimes_comm A (B +ₐ G))
    (sm_trans (sm_clsTimes_distrib A B G) ?_))
  exact sm_clsSum (sm_trans (sm_clsTimes_comm B A) (sm_symm hY))
    (sm_trans (sm_clsTimes_comm G A) (sm_symm hZ))

/-- ✱113·44. \(\vdash .(sʻ\kappa ) \times \alpha = sʻ(x \alpha )ʻʻ\kappa\)

`×α` is the relation of `β × α` to `β` (`graph (· ×ₐ A)`).

**Status.** proved (reading): transcription error: the e-text prints `x α` for `×α` (as
✱113·45·46·47 print it). -/
theorem pm113_44 {A : Set α} {K : Set (Set β)} :
    sumCls K ×ₐ A = sumCls (graph (fun B => B ×ₐ A) ʻʻ K) := by
  ext R
  rw [mem_clsTimes]
  constructor
  · rintro ⟨x, y, ⟨hx, ⟨B, hB, hy⟩⟩, rfl⟩
    exact ⟨B ×ₐ A, ⟨B, hB, rfl⟩, couple_mem_clsTimes.2 ⟨hx, hy⟩⟩
  · rintro ⟨_, ⟨B, hB, rfl⟩, hR⟩
    obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 hR
    exact ⟨x, y, ⟨hx, B, hB, hy⟩, rfl⟩

/-- ✱113·45. \(\vdash :\kappa \in \text{Cls}^{2} \text{excl}.\supset . \times \alpha ʻʻ\kappa \in \text{Cls}^{2} \text{excl}\) -/
theorem pm113_45 {A : Set α} {K : Set (Set β)} :
    K ∈ Cls2excl → graph (fun B => B ×ₐ A) ʻʻ K ∈ Cls2excl := by
  rintro hK _ _ ⟨⟨⟨B, hB, rfl⟩, ⟨G, hG, rfl⟩⟩, hne⟩
  exact pm113_401 (hK B G ⟨⟨hB, hG⟩, fun h => hne (h ▸ rfl)⟩)

/-- ✱113·46. \(\vdash :\kappa \in \text{Cls}^{2} \text{excl}.\supset .\Sigma ʻ \times \alpha ʻʻ\kappa \text{ sm }(\Sigma ʻ\kappa ) \times \alpha\) -/
theorem pm113_46 {A : Set α} {K : Set (Set β)} :
    K ∈ Cls2excl → sm (clsSigma (graph (fun B => B ×ₐ A) ʻʻ K)) (clsSigma K ×ₐ A) := by
  intro hK
  have h1 := sm_symm (sumCls_mem_sigmaNc (pm113_45 (A := A) hK))
  rw [← pm113_44] at h1
  exact sm_trans h1 (sm_clsTimes (sm_refl A) (sumCls_mem_sigmaNc hK))

/-- ✱113·47. \[\begin{aligned}&\vdash :\kappa \in \text{Cls}^{2} \text{excl}.\supset .\Sigma \text{Nc}ʻ \times \alpha ʻʻ\kappa = \text{Nc}ʻ{(\Sigma ʻ\kappa ) \times \alpha } = \Sigma \text{Nc}ʻ\kappa \times _{c} \text{Nc}ʻ\alpha \\ &[*113·46]\end{aligned}\]

The argument `ΣNc'κ` of `×_c` has an adequate type `W` (IIT); `Nc'α` is `n₀c A`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component ΣNc'κ is adequate -/
theorem pm113_47 {W : Type*} {A : Set α} {K : Set (Set β)} (hW : AdeqSigmaNc W K) :
    K ∈ Cls2excl → sigmaNc γ (graph (fun B => B ×ₐ A) ʻʻ K) = nc γ (clsSigma K ×ₐ A) ∧
      nc γ (clsSigma K ×ₐ A) = (sigmaNc W K ×ᶜ n₀c A : Set (Set γ)) := by
  intro hK
  obtain ⟨X, hX⟩ := adeqSigmaNc_nonempty hW K
  refine ⟨nc_eq_nc_of_sm (pm113_46 hK), ?_⟩
  rw [show sigmaNc W K = n₀c X from nc_eq_n₀c_of_mem hX, n₀c_cardMul_n₀c]
  exact nc_eq_nc_of_sm (sm_clsTimes (sm_refl A) (sm_symm hX))

/-- ✱113·48. \(\vdash .sʻ\alpha \times ʻʻ\kappa = \alpha \times (sʻ\kappa ) = \text{Cnv}ʻʻ\{(sʻ\kappa ) \times \alpha\}\)

`α×` is the relation of `α × β` to `β` (`graph (A ×ₐ ·)`); the chain is a conjunction. -/
theorem pm113_48 {A : Set α} {K : Set (Set β)} :
    sumCls (graph (fun B => A ×ₐ B) ʻʻ K) = A ×ₐ sumCls K ∧
      A ×ₐ sumCls K = Cnv ʻʻ (sumCls K ×ₐ A) := by
  refine ⟨?_, pm113_14⟩
  ext R
  rw [mem_clsTimes]
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, hR⟩
    obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 hR
    exact ⟨x, y, ⟨⟨B, hB, hx⟩, hy⟩, rfl⟩
  · rintro ⟨x, y, ⟨⟨B, hB, hx⟩, hy⟩, rfl⟩
    exact ⟨A ×ₐ B, ⟨B, hB, rfl⟩, couple_mem_clsTimes.2 ⟨hx, hy⟩⟩

/-- ✱113·49. \(\vdash :\kappa \in \text{Cls}^{2} \text{excl}.\supset .\Sigma ʻ\alpha \times ʻʻ\kappa \text{ sm }\alpha \times (\Sigma ʻ\kappa )\) -/
theorem pm113_49 {A : Set α} {K : Set (Set β)} :
    K ∈ Cls2excl → sm (clsSigma (graph (fun B => A ×ₐ B) ʻʻ K)) (A ×ₐ clsSigma K) := by
  intro hK
  have hex : graph (fun B => A ×ₐ B) ʻʻ K ∈ Cls2excl := by
    rintro _ _ ⟨⟨⟨B, hB, rfl⟩, ⟨G, hG, rfl⟩⟩, hne⟩
    have h0 := hK B G ⟨⟨hB, hG⟩, fun h => hne (h ▸ rfl)⟩
    rw [Null_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne'
    have := (pm113_19.1 hne').2
    rw [h0, Null_eq_empty] at this
    exact Set.not_nonempty_empty this
  have h1 := sm_symm (sumCls_mem_sigmaNc hex)
  rw [pm113_48.1] at h1
  exact sm_trans h1 (sm_clsTimes (sumCls_mem_sigmaNc hK) (sm_refl A))

/-- ✱113·491. \[\begin{aligned}&\vdash :\kappa \in \text{Cls}^{2} \text{excl}.\supset .\Sigma \text{Nc}ʻ\alpha \times ʻʻ\kappa = \text{Nc}ʻ{\alpha \times (\Sigma ʻ\kappa )} = \text{Nc}ʻ\alpha \times _{c} \Sigma \text{Nc}ʻ\kappa \\ &[*113·49·25]\end{aligned}\]

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component ΣNc'κ is adequate -/
theorem pm113_491 {W : Type*} {A : Set α} {K : Set (Set β)} (hW : AdeqSigmaNc W K) :
    K ∈ Cls2excl → sigmaNc γ (graph (fun B => A ×ₐ B) ʻʻ K) = nc γ (A ×ₐ clsSigma K) ∧
      nc γ (A ×ₐ clsSigma K) = (n₀c A ×ᶜ sigmaNc W K : Set (Set γ)) := by
  intro hK
  obtain ⟨X, hX⟩ := adeqSigmaNc_nonempty hW K
  refine ⟨nc_eq_nc_of_sm (pm113_49 hK), ?_⟩
  rw [show sigmaNc W K = n₀c X from nc_eq_n₀c_of_mem hX, n₀c_cardMul_n₀c]
  exact nc_eq_nc_of_sm (sm_clsTimes (sm_symm hX) (sm_refl A))

/-- ✱113·5. \(\vdash .(\gamma \times \beta ) \times \alpha = \hat{R} \{(\exists x,y,z).x\in \alpha .y\in \beta .z\in \gamma .R = x\downarrow (y\downarrow z)\}\) -/
theorem pm113_5 {A : Set α} {B : Set β} {G : Set δ} :
    (G ×ₐ B) ×ₐ A = {R | ∃ x y z, ((x ∈ A ∧ y ∈ B) ∧ z ∈ G) ∧ R = x ↓ (y ↓ z)} := by
  ext R
  rw [mem_clsTimes]
  constructor
  · rintro ⟨x, P, ⟨hx, hP⟩, rfl⟩
    obtain ⟨y, z, ⟨hy, hz⟩, rfl⟩ := mem_clsTimes.1 hP
    exact ⟨x, y, z, ⟨⟨hx, hy⟩, hz⟩, rfl⟩
  · rintro ⟨x, y, z, ⟨⟨hx, hy⟩, hz⟩, rfl⟩
    exact ⟨x, y ↓ z, ⟨hx, couple_mem_clsTimes.2 ⟨hy, hz⟩⟩, rfl⟩

/-- ✱113·51. \(\vdash .(\alpha \times \beta ) \times \gamma \text{ sm }\alpha \times (\beta \times \gamma )\) -/
theorem pm113_51 {A : Set α} {B : Set β} {G : Set δ} : sm (A ×ₐ B ×ₐ G) (A ×ₐ (B ×ₐ G)) :=
  sm_clsTimes_assoc A B G

/-- ✱113·511 (Df). \(\alpha \times \beta \times \gamma = (\alpha \times \beta ) \times \gamma \quad\text{Df}\) -/
theorem pm113_511 {A : Set α} {B : Set β} {G : Set δ} : A ×ₐ B ×ₐ G = (A ×ₐ B) ×ₐ G := rfl

/-- ✱113·52. \(\vdash . (\text{Nc}ʻ\alpha \times _{c} \text{Nc}ʻ\beta ) \times _{c} \text{Nc}ʻ\gamma = \text{Nc}ʻ(\alpha \times \beta \times \gamma ) \quad[*113·25]\)

The inner product is an arithmetical component with an adequate type `W` (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component Nc'α ×_c Nc'β is adequate -/
theorem pm113_52 {W : Type*} {A : Set α} {B : Set β} {G : Set δ}
    (h : AdeqMul W (n₀c A) (n₀c B)) :
    ((n₀c A ×ᶜ n₀c B : Set (Set W)) ×ᶜ n₀c G : Set (Set γ)) = nc γ (A ×ₐ B ×ₐ G) := by
  obtain ⟨X, hX, e⟩ := inner_mul_eq h
  rw [e, n₀c_cardMul_n₀c]
  exact nc_eq_nc_of_sm (sm_clsTimes (sm_refl G) hX)

/-- ✱113·53. \(\vdash . (\text{Nc}ʻ\alpha \times _{c} \text{Nc}ʻ\beta ) \times _{c} \text{Nc}ʻ\gamma = \text{Nc}ʻ\alpha \times _{c} (\text{Nc}ʻ\beta \times _{c} \text{Nc}ʻ\gamma )\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components are adequate -/
theorem pm113_53 {W₁ W₂ : Type*} {A : Set α} {B : Set β} {G : Set δ}
    (h₁ : AdeqMul W₁ (n₀c A) (n₀c B)) (h₂ : AdeqMul W₂ (n₀c B) (n₀c G)) :
    ((n₀c A ×ᶜ n₀c B : Set (Set W₁)) ×ᶜ n₀c G : Set (Set γ)) =
      n₀c A ×ᶜ (n₀c B ×ᶜ n₀c G : Set (Set W₂)) := by
  obtain ⟨Y, hY, e⟩ := inner_mul_eq h₂
  rw [pm113_52 h₁, e, n₀c_cardMul_n₀c]
  exact nc_eq_nc_of_sm (sm_trans (sm_clsTimes_assoc A B G) (sm_clsTimes (sm_symm hY) (sm_refl A)))

/-- ✱113·531. \[\begin{aligned}&\vdash . (\text{N}_{0}\text{c}ʻ\alpha \times _{c} \text{N}_{0}\text{c}ʻ\beta ) \times _{c} \text{N}_{0}\text{c}ʻ\gamma = \text{N}_{0}\text{c}ʻ\alpha \times _{c} (\text{N}_{0}\text{c}ʻ\beta \times _{c} \text{N}_{0}\text{c}ʻ\gamma )\\ &[*113·53.(*113·04·05)]\end{aligned}\]

(After normal adjustment this is the statement of ✱113·53.)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components are adequate -/
theorem pm113_531 {W₁ W₂ : Type*} {A : Set α} {B : Set β} {G : Set δ}
    (h₁ : AdeqMul W₁ (n₀c A) (n₀c B)) (h₂ : AdeqMul W₂ (n₀c B) (n₀c G)) :
    ((n₀c A ×ᶜ n₀c B : Set (Set W₁)) ×ᶜ n₀c G : Set (Set γ)) =
      n₀c A ×ᶜ (n₀c B ×ᶜ n₀c G : Set (Set W₂)) :=
  pm113_53 h₁ h₂

/-- ✱113·54. \(\vdash . (\mu \times _{c} \nu ) \times _{c} \varpi = \mu \times _{c} (\nu \times _{c} \varpi )\)

As ✱110·56 (IIT for the inner products).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components μ ×_c ν and ν ×_c ϖ are adequate -/
theorem pm113_54 {α₁ α₂ α₃ W₁ W₂ : Type*} {μ : Set (Set α₁)} {ν : Set (Set α₂)}
    {ϖ : Set (Set α₃)} (h₁ : AdeqMul W₁ μ ν) (h₂ : AdeqMul W₂ ν ϖ) :
    ((μ ×ᶜ ν : Set (Set W₁)) ×ᶜ ϖ : Set (Set γ)) = μ ×ᶜ (ν ×ᶜ ϖ : Set (Set W₂)) := by
  by_cases hμ : ∃ A, μ = n₀c A
  · by_cases hν : ∃ B, ν = n₀c B
    · by_cases hϖ : ∃ G, ϖ = n₀c G
      · obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν; obtain ⟨G, rfl⟩ := hϖ
        exact pm113_53 h₁ h₂
      · push Not at hϖ
        rw [cardMul_eq_empty_of_right _ hϖ, cardMul_eq_empty_of_right (ν := ϖ) _ hϖ,
          cardMul_empty]
    · push Not at hν
      rw [cardMul_eq_empty_of_right (ν := ν) _ hν, cardMul_eq_empty_of_left (μ := ν) hν,
        empty_cardMul, cardMul_empty]
  · push Not at hμ
    rw [cardMul_eq_empty_of_left (μ := μ) hμ, cardMul_eq_empty_of_left (μ := μ) hμ,
      empty_cardMul]

/-- ✱113·541 (Df). \(\mu \times _{c} \nu \times _{c} \varpi = (\mu \times _{c} \nu ) \times _{c} \varpi \quad\text{Df}\)

Realized by `infixl`; the inner product has its own type `W` (IIT). -/
theorem pm113_541 {W : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set δ)} :
    ((μ ×ᶜ ν : Set (Set W)) ×ᶜ ϖ : Set (Set γ)) = ((μ ×ᶜ ν : Set (Set W)) ×ᶜ ϖ : Set (Set γ)) := rfl

/-- ✱113·6. \(\vdash . \text{Nc}ʻ\alpha \times _{c} 0 = 0\)

`0` is an arithmetical argument with its own type (no hypothesis is needed for `0`). -/
theorem pm113_6 {W : Type*} {A : Set α} :
    (n₀c A ×ᶜ (zero : Set (Set W)) : Set (Set γ)) = zero := by
  rw [zero_eq_n₀c_empty, n₀c_cardMul_n₀c, clsTimes_empty]
  exact zero_eq_nc_empty.symm

/-- ✱113·601. \(\vdash :\mu \in \text{NC} - \iota ʻ\Lambda .\supset .\mu \times _{c} 0 = 0\) -/
theorem pm113_601 {β' W : Type*} {μ : Set (Set α)} :
    μ ∈ NC β' \ ι Λ → (μ ×ᶜ (zero : Set (Set W)) : Set (Set γ)) = zero := by
  rintro ⟨hμ, hne⟩
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · exact absurd (by rw [Null_eq_empty]; rfl) hne
  exact pm113_6

/-- ✱113·602. \(\vdash \colon\ldotp \mu \times _{c} \nu = 0. \equiv :\mu ,\nu \in \text{NC} -{℩} ʻ\Lambda :\mu = 0.\lor.\nu = 0\)

`μ = 0`, `ν = 0` are in the types of `μ`, `ν`.

**Status.** proved (reading): the ambiguous `NC` is taken as in ✱113·203 (`NC^α(α)`). -/
theorem pm113_602 {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ×ᶜ ν : Set (Set γ)) = zero ↔ (μ ∈ NC α \ ι Λ ∧ ν ∈ NC β \ ι Λ) ∧ (μ = zero ∨ ν = zero) := by
  constructor
  · intro h
    have h0 : (∅ : Set γ) ∈ (μ ×ᶜ ν : Set (Set γ)) := by rw [h, zero_eq]; rfl
    refine ⟨(pm113_203 ⟨_, h0⟩).1, ?_⟩
    obtain ⟨A, B, ⟨rfl, rfl⟩, hs⟩ := h0
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hs
    by_contra hne
    push Not at hne
    rw [zero_eq_n₀c_empty, Ne, n₀c_eq_n₀c_iff, zero_eq_n₀c_empty, Ne, n₀c_eq_n₀c_iff] at hne
    have hA : A.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]; rintro rfl; exact hne.1 (sm_refl _)
    have hB : B.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]; rintro rfl; exact hne.2 (sm_refl _)
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    exact (e.symm ⟨b ↓ a, couple_mem_clsTimes.2 ⟨hb, ha⟩⟩).2
  · rintro ⟨⟨⟨hμ, hμ0⟩, ⟨hν, hν0⟩⟩, h⟩
    rcases NC_cases hμ with rfl | ⟨A, rfl⟩
    · exact absurd (by rw [Null_eq_empty]; rfl) hμ0
    rcases NC_cases hν with rfl | ⟨B, rfl⟩
    · exact absurd (by rw [Null_eq_empty]; rfl) hν0
    rw [n₀c_cardMul_n₀c, zero_eq_nc_empty (α := β → α → Prop)]
    rcases h with h | h
    · rw [zero_eq_n₀c_empty, n₀c_eq_n₀c_iff] at h
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
      have : A = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => (e ⟨x, hx⟩).2
      subst this
      rw [show (∅ : Set α) ×ₐ B = ∅ from by
        ext R; simp only [Set.mem_empty_iff_false, iff_false]; intro hR
        obtain ⟨x, y, ⟨-, hy⟩, -⟩ := mem_clsTimes.1 hR; exact hy]
    · rw [zero_eq_n₀c_empty, n₀c_eq_n₀c_iff] at h
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
      have : B = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => (e ⟨x, hx⟩).2
      subst this
      rw [clsTimes_empty]

/-- ✱113·61. \(\vdash .\iota ʻz \times \alpha = \downarrow zʻʻ\alpha\)

`↓z''α` is `coupleR z ʻʻ A`. -/
theorem pm113_61 {A : Set α} {z : δ} : ι z ×ₐ A = coupleR z ʻʻ A := by
  ext R
  rw [mem_clsTimes]
  constructor
  · rintro ⟨x, y, ⟨hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, z, ⟨hx, rfl⟩, rfl⟩

/-- ✱113·611. \(\vdash .\iota ʻz \times \alpha \text{ sm }\alpha \quad[*113·61.*73·611]\) -/
theorem pm113_611 {A : Set α} {z : δ} : sm (ι z ×ₐ A) A := clsTimes_unit_sm A z

/-- ✱113·612. \(\vdash .\alpha \times \iota ʻz\text{ sm }\alpha \quad[*113·611·141]\) -/
theorem pm113_612 {A : Set α} {z : δ} : sm (A ×ₐ ι z) A :=
  sm_trans (sm_clsTimes_comm A (ι z)) (clsTimes_unit_sm A z)

/-- ✱113·62. \(\vdash .\text{Nc}ʻ\alpha \times _{c} 1 = \text{Nc}ʻ\alpha\)

The constant `1` has its own type `W`, in which it exists (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the `1` is taken in a type
in which it exists -/
theorem pm113_62 {W : Type*} [Nonempty W] {A : Set α} :
    (n₀c A ×ᶜ (one : Set (Set W)) : Set (Set γ)) = nc γ A := by
  obtain ⟨w⟩ := ‹Nonempty W›
  rw [one_eq_n₀c_singleton w, n₀c_cardMul_n₀c, ← unitCls_eq_singleton]
  exact nc_eq_nc_of_sm (sm_trans (sm_clsTimes_comm A (ι w)) (clsTimes_unit_sm A w))

/-- ✱113·621. \(\vdash :\mu \in \text{NC}.\supset .\mu \times _{c} 1 = \text{ sm }ʻʻ\mu\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the `1` is taken in a type
in which it exists -/
theorem pm113_621 {β' W : Type*} [Nonempty W] {μ : Set (Set α)} :
    μ ∈ NC β' → (μ ×ᶜ (one : Set (Set W)) : Set (Set γ)) = sm ʻʻ μ := by
  intro hμ
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [empty_cardMul, sm_img_empty]
  rw [pm113_62, sm_img_n₀c]

/-- ✱113·63. \(\vdash :z{\sim}\in \alpha .\supset .\downarrow zʻʻ\alpha \text{ sm } \text{D}ʻʻ{\in}_{\Delta}ʻ(\iota ʻ\alpha \cup \iota ʻ\iota ʻz)\) -/
theorem pm113_63 {A : Set α} {z : α} :
    z ∉ A → sm (coupleR z ʻʻ A) (D ʻʻ sel memRel (ι A ∪ ι (ι z))) := by
  intro hz
  have hd : A ∩ ι z = Λ := by
    rw [inter_eq_null_iff, Set.disjoint_right]
    intro x hx hxA; rw [mem_unitCls.1 hx] at hxA; exact hz hxA
  rw [← pm113_61]
  exact sm_trans (sm_clsTimes_comm (ι z) A) (sm_symm (pm113_152 hd).2)

/-- ✱113·64. \(\vdash .\downarrow zʻʻ\alpha \times \downarrow zʻʻ\beta \text{ sm } \alpha \times \beta .\downarrow zʻʻ\alpha \times \downarrow zʻʻ\beta \text{ sm }\downarrow zʻʻ(\alpha \times \beta )\) -/
theorem pm113_64 {A : Set α} {B : Set β} {z : δ} :
    sm ((coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B)) (A ×ₐ B) ∧
      sm ((coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B)) (coupleR z ʻʻ (A ×ₐ B)) := by
  have h1 : sm ((coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B)) (A ×ₐ B) :=
    sm_clsTimes (coupleR_img_sm z B) (coupleR_img_sm z A)
  exact ⟨h1, sm_trans h1 (sm_symm (coupleR_img_sm z _))⟩

/-- ✱113·65. \(\vdash .\downarrow zʻʻ\alpha \times \downarrow zʻʻ\beta = (\downarrow z\parallel \text{Cnv}ʻ\downarrow z)ʻʻ(\alpha \times \beta )\)

`Cnv'↓z` is `(coupleR z)˘`. -/
theorem pm113_65 {A : Set α} {B : Set β} {z : δ} :
    (coupleR z ʻʻ A) ×ₐ (coupleR z ʻʻ B) = (coupleR z ∥ (coupleR z)˘) ʻʻ (A ×ₐ B) := by
  exact (pm113_126 ⟨⟨⟨coupleR_cres_oneCls z B, coupleR_cres_oneCls z A⟩,
    subset_codom_coupleR z B⟩, subset_codom_coupleR z A⟩).symm

/-- ✱113·66. \(\vdash .\mu \times _{c} 2 = \mu +_{c} \mu\)

The constant `2` has its own type `W`, in which it exists (IIT); the equation is in a free type.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the `2` is taken in a type
in which it exists -/
theorem pm113_66 {W : Type w'} {μ : Set (Set α)} (h2 : (two : Set (Set W)).Nonempty) :
    (μ ×ᶜ (two : Set (Set W)) : Set (Set γ)) = μ +ᶜ μ := by
  classical
  obtain ⟨_, a, b, hab, rfl⟩ := h2
  by_cases hμ : ∃ A, μ = n₀c A
  · obtain ⟨A, rfl⟩ := hμ
    rw [two_eq_n₀c_pair hab, n₀c_cardMul_n₀c, n₀c_cardAdd_n₀c]
    apply nc_eq_nc_of_sm
    have hb : a ∉ ({b} : Set W) := fun h => hab h
    refine sm_of_equiv ((clsTimesEquiv A {a, b}).trans ((((Equiv.Set.insert hb).trans
      ((Equiv.Set.singleton.{w' + 1} b).sumCongr (Equiv.refl _))).prodCongr (Equiv.refl _)).trans
        ((Equiv.sumProdDistrib _ _ _).trans (((Equiv.punitProd _).sumCongr
          (Equiv.punitProd _)).trans (clsSumEquiv A A).symm))))
  · push Not at hμ
    rw [cardMul_eq_empty_of_left hμ, cardAdd_eq_empty_of_left hμ]

/-- ✱113·67. \(\vdash .\text{Nc}ʻ\alpha \times _{c} \text{Nc}ʻ(\beta + \iota ʻy) = (\text{Nc}ʻ\alpha \times _{c} \text{Nc}ʻ\beta ) +_{c} \text{Nc}ʻ\alpha\)

The inner product is an arithmetical component with an adequate type `W` (IIT); the arguments
`Nc'α`, `Nc'(β + ι'y)` are `n₀c A`, `n₀c (B +ₐ ι y)`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component Nc'α ×_c Nc'β is adequate -/
theorem pm113_67 {W : Type*} {A : Set α} {B : Set β} {y : δ} (h : AdeqMul W (n₀c A) (n₀c B)) :
    (n₀c A ×ᶜ n₀c (B +ₐ ι y) : Set (Set γ)) = ((n₀c A ×ᶜ n₀c B : Set (Set W)) +ᶜ n₀c A) := by
  obtain ⟨X, hX, e⟩ := inner_mul_eq h
  rw [e, n₀c_cardMul_n₀c, n₀c_cardAdd_n₀c]
  apply nc_eq_nc_of_sm
  refine sm_trans (sm_clsTimes_comm A (B +ₐ ι y)) (sm_trans (sm_clsTimes_distrib A B (ι y)) ?_)
  exact sm_clsSum (sm_trans (sm_clsTimes_comm B A) (sm_symm hX)) (clsTimes_unit_sm A y)

/-- ✱113·671. \(\vdash .\mu \times _{c} (\nu +_{c} 1) = (\mu \times _{c} \nu ) +_{c} \mu \quad[*113·67·205.*110·4]\)

The `1` is in the type of `ν` (the standard adjustment for `+_c 1`, encoding decision 10), in
which it exists; the inner sum and product have adequate types (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components ν +_c 1 and μ ×_c ν are adequate, and the `1` exists (PM assumes every
type has a member, Introduction, Ch. I) -/
theorem pm113_671 {W₁ W₂ : Type*} [Nonempty β] {μ : Set (Set α)} {ν : Set (Set β)}
    (h₁ : AdeqAdd W₁ ν (one : Set (Set β))) (h₂ : AdeqMul W₂ μ ν) :
    (μ ×ᶜ (ν +ᶜ (one : Set (Set β)) : Set (Set W₁)) : Set (Set γ)) =
      ((μ ×ᶜ ν : Set (Set W₂)) +ᶜ μ) := by
  obtain ⟨b⟩ := ‹Nonempty β›
  by_cases hμ : ∃ A, μ = n₀c A
  swap
  · push Not at hμ
    rw [cardMul_eq_empty_of_left hμ, cardMul_eq_empty_of_left hμ, empty_cardAdd]
  by_cases hν : ∃ B, ν = n₀c B
  swap
  · push Not at hν
    rw [cardAdd_eq_empty_of_left hν, cardMul_empty, cardMul_eq_empty_of_right _ hν, empty_cardAdd]
  obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν
  rw [one_eq_n₀c_singleton b] at h₁ ⊢
  obtain ⟨Y, hY, e1⟩ := inner_add_eq h₁
  obtain ⟨X, hX, e2⟩ := inner_mul_eq h₂
  rw [e1, e2, n₀c_cardMul_n₀c, n₀c_cardAdd_n₀c]
  apply nc_eq_nc_of_sm
  refine sm_trans (sm_clsTimes hY (sm_refl A)) (sm_trans (sm_clsTimes_comm A (B +ₐ {b}))
    (sm_trans (sm_clsTimes_distrib A B {b}) ?_))
  refine sm_clsSum (sm_trans (sm_clsTimes_comm B A) (sm_symm hX)) ?_
  rw [← unitCls_eq_singleton]; exact clsTimes_unit_sm A b

section Helpers114

private theorem mem_selM {K : Set (Set α)} {M : α → Set α → Prop} :
    M ∈ sel memRel K ↔
      ((∀ x y A, M x A ∧ M y A → x = y) ∧ ∀ x A, M x A → x ∈ A) ∧ codom M = K := by
  rw [mem_sel_iff, mem_arrow_one_Cls]; exact Iff.rfl

private theorem nc_eq_zero_iff {X : Set α} : nc γ X = zero ↔ X = ∅ := by
  constructor
  · intro h
    have : (∅ : Set γ) ∈ nc γ X := by rw [h, zero_eq]; rfl
    obtain ⟨e⟩ := mem_nc_iff_equiv.1 this
    exact Set.eq_empty_iff_forall_notMem.2 fun x hx => (e.symm ⟨x, hx⟩).2
  · rintro rfl; exact zero_eq_nc_empty.symm

private theorem sel_nonempty_iff {K : Set (Set α)} :
    (sel memRel K).Nonempty ↔ ∀ A, A ∈ K → A.Nonempty := by
  constructor
  · rintro ⟨M, hM⟩ A hA
    obtain ⟨⟨-, h2⟩, h3⟩ := mem_selM.1 hM
    have : A ∈ codom M := by rw [h3]; exact hA
    obtain ⟨x, hx⟩ := this
    exact ⟨x, h2 x A hx⟩
  · exact sel_memRel_nonempty

private theorem piNc_ne_zero_iff {K : Set (Set α)} :
    piNc γ K ≠ zero ↔ ∀ A, A ∈ K → A.Nonempty := by
  rw [piNc, Ne, nc_eq_zero_iff, ← sel_nonempty_iff, Set.nonempty_iff_ne_empty]

private theorem piNc_eq_zero_iff {K : Set (Set α)} : piNc γ K = zero ↔ ∅ ∈ K := by
  rw [← not_iff_not, ← Ne, piNc_ne_zero_iff]
  constructor
  · intro h h0; exact Set.not_nonempty_empty (h ∅ h0)
  · intro h A hA
    rw [Set.nonempty_iff_ne_empty]; rintro rfl; exact h hA

private theorem sel_cres {K K' : Set (Set α)} {M : α → Set α → Prop} (hM : M ∈ sel memRel K')
    (h : K ⊆ K') : M ↾ K ∈ sel memRel K := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_selM.1 hM
  refine mem_selM.2 ⟨⟨fun x y A ⟨hx, hy⟩ => h1 x y A ⟨hx.1, hy.1⟩, fun x A hx => h2 x A hx.1⟩, ?_⟩
  ext A
  constructor
  · rintro ⟨x, -, hA⟩; exact hA
  · intro hA
    have : A ∈ codom M := by rw [h3]; exact h hA
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx, hA⟩

private theorem sel_unitCls {A : Set α} {M : α → Set α → Prop} :
    M ∈ sel memRel (ι A) ↔ ∃ x, x ∈ A ∧ M = x ↓ A := by
  constructor
  · intro hM
    obtain ⟨⟨h1, h2⟩, h3⟩ := mem_selM.1 hM
    have : A ∈ codom M := by rw [h3]; rfl
    obtain ⟨x, hx⟩ := this
    refine ⟨x, h2 x A hx, funext fun z => funext fun B => propext ⟨fun hz => ?_, ?_⟩⟩
    · have hB : B ∈ codom M := ⟨z, hz⟩
      rw [h3] at hB
      have hB' : B = A := hB
      subst hB'
      exact ⟨h1 z x B ⟨hz, hx⟩, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact hx
  · rintro ⟨x, hx, rfl⟩
    refine mem_selM.2 ⟨⟨fun a b B ⟨h1, h2⟩ => h1.1.trans h2.1.symm, ?_⟩, codom_couple x A⟩
    rintro a B ⟨rfl, rfl⟩; exact hx

private theorem sel_unitCls_sm (A : Set α) : sm (sel memRel (ι A)) A :=
  sm_of_injOn (fun x => x ↓ A) (fun x y _ _ h => (couple_eq_couple_iff.1 h).1)
    fun _ => sel_unitCls

private theorem sel_empty_eq : (sel memRel (∅ : Set (Set α))) = ι rNull := by
  ext M
  rw [mem_unitCls]
  constructor
  · intro hM
    obtain ⟨-, h3⟩ := mem_selM.1 hM
    funext x A
    apply propext
    exact ⟨fun h => by
      have : A ∈ codom M := ⟨x, h⟩
      rw [h3] at this; exact this.elim, fun h => absurd h (rNull_apply _ _)⟩
  · rintro rfl
    refine mem_selM.2 ⟨⟨fun _ _ _ h => absurd h.1 (rNull_apply _ _),
      fun _ _ h => absurd h (rNull_apply _ _)⟩, ?_⟩
    ext A; exact ⟨fun ⟨_, h⟩ => absurd h (rNull_apply _ _), fun h => h.elim⟩

/-- `κ ∩ λ = Λ . ⊃ . ∈_Δ'(κ ∪ λ) sm ∈_Δ'κ × ∈_Δ'λ` (✱114·301). -/
private theorem sel_union_sm {K L : Set (Set α)} (hd : K ∩ L = Λ) :
    sm (sel memRel (K ∪ L)) (sel memRel K ×ₐ sel memRel L) := by
  rw [inter_eq_null_iff] at hd
  refine sm_symm (sm_of_injOn (fun M => (M ↾ L) ↓ (M ↾ K)) ?_ ?_)
  · intro M M' hM hM' h
    obtain ⟨e1, e2⟩ := couple_eq_couple_iff.1 h
    obtain ⟨-, h3⟩ := mem_selM.1 hM
    obtain ⟨-, h3'⟩ := mem_selM.1 hM'
    funext x A
    apply propext
    constructor
    · intro hx
      have hA : A ∈ codom M := ⟨x, hx⟩
      rw [h3] at hA
      rcases hA with hA | hA
      · have : (M ↾ K) x A := ⟨hx, hA⟩
        rw [e2] at this; exact this.1
      · have : (M ↾ L) x A := ⟨hx, hA⟩
        rw [e1] at this; exact this.1
    · intro hx
      have hA : A ∈ codom M' := ⟨x, hx⟩
      rw [h3'] at hA
      rcases hA with hA | hA
      · have : (M' ↾ K) x A := ⟨hx, hA⟩
        rw [← e2] at this; exact this.1
      · have : (M' ↾ L) x A := ⟨hx, hA⟩
        rw [← e1] at this; exact this.1
  · intro z
    rw [mem_clsTimes]
    constructor
    · rintro ⟨X, Y, ⟨hX, hY⟩, rfl⟩
      obtain ⟨⟨x1, x2⟩, x3⟩ := mem_selM.1 hX
      obtain ⟨⟨y1, y2⟩, y3⟩ := mem_selM.1 hY
      have hXK : ∀ x A, X x A → A ∈ L := fun x A h => x3 ▸ ⟨x, h⟩
      have hYK : ∀ x A, Y x A → A ∈ K := fun x A h => y3 ▸ ⟨x, h⟩
      refine ⟨Y ⊍ X, mem_selM.2 ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rintro a b A ⟨ha | ha, hb | hb⟩
        · exact y1 a b A ⟨ha, hb⟩
        · exact absurd (hXK _ _ hb) (Set.disjoint_left.1 hd (hYK _ _ ha))
        · exact absurd (hXK _ _ ha) (Set.disjoint_left.1 hd (hYK _ _ hb))
        · exact x1 a b A ⟨ha, hb⟩
      · rintro a A (h | h)
        · exact y2 a A h
        · exact x2 a A h
      · ext A
        constructor
        · rintro ⟨a, h | h⟩
          · exact Or.inl (hYK _ _ h)
          · exact Or.inr (hXK _ _ h)
        · rintro (h | h)
          · rw [← y3] at h; obtain ⟨a, ha⟩ := h; exact ⟨a, Or.inl ha⟩
          · rw [← x3] at h; obtain ⟨a, ha⟩ := h; exact ⟨a, Or.inr ha⟩
      · congr 1
        · funext a A; apply propext
          constructor
          · intro h; exact ⟨Or.inr h, hXK _ _ h⟩
          · rintro ⟨h | h, hA⟩
            · exact absurd hA (Set.disjoint_left.1 hd (hYK _ _ h))
            · exact h
        · funext a A; apply propext
          constructor
          · intro h; exact ⟨Or.inl h, hYK _ _ h⟩
          · rintro ⟨h | h, hA⟩
            · exact h
            · exact absurd (hXK _ _ h) (Set.disjoint_left.1 hd hA)
    · rintro ⟨M, hM, rfl⟩
      exact ⟨M ↾ L, M ↾ K, ⟨sel_cres hM Set.subset_union_right,
        sel_cres hM Set.subset_union_left⟩, rfl⟩

/-- For `A` a unit class in the converse domain of a selection `M`, `xMA` iff `x ∈ A`. -/
private theorem sel_one_iff {K : Set (Set α)} {M : α → Set α → Prop} (hM : M ∈ sel memRel K)
    {A : Set α} (hA : A ∈ K) (h1 : A ∈ one) (x : α) : M x A ↔ x ∈ A := by
  obtain ⟨⟨-, h2⟩, h3⟩ := mem_selM.1 hM
  obtain ⟨a, rfl⟩ := h1
  constructor
  · exact h2 x _
  · intro hx
    have : ι a ∈ codom M := by rw [h3]; exact hA
    obtain ⟨y, hy⟩ := this
    have e1 : x = a := hx
    have e2 : y = a := h2 y _ hy
    rw [e1, ← e2]; rw [← e2] at hy; exact hy

private theorem sel_union_one_sm {K L : Set (Set α)} (hL : L ⊆ one) :
    sm (sel memRel (K ∪ L)) (sel memRel K) := by
  refine sm_symm (sm_of_injOn (fun M => M ↾ K) ?_ ?_)
  · intro M M' hM hM' h
    obtain ⟨-, h3⟩ := mem_selM.1 hM
    obtain ⟨-, h3'⟩ := mem_selM.1 hM'
    funext x A
    apply propext
    by_cases hA : A ∈ K
    · constructor
      · intro hx
        have : (M ↾ K) x A := ⟨hx, hA⟩
        rw [show M ↾ K = M' ↾ K from h] at this; exact this.1
      · intro hx
        have : (M' ↾ K) x A := ⟨hx, hA⟩
        rw [← show M ↾ K = M' ↾ K from h] at this; exact this.1
    · constructor
      · intro hx
        have hA' : A ∈ codom M := ⟨x, hx⟩
        rw [h3] at hA'
        have hAL := hA'.resolve_left hA
        exact (sel_one_iff hM' (Or.inr hAL) (hL hAL) x).2 ((sel_one_iff hM (Or.inr hAL) (hL hAL) x).1 hx)
      · intro hx
        have hA' : A ∈ codom M' := ⟨x, hx⟩
        rw [h3'] at hA'
        have hAL := hA'.resolve_left hA
        exact (sel_one_iff hM (Or.inr hAL) (hL hAL) x).2 ((sel_one_iff hM' (Or.inr hAL) (hL hAL) x).1 hx)
  · intro N
    constructor
    · intro hN
      obtain ⟨⟨n1, n2⟩, n3⟩ := mem_selM.1 hN
      have hNK : ∀ x A, N x A → A ∈ K := fun x A h => n3 ▸ ⟨x, h⟩
      refine ⟨fun x A => N x A ∨ ((A ∈ L ∧ A ∉ K) ∧ x ∈ A), mem_selM.2 ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rintro a b A ⟨ha | ⟨⟨hL1, hK1⟩, ha⟩, hb | ⟨⟨hL2, hK2⟩, hb⟩⟩
        · exact n1 a b A ⟨ha, hb⟩
        · exact absurd (hNK _ _ ha) hK2
        · exact absurd (hNK _ _ hb) hK1
        · obtain ⟨c, rfl⟩ := hL hL1
          exact (show a = c from ha).trans (show b = c from hb).symm
      · rintro a A (h | h)
        · exact n2 a A h
        · exact h.2
      · ext A
        constructor
        · rintro ⟨a, h | h⟩
          · exact Or.inl (hNK _ _ h)
          · exact Or.inr h.1.1
        · rintro (h | h)
          · rw [← n3] at h; obtain ⟨a, ha⟩ := h; exact ⟨a, Or.inl ha⟩
          · by_cases hK : A ∈ K
            · rw [← n3] at hK; obtain ⟨a, ha⟩ := hK; exact ⟨a, Or.inl ha⟩
            · obtain ⟨c, rfl⟩ := hL h
              exact ⟨c, Or.inr ⟨⟨h, hK⟩, rfl⟩⟩
      · funext x A; apply propext
        constructor
        · intro h; exact ⟨Or.inl h, hNK _ _ h⟩
        · rintro ⟨h | h, hA⟩
          · exact h
          · exact absurd hA h.1.2
    · rintro ⟨M, hM, rfl⟩
      exact sel_cres hM Set.subset_union_left

private theorem pm114_501_aux {L : Set (Set β)} {T : α → β → Prop} {R : β → Set β → Prop}
    (hR : R ∈ sel memRel L) :
    (T ↾ sumCls L) ⨾ (R ⨾ imgRelCnv (T ↾ sumCls L)) = T ⨾ (R ⨾ imgRelCnv T) := by
  obtain ⟨⟨-, r2⟩, r3⟩ := mem_selM.1 hR
  have hB : ∀ y B, R y B → B ⊆ sumCls L := fun y B h => subset_sumCls (r3 ▸ ⟨y, h⟩)
  have himg : ∀ B, B ⊆ sumCls L → (T ↾ sumCls L) ʻʻ B = T ʻʻ B := fun B hB => by
    ext x; exact ⟨fun ⟨y, hy, hxy, _⟩ => ⟨y, hy, hxy⟩, fun ⟨y, hy, hxy⟩ => ⟨y, hy, hxy, hB hy⟩⟩
  funext x A
  apply propext
  constructor
  · rintro ⟨y, ⟨hxy, -⟩, B, hyB, hA⟩
    refine ⟨y, hxy, B, hyB, ?_⟩
    show A = T ʻʻ B
    rw [← himg B (hB y B hyB)]; exact hA
  · rintro ⟨y, hxy, B, hyB, hA⟩
    refine ⟨y, ⟨hxy, hB y B hyB (r2 y B hyB)⟩, B, hyB, ?_⟩
    show A = (T ↾ sumCls L) ʻʻ B
    rw [himg B (hB y B hyB)]; exact hA

/-- `κ ∈ Cls² excl . ⊃ . ∈_Δ'∈_Δ''κ sm ∈_Δ's'κ` (cf. ✱85·44). -/
private theorem pm114_6_aux {K : Set (Set (Set α))} (hK : K ∈ Cls2excl) :
    sm (sel memRel (selRel memRel ʻʻ K)) (sel memRel (sumCls K)) := by
  by_cases h0 : ∅ ∈ sumCls K
  · obtain ⟨L, hL, h0L⟩ := h0
    have e1 : sel memRel (sumCls K) = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty, sel_nonempty_iff]
      intro h; exact Set.not_nonempty_empty (h ∅ ⟨L, hL, h0L⟩)
    have e2 : sel memRel (selRel memRel ʻʻ K) = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty, sel_nonempty_iff]
      intro h
      have := h _ ⟨L, hL, rfl⟩
      rw [sel_nonempty_iff] at this
      exact Set.not_nonempty_empty (this ∅ h0L)
    rw [e1, e2]; exact sm_of_equiv (Equiv.equivOfIsEmpty _ _)
  have hne : ∀ L, L ∈ K → (sel memRel L).Nonempty := fun L hL =>
    sel_nonempty_iff.2 fun A hA => by
      rw [Set.nonempty_iff_ne_empty]; rintro rfl; exact h0 ⟨L, hL, hA⟩
  have hexcl : ∀ L L' (A : Set α), L ∈ K → L' ∈ K → A ∈ L → A ∈ L' → L = L' := by
    intro L L' A hL hL' hA hA'
    by_contra hne'
    have h1 := hK L L' ⟨⟨hL, hL'⟩, hne'⟩
    have : A ∈ L ∩ L' := ⟨hA, hA'⟩
    rw [h1, Null_eq_empty] at this; exact this
  have hselinj : ∀ L L', L ∈ K → L' ∈ K → sel memRel L = sel memRel L' → L = L' := by
    intro L L' hL _ e
    obtain ⟨M, hM⟩ := hne L hL
    have hM' : M ∈ sel memRel L' := e ▸ hM
    exact (mem_selM.1 hM).2.symm.trans (mem_selM.1 hM').2
  refine sm_of_injOn
    (fun N => fun M U => ∃ L, (L ∈ K ∧ U = sel memRel L) ∧ M = N ↾ L) ?_ ?_
  · intro N N' hN hN' e
    have key : ∀ N N', N ∈ sel memRel (sumCls K) →
        (fun M U => ∃ L, (L ∈ K ∧ U = sel memRel L) ∧ M = N ↾ L) =
          (fun M U => ∃ L, (L ∈ K ∧ U = sel memRel L) ∧ M = N' ↾ L) →
        ∀ x A, N x A → N' x A := by
      intro N N' hN e x A hx
      have hA : A ∈ codom N := ⟨x, hx⟩
      rw [(mem_selM.1 hN).2] at hA
      obtain ⟨L, hL, hAL⟩ := hA
      have h1 : (fun M U => ∃ L, (L ∈ K ∧ U = sel memRel L) ∧ M = N ↾ L) (N ↾ L) (sel memRel L) :=
        ⟨L, ⟨hL, rfl⟩, rfl⟩
      rw [e] at h1
      obtain ⟨L', ⟨hL', e1⟩, e2⟩ := h1
      have := hselinj L L' hL hL' e1
      subst this
      have : (N ↾ L) x A := ⟨hx, hAL⟩
      rw [e2] at this
      exact this.1
    funext x A
    exact propext ⟨key N N' hN e x A, key N' N hN' e.symm x A⟩
  · intro Q
    constructor
    · intro hQ
      obtain ⟨⟨q1, q2⟩, q3⟩ := mem_selM.1 hQ
      have hQL : ∀ M U, Q M U → ∃ L, L ∈ K ∧ U = sel memRel L := fun M U h => by
        have : U ∈ codom Q := ⟨M, h⟩
        rw [q3] at this
        obtain ⟨L, hL, e⟩ := this
        exact ⟨L, hL, e⟩
      let N : α → Set α → Prop := fun x A => ∃ L M, (L ∈ K ∧ Q M (sel memRel L)) ∧ M x A
      have hMsel : ∀ M L, Q M (sel memRel L) → M ∈ sel memRel L := fun M L h => q2 M _ h
      have hN : N ∈ sel memRel (sumCls K) := by
        refine mem_selM.2 ⟨⟨?_, ?_⟩, ?_⟩
        · rintro x y A ⟨⟨L, M, ⟨hL, hQM⟩, hx⟩, ⟨L', M', ⟨hL', hQM'⟩, hy⟩⟩
          have hAL : A ∈ L := by rw [← (mem_selM.1 (hMsel M L hQM)).2]; exact ⟨x, hx⟩
          have hAL' : A ∈ L' := by rw [← (mem_selM.1 (hMsel M' L' hQM')).2]; exact ⟨y, hy⟩
          have := hexcl L L' A hL hL' hAL hAL'
          subst this
          have := q1 M M' _ ⟨hQM, hQM'⟩
          subst this
          exact (mem_selM.1 (hMsel M L hQM)).1.1 x y A ⟨hx, hy⟩
        · rintro x A ⟨L, M, ⟨-, hQM⟩, hx⟩
          exact (mem_selM.1 (hMsel M L hQM)).1.2 x A hx
        · ext A
          constructor
          · rintro ⟨x, L, M, ⟨hL, hQM⟩, hx⟩
            exact ⟨L, hL, by rw [← (mem_selM.1 (hMsel M L hQM)).2]; exact ⟨x, hx⟩⟩
          · rintro ⟨L, hL, hAL⟩
            have : sel memRel L ∈ codom Q := by rw [q3]; exact ⟨L, hL, rfl⟩
            obtain ⟨M, hQM⟩ := this
            have hA : A ∈ codom M := by rw [(mem_selM.1 (hMsel M L hQM)).2]; exact hAL
            obtain ⟨x, hx⟩ := hA
            exact ⟨x, L, M, ⟨hL, hQM⟩, hx⟩
      refine ⟨N, hN, ?_⟩
      have hres : ∀ L M, L ∈ K → Q M (sel memRel L) → M = N ↾ L := by
        intro L M hL hQM
        funext x A
        apply propext
        constructor
        · intro hx
          exact ⟨⟨L, M, ⟨hL, hQM⟩, hx⟩,
            by rw [← (mem_selM.1 (hMsel M L hQM)).2]; exact ⟨x, hx⟩⟩
        · rintro ⟨⟨L', M', ⟨hL', hQM'⟩, hx⟩, hAL⟩
          have hAL' : A ∈ L' := by rw [← (mem_selM.1 (hMsel M' L' hQM')).2]; exact ⟨x, hx⟩
          have := hexcl L L' A hL hL' hAL hAL'
          subst this
          rw [q1 M M' _ ⟨hQM, hQM'⟩]; exact hx
      funext M U
      apply propext
      constructor
      · intro hMU
        obtain ⟨L, hL, rfl⟩ := hQL M U hMU
        exact ⟨L, ⟨hL, rfl⟩, hres L M hL hMU⟩
      · rintro ⟨L, ⟨hL, rfl⟩, rfl⟩
        have : sel memRel L ∈ codom Q := by rw [q3]; exact ⟨L, hL, rfl⟩
        obtain ⟨M, hQM⟩ := this
        rw [← hres L M hL hQM]; exact hQM
    · rintro ⟨N, hN, rfl⟩
      refine mem_selM.2 ⟨⟨?_, ?_⟩, ?_⟩
      · rintro M M' U ⟨⟨L, ⟨hL, rfl⟩, rfl⟩, ⟨L', ⟨hL', e⟩, rfl⟩⟩
        rw [hselinj L L' hL hL' e]
      · rintro M U ⟨L, ⟨hL, rfl⟩, rfl⟩
        exact sel_cres hN (fun A hA => ⟨L, hL, hA⟩)
      · ext U
        constructor
        · rintro ⟨M, L, ⟨hL, rfl⟩, -⟩; exact ⟨L, hL, rfl⟩
        · rintro ⟨L, hL, rfl⟩; exact ⟨N ↾ L, L, ⟨hL, rfl⟩, rfl⟩

end Helpers114

/-!
## [✱114] The arithmetical product of a class of classes

*(Vol. 2, p. 124)*

> *Summary of* *114.
>
> The kind of multiplication defined in *113 cannot be extended beyond a finite number of factors. We therefore, as in the case of addition, introduce another definition, defining the product of the numbers of a class of classes, and capable of being applied to an infinite number of factors. We define the product of the numbers of members of \(\kappa\) as \(\text{Nc}ʻ{\in}_{\Delta }ʻ\kappa\); thus we put \[ \Pi \text{Nc}ʻ\kappa = \text{Nc}ʻ{\in}_{\Delta}ʻ\kappa \quad\text{Df}. \]
>
> It is to be observed that \(\Pi \text{Nc}ʻ\kappa\) is not a function of \(\text{Nc}ʻʻ\kappa\), because, if two members of \(\kappa\) have the same number, this will count only once in \(\text{Nc}ʻʻ\kappa\), but will count twice in \(\Pi \text{Nc}ʻ\kappa\).
>
> …

**Lean reading.** `ΠNc'κ` is `piNc γ K` (`= Nc'∈_Δ'κ`, with its type explicit), `∈_Δ'κ` is
`sel memRel K`, `∈_Δ''κ` the image under `selRel memRel`. Equations and `≠ 0` between products are
in free types (independent where nothing ties them). `Mult ax` (a theorem of Lean) is kept where
PM has it, at the type of the classes whose selections are used. As arguments of `×_c`, `Nc'α` is
`n₀c A` and inner products have adequate types (IIT); for `ΠNc'κ` PM's adequacy condition (i) is
vacuous (`Λ ∈ t₀'κ`, `pm114_31_aux_adeqPiNc`), so the IIT hypothesis is read as the existence of
the formal number in its actual type. In ✱114·601–·65 the relations `S_×`, `A`, `T`, `P`, `X`, `Y`
are given by their definitions as hypotheses (`Sx`, `Ar`, …), `Hp ✱114·N` is the hypothesis of
✱114·N, and the descriptions `S'α`, `S_×'α`, `R'z`, … are kept with `Desc`.

**Status.** proved (all propositions; ✱114·25·26·261·27·31·311·33·36·561·604·631 proved (reading), see their docstrings)
-/

/-- ✱114·01 (Df). \(\Pi \text{Nc}ʻ\kappa = \text{Nc}ʻ{\in}_{\Delta }ʻ\kappa \quad\text{Df}\) -/
theorem pm114_01 {K : Set (Set α)} : piNc γ K = nc γ (sel memRel K) := rfl

/-- ✱114·1. \(\vdash . \Pi \text{Nc}ʻ\kappa = \text{Nc}ʻ{\in}_{\Delta}ʻ\kappa \quad[(*114·01)]\)

PM gives the value of the descriptive function `ΠNc'κ`, so the statement keeps the description
(Basic §5). -/
theorem pm114_1 {K : Set (Set α)} :
    Desc (PiNc : Set (Set γ) → Set (Set α) → Prop) K (fun X => X = nc γ (sel memRel K)) :=
  (desc_PiNc K _).2 rfl

/-- ✱114·11. \(\vdash :\beta \in \Pi \text{Nc}ʻ\kappa . \equiv .\beta \text{ sm }{\in}_{\Delta}ʻ\kappa . \equiv .\beta \in \text{Nc}ʻ{\in}_{\Delta}ʻ\kappa \quad[*114·1.*100·31]\)

`β ∈ ΠNc'κ`, `β ∈ Nc'∈_Δ'κ` are attributive (in the type of `β`); the chain is a conjunction. -/
theorem pm114_11 {K : Set (Set α)} {B : Set γ} :
    (B ∈ piNc γ K ↔ sm B (sel memRel K)) ∧ (sm B (sel memRel K) ↔ B ∈ nc γ (sel memRel K)) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ✱114·12. \(\vdash .{\in}_{\Delta}ʻ\kappa \in \Pi \text{Nc}ʻ\kappa \quad[*100·3.*114·1]\) -/
theorem pm114_12 {K : Set (Set α)} : sel memRel K ∈ piNc (α → Set α → Prop) K := sm_refl _

/-- ✱114·2. \(\vdash .\Pi \text{Nc}ʻ\Lambda = 1 \quad[*83·15 .*101·2]\)

`1` is in the type of `ΠNc'Λ` (meaning). -/
theorem pm114_2 : piNc γ (Λ : Set (Set α)) = one := by
  rw [Null_eq_empty, piNc, sel_empty_eq, one_eq_nc_unitCls rNull]

/-- ✱114·21. \(\vdash .\Pi \text{Nc}ʻ\iota ʻ\alpha = \text{Nc}ʻ\alpha \quad[*83·41]\) -/
theorem pm114_21 {A : Set α} : piNc γ (ι A) = nc γ A :=
  nc_eq_nc_of_sm (sel_unitCls_sm A)

/-- ✱114·22. \(\vdash . \Pi \text{Nc}ʻ\iota ʻ\Lambda = 0 \quad[*114·21.*101·1]\) -/
theorem pm114_22 : piNc γ (ι (Λ : Set α)) = zero := by
  rw [piNc_eq_zero_iff, Null_eq_empty]; rfl

/-- ✱114·23. \(\vdash :\Lambda \in \kappa .\supset .\Pi \text{Nc}ʻ\kappa = 0 \quad[*83·11.*101·1]\) -/
theorem pm114_23 {K : Set (Set α)} : Λ ∈ K → piNc γ K = zero := by
  intro h; rw [piNc_eq_zero_iff]; rw [Null_eq_empty] at h; exact h

/-- ✱114·24. \(\vdash :\Pi \text{Nc}ʻ\lambda \neq 0.\kappa \subset \lambda .\supset .\Pi \text{Nc}ʻ\kappa \neq 0\)

The two products are in independent types (the proposition holds for any). -/
theorem pm114_24 {δ' : Type*} {K L : Set (Set α)} :
    piNc γ L ≠ zero ∧ K ⊆ L → piNc δ' K ≠ zero := by
  rintro ⟨h, hKL⟩
  rw [piNc_ne_zero_iff] at h ⊢
  exact fun A hA => h A (hKL hA)

/-- ✱114·25. \(\vdash \colon\ldotp \text{Mult ax}. \equiv :\Pi \text{Nc}ʻ\kappa = 0.\supset _{\kappa }.\Lambda \in \kappa\)

`Mult ax` is at the type of the members of the members of `κ`.

**Status.** proved (reading): `Mult ax` is a theorem of Lean (Basic §4), so the equivalence holds
with both sides proved. -/
theorem pm114_25 : MultAx α ↔ ∀ K : Set (Set α), piNc γ K = zero → Λ ∈ K := by
  constructor
  · intro _ K h; rw [piNc_eq_zero_iff] at h; rw [Null_eq_empty]; exact h
  · intro _; exact multAx_holds α

/-- ✱114·26. \(\vdash \colon\ldotp \text{Mult ax}. \equiv :\Pi \text{Nc}ʻ\kappa = 0. \equiv _{\kappa } .\Lambda \in \kappa \quad[*88·372.*101·1]\)

**Status.** proved (reading): `Mult ax` is a theorem of Lean (Basic §4), so the equivalence holds
with both sides proved. -/
theorem pm114_26 : MultAx α ↔ ∀ K : Set (Set α), (piNc γ K = zero ↔ Λ ∈ K) := by
  constructor
  · intro _ K; rw [piNc_eq_zero_iff, Null_eq_empty]
  · intro _; exact multAx_holds α

/-- ✱114·261. \(\vdash \colon\ldotp \text{Mult ax}. \equiv :\Pi \text{Nc}ʻ\kappa = 0. \equiv _{\kappa } .0\in \text{Nc}ʻʻ\kappa \quad[*114·26.*101·1]\)

`0 ∈ Nc''κ`: the image under the relation `Nc` (✱100·01), whose members are in a free type `δ`.

**Status.** proved (reading): `Mult ax` is a theorem of Lean (Basic §4), so the equivalence holds
with both sides proved. -/
theorem pm114_261 {δ' : Type*} :
    MultAx α ↔ ∀ K : Set (Set α),
      (piNc γ K = zero ↔ (zero : Set (Set δ')) ∈ (Nc : Set (Set δ') → Set α → Prop) ʻʻ K) := by
  constructor
  · intro _ K
    rw [piNc_eq_zero_iff]
    constructor
    · intro h; exact ⟨∅, h, zero_eq_nc_empty⟩
    · rintro ⟨A, hA, h⟩
      have : A = ∅ := nc_eq_zero_iff.1 (show zero = nc δ' A from h).symm
      rw [← this]; exact hA
  · intro _; exact multAx_holds α

/-- ✱114·27. \[\begin{aligned}&\vdash \colon\colon \text{Mult ax}. \equiv \colon\ldotp \alpha \in \kappa .\supset _{\alpha }.\exists !\alpha : \equiv _{\kappa } .\Pi \text{Nc}ʻ\kappa \neq 0\\ &[*114·26. \text{Transp}.*24·63]\end{aligned}\]

**Status.** proved (reading): `Mult ax` is a theorem of Lean (Basic §4), so the equivalence holds
with both sides proved. -/
theorem pm114_27 :
    MultAx α ↔ ∀ K : Set (Set α), ((∀ A, A ∈ K → A.Nonempty) ↔ piNc γ K ≠ zero) := by
  constructor
  · intro _ K; rw [piNc_ne_zero_iff]
  · intro _; exact multAx_holds α

/-- ✱114·3. \(\vdash :\kappa \neq \lambda .\supset .{\in}_{\Delta}ʻ(\iota ʻ{\in}_{\Delta}ʻ\kappa \cup \iota ʻ{\in}_{\Delta}ʻ\lambda )\text{ sm }{\in}_{\Delta}ʻ\kappa \times {\in}_{\Delta}ʻ\lambda\) -/
theorem pm114_3 {K L : Set (Set α)} :
    K ≠ L → sm (sel memRel (ι (sel memRel K) ∪ ι (sel memRel L))) (sel memRel K ×ₐ sel memRel L) := by
  intro hKL
  by_cases h : sel memRel K = sel memRel L
  · have hK : sel memRel K = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro M hM
      have hM' : M ∈ sel memRel L := h ▸ hM
      exact hKL ((mem_selM.1 hM).2.symm.trans (mem_selM.1 hM').2)
    rw [← h, hK, Set.union_self]
    have e1 : sel memRel (ι (∅ : Set (α → Set α → Prop))) = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty, sel_nonempty_iff]
      intro h'; exact Set.not_nonempty_empty (h' ∅ rfl)
    rw [e1, clsTimes_empty]
    exact sm_of_equiv (Equiv.equivOfIsEmpty _ _)
  · exact sm_symm (pm113_146 h)

/-- ✱114·301. \(\vdash :\kappa \cap \lambda = \Lambda .\supset .{\in}_{\Delta}ʻ(\kappa \cup \lambda )\text{ sm }{\in}_{\Delta}ʻ\kappa \times {\in}_{\Delta}ʻ\lambda\) -/
theorem pm114_301 {K L : Set (Set α)} :
    K ∩ L = Λ → sm (sel memRel (K ∪ L)) (sel memRel K ×ₐ sel memRel L) := sel_union_sm

/-- ✱114·31. \[\begin{aligned}&\vdash :\kappa \cap \lambda = \Lambda .\supset .\Pi \text{Nc}ʻ\kappa \times _{c} \Pi \text{Nc}ʻ\lambda = \Pi \text{Nc}ʻ(\kappa \cup \lambda )\\ &[*114·301·1.*113·25]\end{aligned}\]

The arguments `ΠNc'κ`, `ΠNc'λ` of `×_c` are arithmetical occurrences of formal numbers of the
primary group (IIT). PM's definition (i) of an adequate type for `ΠNc'κ`, `∃!ΠNc't₀'κ`, is
satisfied by every type, since `Λ ∈ t₀'κ` makes `ΠNc't₀'κ = 0` (`pm114_31_aux_adeqPiNc`); the
adequacy wanted (that the formal number exists in its actual type) is stated directly:
`∃!ΠNc'κ`, `∃!ΠNc'λ` in the types `W₁`, `W₂`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV), the adequacy of the actual
types of ΠNc'κ, ΠNc'λ being read as their existence (PM's definition (i) is vacuous for ΠNc). -/
theorem pm114_31 {W₁ W₂ : Type*} {K L : Set (Set α)} (h₁ : (piNc W₁ K).Nonempty)
    (h₂ : (piNc W₂ L).Nonempty) :
    K ∩ L = Λ → (piNc W₁ K ×ᶜ piNc W₂ L : Set (Set γ)) = piNc γ (K ∪ L) := by
  intro h
  obtain ⟨X, hX⟩ := h₁
  obtain ⟨Y, hY⟩ := h₂
  rw [show piNc W₁ K = n₀c X from nc_eq_n₀c_of_mem hX,
    show piNc W₂ L = n₀c Y from nc_eq_n₀c_of_mem hY, n₀c_cardMul_n₀c]
  exact nc_eq_nc_of_sm (sm_trans (sm_clsTimes hY hX) (sm_symm (sel_union_sm h)))

/-- PM's adequacy condition (i) for `ΠNc'κ` holds in every type (so it gives nothing). -/
theorem pm114_31_aux_adeqPiNc {W : Type*} (K : Set (Set α)) : AdeqPiNc W K := by
  refine ⟨∅, ?_⟩
  show sm ∅ (sel memRel (typ₀ K))
  have : sel memRel (typ₀ K) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty, sel_nonempty_iff]
    intro h
    exact Set.not_nonempty_empty (h ∅ (by rw [typ₀_eq_univ]; trivial))
  rw [this]; exact sm_of_equiv (Equiv.equivOfIsEmpty _ _)

/-- ✱114·311. \(\vdash .\Pi \text{Nc}ʻ(\kappa \cup \lambda ) = \Pi \text{Nc}ʻ\kappa \times _{c} \Pi \text{Nc}ʻ(\lambda - \kappa ) \quad[*114·31.*22·91]\)

**Status.** proved (reading): convention IIT, read as in ✱114·31 (existence of the arithmetical
components in their actual types). -/
theorem pm114_311 {W₁ W₂ : Type*} {K L : Set (Set α)} (h₁ : (piNc W₁ K).Nonempty)
    (h₂ : (piNc W₂ (L \ K)).Nonempty) :
    piNc γ (K ∪ L) = (piNc W₁ K ×ᶜ piNc W₂ (L \ K) : Set (Set γ)) := by
  rw [pm114_31 h₁ h₂ (by rw [inter_eq_null_iff]; exact Set.disjoint_sdiff_right),
    Set.union_sdiff_self]

/-- ✱114·32. \(\vdash :\Pi \text{Nc}ʻ(\kappa \cup \lambda ) \neq 0. \equiv .\Pi \text{Nc}ʻ\kappa \neq 0.\Pi \text{Nc}ʻ\lambda \neq 0\)

The three products are in independent types (the proposition holds for any). -/
theorem pm114_32 {γ₁ γ₂ : Type*} {K L : Set (Set α)} :
    piNc γ (K ∪ L) ≠ zero ↔ piNc γ₁ K ≠ zero ∧ piNc γ₂ L ≠ zero := by
  simp only [piNc_ne_zero_iff, Set.mem_union]
  exact ⟨fun h => ⟨fun A hA => h A (Or.inl hA), fun A hA => h A (Or.inr hA)⟩,
    fun h A hA => hA.elim (h.1 A) (h.2 A)⟩

/-- ✱114·33. \(\vdash :\alpha {\sim}\in \kappa .\supset .\Pi \text{Nc}ʻ(\kappa \cup \iota ʻ\alpha ) = \Pi \text{Nc}ʻ\kappa \times _{c} \text{Nc}ʻ\alpha \quad[*114·31·21]\)

`ΠNc'κ` as an argument of `×_c` exists in its type (IIT, as ✱114·31); `Nc'α` is `n₀c A`.

**Status.** proved (reading): convention IIT, read as in ✱114·31. -/
theorem pm114_33 {W : Type*} {K : Set (Set α)} {A : Set α} (hW : (piNc W K).Nonempty) :
    A ∉ K → piNc γ (K ∪ ι A) = (piNc W K ×ᶜ n₀c A : Set (Set γ)) := by
  intro hA
  obtain ⟨X, hX⟩ := hW
  rw [show piNc W K = n₀c X from nc_eq_n₀c_of_mem hX, n₀c_cardMul_n₀c]
  have hd : K ∩ ι A = Λ := by
    rw [inter_eq_null_iff, Set.disjoint_right]
    intro B hB hBK; rw [mem_unitCls.1 hB] at hBK; exact hA hBK
  exact nc_eq_nc_of_sm (sm_trans (sel_union_sm hd) (sm_clsTimes (sel_unitCls_sm A) (sm_symm hX)))

/-- ✱114·34. \[\begin{aligned}&\vdash :\Pi \text{Nc}ʻ\kappa \neq 0.\exists !\alpha . \equiv .\Pi \text{Nc}ʻ(\kappa \cup \iota ʻ\alpha ) \neq 0\\ &[*114·32·21.*101·14]\end{aligned}\] -/
theorem pm114_34 {γ₁ γ₂ : Type*} {K : Set (Set α)} {A : Set α} :
    piNc γ₁ K ≠ zero ∧ A.Nonempty ↔ piNc γ₂ (K ∪ ι A) ≠ zero := by
  simp only [piNc_ne_zero_iff, Set.mem_union]
  constructor
  · rintro ⟨h, hA⟩ B (hB | hB)
    · exact h B hB
    · rw [mem_unitCls.1 hB]; exact hA
  · intro h; exact ⟨fun B hB => h B (Or.inl hB), h A (Or.inr rfl)⟩

/-- ✱114·35. \(\vdash :\alpha \neq \beta .\supset .\Pi \text{Nc}ʻ(\iota ʻ\alpha \cup \iota ʻ\beta ) = \text{Nc}ʻ\alpha \times _{c} \text{Nc}ʻ\beta \quad[*114·33·21]\)

The arguments `Nc'α`, `Nc'β` of `×_c` are `n₀c A`, `n₀c B`. -/
theorem pm114_35 {A B : Set α} :
    A ≠ B → piNc γ (ι A ∪ ι B) = (n₀c A ×ᶜ n₀c B : Set (Set γ)) := by
  intro h
  rw [n₀c_cardMul_n₀c]
  exact nc_eq_nc_of_sm (sm_symm (pm113_146 h))

/-- ✱114·36. \[\begin{aligned}&\vdash :\alpha \neq \beta .\alpha \neq \gamma .\beta \neq \gamma .\supset .\Pi \text{Nc}ʻ(\iota ʻ\alpha \cup \iota ʻ\beta \cup \iota ʻ\gamma ) = \text{Nc}ʻ\alpha \times _{c} \text{Nc}ʻ\beta \times _{c} \text{Nc}ʻ\gamma \\ &[*114·33·35]\end{aligned}\]

The inner product is an arithmetical component with an adequate type `W` (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component Nc'α ×_c Nc'β is adequate -/
theorem pm114_36 {W : Type*} {A B G : Set α} (hW : AdeqMul W (n₀c A) (n₀c B)) :
    (A ≠ B ∧ A ≠ G) ∧ B ≠ G →
      piNc γ (ι A ∪ ι B ∪ ι G) = ((n₀c A ×ᶜ n₀c B : Set (Set W)) ×ᶜ n₀c G : Set (Set γ)) := by
  rintro ⟨⟨hAB, hAG⟩, hBG⟩
  rw [pm113_52 hW]
  have hd : (ι A ∪ ι B) ∩ ι G = Λ := by
    rw [inter_eq_null_iff, Set.disjoint_right]
    rintro X hX (hXA | hXB)
    · exact hAG ((mem_unitCls.1 hXA).symm.trans (mem_unitCls.1 hX))
    · exact hBG ((mem_unitCls.1 hXB).symm.trans (mem_unitCls.1 hX))
  refine nc_eq_nc_of_sm (sm_trans (sel_union_sm hd) (sm_clsTimes (sel_unitCls_sm G) ?_))
  exact sm_trans (sm_symm (pm113_146 hAB)) (sm_refl _)

/-- ✱114·4. \(\vdash :\lambda \subset 1.\supset .\Pi \text{Nc}ʻ\lambda = 1 \quad[*83·44]\)

`1` is in the type of `ΠNc'λ` (meaning). -/
theorem pm114_4 {L : Set (Set α)} : L ⊆ one → piNc γ L = one := by
  intro hL
  have hM0 : (fun x A => A ∈ L ∧ x ∈ A : α → Set α → Prop) ∈ sel memRel L := by
    refine mem_selM.2 ⟨⟨?_, fun x A h => h.2⟩, ?_⟩
    · rintro x y A ⟨⟨hA, hx⟩, ⟨-, hy⟩⟩
      obtain ⟨c, rfl⟩ := hL hA
      exact (show x = c from hx).trans (show y = c from hy).symm
    · ext A
      constructor
      · rintro ⟨x, hA, -⟩; exact hA
      · intro hA; obtain ⟨c, rfl⟩ := hL hA; exact ⟨c, hA, rfl⟩
  have e : sel memRel L = ι (fun x A => A ∈ L ∧ x ∈ A) := by
    ext M
    rw [mem_unitCls]
    constructor
    · intro hM
      funext x A; apply propext
      constructor
      · intro h
        have hA : A ∈ codom M := ⟨x, h⟩
        rw [(mem_selM.1 hM).2] at hA
        exact ⟨hA, (mem_selM.1 hM).1.2 x A h⟩
      · rintro ⟨hA, hx⟩; exact (sel_one_iff hM hA (hL hA) x).2 hx
    · rintro rfl; exact hM0
  rw [piNc, e, one_eq_nc_unitCls]

/-- ✱114·41. \(\vdash :\lambda \subset 1.\supset .\Pi \text{Nc}ʻ(\kappa \cup \lambda ) = \Pi \text{Nc}ʻ\kappa \quad[*83·57]\) -/
theorem pm114_41 {K L : Set (Set α)} : L ⊆ one → piNc γ (K ∪ L) = piNc γ K :=
  fun h => nc_eq_nc_of_sm (sel_union_one_sm h)

/-- ✱114·42. \(\vdash .\Pi \text{Nc}ʻ\kappa = \Pi \text{Nc}ʻ(\kappa -1)\) -/
theorem pm114_42 {K : Set (Set α)} : piNc γ K = piNc γ (K \ one) := by
  conv_lhs => rw [← Set.sdiff_union_inter K one]
  exact pm114_41 Set.inter_subset_right

/-- ✱114·43. \(\vdash .\Pi \text{Nc}ʻ(\kappa \cup \iotaʻʻ\alpha ) = \Pi \text{Nc}ʻ\kappa \quad[*114·41.*52·3]\) -/
theorem pm114_43 {K : Set (Set α)} {A : Set α} : piNc γ (K ∪ iota ʻʻ A) = piNc γ K := by
  refine pm114_41 ?_
  rintro _ ⟨x, -, rfl⟩
  exact ⟨x, rfl⟩

/-- ✱114·5. \(\vdash :T\in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda .\supset .(T\parallel \breve{T} _{\in })\upharpoonright {\in}_{\Delta}ʻ\lambda \in ({\in}_{\Delta}ʻ\kappa )\,\overline{\text{ sm }}\, ({\in}_{\Delta}ʻ\lambda )\)

`T̆_∈` is `imgRelCnv T`. -/
theorem pm114_5 {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop} :
    T ∈ smsmbar K L →
      (T ∥ imgRelCnv T) ↾ sel memRel L ∈ smbar (sel memRel K) (sel memRel L) := by
  intro hT
  obtain ⟨⟨hT1, hLc⟩, hK⟩ := mem_smsmbar_iff.1 hT
  obtain ⟨t1, t2⟩ := mem_arrow_one_one.1 hT1
  have hsub : ∀ B, B ∈ L → B ⊆ codom T := fun B hB => (subset_sumCls hB).trans hLc.le
  -- the image of a selection
  have hΦ : ∀ (R : β → Set β → Prop) x A,
      (T ⨾ (R ⨾ imgRelCnv T)) x A ↔ ∃ y B, (T x y ∧ R y B) ∧ A = T ʻʻ B := by
    intro R x A
    constructor
    · rintro ⟨y, hxy, B, hyB, hA⟩; exact ⟨y, B, ⟨hxy, hyB⟩, hA⟩
    · rintro ⟨y, B, ⟨hxy, hyB⟩, hA⟩; exact ⟨y, hxy, B, hyB, hA⟩
  have himg : ∀ R, R ∈ sel memRel L → T ⨾ (R ⨾ imgRelCnv T) ∈ sel memRel K := by
    intro R hR
    obtain ⟨⟨r1, r2⟩, r3⟩ := mem_selM.1 hR
    have hRL : ∀ y B, R y B → B ∈ L := fun y B h => r3 ▸ ⟨y, h⟩
    refine mem_selM.2 ⟨⟨?_, ?_⟩, ?_⟩
    · intro x x' A ⟨h1, h2⟩
      obtain ⟨y, B, ⟨hxy, hyB⟩, rfl⟩ := (hΦ R x A).1 h1
      obtain ⟨y', B', ⟨hxy', hyB'⟩, e⟩ := (hΦ R x' _).1 h2
      have hBB := img_inj hT1 (hsub B (hRL _ _ hyB)) (hsub B' (hRL _ _ hyB')) e
      subst hBB
      have := r1 y y' B ⟨hyB, hyB'⟩
      subst this
      exact t1 x x' y ⟨hxy, hxy'⟩
    · intro x A h
      obtain ⟨y, B, ⟨hxy, hyB⟩, rfl⟩ := (hΦ R x A).1 h
      exact ⟨y, r2 y B hyB, hxy⟩
    · rw [hK]
      ext A
      constructor
      · rintro ⟨x, h⟩
        obtain ⟨y, B, ⟨-, hyB⟩, rfl⟩ := (hΦ R x A).1 h
        exact ⟨B, hRL _ _ hyB, rfl⟩
      · rintro ⟨B, hB, rfl⟩
        have : B ∈ codom R := by rw [r3]; exact hB
        obtain ⟨y, hyB⟩ := this
        obtain ⟨x, hxy⟩ := hsub B hB (r2 y B hyB)
        exact ⟨x, (hΦ R x _).2 ⟨y, B, ⟨hxy, hyB⟩, rfl⟩⟩
  have hrel : ∀ P R, ((T ∥ imgRelCnv T) ↾ sel memRel L) P R ↔
      P = T ⨾ (R ⨾ imgRelCnv T) ∧ R ∈ sel memRel L := by
    intro P R
    exact ⟨fun ⟨h1, h2⟩ => ⟨(dpar_iff _ _ _ _).1 h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(dpar_iff _ _ _ _).2 h1, h2⟩⟩
  refine mem_smbar_iff.2 ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro P P' R ⟨h1, h2⟩
    exact ((hrel _ _).1 h1).1.trans ((hrel _ _).1 h2).1.symm
  · intro P R R' ⟨h1, h2⟩
    obtain ⟨e1, hR⟩ := (hrel _ _).1 h1
    obtain ⟨e2, hR'⟩ := (hrel _ _).1 h2
    have e : T ⨾ (R ⨾ imgRelCnv T) = T ⨾ (R' ⨾ imgRelCnv T) := e1.symm.trans e2
    have key : ∀ R R', R ∈ sel memRel L → R' ∈ sel memRel L →
        T ⨾ (R ⨾ imgRelCnv T) = T ⨾ (R' ⨾ imgRelCnv T) → ∀ y B, R y B → R' y B := by
      intro R R' hR hR' e y B hyB
      obtain ⟨⟨-, r2⟩, r3⟩ := mem_selM.1 hR
      obtain ⟨-, r3'⟩ := mem_selM.1 hR'
      have hB : B ∈ L := r3 ▸ ⟨y, hyB⟩
      obtain ⟨x, hxy⟩ := hsub B hB (r2 y B hyB)
      have h1 : (T ⨾ (R ⨾ imgRelCnv T)) x (T ʻʻ B) := (hΦ R x _).2 ⟨y, B, ⟨hxy, hyB⟩, rfl⟩
      rw [e] at h1
      obtain ⟨y', B', ⟨hxy', hyB'⟩, e'⟩ := (hΦ R' x _).1 h1
      have hB' : B' ∈ L := r3' ▸ ⟨y', hyB'⟩
      have := img_inj hT1 (hsub B hB) (hsub B' hB') e'
      subst this
      rw [t2 x y y' ⟨hxy, hxy'⟩]; exact hyB'
    funext y B
    exact propext ⟨key R R' hR hR' e y B, key R' R hR' hR e.symm y B⟩
  · ext P
    constructor
    · intro hP
      obtain ⟨⟨p1, p2⟩, p3⟩ := mem_selM.1 hP
      let R : β → Set β → Prop := fun y B => B ∈ L ∧ ∃ x, T x y ∧ P x (T ʻʻ B)
      have hR : R ∈ sel memRel L := by
        refine mem_selM.2 ⟨⟨?_, ?_⟩, ?_⟩
        · rintro y y' B ⟨⟨-, x, hxy, hx⟩, ⟨-, x', hxy', hx'⟩⟩
          have := p1 x x' _ ⟨hx, hx'⟩
          subst this
          exact t2 x y y' ⟨hxy, hxy'⟩
        · rintro y B ⟨hB, x, hxy, hx⟩
          obtain ⟨y', hy', hxy'⟩ := p2 x _ hx
          rw [t2 x y y' ⟨hxy, hxy'⟩]; exact hy'
        · ext B
          constructor
          · rintro ⟨y, hB, -⟩; exact hB
          · intro hB
            have : T ʻʻ B ∈ codom P := by rw [p3, hK]; exact ⟨B, hB, rfl⟩
            obtain ⟨x, hx⟩ := this
            obtain ⟨y, hy, hxy⟩ := p2 x _ hx
            exact ⟨y, hB, x, hxy, hx⟩
      refine ⟨R, (hrel _ _).2 ⟨?_, hR⟩⟩
      funext x A
      apply propext
      rw [hΦ]
      constructor
      · intro hxA
        have hA : A ∈ codom P := ⟨x, hxA⟩
        rw [p3, hK] at hA
        obtain ⟨B, hB, rfl⟩ := hA
        obtain ⟨y, hy, hxy⟩ := p2 x _ hxA
        exact ⟨y, B, ⟨hxy, hB, x, hxy, hxA⟩, rfl⟩
      · rintro ⟨y, B, ⟨hxy, -, x', hx'y, hx'⟩, rfl⟩
        rw [t1 x x' y ⟨hxy, hx'y⟩]; exact hx'
    · rintro ⟨R, hPR⟩
      obtain ⟨rfl, hR⟩ := (hrel _ _).1 hPR
      exact himg R hR
  · ext R
    constructor
    · intro hR; exact ⟨_, (hrel _ _).2 ⟨rfl, hR⟩⟩
    · rintro ⟨P, hP⟩; exact ((hrel _ _).1 hP).2

/-- ✱114·501. \(\vdash :S = T\upharpoonright sʻ\lambda .\supset .(S\parallel \breve{S} _\in )\upharpoonright {\in}_{\Delta}ʻ\lambda = (T\parallel \breve{T} _{\in })\upharpoonright {\in}_{\Delta}ʻ\lambda\) -/
theorem pm114_501 {L : Set (Set β)} {T S : α → β → Prop} :
    S = T ↾ sumCls L → (S ∥ imgRelCnv S) ↾ sel memRel L = (T ∥ imgRelCnv T) ↾ sel memRel L := by
  rintro rfl
  funext P R
  apply propext
  constructor
  · rintro ⟨h, hR⟩
    refine ⟨(dpar_iff _ _ _ _).2 (((dpar_iff _ _ _ _).1 h).trans ?_), hR⟩
    exact pm114_501_aux hR
  · rintro ⟨h, hR⟩
    refine ⟨(dpar_iff _ _ _ _).2 (((dpar_iff _ _ _ _).1 h).trans (pm114_501_aux hR).symm), hR⟩

/-- ✱114·51. \[\begin{aligned}&\vdash :T\upharpoonright sʻ\lambda \in \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda .\supset .(T\parallel \breve{T} _{\in })\upharpoonright {\in}_{\Delta}ʻ\lambda \in ({\in}_{\Delta}ʻ\kappa )\,\overline{\text{ sm }}\, ({\in}_{\Delta}ʻ\lambda )\\ &[*114·5·501]\end{aligned}\] -/
theorem pm114_51 {K : Set (Set α)} {L : Set (Set β)} {T : α → β → Prop} :
    T ↾ sumCls L ∈ smsmbar K L →
      (T ∥ imgRelCnv T) ↾ sel memRel L ∈ smbar (sel memRel K) (sel memRel L) := by
  intro h
  rw [← pm114_501 rfl]
  exact pm114_5 h

/-- ✱114·52. \(\vdash :\kappa \text{ sm }\text{ sm } \lambda .\supset .\Pi \text{Nc}ʻ\kappa = \Pi \text{Nc}ʻ\lambda .{\in}_{\Delta}ʻ\kappa \text{ sm }{\in}_{\Delta}ʻ\lambda \quad[*114·51 .*111·4]\)

The equation is in a free type `γ`. -/
theorem pm114_52 {K : Set (Set α)} {L : Set (Set β)} :
    smsm K L → piNc γ K = piNc γ L ∧ sm (sel memRel K) (sel memRel L) := by
  rintro ⟨T, hT⟩
  have h : sm (sel memRel K) (sel memRel L) := ⟨_, pm114_5 hT⟩
  exact ⟨nc_eq_nc_of_sm h, h⟩

/-- ✱114·53. \[\begin{aligned}\vdash \colon\colon &\text{Mult ax}.\supset \colon\ldotp \kappa ,\lambda \in \text{Cls}^{2} \text{excl}:\\ &(\exists S).S\in 1\rightarrow 1.S\,\unicode{x2abd}\, \text{ sm }.\text{D}ʻS = \kappa .\text{ᗡ}ʻS = \lambda :\supset .\Pi \text{Nc}ʻ\kappa = \Pi \text{Nc}ʻ\lambda\\ &[*114·52.*111·5]\end{aligned}\]

`Mult ax` at the type of ✱111·5. The prefix `(∃S)` extends to the `⊃` (Group II dots). -/
theorem pm114_53 {K : Set (Set α)} {L : Set (Set β)} :
    MultAx (α → β → Prop) →
      (K ∈ Cls2excl ∧ L ∈ Cls2excl) ∧ (∃ S : Set α → Set β → Prop,
          ((S ∈ arrow one one ∧ S ⪽ sm) ∧ dom S = K) ∧ codom S = L) →
        piNc γ K = piNc γ L := by
  rintro hM ⟨hKL, hS⟩
  exact (pm114_52 ((pm111_5 hM hKL).1.2 hS)).1

/-- ✱114·54. \[\begin{aligned}&\vdash \colon\ldotp \text{Mult ax}.\supset :\mu ,\nu \in \text{NC}.\kappa ,\lambda \in \mu \cap \text{Cl excl}ʻ\nu .\supset .\Pi \text{Nc}ʻ\kappa = \Pi \text{Nc}ʻ\lambda \\ &[*114·52.*111·53]\end{aligned}\] -/
theorem pm114_54 {β₁ β₂ : Type*} {μ : Set (Set (Set α))} {ν : Set (Set α)} {K L : Set (Set α)} :
    MultAx (α → α → Prop) →
      (μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ (K ∈ μ ∩ clExcl ν ∧ L ∈ μ ∩ clExcl ν) →
        piNc γ K = piNc γ L :=
  fun hM h => (pm114_52 (pm111_53 hM h)).1

/-- ✱114·56. \(\vdash .{\in}_{\Delta}ʻ\kappa \text{ sm }{\in}_{\Delta}ʻ\in \unicode{x21A7}ʻʻ\kappa .\Pi \text{Nc}ʻ\kappa = \Pi \text{Nc}ʻ\in \unicode{x21A7}ʻʻ\kappa \quad[*85·54]\)

The product of the two propositions; the equation is in a free type `γ`. -/
theorem pm114_56 {K : Set (Set α)} :
    sm (sel memRel K) (sel memRel (opL downCls memRel ʻʻ K)) ∧
      piNc γ K = piNc γ (opL downCls memRel ʻʻ K) := by
  have h : sm (sel memRel K) (sel memRel (opL downCls memRel ʻʻ K)) := by
    refine sm_symm (sm_of_injOn
      (fun M => fun r u => ∃ x A, M x A ∧ r = x ↓ A ∧ u = memRel ↧ A) ?_ ?_)
    · intro M M' hM hM' e
      funext x A
      apply propext
      constructor
      · intro hx
        have : (fun r u => ∃ x A, M x A ∧ r = x ↓ A ∧ u = memRel ↧ A) (x ↓ A) (memRel ↧ A) :=
          ⟨x, A, hx, rfl, rfl⟩
        rw [e] at this
        obtain ⟨x', A', hx', e1, -⟩ := this
        obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e1
        exact hx'
      · intro hx
        have : (fun r u => ∃ x A, M' x A ∧ r = x ↓ A ∧ u = memRel ↧ A) (x ↓ A) (memRel ↧ A) :=
          ⟨x, A, hx, rfl, rfl⟩
        rw [← e] at this
        obtain ⟨x', A', hx', e1, -⟩ := this
        obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e1
        exact hx'
    · intro Q
      constructor
      · intro hQ
        obtain ⟨⟨q1, q2⟩, q3⟩ := mem_selM.1 hQ
        let M : α → Set α → Prop := fun x A => A ∈ K ∧ Q (x ↓ A) (memRel ↧ A)
        have hM : M ∈ sel memRel K := by
          refine mem_selM.2 ⟨⟨?_, ?_⟩, ?_⟩
          · rintro x y A ⟨⟨-, hx⟩, ⟨-, hy⟩⟩
            exact (couple_eq_couple_iff.1 (q1 _ _ _ ⟨hx, hy⟩)).1
          · rintro x A ⟨-, hx⟩
            obtain ⟨z, hz, e⟩ := q2 _ _ hx
            rw [(couple_eq_couple_iff.1 e).1]; exact hz
          · ext A
            constructor
            · rintro ⟨x, hA, -⟩; exact hA
            · intro hA
              have : memRel ↧ A ∈ codom Q := by rw [q3]; exact ⟨A, hA, rfl⟩
              obtain ⟨r, hr⟩ := this
              obtain ⟨z, -, rfl⟩ := q2 _ _ hr
              exact ⟨z, hA, hr⟩
        refine ⟨M, hM, ?_⟩
        funext r u
        apply propext
        constructor
        · intro hru
          have hu : u ∈ codom Q := ⟨r, hru⟩
          rw [q3] at hu
          obtain ⟨A, hA, rfl⟩ := hu
          obtain ⟨z, -, rfl⟩ := q2 _ _ hru
          exact ⟨z, A, ⟨hA, hru⟩, rfl, rfl⟩
        · rintro ⟨x, A, ⟨-, h⟩, rfl, rfl⟩; exact h
      · rintro ⟨M, hM, rfl⟩
        obtain ⟨⟨m1, m2⟩, m3⟩ := mem_selM.1 hM
        refine mem_selM.2 ⟨⟨?_, ?_⟩, ?_⟩
        · rintro r r' u ⟨⟨x, A, hx, rfl, rfl⟩, ⟨x', A', hx', rfl, e⟩⟩
          have := downCls_inj e
          subst this
          rw [m1 x x' A ⟨hx, hx'⟩]
        · rintro r u ⟨x, A, hx, rfl, rfl⟩; exact ⟨x, m2 x A hx, rfl⟩
        · ext u
          constructor
          · rintro ⟨r, x, A, hx, -, rfl⟩
            exact ⟨A, m3 ▸ ⟨x, hx⟩, rfl⟩
          · rintro ⟨A, hA, rfl⟩
            rw [← m3] at hA
            obtain ⟨x, hx⟩ := hA
            exact ⟨x ↓ A, x, A, hx, rfl, rfl⟩
  exact ⟨h, nc_eq_nc_of_sm h⟩

/-- ✱114·561. \[\begin{aligned}&\vdash :S\in \kappa \,\overline{\text{ sm }}\, \lambda \cap \text{ᗡ}ʻʻʻ\text{ sm }.\supset .\in \unicode{x21A7}\mid S\mid \text{Cnv}ʻ(\in \unicode{x21A7})\in (\in \unicode{x21A7}ʻʻ\kappa )\,\overline{\text{ sm }}\, (e\unicode{x21A7}ʻʻ\lambda )\cap \text{ᗡ}ʻʻʻ\text{ sm }\\ &[*73·63.*85·601.*38·12.*33·432]\end{aligned}\]

As ✱112·231 (the e-text prints `e↧''λ` for `∈↧''λ`).

**Status.** proved (reading): transcription error: the e-text prints `ᗡ'''sm` for `Rl'sm` (twice)
and `e↧` for `∈↧`. -/
theorem pm114_561 {K : Set (Set α)} {L : Set (Set β)} {S : Set α → Set β → Prop} :
    S ∈ smbar K L ∩ rl sm →
      opL downCls memRel ⨾ S ⨾ (opL downCls memRel)˘ ∈
        smbar (opL downCls memRel ʻʻ K) (opL downCls memRel ʻʻ L) ∩ rl sm :=
  pm112_231

/-- ✱114·562. \(\vdash \colon\ldotp \text{Mult ax}.\supset : (\exists S).S\in 1\rightarrow 1.S\,\unicode{x2abd}\, \text{ sm }.\text{D}ʻS = \kappa .\text{ᗡ}ʻS = \lambda .\supset .\in \unicode{x21A7}ʻʻ\kappa \text{ sm }\text{ sm }\in \unicode{x21A7}ʻʻ\lambda\)

`Mult ax` at the type of ✱111·5 applied to `∈↧''κ`, `∈↧''λ`. -/
theorem pm114_562 {K : Set (Set α)} {L : Set (Set β)} :
    MultAx ((α → Set α → Prop) → (β → Set β → Prop) → Prop) →
      (∃ S : Set α → Set β → Prop, ((S ∈ arrow one one ∧ S ⪽ sm) ∧ dom S = K) ∧ codom S = L) →
        smsm (opL downCls memRel ʻʻ K) (opL downCls memRel ʻʻ L) := by
  rintro hM ⟨S, ⟨⟨h1, h2⟩, h3⟩, h4⟩
  have := pm114_561 (S := S) ⟨mem_smbar_iff.2 ⟨⟨h1, h3.symm⟩, h4.symm⟩, h2⟩
  have h5 := pm111_5 hM ⟨downImg_excl K, downImg_excl L⟩
  exact h5.1.2 (h5.2.2 ⟨_, this⟩)

/-- ✱114·57. \[\begin{aligned}\vdash \colon\ldotp &\text{Mult ax}.\supset :\\ &(\exists S).S\in 1\rightarrow 1.S\,\unicode{x2abd}\, \text{ sm }.\text{D}ʻS = \kappa .\text{ᗡ}ʻS = \lambda .\supset .\Pi \text{Nc}ʻ\kappa = \Pi \text{Nc}ʻ\lambda \end{aligned}\] -/
theorem pm114_57 {K : Set (Set α)} {L : Set (Set β)} :
    MultAx ((α → Set α → Prop) → (β → Set β → Prop) → Prop) →
      (∃ S : Set α → Set β → Prop, ((S ∈ arrow one one ∧ S ⪽ sm) ∧ dom S = K) ∧ codom S = L) →
        piNc γ K = piNc γ L := by
  intro hM hS
  rw [(pm114_56 (K := K)).2, (pm114_56 (K := L)).2]
  exact (pm114_52 (pm114_562 hM hS)).1

/-- ✱114·571. \[\begin{aligned}&\vdash \colon\ldotp \text{Mult ax}.\supset :\mu ,\nu \in \text{NC}.\kappa ,\lambda \in \mu \cap \text{Cl}ʻ\nu .\supset .\Pi \text{Nc}ʻ\kappa = \Pi \text{Nc}ʻ\lambda \\ &[*111·52 . *114·57]\end{aligned}\] -/
theorem pm114_571 {β₁ β₂ : Type*} {μ : Set (Set (Set α))} {ν : Set (Set α)} {K L : Set (Set α)} :
    MultAx ((α → Set α → Prop) → (α → Set α → Prop) → Prop) →
      (μ ∈ NC β₁ ∧ ν ∈ NC β₂) ∧ (K ∈ μ ∩ cl ν ∧ L ∈ μ ∩ cl ν) → piNc γ K = piNc γ L := by
  intro hM h
  obtain ⟨S, ⟨⟨hS1, hK⟩, hL⟩, hsm⟩ := pm111_52 h
  exact pm114_57 hM ⟨S, ⟨⟨hS1, hsm⟩, hK.symm⟩, hL.symm⟩

/-- ✱114·6. \(\vdash :\kappa \in \text{Cls}^{2} \text{excl}.\supset .\Pi \text{Nc}ʻ{\in}_{\Delta}ʻʻ\kappa = \Pi \text{Nc}ʻsʻ\kappa \quad[*85·44]\)

`∈_Δ''κ` is the image under the relation `∈_Δ` (`selRel memRel`). -/
theorem pm114_6 {K : Set (Set (Set α))} :
    K ∈ Cls2excl → piNc γ (selRel memRel ʻʻ K) = piNc γ (sumCls K) :=
  fun h => nc_eq_nc_of_sm (pm114_6_aux h)

section Helpers114b

/-- Under `S ↾ γ ∈ 1 → 1`, a description `S'α` with `α ∈ γ` reduces to a referent. -/
private theorem desc_unique_iff {G : Set (Set α)} {S : Set β → Set α → Prop}
    (h1 : S ↾ G ∈ arrow one one) {A : Set α} {ψ : Set β → Prop} :
    (A ∈ G ∧ Desc S A ψ) ↔ ∃ B, (A ∈ G ∧ S B A) ∧ ψ B := by
  constructor
  · rintro ⟨hA, b, hb, hψ⟩; exact ⟨b, ⟨hA, (hb b).2 rfl⟩, hψ⟩
  · rintro ⟨B, ⟨hA, hB⟩, hψ⟩
    refine ⟨hA, B, fun x => ⟨fun hx => ?_, fun e => e ▸ hB⟩, hψ⟩
    exact (mem_arrow_one_one.1 h1).1 x B A ⟨⟨hx, hA⟩, ⟨hB, hA⟩⟩

private theorem sel_unique {K : Set (Set α)} {M : α → Set α → Prop} (hM : M ∈ sel memRel K)
    {A : Set α} (hA : A ∈ K) : ∃ x, M x A ∧ ∀ x', M x' A ↔ x' = x := by
  obtain ⟨⟨m1, -⟩, m3⟩ := mem_selM.1 hM
  have : A ∈ codom M := by rw [m3]; exact hA
  obtain ⟨x, hx⟩ := this
  exact ⟨x, hx, fun x' => ⟨fun h => m1 x' x A ⟨h, hx⟩, fun e => e ▸ hx⟩⟩

/-- The relation `P = (Y ‖ X̆) | A | S̆_×` of ✱114·603, computed. -/
private theorem P_iff {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {Ar : (Set β → Set α → Prop) → Set α → Prop}
    {X : α → Set α → Prop} {Y : β → Set β → Prop} (h1 : S ↾ G ∈ arrow one one)
    (hSx : Sx = fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))
    (hAr : Ar = fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A))
    (hX : X ∈ sel memRel G) (hY : Y ∈ sel memRel (S ʻʻ G)) (M : β → α → Prop)
    (μ : Set (β → α → Prop)) :
    ((Y ∥ X˘) ⨾ Ar ⨾ Sx˘) M μ ↔
      ∃ A B x y, ((((A ∈ G ∧ S B A) ∧ X x A) ∧ Y y B) ∧ μ = A ×ₐ B) ∧ M = y ↓ x := by
  subst hSx hAr
  constructor
  · rintro ⟨A, ⟨R, hMR, hRA⟩, hμA⟩
    obtain ⟨B, ⟨hA, hB⟩, rfl⟩ := (desc_unique_iff h1).1 hRA
    obtain ⟨B', ⟨-, hB'⟩, rfl⟩ := (desc_unique_iff h1).1 hμA
    have hBB : B' = B := (mem_arrow_one_one.1 h1).1 B' B A ⟨⟨hB', hA⟩, ⟨hB, hA⟩⟩
    subst hBB
    obtain ⟨x, hx, ux⟩ := sel_unique hX hA
    obtain ⟨y, hy, uy⟩ := sel_unique hY ⟨A, hA, hB⟩
    refine ⟨A, B', x, y, ⟨⟨⟨⟨hA, hB⟩, hx⟩, hy⟩, rfl⟩, ?_⟩
    rw [(dpar_iff _ _ _ _).1 hMR]
    exact dpar_couple uy ux
  · rintro ⟨A, B, x, y, ⟨⟨⟨⟨hA, hB⟩, hx⟩, hy⟩, rfl⟩, rfl⟩
    obtain ⟨x', hx', ux⟩ := sel_unique hX hA
    obtain ⟨y', hy', uy⟩ := sel_unique hY ⟨A, hA, hB⟩
    have ex : x = x' := (ux x).1 hx
    have ey : y = y' := (uy y).1 hy
    subst ex ey
    refine ⟨A, ⟨B ↓ A, (dpar_iff _ _ _ _).2 (dpar_couple uy ux).symm, ?_⟩, ?_⟩
    · exact (desc_unique_iff h1).2 ⟨B, ⟨hA, hB⟩, rfl⟩
    · exact (desc_unique_iff h1).2 ⟨B, ⟨hA, hB⟩, rfl⟩

end Helpers114b

/-- ✱114·601. \[\begin{aligned}\vdash \colon\ldotp S\upharpoonright \gamma &\in 1\rightarrow 1.\gamma \subset \text{ᗡ}ʻS.\Lambda {\sim}\in \gamma .S_{\times } = \hat{\mu} \hat{\alpha} (\alpha \in \gamma .\mu = \alpha \times Sʻ\alpha ).\supset :\\ &S_{\times }\in 1\rightarrow 1.\text{ᗡ}ʻS_{\times } = \gamma .\text{D}ʻS_{\times } = \hat{\mu} \{(\exists \alpha ).\alpha \in \gamma .\mu = \alpha \times Sʻ\alpha\}:\\ &\alpha \in \gamma .\supset _{\alpha }.S_{\times }ʻ\alpha = \alpha \times Sʻ\alpha\end{aligned}\]

`γ` is a class of classes of `α`-things, `S` relates classes of `β`-things to them; `α × S'α`
is `A ×ₐ B` with `B = S'α` (a description, kept with `Desc`), and `S_×` is given by its
definition as a hypothesis. `S_×'α = α × S'α` has two descriptions, the first with the larger
scope. -/
theorem pm114_601 {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} :
    ((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B)) →
      ((Sx ∈ arrow one one ∧ codom Sx = G) ∧
          dom Sx = {μ | ∃ A, A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B)}) ∧
        ∀ A, A ∈ G → Desc Sx A (fun μ => Desc S A (fun B => μ = A ×ₐ B)) := by
  rintro ⟨⟨⟨h1, h2⟩, h3⟩, rfl⟩
  have hne : ∀ A, A ∈ G → A.Nonempty := fun A hA => by
    rw [Set.nonempty_iff_ne_empty]; rintro rfl; exact h3 (by rw [Null_eq_empty]; exact hA)
  refine ⟨⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, rfl⟩, ?_⟩
  · rintro μ μ' A ⟨h, h'⟩
    obtain ⟨B, ⟨hA, hB⟩, rfl⟩ := (desc_unique_iff h1).1 h
    obtain ⟨B', ⟨-, hB'⟩, rfl⟩ := (desc_unique_iff h1).1 h'
    rw [(mem_arrow_one_one.1 h1).1 B B' A ⟨⟨hB, hA⟩, ⟨hB', hA⟩⟩]
  · rintro μ A A' ⟨h, h'⟩
    obtain ⟨B, ⟨hA, hB⟩, rfl⟩ := (desc_unique_iff h1).1 h
    obtain ⟨B', ⟨hA', hB'⟩, e⟩ := (desc_unique_iff h1).1 h'
    have hBB : B = B' := pm113_181 ⟨⟨hne A hA, hne A' hA'⟩, e⟩
    subst hBB
    exact (mem_arrow_one_one.1 h1).2 B A A' ⟨⟨hB, hA⟩, ⟨hB', hA'⟩⟩
  · ext A
    constructor
    · rintro ⟨μ, hA, -⟩; exact hA
    · intro hA
      obtain ⟨B, hB⟩ := h2 hA
      exact ⟨A ×ₐ B, (desc_unique_iff h1).2 ⟨B, ⟨hA, hB⟩, rfl⟩⟩
  · intro A hA
    obtain ⟨B, hB⟩ := h2 hA
    have u : ∀ μ, (A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B)) ↔ μ = A ×ₐ B := fun μ => by
      rw [desc_unique_iff h1]
      constructor
      · rintro ⟨B', ⟨-, hB'⟩, rfl⟩
        rw [(mem_arrow_one_one.1 h1).1 B' B A ⟨⟨hB', hA⟩, ⟨hB, hA⟩⟩]
      · intro e; exact ⟨B, ⟨hA, hB⟩, e⟩
    rw [desc_of_unique u]
    exact ((desc_unique_iff (ψ := fun B' => A ×ₐ B = A ×ₐ B') h1).2 ⟨B, ⟨hA, hB⟩, rfl⟩).2

/-- ✱114·602. \(\vdash :\text{Hp}*114·601.A = \hat{R} \hat{\alpha} \{\alpha \in \gamma .R = (Sʻ\alpha )\downarrow \alpha\}.\supset .A\in 1\rightarrow 1.\text{ᗡ}ʻA = \gamma\)

`Hp ✱114·601` is its hypothesis; the relation `A` of PM is `Ar`. -/
theorem pm114_602 {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {Ar : (Set β → Set α → Prop) → Set α → Prop} :
    (((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))) ∧
      Ar = (fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A)) →
      Ar ∈ arrow one one ∧ codom Ar = G := by
  rintro ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, rfl⟩
  refine ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩
  · rintro R R' A ⟨h, h'⟩
    obtain ⟨B, ⟨hA, hB⟩, rfl⟩ := (desc_unique_iff h1).1 h
    obtain ⟨B', ⟨-, hB'⟩, rfl⟩ := (desc_unique_iff h1).1 h'
    rw [(mem_arrow_one_one.1 h1).1 B B' A ⟨⟨hB, hA⟩, ⟨hB', hA⟩⟩]
  · rintro R A A' ⟨h, h'⟩
    obtain ⟨B, -, rfl⟩ := (desc_unique_iff h1).1 h
    obtain ⟨B', -, e⟩ := (desc_unique_iff h1).1 h'
    exact (couple_eq_couple_iff.1 e).2
  · ext A
    constructor
    · rintro ⟨R, hA, -⟩; exact hA
    · intro hA
      obtain ⟨B, hB⟩ := h2 hA
      exact ⟨B ↓ A, (desc_unique_iff h1).2 ⟨B, ⟨hA, hB⟩, rfl⟩⟩

/-- ✱114·603. \(\vdash :\text{Hp}*114·602.X\in {\in}_{\Delta}ʻ\gamma .Y\in {\in}_{\Delta}ʻSʻʻ\gamma .P = (Y\parallel \breve{X} )\mid A\mid \breve{S} _{\times }.\supset .P\in {\in}_{\Delta}ʻ\text{D}ʻS_{\times }\)

`(Y ‖ X̆) | A | S̆_×` is `(Y ∥ X˘) ⨾ Ar ⨾ Sx˘`. -/
theorem pm114_603 {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {Ar : (Set β → Set α → Prop) → Set α → Prop}
    {X : α → Set α → Prop} {Y : β → Set β → Prop}
    {P : (β → α → Prop) → Set (β → α → Prop) → Prop} :
    (((((((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))) ∧
      Ar = (fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A))) ∧ X ∈ sel memRel G) ∧
        Y ∈ sel memRel (S ʻʻ G)) ∧ P = (Y ∥ X˘) ⨾ Ar ⨾ Sx˘) →
      P ∈ sel memRel (dom Sx) := by
  rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hSx⟩, hAr⟩, hX⟩, hY⟩, rfl⟩
  have hP := P_iff h1 hSx hAr hX hY
  have hne : ∀ A, A ∈ G → A.Nonempty := fun A hA => by
    rw [Set.nonempty_iff_ne_empty]; rintro rfl; exact h3 (by rw [Null_eq_empty]; exact hA)
  have hdom : ∀ μ, μ ∈ dom Sx ↔ ∃ A B, (A ∈ G ∧ S B A) ∧ μ = A ×ₐ B := by
    intro μ
    rw [hSx]
    exact ⟨fun ⟨A, h⟩ => let ⟨B, hB, e⟩ := (desc_unique_iff h1).1 h; ⟨A, B, hB, e⟩,
      fun ⟨A, B, hB, e⟩ => ⟨A, (desc_unique_iff h1).2 ⟨B, hB, e⟩⟩⟩
  refine mem_selM.2 ⟨⟨?_, ?_⟩, ?_⟩
  · intro M M' μ ⟨hM, hM'⟩
    obtain ⟨A, B, x, y, ⟨⟨⟨⟨hA, hB⟩, hx⟩, hy⟩, rfl⟩, rfl⟩ := (hP M μ).1 hM
    obtain ⟨A', B', x', y', ⟨⟨⟨⟨hA', hB'⟩, hx'⟩, hy'⟩, e⟩, rfl⟩ := (hP M' _).1 hM'
    have hBB : B = B' := pm113_181 ⟨⟨hne A hA, hne A' hA'⟩, e⟩
    subst hBB
    have hAA : A = A' := (mem_arrow_one_one.1 h1).2 B A A' ⟨⟨hB, hA⟩, ⟨hB', hA'⟩⟩
    subst hAA
    rw [(mem_selM.1 hX).1.1 x x' A ⟨hx, hx'⟩, (mem_selM.1 hY).1.1 y y' B ⟨hy, hy'⟩]
  · intro M μ hM
    obtain ⟨A, B, x, y, ⟨⟨⟨⟨hA, hB⟩, hx⟩, hy⟩, rfl⟩, rfl⟩ := (hP M μ).1 hM
    exact couple_mem_clsTimes.2 ⟨(mem_selM.1 hY).1.2 y B hy, (mem_selM.1 hX).1.2 x A hx⟩
  · ext μ
    rw [hdom]
    constructor
    · rintro ⟨M, hM⟩
      obtain ⟨A, B, x, y, ⟨⟨⟨hAB, -⟩, -⟩, e⟩, -⟩ := (hP M μ).1 hM
      exact ⟨A, B, hAB, e⟩
    · rintro ⟨A, B, ⟨hA, hB⟩, rfl⟩
      obtain ⟨x, hx, -⟩ := sel_unique hX hA
      obtain ⟨y, hy, -⟩ := sel_unique hY ⟨A, hA, hB⟩
      exact ⟨y ↓ x, (hP _ _).2 ⟨A, B, x, y, ⟨⟨⟨⟨hA, hB⟩, hx⟩, hy⟩, rfl⟩, rfl⟩⟩

/-- ✱114·604. \[\begin{aligned}\vdash :\text{Hp}*114·602.T = &\hat{P} \hat{Q}\{(\exists X,Y).X\in {\in}_{\Delta}ʻ\gamma .Y\in {\in}_{\Delta}ʻSʻʻ\gamma\}.\\ &\{Q = Y\downarrow X.P = (Y\parallel \breve{X} )\mid A\mid \breve{S} _{\times }\}.\\ &\supset .T\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻT = {\in}_{\Delta}ʻ\gamma \times {\in}_{\Delta}ʻSʻʻ\gamma .\text{D}ʻT\subset {\in}_{\Delta}ʻ\text{D}ʻS_{\times }\end{aligned}\]

`Hp ✱114·602` is its hypothesis. The e-text garbles the braces of the definition of `T`; it is
`P̂Q̂{(∃X, Y) . X ∈ ∈_Δ'γ . Y ∈ ∈_Δ'S''γ . Q = Y ↓ X . P = (Y ‖ X̆) | A | S̆_×}`, a product of four.

**Status.** proved (reading): transcription error: the braces of the definition of `T` are
garbled in the e-text; the definiens is read as one product inside `(∃X, Y)`. -/
theorem pm114_604 {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {Ar : (Set β → Set α → Prop) → Set α → Prop}
    {T : ((β → α → Prop) → Set (β → α → Prop) → Prop) →
      ((β → Set β → Prop) → (α → Set α → Prop) → Prop) → Prop} :
    ((((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))) ∧
      Ar = (fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A))) ∧
      T = (fun P Q => ∃ (X : α → Set α → Prop) (Y : β → Set β → Prop),
        ((X ∈ sel memRel G ∧ Y ∈ sel memRel (S ʻʻ G)) ∧ Q = Y ↓ X) ∧
          P = (Y ∥ X˘) ⨾ Ar ⨾ Sx˘) →
      (T ∈ arrow one Cls ∧ codom T = sel memRel G ×ₐ sel memRel (S ʻʻ G)) ∧
        dom T ⊆ sel memRel (dom Sx) := by
  rintro ⟨hp, rfl⟩
  refine ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩
  · rintro P P' Q ⟨⟨X, Y, ⟨-, rfl⟩, rfl⟩, ⟨X', Y', ⟨-, e⟩, rfl⟩⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    rfl
  · ext Q
    rw [mem_clsTimes]
    constructor
    · rintro ⟨P, X, Y, ⟨⟨hX, hY⟩, rfl⟩, -⟩; exact ⟨Y, X, ⟨hY, hX⟩, rfl⟩
    · rintro ⟨Y, X, ⟨hY, hX⟩, rfl⟩; exact ⟨_, X, Y, ⟨⟨hX, hY⟩, rfl⟩, rfl⟩
  · rintro P ⟨Q, X, Y, ⟨⟨hX, hY⟩, -⟩, rfl⟩
    exact pm114_603 ⟨⟨⟨hp, hX⟩, hY⟩, rfl⟩

/-- ✱114·605. \(\vdash :\text{Hp}*114·604.\supset .T\in \text{Cls}\rightarrow 1\)

`Hp ✱114·604` is its hypothesis. -/
theorem pm114_605 {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {Ar : (Set β → Set α → Prop) → Set α → Prop}
    {T : ((β → α → Prop) → Set (β → α → Prop) → Prop) →
      ((β → Set β → Prop) → (α → Set α → Prop) → Prop) → Prop} :
    ((((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))) ∧
      Ar = (fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A))) ∧
      T = (fun P Q => ∃ (X : α → Set α → Prop) (Y : β → Set β → Prop),
        ((X ∈ sel memRel G ∧ Y ∈ sel memRel (S ʻʻ G)) ∧ Q = Y ↓ X) ∧
          P = (Y ∥ X˘) ⨾ Ar ⨾ Sx˘) →
      T ∈ arrow Cls one := by
  rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hSx⟩, hAr⟩, rfl⟩
  have hne : ∀ A, A ∈ G → A.Nonempty := fun A hA => by
    rw [Set.nonempty_iff_ne_empty]; rintro rfl; exact h3 (by rw [Null_eq_empty]; exact hA)
  refine mem_arrow_Cls_one.2 ?_
  rintro P Q Q' ⟨⟨X, Y, ⟨⟨hX, hY⟩, rfl⟩, rfl⟩, ⟨X', Y', ⟨⟨hX', hY'⟩, rfl⟩, e⟩⟩
  have hP := P_iff h1 hSx hAr hX hY
  have hP' := P_iff h1 hSx hAr hX' hY'
  have key : ∀ A B, A ∈ G → S B A → ∀ x y x' y', X x A → Y y B → X' x' A → Y' y' B →
      x = x' ∧ y = y' := by
    intro A B hA hB x y x' y' hx hy hx' hy'
    have h := (hP (y ↓ x) (A ×ₐ B)).2 ⟨A, B, x, y, ⟨⟨⟨⟨hA, hB⟩, hx⟩, hy⟩, rfl⟩, rfl⟩
    rw [e] at h
    obtain ⟨A', B', x'', y'', ⟨⟨⟨⟨hA', hB'⟩, hx''⟩, hy''⟩, e1⟩, e2⟩ := (hP' _ _).1 h
    have hBB : B = B' := pm113_181 ⟨⟨hne A hA, hne A' hA'⟩, e1⟩
    subst hBB
    have hAA : A = A' := (mem_arrow_one_one.1 h1).2 B A A' ⟨⟨hB, hA⟩, ⟨hB', hA'⟩⟩
    subst hAA
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e2
    exact ⟨(mem_selM.1 hX').1.1 _ _ A ⟨hx'', hx'⟩, (mem_selM.1 hY').1.1 _ _ B ⟨hy'', hy'⟩⟩
  have eX : X = X' := by
    funext x A
    apply propext
    have hcX : ∀ x A, X x A → A ∈ G := fun x A h => (mem_selM.1 hX).2 ▸ ⟨x, h⟩
    have hcX' : ∀ x A, X' x A → A ∈ G := fun x A h => (mem_selM.1 hX').2 ▸ ⟨x, h⟩
    constructor
    · intro hx
      have hA := hcX x A hx
      obtain ⟨B, hB⟩ := h2 hA
      obtain ⟨y, hy, -⟩ := sel_unique hY ⟨A, hA, hB⟩
      obtain ⟨x', hx', -⟩ := sel_unique hX' hA
      obtain ⟨y', hy', -⟩ := sel_unique hY' ⟨A, hA, hB⟩
      rw [(key A B hA hB x y x' y' hx hy hx' hy').1]; exact hx'
    · intro hx'
      have hA := hcX' x A hx'
      obtain ⟨B, hB⟩ := h2 hA
      obtain ⟨y, hy, -⟩ := sel_unique hY ⟨A, hA, hB⟩
      obtain ⟨x0, hx0, -⟩ := sel_unique hX hA
      obtain ⟨y', hy', -⟩ := sel_unique hY' ⟨A, hA, hB⟩
      rw [← (key A B hA hB x0 y x y' hx0 hy hx' hy').1]; exact hx0
  have eY : Y = Y' := by
    funext y B
    apply propext
    have hcY : ∀ y B, Y y B → B ∈ S ʻʻ G := fun y B h => (mem_selM.1 hY).2 ▸ ⟨y, h⟩
    have hcY' : ∀ y B, Y' y B → B ∈ S ʻʻ G := fun y B h => (mem_selM.1 hY').2 ▸ ⟨y, h⟩
    constructor
    · intro hy
      obtain ⟨A, hA, hB⟩ := hcY y B hy
      obtain ⟨x, hx, -⟩ := sel_unique hX hA
      obtain ⟨x', hx', -⟩ := sel_unique hX' hA
      obtain ⟨y', hy', -⟩ := sel_unique hY' ⟨A, hA, hB⟩
      rw [(key A B hA hB x y x' y' hx hy hx' hy').2]; exact hy'
    · intro hy'
      obtain ⟨A, hA, hB⟩ := hcY' y B hy'
      obtain ⟨x, hx, -⟩ := sel_unique hX hA
      obtain ⟨x', hx', -⟩ := sel_unique hX' hA
      obtain ⟨y0, hy0, -⟩ := sel_unique hY ⟨A, hA, hB⟩
      rw [← (key A B hA hB x y0 x' y hx hy0 hx' hy').2]; exact hy0
  rw [eX, eY]


section Helpers114c

private theorem X_iff {P : (β → α → Prop) → Set (β → α → Prop) → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} (x : α) (A : Set α) :
    (iota˘ ⨾ Dcnv ⨾ P ⨾ Sx) x A ↔ ∃ μ M, (codom M = ι x ∧ P M μ) ∧ Sx μ A := by
  constructor
  · rintro ⟨μ, ⟨M, ⟨u, hu, hM⟩, hP⟩, hS⟩
    exact ⟨μ, M, ⟨(show u = codom M from hM).symm.trans (show u = ι x from hu), hP⟩, hS⟩
  · rintro ⟨μ, M, ⟨hc, hP⟩, hS⟩
    exact ⟨μ, ⟨M, ⟨ι x, show ι x = ι x from rfl, show ι x = codom M from hc.symm⟩, hP⟩, hS⟩

private theorem Y_iff {P : (β → α → Prop) → Set (β → α → Prop) → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {S : Set β → Set α → Prop} (y : β) (B : Set β) :
    (iota˘ ⨾ D ⨾ P ⨾ Sx ⨾ S˘) y B ↔ ∃ A μ M, ((dom M = ι y ∧ P M μ) ∧ Sx μ A) ∧ S B A := by
  constructor
  · rintro ⟨A, ⟨μ, ⟨M, ⟨u, hu, hM⟩, hP⟩, hSx⟩, hS⟩
    exact ⟨A, μ, M, ⟨⟨(show u = dom M from hM).symm.trans (show u = ι y from hu), hP⟩, hSx⟩, hS⟩
  · rintro ⟨A, μ, M, ⟨⟨hc, hP⟩, hSx⟩, hS⟩
    exact ⟨A, ⟨μ, ⟨M, ⟨ι y, show ι y = ι y from rfl, show ι y = dom M from hc.symm⟩, hP⟩, hSx⟩, hS⟩

/-- The facts used in ✱114·61–·614: for `α ∈ γ` with `S'α = B`, `P'(α × B)` is a couple `b ↓ a`. -/
private theorem P_couple {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {P : (β → α → Prop) → Set (β → α → Prop) → Prop}
    (h1 : S ↾ G ∈ arrow one one)
    (hSx : Sx = fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))
    (hP : P ∈ sel memRel (dom Sx)) {A : Set α} {B : Set β} (hA : A ∈ G) (hB : S B A) :
    ∃ a b, (a ∈ A ∧ b ∈ B) ∧ ∀ M, P M (A ×ₐ B) ↔ M = b ↓ a := by
  have hmem : A ×ₐ B ∈ dom Sx := ⟨A, by rw [hSx]; exact (desc_unique_iff h1).2 ⟨B, ⟨hA, hB⟩, rfl⟩⟩
  obtain ⟨M, hM, uM⟩ := sel_unique hP hmem
  have hMm : M ∈ A ×ₐ B := (mem_selM.1 hP).1.2 M _ hM
  obtain ⟨b, a, ⟨hb, ha⟩, rfl⟩ := mem_clsTimes.1 hMm
  exact ⟨a, b, ⟨ha, hb⟩, uM⟩

private theorem Sx_iff {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} (h1 : S ↾ G ∈ arrow one one)
    (hSx : Sx = fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B)) (μ : Set (β → α → Prop))
    (A : Set α) : Sx μ A ↔ ∃ B, (A ∈ G ∧ S B A) ∧ μ = A ×ₐ B := by
  rw [hSx]; exact desc_unique_iff h1

end Helpers114c

/-- ✱114·61. \[\begin{aligned}\vdash :\text{Hp}*114·602.P\in {\in}_{\Delta}ʻ\text{D}ʻS_{\times }.&X = \breve{\iota} \mid \text{ᗡ}\mid P\mid S_{\times }.Y = \breve{\iota} \mid \text{D}\mid P\mid S_{\times }\mid \breve{S} .\supset .\\ &X\in {\in}_{\Delta}ʻ\gamma .Y\in {\in}_{\Delta}ʻSʻʻ\gamma\end{aligned}\]

`X = ῐ | ᗡ | P | S_×` and `Y = ῐ | D | P | S_× | S̆` are relational products (`ῐ` is `iota˘`, `ᗡ`
and `D` the relations `Dcnv`, `D`). -/
theorem pm114_61 {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {Ar : (Set β → Set α → Prop) → Set α → Prop}
    {P : (β → α → Prop) → Set (β → α → Prop) → Prop} {X : α → Set α → Prop}
    {Y : β → Set β → Prop} :
    ((((((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))) ∧
      Ar = (fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A))) ∧ P ∈ sel memRel (dom Sx)) ∧
        X = iota˘ ⨾ Dcnv ⨾ P ⨾ Sx) ∧ Y = iota˘ ⨾ D ⨾ P ⨾ Sx ⨾ S˘ →
      X ∈ sel memRel G ∧ Y ∈ sel memRel (S ʻʻ G) := by
  rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hSx⟩, -⟩, hP⟩, rfl⟩, rfl⟩
  obtain ⟨s1, s2⟩ := mem_arrow_one_one.1 h1
  have hX : ∀ x A, (iota˘ ⨾ Dcnv ⨾ P ⨾ Sx) x A ↔ ∃ B a b, ((A ∈ G ∧ S B A) ∧
      (a ∈ A ∧ b ∈ B) ∧ P (b ↓ a) (A ×ₐ B)) ∧ x = a := by
    intro x A
    rw [X_iff]
    constructor
    · rintro ⟨μ, M, ⟨hc, hPM⟩, hS⟩
      obtain ⟨B, ⟨hA, hB⟩, rfl⟩ := (Sx_iff h1 hSx μ A).1 hS
      obtain ⟨a, b, ⟨ha, hb⟩, uM⟩ := P_couple h1 hSx hP hA hB
      have := (uM M).1 hPM
      subst this
      rw [codom_couple] at hc
      exact ⟨B, a, b, ⟨⟨hA, hB⟩, ⟨ha, hb⟩, (uM _).2 rfl⟩, (unitCls_injective hc).symm⟩
    · rintro ⟨B, a, b, ⟨⟨hA, hB⟩, -, hPM⟩, rfl⟩
      exact ⟨A ×ₐ B, b ↓ x, ⟨codom_couple b x, hPM⟩, (Sx_iff h1 hSx _ A).2 ⟨B, ⟨hA, hB⟩, rfl⟩⟩
  have hY : ∀ y B, (iota˘ ⨾ D ⨾ P ⨾ Sx ⨾ S˘) y B ↔ ∃ A a b, ((A ∈ G ∧ S B A) ∧
      (a ∈ A ∧ b ∈ B) ∧ P (b ↓ a) (A ×ₐ B)) ∧ y = b := by
    intro y B
    rw [Y_iff]
    constructor
    · rintro ⟨A, μ, M, ⟨⟨hc, hPM⟩, hS⟩, hBA⟩
      obtain ⟨B', ⟨hA, hB'⟩, rfl⟩ := (Sx_iff h1 hSx μ A).1 hS
      have : B' = B := s1 B' B A ⟨⟨hB', hA⟩, ⟨hBA, hA⟩⟩
      subst this
      obtain ⟨a, b, ⟨ha, hb⟩, uM⟩ := P_couple h1 hSx hP hA hB'
      have := (uM M).1 hPM
      subst this
      rw [dom_couple] at hc
      exact ⟨A, a, b, ⟨⟨hA, hB'⟩, ⟨ha, hb⟩, (uM _).2 rfl⟩, (unitCls_injective hc).symm⟩
    · rintro ⟨A, a, b, ⟨⟨hA, hB⟩, -, hPM⟩, rfl⟩
      exact ⟨A, A ×ₐ B, y ↓ a, ⟨⟨dom_couple y a, hPM⟩,
        (Sx_iff h1 hSx _ A).2 ⟨B, ⟨hA, hB⟩, rfl⟩⟩, hB⟩
  constructor
  · refine mem_selM.2 ⟨⟨?_, ?_⟩, ?_⟩
    · intro x x' A ⟨h, h'⟩
      obtain ⟨B, a, b, ⟨⟨hA, hB⟩, -, hPM⟩, rfl⟩ := (hX x A).1 h
      obtain ⟨B', a', b', ⟨⟨-, hB'⟩, -, hPM'⟩, rfl⟩ := (hX x' A).1 h'
      have : B' = B := s1 B' B A ⟨⟨hB', hA⟩, ⟨hB, hA⟩⟩
      subst this
      have := (mem_selM.1 hP).1.1 _ _ _ ⟨hPM, hPM'⟩
      exact (couple_eq_couple_iff.1 this).2
    · intro x A h
      obtain ⟨B, a, b, ⟨-, ⟨ha, -⟩, -⟩, rfl⟩ := (hX x A).1 h
      exact ha
    · ext A
      constructor
      · rintro ⟨x, h⟩
        obtain ⟨B, a, b, ⟨⟨hA, -⟩, -⟩, -⟩ := (hX x A).1 h
        exact hA
      · intro hA
        obtain ⟨B, hB⟩ := h2 hA
        obtain ⟨a, b, ⟨ha, hb⟩, uM⟩ := P_couple h1 hSx hP hA hB
        exact ⟨a, (hX a A).2 ⟨B, a, b, ⟨⟨hA, hB⟩, ⟨ha, hb⟩, (uM _).2 rfl⟩, rfl⟩⟩
  · refine mem_selM.2 ⟨⟨?_, ?_⟩, ?_⟩
    · intro y y' B ⟨h, h'⟩
      obtain ⟨A, a, b, ⟨⟨hA, hB⟩, -, hPM⟩, rfl⟩ := (hY y B).1 h
      obtain ⟨A', a', b', ⟨⟨hA', hB'⟩, -, hPM'⟩, rfl⟩ := (hY y' B).1 h'
      have : A = A' := s2 B A A' ⟨⟨hB, hA⟩, ⟨hB', hA'⟩⟩
      subst this
      have := (mem_selM.1 hP).1.1 _ _ _ ⟨hPM, hPM'⟩
      exact (couple_eq_couple_iff.1 this).1
    · intro y B h
      obtain ⟨A, a, b, ⟨-, ⟨-, hb⟩, -⟩, rfl⟩ := (hY y B).1 h
      exact hb
    · ext B
      constructor
      · rintro ⟨y, h⟩
        obtain ⟨A, a, b, ⟨⟨hA, hB⟩, -⟩, -⟩ := (hY y B).1 h
        exact ⟨A, hA, hB⟩
      · rintro ⟨A, hA, hB⟩
        obtain ⟨a, b, ⟨ha, hb⟩, uM⟩ := P_couple h1 hSx hP hA hB
        exact ⟨b, (hY b B).2 ⟨A, a, b, ⟨⟨hA, hB⟩, ⟨ha, hb⟩, (uM _).2 rfl⟩, rfl⟩⟩

/-- The values of the selectors `X`, `Y` of ✱114·61. -/
private theorem pm114_61_aux {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {P : (β → α → Prop) → Set (β → α → Prop) → Prop}
    (h1 : S ↾ G ∈ arrow one one)
    (hSx : Sx = fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))
    (hP : P ∈ sel memRel (dom Sx)) {A : Set α} {B : Set β} (hA : A ∈ G) (hB : S B A) {a : α}
    {b : β} (hPM : P (b ↓ a) (A ×ₐ B)) :
    (∀ x, (iota˘ ⨾ Dcnv ⨾ P ⨾ Sx) x A ↔ x = a) ∧ (∀ y, (iota˘ ⨾ D ⨾ P ⨾ Sx ⨾ S˘) y B ↔ y = b) := by
  obtain ⟨s1, s2⟩ := mem_arrow_one_one.1 h1
  obtain ⟨a', b', -, uM⟩ := P_couple h1 hSx hP hA hB
  obtain ⟨e1, e2⟩ := couple_eq_couple_iff.1 ((uM _).1 hPM)
  subst e1 e2
  constructor
  · intro x
    rw [X_iff]
    constructor
    · rintro ⟨μ, M, ⟨hc, hPM'⟩, hS⟩
      obtain ⟨B'', ⟨-, hB''⟩, rfl⟩ := (Sx_iff h1 hSx μ A).1 hS
      have : B'' = B := s1 B'' B A ⟨⟨hB'', hA⟩, ⟨hB, hA⟩⟩
      subst this
      rw [(uM M).1 hPM', codom_couple] at hc
      exact (unitCls_injective hc).symm
    · intro hx
      rw [hx]
      exact ⟨A ×ₐ B, b ↓ a, ⟨codom_couple b a, hPM⟩, (Sx_iff h1 hSx _ A).2 ⟨B, ⟨hA, hB⟩, rfl⟩⟩
  · intro y
    rw [Y_iff]
    constructor
    · rintro ⟨A', μ, M, ⟨⟨hc, hPM'⟩, hS⟩, hBA'⟩
      obtain ⟨B'', ⟨hA', hB''⟩, rfl⟩ := (Sx_iff h1 hSx μ A').1 hS
      have e1 : A' = A := s2 B A' A ⟨⟨hBA', hA'⟩, ⟨hB, hA⟩⟩
      subst e1
      have : B'' = B := s1 B'' B A' ⟨⟨hB'', hA'⟩, ⟨hB, hA'⟩⟩
      subst this
      rw [(uM M).1 hPM', dom_couple] at hc
      exact (unitCls_injective hc).symm
    · intro hy
      rw [hy]
      exact ⟨A, A ×ₐ B, b ↓ a, ⟨⟨dom_couple b a, hPM⟩,
        (Sx_iff h1 hSx _ A).2 ⟨B, ⟨hA, hB⟩, rfl⟩⟩, hB⟩

/-- ✱114·611. \(\vdash \colon\ldotp \text{Hp}*114·61.\supset :\alpha \in \gamma .\supset .(YʻSʻ\alpha )\downarrow (Xʻ\alpha ) = PʻS_{\times }ʻ\alpha\)

`(Y'S'α) ↓ (X'α) = P'S_×'α`: descriptions in order of scope; `α` is a real variable. -/
theorem pm114_611 {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {Ar : (Set β → Set α → Prop) → Set α → Prop}
    {P : (β → α → Prop) → Set (β → α → Prop) → Prop} {X : α → Set α → Prop}
    {Y : β → Set β → Prop} {A : Set α} :
    ((((((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))) ∧
      Ar = (fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A))) ∧ P ∈ sel memRel (dom Sx)) ∧
        X = iota˘ ⨾ Dcnv ⨾ P ⨾ Sx) ∧ Y = iota˘ ⨾ D ⨾ P ⨾ Sx ⨾ S˘ →
      (A ∈ G → Desc2 Y S A (fun y => Desc X A (fun x => Desc2 P Sx A (fun M => y ↓ x = M)))) := by
  rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, hSx⟩, -⟩, hP⟩, rfl⟩, rfl⟩ hA
  obtain ⟨B, hB⟩ := h2 hA
  obtain ⟨a, b, -, uM⟩ := P_couple h1 hSx hP hA hB
  obtain ⟨hXa, hYb⟩ := pm114_61_aux h1 hSx hP hA hB ((uM _).2 rfl)
  have uB : ∀ B', S B' A ↔ B' = B := fun B' =>
    ⟨fun h => (mem_arrow_one_one.1 h1).1 B' B A ⟨⟨h, hA⟩, ⟨hB, hA⟩⟩, fun e => e ▸ hB⟩
  have uμ : ∀ μ, Sx μ A ↔ μ = A ×ₐ B := fun μ => by
    rw [Sx_iff h1 hSx]
    constructor
    · rintro ⟨B', ⟨-, hB'⟩, rfl⟩; rw [(uB B').1 hB']
    · intro e; exact ⟨B, ⟨hA, hB⟩, e⟩
  rw [desc2_iff, desc_of_unique uB, desc_of_unique hYb, desc_of_unique hXa, desc2_iff,
    desc_of_unique uμ, desc_of_unique uM]

/-- ✱114·612. \(\vdash :\text{Hp} *114·61.\supset .(Y\parallel \breve{X} )\mid A\mid \breve{S} _{\times } = P\) -/
theorem pm114_612 {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {Ar : (Set β → Set α → Prop) → Set α → Prop}
    {P : (β → α → Prop) → Set (β → α → Prop) → Prop} {X : α → Set α → Prop}
    {Y : β → Set β → Prop} :
    ((((((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))) ∧
      Ar = (fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A))) ∧ P ∈ sel memRel (dom Sx)) ∧
        X = iota˘ ⨾ Dcnv ⨾ P ⨾ Sx) ∧ Y = iota˘ ⨾ D ⨾ P ⨾ Sx ⨾ S˘ →
      (Y ∥ X˘) ⨾ Ar ⨾ Sx˘ = P := by
  intro h
  obtain ⟨hX, hY⟩ := pm114_61 h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, hSx⟩, hAr⟩, hP⟩, rfl⟩, rfl⟩ := h
  have hPi := P_iff h1 hSx hAr hX hY
  funext M μ
  apply propext
  rw [hPi]
  constructor
  · rintro ⟨A, B, x, y, ⟨⟨⟨⟨hA, hB⟩, hx⟩, hy⟩, rfl⟩, rfl⟩
    obtain ⟨a, b, -, uM⟩ := P_couple h1 hSx hP hA hB
    obtain ⟨hXa, hYb⟩ := pm114_61_aux h1 hSx hP hA hB ((uM _).2 rfl)
    rw [(hXa x).1 hx, (hYb y).1 hy]
    exact (uM _).2 rfl
  · intro hM
    have hμ : μ ∈ codom P := ⟨M, hM⟩
    rw [(mem_selM.1 hP).2] at hμ
    obtain ⟨A, hS⟩ := hμ
    obtain ⟨B, ⟨hA, hB⟩, rfl⟩ := (Sx_iff h1 hSx μ A).1 hS
    obtain ⟨a, b, -, uM⟩ := P_couple h1 hSx hP hA hB
    obtain ⟨hXa, hYb⟩ := pm114_61_aux h1 hSx hP hA hB ((uM _).2 rfl)
    rw [(uM M).1 hM]
    exact ⟨A, B, a, b, ⟨⟨⟨⟨hA, hB⟩, (hXa a).2 rfl⟩, (hYb b).2 rfl⟩, rfl⟩, rfl⟩

/-- ✱114·613. \[\begin{aligned}\vdash :\text{Hp}*114·61.&\text{Hp}*114·604.\supset .\\ &P = Tʻ(Y\downarrow X).(Y\downarrow X)\in {\in}_{\Delta}ʻ\gamma \times {\in}_{\Delta}ʻSʻʻ\gamma \end{aligned}\]

`Hp ✱114·61 . Hp ✱114·604`: the conjunction of the two hypotheses (sharing `γ`, `S`, `S_×`, `A`).
`T'(Y ↓ X)` is a description. -/
theorem pm114_613 {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {Ar : (Set β → Set α → Prop) → Set α → Prop}
    {P : (β → α → Prop) → Set (β → α → Prop) → Prop} {X : α → Set α → Prop}
    {Y : β → Set β → Prop}
    {T : ((β → α → Prop) → Set (β → α → Prop) → Prop) →
      ((β → Set β → Prop) → (α → Set α → Prop) → Prop) → Prop} :
    (((((((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))) ∧
      Ar = (fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A))) ∧ P ∈ sel memRel (dom Sx)) ∧
        X = iota˘ ⨾ Dcnv ⨾ P ⨾ Sx) ∧ Y = iota˘ ⨾ D ⨾ P ⨾ Sx ⨾ S˘) ∧
      (((((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))) ∧
      Ar = (fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A))) ∧
      T = (fun P Q => ∃ (X : α → Set α → Prop) (Y : β → Set β → Prop),
        ((X ∈ sel memRel G ∧ Y ∈ sel memRel (S ʻʻ G)) ∧ Q = Y ↓ X) ∧
          P = (Y ∥ X˘) ⨾ Ar ⨾ Sx˘)) →
      Desc T (Y ↓ X) (fun Q => P = Q) ∧ Y ↓ X ∈ sel memRel G ×ₐ sel memRel (S ʻʻ G) := by
  rintro ⟨h61, -, rfl⟩
  obtain ⟨hX, hY⟩ := pm114_61 h61
  have e := pm114_612 h61
  refine ⟨?_, couple_mem_clsTimes.2 ⟨hY, hX⟩⟩
  have u : ∀ Q, (∃ (X' : α → Set α → Prop) (Y' : β → Set β → Prop),
      ((X' ∈ sel memRel G ∧ Y' ∈ sel memRel (S ʻʻ G)) ∧ Y ↓ X = Y' ↓ X') ∧
        Q = (Y' ∥ X'˘) ⨾ Ar ⨾ Sx˘) ↔ Q = P := by
    intro Q
    constructor
    · rintro ⟨X', Y', ⟨-, e'⟩, rfl⟩
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e'
      exact e
    · rintro rfl; exact ⟨X, Y, ⟨⟨hX, hY⟩, rfl⟩, e.symm⟩
  exact (desc_of_unique u).2 rfl

/-- ✱114·614. \(\vdash :\text{Hp}*114·604.\supset .{\in}_{\Delta}ʻ\text{D}ʻS_{\times }\subset \text{D}ʻT\) -/
theorem pm114_614 {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {Ar : (Set β → Set α → Prop) → Set α → Prop}
    {T : ((β → α → Prop) → Set (β → α → Prop) → Prop) →
      ((β → Set β → Prop) → (α → Set α → Prop) → Prop) → Prop} :
    ((((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))) ∧
      Ar = (fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A))) ∧
      T = (fun P Q => ∃ (X : α → Set α → Prop) (Y : β → Set β → Prop),
        ((X ∈ sel memRel G ∧ Y ∈ sel memRel (S ʻʻ G)) ∧ Q = Y ↓ X) ∧
          P = (Y ∥ X˘) ⨾ Ar ⨾ Sx˘) →
      sel memRel (dom Sx) ⊆ dom T := by
  rintro ⟨hp, rfl⟩ P hP
  have := pm114_61 (P := P) (X := iota˘ ⨾ Dcnv ⨾ P ⨾ Sx) (Y := iota˘ ⨾ D ⨾ P ⨾ Sx ⨾ S˘)
    ⟨⟨⟨hp, hP⟩, rfl⟩, rfl⟩
  exact ⟨_, _, _, ⟨⟨this.1, this.2⟩, rfl⟩, (pm114_612 ⟨⟨⟨hp, hP⟩, rfl⟩, rfl⟩).symm⟩

/-- ✱114·62. \[\begin{aligned}&\vdash :\text{Hp}*114·604.\supset .T\in 1\rightarrow 1.\text{D}ʻT = {\in}_{\Delta}ʻ\text{D}ʻS_{\times }.\text{ᗡ}ʻT = {\in}_{\Delta}ʻ\gamma \times {\in}_{\Delta}ʻSʻʻ\gamma \\ &[*114·604·605·614]\end{aligned}\] -/
theorem pm114_62 {G : Set (Set α)} {S : Set β → Set α → Prop}
    {Sx : Set (β → α → Prop) → Set α → Prop} {Ar : (Set β → Set α → Prop) → Set α → Prop}
    {T : ((β → α → Prop) → Set (β → α → Prop) → Prop) →
      ((β → Set β → Prop) → (α → Set α → Prop) → Prop) → Prop} :
    ((((S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G) ∧
        Sx = (fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))) ∧
      Ar = (fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A))) ∧
      T = (fun P Q => ∃ (X : α → Set α → Prop) (Y : β → Set β → Prop),
        ((X ∈ sel memRel G ∧ Y ∈ sel memRel (S ʻʻ G)) ∧ Q = Y ↓ X) ∧
          P = (Y ∥ X˘) ⨾ Ar ⨾ Sx˘) →
      (T ∈ arrow one one ∧ dom T = sel memRel (dom Sx)) ∧
        codom T = sel memRel G ×ₐ sel memRel (S ʻʻ G) := by
  intro h
  obtain ⟨⟨h1, h2⟩, h3⟩ := pm114_604 h
  have h4 := pm114_605 h
  have h5 := pm114_614 h
  exact ⟨⟨mem_arrow_one_one.2 ⟨mem_arrow_one_Cls.1 h1, mem_arrow_Cls_one.1 h4⟩,
    h3.antisymm h5⟩, h2⟩

/-- ✱114·621. \[\begin{aligned}\vdash :S\upharpoonright \gamma \in 1\rightarrow 1.&\gamma \subset \text{ᗡ}ʻS.\Lambda {\sim}\in \gamma .\supset .\\ &{\in}_{\Delta}ʻ\hat{\mu}\{(\exists \alpha ).\alpha \in \gamma .\mu = \alpha \times Sʻ\alpha\}\text{ sm }{\in}_{\Delta}ʻ\gamma \times {\in}_{\Delta}ʻSʻʻ\gamma \\ &[*114·62·601]\end{aligned}\] -/
theorem pm114_621 {G : Set (Set α)} {S : Set β → Set α → Prop} :
    (S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ Λ ∉ G →
      sm (sel memRel {μ | ∃ A, A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B)})
        (sel memRel G ×ₐ sel memRel (S ʻʻ G)) := by
  intro h
  have h601 := pm114_601 (Sx := fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B)) ⟨h, rfl⟩
  have h62 := pm114_62 (Sx := fun μ A => A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B))
    (Ar := fun R A => A ∈ G ∧ Desc S A (fun B => R = B ↓ A)) (T := _) ⟨⟨⟨h, rfl⟩, rfl⟩, rfl⟩
  rw [← h601.1.2]
  exact ⟨_, mem_smbar_iff.2 ⟨⟨h62.1.1, h62.1.2.symm⟩, h62.2.symm⟩⟩

/-- ✱114·63. \[\begin{aligned}\vdash :S\upharpoonright \gamma \in 1\rightarrow& 1.\gamma \subset \text{ᗡ}ʻS.\supset .\\ &{\in}_{\Delta}ʻ\hat{\mu}\{(\exists \alpha ).\alpha \in \gamma .\mu = \alpha \times Sʻ\alpha\}\text{ sm }{\in}_{\Delta}ʻ\gamma \times {\in}_{\Delta}ʻSʻʻ\gamma\end{aligned}\] -/
theorem pm114_63 {G : Set (Set α)} {S : Set β → Set α → Prop} :
    S ↾ G ∈ arrow one one ∧ G ⊆ codom S →
      sm (sel memRel {μ | ∃ A, A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B)})
        (sel memRel G ×ₐ sel memRel (S ʻʻ G)) := by
  intro h
  by_cases hΛ : Λ ∈ G
  · rw [Null_eq_empty] at hΛ
    obtain ⟨B, hB⟩ := h.2 hΛ
    have e1 : sel memRel {μ | ∃ A, A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B)} = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty, sel_nonempty_iff]
      intro h'
      obtain ⟨R, hR⟩ := h' (∅ ×ₐ B) ⟨∅, (desc_unique_iff h.1).2 ⟨B, ⟨hΛ, hB⟩, rfl⟩⟩
      obtain ⟨x, y, ⟨-, hy⟩, -⟩ := mem_clsTimes.1 hR
      exact hy
    have e2 : sel memRel G = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty, sel_nonempty_iff]
      intro h'; exact Set.not_nonempty_empty (h' ∅ hΛ)
    rw [e1, e2, show (∅ : Set (α → Set α → Prop)) ×ₐ sel memRel (S ʻʻ G) = ∅ from by
      ext R; simp only [Set.mem_empty_iff_false, iff_false]; intro hR
      obtain ⟨x, y, ⟨-, hy⟩, -⟩ := mem_clsTimes.1 hR; exact hy]
    exact sm_of_equiv (Equiv.equivOfIsEmpty _ _)
  · exact pm114_621 ⟨h, hΛ⟩

/-- ✱114·631. \(\vdash .{\in}_{\Delta}ʻ\hat{\mu}\{(\exists \alpha ).\alpha \in \gamma .\mu = \alpha \times \alpha \}\text{ sm }{\in}_{\Delta}ʻ\alpha \times {\in}_{\Delta}ʻ\alpha \quad\left[*114·63 \frac{I}{S}\right]\)

`S` is `I` (so `S'α = α`, `S''γ = γ`).

**Status.** proved (reading): transcription error: the e-text prints `∈_Δ'α × ∈_Δ'α` for
`∈_Δ'γ × ∈_Δ'γ` (✱114·63 with `I` for `S` gives `S''γ = γ`). -/
theorem pm114_631 {G : Set (Set α)} :
    sm (sel memRel {μ | ∃ A, A ∈ G ∧ μ = A ×ₐ A}) (sel memRel G ×ₐ sel memRel G) := by
  have hI : (I : Set α → Set α → Prop) ↾ G ∈ arrow one one :=
    mem_arrow_one_one.2 ⟨fun x y z ⟨h1, h2⟩ => (show x = z from h1.1).trans (show y = z from h2.1).symm,
      fun x y z ⟨h1, h2⟩ => (show x = y from h1.1).symm.trans (show x = z from h2.1)⟩
  have h := pm114_63 (S := I) ⟨hI, fun A _ => ⟨A, rfl⟩⟩
  have e1 : {μ | ∃ A, A ∈ G ∧ Desc I A (fun B => μ = A ×ₐ B)} = {μ | ∃ A, A ∈ G ∧ μ = A ×ₐ A} := by
    ext μ; simp only [Set.mem_ofPred_eq, desc_I]
  have e2 : (I : Set α → Set α → Prop) ʻʻ G = G := by
    ext A; exact ⟨fun ⟨B, hB, e⟩ => (show A = B from e) ▸ hB, fun hA => ⟨A, hA, rfl⟩⟩
  rw [e1, e2] at h
  exact h

/-- ✱114·632. \[\begin{aligned}\vdash :S\upharpoonright &\gamma \in 1\rightarrow 1.\gamma \subset \text{ᗡ}ʻS.\gamma \cap Sʻʻ\gamma = \Lambda .\supset .\\ &{\in}_{\Delta}ʻ\hat{\mu}\{(\exists \alpha ).\alpha \in \gamma .\mu = \alpha \times Sʻ\alpha\}\text{ sm }{\in}_{\Delta}ʻ(\gamma \cup Sʻʻ\gamma ) \quad[*114·63·301]\end{aligned}\]

`γ ∩ S''γ` puts `S'α` in the type of `α`. -/
theorem pm114_632 {G : Set (Set α)} {S : Set α → Set α → Prop} :
    (S ↾ G ∈ arrow one one ∧ G ⊆ codom S) ∧ G ∩ S ʻʻ G = Λ →
      sm (sel memRel {μ | ∃ A, A ∈ G ∧ Desc S A (fun B => μ = A ×ₐ B)})
        (sel memRel (G ∪ S ʻʻ G)) :=
  fun ⟨h, hd⟩ => sm_trans (pm114_63 h) (sm_symm (sel_union_sm hd))

/-- ✱114·64. \[\begin{align}\vdash :(Rʻʻ\gamma )&\upharpoonleft R,S\upharpoonright \gamma \in 1\rightarrow 1.\gamma \subset \text{ᗡ}ʻR.\gamma \subset \text{ᗡ}ʻS.\supset .\\ &{\in}_{\Delta}ʻRʻʻ\gamma \times {\in}_{\Delta}ʻSʻʻ\gamma \text{ sm }{\in}_{\Delta}ʻ\hat{\mu} \{(\exists z).z\in \gamma .\mu = Rʻz \times Sʻz\}\end{align}\]

`(R''γ) ↿ R, S ↾ γ ∈ 1 → 1` is a product (the relations are of different types); `R'z × S'z`
has two descriptions, the first with the larger scope. -/
theorem pm114_64 {G : Set δ} {R : Set α → δ → Prop} {S : Set β → δ → Prop} :
    (((R ʻʻ G) ◁ R ∈ arrow one one ∧ S ↾ G ∈ arrow one one) ∧ G ⊆ codom R) ∧ G ⊆ codom S →
      sm (sel memRel (R ʻʻ G) ×ₐ sel memRel (S ʻʻ G))
        (sel memRel {μ | ∃ z, z ∈ G ∧ Desc R z (fun A => Desc S z (fun B => μ = A ×ₐ B))}) := by
  rintro ⟨⟨⟨hR, hS⟩, hGR⟩, hGS⟩
  obtain ⟨r1, r2⟩ := mem_arrow_one_one.1 hR
  obtain ⟨s1, s2⟩ := mem_arrow_one_one.1 hS
  -- `A ∈ R''γ` and `ARz` give `z ∈ γ`
  have hz : ∀ A z, A ∈ R ʻʻ G → R A z → z ∈ G := by
    rintro A z ⟨z', hz', hAz'⟩ hAz
    rw [r2 A z z' ⟨⟨⟨z', hz', hAz'⟩, hAz⟩, ⟨⟨z', hz', hAz'⟩, hAz'⟩⟩]; exact hz'
  have hS' : (S ⨾ R˘) ↾ (R ʻʻ G) ∈ arrow one one := by
    refine mem_arrow_one_one.2 ⟨?_, ?_⟩
    · rintro B B' A ⟨⟨⟨z, hBz, hAz⟩, hA⟩, ⟨⟨z', hBz', hAz'⟩, -⟩⟩
      have := r2 A z z' ⟨⟨hA, hAz⟩, ⟨hA, hAz'⟩⟩
      subst this
      exact s1 B B' z ⟨⟨hBz, hz A z hA hAz⟩, ⟨hBz', hz A z hA hAz⟩⟩
    · rintro B A A' ⟨⟨⟨z, hBz, hAz⟩, hA⟩, ⟨⟨z', hBz', hAz'⟩, hA'⟩⟩
      have := s2 B z z' ⟨⟨hBz, hz A z hA hAz⟩, ⟨hBz', hz A' z' hA' hAz'⟩⟩
      subst this
      exact r1 A A' z ⟨⟨hA, hAz⟩, ⟨hA', hAz'⟩⟩
  have hcod : R ʻʻ G ⊆ codom (S ⨾ R˘) := by
    rintro A ⟨z, hz', hAz⟩
    obtain ⟨B, hBz⟩ := hGS hz'
    exact ⟨B, z, hBz, hAz⟩
  have h := pm114_63 ⟨hS', hcod⟩
  have e1 : {μ | ∃ A, A ∈ R ʻʻ G ∧ Desc (S ⨾ R˘) A (fun B => μ = A ×ₐ B)} =
      {μ | ∃ z, z ∈ G ∧ Desc R z (fun A => Desc S z (fun B => μ = A ×ₐ B))} := by
    ext μ
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨A, hA, hD⟩
      obtain ⟨B, ⟨-, z, hBz, hAz⟩, rfl⟩ := (desc_unique_iff hS').1 ⟨hA, hD⟩
      have hzG := hz A z hA hAz
      refine ⟨z, hzG, ?_⟩
      have uA : ∀ A', R A' z ↔ A' = A := fun A' =>
        ⟨fun h => r1 A' A z ⟨⟨⟨z, hzG, h⟩, h⟩, ⟨hA, hAz⟩⟩, fun e => e ▸ hAz⟩
      have uB : ∀ B', S B' z ↔ B' = B := fun B' =>
        ⟨fun h => s1 B' B z ⟨⟨h, hzG⟩, ⟨hBz, hzG⟩⟩, fun e => e ▸ hBz⟩
      rw [desc_of_unique uA, desc_of_unique uB]
    · rintro ⟨z, hzG, hD⟩
      obtain ⟨A, hAz⟩ := hGR hzG
      obtain ⟨B, hBz⟩ := hGS hzG
      have hA : A ∈ R ʻʻ G := ⟨z, hzG, hAz⟩
      have uA : ∀ A', R A' z ↔ A' = A := fun A' =>
        ⟨fun h => r1 A' A z ⟨⟨⟨z, hzG, h⟩, h⟩, ⟨hA, hAz⟩⟩, fun e => e ▸ hAz⟩
      have uB : ∀ B', S B' z ↔ B' = B := fun B' =>
        ⟨fun h => s1 B' B z ⟨⟨h, hzG⟩, ⟨hBz, hzG⟩⟩, fun e => e ▸ hBz⟩
      rw [desc_of_unique uA, desc_of_unique uB] at hD
      exact ⟨A, hA, ((desc_unique_iff hS').2 ⟨B, ⟨hA, z, hBz, hAz⟩, hD⟩).2⟩
  have e2 : (S ⨾ R˘) ʻʻ (R ʻʻ G) = S ʻʻ G := by
    ext B
    constructor
    · rintro ⟨A, hA, z, hBz, hAz⟩; exact ⟨z, hz A z hA hAz, hBz⟩
    · rintro ⟨z, hzG, hBz⟩
      obtain ⟨A, hAz⟩ := hGR hzG
      exact ⟨A, ⟨z, hzG, hAz⟩, z, hBz, hAz⟩
  rw [e1, e2] at h
  exact sm_symm h

/-- ✱114·65. \[\begin{align}\vdash \colon\ldotp &(Rʻʻ\gamma )\upharpoonleft R,S\upharpoonright \gamma \in 1\rightarrow 1.\gamma \subset \text{ᗡ}ʻR.\gamma \subset \text{ᗡ}ʻS.Rʻʻ\gamma \cap Sʻʻ\gamma = \Lambda .\supset .\\ &{\in}_{\Delta}ʻ(Rʻʻ\gamma \cup Sʻʻ\gamma )\text{ sm }{\in}_{\Delta}ʻ\hat{\mu} \{(\exists z).z\in \gamma .\mu = Rʻz \times Sʻz\}\\ &[*114·64·301]\end{align}\]

`R''γ ∩ S''γ` puts `R'z`, `S'z` in one type. -/
theorem pm114_65 {G : Set δ} {R S : Set α → δ → Prop} :
    ((((R ʻʻ G) ◁ R ∈ arrow one one ∧ S ↾ G ∈ arrow one one) ∧ G ⊆ codom R) ∧ G ⊆ codom S) ∧
        R ʻʻ G ∩ S ʻʻ G = Λ →
      sm (sel memRel (R ʻʻ G ∪ S ʻʻ G))
        (sel memRel {μ | ∃ z, z ∈ G ∧ Desc R z (fun A => Desc S z (fun B => μ = A ×ₐ B))}) :=
  fun ⟨h, hd⟩ => sm_trans (sel_union_sm hd) (pm114_64 h)

end PrincipiaMathematica
