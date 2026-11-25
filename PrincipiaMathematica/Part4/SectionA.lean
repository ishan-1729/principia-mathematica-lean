import PrincipiaMathematica.Defs.Part4

/-!
# Part IV, Section A: Ordinal similarity and relation-numbers

Volume 2. Numbers: ✱150, ✱151, ✱152, ✱153, ✱154, ✱155.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

/-! ### Helper lemmas for ✱150–✱155 (not propositions of PM) -/

/-- `x(S;Q)y` unfolded, with the product flattened. -/
private theorem semi_iff {α β : Type*} (S : α → β → Prop) (Q : β → β → Prop) (x y : α) :
    (S ⁏ Q) x y ↔ ∃ z w, S x z ∧ S y w ∧ Q z w := by
  rw [semi_apply]; simp only [and_assoc]

/-- Unfold the relations, classes and descriptions of Section A to first-order logic. -/
local macro "rsimp" : tactic => `(tactic| simp only [semi_iff, rcup, rcap, rdiff, rneg, cres,
  dres, bres, fres, couple_apply, cross, mem_unitCls, refs, rels, img, dom, codom, fld,
  Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff, RSub,
  relProd, sumRel, sumCls, Null_eq_empty, Set.mem_empty_iff_false, mem_rl, rNull, rV,
  Set.subset_def, rel_eq_iff, Set.ext_iff, Set.Nonempty, D, Dcnv, C, F, graph, eq_iff_iff, ne_eq,
  I, not_exists, mem_arrow_Cls_one, mem_arrow_one_Cls, mem_arrow_one_one, cnv, exists_imp,
  and_imp, rEx, Desc, TheIs, EDesc, EBang, daggerRel, daggerOp, opL, opR, opSemi, coupleR,
  coupleL, iota, Rfwd, imgRel, cl, Beg, Set.mem_univ, true_and, and_true] at *)


section Helpers

variable {α β γ δ : Type*}

private theorem rel_ext' {R S : α → β → Prop} (h : ∀ x y, R x y ↔ S x y) : R = S :=
  funext fun x => funext fun y => propext (h x y)

private theorem relProd_assoc (R : α → β → Prop) (S : β → γ → Prop) (T : γ → δ → Prop) :
    R ⨾ S ⨾ T = R ⨾ (S ⨾ T) :=
  rel_ext' fun _ _ => ⟨fun ⟨w, ⟨z, h1, h2⟩, h3⟩ => ⟨z, h1, w, h2, h3⟩,
    fun ⟨z, h1, w, h2, h3⟩ => ⟨w, ⟨z, h1, h2⟩, h3⟩⟩

/-- `(S ‖ S̆)'Q = S;Q`. -/
private theorem desc_dpar_cnv (S : α → β → Prop) (Q : β → β → Prop) (ψ : (α → α → Prop) → Prop) :
    Desc (S ∥ S˘) Q ψ ↔ ψ (S ⁏ Q) :=
  TheIs_iff_of_unique (b := S ⁏ Q) fun X => by
    rw [dpar_iff, ← relProd_assoc]; exact Iff.rfl

/-- `(S ↾ β);Q = S;(Q ⥏ β)` (✱150·36). -/
private theorem cres_semi (S : α → β → Prop) (Q : β → β → Prop) (B : Set β) :
    (S ↾ B) ⁏ Q = S ⁏ (Q ⥏ B) := by
  rsimp
  grind

private theorem fres_eq_self {P : α → α → Prop} {A : Set α} (h : fld P ⊆ A) : P ⥏ A = P := by
  rsimp
  grind

/-- Induction over the powers of `R` (✱91). -/
private theorem pot_induction {R : α → α → Prop} {motive : (α → α → Prop) → Prop}
    (base : motive R) (step : ∀ X, X ∈ pot R → motive X → motive (X ⨾ R)) {S : α → α → Prop}
    (h : S ∈ pot R) : motive S := by
  have hfld : ∀ X : α → α → Prop, X ∈ fld (relProdR R) :=
    fun X => ⟨X ⨾ R, Or.inr ((relProdR_apply _ _ _).2 rfl)⟩
  rw [mem_pot_iff] at h
  obtain ⟨-, h⟩ := h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact base
  | head hac hc ih =>
    have e := (relProdR_apply _ _ _).1 hac
    rw [e]
    exact step _ (mem_pot_iff.2 ⟨hfld _, hc⟩) ih

private theorem codom_pot_subset {R X : α → α → Prop} (h : X ∈ pot R) : codom X ⊆ codom R := by
  refine pot_induction (motive := fun X => codom X ⊆ codom R) (subset_refl _) ?_ h
  rintro X - - y ⟨x, z, -, hzy⟩
  exact ⟨z, hzy⟩

/-- `(S;P) | (S;Q) = S;(P | Q)` for many-one `S` (cf. ✱150·8). -/
private theorem semi_comp_semi {S : α → β → Prop} {P Q : β → β → Prop} (hS : S ∈ arrow Cls one)
    (h : dom Q ⊆ codom S ∨ codom P ⊆ codom S) : (S ⁏ P) ⨾ (S ⁏ Q) = S ⁏ (P ⨾ Q) := by
  rsimp
  grind

/-- `S̆;S;Q = Q` for many-one `S` with `C'Q ⊂ ᗡ'S` (✱151·252). -/
private theorem cnv_semi_semi {S : α → β → Prop} {Q : β → β → Prop} (hS : S ∈ arrow Cls one)
    (hQ : fld Q ⊆ codom S) : S˘ ⁏ S ⁏ Q = Q := by
  rsimp
  grind

private theorem rsub_antisymm {R S : α → β → Prop} (h1 : R ⪽ S) (h2 : S ⪽ R) : R = S :=
  rel_ext' fun x y => ⟨h1 x y, h2 x y⟩

private theorem cnv_mem_arrow_one_one {S : α → β → Prop} (h : S ∈ arrow one one) :
    S˘ ∈ arrow one one :=
  mem_arrow_one_one.2 ⟨fun x y z h' => (mem_arrow_one_one.1 h).2 z x y h',
    fun x y z h' => (mem_arrow_one_one.1 h).1 y z x h'⟩

private theorem cnv_mem_arrow_Cls_one {S : α → β → Prop} (h : S ∈ arrow one Cls) :
    S˘ ∈ arrow Cls one :=
  mem_arrow_Cls_one.2 fun x y z h' => (mem_arrow_one_Cls.1 h) y z x h'

private theorem arrow_Cls_one_of {S : α → β → Prop} (h : S ∈ arrow one one) : S ∈ arrow Cls one :=
  mem_arrow_Cls_one.2 (mem_arrow_one_one.1 h).2

private theorem arrow_one_Cls_of {S : α → β → Prop} (h : S ∈ arrow one one) : S ∈ arrow one Cls :=
  mem_arrow_one_Cls.2 (mem_arrow_one_one.1 h).1

/-- `R'x = R'y` when `R'x`, `R'y` exist with values `b`, `c`. -/
private theorem desc_eq_iff' {R : γ → β → Prop} {x y : β} {b c : γ} (hb : ∀ u, R u x ↔ u = b)
    (hc : ∀ u, R u y ↔ u = c) : Desc R x (fun u => Desc R y (fun v => u = v)) ↔ b = c := by
  rw [Desc, TheIs_iff_of_unique hb, Desc, TheIs_iff_of_unique hc]

/-- Two descriptions unfolded. -/
private theorem desc_desc_iff {R : α → β → Prop} {y y' : β} {φ : α → α → Prop} :
    Desc R y (fun a => Desc R y' (fun b => φ a b)) ↔
      ∃ a b, ((∀ u, R u y ↔ u = a) ∧ (∀ u, R u y' ↔ u = b)) ∧ φ a b :=
  ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨a, b, ⟨ha, hb⟩, h⟩, fun ⟨a, b, ⟨ha, hb⟩, h⟩ => ⟨a, ha, b, hb, h⟩⟩

/-- From a one-one `S ↾ β` with `β ⊂ ᗡ'S`: each member of `β` has exactly one referent. -/
private theorem uniq_of_cres {S : α → β → Prop} {B : Set β} (hB : B ⊆ codom S)
    (h : S ↾ B ∈ arrow one one) {y : β} (hy : y ∈ B) : ∃ b, ∀ x, S x y ↔ x = b := by
  obtain ⟨b, hb⟩ := hB hy
  exact ⟨b, fun x => ⟨fun hx => (mem_arrow_one_one.1 h).1 x b y ⟨⟨hx, hy⟩, ⟨hb, hy⟩⟩,
    fun e => e ▸ hb⟩⟩

private theorem cres_one_one {S : α → β → Prop} {B : Set β} (h : S ∈ arrow one one) :
    S ↾ B ∈ arrow one one := by
  rsimp
  grind

private theorem cres_one_one_mono {S : α → β → Prop} {A B : Set β} (hAB : A ⊆ B)
    (h : S ↾ B ∈ arrow one one) : S ↾ A ∈ arrow one one := by
  rsimp
  grind

private theorem codom_cres_iff {S : α → β → Prop} {B : Set β} :
    B = codom (S ↾ B) ↔ B ⊆ codom S := by
  rsimp
  grind

private theorem fld_mono' {P Q : α → α → Prop} (h : P ⪽ Q) : fld P ⊆ fld Q := fld_mono h

private theorem fld_pot_subset {R X : α → α → Prop} (h : X ∈ pot R) : fld X ⊆ fld R := by
  refine pot_induction (motive := fun X => fld X ⊆ fld R) (subset_refl _) ?_ h
  rintro X - ih x ⟨y, ⟨z, hxz, hzy⟩ | ⟨z, hyz, hzx⟩⟩
  · exact ih ⟨z, Or.inl hxz⟩
  · exact ⟨z, Or.inr hzx⟩

private theorem fld_po {R : α → α → Prop} : fld (po R) = fld R := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · obtain ⟨X, hX, hxy⟩ := h
      exact fld_pot_subset hX ⟨y, Or.inl hxy⟩
    · obtain ⟨X, hX, hxy⟩ := h
      exact fld_pot_subset hX ⟨y, Or.inr hxy⟩
  · rintro ⟨y, h | h⟩
    · exact ⟨y, Or.inl ⟨R, self_mem_pot R, h⟩⟩
    · exact ⟨y, Or.inr ⟨R, self_mem_pot R, h⟩⟩

/-- The correlator `S` of `P` with `Q` carries `Q`-chains to `P`-chains and back. -/
private theorem rtg_transfer {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    (hS : S ∈ arrow one one) (hQ : fld Q = codom S) (hP : P = S ⁏ Q) {x y : α} {z w : β}
    (hxz : S x z) (hyw : S y w) :
    Relation.ReflTransGen P x y ↔ Relation.ReflTransGen Q z w := by
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS
  constructor
  · intro h
    revert w
    induction h with
    | refl =>
      intro w hyw
      obtain rfl := h2 _ _ _ ⟨hxz, hyw⟩
      exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      intro w hyw
      rw [hP, semi_iff] at hbc
      obtain ⟨c', d, hc', hd, hcd⟩ := hbc
      obtain rfl := h2 _ _ _ ⟨hd, hyw⟩
      exact (ih hc').tail hcd
  · intro h
    revert y
    induction h with
    | refl =>
      intro y hyw
      obtain rfl := h1 _ _ _ ⟨hyw, hxz⟩
      exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih =>
      intro y hyw
      have hc : c ∈ codom S := hQ ▸ (⟨d, Or.inl hcd⟩ : c ∈ fld Q)
      obtain ⟨y', hy'⟩ := hc
      refine (ih hy').tail ?_
      rw [hP, semi_iff]
      exact ⟨c, d, hy', hyw, hcd⟩

private theorem n₀c_eq_cardAdd_iff {η : Type*} (X : Set η) (μ : Set (Set α)) (ν : Set (Set β)) :
    n₀c X = (μ +ᶜ ν : Set (Set η)) ↔
      ∃ (P : Set α) (Q : Set β), (μ = n₀c P ∧ ν = n₀c Q) ∧ sm X (P +ₐ Q) := by
  constructor
  · intro e
    exact mem_cardAdd.1 (e ▸ self_mem_n₀c X)
  · rintro ⟨P, Q, ⟨hP, hQ⟩, hX⟩
    ext Y
    rw [mem_n₀c, mem_cardAdd]
    constructor
    · intro hY; exact ⟨P, Q, ⟨hP, hQ⟩, sm_trans hY hX⟩
    · rintro ⟨P', Q', ⟨hP', hQ'⟩, hY⟩
      have e1 : sm P' P := n₀c_eq_n₀c_iff.1 (hP'.symm.trans hP)
      have e2 : sm Q' Q := n₀c_eq_n₀c_iff.1 (hQ'.symm.trans hQ)
      exact sm_trans hY (sm_trans (sm_clsSum e1 e2) (sm_symm hX))

/-- `N₀c'α = μ +_c ν` transfers along similarity (the equations in two types). -/
private theorem n₀c_eq_cardAdd_transfer {A : Set γ} {B : Set δ} (h : sm A B)
    (μ : Set (Set α)) (ν : Set (Set β)) :
    n₀c A = (μ +ᶜ ν : Set (Set γ)) ↔ n₀c B = (μ +ᶜ ν : Set (Set δ)) := by
  rw [n₀c_eq_cardAdd_iff, n₀c_eq_cardAdd_iff]
  exact ⟨fun ⟨P, Q, hPQ, hX⟩ => ⟨P, Q, hPQ, sm_trans (sm_symm h) hX⟩,
    fun ⟨P, Q, hPQ, hX⟩ => ⟨P, Q, hPQ, sm_trans h hX⟩⟩

/-- `C'Q = ᗡ'S . ⊃ . C'S;Q = D'S` (✱150·23). -/
private theorem fld_semi_eq_dom {S : α → β → Prop} {Q : β → β → Prop} (h : fld Q = codom S) :
    fld (S ⁏ Q) = dom S := by
  rsimp
  grind

private theorem smorbar_cnv {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    (h : S ∈ smorbar P Q) : S˘ ∈ smorbar Q P := by
  obtain ⟨⟨hS, hQ⟩, rfl⟩ := h
  exact ⟨⟨cnv_mem_arrow_one_one hS, fld_semi_eq_dom hQ⟩,
    (cnv_semi_semi (arrow_Cls_one_of hS) hQ.le).symm⟩

private theorem mem_Ccnv_img_cl {Q : α → α → Prop} {B : Set α} : Q ∈ C˘ ʻʻ cl B ↔ fld Q ⊆ B :=
  ⟨fun ⟨A, hA, e⟩ => (show A = fld Q from e) ▸ hA, fun h => ⟨fld Q, h, rfl⟩⟩

/-- The relation of ✱151·281 (correlation of predecessors and successors) gives a correlator. -/
private theorem smor281 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    (h1 : ∀ x y, P x y → Desc S˘ x (fun a => Desc S˘ y (fun b => Q a b)))
    (h2 : ∀ z w, Q z w → Desc S z (fun a => Desc S w (fun b => P a b))) :
    fld P ◁ S = S ↾ fld Q ∧ S ↾ fld Q ∈ smorbar P Q := by
  simp only [desc_desc_iff] at h1 h2
  have hP : ∀ x, x ∈ fld P → ∃ a, (∀ u, S x u ↔ u = a) ∧ a ∈ fld Q := by
    rintro x ⟨y, hxy | hyx⟩
    · obtain ⟨a, b, ⟨ha, -⟩, hab⟩ := h1 x y hxy
      exact ⟨a, ha, b, Or.inl hab⟩
    · obtain ⟨a, b, ⟨-, hb⟩, hab⟩ := h1 y x hyx
      exact ⟨b, hb, a, Or.inr hab⟩
  have hQ : ∀ z, z ∈ fld Q → ∃ a, (∀ u, S u z ↔ u = a) ∧ a ∈ fld P := by
    rintro z ⟨w, hzw | hwz⟩
    · obtain ⟨a, b, ⟨ha, -⟩, hab⟩ := h2 z w hzw
      exact ⟨a, ha, b, Or.inl hab⟩
    · obtain ⟨a, b, ⟨-, hb⟩, hab⟩ := h2 w z hwz
      exact ⟨b, hb, a, Or.inr hab⟩
  have e : fld P ◁ S = S ↾ fld Q := by
    refine rel_ext' fun x z => ⟨fun ⟨hx, hxz⟩ => ⟨hxz, ?_⟩, fun ⟨hxz, hz⟩ => ⟨?_, hxz⟩⟩
    · obtain ⟨a, ha, haQ⟩ := hP x hx
      rw [(ha z).1 hxz]; exact haQ
    · obtain ⟨a, ha, haP⟩ := hQ z hz
      rw [(ha x).1 hxz]; exact haP
  refine ⟨e, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · refine mem_arrow_one_one.2 ⟨?_, ?_⟩
    · rintro x y z ⟨⟨hx, hz⟩, ⟨hy, -⟩⟩
      obtain ⟨a, ha, -⟩ := hQ z hz
      exact ((ha x).1 hx).trans ((ha y).1 hy).symm
    · rintro x y z ⟨⟨hy, hyQ⟩, ⟨hz, -⟩⟩
      obtain ⟨b, hb, hbP⟩ := hQ y hyQ
      have hx : x ∈ fld P := (hb x).1 hy ▸ hbP
      obtain ⟨a, ha, -⟩ := hP x hx
      exact ((ha y).1 hy).trans ((ha z).1 hz).symm
  · ext z
    constructor
    · intro hz
      obtain ⟨a, ha, -⟩ := hQ z hz
      exact ⟨a, (ha a).2 rfl, hz⟩
    · rintro ⟨x, -, hz⟩; exact hz
  · refine rel_ext' fun x y => ?_
    rw [semi_iff]
    constructor
    · intro hxy
      obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := h1 x y hxy
      exact ⟨a, b, ⟨(ha a).2 rfl, ⟨b, Or.inl hab⟩⟩, ⟨(hb b).2 rfl, ⟨a, Or.inr hab⟩⟩, hab⟩
    · rintro ⟨z, w, ⟨hxz, -⟩, ⟨hyw, -⟩, hzw⟩
      obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := h2 z w hzw
      rw [(ha x).1 hxz, (hb y).1 hyw]; exact hab

private theorem rtg_fld {P : α → α → Prop} {a b : α} (h : Relation.ReflTransGen P a b)
    (ha : a ∈ fld P) : b ∈ fld P := by
  induction h with
  | refl => exact ha
  | tail _ hcd _ => exact ⟨_, Or.inr hcd⟩

private theorem itvCC_sub_fld {Q : β → β → Prop} {z w u : β} (h : u ∈ itvCC Q z w) : u ∈ fld Q :=
  (anc_iff_reflTransGen.1 h.2).1

/-- A correlator carries the intervals of `Q` onto those of `P` (cf. ✱151·57). -/
private theorem itv_transfer {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    (hS : S ∈ arrow one one) (hQ : fld Q = codom S) (hP : P = S ⁏ Q) {z w : β}
    (hz : z ∈ fld Q) (hw : w ∈ fld Q) :
    Desc S z (fun a => Desc S w (fun b => itvCC P a b = S ʻʻ itvCC Q z w)) := by
  obtain ⟨h1, -⟩ := mem_arrow_one_one.1 hS
  obtain ⟨a, ha⟩ : z ∈ codom S := by rw [← hQ]; exact hz
  obtain ⟨b, hb⟩ : w ∈ codom S := by rw [← hQ]; exact hw
  have ua : ∀ u, S u z ↔ u = a := fun u => ⟨fun hu => h1 u a z ⟨hu, ha⟩, fun e => e ▸ ha⟩
  have ub : ∀ u, S u w ↔ u = b := fun u => ⟨fun hu => h1 u b w ⟨hu, hb⟩, fun e => e ▸ hb⟩
  refine (TheIs_iff_of_unique ua).2 ((TheIs_iff_of_unique ub).2 ?_)
  have hdomS : dom S = fld P := by rw [hP, fld_semi_eq_dom hQ]
  ext u
  simp only [itvCC, Set.mem_inter_iff, rels, refs, Set.mem_ofPred_eq, img,
    anc_iff_reflTransGen]
  constructor
  · rintro ⟨⟨-, hau⟩, hu, hub⟩
    obtain ⟨y, huy⟩ : u ∈ dom S := by rw [hdomS]; exact hu
    have hy : y ∈ fld Q := by rw [hQ]; exact ⟨u, huy⟩
    exact ⟨y, ⟨⟨hz, (rtg_transfer hS hQ hP ha huy).1 hau⟩, hy,
      (rtg_transfer hS hQ hP huy hb).1 hub⟩, huy⟩
  · rintro ⟨y, ⟨⟨-, hzy⟩, -, hyw⟩, huy⟩
    have haP : a ∈ fld P := by rw [← hdomS]; exact ⟨z, ha⟩
    have huP : u ∈ fld P := by rw [← hdomS]; exact ⟨y, huy⟩
    exact ⟨⟨haP, (rtg_transfer hS hQ hP ha huy).2 hzy⟩, huP,
      (rtg_transfer hS hQ hP huy hb).2 hyw⟩

/-- `α ⊂ ᗡ'R . R↾α ∈ 1 → 1 . ⊃ . R''α sm α` (cf. ✱73·15). -/
private theorem sm_img_cres {R : γ → β → Prop} {A : Set β} (hA : A ⊆ codom R)
    (hR : R ↾ A ∈ arrow one one) : sm (R ʻʻ A) A := by
  refine sm_iff.2 ⟨R ↾ A, ⟨hR, ?_⟩, ?_⟩
  · ext x
    exact ⟨fun ⟨y, hy, hxy⟩ => ⟨y, hxy, hy⟩, fun ⟨y, hxy, hy⟩ => ⟨y, hy, hxy⟩⟩
  · ext y
    exact ⟨fun hy => let ⟨x, hx⟩ := hA hy; ⟨x, hx, hy⟩, fun ⟨_, _, hy⟩ => hy⟩

private theorem itvCC_nonempty_of_Pnu {P : α → α → Prop} {ν : Set (Set γ)} {x y : α}
    (h : Pnu P ν x y) : (itvCC P x y).Nonempty := by
  have hX : itvCC P x y ∈ (ν +ᶜ (one : Set (Set γ)) : Set (Set α)) := by
    rw [← (h : n₀c _ = _)]; exact self_mem_n₀c _
  obtain ⟨A, B, ⟨-, hB⟩, hsm⟩ := mem_cardAdd.1 hX
  have hB' : B ∈ (one : Set (Set γ)) := by rw [hB]; exact self_mem_n₀c B
  obtain ⟨b, rfl⟩ := hB'
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hsm
  have p : ↥(A +ₐ ι b) := (clsSumEquiv A (ι b)).symm (Sum.inr ⟨b, mem_unitCls.2 rfl⟩)
  exact ⟨(e.symm p : α), (e.symm p).2⟩

/-- `C'P_ν ⊂ C'P`. -/
private theorem fld_Pnu_subset {P : α → α → Prop} {ν : Set (Set γ)} : fld (Pnu P ν) ⊆ fld P := by
  have key : ∀ x y, Pnu P ν x y → x ∈ fld P ∧ y ∈ fld P := by
    intro x y h
    obtain ⟨u, hxu, huy⟩ := itvCC_nonempty_of_Pnu h
    obtain ⟨hx, -⟩ := anc_iff_reflTransGen.1 hxu
    obtain ⟨hu, huy'⟩ := anc_iff_reflTransGen.1 huy
    exact ⟨hx, rtg_fld huy' hu⟩
  rintro x ⟨y, h | h⟩
  · exact (key x y h).1
  · exact (key y x h).2

private theorem fld_cnv {P : α → α → Prop} : fld P˘ = fld P := by
  ext x
  exact ⟨fun ⟨y, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, h.symm⟩⟩

/-- `B⃗'S;Q = S''B⃗'Q` for a correlator `S ↾ C'Q` (cf. ✱151·5). -/
private theorem beg_semi {S : α → β → Prop} {Q : β → β → Prop} (h1 : S ↾ fld Q ∈ arrow one one)
    (hQ : fld Q ⊆ codom S) : refs Beg (S ⁏ Q) = S ʻʻ refs Beg Q := by
  ext x
  simp only [refs, Beg, Set.mem_ofPred_eq, Set.mem_sdiff, dom, codom, img, semi_iff]
  constructor
  · rintro ⟨⟨y, z, w, hxz, hyw, hzw⟩, hx⟩
    refine ⟨z, ⟨⟨w, hzw⟩, ?_⟩, hxz⟩
    rintro ⟨v, hvz⟩
    obtain ⟨u, huv⟩ := hQ ⟨z, Or.inl hvz⟩
    exact hx ⟨u, v, z, huv, hxz, hvz⟩
  · rintro ⟨z, ⟨⟨w, hzw⟩, hz⟩, hxz⟩
    obtain ⟨y, hyw⟩ := hQ ⟨z, Or.inr hzw⟩
    refine ⟨⟨y, z, w, hxz, hyw, hzw⟩, ?_⟩
    rintro ⟨u, a, b, hua, hxb, hab⟩
    have e : z = b :=
      (mem_arrow_one_one.1 h1).2 x z b ⟨⟨hxz, ⟨w, Or.inl hzw⟩⟩, ⟨hxb, ⟨a, Or.inr hab⟩⟩⟩
    exact hz ⟨a, by rw [e]; exact hab⟩

/-- `P smor Λ̇ . ≡ . P = Λ̇` (✱153·101), with `Λ̇` of any type. -/
private theorem smor_rNull_iff {P : α → α → Prop} : smor P (rNull : β → β → Prop) ↔ P = rNull := by
  constructor
  · rintro ⟨S, ⟨-, -⟩, rfl⟩
    rsimp
    grind
  · rintro rfl
    refine ⟨rNull, ⟨?_, ?_⟩, ?_⟩ <;> rsimp <;> grind

/-- A class similar to `C'Q` is the field of a relation like `Q` (cf. ✱151·19). -/
private theorem exists_smor_fld {X : Set γ} {Q : β → β → Prop} (h : sm X (fld Q)) :
    ∃ R : γ → γ → Prop, fld R = X ∧ smor R Q := by
  obtain ⟨S, ⟨hS, hdom⟩, hcod⟩ := sm_iff.1 h
  exact ⟨S ⁏ Q, (fld_semi_eq_dom hcod).trans hdom.symm, ⟨S, ⟨hS, hcod⟩, rfl⟩⟩

/-- `Nc'C'Q = C''Nr'Q` (✱152·7), in any type. -/
private theorem nc_fld_eq {Q : β → β → Prop} : nc γ (fld Q) = C ʻʻ nr γ Q := by
  ext X
  constructor
  · intro h
    obtain ⟨R, hR, hRQ⟩ := exists_smor_fld h
    exact ⟨R, hRQ, hR.symm⟩
  · rintro ⟨R, hR, rfl⟩
    exact sm_fld_of_smor hR

private theorem fld_I_cres (B : Set α) : fld ((I : α → α → Prop) ↾ B) = B := by
  ext x
  constructor
  · rintro ⟨y, ⟨rfl, hy⟩ | ⟨-, hx⟩⟩
    · exact hy
    · exact hx
  · intro hx
    exact ⟨x, Or.inl ⟨rfl, hx⟩⟩

private theorem relT2T_eq'' (R : Set α → β → Prop) (x : α) (y : β) : relT2T R x y = R := by
  funext K z; simp [relT2T, dres, cres, typ2, typ_eq_univ]

private theorem relT2_eq'' (R : Set α → β → Prop) (x : α) : relT2 R x = R := by
  funext K z; simp [relT2, dres, typ2, typ_eq_univ]

private theorem clsT2_eq'' (A : Set (Set α)) (x : α) : clsT2 A x = A := by
  rw [clsT2, typ_eq_univ, Set.inter_univ]

/-- `Nr(X_Y)'Q` is `nr γ Q`. -/
private theorem desc_relT2T_Nr (X : γ → γ → Prop) (Y Q : β → β → Prop)
    (ψ : Set (γ → γ → Prop) → Prop) :
    Desc (relT2T (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) X Y) Q ψ ↔ ψ (nr γ Q) := by
  rw [relT2T_eq'']; exact desc_Nr Q ψ

/-- `Nr_x'Q` (✱65·03, `x` a class of relations) is `nr γ Q`. -/
private theorem desc_relT_Nr (x : Set (γ → γ → Prop)) (Q : β → β → Prop)
    (ψ : Set (γ → γ → Prop) → Prop) :
    Desc (relT (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) x) Q ψ ↔ ψ (nr γ Q) := by
  rw [relT_eq]; exact desc_Nr Q ψ

/-- `Nc(α)'β` is `nc γ β`. -/
private theorem desc_relT2_Nc'' (A : Set γ) (E : Set β) (ψ : Set (Set γ) → Prop) :
    Desc (relT2 (Nc : Set (Set γ) → Set β → Prop) A) E ψ ↔ ψ (nc γ E) := by
  rw [relT2_eq'']; exact desc_Nc E ψ

private theorem mem_typ' (x y : α) : y ∈ typ x := by rw [typ_eq_univ]; trivial

/-- `∃!Cl'α ∩ Nc'β` iff `β` injects into `α`. -/
private theorem cl_nc_nonempty_iff {A : Set α} {B : Set β} :
    (cl A ∩ nc α B).Nonempty ↔ Nonempty (B ↪ A) := by
  constructor
  · rintro ⟨X, hXA, hX⟩
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hX
    refine ⟨⟨fun b => ⟨(e.symm b : α), hXA (e.symm b).2⟩, fun b b' h => ?_⟩⟩
    have h' := congrArg (fun p : ↥A => (p : α)) h
    exact e.symm.injective (Subtype.ext h')
  · rintro ⟨f⟩
    refine ⟨Set.range (fun b => (f b : α)), ?_, ?_⟩
    · rintro _ ⟨b, rfl⟩; exact (f b).2
    · exact sm_iff_nonempty_equiv.2
        ⟨(Equiv.ofInjective _ (fun b b' h => f.injective (Subtype.ext h))).symm⟩

/-- `N₀c'α ≥ N₀c'β . ≡ . ∃!Cl'α ∩ Nc'β` (✱117). -/
private theorem n₀c_ge_iff {A : Set α} {B : Set β} :
    n₀c A ≥ᶜ n₀c B ↔ (cl A ∩ nc α B).Nonempty := by
  rw [cl_nc_nonempty_iff]
  constructor
  · rintro (⟨A', B', ⟨⟨hA, hB⟩, h1⟩, -⟩ | ⟨-, e⟩)
    · obtain ⟨f⟩ := cl_nc_nonempty_iff.1 h1
      obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 hA)
      obtain ⟨eB⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 hB)
      exact ⟨eB.toEmbedding.trans (f.trans eA.symm.toEmbedding)⟩
    · have hA : A ∈ sm ʻʻ n₀c B := by rw [← e]; exact self_mem_n₀c A
      obtain ⟨Y, hY, hAY⟩ := hA
      obtain ⟨e1⟩ := sm_iff_nonempty_equiv.1 (sm_trans hAY (mem_n₀c.1 hY))
      exact ⟨e1.symm.toEmbedding⟩
  · rintro ⟨f⟩
    by_cases hg : Nonempty (A ↪ B)
    · obtain ⟨g⟩ := hg
      obtain ⟨e⟩ := Function.Embedding.antisymm g f
      have sAB : sm A B := sm_iff_nonempty_equiv.2 ⟨e⟩
      refine Or.inr ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, ?_⟩
      ext X
      rw [mem_n₀c]
      constructor
      · intro h; exact ⟨B, self_mem_n₀c B, sm_trans h sAB⟩
      · rintro ⟨Y, hY, hXY⟩
        exact sm_trans hXY (sm_trans (mem_n₀c.1 hY) (sm_symm sAB))
    · exact Or.inl ⟨A, B, ⟨⟨rfl, rfl⟩, cl_nc_nonempty_iff.2 ⟨f⟩⟩,
        fun h => hg (cl_nc_nonempty_iff.1 h)⟩

/-- No relation on `γ` is like a relation whose field is the whole of `Set γ` (Cantor). -/
private theorem nr_eq_empty_of_cantor {Q : Set γ → Set γ → Prop} (h : fld Q = Set.univ) :
    nr γ Q = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun R hR => ?_
  obtain ⟨f, hf⟩ := nr_nonempty_iff.1 ⟨R, hR⟩
  have hmem : ∀ A : Set γ, A ∈ fld Q := fun A => h ▸ Set.mem_univ A
  exact Function.cantor_injective (fun A => f ⟨A, hmem A⟩)
    (fun A B e => congrArg Subtype.val (hf e))

/-- `β sm ι'x . ≡ . β ∈ 1` (cf. ✱73·45). -/
private theorem sm_unit_iff' {B : Set α} {x : β} : sm B (ι x) ↔ B ∈ one := by
  rw [sm_iff_nonempty_equiv]
  constructor
  · rintro ⟨e⟩
    rw [unitCls_eq_singleton] at e
    refine ⟨(e.symm ⟨x, rfl⟩ : α), Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
    · have : e ⟨z, hz⟩ = ⟨x, rfl⟩ := Subsingleton.elim _ _
      exact congrArg Subtype.val (e.symm_apply_eq.2 this.symm).symm
    · rw [mem_unitCls.1 hz]
      exact (e.symm ⟨x, rfl⟩).2
  · rintro ⟨y, rfl⟩
    rw [unitCls_eq_singleton, unitCls_eq_singleton]
    exact ⟨Equiv.ofUnique _ _⟩

private theorem two_r_not_zero_r {R : α → α → Prop} (h : R ∈ (two_r : Set (α → α → Prop))) :
    R ∉ (zero_r : Set (α → α → Prop)) := by
  obtain ⟨x, y, -, rfl⟩ := h
  intro h
  have e : x ↓ y = rNull := mem_unitCls.1 h
  apply rNull_apply x y
  rw [← e]
  exact ⟨mem_unitCls.2 rfl, mem_unitCls.2 rfl⟩

end Helpers

variable {α β γ δ ε ξ : Type*}

/-!
## [✱150] Internal transformation of a relation

*(Vol. 2, p. 306)*

> *Summary of* *150.
>
> In this number we introduce two notations which have uses in regard to relations closely analogous to the uses of \(Rʻʻ\alpha\) and \(R_{\in}\) in regard to classes. These two notations are defined as follows: \[ \begin{aligned} S^{;}Q&=S\mid Q\mid \breve{S} \quad\text{Df},\\ S\dagger Q&=S\mid Q\mid \breve{S} \quad\text{Df}. \end{aligned} \] We then have \(\vdash .S\dagger Q=S^{;}Q=S\mid Q\mid \breve{S}=(S\parallel \breve{S})ʻQ\).
>
> \(S\dagger Q\) is merely an alternative to \(S^{;}Q\), just as \(R_{\in}ʻ\alpha\) is an alternative to \(Rʻʻ\alpha\). Also \(S\dagger =S\parallel \breve{S}\), in virtue of *38·01 and *43·01.
>
> The uses of \(S^{;}Q\) occur chiefly when \(S\) is a one-one relation and \(CʻQ\subset \text{ᗡ}ʻS\). This case is illustrated in the figure in the introduction to this section. Here if \(Q\) relates \(x\) and \(y\), \(S^{;}Q\) relates \(Sʻx\) and \(Sʻy\). Thus given a class \(\alpha\) similar to \(CʻQ\), if \(S\) is the correlating relation, \(S^{;}Q\) has \(\alpha\) for its field, and has, in very many respects, properties analogous to those of \(Q\).
>
> …

**Lean reading.** `S;Q` is `S ⁏ Q` (`semi`, ✱150·01); the term `S†Q` is `daggerOp S Q` and the
relation `S†` is
`daggerRel S` (✱38·01, encoding decision 7 of `Defs/Part4`); `Q♀.,y` is `opSemi f Q y` for a
double descriptive function `f`, its relation `Q♀.,` is `opL (opSemi f) Q`. The correlator `S` may
be heterogeneous (`α → β → Prop`), `Q` is homogeneous on `β`. Descriptive functions that always
exist are written by their values (`D'S;Q` is `dom (S ⁏ Q)`, `S⃗'z` is `refs S z`, `S†'Q` is
`daggerOp S Q`), except in ✱150·1, where PM proves the values of `(S ‖ S̆)'Q` and `S†'Q` (kept as
`Desc`); descriptions that may fail (`S'z`, `S̆'x`, `ῐ'α`) are `Desc` with the smallest scope.
`s'C''λ` is `sumCls (C ʻʻ L)`, `Pot'Q` is `pot Q`, `Q_po` is `po Q`, `⥏λ` is `opR fres L`, `S_∈`
is `imgRel S`, `ṡ` is `sDotRel`. Where `D;…`, `ṡ;…` must be significant (✱150·96·961) the
relations concerned are homogeneous. Most proofs unfold everything to first-order logic and close
it with `grind`.

**Status.** proved (all propositions; ✱150·01–·05 definition; ✱150·512, ✱150·933, ✱150·95, ✱150·96
proved (reading): transcription errors, see their docstrings)
-/

/-- ✱150·01 (Df). \(S^{;}Q=S\mid Q\mid \breve{S} \quad\text{Df}\) -/
theorem pm150_01 {S : α → β → Prop} {Q : β → β → Prop} : S ⁏ Q = S ⨾ Q ⨾ S˘ := rfl

/-- ✱150·02 (Df). \(S\dagger Q=S\mid Q\mid \breve{S} \quad \text{Df}\)

The term `S†Q` is `daggerOp S Q`; the relation `S†` is `daggerRel S` (✱38·01). -/
theorem pm150_02 {S : α → β → Prop} {Q : β → β → Prop} : daggerOp S Q = S ⨾ Q ⨾ S˘ := rfl

/-- ✱150·03 (Df). \(Q\unicode{x2640}_{.,}y=\unicode{x2640}y^{;}Q \quad\text{Df}\)

`♀` is a double descriptive function `f : α → β → γ`; `♀y` is `opR f y` and `Q♀.,y` is
`opSemi f Q y`. -/
theorem pm150_03 {f : α → β → γ} {Q : α → α → Prop} {y : β} : opSemi f Q y = opR f y ⁏ Q := rfl

/-- ✱150·04 (Df). \(RʻS^{;}Q=Rʻ(S^{;}Q) \quad\text{Df}\)

A bracketing convention: `ψ(R'S;Q)` is the description `Desc R (S ⁏ Q) ψ`. -/
theorem pm150_04 {R : γ → (α → α → Prop) → Prop} {S : α → β → Prop} {Q : β → β → Prop}
    {ψ : γ → Prop} : Desc R (S ⁏ Q) ψ ↔ TheIs (fun x => R x (S ⁏ Q)) ψ := Iff.rfl

/-- ✱150·05 (Df). \(R^{;}S^{;}Q=R^{;}(S^{;}Q) \quad\text{Df}\)

Realized by `infixr` for `⁏`. -/
theorem pm150_05 {R : δ → α → Prop} {S : α → β → Prop} {Q : β → β → Prop} :
    R ⁏ S ⁏ Q = R ⁏ (S ⁏ Q) := rfl

/-- ✱150·1. \[\begin{align}&\vdash .S^{;}Q=S\mid Q\mid \breve{S} =(S\parallel \breve{S} )ʻQ=S\dagger Q=S\dagger ʻQ\\ &[*43·112.*38·11.(*150·01·02)]\end{align}\]

The chain of five is the conjunction of its four links. `(S ‖ S̆)'Q` and `S†'Q` are
descriptions (`Desc (S ∥ S˘) Q ψ`, `Desc (daggerRel S) Q ψ`; PM proves their values here). -/
theorem pm150_1 {S : α → β → Prop} {Q : β → β → Prop} :
    ((S ⁏ Q = S ⨾ Q ⨾ S˘ ∧ Desc (S ∥ S˘) Q (fun X => S ⨾ Q ⨾ S˘ = X)) ∧
      Desc (S ∥ S˘) Q (fun X => X = daggerOp S Q)) ∧
      Desc (daggerRel S) Q (fun X => daggerOp S Q = X) :=
  ⟨⟨⟨rfl, (desc_dpar_cnv S Q _).2 rfl⟩, (desc_dpar_cnv S Q _).2 rfl⟩,
    (desc_daggerRel S Q _).2 rfl⟩

/-- ✱150·11. \(\vdash :x(S^{;}Q)y.\equiv .(\exists z,w).xSz.ySw.zQw \quad[*34·1.*31·11]\) -/
theorem pm150_11 {S : α → β → Prop} {Q : β → β → Prop} {x y : α} :
    (S ⁏ Q) x y ↔ ∃ z w, (S x z ∧ S y w) ∧ Q z w :=
  semi_apply S Q x y

/-- ✱150·12. \(\vdash .\text{Cnv}ʻS^{;}Q=S^{;}\breve{Q} \quad [*34·2.*31·33]\)

`Cnv'S;Q` is `Cnv'(S;Q)` (✱150·04), written `(S ⁏ Q)˘` (`desc_Cnv`). -/
theorem pm150_12 {S : α → β → Prop} {Q : β → β → Prop} : (S ⁏ Q)˘ = S ⁏ Q˘ := cnv_semi S Q

/-- ✱150·13. \(\vdash .R^{;}S^{;}Q=(R\mid S)^{;}Q\) -/
theorem pm150_13 {R : δ → α → Prop} {S : α → β → Prop} {Q : β → β → Prop} :
    R ⁏ S ⁏ Q = (R ⨾ S) ⁏ Q :=
  semi_semi R S Q

/-- ✱150·131. \(\vdash .(R^{;}S)^{;}Q=R^{;}(S\mid \breve{R} )^{;}Q\) -/
theorem pm150_131 {R : α → β → Prop} {S : β → β → Prop} {Q : α → α → Prop} :
    (R ⁏ S) ⁏ Q = R ⁏ (S ⨾ R˘) ⁏ Q := by
  rsimp
  grind

/-- ✱150·14. \(\vdash .R\dagger \mid S\dagger =(R\mid S)\dagger\) -/
theorem pm150_14 {R : α → β → Prop} {S : β → γ → Prop} :
    daggerRel R ⨾ daggerRel S = daggerRel (R ⨾ S) := by
  refine rel_ext' fun X Q => ?_
  show (∃ Y, X = R ⁏ Y ∧ Y = S ⁏ Q) ↔ X = (R ⨾ S) ⁏ Q
  rw [← semi_semi]
  exact ⟨fun ⟨Y, h1, h2⟩ => h2 ▸ h1, fun h => ⟨S ⁏ Q, h, rfl⟩⟩

/-- ✱150·141. \(\vdash .S\dagger =S\parallel \breve{S} \quad[*150·1.*30·41]\) -/
theorem pm150_141 {S : α → β → Prop} : daggerRel S = S ∥ S˘ := daggerRel_eq_dpar S

/-- ✱150·15. \(\vdash .S\dagger \in 1\rightarrow \text{Cls} \quad[*72·14]\) -/
theorem pm150_15 {S : α → β → Prop} : daggerRel S ∈ arrow one Cls :=
  mem_arrow_one_Cls.2 fun _ _ _ ⟨h1, h2⟩ => h1.trans h2.symm

/-- ✱150·151. \(\vdash \colon\ldotp (x).\text{E}!Sʻx: S\in \text{Cls}\rightarrow 1:\supset .S\dagger \in 1\rightarrow 1 \quad[*74·772.*150·141]\) -/
theorem pm150_151 {S : α → β → Prop} :
    (∀ x, EDesc S x) ∧ S ∈ arrow Cls one → daggerRel S ∈ arrow one one := by
  rintro ⟨hE, hS⟩
  refine mem_arrow_one_one.2 ⟨mem_arrow_one_Cls.1 pm150_15, ?_⟩
  rintro X Q R ⟨hQ, hR⟩
  have hQR : S ⁏ Q = S ⁏ R := (hQ : X = S ⁏ Q).symm.trans hR
  choose f hf using hE
  have hf' : ∀ y u, S u y ↔ u = f y := hf
  rw [mem_arrow_Cls_one] at hS
  refine rel_ext' fun z w => ⟨fun h => ?_, fun h => ?_⟩
  · have : (S ⁏ R) (f z) (f w) := hQR ▸ (semi_iff S Q _ _).2
      ⟨z, w, (hf' z _).2 rfl, (hf' w _).2 rfl, h⟩
    obtain ⟨z', w', h1, h2, h3⟩ := (semi_iff S R _ _).1 this
    rw [hS _ _ _ ⟨(hf' z _).2 rfl, h1⟩, hS _ _ _ ⟨(hf' w _).2 rfl, h2⟩]
    exact h3
  · have : (S ⁏ Q) (f z) (f w) := hQR.symm ▸ (semi_iff S R _ _).2
      ⟨z, w, (hf' z _).2 rfl, (hf' w _).2 rfl, h⟩
    obtain ⟨z', w', h1, h2, h3⟩ := (semi_iff S Q _ _).1 this
    rw [hS _ _ _ ⟨(hf' z _).2 rfl, h1⟩, hS _ _ _ ⟨(hf' w _).2 rfl, h2⟩]
    exact h3

/-- ✱150·152. \(\vdash :S\upharpoonright sʻCʻʻ\lambda \in \text{Cls}\rightarrow 1.sʻCʻʻ\lambda \subset \text{ᗡ}ʻS.\supset .(S\dagger )\upharpoonright \lambda \in 1\rightarrow 1\)

`s'C''λ` is `sumCls (C ʻʻ L)`; `(S†) ↾ λ` is `daggerRel S ↾ L`. -/
theorem pm150_152 {S : α → β → Prop} {L : Set (β → β → Prop)} :
    S ↾ sumCls (C ʻʻ L) ∈ arrow Cls one ∧ sumCls (C ʻʻ L) ⊆ codom S →
      daggerRel S ↾ L ∈ arrow one one := by
  rintro ⟨h1, h2⟩
  rw [mem_arrow_Cls_one] at h1
  have hmem : ∀ Q z, Q ∈ L → z ∈ fld Q → z ∈ sumCls (C ʻʻ L) :=
    fun Q z hQ hz => ⟨fld Q, ⟨Q, hQ, rfl⟩, hz⟩
  refine mem_arrow_one_one.2 ⟨fun X Y Q ⟨⟨hX, _⟩, ⟨hY, _⟩⟩ =>
    (hX : X = S ⁏ Q).trans (hY : Y = S ⁏ Q).symm, ?_⟩
  rintro X Q R ⟨⟨hQ, hQL⟩, ⟨hR, hRL⟩⟩
  have e : S ⁏ Q = S ⁏ R := (hQ : X = S ⁏ Q).symm.trans hR
  have key : ∀ Q R : β → β → Prop, Q ∈ L → R ∈ L → S ⁏ Q = S ⁏ R → ∀ z w, Q z w → R z w := by
    intro Q R hQ hR e z w hzw
    obtain ⟨x, hx⟩ := h2 (hmem Q z hQ ⟨w, Or.inl hzw⟩)
    obtain ⟨y, hy⟩ := h2 (hmem Q w hQ ⟨z, Or.inr hzw⟩)
    have : (S ⁏ R) x y := e ▸ (semi_iff S Q x y).2 ⟨z, w, hx, hy, hzw⟩
    obtain ⟨z', w', hxz', hyw', hR'⟩ := (semi_iff S R x y).1 this
    have ez : z = z' := h1 x z z'
      ⟨⟨hx, hmem Q z hQ ⟨w, Or.inl hzw⟩⟩, ⟨hxz', hmem R z' hR ⟨w', Or.inl hR'⟩⟩⟩
    have ew : w = w' := h1 y w w'
      ⟨⟨hy, hmem Q w hQ ⟨z, Or.inr hzw⟩⟩, ⟨hyw', hmem R w' hR ⟨z', Or.inr hR'⟩⟩⟩
    rw [ez, ew]; exact hR'
  exact rel_ext' fun z w => ⟨key Q R hQL hRL e z w, key R Q hRL hQL e.symm z w⟩

/-- ✱150·153. \[\begin{align}\vdash \colon\ldotp S\upharpoonright sʻCʻʻ\lambda \in \text{Cls}\rightarrow 1.sʻCʻʻ\lambda \subset \text{ᗡ}ʻS.Q,&R\in \lambda .\supset :\\ &S^{;}Q=S^{;}R.\supset .Q=R\end{align}\] -/
theorem pm150_153 {S : α → β → Prop} {L : Set (β → β → Prop)} {Q R : β → β → Prop} :
    (S ↾ sumCls (C ʻʻ L) ∈ arrow Cls one ∧ sumCls (C ʻʻ L) ⊆ codom S) ∧ (Q ∈ L ∧ R ∈ L) →
      (S ⁏ Q = S ⁏ R → Q = R) := by
  rintro ⟨h, hQ, hR⟩ e
  exact (mem_arrow_one_one.1 (pm150_152 h)).2 (S ⁏ Q) Q R ⟨⟨rfl, hQ⟩, ⟨e, hR⟩⟩

/-- ✱150·16. \(\vdash .\dot{s} ʻR\dagger ʻʻ\lambda =R\dagger (\dot{s} ʻ\lambda )=R^{;}\dot{s} ʻ\lambda \left[*43·43\frac{\breve{R}}{S}.*150·141·1\right]\)

The chain is the conjunction of its two links; `R†(ṡ'λ)` is the term `daggerOp R (sumRel L)`. -/
theorem pm150_16 {R : α → β → Prop} {L : Set (β → β → Prop)} :
    sumRel (daggerRel R ʻʻ L) = daggerOp R (sumRel L) ∧ daggerOp R (sumRel L) = R ⁏ sumRel L := by
  refine ⟨rel_ext' fun x y => ?_, rfl⟩
  constructor
  · rintro ⟨M, ⟨Q, hQ, hMQ⟩, hM⟩
    rw [show M = R ⁏ Q from hMQ] at hM
    obtain ⟨z, w, h1, h2, h3⟩ := (semi_iff R Q x y).1 hM
    exact (semi_iff R _ x y).2 ⟨z, w, h1, h2, Q, hQ, h3⟩
  · intro h
    obtain ⟨z, w, h1, h2, Q, hQ, h3⟩ := (semi_iff R (sumRel L) x y).1 h
    exact ⟨R ⁏ Q, ⟨Q, hQ, rfl⟩, (semi_iff R Q x y).2 ⟨z, w, h1, h2, h3⟩⟩

/-- ✱150·17. \(\vdash .(R\upharpoonright \lambda )\dagger =R\dagger \mid \unicode{x0294f}\lambda\)

`⥏λ` is the relation `♀λ` of ✱38 with `♀ = ⥏`, `opR fres L` (`P⥏λ` to `P`). -/
theorem pm150_17 {R : α → β → Prop} {L : Set β} :
    daggerRel (R ↾ L) = daggerRel R ⨾ opR fres L := by
  refine rel_ext' fun X P => ?_
  show X = (R ↾ L) ⁏ P ↔ ∃ Y, X = R ⁏ Y ∧ Y = P ⥏ L
  rw [cres_semi]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨Y, h1, h2⟩ => h2 ▸ h1⟩

/-- ✱150·171. \(\vdash :sʻCʻʻCʻQ\subset \lambda .\supset .(R\upharpoonright \lambda )\dagger ^{;}Q=R\dagger ^{;}Q.\unicode{x0294f}\lambda ^{;}Q=Q\)

`s'C''C'Q` is `sumCls (C ʻʻ fld Q)`. -/
theorem pm150_171 {R : α → β → Prop} {L : Set β} {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    sumCls (C ʻʻ fld Q) ⊆ L → daggerRel (R ↾ L) ⁏ Q = daggerRel R ⁏ Q ∧ opR fres L ⁏ Q = Q := by
  intro hL
  have hfix : ∀ X, X ∈ fld Q → X ⥏ L = X := fun X hX =>
    fres_eq_self fun z hz => hL ⟨fld X, ⟨X, hX, rfl⟩, hz⟩
  have h2 : opR fres L ⁏ Q = Q := by
    refine rel_ext' fun M N => ?_
    rw [show opR fres L = graph (fun X : β → β → Prop => X ⥏ L) from rfl, semi_graph_apply]
    constructor
    · rintro ⟨X, Y, ⟨rfl, rfl⟩, hXY⟩
      rw [hfix X ⟨Y, Or.inl hXY⟩, hfix Y ⟨X, Or.inr hXY⟩]; exact hXY
    · intro h
      exact ⟨M, N, ⟨(hfix M ⟨N, Or.inl h⟩).symm, (hfix N ⟨M, Or.inr h⟩).symm⟩, h⟩
  refine ⟨?_, h2⟩
  rw [pm150_17, ← semi_semi, h2]

/-- ✱150·2. \(\vdash .\text{D}ʻS^{;}Q=SʻʻQʻʻ\text{ᗡ}ʻS.\text{ᗡ}ʻS^{;}Q=Sʻʻ\breve{Q} ʻʻ\text{ᗡ}ʻS \quad[*37·32.*150·1]\) -/
theorem pm150_2 {S : α → β → Prop} {Q : β → β → Prop} :
    dom (S ⁏ Q) = S ʻʻ Q ʻʻ codom S ∧ codom (S ⁏ Q) = S ʻʻ Q˘ ʻʻ codom S := by
  rsimp
  grind

/-- ✱150·201. \(\vdash .CʻS^{;}Q=Sʻʻ(Q\unicode{x228d} \breve{Q} )ʻʻ\text{ᗡ}ʻS=\text{D}ʻS^{;}(Q\unicode{x228d} \breve{Q} )\) -/
theorem pm150_201 {S : α → β → Prop} {Q : β → β → Prop} :
    fld (S ⁏ Q) = S ʻʻ (Q ⊍ Q˘) ʻʻ codom S ∧ S ʻʻ (Q ⊍ Q˘) ʻʻ codom S = dom (S ⁏ (Q ⊍ Q˘)) := by
  rsimp
  grind

/-- ✱150·202. \(\vdash .\text{D}ʻS^{;}Q\subset Sʻʻ\text{D}ʻQ.\text{ᗡ}ʻS^{;}Q\subset Sʻʻ\text{ᗡ}ʻQ.CʻS^{;}Q\subset SʻʻCʻQ\) -/
theorem pm150_202 {S : α → β → Prop} {Q : β → β → Prop} :
    (dom (S ⁏ Q) ⊆ S ʻʻ dom Q ∧ codom (S ⁏ Q) ⊆ S ʻʻ codom Q) ∧ fld (S ⁏ Q) ⊆ S ʻʻ fld Q := by
  rsimp
  grind

/-- ✱150·203. \(\vdash .CʻS^{;}Q\subset \text{D}ʻS \quad[*150·202.*37·15]\) -/
theorem pm150_203 {S : α → β → Prop} {Q : β → β → Prop} : fld (S ⁏ Q) ⊆ dom S := by
  rsimp
  grind

/-- ✱150·21. \(\vdash :\text{ᗡ}ʻQ\subset \text{ᗡ}ʻS.\supset .\text{D}ʻS^{;}Q=Sʻʻ\text{D}ʻQ=\text{D}ʻ(S\mid Q) \quad[*150·2.*37·27·32]\) -/
theorem pm150_21 {S : α → β → Prop} {Q : β → β → Prop} :
    codom Q ⊆ codom S → dom (S ⁏ Q) = S ʻʻ dom Q ∧ S ʻʻ dom Q = dom (S ⨾ Q) := by
  rsimp
  grind

/-- ✱150·211. \[\begin{align}&\vdash :\text{D}ʻQ\subset \text{ᗡ}ʻS.\supset .\text{ᗡ}ʻS^{;}Q=Sʻʻ\text{ᗡ}ʻQ=\text{D}ʻ(S\mid \breve{Q} )\\ &[*150·2.*37·271·32]\end{align}\] -/
theorem pm150_211 {S : α → β → Prop} {Q : β → β → Prop} :
    dom Q ⊆ codom S → codom (S ⁏ Q) = S ʻʻ codom Q ∧ S ʻʻ codom Q = dom (S ⨾ Q˘) := by
  rsimp
  grind

/-- ✱150·22. \(\vdash :CʻQ\subset \text{ᗡ}ʻS.\supset .CʻS^{;}Q=SʻʻCʻQ \quad[*150·21·211.*37·22]\) -/
theorem pm150_22 {S : α → β → Prop} {Q : β → β → Prop} :
    fld Q ⊆ codom S → fld (S ⁏ Q) = S ʻʻ fld Q := by
  rsimp
  grind

/-- ✱150·23. \(\vdash :CʻQ=\text{ᗡ}ʻS.\supset .CʻS^{;}Q=\text{D}ʻS \quad[*150·22.*37·25]\) -/
theorem pm150_23 {S : α → β → Prop} {Q : β → β → Prop} :
    fld Q = codom S → fld (S ⁏ Q) = dom S := by
  rsimp
  grind

/-- ✱150·24. \(\vdash \colon\ldotp CʻQ\subset \text{ᗡ}ʻS.\supset :_{\dot{\exists} }!S^{;}Q.\equiv ._{\dot{\exists} }!Q\) -/
theorem pm150_24 {S : α → β → Prop} {Q : β → β → Prop} :
    fld Q ⊆ codom S → (rEx (S ⁏ Q) ↔ rEx Q) := by
  rsimp
  grind

/-- ✱150·25. \(\vdash \colon\ldotp (y).\text{E}!Sʻy.\supset :_{\dot{\exists} }!S^{;}Q.\equiv ._{\dot{\exists} }!Q \quad[*150·24.*33·431]\) -/
theorem pm150_25 {S : α → β → Prop} {Q : β → β → Prop} :
    (∀ y, EDesc S y) → (rEx (S ⁏ Q) ↔ rEx Q) := by
  intro h
  refine pm150_24 fun z _ => ?_
  obtain ⟨b, hb⟩ := h z
  exact ⟨b, (hb b).2 rfl⟩

/-- ✱150·3. \(\vdash .S^{;}(Q\unicode{x228d} R)=S^{;}Q\unicode{x228d} S^{;}R \quad[*34·25·26.*150·1]\) -/
theorem pm150_3 {S : α → β → Prop} {Q R : β → β → Prop} : S ⁏ (Q ⊍ R) = S ⁏ Q ⊍ S ⁏ R := by
  rsimp
  grind

/-- ✱150·301. \(\vdash .S^{;}(Q\dot{\cap} R)\,\unicode{x2abd}\, (S^{;}Q)\dot{\cap} (S^{;}R) \quad[*34·23·24.*150·1]\) -/
theorem pm150_301 {S : α → β → Prop} {Q R : β → β → Prop} :
    S ⁏ (Q ⩀ R) ⪽ (S ⁏ Q) ⩀ (S ⁏ R) := by
  rsimp
  grind

/-- ✱150·31. \(\vdash :P\,\unicode{x2abd}\, Q.R\,\unicode{x2abd}\, S.\supset .R^{;}P\,\unicode{x2abd}\, S^{;}Q \quad[*34·34.*150·1]\) -/
theorem pm150_31 {P Q : β → β → Prop} {R S : α → β → Prop} :
    P ⪽ Q ∧ R ⪽ S → R ⁏ P ⪽ S ⁏ Q := by
  rsimp
  grind

/-- ✱150·32. \(\vdash .(S\upharpoonright CʻQ)^{;}Q=S^{;}Q \left[*43.5\frac{S,\,\breve{S},\,CʻQ,\,CʻQ}{Q,\,R,\,\alpha,\,\beta }.*150·141\right]\) -/
theorem pm150_32 {S : α → β → Prop} {Q : β → β → Prop} : (S ↾ fld Q) ⁏ Q = S ⁏ Q := by
  rsimp
  grind

/-- ✱150·33. \(\vdash :CʻQ\subset \beta .\supset .(S\upharpoonright \beta )^{;}Q=S^{;}Q \left[*43·5\frac{S,\,\breve{S}}{Q,\,R}.*150·141\right]\) -/
theorem pm150_33 {S : α → β → Prop} {Q : β → β → Prop} {B : Set β} :
    fld Q ⊆ B → (S ↾ B) ⁏ Q = S ⁏ Q := by
  rsimp
  grind

/-- ✱150·34. \[\begin{align}&\vdash :\text{D}ʻQ\subset \alpha .\text{ᗡ}ʻQ\subset \beta .\supset .S\upharpoonright \alpha \mid Q\mid \beta \upharpoonleft \breve{S} =S^{;}\alpha \upharpoonleft Q\upharpoonright \beta =S^{;}Q\\ &[*43·5.*35·354.*150·141·1]\end{align}\]

`S↾α | Q | β↿S̆` is `(S ↾ A) ⨾ Q ⨾ (B ◁ S˘)` (only this bracketing is significant), and
`S;α↿Q↾β` is `S ⁏ A ◁ Q ↾ B`, i.e. `S;(α↿Q↾β)`. The chain is the conjunction of its links. -/
theorem pm150_34 {S : α → β → Prop} {Q : β → β → Prop} {A B : Set β} :
    dom Q ⊆ A ∧ codom Q ⊆ B →
      (S ↾ A) ⨾ Q ⨾ (B ◁ S˘) = S ⁏ A ◁ Q ↾ B ∧ S ⁏ A ◁ Q ↾ B = S ⁏ Q := by
  rsimp
  grind

/-- ✱150·35. \(\vdash \colon\ldotp y\in CʻQ.\supset _{y}.Rʻy=Sʻy:\supset .R^{;}Q=S^{;}Q\)

`R'y = S'y` has two descriptions, the first with the larger scope (✱14·113). -/
theorem pm150_35 {R S : α → β → Prop} {Q : β → β → Prop} :
    (∀ y, y ∈ fld Q → Desc R y (fun u => Desc S y (fun v => u = v))) → R ⁏ Q = S ⁏ Q := by
  rsimp
  grind

/-- ✱150·36. \(\vdash .(S\upharpoonright \beta )^{;}Q=S^{;}(Q\unicode{x0294f}\beta )\) -/
theorem pm150_36 {S : α → β → Prop} {Q : β → β → Prop} {B : Set β} :
    (S ↾ B) ⁏ Q = S ⁏ (Q ⥏ B) := by
  rsimp
  grind

/-- ✱150·361. \(\vdash .(\alpha \upharpoonleft S)^{;}Q=(S^{;}Q)\unicode{x0294f}\alpha \quad[\text{Proof as in *150·36}]\) -/
theorem pm150_361 {S : α → β → Prop} {Q : β → β → Prop} {A : Set α} :
    (A ◁ S) ⁏ Q = (S ⁏ Q) ⥏ A := by
  rsimp
  grind

/-- ✱150·37. \[\begin{align}\vdash :S\in \text{Cls}\rightarrow 1.\supset .S^{;}(Q\unicode{x0294f}\beta )&=(S^{;}Q)\unicode{x0294f}Sʻʻ\beta \\ &=(S\upharpoonright \beta )^{;}Q={(Sʻʻ\beta )\upharpoonleft S}^{;}Q\end{align}\]

The chain of four is the conjunction of its three links. -/
theorem pm150_37 {S : α → β → Prop} {Q : β → β → Prop} {B : Set β} :
    S ∈ arrow Cls one →
      (S ⁏ (Q ⥏ B) = (S ⁏ Q) ⥏ S ʻʻ B ∧ (S ⁏ Q) ⥏ S ʻʻ B = (S ↾ B) ⁏ Q) ∧
        (S ↾ B) ⁏ Q = (S ʻʻ B ◁ S) ⁏ Q := by
  rsimp
  grind

/-- ✱150·38. \(\vdash :S\in 1\rightarrow 1.\supset .S^{;}\breve{S} ^{;}Q=Q\unicode{x0294f}\text{D}ʻS\) -/
theorem pm150_38 {S : α → β → Prop} {Q : α → α → Prop} :
    S ∈ arrow one one → S ⁏ S˘ ⁏ Q = Q ⥏ dom S := by
  rsimp
  grind

/-- ✱150·4. \[\begin{align}&\vdash \colon\ldotp S\in 1\rightarrow \text{Cls}.\supset :x(S^{;}Q)y.\equiv .(\exists z,w).x=Sʻz.y=Sʻw.zQw\\ &[*150·11.*71·36]\end{align}\]

`x = S'z` is `Desc S z (fun u => x = u)` (the description has the smallest scope). -/
theorem pm150_4 {S : α → β → Prop} {Q : β → β → Prop} {x y : α} :
    S ∈ arrow one Cls →
      ((S ⁏ Q) x y ↔ ∃ z w, (Desc S z (fun u => x = u) ∧ Desc S w (fun u => y = u)) ∧ Q z w) := by
  rsimp
  grind

/-- ✱150·41. \(\vdash \colon\ldotp S\in \text{Cls}\rightarrow 1.\supset :x(S^{;}Q)y.\equiv .(\breve{S} ʻx)Q(\breve{S} ʻy) \quad[*150·11.*71·331]\)

`(S̆'x)Q(S̆'y)` has two descriptions, the first with the larger scope. -/
theorem pm150_41 {S : α → β → Prop} {Q : β → β → Prop} {x y : α} :
    S ∈ arrow Cls one →
      ((S ⁏ Q) x y ↔ Desc S˘ x (fun u => Desc S˘ y (fun v => Q u v))) := by
  rsimp
  grind

/-- ✱150·42. \(\vdash .S^{;}\dot{\Lambda} =\dot{\Lambda} \quad[*150·1.*34·32]\) -/
theorem pm150_42 {S : α → β → Prop} : S ⁏ (rNull : β → β → Prop) = rNull := by
  rsimp
  grind

/-- ✱150·5. \(\vdash :\alpha (\overrightarrow{R}^{;}P)\beta .\equiv .(\exists x,y).\alpha =\overrightarrow{R}ʻx.\beta =\overrightarrow{R}ʻy.xPy\)

`R⃗` is `Rfwd R = graph (refs R)`, so `R⃗'x` is `refs R x` (Basic §5). -/
theorem pm150_5 {R : α → β → Prop} {P : β → β → Prop} {A B : Set α} :
    (Rfwd R ⁏ P) A B ↔ ∃ x y, (A = refs R x ∧ B = refs R y) ∧ P x y :=
  semi_graph_apply _ _ _ _

/-- ✱150·51. \(\vdash :\alpha (\text{D}^{;}R)\beta .\equiv .(\exists P,Q).\alpha =\text{D}ʻP.\beta =\text{D}ʻQ.PRQ\) -/
theorem pm150_51 {R : (α → β → Prop) → (α → β → Prop) → Prop} {A B : Set α} :
    (D ⁏ R) A B ↔ ∃ P Q, (A = dom P ∧ B = dom Q) ∧ R P Q :=
  semi_graph_apply _ _ _ _

/-- ✱150·511. \(\vdash :\alpha (\text{ᗡ}^{;}R)\beta .\equiv .(\exists P,Q).\alpha =\text{ᗡ}ʻP.\beta =\text{ᗡ}ʻQ.PRQ\) -/
theorem pm150_511 {R : (α → β → Prop) → (α → β → Prop) → Prop} {A B : Set β} :
    (Dcnv ⁏ R) A B ↔ ∃ P Q, (A = codom P ∧ B = codom Q) ∧ R P Q :=
  semi_graph_apply _ _ _ _

/-- ✱150·512. \(\vdash :\alpha (C^{;}R)\beta .\equiv .(\exists P,Q).\alpha =CʻR.\beta =CʻQ.PRQ\)

**Status.** proved (reading): transcription error: the e-text prints `α = C'R` for
`α = C'P` (`C'R` is a class of relations, `α` a class of terms, so the printed formula is
not significant; cf. ✱150·51·511). -/
theorem pm150_512 {R : (α → α → Prop) → (α → α → Prop) → Prop} {A B : Set α} :
    (C ⁏ R) A B ↔ ∃ P Q, (A = fld P ∧ B = fld Q) ∧ R P Q :=
  semi_graph_apply _ _ _ _

/-- ✱150·52. \[\begin{align}&\vdash :x(F^{;}R)y.\equiv .(\exists P,Q).x\in CʻP.y\in CʻQ.PRQ\\ &[*150·11.*33·51]\end{align}\]

`xFP` is `x ∈ C'P` (✱33·04). -/
theorem pm150_52 {R : (α → α → Prop) → (α → α → Prop) → Prop} {x y : α} :
    (F ⁏ R) x y ↔ ∃ P Q, (x ∈ fld P ∧ y ∈ fld Q) ∧ R P Q :=
  semi_apply _ _ _ _

/-- ✱150·53. \(\vdash .I^{;}P=P \quad[*50·4]\) -/
theorem pm150_53 {P : α → α → Prop} : (I : α → α → Prop) ⁏ P = P := by
  rsimp
  grind

/-- ✱150·531. \(\vdash .P^{;}I=P\mid \breve{P} \quad[*50·4]\) -/
theorem pm150_531 {P : α → β → Prop} : P ⁏ (I : β → β → Prop) = P ⨾ P˘ := by
  rsimp
  grind

/-- ✱150·532. \(\vdash .P^{;}I^{;}Q=P^{;}Q \quad[*150·13.*50·4]\) -/
theorem pm150_532 {P : α → β → Prop} {Q : β → β → Prop} : P ⁏ I ⁏ Q = P ⁏ Q := by
  rsimp
  grind

/-- ✱150·534. \(\vdash .(I\upharpoonright CʻP)^{;}P=P \quad[*150·53·32]\) -/
theorem pm150_534 {P : α → α → Prop} : (I ↾ fld P) ⁏ P = P := by
  rsimp
  grind

/-- ✱150·535. \(\vdash :CʻP\subset \alpha .\supset .(I\upharpoonright \alpha )^{;}P=P \quad[*150·53·33]\) -/
theorem pm150_535 {P : α → α → Prop} {A : Set α} : fld P ⊆ A → (I ↾ A) ⁏ P = P := by
  rsimp
  grind

/-- ✱150·54. \(\vdash :\alpha (\iota ^{;}R)\beta .\equiv .(\breve{\iota} ʻ\alpha )R(\breve{\iota} ʻ\beta )\)

`ῐ'α` is a description (`Desc iota˘ A ψ`), which exists only when `α` is a unit class; the
first description has the larger scope. -/
theorem pm150_54 {R : α → α → Prop} {A B : Set α} :
    (iota ⁏ R) A B ↔ Desc iota˘ A (fun x => Desc iota˘ B (fun y => R x y)) := by
  have key : ∀ (A : Set α) (ψ : α → Prop), Desc iota˘ A ψ ↔ ∃ a, A = ι a ∧ ψ a := by
    intro A ψ
    constructor
    · rintro ⟨a, ha, hψ⟩; exact ⟨a, (ha a).2 rfl, hψ⟩
    · rintro ⟨a, rfl, hψ⟩
      refine ⟨a, fun x => ⟨fun h => (unitCls_injective (h : ι a = ι x)).symm, fun e => ?_⟩, hψ⟩
      subst e; rfl
  rw [key, semi_iff]
  simp only [key]
  constructor
  · rintro ⟨x, y, h1, h2, h3⟩; exact ⟨x, h1, y, h2, h3⟩
  · rintro ⟨x, h1, y, h2, h3⟩; exact ⟨x, y, h1, h2, h3⟩

/-- ✱150·541. \(\vdash :x(\breve{\iota} ^{;}R)y.\equiv .(\iota ʻx)R(\iota ʻy)\)

`ι'x` always exists and is `ι x` (`desc_iota`). -/
theorem pm150_541 {R : Set α → Set α → Prop} {x y : α} : (iota˘ ⁏ R) x y ↔ R (ι x) (ι y) := by
  rw [semi_iff]
  constructor
  · rintro ⟨A, B, h1, h2, h3⟩
    obtain rfl : A = ι x := h1
    obtain rfl : B = ι y := h2
    exact h3
  · exact fun h => ⟨ι x, ι y, rfl, rfl, h⟩

/-- ✱150·55. \(\vdash :Q(\downarrow z^{;}P)R.\equiv .(\exists u,v).Q=u\downarrow z.R=v\downarrow z.uPv\)

`↓z` is `coupleR z` (`u ↓ z` to `u`). -/
theorem pm150_55 {z : β} {P : α → α → Prop} {Q R : α → β → Prop} :
    (coupleR z ⁏ P) Q R ↔ ∃ u v, (Q = u ↓ z ∧ R = v ↓ z) ∧ P u v :=
  semi_graph_apply _ _ _ _

/-- ✱150·56. \[\begin{align}&\vdash :M(S\dagger ^{;}Q)N.\equiv .(\exists X,Y).XQY.M=S^{;}X.N=S^{;}Y\\ &[*150·4·15·1]\end{align}\] -/
theorem pm150_56 {S : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    {M N : α → α → Prop} :
    (daggerRel S ⁏ Q) M N ↔ ∃ X Y, (Q X Y ∧ M = S ⁏ X) ∧ N = S ⁏ Y := by
  rw [semi_apply]
  exact ⟨fun ⟨X, Y, ⟨h1, h2⟩, h3⟩ => ⟨X, Y, ⟨h3, h1⟩, h2⟩,
    fun ⟨X, Y, ⟨h3, h1⟩, h2⟩ => ⟨X, Y, ⟨h1, h2⟩, h3⟩⟩

/-- ✱150·6. \(\vdash .P\unicode{x2640}_{.,}y=\unicode{x2640}y^{;}P \quad[(*150·03)]\) -/
theorem pm150_6 {f : α → β → γ} {P : α → α → Prop} {y : β} : opSemi f P y = opR f y ⁏ P := rfl

/-- ✱150·601. \(\vdash .P\unicode{x2640}_{.,}\in 1\rightarrow \text{Cls} \quad[*150·6.*14·21.*71·166]\)

The relation `P♀.,` (of `P♀.,y` to `y`) is `opL (opSemi f) P`. -/
theorem pm150_601 {f : α → β → γ} {P : α → α → Prop} : opL (opSemi f) P ∈ arrow one Cls :=
  mem_arrow_one_Cls.2 fun _ _ _ ⟨h1, h2⟩ => h1.trans h2.symm

/-- ✱150·61. \[\begin{align}&\vdash :z(P\unicode{x2640}_{.,}y)w.\equiv .(\exists u,v).z=u\unicode{x2640}y.w=v\unicode{x2640}y.uPv\\ &[*150·11.*38·101.*150·6]\end{align}\]

`u♀y` is `f u y`. -/
theorem pm150_61 {f : α → β → γ} {P : α → α → Prop} {y : β} {z w : γ} :
    opSemi f P y z w ↔ ∃ u v, (z = f u y ∧ w = f v y) ∧ P u v :=
  semi_graph_apply _ _ _ _

/-- ✱150·62. \[\begin{align}&\vdash :R(P\unicode{x2640}_{.,}^{;}Q)S.\equiv .(\exists z,w).R=\unicode{x2640}z^{;}P.S=\unicode{x2640}w^{;}P.zQw\\ &[*150·4·601·6]\end{align}\] -/
theorem pm150_62 {f : α → β → γ} {P : α → α → Prop} {Q : β → β → Prop} {R S : γ → γ → Prop} :
    (opL (opSemi f) P ⁏ Q) R S ↔ ∃ z w, (R = opR f z ⁏ P ∧ S = opR f w ⁏ P) ∧ Q z w :=
  semi_graph_apply _ _ _ _

/-- ✱150·7. \(\vdash .S^{;}(z\downarrow w)=\overrightarrow{S}ʻz\uparrow \overrightarrow{S}ʻw \quad [*55·6]\) -/
theorem pm150_7 {S : α → β → Prop} {z w : β} : S ⁏ (z ↓ w) = cross (refs S z) (refs S w) := by
  rsimp
  grind

/-- ✱150·71. \(\vdash :S\in 1\rightarrow \text{Cls}.z,w\in \text{ᗡ}ʻS.\supset .S^{;}(z\downarrow w)=(Sʻz)\downarrow (Sʻw) \quad[*55·61]\)

The descriptions `S'z`, `S'w` have the whole equation for scope, `S'z` the larger one. -/
theorem pm150_71 {S : α → β → Prop} {z w : β} :
    S ∈ arrow one Cls ∧ (z ∈ codom S ∧ w ∈ codom S) →
      Desc S z (fun a => Desc S w (fun b => S ⁏ (z ↓ w) = a ↓ b)) := by
  rintro ⟨hS, ⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [mem_arrow_one_Cls] at hS
  have ua : ∀ u, S u z ↔ u = a := fun u => ⟨fun h => hS u a z ⟨h, ha⟩, fun e => e ▸ ha⟩
  have ub : ∀ u, S u w ↔ u = b := fun u => ⟨fun h => hS u b w ⟨h, hb⟩, fun e => e ▸ hb⟩
  refine (TheIs_iff_of_unique ua).2 ((TheIs_iff_of_unique ub).2 ?_)
  refine rel_ext' fun x y => ?_
  rw [semi_iff]
  simp only [couple_apply]
  constructor
  · rintro ⟨z', w', h1, h2, rfl, rfl⟩; exact ⟨(ua x).1 h1, (ub y).1 h2⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨z, w, ha, hb, rfl, rfl⟩

/-- ✱150·72. \(\vdash :z\neq w.S=x\downarrow z\unicode{x228d} y\downarrow w.\supset .S^{;}(z\downarrow w)=x\downarrow y \quad[*55·62·61]\) -/
theorem pm150_72 {x y : α} {z w : β} {S : α → β → Prop} :
    z ≠ w ∧ S = x ↓ z ⊍ y ↓ w → S ⁏ (z ↓ w) = x ↓ y := by
  rsimp
  grind

/-- ✱150·73. \(\vdash .S^{;}(\alpha \uparrow \beta )=Sʻʻ\alpha \uparrow Sʻʻ\beta \quad\left[*37·82 \frac{S,\,\breve{S}}{R,\,S}\right]\) -/
theorem pm150_73 {S : α → β → Prop} {A B : Set β} :
    S ⁏ cross A B = cross (S ʻʻ A) (S ʻʻ B) := by
  rsimp
  grind

/-- ✱150·74. \(\vdash .(S\unicode{x228d} T)^{;}Q=S^{;}Q\unicode{x228d} T^{;}Q\unicode{x228d} S\mid Q\mid \breve{T} \unicode{x228d} T\mid Q\mid \breve{S} \quad[*150·1]\)

`S;Q ∪̇ T;Q ∪̇ S|Q|T̆ ∪̇ T|Q|S̆` is `((S;Q ∪̇ T;Q) ∪̇ S|Q|T̆) ∪̇ T|Q|S̆` (precedences of
`⁏`, `⊍`, `⨾`). -/
theorem pm150_74 {S T : α → β → Prop} {Q : β → β → Prop} :
    (S ⊍ T) ⁏ Q = S ⁏ Q ⊍ T ⁏ Q ⊍ S ⨾ Q ⨾ T˘ ⊍ T ⨾ Q ⨾ S˘ := by
  rsimp
  grind

/-- ✱150·75. \(\vdash :{\sim}(yQy).\supset .(S\unicode{x228d} x\downarrow y)^{;}Q=S^{;}Q\unicode{x228d} Sʻʻ\overrightarrow{Q}ʻy\uparrow \iota ʻx\unicode{x228d} \iota ʻx\uparrow Sʻʻ\overleftarrow{Q}ʻy\)

`Q⃗'y` is `refs Q y`, `Q⃖'y` is `rels Q y`; `S''Q⃗'y ↑ ι'x` is `cross (S ʻʻ refs Q y) (ι x)`. -/
theorem pm150_75 {S : α → β → Prop} {Q : β → β → Prop} {x : α} {y : β} :
    ¬ Q y y → (S ⊍ x ↓ y) ⁏ Q =
      S ⁏ Q ⊍ cross (S ʻʻ refs Q y) (ι x) ⊍ cross (ι x) (S ʻʻ rels Q y) := by
  intro hQ
  refine rel_ext' fun u v => ?_
  simp only [rcup, semi_iff]
  show (∃ a b, (S u a ∨ (u = x ∧ a = y)) ∧ (S v b ∨ (v = x ∧ b = y)) ∧ Q a b) ↔
    ((∃ a b, S u a ∧ S v b ∧ Q a b) ∨ ((∃ a, a ∈ refs Q y ∧ S u a) ∧ v = x)) ∨
      (u = x ∧ ∃ b, b ∈ rels Q y ∧ S v b)
  constructor
  · rintro ⟨a, b, h1 | ⟨rfl, rfl⟩, h2 | ⟨rfl, rfl⟩, h3⟩
    · exact Or.inl (Or.inl ⟨a, b, h1, h2, h3⟩)
    · exact Or.inl (Or.inr ⟨⟨a, h3, h1⟩, rfl⟩)
    · exact Or.inr ⟨rfl, b, h3, h2⟩
    · exact absurd h3 hQ
  · rintro ((⟨a, b, h1, h2, h3⟩ | ⟨⟨a, h3, h1⟩, rfl⟩) | ⟨rfl, b, h3, h2⟩)
    · exact ⟨a, b, Or.inl h1, Or.inl h2, h3⟩
    · exact ⟨a, y, Or.inl h1, Or.inr ⟨rfl, rfl⟩, h3⟩
    · exact ⟨y, b, Or.inr ⟨rfl, rfl⟩, Or.inl h2, h3⟩

/-- ✱150·8. \[\begin{align}\vdash \colon\ldotp S\in \text{Cls}\rightarrow 1:\text{D}ʻQ\subset &\text{ᗡ}ʻS.\lor.\text{ᗡ}ʻQ\subset \text{ᗡ}ʻS:P\in \text{Pot}ʻQ:\supset .\\ &S^{;}P\in \text{Pot}ʻ(S^{;}Q).(S^{;}P)\mid (S^{;}Q)=S^{;}(P\mid Q)\end{align}\]

The hypothesis is the product of three (`Pot'Q` is `pot Q`), bracketed to the left. -/
theorem pm150_8 {S : α → β → Prop} {Q P : β → β → Prop} :
    (S ∈ arrow Cls one ∧ (dom Q ⊆ codom S ∨ codom Q ⊆ codom S)) ∧ P ∈ pot Q →
      S ⁏ P ∈ pot (S ⁏ Q) ∧ (S ⁏ P) ⨾ (S ⁏ Q) = S ⁏ (P ⨾ Q) := by
  rintro ⟨⟨hS, hQ⟩, hP⟩
  have key : ∀ X, X ∈ pot Q → (S ⁏ X) ⨾ (S ⁏ Q) = S ⁏ (X ⨾ Q) := fun X hX =>
    semi_comp_semi hS (hQ.imp_right fun h => (codom_pot_subset hX).trans h)
  refine ⟨?_, key P hP⟩
  refine pot_induction (motive := fun X => S ⁏ X ∈ pot (S ⁏ Q)) (self_mem_pot _) ?_ hP
  intro X hX ih
  rw [← key X hX]; exact relProd_mem_pot ih

/-- ✱150·81. \[\begin{align}\vdash \colon\ldotp S\in \text{Cls}\rightarrow 1:\text{D}ʻQ\subset \text{ᗡ}ʻS.\lor.\text{ᗡ}ʻQ\subset &\text{ᗡ}ʻS:T\in \text{Pot}ʻS^{;}Q:\supset .\\ &(\exists P).P\in \text{Pot}ʻQ.T=S^{;}P\end{align}\] -/
theorem pm150_81 {S : α → β → Prop} {Q : β → β → Prop} {T : α → α → Prop} :
    (S ∈ arrow Cls one ∧ (dom Q ⊆ codom S ∨ codom Q ⊆ codom S)) ∧ T ∈ pot (S ⁏ Q) →
      ∃ P, P ∈ pot Q ∧ T = S ⁏ P := by
  rintro ⟨⟨hS, hQ⟩, hT⟩
  refine pot_induction (motive := fun T => ∃ P, P ∈ pot Q ∧ T = S ⁏ P)
    ⟨Q, self_mem_pot Q, rfl⟩ ?_ hT
  rintro X - ⟨P, hP, rfl⟩
  exact ⟨P ⨾ Q, relProd_mem_pot hP, ((pm150_8 ⟨⟨hS, hQ⟩, hP⟩).2).symm ▸ rfl⟩

/-- ✱150·82. \(\vdash \colon\ldotp S \in \text{Cls} \rightarrow 1 : \text{D}ʻQ \subset \text{ᗡ}ʻS . \lor . \text{ᗡ}ʻQ \subset \text{ᗡ}ʻS : \supset . \text{Pot}ʻS^{;}Q = S\dagger ʻʻ\text{Pot}ʻQ\)

`S†''Pot'Q` is `daggerRel S ʻʻ pot Q`. -/
theorem pm150_82 {S : α → β → Prop} {Q : β → β → Prop} :
    S ∈ arrow Cls one ∧ (dom Q ⊆ codom S ∨ codom Q ⊆ codom S) →
      pot (S ⁏ Q) = daggerRel S ʻʻ pot Q := by
  intro h
  ext T
  constructor
  · intro hT
    obtain ⟨P, hP, rfl⟩ := pm150_81 ⟨h, hT⟩
    exact ⟨P, hP, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact (pm150_8 ⟨h, hP⟩).1

/-- ✱150·83. \(\vdash \colon\ldotp S\in \text{Cls} \rightarrow 1 : \text{D}ʻQ \subset \text{ᗡ}ʻS . \lor . \text{ᗡ}ʻQ \subset \text{ᗡ}ʻS : \supset . (S^{;}Q)_{\text{po}} = S^{;}Q_{\text{po}}\)

`Q_po` is `po Q` (✱91·05). -/
theorem pm150_83 {S : α → β → Prop} {Q : β → β → Prop} :
    S ∈ arrow Cls one ∧ (dom Q ⊆ codom S ∨ codom Q ⊆ codom S) → po (S ⁏ Q) = S ⁏ po Q := by
  intro h
  refine rel_ext' fun x y => ?_
  show (∃ T, T ∈ pot (S ⁏ Q) ∧ T x y) ↔ _
  rw [pm150_82 h, semi_iff]
  constructor
  · rintro ⟨T, ⟨P, hP, rfl⟩, hxy⟩
    obtain ⟨z, w, h1, h2, h3⟩ := (semi_iff S P x y).1 hxy
    exact ⟨z, w, h1, h2, P, hP, h3⟩
  · rintro ⟨z, w, h1, h2, P, hP, h3⟩
    exact ⟨S ⁏ P, ⟨P, hP, rfl⟩, (semi_iff S P x y).2 ⟨z, w, h1, h2, h3⟩⟩

/-- ✱150·9. \(\vdash . (I\dagger )^{;}Q = Q\) -/
theorem pm150_9 {Q : (α → α → Prop) → (α → α → Prop) → Prop} :
    daggerRel (I : α → α → Prop) ⁏ Q = Q := by
  refine rel_ext' fun M N => ?_
  rw [pm150_56]
  simp only [pm150_53]
  exact ⟨fun ⟨X, Y, ⟨h, e1⟩, e2⟩ => e1 ▸ e2 ▸ h, fun h => ⟨M, N, ⟨h, rfl⟩, rfl⟩⟩

/-- ✱150·91. \(\vdash : sʻCʻʻCʻQ \subset \alpha .\supset . (I \upharpoonright \alpha )\dagger ^{;}Q = Q\) -/
theorem pm150_91 {A : Set α} {Q : (α → α → Prop) → (α → α → Prop) → Prop} :
    sumCls (C ʻʻ fld Q) ⊆ A → daggerRel (I ↾ A) ⁏ Q = Q := by
  intro hA
  have h : ∀ X, X ∈ fld Q → (I ↾ A) ⁏ X = X := fun X hX =>
    pm150_535 fun z hz => hA ⟨fld X, ⟨X, hX, rfl⟩, hz⟩
  refine rel_ext' fun M N => ?_
  rw [pm150_56]
  constructor
  · rintro ⟨X, Y, ⟨hXY, e1⟩, e2⟩
    rw [e1, e2, h X ⟨Y, Or.inl hXY⟩, h Y ⟨X, Or.inr hXY⟩]
    exact hXY
  · intro hMN
    exact ⟨M, N, ⟨hMN, (h M ⟨N, Or.inl hMN⟩).symm⟩, (h N ⟨M, Or.inr hMN⟩).symm⟩

/-- ✱150·92. \(\vdash : S \in \text{Cls} \rightarrow 1 . sʻCʻʻCʻQ \subset \text{ᗡ}ʻS. \supset . \breve{S} \dagger ^{;}S\dagger ^{;}Q = Q\) -/
theorem pm150_92 {S : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    S ∈ arrow Cls one ∧ sumCls (C ʻʻ fld Q) ⊆ codom S → daggerRel S˘ ⁏ daggerRel S ⁏ Q = Q := by
  rintro ⟨hS, hQ⟩
  have e : S˘ ⨾ S = I ↾ codom S := by
    rw [mem_arrow_Cls_one] at hS
    refine rel_ext' fun z w => ⟨fun ⟨x, h1, h2⟩ => ⟨hS x z w ⟨h1, h2⟩, x, h2⟩, ?_⟩
    rintro ⟨rfl, x, hx⟩
    exact ⟨x, hx, hx⟩
  rw [pm150_13, pm150_14, e]
  exact pm150_91 hQ

/-- ✱150·921. \(\vdash : S \in 1 \rightarrow \text{Cls} . sʻCʻʻCʻP \subset \text{D}ʻS . \supset . S\dagger ^{;} \breve{S} \dagger ^{;}P = P\) -/
theorem pm150_921 {S : α → β → Prop} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    S ∈ arrow one Cls ∧ sumCls (C ʻʻ fld P) ⊆ dom S → daggerRel S ⁏ daggerRel S˘ ⁏ P = P := by
  rintro ⟨hS, hP⟩
  refine pm150_92 (S := S˘) ⟨?_, hP⟩
  rw [mem_arrow_Cls_one]
  exact fun x y z h => (mem_arrow_one_Cls.1 hS) y z x h

/-- ✱150·93. \[\begin{align}]\vdash \colon\ldotp S \in 1 \rightarrow 1 . sʻCʻʻCʻP \subset &\text{D}ʻS . sʻCʻʻCʻQ \subset \text{ᗡ}ʻS . \supset :\\ &P = S\dagger ^{;}Q . \equiv . Q = \breve{S} \dagger ^{;}P \quad[*150·92·921]\end{align}\]

(The e-text prints a stray `]` at the start.) -/
theorem pm150_93 {S : α → β → Prop} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    (S ∈ arrow one one ∧ sumCls (C ʻʻ fld P) ⊆ dom S) ∧ sumCls (C ʻʻ fld Q) ⊆ codom S →
      (P = daggerRel S ⁏ Q ↔ Q = daggerRel S˘ ⁏ P) := by
  rintro ⟨⟨hS, hP⟩, hQ⟩
  have h1 : S ∈ arrow Cls one := mem_arrow_Cls_one.2 (mem_arrow_one_one.1 hS).2
  have h2 : S ∈ arrow one Cls := mem_arrow_one_Cls.2 (mem_arrow_one_one.1 hS).1
  constructor
  · rintro rfl; exact (pm150_92 ⟨h1, hQ⟩).symm
  · rintro rfl; exact (pm150_921 ⟨h2, hP⟩).symm

/-- ✱150·931. \(\vdash : sʻCʻʻCʻQ \subset \text{ᗡ}ʻS . \supset . CʻʻCʻS\dagger ^{;}Q = S_{\in}ʻʻCʻʻCʻQ\)

`C''C'S†;Q` is `C ʻʻ fld (daggerRel S ⁏ Q)`; `S_∈` is `imgRel S`. -/
theorem pm150_931 {S : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    sumCls (C ʻʻ fld Q) ⊆ codom S → C ʻʻ fld (daggerRel S ⁏ Q) = imgRel S ʻʻ C ʻʻ fld Q := by
  intro hQ
  have h1 : fld (daggerRel S ⁏ Q) = daggerRel S ʻʻ fld Q := fld_semi_graph _ _
  rw [h1]
  ext A
  constructor
  · rintro ⟨M, ⟨N, hN, rfl⟩, rfl⟩
    refine ⟨fld N, ⟨N, hN, rfl⟩, ?_⟩
    show fld (S ⁏ N) = S ʻʻ fld N
    exact pm150_22 fun z hz => hQ ⟨fld N, ⟨N, hN, rfl⟩, hz⟩
  · rintro ⟨B, ⟨N, hN, rfl⟩, rfl⟩
    refine ⟨S ⁏ N, ⟨N, hN, rfl⟩, ?_⟩
    show S ʻʻ fld N = fld (S ⁏ N)
    exact (pm150_22 fun z hz => hQ ⟨fld N, ⟨N, hN, rfl⟩, hz⟩).symm

/-- ✱150·932. \[\begin{align}&\vdash :sʻCʻʻCʻQ\subset \text{ᗡ}ʻS.\supset .sʻCʻʻCʻS{\dagger}^{;}Q = SʻʻsʻCʻʻCʻQ\\ &[*150·931.*37·11.*40·38]\end{align}\] -/
theorem pm150_932 {S : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    sumCls (C ʻʻ fld Q) ⊆ codom S →
      sumCls (C ʻʻ fld (daggerRel S ⁏ Q)) = S ʻʻ sumCls (C ʻʻ fld Q) := by
  intro hQ
  rw [pm150_931 hQ]
  ext x
  constructor
  · rintro ⟨A, ⟨B, hB, rfl⟩, ⟨y, hy, hxy⟩⟩
    exact ⟨y, ⟨B, hB, hy⟩, hxy⟩
  · rintro ⟨y, ⟨B, hB, hy⟩, hxy⟩
    exact ⟨S ʻʻ B, ⟨B, hB, rfl⟩, ⟨y, hy, hxy⟩⟩

/-- ✱150·933. \(\vdash :sʻCʻʻCʻQ\subset \text{ᗡ}ʻS.\supset .sʻCʻʻCʻ{\dagger}^{;}Q\subset \text{D}ʻS \quad[*150·932.*37·15]\)

**Status.** proved (reading): transcription error: the e-text prints `s'C''C'†;Q` for
`s'C''C'S†;Q` (PM cites ✱150·932, whose left-hand side this is). -/
theorem pm150_933 {S : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    sumCls (C ʻʻ fld Q) ⊆ codom S → sumCls (C ʻʻ fld (daggerRel S ⁏ Q)) ⊆ dom S := by
  intro hQ
  rw [pm150_932 hQ]
  rintro x ⟨y, -, hxy⟩
  exact ⟨y, hxy⟩

/-- ✱150·94. \[\begin{align}\vdash \colon\ldotp S\in 1\rightarrow 1.&\supset :sʻCʻʻCʻQ\subset \text{ᗡ}ʻS.P = S{\dagger}^{;}Q. \equiv .\\ &sʻCʻʻCʻP\subset \text{D}ʻS.Q = \breve{S} \dagger ^{;}P\end{align}\] -/
theorem pm150_94 {S : α → β → Prop} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    S ∈ arrow one one →
      (sumCls (C ʻʻ fld Q) ⊆ codom S ∧ P = daggerRel S ⁏ Q ↔
        sumCls (C ʻʻ fld P) ⊆ dom S ∧ Q = daggerRel S˘ ⁏ P) := by
  intro hS
  constructor
  · rintro ⟨hQ, rfl⟩
    have hP := pm150_933 hQ
    exact ⟨hP, (pm150_93 ⟨⟨hS, hP⟩, hQ⟩).1 rfl⟩
  · rintro ⟨hP, rfl⟩
    have hS' : S˘ ∈ arrow one one :=
      mem_arrow_one_one.2 ⟨fun x y z h => (mem_arrow_one_one.1 hS).2 z x y h,
        fun x y z h => (mem_arrow_one_one.1 hS).1 y z x h⟩
    have hQ : sumCls (C ʻʻ fld (daggerRel S˘ ⁏ P)) ⊆ codom S := pm150_933 (S := S˘) hP
    exact ⟨hQ, (pm150_93 ⟨⟨hS, hP⟩, hQ⟩).2 rfl⟩

/-- ✱150·95. \(\vdash :CʻR\subset \text{Cl}ʻ\alpha .\supset .(S\upharpoonright \alpha )_{\in }^{;}R = S^{;}R\)

`(S ↾ α)_∈` is `imgRel (S ↾ A)`, `C'R ⊂ Cl'α` is `fld R ⊆ cl A`.

**Status.** proved (reading): transcription error: the e-text prints `S;R` for `S_∈;R` on the
right (`R` is a relation of classes, so `S;R` is not significant; PM's proof, by ✱37·11 and
✱150·35, gives `S_∈;R`). -/
theorem pm150_95 {S : α → β → Prop} {A : Set β} {R : Set β → Set β → Prop} :
    fld R ⊆ cl A → imgRel (S ↾ A) ⁏ R = imgRel S ⁏ R := by
  intro h
  refine rel_ext' fun X Y => ?_
  rw [show imgRel (S ↾ A) = graph (img (S ↾ A)) from rfl, show imgRel S = graph (img S) from rfl,
    semi_graph_apply, semi_graph_apply]
  have key : ∀ B, B ∈ fld R → (S ↾ A) ʻʻ B = S ʻʻ B := fun B hB => by
    have hBA : B ⊆ A := h hB
    ext x
    exact ⟨fun ⟨y, hy, hxy, _⟩ => ⟨y, hy, hxy⟩, fun ⟨y, hy, hxy⟩ => ⟨y, hy, hxy, hBA hy⟩⟩
  constructor
  · rintro ⟨B, B', ⟨rfl, rfl⟩, hBB⟩
    exact ⟨B, B', ⟨key B ⟨B', Or.inl hBB⟩, key B' ⟨B, Or.inr hBB⟩⟩, hBB⟩
  · rintro ⟨B, B', ⟨rfl, rfl⟩, hBB⟩
    exact ⟨B, B', ⟨(key B ⟨B', Or.inl hBB⟩).symm, (key B' ⟨B, Or.inr hBB⟩).symm⟩, hBB⟩

/-- ✱150·96. \(\vdash :\text{ᗡ}ʻ\dot{s} ʻ\lambda \subset \text{ᗡ}ʻS.\supset .\text{D}^{;}(T\parallel \breve{S} \upharpoonright \lambda =T_{\in }\upharpoonright \text{D}ʻʻ\lambda \)

`T`, `S` are homogeneous, since `D;(T ‖ S̆)↾λ` must be significant; `ᗡ'ṡ'λ` is
`codom (sumRel L)`, `T_∈ ↾ D''λ` is `imgRel T ↾ D ʻʻ L`.

**Status.** proved (reading): transcription error: the e-text omits the closing bracket of
`D;(T ‖ S̆)↾λ`, which PM's demonstration shows to be `D;{(T ‖ S̆)↾λ}`. -/
theorem pm150_96 {T : α → α → Prop} {S : γ → γ → Prop} {L : Set (α → γ → Prop)} :
    codom (sumRel L) ⊆ codom S → D ⁏ ((T ∥ S˘) ↾ L) = imgRel T ↾ D ʻʻ L := by
  intro hL
  have hdom : ∀ N, N ∈ L → dom (T ⨾ (N ⨾ S˘)) = T ʻʻ dom N := by
    intro N hN
    ext x
    constructor
    · rintro ⟨y, a, hxa, b, hab, _⟩
      exact ⟨a, ⟨b, hab⟩, hxa⟩
    · rintro ⟨a, ⟨b, hab⟩, hxa⟩
      obtain ⟨y, hyb⟩ := hL ⟨a, N, hN, hab⟩
      exact ⟨y, a, hxa, b, hab, hyb⟩
  refine rel_ext' fun X Y => ?_
  rw [show (D : Set α → (α → γ → Prop) → Prop) = graph dom from rfl, semi_graph_apply]
  constructor
  · rintro ⟨M, N, ⟨rfl, rfl⟩, hMN, hN⟩
    rw [dpar_iff] at hMN
    subst hMN
    exact ⟨hdom N hN, N, hN, rfl⟩
  · rintro ⟨hXY, N, hN, hYN⟩
    refine ⟨T ⨾ (N ⨾ S˘), N, ⟨?_, hYN⟩, (dpar_iff _ _ _ _).2 rfl, hN⟩
    rw [hdom N hN, ← (hYN : Y = dom N)]
    exact hXY

/-- ✱150·961. \(\vdash .\dot{s} ^{;}(U\parallel \breve{W} )_{\in }\upharpoonright \lambda =(U\parallel \breve{W} )\upharpoonright \dot{s}ʻʻ\lambda \)

`U`, `W` are homogeneous (`ṡ;(U ‖ W̆)_∈↾λ` must be significant); `ṡ` is `sDotRel`. -/
theorem pm150_961 {U : α → α → Prop} {W : γ → γ → Prop} {L : Set (Set (α → γ → Prop))} :
    sDotRel ⁏ (imgRel (U ∥ W˘) ↾ L) = (U ∥ W˘) ↾ sDotRel ʻʻ L := by
  have key : ∀ K : Set (α → γ → Prop), sumRel ((U ∥ W˘) ʻʻ K) = U ⨾ (sumRel K ⨾ W˘) := by
    intro K
    refine rel_ext' fun x y => ?_
    constructor
    · rintro ⟨M, ⟨N, hN, hMN⟩, hM⟩
      rw [dpar_iff] at hMN
      subst hMN
      obtain ⟨a, h1, b, h2, h3⟩ := hM
      exact ⟨a, h1, b, ⟨N, hN, h2⟩, h3⟩
    · rintro ⟨a, h1, b, ⟨N, hN, h2⟩, h3⟩
      exact ⟨U ⨾ (N ⨾ W˘), ⟨N, hN, (dpar_iff _ _ _ _).2 rfl⟩, a, h1, b, h2, h3⟩
  refine rel_ext' fun R R' => ?_
  rw [show (sDotRel : (α → γ → Prop) → Set (α → γ → Prop) → Prop) = graph sumRel from rfl,
    semi_graph_apply]
  constructor
  · rintro ⟨K, K', ⟨rfl, rfl⟩, hKK, hK'⟩
    obtain rfl : K = (U ∥ W˘) ʻʻ K' := hKK
    rw [key]
    exact ⟨(dpar_iff _ _ _ _).2 rfl, K', hK', rfl⟩
  · rintro ⟨hR, K', hK', hR'⟩
    rw [dpar_iff] at hR
    refine ⟨(U ∥ W˘) ʻʻ K', K', ⟨?_, hR'⟩, rfl, hK'⟩
    rw [key, hR, ← (hR' : R' = sumRel K')]

/-!
## [✱151] Ordinal similarity

*(Vol. 2, p. 319)*

> *Summary of* *151.
>
> In this number, we give the definition of ordinal similarity, and various equivalent forms; we prove that ordinal similarity is reflexive (*151·13), symmetrical (*151·14) and transitive (*151·15), and we give some particular cases of ordinal similarity (*151·6 ff.). Propositions in this number should be compared with those in *73, to which they are analogous.
>
> The class of ordinal correlators of \(P\) and \(Q\) is written \(P\,\overline{\text{smor}}\,Q\), where "\(\text{smor}\)" stands for "similar ordinally." We put \[ P\,\overline{\text{smor}}\,Q=\hat{S}\{S\in 1\rightarrow 1.CʻQ=\text{ᗡ}ʻS.P=S^{;}Q\} \quad\text{Df}. \]
>
> (We might equally well put \[ P\,\overline{\text{smor}}\,Q=(1\rightarrow 1)\cap \overleftarrow{\text{ᗡ}}ʻCʻQ\cap \dagger \overleftarrow{Q}ʻP \quad\text{Df}, \] which is an equivalent but more condensed form of the definition.) We then define "\(P\) is ordinally similar to \(Q\)" as meaning that there is at least one ordinal correlator of \(P\) and \(Q\), *i.e.* \[ \text{smor}=\hat{P} \hat{Q} (\exists !P\,\overline{\text{smor}}\,Q) \quad\text{Df}. \]
>
> …

**Lean reading.** `P smor̄ Q` is `smorbar P Q`, `P smor Q` is `smor P Q`; `P` and `Q` are
homogeneous relations of
possibly different types `α`, `β`, the correlators `S : α → β → Prop`. `S'y`, `S̆'x` are
descriptions (`Desc`), `S'y = S'z` and `(S'z)P(S'w)` have the first description with the larger
scope, `(y) . E!S'y` is `∀ y, EDesc S y`. `P_po` is `po P`, `Pot'Q` is `pot Q`, `P(x⊢⊣y)` is
`itvCC P x y`, `P_ν` is `Pnu P ν` (the cardinal `ν` of any type), `B⃗'P` is `refs Beg P`, `Rl'Q` is
`rl Q`, `C'P ↿ S` is `fld P ◁ S`, `α sm̄ β` is `smbar A B`. Where `smor` must be homogeneous to be
significant (✱151·16·161·162) it is taken on one type. ✱151·264 needs the hypothesis
`C'Q ⊂ ᗡ'S`, which PM's proof assumes.

**Status.** proved (all propositions; ✱151·01·02 definition; ✱151·131 proved (reading):
transcription
error; ✱151·264 proved (corrected): the hypothesis `C'Q ⊂ ᗡ'S` is added, the printed form is
refuted by `pm151_264_printed_false`)
-/

/-- ✱151·01 (Df). \(P\,\overline{\text{smor}}\,Q=\hat{S}\{S\in 1\rightarrow 1.CʻQ=\text{ᗡ}ʻS.P=S^{;}Q\} \quad\text{Df}\) -/
theorem pm151_01 {P : α → α → Prop} {Q : β → β → Prop} :
    smorbar P Q = {S | (S ∈ arrow one one ∧ fld Q = codom S) ∧ P = S ⁏ Q} := rfl

/-- ✱151·02 (Df). \(\text{smor}=\hat{P} \hat{Q}\{\exists !P\,\overline{\text{smor}}\,Q\} \quad\text{Df}\) -/
theorem pm151_02 :
    (smor : (α → α → Prop) → (β → β → Prop) → Prop) = fun P Q => (smorbar P Q).Nonempty := rfl

/-- ✱151·1. \(\vdash :P\,\text{smor}\,Q.\equiv .(\exists S).S\in 1\rightarrow 1.CʻQ=\text{ᗡ}ʻS.P=S^{;}Q \quad[(*151·02)]\) -/
theorem pm151_1 {P : α → α → Prop} {Q : β → β → Prop} :
    smor P Q ↔ ∃ S : α → β → Prop, (S ∈ arrow one one ∧ fld Q = codom S) ∧ P = S ⁏ Q :=
  smor_iff

/-- ✱151·11. \(\vdash :S\in P\,\overline{\text{smor}}\,Q.\equiv .S\in 1\rightarrow 1.CʻQ=\text{ᗡ}ʻS.P=S^{;}Q \quad[(*151·01)]\) -/
theorem pm151_11 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    S ∈ smorbar P Q ↔ (S ∈ arrow one one ∧ fld Q = codom S) ∧ P = S ⁏ Q := Iff.rfl

/-- ✱151·12. \(\vdash :P\,\text{smor}\,Q.\equiv .\exists !P\,\overline{\text{smor}}\,Q \quad[(*151·02)]\) -/
theorem pm151_12 {P : α → α → Prop} {Q : β → β → Prop} : smor P Q ↔ (smorbar P Q).Nonempty :=
  Iff.rfl

/-- ✱151·121. \(\vdash .I\upharpoonright CʻQ\in (Q\overline{\text{smor}} Q)\quad[*72·17.*50·5·52.*150·534.*151·11]\) -/
theorem pm151_121 {Q : α → α → Prop} : (I : α → α → Prop) ↾ fld Q ∈ smorbar Q Q := by
  refine ⟨⟨?_, ?_⟩, pm150_534.symm⟩
  · rsimp
    grind
  · rsimp
    grind

/-- ✱151·13. \(\vdash .Q\text{smor}Q \quad[*151·121·12]\) -/
theorem pm151_13 {Q : α → α → Prop} : smor Q Q := ⟨_, pm151_121⟩

/-- ✱151·131. \(\vdash :S\in P\,\overline{\text{smor}}\,Q.=.\breve{S} \in Q\,\overline{\text{smor}}\,P\)

**Status.** proved (reading): transcription error: the e-text prints `.=.` for `.≡.` between the
two propositions. -/
theorem pm151_131 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    S ∈ smorbar P Q ↔ S˘ ∈ smorbar Q P :=
  ⟨smorbar_cnv, fun h => smorbar_cnv h⟩

/-- ✱151·14. \(\vdash :P\,\text{smor}\,Q.\equiv .Q\,\text{smor}\,P \quad[*151·131·12.*31·52]\) -/
theorem pm151_14 {P : α → α → Prop} {Q : β → β → Prop} : smor P Q ↔ smor Q P :=
  ⟨smor_symm, smor_symm⟩

/-- ✱151·141. \(\vdash :S\in P\,\overline{\text{smor}}\,Q.T\in Q\,\overline{\text{smor}}\,R.\supset .S\mid T\in P\,\overline{\text{smor}}\,R\) -/
theorem pm151_141 {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop} {S : α → β → Prop}
    {T : β → γ → Prop} : S ∈ smorbar P Q ∧ T ∈ smorbar Q R → S ⨾ T ∈ smorbar P R := by
  rintro ⟨⟨⟨hS, hQ⟩, hP⟩, ⟨⟨hT, hR⟩, hQ'⟩⟩
  have hdT : dom T = fld Q := by rw [hQ', pm150_23 hR]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_arrow_one_one] at hS hT ⊢
    obtain ⟨hS1, hS2⟩ := hS
    obtain ⟨hT1, hT2⟩ := hT
    constructor
    · rintro x y z ⟨⟨a, hxa, haz⟩, ⟨b, hyb, hbz⟩⟩
      obtain rfl := hT1 a b z ⟨haz, hbz⟩
      exact hS1 x y a ⟨hxa, hyb⟩
    · rintro x y z ⟨⟨a, hxa, hay⟩, ⟨b, hxb, hbz⟩⟩
      obtain rfl := hS2 x a b ⟨hxa, hxb⟩
      exact hT2 a y z ⟨hay, hbz⟩
  · rw [hR]
    ext z
    constructor
    · rintro ⟨y, hyz⟩
      have : y ∈ codom S := by rw [← hQ, ← hdT]; exact ⟨z, hyz⟩
      obtain ⟨x, hxy⟩ := this
      exact ⟨x, y, hxy, hyz⟩
    · rintro ⟨x, y, -, hyz⟩
      exact ⟨y, hyz⟩
  · rw [hP, hQ', semi_semi]

/-- ✱151·15. \(\vdash :P\,\text{smor}\,Q.Q\,\text{smor}\,R.\supset .P\,\text{smor}\,R \quad[*151·141]\) -/
theorem pm151_15 {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop} :
    smor P Q ∧ smor Q R → smor P R :=
  fun ⟨h1, h2⟩ => smor_trans h1 h2

/-- ✱151·16. \(\vdash .I\,\unicode{x2abd}\, \text{smor} \quad[*151·13]\)

`smor` is here a homogeneous relation (that `I ⊂̇ smor` be significant). -/
theorem pm151_16 : (I : (α → α → Prop) → (α → α → Prop) → Prop) ⪽ smor := by
  intro P Q h
  rw [show P = Q from h]
  exact smor_refl Q

/-- ✱151·161. \(\vdash .\text{smor}=\text{Cnv}ʻ\text{smor} \quad[*151·14]\)

`Cnv'smor` is `smor˘`; `smor` is homogeneous here. -/
theorem pm151_161 : (smor : (α → α → Prop) → (α → α → Prop) → Prop) = smor˘ :=
  rel_ext' fun _ _ => ⟨smor_symm, smor_symm⟩

/-- ✱151·162. \(\vdash .(\text{smor})^{2}=\text{smor} \quad[*151·15·161.*34·81]\) -/
theorem pm151_162 : rsq (smor : (α → α → Prop) → (α → α → Prop) → Prop) = smor :=
  rel_ext' fun P _ => ⟨fun ⟨_, h1, h2⟩ => smor_trans h1 h2, fun h => ⟨P, smor_refl P, h⟩⟩

/-- ✱151·17. \(\vdash \colon\ldotp P\,\text{smor}\,Q.\supset :R\,\text{smor}\,P.\equiv .R\,\text{smor}\,Q \quad[*151·14·15]\) -/
theorem pm151_17 {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop} :
    smor P Q → (smor R P ↔ smor R Q) :=
  fun h => ⟨fun h' => smor_trans h' h, fun h' => smor_trans h' (smor_symm h)⟩

/-- ✱151·18. \(\vdash:P\,\text{smor}\,Q.\supset .CʻP\text{ sm }CʻQ\) -/
theorem pm151_18 {P : α → α → Prop} {Q : β → β → Prop} : smor P Q → sm (fld P) (fld Q) :=
  sm_fld_of_smor

/-- ✱151·19. \(\vdash :CʻP\text{ sm }CʻQ.\equiv .(\exists R).CʻR=CʻP.R\,\text{smor}\,Q\)

`C'R = C'P` puts `R` in the type of `P`. -/
theorem pm151_19 {P : α → α → Prop} {Q : β → β → Prop} :
    sm (fld P) (fld Q) ↔ ∃ R : α → α → Prop, fld R = fld P ∧ smor R Q := by
  constructor
  · intro h
    obtain ⟨S, ⟨hS, hdom⟩, hcod⟩ := sm_iff.1 h
    exact ⟨S ⁏ Q, (pm150_23 hcod).trans hdom.symm, ⟨S, ⟨hS, hcod⟩, rfl⟩⟩
  · rintro ⟨R, hR, h⟩
    rw [← hR]
    exact sm_fld_of_smor h

/-- ✱151·191. \(\vdash :S\in P\,\overline{\text{smor}}\,Q.\equiv .S\in (CʻP)\,\overline{\text{ sm }}\, (CʻQ).P=S^{;}Q\)

`S ∈ (C'P) sm̄ (C'Q)` is `S ∈ smbar (fld P) (fld Q)` (✱73·01). -/
theorem pm151_191 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    S ∈ smorbar P Q ↔ S ∈ smbar (fld P) (fld Q) ∧ P = S ⁏ Q := by
  constructor
  · rintro ⟨⟨hS, hQ⟩, rfl⟩
    exact ⟨⟨⟨hS, pm150_23 hQ⟩, hQ⟩, rfl⟩
  · rintro ⟨⟨⟨hS, -⟩, hQ⟩, hP⟩
    exact ⟨⟨hS, hQ⟩, hP⟩

/-- ✱151·2. \(\vdash :S\in 1\rightarrow 1.CʻQ\subset \text{ᗡ}ʻS.P=S^{;}Q.\supset .S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q\) -/
theorem pm151_2 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    (S ∈ arrow one one ∧ fld Q ⊆ codom S) ∧ P = S ⁏ Q → S ↾ fld Q ∈ smorbar P Q := by
  rintro ⟨⟨hS, hQ⟩, rfl⟩
  exact ⟨⟨cres_one_one hS, codom_cres_iff.2 hQ⟩, pm150_32.symm⟩

/-- ✱151·21. \(\vdash :P\,\text{smor}\,Q.\equiv .(\exists S).S\in 1\rightarrow 1.CʻQ\subset \text{ᗡ}ʻS.P=S^{;}Q \quad[*151·2]\) -/
theorem pm151_21 {P : α → α → Prop} {Q : β → β → Prop} :
    smor P Q ↔ ∃ S : α → β → Prop, (S ∈ arrow one one ∧ fld Q ⊆ codom S) ∧ P = S ⁏ Q := by
  constructor
  · rintro ⟨S, ⟨hS, hQ⟩, hP⟩
    exact ⟨S, ⟨hS, hQ.le⟩, hP⟩
  · rintro ⟨S, h⟩
    exact ⟨_, pm151_2 h⟩

/-- ✱151·22. \(\vdash :S\upharpoonright CʻQ\in 1\rightarrow 1.CʻQ\subset \text{ᗡ}ʻS.P=S^{;}Q.\equiv .S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q\) -/
theorem pm151_22 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    (S ↾ fld Q ∈ arrow one one ∧ fld Q ⊆ codom S) ∧ P = S ⁏ Q ↔ S ↾ fld Q ∈ smorbar P Q := by
  constructor
  · rintro ⟨⟨h1, h2⟩, rfl⟩
    exact ⟨⟨h1, codom_cres_iff.2 h2⟩, pm150_32.symm⟩
  · rintro ⟨⟨h1, h2⟩, hP⟩
    exact ⟨⟨h1, codom_cres_iff.1 h2⟩, hP.trans pm150_32⟩

/-- ✱151·23. \(\vdash :P\,\text{smor}\,Q.\equiv .(\exists S).S\upharpoonright CʻQ\in 1\rightarrow 1.CʻQ\subset \text{ᗡ}ʻS.P=S^{;}Q \quad[*151·22]\) -/
theorem pm151_23 {P : α → α → Prop} {Q : β → β → Prop} :
    smor P Q ↔
      ∃ S : α → β → Prop, (S ↾ fld Q ∈ arrow one one ∧ fld Q ⊆ codom S) ∧ P = S ⁏ Q := by
  constructor
  · rintro ⟨S, ⟨hS, hQ⟩, hP⟩
    exact ⟨S, ⟨cres_one_one hS, hQ.le⟩, hP⟩
  · rintro ⟨S, h⟩
    exact ⟨_, pm151_22.1 h⟩

/-- ✱151·231. \[\begin{align}&\vdash \colon\ldotp (y).\text{E}!Sʻy:S\upharpoonright CʻQ\in 1\rightarrow 1.P=S^{;}Q:\supset .S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q\\ &[*151·22.*33·431]\end{align}\]

`(y) . E!S'y` is `∀ y, EDesc S y`. -/
theorem pm151_231 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    (∀ y, EDesc S y) ∧ (S ↾ fld Q ∈ arrow one one ∧ P = S ⁏ Q) → S ↾ fld Q ∈ smorbar P Q := by
  rintro ⟨hE, h1, hP⟩
  refine pm151_22.1 ⟨⟨h1, fun y _ => ?_⟩, hP⟩
  obtain ⟨b, hb⟩ := hE y
  exact ⟨b, (hb b).2 rfl⟩

/-- ✱151·232. \[\begin{align}&\vdash \colon\ldotp (\exists S):(y).\text{E}!Sʻy:S\upharpoonright CʻQ\in 1\rightarrow 1.P=S^{;}Q:\supset .P\,\text{smor}\,Q\\ &[*151·231·12]\end{align}\] -/
theorem pm151_232 {P : α → α → Prop} {Q : β → β → Prop} :
    (∃ S : α → β → Prop, (∀ y, EDesc S y) ∧ (S ↾ fld Q ∈ arrow one one ∧ P = S ⁏ Q)) →
      smor P Q :=
  fun ⟨_, h⟩ => ⟨_, pm151_231 h⟩

/-- ✱151·24. \[\begin{align}\vdash \colon\ldotp &(y).\text{E}!Sʻy:y,z\in CʻQ.Sʻy=Sʻz.\supset _{y,z}.y=z:P=S^{;}Q:\supset .\\ &S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q.P\,\text{smor}\,Q \quad[*71·166·55.*33·431.*151·22·23]\end{align}\]

`S'y = S'z` is `Desc S y (fun a => Desc S z (fun b => a = b))`; the hypothesis is the
product of three, bracketed to the left. -/
theorem pm151_24 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    ((∀ y, EDesc S y) ∧ (∀ y z, (y ∈ fld Q ∧ z ∈ fld Q) ∧
      Desc S y (fun a => Desc S z (fun b => a = b)) → y = z)) ∧ P = S ⁏ Q →
        S ↾ fld Q ∈ smorbar P Q ∧ smor P Q := by
  rintro ⟨⟨hE, hinj⟩, hP⟩
  choose f hf using hE
  have hf' : ∀ y u, S u y ↔ u = f y := hf
  have h1 : S ↾ fld Q ∈ arrow one one := by
    refine mem_arrow_one_one.2 ⟨?_, ?_⟩
    · rintro x y z ⟨⟨hx, -⟩, ⟨hy, -⟩⟩
      exact ((hf' z x).1 hx).trans ((hf' z y).1 hy).symm
    · rintro x y z ⟨⟨hy, hyQ⟩, ⟨hz, hzQ⟩⟩
      refine hinj y z ⟨⟨hyQ, hzQ⟩, (desc_eq_iff' (hf' y) (hf' z)).2 ?_⟩
      exact ((hf' y x).1 hy).symm.trans ((hf' z x).1 hz)
  have h := pm151_231 ⟨fun y => ⟨f y, hf' y⟩, h1, hP⟩
  exact ⟨h, ⟨_, h⟩⟩

/-- ✱151·241. \[\begin{align}\vdash \colon\ldotp S\in 1\rightarrow \text{Cls}.&CʻQ\subset \text{ᗡ}ʻS:y,z\in CʻQ.Sʻy=Sʻz.\supset _{y,z}.y=z:P=S^{;}Q:\supset .\\ &S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q.P\,\text{smor}\,Q \quad[*71·55.*151·22·23]\end{align}\] -/
theorem pm151_241 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    ((S ∈ arrow one Cls ∧ fld Q ⊆ codom S) ∧ (∀ y z, (y ∈ fld Q ∧ z ∈ fld Q) ∧
      Desc S y (fun a => Desc S z (fun b => a = b)) → y = z)) ∧ P = S ⁏ Q →
        S ↾ fld Q ∈ smorbar P Q ∧ smor P Q := by
  rintro ⟨⟨⟨hS, hQ⟩, hinj⟩, hP⟩
  rw [mem_arrow_one_Cls] at hS
  have hu : ∀ y, y ∈ fld Q → ∃ b, ∀ u, S u y ↔ u = b := fun y hy => by
    obtain ⟨b, hb⟩ := hQ hy
    exact ⟨b, fun u => ⟨fun hu => hS u b y ⟨hu, hb⟩, fun e => e ▸ hb⟩⟩
  have h1 : S ↾ fld Q ∈ arrow one one := by
    refine mem_arrow_one_one.2 ⟨fun x y z ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => hS x y z ⟨hx, hy⟩, ?_⟩
    rintro x y z ⟨⟨hy, hyQ⟩, ⟨hz, hzQ⟩⟩
    obtain ⟨b, hb⟩ := hu y hyQ
    obtain ⟨c, hc⟩ := hu z hzQ
    refine hinj y z ⟨⟨hyQ, hzQ⟩, (desc_eq_iff' hb hc).2 ?_⟩
    exact ((hb x).1 hy).symm.trans ((hc x).1 hz)
  have h := pm151_22.1 ⟨⟨h1, hQ⟩, hP⟩
  exact ⟨h, ⟨_, h⟩⟩

/-- ✱151·242. \[\begin{align}&\vdash \colon\colon y,z\in CʻQ.\supset _{y,z}:Sʻy=Sʻz.\equiv .y=z\colon\ldotp P=S^{;}Q\colon\ldotp \equiv .S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q\\ &[*71·59.*151·22]\end{align}\] -/
theorem pm151_242 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    (∀ y z, (y ∈ fld Q ∧ z ∈ fld Q) →
      (Desc S y (fun a => Desc S z (fun b => a = b)) ↔ y = z)) ∧ P = S ⁏ Q ↔
        S ↾ fld Q ∈ smorbar P Q := by
  constructor
  · rintro ⟨h, hP⟩
    have hu : ∀ y, y ∈ fld Q → ∃ b, ∀ u, S u y ↔ u = b := fun y hy => by
      obtain ⟨b, hb, -⟩ := (h y y ⟨hy, hy⟩).2 rfl
      exact ⟨b, hb⟩
    have hQ : fld Q ⊆ codom S := fun y hy => by
      obtain ⟨b, hb⟩ := hu y hy
      exact ⟨b, (hb b).2 rfl⟩
    have h1 : S ↾ fld Q ∈ arrow one one := by
      refine mem_arrow_one_one.2 ⟨?_, ?_⟩
      · rintro x y z ⟨⟨hx, hzQ⟩, ⟨hy, -⟩⟩
        obtain ⟨b, hb⟩ := hu z hzQ
        exact ((hb x).1 hx).trans ((hb y).1 hy).symm
      · rintro x y z ⟨⟨hy, hyQ⟩, ⟨hz, hzQ⟩⟩
        obtain ⟨b, hb⟩ := hu y hyQ
        obtain ⟨c, hc⟩ := hu z hzQ
        refine (h y z ⟨hyQ, hzQ⟩).1 ((desc_eq_iff' hb hc).2 ?_)
        exact ((hb x).1 hy).symm.trans ((hc x).1 hz)
    exact pm151_22.1 ⟨⟨h1, hQ⟩, hP⟩
  · intro hS
    obtain ⟨⟨h1, hQ⟩, hP⟩ := pm151_22.2 hS
    refine ⟨fun y z ⟨hy, hz⟩ => ?_, hP⟩
    obtain ⟨b, hb⟩ := uniq_of_cres hQ h1 hy
    obtain ⟨c, hc⟩ := uniq_of_cres hQ h1 hz
    rw [desc_eq_iff' hb hc]
    constructor
    · rintro rfl
      exact (mem_arrow_one_one.1 h1).2 b y z ⟨⟨(hb b).2 rfl, hy⟩, ⟨(hc b).2 rfl, hz⟩⟩
    · rintro rfl
      exact (hc b).1 ((hb b).2 rfl)

/-- ✱151·243. \[\begin{align}&\vdash \colon\colon y,z\in CʻQ.\supset _{y,z}:Sʻy=Sʻz.\equiv .y=z\colon\ldotp P=S^{;}Q\colon\ldotp \supset .P\,\text{smor}\,Q\\ &[*151·242·12]\end{align}\] -/
theorem pm151_243 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    (∀ y z, (y ∈ fld Q ∧ z ∈ fld Q) →
      (Desc S y (fun a => Desc S z (fun b => a = b)) ↔ y = z)) ∧ P = S ⁏ Q → smor P Q :=
  fun h => ⟨_, pm151_242.1 h⟩

/-- ✱151·25. \(\vdash :S\in \text{Cls}\rightarrow 1.CʻQ\subset \text{ᗡ}ʻS.P=S^{;}Q.\supset .Q=\breve{S} ^{;}P\) -/
theorem pm151_25 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    (S ∈ arrow Cls one ∧ fld Q ⊆ codom S) ∧ P = S ⁏ Q → Q = S˘ ⁏ P := by
  rintro ⟨⟨hS, hQ⟩, rfl⟩
  exact (cnv_semi_semi hS hQ).symm

/-- ✱151·251. \[\begin{align}&\vdash \colon\ldotp S\in 1\rightarrow 1.\supset :CʻQ\subset \text{ᗡ}ʻS.P=S^{;}Q.\equiv .CʻP\subset \text{D}ʻS.Q=\breve{S} ^{;}P\\ &[*151·25.*150·22.*37·15]\end{align}\] -/
theorem pm151_251 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    S ∈ arrow one one → (fld Q ⊆ codom S ∧ P = S ⁏ Q ↔ fld P ⊆ dom S ∧ Q = S˘ ⁏ P) := by
  intro hS
  constructor
  · rintro ⟨hQ, rfl⟩
    exact ⟨pm150_203, (cnv_semi_semi (arrow_Cls_one_of hS) hQ).symm⟩
  · rintro ⟨hP, rfl⟩
    exact ⟨pm150_203,
      (cnv_semi_semi (S := S˘) (cnv_mem_arrow_Cls_one (arrow_one_Cls_of hS)) hP).symm⟩

/-- ✱151·252. \(\vdash :S\in \text{Cls}\rightarrow 1.CʻQ\subset \text{ᗡ}ʻS.\supset .Q=\breve{S} ^{;}S^{;}Q \quad[*151·25]\) -/
theorem pm151_252 {Q : β → β → Prop} {S : α → β → Prop} :
    S ∈ arrow Cls one ∧ fld Q ⊆ codom S → Q = S˘ ⁏ S ⁏ Q :=
  fun ⟨hS, hQ⟩ => (cnv_semi_semi hS hQ).symm

/-- ✱151·253. \(\vdash :S\in 1\rightarrow \text{Cls}.CʻP\subset \text{D}ʻS.\supset .P=S^{;}\breve{S} ^{;}P \quad\left[*151·252\frac{\breve{S}}{S}\right]\) -/
theorem pm151_253 {P : α → α → Prop} {S : α → β → Prop} :
    S ∈ arrow one Cls ∧ fld P ⊆ dom S → P = S ⁏ S˘ ⁏ P :=
  fun ⟨hS, hP⟩ => (cnv_semi_semi (S := S˘) (cnv_mem_arrow_Cls_one hS) hP).symm

/-- ✱151·254. \(\vdash :S\in 1\rightarrow 1.\supset .S\dagger \upharpoonright \breve{C} ʻʻ\text{Cl}ʻ\text{ᗡ}ʻS=\text{Cnv}ʻ{\breve{S} \dagger \upharpoonright \breve{C} ʻʻ\text{Cl}ʻ\text{D}ʻS}\)

`C̆''Cl'ᗡ'S` is `C˘ ʻʻ cl (codom S)` (the relations whose fields are contained in `ᗡ'S`);
`Cnv'{…}` is written `(…)˘` (`desc_Cnv`), and `S̆†` is `(Cnv'S)†`, `daggerRel S˘`. -/
theorem pm151_254 {S : α → β → Prop} :
    S ∈ arrow one one →
      daggerRel S ↾ C˘ ʻʻ cl (codom S) = (daggerRel S˘ ↾ C˘ ʻʻ cl (dom S))˘ := by
  intro hS
  refine rel_ext' fun P Q => ?_
  show P = S ⁏ Q ∧ Q ∈ C˘ ʻʻ cl (codom S) ↔ Q = S˘ ⁏ P ∧ P ∈ C˘ ʻʻ cl (dom S)
  rw [mem_Ccnv_img_cl, mem_Ccnv_img_cl]
  have h := pm151_251 (P := P) (Q := Q) hS
  constructor
  · rintro ⟨a, b⟩
    obtain ⟨c, d⟩ := h.1 ⟨b, a⟩
    exact ⟨d, c⟩
  · rintro ⟨a, b⟩
    obtain ⟨c, d⟩ := h.2 ⟨b, a⟩
    exact ⟨d, c⟩

/-- ✱151·26. \[\begin{align}\vdash \colon\ldotp S\in \text{Cls}\rightarrow 1.CʻQ\subset &\text{ᗡ}ʻS.\supset :\\ &P\,\unicode{x2abd}\, S^{;}Q.\supset .\breve{S} ^{;}P\,\unicode{x2abd}\, Q:S^{;}Q\,\unicode{x2abd}\, P.\supset .Q\,\unicode{x2abd}\, \breve{S} ^{;}P\end{align}\] -/
theorem pm151_26 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    S ∈ arrow Cls one ∧ fld Q ⊆ codom S →
      (P ⪽ S ⁏ Q → S˘ ⁏ P ⪽ Q) ∧ (S ⁏ Q ⪽ P → Q ⪽ S˘ ⁏ P) := by
  rintro ⟨hS, hQ⟩
  have e := cnv_semi_semi hS hQ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := semi_mono S˘ h
    rwa [e] at this
  · have := semi_mono S˘ h
    rwa [e] at this

/-- ✱151·261. \[\begin{align}&\vdash \colon\ldotp S\in 1\rightarrow \text{Cls}.CʻP\subset \text{D}ʻS.\supset :\\ &Q\,\unicode{x2abd}\, \breve{S} ^{;}P.\supset .S^{;}Q\,\unicode{x2abd}\, P:\breve{S} ^{;}P\,\unicode{x2abd}\, Q.\supset .P\,\unicode{x2abd}\, S^{;}Q \quad\left[*151·26\frac{\breve{S},\,Q,\,P}{S,\,P,\,Q}\right]\end{align}\] -/
theorem pm151_261 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    S ∈ arrow one Cls ∧ fld P ⊆ dom S →
      (Q ⪽ S˘ ⁏ P → S ⁏ Q ⪽ P) ∧ (S˘ ⁏ P ⪽ Q → P ⪽ S ⁏ Q) := by
  rintro ⟨hS, hP⟩
  have e : S ⁏ S˘ ⁏ P = P := cnv_semi_semi (S := S˘) (cnv_mem_arrow_Cls_one hS) hP
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := semi_mono S h
    rwa [e] at this
  · have := semi_mono S h
    rwa [e] at this

/-- ✱151·262. \[\begin{align}&\vdash \colon\ldotp S\in 1\rightarrow 1.CʻP\subset \text{D}ʻS.CʻQ\subset \text{ᗡ}ʻS.\supset :\\ &P\,\unicode{x2abd}\, S^{;}Q.\equiv .\breve{S} ^{;}P\,\unicode{x2abd}\, Q:Q\,\unicode{x2abd}\, \breve{S} ^{;}P.\equiv .S^{;}Q\,\unicode{x2abd}\, P \\ &[*151·26·261]\end{align}\] -/
theorem pm151_262 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    (S ∈ arrow one one ∧ fld P ⊆ dom S) ∧ fld Q ⊆ codom S →
      (P ⪽ S ⁏ Q ↔ S˘ ⁏ P ⪽ Q) ∧ (Q ⪽ S˘ ⁏ P ↔ S ⁏ Q ⪽ P) := by
  rintro ⟨⟨hS, hP⟩, hQ⟩
  have h1 := pm151_26 (P := P) ⟨arrow_Cls_one_of hS, hQ⟩
  have h2 := pm151_261 (Q := Q) ⟨arrow_one_Cls_of hS, hP⟩
  exact ⟨⟨h1.1, h2.2⟩, ⟨h2.1, h1.2⟩⟩

/-- ✱151·263. \[\begin{align}&\vdash \colon\ldotp S\in 1\rightarrow 1.CʻP\subset \text{D}ʻS.CʻQ\subset \text{ᗡ}ʻS.\supset :\\ &P\,\unicode{x2abd}\, S^{;}Q.Q\,\unicode{x2abd}\, \breve{S} ^{;}P.\equiv .\breve{S} ^{;}P\,\unicode{x2abd}\, Q.S^{;}Q\,\unicode{x2abd}\, P.\equiv .P=S^{;}Q.\equiv .Q=\breve{S} ^{;}P\\ &[*151·262]\end{align}\]

The chain of four equivalences is the conjunction of its three links. -/
theorem pm151_263 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    (S ∈ arrow one one ∧ fld P ⊆ dom S) ∧ fld Q ⊆ codom S →
      ((P ⪽ S ⁏ Q ∧ Q ⪽ S˘ ⁏ P ↔ S˘ ⁏ P ⪽ Q ∧ S ⁏ Q ⪽ P) ∧
        (S˘ ⁏ P ⪽ Q ∧ S ⁏ Q ⪽ P ↔ P = S ⁏ Q)) ∧ (P = S ⁏ Q ↔ Q = S˘ ⁏ P) := by
  intro h
  obtain ⟨e1, e2⟩ := pm151_262 h
  obtain ⟨⟨hS, hP⟩, hQ⟩ := h
  have l3 : P = S ⁏ Q ↔ Q = S˘ ⁏ P :=
    ⟨fun e => ((pm151_251 hS).1 ⟨hQ, e⟩).2, fun e => ((pm151_251 hS).2 ⟨hP, e⟩).2⟩
  refine ⟨⟨⟨fun ⟨a, b⟩ => ⟨e1.1 a, e2.1 b⟩, fun ⟨a, b⟩ => ⟨e1.2 a, e2.2 b⟩⟩, ?_⟩, l3⟩
  constructor
  · rintro ⟨a, b⟩
    exact rsub_antisymm (e1.2 a) b
  · intro e
    have e' := l3.1 e
    exact ⟨fun x y h => e' ▸ h, fun x y h => e ▸ h⟩

/-- ✱151·264. \(\vdash \colon\ldotp S\upharpoonright CʻQ\in 1\rightarrow 1.\supset :P\,\unicode{x2abd}\, S^{;}Q.Q\,\unicode{x2abd}\, \breve{S} ^{;}P.\equiv .P=S^{;}Q\)

**Status.** proved (corrected): the hypothesis `C'Q ⊂ ᗡ'S` is needed. As printed, the
implication from right to left fails: with `S = Λ̇`, `P = Λ̇` and `Q` not null, `S ↾ C'Q ∈ 1 → 1`
and `P = S;Q`, but `Q ⊂̇ S̆;P = Λ̇` is false (`pm151_264_printed_false`). PM's
demonstration applies ✱151·262 with `S ↾ C'Q` for `S`, which requires `C'Q ⊂ ᗡ'S`; this is
the added hypothesis (it holds where PM uses the proposition, ✱151·281). -/
theorem pm151_264 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    S ↾ fld Q ∈ arrow one one ∧ fld Q ⊆ codom S → (P ⪽ S ⁏ Q ∧ Q ⪽ S˘ ⁏ P ↔ P = S ⁏ Q) := by
  rsimp
  grind

/-- The printed form of ✱151·264 (without `C'Q ⊂ ᗡ'S`) is false. -/
theorem pm151_264_printed_false : ¬ ∀ {P Q S : Unit → Unit → Prop},
    S ↾ fld Q ∈ arrow one one → (P ⪽ S ⁏ Q ∧ Q ⪽ S˘ ⁏ P ↔ P = S ⁏ Q) := by
  have hS : (rNull : Unit → Unit → Prop) ↾ fld (fun _ _ : Unit => True) ∈ arrow one one := by
    rsimp
    grind
  have e : (rNull : Unit → Unit → Prop) =
      (rNull : Unit → Unit → Prop) ⁏ (fun _ _ : Unit => True) := by
    rsimp
    grind
  have hn : ¬ ((rNull : Unit → Unit → Prop)˘ ⁏ (rNull : Unit → Unit → Prop)) () () := by
    rsimp
    grind
  intro h
  exact hn (((h hS).2 e).2 () () trivial)

/-- ✱151·27. \[\begin{align}&\vdash :S\in 1\rightarrow 1.P\,\unicode{x2abd}\, S^{;}Q.Q\,\unicode{x2abd}\, \breve{S} ^{;}P.\\ &\equiv .S\in 1\rightarrow 1.CʻP\subset \text{D}ʻS.CʻQ\subset \text{ᗡ}ʻS.\breve{S} ^{;}P\,\unicode{x2abd}\, Q.S^{;}Q\,\unicode{x2abd}\, P.\\ &\equiv .S\in 1\rightarrow 1.CʻQ\subset \text{ᗡ}ʻS.P=S^{;}Q.\\ &\equiv .S\in 1\rightarrow 1.CʻP\subset \text{D}ʻS.Q=\breve{S} ^{;}P\\ &[*151·263.*5·32.*150·203.*4·73]\end{align}\]

The chain of four equivalences is the conjunction of its three links; each product is
bracketed to the left. -/
theorem pm151_27 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    ((((S ∈ arrow one one ∧ P ⪽ S ⁏ Q) ∧ Q ⪽ S˘ ⁏ P) ↔
        ((((S ∈ arrow one one ∧ fld P ⊆ dom S) ∧ fld Q ⊆ codom S) ∧ S˘ ⁏ P ⪽ Q) ∧ S ⁏ Q ⪽ P)) ∧
      (((((S ∈ arrow one one ∧ fld P ⊆ dom S) ∧ fld Q ⊆ codom S) ∧ S˘ ⁏ P ⪽ Q) ∧ S ⁏ Q ⪽ P) ↔
        (S ∈ arrow one one ∧ fld Q ⊆ codom S) ∧ P = S ⁏ Q)) ∧
      ((S ∈ arrow one one ∧ fld Q ⊆ codom S) ∧ P = S ⁏ Q ↔
        (S ∈ arrow one one ∧ fld P ⊆ dom S) ∧ Q = S˘ ⁏ P) := by
  have hA : ((S ∈ arrow one one ∧ P ⪽ S ⁏ Q) ∧ Q ⪽ S˘ ⁏ P) ↔
      (S ∈ arrow one one ∧ fld Q ⊆ codom S) ∧ P = S ⁏ Q := by
    constructor
    · rintro ⟨⟨hS, h1⟩, h2⟩
      have hP : fld P ⊆ dom S := (fld_mono h1).trans pm150_203
      have hQ : fld Q ⊆ codom S := (fld_mono h2).trans pm150_203
      exact ⟨⟨hS, hQ⟩, (pm151_263 ⟨⟨hS, hP⟩, hQ⟩).1.2.1 ((pm151_263 ⟨⟨hS, hP⟩, hQ⟩).1.1.1 ⟨h1, h2⟩)⟩
    · rintro ⟨⟨hS, hQ⟩, hP⟩
      have hP' : fld P ⊆ dom S := by rw [hP]; exact pm150_203
      have := (pm151_263 ⟨⟨hS, hP'⟩, hQ⟩).1
      exact ⟨⟨hS, (this.1.2 (this.2.2 hP)).1⟩, (this.1.2 (this.2.2 hP)).2⟩
  have hB : ((((S ∈ arrow one one ∧ fld P ⊆ dom S) ∧ fld Q ⊆ codom S) ∧ S˘ ⁏ P ⪽ Q) ∧
      S ⁏ Q ⪽ P) ↔ (S ∈ arrow one one ∧ fld Q ⊆ codom S) ∧ P = S ⁏ Q := by
    constructor
    · rintro ⟨⟨⟨⟨hS, hP⟩, hQ⟩, h1⟩, h2⟩
      exact ⟨⟨hS, hQ⟩, (pm151_263 ⟨⟨hS, hP⟩, hQ⟩).1.2.1 ⟨h1, h2⟩⟩
    · rintro ⟨⟨hS, hQ⟩, hP⟩
      have hP' : fld P ⊆ dom S := by rw [hP]; exact pm150_203
      have := ((pm151_263 ⟨⟨hS, hP'⟩, hQ⟩).1.2.2 hP)
      exact ⟨⟨⟨⟨hS, hP'⟩, hQ⟩, this.1⟩, this.2⟩
  have hC : (S ∈ arrow one one ∧ fld Q ⊆ codom S) ∧ P = S ⁏ Q ↔
      (S ∈ arrow one one ∧ fld P ⊆ dom S) ∧ Q = S˘ ⁏ P := by
    constructor
    · rintro ⟨⟨hS, hQ⟩, hP⟩
      have h' := (pm151_251 hS).1 ⟨hQ, hP⟩
      exact ⟨⟨hS, h'.1⟩, h'.2⟩
    · rintro ⟨⟨hS, hP⟩, hQP⟩
      have h' := (pm151_251 hS).2 ⟨hP, hQP⟩
      exact ⟨⟨hS, h'.1⟩, h'.2⟩
  exact ⟨⟨hA.trans hB.symm, hB⟩, hC⟩

/-- ✱151·271. \[\begin{align}&\vdash :(\exists S).S\in 1\rightarrow 1.P\,\unicode{x2abd}\, S^{;}Q.Q\,\unicode{x2abd}\, \breve{S} ^{;}P.\\ &\equiv .(\exists S).S\in 1\rightarrow 1.CʻP\subset \text{D}ʻS.CʻQ\subset \text{ᗡ}ʻS.\breve{S} ^{;}P\,\unicode{x2abd}\, Q.S^{;}Q\,\unicode{x2abd}\, P.\\ &\equiv .P\,\text{smor}\,Q \quad[*151·27·21]\end{align}\] -/
theorem pm151_271 {P : α → α → Prop} {Q : β → β → Prop} :
    ((∃ S : α → β → Prop, (S ∈ arrow one one ∧ P ⪽ S ⁏ Q) ∧ Q ⪽ S˘ ⁏ P) ↔
      ∃ S : α → β → Prop, (((S ∈ arrow one one ∧ fld P ⊆ dom S) ∧ fld Q ⊆ codom S) ∧
        S˘ ⁏ P ⪽ Q) ∧ S ⁏ Q ⪽ P) ∧
    ((∃ S : α → β → Prop, (((S ∈ arrow one one ∧ fld P ⊆ dom S) ∧ fld Q ⊆ codom S) ∧
        S˘ ⁏ P ⪽ Q) ∧ S ⁏ Q ⪽ P) ↔ smor P Q) := by
  refine ⟨exists_congr fun S => pm151_27.1.1, ?_⟩
  rw [pm151_21]
  exact exists_congr fun S => pm151_27.1.2

/-- ✱151·28. \[\begin{align}\vdash \colon\ldotp P\,\text{smor}\,Q.\equiv :(\exists S):S\in 1\rightarrow 1:&xPy.\supset _{x,y}.(\breve{S} ʻx)Q(\breve{S} ʻy):\\ &zQw.\supset _{z,w}.(Sʻz)P(Sʻw)\end{align}\]

`(S̆'x)Q(S̆'y)` and `(S'z)P(S'w)` have two descriptions each, the first with the larger
scope; the right-hand side is a product of three (two-dot products, bracketed to the left). -/
theorem pm151_28 {P : α → α → Prop} {Q : β → β → Prop} :
    smor P Q ↔ ∃ S : α → β → Prop, (S ∈ arrow one one ∧
      ∀ x y, P x y → Desc S˘ x (fun a => Desc S˘ y (fun b => Q a b))) ∧
      ∀ z w, Q z w → Desc S z (fun a => Desc S w (fun b => P a b)) := by
  constructor
  · rintro ⟨S, ⟨hS, hQ⟩, rfl⟩
    obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS
    refine ⟨S, ⟨hS, fun x y hxy => ?_⟩, fun z w hzw => ?_⟩
    · obtain ⟨z, w, hxz, hyw, hzw⟩ := (semi_iff S Q x y).1 hxy
      exact desc_desc_iff.2 ⟨z, w, ⟨fun u => ⟨fun hu => h2 x u z ⟨hu, hxz⟩, fun e => e ▸ hxz⟩,
        fun u => ⟨fun hu => h2 y u w ⟨hu, hyw⟩, fun e => e ▸ hyw⟩⟩, hzw⟩
    · obtain ⟨x, hxz⟩ : z ∈ codom S := by rw [← hQ]; exact ⟨w, Or.inl hzw⟩
      obtain ⟨y, hyw⟩ : w ∈ codom S := by rw [← hQ]; exact ⟨z, Or.inr hzw⟩
      exact desc_desc_iff.2 ⟨x, y, ⟨fun u => ⟨fun hu => h1 u x z ⟨hu, hxz⟩, fun e => e ▸ hxz⟩,
        fun u => ⟨fun hu => h1 u y w ⟨hu, hyw⟩, fun e => e ▸ hyw⟩⟩,
        (semi_iff S Q x y).2 ⟨z, w, hxz, hyw, hzw⟩⟩
  · rintro ⟨S, ⟨-, h1⟩, h2⟩
    exact ⟨_, (smor281 h1 h2).2⟩

/-- ✱151·281. \[\begin{align}\vdash \colon\ldotp xPy.&\supset _{x,y}.(\breve{S} ʻx)Q(\breve{S} ʻy):zQw.\supset _{z,w}.(Sʻz)P(Sʻw):\\ &\supset .CʻP\upharpoonleft S=S\upharpoonright CʻQ.S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q\end{align}\]

`C'P ↿ S` is `fld P ◁ S`. -/
theorem pm151_281 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    (∀ x y, P x y → Desc S˘ x (fun a => Desc S˘ y (fun b => Q a b))) ∧
      (∀ z w, Q z w → Desc S z (fun a => Desc S w (fun b => P a b))) →
        fld P ◁ S = S ↾ fld Q ∧ S ↾ fld Q ∈ smorbar P Q :=
  fun ⟨h1, h2⟩ => smor281 h1 h2

/-- ✱151·29. \[\begin{align}&\vdash \colon\ldotp P\,\text{smor}\,Q.\equiv :(\exists S):xPy.\supset _{x,y}.(\breve{S} ʻx)Q(\breve{S} ʻy):zQw.\supset _{z,w}.(Sʻz)P(Sʻw)\\ &[*151·28·281]\end{align}\] -/
theorem pm151_29 {P : α → α → Prop} {Q : β → β → Prop} :
    smor P Q ↔ ∃ S : α → β → Prop,
      (∀ x y, P x y → Desc S˘ x (fun a => Desc S˘ y (fun b => Q a b))) ∧
        ∀ z w, Q z w → Desc S z (fun a => Desc S w (fun b => P a b)) := by
  constructor
  · intro h
    obtain ⟨S, ⟨-, h1⟩, h2⟩ := pm151_28.1 h
    exact ⟨S, h1, h2⟩
  · rintro ⟨S, h1, h2⟩
    exact ⟨_, (smor281 h1 h2).2⟩

/-- ✱151·31. \(\vdash :S\in \text{Cls}\rightarrow 1.S^{;}Q=S^{;}R.CʻQ\subset \text{ᗡ}ʻS.CʻR\subset \text{ᗡ}ʻS.\supset .Q=R\) -/
theorem pm151_31 {Q R : β → β → Prop} {S : α → β → Prop} :
    ((S ∈ arrow Cls one ∧ S ⁏ Q = S ⁏ R) ∧ fld Q ⊆ codom S) ∧ fld R ⊆ codom S → Q = R := by
  rintro ⟨⟨⟨hS, e⟩, hQ⟩, hR⟩
  rw [← cnv_semi_semi hS hQ, e, cnv_semi_semi hS hR]

/-- ✱151·32. \(\vdash \colon\ldotp P\,\text{smor}\,Q.\supset :\dot{\exists} !P.\equiv .\dot{\exists} !Q \quad[*151·18.*73·36.*33·24]\) -/
theorem pm151_32 {P : α → α → Prop} {Q : β → β → Prop} : smor P Q → (rEx P ↔ rEx Q) := by
  rintro ⟨S, ⟨-, hQ⟩, rfl⟩
  exact pm150_24 hQ.le

/-- ✱151·33. \(\vdash :S\in P\,\overline{\text{smor}}\,Q.\supset .P\mid S=S\mid Q.\breve{S} \mid P=Q\mid \breve{S}\) -/
theorem pm151_33 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    S ∈ smorbar P Q → P ⨾ S = S ⨾ Q ∧ S˘ ⨾ P = Q ⨾ S˘ := by
  rintro ⟨⟨hS, hQ⟩, rfl⟩
  rsimp
  grind

/-- ✱151·4. \(\vdash :T\upharpoonright CʻQ\in 1\rightarrow 1.CʻP=TʻʻCʻQ.Q=\breve{T} ^{;}P.\supset .T\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q\) -/
theorem pm151_4 {P : α → α → Prop} {Q : β → β → Prop} {T : α → β → Prop} :
    (T ↾ fld Q ∈ arrow one one ∧ fld P = T ʻʻ fld Q) ∧ Q = T˘ ⁏ P → T ↾ fld Q ∈ smorbar P Q := by
  rintro ⟨⟨hT, hP⟩, hQ⟩
  have hQT : fld Q ⊆ codom T := by
    have := pm150_203 (S := T˘) (Q := P)
    rw [← hQ] at this
    exact this
  refine pm151_22.1 ⟨⟨hT, hQT⟩, ?_⟩
  refine rel_ext' fun x y => ?_
  rw [semi_iff]
  constructor
  · intro hxy
    obtain ⟨z, hz, hxz⟩ : x ∈ T ʻʻ fld Q := by rw [← hP]; exact ⟨y, Or.inl hxy⟩
    obtain ⟨w, hw, hyw⟩ : y ∈ T ʻʻ fld Q := by rw [← hP]; exact ⟨x, Or.inr hxy⟩
    refine ⟨z, w, hxz, hyw, ?_⟩
    rw [hQ, semi_iff]
    exact ⟨x, y, hxz, hyw, hxy⟩
  · rintro ⟨z, w, hxz, hyw, hzw⟩
    have hz : z ∈ fld Q := ⟨w, Or.inl hzw⟩
    have hw : w ∈ fld Q := ⟨z, Or.inr hzw⟩
    rw [hQ, semi_iff] at hzw
    obtain ⟨a, b, haz, hbw, hab⟩ := hzw
    obtain rfl := (mem_arrow_one_one.1 hT).1 a x z ⟨⟨haz, hz⟩, ⟨hxz, hz⟩⟩
    obtain rfl := (mem_arrow_one_one.1 hT).1 b y w ⟨⟨hbw, hw⟩, ⟨hyw, hw⟩⟩
    exact hab

/-- ✱151·401. \[\begin{align}\vdash :T\upharpoonright CʻP\in X,\overline{\text{smor}}\,P.T\upharpoonright CʻQ\in Y\overline{\text{smor}} &Q.S\in P\,\overline{\text{smor}}\,Q.\supset .\\ &T^{;}S\in X\,\overline{\text{smor}} \,Y\end{align}\]

(The e-text prints a stray comma in `X, smor̄ P`.) `P`, `Q` are of one type, since `T ↾ C'P`
and `T ↾ C'Q` are restrictions of the same `T`. -/
theorem pm151_401 {P Q S : α → α → Prop} {X Y : δ → δ → Prop} {T : δ → α → Prop} :
    (T ↾ fld P ∈ smorbar X P ∧ T ↾ fld Q ∈ smorbar Y Q) ∧ S ∈ smorbar P Q →
      T ⁏ S ∈ smorbar X Y := by
  rintro ⟨⟨hX, hY⟩, hS⟩
  have h := pm151_141 ⟨pm151_141 ⟨hX, hS⟩, pm151_131.1 hY⟩
  obtain ⟨⟨-, hQ⟩, hP⟩ := hS
  have hdom : dom S = fld P := by rw [hP, pm150_23 hQ]
  have e : (T ↾ fld P) ⨾ S ⨾ (T ↾ fld Q)˘ = T ⁏ S := by
    rw [← hdom, hQ]
    rsimp
    grind
  rwa [e] at h

/-- ✱151·41. \[\begin{align}\vdash :S\in P\,\overline{\text{smor}}\,Q.T\upharpoonright CʻP,T\upharpoonright &CʻQ\in 1\rightarrow 1.CʻP\cup CʻQ\subset \text{ᗡ}ʻT.\supset .\\ &T^{;}S\in (T^{;}P)\overline{\text{smor}} (T^{;}Q) \quad[*151·401·22]\end{align}\] -/
theorem pm151_41 {P Q S : α → α → Prop} {T : δ → α → Prop} :
    (S ∈ smorbar P Q ∧ (T ↾ fld P ∈ arrow one one ∧ T ↾ fld Q ∈ arrow one one)) ∧
      fld P ∪ fld Q ⊆ codom T → T ⁏ S ∈ smorbar (T ⁏ P) (T ⁏ Q) := by
  rintro ⟨⟨hS, h1, h2⟩, h3⟩
  refine pm151_401 ⟨⟨pm151_22.1 ⟨⟨h1, ?_⟩, rfl⟩, pm151_22.1 ⟨⟨h2, ?_⟩, rfl⟩⟩, hS⟩
  · exact fun x hx => h3 (Or.inl hx)
  · exact fun x hx => h3 (Or.inr hx)

/-- ✱151·5. \[\begin{align}\vdash :S\upharpoonright &CʻQ\in P\,\overline{\text{smor}}\,Q.\supset .\\ &\text{D}ʻP=Sʻʻ\text{D}ʻQ.\text{ᗡ}ʻP=Sʻʻ\text{ᗡ}ʻQ.\overrightarrow{B}ʻP=Sʻʻ\overrightarrow{B}ʻQ.\overrightarrow{B}ʻ\breve{P} =Sʻʻ\overrightarrow{B}ʻ\breve{Q}\end{align}\]

`B⃗'P` is `refs Beg P` (✱93·01), `B⃗'P̆` is `refs Beg P˘`; the conclusion is a product of four,
bracketed to the left. -/
theorem pm151_5 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    S ↾ fld Q ∈ smorbar P Q →
      ((dom P = S ʻʻ dom Q ∧ codom P = S ʻʻ codom Q) ∧ refs Beg P = S ʻʻ refs Beg Q) ∧
        refs Beg P˘ = S ʻʻ refs Beg Q˘ := by
  intro h
  obtain ⟨⟨h1, hQ⟩, rfl⟩ := pm151_22.2 h
  have hQ' : fld Q˘ ⊆ codom S := by rw [fld_cnv]; exact hQ
  have h1' : S ↾ fld Q˘ ∈ arrow one one := by rw [fld_cnv]; exact h1
  refine ⟨⟨⟨(pm150_21 fun z ⟨w, hwz⟩ => hQ ⟨w, Or.inr hwz⟩).1,
    (pm150_211 fun z ⟨w, hzw⟩ => hQ ⟨w, Or.inl hzw⟩).1⟩, beg_semi h1 hQ⟩, ?_⟩
  rw [pm150_12]
  exact beg_semi h1' hQ'

/-- ✱151·51. \(\vdash :S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q.R\,\unicode{x2abd}\, Q.\supset .S\upharpoonright CʻR\in (S^{;}R)\overline{\text{smor}} R.S^{;}R\,\unicode{x2abd}\, P\) -/
theorem pm151_51 {P : α → α → Prop} {Q R : β → β → Prop} {S : α → β → Prop} :
    S ↾ fld Q ∈ smorbar P Q ∧ R ⪽ Q → S ↾ fld R ∈ smorbar (S ⁏ R) R ∧ S ⁏ R ⪽ P := by
  rintro ⟨h, hR⟩
  obtain ⟨⟨h1, hQ⟩, rfl⟩ := pm151_22.2 h
  have hRQ := fld_mono hR
  exact ⟨pm151_22.1 ⟨⟨cres_one_one_mono hRQ h1, hRQ.trans hQ⟩, rfl⟩, semi_mono S hR⟩

/-- ✱151·52. \(\vdash :P\,\text{smor}\,Q.\supset .\text{Rl}ʻQ\subset \text{smor}ʻʻ\text{Rl}ʻP \quad[*151·51·12·14]\)

`smor''Rl'P` is `smor ʻʻ rl P`. -/
theorem pm151_52 {P : α → α → Prop} {Q : β → β → Prop} : smor P Q → rl Q ⊆ smor ʻʻ rl P := by
  rintro hPQ R hR
  obtain ⟨S, ⟨hS, hQ⟩, hP⟩ := hPQ
  have h : S ↾ fld Q ∈ smorbar P Q := pm151_22.1 ⟨⟨cres_one_one hS, hQ.le⟩, hP⟩
  obtain ⟨h1, h2⟩ := pm151_51 ⟨h, hR⟩
  exact ⟨S ⁏ R, h2, smor_symm ⟨_, h1⟩⟩

/-- ✱151·53. \[\begin{align}\vdash :S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q.T\in &\text{Pot}ʻQ.\supset .\\ &S\upharpoonright CʻT\in (S^{;}T)\overline{\text{smor}} T.S^{;}T\in \text{Pot}ʻP\end{align}\]

`Pot'Q` is `pot Q`. -/
theorem pm151_53 {P : α → α → Prop} {Q T : β → β → Prop} {S : α → β → Prop} :
    S ↾ fld Q ∈ smorbar P Q ∧ T ∈ pot Q → S ↾ fld T ∈ smorbar (S ⁏ T) T ∧ S ⁏ T ∈ pot P := by
  rintro ⟨h, hT⟩
  obtain ⟨⟨h1, hQ'⟩, hP⟩ := h
  have hQ := codom_cres_iff.1 hQ'
  have hTQ := fld_pot_subset hT
  refine ⟨pm151_22.1 ⟨⟨cres_one_one_mono hTQ h1, hTQ.trans hQ⟩, rfl⟩, ?_⟩
  have hdom : dom Q ⊆ codom (S ↾ fld Q) := fun z ⟨w, hzw⟩ => by
    rw [← hQ']; exact ⟨w, Or.inl hzw⟩
  have := (pm150_8 ⟨⟨arrow_Cls_one_of h1, Or.inl hdom⟩, hT⟩).1
  rwa [pm150_33 hTQ, ← hP] at this

/-- ✱151·54. \(\vdash :S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q.\supset .S\upharpoonright CʻQ\in P_{\text{po}}\overline{\text{smor}} Q_{\text{po}}\)

`P_po` is `po P` (✱91·05). -/
theorem pm151_54 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    S ↾ fld Q ∈ smorbar P Q → S ↾ fld Q ∈ smorbar (po P) (po Q) := by
  intro h
  obtain ⟨⟨h1, hQ⟩, hP⟩ := h
  refine ⟨⟨h1, fld_po.trans hQ⟩, ?_⟩
  have hdom : dom Q ⊆ codom (S ↾ fld Q) := fun z ⟨w, hzw⟩ => by
    rw [← hQ]; exact ⟨w, Or.inl hzw⟩
  rw [hP, pm150_83 ⟨arrow_Cls_one_of h1, Or.inl hdom⟩]

/-- ✱151·55. \(\vdash :S\in P\,\overline{\text{smor}}\,Q.\supset .S\in P_{\text{po}}\overline{\text{smor}} Q_{\text{po}} \quad[*151·54]\) -/
theorem pm151_55 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} :
    S ∈ smorbar P Q → S ∈ smorbar (po P) (po Q) := by
  intro h
  have e : S ↾ fld Q = S := by
    obtain ⟨⟨-, hQ⟩, -⟩ := h
    refine rel_ext' fun x z => ⟨fun h => h.1, fun h => ⟨h, by rw [hQ]; exact ⟨x, h⟩⟩⟩
  have h' : S ↾ fld Q ∈ smorbar P Q := by rw [e]; exact h
  have := pm151_54 h'
  rwa [e] at this

/-- ✱151·56. \(\vdash :P\,\text{smor}\,Q.\supset .P_{\text{po}}\text{smor}Q_{\text{po}} \quad[*151·55]\) -/
theorem pm151_56 {P : α → α → Prop} {Q : β → β → Prop} : smor P Q → smor (po P) (po Q) :=
  fun ⟨S, h⟩ => ⟨S, pm151_55 h⟩

/-- ✱151·57. \(\vdash :S\in P\,\overline{\text{smor}}\,Q.z,w\in CʻQ.\supset .P(Sʻz\vdash\dashv Sʻw)=SʻʻQ(z\vdash\dashv w)\)

`P(x ⊢⊣ y)` is `itvCC P x y` (✱121·013); the descriptions `S'z`, `S'w` have the equation
for scope, `S'z` the larger one. -/
theorem pm151_57 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} {z w : β} :
    S ∈ smorbar P Q ∧ (z ∈ fld Q ∧ w ∈ fld Q) →
      Desc S z (fun a => Desc S w (fun b => itvCC P a b = S ʻʻ itvCC Q z w)) := by
  rintro ⟨⟨⟨hS, hQ⟩, hP⟩, hz, hw⟩
  exact itv_transfer hS hQ hP hz hw

/-- ✱151·58. \(\vdash :S\in P\,\overline{\text{smor}}\,Q.\supset .S\upharpoonright CʻQ_{\nu }\in P_{\nu }\overline{\text{smor}} Q_{\nu }\)

`Q_ν` is `Pnu Q ν` (✱121·02), with the cardinal `ν` of any type. -/
theorem pm151_58 {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} {ν : Set (Set γ)} :
    S ∈ smorbar P Q → S ↾ fld (Pnu Q ν) ∈ smorbar (Pnu P ν) (Pnu Q ν) := by
  rintro ⟨⟨hS, hQ⟩, hP⟩
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS
  have hPQ : ∀ x y z w, S x z → S y w → (Pnu P ν x y ↔ Pnu Q ν z w) := by
    intro x y z w hxz hyw
    have hz : z ∈ fld Q := by rw [hQ]; exact ⟨x, hxz⟩
    have hw : w ∈ fld Q := by rw [hQ]; exact ⟨y, hyw⟩
    have ux : ∀ u, S u z ↔ u = x := fun u => ⟨fun hu => h1 u x z ⟨hu, hxz⟩, fun e => e ▸ hxz⟩
    have uy : ∀ u, S u w ↔ u = y := fun u => ⟨fun hu => h1 u y w ⟨hu, hyw⟩, fun e => e ▸ hyw⟩
    have e := itv_transfer hS hQ hP hz hw
    rw [Desc, TheIs_iff_of_unique ux, Desc, TheIs_iff_of_unique uy] at e
    have hsm : sm (itvCC P x y) (itvCC Q z w) := by
      rw [e]
      exact sm_img_cres (fun u hu => by rw [← hQ]; exact itvCC_sub_fld hu) (cres_one_one hS)
    exact n₀c_eq_cardAdd_transfer hsm ν one
  have hfld : fld (Pnu Q ν) ⊆ fld Q := fld_Pnu_subset
  have hQS : fld Q ⊆ codom S := hQ.le
  refine pm151_22.1 ⟨⟨cres_one_one hS, hfld.trans hQS⟩, ?_⟩
  refine rel_ext' fun x y => ?_
  rw [semi_iff]
  constructor
  · intro hxy
    have hdomS : dom S = fld P := by rw [hP, pm150_23 hQ]
    obtain ⟨z, hxz⟩ : x ∈ dom S := by rw [hdomS]; exact fld_Pnu_subset ⟨y, Or.inl hxy⟩
    obtain ⟨w, hyw⟩ : y ∈ dom S := by rw [hdomS]; exact fld_Pnu_subset ⟨x, Or.inr hxy⟩
    exact ⟨z, w, hxz, hyw, (hPQ x y z w hxz hyw).1 hxy⟩
  · rintro ⟨z, w, hxz, hyw, hzw⟩
    exact (hPQ x y z w hxz hyw).2 hzw

/-- ✱151·59. \(\vdash :P\,\text{smor}\,Q.\supset .P_{\nu }\text{smor}Q_{\nu } \quad[*151·58]\) -/
theorem pm151_59 {P : α → α → Prop} {Q : β → β → Prop} {ν : Set (Set γ)} :
    smor P Q → smor (Pnu P ν) (Pnu Q ν) :=
  fun ⟨_, h⟩ => ⟨_, pm151_58 h⟩

/-- ✱151·6. \[\begin{align}&\vdash .\text{Cnv}^{;}P\,\text{smor}\,P.\text{Cnv}\upharpoonright CʻP\in (\text{Cnv}^{;}P)\,\overline{\text{smor}}\,P\\ &[*151·231.*31·13.*72·11]\end{align}\]

`P` is a relation of relations (PM: the proposition is only significant then); `Cnv` is the
relation of ✱31·01, `Cnv;P` is `Cnv ⁏ P`. -/
theorem pm151_6 {P : (α → β → Prop) → (α → β → Prop) → Prop} :
    smor (Cnv ⁏ P) P ∧ Cnv ↾ fld P ∈ smorbar (Cnv ⁏ P) P := by
  have hE : ∀ y : α → β → Prop, EDesc (Cnv : (β → α → Prop) → (α → β → Prop) → Prop) y :=
    fun y => ⟨y˘, fun x => Cnv_iff⟩
  have h : Cnv ↾ fld P ∈ smorbar (Cnv ⁏ P) P := by
    refine pm151_231 ⟨hE, ?_, rfl⟩
    refine mem_arrow_one_one.2
      ⟨fun x y z ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => ?_, fun x y z ⟨⟨hy, _⟩, ⟨hz, _⟩⟩ => ?_⟩
    · rw [Cnv_iff] at hx hy; rw [hx, hy]
    · rw [Cnv_iff] at hy hz
      have := hy.symm.trans hz
      exact congrArg cnv this
  exact ⟨⟨_, h⟩, h⟩

/-- ✱151·61. \(\vdash .\iota ^{;}P\,\text{smor}\,P \quad[*151·232.*51·12.*72·18]\)

`ι` is `iota` (`ι'x` to `x`). -/
theorem pm151_61 {P : α → α → Prop} : smor (iota ⁏ P) P := by
  refine pm151_232 ⟨iota, fun y => EDesc_graph _ y, ?_, rfl⟩
  exact mem_arrow_one_one.2
    ⟨fun A B x ⟨⟨hA, _⟩, ⟨hB, _⟩⟩ => (hA : A = ι x).trans (hB : B = ι x).symm,
      fun A x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => unitCls_injective ((hx : A = ι x).symm.trans hy)⟩

/-- ✱151·62. \(\vdash :CʻP\subset 1.\supset .\breve{\iota} ^{;}P\,\text{smor}\,P \quad[*52·62 . *151·243]\)

`C'P ⊂ 1` is `fld P ⊆ one`. -/
theorem pm151_62 {P : Set α → Set α → Prop} : fld P ⊆ one → smor (iota˘ ⁏ P) P := by
  intro h
  refine pm151_243 ⟨fun A B ⟨hA, hB⟩ => ?_, rfl⟩
  obtain ⟨a, rfl⟩ := h hA
  obtain ⟨b, rfl⟩ := h hB
  have ua : ∀ u, iota˘ u (ι a) ↔ u = a :=
    fun u => ⟨fun hu => unitCls_injective (hu : ι a = ι u).symm, fun e => by subst e; rfl⟩
  have ub : ∀ u, iota˘ u (ι b) ↔ u = b :=
    fun u => ⟨fun hu => unitCls_injective (hu : ι b = ι u).symm, fun e => by subst e; rfl⟩
  rw [desc_eq_iff' ua ub]
  exact ⟨fun e => e ▸ rfl, fun e => unitCls_injective e⟩

/-- ✱151·63. \(\vdash :x\neq y.z\neq w.\supset .x\downarrow y\text{smor}z\downarrow w.x\downarrow z\unicode{x228d} y\downarrow w\in (x\downarrow y)\overline{\text{smor}} (z\downarrow w)\) -/
theorem pm151_63 {x y : α} {z w : β} :
    x ≠ y ∧ z ≠ w → smor (x ↓ y) (z ↓ w) ∧ x ↓ z ⊍ y ↓ w ∈ smorbar (x ↓ y) (z ↓ w) := by
  rintro ⟨hxy, hzw⟩
  have h : x ↓ z ⊍ y ↓ w ∈ smorbar (x ↓ y) (z ↓ w) := by
    refine ⟨⟨?_, ?_⟩, (pm150_72 ⟨hzw, rfl⟩).symm⟩
    · rsimp
      grind
    · rsimp
      grind
  exact ⟨⟨_, h⟩, h⟩

/-- ✱151·631. \(\vdash .x\downarrow x \text{smor} z\downarrow z\) -/
theorem pm151_631 {x : α} {z : β} : smor (x ↓ x) (z ↓ z) := by
  refine ⟨x ↓ z, ⟨?_, ?_⟩, ?_⟩
  · rsimp
    grind
  · rsimp
    grind
  · rsimp
    grind

/-- ✱151·64. \[\begin{align}&\vdash .x\downarrow ^{;}P \,\text{smor} P.(x\downarrow )\upharpoonright CʻP\in (x\downarrow ^{;}P) \overline{\text{smor}} P\\ &[*72·184.*55·12.*151·231]\end{align}\]

`x↓` is `coupleL x` (`x ↓ y` to `y`). -/
theorem pm151_64 {x : γ} {P : α → α → Prop} :
    smor (coupleL x ⁏ P) P ∧ coupleL x ↾ fld P ∈ smorbar (coupleL x ⁏ P) P := by
  have h : coupleL x ↾ fld P ∈ smorbar (coupleL x ⁏ P) P := by
    refine pm151_231 ⟨fun y => EDesc_graph _ y, ?_, rfl⟩
    exact mem_arrow_one_one.2
      ⟨fun R R' y ⟨⟨hR, _⟩, ⟨hR', _⟩⟩ => (hR : R = x ↓ y).trans (hR' : R' = x ↓ y).symm,
        fun R y z ⟨⟨hy, _⟩, ⟨hz, _⟩⟩ =>
          (couple_eq_couple_iff.1 ((hy : R = x ↓ y).symm.trans hz)).2⟩
  exact ⟨⟨_, h⟩, h⟩

/-- ✱151·65. \[\begin{align}&\vdash .\downarrow x^{;}P \,\text{smor} P.(\downarrow x)\upharpoonright CʻP\in (\downarrow x^{;}P)\overline{\text{smor}} P\\ &[*72·184.*55·121.*151·231]\end{align}\]

`↓x` is `coupleR x` (`y ↓ x` to `y`). -/
theorem pm151_65 {x : γ} {P : α → α → Prop} :
    smor (coupleR x ⁏ P) P ∧ coupleR x ↾ fld P ∈ smorbar (coupleR x ⁏ P) P := by
  have h : coupleR x ↾ fld P ∈ smorbar (coupleR x ⁏ P) P := by
    refine pm151_231 ⟨fun y => EDesc_graph _ y, ?_, rfl⟩
    exact mem_arrow_one_one.2
      ⟨fun R R' y ⟨⟨hR, _⟩, ⟨hR', _⟩⟩ => (hR : R = y ↓ x).trans (hR' : R' = y ↓ x).symm,
        fun R y z ⟨⟨hy, _⟩, ⟨hz, _⟩⟩ =>
          (couple_eq_couple_iff.1 ((hy : R = y ↓ x).symm.trans hz)).1⟩
  exact ⟨⟨_, h⟩, h⟩

/-!
## [✱152] Definition and elementary properties of relation-numbers

*(Vol. 2, p. 330)*

> *Summary of* *152.
>
> The relation-number of \(P\), which we denote by \(\text{Nr}ʻP\), is defined as the class of relations which are ordinally similar to \(P\), *i.e.* \[ \text{Nr}ʻP = \overrightarrow{\text{smor}}ʻP. \] Hence our definition is \[ \text{Nr} = \overrightarrow{\text{smor}} \quad\text{Df}. \] The class of relation-numbers consists of all such classes as \(\text{Nr}ʻP\), *i.e.* \[ \text{NR} = \text{D}ʻ\text{Nr} \quad\text{Df}. \] These two definitions are analogous to those of *100, merely substituting "\(\text{smor}\)" for "\(\text{sm}\)." They are justified by similar considerations, and lead to similar results. With the exception of *152·7·71·72, the propositions of this number are the analogues of those of *100, and call for no remarks other than those in the introduction to *100 (*mutatis mutandis*).
>
> *152·7·71·72 give relations between relation-numbers and cardinals. *152·7, which is constantly used, states that the cardinal number of \(CʻQ\) consists of the fields of the relation-number of \(Q\), *i.e.* the classes similar to \(CʻQ\) are the fields of the relations similar to \(Q\); in symbols,
>
> *152·7. \(\vdash . \text{Nc}ʻCʻQ = Cʻʻ\text{Nr}ʻQ\)
>
> …

**Lean reading.** As ✱100 (PM: "the analogues of those of ✱100"): `Nr'P` is `nr γ P` with the
actual type `γ`
explicit, `NR` is `NR β` with the converse-domain type `β` explicit, and `μ, ν ∈ NR` does not
identify the types of the two `NR`s. Convention IT as in ✱100: attributive occurrences
(`P ∈ Nr'Q`) are in the type of the member, logical and equational ones in one type unless an
argumental occurrence intervenes (✱152·53); `smor''μ` "represents in any type the same number"
(✱152·51). `C''Nr'Q` is `C ʻʻ nr γ Q`, `C'''…` is `C ʻʻʻ …`, `ι;P`, `x↓;P`, `↓x;P` are
`iota ⁏ P`, `coupleL x ⁏ P`, `coupleR x ⁏ P`. Where the converse domain of `NR` or `NC` must be a
particular type for the proposition to hold (✱152·41·52·54·71·72), PM's proof fixes it and the
status says so.

**Status.** proved (all propositions; ✱152·01·02 definition; ✱152·35, ✱152·53 proved (reading):
convention IT; ✱152·41, ✱152·52, ✱152·54, ✱152·71, ✱152·72 proved (reading): the
converse-domain types of `NR`, `NC`, see their docstrings)
-/

/-- ✱152·01 (Df). \(\text{Nr} = \overrightarrow{\text{smor}} \quad\text{Df}\) -/
theorem pm152_01 : (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) = Rfwd smor := rfl

/-- ✱152·02 (Df). \(\text{NR}= \text{D}ʻ\text{Nr} \quad\text{Df}\)

The definiens is the descriptive function `D'Nr` (Basic §5). -/
theorem pm152_02 :
    Desc D (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) (fun K => NR β = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱152·1. \[\begin{align}&\vdash .\text{Nr}ʻP=\hat{Q} (Q\,\text{smor}\,P)=\hat{Q} (P\,\text{smor}\,Q)\\ &[*32·11.(*152·01).*151·14]\end{align}\]

`Nr'P` is `nr γ P`, in an arbitrary type `γ`; the chain is the conjunction of its two links. -/
theorem pm152_1 {P : β → β → Prop} :
    nr γ P = {Q | smor Q P} ∧ {Q : γ → γ → Prop | smor Q P} = {Q | smor P Q} :=
  ⟨rfl, Set.ext fun _ => ⟨smor_symm, smor_symm⟩⟩

/-- ✱152·11. \(\vdash :Q\in \text{Nr}ʻP.\equiv .Q\,\text{smor}\,P.\equiv .P\,\text{smor}\,Q \quad[*152·1]\)

The attributive `Nr'P` is in the type of `Q`. -/
theorem pm152_11 {P : β → β → Prop} {Q : γ → γ → Prop} :
    (Q ∈ nr γ P ↔ smor Q P) ∧ (smor Q P ↔ smor P Q) :=
  ⟨Iff.rfl, ⟨smor_symm, smor_symm⟩⟩

/-- ✱152·2. \(\vdash .\text{E}!\text{Nr}ʻP \quad[*152·1.*14·21]\) -/
theorem pm152_2 {P : β → β → Prop} : EDesc (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) P :=
  EDesc_Nr P

/-- ✱152·21. \(\vdash .\text{ᗡ}ʻ\text{Nr}=\text{Rel} \quad[*152·2.*33·432]\) -/
theorem pm152_21 : codom (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) = Rel := by
  rw [Rel_eq_univ]
  exact Set.eq_univ_of_forall fun P => ⟨nr γ P, rfl⟩

/-- ✱152·22. \(\vdash .\text{Nr}\in 1\rightarrow \text{Cls} \quad[*152·2.*71·166]\) -/
theorem pm152_22 : (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) ∈ arrow one Cls :=
  mem_arrow_one_Cls.2 fun _ _ _ ⟨hx, hy⟩ => hx.trans hy.symm

/-- ✱152·3. \(\vdash .P\in \text{Nr}ʻP \quad[*151·13.*152·11]\) -/
theorem pm152_3 {P : α → α → Prop} : P ∈ nr α P := self_mem_nr P

/-- ✱152·31. \(\vdash :P\in \text{Nr}ʻQ.\equiv .Q\in \text{Nr}ʻP \quad[*152·11]\)

Each attributive `Nr'…` is in the type of its member (cf. ✱100·31). -/
theorem pm152_31 {P : α → α → Prop} {Q : β → β → Prop} : P ∈ nr α Q ↔ Q ∈ nr β P :=
  ⟨smor_symm, smor_symm⟩

/-- ✱152·32. \(\vdash :P\in \text{Nr}ʻQ.Q\in \text{Nr}ʻR.\supset .P\in \text{Nr}ʻR \quad [*151·15.*152·11]\) -/
theorem pm152_32 {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop} :
    P ∈ nr α Q ∧ Q ∈ nr β R → P ∈ nr α R :=
  fun ⟨h1, h2⟩ => smor_trans h1 h2

/-- ✱152·321. \(\vdash :P\,\text{smor}\,Q.\supset .\text{Nr}ʻP=\text{Nr}ʻQ \quad[*151·17.*152·1]\)

The equation is in an arbitrary type `γ`. -/
theorem pm152_321 {P : α → α → Prop} {Q : β → β → Prop} : smor P Q → nr γ P = nr γ Q :=
  nr_eq_nr_of_smor

/-- ✱152·33. \(\vdash :\exists !\text{Nr}ʻP\cap \text{Nr}ʻQ.\supset .P\,\text{smor}\,Q.\text{Nr}ʻP=\text{Nr}ʻQ\)

`Nr'P ∩ Nr'Q` puts both numbers in one type `γ`, as is the equation. -/
theorem pm152_33 {P : α → α → Prop} {Q : β → β → Prop} :
    (nr γ P ∩ nr γ Q).Nonempty → smor P Q ∧ nr γ P = nr γ Q := by
  rintro ⟨R, h1, h2⟩
  have h : smor P Q := smor_trans (smor_symm h1) h2
  exact ⟨h, nr_eq_nr_of_smor h⟩

/-- ✱152·35. \[\begin{align}\vdash \colon\ldotp \exists !&\text{Nr}ʻP.\lor.\exists !\text{Nr}ʻQ:\supset :\\ &\text{Nr}ʻP=\text{Nr}ʻQ.\equiv .P\in \text{Nr}ʻQ.\equiv .Q\in \text{Nr}ʻP.\equiv .P\,\text{smor}\,Q\end{align}\]

As ✱100·35 (PM: "the same remarks as to types are to be made"): the logical and
equational occurrences of `Nr'P`, `Nr'Q` are in one type `γ`, the attributive ones in the
types of `P` and `Q`. The chain of four is the conjunction of its three links.

**Status.** proved (reading): convention IT (Prefatory Statement, IV), as in ✱100·35: the
logical and equational occurrences share the type `γ`, the attributive ones are in the types
of `P` and `Q`. -/
theorem pm152_35 {P : α → α → Prop} {Q : β → β → Prop} :
    (nr γ P).Nonempty ∨ (nr γ Q).Nonempty →
      ((nr γ P = nr γ Q ↔ P ∈ nr α Q) ∧ (P ∈ nr α Q ↔ Q ∈ nr β P)) ∧
        (Q ∈ nr β P ↔ smor P Q) := by
  intro h
  have hPQ : nr γ P = nr γ Q ↔ smor P Q := by
    rcases h with h | h
    · exact nr_eq_nr_iff h
    · rw [eq_comm, nr_eq_nr_iff h]
      exact ⟨smor_symm, smor_symm⟩
  exact ⟨⟨hPQ, ⟨smor_symm, smor_symm⟩⟩, ⟨smor_symm, smor_symm⟩⟩

/-- ✱152·4. \(\vdash :\mu \in \text{NR}.\equiv .(\exists P).\mu =\text{Nr}ʻP \quad[*37·78·79.(*152·02·01)]\)

The apparent variable `P` ranges over the relations of the type `β` of the converse domain
of `Nr` in `NR` (encoding decision 2 of `Defs/Part4`). -/
theorem pm152_4 {μ : Set (γ → γ → Prop)} : μ ∈ NR β ↔ ∃ P : β → β → Prop, μ = nr γ P := Iff.rfl

/-- ✱152·41. \(\vdash .\text{Nr}ʻP\in \text{NR} \quad[*152·4·2]\)

**Status.** proved (reading): the converse domain of `NR` is taken in the type of `P`, as
PM's proof by ✱152·4·2 shows (cf. ✱100·41). -/
theorem pm152_41 {P : β → β → Prop} : nr γ P ∈ NR β := nr_mem_NR P

/-- ✱152·42. \(\vdash :\mu ,\nu \in \text{NR}.\exists !\mu \cap \nu .\supset .\mu =\nu \quad[*152·33·4]\)

`μ, ν ∈ NR` does not identify the converse-domain types of the two `NR`s (cf. ✱100·42);
`μ ∩ ν` puts `μ` and `ν` in one type. -/
theorem pm152_42 {μ ν : Set (γ → γ → Prop)} :
    (μ ∈ NR β ∧ ν ∈ NR δ) ∧ (μ ∩ ν).Nonempty → μ = ν := by
  rintro ⟨⟨⟨P, rfl⟩, ⟨Q, rfl⟩⟩, R, h1, h2⟩
  exact nr_eq_nr_of_smor (smor_trans (smor_symm h1) h2)

/-- ✱152·43. \(\vdash .\text{NR}\in \text{Cls}^{2} \text{excl} \quad[*152·42]\) -/
theorem pm152_43 : (NR β : Set (Set (γ → γ → Prop))) ∈ Cls2excl := by
  rintro μ ν ⟨hμν, hne⟩
  rw [Null_eq_empty]
  by_contra h
  exact hne (pm152_42 ⟨hμν, Set.nonempty_iff_ne_empty.2 h⟩)

/-- ✱152·44. \[\begin{align}&\vdash \colon\ldotp \mu \in \text{NR}:\exists !\mu .\lor.\exists !\text{Nr}ʻP.\supset :P\in \mu .\equiv .\text{Nr}ʻP=\mu \\ &[*152·35·4]\end{align}\]

`P ∈ μ` puts `P` in the type of the members of `μ`; `∃!Nr'P` is bound to the equation
`Nr'P = μ`, in the type of `μ` (convention IT). -/
theorem pm152_44 {μ : Set (γ → γ → Prop)} {P : γ → γ → Prop} :
    μ ∈ NR β ∧ (μ.Nonempty ∨ (nr γ P).Nonempty) → (P ∈ μ ↔ nr γ P = μ) := by
  rintro ⟨⟨Q, rfl⟩, -⟩
  exact ⟨fun h => nr_eq_nr_of_smor h, fun h => h ▸ self_mem_nr P⟩

/-- ✱152·45. \(\vdash :\mu \in \text{NR}.P\in \mu .\supset .\text{Nr}ʻP=\mu \quad[*152·44.*10·24]\) -/
theorem pm152_45 {μ : Set (γ → γ → Prop)} {P : γ → γ → Prop} :
    μ ∈ NR β ∧ P ∈ μ → nr γ P = μ := by
  rintro ⟨⟨Q, rfl⟩, h⟩
  exact nr_eq_nr_of_smor h

/-- ✱152·5. \(\vdash :\mu \in \text{NR}.P,Q\in \mu .\supset .P\,\text{smor}\,Q \quad[*152·31·32·4]\) -/
theorem pm152_5 {μ : Set (γ → γ → Prop)} {P Q : γ → γ → Prop} :
    μ ∈ NR β ∧ (P ∈ μ ∧ Q ∈ μ) → smor P Q := by
  rintro ⟨⟨R, rfl⟩, h1, h2⟩
  exact smor_trans h1 (smor_symm h2)

/-- ✱152·51. \(\vdash :\mu \in \text{NR}.P\in \mu .\supset .\text{smor}ʻʻ\mu =\text{Nr}ʻP\)

`smor''μ` represents in any type the "same" number as `μ`: the equation is in an arbitrary
type `δ` (cf. ✱100·51). -/
theorem pm152_51 {μ : Set (γ → γ → Prop)} {P : γ → γ → Prop} :
    μ ∈ NR β ∧ P ∈ μ → (smor ʻʻ μ : Set (δ → δ → Prop)) = nr δ P := by
  rintro ⟨⟨Q, rfl⟩, hP⟩
  ext R
  constructor
  · rintro ⟨S, hS, hRS⟩
    exact smor_trans hRS (smor_trans hS (smor_symm hP))
  · intro h
    exact ⟨P, hP, h⟩

/-- ✱152·52. \(\vdash :\mu \in \text{NR}.\exists !\mu .\supset .\text{smor}ʻʻ\mu \in \text{NR} \quad[*152·51·4]\)

**Status.** proved (reading): the converse domain of the second `NR` is taken in the type of
the members of `μ`, as PM's proof by ✱152·51·4 (`smor''μ = Nr'P` with `P ∈ μ`) requires
(cf. ✱100·52); the first `NR` has an independent converse-domain type `β`. -/
theorem pm152_52 {μ : Set (γ → γ → Prop)} :
    μ ∈ NR β ∧ μ.Nonempty → (smor ʻʻ μ : Set (δ → δ → Prop)) ∈ NR γ := by
  rintro ⟨hμ, P, hP⟩
  rw [pm152_51 ⟨hμ, hP⟩]
  exact nr_mem_NR P

/-- ✱152·53. \(\vdash :\exists !\text{Nr}ʻQ.\supset .\text{smor}ʻʻ\text{Nr}ʻQ=\text{Nr}ʻQ\)

As ✱100·511: the logical and the argumental occurrences of `Nr'Q` share one type `γ`; the
equational one is in an independent type `δ`.

**Status.** proved (reading): convention IT (Prefatory Statement, IV), as in ✱100·511. -/
theorem pm152_53 {Q : β → β → Prop} :
    (nr γ Q).Nonempty → (smor ʻʻ nr γ Q : Set (δ → δ → Prop)) = nr δ Q := by
  rintro ⟨P, hP⟩
  ext R
  constructor
  · rintro ⟨S, hS, hRS⟩
    exact smor_trans hRS hS
  · intro h
    exact ⟨P, hP, smor_trans h (smor_symm hP)⟩

/-- ✱152·54. \[\begin{align}&\vdash \colon\ldotp \exists !\mu .\exists !\nu .\supset :\mu \in \text{NR}.\nu =\text{smor}ʻʻ\mu .\equiv .\nu \in \text{NR}.\mu =\text{smor}ʻʻ\nu \\ &[\text{Proof as in *100·53}]\end{align}\]

**Status.** proved (reading): as ✱100·53, the converse domain of the `NR` in `μ ∈ NR` is the
type of the members of `ν`, and that of the `NR` in `ν ∈ NR` the type of the members of `μ`,
as PM's proof (by ✱152·52 and its converse) requires. -/
theorem pm152_54 {μ : Set (γ → γ → Prop)} {ν : Set (δ → δ → Prop)} :
    μ.Nonempty ∧ ν.Nonempty → (μ ∈ NR δ ∧ ν = smor ʻʻ μ ↔ ν ∈ NR γ ∧ μ = smor ʻʻ ν) := by
  rintro ⟨hμ, hν⟩
  constructor
  · rintro ⟨hN, rfl⟩
    obtain ⟨Q, rfl⟩ := mem_NR.1 hN
    obtain ⟨P, hP⟩ := hμ
    refine ⟨pm152_52 ⟨hN, P, hP⟩, ?_⟩
    obtain ⟨R, hR⟩ := hν
    rw [pm152_51 ⟨hN, hP⟩] at hR ⊢
    rw [pm152_53 ⟨R, hR⟩]
    exact (nr_eq_nr_of_smor hP).symm
  · rintro ⟨hN, rfl⟩
    obtain ⟨Q, rfl⟩ := mem_NR.1 hN
    obtain ⟨P, hP⟩ := hν
    refine ⟨pm152_52 ⟨hN, P, hP⟩, ?_⟩
    obtain ⟨R, hR⟩ := hμ
    rw [pm152_51 ⟨hN, hP⟩] at hR ⊢
    rw [pm152_53 ⟨R, hR⟩]
    exact (nr_eq_nr_of_smor hP).symm

/-- ✱152·6. \(\vdash .\iota ^{;}P\in \text{Nr}ʻP \quad[*151·61]\)

The attributive `Nr'P` is in the type of `ι;P` (relations on `Set α`). -/
theorem pm152_6 {P : α → α → Prop} : iota ⁏ P ∈ nr (Set α) P := pm151_61

/-- ✱152·62. \(\vdash .x\downarrow ^{;}P\in \text{Nr}ʻP \quad[*151·64]\) -/
theorem pm152_62 {x : γ} {P : α → α → Prop} : coupleL x ⁏ P ∈ nr (γ → α → Prop) P :=
  pm151_64.1

/-- ✱152·63. \(\vdash .\downarrow x^{;}P\in \text{Nr}ʻP \quad[*151·65]\) -/
theorem pm152_63 {x : γ} {P : α → α → Prop} : coupleR x ⁏ P ∈ nr (α → γ → Prop) P :=
  pm151_65.1

/-- ✱152·7. \(\vdash .\text{Nc}ʻCʻQ=Cʻʻ\text{Nr}ʻQ\)

`Nc'C'Q` and `Nr'Q` are in one type (the equation); `C''Nr'Q` is `C ʻʻ nr γ Q`. -/
theorem pm152_7 {Q : β → β → Prop} : nc γ (fld Q) = C ʻʻ nr γ Q := nc_fld_eq

/-- ✱152·71. \(\vdash :\mu \in \text{NR}.\supset .Cʻʻ\mu \in \text{NC} \quad[*152·7]\)

**Status.** proved (reading): the converse domain of `NC` is taken in the type of the fields
of the relations of the converse domain of `NR`, as PM's proof by ✱152·7 requires (with an
independent type the proposition fails, e.g. `NC Empty` contains only `Nc'Λ`). -/
theorem pm152_71 {μ : Set (γ → γ → Prop)} : μ ∈ NR β → C ʻʻ μ ∈ NC β := by
  intro h
  obtain ⟨P, rfl⟩ := mem_NR.1 h
  rw [← nc_fld_eq]
  exact nc_mem_NC _

/-- ✱152·72. \(\vdash .\text{NC}-\iota ʻ\Lambda =Cʻʻʻ(\text{NR}-\iota ʻ\Lambda )\)

`C'''(NR − ι'Λ)` is `C ʻʻʻ (NR β \ ι Λ)`.

**Status.** proved (reading): the converse domains of `NC` and `NR` are taken in one type `β`
(of the members of the fields of the relations), as PM's proof (by ✱152·7 and
`Nr'(I ↾ α)`) requires; with independent types the equation fails when the types differ in
size. -/
theorem pm152_72 :
    (NC β : Set (Set (Set γ))) \ ι Λ = C ʻʻʻ ((NR β : Set (Set (γ → γ → Prop))) \ ι Λ) := by
  ext K
  constructor
  · rintro ⟨hB, hK⟩
    obtain ⟨B, rfl⟩ := mem_NC.1 hB
    have e : nc γ B = C ʻʻ nr γ ((I : β → β → Prop) ↾ B) := by rw [← nc_fld_eq, fld_I_cres]
    refine ⟨nr γ ((I : β → β → Prop) ↾ B), ⟨nr_mem_NR _, fun h => hK ?_⟩, e⟩
    rw [mem_unitCls] at h ⊢
    rw [e, h, Null_eq_empty, Null_eq_empty]
    refine Set.eq_empty_iff_forall_notMem.2 fun X hX => ?_
    obtain ⟨R, hR, -⟩ := hX
    exact hR
  · rintro ⟨μ, ⟨⟨P, rfl⟩, hμ⟩, hK⟩
    have hK' : K = nc γ (fld P) := (hK : K = C ʻʻ nr γ P).trans nc_fld_eq.symm
    subst hK'
    refine ⟨nc_mem_NC _, fun h => hμ ?_⟩
    rw [mem_unitCls] at h ⊢
    rw [Null_eq_empty] at h ⊢
    exact Set.eq_empty_iff_forall_notMem.2 fun R hR =>
      (Set.eq_empty_iff_forall_notMem.1 h) (fld R) (sm_fld_of_smor hR)

/-!
## [✱153] The relation-numbers \(0_{r}\), \(2_{r}\) and \(1_{s}\)

*(Vol. 2, p. 334)*

> *Summary of* *153.
>
> The relation-numbers \(0_{r}\) and \(2_{r}\) have already been defined (in *56), though it remains for the present number to show that they are relation-numbers. They are the ordinal 0 and 2 respectively, *i.e.* they are the ordinal numbers of well-ordered series of no terms and series of two terms respectively. But there is no means of introducing an ordinal 1 which shall be analogous to the cardinal 1 as completely as \(0_{r}\) and \(2_{r}\) are analogous to 0 and 2. The only relations whose fields are unit classes are relations of the form \(x\downarrow x\). We therefore put
>
> *153·01. \(1_{s}=\hat{R} \{(\exists x).R=x\downarrow x\} \quad\text{Df}\)
>
> …

**Lean reading.** `0_r`, `2_r` are `zero_r`, `two_r` (✱56·03·02), `1_s` is `one_s` (✱153·01), `2̇`
is `twoDot`;
`0`, `1`, `2` are `zero`, `one`, `two`. As in ✱101, each occurrence of a typically ambiguous
constant whose type nothing fixes has its own type parameter (✱153·15·17·202·251·27), and
equations are in a free type. `B'P` is a description (`Desc Beg P ψ`), `ῐ'D'P` likewise; `C̆''1`
is `C˘ ʻʻ one`; `Rl'(Cls ↑ Cls)` is `rl (cross Cls Cls)`, `Rel²` is `Rel2`, `t¹¹'z` is
`typ11 z`, `2(z)` is `clsT2 two z`. PM assumes every type has a member; where a proposition
needs it, `[Nonempty _]` is added.

**Status.** proved (all propositions; ✱153·01 definition; ✱153·13 proved (reading): erratum (Vol. I,
p. 218), `Λ̇` for `Λ`; ✱153·22 proved (reading): transcription errors; ✱153·25, ✱153·26,
✱153·262, ✱153·33, ✱153·34 proved (reading): `[Nonempty _]` (✱153·25, ✱153·33 also the
converse-domain type of `NR`); ✱153·27 proved (reading): `Rl'Cls` read `Rl'(Cls ↑ Cls)`, and
`[Nonempty _]`)
-/

/-- ✱153·01 (Df). \(1_{s}=\hat{R}\{(\exists x).R=x\downarrow x\} \quad\text{Df}\) -/
theorem pm153_01 : (one_s : Set (α → α → Prop)) = {R | ∃ x, R = x ↓ x} := rfl

/-- ✱153·1. \(\vdash :P\in 0_{r}.\equiv .P=\dot{\Lambda} \quad[*56·104]\)

`0_r` is `zero_r` (✱56·03). -/
theorem pm153_1 {P : α → β → Prop} : P ∈ (zero_r : Set (α → β → Prop)) ↔ P = rNull := Iff.rfl

/-- ✱153·101. \(\vdash :P\text{smor}\dot{\Lambda} .\equiv .P=\dot{\Lambda}\) -/
theorem pm153_101 {P : α → α → Prop} : smor P (rNull : β → β → Prop) ↔ P = rNull :=
  smor_rNull_iff

/-- ✱153·11. \(\vdash .0_{r}=\text{Nr}ʻ\dot{\Lambda} \quad[*153·1·101.*152·1]\)

The equation is in the type `γ`; the `Λ̇` of `Nr'Λ̇` has an arbitrary type. -/
theorem pm153_11 : (zero_r : Set (γ → γ → Prop)) = nr γ (rNull : β → β → Prop) := by
  ext P
  exact smor_rNull_iff.symm

/-- ✱153·111. \(\vdash .0_{r}\in \text{NR} \quad[*152·41.*153·11]\) -/
theorem pm153_111 : (zero_r : Set (γ → γ → Prop)) ∈ NR β := ⟨rNull, pm153_11⟩

/-- ✱153·12. \(\vdash .\exists !0_{r} \quad[*51·161]\) -/
theorem pm153_12 : (zero_r : Set (α → β → Prop)).Nonempty := ⟨rNull, rfl⟩

/-- ✱153·13. \(\vdash .\exists !0_{r}\cap \text{Rl}ʻR.\Lambda \in 0_{r}\cap \text{Rl}ʻR \quad[*61·3]\)

**Status.** proved (reading): erratum (Vol. I, p. 218): the e-text prints `Λ ∈ 0_r ∩ Rl'R`,
where only `Λ̇` is significant (`0_r ∩ Rl'R` is a class of relations). -/
theorem pm153_13 {R : α → β → Prop} :
    (zero_r ∩ rl R).Nonempty ∧ rNull ∈ zero_r ∩ rl R := by
  have h : rNull ∈ zero_r ∩ rl R := ⟨rfl, fun x y h => absurd h (rNull_apply x y)⟩
  exact ⟨⟨_, h⟩, h⟩

/-- ✱153·14. \(\vdash :\text{Nr}ʻP = 0_{r}. \equiv .P = \dot{\Lambda}\)

The equation is in an arbitrary type `γ`. -/
theorem pm153_14 {P : β → β → Prop} : nr γ P = (zero_r : Set (γ → γ → Prop)) ↔ P = rNull := by
  rw [pm153_11 (β := β)]
  constructor
  · intro e
    have h : (rNull : γ → γ → Prop) ∈ nr γ P := by rw [e]; exact smor_rNull_iff.2 rfl
    exact (smor_rNull_iff.1 (smor_symm h))
  · rintro rfl; rfl

/-- ✱153·15. \(\vdash .\text{smor}ʻʻ0_{r} = 0_{r}\)

The argument `0_r` and the result are in independent types. -/
theorem pm153_15 : (smor ʻʻ (zero_r : Set (α → α → Prop)) : Set (γ → γ → Prop)) = zero_r := by
  rw [pm153_11 (β := α), pm153_11 (β := α)]
  ext R
  constructor
  · rintro ⟨S, hS, hRS⟩
    exact smor_trans hRS hS
  · intro h
    exact ⟨rNull, smor_refl _, h⟩

/-- ✱153·16. \(\vdash \colon\ldotp \mu \in \text{NR}-\iota ʻ0_{r}.\supset :P\in \mu .\supset _{P}.\dot{\exists} !P\) -/
theorem pm153_16 {μ : Set (γ → γ → Prop)} :
    μ ∈ NR β \ ι zero_r → ∀ P, P ∈ μ → rEx P := by
  rintro ⟨⟨Q, rfl⟩, hμ⟩ P hP
  by_contra hne
  have e : P = rNull :=
    rel_ext' fun x y => ⟨fun h => (hne ⟨x, y, h⟩).elim, fun h => absurd h (rNull_apply x y)⟩
  subst e
  have hQ : smor Q (rNull : β → β → Prop) := smor_trans (smor_symm hP) (smor_rNull_iff.2 rfl)
  apply hμ
  rw [mem_unitCls, pm153_11 (β := β)]
  exact nr_eq_nr_of_smor hQ

/-- ✱153·17. \[\begin{align}&\vdash :\dot{\Lambda} \in \text{Nr}ʻP. \equiv .\text{Nr}ʻP = 0_r. \equiv .\text{Nr}ʻP = \text{Nr}ʻ\dot{\Lambda} . \equiv .P = \dot{\Lambda} \\ &[*152·35.*153·11·14]\end{align}\]

As ✱101·17: no logical occurrences, so the attributive `Λ̇ ∈ Nr'P` is in the type `γ₁` of its
`Λ̇`, and each equation is in a type of its own; the chain of four is the conjunction of its
three links. -/
theorem pm153_17 {γ₁ γ₂ γ₃ : Type*} {P : β → β → Prop} :
    (((rNull : γ₁ → γ₁ → Prop) ∈ nr γ₁ P ↔ nr γ₂ P = zero_r) ∧
      (nr γ₂ P = zero_r ↔ nr γ₃ P = nr γ₃ (rNull : δ → δ → Prop))) ∧
      (nr γ₃ P = nr γ₃ (rNull : δ → δ → Prop) ↔ P = rNull) := by
  have e1 : (rNull : γ₁ → γ₁ → Prop) ∈ nr γ₁ P ↔ P = rNull :=
    ⟨fun h => smor_rNull_iff.1 (smor_symm h), fun h => by subst h; exact smor_rNull_iff.2 rfl⟩
  have e3 : nr γ₃ P = nr γ₃ (rNull : δ → δ → Prop) ↔ P = rNull := by
    rw [← pm153_11, pm153_14]
  rw [e1, pm153_14, e3]
  exact ⟨⟨Iff.rfl, Iff.rfl⟩, Iff.rfl⟩

/-- ✱153·18. \(\vdash .Cʻʻ0_{r} = 0\)

`0` is `zero` (✱54·01), in the type of the fields. -/
theorem pm153_18 : C ʻʻ (zero_r : Set (α → α → Prop)) = zero := by
  have hf : fld (rNull : α → α → Prop) = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun x ⟨y, h⟩ => h.elim (rNull_apply _ _) (rNull_apply _ _)
  rw [zero_eq]
  ext A
  constructor
  · rintro ⟨R, hR, hA⟩
    rw [mem_unitCls.1 hR] at hA
    rw [Set.mem_singleton_iff, (hA : A = fld rNull), hf]
  · intro h
    rw [Set.mem_singleton_iff] at h
    exact ⟨rNull, mem_unitCls.2 rfl, (h.trans hf.symm : A = fld rNull)⟩

/-- ✱153·2. \(\vdash :P\in 2_{r}. \equiv .(\exists x,y).x \neq y.P = x\downarrow y \quad[*56·11]\) -/
theorem pm153_2 {P : α → α → Prop} :
    P ∈ (two_r : Set (α → α → Prop)) ↔ ∃ x y, x ≠ y ∧ P = x ↓ y := Iff.rfl

/-- ✱153·201. \(\vdash :x \neq y. \equiv .x\downarrow y\in 2_{r} \quad[*56·17]\) -/
theorem pm153_201 {x y : α} : x ≠ y ↔ x ↓ y ∈ (two_r : Set (α → α → Prop)) := by
  constructor
  · intro h; exact ⟨x, y, h, rfl⟩
  · rintro ⟨a, b, hab, e⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    exact hab

/-- ✱153·202. \(\vdash :P,Q\in 2_{r}.\supset .P \,\text{smor} \,Q \quad[*151·63.*153·2]\)

`P, Q ∈ 2_r` does not identify the types of `P` and `Q`. -/
theorem pm153_202 {P : α → α → Prop} {Q : β → β → Prop} :
    P ∈ (two_r : Set (α → α → Prop)) ∧ Q ∈ (two_r : Set (β → β → Prop)) → smor P Q := by
  rintro ⟨⟨x, y, hxy, rfl⟩, ⟨z, w, hzw, rfl⟩⟩
  exact (pm151_63 ⟨hxy, hzw⟩).1

/-- ✱153·203. \(\vdash :Q\in 2_{r}.P \,\text{smor} \,Q.\supset .P\in 2_{r}\) -/
theorem pm153_203 {P : α → α → Prop} {Q : β → β → Prop} :
    Q ∈ (two_r : Set (β → β → Prop)) ∧ smor P Q → P ∈ (two_r : Set (α → α → Prop)) := by
  rintro ⟨⟨z, w, hzw, rfl⟩, S, ⟨hS, hQ⟩, rfl⟩
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS
  obtain ⟨a, ha⟩ : z ∈ codom S := by
    rw [← hQ]; exact ⟨w, Or.inl ⟨mem_unitCls.2 rfl, mem_unitCls.2 rfl⟩⟩
  obtain ⟨b, hb⟩ : w ∈ codom S := by
    rw [← hQ]; exact ⟨z, Or.inr ⟨mem_unitCls.2 rfl, mem_unitCls.2 rfl⟩⟩
  refine ⟨a, b, fun e => hzw (h2 a z w ⟨ha, e ▸ hb⟩), ?_⟩
  refine rel_ext' fun u v => ?_
  rw [semi_iff]
  constructor
  · rintro ⟨c, d, hc, hd, hcz, hdw⟩
    rw [mem_unitCls.1 hcz] at hc
    rw [mem_unitCls.1 hdw] at hd
    exact ⟨h1 u a z ⟨hc, ha⟩, h1 v b w ⟨hd, hb⟩⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨z, w, ha, hb, mem_unitCls.2 rfl, mem_unitCls.2 rfl⟩

/-- ✱153·21. \(\vdash :P\in 2_{r}.\supset .2_{r} = \text{Nr}ʻP \quad[*153·202·203]\)

The equation is in an arbitrary type `γ`. -/
theorem pm153_21 {P : α → α → Prop} :
    P ∈ (two_r : Set (α → α → Prop)) → (two_r : Set (γ → γ → Prop)) = nr γ P := by
  intro hP
  ext R
  exact ⟨fun h => pm153_202 ⟨h, hP⟩, fun h => pm153_203 ⟨hP, h⟩⟩

/-- ✱153·211. \(\vdash :x \neq y.\supset .2_{r} = \text{Nr}ʻ(x\downarrow y) \quad[*153·21·201]\) -/
theorem pm153_211 {x y : α} : x ≠ y → (two_r : Set (γ → γ → Prop)) = nr γ (x ↓ y) :=
  fun h => pm153_21 (pm153_201.1 h)

/-- ✱153·212. \(\vdash .Cʻʻ2_{r} = 2 \quad[*55·15.*56·11.*54·101]\)

`2` is `two` (✱54·02), in the type of the fields. -/
theorem pm153_212 : C ʻʻ (two_r : Set (α → α → Prop)) = two := by
  ext A
  constructor
  · rintro ⟨R, ⟨x, y, hxy, rfl⟩, rfl⟩
    refine ⟨x, y, hxy, ?_⟩
    rsimp
    grind
  · rintro ⟨x, y, hxy, rfl⟩
    refine ⟨x ↓ y, ⟨x, y, hxy, rfl⟩, ?_⟩
    rsimp
    grind

/-- ✱153·22. \(\vdash :\exists !2_{r}\cap t''ʻz.\equiv .\exists !2(z).\equiv .(\exists x,y).x\neq yx\in tʻz \quad[*153·211.*101·4]\)

`t''z` is read `t¹¹'z` (`typ11 z`, ✱64·011), `2(z)` is `2 ∩ t't'z` (✱65·02, `clsT2 two z`).

**Status.** proved (reading): transcription error: the e-text prints `t''ʻz` for `t¹¹ʻz` and
`x\neq yx\in tʻz` for `x ≠ y . x, y ∈ t'z`. -/
theorem pm153_22 {z : α} :
    ((two_r ∩ typ11 z).Nonempty ↔ (clsT2 two z).Nonempty) ∧
      ((clsT2 two z).Nonempty ↔ ∃ x y, x ≠ y ∧ (x ∈ typ z ∧ y ∈ typ z)) := by
  rw [clsT2_eq'', show typ11 z = Set.univ from typ_eq_univ _, Set.inter_univ]
  refine ⟨⟨fun ⟨_, x, y, h, _⟩ => ⟨ι x ∪ ι y, x, y, h, rfl⟩,
    fun ⟨_, x, y, h, _⟩ => ⟨x ↓ y, x, y, h, rfl⟩⟩, ?_⟩
  exact ⟨fun ⟨_, x, y, h, _⟩ => ⟨x, y, h, mem_typ' z x, mem_typ' z y⟩,
    fun ⟨x, y, h, _⟩ => ⟨ι x ∪ ι y, x, y, h, rfl⟩⟩

/-- ✱153·23. \(\vdash :P\in 2_{r}.\supset .\text{Rl}ʻP\subset 0_{r}\cup 2_{r} \quad[*56·261]\)

`Rl'P` is `rl P`. -/
theorem pm153_23 {P : α → α → Prop} :
    P ∈ (two_r : Set (α → α → Prop)) → rl P ⊆ zero_r ∪ two_r := by
  rintro ⟨x, y, hxy, rfl⟩ R hR
  by_cases h : R x y
  · right
    refine ⟨x, y, hxy, rel_ext' fun u v => ⟨fun huv => hR u v huv, ?_⟩⟩
    rintro ⟨rfl, rfl⟩
    exact h
  · left
    show R = rNull
    exact rel_ext' fun u v => ⟨fun huv => by
      obtain ⟨rfl, rfl⟩ := hR u v huv
      exact absurd huv h, fun h' => absurd h' (rNull_apply u v)⟩

/-- ✱153·24. \(\vdash .2_{r}=\text{Nr}ʻ(\Lambda \downarrow \iota ʻx) \quad[*153·211.*51·161]\)

`Λ ↓ ι'x` is a couple of classes (`x` of any type `α`); the equation is in the type `γ`. -/
theorem pm153_24 {x : α} : (two_r : Set (γ → γ → Prop)) = nr γ ((Λ : Set α) ↓ ι x) := by
  refine pm153_211 fun h => ?_
  have : x ∈ (Λ : Set α) := by rw [h]; exact mem_unitCls.2 rfl
  rw [Null_eq_empty] at this
  exact this

/-- ✱153·25. \(\vdash .2_{r}\in \text{NR} \quad[*153·24.*152·41]\)

**Status.** proved (reading): as ✱101·32, the converse domain of `NR` is taken in a type of
classes `Set α` (PM's proof is by ✱153·24, `2_r = Nr'(Λ ↓ ι'x)`), with `[Nonempty α]` since PM
assumes every type has a member (Introduction, Ch. I). -/
theorem pm153_25 [Nonempty α] : (two_r : Set (γ → γ → Prop)) ∈ NR (Set α) :=
  let ⟨x⟩ := ‹Nonempty α›
  ⟨_, pm153_24 (x := x)⟩

/-- ✱153·251. \(\vdash .2_{r}\neq 0_{r}.2_{r}\cap 0_{r}=\Lambda\)

The two propositions are in independent types `α`, `β`. -/
theorem pm153_251 :
    (two_r : Set (α → α → Prop)) ≠ zero_r ∧ (two_r ∩ zero_r : Set (β → β → Prop)) = Λ := by
  refine ⟨fun e => two_r_not_zero_r (R := rNull) (by rw [e]; exact mem_unitCls.2 rfl)
    (mem_unitCls.2 rfl), ?_⟩
  rw [Null_eq_empty]
  exact Set.eq_empty_iff_forall_notMem.2 fun R ⟨h1, h2⟩ => two_r_not_zero_r h1 h2

/-- ✱153·26. \(\vdash .\exists !2_{r}\cap \text{Rl}ʻ(\text{Cls}\uparrow \text{Cls}) \quad[*153·24.*152·3]\)

`Rl'(Cls ↑ Cls)` is `rl (cross Cls Cls)`, the relations between classes of `α`-things.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the
proof uses `Λ ↓ ι'x`): `[Nonempty α]`. -/
theorem pm153_26 [Nonempty α] :
    (two_r ∩ rl (cross (Cls : Set (Set α)) (Cls : Set (Set α)))).Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty α›
  refine ⟨(Λ : Set α) ↓ ι x, (pm153_201 (α := Set α)).1 fun h => ?_, fun _ _ _ =>
    ⟨by rw [Cls_eq_univ]; trivial, by rw [Cls_eq_univ]; trivial⟩⟩
  have : x ∈ (Λ : Set α) := by rw [h]; exact mem_unitCls.2 rfl
  rw [Null_eq_empty] at this
  exact this

/-- ✱153·261. \(\vdash .\dot{\Lambda} \downarrow (x\downarrow x)\in 2_{r} \quad[*55·134.*56·11]\) -/
theorem pm153_261 {x : α} : (rNull : α → α → Prop) ↓ (x ↓ x) ∈ two_r := by
  refine (pm153_201).1 fun h => ?_
  exact rNull_apply x x (by rw [h]; exact ⟨mem_unitCls.2 rfl, mem_unitCls.2 rfl⟩)

/-- ✱153·262. \(\vdash .\exists !2_{r}\cap \text{Rel}^{2} \quad[*153·261.(*61·03)]\)

`Rel²` is `Rel2` (✱61·03).

**Status.** proved (reading): PM assumes every type has a member (the proof uses
`Λ̇ ↓ (x ↓ y)`): `[Nonempty α]`, `[Nonempty β]`. -/
theorem pm153_262 [Nonempty α] [Nonempty β] :
    (two_r ∩ (Rel2 : Set ((α → β → Prop) → (α → β → Prop) → Prop))).Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty α›
  obtain ⟨y⟩ := ‹Nonempty β›
  refine ⟨(rNull : α → β → Prop) ↓ (x ↓ y), (pm153_201).1 fun h => ?_, fun _ _ _ =>
    ⟨by rw [Rel_eq_univ]; trivial, by rw [Rel_eq_univ]; trivial⟩⟩
  exact rNull_apply x y (by rw [h]; exact ⟨mem_unitCls.2 rfl, mem_unitCls.2 rfl⟩)

/-- ✱153·27. \[\begin{align}&\vdash .2_r=\text{smor}ʻʻ(2_r\cap \text{Rl}ʻ\text{Cls})=\text{smor}ʻʻ(2_r\cap \text{Rel}^2)\\ &[*152·53.*153·26·262·24]\end{align}\]

`Rl'Cls` is read `Rl'(Cls ↑ Cls)` (as in ✱153·26, which PM cites); the arguments of
`smor''` are in their own types, the equations in the type `γ`.

**Status.** proved (reading): `Rl'Cls` (not significant, `Cls` being a class) is read
`Rl'(Cls ↑ Cls)`, as in ✱153·26 cited in the proof; `[Nonempty α]`, `[Nonempty δ]`,
`[Nonempty ε]` (PM assumes every type has a member). -/
theorem pm153_27 [Nonempty α] [Nonempty δ] [Nonempty ε] :
    (two_r : Set (γ → γ → Prop)) =
        smor ʻʻ (two_r ∩ rl (cross (Cls : Set (Set α)) (Cls : Set (Set α)))) ∧
      (smor ʻʻ (two_r ∩ rl (cross (Cls : Set (Set α)) (Cls : Set (Set α)))) :
          Set (γ → γ → Prop)) =
        smor ʻʻ (two_r ∩ (Rel2 : Set ((δ → ε → Prop) → (δ → ε → Prop) → Prop))) := by
  have key1 : (smor ʻʻ (two_r ∩ rl (cross (Cls : Set (Set α)) (Cls : Set (Set α)))) :
      Set (γ → γ → Prop)) = two_r := by
    obtain ⟨P, hP⟩ := pm153_26 (α := α)
    ext R
    constructor
    · rintro ⟨S, hS, hRS⟩; exact pm153_203 ⟨hS.1, hRS⟩
    · intro h; exact ⟨P, hP, pm153_202 ⟨h, hP.1⟩⟩
  have key2 : (smor ʻʻ (two_r ∩ (Rel2 : Set ((δ → ε → Prop) → (δ → ε → Prop) → Prop))) :
      Set (γ → γ → Prop)) = two_r := by
    obtain ⟨P, hP⟩ := pm153_262 (α := δ) (β := ε)
    ext R
    constructor
    · rintro ⟨S, hS, hRS⟩; exact pm153_203 ⟨hS.1, hRS⟩
    · intro h; exact ⟨P, hP, pm153_202 ⟨h, hP.1⟩⟩
  rw [key1, key2]
  exact ⟨rfl, rfl⟩

/-- ✱153·28. \(\vdash :x\neq y.\supset .Bʻ(x\downarrow y)=x.Bʻ\text{Cnv}ʻ(x\downarrow y)=y\)

`B'(x ↓ y)` is a description (`Desc Beg (x ↓ y) ψ`); `Cnv'(x ↓ y)` is `(x ↓ y)˘`. -/
theorem pm153_28 {x y : α} :
    x ≠ y → Desc Beg (x ↓ y) (fun b => b = x) ∧ Desc Beg (x ↓ y)˘ (fun b => b = y) := by
  intro h
  refine ⟨TheIs_iff_of_unique (b := x) (fun u => ?_) |>.2 rfl,
    TheIs_iff_of_unique (b := y) (fun u => ?_) |>.2 rfl⟩
  · rsimp
    grind
  · rsimp
    grind

/-- ✱153·281. \(\vdash :P\in 2_{r}.\supset .BʻP=\breve{\iota} ʻ\text{D}ʻP.Bʻ\breve{P} =\breve{\iota} ʻ\text{ᗡ}ʻP \quad[*153·28.*55·15]\)

`B'P = ῐ'D'P` has two descriptions, `B'P` with the larger scope. -/
theorem pm153_281 {P : α → α → Prop} :
    P ∈ (two_r : Set (α → α → Prop)) →
      Desc Beg P (fun b => Desc iota˘ (dom P) (fun c => b = c)) ∧
        Desc Beg P˘ (fun b => Desc iota˘ (codom P) (fun c => b = c)) := by
  rintro ⟨x, y, hxy, rfl⟩
  have hd : dom (x ↓ y) = ι x := by rsimp; grind
  have hc : codom (x ↓ y) = ι y := by rsimp; grind
  have hι : ∀ a : α, ∀ u, iota˘ u (ι a) ↔ u = a :=
    fun a u => ⟨fun hu => unitCls_injective (hu : ι a = ι u).symm, fun e => by subst e; rfl⟩
  obtain ⟨h1, h2⟩ := pm153_28 hxy
  rw [hd, hc]
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb, hbx⟩ := h1
    exact ⟨b, hb, by rw [hbx]; exact (TheIs_iff_of_unique (hι x)).2 rfl⟩
  · obtain ⟨b, hb, hby⟩ := h2
    exact ⟨b, hb, by rw [hby]; exact (TheIs_iff_of_unique (hι y)).2 rfl⟩

/-- ✱153·3. \(\vdash .1_{s}=\dot{2} -2_{r}=\hat{R} \{(\exists x).R=x\downarrow x\} \quad[*56·13.(*153·01)]\)

`2̇ − 2_r` is `twoDot \ two_r` (✱56·01·02); the chain is the conjunction of its two links. -/
theorem pm153_3 :
    (one_s : Set (α → α → Prop)) = twoDot \ two_r ∧
      (twoDot \ two_r : Set (α → α → Prop)) = {R | ∃ x, R = x ↓ x} := by
  have h : (twoDot \ two_r : Set (α → α → Prop)) = {R | ∃ x, R = x ↓ x} := by
    ext R
    constructor
    · rintro ⟨⟨x, y, rfl⟩, h⟩
      refine ⟨x, ?_⟩
      by_cases hxy : x = y
      · rw [hxy]
      · exact absurd ⟨x, y, hxy, rfl⟩ h
    · rintro ⟨x, rfl⟩
      refine ⟨⟨x, x, rfl⟩, ?_⟩
      rintro ⟨a, b, hab, e⟩
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
      exact hab rfl
  exact ⟨h.symm, h⟩

/-- ✱153·301. \(\vdash .1_{s}=\breve{C} ʻʻ1 \quad[*153·3.*56·39]\)

`C̆''1` is `C˘ ʻʻ one`. -/
theorem pm153_301 : (one_s : Set (α → α → Prop)) = C˘ ʻʻ one := by
  ext R
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨ι x, ⟨x, rfl⟩, ?_⟩
    show ι x = fld (x ↓ x)
    rsimp
    grind
  · rintro ⟨A, ⟨x, rfl⟩, hA⟩
    have hA' : ι x = fld R := hA
    refine ⟨x, rel_ext' fun u v => ⟨fun h => ?_, ?_⟩⟩
    · have hu : u ∈ ι x := by rw [hA']; exact ⟨v, Or.inl h⟩
      have hv : v ∈ ι x := by rw [hA']; exact ⟨u, Or.inr h⟩
      exact ⟨hu, hv⟩
    · intro huv
      rw [mem_unitCls.1 huv.1, mem_unitCls.1 huv.2]
      obtain ⟨w, hw | hw⟩ : x ∈ fld R := by rw [← hA']; exact mem_unitCls.2 rfl
      · have : w ∈ ι x := by rw [hA']; exact ⟨x, Or.inr hw⟩
        rwa [mem_unitCls.1 this] at hw
      · have : w ∈ ι x := by rw [hA']; exact ⟨x, Or.inl hw⟩
        rwa [mem_unitCls.1 this] at hw

/-- ✱153·31. \(\vdash .x\downarrow y\in (x\downarrow x)\overline{\text{smor}} (y\downarrow y)\) -/
theorem pm153_31 {x : α} {y : β} : x ↓ y ∈ smorbar (x ↓ x) (y ↓ y) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rsimp <;> grind

/-- ✱153·311. \(\vdash :Q\in 1_{s}.P\,\text{smor}\,Q.\supset .P\in 1_{s}\) -/
theorem pm153_311 {P : α → α → Prop} {Q : β → β → Prop} :
    Q ∈ (one_s : Set (β → β → Prop)) ∧ smor P Q → P ∈ (one_s : Set (α → α → Prop)) := by
  rintro ⟨⟨y, rfl⟩, S, ⟨hS, hQ⟩, rfl⟩
  obtain ⟨x, hx⟩ : y ∈ codom S := by
    rw [← hQ]; exact ⟨y, Or.inl ⟨mem_unitCls.2 rfl, mem_unitCls.2 rfl⟩⟩
  obtain ⟨h1, -⟩ := mem_arrow_one_one.1 hS
  refine ⟨x, rel_ext' fun u v => ?_⟩
  rw [semi_iff]
  constructor
  · rintro ⟨c, d, hc, hd, hcy, hdy⟩
    rw [mem_unitCls.1 hcy] at hc
    rw [mem_unitCls.1 hdy] at hd
    exact ⟨h1 u x y ⟨hc, hx⟩, h1 v x y ⟨hd, hx⟩⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨y, y, hx, hx, mem_unitCls.2 rfl, mem_unitCls.2 rfl⟩

/-- ✱153·32. \(\vdash .1_{s}=\text{Nr}ʻ(y\downarrow y) \quad[*153·31·311]\)

The equation is in the type `γ`; `y` has an arbitrary type. -/
theorem pm153_32 {y : β} : (one_s : Set (γ → γ → Prop)) = nr γ (y ↓ y) := by
  ext R
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, pm153_31⟩
  · intro h
    exact pm153_311 ⟨⟨y, rfl⟩, h⟩

/-- ✱153·33. \(\vdash .1_{s}\in \text{NR} \quad[*153·32]\)

**Status.** proved (reading): the converse domain of `NR` is taken in a type `β` with a
member (PM's proof is by ✱153·32, `1_s = Nr'(y ↓ y)`): `[Nonempty β]` (PM assumes every type
has a member). -/
theorem pm153_33 [Nonempty β] : (one_s : Set (γ → γ → Prop)) ∈ NR β :=
  let ⟨y⟩ := ‹Nonempty β›
  ⟨_, pm153_32 (y := y)⟩

/-- ✱153·34. \(\vdash .\exists !1_{s}.1_{s}\neq 0_{r}.1_{s}\neq 2_{r}.1_{s}\cap 0_{r}=\Lambda .1_{s}\cap 2_{r}=\Lambda\)

The conclusion is a product of five, bracketed to the left, in one type `α`.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty α]` (in an empty type `1_s = 2_r = Λ`). -/
theorem pm153_34 [Nonempty α] :
    (((((one_s : Set (α → α → Prop)).Nonempty ∧ (one_s : Set (α → α → Prop)) ≠ zero_r) ∧
        (one_s : Set (α → α → Prop)) ≠ two_r) ∧ (one_s ∩ zero_r : Set (α → α → Prop)) = Λ) ∧
      (one_s ∩ two_r : Set (α → α → Prop)) = Λ) := by
  obtain ⟨x⟩ := ‹Nonempty α›
  have h1 : (x ↓ x : α → α → Prop) ∈ one_s := ⟨x, rfl⟩
  have h0 : ∀ R : α → α → Prop, R ∈ one_s → R ∉ zero_r := by
    rintro R ⟨y, rfl⟩ h
    apply rNull_apply y y
    rw [← (mem_unitCls.1 h : y ↓ y = rNull)]
    exact ⟨mem_unitCls.2 rfl, mem_unitCls.2 rfl⟩
  have h2 : ∀ R : α → α → Prop, R ∈ one_s → R ∉ two_r := by
    rintro R ⟨y, rfl⟩ h
    exact (pm153_201.2 h) rfl
  refine ⟨⟨⟨⟨⟨_, h1⟩, fun e => h0 _ h1 (e ▸ h1)⟩, fun e => h2 _ h1 (e ▸ h1)⟩, ?_⟩, ?_⟩
  · rw [Null_eq_empty]
    exact Set.eq_empty_iff_forall_notMem.2 fun R ⟨hR1, hR2⟩ => h0 R hR1 hR2
  · rw [Null_eq_empty]
    exact Set.eq_empty_iff_forall_notMem.2 fun R ⟨hR1, hR2⟩ => h2 R hR1 hR2

/-- ✱153·341. \(\vdash :R\in 1_{s}.\equiv .\text{Nr}ʻR=1_{s} \quad[*153·33·34.*152·44]\)

`R ∈ 1_s` puts `1_s` in the type of `R`, and `Nr'R = 1_s` is in that type. -/
theorem pm153_341 {R : α → α → Prop} : R ∈ (one_s : Set (α → α → Prop)) ↔ nr α R = one_s := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (pm153_32).symm
  · intro e
    rw [← e]
    exact self_mem_nr R

/-- ✱153·35. \(\vdash :R\in 1_{s}.\supset .\text{Nc}ʻCʻR=Cʻʻ\text{Nr}ʻR=1\)

The chain is the conjunction of its two links, in one type `γ`. -/
theorem pm153_35 {R : α → α → Prop} :
    R ∈ (one_s : Set (α → α → Prop)) →
      nc γ (fld R) = C ʻʻ nr γ R ∧ C ʻʻ nr γ R = (one : Set (Set γ)) := by
  rintro ⟨x, rfl⟩
  refine ⟨nc_fld_eq, ?_⟩
  rw [← nc_fld_eq]
  have : fld (x ↓ x) = ι x := by rsimp; grind
  rw [this]
  ext B
  exact sm_unit_iff'

/-- ✱153·36. \(\vdash .Cʻʻ1_{s}=1\) -/
theorem pm153_36 : C ʻʻ (one_s : Set (α → α → Prop)) = one := by
  ext A
  constructor
  · rintro ⟨R, ⟨x, rfl⟩, rfl⟩
    refine ⟨x, ?_⟩
    rsimp
    grind
  · rintro ⟨x, rfl⟩
    refine ⟨x ↓ x, ⟨x, rfl⟩, ?_⟩
    show ι x = fld (x ↓ x)
    rsimp
    grind

/-!
## [✱154] Relation-numbers of assigned types

*(Vol. 2, p. 339)*

> *Summary of* *154.
>
> This number gives propositions analogous to those of *102. In accordance with our general notations for typical definiteness, "\(\text{Nr}(P)ʻQ\)" means "the class of relations like \(Q\) and of the same type as \(P\)," "\(\text{Nr} (P_{Q})\)" means "the relation to a relation of the type of \(Q\) of the class of relations like it and of the type of \(P\)." By a special definition, "\(\text{NR}^{Q}(P)\)" is to mean all typically definite relation-numbers of the form "\(\text{Nr}(P_{Q})ʻR\)," *i.e.* all relation-numbers generated by the relation \(\text{Nr}(P_{Q})\), *i.e.* the domain of \(\text{Nr}(P_{Q})\).
>
> Existence-theorems in this subject can be proved by means of *154·14, which states that relations like \(Q\) exist in the type of \(P\) when, and only when, classes similar to \(CʻQ\) exist in the type of \(CʻP\). In virtue of this proposition, the existence-theorems of our present topic are deducible from those for cardinals. In symbols, this proposition is
>
> *154·14. \(\vdash :\exists !\text{Nr}(P)ʻQ.\equiv .\exists !\text{Nc}(CʻP)ʻCʻQ\)
>
> Hence by *102·73 we deduce
>
> *154·242. \(\vdash . \Lambda \in \text{NR}^{\iota ^{;}P}(P)\)
>
> whence, by *152·72,
>
> …

**Lean reading.** As ✱102: the typically definite relations of ✱65 are explicit: `Nr(X)` is `relT2
Nr X`
(✱65·04), `Nr(X_Y)` is `relT2T Nr X Y` (✱65·11), `smor_{(X,Y)}` is `relTT smor X Y`, `smor_Y` is
`relT smor Y`, `Nc(C'P)` is `relT2 Nc (fld P)`, `NR^Y(X)` is `NRT X Y` (= `NR β`, `NRT_eq_NR`),
`NC^{C'Q}(C'P)` is `NCT (fld P) (fld Q)`. Their descriptive functions are kept as descriptions,
with the smallest scopes. The relative types `t'P`, `t'C'P`, `t₀'C'P`, `t₀₀'C'P`, `t¹¹'C'P`,
`t²'C'Q` are `typ P`, `typ (fld P)`, `typ₀ (fld P)`, `typ₀₀ (fld P)`, `typ11 (fld P)`,
`typ2 (fld Q)`, each `Set.univ` of its Lean type: the typing propositions (✱154·121·31·32·322·33)
hold by `typ_eq_univ`, and hypotheses `∈ t'…` fix the Lean types. `Nc'α ≥ Nc'C'Q` is normally
adjusted (`n₀c A ≥ᶜ n₀c (fld Q)`, ✱117). The non-existence theorems ✱154·24·25 are Cantor's
theorem.

**Status.** proved (all propositions; ✱154·01 definition; ✱154·23 proved (reading): transcription
error;
✱154·262 proved (reading): `C'P ∈ t₀₀'C'Q` read `C'P ∈ t't₀₀'C'Q`; ✱154·311, ✱154·321 proved
(reading): `Nr(σ)` with a class `σ` read `Nr_σ` (✱65·03); ✱154·331 proved (reading): the same,
and a transcription error; ✱154·9 proved (reading): the converse-domain types of `NC` and
`NR`)
-/

/-- ✱154·01 (Df). \(\text{NR}^{Y}(X) = \text{D}ʻ\text{Nr}(X_{Y}) \quad\text{Df}\)

`Nr(X_Y)` is ✱65·11 `relT2T Nr X Y`; the definiens is a descriptive function (Basic §5). -/
theorem pm154_01 {X : γ → γ → Prop} {Y : β → β → Prop} :
    Desc D (relT2T (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) X Y) (fun K => NRT X Y = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱154·1. \(\vdash : \exists ! \text{Rl}ʻP \cap \text{Nr}ʻQ . \supset . \exists ! \text{Cl}ʻCʻP \cap \text{Nc}ʻCʻQ\)

`Rl'P ∩ Nr'Q` puts `Nr'Q` in the type of `P`; `Cl'C'P ∩ Nc'C'Q` puts `Nc'C'Q` in that of
`C'P`. -/
theorem pm154_1 {P : α → α → Prop} {Q : β → β → Prop} :
    (rl P ∩ nr α Q).Nonempty → (cl (fld P) ∩ nc α (fld Q)).Nonempty := by
  rintro ⟨R, hRP, hRQ⟩
  exact ⟨fld R, fld_mono hRP, sm_fld_of_smor hRQ⟩

/-- ✱154·11. \(\vdash :\exists !\text{Cl}ʻCʻP\cap \text{Nc}ʻCʻQ.\supset .(\exists R).R\,\text{smor}\,Q.CʻR\subset CʻP\) -/
theorem pm154_11 {P : α → α → Prop} {Q : β → β → Prop} :
    (cl (fld P) ∩ nc α (fld Q)).Nonempty → ∃ R : α → α → Prop, smor R Q ∧ fld R ⊆ fld P := by
  rintro ⟨X, hX, hXQ⟩
  obtain ⟨R, hR, hRQ⟩ := exists_smor_fld hXQ
  exact ⟨R, hRQ, hR ▸ hX⟩

/-- ✱154·12. \(\vdash :\exists !\text{Rl}ʻ(\alpha \uparrow \alpha )\cap \text{Nr}ʻQ.\equiv .\exists !\text{Cl}ʻ\alpha \cap \text{Nc}ʻCʻQ.\equiv .\text{Nc}ʻ\alpha \geq \text{Nc}ʻCʻQ\)

`α ↑ α` is `cross A A`; the sides of `≥` are normally adjusted (✱117·02·03 and the note after
✱117·06): `Nc'α ≥ Nc'C'Q` is `n₀c A ≥ᶜ n₀c (fld Q)`. The chain is the conjunction of its links. -/
theorem pm154_12 {A : Set α} {Q : β → β → Prop} :
    ((rl (cross A A) ∩ nr α Q).Nonempty ↔ (cl A ∩ nc α (fld Q)).Nonempty) ∧
      ((cl A ∩ nc α (fld Q)).Nonempty ↔ n₀c A ≥ᶜ n₀c (fld Q)) := by
  refine ⟨⟨?_, ?_⟩, n₀c_ge_iff.symm⟩
  · rintro ⟨R, hRA, hRQ⟩
    refine ⟨fld R, ?_, sm_fld_of_smor hRQ⟩
    rintro x ⟨y, h | h⟩
    · exact (hRA x y h).1
    · exact (hRA y x h).2
  · rintro ⟨X, hXA, hXQ⟩
    obtain ⟨R, hR, hRQ⟩ := exists_smor_fld hXQ
    refine ⟨R, fun x y h => ⟨hXA ?_, hXA ?_⟩, hRQ⟩
    · rw [← hR]; exact ⟨y, Or.inl h⟩
    · rw [← hR]; exact ⟨x, Or.inr h⟩

/-- ✱154·121. \(\vdash .\text{Rl}ʻ(t_{0}ʻCʻP\uparrow t_{0}ʻCʻP)=tʻP=t_{00}ʻCʻP\)

The relative types of ✱63–✱64 are `Set.univ` of their Lean types (`typ_eq_univ`); the chain is
the conjunction of its two links. -/
theorem pm154_121 {P : α → α → Prop} :
    rl (cross (typ₀ (fld P)) (typ₀ (fld P))) = typ P ∧ typ P = typ₀₀ (fld P) := by
  have h1 : rl (cross (typ₀ (fld P)) (typ₀ (fld P))) = Set.univ :=
    Set.eq_univ_of_forall fun R x y _ =>
      ⟨by rw [typ₀_eq_univ]; trivial, by rw [typ₀_eq_univ]; trivial⟩
  exact ⟨h1.trans (typ_eq_univ P).symm, (typ_eq_univ P).trans (typ_eq_univ _).symm⟩

/-- ✱154·13. \(\vdash :\exists !tʻP\cap \text{Nr}ʻQ.\equiv .\exists !tʻCʻP\cap \text{Nc}ʻCʻQ.\equiv .\text{Nc}ʻt_{0}ʻCʻP\geq \text{Nc}ʻCʻQ\)

`t'C'P` is `typ (fld P)` (the classes of the type of `C'P`), `t₀'C'P` is `typ₀ (fld P)`. -/
theorem pm154_13 {P : α → α → Prop} {Q : β → β → Prop} :
    ((typ P ∩ nr α Q).Nonempty ↔ (typ (fld P) ∩ nc α (fld Q)).Nonempty) ∧
      ((typ (fld P) ∩ nc α (fld Q)).Nonempty ↔ n₀c (typ₀ (fld P)) ≥ᶜ n₀c (fld Q)) := by
  have hc : cl (typ₀ (fld P)) = typ (fld P) := by
    rw [typ₀_eq_univ, typ_eq_univ]
    exact Set.eq_univ_of_forall fun _ => Set.subset_univ _
  rw [n₀c_ge_iff, hc]
  refine ⟨?_, Iff.rfl⟩
  rw [typ_eq_univ, typ_eq_univ, Set.univ_inter, Set.univ_inter, nr_nonempty_iff, nc_nonempty_iff]

/-- ✱154·14. \(\vdash :\exists !\text{Nr}(P)ʻQ.\equiv .\exists !\text{Nc}(CʻP)ʻCʻQ \quad[*154·13.(*65·04)]\)

`Nr(P)` is ✱65·04 `relT2 Nr P`, `Nc(C'P)` is `relT2 Nc (fld P)`; both descriptions exist. -/
theorem pm154_14 {P : γ → γ → Prop} {Q : β → β → Prop} :
    Desc (relT2 Nr P) Q (fun μ => μ.Nonempty) ↔
      Desc (relT2 Nc (fld P)) (fld Q) (fun μ => μ.Nonempty) := by
  rw [desc_relT2_Nr, desc_relT2_Nc'', nr_nonempty_iff, nc_nonempty_iff]

/-- ✱154·2. \(\vdash .\text{Nr}(X_{Y})ʻQ=\hat{P} \{P\text{smor}_{(X,Y)}Q\} \quad[*65·2.(*152·01)]\)

`smor_{(X,Y)}` is ✱65·1 `relTT smor X Y`. -/
theorem pm154_2 {X : γ → γ → Prop} {Y Q : β → β → Prop} :
    Desc (relT2T Nr X Y) Q (fun μ => μ = {P | relTT smor X Y P Q}) := by
  rw [desc_relT2T_Nr, relTT_eq]
  rfl

/-- ✱154·201. \(\vdash .\text{Nr}(X)ʻQ=\text{Nr}ʻQ\cap tʻX \quad[\text{Proof as in *102·6}]\)

`Nr'Q ∩ t'X` puts `Nr'Q` in the type of `X`. -/
theorem pm154_201 {X : γ → γ → Prop} {Q : β → β → Prop} :
    Desc (relT2 Nr X) Q (fun μ => μ = nr γ Q ∩ typ X) := by
  rw [desc_relT2_Nr, typ_eq_univ, Set.inter_univ]

/-- ✱154·202. \[\begin{align}&\vdash :P\in \text{Nr}(X_{Y})ʻQ.\equiv .P\in \text{Nr}(X)ʻQ.Q\in tʻY.\equiv .\\ &P\in \text{Nr}ʻQ.P\in tʻX.Q\in tʻY \quad[*152·2·201. (*65·1)]\end{align}\]

The chain of three is the conjunction of its two links; products bracket to the left. -/
theorem pm154_202 {X P : γ → γ → Prop} {Y Q : β → β → Prop} :
    (Desc (relT2T Nr X Y) Q (fun μ => P ∈ μ) ↔ Desc (relT2 Nr X) Q (fun μ => P ∈ μ) ∧ Q ∈ typ Y) ∧
      (Desc (relT2 Nr X) Q (fun μ => P ∈ μ) ∧ Q ∈ typ Y ↔
        (P ∈ nr γ Q ∧ P ∈ typ X) ∧ Q ∈ typ Y) := by
  rw [desc_relT2T_Nr, desc_relT2_Nr]
  simp only [typ_eq_univ, Set.mem_univ, and_true, iff_self, and_self]

/-- ✱154·203. \(\vdash :Q\in tʻY.\supset .\text{Nr}(X_{Y})ʻQ=\text{Nr}(X)ʻQ \quad[*154·202]\) -/
theorem pm154_203 {X : γ → γ → Prop} {Y Q : β → β → Prop} :
    Q ∈ typ Y → Desc (relT2T Nr X Y) Q (fun μ => Desc (relT2 Nr X) Q (fun ν => μ = ν)) := by
  intro _
  rw [desc_relT2T_Nr, desc_relT2_Nr]

/-- ✱154·21. \(\vdash .\text{NR}^{Y}(X)=\hat{\lambda} \{(\exists Q).\lambda =\text{Nr}(X_{Y})ʻQ\} \quad[(*154·01)]\)

`NR^Y(X)` is `NRT X Y` (✱154·01); the apparent `Q` is of the type of `Y`. -/
theorem pm154_21 {X : γ → γ → Prop} {Y : β → β → Prop} :
    NRT X Y = {L | ∃ Q : β → β → Prop, Desc (relT2T Nr X Y) Q (fun μ => L = μ)} := by
  rw [NRT_eq_NR]
  ext L
  simp only [desc_relT2T_Nr]
  exact Iff.rfl

/-- ✱154·22. \(\vdash .\text{NR}^{Y}(X)=\text{Nr}(X)ʻʻtʻY=(\cap tʻX)ʻʻ\text{Nr}ʻʻtʻY\)

`Nr(X)''t'Y` is `relT2 Nr X ʻʻ typ Y`; `(∩ t'X)` is the relation `♀y` of ✱38 with `♀ = ∩`,
`opR (· ∩ ·) (typ X)` (`μ ∩ t'X` to `μ`); `Nr''t'Y` is `Nr ʻʻ typ Y`, put in the type of `X` by
`∩ t'X`. The chain is the conjunction of its two links. -/
theorem pm154_22 {X : γ → γ → Prop} {Y : β → β → Prop} :
    NRT X Y = relT2 (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) X ʻʻ typ Y ∧
      relT2 (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) X ʻʻ typ Y =
        opR (· ∩ ·) (typ X) ʻʻ ((Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) ʻʻ typ Y) := by
  rw [relT2_eq'', NRT_eq_NR, typ_eq_univ, typ_eq_univ]
  constructor
  · ext L
    exact ⟨fun ⟨Q, hQ⟩ => ⟨Q, trivial, hQ⟩, fun ⟨Q, _, hQ⟩ => ⟨Q, hQ⟩⟩
  · ext L
    constructor
    · rintro ⟨Q, -, hQ⟩
      exact ⟨L, ⟨Q, trivial, hQ⟩, (Set.inter_univ L).symm⟩
    · rintro ⟨M, ⟨Q, -, hQ⟩, hL⟩
      have hL' : L = M ∩ Set.univ := hL
      rw [Set.inter_univ] at hL'
      exact ⟨Q, trivial, hL' ▸ hQ⟩

/-- ✱154·23. \(\vdash :\Lambda \in \text{NR}^{Q}(P).\equiv .\Lambda \in \text{NC}^{CʻQ}(CʻP).\equiv .\Lambda \in \text{NC}(CʻP)ʻʻtʻCʻQ\)

`NC^{C'Q}(C'P)` is `NCT (fld P) (fld Q)`, `Nc(C'P)''t'C'Q` is `relT2 Nc (fld P) ʻʻ typ (fld Q)`.

**Status.** proved (reading): transcription error: the e-text prints `NC(C'P)''t'C'Q` for
`Nc(C'P)''t'C'Q` (PM's proof: `Λ ∈ Nc(C'P)''t'C'Q`, by ✱37·6). -/
theorem pm154_23 {P : γ → γ → Prop} {Q : β → β → Prop} :
    (Λ ∈ NRT P Q ↔ Λ ∈ NCT (fld P) (fld Q)) ∧
      (Λ ∈ NCT (fld P) (fld Q) ↔
        Λ ∈ relT2 (Nc : Set (Set γ) → Set β → Prop) (fld P) ʻʻ typ (fld Q)) := by
  rw [NRT_eq_NR, NCT_eq_NC, relT2_eq'', typ_eq_univ]
  refine ⟨?_, ⟨fun ⟨B, hB⟩ => ⟨B, trivial, hB⟩, fun ⟨B, _, hB⟩ => ⟨B, hB⟩⟩⟩
  constructor
  · intro h
    obtain ⟨R, hR⟩ := mem_NR.1 h
    refine mem_NC.2 ⟨fld R, ?_⟩
    rw [nc_fld_eq, ← hR, Null_eq_empty, Null_eq_empty]
    refine (Set.eq_empty_iff_forall_notMem.2 fun X hX => ?_).symm
    obtain ⟨S, hS, -⟩ := hX
    exact hS
  · intro h
    obtain ⟨B, hB⟩ := mem_NC.1 h
    refine mem_NR.2 ⟨(I : β → β → Prop) ↾ B, ?_⟩
    rw [Null_eq_empty] at hB ⊢
    refine (Set.eq_empty_iff_forall_notMem.2 fun R hR => ?_).symm
    have : fld R ∈ nc γ B := by
      rw [← fld_I_cres B]; exact sm_fld_of_smor hR
    rw [← hB] at this
    exact this

/-- ✱154·24. \(\vdash :CʻQ=tʻCʻP.\supset .\text{Nr}(P)ʻQ=\Lambda \quad[*102·73.*154·14]\)

`C'Q = t'C'P` makes `Q` a relation of classes of the type of `C'P` with every such class in
its field. -/
theorem pm154_24 {P : γ → γ → Prop} {Q : Set γ → Set γ → Prop} :
    fld Q = typ (fld P) → Desc (relT2 Nr P) Q (fun μ => μ = Λ) := by
  intro h
  rw [desc_relT2_Nr, Null_eq_empty]
  exact nr_eq_empty_of_cantor (h.trans (typ_eq_univ _))

/-- ✱154·241. \(\vdash .\text{Nr}(P)ʻI\upharpoonright tʻCʻP=\Lambda \quad[*154·24]\)

`Nr(P)'I↾t'C'P` is `Nr(P)'(I ↾ t'C'P)` (only this bracketing is significant). -/
theorem pm154_241 {P : γ → γ → Prop} :
    Desc (relT2 Nr P) ((I : Set γ → Set γ → Prop) ↾ typ (fld P)) (fun μ => μ = Λ) :=
  pm154_24 (fld_I_cres _)

/-- ✱154·242. \(\vdash .\Lambda \in \text{NR}^{\iota ^{;}P}(P)\)

`NR^{ι;P}(P)` is `NRT P (iota ⁏ P)`. -/
theorem pm154_242 {P : γ → γ → Prop} : Λ ∈ NRT P (iota ⁏ P) := by
  rw [NRT_eq_NR]
  exact ⟨_, ((desc_relT2_Nr _ _ _).1 (pm154_241 (P := P))).symm⟩

/-- ✱154·25. \(\vdash :CʻQ=t_{00}ʻCʻP.\supset .\text{Nr}(P)ʻQ=\Lambda \quad[*106·53.*154·14]\)

`t₀₀'C'P` is `typ₀₀ (fld P)` (✱64·01), the relations of the type of `C'P ↑ C'P`. -/
theorem pm154_25 {P : γ → γ → Prop} {Q : (γ → γ → Prop) → (γ → γ → Prop) → Prop} :
    fld Q = typ₀₀ (fld P) → Desc (relT2 Nr P) Q (fun μ => μ = Λ) := by
  intro h
  rw [desc_relT2_Nr, Null_eq_empty]
  refine Set.eq_empty_iff_forall_notMem.2 fun R hR => ?_
  obtain ⟨f, hf⟩ := nr_nonempty_iff.1 ⟨R, hR⟩
  have hmem : ∀ A : Set γ, cross A A ∈ fld Q := fun A => by
    rw [h, typ₀₀, typ_eq_univ]; trivial
  refine Function.cantor_injective (fun A => f ⟨cross A A, hmem A⟩) fun A B e => ?_
  have e1 : cross A A = cross B B := congrArg Subtype.val (hf e)
  ext x
  constructor
  · intro hx; exact (Eq.mp (congrFun (congrFun e1 x) x) ⟨hx, hx⟩).1
  · intro hx; exact (Eq.mpr (congrFun (congrFun e1 x) x) ⟨hx, hx⟩).1

/-- ✱154·251. \(\vdash .\Lambda \in \text{NR}^{P\downarrow P}(P)\)

`NR^{P↓P}(P)` is `NRT P (P ↓ P)`. -/
theorem pm154_251 {P : γ → γ → Prop} : Λ ∈ NRT P (P ↓ P) := by
  rw [NRT_eq_NR]
  exact ⟨_, ((desc_relT2_Nr _ _ _).1 (pm154_25 (P := P) (fld_I_cres (typ₀₀ (fld P))))).symm⟩

/-- ✱154·26. \(\vdash :P\in tʻQ.\supset .\exists !\text{Nr}(P)ʻQ \quad[*64·231.*103·3·13.*154·14]\)

`P ∈ t'Q` makes `P` of the type of `Q`. -/
theorem pm154_26 {P Q : γ → γ → Prop} : P ∈ typ Q → Desc (relT2 Nr P) Q (fun μ => μ.Nonempty) := by
  intro _
  rw [desc_relT2_Nr]
  exact ⟨Q, smor_refl Q⟩

/-- ✱154·261. \(\vdash :CʻP\in t^{2}ʻCʻQ.\supset .\exists !\text{Nr}(P)ʻQ \quad[*104·21·1.*154·14]\)

`t²'C'Q` is `typ2 (fld Q)`; `C'P ∈ t²'C'Q` makes `P` a relation of classes of the type of
`C'Q`. -/
theorem pm154_261 {Q : β → β → Prop} {P : Set β → Set β → Prop} :
    fld P ∈ typ2 (fld Q) → Desc (relT2 Nr P) Q (fun μ => μ.Nonempty) := by
  intro _
  rw [desc_relT2_Nr]
  exact nr_nonempty_iff.2 ⟨fun x => ι (x : β), fun x y h => Subtype.ext (unitCls_injective h)⟩

/-- ✱154·262. \(\vdash :CʻP\in t_{00}ʻCʻQ.\supset .\exists !\text{Nr}(P)ʻQ \quad[*106·21·1.*154·14]\)

**Status.** proved (reading): the e-text prints `C'P ∈ t₀₀'C'Q`, which is not significant
(`C'P` is a class, `t₀₀'C'Q` a type of relations); it is read `C'P ∈ t't₀₀'C'Q` (`C'P` a class
of relations of the type `t₀₀'C'Q`), the hypothesis of ✱106·21 cited in the proof, by analogy
with ✱154·261 (`C'P ∈ t²'C'Q`). -/
theorem pm154_262 {Q : β → β → Prop} {P : (β → β → Prop) → (β → β → Prop) → Prop} :
    fld P ∈ typ (typ₀₀ (fld Q)) → Desc (relT2 Nr P) Q (fun μ => μ.Nonempty) := by
  intro _
  rw [desc_relT2_Nr]
  exact nr_nonempty_iff.2 ⟨fun x => (x : β) ↓ (x : β),
    fun x y h => Subtype.ext (couple_eq_couple_iff.1 h).1⟩

/-- ✱154·31. \(\vdash .tʻ\iota ^{;}P=t^{11}ʻCʻP\)

`t¹¹'C'P` is `typ11 (fld P)` (✱64·011). -/
theorem pm154_31 {P : α → α → Prop} : typ (iota ⁏ P) = typ11 (fld P) := by
  rw [typ11, typ_eq_univ, typ_eq_univ]

/-- ✱154·311. \(\vdash .\exists !\text{Nr}(t^{11}ʻCʻP)ʻP \quad[*154·31.*152·6]\)

`Nr(t¹¹'C'P)` has a class (the type `t¹¹'C'P`) for its index; it is read as ✱65·03
`Nr_σ = t'σ ↿ Nr` (`relT Nr (typ11 (fld P))`), the `Nr` whose values are classes of relations
of the type `t¹¹'C'P`.

**Status.** proved (reading): `Nr(σ)` with a class `σ` is read `Nr_σ` (✱65·03), since ✱65·04's
`t²'σ ↿ Nr` is not significant for a class `σ`. -/
theorem pm154_311 {P : α → α → Prop} :
    Desc (relT Nr (typ11 (fld P))) P (fun μ => μ.Nonempty) := by
  rw [desc_relT_Nr]
  exact ⟨iota ⁏ P, pm152_6⟩

/-- ✱154·32. \(\vdash :x\in t_{0}ʻCʻP.\supset .tʻx\downarrow ^{;}P=t^{11}ʻP.t_{0}ʻx\downarrowʻʻCʻP=tʻP\)

`t₀'x↓''C'P` is `typ₀ (coupleL x ʻʻ fld P)`; the conclusion is a product of two. -/
theorem pm154_32 {P : α → α → Prop} {x : α} :
    x ∈ typ₀ (fld P) → typ (coupleL x ⁏ P) = typ11 P ∧ typ₀ (coupleL x ʻʻ fld P) = typ P := by
  intro _
  rw [typ11, typ_eq_univ, typ_eq_univ, typ₀_eq_univ, typ_eq_univ]
  exact ⟨rfl, rfl⟩

/-- ✱154·321. \(\vdash .\exists !\text{Nr}(t^{11}ʻP)ʻP \quad[*154·32.*152·62.*63·18]\)

**Status.** proved (reading): as ✱154·311, `Nr(t¹¹'P)` is read `Nr_{t¹¹'P}` (✱65·03). -/
theorem pm154_321 {P : α → α → Prop} : Desc (relT Nr (typ11 P)) P (fun μ => μ.Nonempty) := by
  rw [desc_relT_Nr]
  exact nr_nonempty_iff.2 ⟨fun x => (x : α) ↓ (x : α),
    fun x y h => Subtype.ext (couple_eq_couple_iff.1 h).1⟩

/-- ✱154·322. \(\vdash :x\in t_{0}ʻCʻP.\supset .tʻ\downarrow x^{;}P=t^{11}ʻP \quad[\text{Proof as in *154·32}]\) -/
theorem pm154_322 {P : α → α → Prop} {x : α} :
    x ∈ typ₀ (fld P) → typ (coupleR x ⁏ P) = typ11 P := by
  intro _
  rw [typ11, typ_eq_univ, typ_eq_univ]

/-- ✱154·33. \(\vdash :x\in t_{0}ʻCʻP.\supset .tʻP\downarrow ^{;}x\downarrow ^{;}P=t^{11}ʻ\dot{s} ʻt^{11}ʻP\)

`P↓;x↓;P` is `coupleL P ⁏ coupleL x ⁏ P` (✱150·05), `ṡ't¹¹'P` is `sumRel (typ11 P)`. -/
theorem pm154_33 {P : α → α → Prop} {x : α} :
    x ∈ typ₀ (fld P) → typ (coupleL P ⁏ coupleL x ⁏ P) = typ11 (sumRel (typ11 P)) := by
  intro _
  simp only [typ11, typ_eq_univ]

/-- ✱154·331. \(\vdash .\exists !\text{Nr}(t^{11}ʻ\dot{s} ʻt^{11}ʻP) \quad[*154·33.*152·62.*63·18]\)

**Status.** proved (reading): transcription error: the e-text omits the argument `'P` of
`Nr(t¹¹'ṡ't¹¹'P)` (PM's proof is by ✱154·33 and ✱152·62, for `P↓;x↓;P`); and, as in ✱154·311,
`Nr(σ)` with a class `σ` is read `Nr_σ` (✱65·03). -/
theorem pm154_331 {P : α → α → Prop} :
    Desc (relT Nr (typ11 (sumRel (typ11 P)))) P (fun μ => μ.Nonempty) := by
  rw [desc_relT_Nr]
  exact nr_nonempty_iff.2 ⟨fun x => ((x : α) ↓ (x : α)) ↓ ((x : α) ↓ (x : α)),
    fun x y h => Subtype.ext (couple_eq_couple_iff.1 (couple_eq_couple_iff.1 h).1).1⟩

/-- ✱154·4. \[\begin{align}\vdash .\text{Nr}(X_{Y})ʻQ=\hat{P} \{(\exists S).S\in 1\rightarrow 1.&\text{ᗡ}ʻS=CʻQ.P=S^{;}Q.\\ &\text{D}ʻS\in tʻCʻX.\text{ᗡ}ʻS\in tʻCʻY\}\end{align}\]

`D'S ∈ t'C'X` is `dom S ∈ typ (fld X)`; the condition is a product of five, bracketed to the
left. -/
theorem pm154_4 {X : γ → γ → Prop} {Y Q : β → β → Prop} :
    Desc (relT2T Nr X Y) Q (fun μ => μ = {P | ∃ S : γ → β → Prop,
      (((S ∈ arrow one one ∧ codom S = fld Q) ∧ P = S ⁏ Q) ∧ dom S ∈ typ (fld X)) ∧
        codom S ∈ typ (fld Y)}) := by
  rw [desc_relT2T_Nr]
  ext P
  simp only [typ_eq_univ, Set.mem_univ, and_true]
  exact ⟨fun ⟨S, ⟨hS, hQ⟩, hP⟩ => ⟨S, ⟨hS, hQ.symm⟩, hP⟩,
    fun ⟨S, ⟨hS, hQ⟩, hP⟩ => ⟨S, ⟨hS, hQ.symm⟩, hP⟩⟩

/-- ✱154·401. \[\begin{align}&\vdash .\text{Nr}(X_{Y})ʻQ=\hat{P} \{\exists !(P\,\overline{\text{smor}}\,Q)\cap tʻ(CʻX\uparrow CʻY)\}\\ &[*154·4.*151·11.*64·63]\end{align}\]

`t'(C'X ↑ C'Y)` is `typ (cross (fld X) (fld Y))`. -/
theorem pm154_401 {X : γ → γ → Prop} {Y Q : β → β → Prop} :
    Desc (relT2T Nr X Y) Q
      (fun μ => μ = {P | (smorbar P Q ∩ typ (cross (fld X) (fld Y))).Nonempty}) := by
  rw [desc_relT2T_Nr, typ_eq_univ]
  ext P
  simp only [Set.inter_univ]
  exact Iff.rfl

/-- ✱154·41. \(\vdash :P\in \text{Nr}(X_{Z})ʻR.Q\in \text{Nr}(Y_{Z})ʻR.\supset .P\in \text{Nr}(X_{Y})ʻQ.Q\in \text{Nr}(Y_{X})ʻP\) -/
theorem pm154_41 {X P : γ → γ → Prop} {Y Q : β → β → Prop} {Z R : δ → δ → Prop} :
    Desc (relT2T Nr X Z) R (fun μ => P ∈ μ) ∧ Desc (relT2T Nr Y Z) R (fun μ => Q ∈ μ) →
      Desc (relT2T Nr X Y) Q (fun μ => P ∈ μ) ∧ Desc (relT2T Nr Y X) P (fun μ => Q ∈ μ) := by
  simp only [desc_relT2T_Nr]
  rintro ⟨h1, h2⟩
  exact ⟨smor_trans h1 (smor_symm h2), smor_trans h2 (smor_symm h1)⟩

/-- ✱154·42. \(\vdash .P\in \text{Nr}(P_{P})ʻP\) -/
theorem pm154_42 {P : α → α → Prop} : Desc (relT2T Nr P P) P (fun μ => P ∈ μ) := by
  rw [desc_relT2T_Nr]; exact smor_refl P

/-- ✱154·43. \(\vdash .\exists !\text{Nr}(P_{P})ʻP\) -/
theorem pm154_43 {P : α → α → Prop} : Desc (relT2T Nr P P) P (fun μ => μ.Nonempty) := by
  rw [desc_relT2T_Nr]; exact ⟨P, smor_refl P⟩

/-- ✱154·46. \(\vdash :P\in \text{Nr}(X_{Y})ʻQ.\equiv .Q\in \text{Nr}(Y_{X})ʻP.\equiv .P\,\text{smor}\,Q.P\in tʻX.Q\in tʻY\) -/
theorem pm154_46 {X P : γ → γ → Prop} {Y Q : β → β → Prop} :
    (Desc (relT2T Nr X Y) Q (fun μ => P ∈ μ) ↔ Desc (relT2T Nr Y X) P (fun μ => Q ∈ μ)) ∧
      (Desc (relT2T Nr Y X) P (fun μ => Q ∈ μ) ↔ (smor P Q ∧ P ∈ typ X) ∧ Q ∈ typ Y) := by
  simp only [desc_relT2T_Nr, typ_eq_univ, Set.mem_univ, and_true]
  exact ⟨⟨smor_symm, smor_symm⟩, ⟨smor_symm, smor_symm⟩⟩

/-- ✱154·52. \(\vdash :\exists !\text{Nr}(X_{Y})ʻQ.\supset .\text{Nr}(X_{Y})ʻQ\in \text{NR}^{X}(X)\) -/
theorem pm154_52 {X : γ → γ → Prop} {Y Q : β → β → Prop} :
    Desc (relT2T Nr X Y) Q (fun μ => μ.Nonempty) →
      Desc (relT2T Nr X Y) Q (fun μ => μ ∈ NRT X X) := by
  simp only [desc_relT2T_Nr, NRT_eq_NR]
  rintro ⟨P, hP⟩
  exact ⟨P, nr_eq_nr_of_smor (smor_symm hP)⟩

/-- ✱154·53. \(\vdash :\text{NR}^{Y}(X)-\iota ʻ\Lambda \subset \text{NR}^{X}(X)\) -/
theorem pm154_53 {X : γ → γ → Prop} {Y : β → β → Prop} : NRT X Y \ ι Λ ⊆ NRT X X := by
  rw [NRT_eq_NR, NRT_eq_NR]
  rintro μ ⟨hμ, hne⟩
  obtain ⟨Q, rfl⟩ := mem_NR.1 hμ
  have : (nr γ Q).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hne (by rw [mem_unitCls, h, Null_eq_empty])
  obtain ⟨P, hP⟩ := this
  exact mem_NR.2 ⟨P, nr_eq_nr_of_smor (smor_symm hP)⟩

/-- ✱154·55. \(\vdash :\Lambda {\sim}\in \text{NR}^{X}(Y).\supset .\text{NR}^{Y}(X)-\iota ʻ\Lambda =\text{NR}^{X}(X)\) -/
theorem pm154_55 {X : γ → γ → Prop} {Y : β → β → Prop} :
    Λ ∉ NRT Y X → NRT X Y \ ι Λ = NRT X X := by
  intro hΛ
  refine Set.Subset.antisymm pm154_53 ?_
  rw [NRT_eq_NR] at hΛ
  rw [NRT_eq_NR, NRT_eq_NR]
  intro μ hμ
  obtain ⟨R, rfl⟩ := mem_NR.1 hμ
  have hne : (nr β R).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hΛ (mem_NR.2 ⟨R, by rw [h, Null_eq_empty]⟩)
  obtain ⟨R', hR'⟩ := hne
  refine ⟨mem_NR.2 ⟨R', nr_eq_nr_of_smor (smor_symm hR')⟩, fun h => ?_⟩
  have h' : nr γ R = Λ := mem_unitCls.1 h
  have hR : R ∈ nr γ R := self_mem_nr R
  rw [h', Null_eq_empty] at hR
  exact hR

/-- ✱154·64. \(\vdash :\mu \in \text{NR}.\exists !\mu .\supset .(\exists P,Q).\mu =\text{Nr}(P)ʻQ\) -/
theorem pm154_64 {μ : Set (γ → γ → Prop)} :
    μ ∈ NR β ∧ μ.Nonempty →
      ∃ (P : γ → γ → Prop) (Q : β → β → Prop), Desc (relT2 Nr P) Q (fun ν => μ = ν) := by
  rintro ⟨hμ, P, -⟩
  obtain ⟨Q, rfl⟩ := mem_NR.1 hμ
  exact ⟨P, Q, (desc_relT2_Nr _ _ _).2 rfl⟩

/-- ✱154·641. \(\vdash :\mu \in \text{NR}.\supset .(\exists P,Q).\mu =\text{Nr}(P)ʻQ \quad[*154·64·241]\)

For `μ = Λ` PM's proof uses ✱154·241; here the relation `Q` with `μ = Nr'Q` given by
`μ ∈ NR` serves (the apparent `Q` is of the type of the converse domain of `NR`). -/
theorem pm154_641 {μ : Set (γ → γ → Prop)} :
    μ ∈ NR β → ∃ (P : γ → γ → Prop) (Q : β → β → Prop), Desc (relT2 Nr P) Q (fun ν => μ = ν) := by
  intro hμ
  obtain ⟨Q, rfl⟩ := mem_NR.1 hμ
  exact ⟨rNull, Q, (desc_relT2_Nr _ _ _).2 rfl⟩

/-- ✱154·8. \(\vdash :P\in \text{Nr}(X_{Y})ʻQ.P\,\text{smor}\,R.R\in tʻS.\supset .R\in \text{Nr}(S_{Y})ʻQ.R\in \text{Nr}(S_{X})ʻP\) -/
theorem pm154_8 {X P : γ → γ → Prop} {Y Q : β → β → Prop} {S R : δ → δ → Prop} :
    (Desc (relT2T Nr X Y) Q (fun μ => P ∈ μ) ∧ smor P R) ∧ R ∈ typ S →
      Desc (relT2T Nr S Y) Q (fun μ => R ∈ μ) ∧ Desc (relT2T Nr S X) P (fun μ => R ∈ μ) := by
  simp only [desc_relT2T_Nr]
  rintro ⟨⟨h1, h2⟩, -⟩
  exact ⟨smor_trans (smor_symm h2) h1, smor_symm h2⟩

/-- ✱154·81. \(\vdash :P\in \text{Nr}(X_{Y})ʻQ.\supset .\text{smor}ʻʻ\text{Nr}(X_{Y})ʻQ\cap tʻS=\text{Nr}(S_{Y})ʻQ=\text{Nr}(S_{X})ʻP\)

The descriptions have the smallest scopes (each link of the chain); `smor''Nr(X_Y)'Q ∩ t'S`
is in the type of `S`. -/
theorem pm154_81 {X P : γ → γ → Prop} {Y Q : β → β → Prop} {S : δ → δ → Prop} :
    Desc (relT2T Nr X Y) Q (fun μ => P ∈ μ) →
      Desc (relT2T Nr X Y) Q
          (fun μ => Desc (relT2T Nr S Y) Q (fun ν => smor ʻʻ μ ∩ typ S = ν)) ∧
        Desc (relT2T Nr S Y) Q (fun ν => Desc (relT2T Nr S X) P (fun ρ => ν = ρ)) := by
  simp only [desc_relT2T_Nr, typ_eq_univ, Set.inter_univ]
  intro h
  exact ⟨pm152_53 ⟨P, h⟩, nr_eq_nr_of_smor (smor_symm h)⟩

/-- ✱154·82. \(\vdash :\mu \in \text{NR}^{Y}(X).\exists !\mu .\supset .\text{smor}ʻʻ\mu \cap tʻS\in \text{NR}^{Y}(S)\) -/
theorem pm154_82 {X : γ → γ → Prop} {Y : β → β → Prop} {S : δ → δ → Prop}
    {μ : Set (γ → γ → Prop)} : μ ∈ NRT X Y ∧ μ.Nonempty → smor ʻʻ μ ∩ typ S ∈ NRT S Y := by
  rw [NRT_eq_NR, NRT_eq_NR]
  rintro ⟨hμ, P, hP⟩
  obtain ⟨Q, rfl⟩ := mem_NR.1 hμ
  rw [typ_eq_univ, Set.inter_univ, pm152_53 ⟨P, hP⟩]
  exact nr_mem_NR Q

/-- ✱154·83. \[\begin{align}\vdash :\mu \in \text{NR}^{Y}(X).\nu =&\text{smor}ʻʻ\mu \cap tʻS.\exists !\nu .\supset .\\ &\text{smor}ʻʻ\mu \cap tʻS=\text{smor}ʻʻ\nu \cap tʻS.\mu =\text{smor}ʻʻ\nu \cap tʻX\end{align}\] -/
theorem pm154_83 {X : γ → γ → Prop} {Y : β → β → Prop} {S : δ → δ → Prop}
    {μ : Set (γ → γ → Prop)} {ν : Set (δ → δ → Prop)} :
    (μ ∈ NRT X Y ∧ ν = smor ʻʻ μ ∩ typ S) ∧ ν.Nonempty →
      smor ʻʻ μ ∩ typ S = smor ʻʻ ν ∩ typ S ∧ μ = smor ʻʻ ν ∩ typ X := by
  rw [NRT_eq_NR]
  rintro ⟨⟨hμ, rfl⟩, hν⟩
  obtain ⟨Q, rfl⟩ := mem_NR.1 hμ
  simp only [typ_eq_univ, Set.inter_univ] at hν ⊢
  have hP : (nr γ Q).Nonempty := by
    obtain ⟨R, P, hP, -⟩ := hν
    exact ⟨P, hP⟩
  have h1 : (smor ʻʻ nr γ Q : Set (δ → δ → Prop)) = nr δ Q := pm152_53 hP
  have hδ : (nr δ Q).Nonempty := by rw [← h1]; exact hν
  rw [h1, pm152_53 hδ, pm152_53 hδ]
  exact ⟨rfl, rfl⟩

/-- ✱154·84. \(\vdash :(\exists P).P\,\text{smor}\,X.P\in tʻX.Q\,\text{smor}\,P.\equiv .Q\,\text{smor}\,X\) -/
theorem pm154_84 {X : γ → γ → Prop} {Q : δ → δ → Prop} :
    (∃ P : γ → γ → Prop, (smor P X ∧ P ∈ typ X) ∧ smor Q P) ↔ smor Q X := by
  constructor
  · rintro ⟨P, ⟨h1, -⟩, h2⟩
    exact smor_trans h2 h1
  · intro h
    exact ⟨X, ⟨smor_refl X, mem_typ' _ _⟩, h⟩

/-- ✱154·85. \(\vdash .\text{smor}ʻʻ\mu \cap tʻY=\text{smor}_{Y}ʻʻ\mu\)

`smor_Y` is ✱65·03 `relT smor Y`. -/
theorem pm154_85 {Y : γ → γ → Prop} {μ : Set (β → β → Prop)} :
    smor ʻʻ μ ∩ typ Y = relT smor Y ʻʻ μ := by
  rw [typ_eq_univ, Set.inter_univ, relT_eq]

/-- ✱154·86. \(\vdash :\mu =\text{Nr}(X)ʻQ.\exists !\mu .\supset .\text{smor}_{Y}ʻʻ\mu =\text{Nr}(Y)ʻQ\) -/
theorem pm154_86 {X : γ → γ → Prop} {Y : ξ → ξ → Prop} {Q : δ → δ → Prop}
    {μ : Set (γ → γ → Prop)} :
    Desc (relT2 Nr X) Q (fun ν => μ = ν) ∧ μ.Nonempty →
      Desc (relT2 Nr Y) Q (fun ν => relT smor Y ʻʻ μ = ν) := by
  simp only [desc_relT2_Nr, relT_eq]
  rintro ⟨rfl, P, hP⟩
  exact pm152_53 ⟨P, hP⟩

/-- ✱154·861. \(\vdash .\text{smor}_{X}ʻʻ\text{smor}_{Y}ʻʻ\mu \subset \text{smor}_{X}ʻʻ\mu\) -/
theorem pm154_861 {X : γ → γ → Prop} {Y : ξ → ξ → Prop} {μ : Set (β → β → Prop)} :
    relT smor X ʻʻ (relT smor Y ʻʻ μ) ⊆ relT smor X ʻʻ μ := by
  simp only [relT_eq]
  rintro R ⟨S, ⟨T, hT, hST⟩, hRS⟩
  exact ⟨T, hT, smor_trans hRS hST⟩

/-- ✱154·87. \(\vdash :\mu =\text{Nr}(Y)ʻQ.\exists !\text{Nr}(X)ʻQ.\supset .\text{smor}_{P}ʻʻ\mu =\text{smor}_{P}ʻʻ\text{smor}_{X}ʻʻ\mu\) -/
theorem pm154_87 {P : α → α → Prop} {X : ξ → ξ → Prop} {Y : β → β → Prop} {Q : δ → δ → Prop}
    {μ : Set (β → β → Prop)} :
    Desc (relT2 Nr Y) Q (fun ν => μ = ν) ∧ Desc (relT2 Nr X) Q (fun ν => ν.Nonempty) →
      relT smor P ʻʻ μ = relT smor P ʻʻ (relT smor X ʻʻ μ) := by
  simp only [desc_relT2_Nr, relT_eq]
  rintro ⟨rfl, Z, hZ⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro R ⟨H, hH, hRH⟩
    exact ⟨Z, ⟨H, hH, smor_trans hZ (smor_symm hH)⟩, smor_trans hRH (smor_trans hH (smor_symm hZ))⟩
  · rintro R ⟨S, ⟨T, hT, hST⟩, hRS⟩
    exact ⟨T, hT, smor_trans hRS hST⟩

/-- ✱154·88. \[\begin{align}\vdash :\mu =\text{Nr}(Y)ʻQ.\exists !&\text{smor}_{P}ʻʻ\mu .\supset .\\ &\text{smor}_{P}ʻʻ\mu =\text{Nr}(P)ʻQ.\text{smor}_{X}ʻʻ\mu =\text{Nr}(X)ʻQ.\\ &\text{smor}_{X}ʻʻ\mu =\text{smor}_{X}ʻʻ\text{smor}_{P}ʻʻ\mu =\text{smor}_{X}ʻʻ\text{Nr}(P)ʻQ\end{align}\]

The conclusion is the product of `smor_P''μ = Nr(P)'Q`, `smor_X''μ = Nr(X)'Q` and the chain
`smor_X''μ = smor_X''smor_P''μ = smor_X''Nr(P)'Q` (the conjunction of its two links). -/
theorem pm154_88 {P : α → α → Prop} {X : ξ → ξ → Prop} {Y : β → β → Prop} {Q : δ → δ → Prop}
    {μ : Set (β → β → Prop)} :
    Desc (relT2 Nr Y) Q (fun ν => μ = ν) ∧ (relT smor P ʻʻ μ).Nonempty →
      (Desc (relT2 Nr P) Q (fun ν => relT smor P ʻʻ μ = ν) ∧
          Desc (relT2 Nr X) Q (fun ν => relT smor X ʻʻ μ = ν)) ∧
        (relT smor X ʻʻ μ = relT smor X ʻʻ (relT smor P ʻʻ μ) ∧
          Desc (relT2 Nr P) Q
            (fun ν => relT smor X ʻʻ (relT smor P ʻʻ μ) = relT smor X ʻʻ ν)) := by
  simp only [desc_relT2_Nr, relT_eq]
  rintro ⟨rfl, Z, H, hH, hZH⟩
  have e1 : (smor ʻʻ nr β Q : Set (α → α → Prop)) = nr α Q := pm152_53 ⟨H, hH⟩
  have e2 : (smor ʻʻ nr β Q : Set (ξ → ξ → Prop)) = nr ξ Q := pm152_53 ⟨H, hH⟩
  have e3 : (smor ʻʻ nr α Q : Set (ξ → ξ → Prop)) = nr ξ Q := pm152_53 ⟨Z, smor_trans hZH hH⟩
  rw [e1, e2, e3]
  exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩

/-- ✱154·9. \(\vdash.\text{NC}=Cʻʻʻ\text{NR}\)

**Status.** proved (reading): the converse domains of `NC` and `NR` are taken in one type `β`
(as in ✱152·72, on which PM's proof rests). -/
theorem pm154_9 : (NC β : Set (Set (Set γ))) = C ʻʻʻ (NR β : Set (Set (γ → γ → Prop))) := by
  ext K
  constructor
  · intro h
    obtain ⟨B, rfl⟩ := mem_NC.1 h
    refine ⟨nr γ ((I : β → β → Prop) ↾ B), nr_mem_NR _, ?_⟩
    show nc γ B = C ʻʻ nr γ ((I : β → β → Prop) ↾ B)
    rw [← nc_fld_eq, fld_I_cres]
  · rintro ⟨μ, hμ, hK⟩
    obtain ⟨P, rfl⟩ := mem_NR.1 hμ
    rw [(hK : K = C ʻʻ nr γ P), ← nc_fld_eq]
    exact nc_mem_NC _

/-!
## [✱155] Homogeneous relation-numbers

*(Vol. 2, p. 344)*

> *Summary of* *155.
>
> A relation-number is called homogeneous when it is generated by a homogeneous relation of likeness, *i.e.* when it consists of all relations which are like a given relation \(P\) and of the same type as \(P\). For the homogeneous relation-number of \(P\) we write "\(\text{N}_{0}\text{r}ʻP\)"; thus \(\text{N}_{0}\text{r}ʻP=\text{Nr}ʻP\cap tʻP\). When \(P\) is given, \(\text{N}_{0}\text{r}ʻP\) is typically definite. We have always \(P\in \text{N}_{0}\text{r}ʻP\), hence \(\exists !\text{N}_{0}\text{r}ʻP\). Conversely, if a typically definite relation-number is not null, it is a homogeneous relation-number; in fact, if \(P\) is a member of it, it is \(\text{N}_{0}\text{r}ʻP\). Thus the homogeneous relation-numbers are all the relation-numbers except \(\Lambda\).
>
> Homogeneous relation-numbers play the same part in relation-arithmetic as homogeneous cardinals play in cardinal arithmetic. The propositions of this number (except *155·6·61) are the analogues of those with the same decimal part in *103. Their proofs are exactly analogous to the proofs of their analogues in *103, and are therefore omitted.
>
> The following propositions are the most useful in this number.
>
> …

**Lean reading.** As ✱103: `N₀r'P` is `n₀r P` (typically definite once `P` is given), `N₀R` is
`N₀R`, `N₀R(X)` is
✱65·02 `clsT2 N₀R X`, `NR(X)` is `clsT2 (NR β) X` with the converse-domain type `β` of `NR`
arbitrary; the typically definite relations are as in ✱154. Equations between `Nr`s are in free
types; in ✱155·16 PM states that convention AT applies, and the equation `Nr'P = Nr'Q` is taken
in a type adequate for both sides (`AdeqNr`, `Defs/Part4`). `C''N₀r'P` is `C ʻʻ n₀r P`,
`N₀c'C'P` is `n₀c (fld P)`. The e-text prints ✱155·26·27 before ✱155·01 (and again after
✱155·25).

**Status.** proved (all propositions; ✱155·01·02 definition; ✱155·11 proved (reading): transcription
error; ✱155·16 proved (reading): convention AT; ✱155·21, ✱155·27 proved (reading): the
converse-domain type of `NR`; ✱155·51, ✱155·52 proved (reading): `[Nonempty _]` (✱155·51 also
`Rl'Cls` read `Rl'(Cls ↑ Cls)`))
-/

/-- ✱155·26. \(\vdash \colon\ldotp \mu \in \text{NR}.\supset :P\in \mu .\equiv .\text{N}_{0}\text{r}ʻP=\mu\)

(The e-text prints ✱155·26·27 before ✱155·01, and again after ✱155·25.) -/
theorem pm155_26 {μ : Set (α → α → Prop)} {P : α → α → Prop} :
    μ ∈ NR β → (P ∈ μ ↔ n₀r P = μ) := by
  intro h
  obtain ⟨Q, rfl⟩ := mem_NR.1 h
  rw [n₀r_eq_nr]
  exact ⟨fun h => nr_eq_nr_of_smor h, fun e => e ▸ self_mem_nr P⟩

/-- ✱155·27. \(\vdash :\mu =\text{N}_{0}\text{r}ʻP.\equiv .\mu \in \text{NR}.P\in \mu\)

**Status.** proved (reading): the converse domain of `NR` is taken in the type of `P` (as in
✱103·27: from left to right PM's proof uses ✱155·21; from right to left any converse-domain
type serves). -/
theorem pm155_27 {μ : Set (α → α → Prop)} {P : α → α → Prop} :
    μ = n₀r P ↔ μ ∈ NR α ∧ P ∈ μ := by
  constructor
  · rintro rfl
    exact ⟨mem_NR.2 ⟨P, n₀r_eq_nr P⟩, self_mem_n₀r P⟩
  · rintro ⟨h, hP⟩
    exact ((pm155_26 h).1 hP).symm

/-- ✱155·01 (Df). \(\text{N}_{0}\text{r}ʻP=\text{Nr}ʻP\cap tʻP \quad\text{Df}\) -/
theorem pm155_01 {P : α → α → Prop} : n₀r P = nr α P ∩ typ P := rfl

/-- ✱155·02 (Df). \(\text{N}_{0}\text{R}=\text{D}ʻ\text{N}_{0}\text{r} \quad\text{Df}\)

The definiens is the descriptive function `D'N₀r` (Basic §5). -/
theorem pm155_02 : Desc D N₀r (fun K => (N₀R : Set (Set (α → α → Prop))) = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱155·11. \(\vdash :Q\in \text{N}_{0}\text{r}ʻP. =.Q\,\text{smor}\,P.Q\in tʻP.\equiv .Q\in \text{Nr}ʻP.Q\in tʻP\)

**Status.** proved (reading): transcription error: the e-text prints `.=.` for `.≡.` after
`Q ∈ N₀r'P`. The chain is the conjunction of its two links. -/
theorem pm155_11 {P Q : α → α → Prop} :
    (Q ∈ n₀r P ↔ smor Q P ∧ Q ∈ typ P) ∧ (smor Q P ∧ Q ∈ typ P ↔ Q ∈ nr α P ∧ Q ∈ typ P) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ✱155·12. \(\vdash .P\in \text{N}_{0}\text{r}ʻP\) -/
theorem pm155_12 {P : α → α → Prop} : P ∈ n₀r P := self_mem_n₀r P

/-- ✱155·13. \(\vdash .\exists !\text{N}_{0}\text{r}ʻP\) -/
theorem pm155_13 {P : α → α → Prop} : (n₀r P).Nonempty := n₀r_nonempty P

/-- ✱155·14. \(\vdash :\text{N}_{0}\text{r}ʻP=\text{N}_{0}\text{r}ʻQ.\equiv .P\in \text{N}_{0}\text{r}ʻQ.\equiv .Q\in \text{N}_{0}\text{r}ʻP.\equiv .P\,\text{smor}\,Q.Q\in tʻP\) -/
theorem pm155_14 {P Q : α → α → Prop} :
    ((n₀r P = n₀r Q ↔ P ∈ n₀r Q) ∧ (P ∈ n₀r Q ↔ Q ∈ n₀r P)) ∧
      (Q ∈ n₀r P ↔ smor P Q ∧ Q ∈ typ P) := by
  rw [mem_n₀r, mem_n₀r, n₀r_eq_n₀r_iff]
  exact ⟨⟨Iff.rfl, ⟨smor_symm, smor_symm⟩⟩,
    ⟨fun h => ⟨smor_symm h, mem_typ' _ _⟩, fun h => smor_symm h.1⟩⟩

/-- ✱155·15. \(\vdash :\exists !\text{N}_{0}\text{r}ʻP\cap \text{N}_{0}\text{r}ʻQ.\equiv .\text{N}_{0}\text{r}ʻP=\text{N}_{0}\text{r}ʻQ\) -/
theorem pm155_15 {P Q : α → α → Prop} : (n₀r P ∩ n₀r Q).Nonempty ↔ n₀r P = n₀r Q := by
  constructor
  · rintro ⟨R, h1, h2⟩
    exact n₀r_eq_n₀r_iff.2 (smor_trans (smor_symm (mem_n₀r.1 h1)) (mem_n₀r.1 h2))
  · intro e
    exact ⟨P, self_mem_n₀r P, e ▸ self_mem_n₀r P⟩

/-- ✱155·16. \(\vdash :\text{N}_{0}\text{r}ʻP=\text{Nr}ʻQ.\equiv .\text{Nr}ʻP=\text{Nr}ʻQ\)

PM: the equation `Nr'P = Nr'Q` on the right "should be subject to the convention AT"
(Summary of ✱155): it is taken in a type `γ` adequate for both sides; `N₀r'P = Nr'Q` is in the
type of `P`.

**Status.** proved (reading): convention AT (Prefatory Statement, VI), as PM states: the
equation `Nr'P = Nr'Q` is in a type adequate for both sides (`AdeqNr γ P`, `AdeqNr γ Q`). -/
theorem pm155_16 {P : α → α → Prop} {Q : β → β → Prop} (hP : AdeqNr γ P) (_hQ : AdeqNr γ Q) :
    n₀r P = nr α Q ↔ nr γ P = nr γ Q := by
  rw [n₀r_eq_nr, nr_eq_nr_iff ⟨P, self_mem_nr P⟩, nr_eq_nr_iff (hP.nr_nonempty P)]

/-- ✱155·2. \(\vdash :\mu \in \text{N}_{0}\text{R}.\equiv .(\exists P).\mu =\text{Nr}ʻP\cap tʻP.\equiv .(\exists P).\mu =\text{N}_{0}\text{r}ʻP\)

`Nr'P ∩ t'P` is `nr α P ∩ typ P`; the chain is the conjunction of its two links. -/
theorem pm155_2 {μ : Set (α → α → Prop)} :
    (μ ∈ N₀R ↔ ∃ P, μ = nr α P ∩ typ P) ∧ ((∃ P, μ = nr α P ∩ typ P) ↔ ∃ P, μ = n₀r P) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ✱155·21. \(\vdash .\text{N}_{0}\text{r}ʻP\in \text{N}_{0}\text{R}.\text{N}_{0}\text{r}ʻP\in \text{NR}\)

**Status.** proved (reading): the converse domain of `NR` is taken in the type of `P` (cf.
✱103·21). -/
theorem pm155_21 {P : α → α → Prop} : n₀r P ∈ N₀R ∧ n₀r P ∈ NR α :=
  ⟨⟨P, rfl⟩, mem_NR.2 ⟨P, n₀r_eq_nr P⟩⟩

/-- ✱155·22. \(\vdash :\mu \in \text{N}_{0}\text{R}.\supset .\exists !\mu\) -/
theorem pm155_22 {μ : Set (α → α → Prop)} : μ ∈ N₀R → μ.Nonempty := by
  rintro ⟨P, rfl⟩
  exact n₀r_nonempty P

/-- ✱155·23. \(\vdash .\Lambda {\sim}\in \text{N}_{0}\text{R}\) -/
theorem pm155_23 : (Λ : Set (α → α → Prop)) ∉ N₀R := by
  intro h
  obtain ⟨P, hP⟩ := pm155_22 h
  rw [Null_eq_empty] at hP
  exact hP

/-- ✱155·24. \(\vdash .\text{N}_{0}\text{R}\in \text{Cls ex}^{2}\text{excl}\)

`Cls ex² excl` is `ClsEx2excl` (✱84·03). -/
theorem pm155_24 : (N₀R : Set (Set (α → α → Prop))) ∈ ClsEx2excl := by
  refine ⟨?_, fun h => pm155_23 h⟩
  rintro μ ν ⟨⟨⟨P, rfl⟩, ⟨Q, rfl⟩⟩, hne⟩
  rw [Null_eq_empty]
  by_contra h
  exact hne (pm155_15.1 (Set.nonempty_iff_ne_empty.2 h))

/-- ✱155·25. \(\vdash \colon\ldotp \mu ,\nu \in \text{N}_{0}\text{R}.\supset :\exists !\mu \cap \nu .\equiv .\mu =\nu\)

`μ ∩ ν` puts `μ`, `ν` in one type. -/
theorem pm155_25 {μ ν : Set (α → α → Prop)} :
    μ ∈ N₀R ∧ ν ∈ N₀R → ((μ ∩ ν).Nonempty ↔ μ = ν) := by
  rintro ⟨⟨P, rfl⟩, ⟨Q, rfl⟩⟩
  exact pm155_15

/-- ✱155·28. \(\vdash :(\exists R).R\,\text{smor}\,P.\mu =\text{N}_{0}\text{r}ʻR.\equiv .\exists !\mu .\mu = \text{Nr}ʻP\)

`μ = Nr'P` is in the type of `μ`; `P` has an arbitrary type. -/
theorem pm155_28 {μ : Set (α → α → Prop)} {P : β → β → Prop} :
    (∃ R : α → α → Prop, smor R P ∧ μ = n₀r R) ↔ μ.Nonempty ∧ μ = nr α P := by
  constructor
  · rintro ⟨R, h, rfl⟩
    exact ⟨n₀r_nonempty R, by rw [n₀r_eq_nr]; exact nr_eq_nr_of_smor h⟩
  · rintro ⟨⟨R, hR⟩, rfl⟩
    exact ⟨R, hR, by rw [n₀r_eq_nr]; exact nr_eq_nr_of_smor (smor_symm hR)⟩

/-- ✱155·3. \(\vdash :Q\in tʻP.\supset .\text{N}_{0}\text{r}ʻQ=\text{Nr}(P)ʻQ=\text{Nr}(P_{P})ʻQ=\text{Nr}ʻQ\cap tʻP\)

`Nr(P)` is `relT2 Nr P`, `Nr(P_P)` is `relT2T Nr P P`; the chain of four is the conjunction of
its three links. -/
theorem pm155_3 {P Q : α → α → Prop} :
    Q ∈ typ P →
      (Desc (relT2 Nr P) Q (fun μ => n₀r Q = μ) ∧
          Desc (relT2 Nr P) Q (fun μ => Desc (relT2T Nr P P) Q (fun ν => μ = ν))) ∧
        Desc (relT2T Nr P P) Q (fun ν => ν = nr α Q ∩ typ P) := by
  intro _
  refine ⟨⟨(desc_relT2_Nr _ _ _).2 (n₀r_eq_nr Q),
    (desc_relT2_Nr _ _ _).2 ((desc_relT2T_Nr _ _ _ _).2 rfl)⟩, (desc_relT2T_Nr _ _ _ _).2 ?_⟩
  rw [typ_eq_univ, Set.inter_univ]

/-- ✱155·301. \(\vdash .\text{NR}^{P}(P)=\text{N}_{0}\text{R}(P)\)

`N₀R(P)` is ✱65·02 `clsT2 N₀R P`. -/
theorem pm155_301 {P : α → α → Prop} : NRT P P = clsT2 N₀R P := by
  rw [clsT2_eq'', NRT_eq_NR]
  ext μ
  constructor
  · intro h
    obtain ⟨Q, rfl⟩ := mem_NR.1 h
    exact ⟨Q, (n₀r_eq_nr Q).symm⟩
  · rintro ⟨Q, rfl⟩
    exact mem_NR.2 ⟨Q, n₀r_eq_nr Q⟩

/-- ✱155·31. \(\vdash :\exists !\text{Nr}(X_{Y})ʻQ.\supset .\text{Nr}(X_{Y})ʻQ\in \text{N}_{0}\text{R}(X)\) -/
theorem pm155_31 {X : γ → γ → Prop} {Y Q : β → β → Prop} :
    Desc (relT2T Nr X Y) Q (fun μ => μ.Nonempty) →
      Desc (relT2T Nr X Y) Q (fun μ => μ ∈ clsT2 N₀R X) := by
  simp only [desc_relT2T_Nr, clsT2_eq'']
  rintro ⟨P, hP⟩
  exact mem_N₀R.2 ⟨P, by rw [n₀r_eq_nr]; exact nr_eq_nr_of_smor (smor_symm hP)⟩

/-- ✱155·32. \(\vdash .\text{NR}^{Y}(X)-\iota ʻ\Lambda \subset \text{N}_{0}\text{R}(X)\) -/
theorem pm155_32 {X : γ → γ → Prop} {Y : β → β → Prop} : NRT X Y \ ι Λ ⊆ clsT2 N₀R X := by
  rw [← pm155_301]
  exact pm154_53

/-- ✱155·33. \(\vdash .\text{NR}(X)-\iota ʻ\Lambda \subset \text{N}_{0}\text{R}(X)\)

`NR(X)` is `clsT2 (NR β) X` (✱65·02), with the converse-domain type `β` of `NR` arbitrary
(as for ✱103·33). -/
theorem pm155_33 {X : γ → γ → Prop} : clsT2 (NR β) X \ ι Λ ⊆ clsT2 N₀R X := by
  have h := pm154_53 (X := X) (Y := (fun _ _ : β => True))
  rw [NRT_eq_NR X (fun _ _ : β => True), pm155_301] at h
  rwa [clsT2_eq'' (NR β) X]

/-- ✱155·34. \(\vdash .\text{NR}-\iota ʻ\Lambda \subset \text{N}_{0}\text{R}\) -/
theorem pm155_34 : (NR β : Set (Set (α → α → Prop))) \ ι Λ ⊆ N₀R := by
  have h := pm155_33 (β := β) (X := (rNull : α → α → Prop))
  rwa [clsT2_eq'', clsT2_eq''] at h

/-- ✱155·35. \(\vdash :\Lambda {\sim}\in \text{NR}^{X}(Y).\supset .\text{NR}^{Y}(X)-\iota ʻ\Lambda =\text{N}_{0}\text{R}(X)\) -/
theorem pm155_35 {X : γ → γ → Prop} {Y : β → β → Prop} :
    Λ ∉ NRT Y X → NRT X Y \ ι Λ = clsT2 N₀R X :=
  fun h => (pm154_55 h).trans pm155_301

/-- ✱155·4. \(\vdash .\text{smor}ʻʻ\text{N}_{0}\text{r}ʻP=\text{Nr}ʻP\)

The equation is in an arbitrary type `γ`. -/
theorem pm155_4 {P : α → α → Prop} : (smor ʻʻ n₀r P : Set (γ → γ → Prop)) = nr γ P := by
  rw [n₀r_eq_nr]
  exact pm152_53 ⟨P, self_mem_nr P⟩

/-- ✱155·41. \(\vdash .\text{smor}ʻʻ\text{N}_{0}\text{r}ʻP\cap tʻQ=\text{Nr}(Q)ʻP\) -/
theorem pm155_41 {P : α → α → Prop} {Q : β → β → Prop} :
    Desc (relT2 Nr Q) P (fun μ => smor ʻʻ n₀r P ∩ typ Q = μ) := by
  rw [desc_relT2_Nr, typ_eq_univ, Set.inter_univ, pm155_4]

/-- ✱155·42. \(\vdash :Q\,\text{smor}\,P.\equiv .\text{Nr}(Q)ʻP=\text{N}_{0}\text{r}ʻQ\) -/
theorem pm155_42 {P : α → α → Prop} {Q : β → β → Prop} :
    smor Q P ↔ Desc (relT2 Nr Q) P (fun μ => μ = n₀r Q) := by
  rw [desc_relT2_Nr, n₀r_eq_nr]
  constructor
  · intro h; exact nr_eq_nr_of_smor (smor_symm h)
  · intro e
    have h := self_mem_nr Q
    rw [← e] at h
    exact h

/-- ✱155·43. \(\vdash :\mu \in \text{NR}.\supset .\text{smor}ʻʻ\mu \cap t_{0}ʻ\mu =\mu\)

`t₀'μ` is `typ₀ μ`. -/
theorem pm155_43 {μ : Set (α → α → Prop)} : μ ∈ NR β → smor ʻʻ μ ∩ typ₀ μ = μ := by
  intro h
  obtain ⟨Q, rfl⟩ := mem_NR.1 h
  rw [typ₀_eq_univ, Set.inter_univ]
  by_cases hne : (nr α Q).Nonempty
  · exact pm152_53 hne
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Set.eq_empty_iff_forall_notMem.2 fun _ ⟨_, h, _⟩ => h

/-- ✱155·44. \(\vdash \colon\ldotp \mu ,\nu \in \text{N}_{0}\text{R}.\supset :\mu =\text{smor}ʻʻ\nu .\equiv .\nu =\text{smor}ʻʻ\mu\)

`μ = smor''ν` is in the type of `μ`, `ν = smor''μ` in that of `ν`. -/
theorem pm155_44 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    μ ∈ N₀R ∧ ν ∈ N₀R → (μ = smor ʻʻ ν ↔ ν = smor ʻʻ μ) := by
  rintro ⟨⟨P, rfl⟩, ⟨Q, rfl⟩⟩
  rw [pm155_4, pm155_4, n₀r_eq_nr, n₀r_eq_nr, nr_eq_nr_iff ⟨P, self_mem_nr P⟩,
    nr_eq_nr_iff ⟨Q, self_mem_nr Q⟩]
  exact ⟨smor_symm, smor_symm⟩

/-- ✱155·5. \(\vdash .0_{r}\in \text{N}_{0}\text{R}\) -/
theorem pm155_5 : (zero_r : Set (α → α → Prop)) ∈ N₀R :=
  mem_N₀R.2 ⟨rNull, by rw [n₀r_eq_nr]; exact pm153_11⟩

/-- ✱155·51. \(\vdash .2_{r}\cap \text{Rl}ʻ\text{Cls}\in \text{N}_{0}\text{R}\)

`Rl'Cls` is read `Rl'(Cls ↑ Cls)` (as in ✱153·27).

**Status.** proved (reading): `Rl'Cls` is read `Rl'(Cls ↑ Cls)` (see ✱153·27); `[Nonempty α]`
(PM assumes every type has a member; in an empty type `2_r ∩ Rl'(Cls ↑ Cls) = Λ`). -/
theorem pm155_51 [Nonempty α] :
    two_r ∩ rl (cross (Cls : Set (Set α)) (Cls : Set (Set α))) ∈ N₀R := by
  obtain ⟨x⟩ := ‹Nonempty α›
  have e : two_r ∩ rl (cross (Cls : Set (Set α)) (Cls : Set (Set α))) = two_r := by
    refine Set.inter_eq_left.2 fun R _ u v _ => ⟨?_, ?_⟩ <;> rw [Cls_eq_univ] <;> trivial
  rw [e]
  exact mem_N₀R.2 ⟨(Λ : Set α) ↓ ι x, by rw [n₀r_eq_nr]; exact pm153_24⟩

/-- ✱155·52. \(\vdash .2_{r}\cap \text{Rel}^{2}\in \text{N}_{0}\text{R}\)

`Rel²` is `Rel2` (✱61·03).

**Status.** proved (reading): `[Nonempty α]`, `[Nonempty β]` (PM assumes every type has a
member; otherwise `2_r ∩ Rel² = Λ`). -/
theorem pm155_52 [Nonempty α] [Nonempty β] :
    two_r ∩ (Rel2 : Set ((α → β → Prop) → (α → β → Prop) → Prop)) ∈ N₀R := by
  obtain ⟨x⟩ := ‹Nonempty α›
  obtain ⟨y⟩ := ‹Nonempty β›
  have e : two_r ∩ (Rel2 : Set ((α → β → Prop) → (α → β → Prop) → Prop)) = two_r := by
    refine Set.inter_eq_left.2 fun R _ u v _ => ⟨?_, ?_⟩ <;> rw [Rel_eq_univ] <;> trivial
  rw [e]
  have hne : (rNull : α → β → Prop) ≠ x ↓ y := fun h =>
    rNull_apply x y (by rw [h]; exact ⟨mem_unitCls.2 rfl, mem_unitCls.2 rfl⟩)
  exact mem_N₀R.2 ⟨(rNull : α → β → Prop) ↓ (x ↓ y), by rw [n₀r_eq_nr]; exact pm153_211 hne⟩

/-- ✱155·6. \(\vdash .Cʻʻ\text{N}_{0}\text{r}ʻP=\text{N}_{0}\text{c}ʻCʻP\)

`N₀c'C'P` is `n₀c (fld P)`. -/
theorem pm155_6 {P : α → α → Prop} : C ʻʻ n₀r P = n₀c (fld P) := by
  rw [n₀r_eq_nr, n₀c_eq_nc, nc_fld_eq]

/-- ✱155·61. \(\vdash .Cʻʻʻ\text{N}_{0}\text{R}=\text{N}_{0}\text{C} \quad[*155·6]\)

`C'''N₀R` is `C ʻʻʻ N₀R`. -/
theorem pm155_61 : C ʻʻʻ (N₀R : Set (Set (α → α → Prop))) = N₀C := by
  ext K
  constructor
  · rintro ⟨μ, ⟨P, rfl⟩, hK⟩
    exact ⟨fld P, (hK : K = C ʻʻ n₀r P).trans pm155_6⟩
  · rintro ⟨A, rfl⟩
    refine ⟨n₀r ((I : α → α → Prop) ↾ A), ⟨_, rfl⟩, ?_⟩
    show n₀c A = C ʻʻ n₀r ((I : α → α → Prop) ↾ A)
    rw [pm155_6, fld_I_cres]

end PrincipiaMathematica
