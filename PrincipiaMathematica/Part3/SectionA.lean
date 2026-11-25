import PrincipiaMathematica.Defs.Part3

/-!
# Part III, Section A: Definition and logical properties of cardinal numbers

Volume 2. Numbers: ✱100, ✱101, ✱102, ✱103, ✱104, ✱105, ✱106.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

/-- Rewrites the relative types of ✱63–✱64 (each `Set.univ` of its Lean type) and the typically
definite constants of ✱65 (`α_x`, `α(x)`, `R_x`, `R_{(x,y)}`, `R(x_y)`, `R(x,y)`), and simplifies. -/
local macro "typ_simp" : tactic =>
  `(tactic| simp only [typ_eq_univ, typ₀_eq_univ, typ₁, typ₂, typ2, typ₀₀, typ11, typ₀₁, typ₀1,
    typ1₀, typ₁₁, Set.mem_univ, Set.subset_univ, and_true, true_and, Set.inter_univ, clsT_eq,
    relT_eq, relTT_eq, iff_self, and_self] at *)

/-! ### Helper lemmas for ✱100–✱106 (not propositions of PM) -/

section Helpers

variable {α β γ δ : Type*}

private theorem mem_typ (x y : α) : y ∈ typ x := by rw [typ_eq_univ]; trivial

private theorem typ_eq_typ (x y : α) : typ x = typ y := by rw [typ_eq_univ, typ_eq_univ]

private theorem typ₀_eq_typ₀ (A B : Set α) : typ₀ A = typ₀ B := by
  rw [typ₀_eq_univ, typ₀_eq_univ]

private theorem mem_typ₀ (A : Set α) (x : α) : x ∈ typ₀ A := by rw [typ₀_eq_univ]; trivial
private theorem mem_typ₁ (K : Set (Set α)) (x : α) : x ∈ typ₁ K := mem_typ₀ _ x
private theorem mem_typ₂ (K : Set (Set (Set α))) (x : α) : x ∈ typ₂ K := mem_typ₀ _ x
private theorem sub_typ (x : α) (B : Set α) : B ⊆ typ x := fun y _ => mem_typ x y
private theorem sub_typ₀ (A B : Set α) : B ⊆ typ₀ A := fun y _ => mem_typ₀ A y
private theorem sub_typ₁ (K : Set (Set α)) (B : Set α) : B ⊆ typ₁ K := fun y _ => mem_typ₁ K y
private theorem sub_typ₂ (K : Set (Set (Set α))) (B : Set α) : B ⊆ typ₂ K :=
  fun y _ => mem_typ₂ K y
private theorem sub_typ2 (x : α) (B : Set (Set α)) : B ⊆ typ2 x := fun y _ => mem_typ (typ x) y

/-- Adding conditions that always hold (typing conditions) under an existential. -/
private theorem ex_congr_true {τ : Sort*} {P Q₁ Q₂ : τ → Prop} (h1 : ∀ i, Q₁ i)
    (h2 : ∀ i, Q₂ i) : (∃ i, P i ∧ Q₁ i) ↔ ∃ i, P i ∧ Q₂ i :=
  ⟨fun ⟨i, h, _⟩ => ⟨i, h, h2 i⟩, fun ⟨i, h, _⟩ => ⟨i, h, h1 i⟩⟩

private theorem mem_img_iff_ex_true {R : α → β → Prop} {B : Set β} {x : α} {Q : β → Prop}
    (h : ∀ i, Q i) : x ∈ R ʻʻ B ↔ ∃ y, (y ∈ B ∧ R x y) ∧ Q y :=
  ⟨fun ⟨y, hy, hr⟩ => ⟨y, ⟨hy, hr⟩, h y⟩, fun ⟨y, ⟨hy, hr⟩, _⟩ => ⟨y, hy, hr⟩⟩

private theorem clsT2_eq' (A : Set (Set α)) (x : α) : clsT2 A x = A := by
  rw [clsT2, typ_eq_univ, Set.inter_univ]

private theorem relT2_eq' (R : Set α → β → Prop) (x : α) : relT2 R x = R := by
  funext K y; simp [relT2, dres, typ2, typ_eq_univ]

private theorem relT2T_eq' (R : Set α → β → Prop) (x : α) (y : β) : relT2T R x y = R := by
  funext K z; simp [relT2T, dres, cres, typ2, typ_eq_univ]

private theorem relT2T2_eq' (R : Set α → Set β → Prop) (x : α) (y : β) :
    relT2T2 R x y = R := by
  funext K z; simp [relT2T2, dres, cres, typ2, typ_eq_univ]

/-- `Nc(α_β)'δ` is `nc α δ` (the descriptive function of `Nc(α_β)` always exists). -/
private theorem desc_relT2T_Nc (A : Set α) (B E : Set β) (ψ : Set (Set α) → Prop) :
    Desc (relT2T (Nc : Set (Set α) → Set β → Prop) A B) E ψ ↔ ψ (nc α E) := by
  rw [relT2T_eq']; exact desc_Nc E ψ

/-- `Nc(α)'δ` is `nc α δ`. -/
private theorem desc_relT2_Nc' (A : Set α) (E : Set β) (ψ : Set (Set α) → Prop) :
    Desc (relT2 (Nc : Set (Set α) → Set β → Prop) A) E ψ ↔ ψ (nc α E) := by
  rw [relT2_eq']; exact desc_Nc E ψ

/-- `Nc(α,β)'δ` is `nc α δ`. -/
private theorem desc_relT2T2_Nc (A : Set α) (b : β) (E : Set β) (ψ : Set (Set α) → Prop) :
    Desc (relT2T2 (Nc : Set (Set α) → Set β → Prop) A b) E ψ ↔ ψ (nc α E) := by
  rw [relT2T2_eq']; exact desc_Nc E ψ

private theorem img_graph (f : β → α) (A : Set β) : graph f ʻʻ A = f '' A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

/-- An injective image of `A` is similar to `A`. -/
private theorem sm_graph_img {f : β → α} {A : Set β} (hf : Set.InjOn f A) :
    sm (graph f ʻʻ A) A := by
  rw [img_graph]
  exact sm_iff_nonempty_equiv.2 ⟨(Equiv.Set.imageOfInjOn f A hf).symm⟩

private theorem iota_eq_graph : (iota : Set α → α → Prop) = graph unitCls := rfl

private theorem sm_iota_img (A : Set α) : sm (iota ʻʻ A) A := by
  rw [iota_eq_graph]; exact sm_graph_img (unitCls_injective.injOn)

/-- `α sm Λ . ≡ . α = Λ` (cf. ✱73·48). -/
private theorem sm_empty_iff {B : Set α} : sm B (∅ : Set β) ↔ B = ∅ := by
  rw [sm_iff_nonempty_equiv]
  constructor
  · rintro ⟨e⟩
    exact Set.eq_empty_iff_forall_notMem.2 fun b hb => (e ⟨b, hb⟩).2
  · rintro rfl
    exact ⟨Equiv.equivOfIsEmpty _ _⟩

/-- `α sm ι'x . ≡ . α ∈ 1` (cf. ✱73·45). -/
private theorem sm_unit_iff {B : Set α} {x : β} : sm B (ι x) ↔ B ∈ one := by
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

/-- `Nc'α = 1 . ≡ . α ∈ 1` in a type with members. -/
private theorem nc_eq_one_iff [Nonempty γ] {A : Set α} : nc γ A = one ↔ A ∈ one := by
  constructor
  · intro h
    obtain ⟨g⟩ := ‹Nonempty γ›
    have hg : ι g ∈ nc γ A := by rw [h]; exact ⟨g, rfl⟩
    exact sm_unit_iff.1 (sm_symm hg)
  · rintro ⟨y, rfl⟩
    ext B
    exact sm_unit_iff

private theorem nonempty_of_not_mem_iota_null {μ : Set α} (h : μ ∉ ι Λ) : μ.Nonempty := by
  by_contra h'
  rw [Set.not_nonempty_iff_eq_empty] at h'
  exact h (by rw [h', Null_eq_empty]; exact mem_unitCls.2 rfl)

private theorem unit_union_ne_empty (x y : α) : ι x ∪ ι y ≠ ∅ :=
  Set.nonempty_iff_ne_empty.1 ⟨x, Or.inl rfl⟩

/-- `x ≠ y . ⊃ : α sm (ι'x ∪ ι'y) . ≡ . α ∈ 2` (cf. ✱54·26, ✱101·3). -/
private theorem sm_pair_iff {B : Set α} {x y : β} (hxy : x ≠ y) :
    sm B (ι x ∪ ι y) ↔ B ∈ two := by
  rw [sm_iff_nonempty_equiv, mem_two_iff, unitCls_eq_singleton, unitCls_eq_singleton,
    Set.singleton_union]
  have hfin : Finite ↥({x, y} : Set β) := Set.toFinite _
  constructor
  · rintro ⟨e⟩
    have h2 : B.ncard = 2 := by
      rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_pair hxy]
    obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.1 h2
    exact ⟨a, b, hab, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩
    have : Finite ↥({a, b} : Set α) := Set.toFinite _
    apply Finite.card_eq.1
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_pair hab, Set.ncard_pair hxy]

/-- Restricting a one-one relation to a part `α` of its domain: `α sm R̆''α` (cf. ✱73·11). -/
private theorem sm_cnv_img {R : β → γ → Prop} {A : Set β} (hR : R ∈ arrow one one)
    (hA : A ⊆ dom R) : sm A (R˘ ʻʻ A) := by
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
  refine sm_iff.2 ⟨fun x y => x ∈ A ∧ R x y, ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨_, hx⟩, ⟨_, hy⟩⟩; exact h1 x y z ⟨hx, hy⟩
  · rintro x y z ⟨⟨_, hy⟩, ⟨_, hz⟩⟩; exact h2 x y z ⟨hy, hz⟩
  · ext x
    exact ⟨fun hx => let ⟨y, hy⟩ := hA hx; ⟨y, hx, hy⟩, fun ⟨_, hx, _⟩ => hx⟩
  · ext y
    exact Iff.rfl

/-- `α ⊂ ᗡ'R . R↾α ∈ 1 → 1 . ⊃ . R''α sm α` (cf. ✱73·15). -/
private theorem sm_img_cres {R : γ → β → Prop} {A : Set β} (hA : A ⊆ codom R)
    (hR : R ↾ A ∈ arrow one one) : sm (R ʻʻ A) A := by
  refine sm_iff.2 ⟨R ↾ A, ⟨hR, ?_⟩, ?_⟩
  · ext x
    exact ⟨fun ⟨y, hy, hxy⟩ => ⟨y, hxy, hy⟩, fun ⟨y, hxy, hy⟩ => ⟨y, hy, hxy⟩⟩
  · ext y
    exact ⟨fun hy => let ⟨x, hx⟩ := hA hy; ⟨x, hx, hy⟩, fun ⟨_, _, hy⟩ => hy⟩

/-- From a one-one `R↾α` with `α ⊂ ᗡ'R`: every `y ∈ α` has exactly one referent. -/
private theorem unique_of_cres {R : γ → β → Prop} {A : Set β} (hA : A ⊆ codom R)
    (hR : R ↾ A ∈ arrow one one) {y : β} (hy : y ∈ A) : ∃ b, ∀ x, R x y ↔ x = b := by
  obtain ⟨b, hb⟩ := hA hy
  exact ⟨b, fun x => ⟨fun hx => (mem_arrow_one_one.1 hR).1 x b y ⟨⟨hx, hy⟩, ⟨hb, hy⟩⟩,
    fun e => e ▸ hb⟩⟩

/-- `R'x = R'y` when `R'x`, `R'y` exist with values `b`, `c`. -/
private theorem desc_eq_iff {R : γ → β → Prop} {x y : β} {b c : γ} (hb : ∀ u, R u x ↔ u = b)
    (hc : ∀ u, R u y ↔ u = c) : Desc R x (fun u => Desc R y (fun v => u = v)) ↔ b = c := by
  rw [Desc, TheIs_iff_of_unique hb, Desc, TheIs_iff_of_unique hc]

/-- The condition of ✱100·14 on `R` is that of ✱100·15. -/
private theorem cond14_iff_cond15 {R : γ → β → Prop} {A : Set β} :
    (A ⊆ codom R ∧ R ↾ A ∈ arrow one one) ↔
      (EE R A ∧ ∀ x y, (x ∈ A ∧ y ∈ A) ∧ Desc R x (fun u => Desc R y (fun v => u = v)) →
        x = y) := by
  constructor
  · rintro ⟨hA, hR⟩
    refine ⟨fun y hy => unique_of_cres hA hR hy, ?_⟩
    rintro x y ⟨⟨hx, hy⟩, h⟩
    obtain ⟨b, hb⟩ := unique_of_cres hA hR hx
    obtain ⟨c, hc⟩ := unique_of_cres hA hR hy
    have e : b = c := (desc_eq_iff hb hc).1 h
    subst e
    exact (mem_arrow_one_one.1 hR).2 b x y ⟨⟨(hb b).2 rfl, hx⟩, ⟨(hc b).2 rfl, hy⟩⟩
  · rintro ⟨hE, hinj⟩
    refine ⟨fun y hy => let ⟨b, hb⟩ := hE y hy; ⟨b, (hb b).2 rfl⟩, mem_arrow_one_one.2 ⟨?_, ?_⟩⟩
    · rintro x x' z ⟨⟨hx, hz⟩, ⟨hx', _⟩⟩
      obtain ⟨b, hb⟩ := hE z hz
      exact ((hb x).1 hx).trans ((hb x').1 hx').symm
    · rintro x y z ⟨⟨hxy, hy⟩, ⟨hxz, hz⟩⟩
      obtain ⟨b, hb⟩ := hE y hy
      obtain ⟨c, hc⟩ := hE z hz
      exact hinj y z ⟨⟨hy, hz⟩, (desc_eq_iff hb hc).2 (((hb x).1 hxy).symm.trans ((hc x).1 hxz))⟩

/-- The condition of ✱100·14 on `R` is that of ✱100·16. -/
private theorem cond14_iff_cond16 {R : γ → β → Prop} {A : Set β} :
    (A ⊆ codom R ∧ R ↾ A ∈ arrow one one) ↔
      (∀ x y, x ∈ A ∧ y ∈ A → (Desc R x (fun u => Desc R y (fun v => u = v)) ↔ x = y)) := by
  constructor
  · rintro ⟨hA, hR⟩ x y ⟨hx, hy⟩
    obtain ⟨b, hb⟩ := unique_of_cres hA hR hx
    obtain ⟨c, hc⟩ := unique_of_cres hA hR hy
    rw [desc_eq_iff hb hc]
    constructor
    · rintro rfl
      exact (mem_arrow_one_one.1 hR).2 b x y ⟨⟨(hb b).2 rfl, hx⟩, ⟨(hc b).2 rfl, hy⟩⟩
    · rintro rfl
      exact (hc b).1 ((hb b).2 rfl)
  · intro h
    have hE : ∀ y, y ∈ A → ∃ b, ∀ x, R x y ↔ x = b := by
      intro y hy
      obtain ⟨b, hb, -⟩ := (h y y ⟨hy, hy⟩).2 rfl
      exact ⟨b, hb⟩
    exact (cond14_iff_cond15 (R := R)).2 ⟨hE, fun x y ⟨hxy, hd⟩ => (h x y hxy).1 hd⟩

/-- Cantor (✱102·71·72): no sub-class of `α` is similar to `Cl'α`. -/
private theorem not_sm_cl {A B : Set α} (h : B ⊆ A) : ¬ sm B (cl A) := by
  intro hs
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hs
  let W : Set α := {x | ∃ hx : x ∈ B, x ∉ (e ⟨x, hx⟩ : Set α)}
  have hW : W ∈ cl A := fun x ⟨hx, _⟩ => h hx
  obtain ⟨⟨w, hwB⟩, hw⟩ := e.surjective ⟨W, hW⟩
  have key : w ∈ W ↔ w ∉ W := by
    have hv : (e ⟨w, hwB⟩ : Set α) = W := congrArg Subtype.val hw
    constructor
    · rintro ⟨_, h'⟩; rwa [hv] at h'
    · intro h'; exact ⟨hwB, by rwa [hv]⟩
  by_cases hm : w ∈ W
  · exact key.1 hm hm
  · exact hm (key.2 hm)

/-- No class of the type of `α` is similar to `t'α` (✱102·73). -/
private theorem nc_typ_eq_empty (A : Set α) : nc α (typ A) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun B hB => not_sm_cl (Set.subset_univ B) ?_
  have : cl (Set.univ : Set α) = typ A := by
    rw [typ_eq_univ]; exact Set.eq_univ_of_forall fun _ => Set.subset_univ _
  rw [this]; exact hB

private theorem n1c_eq (A : Set α) : n1c A = nc (Set α) A := by
  simp only [n1c, typ_eq_univ, Set.inter_univ]
private theorem n2c_eq (A : Set α) : n2c A = nc (Set (Set α)) A := by
  simp only [n2c, typ_eq_univ, Set.inter_univ]
private theorem n₁c_eq (A : Set (Set α)) : n₁c A = nc α A := by
  simp only [n₁c, typ_eq_univ, Set.inter_univ]
private theorem n₂c_eq (A : Set (Set (Set α))) : n₂c A = nc α A := by
  simp only [n₂c, typ_eq_univ, Set.inter_univ]
private theorem up1_eq (μ : Set (Set α)) : up1 μ = sm ʻʻ μ := by
  simp only [up1, typ_eq_univ, Set.inter_univ]
private theorem up2_eq (μ : Set (Set α)) : up2 μ = sm ʻʻ μ := by
  simp only [up2, typ2, typ_eq_univ, Set.inter_univ]
private theorem down1_eq (μ : Set (Set (Set α))) : down1 μ = sm ʻʻ μ := by
  simp only [down1, typ₁, typ₀_eq_univ, Set.inter_univ]
private theorem down2_eq (μ : Set (Set (Set (Set α)))) : down2 μ = sm ʻʻ μ := by
  simp only [down2, typ₂, typ₁, typ₀_eq_univ, Set.inter_univ]
private theorem n₀₀c_eq (A : Set α) : n₀₀c A = nc (α → α → Prop) A := by
  simp only [n₀₀c, typ_eq_univ, Set.inter_univ]
private theorem n11c_eq (A : Set α) : n11c A = nc (Set α → Set α → Prop) A := by
  simp only [n11c, typ_eq_univ, Set.inter_univ]
private theorem n₀₁c_eq (A : Set (Set α)) : n₀₁c A = nc (Set α → α → Prop) A := by
  simp only [n₀₁c, typ_eq_univ, Set.inter_univ]
private theorem n₀1c_eq (A : Set α) : n₀1c A = nc (α → Set α → Prop) A := by
  simp only [n₀1c, typ_eq_univ, Set.inter_univ]
private theorem n1₀c_eq (A : Set α) : n1₀c A = nc (Set α → α → Prop) A := by
  simp only [n1₀c, typ_eq_univ, Set.inter_univ]
private theorem down00_eq (μ : Set (Set α)) : down00 μ = sm ʻʻ μ := by
  simp only [down00, typ_eq_univ, Set.inter_univ]
private theorem up11_eq (μ : Set (Set α)) : up11 μ = sm ʻʻ μ := by
  simp only [up11, typ_eq_univ, Set.inter_univ]

/-- `sm''μ` is null when `μ` is. -/
private theorem sm_img_empty : (sm ʻʻ (∅ : Set (Set α)) : Set (Set β)) = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ ⟨_, hY, _⟩ => hY

/-- `ι'x ∪ ι'y = ι'x ∪ ι'y' . ⊃ . y = y'`. -/
private theorem pair_right_inj {x y y' : α} (h : ι x ∪ ι y = ι x ∪ ι y') : y = y' := by
  have hy : y ∈ ι x ∪ ι y' := by rw [← h]; exact Or.inr rfl
  have hy' : y' ∈ ι x ∪ ι y := by rw [h]; exact Or.inr rfl
  rcases hy with hy | hy
  · rcases hy' with hy' | hy'
    · exact (mem_unitCls.1 hy).trans (mem_unitCls.1 hy').symm
    · exact (mem_unitCls.1 hy').symm
  · exact mem_unitCls.1 hy

/-- A cardinal of the form `sm''Nc'α`, when it exists, is `Nc'α`. -/
private theorem nc_of_mem {A : Set α} {B : Set β} (h : B ∈ nc β A) :
    (sm ʻʻ nc β A : Set (Set γ)) = nc γ A := by
  ext X
  constructor
  · rintro ⟨Y, hY, hXY⟩; exact sm_trans hXY hY
  · intro hX; exact ⟨B, h, sm_trans hX (sm_symm h)⟩

end Helpers

/-!
## [✱100] Definition and elementary properties of cardinal numbers

*(Vol. 2, p. 13)*

> *Summary of* *100.
>
> In this number we shall be concerned only with such immediate consequences of the definition of cardinal numbers as do not require typical definiteness, beyond what the inherent conditions of significance may bestow. We introduce here the fundamental definitions:
>
> *100·01. \(\text{Nc} = \overrightarrow{\text{ sm }} \quad\text{Df}\)
>
> *100·02. \(\text{NC} = \text{D}ʻ\text{Nc} \quad\text{Df}\)
>
> The definition "\(\text{Nc}\)" is required chiefly for the sake of the descriptive function \(\text{Nc}ʻ\alpha\). We have
>
> *100·1. \(\vdash .\text{Nc}ʻ\alpha = \hat{\beta}(\beta\,\text{ sm }\,\alpha) = \hat{\beta}(\alpha\,\text{ sm }\,\beta)\)
>
> This may be stated in various equivalent forms, which are given at the beginning of this number (*100·1—·16). After a few propositions on \(\text{Nc}\) as a relation, we proceed to the elementary properties of \(\text{Nc}ʻ\alpha\). We have
>
> *100·3. \(\vdash .\alpha \in \text{Nc}ʻ\alpha\)
>
> *100·31. \(\vdash :\alpha \in \text{Nc}ʻ\beta . \equiv . \beta \in \text{Nc}ʻ\alpha . \equiv . \alpha \text{ sm } \beta\)
>
> *100·321. \(\vdash : \alpha\,\text{ sm }\,\beta . \supset . \text{Nc}ʻ\alpha = \text{Nc}ʻ\beta\)
>
> …

**Lean reading.** (Conventions: `Defs/Part3.lean`, "Encoding decisions: types".) `Nc'α` is
`nc γ A`, the classes of `γ`-things similar to `A : Set β`; its actual type `γ` is an explicit
argument, and an unconstrained one is a type parameter of the theorem (the form is asserted for
every determination). The relation `Nc` is `Rfwd sm`. `NC` is `NC β`: the type `β` of the
classes whose numbers are in question is explicit, and `μ, ν ∈ NC` is `μ ∈ NC β ∧ ν ∈ NC β'`
with independent `β`, `β'` (Prefatory Statement, V). The types of the several occurrences of
`Nc'α` in one enunciation are fixed by significance and by convention IT (Prefatory Statement,
IV): all logical occurrences share one type parameter; argumental occurrences (`sm''Nc'α`) share
it too, and then the equational occurrences are free (✱100·511); without argumental occurrences
the equational occurrences share the logical type (✱100·35); an attributive occurrence
`β ∈ Nc'α` is in the type of `β` (`B ∈ nc β' A` for `B : Set β'`); see ✱100·35, PM's own
example. Convention AT is not applied in ✱100 (the Prefatory Statement, VI, shows its effect on
✱100·35: `pm100_35_aux_AT`). ✱100·01·02·1·2·3·35·4·42·511 are finished; they are the worked
examples of these conventions for the Part III Section agents. Where an `NC` must have the
converse-domain type of a particular class for the proposition to hold (✱100·41·52·53), PM's proof
fixes it and the status says so. The equivalent forms ✱100·11–·16 are stated with the apparent
relation `R` between the type of `α` and the actual type `γ`; `R'x = R'y` is a pair of
descriptions (Basic §5). `∈_Δ'ι'α` is `sel memRel (ι A)`, `D''…` is `D ʻʻ …`.

**Status.** proved (all propositions; ✱100·01·02 definition; ✱100·35, ✱100·511 proved (reading):
convention IT; ✱100·41, ✱100·52, ✱100·53 proved (reading): the converse-domain type of `NC` is the
one PM's proof uses, see their docstrings)
-/

/-- ✱100·01 (Df). \(\text{Nc}=\overrightarrow{\text{ sm }} \quad\text{Df}\)

`Nc` is typically ambiguous in its domain (cardinals whose members are classes of `γ`) and in its
converse domain (classes of `β`): both are type parameters. -/
theorem pm100_01 {γ : Type*} {β : Type*} : (Nc : Set (Set γ) → Set β → Prop) = Rfwd sm := rfl

/-- ✱100·02 (Df). \(\text{NC}=\text{D}ʻ\text{Nc} \quad \text{Df}\)

The definiens is the descriptive function `D'Nc`, so the statement keeps the description (Basic
§5). The type `β` of the converse domain of `Nc` is the explicit argument of `NC`. -/
theorem pm100_02 {γ : Type*} {β : Type*} :
    Desc D (Nc : Set (Set γ) → Set β → Prop) (fun K => NC β = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱100·1. \(\vdash .\text{Nc}ʻ\alpha =\hat{\beta}(\beta\, \text{ sm }\,\alpha)=\hat{\beta}(\alpha\, \text{ sm }\,\beta) \quad[*32·13.*73·31.(*100·01)]\)

`Nc'α` is written with its value function `nc γ A` (the descriptive function always exists,
✱100·2); the actual type `γ` is a type parameter, and `β̂` ranges over `Set γ`. The chain of
identities is the conjunction of its links. -/
theorem pm100_1 {γ : Type*} {β : Type*} {A : Set β} :
    nc γ A = {B | sm B A} ∧ {B : Set γ | sm B A} = {B | sm A B} :=
  ⟨rfl, Set.ext fun _ => ⟨sm_symm, sm_symm⟩⟩

/-- ✱100·11. \(\vdash .\text{Nc}ʻ\alpha =\hat{\beta}\{(\exists R).R\in 1\rightarrow 1.\text{D}ʻR=\alpha .\text{ᗡ}ʻR=\beta\} \quad[*100·1.*73·1]\)

The apparent variable `R` is a relation from the type of `α` to the actual type `γ` of the
members of `Nc'α` (significance); the product after `(∃R)` brackets to the left. -/
theorem pm100_11 {γ β : Type*} {A : Set β} :
    nc γ A = {B | ∃ R : β → γ → Prop, (R ∈ arrow one one ∧ dom R = A) ∧ codom R = B} := by
  ext B
  constructor
  · intro h
    obtain ⟨R, ⟨h1, h2⟩, h3⟩ := sm_iff.1 (sm_symm (mem_nc.1 h))
    exact ⟨R, ⟨h1, h2.symm⟩, h3.symm⟩
  · rintro ⟨R, ⟨h1, h2⟩, h3⟩
    exact mem_nc.2 (sm_symm (sm_iff.2 ⟨R, ⟨h1, h2.symm⟩, h3.symm⟩))

/-- ✱100·12. \(\vdash . \text{Nc}ʻ\alpha =\hat{\beta}\{(\exists R).R\in 1\rightarrow 1.\alpha \subset \text{D}ʻR.\beta =\breve{R}ʻʻ\alpha\} \quad[*100·1.*73·11]\) -/
theorem pm100_12 {γ β : Type*} {A : Set β} :
    nc γ A = {B | ∃ R : β → γ → Prop, (R ∈ arrow one one ∧ A ⊆ dom R) ∧ B = R˘ ʻʻ A} := by
  ext B
  constructor
  · intro h
    obtain ⟨R, ⟨h1, rfl⟩, rfl⟩ := sm_iff.1 (sm_symm (mem_nc.1 h))
    refine ⟨R, ⟨h1, subset_rfl⟩, ?_⟩
    ext y
    exact ⟨fun ⟨x, hx⟩ => ⟨x, ⟨y, hx⟩, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
  · rintro ⟨R, ⟨h1, h2⟩, rfl⟩
    exact mem_nc.2 (sm_symm (sm_cnv_img h1 h2))

/-- ✱100·13. \(\vdash .\text{Nc}ʻ\alpha =\text{ᗡ}ʻʻ(1\rightarrow 1\cap \overleftarrow{\text{D}}ʻ\alpha )=\text{D}ʻʻ(1\rightarrow 1\cap \overleftarrow{\text{ᗡ}}ʻ\alpha)\)

`ᗡ''(1 → 1 ∩ D⃖'α)` is `Dcnv ʻʻ (arrow one one ∩ rels D A)` (the relations of the image are
determined by significance: from the type of `α` to the actual type `γ`), and
`D''(1 → 1 ∩ ᗡ⃖'α)` likewise with relations from `γ` to the type of `α`. The chain is the
conjunction of its links. -/
theorem pm100_13 {γ β : Type*} {A : Set β} :
    nc γ A = (Dcnv ʻʻ (arrow one one ∩ rels D A) : Set (Set γ)) ∧
      (Dcnv ʻʻ (arrow one one ∩ rels D A) : Set (Set γ)) = D ʻʻ (arrow one one ∩ rels Dcnv A) := by
  have h1 : nc γ A = (Dcnv ʻʻ (arrow one one ∩ rels D A) : Set (Set γ)) := by
    ext B
    constructor
    · intro h
      obtain ⟨R, ⟨h1, h2⟩, h3⟩ := sm_iff.1 (sm_symm (mem_nc.1 h))
      exact ⟨R, ⟨h1, h2⟩, h3⟩
    · rintro ⟨R, ⟨h1, h2⟩, h3⟩
      exact mem_nc.2 (sm_symm (sm_iff.2 ⟨R, ⟨h1, h2⟩, h3⟩))
  refine ⟨h1, ?_⟩
  rw [← h1]
  ext B
  constructor
  · intro h
    obtain ⟨R, ⟨h1, h2⟩, h3⟩ := sm_iff.1 (mem_nc.1 h)
    exact ⟨R, ⟨h1, h3⟩, h2⟩
  · rintro ⟨R, ⟨h1, h2⟩, h3⟩
    exact mem_nc.2 (sm_iff.2 ⟨R, ⟨h1, h3⟩, h2⟩)

/-- ✱100·14. \(\vdash .\text{Nc}ʻ\alpha =\hat{\beta} \{(\exists R).\alpha \subset \text{ᗡ}ʻR.R\upharpoonright \alpha \in 1\rightarrow 1.\beta = Rʻʻ\alpha\} \quad [*73·15.*100·1]\) -/
theorem pm100_14 {γ β : Type*} {A : Set β} :
    nc γ A = {B | ∃ R : γ → β → Prop, (A ⊆ codom R ∧ R ↾ A ∈ arrow one one) ∧ B = R ʻʻ A} := by
  ext B
  constructor
  · intro h
    obtain ⟨R, ⟨h1, rfl⟩, rfl⟩ := sm_iff.1 (mem_nc.1 h)
    refine ⟨R, ⟨subset_rfl, ?_⟩, ?_⟩
    · obtain ⟨h2, h3⟩ := mem_arrow_one_one.1 h1
      exact mem_arrow_one_one.2 ⟨fun x y z ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => h2 x y z ⟨hx, hy⟩,
        fun x y z ⟨⟨hy, _⟩, ⟨hz, _⟩⟩ => h3 x y z ⟨hy, hz⟩⟩
    · ext x
      exact ⟨fun ⟨y, hy⟩ => ⟨y, ⟨x, hy⟩, hy⟩, fun ⟨y, _, hy⟩ => ⟨y, hy⟩⟩
  · rintro ⟨R, ⟨h1, h2⟩, rfl⟩
    exact mem_nc.2 (sm_img_cres h1 h2)

/-- ✱100·15. \(\vdash .\text{Nc}ʻ\alpha =\hat{\beta} \{(\exists R):\text{E}!!Rʻʻ\alpha : x,y\in \alpha .Rʻx=Rʻy.\supset _{x,y}.x=y:\beta =Rʻʻ\alpha\}\)

`E!!R''α` is `EE R A`; `R'x = R'y` has two descriptions, the first with the larger scope, each
with the smallest scope that contains it (Basic §5), i.e. the equation itself. -/
theorem pm100_15 {γ β : Type*} {A : Set β} :
    nc γ A = {B | ∃ R : γ → β → Prop,
      (EE R A ∧ ∀ x y, (x ∈ A ∧ y ∈ A) ∧ Desc R x (fun u => Desc R y (fun v => u = v)) →
        x = y) ∧ B = R ʻʻ A} := by
  rw [pm100_14]
  ext B
  exact exists_congr fun R => and_congr_left' cond14_iff_cond15

/-- ✱100·16. \(\vdash .\text{Nc}ʻ\alpha =\hat{\beta} \{(\exists R)\colon\ldotp x,y\in \alpha .\supset _{x,y}:Rʻx=Rʻy.\equiv .x=y\colon\ldotp \beta =Rʻʻ\alpha\}\) -/
theorem pm100_16 {γ β : Type*} {A : Set β} :
    nc γ A = {B | ∃ R : γ → β → Prop,
      (∀ x y, x ∈ A ∧ y ∈ A → (Desc R x (fun u => Desc R y (fun v => u = v)) ↔ x = y)) ∧
        B = R ʻʻ A} := by
  rw [pm100_14]
  ext B
  exact exists_congr fun R => and_congr_left' cond14_iff_cond16

/-- ✱100·2. \(\vdash .\text{E}!\text{Nc}ʻ\alpha \quad[*32·12.(*100·01)]\)

PM proves that the descriptive function exists, so the statement keeps `E!` (Basic §5). -/
theorem pm100_2 {γ : Type*} {β : Type*} {A : Set β} :
    EDesc (Nc : Set (Set γ) → Set β → Prop) A :=
  EDesc_Nc A

/-- ✱100·21. \(\vdash .\text{ᗡ}ʻ\text{Nc} = \text{Cls}\)

`ᗡ'Nc` is `codom Nc` (`ᗡ` is `graph codom`); `Cls` is the class of all classes of the type of
the converse domain. -/
theorem pm100_21 {γ β : Type*} : codom (Nc : Set (Set γ) → Set β → Prop) = Cls := by
  rw [Cls_eq_univ]
  exact Set.eq_univ_of_forall fun B => ⟨nc γ B, rfl⟩

/-- ✱100·22. \(\vdash .\text{Nc}\in 1\rightarrow \text{Cls} \quad[*72·12.(*100·01)]\) -/
theorem pm100_22 {γ β : Type*} : (Nc : Set (Set γ) → Set β → Prop) ∈ arrow one Cls :=
  mem_arrow_one_Cls.2 fun _ _ _ ⟨hx, hy⟩ => hx.trans hy.symm

/-- ✱100·3. \(\vdash .\alpha \in \text{Nc}ʻ\alpha \quad[*73·3.*100·1]\)

"Here `Nc` must mean `Nc(α_α)`" (Summary of Section A): significance puts this attributive
occurrence of `Nc'α` in the type of `α`. (One may *not* infer `∃!Nc'α` in an arbitrary type.) -/
theorem pm100_3 {α : Type*} {A : Set α} : A ∈ nc α A := self_mem_nc A

/-- ✱100·31. \(\vdash :\alpha \in \text{Nc}ʻ\beta .\equiv .\beta \in \text{Nc}ʻ\alpha .\equiv .\alpha\,\text{ sm }\,\beta \quad[*32·18.*73·31.(*100·01)]\)

Both occurrences of `Nc` are attributive: `α ∈ Nc'β` is in the type of `α`, `β ∈ Nc'α` in the
type of `β` (Prefatory Statement, IV; cf. ✱100·35). -/
theorem pm100_31 {α β : Type*} {A : Set α} {B : Set β} :
    (A ∈ nc α B ↔ B ∈ nc β A) ∧ (B ∈ nc β A ↔ sm A B) :=
  ⟨⟨sm_symm, sm_symm⟩, ⟨sm_symm, sm_symm⟩⟩

/-- ✱100·32. \(\vdash :\alpha \in \text{Nc}ʻ\beta .\beta \in \text{Nc}ʻ\gamma .\supset .\alpha \in \text{Nc}ʻ\gamma \quad[*100·31.*73·32]\) -/
theorem pm100_32 {α β γ : Type*} {A : Set α} {B : Set β} {G : Set γ} :
    A ∈ nc α B ∧ B ∈ nc β G → A ∈ nc α G :=
  fun ⟨h1, h2⟩ => sm_trans h1 h2

/-- ✱100·321. \(\vdash :\alpha\,\text{ sm }\,\beta .\supset .\text{Nc}ʻ\alpha =\text{Nc}ʻ\beta\)

The equation is in an arbitrary type `γ` ("Nc'α = Nc'β" holds in every type). -/
theorem pm100_321 {α β γ : Type*} {A : Set α} {B : Set β} : sm A B → nc γ A = nc γ B :=
  nc_eq_nc_of_sm

/-- ✱100·33. \(\vdash :\exists !\text{Nc}ʻ\alpha \cap \text{Nc}ʻ\beta .\supset .\alpha \,\text{ sm }\,\beta\)

The two logical occurrences are in one type `γ` (convention IT). -/
theorem pm100_33 {α β γ : Type*} {A : Set α} {B : Set β} :
    (nc γ A ∩ nc γ B).Nonempty → sm A B :=
  fun ⟨_, h1, h2⟩ => sm_of_mem_nc_of_mem_nc h1 h2

/-- ✱100·34. \(\vdash : \exists ! \text{Nc}ʻ\alpha \cap \text{Nc}ʻ\beta . \supset . \text{Nc}ʻ\alpha = \text{Nc}ʻ\beta \quad[*100·33·321]\)

The logical and equational occurrences are in one type `γ` (convention IT: there are no
argumental occurrences). -/
theorem pm100_34 {α β γ : Type*} {A : Set α} {B : Set β} :
    (nc γ A ∩ nc γ B).Nonempty → nc γ A = nc γ B :=
  fun h => nc_eq_nc_of_sm (pm100_33 h)

/-- ✱100·35. \[\begin{aligned}\vdash \colon\ldotp \exists ! \text{Nc}ʻ\alpha . \lor . &\exists ! \text{Nc}ʻ\beta : \supset:\\ &\text{Nc}ʻ\alpha = \text{Nc}ʻ\beta . \equiv . \alpha \in \text{Nc}ʻ\beta . \equiv . \beta \in \text{Nc}ʻ\alpha . \equiv . \alpha \,\text{ sm }\, \beta \end{aligned}\]

The worked example of convention IT. The Prefatory Statement (IV) says that ✱100·35 "is to mean"
`∃!Nc(ξ)'α ∨ ∃!Nc(ξ)'β : ⊃ : Nc(ξ)'α = Nc(ξ)'β ≡ α ∈ Nc(α)'β ≡ β ∈ Nc(β)'α ≡ α sm β`: the
logical and equational occurrences of `Nc'α` and `Nc'β` are in one type (`γ`), the attributive
ones in the types of `α` and `β` (`nc α B`, `nc β A`). The chain of four equivalences is the
conjunction of its three links, bracketed to the left (✱4·02).

**Status.** proved (reading): convention IT (Prefatory Statement, IV): the logical and
equational occurrences of `Nc'α`, `Nc'β` share one type parameter `γ`; the attributive ones are
in the types of `α` and `β`, as PM's own reading of ✱100·35 states. -/
theorem pm100_35 {α β γ : Type*} {A : Set α} {B : Set β} :
    (nc γ A).Nonempty ∨ (nc γ B).Nonempty →
      (((nc γ A = nc γ B ↔ A ∈ nc α B) ∧ (A ∈ nc α B ↔ B ∈ nc β A)) ∧
        (B ∈ nc β A ↔ sm A B)) := by
  intro h
  have hAB : nc γ A = nc γ B ↔ sm A B := by
    rcases h with h | h
    · exact nc_eq_nc_iff h
    · rw [eq_comm, nc_eq_nc_iff h]
      exact ⟨sm_symm, sm_symm⟩
  have h1 : A ∈ nc α B ↔ sm A B := Iff.rfl
  have h2 : B ∈ nc β A ↔ sm A B := ⟨sm_symm, sm_symm⟩
  exact ⟨⟨hAB.trans h1.symm, h1.trans h2.symm⟩, h2⟩

/-- The form of ✱100·35 under convention AT (Prefatory Statement, VI): "If we apply AT to this, we can
write `⊢ : Nc'α = Nc'β . ≡ . α ∈ Nc'β . ≡ . β ∈ Nc'α . ≡ . α sm β`. For the equational
occurrences of `Nc'α` and `Nc'β` are by AT and IIT to be with adequate actual types." The
worked example of convention AT: the type `γ` of the equation gets the adequacy hypotheses of
both sides (`AdeqNc γ A`, `AdeqNc γ B`, Prefatory Statement, II (i)), and the existential
hypothesis disappears. Not a separate proposition of PM (PM's ✱100·35 is `pm100_35`); a
proposition to which PM applies AT (✱103·16, ✱110·71·72, ✱117) is stated in this form, with
**Status.** `proved (reading): convention AT, Prefatory Statement`. -/
theorem pm100_35_aux_AT {α β γ : Type*} {A : Set α} {B : Set β} (hA : AdeqNc γ A)
    (_hB : AdeqNc γ B) :
    ((nc γ A = nc γ B ↔ A ∈ nc α B) ∧ (A ∈ nc α B ↔ B ∈ nc β A)) ∧ (B ∈ nc β A ↔ sm A B) :=
  pm100_35 (Or.inl (hA.nc_nonempty A))

/-- ✱100·36. \(\vdash \colon\ldotp \beta \in \text{Nc}ʻ\alpha . \supset : \exists ! \alpha . \equiv . \exists !\beta \quad[*100·31.*73·36]\) -/
theorem pm100_36 {α β : Type*} {A : Set α} {B : Set β} :
    B ∈ nc β A → (A.Nonempty ↔ B.Nonempty) := by
  intro h
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(e.symm ⟨a, ha⟩ : β), (e.symm ⟨a, ha⟩).2⟩
  · rintro ⟨b, hb⟩
    exact ⟨(e ⟨b, hb⟩ : α), (e ⟨b, hb⟩).2⟩

/-- ✱100·4. \(\vdash : \mu \in \text{NC} . \equiv . (\exists \alpha) . \mu = \text{Nc}ʻ\alpha \quad[*37·78·79.(*100·02·01)]\)

The apparent variable `α` ranges over the classes of the type `β` of the converse domain of
`Nc` in `NC` (encoding decision 3 of `Defs/Part3`). -/
theorem pm100_4 {γ : Type*} {β : Type*} {μ : Set (Set γ)} :
    μ ∈ NC β ↔ ∃ A : Set β, μ = nc γ A :=
  Iff.rfl

/-- ✱100·41. \(\vdash . \text{Nc}ʻ\alpha \in \text{NC} \quad[*100·4·2.*14·204]\)

**Status.** proved (reading): the converse domain of `NC` (`NC β`, encoding decision 3 of
`Defs/Part3`) is taken in the type of `α`, as PM's proof by ✱100·4·2 shows (the `Nc` of `Nc'α`
is the `Nc` whose domain is `NC`); with an independent converse-domain type the proposition can
fail (`NC Empty` contains only `Nc'Λ`). -/
theorem pm100_41 {γ β : Type*} {A : Set β} : nc γ A ∈ NC β := nc_mem_NC A

/-- ✱100·42. \(\vdash : \mu,\nu \in \text{NC} . \exists !\mu \cap \nu . \supset . \mu = \nu\)

The worked example of the ambiguity of `NC` (Prefatory Statement, V): "`μ, ν ∈ NC`" stands for
`μ ∈ NC . ν ∈ NC` "and therefore as not necessarily identifying the types of `μ` and `ν`": the
converse domains of the two `NC`s are of independent types `β`, `β'`; `μ ∩ ν` (significance)
puts `μ` and `ν` themselves in one type. The antecedent is the product of three, bracketed to
the left. -/
theorem pm100_42 {γ β β' : Type*} {μ ν : Set (Set γ)} :
    (μ ∈ NC β ∧ ν ∈ NC β') ∧ (μ ∩ ν).Nonempty → μ = ν := by
  rintro ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, C, hCA, hCB⟩
  exact nc_eq_nc_of_sm (sm_of_mem_nc_of_mem_nc hCA hCB)

/-- ✱100·43. \(\vdash . \text{NC} \in \text{Cls}^{2} \text{excl} \quad[*100·42.*84·11]\) -/
theorem pm100_43 {γ β : Type*} : (NC β : Set (Set (Set γ))) ∈ Cls2excl := by
  show ∀ μ ν, (μ ∈ NC β ∧ ν ∈ NC β) ∧ μ ≠ ν → μ ∩ ν = Λ
  rintro μ ν ⟨hμν, hne⟩
  rw [Null_eq_empty]
  by_contra h
  exact hne (pm100_42 ⟨hμν, Set.nonempty_iff_ne_empty.2 h⟩)

/-- ✱100·44. \(\vdash \colon\ldotp \mu \in \text{NC}. \exists ! \text{Nc}ʻ\alpha . \supset : \alpha \in \mu . \equiv . \text{Nc}ʻ\alpha = \mu\)

`α ∈ μ` puts `α` in the type of the members of `μ`; the logical occurrence `∃!Nc'α` is bound to
the equational one `Nc'α = μ`, which is in the type of `μ` (convention IT). -/
theorem pm100_44 {γ β : Type*} {μ : Set (Set γ)} {A : Set γ} :
    μ ∈ NC β ∧ (nc γ A).Nonempty → (A ∈ μ ↔ nc γ A = μ) := by
  rintro ⟨⟨B, rfl⟩, -⟩
  exact ⟨fun h => nc_eq_nc_of_sm h, fun h => h ▸ self_mem_nc A⟩

/-- ✱100·45. \(\vdash : \mu \in \text{NC} . \alpha \in \mu . \supset . \text{Nc}ʻ\alpha = \mu \quad[*100·4·31·321]\) -/
theorem pm100_45 {γ β : Type*} {μ : Set (Set γ)} {A : Set γ} :
    μ ∈ NC β ∧ A ∈ μ → nc γ A = μ := by
  rintro ⟨⟨B, rfl⟩, h⟩
  exact nc_eq_nc_of_sm h

/-- ✱100·5. \(\vdash : \mu \in \text{NC} . \alpha ,\beta \in \mu . \supset . \alpha \,\text{ sm }\, \beta\) -/
theorem pm100_5 {γ δ : Type*} {μ : Set (Set γ)} {A B : Set γ} :
    μ ∈ NC δ ∧ (A ∈ μ ∧ B ∈ μ) → sm A B := by
  rintro ⟨⟨C, rfl⟩, h1, h2⟩
  exact sm_trans h1 (sm_symm h2)

/-- ✱100·51. \(\vdash : \mu \in \text{NC} . \alpha \in \mu . \supset . \text{ sm }ʻʻ\mu = \text{Nc}ʻ\alpha\)

"`sm''μ` is a typically ambiguous symbol, which will represent in any type the 'same' number as
`μ`" (Summary): the equation is in an arbitrary type `δ`. -/
theorem pm100_51 {γ β δ : Type*} {μ : Set (Set γ)} {A : Set γ} :
    μ ∈ NC β ∧ A ∈ μ → (sm ʻʻ μ : Set (Set δ)) = nc δ A := by
  rintro ⟨⟨B, rfl⟩, hA⟩
  ext X
  constructor
  · rintro ⟨Y, hY, hXY⟩
    exact sm_trans hXY (sm_trans hY (sm_symm hA))
  · intro h
    exact ⟨A, hA, h⟩

/-- ✱100·511. \(\vdash : \exists ! \text{Nc}ʻ\beta . \supset . \text{ sm }ʻʻ\text{Nc}ʻ\beta = \text{Nc}ʻ\beta\)

The worked example of convention IT with an argumental occurrence (Prefatory Statement, III–IV):
the first occurrence of `Nc'β` is logical, the second argumental, the third equational; IT binds
the argumental occurrence to the logical one (one type `γ`), and since there is an argumental
occurrence it does not bind the equational one, which with `sm''Nc'β` (opposed sides) is in a
type `δ`: "the last `Nc'β` may be of a different type from the others: the proposition holds
however its type is determined" (PM).

**Status.** proved (reading): convention IT (Prefatory Statement, IV): the logical and the
argumental occurrences of `Nc'β` share one type parameter `γ`; the equation is in an independent
type `δ`, as PM's note states. -/
theorem pm100_511 {β γ δ : Type*} {B : Set β} :
    (nc γ B).Nonempty → (sm ʻʻ nc γ B : Set (Set δ)) = nc δ B := by
  rintro ⟨C, hC⟩
  ext X
  constructor
  · rintro ⟨Y, hY, hXY⟩
    exact sm_trans hXY hY
  · intro h
    exact ⟨C, hC, sm_trans h (sm_symm hC)⟩

/-- ✱100·52. \(\vdash : \mu \in \text{NC} . \exists ! \mu . \supset . \text{ sm }ʻʻ\mu \in \text{NC} \quad[*100·51·4]\)

**Status.** proved (reading): the converse domain of the second `NC` is taken in the type of the
members of `μ`, as PM's proof by ✱100·51·4 (`sm''μ = Nc'α` with `α ∈ μ`) requires; with an
independent type it can fail (e.g. `NC Empty` contains only `Nc'Λ`). The first `NC` has an
independent converse-domain type `β`. -/
theorem pm100_52 {γ β δ : Type*} {μ : Set (Set γ)} :
    μ ∈ NC β ∧ μ.Nonempty → (sm ʻʻ μ : Set (Set δ)) ∈ NC γ := by
  rintro ⟨hμ, A, hA⟩
  rw [pm100_51 ⟨hμ, hA⟩]
  exact nc_mem_NC A

/-- ✱100·521. \(\vdash : \mu \in \text{NC} . \exists ! \text{ sm }ʻʻ\mu . \supset . \text{ sm }ʻʻ\text{ sm }ʻʻ\mu = \mu\)

The logical occurrence `∃!sm''μ` and the argumental one in `sm''sm''μ` are in one type `δ`
(convention IT); the outer `sm''` is in the type of `μ` (the equation). -/
theorem pm100_521 {γ β δ : Type*} {μ : Set (Set γ)} :
    μ ∈ NC β ∧ (sm ʻʻ μ : Set (Set δ)).Nonempty → sm ʻʻ (sm ʻʻ μ : Set (Set δ)) = μ := by
  rintro ⟨hμ, X, Y, hY, hXY⟩
  rw [pm100_51 ⟨hμ, hY⟩, pm100_511 ⟨X, hXY⟩]
  exact pm100_45 ⟨hμ, hY⟩

/-- ✱100·53. \(\vdash \colon\ldotp \exists !\mu . \exists !\nu . \supset : \mu \in \text{NC} . \nu = \text{ sm }ʻʻ\mu . \equiv . \nu \in \text{NC} . \mu = \text{ sm }ʻʻ\nu\)

**Status.** proved (reading): the converse domain of the `NC` in `μ ∈ NC` is the type of the
members of `ν`, and that of the `NC` in `ν ∈ NC` the type of the members of `μ`, as PM's proof
(by ✱100·52 and its converse) requires; with independent types the equivalence can fail. -/
theorem pm100_53 {γ δ : Type*} {μ : Set (Set γ)} {ν : Set (Set δ)} :
    μ.Nonempty ∧ ν.Nonempty → (μ ∈ NC δ ∧ ν = sm ʻʻ μ ↔ ν ∈ NC γ ∧ μ = sm ʻʻ ν) := by
  rintro ⟨hμ, hν⟩
  constructor
  · rintro ⟨h1, rfl⟩
    exact ⟨pm100_52 ⟨h1, hμ⟩, (pm100_521 ⟨h1, hν⟩).symm⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨pm100_52 ⟨h1, hν⟩, (pm100_521 ⟨h1, hμ⟩).symm⟩

/-- ✱100·6. \(\vdash .\iotaʻʻ\alpha \in \text{Nc}ʻ\alpha \quad[*73·41.*100·31]\)

`ι''α` is `iota ʻʻ A`; the attributive `Nc'α` is in the type of `ι''α`. -/
theorem pm100_6 {α : Type*} {A : Set α} : iota ʻʻ A ∈ nc (Set α) A := sm_iota_img A

/-- ✱100·61. \(\vdash .\hat{\beta}\{(\exists y).y \in \alpha .\beta = \iota ʻx \cup \iota ʻy\} \in \text{Nc}ʻ\alpha \quad [*73·27.*54·21.*100·31]\) -/
theorem pm100_61 {α : Type*} {A : Set α} {x : α} :
    {B | ∃ y, y ∈ A ∧ B = ι x ∪ ι y} ∈ nc (Set α) A := by
  show sm (graph (fun y => ι x ∪ ι y) ʻʻ A) A
  refine sm_graph_img fun y _ y' _ h => ?_
  have h' : ι x ∪ ι y = ι x ∪ ι y' := h
  have hy : y ∈ ι x ∪ ι y' := by rw [← h']; exact Or.inr rfl
  have hy' : y' ∈ ι x ∪ ι y := by rw [h']; exact Or.inr rfl
  rcases hy with hy | hy
  · rcases hy' with hy' | hy'
    · exact (mem_unitCls.1 hy).trans (mem_unitCls.1 hy').symm
    · exact (mem_unitCls.1 hy').symm
  · exact mem_unitCls.1 hy

/-- ✱100·62. \(\vdash .x\downarrow ʻʻ\alpha \in \text{Nc}ʻ\alpha \quad[*73·61.*100·31]\)

`x↓''α` is `coupleL x ʻʻ A`. -/
theorem pm100_62 {α β : Type*} {A : Set α} {x : β} : coupleL x ʻʻ A ∈ nc (β → α → Prop) A :=
  sm_graph_img (f := couple x) fun _ _ _ _ h => (couple_eq_couple_iff.1 h).2

/-- ✱100·621. \(\vdash .\downarrow xʻʻ\alpha \in \text{Nc}ʻ\alpha \quad[*73·611.*100·31]\)

`↓x''α` is `coupleR x ʻʻ A`. -/
theorem pm100_621 {α β : Type*} {A : Set α} {x : β} : coupleR x ʻʻ A ∈ nc (α → β → Prop) A :=
  sm_graph_img (f := fun y => couple y x) fun _ _ _ _ h => (couple_eq_couple_iff.1 h).1

/-- ✱100·63. \(\vdash .\in_{\Delta }ʻ\iota ʻ\alpha \in \text{Nc}ʻ\alpha \quad[*83·41.*100·31]\)

The e-text's `∈_Δ'ι'α` is the class of `∈`-selections from `ι'α` (`sel memRel (ι A)`), i.e. the
couples `x ↓ α` with `x ∈ α` (✱83·41). -/
theorem pm100_63 {α : Type*} {A : Set α} : sel memRel (ι A) ∈ nc (α → Set α → Prop) A := by
  have h : sel memRel (ι A) = coupleR A ʻʻ A := by
    ext M
    rw [mem_sel_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hA : A ∈ codom M := by rw [h3]; exact mem_unitCls.2 rfl
      obtain ⟨x, hx⟩ := hA
      refine ⟨x, h2 x A hx, ?_⟩
      show M = x ↓ A
      funext u B
      apply propext
      constructor
      · intro hu
        have hB : B = A := by
          have : B ∈ codom M := ⟨u, hu⟩
          rw [h3] at this
          exact this
        rw [hB] at hu
        exact (couple_apply x A u B).2 ⟨(mem_arrow_one_Cls.1 h1) u x A ⟨hu, hx⟩, hB⟩
      · intro h
        obtain ⟨rfl, rfl⟩ := (couple_apply x A u B).1 h
        exact hx
    · rintro ⟨x, hx, hM⟩
      have hM' : M = x ↓ A := hM
      subst hM'
      refine ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩
      · intro u v B ⟨hu, hv⟩
        exact ((couple_apply x A u B).1 hu).1.trans ((couple_apply x A v B).1 hv).1.symm
      · intro u B h
        obtain ⟨rfl, rfl⟩ := (couple_apply x A u B).1 h
        exact hx
      · ext B
        exact ⟨fun ⟨u, h⟩ => ((couple_apply x A u B).1 h).2,
          fun hB => ⟨x, (couple_apply x A x B).2 ⟨rfl, hB⟩⟩⟩
  rw [h]
  exact pm100_621

/-- ✱100·631. \(\vdash .\text{D}ʻʻ{\in}_{\Delta}ʻ\iota ʻ\alpha \in \text{Nc}ʻ\alpha \quad[*83·7.*100·6]\) -/
theorem pm100_631 {α : Type*} {A : Set α} : D ʻʻ sel memRel (ι A) ∈ nc (Set α) A := by
  have h : D ʻʻ sel memRel (ι A) = iota ʻʻ A := by
    ext X
    constructor
    · rintro ⟨M, hM, rfl⟩
      obtain ⟨⟨h1, h2⟩, h3⟩ := mem_sel_iff.1 hM
      have hA : A ∈ codom M := by rw [h3]; exact mem_unitCls.2 rfl
      obtain ⟨x, hx⟩ := hA
      refine ⟨x, h2 x A hx, ?_⟩
      show dom M = ι x
      ext u
      constructor
      · rintro ⟨B, hu⟩
        have hB : B = A := by
          have : B ∈ codom M := ⟨u, hu⟩
          rw [h3] at this
          exact this
        subst hB
        exact (mem_arrow_one_Cls.1 h1) u x B ⟨hu, hx⟩
      · intro hu
        rw [mem_unitCls.1 hu]
        exact ⟨A, hx⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x ↓ A, mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩, ?_⟩
      · intro u v B ⟨hu, hv⟩
        exact ((couple_apply x A u B).1 hu).1.trans ((couple_apply x A v B).1 hv).1.symm
      · intro u B h
        obtain ⟨rfl, rfl⟩ := (couple_apply x A u B).1 h
        exact hx
      · ext B
        exact ⟨fun ⟨u, h⟩ => ((couple_apply x A u B).1 h).2,
          fun hB => ⟨x, (couple_apply x A x B).2 ⟨rfl, hB⟩⟩⟩
      · show ι x = dom (x ↓ A)
        ext u
        exact ⟨fun hu => ⟨A, (couple_apply x A u A).2 ⟨hu, rfl⟩⟩,
          fun ⟨B, h⟩ => ((couple_apply x A u B).1 h).1⟩
  rw [h]
  exact pm100_6

/-- ✱100·64. \(\vdash :\kappa \in \text{Cls}^{2} \text{excl} .\supset . \text{D}ʻʻ\in_{\Delta }ʻ\kappa \subset \text{Nc}ʻ\kappa\)

`Nc'κ` is attributive, in the type of the members of `D''∈_Δ'κ`, i.e. of the members of the
members of `κ`. -/
theorem pm100_64 {α : Type*} {K : Set (Set α)} :
    K ∈ Cls2excl → D ʻʻ sel memRel K ⊆ nc α K := by
  rintro hK X ⟨M, hM, rfl⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_sel_iff.1 hM
  refine sm_iff.2 ⟨M, ⟨mem_arrow_one_one.2 ⟨mem_arrow_one_Cls.1 h1, ?_⟩, rfl⟩, h3.symm⟩
  rintro x B C ⟨hB, hC⟩
  by_contra hne
  have hBK : B ∈ K := by rw [← h3]; exact ⟨x, hB⟩
  have hCK : C ∈ K := by rw [← h3]; exact ⟨x, hC⟩
  have hcap := hK B C ⟨⟨hBK, hCK⟩, hne⟩
  have hx : x ∈ B ∩ C := ⟨h2 x B hB, h2 x C hC⟩
  rw [hcap, Null_eq_empty] at hx
  exact hx

/-!
## [✱101] On 0 and 1 and 2

*(Vol. 2, p. 19)*

> *Summary of* *101.
>
> In the present number, we have to show that 0 and 1 and 2 as previously defined are cardinal numbers in the sense defined in *100, and to add a few elementary propositions to those already given concerning them. We prove (*101·12·241) that 0 and 1 are not null, which cannot be proved, with our axioms, for any other cardinal, except (in the case of finite cardinals) when the type is specified as a sufficiently high one. Thus we prove (*101·42·43) that \(2_{\text{Cls}}\) and \(2_{\text{Rel}}\) exist; this follows from \(\Lambda \neq \text{V}\) and \(\dot{\Lambda}\neq \dot{\text{V}}\). We prove (*101·22·34) that 0 and 1 and 2 are all different from each other. We prove (*101·15·28) that \(\text{ sm }ʻʻ0 = 0\) and \(\text{ sm }ʻʻ1 = 1\), but we cannot prove \(\text{ sm }ʻʻ2 = 2\) unless we assume the existence of at least two individuals, or define the first 2 in "\(\text{ sm }ʻʻ2 = 2\)" as a 2 of some type other than \(2_{\text{Indiv}}\), where "\(\text{Indiv}\)" stands for the type of individuals.
>
> …

**Lean reading.** `0`, `1`, `2` are `zero`, `one`, `two` (Defs/Part2), typically ambiguous
constants taken at the type their position determines; when nothing determines it, each occurrence
has a type parameter of its own (e.g. ✱101·15 `sm''0 = 0`, the two `0`s in types `α`, `β`).
`Nc'α` follows ✱100: equations are in a free type, attributive occurrences in the type of the
member; in ✱101·17·29 IT binds nothing (no logical occurrences), so each equation has its own type.
`Cl''1`, `s'` are `Cl ʻʻ one`, `sumCls`; `2_Cls`, `2_Rel` are `clsT two Cls`, `clsT two Rel`
(✱65·01). PM assumes every type has a member; where a proposition fails for an empty type (`1`, `2`
and `Λ ≠ V` need members), `[Nonempty _]` is added. ✱101·32 takes the converse domain of `NC` in a
type of classes, as PM's proof (by ✱101·31) and its note to ✱101·4 indicate.

**Status.** proved (all propositions; ✱101·21, ✱101·241, ✱101·26, ✱101·28, ✱101·29, ✱101·32,
✱101·34, ✱101·42, ✱101·43 proved (reading): `[Nonempty _]` (PM assumes every type has a member),
✱101·29 also a transcription error, ✱101·32 also the converse-domain type of `NC`)
-/

/-- ✱101·1. \(\vdash . 0 = \text{Nc}ʻ\Lambda \quad[*73·48 . *100·1]\)

`0` and `Nc'Λ` are in one type `γ` (the equation); the `Λ` of `Nc'Λ` is in an arbitrary type `β`. -/
theorem pm101_1 {γ β : Type*} : (zero : Set (Set γ)) = nc γ (Λ : Set β) := by
  ext B
  rw [zero_eq, Set.mem_singleton_iff, Null_eq_empty]
  exact sm_empty_iff.symm

/-- ✱101·11. \(\vdash . 0 \in \text{NC} \quad[*101·1 .*100·4]\)

`0 ∈ NC` holds for every converse-domain type `β` of `NC`. -/
theorem pm101_11 {γ β : Type*} : (zero : Set (Set γ)) ∈ NC β := ⟨Λ, pm101_1⟩

/-- ✱101·12. \(\vdash . \exists ! 0 \quad[*51·161. (*54·01)]\) -/
theorem pm101_12 {α : Type*} : (zero : Set (Set α)).Nonempty := ⟨Λ, mem_unitCls.2 rfl⟩

/-- ✱101·13. \(\vdash . \exists ! 0 \cap \text{Cl}ʻ\alpha . \Lambda \in 0 \cap \text{Cl}ʻ\alpha \quad[*51·16 . *60·3]\) -/
theorem pm101_13 {α : Type*} {A : Set α} :
    (zero ∩ cl A).Nonempty ∧ Λ ∈ zero ∩ cl A := by
  have h : Λ ∈ zero ∩ cl A :=
    ⟨mem_unitCls.2 rfl, by rw [mem_cl, Null_eq_empty]; exact Set.empty_subset A⟩
  exact ⟨⟨Λ, h⟩, h⟩

/-- ✱101·14. \(\vdash : \text{Nc}ʻ\gamma = 0 . \equiv . \gamma = \Lambda\)

The equation `Nc'γ = 0` is in an arbitrary type `δ`. -/
theorem pm101_14 {δ α : Type*} {G : Set α} : nc δ G = zero ↔ G = Λ := by
  constructor
  · intro h
    have h0 : (∅ : Set δ) ∈ nc δ G := by rw [h, zero_eq]; rfl
    rw [Null_eq_empty]
    exact sm_empty_iff.1 (sm_symm h0)
  · rintro rfl
    exact (pm101_1).symm

/-- ✱101·15. \(\vdash . \text{ sm }ʻʻ0 = 0\)

The two `0`s are typically ambiguous constants, the argument of `sm''` in a type `α` and the
equation in a type `β`. -/
theorem pm101_15 {α β : Type*} : (sm ʻʻ (zero : Set (Set α)) : Set (Set β)) = zero := by
  have h1 : (sm ʻʻ (zero : Set (Set α)) : Set (Set β)) = nc β (∅ : Set α) := by
    rw [zero_eq_n₀c_empty]; exact sm_img_n₀c _
  rw [h1, pm101_1 (γ := β) (β := α), Null_eq_empty]

/-- ✱101·16. \(\vdash \colon\ldotp \mu \in \text{NC}-\iota ʻ0 . \supset : \alpha \in \mu . \supset_{\alpha} . \exists !\alpha\)

`0` (in `ι'0`) is in the type of the members of `NC`, i.e. of `μ` (significance). -/
theorem pm101_16 {γ β : Type*} {μ : Set (Set γ)} :
    μ ∈ NC β \ ι zero → ∀ A, A ∈ μ → A.Nonempty := by
  rintro ⟨⟨B, rfl⟩, hz⟩ A hA
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  apply hz
  show nc γ B = zero
  rw [pm101_14, Null_eq_empty]
  exact sm_empty_iff.1 (sm_symm hA)

/-- ✱101·17. \(\vdash : \Lambda \in \text{Nc}ʻ\alpha . \equiv . \text{Nc}ʻ\alpha = 0 . \equiv . \text{Nc}ʻ\alpha = \text{Nc}ʻ\Lambda . \equiv . \alpha = \Lambda\)

The four propositions of the chain are linked by three equivalences (✱4·02). There are no
logical or argumental occurrences of `Nc'α`, so convention IT binds nothing: the attributive
`Λ ∈ Nc'α` is in the type `γ₁` of its `Λ`, and each equation is in a type of its own (`γ₂`, `γ₃`);
the `Λ` of `Nc'Λ` is in an arbitrary type `δ`. -/
theorem pm101_17 {γ₁ γ₂ γ₃ δ α : Type*} {A : Set α} :
    (((Λ : Set γ₁) ∈ nc γ₁ A ↔ nc γ₂ A = zero) ∧
      (nc γ₂ A = zero ↔ nc γ₃ A = nc γ₃ (Λ : Set δ))) ∧
      (nc γ₃ A = nc γ₃ (Λ : Set δ) ↔ A = Λ) := by
  have e1 : (Λ : Set γ₁) ∈ nc γ₁ A ↔ A = Λ := by
    rw [Null_eq_empty, Null_eq_empty]
    exact ⟨fun h => sm_empty_iff.1 (sm_symm h), fun h => by rw [h]; exact sm_empty_iff.2 rfl⟩
  have e2 : nc γ₂ A = zero ↔ A = Λ := pm101_14
  have e3 : nc γ₃ A = nc γ₃ (Λ : Set δ) ↔ A = Λ := by rw [← pm101_1]; exact pm101_14
  exact ⟨⟨e1.trans e2.symm, e2.trans e3.symm⟩, e3⟩

/-- ✱101·2. \(\vdash . 1 = \text{Nc}ʻ\iota ʻx \quad[*73·45.*100·1]\) -/
theorem pm101_2 {γ α : Type*} {x : α} : (one : Set (Set γ)) = nc γ (ι x) := by
  ext B
  exact sm_unit_iff.symm

/-- ✱101·21. \(\vdash . 1 \in \text{NC} \quad[*101·2.*100·4]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the proof
uses `1 = Nc'ι'x`): `[Nonempty β]` for the converse-domain type `β` of `NC` (for an empty `β`,
`NC` contains only `Nc'Λ = 0`). -/
theorem pm101_21 {γ β : Type*} [Nonempty β] : (one : Set (Set γ)) ∈ NC β :=
  let ⟨x⟩ := ‹Nonempty β›
  ⟨ι x, pm101_2⟩

/-- ✱101·22. \(\vdash . 1 \neq 0\) -/
theorem pm101_22 {α : Type*} : (one : Set (Set α)) ≠ zero := by
  intro h
  have h0 : (Λ : Set α) ∈ (one : Set (Set α)) := by rw [h]; exact mem_unitCls.2 rfl
  obtain ⟨x, hx⟩ := h0
  have : x ∈ (Λ : Set α) := by rw [hx]; exact mem_unitCls.2 rfl
  rw [Null_eq_empty] at this
  exact this

/-- ✱101·23. \(\vdash . 1 \cap 0 = \Lambda\) -/
theorem pm101_23 {α : Type*} : (one ∩ zero : Set (Set α)) = Λ := by
  rw [Null_eq_empty]
  refine Set.eq_empty_iff_forall_notMem.2 fun B ⟨⟨x, hx⟩, h0⟩ => ?_
  have h0' : B = Λ := h0
  have : x ∈ B := by rw [hx]; exact mem_unitCls.2 rfl
  rw [h0', Null_eq_empty] at this
  exact this

/-- ✱101·24. \(\vdash : \exists !\alpha . \supset . \exists ! 1 \cap \text{Cl}ʻ\alpha\) -/
theorem pm101_24 {α : Type*} {A : Set α} : A.Nonempty → (one ∩ cl A).Nonempty := by
  rintro ⟨x, hx⟩
  refine ⟨ι x, ⟨x, rfl⟩, ?_⟩
  intro y hy
  rw [mem_unitCls.1 hy]
  exact hx

/-- ✱101·241. \(\vdash . \exists !1 \quad[*52·23]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the proof
cites ✱52·23, `∃!1`, from ✱10·25); for an empty type `1` is null, so `[Nonempty α]` is added. -/
theorem pm101_241 {α : Type*} [Nonempty α] : (one : Set (Set α)).Nonempty :=
  let ⟨x⟩ := ‹Nonempty α›
  ⟨ι x, x, rfl⟩

/-- ✱101·25. \(\vdash : \alpha \in 1 . \beta \subset \alpha . \beta \neq \alpha . \supset . \beta \in 0\) -/
theorem pm101_25 {α : Type*} {A B : Set α} : (A ∈ one ∧ B ⊆ A) ∧ B ≠ A → B ∈ zero := by
  rintro ⟨⟨⟨x, rfl⟩, hBA⟩, hne⟩
  rw [unitCls_eq_singleton, Set.subset_singleton_iff_eq] at hBA
  rcases hBA with h | h
  · show B = Λ
    rw [h, Null_eq_empty]
  · exact absurd h hne

/-- ✱101·26. \(\vdash . sʻ\text{Cl}ʻʻ1 = 0 \cup 1\)

`Cl''1` is `Cl ʻʻ one` and `s'` is `sumCls`.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the proof
uses `Λ ∈ Cl'ι'x`): for an empty type `1` is null and `s'Cl''1 = Λ ≠ 0`, so `[Nonempty α]` is
added. -/
theorem pm101_26 {α : Type*} [Nonempty α] : sumCls (Cl ʻʻ (one : Set (Set α))) = zero ∪ one := by
  ext B
  constructor
  · rintro ⟨C, ⟨A, ⟨x, rfl⟩, rfl⟩, hB⟩
    have hB' : B ⊆ {x} := hB
    rw [Set.subset_singleton_iff_eq] at hB'
    rcases hB' with h | h
    · left; show B = Λ; rw [h, Null_eq_empty]
    · right; exact ⟨x, h⟩
  · rintro (h | ⟨x, rfl⟩)
    · obtain ⟨x⟩ := ‹Nonempty α›
      refine ⟨cl (ι x), ⟨ι x, ⟨x, rfl⟩, rfl⟩, ?_⟩
      have h' : B = Λ := h
      rw [h', Null_eq_empty]
      exact Set.empty_subset _
    · exact ⟨cl (ι x), ⟨ι x, ⟨x, rfl⟩, rfl⟩, mem_cl.2 subset_rfl⟩

/-- ✱101·27. \(\vdash . 1 = \hat{\alpha}\{(\exists x) . x \in \alpha . \alpha - \iota ʻx \in 0\}\) -/
theorem pm101_27 {α : Type*} : (one : Set (Set α)) = {A | ∃ x, x ∈ A ∧ A \ ι x ∈ zero} := by
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, rfl, ?_⟩
    show ι x \ ι x = Λ
    rw [Set.sdiff_self, Null_eq_empty]
  · rintro ⟨x, hx, h⟩
    have h' : A \ ι x = Λ := h
    rw [Null_eq_empty] at h'
    refine ⟨x, Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
    · by_contra hzx
      have : z ∈ A \ ι x := ⟨hz, hzx⟩
      rw [h'] at this
      exact this
    · rw [mem_unitCls.1 hz]; exact hx

/-- ✱101·28. \(\vdash . \text{ sm }ʻʻ1 = 1\)

The two `1`s are in independent types `α` (argument of `sm''`) and `β` (equation).

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the proof
uses `γ sm ι'x`): if `α` is empty, `1` is null in `α` and `sm''1 = Λ`, so `[Nonempty α]` is
added. -/
theorem pm101_28 {α β : Type*} [Nonempty α] :
    (sm ʻʻ (one : Set (Set α)) : Set (Set β)) = one := by
  obtain ⟨x⟩ := ‹Nonempty α›
  have h := pm101_2 (γ := β) (x := x)
  rw [one_eq_n₀c_singleton x, sm_img_n₀c, h]
  rfl

/-- ✱101·29. \(\vdash : \iota ʻx\in \text{Nc}ʻ\alpha . \equiv . \text{Nc}ʻ\alpha = 1. \equiv . \text{Nc}ʻ\alpha = \text{Nc}ʻ\iota ʻx. = . \alpha \in 1\)

The e-text prints `= .` for the last `≡ .`. As in ✱101·17, IT binds nothing: the attributive
`ι'x ∈ Nc'α` is in the type `γ₁` of `x`, the equations `Nc'α = 1` and `Nc'α = Nc'ι'x` in types
`γ₂`, `γ₃` of their own, and the `1` of `α ∈ 1` in the type of `α`.

**Status.** proved (reading): transcription error (`=` for the last `≡`); PM assumes every type
has a member (Introduction, Ch. I): `[Nonempty γ₂]`, `[Nonempty γ₃]` (in an empty type `1` and
`Nc'α` are both null for any `α` with two members). -/
theorem pm101_29 {γ₁ γ₂ γ₃ α : Type*} [Nonempty γ₂] [Nonempty γ₃] {x : γ₁} {A : Set α} :
    ((ι x ∈ nc γ₁ A ↔ nc γ₂ A = one) ∧ (nc γ₂ A = one ↔ nc γ₃ A = nc γ₃ (ι x))) ∧
      (nc γ₃ A = nc γ₃ (ι x) ↔ A ∈ one) := by
  have e1 : ι x ∈ nc γ₁ A ↔ A ∈ one := ⟨fun h => sm_unit_iff.1 (sm_symm h),
    fun h => sm_symm (sm_unit_iff.2 h)⟩
  have e2 : nc γ₂ A = one ↔ A ∈ one := nc_eq_one_iff
  have e3 : nc γ₃ A = nc γ₃ (ι x) ↔ A ∈ one := by rw [← pm101_2]; exact nc_eq_one_iff
  exact ⟨⟨e1.trans e2.symm, e2.trans e3.symm⟩, e3⟩

/-- ✱101·3. \(\vdash :x\neq y.\supset .2=\text{Nc}ʻ(\iota ʻx\cup \iota ʻy)\) -/
theorem pm101_3 {γ α : Type*} {x y : α} : x ≠ y → (two : Set (Set γ)) = nc γ (ι x ∪ ι y) := by
  intro hxy
  ext B
  exact (sm_pair_iff hxy).symm

/-- ✱101·301. \(\vdash.2=\hat{\alpha}\{(\exists x).x\in \alpha .\alpha -\iota ʻx\in 1\} \quad[*54·3]\) -/
theorem pm101_301 {α : Type*} : (two : Set (Set α)) = {A | ∃ x, x ∈ A ∧ A \ ι x ∈ one} := by
  ext A
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨a, Or.inl rfl, b, Set.ext fun z => ⟨?_, ?_⟩⟩
    · rintro ⟨hz | hz, hza⟩
      · exact absurd hz hza
      · exact hz
    · intro hz
      rw [mem_unitCls.1 hz]
      exact ⟨Or.inr rfl, fun h => hab (mem_unitCls.1 h).symm⟩
  · rintro ⟨x, hx, y, hy⟩
    have hyA : y ∈ A \ ι x := by rw [hy]; exact mem_unitCls.2 rfl
    refine ⟨x, y, fun h => hyA.2 (mem_unitCls.2 h.symm), Set.ext fun z => ⟨fun hz => ?_, ?_⟩⟩
    · by_cases hzx : z ∈ ι x
      · exact Or.inl hzx
      · right
        have : z ∈ A \ ι x := ⟨hz, hzx⟩
        rw [hy] at this
        exact this
    · rintro (hz | hz)
      · rw [mem_unitCls.1 hz]; exact hx
      · rw [mem_unitCls.1 hz]; exact hyA.1

/-- ✱101·31. \(\vdash .2=\text{Nc}ʻ(\iota ʻ\iota ʻx\cup \iota ʻ\Lambda)\)

`2` and `Nc'…` are in one type `γ` (the equation); `x` has an arbitrary type. -/
theorem pm101_31 {γ α : Type*} {x : α} : (two : Set (Set γ)) = nc γ (ι (ι x) ∪ ι Λ) := by
  refine pm101_3 fun h => ?_
  have : x ∈ (Λ : Set α) := by rw [← h]; exact mem_unitCls.2 rfl
  rw [Null_eq_empty] at this
  exact this

/-- ✱101·32. \(\vdash .2\in \text{NC} \quad[*101·31.*100·4]\)

**Status.** proved (reading): the converse domain of `NC` is taken in a type of classes `Set α`,
as PM's proof by ✱101·31 (`2 = Nc'(ι'ι'x ∪ ι'Λ)`) and the note to ✱101·4 show (in the lowest type
two members cannot be proved to exist), with `[Nonempty α]` since PM assumes every type has a
member (Introduction, Ch. I). -/
theorem pm101_32 {γ α : Type*} [Nonempty α] : (two : Set (Set γ)) ∈ NC (Set α) :=
  let ⟨x⟩ := ‹Nonempty α›
  ⟨ι (ι x) ∪ ι Λ, pm101_31⟩

/-- ✱101·33. \(\vdash :\alpha,\beta \in 1.\alpha \cap \beta =\Lambda .\supset .\alpha \cup \beta \in 2 \quad[*54·43]\) -/
theorem pm101_33 {α : Type*} {A B : Set α} :
    (A ∈ one ∧ B ∈ one) ∧ A ∩ B = Λ → A ∪ B ∈ two := by
  rintro ⟨⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩, h⟩
  refine ⟨x, y, fun hxy => ?_, rfl⟩
  have : x ∈ ι x ∩ ι y := ⟨mem_unitCls.2 rfl, mem_unitCls.2 hxy⟩
  rw [h, Null_eq_empty] at this
  exact this

/-- ✱101·34. \(\vdash .2\neq 0.2\neq 1\)

The two conjuncts are separate assertions, each in a type of its own.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the proof
uses `ι'y ∈ 1`): in an empty type `1 = 2 = Λ`, so `[Nonempty β]` is added for `2 ≠ 1`. -/
theorem pm101_34 {α β : Type*} [Nonempty β] :
    (two : Set (Set α)) ≠ zero ∧ (two : Set (Set β)) ≠ one := by
  constructor
  · intro h
    have h0 : (Λ : Set α) ∈ (two : Set (Set α)) := by rw [h]; exact mem_unitCls.2 rfl
    obtain ⟨x, y, _, hxy⟩ := h0
    have : x ∈ (Λ : Set α) := by rw [hxy]; exact Or.inl rfl
    rw [Null_eq_empty] at this
    exact this
  · intro h
    obtain ⟨b⟩ := ‹Nonempty β›
    have h1 : ι b ∈ (two : Set (Set β)) := by rw [h]; exact ⟨b, rfl⟩
    obtain ⟨x, y, hxy, he⟩ := h1
    have hx : x ∈ ι b := by rw [he]; exact Or.inl rfl
    have hy : y ∈ ι b := by rw [he]; exact Or.inr rfl
    exact hxy ((mem_unitCls.1 hx).trans (mem_unitCls.1 hy).symm)

/-- ✱101·35. \(\vdash .2\cap 0=\Lambda .2\cap 1=\Lambda \quad[*100·42.\text{Transp}.*101·11·21·32·34]\) -/
theorem pm101_35 {α β : Type*} :
    (two ∩ zero : Set (Set α)) = Λ ∧ (two ∩ one : Set (Set β)) = Λ := by
  rw [Null_eq_empty, Null_eq_empty]
  constructor
  · refine Set.eq_empty_iff_forall_notMem.2 fun B ⟨⟨x, y, _, hxy⟩, h0⟩ => ?_
    have h0' : B = Λ := h0
    have : x ∈ B := by rw [hxy]; exact Or.inl rfl
    rw [h0', Null_eq_empty] at this
    exact this
  · refine Set.eq_empty_iff_forall_notMem.2 fun B ⟨⟨x, y, hne, hxy⟩, ⟨z, hz⟩⟩ => ?_
    have hx : x ∈ ι z := by rw [← hz, hxy]; exact Or.inl rfl
    have hy : y ∈ ι z := by rw [← hz, hxy]; exact Or.inr rfl
    exact hne ((mem_unitCls.1 hx).trans (mem_unitCls.1 hy).symm)

/-- ✱101·36. \(\vdash :\alpha \in 2.\beta \subset \alpha .\beta \neq \alpha .\supset .\beta \in 0\cup 1\) -/
theorem pm101_36 {α : Type*} {A B : Set α} :
    (A ∈ two ∧ B ⊆ A) ∧ B ≠ A → B ∈ zero ∪ one := by
  rintro ⟨⟨hA, hBA⟩, hne⟩
  obtain ⟨a, b, _, rfl⟩ := mem_two_iff.1 hA
  rw [Set.subset_pair_iff_eq] at hBA
  rcases hBA with h | h | h | h
  · left; show B = Λ; rw [h, Null_eq_empty]
  · right; exact ⟨a, h⟩
  · right; exact ⟨b, h⟩
  · exact absurd h hne

/-- ✱101·37. \(\vdash . sʻ\text{Cl}ʻʻ2 \subset 0\cup 1\cup 2 \quad[*54·411]\) -/
theorem pm101_37 {α : Type*} : sumCls (Cl ʻʻ (two : Set (Set α))) ⊆ zero ∪ one ∪ two := by
  rintro B ⟨C, ⟨A, hA, rfl⟩, hB⟩
  obtain ⟨a, b, hab, rfl⟩ := mem_two_iff.1 hA
  have hB' : B ⊆ {a, b} := hB
  rw [Set.subset_pair_iff_eq] at hB'
  rcases hB' with h | h | h | h
  · left; left; show B = Λ; rw [h, Null_eq_empty]
  · left; right; exact ⟨a, h⟩
  · left; right; exact ⟨b, h⟩
  · right; exact mem_two_iff.2 ⟨a, b, hab, h⟩

/-- ✱101·38. \(\vdash : \exists ! 2 . \supset . sʻ\text{Cl}ʻʻ2 = 0\cup 1\cup 2\) -/
theorem pm101_38 {α : Type*} :
    (two : Set (Set α)).Nonempty → sumCls (Cl ʻʻ (two : Set (Set α))) = zero ∪ one ∪ two := by
  rintro ⟨A, hA⟩
  refine Set.Subset.antisymm pm101_37 ?_
  obtain ⟨a, b, hab, rfl⟩ := mem_two_iff.1 hA
  rintro B ((h | ⟨z, rfl⟩) | h)
  · refine ⟨cl {a, b}, ⟨{a, b}, hA, rfl⟩, ?_⟩
    have h' : B = Λ := h
    rw [h', Null_eq_empty]
    exact Set.empty_subset _
  · by_cases hza : z = a
    · subst hza
      refine ⟨cl {z, b}, ⟨{z, b}, hA, rfl⟩, ?_⟩
      intro w hw
      rw [mem_unitCls.1 hw]
      exact Or.inl rfl
    · refine ⟨cl {z, a}, ⟨{z, a}, mem_two_iff.2 ⟨z, a, hza, rfl⟩, rfl⟩, ?_⟩
      intro w hw
      rw [mem_unitCls.1 hw]
      exact Or.inl rfl
  · exact ⟨cl B, ⟨B, h, rfl⟩, mem_cl.2 subset_rfl⟩

/-- ✱101·4. \(\vdash : (\exists x,y) . x\neq y . \equiv . \exists !2\) -/
theorem pm101_4 {α : Type*} : (∃ x y : α, x ≠ y) ↔ (two : Set (Set α)).Nonempty := by
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨ι x ∪ ι y, x, y, hxy, rfl⟩
  · rintro ⟨A, x, y, hxy, -⟩
    exact ⟨x, y, hxy⟩

/-- ✱101·41. \(\vdash : (\exists x) . \iota ʻx\neq \text{V}. \equiv . \exists !2\) -/
theorem pm101_41 {α : Type*} : (∃ x : α, ι x ≠ V) ↔ (two : Set (Set α)).Nonempty := by
  rw [← pm101_4, V_eq_univ]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem _).1 hx
    exact ⟨y, x, fun h => hy (mem_unitCls.2 h)⟩
  · rintro ⟨x, y, hxy⟩
    exact ⟨y, fun h => hxy (mem_unitCls.1 (h ▸ Set.mem_univ x : x ∈ ι y))⟩

/-- ✱101·42. \(\vdash . \exists ! 2_{\text{Cls}} . \iota ʻ\Lambda \cup \iota ʻ\text{V} \in 2_{\text{Cls}}\)

`2_Cls` is `2 ∩ t'Cls` (✱65·01), `clsT two Cls`, with `Cls : Set (Set α)`.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the proof
uses `Λ ≠ V`, ✱24·1, from ✱10·25): for an empty `α`, `Λ = V`, so `[Nonempty α]` is added. -/
theorem pm101_42 {α : Type*} [Nonempty α] :
    (clsT two (Cls : Set (Set α))).Nonempty ∧ ι Λ ∪ ι V ∈ clsT two (Cls : Set (Set α)) := by
  rw [clsT_eq]
  have hne : (Λ : Set α) ≠ V := by
    obtain ⟨a⟩ := ‹Nonempty α›
    intro h
    have : a ∈ (Λ : Set α) := by rw [h, V_eq_univ]; trivial
    rw [Null_eq_empty] at this
    exact this
  exact ⟨⟨_, Λ, V, hne, rfl⟩, Λ, V, hne, rfl⟩

/-- ✱101·43. \(\vdash . \exists ! 2_{\text{Rel}} \quad[\text{Proof as in *101·42}]\)

`2_Rel` is `2 ∩ t'Rel` (✱65·01), `clsT two Rel`.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the proof
uses `Λ̇ ≠ V̇`): `[Nonempty α]`, `[Nonempty β]` for the referents and relata. -/
theorem pm101_43 {α β : Type*} [Nonempty α] [Nonempty β] :
    (clsT two (Rel : Set (α → β → Prop))).Nonempty := by
  rw [clsT_eq]
  obtain ⟨a⟩ := ‹Nonempty α›
  obtain ⟨b⟩ := ‹Nonempty β›
  refine ⟨_, rNull, rV, fun h => ?_, rfl⟩
  have : rNull a b := by rw [h]; exact ⟨rfl, rfl⟩
  exact rNull_apply a b this

/-!
## [✱102] On cardinal numbers of assigned types

*(Vol. 2, p. 24)*

> *Summary of* *102.
>
> In this number, we shall consider a typically definite relation "\(\text{Nc}\)," *i.e.* we shall consider the relation, to a class \(\delta\) which is given as of the same type as \(\beta\), of the class \(\mu\) of those classes \(\gamma\) which are similar to \(\delta\) and of the same type as \(\alpha\). We shall then put \[ \begin{aligned} \mu &= \text{Nc}(\alpha _{\beta })ʻ\delta ,\\ \gamma &\in \text{Nc}(\alpha _{\beta })ʻ\delta ,\\ \gamma &\,\text{ sm }_{(\alpha ,\beta )}\delta , \end{aligned} \] and the class of all such numbers as \(\mu\) for a given \(\alpha\) and \(\beta\) we shall call \(\text{NC}^{\beta }(\alpha)\), so that \[ \text{NC}^{\beta }(\alpha ) = \text{D}ʻ\text{Nc}(\alpha _{\beta }). \]
>
> The notations here introduced for giving typical definiteness to "\(\text{sm}\)" and "\(\text{Nc}\)" are those defined in *65 for any typically ambiguous relation.
>
> By *63·01·02 we have, if \(\alpha\) is a typically ambiguous symbol, \[ \begin{aligned} &\vdash .\alpha _{x} = \alpha \cap tʻx,\\ &\vdash .\alpha (x) = \alpha \cap tʻ\iota ʻx. \end{aligned} \]
>
> …

**Lean reading.** The typically definite relations of ✱65 are explicit: `sm_(α,β)` is
`relTT sm A B`, `sm(x,y)` is `relT2T2 sm x y`, `sm_β` is `relT sm B`, `Nc(α_β)` is
`relT2T Nc A B`, `Nc(α)` is `relT2 Nc A`, `Nc(α,β)` is `relT2T2 Nc A b`, `1_α` is `clsT one A`,
`1(x)` is `clsT2 one x`, and `NC^β(α)` is `NCT A B` (✱102·01). In Lean the types of `α`, `β`
are those of `A`, `B`, so the restrictions to `t'α`, `t'β` are typings (`relTT_eq`, …), and
`γ ∈ t'α` (always true when significant) forces `γ` into the type of `α`. Since these relations
are not syntactically `graph`s, their descriptive functions are kept as descriptions
(`Desc (relT2T Nc A B) E ψ`) throughout, with the smallest scopes. `t'α` is `typ A`, `Cl'α` is
`cl A`, `Rl'P` is `rl P`. ✱102·23, which the e-text prints inside the entry of ✱102·22, is
formalized as well.

**Status.** proved (all propositions, including ✱102·23; ✱102·01 definition; ✱102·5 proved
(reading): transcription error; ✱102·541 proved (corrected): `t'Λ` printed for `ι'Λ`, the printed
form is refuted by `pm102_541_printed_false`)
-/

/-- ✱102·01 (Df). \(\text{NC}^\beta (\alpha ) = \text{D}ʻ\text{Nc}(\alpha _{\beta }) \quad\text{Df}\) -/
theorem pm102_01 {α β : Type*} {A : Set α} {B : Set β} :
    Desc D (relT2T Nc A B) (fun K => NCT A B = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱102·11. \(\vdash :R \in 1\rightarrow 1.\supset .R_{(x,y)} \in 1(x)\rightarrow 1(y)\)

`R_{(x,y)}` is `relTT R x y` (✱65·1) and `1(x)` is `clsT2 one x` (✱65·02). -/
theorem pm102_11 {α β : Type*} {R : α → β → Prop} {x : α} {y : β} :
    R ∈ arrow one one → relTT R x y ∈ arrow (clsT2 one x) (clsT2 one y) := by
  intro h
  rw [relTT_eq, clsT2_eq', clsT2_eq']
  exact h

/-- ✱102·13. \(\vdash :R \in 1\rightarrow 1.\supset .R_{x} \in 1(x)\rightarrow 1 \quad[\text{Proof as in *102·11}]\) -/
theorem pm102_13 {α β : Type*} {R : α → β → Prop} {x : α} :
    R ∈ arrow one one → relT R x ∈ arrow (clsT2 one x) one := by
  intro h
  rw [relT_eq, clsT2_eq']
  exact h

/-- ✱102·2. \(\vdash :\gamma \text{ sm }_{(\alpha ,\beta )}\delta . \equiv .\gamma \text{ sm } \delta .\gamma \in tʻ\alpha .\delta \in tʻ\beta \quad[*35·102.(*65·1)]\)

`sm_(α,β)` is `relTT sm A B` (✱65·1); `γ ∈ t'α` makes `γ` of the type of `α`. -/
theorem pm102_2 {α β : Type*} {A G : Set α} {B E : Set β} :
    relTT sm A B G E ↔ (sm G E ∧ G ∈ typ A) ∧ E ∈ typ B := by
  rw [relTT_eq]
  simp [typ_eq_univ]

/-- ✱102·21. \[\begin{aligned}\vdash :\gamma \text{ sm }_{(\alpha ,\beta )}&\delta . \equiv .(\exists R).R \in 1\rightarrow 1.\text{D}ʻR \in tʻ\alpha .\\ &\text{ᗡ}ʻR \in tʻ\beta .\text{D}ʻR = \gamma .\text{ᗡ}ʻR = \delta \quad[*102·2.*73·1]\end{aligned}\] -/
theorem pm102_21 {α β : Type*} {A G : Set α} {B E : Set β} :
    relTT sm A B G E ↔ ∃ R : α → β → Prop,
      (((R ∈ arrow one one ∧ dom R ∈ typ A) ∧ codom R ∈ typ B) ∧ dom R = G) ∧ codom R = E := by
  rw [relTT_eq, sm_iff]
  constructor
  · rintro ⟨R, ⟨h1, h2⟩, h3⟩
    exact ⟨R, ⟨⟨⟨h1, mem_typ _ _⟩, mem_typ _ _⟩, h2.symm⟩, h3.symm⟩
  · rintro ⟨R, ⟨⟨⟨h1, -⟩, -⟩, h2⟩, h3⟩
    exact ⟨R, ⟨h1, h2.symm⟩, h3.symm⟩

/-- ✱102·22. \(\vdash :\gamma \text{ sm }(x,y)\delta . \equiv .\gamma \text{ sm } \delta .\gamma \subset tʻx.\delta \subset tʻy \quad[*63·5.(*65·12)]\)

`sm(x,y)` is `relT2T2 sm x y` (✱65·12). -/
theorem pm102_22 {α β : Type*} {x : α} {y : β} {G : Set α} {E : Set β} :
    relT2T2 sm x y G E ↔ (sm G E ∧ G ⊆ typ x) ∧ E ⊆ typ y := by
  rw [relT2T2_eq']
  simp [typ_eq_univ]

/-- ✱102·23. \[\begin{aligned}\vdash :\gamma \text{ sm }(x,y)&\delta . \equiv .(\exists R).R \in 1\rightarrow 1.\text{D}ʻR\subset tʻx.\\ &\text{ᗡ}ʻR\subset tʻy.\text{D}ʻR = \gamma .\text{ᗡ}ʻR = \delta \quad[*102·22.*73·1]\end{aligned}\]

(The e-text prints this proposition inside the entry of ✱102·22.) -/
theorem pm102_23 {α β : Type*} {x : α} {y : β} {G : Set α} {E : Set β} :
    relT2T2 sm x y G E ↔ ∃ R : α → β → Prop,
      (((R ∈ arrow one one ∧ dom R ⊆ typ x) ∧ codom R ⊆ typ y) ∧ dom R = G) ∧ codom R = E := by
  rw [relT2T2_eq', sm_iff]
  constructor
  · rintro ⟨R, ⟨h1, h2⟩, h3⟩
    exact ⟨R, ⟨⟨⟨h1, by rw [typ_eq_univ]; exact Set.subset_univ _⟩,
      by rw [typ_eq_univ]; exact Set.subset_univ _⟩, h2.symm⟩, h3.symm⟩
  · rintro ⟨R, ⟨⟨⟨h1, -⟩, -⟩, h2⟩, h3⟩
    exact ⟨R, ⟨h1, h2.symm⟩, h3.symm⟩

/-- ✱102·24. \(\vdash :\gamma \text{ sm } (x,y) \delta . \equiv .(\exists R).R \in 1(x)\rightarrow 1(y).\text{D}ʻR = \gamma .\text{ᗡ}ʻR = \delta \) -/
theorem pm102_24 {α β : Type*} {x : α} {y : β} {G : Set α} {E : Set β} :
    relT2T2 sm x y G E ↔ ∃ R : α → β → Prop,
      (R ∈ arrow (clsT2 one x) (clsT2 one y) ∧ dom R = G) ∧ codom R = E := by
  rw [relT2T2_eq', clsT2_eq', clsT2_eq', sm_iff]
  constructor
  · rintro ⟨R, ⟨h1, h2⟩, h3⟩
    exact ⟨R, ⟨h1, h2.symm⟩, h3.symm⟩
  · rintro ⟨R, ⟨h1, h2⟩, h3⟩
    exact ⟨R, ⟨h1, h2.symm⟩, h3.symm⟩

/-- ✱102·25. \[\begin{aligned}&\vdash :\gamma \text{ sm }_{(\alpha ,\beta )} \delta . \equiv .(\exists R).R \in 1_{\alpha }\rightarrow 1_{\beta }.\text{D}ʻR = \gamma .\text{ᗡ}ʻR = \delta\\ &[\text{Proof as in *102·24}]\end{aligned}\]

`1_α` is `clsT one A` (✱65·01). -/
theorem pm102_25 {α β : Type*} {A G : Set α} {B E : Set β} :
    relTT sm A B G E ↔ ∃ R : α → β → Prop,
      (R ∈ arrow (clsT one A) (clsT one B) ∧ dom R = G) ∧ codom R = E := by
  rw [relTT_eq, clsT_eq, clsT_eq, sm_iff]
  constructor
  · rintro ⟨R, ⟨h1, h2⟩, h3⟩
    exact ⟨R, ⟨h1, h2.symm⟩, h3.symm⟩
  · rintro ⟨R, ⟨h1, h2⟩, h3⟩
    exact ⟨R, ⟨h1, h2.symm⟩, h3.symm⟩

/-- ✱102·26. \(\vdash :\gamma \text{ sm }_{(\alpha ,\beta )} \delta .\gamma'\text{ sm }_{(\alpha ,\beta )} \delta .\supset .\gamma \text{ sm }_{(\alpha ,\alpha )}\gamma'\) -/
theorem pm102_26 {α β : Type*} {A G G' : Set α} {B E : Set β} :
    relTT sm A B G E ∧ relTT sm A B G' E → relTT sm A A G G' := by
  simp only [relTT_eq]
  exact fun ⟨h1, h2⟩ => sm_trans h1 (sm_symm h2)

/-- ✱102·27. \(\vdash :\gamma \text{ sm }_{(\alpha ,\beta )} \delta .\gamma' \text{ sm }_{(\alpha ʻ,\beta )} \delta .\supset .\gamma \text{ sm }_{(\alpha ,\alpha ʻ)}\gamma' \quad[\text{Proof as in *102·26}]\)

The e-text renders PM's `α'` as `αʻ`. -/
theorem pm102_27 {α α' β : Type*} {A G : Set α} {A' G' : Set α'} {B E : Set β} :
    relTT sm A B G E ∧ relTT sm A' B G' E → relTT sm A A' G G' := by
  simp only [relTT_eq]
  exact fun ⟨h1, h2⟩ => sm_trans h1 (sm_symm h2)

/-- ✱102·3. \(\vdash :\gamma \text{ sm }_{(\alpha ,\beta )} \delta . \equiv .\gamma \in \text{Nc}{(\alpha _\beta )}ʻ\delta \)

`Nc(α_β)` is `relT2T Nc A B` (✱65·11); its descriptive function `Nc(α_β)'δ` is kept as a
description, `Desc (relT2T Nc A B) E ψ`, throughout ✱102 (it is not syntactically a `graph`). -/
theorem pm102_3 {α β : Type*} {A G : Set α} {B E : Set β} :
    relTT sm A B G E ↔ Desc (relT2T Nc A B) E (fun μ => G ∈ μ) := by
  rw [relTT_eq, desc_relT2T_Nc]
  exact Iff.rfl

/-- ✱102·31. \(\vdash .\text{Nc} (\alpha _{\beta })ʻ\delta = \text{D}ʻʻ\{1\rightarrow 1\cap \hat{R} (\text{D}ʻR \in tʻ\alpha .\text{ᗡ}ʻR \in tʻ\beta .\text{ᗡ}ʻR = \delta )\}\) -/
theorem pm102_31 {α β : Type*} {A : Set α} {B E : Set β} :
    Desc (relT2T Nc A B) E (fun μ => μ = D ʻʻ (arrow one one ∩
      {R : α → β → Prop | (dom R ∈ typ A ∧ codom R ∈ typ B) ∧ codom R = E})) := by
  rw [desc_relT2T_Nc]
  ext G
  constructor
  · intro h
    obtain ⟨R, ⟨h1, h2⟩, h3⟩ := sm_iff.1 (mem_nc.1 h)
    exact ⟨R, ⟨h1, ⟨mem_typ _ _, mem_typ _ _⟩, h3.symm⟩, h2⟩
  · rintro ⟨R, ⟨h1, -, h3⟩, h2⟩
    exact mem_nc.2 (sm_iff.2 ⟨R, ⟨h1, h2⟩, h3.symm⟩)

/-- ✱102·32. \(\vdash . \text{Nc}(\alpha _{\beta })ʻ\delta = \text{D}ʻʻ\{(1_{\alpha }\rightarrow 1_{\beta }) \cap \overleftarrow{\text{ᗡ}}ʻ\delta\}\) -/
theorem pm102_32 {α β : Type*} {A : Set α} {B E : Set β} :
    Desc (relT2T Nc A B) E
      (fun μ => μ = D ʻʻ (arrow (clsT one A) (clsT one B) ∩ rels Dcnv E)) := by
  rw [desc_relT2T_Nc, clsT_eq, clsT_eq]
  ext G
  constructor
  · intro h
    obtain ⟨R, ⟨h1, h2⟩, h3⟩ := sm_iff.1 (mem_nc.1 h)
    exact ⟨R, ⟨h1, h3⟩, h2⟩
  · rintro ⟨R, ⟨h1, h3⟩, h2⟩
    exact mem_nc.2 (sm_iff.2 ⟨R, ⟨h1, h2⟩, h3⟩)

/-- ✱102·34. \[\begin{aligned}\vdash . \text{Nc}(\alpha ,\beta )ʻ\delta = &\text{D}ʻʻ\{1 \rightarrow 1 \cap \hat{R} (\text{D}ʻR \in tʻ\alpha . \text{ᗡ}ʻR \subset tʻ\beta . \text{ᗡ}ʻR = \delta )\}\\ &[\text{Proof as in *102·31}]\end{aligned}\]

`Nc(α,β)` is `relT2T2 Nc A b` (✱65·12); `ᗡ'R ⊂ t'β` makes `β` an object `b` of the type of the
members of `δ`. -/
theorem pm102_34 {α β : Type*} {A : Set α} {b : β} {E : Set β} :
    Desc (relT2T2 Nc A b) E (fun μ => μ = D ʻʻ (arrow one one ∩
      {R : α → β → Prop | (dom R ∈ typ A ∧ codom R ⊆ typ b) ∧ codom R = E})) := by
  rw [desc_relT2T2_Nc]
  ext G
  constructor
  · intro h
    obtain ⟨R, ⟨h1, h2⟩, h3⟩ := sm_iff.1 (mem_nc.1 h)
    exact ⟨R, ⟨h1, ⟨mem_typ _ _, by rw [typ_eq_univ]; exact Set.subset_univ _⟩, h3.symm⟩, h2⟩
  · rintro ⟨R, ⟨h1, -, h3⟩, h2⟩
    exact mem_nc.2 (sm_iff.2 ⟨R, ⟨h1, h2⟩, h3.symm⟩)

/-- ✱102·35. \(\vdash . \text{Nc}(\alpha ,\beta )ʻ\delta = \text{D}ʻʻ[{1_{\alpha } \rightarrow 1(\beta )} \cap \overleftarrow{\text{ᗡ}}ʻ\delta ] \quad[\text{Proof as in *102·32}]\) -/
theorem pm102_35 {α β : Type*} {A : Set α} {b : β} {E : Set β} :
    Desc (relT2T2 Nc A b) E
      (fun μ => μ = D ʻʻ (arrow (clsT one A) (clsT2 one b) ∩ rels Dcnv E)) := by
  rw [desc_relT2T2_Nc, clsT_eq, clsT2_eq']
  ext G
  constructor
  · intro h
    obtain ⟨R, ⟨h1, h2⟩, h3⟩ := sm_iff.1 (mem_nc.1 h)
    exact ⟨R, ⟨h1, h3⟩, h2⟩
  · rintro ⟨R, ⟨h1, h3⟩, h2⟩
    exact mem_nc.2 (sm_iff.2 ⟨R, ⟨h1, h2⟩, h3⟩)

/-- ✱102·36. \(\vdash . \text{E}! \text{Nc}(\alpha _{\beta })ʻ\delta \quad[*102·31.*14·21]\) -/
theorem pm102_36 {α β : Type*} {A : Set α} {B E : Set β} : EDesc (relT2T Nc A B) E := by
  rw [relT2T_eq']; exact EDesc_Nc E

/-- ✱102·361. \(\vdash . \text{E}! \text{Nc}(\alpha , \beta )ʻ\delta \quad[*102·34.*14·21]\) -/
theorem pm102_361 {α β : Type*} {A : Set α} {b : β} {E : Set β} :
    EDesc (relT2T2 Nc A b) E := by
  rw [relT2T2_eq']; exact EDesc_Nc E

/-- ✱102·37. \(\vdash . \text{ᗡ}ʻ\text{Nc}(\alpha _{\beta }) = tʻ\beta\) -/
theorem pm102_37 {α β : Type*} {A : Set α} {B : Set β} :
    codom (relT2T (Nc : Set (Set α) → Set β → Prop) A B) = typ B := by
  rw [relT2T_eq', typ_eq_univ]
  exact Set.eq_univ_of_forall fun E => ⟨nc α E, rfl⟩

/-- ✱102·4. \(\vdash : \gamma \in \text{Nc}(\alpha _{\beta })ʻ\delta . \gamma' \in \text{Nc}(\alpha _{\beta })ʻ\delta . \supset . \gamma \in \text{Nc}(\alpha _{\alpha })ʻ\gamma'\quad[*102·3·26]\) -/
theorem pm102_4 {α β : Type*} {A G G' : Set α} {B E : Set β} :
    Desc (relT2T Nc A B) E (fun μ => G ∈ μ) ∧ Desc (relT2T Nc A B) E (fun μ => G' ∈ μ) →
      Desc (relT2T Nc A A) G' (fun μ => G ∈ μ) := by
  simp only [desc_relT2T_Nc]
  exact fun ⟨h1, h2⟩ => sm_trans h1 (sm_symm h2)

/-- ✱102·41. \(\vdash : \gamma \in \text{Nc}(\alpha _{\beta })ʻ\delta . \gamma'\in \text{Nc}(\alpha _{\beta }ʻ)ʻ\delta . \supset . \gamma \in \text{Nc}(\alpha _{\alpha ʻ})ʻ\gamma' \quad[*102·3·27]\)

The e-text renders PM's `α'` as `αʻ`. -/
theorem pm102_41 {α α' β : Type*} {A G : Set α} {A' G' : Set α'} {B E : Set β} :
    Desc (relT2T Nc A B) E (fun μ => G ∈ μ) ∧ Desc (relT2T Nc A' B) E (fun μ => G' ∈ μ) →
      Desc (relT2T Nc A A') G' (fun μ => G ∈ μ) := by
  simp only [desc_relT2T_Nc]
  exact fun ⟨h1, h2⟩ => sm_trans h1 (sm_symm h2)

/-- ✱102·42. \(\vdash . \alpha \in \text{Nc}(\alpha _{\alpha })ʻ\alpha \quad[*102·3·2.*73·3.*63·103]\) -/
theorem pm102_42 {α : Type*} {A : Set α} : Desc (relT2T Nc A A) A (fun μ => A ∈ μ) := by
  rw [desc_relT2T_Nc]; exact sm_refl A

/-- ✱102·43. \(\vdash . \exists ! \text{Nc}(\alpha _{\alpha })ʻ\alpha \quad[*102·42]\) -/
theorem pm102_43 {α : Type*} {A : Set α} : Desc (relT2T Nc A A) A (fun μ => μ.Nonempty) := by
  rw [desc_relT2T_Nc]; exact ⟨A, sm_refl A⟩

/-- ✱102·44. \(\vdash : \alpha \text{ sm } \beta . \equiv . \alpha \in \text{Nc}(\alpha _{\beta })ʻ\beta . \equiv . \beta \in \text{Nc}(\beta _{\alpha })ʻ\alpha\) -/
theorem pm102_44 {α β : Type*} {A : Set α} {B : Set β} :
    (sm A B ↔ Desc (relT2T Nc A B) B (fun μ => A ∈ μ)) ∧
      (Desc (relT2T Nc A B) B (fun μ => A ∈ μ) ↔ Desc (relT2T Nc B A) A (fun μ => B ∈ μ)) := by
  simp only [desc_relT2T_Nc]
  exact ⟨Iff.rfl, ⟨sm_symm, sm_symm⟩⟩

/-- ✱102·45. \(\vdash :\gamma \in \text{Nc}(\alpha _{\beta })ʻ\delta .\supset .\gamma \in \text{Nc}(\alpha _{\alpha })ʻ\gamma \) -/
theorem pm102_45 {α β : Type*} {A G : Set α} {B E : Set β} :
    Desc (relT2T Nc A B) E (fun μ => G ∈ μ) → Desc (relT2T Nc A A) G (fun μ => G ∈ μ) := by
  simp only [desc_relT2T_Nc]
  exact fun _ => sm_refl G

/-- ✱102·46. \[\begin{aligned}&\vdash :\gamma \in \text{Nc}(\alpha _{\beta })ʻ\delta . \equiv .\delta \in \text{Nc}(\beta _{\alpha }ʻ\gamma . \equiv .\gamma \text{ sm } \delta .\gamma \in tʻ\alpha.\delta \in tʻ\beta \\ &[*102·2·3.*73·31]\end{aligned}\]

(The e-text omits the closing bracket of `Nc(β_α)`.) -/
theorem pm102_46 {α β : Type*} {A G : Set α} {B E : Set β} :
    (Desc (relT2T Nc A B) E (fun μ => G ∈ μ) ↔ Desc (relT2T Nc B A) G (fun μ => E ∈ μ)) ∧
      (Desc (relT2T Nc B A) G (fun μ => E ∈ μ) ↔ (sm G E ∧ G ∈ typ A) ∧ E ∈ typ B) := by
  simp only [desc_relT2T_Nc, typ_eq_univ, Set.mem_univ, and_true]
  exact ⟨⟨sm_symm, sm_symm⟩, ⟨sm_symm, sm_symm⟩⟩

/-- ✱102·5. \(\vdash :\mu \in \text{NC}^\beta (\alpha ). \colon\ldotp .(\exists \delta ).\mu = \text{Nc}(\alpha _{\beta })ʻ\delta \quad[*100·22.*71·41.(*102*01)]\)

`NC^β(α)` is `NCT A B` (✱102·01).

**Status.** proved (reading): transcription error: the e-text prints `:. .` where PM has `≡`. -/
theorem pm102_5 {α β : Type*} {A : Set α} {B : Set β} {μ : Set (Set α)} :
    μ ∈ NCT A B ↔ ∃ E : Set β, Desc (relT2T Nc A B) E (fun ν => μ = ν) := by
  rw [NCT, relT2T_eq']
  exact exists_congr fun E => (desc_Nc E (fun ν => μ = ν)).symm

/-- ✱102·501. \(\vdash .\text{Nc}(\alpha _{\beta }ʻ\delta \in \text{NC}^\beta (\alpha ) \quad[*102·5·36]\)

(The e-text omits the closing bracket of `Nc(α_β)`.) -/
theorem pm102_501 {α β : Type*} {A : Set α} {B E : Set β} :
    Desc (relT2T Nc A B) E (fun μ => μ ∈ NCT A B) := by
  rw [desc_relT2T_Nc, NCT_eq_NC]; exact nc_mem_NC E

/-- ✱102·51. \[\begin{aligned}\vdash :\gamma \in \text{Nc}(\alpha _{\beta })ʻ\delta .\supset .&\text{Nc}((\alpha _{\beta })ʻ\delta = \text{Nc}(\alpha _{\alpha })ʻ\gamma .\\ &\text{Nc}(\alpha _{\beta })ʻ\delta \in \text{NC}^\beta (\alpha ).\text{Nc}(\alpha _{\alpha })ʻ\gamma \in \text{NC}^\alpha (\alpha )\end{aligned}\]

(The e-text prints a superfluous bracket in `Nc((α_β)'δ`.) The conclusion is a product of three,
bracketed to the left; `Nc(α_β)'δ = Nc(α_α)'γ` has two descriptions, the first with the larger
scope. -/
theorem pm102_51 {α β : Type*} {A G : Set α} {B E : Set β} :
    Desc (relT2T Nc A B) E (fun μ => G ∈ μ) →
      (Desc (relT2T Nc A B) E (fun μ => Desc (relT2T Nc A A) G (fun ν => μ = ν)) ∧
        Desc (relT2T Nc A B) E (fun μ => μ ∈ NCT A B)) ∧
        Desc (relT2T Nc A A) G (fun ν => ν ∈ NCT A A) := by
  simp only [desc_relT2T_Nc, NCT_eq_NC]
  intro h
  exact ⟨⟨nc_eq_nc_of_sm (sm_symm h), nc_mem_NC E⟩, nc_mem_NC G⟩

/-- ✱102·52. \(\vdash :\exists ! \text{Nc}(\alpha _{\beta })ʻ\delta .\supset .\text{Nc}(\alpha _{\beta })ʻ\delta \in \text{NC}^\alpha (\alpha ) \quad[*102·51]\) -/
theorem pm102_52 {α β : Type*} {A : Set α} {B E : Set β} :
    Desc (relT2T Nc A B) E (fun μ => μ.Nonempty) →
      Desc (relT2T Nc A B) E (fun μ => μ ∈ NCT A A) := by
  simp only [desc_relT2T_Nc, NCT_eq_NC]
  rintro ⟨G, hG⟩
  exact ⟨G, nc_eq_nc_of_sm (sm_symm hG)⟩

/-- ✱102·53. \(\vdash .\text{NC}^\beta (\alpha )-\iota ʻ\Lambda \subset \text{NC}^\alpha (\alpha )\) -/
theorem pm102_53 {α β : Type*} {A : Set α} {B : Set β} : NCT A B \ ι Λ ⊆ NCT A A := by
  rw [NCT_eq_NC, NCT_eq_NC]
  rintro μ ⟨⟨E, rfl⟩, hne⟩
  obtain ⟨G, hG⟩ := nonempty_of_not_mem_iota_null hne
  exact ⟨G, nc_eq_nc_of_sm (sm_symm hG)⟩

/-- ✱102·54. \(\vdash :\delta \in \text{Nc}(\beta _{\alpha })ʻ\gamma .\supset .\text{Nc}(\alpha _{\beta })ʻ\delta = \text{Nc}(\alpha _{\alpha })ʻ\gamma \quad[*102·51·46]\) -/
theorem pm102_54 {α β : Type*} {A G : Set α} {B E : Set β} :
    Desc (relT2T Nc B A) G (fun μ => E ∈ μ) →
      Desc (relT2T Nc A B) E (fun μ => Desc (relT2T Nc A A) G (fun ν => μ = ν)) := by
  simp only [desc_relT2T_Nc]
  exact nc_eq_nc_of_sm

/-- ✱102·541. \(\vdash :\exists ! \text{Nc}(\beta _{\alpha })ʻ\gamma .\supset .\text{Nc}(\alpha _{\alpha })ʻ\gamma \in \text{NC}^\beta (\alpha )-tʻ\Lambda\)

**Status.** proved (corrected): the e-text prints `NC^β(α) − t'Λ`; since `t'Λ` is the whole type
of `Λ`, `NC^β(α) − t'Λ` is null and the printed conclusion is false whenever the hypothesis holds
(`pm102_541_printed_false`: `α = β = Unit`, `γ = Λ`). PM's demonstration (and ✱102·55, which
cites this proposition) shows that `ι'Λ` is meant (presumably a misprint of `ι` as `t`). -/
theorem pm102_541 {α β : Type*} {A G : Set α} {B : Set β} :
    Desc (relT2T Nc B A) G (fun μ => μ.Nonempty) →
      Desc (relT2T Nc A A) G (fun ν => ν ∈ NCT A B \ ι Λ) := by
  simp only [desc_relT2T_Nc, NCT_eq_NC]
  rintro ⟨E, hE⟩
  refine ⟨⟨E, nc_eq_nc_of_sm (sm_symm hE)⟩, fun h => ?_⟩
  have h' : nc α G = Λ := h
  have hG : G ∈ nc α G := self_mem_nc G
  rw [h', Null_eq_empty] at hG
  exact hG

/-- The printed form of ✱102·541 (with `t'Λ`) is false. -/
theorem pm102_541_printed_false : ¬ ∀ {A G B : Set Unit},
    Desc (relT2T Nc B A) G (fun μ => μ.Nonempty) →
      Desc (relT2T Nc A A) G (fun ν => ν ∈ NCT A B \ typ (Λ : Set (Set Unit))) := by
  intro h
  have := @h ∅ ∅ ∅ (by rw [desc_relT2T_Nc]; exact ⟨∅, sm_refl _⟩)
  rw [desc_relT2T_Nc] at this
  exact this.2 (mem_typ _ _)

/-- ✱102·55. \(\vdash : \Lambda {\sim}\in \text{NC}^\alpha (\beta ) . \supset . \text{NC}^\beta (\alpha ) - \iota ʻ\Lambda = \text{NC}^\alpha (\alpha )\)

`NC^α(β)` is `NCT B A`. -/
theorem pm102_55 {α β : Type*} {A : Set α} {B : Set β} :
    Λ ∉ NCT B A → NCT A B \ ι Λ = NCT A A := by
  intro hΛ
  refine Set.Subset.antisymm pm102_53 ?_
  rw [NCT_eq_NC] at hΛ
  rw [NCT_eq_NC, NCT_eq_NC]
  rintro μ ⟨G, rfl⟩
  have hne : (nc β G).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hΛ (mem_NC.2 ⟨G, by rw [h, Null_eq_empty]⟩)
  obtain ⟨E, hE⟩ := hne
  refine ⟨⟨E, nc_eq_nc_of_sm (sm_symm hE)⟩, fun h => ?_⟩
  have h' : nc α G = Λ := h
  have hG : G ∈ nc α G := self_mem_nc G
  rw [h', Null_eq_empty] at hG
  exact hG

/-- ✱102·6. \(\vdash . \text{Nc}(\alpha )ʻ\beta = \text{Nc}(\alpha _{\beta })ʻ\beta = \hat{\gamma} (\gamma \text{ sm } \beta . \gamma \in tʻ\alpha ) = \text{Nc}ʻ\beta \cap tʻ\alpha\)

`Nc(α)` is `relT2 Nc A` (✱65·04). `Nc'β ∩ t'α` is `nc α B ∩ typ A` (the intersection with `t'α`
puts `Nc'β` in the type of `α`). The chain of four is the conjunction of its three links. -/
theorem pm102_6 {α β : Type*} {A : Set α} {B : Set β} :
    (Desc (relT2 Nc A) B (fun μ => Desc (relT2T Nc A B) B (fun ν => μ = ν)) ∧
      Desc (relT2T Nc A B) B (fun ν => ν = {G | sm G B ∧ G ∈ typ A})) ∧
      {G | sm G B ∧ G ∈ typ A} = nc α B ∩ typ A := by
  refine ⟨⟨(desc_relT2_Nc' _ _ _).2 ((desc_relT2T_Nc _ _ _ _).2 rfl),
    (desc_relT2T_Nc _ _ _ _).2 (Set.ext fun G => ?_)⟩, Set.ext fun G => ?_⟩
  · show sm G B ↔ sm G B ∧ G ∈ typ A
    rw [typ_eq_univ]; simp
  · show sm G B ∧ G ∈ typ A ↔ G ∈ nc α B ∩ typ A
    rw [typ_eq_univ, Set.inter_univ]; simp; exact Iff.rfl

/-- ✱102·61. \(\vdash : \delta \in tʻ\beta . \supset . \text{Nc}(\alpha )ʻ\delta = \text{Nc}(\alpha _{\beta })ʻ\delta \) -/
theorem pm102_61 {α β : Type*} {A : Set α} {B E : Set β} :
    E ∈ typ B → Desc (relT2 Nc A) E (fun μ => Desc (relT2T Nc A B) E (fun ν => μ = ν)) := by
  intro _
  rw [desc_relT2_Nc', desc_relT2T_Nc]

/-- ✱102·62. \(\vdash . \text{NC}^\beta (\alpha ) = \text{Nc}(\alpha )ʻʻtʻ\beta\)

`Nc(α)''t'β` is `relT2 Nc A ʻʻ typ B`. -/
theorem pm102_62 {α β : Type*} {A : Set α} {B : Set β} : NCT A B = relT2 Nc A ʻʻ typ B := by
  rw [NCT_eq_NC, relT2_eq', typ_eq_univ]
  ext μ
  constructor
  · rintro ⟨E, rfl⟩; exact ⟨E, trivial, rfl⟩
  · rintro ⟨E, -, h⟩; exact ⟨E, h⟩

/-- ✱102·63. \(\vdash : \mu = \text{Nc}ʻ\gamma . \alpha \in \mu . \supset . \mu = \text{Nc}(\alpha )ʻ\gamma\)

`α ∈ μ` puts `α` in the type of the members of `μ`; `Nc'γ = μ` is in the type of `μ`. -/
theorem pm102_63 {α γ : Type*} {μ : Set (Set α)} {A : Set α} {G : Set γ} :
    μ = nc α G ∧ A ∈ μ → Desc (relT2 Nc A) G (fun ν => μ = ν) := by
  rintro ⟨rfl, -⟩
  rw [desc_relT2_Nc']

/-- ✱102·64. \(\vdash : \mu \in \text{NC} . \exists !\mu . \supset . (\exists \alpha ,\gamma ) . \mu = \text{Nc}(\alpha )ʻ\gamma \quad[*102·63.*100·4]\) -/
theorem pm102_64 {α β : Type*} {μ : Set (Set α)} :
    μ ∈ NC β ∧ μ.Nonempty → ∃ (A : Set α) (G : Set β), Desc (relT2 Nc A) G (fun ν => μ = ν) := by
  rintro ⟨⟨G, rfl⟩, A, -⟩
  exact ⟨A, G, (desc_relT2_Nc' _ _ _).2 rfl⟩

/-- ✱102·71. \(\vdash : R \in \text{Cls} \rightarrow 1 . \text{D}ʻR\subset \alpha . \text{ᗡ}ʻR\subset \text{Cl}ʻ\alpha . \supset . \exists ! \text{Cl}ʻ\alpha - \text{ᗡ}ʻR\)

`R ∈ Cls → 1` with `ᗡ'R ⊂ Cl'α`: `R` relates members of the type of `α` to classes of them. -/
theorem pm102_71 {α : Type*} {R : α → Set α → Prop} {A : Set α} :
    (R ∈ arrow Cls one ∧ dom R ⊆ A) ∧ codom R ⊆ cl A → (cl A \ codom R).Nonempty := by
  rintro ⟨⟨h1, h2⟩, -⟩
  have hmo := mem_arrow_Cls_one.1 h1
  refine ⟨{x | x ∈ dom R ∧ ∀ Y, R x Y → x ∉ Y}, fun x hx => h2 hx.1, ?_⟩
  rintro ⟨x, hx⟩
  by_cases hxW : x ∈ {x | x ∈ dom R ∧ ∀ Y, R x Y → x ∉ Y}
  · exact hxW.2 _ hx hxW
  · exact hxW ⟨⟨_, hx⟩, fun Y hY => by rw [← hmo x _ Y ⟨hx, hY⟩]; exact hxW⟩

/-- ✱102·72. \(\vdash : \beta \subset \alpha . \supset .{\sim}(\beta \text{ sm } \text{Cl}ʻ\alpha )\) -/
theorem pm102_72 {α : Type*} {A B : Set α} : B ⊆ A → ¬ sm B (cl A) := not_sm_cl

/-- ✱102·73. \(\vdash . \text{Nc}(\alpha )ʻtʻ\alpha = \Lambda\)

`Nc(α)'t'α` is `Desc (relT2 Nc A) (typ A) ψ`, `t'α` being the class `typ A` of all classes of the
type of `α`. -/
theorem pm102_73 {α : Type*} {A : Set α} : Desc (relT2 Nc A) (typ A) (fun μ => μ = Λ) := by
  rw [desc_relT2_Nc', nc_typ_eq_empty, Null_eq_empty]

/-- ✱102·74. \(\vdash . \Lambda \in \text{NC}^{tʻ\alpha }(\alpha )\) -/
theorem pm102_74 {α : Type*} {A : Set α} : Λ ∈ NCT A (typ A) := by
  rw [NCT_eq_NC]
  exact mem_NC.2 ⟨typ A, by rw [nc_typ_eq_empty, Null_eq_empty]⟩

/-- ✱102·75. \(\vdash . \text{NC}^{tʻ\alpha }(\alpha ) = \text{NC}^\alpha (\alpha ) \cup \iota ʻ\Lambda \) -/
theorem pm102_75 {α : Type*} {A : Set α} : NCT A (typ A) = NCT A A ∪ ι Λ := by
  rw [NCT_eq_NC, NCT_eq_NC]
  ext μ
  constructor
  · rintro ⟨K, rfl⟩
    by_cases h : (nc α K).Nonempty
    · obtain ⟨G, hG⟩ := h
      exact Or.inl ⟨G, nc_eq_nc_of_sm (sm_symm hG)⟩
    · right
      rw [Set.not_nonempty_iff_eq_empty] at h
      show nc α K = Λ
      rw [h, Null_eq_empty]
  · rintro (⟨G, rfl⟩ | h)
    · exact ⟨iota ʻʻ G, nc_eq_nc_of_sm (sm_symm (sm_iota_img G))⟩
    · have h' : μ = Λ := h
      rw [h']
      exact mem_NC.2 ⟨typ A, by rw [nc_typ_eq_empty, Null_eq_empty]⟩

/-- ✱102·8. \(\vdash : \gamma \in \text{Nc}(\alpha _{\beta })ʻ\delta . \gamma \text{ sm } \zeta . \zeta \in tʻ\xi . \supset . \zeta \in \text{Nc}(\xi _{\beta })ʻ\delta . \zeta \in \text{Nc}(\xi _{\alpha })ʻ\gamma\) -/
theorem pm102_8 {α β ξ : Type*} {A G : Set α} {B E : Set β} {X Z : Set ξ} :
    (Desc (relT2T Nc A B) E (fun μ => G ∈ μ) ∧ sm G Z) ∧ Z ∈ typ X →
      Desc (relT2T Nc X B) E (fun μ => Z ∈ μ) ∧ Desc (relT2T Nc X A) G (fun μ => Z ∈ μ) := by
  simp only [desc_relT2T_Nc]
  rintro ⟨⟨h1, h2⟩, -⟩
  exact ⟨sm_trans (sm_symm h2) h1, sm_symm h2⟩

/-- ✱102·81. \(\vdash : \gamma \in \text{Nc}(\alpha _{\beta })ʻ\delta . \supset . \text{ sm }ʻʻ\text{Nc}(\alpha _{\beta })ʻ\delta \cap tʻ\xi = \text{Nc}(\xi _{\beta })ʻ\delta = \text{Nc}(\xi _{\alpha })ʻ\gamma \)

The descriptions have the smallest scopes (each link of the chain); `sm''Nc(α_β)'δ ∩ t'ξ` is in
the type of `ξ` (significance). -/
theorem pm102_81 {α β ξ : Type*} {A G : Set α} {B E : Set β} {X : Set ξ} :
    Desc (relT2T Nc A B) E (fun μ => G ∈ μ) →
      Desc (relT2T Nc A B) E
          (fun μ => Desc (relT2T Nc X B) E (fun ν => sm ʻʻ μ ∩ typ X = ν)) ∧
        Desc (relT2T Nc X B) E (fun ν => Desc (relT2T Nc X A) G (fun ρ => ν = ρ)) := by
  simp only [desc_relT2T_Nc, typ_eq_univ, Set.inter_univ]
  intro h
  exact ⟨pm100_511 ⟨G, h⟩, nc_eq_nc_of_sm (sm_symm h)⟩

/-- ✱102·82. \(\vdash : \mu \in \text{NC}^\beta (\alpha ) . \exists !\mu . \supset . \text{ sm }ʻʻ\mu \cap tʻ\xi \in \text{NC}^\beta (\xi ) \quad[*102·81·5]\) -/
theorem pm102_82 {α β ξ : Type*} {A : Set α} {B : Set β} {X : Set ξ} {μ : Set (Set α)} :
    μ ∈ NCT A B ∧ μ.Nonempty → sm ʻʻ μ ∩ typ X ∈ NCT X B := by
  rw [NCT_eq_NC, NCT_eq_NC]
  rintro ⟨hμ, G, hG⟩
  obtain ⟨E, rfl⟩ := mem_NC.1 hμ
  rw [typ_eq_univ, Set.inter_univ, pm100_511 ⟨G, hG⟩]
  exact nc_mem_NC E

/-- ✱102·83. \[\begin{aligned}\vdash : \mu \in \text{NC}^\beta (\alpha ) . &\exists !\mu . \nu = \text{ sm }ʻʻ\mu \cap tʻ\xi . \exists !\nu . \supset .\\ &\text{ sm }ʻʻ\mu \cap tʻ\zeta = \text{ sm }ʻʻ\nu \cap tʻ\zeta . \mu = \text{ sm }ʻʻ\nu \cap tʻ\alpha\end{aligned}\] -/
theorem pm102_83 {α β ξ ζ : Type*} {A : Set α} {B : Set β} {X : Set ξ} {Z : Set ζ}
    {μ : Set (Set α)} {ν : Set (Set ξ)} :
    ((μ ∈ NCT A B ∧ μ.Nonempty) ∧ ν = sm ʻʻ μ ∩ typ X) ∧ ν.Nonempty →
      sm ʻʻ μ ∩ typ Z = sm ʻʻ ν ∩ typ Z ∧ μ = sm ʻʻ ν ∩ typ A := by
  rw [NCT_eq_NC]
  rintro ⟨⟨⟨hμ, G, hG⟩, rfl⟩, hν⟩
  obtain ⟨E, rfl⟩ := mem_NC.1 hμ
  simp only [typ_eq_univ, Set.inter_univ] at hν ⊢
  have h1 : (sm ʻʻ nc α E : Set (Set ξ)) = nc ξ E := pm100_511 ⟨G, hG⟩
  rw [h1] at hν ⊢
  have e1 : (sm ʻʻ nc α E : Set (Set ζ)) = nc ζ E := pm100_511 ⟨G, hG⟩
  have e2 : (sm ʻʻ nc ξ E : Set (Set ζ)) = nc ζ E := pm100_511 hν
  have e3 : (sm ʻʻ nc ξ E : Set (Set α)) = nc α E := pm100_511 hν
  rw [e1, e2, e3]
  exact ⟨rfl, rfl⟩

/-- ✱102·84. \(\vdash : (\exists \gamma ) . \gamma \text{ sm } \alpha . \gamma \in tʻ\alpha . \delta \text{ sm } \gamma . \equiv . \delta \text{ sm } \alpha\) -/
theorem pm102_84 {α δ : Type*} {A : Set α} {E : Set δ} :
    (∃ G : Set α, (sm G A ∧ G ∈ typ A) ∧ sm E G) ↔ sm E A := by
  constructor
  · rintro ⟨G, ⟨h1, -⟩, h2⟩
    exact sm_trans h2 h1
  · intro h
    exact ⟨A, ⟨sm_refl A, mem_typ _ _⟩, h⟩

/-- ✱102·85. \(\vdash . \text{ sm }ʻʻ\mu \cap tʻ\beta = \text{ sm }_{\beta }ʻʻ\mu \quad[*65·3]\)

`sm_β` is `relT sm B` (✱65·03). -/
theorem pm102_85 {β γ : Type*} {B : Set β} {μ : Set (Set γ)} :
    sm ʻʻ μ ∩ typ B = relT sm B ʻʻ μ := by
  rw [typ_eq_univ, Set.inter_univ, relT_eq]

/-- ✱102·86. \(\vdash : \mu = \text{Nc} (\alpha )ʻ\delta . \exists !\mu . \supset . \text{ sm }_{\xi }ʻʻ\mu = \text{Nc}(\xi )ʻ\delta\) -/
theorem pm102_86 {α δ ξ : Type*} {A : Set α} {E : Set δ} {X : Set ξ} {μ : Set (Set α)} :
    Desc (relT2 Nc A) E (fun ν => μ = ν) ∧ μ.Nonempty →
      Desc (relT2 Nc X) E (fun ν => relT sm X ʻʻ μ = ν) := by
  simp only [desc_relT2_Nc', relT_eq]
  rintro ⟨rfl, G, hG⟩
  exact pm100_511 ⟨G, hG⟩

/-- ✱102·861. \(\vdash . \text{ sm }_{\alpha }ʻʻ\text{ sm }_{\xi }ʻʻ \mu \subset \text{ sm }_{\alpha }ʻʻ\mu \) -/
theorem pm102_861 {α β ξ : Type*} {A : Set α} {X : Set ξ} {μ : Set (Set β)} :
    relT sm A ʻʻ (relT sm X ʻʻ μ) ⊆ relT sm A ʻʻ μ := by
  simp only [relT_eq]
  rintro G ⟨Z, ⟨H, hH, hZH⟩, hGZ⟩
  exact ⟨H, hH, sm_trans hGZ hZH⟩

/-- ✱102·862. \(\vdash \colon\ldotp \eta \in \mu . \supset _{\eta } . \exists !\text{Nc}(\xi )ʻ\eta : \supset . \text{ sm }_{\alpha }ʻʻ\mu = \text{ sm }_{\alpha }ʻʻ\text{ sm }_{\xi }ʻʻ\mu \) -/
theorem pm102_862 {α β ξ : Type*} {A : Set α} {X : Set ξ} {μ : Set (Set β)} :
    (∀ H, H ∈ μ → Desc (relT2 Nc X) H (fun ν => ν.Nonempty)) →
      relT sm A ʻʻ μ = relT sm A ʻʻ (relT sm X ʻʻ μ) := by
  intro h
  refine Set.Subset.antisymm ?_ pm102_861
  simp only [relT_eq]
  rintro G ⟨H, hH, hGH⟩
  obtain ⟨Z, hZ⟩ := (desc_relT2_Nc' _ _ _).1 (h H hH)
  exact ⟨Z, ⟨H, hH, hZ⟩, sm_trans hGH (sm_symm hZ)⟩

/-- ✱102·863. \(\vdash \colon\ldotp \mu = \text{Nc}(\beta )ʻ\delta . \exists !\text{Nc}(\xi )ʻ\delta . \supset : \eta \in \mu . \supset _{\eta } . \exists !\text{Nc}(\xi )ʻ\eta \) -/
theorem pm102_863 {β δ ξ : Type*} {B : Set β} {E : Set δ} {X : Set ξ} {μ : Set (Set β)} :
    Desc (relT2 Nc B) E (fun ν => μ = ν) ∧ Desc (relT2 Nc X) E (fun ν => ν.Nonempty) →
      ∀ H, H ∈ μ → Desc (relT2 Nc X) H (fun ν => ν.Nonempty) := by
  simp only [desc_relT2_Nc']
  rintro ⟨rfl, Z, hZ⟩ H hH
  exact ⟨Z, sm_trans hZ (sm_symm hH)⟩

/-- ✱102·87. \[\begin{aligned}&\vdash : \mu = \text{Nc}(\beta )ʻ\delta . \exists !\text{Nc}(\xi )ʻ\delta . \supset . \text{ sm }_{\alpha }ʻʻ\mu = \text{ sm }_{\alpha }ʻʻ\text{ sm }_{\xi }ʻʻ\mu \\ &[*102·862·863]\end{aligned}\] -/
theorem pm102_87 {α β δ ξ : Type*} {A : Set α} {B : Set β} {E : Set δ} {X : Set ξ}
    {μ : Set (Set β)} :
    Desc (relT2 Nc B) E (fun ν => μ = ν) ∧ Desc (relT2 Nc X) E (fun ν => ν.Nonempty) →
      relT sm A ʻʻ μ = relT sm A ʻʻ (relT sm X ʻʻ μ) :=
  fun h => pm102_862 (pm102_863 h)

/-- ✱102·88. \[\begin{aligned}\vdash : \mu = \text{Nc}(\beta )ʻ\delta . \exists !\text{ sm }_{\xi }ʻʻ\mu . \supset . &\text{ sm }_{\xi }ʻʻ\mu = \text{Nc}(\xi )ʻ\delta . \text{ sm }_{\alpha }ʻʻ\mu = \text{Nc}(\alpha )ʻ\delta .\\ &\text{ sm }_{\alpha }ʻʻ\mu = \text{ sm }_{\alpha }ʻʻ\text{ sm }_{\xi }ʻʻ\mu = \text{ sm }_{\alpha }ʻʻ\text{Nc}(\xi )ʻ\delta\end{aligned}\]

The conclusion is the product of `sm_ξ''μ = Nc(ξ)'δ`, `sm_α''μ = Nc(α)'δ` and the chain
`sm_α''μ = sm_α''sm_ξ''μ = sm_α''Nc(ξ)'δ` (the conjunction of its two links). -/
theorem pm102_88 {α β δ ξ : Type*} {A : Set α} {B : Set β} {E : Set δ} {X : Set ξ}
    {μ : Set (Set β)} :
    Desc (relT2 Nc B) E (fun ν => μ = ν) ∧ (relT sm X ʻʻ μ).Nonempty →
      (Desc (relT2 Nc X) E (fun ν => relT sm X ʻʻ μ = ν) ∧
          Desc (relT2 Nc A) E (fun ν => relT sm A ʻʻ μ = ν)) ∧
        (relT sm A ʻʻ μ = relT sm A ʻʻ (relT sm X ʻʻ μ) ∧
          Desc (relT2 Nc X) E
            (fun ν => relT sm A ʻʻ (relT sm X ʻʻ μ) = relT sm A ʻʻ ν)) := by
  simp only [desc_relT2_Nc', relT_eq]
  rintro ⟨rfl, Z, H, hH, hZH⟩
  have e1 : (sm ʻʻ nc β E : Set (Set ξ)) = nc ξ E := pm100_511 ⟨H, hH⟩
  have e2 : (sm ʻʻ nc β E : Set (Set α)) = nc α E := pm100_511 ⟨H, hH⟩
  have e3 : (sm ʻʻ nc ξ E : Set (Set α)) = nc α E := pm100_511 ⟨Z, sm_trans hZH hH⟩
  rw [e1, e2, e3]
  exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩

/-!
## [✱103] Homogeneous cardinals

*(Vol. 2, p. 36)*

> *Summary of* *103.
>
> In this number, we shall consider cardinals generated by a homogeneous relation of similarity. A "homogeneous" cardinal is to mean all the classes similar to some class \(\alpha\) and of the same type as \(\alpha\). The "homogeneous cardinal of \(\alpha\)" will be defined as \(\text{Nc}ʻ\alpha \cap tʻ\alpha\); we shall denote it by "\(\text{N}_{0}\text{c}ʻ\alpha\)." Then the class of homogeneous cardinals is the class of all such cardinals as "\(\text{N}_{0}\text{c}ʻ\alpha\)," *i.e.* it is \(\text{D}ʻ\text{N}_{0}\text{c}\); this we shall denote by "\(\text{N}_{0}\text{C}\)." The symbol "\(\text{N}_{0}\text{c}ʻ\alpha\)" is typically definite as soon as \(\alpha\) is assigned; "\(\text{N}_{0}\text{C}\)," on the contrary, is typically ambiguous: it must be a \(\text{Cls}^{3}\), but otherwise its type may vary indefinitely. Homogeneous cardinals have, however, many properties which do not require that the ambiguity of "\(\text{N}_{0}\text{C}\)" should be determined, and few which do require this. They are important also as being the simplest kind of cardinals, and as being a kind to which other kinds can usually be reduced.
>
> …

**Lean reading.** `N₀c'α` is `n₀c A`, `N₀C` is `N₀C` (typically definite once the type of the
members of its members is given), `N₀C(α)` is `clsT2 N₀C A`, `NC(α)` is `clsT2 (NC β) A` with the
converse-domain type `β` arbitrary, `NC^β(α)` is `NCT A B`; `Nc(α)`, `Nc(α_α)` are as in ✱102.
Equations between `Nc`s are in free types; in ✱103·16 PM states that convention AT applies, and
the equation `Nc'α = Nc'β` is taken in a type adequate for both sides (the worked example of
`Defs/Part3`). Where `μ ∈ NC` must have the converse-domain type of `α` (✱103·21·27), the status
says so. ✱103·5 (`0 ∈ N₀C`), which the e-text prints inside the entry of ✱103·44, is formalized
as well.

**Status.** proved (all propositions, including ✱103·5; ✱103·01·02 definition; ✱103·16 proved
(reading): convention AT; ✱103·21, ✱103·27 proved (reading): converse-domain type of `NC`;
✱103·51 proved (reading): `[Nonempty α]`)
-/

/-- ✱103·01 (Df). \(\text{N}_{0}\text{c}ʻ\alpha =\text{Nc}ʻ\alpha \cap tʻ\alpha \quad\text{Df}\) -/
theorem pm103_01 {α : Type*} {A : Set α} : n₀c A = nc α A ∩ typ A := rfl

/-- ✱103·02 (Df). \(\text{N}_{0}\text{C}=\text{D}ʻ\text{N}_{0}\text{c} \quad\text{Df}\) -/
theorem pm103_02 {α : Type*} : Desc D N₀c (fun K => (N₀C : Set (Set (Set α))) = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱103·1. \(\vdash .\text{N}_{0}\text{c}ʻ\alpha =(\text{Nc}ʻ\alpha )_{\alpha }=\text{Nc}(\alpha )ʻ\alpha =\text{Nc}(\alpha _{\alpha })ʻ\alpha \quad[*102·6.(*103·01)]\)

`(Nc'α)_α` is `clsT (nc α A) A` (✱65·01), `Nc(α)` is `relT2 Nc A` (✱65·04), `Nc(α_α)` is
`relT2T Nc A A` (✱65·11); the chain is the conjunction of its links. -/
theorem pm103_1 {α : Type*} {A : Set α} :
    (n₀c A = clsT (nc α A) A ∧ Desc (relT2 Nc A) A (fun μ => clsT (nc α A) A = μ)) ∧
      Desc (relT2 Nc A) A (fun μ => Desc (relT2T Nc A A) A (fun ν => μ = ν)) :=
  ⟨⟨rfl, (desc_relT2_Nc' _ _ _).2 (clsT_eq _ _)⟩,
    (desc_relT2_Nc' _ _ _).2 ((desc_relT2T_Nc _ _ _ _).2 rfl)⟩

/-- ✱103·11. \[\begin{aligned}&\vdash :\beta \in \text{N}_{0}\text{c}ʻ\alpha .\equiv .\beta \text{ sm }\alpha .\beta \in tʻ\alpha .\equiv .\beta \in \text{Nc}ʻ\alpha .\beta \in tʻ\alpha\\ &[*103·1.*102·6]\end{aligned}\] -/
theorem pm103_11 {α : Type*} {A B : Set α} :
    (B ∈ n₀c A ↔ sm B A ∧ B ∈ typ A) ∧ (sm B A ∧ B ∈ typ A ↔ B ∈ nc α A ∧ B ∈ typ A) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ✱103·12. \(\vdash .\alpha \in \text{N}_{0}\text{c}ʻ\alpha \quad[*103·11.*73·3.*63·103]\) -/
theorem pm103_12 {α : Type*} {A : Set α} : A ∈ n₀c A := self_mem_n₀c A

/-- ✱103·13. \(\vdash .\exists !\text{N}_{0}\text{c}ʻ\alpha \quad[*103·12.*10·24]\) -/
theorem pm103_13 {α : Type*} {A : Set α} : (n₀c A).Nonempty := n₀c_nonempty A

/-- ✱103·14. \(\vdash :\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta .\equiv .\alpha \in \text{N}_{0}\text{c}ʻ\beta .\equiv .\beta \in \text{N}_{0}\text{c}ʻ\alpha .\equiv .\alpha \text{ sm }\beta .\alpha \in tʻ\beta\) -/
theorem pm103_14 {α : Type*} {A B : Set α} :
    ((n₀c A = n₀c B ↔ A ∈ n₀c B) ∧ (A ∈ n₀c B ↔ B ∈ n₀c A)) ∧
      (B ∈ n₀c A ↔ sm A B ∧ A ∈ typ B) := by
  rw [mem_n₀c, mem_n₀c, n₀c_eq_n₀c_iff]
  exact ⟨⟨Iff.rfl, ⟨sm_symm, sm_symm⟩⟩, ⟨fun h => ⟨sm_symm h, mem_typ _ _⟩, fun h => sm_symm h.1⟩⟩

/-- ✱103·15. \(\vdash :\exists !\text{N}_{0}\text{c}ʻ\alpha \cap \text{N}_{0}\text{c}ʻ\beta .\equiv .\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta\) -/
theorem pm103_15 {α : Type*} {A B : Set α} :
    (n₀c A ∩ n₀c B).Nonempty ↔ n₀c A = n₀c B := by
  constructor
  · rintro ⟨G, h1, h2⟩
    exact n₀c_eq_n₀c_iff.2 (sm_trans (sm_symm (mem_n₀c.1 h1)) (mem_n₀c.1 h2))
  · intro h
    exact ⟨A, self_mem_n₀c A, h ▸ self_mem_n₀c A⟩

/-- ✱103·16. \(\vdash : \text{N}_{0}\text{c}ʻ\alpha = \text{Nc}ʻ\beta . \equiv . \text{Nc}ʻ\alpha = \text{Nc}ʻ\beta \)

PM: "the equation `Nc'α = Nc'β` must be supposed to hold in any type for which it is
significant" (convention AT). The `Nc'β` of the first equation is in the type of `α` (meaning);
the second equation is in a type `γ` adequate for both sides.

**Status.** proved (reading): convention AT (Prefatory Statement, VI): the equation
`Nc'α = Nc'β` is taken in a type adequate for both sides. -/
theorem pm103_16 {α β γ : Type*} {A : Set α} {B : Set β} (hA : AdeqNc γ A) (_hB : AdeqNc γ B) :
    n₀c A = nc α B ↔ nc γ A = nc γ B := by
  rw [n₀c_eq_nc, nc_eq_nc_iff ⟨A, self_mem_nc A⟩, nc_eq_nc_iff (hA.nc_nonempty A)]

/-- ✱103·2. \[\begin{aligned}&\vdash : \mu \in \text{N}_{0}\text{C} . \equiv . (\exists \alpha ) . \mu = \text{Nc}ʻ\alpha \cap tʻ\alpha . \equiv . (\exists \alpha ). \mu = \text{N}_{0}\text{c}ʻ\alpha\\ &[*71·41.*100·22.(*103·01·02)]\end{aligned}\]

`Nc'α ∩ t'α` is `nc α A ∩ typ A` (the intersection puts `Nc'α` in the type of `α`). -/
theorem pm103_2 {α : Type*} {μ : Set (Set α)} :
    (μ ∈ N₀C ↔ ∃ A, μ = nc α A ∩ typ A) ∧ ((∃ A, μ = nc α A ∩ typ A) ↔ ∃ A, μ = n₀c A) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ✱103·21. \(\vdash . \text{N}_{0}\text{c}ʻ\alpha \in \text{N}_{0}\text{C} . \text{N}_{0}\text{c}ʻ\alpha \in \text{NC} \quad[*103·2.*100·2·4.*14·28.*65·13]\)

**Status.** proved (reading): the converse domain of `NC` is taken in the type of `α` (as for
✱100·41; PM's proof cites ✱100·2·4). -/
theorem pm103_21 {α : Type*} {A : Set α} : n₀c A ∈ N₀C ∧ n₀c A ∈ NC α :=
  ⟨⟨A, rfl⟩, mem_NC.2 ⟨A, n₀c_eq_nc A⟩⟩

/-- ✱103·22. \(\vdash : \mu \in \text{N}_{0}\text{C} . \supset . \exists !\mu \quad[*103·13·2]\) -/
theorem pm103_22 {α : Type*} {μ : Set (Set α)} : μ ∈ N₀C → μ.Nonempty := by
  rintro ⟨A, rfl⟩
  exact n₀c_nonempty A

/-- ✱103·23. \(\vdash . \Lambda {\sim}\in \text{N}_{0}\text{C} \quad[*103·22]\) -/
theorem pm103_23 {α : Type*} : (Λ : Set (Set α)) ∉ N₀C := by
  intro h
  obtain ⟨B, hB⟩ := pm103_22 h
  rw [Null_eq_empty] at hB
  exact hB

/-- ✱103·24. \(\vdash . \text{N}_{0}\text{C} \in \text{Cls ex}^{2}\,\text{excl}\quad[*100·43.*103·23.*84·13]\)

`Cls ex² excl` is `ClsEx2excl` (✱84·03). -/
theorem pm103_24 {α : Type*} : (N₀C : Set (Set (Set α))) ∈ ClsEx2excl := by
  refine ⟨?_, pm103_23⟩
  show ∀ μ ν, (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ μ ≠ ν → μ ∩ ν = Λ
  rintro μ ν ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, hne⟩
  rw [Null_eq_empty]
  by_contra h
  exact hne (pm103_15.1 (Set.nonempty_iff_ne_empty.2 h))

/-- ✱103·25. \(\vdash \colon\ldotp \mu ,\nu \in \text{N}_{0}\text{C} . \supset : \exists !\mu \cap \nu . \equiv . \mu = \nu \quad[*103·24 . *84·135]\)

`μ ∩ ν` puts `μ` and `ν` in one type, so the two `N₀C`s are in one type. -/
theorem pm103_25 {α : Type*} {μ ν : Set (Set α)} :
    μ ∈ N₀C ∧ ν ∈ N₀C → ((μ ∩ ν).Nonempty ↔ μ = ν) := by
  rintro ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩
  exact pm103_15

/-- ✱103·26. \(\vdash \colon\ldotp \mu \in \text{NC}. \supset : \alpha \in \mu . \equiv . \text{N}_{0}\text{c}ʻ\alpha = \mu\) -/
theorem pm103_26 {α β : Type*} {μ : Set (Set α)} {A : Set α} :
    μ ∈ NC β → (A ∈ μ ↔ n₀c A = μ) := by
  intro h
  obtain ⟨B, rfl⟩ := mem_NC.1 h
  rw [n₀c_eq_nc]
  exact ⟨fun h => nc_eq_nc_of_sm h, fun e => e ▸ self_mem_nc A⟩

/-- ✱103·27. \(\vdash : \mu = \text{N}_{0}\text{c}ʻ\alpha . \equiv . \mu \in \text{NC} . \alpha \in \mu\)

**Status.** proved (reading): the converse domain of `NC` is taken in the type of `α` (the
implication from right to left holds for every converse-domain type; from left to right PM's
proof uses ✱103·21). -/
theorem pm103_27 {α : Type*} {μ : Set (Set α)} {A : Set α} : μ = n₀c A ↔ μ ∈ NC α ∧ A ∈ μ := by
  constructor
  · rintro rfl
    exact ⟨mem_NC.2 ⟨A, n₀c_eq_nc A⟩, self_mem_n₀c A⟩
  · rintro ⟨h, hA⟩
    exact ((pm103_26 h).1 hA).symm

/-- ✱103·28. \(\vdash : (\exists \alpha ) . \gamma \text{ sm } \alpha . \mu = \text{N}_{0}\text{c}ʻ\alpha . \equiv . \exists ! \mu . \mu = \text{Nc}ʻ\gamma\)

`μ = Nc'γ` is in the type of `μ`; `γ` has an arbitrary type. -/
theorem pm103_28 {α β : Type*} {μ : Set (Set α)} {G : Set β} :
    (∃ A, sm G A ∧ μ = n₀c A) ↔ μ.Nonempty ∧ μ = nc α G := by
  constructor
  · rintro ⟨A, h, rfl⟩
    exact ⟨n₀c_nonempty A, by rw [n₀c_eq_nc]; exact nc_eq_nc_of_sm (sm_symm h)⟩
  · rintro ⟨⟨A, hA⟩, rfl⟩
    exact ⟨A, sm_symm hA, by rw [n₀c_eq_nc]; exact nc_eq_nc_of_sm (sm_symm hA)⟩

/-- ✱103·3. \(\vdash :\beta \in tʻ\alpha .\supset .\text{N}_{0}\text{c}ʻ\beta =\text{Nc}(\alpha )ʻ\beta =\text{Nc}(\alpha _{\alpha })ʻ\beta =\text{Nc}ʻ\beta \cap tʻ\alpha\) -/
theorem pm103_3 {α : Type*} {A B : Set α} :
    B ∈ typ A →
      (Desc (relT2 Nc A) B (fun μ => n₀c B = μ) ∧
          Desc (relT2 Nc A) B (fun μ => Desc (relT2T Nc A A) B (fun ν => μ = ν))) ∧
        Desc (relT2T Nc A A) B (fun ν => ν = nc α B ∩ typ A) := by
  intro _
  refine ⟨⟨(desc_relT2_Nc' _ _ _).2 (n₀c_eq_nc B),
    (desc_relT2_Nc' _ _ _).2 ((desc_relT2T_Nc _ _ _ _).2 rfl)⟩, (desc_relT2T_Nc _ _ _ _).2 ?_⟩
  show nc α B = nc α B ∩ typ A
  rw [typ_eq_univ, Set.inter_univ]

/-- ✱103·301. \(\vdash .\text{NC}^\alpha (\alpha )=\text{N}_{0}\text{C}(\alpha )\)

`N₀C(α)` is `clsT2 N₀C A` (✱65·02). -/
theorem pm103_301 {α : Type*} {A : Set α} : NCT A A = clsT2 N₀C A := by
  rw [clsT2_eq', NCT_eq_NC]
  ext μ
  constructor
  · intro h
    obtain ⟨B, rfl⟩ := mem_NC.1 h
    exact ⟨B, (n₀c_eq_nc B).symm⟩
  · rintro ⟨B, h⟩
    exact mem_NC.2 ⟨B, h.trans (n₀c_eq_nc B)⟩

/-- ✱103·31. \(\vdash :\exists !\text{Nc}(\alpha _{\beta })ʻ\delta .\supset .\text{Nc}(\alpha _{\beta })ʻ\delta \in \text{N}_{0}\text{C}(\alpha )\) -/
theorem pm103_31 {α β : Type*} {A : Set α} {B E : Set β} :
    Desc (relT2T Nc A B) E (fun μ => μ.Nonempty) →
      Desc (relT2T Nc A B) E (fun μ => μ ∈ clsT2 N₀C A) := by
  simp only [desc_relT2T_Nc, clsT2_eq']
  rintro ⟨G, hG⟩
  exact mem_N₀C.2 ⟨G, by rw [n₀c_eq_nc]; exact nc_eq_nc_of_sm (sm_symm hG)⟩

/-- ✱103·32. \(\vdash .\text{NC}^\beta (\alpha )-\iota ʻ\Lambda \subset \text{N}_{0}\text{C}(\alpha )\) -/
theorem pm103_32 {α β : Type*} {A : Set α} {B : Set β} : NCT A B \ ι Λ ⊆ clsT2 N₀C A := by
  rw [clsT2_eq', NCT_eq_NC]
  rintro μ ⟨hμ, hne⟩
  obtain ⟨E, rfl⟩ := mem_NC.1 hμ
  obtain ⟨G, hG⟩ := nonempty_of_not_mem_iota_null hne
  exact mem_N₀C.2 ⟨G, by rw [n₀c_eq_nc]; exact nc_eq_nc_of_sm (sm_symm hG)⟩

/-- ✱103·33. \(\vdash . \text{NC}(\alpha ) - \iota ʻ\Lambda \subset \text{N}_{0}\text{C}(\alpha )\)

`NC(α)` is `clsT2 (NC β) A` (✱65·02), with the converse-domain type `β` of `NC` arbitrary: "any
possible determination of `NC(α)` makes the above proposition true" (PM, note to ✱103·32). -/
theorem pm103_33 {α β : Type*} {A : Set α} : clsT2 (NC β) A \ ι Λ ⊆ clsT2 N₀C A := by
  rw [clsT2_eq', clsT2_eq']
  rintro μ ⟨hμ, hne⟩
  obtain ⟨E, rfl⟩ := mem_NC.1 hμ
  obtain ⟨G, hG⟩ := nonempty_of_not_mem_iota_null hne
  exact mem_N₀C.2 ⟨G, by rw [n₀c_eq_nc]; exact nc_eq_nc_of_sm (sm_symm hG)⟩

/-- ✱103·34. \(\vdash . \text{NC} - \iota ʻ\Lambda \subset \text{N}_{0}\text{C}\) -/
theorem pm103_34 {α β : Type*} : (NC β : Set (Set (Set α))) \ ι Λ ⊆ N₀C := by
  rintro μ ⟨hμ, hne⟩
  obtain ⟨E, rfl⟩ := mem_NC.1 hμ
  obtain ⟨G, hG⟩ := nonempty_of_not_mem_iota_null hne
  exact mem_N₀C.2 ⟨G, by rw [n₀c_eq_nc]; exact nc_eq_nc_of_sm (sm_symm hG)⟩

/-- ✱103·35. \(\vdash : \Lambda {\sim} \in \text{NC}^\alpha (\beta ) . \supset . \text{NC}^\beta (\alpha ) - \iota ʻ\Lambda = \text{N}_{0}\text{C}(\alpha ) \quad[*102·55 . *103·301]\) -/
theorem pm103_35 {α β : Type*} {A : Set α} {B : Set β} :
    Λ ∉ NCT B A → NCT A B \ ι Λ = clsT2 N₀C A :=
  fun h => (pm102_55 h).trans pm103_301

/-- ✱103·4. \(\vdash . \text{ sm }ʻʻ\text{N}_{0}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha\)

The equation is in an arbitrary type `γ`. -/
theorem pm103_4 {α γ : Type*} {A : Set α} : (sm ʻʻ n₀c A : Set (Set γ)) = nc γ A :=
  sm_img_n₀c A

/-- ✱103·41. \(\vdash . \text{ sm }ʻʻ\text{N}_{0}\text{c}ʻ\alpha \cap tʻ\beta = \text{Nc}(\beta )ʻ\alpha \) -/
theorem pm103_41 {α β : Type*} {A : Set α} {B : Set β} :
    Desc (relT2 Nc B) A (fun μ => sm ʻʻ n₀c A ∩ typ B = μ) := by
  rw [desc_relT2_Nc']
  show sm ʻʻ n₀c A ∩ typ B = nc β A
  rw [typ_eq_univ, Set.inter_univ, sm_img_n₀c]

/-- ✱103·42. \(\vdash :\beta \text{ sm } \alpha . \equiv .\text{Nc}(\beta )ʻ\alpha = \text{N}_{0}\text{c}ʻ\beta \) -/
theorem pm103_42 {α β : Type*} {A : Set α} {B : Set β} :
    sm B A ↔ Desc (relT2 Nc B) A (fun μ => μ = n₀c B) := by
  rw [desc_relT2_Nc']
  show sm B A ↔ nc β A = n₀c B
  rw [n₀c_eq_nc]
  constructor
  · intro h; exact nc_eq_nc_of_sm (sm_symm h)
  · intro e
    have h := self_mem_nc B
    rw [← e] at h
    exact h

/-- ✱103·43. \(\vdash :\mu \in \text{NC}.\supset .\text{ sm }ʻʻ\mu \cap t_{0}ʻ\mu = \mu\)

`t₀'μ` is `typ₀ μ`. -/
theorem pm103_43 {α β : Type*} {μ : Set (Set α)} : μ ∈ NC β → sm ʻʻ μ ∩ typ₀ μ = μ := by
  intro h
  obtain ⟨B, rfl⟩ := mem_NC.1 h
  rw [typ₀_eq_univ, Set.inter_univ]
  by_cases hne : (nc α B).Nonempty
  · exact pm100_511 hne
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    exact sm_img_empty

/-- ✱103·44. \(\vdash \colon\ldotp \mu ,\nu \in \text{N}_{0}\text{C}.\supset :\mu = \text{ sm }ʻʻ\nu .\equiv .\nu = \text{ sm }ʻʻ\mu\)

`μ = sm''ν` is in the type of `μ`, `ν = sm''μ` in that of `ν`; the two `N₀C`s are in the types of
`μ` and `ν`, which are independent. -/
theorem pm103_44 {α β : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ N₀C ∧ ν ∈ N₀C → (μ = sm ʻʻ ν ↔ ν = sm ʻʻ μ) := by
  rintro ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩
  rw [sm_img_n₀c, sm_img_n₀c, n₀c_eq_nc, n₀c_eq_nc, nc_eq_nc_iff ⟨A, self_mem_nc A⟩,
    nc_eq_nc_iff ⟨B, self_mem_nc B⟩]
  exact ⟨sm_symm, sm_symm⟩

/-- ✱103·5. \(\vdash .0\in \text{N}_{0}\text{C}\)

(The e-text prints this proposition inside the entry of ✱103·44.) -/
theorem pm103_5 {α : Type*} : (zero : Set (Set α)) ∈ N₀C := ⟨∅, zero_eq_n₀c_empty⟩

/-- ✱103·51. \(\vdash .1\in \text{N}_{0}\text{C}\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the proof
uses ✱101·241, `∃!1`): `[Nonempty α]` (in an empty type `1 = Λ ∉ N₀C`). -/
theorem pm103_51 {α : Type*} [Nonempty α] : (one : Set (Set α)) ∈ N₀C :=
  let ⟨x⟩ := ‹Nonempty α›
  ⟨{x}, one_eq_n₀c_singleton x⟩

/-!
## [✱104] Ascending cardinals

*(Vol. 2, p. 42)*

> *Summary of* *104.
>
> In this number we have to consider cardinals derived from a relation of similarity which goes from the type of \(\alpha\) to that of \(tʻ\alpha\), or to that of \(t^{2}ʻ\alpha\). The propositions to be proved can be extended, by a mere repetition of the proofs, to \(t^{3}ʻ\alpha\), \(t^{4}ʻ\alpha\), etc. This extension must, however, be made afresh in each instance; we cannot prove that it can be made generally, because mathematical induction cannot be applied to the series \[ t_{0}ʻ\alpha,\quad tʻ\alpha,\quad t^{2}ʻ\alpha,\quad t^{3}ʻ\alpha ,\ldotp\ldots \]
>
> Ascending cardinals, though less important than homogeneous cardinals, yet have considerable importance in arithmetic, because \(\text{Nc}ʻ\alpha \times \text{Nc}ʻ\beta\) and \((\text{Nc}ʻ\alpha)^{\text{Nc}ʻ\beta }\) are defined as the cardinals of classes of higher types than those of \(\alpha\) and \(\beta\), and the same applies to the product of the cardinals of members of a class of classes. In these cases, however, we also need cardinals of relational types, which will be dealt with in *106.
>
> We have to deal, in this number, with three different sets of notions, namely
>
> …

**Lean reading.** `N¹c'α`, `N²c'α`, `N¹C`, `N²C`, `μ^{(1)}`, `μ^{(2)}` are `n1c A`, `n2c A`,
`N1C`, `N2C`, `up1 μ`, `up2 μ` (Defs/Part3), typically definite once `α` or `μ` is given; the
`N₀C` in `N¹C ⊂ N₀C` etc. is at the type significance determines. `ι''α` is `iota ʻʻ A`,
`Cl'1`, `Cl'2` are `cl one`, `cl two`, `Λ_α` is `clsT Λ A`, and `t'α = t'β` (true when
significant) puts `α` and `β` in one type. In ✱104·4 the hypothesis `(w) . w_ι = …` introduces a
real variable `W : α → Set α → α → Prop`, and `ι'y_ι'z` keeps the description `y_ι'z`. As in
✱100·52, ✱104·141·142 take the converse domain of the second `NC` in the type of the members of
`μ`.

**Status.** proved (all propositions; ✱104·01·011·02·021·03·031 definition; ✱104·141, ✱104·142
proved (reading): converse-domain type of `NC`, as in ✱100·52)
-/

/-- ✱104·01 (Df). \(\text{N}^{1}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻtʻ\alpha \quad\text{Df}\) -/
theorem pm104_01 {α : Type*} {A : Set α} : n1c A = nc (Set α) A ∩ typ (typ A) := rfl

/-- ✱104·011 (Df). \(\text{N}^{2}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻt^{2}ʻ\alpha \quad\text{Df}\) -/
theorem pm104_011 {α : Type*} {A : Set α} : n2c A = nc (Set (Set α)) A ∩ typ (typ2 A) := rfl

/-- ✱104·02 (Df). \(\text{N}^{1}\text{C} = \text{D}ʻ\text{N}^{1}\text{c} \quad\text{Df}\) -/
theorem pm104_02 {α : Type*} : Desc D N1c (fun K => (N1C : Set (Set (Set (Set α)))) = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱104·021 (Df). \(\text{N}^{2}\text{C} = \text{D}ʻ\text{N}^{2}\text{c} \quad\text{Df}\) -/
theorem pm104_021 {α : Type*} :
    Desc D N2c (fun K => (N2C : Set (Set (Set (Set (Set α))))) = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱104·03 (Df). \(\mu ^{(1)} = \text{ sm }ʻʻ\mu \cap tʻ\mu \quad\text{Df}\) -/
theorem pm104_03 {α : Type*} {μ : Set (Set α)} : up1 μ = sm ʻʻ μ ∩ typ μ := rfl

/-- ✱104·031 (Df). \(\mu ^{(2)} = \text{ sm }ʻʻ\mu \cap t^{2}ʻ\mu \quad\text{Df}\) -/
theorem pm104_031 {α : Type*} {μ : Set (Set α)} : up2 μ = sm ʻʻ μ ∩ typ2 μ := rfl

/-- ✱104·1. \[\begin{aligned}&\vdash :\beta \in \text{N}^{1}\text{c}ʻ\alpha . \equiv .\beta \in \text{Nc}ʻ\alpha .\beta \in tʻtʻ\alpha . \equiv .\beta \in \text{Nc}ʻ\alpha .\beta \subset tʻ\alpha \\ &[*63·5. (*104-01)]\end{aligned}\]

`β ∈ Nc'α` is attributive (in the type of `β`); `t't'α` is `typ (typ A)`. -/
theorem pm104_1 {α : Type*} {A : Set α} {B : Set (Set α)} :
    (B ∈ n1c A ↔ B ∈ nc (Set α) A ∧ B ∈ typ (typ A)) ∧
      (B ∈ nc (Set α) A ∧ B ∈ typ (typ A) ↔ B ∈ nc (Set α) A ∧ B ⊆ typ A) :=
  ⟨Iff.rfl, by simp only [typ_eq_univ, Set.mem_univ, Set.subset_univ]⟩

/-- ✱104·101. \(\vdash :\beta \in \text{N}^{1}\text{c}ʻ\alpha . \equiv .\beta \text{ sm } \alpha .\beta \subset tʻ\alpha \quad[*100·31.*104·1]\) -/
theorem pm104_101 {α : Type*} {A : Set α} {B : Set (Set α)} :
    B ∈ n1c A ↔ sm B A ∧ B ⊆ typ A := by
  rw [n1c_eq, typ_eq_univ]
  simp only [Set.subset_univ, and_true]
  exact Iff.rfl

/-- ✱104·102. \(\vdash .\text{N}^{1}\text{c}ʻ\alpha = \text{Nc}(tʻ\alpha )ʻ\alpha = \text{Nc} {(tʻ\alpha )_{\alpha }}ʻ\alpha \quad[*102·6.(*104·01)]\)

`Nc(t'α)` is `relT2 Nc (typ A)` and `Nc{(t'α)_α}` is `relT2T Nc (typ A) A`. -/
theorem pm104_102 {α : Type*} {A : Set α} :
    Desc (relT2 Nc (typ A)) A (fun μ => n1c A = μ) ∧
      Desc (relT2 Nc (typ A)) A (fun μ => Desc (relT2T Nc (typ A) A) A (fun ν => μ = ν)) :=
  ⟨(desc_relT2_Nc' _ _ _).2 (n1c_eq A), (desc_relT2_Nc' _ _ _).2 ((desc_relT2T_Nc _ _ _ _).2 rfl)⟩

/-- ✱104·11. \[\begin{aligned}&\vdash :\beta \in \text{N}^{2}\text{c}ʻ\alpha . \equiv .\beta \in \text{Nc}ʻ\alpha . \beta \in tʻt^{2}ʻ\alpha . \equiv .\beta \in \text{Nc}ʻ\alpha .\beta \subset t^{2}ʻ\alpha\\ &[*63·5.(*104·011)]\end{aligned}\] -/
theorem pm104_11 {α : Type*} {A : Set α} {B : Set (Set (Set α))} :
    (B ∈ n2c A ↔ B ∈ nc (Set (Set α)) A ∧ B ∈ typ (typ2 A)) ∧
      (B ∈ nc (Set (Set α)) A ∧ B ∈ typ (typ2 A) ↔ B ∈ nc (Set (Set α)) A ∧ B ⊆ typ2 A) :=
  ⟨Iff.rfl, by simp only [typ2, typ_eq_univ, Set.mem_univ, Set.subset_univ]⟩

/-- ✱104·111. \(\vdash :\beta \in \text{N}^{2}\text{c}ʻ\alpha . \equiv .\beta \text{ sm } \alpha .\beta \subset t^{2}ʻ\alpha \quad[*100·31.*104·11]\) -/
theorem pm104_111 {α : Type*} {A : Set α} {B : Set (Set (Set α))} :
    B ∈ n2c A ↔ sm B A ∧ B ⊆ typ2 A := by
  rw [n2c_eq]
  simp only [typ2, typ_eq_univ, Set.subset_univ, and_true]
  exact Iff.rfl

/-- ✱104·112. \(\vdash .\text{N}^{2}\text{c}ʻ\alpha = \text{Nc}(t^{2}ʻ\alpha )ʻ\alpha = \text{Nc}{(t^{2}ʻ\alpha )_{\alpha }}ʻ\alpha \quad[*102·6.(*104·011)]\) -/
theorem pm104_112 {α : Type*} {A : Set α} :
    Desc (relT2 Nc (typ2 A)) A (fun μ => n2c A = μ) ∧
      Desc (relT2 Nc (typ2 A)) A (fun μ => Desc (relT2T Nc (typ2 A) A) A (fun ν => μ = ν)) :=
  ⟨(desc_relT2_Nc' _ _ _).2 (n2c_eq A), (desc_relT2_Nc' _ _ _).2 ((desc_relT2T_Nc _ _ _ _).2 rfl)⟩

/-- ✱104·12. \(\vdash :\beta \in \text{N}^{1}\text{c}ʻ\alpha .\gamma \in \text{N}^{1}\text{c}ʻ\beta .\supset .\gamma \in \text{N}^{2}\text{c}ʻ\alpha\) -/
theorem pm104_12 {α : Type*} {A : Set α} {B : Set (Set α)} {G : Set (Set (Set α))} :
    B ∈ n1c A ∧ G ∈ n1c B → G ∈ n2c A := by
  simp only [n1c_eq, n2c_eq]
  exact fun ⟨h1, h2⟩ => sm_trans h2 h1

/-- ✱104·121. \(\vdash :\beta \in \text{N}^{1}\text{c}ʻ\alpha .\gamma \in \text{N}^{2}\text{c}ʻ\alpha .\supset .\gamma \in \text{N}^{1}\text{c}ʻ\beta \) -/
theorem pm104_121 {α : Type*} {A : Set α} {B : Set (Set α)} {G : Set (Set (Set α))} :
    B ∈ n1c A ∧ G ∈ n2c A → G ∈ n1c B := by
  simp only [n1c_eq, n2c_eq]
  exact fun ⟨h1, h2⟩ => sm_trans h2 (sm_symm h1)

/-- ✱104·122. \(\vdash :\beta \in \text{N}^{1}\text{c}ʻ\alpha .\supset .\text{N}^{1}\text{c}ʻ\beta = \text{N}^{2}\text{c}ʻ\alpha \quad[*104·12·121]\) -/
theorem pm104_122 {α : Type*} {A : Set α} {B : Set (Set α)} : B ∈ n1c A → n1c B = n2c A := by
  simp only [n1c_eq, n2c_eq]
  exact nc_eq_nc_of_sm

/-- ✱104·123. \(\vdash :\text{N}_{0}\text{c}ʻ\beta = \text{N}^{1}\text{c}ʻ\alpha .\supset . \text{N}^{1}\text{c}ʻ\beta = \text{N}^{2}\text{c}ʻ\alpha \quad[*104·122.*103·26]\) -/
theorem pm104_123 {α : Type*} {A : Set α} {B : Set (Set α)} :
    n₀c B = n1c A → n1c B = n2c A := by
  intro h
  apply pm104_122
  rw [← h]
  exact self_mem_n₀c B

/-- ✱104·13. \(\vdash :\mu \in \text{N}^{1}\text{C}. \equiv .(\exists \alpha ).\mu = \text{N}^{1}\text{c}ʻ\alpha \quad[*100·122.*71·41.(*104·02)]\)

(The e-text cites ✱100·122 for ✱100·22.) -/
theorem pm104_13 {α : Type*} {μ : Set (Set (Set α))} : μ ∈ N1C ↔ ∃ A, μ = n1c A := Iff.rfl

/-- ✱104·14. \[\begin{aligned}&\vdash :\delta \in \mu ^{(1)}. \equiv .(\exists \gamma ).\gamma \in \mu .\delta \text{ sm } \gamma .\delta \in tʻ\mu . \equiv .(\exists \gamma ).\gamma \in \mu .\delta \text{ sm } \gamma .\delta \subset tʻ\gamma\\ &[*37·1.*63·22.(*104·03)]\end{aligned}\]

`δ` and `γ` are of the types forced by `δ ∈ t'μ` and `γ ∈ μ`. -/
theorem pm104_14 {α : Type*} {μ : Set (Set α)} {E : Set (Set α)} :
    (E ∈ up1 μ ↔ ∃ G, (G ∈ μ ∧ sm E G) ∧ E ∈ typ μ) ∧
      ((∃ G, (G ∈ μ ∧ sm E G) ∧ E ∈ typ μ) ↔ ∃ G, (G ∈ μ ∧ sm E G) ∧ E ⊆ typ G) := by
  rw [up1_eq]
  exact ⟨⟨fun ⟨G, hG, h⟩ => ⟨G, ⟨hG, h⟩, mem_typ _ _⟩, fun ⟨G, ⟨hG, h⟩, _⟩ => ⟨G, hG, h⟩⟩,
    ⟨fun ⟨G, h, _⟩ => ⟨G, h, by rw [typ_eq_univ]; exact Set.subset_univ _⟩,
      fun ⟨G, h, _⟩ => ⟨G, h, mem_typ _ _⟩⟩⟩

/-- ✱104·141. \(\vdash :\mu \in \text{NC}.\exists !\mu .\supset .\mu ^{(1)}\in \text{NC} \quad[*100·52]\)

**Status.** proved (reading): as in ✱100·52 (which PM cites), the converse domain of the second
`NC` is taken in the type of the members of `μ`. -/
theorem pm104_141 {α β : Type*} {μ : Set (Set α)} :
    μ ∈ NC β ∧ μ.Nonempty → up1 μ ∈ NC α := by
  rw [up1_eq]; exact pm100_52

/-- ✱104·142. \(\vdash :\mu \in \text{NC}.\exists !\mu .\supset .\mu ^{(2)}\in \text{NC} \quad[*100·52]\)

**Status.** proved (reading): as in ✱100·52 (which PM cites), the converse domain of the second
`NC` is taken in the type of the members of `μ`. -/
theorem pm104_142 {α β : Type*} {μ : Set (Set α)} :
    μ ∈ NC β ∧ μ.Nonempty → up2 μ ∈ NC α := by
  rw [up2_eq]; exact pm100_52

/-- ✱104·15. \(\vdash :\mu \in \text{N}^{2}\text{C}. \equiv .(\exists \alpha ).\mu = \text{N}^{2}\text{c}ʻ\alpha \quad[*100·22.*71·41. (*104·021)]\) -/
theorem pm104_15 {α : Type*} {μ : Set (Set (Set (Set α)))} :
    μ ∈ N2C ↔ ∃ A, μ = n2c A := Iff.rfl

/-- ✱104·2. \(\vdash .\iota ʻʻ\alpha \in \text{N}^{1}\text{c}ʻ\alpha\) -/
theorem pm104_2 {α : Type*} {A : Set α} : iota ʻʻ A ∈ n1c A := by
  rw [n1c_eq]; exact sm_iota_img A

/-- ✱104·201. \(\vdash :\beta \in \text{N}_{0}\text{c}ʻ\alpha .\supset .\iotaʻʻ\beta \in \text{N}^{1}\text{c}ʻ\alpha .\text{N}^{1}\text{c}ʻ\alpha =\text{N}^{1}\text{c}ʻ\beta\) -/
theorem pm104_201 {α : Type*} {A B : Set α} :
    B ∈ n₀c A → iota ʻʻ B ∈ n1c A ∧ n1c A = n1c B := by
  intro h
  have h' := mem_n₀c.1 h
  rw [n1c_eq, n1c_eq]
  exact ⟨sm_trans (sm_iota_img B) h', nc_eq_nc_of_sm (sm_symm h')⟩

/-- ✱104·21. \(\vdash .\exists !\text{N}^{1}\text{c}ʻ\alpha \quad[*104·2]\) -/
theorem pm104_21 {α : Type*} {A : Set α} : (n1c A).Nonempty := ⟨_, pm104_2⟩

/-- ✱104·211. \(\vdash .\exists !\text{N}^{1}\text{c}ʻ\alpha \cap \text{Cl}ʻ1 \quad[*104·2.*52·3]\)

`Cl'1` is `cl one`, `1` being in the type of the members of `ι''α`. -/
theorem pm104_211 {α : Type*} {A : Set α} : (n1c A ∩ cl one).Nonempty :=
  ⟨iota ʻʻ A, pm104_2, fun _ ⟨x, _, hX⟩ => ⟨x, hX⟩⟩

/-- ✱104·23. \(\vdash .\hat{\beta} \{(\exists y).y\in \alpha .\beta =\iota ʻx\cup \iota ʻy\}\in \text{N}^{1}\text{c}ʻ\alpha\) -/
theorem pm104_23 {α : Type*} {A : Set α} {x : α} :
    {B | ∃ y, y ∈ A ∧ B = ι x ∪ ι y} ∈ n1c A := by
  rw [n1c_eq]; exact pm100_61

/-- ✱104·231. \(\vdash :\text{N}^{1}\text{c}ʻ\alpha =\text{N}^{1}\text{c}ʻ\beta .\supset .\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta\) -/
theorem pm104_231 {α : Type*} {A B : Set α} : n1c A = n1c B → n₀c A = n₀c B := by
  intro h
  have h1 : iota ʻʻ B ∈ n1c A := by rw [h]; exact pm104_2
  rw [n1c_eq] at h1
  exact n₀c_eq_n₀c_iff.2 (sm_symm (sm_trans (sm_symm (sm_iota_img B)) h1))

/-- ✱104·232. \[\begin{aligned}&\vdash :\text{N}^{1}\text{c}ʻ\alpha =\text{N}^{1}\text{c}ʻ\beta .\equiv .\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta .\equiv .\beta \in \text{N}_{0}\text{c}ʻ\alpha\\ &[*104·231·201.*103·14]\end{aligned}\] -/
theorem pm104_232 {α : Type*} {A B : Set α} :
    (n1c A = n1c B ↔ n₀c A = n₀c B) ∧ (n₀c A = n₀c B ↔ B ∈ n₀c A) := by
  refine ⟨⟨pm104_231, fun h => ?_⟩, ⟨fun h => mem_n₀c.2 (sm_symm (n₀c_eq_n₀c_iff.1 h)),
    fun h => n₀c_eq_n₀c_iff.2 (sm_symm (mem_n₀c.1 h))⟩⟩
  rw [n1c_eq, n1c_eq]
  exact nc_eq_nc_of_sm (n₀c_eq_n₀c_iff.1 h)

/-- ✱104·24. \[\begin{aligned}&\vdash :\mu =\text{N}^{1}\text{c}ʻ\alpha .\supset .\mu =\text{N}_{0}\text{c}ʻ\iotaʻʻ\alpha =\text{N}_{0}\text{c}ʻ\hat{\beta} \{(\exists y).y\in \alpha .\beta =\iota ʻx\cup \iota ʻy\}\\ &[*104·2·23.*103·26]\end{aligned}\] -/
theorem pm104_24 {α : Type*} {A : Set α} {x : α} {μ : Set (Set (Set α))} :
    μ = n1c A → μ = n₀c (iota ʻʻ A) ∧ n₀c (iota ʻʻ A) = n₀c {B | ∃ y, y ∈ A ∧ B = ι x ∪ ι y} := by
  rintro rfl
  rw [n1c_eq, n₀c_eq_nc, n₀c_eq_nc]
  exact ⟨nc_eq_nc_of_sm (sm_symm (sm_iota_img A)),
    nc_eq_nc_of_sm (sm_trans (sm_iota_img A) (sm_symm pm100_61))⟩

/-- ✱104·25. \(\vdash .\text{N}^{1}\text{C}\subset \text{N}_{0}\text{C} \quad[*104·24·13]\)

The `N₀C` is in the type determined by `N¹C` (its members are cardinals of classes of classes). -/
theorem pm104_25 {α : Type*} : (N1C : Set (Set (Set (Set α)))) ⊆ N₀C := by
  rintro μ ⟨A, rfl⟩
  exact mem_N₀C.2 ⟨iota ʻʻ A, by
    rw [n1c_eq, n₀c_eq_nc]; exact nc_eq_nc_of_sm (sm_symm (sm_iota_img A))⟩

/-- ✱104·251. \(\vdash .\Lambda {\sim}\in \text{N}^{1}\text{C} \quad[*104·25.*103·23]\) -/
theorem pm104_251 {α : Type*} : (Λ : Set (Set (Set α))) ∉ N1C := fun h => pm103_23 (pm104_25 h)

/-- ✱104·252. \(\vdash .\text{N}^{1}\text{C}\in \text{Cls ex}^{2}\,\text{excl} \quad[*104·25.*103·24.*84·26]\) -/
theorem pm104_252 {α : Type*} : (N1C : Set (Set (Set (Set α)))) ∈ ClsEx2excl := by
  have hex : ∀ μ ν : Set (Set (Set α)), (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ μ ≠ ν → μ ∩ ν = Λ :=
    (pm103_24 (α := Set α)).1
  exact ⟨fun μ ν ⟨⟨hμ, hν⟩, hne⟩ => hex μ ν ⟨⟨pm104_25 hμ, pm104_25 hν⟩, hne⟩, pm104_251⟩

/-- ✱104·26. \(\vdash :\mu =\text{N}_{0}\text{c}ʻ\alpha .\supset .\mu ^{(1)}=\text{N}_{0}\text{c}ʻ\iotaʻʻ\alpha =\text{N}^{1}\text{c}ʻ\alpha\) -/
theorem pm104_26 {α : Type*} {A : Set α} {μ : Set (Set α)} :
    μ = n₀c A → up1 μ = n₀c (iota ʻʻ A) ∧ n₀c (iota ʻʻ A) = n1c A := by
  rintro rfl
  rw [up1_eq, sm_img_n₀c, n₀c_eq_nc, n1c_eq]
  exact ⟨nc_eq_nc_of_sm (sm_symm (sm_iota_img A)), nc_eq_nc_of_sm (sm_iota_img A)⟩

/-- ✱104·261. \(\vdash :\mu ^{(1)}=\text{N}^{1}\text{c}ʻ\alpha .\supset .\mu \subset \text{N}_{0}\text{c}ʻ\alpha\) -/
theorem pm104_261 {α : Type*} {A : Set α} {μ : Set (Set α)} : up1 μ = n1c A → μ ⊆ n₀c A := by
  intro h G hG
  rw [up1_eq] at h
  have h1 : iota ʻʻ G ∈ sm ʻʻ μ := ⟨G, hG, sm_iota_img G⟩
  rw [h, n1c_eq] at h1
  exact mem_n₀c.2 (sm_trans (sm_symm (sm_iota_img G)) h1)

/-- ✱104·262. \(\vdash :\mu \in \text{NC}.\mu ^{(1)}=\text{N}^{1}\text{c}ʻ\alpha .\supset .\mu =\text{N}_{0}\text{c}ʻ\alpha\) -/
theorem pm104_262 {α β : Type*} {A : Set α} {μ : Set (Set α)} :
    μ ∈ NC β ∧ up1 μ = n1c A → μ = n₀c A := by
  rintro ⟨hμ, h⟩
  have hsub := pm104_261 h
  rw [up1_eq] at h
  have h1 : iota ʻʻ A ∈ sm ʻʻ μ := by rw [h]; exact pm104_2
  obtain ⟨G, hG, -⟩ := h1
  exact ((pm103_26 hμ).1 hG).symm.trans (n₀c_eq_n₀c_iff.2 (mem_n₀c.1 (hsub hG)))

/-- ✱104·263. \(\vdash :\alpha \in \mu .\supset .\iotaʻʻ\alpha \in \mu ^{(1)}\) -/
theorem pm104_263 {α : Type*} {A : Set α} {μ : Set (Set α)} : A ∈ μ → iota ʻʻ A ∈ up1 μ := by
  rw [up1_eq]; exact fun h => ⟨A, h, sm_iota_img A⟩

/-- ✱104·264. \(\vdash :\exists !\mu .\equiv .\exists !\mu ^{(1)}\) -/
theorem pm104_264 {α : Type*} {μ : Set (Set α)} : μ.Nonempty ↔ (up1 μ).Nonempty := by
  rw [up1_eq]
  exact ⟨fun ⟨A, hA⟩ => ⟨_, A, hA, sm_iota_img A⟩, fun ⟨_, A, hA, _⟩ => ⟨A, hA⟩⟩

/-- ✱104·265. \(\vdash .\mu ^(1)=\text{ sm }_\muʻʻ\mu \quad[*102·85.(*104·03)]\)

`sm_μ` is `relT sm μ` (✱65·03). (The e-text prints `μ^(1)` without braces.) -/
theorem pm104_265 {α : Type*} {μ : Set (Set α)} : up1 μ = relT sm μ ʻʻ μ := by
  rw [up1_eq, relT_eq]

/-- ✱104·27. \(\vdash \colon\ldotp \mu \in \text{NC}.\supset :\mu =\text{N}_{0}\text{c}ʻ\alpha .\equiv .\mu ^{(1)}=\text{N}^{1}\text{c}ʻ\alpha \quad[*104·26·262]\) -/
theorem pm104_27 {α β : Type*} {A : Set α} {μ : Set (Set α)} :
    μ ∈ NC β → (μ = n₀c A ↔ up1 μ = n1c A) :=
  fun hμ => ⟨fun h => (pm104_26 h).1.trans (pm104_26 h).2, fun h => pm104_262 ⟨hμ, h⟩⟩

/-- ✱104·28. \(\vdash :\mu \in \text{NC}-\iota ʻ\Lambda .\supset .\mu ^{(1)}\in \text{N}^{1}\text{C} \quad[*104·26.*103·34]\) -/
theorem pm104_28 {α β : Type*} {μ : Set (Set α)} : μ ∈ NC β \ ι Λ → up1 μ ∈ N1C := by
  rintro ⟨hμ, hne⟩
  obtain ⟨G, hG⟩ := nonempty_of_not_mem_iota_null hne
  have h : μ = n₀c G := ((pm103_26 hμ).1 hG).symm
  exact ⟨G, (pm104_26 h).1.trans (pm104_26 h).2⟩

/-- ✱104·29. \(\vdash :\nu \in \text{N}^{1}\text{C}.\equiv .(\exists \mu )·\mu \in \text{N}_{0}\text{C}.\nu =\mu ^{(1)}\) -/
theorem pm104_29 {α : Type*} {ν : Set (Set (Set α))} :
    ν ∈ N1C ↔ ∃ μ, μ ∈ N₀C ∧ ν = up1 μ := by
  constructor
  · rintro ⟨A, rfl⟩
    have h := pm104_26 (A := A) rfl
    exact ⟨n₀c A, ⟨A, rfl⟩, (h.1.trans h.2).symm⟩
  · rintro ⟨μ, ⟨A, rfl⟩, rfl⟩
    have h := pm104_26 (A := A) rfl
    exact ⟨A, h.1.trans h.2⟩

/-- ✱104·3. \(\vdash .\iotaʻʻ\iotaʻʻ\alpha \in \text{N}^{2}\text{c}ʻ\alpha\) -/
theorem pm104_3 {α : Type*} {A : Set α} : iota ʻʻ (iota ʻʻ A) ∈ n2c A := by
  rw [n2c_eq]; exact sm_trans (sm_iota_img _) (sm_iota_img A)

/-- ✱104·31. \(\vdash .\exists !\text{N}^{2}\text{c}ʻ\alpha \quad[*104·3]\) -/
theorem pm104_31 {α : Type*} {A : Set α} : (n2c A).Nonempty := ⟨_, pm104_3⟩

/-- ✱104·311. \(\vdash .\text{N}^{2}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\iotaʻʻ\iotaʻʻ\alpha =\text{N}^{1}\text{c}ʻ\iotaʻʻ\alpha \quad[*104·3·2.*103·26]\) -/
theorem pm104_311 {α : Type*} {A : Set α} :
    n2c A = n₀c (iota ʻʻ (iota ʻʻ A)) ∧ n₀c (iota ʻʻ (iota ʻʻ A)) = n1c (iota ʻʻ A) := by
  rw [n2c_eq, n₀c_eq_nc, n1c_eq]
  exact ⟨nc_eq_nc_of_sm (sm_symm (sm_trans (sm_iota_img _) (sm_iota_img A))),
    nc_eq_nc_of_sm (sm_iota_img _)⟩

/-- ✱104·32. \(\vdash :\mu =\text{N}_{0}\text{c}ʻ\alpha .\supset .\mu ^{(2)}=\text{N}_{0}\text{c}ʻ\iotaʻʻ\iotaʻʻ\alpha =\text{N}^{1}\text{c}ʻ\iotaʻʻ\alpha =\text{N}^{2}\text{c}ʻ\alpha =\{\mu ^{(1)}\}^{(1)}\)

The chain of five is the conjunction of its four links, bracketed to the left. -/
theorem pm104_32 {α : Type*} {A : Set α} {μ : Set (Set α)} :
    μ = n₀c A →
      ((up2 μ = n₀c (iota ʻʻ (iota ʻʻ A)) ∧ n₀c (iota ʻʻ (iota ʻʻ A)) = n1c (iota ʻʻ A)) ∧
          n1c (iota ʻʻ A) = n2c A) ∧ n2c A = up1 (up1 μ) := by
  rintro rfl
  have h1 : sm (iota ʻʻ (iota ʻʻ A)) A := sm_trans (sm_iota_img _) (sm_iota_img A)
  have h2 : (sm ʻʻ nc (Set α) A : Set (Set (Set (Set α)))) = nc (Set (Set α)) A :=
    pm100_511 ⟨_, sm_iota_img A⟩
  have e1 : up2 (n₀c A) = nc (Set (Set α)) A := by rw [up2_eq, sm_img_n₀c]
  have e2 : up1 (up1 (n₀c A)) = nc (Set (Set α)) A := by
    rw [up1_eq, up1_eq, sm_img_n₀c, h2]
  rw [e1, e2, n₀c_eq_nc, n1c_eq, n2c_eq]
  exact ⟨⟨⟨nc_eq_nc_of_sm (sm_symm h1), nc_eq_nc_of_sm (sm_iota_img _)⟩,
    nc_eq_nc_of_sm (sm_iota_img A)⟩, rfl⟩

/-- ✱104·33. \(\vdash \colon\ldotp \mu \in \text{NC}.\supset :\mu =\text{N}_{0}\text{c}ʻ\alpha .\equiv .\mu ^{(2)}=\text{N}^{2}\text{c}ʻ\alpha\) -/
theorem pm104_33 {α β : Type*} {A : Set α} {μ : Set (Set α)} :
    μ ∈ NC β → (μ = n₀c A ↔ up2 μ = n2c A) := by
  intro hμ
  obtain ⟨B, rfl⟩ := mem_NC.1 hμ
  constructor
  · intro h
    exact (pm104_32 h).1.1.1.trans ((pm104_32 h).1.1.2.trans (pm104_32 h).1.2)
  · intro h
    rw [up2_eq, n2c_eq] at h
    have hA : iota ʻʻ (iota ʻʻ A) ∈ nc (Set (Set α)) A :=
      sm_trans (sm_iota_img _) (sm_iota_img A)
    rw [← h] at hA
    obtain ⟨G, hG, hsm⟩ := hA
    have hAG : sm A G := sm_trans (sm_symm (sm_trans (sm_iota_img _) (sm_iota_img A))) hsm
    rw [n₀c_eq_nc]
    exact nc_eq_nc_of_sm (sm_symm (sm_trans hAG hG))

/-- ✱104·34. \(\vdash :\varpi \in \text{N}^{2}\text{C}.\equiv .(\exists \nu ).\nu \in \text{N}^{1}\text{C}.\varpi =\nu ^{(1)}.\equiv .(\exists \mu ).\mu \in \text{N}_{0}\text{C}.\varpi =\mu ^{(2)}\)

`ϖ`, `ν`, `μ` are of the types forced by `N²C`, `N¹C`, `N₀C` and `ν^{(1)}`, `μ^{(2)}`. -/
theorem pm104_34 {α : Type*} {ϖ : Set (Set (Set (Set (Set α))))} :
    (ϖ ∈ N2C ↔ ∃ ν, ν ∈ N1C ∧ ϖ = up1 ν) ∧
      ((∃ ν, ν ∈ N1C ∧ ϖ = up1 ν) ↔ ∃ μ : Set (Set (Set α)), μ ∈ N₀C ∧ ϖ = up2 μ) := by
  have k1 : ∀ A : Set (Set α), up1 (n1c A) = n2c A := by
    intro A
    rw [up1_eq, n1c_eq, n2c_eq]
    exact pm100_511 ⟨_, sm_iota_img A⟩
  have k2 : ∀ A : Set (Set α), up2 (n₀c A) = n2c A := by
    intro A
    rw [up2_eq, sm_img_n₀c, n2c_eq]
  have e2 : (∃ ν, ν ∈ N1C ∧ ϖ = up1 ν) ↔ ∃ A, ϖ = n2c A := by
    constructor
    · rintro ⟨ν, ⟨A, rfl⟩, rfl⟩; exact ⟨A, k1 A⟩
    · rintro ⟨A, rfl⟩; exact ⟨n1c A, ⟨A, rfl⟩, (k1 A).symm⟩
  have e3 : (∃ μ : Set (Set (Set α)), μ ∈ N₀C ∧ ϖ = up2 μ) ↔ ∃ A, ϖ = n2c A := by
    constructor
    · rintro ⟨μ, ⟨B, rfl⟩, rfl⟩
      exact ⟨B, k2 B⟩
    · rintro ⟨A, rfl⟩
      exact ⟨n₀c A, ⟨A, rfl⟩, (k2 A).symm⟩
  exact ⟨e2.symm, e2.trans e3.symm⟩

/-- ✱104·35. \(\vdash .\text{N}^{2}\text{C}\subset \text{N}^{1}\text{C}.\text{N}^{2}\text{C}\subset \text{N}_{0}\text{C} \quad[*104·311·13·15]\) -/
theorem pm104_35 {α : Type*} :
    (N2C : Set (Set (Set (Set (Set α))))) ⊆ N1C ∧ (N2C : Set (Set (Set (Set (Set α))))) ⊆ N₀C := by
  constructor
  · rintro μ ⟨A, rfl⟩
    exact ⟨iota ʻʻ A, (pm104_311.1.trans pm104_311.2)⟩
  · rintro μ ⟨A, rfl⟩
    exact mem_N₀C.2 ⟨iota ʻʻ (iota ʻʻ A), pm104_311.1⟩

/-- ✱104·36. \(\vdash :\gamma \in \text{N}^{2}\text{c}ʻ\alpha .\gamma \in \text{N}^{1}\text{c}ʻ\beta .\supset .\beta \in \text{N}^{1}\text{c}ʻ\alpha .\text{N}^{1}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta\) -/
theorem pm104_36 {α : Type*} {A : Set α} {B : Set (Set α)} {G : Set (Set (Set α))} :
    G ∈ n2c A ∧ G ∈ n1c B → B ∈ n1c A ∧ n1c A = n₀c B := by
  simp only [n2c_eq, n1c_eq, n₀c_eq_nc]
  rintro ⟨h1, h2⟩
  have hBA : sm B A := sm_trans (sm_symm h2) h1
  exact ⟨hBA, nc_eq_nc_of_sm (sm_symm hBA)⟩

/-- ✱104·37. \(\vdash :\text{N}^{2}\text{c}ʻ\alpha =\text{N}^{1}\text{c}ʻ\beta .\equiv .\text{N}^{1}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta\) -/
theorem pm104_37 {α : Type*} {A : Set α} {B : Set (Set α)} : n2c A = n1c B ↔ n1c A = n₀c B := by
  constructor
  · intro h
    have hG : iota ʻʻ (iota ʻʻ A) ∈ n2c A := pm104_3
    have hG' : iota ʻʻ (iota ʻʻ A) ∈ n1c B := h ▸ hG
    exact (pm104_36 ⟨hG, hG'⟩).2
  · intro h
    exact (pm104_123 h.symm).symm

/-- ✱104·4. \[\begin{aligned}\vdash \colon\ldotp x\in \alpha .x\neq y.x\neq z.y\neq z:&(w).w_{\iota }=\hat{\alpha}\hat{u}(\alpha =\iota ʻw\cup \iota ʻu):\supset .\\ &x_{\iota }ʻʻ(\alpha -\iota ʻx)\cup \iota ʻy_{\iota }ʻz\in \text{N}^{1}\text{c}ʻ\alpha \cap \text{Cl}ʻ2\end{aligned}\]

The hypothesis `(w) . w_ι = α̂û(α = ι'w ∪ ι'u)` introduces a relation `w_ι` for each `w`: a real
variable `W : α → Set α → α → Prop`. `x_ι''(α − ι'x)` is `W x ʻʻ (A \ ι x)`, and `ι'y_ι'z` is
`ι'(y_ι'z)`, whose description `y_ι'z` has the conclusion as its scope. `Cl'2` is `cl two`. -/
theorem pm104_4 {α : Type*} {A : Set α} {x y z : α} {W : α → Set α → α → Prop} :
    ((((x ∈ A ∧ x ≠ y) ∧ x ≠ z) ∧ y ≠ z) ∧ ∀ w, W w = fun B u => B = ι w ∪ ι u) →
      Desc (W y) z (fun B => W x ʻʻ (A \ ι x) ∪ ι B ∈ n1c A ∩ cl two) := by
  classical
  rintro ⟨⟨⟨⟨hxA, hxy⟩, hxz⟩, hyz⟩, hW⟩
  have hWg : ∀ w, W w = graph (fun u => ι w ∪ ι u) := hW
  rw [hWg y, desc_graph, hWg x]
  show graph (fun u => ι x ∪ ι u) ʻʻ (A \ ι x) ∪ ι (ι y ∪ ι z) ∈ n1c A ∩ cl two
  let g : α → Set α := fun u => if u = x then ι y ∪ ι z else ι x ∪ ι u
  have hg1 : ∀ u, u = x → g u = ι y ∪ ι z := fun u h => ite_eq_left h
  have hg2 : ∀ u, u ≠ x → g u = ι x ∪ ι u := fun u h => ite_eq_right h
  have hset : graph (fun u => ι x ∪ ι u) ʻʻ (A \ ι x) ∪ ι (ι y ∪ ι z) = g '' A := by
    ext S
    constructor
    · rintro (⟨u, ⟨huA, hux⟩, rfl⟩ | hS)
      · exact ⟨u, huA, hg2 u hux⟩
      · exact ⟨x, hxA, by rw [mem_unitCls.1 hS]; exact hg1 x rfl⟩
    · rintro ⟨u, huA, rfl⟩
      by_cases hux : u = x
      · right
        exact mem_unitCls.2 (hg1 u hux)
      · left
        exact ⟨u, ⟨huA, hux⟩, hg2 u hux⟩
  have hx_notin : x ∉ ι y ∪ ι z := by
    rintro (h | h)
    · exact hxy (mem_unitCls.1 h)
    · exact hxz (mem_unitCls.1 h)
  have hinj : Set.InjOn g A := by
    intro u _ v _ huv
    by_cases hux : u = x
    · by_cases hvx : v = x
      · exact hux.trans hvx.symm
      · exfalso
        rw [hg1 u hux, hg2 v hvx] at huv
        exact hx_notin (by rw [huv]; exact Or.inl rfl)
    · by_cases hvx : v = x
      · exfalso
        rw [hg2 u hux, hg1 v hvx] at huv
        exact hx_notin (by rw [← huv]; exact Or.inl rfl)
      · rw [hg2 u hux, hg2 v hvx] at huv
        exact pair_right_inj huv
  rw [hset]
  refine ⟨?_, ?_⟩
  · rw [n1c_eq]
    exact sm_iff_nonempty_equiv.2 ⟨(Equiv.Set.imageOfInjOn g A hinj).symm⟩
  · rintro S ⟨u, _, rfl⟩
    by_cases hux : u = x
    · show g u ∈ two
      rw [hg1 u hux]
      exact ⟨y, z, hyz, rfl⟩
    · show g u ∈ two
      rw [hg2 u hux]
      exact ⟨x, u, fun h => hux h.symm, rfl⟩

/-- ✱104·41. \[\begin{aligned}\vdash \colon\ldotp tʻ\alpha =tʻ\beta :(\exists x,y,z).x\in \alpha .&x\neq y.x\neq z.y\neq z:\supset .\\ &(\exists \gamma ,\delta ).\gamma \in \text{N}^{1}\text{c}ʻ\alpha .\delta \in \text{N}^{1}\text{c}ʻ\beta .\gamma \cap \delta =\Lambda\end{aligned}\]

`t'α = t'β` (true when significant) makes `α` and `β` of one type. -/
theorem pm104_41 {α : Type*} {A B : Set α} :
    typ A = typ B ∧ (∃ x y z, ((x ∈ A ∧ x ≠ y) ∧ x ≠ z) ∧ y ≠ z) →
      ∃ G E, (G ∈ n1c A ∧ E ∈ n1c B) ∧ G ∩ E = Λ := by
  rintro ⟨-, x, y, z, h⟩
  have h4 := pm104_4 (A := A) (W := fun w => graph (fun u => ι w ∪ ι u)) ⟨h, fun w => rfl⟩
  rw [desc_graph] at h4
  refine ⟨_, iota ʻʻ B, ⟨h4.1, pm104_2⟩, ?_⟩
  rw [Null_eq_empty]
  refine Set.eq_empty_iff_forall_notMem.2 fun S ⟨hS2, ⟨b, _, hS1⟩⟩ => ?_
  have h2 : S ∈ (two : Set (Set α)) := h4.2 hS2
  have h1 : S ∈ (one : Set (Set α)) := ⟨b, hS1⟩
  have h21 : S ∈ (two ∩ one : Set (Set α)) := ⟨h2, h1⟩
  rw [(pm101_35 (α := α) (β := α)).2, Null_eq_empty] at h21
  exact h21

/-- ✱104·411. \(\vdash :tʻ\alpha =tʻ\beta .\alpha \in 0.\gamma =\Lambda _{\alpha }.\delta =\iotaʻʻ\beta .\supset .\gamma \in \text{N}^{1}\text{c}ʻ\alpha .\delta \in \text{N}^{1}\text{c}ʻ\beta .\gamma \cap \delta =\Lambda\)

`Λ_α` is `clsT Λ A` (✱65·01). -/
theorem pm104_411 {α : Type*} {A B : Set α} {G E : Set (Set α)} :
    ((typ A = typ B ∧ A ∈ zero) ∧ G = clsT Λ A) ∧ E = iota ʻʻ B →
      (G ∈ n1c A ∧ E ∈ n1c B) ∧ G ∩ E = Λ := by
  rintro ⟨⟨⟨-, hA⟩, rfl⟩, rfl⟩
  have hA' : A = Λ := hA
  rw [clsT_eq, Null_eq_empty, Set.empty_inter]
  refine ⟨⟨?_, pm104_2⟩, rfl⟩
  rw [n1c_eq, hA', Null_eq_empty]
  exact sm_empty_iff.2 rfl

/-- ✱104·412. \[\begin{aligned}\vdash :tʻ\alpha =tʻ\beta .\alpha =\iota ʻx.\gamma =\iota ʻ\Lambda _{x}.&\delta =\iotaʻʻ\beta .\supset .\\ &\gamma \in \text{N}^{1}\text{c}ʻ\alpha .\delta \in \text{N}^{1}\text{c}ʻ\beta .\gamma \cap \delta =\Lambda\end{aligned}\]

`Λ_x` is `clsT Λ x` (✱65·01). -/
theorem pm104_412 {α : Type*} {A B : Set α} {x : α} {G E : Set (Set α)} :
    (((typ A = typ B ∧ A = ι x) ∧ G = ι (clsT Λ x)) ∧ E = iota ʻʻ B) →
      (G ∈ n1c A ∧ E ∈ n1c B) ∧ G ∩ E = Λ := by
  rintro ⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩
  rw [clsT_eq]
  refine ⟨⟨?_, pm104_2⟩, ?_⟩
  · rw [n1c_eq]
    exact sm_unit_iff.2 ⟨Λ, rfl⟩
  · rw [show (Λ : Set (Set α)) = ∅ from Null_eq_empty]
    refine Set.eq_empty_iff_forall_notMem.2 fun S hS' => ?_
    obtain ⟨hS, b, _, hb⟩ := hS'
    have h1 : S = Λ := hS
    have h2 : b ∈ S := by rw [show S = ι b from hb]; exact mem_unitCls.2 rfl
    rw [h1, Null_eq_empty] at h2
    exact h2

/-- ✱104·413. \[\begin{aligned}\vdash :tʻ\alpha =tʻ\beta .\alpha =\iota ʻx\cup \iota ʻy.&x \neq y.\gamma =\iota ʻ\Lambda \cup \iota ʻ(\iota ʻx\cup \iota ʻy).\delta =\iotaʻʻ\beta .\supset .\\ &\gamma \in \text{N}^{1}\text{c}ʻ\alpha .\delta \in \text{N}^{1}\text{c}ʻ\beta .\gamma \cap \delta =\Lambda\end{aligned}\] -/
theorem pm104_413 {α : Type*} {A B : Set α} {x y : α} {G E : Set (Set α)} :
    ((((typ A = typ B ∧ A = ι x ∪ ι y) ∧ x ≠ y) ∧ G = ι Λ ∪ ι (ι x ∪ ι y)) ∧
        E = iota ʻʻ B) →
      (G ∈ n1c A ∧ E ∈ n1c B) ∧ G ∩ E = Λ := by
  rintro ⟨⟨⟨⟨-, rfl⟩, hxy⟩, rfl⟩, rfl⟩
  have hne : (Λ : Set α) ≠ ι x ∪ ι y := by
    rw [Null_eq_empty]; exact (unit_union_ne_empty x y).symm
  refine ⟨⟨?_, pm104_2⟩, ?_⟩
  · rw [n1c_eq]
    exact (sm_pair_iff hxy).2 ⟨Λ, ι x ∪ ι y, hne, rfl⟩
  · rw [show (Λ : Set (Set α)) = ∅ from Null_eq_empty]
    refine Set.eq_empty_iff_forall_notMem.2 fun S hS' => ?_
    obtain ⟨hS, b, _, hb⟩ := hS'
    have hb' : S = ι b := hb
    rcases hS with hS | hS
    · have h1 : S = Λ := hS
      have h2 : b ∈ S := by rw [hb']; exact mem_unitCls.2 rfl
      rw [h1, Null_eq_empty] at h2
      exact h2
    · have h1 : S = ι x ∪ ι y := hS
      have hx : x ∈ ι b := by rw [← hb', h1]; exact Or.inl rfl
      have hy : y ∈ ι b := by rw [← hb', h1]; exact Or.inr rfl
      exact hxy ((mem_unitCls.1 hx).trans (mem_unitCls.1 hy).symm)

/-- ✱104·42. \[\begin{aligned}&\vdash :tʻ\alpha =tʻ\beta .\alpha \in 0\cup 1\cup 2.\supset .(\exists \gamma ,\delta ).\gamma \in \text{N}^{1}\text{c}ʻ\alpha .\delta \in \text{N}^{1}\text{c}ʻ\beta .\gamma \cap \delta =\Lambda \\ &[*104·411·412·413.*52·1.*54·101]\end{aligned}\] -/
theorem pm104_42 {α : Type*} {A B : Set α} :
    typ A = typ B ∧ A ∈ zero ∪ one ∪ two → ∃ G E, (G ∈ n1c A ∧ E ∈ n1c B) ∧ G ∩ E = Λ := by
  rintro ⟨hAB, (h0 | ⟨x, rfl⟩) | ⟨x, y, hxy, rfl⟩⟩
  · exact ⟨_, _, pm104_411 ⟨⟨⟨hAB, h0⟩, rfl⟩, rfl⟩⟩
  · exact ⟨_, _, pm104_412 ⟨⟨⟨hAB, rfl⟩, rfl⟩, rfl⟩⟩
  · exact ⟨_, _, pm104_413 ⟨⟨⟨⟨hAB, rfl⟩, hxy⟩, rfl⟩, rfl⟩⟩

/-- ✱104·43. \(\vdash :tʻ\alpha =tʻ\beta .\supset .(\exists \gamma ,\delta ).\gamma \in \text{N}^{1}\text{c}ʻ\alpha .\delta \in \text{N}^{1}\text{c}ʻ\beta .\gamma \cap \delta =\Lambda \) -/
theorem pm104_43 {α : Type*} {A B : Set α} :
    typ A = typ B → ∃ G E, (G ∈ n1c A ∧ E ∈ n1c B) ∧ G ∩ E = Λ := by
  intro hAB
  by_cases h : A ∈ zero ∪ one ∪ two
  · exact pm104_42 ⟨hAB, h⟩
  · refine pm104_41 ⟨hAB, ?_⟩
    have h0 : A.Nonempty := by
      by_contra h'
      exact h (Or.inl (Or.inl (show A = Λ by
        rw [Null_eq_empty]; exact Set.not_nonempty_iff_eq_empty.1 h')))
    obtain ⟨x, hx⟩ := h0
    have h1 : ∃ y, y ∈ A ∧ y ≠ x := by
      by_contra h'
      push Not at h'
      exact h (Or.inl (Or.inr ⟨x, Set.ext fun z =>
        ⟨fun hz => h' z hz, fun hz => by rw [mem_unitCls.1 hz]; exact hx⟩⟩))
    obtain ⟨y, hy, hyx⟩ := h1
    have h2 : ∃ z, z ∈ A ∧ z ≠ x ∧ z ≠ y := by
      by_contra h'
      push Not at h'
      exact h (Or.inr ⟨x, y, hyx.symm, Set.ext fun z => ⟨fun hz => by
        by_cases hzx : z = x
        · exact Or.inl hzx
        · exact Or.inr (h' z hz hzx), fun hz => by
        rcases hz with hz | hz
        · rw [mem_unitCls.1 hz]; exact hx
        · rw [mem_unitCls.1 hz]; exact hy⟩⟩)
    obtain ⟨z, hz, hzx, hzy⟩ := h2
    exact ⟨x, y, z, ⟨⟨hx, hyx.symm⟩, fun h => hzx h.symm⟩, fun h => hzy h.symm⟩

/-- ✱104·44. \[\begin{aligned}&\vdash :\mu ,\nu \in \text{N}^{1}\text{C}.tʻ\mu =tʻ\nu .\supset .(\exists \gamma ,\delta ).\gamma \in \mu .\delta \in \nu .\gamma \cap \delta =\Lambda\\ &[*104·13·43]\end{aligned}\] -/
theorem pm104_44 {α : Type*} {μ ν : Set (Set (Set α))} :
    (μ ∈ N1C ∧ ν ∈ N1C) ∧ typ μ = typ ν → ∃ G E, (G ∈ μ ∧ E ∈ ν) ∧ G ∩ E = Λ := by
  rintro ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, -⟩
  exact pm104_43 (A := A) (B := B) (typ_eq_typ _ _)

/-- ✱104·45. \[\begin{aligned}&\vdash :\mu ,\nu \in \text{N}_{0}\text{C}.tʻ\mu =tʻ\nu .\supset .(\exists \gamma ,\delta ).\gamma \in \mu ^{(1)}.\delta \in \nu ^{(1)}.\gamma \cap \delta =\Lambda\\ &[*104·29·44]\end{aligned}\] -/
theorem pm104_45 {α : Type*} {μ ν : Set (Set α)} :
    (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ typ μ = typ ν → ∃ G E, (G ∈ up1 μ ∧ E ∈ up1 ν) ∧ G ∩ E = Λ := by
  rintro ⟨⟨hμ, hν⟩, -⟩
  exact pm104_44 ⟨⟨pm104_29.2 ⟨μ, hμ, rfl⟩, pm104_29.2 ⟨ν, hν, rfl⟩⟩, typ_eq_typ _ _⟩

/-- ✱104·46. \[\begin{aligned}&\vdash :\mu ,\nu \in \text{NC} - \iota ʻ\Lambda .tʻ\mu =tʻ\nu .\supset .(\exists \gamma ,\delta ).\gamma \in \mu ^{(1)}.\delta \in \nu ^{(1)}.\gamma \cap \delta =\Lambda \\ &[*104·28·44]\end{aligned}\]

The two `NC`s have independent converse-domain types. -/
theorem pm104_46 {α β β' : Type*} {μ ν : Set (Set α)} :
    (μ ∈ NC β \ ι Λ ∧ ν ∈ NC β' \ ι Λ) ∧ typ μ = typ ν →
      ∃ G E, (G ∈ up1 μ ∧ E ∈ up1 ν) ∧ G ∩ E = Λ := by
  rintro ⟨⟨hμ, hν⟩, -⟩
  exact pm104_44 ⟨⟨pm104_28 hμ, pm104_28 hν⟩, typ_eq_typ _ _⟩

/-!
## [✱105] Descending cardinals

*(Vol. 2, p. 52)*

> *Summary of* *105.
>
> In this number, we consider cardinals generated by a relation of similarity which goes from a higher to a lower type, *i.e.* given any class of classes \(\kappa\), we consider \(\text{Nc}ʻ\kappa\) in the type of members of \(\kappa\) (which we shall call \(\text{N}_{1}\text{c}ʻ\kappa\)) or in some lower type. Thus *e.g.* we shall have \[ \kappa =\iotaʻʻ\alpha .\supset .\alpha \in \text{N}_{1}\text{c}ʻ\kappa , \] where "\(\text{N}_{1}\text{c}ʻ\kappa\)" means "classes similar to \(\kappa\) but of the next lower type." Similarly \[ \kappa =\iotaʻʻ\iotaʻʻ\alpha .\supset .\alpha \in \text{N}_{2}\text{c}ʻ\kappa , \] and so on. We shall have generally \[ \begin{aligned} \beta \in \text{N}_{1}\text{c}ʻ\alpha .&\equiv \alpha \in \text{N}^{1}\text{c}ʻ\beta ,\\ \beta \in \text{N}_{2}\text{c}ʻ\alpha .&\equiv \alpha \in \text{N}^{2}\text{c}ʻ\beta , \end{aligned} \] and so on. The chief difference between ascending and descending cardinals is that \(\Lambda\) is one of the latter, but not one of the former. Otherwise the propositions of the present number are mostly analogous to corresponding propositions of *104.
>
> …

**Lean reading.** `N₁c'α`, `N₂c'α`, `N₁C`, `N₂C`, `μ_{(1)}`, `μ_{(2)}` are `n₁c A`, `n₂c A`,
`N₁C`, `N₂C`, `down1 μ`, `down2 μ` (Defs/Part3); their arguments are classes of classes (of
classes), so the types of `α`, `β`, `γ`, `μ` in each proposition are fixed by the definitions,
and the relative types `t₀'α`, `t₁'α`, `t₂'α`, `t'α`, `t²'α` are `typ₀ A`, `typ₁ A`, `typ₂ A`,
`typ A`, `typ2 A`. `Nc(t₁'α)` etc. are as in ✱102. `μ, ν ∈ NC` has independent converse-domain
types; ✱105·356·357 use the converse domain of the cardinal `μ_{(1)}` in the type of the members of
`μ` (by ✱100·52).

**Status.** proved (all propositions; ✱105·01·011·02·021·03·031 definition; ✱105·14 proved
(reading): transcription error `a` for `α`)
-/

/-- ✱105·01 (Df). \(\text{N}_{1}\text{c}ʻ\alpha =\text{Nc}ʻ\alpha \cap tʻt_{1}ʻ\alpha \quad\text{Df}\) -/
theorem pm105_01 {α : Type*} {A : Set (Set α)} : n₁c A = nc α A ∩ typ (typ₁ A) := rfl

/-- ✱105·011 (Df). \(\text{N}_{2}\text{c}ʻ\alpha =\text{Nc}ʻ\alpha \cap tʻt_{2}ʻ\alpha \quad\text{Df}\) -/
theorem pm105_011 {α : Type*} {A : Set (Set (Set α))} : n₂c A = nc α A ∩ typ (typ₂ A) := rfl

/-- ✱105·02 (Df). \(\text{N}_{1}\text{C}=\text{D}ʻ\text{N}_{1}\text{c} \quad\text{Df}\) -/
theorem pm105_02 {α : Type*} : Desc D N₁c (fun K => (N₁C : Set (Set (Set α))) = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱105·021 (Df). \(\text{N}_{2}\text{C}=\text{D}ʻ\text{N}_{2}\text{c} \quad\text{Df}\) -/
theorem pm105_021 {α : Type*} : Desc D N₂c (fun K => (N₂C : Set (Set (Set α))) = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱105·03 (Df). \(\mu _{(1)}=\text{ sm }ʻʻ\mu \cap t_{1}ʻ\mu \quad\text{Df}\) -/
theorem pm105_03 {α : Type*} {μ : Set (Set (Set α))} : down1 μ = sm ʻʻ μ ∩ typ₁ μ := rfl

/-- ✱105·031 (Df). \(\mu _{(2)}=\text{ sm }ʻʻ\mu \cap t_{2}ʻ\mu \quad\text{Df}\) -/
theorem pm105_031 {α : Type*} {μ : Set (Set (Set (Set α)))} : down2 μ = sm ʻʻ μ ∩ typ₂ μ := rfl

/-- ✱105·1. \(\vdash .\text{N}_{1}\text{c}ʻ\alpha =\text{Nc}ʻ\alpha \cap t_{0}ʻ\alpha \quad[*63·383.(*105·01)]\) -/
theorem pm105_1 {α : Type*} {A : Set (Set α)} : n₁c A = nc α A ∩ typ₀ A := by
  rw [n₁c_eq, typ₀_eq_univ, Set.inter_univ]

/-- ✱105·101. \(\vdash .\text{N}_{2}\text{c}ʻ\alpha =\text{Nc}ʻ\alpha \cap t_{1}ʻ\alpha \quad[*63·41.(*105·011)]\) -/
theorem pm105_101 {α : Type*} {A : Set (Set (Set α))} : n₂c A = nc α A ∩ typ₁ A := by
  rw [n₂c_eq, typ₁, typ₀_eq_univ, Set.inter_univ]

/-- ✱105·11. \[\begin{aligned}&\vdash :\beta \in \text{N}_{1}\text{c}ʻ\alpha .\equiv .\beta \in \text{Nc}ʻ\alpha .\beta \in t_{0}ʻ\alpha .\equiv .\beta \text{ sm }\alpha .\beta \in t_{0}ʻ\alpha .\equiv .\beta \text{ sm }\alpha .\beta \subset t_{1}ʻ\alpha \\ &[*105·1.*100·31.*63·51]\end{aligned}\] -/
theorem pm105_11 {α : Type*} {A : Set (Set α)} {B : Set α} :
    ((B ∈ n₁c A ↔ B ∈ nc α A ∧ B ∈ typ₀ A) ∧
        (B ∈ nc α A ∧ B ∈ typ₀ A ↔ sm B A ∧ B ∈ typ₀ A)) ∧
      (sm B A ∧ B ∈ typ₀ A ↔ sm B A ∧ B ⊆ typ₁ A) := by
  rw [n₁c_eq]
  exact ⟨⟨⟨fun h => ⟨h, mem_typ₀ _ _⟩, fun h => h.1⟩, Iff.rfl⟩,
    ⟨fun h => ⟨h.1, sub_typ₁ _ _⟩, fun h => ⟨h.1, mem_typ₀ _ _⟩⟩⟩

/-- ✱105·111. \[\begin{aligned}&\vdash :\beta \in \text{N}_{2}\text{c}ʻ\alpha .\equiv .\beta \in \text{Nc}ʻ\alpha .\beta \in t_{1}ʻ\alpha .\equiv .\beta \text{ sm }\alpha .\beta \in t_{1}ʻ\alpha .\equiv .\beta \text{ sm }\alpha .\beta \subset t_{2}ʻ\alpha\\ &[*105·101.*100·31.*63·52]\end{aligned}\] -/
theorem pm105_111 {α : Type*} {A : Set (Set (Set α))} {B : Set α} :
    ((B ∈ n₂c A ↔ B ∈ nc α A ∧ B ∈ typ₁ A) ∧
        (B ∈ nc α A ∧ B ∈ typ₁ A ↔ sm B A ∧ B ∈ typ₁ A)) ∧
      (sm B A ∧ B ∈ typ₁ A ↔ sm B A ∧ B ⊆ typ₂ A) := by
  rw [n₂c_eq]
  exact ⟨⟨⟨fun h => ⟨h, mem_typ₁ _ _⟩, fun h => h.1⟩, Iff.rfl⟩,
    ⟨fun h => ⟨h.1, sub_typ₂ _ _⟩, fun h => ⟨h.1, mem_typ₁ _ _⟩⟩⟩

/-- ✱105·12. \[\begin{aligned}&\vdash :\beta \in \text{N}_{1}\text{c}ʻ\alpha .\equiv .\beta \in \text{Nc}ʻ\alpha .\alpha \subset tʻ\beta .\equiv .\beta \text{ sm }\alpha .\alpha \subset tʻ\beta .\equiv .\alpha \in \text{N}^{1}\text{c}ʻ\beta \\ &[*105·11.*63·51.*104·1]\end{aligned}\] -/
theorem pm105_12 {α : Type*} {A : Set (Set α)} {B : Set α} :
    ((B ∈ n₁c A ↔ B ∈ nc α A ∧ A ⊆ typ B) ∧ (B ∈ nc α A ∧ A ⊆ typ B ↔ sm B A ∧ A ⊆ typ B)) ∧
      (sm B A ∧ A ⊆ typ B ↔ A ∈ n1c B) := by
  rw [n₁c_eq, n1c_eq]
  exact ⟨⟨⟨fun h => ⟨h, sub_typ _ _⟩, fun h => h.1⟩, Iff.rfl⟩,
    ⟨fun h => sm_symm h.1, fun h => ⟨sm_symm h, sub_typ _ _⟩⟩⟩

/-- ✱105·121. \[\begin{aligned}&\vdash :\beta \in \text{N}_{2}\text{c}ʻ\alpha .\equiv .\beta \in \text{Nc}ʻ\alpha .\alpha \subset t^{2}ʻ\beta .\equiv .\beta \text{ sm }\alpha .\alpha \subset t^{2}ʻ\beta .\equiv .\alpha \in \text{N}^{2}\text{c}ʻ\beta \\ &[*105·111.*63·52.*104·11]\end{aligned}\] -/
theorem pm105_121 {α : Type*} {A : Set (Set (Set α))} {B : Set α} :
    ((B ∈ n₂c A ↔ B ∈ nc α A ∧ A ⊆ typ2 B) ∧ (B ∈ nc α A ∧ A ⊆ typ2 B ↔ sm B A ∧ A ⊆ typ2 B)) ∧
      (sm B A ∧ A ⊆ typ2 B ↔ A ∈ n2c B) := by
  rw [n₂c_eq, n2c_eq]
  exact ⟨⟨⟨fun h => ⟨h, sub_typ2 _ _⟩, fun h => h.1⟩, Iff.rfl⟩,
    ⟨fun h => sm_symm h.1, fun h => ⟨sm_symm h, sub_typ2 _ _⟩⟩⟩

/-- ✱105·13. \(\vdash .\text{N}_{1}\text{c}ʻ\alpha =\text{Nc}(t_{1}ʻ\alpha )ʻ\alpha =\text{Nc}\{(t_{1}ʻ\alpha )_{\alpha }\}ʻ\alpha \quad[*102·6.(*105·.01)]\)

`Nc(t₁'α)` is `relT2 Nc (typ₁ A)`, `Nc{(t₁'α)_α}` is `relT2T Nc (typ₁ A) A`. -/
theorem pm105_13 {α : Type*} {A : Set (Set α)} :
    Desc (relT2 Nc (typ₁ A)) A (fun μ => n₁c A = μ) ∧
      Desc (relT2 Nc (typ₁ A)) A (fun μ => Desc (relT2T Nc (typ₁ A) A) A (fun ν => μ = ν)) :=
  ⟨(desc_relT2_Nc' _ _ _).2 (n₁c_eq A), (desc_relT2_Nc' _ _ _).2 ((desc_relT2T_Nc _ _ _ _).2 rfl)⟩

/-- ✱105·131. \(\vdash .\text{N}_{2}\text{c}ʻ\alpha =\text{Nc}(t_{2}ʻ\alpha )ʻ\alpha =\text{Nc}\{(t_{2}ʻ\alpha )_{\alpha }\}ʻ\alpha \quad[*102·6.(*105·011)]\) -/
theorem pm105_131 {α : Type*} {A : Set (Set (Set α))} :
    Desc (relT2 Nc (typ₂ A)) A (fun μ => n₂c A = μ) ∧
      Desc (relT2 Nc (typ₂ A)) A (fun μ => Desc (relT2T Nc (typ₂ A) A) A (fun ν => μ = ν)) :=
  ⟨(desc_relT2_Nc' _ _ _).2 (n₂c_eq A), (desc_relT2_Nc' _ _ _).2 ((desc_relT2T_Nc _ _ _ _).2 rfl)⟩

/-- ✱105·14. \(\vdash :\alpha \in t_{0}ʻ\beta .\supset .\text{N}_{1}\text{c}ʻ\beta =\text{Nc}(a)ʻ\beta =\text{Nc}(a_{\beta })ʻ\beta\)

**Status.** proved (reading): transcription error: the e-text prints `a` for `α` in
`Nc(α)'β = Nc(α_β)'β`. -/
theorem pm105_14 {α : Type*} {A : Set α} {B : Set (Set α)} :
    A ∈ typ₀ B →
      Desc (relT2 Nc A) B (fun μ => n₁c B = μ) ∧
        Desc (relT2 Nc A) B (fun μ => Desc (relT2T Nc A B) B (fun ν => μ = ν)) :=
  fun _ => ⟨(desc_relT2_Nc' _ _ _).2 (n₁c_eq B),
    (desc_relT2_Nc' _ _ _).2 ((desc_relT2T_Nc _ _ _ _).2 rfl)⟩

/-- ✱105·141. \(\vdash :\alpha \in t_{1}ʻ\beta .\supset .\text{N}_{2}\text{c}ʻ\beta =\text{Nc}(\alpha )ʻ\beta =\text{Nc}(\alpha _{\beta })ʻ\beta \quad[\text{Proof as in}\, *105·14]\) -/
theorem pm105_141 {α : Type*} {A : Set α} {B : Set (Set (Set α))} :
    A ∈ typ₁ B →
      Desc (relT2 Nc A) B (fun μ => n₂c B = μ) ∧
        Desc (relT2 Nc A) B (fun μ => Desc (relT2T Nc A B) B (fun ν => μ = ν)) :=
  fun _ => ⟨(desc_relT2_Nc' _ _ _).2 (n₂c_eq B),
    (desc_relT2_Nc' _ _ _).2 ((desc_relT2T_Nc _ _ _ _).2 rfl)⟩

/-- ✱105·142. \(\vdash :\beta \subset tʻ\alpha .\supset .\text{N}_{1}\text{c}ʻ\beta =\text{Nc}(\alpha )ʻ\beta =\text{Nc}(\alpha _{\beta })ʻ\beta \quad[*105·14.*63·51]\) -/
theorem pm105_142 {α : Type*} {A : Set α} {B : Set (Set α)} :
    B ⊆ typ A →
      Desc (relT2 Nc A) B (fun μ => n₁c B = μ) ∧
        Desc (relT2 Nc A) B (fun μ => Desc (relT2T Nc A B) B (fun ν => μ = ν)) :=
  fun _ => ⟨(desc_relT2_Nc' _ _ _).2 (n₁c_eq B),
    (desc_relT2_Nc' _ _ _).2 ((desc_relT2T_Nc _ _ _ _).2 rfl)⟩

/-- ✱105·143. \(\vdash :\beta \subset t^{2}ʻ\alpha .\supset .\text{N}_{2}\text{c}ʻ\beta =\text{Nc}(\alpha )ʻ\beta =\text{Nc}(\alpha _{\beta })ʻ\beta \quad[*105·141.*63·52]\) -/
theorem pm105_143 {α : Type*} {A : Set α} {B : Set (Set (Set α))} :
    B ⊆ typ2 A →
      Desc (relT2 Nc A) B (fun μ => n₂c B = μ) ∧
        Desc (relT2 Nc A) B (fun μ => Desc (relT2T Nc A B) B (fun ν => μ = ν)) :=
  fun _ => ⟨(desc_relT2_Nc' _ _ _).2 (n₂c_eq B),
    (desc_relT2_Nc' _ _ _).2 ((desc_relT2T_Nc _ _ _ _).2 rfl)⟩

/-- ✱105·15. \(\vdash :\mu \in \text{N}_{1}\text{C}.\equiv .(\exists \alpha ).\mu =\text{N}_{1}\text{c}ʻ\alpha \quad[*100·22.*71·41.(*105·02)]\) -/
theorem pm105_15 {α : Type*} {μ : Set (Set α)} : μ ∈ N₁C ↔ ∃ A, μ = n₁c A := Iff.rfl

/-- ✱105·151. \(\vdash :\mu \in \text{N}_{2}\text{C}.\equiv .(\exists \alpha ).\mu =\text{N}_{2}\text{c}ʻ\alpha\) -/
theorem pm105_151 {α : Type*} {μ : Set (Set α)} : μ ∈ N₂C ↔ ∃ A, μ = n₂c A := Iff.rfl

/-- ✱105·16. \[\begin{aligned}\vdash :\delta \in \mu _{(1)}.&\equiv .(\exists \gamma ).\gamma \in \mu .\delta \text{ sm }\gamma .\delta \in t_{1}ʻ\mu .\\ &\equiv .(\exists \gamma ).\gamma \in \mu .\delta \text{ sm }\gamma .\delta \in t_{0}ʻ\gamma .\\ &\equiv .(\exists \gamma ).\gamma \in \mu .\delta \text{ sm }\gamma .\gamma \subset tʻ\delta \quad[*37·1.*63·51·54]\end{aligned}\] -/
theorem pm105_16 {α : Type*} {μ : Set (Set (Set α))} {E : Set α} :
    ((E ∈ down1 μ ↔ ∃ G, (G ∈ μ ∧ sm E G) ∧ E ∈ typ₁ μ) ∧
        ((∃ G, (G ∈ μ ∧ sm E G) ∧ E ∈ typ₁ μ) ↔ ∃ G, (G ∈ μ ∧ sm E G) ∧ E ∈ typ₀ G)) ∧
      ((∃ G, (G ∈ μ ∧ sm E G) ∧ E ∈ typ₀ G) ↔ ∃ G, (G ∈ μ ∧ sm E G) ∧ G ⊆ typ E) := by
  rw [down1_eq]
  exact ⟨⟨mem_img_iff_ex_true (fun _ => mem_typ₁ _ _),
    ex_congr_true (fun _ => mem_typ₁ _ _) (fun _ => mem_typ₀ _ _)⟩,
    ex_congr_true (fun _ => mem_typ₀ _ _) (fun _ => sub_typ _ _)⟩

/-- ✱105·161. \[\begin{aligned}\vdash :\delta \in \mu _{(2)}.&\equiv .(\exists \gamma ).\gamma \in \mu .\delta \text{ sm }\gamma .\delta \in t_{2}ʻ\mu .\\ &\equiv .(\exists \gamma ).\gamma \in \mu .\delta \text{ sm }\gamma .\delta \in t_{1}ʻ\gamma .\\ &\equiv .(\exists \gamma ).\gamma \in \mu .\delta \text{ sm }\gamma .\gamma \subset t^{2}ʻ\delta \quad[*37·1.*63·52·55]\end{aligned}\] -/
theorem pm105_161 {α : Type*} {μ : Set (Set (Set (Set α)))} {E : Set α} :
    ((E ∈ down2 μ ↔ ∃ G, (G ∈ μ ∧ sm E G) ∧ E ∈ typ₂ μ) ∧
        ((∃ G, (G ∈ μ ∧ sm E G) ∧ E ∈ typ₂ μ) ↔ ∃ G, (G ∈ μ ∧ sm E G) ∧ E ∈ typ₁ G)) ∧
      ((∃ G, (G ∈ μ ∧ sm E G) ∧ E ∈ typ₁ G) ↔ ∃ G, (G ∈ μ ∧ sm E G) ∧ G ⊆ typ2 E) := by
  rw [down2_eq]
  exact ⟨⟨mem_img_iff_ex_true (fun _ => mem_typ₂ _ _),
    ex_congr_true (fun _ => mem_typ₂ _ _) (fun _ => mem_typ₁ _ _)⟩,
    ex_congr_true (fun _ => mem_typ₁ _ _) (fun _ => sub_typ2 _ _)⟩

/-- ✱105·2. \(\vdash .\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{1}\text{c}ʻ\iotaʻʻ\alpha\) -/
theorem pm105_2 {α : Type*} {A : Set α} : n₀c A = n₁c (iota ʻʻ A) := by
  rw [n₀c_eq_nc, n₁c_eq]
  exact nc_eq_nc_of_sm (sm_symm (sm_iota_img A))

/-- ✱105·201. \(\vdash .\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{2}\text{c}ʻ\iotaʻʻ\iotaʻʻ\alpha\) -/
theorem pm105_201 {α : Type*} {A : Set α} : n₀c A = n₂c (iota ʻʻ (iota ʻʻ A)) := by
  rw [n₀c_eq_nc, n₂c_eq]
  exact nc_eq_nc_of_sm (sm_symm (sm_trans (sm_iota_img _) (sm_iota_img A)))

/-- ✱105·21. \(\vdash .\text{N}_{0}\text{C}\subset \text{N}_{1}\text{C} \quad[*105·2·15]\) -/
theorem pm105_21 {α : Type*} : (N₀C : Set (Set (Set α))) ⊆ N₁C := by
  rintro μ ⟨A, rfl⟩
  exact ⟨iota ʻʻ A, pm105_2⟩

/-- ✱105·211. \(\vdash .\text{N}_{0}\text{C}\subset \text{N}_{2}\text{C}\) -/
theorem pm105_211 {α : Type*} : (N₀C : Set (Set (Set α))) ⊆ N₂C := by
  rintro μ ⟨A, rfl⟩
  exact ⟨iota ʻʻ (iota ʻʻ A), pm105_201⟩

/-- ✱105·22. \(\vdash :\gamma \in \text{N}_{1}\text{c}ʻ\delta .\supset .\text{N}_{1}\text{c}ʻ\delta =\text{N}_{0}\text{c}ʻ\gamma \quad[*103·26]\) -/
theorem pm105_22 {α : Type*} {E : Set (Set α)} {G : Set α} : G ∈ n₁c E → n₁c E = n₀c G := by
  rw [n₁c_eq, n₀c_eq_nc]
  exact fun h => nc_eq_nc_of_sm (sm_symm h)

/-- ✱105·221. \(\vdash :\gamma \in \text{N}_{2}\text{c}ʻ\delta .\supset .\text{N}_{2}\text{c}ʻ\delta =\text{N}_{0}\text{c}ʻ\gamma\) -/
theorem pm105_221 {α : Type*} {E : Set (Set (Set α))} {G : Set α} :
    G ∈ n₂c E → n₂c E = n₀c G := by
  rw [n₂c_eq, n₀c_eq_nc]
  exact fun h => nc_eq_nc_of_sm (sm_symm h)

/-- ✱105·23. \(\vdash :\exists !\text{N}_{1}\text{c}ʻ\delta .\supset .\text{N}_{1}\text{c}ʻ\delta \in \text{N}_{0}\text{C} \quad[*105·22]\) -/
theorem pm105_23 {α : Type*} {E : Set (Set α)} : (n₁c E).Nonempty → n₁c E ∈ N₀C := by
  rintro ⟨G, hG⟩
  exact ⟨G, pm105_22 hG⟩

/-- ✱105·231. \(\vdash :\exists !\text{N}_{2}\text{c}ʻ\delta .\supset .\text{N}_{2}\text{c}ʻ\delta \in \text{N}_{0}\text{C}\) -/
theorem pm105_231 {α : Type*} {E : Set (Set (Set α))} : (n₂c E).Nonempty → n₂c E ∈ N₀C := by
  rintro ⟨G, hG⟩
  exact ⟨G, pm105_221 hG⟩

/-- ✱105·24. \(\vdash .\text{N}_{1}\text{C}-\iota ʻ\Lambda \subset \text{N}_{0}\text{C} \quad[*105·23]\) -/
theorem pm105_24 {α : Type*} : (N₁C : Set (Set (Set α))) \ ι Λ ⊆ N₀C := by
  rintro μ ⟨⟨E, rfl⟩, hne⟩
  exact pm105_23 (nonempty_of_not_mem_iota_null hne)

/-- ✱105·241. \(\vdash .\text{N}_{2}\text{C}-\iota ʻ\Lambda \subset \text{N}_{0}\text{C}\) -/
theorem pm105_241 {α : Type*} : (N₂C : Set (Set (Set α))) \ ι Λ ⊆ N₀C := by
  rintro μ ⟨⟨E, rfl⟩, hne⟩
  exact pm105_231 (nonempty_of_not_mem_iota_null hne)

/-- ✱105·25. \(\vdash .\text{N}_{0}\text{C}=\text{N}_{1}\text{C}-\iota ʻ\Lambda \quad[*105·21·24.*103·23]\) -/
theorem pm105_25 {α : Type*} : (N₀C : Set (Set (Set α))) = N₁C \ ι Λ := by
  refine Set.Subset.antisymm (fun μ hμ => ⟨pm105_21 hμ, fun h => ?_⟩) pm105_24
  exact pm103_23 ((mem_unitCls.1 h) ▸ hμ)

/-- ✱105·251. \(\vdash .\text{N}_{0}\text{C}=\text{N}_{2}\text{C}-\iota ʻ\Lambda\) -/
theorem pm105_251 {α : Type*} : (N₀C : Set (Set (Set α))) = N₂C \ ι Λ := by
  refine Set.Subset.antisymm (fun μ hμ => ⟨pm105_211 hμ, fun h => ?_⟩) pm105_241
  exact pm103_23 ((mem_unitCls.1 h) ▸ hμ)

/-- ✱105·252. \(\vdash .\text{N}_{1}\text{c}ʻ\beta =\text{N}_{2}\text{c}ʻ\iotaʻʻ\beta\) -/
theorem pm105_252 {α : Type*} {B : Set (Set α)} : n₁c B = n₂c (iota ʻʻ B) := by
  rw [n₁c_eq, n₂c_eq]
  exact nc_eq_nc_of_sm (sm_symm (sm_iota_img B))

/-- ✱105·26. \(\vdash .\text{N}_{1}\text{c}ʻtʻ\alpha =\Lambda\) -/
theorem pm105_26 {α : Type*} {A : Set α} : n₁c (typ A) = Λ := by
  rw [n₁c_eq, nc_typ_eq_empty, Null_eq_empty]

/-- ✱105·261. \(\vdash .\text{N}_{2}\text{c}ʻ\iotaʻʻtʻ\alpha =\Lambda \quad[*105·26·252]\) -/
theorem pm105_261 {α : Type*} {A : Set α} : n₂c (iota ʻʻ typ A) = Λ := by
  rw [← pm105_252]; exact pm105_26

/-- ✱105·27. \(\vdash .\Lambda \in \text{N}_{1}\text{C} \quad[*105·26]\)

`Λ` is in the type of the members of `N₁C`. -/
theorem pm105_27 {α : Type*} : (Λ : Set (Set α)) ∈ N₁C := ⟨typ (∅ : Set α), pm105_26.symm⟩

/-- ✱105·271. \(\vdash .\Lambda \in \text{N}_{2}\text{C}\) -/
theorem pm105_271 {α : Type*} : (Λ : Set (Set α)) ∈ N₂C :=
  ⟨iota ʻʻ typ (∅ : Set α), pm105_261.symm⟩

/-- ✱105·28. \(\vdash .\text{N}_{1}\text{C}=\text{N}_{0}\text{C}\cup \iota ʻ\Lambda \quad[*105·25·27]\) -/
theorem pm105_28 {α : Type*} : (N₁C : Set (Set (Set α))) = N₀C ∪ ι Λ := by
  ext μ
  constructor
  · intro h
    by_cases hΛ : μ ∈ ι Λ
    · exact Or.inr hΛ
    · exact Or.inl (pm105_24 ⟨h, hΛ⟩)
  · rintro (h | h)
    · exact pm105_21 h
    · rw [mem_unitCls.1 h]; exact pm105_27

/-- ✱105·281. \(\vdash .\text{N}_{2}\text{C}=\text{N}_{1}\text{C}=\text{N}_{0}\text{C}\cup \iota ʻ\Lambda\)

The chain is the conjunction of its links. -/
theorem pm105_281 {α : Type*} :
    (N₂C : Set (Set (Set α))) = N₁C ∧ (N₁C : Set (Set (Set α))) = N₀C ∪ ι Λ := by
  have h2 : (N₂C : Set (Set (Set α))) = N₀C ∪ ι Λ := by
    ext μ
    constructor
    · intro h
      by_cases hΛ : μ ∈ ι Λ
      · exact Or.inr hΛ
      · exact Or.inl (pm105_241 ⟨h, hΛ⟩)
    · rintro (h | h)
      · exact pm105_211 h
      · rw [mem_unitCls.1 h]; exact pm105_271
  exact ⟨h2.trans pm105_28.symm, pm105_28⟩

/-- ✱105·29. \(\vdash .\text{NC}\subset \text{N}_{1}\text{C}.\text{NC}\subset \text{N}_{2}\text{C} \quad[*105·281.*103·34]\)

The two `NC`s have independent converse-domain types. -/
theorem pm105_29 {α β β' : Type*} :
    (NC β : Set (Set (Set α))) ⊆ N₁C ∧ (NC β' : Set (Set (Set α))) ⊆ N₂C := by
  constructor
  · intro μ hμ
    rw [(pm105_281 (α := α)).2]
    by_cases hΛ : μ ∈ ι Λ
    · exact Or.inr hΛ
    · exact Or.inl (pm103_34 ⟨hμ, hΛ⟩)
  · intro μ hμ
    rw [(pm105_281 (α := α)).1, (pm105_281 (α := α)).2]
    by_cases hΛ : μ ∈ ι Λ
    · exact Or.inr hΛ
    · exact Or.inl (pm103_34 ⟨hμ, hΛ⟩)

/-- ✱105·3. \(\vdash :\mu =\text{N}_{0}\text{c}ʻ\alpha .\supset .\mu _{(1)}=\text{N}_{1}\text{c}ʻ\alpha\)

`N₁c'α` makes `α` a class of classes, so `μ = N₀c'α` is a class of classes of classes. -/
theorem pm105_3 {α : Type*} {A : Set (Set α)} {μ : Set (Set (Set α))} :
    μ = n₀c A → down1 μ = n₁c A := by
  rintro rfl
  rw [down1_eq, sm_img_n₀c, n₁c_eq]

/-- ✱105·301. \(\vdash :\mu =\text{N}_{0}\text{c}ʻ\alpha .\supset .\mu _{(2)}=\text{N}_{2}\text{c}ʻ\alpha\) -/
theorem pm105_301 {α : Type*} {A : Set (Set (Set α))} {μ : Set (Set (Set (Set α)))} :
    μ = n₀c A → down2 μ = n₂c A := by
  rintro rfl
  rw [down2_eq, sm_img_n₀c, n₂c_eq]

/-- ✱105·31. \(\vdash :\mu \in \text{N}_{0}\text{C}.\supset .\mu {(1)}\in \text{N}_{1}\text{C} \quad[*105·3·15.*103·2]\)

(The e-text prints `μ{(1)}` for `μ_{(1)}`.) -/
theorem pm105_31 {α : Type*} {μ : Set (Set (Set α))} : μ ∈ N₀C → down1 μ ∈ N₁C := by
  rintro ⟨A, rfl⟩
  exact ⟨A, pm105_3 rfl⟩

/-- ✱105·311. \(\vdash :\mu \in \text{N}_{0}\text{C}.\supset .\mu _{(2)}\in \text{N}_{2}\text{C}\) -/
theorem pm105_311 {α : Type*} {μ : Set (Set (Set (Set α)))} : μ ∈ N₀C → down2 μ ∈ N₂C := by
  rintro ⟨A, rfl⟩
  exact ⟨A, pm105_301 rfl⟩

/-- ✱105·312. \(\vdash :\gamma \in \text{N}_{1}\text{c}ʻ\alpha .\supset .\alpha \in \text{N}^{1}\text{c}ʻ\gamma .\text{N}^{1}\text{c}ʻ\gamma =\text{N}_{0}\text{c}ʻ\alpha \quad[*105·12.*103·26]\) -/
theorem pm105_312 {α : Type*} {A : Set (Set α)} {G : Set α} :
    G ∈ n₁c A → A ∈ n1c G ∧ n1c G = n₀c A := by
  rw [n₁c_eq, n1c_eq, n₀c_eq_nc]
  exact fun h => ⟨sm_symm h, nc_eq_nc_of_sm h⟩

/-- ✱105·313. \(\vdash :\gamma \in \text{N}_{2}\text{c}ʻ\alpha .\supset .\alpha \in \text{N}^{2}\text{c}ʻ\gamma .\text{N}^{2}\text{c}ʻ\gamma =\text{N}_{0}\text{c}ʻ\alpha\) -/
theorem pm105_313 {α : Type*} {A : Set (Set (Set α))} {G : Set α} :
    G ∈ n₂c A → A ∈ n2c G ∧ n2c G = n₀c A := by
  rw [n₂c_eq, n2c_eq, n₀c_eq_nc]
  exact fun h => ⟨sm_symm h, nc_eq_nc_of_sm h⟩

/-- ✱105·314. \(\vdash :\text{N}_{1}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\gamma .\supset .\text{N}_{0}\text{c}ʻ\alpha =\text{N}^{1}\text{c}ʻ\gamma \quad[*105·312.*103·12]\) -/
theorem pm105_314 {α : Type*} {A : Set (Set α)} {G : Set α} :
    n₁c A = n₀c G → n₀c A = n1c G := by
  intro h
  exact (pm105_312 (by rw [h]; exact self_mem_n₀c G)).2.symm

/-- ✱105·315. \(\vdash :\text{N}_{2}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\gamma .\supset .\text{N}_{0}\text{c}ʻ\alpha =\text{N}^{2}\text{c}ʻ\gamma\) -/
theorem pm105_315 {α : Type*} {A : Set (Set (Set α))} {G : Set α} :
    n₂c A = n₀c G → n₀c A = n2c G := by
  intro h
  exact (pm105_313 (by rw [h]; exact self_mem_n₀c G)).2.symm

/-- ✱105·316. \(\vdash :\exists !\text{N}_{1}\text{c}ʻ\alpha .\text{N}_{1}\text{c}ʻ\alpha =\text{N}_{1}\text{c}ʻ\beta .\supset .\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta\) -/
theorem pm105_316 {α : Type*} {A B : Set (Set α)} :
    (n₁c A).Nonempty ∧ n₁c A = n₁c B → n₀c A = n₀c B := by
  rintro ⟨⟨G, hG⟩, h⟩
  have hG' : G ∈ n₁c B := h ▸ hG
  exact (pm105_312 hG).2.symm.trans (pm105_312 hG').2

/-- ✱105·317. \(\vdash :\exists !\text{N}_{2}\text{c}ʻ\alpha .\text{N}_{2}\text{c}ʻ\alpha =\text{N}_{2}\text{c}ʻ\beta .\supset .\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta\) -/
theorem pm105_317 {α : Type*} {A B : Set (Set (Set α))} :
    (n₂c A).Nonempty ∧ n₂c A = n₂c B → n₀c A = n₀c B := by
  rintro ⟨⟨G, hG⟩, h⟩
  have hG' : G ∈ n₂c B := h ▸ hG
  exact (pm105_313 hG).2.symm.trans (pm105_313 hG').2

/-- ✱105·32. \(\vdash :\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta .\supset .\text{N}_{1}\text{c}ʻ\alpha =\text{N}_{1}\text{c}ʻ\beta\) -/
theorem pm105_32 {α : Type*} {A B : Set (Set α)} : n₀c A = n₀c B → n₁c A = n₁c B := by
  rw [n₀c_eq_n₀c_iff, n₁c_eq, n₁c_eq]
  exact nc_eq_nc_of_sm

/-- ✱105·321. \(\vdash :\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta .\supset .\text{N}_{2}\text{c}ʻ\alpha =\text{N}_{2}\text{c}ʻ\beta\) -/
theorem pm105_321 {α : Type*} {A B : Set (Set (Set α))} : n₀c A = n₀c B → n₂c A = n₂c B := by
  rw [n₀c_eq_n₀c_iff, n₂c_eq, n₂c_eq]
  exact nc_eq_nc_of_sm

/-- ✱105·322. \(\vdash \colon\ldotp \exists !\text{N}_{1}\text{c}ʻ\alpha .\supset :\text{N}_{1}\text{c}ʻ\alpha =\text{N}_{1}\text{c}ʻ\beta .\equiv .\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta \quad[*105·316·32]\) -/
theorem pm105_322 {α : Type*} {A B : Set (Set α)} :
    (n₁c A).Nonempty → (n₁c A = n₁c B ↔ n₀c A = n₀c B) :=
  fun h => ⟨fun e => pm105_316 ⟨h, e⟩, pm105_32⟩

/-- ✱105·323. \(\vdash \colon\ldotp \exists !\text{N}_{2}\text{c}ʻ\alpha .\supset :\text{N}_{2}\text{c}ʻ\alpha =\text{N}_{2}\text{c}ʻ\beta .\equiv .\text{N}_{0}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta\) -/
theorem pm105_323 {α : Type*} {A B : Set (Set (Set α))} :
    (n₂c A).Nonempty → (n₂c A = n₂c B ↔ n₀c A = n₀c B) :=
  fun h => ⟨fun e => pm105_317 ⟨h, e⟩, pm105_321⟩

/-- ✱105·324. \(\vdash :\exists !\mu _{(1)}.\supset .\exists !\mu \quad[*37·29.(*105·03)]\) -/
theorem pm105_324 {α : Type*} {μ : Set (Set (Set α))} : (down1 μ).Nonempty → μ.Nonempty := by
  rw [down1_eq]
  rintro ⟨_, G, hG, _⟩
  exact ⟨G, hG⟩

/-- ✱105·325. \(\vdash :\exists !\mu _{(2)}.\supset .\exists !\mu \) -/
theorem pm105_325 {α : Type*} {μ : Set (Set (Set (Set α)))} :
    (down2 μ).Nonempty → μ.Nonempty := by
  rw [down2_eq]
  rintro ⟨_, G, hG, _⟩
  exact ⟨G, hG⟩

/-- ✱105·326. \(\vdash :\mu \in \text{NC}.\mu _{(1)}=\text{N}_{0}\text{c}ʻ\gamma .\supset .\mu =\text{N}^{1}\text{c}ʻ\gamma\) -/
theorem pm105_326 {α β : Type*} {μ : Set (Set (Set α))} {G : Set α} :
    μ ∈ NC β ∧ down1 μ = n₀c G → μ = n1c G := by
  rintro ⟨hμ, h⟩
  have hne : (down1 μ).Nonempty := by rw [h]; exact n₀c_nonempty G
  obtain ⟨A, hA⟩ := pm105_324 hne
  have hμA : μ = n₀c A := ((pm103_26 hμ).1 hA).symm
  rw [hμA]
  exact pm105_314 ((pm105_3 hμA).symm.trans h)

/-- ✱105·327. \(\vdash :\mu \in \text{NC}.\mu _{(2)}=\text{N}_{0}\text{c}ʻ\gamma .\supset .\mu =\text{N}^{2}\text{c}ʻ\gamma\) -/
theorem pm105_327 {α β : Type*} {μ : Set (Set (Set (Set α)))} {G : Set α} :
    μ ∈ NC β ∧ down2 μ = n₀c G → μ = n2c G := by
  rintro ⟨hμ, h⟩
  have hne : (down2 μ).Nonempty := by rw [h]; exact n₀c_nonempty G
  obtain ⟨A, hA⟩ := pm105_325 hne
  have hμA : μ = n₀c A := ((pm103_26 hμ).1 hA).symm
  rw [hμA]
  exact pm105_315 ((pm105_301 hμA).symm.trans h)

/-- ✱105·33. \(\vdash :\mu \in \text{NC}.\exists !\mu _{(1)}.\mu _{(1)}=\text{N}_{1}\text{c}ʻ\alpha .\supset .\mu =\text{N}_{0}\text{c}ʻ\alpha\) -/
theorem pm105_33 {α β : Type*} {A : Set (Set α)} {μ : Set (Set (Set α))} :
    (μ ∈ NC β ∧ (down1 μ).Nonempty) ∧ down1 μ = n₁c A → μ = n₀c A := by
  rintro ⟨⟨hμ, hne⟩, h⟩
  obtain ⟨B, hB⟩ := pm105_324 hne
  have hμB : μ = n₀c B := ((pm103_26 hμ).1 hB).symm
  have e : n₁c B = n₁c A := (pm105_3 hμB).symm.trans h
  rw [hμB]
  exact pm105_316 ⟨by rw [e, ← h]; exact hne, e⟩

/-- ✱105·331. \(\vdash :\mu \in \text{NC}.\exists !\mu _{(2)}.\mu _{(2)}=\text{N}_{2}\text{c}ʻ\alpha .\supset .\mu =\text{N}_{0}\text{c}ʻ\alpha\) -/
theorem pm105_331 {α β : Type*} {A : Set (Set (Set α))} {μ : Set (Set (Set (Set α)))} :
    (μ ∈ NC β ∧ (down2 μ).Nonempty) ∧ down2 μ = n₂c A → μ = n₀c A := by
  rintro ⟨⟨hμ, hne⟩, h⟩
  obtain ⟨B, hB⟩ := pm105_325 hne
  have hμB : μ = n₀c B := ((pm103_26 hμ).1 hB).symm
  have e : n₂c B = n₂c A := (pm105_301 hμB).symm.trans h
  rw [hμB]
  exact pm105_317 ⟨by rw [e, ← h]; exact hne, e⟩

/-- ✱105·34. \(\vdash \colon\ldotp \mu \in \text{NC}.\exists !\mu _{(1)}.\supset :\mu _{(1)}=\text{N}_{1}\text{c}ʻ\alpha .\equiv .\mu =\text{N}_{0}\text{c}ʻ\alpha \quad[*105·33·3]\) -/
theorem pm105_34 {α β : Type*} {A : Set (Set α)} {μ : Set (Set (Set α))} :
    μ ∈ NC β ∧ (down1 μ).Nonempty → (down1 μ = n₁c A ↔ μ = n₀c A) :=
  fun h => ⟨fun e => pm105_33 ⟨h, e⟩, pm105_3⟩

/-- ✱105·341. \(\vdash \colon\ldotp \mu \in \text{NC}.\exists !\mu _{(2)}.\supset :\mu _{(2)}=\text{N}_{2}\text{c}ʻ\alpha .\equiv .\mu =\text{N}_{0}\text{c}ʻ\alpha\) -/
theorem pm105_341 {α β : Type*} {A : Set (Set (Set α))} {μ : Set (Set (Set (Set α)))} :
    μ ∈ NC β ∧ (down2 μ).Nonempty → (down2 μ = n₂c A ↔ μ = n₀c A) :=
  fun h => ⟨fun e => pm105_331 ⟨h, e⟩, pm105_301⟩

/-- ✱105·342. \(\vdash .\mu \in \text{NC}.\supset .\mu _{(1)}\in \text{N}_{1}\text{C}\)

(The e-text prints the first dots as `⊢ . μ ∈ NC . ⊃ .`.) -/
theorem pm105_342 {α β : Type*} {μ : Set (Set (Set α))} : μ ∈ NC β → down1 μ ∈ N₁C := by
  intro hμ
  by_cases hne : μ.Nonempty
  · exact pm105_31 (pm103_34 ⟨hμ, fun h => by
      obtain ⟨A, hA⟩ := hne
      rw [mem_unitCls.1 h, Null_eq_empty] at hA
      exact hA⟩)
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, down1_eq, sm_img_empty, ← Null_eq_empty]
    exact pm105_27

/-- ✱105·343. \(\vdash :\mu \in \text{NC}.\supset .\mu _{(2)}\in \text{N}_{2}\text{C}\) -/
theorem pm105_343 {α β : Type*} {μ : Set (Set (Set (Set α)))} : μ ∈ NC β → down2 μ ∈ N₂C := by
  intro hμ
  by_cases hne : μ.Nonempty
  · exact pm105_311 (pm103_34 ⟨hμ, fun h => by
      obtain ⟨A, hA⟩ := hne
      rw [mem_unitCls.1 h, Null_eq_empty] at hA
      exact hA⟩)
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, down2_eq, sm_img_empty, ← Null_eq_empty]
    exact pm105_271

/-- ✱105·344. \(\vdash :\mu =\text{N}^{1}\text{c}ʻ\gamma .\supset .\mu _{(1)}=\text{N}_{0}\text{c}ʻ\gamma\) -/
theorem pm105_344 {α : Type*} {μ : Set (Set (Set α))} {G : Set α} :
    μ = n1c G → down1 μ = n₀c G := by
  rintro rfl
  rw [down1_eq, n1c_eq, n₀c_eq_nc]
  exact pm100_511 ⟨_, sm_iota_img G⟩

/-- ✱105·345. \(\vdash :\mu =\text{N}^{2}\text{c}ʻ\gamma .\supset .\mu _{(2)}=\text{N}_{0}\text{c}ʻ\gamma\) -/
theorem pm105_345 {α : Type*} {μ : Set (Set (Set (Set α)))} {G : Set α} :
    μ = n2c G → down2 μ = n₀c G := by
  rintro rfl
  rw [down2_eq, n2c_eq, n₀c_eq_nc]
  exact pm100_511 ⟨_, sm_trans (sm_iota_img _) (sm_iota_img G)⟩

/-- ✱105·35. \(\vdash \colon\ldotp \mu \in \text{NC}.\nu \in \text{N}_{0}\text{C}.\supset :\mu =\nu ^{(1)}.\equiv .\mu _{(1)}=\nu\) -/
theorem pm105_35 {α β : Type*} {μ : Set (Set (Set α))} {ν : Set (Set α)} :
    μ ∈ NC β ∧ ν ∈ N₀C → (μ = up1 ν ↔ down1 μ = ν) := by
  rintro ⟨hμ, ⟨G, rfl⟩⟩
  have k : up1 (n₀c G) = n1c G := (pm104_26 rfl).1.trans (pm104_26 rfl).2
  rw [k]
  exact ⟨pm105_344, fun h => pm105_326 ⟨hμ, h⟩⟩

/-- ✱105·351. \(\vdash \colon\ldotp \mu \in \text{NC}.\nu \in \text{N}_{0}\text{C}.\supset :\mu =\nu ^{(2)}.\equiv .\mu _{(2)}=\nu\) -/
theorem pm105_351 {α β : Type*} {μ : Set (Set (Set (Set α)))} {ν : Set (Set α)} :
    μ ∈ NC β ∧ ν ∈ N₀C → (μ = up2 ν ↔ down2 μ = ν) := by
  rintro ⟨hμ, ⟨G, rfl⟩⟩
  have h := pm104_32 (A := G) rfl
  have k : up2 (n₀c G) = n2c G := h.1.1.1.trans (h.1.1.2.trans h.1.2)
  rw [k]
  exact ⟨pm105_345, fun h => pm105_327 ⟨hμ, h⟩⟩

/-- ✱105·352. \(\vdash \colon\ldotp \mu ,\nu \in \text{NC}.\exists !\nu .\supset :\mu =\nu ^{(1)}.\equiv .\mu _{(1)}=\nu \quad[*105·35.*103·34]\)

The two `NC`s have independent converse-domain types. -/
theorem pm105_352 {α β β' : Type*} {μ : Set (Set (Set α))} {ν : Set (Set α)} :
    (μ ∈ NC β ∧ ν ∈ NC β') ∧ ν.Nonempty → (μ = up1 ν ↔ down1 μ = ν) := by
  rintro ⟨⟨hμ, hν⟩, ⟨A, hA⟩⟩
  refine pm105_35 ⟨hμ, pm103_34 ⟨hν, fun h => ?_⟩⟩
  rw [mem_unitCls.1 h, Null_eq_empty] at hA
  exact hA

/-- ✱105·353. \(\vdash \colon\ldotp \mu ,\nu \in \text{NC}.\exists !\nu .\supset :\mu =\nu ^{(2)}.\equiv .\mu _{(2)}=\nu\) -/
theorem pm105_353 {α β β' : Type*} {μ : Set (Set (Set (Set α)))} {ν : Set (Set α)} :
    (μ ∈ NC β ∧ ν ∈ NC β') ∧ ν.Nonempty → (μ = up2 ν ↔ down2 μ = ν) := by
  rintro ⟨⟨hμ, hν⟩, ⟨A, hA⟩⟩
  refine pm105_351 ⟨hμ, pm103_34 ⟨hν, fun h => ?_⟩⟩
  rw [mem_unitCls.1 h, Null_eq_empty] at hA
  exact hA

/-- ✱105·354. \(\vdash :\nu \in \text{NC}.\exists !\nu .\supset .{\nu ^{(1)}}_{(1)}=\nu \quad[*105·352]\) -/
theorem pm105_354 {α β : Type*} {ν : Set (Set α)} :
    ν ∈ NC β ∧ ν.Nonempty → down1 (up1 ν) = ν :=
  fun h => (pm105_352 ⟨⟨pm104_141 h, h.1⟩, h.2⟩).1 rfl

/-- ✱105·355. \(\vdash :\nu \in \text{NC}.\exists !\nu .\supset .\{\nu ^{(2)}\}_{(2)}=\nu\) -/
theorem pm105_355 {α β : Type*} {ν : Set (Set α)} :
    ν ∈ NC β ∧ ν.Nonempty → down2 (up2 ν) = ν :=
  fun h => (pm105_353 ⟨⟨pm104_142 h, h.1⟩, h.2⟩).1 rfl

/-- ✱105·356. \(\vdash :\mu \in \text{NC}.\exists !\mu _{(1)}.\supset .\{\mu _{(1)}\}^{(1)}=\mu \quad[*105·352]\) -/
theorem pm105_356 {α β : Type*} {μ : Set (Set (Set α))} :
    μ ∈ NC β ∧ (down1 μ).Nonempty → up1 (down1 μ) = μ := by
  rintro ⟨hμ, hne⟩
  have hν : down1 μ ∈ NC (Set α) := by
    rw [down1_eq]; exact pm100_52 ⟨hμ, pm105_324 hne⟩
  exact ((pm105_352 ⟨⟨hμ, hν⟩, hne⟩).2 rfl).symm

/-- ✱105·357. \(\vdash :\mu \in \text{NC}.\exists !\mu _{(2)}.\supset .\{\mu _{(2)}\}^{(2)}=\mu\) -/
theorem pm105_357 {α β : Type*} {μ : Set (Set (Set (Set α)))} :
    μ ∈ NC β ∧ (down2 μ).Nonempty → up2 (down2 μ) = μ := by
  rintro ⟨hμ, hne⟩
  have hν : down2 μ ∈ NC (Set (Set α)) := by
    rw [down2_eq]; exact pm100_52 ⟨hμ, pm105_325 hne⟩
  exact ((pm105_353 ⟨⟨hμ, hν⟩, hne⟩).2 rfl).symm

/-- ✱105·36. \(\vdash :\beta \in \text{N}_{1}\text{c}ʻ\alpha .\gamma \in \text{N}_{1}\text{c}ʻ\beta .\supset .\gamma \in \text{N}_{2}\text{c}ʻ\alpha\) -/
theorem pm105_36 {α : Type*} {A : Set (Set (Set α))} {B : Set (Set α)} {G : Set α} :
    B ∈ n₁c A ∧ G ∈ n₁c B → G ∈ n₂c A := by
  simp only [n₁c_eq, n₂c_eq]
  exact fun ⟨h1, h2⟩ => sm_trans h2 h1

/-- ✱105·361. \(\vdash :\beta \in \text{N}_{1}\text{c}ʻ\alpha .\gamma \in \text{N}_{2}\text{c}ʻ\alpha .\supset .\gamma \in \text{N}_{1}\text{c}ʻ\beta\) -/
theorem pm105_361 {α : Type*} {A : Set (Set (Set α))} {B : Set (Set α)} {G : Set α} :
    B ∈ n₁c A ∧ G ∈ n₂c A → G ∈ n₁c B := by
  simp only [n₁c_eq, n₂c_eq]
  exact fun ⟨h1, h2⟩ => sm_trans h2 (sm_symm h1)

/-- ✱105·362. \(\vdash :\beta \in \text{N}_{1}\text{c}ʻ\alpha .\supset .\text{N}_{1}\text{c}ʻ\beta =\text{N}_{2}\text{c}ʻ\alpha \quad[*105·36·361]\) -/
theorem pm105_362 {α : Type*} {A : Set (Set (Set α))} {B : Set (Set α)} :
    B ∈ n₁c A → n₁c B = n₂c A := by
  simp only [n₁c_eq, n₂c_eq]
  exact nc_eq_nc_of_sm

/-- ✱105·37. \(\vdash :\text{N}_{0}\text{c}ʻ\beta =\text{N}_{1}\text{c}ʻ\alpha .\supset .\text{N}_{1}\text{c}ʻ\beta =\text{N}_{2}\text{c}ʻ\alpha \quad[*105·362.*103·12]\) -/
theorem pm105_37 {α : Type*} {A : Set (Set (Set α))} {B : Set (Set α)} :
    n₀c B = n₁c A → n₁c B = n₂c A :=
  fun h => pm105_362 (h ▸ self_mem_n₀c B)

/-- ✱105·371. \(\vdash :\exists !\mu _{(2)}.\supset .\exists !\mu _{(1)}\) -/
theorem pm105_371 {α : Type*} {μ : Set (Set (Set (Set α)))} :
    (down2 μ).Nonempty → (down1 μ).Nonempty := by
  rw [down2_eq, down1_eq]
  rintro ⟨E, A, hA, hEA⟩
  exact ⟨iota ʻʻ E, A, hA, sm_trans (sm_iota_img E) hEA⟩

/-- ✱105·372. \(\vdash :\mu _{(1)}=\Lambda .\supset .\mu _{(2)}=\Lambda \quad[*105·371.\text{Transp}]\) -/
theorem pm105_372 {α : Type*} {μ : Set (Set (Set (Set α)))} : down1 μ = Λ → down2 μ = Λ := by
  intro h
  rw [Null_eq_empty] at h ⊢
  by_contra h'
  have := pm105_371 (Set.nonempty_iff_ne_empty.2 h')
  rw [h] at this
  exact Set.not_nonempty_empty this

/-- ✱105·38. \(\vdash .\{\mu _{(1)}\}_{(1)}=\mu _{(2)}\) -/
theorem pm105_38 {α : Type*} {μ : Set (Set (Set (Set α)))} : down1 (down1 μ) = down2 μ := by
  rw [down1_eq, down1_eq, down2_eq]
  ext E
  constructor
  · rintro ⟨X, ⟨A, hA, hXA⟩, hEX⟩
    exact ⟨A, hA, sm_trans hEX hXA⟩
  · rintro ⟨A, hA, hEA⟩
    exact ⟨iota ʻʻ E, ⟨A, hA, sm_trans (sm_iota_img E) hEA⟩, sm_symm (sm_iota_img E)⟩

/-- ✱105·4. \(\vdash :\gamma \in \text{N}_{2}\text{c}ʻ\alpha .\supset .\iotaʻʻ\gamma \in \text{N}_{1}\text{c}ʻ\alpha\) -/
theorem pm105_4 {α : Type*} {A : Set (Set (Set α))} {G : Set α} :
    G ∈ n₂c A → iota ʻʻ G ∈ n₁c A := by
  simp only [n₂c_eq, n₁c_eq]
  exact fun h => sm_trans (sm_iota_img G) h

/-- ✱105·41. \(\vdash :\exists !\text{N}_{2}\text{c}ʻ\alpha .\supset .\exists !\text{N}_{1}\text{c}ʻ\alpha \quad[*105·4]\) -/
theorem pm105_41 {α : Type*} {A : Set (Set (Set α))} : (n₂c A).Nonempty → (n₁c A).Nonempty :=
  fun ⟨_, hG⟩ => ⟨_, pm105_4 hG⟩

/-- ✱105·42. \(\vdash :\text{N}_{1}\text{c}ʻ\alpha =\Lambda .\supset .\text{N}_{2}\text{c}ʻ\alpha =\Lambda \quad[*105·41]\) -/
theorem pm105_42 {α : Type*} {A : Set (Set (Set α))} : n₁c A = Λ → n₂c A = Λ := by
  intro h
  rw [Null_eq_empty] at h ⊢
  by_contra h'
  have := pm105_41 (Set.nonempty_iff_ne_empty.2 h')
  rw [h] at this
  exact Set.not_nonempty_empty this

/-- ✱105·43. \(\vdash :\mu _{(1)}=\text{N}_{1}\text{c}ʻ\alpha .\supset .\mu _{(2)}=\text{N}_{2}\text{c}ʻ\alpha \)

`μ_{(1)} = N₁c'α` makes `α` a class of the type of the members of `μ`. -/
theorem pm105_43 {α : Type*} {μ : Set (Set (Set (Set α)))} {A : Set (Set (Set α))} :
    down1 μ = n₁c A → down2 μ = n₂c A := by
  rw [down1_eq, down2_eq, n₁c_eq, n₂c_eq]
  intro h
  ext E
  constructor
  · rintro ⟨X, hX, hEX⟩
    have h1 : iota ʻʻ E ∈ sm ʻʻ μ := ⟨X, hX, sm_trans (sm_iota_img E) hEX⟩
    rw [h] at h1
    exact sm_trans (sm_symm (sm_iota_img E)) h1
  · intro hE
    have h1 : iota ʻʻ E ∈ nc (Set α) A := sm_trans (sm_iota_img E) hE
    rw [← h] at h1
    obtain ⟨X, hX, hEX⟩ := h1
    exact ⟨X, hX, sm_trans (sm_symm (sm_iota_img E)) hEX⟩

/-- ✱105·44. \(\vdash .\text{N}_{2}\text{c}ʻt^{2}ʻ\alpha =\Lambda\) -/
theorem pm105_44 {α : Type*} {A : Set α} : n₂c (typ2 A) = Λ :=
  pm105_42 (pm105_26 (A := typ A))

/-!
## [✱106] Cardinals of relational types

*(Vol. 2, p. 60)*

> *Summary of* *106.
>
> In this number we have to consider the cardinals whose members are classes of relations which have a given relation of type to some given class. For example, we have \(\downarrow xʻʻ\alpha \text{ sm }\alpha\), and \(\downarrow xʻʻ\alpha\) has a given relation of type to \(\alpha\) when \(x\) is given. Thus we want a notation for \[ \text{Nc}ʻ\alpha \cap tʻ\downarrow xʻʻ\alpha \] and all the associated ideas. In this number, we shall deal only with relations in which the referent and relatum have a relation, as to type, which can be expressed by the notations of *63, *i.e.* roughly speaking, when, for suitable values of \(\alpha\), \(m\), \(n\), our relations are contained in \[ t^{m}ʻ\alpha \uparrow t^{n}ʻ\alpha\,\,\, \text{or}\,\,\, t_{m}ʻ\alpha \uparrow t_{n}ʻ\alpha\,\,\, \text{or}\,\,\, t^{m}ʻ\alpha \uparrow t_{n}ʻ\alpha\,\,\, \text{or}\,\,\, t_{m}ʻ\alpha \uparrow t^{n}ʻ\alpha. \]
>
> …

**Lean reading.** `N₀₀c'α`, `N¹¹c'α`, `N₀₁c'α`, `N₀¹c'α`, `¹N₀c'α`, `N₀₀C`, `μ_{(00)}`, `μ^{(11)}`
are the Defs definitions `n₀₀c A`, `n11c A`, `n₀₁c A`, `n₀1c A`, `n1₀c A`, `N₀₀C`, `down00 μ`,
`up11 μ`. The further analogues that ✱106 uses but PM defines only by "Df etc." (`N₀²c`, `²N₀c`,
`N₀¹C`, `¹N₀C`, `N₀²C`, `²N₀C`, `N₁₁c`, `μ_{(11)}`, `μ₀¹`) are defined in this file in the same
pattern (`typ₀2`, `typ2₀`, `n₀2c`, `n2₀c`, `N₀1C`, `N1₀C`, `N₀2C`, `N2₀C`, `n₁₁c`, `down11`,
`down₀1`), and the propositions using them are `proved (reading)`. `↓x''α` is `coupleR x ʻʻ A`,
`Cnv''λ` is `Cnv ʻʻ L`, `α ↑ β` is `cross A B`, `Rl'(α ↑ α)` is `rl (cross A A)`. The Dfs
✱106·012·02·021·03·041, printed as propositions, have status `definition`.

**Status.** proved (all propositions; ✱106·01·011·012·02·021·03·04·041 definition; ✱106·11,
✱106·12 proved (reading): transcription errors; ✱106·5 proved (reading): `ᗡ'''(α ↑ α)` read as
`Rl'(α ↑ α)`; ✱106·141, ✱106·202, ✱106·204, ✱106·212, ✱106·213, ✱106·221, ✱106·222, ✱106·223,
✱106·231, ✱106·241, ✱106·251, ✱106·402, ✱106·411 proved (reading): analogues defined by "Df etc.";
✱106·31 proved (corrected): `↓x''β` printed for `↓y''β`, the printed form is refuted by
`pm106_31_printed_false`)
-/

/-! ### The analogues ("Df etc.") of ✱106·01–·041 used in ✱106

PM's Summary of ✱106 and the "Df etc." of ✱106·012–·041 extend the definitions of `Defs/Part3` to
further indices and suffixes ("with analogous definitions for `t^{μν}'α`, `t^μ_ν'α` and
`^μt_ν'α`"). The ones used by the propositions of ✱106 are defined here, in the pattern of the
Defs (`N_s c'α = Nc'α ∩ t't_s'α`, `N_s C = D'N_s c`, `ξ_{μν} = sm''ξ ∩ t't_{μν}'t₁'ξ`). -/

/-- `t₀²'α = t'(t₀'α ↑ t²'α)` (the analogue of ✱64·03 for the index 2). -/
def typ₀2 {α : Type*} (A : Set α) : Set (α → Set (Set α) → Prop) :=
  typ (cross (typ₀ A) (typ2 A))

/-- `²t₀'α = t'(t²'α ↑ t₀'α)` (the analogue of ✱64·04 for the index 2). -/
def typ2₀ {α : Type*} (A : Set α) : Set (Set (Set α) → α → Prop) :=
  typ (cross (typ2 A) (typ₀ A))

/-- `N₀²c'α = Nc'α ∩ t't₀²'α`. -/
def n₀2c {α : Type*} (A : Set α) : Set (Set (α → Set (Set α) → Prop)) :=
  nc (α → Set (Set α) → Prop) A ∩ typ (typ₀2 A)

/-- `²N₀c'α = Nc'α ∩ t'²t₀'α`. -/
def n2₀c {α : Type*} (A : Set α) : Set (Set (Set (Set α) → α → Prop)) :=
  nc (Set (Set α) → α → Prop) A ∩ typ (typ2₀ A)

/-- `N₁₁c'κ = Nc'κ ∩ t't₁₁'κ` (`κ` a class of classes). -/
def n₁₁c {α : Type*} (A : Set (Set α)) : Set (Set (α → α → Prop)) :=
  nc (α → α → Prop) A ∩ typ (typ₁₁ A)

/-- The relation `N₀¹c` of `N₀¹c'α` to `α`. -/
def N₀1c {α : Type*} : Set (Set (α → Set α → Prop)) → Set α → Prop := graph n₀1c

/-- `N₀¹C = D'N₀¹c`. -/
def N₀1C {α : Type*} : Set (Set (Set (α → Set α → Prop))) :=
  dom (N₀1c : Set (Set (α → Set α → Prop)) → Set α → Prop)

/-- The relation `¹N₀c` of `¹N₀c'α` to `α`. -/
def N1₀c {α : Type*} : Set (Set (Set α → α → Prop)) → Set α → Prop := graph n1₀c

/-- `¹N₀C = D'¹N₀c`. -/
def N1₀C {α : Type*} : Set (Set (Set (Set α → α → Prop))) :=
  dom (N1₀c : Set (Set (Set α → α → Prop)) → Set α → Prop)

/-- The relation `N₀²c` of `N₀²c'α` to `α`. -/
def N₀2c {α : Type*} : Set (Set (α → Set (Set α) → Prop)) → Set α → Prop := graph n₀2c

/-- `N₀²C = D'N₀²c`. -/
def N₀2C {α : Type*} : Set (Set (Set (α → Set (Set α) → Prop))) :=
  dom (N₀2c : Set (Set (α → Set (Set α) → Prop)) → Set α → Prop)

/-- The relation `²N₀c` of `²N₀c'α` to `α`. -/
def N2₀c {α : Type*} : Set (Set (Set (Set α) → α → Prop)) → Set α → Prop := graph n2₀c

/-- `²N₀C = D'²N₀c`. -/
def N2₀C {α : Type*} : Set (Set (Set (Set (Set α) → α → Prop))) :=
  dom (N2₀c : Set (Set (Set (Set α) → α → Prop)) → Set α → Prop)

/-- `μ_{(11)} = sm''μ ∩ t't₁₁'t₁'μ` (the analogue of ✱106·04). -/
def down11 {α : Type*} (μ : Set (Set (Set α))) : Set (Set (α → α → Prop)) :=
  sm ʻʻ μ ∩ typ (typ₁₁ (typ₁ μ))

/-- `μ₀¹ = sm''μ ∩ t't₀¹'t₁'μ` (the analogue of ✱106·04; printed `μ₀¹` in ✱106·141). -/
def down₀1 {α : Type*} (μ : Set (Set α)) : Set (Set (α → Set α → Prop)) :=
  sm ʻʻ μ ∩ typ (typ₀1 (typ₁ μ))

private theorem n₀2c_eq {α : Type*} (A : Set α) : n₀2c A = nc (α → Set (Set α) → Prop) A := by
  simp only [n₀2c, typ_eq_univ, Set.inter_univ]
private theorem n2₀c_eq {α : Type*} (A : Set α) : n2₀c A = nc (Set (Set α) → α → Prop) A := by
  simp only [n2₀c, typ_eq_univ, Set.inter_univ]
private theorem n₁₁c_eq {α : Type*} (A : Set (Set α)) : n₁₁c A = nc (α → α → Prop) A := by
  simp only [n₁₁c, typ_eq_univ, Set.inter_univ]
private theorem down11_eq {α : Type*} (μ : Set (Set (Set α))) : down11 μ = sm ʻʻ μ := by
  simp only [down11, typ_eq_univ, Set.inter_univ]
private theorem down₀1_eq {α : Type*} (μ : Set (Set α)) : down₀1 μ = sm ʻʻ μ := by
  simp only [down₀1, typ_eq_univ, Set.inter_univ]

/-- A non-null `Nc'α` is a homogeneous cardinal. -/
private theorem nc_mem_N₀C {α β : Type*} {A : Set β} (h : (nc α A).Nonempty) : nc α A ∈ N₀C := by
  obtain ⟨X, hX⟩ := h
  exact mem_N₀C.2 ⟨X, nc_eq_n₀c_of_mem hX⟩

/-- A class of homogeneous cardinals is a `Cls ex² excl` (cf. ✱84·26). -/
private theorem clsEx2excl_of_sub {τ : Type*} {X : Set (Set (Set τ))} (h : X ⊆ N₀C) :
    X ∈ ClsEx2excl := by
  have hex : ∀ μ ν : Set (Set τ), (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ μ ≠ ν → μ ∩ ν = Λ :=
    (pm103_24 (α := τ)).1
  exact ⟨fun μ ν ⟨⟨hμ, hν⟩, hne⟩ => hex μ ν ⟨⟨h hμ, h hν⟩, hne⟩, fun hΛ => pm103_23 (h hΛ)⟩

/-- `Cnv''λ sm λ` (cf. ✱73·4). -/
private theorem sm_Cnv_img {α β : Type*} (L : Set (α → β → Prop)) : sm (Cnv ʻʻ L) L := by
  have e : Cnv ʻʻ L = graph cnv ʻʻ L := by
    ext Q
    exact ⟨fun ⟨P, hP, h⟩ => ⟨P, hP, Cnv_iff.1 h⟩, fun ⟨P, hP, h⟩ => ⟨P, hP, Cnv_iff.2 h⟩⟩
  rw [e]
  exact sm_graph_img fun P _ P' _ h => congrArg cnv h

/-- ✱106·01 (Df). \(\text{N}_{00}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻt_{00}ʻ\alpha \quad\text{Df}\) -/
theorem pm106_01 {α : Type*} {A : Set α} : n₀₀c A = nc (α → α → Prop) A ∩ typ (typ₀₀ A) := rfl

/-- ✱106·011 (Df). \(\text{N}^{11}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻt^{11}ʻ\alpha \quad\text{Df}\) -/
theorem pm106_011 {α : Type*} {A : Set α} :
    n11c A = nc (Set α → Set α → Prop) A ∩ typ (typ11 A) := rfl

/-- ✱106·012. \(\text{N}_{01}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻt_{01}ʻ\alpha \quad\text{Df etc.}\)

**Status.** definition: printed in the e-text as a proposition ("Df etc."); `α` is a class of
classes. -/
theorem pm106_012 {α : Type*} {A : Set (Set α)} :
    n₀₁c A = nc (Set α → α → Prop) A ∩ typ (typ₀₁ A) := rfl

/-- ✱106·02. \(\text{N}^{1}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻt_{0}^{1}ʻ\alpha \quad\text{Df etc.}\)

**Status.** definition: printed in the e-text as a proposition ("Df etc."), and with `N¹c` for the
definiendum `N₀¹c` (transcription error: `t₀¹` and ✱106·22 show `N₀¹c'α`; `N¹c` is ✱104·01). -/
theorem pm106_02 {α : Type*} {A : Set α} :
    n₀1c A = nc (α → Set α → Prop) A ∩ typ (typ₀1 A) := rfl

/-- ✱106·021. \(^{1}\text{N}_{0}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻ^{1}t_{0}ʻ\alpha \quad\text{Df etc.}\)

**Status.** definition: printed in the e-text as a proposition ("Df etc."). -/
theorem pm106_021 {α : Type*} {A : Set α} :
    n1₀c A = nc (Set α → α → Prop) A ∩ typ (typ1₀ A) := rfl

/-- ✱106·03. \(\text{N}_{00}\text{C} = \text{D}ʻ\text{N}_{00}\text{c} \quad\text{Df etc.}\)

**Status.** definition: printed in the e-text as a proposition ("Df etc."); the definiens is the
descriptive function `D'N₀₀c`, kept as a description. -/
theorem pm106_03 {α : Type*} :
    Desc D N₀₀c (fun K => (N₀₀C : Set (Set (Set (α → α → Prop)))) = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱106·04 (Df). \(\mu _{(00)} = \text{ sm }ʻʻ\mu \cap tʻt_{00}ʻt_{1}ʻ\mu \quad\text{Df}\) -/
theorem pm106_04 {α : Type*} {μ : Set (Set α)} : down00 μ = sm ʻʻ μ ∩ typ (typ₀₀ (typ₁ μ)) := rfl

/-- ✱106·041. \(\mu ^{(11)} = \text{ sm }ʻʻ\mu \cap tʻt^{11}ʻt_{1}ʻ\mu \quad\text{Df etc.}\)

**Status.** definition: printed in the e-text as a proposition ("Df etc."). -/
theorem pm106_041 {α : Type*} {μ : Set (Set α)} :
    up11 μ = sm ʻʻ μ ∩ typ (typ11 (typ₁ μ)) := rfl

/-- ✱106·1. \[\begin{aligned}\vdash :\beta \in \text{N}_{00}\text{c}ʻ\alpha . &\equiv .\beta \in \text{Nc}ʻ\alpha .\beta \in tʻt_{00}ʻ\alpha .\\ &\equiv .\beta \text{ sm } \alpha .\beta \in tʻtʻ(t_{0}ʻ\alpha \uparrow t_{0}ʻ\alpha ).\\ &\equiv .\beta \text{ sm } \alpha .\beta \subset tʻ(\alpha \uparrow \alpha )\\ &[*100·1.(*106·01.*64·01).*64·11]\end{aligned}\]

`β` is a class of relations between members of the type of `α`; the chain of four is the
conjunction of its three links. -/
theorem pm106_1 {α : Type*} {A : Set α} {B : Set (α → α → Prop)} :
    ((B ∈ n₀₀c A ↔ B ∈ nc (α → α → Prop) A ∧ B ∈ typ (typ₀₀ A)) ∧
        (B ∈ nc (α → α → Prop) A ∧ B ∈ typ (typ₀₀ A) ↔
          sm B A ∧ B ∈ typ (typ (cross (typ₀ A) (typ₀ A))))) ∧
      (sm B A ∧ B ∈ typ (typ (cross (typ₀ A) (typ₀ A))) ↔ sm B A ∧ B ⊆ typ (cross A A)) :=
  ⟨⟨Iff.rfl, ⟨fun h => ⟨h.1, mem_typ _ _⟩, fun h => ⟨h.1, mem_typ _ _⟩⟩⟩,
    ⟨fun h => ⟨h.1, sub_typ _ _⟩, fun h => ⟨h.1, mem_typ _ _⟩⟩⟩

/-- ✱106·101. \[\begin{aligned}\vdash :\beta \in \text{N}^{11}\text{c}ʻ\alpha . &\equiv .\beta \in \text{Nc}ʻ\alpha .\beta \in tʻt^{11}ʻ\alpha .\\ &\equiv .\beta \text{ sm } \alpha .\beta \in tʻtʻ(tʻ\alpha \uparrow tʻ\alpha ).\\ &\equiv .\beta \text{ sm } \alpha .\beta \subset tʻ(tʻ\alpha \uparrow tʻ\alpha )\end{aligned}\] -/
theorem pm106_101 {α : Type*} {A : Set α} {B : Set (Set α → Set α → Prop)} :
    ((B ∈ n11c A ↔ B ∈ nc (Set α → Set α → Prop) A ∧ B ∈ typ (typ11 A)) ∧
        (B ∈ nc (Set α → Set α → Prop) A ∧ B ∈ typ (typ11 A) ↔
          sm B A ∧ B ∈ typ (typ (cross (typ A) (typ A))))) ∧
      (sm B A ∧ B ∈ typ (typ (cross (typ A) (typ A))) ↔
        sm B A ∧ B ⊆ typ (cross (typ A) (typ A))) :=
  ⟨⟨Iff.rfl, ⟨fun h => ⟨h.1, mem_typ _ _⟩, fun h => ⟨h.1, mem_typ _ _⟩⟩⟩,
    ⟨fun h => ⟨h.1, sub_typ _ _⟩, fun h => ⟨h.1, mem_typ _ _⟩⟩⟩

/-- ✱106·11. \[\begin{aligned}\vdash :\beta \in \text{N}_{01}\text{c}ʻ\alpha . &\equiv .\beta \in \text{Nc}ʻ\alpha .\beta tʻt_{01}ʻ\alpha .\\ &\equiv .\beta \text{ sm } \alpha .\beta \in tʻtʻ(t_{0}ʻ\alpha \uparrow t_{1}ʻ\alpha ).\\ &\equiv .\beta \text{ sm } \alpha .\beta \subset tʻ(t_{0}ʻ\alpha \uparrow t_{1}ʻ\alpha )\end{aligned}\]

**Status.** proved (reading): transcription error: the e-text omits the `∈` of
`β ∈ t't₀₁'α`. -/
theorem pm106_11 {α : Type*} {A : Set (Set α)} {B : Set (Set α → α → Prop)} :
    ((B ∈ n₀₁c A ↔ B ∈ nc (Set α → α → Prop) A ∧ B ∈ typ (typ₀₁ A)) ∧
        (B ∈ nc (Set α → α → Prop) A ∧ B ∈ typ (typ₀₁ A) ↔
          sm B A ∧ B ∈ typ (typ (cross (typ₀ A) (typ₁ A))))) ∧
      (sm B A ∧ B ∈ typ (typ (cross (typ₀ A) (typ₁ A))) ↔
        sm B A ∧ B ⊆ typ (cross (typ₀ A) (typ₁ A))) :=
  ⟨⟨Iff.rfl, ⟨fun h => ⟨h.1, mem_typ _ _⟩, fun h => ⟨h.1, mem_typ _ _⟩⟩⟩,
    ⟨fun h => ⟨h.1, sub_typ _ _⟩, fun h => ⟨h.1, mem_typ _ _⟩⟩⟩

/-- ✱106·12. \[\begin{aligned}\vdash :\beta \in \text{N}^{1}\text{c}ʻ\alpha . &\equiv .\beta \in \text{Nc}ʻ\alpha .\beta \in tʻt_{0}^{1}ʻ\alpha .\\ &\equiv .\beta \text{ sm } \alpha .\beta \in tʻtʻ(t_{0}ʻ\alpha \uparrow tʻ\alpha ).\\ &\equiv .\beta \text{ sm } \alpha .\beta \subset tʻ(t_{0}ʻ\alpha \uparrow tʻ\alpha )\end{aligned}\]

**Status.** proved (reading): transcription error: the e-text prints `N¹c'α` for `N₀¹c'α` (as in
✱106·02; `t₀¹'α` shows which cardinal is meant). -/
theorem pm106_12 {α : Type*} {A : Set α} {B : Set (α → Set α → Prop)} :
    ((B ∈ n₀1c A ↔ B ∈ nc (α → Set α → Prop) A ∧ B ∈ typ (typ₀1 A)) ∧
        (B ∈ nc (α → Set α → Prop) A ∧ B ∈ typ (typ₀1 A) ↔
          sm B A ∧ B ∈ typ (typ (cross (typ₀ A) (typ A))))) ∧
      (sm B A ∧ B ∈ typ (typ (cross (typ₀ A) (typ A))) ↔
        sm B A ∧ B ⊆ typ (cross (typ₀ A) (typ A))) :=
  ⟨⟨Iff.rfl, ⟨fun h => ⟨h.1, mem_typ _ _⟩, fun h => ⟨h.1, mem_typ _ _⟩⟩⟩,
    ⟨fun h => ⟨h.1, sub_typ _ _⟩, fun h => ⟨h.1, mem_typ _ _⟩⟩⟩

/-- ✱106·121. \[\begin{aligned}\vdash :\beta \in ^{1}\text{N}_{0}\text{c}ʻ\alpha . &\equiv .\beta \in \text{Nc}ʻ\alpha .\beta \in tʻ^{1}t_{0}ʻ\alpha .\\ &\equiv .\beta \text{ sm } \alpha .\beta \in tʻtʻ(tʻ\alpha \uparrow t_{0}ʻ\alpha ).\\ &\equiv .\beta \text{ sm } \alpha .\beta \subset tʻ(tʻ\alpha \uparrow t_{0}ʻ\alpha )\end{aligned}\] -/
theorem pm106_121 {α : Type*} {A : Set α} {B : Set (Set α → α → Prop)} :
    ((B ∈ n1₀c A ↔ B ∈ nc (Set α → α → Prop) A ∧ B ∈ typ (typ1₀ A)) ∧
        (B ∈ nc (Set α → α → Prop) A ∧ B ∈ typ (typ1₀ A) ↔
          sm B A ∧ B ∈ typ (typ (cross (typ A) (typ₀ A))))) ∧
      (sm B A ∧ B ∈ typ (typ (cross (typ A) (typ₀ A))) ↔
        sm B A ∧ B ⊆ typ (cross (typ A) (typ₀ A))) :=
  ⟨⟨Iff.rfl, ⟨fun h => ⟨h.1, mem_typ _ _⟩, fun h => ⟨h.1, mem_typ _ _⟩⟩⟩,
    ⟨fun h => ⟨h.1, sub_typ _ _⟩, fun h => ⟨h.1, mem_typ _ _⟩⟩⟩

/-- ✱106·13. \(\vdash :\mu \in \text{N}_{00}\text{C}.\equiv .(\exists \alpha ).\mu =\text{N}_{00}\text{c}ʻ\alpha \quad[*100·22.*71·41]\) -/
theorem pm106_13 {α : Type*} {μ : Set (Set (α → α → Prop))} :
    μ ∈ N₀₀C ↔ ∃ A, μ = n₀₀c A := Iff.rfl

/-- ✱106·14. \[\begin{aligned}\vdash :\beta \in \mu _{(00)}.&\equiv .(\exists \alpha ).\alpha \in \mu .\beta \text{ sm }\alpha .\beta \in tʻtʻ(t_{1}ʻ\mu \uparrow t_{1}ʻ\mu ).\\ &\equiv .(\exists \alpha ).\alpha \in \mu .\beta \text{ sm }\alpha .\beta \in tʻt_{00}ʻ\alpha .\\ &\equiv .(\exists \alpha ).\alpha \in \mu .\beta \text{ sm }\alpha .\beta \subset tʻ(\alpha \uparrow \alpha ) \quad[*64·33·11]\end{aligned}\] -/
theorem pm106_14 {α : Type*} {μ : Set (Set α)} {B : Set (α → α → Prop)} :
    ((B ∈ down00 μ ↔
          ∃ A, (A ∈ μ ∧ sm B A) ∧ B ∈ typ (typ (cross (typ₁ μ) (typ₁ μ)))) ∧
        ((∃ A, (A ∈ μ ∧ sm B A) ∧ B ∈ typ (typ (cross (typ₁ μ) (typ₁ μ)))) ↔
          ∃ A, (A ∈ μ ∧ sm B A) ∧ B ∈ typ (typ₀₀ A))) ∧
      ((∃ A, (A ∈ μ ∧ sm B A) ∧ B ∈ typ (typ₀₀ A)) ↔
        ∃ A, (A ∈ μ ∧ sm B A) ∧ B ⊆ typ (cross A A)) := by
  rw [down00_eq]
  exact ⟨⟨mem_img_iff_ex_true (fun _ => mem_typ _ _),
    ex_congr_true (fun _ => mem_typ _ _) (fun _ => mem_typ _ _)⟩,
    ex_congr_true (fun _ => mem_typ _ _) (fun _ => sub_typ _ _)⟩

/-- ✱106·141. \[\begin{aligned}\vdash :\beta \in \mu _{0}^{1}.&\equiv .(\exists \alpha ).\alpha \in \mu .\beta \text{ sm }\alpha .\beta \in tʻtʻ(t_{1}ʻ\mu \uparrow t_{0}ʻ\mu ).\\ &\equiv .(\exists \alpha ).\alpha \in \mu .\beta \text{ sm }\alpha .\beta \in tʻt_{0}^{1}ʻ\alpha .\\ &\equiv .(\exists \alpha ).\alpha \in \mu .\beta \text{ sm }\alpha .\beta \subset tʻ(\alpha \uparrow tʻ\alpha )\end{aligned}\]

`μ₀¹` is `down₀1 μ`, the analogue of ✱106·04 defined above.

**Status.** proved (reading): `μ₀¹` is not defined by PM except by "etc." (Summary of ✱106);
it is read as `sm''μ ∩ t't₀¹'t₁'μ`, the analogue of ✱106·04. -/
theorem pm106_141 {α : Type*} {μ : Set (Set α)} {B : Set (α → Set α → Prop)} :
    ((B ∈ down₀1 μ ↔
          ∃ A, (A ∈ μ ∧ sm B A) ∧ B ∈ typ (typ (cross (typ₁ μ) (typ₀ μ)))) ∧
        ((∃ A, (A ∈ μ ∧ sm B A) ∧ B ∈ typ (typ (cross (typ₁ μ) (typ₀ μ)))) ↔
          ∃ A, (A ∈ μ ∧ sm B A) ∧ B ∈ typ (typ₀1 A))) ∧
      ((∃ A, (A ∈ μ ∧ sm B A) ∧ B ∈ typ (typ₀1 A)) ↔
        ∃ A, (A ∈ μ ∧ sm B A) ∧ B ⊆ typ (cross A (typ A))) := by
  rw [down₀1_eq]
  exact ⟨⟨mem_img_iff_ex_true (fun _ => mem_typ _ _),
    ex_congr_true (fun _ => mem_typ _ _) (fun _ => mem_typ _ _)⟩,
    ex_congr_true (fun _ => mem_typ _ _) (fun _ => sub_typ _ _)⟩

/-- ✱106·2. \(\vdash :x\in t_{0}ʻ\alpha .\supset .\downarrow xʻʻ\alpha \in \text{N}_{00}\text{c}ʻ\alpha .\downarrow xʻʻ\alpha \in \text{N}_{0}\text{c}ʻ\downarrow xʻʻ\alpha\)

`↓x''α` is `coupleR x ʻʻ A`. -/
theorem pm106_2 {α : Type*} {A : Set α} {x : α} :
    x ∈ typ₀ A → coupleR x ʻʻ A ∈ n₀₀c A ∧ coupleR x ʻʻ A ∈ n₀c (coupleR x ʻʻ A) := by
  intro _
  refine ⟨?_, self_mem_n₀c _⟩
  rw [n₀₀c_eq]
  exact pm100_621

/-- ✱106·201. \(\vdash :\beta \in tʻ\alpha .\supset .\downarrow \beta ʻʻ\alpha \in \text{N}_{0}^{1}\text{c}ʻ\alpha \) -/
theorem pm106_201 {α : Type*} {A B : Set α} : B ∈ typ A → coupleR B ʻʻ A ∈ n₀1c A := by
  intro _
  rw [n₀1c_eq]
  exact pm100_621

/-- ✱106·202. \(\vdash :\beta \in t^{2}ʻ\alpha .\supset .\downarrow \beta ʻʻ\alpha \in \text{N}_{0}^{2}\text{c}ʻ\alpha\)

`N₀²c'α` is `n₀2c A`, the analogue ("Df etc.") defined above.

**Status.** proved (reading): `N₀²c` is not defined by PM except by "Df etc."; it is read as
`Nc'α ∩ t't₀²'α` with `t₀²'α = t'(t₀'α ↑ t²'α)`, by analogy with ✱106·02. -/
theorem pm106_202 {α : Type*} {A : Set α} {B : Set (Set α)} :
    B ∈ typ2 A → coupleR B ʻʻ A ∈ n₀2c A := by
  intro _
  rw [n₀2c_eq]
  exact pm100_621

/-- ✱106·203. \(\vdash .\downarrow \alpha ʻʻ\alpha \in \text{N}_{0}^{1}\text{c}ʻ\alpha \quad[*106·201]\) -/
theorem pm106_203 {α : Type*} {A : Set α} : coupleR A ʻʻ A ∈ n₀1c A := pm106_201 (mem_typ _ _)

/-- ✱106·204. \(\vdash .\downarrow (\iotaʻʻ\alpha )ʻʻ\alpha \in \text{N}_{0}^{2}\text{c}ʻ\alpha \quad[*106·202]\)

**Status.** proved (reading): `N₀²c` is the analogue ("Df etc.") of ✱106·02, as in ✱106·202. -/
theorem pm106_204 {α : Type*} {A : Set α} : coupleR (iota ʻʻ A) ʻʻ A ∈ n₀2c A :=
  pm106_202 (mem_typ _ _)

/-- ✱106·21. \(\vdash .\exists !\text{N}_{00}\text{c}ʻ\alpha .\text{N}_{00}\text{c}ʻ\alpha \in \text{N}_{0}\text{C} \quad[*106·2.*63·18]\)

No hypothesis `∃!α` is needed: for `α = Λ`, `Λ ∈ N₀₀c'α`; otherwise `x ↓ x` (`x ∈ α`) gives a
member (PM's proof uses `∃!t₀'α`, ✱63·18). -/
theorem pm106_21 {α : Type*} {A : Set α} : (n₀₀c A).Nonempty ∧ n₀₀c A ∈ N₀C := by
  have h : graph (fun a : α => a ↓ a) ʻʻ A ∈ n₀₀c A := by
    rw [n₀₀c_eq]
    exact sm_graph_img fun a _ b _ h => (couple_eq_couple_iff.1 h).1
  refine ⟨⟨_, h⟩, ?_⟩
  rw [n₀₀c_eq] at h ⊢
  exact nc_mem_N₀C ⟨_, h⟩

/-- ✱106·211. \(\vdash .\Lambda {\sim}\in \text{N}_{00}\text{C}.\text{N}_{00}\text{C}\subset \text{N}_{0}\text{C}.\text{N}_{00}\text{C}\in \text{Cls ex}^{2}\,\text{excl} \quad[*106·21.*103·24]\) -/
theorem pm106_211 {α : Type*} :
    ((Λ : Set (Set (α → α → Prop))) ∉ N₀₀C ∧ (N₀₀C : Set (Set (Set (α → α → Prop)))) ⊆ N₀C) ∧
      (N₀₀C : Set (Set (Set (α → α → Prop)))) ∈ ClsEx2excl := by
  have hsub : (N₀₀C : Set (Set (Set (α → α → Prop)))) ⊆ N₀C := by
    rintro μ ⟨A, rfl⟩
    exact pm106_21.2
  exact ⟨⟨fun h => pm103_23 (hsub h), hsub⟩, clsEx2excl_of_sub hsub⟩

/-- ✱106·212. \(\vdash .\Lambda {\sim}\in \text{N}_{0}^{1}\text{C}.\text{N}_{0}^{1}\text{C}\subset \text{N}_{0}\text{C}.\text{N}_{0}^{1}\text{C}\in \text{Cls ex}^{2}\,\text{excl} \quad[*106·203]\)

`N₀¹C` is `N₀1C = D'N₀¹c`, the analogue ("Df etc.") of ✱106·03 defined above.

**Status.** proved (reading): `N₀¹C` is not defined by PM except by "Df etc."; it is read as
`D'N₀¹c`, by analogy with ✱106·03. -/
theorem pm106_212 {α : Type*} :
    ((Λ : Set (Set (α → Set α → Prop))) ∉ N₀1C ∧
        (N₀1C : Set (Set (Set (α → Set α → Prop)))) ⊆ N₀C) ∧
      (N₀1C : Set (Set (Set (α → Set α → Prop)))) ∈ ClsEx2excl := by
  have hsub : (N₀1C : Set (Set (Set (α → Set α → Prop)))) ⊆ N₀C := by
    rintro μ ⟨A, rfl⟩
    have h := pm106_203 (A := A)
    rw [n₀1c_eq] at h ⊢
    exact nc_mem_N₀C ⟨_, h⟩
  exact ⟨⟨fun h => pm103_23 (hsub h), hsub⟩, clsEx2excl_of_sub hsub⟩

/-- ✱106·213. \(\vdash .\Lambda {\sim}\in \text{N}_{0}^{2}\text{C}.\text{N}_{0}^{2}\text{C}\subset \text{N}_{0}\text{C}.\text{N}_{0}^{2}\text{C}\in \text{Cls ex}^{2}\,\text{excl} \quad[*106·204]\)

**Status.** proved (reading): `N₀²C` is not defined by PM except by "Df etc."; it is read as
`D'N₀²c` (`N₀2C`), by analogy with ✱106·03. -/
theorem pm106_213 {α : Type*} :
    ((Λ : Set (Set (α → Set (Set α) → Prop))) ∉ N₀2C ∧
        (N₀2C : Set (Set (Set (α → Set (Set α) → Prop)))) ⊆ N₀C) ∧
      (N₀2C : Set (Set (Set (α → Set (Set α) → Prop)))) ∈ ClsEx2excl := by
  have hsub : (N₀2C : Set (Set (Set (α → Set (Set α) → Prop)))) ⊆ N₀C := by
    rintro μ ⟨A, rfl⟩
    have h := pm106_204 (A := A)
    rw [n₀2c_eq] at h ⊢
    exact nc_mem_N₀C ⟨_, h⟩
  exact ⟨⟨fun h => pm103_23 (hsub h), hsub⟩, clsEx2excl_of_sub hsub⟩

/-- ✱106·22. \(\vdash :\lambda \in \text{N}_{0}^{1}\text{c}ʻ\alpha .\equiv .\text{Cnv}ʻʻ\lambda \in ^{1}\text{N}_{0}\text{c}ʻ\alpha\)

`λ` is `L`; `Cnv''λ` is `Cnv ʻʻ L`. -/
theorem pm106_22 {α : Type*} {A : Set α} {L : Set (α → Set α → Prop)} :
    L ∈ n₀1c A ↔ Cnv ʻʻ L ∈ n1₀c A := by
  rw [n₀1c_eq, n1₀c_eq]
  exact ⟨fun h => sm_trans (sm_Cnv_img L) h, fun h => sm_trans (sm_symm (sm_Cnv_img L)) h⟩

/-- ✱106·221. \(\vdash :\lambda \in \text{N}_{0}^{2}\text{c}ʻ\alpha .\equiv .\text{Cnv}ʻʻ\lambda \in ^{2}\text{N}_{0}\text{c}ʻ\alpha\)

**Status.** proved (reading): `N₀²c` and `²N₀c` are not defined by PM except by "Df etc."; they
are read as `Nc'α ∩ t't₀²'α` and `Nc'α ∩ t'²t₀'α`, by analogy with ✱106·02·021. -/
theorem pm106_221 {α : Type*} {A : Set α} {L : Set (α → Set (Set α) → Prop)} :
    L ∈ n₀2c A ↔ Cnv ʻʻ L ∈ n2₀c A := by
  rw [n₀2c_eq, n2₀c_eq]
  exact ⟨fun h => sm_trans (sm_Cnv_img L) h, fun h => sm_trans (sm_symm (sm_Cnv_img L)) h⟩

/-- ✱106·222. \(\vdash .\Lambda {\sim}\in ^{1}\text{N}_{0}\text{C}.^{1}\text{N}_{0}\text{C}\subset \text{N}_{0}\text{C}.^{1}\text{N}_{0}\text{C}\in \text{Cls ex}^{2}\,\text{excl} \quad[*106·22·212]\)

**Status.** proved (reading): `¹N₀C` is not defined by PM except by "Df etc."; it is read as
`D'¹N₀c` (`N1₀C`), by analogy with ✱106·03. -/
theorem pm106_222 {α : Type*} :
    ((Λ : Set (Set (Set α → α → Prop))) ∉ N1₀C ∧
        (N1₀C : Set (Set (Set (Set α → α → Prop)))) ⊆ N₀C) ∧
      (N1₀C : Set (Set (Set (Set α → α → Prop)))) ∈ ClsEx2excl := by
  have hsub : (N1₀C : Set (Set (Set (Set α → α → Prop)))) ⊆ N₀C := by
    rintro μ ⟨A, rfl⟩
    have h := pm106_22.1 (pm106_203 (A := A))
    rw [n1₀c_eq] at h ⊢
    exact nc_mem_N₀C ⟨_, h⟩
  exact ⟨⟨fun h => pm103_23 (hsub h), hsub⟩, clsEx2excl_of_sub hsub⟩

/-- ✱106·223. \(\vdash .\Lambda {\sim}\in ^{2}\text{N}_{0}\text{C}.^{2}\text{N}_{0}\text{C}\subset \text{N}_{0}\text{C}.^{2}\text{N}_{0}\text{C}\in \text{Cls ex}^{2}\,\text{excl}\)

**Status.** proved (reading): `²N₀C` is not defined by PM except by "Df etc."; it is read as
`D'²N₀c` (`N2₀C`), by analogy with ✱106·03. -/
theorem pm106_223 {α : Type*} :
    ((Λ : Set (Set (Set (Set α) → α → Prop))) ∉ N2₀C ∧
        (N2₀C : Set (Set (Set (Set (Set α) → α → Prop)))) ⊆ N₀C) ∧
      (N2₀C : Set (Set (Set (Set (Set α) → α → Prop)))) ∈ ClsEx2excl := by
  have hsub : (N2₀C : Set (Set (Set (Set (Set α) → α → Prop)))) ⊆ N₀C := by
    rintro μ ⟨A, rfl⟩
    have h := pm106_221.1 (pm106_204 (A := A))
    rw [n2₀c_eq] at h ⊢
    exact nc_mem_N₀C ⟨_, h⟩
  exact ⟨⟨fun h => pm103_23 (hsub h), hsub⟩, clsEx2excl_of_sub hsub⟩

/-- ✱106·23. \(\vdash :\beta \in \text{N}^{1}\text{c}ʻ\alpha .\supset .\text{N}^{11}\text{c}ʻ\alpha =\text{N}_{00}\text{c}ʻ\beta\) -/
theorem pm106_23 {α : Type*} {A : Set α} {B : Set (Set α)} : B ∈ n1c A → n11c A = n₀₀c B := by
  rw [n1c_eq, n11c_eq, n₀₀c_eq]
  exact fun h => nc_eq_nc_of_sm (sm_symm h)

/-- ✱106·231. \(\vdash :\beta \in \text{N}_{1}\text{c}ʻ\alpha .\supset .\text{N}_{11}\text{c}ʻ\alpha =\text{N}_{00}\text{c}ʻ\beta \quad[\text{Proof as in}\, *106·23]\)

`N₁₁c` is `n₁₁c`, the analogue ("Proof as in ✱106·23") defined above.

**Status.** proved (reading): `N₁₁c` is not defined by PM except by analogy; it is read as
`Nc'α ∩ t't₁₁'α`, by analogy with ✱106·01. -/
theorem pm106_231 {α : Type*} {A : Set (Set α)} {B : Set α} :
    B ∈ n₁c A → n₁₁c A = n₀₀c B := by
  rw [n₁c_eq, n₁₁c_eq, n₀₀c_eq]
  exact fun h => nc_eq_nc_of_sm (sm_symm h)

/-- ✱106·24. \(\vdash :\text{N}^{1}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta .\supset .\text{N}^{11}\text{c}ʻ\alpha =\text{N}_{00}\text{c}ʻ\beta \quad[*106·23]\) -/
theorem pm106_24 {α : Type*} {A : Set α} {B : Set (Set α)} :
    n1c A = n₀c B → n11c A = n₀₀c B :=
  fun h => pm106_23 (h ▸ self_mem_n₀c B)

/-- ✱106·241. \(\vdash :\text{N}_{1}\text{c}ʻ\alpha =\text{N}_{0}\text{c}ʻ\beta .\supset .\text{N}_{11}\text{c}ʻ\alpha =\text{N}_{00}\text{c}ʻ\beta\)

**Status.** proved (reading): `N₁₁c` is the analogue of ✱106·01 defined above (as in ✱106·231). -/
theorem pm106_241 {α : Type*} {A : Set (Set α)} {B : Set α} :
    n₁c A = n₀c B → n₁₁c A = n₀₀c B :=
  fun h => pm106_231 (h ▸ self_mem_n₀c B)

/-- ✱106·25. \(\vdash .\text{N}^{11}\text{c}ʻ\alpha =\text{N}_{00}\text{c}ʻ\iotaʻʻ\alpha \quad[*106·23.*104·2]\) -/
theorem pm106_25 {α : Type*} {A : Set α} : n11c A = n₀₀c (iota ʻʻ A) := pm106_23 pm104_2

/-- ✱106·251. \(\vdash .\text{N}_{00}\text{c}ʻ\alpha =\text{N}_{11}\text{c}ʻ\iotaʻʻ\alpha\)

**Status.** proved (reading): `N₁₁c` is the analogue of ✱106·01 defined above (as in ✱106·231). -/
theorem pm106_251 {α : Type*} {A : Set α} : n₀₀c A = n₁₁c (iota ʻʻ A) := by
  refine (pm106_231 ?_).symm
  rw [n₁c_eq]
  exact sm_symm (sm_iota_img A)

/-- ✱106·31. \[\begin{aligned}\vdash :x,y\in t_{0}ʻ\alpha .t_{0}ʻ\alpha &=t_{0}ʻ\beta .x\neq y.\supset .\\ &\downarrow xʻʻ\alpha \in \text{N}_{00}\text{c}ʻ\alpha .\downarrow yʻʻ\beta \in \text{N}_{00}\text{c}ʻ\beta .\downarrow xʻʻ\alpha \cap \downarrow xʻʻ\beta =\Lambda \\ \quad[*106·2.*55·233]\end{aligned}\]

`x, y ∈ t₀'α` is `x ∈ t₀'α . y ∈ t₀'α`.

**Status.** proved (corrected): the e-text prints the last conjunct as `↓x''α ∩ ↓x''β = Λ`,
which is false (`pm106_31_printed_false`: `α = β = ι'x`); PM's reference to ✱55·233
(`x ≠ y . ⊃ . ↓x''α ∩ ↓y''β = Λ`) and the second conjunct `↓y''β ∈ N₀₀c'β` show that
`↓x''α ∩ ↓y''β = Λ` is meant. -/
theorem pm106_31 {α : Type*} {A B : Set α} {x y : α} :
    ((x ∈ typ₀ A ∧ y ∈ typ₀ A) ∧ typ₀ A = typ₀ B) ∧ x ≠ y →
      (coupleR x ʻʻ A ∈ n₀₀c A ∧ coupleR y ʻʻ B ∈ n₀₀c B) ∧
        coupleR x ʻʻ A ∩ coupleR y ʻʻ B = Λ := by
  rintro ⟨⟨⟨hx, -⟩, -⟩, hxy⟩
  refine ⟨⟨(pm106_2 hx).1, (pm106_2 (mem_typ₀ B y)).1⟩, ?_⟩
  rw [Null_eq_empty]
  refine Set.eq_empty_iff_forall_notMem.2 fun R hR => ?_
  obtain ⟨⟨u, -, hu⟩, ⟨v, -, hv⟩⟩ := hR
  have e : u ↓ x = v ↓ y := ((coupleR_apply x R u).1 hu).symm.trans ((coupleR_apply y R v).1 hv)
  exact hxy (couple_eq_couple_iff.1 e).2

/-- The printed form of ✱106·31 (with `↓x''α ∩ ↓x''β = Λ`) is false. -/
theorem pm106_31_printed_false : ¬ ∀ {A B : Set Bool} {x y : Bool},
    ((x ∈ typ₀ A ∧ y ∈ typ₀ A) ∧ typ₀ A = typ₀ B) ∧ x ≠ y →
      (coupleR x ʻʻ A ∈ n₀₀c A ∧ coupleR y ʻʻ B ∈ n₀₀c B) ∧
        coupleR x ʻʻ A ∩ coupleR x ʻʻ B = Λ := by
  intro h
  have h1 := (@h {true} {true} true false
    ⟨⟨⟨mem_typ₀ _ _, mem_typ₀ _ _⟩, rfl⟩, Bool.true_eq_false.mp⟩).2
  have hm : (true ↓ true : Bool → Bool → Prop) ∈
      coupleR true ʻʻ ({true} : Set Bool) ∩ coupleR true ʻʻ ({true} : Set Bool) :=
    ⟨⟨true, rfl, rfl⟩, ⟨true, rfl, rfl⟩⟩
  rw [h1, Null_eq_empty] at hm
  exact hm

/-- ✱106·311. \[\begin{aligned}\vdash \colon\ldotp x\in t_{0}ʻ\alpha .t_{0}ʻ\alpha &=t_{0}ʻ\beta :\alpha =\Lambda .\lor.\beta =\Lambda :\supset .\\ &\downarrow xʻʻ\alpha \in \text{N}_{00}\text{c}ʻ\alpha .\downarrow xʻʻ\beta \in \text{N}_{00}\text{c}ʻ\beta .\downarrow xʻʻ\alpha \cap \downarrow xʻʻ\beta =\Lambda \\ \quad[*106·2.*55·232.\text{Transp}]\end{aligned}\] -/
theorem pm106_311 {α : Type*} {A B : Set α} {x : α} :
    (x ∈ typ₀ A ∧ typ₀ A = typ₀ B) ∧ (A = Λ ∨ B = Λ) →
      (coupleR x ʻʻ A ∈ n₀₀c A ∧ coupleR x ʻʻ B ∈ n₀₀c B) ∧
        coupleR x ʻʻ A ∩ coupleR x ʻʻ B = Λ := by
  rintro ⟨⟨hx, -⟩, h⟩
  refine ⟨⟨(pm106_2 hx).1, (pm106_2 (mem_typ₀ B x)).1⟩, ?_⟩
  rw [show (Λ : Set (α → α → Prop)) = ∅ from Null_eq_empty]
  rcases h with h | h
  · rw [Null_eq_empty] at h
    rw [h]
    exact Set.eq_empty_iff_forall_notMem.2 fun R ⟨⟨_, hu, _⟩, _⟩ => hu
  · rw [Null_eq_empty] at h
    rw [h]
    exact Set.eq_empty_iff_forall_notMem.2 fun R ⟨_, ⟨_, hu, _⟩⟩ => hu

/-- ✱106·312. \[\begin{aligned}\vdash :&t_{0}ʻ\alpha =\iota ʻx.\alpha =\beta =\iota ʻx.\supset .\\ &\iota ʻ(\iota ʻx\uparrow \iota ʻx)\in \text{N}_{00}\text{c}ʻ\alpha .\iota ʻ(\Lambda \uparrow \iota ʻx)\in \text{N}_{00}\text{c}ʻ\beta .\iota ʻ(\iota ʻx\uparrow \iota ʻx)\cap \iota ʻ(\Lambda \uparrow \iota ʻx)=\Lambda \end{aligned}\]

`α = β = ι'x` is the conjunction of its two links; `ι'x ↑ ι'x` and `Λ ↑ ι'x` are
`cross (ι x) (ι x)` and `cross Λ (ι x)`. -/
theorem pm106_312 {α : Type*} {A B : Set α} {x : α} :
    typ₀ A = ι x ∧ (A = B ∧ B = ι x) →
      (ι (cross (ι x) (ι x)) ∈ n₀₀c A ∧ ι (cross Λ (ι x)) ∈ n₀₀c B) ∧
        ι (cross (ι x) (ι x)) ∩ ι (cross Λ (ι x)) = Λ := by
  rintro ⟨-, hAB, rfl⟩
  subst hAB
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [n₀₀c_eq]; exact sm_unit_iff.2 ⟨_, rfl⟩
  · rw [n₀₀c_eq]; exact sm_unit_iff.2 ⟨_, rfl⟩
  · rw [show (Λ : Set (α → α → Prop)) = ∅ from Null_eq_empty]
    refine Set.eq_empty_iff_forall_notMem.2 fun R ⟨h1, h2⟩ => ?_
    have e : cross (ι x) (ι x) = cross Λ (ι x) :=
      (mem_unitCls.1 h1).symm.trans (mem_unitCls.1 h2)
    have : cross (ι x) (ι x) x x := ⟨rfl, rfl⟩
    rw [e] at this
    have h3 : x ∈ (Λ : Set α) := this.1
    rw [Null_eq_empty] at h3
    exact h3

/-- ✱106·32. \(\vdash :t_{0}ʻ\alpha =t_{0}ʻ\beta .\supset .(\exists \gamma ,\delta ).\gamma \in \text{N}_{00}\text{c}ʻ\alpha .\delta \in \text{N}_{00}\text{c}ʻ\beta .\gamma \cap \delta =\Lambda\)

PM's proof treats three cases (✱106·31·311·312); the proof here follows it. -/
theorem pm106_32 {α : Type*} {A B : Set α} :
    typ₀ A = typ₀ B → ∃ G E, (G ∈ n₀₀c A ∧ E ∈ n₀₀c B) ∧ G ∩ E = Λ := by
  intro hAB
  by_cases h2 : ∃ x y : α, x ≠ y
  · obtain ⟨x, y, hxy⟩ := h2
    exact ⟨_, _, pm106_31 ⟨⟨⟨mem_typ₀ _ _, mem_typ₀ _ _⟩, hAB⟩, hxy⟩⟩
  · push Not at h2
    by_cases hA : A = Λ ∨ B = Λ
    · by_cases hx : Nonempty α
      · obtain ⟨x⟩ := hx
        exact ⟨_, _, pm106_311 (x := x) ⟨⟨mem_typ₀ _ _, hAB⟩, hA⟩⟩
      · have hA' : A = ∅ := Set.eq_empty_of_forall_notMem fun a _ => hx ⟨a⟩
        have hB' : B = ∅ := Set.eq_empty_of_forall_notMem fun a _ => hx ⟨a⟩
        refine ⟨∅, ∅, ⟨?_, ?_⟩, by rw [Set.inter_self, Null_eq_empty]⟩
        · rw [hA', n₀₀c_eq]; exact sm_empty_iff.2 rfl
        · rw [hB', n₀₀c_eq]; exact sm_empty_iff.2 rfl
    · push Not at hA
      obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 (by rw [← Null_eq_empty]; exact hA.1)
      have huniv : ∀ C : Set α, C ≠ Λ → C = ι a := by
        intro C hC
        obtain ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.2 (by rw [← Null_eq_empty]; exact hC)
        ext z
        constructor
        · intro _; exact mem_unitCls.2 (h2 z a)
        · intro hz; rw [mem_unitCls.1 hz, h2 a c]; exact hc
      have htyp : typ₀ A = ι a := by
        rw [typ₀_eq_univ]
        exact (Set.eq_univ_of_forall fun z => mem_unitCls.2 (h2 z a)).symm
      exact ⟨_, _, pm106_312 (x := a)
        ⟨htyp, (huniv A hA.1).trans (huniv B hA.2).symm, huniv B hA.2⟩⟩

/-- ✱106·4. \(\vdash :\mu =\text{N}_{0}\text{c}ʻ\alpha .\supset .\mu _{(00)}=\text{N}_{00}\text{c}ʻ\alpha\) -/
theorem pm106_4 {α : Type*} {A : Set α} {μ : Set (Set α)} :
    μ = n₀c A → down00 μ = n₀₀c A := by
  rintro rfl
  rw [down00_eq, sm_img_n₀c, n₀₀c_eq]

/-- ✱106·401. \(\vdash :\mu =\text{N}^{1}\text{c}ʻ\alpha .\supset .\mu _{(00)}=\text{N}^{11}\text{c}ʻ\alpha\) -/
theorem pm106_401 {α : Type*} {A : Set α} {μ : Set (Set (Set α))} :
    μ = n1c A → down00 μ = n11c A := by
  rintro rfl
  rw [down00_eq, n1c_eq, n11c_eq]
  exact pm100_511 ⟨_, sm_iota_img A⟩

/-- ✱106·402. \(\vdash :\mu =\text{N}_{1}\text{c}ʻ\alpha .\exists !\mu .\supset .\mu _{(00)}=\text{N}_{11}\text{c}ʻ\alpha\)

**Status.** proved (reading): `N₁₁c` is the analogue of ✱106·01 defined above (as in ✱106·231). -/
theorem pm106_402 {α : Type*} {A : Set (Set α)} {μ : Set (Set α)} :
    μ = n₁c A ∧ μ.Nonempty → down00 μ = n₁₁c A := by
  rintro ⟨rfl, B, hB⟩
  rw [n₁c_eq] at hB
  rw [down00_eq, n₁c_eq, n₁₁c_eq]
  exact pm100_511 ⟨B, hB⟩

/-- ✱106·41. \(\vdash :\mu =\text{N}_{0}\text{c}ʻ\alpha .\supset .\mu ^{(11)}=\text{N}^{11}\text{c}ʻ\alpha\) -/
theorem pm106_41 {α : Type*} {A : Set α} {μ : Set (Set α)} :
    μ = n₀c A → up11 μ = n11c A := by
  rintro rfl
  rw [up11_eq, sm_img_n₀c, n11c_eq]

/-- ✱106·411. \(\vdash :\mu =\text{N}_{0}\text{c}ʻ\alpha .\supset .\mu _{(11)}=\text{N}_{11}\text{c}ʻ\alpha \quad[\text{Proof as in}\, *106·41]\)

**Status.** proved (reading): `μ_{(11)}` and `N₁₁c` are the analogues of ✱106·04 and ✱106·01
defined above ("Proof as in ✱106·41"). -/
theorem pm106_411 {α : Type*} {A : Set (Set α)} {μ : Set (Set (Set α))} :
    μ = n₀c A → down11 μ = n₁₁c A := by
  rintro rfl
  rw [down11_eq, sm_img_n₀c, n₁₁c_eq]

/-- ✱106·43. \(\vdash :\mu ,\nu \in \text{N}_{0}\text{C}.tʻ\mu =tʻ\nu .\supset .(\exists \gamma ,\delta ).\gamma \in \mu _{(00)}.\delta \in \nu _{(00)}.\gamma \cap \delta =\Lambda\) -/
theorem pm106_43 {α : Type*} {μ ν : Set (Set α)} :
    (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ typ μ = typ ν →
      ∃ G E, (G ∈ down00 μ ∧ E ∈ down00 ν) ∧ G ∩ E = Λ := by
  rintro ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, -⟩
  rw [pm106_4 rfl, pm106_4 rfl]
  exact pm106_32 (typ₀_eq_typ₀ A B)

/-- ✱106·44. \(\vdash :\mu ,\nu \in \text{N}_{00}\text{C}.tʻ\mu =tʻ\nu .\supset .(\exists \gamma ,\delta ).\gamma \in \mu .\delta \in \nu .\gamma \cap \delta =\Lambda \quad[*106·32]\) -/
theorem pm106_44 {α : Type*} {μ ν : Set (Set (α → α → Prop))} :
    (μ ∈ N₀₀C ∧ ν ∈ N₀₀C) ∧ typ μ = typ ν → ∃ G E, (G ∈ μ ∧ E ∈ ν) ∧ G ∩ E = Λ := by
  rintro ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, -⟩
  exact pm106_32 (typ₀_eq_typ₀ A B)

/-- ✱106·5. \[\begin{aligned}\vdash :R\in \text{Cls}\rightarrow &1.\text{D}ʻR\subset \alpha .\text{ᗡ}ʻR\subset \text{ᗡ}ʻʻʻ(\alpha \uparrow \alpha ).\\ &W=\hat{x} \hat{y} \{x,y\in \alpha .{\sim}x(\breve{R} ʻx)y\}.\supset .W{\sim}\in \text{ᗡ}ʻR.W\unicode{x2abd} \alpha \uparrow \alpha\end{aligned}\]

`R` relates members of the type of `α` to relations between them; `R̆'x` is a description with
the smallest scope, `x(R̆'x)y` (Basic §5), so `∼x(R̆'x)y` is `¬ Desc R˘ x (fun S => S x y)`.

**Status.** proved (reading): transcription error: the e-text prints `ᗡ'''(α ↑ α)`, which is not
significant (`α ↑ α` is a relation, not a class of classes); PM's demonstration and ✱106·51
(`β sm Rl'(α ↑ α)`) show that `Rl'(α ↑ α)` is meant. -/
theorem pm106_5 {α : Type*} {A : Set α} {R : α → (α → α → Prop) → Prop}
    {W : α → α → Prop} :
    ((R ∈ arrow Cls one ∧ dom R ⊆ A) ∧ codom R ⊆ rl (cross A A)) ∧
        W = (fun x y => (x ∈ A ∧ y ∈ A) ∧ ¬ Desc R˘ x (fun S => S x y)) →
      W ∉ codom R ∧ W ⪽ cross A A := by
  rintro ⟨⟨⟨h1, h2⟩, -⟩, hW⟩
  have hmo := mem_arrow_Cls_one.1 h1
  constructor
  · rintro ⟨x, hx⟩
    have hxA : x ∈ A := h2 ⟨W, hx⟩
    have hd : Desc R˘ x (fun S => S x x) ↔ W x x :=
      TheIs_iff_of_unique (fun S => ⟨fun h => hmo x S W ⟨h, hx⟩, fun e => by rw [e]; exact hx⟩)
    have hWx : W x x ↔ (x ∈ A ∧ x ∈ A) ∧ ¬ Desc R˘ x (fun S => S x x) := by rw [hW]
    by_cases h : W x x
    · exact (hWx.1 h).2 (hd.2 h)
    · exact h (hWx.2 ⟨⟨hxA, hxA⟩, fun hd' => h (hd.1 hd')⟩)
  · intro x y h
    rw [hW] at h
    exact h.1

/-- ✱106·51. \(\vdash :\beta \subset \alpha .\supset .{\sim}\{\beta \text{ sm }\text{Rl}ʻ(\alpha \uparrow \alpha )\}\)

`Rl'(α ↑ α)` is `rl (cross A A)`. -/
theorem pm106_51 {α : Type*} {A B : Set α} : B ⊆ A → ¬ sm B (rl (cross A A)) := by
  intro hBA hs
  obtain ⟨R, ⟨hR, hdom⟩, hcod⟩ := sm_iff.1 hs
  have h := pm106_5 (R := R) (A := A)
    (W := fun x y => (x ∈ A ∧ y ∈ A) ∧ ¬ Desc R˘ x (fun S => S x y))
    ⟨⟨⟨mem_arrow_Cls_one.2 (mem_arrow_one_one.1 hR).2, by rw [← hdom]; exact hBA⟩,
      hcod.symm.subset⟩, rfl⟩
  apply h.1
  rw [← hcod]
  exact h.2

/-- ✱106·52. \(\vdash :\beta \subset t_{0}ʻ\alpha .\supset .\beta {\sim}\in \text{Nc}ʻt_{00}ʻ\alpha\)

`β ∈ Nc't₀₀'α` is attributive (in the type of `β`). -/
theorem pm106_52 {α : Type*} {A B : Set α} : B ⊆ typ₀ A → B ∉ nc α (typ₀₀ A) := by
  intro h hB
  have e : typ₀₀ A = rl (cross (typ₀ A) (typ₀ A)) := by
    rw [typ₀₀, typ_eq_univ]
    exact (Set.eq_univ_of_forall fun R x y _ => ⟨mem_typ₀ _ _, mem_typ₀ _ _⟩).symm
  rw [e] at hB
  exact pm106_51 h hB

/-- ✱106·53. \(\vdash .\text{Nc}(\alpha )ʻt_{00}ʻ\alpha =\Lambda \quad[*106·52.*102·6.*63·371]\) -/
theorem pm106_53 {α : Type*} {A : Set α} : Desc (relT2 Nc A) (typ₀₀ A) (fun μ => μ = Λ) := by
  rw [desc_relT2_Nc', Null_eq_empty]
  exact Set.eq_empty_iff_forall_notMem.2 fun B hB => pm106_52 (sub_typ₀ A B) hB

/-- ✱106·54. \(\vdash .\text{N}_{0}\text{c}ʻt_{00}ʻ\alpha {\sim}\in \text{N}_{00}\text{C}\) -/
theorem pm106_54 {α : Type*} {A : Set α} : n₀c (typ₀₀ A) ∉ N₀₀C := by
  rintro ⟨B, hB⟩
  have h1 : typ₀₀ A ∈ n₀₀c B := by rw [← hB]; exact self_mem_n₀c _
  rw [n₀₀c_eq] at h1
  exact pm106_52 (sub_typ₀ A B) (sm_symm h1)

/-- ✱106·55. \(\vdash .\exists !\text{N}_{0}\text{C}-\text{N}_{00}\text{C} \quad[*106·54]\) -/
theorem pm106_55 {α : Type*} : ((N₀C : Set (Set (Set (α → α → Prop)))) \ N₀₀C).Nonempty :=
  ⟨n₀c (typ₀₀ (∅ : Set α)), ⟨_, rfl⟩, pm106_54⟩

end PrincipiaMathematica
