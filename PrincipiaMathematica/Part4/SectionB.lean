import PrincipiaMathematica.Defs.Part4

/-!
# Part IV, Section B: Addition of relations, and the product of two relations

Volume 2. Numbers: ✱160, ✱161, ✱162, ✱163, ✱164, ✱165, ✱166.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

/-! ### Helper lemmas for ✱160–✱166 (not propositions of PM) -/

/-- `x(S;Q)y` unfolded, with the product flattened. -/
private theorem semi_iff' {α β : Type*} (S : α → β → Prop) (Q : β → β → Prop) (x y : α) :
    (S ⁏ Q) x y ↔ ∃ z w, S x z ∧ S y w ∧ Q z w := by
  rw [semi_apply]; simp only [and_assoc]

/-- Unfold the relations and classes of Section B to first-order logic. -/
local macro "bsimp" : tactic => `(tactic| simp only [semi_iff', rcup, rcap, rdiff, rneg, cres,
  dres, bres, fres, couple_apply, cross, mem_unitCls, refs, rels, img, dom, codom, fld,
  Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff, RSub,
  relProd, sumRel, sumCls, Null_eq_empty, Set.mem_empty_iff_false, mem_rl, rNull, rV,
  Set.subset_def, rel_eq_iff, Set.ext_iff, Set.Nonempty, D, Dcnv, C, F, graph, eq_iff_iff, ne_eq,
  I, not_exists, mem_arrow_Cls_one, mem_arrow_one_Cls, mem_arrow_one_one, cnv, exists_imp,
  and_imp, rEx, rsum, addLast, addFirst, relSigma, Beg, Set.mem_univ, true_and, and_true,
  smorbar, rtimes, coupleSemi, opSemi, opL, opR, coupleR, coupleL, daggerRel, daggerOp,
  Rel2excl, V_eq_univ] at *)

section Helpers

variable {α β γ δ : Type*}

private theorem rel_ext' {R S : α → β → Prop} (h : ∀ x y, R x y ↔ S x y) : R = S :=
  funext fun x => funext fun y => propext (h x y)

private theorem mem_fld_l {R : α → α → Prop} {x y : α} (h : R x y) : x ∈ fld R := ⟨y, Or.inl h⟩

private theorem mem_fld_r {R : α → α → Prop} {x y : α} (h : R x y) : y ∈ fld R := ⟨x, Or.inr h⟩

private theorem fld_cnv' (P : α → α → Prop) : fld P˘ = fld P := by
  ext x
  constructor <;> rintro ⟨y, h | h⟩
  exacts [⟨y, Or.inr h⟩, ⟨y, Or.inl h⟩, ⟨y, Or.inr h⟩, ⟨y, Or.inl h⟩]

private theorem fld_rcup (P Q : α → α → Prop) : fld (P ⊍ Q) = fld P ∪ fld Q := by
  ext x
  constructor
  · rintro ⟨y, (h | h) | (h | h)⟩
    exacts [Or.inl ⟨y, Or.inl h⟩, Or.inr ⟨y, Or.inl h⟩, Or.inl ⟨y, Or.inr h⟩,
      Or.inr ⟨y, Or.inr h⟩]
  · rintro (⟨y, h | h⟩ | ⟨y, h | h⟩)
    exacts [⟨y, Or.inl (Or.inl h)⟩, ⟨y, Or.inr (Or.inl h)⟩, ⟨y, Or.inl (Or.inr h)⟩,
      ⟨y, Or.inr (Or.inr h)⟩]

private theorem fld_cross_sub (A B : Set α) : fld (cross A B) ⊆ A ∪ B := by
  rintro x ⟨y, ⟨h, -⟩ | ⟨-, h⟩⟩
  exacts [Or.inl h, Or.inr h]

private theorem fld_cross {A B : Set α} (hA : A.Nonempty) (hB : B.Nonempty) :
    fld (cross A B) = A ∪ B := by
  refine Set.Subset.antisymm (fld_cross_sub A B) ?_
  rintro x (h | h)
  · obtain ⟨y, hy⟩ := hB; exact ⟨y, Or.inl ⟨h, hy⟩⟩
  · obtain ⟨y, hy⟩ := hA; exact ⟨y, Or.inr ⟨hy, h⟩⟩

private theorem rEx_iff_fld {P : α → α → Prop} : rEx P ↔ (fld P).Nonempty := by
  constructor
  · rintro ⟨x, y, h⟩; exact ⟨x, mem_fld_l h⟩
  · rintro ⟨x, y, h | h⟩
    exacts [⟨x, y, h⟩, ⟨y, x, h⟩]

private theorem eq_rNull_of_not_rEx {P : α → β → Prop} (h : ¬ rEx P) : P = rNull :=
  rel_ext' fun x y => ⟨fun hxy => absurd ⟨x, y, hxy⟩ h, fun hxy => absurd hxy (rNull_apply x y)⟩

private theorem fld_eq_empty_of_not_rEx {P : α → α → Prop} (h : ¬ rEx P) : fld P = ∅ := by
  rw [rEx_iff_fld, Set.not_nonempty_iff_eq_empty] at h; exact h

private theorem not_mem_of_disj {A B : Set α} (h : A ∩ B = Λ) {x : α} (hA : x ∈ A) : x ∉ B :=
  fun hB => by rw [Null_eq_empty] at h; exact (h ▸ (⟨hA, hB⟩ : x ∈ A ∩ B) : x ∈ (∅ : Set α))

private theorem cres_semi_of {S : α → β → Prop} {Q : β → β → Prop} {B : Set β}
    (h : fld Q ⊆ B) : (S ↾ B) ⁏ Q = S ⁏ Q := by
  refine rel_ext' fun x y => ?_
  rw [semi_iff', semi_iff']
  constructor
  · rintro ⟨z, w, ⟨h1, -⟩, ⟨h2, -⟩, h3⟩; exact ⟨z, w, h1, h2, h3⟩
  · rintro ⟨z, w, h1, h2, h3⟩
    exact ⟨z, w, ⟨h1, h (mem_fld_l h3)⟩, ⟨h2, h (mem_fld_r h3)⟩, h3⟩

private theorem codom_cres_eq {S : α → β → Prop} {B : Set β} : B = codom (S ↾ B) ↔ B ⊆ codom S := by
  constructor
  · intro h y hy
    rw [h] at hy
    obtain ⟨x, hx, -⟩ := hy
    exact ⟨x, hx⟩
  · intro h
    ext y
    constructor
    · intro hy; obtain ⟨x, hx⟩ := h hy; exact ⟨x, hx, hy⟩
    · rintro ⟨x, -, hy⟩; exact hy

private theorem fld_semi_sub (S : α → β → Prop) (Q : β → β → Prop) : fld (S ⁏ Q) ⊆ S ʻʻ fld Q := by
  rintro x ⟨y, h | h⟩
  · obtain ⟨z, w, h1, -, h3⟩ := (semi_iff' S Q x y).1 h; exact ⟨z, mem_fld_l h3, h1⟩
  · obtain ⟨z, w, -, h2, h3⟩ := (semi_iff' S Q y x).1 h; exact ⟨w, mem_fld_r h3, h2⟩

private theorem fld_semi_of {S : α → β → Prop} {Q : β → β → Prop} (h : fld Q ⊆ codom S) :
    fld (S ⁏ Q) = S ʻʻ fld Q := by
  refine Set.Subset.antisymm (fld_semi_sub S Q) ?_
  rintro x ⟨z, ⟨w, hzw | hwz⟩, hxz⟩
  · obtain ⟨y, hy⟩ := h (mem_fld_r hzw)
    exact mem_fld_l ((semi_iff' S Q x y).2 ⟨z, w, hxz, hy, hzw⟩)
  · obtain ⟨y, hy⟩ := h (mem_fld_l hwz)
    exact mem_fld_r ((semi_iff' S Q y x).2 ⟨w, z, hy, hxz, hwz⟩)

private theorem img_codom (S : α → β → Prop) : S ʻʻ codom S = dom S := by
  ext x
  constructor
  · rintro ⟨y, -, h⟩; exact ⟨y, h⟩
  · rintro ⟨y, h⟩; exact ⟨y, ⟨x, h⟩, h⟩

/-- A correlator of `P` with `Q` has domain `C'P` (✱151·131). -/
private theorem dom_of_smorbar {S : α → β → Prop} {P : α → α → Prop} {Q : β → β → Prop}
    (h : S ∈ smorbar P Q) : dom S = fld P := by
  obtain ⟨⟨-, hc⟩, rfl⟩ := h
  rw [fld_semi_of hc.le, hc, img_codom]

private theorem oneone_iff {S : α → β → Prop} :
    S ∈ arrow one one ↔ (∀ x y z, S x z ∧ S y z → x = y) ∧ (∀ x y z, S x y ∧ S x z → y = z) :=
  mem_arrow_one_one

/-- A union of two correlators with disjoint domains and disjoint converse domains is one-one. -/
private theorem oneone_rcup {S T : α → β → Prop} (hS : S ∈ arrow one one) (hT : T ∈ arrow one one)
    (hd : ∀ x y z, S x y → T x z → False) (hc : ∀ x y z, S x z → T y z → False) :
    S ⊍ T ∈ arrow one one := by
  rw [oneone_iff] at *
  refine ⟨?_, ?_⟩
  · rintro x y z ⟨h1 | h1, h2 | h2⟩
    · exact hS.1 x y z ⟨h1, h2⟩
    · exact (hc x y z h1 h2).elim
    · exact (hc y x z h2 h1).elim
    · exact hT.1 x y z ⟨h1, h2⟩
  · rintro x y z ⟨h1 | h1, h2 | h2⟩
    · exact hS.2 x y z ⟨h1, h2⟩
    · exact (hd x y z h1 h2).elim
    · exact (hd x z y h2 h1).elim
    · exact hT.2 x y z ⟨h1, h2⟩

private theorem codom_rcup (S T : α → β → Prop) : codom (S ⊍ T) = codom S ∪ codom T := by
  ext y
  constructor
  · rintro ⟨x, h | h⟩
    exacts [Or.inl ⟨x, h⟩, Or.inr ⟨x, h⟩]
  · rintro (⟨x, h⟩ | ⟨x, h⟩)
    exacts [⟨x, Or.inl h⟩, ⟨x, Or.inr h⟩]

/-- `(S ∪̇ T);P = S;P` when `C'P` and `ᗡ'T` are disjoint. -/
private theorem rcup_semi_left {S T : α → β → Prop} {P : β → β → Prop}
    (h : ∀ z, z ∈ fld P → z ∉ codom T) : (S ⊍ T) ⁏ P = S ⁏ P := by
  refine rel_ext' fun x y => ?_
  rw [semi_iff', semi_iff']
  constructor
  · rintro ⟨z, w, h1, h2, h3⟩
    refine ⟨z, w, ?_, ?_, h3⟩
    · rcases h1 with h1 | h1
      exacts [h1, absurd ⟨x, h1⟩ (h z (mem_fld_l h3))]
    · rcases h2 with h2 | h2
      exacts [h2, absurd ⟨y, h2⟩ (h w (mem_fld_r h3))]
  · rintro ⟨z, w, h1, h2, h3⟩; exact ⟨z, w, Or.inl h1, Or.inl h2, h3⟩

private theorem rcup_comm (S T : α → β → Prop) : S ⊍ T = T ⊍ S :=
  rel_ext' fun _ _ => or_comm

private theorem rcup_apply' (R S : α → β → Prop) (x : α) (y : β) : (R ⊍ S) x y ↔ R x y ∨ S x y :=
  Iff.rfl

private theorem cross_apply' (A : Set α) (B : Set β) (x : α) (y : β) :
    cross A B x y ↔ x ∈ A ∧ y ∈ B := Iff.rfl

private theorem rEx_cnv {P : α → β → Prop} (h : rEx P) : rEx P˘ := by
  obtain ⟨x, y, hxy⟩ := h; exact ⟨y, x, hxy⟩

private theorem fld_couple (x y : α) : fld (x ↓ y) = ι x ∪ ι y := by
  ext u
  constructor
  · rintro ⟨v, ⟨h, -⟩ | ⟨-, h⟩⟩
    exacts [Or.inl h, Or.inr h]
  · rintro (h | h)
    · exact ⟨y, Or.inl ⟨h, mem_unitCls.2 rfl⟩⟩
    · exact ⟨x, Or.inr ⟨mem_unitCls.2 rfl, h⟩⟩

private theorem codom_couple (x : α) (y : β) : codom (x ↓ y) = ι y := by
  ext u
  constructor
  · rintro ⟨a, -, h⟩; exact h
  · intro h; exact ⟨x, mem_unitCls.2 rfl, h⟩

private theorem couple_oneone (x : α) (y : β) : x ↓ y ∈ arrow one one := by
  rw [oneone_iff]
  refine ⟨fun a b c h => ?_, fun a b c h => ?_⟩
  · rw [couple_apply, couple_apply] at h; exact h.1.1.trans h.2.1.symm
  · rw [couple_apply, couple_apply] at h; exact h.1.2.trans h.2.2.symm

private theorem fld_addLast {P : α → α → Prop} (h : rEx P) (x : α) : fld (P ⇸ x) = fld P ∪ ι x := by
  rw [addLast, fld_rcup, fld_cross (rEx_iff_fld.1 h) ⟨x, mem_unitCls.2 rfl⟩, ← Set.union_assoc,
    Set.union_self]

private theorem fld_addFirst {P : α → α → Prop} (h : rEx P) (x : α) :
    fld (x ⇷ P) = fld P ∪ ι x := by
  rw [addFirst, fld_rcup, fld_cross ⟨x, mem_unitCls.2 rfl⟩ (rEx_iff_fld.1 h), Set.union_assoc,
    Set.union_self, Set.union_comm]

private theorem addLast_rNull (x : α) : (rNull : α → α → Prop) ⇸ x = rNull := by
  refine rel_ext' fun a b => ⟨fun h => ?_, fun h => absurd h (rNull_apply a b)⟩
  rcases h with h | ⟨⟨c, h | h⟩, -⟩ <;> exact absurd h (rNull_apply _ _)

private theorem addFirst_rNull (x : α) : x ⇷ (rNull : α → α → Prop) = rNull := by
  refine rel_ext' fun a b => ⟨fun h => ?_, fun h => absurd h (rNull_apply a b)⟩
  rcases h with ⟨-, ⟨c, h | h⟩⟩ | h <;> exact absurd h (rNull_apply _ _)

private theorem addLast_eq_rNull_iff {P : α → α → Prop} {x : α} : P ⇸ x = rNull ↔ P = rNull := by
  refine ⟨fun h => rel_ext' fun a b => ⟨fun hab => ?_, fun hab => absurd hab (rNull_apply a b)⟩,
    fun h => by rw [h, addLast_rNull]⟩
  have : (P ⇸ x) a b := Or.inl hab
  rw [h] at this
  exact absurd this (rNull_apply a b)

private theorem addFirst_eq_rNull_iff {P : α → α → Prop} {x : α} : x ⇷ P = rNull ↔ P = rNull := by
  refine ⟨fun h => rel_ext' fun a b => ⟨fun hab => ?_, fun hab => absurd hab (rNull_apply a b)⟩,
    fun h => by rw [h, addFirst_rNull]⟩
  have : (x ⇷ P) a b := Or.inr hab
  rw [h] at this
  exact absurd this (rNull_apply a b)

private theorem semi_rNull (S : α → β → Prop) : S ⁏ (rNull : β → β → Prop) = rNull := by
  refine rel_ext' fun a b => ?_
  rw [semi_iff']
  exact ⟨fun ⟨_, _, _, _, h⟩ => absurd h (rNull_apply _ _), fun h => absurd h (rNull_apply _ _)⟩

private theorem fld_rNull : fld (rNull : α → α → Prop) = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨w, h | h⟩ <;> exact rNull_apply _ _ h

private theorem oneone_rNull : (rNull : α → β → Prop) ∈ arrow one one := by
  rw [oneone_iff]
  exact ⟨fun _ _ _ h => absurd h.1 (rNull_apply _ _), fun _ _ _ h => absurd h.1 (rNull_apply _ _)⟩

private theorem smor_rNull : smor (rNull : α → α → Prop) (rNull : β → β → Prop) := by
  refine ⟨rNull, ⟨oneone_rNull, ?_⟩, (semi_rNull _).symm⟩
  rw [fld_rNull]
  ext z
  simp only [Set.mem_empty_iff_false, false_iff]
  rintro ⟨w, h⟩
  exact rNull_apply _ _ h

private theorem smor_rNull_iff {P : α → α → Prop} : smor P (rNull : β → β → Prop) ↔ P = rNull :=
  ⟨fun ⟨S, _, e⟩ => e.trans (semi_rNull S), fun e => by rw [e]; exact smor_rNull⟩

private theorem smorbar_cnv {S : α → β → Prop} {P : α → α → Prop} {Q : β → β → Prop}
    (h : S ∈ smorbar P Q) : S ∈ smorbar P˘ Q˘ := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨⟨h1, by rw [fld_cnv']; exact h2⟩, by rw [h3, cnv_semi]⟩

/-- The content of ✱161·3, proved here so that ✱161·301 can use it with converses. -/
private theorem addLast_smorbar {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} {x : α}
    {y : β} (h : ((rEx Q ∧ S ∈ smorbar P Q) ∧ x ∉ fld P) ∧ y ∉ fld Q) :
    S ⊍ x ↓ y ∈ smorbar (P ⇸ x) (Q ⇸ y) := by
  obtain ⟨⟨⟨hQ, hS⟩, hx⟩, hy⟩ := h
  have dS := dom_of_smorbar hS
  obtain ⟨⟨oS, cS⟩, eS⟩ := hS
  have yQ : ∀ z, z ∈ fld Q → z ≠ y := fun z hz e => hy (e ▸ hz)
  refine ⟨⟨oneone_rcup oS (couple_oneone x y) ?_ ?_, ?_⟩, ?_⟩
  · intro a b c hab hac
    have ha : a ∈ fld P := by rw [← dS]; exact ⟨b, hab⟩
    rw [couple_apply] at hac
    rw [hac.1] at ha
    exact hx ha
  · intro a b c hac hbc
    have hc : c ∈ fld Q := by rw [cS]; exact ⟨a, hac⟩
    rw [couple_apply] at hbc
    exact yQ c hc hbc.2
  · rw [fld_addLast hQ, codom_rcup, cS, codom_couple]
  · refine rel_ext' fun a b => ?_
    rw [addLast_apply, semi_iff', ← dS, eS, semi_iff']
    constructor
    · rintro (⟨z, w, h1, h2, h3⟩ | ⟨⟨z, hz⟩, e⟩)
      · exact ⟨z, w, Or.inl h1, Or.inl h2, Or.inl h3⟩
      · have : z ∈ fld Q := by rw [cS]; exact ⟨a, hz⟩
        exact ⟨z, y, Or.inl hz, Or.inr ((couple_apply _ _ _ _).2 ⟨e, rfl⟩), Or.inr ⟨this, rfl⟩⟩
    · rintro ⟨z, w, h1 | h1, h2 | h2, h3 | ⟨h3, e⟩⟩
      · exact Or.inl ⟨z, w, h1, h2, h3⟩
      · exact absurd e (yQ w (by rw [cS]; exact ⟨b, h2⟩))
      · rw [couple_apply] at h2
        exact absurd h2.2 (yQ w (mem_fld_r h3))
      · rw [couple_apply] at h2
        exact Or.inr ⟨⟨z, h1⟩, h2.1⟩
      all_goals
        rw [couple_apply] at h1
        first
          | exact absurd h1.2 (yQ z (mem_fld_l h3))
          | exact absurd h1.2 (yQ z h3)

/-- The content of ✱161·32, proved here so that ✱161·321 can use it with converses. -/
private theorem smorbar_of_addLast {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    {x : α} {y : β} (h : ((rEx Q ∧ x ∉ fld P) ∧ y ∉ fld Q) ∧ S ∈ smorbar (P ⇸ x) (Q ⇸ y)) :
    S ↾ (ι y)ᶜ ∈ smorbar P Q ∧ S x y := by
  obtain ⟨⟨⟨hQ, hx⟩, hy⟩, ⟨⟨oS, cS⟩, eS⟩⟩ := h
  rw [fld_addLast hQ] at cS
  rw [oneone_iff] at oS
  have yQ : ∀ z, z ∈ fld Q → z ≠ y := fun z hz e => hy (e ▸ hz)
  have hyc : y ∈ codom S := by rw [← cS]; exact Or.inr (mem_unitCls.2 rfl)
  obtain ⟨u, hu⟩ := hyc
  have key : ∀ a b, (P ⇸ x) a b ↔ ∃ z w, S a z ∧ S b w ∧ (Q ⇸ y) z w := fun a b => by
    rw [eS, semi_iff']
  have hnu : ∀ b, ¬ (P ⇸ x) u b := by
    intro b hb
    obtain ⟨z, w, h1, -, h3⟩ := (key u b).1 hb
    have e : z = y := oS.2 u z y ⟨h1, hu⟩
    rcases h3 with h3 | ⟨h3, -⟩
    · exact yQ z (mem_fld_l h3) e
    · exact yQ z h3 e
  have hux : u = x := by
    obtain ⟨z₀, w₀, hz₀⟩ := hQ
    have hz : z₀ ∈ codom S := by rw [← cS]; exact Or.inl (mem_fld_l hz₀)
    obtain ⟨v, hv⟩ := hz
    have : (P ⇸ x) v u := (key v u).2 ⟨z₀, y, hv, hu, Or.inr ⟨mem_fld_l hz₀, rfl⟩⟩
    rcases this with h | ⟨-, e⟩
    · exact (hnu x (Or.inr ⟨mem_fld_r h, rfl⟩)).elim
    · exact e
  rw [hux] at hu
  have hsub : fld Q ⊆ (ι y)ᶜ := fun z hz e => yQ z hz (mem_unitCls.1 e)
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hu⟩
  · rw [oneone_iff]
    exact ⟨fun a b c h => oS.1 a b c ⟨h.1.1, h.2.1⟩, fun a b c h => oS.2 a b c ⟨h.1.1, h.2.1⟩⟩
  · ext z
    constructor
    · intro hz
      have : z ∈ codom S := by rw [← cS]; exact Or.inl hz
      obtain ⟨a, ha⟩ := this
      exact ⟨a, ha, hsub hz⟩
    · rintro ⟨a, ha, hz⟩
      have : z ∈ fld Q ∪ ι y := by rw [cS]; exact ⟨a, ha⟩
      exact this.resolve_right hz
  · rw [cres_semi_of hsub]
    refine rel_ext' fun a b => ?_
    rw [semi_iff']
    constructor
    · intro hab
      obtain ⟨z, w, h1, h2, h3 | ⟨-, e⟩⟩ := (key a b).1 (Or.inl hab)
      · exact ⟨z, w, h1, h2, h3⟩
      · rw [e] at h2
        have hb : b = x := oS.1 b x y ⟨h2, hu⟩
        exact (hx (by rw [← hb]; exact mem_fld_r hab)).elim
    · rintro ⟨z, w, h1, h2, h3⟩
      rcases (key a b).2 ⟨z, w, h1, h2, Or.inl h3⟩ with h | ⟨-, e⟩
      · exact h
      · rw [e] at h2
        have hw : w = y := oS.2 x w y ⟨h2, hu⟩
        exact (yQ w (mem_fld_r h3) hw).elim

private theorem graph_semi_addLast (f : β → α) (Q : β → β → Prop) (x : β) :
    graph f ⁏ (Q ⇸ x) = (graph f ⁏ Q) ⇸ f x := by
  refine rel_ext' fun a b => ?_
  rw [semi_graph_apply, addLast_apply, semi_graph_apply, fld_semi_graph]
  constructor
  · rintro ⟨z, w, ⟨rfl, rfl⟩, h | ⟨hz, e⟩⟩
    · exact Or.inl ⟨z, w, ⟨rfl, rfl⟩, h⟩
    · exact Or.inr ⟨⟨z, hz, rfl⟩, by rw [e]⟩
  · rintro (⟨z, w, ⟨rfl, rfl⟩, h⟩ | ⟨⟨z, hz, rfl⟩, rfl⟩)
    · exact ⟨z, w, ⟨rfl, rfl⟩, Or.inl h⟩
    · exact ⟨z, x, ⟨rfl, rfl⟩, Or.inr ⟨hz, rfl⟩⟩

private theorem graph_semi_addFirst (f : β → α) (Q : β → β → Prop) (x : β) :
    graph f ⁏ (x ⇷ Q) = f x ⇷ (graph f ⁏ Q) := by
  refine rel_ext' fun a b => ?_
  rw [semi_graph_apply, addFirst_apply, semi_graph_apply, fld_semi_graph]
  constructor
  · rintro ⟨z, w, ⟨rfl, rfl⟩, ⟨e, hw⟩ | h⟩
    · exact Or.inl ⟨by rw [e], ⟨w, hw, rfl⟩⟩
    · exact Or.inr ⟨z, w, ⟨rfl, rfl⟩, h⟩
  · rintro (⟨rfl, ⟨w, hw, rfl⟩⟩ | ⟨z, w, ⟨rfl, rfl⟩, h⟩)
    · exact ⟨x, w, ⟨rfl, rfl⟩, Or.inl ⟨rfl, hw⟩⟩
    · exact ⟨z, w, ⟨rfl, rfl⟩, Or.inr h⟩

private theorem rcup_assoc (R S T : α → β → Prop) : R ⊍ S ⊍ T = R ⊍ (S ⊍ T) :=
  rel_ext' fun _ _ => or_assoc

private theorem semi_rcup (S : α → β → Prop) (P Q : β → β → Prop) :
    S ⁏ (P ⊍ Q) = S ⁏ P ⊍ S ⁏ Q := by
  refine rel_ext' fun x y => ?_
  rw [rcup_apply', semi_iff', semi_iff', semi_iff']
  constructor
  · rintro ⟨z, w, h1, h2, h | h⟩
    exacts [Or.inl ⟨z, w, h1, h2, h⟩, Or.inr ⟨z, w, h1, h2, h⟩]
  · rintro (⟨z, w, h1, h2, h⟩ | ⟨z, w, h1, h2, h⟩)
    exacts [⟨z, w, h1, h2, Or.inl h⟩, ⟨z, w, h1, h2, Or.inr h⟩]

private theorem mem_fld_sumRel {L : Set (α → α → Prop)} {x : α} :
    x ∈ fld (sumRel L) ↔ ∃ Q, Q ∈ L ∧ x ∈ fld Q := by
  constructor
  · rintro ⟨y, ⟨Q, hQ, h⟩ | ⟨Q, hQ, h⟩⟩
    exacts [⟨Q, hQ, mem_fld_l h⟩, ⟨Q, hQ, mem_fld_r h⟩]
  · rintro ⟨Q, hQ, ⟨y, h | h⟩⟩
    exacts [⟨y, Or.inl ⟨Q, hQ, h⟩⟩, ⟨y, Or.inr ⟨Q, hQ, h⟩⟩]

private theorem mem_sumCls_graph_img {f : β → Set α} {K : Set β} {x : α} :
    x ∈ sumCls (graph f ʻʻ K) ↔ ∃ Q, Q ∈ K ∧ x ∈ f Q := by
  constructor
  · rintro ⟨A, ⟨Q, hQ, rfl⟩, hx⟩; exact ⟨Q, hQ, hx⟩
  · rintro ⟨Q, hQ, hx⟩; exact ⟨f Q, ⟨Q, hQ, rfl⟩, hx⟩

private theorem Cnv_eq_graph : (Cnv : (β → α → Prop) → (α → β → Prop) → Prop) = graph cnv := by
  funext Q P
  exact propext Cnv_iff

private theorem sumRel_unit (Q : α → β → Prop) : sumRel (ι Q) = Q :=
  rel_ext' fun x y => ⟨fun ⟨R, hR, h⟩ => by rw [mem_unitCls] at hR; rw [← hR]; exact h,
    fun h => ⟨Q, mem_unitCls.2 rfl, h⟩⟩

private theorem semi_sumRel (R : α → β → Prop) (L : Set (β → β → Prop)) :
    R ⁏ sumRel L = sumRel (daggerRel R ʻʻ L) := by
  refine rel_ext' fun x y => ?_
  rw [semi_iff']
  constructor
  · rintro ⟨z, w, h1, h2, Q, hQ, h⟩
    exact ⟨daggerOp R Q, ⟨Q, hQ, rfl⟩, (semi_iff' R Q x y).2 ⟨z, w, h1, h2, h⟩⟩
  · rintro ⟨T, ⟨Q, hQ, rfl⟩, h⟩
    obtain ⟨z, w, h1, h2, h⟩ := (semi_iff' R Q x y).1 h
    exact ⟨z, w, h1, h2, Q, hQ, h⟩

private theorem relSigma_iff (P : (α → α → Prop) → (α → α → Prop) → Prop) (x y : α) :
    relSigma P x y ↔ sumRel (fld P) x y ∨ (F ⁏ P) x y := Iff.rfl

private theorem inter_null_iff {A B : Set α} : A ∩ B = Λ ↔ ¬ (A ∩ B).Nonempty := by
  rw [Null_eq_empty, Set.not_nonempty_iff_eq_empty]

private theorem eq_rNull_of_fld {Q : α → α → Prop} (h : fld Q = ∅) : Q = rNull :=
  eq_rNull_of_not_rEx (by rw [rEx_iff_fld, h]; exact Set.not_nonempty_empty)

private theorem eq_rNull_of_dom {Q : α → β → Prop} (h : dom Q = ∅) : Q = rNull :=
  rel_ext' fun x y => ⟨fun hxy => by
    have : x ∈ dom Q := ⟨y, hxy⟩
    rw [h] at this; simp at this, fun hxy => absurd hxy (rNull_apply x y)⟩

private theorem eq_rNull_of_codom {Q : α → β → Prop} (h : codom Q = ∅) : Q = rNull :=
  rel_ext' fun x y => ⟨fun hxy => by
    have : y ∈ codom Q := ⟨x, hxy⟩
    rw [h] at this; simp at this, fun hxy => absurd hxy (rNull_apply x y)⟩

/-- `P ∈ Rel² excl` pointwise: members of `C'P` with a common field member are identical. -/
private theorem excl_iff' {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ↔ ∀ Q R, Q ∈ fld P → R ∈ fld P → ∀ x, x ∈ fld Q → x ∈ fld R → Q = R := by
  constructor
  · intro h Q R hQ hR x hxQ hxR
    by_contra hne
    exact not_mem_of_disj (h Q R ⟨⟨hQ, hR⟩, hne⟩) hxQ hxR
  · intro h Q R ⟨⟨hQ, hR⟩, hne⟩
    rw [inter_null_iff]
    rintro ⟨x, hxQ, hxR⟩
    exact hne (h Q R hQ hR x hxQ hxR)

private theorem mem_sumCls_C {K : Set (α → α → Prop)} {x : α} :
    x ∈ sumCls (C ʻʻ K) ↔ ∃ Q, Q ∈ K ∧ x ∈ fld Q := mem_sumCls_graph_img

private theorem mem_Cnv_img {K : Set (α → β → Prop)} {T : β → α → Prop} :
    T ∈ Cnv ʻʻ K ↔ ∃ Q, Q ∈ K ∧ T = Q˘ :=
  ⟨fun ⟨Q, hQ, h⟩ => ⟨Q, hQ, Cnv_iff.1 h⟩, fun ⟨Q, hQ, h⟩ => ⟨Q, hQ, Cnv_iff.2 h⟩⟩

private theorem fld_Cnv_semi (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    fld (Cnv ⁏ P) = Cnv ʻʻ fld P := by
  rw [Cnv_eq_graph]; exact fld_semi_graph _ _

private theorem smorsmorbar_iff {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    S ∈ smorsmorbar P Q ↔
      (S ∈ arrow one one ∧ codom S = fld (relSigma Q)) ∧ P = daggerRel S ⁏ Q := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, (h2 : fld (relSigma Q) = codom S).symm⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, (h2.symm : fld (relSigma Q) = codom S)⟩, h3⟩

private theorem semi_dagger_apply (S : α → β → Prop) (Q : (β → β → Prop) → (β → β → Prop) → Prop)
    (X Y : α → α → Prop) :
    (daggerRel S ⁏ Q) X Y ↔ ∃ M N, (X = S ⁏ M ∧ Y = S ⁏ N) ∧ Q M N :=
  semi_graph_apply (daggerOp S) Q X Y

private theorem cres_oneone {S : α → β → Prop} {B : Set β} (h : S ∈ arrow one one) :
    S ↾ B ∈ arrow one one := by
  rw [oneone_iff] at *
  exact ⟨fun x y z h' => h.1 x y z ⟨h'.1.1, h'.2.1⟩, fun x y z h' => h.2 x y z ⟨h'.1.1, h'.2.1⟩⟩

private theorem cnv_oneone {S : α → β → Prop} (h : S ∈ arrow one one) : S˘ ∈ arrow one one := by
  rw [oneone_iff] at *
  exact ⟨fun x y z h' => h.2 z x y h', fun x y z h' => h.1 y z x h'⟩

private theorem oneone_Cls_one {S : α → β → Prop} (h : S ∈ arrow one one) : S ∈ arrow Cls one :=
  mem_arrow_Cls_one.2 (oneone_iff.1 h).2

private theorem cnv_semi_semi' {S : α → β → Prop} {M : β → β → Prop} (hS : S ∈ arrow Cls one)
    (hM : fld M ⊆ codom S) : S˘ ⁏ (S ⁏ M) = M := by
  refine rel_ext' fun a b => ?_
  rw [semi_iff']
  constructor
  · rintro ⟨x, y, hxa, hyb, h⟩
    obtain ⟨c, d, hxc, hyd, hcd⟩ := (semi_iff' S M x y).1 h
    have h1 : a = c := mem_arrow_Cls_one.1 hS x a c ⟨hxa, hxc⟩
    have h2 : b = d := mem_arrow_Cls_one.1 hS y b d ⟨hyb, hyd⟩
    rw [h1, h2]; exact hcd
  · intro hab
    obtain ⟨x, hx⟩ := hM (mem_fld_l hab)
    obtain ⟨y, hy⟩ := hM (mem_fld_r hab)
    exact ⟨x, y, hx, hy, (semi_iff' S M x y).2 ⟨a, b, hx, hy, hab⟩⟩

private theorem oneone_comp {S : α → β → Prop} {T : β → γ → Prop} (hS : S ∈ arrow one one)
    (hT : T ∈ arrow one one) : S ⨾ T ∈ arrow one one := by
  rw [oneone_iff] at *
  refine ⟨?_, ?_⟩
  · rintro x y z ⟨⟨u, hxu, huz⟩, ⟨v, hyv, hvz⟩⟩
    have : u = v := hT.1 u v z ⟨huz, hvz⟩
    rw [this] at hxu
    exact hS.1 x y v ⟨hxu, hyv⟩
  · rintro x y z ⟨⟨u, hxu, huy⟩, ⟨v, hxv, hvz⟩⟩
    have : u = v := hS.2 x u v ⟨hxu, hxv⟩
    rw [this] at huy
    exact hT.2 v y z ⟨huy, hvz⟩

private theorem I_oneone : (I : α → α → Prop) ∈ arrow one one := by
  rw [oneone_iff]
  exact ⟨fun x y z h => (h.1 : x = z).trans (h.2 : y = z).symm,
    fun x y z h => (h.1 : x = y).symm.trans (h.2 : x = z)⟩

private theorem semi_I (M : α → α → Prop) : I ⁏ M = M := by
  refine rel_ext' fun a b => ?_
  rw [semi_iff']
  constructor
  · rintro ⟨z, w, h1, h2, h⟩
    have h1' : a = z := h1
    have h2' : b = w := h2
    rw [h1', h2']; exact h
  · intro h; exact ⟨a, b, rfl, rfl, h⟩

private theorem graph_semi_couple (f : β → α) (a b : β) : graph f ⁏ (a ↓ b) = f a ↓ f b := by
  refine rel_ext' fun x y => ?_
  rw [semi_graph_apply, couple_apply]
  constructor
  · rintro ⟨z, w, ⟨rfl, rfl⟩, h⟩
    rw [couple_apply] at h
    rw [h.1, h.2]
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨a, b, ⟨rfl, rfl⟩, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩⟩

private theorem semi_dagger_couple (X : α → β → Prop) (A B : β → β → Prop) :
    daggerRel X ⁏ (A ↓ B) = (X ⁏ A) ↓ (X ⁏ B) :=
  graph_semi_couple (daggerOp X) A B

/-- A selection from a class of non-empty classes (Lean's choice; cf. ✱88·37). -/
private theorem sel_memRel_nonempty' {K : Set (Set γ)} (h : ∀ L, L ∈ K → L.Nonempty) :
    (sel memRel K).Nonempty := by
  refine ⟨fun T L => ∃ hL : L ∈ K, T = (h L hL).some, mem_sel_iff.2 ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rw [mem_arrow_one_Cls]
    rintro x y L ⟨⟨hL, rfl⟩, ⟨hL', rfl⟩⟩
    rfl
  · rintro T L ⟨hL, rfl⟩
    exact (h L hL).some_mem
  · ext L
    constructor
    · rintro ⟨T, hL, -⟩; exact hL
    · intro hL; exact ⟨_, hL, rfl⟩

private theorem mem_fld_coupleSemi_semi {P : α → α → Prop} {Q : β → β → Prop}
    {T : (α → β → Prop) → (α → β → Prop) → Prop} :
    T ∈ fld (coupleSemi P ⁏ Q) ↔ ∃ z, z ∈ fld Q ∧ T = opSemi couple P z := by
  rw [fld_coupleSemi_semi]; exact Iff.rfl

private theorem rEx_opSemi {P : α → α → Prop} {z : β} : rEx (opSemi couple P z) ↔ rEx P := by
  constructor
  · rintro ⟨X, Y, h⟩
    obtain ⟨x, y, -, hxy⟩ := (opSemi_couple_apply P z X Y).1 h
    exact ⟨x, y, hxy⟩
  · rintro ⟨x, y, h⟩
    exact ⟨x ↓ z, y ↓ z, (opSemi_couple_apply P z _ _).2 ⟨x, y, ⟨rfl, rfl⟩, h⟩⟩

private theorem opSemi_inj {P : α → α → Prop} (hP : rEx P) {z w : β}
    (h : opSemi couple P z = opSemi couple P w) : z = w := by
  obtain ⟨x, y, hxy⟩ := hP
  have h1 : opSemi couple P z (x ↓ z) (y ↓ z) := (opSemi_couple_apply P z _ _).2 ⟨x, y, ⟨rfl, rfl⟩, hxy⟩
  rw [h] at h1
  obtain ⟨x', y', ⟨e, -⟩, -⟩ := (opSemi_couple_apply P w _ _).1 h1
  exact (couple_eq_couple_iff.1 e).2

private theorem mem_clsTimes' {A : Set α} {B : Set β} {X : α → β → Prop} :
    X ∈ B ×ₐ A ↔ ∃ x y, (x ∈ A ∧ y ∈ B) ∧ X = x ↓ y := by
  constructor
  · rintro ⟨K, ⟨y, hy, hK⟩, hX⟩
    have hK' : K = opImg couple A y := hK
    rw [hK'] at hX
    obtain ⟨x, hx, hX⟩ := hX
    exact ⟨x, y, ⟨hx, hy⟩, hX⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    exact couple_mem_clsTimes.2 ⟨hx, hy⟩

private theorem EE_of {R : α → β → Prop} {B : Set β} (h1 : R ↾ B ∈ arrow one Cls)
    (h2 : B ⊆ codom R) : EE R B := by
  intro y hy
  obtain ⟨b, hb⟩ := h2 hy
  exact ⟨b, fun x => ⟨fun hx => mem_arrow_one_Cls.1 h1 x b y ⟨⟨hx, hy⟩, ⟨hb, hy⟩⟩,
    fun e => e ▸ hb⟩⟩

private theorem relProd_couple {R : γ → α → Prop} {y : α} {b : γ} (hb : ∀ x, R x y ↔ x = b)
    (z : β) : R ⨾ (y ↓ z) = b ↓ z := by
  refine rel_ext' fun u w => ?_
  rw [couple_apply]
  constructor
  · rintro ⟨v, hv, h⟩
    rw [couple_apply] at h
    rw [h.1] at hv
    exact ⟨(hb u).1 hv, h.2⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨y, (hb u).2 rfl, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩⟩

private theorem couple_relProd_cnv {S : δ → β → Prop} {z : β} {b : δ} (hb : ∀ u, S u z ↔ u = b)
    (x : α) : (x ↓ z) ⨾ S˘ = x ↓ b := by
  refine rel_ext' fun a c => ?_
  rw [couple_apply]
  constructor
  · rintro ⟨v, h, hv⟩
    rw [couple_apply] at h
    have hv' : S c v := hv
    rw [h.2] at hv'
    exact ⟨h.1, (hb c).1 hv'⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨z, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩, ((hb _).2 rfl : S _ z)⟩

private theorem cres_codom_self (S : α → β → Prop) : S ↾ codom S = S :=
  rel_ext' fun x _ => ⟨fun h => h.1, fun h => ⟨h, ⟨x, h⟩⟩⟩

end Helpers

/-- Rewrite sums, added terms, couples and their fields pointwise (keeping `C'P` as an atom). -/
local macro "asimp" : tactic => `(tactic| simp only [rel_eq_iff, rsum_apply, addLast_apply,
  addFirst_apply, rcup_apply', cross_apply', couple_apply, mem_unitCls, Set.mem_union, fld_rsum,
  fld_couple, fld_rcup])

/-!
## [✱160] The sum of two relations

*(Vol. 2, p. 351)*

> *Summary of* *160.
>
> In this number, we introduce the definition \[ P\unicode{x2909}Q=P\unicode{x228d} Q\unicode{x228d} CʻP\uparrow CʻQ \quad\text{Df}, \] which was explained in the introduction to this section. Although the propositions of this and other numbers in this Part do not require that \(P\) and \(Q\) should be such as to generate series, yet the reader will find it convenient to imagine them to be such, since the important applications of the ideas of this Part are to series. Thus we may regard the sum of \(P\) and \(Q\) as a relation which holds between \(x\) and \(y\) when either \(x\) precedes \(y\) in the \(P\)-series, or \(x\) precedes \(y\) in the \(Q\)-series, or \(x\) belongs to the \(P\)-series and \(y\) belongs to the \(Q\)-series.
>
> The most important propositions of this number are :
>
> *160·14. \(\vdash .Cʻ(P\unicode{x2909}Q)=CʻP\cup CʻQ\)
>
> *160·21. \(\vdash .P\unicode{x2909}\dot{\Lambda} =P\)
>
> *160·22. \(\vdash .\dot{\Lambda} \unicode{x2909}Q=Q\)
>
> *160·31. \(\vdash .(P\unicode{x2909}Q)\unicode{x2909}R=P\unicode{x2909}(Q\unicode{x2909}R)\)
>
> which is the associative law, and
>
> …

**Lean reading.** `P ⤉ Q` is `rsum P Q` (homogeneous `P Q : α → α → Prop`), `P ∪̇ Q ∪̇ C'P ↑ C'Q`
with `∪̇` bracketed to the left; `B⃗'P` (✱93) is `refs Beg P`, `Cnv'P` is `P˘`, `D'R`, `ᗡ'R`,
`C'R` are `dom R`, `codom R`, `fld R`, `R²` is `rsq R`, `S;Q` is `S ⁏ Q`, `P ⥏ α` is `P ⥏ A`.
In ✱160·41 the relation `⤉R` (✱38·02) is `opR rsum R`, so `⤉R''λ` is `opR rsum R ʻʻ L`, and
`λ⤉R` (the e-text drops the `,,` of ✱38·03) is `opImg rsum L R`; in ✱160·411 `P⤉` is `opL rsum P`;
in ✱160·412 `λ⤉,,` is the relation `opL (opImg rsum) L`. The correlators of ✱160·45–·47 are
heterogeneous `S : α → β → Prop`. ✱160·35 is false as printed (`P ⤉ Q ⊂̇ R ⤉ S` from
`P ⊂̇ Q . R ⊂̇ S`); its proof `[✱160·33·34]` gives `P ⤉ R ⊂̇ Q ⤉ S`, which is proved, with the
counterexample to the printed form. (The e-text numbers ✱160·34, `R ⊂̇ S . ⊃ . Q ⤉ R ⊂̇ Q ⤉ S`,
`*160*34.`, a star for the centred dot; it is used in the proof of ✱160·35.)

**Status.** proved (all propositions; ✱160·01·32 definition; ✱160·35 proved (corrected),
✱160·41 proved (reading), see their docstrings)
-/

/-- ✱160·01 (Df). \(P\unicode{x2909}Q=P\unicode{x228d} Q\unicode{x228d} CʻP\uparrow CʻQ \quad\text{Df}\) -/
theorem pm160_01 {α : Type*} {P Q : α → α → Prop} : P ⤉ Q = P ⊍ Q ⊍ cross (fld P) (fld Q) := rfl

/-- ✱160·1. \(\vdash .P\unicode{x2909}Q=P\unicode{x228d} Q\unicode{x228d} CʻP\uparrow CʻQ \quad[(*160·01)]\) -/
theorem pm160_1 {α : Type*} {P Q : α → α → Prop} : P ⤉ Q = P ⊍ Q ⊍ cross (fld P) (fld Q) := rfl

/-- ✱160·11. \(\vdash \colon\ldotp x(P\unicode{x2909}Q)y.\equiv :xPy.\lor.xQy.\lor.x\in CʻP.y\in CʻQ \quad[*160·1]\) -/
theorem pm160_11 {α : Type*} {P Q : α → α → Prop} {x y : α} :
    (P ⤉ Q) x y ↔ (P x y ∨ Q x y) ∨ x ∈ fld P ∧ y ∈ fld Q := Iff.rfl

/-- ✱160·111. \(\vdash \colon\ldotp x(P\unicode{x2909}Q)y.\equiv :xPy.\lor.xQy.\lor.xFP.yFQ \quad[*160·11.*33·51]\)

`xFP` is `F x P` (✱33·04: `x ∈ C'P`). -/
theorem pm160_111 {α : Type*} {P Q : α → α → Prop} {x y : α} :
    (P ⤉ Q) x y ↔ (P x y ∨ Q x y) ∨ F x P ∧ F y Q := Iff.rfl

/-- ✱160·12. \(\vdash :\dot{\exists} !Q.\supset .\text{D}ʻ(P\unicode{x2909}Q)=CʻP\cup \text{D}ʻQ \quad[*33·26.*35·85.*160·1]\) -/
theorem pm160_12 {α : Type*} {P Q : α → α → Prop} : rEx Q → dom (P ⤉ Q) = fld P ∪ dom Q := by
  intro h
  bsimp
  grind

/-- ✱160·13. \(\vdash :\dot{\exists} !P.\supset .\text{ᗡ}ʻ(P\unicode{x2909}Q)=\text{ᗡ}ʻP\cup CʻQ\) -/
theorem pm160_13 {α : Type*} {P Q : α → α → Prop} : rEx P → codom (P ⤉ Q) = codom P ∪ fld Q := by
  intro h
  bsimp
  grind

/-- ✱160·14. \(\vdash .Cʻ(P\unicode{x2909}Q)=CʻP\cup CʻQ\) -/
theorem pm160_14 {α : Type*} {P Q : α → α → Prop} : fld (P ⤉ Q) = fld P ∪ fld Q := fld_rsum P Q

/-- ✱160·15. \(\vdash :\dot{\exists} !P.\supset .\overrightarrow{B}ʻ(P\unicode{x2909}Q)=\overrightarrow{B}ʻP-CʻQ\) -/
theorem pm160_15 {α : Type*} {P Q : α → α → Prop} :
    rEx P → refs Beg (P ⤉ Q) = refs Beg P \ fld Q := by
  intro h
  ext x
  show x ∈ dom (P ⤉ Q) \ codom (P ⤉ Q) ↔ x ∈ dom P \ codom P ∧ x ∉ fld Q
  rw [pm160_13 h]
  simp only [Set.mem_sdiff, Set.mem_union, not_or]
  constructor
  · rintro ⟨⟨y, hy⟩, hc, hq⟩
    refine ⟨⟨?_, hc⟩, hq⟩
    rcases hy with (hy | hy) | ⟨⟨z, hz | hz⟩, -⟩
    · exact ⟨y, hy⟩
    · exact absurd (mem_fld_l hy) hq
    · exact ⟨z, hz⟩
    · exact absurd ⟨z, hz⟩ hc
  · rintro ⟨⟨⟨y, hy⟩, hc⟩, hq⟩
    exact ⟨⟨y, Or.inl (Or.inl hy)⟩, hc, hq⟩

/-- ✱160·151. \(\vdash :\dot{\exists} !Q.\supset .\overrightarrow{B}ʻ\text{Cnv}ʻ(P\unicode{x2909}Q)=\overrightarrow{B}ʻ\breve{Q} -CʻP\) -/
theorem pm160_151 {α : Type*} {P Q : α → α → Prop} :
    rEx Q → refs Beg (P ⤉ Q)˘ = refs Beg Q˘ \ fld P := by
  intro h
  have e : (P ⤉ Q)˘ = Q˘ ⤉ P˘ := by bsimp; grind
  rw [e, pm160_15 (by obtain ⟨x, y, hxy⟩ := h; exact ⟨y, x, hxy⟩), fld_cnv']

/-- ✱160·16. \(\vdash :\dot{\exists} !P.\overrightarrow{B}ʻP\cap CʻQ=\Lambda .\supset .\overrightarrow{B}ʻ(P\unicode{x2909}Q)=\overrightarrow{B}ʻP \quad[*160·15]\) -/
theorem pm160_16 {α : Type*} {P Q : α → α → Prop} :
    rEx P ∧ refs Beg P ∩ fld Q = Λ → refs Beg (P ⤉ Q) = refs Beg P := by
  rintro ⟨h1, h2⟩
  rw [pm160_15 h1]
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, not_mem_of_disj h2 hx⟩⟩

/-- ✱160·161. \(\vdash :\dot{\exists} !Q.\overrightarrow{B}ʻ\breve{Q} \cap CʻP=\Lambda .\supset .\overrightarrow{B}ʻ\text{Cnv}ʻ(P\unicode{x2909}Q)=\overrightarrow{B}ʻ\breve{Q} \) -/
theorem pm160_161 {α : Type*} {P Q : α → α → Prop} :
    rEx Q ∧ refs Beg Q˘ ∩ fld P = Λ → refs Beg (P ⤉ Q)˘ = refs Beg Q˘ := by
  rintro ⟨h1, h2⟩
  rw [pm160_151 h1]
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, not_mem_of_disj h2 hx⟩⟩

/-- ✱160·2. \(\vdash .\text{Cnv}ʻ(P\unicode{x2909}Q)=\breve{Q} \unicode{x2909}\breve{P} \quad[*31·15.*35·84]\) -/
theorem pm160_2 {α : Type*} {P Q : α → α → Prop} : (P ⤉ Q)˘ = Q˘ ⤉ P˘ := by
  bsimp
  grind

/-- ✱160·21. \(\vdash .P\unicode{x2909}\dot{\Lambda} =P \quad[*35·88.*25·24]\) -/
theorem pm160_21 {α : Type*} {P : α → α → Prop} : P ⤉ rNull = P := by
  bsimp
  grind

/-- ✱160·22. \(\vdash .\dot{\Lambda} \unicode{x2909}Q=Q\) -/
theorem pm160_22 {α : Type*} {Q : α → α → Prop} : rNull ⤉ Q = Q := by
  bsimp
  grind

/-- ✱160·3. \(\vdash .(P\unicode{x2909}Q)\unicode{x2909}R=P\unicode{x228d} Q\unicode{x228d} R\unicode{x228d} CʻP\uparrow CʻQ\unicode{x228d} CʻP\uparrow CʻR\unicode{x228d} CʻQ\uparrow CʻR\) -/
theorem pm160_3 {α : Type*} {P Q R : α → α → Prop} :
    (P ⤉ Q) ⤉ R = P ⊍ Q ⊍ R ⊍ cross (fld P) (fld Q) ⊍ cross (fld P) (fld R) ⊍
      cross (fld Q) (fld R) := by
  rw [rsum, fld_rsum]
  simp only [rsum, rcup, cross, Set.mem_union, rel_eq_iff]
  intro x y; tauto

/-- ✱160·31. \(\vdash .(P\unicode{x2909}Q)\unicode{x2909}R=P\unicode{x2909}(Q\unicode{x2909}R)\) -/
theorem pm160_31 {α : Type*} {P Q R : α → α → Prop} : (P ⤉ Q) ⤉ R = P ⤉ (Q ⤉ R) := by
  bsimp
  grind

/-- ✱160·32 (Df). \(P\unicode{x2909}Q\unicode{x2909}R=(P\unicode{x2909}Q)\unicode{x2909}R \quad\text{Df}\) -/
theorem pm160_32 {α : Type*} {P Q R : α → α → Prop} : P ⤉ Q ⤉ R = (P ⤉ Q) ⤉ R := rfl

/-- ✱160·33. \(\vdash :P\,\unicode{x2abd}\, Q.\supset .P\unicode{x2909}R\,\unicode{x2abd}\, Q\unicode{x2909}R \quad[*33·265.*160·1]\) -/
theorem pm160_33 {α : Type*} {P Q R : α → α → Prop} : P ⪽ Q → P ⤉ R ⪽ Q ⤉ R := by
  rintro h x y ((h1 | h1) | ⟨h1, h2⟩)
  · exact Or.inl (Or.inl (h _ _ h1))
  · exact Or.inl (Or.inr h1)
  · exact Or.inr ⟨fld_mono h h1, h2⟩

/-- ✱160·34. \(\vdash :R\,\unicode{x2abd}\, S.\supset .Q\unicode{x2909}R\,\unicode{x2abd}\, Q\unicode{x2909}S \quad [*33·265.*160·1]\)

The e-text numbers it `*160*34.` (a star for the centred dot). -/
theorem pm160_34 {α : Type*} {Q R S : α → α → Prop} : R ⪽ S → Q ⤉ R ⪽ Q ⤉ S := by
  rintro h x y ((h1 | h1) | ⟨h1, h2⟩)
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (h _ _ h1))
  · exact Or.inr ⟨h1, fld_mono h h2⟩

/-- ✱160·35.\(\vdash :P\,\unicode{x2abd}\, Q.R\,\unicode{x2abd}\, S.\supset .P\unicode{x2909}Q\,\unicode{x2abd}\, R\unicode{x2909}S \quad[*160*33*34]\)

**Status.** proved (corrected): as printed, `P ⊂̇ Q . R ⊂̇ S . ⊃ . P ⤉ Q ⊂̇ R ⤉ S` is false:
with `P = R = S = Λ̇` and `Q = V̇` the hypotheses hold but `P ⤉ Q = V̇ ⊄ Λ̇ = R ⤉ S`
(`pm160_35_printed_false`, in a nonempty type). The proof cited, `[✱160·33·34]`, gives
`P ⤉ R ⊂̇ Q ⤉ S` (enlarge first the left, then the right summand), which is proved. -/
theorem pm160_35 {α : Type*} {P Q R S : α → α → Prop} : P ⪽ Q ∧ R ⪽ S → P ⤉ R ⪽ Q ⤉ S := by
  rintro ⟨h, h'⟩ x y ((h1 | h1) | ⟨h1, h2⟩)
  · exact Or.inl (Or.inl (h _ _ h1))
  · exact Or.inl (Or.inr (h' _ _ h1))
  · exact Or.inr ⟨fld_mono h h1, fld_mono h' h2⟩

/-- The printed form of ✱160·35 fails (see its docstring). -/
theorem pm160_35_printed_false {α : Type*} [Nonempty α] :
    ¬ ∀ P Q R S : α → α → Prop, P ⪽ Q ∧ R ⪽ S → P ⤉ Q ⪽ R ⤉ S := by
  intro h
  obtain ⟨a⟩ := ‹Nonempty α›
  have := h rNull rV rNull rNull ⟨fun x y hxy => absurd hxy (rNull_apply x y),
    fun x y hxy => hxy⟩ a a (Or.inl (Or.inr ⟨rfl, rfl⟩))
  rcases this with (h1 | h1) | ⟨⟨b, h1 | h1⟩, -⟩ <;> exact rNull_apply _ _ h1

/-- ✱160·4. \(\vdash .(P\unicode{x228d} Q)\unicode{x2909}R=(P\unicode{x2909}R)\unicode{x228d} (Q\unicode{x2909}R)\) -/
theorem pm160_4 {α : Type*} {P Q R : α → α → Prop} : (P ⊍ Q) ⤉ R = (P ⤉ R) ⊍ (Q ⤉ R) := by
  simp only [rsum, fld_rcup]
  simp only [rcup, cross, Set.mem_union, rel_eq_iff]
  intro x y; tauto

/-- ✱160·401. \(\vdash .P\unicode{x2909}(Q\unicode{x228d} R)=(P\unicode{x2909}Q)\unicode{x228d} (P\unicode{x2909}R)\) -/
theorem pm160_401 {α : Type*} {P Q R : α → α → Prop} : P ⤉ (Q ⊍ R) = (P ⤉ Q) ⊍ (P ⤉ R) := by
  simp only [rsum, fld_rcup]
  simp only [rcup, cross, Set.mem_union, rel_eq_iff]
  intro x y; tauto

/-- ✱160·41. \(\vdash :\exists !\lambda .\supset .\dot{s} ʻ\lambda \unicode{x2909}R=\dot{s} ʻ\unicode{x2909}Rʻʻ\lambda =\dot{s} ʻ(\lambda \unicode{x2909}R)\)

`⤉R` is the relation `opR rsum R` (✱38·02), so `⤉R''λ` is `opR rsum R ʻʻ L`.

**Status.** proved (reading): the e-text prints `ṡ'(λ⤉R)`; `λ⤉R` is read as `λ⤉,,R`
(✱38·03, `opImg rsum L R`), the only significant reading (the `,,` is lost, as in ✱160·412's
`λ⤉,,`); the chain is the conjunction of its two links. -/
theorem pm160_41 {α : Type*} {L : Set (α → α → Prop)} {R : α → α → Prop} :
    L.Nonempty →
      sumRel L ⤉ R = sumRel (opR rsum R ʻʻ L) ∧
        sumRel (opR rsum R ʻʻ L) = sumRel (opImg rsum L R) := by
  rintro ⟨P₀, hP₀⟩
  refine ⟨rel_ext' fun x y => ?_, rfl⟩
  constructor
  · rintro ((⟨P, hP, h⟩ | h) | ⟨⟨z, ⟨P, hP, h⟩ | ⟨P, hP, h⟩⟩, hy⟩)
    · exact ⟨P ⤉ R, ⟨P, hP, rfl⟩, Or.inl (Or.inl h)⟩
    · exact ⟨P₀ ⤉ R, ⟨P₀, hP₀, rfl⟩, Or.inl (Or.inr h)⟩
    · exact ⟨P ⤉ R, ⟨P, hP, rfl⟩, Or.inr ⟨mem_fld_l h, hy⟩⟩
    · exact ⟨P ⤉ R, ⟨P, hP, rfl⟩, Or.inr ⟨mem_fld_r h, hy⟩⟩
  · rintro ⟨T, ⟨P, hP, rfl⟩, (h | h) | ⟨⟨z, h | h⟩, hy⟩⟩
    · exact Or.inl (Or.inl ⟨P, hP, h⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨⟨z, Or.inl ⟨P, hP, h⟩⟩, hy⟩
    · exact Or.inr ⟨⟨z, Or.inr ⟨P, hP, h⟩⟩, hy⟩

/-- ✱160·411. \(\vdash :\exists !\lambda .\supset .P\unicode{x2909}\dot{s} ʻ\lambda =\dot{s} ʻP\unicode{x2909}ʻʻ\lambda \quad[\text{Proof as in *160*41}]\)

`P⤉` is the relation `opL rsum P` (✱38·01). -/
theorem pm160_411 {α : Type*} {L : Set (α → α → Prop)} {P : α → α → Prop} :
    L.Nonempty → P ⤉ sumRel L = sumRel (opL rsum P ʻʻ L) := by
  rintro ⟨R₀, hR₀⟩
  refine rel_ext' fun x y => ?_
  constructor
  · rintro ((h | ⟨R, hR, h⟩) | ⟨hx, ⟨z, ⟨R, hR, h⟩ | ⟨R, hR, h⟩⟩⟩)
    · exact ⟨P ⤉ R₀, ⟨R₀, hR₀, rfl⟩, Or.inl (Or.inl h)⟩
    · exact ⟨P ⤉ R, ⟨R, hR, rfl⟩, Or.inl (Or.inr h)⟩
    · exact ⟨P ⤉ R, ⟨R, hR, rfl⟩, Or.inr ⟨hx, mem_fld_l h⟩⟩
    · exact ⟨P ⤉ R, ⟨R, hR, rfl⟩, Or.inr ⟨hx, mem_fld_r h⟩⟩
  · rintro ⟨T, ⟨R, hR, rfl⟩, (h | h) | ⟨hx, ⟨z, h | h⟩⟩⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨R, hR, h⟩)
    · exact Or.inr ⟨hx, ⟨z, Or.inl ⟨R, hR, h⟩⟩⟩
    · exact Or.inr ⟨hx, ⟨z, Or.inr ⟨R, hR, h⟩⟩⟩

/-- ✱160·412. \(\vdash :\exists !\lambda .\exists !\mu .\supset .\dot{s} ʻ\lambda \unicode{x2909}\dot{s} ʻ\mu = \dot{s} ʻsʻ\lambda \unicode{x2909}_{,,}ʻʻ\mu\)

`λ⤉,,` is the relation `opL (opImg rsum) L` (✱38·01 with ✱38·03), so `s'λ⤉,,''μ` is
`sumCls (opL (opImg rsum) L ʻʻ M)`. -/
theorem pm160_412 {α : Type*} {L M : Set (α → α → Prop)} :
    L.Nonempty ∧ M.Nonempty →
      sumRel L ⤉ sumRel M = sumRel (sumCls (opL (opImg rsum) L ʻʻ M)) := by
  rintro ⟨hL, hM⟩
  rw [pm160_411 hM]
  refine rel_ext' fun x y => ?_
  constructor
  · rintro ⟨T, ⟨R, hR, rfl⟩, h⟩
    rw [(pm160_41 (R := R) hL).1] at h
    obtain ⟨T', ⟨P, hP, rfl⟩, h'⟩ := h
    exact ⟨P ⤉ R, ⟨_, ⟨R, hR, rfl⟩, ⟨P, hP, rfl⟩⟩, h'⟩
  · rintro ⟨T, ⟨K, ⟨R, hR, rfl⟩, ⟨P, hP, rfl⟩⟩, h⟩
    refine ⟨sumRel L ⤉ R, ⟨R, hR, rfl⟩, ?_⟩
    rw [(pm160_41 (R := R) hL).1]
    exact ⟨P ⤉ R, ⟨P, hP, rfl⟩, h⟩

/-- ✱160·42. \(\vdash .(P\unicode{x2909}Q)\mid S=P\mid S\unicode{x228d} Q\mid S\unicode{x228d} CʻP\uparrow \breve{S} ʻʻCʻQ\) -/
theorem pm160_42 {α β : Type*} {P Q : α → α → Prop} {S : α → β → Prop} :
    (P ⤉ Q) ⨾ S = P ⨾ S ⊍ Q ⨾ S ⊍ cross (fld P) (S˘ ʻʻ fld Q) := by
  bsimp
  grind

/-- ✱160·421. \(\vdash .S\mid (P\unicode{x2909}Q)=S\mid P\unicode{x228d} S\mid Q\unicode{x228d} SʻʻCʻP\uparrow CʻQ\) -/
theorem pm160_421 {α β : Type*} {P Q : α → α → Prop} {S : β → α → Prop} :
    S ⨾ (P ⤉ Q) = S ⨾ P ⊍ S ⨾ Q ⊍ cross (S ʻʻ fld P) (fld Q) := by
  bsimp
  grind

/-- ✱160·43. \(\vdash .S^{;}(P\unicode{x2909}Q)=S^{;}P\unicode{x228d} S^{;}Q\unicode{x228d} SʻʻCʻP\uparrow SʻʻCʻQ\) -/
theorem pm160_43 {α β : Type*} {S : α → β → Prop} {P Q : β → β → Prop} :
    S ⁏ (P ⤉ Q) = S ⁏ P ⊍ S ⁏ Q ⊍ cross (S ʻʻ fld P) (S ʻʻ fld Q) := by
  bsimp
  grind

/-- ✱160·44. \(\vdash :CʻP\subset \text{ᗡ}ʻS.CʻQ\subset \text{ᗡ}ʻS.\supset .S^{;}(P\unicode{x2909}Q)=S^{;}P\unicode{x2909}S^{;}Q\) -/
theorem pm160_44 {α β : Type*} {S : α → β → Prop} {P Q : β → β → Prop} :
    fld P ⊆ codom S ∧ fld Q ⊆ codom S → S ⁏ (P ⤉ Q) = S ⁏ P ⤉ S ⁏ Q := by
  rintro ⟨hP, hQ⟩
  rw [pm160_43, rsum, fld_semi_of hP, fld_semi_of hQ]

/-- ✱160·45. \[\begin{align}\vdash :S\upharpoonright (CʻP'\cup CʻQ')\in 1\rightarrow 1.&S\upharpoonright CʻP'\in P\,\overline{\text{smor}}\,P'.S\upharpoonright CʻQ'\in Q\overline{\text{smor}} Q'.\supset .\\ &S\upharpoonright Cʻ(P'\unicode{x2909}Q')\in (P\unicode{x2909}Q)\overline{\text{smor}} (P'\unicode{x2909}Q')\end{align}\] -/
theorem pm160_45 {α β : Type*} {P Q : α → α → Prop} {P' Q' : β → β → Prop} {S : α → β → Prop} :
    (S ↾ (fld P' ∪ fld Q') ∈ arrow one one ∧ S ↾ fld P' ∈ smorbar P P') ∧
        S ↾ fld Q' ∈ smorbar Q Q' →
      S ↾ fld (P' ⤉ Q') ∈ smorbar (P ⤉ Q) (P' ⤉ Q') := by
  rintro ⟨⟨h1, ⟨-, hc1⟩, e1⟩, ⟨-, hc2⟩, e2⟩
  rw [codom_cres_eq] at hc1 hc2
  have hf := fld_rsum P' Q'
  refine ⟨⟨by rw [hf]; exact h1, ?_⟩, ?_⟩
  · rw [codom_cres_eq, hf]; exact Set.union_subset hc1 hc2
  · rw [cres_semi_of Set.Subset.rfl, pm160_44 ⟨hc1, hc2⟩, e1, e2, cres_semi_of Set.Subset.rfl,
      cres_semi_of Set.Subset.rfl]

/-- ✱160·451. \[\begin{align}\vdash :S\upharpoonright CʻP'\in P\overline{\text{smor}} &P'.S\upharpoonright CʻQ'\in Q\overline{\text{smor}} Q'.Sʻʻ(CʻP'-CʻQ')\cap CʻQ=\Lambda .\\ &\supset .S\upharpoonright Cʻ(P'\unicode{x2909}Q')\in (P\unicode{x2909}Q)\overline{\text{smor}} (P'\unicode{x2909}Q')\end{align}\] -/
theorem pm160_451 {α β : Type*} {P Q : α → α → Prop} {P' Q' : β → β → Prop} {S : α → β → Prop} :
    (S ↾ fld P' ∈ smorbar P P' ∧ S ↾ fld Q' ∈ smorbar Q Q') ∧
        (S ʻʻ (fld P' \ fld Q')) ∩ fld Q = Λ →
      S ↾ fld (P' ⤉ Q') ∈ smorbar (P ⤉ Q) (P' ⤉ Q') := by
  rintro ⟨⟨h1, h2⟩, h3⟩
  refine pm160_45 ⟨⟨?_, h1⟩, h2⟩
  obtain ⟨⟨o1, hc1⟩, e1⟩ := h1
  obtain ⟨⟨o2, hc2⟩, e2⟩ := h2
  rw [codom_cres_eq] at hc1 hc2
  have hQ : fld Q = S ʻʻ fld Q' := by
    rw [e2, cres_semi_of Set.Subset.rfl, fld_semi_of hc2]
  rw [oneone_iff] at *
  refine ⟨?_, ?_⟩
  · rintro x y z ⟨⟨hx, hz⟩, ⟨hy, -⟩⟩
    rcases hz with hz | hz
    · exact o1.1 x y z ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩
    · exact o2.1 x y z ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩
  · rintro x y z ⟨⟨hy, hy'⟩, ⟨hz, hz'⟩⟩
    have key : ∀ u v, u ∈ fld P' → v ∈ fld Q' → S x u → S x v → u = v := by
      intro u v hu hv hxu hxv
      by_cases hv' : v ∈ fld P'
      · exact o1.2 x u v ⟨⟨hxu, hu⟩, ⟨hxv, hv'⟩⟩
      · by_cases hu' : u ∈ fld Q'
        · exact o2.2 x u v ⟨⟨hxu, hu'⟩, ⟨hxv, hv⟩⟩
        · exfalso
          refine not_mem_of_disj h3 ⟨u, ⟨hu, hu'⟩, hxu⟩ ?_
          rw [hQ]; exact ⟨v, hv, hxv⟩
    rcases hy' with hy' | hy' <;> rcases hz' with hz' | hz'
    · exact o1.2 x y z ⟨⟨hy, hy'⟩, ⟨hz, hz'⟩⟩
    · exact key y z hy' hz' hy hz
    · exact (key z y hz' hy' hz hy).symm
    · exact o2.2 x y z ⟨⟨hy, hy'⟩, ⟨hz, hz'⟩⟩

/-- ✱160·452. \[\begin{align}\vdash :S\upharpoonright CʻP'\in P\,\overline{\text{smor}}\,P'.&S\upharpoonright CʻQ'\in Q\overline{\text{smor}} Q'.CʻP\cap CʻQ=\Lambda .\supset .\\ &S\upharpoonright Cʻ(P'\unicode{x2909}Q')\in (P\unicode{x2909}Q)\overline{\text{smor}} (P'\unicode{x2909}Q')\end{align}\] -/
theorem pm160_452 {α β : Type*} {P Q : α → α → Prop} {P' Q' : β → β → Prop} {S : α → β → Prop} :
    (S ↾ fld P' ∈ smorbar P P' ∧ S ↾ fld Q' ∈ smorbar Q Q') ∧ fld P ∩ fld Q = Λ →
      S ↾ fld (P' ⤉ Q') ∈ smorbar (P ⤉ Q) (P' ⤉ Q') := by
  rintro ⟨⟨h1, h2⟩, h3⟩
  refine pm160_451 ⟨⟨h1, h2⟩, ?_⟩
  have hP : fld P = S ʻʻ fld P' := by
    rw [h1.2, cres_semi_of Set.Subset.rfl, fld_semi_of (codom_cres_eq.1 h1.1.2)]
  ext x
  simp only [Null_eq_empty, Set.mem_empty_iff_false, iff_false, Set.mem_inter_iff, not_and]
  rintro ⟨u, ⟨hu, -⟩, hxu⟩ hx
  exact not_mem_of_disj h3 (by rw [hP]; exact ⟨u, hu, hxu⟩) hx

/-- ✱160·46. \[\begin{align}\vdash :CʻP=\text{ᗡ}ʻS.CʻQ=\text{ᗡ}ʻT.CʻP\cap Cʻ&Q=\Lambda .\supset .\\ &(S\unicode{x228d} T)^{;}(P\unicode{x2909}Q)=S^{;}P\unicode{x2909}T^{;}Q\end{align}\] -/
theorem pm160_46 {α β : Type*} {P Q : β → β → Prop} {S T : α → β → Prop} :
    (fld P = codom S ∧ fld Q = codom T) ∧ fld P ∩ fld Q = Λ →
      (S ⊍ T) ⁏ (P ⤉ Q) = S ⁏ P ⤉ T ⁏ Q := by
  rintro ⟨⟨h1, h2⟩, h3⟩
  rw [pm160_44 ⟨fun z hz => by rw [codom_rcup, ← h1]; exact Or.inl hz,
    fun z hz => by rw [codom_rcup, ← h2]; exact Or.inr hz⟩]
  rw [rcup_semi_left (fun z hz hT => not_mem_of_disj h3 hz (by rw [h2]; exact hT)), rcup_comm,
    rcup_semi_left (fun z hz hS => not_mem_of_disj h3 (by rw [h1]; exact hS) hz)]

/-- ✱160·47. \[\begin{align}\vdash :CʻP\cap CʻQ=\Lambda .CʻP'\cap CʻQ'=\Lambda .&S\in P\,\overline{\text{smor}}\,P'.T\in Q\overline{\text{smor}} Q'.\supset .\\ &S\unicode{x228d} T\in (P\unicode{x2909}Q)\overline{\text{smor}} (P'\unicode{x2909}Q')\end{align}\] -/
theorem pm160_47 {α β : Type*} {P Q : α → α → Prop} {P' Q' : β → β → Prop} {S T : α → β → Prop} :
    ((fld P ∩ fld Q = Λ ∧ fld P' ∩ fld Q' = Λ) ∧ S ∈ smorbar P P') ∧ T ∈ smorbar Q Q' →
      S ⊍ T ∈ smorbar (P ⤉ Q) (P' ⤉ Q') := by
  rintro ⟨⟨⟨h1, h2⟩, hS⟩, hT⟩
  have dS := dom_of_smorbar hS
  have dT := dom_of_smorbar hT
  obtain ⟨⟨oS, cS⟩, eS⟩ := hS
  obtain ⟨⟨oT, cT⟩, eT⟩ := hT
  refine ⟨⟨oneone_rcup oS oT
    (fun x y z hy hz => not_mem_of_disj h1 (by rw [← dS]; exact ⟨y, hy⟩) (by rw [← dT]; exact ⟨z, hz⟩))
    (fun x y z hx hy => not_mem_of_disj h2 (by rw [cS]; exact ⟨x, hx⟩) (by rw [cT]; exact ⟨y, hy⟩)),
    ?_⟩, ?_⟩
  · rw [fld_rsum, codom_rcup, cS, cT]
  · rw [pm160_46 ⟨⟨cS, cT⟩, h2⟩, eS, eT]

/-- ✱160·48. \[\begin{align}\vdash :CʻP\cap CʻQ=\Lambda .CʻP'\cap &CʻQ'=\Lambda .P\,\text{smor}\,P'.Q\text{smor}Q'.\supset .\\ &P\unicode{x2909}Q\,\text{smor}\,P'\unicode{x2909}Q' \quad[*160·47.*151·12]\end{align}\] -/
theorem pm160_48 {α β : Type*} {P Q : α → α → Prop} {P' Q' : β → β → Prop} :
    ((fld P ∩ fld Q = Λ ∧ fld P' ∩ fld Q' = Λ) ∧ smor P P') ∧ smor Q Q' →
      smor (P ⤉ Q) (P' ⤉ Q') := by
  rintro ⟨⟨h, ⟨S, hS⟩⟩, ⟨T, hT⟩⟩
  exact ⟨S ⊍ T, pm160_47 ⟨⟨h, hS⟩, hT⟩⟩

/-- ✱160·5. \(\vdash :CʻP\cap CʻQ=\Lambda .\supset .(P\unicode{x2909}Q)\unicode{x0294f}CʻP=P.(P\unicode{x2909}Q)\unicode{x0294f}CʻQ=Q\)

The two equations are the product `(P ⤉ Q) ⥏ C'P = P . (P ⤉ Q) ⥏ C'Q = Q`. -/
theorem pm160_5 {α : Type*} {P Q : α → α → Prop} :
    fld P ∩ fld Q = Λ → (P ⤉ Q) ⥏ fld P = P ∧ (P ⤉ Q) ⥏ fld Q = Q := by
  intro h
  constructor
  · refine rel_ext' fun x y => ⟨?_, fun hxy => ⟨⟨mem_fld_l hxy, Or.inl (Or.inl hxy)⟩, mem_fld_r hxy⟩⟩
    rintro ⟨⟨hx, (h1 | h1) | ⟨-, h1⟩⟩, hy⟩
    · exact h1
    · exact absurd (mem_fld_l h1) (not_mem_of_disj h hx)
    · exact absurd h1 (not_mem_of_disj h hy)
  · refine rel_ext' fun x y => ⟨?_, fun hxy => ⟨⟨mem_fld_l hxy, Or.inl (Or.inr hxy)⟩, mem_fld_r hxy⟩⟩
    rintro ⟨⟨hx, (h1 | h1) | ⟨h1, -⟩⟩, hy⟩
    · exact absurd hx (not_mem_of_disj h (mem_fld_l h1))
    · exact h1
    · exact absurd hx (not_mem_of_disj h h1)

/-- ✱160·51. \(\vdash :CʻP\cap CʻQ=\Lambda .\supset .(P\unicode{x2909}Q)^{2}=P^{2}\unicode{x228d} Q^{2}\unicode{x228d} \text{D}ʻP\uparrow CʻQ\unicode{x228d} CʻP\uparrow \text{ᗡ}ʻQ\) -/
theorem pm160_51 {α : Type*} {P Q : α → α → Prop} :
    fld P ∩ fld Q = Λ →
      rsq (P ⤉ Q) = rsq P ⊍ rsq Q ⊍ cross (dom P) (fld Q) ⊍ cross (fld P) (codom Q) := by
  intro h
  refine rel_ext' fun x z => ⟨?_, ?_⟩
  · rintro ⟨y, (h1 | h1) | ⟨h1, h2⟩, (h3 | h3) | ⟨h3, h4⟩⟩
    · exact Or.inl (Or.inl (Or.inl ⟨y, h1, h3⟩))
    · exact absurd (mem_fld_l h3) (not_mem_of_disj h (mem_fld_r h1))
    · exact Or.inl (Or.inr ⟨⟨y, h1⟩, h4⟩)
    · exact absurd (mem_fld_r h1) (not_mem_of_disj h (mem_fld_l h3))
    · exact Or.inl (Or.inl (Or.inr ⟨y, h1, h3⟩))
    · exact absurd (mem_fld_r h1) (not_mem_of_disj h h3)
    · exact absurd h2 (not_mem_of_disj h (mem_fld_l h3))
    · exact Or.inr ⟨h1, ⟨y, h3⟩⟩
    · exact absurd h2 (not_mem_of_disj h h3)
  · rintro (((⟨y, h1, h2⟩ | ⟨y, h1, h2⟩) | ⟨⟨y, h1⟩, h2⟩) | ⟨h1, ⟨y, h2⟩⟩)
    · exact ⟨y, Or.inl (Or.inl h1), Or.inl (Or.inl h2)⟩
    · exact ⟨y, Or.inl (Or.inr h1), Or.inl (Or.inr h2)⟩
    · exact ⟨y, Or.inl (Or.inl h1), Or.inr ⟨mem_fld_r h1, h2⟩⟩
    · exact ⟨y, Or.inr ⟨h1, mem_fld_l h2⟩, Or.inl (Or.inr h2)⟩

/-- ✱160·52. \(\vdash :CʻP\cap CʻQ=\Lambda .CʻP\cap CʻR=\Lambda .P\unicode{x2909}Q=P\unicode{x2909}R.\supset .Q=R\) -/
theorem pm160_52 {α : Type*} {P Q R : α → α → Prop} :
    (fld P ∩ fld Q = Λ ∧ fld P ∩ fld R = Λ) ∧ P ⤉ Q = P ⤉ R → Q = R := by
  rintro ⟨⟨h1, h2⟩, h⟩
  have hf : fld Q = fld R := by
    have e := congrArg fld h
    rw [fld_rsum, fld_rsum] at e
    ext x
    constructor
    · intro hx
      have : x ∈ fld P ∪ fld R := by rw [← e]; exact Or.inr hx
      exact this.resolve_left fun hp => not_mem_of_disj h1 hp hx
    · intro hx
      have : x ∈ fld P ∪ fld Q := by rw [e]; exact Or.inr hx
      exact this.resolve_left fun hp => not_mem_of_disj h2 hp hx
  rw [← (pm160_5 h1).2, ← (pm160_5 h2).2, h, hf]

/-!
## [✱161] Addition of a term to a relation

*(Vol. 2, p. 357)*

> *Summary of* *161.
>
> The addition of a term has two forms, according as it occurs at the beginning or end of the field of the relation in question. If we add first \(x\) and then \(y\) at the end, the result is the same as if we added \(x\downarrow y\) (*161·22); if at the beginning, it is the same as if we added \(y\downarrow x\) (*161·221). The propositions of the present number are all obvious, and offer no difficulties of any kind. As explained in the introduction to this section, we put \[ \begin{aligned} P\unicode{x21f8} x &= P\unicode{x228d} CʻP\uparrow {℩}ʻx \quad\text{Df},\\ x\unicode{x21f7}P &= {℩}ʻx\uparrow CʻP\unicode{x228d} P \quad\text{Df}. \end{aligned} \] Most of the propositions of this number require the hypothesis \(\dot{\exists} !P\), because if \(P = \dot{\Lambda}\), \(P\unicode{x21f8} x = x\unicode{x21f7}P = \dot{\Lambda}\) (*161·2·201). This is connected with the fact that there is no ordinal number 1. Apart from propositions already mentioned, the chief propositions of this number are the following (we omit propositions about \(x\unicode{x21f7}P\) when they are merely analogues of propositions about \(P\unicode{x21f8} x\)):
>
> …

**Lean reading.** `P ⇸ x` is `addLast P x` (`P ∪̇ C'P ↑ ι'x`) and `x ⇷ P` is `addFirst x P`
(`ι'x ↑ C'P ∪̇ P`), with `P : α → α → Prop`, `x : α`; `P ⇸ x ⇸ y` and `x ⇷ y ⇷ P` are bracketed by
`infixl`/`infixr` (✱161·212·213). `ι'x` (printed `℩'x` in places) is `ι x`, `B⃗'P` is
`refs Beg P`, and `B'P` (✱161·15) keeps its description: `Desc Beg (x ⇷ P˘) (fun b => b = x)`.
In ✱161·4·41 `S'x` is a description, `Desc S x (fun u => …)`, with scope the equation; `↓y` is
`coupleR y` (✱55·01, `↓y'x = x ↓ y`). Correlators are heterogeneous (`S : α → β → Prop`). The
proofs of ✱161·301·321 are obtained from ✱161·3·32 by conversion (✱161·12).

**Status.** proved (all propositions; ✱161·01·02·212·213 definition; ✱161·43 proved (reading),
see its docstring)
-/

/-- ✱161·01 (Df). \(P\unicode{x21f8} x = P\unicode{x228d} CʻP\uparrow {℩}ʻx \quad\text{Df}\) -/
theorem pm161_01 {α : Type*} {P : α → α → Prop} {x : α} : P ⇸ x = P ⊍ cross (fld P) (ι x) := rfl

/-- ✱161·02 (Df). \(x\unicode{x21f7}P = {℩}ʻx\uparrow CʻP\unicode{x228d} P \quad\text{Df}\) -/
theorem pm161_02 {α : Type*} {P : α → α → Prop} {x : α} : x ⇷ P = cross (ι x) (fld P) ⊍ P := rfl

/-- ✱161·1. \(\vdash .P\unicode{x21f8} x = P\unicode{x228d} CʻP\uparrow {℩}ʻx \quad[(*161·01)]\) -/
theorem pm161_1 {α : Type*} {P : α → α → Prop} {x : α} : P ⇸ x = P ⊍ cross (fld P) (ι x) := rfl

/-- ✱161·101. \(\vdash .x\unicode{x21f7}P = {℩}ʻx\uparrow CʻP\unicode{x228d} P \quad[(*161·02)]\) -/
theorem pm161_101 {α : Type*} {P : α → α → Prop} {x : α} : x ⇷ P = cross (ι x) (fld P) ⊍ P := rfl

/-- ✱161·11. \(\vdash \colon\ldotp y(P\unicode{x21f8} x)z.\equiv :yPz.\lor.y\in CʻP.z = x \quad[*161·1]\) -/
theorem pm161_11 {α : Type*} {P : α → α → Prop} {x y z : α} :
    (P ⇸ x) y z ↔ P y z ∨ y ∈ fld P ∧ z = x := Iff.rfl

/-- ✱161·111. \(\vdash \colon\ldotp y(x\unicode{x21f7}P)z.\equiv :y=x.z\in CʻP.\lor.yPz \quad[*161·101]\) -/
theorem pm161_111 {α : Type*} {P : α → α → Prop} {x y z : α} :
    (x ⇷ P) y z ↔ (y = x ∧ z ∈ fld P) ∨ P y z := Iff.rfl

/-- ✱161·12. \(\vdash .x\unicode{x21f7}P=\text{Cnv}ʻ(\breve{P} \unicode{x21f8} x) \quad[*161·1·101.*35·84.*33·22]\) -/
theorem pm161_12 {α : Type*} {P : α → α → Prop} {x : α} : x ⇷ P = (P˘ ⇸ x)˘ := by
  refine rel_ext' fun y z => ?_
  show (y ∈ ι x ∧ z ∈ fld P) ∨ P y z ↔ P y z ∨ z ∈ fld P˘ ∧ y ∈ ι x
  rw [fld_cnv']
  tauto

/-- ✱161·13. \(\vdash .\text{D}ʻ(P\unicode{x21f8} x)=CʻP.\text{ᗡ}ʻ(x\unicode{x21f7}P)=CʻP\) -/
theorem pm161_13 {α : Type*} {P : α → α → Prop} {x : α} :
    dom (P ⇸ x) = fld P ∧ codom (x ⇷ P) = fld P := by
  constructor
  · ext y
    constructor
    · rintro ⟨z, h | ⟨h, -⟩⟩
      exacts [mem_fld_l h, h]
    · intro h; exact ⟨x, Or.inr ⟨h, mem_unitCls.2 rfl⟩⟩
  · ext y
    constructor
    · rintro ⟨z, ⟨-, h⟩ | h⟩
      exacts [h, mem_fld_r h]
    · intro h; exact ⟨x, Or.inl ⟨mem_unitCls.2 rfl, h⟩⟩

/-- ✱161·131. \[\begin{align}&\vdash :\dot{\exists} !P.\supset .\text{ᗡ}ʻ(P\unicode{x21f8} x)=\text{ᗡ}ʻP\cup \iota ʻx.\text{D}ʻ(x\unicode{x21f7}P)=\text{D}ʻP\cup \iota ʻx\\ &[*35·86.*161·1]\end{align}\] -/
theorem pm161_131 {α : Type*} {P : α → α → Prop} {x : α} :
    rEx P → codom (P ⇸ x) = codom P ∪ ι x ∧ dom (x ⇷ P) = dom P ∪ ι x := by
  rintro ⟨a, b, hab⟩
  constructor
  · ext y
    constructor
    · rintro ⟨z, h | ⟨-, h⟩⟩
      exacts [Or.inl ⟨z, h⟩, Or.inr h]
    · rintro (⟨z, h⟩ | h)
      exacts [⟨z, Or.inl h⟩, ⟨a, Or.inr ⟨mem_fld_l hab, h⟩⟩]
  · ext y
    constructor
    · rintro ⟨z, ⟨h, -⟩ | h⟩
      exacts [Or.inr h, Or.inl ⟨z, h⟩]
    · rintro (⟨z, h⟩ | h)
      exacts [⟨z, Or.inr h⟩, ⟨a, Or.inl ⟨h, mem_fld_l hab⟩⟩]

/-- ✱161·14. \(\vdash :\dot{\exists} !P.\supset .Cʻ(P\unicode{x21f8} x)=CʻP\cup \iota ʻx=Cʻ(x\unicode{x21f7}P) \quad[*161·13·131]\) -/
theorem pm161_14 {α : Type*} {P : α → α → Prop} {x : α} :
    rEx P → fld (P ⇸ x) = fld P ∪ ι x ∧ fld P ∪ ι x = fld (x ⇷ P) := fun h =>
  ⟨fld_addLast h x, (fld_addFirst h x).symm⟩

/-- ✱161·141. \[\begin{align}&\vdash :\dot{\exists} !P.\supset .\overrightarrow{B}ʻ(P\unicode{x21f8} x)=\overrightarrow{B}ʻP-\iota ʻx.\overrightarrow{B}ʻ\text{Cnv}ʻ(P\unicode{x21f8} x)=\iota ʻx-CʻP\\ &[*161·13·131.*93·101]\end{align}\] -/
theorem pm161_141 {α : Type*} {P : α → α → Prop} {x : α} :
    rEx P → refs Beg (P ⇸ x) = refs Beg P \ ι x ∧ refs Beg (P ⇸ x)˘ = ι x \ fld P := by
  intro h
  obtain ⟨h1, -⟩ := pm161_13 (P := P) (x := x)
  obtain ⟨h2, -⟩ := pm161_131 (x := x) h
  constructor
  · ext y
    show y ∈ dom (P ⇸ x) \ codom (P ⇸ x) ↔ (y ∈ dom P \ codom P) ∧ y ∉ ι x
    rw [h1, h2]
    simp only [Set.mem_sdiff, Set.mem_union, not_or]
    constructor
    · rintro ⟨⟨z, hz | hz⟩, hc, hx⟩
      exacts [⟨⟨⟨z, hz⟩, hc⟩, hx⟩, absurd ⟨z, hz⟩ hc]
    · rintro ⟨⟨⟨z, hz⟩, hc⟩, hx⟩
      exact ⟨mem_fld_l hz, hc, hx⟩
  · ext y
    show y ∈ codom (P ⇸ x) \ dom (P ⇸ x) ↔ y ∈ ι x \ fld P
    rw [h1, h2]
    simp only [Set.mem_sdiff, Set.mem_union]
    constructor
    · rintro ⟨⟨z, hz⟩ | hx, hf⟩
      exacts [absurd (mem_fld_r hz) hf, ⟨hx, hf⟩]
    · rintro ⟨hx, hf⟩
      exact ⟨Or.inr hx, hf⟩

/-- ✱161·15. \[\begin{align}&\vdash :\dot{\exists} !P.x{\sim}\in CʻP.\supset .\\ &\overrightarrow{B}ʻ(P\unicode{x21f8} x)=\overrightarrow{B}ʻP.\overrightarrow{B}ʻ\text{Cnv}ʻ(P\unicode{x21f8} x)=\iota ʻx.Bʻ(x\unicode{x21f7}\breve{P} )=x \quad[*161·141]\end{align}\]

`B'(x ⇷ P̆)` keeps its description (PM proves its value): `Desc Beg (x ⇷ P˘) (fun b => b = x)`. -/
theorem pm161_15 {α : Type*} {P : α → α → Prop} {x : α} :
    rEx P ∧ x ∉ fld P →
      (refs Beg (P ⇸ x) = refs Beg P ∧ refs Beg (P ⇸ x)˘ = ι x) ∧
        Desc Beg (x ⇷ P˘) (fun b => b = x) := by
  rintro ⟨h, hx⟩
  obtain ⟨e1, e2⟩ := pm161_141 (x := x) h
  have e2' : refs Beg (P ⇸ x)˘ = ι x := by
    rw [e2]
    ext y
    constructor
    · exact fun hy => hy.1
    · intro hy
      rw [mem_unitCls] at hy
      subst hy
      exact ⟨mem_unitCls.2 rfl, hx⟩
  refine ⟨⟨?_, e2'⟩, ?_⟩
  · rw [e1]
    ext y
    constructor
    · exact fun hy => hy.1
    · intro hy
      refine ⟨hy, fun e => ?_⟩
      rw [mem_unitCls] at e
      subst e
      exact hx (mem_fld_l hy.1.choose_spec)
  · have e3 : x ⇷ P˘ = (P ⇸ x)˘ := pm161_12
    refine (TheIs_iff_of_unique (b := x) fun y => ?_).2 rfl
    have := Set.ext_iff.1 e2' y
    rw [e3]
    exact this.trans mem_unitCls

/-- ✱161·16. \(\vdash :x{\sim}\in CʻP.\supset .(P\unicode{x21f8} x)\unicode{x0294f}CʻP=(P\unicode{x21f8} x)\unicode{x0294f}(-\iota ʻx)=P \quad[*161·1]\) -/
theorem pm161_16 {α : Type*} {P : α → α → Prop} {x : α} :
    x ∉ fld P → (P ⇸ x) ⥏ fld P = (P ⇸ x) ⥏ (ι x)ᶜ ∧ (P ⇸ x) ⥏ (ι x)ᶜ = P := by
  intro hx
  have ne : ∀ y, y ∈ fld P → y ≠ x := fun y hy e => hx (e ▸ hy)
  constructor
  · refine rel_ext' fun y z => ?_
    show ((y ∈ fld P ∧ (P ⇸ x) y z) ∧ z ∈ fld P) ↔ ((y ∉ ι x ∧ (P ⇸ x) y z) ∧ z ∉ ι x)
    rw [addLast_apply, mem_unitCls, mem_unitCls]
    constructor
    · rintro ⟨⟨hy, h⟩, hz⟩
      exact ⟨⟨ne y hy, h⟩, ne z hz⟩
    · rintro ⟨⟨hy, h | ⟨-, e⟩⟩, hz⟩
      · exact ⟨⟨mem_fld_l h, Or.inl h⟩, mem_fld_r h⟩
      · exact absurd e hz
  · refine rel_ext' fun y z => ?_
    show ((y ∉ ι x ∧ (P ⇸ x) y z) ∧ z ∉ ι x) ↔ P y z
    rw [addLast_apply, mem_unitCls, mem_unitCls]
    constructor
    · rintro ⟨⟨hy, h | ⟨-, e⟩⟩, hz⟩
      exacts [h, absurd e hz]
    · intro h
      exact ⟨⟨ne y (mem_fld_l h), Or.inl h⟩, ne z (mem_fld_r h)⟩

/-- ✱161·161. \(\vdash :x{\sim}\in CʻP.\supset .(x\unicode{x21f7}P)\unicode{x0294f}CʻP=(x\unicode{x21f7}P)\unicode{x0294f}(-\iota ʻx)=P\) -/
theorem pm161_161 {α : Type*} {P : α → α → Prop} {x : α} :
    x ∉ fld P → (x ⇷ P) ⥏ fld P = (x ⇷ P) ⥏ (ι x)ᶜ ∧ (x ⇷ P) ⥏ (ι x)ᶜ = P := by
  intro hx
  have ne : ∀ y, y ∈ fld P → y ≠ x := fun y hy e => hx (e ▸ hy)
  constructor
  · refine rel_ext' fun y z => ?_
    show ((y ∈ fld P ∧ (x ⇷ P) y z) ∧ z ∈ fld P) ↔ ((y ∉ ι x ∧ (x ⇷ P) y z) ∧ z ∉ ι x)
    rw [addFirst_apply, mem_unitCls, mem_unitCls]
    constructor
    · rintro ⟨⟨hy, h⟩, hz⟩
      exact ⟨⟨ne y hy, h⟩, ne z hz⟩
    · rintro ⟨⟨hy, ⟨e, -⟩ | h⟩, hz⟩
      · exact absurd e hy
      · exact ⟨⟨mem_fld_l h, Or.inr h⟩, mem_fld_r h⟩
  · refine rel_ext' fun y z => ?_
    show ((y ∉ ι x ∧ (x ⇷ P) y z) ∧ z ∉ ι x) ↔ P y z
    rw [addFirst_apply, mem_unitCls, mem_unitCls]
    constructor
    · rintro ⟨⟨hy, ⟨e, -⟩ | h⟩, hz⟩
      exacts [absurd e hy, h]
    · intro h
      exact ⟨⟨ne y (mem_fld_l h), Or.inr h⟩, ne z (mem_fld_r h)⟩

/-- ✱161·2. \(\vdash .\dot{\Lambda} \unicode{x21f8} x=\dot{\Lambda} \quad[*35·75·82.*161·1]\) -/
theorem pm161_2 {α : Type*} {x : α} : (rNull : α → α → Prop) ⇸ x = rNull :=
  addLast_rNull x

/-- ✱161·201. \(\vdash .x\unicode{x21f7}\dot{\Lambda} =\dot{\Lambda}\) -/
theorem pm161_201 {α : Type*} {x : α} : x ⇷ (rNull : α → α → Prop) = rNull :=
  addFirst_rNull x

/-- ✱161·21. \(\vdash .(x\downarrow y)\unicode{x21f8} z=x\downarrow y\unicode{x228d} x\downarrow z\unicode{x228d} y\downarrow z\) -/
theorem pm161_21 {α : Type*} {x y z : α} : (x ↓ y) ⇸ z = x ↓ y ⊍ x ↓ z ⊍ y ↓ z := by
  asimp
  intro u v; tauto

/-- ✱161·211. \[\begin{align}&\vdash .x\unicode{x21f7}(y\downarrow z)=x\downarrow y\unicode{x228d} x\downarrow z\unicode{x228d} y\downarrow z=(x\downarrow y)\unicode{x21f8} z\\ &[\text{Proof as in *161·21}]\end{align}\] -/
theorem pm161_211 {α : Type*} {x y z : α} :
    x ⇷ (y ↓ z) = x ↓ y ⊍ x ↓ z ⊍ y ↓ z ∧ x ↓ y ⊍ x ↓ z ⊍ y ↓ z = (x ↓ y) ⇸ z := by
  constructor <;> asimp <;> intro u v <;> tauto

/-- ✱161·212 (Df). \(P\unicode{x21f8} x\unicode{x21f8} y=(P\unicode{x21f8} x)\unicode{x21f8} y \quad\text{Df}\) -/
theorem pm161_212 {α : Type*} {P : α → α → Prop} {x y : α} : P ⇸ x ⇸ y = (P ⇸ x) ⇸ y := rfl

/-- ✱161·213 (Df). \(x\unicode{x21f7}y\unicode{x21f7}P=x\unicode{x21f7}(y\unicode{x21f7}P) \quad\text{Df}\) -/
theorem pm161_213 {α : Type*} {P : α → α → Prop} {x y : α} : x ⇷ y ⇷ P = x ⇷ (y ⇷ P) := rfl

/-- ✱161·22. \(\vdash :\dot{\exists} !P.\supset .(P\unicode{x21f8} x)\unicode{x21f8} y=P\unicode{x2909}(x\downarrow y)\) -/
theorem pm161_22 {α : Type*} {P : α → α → Prop} {x y : α} :
    rEx P → (P ⇸ x) ⇸ y = P ⤉ (x ↓ y) := by
  intro h
  asimp
  simp only [fld_addLast h, Set.mem_union, mem_unitCls]
  intro u v; tauto

/-- ✱161·221. \(\vdash :\dot{\exists} !P.\supset .x\unicode{x21f7}(y\unicode{x21f7}P)=(x\downarrow y)\unicode{x2909}P\) -/
theorem pm161_221 {α : Type*} {P : α → α → Prop} {x y : α} :
    rEx P → x ⇷ (y ⇷ P) = (x ↓ y) ⤉ P := by
  intro h
  asimp
  simp only [fld_addFirst h, Set.mem_union, mem_unitCls]
  intro u v; tauto

/-- ✱161·23. \(\vdash :\dot{\exists} !Q.\supset .(P\unicode{x2909}Q)\unicode{x21f8} y=P\unicode{x2909}(Q\unicode{x21f8} y)\) -/
theorem pm161_23 {α : Type*} {P Q : α → α → Prop} {y : α} :
    rEx Q → (P ⤉ Q) ⇸ y = P ⤉ (Q ⇸ y) := by
  intro h
  asimp
  simp only [fld_addLast h, Set.mem_union, mem_unitCls]
  intro u v; tauto

/-- ✱161·231. \(\vdash :\dot{\exists} !P.\supset .x\unicode{x21f7}(P\unicode{x2909}Q)=(x\unicode{x21f7}P)\unicode{x2909}Q\) -/
theorem pm161_231 {α : Type*} {P Q : α → α → Prop} {x : α} :
    rEx P → x ⇷ (P ⤉ Q) = (x ⇷ P) ⤉ Q := by
  intro h
  asimp
  simp only [fld_addFirst h, Set.mem_union, mem_unitCls]
  intro u v; tauto

/-- ✱161·232. \(\vdash :\dot{\exists} !P.\dot{\exists} !Q.\supset .P\unicode{x2909}(x\unicode{x21f7}Q)=(P\unicode{x21f8} x)\unicode{x2909}Q\) -/
theorem pm161_232 {α : Type*} {P Q : α → α → Prop} {x : α} :
    rEx P ∧ rEx Q → P ⤉ (x ⇷ Q) = (P ⇸ x) ⤉ Q := by
  rintro ⟨hP, hQ⟩
  asimp
  simp only [fld_addFirst hQ, fld_addLast hP, Set.mem_union, mem_unitCls]
  intro u v; tauto

/-- ✱161·24. \(\vdash .x\unicode{x21f7}(P\unicode{x21f8} y)=(x\unicode{x21f7}P)\unicode{x21f8} y\) -/
theorem pm161_24 {α : Type*} {P : α → α → Prop} {x y : α} : x ⇷ (P ⇸ y) = (x ⇷ P) ⇸ y := by
  by_cases h : rEx P
  · asimp
    simp only [fld_addFirst h, fld_addLast h, Set.mem_union, mem_unitCls]
    intro u v; tauto
  · rw [eq_rNull_of_not_rEx h, addLast_rNull, addFirst_rNull, addLast_rNull]

/-- ✱161·25. \(\vdash :\dot{\exists} !P.\dot{\exists} !Q.\supset .(P \unicode{x21f8} x) \unicode{x2909} (y \unicode{x21f7} Q) = P \unicode{x2909} (x\downarrow y) \unicode{x2909} Q\) -/
theorem pm161_25 {α : Type*} {P Q : α → α → Prop} {x y : α} :
    rEx P ∧ rEx Q → (P ⇸ x) ⤉ (y ⇷ Q) = P ⤉ (x ↓ y) ⤉ Q := by
  rintro ⟨hP, hQ⟩
  asimp
  simp only [fld_addFirst hQ, fld_addLast hP, Set.mem_union, mem_unitCls]
  intro u v; tauto

/-- ✱161·26. \[\begin{align}\vdash . x \unicode{x21f7} \{y \unicode{x21f7} (z\downarrow w)\} &= (x\downarrow y) \unicode{x2909} (z\downarrow w) = \{(x\downarrow y) \unicode{x21f8} z\} \unicode{x21f8} w\\ &= \{x \unicode{x21f7} (y\downarrow z)\} \unicode{x21f8} w\end{align}\]

The three equations form a chain: the conjunction of its links. -/
theorem pm161_26 {α : Type*} {x y z w : α} :
    (x ⇷ (y ⇷ (z ↓ w)) = (x ↓ y) ⤉ (z ↓ w) ∧ (x ↓ y) ⤉ (z ↓ w) = ((x ↓ y) ⇸ z) ⇸ w) ∧
      ((x ↓ y) ⇸ z) ⇸ w = (x ⇷ (y ↓ z)) ⇸ w := by
  have hzw : rEx (z ↓ w) := ⟨z, w, rfl, rfl⟩
  have hxy : rEx (x ↓ y) := ⟨x, y, rfl, rfl⟩
  have hyz : rEx (y ↓ z) := ⟨y, z, rfl, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · asimp
    simp only [fld_addFirst hzw, fld_couple, Set.mem_union, mem_unitCls]
    intro u v; tauto
  · asimp
    simp only [fld_addLast hxy, fld_couple, Set.mem_union, mem_unitCls]
    intro u v; tauto
  · asimp
    simp only [fld_addLast hxy, fld_addFirst hyz, fld_couple, Set.mem_union, mem_unitCls]
    intro u v; tauto

/-- ✱161·3. \[\begin{align}\vdash : \dot{\exists} !Q . S\in P \overline{\text{smor}} Q . x{\sim}\in CʻP . &y{\sim}\in CʻQ. \supset .\\ &S \unicode{x228d} x\downarrow y\in (P \unicode{x21f8} x) \overline{\text{smor}} (Q \unicode{x21f8} y)\end{align}\] -/
theorem pm161_3 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} {x : α}
    {y : β} :
    ((rEx Q ∧ S ∈ smorbar P Q) ∧ x ∉ fld P) ∧ y ∉ fld Q →
      S ⊍ x ↓ y ∈ smorbar (P ⇸ x) (Q ⇸ y) :=
  addLast_smorbar

/-- ✱161·301. \[\begin{align}\vdash : \dot{\exists} !Q. S\in P \overline{\text{smor}} Q. x{\sim}\in CʻP. &y{\sim}\in CʻQ. \supset .\\ &x\downarrow y \unicode{x228d} S\in (x \unicode{x21f7} P) \overline{\text{smor}} (y \unicode{x21f7} Q)\end{align}\] -/
theorem pm161_301 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} {x : α}
    {y : β} :
    ((rEx Q ∧ S ∈ smorbar P Q) ∧ x ∉ fld P) ∧ y ∉ fld Q →
      x ↓ y ⊍ S ∈ smorbar (x ⇷ P) (y ⇷ Q) := by
  rintro ⟨⟨⟨hQ, hS⟩, hx⟩, hy⟩
  have h := addLast_smorbar (P := P˘) (Q := Q˘) (x := x) (y := y)
    ⟨⟨⟨⟨hQ.choose_spec.choose, hQ.choose, hQ.choose_spec.choose_spec⟩, smorbar_cnv hS⟩,
      by rw [fld_cnv']; exact hx⟩, by rw [fld_cnv']; exact hy⟩
  rw [rcup_comm, pm161_12, pm161_12]
  exact smorbar_cnv h

/-- ✱161·31. \[\begin{align}\vdash : P \,\text{smor} \,Q. x{\sim}\in CʻP. &y{\sim}\in CʻQ. \supset .\\ &P \unicode{x21f8} x \,\text{smor}\, Q \unicode{x21f8} y. x \unicode{x21f7} P \,\text{smor}\, y \unicode{x21f7} Q\end{align}\] -/
theorem pm161_31 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {x : α} {y : β} :
    (smor P Q ∧ x ∉ fld P) ∧ y ∉ fld Q → smor (P ⇸ x) (Q ⇸ y) ∧ smor (x ⇷ P) (y ⇷ Q) := by
  rintro ⟨⟨⟨S, hS⟩, hx⟩, hy⟩
  by_cases hQ : rEx Q
  · exact ⟨⟨_, pm161_3 ⟨⟨⟨hQ, hS⟩, hx⟩, hy⟩⟩, ⟨_, pm161_301 ⟨⟨⟨hQ, hS⟩, hx⟩, hy⟩⟩⟩
  · have hQ' := eq_rNull_of_not_rEx hQ
    have hP : P = rNull := by rw [hS.2, hQ', semi_rNull]
    rw [hP, hQ', addLast_rNull, addLast_rNull, addFirst_rNull, addFirst_rNull]
    exact ⟨smor_rNull, smor_rNull⟩

/-- ✱161·32. \[\begin{align}\vdash : \dot{\exists} !Q. x{\sim}\in CʻP. y{\sim}\in CʻQ. &S\in (P \unicode{x21f8} x) \overline{\text{smor}} (Q \unicode{x21f8} y). \supset .\\ &S\upharpoonright (-\iota ʻy)\in P \overline{\text{smor}} Q. xSy\end{align}\] -/
theorem pm161_32 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} {x : α}
    {y : β} :
    ((rEx Q ∧ x ∉ fld P) ∧ y ∉ fld Q) ∧ S ∈ smorbar (P ⇸ x) (Q ⇸ y) →
      S ↾ (ι y)ᶜ ∈ smorbar P Q ∧ S x y :=
  smorbar_of_addLast

/-- ✱161·321. \[\begin{align}\vdash : \dot{\exists} !Q. x{\sim}\in CʻP. y{\sim}\in CʻQ. &S\in (x \unicode{x21f7} P) \overline{\text{smor}} (y \unicode{x21f7} Q). \supset .\\ &S\upharpoonright (-\iota ʻy)\in P \overline{\text{smor}} Q. xSy\end{align}\] -/
theorem pm161_321 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop} {x : α}
    {y : β} :
    ((rEx Q ∧ x ∉ fld P) ∧ y ∉ fld Q) ∧ S ∈ smorbar (x ⇷ P) (y ⇷ Q) →
      S ↾ (ι y)ᶜ ∈ smorbar P Q ∧ S x y := by
  rintro ⟨⟨⟨hQ, hx⟩, hy⟩, hS⟩
  rw [pm161_12, pm161_12] at hS
  have h := smorbar_of_addLast (P := P˘) (Q := Q˘)
    ⟨⟨⟨⟨hQ.choose_spec.choose, hQ.choose, hQ.choose_spec.choose_spec⟩,
      by rw [fld_cnv']; exact hx⟩, by rw [fld_cnv']; exact hy⟩, smorbar_cnv hS⟩
  exact ⟨smorbar_cnv h.1, h.2⟩

/-- ✱161·33. \[\begin{align}\vdash \colon\ldotp x&{\sim}\in CʻP. y{\sim}\in CʻQ. \supset :\\ &P \,\text{smor} \,Q. \equiv . (P \unicode{x21f8} x) \text{smor} (Q \unicode{x21f8} y). \equiv . (x \unicode{x21f7} P) \text{smor} (y \unicode{x21f7} Q)\\ &[*161·31·32·321·2·201. *153·101]\end{align}\]

The chain `≡ . ≡` is the conjunction of its links. -/
theorem pm161_33 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {x : α} {y : β} :
    x ∉ fld P ∧ y ∉ fld Q →
      (smor P Q ↔ smor (P ⇸ x) (Q ⇸ y)) ∧ (smor (P ⇸ x) (Q ⇸ y) ↔ smor (x ⇷ P) (y ⇷ Q)) := by
  rintro ⟨hx, hy⟩
  by_cases hQ : rEx Q
  · have a : smor (P ⇸ x) (Q ⇸ y) → smor P Q := fun ⟨S, hS⟩ =>
      ⟨_, (pm161_32 ⟨⟨⟨hQ, hx⟩, hy⟩, hS⟩).1⟩
    have b : smor (x ⇷ P) (y ⇷ Q) → smor P Q := fun ⟨S, hS⟩ =>
      ⟨_, (pm161_321 ⟨⟨⟨hQ, hx⟩, hy⟩, hS⟩).1⟩
    have c := fun h : smor P Q => pm161_31 ⟨⟨h, hx⟩, hy⟩
    exact ⟨⟨fun h => (c h).1, a⟩, ⟨fun h => (c (a h)).2, fun h => (c (b h)).1⟩⟩
  · have hQ' := eq_rNull_of_not_rEx hQ
    rw [hQ', addLast_rNull, addFirst_rNull, smor_rNull_iff, smor_rNull_iff, smor_rNull_iff,
      addLast_eq_rNull_iff, addFirst_eq_rNull_iff]
    exact ⟨Iff.rfl, Iff.rfl⟩

/-- ✱161·4. \(\vdash : CʻQ \subset \text{ᗡ}ʻS. x\in \text{ᗡ}ʻS. S\in 1\rightarrow \text{Cls}. \supset . S^{;}(Q \unicode{x21f8} x) = S^{;}Q \unicode{x21f8} Sʻx\)

`S'x` is a description; its scope is the equation. -/
theorem pm161_4 {α β : Type*} {S : α → β → Prop} {Q : β → β → Prop} {x : β} :
    (fld Q ⊆ codom S ∧ x ∈ codom S) ∧ S ∈ arrow one Cls →
      Desc S x (fun u => S ⁏ (Q ⇸ x) = S ⁏ Q ⇸ u) := by
  rintro ⟨⟨hQ, ⟨u, hu⟩⟩, hS⟩
  have huniq : ∀ v, S v x ↔ v = u := fun v =>
    ⟨fun hv => mem_arrow_one_Cls.1 hS v u x ⟨hv, hu⟩, fun e => e ▸ hu⟩
  refine (TheIs_iff_of_unique huniq).2 (rel_ext' fun a b => ?_)
  rw [semi_iff', addLast_apply, fld_semi_of hQ, semi_iff']
  constructor
  · rintro ⟨z, w, h1, h2, h3 | ⟨h3, rfl⟩⟩
    · exact Or.inl ⟨z, w, h1, h2, h3⟩
    · exact Or.inr ⟨⟨z, h3, h1⟩, (huniq b).1 h2⟩
  · rintro (⟨z, w, h1, h2, h3⟩ | ⟨⟨z, h3, h1⟩, rfl⟩)
    · exact ⟨z, w, h1, h2, Or.inl h3⟩
    · exact ⟨z, x, h1, hu, Or.inr ⟨h3, rfl⟩⟩

/-- ✱161·41. \(\vdash : CʻQ \subset \text{ᗡ}ʻS. x\in \text{ᗡ}ʻS. S\in 1\rightarrow \text{Cls}. \supset . S^{;}(x \unicode{x21f7} Q) = Sʻx \unicode{x21f7} S^{;}Q\)

`S'x` is a description; its scope is the equation. -/
theorem pm161_41 {α β : Type*} {S : α → β → Prop} {Q : β → β → Prop} {x : β} :
    (fld Q ⊆ codom S ∧ x ∈ codom S) ∧ S ∈ arrow one Cls →
      Desc S x (fun u => S ⁏ (x ⇷ Q) = u ⇷ S ⁏ Q) := by
  rintro ⟨⟨hQ, ⟨u, hu⟩⟩, hS⟩
  have huniq : ∀ v, S v x ↔ v = u := fun v =>
    ⟨fun hv => mem_arrow_one_Cls.1 hS v u x ⟨hv, hu⟩, fun e => e ▸ hu⟩
  refine (TheIs_iff_of_unique huniq).2 (rel_ext' fun a b => ?_)
  rw [semi_iff', addFirst_apply, fld_semi_of hQ, semi_iff']
  constructor
  · rintro ⟨z, w, h1, h2, ⟨rfl, h3⟩ | h3⟩
    · exact Or.inl ⟨(huniq a).1 h1, ⟨w, h3, h2⟩⟩
    · exact Or.inr ⟨z, w, h1, h2, h3⟩
  · rintro (⟨rfl, ⟨w, h3, h2⟩⟩ | ⟨z, w, h1, h2, h3⟩)
    · exact ⟨x, w, hu, h2, Or.inl ⟨rfl, h3⟩⟩
    · exact ⟨z, w, h1, h2, Or.inr h3⟩

/-- ✱161·42. \(\vdash . \downarrow y^{;}(Q \unicode{x21f8} x) = \downarrow y^{;}Q \unicode{x21f8} (x\downarrow y) \quad[*161·4.*55·21.*72·184]\)

`↓y` is `coupleR y`, so `↓y;Q` is `coupleR y ⁏ Q`. -/
theorem pm161_42 {α β : Type*} {Q : α → α → Prop} {x : α} {y : β} :
    coupleR y ⁏ (Q ⇸ x) = (coupleR y ⁏ Q) ⇸ (x ↓ y) :=
  graph_semi_addLast (fun u : α => u ↓ y) Q x

/-- ✱161·43. \(\vdash . \downarrow y^{;}(x \unicode{x21f7} Q) = (x\downarrow y) \unicode{x21f7} y^{;}Q\)

**Status.** proved (reading): transcription error: the e-text prints `(x↓y) ⇷ y;Q`, which is not
significant (`y` is not a relation); PM's right-hand side is `(x↓y) ⇷ ↓y;Q`, the analogue of
✱161·42. -/
theorem pm161_43 {α β : Type*} {Q : α → α → Prop} {x : α} {y : β} :
    coupleR y ⁏ (x ⇷ Q) = (x ↓ y) ⇷ (coupleR y ⁏ Q) :=
  graph_semi_addFirst (fun u : α => u ↓ y) Q x

/-!
## [✱162] The sum of the relations of a field

*(Vol. 2, p. 362)*

> *Summary of* *162.
>
> The form of summation defined in *160 cannot be extended beyond a finite number of summands, since it involves explicit mention of all the summands. In the present number, we shall be concerned with a form of summation which is not subject to this restriction. It will be observed that, since relational summation is not permutative, we cannot define the sum of a *class* of relations, for this would not determine the order in which the summation is to be effected. Our relations must be given as the field of some relation which orders them; thus the sum appears not as the sum of a class, but as the sum of a relation, namely of a relation whose field is the relations to be summed. In the case of two relations \(Q\) and \(R\), the sum of \(Q\downarrow R\), as defined in the present number, will be equal to \(Q\unicode{x2909}R\); similarly for three, the sum of \(Q\downarrow R\unicode{x228d} Q\downarrow S\unicode{x228d} R\downarrow S\) will be equal to \(Q\unicode{x2909}R\unicode{x2909}S\), and so on for any finite number of summands.
>
> As explained in the introduction to this Section, if P is a relation between relations, we put
>
> …

**Lean reading.** `Σ'P` is `relSigma P` for a relation of relations
`P : (α → α → Prop) → (α → α → Prop) → Prop`; the relation `Σ` is `RelSigma` (`graph relSigma`),
`ṡ` is `sDotRel`, `C`, `D`, `ᗡ`, `F` are the relations of ✱33, so `C''C'P` is `C ʻʻ fld P`,
`F;P` is `F ⁏ P`, `F²` is `F ⨾ F` (the two `F`'s of different types, ✱34·02), and `F⃗²'P` is
`refs (F ⨾ F) P`. `Cnv;P̆` is `Cnv ⁏ P˘` and `R†;Q` is `daggerRel R ⁏ Q`. `−ι'Λ̇` is `(ι rNull)ᶜ`.
Where PM leaves brackets to the types (✱162·372, `Σ'(ι'P) ↑ β`, i.e. `Σ'{(ι'P) ↑ β}`), Lean
writes them. The e-text has transcription errors in ✱162·12 (`Q ⊂̇ C'P` for `Q ∈ C'P`), ✱162·14
(`=` for `≡`), ✱162·332 (`ṡ'C'ṡ'P` for `ṡ'C'ṡ'C'P`) and ✱162·34 (`Σ'Σ;` for `Σ'Σ;P`); they are
read as PM's demonstrations and summary show. (The e-text numbers ✱162·44 `*162.44.`, a full stop
for the centred dot.)

**Status.** proved (all propositions; ✱162·01 definition; ✱162·12·14·332·34 proved (reading),
see their docstrings)
-/

/-- ✱162·01 (Df). \(\Sigma ʻP=\dot{s} ʻCʻP\unicode{x228d} F^{;}P \quad\text{Df}\) -/
theorem pm162_01 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    relSigma P = sumRel (fld P) ⊍ F ⁏ P := rfl

/-- ✱162·1. \(\vdash .\Sigma ʻP=\dot{s} ʻCʻP\unicode{x228d} F^{;}P \quad[(*162·01)]\) -/
theorem pm162_1 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    relSigma P = sumRel (fld P) ⊍ F ⁏ P := rfl

/-- ✱162·11. \(\vdash \colon\ldotp x(\Sigma ʻP)y.\equiv :x(\dot{s} ʻCʻP)y.\lor.x(F^{;}P)y \quad[*162·1]\) -/
theorem pm162_11 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {x y : α} :
    relSigma P x y ↔ sumRel (fld P) x y ∨ (F ⁏ P) x y := Iff.rfl

/-- ✱162·12. \[\begin{align}&\vdash \colon\ldotp x(\Sigma ʻP)y.\equiv :(\exists Q).Q\,\unicode{x2abd}\, CʻP.xQy.\lor.(\exists Q,R).xFQ.yFR.QPR\\ &[*162·1.*41·11.*150·11]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `Q ⊂̇ C'P`, which is not
significant (`C'P` is a class of relations); PM has `Q ∈ C'P`, as in ✱162·13 and in the
proof `[✱162·1.✱41·11.✱150·11]` (`x(ṡ'C'P)y . ≡ . (∃Q) . Q ∈ C'P . xQy`). -/
theorem pm162_12 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {x y : α} :
    relSigma P x y ↔ (∃ Q, Q ∈ fld P ∧ Q x y) ∨ ∃ Q R, (F x Q ∧ F y R) ∧ P Q R :=
  relSigma_apply P x y

/-- ✱162·13. \[\begin{align}\vdash \colon\ldotp x(\Sigma ʻP)&y.\equiv :(\exists Q).Q\in CʻP.xQy.\\ &\lor.(\exists Q,R).x\in CʻQ.y\in CʻR.QPR \quad[*161·12.*33·51]\end{align}\] -/
theorem pm162_13 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {x y : α} :
    relSigma P x y ↔ (∃ Q, Q ∈ fld P ∧ Q x y) ∨ ∃ Q R, (x ∈ fld Q ∧ y ∈ fld R) ∧ P Q R :=
  relSigma_apply P x y

/-- ✱162·14. \[\begin{align}&\vdash \colon\ldotp x(\Sigma ʻP)y.=:(\exists Q).QFP.xQy.\lor.(\exists Q,R).xFQ.yFR.QPR\\ &[*161·12.*33·51]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `=` for the principal `≡`
(as in ✱162·12·13). -/
theorem pm162_14 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {x y : α} :
    relSigma P x y ↔ (∃ Q, F Q P ∧ Q x y) ∨ ∃ Q R, (F x Q ∧ F y R) ∧ P Q R :=
  relSigma_apply P x y

/-- ✱162·2. \(\vdash .\text{Cnv}ʻ\Sigma ʻP=\Sigma ʻ\text{Cnv}^{;}\breve{P}\) -/
theorem pm162_2 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    (relSigma P)˘ = relSigma (Cnv ⁏ P˘) := by
  rw [Cnv_eq_graph]
  refine rel_ext' fun x y => ?_
  show relSigma P y x ↔ _
  rw [relSigma_apply, relSigma_apply, fld_semi_graph, fld_cnv']
  constructor
  · rintro (⟨Q, hQ, h⟩ | ⟨Q, R, ⟨hy, hx⟩, h⟩)
    · exact Or.inl ⟨Q˘, ⟨Q, hQ, rfl⟩, h⟩
    · exact Or.inr ⟨R˘, Q˘, ⟨by rw [fld_cnv']; exact hx, by rw [fld_cnv']; exact hy⟩,
        (semi_graph_apply _ _ _ _).2 ⟨R, Q, ⟨rfl, rfl⟩, h⟩⟩
  · rintro (⟨T, ⟨Q, hQ, rfl⟩, h⟩ | ⟨T, T', ⟨hx, hy⟩, h⟩)
    · exact Or.inl ⟨Q, hQ, h⟩
    · obtain ⟨R, Q, ⟨rfl, rfl⟩, h'⟩ := (semi_graph_apply _ _ _ _).1 h
      rw [fld_cnv'] at hx hy
      exact Or.inr ⟨Q, R, ⟨hy, hx⟩, h'⟩

/-- ✱162·21. \(\vdash .\text{D}ʻ\Sigma ʻP=sʻ\text{D}ʻʻCʻP\cup sʻCʻʻ\text{D}ʻ(P\upharpoonright -{℩}ʻ\dot{\Lambda} )\) -/
theorem pm162_21 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    dom (relSigma P) = sumCls (D ʻʻ fld P) ∪ sumCls (C ʻʻ dom (P ↾ (ι rNull)ᶜ)) := by
  ext x
  show x ∈ dom (relSigma P) ↔ x ∈ sumCls (graph dom ʻʻ fld P) ∨
    x ∈ sumCls (graph fld ʻʻ dom (P ↾ (ι rNull)ᶜ))
  rw [mem_sumCls_graph_img, mem_sumCls_graph_img]
  constructor
  · rintro ⟨y, h⟩
    rcases (relSigma_apply P x y).1 h with ⟨Q, hQ, h⟩ | ⟨Q, R, ⟨hx, hy⟩, h⟩
    · exact Or.inl ⟨Q, hQ, ⟨y, h⟩⟩
    · refine Or.inr ⟨Q, ⟨R, h, fun e => ?_⟩, hx⟩
      rw [mem_unitCls] at e
      rw [e, fld_rNull] at hy
      simp at hy
  · rintro (⟨Q, hQ, ⟨y, h⟩⟩ | ⟨Q, ⟨R, h, hR⟩, hx⟩)
    · exact ⟨y, (relSigma_apply P x y).2 (Or.inl ⟨Q, hQ, h⟩)⟩
    · have : rEx R := by
        by_contra hn
        exact hR (mem_unitCls.2 (eq_rNull_of_not_rEx hn))
      obtain ⟨y, hy⟩ := rEx_iff_fld.1 this
      exact ⟨y, (relSigma_apply P x y).2 (Or.inr ⟨Q, R, ⟨hx, hy⟩, h⟩)⟩

/-- ✱162·211. \(\vdash .\text{ᗡ}ʻ\Sigma ʻP=sʻ\text{ᗡ}ʻʻCʻP\cup sʻCʻʻ\text{ᗡ}ʻ(-{℩}ʻ\dot{\Lambda} )\upharpoonleft P\)

`(−ι'Λ̇) ↿ P` is `(ι rNull)ᶜ ◁ P`. -/
theorem pm162_211 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    codom (relSigma P) = sumCls (Dcnv ʻʻ fld P) ∪ sumCls (C ʻʻ codom ((ι rNull)ᶜ ◁ P)) := by
  ext y
  show y ∈ codom (relSigma P) ↔ y ∈ sumCls (graph codom ʻʻ fld P) ∨
    y ∈ sumCls (graph fld ʻʻ codom ((ι rNull)ᶜ ◁ P))
  rw [mem_sumCls_graph_img, mem_sumCls_graph_img]
  constructor
  · rintro ⟨x, h⟩
    rcases (relSigma_apply P x y).1 h with ⟨Q, hQ, h⟩ | ⟨Q, R, ⟨hx, hy⟩, h⟩
    · exact Or.inl ⟨Q, hQ, ⟨x, h⟩⟩
    · refine Or.inr ⟨R, ⟨Q, fun e => ?_, h⟩, hy⟩
      rw [mem_unitCls] at e
      rw [e, fld_rNull] at hx
      simp at hx
  · rintro (⟨Q, hQ, ⟨x, h⟩⟩ | ⟨R, ⟨Q, hQ, h⟩, hy⟩)
    · exact ⟨x, (relSigma_apply P x y).2 (Or.inl ⟨Q, hQ, h⟩)⟩
    · have : rEx Q := by
        by_contra hn
        exact hQ (mem_unitCls.2 (eq_rNull_of_not_rEx hn))
      obtain ⟨x, hx⟩ := rEx_iff_fld.1 this
      exact ⟨x, (relSigma_apply P x y).2 (Or.inr ⟨Q, R, ⟨hx, hy⟩, h⟩)⟩

/-- ✱162·212. \(\vdash :\dot{\Lambda} {\sim}\in \text{ᗡ}ʻP.\supset .\text{D}ʻ\Sigma ʻP=sʻCʻʻ\text{D}ʻP\cup sʻ\text{D}ʻʻ\overrightarrow{B}ʻ\breve{P} \) -/
theorem pm162_212 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    rNull ∉ codom P → dom (relSigma P) = sumCls (C ʻʻ dom P) ∪ sumCls (D ʻʻ refs Beg P˘) := by
  intro hN
  ext x
  show x ∈ dom (relSigma P) ↔ x ∈ sumCls (graph fld ʻʻ dom P) ∨
    x ∈ sumCls (graph dom ʻʻ refs Beg P˘)
  rw [mem_sumCls_graph_img, mem_sumCls_graph_img]
  constructor
  · rintro ⟨y, h⟩
    rcases (relSigma_apply P x y).1 h with ⟨Q, ⟨R, hQR | hRQ⟩, h⟩ | ⟨Q, R, ⟨hx, -⟩, h⟩
    · exact Or.inl ⟨Q, ⟨R, hQR⟩, mem_fld_l h⟩
    · by_cases hQ : Q ∈ dom P
      · exact Or.inl ⟨Q, hQ, mem_fld_l h⟩
      · exact Or.inr ⟨Q, ⟨⟨R, hRQ⟩, hQ⟩, ⟨y, h⟩⟩
    · exact Or.inl ⟨Q, ⟨R, h⟩, hx⟩
  · rintro (⟨Q, ⟨R, h⟩, hx⟩ | ⟨Q, ⟨⟨R, hRQ⟩, -⟩, ⟨y, h⟩⟩)
    · have : rEx R := by
        by_contra hn
        exact hN (by rw [← eq_rNull_of_not_rEx hn]; exact ⟨Q, h⟩)
      obtain ⟨y, hy⟩ := rEx_iff_fld.1 this
      exact ⟨y, (relSigma_apply P x y).2 (Or.inr ⟨Q, R, ⟨hx, hy⟩, h⟩)⟩
    · exact ⟨y, (relSigma_apply P x y).2 (Or.inl ⟨Q, mem_fld_r hRQ, h⟩)⟩

/-- ✱162·213. \(\vdash :\dot{\Lambda} {\sim} \in \text{D}ʻP.\supset .\text{ᗡ}ʻ\Sigma ʻP = sʻCʻʻ\text{ᗡ}ʻP\cup sʻ\text{ᗡ}ʻʻ\overrightarrow{B}ʻP\) -/
theorem pm162_213 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    rNull ∉ dom P → codom (relSigma P) = sumCls (C ʻʻ codom P) ∪ sumCls (Dcnv ʻʻ refs Beg P) := by
  intro hN
  ext y
  show y ∈ codom (relSigma P) ↔ y ∈ sumCls (graph fld ʻʻ codom P) ∨
    y ∈ sumCls (graph codom ʻʻ refs Beg P)
  rw [mem_sumCls_graph_img, mem_sumCls_graph_img]
  constructor
  · rintro ⟨x, h⟩
    rcases (relSigma_apply P x y).1 h with ⟨Q, ⟨R, hQR | hRQ⟩, h⟩ | ⟨Q, R, ⟨-, hy⟩, h⟩
    · by_cases hQ : Q ∈ codom P
      · exact Or.inl ⟨Q, hQ, mem_fld_r h⟩
      · exact Or.inr ⟨Q, ⟨⟨R, hQR⟩, hQ⟩, ⟨x, h⟩⟩
    · exact Or.inl ⟨Q, ⟨R, hRQ⟩, mem_fld_r h⟩
    · exact Or.inl ⟨R, ⟨Q, h⟩, hy⟩
  · rintro (⟨R, ⟨Q, h⟩, hy⟩ | ⟨Q, ⟨⟨R, hQR⟩, -⟩, ⟨x, h⟩⟩)
    · have : rEx Q := by
        by_contra hn
        exact hN (by rw [← eq_rNull_of_not_rEx hn]; exact ⟨R, h⟩)
      obtain ⟨x, hx⟩ := rEx_iff_fld.1 this
      exact ⟨x, (relSigma_apply P x y).2 (Or.inr ⟨Q, R, ⟨hx, hy⟩, h⟩)⟩
    · exact ⟨x, (relSigma_apply P x y).2 (Or.inl ⟨Q, mem_fld_l hQR, h⟩)⟩

/-- ✱162·22. \(\vdash .Cʻ\Sigma ʻP = sʻCʻʻCʻP\) -/
theorem pm162_22 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    fld (relSigma P) = sumCls (C ʻʻ fld P) := by
  ext x
  show x ∈ fld (relSigma P) ↔ x ∈ sumCls (graph fld ʻʻ fld P)
  rw [mem_sumCls_graph_img]
  constructor
  · rintro ⟨y, h | h⟩
    · rcases (relSigma_apply P x y).1 h with ⟨Q, hQ, h⟩ | ⟨Q, R, ⟨hx, -⟩, h⟩
      exacts [⟨Q, hQ, mem_fld_l h⟩, ⟨Q, mem_fld_l h, hx⟩]
    · rcases (relSigma_apply P y x).1 h with ⟨Q, hQ, h⟩ | ⟨Q, R, ⟨-, hx⟩, h⟩
      exacts [⟨Q, hQ, mem_fld_r h⟩, ⟨R, mem_fld_r h, hx⟩]
  · rintro ⟨Q, hQ, ⟨y, h | h⟩⟩
    · exact ⟨y, Or.inl ((relSigma_apply P x y).2 (Or.inl ⟨Q, hQ, h⟩))⟩
    · exact ⟨y, Or.inr ((relSigma_apply P y x).2 (Or.inl ⟨Q, hQ, h⟩))⟩

/-- ✱162·23. \(\vdash .Cʻ\Sigma ʻP = Cʻ\dot{s} ʻCʻP = FʻʻCʻP = \overrightarrow{F}^{2}ʻP \quad[*162·22.*42·2]\)

`F⃗²'P` is `refs (F ⨾ F) P` (`F²` is `F | F`, ✱34·02, the two `F`'s being of different types);
the chain is the conjunction of its links. -/
theorem pm162_23 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    (fld (relSigma P) = fld (sumRel (fld P)) ∧ fld (sumRel (fld P)) = F ʻʻ fld P) ∧
      F ʻʻ fld P = refs (F ⨾ F) P := by
  have e : ∀ x, x ∈ fld (relSigma P) ↔ ∃ Q, Q ∈ fld P ∧ x ∈ fld Q := fun x => by
    rw [pm162_22]; exact mem_sumCls_graph_img
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext x; exact (e x).trans mem_fld_sumRel.symm
  · ext x
    exact mem_fld_sumRel.trans ⟨fun ⟨Q, hQ, hx⟩ => ⟨Q, hQ, hx⟩, fun ⟨Q, hQ, hx⟩ => ⟨Q, hQ, hx⟩⟩
  · ext x
    exact ⟨fun ⟨Q, hQ, hx⟩ => ⟨Q, hx, hQ⟩, fun ⟨Q, hx, hQ⟩ => ⟨Q, hQ, hx⟩⟩

/-- ✱162·26. \(\vdash .\Sigma ʻ(P\unicode{x228d} Q) = \Sigma ʻP\unicode{x228d} \Sigma ʻQ\) -/
theorem pm162_26 {α : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop} :
    relSigma (P ⊍ Q) = relSigma P ⊍ relSigma Q := by
  refine rel_ext' fun x y => ?_
  rw [rcup_apply', relSigma_apply, relSigma_apply, relSigma_apply, fld_rcup]
  constructor
  · rintro (⟨R, hR | hR, h⟩ | ⟨R, S, hRS, h | h⟩)
    · exact Or.inl (Or.inl ⟨R, hR, h⟩)
    · exact Or.inr (Or.inl ⟨R, hR, h⟩)
    · exact Or.inl (Or.inr ⟨R, S, hRS, h⟩)
    · exact Or.inr (Or.inr ⟨R, S, hRS, h⟩)
  · rintro ((⟨R, hR, h⟩ | ⟨R, S, hRS, h⟩) | (⟨R, hR, h⟩ | ⟨R, S, hRS, h⟩))
    · exact Or.inl ⟨R, Or.inl hR, h⟩
    · exact Or.inr ⟨R, S, hRS, Or.inl h⟩
    · exact Or.inl ⟨R, Or.inr hR, h⟩
    · exact Or.inr ⟨R, S, hRS, Or.inr h⟩

/-- ✱162·27. \(\vdash .\Sigma ʻS^{;}(P\unicode{x228d} Q) = \Sigma ʻS^{;}P\unicode{x228d} \Sigma ʻS^{;}Q \quad[*162·26.*150·3]\)

`Σ'S;P` is `Σ'(S;P)` (✱150·04). -/
theorem pm162_27 {α β : Type*} {S : (α → α → Prop) → β → Prop} {P Q : β → β → Prop} :
    relSigma (S ⁏ (P ⊍ Q)) = relSigma (S ⁏ P) ⊍ relSigma (S ⁏ Q) := by
  rw [semi_rcup, pm162_26]

/-- ✱162·3. \(\vdash .\Sigma ʻ(Q\downarrow R) = Q\unicode{x2909}R\) -/
theorem pm162_3 {α : Type*} {Q R : α → α → Prop} : relSigma (Q ↓ R) = Q ⤉ R := by
  refine rel_ext' fun x y => ?_
  rw [relSigma_apply, fld_couple, rsum_apply]
  constructor
  · rintro (⟨T, hT | hT, h⟩ | ⟨T, T', ⟨hx, hy⟩, hT, hT'⟩)
    · rw [mem_unitCls] at hT; rw [hT] at h; exact Or.inl (Or.inl h)
    · rw [mem_unitCls] at hT; rw [hT] at h; exact Or.inl (Or.inr h)
    · rw [mem_unitCls] at hT hT'; rw [hT] at hx; rw [hT'] at hy; exact Or.inr ⟨hx, hy⟩
  · rintro ((h | h) | ⟨hx, hy⟩)
    · exact Or.inl ⟨Q, Or.inl (mem_unitCls.2 rfl), h⟩
    · exact Or.inl ⟨R, Or.inr (mem_unitCls.2 rfl), h⟩
    · exact Or.inr ⟨Q, R, ⟨hx, hy⟩, mem_unitCls.2 rfl, mem_unitCls.2 rfl⟩

/-- ✱162·31. \(\vdash .\Sigma ʻQ\unicode{x2909}\Sigma ʻR = \Sigma ʻ(Q\unicode{x2909}R)\) -/
theorem pm162_31 {α : Type*} {Q R : (α → α → Prop) → (α → α → Prop) → Prop} :
    relSigma Q ⤉ relSigma R = relSigma (Q ⤉ R) := by
  have e : ∀ (P : (α → α → Prop) → (α → α → Prop) → Prop) x,
      x ∈ fld (relSigma P) ↔ ∃ T, T ∈ fld P ∧ x ∈ fld T := fun P x => by
    rw [pm162_22]; exact mem_sumCls_graph_img
  refine rel_ext' fun x y => ?_
  rw [rsum_apply, relSigma_apply, relSigma_apply, relSigma_apply, e, e, fld_rsum]
  constructor
  · rintro (((⟨T, hT, h⟩ | ⟨T, T', hTT, h⟩) | (⟨T, hT, h⟩ | ⟨T, T', hTT, h⟩)) |
      ⟨⟨T, hT, hx⟩, ⟨T', hT', hy⟩⟩)
    · exact Or.inl ⟨T, Or.inl hT, h⟩
    · exact Or.inr ⟨T, T', hTT, Or.inl (Or.inl h)⟩
    · exact Or.inl ⟨T, Or.inr hT, h⟩
    · exact Or.inr ⟨T, T', hTT, Or.inl (Or.inr h)⟩
    · exact Or.inr ⟨T, T', ⟨hx, hy⟩, Or.inr ⟨hT, hT'⟩⟩
  · rintro (⟨T, hT | hT, h⟩ | ⟨T, T', ⟨hx, hy⟩, (h | h) | ⟨hT, hT'⟩⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨T, hT, h⟩))
    · exact Or.inl (Or.inr (Or.inl ⟨T, hT, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨T, T', ⟨hx, hy⟩, h⟩))
    · exact Or.inl (Or.inr (Or.inr ⟨T, T', ⟨hx, hy⟩, h⟩))
    · exact Or.inr ⟨⟨T, hT, hx⟩, ⟨T', hT', hy⟩⟩

/-- ✱162·32. \(\vdash .\Sigma ʻ\dot{s} ʻ\kappa = \dot{s} ʻ\Sigma ʻʻ\kappa\)

`Σ''κ` is `RelSigma ʻʻ K`. -/
theorem pm162_32 {α : Type*} {K : Set ((α → α → Prop) → (α → α → Prop) → Prop)} :
    relSigma (sumRel K) = sumRel (RelSigma ʻʻ K) := by
  refine rel_ext' fun x y => ?_
  rw [relSigma_apply]
  constructor
  · rintro (⟨T, hT, h⟩ | ⟨T, T', hTT, ⟨P, hP, h⟩⟩)
    · obtain ⟨P, hP, hTP⟩ := mem_fld_sumRel.1 hT
      exact ⟨relSigma P, ⟨P, hP, rfl⟩, (relSigma_apply P x y).2 (Or.inl ⟨T, hTP, h⟩)⟩
    · exact ⟨relSigma P, ⟨P, hP, rfl⟩, (relSigma_apply P x y).2 (Or.inr ⟨T, T', hTT, h⟩)⟩
  · rintro ⟨U, ⟨P, hP, rfl⟩, h⟩
    rcases (relSigma_apply P x y).1 h with ⟨T, hT, h⟩ | ⟨T, T', hTT, h⟩
    · exact Or.inl ⟨T, mem_fld_sumRel.2 ⟨P, hP, hT⟩, h⟩
    · exact Or.inr ⟨T, T', hTT, ⟨P, hP, h⟩⟩

/-- ✱162·33. \(\vdash .\Sigma ʻ\Sigma ʻP = \dot{s} ʻCʻ\dot{s} ʻCʻP\unicode{x228d} F^{;}\dot{s} ʻCʻP\unicode{x228d} F^{2;}P\)

`F^{2;}P` is `F²;P`, i.e. `(F ⨾ F) ⁏ P`. -/
theorem pm162_33 {α : Type*}
    {P : (((α → α → Prop) → (α → α → Prop) → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) →
      Prop)} :
    relSigma (relSigma P) = sumRel (fld (sumRel (fld P))) ⊍ F ⁏ sumRel (fld P) ⊍ (F ⨾ F) ⁏ P := by
  show sumRel (fld (relSigma P)) ⊍ F ⁏ relSigma P = _
  rw [pm162_23.1.1, show relSigma P = sumRel (fld P) ⊍ F ⁏ P from rfl, semi_rcup, semi_semi,
    rcup_assoc]

/-- ✱162·331. \(\vdash .F\mid \Sigma =F\mid \dot{s} \mid C=F^{2}\)

The relations are typically ambiguous: `F | Σ`, `F | ṡ | C` and `F²` relate a term `x` (of type
`α`) to a relation of relations; `F | ṡ | C` is `(F | ṡ) | C` (✱34·22). -/
theorem pm162_331 {α : Type*} :
    ((F : α → (α → α → Prop) → Prop) ⨾ RelSigma = F ⨾ sDotRel ⨾ C) ∧
      ((F : α → (α → α → Prop) → Prop) ⨾ sDotRel ⨾ C = F ⨾ F) := by
  have e1 : ∀ x (P : (α → α → Prop) → (α → α → Prop) → Prop),
      ((F : α → (α → α → Prop) → Prop) ⨾ RelSigma) x P ↔ x ∈ fld (relSigma P) := by
    intro x P
    constructor
    · rintro ⟨T, hx, (hT : T = relSigma P)⟩; rw [← hT]; exact hx
    · intro hx; exact ⟨relSigma P, hx, rfl⟩
  have e2 : ∀ x (P : (α → α → Prop) → (α → α → Prop) → Prop),
      ((F : α → (α → α → Prop) → Prop) ⨾ sDotRel ⨾ C) x P ↔ x ∈ fld (sumRel (fld P)) := by
    intro x P
    constructor
    · rintro ⟨L, ⟨T, hx, (hT : T = sumRel L)⟩, (hL : L = fld P)⟩; rw [← hL, ← hT]; exact hx
    · intro hx; exact ⟨fld P, ⟨sumRel (fld P), hx, rfl⟩, rfl⟩
  have e3 : ∀ x (P : (α → α → Prop) → (α → α → Prop) → Prop),
      ((F : α → (α → α → Prop) → Prop) ⨾ F) x P ↔ x ∈ F ʻʻ fld P :=
    fun x P => ⟨fun ⟨T, hx, hT⟩ => ⟨T, hT, hx⟩, fun ⟨T, hT, hx⟩ => ⟨T, hx, hT⟩⟩
  refine ⟨rel_ext' fun x P => ?_, rel_ext' fun x P => ?_⟩
  · rw [e1, e2, pm162_23.1.1]
  · rw [e2, e3, pm162_23.1.2]

/-- ✱162·332. \(\vdash .\Sigma ʻ\Sigma ^{;}P= \dot{s} ʻCʻ\dot{s} ʻP\unicode{x228d} F^{;}\dot{s} ʻCʻP\unicode{x228d} F^{2;}P\)

**Status.** proved (reading): transcription error: the e-text prints `ṡ'C'ṡ'P` as the first
summand, which is not significant (`P` is a relation, not a class); PM's demonstration ends with
`ṡ'C'ṡ'C'P ∪̇ F;ṡ'C'P ∪̇ F²;P`, the right-hand side of ✱162·33. -/
theorem pm162_332 {α : Type*}
    {P : (((α → α → Prop) → (α → α → Prop) → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) →
      Prop)} :
    relSigma (RelSigma ⁏ P) =
      sumRel (fld (sumRel (fld P))) ⊍ F ⁏ sumRel (fld P) ⊍ (F ⨾ F) ⁏ P := by
  show sumRel (fld (graph relSigma ⁏ P)) ⊍ F ⁏ graph relSigma ⁏ P = _
  rw [fld_semi_graph, semi_semi]
  rw [show (F ⨾ graph relSigma : α → _ → Prop) = F ⨾ F from pm162_331.1.trans pm162_331.2]
  rw [show sumRel (graph relSigma ʻʻ fld P) = relSigma (sumRel (fld P)) from pm162_32.symm]
  rfl

/-- ✱162·34. \(\vdash .\Sigma ʻ\Sigma ^{;}=\Sigma ʻ\Sigma ʻP \quad[*162·33·332]\)

**Status.** proved (reading): transcription error: the e-text prints `Σ'Σ;` for `Σ'Σ;P` (the
associative law; the proof `[✱162·33·332]` and the Summary have `Σ'Σ;P = Σ'Σ'P`). -/
theorem pm162_34 {α : Type*}
    {P : (((α → α → Prop) → (α → α → Prop) → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) →
      Prop)} :
    relSigma (RelSigma ⁏ P) = relSigma (relSigma P) :=
  pm162_332.trans pm162_33.symm

/-- ✱162·341. \(\vdash \colon\ldotp CʻQ\subset \text{ᗡ}ʻR.\supset :x(F\mid R\dagger )Q.\equiv .x(R\mid F)Q\) -/
theorem pm162_341 {α β : Type*} {R : α → β → Prop} {Q : β → β → Prop} {x : α} :
    fld Q ⊆ codom R → ((F ⨾ daggerRel R) x Q ↔ (R ⨾ F) x Q) := by
  intro h
  constructor
  · rintro ⟨T, hx, (hT : T = daggerOp R Q)⟩
    have hx' : x ∈ fld T := hx
    rw [hT, daggerOp_eq_semi, fld_semi_of h] at hx'
    obtain ⟨z, hz, hxz⟩ := hx'
    exact ⟨z, hxz, hz⟩
  · rintro ⟨z, hxz, hz⟩
    refine ⟨daggerOp R Q, ?_, rfl⟩
    show x ∈ fld (daggerOp R Q)
    rw [daggerOp_eq_semi, fld_semi_of h]
    exact ⟨z, hz, hxz⟩

/-- ✱162·342. \(\vdash :Cʻ\dot{s} ʻ\lambda \subset \text{ᗡ}ʻR.\supset .(F\mid R\dagger )\upharpoonright \lambda =(R\mid F)\upharpoonright \lambda\) -/
theorem pm162_342 {α β : Type*} {R : α → β → Prop} {L : Set (β → β → Prop)} :
    fld (sumRel L) ⊆ codom R → (F ⨾ daggerRel R) ↾ L = (R ⨾ F) ↾ L := by
  intro h
  refine rel_ext' fun x Q => ⟨fun ⟨h1, h2⟩ => ⟨?_, h2⟩, fun ⟨h1, h2⟩ => ⟨?_, h2⟩⟩
  · have hQ : fld Q ⊆ codom R := fun z hz => h (mem_fld_sumRel.2 ⟨Q, h2, hz⟩)
    exact (pm162_341 hQ).1 h1
  · have hQ : fld Q ⊆ codom R := fun z hz => h (mem_fld_sumRel.2 ⟨Q, h2, hz⟩)
    exact (pm162_341 hQ).2 h1

/-- ✱162·343. \(\vdash : Cʻ\Sigma ʻP\subset \text{ᗡ}ʻR.\supset .F^{;}R\dagger ^{;}P=R^{;}F^{;}P\) -/
theorem pm162_343 {α β : Type*} {R : α → β → Prop} {P : (β → β → Prop) → (β → β → Prop) → Prop} :
    fld (relSigma P) ⊆ codom R → F ⁏ daggerRel R ⁏ P = R ⁏ F ⁏ P := by
  intro h
  have hQ : ∀ Q, Q ∈ fld P → fld Q ⊆ codom R := fun Q hQ z hz => h (by
    rw [pm162_22]; exact mem_sumCls_graph_img.2 ⟨Q, hQ, hz⟩)
  rw [semi_semi, semi_semi]
  refine rel_ext' fun x y => ?_
  rw [semi_iff', semi_iff']
  constructor
  · rintro ⟨Q, Q', h1, h2, h3⟩
    exact ⟨Q, Q', (pm162_341 (hQ Q (mem_fld_l h3))).1 h1, (pm162_341 (hQ Q' (mem_fld_r h3))).1 h2, h3⟩
  · rintro ⟨Q, Q', h1, h2, h3⟩
    exact ⟨Q, Q', (pm162_341 (hQ Q (mem_fld_l h3))).2 h1, (pm162_341 (hQ Q' (mem_fld_r h3))).2 h2, h3⟩

/-- ✱162·35. \(\vdash :Cʻ\Sigma ʻQ\subset \text{ᗡ}ʻR.\supset .\Sigma ʻR\dagger ^{;}Q=R^{;}\Sigma ʻQ\) -/
theorem pm162_35 {α β : Type*} {R : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    fld (relSigma Q) ⊆ codom R → relSigma (daggerRel R ⁏ Q) = R ⁏ relSigma Q := by
  intro h
  show sumRel (fld (graph (daggerOp R) ⁏ Q)) ⊍ F ⁏ daggerRel R ⁏ Q =
    R ⁏ (sumRel (fld Q) ⊍ F ⁏ Q)
  rw [fld_semi_graph, pm162_343 h, semi_rcup, semi_sumRel]
  rfl

/-- ✱162·36. \(\vdash :CʻP\cup CʻQ\subset \text{ᗡ}ʻR.\supset .R^{;}P\unicode{x2909}R^{;}Q=R^{;}(P\unicode{x2909}Q)\) -/
theorem pm162_36 {α β : Type*} {R : α → β → Prop} {P Q : β → β → Prop} :
    fld P ∪ fld Q ⊆ codom R → R ⁏ P ⤉ R ⁏ Q = R ⁏ (P ⤉ Q) := fun h =>
  (pm160_44 ⟨fun _ hz => h (Or.inl hz), fun _ hz => h (Or.inr hz)⟩).symm

/-- ✱162·37. \(\vdash :\exists !\lambda .\exists !\mu .\supset .\Sigma ʻ(\lambda \uparrow \mu )=\dot{s} ʻ\lambda \unicode{x2909}\dot{s} ʻ\mu\) -/
theorem pm162_37 {α : Type*} {L M : Set (α → α → Prop)} :
    L.Nonempty ∧ M.Nonempty → relSigma (cross L M) = sumRel L ⤉ sumRel M := by
  rintro ⟨hL, hM⟩
  refine rel_ext' fun x y => ?_
  rw [relSigma_apply, rsum_apply, fld_cross hL hM, mem_fld_sumRel, mem_fld_sumRel]
  constructor
  · rintro (⟨T, hT | hT, h⟩ | ⟨T, T', ⟨hx, hy⟩, hT, hT'⟩)
    · exact Or.inl (Or.inl ⟨T, hT, h⟩)
    · exact Or.inl (Or.inr ⟨T, hT, h⟩)
    · exact Or.inr ⟨⟨T, hT, hx⟩, ⟨T', hT', hy⟩⟩
  · rintro ((⟨T, hT, h⟩ | ⟨T, hT, h⟩) | ⟨⟨T, hT, hx⟩, ⟨T', hT', hy⟩⟩)
    · exact Or.inl ⟨T, Or.inl hT, h⟩
    · exact Or.inl ⟨T, Or.inr hT, h⟩
    · exact Or.inr ⟨T, T', ⟨hx, hy⟩, hT, hT'⟩

/-- ✱162·371. \(\vdash :\exists !\alpha .\supset .\Sigma ʻ(\alpha \uparrow \iota ʻQ)=\dot{s} ʻ\alpha \unicode{x2909}Q \quad[*162·37.*53·04]\) -/
theorem pm162_371 {α : Type*} {A : Set (α → α → Prop)} {Q : α → α → Prop} :
    A.Nonempty → relSigma (cross A (ι Q)) = sumRel A ⤉ Q := by
  intro h
  rw [pm162_37 ⟨h, ⟨Q, mem_unitCls.2 rfl⟩⟩, sumRel_unit]

/-- ✱162·372. \(\vdash :\exists !\beta .\supset .\Sigma ʻ(\iota ʻP)\uparrow \beta =P\unicode{x2909}\dot{s} ʻ\beta \)

`Σ'(ι'P) ↑ β` is `Σ'{(ι'P) ↑ β}` (the only significant bracketing). -/
theorem pm162_372 {α : Type*} {B : Set (α → α → Prop)} {P : α → α → Prop} :
    B.Nonempty → relSigma (cross (ι P) B) = P ⤉ sumRel B := by
  intro h
  rw [pm162_37 ⟨⟨P, mem_unitCls.2 rfl⟩, h⟩, sumRel_unit]

/-- ✱162·4. \(\vdash . \Sigma ʻ\dot{\Lambda} = \dot{\Lambda}\) -/
theorem pm162_4 {α : Type*} :
    relSigma (rNull : (α → α → Prop) → (α → α → Prop) → Prop) = rNull := by
  refine rel_ext' fun x y => ⟨fun h => ?_, fun h => absurd h (rNull_apply x y)⟩
  rcases (relSigma_apply _ x y).1 h with ⟨T, hT, -⟩ | ⟨T, T', -, h⟩
  · rw [fld_rNull] at hT; simp at hT
  · exact absurd h (rNull_apply _ _)

/-- ✱162·41. \(\vdash . \Sigma ʻ(\dot{\Lambda} \downarrow \dot{\Lambda} ) = \dot{\Lambda} \) -/
theorem pm162_41 {α : Type*} : relSigma ((rNull : α → α → Prop) ↓ rNull) = rNull := by
  rw [pm162_3, pm160_21]

/-- ✱162·42. \(\vdash : \dot{\exists} !\Sigma ʻP .\equiv . \dot{\exists} !\dot{s} ʻCʻP .\equiv . .\exists !CʻP-\iota ʻ\dot{\Lambda}\)

The chain is the conjunction of its links (the e-text's doubled dot is a misprint without
significance). -/
theorem pm162_42 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    (rEx (relSigma P) ↔ rEx (sumRel (fld P))) ∧
      (rEx (sumRel (fld P)) ↔ (fld P \ ι rNull).Nonempty) := by
  constructor
  · rw [rEx_iff_fld, rEx_iff_fld, pm162_23.1.1]
  · constructor
    · rintro ⟨x, y, T, hT, h⟩
      exact ⟨T, hT, fun e => by rw [mem_unitCls] at e; rw [e] at h; exact rNull_apply _ _ h⟩
    · rintro ⟨T, hT, hT'⟩
      have : rEx T := by
        by_contra hn
        exact hT' (mem_unitCls.2 (eq_rNull_of_not_rEx hn))
      obtain ⟨x, y, h⟩ := this
      exact ⟨x, y, T, hT, h⟩

/-- ✱162·43. \(\vdash : \dot{\exists} !P .\supset . \Sigma ʻ(P\unicode{x21f8} R) = \Sigma ʻP\unicode{x2909}R\)

In ✱162·43·431 `R` is of the type of the members of `C'P` (PM's note). -/
theorem pm162_43 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {R : α → α → Prop} :
    rEx P → relSigma (P ⇸ R) = relSigma P ⤉ R := by
  intro h
  rw [addLast, pm162_26, pm162_371 (rEx_iff_fld.1 h)]
  refine rel_ext' fun x y => ?_
  simp only [rcup_apply', rsum_apply, relSigma_iff, pm162_23.1.1]
  tauto

/-- ✱162·431. \(\vdash : \dot{\exists} !P .\supset . \Sigma ʻ(R\unicode{x21f7}P) = R\unicode{x2909}\Sigma ʻP \quad[\text{Proof as in *162·43}]\) -/
theorem pm162_431 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {R : α → α → Prop} :
    rEx P → relSigma (R ⇷ P) = R ⤉ relSigma P := by
  intro h
  rw [addFirst, pm162_26, pm162_372 (rEx_iff_fld.1 h)]
  refine rel_ext' fun x y => ?_
  simp only [rcup_apply', rsum_apply, relSigma_iff, pm162_23.1.1]
  tauto

/-- ✱162·44. \(\vdash . \Sigma ʻ(P\unicode{x21f8} \dot{\Lambda} ) = \Sigma ʻ(\dot{\Lambda} \unicode{x21f7}P) = \Sigma ʻP\)

The e-text numbers it `*162.44.` (a full stop for the centred dot). `Λ̇` is of the type of the members of `C'P`; the chain is the conjunction of its links. -/
theorem pm162_44 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    relSigma (P ⇸ (rNull : α → α → Prop)) = relSigma (rNull ⇷ P) ∧
      relSigma (rNull ⇷ P) = relSigma P := by
  have h1 : relSigma (P ⇸ (rNull : α → α → Prop)) = relSigma P := by
    refine rel_ext' fun x y => ?_
    rw [relSigma_apply, relSigma_apply]
    constructor
    · rintro (⟨Q, ⟨R, h | h⟩, hxy⟩ | ⟨Q, R, ⟨hx, hy⟩, h⟩)
      · rcases (addLast_apply P rNull Q R).1 h with h | ⟨hQ, -⟩
        · exact Or.inl ⟨Q, mem_fld_l h, hxy⟩
        · exact Or.inl ⟨Q, hQ, hxy⟩
      · rcases (addLast_apply P rNull R Q).1 h with h | ⟨-, rfl⟩
        · exact Or.inl ⟨Q, mem_fld_r h, hxy⟩
        · exact absurd hxy (rNull_apply x y)
      · rcases (addLast_apply P rNull Q R).1 h with h | ⟨-, rfl⟩
        · exact Or.inr ⟨Q, R, ⟨hx, hy⟩, h⟩
        · obtain ⟨z, hz | hz⟩ := hy <;> exact absurd hz (rNull_apply _ _)
    · rintro (⟨Q, ⟨R, h | h⟩, hxy⟩ | ⟨Q, R, hQR, h⟩)
      · exact Or.inl ⟨Q, mem_fld_l ((addLast_apply P rNull Q R).2 (Or.inl h)), hxy⟩
      · exact Or.inl ⟨Q, mem_fld_r ((addLast_apply P rNull R Q).2 (Or.inl h)), hxy⟩
      · exact Or.inr ⟨Q, R, hQR, (addLast_apply P rNull Q R).2 (Or.inl h)⟩
  have h2 : relSigma ((rNull : α → α → Prop) ⇷ P) = relSigma P := by
    refine rel_ext' fun x y => ?_
    rw [relSigma_apply, relSigma_apply]
    constructor
    · rintro (⟨Q, ⟨R, h | h⟩, hxy⟩ | ⟨Q, R, ⟨hx, hy⟩, h⟩)
      · rcases (addFirst_apply rNull P Q R).1 h with ⟨rfl, -⟩ | h
        · exact absurd hxy (rNull_apply x y)
        · exact Or.inl ⟨Q, mem_fld_l h, hxy⟩
      · rcases (addFirst_apply rNull P R Q).1 h with ⟨-, hQ⟩ | h
        · exact Or.inl ⟨Q, hQ, hxy⟩
        · exact Or.inl ⟨Q, mem_fld_r h, hxy⟩
      · rcases (addFirst_apply rNull P Q R).1 h with ⟨rfl, -⟩ | h
        · obtain ⟨z, hz | hz⟩ := hx <;> exact absurd hz (rNull_apply _ _)
        · exact Or.inr ⟨Q, R, ⟨hx, hy⟩, h⟩
    · rintro (⟨Q, ⟨R, h | h⟩, hxy⟩ | ⟨Q, R, hQR, h⟩)
      · exact Or.inl ⟨Q, mem_fld_l ((addFirst_apply rNull P Q R).2 (Or.inr h)), hxy⟩
      · exact Or.inl ⟨Q, mem_fld_r ((addFirst_apply rNull P R Q).2 (Or.inr h)), hxy⟩
      · exact Or.inr ⟨Q, R, hQR, (addFirst_apply rNull P Q R).2 (Or.inr h)⟩
  exact ⟨h1.trans h2.symm, h2⟩

/-- ✱162·45.\(\vdash :\dot{\exists} !P.\Sigma ʻP=\dot{\Lambda} .\equiv .P=\dot{\Lambda} \downarrow \dot{\Lambda}\) -/
theorem pm162_45 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    rEx P ∧ relSigma P = rNull ↔ P = rNull ↓ rNull := by
  constructor
  · rintro ⟨hP, hS⟩
    have hN : ¬ rEx (relSigma P) := by rw [hS]; rintro ⟨x, y, h⟩; exact rNull_apply x y h
    rw [pm162_42.1, pm162_42.2] at hN
    have hf : ∀ T, T ∈ fld P → T = rNull := fun T hT => by
      by_contra hT'
      exact hN ⟨T, hT, fun e => hT' (mem_unitCls.1 e)⟩
    obtain ⟨Q, R, hQR⟩ := hP
    have hQ := hf Q (mem_fld_l hQR)
    have hR := hf R (mem_fld_r hQR)
    refine rel_ext' fun T T' => ⟨fun h => ?_, fun h => ?_⟩
    · exact (couple_apply _ _ _ _).2 ⟨hf T (mem_fld_l h), hf T' (mem_fld_r h)⟩
    · rw [couple_apply] at h
      rw [h.1, h.2]
      rw [hQ, hR] at hQR
      exact hQR
  · intro e
    rw [e]
    exact ⟨⟨rNull, rNull, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩⟩, pm162_41⟩

/-!
## [✱163] Relations of mutually exclusive relations

*(Vol. 2, p. 369)*

> *Summary of* *163.
>
> In the present number we have to define mutually exclusive relations, and to give a few of their properties. Mutually exclusive relations play much the same part in relation-arithmetic as mutually exclusive classes play in cardinal arithmetic. *Prima facie*, there are various ways in which we might define them. We might define \(P\) as a relation of mutually exclusive relations when \[ \begin{aligned} QPR . Q &\neq R . \supset _{Q,R} . Q \dot{\cap} R = \dot{\Lambda} ,\\ \text{or when}\quad Q,R \in CʻP . Q &\neq R . \supset _{Q,R} . Q \dot{\cap} R = \dot{\Lambda} , \end{aligned} \] or when \[ Q,R \in CʻP . Q \neq R . \supset _{Q,R} . \text{D}ʻQ \cap \text{D}ʻR = \Lambda . \text{ᗡ}ʻQ \cap \text{ᗡ}ʻR = \Lambda , \] or in several other ways. But in fact the most useful property to choose is the property that any two members of the field have mutually exclusive fields, *i.e.* \[ Q,R \in CʻP . Q \neq R . \supset _{Q,R} . CʻQ \cap CʻR = \Lambda . \]
>
> …

**Lean reading.** `Rel² excl` is `Rel2excl`, a class of relations of relations
`P : (α → α → Prop) → (α → α → Prop) → Prop`; `Q, R ∈ C'P` is `Q ∈ fld P ∧ R ∈ fld P` (✱20·04)
and `P, Q ∈ Rel² excl` is the conjunction. `F ↾ C'P`, `C ↾ C'P`, `D ↾ C'P`, `ᗡ ↾ C'P` restrict
the relations of ✱33 (`C ↾ C'P` is `C ↾ fld P`); `C''C'P` is `C ʻʻ fld P`; `F_Δ'C'P` is
`sel F (fld P)` and `Prod'κ` is `prodK K` (✱115); `B''X` is `Beg ʻʻ X`; `Cnv''X` is `Cnv ʻʻ X`.
In ✱163·45 the e-text prints `P ⤉ R` where PM's proof (and ✱163·451·452·46) have `P ⇸ R` (`R` a
relation of the type of the members of `C'P`): read `P ⇸ R`.

**Status.** proved (all propositions; ✱163·01 definition; ✱163·45 proved (reading), see its
docstring)
-/

/-- ✱163·01 (Df). \(\text{Rel}^{2}\text{excl}=\hat{P} \{Q,R\in CʻP.Q\neq R.\supset _{Q,R}.CʻQ\cap CʻR=\Lambda\} \quad\text{Df}\) -/
theorem pm163_01 {α : Type*} :
    (Rel2excl : Set ((α → α → Prop) → (α → α → Prop) → Prop)) =
      {P | ∀ Q R, (Q ∈ fld P ∧ R ∈ fld P) ∧ Q ≠ R → fld Q ∩ fld R = Λ} := rfl

/-- ✱163·1. \[\begin{align}&\vdash \colon\ldotp P\in \text{Rel}^{2}\text{excl}.\equiv :Q,R\in CʻP.Q\neq R.\supset _{Q,R}.CʻQ\cap CʻR=\Lambda \\ &[(*163·01)]\end{align}\] -/
theorem pm163_1 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ↔ ∀ Q R, (Q ∈ fld P ∧ R ∈ fld P) ∧ Q ≠ R → fld Q ∩ fld R = Λ := Iff.rfl

private theorem mem_fld_relSigma {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {x : α} : x ∈ fld (relSigma P) ↔ ∃ Q, Q ∈ fld P ∧ x ∈ fld Q := by
  rw [pm162_22]; exact mem_sumCls_C

/-- ✱163·11. \[\begin{align}&\vdash \colon\ldotp P\in \text{Rel}^{2}\text{excl}.\equiv :Q,R\in CʻP.\exists !CʻQ\cap CʻR.\supset _{Q,R}.Q=R\\ &[*163·1.\text{Transp}]\end{align}\] -/
theorem pm163_11 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ↔ ∀ Q R, (Q ∈ fld P ∧ R ∈ fld P) ∧ (fld Q ∩ fld R).Nonempty → Q = R := by
  rw [excl_iff']
  constructor
  · rintro h Q R ⟨⟨hQ, hR⟩, ⟨x, hxQ, hxR⟩⟩; exact h Q R hQ hR x hxQ hxR
  · intro h Q R hQ hR x hxQ hxR; exact h Q R ⟨⟨hQ, hR⟩, ⟨x, hxQ, hxR⟩⟩

/-- ✱163·12. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\equiv .F\upharpoonright CʻP\in \text{Cls}\rightarrow 1 \quad[*163·1.*74·632]\) -/
theorem pm163_12 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ↔ F ↾ fld P ∈ arrow Cls one := by
  rw [excl_iff', mem_arrow_Cls_one]
  constructor
  · rintro h x Q R ⟨⟨hxQ, hQ⟩, ⟨hxR, hR⟩⟩; exact h Q R hQ hR x hxQ hxR
  · intro h Q R hQ hR x hxQ hxR; exact h x Q R ⟨⟨hxQ, hQ⟩, ⟨hxR, hR⟩⟩

/-- ✱163·13. \[\begin{align}\vdash \colon\ldotp P&\in \text{Rel}^{2}\text{excl}.\supset :\\ &Q,R\in CʻP.Q\neq R.\supset _{Q,R}.\text{D}ʻQ\cap \text{D}ʻR=\Lambda .\text{ᗡ}ʻQ\cap \text{ᗡ}ʻR=\Lambda \\ &[*24·402 .*163·1]\end{align}\] -/
theorem pm163_13 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl →
      ∀ Q R, (Q ∈ fld P ∧ R ∈ fld P) ∧ Q ≠ R → dom Q ∩ dom R = Λ ∧ codom Q ∩ codom R = Λ := by
  intro h Q R hQR
  have e := h Q R hQR
  constructor
  · rw [inter_null_iff]
    rintro ⟨x, ⟨y, hy⟩, ⟨z, hz⟩⟩
    exact not_mem_of_disj e (mem_fld_l hy) (mem_fld_l hz)
  · rw [inter_null_iff]
    rintro ⟨x, ⟨y, hy⟩, ⟨z, hz⟩⟩
    exact not_mem_of_disj e (mem_fld_r hy) (mem_fld_r hz)

/-- ✱163·14. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .C\upharpoonright CʻP\in 1\rightarrow 1 \quad[*163·12.*74·32.*33·5]\) -/
theorem pm163_14 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl → C ↾ fld P ∈ arrow one one := by
  intro h
  rw [excl_iff'] at h
  rw [oneone_iff]
  refine ⟨fun A B Q hAB => ?_, fun A Q R hQR => ?_⟩
  · obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hAB
    have h1' : A = fld Q := h1
    have h2' : B = fld Q := h2
    rw [h1', h2']
  · obtain ⟨⟨h1, hQ⟩, ⟨h2, hR⟩⟩ := hQR
    have h1' : A = fld Q := h1
    have h2' : A = fld R := h2
    by_cases hA : A.Nonempty
    · obtain ⟨x, hx⟩ := hA
      exact h Q R hQ hR x (by rw [← h1']; exact hx) (by rw [← h2']; exact hx)
    · rw [Set.not_nonempty_iff_eq_empty] at hA
      rw [eq_rNull_of_fld (Q := Q) (by rw [← h1']; exact hA),
        eq_rNull_of_fld (Q := R) (by rw [← h2']; exact hA)]

/-- ✱163·15. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\text{D}\upharpoonright CʻP,\text{ᗡ}\upharpoonright CʻP\in 1\rightarrow 1\)

`D ↾ C'P, ᗡ ↾ C'P ∈ 1 → 1` is the conjunction. -/
theorem pm163_15 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl → D ↾ fld P ∈ arrow one one ∧ Dcnv ↾ fld P ∈ arrow one one := by
  intro h
  rw [excl_iff'] at h
  constructor
  · rw [oneone_iff]
    refine ⟨fun A B Q hAB => ?_, fun A Q R hQR => ?_⟩
    · obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hAB
      have h1' : A = dom Q := h1
      have h2' : B = dom Q := h2
      rw [h1', h2']
    · obtain ⟨⟨h1, hQ⟩, ⟨h2, hR⟩⟩ := hQR
      have h1' : A = dom Q := h1
      have h2' : A = dom R := h2
      by_cases hA : A.Nonempty
      · obtain ⟨x, hx⟩ := hA
        rw [h1'] at hx
        obtain ⟨y, hy⟩ := hx
        have hx2 : x ∈ dom R := by rw [← h2', h1']; exact ⟨y, hy⟩
        obtain ⟨z, hz⟩ := hx2
        exact h Q R hQ hR x (mem_fld_l hy) (mem_fld_l hz)
      · rw [Set.not_nonempty_iff_eq_empty] at hA
        rw [eq_rNull_of_dom (Q := Q) (by rw [← h1']; exact hA),
          eq_rNull_of_dom (Q := R) (by rw [← h2']; exact hA)]
  · rw [oneone_iff]
    refine ⟨fun A B Q hAB => ?_, fun A Q R hQR => ?_⟩
    · obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hAB
      have h1' : A = codom Q := h1
      have h2' : B = codom Q := h2
      rw [h1', h2']
    · obtain ⟨⟨h1, hQ⟩, ⟨h2, hR⟩⟩ := hQR
      have h1' : A = codom Q := h1
      have h2' : A = codom R := h2
      by_cases hA : A.Nonempty
      · obtain ⟨x, hx⟩ := hA
        rw [h1'] at hx
        obtain ⟨y, hy⟩ := hx
        have hx2 : x ∈ codom R := by rw [← h2', h1']; exact ⟨y, hy⟩
        obtain ⟨z, hz⟩ := hx2
        exact h Q R hQ hR x (mem_fld_r hy) (mem_fld_r hz)
      · rw [Set.not_nonempty_iff_eq_empty] at hA
        rw [eq_rNull_of_codom (Q := Q) (by rw [← h1']; exact hA),
          eq_rNull_of_codom (Q := R) (by rw [← h2']; exact hA)]

/-- ✱163·16. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .CʻʻCʻP\in \text{Cls}^{2} \text{excl} \quad[*84·51.*33·5.*163·12]\) -/
theorem pm163_16 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl → C ʻʻ fld P ∈ Cls2excl := by
  intro h
  rw [excl_iff'] at h
  rintro A B ⟨⟨⟨Q, hQ, hAQ⟩, ⟨R, hR, hBR⟩⟩, hne⟩
  have hA : A = fld Q := hAQ
  have hB : B = fld R := hBR
  rw [inter_null_iff]
  rintro ⟨x, hxA, hxB⟩
  rw [hA] at hxA
  rw [hB] at hxB
  exact hne (by rw [hA, hB, h Q R hQ hR x hxA hxB])

/-- ✱163·17. \[\begin{align}&\vdash :P\in \text{Rel}^{2}\text{excl}.\equiv .C\upharpoonright CʻP\in 1\rightarrow 1.CʻʻCʻP\in \text{Cls}^{2} \text{excl}\\ &[*163·12.*84·522.*33·5]\end{align}\] -/
theorem pm163_17 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ↔ C ↾ fld P ∈ arrow one one ∧ C ʻʻ fld P ∈ Cls2excl := by
  refine ⟨fun h => ⟨pm163_14 h, pm163_16 h⟩, fun ⟨h1, h2⟩ => ?_⟩
  rw [excl_iff']
  intro Q R hQ hR x hxQ hxR
  by_contra hne
  have hf : fld Q ≠ fld R := fun e =>
    hne ((oneone_iff.1 h1).2 (fld Q) Q R ⟨⟨rfl, hQ⟩, ⟨e, hR⟩⟩)
  exact not_mem_of_disj (h2 (fld Q) (fld R) ⟨⟨⟨Q, hQ, rfl⟩, ⟨R, hR, rfl⟩⟩, hf⟩) hxQ hxR

/-- ✱163·2. \[\begin{align}&\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\text{D}\upharpoonright F_{\Delta }ʻCʻP\in 1\rightarrow 1.F_{\Delta }ʻCʻP\subset 1\rightarrow 1\\ &[*81·21·1.*163·12]\end{align}\]

`F_Δ'C'P` is `sel F (fld P)`; the conclusion is the product of two. -/
theorem pm163_2 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl → D ↾ sel F (fld P) ∈ arrow one one ∧ sel F (fld P) ⊆ arrow one one := by
  intro h
  rw [excl_iff'] at h
  have key : ∀ M, M ∈ sel F (fld P) → ∀ x Q R, M x Q → M x R → Q = R := by
    intro M hM x Q R hQ hR
    obtain ⟨⟨-, hMF⟩, hc⟩ := mem_sel_iff.1 hM
    exact h Q R (by rw [← hc]; exact ⟨x, hQ⟩) (by rw [← hc]; exact ⟨x, hR⟩) x (hMF _ _ hQ)
      (hMF _ _ hR)
  constructor
  · rw [oneone_iff]
    refine ⟨fun A B M hAB => ?_, fun A M N hMN => ?_⟩
    · obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hAB
      have h1' : A = dom M := h1
      have h2' : B = dom M := h2
      rw [h1', h2']
    · obtain ⟨⟨h1, hM⟩, ⟨h2, hN⟩⟩ := hMN
      have h1' : A = dom M := h1
      have h2' : A = dom N := h2
      have e : dom M = dom N := by rw [← h1', ← h2']
      have sub : ∀ M N, M ∈ sel F (fld P) → N ∈ sel F (fld P) → dom M = dom N →
          ∀ x Q, M x Q → N x Q := by
        intro M N hM hN e x Q hxQ
        have : x ∈ dom N := by rw [← e]; exact ⟨Q, hxQ⟩
        obtain ⟨R, hxR⟩ := this
        obtain ⟨⟨-, hMF⟩, hcM⟩ := mem_sel_iff.1 hM
        obtain ⟨⟨-, hNF⟩, hcN⟩ := mem_sel_iff.1 hN
        have := h Q R (by rw [← hcM]; exact ⟨x, hxQ⟩) (by rw [← hcN]; exact ⟨x, hxR⟩) x
          (hMF _ _ hxQ) (hNF _ _ hxR)
        rw [this]; exact hxR
      exact rel_ext' fun x Q => ⟨sub M N hM hN e x Q, sub N M hN hM e.symm x Q⟩
  · intro M hM
    rw [oneone_iff]
    exact ⟨fun x y Q hxy => mem_arrow_one_Cls.1 (mem_sel_iff.1 hM).1.1 x y Q hxy,
      fun x Q R hQR => key M hM x Q R hQR.1 hQR.2⟩

/-- ✱163·21. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\text{D}ʻʻF_{\Delta }ʻCʻP=\text{Prod}ʻCʻʻCʻP\)

`Prod'C''C'P` is `prodK (C ʻʻ fld P)` (✱115·01, `D''∈_Δ'κ`). -/
theorem pm163_21 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl → D ʻʻ sel F (fld P) = prodK (C ʻʻ fld P) := by
  intro h
  rw [excl_iff'] at h
  ext A
  constructor
  · rintro ⟨M, hM, hA⟩
    have hA' : A = dom M := hA
    obtain ⟨⟨hM1, hMF⟩, hcM⟩ := mem_sel_iff.1 hM
    refine ⟨fun x B => ∃ Q, M x Q ∧ B = fld Q, mem_sel_iff.2 ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [mem_arrow_one_Cls]
      rintro x y B ⟨⟨Q, hxQ, rfl⟩, ⟨Q', hyQ', e⟩⟩
      have hQ : Q ∈ fld P := by rw [← hcM]; exact ⟨x, hxQ⟩
      have hQ' : Q' ∈ fld P := by rw [← hcM]; exact ⟨y, hyQ'⟩
      have hx' : x ∈ fld Q' := by rw [← e]; exact hMF _ _ hxQ
      have := h Q Q' hQ hQ' x (hMF _ _ hxQ) hx'
      rw [← this] at hyQ'
      exact mem_arrow_one_Cls.1 hM1 x y Q ⟨hxQ, hyQ'⟩
    · rintro x B ⟨Q, hxQ, rfl⟩
      exact hMF _ _ hxQ
    · ext B
      constructor
      · rintro ⟨x, Q, hxQ, rfl⟩
        exact ⟨Q, by rw [← hcM]; exact ⟨x, hxQ⟩, rfl⟩
      · rintro ⟨Q, hQ, hBQ⟩
        rw [← hcM] at hQ
        obtain ⟨x, hxQ⟩ := hQ
        exact ⟨x, Q, hxQ, hBQ⟩
    · show A = dom _
      rw [hA']
      ext x
      constructor
      · rintro ⟨Q, hxQ⟩; exact ⟨fld Q, Q, hxQ, rfl⟩
      · rintro ⟨B, Q, hxQ, -⟩; exact ⟨Q, hxQ⟩
  · rintro ⟨N, hN, hA⟩
    have hA' : A = dom N := hA
    obtain ⟨⟨hN1, hNm⟩, hcN⟩ := mem_sel_iff.1 hN
    refine ⟨fun x Q => Q ∈ fld P ∧ N x (fld Q), mem_sel_iff.2 ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [mem_arrow_one_Cls]
      rintro x y Q ⟨⟨-, hx⟩, ⟨-, hy⟩⟩
      exact mem_arrow_one_Cls.1 hN1 x y _ ⟨hx, hy⟩
    · rintro x Q ⟨-, hx⟩
      exact hNm _ _ hx
    · ext Q
      constructor
      · rintro ⟨x, hQ, -⟩; exact hQ
      · intro hQ
        have : fld Q ∈ codom N := by rw [hcN]; exact ⟨Q, hQ, rfl⟩
        obtain ⟨x, hx⟩ := this
        exact ⟨x, hQ, hx⟩
    · show A = dom _
      rw [hA']
      ext x
      constructor
      · rintro ⟨B, hxB⟩
        have : B ∈ codom N := ⟨x, hxB⟩
        rw [hcN] at this
        obtain ⟨Q, hQ, hBQ⟩ := this
        have hB : B = fld Q := hBQ
        rw [hB] at hxB
        exact ⟨Q, hQ, hxB⟩
      · rintro ⟨Q, -, hx⟩; exact ⟨fld Q, hx⟩

/-- ✱163·22. \[\begin{align}\vdash :P\in \text{Rel}^{2}\text{excl}.\dot{\Lambda} &{\sim}\in CʻP.\supset .\\ &\overrightarrow{B}ʻ\Sigma ʻP=Bʻʻ\overrightarrow{B}ʻP.\overrightarrow{B}ʻ\text{Cnv}ʻ\Sigma ʻP=Bʻʻ\text{Cnv}ʻʻ\overrightarrow{B}ʻ\breve{P}\end{align}\]

`B''X` is `Beg ʻʻ X` and `Cnv''X` is `Cnv ʻʻ X`. -/
theorem pm163_22 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ∧ rNull ∉ fld P →
      refs Beg (relSigma P) = Beg ʻʻ refs Beg P ∧
        refs Beg (relSigma P)˘ = Beg ʻʻ Cnv ʻʻ refs Beg P˘ := by
  rintro ⟨h, hN⟩
  rw [excl_iff'] at h
  have ne : ∀ Q, Q ∈ fld P → ∃ z, z ∈ fld Q := fun Q hQ => by
    by_contra hn
    have hQ0 : ¬ rEx Q := fun ⟨a, b, hab⟩ => hn ⟨a, mem_fld_l hab⟩
    exact hN (by rw [← eq_rNull_of_not_rEx hQ0]; exact hQ)
  constructor
  · ext x
    show x ∈ dom (relSigma P) \ codom (relSigma P) ↔ ∃ Q, Q ∈ refs Beg P ∧ Beg x Q
    constructor
    · rintro ⟨⟨y, hxy⟩, hc⟩
      have hc' : ∀ z, ¬ relSigma P z x := fun z hz => hc ⟨z, hz⟩
      have notc : ∀ Q, x ∈ fld Q → Q ∉ codom P := by
        rintro Q hxQ ⟨Q', hQ'⟩
        obtain ⟨z, hz⟩ := ne Q' (mem_fld_l hQ')
        exact hc' z ((relSigma_apply P z x).2 (Or.inr ⟨Q', Q, ⟨hz, hxQ⟩, hQ'⟩))
      have notcQ : ∀ Q, Q ∈ fld P → x ∉ codom Q := by
        rintro Q hQ ⟨z, hz⟩
        exact hc' z ((relSigma_apply P z x).2 (Or.inl ⟨Q, hQ, hz⟩))
      rcases (relSigma_apply P x y).1 hxy with ⟨Q, hQ, h1⟩ | ⟨Q, R, ⟨hxQ, -⟩, h1⟩
      · have hQd : Q ∈ dom P := by
          rcases hQ with ⟨Q', hQ' | hQ'⟩
          exacts [⟨Q', hQ'⟩, absurd ⟨Q', hQ'⟩ (notc Q (mem_fld_l h1))]
        exact ⟨Q, ⟨hQd, notc Q (mem_fld_l h1)⟩, ⟨y, h1⟩, notcQ Q hQ⟩
      · have hQ : Q ∈ fld P := mem_fld_l h1
        refine ⟨Q, ⟨⟨R, h1⟩, notc Q hxQ⟩, ?_, notcQ Q hQ⟩
        rcases hxQ with ⟨z, hz | hz⟩
        exacts [⟨z, hz⟩, absurd ⟨z, hz⟩ (notcQ Q hQ)]
    · rintro ⟨Q, ⟨⟨R, hQR⟩, hQc⟩, ⟨y, hxy⟩, hxc⟩
      refine ⟨⟨y, (relSigma_apply P x y).2 (Or.inl ⟨Q, mem_fld_l hQR, hxy⟩)⟩, ?_⟩
      rintro ⟨z, hz⟩
      rcases (relSigma_apply P z x).1 hz with ⟨Q', hQ', h1⟩ | ⟨Q', R', ⟨-, hxR'⟩, h1⟩
      · have := h Q' Q hQ' (mem_fld_l hQR) x (mem_fld_r h1) (mem_fld_l hxy)
        rw [this] at h1
        exact hxc ⟨z, h1⟩
      · have := h R' Q (mem_fld_r h1) (mem_fld_l hQR) x hxR' (mem_fld_l hxy)
        rw [this] at h1
        exact hQc ⟨Q', h1⟩
  · ext x
    show x ∈ codom (relSigma P) \ dom (relSigma P) ↔ x ∈ Beg ʻʻ Cnv ʻʻ refs Beg P˘
    have e : x ∈ Beg ʻʻ Cnv ʻʻ refs Beg P˘ ↔
        ∃ Q, (Q ∈ codom P ∧ Q ∉ dom P) ∧ (x ∈ codom Q ∧ x ∉ dom Q) := by
      constructor
      · rintro ⟨T, hT, hxT⟩
        obtain ⟨Q, hQ, rfl⟩ := mem_Cnv_img.1 hT
        exact ⟨Q, hQ, hxT⟩
      · rintro ⟨Q, hQ, hxQ⟩
        exact ⟨Q˘, mem_Cnv_img.2 ⟨Q, hQ, rfl⟩, hxQ⟩
    rw [e]
    constructor
    · rintro ⟨⟨y, hyx⟩, hd⟩
      have hd' : ∀ z, ¬ relSigma P x z := fun z hz => hd ⟨z, hz⟩
      have notd : ∀ Q, x ∈ fld Q → Q ∉ dom P := by
        rintro Q hxQ ⟨Q', hQ'⟩
        obtain ⟨z, hz⟩ := ne Q' (mem_fld_r hQ')
        exact hd' z ((relSigma_apply P x z).2 (Or.inr ⟨Q, Q', ⟨hxQ, hz⟩, hQ'⟩))
      have notdQ : ∀ Q, Q ∈ fld P → x ∉ dom Q := by
        rintro Q hQ ⟨z, hz⟩
        exact hd' z ((relSigma_apply P x z).2 (Or.inl ⟨Q, hQ, hz⟩))
      rcases (relSigma_apply P y x).1 hyx with ⟨Q, hQ, h1⟩ | ⟨R, Q, ⟨-, hxQ⟩, h1⟩
      · have hQc : Q ∈ codom P := by
          rcases hQ with ⟨Q', hQ' | hQ'⟩
          exacts [absurd ⟨Q', hQ'⟩ (notd Q (mem_fld_r h1)), ⟨Q', hQ'⟩]
        exact ⟨Q, ⟨hQc, notd Q (mem_fld_r h1)⟩, ⟨y, h1⟩, notdQ Q hQ⟩
      · have hQ : Q ∈ fld P := mem_fld_r h1
        refine ⟨Q, ⟨⟨R, h1⟩, notd Q hxQ⟩, ?_, notdQ Q hQ⟩
        rcases hxQ with ⟨z, hz | hz⟩
        exacts [absurd ⟨z, hz⟩ (notdQ Q hQ), ⟨z, hz⟩]
    · rintro ⟨Q, ⟨⟨R, hRQ⟩, hQd⟩, ⟨y, hyx⟩, hxd⟩
      refine ⟨⟨y, (relSigma_apply P y x).2 (Or.inl ⟨Q, mem_fld_r hRQ, hyx⟩)⟩, ?_⟩
      rintro ⟨z, hz⟩
      rcases (relSigma_apply P x z).1 hz with ⟨Q', hQ', h1⟩ | ⟨Q', R', ⟨hxQ', -⟩, h1⟩
      · have := h Q' Q hQ' (mem_fld_r hRQ) x (mem_fld_l h1) (mem_fld_r hyx)
        rw [this] at h1
        exact hxd ⟨z, h1⟩
      · have := h Q' Q (mem_fld_l h1) (mem_fld_r hRQ) x hxQ' (mem_fld_r hyx)
        rw [this] at h1
        exact hQd ⟨R', h1⟩

/-- ✱163·3. \(\vdash :Q\in \text{Rel}^{2}\text{excl}.S\in \text{Cls}\rightarrow 1.\supset .S\dagger ^{;}Q\in \text{Rel}^{2}\text{excl}\) -/
theorem pm163_3 {α β : Type*} {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    Q ∈ Rel2excl ∧ S ∈ arrow Cls one → daggerRel S ⁏ Q ∈ Rel2excl := by
  rintro ⟨h, hS⟩
  rw [excl_iff'] at h ⊢
  have hf : fld (daggerRel S ⁏ Q) = daggerRel S ʻʻ fld Q := fld_semi_graph _ _
  rw [hf]
  rintro T T' ⟨M, hM, hT⟩ ⟨N, hN, hT'⟩ x hxT hxT'
  have e1 : T = S ⁏ M := hT
  have e2 : T' = S ⁏ N := hT'
  rw [e1] at hxT
  rw [e2] at hxT'
  obtain ⟨u, hu, hxu⟩ := fld_semi_sub S M hxT
  obtain ⟨v, hv, hxv⟩ := fld_semi_sub S N hxT'
  have : u = v := mem_arrow_Cls_one.1 hS x u v ⟨hxu, hxv⟩
  rw [this] at hu
  rw [e1, e2, h M N hM hN v hu hv]

/-- ✱163·31. \(\vdash \colon\ldotp CʻP=CʻQ.\supset :P\in \text{Rel}^{2}\text{excl}.\equiv .Q\in \text{Rel}^{2}\text{excl} \quad[*163·1.*13·12]\) -/
theorem pm163_31 {α : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop} :
    fld P = fld Q → (P ∈ Rel2excl ↔ Q ∈ Rel2excl) := by
  intro h
  rw [mem_Rel2excl, mem_Rel2excl, h]

/-- ✱163·311. \(\vdash \colon\ldotp CʻQ=\text{Cnv}ʻʻCʻP.\supset :P\in \text{Rel}^{2}\text{excl}.\equiv .Q\in \text{Rel}^{2}\text{excl}\) -/
theorem pm163_311 {α : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop} :
    fld Q = Cnv ʻʻ fld P → (P ∈ Rel2excl ↔ Q ∈ Rel2excl) := by
  intro h
  rw [excl_iff', excl_iff']
  constructor
  · intro hP T T' hT hT' x hxT hxT'
    rw [h] at hT hT'
    obtain ⟨M, hM, rfl⟩ := mem_Cnv_img.1 hT
    obtain ⟨N, hN, rfl⟩ := mem_Cnv_img.1 hT'
    rw [fld_cnv'] at hxT hxT'
    rw [hP M N hM hN x hxT hxT']
  · intro hQ M N hM hN x hxM hxN
    have h1 : M˘ ∈ fld Q := by rw [h]; exact mem_Cnv_img.2 ⟨M, hM, rfl⟩
    have h2 : N˘ ∈ fld Q := by rw [h]; exact mem_Cnv_img.2 ⟨N, hN, rfl⟩
    have := hQ _ _ h1 h2 x (by rw [fld_cnv']; exact hxM) (by rw [fld_cnv']; exact hxN)
    exact congrArg cnv this

/-- ✱163·32. \[\begin{align}\vdash :P\in \text{Rel}^{2}\text{excl}.&\equiv .\breve{P} \in \text{Rel}^{2}\text{excl}.\equiv .\text{Cnv}^{;}P\in \text{Rel}^{2}\text{excl}.\equiv .\\ &\text{Cnv}^{;}\breve{P} \in \text{Rel}^{2}\text{excl}\quad[*163·31·311.*33·22.*150·22·12]\end{align}\]

`Cnv;P` is `Cnv ⁏ P`; the chain is the conjunction of its links. -/
theorem pm163_32 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    ((P ∈ Rel2excl ↔ P˘ ∈ Rel2excl) ∧ (P˘ ∈ Rel2excl ↔ Cnv ⁏ P ∈ Rel2excl)) ∧
      (Cnv ⁏ P ∈ Rel2excl ↔ Cnv ⁏ P˘ ∈ Rel2excl) := by
  have a : P ∈ Rel2excl ↔ P˘ ∈ Rel2excl := pm163_31 (fld_cnv' P).symm
  have b : P ∈ Rel2excl ↔ Cnv ⁏ P ∈ Rel2excl := pm163_311 (fld_Cnv_semi P)
  have c : Cnv ⁏ P ∈ Rel2excl ↔ Cnv ⁏ P˘ ∈ Rel2excl :=
    pm163_31 (by rw [fld_Cnv_semi, fld_Cnv_semi, fld_cnv'])
  exact ⟨⟨a, a.symm.trans b⟩, c⟩

/-- ✱163·33. \(\vdash :P\unicode{x2909}Q\in \text{Rel}^{2}\text{excl}.\equiv .Q\unicode{x2909}P\in \text{Rel}^{2}\text{excl} \quad[*163·31.*160·14]\) -/
theorem pm163_33 {α : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ⤉ Q ∈ Rel2excl ↔ Q ⤉ P ∈ Rel2excl :=
  pm163_31 (by rw [fld_rsum, fld_rsum, Set.union_comm])

/-- ✱163·331. \[\begin{align}&\vdash :P\unicode{x21f8} R\in \text{Rel}^{2}\text{excl}.\equiv .R\unicode{x21f7}P\in \text{Rel}^{2}\text{excl}\\ &[*163·31.*161·14·2·201]\end{align}\] -/
theorem pm163_331 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {R : α → α → Prop} :
    P ⇸ R ∈ Rel2excl ↔ R ⇷ P ∈ Rel2excl := by
  by_cases h : rEx P
  · exact pm163_31 (by rw [fld_addLast h, fld_addFirst h])
  · rw [eq_rNull_of_not_rEx h, addLast_rNull, addFirst_rNull]

/-- ✱163·4. \(\vdash .\dot{\Lambda} \in \text{Rel}^{2}\text{excl}\) -/
theorem pm163_4 {α : Type*} : (rNull : (α → α → Prop) → (α → α → Prop) → Prop) ∈ Rel2excl := by
  rw [excl_iff']
  intro Q R hQ
  rw [fld_rNull] at hQ
  simp at hQ

/-- ✱163·41. \(\vdash .P\downarrow P\in \text{Rel}^{2}\text{excl}\) -/
theorem pm163_41 {α : Type*} {P : α → α → Prop} : P ↓ P ∈ Rel2excl := by
  rw [excl_iff', fld_couple, Set.union_self]
  intro Q R hQ hR _ _ _
  rw [mem_unitCls] at hQ hR
  rw [hQ, hR]

/-- ✱163·42. \(\vdash \colon\ldotp P\downarrow Q\in \text{Rel}^{2}\text{excl}.\equiv :P=Q.\lor.CʻP\cap CʻQ=\Lambda \) -/
theorem pm163_42 {α : Type*} {P Q : α → α → Prop} :
    P ↓ Q ∈ Rel2excl ↔ P = Q ∨ fld P ∩ fld Q = Λ := by
  constructor
  · intro h
    by_cases e : P = Q
    · exact Or.inl e
    · refine Or.inr (h P Q ⟨⟨?_, ?_⟩, e⟩)
      · rw [fld_couple]; exact Or.inl (mem_unitCls.2 rfl)
      · rw [fld_couple]; exact Or.inr (mem_unitCls.2 rfl)
  · rintro (e | e)
    · rw [e]; exact pm163_41
    · intro T T' ⟨⟨hT, hT'⟩, hne⟩
      rw [fld_couple] at hT hT'
      rcases hT with hT | hT <;> rcases hT' with hT' | hT' <;> rw [mem_unitCls] at hT hT' <;>
        rw [hT, hT'] at hne ⊢
      · exact absurd rfl hne
      · exact e
      · rw [Set.inter_comm]; exact e
      · exact absurd rfl hne

/-- ✱163·43. \(\vdash :P\in \text{Rel}^{2}\text{excl}.Q\,\unicode{x2abd}\, P.\supset .Q\in \text{Rel}^{2}\text{excl}\) -/
theorem pm163_43 {α : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ∧ Q ⪽ P → Q ∈ Rel2excl := by
  rintro ⟨h, hQ⟩ R S ⟨⟨hR, hS⟩, hne⟩
  exact h R S ⟨⟨fld_mono hQ hR, fld_mono hQ hS⟩, hne⟩

/-- ✱163·431. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\text{Rl}ʻP\subset \text{Rel}^{2}\text{excl} \quad[*163·43]\) -/
theorem pm163_431 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl → rl P ⊆ Rel2excl := fun h _ hQ => pm163_43 ⟨h, hQ⟩

/-- ✱163·44. \[\begin{align}\vdash :P\unicode{x2909}Q\in \text{Rel}^{2}&\text{excl}.\equiv .\\ &P,Q\in \text{Rel}^{2}\text{excl}.sʻCʻʻCʻP\cap sʻCʻʻ(CʻQ-CʻP)=\Lambda\end{align}\]

`P, Q ∈ Rel² excl` is the conjunction. -/
theorem pm163_44 {α : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ⤉ Q ∈ Rel2excl ↔
      (P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ sumCls (C ʻʻ fld P) ∩ sumCls (C ʻʻ (fld Q \ fld P)) = Λ := by
  rw [excl_iff', excl_iff', excl_iff', fld_rsum, inter_null_iff]
  constructor
  · intro h
    refine ⟨⟨fun T T' hT hT' => h T T' (Or.inl hT) (Or.inl hT'),
      fun T T' hT hT' => h T T' (Or.inr hT) (Or.inr hT')⟩, ?_⟩
    rintro ⟨x, hx1, hx2⟩
    obtain ⟨T, hT, hxT⟩ := mem_sumCls_C.1 hx1
    obtain ⟨T', ⟨hT', hT'P⟩, hxT'⟩ := mem_sumCls_C.1 hx2
    have := h T T' (Or.inl hT) (Or.inr hT') x hxT hxT'
    rw [this] at hT
    exact hT'P hT
  · rintro ⟨⟨hP, hQ⟩, hd⟩ T T' hT hT' x hxT hxT'
    have cross : ∀ T T', T ∈ fld P → T' ∈ fld Q → x ∈ fld T → x ∈ fld T' → T = T' := by
      intro T T' hT hT' hxT hxT'
      by_cases hT'P : T' ∈ fld P
      · exact hP T T' hT hT'P x hxT hxT'
      · exact absurd ⟨x, mem_sumCls_C.2 ⟨T, hT, hxT⟩, mem_sumCls_C.2 ⟨T', ⟨hT', hT'P⟩, hxT'⟩⟩ hd
    rcases hT with hT | hT <;> rcases hT' with hT' | hT'
    · exact hP T T' hT hT' x hxT hxT'
    · exact cross T T' hT hT' hxT hxT'
    · exact (cross T' T hT' hT hxT' hxT).symm
    · exact hQ T T' hT hT' x hxT hxT'

/-- ✱163·441. \[\begin{align}&\vdash :P,Q\in \text{Rel}^{2}\text{excl}.Cʻ\Sigma ʻP\cap Cʻ\Sigma ʻQ=\Lambda .\supset .P\unicode{x2909}Q\in \text{Rel}^{2}\text{excl}\\ &[*163·44.*162·22]\end{align}\] -/
theorem pm163_441 {α : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop} :
    (P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ fld (relSigma P) ∩ fld (relSigma Q) = Λ →
      P ⤉ Q ∈ Rel2excl := by
  rintro ⟨hPQ, hd⟩
  refine pm163_44.2 ⟨hPQ, ?_⟩
  rw [inter_null_iff] at hd ⊢
  rintro ⟨x, hx1, hx2⟩
  obtain ⟨T, hT, hxT⟩ := mem_sumCls_C.1 hx1
  obtain ⟨T', ⟨hT', -⟩, hxT'⟩ := mem_sumCls_C.1 hx2
  exact hd ⟨x, mem_fld_relSigma.2 ⟨T, hT, hxT⟩, mem_fld_relSigma.2 ⟨T', hT', hxT'⟩⟩

/-- ✱163·442. \[\begin{align}\vdash \colon\ldotp CʻP&\cap CʻQ=\Lambda .\supset :\\ &P\unicode{x2909}Q\in \text{Rel}^{2}\text{excl}.\equiv .P,Q\in \text{Rel}^{2}\text{excl}.Cʻ\Sigma ʻP\cap Cʻ\Sigma ʻQ=\Lambda \end{align}\] -/
theorem pm163_442 {α : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop} :
    fld P ∩ fld Q = Λ →
      (P ⤉ Q ∈ Rel2excl ↔
        (P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ fld (relSigma P) ∩ fld (relSigma Q) = Λ) := by
  intro h
  have e : fld Q \ fld P = fld Q := by
    ext T; exact ⟨fun hT => hT.1, fun hT => ⟨hT, fun hP => not_mem_of_disj h hP hT⟩⟩
  rw [pm163_44, e, pm162_22, pm162_22]

/-- ✱163·45. \(\vdash :P\unicode{x2909}R\in \text{Rel}^{2}\text{excl}.\equiv .P\in \text{Rel}^{2}\text{excl}.sʻCʻʻ(CʻP-\iota ʻR)\cap CʻR=\Lambda\)

**Status.** proved (reading): transcription error: the e-text prints `P ⤉ R`, which is not
significant here (`s'C''(C'P − ι'R) ∩ C'R` makes `R` a relation of the type of the members of
`C'P`); PM's demonstration (`✱161·14 . ✱163·12 ⊃ ⊢ :. ∃̇!P . ⊃ : P ⇸ R ∈ Rel² excl . ≡ …`), the
Summary's ✱163·451 and the following ✱163·451·452·46 have `P ⇸ R`. -/
theorem pm163_45 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {R : α → α → Prop} :
    P ⇸ R ∈ Rel2excl ↔ P ∈ Rel2excl ∧ sumCls (C ʻʻ (fld P \ ι R)) ∩ fld R = Λ := by
  by_cases hP : rEx P
  · rw [excl_iff', excl_iff', fld_addLast hP, inter_null_iff]
    constructor
    · intro h
      refine ⟨fun T T' hT hT' => h T T' (Or.inl hT) (Or.inl hT'), ?_⟩
      rintro ⟨x, hx1, hx2⟩
      obtain ⟨T, ⟨hT, hTR⟩, hxT⟩ := mem_sumCls_C.1 hx1
      exact hTR (mem_unitCls.2 (h T R (Or.inl hT) (Or.inr (mem_unitCls.2 rfl)) x hxT hx2))
    · rintro ⟨h, hd⟩
      have cross : ∀ T, T ∈ fld P → ∀ x, x ∈ fld T → x ∈ fld R → T = R := by
        intro T hT x hxT hxR
        by_contra hne
        exact hd ⟨x, mem_sumCls_C.2 ⟨T, ⟨hT, fun e => hne (mem_unitCls.1 e)⟩, hxT⟩, hxR⟩
      intro T T' hT hT' x hxT hxT'
      rcases hT with hT | hT <;> rcases hT' with hT' | hT'
      · exact h T T' hT hT' x hxT hxT'
      · rw [mem_unitCls] at hT'; rw [hT'] at hxT' ⊢; exact cross T hT x hxT hxT'
      · rw [mem_unitCls] at hT; rw [hT] at hxT ⊢; exact (cross T' hT' x hxT' hxT).symm
      · rw [mem_unitCls] at hT hT'; rw [hT, hT']
  · rw [eq_rNull_of_not_rEx hP, addLast_rNull, fld_rNull]
    refine ⟨fun _ => ⟨pm163_4, ?_⟩, fun _ => pm163_4⟩
    rw [inter_null_iff]
    rintro ⟨x, hx, -⟩
    obtain ⟨T, ⟨hT, -⟩, -⟩ := mem_sumCls_C.1 hx
    simp at hT

/-- ✱163·451. \[\begin{align}&\vdash :P\in \text{Rel}^{2}\text{excl}.Cʻ\Sigma ʻP\cap CʻR=\Lambda .\supset .P\unicode{x21f8} R\in \text{Rel}^{2}\text{excl}\\ &[*163·45.*162·22]\end{align}\] -/
theorem pm163_451 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {R : α → α → Prop} :
    P ∈ Rel2excl ∧ fld (relSigma P) ∩ fld R = Λ → P ⇸ R ∈ Rel2excl := by
  rintro ⟨h, hd⟩
  refine pm163_45.2 ⟨h, ?_⟩
  rw [inter_null_iff] at hd ⊢
  rintro ⟨x, hx1, hx2⟩
  obtain ⟨T, ⟨hT, -⟩, hxT⟩ := mem_sumCls_C.1 hx1
  exact hd ⟨x, mem_fld_relSigma.2 ⟨T, hT, hxT⟩, hx2⟩

/-- ✱163·452. \[\begin{align}&\vdash \colon\ldotp R{\sim}\in CʻP.\supset :P\unicode{x21f8} R\in \text{Rel}^{2}\text{excl}.\equiv .P\in \text{Rel}^{2}\text{excl}.Cʻ\Sigma ʻP\cap CʻR=\Lambda \\ &[*51·222.*163·45.*162·22]\end{align}\] -/
theorem pm163_452 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {R : α → α → Prop} :
    R ∉ fld P → (P ⇸ R ∈ Rel2excl ↔ P ∈ Rel2excl ∧ fld (relSigma P) ∩ fld R = Λ) := by
  intro hR
  have e : fld P \ ι R = fld P := by
    ext T
    exact ⟨fun hT => hT.1, fun hT => ⟨hT, fun e => hR (by rw [← mem_unitCls.1 e]; exact hT)⟩⟩
  rw [pm163_45, e, pm162_22]

/-- ✱163·46. \[\begin{align}&\vdash :R\unicode{x21f7}P\in \text{Rel}^{2}\text{excl}.\equiv .P\in \text{Rel}^{2}\text{excl}.sʻCʻʻ(CʻP-{℩}ʻR)\cap CʻR=\Lambda \\ &[*163·45·331]\end{align}\]

`{℩}'R` is `ι'R`. -/
theorem pm163_46 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {R : α → α → Prop} :
    R ⇷ P ∈ Rel2excl ↔ P ∈ Rel2excl ∧ sumCls (C ʻʻ (fld P \ ι R)) ∩ fld R = Λ :=
  pm163_331.symm.trans pm163_45

/-- ✱163·461. \[\begin{align}&\vdash :P\in \text{Rel}^{2}\text{excl}.Cʻ\Sigma ʻP\cap CʻR=\Lambda .\supset .R\unicode{x21f7}P\in \text{Rel}^{2}\text{excl}\\ &[*163·451·331]\end{align}\] -/
theorem pm163_461 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {R : α → α → Prop} :
    P ∈ Rel2excl ∧ fld (relSigma P) ∩ fld R = Λ → R ⇷ P ∈ Rel2excl := fun h =>
  pm163_331.1 (pm163_451 h)

/-- ✱163·462. \[\begin{align}&\vdash \colon\ldotp R{\sim}\in CʻP.\supset :R\unicode{x21f7}P\in \text{Rel}^{2}\text{excl}.\equiv .P\in \text{Rel}^{2}\text{excl}.Cʻ\Sigma ʻP\cap CʻR=\Lambda \\ &[*163·452·331]\end{align}\] -/
theorem pm163_462 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {R : α → α → Prop} :
    R ∉ fld P → (R ⇷ P ∈ Rel2excl ↔ P ∈ Rel2excl ∧ fld (relSigma P) ∩ fld R = Λ) := fun h =>
  pm163_331.symm.trans (pm163_452 h)

/-!
## [✱164] Double likeness

*(Vol. 2, p. 376)*

> *Summary of* *164.
>
> …

**Lean reading.** `P smor̄ smor̄ Q` is `smorsmorbar P Q` and `smor smor` is `smorsmor`, for
relations of relations `P` (members of `C'P` on `α`) and `Q` (on `β`); the double correlators
are `S : α → β → Prop`. `S†` is the relation `daggerRel S` (so `S†;Q` is `daggerRel S ⁏ Q` and
`(S†) ↾ C'Q` is `daggerRel S ↾ fld Q`), `ᗡ'S = C'Σ'Q` is `codom S = fld (relSigma Q)` (as printed
in ✱164·1; the Df has `ᗡ⃖'C'Σ'Q`), `κ sm̄ sm̄ λ` is Defs/Part3's `smsmbar`, `Rl'smor` is `rl smor`,
`Cl'Nr'P` is `cl (nr α P)`, `∈_Δ'μ` is `sel memRel μ`. In ✱164·4–·43 `R` and `S` are arbitrary
relations whose descriptive functions need not exist: `R'N ∈ (S'N) smor̄ N` is
`Desc R N (fun T => Desc S N (fun M => T ∈ smorbar M N))` (the first description has the larger
scope, ✱14·03), "Hp ✱164·4" and "Hp ✱164·41" are written out, and in ✱164·413 `N` is a real
variable. In ✱164·43·431·432·433 `(S'N) smor̄ N` keeps its description,
`Desc S N (fun M => λ = smorbar M N)`. `Mult ax` is taken at the type of the correlators whose
classes are selected, `MultAx (α → β → Prop)`; it is a theorem of Lean but is kept as a
hypothesis. In ✱164·47·48 `R, S ∈ Nr'Q` does not identify the types of `R` and `S` (as
`μ, ν ∈ NR`, Defs/Part4 decision 2).

**Status.** proved (all propositions; ✱164·01·02 definition; ✱164·43 proved (reading), see its
docstring)
-/

/-- ✱164·01 (Df). \(P\,\overline{\text{smor}} \,\overline{\text{smor}}\, Q=(1\rightarrow 1)\cap \overleftarrow{\text{ᗡ}}ʻCʻ\Sigma ʻQ\cap \hat{S} (P=S\dagger ^{;}Q) \quad\text{Df}\) -/
theorem pm164_01 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmorbar P Q = arrow one one ∩ rels Dcnv (fld (relSigma Q)) ∩ {S | P = daggerRel S ⁏ Q} :=
  rfl

/-- ✱164·02 (Df). \(\text{smor} \text{smor} =\hat{P} \hat{Q} (\exists !P\,\overline{\text{smor}} \,\overline{\text{smor}}\, Q) \quad\text{Df}\) -/
theorem pm164_02 {α β : Type*} :
    (smorsmor : ((α → α → Prop) → (α → α → Prop) → Prop) →
      ((β → β → Prop) → (β → β → Prop) → Prop) → Prop) = fun P Q => (smorsmorbar P Q).Nonempty :=
  rfl

/-- ✱164·1. \[\begin{align}&\vdash :S\in P\,\overline{\text{smor}} \,\overline{\text{smor}}\, Q.\equiv .S\in 1\rightarrow 1.\text{ᗡ}ʻS=Cʻ\Sigma ʻQ.P=S\dagger ^{;}Q\\ &[(*164·01)]\end{align}\] -/
theorem pm164_1 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    S ∈ smorsmorbar P Q ↔
      (S ∈ arrow one one ∧ codom S = fld (relSigma Q)) ∧ P = daggerRel S ⁏ Q :=
  smorsmorbar_iff

/-- ✱164·11. \(\vdash :P \,\text{smor} \text{smor} Q.\equiv .\exists !P\,\overline{\text{smor}} \,\overline{\text{smor}}\, Q \quad[(*164·02)]\) -/
theorem pm164_11 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor P Q ↔ (smorsmorbar P Q).Nonempty := Iff.rfl

/-- ✱164·12. \[\begin{align}&\vdash :P \,\text{smor} \text{smor} Q.\equiv .(\exists S).S\in 1\rightarrow 1.\text{ᗡ}ʻS=Cʻ\Sigma ʻQ.P=S\dagger ^{;}Q\\ &[*164·1·11]\end{align}\] -/
theorem pm164_12 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor P Q ↔
      ∃ S : α → β → Prop, (S ∈ arrow one one ∧ codom S = fld (relSigma Q)) ∧ P = daggerRel S ⁏ Q :=
  ⟨fun ⟨S, h⟩ => ⟨S, smorsmorbar_iff.1 h⟩, fun ⟨S, h⟩ => ⟨S, smorsmorbar_iff.2 h⟩⟩

/-- ✱164·13. \[\begin{align}&\vdash :S\upharpoonright Cʻ\Sigma ʻQ\in 1\rightarrow 1.Cʻ\Sigma ʻQ\subset \text{ᗡ}ʻS.\supset .(S\dagger )\upharpoonright CʻQ\in 1\rightarrow 1\\ &[*150·152.*162·22]\end{align}\]

`(S†) ↾ C'Q` is `daggerRel S ↾ fld Q`. -/
theorem pm164_13 {α β : Type*} {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    S ↾ fld (relSigma Q) ∈ arrow one one ∧ fld (relSigma Q) ⊆ codom S →
      daggerRel S ↾ fld Q ∈ arrow one one := by
  rintro ⟨h1, h2⟩
  have hsub : ∀ M, M ∈ fld Q → fld M ⊆ fld (relSigma Q) := fun M hM z hz =>
    mem_fld_relSigma.2 ⟨M, hM, hz⟩
  rw [oneone_iff] at h1 ⊢
  refine ⟨fun X Y M h => ?_, fun X M N h => ?_⟩
  · obtain ⟨⟨hX, -⟩, ⟨hY, -⟩⟩ := h
    have hX' : X = S ⁏ M := hX
    have hY' : Y = S ⁏ M := hY
    rw [hX', hY']
  · obtain ⟨⟨hM, hMQ⟩, ⟨hN, hNQ⟩⟩ := h
    have hM' : X = S ⁏ M := hM
    have hN' : X = S ⁏ N := hN
    have e : S ⁏ M = S ⁏ N := hM'.symm.trans hN'
    have key : ∀ M N, M ∈ fld Q → N ∈ fld Q → S ⁏ M = S ⁏ N → ∀ a b, M a b → N a b := by
      intro M N hM hN e a b hab
      obtain ⟨x, hxa⟩ := h2 (hsub M hM (mem_fld_l hab))
      obtain ⟨y, hyb⟩ := h2 (hsub M hM (mem_fld_r hab))
      have : (S ⁏ N) x y := by rw [← e]; exact (semi_iff' S M x y).2 ⟨a, b, hxa, hyb, hab⟩
      obtain ⟨c, d, hxc, hyd, hcd⟩ := (semi_iff' S N x y).1 this
      have hac : a = c := h1.2 x a c
        ⟨⟨hxa, hsub M hM (mem_fld_l hab)⟩, ⟨hxc, hsub N hN (mem_fld_l hcd)⟩⟩
      have hbd : b = d := h1.2 y b d
        ⟨⟨hyb, hsub M hM (mem_fld_r hab)⟩, ⟨hyd, hsub N hN (mem_fld_r hcd)⟩⟩
      rw [hac, hbd]; exact hcd
    exact rel_ext' fun a b => ⟨key M N hMQ hNQ e a b, key N M hNQ hMQ e.symm a b⟩

/-- ✱164·131. \(\vdash :\text{ᗡ}ʻS=Cʻ\Sigma ʻQ.P=S\dagger ^{;}Q.\supset .\text{D}ʻS=Cʻ\Sigma ʻP.\Sigma ʻP=S^{;}\Sigma ʻQ\) -/
theorem pm164_131 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    codom S = fld (relSigma Q) ∧ P = daggerRel S ⁏ Q →
      dom S = fld (relSigma P) ∧ relSigma P = S ⁏ relSigma Q := by
  rintro ⟨h1, h2⟩
  have e : relSigma P = S ⁏ relSigma Q := by rw [h2]; exact pm162_35 h1.ge
  refine ⟨?_, e⟩
  rw [e, fld_semi_of h1.ge, ← h1, img_codom]

/-- ✱164·14. \(\vdash :S\in P\,\overline{\text{smor}} \,\overline{\text{smor}}\, Q.\supset .S\in \Sigma ʻP\overline{\text{smor}} \Sigma ʻQ \quad[*164·1·131.*151·11]\) -/
theorem pm164_14 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    S ∈ smorsmorbar P Q → S ∈ smorbar (relSigma P) (relSigma Q) := by
  intro h
  obtain ⟨⟨h1, h2⟩, h3⟩ := smorsmorbar_iff.1 h
  exact ⟨⟨h1, h2.symm⟩, (pm164_131 ⟨h2, h3⟩).2⟩

/-- ✱164·141. \(\vdash :Cʻ\Sigma ʻQ\subset \alpha .\supset .(T\upharpoonright \alpha )\dagger ^{;}Q=T\dagger ^{;}Q \quad[*150·171.*162·22]\)

`T ↾ α` is `T ↾ A`; `(T ↾ α)†;Q` is `daggerRel (T ↾ A) ⁏ Q`. -/
theorem pm164_141 {α β : Type*} {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop}
    {A : Set β} : fld (relSigma Q) ⊆ A → daggerRel (T ↾ A) ⁏ Q = daggerRel T ⁏ Q := by
  intro h
  have key : ∀ M, M ∈ fld Q → (T ↾ A) ⁏ M = T ⁏ M := fun M hM =>
    cres_semi_of fun z hz => h (mem_fld_relSigma.2 ⟨M, hM, hz⟩)
  refine rel_ext' fun X Y => ?_
  rw [semi_dagger_apply, semi_dagger_apply]
  constructor
  · rintro ⟨M, N, ⟨rfl, rfl⟩, hMN⟩
    exact ⟨M, N, ⟨key M (mem_fld_l hMN), key N (mem_fld_r hMN)⟩, hMN⟩
  · rintro ⟨M, N, ⟨rfl, rfl⟩, hMN⟩
    exact ⟨M, N, ⟨(key M (mem_fld_l hMN)).symm, (key N (mem_fld_r hMN)).symm⟩, hMN⟩

/-- ✱164·142. \(\vdash .(T\upharpoonright Cʻ\Sigma ʻQ)\dagger ^{;}Q=T\dagger ^{;}Q=\{(T\dagger )\upharpoonright CʻQ\}^{;}Q \quad[*164·141.*150·32]\)

The chain is the conjunction of its links. -/
theorem pm164_142 {α β : Type*} {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop} :
    daggerRel (T ↾ fld (relSigma Q)) ⁏ Q = daggerRel T ⁏ Q ∧
      daggerRel T ⁏ Q = (daggerRel T ↾ fld Q) ⁏ Q :=
  ⟨pm164_141 Set.Subset.rfl, (cres_semi_of Set.Subset.rfl).symm⟩

/-- ✱164·143. \(\vdash :S\in P\,\overline{\text{smor}} \,\overline{\text{smor}}\, Q.\supset .(S\dagger )\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q\) -/
theorem pm164_143 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    S ∈ smorsmorbar P Q → daggerRel S ↾ fld Q ∈ smorbar P Q := by
  intro h
  obtain ⟨⟨h1, h2⟩, h3⟩ := smorsmorbar_iff.1 h
  refine ⟨⟨pm164_13 ⟨cres_oneone h1, h2.ge⟩, codom_cres_eq.2 fun M _ => ⟨S ⁏ M, rfl⟩⟩, ?_⟩
  rw [cres_semi_of Set.Subset.rfl]
  exact h3

/-- ✱164·15. \(\vdash :S\in P\,\overline{\text{smor}} \,\overline{\text{smor}}\, Q.\equiv .S\in \Sigma ʻP\overline{\text{smor}} \Sigma ʻQ.(S\dagger )\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q\) -/
theorem pm164_15 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    S ∈ smorsmorbar P Q ↔
      S ∈ smorbar (relSigma P) (relSigma Q) ∧ daggerRel S ↾ fld Q ∈ smorbar P Q := by
  constructor
  · intro h; exact ⟨pm164_14 h, pm164_143 h⟩
  · rintro ⟨⟨⟨h1, h2⟩, -⟩, ⟨-, h4⟩⟩
    refine smorsmorbar_iff.2 ⟨⟨h1, h2.symm⟩, ?_⟩
    rw [h4, cres_semi_of Set.Subset.rfl]

/-- ✱164·151. \(\vdash :P\,\text{smor}\,\text{smor}\,Q.\supset .\Sigma ʻP\,\text{smor}\,\Sigma ʻQ.P\,\text{smor}\,Q \quad[*164·15·11]\) -/
theorem pm164_151 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor P Q → smor (relSigma P) (relSigma Q) ∧ smor P Q := by
  rintro ⟨S, hS⟩
  obtain ⟨h1, h2⟩ := pm164_15.1 hS
  exact ⟨⟨S, h1⟩, ⟨_, h2⟩⟩

/-- ✱164·16. \(\vdash :S\in P\,\overline{\text{smor}} \,\overline{\text{smor}}\, Q.\supset .(S\dagger )\upharpoonright CʻQ\,\unicode{x2abd}\, \text{smor}\) -/
theorem pm164_16 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    S ∈ smorsmorbar P Q → daggerRel S ↾ fld Q ⪽ smor := by
  intro h
  obtain ⟨⟨h1, h2⟩, -⟩ := smorsmorbar_iff.1 h
  rintro X M ⟨hX, hM⟩
  have hX' : X = S ⁏ M := hX
  have hsub : fld M ⊆ codom S := fun z hz => by
    rw [h2]; exact mem_fld_relSigma.2 ⟨M, hM, hz⟩
  refine ⟨S ↾ fld M, ⟨cres_oneone h1, codom_cres_eq.2 hsub⟩, ?_⟩
  rw [hX', cres_semi_of Set.Subset.rfl]

/-- ✱164·17. \(\vdash :P\,\text{smor}\,\text{smor}\,Q.\supset .\exists !P\,\overline{\text{smor}}\,Q\cap \text{Rl}ʻ\text{smor} \quad[*164·143·16]\) -/
theorem pm164_17 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor P Q → (smorbar P Q ∩ rl smor).Nonempty := by
  rintro ⟨S, hS⟩
  exact ⟨_, pm164_143 hS, pm164_16 hS⟩

/-- ✱164·18. \[\begin{align}\vdash :S\upharpoonright Cʻ\Sigma ʻQ\in P\,\overline{\text{smor}}\,&\overline{\text{smor}}\,Q.\equiv .\\ &S\upharpoonright Cʻ\SigmaʻQ \in 1\rightarrow 1.Cʻ\Sigma ʻQ\subset \text{ᗡ}ʻS.P=S\dagger ^{;}Q\end{align}\] -/
theorem pm164_18 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    S ↾ fld (relSigma Q) ∈ smorsmorbar P Q ↔
      (S ↾ fld (relSigma Q) ∈ arrow one one ∧ fld (relSigma Q) ⊆ codom S) ∧
        P = daggerRel S ⁏ Q := by
  rw [smorsmorbar_iff, pm164_141 Set.Subset.rfl]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    rw [← codom_cres_eq]; exact h2.symm
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, (codom_cres_eq.2 h2).symm⟩, h3⟩

/-- ✱164·181. \(\vdash : P \,\text{smor} \text{smor} Q. \equiv . (\exists S). S\upharpoonright Cʻ\Sigma ʻQ\in 1\rightarrow 1. Cʻ\Sigma ʻQ \subset \text{ᗡ}ʻS. P = S\dagger ^{;} Q\) -/
theorem pm164_181 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor P Q ↔
      ∃ S : α → β → Prop, (S ↾ fld (relSigma Q) ∈ arrow one one ∧ fld (relSigma Q) ⊆ codom S) ∧
        P = daggerRel S ⁏ Q := by
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := smorsmorbar_iff.1 hS
    exact ⟨S, ⟨cres_oneone h1, h2.ge⟩, h3⟩
  · rintro ⟨S, h⟩
    exact ⟨_, pm164_18.2 h⟩

/-- ✱164·2. \(\vdash . I\upharpoonright Cʻ\Sigma ʻP\in P \,\overline{\text{smor}}\,\overline{\text{smor}}\, P\) -/
theorem pm164_2 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    I ↾ fld (relSigma P) ∈ smorsmorbar P P := by
  refine pm164_18.2 ⟨⟨cres_oneone I_oneone, fun y _ => ⟨y, rfl⟩⟩, ?_⟩
  refine rel_ext' fun X Y => ?_
  rw [semi_dagger_apply]
  constructor
  · intro h; exact ⟨X, Y, ⟨(semi_I X).symm, (semi_I Y).symm⟩, h⟩
  · rintro ⟨M, N, ⟨rfl, rfl⟩, h⟩; rw [semi_I, semi_I]; exact h

/-- ✱164·201. \(\vdash . P \,\text{smor smor}\, P \quad[*164·2·11]\) -/
theorem pm164_201 {α : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} : smorsmor P P :=
  ⟨_, pm164_2⟩

private theorem smorsmorbar_cnv {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop}
    (h : S ∈ smorsmorbar P Q) : S˘ ∈ smorsmorbar Q P := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := smorsmorbar_iff.1 h
  obtain ⟨h4, -⟩ := pm164_131 ⟨h2, h3⟩
  refine smorsmorbar_iff.2 ⟨⟨cnv_oneone h1, h4⟩, ?_⟩
  have hc : ∀ M, M ∈ fld Q → S˘ ⁏ (S ⁏ M) = M := fun M hM =>
    cnv_semi_semi' (oneone_Cls_one h1) fun z hz => by
      rw [h2]; exact mem_fld_relSigma.2 ⟨M, hM, hz⟩
  rw [h3]
  refine rel_ext' fun M N => ?_
  rw [semi_dagger_apply]
  constructor
  · intro hMN
    exact ⟨S ⁏ M, S ⁏ N, ⟨(hc M (mem_fld_l hMN)).symm, (hc N (mem_fld_r hMN)).symm⟩,
      (semi_dagger_apply S Q _ _).2 ⟨M, N, ⟨rfl, rfl⟩, hMN⟩⟩
  · rintro ⟨X, Y, ⟨rfl, rfl⟩, hXY⟩
    obtain ⟨M, N, ⟨rfl, rfl⟩, hMN⟩ := (semi_dagger_apply S Q _ _).1 hXY
    rw [hc M (mem_fld_l hMN), hc N (mem_fld_r hMN)]
    exact hMN

/-- ✱164·21. \(\vdash : S\in P \,\overline{\text{smor}}\,\overline{\text{smor}}\, Q. \equiv . \breve{S} \in Q \,\overline{\text{smor}}\,\overline{\text{smor}}\, P\) -/
theorem pm164_21 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    S ∈ smorsmorbar P Q ↔ S˘ ∈ smorsmorbar Q P :=
  ⟨smorsmorbar_cnv, fun h => smorsmorbar_cnv h⟩

/-- ✱164·211. \(\vdash : P \,\text{smor}\,\text{smor}\,Q. \equiv . Q\,\text{smor}\,\text{smor}\,P \quad[*164·21·11]\) -/
theorem pm164_211 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} : smorsmor P Q ↔ smorsmor Q P :=
  ⟨fun ⟨_, h⟩ => ⟨_, smorsmorbar_cnv h⟩, fun ⟨_, h⟩ => ⟨_, smorsmorbar_cnv h⟩⟩

/-- ✱164·22. \(\vdash :S\in P \,\overline{\text{smor}}\,\overline{\text{smor}}\, Q. T\in Q \,\overline{\text{smor}}\,\overline{\text{smor}}\, R. \supset . S\mid T\in P \,\overline{\text{smor}}\,\overline{\text{smor}}\, R\) -/
theorem pm164_22 {α β γ : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {R : (γ → γ → Prop) → (γ → γ → Prop) → Prop}
    {S : α → β → Prop} {T : β → γ → Prop} :
    S ∈ smorsmorbar P Q ∧ T ∈ smorsmorbar Q R → S ⨾ T ∈ smorsmorbar P R := by
  rintro ⟨hS, hT⟩
  obtain ⟨⟨oS, cS⟩, eP⟩ := smorsmorbar_iff.1 hS
  obtain ⟨⟨oT, cT⟩, eQ⟩ := smorsmorbar_iff.1 hT
  obtain ⟨dT, -⟩ := pm164_131 ⟨cT, eQ⟩
  refine smorsmorbar_iff.2 ⟨⟨oneone_comp oS oT, ?_⟩, ?_⟩
  · rw [← cT]
    ext z
    constructor
    · rintro ⟨x, y, -, hyz⟩; exact ⟨y, hyz⟩
    · rintro ⟨y, hyz⟩
      have : y ∈ codom S := by rw [cS, ← dT]; exact ⟨z, hyz⟩
      obtain ⟨x, hxy⟩ := this
      exact ⟨x, y, hxy, hyz⟩
  · rw [eP, eQ]
    refine rel_ext' fun X Y => ?_
    rw [semi_dagger_apply, semi_dagger_apply]
    constructor
    · rintro ⟨M, N, ⟨rfl, rfl⟩, hMN⟩
      obtain ⟨M', N', ⟨rfl, rfl⟩, h⟩ := (semi_dagger_apply T R M N).1 hMN
      exact ⟨M', N', ⟨semi_semi S T M', semi_semi S T N'⟩, h⟩
    · rintro ⟨M', N', ⟨rfl, rfl⟩, h⟩
      exact ⟨T ⁏ M', T ⁏ N', ⟨(semi_semi S T M').symm, (semi_semi S T N').symm⟩,
        (semi_dagger_apply T R _ _).2 ⟨M', N', ⟨rfl, rfl⟩, h⟩⟩

/-- ✱164·221. \(\vdash :P \,\text{smor}\,\text{smor}\,Q.Q\,\text{smor}\,\text{smor}\,R.\supset .P \,\text{smor} \text{smor} R \quad[*164·22·11]\) -/
theorem pm164_221 {α β γ : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {R : (γ → γ → Prop) → (γ → γ → Prop) → Prop} :
    smorsmor P Q ∧ smorsmor Q R → smorsmor P R := by
  rintro ⟨⟨S, hS⟩, ⟨T, hT⟩⟩
  exact ⟨_, pm164_22 ⟨hS, hT⟩⟩

/-- ✱164·23. \(\vdash \colon\ldotp P \,\text{smor}\,\text{smor}\,Q.\supset :P \in \text{Rel}^{2}\text{excl}.\equiv .Q \in \text{Rel}^{2}\text{excl}\) -/
theorem pm164_23 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor P Q → (P ∈ Rel2excl ↔ Q ∈ Rel2excl) := by
  rintro ⟨S, hS⟩
  obtain ⟨⟨h1, -⟩, h3⟩ := smorsmorbar_iff.1 hS
  obtain ⟨⟨h1', -⟩, h3'⟩ := smorsmorbar_iff.1 (smorsmorbar_cnv hS)
  constructor
  · intro hP; rw [h3']; exact pm163_3 ⟨hP, oneone_Cls_one h1'⟩
  · intro hQ; rw [h3]; exact pm163_3 ⟨hQ, oneone_Cls_one h1⟩

/-- ✱164·3. \(\vdash :S \in P \,\overline{\text{smor}} \,\overline{\text{smor}}\, Q.\supset .S \in (CʻʻCʻP)\,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, (CʻʻCʻQ)\)

`κ sm̄ sm̄ λ` is `smsmbar K L` (✱111·01). -/
theorem pm164_3 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    S ∈ smorsmorbar P Q → S ∈ smsmbar (C ʻʻ fld P) (C ʻʻ fld Q) := by
  intro h
  obtain ⟨⟨h1, h2⟩, h3⟩ := smorsmorbar_iff.1 h
  have hsub : ∀ M, M ∈ fld Q → fld M ⊆ codom S := fun M hM z hz => by
    rw [h2]; exact mem_fld_relSigma.2 ⟨M, hM, hz⟩
  refine ⟨⟨h1, ?_⟩, ?_⟩
  · show sumCls (C ʻʻ fld Q) = codom S
    rw [h2, pm162_22]
  · show C ʻʻ fld P = imgRel S ʻʻ C ʻʻ fld Q
    rw [h3, show fld (daggerRel S ⁏ Q) = daggerRel S ʻʻ fld Q from fld_semi_graph _ _]
    ext A
    constructor
    · rintro ⟨X, ⟨M, hM, hX⟩, hA⟩
      have hX' : X = S ⁏ M := hX
      have hA' : A = fld X := hA
      refine ⟨fld M, ⟨M, hM, rfl⟩, ?_⟩
      show A = S ʻʻ fld M
      rw [hA', hX', fld_semi_of (hsub M hM)]
    · rintro ⟨B, ⟨M, hM, hB⟩, hA⟩
      have hB' : B = fld M := hB
      have hA' : A = S ʻʻ B := hA
      refine ⟨S ⁏ M, ⟨M, hM, rfl⟩, ?_⟩
      show A = fld (S ⁏ M)
      rw [hA', hB', fld_semi_of (hsub M hM)]

/-- ✱164·301. \(\vdash :P \,\text{smor}\,\text{smor}\,Q.\supset .CʻʻCʻP \text{sm sm} CʻʻCʻQ \quad[*164·3·11.*111·4]\)

`sm sm` is `smsm` (✱111·03). -/
theorem pm164_301 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor P Q → smsm (C ʻʻ fld P) (C ʻʻ fld Q) := by
  rintro ⟨S, hS⟩
  exact ⟨S, pm164_3 hS⟩

/-- ✱164·31. \(\vdash :S \in P \,\overline{\text{smor}}\,\overline{\text{smor}}\, Q. \equiv .S \in (CʻʻCʻP) \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, (CʻʻCʻQ).P=S\dagger ^{;}Q\) -/
theorem pm164_31 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : α → β → Prop} :
    S ∈ smorsmorbar P Q ↔ S ∈ smsmbar (C ʻʻ fld P) (C ʻʻ fld Q) ∧ P = daggerRel S ⁏ Q := by
  constructor
  · intro h; exact ⟨pm164_3 h, (smorsmorbar_iff.1 h).2⟩
  · rintro ⟨⟨⟨h1, h2⟩, -⟩, h3⟩
    have h2' : sumCls (C ʻʻ fld Q) = codom S := h2
    refine smorsmorbar_iff.2 ⟨⟨h1, ?_⟩, h3⟩
    rw [← h2', pm162_22]

/-- ✱164·32. \(\vdash .\dot{\Lambda} \in (\dot{\Lambda} \,\overline{\text{smor}} \,\overline{\text{smor}}\, \dot{\Lambda} ).\dot{\Lambda} \text{smor} \text{smor} \dot{\Lambda}\)

The `Λ̇`'s are of different types (PM's note): the correlator `Λ̇ : α → β → Prop`, the relations
of relations on `α`- and on `β`-relations. -/
theorem pm164_32 {α β : Type*} :
    (rNull : α → β → Prop) ∈
        smorsmorbar (rNull : (α → α → Prop) → (α → α → Prop) → Prop)
          (rNull : (β → β → Prop) → (β → β → Prop) → Prop) ∧
      smorsmor (rNull : (α → α → Prop) → (α → α → Prop) → Prop)
        (rNull : (β → β → Prop) → (β → β → Prop) → Prop) := by
  have h : (rNull : α → β → Prop) ∈
      smorsmorbar (rNull : (α → α → Prop) → (α → α → Prop) → Prop)
        (rNull : (β → β → Prop) → (β → β → Prop) → Prop) := by
    refine smorsmorbar_iff.2 ⟨⟨oneone_rNull, ?_⟩, (semi_rNull _).symm⟩
    rw [pm162_4, fld_rNull]
    ext z
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, hx⟩
    exact rNull_apply _ _ hx
  exact ⟨h, ⟨_, h⟩⟩

/-- ✱164·33. \[\begin{align}\vdash :M \in P\,\overline{\text{smor}}\,R.N \in Q \,\overline{\text{smor}}\,S.Cʻ&P \cap CʻQ = \Lambda .CʻR \cap CʻS = \Lambda .\supset .\\ &M \unicode{x228d} N \in (P \downarrow Q)\,\overline{\text{smor}} \,\overline{\text{smor}}\, (R \downarrow S)\end{align}\] -/
theorem pm164_33 {α β : Type*} {P Q : α → α → Prop} {R S : β → β → Prop} {M N : α → β → Prop} :
    ((M ∈ smorbar P R ∧ N ∈ smorbar Q S) ∧ fld P ∩ fld Q = Λ) ∧ fld R ∩ fld S = Λ →
      M ⊍ N ∈ smorsmorbar (P ↓ Q) (R ↓ S) := by
  rintro ⟨⟨⟨hM, hN⟩, h1⟩, h2⟩
  have h := pm160_47 ⟨⟨⟨h1, h2⟩, hM⟩, hN⟩
  obtain ⟨⟨o, c⟩, -⟩ := h
  obtain ⟨⟨-, cM⟩, eM⟩ := hM
  obtain ⟨⟨-, cN⟩, eN⟩ := hN
  refine smorsmorbar_iff.2 ⟨⟨o, by rw [pm162_3]; exact c.symm⟩, ?_⟩
  rw [semi_dagger_couple,
    rcup_semi_left (fun z hz hT => not_mem_of_disj h2 hz (by rw [cN]; exact hT)), rcup_comm,
    rcup_semi_left (fun z hz hT => not_mem_of_disj h2 (by rw [cM]; exact hT) hz), ← eM, ← eN]

/-- ✱164·34. \[\begin{align}\vdash :P \,\text{smor} R.Q\,\text{smor}\,S.CʻP \cap CʻQ = \Lambda .&CʻR \cap CʻS =\Lambda .\supset .\\ &P \downarrow Q\,\text{smor smor}\,R \downarrow S\\ [*164·33·11.*151·12]\end{align}\] -/
theorem pm164_34 {α β : Type*} {P Q : α → α → Prop} {R S : β → β → Prop} :
    ((smor P R ∧ smor Q S) ∧ fld P ∩ fld Q = Λ) ∧ fld R ∩ fld S = Λ →
      smorsmor (P ↓ Q) (R ↓ S) := by
  rintro ⟨⟨⟨⟨M, hM⟩, ⟨N, hN⟩⟩, h1⟩, h2⟩
  exact ⟨_, pm164_33 ⟨⟨⟨hM, hN⟩, h1⟩, h2⟩⟩

/-- ✱164·4. \(\vdash \colon\ldotp N \in CʻQ.\supset _{N}.RʻN \in (SʻN)\,\overline{\text{smor}}\,N:\supset .\text{ᗡ}ʻ\dot{s} ʻRʻʻCʻQ = Cʻ\Sigma ʻQ\)

`R'N`, `S'N` are descriptions: `R'N ∈ (S'N) smor̄ N` is
`Desc R N (fun T => Desc S N (fun M => T ∈ smorbar M N))`; `ṡ'R''C'Q` is `sumRel (R ʻʻ fld Q)`. -/
theorem pm164_4 {α β : Type*} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    {S : (α → α → Prop) → (β → β → Prop) → Prop} {R : (α → β → Prop) → (β → β → Prop) → Prop} :
    (∀ N, N ∈ fld Q → Desc R N (fun T => Desc S N (fun M => T ∈ smorbar M N))) →
      codom (sumRel (R ʻʻ fld Q)) = fld (relSigma Q) := by
  intro h
  ext y
  rw [mem_fld_relSigma]
  constructor
  · rintro ⟨x, T, ⟨N, hN, hTN⟩, hxy⟩
    obtain ⟨T', hT', M, -, hTM⟩ := h N hN
    have e : T = T' := (hT' T).1 hTN
    rw [e] at hxy
    refine ⟨N, hN, ?_⟩
    rw [hTM.1.2]; exact ⟨x, hxy⟩
  · rintro ⟨N, hN, hy⟩
    obtain ⟨T, hT, M, -, hTM⟩ := h N hN
    rw [hTM.1.2] at hy
    obtain ⟨x, hxy⟩ := hy
    exact ⟨x, T, ⟨N, hN, (hT T).2 rfl⟩, hxy⟩

/-- ✱164·41. \[\begin{align}\vdash \colon\ldotp Q \in \text{Rel}^{2}\text{excl}: N \in CʻQ.\supset _{N}.RʻN \in (SʻN)\,&\overline{\text{smor}}\,N:\supset .\\ &\dot{s} ʻRʻʻCʻQ \in 1 \rightarrow \text{Cls}\end{align}\] -/
theorem pm164_41 {α β : Type*} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    {S : (α → α → Prop) → (β → β → Prop) → Prop} {R : (α → β → Prop) → (β → β → Prop) → Prop} :
    Q ∈ Rel2excl ∧ (∀ N, N ∈ fld Q → Desc R N (fun T => Desc S N (fun M => T ∈ smorbar M N))) →
      sumRel (R ʻʻ fld Q) ∈ arrow one Cls := by
  rintro ⟨hQ, h⟩
  rw [excl_iff'] at hQ
  rw [mem_arrow_one_Cls]
  rintro x x' y ⟨⟨T, ⟨N, hN, hTN⟩, hxy⟩, ⟨T', ⟨N', hN', hTN'⟩, hx'y⟩⟩
  obtain ⟨T₀, hT₀, M, -, hTM⟩ := h N hN
  obtain ⟨T₁, hT₁, M', -, hTM'⟩ := h N' hN'
  have e0 : T = T₀ := (hT₀ T).1 hTN
  have e1 : T' = T₁ := (hT₁ T').1 hTN'
  have hyN : y ∈ fld N := by rw [hTM.1.2, ← e0]; exact ⟨x, hxy⟩
  have hyN' : y ∈ fld N' := by rw [hTM'.1.2, ← e1]; exact ⟨x', hx'y⟩
  have e : N = N' := hQ N N' hN hN' y hyN hyN'
  rw [← e] at hTN'
  have e2 : T' = T₀ := (hT₀ T').1 hTN'
  rw [e0] at hxy
  rw [e2] at hx'y
  exact (oneone_iff.1 hTM.1.1).1 x x' y ⟨hxy, hx'y⟩

/-- ✱164·411. \(\vdash :S^{;}Q \in \text{Rel}^{2}\text{excl}.S\upharpoonright CʻQ \in 1 \rightarrow 1.\text{Hp}*164·4.\supset .\dot{s} ʻRʻʻCʻQ \in \text{Cls} \rightarrow 1\)

"Hp ✱164·4" is the hypothesis of ✱164·4. -/
theorem pm164_411 {α β : Type*} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    {S : (α → α → Prop) → (β → β → Prop) → Prop} {R : (α → β → Prop) → (β → β → Prop) → Prop} :
    (S ⁏ Q ∈ Rel2excl ∧ S ↾ fld Q ∈ arrow one one) ∧
        (∀ N, N ∈ fld Q → Desc R N (fun T => Desc S N (fun M => T ∈ smorbar M N))) →
      sumRel (R ʻʻ fld Q) ∈ arrow Cls one := by
  rintro ⟨⟨hSQ, hS1⟩, h⟩
  rw [excl_iff'] at hSQ
  rw [oneone_iff] at hS1
  have hdesc : ∀ K, K ∈ fld Q → ∃ M₀, S M₀ K := fun K hK => by
    obtain ⟨-, -, M₀, hM₀, -⟩ := h K hK; exact ⟨M₀, (hM₀ M₀).2 rfl⟩
  have hMf : ∀ N₀ M₀, N₀ ∈ fld Q → S M₀ N₀ → M₀ ∈ fld (S ⁏ Q) := by
    intro N₀ M₀ hN₀ hS₀
    obtain ⟨K, hK | hK⟩ := hN₀
    · obtain ⟨M₁, hM₁⟩ := hdesc K (mem_fld_r hK)
      exact mem_fld_l ((semi_iff' S Q M₀ M₁).2 ⟨N₀, K, hS₀, hM₁, hK⟩)
    · obtain ⟨M₁, hM₁⟩ := hdesc K (mem_fld_l hK)
      exact mem_fld_r ((semi_iff' S Q M₁ M₀).2 ⟨K, N₀, hM₁, hS₀, hK⟩)
  rw [mem_arrow_Cls_one]
  rintro x y z ⟨⟨T, ⟨N, hN, hTN⟩, hxy⟩, ⟨T', ⟨N', hN', hTN'⟩, hxz⟩⟩
  obtain ⟨T₀, hT₀, M, hM, hTM⟩ := h N hN
  obtain ⟨T₁, hT₁, M', hM', hTM'⟩ := h N' hN'
  rw [(hT₀ T).1 hTN] at hxy
  rw [(hT₁ T').1 hTN'] at hxz
  have hxM : x ∈ fld M := by rw [← dom_of_smorbar hTM]; exact ⟨y, hxy⟩
  have hxM' : x ∈ fld M' := by rw [← dom_of_smorbar hTM']; exact ⟨z, hxz⟩
  have eM : M = M' := hSQ M M' (hMf N M hN ((hM M).2 rfl)) (hMf N' M' hN' ((hM' M').2 rfl)) x
    hxM hxM'
  have eN : N = N' := hS1.2 M N N' ⟨⟨(hM M).2 rfl, hN⟩, ⟨by rw [eM]; exact (hM' M').2 rfl, hN'⟩⟩
  rw [← eN] at hT₁
  have : T₁ = T₀ := (hT₀ T₁).1 ((hT₁ T₁).2 rfl)
  rw [this] at hxz
  exact (oneone_iff.1 hTM.1.1).2 x y z ⟨hxy, hxz⟩

/-- ✱164·412. \[\begin{align}\vdash \colon\ldotp S^{;}Q,&Q \in \text{Rel}^{2}\text{excl}.S\upharpoonright CʻQ \in 1 \rightarrow 1:\\ &N \in CʻQ.\supset _N.RʻN \in (SʻN)\,\overline{\text{smor}}\, N:\supset .\dot{s} ʻRʻʻCʻQ \in 1 \rightarrow 1\\ &[*164·41·411]\end{align}\] -/
theorem pm164_412 {α β : Type*} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    {S : (α → α → Prop) → (β → β → Prop) → Prop} {R : (α → β → Prop) → (β → β → Prop) → Prop} :
    ((S ⁏ Q ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ S ↾ fld Q ∈ arrow one one) ∧
        (∀ N, N ∈ fld Q → Desc R N (fun T => Desc S N (fun M => T ∈ smorbar M N))) →
      sumRel (R ʻʻ fld Q) ∈ arrow one one := by
  rintro ⟨⟨⟨hSQ, hQ⟩, hS1⟩, h⟩
  exact mem_arrow_one_one.2 ⟨mem_arrow_one_Cls.1 (pm164_41 ⟨hQ, h⟩),
    mem_arrow_Cls_one.1 (pm164_411 ⟨⟨hSQ, hS1⟩, h⟩)⟩

/-- ✱164·413. \[\begin{align}\vdash \colon\ldotp \text{Hp}&*164·41.\supset :\\ &N \in CʻQ.\supset .RʻN = (\dot{s} ʻRʻʻCʻQ)\upharpoonright CʻN.SʻN = (\dot{s} ʻRʻʻCʻQ)^{;}N\end{align}\]

"Hp ✱164·41" is the hypothesis of ✱164·41; `N` is a real variable. -/
theorem pm164_413 {α β : Type*} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    {S : (α → α → Prop) → (β → β → Prop) → Prop} {R : (α → β → Prop) → (β → β → Prop) → Prop}
    {N : β → β → Prop} :
    Q ∈ Rel2excl ∧ (∀ N', N' ∈ fld Q → Desc R N' (fun T => Desc S N' (fun M => T ∈ smorbar M N'))) →
      (N ∈ fld Q →
        Desc R N (fun T => T = sumRel (R ʻʻ fld Q) ↾ fld N) ∧
          Desc S N (fun M => M = sumRel (R ʻʻ fld Q) ⁏ N)) := by
  rintro ⟨hQ, h⟩ hN
  rw [excl_iff'] at hQ
  obtain ⟨T, hT, M, hM, hTM⟩ := h N hN
  have key : sumRel (R ʻʻ fld Q) ↾ fld N = T := by
    refine rel_ext' fun x y => ⟨?_, fun hxy => ⟨⟨T, ⟨N, hN, (hT T).2 rfl⟩, hxy⟩,
      by rw [hTM.1.2]; exact ⟨x, hxy⟩⟩⟩
    rintro ⟨⟨T', ⟨N', hN', hTN'⟩, hxy⟩, hy⟩
    obtain ⟨T₁, hT₁, M', -, hTM'⟩ := h N' hN'
    have e1 : T' = T₁ := (hT₁ T').1 hTN'
    rw [e1] at hxy
    have hyN' : y ∈ fld N' := by rw [hTM'.1.2]; exact ⟨x, hxy⟩
    have e : N' = N := hQ N' N hN' hN y hyN' hy
    rw [e] at hT₁
    have : T₁ = T := (hT T₁).1 ((hT₁ T₁).2 rfl)
    rw [this] at hxy
    exact hxy
  refine ⟨(TheIs_iff_of_unique hT).2 key.symm, (TheIs_iff_of_unique hM).2 ?_⟩
  rw [hTM.2, ← key, cres_semi_of Set.Subset.rfl]

/-- ✱164·414. \(\vdash :\text{Hp}*164·41.\supset .S^{;}Q = (\dot{s} ʻRʻʻCʻQ)\dagger ^{;}Q \quad[*164·413.*150·1·35]\) -/
theorem pm164_414 {α β : Type*} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    {S : (α → α → Prop) → (β → β → Prop) → Prop} {R : (α → β → Prop) → (β → β → Prop) → Prop} :
    Q ∈ Rel2excl ∧ (∀ N, N ∈ fld Q → Desc R N (fun T => Desc S N (fun M => T ∈ smorbar M N))) →
      S ⁏ Q = daggerRel (sumRel (R ʻʻ fld Q)) ⁏ Q := by
  rintro ⟨hQ, h⟩
  have hS : ∀ N, N ∈ fld Q → ∀ M, S M N ↔ M = sumRel (R ʻʻ fld Q) ⁏ N := fun N hN M => by
    obtain ⟨M₀, hM₀, e⟩ := (pm164_413 ⟨hQ, h⟩ hN).2
    rw [← e]
    exact hM₀ M
  refine rel_ext' fun X Y => ?_
  rw [semi_iff', semi_dagger_apply]
  constructor
  · rintro ⟨N, N', hX, hY, hNN'⟩
    exact ⟨N, N', ⟨(hS N (mem_fld_l hNN') X).1 hX, (hS N' (mem_fld_r hNN') Y).1 hY⟩, hNN'⟩
  · rintro ⟨N, N', ⟨hX, hY⟩, hNN'⟩
    exact ⟨N, N', (hS N (mem_fld_l hNN') X).2 hX, (hS N' (mem_fld_r hNN') Y).2 hY, hNN'⟩

/-- ✱164·42. \[\begin{align}\vdash \colon\ldotp Q,S^{;}Q \in &\text{Rel}^{2}\text{excl}.S \upharpoonright CʻQ \in 1 \rightarrow 1:\\ &N \in CʻQ.\supset _N.RʻN \in (SʻN)\,\overline{\text{smor}}\,N:\supset .\\ &\dot{s} ʻRʻʻCʻQ \in (S^{;}Q) \,\overline{\text{smor}}\,\overline{\text{smor}}\, Q \quad[*164·4·412·414·1]\end{align}\] -/
theorem pm164_42 {α β : Type*} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    {S : (α → α → Prop) → (β → β → Prop) → Prop} {R : (α → β → Prop) → (β → β → Prop) → Prop} :
    ((Q ∈ Rel2excl ∧ S ⁏ Q ∈ Rel2excl) ∧ S ↾ fld Q ∈ arrow one one) ∧
        (∀ N, N ∈ fld Q → Desc R N (fun T => Desc S N (fun M => T ∈ smorbar M N))) →
      sumRel (R ʻʻ fld Q) ∈ smorsmorbar (S ⁏ Q) Q := by
  rintro ⟨⟨⟨hQ, hSQ⟩, hS1⟩, h⟩
  exact smorsmorbar_iff.2 ⟨⟨pm164_412 ⟨⟨⟨hSQ, hQ⟩, hS1⟩, h⟩, pm164_4 h⟩, pm164_414 ⟨hQ, h⟩⟩

/-- ✱164·421. \[\begin{align}\vdash \colon\ldotp P,Q \in &\text{Rel}^{2}\text{excl}.S \upharpoonright CʻQ \in P\,\overline{\text{smor}}\,Q:\\ &N \in CʻQ.\supset _N.RʻN \in (SʻN)\,\overline{\text{smor}}\,N:\supset .\\ &\dot{s} ʻRʻʻCʻQ \in P \,\overline{\text{smor}}\,\overline{\text{smor}}\, Q \quad[*164·42]\end{align}\] -/
theorem pm164_421 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    {S : (α → α → Prop) → (β → β → Prop) → Prop} {R : (α → β → Prop) → (β → β → Prop) → Prop} :
    ((P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ S ↾ fld Q ∈ smorbar P Q) ∧
        (∀ N, N ∈ fld Q → Desc R N (fun T => Desc S N (fun M => T ∈ smorbar M N))) →
      sumRel (R ʻʻ fld Q) ∈ smorsmorbar P Q := by
  rintro ⟨⟨⟨hP, hQ⟩, hS⟩, h⟩
  obtain ⟨⟨o, -⟩, e⟩ := hS
  rw [cres_semi_of Set.Subset.rfl] at e
  rw [e]
  exact pm164_42 ⟨⟨⟨hQ, by rw [← e]; exact hP⟩, o⟩, h⟩

/-- ✱164·43. \[\begin{align}\vdash \colon\ldotp P,Q\in &\text{Rel}^{2}\text{excl}.S\in P\,\overline{\text{smor}}\,Q.\\ &\mu =\hat{\lambda}\{(\exists N).N\in CʻQ.\lambda =(SʻN)\,\overline{\text{smor}}\,N\}.\supset :\\ &R\in {\in}_{\Delta}ʻ\mu .\supset .\dot{s} ʻ\text{D}ʻR\in P\,\overline{\text{smor}} \,\overline{\text{smor}}\, Q.S=(\dot{s} ʻ\text{D}ʻR)]\dagger \upharpoonright CʻQ\end{align}\]

`(S'N) smor̄ N` keeps its description: `Desc S N (fun M => λ = smorbar M N)`; `∈_Δ'μ` is
`sel memRel μ`; the conclusion is the product of the two `⊃`-consequents.

**Status.** proved (reading): transcription error: the e-text prints a stray `]` in
`S = (ṡ'D'R)]† ↾ C'Q`; read `S = (ṡ'D'R)† ↾ C'Q`. -/
theorem pm164_43 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : (α → α → Prop) → (β → β → Prop) → Prop}
    {μ : Set (Set (α → β → Prop))} {R : (α → β → Prop) → Set (α → β → Prop) → Prop} :
    ((P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ S ∈ smorbar P Q) ∧
        μ = {L | ∃ N, N ∈ fld Q ∧ Desc S N (fun M => L = smorbar M N)} →
      (R ∈ sel memRel μ →
        sumRel (dom R) ∈ smorsmorbar P Q ∧ S = daggerRel (sumRel (dom R)) ↾ fld Q) := by
  rintro ⟨⟨⟨hP, hQ⟩, hS⟩, rfl⟩ hR
  obtain ⟨⟨oS, cS⟩, eS⟩ := hS
  obtain ⟨⟨hR1, hRm⟩, hRc⟩ := mem_sel_iff.1 hR
  have hSN : ∀ N, N ∈ fld Q → ∃ M, ∀ M', S M' N ↔ M' = M := fun N hN => by
    rw [cS] at hN
    obtain ⟨M, hM⟩ := hN
    exact ⟨M, fun M' => ⟨fun h => (oneone_iff.1 oS).1 M' M N ⟨h, hM⟩, fun e => e ▸ hM⟩⟩
  let R' : (α → β → Prop) → (β → β → Prop) → Prop := fun T N =>
    N ∈ fld Q ∧ ∃ M, S M N ∧ R T (smorbar M N)
  have hR' : ∀ N, N ∈ fld Q → Desc R' N (fun T => Desc S N (fun M => T ∈ smorbar M N)) := by
    intro N hN
    obtain ⟨M, hM⟩ := hSN N hN
    have hL : smorbar M N ∈ codom R := by
      rw [hRc]; exact ⟨N, hN, (TheIs_iff_of_unique hM).2 rfl⟩
    obtain ⟨T, hT⟩ := hL
    have huniq : ∀ T', R' T' N ↔ T' = T := by
      intro T'
      constructor
      · rintro ⟨-, M', hM', hT'⟩
        rw [(hM M').1 hM'] at hT'
        exact mem_arrow_one_Cls.1 hR1 T' T _ ⟨hT', hT⟩
      · intro e
        rw [e]
        exact ⟨hN, M, (hM M).2 rfl, hT⟩
    exact (TheIs_iff_of_unique huniq).2 ((TheIs_iff_of_unique hM).2 (hRm _ _ hT))
  have hdom : R' ʻʻ fld Q = dom R := by
    ext T
    constructor
    · rintro ⟨N, -, -, M, -, hT⟩; exact ⟨_, hT⟩
    · rintro ⟨L, hT⟩
      have : L ∈ codom R := ⟨T, hT⟩
      rw [hRc] at this
      obtain ⟨N, hN, hL⟩ := this
      obtain ⟨M, hM⟩ := hSN N hN
      have hL' : L = smorbar M N := (TheIs_iff_of_unique hM).1 hL
      exact ⟨N, hN, hN, M, (hM M).2 rfl, by rw [← hL']; exact hT⟩
  have hS' : S ↾ fld Q ∈ smorbar P Q := by
    have e : S ↾ fld Q = S :=
      rel_ext' fun M N => ⟨fun h => h.1, fun h => ⟨h, by rw [cS]; exact ⟨M, h⟩⟩⟩
    rw [e]; exact ⟨⟨oS, cS⟩, eS⟩
  have main := pm164_421 (R := R') ⟨⟨⟨hP, hQ⟩, hS'⟩, hR'⟩
  rw [hdom] at main
  refine ⟨main, rel_ext' fun M N => ?_⟩
  constructor
  · intro hMN
    have hN : N ∈ fld Q := by rw [cS]; exact ⟨M, hMN⟩
    refine ⟨?_, hN⟩
    obtain ⟨M₀, hM₀, e⟩ := (pm164_413 (R := R') ⟨hQ, hR'⟩ hN).2
    rw [hdom] at e
    show M = sumRel (dom R) ⁏ N
    rw [(hM₀ M).1 hMN, e]
  · rintro ⟨hMN, hN⟩
    obtain ⟨M₀, hM₀, e⟩ := (pm164_413 (R := R') ⟨hQ, hR'⟩ hN).2
    rw [hdom] at e
    have hMN' : M = sumRel (dom R) ⁏ N := hMN
    rw [hMN', ← e]
    exact (hM₀ M₀).2 rfl

/-- ✱164·431. \[\begin{align}\vdash \colon\ldotp &P,Q\in \text{Rel}^{2}\text{excl}:(\exists S).S\in P\,\overline{\text{smor}}\,Q.\\ &\exists !{\in}_{\Delta}ʻ\hat{\lambda}\{(\exists N).N\in CʻQ.\lambda =(SʻN)\,\overline{\text{smor}}\,N\}:\supset .P \,\text{smor} \text{smor} Q\\ &[*163·43·11]\end{align}\]

The colon makes `(∃S) . S ∈ P smor̄ Q . ∃!∈_Δ'λ̂{…}` one factor (Group II dots). -/
theorem pm164_431 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    (P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧
        (∃ S : (α → α → Prop) → (β → β → Prop) → Prop, S ∈ smorbar P Q ∧
          (sel memRel {L : Set (α → β → Prop) |
            ∃ N, N ∈ fld Q ∧ Desc S N (fun M => L = smorbar M N)}).Nonempty) →
      smorsmor P Q := by
  rintro ⟨hPQ, S, hS, ⟨R, hR⟩⟩
  exact ⟨_, (pm164_43 ⟨⟨hPQ, hS⟩, rfl⟩ hR).1⟩

/-- ✱164·432. \[\begin{align}\vdash :S\in P\,\overline{\text{smor}}\,Q\cap \text{Rl}ʻ&\text{smor}.\supset .\\ &\Lambda {\sim}\in \hat{\lambda} \{(\exists N).N\in CʻQ.\lambda =(SʻN)\overline{\text{smor}} N\}\end{align}\] -/
theorem pm164_432 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : (α → α → Prop) → (β → β → Prop) → Prop} :
    S ∈ smorbar P Q ∩ rl smor →
      (Λ : Set (α → β → Prop)) ∉
        {L : Set (α → β → Prop) | ∃ N, N ∈ fld Q ∧ Desc S N (fun M => L = smorbar M N)} := by
  rintro ⟨⟨⟨oS, cS⟩, -⟩, hsm⟩ ⟨N, hN, hL⟩
  rw [cS] at hN
  obtain ⟨M, hM⟩ := hN
  have huniq : ∀ M', S M' N ↔ M' = M := fun M' =>
    ⟨fun h => (oneone_iff.1 oS).1 M' M N ⟨h, hM⟩, fun e => e ▸ hM⟩
  have hL' : Λ = smorbar M N := (TheIs_iff_of_unique huniq).1 hL
  obtain ⟨T, hT⟩ := hsm M N hM
  rw [← hL', Null_eq_empty] at hT
  simp at hT

/-- ✱164·433. \[\begin{align}\vdash \colon\ldotp \text{Mult ax}.\supset :S\in &P\,\overline{\text{smor}}\,Q\cap \text{Rl}ʻ\text{smor}.\supset .\\ &\exists !{\in}_{\Delta}ʻ\hat{\lambda} \{(\exists N).N\in CʻQ.\lambda =(SʻN)\overline{\text{smor}} N\}\\ &[*164·432.*88·37]\end{align}\]

`Mult ax` is at the type of the correlators `α → β → Prop` whose classes are selected (✱88·37). -/
theorem pm164_433 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : (α → α → Prop) → (β → β → Prop) → Prop} :
    MultAx (α → β → Prop) →
      (S ∈ smorbar P Q ∩ rl smor →
        (sel memRel {L : Set (α → β → Prop) |
          ∃ N, N ∈ fld Q ∧ Desc S N (fun M => L = smorbar M N)}).Nonempty) := by
  intro _ h
  apply sel_memRel_nonempty'
  intro L hL
  rw [Set.nonempty_iff_ne_empty]
  intro e
  apply pm164_432 h
  rw [Null_eq_empty, ← e]
  exact hL

/-- ✱164·44. \[\begin{align}\vdash \colon\ldotp \text{Mult ax}.\supset :P,Q\in \text{Rel}^{2}\text{excl}.\exists !&P\,\overline{\text{smor}}\,Q\cap \text{Rl}ʻ\text{smor}.\supset .\\ &P \,\text{smor smor}\,Q \quad[*164·433·431]\end{align}\] -/
theorem pm164_44 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    MultAx (α → β → Prop) →
      ((P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ (smorbar P Q ∩ rl smor).Nonempty → smorsmor P Q) := by
  rintro hM ⟨hPQ, ⟨S, hS⟩⟩
  exact pm164_431 ⟨hPQ, S, hS.1, pm164_433 hM hS⟩

/-- ✱164·45. \[\begin{align}\vdash \colon\colon &\text{Mult ax}.\supset \colon\ldotp P,Q\in \text{Rel}^{2}\text{excl}.\supset :\\ &\exists !P\,\overline{\text{smor}}\,Q\cap \text{Rl}ʻ\text{smor}.\equiv .P \,\text{smor smor}\,Q \quad[*164·44·17]\end{align}\] -/
theorem pm164_45 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    MultAx (α → β → Prop) →
      ((P ∈ Rel2excl ∧ Q ∈ Rel2excl) →
        ((smorbar P Q ∩ rl smor).Nonempty ↔ smorsmor P Q)) := fun hM hPQ =>
  ⟨fun h => pm164_44 hM ⟨hPQ, h⟩, pm164_17⟩

/-- ✱164·46. \[\begin{align}\vdash \colon\ldotp \text{Mult ax}.\supset :P,Q\in \text{Rel}^{2}\text{excl}.\exists !&P\,\overline{\text{smor}}\,Q\cap \text{Rl}ʻ\text{smor}.\supset .\\ &\Sigma ʻP\text{smor}\Sigma ʻQ \quad[*164·44·151]\end{align}\] -/
theorem pm164_46 {α β : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    MultAx (α → β → Prop) →
      ((P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ (smorbar P Q ∩ rl smor).Nonempty →
        smor (relSigma P) (relSigma Q)) := fun hM h =>
  (pm164_151 (pm164_44 hM h)).1

/-- ✱164·47. \(\vdash : R, S \in \text{Nr}ʻQ . CʻR, CʻS \in \text{Cl}ʻ\text{Nr}ʻP . \supset . \exists ! R \overline{\text{smor}} S \cap \text{Rl}ʻ\text{smor}\)

`R, S ∈ Nr'Q` is `R ∈ Nr'Q . S ∈ Nr'Q` (✱20·04); as for `μ, ν ∈ NR` (Defs/Part4, decision 2)
it does not identify the types of `R` and `S`, so each `Nr'Q` (and each `Nr'P` of
`C'R, C'S ∈ Cl'Nr'P`) is taken in the type of the relations it is said to contain:
`R ∈ nr (α → α → Prop) Q`, `S ∈ nr (β → β → Prop) Q`, `fld R ∈ cl (nr α P)`,
`fld S ∈ cl (nr β P)`. -/
theorem pm164_47 {α β δ ε : Type*} {Q : δ → δ → Prop} {P : ε → ε → Prop}
    {R : (α → α → Prop) → (α → α → Prop) → Prop} {S : (β → β → Prop) → (β → β → Prop) → Prop} :
    (R ∈ nr (α → α → Prop) Q ∧ S ∈ nr (β → β → Prop) Q) ∧
        (fld R ∈ cl (nr α P) ∧ fld S ∈ cl (nr β P)) →
      (smorbar R S ∩ rl smor).Nonempty := by
  rintro ⟨⟨hR, hS⟩, ⟨hRP, hSP⟩⟩
  obtain ⟨T, hT⟩ := smor_trans (mem_nr.1 hR) (smor_symm (mem_nr.1 hS))
  refine ⟨T, hT, fun M N hMN => ?_⟩
  have hM : M ∈ fld R := by rw [← dom_of_smorbar hT]; exact ⟨N, hMN⟩
  have hN : N ∈ fld S := by rw [hT.1.2]; exact ⟨M, hMN⟩
  exact smor_trans (mem_nr.1 (hRP hM)) (smor_symm (mem_nr.1 (hSP hN)))

/-- ✱164·48. \[\begin{align}\vdash \colon\ldotp \text{Mult ax} . \supset : R, S &\in \text{Rel}^{2}\text{excl} \cap \text{Nr}ʻQ . CʻR, CʻS \in \text{Cl}ʻ\text{Nr}ʻP . \supset .\\ &R\, \text{smor smor}\, S . \Sigma ʻR \,\text{smor}\, \Sigma ʻS \quad[*164·47·44·46]\end{align}\]

The types of `R` and `S` are not identified (see ✱164·47); `Mult ax` is at the type
`α → β → Prop` of the double correlators (✱164·44). -/
theorem pm164_48 {α β δ ε : Type*} {Q : δ → δ → Prop} {P : ε → ε → Prop}
    {R : (α → α → Prop) → (α → α → Prop) → Prop} {S : (β → β → Prop) → (β → β → Prop) → Prop} :
    MultAx (α → β → Prop) →
      ((R ∈ Rel2excl ∩ nr (α → α → Prop) Q ∧ S ∈ Rel2excl ∩ nr (β → β → Prop) Q) ∧
          (fld R ∈ cl (nr α P) ∧ fld S ∈ cl (nr β P)) →
        smorsmor R S ∧ smor (relSigma R) (relSigma S)) := by
  rintro hM ⟨⟨⟨hRe, hR⟩, ⟨hSe, hS⟩⟩, hC⟩
  have h47 := pm164_47 ⟨⟨hR, hS⟩, hC⟩
  exact ⟨pm164_44 hM ⟨⟨hRe, hSe⟩, h47⟩, pm164_46 hM ⟨⟨hRe, hSe⟩, h47⟩⟩

/-!
## [✱165] Relations of relations of couples

*(Vol. 2, p. 386)*

> *Summary of* *165.
>
> …

**Lean reading.** For `P : α → α → Prop` and `z : β`, `P ↓., z` is `opSemi couple P z`
(`= ↓z;P`, ✱150·03, where `↓z` is `coupleR z`) and the relation `P↓.,` is `coupleSemi P`, so
`P↓.,;Q` is `coupleSemi P ⁏ Q` and `P↓.,''β` is `coupleSemi P ʻʻ B`; `(C'P)↓,,z` is
`opImg couple (fld P) z` and the relation `(C'P)↓,,` is `coupleImg (fld P)` (✱113); `C'Q × C'P`
is `fld Q ×ₐ fld P`; `(C'P ↑ ι'z)_Δ'ι'z` is `sel (cross (fld P) (ι z)) (ι z)` and `_Δ''` is an
image under `selRel`; `R|` and `|S̆` are `relProdL R` and `relProdR S˘` (✱38), `R ‖ S̆` is
`R ∥ S˘` (✱43·01), `E!!R''C'P` is `EE R (fld P)`. `↓z'R'y` (✱165·3) and `↓(S'z)` (✱165·32·321)
keep the descriptions `R'y`, `S'z` (`Desc`), scope the equation in which they occur. `Nr'P` and
`Nr'Q` are taken in the types of the relations claimed to be like `P` and `Q`. `Mult ax` (✱165·38)
is at the type of the correlators `γ → (α → β → Prop) → Prop`. In ✱165·245 the e-text prints
`Λ̇ ∼∈ (C'P)↓,,''C'Q`, where only the null *class* is significant (the members of `(C'P)↓,,''C'Q`
are classes of couples): read `Λ`.

**Status.** proved (all propositions; ✱165·245 proved (reading), see its docstring)
-/

/-- ✱165·01. \(\vdash .P\downarrow_{.,} z=\downarrow z^{;}P \quad[*150·6]\) -/
theorem pm165_01 {α β : Type*} {P : α → α → Prop} {z : β} :
    opSemi couple P z = coupleR z ⁏ P := rfl

/-- ✱165·1. \(\vdash :R(P\downarrow_{.,} ^{;}Q)S.\equiv .(\exists z,w).zQw.R=\downarrow z^{;}P.S=\downarrow w^{;}P \quad[*150·62]\) -/
theorem pm165_1 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop}
    {R S : (α → β → Prop) → (α → β → Prop) → Prop} :
    (coupleSemi P ⁏ Q) R S ↔ ∃ z w, (Q z w ∧ R = coupleR z ⁏ P) ∧ S = coupleR w ⁏ P := by
  rw [coupleSemi_semi_apply]
  constructor
  · rintro ⟨z, w, ⟨h1, h2⟩, h3⟩; exact ⟨z, w, ⟨h3, h1⟩, h2⟩
  · rintro ⟨z, w, ⟨h3, h1⟩, h2⟩; exact ⟨z, w, ⟨h1, h2⟩, h3⟩

/-- ✱165·11. \(\vdash :X(\downarrow z^{;}P)Y.\equiv .(\exists x,y).xPy.X=x\downarrow z.Y=y\downarrow z \quad [*150·55]\) -/
theorem pm165_11 {α β : Type*} {P : α → α → Prop} {z : β} {X Y : α → β → Prop} :
    (coupleR z ⁏ P) X Y ↔ ∃ x y, (P x y ∧ X = x ↓ z) ∧ Y = y ↓ z := by
  rw [← pm165_01, opSemi_couple_apply]
  constructor
  · rintro ⟨x, y, ⟨h1, h2⟩, h3⟩; exact ⟨x, y, ⟨h3, h1⟩, h2⟩
  · rintro ⟨x, y, ⟨h3, h1⟩, h2⟩; exact ⟨x, y, ⟨h1, h2⟩, h3⟩

/-- ✱165·12. \(\vdash .CʻP\downarrow_{.,} ^{;}Q=P\downarrow_{.,} ʻʻCʻQ \quad[*150·22]\) -/
theorem pm165_12 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    fld (coupleSemi P ⁏ Q) = coupleSemi P ʻʻ fld Q :=
  fld_semi_graph _ _

/-- ✱165·13. \(\vdash .CʻP\downarrow_{.,} z=\downarrow zʻʻCʻP=(CʻP)\downarrow_{,,} z \quad[*165·01.*150·22.*38·2]\)

The chain is the conjunction of its links. -/
theorem pm165_13 {α β : Type*} {P : α → α → Prop} {z : β} :
    fld (opSemi couple P z) = coupleR z ʻʻ fld P ∧ coupleR z ʻʻ fld P = opImg couple (fld P) z :=
  ⟨fld_semi_graph _ _, rfl⟩

/-- ✱165·131. \(\vdash .CʻʻP\downarrow_{.,} ʻʻ\beta =(CʻP)\downarrow_{,,}ʻʻ\beta \quad[*165·13.*38·11.*37·68]\)

`C''P↓.,''β` is `C''(P↓.,''β)`. -/
theorem pm165_131 {α β : Type*} {P : α → α → Prop} {B : Set β} :
    C ʻʻ coupleSemi P ʻʻ B = coupleImg (fld P) ʻʻ B := by
  ext K
  constructor
  · rintro ⟨R, ⟨y, hy, hR⟩, hK⟩
    have hR' : R = opSemi couple P y := hR
    have hK' : K = fld R := hK
    refine ⟨y, hy, ?_⟩
    show K = opImg couple (fld P) y
    rw [hK', hR', pm165_13.1, pm165_13.2]
  · rintro ⟨y, hy, hK⟩
    have hK' : K = opImg couple (fld P) y := hK
    refine ⟨opSemi couple P y, ⟨y, hy, rfl⟩, ?_⟩
    show K = fld (opSemi couple P y)
    rw [hK', pm165_13.1, pm165_13.2]

/-- ✱165·14. \(\vdash .CʻʻCʻP\downarrow_{.,} ^{;}Q=(CʻP)\downarrow_{,,}ʻʻCʻQ \quad[*165·12·131]\) -/
theorem pm165_14 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    C ʻʻ fld (coupleSemi P ⁏ Q) = coupleImg (fld P) ʻʻ fld Q := by
  rw [pm165_12, pm165_131]

/-- ✱165·15. \(\vdash .sʻCʻʻCʻP\downarrow_{.,} ^{;}Q=CʻQ\times CʻP \quad[*165·14.*113·1]\) -/
theorem pm165_15 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    sumCls (C ʻʻ fld (coupleSemi P ⁏ Q)) = fld Q ×ₐ fld P := by
  rw [pm165_14]; rfl

/-- ✱165·16. \(\vdash .Cʻ\Sigma ʻP\downarrow_{.,} ^{;}Q=CʻQ\times CʻP \quad[*165·15.*162·22]\) -/
theorem pm165_16 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    fld (relSigma (coupleSemi P ⁏ Q)) = fld Q ×ₐ fld P := by
  rw [pm162_22, pm165_15]

/-- ✱165·161. \[\begin{align}\vdash :M(F^{;}P\downarrow_{.,} ^{;}Q)&N.\equiv .\\ &(\exists x,y,z,w).x,y\in CʻP.zQw.M=x\downarrow z.N=y\downarrow w\end{align}\]

`x, y ∈ C'P` is the conjunction. -/
theorem pm165_161 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {M N : α → β → Prop} :
    (F ⁏ coupleSemi P ⁏ Q) M N ↔
      ∃ x y z w, (((x ∈ fld P ∧ y ∈ fld P) ∧ Q z w) ∧ M = x ↓ z) ∧ N = y ↓ w := by
  rw [semi_iff']
  constructor
  · rintro ⟨R, S, hM, hN, h⟩
    obtain ⟨z, w, ⟨rfl, rfl⟩, hzw⟩ := (coupleSemi_semi_apply P Q R S).1 h
    have hM' : M ∈ fld (opSemi couple P z) := hM
    have hN' : N ∈ fld (opSemi couple P w) := hN
    rw [fld_opSemi_couple] at hM' hN'
    obtain ⟨x, hx, rfl⟩ := hM'
    obtain ⟨y, hy, rfl⟩ := hN'
    exact ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, rfl⟩, rfl⟩
  · rintro ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, rfl⟩, rfl⟩
    refine ⟨opSemi couple P z, opSemi couple P w, ?_, ?_,
      (coupleSemi_semi_apply P Q _ _).2 ⟨z, w, ⟨rfl, rfl⟩, hzw⟩⟩
    · show x ↓ z ∈ fld (opSemi couple P z)
      rw [fld_opSemi_couple]; exact ⟨x, hx, rfl⟩
    · show y ↓ w ∈ fld (opSemi couple P w)
      rw [fld_opSemi_couple]; exact ⟨y, hy, rfl⟩

/-- ✱165·162. \(\vdash :M(\dot{s} ʻCʻP\downarrow_{.,} ^{;}Q)N.\equiv .(\exists x,y,z).xPy.z\in CʻQ.M=x\downarrow z.N=y\downarrow z\)

`ṡ'C'P↓.,;Q` is `ṡ'C'(P↓.,;Q)`. -/
theorem pm165_162 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {M N : α → β → Prop} :
    sumRel (fld (coupleSemi P ⁏ Q)) M N ↔
      ∃ x y z, ((P x y ∧ z ∈ fld Q) ∧ M = x ↓ z) ∧ N = y ↓ z := by
  rw [pm165_12]
  constructor
  · rintro ⟨R, ⟨z, hz, hR⟩, h⟩
    have hR' : R = opSemi couple P z := hR
    rw [hR', opSemi_couple_apply] at h
    obtain ⟨x, y, ⟨rfl, rfl⟩, hxy⟩ := h
    exact ⟨x, y, z, ⟨⟨hxy, hz⟩, rfl⟩, rfl⟩
  · rintro ⟨x, y, z, ⟨⟨hxy, hz⟩, rfl⟩, rfl⟩
    exact ⟨opSemi couple P z, ⟨z, hz, rfl⟩,
      (opSemi_couple_apply P z _ _).2 ⟨x, y, ⟨rfl, rfl⟩, hxy⟩⟩

/-- ✱165·17. \[\begin{align}\vdash \colon\ldotp &M(\Sigma ʻP\downarrow_{.,} ^{;}Q)N.\equiv :(\exists x,y,z,w):\\ &x,y\in CʻP.z,w\in CʻQ:zQw.\lor.z=w.xPy:M=x\downarrow z.N=y\downarrow w\end{align}\] -/
theorem pm165_17 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {M N : α → β → Prop} :
    relSigma (coupleSemi P ⁏ Q) M N ↔
      ∃ x y z w, (((x ∈ fld P ∧ y ∈ fld P) ∧ (z ∈ fld Q ∧ w ∈ fld Q)) ∧
        (Q z w ∨ z = w ∧ P x y)) ∧ (M = x ↓ z ∧ N = y ↓ w) := by
  rw [show relSigma (coupleSemi P ⁏ Q) = Q ×ᵣ P from rfl, rtimes_apply]
  constructor
  · rintro (⟨z, hz, x, y, ⟨rfl, rfl⟩, hxy⟩ | ⟨z, w, hzw, x, y, ⟨hx, hy⟩, rfl, rfl⟩)
    · exact ⟨x, y, z, z, ⟨⟨⟨mem_fld_l hxy, mem_fld_r hxy⟩, ⟨hz, hz⟩⟩, Or.inr ⟨rfl, hxy⟩⟩, rfl, rfl⟩
    · exact ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, ⟨mem_fld_l hzw, mem_fld_r hzw⟩⟩, Or.inl hzw⟩, rfl, rfl⟩
  · rintro ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, hzw | ⟨e, hxy⟩⟩, rfl, rfl⟩
    · exact Or.inr ⟨z, w, hzw, x, y, ⟨hx, hy⟩, rfl, rfl⟩
    · exact Or.inl ⟨z, hz, x, y, ⟨rfl, by rw [e]⟩, hxy⟩

/-- ✱165·18. \(\vdash .\text{Cnv}ʻP\downarrow_{.,} ^{;}Q=P\downarrow_{.,} ^{;}\breve{Q} \quad[*150·12]\)

`Cnv'P↓.,;Q` is `Cnv'(P↓.,;Q)`. -/
theorem pm165_18 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    (coupleSemi P ⁏ Q)˘ = coupleSemi P ⁏ Q˘ := cnv_semi _ _

/-- ✱165·181. \(\vdash .\text{Cnv}ʻP\downarrow_{.,} z=\breve{P} \downarrow_{.,} z \quad[*165·01.*150·12]\) -/
theorem pm165_181 {α β : Type*} {P : α → α → Prop} {z : β} :
    (opSemi couple P z)˘ = opSemi couple P˘ z := cnv_semi _ _

/-- ✱165·182. \(\vdash .\text{Cnv}^{;}P\downarrow_{.,} ^{;}Q=\breve{P} \downarrow_{.,} ^{;}Q \quad[*165·181.*150·35]\)

`Cnv;P↓.,;Q` is `Cnv;(P↓.,;Q)` (✱150·05). -/
theorem pm165_182 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    Cnv ⁏ coupleSemi P ⁏ Q = coupleSemi P˘ ⁏ Q := by
  rw [Cnv_eq_graph, semi_semi]
  congr 1
  funext X y
  apply propext
  constructor
  · rintro ⟨R, hX, hR⟩
    have hX' : X = R˘ := hX
    have hR' : R = opSemi couple P y := hR
    show X = opSemi couple P˘ y
    rw [hX', hR', pm165_181]
  · intro h
    have h' : X = opSemi couple P˘ y := h
    refine ⟨opSemi couple P y, ?_, rfl⟩
    show X = (opSemi couple P y)˘
    rw [h', pm165_181]

/-- ✱165·19. \(\vdash .\text{Cnv}ʻ\text{Cnv}^{;}P\downarrow_{.,} ^{;}Q=\breve{P} \downarrow_{.,} ^{;}\breve{Q} =\text{Cnv}^{;}\text{Cnv}ʻP\downarrow_{.,} ^{;}Q \quad[*165·18·182]\)

The chain is the conjunction of its links. -/
theorem pm165_19 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    (Cnv ⁏ coupleSemi P ⁏ Q)˘ = coupleSemi P˘ ⁏ Q˘ ∧
      coupleSemi P˘ ⁏ Q˘ = Cnv ⁏ (coupleSemi P ⁏ Q)˘ := by
  constructor
  · rw [pm165_182, cnv_semi]
  · rw [pm165_18, pm165_182]

/-- ✱165·2. \(\vdash .P\downarrow_{.,} \in 1\rightarrow \text{Cls} \quad[*72·14]\) -/
theorem pm165_2 {α β : Type*} {P : α → α → Prop} :
    (coupleSemi P : _ → β → Prop) ∈ arrow one Cls :=
  mem_arrow_one_Cls.2 fun X Y z h =>
    (h.1 : X = opSemi couple P z).trans (h.2 : Y = opSemi couple P z).symm

private theorem sel_cross_unit {α β : Type*} (A : Set α) {B : Set β} {z : β} (hz : z ∈ B) :
    sel (cross A B) (ι z) = {X | ∃ x, x ∈ A ∧ X = x ↓ z} := by
  ext X
  rw [mem_sel_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have : z ∈ codom X := by rw [h3]; exact mem_unitCls.2 rfl
    obtain ⟨x, hx⟩ := this
    refine ⟨x, (h2 _ _ hx).1, rel_ext' fun a b => ⟨fun hab => ?_, fun hab => ?_⟩⟩
    · have hb : b ∈ ι z := by rw [← h3]; exact ⟨a, hab⟩
      rw [mem_unitCls] at hb
      rw [hb] at hab
      exact (couple_apply _ _ _ _).2 ⟨mem_arrow_one_Cls.1 h1 a x z ⟨hab, hx⟩, hb⟩
    · rw [couple_apply] at hab
      rw [hab.1, hab.2]; exact hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨mem_arrow_one_Cls.2 (oneone_iff.1 (couple_oneone x z)).1, fun a b h => ?_⟩,
      codom_couple x z⟩
    rw [couple_apply] at h
    rw [h.1, h.2]; exact ⟨hx, hz⟩

/-- ✱165·201. \(\vdash .Cʻ(P\downarrow_{.,} z)=(CʻP\uparrow \iota ʻz)_{\Delta }ʻ\iota ʻz\)

`(C'P ↑ ι'z)_Δ'ι'z` is `sel (cross (fld P) (ι z)) (ι z)` (✱80·01). -/
theorem pm165_201 {α β : Type*} {P : α → α → Prop} {z : β} :
    fld (opSemi couple P z) = sel (cross (fld P) (ι z)) (ι z) := by
  rw [sel_cross_unit _ (mem_unitCls.2 rfl), fld_opSemi_couple]

/-- ✱165·202. \(\vdash .CʻʻCʻP\downarrow_{.,} ^{;}Q=(CʻP\uparrow CʻQ)_{\Delta }ʻʻ\iotaʻʻCʻQ \quad[*165·14.*113·103]\)

`(C'P ↑ C'Q)_Δ''ι''C'Q` is `selRel (cross (fld P) (fld Q)) ʻʻ iota ʻʻ fld Q`. -/
theorem pm165_202 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    C ʻʻ fld (coupleSemi P ⁏ Q) = selRel (cross (fld P) (fld Q)) ʻʻ iota ʻʻ fld Q := by
  ext K
  constructor
  · rintro ⟨R, hR, hK⟩
    obtain ⟨z, hz, rfl⟩ := mem_fld_coupleSemi_semi.1 hR
    have hK' : K = fld (opSemi couple P z) := hK
    refine ⟨ι z, ⟨z, hz, rfl⟩, ?_⟩
    show K = sel (cross (fld P) (fld Q)) (ι z)
    rw [hK', sel_cross_unit _ hz, fld_opSemi_couple]
  · rintro ⟨A, ⟨z, hz, hA⟩, hK⟩
    have hA' : A = ι z := hA
    have hK' : K = sel (cross (fld P) (fld Q)) A := hK
    refine ⟨opSemi couple P z, mem_fld_coupleSemi_semi.2 ⟨z, hz, rfl⟩, ?_⟩
    show K = fld (opSemi couple P z)
    rw [hK', hA', sel_cross_unit _ hz, fld_opSemi_couple]

/-- ✱165·203. \(\vdash .CʻʻCʻP\downarrow_{.,} ^{;}Q\in \text{Cls}^{2} \text{excl} \quad[*84·55.*165·202]\) -/
theorem pm165_203 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    C ʻʻ fld (coupleSemi P ⁏ Q) ∈ Cls2excl := by
  rintro K K' ⟨⟨⟨R, hR, hK⟩, ⟨R', hR', hK'⟩⟩, hne⟩
  obtain ⟨z, -, rfl⟩ := mem_fld_coupleSemi_semi.1 hR
  obtain ⟨w, -, rfl⟩ := mem_fld_coupleSemi_semi.1 hR'
  have e1 : K = fld (opSemi couple P z) := hK
  have e2 : K' = fld (opSemi couple P w) := hK'
  rw [inter_null_iff]
  rintro ⟨X, hX, hX'⟩
  rw [e1, fld_opSemi_couple] at hX
  rw [e2, fld_opSemi_couple] at hX'
  obtain ⟨x, -, rfl⟩ := hX
  obtain ⟨y, -, e⟩ := hX'
  have : z = w := (couple_eq_couple_iff.1 e).2
  exact hne (by rw [e1, e2, this])

/-- ✱165·204. \(\vdash :CʻP\downarrow_{.,} x=CʻP\downarrow_{.,} y.\equiv .P\downarrow_{.,} x=P\downarrow_{.,} y\) -/
theorem pm165_204 {α β : Type*} {P : α → α → Prop} {x y : β} :
    fld (opSemi couple P x) = fld (opSemi couple P y) ↔ opSemi couple P x = opSemi couple P y := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  by_cases hP : rEx P
  · obtain ⟨a, b, hab⟩ := hP
    have : a ↓ x ∈ fld (opSemi couple P x) := by
      rw [fld_opSemi_couple]; exact ⟨a, mem_fld_l hab, rfl⟩
    rw [h, fld_opSemi_couple] at this
    obtain ⟨c, -, e⟩ := this
    rw [(couple_eq_couple_iff.1 e).2]
  · rw [eq_rNull_of_not_rEx hP, pm165_01, pm165_01, semi_rNull, semi_rNull]

/-- ✱165·205. \(\vdash .C\upharpoonright \text{D}ʻP\downarrow_{.,} \in 1\rightarrow 1 \quad[*165·204.*71·58]\)

`C ↾ D'P↓.,` is `C ↾ dom (coupleSemi P)`. -/
theorem pm165_205 {α β : Type*} {P : α → α → Prop} :
    C ↾ dom (coupleSemi P : _ → β → Prop) ∈ arrow one one := by
  rw [oneone_iff]
  refine ⟨fun A B R h => ?_, fun A R R' h => ?_⟩
  · have h1 : A = fld R := h.1.1
    have h2 : B = fld R := h.2.1
    rw [h1, h2]
  · obtain ⟨⟨h1, ⟨y, hy⟩⟩, ⟨h2, ⟨y', hy'⟩⟩⟩ := h
    have e1 : A = fld R := h1
    have e2 : A = fld R' := h2
    have f1 : R = opSemi couple P y := hy
    have f2 : R' = opSemi couple P y' := hy'
    rw [f1, f2]
    rw [f1] at e1
    rw [f2] at e2
    exact pm165_204.1 (e1.symm.trans e2)

/-- ✱165·206. \(\vdash :(x).\text{E}!P\downarrow_{.,} ʻx:(\alpha ).\alpha \subset \text{ᗡ}ʻP\downarrow_{.,} \quad[*38·12.*33·431]\)

The product of `(x) . E!P↓.,'x` (`EDesc`) and `(α) . α ⊂ ᗡ'P↓.,`. -/
theorem pm165_206 {α β : Type*} {P : α → α → Prop} :
    (∀ x : β, EDesc (coupleSemi P) x) ∧ ∀ A : Set β, A ⊆ codom (coupleSemi P) :=
  ⟨fun x => EDesc_graph _ x, fun _ _ _ => ⟨_, rfl⟩⟩

/-- ✱165·21. \(\vdash .P\downarrow_{.,} ^{;}Q\in \text{Rel}^{2}\text{excl}\) -/
theorem pm165_21 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    coupleSemi P ⁏ Q ∈ Rel2excl := by
  rw [excl_iff']
  intro T T' hT hT' X hX hX'
  obtain ⟨z, -, rfl⟩ := mem_fld_coupleSemi_semi.1 hT
  obtain ⟨w, -, rfl⟩ := mem_fld_coupleSemi_semi.1 hT'
  rw [fld_opSemi_couple] at hX hX'
  obtain ⟨x, -, rfl⟩ := hX
  obtain ⟨y, -, e⟩ := hX'
  rw [(couple_eq_couple_iff.1 e).2]

/-- ✱165·211. \(\vdash :\exists !CʻP\downarrow_{.,} x\cap CʻP\downarrow_{.,} y.\supset .x=y \quad[*165·13.*55·232]\) -/
theorem pm165_211 {α β : Type*} {P : α → α → Prop} {x y : β} :
    (fld (opSemi couple P x) ∩ fld (opSemi couple P y)).Nonempty → x = y := by
  rintro ⟨X, hX, hY⟩
  rw [fld_opSemi_couple] at hX hY
  obtain ⟨a, -, rfl⟩ := hX
  obtain ⟨b, -, e⟩ := hY
  exact (couple_eq_couple_iff.1 e).2

/-- ✱165·212. \(\vdash :\dot{\exists} !P.\equiv .\dot{\exists} !P\downarrow_{.,} x\) -/
theorem pm165_212 {α β : Type*} {P : α → α → Prop} {x : β} : rEx P ↔ rEx (opSemi couple P x) :=
  rEx_opSemi.symm

/-- ✱165·22. \(\vdash :\dot{\exists} !P.\supset .P\downarrow_{.,} \in 1\rightarrow 1\) -/
theorem pm165_22 {α β : Type*} {P : α → α → Prop} :
    rEx P → (coupleSemi P : _ → β → Prop) ∈ arrow one one := by
  intro hP
  refine mem_arrow_one_one.2 ⟨mem_arrow_one_Cls.1 pm165_2, fun R y y' h => ?_⟩
  have h1 : R = opSemi couple P y := h.1
  have h2 : R = opSemi couple P y' := h.2
  exact opSemi_inj hP (h1.symm.trans h2)

/-- ✱165·221. \(\vdash \colon\ldotp \dot{\exists} !P.\supset :\dot{\exists} !P\downarrow_{.,} x\dot{\cap} P\downarrow_{.,} y.\equiv .P\downarrow_{.,} x=P\downarrow_{.,} y.\equiv .x=y\)

`∃̇!(P↓.,x ∩̇ P↓.,y)` is `rEx (opSemi couple P x ⩀ opSemi couple P y)`; the chain is the
conjunction of its links. -/
theorem pm165_221 {α β : Type*} {P : α → α → Prop} {x y : β} :
    rEx P →
      ((rEx (opSemi couple P x ⩀ opSemi couple P y) ↔ opSemi couple P x = opSemi couple P y) ∧
        (opSemi couple P x = opSemi couple P y ↔ x = y)) := by
  intro hP
  have e : opSemi couple P x = opSemi couple P y ↔ x = y :=
    ⟨opSemi_inj hP, fun h => by rw [h]⟩
  refine ⟨⟨fun ⟨X, Y, h1, h2⟩ => ?_, fun h => ?_⟩, e⟩
  · obtain ⟨a, b, ⟨rfl, -⟩, -⟩ := (opSemi_couple_apply P x X Y).1 h1
    obtain ⟨a', b', ⟨e', -⟩, -⟩ := (opSemi_couple_apply P y _ Y).1 h2
    rw [(couple_eq_couple_iff.1 e').2]
  · obtain ⟨X, Y, hXY⟩ := (rEx_opSemi (z := x)).2 hP
    exact ⟨X, Y, hXY, by rw [← h]; exact hXY⟩

/-- ✱165·222. \[\begin{align}&\vdash \colon\ldotp \dot{\exists} !P.\supset :\exists !CʻP\downarrow_{.,} x\cap CʻP\downarrow_{.,} y.\equiv .CʻP \downarrow_{.,} x=CʻP\downarrow_{.,} y.\equiv .x=y\\ &[\text{Proof as in *165·221}]\end{align}\] -/
theorem pm165_222 {α β : Type*} {P : α → α → Prop} {x y : β} :
    rEx P →
      (((fld (opSemi couple P x) ∩ fld (opSemi couple P y)).Nonempty ↔
          fld (opSemi couple P x) = fld (opSemi couple P y)) ∧
        (fld (opSemi couple P x) = fld (opSemi couple P y) ↔ x = y)) := by
  intro hP
  have e : fld (opSemi couple P x) = fld (opSemi couple P y) ↔ x = y :=
    pm165_204.trans ⟨opSemi_inj hP, fun h => by rw [h]⟩
  refine ⟨⟨fun h => e.2 (pm165_211 h), fun h => ?_⟩, e⟩
  obtain ⟨a, b, hab⟩ := hP
  refine ⟨a ↓ x, ?_, ?_⟩
  · rw [fld_opSemi_couple]; exact ⟨a, mem_fld_l hab, rfl⟩
  · rw [← h, fld_opSemi_couple]; exact ⟨a, mem_fld_l hab, rfl⟩

/-- ✱165·223. \(\vdash \colon\ldotp \dot{\exists} !P.\supset :P\downarrow_{.,} ^{;}Q=P\downarrow_{.,} ^{;}R.\equiv .Q=R\) -/
theorem pm165_223 {α β : Type*} {P : α → α → Prop} {Q R : β → β → Prop} :
    rEx P → (coupleSemi P ⁏ Q = coupleSemi P ⁏ R ↔ Q = R) := by
  intro hP
  refine ⟨fun h => rel_ext' fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun h => by rw [h]⟩
  · have : (coupleSemi P ⁏ Q) (opSemi couple P a) (opSemi couple P b) :=
      (coupleSemi_semi_apply P Q _ _).2 ⟨a, b, ⟨rfl, rfl⟩, hab⟩
    rw [h, coupleSemi_semi_apply] at this
    obtain ⟨c, d, ⟨e1, e2⟩, hcd⟩ := this
    rw [opSemi_inj hP e1, opSemi_inj hP e2]; exact hcd
  · have : (coupleSemi P ⁏ R) (opSemi couple P a) (opSemi couple P b) :=
      (coupleSemi_semi_apply P R _ _).2 ⟨a, b, ⟨rfl, rfl⟩, hab⟩
    rw [← h, coupleSemi_semi_apply] at this
    obtain ⟨c, d, ⟨e1, e2⟩, hcd⟩ := this
    rw [opSemi_inj hP e1, opSemi_inj hP e2]; exact hcd

/-- ✱165·23. \(\vdash :P\downarrow_{.,} x=Q\downarrow_{.,} y.\supset .P=Q\) -/
theorem pm165_23 {α β : Type*} {P Q : α → α → Prop} {x y : β} :
    opSemi couple P x = opSemi couple Q y → P = Q := by
  intro h
  refine rel_ext' fun a b => ⟨fun hab => ?_, fun hab => ?_⟩
  · have : opSemi couple P x (a ↓ x) (b ↓ x) := (opSemi_couple_apply P x _ _).2 ⟨a, b, ⟨rfl, rfl⟩, hab⟩
    rw [h, opSemi_couple_apply] at this
    obtain ⟨c, d, ⟨e1, e2⟩, hcd⟩ := this
    rw [(couple_eq_couple_iff.1 e1).1, (couple_eq_couple_iff.1 e2).1]; exact hcd
  · have : opSemi couple Q y (a ↓ y) (b ↓ y) := (opSemi_couple_apply Q y _ _).2 ⟨a, b, ⟨rfl, rfl⟩, hab⟩
    rw [← h, opSemi_couple_apply] at this
    obtain ⟨c, d, ⟨e1, e2⟩, hcd⟩ := this
    rw [(couple_eq_couple_iff.1 e1).1, (couple_eq_couple_iff.1 e2).1]; exact hcd

/-- ✱165·231. \(\vdash :P\downarrow_{.,} x=Q\downarrow_{.,} x.\equiv .P=Q \quad[*165·23.*30·37]\) -/
theorem pm165_231 {α β : Type*} {P Q : α → α → Prop} {x : β} :
    opSemi couple P x = opSemi couple Q x ↔ P = Q :=
  ⟨pm165_23, fun h => by rw [h]⟩

/-- ✱165·232. \(\vdash \colon\ldotp \dot{\exists} !P.\lor.\dot{\exists} !Q:\supset :P\downarrow_{.,} x=Q\downarrow_{.,} y.\equiv .P=Q.x=y\) -/
theorem pm165_232 {α β : Type*} {P Q : α → α → Prop} {x y : β} :
    rEx P ∨ rEx Q → (opSemi couple P x = opSemi couple Q y ↔ P = Q ∧ x = y) := by
  intro h
  refine ⟨fun e => ⟨pm165_23 e, ?_⟩, fun ⟨e1, e2⟩ => by rw [e1, e2]⟩
  have hPQ := pm165_23 e
  rw [← hPQ] at e
  rcases h with hP | hQ
  · exact opSemi_inj hP e
  · rw [← hPQ] at hQ; exact opSemi_inj hQ e

/-- ✱165·233. \[\begin{align}&\vdash :\exists !CʻP\downarrow_{.,} x\cap CʻQ\downarrow_{.,} y.\equiv .x=y.\exists !CʻP\cap CʻQ\\ &[*55·232.*165·13]\end{align}\] -/
theorem pm165_233 {α β : Type*} {P Q : α → α → Prop} {x y : β} :
    (fld (opSemi couple P x) ∩ fld (opSemi couple Q y)).Nonempty ↔
      x = y ∧ (fld P ∩ fld Q).Nonempty := by
  rw [fld_opSemi_couple, fld_opSemi_couple]
  constructor
  · rintro ⟨X, ⟨a, ha, rfl⟩, ⟨b, hb, e⟩⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    exact ⟨rfl, a, ha, hb⟩
  · rintro ⟨rfl, a, ha, hb⟩
    exact ⟨a ↓ x, ⟨a, ha, rfl⟩, ⟨a, hb, rfl⟩⟩

/-- ✱165·24. \(\vdash :P=\dot{\Lambda} .\supset .P\downarrow_{.,} x=\dot{\Lambda} .P\downarrow_{.,} =\iota ʻ\dot{\Lambda} \uparrow \text{V}\)

`P↓., = ι'Λ̇ ↑ V` with `V` of the type of the relata. -/
theorem pm165_24 {α β : Type*} {P : α → α → Prop} {x : β} :
    P = rNull → opSemi couple P x = rNull ∧ (coupleSemi P : _ → β → Prop) = cross (ι rNull) V := by
  intro h
  have e : ∀ y : β, opSemi couple P y = rNull := fun y => by rw [h, pm165_01, semi_rNull]
  refine ⟨e x, rel_ext' fun R y => ?_⟩
  show R = opSemi couple P y ↔ R ∈ ι rNull ∧ y ∈ V
  rw [e y, mem_unitCls, V_eq_univ]
  exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩

/-- ✱165·241. \(\vdash :Q=\dot{\Lambda} .\supset .P\downarrow_{.,} ^{;}Q=\dot{\Lambda} \quad[*150·42]\) -/
theorem pm165_241 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    Q = rNull → coupleSemi P ⁏ Q = rNull := by
  intro h; rw [h, semi_rNull]

/-- ✱165·242. \(\vdash :P=\dot{\Lambda} .\dot{\exists} !Q.\supset .P\downarrow_{.,} ^{;}Q=\dot{\Lambda} \downarrow \dot{\Lambda}\) -/
theorem pm165_242 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    P = rNull ∧ rEx Q → coupleSemi P ⁏ Q = rNull ↓ rNull := by
  rintro ⟨hP, ⟨a, b, hab⟩⟩
  have e : ∀ y : β, opSemi couple P y = rNull := fun y => by rw [hP, pm165_01, semi_rNull]
  refine rel_ext' fun R S => ?_
  rw [coupleSemi_semi_apply, couple_apply]
  constructor
  · rintro ⟨z, w, ⟨rfl, rfl⟩, -⟩; exact ⟨e z, e w⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨a, b, ⟨(e a).symm, (e b).symm⟩, hab⟩

/-- ✱165·243. \(\vdash :\dot{\exists} !Q.\equiv .\dot{\exists} !P\downarrow_{.,} ^{;}Q\) -/
theorem pm165_243 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    rEx Q ↔ rEx (coupleSemi P ⁏ Q) := by
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨_, _, (coupleSemi_semi_apply P Q _ _).2 ⟨a, b, ⟨rfl, rfl⟩, hab⟩⟩
  · rintro ⟨R, S, h⟩
    obtain ⟨z, w, -, hzw⟩ := (coupleSemi_semi_apply P Q R S).1 h
    exact ⟨z, w, hzw⟩

/-- ✱165·244. \(\vdash :\dot{\Lambda} \in CʻP\downarrow_{.,} ^{;}Q.\equiv .P=\dot{\Lambda} .\dot{\exists} !Q.\equiv .P\downarrow_{.,} ^{;}Q=\dot{\Lambda} \downarrow \dot{\Lambda}\)

The chain is the conjunction of its links. -/
theorem pm165_244 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    (rNull ∈ fld (coupleSemi P ⁏ Q) ↔ P = rNull ∧ rEx Q) ∧
      (P = rNull ∧ rEx Q ↔ coupleSemi P ⁏ Q = rNull ↓ rNull) := by
  have a : rNull ∈ fld (coupleSemi P ⁏ Q) ↔ P = rNull ∧ rEx Q := by
    rw [mem_fld_coupleSemi_semi]
    constructor
    · rintro ⟨z, hz, e⟩
      refine ⟨eq_rNull_of_not_rEx fun hP => ?_, (rEx_iff_fld).2 ⟨z, hz⟩⟩
      obtain ⟨X, Y, h⟩ := (rEx_opSemi (z := z)).2 hP
      rw [← e] at h
      exact rNull_apply _ _ h
    · rintro ⟨hP, hQ⟩
      obtain ⟨z, hz⟩ := rEx_iff_fld.1 hQ
      exact ⟨z, hz, by rw [hP, pm165_01, semi_rNull]⟩
  refine ⟨a, ⟨pm165_242, fun h => a.1 ?_⟩⟩
  rw [h, fld_couple]
  exact Or.inl (mem_unitCls.2 rfl)

/-- ✱165·245. \[\begin{align}&\vdash \colon\ldotp \dot{\exists} !P.\lor.Q = \dot{\Lambda} : \equiv .\dot{\Lambda} {\sim} \in CʻP\downarrow_{.,} ^{;}Q. \equiv .\dot{\Lambda} {\sim} \in (CʻP)\downarrow_{,,}ʻʻCʻQ\\ &[*165·244.\text{Transp}.*33·241.*165·14]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `Λ̇ ∼∈ (C'P)↓,,''C'Q`; the
members of `(C'P)↓,,''C'Q` are classes, so only the null class `Λ` is significant (the proof
cites ✱33·241, `C'P = Λ . ≡ . P = Λ̇`, with ✱165·14). The chain is the conjunction of its links. -/
theorem pm165_245 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    ((rEx P ∨ Q = rNull) ↔ rNull ∉ fld (coupleSemi P ⁏ Q)) ∧
      (rNull ∉ fld (coupleSemi P ⁏ Q) ↔ (Λ : Set (α → β → Prop)) ∉ coupleImg (fld P) ʻʻ fld Q) := by
  rw [pm165_244.1]
  constructor
  · constructor
    · rintro (hP | hQ) ⟨hP', hQ'⟩
      · rw [hP'] at hP; obtain ⟨a, b, h⟩ := hP; exact rNull_apply a b h
      · rw [hQ] at hQ'; obtain ⟨a, b, h⟩ := hQ'; exact rNull_apply a b h
    · intro h
      by_cases hP : rEx P
      · exact Or.inl hP
      · exact Or.inr (eq_rNull_of_not_rEx fun hQ => h ⟨eq_rNull_of_not_rEx hP, hQ⟩)
  · apply not_congr
    constructor
    · rintro ⟨hP, hQ⟩
      obtain ⟨z, hz⟩ := rEx_iff_fld.1 hQ
      refine ⟨z, hz, ?_⟩
      show Λ = opImg couple (fld P) z
      rw [← pm165_13.2, ← pm165_13.1, hP, pm165_01, semi_rNull, fld_rNull, Null_eq_empty]
    · rintro ⟨z, hz, hL⟩
      have hL' : Λ = opImg couple (fld P) z := hL
      rw [← pm165_13.2, ← pm165_13.1, Null_eq_empty] at hL'
      refine ⟨eq_rNull_of_not_rEx fun hP => ?_, rEx_iff_fld.2 ⟨z, hz⟩⟩
      obtain ⟨a, b, hab⟩ := hP
      have : a ↓ z ∈ fld (opSemi couple P z) := by
        rw [fld_opSemi_couple]; exact ⟨a, mem_fld_l hab, rfl⟩
      rw [← hL'] at this
      exact this

/-- ✱165·25. \[\begin{align}&\vdash :\dot{\exists} !P.\supset .P\downarrow_{.,} ^{;}Q\,\text{smor}\,Q.(P\downarrow_{.,} )\upharpoonright CʻQ\in (P\downarrow_{.,} ^{;}Q)\,\overline{\text{smor}}\,Q\\ &[*165·22·206.*151·231]\end{align}\] -/
theorem pm165_25 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    rEx P → smor (coupleSemi P ⁏ Q) Q ∧ coupleSemi P ↾ fld Q ∈ smorbar (coupleSemi P ⁏ Q) Q := by
  intro hP
  have h : coupleSemi P ↾ fld Q ∈ smorbar (coupleSemi P ⁏ Q) Q :=
    ⟨⟨cres_oneone (pm165_22 hP), codom_cres_eq.2 fun z _ => ⟨_, rfl⟩⟩,
      (cres_semi_of Set.Subset.rfl).symm⟩
  exact ⟨⟨_, h⟩, h⟩

/-- ✱165·251. \[\begin{align}&\vdash .P\downarrow_{.,} x\,\text{smor}\,P.(\downarrow x)\upharpoonright CʻP\in (P\downarrow_{.,} x)\overline{\text{smor}} P\\ &[*72·184.*55·21.*151·22]\end{align}\]

`(↓x) ↾ C'P` is `coupleR x ↾ fld P`. -/
theorem pm165_251 {α β : Type*} {P : α → α → Prop} {x : β} :
    smor (opSemi couple P x) P ∧ coupleR x ↾ fld P ∈ smorbar (opSemi couple P x) P := by
  have o : (coupleR x : (α → β → Prop) → α → Prop) ∈ arrow one one := by
    rw [oneone_iff]
    refine ⟨fun X Y a h => ?_, fun X a b h => ?_⟩
    · exact (h.1 : X = a ↓ x).trans (h.2 : Y = a ↓ x).symm
    · exact (couple_eq_couple_iff.1 ((h.1 : X = a ↓ x).symm.trans (h.2 : X = b ↓ x))).1
  have h : coupleR x ↾ fld P ∈ smorbar (opSemi couple P x) P :=
    ⟨⟨cres_oneone o, codom_cres_eq.2 fun a _ => ⟨a ↓ x, rfl⟩⟩,
      (cres_semi_of Set.Subset.rfl).symm⟩
  exact ⟨⟨_, h⟩, h⟩

/-- ✱165·26. \(\vdash .CʻP\downarrow_{.,} ^{;}Q\subset \text{Nr}ʻP \quad[*165·251·12.*152·11]\)

`Nr'P` is taken in the type `α → β → Prop` of the members of `C'P↓.,;Q`. -/
theorem pm165_26 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    fld (coupleSemi P ⁏ Q) ⊆ nr (α → β → Prop) P := by
  intro R hR
  obtain ⟨z, -, rfl⟩ := mem_fld_coupleSemi_semi.1 hR
  exact pm165_251.1

/-- ✱165·27. \[\begin{align}&\vdash :\dot{\exists} !P.\supset .P\downarrow_{.,} ^{;}Q\in \text{Rel}^{2}\text{excl}\cap \text{Nr}ʻQ.CʻP\downarrow_{.,} ^{;}Q\in \text{Cl}ʻ\text{Nr}ʻP\\ &[*165·21·25.*152·11.*165·26]\end{align}\] -/
theorem pm165_27 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    rEx P →
      coupleSemi P ⁏ Q ∈ Rel2excl ∩ nr ((α → β → Prop) → (α → β → Prop) → Prop) Q ∧
        fld (coupleSemi P ⁏ Q) ∈ cl (nr (α → β → Prop) P) :=
  fun hP => ⟨⟨pm165_21, (pm165_25 hP).1⟩, pm165_26⟩

/-- ✱165·3. \(\vdash :\text{E}!Rʻy.\supset .\downarrow zʻRʻy = R\mid ʻ\downarrow zʻy\)

`↓z'R'y` keeps the description `R'y`; `R|'↓z'y` is `R ⨾ (y ↓ z)`. -/
theorem pm165_3 {α β γ : Type*} {R : γ → α → Prop} {y : α} {z : β} :
    EDesc R y → Desc R y (fun u => u ↓ z = R ⨾ (y ↓ z)) := by
  rintro ⟨b, hb⟩
  exact (TheIs_iff_of_unique hb).2 (relProd_couple hb z).symm

/-- ✱165·301. \(\vdash :R\in 1\rightarrow \text{Cls}.\supset .\downarrow z\mid R = (R\mid )\mid (\downarrow z)\upharpoonright \text{ᗡ}ʻR\)

`(R|)|(↓z) ↾ ᗡ'R` is `{(R|)|(↓z)} ↾ ᗡ'R`. -/
theorem pm165_301 {α β γ : Type*} {R : γ → α → Prop} {z : β} :
    R ∈ arrow one Cls → coupleR z ⨾ R = (relProdL R ⨾ coupleR z) ↾ codom R := by
  intro hR
  refine rel_ext' fun M y => ⟨?_, ?_⟩
  · rintro ⟨u, hM, hu⟩
    have hM' : M = u ↓ z := hM
    have hb : ∀ x, R x y ↔ x = u := fun x =>
      ⟨fun hx => mem_arrow_one_Cls.1 hR x u y ⟨hx, hu⟩, fun e => e ▸ hu⟩
    exact ⟨⟨y ↓ z, by show M = R ⨾ (y ↓ z); rw [hM', relProd_couple hb z], rfl⟩, ⟨u, hu⟩⟩
  · rintro ⟨⟨X, hM, hX⟩, ⟨u, hu⟩⟩
    have hb : ∀ x, R x y ↔ x = u := fun x =>
      ⟨fun hx => mem_arrow_one_Cls.1 hR x u y ⟨hx, hu⟩, fun e => e ▸ hu⟩
    have hX' : X = y ↓ z := hX
    have hM' : M = R ⨾ X := hM
    refine ⟨u, ?_, hu⟩
    show M = u ↓ z
    rw [hM', hX', relProd_couple hb z]

/-- ✱165·302. \(\vdash :\text{E}!!RʻʻCʻP.\supset .\downarrow z^{;}R^{;}P = R\mid ^{;}\downarrow z^{;}P\)

`↓z;R;P` is `↓z;(R;P)` and `R|;↓z;P` is `(R|);(↓z;P)` (✱150·05). -/
theorem pm165_302 {α β γ : Type*} {R : γ → α → Prop} {P : α → α → Prop} {z : β} :
    EE R (fld P) → coupleR z ⁏ R ⁏ P = relProdL R ⁏ coupleR z ⁏ P := by
  intro h
  rw [semi_semi, semi_semi, ← cres_semi_of (S := coupleR z ⨾ R) (B := fld P) Set.Subset.rfl,
    ← cres_semi_of (S := relProdL R ⨾ coupleR z) (B := fld P) Set.Subset.rfl]
  congr 1
  refine rel_ext' fun M y => ⟨fun ⟨hM, hy⟩ => ⟨?_, hy⟩, fun ⟨hM, hy⟩ => ⟨?_, hy⟩⟩
  · obtain ⟨b, hb⟩ := h y hy
    obtain ⟨u, hMu, hu⟩ := hM
    have hMu' : M = u ↓ z := hMu
    rw [(hb u).1 hu] at hMu'
    exact ⟨y ↓ z, by show M = R ⨾ (y ↓ z); rw [hMu', relProd_couple hb z], rfl⟩
  · obtain ⟨b, hb⟩ := h y hy
    obtain ⟨X, hMX, hX⟩ := hM
    have hMX' : M = R ⨾ X := hMX
    have hX' : X = y ↓ z := hX
    refine ⟨b, ?_, (hb b).2 rfl⟩
    show M = b ↓ z
    rw [hMX', hX', relProd_couple hb z]

private theorem coupleSemi_semi_relProdL {α β γ : Type*} {R : γ → α → Prop} {P : α → α → Prop}
    {Q : β → β → Prop} (h : EE R (fld P)) :
    coupleSemi (R ⁏ P) ⁏ Q = daggerRel (relProdL R) ⁏ coupleSemi P ⁏ Q := by
  have e : ∀ w : β, opSemi couple (R ⁏ P) w = relProdL R ⁏ opSemi couple P w := fun w =>
    pm165_302 h
  refine rel_ext' fun X Y => ?_
  rw [coupleSemi_semi_apply, semi_dagger_apply]
  constructor
  · rintro ⟨z, w, ⟨rfl, rfl⟩, hzw⟩
    exact ⟨_, _, ⟨e z, e w⟩, (coupleSemi_semi_apply P Q _ _).2 ⟨z, w, ⟨rfl, rfl⟩, hzw⟩⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, hAB⟩
    obtain ⟨z, w, ⟨rfl, rfl⟩, hzw⟩ := (coupleSemi_semi_apply P Q A B).1 hAB
    exact ⟨z, w, ⟨(e z).symm, (e w).symm⟩, hzw⟩

/-- ✱165·31. \(\vdash :\text{E}!!RʻʻCʻP.\supset .(R^{;}P)\downarrow_{.,} z=R\mid ^{;}P\downarrow_{.,} z.(R^{;}P)\downarrow_{.,} ^{;}Q=(R\mid )\dagger ^{;}P\downarrow_{.,} ^{;}Q\)

`(R|)†;P↓.,;Q` is `(R|)†;(P↓.,;Q)`. -/
theorem pm165_31 {α β γ : Type*} {R : γ → α → Prop} {P : α → α → Prop} {Q : β → β → Prop}
    {z : β} :
    EE R (fld P) →
      opSemi couple (R ⁏ P) z = relProdL R ⁏ opSemi couple P z ∧
        coupleSemi (R ⁏ P) ⁏ Q = daggerRel (relProdL R) ⁏ coupleSemi P ⁏ Q :=
  fun h => ⟨pm165_302 h, coupleSemi_semi_relProdL h⟩

/-- ✱165·311. \[\begin{align}\vdash :R\upharpoonright CʻP\in 1\rightarrow \text{Cls}.&CʻP\subset \text{ᗡ}ʻR.\supset .\\ &(R^{;}P)\downarrow_{.,} z=R\mid ^{;}P\downarrow_{.,} z.(R^{;}P)\downarrow_{.,} ^{;}Q=(R\mid )\dagger ^{;}P\downarrow_{.,} ^{;}Q\\ [*165·31.*71·571]\end{align}\]

`R ↾ C'P ∈ 1 → Cls . C'P ⊂ ᗡ'R` gives `E!!R''C'P` (✱71·571). -/
theorem pm165_311 {α β γ : Type*} {R : γ → α → Prop} {P : α → α → Prop} {Q : β → β → Prop}
    {z : β} :
    R ↾ fld P ∈ arrow one Cls ∧ fld P ⊆ codom R →
      opSemi couple (R ⁏ P) z = relProdL R ⁏ opSemi couple P z ∧
        coupleSemi (R ⁏ P) ⁏ Q = daggerRel (relProdL R) ⁏ coupleSemi P ⁏ Q :=
  fun ⟨h1, h2⟩ => pm165_31 (EE_of h1 h2)

/-- ✱165·32. \(\vdash :\text{E}!Sʻz.\supset .\downarrow (Sʻz)=(\mid \breve{S} )\mid \downarrow z.\downarrow (Sʻz)^{;}P=\mid \breve{S} ^{;}\downarrow z^{;}P\)

`↓(S'z)` keeps the description `S'z`; `|S̆` is `relProdR S˘`, and the two equations, each with
its own description, form a product. -/
theorem pm165_32 {α β δ : Type*} {S : δ → β → Prop} {z : β} {P : α → α → Prop} :
    EDesc S z →
      Desc S z (fun u => (coupleR u : (α → δ → Prop) → α → Prop) = relProdR S˘ ⨾ coupleR z) ∧
        Desc S z (fun u => coupleR u ⁏ P = relProdR S˘ ⁏ coupleR z ⁏ P) := by
  rintro ⟨b, hb⟩
  have e : (coupleR b : (α → δ → Prop) → α → Prop) = relProdR S˘ ⨾ coupleR z := by
    refine rel_ext' fun M x => ⟨fun hM => ⟨x ↓ z, ?_, rfl⟩, fun ⟨X, hM, hX⟩ => ?_⟩
    · show M = (x ↓ z) ⨾ S˘
      rw [couple_relProd_cnv hb x]; exact hM
    · have hM' : M = X ⨾ S˘ := hM
      have hX' : X = x ↓ z := hX
      show M = x ↓ b
      rw [hM', hX', couple_relProd_cnv hb x]
  refine ⟨(TheIs_iff_of_unique hb).2 e, (TheIs_iff_of_unique hb).2 ?_⟩
  rw [semi_semi, ← e]

/-- ✱165·321. \(\vdash :\text{E}!Sʻz.\supset .P\downarrow_{.,} (Sʻz)=\mid \breve{S} ^{;}P\downarrow_{.,} z \quad[*165·32·01]\) -/
theorem pm165_321 {α β δ : Type*} {S : δ → β → Prop} {z : β} {P : α → α → Prop} :
    EDesc S z → Desc S z (fun u => opSemi couple P u = relProdR S˘ ⁏ opSemi couple P z) :=
  fun h => (pm165_32 h).2

/-- ✱165·33. \(\vdash :\text{E}!!SʻʻCʻQ.\supset .P\downarrow_{.,} ^{;}S^{;}Q=(\mid \breve{S} )\dagger ^{;}P\downarrow_{.,} ^{;}Q\)

`P↓.,;S;Q` is `P↓.,;(S;Q)`. -/
theorem pm165_33 {α β δ : Type*} {S : δ → β → Prop} {P : α → α → Prop} {Q : β → β → Prop} :
    EE S (fld Q) → coupleSemi P ⁏ S ⁏ Q = daggerRel (relProdR S˘) ⁏ coupleSemi P ⁏ Q := by
  intro h
  have e : ∀ z, z ∈ fld Q → ∀ u, S u z →
      opSemi couple P u = relProdR S˘ ⁏ opSemi couple P z := by
    intro z hz u hu
    obtain ⟨b, hb⟩ := h z hz
    have := (TheIs_iff_of_unique hb).1 (pm165_321 (P := P) ⟨b, hb⟩)
    rw [(hb u).1 hu]; exact this
  refine rel_ext' fun X Y => ?_
  rw [coupleSemi_semi_apply, semi_dagger_apply]
  constructor
  · rintro ⟨u, v, ⟨rfl, rfl⟩, huv⟩
    obtain ⟨z, w, hu, hv, hzw⟩ := (semi_iff' S Q u v).1 huv
    exact ⟨_, _, ⟨e z (mem_fld_l hzw) u hu, e w (mem_fld_r hzw) v hv⟩,
      (coupleSemi_semi_apply P Q _ _).2 ⟨z, w, ⟨rfl, rfl⟩, hzw⟩⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, hAB⟩
    obtain ⟨z, w, ⟨rfl, rfl⟩, hzw⟩ := (coupleSemi_semi_apply P Q A B).1 hAB
    obtain ⟨u, hu⟩ := h z (mem_fld_l hzw)
    obtain ⟨v, hv⟩ := h w (mem_fld_r hzw)
    exact ⟨u, v, ⟨(e z (mem_fld_l hzw) u ((hu u).2 rfl)).symm,
      (e w (mem_fld_r hzw) v ((hv v).2 rfl)).symm⟩,
      (semi_iff' S Q u v).2 ⟨z, w, (hu u).2 rfl, (hv v).2 rfl, hzw⟩⟩

/-- ✱165·331. \[\begin{align}&\vdash :S\upharpoonright CʻQ\in 1\rightarrow \text{Cls}.CʻQ\subset \text{ᗡ}ʻS.\supset .P\downarrow_{.,} ^{;}S^{;}Q=(\mid \breve{S} )\dagger ^{;}P\downarrow_{.,} ^{;}Q\\ &[*165·33.*71·571]\end{align}\] -/
theorem pm165_331 {α β δ : Type*} {S : δ → β → Prop} {P : α → α → Prop} {Q : β → β → Prop} :
    S ↾ fld Q ∈ arrow one Cls ∧ fld Q ⊆ codom S →
      coupleSemi P ⁏ S ⁏ Q = daggerRel (relProdR S˘) ⁏ coupleSemi P ⁏ Q :=
  fun ⟨h1, h2⟩ => pm165_33 (EE_of h1 h2)

private theorem dpar_cnv_eq {α β γ δ : Type*} (R : γ → α → Prop) (S : δ → β → Prop) :
    R ∥ S˘ = relProdL R ⨾ relProdR S˘ := by
  refine rel_ext' fun M X => ?_
  rw [dpar_iff]
  constructor
  · intro h; exact ⟨X ⨾ S˘, h, rfl⟩
  · rintro ⟨N, hM, hN⟩
    have hM' : M = R ⨾ N := hM
    have hN' : N = X ⨾ S˘ := hN
    rw [hM', hN']

/-- ✱165·34. \(\vdash :\text{E}!!RʻʻCʻP.\text{E}!!SʻʻCʻQ.\supset .(R^{;}P)\downarrow_{.,} ^{;}(S^{;}Q)=(R\parallel \breve{S} )\dagger ^{;}(P\downarrow_{.,} ^{;}Q)\)

`(R ‖ S̆)†` is `daggerRel (R ∥ S˘)`. -/
theorem pm165_34 {α β γ δ : Type*} {R : γ → α → Prop} {S : δ → β → Prop} {P : α → α → Prop}
    {Q : β → β → Prop} :
    EE R (fld P) ∧ EE S (fld Q) →
      coupleSemi (R ⁏ P) ⁏ (S ⁏ Q) = daggerRel (R ∥ S˘) ⁏ (coupleSemi P ⁏ Q) := by
  rintro ⟨hR, hS⟩
  have eR : ∀ u : δ, opSemi couple (R ⁏ P) u = relProdL R ⁏ opSemi couple P u := fun u =>
    pm165_302 hR
  have eS : ∀ z, z ∈ fld Q → ∀ u, S u z →
      opSemi couple P u = relProdR S˘ ⁏ opSemi couple P z := by
    intro z hz u hu
    obtain ⟨b, hb⟩ := hS z hz
    have := (TheIs_iff_of_unique hb).1 (pm165_321 (P := P) ⟨b, hb⟩)
    rw [(hb u).1 hu]; exact this
  have key : ∀ z, z ∈ fld Q → ∀ u, S u z →
      opSemi couple (R ⁏ P) u = (R ∥ S˘) ⁏ opSemi couple P z := by
    intro z hz u hu
    rw [dpar_cnv_eq, ← semi_semi, ← eS z hz u hu, eR u]
  refine rel_ext' fun X Y => ?_
  rw [coupleSemi_semi_apply, semi_dagger_apply]
  constructor
  · rintro ⟨u, v, ⟨rfl, rfl⟩, huv⟩
    obtain ⟨z, w, hu, hv, hzw⟩ := (semi_iff' S Q u v).1 huv
    exact ⟨_, _, ⟨key z (mem_fld_l hzw) u hu, key w (mem_fld_r hzw) v hv⟩,
      (coupleSemi_semi_apply P Q _ _).2 ⟨z, w, ⟨rfl, rfl⟩, hzw⟩⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, hAB⟩
    obtain ⟨z, w, ⟨rfl, rfl⟩, hzw⟩ := (coupleSemi_semi_apply P Q A B).1 hAB
    obtain ⟨u, hu⟩ := hS z (mem_fld_l hzw)
    obtain ⟨v, hv⟩ := hS w (mem_fld_r hzw)
    exact ⟨u, v, ⟨(key z (mem_fld_l hzw) u ((hu u).2 rfl)).symm,
      (key w (mem_fld_r hzw) v ((hv v).2 rfl)).symm⟩,
      (semi_iff' S Q u v).2 ⟨z, w, (hu u).2 rfl, (hv v).2 rfl, hzw⟩⟩

/-- ✱165·341. \[\begin{align}\vdash :R \upharpoonright CʻP,S &\upharpoonright CʻQ \in 1 \rightarrow \text{Cls}.CʻP \subset \text{ᗡ}ʻR.CʻQ \subset \text{ᗡ}ʻS.\supset .\\ &(R^{;}P) \downarrow_{.,} ^{;}(S^{;}Q) = (R \parallel \breve{S} )\dagger ^{;}P\downarrow_{.,} ^{;}Q \quad[*165·34.*71·571]\end{align}\] -/
theorem pm165_341 {α β γ δ : Type*} {R : γ → α → Prop} {S : δ → β → Prop} {P : α → α → Prop}
    {Q : β → β → Prop} :
    ((R ↾ fld P ∈ arrow one Cls ∧ S ↾ fld Q ∈ arrow one Cls) ∧ fld P ⊆ codom R) ∧
        fld Q ⊆ codom S →
      coupleSemi (R ⁏ P) ⁏ (S ⁏ Q) = daggerRel (R ∥ S˘) ⁏ coupleSemi P ⁏ Q :=
  fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => pm165_34 ⟨EE_of h1 h3, EE_of h2 h4⟩

/-- ✱165·35. \(\vdash :R \upharpoonright CʻP \in \text{Cls} \rightarrow 1.CʻP \subset \text{ᗡ}ʻR.\supset .(R\mid )\upharpoonright Cʻ\Sigma ʻP \downarrow_{.,} ^{;}Q \in 1 \rightarrow 1\)

`(R|) ↾ C'Σ'P↓.,;Q` is `relProdL R ↾ fld (relSigma (coupleSemi P ⁏ Q))`. -/
theorem pm165_35 {α β γ : Type*} {R : γ → α → Prop} {P : α → α → Prop} {Q : β → β → Prop} :
    R ↾ fld P ∈ arrow Cls one ∧ fld P ⊆ codom R →
      relProdL R ↾ fld (relSigma (coupleSemi P ⁏ Q)) ∈ arrow one one := by
  rintro ⟨h1, h2⟩
  rw [pm165_16, oneone_iff]
  refine ⟨fun M M' X h => ?_, fun M X X' h => ?_⟩
  · exact (h.1.1 : M = R ⨾ X).trans (h.2.1 : M' = R ⨾ X).symm
  · obtain ⟨⟨hM, hX⟩, ⟨hM', hX'⟩⟩ := h
    obtain ⟨x, z, ⟨hx, hz⟩, rfl⟩ := mem_clsTimes'.1 hX
    obtain ⟨x', z', ⟨hx', hz'⟩, rfl⟩ := mem_clsTimes'.1 hX'
    have e : R ⨾ (x ↓ z) = R ⨾ (x' ↓ z') :=
      (hM : M = R ⨾ (x ↓ z)).symm.trans (hM' : M = R ⨾ (x' ↓ z'))
    obtain ⟨u, hu⟩ := h2 hx
    have : (R ⨾ (x' ↓ z')) u z := by
      rw [← e]; exact ⟨x, hu, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩⟩
    obtain ⟨v, huv, hv⟩ := this
    rw [couple_apply] at hv
    rw [hv.1] at huv
    have hxx : x = x' := mem_arrow_Cls_one.1 h1 u x x' ⟨⟨hu, hx⟩, ⟨huv, hx'⟩⟩
    rw [hxx, hv.2]

/-- ✱165·351. \(\vdash :S \upharpoonright CʻQ \in \text{Cls} \rightarrow 1.CʻQ \subset \text{ᗡ}ʻS.\supset .(\mid \breve{S} ) \upharpoonright Cʻ\Sigma ʻP \downarrow_{.,} ^{;}Q \in 1 \rightarrow 1\) -/
theorem pm165_351 {α β δ : Type*} {S : δ → β → Prop} {P : α → α → Prop} {Q : β → β → Prop} :
    S ↾ fld Q ∈ arrow Cls one ∧ fld Q ⊆ codom S →
      relProdR S˘ ↾ fld (relSigma (coupleSemi P ⁏ Q)) ∈ arrow one one := by
  rintro ⟨h1, h2⟩
  rw [pm165_16, oneone_iff]
  refine ⟨fun M M' X h => ?_, fun M X X' h => ?_⟩
  · exact (h.1.1 : M = X ⨾ S˘).trans (h.2.1 : M' = X ⨾ S˘).symm
  · obtain ⟨⟨hM, hX⟩, ⟨hM', hX'⟩⟩ := h
    obtain ⟨x, z, ⟨hx, hz⟩, rfl⟩ := mem_clsTimes'.1 hX
    obtain ⟨x', z', ⟨hx', hz'⟩, rfl⟩ := mem_clsTimes'.1 hX'
    have e : (x ↓ z) ⨾ S˘ = (x' ↓ z') ⨾ S˘ :=
      (hM : M = (x ↓ z) ⨾ S˘).symm.trans (hM' : M = (x' ↓ z') ⨾ S˘)
    obtain ⟨c, hc⟩ := h2 hz
    have : ((x' ↓ z') ⨾ S˘) x c := by
      rw [← e]; exact ⟨z, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩, hc⟩
    obtain ⟨v, hv, hcv⟩ := this
    rw [couple_apply] at hv
    have hcv' : S c v := hcv
    rw [hv.2] at hcv'
    have hzz : z = z' := mem_arrow_Cls_one.1 h1 c z z' ⟨⟨hc, hz⟩, ⟨hcv', hz'⟩⟩
    rw [hv.1, hzz]

/-- ✱165·352. \[\begin{align}\vdash :R \upharpoonright CʻP,S \upharpoonright CʻQ \in \text{Cls} \rightarrow 1.CʻP \subset \text{ᗡ}ʻR.&CʻQ \subset \text{ᗡ}ʻS.\supset .\\ &(R\parallel \breve{S} ) \upharpoonright Cʻ\Sigma ʻP\downarrow_{.,} ^{;}Q \in 1 \rightarrow 1\end{align}\] -/
theorem pm165_352 {α β γ δ : Type*} {R : γ → α → Prop} {S : δ → β → Prop} {P : α → α → Prop}
    {Q : β → β → Prop} :
    ((R ↾ fld P ∈ arrow Cls one ∧ S ↾ fld Q ∈ arrow Cls one) ∧ fld P ⊆ codom R) ∧
        fld Q ⊆ codom S →
      (R ∥ S˘) ↾ fld (relSigma (coupleSemi P ⁏ Q)) ∈ arrow one one := by
  rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  rw [pm165_16, oneone_iff]
  refine ⟨fun M M' X h => ?_, fun M X X' h => ?_⟩
  · rw [(dpar_iff _ _ _ _).1 h.1.1, (dpar_iff _ _ _ _).1 h.2.1]
  · obtain ⟨⟨hM, hX⟩, ⟨hM', hX'⟩⟩ := h
    rw [dpar_iff] at hM hM'
    obtain ⟨x, z, ⟨hx, hz⟩, rfl⟩ := mem_clsTimes'.1 hX
    obtain ⟨x', z', ⟨hx', hz'⟩, rfl⟩ := mem_clsTimes'.1 hX'
    have e := hM.symm.trans hM'
    obtain ⟨u, hu⟩ := h3 hx
    obtain ⟨c, hc⟩ := h4 hz
    have : (R ⨾ ((x' ↓ z') ⨾ S˘)) u c := by
      rw [← e]; exact ⟨x, hu, z, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩, hc⟩
    obtain ⟨a, hua, v, hav, hcv⟩ := this
    rw [couple_apply] at hav
    rw [hav.1] at hua
    have hcv' : S c v := hcv
    rw [hav.2] at hcv'
    have hxx : x = x' := mem_arrow_Cls_one.1 h1 u x x' ⟨⟨hu, hx⟩, ⟨hua, hx'⟩⟩
    have hzz : z = z' := mem_arrow_Cls_one.1 h2 c z z' ⟨⟨hc, hz⟩, ⟨hcv', hz'⟩⟩
    rw [hxx, hzz]

/-- ✱165·36. \[\begin{align}\vdash :R \upharpoonright CʻP' \in \,P\overline{\text{smor}}\, &P'.\supset .\\ &(R\mid ) \upharpoonright Cʻ\Sigma ʻP'\downarrow_{.,} ^{;}Q \in (P\downarrow_{.,} ^{;}Q)\,\overline{\text{smor}} \,\overline{\text{smor}}\, (P'\downarrow_{.,} ^{;}Q)\end{align}\]

`R ↾ C'P' ∈ P smor̄ P'` with `R : γ → α → Prop` (`P` on `γ`, `P'` on `α`). -/
theorem pm165_36 {α β γ : Type*} {P : γ → γ → Prop} {P' : α → α → Prop} {Q : β → β → Prop}
    {R : γ → α → Prop} :
    R ↾ fld P' ∈ smorbar P P' →
      relProdL R ↾ fld (relSigma (coupleSemi P' ⁏ Q)) ∈
        smorsmorbar (coupleSemi P ⁏ Q) (coupleSemi P' ⁏ Q) := by
  rintro ⟨⟨o, c⟩, e⟩
  rw [codom_cres_eq] at c
  rw [cres_semi_of Set.Subset.rfl] at e
  refine pm164_18.2 ⟨⟨pm165_35 ⟨oneone_Cls_one o, c⟩, fun X _ => ⟨R ⨾ X, rfl⟩⟩, ?_⟩
  rw [e]
  exact coupleSemi_semi_relProdL (EE_of (mem_arrow_one_Cls.2 (oneone_iff.1 o).1) c)

/-- ✱165·361. \[\begin{align}\vdash :S\upharpoonright CʻQ' \in Q&\overline{\text{smor}} Q'.\supset .\\ &(\mid \breve{S} )\upharpoonright Cʻ\Sigma ʻP\downarrow_{.,} ^{;}Q' \in (P\downarrow_{.,} ^{;}Q)\,\overline{\text{smor}} \,\overline{\text{smor}}\, (P\downarrow_{.,} ^{;}Q')\\ [*165·351·331]\end{align}\] -/
theorem pm165_361 {α β δ : Type*} {P : α → α → Prop} {Q : δ → δ → Prop} {Q' : β → β → Prop}
    {S : δ → β → Prop} :
    S ↾ fld Q' ∈ smorbar Q Q' →
      relProdR S˘ ↾ fld (relSigma (coupleSemi P ⁏ Q')) ∈
        smorsmorbar (coupleSemi P ⁏ Q) (coupleSemi P ⁏ Q') := by
  rintro ⟨⟨o, c⟩, e⟩
  rw [codom_cres_eq] at c
  rw [cres_semi_of Set.Subset.rfl] at e
  refine pm164_18.2 ⟨⟨pm165_351 ⟨oneone_Cls_one o, c⟩, fun X _ => ⟨X ⨾ S˘, rfl⟩⟩, ?_⟩
  rw [e]
  exact pm165_331 ⟨mem_arrow_one_Cls.2 (oneone_iff.1 o).1, c⟩

/-- ✱165·362. \[\begin{align}\vdash :R \upharpoonright CʻP' \in P\,&\overline{\text{smor}}\,P'.S \upharpoonright CʻQ' \in Q\,\overline{\text{smor}}\,Q'.\supset .\\ &(R \parallel \breve{S} ) \upharpoonright Cʻ\Sigma ʻP'\downarrow_{.,} ^{;}Q' \in (P\downarrow_{.,} ^{;}Q) \,\overline{\text{smor}} \,\overline{\text{smor}}\, (P'\downarrow_{.,} ^{;}Q')\\ [*165·352·341]\end{align}\] -/
theorem pm165_362 {α β γ δ : Type*} {P : γ → γ → Prop} {P' : α → α → Prop} {Q : δ → δ → Prop}
    {Q' : β → β → Prop} {R : γ → α → Prop} {S : δ → β → Prop} :
    R ↾ fld P' ∈ smorbar P P' ∧ S ↾ fld Q' ∈ smorbar Q Q' →
      (R ∥ S˘) ↾ fld (relSigma (coupleSemi P' ⁏ Q')) ∈
        smorsmorbar (coupleSemi P ⁏ Q) (coupleSemi P' ⁏ Q') := by
  rintro ⟨⟨⟨oR, cR⟩, eR⟩, ⟨⟨oS, cS⟩, eS⟩⟩
  rw [codom_cres_eq] at cR cS
  rw [cres_semi_of Set.Subset.rfl] at eR eS
  refine pm164_18.2 ⟨⟨pm165_352 ⟨⟨⟨oneone_Cls_one oR, oneone_Cls_one oS⟩, cR⟩, cS⟩,
    fun X _ => ⟨R ⨾ (X ⨾ S˘), (dpar_iff _ _ _ _).2 rfl⟩⟩, ?_⟩
  rw [eR, eS]
  exact pm165_341 ⟨⟨⟨mem_arrow_one_Cls.2 (oneone_iff.1 oR).1,
    mem_arrow_one_Cls.2 (oneone_iff.1 oS).1⟩, cR⟩, cS⟩

/-- ✱165·37. \[\begin{align}&\vdash :P\,\text{smor}\,P'.Q\text{smor}Q'.\supset .P\downarrow_{.,} ^{;}Q\,\text{smor smor}\,P'\downarrow_{.,} ^{;}Q'\\ &[*165·362.*164·11.*151·12]\end{align}\] -/
theorem pm165_37 {α β γ δ : Type*} {P : γ → γ → Prop} {P' : α → α → Prop} {Q : δ → δ → Prop}
    {Q' : β → β → Prop} :
    smor P P' ∧ smor Q Q' → smorsmor (coupleSemi P ⁏ Q) (coupleSemi P' ⁏ Q') := by
  rintro ⟨⟨R, hR⟩, ⟨S, hS⟩⟩
  have hR' : R ↾ fld P' ∈ smorbar P P' := by rw [hR.1.2, cres_codom_self]; exact hR
  have hS' : S ↾ fld Q' ∈ smorbar Q Q' := by rw [hS.1.2, cres_codom_self]; exact hS
  exact ⟨_, pm165_362 ⟨hR', hS'⟩⟩

/-- ✱165·38. \[\begin{align}\vdash \colon\ldotp \text{Mult ax}.\supset :R\in \text{Rel}^{2}\text{excl}\cap &\text{Nr}ʻQ.CʻR\subset \text{Nr}ʻP.\supset .\\ &R\,\text{smor smor}\,P\downarrow_{.,} ^{;}Q\end{align}\]

`R ∈ Nr'Q` with `R` a relation of relations on `γ`, `C'R ⊂ Nr'P` in the type `γ`; `Mult ax` is at
the type of the correlators `γ → (α → β → Prop) → Prop`. -/
theorem pm165_38 {α β γ : Type*} {P : α → α → Prop} {Q : β → β → Prop}
    {R : (γ → γ → Prop) → (γ → γ → Prop) → Prop} :
    MultAx (γ → (α → β → Prop) → Prop) →
      (R ∈ Rel2excl ∩ nr (γ → γ → Prop) Q ∧ fld R ⊆ nr γ P → smorsmor R (coupleSemi P ⁏ Q)) := by
  rintro hM ⟨⟨hRe, hRQ⟩, hRP⟩
  by_cases hP : rEx P
  · refine pm164_44 hM ⟨⟨hRe, pm165_21⟩, ?_⟩
    obtain ⟨T, hT⟩ := smor_trans (mem_nr.1 hRQ) (smor_symm (pm165_25 (Q := Q) hP).1)
    refine ⟨T, hT, fun M N hMN => ?_⟩
    have hMf : M ∈ fld R := by rw [← dom_of_smorbar hT]; exact ⟨N, hMN⟩
    have hNf : N ∈ fld (coupleSemi P ⁏ Q) := by rw [hT.1.2]; exact ⟨M, hMN⟩
    exact smor_trans (mem_nr.1 (hRP hMf)) (smor_symm (pm165_26 hNf))
  · have hP' := eq_rNull_of_not_rEx hP
    by_cases hQ : rEx Q
    · rw [pm165_242 ⟨hP', hQ⟩]
      have hfR : ∀ M, M ∈ fld R → M = rNull := fun M hM => by
        have h1 : smor M P := mem_nr.1 (hRP hM)
        rw [hP'] at h1
        exact smor_rNull_iff.1 h1
      have hRne : rEx R := by
        by_contra hn
        have h1 : smor R Q := mem_nr.1 hRQ
        rw [eq_rNull_of_not_rEx hn] at h1
        have hQ0 : Q = rNull := smor_rNull_iff.1 (smor_symm h1)
        rw [hQ0] at hQ
        obtain ⟨a, b, hab⟩ := hQ
        exact rNull_apply a b hab
      have hR0 : R = rNull ↓ rNull := by
        obtain ⟨a, b, hab⟩ := hRne
        refine rel_ext' fun M N => ⟨fun h => (couple_apply _ _ _ _).2
          ⟨hfR M (mem_fld_l h), hfR N (mem_fld_r h)⟩, fun h => ?_⟩
        rw [couple_apply] at h
        rw [hfR a (mem_fld_l hab), hfR b (mem_fld_r hab)] at hab
        rw [h.1, h.2]
        exact hab
      have e1 : fld (rNull : γ → γ → Prop) ∩ fld (rNull : γ → γ → Prop) = Λ := by
        rw [fld_rNull, Null_eq_empty, Set.inter_self]
      have e2 : fld (rNull : (α → β → Prop) → (α → β → Prop) → Prop) ∩ fld rNull = Λ := by
        rw [fld_rNull, Null_eq_empty, Set.inter_self]
      rw [hR0]
      exact pm164_34 ⟨⟨⟨smor_rNull, smor_rNull⟩, e1⟩, e2⟩
    · have hQ' := eq_rNull_of_not_rEx hQ
      have hR0 : R = rNull := smor_rNull_iff.1 (by rw [← hQ']; exact mem_nr.1 hRQ)
      rw [pm165_241 hQ', hR0]
      exact pm164_32.2

/-!
## [✱166] The product of two relations

*(Vol. 2, p. 396)*

> *Summary of* *166.
>
> The product \(Q \times P\) is defined as \(\Sigma ʻP\downarrow_{.,}^{;}Q\). This is a relation which has for its field all the couples that can be formed by choosing the referent in \(CʻP\) and the relatum in \(CʻQ\). These couples are arranged by \(Q \times P\) on the following principle: If the relatum of the one couple has the relation \(Q\) to the relatum of the other, we put the one before the other, and if the relata of the two couples are equal while the referent of the one has the relation \(P\) to the referent of the other, we put the one before the other. Thus in advancing from any term \(x\downarrow y\) in the field of \(Q \times P\), we first keep \(y\) fixed and alter \(x\) into later terms as long as possible; then we alter \(y\) into a later term, move \(x\) back to the beginning, and so on. Thus with a given \(y\), we get a series which is like \(P\), and this series is wholly followed or wholly preceded by the series with the referent \(y'\), where \(y'\) follows or precedes \(y\).
>
> The propositions of this number are for the most part immediate consequences of those of *165. The most important of them are:
>
> …

**Lean reading.** `Q × P` is `Q ×ᵣ P` (`rtimes Q P := relSigma (coupleSemi P ⁏ Q)`), with
`Q : β → β → Prop`, `P : α → α → Prop` and couples `x ↓ z : α → β → Prop`; `P × Q × R` is
`(P ×ᵣ Q) ×ᵣ R` (`infixl`); the class product `C'P × C'Q` is `fld P ×ₐ fld Q`. `×P` is the
relation `opR rtimes P` (✱38·02), so `×P;Q` is `opR rtimes P ⁏ Q`; `P↓.,y` is
`opSemi couple P y`; `R|`, `|S̆`, `R ‖ S̆` are as in ✱165; `B⃗'P` is `refs Beg P`. The e-text
prints `Pʻ`, `Qʻ`, `xʻ`, `yʻ` for `P'`, `Q'`, `x'`, `y'` in places (✱166·2·21·3·4·401); they are
the primed letters. Transcription errors: ✱166·13 (`=` for `≡`), ✱166·41 (misplaced braces),
✱166·472 (`C'P ↓ C'Q` for `C'P ↑ C'Q`), ✱166·511 (`ι'y ↑ C'P` for `ι'y ↑ C'Q`); see their
docstrings. `Mult ax` (✱166·24) is at the type of the correlators, as in ✱165·38.

**Status.** proved (all propositions; ✱166·01·421 definition; ✱166·13·41·472·511 proved
(reading), see their docstrings)
-/

/-- ✱166·01 (Df). \(Q\times P=\Sigma ʻP\downarrow_{.,} ^{;}Q \quad\text{Df}\) -/
theorem pm166_01 {α β : Type*} {Q : β → β → Prop} {P : α → α → Prop} :
    Q ×ᵣ P = relSigma (coupleSemi P ⁏ Q) := rfl

/-- ✱166·1. \(\vdash .Q\times P=\Sigma ʻP\downarrow_{.,} ^{;}Q \quad[(*166·01)]\) -/
theorem pm166_1 {α β : Type*} {Q : β → β → Prop} {P : α → α → Prop} :
    Q ×ᵣ P = relSigma (coupleSemi P ⁏ Q) := rfl

/-- ✱166·11. \[\begin{align}\vdash \colon\ldotp M(Q\times P)&N.\equiv :(\exists x,y,z,w):x,y\in CʻP.z,w\in CʻQ:zQw.\lor.\\ &z=w.xPy:M=x\downarrow z.N=y\downarrow w \quad[*165·17.*166·1]\end{align}\] -/
theorem pm166_11 {α β : Type*} {Q : β → β → Prop} {P : α → α → Prop} {M N : α → β → Prop} :
    (Q ×ᵣ P) M N ↔
      ∃ x y z w, (((x ∈ fld P ∧ y ∈ fld P) ∧ (z ∈ fld Q ∧ w ∈ fld Q)) ∧
        (Q z w ∨ z = w ∧ P x y)) ∧ (M = x ↓ z ∧ N = y ↓ w) :=
  pm165_17

/-- ✱166·111. \[\begin{align}\vdash \colon\ldotp M(P\times Q)&N.\equiv :(\exists x,y,z,w):x,y\in CʻP.z,w\in CʻQ:xPy.\lor.\\ &x=y.zQw:M=z\downarrow x.N=w\downarrow y \quad[*165·17.*166·1]\end{align}\] -/
theorem pm166_111 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {M N : β → α → Prop} :
    (P ×ᵣ Q) M N ↔
      ∃ x y z w, (((x ∈ fld P ∧ y ∈ fld P) ∧ (z ∈ fld Q ∧ w ∈ fld Q)) ∧
        (P x y ∨ x = y ∧ Q z w)) ∧ (M = z ↓ x ∧ N = w ↓ y) := by
  rw [pm166_11]
  constructor
  · rintro ⟨z, w, x, y, ⟨⟨⟨hz, hw⟩, ⟨hx, hy⟩⟩, h⟩, hM, hN⟩
    exact ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, h⟩, hM, hN⟩
  · rintro ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, h⟩, hM, hN⟩
    exact ⟨z, w, x, y, ⟨⟨⟨hz, hw⟩, ⟨hx, hy⟩⟩, h⟩, hM, hN⟩

/-- ✱166·112. \[\begin{align}\vdash \colon\ldotp (x\downarrow z)(Q\times P)(y\downarrow w).&\equiv :x,y\in CʻP.z,w\in CʻQ:zQw.\lor.\\ &z=w.xPy \quad[*166·11.*55·202.*13·22]\end{align}\] -/
theorem pm166_112 {α β : Type*} {Q : β → β → Prop} {P : α → α → Prop} {x y : α} {z w : β} :
    (Q ×ᵣ P) (x ↓ z) (y ↓ w) ↔
      ((x ∈ fld P ∧ y ∈ fld P) ∧ (z ∈ fld Q ∧ w ∈ fld Q)) ∧ (Q z w ∨ z = w ∧ P x y) := by
  rw [pm166_11]
  constructor
  · rintro ⟨a, b, c, d, h, e1, e2⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e1
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e2
    exact h
  · intro h; exact ⟨x, y, z, w, h, rfl, rfl⟩

/-- ✱166·113. \[\begin{align}\vdash \colon\colon x,y\in &CʻP.z,w\in CʻQ.\supset \colon\ldotp \\ &(x\downarrow z)(Q\times P)(y\downarrow w).\equiv :zQw.\lor.z=w.xPy \quad[*166·112]\end{align}\] -/
theorem pm166_113 {α β : Type*} {Q : β → β → Prop} {P : α → α → Prop} {x y : α} {z w : β} :
    (x ∈ fld P ∧ y ∈ fld P) ∧ (z ∈ fld Q ∧ w ∈ fld Q) →
      ((Q ×ᵣ P) (x ↓ z) (y ↓ w) ↔ Q z w ∨ z = w ∧ P x y) := by
  intro h
  rw [pm166_112]
  exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩

/-- ✱166·12. \(\vdash .Cʻ(P\times Q)=CʻP\times CʻQ \quad[*165·16.*166·1]\) -/
theorem pm166_12 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    fld (P ×ᵣ Q) = fld P ×ₐ fld Q := pm165_16

/-- ✱166·13. \(\vdash \colon\ldotp P\times Q=\dot{\Lambda} .=:P=\dot{\Lambda} .\lor.Q=\dot{\Lambda} \quad[*166·12.*113·114.*33·241]\)

**Status.** proved (reading): transcription error: the e-text prints `=` for the principal `≡`
(the proof `[✱166·12.✱113·114.✱33·241]` gives an equivalence). -/
theorem pm166_13 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    P ×ᵣ Q = rNull ↔ P = rNull ∨ Q = rNull := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨hP, hQ⟩ := not_or.1 hn
    have hP' : rEx P := by by_contra h'; exact hP (eq_rNull_of_not_rEx h')
    have hQ' : rEx Q := by by_contra h'; exact hQ (eq_rNull_of_not_rEx h')
    obtain ⟨x, hx⟩ := rEx_iff_fld.1 hP'
    obtain ⟨z, hz⟩ := rEx_iff_fld.1 hQ'
    have : z ↓ x ∈ fld (P ×ᵣ Q) := by rw [pm166_12]; exact couple_mem_clsTimes.2 ⟨hz, hx⟩
    rw [h, fld_rNull] at this
    simp at this
  · intro h
    apply eq_rNull_of_fld
    rw [pm166_12]
    ext X
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hX
    obtain ⟨a, b, ⟨ha, hb⟩, -⟩ := mem_clsTimes'.1 hX
    rcases h with h | h
    · rw [h, fld_rNull] at hb; simp at hb
    · rw [h, fld_rNull] at ha; simp at ha

/-- ✱166·14. \(\vdash :\dot{\exists} !P\times Q.\equiv .\dot{\exists} !P.\dot{\exists} !Q \quad[*166·13]\) -/
theorem pm166_14 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    rEx (P ×ᵣ Q) ↔ rEx P ∧ rEx Q := by
  constructor
  · intro h
    constructor
    · by_contra hP
      rw [pm166_13.2 (Or.inl (eq_rNull_of_not_rEx hP))] at h
      obtain ⟨a, b, hab⟩ := h
      exact rNull_apply a b hab
    · by_contra hQ
      rw [pm166_13.2 (Or.inr (eq_rNull_of_not_rEx hQ))] at h
      obtain ⟨a, b, hab⟩ := h
      exact rNull_apply a b hab
  · rintro ⟨hP, hQ⟩
    by_contra h
    rcases pm166_13.1 (eq_rNull_of_not_rEx h) with e | e
    · rw [e] at hP; obtain ⟨a, b, hab⟩ := hP; exact rNull_apply a b hab
    · rw [e] at hQ; obtain ⟨a, b, hab⟩ := hQ; exact rNull_apply a b hab

/-- ✱166·15. \(\vdash .\text{Cnv}ʻ(P\times Q)=\breve{P} \times \breve{Q} \quad[*165·19 . *162·2]\) -/
theorem pm166_15 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    (P ×ᵣ Q)˘ = P˘ ×ᵣ Q˘ := by
  show (relSigma (coupleSemi Q ⁏ P))˘ = relSigma (coupleSemi Q˘ ⁏ P˘)
  rw [pm162_2, pm165_18, pm165_182]

private theorem beg_rtimes {α β : Type*} (P : α → α → Prop) (Q : β → β → Prop) :
    refs Beg (P ×ᵣ Q) = refs Beg P ×ₐ refs Beg Q := by
  ext X
  rw [mem_clsTimes']
  show X ∈ dom (P ×ᵣ Q) ∧ X ∉ codom (P ×ᵣ Q) ↔ _
  constructor
  · rintro ⟨⟨N, hN⟩, hc⟩
    have hc' : ∀ M, ¬ (P ×ᵣ Q) M X := fun M hM => hc ⟨M, hM⟩
    rw [rtimes_apply] at hN
    obtain ⟨z, x, hz, hx, rfl⟩ : ∃ z x, z ∈ fld Q ∧ x ∈ fld P ∧ X = z ↓ x := by
      rcases hN with ⟨x, hx, z, w, ⟨rfl, -⟩, hzw⟩ | ⟨x, y, hxy, z, w, ⟨hz, -⟩, rfl, -⟩
      · exact ⟨z, x, mem_fld_l hzw, hx, rfl⟩
      · exact ⟨z, x, hz, mem_fld_l hxy, rfl⟩
    have hzc : z ∉ codom Q := by
      rintro ⟨w, hwz⟩
      exact hc' (w ↓ x) ((rtimes_apply P Q _ _).2 (Or.inl ⟨x, hx, w, z, ⟨rfl, rfl⟩, hwz⟩))
    have hxc : x ∉ codom P := by
      rintro ⟨y, hyx⟩
      exact hc' (z ↓ y) ((rtimes_apply P Q _ _).2 (Or.inr ⟨y, x, hyx, z, z, ⟨hz, hz⟩, rfl, rfl⟩))
    refine ⟨z, x, ⟨⟨?_, hzc⟩, ⟨?_, hxc⟩⟩, rfl⟩
    · rcases hz with ⟨w, h | h⟩
      exacts [⟨w, h⟩, absurd ⟨w, h⟩ hzc]
    · rcases hx with ⟨w, h | h⟩
      exacts [⟨w, h⟩, absurd ⟨w, h⟩ hxc]
  · rintro ⟨z, x, ⟨⟨⟨w, hzw⟩, hzc⟩, ⟨⟨y, hxy⟩, hxc⟩⟩, rfl⟩
    refine ⟨⟨z ↓ y, (rtimes_apply P Q _ _).2
      (Or.inr ⟨x, y, hxy, z, z, ⟨mem_fld_l hzw, mem_fld_l hzw⟩, rfl, rfl⟩)⟩, ?_⟩
    rintro ⟨M, hM⟩
    rw [rtimes_apply] at hM
    rcases hM with ⟨x', hx', z', w', ⟨-, e⟩, hzw'⟩ | ⟨x', y', hxy', z', w', -, -, e⟩
    · obtain ⟨e1, -⟩ := couple_eq_couple_iff.1 e
      rw [← e1] at hzw'
      exact hzc ⟨z', hzw'⟩
    · obtain ⟨-, e2⟩ := couple_eq_couple_iff.1 e
      rw [← e2] at hxy'
      exact hxc ⟨x', hxy'⟩

/-- ✱166·16. \(\vdash .\overrightarrow{B}ʻ(P\times Q)=\overrightarrow{B}ʻP\times \overrightarrow{B}ʻQ.\overrightarrow{B}ʻ\text{Cnv}ʻ(P\times Q)=\overrightarrow{B}ʻ\breve{P} \times \overrightarrow{B}ʻ\breve{Q}\) -/
theorem pm166_16 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} :
    refs Beg (P ×ᵣ Q) = refs Beg P ×ₐ refs Beg Q ∧
      refs Beg (P ×ᵣ Q)˘ = refs Beg P˘ ×ₐ refs Beg Q˘ :=
  ⟨beg_rtimes P Q, by rw [pm166_15]; exact beg_rtimes P˘ Q˘⟩

/-- ✱166·2. \[\begin{align}&\vdash :R\upharpoonright CʻPʻ\in P\,\overline{\text{smor}}\,Pʻ.\supset .(R\mid )\upharpoonright Cʻ(Q\times Pʻ)\in (Q\times P)\overline{\text{smor}} (Q\times Pʻ)\\ &[*165·36.*166·1.*164·14]\end{align}\]

The e-text prints `Pʻ` for `P'`. -/
theorem pm166_2 {α β γ : Type*} {Q : β → β → Prop} {P : γ → γ → Prop} {P' : α → α → Prop}
    {R : γ → α → Prop} :
    R ↾ fld P' ∈ smorbar P P' → relProdL R ↾ fld (Q ×ᵣ P') ∈ smorbar (Q ×ᵣ P) (Q ×ᵣ P') :=
  fun h => pm164_14 (pm165_36 h)

/-- ✱166·21. \[\begin{align}&\vdash :S\upharpoonright CʻQʻ\in Q\,\overline{\text{smor}}\,Qʻ.\supset .(\mid \breve{S} )\upharpoonright Cʻ(Qʻ\times P)\in (Q\times P)\overline{\text{smor}} (Qʻ\times P)\\ &[*165·361.*166·1.*164·14]\end{align}\]

The e-text prints `Qʻ` for `Q'`. -/
theorem pm166_21 {α β δ : Type*} {P : α → α → Prop} {Q : δ → δ → Prop} {Q' : β → β → Prop}
    {S : δ → β → Prop} :
    S ↾ fld Q' ∈ smorbar Q Q' →
      relProdR S˘ ↾ fld (Q' ×ᵣ P) ∈ smorbar (Q ×ᵣ P) (Q' ×ᵣ P) :=
  fun h => pm164_14 (pm165_361 h)

/-- ✱166·22. \[\begin{align}\vdash :R\upharpoonright CʻP'\in P\,\overline{\text{smor}}\,P'.&S\upharpoonright CʻQ'\in Q\overline{\text{smor}} Q'.\supset .\\ &(R\parallel \breve{S} )\upharpoonright Cʻ(Q'\times P')\in (Q\times P)\,\overline{\text{smor}}\,(Q'\times P')\\ [*165·362.*166·1.*164·14]\end{align}\] -/
theorem pm166_22 {α β γ δ : Type*} {P : γ → γ → Prop} {P' : α → α → Prop} {Q : δ → δ → Prop}
    {Q' : β → β → Prop} {R : γ → α → Prop} {S : δ → β → Prop} :
    R ↾ fld P' ∈ smorbar P P' ∧ S ↾ fld Q' ∈ smorbar Q Q' →
      (R ∥ S˘) ↾ fld (Q' ×ᵣ P') ∈ smorbar (Q ×ᵣ P) (Q' ×ᵣ P') :=
  fun h => pm164_14 (pm165_362 h)

/-- ✱166·23. \[\begin{align}&\vdash :P \,\text{smor} P'.Q \text{smor} Q'.\supset .Q\times P \,\text{smor} \,Q'\times P'\\ &[*166·22.*151·12]\end{align}\] -/
theorem pm166_23 {α β γ δ : Type*} {P : γ → γ → Prop} {P' : α → α → Prop} {Q : δ → δ → Prop}
    {Q' : β → β → Prop} :
    smor P P' ∧ smor Q Q' → smor (Q ×ᵣ P) (Q' ×ᵣ P') :=
  fun h => (pm164_151 (pm165_37 h)).1

/-- ✱166·24. \[\begin{align}&\vdash \colon\ldotp \text{Mult ax}.\supset :R\in \text{Rel}^{2}\text{excl}\cap \text{Nr}ʻQ.CʻR\subset \text{Nr}ʻP.\supset .\\ &\Sigma ʻR\,\text{smor}\,Q\times P \quad[*165·38.*164·151.*166·1]\end{align}\] -/
theorem pm166_24 {α β γ : Type*} {P : α → α → Prop} {Q : β → β → Prop}
    {R : (γ → γ → Prop) → (γ → γ → Prop) → Prop} :
    MultAx (γ → (α → β → Prop) → Prop) →
      (R ∈ Rel2excl ∩ nr (γ → γ → Prop) Q ∧ fld R ⊆ nr γ P → smor (relSigma R) (Q ×ᵣ P)) :=
  fun hM h => (pm164_151 (pm165_38 hM h)).1

/-- ✱166·3. \[\begin{align}&\vdash :\exists !Cʻ(P\times Q)\cap Cʻ(Pʻ\times Qʻ).\equiv .\exists !CʻP\cap CʻPʻ.\exists !CʻQ\cap CʻQʻ\\ &[*166·12.*113·19]\end{align}\]

The e-text prints `Pʻ`, `Qʻ` for `P'`, `Q'`. -/
theorem pm166_3 {α β : Type*} {P P' : α → α → Prop} {Q Q' : β → β → Prop} :
    (fld (P ×ᵣ Q) ∩ fld (P' ×ᵣ Q')).Nonempty ↔
      (fld P ∩ fld P').Nonempty ∧ (fld Q ∩ fld Q').Nonempty := by
  rw [pm166_12, pm166_12]
  constructor
  · rintro ⟨X, h1, h2⟩
    obtain ⟨z, x, ⟨hz, hx⟩, rfl⟩ := mem_clsTimes'.1 h1
    obtain ⟨z', x', ⟨hz', hx'⟩, e⟩ := mem_clsTimes'.1 h2
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    exact ⟨⟨x, hx, hx'⟩, ⟨z, hz, hz'⟩⟩
  · rintro ⟨⟨x, hx, hx'⟩, ⟨z, hz, hz'⟩⟩
    exact ⟨z ↓ x, couple_mem_clsTimes.2 ⟨hz, hx⟩, couple_mem_clsTimes.2 ⟨hz', hx'⟩⟩

/-- ✱166·31. \(\vdash .\dot{s} ʻCʻ(Q\times P)=CʻP\uparrow CʻQ \quad[*113·115.*166·12]\) -/
theorem pm166_31 {α β : Type*} {Q : β → β → Prop} {P : α → α → Prop} :
    sumRel (fld (Q ×ᵣ P)) = cross (fld P) (fld Q) := by
  rw [show fld (Q ×ᵣ P) = fld Q ×ₐ fld P from pm165_16]
  refine rel_ext' fun a b => ?_
  constructor
  · rintro ⟨X, hX, h⟩
    obtain ⟨x, z, ⟨hx, hz⟩, rfl⟩ := mem_clsTimes'.1 hX
    rw [couple_apply] at h
    rw [h.1, h.2]; exact ⟨hx, hz⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a ↓ b, couple_mem_clsTimes.2 ⟨ha, hb⟩, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩⟩

/-- ✱166·311. \[\begin{align}&\vdash :\dot{\exists} !Q.\supset .sʻ\text{D}ʻʻCʻ(Q\times P)=CʻP:\dot{\exists} !P.\supset .sʻ\text{ᗡ}ʻʻCʻ(Q\times P)=CʻQ\\ &[*113·116.*166·12.*33·24]\end{align}\]

The colon makes a product of the two implications. -/
theorem pm166_311 {α β : Type*} {Q : β → β → Prop} {P : α → α → Prop} :
    (rEx Q → sumCls (D ʻʻ fld (Q ×ᵣ P)) = fld P) ∧
      (rEx P → sumCls (Dcnv ʻʻ fld (Q ×ᵣ P)) = fld Q) := by
  have hf : fld (Q ×ᵣ P) = fld Q ×ₐ fld P := pm165_16
  constructor
  · intro hQ
    ext x
    show x ∈ sumCls (graph dom ʻʻ fld (Q ×ᵣ P)) ↔ x ∈ fld P
    rw [mem_sumCls_graph_img, hf]
    constructor
    · rintro ⟨X, hX, ⟨w, hxw⟩⟩
      obtain ⟨a, z, ⟨ha, -⟩, rfl⟩ := mem_clsTimes'.1 hX
      rw [couple_apply] at hxw
      rw [hxw.1]; exact ha
    · intro hx
      obtain ⟨z, hz⟩ := rEx_iff_fld.1 hQ
      exact ⟨x ↓ z, couple_mem_clsTimes.2 ⟨hx, hz⟩, ⟨z, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩⟩⟩
  · intro hP
    ext z
    show z ∈ sumCls (graph codom ʻʻ fld (Q ×ᵣ P)) ↔ z ∈ fld Q
    rw [mem_sumCls_graph_img, hf]
    constructor
    · rintro ⟨X, hX, ⟨a, hxz⟩⟩
      obtain ⟨x, w, ⟨-, hw⟩, rfl⟩ := mem_clsTimes'.1 hX
      rw [couple_apply] at hxz
      rw [hxz.2]; exact hw
    · intro hz
      obtain ⟨x, hx⟩ := rEx_iff_fld.1 hP
      exact ⟨x ↓ z, couple_mem_clsTimes.2 ⟨hx, hz⟩, ⟨x, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩⟩⟩

/-- ✱166·312. \[\begin{align}&\vdash .sʻ\text{D}ʻʻCʻ(Q\times P)\subset CʻP.sʻ\text{ᗡ}ʻʻCʻ(Q\times P)\subset CʻQ\\ &[*113·118.*166·12]\end{align}\] -/
theorem pm166_312 {α β : Type*} {Q : β → β → Prop} {P : α → α → Prop} :
    sumCls (D ʻʻ fld (Q ×ᵣ P)) ⊆ fld P ∧ sumCls (Dcnv ʻʻ fld (Q ×ᵣ P)) ⊆ fld Q := by
  have hf : fld (Q ×ᵣ P) = fld Q ×ₐ fld P := pm165_16
  constructor
  · intro x hx
    have hx' : x ∈ sumCls (graph dom ʻʻ fld (Q ×ᵣ P)) := hx
    rw [mem_sumCls_graph_img, hf] at hx'
    obtain ⟨X, hX, ⟨w, hxw⟩⟩ := hx'
    obtain ⟨a, z, ⟨ha, -⟩, rfl⟩ := mem_clsTimes'.1 hX
    rw [couple_apply] at hxw
    rw [hxw.1]; exact ha
  · intro z hz
    have hz' : z ∈ sumCls (graph codom ʻʻ fld (Q ×ᵣ P)) := hz
    rw [mem_sumCls_graph_img, hf] at hz'
    obtain ⟨X, hX, ⟨a, hxz⟩⟩ := hz'
    obtain ⟨x, w, ⟨-, hw⟩, rfl⟩ := mem_clsTimes'.1 hX
    rw [couple_apply] at hxz
    rw [hxz.2]; exact hw

/-- ✱166·4. \[\begin{align}\vdash \colon\ldotp M \{(P \times Q) \times R\} &M'. \equiv : (\exists x, y, z, x', y', z') :\\ &x, x' \in CʻP . y, y' \in CʻQ . z, z' \in CʻR :\\ &xPx' . \lor . x = x' . yQy'. \lor . x = x' . y = yʻ . zRz' :\\ &M = z \downarrow (y \downarrow x) . M' = z' \downarrow (y' \downarrow x')\end{align}\]

The three factors after `(∃x, y, z, x', y', z')` are separated by colons; `x, x' ∈ C'P` etc. are
conjunctions and the disjunction is bracketed to the left (✱2·33). -/
theorem pm166_4 {α β γ : Type*} {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop}
    {M M' : γ → (β → α → Prop) → Prop} :
    ((P ×ᵣ Q) ×ᵣ R) M M' ↔
      ∃ x y z x' y' z', ((((x ∈ fld P ∧ x' ∈ fld P) ∧ (y ∈ fld Q ∧ y' ∈ fld Q)) ∧
        (z ∈ fld R ∧ z' ∈ fld R)) ∧
          ((P x x' ∨ x = x' ∧ Q y y') ∨ (x = x' ∧ y = y') ∧ R z z')) ∧
        (M = z ↓ (y ↓ x) ∧ M' = z' ↓ (y' ↓ x')) := by
  rw [pm166_111]
  constructor
  · rintro ⟨N, N', z, z', ⟨⟨⟨hN, hN'⟩, ⟨hz, hz'⟩⟩, h⟩, rfl, rfl⟩
    rw [pm166_12] at hN hN'
    obtain ⟨y, x, ⟨hy, hx⟩, rfl⟩ := mem_clsTimes'.1 hN
    obtain ⟨y', x', ⟨hy', hx'⟩, rfl⟩ := mem_clsTimes'.1 hN'
    refine ⟨x, y, z, x', y', z', ⟨⟨⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩, ⟨hz, hz'⟩⟩, ?_⟩, rfl, rfl⟩
    rcases h with h | ⟨e, hzz⟩
    · rw [pm166_112] at h
      exact Or.inl h.2
    · obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
      exact Or.inr ⟨⟨rfl, rfl⟩, hzz⟩
  · rintro ⟨x, y, z, x', y', z', ⟨⟨⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩, ⟨hz, hz'⟩⟩, h⟩, rfl, rfl⟩
    refine ⟨y ↓ x, y' ↓ x', z, z', ⟨⟨⟨?_, ?_⟩, ⟨hz, hz'⟩⟩, ?_⟩, rfl, rfl⟩
    · rw [pm166_12]; exact couple_mem_clsTimes.2 ⟨hy, hx⟩
    · rw [pm166_12]; exact couple_mem_clsTimes.2 ⟨hy', hx'⟩
    · rcases h with h | ⟨⟨rfl, rfl⟩, hzz⟩
      · exact Or.inl (pm166_112.2 ⟨⟨⟨hy, hy'⟩, ⟨hx, hx'⟩⟩, h⟩)
      · exact Or.inr ⟨rfl, hzz⟩

/-- ✱166·401. \[\begin{align}\vdash \colon\ldotp N \{P \times (Q \times R)\} &N'. \equiv : (\exists x, x', y, y', z, z') :\\ &x, x' \in CʻP . y, y' \in CʻQ . z, z' \in CʻR :\\ &xPx' . \lor . x = x' . yQy' . \lor . x = x' . y = y' . zRz' :\\ &N = (z \downarrow y) \downarrow x . N' = (z' \downarrow y') \downarrow xʻ \quad[\text{Proof as in *166·4}]\end{align}\]

The e-text prints `xʻ` for `x'`. -/
theorem pm166_401 {α β γ : Type*} {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop}
    {N N' : (γ → β → Prop) → α → Prop} :
    (P ×ᵣ (Q ×ᵣ R)) N N' ↔
      ∃ x x' y y' z z', ((((x ∈ fld P ∧ x' ∈ fld P) ∧ (y ∈ fld Q ∧ y' ∈ fld Q)) ∧
        (z ∈ fld R ∧ z' ∈ fld R)) ∧
          ((P x x' ∨ x = x' ∧ Q y y') ∨ (x = x' ∧ y = y') ∧ R z z')) ∧
        (N = (z ↓ y) ↓ x ∧ N' = (z' ↓ y') ↓ x') := by
  rw [pm166_111]
  constructor
  · rintro ⟨x, x', K, K', ⟨⟨⟨hx, hx'⟩, ⟨hK, hK'⟩⟩, h⟩, rfl, rfl⟩
    rw [pm166_12] at hK hK'
    obtain ⟨z, y, ⟨hz, hy⟩, rfl⟩ := mem_clsTimes'.1 hK
    obtain ⟨z', y', ⟨hz', hy'⟩, rfl⟩ := mem_clsTimes'.1 hK'
    refine ⟨x, x', y, y', z, z', ⟨⟨⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩, ⟨hz, hz'⟩⟩, ?_⟩, rfl, rfl⟩
    rcases h with h | ⟨e, h⟩
    · exact Or.inl (Or.inl h)
    · rw [pm166_112] at h
      rcases h.2 with h2 | ⟨e2, h2⟩
      · exact Or.inl (Or.inr ⟨e, h2⟩)
      · exact Or.inr ⟨⟨e, e2⟩, h2⟩
  · rintro ⟨x, x', y, y', z, z', ⟨⟨⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩, ⟨hz, hz'⟩⟩, h⟩, rfl, rfl⟩
    refine ⟨x, x', z ↓ y, z' ↓ y', ⟨⟨⟨hx, hx'⟩, ⟨?_, ?_⟩⟩, ?_⟩, rfl, rfl⟩
    · rw [pm166_12]; exact couple_mem_clsTimes.2 ⟨hz, hy⟩
    · rw [pm166_12]; exact couple_mem_clsTimes.2 ⟨hz', hy'⟩
    · rcases h with (h | ⟨e, h⟩) | ⟨⟨e, e2⟩, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, pm166_112.2 ⟨⟨⟨hz, hz'⟩, ⟨hy, hy'⟩⟩, Or.inl h⟩⟩
      · exact Or.inr ⟨e, pm166_112.2 ⟨⟨⟨hz, hz'⟩, ⟨hy, hy'⟩⟩, Or.inr ⟨e2, h⟩⟩⟩

/-- ✱166·41. \[\begin{align}\vdash : T = \hat{M} \hat{N} &\{(\exists x, y, z) . x \in CʻP . y \in CʻQ . z \in CʻR . M = z \downarrow (y \downarrow x)\}.\\ &N = \{(z \downarrow y) \downarrow x\} . \supset . T \in \{(P \times Q) \times R\} \overline{\text{smor}} \{P \times (Q \times R)\}\end{align}\]

**Status.** proved (reading): transcription error: the e-text's braces are misplaced
(`M̂N̂{(∃x, y, z) . … . M = z↓(y↓x)} . N = {(z↓y)↓x}`); PM's correlator is
`M̂N̂{(∃x, y, z) . x ∈ C'P . y ∈ C'Q . z ∈ C'R . M = z↓(y↓x) . N = (z↓y)↓x}` (the proof uses
`MTN . ≡ . (∃x, y, z) . … . M = z↓(y↓x) . N = (z↓y)↓x`), a product of five bracketed to the left. -/
theorem pm166_41 {α β γ : Type*} {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop}
    {T : (γ → (β → α → Prop) → Prop) → ((γ → β → Prop) → α → Prop) → Prop} :
    T = (fun M N => ∃ x y z, ((((x ∈ fld P ∧ y ∈ fld Q) ∧ z ∈ fld R) ∧ M = z ↓ (y ↓ x)) ∧
        N = (z ↓ y) ↓ x)) →
      T ∈ smorbar ((P ×ᵣ Q) ×ᵣ R) (P ×ᵣ (Q ×ᵣ R)) := by
  rintro rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [oneone_iff]
    refine ⟨?_, ?_⟩
    · rintro M M' N ⟨⟨x, y, z, ⟨-, rfl⟩, rfl⟩, ⟨x', y', z', ⟨-, rfl⟩, e⟩⟩
      obtain ⟨e1, e2⟩ := couple_eq_couple_iff.1 e
      obtain ⟨e3, e4⟩ := couple_eq_couple_iff.1 e1
      rw [e2, e3, e4]
    · rintro M N N' ⟨⟨x, y, z, ⟨-, rfl⟩, rfl⟩, ⟨x', y', z', ⟨-, e⟩, rfl⟩⟩
      obtain ⟨e1, e2⟩ := couple_eq_couple_iff.1 e
      obtain ⟨e3, e4⟩ := couple_eq_couple_iff.1 e2
      rw [e1, e3, e4]
  · ext N
    rw [show fld (P ×ᵣ (Q ×ᵣ R)) = fld P ×ₐ fld (Q ×ᵣ R) from pm165_16, mem_clsTimes']
    constructor
    · rintro ⟨K, x, ⟨hK, hx⟩, rfl⟩
      rw [show fld (Q ×ᵣ R) = fld Q ×ₐ fld R from pm165_16, mem_clsTimes'] at hK
      obtain ⟨z, y, ⟨hz, hy⟩, rfl⟩ := hK
      exact ⟨z ↓ (y ↓ x), x, y, z, ⟨⟨⟨hx, hy⟩, hz⟩, rfl⟩, rfl⟩
    · rintro ⟨M, x, y, z, ⟨⟨⟨hx, hy⟩, hz⟩, -⟩, rfl⟩
      refine ⟨z ↓ y, x, ⟨?_, hx⟩, rfl⟩
      rw [show fld (Q ×ᵣ R) = fld Q ×ₐ fld R from pm165_16]
      exact couple_mem_clsTimes.2 ⟨hz, hy⟩
  · refine rel_ext' fun M M' => ?_
    rw [pm166_4, semi_iff']
    constructor
    · rintro ⟨x, y, z, x', y', z', ⟨hf, h⟩, rfl, rfl⟩
      obtain ⟨⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩, ⟨hz, hz'⟩⟩ := hf
      refine ⟨(z ↓ y) ↓ x, (z' ↓ y') ↓ x', ⟨x, y, z, ⟨⟨⟨hx, hy⟩, hz⟩, rfl⟩, rfl⟩,
        ⟨x', y', z', ⟨⟨⟨hx', hy'⟩, hz'⟩, rfl⟩, rfl⟩, ?_⟩
      exact pm166_401.2 ⟨x, x', y, y', z, z', ⟨⟨⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩, ⟨hz, hz'⟩⟩, h⟩, rfl, rfl⟩
    · rintro ⟨N, N', ⟨x, y, z, ⟨⟨⟨hx, hy⟩, hz⟩, rfl⟩, rfl⟩,
        ⟨x', y', z', ⟨⟨⟨hx', hy'⟩, hz'⟩, rfl⟩, rfl⟩, hNN⟩
      obtain ⟨a, a', b, b', c, c', ⟨-, h⟩, e1, e2⟩ := pm166_401.1 hNN
      obtain ⟨e11, e12⟩ := couple_eq_couple_iff.1 e1
      obtain ⟨e13, e14⟩ := couple_eq_couple_iff.1 e11
      obtain ⟨e21, e22⟩ := couple_eq_couple_iff.1 e2
      obtain ⟨e23, e24⟩ := couple_eq_couple_iff.1 e21
      rw [← e12, ← e22, ← e13, ← e23, ← e14, ← e24] at h
      exact ⟨x, y, z, x', y', z', ⟨⟨⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩, ⟨hz, hz'⟩⟩, h⟩, rfl, rfl⟩

/-- ✱166·42. \(\vdash . (P \times Q) \times R \text{smor} P \times (Q \times R) \quad[*166·41]\) -/
theorem pm166_42 {α β γ : Type*} {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop} :
    smor ((P ×ᵣ Q) ×ᵣ R) (P ×ᵣ (Q ×ᵣ R)) :=
  ⟨_, pm166_41 rfl⟩

/-- ✱166·421 (Df). \(P \times Q \times R = (P \times Q) \times R \quad\text{Df}\) -/
theorem pm166_421 {α β γ : Type*} {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop} :
    P ×ᵣ Q ×ᵣ R = (P ×ᵣ Q) ×ᵣ R := rfl

/-- ✱166·44. \(\vdash . \Sigma ʻ \times P^{;}Q = (\Sigma ʻQ) \times P\)

`×P` is the relation `opR rtimes P` (✱38·02); `Σ'×P;Q` is `Σ'(×P;Q)` (✱150·04). -/
theorem pm166_44 {α β : Type*} {P : α → α → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    relSigma (opR rtimes P ⁏ Q) = relSigma Q ×ᵣ P := by
  have hf : fld (opR rtimes P ⁏ Q) = opR rtimes P ʻʻ fld Q := fld_semi_graph _ _
  have hfM : ∀ M : β → β → Prop, fld (M ×ᵣ P) = fld M ×ₐ fld P := fun M => pm165_16
  refine rel_ext' fun X Y => ?_
  rw [relSigma_apply, hf, rtimes_apply]
  constructor
  · rintro (⟨T, ⟨M, hM, rfl⟩, h⟩ | ⟨T, T', ⟨hX, hY⟩, h⟩)
    · rw [rtimes_apply] at h
      rcases h with ⟨z, hz, x, y, hxy, h⟩ | ⟨z, w, hzw, x, y, hxy, hX, hY⟩
      · exact Or.inl ⟨z, mem_fld_relSigma.2 ⟨M, hM, hz⟩, x, y, hxy, h⟩
      · exact Or.inr ⟨z, w, (relSigma_apply Q z w).2 (Or.inl ⟨M, hM, hzw⟩), x, y, hxy, hX, hY⟩
    · obtain ⟨M, N, ⟨rfl, rfl⟩, hMN⟩ := (semi_graph_apply _ _ _ _).1 h
      rw [hfM, mem_clsTimes'] at hX hY
      obtain ⟨x, z, ⟨hx, hz⟩, rfl⟩ := hX
      obtain ⟨y, w, ⟨hy, hw⟩, rfl⟩ := hY
      exact Or.inr ⟨z, w, (relSigma_apply Q z w).2 (Or.inr ⟨M, N, ⟨hz, hw⟩, hMN⟩), x, y, ⟨hx, hy⟩,
        rfl, rfl⟩
  · rintro (⟨z, hz, x, y, hxy, h⟩ | ⟨z, w, hzw, x, y, hxy, rfl, rfl⟩)
    · obtain ⟨M, hM, hzM⟩ := mem_fld_relSigma.1 hz
      exact Or.inl ⟨M ×ᵣ P, ⟨M, hM, rfl⟩, (rtimes_apply M P X Y).2 (Or.inl ⟨z, hzM, x, y, hxy, h⟩)⟩
    · rcases (relSigma_apply Q z w).1 hzw with ⟨M, hM, h⟩ | ⟨M, N, ⟨hz, hw⟩, hMN⟩
      · exact Or.inl ⟨M ×ᵣ P, ⟨M, hM, rfl⟩,
          (rtimes_apply M P _ _).2 (Or.inr ⟨z, w, h, x, y, hxy, rfl, rfl⟩)⟩
      · refine Or.inr ⟨M ×ᵣ P, N ×ᵣ P, ⟨?_, ?_⟩,
          (semi_graph_apply _ _ _ _).2 ⟨M, N, ⟨rfl, rfl⟩, hMN⟩⟩
        · rw [hfM]; exact couple_mem_clsTimes.2 ⟨hxy.1, hz⟩
        · rw [hfM]; exact couple_mem_clsTimes.2 ⟨hxy.2, hw⟩

/-- ✱166·45. \(\vdash . (Q \unicode{x2909} R) \times P = (Q \times P) \unicode{x2909} (R \times P)\) -/
theorem pm166_45 {α β : Type*} {Q R : β → β → Prop} {P : α → α → Prop} :
    (Q ⤉ R) ×ᵣ P = (Q ×ᵣ P) ⤉ (R ×ᵣ P) := by
  show relSigma (coupleSemi P ⁏ (Q ⤉ R)) = relSigma (coupleSemi P ⁏ Q) ⤉ relSigma (coupleSemi P ⁏ R)
  rw [pm162_31, pm162_36 (R := coupleSemi P) (P := Q) (Q := R) (fun _ _ => ⟨_, rfl⟩)]

/-- ✱166·46. \(\vdash . (P \unicode{x228d} Q) \downarrow_{.,} z = P \downarrow_{.,} z \unicode{x228d} Q \downarrow_{.,} z \quad[*165·01 . *150·3]\)

`(P ∪̇ Q)↓., z` is `opSemi couple (P ⊍ Q) z`. -/
theorem pm166_46 {α β : Type*} {P Q : α → α → Prop} {z : β} :
    opSemi couple (P ⊍ Q) z = opSemi couple P z ⊍ opSemi couple Q z :=
  semi_rcup _ _ _

/-- ✱166·461. \[\begin{align}&\vdash . \dot{s} ʻCʻ(P \unicode{x228d} Q) \downarrow_{.,} ^{;}R = \dot{s} ʻCʻP \downarrow_{.,} ^{;}R \unicode{x228d} \dot{s} ʻCʻQ \downarrow_{.,} ^{;}R\\ &[*41·6 . *165·12 . *166·46]\end{align}\]

`ṡ'C'(P ∪̇ Q)↓.,;R` is `ṡ'C'((P ∪̇ Q)↓.,;R)`. -/
theorem pm166_461 {α β : Type*} {P Q : α → α → Prop} {R : β → β → Prop} :
    sumRel (fld (coupleSemi (P ⊍ Q) ⁏ R)) =
      sumRel (fld (coupleSemi P ⁏ R)) ⊍ sumRel (fld (coupleSemi Q ⁏ R)) := by
  refine rel_ext' fun M N => ?_
  constructor
  · rintro ⟨T, hT, h⟩
    obtain ⟨z, hz, rfl⟩ := mem_fld_coupleSemi_semi.1 hT
    rw [pm166_46] at h
    rcases h with h | h
    · exact Or.inl ⟨_, mem_fld_coupleSemi_semi.2 ⟨z, hz, rfl⟩, h⟩
    · exact Or.inr ⟨_, mem_fld_coupleSemi_semi.2 ⟨z, hz, rfl⟩, h⟩
  · rintro (⟨T, hT, h⟩ | ⟨T, hT, h⟩)
    · obtain ⟨z, hz, rfl⟩ := mem_fld_coupleSemi_semi.1 hT
      exact ⟨_, mem_fld_coupleSemi_semi.2 ⟨z, hz, rfl⟩, by rw [pm166_46]; exact Or.inl h⟩
    · obtain ⟨z, hz, rfl⟩ := mem_fld_coupleSemi_semi.1 hT
      exact ⟨_, mem_fld_coupleSemi_semi.2 ⟨z, hz, rfl⟩, by rw [pm166_46]; exact Or.inr h⟩

/-- ✱166·462. \[\begin{align}&\vdash .F^{;}(P\unicode{x228d} Q)\downarrow_{.,} ^{;}R=F^{;}P\downarrow_{.,} ^{;}R\unicode{x228d} F^{;}Q\downarrow_{.,} ^{;}R\unicode{x228d} \hat{M} \hat{N} \{(\exists x,y,z,w):\\ &zRw:x\in CʻP.y\in CʻQ.\lor.x\in CʻQ.y\in CʻP:M=x\downarrow z.N=y\downarrow w\}\end{align}\]

`F;(P ∪̇ Q)↓.,;R` is `F;((P ∪̇ Q)↓.,;R)`; the relation `M̂N̂{…}` is written as a `fun`. -/
theorem pm166_462 {α β : Type*} {P Q : α → α → Prop} {R : β → β → Prop} :
    F ⁏ coupleSemi (P ⊍ Q) ⁏ R =
      F ⁏ coupleSemi P ⁏ R ⊍ F ⁏ coupleSemi Q ⁏ R ⊍
        (fun M N => ∃ x y z w, (R z w ∧ (x ∈ fld P ∧ y ∈ fld Q ∨ x ∈ fld Q ∧ y ∈ fld P)) ∧
          (M = x ↓ z ∧ N = y ↓ w)) := by
  refine rel_ext' fun M N => ?_
  rw [rcup_apply', rcup_apply', pm165_161, pm165_161, pm165_161, fld_rcup]
  constructor
  · rintro ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, rfl⟩, rfl⟩
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (Or.inl ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, rfl⟩, rfl⟩)
    · exact Or.inr ⟨x, y, z, w, ⟨hzw, Or.inl ⟨hx, hy⟩⟩, rfl, rfl⟩
    · exact Or.inr ⟨x, y, z, w, ⟨hzw, Or.inr ⟨hx, hy⟩⟩, rfl, rfl⟩
    · exact Or.inl (Or.inr ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, rfl⟩, rfl⟩)
  · rintro ((⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, rfl⟩, rfl⟩ | ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, rfl⟩, rfl⟩) |
      ⟨x, y, z, w, ⟨hzw, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩, rfl, rfl⟩)
    · exact ⟨x, y, z, w, ⟨⟨⟨Or.inl hx, Or.inl hy⟩, hzw⟩, rfl⟩, rfl⟩
    · exact ⟨x, y, z, w, ⟨⟨⟨Or.inr hx, Or.inr hy⟩, hzw⟩, rfl⟩, rfl⟩
    · exact ⟨x, y, z, w, ⟨⟨⟨Or.inl hx, Or.inr hy⟩, hzw⟩, rfl⟩, rfl⟩
    · exact ⟨x, y, z, w, ⟨⟨⟨Or.inr hx, Or.inl hy⟩, hzw⟩, rfl⟩, rfl⟩

/-- ✱166·463. \(\vdash :CʻP\subset CʻQ.\supset .F^{;}P\downarrow_{.,} ^{;}R\,\unicode{x2abd}\, F^{;}Q\downarrow_{.,} ^{;}R \quad[*165·161]\) -/
theorem pm166_463 {α β : Type*} {P Q : α → α → Prop} {R : β → β → Prop} :
    fld P ⊆ fld Q → F ⁏ coupleSemi P ⁏ R ⪽ F ⁏ coupleSemi Q ⁏ R := by
  intro h M N hMN
  rw [pm165_161] at hMN ⊢
  obtain ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, hM⟩, hN⟩ := hMN
  exact ⟨x, y, z, w, ⟨⟨⟨h hx, h hy⟩, hzw⟩, hM⟩, hN⟩

/-- ✱166·464. \(\vdash :CʻP\subset CʻQ.\supset .F^{;}(P\unicode{x228d} Q)\downarrow_{.,} ^{;}R=F^{;}Q\downarrow_{.,} ^{;}R=F^{;}P\downarrow_{.,} ^{;}R\unicode{x228d} F^{;}Q\downarrow_{.,} ^{;}R\)

The chain is the conjunction of its links. -/
theorem pm166_464 {α β : Type*} {P Q : α → α → Prop} {R : β → β → Prop} :
    fld P ⊆ fld Q →
      F ⁏ coupleSemi (P ⊍ Q) ⁏ R = F ⁏ coupleSemi Q ⁏ R ∧
        F ⁏ coupleSemi Q ⁏ R = F ⁏ coupleSemi P ⁏ R ⊍ F ⁏ coupleSemi Q ⁏ R := by
  intro h
  constructor
  · refine rel_ext' fun M N => ?_
    rw [pm165_161, pm165_161, fld_rcup, Set.union_eq_right.2 h]
  · exact rel_ext' fun M N => ⟨Or.inr, fun h' => h'.elim (pm166_463 h M N) id⟩

/-- ✱166·47. \[\begin{align}&\vdash .R\times (P\unicode{x228d} Q)=(R\times P)\unicode{x228d} (R\times Q)\unicode{x228d} \hat{M} \hat{N} \{(\exists x,y,z,w):\\ &x\in CʻP.y\in CʻQ.\lor.x\in CʻQ.y\in CʻP:zRw.M=x\downarrow z.N=y\downarrow w\}\\ &[*166·461·462·1.*162·1]\end{align}\]

The relation `M̂N̂{…}` is written as a `fun`; inside it, the colon makes
`zRw . M = x↓z . N = y↓w` (a product of three) the second factor. -/
theorem pm166_47 {α β : Type*} {R : β → β → Prop} {P Q : α → α → Prop} :
    R ×ᵣ (P ⊍ Q) =
      R ×ᵣ P ⊍ R ×ᵣ Q ⊍
        (fun M N => ∃ x y z w, (x ∈ fld P ∧ y ∈ fld Q ∨ x ∈ fld Q ∧ y ∈ fld P) ∧
          ((R z w ∧ M = x ↓ z) ∧ N = y ↓ w)) := by
  refine rel_ext' fun M N => ?_
  rw [rcup_apply', rcup_apply', pm166_11, pm166_11, pm166_11, fld_rcup]
  constructor
  · rintro ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, h⟩, rfl, rfl⟩
    rcases h with hzw | ⟨e, hxy | hxy⟩
    · rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (Or.inl ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, Or.inl hzw⟩, rfl, rfl⟩)
      · exact Or.inr ⟨x, y, z, w, Or.inl ⟨hx, hy⟩, ⟨hzw, rfl⟩, rfl⟩
      · exact Or.inr ⟨x, y, z, w, Or.inr ⟨hx, hy⟩, ⟨hzw, rfl⟩, rfl⟩
      · exact Or.inl (Or.inr ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, Or.inl hzw⟩, rfl, rfl⟩)
    · exact Or.inl (Or.inl ⟨x, y, z, w, ⟨⟨⟨mem_fld_l hxy, mem_fld_r hxy⟩, ⟨hz, hw⟩⟩,
        Or.inr ⟨e, hxy⟩⟩, rfl, rfl⟩)
    · exact Or.inl (Or.inr ⟨x, y, z, w, ⟨⟨⟨mem_fld_l hxy, mem_fld_r hxy⟩, ⟨hz, hw⟩⟩,
        Or.inr ⟨e, hxy⟩⟩, rfl, rfl⟩)
  · rintro ((⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, h⟩, rfl, rfl⟩ |
      ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, h⟩, rfl, rfl⟩) | ⟨x, y, z, w, hxy, ⟨h, rfl⟩, rfl⟩)
    · refine ⟨x, y, z, w, ⟨⟨⟨Or.inl hx, Or.inl hy⟩, hzw⟩, ?_⟩, rfl, rfl⟩
      rcases h with h | ⟨e, h⟩
      exacts [Or.inl h, Or.inr ⟨e, Or.inl h⟩]
    · refine ⟨x, y, z, w, ⟨⟨⟨Or.inr hx, Or.inr hy⟩, hzw⟩, ?_⟩, rfl, rfl⟩
      rcases h with h | ⟨e, h⟩
      exacts [Or.inl h, Or.inr ⟨e, Or.inr h⟩]
    · refine ⟨x, y, z, w, ⟨⟨?_, ⟨mem_fld_l h, mem_fld_r h⟩⟩, Or.inl h⟩, rfl, rfl⟩
      rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      exacts [⟨Or.inl hx, Or.inr hy⟩, ⟨Or.inr hx, Or.inl hy⟩]

/-- ✱166·471. \[\begin{align}&\vdash :CʻP\subset CʻQ.\supset .R\times (P\unicode{x228d} Q)=(R\times P)\unicode{x228d} (R\times Q)\\ &[*166·461·464]\end{align}\] -/
theorem pm166_471 {α β : Type*} {R : β → β → Prop} {P Q : α → α → Prop} :
    fld P ⊆ fld Q → R ×ᵣ (P ⊍ Q) = R ×ᵣ P ⊍ R ×ᵣ Q := by
  intro hPQ
  rw [pm166_47]
  refine rel_ext' fun M N => ⟨fun h => h.elim id fun h => Or.inr ?_, Or.inl⟩
  obtain ⟨x, y, z, w, hxy, ⟨hzw, rfl⟩, rfl⟩ := h
  have hx : x ∈ fld Q := by rcases hxy with ⟨hx, -⟩ | ⟨hx, -⟩; exacts [hPQ hx, hx]
  have hy : y ∈ fld Q := by rcases hxy with ⟨-, hy⟩ | ⟨-, hy⟩; exacts [hy, hPQ hy]
  exact pm166_11.2 ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, ⟨mem_fld_l hzw, mem_fld_r hzw⟩⟩, Or.inl hzw⟩, rfl, rfl⟩

/-- ✱166·472. \(\vdash .R\times (P\unicode{x2909}Q)=(R\times P)\unicode{x228d} (R\times Q)\unicode{x228d} R\times (CʻP\downarrow CʻQ)\)

**Status.** proved (reading): transcription error: the e-text prints `R × (C'P ↓ C'Q)`, which is
not significant (`C'P ↓ C'Q` is a couple of classes, not a relation of the type of `P`); the
proof (`✱166·471 . ✱35·85 …`, `R × (C'P ↑ C'Q)`) has `C'P ↑ C'Q`. -/
theorem pm166_472 {α β : Type*} {R : β → β → Prop} {P Q : α → α → Prop} :
    R ×ᵣ (P ⤉ Q) = R ×ᵣ P ⊍ R ×ᵣ Q ⊍ R ×ᵣ cross (fld P) (fld Q) := by
  refine rel_ext' fun M N => ?_
  rw [rcup_apply', rcup_apply', pm166_11, pm166_11, pm166_11, pm166_11, fld_rsum]
  constructor
  · rintro ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, h⟩, rfl, rfl⟩
    have mixed : ∀ x y, x ∈ fld P → y ∈ fld Q → x ∈ fld (cross (fld P) (fld Q)) ∧
        y ∈ fld (cross (fld P) (fld Q)) := fun x y hx hy => by
      rw [fld_cross ⟨x, hx⟩ ⟨y, hy⟩]; exact ⟨Or.inl hx, Or.inr hy⟩
    rcases h with hzw | ⟨e, (hxy | hxy) | ⟨hx', hy'⟩⟩
    · rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (Or.inl ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, Or.inl hzw⟩, rfl, rfl⟩)
      · exact Or.inr ⟨x, y, z, w, ⟨⟨mixed x y hx hy, ⟨hz, hw⟩⟩, Or.inl hzw⟩, rfl, rfl⟩
      · obtain ⟨h1, h2⟩ := mixed y x hy hx
        exact Or.inr ⟨x, y, z, w, ⟨⟨⟨h2, h1⟩, ⟨hz, hw⟩⟩, Or.inl hzw⟩, rfl, rfl⟩
      · exact Or.inl (Or.inr ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, ⟨hz, hw⟩⟩, Or.inl hzw⟩, rfl, rfl⟩)
    · exact Or.inl (Or.inl ⟨x, y, z, w, ⟨⟨⟨mem_fld_l hxy, mem_fld_r hxy⟩, ⟨hz, hw⟩⟩,
        Or.inr ⟨e, hxy⟩⟩, rfl, rfl⟩)
    · exact Or.inl (Or.inr ⟨x, y, z, w, ⟨⟨⟨mem_fld_l hxy, mem_fld_r hxy⟩, ⟨hz, hw⟩⟩,
        Or.inr ⟨e, hxy⟩⟩, rfl, rfl⟩)
    · exact Or.inr ⟨x, y, z, w, ⟨⟨mixed x y hx' hy', ⟨hz, hw⟩⟩, Or.inr ⟨e, ⟨hx', hy'⟩⟩⟩,
        rfl, rfl⟩
  · rintro ((⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, h⟩, rfl, rfl⟩ |
      ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, h⟩, rfl, rfl⟩) | ⟨x, y, z, w, ⟨⟨⟨hx, hy⟩, hzw⟩, h⟩, rfl, rfl⟩)
    · refine ⟨x, y, z, w, ⟨⟨⟨Or.inl hx, Or.inl hy⟩, hzw⟩, ?_⟩, rfl, rfl⟩
      rcases h with h | ⟨e, h⟩
      exacts [Or.inl h, Or.inr ⟨e, Or.inl (Or.inl h)⟩]
    · refine ⟨x, y, z, w, ⟨⟨⟨Or.inr hx, Or.inr hy⟩, hzw⟩, ?_⟩, rfl, rfl⟩
      rcases h with h | ⟨e, h⟩
      exacts [Or.inl h, Or.inr ⟨e, Or.inl (Or.inr h)⟩]
    · refine ⟨x, y, z, w, ⟨⟨⟨fld_cross_sub _ _ hx, fld_cross_sub _ _ hy⟩, hzw⟩, ?_⟩, rfl, rfl⟩
      rcases h with h | ⟨e, h⟩
      exacts [Or.inl h, Or.inr ⟨e, Or.inr h⟩]

/-- ✱166·5. \(\vdash .(Q\unicode{x228d} R)\times P=(Q\times P)\unicode{x228d} (R\times P)\) -/
theorem pm166_5 {α β : Type*} {Q R : β → β → Prop} {P : α → α → Prop} :
    (Q ⊍ R) ×ᵣ P = Q ×ᵣ P ⊍ R ×ᵣ P :=
  pm162_27

/-- ✱166·51. \(\vdash .(Q\unicode{x21f8} y)\times P=(Q\times P)\unicode{x228d} (CʻQ\uparrow {℩}ʻy)\times P \quad[*166·5.*161·1]\)

`(C'Q ↑ {℩}'y) × P` is `cross (fld Q) (ι y) ×ᵣ P`. -/
theorem pm166_51 {α β : Type*} {Q : β → β → Prop} {y : β} {P : α → α → Prop} :
    (Q ⇸ y) ×ᵣ P = Q ×ᵣ P ⊍ cross (fld Q) (ι y) ×ᵣ P :=
  pm166_5

/-- ✱166·511. \(\vdash .(y\unicode{x21f7}Q)\times P=({℩}ʻy\uparrow CʻP)\times P\unicode{x228d} (Q\times P)\)

**Status.** proved (reading): transcription error: the e-text prints `(ι'y ↑ C'P) × P`, which
is not significant (`C'P` is not a class of the type of `y`); since `y ⇷ Q = ι'y ↑ C'Q ∪̇ Q`
(✱161·101), PM's summand is `(ι'y ↑ C'Q) × P`, the analogue of ✱166·51. -/
theorem pm166_511 {α β : Type*} {Q : β → β → Prop} {y : β} {P : α → α → Prop} :
    (y ⇷ Q) ×ᵣ P = cross (ι y) (fld Q) ×ᵣ P ⊍ Q ×ᵣ P :=
  pm166_5

/-- ✱166·52. \(\vdash .P\downarrow_{.,} ^{;}(Q\unicode{x21f8} y)=P\downarrow_{.,} ^{;}Q\unicode{x21f8} P\downarrow_{.,} y \quad[*161·4.*165·2]\)

`P↓.,;Q ⇸ P↓.,y` is `(P↓.,;Q) ⇸ (P↓.,y)`. -/
theorem pm166_52 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {y : β} :
    coupleSemi P ⁏ (Q ⇸ y) = coupleSemi P ⁏ Q ⇸ opSemi couple P y :=
  graph_semi_addLast (opSemi couple P) Q y

/-- ✱166·521. \(\vdash .P\downarrow_{.,} ^{;}(y\unicode{x21f7}Q)=P\downarrow_{.,} y\unicode{x21f7}P\downarrow_{.,} ^{;}Q\) -/
theorem pm166_521 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {y : β} :
    coupleSemi P ⁏ (y ⇷ Q) = opSemi couple P y ⇷ coupleSemi P ⁏ Q :=
  graph_semi_addFirst (opSemi couple P) Q y

/-- ✱166·53. \(\vdash :\dot{\exists} !Q.\supset .(Q\unicode{x21f8} y)\times P=(Q\times P)\unicode{x2909}(P\downarrow_{.,} y)\) -/
theorem pm166_53 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {y : β} :
    rEx Q → (Q ⇸ y) ×ᵣ P = (Q ×ᵣ P) ⤉ (opSemi couple P y) := by
  intro h
  show relSigma (coupleSemi P ⁏ (Q ⇸ y)) = relSigma (coupleSemi P ⁏ Q) ⤉ opSemi couple P y
  rw [pm166_52, pm162_43 (pm165_243.1 h)]

/-- ✱166·531. \(\vdash :\dot{\exists} !Q.\supset .(y\unicode{x21f7}Q)\times P=(P\downarrow_{.,} y)\unicode{x2909}(Q\times P)\) -/
theorem pm166_531 {α β : Type*} {P : α → α → Prop} {Q : β → β → Prop} {y : β} :
    rEx Q → (y ⇷ Q) ×ᵣ P = (opSemi couple P y) ⤉ (Q ×ᵣ P) := by
  intro h
  show relSigma (coupleSemi P ⁏ (y ⇷ Q)) = opSemi couple P y ⤉ relSigma (coupleSemi P ⁏ Q)
  rw [pm166_521, pm162_431 (pm165_243.1 h)]

/-- ✱166·54. \(\vdash .Q\times (P\unicode{x21f8} x)=(Q\times P)\unicode{x228d} Q\times (CʻP\uparrow {℩}ʻx)\)

`Q × (C'P ↑ {℩}'x)` is `Q ×ᵣ cross (fld P) (ι x)`. -/
theorem pm166_54 {α β : Type*} {Q : β → β → Prop} {P : α → α → Prop} {x : α} :
    Q ×ᵣ (P ⇸ x) = Q ×ᵣ P ⊍ Q ×ᵣ cross (fld P) (ι x) := by
  by_cases hP : rEx P
  · exact pm166_471 fun z hz => by
      rw [fld_cross (rEx_iff_fld.1 hP) ⟨x, mem_unitCls.2 rfl⟩]; exact Or.inl hz
  · have hP' := eq_rNull_of_not_rEx hP
    have hc : cross (fld P) (ι x) = rNull := by
      rw [hP', fld_rNull]
      exact rel_ext' fun a b => ⟨fun h => absurd h.1 (by simp), fun h => absurd h (rNull_apply a b)⟩
    have e : ∀ X : α → α → Prop, X = rNull → Q ×ᵣ X = rNull := fun X hX => pm166_13.2 (Or.inr hX)
    rw [e (P ⇸ x) (by rw [hP', addLast_rNull]), e P hP', e (cross (fld P) (ι x)) hc]
    exact rel_ext' fun a b => ⟨fun h => absurd h (rNull_apply a b),
      fun h => h.elim (fun h => absurd h (rNull_apply a b)) (fun h => absurd h (rNull_apply a b))⟩

/-- ✱166·541. \(\vdash .Q\times (x\unicode{x21f7}P)=Q\times ({℩}ʻx\uparrow CʻP)\unicode{x228d} (Q\times P)\) -/
theorem pm166_541 {α β : Type*} {Q : β → β → Prop} {P : α → α → Prop} {x : α} :
    Q ×ᵣ (x ⇷ P) = Q ×ᵣ cross (ι x) (fld P) ⊍ Q ×ᵣ P := by
  by_cases hP : rEx P
  · rw [show x ⇷ P = P ⊍ cross (ι x) (fld P) from rcup_comm _ _,
      pm166_471 fun z hz => by
        rw [fld_cross ⟨x, mem_unitCls.2 rfl⟩ (rEx_iff_fld.1 hP)]; exact Or.inr hz,
      rcup_comm]
  · have hP' := eq_rNull_of_not_rEx hP
    have hc : cross (ι x) (fld P) = rNull := by
      rw [hP', fld_rNull]
      exact rel_ext' fun a b => ⟨fun h => absurd h.2 (by simp), fun h => absurd h (rNull_apply a b)⟩
    have e : ∀ X : α → α → Prop, X = rNull → Q ×ᵣ X = rNull := fun X hX => pm166_13.2 (Or.inr hX)
    rw [e (x ⇷ P) (by rw [hP', addFirst_rNull]), e P hP', e (cross (ι x) (fld P)) hc]
    exact rel_ext' fun a b => ⟨fun h => absurd h (rNull_apply a b),
      fun h => h.elim (fun h => absurd h (rNull_apply a b)) (fun h => absurd h (rNull_apply a b))⟩

end PrincipiaMathematica
