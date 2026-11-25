import PrincipiaMathematica.Defs.Part4

/-!
# Part IV, Section C: The principle of first differences, and the multiplication and exponentiation of relations

Volume 2. Numbers: ✱170, ✱171, ✱172, ✱173, ✱174, ✱176, ✱177.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w u'

/-!
## [✱170] On the relation of first differences among the sub-classes of a given class

*(Vol. 2, p. 411)*

> *Summary of* *170.
>
> …

**Lean reading.** `P_cl` is `Pcl P : Set α → Set α → Prop` (✱170·01) and `P_lc` is
`Plc P = (Pcl P˘)˘`; the Df ✱170·02 and its restatement ✱170·101 keep the description `Cnv'`.
`α, β ∈ Cl'C'P` is `A ∈ cl (fld P) ∧ B ∈ cl (fld P)`, `P⃗'y` is `refs P y`, `p'P⃗''(α − β)` is
`prodCls (Rfwd P ʻʻ (A \ B))`, `α −̇P_cl β` is `(∸Pcl P) A B`. `B'P_cl` (✱170·38) keeps the
description (`Desc Beg …`), while `Cnv'P_cl` is written `(Pcl P)˘`. `S_∈;Q_cl` is
`imgRel S ⁏ Pcl Q`, `(ι'x ∪);P_cl` is `opL (· ∪ ·) (ι x) ⁏ Pcl P`, `s;C;R` is `sRel ⁏ C ⁏ R`,
`(s|C) ↾ C'R` is `(sRel ⨾ C) ↾ fld R`, and `P_cl × Q_cl` is `Pcl P ×ᵣ Pcl Q` (couples `γ ↓ α`
with `α ∈ C'P_cl`, ordered first by `P_cl`, Defs/Part4 decision 9). Products of hypotheses are
conjunctions bracketed to the left. The correlators of ✱170·43·68 are shown to be correlators via
the general lemma `pm170_aux_smorbar` (`graph f ↾ C'Q` with `f` injective on `C'Q`).

**Status.** proved (all propositions; ✱170·01·02 definition; ✱170·1·102·66 proved (reading):
transcription errors of the e-text, see their docstrings).
-/

section Helpers170

variable {α : Type u} {β : Type v}

theorem pm170_aux_fld_cnv (P : α → α → Prop) : fld P˘ = fld P := by
  ext x; constructor <;> rintro ⟨y, h | h⟩ <;> exact ⟨y, by tauto⟩

theorem pm170_aux_Null (x : α) : x ∉ (Λ : Set α) := fun h => h rfl

theorem pm170_aux_Null_eq : (Λ : Set α) = ∅ := Null_eq_empty

theorem pm170_aux_rEx_iff_fld {P : α → α → Prop} : rEx P ↔ (fld P).Nonempty := by
  constructor
  · rintro ⟨x, y, h⟩; exact ⟨x, y, Or.inl h⟩
  · rintro ⟨x, y, h | h⟩
    · exact ⟨x, y, h⟩
    · exact ⟨y, x, h⟩

/-- A correlator `graph f ↾ C'Q` with `f` injective on `C'Q` and `P` the image of `Q`. -/
theorem pm170_aux_smorbar {P : α → α → Prop} {Q : β → β → Prop} (f : β → α)
    (hinj : ∀ z w, z ∈ fld Q → w ∈ fld Q → f z = f w → z = w)
    (hP : ∀ x y, P x y ↔ ∃ z w, Q z w ∧ x = f z ∧ y = f w) :
    graph f ↾ fld Q ∈ smorbar P Q := by
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨hx, -⟩, ⟨hy, -⟩⟩; exact hx.trans hy.symm
  · rintro x y z ⟨⟨hy, hyQ⟩, ⟨hz, hzQ⟩⟩; exact hinj y z hyQ hzQ (hy.symm.trans hz)
  · ext z; exact ⟨fun h => ⟨f z, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  · funext x y; apply propext; rw [hP, semi_apply]
    constructor
    · rintro ⟨z, w, hzw, rfl, rfl⟩
      exact ⟨z, w, ⟨⟨rfl, w, Or.inl hzw⟩, ⟨rfl, z, Or.inr hzw⟩⟩, hzw⟩
    · rintro ⟨z, w, ⟨⟨hx, -⟩, ⟨hy, -⟩⟩, hzw⟩
      exact ⟨z, w, hzw, hx, hy⟩

theorem pm170_aux_mem_fld_couple {x y z : α} : z ∈ fld (x ↓ y) ↔ z = x ∨ z = y := by
  constructor
  · rintro ⟨w, ⟨h, -⟩ | ⟨-, h⟩⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨y, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨x, Or.inr ⟨rfl, rfl⟩⟩

end Helpers170

variable {α : Type u} {β : Type v}

section Helpers170b

variable {α : Type u} {β : Type v}

theorem pm170_aux_imgRel_semi (S : α → β → Prop) (R : Set β → Set β → Prop) (A B : Set α) :
    (imgRel S ⁏ R) A B ↔ ∃ G D, (A = S ʻʻ G ∧ B = S ʻʻ D) ∧ R G D :=
  semi_graph_apply _ _ _ _

theorem pm170_aux_fld_semi {S : α → β → Prop} {Q : β → β → Prop} (hc : fld Q = codom S) :
    fld (S ⁏ Q) = dom S := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · obtain ⟨z, w, ⟨hxz, -⟩, -⟩ := (semi_apply S Q x y).1 h; exact ⟨z, hxz⟩
    · obtain ⟨z, w, ⟨-, hxw⟩, -⟩ := (semi_apply S Q y x).1 h; exact ⟨w, hxw⟩
  · rintro ⟨z, hxz⟩
    have hz : z ∈ fld Q := by rw [hc]; exact ⟨x, hxz⟩
    obtain ⟨w, hzw | hwz⟩ := hz
    · have : w ∈ codom S := by rw [← hc]; exact ⟨z, Or.inr hzw⟩
      obtain ⟨y, hyw⟩ := this
      exact ⟨y, Or.inl ((semi_apply S Q x y).2 ⟨z, w, ⟨hxz, hyw⟩, hzw⟩)⟩
    · have : w ∈ codom S := by rw [← hc]; exact ⟨z, Or.inl hwz⟩
      obtain ⟨y, hyw⟩ := this
      exact ⟨y, Or.inr ((semi_apply S Q y x).2 ⟨w, z, ⟨hyw, hxz⟩, hwz⟩)⟩

theorem pm170_aux_semi_cres (S : α → β → Prop) (Q : β → β → Prop) : S ⁏ Q = (S ↾ fld Q) ⁏ Q := by
  funext x y; apply propext
  rw [semi_apply, semi_apply]
  constructor
  · rintro ⟨z, w, ⟨h1, h2⟩, hq⟩
    exact ⟨z, w, ⟨⟨h1, w, Or.inl hq⟩, ⟨h2, z, Or.inr hq⟩⟩, hq⟩
  · rintro ⟨z, w, ⟨h1, h2⟩, hq⟩
    exact ⟨z, w, ⟨h1.1, h2.1⟩, hq⟩

theorem pm170_aux_img_cres {S : α → β → Prop} {B G : Set β} (h : G ⊆ B) :
    (S ↾ B) ʻʻ G = S ʻʻ G := by
  ext x; exact ⟨fun ⟨z, hz, h1, _⟩ => ⟨z, hz, h1⟩, fun ⟨z, hz, h1⟩ => ⟨z, hz, h1, h hz⟩⟩

end Helpers170b

/-- ✱170·01 (Df). \(P_{\text{cl}}=\hat{\alpha} \hat{\beta} \{\alpha ,\beta \in \text{Cl}ʻCʻP.\exists !\alpha -\beta -\breve{P} ʻʻ(\beta -\alpha )\} \quad\text{Df}\) -/
theorem pm170_01 (P : α → α → Prop) : Pcl P = fun A B => (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧
    ((A \ B) \ P˘ ʻʻ (B \ A)).Nonempty := rfl

/-- ✱170·02 (Df). \(P_{\text{lc}} = \text{Cnv}ʻ(\breve{P} )_{\text{cl}} \quad\text{Df}\) -/
theorem pm170_02 (P : α → α → Prop) : Desc Cnv (Pcl P˘) (fun X => Plc P = X) :=
  (desc_Cnv _ _).2 rfl

/-- ✱170·1. \(\vdash :\alpha P_{\text{cl}}\beta .\equiv .a,\beta \in \text{Cl}ʻCʻP.\exists !\alpha -\beta -\breve{P} ʻʻ(\beta -\alpha ) \quad[(*170·01)]\)

**Status.** proved (reading): transcription error: the e-text prints `a, β` for `α, β` (as in
✱170·01). -/
theorem pm170_1 {P : α → α → Prop} {A B : Set α} : Pcl P A B ↔
    (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧ ((A \ B) \ P˘ ʻʻ (B \ A)).Nonempty := Iff.rfl

/-- ✱170·101. \(\vdash .P_{\text{lc}}=\text{Cnv}ʻ(\breve{P} )_{\text{cl}} \quad[(*170·02)]\) -/
theorem pm170_101 (P : α → α → Prop) : Desc Cnv (Pcl P˘) (fun X => Plc P = X) :=
  (desc_Cnv _ _).2 rfl

/-- ✱170·102. \(\vdash :\alpha P_{\text{lc}}\beta .\equiv .a,\beta \in \text{Cl}ʻCʻP.\exists !\beta -\alpha -Pʻʻ(\alpha -\beta ) \quad[*170·1·101]\)

**Status.** proved (reading): transcription error: the e-text prints `a, β` for `α, β`. -/
theorem pm170_102 {P : α → α → Prop} {A B : Set α} : Plc P A B ↔
    (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧ ((B \ A) \ P ʻʻ (A \ B)).Nonempty := by
  show Pcl P˘ B A ↔ _
  rw [pm170_1, pm170_aux_fld_cnv]
  exact and_congr (and_comm) Iff.rfl

/-- ✱170·103. \(\vdash :y{\sim}\in \breve{P} ʻʻ(\beta-\alpha ).\equiv .\overrightarrow{P}ʻy\cap \beta \subset \alpha\) -/
theorem pm170_103 {P : α → α → Prop} {A B : Set α} {y : α} :
    y ∉ P˘ ʻʻ (B \ A) ↔ refs P y ∩ B ⊆ A := by
  constructor
  · intro h x ⟨hx, hxB⟩
    by_contra hA
    exact h ⟨x, ⟨hxB, hA⟩, hx⟩
  · rintro h ⟨x, ⟨hxB, hxA⟩, hx⟩
    exact hxA (h ⟨hx, hxB⟩)

/-- ✱170·11. \[\begin{align}&\vdash \colon\ldotp \alpha P_{\text{cl}}\beta .\equiv :\alpha ,\beta \in \text{Cl}ʻCʻP:(\exists y).y\in \alpha -\beta .\overrightarrow{P}ʻy\cap \beta \subset \alpha \\ &[*170·1·103]\end{align}\] -/
theorem pm170_11 {P : α → α → Prop} {A B : Set α} : Pcl P A B ↔
    (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧ ∃ y, y ∈ A \ B ∧ refs P y ∩ B ⊆ A := by
  rw [pm170_1]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨y, hy, h⟩; exact ⟨y, hy, pm170_103.1 h⟩
  · rintro ⟨y, hy, h⟩; exact ⟨y, hy, pm170_103.2 h⟩

/-- ✱170·12. \[\begin{align}&\vdash :\alpha P_{\text{cl}}\beta .\equiv .\alpha ,\beta \in \text{Cl}ʻCʻP.\exists !\alpha -(\alpha \cap \beta )-\breve{P} ʻʻ\{\beta -(\alpha \cap \beta )\}\\ &[*170·1.*22·93]\end{align}\] -/
theorem pm170_12 {P : α → α → Prop} {A B : Set α} : Pcl P A B ↔
    (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧ ((A \ (A ∩ B)) \ P˘ ʻʻ (B \ (A ∩ B))).Nonempty := by
  rw [pm170_1, Set.sdiff_self_inter, Set.sdiff_inter_self_eq_sdiff]

/-- ✱170·14. \[\begin{align}&\vdash \colon\ldotp \alpha ,\beta \in \text{Cl}ʻCʻP.\supset :\alpha \dot{-} P_{\text{cl}}\beta .\equiv .\alpha -\beta \subset \breve{P} ʻʻ(\beta -\alpha )\\ &[*170·1.*24·55]\end{align}\] -/
theorem pm170_14 {P : α → α → Prop} {A B : Set α} (h : A ∈ cl (fld P) ∧ B ∈ cl (fld P)) :
    (∸Pcl P) A B ↔ A \ B ⊆ P˘ ʻʻ (B \ A) := by
  show ¬ Pcl P A B ↔ _
  rw [pm170_1, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  exact not_congr ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩

/-- ✱170·141. \[\begin{align}&\vdash \colon\ldotp \alpha ,\beta \in \text{Cl}ʻCʻP.\supset :\alpha \dot{-} P_{\text{lc}}\beta .\equiv .\beta -\alpha \subset Pʻʻ(\alpha - \beta )\\ &[*170·14·101]\end{align}\] -/
theorem pm170_141 {P : α → α → Prop} {A B : Set α} (h : A ∈ cl (fld P) ∧ B ∈ cl (fld P)) :
    (∸Plc P) A B ↔ B \ A ⊆ P ʻʻ (A \ B) := by
  show ¬ Plc P A B ↔ _
  rw [pm170_102, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  exact not_congr ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩

/-- ✱170·15. \(\vdash :\alpha P_{\text{cl}}\beta .\supset .\beta \cap pʻ\overrightarrow{P}ʻʻ(\alpha -\beta )\subset \alpha\) -/
theorem pm170_15 {P : α → α → Prop} {A B : Set α} (h : Pcl P A B) :
    B ∩ prodCls (Rfwd P ʻʻ (A \ B)) ⊆ A := by
  obtain ⟨-, y, hy, hyB⟩ := pm170_11.1 h
  rintro x ⟨hxB, hx⟩
  exact hyB ⟨hx (refs P y) ⟨y, hy, rfl⟩, hxB⟩

/-- ✱170·16. \(\vdash :\alpha \subset CʻP.\beta \subset \alpha .\beta \neq \alpha .\supset .\alpha P_{\text{cl}}\beta\) -/
theorem pm170_16 {P : α → α → Prop} {A B : Set α} (h : (A ⊆ fld P ∧ B ⊆ A) ∧ B ≠ A) :
    Pcl P A B := by
  obtain ⟨⟨hA, hBA⟩, hne⟩ := h
  obtain ⟨y, hyA, hyB⟩ : (A \ B).Nonempty := by
    by_contra h'
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h'
    exact hne (Set.Subset.antisymm hBA h')
  refine pm170_11.2 ⟨⟨hA, hBA.trans hA⟩, y, ⟨hyA, hyB⟩, fun x hx => hBA hx.2⟩

/-- ✱170·161. \(\vdash :\alpha \subset CʻP.\beta \subset \alpha .\beta \neq \alpha .\supset .\beta P_{\text{lc}}\alpha \) -/
theorem pm170_161 {P : α → α → Prop} {A B : Set α} (h : (A ⊆ fld P ∧ B ⊆ A) ∧ B ≠ A) :
    Plc P B A := by
  show Pcl P˘ A B
  apply pm170_16
  rw [pm170_aux_fld_cnv]; exact h

/-- ✱170·17. \(\vdash .P_{\text{cl}}\,\unicode{x2abd}\, J.P_{\text{lc}}\,\unicode{x2abd}\, J\) -/
theorem pm170_17 (P : α → α → Prop) : Pcl P ⪽ J ∧ Plc P ⪽ J := by
  constructor
  · rintro A B ⟨-, y, ⟨hyA, hyB⟩, -⟩ rfl; exact hyB hyA
  · rintro A B ⟨-, y, ⟨hyA, hyB⟩, -⟩ rfl; exact hyB hyA

/-- ✱170·2. \[\begin{align}&\vdash \colon\ldotp \alpha ,\beta \in \text{Cl}ʻCʻP:(\exists y). y\in \alpha -\beta . \overrightarrow{P}ʻy\cap \alpha = \overrightarrow{P}ʻy\cap \beta :\supset .\alpha P_{\text{cl}}\beta \\ &[*170·11 .*22·43]\end{align}\] -/
theorem pm170_2 {P : α → α → Prop} {A B : Set α}
    (h : (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧ ∃ y, y ∈ A \ B ∧ refs P y ∩ A = refs P y ∩ B) :
    Pcl P A B := by
  obtain ⟨hAB, y, hy, he⟩ := h
  refine pm170_11.2 ⟨hAB, y, hy, ?_⟩
  rw [← he]; exact Set.inter_subset_right

/-- ✱170·21. \(\vdash \colon\ldotp \alpha \subset CʻP.\supset : y \,\text{min}_{P}(\alpha -\beta ).\equiv . y\in \alpha -\beta . \overrightarrow{P}ʻy\cap \alpha \subset \beta\) -/
theorem pm170_21 {P : α → α → Prop} {A B : Set α} {y : α} (hA : A ⊆ fld P) :
    minP P y (A \ B) ↔ y ∈ A \ B ∧ refs P y ∩ A ⊆ B := by
  rw [minP_apply]
  constructor
  · rintro ⟨⟨hy, -⟩, h⟩
    refine ⟨hy, fun x ⟨hx, hxA⟩ => ?_⟩
    by_contra hxB
    exact h ⟨x, ⟨hxA, hxB⟩, hx⟩
  · rintro ⟨hy, h⟩
    exact ⟨⟨hy, hA hy.1⟩, fun ⟨x, ⟨hxA, hxB⟩, hx⟩ => hxB (h ⟨hx, hxA⟩)⟩

/-- ✱170·22. \(\vdash \colon\ldotp \alpha \subset CʻP. y \text{min}_{P} (\alpha -\beta ).\supset : \overrightarrow{P}ʻy\cap \beta \subset \alpha .\equiv . \overrightarrow{P}ʻy\cap \alpha = \overrightarrow{P}ʻy\cap \beta\) -/
theorem pm170_22 {P : α → α → Prop} {A B : Set α} {y : α} (h : A ⊆ fld P ∧ minP P y (A \ B)) :
    refs P y ∩ B ⊆ A ↔ refs P y ∩ A = refs P y ∩ B := by
  have h2 := ((pm170_21 h.1).1 h.2).2
  constructor
  · intro h1
    exact Set.Subset.antisymm (fun x hx => ⟨hx.1, h2 hx⟩) (fun x hx => ⟨hx.1, h1 hx⟩)
  · intro e x hx
    rw [← e] at hx; exact hx.2

/-- ✱170·23. \[\begin{align}\vdash \colon\ldotp \alpha \subset CʻP. y\in \alpha -\beta -\breve{P} ʻʻ&(\beta -\alpha ).\supset :\\ y \,\text{min}_{P} (\alpha-\beta ) .\equiv . \overrightarrow{P}ʻy\cap \alpha =\overrightarrow{P}ʻy\cap \beta \end{align}\] -/
theorem pm170_23 {P : α → α → Prop} {A B : Set α} {y : α}
    (h : A ⊆ fld P ∧ y ∈ (A \ B) \ P˘ ʻʻ (B \ A)) :
    minP P y (A \ B) ↔ refs P y ∩ A = refs P y ∩ B := by
  obtain ⟨hA, hy, hy'⟩ := h
  have h1 := pm170_103.1 hy'
  rw [pm170_21 hA]
  constructor
  · rintro ⟨-, h2⟩
    exact Set.Subset.antisymm (fun x hx => ⟨hx.1, h2 hx⟩) (fun x hx => ⟨hx.1, h1 hx⟩)
  · intro e
    refine ⟨hy, fun x hx => ?_⟩
    rw [e] at hx; exact hx.2

/-- ✱170·3. \(\vdash :\alpha \in \text{Cl}ʻCʻP.\beta \subset \alpha .\exists !\alpha -\beta .\supset .\alpha P_{\text{cl}}\beta \quad[*170·16]\) -/
theorem pm170_3 {P : α → α → Prop} {A B : Set α} (h : (A ∈ cl (fld P) ∧ B ⊆ A) ∧ (A \ B).Nonempty) :
    Pcl P A B := by
  obtain ⟨⟨hA, hBA⟩, y, hyA, hyB⟩ := h
  exact pm170_16 ⟨⟨hA, hBA⟩, fun e => hyB (e ▸ hyA)⟩

/-- ✱170·31. \(\vdash :\beta \subset CʻP.\beta \neq CʻP .\equiv . (CʻP) P_{\text{cl}}\beta \quad[*170·16]\) -/
theorem pm170_31 {P : α → α → Prop} {B : Set α} : (B ⊆ fld P ∧ B ≠ fld P) ↔ Pcl P (fld P) B := by
  constructor
  · rintro ⟨h1, h2⟩; exact pm170_16 ⟨⟨subset_rfl, h1⟩, h2⟩
  · rintro ⟨⟨-, hB⟩, y, ⟨hyA, hyB⟩, -⟩
    exact ⟨hB, fun e => hyB (e ▸ hyA)⟩

/-- ✱170·32. \(\vdash :\alpha \subset CʻP.\exists ! \alpha .\equiv . \alpha P_{\text{cl}}\Lambda \quad[*170·3]\) -/
theorem pm170_32 {P : α → α → Prop} {A : Set α} : (A ⊆ fld P ∧ A.Nonempty) ↔ Pcl P A Λ := by
  constructor
  · rintro ⟨h1, y, hy⟩
    exact pm170_3 ⟨⟨h1, fun x hx => absurd hx (pm170_aux_Null x)⟩, y, hy, pm170_aux_Null y⟩
  · rintro ⟨⟨hA, -⟩, y, ⟨hyA, -⟩, -⟩
    exact ⟨hA, y, hyA⟩

/-- ✱170·33. \(\vdash :\dot{\exists} !P .\equiv . (CʻP)P_{\text{cl}}\Lambda\) -/
theorem pm170_33 {P : α → α → Prop} : rEx P ↔ Pcl P (fld P) Λ := by
  rw [← pm170_32, pm170_aux_rEx_iff_fld]
  exact ⟨fun h => ⟨subset_rfl, h⟩, fun h => h.2⟩

/-- ✱170·34. \(\vdash :\dot{\exists} !P .\equiv . \dot{\exists} !P_{\text{cl}}\) -/
theorem pm170_34 {P : α → α → Prop} : rEx P ↔ rEx (Pcl P) := by
  constructor
  · intro h; exact ⟨_, _, pm170_33.1 h⟩
  · rintro ⟨A, B, ⟨⟨hA, -⟩, y, ⟨hyA, -⟩, -⟩⟩
    exact pm170_aux_rEx_iff_fld.2 ⟨y, hA hyA⟩

/-- ✱170·35. \(\vdash .\dot{\Lambda} _{\text{cl}}=\dot{\Lambda} \quad[*170·34. \text{Transp}]\) -/
theorem pm170_35 : Pcl (rNull : α → α → Prop) = rNull := by
  funext A B; apply propext
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := pm170_34.2 ⟨A, B, h⟩
    exact absurd hxy (rNull_apply x y)
  · intro h; exact absurd h (rNull_apply A B)

/-- ✱170·36. \(\vdash .\text{D}ʻP_{\text{cl}}=\text{Cl ex}ʻCʻP.\text{ᗡ}ʻP_{\text{cl}}=\text{Cl}ʻCʻP-\iota ʻCʻP\) -/
theorem pm170_36 (P : α → α → Prop) :
    dom (Pcl P) = clEx (fld P) ∧ codom (Pcl P) = cl (fld P) \ ι (fld P) := by
  constructor
  · ext A
    constructor
    · rintro ⟨B, ⟨⟨hA, -⟩, y, ⟨hyA, -⟩, -⟩⟩; exact ⟨hA, y, hyA⟩
    · rintro ⟨hA, hne⟩; exact ⟨Λ, pm170_32.1 ⟨hA, hne⟩⟩
  · ext B
    constructor
    · rintro ⟨A, ⟨⟨hA, hB⟩, y, ⟨hyA, hyB⟩, -⟩⟩
      exact ⟨hB, fun e => hyB ((show B = fld P from e) ▸ hA hyA)⟩
    · rintro ⟨hB, hne⟩
      exact ⟨fld P, pm170_31.1 ⟨hB, hne⟩⟩

/-- ✱170·37. \(\vdash :\dot{\exists} !P.\supset .CʻP_{\text{cl}}=\text{Cl}ʻCʻP \quad[*170·36]\) -/
theorem pm170_37 {P : α → α → Prop} (h : rEx P) : fld (Pcl P) = cl (fld P) := by
  obtain ⟨h1, h2⟩ := pm170_36 P
  have hne := pm170_aux_rEx_iff_fld.1 h
  ext A
  constructor
  · rintro ⟨B, ⟨⟨hA, -⟩, -⟩ | ⟨⟨-, hA⟩, -⟩⟩ <;> exact hA
  · intro hA
    by_cases hA' : A.Nonempty
    · have : A ∈ dom (Pcl P) := by rw [h1]; exact ⟨hA, hA'⟩
      obtain ⟨B, hB⟩ := this; exact ⟨B, Or.inl hB⟩
    · have : A ∈ codom (Pcl P) := by
        rw [h2]
        refine ⟨hA, fun e => hA' ?_⟩
        rw [show A = fld P from e]; exact hne
      obtain ⟨B, hB⟩ := this; exact ⟨B, Or.inr hB⟩

/-- ✱170·371. \(\vdash .CʻP_{\text{cl}}\subset \text{Cl}ʻCʻP \quad[*170·37·35.*33·241]\) -/
theorem pm170_371 (P : α → α → Prop) : fld (Pcl P) ⊆ cl (fld P) := by
  rintro A ⟨B, ⟨⟨hA, -⟩, -⟩ | ⟨⟨-, hA⟩, -⟩⟩ <;> exact hA

/-- ✱170·38. \(\vdash :\dot{\exists} !P.\supset .BʻP_{\text{cl}}=CʻP.Bʻ\text{Cnv}ʻP_{\text{cl}}=\Lambda \quad[*170·36]\) -/
theorem pm170_38 {P : α → α → Prop} (h : rEx P) :
    Desc Beg (Pcl P) (fun b => b = fld P) ∧ Desc Beg (Pcl P)˘ (fun b => b = Λ) := by
  obtain ⟨h1, h2⟩ := pm170_36 P
  have hne := pm170_aux_rEx_iff_fld.1 h
  have hcnv1 : dom (Pcl P)˘ = codom (Pcl P) := rfl
  have hcnv2 : codom (Pcl P)˘ = dom (Pcl P) := rfl
  constructor
  · refine ⟨fld P, fun A => ?_, rfl⟩
    show Beg A (Pcl P) ↔ A = fld P
    rw [Beg_apply, h1, h2]
    constructor
    · rintro ⟨⟨hA, -⟩, hA'⟩
      by_contra hne'
      exact hA' ⟨hA, hne'⟩
    · rintro rfl
      exact ⟨⟨subset_rfl, hne⟩, fun ⟨_, h'⟩ => h' rfl⟩
  · refine ⟨Λ, fun A => ?_, rfl⟩
    show Beg A (Pcl P)˘ ↔ A = Λ
    rw [Beg_apply, hcnv1, hcnv2, h1, h2]
    constructor
    · rintro ⟨⟨hA, -⟩, hA'⟩
      by_contra hne'
      refine hA' ⟨hA, ?_⟩
      rw [Set.nonempty_iff_ne_empty, ← pm170_aux_Null_eq]; exact hne'
    · rintro rfl
      refine ⟨⟨fun x hx => absurd hx (pm170_aux_Null x), ?_⟩, ?_⟩
      · intro e
        obtain ⟨y, hy⟩ := hne
        have e' : (Λ : Set α) = fld P := e
        rw [← e'] at hy; exact pm170_aux_Null y hy
      · rintro ⟨-, y, hy⟩; exact pm170_aux_Null y hy

/-- ✱170·4. \(\vdash :S\in 1\rightarrow 1.CʻQ=\text{ᗡ}ʻS.\supset .(S^{;}Q)_{\text{cl}}=S_{\in }^{;}Q_{\text{cl}}\) -/
theorem pm170_4 {S : α → β → Prop} {Q : β → β → Prop} (h : S ∈ arrow one one ∧ fld Q = codom S) :
    Pcl (S ⁏ Q) = imgRel S ⁏ Pcl Q := by
  obtain ⟨hS, hc⟩ := h
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS
  have hf := pm170_aux_fld_semi hc
  funext A B; apply propext
  rw [pm170_1, pm170_aux_imgRel_semi, hf]
  constructor
  · rintro ⟨⟨hA, hB⟩, y, ⟨hyA, hyB⟩, hy⟩
    refine ⟨{z | ∃ x, x ∈ A ∧ S x z}, {z | ∃ x, x ∈ B ∧ S x z}, ⟨?_, ?_⟩, ?_⟩
    · ext x; constructor
      · intro hx; obtain ⟨z, hz⟩ := hA hx; exact ⟨z, ⟨x, hx, hz⟩, hz⟩
      · rintro ⟨z, ⟨x', hx', hz'⟩, hz⟩; rw [h1 x x' z ⟨hz, hz'⟩]; exact hx'
    · ext x; constructor
      · intro hx; obtain ⟨z, hz⟩ := hB hx; exact ⟨z, ⟨x, hx, hz⟩, hz⟩
      · rintro ⟨z, ⟨x', hx', hz'⟩, hz⟩; rw [h1 x x' z ⟨hz, hz'⟩]; exact hx'
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · rintro z ⟨x, -, hz⟩; rw [hc]; exact ⟨x, hz⟩
      · rintro z ⟨x, -, hz⟩; rw [hc]; exact ⟨x, hz⟩
      · obtain ⟨z0, hz0⟩ := hA hyA
        refine ⟨z0, ⟨⟨y, hyA, hz0⟩, ?_⟩, ?_⟩
        · rintro ⟨x, hxB, hx⟩; rw [h1 x y z0 ⟨hx, hz0⟩] at hxB; exact hyB hxB
        · rintro ⟨w, ⟨⟨x, hxB, hxw⟩, hwG⟩, hwz⟩
          have hxA : x ∉ A := fun hxA => hwG ⟨x, hxA, hxw⟩
          exact hy ⟨x, ⟨hxB, hxA⟩, (semi_apply S Q x y).2 ⟨w, z0, ⟨hxw, hz0⟩, hwz⟩⟩
  · rintro ⟨G, D, ⟨rfl, rfl⟩, ⟨⟨hG, hD⟩, z, ⟨hzG, hzD⟩, hz⟩⟩
    have hzc : z ∈ codom S := by rw [← hc]; exact hG hzG
    obtain ⟨y, hyz⟩ := hzc
    refine ⟨⟨?_, ?_⟩, y, ⟨⟨z, hzG, hyz⟩, ?_⟩, ?_⟩
    · rintro x ⟨w, -, hw⟩; exact ⟨w, hw⟩
    · rintro x ⟨w, -, hw⟩; exact ⟨w, hw⟩
    · rintro ⟨w, hwD, hyw⟩; rw [h2 y z w ⟨hyz, hyw⟩] at hzD; exact hzD hwD
    · rintro ⟨x, ⟨⟨w0, hw0D, hxw0⟩, hxG⟩, hxy⟩
      obtain ⟨z1, w1, ⟨hxz1, hyw1⟩, hq⟩ := (semi_apply S Q x y).1 hxy
      rw [h2 y w1 z ⟨hyw1, hyz⟩] at hq
      rw [h2 x z1 w0 ⟨hxz1, hxw0⟩] at hq
      have hw0G : w0 ∉ G := fun h' => hxG ⟨w0, h', hxw0⟩
      exact hz ⟨w0, ⟨hw0D, hw0G⟩, hq⟩

/-- ✱170·41. \(\vdash .(S\upharpoonright CʻQ)_{\in }^{;}Q_{\text{cl}}=S_{\in }^{;}Q_{\text{cl}} \quad[*150·95.*170·371]\) -/
theorem pm170_41 (S : α → β → Prop) (Q : β → β → Prop) :
    imgRel (S ↾ fld Q) ⁏ Pcl Q = imgRel S ⁏ Pcl Q := by
  funext A B; apply propext
  rw [pm170_aux_imgRel_semi, pm170_aux_imgRel_semi]
  constructor
  · rintro ⟨G, D, ⟨rfl, rfl⟩, hGD⟩
    exact ⟨G, D, ⟨pm170_aux_img_cres hGD.1.1, pm170_aux_img_cres hGD.1.2⟩, hGD⟩
  · rintro ⟨G, D, ⟨rfl, rfl⟩, hGD⟩
    exact ⟨G, D, ⟨(pm170_aux_img_cres hGD.1.1).symm, (pm170_aux_img_cres hGD.1.2).symm⟩, hGD⟩

theorem pm170_aux_codom_cres {S : α → β → Prop} {Q : β → β → Prop} (h : fld Q ⊆ codom S) :
    fld Q = codom (S ↾ fld Q) := by
  ext z; constructor
  · intro hz; obtain ⟨x, hx⟩ := h hz; exact ⟨x, hx, hz⟩
  · rintro ⟨x, -, hz⟩; exact hz

/-- ✱170·42. \(\vdash :S\upharpoonright CʻQ\in 1\rightarrow 1.CʻQ\subset \text{ᗡ}ʻS.\supset .(S^{;}Q)_{\text{cl}}=S_{\in }^{;}Q_{\text{cl}}\) -/
theorem pm170_42 {S : α → β → Prop} {Q : β → β → Prop}
    (h : S ↾ fld Q ∈ arrow one one ∧ fld Q ⊆ codom S) :
    Pcl (S ⁏ Q) = imgRel S ⁏ Pcl Q := by
  rw [pm170_aux_semi_cres, pm170_4 ⟨h.1, pm170_aux_codom_cres h.2⟩, pm170_41]

theorem pm170_aux_img_inj {S : α → β → Prop} {B : Set β} (hS : S ↾ B ∈ arrow one one)
    (hc : B ⊆ codom S) {G D : Set β} (hG : G ⊆ B) (hD : D ⊆ B) (e : S ʻʻ G = S ʻʻ D) : G = D := by
  obtain ⟨-, h2⟩ := mem_arrow_one_one.1 hS
  have key : ∀ G D : Set β, G ⊆ B → D ⊆ B → S ʻʻ G = S ʻʻ D → G ⊆ D := by
    intro G D hG hD e z hz
    obtain ⟨x, hx⟩ := hc (hG hz)
    have : x ∈ S ʻʻ D := by rw [← e]; exact ⟨z, hz, hx⟩
    obtain ⟨w, hw, hxw⟩ := this
    rw [h2 x z w ⟨⟨hx, hG hz⟩, ⟨hxw, hD hw⟩⟩]; exact hw
  exact Set.Subset.antisymm (key G D hG hD e) (key D G hD hG e.symm)

/-- ✱170·43. \(\vdash :S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q.\supset .S_{\in }\upharpoonright CʻQ_{\text{cl}}\in P_{\text{cl}}\,\overline{\text{smor}}\, Q_{\text{cl}}\) -/
theorem pm170_43 {S : α → β → Prop} {P : α → α → Prop} {Q : β → β → Prop}
    (h : S ↾ fld Q ∈ smorbar P Q) : imgRel S ↾ fld (Pcl Q) ∈ smorbar (Pcl P) (Pcl Q) := by
  obtain ⟨⟨hS, hc⟩, hP⟩ := h
  have hc' : fld Q ⊆ codom S := by
    intro z hz; rw [hc] at hz; obtain ⟨x, hx, -⟩ := hz; exact ⟨x, hx⟩
  have e : Pcl P = imgRel S ⁏ Pcl Q := by
    rw [hP, pm170_4 ⟨hS, hc⟩, pm170_41]
  apply pm170_aux_smorbar (img S)
  · intro G D hG hD
    exact pm170_aux_img_inj hS hc' (pm170_371 Q hG) (pm170_371 Q hD)
  · intro X Y
    rw [e, pm170_aux_imgRel_semi]
    exact ⟨fun ⟨G, D, ⟨h1, h2⟩, h3⟩ => ⟨G, D, h3, h1, h2⟩, fun ⟨G, D, h3, h1, h2⟩ => ⟨G, D, ⟨h1, h2⟩, h3⟩⟩

theorem pm170_aux_cres_codom {S : α → β → Prop} {Q : β → β → Prop} (h : fld Q = codom S) :
    S ↾ fld Q = S := by
  funext x z; apply propext
  exact ⟨fun h' => h'.1, fun h' => ⟨h', (by rw [h]; exact ⟨x, h'⟩)⟩⟩

/-- ✱170·44. \(\vdash : P\,\text{smor}\,Q.\supset .P_{\text{cl}}\,\text{smor}\,Q_{\text{cl}} \quad[*170·43.*151·23·12]\) -/
theorem pm170_44 {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q) : smor (Pcl P) (Pcl Q) := by
  obtain ⟨S, hS⟩ := h
  have hS' : S ↾ fld Q ∈ smorbar P Q := by rw [pm170_aux_cres_codom hS.1.2]; exact hS
  exact ⟨_, pm170_43 hS'⟩

theorem pm170_aux_fld_couple (x y : α) : fld (x ↓ y) = ι x ∪ ι y := by
  ext z; rw [pm170_aux_mem_fld_couple]; rfl

section Helpers170c
variable {α : Type u}

theorem pm170_aux_mem_iota {x y : α} : y ∈ ι x ↔ y = x := mem_unitCls

/-- `P_cl` of a couple `x ↓ y` (`x ≠ y`), in terms of memberships. -/
theorem pm170_aux_cl_couple {x y : α} (hxy : x ≠ y) {A B : Set α} :
    Pcl (x ↓ y) A B ↔ (A ⊆ ι x ∪ ι y ∧ B ⊆ ι x ∪ ι y) ∧
      ((x ∈ A ∧ x ∉ B) ∨ ((y ∈ A ∧ y ∉ B) ∧ (x ∈ B → x ∈ A))) := by
  rw [pm170_11, pm170_aux_fld_couple]
  constructor
  · rintro ⟨⟨hA, hB⟩, z, ⟨hzA, hzB⟩, h⟩
    refine ⟨⟨hA, hB⟩, ?_⟩
    rcases hA hzA with hz | hz <;> rw [pm170_aux_mem_iota] at hz <;> rw [hz] at hzA hzB h
    · exact Or.inl ⟨hzA, hzB⟩
    · exact Or.inr ⟨⟨hzA, hzB⟩, fun hxB => h ⟨⟨rfl, rfl⟩, hxB⟩⟩
  · rintro ⟨⟨hA, hB⟩, ⟨hxA, hxB⟩ | ⟨⟨hyA, hyB⟩, h⟩⟩
    · exact ⟨⟨hA, hB⟩, x, ⟨hxA, hxB⟩, fun w ⟨hw, _⟩ => absurd hw.2 hxy⟩
    · refine ⟨⟨hA, hB⟩, y, ⟨hyA, hyB⟩, fun w ⟨hw, hwB⟩ => ?_⟩
      have hw' : w = x := hw.1
      rw [hw'] at hwB ⊢; exact h hwB

theorem pm170_aux_eq_pair {x y : α} {A S : Set α} (hA : A ⊆ ι x ∪ ι y) (hS : S ⊆ ι x ∪ ι y) :
    A = S ↔ ((x ∈ A ↔ x ∈ S) ∧ (y ∈ A ↔ y ∈ S)) := by
  constructor
  · rintro rfl; exact ⟨Iff.rfl, Iff.rfl⟩
  · rintro ⟨h1, h2⟩
    ext z; constructor
    · intro hz
      rcases hA hz with hz' | hz' <;> rw [pm170_aux_mem_iota] at hz' <;> rw [hz'] at hz ⊢
      · exact h1.1 hz
      · exact h2.1 hz
    · intro hz
      rcases hS hz with hz' | hz' <;> rw [pm170_aux_mem_iota] at hz' <;> rw [hz'] at hz ⊢
      · exact h1.2 hz
      · exact h2.2 hz

theorem pm170_aux_pair_facts {x y : α} (hxy : x ≠ y) {A : Set α} (hA : A ⊆ ι x ∪ ι y) :
    ((A = ι x ∪ ι y ↔ x ∈ A ∧ y ∈ A) ∧ (A = ι x ↔ x ∈ A ∧ y ∉ A)) ∧
      ((A = ι y ↔ x ∉ A ∧ y ∈ A) ∧ (A = Λ ↔ x ∉ A ∧ y ∉ A)) := by
  have hx : x ∈ ι x := rfl
  have hy : y ∈ ι y := rfl
  have hyx : y ∉ ι x := fun h => hxy h.symm
  have hxy' : x ∉ ι y := fun h => hxy h
  have hN : ∀ z, z ∉ (Λ : Set α) := pm170_aux_Null
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [pm170_aux_eq_pair hA subset_rfl]
    exact ⟨fun h => ⟨h.1.2 (Or.inl hx), h.2.2 (Or.inr hy)⟩,
      fun h => ⟨⟨fun _ => Or.inl hx, fun _ => h.1⟩, ⟨fun _ => Or.inr hy, fun _ => h.2⟩⟩⟩
  · rw [pm170_aux_eq_pair hA Set.subset_union_left]
    exact ⟨fun h => ⟨h.1.2 hx, fun h' => hyx (h.2.1 h')⟩,
      fun h => ⟨⟨fun _ => hx, fun _ => h.1⟩, ⟨fun h' => absurd h' h.2, fun h' => absurd h' hyx⟩⟩⟩
  · rw [pm170_aux_eq_pair hA Set.subset_union_right]
    exact ⟨fun h => ⟨fun h' => hxy' (h.1.1 h'), h.2.2 hy⟩,
      fun h => ⟨⟨fun h' => absurd h' h.1, fun h' => absurd h' hxy'⟩, ⟨fun _ => hy, fun _ => h.2⟩⟩⟩
  · rw [pm170_aux_eq_pair hA (fun z hz => absurd hz (hN z))]
    exact ⟨fun h => ⟨fun h' => hN x (h.1.1 h'), fun h' => hN y (h.2.1 h')⟩,
      fun h => ⟨⟨fun h' => absurd h' h.1, fun h' => absurd h' (hN x)⟩,
        ⟨fun h' => absurd h' h.2, fun h' => absurd h' (hN y)⟩⟩⟩

theorem pm170_aux_taut51 (a b c d : Prop) : ((a ∧ ¬c) ∨ ((b ∧ ¬d) ∧ (c → a))) ↔
    (((((a ∧ b) ∧ (c ∧ ¬d) ∨ (a ∧ b) ∧ (¬c ∧ d)) ∨ (a ∧ b) ∧ (¬c ∧ ¬d)) ∨
      (a ∧ ¬b) ∧ (¬c ∧ d)) ∨ (a ∧ ¬b) ∧ (¬c ∧ ¬d)) ∨ (¬a ∧ b) ∧ (¬c ∧ ¬d) := by
  tauto

theorem pm170_aux_taut52 (p1 p2 p3 q1 q2 q3 : Prop) :
    (((((p1 ∧ q1) ∨ (p1 ∧ q2)) ∨ (p1 ∧ q3)) ∨ (p2 ∧ q2)) ∨ (p2 ∧ q3)) ∨ (p3 ∧ q3) ↔
    ((p1 ∧ q1) ∨ (p3 ∧ q3)) ∨ ((p1 ∨ p2) ∧ (q2 ∨ q3)) := by
  tauto

end Helpers170c

/-- ✱170·5. \(\vdash .(x\downarrow x)_{\text{cl}}=(\iota ʻx)\downarrow \Lambda \) -/
theorem pm170_5 (x : α) : Pcl (x ↓ x) = ι x ↓ Λ := by
  funext A B; apply propext
  show Pcl (x ↓ x) A B ↔ A ∈ ι (ι x) ∧ B ∈ ι Λ
  rw [pm170_aux_mem_iota, pm170_aux_mem_iota, pm170_11, pm170_aux_fld_couple, Set.union_self]
  constructor
  · rintro ⟨⟨hA, hB⟩, z, ⟨hzA, hzB⟩, h⟩
    have hz : z = x := hA hzA
    rw [hz] at hzA hzB h
    constructor
    · ext w; constructor
      · intro hw; exact hA hw
      · intro hw; rw [pm170_aux_mem_iota.1 hw]; exact hzA
    · ext w; constructor
      · intro hw; have : w = x := hB hw
        rw [this] at hw; exact absurd hw hzB
      · intro hw; exact absurd hw (pm170_aux_Null w)
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨(show ι x ⊆ ι x from subset_rfl), fun w hw => absurd hw (pm170_aux_Null w)⟩, x, ⟨rfl, pm170_aux_Null x⟩,
      fun w hw => absurd hw.2 (pm170_aux_Null w)⟩

/-- ✱170·51. \[\begin{align}\vdash :x\neq y.\supset .(x\downarrow y)_{\text{cl}}=(\iota ʻx\cup \iota ʻy)&\downarrow \iota ʻx\unicode{x228d} (\iota ʻx\cup \iota ʻy)\downarrow \iota ʻy\unicode{x228d} (\iota ʻx\cup \iota ʻy)\downarrow \Lambda \\ &\unicode{x228d} \iota ʻx\downarrow \iota ʻy\unicode{x228d} \iota ʻx\downarrow \Lambda \unicode{x228d} \iota ʻy\downarrow \Lambda\end{align}\] -/
theorem pm170_51 {x y : α} (hxy : x ≠ y) :
    Pcl (x ↓ y) = (ι x ∪ ι y) ↓ ι x ⊍ (ι x ∪ ι y) ↓ ι y ⊍ (ι x ∪ ι y) ↓ Λ ⊍ ι x ↓ ι y ⊍
      ι x ↓ Λ ⊍ ι y ↓ Λ := by
  funext A B; apply propext
  rw [pm170_aux_cl_couple hxy]
  show _ ↔ (((((A = ι x ∪ ι y ∧ B = ι x) ∨ (A = ι x ∪ ι y ∧ B = ι y)) ∨
    (A = ι x ∪ ι y ∧ B = Λ)) ∨ (A = ι x ∧ B = ι y)) ∨ (A = ι x ∧ B = Λ)) ∨ (A = ι y ∧ B = Λ)
  have hN : (Λ : Set α) ⊆ ι x ∪ ι y := fun z hz => absurd hz (pm170_aux_Null z)
  constructor
  · rintro ⟨⟨hA, hB⟩, h⟩
    obtain ⟨⟨a1, a2⟩, a3, a4⟩ := pm170_aux_pair_facts hxy hA
    obtain ⟨⟨b1, b2⟩, b3, b4⟩ := pm170_aux_pair_facts hxy hB
    rw [a1, a2, a3, b2, b3, b4]
    exact (pm170_aux_taut51 _ _ _ _).1 h
  · intro h
    have hAB : A ⊆ ι x ∪ ι y ∧ B ⊆ ι x ∪ ι y := by
      rcases h with (((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) |
        ⟨rfl, rfl⟩) <;>
      exact ⟨by first | exact hN | exact Set.subset_union_left |
          exact Set.subset_union_right | exact subset_rfl,
        by first | exact hN | exact Set.subset_union_left |
          exact Set.subset_union_right | exact subset_rfl⟩
    refine ⟨hAB, ?_⟩
    obtain ⟨⟨a1, a2⟩, a3, a4⟩ := pm170_aux_pair_facts hxy hAB.1
    obtain ⟨⟨b1, b2⟩, b3, b4⟩ := pm170_aux_pair_facts hxy hAB.2
    rw [a1, a2, a3, b2, b3, b4] at h
    exact (pm170_aux_taut51 _ _ _ _).2 h

/-- ✱170·52. \(\vdash :x\neq y.\supset .(x\downarrow y)_{\text{cl}}=(\iota ʻx\cup \iota ʻy)\downarrow \iota ʻx\unicode{x2909}\iota ʻy\downarrow \Lambda\) -/
theorem pm170_52 {x y : α} (hxy : x ≠ y) :
    Pcl (x ↓ y) = (ι x ∪ ι y) ↓ ι x ⤉ ι y ↓ Λ := by
  rw [pm170_51 hxy]
  funext A B; apply propext
  rw [rsum_apply, pm170_aux_mem_fld_couple, pm170_aux_mem_fld_couple]
  show (((((A = ι x ∪ ι y ∧ B = ι x) ∨ (A = ι x ∪ ι y ∧ B = ι y)) ∨
    (A = ι x ∪ ι y ∧ B = Λ)) ∨ (A = ι x ∧ B = ι y)) ∨ (A = ι x ∧ B = Λ)) ∨ (A = ι y ∧ B = Λ) ↔
    ((A = ι x ∪ ι y ∧ B = ι x) ∨ (A = ι y ∧ B = Λ)) ∨
      ((A = ι x ∪ ι y ∨ A = ι x) ∧ (B = ι y ∨ B = Λ))
  exact pm170_aux_taut52 _ _ _ _ _ _

/-- ✱170·6. \(\vdash :\Lambda P_{\text{lc}}\beta .\equiv .\beta \subset CʻP.\exists !\beta \quad[*170·32·101]\) -/
theorem pm170_6 {P : α → α → Prop} {B : Set α} : Plc P Λ B ↔ B ⊆ fld P ∧ B.Nonempty := by
  show Pcl P˘ B Λ ↔ _
  rw [← pm170_32, pm170_aux_fld_cnv]

/-- ✱170·601. \(\vdash :\alpha P_{\text{lc}}(CʻP).\equiv .\alpha \subset CʻP.\alpha \neq CʻP \quad[*170·31·101]\) -/
theorem pm170_601 {P : α → α → Prop} {A : Set α} : Plc P A (fld P) ↔ A ⊆ fld P ∧ A ≠ fld P := by
  show Pcl P˘ (fld P) A ↔ _
  have := (pm170_31 (P := P˘) (B := A)).symm
  rw [pm170_aux_fld_cnv] at this
  exact this

section Helpers170d
variable {α : Type u}

theorem pm170_aux_fld_addFirst_sub (x : α) (P : α → α → Prop) : fld (x ⇷ P) ⊆ ι x ∪ fld P := by
  rintro a ⟨b, (⟨h, -⟩ | h) | (⟨-, h⟩ | h)⟩
  · exact Or.inl h
  · exact Or.inr ⟨b, Or.inl h⟩
  · exact Or.inr h
  · exact Or.inr ⟨b, Or.inr h⟩

theorem pm170_aux_sub_fld_addFirst (x : α) (P : α → α → Prop) : fld P ⊆ fld (x ⇷ P) := by
  rintro a ⟨b, h | h⟩
  · exact ⟨b, Or.inl (Or.inr h)⟩
  · exact ⟨b, Or.inr (Or.inr h)⟩

theorem pm170_aux_fld_addFirst {x : α} {P : α → α → Prop} (h : rEx P) :
    fld (x ⇷ P) = ι x ∪ fld P := by
  refine Set.Subset.antisymm (pm170_aux_fld_addFirst_sub x P) ?_
  rintro a (ha | ha)
  · obtain ⟨b, hb⟩ := pm170_aux_rEx_iff_fld.1 h
    rw [pm170_aux_mem_iota.1 ha]; exact ⟨b, Or.inl (Or.inl ⟨rfl, hb⟩)⟩
  · exact pm170_aux_sub_fld_addFirst x P ha

theorem pm170_aux_union_diff {x : α} {G : Set α} (h : x ∉ G) : (ι x ∪ G) \ ι x = G := by
  ext w; constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd h1 h2
    · exact h1
  · intro hw
    exact ⟨Or.inr hw, fun h' => h ((pm170_aux_mem_iota.1 h') ▸ hw)⟩

theorem pm170_aux_union_diff' {x : α} {A : Set α} (h : x ∈ A) : A = ι x ∪ (A \ ι x) := by
  ext w; constructor
  · intro hw
    by_cases hwx : w ∈ ι x
    · exact Or.inl hwx
    · exact Or.inr ⟨hw, hwx⟩
  · rintro (h1 | h1)
    · rw [pm170_aux_mem_iota.1 h1]; exact h
    · exact h1.1

theorem pm170_aux_opL_union_semi (x : α) (R : Set α → Set α → Prop) (A B : Set α) :
    (opL (· ∪ ·) (ι x) ⁏ R) A B ↔ ∃ G D, (A = ι x ∪ G ∧ B = ι x ∪ D) ∧ R G D :=
  semi_graph_apply (fun G : Set α => ι x ∪ G) R A B

end Helpers170d

/-- ✱170·61. \[\begin{align}\vdash \colon\ldotp x{\sim}&\in CʻP.\dot{\exists} !P.x\in \alpha \cap \beta .\supset :\\ &\alpha (x\unicode{x21f7}P)_{\text{cl}}\beta .\equiv .\alpha \{(\iota ʻx\cup )^{;}P_{\text{cl}}\}\beta .\equiv .(\alpha -\iota ʻx)P_{\text{cl}}(\beta -\iota ʻx)\end{align}\] -/
theorem pm170_61 {P : α → α → Prop} {x : α} {A B : Set α}
    (h : (x ∉ fld P ∧ rEx P) ∧ x ∈ A ∩ B) :
    (Pcl (x ⇷ P) A B ↔ (opL (· ∪ ·) (ι x) ⁏ Pcl P) A B) ∧
      ((opL (· ∪ ·) (ι x) ⁏ Pcl P) A B ↔ Pcl P (A \ ι x) (B \ ι x)) := by
  obtain ⟨⟨hx, hP⟩, hxA, hxB⟩ := h
  have h2 : (opL (· ∪ ·) (ι x) ⁏ Pcl P) A B ↔ Pcl P (A \ ι x) (B \ ι x) := by
    rw [pm170_aux_opL_union_semi]
    constructor
    · rintro ⟨G, D, ⟨rfl, rfl⟩, hGD⟩
      rwa [pm170_aux_union_diff (fun h' => hx (hGD.1.1 h')),
        pm170_aux_union_diff (fun h' => hx (hGD.1.2 h'))]
    · intro hGD
      exact ⟨A \ ι x, B \ ι x, ⟨pm170_aux_union_diff' hxA, pm170_aux_union_diff' hxB⟩, hGD⟩
  refine ⟨?_, h2⟩
  rw [h2, pm170_11, pm170_11]
  have hsub : ∀ C : Set α, C ⊆ fld (x ⇷ P) ↔ C \ ι x ⊆ fld P := by
    intro C; constructor
    · rintro hC w ⟨hwC, hwx⟩
      rcases pm170_aux_fld_addFirst_sub x P (hC hwC) with h' | h'
      · exact absurd h' hwx
      · exact h'
    · intro hC w hw
      rw [pm170_aux_fld_addFirst hP]
      by_cases hwx : w ∈ ι x
      · exact Or.inl hwx
      · exact Or.inr (hC ⟨hw, hwx⟩)
  constructor
  · rintro ⟨⟨hA, hB⟩, z, ⟨hzA, hzB⟩, hz⟩
    have hzx : z ∉ ι x := fun h' => hzB ((pm170_aux_mem_iota.1 h') ▸ hxB)
    refine ⟨⟨(hsub A).1 hA, (hsub B).1 hB⟩, z, ⟨⟨hzA, hzx⟩, fun h' => hzB h'.1⟩, ?_⟩
    rintro w ⟨hwz, hwB, hwx⟩
    exact ⟨hz ⟨Or.inr hwz, hwB⟩, hwx⟩
  · rintro ⟨⟨hA, hB⟩, z, ⟨⟨hzA, hzx⟩, hzB⟩, hz⟩
    refine ⟨⟨(hsub A).2 hA, (hsub B).2 hB⟩, z, ⟨hzA, fun h' => hzB ⟨h', hzx⟩⟩, ?_⟩
    rintro w ⟨hwz, hwB⟩
    by_cases hwx : w ∈ ι x
    · rw [pm170_aux_mem_iota.1 hwx]; exact hxA
    · rcases hwz with ⟨hw, -⟩ | hwz
      · exact absurd (pm170_aux_mem_iota.2 hw) hwx
      · exact (hz ⟨hwz, hwB, hwx⟩).1

/-- ✱170·62. \[\begin{align}\vdash \colon\ldotp x{\sim}\in CʻP.\dot{\exists} !P.x\in &\alpha -\beta .\supset :\\ &\alpha (x\unicode{x21f7}P)_{\text{cl}}\beta .\equiv .\alpha \subset \iota ʻx\cup CʻP.\beta \subset CʻP\end{align}\] -/
theorem pm170_62 {P : α → α → Prop} {x : α} {A B : Set α}
    (h : (x ∉ fld P ∧ rEx P) ∧ x ∈ A \ B) :
    Pcl (x ⇷ P) A B ↔ A ⊆ ι x ∪ fld P ∧ B ⊆ fld P := by
  obtain ⟨⟨hx, hP⟩, hxA, hxB⟩ := h
  rw [pm170_11, pm170_aux_fld_addFirst hP]
  constructor
  · rintro ⟨⟨hA, hB⟩, -⟩
    refine ⟨hA, fun w hw => ?_⟩
    rcases hB hw with h' | h'
    · rw [pm170_aux_mem_iota.1 h'] at hw; exact absurd hw hxB
    · exact h'
  · rintro ⟨hA, hB⟩
    refine ⟨⟨hA, hB.trans Set.subset_union_right⟩, x, ⟨hxA, hxB⟩, ?_⟩
    rintro w ⟨⟨-, h'⟩ | h', -⟩
    · exact absurd h' hx
    · exact (hx ⟨w, Or.inr h'⟩).elim

/-- ✱170·63. \(\vdash \colon\ldotp x{\sim}\in (\alpha \cup \beta ).\supset :\alpha (x\unicode{x21f7}P)_{\text{cl}}\beta .\equiv .\alpha P_{\text{cl}}\beta\) -/
theorem pm170_63 {P : α → α → Prop} {x : α} {A B : Set α} (h : x ∉ A ∪ B) :
    Pcl (x ⇷ P) A B ↔ Pcl P A B := by
  have hxA : x ∉ A := fun h' => h (Or.inl h')
  have hxB : x ∉ B := fun h' => h (Or.inr h')
  have hsub : ∀ C : Set α, x ∉ C → (C ⊆ fld (x ⇷ P) ↔ C ⊆ fld P) := by
    intro C hC; constructor
    · intro h' w hw
      rcases pm170_aux_fld_addFirst_sub x P (h' hw) with h'' | h''
      · rw [pm170_aux_mem_iota.1 h''] at hw; exact absurd hw hC
      · exact h''
    · intro h'; exact h'.trans (pm170_aux_sub_fld_addFirst x P)
  rw [pm170_11, pm170_11]
  refine and_congr (and_congr (hsub A hxA) (hsub B hxB)) (exists_congr fun z => and_congr Iff.rfl ?_)
  constructor
  · rintro h' w ⟨hw, hwB⟩; exact h' ⟨Or.inr hw, hwB⟩
  · rintro h' w ⟨⟨hw, -⟩ | hw, hwB⟩
    · rw [hw] at hwB; exact absurd hwB hxB
    · exact h' ⟨hw, hwB⟩

/-- ✱170·64. \(\vdash :x{\sim}\in CʻP.\supset .(x\unicode{x21f7}P)_{\text{cl}}=(\iota ʻx\cup )^{;}P_{\text{cl}}\unicode{x2909}P_{\text{cl}}\) -/
theorem pm170_64 {P : α → α → Prop} {x : α} (hx : x ∉ fld P) :
    Pcl (x ⇷ P) = (opL (· ∪ ·) (ι x) ⁏ Pcl P) ⤉ Pcl P := by
  by_cases hP : rEx P
  · have hfld1 : fld (opL (· ∪ ·) (ι x) ⁏ Pcl P) = {A | ∃ G, G ∈ cl (fld P) ∧ A = ι x ∪ G} := by
      have := fld_semi_graph (fun G : Set α => ι x ∪ G) (Pcl P)
      rw [pm170_37 hP] at this
      exact this
    funext A B; apply propext
    rw [rsum_apply, hfld1, pm170_37 hP]
    by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B
    · rw [(pm170_61 ⟨⟨hx, hP⟩, hxA, hxB⟩).1]
      constructor
      · intro h'; exact Or.inl (Or.inl h')
      · rintro ((h' | ⟨⟨hA, -⟩, -⟩) | ⟨-, hB⟩)
        · exact h'
        · exact absurd (hA hxA) hx
        · exact absurd (hB hxB) hx
    · rw [pm170_62 ⟨⟨hx, hP⟩, hxA, hxB⟩]
      constructor
      · rintro ⟨hA, hB⟩
        refine Or.inr ⟨⟨A \ ι x, ?_, pm170_aux_union_diff' hxA⟩, hB⟩
        rintro w ⟨hw, hwx⟩
        rcases hA hw with h' | h'
        · exact absurd h' hwx
        · exact h'
      · rintro ((h' | ⟨⟨hA, -⟩, -⟩) | ⟨⟨G, hG, rfl⟩, hB⟩)
        · obtain ⟨G, D, ⟨-, rfl⟩, -⟩ := (pm170_aux_opL_union_semi x _ A B).1 h'
          exact (hxB (Or.inl rfl)).elim
        · exact absurd (hA hxA) hx
        · exact ⟨Set.union_subset_union_right _ hG, hB⟩
    · constructor
      · intro h'
        obtain ⟨⟨hA, -⟩, z, ⟨hzA, hzB⟩, hz⟩ := pm170_11.1 h'
        have hz' : z ∈ fld P := by
          rcases pm170_aux_fld_addFirst_sub x P (hA hzA) with h' | h'
          · rw [pm170_aux_mem_iota.1 h'] at hzA; exact absurd hzA hxA
          · exact h'
        exact (hxA (hz (a := x) ⟨Or.inl ⟨rfl, hz'⟩, hxB⟩)).elim
      · rintro ((h' | ⟨⟨-, hB⟩, -⟩) | ⟨⟨G, -, rfl⟩, -⟩)
        · obtain ⟨G, D, ⟨rfl, -⟩, -⟩ := (pm170_aux_opL_union_semi x _ A B).1 h'
          exact (hxA (Or.inl rfl)).elim
        · exact absurd (hB hxB) hx
        · exact (hxA (Or.inl rfl)).elim
    · rw [pm170_63 (fun h' => h'.elim hxA hxB)]
      constructor
      · intro h'; exact Or.inl (Or.inr h')
      · rintro ((h' | h') | ⟨⟨G, -, rfl⟩, -⟩)
        · obtain ⟨G, D, ⟨rfl, -⟩, -⟩ := (pm170_aux_opL_union_semi x _ A B).1 h'
          exact (hxA (Or.inl rfl)).elim
        · exact h'
        · exact (hxA (Or.inl rfl)).elim
  · have hPcl : ∀ A B, ¬ Pcl P A B := fun A B h' => hP (pm170_34.2 ⟨A, B, h'⟩)
    funext A B; apply propext
    rw [rsum_apply]
    constructor
    · intro h'
      obtain ⟨a, b, hab⟩ := pm170_34.2 ⟨A, B, h'⟩
      rcases hab with ⟨-, hb⟩ | hab
      · exact absurd (pm170_aux_rEx_iff_fld.2 ⟨b, hb⟩) hP
      · exact (hP ⟨a, b, hab⟩).elim
    · rintro ((h' | h') | ⟨-, ⟨C, hC | hC⟩⟩)
      · obtain ⟨G, D, -, h''⟩ := (pm170_aux_opL_union_semi x _ A B).1 h'
        exact absurd h'' (hPcl G D)
      · exact absurd h' (hPcl A B)
      · exact absurd hC (hPcl B C)
      · exact absurd hC (hPcl C B)

section Helpers170e
variable {α : Type u} {β : Type v} {γ : Type w}

theorem pm170_aux_rtimes_couple (Q : β → β → Prop) (P : α → α → Prop) (x y : α) (z w : β) :
    (Q ×ᵣ P) (x ↓ z) (y ↓ w) ↔
      (z ∈ fld Q ∧ z = w ∧ P x y) ∨ (Q z w ∧ x ∈ fld P ∧ y ∈ fld P) := by
  rw [rtimes_apply]
  constructor
  · rintro (⟨z', hz', a, b, ⟨h1, h2⟩, hab⟩ | ⟨z', w', hzw, a, b, ⟨ha, hb⟩, h1, h2⟩)
    · rw [couple_eq_couple_iff] at h1 h2
      obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
      exact Or.inl ⟨hz', rfl, hab⟩
    · rw [couple_eq_couple_iff] at h1 h2
      obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
      exact Or.inr ⟨hzw, ha, hb⟩
  · rintro (⟨hz, rfl, hxy⟩ | ⟨hzw, hx, hy⟩)
    · exact Or.inl ⟨z, hz, x, y, ⟨rfl, rfl⟩, hxy⟩
    · exact Or.inr ⟨z, w, hzw, x, y, ⟨hx, hy⟩, rfl, rfl⟩

theorem pm170_aux_fld_rtimes {Q : β → β → Prop} {P : α → α → Prop} {u : α → β → Prop}
    (hu : u ∈ fld (Q ×ᵣ P)) : ∃ x z, (x ∈ fld P ∧ z ∈ fld Q) ∧ u = x ↓ z := by
  obtain ⟨v, h | h⟩ := hu
  · rcases (rtimes_apply Q P u v).1 h with ⟨z, hz, a, b, ⟨rfl, -⟩, hab⟩ |
      ⟨z, w, hzw, a, b, ⟨ha, -⟩, rfl, -⟩
    · exact ⟨a, z, ⟨⟨b, Or.inl hab⟩, hz⟩, rfl⟩
    · exact ⟨a, z, ⟨ha, ⟨w, Or.inl hzw⟩⟩, rfl⟩
  · rcases (rtimes_apply Q P v u).1 h with ⟨z, hz, a, b, ⟨-, rfl⟩, hab⟩ |
      ⟨z, w, hzw, a, b, ⟨-, hb⟩, -, rfl⟩
    · exact ⟨b, z, ⟨⟨a, Or.inr hab⟩, hz⟩, rfl⟩
    · exact ⟨b, w, ⟨hb, ⟨z, Or.inr hzw⟩⟩, rfl⟩

theorem pm170_aux_sRel_C :
    (sRel ⨾ C : Set α → (Set α → Set α → Prop) → Prop) = graph (fun U => sumCls (fld U)) := by
  funext ρ U; apply propext
  constructor
  · rintro ⟨K, h1, h2⟩
    show ρ = sumCls (fld U)
    rw [show ρ = sumCls K from h1, show K = fld U from h2]
  · intro h; exact ⟨fld U, h, rfl⟩

theorem pm170_aux_sumCls_fld_couple (G A : Set α) : sumCls (fld (G ↓ A)) = A ∪ G := by
  ext w; constructor
  · rintro ⟨Z, hZ, hw⟩
    rcases pm170_aux_mem_fld_couple.1 hZ with rfl | rfl
    · exact Or.inr hw
    · exact Or.inl hw
  · rintro (hw | hw)
    · exact ⟨A, pm170_aux_mem_fld_couple.2 (Or.inr rfl), hw⟩
    · exact ⟨G, pm170_aux_mem_fld_couple.2 (Or.inl rfl), hw⟩

theorem pm170_aux_disj {P Q : α → α → Prop} (h : fld P ∩ fld Q = Λ) {z : α} (hP : z ∈ fld P) :
    z ∉ fld Q := fun hQ => by
  have : z ∈ fld P ∩ fld Q := ⟨hP, hQ⟩
  rw [h] at this; exact pm170_aux_Null z this

end Helpers170e

/-- ✱170·65. \[\begin{align}&\vdash \colon\ldotp \rho (P\unicode{x2909}Q)_{\text{cl}}\sigma .\equiv :(\exists \alpha ,\beta ,\gamma ,\delta ):\alpha ,\beta \in \text{Cl}ʻCʻP.\gamma ,\delta \in \text{Cl}ʻCʻQ.\\ &\rho =\alpha \cup \gamma .\sigma =\beta \cup \delta :(\exists y).y\in (\alpha \cup \gamma )-(\beta \cup \delta ).\overrightarrow{P\unicode{x2909}Q} ʻy\cap (\beta \cup \delta )\subset \alpha \cup \gamma \end{align}\] -/
theorem pm170_65 {P Q : α → α → Prop} {ρ σ : Set α} :
    Pcl (P ⤉ Q) ρ σ ↔ ∃ A B G D, ((((A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧
      (G ∈ cl (fld Q) ∧ D ∈ cl (fld Q))) ∧ ρ = A ∪ G) ∧ σ = B ∪ D) ∧
      ∃ y, y ∈ (A ∪ G) \ (B ∪ D) ∧ refs (P ⤉ Q) y ∩ (B ∪ D) ⊆ A ∪ G := by
  rw [pm170_11, fld_rsum]
  constructor
  · rintro ⟨⟨hρ, hσ⟩, y, hy, h⟩
    have e : ∀ X : Set α, X ⊆ fld P ∪ fld Q → X = X ∩ fld P ∪ X ∩ fld Q := fun X hX => by
      rw [← Set.inter_union_distrib_left, Set.inter_eq_left.2 hX]
    refine ⟨ρ ∩ fld P, σ ∩ fld P, ρ ∩ fld Q, σ ∩ fld Q, ⟨⟨⟨⟨Set.inter_subset_right,
      Set.inter_subset_right⟩, ⟨Set.inter_subset_right, Set.inter_subset_right⟩⟩, e ρ hρ⟩,
      e σ hσ⟩, y, ?_⟩
    rw [← e ρ hρ, ← e σ hσ]; exact ⟨hy, h⟩
  · rintro ⟨A, B, G, D, ⟨⟨⟨⟨hA, hB⟩, hG, hD⟩, rfl⟩, rfl⟩, y, hy, h⟩
    exact ⟨⟨Set.union_subset_union hA hG, Set.union_subset_union hB hD⟩, y, hy, h⟩

/-- ✱170·651. \[\begin{align}&\vdash \colon\ldotp CʻP\cap CʻQ=\Lambda .\alpha ,\beta \in \text{Cl}ʻCʻP.\gamma ,\delta \in \text{Cl}ʻCʻQ.y\in \alpha .\supset :\\ &y\in (\alpha \cup \gamma )-(\beta \cup \delta ).\overrightarrow{P\unicode{x2909}Q} ʻy\cap (\beta \cup \delta )\subset \alpha \cup \gamma .\equiv .y\in \alpha -\beta .\overrightarrow{P}ʻy\cap \beta \subset \alpha \end{align}\] -/
theorem pm170_651 {P Q : α → α → Prop} {A B G D : Set α} {y : α}
    (h : ((fld P ∩ fld Q = Λ ∧ (A ∈ cl (fld P) ∧ B ∈ cl (fld P))) ∧
      (G ∈ cl (fld Q) ∧ D ∈ cl (fld Q))) ∧ y ∈ A) :
    (y ∈ (A ∪ G) \ (B ∪ D) ∧ refs (P ⤉ Q) y ∩ (B ∪ D) ⊆ A ∪ G) ↔
      (y ∈ A \ B ∧ refs P y ∩ B ⊆ A) := by
  obtain ⟨⟨⟨hd, hA, hB⟩, hG, hD⟩, hyA⟩ := h
  have hyQ : y ∉ fld Q := pm170_aux_disj hd (hA hyA)
  constructor
  · rintro ⟨⟨-, hyBD⟩, h⟩
    refine ⟨⟨hyA, fun h' => hyBD (Or.inl h')⟩, fun w ⟨hw, hwB⟩ => ?_⟩
    rcases h ⟨Or.inl (Or.inl hw), Or.inl hwB⟩ with h' | h'
    · exact h'
    · exact absurd (hG h') (pm170_aux_disj hd (hB hwB))
  · rintro ⟨⟨-, hyB⟩, h⟩
    refine ⟨⟨Or.inl hyA, ?_⟩, ?_⟩
    · rintro (h' | h')
      · exact hyB h'
      · exact hyQ (hD h')
    · rintro w ⟨(hw | hw) | ⟨-, hy⟩, hwBD⟩
      · rcases hwBD with hwB | hwD
        · exact Or.inl (h ⟨hw, hwB⟩)
        · exact absurd (hD hwD) (pm170_aux_disj hd ⟨y, Or.inl hw⟩)
      · exact absurd ⟨w, Or.inr hw⟩ hyQ
      · exact absurd hy hyQ

/-- ✱170·652. \[\begin{align}\vdash \colon\ldotp CʻP\cap &CʻQ=\Lambda .\alpha ,\beta \in \text{Cl}ʻCʻP.\gamma ,\delta \in \text{Cl}ʻCʻQ.y\in \gamma .\supset :\\ &y\in (\alpha \cup \gamma )-(\beta \cup \delta ).\overrightarrow{P\unicode{x2909}Q} ʻy\cap (\beta \cup \delta )\subset \alpha \cup \gamma .\equiv .\\ &\beta \subset \alpha .y\in \gamma -\delta .\overrightarrow{Q}ʻy\cap \delta \subset \gamma\end{align}\] -/
theorem pm170_652 {P Q : α → α → Prop} {A B G D : Set α} {y : α}
    (h : ((fld P ∩ fld Q = Λ ∧ (A ∈ cl (fld P) ∧ B ∈ cl (fld P))) ∧
      (G ∈ cl (fld Q) ∧ D ∈ cl (fld Q))) ∧ y ∈ G) :
    (y ∈ (A ∪ G) \ (B ∪ D) ∧ refs (P ⤉ Q) y ∩ (B ∪ D) ⊆ A ∪ G) ↔
      ((B ⊆ A ∧ y ∈ G \ D) ∧ refs Q y ∩ D ⊆ G) := by
  obtain ⟨⟨⟨hd, hA, hB⟩, hG, hD⟩, hyG⟩ := h
  have hyP : y ∉ fld P := fun h' => pm170_aux_disj hd h' (hG hyG)
  constructor
  · rintro ⟨⟨-, hyBD⟩, h⟩
    refine ⟨⟨fun w hwB => ?_, hyG, fun h' => hyBD (Or.inr h')⟩, fun w ⟨hw, hwD⟩ => ?_⟩
    · rcases h ⟨Or.inr ⟨hB hwB, hG hyG⟩, Or.inl hwB⟩ with h' | h'
      · exact h'
      · exact absurd (hG h') (pm170_aux_disj hd (hB hwB))
    · rcases h ⟨Or.inl (Or.inr hw), Or.inr hwD⟩ with h' | h'
      · exact absurd (hD hwD) (pm170_aux_disj hd (hA h'))
      · exact h'
  · rintro ⟨⟨hBA, hyG', hyD⟩, h⟩
    refine ⟨⟨Or.inr hyG, ?_⟩, ?_⟩
    · rintro (h' | h')
      · exact hyP (hB h')
      · exact hyD h'
    · rintro w ⟨(hw | hw) | ⟨hw, -⟩, hwBD⟩
      · exact absurd ⟨w, Or.inr hw⟩ hyP
      · rcases hwBD with hwB | hwD
        · exact Or.inl (hBA hwB)
        · exact Or.inr (h ⟨hw, hwD⟩)
      · rcases hwBD with hwB | hwD
        · exact Or.inl (hBA hwB)
        · exact absurd (hD hwD) (pm170_aux_disj hd hw)

/-- ✱170·653. \[\begin{align}\vdash \colon\colon CʻP\cap CʻQ&=\Lambda .\alpha ,\beta \in \text{Cl}ʻCʻP.\gamma ,\delta \in \text{Cl}ʻCʻQ.\supset \colon\ldotp \\ &(\alpha \cup \gamma )(P\unicode{x2909}Q)_{\text{cl}}(\beta \cup \delta ).\equiv :\alpha P_{\text{cl}}\beta .\lor.\alpha =\beta .\gamma Q_{\text{cl}}\delta\end{align}\] -/
theorem pm170_653 {P Q : α → α → Prop} {A B G D : Set α}
    (h : (fld P ∩ fld Q = Λ ∧ (A ∈ cl (fld P) ∧ B ∈ cl (fld P))) ∧
      (G ∈ cl (fld Q) ∧ D ∈ cl (fld Q))) :
    Pcl (P ⤉ Q) (A ∪ G) (B ∪ D) ↔ Pcl P A B ∨ (A = B ∧ Pcl Q G D) := by
  obtain ⟨⟨hd, hA, hB⟩, hG, hD⟩ := h
  have hcl : (A ∪ G ∈ cl (fld (P ⤉ Q)) ∧ B ∪ D ∈ cl (fld (P ⤉ Q))) := by
    rw [fld_rsum]; exact ⟨Set.union_subset_union hA hG, Set.union_subset_union hB hD⟩
  rw [pm170_11 (P := P ⤉ Q)]
  constructor
  · rintro ⟨-, y, hy, h⟩
    rcases hy.1 with hyA | hyG
    · obtain ⟨hy', h'⟩ := (pm170_651 ⟨⟨⟨hd, hA, hB⟩, hG, hD⟩, hyA⟩).1 ⟨hy, h⟩
      exact Or.inl (pm170_11.2 ⟨⟨hA, hB⟩, y, hy', h'⟩)
    · obtain ⟨⟨hBA, hy'⟩, h'⟩ := (pm170_652 ⟨⟨⟨hd, hA, hB⟩, hG, hD⟩, hyG⟩).1 ⟨hy, h⟩
      by_cases e : B = A
      · exact Or.inr ⟨e.symm, pm170_11.2 ⟨⟨hG, hD⟩, y, hy', h'⟩⟩
      · exact Or.inl (pm170_16 ⟨⟨hA, hBA⟩, e⟩)
  · rintro (h' | ⟨rfl, h'⟩)
    · obtain ⟨-, y, hy, h''⟩ := pm170_11.1 h'
      exact ⟨hcl, y, (pm170_651 ⟨⟨⟨hd, hA, hB⟩, hG, hD⟩, hy.1⟩).2 ⟨hy, h''⟩⟩
    · obtain ⟨-, y, hy, h''⟩ := pm170_11.1 h'
      exact ⟨hcl, y, (pm170_652 ⟨⟨⟨hd, hA, hB⟩, hG, hD⟩, hy.1⟩).2 ⟨⟨subset_rfl, hy⟩, h''⟩⟩

/-- ✱170·66. \[\begin{align}&\vdash \colon\ldotp \dot{\exists} !P.\dot{\exists} !Q.CʻP\cap CʻQ=\Lambda .\supset :\\ &\rho (P\unicode{x2909}Q)\sigma .\equiv .(\exists \alpha ,\beta ,\gamma ,\delta ).(\gamma \downarrow \alpha )(P_{\text{cl}}\times Q_{\text{cl}})(\delta \downarrow \beta ).\rho =\alpha \cup \gamma .\sigma =\beta \cup \delta\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `ρ(P ⤉ Q)σ` on the left; PM's
demonstration (from ✱170·65·11·653 and ✱166·112) proves `ρ(P ⤉ Q)_clσ`, which is what is stated (the
printed form would be false: its left side is a relation between members of `C'P ∪ C'Q`, its right
side a relation between sub-classes). -/
theorem pm170_66 {P Q : α → α → Prop} {ρ σ : Set α}
    (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) :
    Pcl (P ⤉ Q) ρ σ ↔ ∃ A B G D, ((Pcl P ×ᵣ Pcl Q) (G ↓ A) (D ↓ B) ∧ ρ = A ∪ G) ∧ σ = B ∪ D := by
  obtain ⟨⟨hP, hQ⟩, hd⟩ := h
  constructor
  · intro h'
    obtain ⟨A, B, G, D, ⟨⟨⟨⟨hA, hB⟩, hG, hD⟩, rfl⟩, rfl⟩, -⟩ := pm170_65.1 h'
    refine ⟨A, B, G, D, ⟨?_, rfl⟩, rfl⟩
    rw [pm170_aux_rtimes_couple, pm170_37 hP, pm170_37 hQ]
    rcases (pm170_653 ⟨⟨hd, hA, hB⟩, hG, hD⟩).1 h' with h'' | ⟨rfl, h''⟩
    · exact Or.inr ⟨h'', hG, hD⟩
    · exact Or.inl ⟨hA, rfl, h''⟩
  · rintro ⟨A, B, G, D, ⟨hr, rfl⟩, rfl⟩
    rw [pm170_aux_rtimes_couple, pm170_37 hP, pm170_37 hQ] at hr
    rcases hr with ⟨hA, rfl, h''⟩ | ⟨h'', hG, hD⟩
    · exact (pm170_653 ⟨⟨hd, hA, hA⟩, h''.1⟩).2 (Or.inr ⟨rfl, h''⟩)
    · exact (pm170_653 ⟨⟨hd, h''.1⟩, hG, hD⟩).2 (Or.inl h'')

/-- ✱170·67. \(\vdash :\dot{\exists} !P.\dot{\exists} !Q.CʻP\cap CʻQ=\Lambda .\supset .(P\unicode{x2909}Q)_{\text{cl}}=s^{;}C^{;}(P_{\text{cl}}\times Q_{\text{cl}})\) -/
theorem pm170_67 {P Q : α → α → Prop} (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) :
    Pcl (P ⤉ Q) = sRel ⁏ C ⁏ (Pcl P ×ᵣ Pcl Q) := by
  rw [semi_semi, pm170_aux_sRel_C]
  funext ρ σ; apply propext
  rw [semi_graph_apply, pm170_66 h]
  constructor
  · rintro ⟨A, B, G, D, ⟨hr, rfl⟩, rfl⟩
    exact ⟨G ↓ A, D ↓ B, ⟨(pm170_aux_sumCls_fld_couple G A).symm,
      (pm170_aux_sumCls_fld_couple D B).symm⟩, hr⟩
  · rintro ⟨U, V, ⟨rfl, rfl⟩, hr⟩
    obtain ⟨G, A, -, rfl⟩ := pm170_aux_fld_rtimes ⟨V, Or.inl hr⟩
    obtain ⟨D, B, -, rfl⟩ := pm170_aux_fld_rtimes ⟨_, Or.inr hr⟩
    exact ⟨A, B, G, D, ⟨hr, pm170_aux_sumCls_fld_couple G A⟩, pm170_aux_sumCls_fld_couple D B⟩

/-- ✱170·68. \[\begin{align}\vdash :\dot{\exists} !P.\dot{\exists} !Q.CʻP&\cap CʻQ=\Lambda .\supset .\\ &(s\mid C)\upharpoonright Cʻ(P_{\text{cl}}\times Q_{\text{cl}})\in (P\unicode{x2909}Q)_{\text{cl}}\,\overline{\text{smor}}\,(P_{\text{cl}}\times Q_{\text{cl}})\end{align}\] -/
theorem pm170_68 {P Q : α → α → Prop} (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) :
    (sRel ⨾ C) ↾ fld (Pcl P ×ᵣ Pcl Q) ∈ smorbar (Pcl (P ⤉ Q)) (Pcl P ×ᵣ Pcl Q) := by
  rw [pm170_aux_sRel_C]
  apply pm170_aux_smorbar
  · intro U V hU hV e
    obtain ⟨G, A, ⟨hG, hA⟩, rfl⟩ := pm170_aux_fld_rtimes hU
    obtain ⟨D, B, ⟨hD, hB⟩, rfl⟩ := pm170_aux_fld_rtimes hV
    simp only [pm170_aux_sumCls_fld_couple] at e
    have hG' := pm170_371 Q hG
    have hD' := pm170_371 Q hD
    have hA' := pm170_371 P hA
    have hB' := pm170_371 P hB
    have key : ∀ (X Y : Set α), X ⊆ fld P → Y ⊆ fld Q → (X ∪ Y) ∩ fld P = X ∧ (X ∪ Y) ∩ fld Q = Y := by
      intro X Y hX hY
      constructor
      · ext z; constructor
        · rintro ⟨hz | hz, hzP⟩
          · exact hz
          · exact absurd (hY hz) (pm170_aux_disj h.2 hzP)
        · intro hz; exact ⟨Or.inl hz, hX hz⟩
      · ext z; constructor
        · rintro ⟨hz | hz, hzQ⟩
          · exact absurd hzQ (pm170_aux_disj h.2 (hX hz))
          · exact hz
        · intro hz; exact ⟨Or.inr hz, hY hz⟩
    have e1 := (key A G hA' hG').1
    have e2 := (key A G hA' hG').2
    rw [e, (key B D hB' hD').1] at e1
    rw [e, (key B D hB' hD').2] at e2
    rw [e1, e2]
  · intro ρ σ
    rw [pm170_67 h, semi_semi, pm170_aux_sRel_C, semi_graph_apply]
    exact ⟨fun ⟨U, V, ⟨h1, h2⟩, h3⟩ => ⟨U, V, h3, h1, h2⟩, fun ⟨U, V, h3, h1, h2⟩ => ⟨U, V, ⟨h1, h2⟩, h3⟩⟩

/-- ✱170·69. \[\begin{align}&\vdash :\dot{\exists} !P.\dot{\exists} !Q.CʻP\cap CʻQ=\Lambda .\supset .(P\unicode{x2909}Q)_{\text{cl}}\,\text{smor}\,(P_{\text{cl}}\times Q_{\text{cl}})\\ &[*170·68]\end{align}\] -/
theorem pm170_69 {P Q : α → α → Prop} (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) :
    smor (Pcl (P ⤉ Q)) (Pcl P ×ᵣ Pcl Q) :=
  ⟨_, pm170_68 h⟩

/-!
## [✱171] The principle of first differences (*continued*)

*(Vol. 2, p. 423)*

> *Summary of* *171.
>
> …

**Lean reading.** `P_df` is `Pdf P` and `P_fd` is `Pfd P = (Pdf P˘)˘` (✱171·02·101 keep the
description `Cnv'`); `P⃗'z ∩ α − ι'z` is `(refs P z ∩ A) \ ι z` and `P⃖'z` is `rels P z`. The
chain ✱171·5 (`X = Y = Z`) is the conjunction of its links. ✱171·51 is stated, as printed, for all
`x`, `y`. The sums ✱171·67–·69 are proved through generic forms of ✱170·66–·68 for any relation
of first differences (`pm171_aux_gen66`, `…gen67`, `…gen68`), with the `P_df` analogue of
✱170·653 (`pm171_aux_653`); ✱171·71 also covers the case where `P` or `Q` is null (then `P ⤉ Q`
is `Q` or `P`), which the cited ✱170·67, ✱171·67 do not.

**Status.** proved (all propositions; ✱171·01·02 definition; ✱171·15·68 proved (reading):
transcription errors of the e-text, see their docstrings).
-/

section Helpers171
variable {α : Type u} {β : Type v}

theorem pm171_aux_beg {R : Set α → Set α → Prop} {X : Set α} (h1 : dom R = clEx X)
    (h2 : codom R = cl X \ ι X) (hne : X.Nonempty) :
    Desc Beg R (fun b => b = X) ∧ Desc Beg R˘ (fun b => b = Λ) := by
  have hcnv1 : dom R˘ = codom R := rfl
  have hcnv2 : codom R˘ = dom R := rfl
  constructor
  · refine ⟨X, fun A => ?_, rfl⟩
    show Beg A R ↔ A = X
    rw [Beg_apply, h1, h2]
    constructor
    · rintro ⟨⟨hA, -⟩, hA'⟩
      by_contra hne'
      exact hA' ⟨hA, hne'⟩
    · rintro rfl
      exact ⟨⟨subset_rfl, hne⟩, fun ⟨_, h'⟩ => h' rfl⟩
  · refine ⟨Λ, fun A => ?_, rfl⟩
    show Beg A R˘ ↔ A = Λ
    rw [Beg_apply, hcnv1, hcnv2, h1, h2]
    constructor
    · rintro ⟨⟨hA, -⟩, hA'⟩
      by_contra hne'
      refine hA' ⟨hA, ?_⟩
      rw [Set.nonempty_iff_ne_empty, ← pm170_aux_Null_eq]; exact hne'
    · rintro rfl
      refine ⟨⟨fun x hx => absurd hx (pm170_aux_Null x), ?_⟩, ?_⟩
      · intro e
        obtain ⟨y, hy⟩ := hne
        have e' : (Λ : Set α) = X := e
        rw [← e'] at hy; exact pm170_aux_Null y hy
      · rintro ⟨-, y, hy⟩; exact pm170_aux_Null y hy

theorem pm171_aux_semi_intro {S : α → β → Prop} {Q : β → β → Prop} {x y : α} {w z : β}
    (h1 : S x w) (h2 : S y z) (hq : Q w z) : (S ⁏ Q) x y :=
  (semi_apply S Q x y).2 ⟨w, z, ⟨h1, h2⟩, hq⟩

end Helpers171

/-- ✱171·01 (Df). \(P_{\text{df}}=\hat{\alpha} \hat{\beta} \{\alpha ,\beta \in \text{Cl}ʻCʻP:(\exists z).z\in \alpha -\beta .\overrightarrow{P}ʻz\cap \alpha -\iota ʻz=\overrightarrow{P}ʻz\cap \beta\} \quad\text{Df}\) -/
theorem pm171_01 (P : α → α → Prop) : Pdf P = fun A B => (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧
    ∃ z, z ∈ A \ B ∧ (refs P z ∩ A) \ ι z = refs P z ∩ B := rfl

/-- ✱171·02 (Df). \(P_\text{fd}=\text{Cnv}ʻ(\breve{P} )_{\text{df}} \quad\text{Df}\) -/
theorem pm171_02 (P : α → α → Prop) : Desc Cnv (Pdf P˘) (fun X => Pfd P = X) :=
  (desc_Cnv _ _).2 rfl

/-- ✱171·1. \[\begin{align}&\vdash \colon\ldotp \alpha P_{\text{df}}\beta .\equiv :\alpha ,\beta \in \text{Cl}ʻCʻP:(\exists z).z\in \alpha -\beta .\overrightarrow{P}ʻz\cap \alpha -\iota ʻz=\overrightarrow{P}ʻz\cap \beta \\ &[(*171·01)]\end{align}\] -/
theorem pm171_1 {P : α → α → Prop} {A B : Set α} : Pdf P A B ↔ (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧
    ∃ z, z ∈ A \ B ∧ (refs P z ∩ A) \ ι z = refs P z ∩ B := Iff.rfl

/-- ✱171·101. \(\vdash .P_\text{fd}=\text{Cnv}ʻ(\breve{P} )_{\text{df}} \quad[(*171·02)]\) -/
theorem pm171_101 (P : α → α → Prop) : Desc Cnv (Pdf P˘) (fun X => Pfd P = X) :=
  (desc_Cnv _ _).2 rfl

/-- ✱171·102. \[\begin{align}&\vdash \colon\ldotp \alpha P_\text{fd}\beta .\equiv :\alpha ,\beta \in \text{Cl}ʻCʻP:(\exists z).z\in \beta -\alpha .\overleftarrow{P}ʻz\cap \beta -\iota ʻz=\overleftarrow{P}ʻz\cap \alpha\\ &[*171·1·101]\end{align}\] -/
theorem pm171_102 {P : α → α → Prop} {A B : Set α} : Pfd P A B ↔ (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧
    ∃ z, z ∈ B \ A ∧ (rels P z ∩ B) \ ι z = rels P z ∩ A := by
  show Pdf P˘ B A ↔ _
  rw [pm171_1, pm170_aux_fld_cnv]
  exact and_congr and_comm Iff.rfl

/-- ✱171·12. \[\begin{align}&\vdash \colon\ldotp \alpha P_{\text{df}}\beta .\equiv :\alpha ,\beta \in \text{Cl}ʻCʻP:\\ &(\exists z).z\in \alpha -\beta .\overrightarrow{P}ʻz\cap \alpha -\iota ʻz=\overrightarrow{P}ʻz\cap \beta -\iota ʻz \quad[*171·1.*51·222]\end{align}\] -/
theorem pm171_12 {P : α → α → Prop} {A B : Set α} : Pdf P A B ↔ (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧
    ∃ z, z ∈ A \ B ∧ (refs P z ∩ A) \ ι z = (refs P z ∩ B) \ ι z := by
  rw [pm171_1]
  refine and_congr Iff.rfl (exists_congr fun z => ?_)
  constructor
  · rintro ⟨hz, e⟩
    refine ⟨hz, ?_⟩
    rw [e]; ext w; exact ⟨fun h => ⟨h, fun h' => hz.2 ((pm170_aux_mem_iota.1 h') ▸ h.2)⟩,
      fun h => h.1⟩
  · rintro ⟨hz, e⟩
    refine ⟨hz, ?_⟩
    rw [e]; ext w; exact ⟨fun h => h.1,
      fun h => ⟨h, fun h' => hz.2 ((pm170_aux_mem_iota.1 h') ▸ h.2)⟩⟩

/-- ✱171·13. \(\vdash .CʻP_{\text{df}}\subset \text{Cl}ʻCʻP \quad[*171·1]\) -/
theorem pm171_13 (P : α → α → Prop) : fld (Pdf P) ⊆ cl (fld P) := by
  rintro A ⟨B, ⟨⟨hA, -⟩, -⟩ | ⟨⟨-, hA⟩, -⟩⟩ <;> exact hA

/-- ✱171·14. \(\vdash :\alpha \subset CʻP.z\in \alpha .\supset .\alpha P_{\text{df}}(\alpha -\iota ʻz)\) -/
theorem pm171_14 {P : α → α → Prop} {A : Set α} {z : α} (h : A ⊆ fld P ∧ z ∈ A) :
    Pdf P A (A \ ι z) := by
  refine ⟨⟨h.1, Set.sdiff_subset.trans h.1⟩, z, ⟨h.2, fun h' => h'.2 rfl⟩, ?_⟩
  ext w; exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- ✱171·15. \(\vdash :\beta \subset CʻP.z\in CʻP-\beta .(\beta \cup \iota ʻz)P_{\text{df}}\beta\)

**Status.** proved (reading): transcription error: the e-text omits the principal `⊃`; PM's
enunciation is `β ⊂ C'P . z ∈ C'P − β . ⊃ . (β ∪ ι'z)P_df β` (the analogue of ✱171·14, used in
✱171·16). -/
theorem pm171_15 {P : α → α → Prop} {B : Set α} {z : α} (h : B ⊆ fld P ∧ z ∈ fld P \ B) :
    Pdf P (B ∪ ι z) B := by
  obtain ⟨hB, hzP, hzB⟩ := h
  refine ⟨⟨Set.union_subset hB (fun w hw => (pm170_aux_mem_iota.1 hw) ▸ hzP), hB⟩, z,
    ⟨Or.inr rfl, hzB⟩, ?_⟩
  ext w; constructor
  · rintro ⟨⟨h1, h2 | h2⟩, h3⟩
    · exact ⟨h1, h2⟩
    · exact absurd h2 h3
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, Or.inl h2⟩, fun h' => hzB ((pm170_aux_mem_iota.1 h') ▸ h2)⟩

/-- ✱171·16. \(\vdash .\text{D}ʻP_{\text{df}}=\text{Cl ex}ʻCʻP.\text{ᗡ}ʻP_{\text{df}}=\text{Cl}ʻCʻP-\iota ʻCʻP\) -/
theorem pm171_16 (P : α → α → Prop) :
    dom (Pdf P) = clEx (fld P) ∧ codom (Pdf P) = cl (fld P) \ ι (fld P) := by
  constructor
  · ext A; constructor
    · rintro ⟨B, ⟨⟨hA, -⟩, z, ⟨hzA, -⟩, -⟩⟩; exact ⟨hA, z, hzA⟩
    · rintro ⟨hA, z, hz⟩; exact ⟨_, pm171_14 ⟨hA, hz⟩⟩
  · ext B; constructor
    · rintro ⟨A, ⟨⟨hA, hB⟩, z, ⟨hzA, hzB⟩, -⟩⟩
      exact ⟨hB, fun e => hzB ((show B = fld P from e) ▸ hA hzA)⟩
    · rintro ⟨hB, hne⟩
      have : ∃ z, z ∈ fld P \ B := by
        by_contra h'
        push Not at h'
        exact hne (Set.Subset.antisymm hB (fun z hz => by_contra fun hzB => h' z ⟨hz, hzB⟩))
      obtain ⟨z, hz⟩ := this
      exact ⟨_, pm171_15 ⟨hB, hz⟩⟩

/-- ✱171·17. \(\vdash :\dot{\exists} !P.\supset .CʻP_{\text{df}}=\text{Cl}ʻCʻP\) -/
theorem pm171_17 {P : α → α → Prop} (h : rEx P) : fld (Pdf P) = cl (fld P) := by
  obtain ⟨h1, h2⟩ := pm171_16 P
  have hne := pm170_aux_rEx_iff_fld.1 h
  refine Set.Subset.antisymm (pm171_13 P) (fun A hA => ?_)
  by_cases hA' : A.Nonempty
  · have : A ∈ dom (Pdf P) := by rw [h1]; exact ⟨hA, hA'⟩
    obtain ⟨B, hB⟩ := this; exact ⟨B, Or.inl hB⟩
  · have : A ∈ codom (Pdf P) := by
      rw [h2]
      refine ⟨hA, fun e => hA' ?_⟩
      rw [show A = fld P from e]; exact hne
    obtain ⟨B, hB⟩ := this; exact ⟨B, Or.inr hB⟩

/-- ✱171·18. \(\vdash :\dot{\exists} !P.\supset .BʻP_{\text{df}}=CʻP.Bʻ\text{Cnv}ʻP_{\text{df}}=\Lambda\) -/
theorem pm171_18 {P : α → α → Prop} (h : rEx P) :
    Desc Beg (Pdf P) (fun b => b = fld P) ∧ Desc Beg (Pdf P)˘ (fun b => b = Λ) :=
  pm171_aux_beg (pm171_16 P).1 (pm171_16 P).2 (pm170_aux_rEx_iff_fld.1 h)

/-- ✱171·19. \(\vdash :P=\dot{\Lambda} .\supset .P_{\text{df}}=\dot{\Lambda}\) -/
theorem pm171_19 {P : α → α → Prop} (h : P = rNull) : Pdf P = rNull := by
  funext A B; apply propext
  constructor
  · rintro ⟨⟨hA, -⟩, z, ⟨hzA, -⟩, -⟩
    obtain ⟨w, hw | hw⟩ := hA hzA <;> rw [h] at hw <;> exact absurd hw (rNull_apply _ _)
  · intro h'; exact absurd h' (rNull_apply A B)

/-- ✱171·2. \(\vdash :P\,\unicode{x2abd}\, J.\supset .P_{\text{df}} =\hat{\alpha} \hat{\beta} \{\alpha ,\beta \in \text{Cl}ʻCʻP:(\exists z).z\in \alpha -\beta .\overrightarrow{P}ʻz\cap \alpha =\overrightarrow{P}ʻz\cap \beta\}\) -/
theorem pm171_2 {P : α → α → Prop} (h : P ⪽ J) : Pdf P = fun A B =>
    (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧ ∃ z, z ∈ A \ B ∧ refs P z ∩ A = refs P z ∩ B := by
  funext A B; apply propext
  refine and_congr Iff.rfl (exists_congr fun z => and_congr Iff.rfl ?_)
  have : (refs P z ∩ A) \ ι z = refs P z ∩ A := by
    ext w; exact ⟨fun h' => h'.1, fun h' => ⟨h', fun e => h _ _ h'.1 (pm170_aux_mem_iota.1 e)⟩⟩
  rw [this]

/-- ✱171·21. \(\vdash .P_{\text{df}}\,\unicode{x2abd}\, P_{\text{cl}}\) -/
theorem pm171_21 (P : α → α → Prop) : Pdf P ⪽ Pcl P := by
  rintro A B ⟨hAB, z, hz, e⟩
  refine pm170_11.2 ⟨hAB, z, hz, ?_⟩
  rw [← e]; exact fun w hw => hw.1.2

/-- ✱171·22. \(\vdash .P_{\text{df}}\,\unicode{x2abd}\, J \quad[*170·17.*171·21]\) -/
theorem pm171_22 (P : α → α → Prop) : Pdf P ⪽ J := fun A B h => (pm170_17 P).1 A B (pm171_21 P A B h)

/-- ✱171·4. \(\vdash :S\in 1\rightarrow 1.CʻQ=\text{ᗡ}ʻS.\supset .(S^{;}Q)_{\text{df}}=S_{\in }^{;}Q_{\text{df}} \quad[\text{Proof as in *170·4}]\) -/
theorem pm171_4 {S : α → β → Prop} {Q : β → β → Prop} (h : S ∈ arrow one one ∧ fld Q = codom S) :
    Pdf (S ⁏ Q) = imgRel S ⁏ Pdf Q := by
  obtain ⟨hS, hc⟩ := h
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS
  have hf := pm170_aux_fld_semi hc
  funext A B; apply propext
  rw [pm171_1, pm170_aux_imgRel_semi, hf]
  constructor
  · rintro ⟨⟨hA, hB⟩, y, ⟨hyA, hyB⟩, he⟩
    refine ⟨{z | ∃ x, x ∈ A ∧ S x z}, {z | ∃ x, x ∈ B ∧ S x z}, ⟨?_, ?_⟩, ?_⟩
    · ext x; constructor
      · intro hx; obtain ⟨z, hz⟩ := hA hx; exact ⟨z, ⟨x, hx, hz⟩, hz⟩
      · rintro ⟨z, ⟨x', hx', hz'⟩, hz⟩; rw [h1 x x' z ⟨hz, hz'⟩]; exact hx'
    · ext x; constructor
      · intro hx; obtain ⟨z, hz⟩ := hB hx; exact ⟨z, ⟨x, hx, hz⟩, hz⟩
      · rintro ⟨z, ⟨x', hx', hz'⟩, hz⟩; rw [h1 x x' z ⟨hz, hz'⟩]; exact hx'
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · rintro z ⟨x, -, hz⟩; rw [hc]; exact ⟨x, hz⟩
      · rintro z ⟨x, -, hz⟩; rw [hc]; exact ⟨x, hz⟩
      · obtain ⟨z0, hz0⟩ := hA hyA
        refine ⟨z0, ⟨⟨y, hyA, hz0⟩, ?_⟩, ?_⟩
        · rintro ⟨x, hxB, hx⟩; rw [h1 x y z0 ⟨hx, hz0⟩] at hxB; exact hyB hxB
        · ext w; constructor
          · rintro ⟨⟨hwz, x, hxA, hxw⟩, hwz0⟩
            have hxy : x ∉ ι y := fun e => hwz0 (by
              rw [pm170_aux_mem_iota.1 e] at hxw; exact h2 y w z0 ⟨hxw, hz0⟩)
            have : x ∈ refs (S ⁏ Q) y ∩ B := by
              rw [← he]; exact ⟨⟨pm171_aux_semi_intro hxw hz0 hwz, hxA⟩, hxy⟩
            exact ⟨hwz, x, this.2, hxw⟩
          · rintro ⟨hwz, x, hxB, hxw⟩
            have : x ∈ (refs (S ⁏ Q) y ∩ A) \ ι y := by
              rw [he]; exact ⟨pm171_aux_semi_intro hxw hz0 hwz, hxB⟩
            refine ⟨⟨hwz, x, this.1.2, hxw⟩, fun e => this.2 ?_⟩
            rw [pm170_aux_mem_iota.1 e] at hxw
            exact h1 x y z0 ⟨hxw, hz0⟩
  · rintro ⟨G, D, ⟨rfl, rfl⟩, ⟨⟨hG, hD⟩, z, ⟨hzG, hzD⟩, he⟩⟩
    have hzc : z ∈ codom S := by rw [← hc]; exact hG hzG
    obtain ⟨y, hyz⟩ := hzc
    refine ⟨⟨?_, ?_⟩, y, ⟨⟨z, hzG, hyz⟩, ?_⟩, ?_⟩
    · rintro x ⟨w, -, hw⟩; exact ⟨w, hw⟩
    · rintro x ⟨w, -, hw⟩; exact ⟨w, hw⟩
    · rintro ⟨w, hwD, hyw⟩; rw [h2 y z w ⟨hyz, hyw⟩] at hzD; exact hzD hwD
    · ext x; constructor
      · rintro ⟨⟨hxy, w0, hw0G, hxw0⟩, hxny⟩
        obtain ⟨z1, w1, ⟨hxz1, hyw1⟩, hq⟩ := (semi_apply S Q x y).1 hxy
        rw [h2 y w1 z ⟨hyw1, hyz⟩, h2 x z1 w0 ⟨hxz1, hxw0⟩] at hq
        have hw0z : w0 ∉ ι z := fun e => hxny (by
          rw [pm170_aux_mem_iota.1 e] at hxw0; exact h1 x y z ⟨hxw0, hyz⟩)
        have : w0 ∈ refs Q z ∩ D := by rw [← he]; exact ⟨⟨hq, hw0G⟩, hw0z⟩
        exact ⟨hxy, w0, this.2, hxw0⟩
      · rintro ⟨hxy, w0, hw0D, hxw0⟩
        obtain ⟨z1, w1, ⟨hxz1, hyw1⟩, hq⟩ := (semi_apply S Q x y).1 hxy
        rw [h2 y w1 z ⟨hyw1, hyz⟩, h2 x z1 w0 ⟨hxz1, hxw0⟩] at hq
        have : w0 ∈ (refs Q z ∩ G) \ ι z := by rw [he]; exact ⟨hq, hw0D⟩
        refine ⟨⟨hxy, w0, this.1.2, hxw0⟩, fun e => this.2 ?_⟩
        rw [pm170_aux_mem_iota.1 e] at hxw0
        exact h2 y w0 z ⟨hxw0, hyz⟩

/-- ✱171·41. \(\vdash :(S\upharpoonright CʻQ)_{\in }^{;}Q_{\text{df}}=S_{\in }^{;}Q_{\text{df}} \quad[\text{Proof as in *170·41}]\) -/
theorem pm171_41 (S : α → β → Prop) (Q : β → β → Prop) :
    imgRel (S ↾ fld Q) ⁏ Pdf Q = imgRel S ⁏ Pdf Q := by
  funext A B; apply propext
  rw [pm170_aux_imgRel_semi, pm170_aux_imgRel_semi]
  constructor
  · rintro ⟨G, D, ⟨rfl, rfl⟩, hGD⟩
    exact ⟨G, D, ⟨pm170_aux_img_cres hGD.1.1, pm170_aux_img_cres hGD.1.2⟩, hGD⟩
  · rintro ⟨G, D, ⟨rfl, rfl⟩, hGD⟩
    exact ⟨G, D, ⟨(pm170_aux_img_cres hGD.1.1).symm, (pm170_aux_img_cres hGD.1.2).symm⟩, hGD⟩

/-- ✱171·42. \(\vdash :S\upharpoonright CʻQ\in 1\rightarrow 1.CʻQ\subset \text{ᗡ}ʻS.\supset .(S^{;}Q)_{\text{df}}=S_{\in }^{;}Q_{\text{df}} \quad[*171·4·41]\) -/
theorem pm171_42 {S : α → β → Prop} {Q : β → β → Prop}
    (h : S ↾ fld Q ∈ arrow one one ∧ fld Q ⊆ codom S) :
    Pdf (S ⁏ Q) = imgRel S ⁏ Pdf Q := by
  rw [pm170_aux_semi_cres, pm171_4 ⟨h.1, pm170_aux_codom_cres h.2⟩, pm171_41]

/-- ✱171·43. \[\begin{align}&\vdash :S\upharpoonright CʻQ\in P\,\overline{\text{smor}}\,Q.\supset .S_{\in }\upharpoonright CʻQ_{\text{df}}\in P_{\text{df}}\,\overline{\text{smor}}\, Q_{\text{df}}\\ &[\text{Proof as in *170·43}]\end{align}\] -/
theorem pm171_43 {S : α → β → Prop} {P : α → α → Prop} {Q : β → β → Prop}
    (h : S ↾ fld Q ∈ smorbar P Q) : imgRel S ↾ fld (Pdf Q) ∈ smorbar (Pdf P) (Pdf Q) := by
  obtain ⟨⟨hS, hc⟩, hP⟩ := h
  have hc' : fld Q ⊆ codom S := by
    intro z hz; rw [hc] at hz; obtain ⟨x, hx, -⟩ := hz; exact ⟨x, hx⟩
  have e : Pdf P = imgRel S ⁏ Pdf Q := by
    rw [hP, pm171_4 ⟨hS, hc⟩, pm171_41]
  apply pm170_aux_smorbar (img S)
  · intro G D hG hD
    exact pm170_aux_img_inj hS hc' (pm171_13 Q hG) (pm171_13 Q hD)
  · intro X Y
    rw [e, pm170_aux_imgRel_semi]
    exact ⟨fun ⟨G, D, ⟨h1, h2⟩, h3⟩ => ⟨G, D, h3, h1, h2⟩, fun ⟨G, D, h3, h1, h2⟩ => ⟨G, D, ⟨h1, h2⟩, h3⟩⟩

/-- ✱171·44. \(\vdash :P\,\text{smor}\,Q.\supset .P_{\text{df}}\text{smor}Q_{\text{df}} \quad[*171·43]\) -/
theorem pm171_44 {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q) : smor (Pdf P) (Pdf Q) := by
  obtain ⟨S, hS⟩ := h
  have hS' : S ↾ fld Q ∈ smorbar P Q := by rw [pm170_aux_cres_codom hS.1.2]; exact hS
  exact ⟨_, pm171_43 hS'⟩

/-- ✱171·5. \(\vdash .(x\downarrow x)_{\text{df}}=(\iota ʻx)\downarrow \Lambda =(x\downarrow x)_{\text{cl}}\) -/
theorem pm171_5 (x : α) : Pdf (x ↓ x) = ι x ↓ Λ ∧ ι x ↓ Λ = Pcl (x ↓ x) := by
  refine ⟨?_, (pm170_5 x).symm⟩
  rw [← pm170_5]
  funext A B; apply propext
  refine ⟨fun h => pm171_21 _ A B h, fun h => ?_⟩
  obtain ⟨⟨hA, hB⟩, z, ⟨hzA, hzB⟩, -⟩ := pm170_11.1 h
  refine ⟨⟨hA, hB⟩, z, ⟨hzA, hzB⟩, ?_⟩
  have hz : z = x := by
    rw [pm170_aux_fld_couple, Set.union_self] at hA; exact hA hzA
  ext w; constructor
  · rintro ⟨⟨⟨h1, -⟩, -⟩, h3⟩; exact absurd (pm170_aux_mem_iota.2 (h1.trans hz.symm)) h3
  · rintro ⟨⟨h1, -⟩, h2⟩
    have : w = z := h1.trans hz.symm
    rw [this] at h2; exact absurd h2 hzB

/-- ✱171·51. \(\vdash .(x\downarrow y)_{\text{df}}=(x\downarrow y)_{\text{cl}}\) -/
theorem pm171_51 (x y : α) : Pdf (x ↓ y) = Pcl (x ↓ y) := by
  by_cases hxy : x = y
  · rw [hxy]; exact (pm171_5 y).1.trans (pm171_5 y).2
  funext A B; apply propext
  refine ⟨fun h => pm171_21 _ A B h, fun h => ?_⟩
  have h' := (pm170_aux_cl_couple hxy).1 h
  obtain ⟨⟨hA, hB⟩, -⟩ := h'
  have hcl : A ∈ cl (fld (x ↓ y)) ∧ B ∈ cl (fld (x ↓ y)) := by
    rw [pm170_aux_fld_couple]; exact ⟨hA, hB⟩
  have hrx : ∀ w, w ∉ refs (x ↓ y) x := fun w hw => hxy hw.2
  by_cases hc : x ∈ A ∧ x ∉ B
  · refine ⟨hcl, x, hc, ?_⟩
    ext w; exact ⟨fun h'' => absurd h''.1.1 (hrx w), fun h'' => absurd h''.1 (hrx w)⟩
  · obtain ⟨-, h''⟩ := (pm170_aux_cl_couple hxy).1 h
    rcases h'' with h'' | ⟨hy, hxBA⟩
    · exact absurd h'' hc
    have hxAB : x ∈ A → x ∈ B := fun hxA => by by_contra hxB; exact hc ⟨hxA, hxB⟩
    refine ⟨hcl, y, hy, ?_⟩
    ext w; constructor
    · rintro ⟨⟨hw, hwA⟩, -⟩
      have : w = x := hw.1
      rw [this] at hwA ⊢; exact ⟨⟨rfl, rfl⟩, hxAB hwA⟩
    · rintro ⟨hw, hwB⟩
      have : w = x := hw.1
      rw [this] at hwB ⊢
      exact ⟨⟨⟨rfl, rfl⟩, hxBA hwB⟩, fun e => hxy (pm170_aux_mem_iota.1 e)⟩

/-- ✱171·52. \[\begin{align}&\vdash :x\neq y.\supset .(x\downarrow y)_{\text{df}}=(\iota 'x\cup \iota 'y)\downarrow (\iota 'x)\unicode{x2909}(\iota 'y)\downarrow \Lambda \\ &[*171·51.*170·52]\end{align}\] -/
theorem pm171_52 {x y : α} (hxy : x ≠ y) :
    Pdf (x ↓ y) = (ι x ∪ ι y) ↓ ι x ⤉ ι y ↓ Λ := by
  rw [pm171_51, pm170_52 hxy]

section Helpers171b
variable {α : Type u}

theorem pm171_aux_tautA (pw qw cw a g b d ne : Prop) (hq : ¬qw) (hc : ¬cw) (hg : pw → ¬g)
    (hd : pw → ¬d) :
    (((((pw ∨ qw) ∨ cw) ∧ (a ∨ g)) ∧ ne) ↔ (((pw ∨ qw) ∨ cw) ∧ (b ∨ d))) ↔
      (((pw ∧ a) ∧ ne) ↔ (pw ∧ b)) := by
  tauto

theorem pm171_aux_tautG (pw qw cw a g b d ne : Prop) (hp : ¬pw) (hcg : cw → ¬g) (hcd : cw → ¬d)
    (hac : a → cw) (hbc : b → cw) (hqc : qw → ¬cw) (han : a → ne) :
    (((((pw ∨ qw) ∨ cw) ∧ (a ∨ g)) ∧ ne) ↔ (((pw ∨ qw) ∨ cw) ∧ (b ∨ d))) ↔
      ((a ↔ b) ∧ (((qw ∧ g) ∧ ne) ↔ (qw ∧ d))) := by
  constructor
  · intro E
    refine ⟨⟨fun ha => ?_, fun hb => ?_⟩, ⟨?_, ?_⟩⟩
    · rcases (E.1 ⟨⟨Or.inr (hac ha), Or.inl ha⟩, han ha⟩).2 with hb | hd'
      · exact hb
      · exact absurd hd' (hcd (hac ha))
    · obtain ⟨⟨-, hag⟩, -⟩ := E.2 ⟨Or.inr (hbc hb), Or.inl hb⟩
      rcases hag with ha | hg
      · exact ha
      · exact absurd hg (hcg (hbc hb))
    · rintro ⟨⟨hq, hg⟩, hne⟩
      rcases (E.1 ⟨⟨Or.inl (Or.inr hq), Or.inr hg⟩, hne⟩).2 with hb | hd'
      · exact absurd (hbc hb) (hqc hq)
      · exact ⟨hq, hd'⟩
    · rintro ⟨hq, hd'⟩
      obtain ⟨⟨-, hag⟩, hne⟩ := E.2 ⟨Or.inl (Or.inr hq), Or.inr hd'⟩
      rcases hag with ha | hg
      · exact absurd (hac ha) (hqc hq)
      · exact ⟨⟨hq, hg⟩, hne⟩
  · rintro ⟨hab, hQ⟩
    constructor
    · rintro ⟨⟨hpqc, hag⟩, hne⟩
      rcases hpqc with (hp' | hq) | hc
      · exact absurd hp' hp
      · rcases hag with ha | hg
        · exact absurd (hac ha) (hqc hq)
        · exact ⟨Or.inl (Or.inr hq), Or.inr (hQ.1 ⟨⟨hq, hg⟩, hne⟩).2⟩
      · rcases hag with ha | hg
        · exact ⟨Or.inr hc, Or.inl (hab.1 ha)⟩
        · exact absurd hg (hcg hc)
    · rintro ⟨hpqc, hbd⟩
      rcases hpqc with (hp' | hq) | hc
      · exact absurd hp' hp
      · rcases hbd with hb | hd'
        · exact absurd (hbc hb) (hqc hq)
        · obtain ⟨⟨-, hg⟩, hne⟩ := hQ.2 ⟨hq, hd'⟩
          exact ⟨⟨Or.inl (Or.inr hq), Or.inr hg⟩, hne⟩
      · rcases hbd with hb | hd'
        · have ha := hab.2 hb
          exact ⟨⟨Or.inr hc, Or.inl ha⟩, han ha⟩
        · exact absurd hd' (hcd hc)

theorem pm171_aux_tautX (ex fz pw a b nz : Prop) (hf : fz) (h1 : ex → ¬pw) (h2 : ex → a)
    (h3 : ex → b) (h4 : ex → nz) :
    ((((ex ∧ fz) ∨ pw) ∧ a) ∧ nz ↔ ((ex ∧ fz) ∨ pw) ∧ b) ↔
      ((pw ∧ (a ∧ ¬ex)) ∧ nz ↔ pw ∧ (b ∧ ¬ex)) := by
  tauto

/-- `P_df` for a sum of relations with disjoint fields (the analogue of ✱170·653). -/
theorem pm171_aux_653 {P Q : α → α → Prop} {A B G D : Set α}
    (h : (fld P ∩ fld Q = Λ ∧ (A ∈ cl (fld P) ∧ B ∈ cl (fld P))) ∧
      (G ∈ cl (fld Q) ∧ D ∈ cl (fld Q))) :
    Pdf (P ⤉ Q) (A ∪ G) (B ∪ D) ↔ Pdf P A B ∨ (A = B ∧ Pdf Q G D) := by
  obtain ⟨⟨hd, hA, hB⟩, hG, hD⟩ := h
  have hcl : (A ∪ G ∈ cl (fld (P ⤉ Q)) ∧ B ∪ D ∈ cl (fld (P ⤉ Q))) := by
    rw [fld_rsum]; exact ⟨Set.union_subset_union hA hG, Set.union_subset_union hB hD⟩
  have dj : ∀ {z}, z ∈ fld P → z ∈ fld Q → False := fun hP hQ => pm170_aux_disj hd hP hQ
  rw [pm171_1 (P := P ⤉ Q)]
  constructor
  · rintro ⟨-, y, ⟨hyAG, hyBD⟩, he⟩
    rcases hyAG with hyA | hyG
    · have hyP := hA hyA
      have key : ∀ w, ((P w y ∧ w ∈ A) ∧ w ∉ ι y ↔ P w y ∧ w ∈ B) := fun w =>
        (pm171_aux_tautA (P w y) (Q w y) (w ∈ fld P ∧ y ∈ fld Q) (w ∈ A) (w ∈ G) (w ∈ B) (w ∈ D)
          (w ∉ ι y) (fun h' => dj hyP ⟨w, Or.inr h'⟩) (fun h' => dj hyP h'.2)
          (fun h' h'' => dj ⟨y, Or.inl h'⟩ (hG h'')) (fun h' h'' => dj ⟨y, Or.inl h'⟩ (hD h''))).1
          (Set.ext_iff.1 he w)
      exact Or.inl ⟨⟨hA, hB⟩, y, ⟨hyA, fun h' => hyBD (Or.inl h')⟩, Set.ext fun w => key w⟩
    · have hyQ := hG hyG
      have key : ∀ w, (w ∈ A ↔ w ∈ B) ∧ ((Q w y ∧ w ∈ G) ∧ w ∉ ι y ↔ Q w y ∧ w ∈ D) := fun w =>
        (pm171_aux_tautG (P w y) (Q w y) (w ∈ fld P ∧ y ∈ fld Q) (w ∈ A) (w ∈ G) (w ∈ B) (w ∈ D)
          (w ∉ ι y) (fun h' => dj ⟨w, Or.inr h'⟩ hyQ) (fun h' h'' => dj h'.1 (hG h''))
          (fun h' h'' => dj h'.1 (hD h'')) (fun h' => ⟨hA h', hyQ⟩) (fun h' => ⟨hB h', hyQ⟩)
          (fun h' h'' => dj h''.1 ⟨y, Or.inl h'⟩)
          (fun h' e => dj (hA h') ((pm170_aux_mem_iota.1 e) ▸ hyQ))).1 (Set.ext_iff.1 he w)
      exact Or.inr ⟨Set.ext fun w => (key w).1,
        ⟨hG, hD⟩, y, ⟨hyG, fun h' => hyBD (Or.inr h')⟩, Set.ext fun w => (key w).2⟩
  · rintro (⟨-, y, ⟨hyA, hyB⟩, he⟩ | ⟨rfl, ⟨-, y, ⟨hyG, hyD⟩, he⟩⟩)
    · have hyP := hA hyA
      refine ⟨hcl, y, ⟨Or.inl hyA, ?_⟩, Set.ext fun w => ?_⟩
      · rintro (h' | h')
        · exact hyB h'
        · exact dj hyP (hD h')
      · exact (pm171_aux_tautA (P w y) (Q w y) (w ∈ fld P ∧ y ∈ fld Q) (w ∈ A) (w ∈ G) (w ∈ B)
          (w ∈ D) (w ∉ ι y) (fun h' => dj hyP ⟨w, Or.inr h'⟩) (fun h' => dj hyP h'.2)
          (fun h' h'' => dj ⟨y, Or.inl h'⟩ (hG h'')) (fun h' h'' => dj ⟨y, Or.inl h'⟩ (hD h''))).2
          (Set.ext_iff.1 he w)
    · have hyQ := hG hyG
      refine ⟨hcl, y, ⟨Or.inr hyG, ?_⟩, Set.ext fun w => ?_⟩
      · rintro (h' | h')
        · exact dj (hA h') hyQ
        · exact hyD h'
      · exact (pm171_aux_tautG (P w y) (Q w y) (w ∈ fld P ∧ y ∈ fld Q) (w ∈ A) (w ∈ G) (w ∈ A)
          (w ∈ D) (w ∉ ι y) (fun h' => dj ⟨w, Or.inr h'⟩ hyQ) (fun h' h'' => dj h'.1 (hG h''))
          (fun h' h'' => dj h'.1 (hD h'')) (fun h' => ⟨hA h', hyQ⟩) (fun h' => ⟨hA h', hyQ⟩)
          (fun h' h'' => dj h''.1 ⟨y, Or.inl h'⟩)
          (fun h' e => dj (hA h') ((pm170_aux_mem_iota.1 e) ▸ hyQ))).2
          ⟨Iff.rfl, Set.ext_iff.1 he w⟩

/-- Generic form of ✱170·66 for a relation of first differences `Φ`. -/
theorem pm171_aux_gen66 (Φ : (α → α → Prop) → Set α → Set α → Prop)
    (hcl : ∀ R A B, Φ R A B → A ∈ cl (fld R) ∧ B ∈ cl (fld R))
    (hfld : ∀ R : α → α → Prop, rEx R → fld (Φ R) = cl (fld R))
    {P Q : α → α → Prop}
    (h653 : ∀ A B G D : Set α, (fld P ∩ fld Q = Λ ∧ (A ∈ cl (fld P) ∧ B ∈ cl (fld P))) ∧
      (G ∈ cl (fld Q) ∧ D ∈ cl (fld Q)) →
      (Φ (P ⤉ Q) (A ∪ G) (B ∪ D) ↔ Φ P A B ∨ (A = B ∧ Φ Q G D)))
    (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) {ρ σ : Set α} :
    Φ (P ⤉ Q) ρ σ ↔ ∃ A B G D, ((Φ P ×ᵣ Φ Q) (G ↓ A) (D ↓ B) ∧ ρ = A ∪ G) ∧ σ = B ∪ D := by
  obtain ⟨⟨hP, hQ⟩, hd⟩ := h
  constructor
  · intro h'
    obtain ⟨hρ, hσ⟩ := hcl _ _ _ h'
    rw [fld_rsum] at hρ hσ
    have e : ∀ X : Set α, X ⊆ fld P ∪ fld Q → X = X ∩ fld P ∪ X ∩ fld Q := fun X hX => by
      rw [← Set.inter_union_distrib_left, Set.inter_eq_left.2 hX]
    refine ⟨ρ ∩ fld P, σ ∩ fld P, ρ ∩ fld Q, σ ∩ fld Q, ⟨?_, e ρ hρ⟩, e σ hσ⟩
    rw [e ρ hρ, e σ hσ] at h'
    rw [pm170_aux_rtimes_couple, hfld P hP, hfld Q hQ]
    rcases (h653 _ _ _ _ ⟨⟨hd, Set.inter_subset_right, Set.inter_subset_right⟩,
      Set.inter_subset_right, Set.inter_subset_right⟩).1 h' with h'' | ⟨e', h''⟩
    · exact Or.inr ⟨h'', Set.inter_subset_right, Set.inter_subset_right⟩
    · exact Or.inl ⟨Set.inter_subset_right, e', h''⟩
  · rintro ⟨A, B, G, D, ⟨hr, rfl⟩, rfl⟩
    rw [pm170_aux_rtimes_couple, hfld P hP, hfld Q hQ] at hr
    rcases hr with ⟨hA, rfl, h''⟩ | ⟨h'', hG, hD⟩
    · exact (h653 _ _ _ _ ⟨⟨hd, hA, hA⟩, hcl _ _ _ h''⟩).2 (Or.inr ⟨rfl, h''⟩)
    · exact (h653 _ _ _ _ ⟨⟨hd, hcl _ _ _ h''⟩, hG, hD⟩).2 (Or.inl h'')

/-- Generic form of ✱170·67. -/
theorem pm171_aux_gen67 (Φ : (α → α → Prop) → Set α → Set α → Prop) {P Q : α → α → Prop}
    (h66 : ∀ ρ σ : Set α, Φ (P ⤉ Q) ρ σ ↔
      ∃ A B G D, ((Φ P ×ᵣ Φ Q) (G ↓ A) (D ↓ B) ∧ ρ = A ∪ G) ∧ σ = B ∪ D) :
    Φ (P ⤉ Q) = sRel ⁏ C ⁏ (Φ P ×ᵣ Φ Q) := by
  rw [semi_semi, pm170_aux_sRel_C]
  funext ρ σ; apply propext
  rw [semi_graph_apply, h66]
  constructor
  · rintro ⟨A, B, G, D, ⟨hr, rfl⟩, rfl⟩
    exact ⟨G ↓ A, D ↓ B, ⟨(pm170_aux_sumCls_fld_couple G A).symm,
      (pm170_aux_sumCls_fld_couple D B).symm⟩, hr⟩
  · rintro ⟨U, V, ⟨rfl, rfl⟩, hr⟩
    obtain ⟨G, A, -, rfl⟩ := pm170_aux_fld_rtimes ⟨V, Or.inl hr⟩
    obtain ⟨D, B, -, rfl⟩ := pm170_aux_fld_rtimes ⟨_, Or.inr hr⟩
    exact ⟨A, B, G, D, ⟨hr, pm170_aux_sumCls_fld_couple G A⟩, pm170_aux_sumCls_fld_couple D B⟩

/-- Generic form of ✱170·68. -/
theorem pm171_aux_gen68 (Φ : (α → α → Prop) → Set α → Set α → Prop)
    (hcl : ∀ R A B, Φ R A B → A ∈ cl (fld R) ∧ B ∈ cl (fld R)) {P Q : α → α → Prop}
    (hd : fld P ∩ fld Q = Λ) (h67 : Φ (P ⤉ Q) = sRel ⁏ C ⁏ (Φ P ×ᵣ Φ Q)) :
    (sRel ⨾ C) ↾ fld (Φ P ×ᵣ Φ Q) ∈ smorbar (Φ (P ⤉ Q)) (Φ P ×ᵣ Φ Q) := by
  have hfl : ∀ R : α → α → Prop, fld (Φ R) ⊆ cl (fld R) := by
    rintro R A ⟨B, h' | h'⟩
    · exact (hcl _ _ _ h').1
    · exact (hcl _ _ _ h').2
  rw [pm170_aux_sRel_C]
  apply pm170_aux_smorbar
  · intro U V hU hV e
    obtain ⟨G, A, ⟨hG, hA⟩, rfl⟩ := pm170_aux_fld_rtimes hU
    obtain ⟨D, B, ⟨hD, hB⟩, rfl⟩ := pm170_aux_fld_rtimes hV
    simp only [pm170_aux_sumCls_fld_couple] at e
    have hG' := hfl Q hG
    have hD' := hfl Q hD
    have hA' := hfl P hA
    have hB' := hfl P hB
    have key : ∀ (X Y : Set α), X ⊆ fld P → Y ⊆ fld Q →
        (X ∪ Y) ∩ fld P = X ∧ (X ∪ Y) ∩ fld Q = Y := by
      intro X Y hX hY
      constructor
      · ext z; constructor
        · rintro ⟨hz | hz, hzP⟩
          · exact hz
          · exact absurd (hY hz) (pm170_aux_disj hd hzP)
        · intro hz; exact ⟨Or.inl hz, hX hz⟩
      · ext z; constructor
        · rintro ⟨hz | hz, hzQ⟩
          · exact absurd hzQ (pm170_aux_disj hd (hX hz))
          · exact hz
        · intro hz; exact ⟨Or.inr hz, hY hz⟩
    have e1 := (key A G hA' hG').1
    have e2 := (key A G hA' hG').2
    rw [e, (key B D hB' hD').1] at e1
    rw [e, (key B D hB' hD').2] at e2
    rw [e1, e2]
  · intro ρ σ
    rw [h67, semi_semi, pm170_aux_sRel_C, semi_graph_apply]
    exact ⟨fun ⟨U, V, ⟨h1, h2⟩, h3⟩ => ⟨U, V, h3, h1, h2⟩, fun ⟨U, V, h3, h1, h2⟩ => ⟨U, V, ⟨h1, h2⟩, h3⟩⟩

theorem pm171_aux_cl (R : α → α → Prop) (A B : Set α) (h : Pdf R A B) :
    A ∈ cl (fld R) ∧ B ∈ cl (fld R) := h.1

theorem pm171_aux_rsum_left {P Q : α → α → Prop} (h : ¬ rEx P) : P ⤉ Q = Q := by
  funext a b; apply propext
  rw [rsum_apply]
  constructor
  · rintro ((h' | h') | ⟨h', -⟩)
    · exact absurd ⟨a, b, h'⟩ h
    · exact h'
    · exact absurd (pm170_aux_rEx_iff_fld.2 ⟨a, h'⟩) h
  · intro h'; exact Or.inl (Or.inr h')

theorem pm171_aux_rsum_right {P Q : α → α → Prop} (h : ¬ rEx Q) : P ⤉ Q = P := by
  funext a b; apply propext
  rw [rsum_apply]
  constructor
  · rintro ((h' | h') | ⟨-, h'⟩)
    · exact h'
    · exact absurd ⟨a, b, h'⟩ h
    · exact absurd (pm170_aux_rEx_iff_fld.2 ⟨b, h'⟩) h
  · intro h'; exact Or.inl (Or.inl h')

end Helpers171b

/-- ✱171·64. \(\vdash :x{\sim}\in C'P.\supset .(x\unicode{x21f7}P)_{\text{df}}=(\iota 'x\cup )^{;}P_{\text{df}}\unicode{x2909}P_{\text{df}}\) -/
theorem pm171_64 {P : α → α → Prop} {x : α} (hx : x ∉ fld P) :
    Pdf (x ⇷ P) = (opL (· ∪ ·) (ι x) ⁏ Pdf P) ⤉ Pdf P := by
  have hrex : ∀ (R : α → α → Prop) A B, Pdf R A B → rEx R := by
    rintro R A B ⟨⟨hA, -⟩, z, ⟨hzA, -⟩, -⟩; exact pm170_aux_rEx_iff_fld.2 ⟨z, hA hzA⟩
  by_cases hP : rEx P
  · have hfld1 : fld (opL (· ∪ ·) (ι x) ⁏ Pdf P) = {A | ∃ G, G ∈ cl (fld P) ∧ A = ι x ∪ G} := by
      have := fld_semi_graph (fun G : Set α => ι x ∪ G) (Pdf P)
      rw [pm171_17 hP] at this
      exact this
    have hsub : ∀ C : Set α, C ⊆ fld (x ⇷ P) ↔ C \ ι x ⊆ fld P := by
      intro C; constructor
      · rintro hC w ⟨hwC, hwx⟩
        rcases pm170_aux_fld_addFirst_sub x P (hC hwC) with h' | h'
        · exact absurd h' hwx
        · exact h'
      · intro hC w hw
        rw [pm170_aux_fld_addFirst hP]
        by_cases hwx : w ∈ ι x
        · exact Or.inl hwx
        · exact Or.inr (hC ⟨hw, hwx⟩)
    have hnx : ∀ w, ¬ (x ⇷ P) w x := by
      rintro w (⟨-, h'⟩ | h')
      · exact hx h'
      · exact hx ⟨w, Or.inr h'⟩
    have hR1 : ∀ A B, (opL (· ∪ ·) (ι x) ⁏ Pdf P) A B → x ∈ A ∧ x ∈ B := by
      intro A B h'
      obtain ⟨G, D, ⟨rfl, rfl⟩, -⟩ := (pm170_aux_opL_union_semi x _ A B).1 h'
      exact ⟨Or.inl rfl, Or.inl rfl⟩
    funext A B; apply propext
    rw [rsum_apply, hfld1, pm171_17 hP]
    by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B
    · -- `x ∈ α ∩ β`
      have h2 : (opL (· ∪ ·) (ι x) ⁏ Pdf P) A B ↔ Pdf P (A \ ι x) (B \ ι x) := by
        rw [pm170_aux_opL_union_semi]
        constructor
        · rintro ⟨G, D, ⟨rfl, rfl⟩, hGD⟩
          rwa [pm170_aux_union_diff (fun h' => hx (hGD.1.1 h')),
            pm170_aux_union_diff (fun h' => hx (hGD.1.2 h'))]
        · intro hGD
          exact ⟨A \ ι x, B \ ι x, ⟨pm170_aux_union_diff' hxA, pm170_aux_union_diff' hxB⟩, hGD⟩
      have h1 : Pdf (x ⇷ P) A B ↔ Pdf P (A \ ι x) (B \ ι x) := by
        constructor
        · rintro ⟨⟨hA, hB⟩, z, ⟨hzA, hzB⟩, he⟩
          have hzx : z ∉ ι x := fun h' => hzB ((pm170_aux_mem_iota.1 h') ▸ hxB)
          have hzP : z ∈ fld P := by
            rcases pm170_aux_fld_addFirst_sub x P (hA hzA) with h' | h'
            · exact absurd h' hzx
            · exact h'
          refine ⟨⟨(hsub A).1 hA, (hsub B).1 hB⟩, z, ⟨⟨hzA, hzx⟩, fun h' => hzB h'.1⟩,
            Set.ext fun w => ?_⟩
          exact (pm171_aux_tautX (w = x) (z ∈ fld P) (P w z) (w ∈ A) (w ∈ B) (w ∉ ι z) hzP
            (fun e h' => hx ⟨z, Or.inl (e ▸ h')⟩) (fun e => e ▸ hxA) (fun e => e ▸ hxB)
            (fun e e' => hzx (pm170_aux_mem_iota.2 ((pm170_aux_mem_iota.1 e').symm.trans e)))).1
            (Set.ext_iff.1 he w)
        · rintro ⟨⟨hA, hB⟩, z, ⟨⟨hzA, hzx⟩, hzB⟩, he⟩
          have hzP : z ∈ fld P := hA ⟨hzA, hzx⟩
          refine ⟨⟨(hsub A).2 hA, (hsub B).2 hB⟩, z, ⟨hzA, fun h' => hzB ⟨h', hzx⟩⟩,
            Set.ext fun w => ?_⟩
          exact (pm171_aux_tautX (w = x) (z ∈ fld P) (P w z) (w ∈ A) (w ∈ B) (w ∉ ι z) hzP
            (fun e h' => hx ⟨z, Or.inl (e ▸ h')⟩) (fun e => e ▸ hxA) (fun e => e ▸ hxB)
            (fun e e' => hzx (pm170_aux_mem_iota.2 ((pm170_aux_mem_iota.1 e').symm.trans e)))).2
            (Set.ext_iff.1 he w)
      rw [h1, ← h2]
      constructor
      · intro h'; exact Or.inl (Or.inl h')
      · rintro ((h' | ⟨⟨hA, -⟩, -⟩) | ⟨-, hB⟩)
        · exact h'
        · exact absurd (hA hxA) hx
        · exact absurd (hB hxB) hx
    · -- `x ∈ α − β`
      constructor
      · rintro ⟨⟨hA, hB⟩, -⟩
        refine Or.inr ⟨⟨A \ ι x, (hsub A).1 hA, pm170_aux_union_diff' hxA⟩, fun w hw => ?_⟩
        rcases pm170_aux_fld_addFirst_sub x P (hB hw) with h' | h'
        · rw [pm170_aux_mem_iota.1 h'] at hw; exact absurd hw hxB
        · exact h'
      · rintro ((h' | ⟨⟨hA, -⟩, -⟩) | ⟨⟨G, hG, rfl⟩, hB⟩)
        · exact absurd (hR1 _ _ h').2 hxB
        · exact absurd (hA hxA) hx
        · refine ⟨⟨(hsub _).2 ?_, hB.trans (pm170_aux_sub_fld_addFirst x P)⟩, x,
            ⟨Or.inl rfl, hxB⟩, Set.ext fun w => ⟨fun h' => (hnx w h'.1.1).elim,
              fun h' => (hnx w h'.1).elim⟩⟩
          rw [pm170_aux_union_diff (fun h' => hx (hG h'))]; exact hG
    · -- `x ∈ β − α`
      constructor
      · rintro ⟨⟨hA, -⟩, z, ⟨hzA, hzB⟩, he⟩
        have hzP : z ∈ fld P := by
          rcases pm170_aux_fld_addFirst_sub x P (hA hzA) with h' | h'
          · rw [pm170_aux_mem_iota.1 h'] at hzA; exact absurd hzA hxA
          · exact h'
        have : x ∈ (refs (x ⇷ P) z ∩ A) \ ι z := by rw [he]; exact ⟨Or.inl ⟨rfl, hzP⟩, hxB⟩
        exact absurd this.1.2 hxA
      · rintro ((h' | ⟨⟨-, hB⟩, -⟩) | ⟨⟨G, -, rfl⟩, -⟩)
        · exact absurd (hR1 _ _ h').1 hxA
        · exact absurd (hB hxB) hx
        · exact (hxA (Or.inl rfl)).elim
    · -- `x ∉ α ∪ β`
      have e1 : ∀ z (X : Set α), x ∉ X → refs (x ⇷ P) z ∩ X = refs P z ∩ X := by
        intro z X hX; ext w; constructor
        · rintro ⟨⟨rfl, -⟩ | h', hw⟩
          · exact absurd hw hX
          · exact ⟨h', hw⟩
        · rintro ⟨h', hw⟩; exact ⟨Or.inr h', hw⟩
      have hsub' : ∀ X : Set α, x ∉ X → (X ⊆ fld (x ⇷ P) ↔ X ⊆ fld P) := by
        intro X hX; constructor
        · intro h' w hw
          rcases pm170_aux_fld_addFirst_sub x P (h' hw) with h'' | h''
          · rw [pm170_aux_mem_iota.1 h''] at hw; exact absurd hw hX
          · exact h''
        · intro h'; exact h'.trans (pm170_aux_sub_fld_addFirst x P)
      have h1 : Pdf (x ⇷ P) A B ↔ Pdf P A B := by
        rw [pm171_1, pm171_1]
        refine and_congr (and_congr (hsub' A hxA) (hsub' B hxB)) (exists_congr fun z => ?_)
        rw [e1 z A hxA, e1 z B hxB]
      rw [h1]
      constructor
      · intro h'; exact Or.inl (Or.inr h')
      · rintro ((h' | h') | ⟨⟨G, -, rfl⟩, -⟩)
        · exact absurd (hR1 _ _ h').1 hxA
        · exact h'
        · exact (hxA (Or.inl rfl)).elim
  · have hPdf : ∀ A B, ¬ Pdf P A B := fun A B h' => hP (hrex P A B h')
    funext A B; apply propext
    rw [rsum_apply]
    constructor
    · intro h'
      obtain ⟨a, b, hab⟩ := hrex _ A B h'
      rcases hab with ⟨-, hb⟩ | hab
      · exact (hP (pm170_aux_rEx_iff_fld.2 ⟨b, hb⟩)).elim
      · exact (hP ⟨a, b, hab⟩).elim
    · rintro ((h' | h') | ⟨-, ⟨C, hC | hC⟩⟩)
      · obtain ⟨G, D, -, h''⟩ := (pm170_aux_opL_union_semi x _ A B).1 h'
        exact absurd h'' (hPdf G D)
      · exact absurd h' (hPdf A B)
      · exact absurd hC (hPdf B C)
      · exact absurd hC (hPdf C B)

/-- ✱171·67. \[\begin{align}&\vdash :\dot{\exists} !P.\dot{\exists} !Q.C'P\cap C'Q=\Lambda .\supset .(P\unicode{x2909}Q)_{\text{df}}=s^{;}C^{;}(P_{\text{df}}\times Q_{\text{df}})\\ &[\text{Proof as in *170·67}]\end{align}\] -/
theorem pm171_67 {P Q : α → α → Prop} (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) :
    Pdf (P ⤉ Q) = sRel ⁏ C ⁏ (Pdf P ×ᵣ Pdf Q) :=
  pm171_aux_gen67 Pdf fun _ _ => pm171_aux_gen66 Pdf pm171_aux_cl (fun _ hR => pm171_17 hR)
    (fun _ _ _ _ h' => pm171_aux_653 h') h

/-- ✱171·68. \[\begin{align}\vdash : \dot{\exists} ! P . \dot{\exists} ! Q . C'P &\cap C'Q = \Lambda . \supset .\\ &s\mid C\upharpoonright (P_{\text{df}}\times Q_{\text{df}})\in (P\unicode{x2909}Q)_{\text{df}}\,\overline{\text{smor}}\,(P_{\text{df}}\times Q_{\text{df}})\\ [\text{Proof as in *170·68}]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `s∣C↾(P_df × Q_df)`,
restricting `C` to a relation (not significant); as in ✱170·68, whose proof PM cites, the correlator
is `(s∣C) ↾ C'(P_df × Q_df)`. -/
theorem pm171_68 {P Q : α → α → Prop} (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) :
    (sRel ⨾ C) ↾ fld (Pdf P ×ᵣ Pdf Q) ∈ smorbar (Pdf (P ⤉ Q)) (Pdf P ×ᵣ Pdf Q) :=
  pm171_aux_gen68 Pdf pm171_aux_cl h.2 (pm171_67 h)

/-- ✱171·69. \[\begin{align}&\vdash :\dot{\exists} !P.\dot{\exists} !Q.C'P\cap C'Q=\Lambda .\supset .(P\unicode{x2909}Q)_{\text{df}}\text{smor}(P_{\text{df}}\times Q_{\text{df}})\\ &[*171·68]\end{align}\] -/
theorem pm171_69 {P Q : α → α → Prop} (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) :
    smor (Pdf (P ⤉ Q)) (Pdf P ×ᵣ Pdf Q) :=
  ⟨_, pm171_68 h⟩

/-- ✱171·7. \[\begin{align}&\vdash :P_{\text{df}}=P_{\text{cl}}.x{\sim}\in C'P.\supset .(x\unicode{x21f7}P)_{\text{df}}=(x\unicode{x21f7}P)_{\text{cl}}\\ &[*171·64.*170·64]\end{align}\] -/
theorem pm171_7 {P : α → α → Prop} {x : α} (h : Pdf P = Pcl P ∧ x ∉ fld P) :
    Pdf (x ⇷ P) = Pcl (x ⇷ P) := by
  rw [pm171_64 h.2, pm170_64 h.2, h.1]

/-- ✱171·71. \[\begin{align}&\vdash :C'P\cap C'Q=\Lambda .P_{\text{df}}=P_{\text{cl}}.Q_{\text{df}}=Q_{\text{cl}}.\supset .(P\unicode{x2909}Q)_{\text{df}}=(P\unicode{x2909}Q)_{\text{cl}}\\ &[*170·67.*171·67.*160·21·22]\end{align}\] -/
theorem pm171_71 {P Q : α → α → Prop}
    (h : (fld P ∩ fld Q = Λ ∧ Pdf P = Pcl P) ∧ Pdf Q = Pcl Q) :
    Pdf (P ⤉ Q) = Pcl (P ⤉ Q) := by
  obtain ⟨⟨hd, hP⟩, hQ⟩ := h
  by_cases hP' : rEx P
  · by_cases hQ' : rEx Q
    · rw [pm171_67 ⟨⟨hP', hQ'⟩, hd⟩, pm170_67 ⟨⟨hP', hQ'⟩, hd⟩, hP, hQ]
    · rw [pm171_aux_rsum_right hQ']; exact hP
  · rw [pm171_aux_rsum_left hP']; exact hQ

/-!
## [✱172] The product of the relations of a field

*(Vol. 2, p. 428)*

> *Summary of* *172.
>
> …

**Lean reading.** `Π'P` is `relPi P` (✱172·01), with the descriptions `M'Q` kept as `Desc`;
for selections, `pm172_aux_relPi_iff` states it without descriptions. `F_Δ'C'P` is
`sel F (fld P)`, `B⃗'Π'P` is `refs Beg (relPi P)`, `M −̇ B | Cnv` is `M ∸ Beg ⨾ Cnv`, `P↓.,P` is
`opSemi couple P P`, `†(Q↓P)` is `opR daggerOp (Q ↓ P)`, `Π'P × Z` is `relPi P ×ᵣ Z`, `ṡ | C` is
`sDotRel ⨾ C`, `T ∥ Cnv'T†` is `T ∥ (daggerRel T)˘`. `Mult ax` (✱172·181·182·45) is a hypothesis
at a stated type (it is a theorem of Lean and is not used). ✱172·3 is proved from ✱172·33 via
`Π'(P ⇸ Z) = Π'(P ⤉ Z↓Z)` (✱172·5) and ✱172·2; ✱172·321 likewise from ✱172·34 via
`Π'(Z ⇷ P) = Π'(Z↓Z ⤉ P)`. The likeness and associativity of ordinal products (✱166·23·42), on
which ✱172·321·36–·37 rest, are re-proved here (`pm172_aux_smor_rtimes`, `pm172_aux_rtimes_assoc`).
The transport of selections by a double correlator `T` (✱172·4–·45) is carried out with
`T | N | Cnv'T†` (`pm172_aux_tr_sel`, `pm172_aux_tr_surj`, `pm172_aux_tr_relPi`); ✱164·44, used by
✱172·45, is `pm172_aux_164_44`.

**Status.** proved (all propositions; ✱172·01 definition; ✱172·31·321·33·181·182·402·42·44·45
proved (reading): transcription errors of the e-text or `Mult ax`, see their docstrings;
✱172·162·171·34 proved (corrected): the printed forms are refuted in Lean
(`pm172_162_printed_false`, `pm172_171_printed_false`, `pm172_34_printed_false`)).
-/

section Helpers172
variable {α : Type u} {β : Type v}

theorem pm172_aux_sel_unique {R M : α → β → Prop} {K : Set β} (hM : M ∈ sel R K) {x y : α} {Q : β}
    (h1 : M x Q) (h2 : M y Q) : x = y :=
  mem_arrow_one_Cls.1 (mem_sel_iff.1 hM).1.1 x y Q ⟨h1, h2⟩

theorem pm172_aux_sel_exists {R M : α → β → Prop} {K : Set β} (hM : M ∈ sel R K) {Q : β}
    (hQ : Q ∈ K) : ∃ x, M x Q := by
  rw [← (mem_sel_iff.1 hM).2] at hQ; exact hQ

theorem pm172_aux_sel_sub {R M : α → β → Prop} {K : Set β} (hM : M ∈ sel R K) {x : α} {Q : β}
    (h : M x Q) : R x Q := (mem_sel_iff.1 hM).1.2 x Q h

theorem pm172_aux_sel_mem {R M : α → β → Prop} {K : Set β} (hM : M ∈ sel R K) {x : α} {Q : β}
    (h : M x Q) : Q ∈ K := by
  rw [← (mem_sel_iff.1 hM).2]; exact ⟨x, h⟩

theorem pm172_aux_desc_sel {R M : α → β → Prop} {K : Set β} (hM : M ∈ sel R K) {x : α} {Q : β}
    (hx : M x Q) (ψ : α → Prop) : Desc M Q ψ ↔ ψ x :=
  TheIs_iff_of_unique fun y => ⟨fun hy => pm172_aux_sel_unique hM hy hx, fun e => e ▸ hx⟩

theorem pm172_aux_mk_sel {R M : α → β → Prop} {K : Set β}
    (h1 : ∀ x y Q, M x Q → M y Q → x = y) (h2 : ∀ x Q, M x Q → R x Q) (h3 : codom M = K) :
    M ∈ sel R K :=
  mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 fun x y z h => h1 x y z h.1 h.2, h2⟩, h3⟩

theorem pm172_aux_sel_iff_sub {R R' M : α → β → Prop} {K : Set β} (hM : M ∈ sel R K) :
    M ∈ sel R' K ↔ M ⪽ R' :=
  ⟨fun h => (mem_sel_iff.1 h).1.2, fun h =>
    mem_sel_iff.2 ⟨⟨(mem_sel_iff.1 hM).1.1, h⟩, (mem_sel_iff.1 hM).2⟩⟩

theorem pm172_aux_sel_ext {R M N : α → β → Prop} {K : Set β} (hM : M ∈ sel R K)
    (hN : N ∈ sel R K) (h : ∀ x Q, M x Q → N x Q) : M = N := by
  funext x Q; apply propext
  refine ⟨h x Q, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := pm172_aux_sel_exists hM (pm172_aux_sel_mem hN hx)
  rw [pm172_aux_sel_unique hN hx (h y Q hy)]; exact hy

theorem pm172_aux_rEx_iff_ne {Q : α → α → Prop} : rEx Q ↔ Q ≠ rNull := by
  constructor
  · rintro ⟨x, y, h⟩ rfl; exact rNull_apply x y h
  · intro h; by_contra h'
    exact h (funext fun x => funext fun y => propext
      ⟨fun hxy => absurd ⟨x, y, hxy⟩ h', fun hxy => absurd hxy (rNull_apply x y)⟩)

end Helpers172

section Helpers172b
variable {α : Type u}

/-- `Π'P` without descriptions: `M(Π'P)N` iff `M, N ∈ F_Δ'C'P` and for some `Q`, `(M'Q)Q(N'Q)`
and `M'R = N'R` for every `R ≠ Q` preceding `Q`. -/
theorem pm172_aux_relPi_iff {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M N : α → (α → α → Prop) → Prop} :
    relPi P M N ↔ (M ∈ sel F (fld P) ∧ N ∈ sel F (fld P)) ∧
      ∃ Q x y, ((M x Q ∧ N y Q) ∧ Q x y) ∧ ∀ R, P R Q ∧ R ≠ Q → ∀ u, M u R → N u R := by
  constructor
  · rintro ⟨⟨hM, hN⟩, Q, ⟨x, hx, y, hy, hq⟩, hR⟩
    refine ⟨⟨hM, hN⟩, Q, x, y, ⟨⟨(hx x).2 rfl, (hy y).2 rfl⟩, hq⟩, fun R hR' u hu => ?_⟩
    obtain ⟨u0, hu0, v0, hv0, e⟩ := hR R hR'
    rw [(hu0 u).1 hu, e]; exact (hv0 v0).2 rfl
  · rintro ⟨⟨hM, hN⟩, Q, x, y, ⟨⟨hx, hy⟩, hq⟩, hR⟩
    refine ⟨⟨hM, hN⟩, Q, (pm172_aux_desc_sel hM hx _).2 ((pm172_aux_desc_sel hN hy _).2 hq),
      fun R hR' => ?_⟩
    have hRP : R ∈ fld P := ⟨Q, Or.inl hR'.1⟩
    obtain ⟨u, hu⟩ := pm172_aux_sel_exists hM hRP
    exact (pm172_aux_desc_sel hM hu _).2 ((pm172_aux_desc_sel hN (hR R hR' u hu) _).2 rfl)

/-- Changing a selection at one relation `Q` (as in ✱172·15). -/
theorem pm172_aux_modify {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M : α → (α → α → Prop) → Prop} {Q : α → α → Prop} {y : α} (hM : M ∈ sel F (fld P))
    (hQ : Q ∈ fld P) (hy : y ∈ fld Q) : (M ↾ (ι Q)ᶜ) ⊍ y ↓ Q ∈ sel F (fld P) := by
  refine pm172_aux_mk_sel ?_ ?_ ?_
  · rintro x x' R (⟨h1, h1'⟩ | ⟨h1, h1'⟩) (⟨h2, h2'⟩ | ⟨h2, h2'⟩)
    · exact pm172_aux_sel_unique hM h1 h2
    · exact absurd h2' h1'
    · exact absurd h1' h2'
    · exact (show x = y from h1).trans (show x' = y from h2).symm
  · rintro x R (⟨h1, -⟩ | ⟨h1, h1'⟩)
    · exact pm172_aux_sel_sub hM h1
    · rw [show x = y from h1, show R = Q from h1']; exact hy
  · ext R; constructor
    · rintro ⟨x, ⟨h1, -⟩ | ⟨-, h1'⟩⟩
      · exact pm172_aux_sel_mem hM h1
      · rw [show R = Q from h1']; exact hQ
    · intro hR
      by_cases e : R ∈ ι Q
      · exact ⟨y, Or.inr ⟨rfl, e⟩⟩
      · obtain ⟨x, hx⟩ := pm172_aux_sel_exists hM hR
        exact ⟨x, Or.inl ⟨hx, e⟩⟩

theorem pm172_aux_Beg_Cnv {x : α} {Q : α → α → Prop} :
    (Beg ⨾ Cnv) x Q ↔ x ∈ codom Q ∧ x ∉ dom Q := by
  constructor
  · rintro ⟨R, hB, hC⟩
    rw [Cnv_iff] at hC; rw [hC] at hB; exact hB
  · intro h; exact ⟨Q˘, h, Cnv_iff.2 rfl⟩

theorem pm172_aux_Beg_sub_F {x : α} {Q : α → α → Prop} (h : Beg x Q) : F x Q := by
  obtain ⟨⟨y, hy⟩, -⟩ := h; exact ⟨y, Or.inl hy⟩

theorem pm172_aux_BegCnv_sub_F {x : α} {Q : α → α → Prop} (h : (Beg ⨾ Cnv) x Q) : F x Q := by
  obtain ⟨⟨y, hy⟩, -⟩ := pm172_aux_Beg_Cnv.1 h; exact ⟨y, Or.inr hy⟩

end Helpers172b

/-- ✱172·01 (Df). \[\begin{align}\Pi ʻP=\hat{M} \hat{N} &\{M,N\in F_{\Delta }ʻCʻP\colon\ldotp \\ &(\exists Q):(MʻQ)Q(NʻQ):RPQ.R\neq Q.\supset _{R}.MʻR=NʻR\} \quad\text{Df}\end{align}\] -/
theorem pm172_01 (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    relPi P = fun M N => (M ∈ sel F (fld P) ∧ N ∈ sel F (fld P)) ∧
      ∃ Q, Desc M Q (fun x => Desc N Q (fun y => Q x y)) ∧
        ∀ R, P R Q ∧ R ≠ Q → Desc M R (fun x => Desc N R (fun y => x = y)) := rfl

/-- ✱172·1. \[\begin{align}\vdash \colon\colon M&(\Pi ʻP)N.\equiv \colon\ldotp M,N\in F_{\Delta }ʻCʻP\colon\ldotp \\ &(\exists Q):(MʻQ)Q(NʻQ):RPQ.R\neq Q.\supset _{R}.MʻR=NʻR\\ [(*172·01)]\end{align}\] -/
theorem pm172_1 {P : (α → α → Prop) → (α → α → Prop) → Prop} {M N : α → (α → α → Prop) → Prop} :
    relPi P M N ↔ (M ∈ sel F (fld P) ∧ N ∈ sel F (fld P)) ∧
      ∃ Q, Desc M Q (fun x => Desc N Q (fun y => Q x y)) ∧
        ∀ R, P R Q ∧ R ≠ Q → Desc M R (fun x => Desc N R (fun y => x = y)) := Iff.rfl

/-- ✱172·11. \[\begin{align}\vdash \colon\colon &M(\Pi ʻP)N.\equiv \colon\ldotp M,N\in F_{\Delta }ʻCʻP\colon\ldotp \\ &(\exists Q):Q\in CʻP.(MʻQ)Q(NʻQ):RPQ.R\neq Q.\supset _{R}.MʻR=NʻR\end{align}\] -/
theorem pm172_11 {P : (α → α → Prop) → (α → α → Prop) → Prop} {M N : α → (α → α → Prop) → Prop} :
    relPi P M N ↔ (M ∈ sel F (fld P) ∧ N ∈ sel F (fld P)) ∧
      ∃ Q, (Q ∈ fld P ∧ Desc M Q (fun x => Desc N Q (fun y => Q x y))) ∧
        ∀ R, P R Q ∧ R ≠ Q → Desc M R (fun x => Desc N R (fun y => x = y)) := by
  rw [pm172_1]
  refine and_congr_right fun hMN => exists_congr fun Q => ⟨?_, fun h => ⟨h.1.2, h.2⟩⟩
  rintro ⟨hd, hR⟩
  obtain ⟨x, hx, -⟩ := id hd
  exact ⟨⟨pm172_aux_sel_mem hMN.1 ((hx x).2 rfl), hd⟩, hR⟩

/-- ✱172·12. \(\vdash .Cʻ\Pi ʻP\subset F_{\Delta }ʻCʻP\) -/
theorem pm172_12 (P : (α → α → Prop) → (α → α → Prop) → Prop) : fld (relPi P) ⊆ sel F (fld P) := by
  rintro M ⟨N, ⟨⟨hM, -⟩, -⟩ | ⟨⟨-, hM⟩, -⟩⟩ <;> exact hM

/-- ✱172·13. \(\vdash .\Pi ʻ\dot{\Lambda} =\dot{\Lambda}\) -/
theorem pm172_13 : relPi (rNull : (α → α → Prop) → (α → α → Prop) → Prop) = rNull := by
  funext M N; apply propext
  constructor
  · rintro ⟨⟨hM, -⟩, Q, ⟨x, hx, -⟩, -⟩
    obtain ⟨R, hR | hR⟩ := pm172_aux_sel_mem hM ((hx x).2 rfl) <;> exact absurd hR (rNull_apply _ _)
  · intro h; exact absurd h (rNull_apply M N)

/-- ✱172·14. \(\vdash :\dot{\Lambda} \in CʻP.\supset .\Pi ʻP=\dot{\Lambda}\) -/
theorem pm172_14 {P : (α → α → Prop) → (α → α → Prop) → Prop} (h : rNull ∈ fld P) :
    relPi P = rNull := by
  funext M N; apply propext
  constructor
  · rintro ⟨⟨hM, -⟩, -⟩
    obtain ⟨x, hx⟩ := pm172_aux_sel_exists hM h
    obtain ⟨y, hy | hy⟩ := pm172_aux_sel_sub hM hx <;> exact absurd hy (rNull_apply _ _)
  · intro h'; exact absurd h' (rNull_apply M N)

/-- ✱172·141. \(\vdash \colon\ldotp \dot{\exists} !\Pi ʻP.\supset :Q\in CʻP.\supset _{Q}.\dot{\exists} !Q \quad[*172·14.\text{Transp}]\) -/
theorem pm172_141 {P : (α → α → Prop) → (α → α → Prop) → Prop} (h : rEx (relPi P)) :
    ∀ Q, Q ∈ fld P → rEx Q := by
  intro Q hQ
  by_contra h'
  rw [pm172_aux_rEx_iff_ne, not_not] at h'
  rw [h'] at hQ
  obtain ⟨M, N, hMN⟩ := h
  rw [pm172_14 hQ] at hMN; exact rNull_apply M N hMN

/-- ✱172·15. \(\vdash :M\in F_{\Delta }ʻCʻP.Q\in CʻP.(MʻQ)Qy.\supset .M(\Pi ʻP)\{M\upharpoonright -\iota ʻQ\unicode{x228d} y\downarrow Q\}\) -/
theorem pm172_15 {P : (α → α → Prop) → (α → α → Prop) → Prop} {M : α → (α → α → Prop) → Prop}
    {Q : α → α → Prop} {y : α}
    (h : (M ∈ sel F (fld P) ∧ Q ∈ fld P) ∧ Desc M Q (fun x => Q x y)) :
    relPi P M ((M ↾ (ι Q)ᶜ) ⊍ y ↓ Q) := by
  obtain ⟨⟨hM, hQ⟩, x, hx, hxy⟩ := h
  have hMx : M x Q := (hx x).2 rfl
  refine pm172_aux_relPi_iff.2 ⟨⟨hM, pm172_aux_modify hM hQ ⟨x, Or.inr hxy⟩⟩, Q, x, y,
    ⟨⟨hMx, Or.inr ⟨rfl, rfl⟩⟩, hxy⟩, fun R hR u hu => Or.inl ⟨hu, hR.2⟩⟩

/-- ✱172·151. \[\begin{align}\vdash :N\in F_{\Delta }ʻCʻP.&Q\in CʻP.yQ(NʻQ).\supset .\\ &\{N\upharpoonright -\iota ʻQ\unicode{x228d} y\downarrow Q\}(\Pi ʻP)N \quad[\text{Proof as in *172·15}]\end{align}\] -/
theorem pm172_151 {P : (α → α → Prop) → (α → α → Prop) → Prop} {N : α → (α → α → Prop) → Prop}
    {Q : α → α → Prop} {y : α}
    (h : (N ∈ sel F (fld P) ∧ Q ∈ fld P) ∧ Desc N Q (fun x => Q y x)) :
    relPi P ((N ↾ (ι Q)ᶜ) ⊍ y ↓ Q) N := by
  obtain ⟨⟨hN, hQ⟩, x, hx, hxy⟩ := h
  have hNx : N x Q := (hx x).2 rfl
  refine pm172_aux_relPi_iff.2 ⟨⟨pm172_aux_modify hN hQ ⟨x, Or.inl hxy⟩, hN⟩, Q, y, x,
    ⟨⟨Or.inr ⟨rfl, rfl⟩, hNx⟩, hxy⟩, fun R hR u hu => ?_⟩
  rcases hu with ⟨hu, -⟩ | ⟨-, hu⟩
  · exact hu
  · exact absurd hu hR.2

/-- ✱172·16. \(\vdash :M\in F_{\Delta }ʻCʻP.\dot{\exists} !M\dot{-} B.\supset .M\in \text{ᗡ}ʻ\Pi ʻP\) -/
theorem pm172_16 {P : (α → α → Prop) → (α → α → Prop) → Prop} {M : α → (α → α → Prop) → Prop}
    (h : M ∈ sel F (fld P) ∧ rEx (M ∸ Beg)) : M ∈ codom (relPi P) := by
  obtain ⟨hM, x, Q, hxQ, hB⟩ := h
  have hF := pm172_aux_sel_sub hM hxQ
  have : x ∈ codom Q := by
    by_contra h'
    refine hB ⟨?_, h'⟩
    obtain ⟨y, hy | hy⟩ := hF
    · exact ⟨y, hy⟩
    · exact absurd ⟨y, hy⟩ h'
  obtain ⟨y, hy⟩ := this
  exact ⟨_, pm172_151 ⟨⟨hM, pm172_aux_sel_mem hM hxQ⟩, (pm172_aux_desc_sel hM hxQ _).2 hy⟩⟩

/-- ✱172·161. \(\vdash :M\in F_{\Delta }ʻCʻP.\dot{\exists} !M\dot{-} B\mid \text{Cnv}.\supset .M\in \text{D}ʻ\Pi ʻP\) -/
theorem pm172_161 {P : (α → α → Prop) → (α → α → Prop) → Prop} {M : α → (α → α → Prop) → Prop}
    (h : M ∈ sel F (fld P) ∧ rEx (M ∸ Beg ⨾ Cnv)) : M ∈ dom (relPi P) := by
  obtain ⟨hM, x, Q, hxQ, hB⟩ := h
  have hF := pm172_aux_sel_sub hM hxQ
  have : x ∈ dom Q := by
    by_contra h'
    refine hB (pm172_aux_Beg_Cnv.2 ⟨?_, h'⟩)
    obtain ⟨y, hy | hy⟩ := hF
    · exact absurd ⟨y, hy⟩ h'
    · exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := this
  exact ⟨_, pm172_15 ⟨⟨hM, pm172_aux_sel_mem hM hxQ⟩, (pm172_aux_desc_sel hM hxQ _).2 hy⟩⟩

theorem pm172_aux_dom_iff {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M : α → (α → α → Prop) → Prop} (hP : rEx P) :
    M ∈ dom (relPi P) ↔ M ∈ sel F (fld P) ∧ M ∉ sel (Beg ⨾ Cnv) (fld P) := by
  constructor
  · rintro ⟨N, hMN⟩
    obtain ⟨⟨hM, hN⟩, Q, x, y, ⟨⟨hx, -⟩, hq⟩, -⟩ := pm172_aux_relPi_iff.1 hMN
    refine ⟨hM, fun h' => ?_⟩
    exact (pm172_aux_Beg_Cnv.1 ((mem_sel_iff.1 h').1.2 x Q hx)).2 ⟨y, hq⟩
  · rintro ⟨hM, hM'⟩
    by_cases h' : M ⪽ Beg ⨾ Cnv
    · exact absurd ((pm172_aux_sel_iff_sub hM).2 h') hM'
    · simp only [RSub, not_forall] at h'
      obtain ⟨x, Q, hxQ, hB⟩ := h'
      exact pm172_161 ⟨hM, x, Q, hxQ, hB⟩

theorem pm172_aux_codom_iff {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M : α → (α → α → Prop) → Prop} :
    M ∈ codom (relPi P) ↔ M ∈ sel F (fld P) ∧ M ∉ sel Beg (fld P) := by
  constructor
  · rintro ⟨N, hMN⟩
    obtain ⟨⟨hN, hM⟩, Q, x, y, ⟨⟨-, hy⟩, hq⟩, -⟩ := pm172_aux_relPi_iff.1 hMN
    refine ⟨hM, fun h' => ?_⟩
    exact ((mem_sel_iff.1 h').1.2 y Q hy).2 ⟨x, hq⟩
  · rintro ⟨hM, hM'⟩
    by_cases h' : M ⪽ Beg
    · exact absurd ((pm172_aux_sel_iff_sub hM).2 h') hM'
    · simp only [RSub, not_forall] at h'
      obtain ⟨x, Q, hxQ, hB⟩ := h'
      exact pm172_16 ⟨hM, x, Q, hxQ, hB⟩

theorem pm172_aux_sel_Beg_dom {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M : α → (α → α → Prop) → Prop} (hP : rEx P) (h : M ∈ sel Beg (fld P)) :
    M ∈ dom (relPi P) := by
  have hM : M ∈ sel F (fld P) := (pm172_aux_sel_iff_sub h).2 fun x Q hx =>
    pm172_aux_Beg_sub_F ((mem_sel_iff.1 h).1.2 x Q hx)
  obtain ⟨Q, hQ⟩ := pm170_aux_rEx_iff_fld.1 hP
  obtain ⟨x, hx⟩ := pm172_aux_sel_exists hM hQ
  obtain ⟨⟨y, hy⟩, -⟩ := (mem_sel_iff.1 h).1.2 x Q hx
  exact ⟨_, pm172_15 ⟨⟨hM, hQ⟩, (pm172_aux_desc_sel hM hx _).2 hy⟩⟩

theorem pm172_aux_sel_BegCnv_codom {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M : α → (α → α → Prop) → Prop} (hP : rEx P) (h : M ∈ sel (Beg ⨾ Cnv) (fld P)) :
    M ∈ codom (relPi P) := by
  have hM : M ∈ sel F (fld P) := (pm172_aux_sel_iff_sub h).2 fun x Q hx =>
    pm172_aux_BegCnv_sub_F ((mem_sel_iff.1 h).1.2 x Q hx)
  obtain ⟨Q, hQ⟩ := pm170_aux_rEx_iff_fld.1 hP
  obtain ⟨x, hx⟩ := pm172_aux_sel_exists hM hQ
  obtain ⟨⟨y, hy⟩, -⟩ := pm172_aux_Beg_Cnv.1 ((mem_sel_iff.1 h).1.2 x Q hx)
  exact ⟨_, pm172_151 ⟨⟨hM, hQ⟩, (pm172_aux_desc_sel hM hx _).2 hy⟩⟩

theorem pm172_aux_162 {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : rEx P) :
    refs Beg (relPi P) = sel Beg (fld P) ∧ refs Beg (relPi P)˘ = sel (Beg ⨾ Cnv) (fld P) := by
  constructor
  · ext M; constructor
    · rintro ⟨hd, hc⟩
      have hM := (pm172_aux_dom_iff hP).1 hd |>.1
      by_contra h'
      exact hc ((pm172_aux_codom_iff).2 ⟨hM, h'⟩)
    · intro h
      refine ⟨pm172_aux_sel_Beg_dom hP h, fun hc => (pm172_aux_codom_iff.1 hc).2 h⟩
  · ext M; constructor
    · rintro ⟨hc, hd⟩
      have hM := (pm172_aux_codom_iff.1 hc).1
      by_contra h'
      exact hd ((pm172_aux_dom_iff hP).2 ⟨hM, h'⟩)
    · intro h
      exact ⟨pm172_aux_sel_BegCnv_codom hP h, fun hd => ((pm172_aux_dom_iff hP).1 hd).2 h⟩

/-- The counterexample for the printed ✱172·162·171: `Q = ⊤ ↓ ⊥` on `Bool`, `P = Q ↓ Q`. -/
theorem pm172_aux_cex :
    let Q : Bool → Bool → Prop := true ↓ false
    let P : (Bool → Bool → Prop) → (Bool → Bool → Prop) → Prop := Q ↓ Q
    rEx P ∧ (false ↓ Q) ∈ sel (Beg ⨾ Cnv) (fld P) ∧ (false ↓ Q) ∉ sel Beg (Cnv ʻʻ fld P) := by
  intro Q P
  have hQ : Q ≠ Q˘ := fun e => by
    have : Q true false := ⟨rfl, rfl⟩
    rw [e] at this; exact Bool.false_ne_true this.1
  refine ⟨⟨Q, Q, rfl, rfl⟩, pm172_aux_mk_sel ?_ ?_ ?_, fun h => ?_⟩
  · rintro x y R ⟨h1, -⟩ ⟨h2, -⟩; exact (show x = false from h1).trans (show y = false from h2).symm
  · rintro x R ⟨h1, h2⟩
    rw [show x = false from h1, show R = Q from h2]
    exact pm172_aux_Beg_Cnv.2 ⟨⟨true, rfl, rfl⟩, fun ⟨y, hy⟩ => Bool.false_ne_true hy.1⟩
  · ext R; constructor
    · rintro ⟨x, -, h2⟩; rw [pm170_aux_fld_couple, show R = Q from h2]; exact Or.inl rfl
    · intro hR
      rw [pm170_aux_fld_couple] at hR
      have : R = Q := by rcases hR with h' | h' <;> exact h'
      exact ⟨false, rfl, this⟩
  · have : Q ∈ Cnv ʻʻ fld P := by rw [← (mem_sel_iff.1 h).2]; exact ⟨false, rfl, rfl⟩
    obtain ⟨R, hR, hC⟩ := this
    rw [pm170_aux_fld_couple] at hR
    have hRQ : R = Q := by rcases hR with h' | h' <;> exact h'
    rw [Cnv_iff, hRQ] at hC; exact hQ hC

/-- ✱172·162. \(\vdash :\dot{\exists} !P.\supset .\overrightarrow{B}ʻ\Pi ʻP=B_{\Delta }ʻCʻP.\overrightarrow{B}ʻ\text{Cnv}ʻ\Pi ʻP=B_{\Delta }ʻ\text{Cnv}ʻʻCʻP\)

**Status.** proved (corrected): the second equation is false as printed: `B_Δ'Cnv''C'P` consists of
selections whose converse domain is `Cnv''C'P`, while the members of `B⃗'Cnv'Π'P` are selections
from `C'P`. E.g. for `Q = ⊤ ↓ ⊥` on `Bool` and `P = Q ↓ Q`, the selection `⊥ ↓ Q` is the last term
of `Π'P` but is not in `B_Δ'Cnv''C'P = B_Δ'ι'Q̆` (`pm172_162_printed_false`). The correct value, as
in PM's demonstration via ✱172·161, is `(B | Cnv)_Δ'C'P`, the selections choosing in each `Q` a last
term (a beginning of `Q̆`). -/
theorem pm172_162 {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : rEx P) :
    refs Beg (relPi P) = sel Beg (fld P) ∧ refs Beg (relPi P)˘ = sel (Beg ⨾ Cnv) (fld P) :=
  pm172_aux_162 hP

theorem pm172_162_printed_false :
    ¬ ∀ P : (Bool → Bool → Prop) → (Bool → Bool → Prop) → Prop, rEx P →
      refs Beg (relPi P)˘ = sel Beg (Cnv ʻʻ fld P) := by
  intro h
  obtain ⟨hP, h1, h2⟩ := pm172_aux_cex
  refine h2 ?_
  rw [← h _ hP, (pm172_aux_162 hP).2]; exact h1

/-- ✱172·17. \(\vdash :\dot{\exists} !P.\supset .Cʻ\Pi ʻP=F_{\Delta }ʻCʻP\) -/
theorem pm172_17 {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : rEx P) :
    fld (relPi P) = sel F (fld P) := by
  refine Set.Subset.antisymm (pm172_12 P) (fun M hM => ?_)
  by_cases h : M ∈ sel Beg (fld P)
  · obtain ⟨N, hN⟩ := pm172_aux_sel_Beg_dom hP h; exact ⟨N, Or.inl hN⟩
  · obtain ⟨N, hN⟩ := pm172_aux_codom_iff.2 ⟨hM, h⟩; exact ⟨N, Or.inr hN⟩

/-- ✱172·171. \[\begin{align}\vdash :\dot{\exists} !P.\supset .&\text{D}ʻ\Pi ʻP=F_{\Delta }ʻCʻP-B_{\Delta }ʻ\text{Cnv}ʻʻCʻP.\\ &\text{ᗡ}ʻ\Pi ʻP=F_{\Delta }ʻCʻP-B_{\Delta }ʻCʻP \quad[*172·162·17]\end{align}\]

**Status.** proved (corrected): the first equation is false as printed, for the reason given at
✱172·162: with `Q = ⊤ ↓ ⊥`, `P = Q ↓ Q`, the last term `⊥ ↓ Q` of `Π'P` is in `F_Δ'C'P −
B_Δ'Cnv''C'P` but not in `D'Π'P` (`pm172_171_printed_false`). Corrected with `(B | Cnv)_Δ'C'P`. -/
theorem pm172_171 {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : rEx P) :
    dom (relPi P) = sel F (fld P) \ sel (Beg ⨾ Cnv) (fld P) ∧
      codom (relPi P) = sel F (fld P) \ sel Beg (fld P) :=
  ⟨Set.ext fun _ => pm172_aux_dom_iff hP, Set.ext fun _ => pm172_aux_codom_iff⟩

theorem pm172_171_printed_false :
    ¬ ∀ P : (Bool → Bool → Prop) → (Bool → Bool → Prop) → Prop, rEx P →
      dom (relPi P) = sel F (fld P) \ sel Beg (Cnv ʻʻ fld P) := by
  intro h
  obtain ⟨hP, h1, h2⟩ := pm172_aux_cex
  have hM : (false ↓ (true ↓ false : Bool → Bool → Prop)) ∈
      sel F (fld ((true ↓ false : Bool → Bool → Prop) ↓ (true ↓ false))) :=
    (pm172_aux_sel_iff_sub h1).2 fun x Q hx => pm172_aux_BegCnv_sub_F ((mem_sel_iff.1 h1).1.2 x Q hx)
  have : (false ↓ (true ↓ false : Bool → Bool → Prop)) ∈ dom (relPi
      ((true ↓ false : Bool → Bool → Prop) ↓ (true ↓ false))) := by
    rw [h _ hP]; exact ⟨hM, h2⟩
  exact ((pm172_aux_dom_iff hP).1 this).2 h1

/-- ✱172·18. \(\vdash \colon\ldotp \dot{\exists} !P.\supset :\dot{\exists} !\Pi ʻP.\equiv .\exists !F_{\Delta }ʻCʻP \quad[*172·17]\) -/
theorem pm172_18 {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : rEx P) :
    rEx (relPi P) ↔ (sel F (fld P)).Nonempty := by
  rw [pm170_aux_rEx_iff_fld, pm172_17 hP]

/-- ✱172·181. \(\vdash \colon\ldotp \text{Mult ax}.\supset :\dot{\Lambda} {\sim}\in CʻP.\dot{\exists} !P.\equiv .\dot{\exists} !\Pi ʻP\)

**Status.** proved (reading): `Mult ax` is taken at the type of the couples `x ↓ Q` (the selections
are relations of this type, ✱88); it is a theorem of Lean (Basic §4) and is not used in the proof. -/
theorem pm172_181 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    (_hm : MultAx (α → (α → α → Prop) → Prop)) : (rNull ∉ fld P ∧ rEx P) ↔ rEx (relPi P) := by
  constructor
  · rintro ⟨hN, hP⟩
    obtain ⟨Q0, hQ0⟩ := pm170_aux_rEx_iff_fld.1 hP
    have hex : ∀ Q, Q ∈ fld P → (fld Q).Nonempty := fun Q hQ =>
      pm170_aux_rEx_iff_fld.1 (pm172_aux_rEx_iff_ne.2 fun e => hN (e ▸ hQ))
    obtain ⟨a, -⟩ := hex Q0 hQ0
    have : Nonempty α := ⟨a⟩
    let c : (α → α → Prop) → α := fun Q => Classical.epsilon (· ∈ fld Q)
    have hc : ∀ Q, Q ∈ fld P → c Q ∈ fld Q := fun Q hQ => Classical.epsilon_spec (hex Q hQ)
    refine (pm172_18 hP).2 ⟨fun x Q => Q ∈ fld P ∧ x = c Q, pm172_aux_mk_sel ?_ ?_ ?_⟩
    · rintro x y Q ⟨-, rfl⟩ ⟨-, rfl⟩; rfl
    · rintro x Q ⟨hQ, rfl⟩; exact hc Q hQ
    · ext Q; exact ⟨fun ⟨_, hQ, _⟩ => hQ, fun hQ => ⟨c Q, hQ, rfl⟩⟩
  · intro h
    refine ⟨fun hN => ?_, ?_⟩
    · obtain ⟨M, N, hMN⟩ := h; rw [pm172_14 hN] at hMN; exact rNull_apply M N hMN
    · by_contra hP
      have : P = rNull := by
        by_contra h'; exact hP (pm172_aux_rEx_iff_ne.2 h')
      obtain ⟨M, N, hMN⟩ := h; rw [this, pm172_13] at hMN; exact rNull_apply M N hMN

/-- ✱172·182. \[\begin{align}&\vdash \colon\colon \text{Mult ax}.\supset \colon\ldotp \dot{\Lambda} \in CʻP.\lor.P=\dot{\Lambda} :\equiv .\Pi ʻP=\dot{\Lambda}\\ &[*172·181.\text{Transp}]\end{align}\]

**Status.** proved (reading): `Mult ax` is taken as in ✱172·181. -/
theorem pm172_182 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    (hm : MultAx (α → (α → α → Prop) → Prop)) : (rNull ∈ fld P ∨ P = rNull) ↔ relPi P = rNull := by
  have h := pm172_181 (P := P) hm
  rw [pm172_aux_rEx_iff_ne, pm172_aux_rEx_iff_ne] at h
  constructor
  · intro h'; by_contra h''
    obtain ⟨h1, h2⟩ := h.2 h''
    rcases h' with h' | h'
    · exact h1 h'
    · exact h2 h'
  · intro h'
    by_contra h''
    push Not at h''
    exact h.1 h'' h'

/-- ✱172·19. \(\vdash :\dot{\exists} !\Pi ʻP.\supset .\dot{s} ʻCʻ\Pi ʻP=F\upharpoonright CʻP \quad[*172·17.*80·42]\) -/
theorem pm172_19 {P : (α → α → Prop) → (α → α → Prop) → Prop} (h : rEx (relPi P)) :
    sumRel (fld (relPi P)) = F ↾ fld P := by
  have hP : rEx P := by
    by_contra hP
    have : P = rNull := by by_contra h'; exact hP (pm172_aux_rEx_iff_ne.2 h')
    obtain ⟨M, N, hMN⟩ := h; rw [this, pm172_13] at hMN; exact rNull_apply M N hMN
  rw [pm172_17 hP]
  funext x Q; apply propext
  constructor
  · rintro ⟨M, hM, hx⟩; exact ⟨pm172_aux_sel_sub hM hx, pm172_aux_sel_mem hM hx⟩
  · rintro ⟨hF, hQ⟩
    obtain ⟨M0, hM0⟩ := (pm172_18 hP).1 h
    exact ⟨_, pm172_aux_modify hM0 hQ hF, Or.inr ⟨rfl, rfl⟩⟩

/-- ✱172·191. \(\vdash .\dot{s} ʻCʻ\Pi ʻP\,\unicode{x2abd}\, F\upharpoonright CʻP\) -/
theorem pm172_191 (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    sumRel (fld (relPi P)) ⪽ F ↾ fld P := by
  rintro x Q ⟨M, hM, hx⟩
  have hM' := pm172_12 P hM
  exact ⟨pm172_aux_sel_sub hM' hx, pm172_aux_sel_mem hM' hx⟩

/-- ✱172·192. \(\vdash .\text{ᗡ}ʻ(F\upharpoonright \beta )=\beta -\iota ʻ\dot{\Lambda}\) -/
theorem pm172_192 (B : Set (α → α → Prop)) : codom (F ↾ B) = B \ ι rNull := by
  ext Q; constructor
  · rintro ⟨x, hF, hQ⟩
    refine ⟨hQ, fun e => ?_⟩
    rw [pm170_aux_mem_iota.1 e] at hF
    obtain ⟨y, hy | hy⟩ := hF <;> exact rNull_apply _ _ hy
  · rintro ⟨hQ, hne⟩
    have : rEx Q := pm172_aux_rEx_iff_ne.2 fun e => hne (pm170_aux_mem_iota.2 e)
    obtain ⟨x, hx⟩ := pm170_aux_rEx_iff_fld.1 this
    exact ⟨x, hx, hQ⟩

section Helpers172c
variable {α : Type u}

theorem pm172_aux_couple_sel {x : α} {Q : α → α → Prop} (hx : x ∈ fld Q) :
    (x ↓ Q) ∈ sel F (ι Q) := by
  refine pm172_aux_mk_sel ?_ ?_ ?_
  · rintro u v R ⟨h1, -⟩ ⟨h2, -⟩; exact (show u = x from h1).trans (show v = x from h2).symm
  · rintro u R ⟨h1, h2⟩; rw [show u = x from h1, show R = Q from h2]; exact hx
  · ext R; exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨x, rfl, h⟩⟩

theorem pm172_aux_sel_eq_couple {M : α → (α → α → Prop) → Prop} {Q : α → α → Prop}
    (hM : M ∈ sel F (ι Q)) {x : α} (hx : M x Q) : M = x ↓ Q := by
  funext u R; apply propext
  constructor
  · intro h
    have hR : R = Q := pm172_aux_sel_mem hM h
    rw [hR] at h
    exact ⟨pm172_aux_sel_unique hM h hx, hR⟩
  · rintro ⟨h1, h2⟩; rw [show u = x from h1, show R = Q from h2]; exact hx

theorem pm172_aux_two_sel {P Q : α → α → Prop} (hne : P ≠ Q) {a b : α} (ha : a ∈ fld P)
    (hb : b ∈ fld Q) : (a ↓ P) ⊍ (b ↓ Q) ∈ sel F (ι P ∪ ι Q) := by
  refine pm172_aux_mk_sel ?_ ?_ ?_
  · rintro u v R (⟨h1, h1'⟩ | ⟨h1, h1'⟩) (⟨h2, h2'⟩ | ⟨h2, h2'⟩)
    · exact (show u = a from h1).trans (show v = a from h2).symm
    · exact absurd ((show R = P from h1').symm.trans h2') hne
    · exact absurd ((show R = P from h2').symm.trans h1') hne
    · exact (show u = b from h1).trans (show v = b from h2).symm
  · rintro u R (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [show u = a from h1, show R = P from h2]; exact ha
    · rw [show u = b from h1, show R = Q from h2]; exact hb
  · ext R; constructor
    · rintro ⟨u, ⟨-, h⟩ | ⟨-, h⟩⟩
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact ⟨a, Or.inl ⟨rfl, h⟩⟩
      · exact ⟨b, Or.inr ⟨rfl, h⟩⟩

theorem pm172_aux_dagger_two {P Q : α → α → Prop} {M : α → (α → α → Prop) → Prop}
    (hM : M ∈ sel F (ι P ∪ ι Q)) {a b : α} (ha : M a P) (hb : M b Q) :
    daggerOp M (Q ↓ P) = b ↓ a := by
  funext u v; apply propext
  constructor
  · rintro ⟨w, ⟨z, hz, h1, h2⟩, hv⟩
    rw [show z = Q from h1] at hz; rw [show w = P from h2] at hv
    exact ⟨pm172_aux_sel_unique hM hz hb, pm172_aux_sel_unique hM hv ha⟩
  · rintro ⟨h1, h2⟩
    rw [show u = b from h1, show v = a from h2]
    exact ⟨P, ⟨Q, hb, rfl, rfl⟩, ha⟩

theorem pm172_aux_relPi_two {P Q : α → α → Prop} (hne : P ≠ Q) {M N : α → (α → α → Prop) → Prop}
    (hM : M ∈ sel F (ι P ∪ ι Q)) (hN : N ∈ sel F (ι P ∪ ι Q)) {a b c d : α} (ha : M a P)
    (hb : M b Q) (hc : N c P) (hd : N d Q) :
    relPi (P ↓ Q) M N ↔ P a c ∨ (a = c ∧ Q b d) := by
  rw [pm172_aux_relPi_iff, pm170_aux_fld_couple]
  constructor
  · rintro ⟨-, R, x, y, ⟨⟨hx, hy⟩, hq⟩, hR⟩
    rcases pm172_aux_sel_mem hM hx with h | h <;> rw [pm170_aux_mem_iota] at h <;> rw [h] at hx hy hq
    · rw [pm172_aux_sel_unique hM hx ha, pm172_aux_sel_unique hN hy hc] at hq
      exact Or.inl hq
    · rw [pm172_aux_sel_unique hM hx hb, pm172_aux_sel_unique hN hy hd] at hq
      have := hR P ⟨⟨rfl, h⟩, fun e => hne (e.trans h)⟩ a ha
      exact Or.inr ⟨pm172_aux_sel_unique hN this hc, hq⟩
  · rintro (h | ⟨rfl, h⟩)
    · refine ⟨⟨hM, hN⟩, P, a, c, ⟨⟨ha, hc⟩, h⟩, fun R ⟨⟨_, h'⟩, _⟩ => absurd h' hne⟩
    · refine ⟨⟨hM, hN⟩, Q, b, d, ⟨⟨hb, hd⟩, h⟩, fun R ⟨⟨h1, _⟩, _⟩ u hu => ?_⟩
      rw [show R = P from h1] at hu ⊢
      rw [pm172_aux_sel_unique hM hu ha]; exact hc

theorem pm172_aux_sel_two_vals {P Q : α → α → Prop} {M : α → (α → α → Prop) → Prop}
    (hM : M ∈ sel F (ι P ∪ ι Q)) : ∃ a b, M a P ∧ M b Q :=
  let ⟨a, ha⟩ := pm172_aux_sel_exists hM (Or.inl rfl)
  let ⟨b, hb⟩ := pm172_aux_sel_exists hM (Or.inr rfl)
  ⟨a, b, ha, hb⟩

end Helpers172c

/-- ✱172·2. \(\vdash .\Pi ʻ(P\downarrow P)=P\downarrow_{.,} P\) -/
theorem pm172_2 (P : α → α → Prop) : relPi (P ↓ P) = opSemi couple P P := by
  have hfld : fld (P ↓ P) = ι P := by rw [pm170_aux_fld_couple, Set.union_self]
  funext M N; apply propext
  rw [pm172_aux_relPi_iff, opSemi_couple_apply, hfld]
  constructor
  · rintro ⟨⟨hM, hN⟩, Q, x, y, ⟨⟨hx, hy⟩, hq⟩, -⟩
    have hQ : Q = P := pm172_aux_sel_mem hM hx
    rw [hQ] at hx hy hq
    exact ⟨x, y, ⟨pm172_aux_sel_eq_couple hM hx, pm172_aux_sel_eq_couple hN hy⟩, hq⟩
  · rintro ⟨x, y, ⟨rfl, rfl⟩, hxy⟩
    refine ⟨⟨pm172_aux_couple_sel ⟨y, Or.inl hxy⟩, pm172_aux_couple_sel ⟨x, Or.inr hxy⟩⟩, P, x, y,
      ⟨⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, hxy⟩, fun R ⟨⟨h1, _⟩, h2⟩ => absurd h1 h2⟩

/-- ✱172·21. \(\vdash :P\neq Q.\supset .P\times Q=\dagger (Q\downarrow P)^{;}\Pi ʻ(P\downarrow Q)\) -/
theorem pm172_21 {P Q : α → α → Prop} (hne : P ≠ Q) :
    P ×ᵣ Q = opR daggerOp (Q ↓ P) ⁏ relPi (P ↓ Q) := by
  funext U V; apply propext
  rw [show (opR daggerOp (Q ↓ P) : _ → (α → (α → α → Prop) → Prop) → Prop) =
    graph (fun M => daggerOp M (Q ↓ P)) from rfl, semi_graph_apply]
  constructor
  · intro h
    obtain ⟨b, a, ⟨hb, ha⟩, rfl⟩ := pm170_aux_fld_rtimes ⟨V, Or.inl h⟩
    obtain ⟨d, c, ⟨hd, hc⟩, rfl⟩ := pm170_aux_fld_rtimes ⟨_, Or.inr h⟩
    have hM := pm172_aux_two_sel hne ha hb
    have hN := pm172_aux_two_sel hne hc hd
    refine ⟨_, _, ⟨(pm172_aux_dagger_two hM (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)).symm,
      (pm172_aux_dagger_two hN (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)).symm⟩, ?_⟩
    rw [pm172_aux_relPi_two hne hM hN (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
      (Or.inr ⟨rfl, rfl⟩)]
    rcases (pm170_aux_rtimes_couple P Q b d a c).1 h with ⟨-, rfl, h'⟩ | ⟨h', -, -⟩
    · exact Or.inr ⟨rfl, h'⟩
    · exact Or.inl h'
  · rintro ⟨M, N, ⟨rfl, rfl⟩, hMN⟩
    have hMN' := hMN
    rw [pm172_aux_relPi_iff, pm170_aux_fld_couple] at hMN'
    obtain ⟨⟨hM, hN⟩, -⟩ := hMN'
    obtain ⟨a, b, ha, hb⟩ := pm172_aux_sel_two_vals hM
    obtain ⟨c, d, hc, hd⟩ := pm172_aux_sel_two_vals hN
    rw [pm172_aux_dagger_two hM ha hb, pm172_aux_dagger_two hN hc hd, pm170_aux_rtimes_couple]
    rcases (pm172_aux_relPi_two hne hM hN ha hb hc hd).1 hMN with h' | ⟨rfl, h'⟩
    · exact Or.inr ⟨h', pm172_aux_sel_sub hM hb, pm172_aux_sel_sub hN hd⟩
    · exact Or.inl ⟨pm172_aux_sel_sub hM ha, rfl, h'⟩

/-- ✱172·22. \(\vdash :P\neq Q.\supset .\{\dagger (Q\downarrow P)\}\upharpoonright F_{\Delta }ʻ(\iota ʻP\cup \iota ʻQ)\in (P\times Q)\,\overline{\text{smor}}\,\Pi ʻ(P\downarrow Q)\) -/
theorem pm172_22 {P Q : α → α → Prop} (hne : P ≠ Q) :
    opR daggerOp (Q ↓ P) ↾ sel F (ι P ∪ ι Q) ∈ smorbar (P ×ᵣ Q) (relPi (P ↓ Q)) := by
  have hfld : fld (relPi (P ↓ Q)) = sel F (ι P ∪ ι Q) := by
    rw [pm172_17 ⟨P, Q, rfl, rfl⟩, pm170_aux_fld_couple]
  rw [← hfld]
  apply pm170_aux_smorbar (fun M => daggerOp M (Q ↓ P))
  · intro M N hM hN e
    rw [hfld] at hM hN
    obtain ⟨a, b, ha, hb⟩ := pm172_aux_sel_two_vals hM
    obtain ⟨c, d, hc, hd⟩ := pm172_aux_sel_two_vals hN
    simp only [pm172_aux_dagger_two hM ha hb, pm172_aux_dagger_two hN hc hd,
      couple_eq_couple_iff] at e
    obtain ⟨rfl, rfl⟩ := e
    refine pm172_aux_sel_ext hM hN fun x R hx => ?_
    rcases pm172_aux_sel_mem hM hx with h | h <;> rw [pm170_aux_mem_iota] at h <;> rw [h] at hx ⊢
    · rw [pm172_aux_sel_unique hM hx ha]; exact hc
    · rw [pm172_aux_sel_unique hM hx hb]; exact hd
  · intro U V
    rw [pm172_21 hne, show (opR daggerOp (Q ↓ P) : _ → (α → (α → α → Prop) → Prop) → Prop) =
      graph (fun M => daggerOp M (Q ↓ P)) from rfl, semi_graph_apply]
    exact ⟨fun ⟨M, N, ⟨h1, h2⟩, h3⟩ => ⟨M, N, h3, h1, h2⟩, fun ⟨M, N, h3, h1, h2⟩ => ⟨M, N, ⟨h1, h2⟩, h3⟩⟩

/-- ✱172·23. \(\vdash :P\neq Q.\supset .\Pi ʻ(P\downarrow Q)\,\text{smor}\,P\times Q \quad[*172·22]\) -/
theorem pm172_23 {P Q : α → α → Prop} (hne : P ≠ Q) : smor (relPi (P ↓ Q)) (P ×ᵣ Q) :=
  smor_symm ⟨_, pm172_22 hne⟩

section Helpers172d
variable {α : Type u}

theorem pm172_aux_inter_Null {A B : Set α} : A ∩ B = Λ ↔ ∀ x, x ∈ A → x ∈ B → False := by
  rw [pm170_aux_Null_eq, Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h x ha hb => h x ⟨ha, hb⟩, fun h x hx => h x hx.1 hx.2⟩

theorem pm172_aux_relPi_congr {P Q : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : fld P = fld Q ∧ P ⩀ J = Q ⩀ J) : relPi P = relPi Q := by
  have e : ∀ R S, (P R S ∧ R ≠ S) ↔ (Q R S ∧ R ≠ S) := fun R S =>
    Iff.of_eq (congrFun (congrFun h.2 R) S)
  funext M N; apply propext
  rw [pm172_aux_relPi_iff, pm172_aux_relPi_iff, h.1]
  simp only [e]

theorem pm172_aux_restrict_sel {K L : Set (α → α → Prop)} {M : α → (α → α → Prop) → Prop}
    (hM : M ∈ sel F (K ∪ L)) : M ↾ K ∈ sel F K := by
  refine pm172_aux_mk_sel (fun x y Q h1 h2 => pm172_aux_sel_unique hM h1.1 h2.1)
    (fun x Q h => pm172_aux_sel_sub hM h.1) ?_
  ext Q; constructor
  · rintro ⟨x, -, hQ⟩; exact hQ
  · intro hQ; obtain ⟨x, hx⟩ := pm172_aux_sel_exists hM (Or.inl hQ); exact ⟨x, hx, hQ⟩

theorem pm172_aux_union_sel {K L : Set (α → α → Prop)} (hd : K ∩ L = Λ)
    {S T : α → (α → α → Prop) → Prop} (hS : S ∈ sel F K) (hT : T ∈ sel F L) :
    S ⊍ T ∈ sel F (K ∪ L) := by
  have dj : ∀ {Q}, Q ∈ K → Q ∈ L → False := fun h1 h2 =>
    pm172_aux_inter_Null.1 hd _ h1 h2
  refine pm172_aux_mk_sel ?_ ?_ ?_
  · rintro x y Q (h1 | h1) (h2 | h2)
    · exact pm172_aux_sel_unique hS h1 h2
    · exact (dj (pm172_aux_sel_mem hS h1) (pm172_aux_sel_mem hT h2)).elim
    · exact (dj (pm172_aux_sel_mem hS h2) (pm172_aux_sel_mem hT h1)).elim
    · exact pm172_aux_sel_unique hT h1 h2
  · rintro x Q (h | h)
    · exact pm172_aux_sel_sub hS h
    · exact pm172_aux_sel_sub hT h
  · ext Q; constructor
    · rintro ⟨x, h | h⟩
      · exact Or.inl (pm172_aux_sel_mem hS h)
      · exact Or.inr (pm172_aux_sel_mem hT h)
    · rintro (h | h)
      · obtain ⟨x, hx⟩ := pm172_aux_sel_exists hS h; exact ⟨x, Or.inl hx⟩
      · obtain ⟨x, hx⟩ := pm172_aux_sel_exists hT h; exact ⟨x, Or.inr hx⟩

theorem pm172_aux_split {K L : Set (α → α → Prop)} {M : α → (α → α → Prop) → Prop}
    (hM : M ∈ sel F (K ∪ L)) : M = (M ↾ K) ⊍ (M ↾ L) := by
  funext x Q; apply propext
  constructor
  · intro h
    rcases pm172_aux_sel_mem hM h with hQ | hQ
    · exact Or.inl ⟨h, hQ⟩
    · exact Or.inr ⟨h, hQ⟩
  · rintro (h | h) <;> exact h.1

/-- The restriction to `K` of `S ∪̇ T`, for selections from disjoint `K`, `L`. -/
theorem pm172_aux_union_restrict {K L : Set (α → α → Prop)} (hd : K ∩ L = Λ)
    {S T : α → (α → α → Prop) → Prop} (hS : S ∈ sel F K) (hT : T ∈ sel F L) :
    (S ⊍ T) ↾ K = S ∧ (S ⊍ T) ↾ L = T := by
  have dj : ∀ {Q}, Q ∈ K → Q ∈ L → False := fun h1 h2 =>
    pm172_aux_inter_Null.1 hd _ h1 h2
  constructor
  · funext x Q; apply propext
    constructor
    · rintro ⟨h | h, hQ⟩
      · exact h
      · exact (dj hQ (pm172_aux_sel_mem hT h)).elim
    · intro h; exact ⟨Or.inl h, pm172_aux_sel_mem hS h⟩
  · funext x Q; apply propext
    constructor
    · rintro ⟨h | h, hQ⟩
      · exact (dj (pm172_aux_sel_mem hS h) hQ).elim
      · exact h
    · intro h; exact ⟨Or.inr h, pm172_aux_sel_mem hT h⟩

/-- The equivalence of ✱172·33 without its existence hypotheses (only the disjointness of the
fields is used). -/
theorem pm172_aux_33 {P Q : (α → α → Prop) → (α → α → Prop) → Prop} (hd : fld P ∩ fld Q = Λ)
    {M N : α → (α → α → Prop) → Prop} :
    relPi (P ⤉ Q) M N ↔ ∃ S T S' T', (((S ∈ sel F (fld P) ∧ S' ∈ sel F (fld P)) ∧
      (T ∈ sel F (fld Q) ∧ T' ∈ sel F (fld Q))) ∧ (relPi P S S' ∨ (S = S' ∧ relPi Q T T'))) ∧
      (M = S ⊍ T ∧ N = S' ⊍ T') := by
  have dj : ∀ {R}, R ∈ fld P → R ∈ fld Q → False := fun h1 h2 =>
    pm172_aux_inter_Null.1 hd _ h1 h2
  rw [pm172_aux_relPi_iff, fld_rsum]
  constructor
  · rintro ⟨⟨hM, hN⟩, R, x, y, ⟨⟨hx, hy⟩, hq⟩, hR⟩
    have hS := pm172_aux_restrict_sel hM
    have hS' := pm172_aux_restrict_sel hN
    have hT := pm172_aux_restrict_sel (Set.union_comm (fld P) (fld Q) ▸ hM)
    have hT' := pm172_aux_restrict_sel (Set.union_comm (fld P) (fld Q) ▸ hN)
    refine ⟨M ↾ fld P, M ↾ fld Q, N ↾ fld P, N ↾ fld Q, ⟨⟨⟨hS, hS'⟩, ⟨hT, hT'⟩⟩, ?_⟩,
      pm172_aux_split hM, pm172_aux_split hN⟩
    rcases pm172_aux_sel_mem hM hx with hRP | hRQ
    · refine Or.inl (pm172_aux_relPi_iff.2 ⟨⟨hS, hS'⟩, R, x, y, ⟨⟨⟨hx, hRP⟩, ⟨hy, hRP⟩⟩, hq⟩,
        fun R' hR' u hu => ⟨hR R' ⟨Or.inl (Or.inl hR'.1), hR'.2⟩ u hu.1, hu.2⟩⟩)
    · refine Or.inr ⟨pm172_aux_sel_ext hS hS' fun u R' hu => ⟨?_, hu.2⟩, pm172_aux_relPi_iff.2
        ⟨⟨hT, hT'⟩, R, x, y, ⟨⟨⟨hx, hRQ⟩, ⟨hy, hRQ⟩⟩, hq⟩,
        fun R' hR' u hu => ⟨hR R' ⟨Or.inl (Or.inr hR'.1), hR'.2⟩ u hu.1, hu.2⟩⟩⟩
      exact hR R' ⟨Or.inr ⟨hu.2, hRQ⟩, fun e => dj (e ▸ hu.2) hRQ⟩ u hu.1
  · rintro ⟨S, T, S', T', ⟨⟨⟨hS, hS'⟩, ⟨hT, hT'⟩⟩, h⟩, rfl, rfl⟩
    have hM := pm172_aux_union_sel hd hS hT
    have hN := pm172_aux_union_sel hd hS' hT'
    refine ⟨⟨hM, hN⟩, ?_⟩
    rcases h with h | ⟨rfl, h⟩
    · obtain ⟨-, R, x, y, ⟨⟨hx, hy⟩, hq⟩, hR⟩ := pm172_aux_relPi_iff.1 h
      have hRP := pm172_aux_sel_mem hS hx
      refine ⟨R, x, y, ⟨⟨Or.inl hx, Or.inl hy⟩, hq⟩, fun R' ⟨hR', hne⟩ u hu => ?_⟩
      rcases hR' with (hR' | hR') | ⟨-, hRQ⟩
      · rcases hu with hu | hu
        · exact Or.inl (hR R' ⟨hR', hne⟩ u hu)
        · exact (dj ⟨R, Or.inl hR'⟩ (pm172_aux_sel_mem hT hu)).elim
      · exact (dj hRP ⟨R', Or.inr hR'⟩).elim
      · exact (dj hRP hRQ).elim
    · obtain ⟨-, R, x, y, ⟨⟨hx, hy⟩, hq⟩, hR⟩ := pm172_aux_relPi_iff.1 h
      have hRQ := pm172_aux_sel_mem hT hx
      refine ⟨R, x, y, ⟨⟨Or.inr hx, Or.inr hy⟩, hq⟩, fun R' ⟨hR', hne⟩ u hu => ?_⟩
      rcases hu with hu | hu
      · exact Or.inl hu
      · rcases hR' with (hR' | hR') | ⟨hR'P, -⟩
        · exact (dj ⟨R', Or.inr hR'⟩ hRQ).elim
        · exact Or.inr (hR R' ⟨hR', hne⟩ u hu)
        · exact (dj hR'P (pm172_aux_sel_mem hT hu)).elim

theorem pm172_aux_sDot_C :
    (sDotRel ⨾ C : (α → (α → α → Prop) → Prop) →
      ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) → Prop) =
      graph (fun U => sumRel (fld U)) := by
  funext M U; apply propext
  constructor
  · rintro ⟨K, h1, h2⟩
    show M = sumRel (fld U)
    rw [show M = sumRel K from h1, show K = fld U from h2]
  · intro h; exact ⟨fld U, h, rfl⟩

theorem pm172_aux_sumRel_fld_couple (T S : α → (α → α → Prop) → Prop) :
    sumRel (fld (T ↓ S)) = S ⊍ T := by
  funext x Q; apply propext
  constructor
  · rintro ⟨Z, hZ, hx⟩
    rcases pm170_aux_mem_fld_couple.1 hZ with rfl | rfl
    · exact Or.inr hx
    · exact Or.inl hx
  · rintro (hx | hx)
    · exact ⟨S, pm170_aux_mem_fld_couple.2 (Or.inr rfl), hx⟩
    · exact ⟨T, pm170_aux_mem_fld_couple.2 (Or.inl rfl), hx⟩

end Helpers172d

/-- ✱172·3. \[\begin{align}&\vdash \colon\ldotp \dot{\exists} !P.Z{\sim}\in CʻP.\supset :M{\Pi ʻ(P\unicode{x21f8} Z)}N.\equiv .\\ &(\exists S,T,u,v).(u\downarrow S)(\Pi ʻP\times Z)(v\downarrow T).M=S\unicode{x228d} u\downarrow Z.N=T\unicode{x228d} v\downarrow Z\end{align}\] -/
theorem pm172_3 {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    {M N : α → (α → α → Prop) → Prop} (h : rEx P ∧ Z ∉ fld P) :
    relPi (P ⇸ Z) M N ↔ ∃ S T u v, ((relPi P ×ᵣ Z) (u ↓ S) (v ↓ T) ∧ M = S ⊍ u ↓ Z) ∧
      N = T ⊍ v ↓ Z := by
  obtain ⟨hP, hZ⟩ := h
  have hZZ : fld (Z ↓ Z) = ι Z := by rw [pm170_aux_fld_couple, Set.union_self]
  have hd : fld P ∩ fld (Z ↓ Z) = Λ := pm172_aux_inter_Null.2 fun R hR hR' => by
    rw [hZZ, pm170_aux_mem_iota] at hR'; rw [hR'] at hR; exact hZ hR
  obtain ⟨R0, hR0⟩ := pm170_aux_rEx_iff_fld.1 hP
  have e : relPi (P ⇸ Z) = relPi (P ⤉ (Z ↓ Z)) := by
    apply pm172_aux_relPi_congr
    constructor
    · rw [fld_rsum, hZZ]
      ext R; constructor
      · rintro ⟨S, (h' | ⟨h', -⟩) | (h' | ⟨-, h'⟩)⟩
        · exact Or.inl ⟨S, Or.inl h'⟩
        · exact Or.inl h'
        · exact Or.inl ⟨S, Or.inr h'⟩
        · exact Or.inr h'
      · rintro (⟨S, h' | h'⟩ | h')
        · exact ⟨S, Or.inl (Or.inl h')⟩
        · exact ⟨S, Or.inr (Or.inl h')⟩
        · rw [pm170_aux_mem_iota.1 h']; exact ⟨R0, Or.inr (Or.inr ⟨hR0, rfl⟩)⟩
    · funext R S; apply propext
      show ((P R S ∨ (R ∈ fld P ∧ S ∈ ι Z)) ∧ R ≠ S) ↔
        (((P R S ∨ (R ∈ ι Z ∧ S ∈ ι Z)) ∨ (R ∈ fld P ∧ S ∈ fld (Z ↓ Z))) ∧ R ≠ S)
      rw [hZZ]
      constructor
      · rintro ⟨h' | h', hne⟩
        · exact ⟨Or.inl (Or.inl h'), hne⟩
        · exact ⟨Or.inr h', hne⟩
      · rintro ⟨(h' | ⟨h1, h2⟩) | h', hne⟩
        · exact ⟨Or.inl h', hne⟩
        · exact absurd ((pm170_aux_mem_iota.1 h1).trans (pm170_aux_mem_iota.1 h2).symm) hne
        · exact ⟨Or.inr h', hne⟩
  rw [e, pm172_aux_33 hd, hZZ]
  constructor
  · rintro ⟨S, T, S', T', ⟨⟨⟨hS, hS'⟩, hT, hT'⟩, h⟩, rfl, rfl⟩
    obtain ⟨u, hu⟩ := pm172_aux_sel_exists hT (rfl : Z ∈ ι Z)
    obtain ⟨v, hv⟩ := pm172_aux_sel_exists hT' (rfl : Z ∈ ι Z)
    have huZ : u ∈ fld Z := pm172_aux_sel_sub hT hu
    have hvZ : v ∈ fld Z := pm172_aux_sel_sub hT' hv
    rw [pm172_aux_sel_eq_couple hT hu, pm172_aux_sel_eq_couple hT' hv] at h ⊢
    refine ⟨S, S', u, v, ⟨?_, rfl⟩, rfl⟩
    rw [pm170_aux_rtimes_couple, pm172_17 hP]
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inr ⟨h, huZ, hvZ⟩
    · rw [pm172_2, opSemi_couple_apply] at h
      obtain ⟨a, b, ⟨e1, e2⟩, hab⟩ := h
      rw [(couple_eq_couple_iff.1 e1).1, (couple_eq_couple_iff.1 e2).1]
      exact Or.inl ⟨hS, rfl, hab⟩
  · rintro ⟨S, T, u, v, ⟨hr, rfl⟩, rfl⟩
    rw [pm170_aux_rtimes_couple, pm172_17 hP] at hr
    rcases hr with ⟨hS, rfl, h⟩ | ⟨h, hu, hv⟩
    · refine ⟨S, u ↓ Z, S, v ↓ Z, ⟨⟨⟨hS, hS⟩, pm172_aux_couple_sel ⟨v, Or.inl h⟩,
        pm172_aux_couple_sel ⟨u, Or.inr h⟩⟩, Or.inr ⟨rfl, ?_⟩⟩, rfl, rfl⟩
      rw [pm172_2, opSemi_couple_apply]; exact ⟨u, v, ⟨rfl, rfl⟩, h⟩
    · obtain ⟨⟨hS, hT⟩, -⟩ := pm172_aux_relPi_iff.1 h
      exact ⟨S, u ↓ Z, T, v ↓ Z, ⟨⟨⟨hS, hT⟩, pm172_aux_couple_sel hu, pm172_aux_couple_sel hv⟩,
        Or.inl h⟩, rfl, rfl⟩

section Helpers172e
variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

/-- Two relations with no pairs are like. -/
theorem pm172_aux_smor_empty {P : α → α → Prop} {Q : β → β → Prop} (hP : ∀ x y, ¬ P x y)
    (hQ : ∀ x y, ¬ Q x y) : smor P Q := by
  refine ⟨fun _ _ => False, ⟨mem_arrow_one_one.2 ⟨fun _ _ _ h => h.1.elim,
    fun _ _ _ h => h.1.elim⟩, ?_⟩, ?_⟩
  · ext y; constructor
    · rintro ⟨z, h | h⟩ <;> exact (hQ _ _ h).elim
    · rintro ⟨x, h⟩; exact h.elim
  · funext x y; apply propext; rw [semi_apply]
    exact ⟨fun h => (hP _ _ h).elim, fun ⟨_, _, ⟨h, _⟩, _⟩ => h.elim⟩

/-- A correlator gives a function from the field of `Q` onto that of `P`. -/
theorem pm172_aux_smor_fun {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q)
    (hne : (fld Q).Nonempty) : ∃ g : β → α, (∀ z w, z ∈ fld Q → w ∈ fld Q → g z = g w → z = w) ∧
      ∀ x y, P x y ↔ ∃ z w, Q z w ∧ x = g z ∧ y = g w := by
  obtain ⟨S, ⟨hS, hcod⟩, rfl⟩ := h
  obtain ⟨s1, s2⟩ := mem_arrow_one_one.1 hS
  obtain ⟨w0, hw0⟩ := hne
  rw [hcod] at hw0
  obtain ⟨x0, -⟩ := hw0
  have : Nonempty α := ⟨x0⟩
  let g : β → α := fun w => Classical.epsilon (fun x => S x w)
  have hg : ∀ w, w ∈ fld Q → S (g w) w := fun w hw => by
    rw [hcod] at hw; exact Classical.epsilon_spec hw
  refine ⟨g, fun z w hz hw e => s2 (g z) z w ⟨hg z hz, e ▸ hg w hw⟩, fun x y => ?_⟩
  rw [semi_apply]
  constructor
  · rintro ⟨z, w, ⟨hxz, hyw⟩, hzw⟩
    exact ⟨z, w, hzw, s1 x (g z) z ⟨hxz, hg z ⟨w, Or.inl hzw⟩⟩,
      s1 y (g w) w ⟨hyw, hg w ⟨z, Or.inr hzw⟩⟩⟩
  · rintro ⟨z, w, hzw, rfl, rfl⟩
    exact ⟨z, w, ⟨hg z ⟨w, Or.inl hzw⟩, hg w ⟨z, Or.inr hzw⟩⟩, hzw⟩

theorem pm172_aux_fld_img {P : α → α → Prop} {Q : β → β → Prop} {g : β → α}
    (hP : ∀ x y, P x y ↔ ∃ z w, Q z w ∧ x = g z ∧ y = g w) {x : α} :
    x ∈ fld P ↔ ∃ z, z ∈ fld Q ∧ x = g z := by
  constructor
  · rintro ⟨y, h | h⟩
    · obtain ⟨z, w, hzw, rfl, -⟩ := (hP _ _).1 h; exact ⟨z, ⟨w, Or.inl hzw⟩, rfl⟩
    · obtain ⟨z, w, hzw, -, rfl⟩ := (hP _ _).1 h; exact ⟨w, ⟨z, Or.inr hzw⟩, rfl⟩
  · rintro ⟨z, ⟨w, h | h⟩, rfl⟩
    · exact ⟨g w, Or.inl ((hP _ _).2 ⟨z, w, h, rfl, rfl⟩)⟩
    · exact ⟨g w, Or.inr ((hP _ _).2 ⟨w, z, h, rfl, rfl⟩)⟩

theorem pm172_aux_mem_fld_rtimes {Q : β → β → Prop} {P : α → α → Prop} {x : α} {z : β} :
    x ↓ z ∈ fld (Q ×ᵣ P) ↔ x ∈ fld P ∧ z ∈ fld Q := by
  constructor
  · intro h
    obtain ⟨x', z', ⟨hx, hz⟩, e⟩ := pm170_aux_fld_rtimes h
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    exact ⟨hx, hz⟩
  · rintro ⟨⟨y, h | h⟩, hz⟩
    · exact ⟨y ↓ z, Or.inl ((pm170_aux_rtimes_couple Q P x y z z).2 (Or.inl ⟨hz, rfl, h⟩))⟩
    · exact ⟨y ↓ z, Or.inr ((pm170_aux_rtimes_couple Q P y x z z).2 (Or.inl ⟨hz, rfl, h⟩))⟩

theorem pm172_aux_rtimes_empty {Q : β → β → Prop} {P : α → α → Prop}
    (h : fld Q = ∅ ∨ fld P = ∅) (U V : α → β → Prop) : ¬ (Q ×ᵣ P) U V := by
  intro hUV
  obtain ⟨x, z, ⟨hx, hz⟩, -⟩ := pm170_aux_fld_rtimes ⟨V, Or.inl hUV⟩
  rcases h with h | h
  · rw [h] at hz; exact hz
  · rw [h] at hx; exact hx

theorem pm172_aux_fld_empty_of_smor {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q)
    (hQ : fld Q = ∅) : fld P = ∅ := by
  obtain ⟨e, -⟩ := smor_iff_exists_equiv.1 h
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  exact Set.eq_empty_iff_forall_notMem.1 hQ _ (e ⟨x, hx⟩).2

/-- Likeness of ordinal products (✱166·23). -/
theorem pm172_aux_smor_rtimes {A : β → β → Prop} {A' : δ → δ → Prop} {B : α → α → Prop}
    {B' : γ → γ → Prop} (hA : smor A A') (hB : smor B B') : smor (A ×ᵣ B) (A' ×ᵣ B') := by
  by_cases hne : (fld A').Nonempty ∧ (fld B').Nonempty
  · obtain ⟨gA, iA, hgA⟩ := pm172_aux_smor_fun hA hne.1
    obtain ⟨gB, iB, hgB⟩ := pm172_aux_smor_fun hB hne.2
    let f : (γ → δ → Prop) → (α → β → Prop) := fun U a b => ∃ x z, U x z ∧ a = gB x ∧ b = gA z
    have hf : ∀ x z, f (x ↓ z) = gB x ↓ gA z := by
      intro x z; funext a b; apply propext
      constructor
      · rintro ⟨x', z', ⟨rfl, rfl⟩, rfl, rfl⟩; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩; exact ⟨x, z, ⟨rfl, rfl⟩, rfl, rfl⟩
    refine ⟨_, pm170_aux_smorbar f ?_ ?_⟩
    · intro U V hU hV e
      obtain ⟨x, z, ⟨hx, hz⟩, rfl⟩ := pm170_aux_fld_rtimes hU
      obtain ⟨y, w, ⟨hy, hw⟩, rfl⟩ := pm170_aux_fld_rtimes hV
      rw [hf, hf, couple_eq_couple_iff] at e
      rw [iB x y hx hy e.1, iA z w hz hw e.2]
    · intro U V
      constructor
      · intro h
        obtain ⟨x, z, ⟨hx, hz⟩, rfl⟩ := pm170_aux_fld_rtimes ⟨V, Or.inl h⟩
        obtain ⟨y, w, ⟨hy, hw⟩, rfl⟩ := pm170_aux_fld_rtimes ⟨_, Or.inr h⟩
        rcases (pm170_aux_rtimes_couple _ _ _ _ _ _).1 h with ⟨-, rfl, hxy⟩ | ⟨hzw, -, -⟩
        · obtain ⟨z', hz', rfl⟩ := (pm172_aux_fld_img hgA).1 hz
          obtain ⟨x', y', hxy', rfl, rfl⟩ := (hgB _ _).1 hxy
          exact ⟨x' ↓ z', y' ↓ z', (pm170_aux_rtimes_couple _ _ _ _ _ _).2
            (Or.inl ⟨hz', rfl, hxy'⟩), (hf _ _).symm, (hf _ _).symm⟩
        · obtain ⟨z', w', hzw', rfl, rfl⟩ := (hgA _ _).1 hzw
          obtain ⟨x', hx', rfl⟩ := (pm172_aux_fld_img hgB).1 hx
          obtain ⟨y', hy', rfl⟩ := (pm172_aux_fld_img hgB).1 hy
          exact ⟨x' ↓ z', y' ↓ w', (pm170_aux_rtimes_couple _ _ _ _ _ _).2
            (Or.inr ⟨hzw', hx', hy'⟩), (hf _ _).symm, (hf _ _).symm⟩
      · rintro ⟨U', V', h, rfl, rfl⟩
        obtain ⟨x, z, -, rfl⟩ := pm170_aux_fld_rtimes ⟨V', Or.inl h⟩
        obtain ⟨y, w, -, rfl⟩ := pm170_aux_fld_rtimes ⟨_, Or.inr h⟩
        rw [hf, hf, pm170_aux_rtimes_couple]
        rcases (pm170_aux_rtimes_couple _ _ _ _ _ _).1 h with ⟨hz, rfl, hxy⟩ | ⟨hzw, hx, hy⟩
        · exact Or.inl ⟨(pm172_aux_fld_img hgA).2 ⟨z, hz, rfl⟩, rfl,
            (hgB _ _).2 ⟨x, y, hxy, rfl, rfl⟩⟩
        · exact Or.inr ⟨(hgA _ _).2 ⟨z, w, hzw, rfl, rfl⟩, (pm172_aux_fld_img hgB).2 ⟨x, hx, rfl⟩,
            (pm172_aux_fld_img hgB).2 ⟨y, hy, rfl⟩⟩
  · have h' : fld A' = ∅ ∨ fld B' = ∅ := by
      rw [not_and_or, Set.not_nonempty_iff_eq_empty, Set.not_nonempty_iff_eq_empty] at hne
      exact hne
    apply pm172_aux_smor_empty
    · apply pm172_aux_rtimes_empty
      rcases h' with h' | h'
      · exact Or.inl (pm172_aux_fld_empty_of_smor hA h')
      · exact Or.inr (pm172_aux_fld_empty_of_smor hB h')
    · exact pm172_aux_rtimes_empty h'

/-- Associativity of ordinal products (✱166·42). -/
theorem pm172_aux_rtimes_assoc (A : γ → γ → Prop) (B : β → β → Prop) (C : α → α → Prop) :
    smor (A ×ᵣ (B ×ᵣ C)) ((A ×ᵣ B) ×ᵣ C) := by
  let f : (α → (β → γ → Prop) → Prop) → ((α → β → Prop) → γ → Prop) :=
    fun U V a => ∃ c b, U c (b ↓ a) ∧ V = c ↓ b
  have hf : ∀ c b a, f (c ↓ (b ↓ a)) = (c ↓ b) ↓ a := by
    intro c b a; funext V a'; apply propext
    show (∃ c' b', (c ↓ (b ↓ a)) c' (b' ↓ a') ∧ V = c' ↓ b') ↔ (V = c ↓ b ∧ a' = a)
    constructor
    · rintro ⟨c', b', ⟨h1, h2⟩, rfl⟩
      have h1' : c' = c := h1
      have h2' : b' ↓ a' = b ↓ a := h2
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 h2'
      subst h1'; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      refine ⟨c, b, ⟨rfl, ?_⟩, h1⟩
      show b ↓ a' = b ↓ a
      rw [h2]
  refine ⟨_, pm170_aux_smorbar f ?_ ?_⟩
  · intro U V hU hV e
    obtain ⟨c, X, ⟨-, hX⟩, rfl⟩ := pm170_aux_fld_rtimes hU
    obtain ⟨b, a, -, rfl⟩ := pm170_aux_fld_rtimes hX
    obtain ⟨c', X', ⟨-, hX'⟩, rfl⟩ := pm170_aux_fld_rtimes hV
    obtain ⟨b', a', -, rfl⟩ := pm170_aux_fld_rtimes hX'
    rw [hf, hf, couple_eq_couple_iff, couple_eq_couple_iff] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    rfl
  · intro U V
    constructor
    · intro h
      obtain ⟨Y, a, ⟨hY, ha⟩, rfl⟩ := pm170_aux_fld_rtimes ⟨V, Or.inl h⟩
      obtain ⟨c, b, -, rfl⟩ := pm170_aux_fld_rtimes hY
      obtain ⟨Y', a', ⟨hY', ha'⟩, rfl⟩ := pm170_aux_fld_rtimes ⟨_, Or.inr h⟩
      obtain ⟨c', b', -, rfl⟩ := pm170_aux_fld_rtimes hY'
      refine ⟨c ↓ (b ↓ a), c' ↓ (b' ↓ a'), ?_, (hf _ _ _).symm, (hf _ _ _).symm⟩
      simp only [pm170_aux_rtimes_couple, pm172_aux_mem_fld_rtimes, couple_eq_couple_iff] at h ⊢
      tauto
    · rintro ⟨U', V', h, rfl, rfl⟩
      obtain ⟨c, X, ⟨-, hX⟩, rfl⟩ := pm170_aux_fld_rtimes ⟨V', Or.inl h⟩
      obtain ⟨b, a, -, rfl⟩ := pm170_aux_fld_rtimes hX
      obtain ⟨c', X', ⟨-, hX'⟩, rfl⟩ := pm170_aux_fld_rtimes ⟨_, Or.inr h⟩
      obtain ⟨b', a', -, rfl⟩ := pm170_aux_fld_rtimes hX'
      rw [hf, hf]
      simp only [pm170_aux_rtimes_couple, pm172_aux_mem_fld_rtimes, couple_eq_couple_iff] at h ⊢
      tauto

end Helpers172e

section Helpers172f
variable {α : Type u}

theorem pm172_aux_addZ_inj {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    (hZ : Z ∉ fld P) {S S' : α → (α → α → Prop) → Prop} (hS : S ∈ sel F (fld P))
    (hS' : S' ∈ sel F (fld P)) {u u' : α} (e : S ⊍ u ↓ Z = S' ⊍ u' ↓ Z) : S = S' ∧ u = u' := by
  have h1 : (S' ⊍ u' ↓ Z) u Z := by rw [← e]; exact Or.inr ⟨rfl, rfl⟩
  have hu : u = u' := by
    rcases h1 with h | ⟨h, -⟩
    · exact absurd (pm172_aux_sel_mem hS' h) hZ
    · exact h
  subst hu
  refine ⟨pm172_aux_sel_ext hS hS' fun x Q hx => ?_, rfl⟩
  have : (S' ⊍ u ↓ Z) x Q := by rw [← e]; exact Or.inl hx
  rcases this with h | ⟨-, hQ⟩
  · exact h
  · exact absurd ((show Q = Z from hQ) ▸ pm172_aux_sel_mem hS hx) hZ

theorem pm172_aux_fld_rNull : fld (rNull : α → α → Prop) = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ ⟨_, h⟩ => by
    rcases h with h | h <;> exact rNull_apply _ _ h

theorem pm172_aux_eq_rNull_of_not_rEx {P : α → α → Prop} (h : ¬ rEx P) : P = rNull := by
  by_contra h'; exact h (pm172_aux_rEx_iff_ne.2 h')

theorem pm172_aux_relPi_couple_smor (Z : α → α → Prop) : smor (relPi (Z ↓ Z)) Z := by
  rw [pm172_2]
  refine ⟨_, pm170_aux_smorbar (fun x => x ↓ Z) (fun z w _ _ e => (couple_eq_couple_iff.1 e).1)
    fun X Y => ?_⟩
  rw [opSemi_couple_apply]
  exact ⟨fun ⟨x, x', ⟨h1, h2⟩, h⟩ => ⟨x, x', h, h1, h2⟩,
    fun ⟨x, x', h, h1, h2⟩ => ⟨x, x', ⟨h1, h2⟩, h⟩⟩

/-- The corrected ✱172·34, stated before ✱172·321, which uses it. -/
theorem pm172_aux_34 {P Q : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) :
    (sDotRel ⨾ C) ↾ fld (relPi P ×ᵣ relPi Q) ∈ smorbar (relPi (P ⤉ Q)) (relPi P ×ᵣ relPi Q) := by
  obtain ⟨⟨hP, hQ⟩, hd⟩ := h
  rw [pm172_aux_sDot_C]
  apply pm170_aux_smorbar
  · intro U V hU hV e
    obtain ⟨T, S, ⟨hT, hS⟩, rfl⟩ := pm170_aux_fld_rtimes hU
    obtain ⟨T', S', ⟨hT', hS'⟩, rfl⟩ := pm170_aux_fld_rtimes hV
    simp only [pm172_aux_sumRel_fld_couple] at e
    have hS1 := pm172_12 P hS
    have hS1' := pm172_12 P hS'
    have hT1 := pm172_12 Q hT
    have hT1' := pm172_12 Q hT'
    obtain ⟨e1, e2⟩ := pm172_aux_union_restrict hd hS1 hT1
    obtain ⟨e1', e2'⟩ := pm172_aux_union_restrict hd hS1' hT1'
    have hSS : S = S' := by rw [← e1, e, e1']
    have hTT : T = T' := by rw [← e2, e, e2']
    rw [hSS, hTT]
  · intro M N
    rw [pm172_aux_33 hd]
    constructor
    · rintro ⟨S, T, S', T', ⟨⟨⟨hS, hS'⟩, hT, hT'⟩, h⟩, rfl, rfl⟩
      refine ⟨T ↓ S, T' ↓ S', ?_, (pm172_aux_sumRel_fld_couple T S).symm,
        (pm172_aux_sumRel_fld_couple T' S').symm⟩
      rw [pm170_aux_rtimes_couple, pm172_17 hP, pm172_17 hQ]
      rcases h with h | ⟨rfl, h⟩
      · exact Or.inr ⟨h, hT, hT'⟩
      · exact Or.inl ⟨hS, rfl, h⟩
    · rintro ⟨U, V, hUV, rfl, rfl⟩
      obtain ⟨T, S, -, rfl⟩ := pm170_aux_fld_rtimes ⟨V, Or.inl hUV⟩
      obtain ⟨T', S', -, rfl⟩ := pm170_aux_fld_rtimes ⟨_, Or.inr hUV⟩
      rw [pm170_aux_rtimes_couple, pm172_17 hP, pm172_17 hQ] at hUV
      simp only [pm172_aux_sumRel_fld_couple]
      rcases hUV with ⟨hS, rfl, h⟩ | ⟨h, hT, hT'⟩
      · obtain ⟨⟨hT, hT'⟩, -⟩ := pm172_aux_relPi_iff.1 h
        exact ⟨S, T, S, T', ⟨⟨⟨hS, hS⟩, hT, hT'⟩, Or.inr ⟨rfl, h⟩⟩, rfl, rfl⟩
      · obtain ⟨⟨hS, hS'⟩, -⟩ := pm172_aux_relPi_iff.1 h
        exact ⟨S, T, S', T', ⟨⟨⟨hS, hS'⟩, hT, hT'⟩, Or.inl h⟩, rfl, rfl⟩

end Helpers172f

/-- ✱172·31. \[\begin{align}&\vdash :\dot{\exists} !P.Z{\sim}\in CʻP.\\ &W=\hat{M} \hat{R} \{(\dot{\exists} S,u).S\in F_{\Delta }ʻCʻP.u\in CʻZ.R=u\downarrow S.M=S\unicode{x228d} u\downarrow Z\}.\supset .\\ &W\in \Pi ʻ(P\unicode{x21f8} Z)\,\overline{\text{smor}}\,(\Pi ʻP x Z)\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `(∃̇S,u)` for `(∃S,u)`. -/
theorem pm172_31 {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    {W : (α → (α → α → Prop) → Prop) → (α → (α → (α → α → Prop) → Prop) → Prop) → Prop}
    (h : (rEx P ∧ Z ∉ fld P) ∧ W = (fun M R => ∃ S u, ((S ∈ sel F (fld P) ∧ u ∈ fld Z) ∧
      R = u ↓ S) ∧ M = S ⊍ u ↓ Z)) :
    W ∈ smorbar (relPi (P ⇸ Z)) (relPi P ×ᵣ Z) := by
  obtain ⟨⟨hP, hZ⟩, rfl⟩ := h
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro M M' R ⟨⟨S, u, ⟨-, rfl⟩, rfl⟩, ⟨S', u', ⟨-, e⟩, rfl⟩⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e
    rfl
  · rintro M R R' ⟨⟨S, u, ⟨⟨hS, -⟩, rfl⟩, rfl⟩, ⟨S', u', ⟨⟨hS', -⟩, rfl⟩, e⟩⟩
    obtain ⟨rfl, rfl⟩ := pm172_aux_addZ_inj hZ hS hS' e
    rfl
  · ext R; constructor
    · intro hR
      obtain ⟨u, S, ⟨hu, hS⟩, rfl⟩ := pm170_aux_fld_rtimes hR
      rw [pm172_17 hP] at hS
      exact ⟨S ⊍ u ↓ Z, S, u, ⟨⟨hS, hu⟩, rfl⟩, rfl⟩
    · rintro ⟨M, S, u, ⟨⟨hS, hu⟩, rfl⟩, -⟩
      rw [pm172_aux_mem_fld_rtimes, pm172_17 hP]; exact ⟨hu, hS⟩
  · funext M N; apply propext
    rw [pm172_3 ⟨hP, hZ⟩, semi_apply]
    constructor
    · rintro ⟨S, T, u, v, ⟨hr, rfl⟩, rfl⟩
      have h1 := pm172_aux_mem_fld_rtimes.1 ⟨_, Or.inl hr⟩
      have h2 := pm172_aux_mem_fld_rtimes.1 ⟨_, Or.inr hr⟩
      rw [pm172_17 hP] at h1 h2
      exact ⟨u ↓ S, v ↓ T, ⟨⟨S, u, ⟨⟨h1.2, h1.1⟩, rfl⟩, rfl⟩, ⟨T, v, ⟨⟨h2.2, h2.1⟩, rfl⟩, rfl⟩⟩, hr⟩
    · rintro ⟨R, R', ⟨⟨S, u, ⟨-, rfl⟩, rfl⟩, ⟨T, v, ⟨-, rfl⟩, rfl⟩⟩, hr⟩
      exact ⟨S, T, u, v, ⟨hr, rfl⟩, rfl⟩

/-- ✱172·32. \(\vdash :Z{\sim}\in CʻP.\supset .\Pi ʻ(P\unicode{x21f8} Z)\,\text{smor}\,\Pi ʻP\times Z\) -/
theorem pm172_32 {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    (h : Z ∉ fld P) : smor (relPi (P ⇸ Z)) (relPi P ×ᵣ Z) := by
  by_cases hP : rEx P
  · exact ⟨_, pm172_31 ⟨⟨hP, h⟩, rfl⟩⟩
  · have hP0 := pm172_aux_eq_rNull_of_not_rEx hP
    subst hP0
    have e : (rNull : (α → α → Prop) → (α → α → Prop) → Prop) ⇸ Z = rNull := by
      funext R S; apply propext; constructor
      · rintro (h' | ⟨h', -⟩)
        · exact absurd h' (rNull_apply _ _)
        · rw [pm172_aux_fld_rNull] at h'; exact h'.elim
      · intro h'; exact absurd h' (rNull_apply _ _)
    apply pm172_aux_smor_empty
    · rw [e, pm172_13]; exact rNull_apply
    · rw [pm172_13]; exact pm172_aux_rtimes_empty (Or.inl pm172_aux_fld_rNull)

/-- ✱172·321. \[\begin{align}&\vdash :Z{\sim}\in CʻP.\supset .\Pi ʻ(Z\unicode{x21f7}CʻP)\,\text{smor}\,Z\times \Pi ʻP\\ &[\text{Proof by similar stages to those in proof of *172·32}]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `Π'(Z ⇷ C'P)`; only `Π'(Z ⇷ P)`
is significant (`Z ⇷` applies to a relation), as the analogue of ✱172·32 shows. -/
theorem pm172_321 {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    (h : Z ∉ fld P) : smor (relPi (Z ⇷ P)) (Z ×ᵣ relPi P) := by
  by_cases hP : rEx P
  · have hZZ : fld (Z ↓ Z) = ι Z := by rw [pm170_aux_fld_couple, Set.union_self]
    have hd : fld (Z ↓ Z) ∩ fld P = Λ := pm172_aux_inter_Null.2 fun R hR hR' => by
      rw [hZZ, pm170_aux_mem_iota] at hR; rw [hR] at hR'; exact h hR'
    have e : relPi (Z ⇷ P) = relPi ((Z ↓ Z) ⤉ P) := by
      apply pm172_aux_relPi_congr
      constructor
      · rw [fld_rsum, hZZ]
        ext R; constructor
        · rintro ⟨S, (⟨h', -⟩ | h') | (⟨-, h'⟩ | h')⟩
          · exact Or.inl h'
          · exact Or.inr ⟨S, Or.inl h'⟩
          · exact Or.inr h'
          · exact Or.inr ⟨S, Or.inr h'⟩
        · rintro (h' | h')
          · obtain ⟨R0, hR0⟩ := pm170_aux_rEx_iff_fld.1 hP
            rw [pm170_aux_mem_iota.1 h']; exact ⟨R0, Or.inl (Or.inl ⟨rfl, hR0⟩)⟩
          · obtain ⟨S, h'' | h''⟩ := h'
            · exact ⟨S, Or.inl (Or.inr h'')⟩
            · exact ⟨S, Or.inr (Or.inr h'')⟩
      · funext R S; apply propext
        show (((R ∈ ι Z ∧ S ∈ fld P) ∨ P R S) ∧ R ≠ S) ↔
          ((((R ∈ ι Z ∧ S ∈ ι Z) ∨ P R S) ∨ (R ∈ fld (Z ↓ Z) ∧ S ∈ fld P)) ∧ R ≠ S)
        rw [hZZ]
        constructor
        · rintro ⟨h' | h', hne⟩
          · exact ⟨Or.inr h', hne⟩
          · exact ⟨Or.inl (Or.inr h'), hne⟩
        · rintro ⟨(⟨h1, h2⟩ | h') | h', hne⟩
          · exact absurd ((pm170_aux_mem_iota.1 h1).trans (pm170_aux_mem_iota.1 h2).symm) hne
          · exact ⟨Or.inr h', hne⟩
          · exact ⟨Or.inl h', hne⟩
    rw [e]
    exact smor_trans ⟨_, pm172_aux_34 ⟨⟨⟨Z, Z, rfl, rfl⟩, hP⟩, hd⟩⟩
      (pm172_aux_smor_rtimes (pm172_aux_relPi_couple_smor Z) (smor_refl _))
  · have hP0 := pm172_aux_eq_rNull_of_not_rEx hP
    subst hP0
    have e : Z ⇷ (rNull : (α → α → Prop) → (α → α → Prop) → Prop) = rNull := by
      funext R S; apply propext; constructor
      · rintro (⟨-, h'⟩ | h')
        · rw [pm172_aux_fld_rNull] at h'; exact h'.elim
        · exact absurd h' (rNull_apply _ _)
      · intro h'; exact absurd h' (rNull_apply _ _)
    apply pm172_aux_smor_empty
    · rw [e, pm172_13]; exact rNull_apply
    · rw [pm172_13]; exact pm172_aux_rtimes_empty (Or.inr pm172_aux_fld_rNull)

/-- ✱172·33. \[\begin{align}&\vdash \colon\colon\dot{\exists} !P.\dot{\exists} !Q.CʻP\cap CʻQ=\Lambda .\supset \colon\ldotp \\ M\{\Pi ʻ(P\unicode{x2909}Q)\}N.&\equiv :(\exists S,T,S',T'):S,S'\in F_{\Delta }ʻCʻP.T,T'\in F_{\Delta }ʻCʻQ:\\ &S(\Pi ʻP)S'.\lor.S=S'.T(\Pi ʻQ)Tʻ:M=S\unicode{x228d} T.M'=S'\unicode{x228d} T'\end{align}\]

**Status.** proved (reading): transcription errors: the e-text prints `M' = S' ∪̇ T'` for `N = S' ∪̇
T'` (the right side must describe `N`) and `T(Π'Q)Tʻ` for `T(Π'Q)T'`. -/
theorem pm172_33 {P Q : (α → α → Prop) → (α → α → Prop) → Prop} {M N : α → (α → α → Prop) → Prop}
    (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) :
    relPi (P ⤉ Q) M N ↔ ∃ S T S' T', (((S ∈ sel F (fld P) ∧ S' ∈ sel F (fld P)) ∧
      (T ∈ sel F (fld Q) ∧ T' ∈ sel F (fld Q))) ∧ (relPi P S S' ∨ (S = S' ∧ relPi Q T T'))) ∧
      (M = S ⊍ T ∧ N = S' ⊍ T') :=
  pm172_aux_33 h.2

/-- ✱172·34. \[\begin{align}\vdash :\dot{\exists} !P.\dot{\exists} !Q.CʻP\cap CʻQ&=\Lambda .\supset .\\ &(\dot{s} \mid C)\in \{\Pi ʻ(P\unicode{x2909}Q)\}\,\overline{\text{smor}}\, \{\Pi ʻP\times \Pi ʻQ\}\end{align}\]

**Status.** proved (corrected): as printed, the correlator is the unrestricted `ṡ | C`, which is not
a correlator of `Π'(P ⤉ Q)` with `Π'P × Π'Q`: its converse domain contains every relation of its
type, e.g. `Λ̇`, which is not in `C'(Π'P × Π'Q)` (`pm172_34_printed_false`). PM's demonstration
(step (2), ✱151·231) proves the statement for `(ṡ | C) ↾ C'(Π'P × Π'Q)`, which is what is stated. -/
theorem pm172_34 {P Q : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) :
    (sDotRel ⨾ C) ↾ fld (relPi P ×ᵣ relPi Q) ∈ smorbar (relPi (P ⤉ Q)) (relPi P ×ᵣ relPi Q) :=
  pm172_aux_34 h

/-- The printed ✱172·34 (with the unrestricted `ṡ | C`) is false. -/
theorem pm172_34_printed_false (P Q : (α → α → Prop) → (α → α → Prop) → Prop) :
    (sDotRel ⨾ C) ∉ smorbar (relPi (P ⤉ Q)) (relPi P ×ᵣ relPi Q) := by
  rintro ⟨⟨-, hc⟩, -⟩
  have h0 : (rNull : (α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) ∈
      codom (sDotRel ⨾ C) := ⟨_, _, rfl, rfl⟩
  rw [← hc] at h0
  obtain ⟨x, z, -, e⟩ := pm170_aux_fld_rtimes h0
  have : (x ↓ z) x z := ⟨rfl, rfl⟩
  rw [← e] at this; exact rNull_apply _ _ this

/-- ✱172·35. \[\begin{align}&\vdash :\dot{\exists} !P.\dot{\exists} !Q.CʻP\cap CʻQ=\Lambda .\supset .\Pi ʻ(P\unicode{x2909}Q)\,\text{smor}\,\Pi ʻP\times \Pi ʻQ\\ &[*172·34]\end{align}\] -/
theorem pm172_35 {P Q : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) : smor (relPi (P ⤉ Q)) (relPi P ×ᵣ relPi Q) :=
  ⟨_, pm172_34 h⟩

/-- ✱172·36. \(\vdash :X\neq Y.X\neq Z.Y\neq Z.\supset .\Pi ʻ{(X\downarrow Y)\unicode{x21f8} Z}\text{smor}X\times Y\times Z\) -/
theorem pm172_36 {X Y Z : α → α → Prop} (h : (X ≠ Y ∧ X ≠ Z) ∧ Y ≠ Z) :
    smor (relPi ((X ↓ Y) ⇸ Z)) (X ×ᵣ Y ×ᵣ Z) := by
  obtain ⟨⟨hXY, hXZ⟩, hYZ⟩ := h
  have hZ : Z ∉ fld (X ↓ Y) := by
    rw [pm170_aux_fld_couple]
    rintro (h' | h')
    · exact hXZ (pm170_aux_mem_iota.1 h').symm
    · exact hYZ (pm170_aux_mem_iota.1 h').symm
  exact smor_trans (pm172_32 hZ) (pm172_aux_smor_rtimes (pm172_23 hXY) (smor_refl Z))

/-- ✱172·361. \[\begin{align}&\vdash :X\neq Y.X\neq Z.Y\neq Z.\supset .\Pi ʻ{X\unicode{x21f7}(Y\downarrow Z)}\,\text{smor}\,X\times Y\times Z\\ &[\text{Proof as in *172·36}]\end{align}\] -/
theorem pm172_361 {X Y Z : α → α → Prop} (h : (X ≠ Y ∧ X ≠ Z) ∧ Y ≠ Z) :
    smor (relPi (X ⇷ (Y ↓ Z))) (X ×ᵣ Y ×ᵣ Z) := by
  obtain ⟨⟨hXY, hXZ⟩, hYZ⟩ := h
  have hX : X ∉ fld (Y ↓ Z) := by
    rw [pm170_aux_fld_couple]
    rintro (h' | h')
    · exact hXY (pm170_aux_mem_iota.1 h')
    · exact hXZ (pm170_aux_mem_iota.1 h')
  exact smor_trans (pm172_321 hX) (smor_trans
    (pm172_aux_smor_rtimes (smor_refl X) (pm172_23 hYZ)) (pm172_aux_rtimes_assoc X Y Z))

/-- ✱172·37. \[\begin{align}\vdash :X\neq Y.X\neq Z.&X\neq W.Y\neq Z.Y\neq W.Z\neq W.\supset .\\ &\Pi ʻ\{(X\downarrow Y)\unicode{x2909}(Z\downarrow W)\}\,\text{smor}\,X\times Y\times Z\times W\end{align}\] -/
theorem pm172_37 {X Y Z W : α → α → Prop}
    (h : ((((X ≠ Y ∧ X ≠ Z) ∧ X ≠ W) ∧ Y ≠ Z) ∧ Y ≠ W) ∧ Z ≠ W) :
    smor (relPi ((X ↓ Y) ⤉ (Z ↓ W))) (X ×ᵣ Y ×ᵣ Z ×ᵣ W) := by
  obtain ⟨⟨⟨⟨⟨hXY, hXZ⟩, hXW⟩, hYZ⟩, hYW⟩, hZW⟩ := h
  have hd : fld (X ↓ Y) ∩ fld (Z ↓ W) = Λ := pm172_aux_inter_Null.2 fun R h1 h2 => by
    rw [pm170_aux_fld_couple] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      rw [pm170_aux_mem_iota] at h1 h2 <;> rw [h1] at h2
    · exact hXZ h2
    · exact hXW h2
    · exact hYZ h2
    · exact hYW h2
  exact smor_trans (pm172_35 ⟨⟨⟨X, Y, rfl, rfl⟩, ⟨Z, W, rfl, rfl⟩⟩, hd⟩)
    (smor_trans (pm172_aux_smor_rtimes (pm172_23 hXY) (pm172_23 hZW))
      (pm172_aux_rtimes_assoc (X ×ᵣ Y) Z W))

section Helpers172g
variable {α : Type u} {β : Type v}

theorem pm172_aux_mem_fld_relSigma {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : α → α → Prop} {x : α} (hQ : Q ∈ fld P) (hx : x ∈ fld Q) : x ∈ fld (relSigma P) := by
  obtain ⟨y, hy | hy⟩ := hx
  · exact ⟨y, Or.inl (Or.inl ⟨Q, hQ, hy⟩)⟩
  · exact ⟨y, Or.inr (Or.inl ⟨Q, hQ, hy⟩)⟩

theorem pm172_aux_fld_relSigma {P : (α → α → Prop) → (α → α → Prop) → Prop} {x : α}
    (hx : x ∈ fld (relSigma P)) : ∃ Q, Q ∈ fld P ∧ x ∈ fld Q := by
  obtain ⟨y, h | h⟩ := hx
  · rcases (relSigma_apply P _ _).1 h with ⟨Q, hQ, hq⟩ | ⟨Q, R, ⟨h1, -⟩, hQR⟩
    · exact ⟨Q, hQ, y, Or.inl hq⟩
    · exact ⟨Q, ⟨R, Or.inl hQR⟩, h1⟩
  · rcases (relSigma_apply P _ _).1 h with ⟨Q, hQ, hq⟩ | ⟨Q, R, ⟨-, h2⟩, hQR⟩
    · exact ⟨Q, hQ, y, Or.inr hq⟩
    · exact ⟨R, ⟨Q, Or.inr hQR⟩, h2⟩

/-- `T ‖ Cnv'T†` relates `T | N | Cnv'T†` to `N`. -/
theorem pm172_aux_dpar_tr (T : α → β → Prop) (M : α → (α → α → Prop) → Prop)
    (N : β → (β → β → Prop) → Prop) :
    (T ∥ (daggerRel T)˘) M N ↔ M = T ⨾ N ⨾ (daggerRel T)˘ := by
  rw [dpar_iff]
  have : T ⨾ (N ⨾ (daggerRel T)˘) = T ⨾ N ⨾ (daggerRel T)˘ := by
    funext x R; apply propext
    constructor
    · rintro ⟨y, h1, S, h2, h3⟩; exact ⟨S, ⟨y, h1, h2⟩, h3⟩
    · rintro ⟨S, ⟨y, h1, h2⟩, h3⟩; exact ⟨y, h1, S, h2, h3⟩
  rw [this]

theorem pm172_aux_tr_apply (T : α → β → Prop) (N : β → (β → β → Prop) → Prop) (x : α)
    (R : α → α → Prop) :
    (T ⨾ N ⨾ (daggerRel T)˘) x R ↔ ∃ y S, (T x y ∧ N y S) ∧ R = daggerOp T S := by
  constructor
  · rintro ⟨S, ⟨y, h1, h2⟩, h3⟩; exact ⟨y, S, ⟨h1, h2⟩, h3⟩
  · rintro ⟨y, S, ⟨h1, h2⟩, h3⟩; exact ⟨S, ⟨y, h1, h2⟩, h3⟩

theorem pm172_aux_dagger_cres {T : α → β → Prop} {K : Set β} {S : β → β → Prop}
    (h : fld S ⊆ K) : daggerOp (T ↾ K) S = daggerOp T S := by
  funext a b; apply propext
  rw [daggerOp_eq_semi, daggerOp_eq_semi, semi_apply, semi_apply]
  constructor
  · rintro ⟨z, w, ⟨h1, h2⟩, h3⟩; exact ⟨z, w, ⟨h1.1, h2.1⟩, h3⟩
  · rintro ⟨z, w, ⟨h1, h2⟩, h3⟩
    exact ⟨z, w, ⟨⟨h1, h ⟨w, Or.inl h3⟩⟩, ⟨h2, h ⟨z, Or.inr h3⟩⟩⟩, h3⟩

variable {T : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
  (h1 : ∀ x y z, T x z ∧ T y z → x = y) (h2 : ∀ x y z, T x y ∧ T x z → y = z)
  (hc : ∀ S, S ∈ fld Q → fld S ⊆ codom T)

include h2 hc in
theorem pm172_aux_dagger_inj {S S' : β → β → Prop} (hS : S ∈ fld Q) (hS' : S' ∈ fld Q)
    (e : daggerOp T S = daggerOp T S') : S = S' := by
  have key : ∀ {S S' : β → β → Prop}, S ∈ fld Q → daggerOp T S = daggerOp T S' →
      ∀ y y', S y y' → S' y y' := by
    intro S S' hS e y y' h
    obtain ⟨a, ha⟩ := hc S hS ⟨y', Or.inl h⟩
    obtain ⟨b, hb⟩ := hc S hS ⟨y, Or.inr h⟩
    have : daggerOp T S a b := (semi_apply _ _ _ _).2 ⟨y, y', ⟨ha, hb⟩, h⟩
    rw [e] at this
    obtain ⟨z, w, ⟨hz, hw⟩, hzw⟩ := (semi_apply _ _ _ _).1 this
    rw [h2 a y z ⟨ha, hz⟩, h2 b y' w ⟨hb, hw⟩]; exact hzw
  funext y y'; apply propext
  exact ⟨key hS e y y', key hS' e.symm y y'⟩

include hc in
theorem pm172_aux_mem_fld_dagger {S : β → β → Prop} (hS : S ∈ fld Q) {x : α} :
    x ∈ fld (daggerOp T S) ↔ ∃ y, T x y ∧ y ∈ fld S := by
  constructor
  · rintro ⟨x', h | h⟩
    · obtain ⟨z, w, ⟨hz, -⟩, hzw⟩ := (semi_apply _ _ _ _).1 h
      exact ⟨z, hz, w, Or.inl hzw⟩
    · obtain ⟨z, w, ⟨-, hw⟩, hzw⟩ := (semi_apply _ _ _ _).1 h
      exact ⟨w, hw, z, Or.inr hzw⟩
  · rintro ⟨y, hxy, w, hw | hw⟩
    · obtain ⟨b, hb⟩ := hc S hS ⟨y, Or.inr hw⟩
      exact ⟨b, Or.inl ((semi_apply _ _ _ _).2 ⟨y, w, ⟨hxy, hb⟩, hw⟩)⟩
    · obtain ⟨b, hb⟩ := hc S hS ⟨y, Or.inl hw⟩
      exact ⟨b, Or.inr ((semi_apply _ _ _ _).2 ⟨w, y, ⟨hb, hxy⟩, hw⟩)⟩

omit h1 h2 hc in
theorem pm172_aux_P_apply {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : P = daggerRel T ⁏ Q)
    (R R' : α → α → Prop) :
    P R R' ↔ ∃ S S', (R = daggerOp T S ∧ R' = daggerOp T S') ∧ Q S S' := by
  rw [hP]; exact semi_graph_apply _ _ _ _

omit h1 h2 hc in
theorem pm172_aux_fld_P {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : P = daggerRel T ⁏ Q)
    (R : α → α → Prop) : R ∈ fld P ↔ ∃ S, S ∈ fld Q ∧ R = daggerOp T S := by
  rw [hP, show (daggerRel T : (α → α → Prop) → (β → β → Prop) → Prop) = graph (daggerOp T)
    from rfl, fld_semi_graph]; exact Iff.rfl

include h1 h2 hc in
theorem pm172_aux_tr_sel {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : P = daggerRel T ⁏ Q)
    {N : β → (β → β → Prop) → Prop} (hN : N ∈ sel F (fld Q)) :
    T ⨾ N ⨾ (daggerRel T)˘ ∈ sel F (fld P) := by
  refine pm172_aux_mk_sel ?_ ?_ ?_
  · intro x x' R hx hx'
    obtain ⟨y, S, ⟨hxy, hyS⟩, rfl⟩ := (pm172_aux_tr_apply _ _ _ _).1 hx
    obtain ⟨y', S', ⟨hxy', hyS'⟩, e⟩ := (pm172_aux_tr_apply _ _ _ _).1 hx'
    have := pm172_aux_dagger_inj h2 hc (pm172_aux_sel_mem hN hyS) (pm172_aux_sel_mem hN hyS') e
    subst this
    rw [pm172_aux_sel_unique hN hyS hyS'] at hxy
    exact h1 x x' y' ⟨hxy, hxy'⟩
  · intro x R hx
    obtain ⟨y, S, ⟨hxy, hyS⟩, rfl⟩ := (pm172_aux_tr_apply _ _ _ _).1 hx
    exact (pm172_aux_mem_fld_dagger hc (pm172_aux_sel_mem hN hyS)).2
      ⟨y, hxy, pm172_aux_sel_sub hN hyS⟩
  · ext R; rw [pm172_aux_fld_P hP]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨y, S, ⟨-, hyS⟩, rfl⟩ := (pm172_aux_tr_apply _ _ _ _).1 hx
      exact ⟨S, pm172_aux_sel_mem hN hyS, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      obtain ⟨y, hy⟩ := pm172_aux_sel_exists hN hS
      obtain ⟨x, hx⟩ := hc S hS (pm172_aux_sel_sub hN hy)
      exact ⟨x, (pm172_aux_tr_apply _ _ _ _).2 ⟨y, S, ⟨hx, hy⟩, rfl⟩⟩

include h2 hc in
theorem pm172_aux_tr_at {N : β → (β → β → Prop) → Prop} (hN : N ∈ sel F (fld Q))
    {S : β → β → Prop} (hS : S ∈ fld Q) (x : α) :
    (T ⨾ N ⨾ (daggerRel T)˘) x (daggerOp T S) ↔ ∃ y, T x y ∧ N y S := by
  rw [pm172_aux_tr_apply]
  constructor
  · rintro ⟨y, S', ⟨hxy, hyS'⟩, e⟩
    rw [pm172_aux_dagger_inj h2 hc hS (pm172_aux_sel_mem hN hyS') e]; exact ⟨y, hxy, hyS'⟩
  · rintro ⟨y, hxy, hyS⟩; exact ⟨y, S, ⟨hxy, hyS⟩, rfl⟩

include h2 hc in
theorem pm172_aux_tr_inj {N N' : β → (β → β → Prop) → Prop} (hN : N ∈ sel F (fld Q))
    (hN' : N' ∈ sel F (fld Q)) (e : T ⨾ N ⨾ (daggerRel T)˘ = T ⨾ N' ⨾ (daggerRel T)˘) :
    N = N' := by
  refine pm172_aux_sel_ext hN hN' fun y S hy => ?_
  have hS := pm172_aux_sel_mem hN hy
  obtain ⟨x, hx⟩ := hc S hS (pm172_aux_sel_sub hN hy)
  have h := (pm172_aux_tr_at h2 hc hN hS x).2 ⟨y, hx, hy⟩
  rw [e, pm172_aux_tr_at h2 hc hN' hS] at h
  obtain ⟨y', hxy', hy'⟩ := h
  rw [h2 x y y' ⟨hx, hxy'⟩]; exact hy'

include h1 h2 hc in
theorem pm172_aux_tr_surj {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : P = daggerRel T ⁏ Q)
    {M : α → (α → α → Prop) → Prop} (hM : M ∈ sel F (fld P)) :
    ∃ N, N ∈ sel F (fld Q) ∧ M = T ⨾ N ⨾ (daggerRel T)˘ := by
  refine ⟨fun y S => S ∈ fld Q ∧ ∃ x, T x y ∧ M x (daggerOp T S), ?_, ?_⟩
  · refine pm172_aux_mk_sel ?_ ?_ ?_
    · rintro y y' S ⟨-, x, hxy, hx⟩ ⟨-, x', hxy', hx'⟩
      rw [pm172_aux_sel_unique hM hx hx'] at hxy
      exact h2 x' y y' ⟨hxy, hxy'⟩
    · rintro y S ⟨hS, x, hxy, hx⟩
      obtain ⟨y0, hxy0, hy0⟩ := (pm172_aux_mem_fld_dagger hc hS).1 (pm172_aux_sel_sub hM hx)
      rw [h2 x y y0 ⟨hxy, hxy0⟩]; exact hy0
    · ext S; constructor
      · rintro ⟨y, hS, -⟩; exact hS
      · intro hS
        have hR : daggerOp T S ∈ fld P := (pm172_aux_fld_P hP _).2 ⟨S, hS, rfl⟩
        obtain ⟨x, hx⟩ := pm172_aux_sel_exists hM hR
        obtain ⟨y, hxy, -⟩ := (pm172_aux_mem_fld_dagger hc hS).1 (pm172_aux_sel_sub hM hx)
        exact ⟨y, hS, x, hxy, hx⟩
  · funext x R; apply propext
    rw [pm172_aux_tr_apply]
    constructor
    · intro hx
      obtain ⟨S, hS, rfl⟩ := (pm172_aux_fld_P hP R).1 (pm172_aux_sel_mem hM hx)
      obtain ⟨y, hxy, -⟩ := (pm172_aux_mem_fld_dagger hc hS).1 (pm172_aux_sel_sub hM hx)
      exact ⟨y, S, ⟨hxy, hS, x, hxy, hx⟩, rfl⟩
    · rintro ⟨y, S, ⟨hxy, -, x', hxy', hx'⟩, rfl⟩
      rw [h1 x x' y ⟨hxy, hxy'⟩]; exact hx'

include h1 h2 hc in
theorem pm172_aux_tr_relPi {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : P = daggerRel T ⁏ Q)
    {N N' : β → (β → β → Prop) → Prop} (hN : N ∈ sel F (fld Q)) (hN' : N' ∈ sel F (fld Q)) :
    relPi P (T ⨾ N ⨾ (daggerRel T)˘) (T ⨾ N' ⨾ (daggerRel T)˘) ↔ relPi Q N N' := by
  have hM := pm172_aux_tr_sel h1 h2 hc hP hN
  have hM' := pm172_aux_tr_sel h1 h2 hc hP hN'
  rw [pm172_aux_relPi_iff, pm172_aux_relPi_iff]
  constructor
  · rintro ⟨-, R, x, x', ⟨⟨hx, hx'⟩, hR⟩, hall⟩
    obtain ⟨y, S, ⟨hxy, hyS⟩, rfl⟩ := (pm172_aux_tr_apply _ _ _ _).1 hx
    have hS := pm172_aux_sel_mem hN hyS
    obtain ⟨y', hxy', hy'⟩ := (pm172_aux_tr_at h2 hc hN' hS x').1 hx'
    obtain ⟨z, w, ⟨hz, hw⟩, hzw⟩ := (semi_apply _ _ _ _).1 hR
    rw [h2 x z y ⟨hz, hxy⟩, h2 x' w y' ⟨hw, hxy'⟩] at hzw
    refine ⟨⟨hN, hN'⟩, S, y, y', ⟨⟨hyS, hy'⟩, hzw⟩, fun S0 ⟨hS0, hne⟩ v hv => ?_⟩
    have hS0f : S0 ∈ fld Q := ⟨S, Or.inl hS0⟩
    obtain ⟨u, hu⟩ := hc S0 hS0f (pm172_aux_sel_sub hN hv)
    have hP0 : P (daggerOp T S0) (daggerOp T S) :=
      (pm172_aux_P_apply hP _ _).2 ⟨S0, S, ⟨rfl, rfl⟩, hS0⟩
    have hne' : daggerOp T S0 ≠ daggerOp T S := fun e => hne (pm172_aux_dagger_inj h2 hc hS0f hS e)
    have := hall _ ⟨hP0, hne'⟩ u ((pm172_aux_tr_at h2 hc hN hS0f u).2 ⟨v, hu, hv⟩)
    obtain ⟨v', huv', hv'⟩ := (pm172_aux_tr_at h2 hc hN' hS0f u).1 this
    rw [h2 u v v' ⟨hu, huv'⟩]; exact hv'
  · rintro ⟨-, S, y, y', ⟨⟨hyS, hy'⟩, hyy⟩, hall⟩
    have hS := pm172_aux_sel_mem hN hyS
    obtain ⟨x, hx⟩ := hc S hS ⟨y', Or.inl hyy⟩
    obtain ⟨x', hx'⟩ := hc S hS ⟨y, Or.inr hyy⟩
    refine ⟨⟨hM, hM'⟩, daggerOp T S, x, x', ⟨⟨(pm172_aux_tr_at h2 hc hN hS x).2 ⟨y, hx, hyS⟩,
      (pm172_aux_tr_at h2 hc hN' hS x').2 ⟨y', hx', hy'⟩⟩,
      (semi_apply _ _ _ _).2 ⟨y, y', ⟨hx, hx'⟩, hyy⟩⟩, fun R0 ⟨hR0, hne⟩ u hu => ?_⟩
    obtain ⟨S0, S1, ⟨rfl, e⟩, hS01⟩ := (pm172_aux_P_apply hP _ _).1 hR0
    have hS0f : S0 ∈ fld Q := ⟨S1, Or.inl hS01⟩
    have hS1 : S1 = S := pm172_aux_dagger_inj h2 hc ⟨S0, Or.inr hS01⟩ hS e.symm
    subst hS1
    obtain ⟨v, huv, hv⟩ := (pm172_aux_tr_at h2 hc hN hS0f u).1 hu
    exact (pm172_aux_tr_at h2 hc hN' hS0f u).2
      ⟨v, huv, hall S0 ⟨hS01, fun e' => hne (by rw [e'])⟩ v hv⟩

end Helpers172g

section Helpers172h
variable {α : Type u} {β : Type v}

theorem pm172_aux_ss {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop} (h : T ∈ smorsmorbar P Q) :
    ((∀ x y z, T x z ∧ T y z → x = y) ∧ (∀ x y z, T x y ∧ T x z → y = z)) ∧
      (∀ S, S ∈ fld Q → fld S ⊆ codom T) ∧ P = daggerRel T ⁏ Q := by
  obtain ⟨⟨hT, hcod⟩, hP⟩ := h
  refine ⟨mem_arrow_one_one.1 hT, fun S hS y hy => ?_, hP⟩
  have : y ∈ fld (relSigma Q) := pm172_aux_mem_fld_relSigma hS hy
  rw [show fld (relSigma Q) = codom T from hcod] at this; exact this

theorem pm172_aux_dagger_cnv {T : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    (h2 : ∀ x y z, T x y ∧ T x z → y = z) (hc : ∀ S, S ∈ fld Q → fld S ⊆ codom T)
    {S : β → β → Prop} (hS : S ∈ fld Q) : daggerOp T˘ (daggerOp T S) = S := by
  funext y y'; apply propext
  rw [daggerOp_eq_semi, semi_apply]
  constructor
  · rintro ⟨x, x', ⟨hx, hx'⟩, h⟩
    obtain ⟨z, w, ⟨hz, hw⟩, hzw⟩ := (semi_apply _ _ _ _).1 h
    rw [h2 x y z ⟨hx, hz⟩, h2 x' y' w ⟨hx', hw⟩]; exact hzw
  · intro h
    obtain ⟨x, hx⟩ := hc S hS ⟨y', Or.inl h⟩
    obtain ⟨x', hx'⟩ := hc S hS ⟨y, Or.inr h⟩
    exact ⟨x, x', ⟨hx, hx'⟩, (semi_apply _ _ _ _).2 ⟨y, y', ⟨hx, hx'⟩, h⟩⟩

theorem pm172_aux_tr_back {T : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    (h2 : ∀ x y z, T x y ∧ T x z → y = z) (hc : ∀ S, S ∈ fld Q → fld S ⊆ codom T)
    {N : β → (β → β → Prop) → Prop} (hN : N ∈ sel F (fld Q)) :
    T˘ ⨾ (T ⨾ N ⨾ (daggerRel T)˘) ⨾ (daggerRel T˘)˘ = N := by
  funext y S'; apply propext
  rw [pm172_aux_tr_apply]
  constructor
  · rintro ⟨x, R, ⟨hxy, hx⟩, rfl⟩
    obtain ⟨y0, S, ⟨hxy0, hy0⟩, rfl⟩ := (pm172_aux_tr_apply _ _ _ _).1 hx
    have hS := pm172_aux_sel_mem hN hy0
    rw [pm172_aux_dagger_cnv h2 hc hS, show y = y0 from h2 x y y0 ⟨hxy, hxy0⟩]; exact hy0
  · intro h
    have hS := pm172_aux_sel_mem hN h
    obtain ⟨x, hx⟩ := hc S' hS (pm172_aux_sel_sub hN h)
    exact ⟨x, daggerOp T S', ⟨hx, (pm172_aux_tr_apply _ _ _ _).2 ⟨y, S', ⟨hx, h⟩, rfl⟩⟩,
      (pm172_aux_dagger_cnv h2 hc hS).symm⟩

theorem pm172_aux_tr_cres {T : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    {N : β → (β → β → Prop) → Prop} (hN : N ∈ sel F (fld Q)) :
    (T ↾ fld (relSigma Q)) ⨾ N ⨾ (daggerRel (T ↾ fld (relSigma Q)))˘ = T ⨾ N ⨾ (daggerRel T)˘ := by
  funext x R; apply propext
  rw [pm172_aux_tr_apply, pm172_aux_tr_apply]
  have hsub : ∀ y S, N y S → fld S ⊆ fld (relSigma Q) := fun y S h z hz =>
    pm172_aux_mem_fld_relSigma (pm172_aux_sel_mem hN h) hz
  constructor
  · rintro ⟨y, S, ⟨⟨hxy, -⟩, hyS⟩, rfl⟩
    exact ⟨y, S, ⟨hxy, hyS⟩, pm172_aux_dagger_cres (hsub y S hyS)⟩
  · rintro ⟨y, S, ⟨hxy, hyS⟩, rfl⟩
    exact ⟨y, S, ⟨⟨hxy, hsub y S hyS (pm172_aux_sel_sub hN hyS)⟩, hyS⟩,
      (pm172_aux_dagger_cres (hsub y S hyS)).symm⟩

/-- PM's ✱164·44: a correlator of `P` with `Q` whose pairs are like gives a double correlator. -/
theorem pm172_aux_164_44 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} (hP : P ∈ Rel2excl) (hQ : Q ∈ Rel2excl)
    {S : (α → α → Prop) → (β → β → Prop) → Prop} (hS : S ∈ smorbar P Q) (hSs : S ⪽ smor) :
    smorsmor P Q := by
  obtain ⟨⟨hS1, hScod⟩, hPS⟩ := hS
  obtain ⟨s1, s2⟩ := mem_arrow_one_one.1 hS1
  subst hPS
  let U : (α → α → Prop) → (β → β → Prop) → (α → β → Prop) := fun R R' =>
    Classical.epsilon (fun V => V ∈ smorbar R R')
  have hU : ∀ R R', S R R' → U R R' ∈ smorbar R R' := fun R R' h =>
    Classical.epsilon_spec (p := fun V => V ∈ smorbar R R') (hSs R R' h)
  let T : α → β → Prop := fun x y => ∃ R R', S R R' ∧ U R R' x y
  have hRP : ∀ R R', S R R' → R ∈ fld (S ⁏ Q) := fun R R' h => by
    rw [pm170_aux_fld_semi hScod]; exact ⟨R', h⟩
  have hR'Q : ∀ R R', S R R' → R' ∈ fld Q := fun R R' h => by rw [hScod]; exact ⟨R, h⟩
  have hUcod : ∀ R R' x y, S R R' → U R R' x y → y ∈ fld R' := fun R R' x y h hu => by
    rw [(hU R R' h).1.2]; exact ⟨x, hu⟩
  have hUdom : ∀ R R' x y, S R R' → U R R' x y → x ∈ fld R := fun R R' x y h hu => by
    rw [(hU R R' h).2, pm170_aux_fld_semi (hU R R' h).1.2]; exact ⟨y, hu⟩
  have disjQ : ∀ R1 R2 y, R1 ∈ fld Q → R2 ∈ fld Q → y ∈ fld R1 → y ∈ fld R2 → R1 = R2 := by
    intro R1 R2 y h1 h2 hy1 hy2
    by_contra hne
    exact pm172_aux_inter_Null.1 (hQ R1 R2 ⟨⟨h1, h2⟩, hne⟩) y hy1 hy2
  have disjP : ∀ R1 R2 x, R1 ∈ fld (S ⁏ Q) → R2 ∈ fld (S ⁏ Q) → x ∈ fld R1 → x ∈ fld R2 →
      R1 = R2 := by
    intro R1 R2 x h1 h2 hx1 hx2
    by_contra hne
    exact pm172_aux_inter_Null.1 (hP R1 R2 ⟨⟨h1, h2⟩, hne⟩) x hx1 hx2
  have key : ∀ R R', S R R' → daggerOp T R' = R := by
    intro R R' h
    have hT : ∀ x z, z ∈ fld R' → (T x z ↔ U R R' x z) := by
      intro x z hz
      constructor
      · rintro ⟨R1, R1', h1, hu⟩
        have e1 : R1' = R' :=
          disjQ R1' R' z (hR'Q R1 R1' h1) (hR'Q R R' h) (hUcod R1 R1' x z h1 hu) hz
        subst e1
        rw [s1 R1 R R1' ⟨h1, h⟩] at hu; exact hu
      · intro hu; exact ⟨R, R', h, hu⟩
    have hR := (hU R R' h).2
    rw [hR]
    funext a b; apply propext
    rw [daggerOp_eq_semi, semi_apply, semi_apply]
    constructor
    · rintro ⟨z, w, ⟨hz, hw⟩, hzw⟩
      exact ⟨z, w, ⟨(hT a z ⟨w, Or.inl hzw⟩).1 hz, (hT b w ⟨z, Or.inr hzw⟩).1 hw⟩, hzw⟩
    · rintro ⟨z, w, ⟨hz, hw⟩, hzw⟩
      exact ⟨z, w, ⟨(hT a z ⟨w, Or.inl hzw⟩).2 hz, (hT b w ⟨z, Or.inr hzw⟩).2 hw⟩, hzw⟩
  refine ⟨T, ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x x' y ⟨⟨R1, R1', h1, hu1⟩, ⟨R2, R2', h2, hu2⟩⟩
    have e' : R1' = R2' := disjQ R1' R2' y (hR'Q _ _ h1) (hR'Q _ _ h2) (hUcod _ _ _ _ h1 hu1)
      (hUcod _ _ _ _ h2 hu2)
    subst e'
    have e : R1 = R2 := s1 R1 R2 R1' ⟨h1, h2⟩
    subst e
    exact (mem_arrow_one_one.1 (hU R1 R1' h1).1.1).1 x x' y ⟨hu1, hu2⟩
  · rintro x y y' ⟨⟨R1, R1', h1, hu1⟩, ⟨R2, R2', h2, hu2⟩⟩
    have e : R1 = R2 := disjP R1 R2 x (hRP _ _ h1) (hRP _ _ h2) (hUdom _ _ _ _ h1 hu1)
      (hUdom _ _ _ _ h2 hu2)
    subst e
    have e' : R1' = R2' := s2 R1 R1' R2' ⟨h1, h2⟩
    subst e'
    exact (mem_arrow_one_one.1 (hU R1 R1' h1).1.1).2 x y y' ⟨hu1, hu2⟩
  · show fld (relSigma Q) = codom T
    ext y; constructor
    · intro hy
      obtain ⟨R', hR', hyR'⟩ := pm172_aux_fld_relSigma hy
      rw [hScod] at hR'
      obtain ⟨R, hRR'⟩ := hR'
      have : y ∈ codom (U R R') := by rw [← (hU R R' hRR').1.2]; exact hyR'
      obtain ⟨x, hx⟩ := this
      exact ⟨x, R, R', hRR', hx⟩
    · rintro ⟨x, R, R', h, hu⟩
      exact pm172_aux_mem_fld_relSigma (hR'Q R R' h) (hUcod R R' x y h hu)
  · show S ⁏ Q = daggerRel T ⁏ Q
    funext R1 R2; apply propext
    rw [show (daggerRel T : (α → α → Prop) → (β → β → Prop) → Prop) = graph (daggerOp T) from rfl,
      semi_apply, semi_graph_apply]
    constructor
    · rintro ⟨R1', R2', ⟨h1, h2⟩, hq⟩
      exact ⟨R1', R2', ⟨(key _ _ h1).symm, (key _ _ h2).symm⟩, hq⟩
    · rintro ⟨R1', R2', ⟨rfl, rfl⟩, hq⟩
      have h1 : R1' ∈ codom S := by rw [← hScod]; exact ⟨R2', Or.inl hq⟩
      have h2 : R2' ∈ codom S := by rw [← hScod]; exact ⟨R1', Or.inr hq⟩
      obtain ⟨A, hA⟩ := h1
      obtain ⟨B, hB⟩ := h2
      exact ⟨R1', R2', ⟨by rw [key _ _ hA]; exact hA, by rw [key _ _ hB]; exact hB⟩, hq⟩

end Helpers172h

/-- ✱172·4. \(\vdash :T\in P\,\overline{\text{smor smor}}\, Q.\supset .\{T\parallel \text{Cnv}ʻT\dagger \}\upharpoonright Cʻ\Pi ʻQ\in 1\rightarrow 1\) -/
theorem pm172_4 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop} (h : T ∈ smorsmorbar P Q) :
    (T ∥ (daggerRel T)˘) ↾ fld (relPi Q) ∈ arrow one one := by
  obtain ⟨⟨-, h2⟩, hc, -⟩ := pm172_aux_ss h
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro M M' N ⟨⟨hM, -⟩, ⟨hM', -⟩⟩
    rw [pm172_aux_dpar_tr] at hM hM'; rw [hM, hM']
  · rintro M N N' ⟨⟨hM, hN⟩, ⟨hM', hN'⟩⟩
    rw [pm172_aux_dpar_tr] at hM hM'
    exact pm172_aux_tr_inj h2 hc (pm172_12 Q hN) (pm172_12 Q hN') (hM.symm.trans hM')

/-- ✱172·401. \[\begin{align}\vdash :T\in P\,\overline{\text{smor smor}}\, Q.N\in F_{\Delta }ʻCʻQ.&S\in CʻQ.\supset .\\ &\{(T\parallel \text{Cnv}ʻT\dagger )ʻN\}ʻT^{;}S=TʻNʻS\end{align}\]

Of the two descriptions the first has the larger scope. -/
theorem pm172_401 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop}
    {N : β → (β → β → Prop) → Prop} {S : β → β → Prop}
    (h : (T ∈ smorsmorbar P Q ∧ N ∈ sel F (fld Q)) ∧ S ∈ fld Q) :
    Desc (T ∥ (daggerRel T)˘) N (fun M => Desc M (T ⁏ S) (fun x =>
      Desc2 T N S (fun y => x = y))) := by
  obtain ⟨⟨hT, hN⟩, hS⟩ := h
  obtain ⟨⟨h1, h2⟩, hc, -⟩ := pm172_aux_ss hT
  refine (TheIs_iff_of_unique (fun M => pm172_aux_dpar_tr T M N)).2 ?_
  obtain ⟨y, hy⟩ := pm172_aux_sel_exists hN hS
  obtain ⟨x, hx⟩ := hc S hS (pm172_aux_sel_sub hN hy)
  refine (TheIs_iff_of_unique (b := x) fun x' => ?_).2 ?_
  · show (T ⨾ N ⨾ (daggerRel T)˘) x' (daggerOp T S) ↔ x' = x
    rw [pm172_aux_tr_at h2 hc hN hS]
    constructor
    · rintro ⟨y', hxy', hy'⟩
      rw [pm172_aux_sel_unique hN hy' hy] at hxy'
      exact h1 x' x y ⟨hxy', hx⟩
    · rintro rfl; exact ⟨y, hx, hy⟩
  · refine (TheIs_iff_of_unique (b := x) fun x' => ?_).2 rfl
    rw [pm172_aux_desc_sel hN hy]
    exact ⟨fun hx' => h1 x' x y ⟨hx', hx⟩, fun e => e ▸ hx⟩

/-- ✱172·402. \[\begin{align}\vdash :T\in P\,\overline{\text{smor smor}}\, Q.&N,N'\in F_{\Delta }ʻCʻQ.S\in CʻQ.M=(T\parallel \text{Cnv}ʻT\dagger )ʻN.\\ &Mʻ=(T\parallel \text{Cnv}ʻT\dagger )ʻN'.R=T^{;}S.\supset :\\ &NʻS=N'ʻS.\equiv .MʻR=M'ʻR:(NʻS)S(N'ʻS).\equiv .(MʻR)R(M'ʻR)\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `Mʻ` for `M'`. -/
theorem pm172_402 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop}
    {N N' : β → (β → β → Prop) → Prop} {M M' : α → (α → α → Prop) → Prop}
    {S : β → β → Prop} {R : α → α → Prop}
    (h : ((((T ∈ smorsmorbar P Q ∧ (N ∈ sel F (fld Q) ∧ N' ∈ sel F (fld Q))) ∧ S ∈ fld Q) ∧
      Desc (T ∥ (daggerRel T)˘) N (fun X => M = X)) ∧
      Desc (T ∥ (daggerRel T)˘) N' (fun X => M' = X)) ∧ R = T ⁏ S) :
    (Desc N S (fun a => Desc N' S (fun b => a = b)) ↔
      Desc M R (fun a => Desc M' R (fun b => a = b))) ∧
    (Desc N S (fun a => Desc N' S (fun b => S a b)) ↔
      Desc M R (fun a => Desc M' R (fun b => R a b))) := by
  obtain ⟨⟨⟨⟨⟨hT, hN, hN'⟩, hS⟩, hM⟩, hM'⟩, rfl⟩ := h
  obtain ⟨⟨h1, h2⟩, hc, hP⟩ := pm172_aux_ss hT
  replace hM := (TheIs_iff_of_unique (fun X => pm172_aux_dpar_tr T X N)).1 hM
  replace hM' := (TheIs_iff_of_unique (fun X => pm172_aux_dpar_tr T X N')).1 hM'
  subst hM hM'
  have hMs := pm172_aux_tr_sel h1 h2 hc hP hN
  have hMs' := pm172_aux_tr_sel h1 h2 hc hP hN'
  obtain ⟨y, hy⟩ := pm172_aux_sel_exists hN hS
  obtain ⟨y', hy'⟩ := pm172_aux_sel_exists hN' hS
  obtain ⟨x, hx⟩ := hc S hS (pm172_aux_sel_sub hN hy)
  obtain ⟨x', hx'⟩ := hc S hS (pm172_aux_sel_sub hN' hy')
  have hMx : (T ⨾ N ⨾ (daggerRel T)˘) x (T ⁏ S) := (pm172_aux_tr_at h2 hc hN hS x).2 ⟨y, hx, hy⟩
  have hMx' : (T ⨾ N' ⨾ (daggerRel T)˘) x' (T ⁏ S) :=
    (pm172_aux_tr_at h2 hc hN' hS x').2 ⟨y', hx', hy'⟩
  simp only [pm172_aux_desc_sel hN hy, pm172_aux_desc_sel hN' hy', pm172_aux_desc_sel hMs hMx,
    pm172_aux_desc_sel hMs' hMx']
  constructor
  · constructor
    · rintro rfl; exact h1 x x' y ⟨hx, hx'⟩
    · rintro rfl; exact h2 x y y' ⟨hx, hx'⟩
  · rw [semi_apply]
    constructor
    · intro h; exact ⟨y, y', ⟨hx, hx'⟩, h⟩
    · rintro ⟨z, w, ⟨hz, hw⟩, h⟩
      rw [h2 x y z ⟨hx, hz⟩, h2 x' y' w ⟨hx', hw⟩]; exact h

/-- ✱172·403. \(\vdash :T\in P\,\overline{\text{smor smor}}\, Q.\supset .(T\parallel \text{Cnv}ʻT\dagger )ʻʻF_{\Delta }ʻCʻQ\subset F_{\Delta }ʻCʻP\) -/
theorem pm172_403 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop} (h : T ∈ smorsmorbar P Q) :
    (T ∥ (daggerRel T)˘) ʻʻ sel F (fld Q) ⊆ sel F (fld P) := by
  obtain ⟨⟨h1, h2⟩, hc, hP⟩ := pm172_aux_ss h
  rintro M ⟨N, hN, hMN⟩
  rw [pm172_aux_dpar_tr] at hMN; rw [hMN]
  exact pm172_aux_tr_sel h1 h2 hc hP hN

/-- ✱172·404. \[\begin{align}\vdash \colon\ldotp T\in P\,\overline{\text{smor smor}}\, Q.\supset :&N\in F_{\Delta }ʻCʻQ.M=T\mid N\mid \text{Cnv}ʻT\dagger .\equiv .\\ &M\in F_{\Delta }ʻCʻP.N=\breve{T} \mid M\mid \text{Cnv}ʻ\breve{T} \dagger\end{align}\] -/
theorem pm172_404 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop}
    {N : β → (β → β → Prop) → Prop} {M : α → (α → α → Prop) → Prop} (h : T ∈ smorsmorbar P Q) :
    (N ∈ sel F (fld Q) ∧ M = T ⨾ N ⨾ (daggerRel T)˘ ↔
      M ∈ sel F (fld P) ∧ N = T˘ ⨾ M ⨾ (daggerRel T˘)˘) := by
  obtain ⟨⟨h1, h2⟩, hc, hP⟩ := pm172_aux_ss h
  constructor
  · rintro ⟨hN, rfl⟩
    exact ⟨pm172_aux_tr_sel h1 h2 hc hP hN, (pm172_aux_tr_back h2 hc hN).symm⟩
  · rintro ⟨hM, rfl⟩
    obtain ⟨N0, hN0, rfl⟩ := pm172_aux_tr_surj h1 h2 hc hP hM
    rw [pm172_aux_tr_back h2 hc hN0]; exact ⟨hN0, rfl⟩

/-- ✱172·41. \(\vdash :T\in P\,\overline{\text{smor smor}}\, Q.\supset .F_{\Delta }ʻCʻP=(T\parallel \text{Cnv}ʻT\dagger )ʻʻF_{\Delta }ʻCʻQ\) -/
theorem pm172_41 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop} (h : T ∈ smorsmorbar P Q) :
    sel F (fld P) = (T ∥ (daggerRel T)˘) ʻʻ sel F (fld Q) := by
  obtain ⟨⟨h1, h2⟩, hc, hP⟩ := pm172_aux_ss h
  refine Set.Subset.antisymm (fun M hM => ?_) (pm172_403 h)
  obtain ⟨N, hN, e⟩ := pm172_aux_tr_surj h1 h2 hc hP hM
  exact ⟨N, hN, (pm172_aux_dpar_tr _ _ _).2 e⟩

/-- ✱172·42. \(\vdash :T\in P\,\overline{\text{smor smor}}\, Q.\supset .(T\mid \text{Cnv}ʻT\dagger )\upharpoonright Cʻ\Pi ʻQ\in (\Pi ʻP)\,\overline{\text{smor}}\,(\Pi ʻQ)\)

**Status.** proved (reading): transcription error: the e-text prints `T ∣ Cnv'T†`, which is not
significant (the relative product of `T` with a relation of relations); as in ✱172·4·43, it is
`T ∥ Cnv'T†`. -/
theorem pm172_42 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop} (h : T ∈ smorsmorbar P Q) :
    (T ∥ (daggerRel T)˘) ↾ fld (relPi Q) ∈ smorbar (relPi P) (relPi Q) := by
  obtain ⟨⟨h1, h2⟩, hc, hP⟩ := pm172_aux_ss h
  refine ⟨⟨pm172_4 h, ?_⟩, ?_⟩
  · ext N; constructor
    · intro hN; exact ⟨_, (pm172_aux_dpar_tr _ _ _).2 rfl, hN⟩
    · rintro ⟨M, -, hN⟩; exact hN
  · funext M M'; apply propext
    rw [semi_apply]
    constructor
    · intro hMM
      obtain ⟨⟨hM, hM'⟩, -⟩ := pm172_aux_relPi_iff.1 hMM
      obtain ⟨N, hN, rfl⟩ := pm172_aux_tr_surj h1 h2 hc hP hM
      obtain ⟨N', hN', rfl⟩ := pm172_aux_tr_surj h1 h2 hc hP hM'
      have hQ := (pm172_aux_tr_relPi h1 h2 hc hP hN hN').1 hMM
      exact ⟨N, N', ⟨⟨(pm172_aux_dpar_tr _ _ _).2 rfl, N', Or.inl hQ⟩,
        ⟨(pm172_aux_dpar_tr _ _ _).2 rfl, N, Or.inr hQ⟩⟩, hQ⟩
    · rintro ⟨N, N', ⟨⟨hMN, hN⟩, ⟨hMN', hN'⟩⟩, hQ⟩
      rw [pm172_aux_dpar_tr] at hMN hMN'
      rw [hMN, hMN']
      exact (pm172_aux_tr_relPi h1 h2 hc hP (pm172_12 Q hN) (pm172_12 Q hN')).2 hQ

/-- ✱172·421. \[\begin{align}\vdash :S=T\upharpoonright Cʻ\Sigma ʻQ.S&\in P\,\overline{\text{smor smor}}\, Q.\supset .\\ &(S\parallel \text{Cnv}ʻS\dagger )\upharpoonright F_{\Delta }ʻCʻQ=(T\parallel \text{Cnv}ʻT\dagger )\upharpoonright F_{\Delta }ʻCʻQ\end{align}\] -/
theorem pm172_421 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T S : α → β → Prop}
    (h : S = T ↾ fld (relSigma Q) ∧ S ∈ smorsmorbar P Q) :
    (S ∥ (daggerRel S)˘) ↾ sel F (fld Q) = (T ∥ (daggerRel T)˘) ↾ sel F (fld Q) := by
  obtain ⟨rfl, -⟩ := h
  funext M N; apply propext
  constructor
  · rintro ⟨hMN, hN⟩
    rw [pm172_aux_dpar_tr, pm172_aux_tr_cres hN] at hMN
    exact ⟨(pm172_aux_dpar_tr _ _ _).2 hMN, hN⟩
  · rintro ⟨hMN, hN⟩
    rw [pm172_aux_dpar_tr, ← pm172_aux_tr_cres hN] at hMN
    exact ⟨(pm172_aux_dpar_tr _ _ _).2 hMN, hN⟩

/-- ✱172·43. \[\begin{align}\vdash :T\upharpoonright Cʻ\Sigma ʻQ\in &P\,\overline{\text{smor smor}}\,Q.\supset .\\ &(T\parallel \text{Cnv}ʻT\dagger )\upharpoonright Cʻ\Pi ʻQ\in (\Pi ʻP)\overline{\text{smor}} (\Pi ʻQ)\\ [*172·42·421]\end{align}\] -/
theorem pm172_43 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop}
    (h : T ↾ fld (relSigma Q) ∈ smorsmorbar P Q) :
    (T ∥ (daggerRel T)˘) ↾ fld (relPi Q) ∈ smorbar (relPi P) (relPi Q) := by
  have e : ((T ↾ fld (relSigma Q)) ∥ (daggerRel (T ↾ fld (relSigma Q)))˘) ↾ fld (relPi Q) =
      (T ∥ (daggerRel T)˘) ↾ fld (relPi Q) := by
    funext M N; apply propext
    constructor
    · rintro ⟨hMN, hN⟩
      rw [pm172_aux_dpar_tr, pm172_aux_tr_cres (pm172_12 Q hN)] at hMN
      exact ⟨(pm172_aux_dpar_tr _ _ _).2 hMN, hN⟩
    · rintro ⟨hMN, hN⟩
      rw [pm172_aux_dpar_tr, ← pm172_aux_tr_cres (pm172_12 Q hN)] at hMN
      exact ⟨(pm172_aux_dpar_tr _ _ _).2 hMN, hN⟩
  rw [← e]; exact pm172_42 h

/-- ✱172·44. \(\vdash :P\text{ sm }\text{smor}Q.\supset .\Pi ʻP\,\text{smor}\,\Pi ʻQ \quad[*172·42]\)

**Status.** proved (reading): transcription error: the e-text prints `P sm smor Q` for `P smor smor
Q`. -/
theorem pm172_44 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} (h : smorsmor P Q) :
    smor (relPi P) (relPi Q) := by
  obtain ⟨T, hT⟩ := h; exact ⟨_, pm172_42 hT⟩

/-- ✱172·45. \[\begin{align}\vdash \colon\ldotp \text{Mult ax}.\supset :P,Q\in \text{Rel}^{2}\text{excl}.\exists !P\,\overline{\text{smor}}\,Q\cap &\text{Rl}ʻ\text{smor}.\supset .\\ &\Pi ʻP\text{smor}\Pi ʻQ\\ [*164·44 . *172·44]\end{align}\]

**Status.** proved (reading): `Mult ax` is taken at the type of the correlators of members of `C'P`
with members of `C'Q`; it is a theorem of Lean (Basic §4) and is not used in the proof (the
correlators of ✱164·44 are chosen with `Classical.epsilon`). -/
theorem pm172_45 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} (_hm : MultAx (α → β → Prop))
    (h : (P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ (smorbar P Q ∩ rl smor).Nonempty) :
    smor (relPi P) (relPi Q) := by
  obtain ⟨⟨hP, hQ⟩, S, hS, hSs⟩ := h
  exact pm172_44 (pm172_aux_164_44 hP hQ hS hSs)

/-- ✱172·5. \(\vdash :CʻP=CʻQ.P\dot{\cap} J=Q\dot{\cap} J.\supset .\Pi ʻP=\Pi ʻQ\) -/
theorem pm172_5 {P Q : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : fld P = fld Q ∧ P ⩀ J = Q ⩀ J) : relPi P = relPi Q := by
  have e : ∀ R S, (P R S ∧ R ≠ S) ↔ (Q R S ∧ R ≠ S) := fun R S =>
    Iff.of_eq (congrFun (congrFun h.2 R) S)
  funext M N; apply propext
  rw [pm172_aux_relPi_iff, pm172_aux_relPi_iff, h.1]
  simp only [e]

/-- ✱172·51. \(\vdash .\Pi ʻP=\Pi ʻ(P\unicode{x228d} I\upharpoonright CʻP) \quad[*172·5]\) -/
theorem pm172_51 (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    relPi P = relPi (P ⊍ I ↾ fld P) := by
  apply pm172_5
  constructor
  · ext R; constructor
    · rintro ⟨S, h | h⟩
      · exact ⟨S, Or.inl (Or.inl h)⟩
      · exact ⟨S, Or.inr (Or.inl h)⟩
    · rintro ⟨S, (h | ⟨h, hS⟩) | (h | ⟨h, hR⟩)⟩
      · exact ⟨S, Or.inl h⟩
      · rw [show R = S from h]; exact hS
      · exact ⟨S, Or.inr h⟩
      · exact hR
  · funext R S; apply propext
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
    · rintro ⟨h1 | ⟨h1, -⟩, h2⟩
      · exact ⟨h1, h2⟩
      · exact absurd h1 h2

/-- ✱172·52. \(\vdash \colon\ldotp Q\in \text{ᗡ}ʻP.\supset _{Q}.(\exists R).RPQ.R\neq Q:\supset .\Pi ʻP=\Pi ʻ(P\dot{\cap} J)\) -/
theorem pm172_52 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : ∀ Q, Q ∈ codom P → ∃ R, P R Q ∧ R ≠ Q) : relPi P = relPi (P ⩀ J) := by
  apply pm172_5
  constructor
  · ext Q; constructor
    · intro hQ
      by_cases hc : Q ∈ codom P
      · obtain ⟨R, hR, hne⟩ := h Q hc; exact ⟨R, Or.inr ⟨hR, hne⟩⟩
      · obtain ⟨R, hR | hR⟩ := hQ
        · refine ⟨R, Or.inl ⟨hR, fun e => hc ?_⟩⟩
          exact ⟨Q, (show Q = R from e) ▸ hR⟩
        · exact absurd ⟨R, hR⟩ hc
    · rintro ⟨R, ⟨h1, -⟩ | ⟨h1, -⟩⟩
      · exact ⟨R, Or.inl h1⟩
      · exact ⟨R, Or.inr h1⟩
  · funext R S; apply propext
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, h2⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩

/-!
## [✱173] The product of the relations of a field (continued)

*(Vol. 2, p. 443)*

> *Summary of* *173.
>
> In this number, we shall consider the relation between the domains of relations related by \(\Pi ʻP\), *i.e.* we shall consider \(\text{D}^{;}\Pi ʻP\). This relation bears to \(\Pi ʻP\) a relation analogous to that which \(\text{Prod}ʻ\kappa\) bears to \({\in}_{\Delta}ʻ\kappa\). We shall denote it by "\(\text{Prod}ʻP\)." When \(P\in \text{Rel}^{2}\text{excl}\), \(\text{Prod}ʻP\) is like \(\Pi ʻP\), and is often more convenient than \(\Pi ʻP\). When \(P\in \text{Rel}^{2}\text{excl}\), \(\text{Prod}ʻP\) arranges the multiplicative class of \(CʻʻCʻP\) by first differences, taking first differences to mean that the earliest member \(Q\) of \(CʻP\) for which \(\mu \cap CʻQ\neq \nu \cap CʻQ\) has the \(\mu\)-member earlier than the \(\nu\)-member in the \(Q\)-series.
>
> The properties of \(\text{Prod}ʻP\) all result immediately from those of \(\Pi ʻP\), and offer no difficulty of any kind. The most important of them are:
>
> *173·14. \(\vdash :\dot{\exists} !P.C\upharpoonright CʻP\in 1\rightarrow 1.\supset .Cʻ\text{Prod}ʻP=\text{Prod}ʻCʻʻCʻP\)
>
> …

**Lean reading.** `Prod'P` is `prodR P = D ⁏ relPi P` (`D;Π'P`); `Prod'κ` of ✱115 is `prodK`,
`C''C'P` is `C ʻʻ fld P`, `T_∈` is `imgRel T`, `R†;Q` is `daggerRel R ⁏ Q`. ✱173·16 rests on the
fact that in a relation of mutually exclusive relations a selection is determined by its domain
(`pm173_aux_excl_dom`); ✱173·24 also covers the case `P = Q` (then both fields are empty).
✱173·14 rests on the correspondence `M ↦ (x, Q) ↦ (x, C'Q)` of `F_Δ'C'P` with `∈_Δ'C''C'P` (when
`C ↾ C'P` is one-one), ✱173·3 on ✱172·43 and `D'(T | N | Cnv'T†) = T''D'N`; in ✱173·27 the
relations need not be distinct (if two are equal, a field is empty and both sides are `Λ̇`).

**Status.** proved (all propositions; ✱173·01 definition; ✱173·3 proved (reading): transcription
error of the e-text, see its docstring).
-/

section Helpers173
variable {α : Type u} {β : Type v}

theorem pm173_aux_rEx_semi_graph (f : β → α) (R : β → β → Prop) : rEx (graph f ⁏ R) ↔ rEx R := by
  constructor
  · rintro ⟨x, y, h⟩
    obtain ⟨z, w, -, hzw⟩ := (semi_graph_apply f R x y).1 h
    exact ⟨z, w, hzw⟩
  · rintro ⟨z, w, h⟩; exact ⟨f z, f w, (semi_graph_apply f R _ _).2 ⟨z, w, ⟨rfl, rfl⟩, h⟩⟩

theorem pm173_aux_semi_rNull (S : α → β → Prop) : S ⁏ (rNull : β → β → Prop) = rNull := by
  funext x y; apply propext
  constructor
  · intro h; obtain ⟨z, w, -, h'⟩ := (semi_apply _ _ x y).1 h; exact absurd h' (rNull_apply z w)
  · intro h; exact absurd h (rNull_apply x y)

theorem pm173_aux_semi_congr {R R' : α → β → Prop} {S : β → β → Prop}
    (h : ∀ x z, z ∈ fld S → (R x z ↔ R' x z)) : R ⁏ S = R' ⁏ S := by
  funext x y; apply propext
  rw [semi_apply, semi_apply]
  constructor
  · rintro ⟨z, w, ⟨h1, h2⟩, h3⟩
    exact ⟨z, w, ⟨(h x z ⟨w, Or.inl h3⟩).1 h1, (h y w ⟨z, Or.inr h3⟩).1 h2⟩, h3⟩
  · rintro ⟨z, w, ⟨h1, h2⟩, h3⟩
    exact ⟨z, w, ⟨(h x z ⟨w, Or.inl h3⟩).2 h1, (h y w ⟨z, Or.inr h3⟩).2 h2⟩, h3⟩

theorem pm173_aux_relPi_rEx {P : (α → α → Prop) → (α → α → Prop) → Prop} (h : rEx (relPi P)) :
    rEx P := by
  by_contra hP
  have : P = rNull := by by_contra h'; exact hP (pm172_aux_rEx_iff_ne.2 h')
  obtain ⟨M, N, hMN⟩ := h; rw [this, pm172_13] at hMN; exact rNull_apply M N hMN

/-- In a relation of mutually exclusive relations two selections with the same domain are equal. -/
theorem pm173_aux_excl_dom {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : P ∈ Rel2excl)
    {M N : α → (α → α → Prop) → Prop} (hM : M ∈ sel F (fld P)) (hN : N ∈ sel F (fld P))
    (e : dom M = dom N) : M = N := by
  refine pm172_aux_sel_ext hM hN fun x Q hx => ?_
  have : x ∈ dom N := by rw [← e]; exact ⟨Q, hx⟩
  obtain ⟨Q', hQ'⟩ := this
  by_cases hQQ : Q = Q'
  · rw [hQQ]; exact hQ'
  · have h0 := hP Q Q' ⟨⟨pm172_aux_sel_mem hM hx, pm172_aux_sel_mem hN hQ'⟩, hQQ⟩
    have : x ∈ fld Q ∩ fld Q' := ⟨pm172_aux_sel_sub hM hx, pm172_aux_sel_sub hN hQ'⟩
    rw [h0] at this; exact absurd this (pm170_aux_Null x)

theorem pm173_aux_dom_two {P Q : α → α → Prop} {M : α → (α → α → Prop) → Prop}
    (hM : M ∈ sel F (ι P ∪ ι Q)) {a b : α} (ha : M a P) (hb : M b Q) : dom M = ι a ∪ ι b := by
  ext u; constructor
  · rintro ⟨R, hR⟩
    rcases pm172_aux_sel_mem hM hR with h | h <;> rw [pm170_aux_mem_iota] at h <;> rw [h] at hR
    · exact Or.inl (pm172_aux_sel_unique hM hR ha)
    · exact Or.inr (pm172_aux_sel_unique hM hR hb)
  · rintro (h | h) <;> rw [pm170_aux_mem_iota] at h <;> rw [h]
    · exact ⟨P, ha⟩
    · exact ⟨Q, hb⟩


theorem pm173_aux_eq_rNull {Q : α → α → Prop} (h : fld Q = ∅) : Q = rNull := by
  by_contra h'
  obtain ⟨x, hx⟩ := pm170_aux_rEx_iff_fld.1 (pm172_aux_rEx_iff_ne.2 h')
  rw [h] at hx; exact hx

/-- In a relation of mutually exclusive relations, `C ↾ C'P` is one-one (✱163·14). -/
theorem pm173_aux_C_one_one {P : (α → α → Prop) → (α → α → Prop) → Prop} (h : P ∈ Rel2excl) :
    C ↾ fld P ∈ arrow one one := by
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro K K' Q ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    exact (show K = fld Q from h1).trans (show K' = fld Q from h2).symm
  · rintro K Q Q' ⟨⟨h1, hQ⟩, ⟨h2, hQ'⟩⟩
    have e : fld Q = fld Q' := (show K = fld Q from h1).symm.trans h2
    by_contra hne
    have h0 := pm172_aux_inter_Null.1 (h Q Q' ⟨⟨hQ, hQ'⟩, hne⟩)
    have hQe : fld Q = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => h0 x hx (e ▸ hx)
    have hQe' : fld Q' = ∅ := e ▸ hQe
    exact hne ((pm173_aux_eq_rNull hQe).trans (pm173_aux_eq_rNull hQe').symm)

/-- A relation whose field lies in `C'P ∪ ι'Z` is a relation of mutually exclusive relations when
`P` is one and `C'Z` is disjoint from `C'Σ'P`. -/
theorem pm173_aux_excl_add {P P' : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    (hP : P ∈ Rel2excl) (hZ : fld Z ∩ fld (relSigma P) = Λ) (hsub : fld P' ⊆ fld P ∪ ι Z) :
    P' ∈ Rel2excl := by
  have hZQ : ∀ Q, Q ∈ fld P → fld Q ∩ fld Z = Λ := fun Q hQ => pm172_aux_inter_Null.2
    fun x h1 h2 => pm172_aux_inter_Null.1 hZ x h2 (pm172_aux_mem_fld_relSigma hQ h1)
  rintro Q R ⟨⟨hQ, hR⟩, hne⟩
  rcases hsub hQ with hQ | hQ <;> rcases hsub hR with hR | hR
  · exact hP Q R ⟨⟨hQ, hR⟩, hne⟩
  · rw [pm170_aux_mem_iota.1 hR]; exact hZQ Q hQ
  · rw [pm170_aux_mem_iota.1 hQ, Set.inter_comm]; exact hZQ R hR
  · exact absurd ((pm170_aux_mem_iota.1 hQ).trans (pm170_aux_mem_iota.1 hR).symm) hne

theorem pm173_aux_fld_addLast_sub (Z : α → α → Prop) (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    fld (P ⇸ Z) ⊆ fld P ∪ ι Z := by
  rintro R ⟨S, (h | ⟨h, -⟩) | (h | ⟨-, h⟩)⟩
  · exact Or.inl ⟨S, Or.inl h⟩
  · exact Or.inl h
  · exact Or.inl ⟨S, Or.inr h⟩
  · exact Or.inr h

theorem pm173_aux_relPi_empty {P : (α → α → Prop) → (α → α → Prop) → Prop} {S : α → α → Prop}
    (hS : S ∈ fld P) (h : fld S = ∅) (M N : α → (α → α → Prop) → Prop) : ¬ relPi P M N := by
  rintro ⟨⟨hM, -⟩, -⟩
  obtain ⟨x, hx⟩ := pm172_aux_sel_exists hM hS
  have := pm172_aux_sel_sub hM hx
  rw [show F x S ↔ x ∈ fld S from Iff.rfl, h] at this; exact this

theorem pm173_aux_dom_tr (T : α → β → Prop) (N : β → (β → β → Prop) → Prop) :
    dom (T ⨾ N ⨾ (daggerRel T)˘) = T ʻʻ dom N := by
  ext x; constructor
  · rintro ⟨R, hR⟩
    obtain ⟨y, S, ⟨hxy, hyS⟩, -⟩ := (pm172_aux_tr_apply _ _ _ _).1 hR
    exact ⟨y, ⟨S, hyS⟩, hxy⟩
  · rintro ⟨y, ⟨S, hyS⟩, hxy⟩
    exact ⟨_, (pm172_aux_tr_apply _ _ _ _).2 ⟨y, S, ⟨hxy, hyS⟩, rfl⟩⟩

end Helpers173

/-- ✱173·01 (Df). \(\text{Prod}ʻP=\text{D}^{;}\Pi ʻP \quad\text{Df}\) -/
theorem pm173_01 (P : (α → α → Prop) → (α → α → Prop) → Prop) : prodR P = D ⁏ relPi P := rfl

/-- ✱173·1. \(\vdash .\text{Prod}ʻP=\text{D}^{;}\Pi ʻP \quad[(*175·01)]\)

The e-text's reference `(*175·01)` is a misprint for the Df ✱173·01 (there is no ✱175); the
enunciation itself is as PM intends, so the status is `proved`. -/
theorem pm173_1 (P : (α → α → Prop) → (α → α → Prop) → Prop) : prodR P = D ⁏ relPi P := rfl

/-- ✱173·11. \[\begin{align}&\vdash :\mu (\text{Prod}ʻP)\nu .\equiv .(\exists M,N).M(\Pi ʻP)N.\mu =\text{D}ʻM.\nu =\text{D}ʻN\\ &[*173·1.*150·51]\end{align}\] -/
theorem pm173_11 {P : (α → α → Prop) → (α → α → Prop) → Prop} {μ ν : Set α} :
    prodR P μ ν ↔ ∃ M N, (relPi P M N ∧ μ = dom M) ∧ ν = dom N := by
  rw [show prodR P = graph dom ⁏ relPi P from rfl, semi_graph_apply]
  exact ⟨fun ⟨M, N, ⟨h1, h2⟩, h3⟩ => ⟨M, N, ⟨h3, h1⟩, h2⟩, fun ⟨M, N, ⟨h3, h1⟩, h2⟩ => ⟨M, N, ⟨h1, h2⟩, h3⟩⟩

/-- ✱173·12. \(\vdash .Cʻ\text{Prod}ʻP\subset \text{D}ʻʻF_{\Delta }ʻCʻP \quad[*172·12.*150·202]\) -/
theorem pm173_12 (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    fld (prodR P) ⊆ D ʻʻ sel F (fld P) := by
  rw [show fld (prodR P) = D ʻʻ fld (relPi P) from fld_semi_graph _ _]
  rintro A ⟨M, hM, hA⟩; exact ⟨M, pm172_12 P hM, hA⟩

/-- ✱173·121. \(\vdash .Cʻ\text{Prod}ʻP=\text{D}ʻʻCʻ\Pi ʻP \quad[*173·1.*150·22]\) -/
theorem pm173_121 (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    fld (prodR P) = D ʻʻ fld (relPi P) := fld_semi_graph _ _

/-- ✱173·13. \(\vdash :\dot{\exists} !P.\supset .Cʻ\text{Prod}ʻP=\text{D}ʻʻF_{\Delta }ʻCʻP \quad[*172·17.*173·121]\) -/
theorem pm173_13 {P : (α → α → Prop) → (α → α → Prop) → Prop} (h : rEx P) :
    fld (prodR P) = D ʻʻ sel F (fld P) := by
  rw [pm173_121, pm172_17 h]

/-- ✱173·14. \(\vdash :\dot{\exists} !P.C\upharpoonright CʻP\in 1\rightarrow 1.\supset .Cʻ\text{Prod}ʻP=\text{Prod}ʻCʻʻCʻP\) -/
theorem pm173_14 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : rEx P ∧ C ↾ fld P ∈ arrow one one) : fld (prodR P) = prodK (C ʻʻ fld P) := by
  obtain ⟨hP, hC⟩ := h
  have hinj : ∀ Q Q', Q ∈ fld P → Q' ∈ fld P → fld Q = fld Q' → Q = Q' := fun Q Q' hQ hQ' e =>
    (mem_arrow_one_one.1 hC).2 (fld Q) Q Q' ⟨⟨rfl, hQ⟩, ⟨e, hQ'⟩⟩
  rw [pm173_13 hP]
  ext μ; constructor
  · rintro ⟨M, hM, hμ⟩
    refine ⟨fun x A => ∃ Q, M x Q ∧ A = fld Q, pm172_aux_mk_sel ?_ ?_ ?_, ?_⟩
    · rintro x y A ⟨Q, hx, rfl⟩ ⟨Q', hy, e⟩
      rw [hinj Q Q' (pm172_aux_sel_mem hM hx) (pm172_aux_sel_mem hM hy) e] at hx
      exact pm172_aux_sel_unique hM hx hy
    · rintro x A ⟨Q, hx, rfl⟩; exact pm172_aux_sel_sub hM hx
    · ext A; constructor
      · rintro ⟨x, Q, hx, rfl⟩; exact ⟨Q, pm172_aux_sel_mem hM hx, rfl⟩
      · rintro ⟨Q, hQ, rfl⟩
        obtain ⟨x, hx⟩ := pm172_aux_sel_exists hM hQ
        exact ⟨x, Q, hx, rfl⟩
    · show μ = dom _
      rw [show μ = dom M from hμ]
      ext x; exact ⟨fun ⟨Q, hx⟩ => ⟨fld Q, Q, hx, rfl⟩, fun ⟨_, Q, hx, _⟩ => ⟨Q, hx⟩⟩
  · rintro ⟨M', hM', hμ⟩
    refine ⟨fun x Q => Q ∈ fld P ∧ M' x (fld Q), pm172_aux_mk_sel ?_ ?_ ?_, ?_⟩
    · rintro x y Q ⟨-, hx⟩ ⟨-, hy⟩; exact pm172_aux_sel_unique hM' hx hy
    · rintro x Q ⟨-, hx⟩; exact pm172_aux_sel_sub hM' hx
    · ext Q; constructor
      · rintro ⟨x, hQ, -⟩; exact hQ
      · intro hQ
        obtain ⟨x, hx⟩ := pm172_aux_sel_exists hM' ⟨Q, hQ, rfl⟩
        exact ⟨x, hQ, hx⟩
    · show μ = dom _
      rw [show μ = dom M' from hμ]
      ext x; constructor
      · rintro ⟨A, hx⟩
        obtain ⟨Q, hQ, rfl⟩ := pm172_aux_sel_mem hM' hx
        exact ⟨Q, hQ, hx⟩
      · rintro ⟨Q, -, hx⟩; exact ⟨fld Q, hx⟩

/-- ✱173·15. \[\begin{align}&\vdash :\text{D}\upharpoonright F_{\Delta }ʻCʻP\in 1\rightarrow 1.\supset .\text{D}\upharpoonright Cʻ\Pi ʻP\in (\text{Prod}ʻP)\,\overline{\text{smor}}\,(\Pi ʻP)\\ &[*173·1.*172·12.*151·231]\end{align}\] -/
theorem pm173_15 {P : (α → α → Prop) → (α → α → Prop) → Prop} (h : D ↾ sel F (fld P) ∈ arrow one one) :
    D ↾ fld (relPi P) ∈ smorbar (prodR P) (relPi P) := by
  obtain ⟨-, h2⟩ := mem_arrow_one_one.1 h
  apply pm170_aux_smorbar dom
  · intro M N hM hN e
    exact h2 (dom M) M N ⟨⟨rfl, pm172_12 P hM⟩, ⟨e, pm172_12 P hN⟩⟩
  · intro x y
    rw [pm173_11]
    exact ⟨fun ⟨M, N, ⟨h1, h2⟩, h3⟩ => ⟨M, N, h1, h2, h3⟩, fun ⟨M, N, h1, h2, h3⟩ => ⟨M, N, ⟨h1, h2⟩, h3⟩⟩

/-- ✱173·151. \(\vdash :\text{D}\upharpoonright F_{\Delta }ʻCʻP\in 1\rightarrow 1.\supset .\text{Prod}ʻP\,\text{smor}\,\Pi ʻP \quad [*173·15]\) -/
theorem pm173_151 {P : (α → α → Prop) → (α → α → Prop) → Prop} (h : D ↾ sel F (fld P) ∈ arrow one one) :
    smor (prodR P) (relPi P) := ⟨_, pm173_15 h⟩

/-- ✱173·16. \[\begin{align}\vdash :P\in &\text{Rel}^{2}\text{excl}.\supset .\\ &\text{Prod}ʻP\,\text{smor}\,\Pi ʻP.\text{D}\upharpoonright Cʻ\Pi ʻP\in (\text{Prod}ʻP)\,\overline{\text{smor}}\,(\Pi ʻP)\end{align}\] -/
theorem pm173_16 {P : (α → α → Prop) → (α → α → Prop) → Prop} (h : P ∈ Rel2excl) :
    smor (prodR P) (relPi P) ∧ D ↾ fld (relPi P) ∈ smorbar (prodR P) (relPi P) := by
  have h' : D ↾ sel F (fld P) ∈ arrow one one := by
    refine mem_arrow_one_one.2 ⟨?_, ?_⟩
    · rintro x y M ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; exact (show x = dom M from h1).trans (show y = dom M from h2).symm
    · rintro A M N ⟨⟨h1, hM⟩, ⟨h2, hN⟩⟩
      exact pm173_aux_excl_dom h hM hN ((show A = dom M from h1).symm.trans h2)
  exact ⟨pm173_151 h', pm173_15 h'⟩

/-- ✱173·161. \[\begin{align}&\vdash :P\in \text{Rel}^{2}\text{excl}.\dot{\exists} !P.\supset .Cʻ\text{Prod}ʻP=\text{Prod}ʻCʻʻCʻP\\ &[*173·14.*163·14]\end{align}\] -/
theorem pm173_161 {P : (α → α → Prop) → (α → α → Prop) → Prop} (h : P ∈ Rel2excl ∧ rEx P) :
    fld (prodR P) = prodK (C ʻʻ fld P) :=
  pm173_14 ⟨h.2, pm173_aux_C_one_one h.1⟩

/-- ✱173·17. \(\vdash :\dot{\exists} !\text{Prod}ʻP.\supset .sʻCʻ\text{Prod}ʻP=Cʻ\Sigma ʻP\) -/
theorem pm173_17 {P : (α → α → Prop) → (α → α → Prop) → Prop} (h : rEx (prodR P)) :
    sumCls (fld (prodR P)) = fld (relSigma P) := by
  have hPi : rEx (relPi P) := (pm173_aux_rEx_semi_graph dom (relPi P)).1 h
  have hP := pm173_aux_relPi_rEx hPi
  obtain ⟨M0, hM0⟩ := (pm172_18 hP).1 hPi
  rw [pm173_121, pm172_17 hP]
  ext x; constructor
  · rintro ⟨A, ⟨M, hM, rfl⟩, Q, hx⟩
    obtain ⟨y, hy | hy⟩ := pm172_aux_sel_sub hM hx
    · exact ⟨y, Or.inl (Or.inl ⟨Q, pm172_aux_sel_mem hM hx, hy⟩)⟩
    · exact ⟨y, Or.inr (Or.inl ⟨Q, pm172_aux_sel_mem hM hx, hy⟩)⟩
  · rintro ⟨y, h' | h'⟩
    all_goals
      obtain ⟨Q, hQ, hxQ⟩ : ∃ Q, Q ∈ fld P ∧ x ∈ fld Q := by
        rcases (relSigma_apply P _ _).1 h' with ⟨Q, hQ, hq⟩ | ⟨Q, R, ⟨h1, h2⟩, hQR⟩
        · first | exact ⟨Q, hQ, y, Or.inl hq⟩ | exact ⟨Q, hQ, y, Or.inr hq⟩
        · first | exact ⟨Q, ⟨R, Or.inl hQR⟩, h1⟩ | exact ⟨R, ⟨Q, Or.inr hQR⟩, h2⟩
      exact ⟨_, ⟨_, pm172_aux_modify hM0 hQ hxQ, rfl⟩, Q, Or.inr ⟨rfl, rfl⟩⟩

/-- ✱173·2. \(\vdash .\text{Prod}ʻ\dot{\Lambda} =\dot{\Lambda} \quad[*172·13.*150·42]\) -/
theorem pm173_2 : prodR (rNull : (α → α → Prop) → (α → α → Prop) → Prop) = rNull := by
  rw [pm173_1, pm172_13, pm173_aux_semi_rNull]

/-- ✱173·21. \(\vdash :\dot{\exists} !\text{Prod}ʻP.\equiv .\dot{\exists} !\Pi ʻP \quad[*173·1.*150·24.*33·12]\) -/
theorem pm173_21 {P : (α → α → Prop) → (α → α → Prop) → Prop} : rEx (prodR P) ↔ rEx (relPi P) :=
  pm173_aux_rEx_semi_graph dom (relPi P)

/-- ✱173·22. \(\vdash .\text{Prod}ʻ(P\downarrow P)=\iota ^{;}P\) -/
theorem pm173_22 (P : α → α → Prop) : prodR (P ↓ P) = iota ⁏ P := by
  rw [pm173_1, pm172_2, opSemi, semi_semi]
  congr 1
  funext A x; apply propext
  constructor
  · rintro ⟨M, h1, h2⟩
    show A = ι x
    rw [show A = dom M from h1, show M = x ↓ P from h2]
    ext u; exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨P, h, rfl⟩⟩
  · intro h
    refine ⟨x ↓ P, ?_, rfl⟩
    show A = dom (x ↓ P)
    rw [show A = ι x from h]
    ext u; exact ⟨fun h => ⟨P, h, rfl⟩, fun ⟨_, h⟩ => h.1⟩

/-- ✱173·23. \(\vdash :P\neq Q.\supset .\text{Prod}ʻ(P\downarrow Q)=C^{;}(P\times Q)\) -/
theorem pm173_23 {P Q : α → α → Prop} (hne : P ≠ Q) : prodR (P ↓ Q) = C ⁏ (P ×ᵣ Q) := by
  rw [pm172_21 hne, semi_semi, pm173_1]
  apply pm173_aux_semi_congr
  intro A M hM
  rw [pm172_17 ⟨P, Q, rfl, rfl⟩, pm170_aux_fld_couple] at hM
  obtain ⟨a, b, ha, hb⟩ := pm172_aux_sel_two_vals hM
  constructor
  · intro h
    refine ⟨_, ?_, rfl⟩
    show A = fld (daggerOp M (Q ↓ P))
    rw [pm172_aux_dagger_two hM ha hb, pm170_aux_fld_couple, Set.union_comm,
      ← pm173_aux_dom_two hM ha hb]
    exact h
  · rintro ⟨X, h1, h2⟩
    show A = dom M
    rw [show A = fld X from h1, show X = daggerOp M (Q ↓ P) from h2, pm172_aux_dagger_two hM ha hb,
      pm170_aux_fld_couple, Set.union_comm, ← pm173_aux_dom_two hM ha hb]

/-- ✱173·24. \[\begin{align}\vdash :CʻP\cap CʻQ=\Lambda.\supset .C\upharpoonright Cʻ(P\times Q)\in &\{\text{Prod}ʻ(P\downarrow Q)\}\,\overline{\text{smor}}\,(P\times Q).\\ &\text{Prod}ʻ(P\downarrow Q)\,\text{smor}\,P\times Q\end{align}\] -/
theorem pm173_24 {P Q : α → α → Prop} (h : fld P ∩ fld Q = Λ) :
    C ↾ fld (P ×ᵣ Q) ∈ smorbar (prodR (P ↓ Q)) (P ×ᵣ Q) ∧ smor (prodR (P ↓ Q)) (P ×ᵣ Q) := by
  have key : C ↾ fld (P ×ᵣ Q) ∈ smorbar (prodR (P ↓ Q)) (P ×ᵣ Q) := by
    by_cases hne : P = Q
    · subst hne
      have hP : ∀ x, x ∉ fld P := fun x hx => by
        have : x ∈ fld P ∩ fld P := ⟨hx, hx⟩
        rw [h] at this; exact pm170_aux_Null x this
      have hR : ∀ U V, ¬ (P ×ᵣ P) U V := fun U V h' => by
        obtain ⟨b, a, ⟨hb, -⟩, -⟩ := pm170_aux_fld_rtimes ⟨V, Or.inl h'⟩
        exact hP b hb
      apply pm170_aux_smorbar fld
      · intro U V hU; obtain ⟨W, hW | hW⟩ := hU <;> exact absurd hW (hR _ _)
      · intro A B
        rw [pm173_22]
        constructor
        · intro h'; obtain ⟨z, w, -, hzw⟩ := (semi_apply _ _ A B).1 h'
          exact absurd ⟨w, Or.inl hzw⟩ (hP z)
        · rintro ⟨U, V, hUV, -⟩; exact absurd hUV (hR U V)
    · apply pm170_aux_smorbar fld
      · intro U V hU hV e
        obtain ⟨b, a, ⟨hb, ha⟩, rfl⟩ := pm170_aux_fld_rtimes hU
        obtain ⟨d, c, ⟨hd, hc⟩, rfl⟩ := pm170_aux_fld_rtimes hV
        simp only [pm170_aux_fld_couple] at e
        have hb' : b ∈ ι d ∪ ι c := by rw [← e]; exact Or.inl rfl
        have ha' : a ∈ ι d ∪ ι c := by rw [← e]; exact Or.inr rfl
        have hbd : b = d := by
          rcases hb' with h' | h'
          · exact h'
          · exact absurd ((pm170_aux_mem_iota.1 h') ▸ hc) (pm170_aux_disj (Q := P)
              (by rw [Set.inter_comm]; exact h) hb)
        have hac : a = c := by
          rcases ha' with h' | h'
          · exact absurd ((pm170_aux_mem_iota.1 h') ▸ hd) (pm170_aux_disj h ha)
          · exact h'
        rw [hbd, hac]
      · intro A B
        rw [pm173_23 hne, show (C : Set α → (α → α → Prop) → Prop) = graph fld from rfl,
          semi_graph_apply]
        exact ⟨fun ⟨U, V, ⟨h1, h2⟩, h3⟩ => ⟨U, V, h3, h1, h2⟩, fun ⟨U, V, h3, h1, h2⟩ => ⟨U, V, ⟨h1, h2⟩, h3⟩⟩
  exact ⟨key, ⟨_, key⟩⟩

/-- ✱173·25. \[\begin{align}&\vdash :P\in \text{Rel}^{2}\text{excl}.Z{\sim}\in CʻP.CʻZ\cap Cʻ\Sigma ʻP=\Lambda.\supset .\\ &\text{Prod}ʻ(P\unicode{x21f8} Z)\,\text{smor}\,(\text{Prod}ʻP\times Z).\text{Prod}ʻ(Z\unicode{x21f7}P)\,\text{smor}\,(Z\times \text{Prod}ʻP)\end{align}\] -/
theorem pm173_25 {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    (h : (P ∈ Rel2excl ∧ Z ∉ fld P) ∧ fld Z ∩ fld (relSigma P) = Λ) :
    smor (prodR (P ⇸ Z)) (prodR P ×ᵣ Z) ∧ smor (prodR (Z ⇷ P)) (Z ×ᵣ prodR P) := by
  obtain ⟨⟨hP, hZ⟩, hd⟩ := h
  have hPi := smor_symm (pm173_16 hP).1
  have h1 : P ⇸ Z ∈ Rel2excl := pm173_aux_excl_add hP hd (pm173_aux_fld_addLast_sub Z P)
  have h2 : Z ⇷ P ∈ Rel2excl := pm173_aux_excl_add hP hd fun R hR => by
    rcases pm170_aux_fld_addFirst_sub Z P hR with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'
  exact ⟨smor_trans (pm173_16 h1).1 (smor_trans (pm172_32 hZ)
      (pm172_aux_smor_rtimes hPi (smor_refl Z))),
    smor_trans (pm173_16 h2).1 (smor_trans (pm172_321 hZ)
      (pm172_aux_smor_rtimes (smor_refl Z) hPi))⟩

/-- ✱173·26. \[\begin{align}\vdash :P,Q\in \text{Rel}^{2}\text{excl}.\dot{\exists} !P.\dot{\exists} !Q.&CʻP\cap CʻQ=\Lambda.Cʻ\Sigma ʻP\cap Cʻ\Sigma ʻQ=\Lambda.\supset .\\ &\text{Prod}ʻ(P\unicode{x2909}Q)\text{smor}\text{Prod}ʻP\times \text{Prod}ʻQ\end{align}\] -/
theorem pm173_26 {P Q : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : ((((P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ rEx P) ∧ rEx Q) ∧ fld P ∩ fld Q = Λ) ∧
      fld (relSigma P) ∩ fld (relSigma Q) = Λ) :
    smor (prodR (P ⤉ Q)) (prodR P ×ᵣ prodR Q) := by
  obtain ⟨⟨⟨⟨⟨hP, hQ⟩, hP'⟩, hQ'⟩, hd⟩, hs⟩ := h
  have hPQ : P ⤉ Q ∈ Rel2excl := by
    have cross : ∀ R1 R2, R1 ∈ fld P → R2 ∈ fld Q → fld R1 ∩ fld R2 = Λ := fun R1 R2 h1 h2 =>
      pm172_aux_inter_Null.2 fun x hx1 hx2 => pm172_aux_inter_Null.1 hs x
        (pm172_aux_mem_fld_relSigma h1 hx1) (pm172_aux_mem_fld_relSigma h2 hx2)
    rintro R1 R2 ⟨⟨h1, h2⟩, hne⟩
    rw [fld_rsum] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hP R1 R2 ⟨⟨h1, h2⟩, hne⟩
    · exact cross R1 R2 h1 h2
    · rw [Set.inter_comm]; exact cross R2 R1 h2 h1
    · exact hQ R1 R2 ⟨⟨h1, h2⟩, hne⟩
  exact smor_trans (pm173_16 hPQ).1 (smor_trans (pm172_35 ⟨⟨hP', hQ'⟩, hd⟩)
    (pm172_aux_smor_rtimes (smor_symm (pm173_16 hP).1) (smor_symm (pm173_16 hQ).1)))

/-- ✱173·27. \[\begin{align}\vdash :CʻP\cap &CʻQ=\Lambda.CʻP\cap CʻR=\Lambda.CʻQ\cap CʻR=\Lambda.\supset .\\ &\text{Prod}ʻ\{(P\downarrow Q)\unicode{x21f8} R\}\,\text{smor}\,P\times Q\times R\end{align}\] -/
theorem pm173_27 {P Q R : α → α → Prop}
    (h : (fld P ∩ fld Q = Λ ∧ fld P ∩ fld R = Λ) ∧ fld Q ∩ fld R = Λ) :
    smor (prodR ((P ↓ Q) ⇸ R)) (P ×ᵣ Q ×ᵣ R) := by
  obtain ⟨⟨hPQ, hPR⟩, hQR⟩ := h
  have hsub : fld ((P ↓ Q) ⇸ R) ⊆ (ι P ∪ ι Q) ∪ ι R := by
    intro X hX
    rcases pm173_aux_fld_addLast_sub R (P ↓ Q) hX with h' | h'
    · rw [pm170_aux_fld_couple] at h'; exact Or.inl h'
    · exact Or.inr h'
  have hex : (P ↓ Q) ⇸ R ∈ Rel2excl := by
    rintro X Y ⟨⟨hX, hY⟩, hne⟩
    rcases hsub hX with (e1 | e1) | e1 <;> rcases hsub hY with (e2 | e2) | e2 <;>
      rw [pm170_aux_mem_iota] at e1 e2 <;> subst e1 e2
    all_goals first
      | exact absurd rfl hne
      | assumption
      | rwa [Set.inter_comm]
  refine smor_trans (pm173_16 hex).1 ?_
  by_cases hdist : (P ≠ Q ∧ P ≠ R) ∧ Q ≠ R
  · exact pm172_36 hdist
  · have hempty : fld P = ∅ ∨ fld Q = ∅ := by
      have e : ∀ X : α → α → Prop, fld X ∩ fld X = Λ → fld X = ∅ := fun X h' => by
        rw [Set.inter_self, pm170_aux_Null_eq] at h'; exact h'
      by_cases e1 : P = Q
      · subst e1; exact Or.inl (e P hPQ)
      by_cases e2 : P = R
      · subst e2; exact Or.inl (e P hPR)
      by_cases e3 : Q = R
      · subst e3; exact Or.inr (e Q hQR)
      exact absurd ⟨⟨e1, e2⟩, e3⟩ hdist
    apply pm172_aux_smor_empty
    · rcases hempty with h' | h'
      · exact pm173_aux_relPi_empty (S := P) ⟨Q, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩ h'
      · exact pm173_aux_relPi_empty (S := Q) ⟨P, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩ h'
    · apply pm172_aux_rtimes_empty
      left
      exact Set.eq_empty_iff_forall_notMem.2 fun U ⟨V, hUV⟩ => by
        rcases hUV with hUV | hUV <;> exact pm172_aux_rtimes_empty hempty _ _ hUV

/-- ✱173·3. \[\begin{align}\vdash :T\upharpoonright Cʻ\Sigma ʻQ\in P\,\overline{\text{smor smor}}\, &Q.\supset .\\ &T\in \upharpoonright Cʻ\text{Prod}ʻQ\in (\text{Prod}ʻP)\,\overline{\text{smor}}\,(\text{Prod}ʻQ)\end{align}\]

The e-text prints `T ∈ ↾ C'Prod'Q` for `T_∈ ↾ C'Prod'Q` (the subscript is lost; PM's
demonstration, step (4), has `T_∈ ↾ C'Prod'Q`), read `imgRel T ↾ fld (prodR Q)`.

**Status.** proved (reading): transcription error (the lost subscript of `T_∈`, see above). -/
theorem pm173_3 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop}
    (h : T ↾ fld (relSigma Q) ∈ smorsmorbar P Q) :
    imgRel T ↾ fld (prodR Q) ∈ smorbar (prodR P) (prodR Q) := by
  have hW := pm172_43 h
  obtain ⟨⟨-, h2⟩, hc, -⟩ := pm172_aux_ss h
  -- every member of a class in `C'Prod'Q` is in `C'Σ'Q` and has a `T`-referent there
  have hB : ∀ B, B ∈ fld (prodR Q) → ∀ y, y ∈ B →
      y ∈ fld (relSigma Q) ∧ ∃ x, (T ↾ fld (relSigma Q)) x y := by
    intro B hB y hy
    obtain ⟨N, hN, hBN⟩ := pm173_12 Q hB
    rw [show B = dom N from hBN] at hy
    obtain ⟨S, hyS⟩ := hy
    have hS := pm172_aux_sel_mem hN hyS
    exact ⟨pm172_aux_mem_fld_relSigma hS (pm172_aux_sel_sub hN hyS),
      hc S hS (pm172_aux_sel_sub hN hyS)⟩
  have hinj : ∀ B B', B ∈ fld (prodR Q) → B' ∈ fld (prodR Q) → T ʻʻ B = T ʻʻ B' → B ⊆ B' := by
    intro B B' hB1 hB1' e y hy
    obtain ⟨-, x, hxy, -⟩ := hB B hB1 y hy
    have : x ∈ T ʻʻ B' := by rw [← e]; exact ⟨y, hy, hxy⟩
    obtain ⟨y', hy', hxy'⟩ := this
    have := h2 x y y' ⟨⟨hxy, (hB B hB1 y hy).1⟩, ⟨hxy', (hB B' hB1' y' hy').1⟩⟩
    rw [this]; exact hy'
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro A A' B ⟨⟨h1, -⟩, ⟨h1', -⟩⟩
    exact (show A = T ʻʻ B from h1).trans (show A' = T ʻʻ B from h1').symm
  · rintro A B B' ⟨⟨h1, hB1⟩, ⟨h1', hB1'⟩⟩
    have e : T ʻʻ B = T ʻʻ B' := (show A = T ʻʻ B from h1).symm.trans h1'
    exact Set.Subset.antisymm (hinj B B' hB1 hB1' e) (hinj B' B hB1' hB1 e.symm)
  · ext B; constructor
    · intro hB1; exact ⟨T ʻʻ B, rfl, hB1⟩
    · rintro ⟨_, -, hB1⟩; exact hB1
  · funext μ ν; apply propext
    rw [pm173_11, semi_apply]
    constructor
    · rintro ⟨M, N, ⟨hMN, rfl⟩, rfl⟩
      rw [hW.2, semi_apply] at hMN
      obtain ⟨N1, N2, ⟨⟨hM1, hN1⟩, ⟨hM2, hN2⟩⟩, hQ⟩ := hMN
      rw [pm172_aux_dpar_tr] at hM1 hM2
      subst hM1 hM2
      have hpr : prodR Q (dom N1) (dom N2) := pm173_11.2 ⟨N1, N2, ⟨hQ, rfl⟩, rfl⟩
      exact ⟨dom N1, dom N2, ⟨⟨pm173_aux_dom_tr T N1, ⟨_, Or.inl hpr⟩⟩,
        ⟨pm173_aux_dom_tr T N2, ⟨_, Or.inr hpr⟩⟩⟩, hpr⟩
    · rintro ⟨B, B', ⟨⟨hμ, -⟩, ⟨hν, -⟩⟩, hpr⟩
      obtain ⟨N1, N2, ⟨hQ, rfl⟩, rfl⟩ := pm173_11.1 hpr
      refine ⟨_, _, ⟨?_, (show μ = T ʻʻ dom N1 from hμ).trans (pm173_aux_dom_tr T N1).symm⟩,
        (show ν = T ʻʻ dom N2 from hν).trans (pm173_aux_dom_tr T N2).symm⟩
      rw [hW.2, semi_apply]
      exact ⟨N1, N2, ⟨⟨(pm172_aux_dpar_tr _ _ _).2 rfl, N2, Or.inl hQ⟩,
        ⟨(pm172_aux_dpar_tr _ _ _).2 rfl, N1, Or.inr hQ⟩⟩, hQ⟩

/-- ✱173·31. \(\vdash :P\,\text{smor smor}\,Q.\supset .\text{Prod}ʻP\,\text{smor}\,\text{Prod}ʻQ \quad[*173·3]\) -/
theorem pm173_31 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} (h : smorsmor P Q) :
    smor (prodR P) (prodR Q) := by
  obtain ⟨T, hT⟩ := h
  have e : T ↾ fld (relSigma Q) = T := by
    funext x y; apply propext
    refine ⟨fun h' => h'.1, fun h' => ⟨h', ?_⟩⟩
    rw [show fld (relSigma Q) = codom T from hT.1.2]; exact ⟨x, h'⟩
  exact ⟨_, pm173_3 (by rw [e]; exact hT)⟩

/-- ✱173·32. \(\vdash :R\upharpoonright Cʻ\Sigma ʻQ\in 1\rightarrow 1.Cʻ\Sigma ʻQ\subset \text{ᗡ}ʻR.\supset .\text{Prod}ʻR\dagger ^{;}Q=R_\in ^{;}\text{Prod}ʻQ\) -/
theorem pm173_32 {Q : (β → β → Prop) → (β → β → Prop) → Prop} {R : α → β → Prop}
    (h : R ↾ fld (relSigma Q) ∈ arrow one one ∧ fld (relSigma Q) ⊆ codom R) :
    prodR (daggerRel R ⁏ Q) = imgRel R ⁏ prodR Q := by
  obtain ⟨hR, hsub⟩ := h
  have hyp : R ↾ fld (relSigma Q) ∈ smorsmorbar (daggerRel R ⁏ Q) Q := by
    refine ⟨⟨hR, ?_⟩, ?_⟩
    · show fld (relSigma Q) = codom (R ↾ fld (relSigma Q))
      ext y; constructor
      · intro hy; obtain ⟨x, hx⟩ := hsub hy; exact ⟨x, hx, hy⟩
      · rintro ⟨x, -, hy⟩; exact hy
    · show daggerRel R ⁏ Q = daggerRel (R ↾ fld (relSigma Q)) ⁏ Q
      apply pm173_aux_semi_congr
      intro X S hS
      show X = daggerOp R S ↔ X = daggerOp (R ↾ fld (relSigma Q)) S
      rw [pm172_aux_dagger_cres fun z hz => pm172_aux_mem_fld_relSigma hS hz]
  rw [(pm173_3 hyp).2, ← pm170_aux_semi_cres]

/-- ✱173·33. \(\vdash :\text{D}\upharpoonright Cʻ\Sigma ʻQ\in 1\rightarrow 1.\supset .\text{Prod}ʻ\text{D}\dagger ^{;}Q=\text{D}_{\in }^{;}\text{Prod}ʻQ \quad\left[*173·32 \frac{\text{D}}{R}\right].\) -/
theorem pm173_33 {Q : ((α → β → Prop) → (α → β → Prop) → Prop) →
    ((α → β → Prop) → (α → β → Prop) → Prop) → Prop}
    (h : (D : Set α → (α → β → Prop) → Prop) ↾ fld (relSigma Q) ∈ arrow one one) :
    prodR (daggerRel D ⁏ Q) = imgRel D ⁏ prodR Q :=
  pm173_32 ⟨h, fun R _ => ⟨dom R, rfl⟩⟩

/-!
## [✱174] The associative law of relational multiplication

*(Vol. 2, p. 447)*

> *Summary of* *174.
>
> In the present number, we have to prove the associative law for \(\Pi\) and for \(\text{Prod}\), *i.e.* we have to prove (with a suitable hypothesis) \[ \Pi ʻ\Pi ^{;}P\text{smor}\Pi ʻ\Sigma ʻP \] and \(\text{Prod}ʻ\text{Prod}^{;}P\text{smor}\text{Prod}ʻ\Sigma ʻP\).
>
> The first of these requires \(P\in \text{Rel}^{2}\text{excl}\) and either \(P\,\unicode{x2abd}\, J\) or \[ QPQ.\supset _{Q}.CʻQ\in 0\cup 1; \] the second requires not only this, but also \(\Sigma ʻP\in\text{Rel}^{2}\text{excl}\). When both \(P\) and \(\SigmaʻP\) are relations of mutually exclusive relations, we call \(P\) an *arithmetical* relation, which we denote by "\(\text{Rel}^{3}\text{arithm}\)." Arithmetical relations serve exactly analogous purposes to those served by arithmetical classes in cardinal arithmetic.
>
> The proof of the associative law for \(\Pi\) consists in showing that, under a suitable hypothesis, \(\dot{s} \mid \text{D}\) (with its converse domain limited) is a correlator of \(\Pi ʻ\Sigma ʻP\) and \(\Pi ʻ\Pi ^{;}P\) (*174·221·23). To prove this, we first prove
>
> *174·17. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\dot{s}ʻʻ\text{D}ʻʻCʻ\Pi ʻ\Pi ^{;}P=Cʻ\Pi ʻ\Sigma ʻP\)
>
> and
>
> …

**Lean reading.** `Rel³ arithm` is `Rel3arithm`; `Π;P`, `Σ;P`, `Prod;P` are `RelPi ⁏ P`,
`RelSigma ⁏ P`, `ProdR ⁏ P`; `Π''C'P` is `RelPi ʻʻ fld P`, `F_Δ''C''C'P` is
`selRel F ʻʻ (C ʻʻ fld P)`, `D_∈` is `imgRel D`, `C'''C''C'P` is `C ʻʻʻ (C ʻʻ fld P)`,
`C'Q ∈ 0 ∪ 1` is `fld Q ∈ zero ∪ one`. In ✱174·2·21·211·212 the descriptions `M'Π'Q`,
`(M'Π'Q)'S` are kept, the first with the larger scope. ✱174·213 is stated as printed, its first
premiss quantified over `Q, R, S, T` and its conclusion about the real variables. The
relation-numbers of ✱174·48 are taken in one type `γ`. The associative law itself
(✱174·161–·25, ✱174·4–·48) is not carried out here.

**Status.** stated (open here) (in part; the propositions not listed are proved): ✱174·01
definition; ✱174·161·162·17·18·19·191·2·21·211·212·215·22·221·23·231·24·241·25,
✱174·33·34·363 and ✱174·4·401·41·42·43·44·45·46·461·462·47·48 stated (open here).
-/

section Helpers174
variable {α : Type u}

theorem pm174_aux_inter_Null {A B : Set α} : A ∩ B = Λ ↔ ∀ x, x ∈ A → x ∈ B → False := by
  rw [pm170_aux_Null_eq, Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h x ha hb => h x ⟨ha, hb⟩, fun h x hx => h x hx.1 hx.2⟩

theorem pm174_aux_excl_iff {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ↔ F ↾ fld P ∈ arrow Cls one := by
  rw [mem_Rel2excl, mem_arrow_Cls_one]
  constructor
  · rintro h x Q Q' ⟨⟨hx, hQ⟩, ⟨hx', hQ'⟩⟩
    by_contra hne
    exact pm174_aux_inter_Null.1 (h Q Q' ⟨⟨hQ, hQ'⟩, hne⟩) x hx hx'
  · intro h Q Q' ⟨⟨hQ, hQ'⟩, hne⟩
    exact pm174_aux_inter_Null.2 fun x hx hx' => hne (h x Q Q' ⟨⟨hx, hQ⟩, ⟨hx', hQ'⟩⟩)

end Helpers174

/-- ✱174·01 (Df). \(\text{Rel}^{3}\text{arithm}=\hat{P} (P,\Sigma ʻP\in \text{Rel}^{2}\text{excl}) \quad\text{Df}\) -/
theorem pm174_01 :
    (Rel3arithm : Set (((α → α → Prop) → (α → α → Prop) → Prop) →
      ((α → α → Prop) → (α → α → Prop) → Prop) → Prop)) =
    {P | P ∈ Rel2excl ∧ relSigma P ∈ Rel2excl} := rfl

/-- ✱174·12. \(\vdash :C\upharpoonright CʻP\in 1\rightarrow 1.\supset .\Pi ^{;}P\in \text{Rel}^{2}\text{excl}\) -/
theorem pm174_12 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} (h : C ↾ fld P ∈ arrow one one) :
    RelPi ⁏ P ∈ Rel2excl := by
  obtain ⟨-, h2⟩ := mem_arrow_one_one.1 h
  intro X Y ⟨⟨hX, hY⟩, hne⟩
  rw [show (RelPi : _ → ((α → α → Prop) → (α → α → Prop) → Prop) → Prop) = graph relPi from rfl,
    fld_semi_graph] at hX hY
  obtain ⟨Q, hQ, rfl⟩ := hX
  obtain ⟨Q', hQ', rfl⟩ := hY
  have hQQ : fld Q ≠ fld Q' := fun e => hne (by rw [h2 (fld Q) Q Q' ⟨⟨rfl, hQ⟩, ⟨e, hQ'⟩⟩])
  refine pm174_aux_inter_Null.2 fun M hM hM' => hQQ ?_
  exact ((mem_sel_iff.1 (pm172_12 Q hM)).2).symm.trans (mem_sel_iff.1 (pm172_12 Q' hM')).2

/-- ✱174·13. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\Pi ^{;}P\in \text{Rel}^{2}\text{excl} \quad[*174·12.*163·14]\) -/
theorem pm174_13 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} (h : P ∈ Rel2excl) :
    RelPi ⁏ P ∈ Rel2excl := pm174_12 (pm173_aux_C_one_one h)

/-- ✱174·16. \(\vdash :\dot{\exists} !P.\supset .Cʻ\Pi ʻ\Pi ^{;}P=F_{\Delta }ʻ\Pi ʻʻCʻP\) -/
theorem pm174_16 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} (h : rEx P) :
    fld (relPi (RelPi ⁏ P)) = sel F (RelPi ʻʻ fld P) := by
  have hR : rEx (RelPi ⁏ P) := (pm173_aux_rEx_semi_graph relPi P).2 h
  rw [pm172_17 hR]
  exact congrArg _ (fld_semi_graph relPi P)

/-- ✱174·161. \[\begin{align}\vdash :\dot{\exists} !P.P\in &\text{Rel}^{2}\text{excl}.\supset .\\ &Cʻ\text{Prod}ʻ\Pi ^{;}P= \text{D}ʻʻCʻ\Pi ʻ\Pi ^{;}P=\text{Prod}ʻF_{\Delta }ʻʻCʻʻCʻP\end{align}\]

**Status.** stated (open here): the associative law of ✱174 (selections from `Π''C'P` and from
`C'Σ'P`) is not carried out here. -/
def pm174_161 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    rEx P ∧ P ∈ Rel2excl →
    fld (prodR (RelPi ⁏ P)) = D ʻʻ fld (relPi (RelPi ⁏ P)) ∧
      D ʻʻ fld (relPi (RelPi ⁏ P)) = prodK (selRel F ʻʻ (C ʻʻ fld P))

/-- ✱174·162. \(\vdash :\dot{\exists} !P.P\in \text{Rel}^{2}\text{excl}.\supset .\dot{s}ʻʻ\text{D}ʻʻCʻ\Pi ʻ\Pi ^{;}P=Cʻ\Pi ʻ\Sigma ʻP=F_{\Delta }ʻCʻ\Sigma ʻP\)

**Status.** stated (open here): as ✱174·161. -/
def pm174_162 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    rEx P ∧ P ∈ Rel2excl →
    sDotRel ʻʻ (D ʻʻ fld (relPi (RelPi ⁏ P))) = fld (relPi (relSigma P)) ∧
      fld (relPi (relSigma P)) = sel F (fld (relSigma P))

/-- ✱174·17. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\dot{s}ʻʻ\text{D}ʻʻCʻ\Pi ʻ\Pi ^{;}P=Cʻ\Pi ʻ\Sigma ʻP\)

**Status.** stated (open here): as ✱174·161. -/
def pm174_17 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel2excl → sDotRel ʻʻ (D ʻʻ fld (relPi (RelPi ⁏ P))) = fld (relPi (relSigma P))

/-- ✱174·18. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\text{D}\upharpoonright Cʻ\Pi ʻ\Pi ^{;}P\in 1\rightarrow 1\)

**Status.** stated (open here): as ✱174·161. -/
def pm174_18 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel2excl → D ↾ fld (relPi (RelPi ⁏ P)) ∈ arrow one one

/-- ✱174·19. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .(\dot{s} \mid \text{D})\upharpoonright Cʻ\Pi ʻ\Pi ^{;}P\in 1\rightarrow 1\)

**Status.** stated (open here): as ✱174·161. -/
def pm174_19 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel2excl → (sDotRel ⨾ D) ↾ fld (relPi (RelPi ⁏ P)) ∈ arrow one one

/-- ✱174·191. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\dot{s} \upharpoonright Cʻ\text{Prod}ʻ\Pi ^{;}P\in 1\rightarrow 1\)

**Status.** stated (open here): as ✱174·161. -/
def pm174_191 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel2excl → sDotRel ↾ fld (prodR (RelPi ⁏ P)) ∈ arrow one one

/-- ✱174·2. \(\vdash :P\in \text{Rel}^{2}\text{excl}.Q\in CʻP.M\in Cʻ\Pi ʻ\Pi ^{;}P.\supset .Mʻ\Pi ʻQ=(\dot{s} ʻ\text{D}ʻM)\upharpoonright CʻQ\)

**Status.** stated (open here): as ✱174·161. -/
def pm174_2 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop)
    (Q : (α → α → Prop) → (α → α → Prop) → Prop)
    (M : (α → (α → α → Prop) → Prop) →
      ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) → Prop),
    (P ∈ Rel2excl ∧ Q ∈ fld P) ∧ M ∈ fld (relPi (RelPi ⁏ P)) →
    Desc M (relPi Q) (fun X => X = sumRel (dom M) ↾ fld Q)

/-- ✱174·21. \[\begin{align}\vdash \colon\colon P\in \text{Rel}^{2}\text{excl}.Q\in CʻP.&M,N\in Cʻ\Pi ʻ\Pi ^{;}P.\supset \colon\ldotp \\ &Mʻ\Pi ʻQ=Nʻ\Pi ʻQ.\equiv :R\in CʻQ.\supset _{R}.(\dot{s} ʻ\text{D}ʻM)ʻR=(\dot{s} ʻ\text{D}ʻN)ʻR\end{align}\]

**Status.** stated (open here): as ✱174·161. -/
def pm174_21 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop)
    (Q : (α → α → Prop) → (α → α → Prop) → Prop)
    (M N : (α → (α → α → Prop) → Prop) →
      ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) → Prop),
    (P ∈ Rel2excl ∧ Q ∈ fld P) ∧ (M ∈ fld (relPi (RelPi ⁏ P)) ∧ N ∈ fld (relPi (RelPi ⁏ P))) →
    (Desc M (relPi Q) (fun X => Desc N (relPi Q) (fun Y => X = Y)) ↔
      ∀ R, R ∈ fld Q → Desc (sumRel (dom M)) R (fun a => Desc (sumRel (dom N)) R (fun b => a = b)))

/-- ✱174·211. \[\begin{align}&\vdash \colon\colon\ldotp P\in \text{Rel}^{2}\text{excl}.\supset \colon\colon M(\Pi ʻ\Pi ^{;}P)N.\equiv \colon\ldotp \\ &M,N\in F_{\Delta }ʻ\Pi ʻʻCʻP\colon\ldotp (\exists Q,S):Q\in CʻP.S\in CʻQ.{(Mʻ\Pi ʻQ)ʻS}S{(Nʻ\Pi ʻQ)ʻS}:\\ &TQS.T\neq S.\supset _{T}.(Mʻ\Pi ʻQ)ʻT=(Nʻ\Pi ʻQ)ʻT:\\ &RPQ.R\neq Q.T\in CʻR.\supset _{R,T}.(Mʻ\Pi ʻR)ʻT=(Nʻ\Pi ʻR)ʻT\end{align}\]

**Status.** stated (open here): as ✱174·161. Of two descriptions the first has the larger scope. -/
def pm174_211 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop)
    (M N : (α → (α → α → Prop) → Prop) →
      ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) → Prop),
    P ∈ Rel2excl →
    (relPi (RelPi ⁏ P) M N ↔ (M ∈ sel F (RelPi ʻʻ fld P) ∧ N ∈ sel F (RelPi ʻʻ fld P)) ∧
      ∃ Q S, (((Q ∈ fld P ∧ S ∈ fld Q) ∧
        Desc M (relPi Q) (fun X => Desc X S (fun a => Desc N (relPi Q) (fun Y =>
          Desc Y S (fun b => S a b))))) ∧
        ∀ T, Q T S ∧ T ≠ S → Desc M (relPi Q) (fun X => Desc X T (fun a =>
          Desc N (relPi Q) (fun Y => Desc Y T (fun b => a = b))))) ∧
        ∀ R T, (P R Q ∧ R ≠ Q) ∧ T ∈ fld R → Desc M (relPi R) (fun X => Desc X T (fun a =>
          Desc N (relPi R) (fun Y => Desc Y T (fun b => a = b)))))

/-- ✱174·212. \[\begin{align}&\vdash \colon\colon\ldotp P\in \text{Rel}^{2}\text{excl}.\supset \colon\colon M(\Pi ʻ\Pi ^{;}P)N.\equiv \colon\ldotp \\ &M,N\in F_{\Delta }ʻ\Pi ʻʻCʻP\colon\ldotp (\exists Q, S):Q\in CʻP.S\in CʻQ.{(\dot{s} ʻ\text{D}ʻM)ʻS}S\{(\dot{s} ʻ\text{D}ʻN)ʻS\}:\\ &TQS.T\neq S.\supset _{T}.(\dot{s} ʻ\text{D}ʻM)ʻT=(\dot{s} ʻ\text{D}ʻN)ʻT:\\ &RPQ.R\neq Q.T\in CʻR.\supset _{R,T}.(\dot{s} ʻ\text{D}ʻM)ʻT=(\dot{s} ʻ\text{D}ʻN)ʻT\\ &[*174·2·211.*35·7]\end{align}\]

**Status.** stated (open here): as ✱174·161. -/
def pm174_212 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop)
    (M N : (α → (α → α → Prop) → Prop) →
      ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) → Prop),
    P ∈ Rel2excl →
    (relPi (RelPi ⁏ P) M N ↔ (M ∈ sel F (RelPi ʻʻ fld P) ∧ N ∈ sel F (RelPi ʻʻ fld P)) ∧
      ∃ Q S, (((Q ∈ fld P ∧ S ∈ fld Q) ∧
        Desc (sumRel (dom M)) S (fun a => Desc (sumRel (dom N)) S (fun b => S a b))) ∧
        ∀ T, Q T S ∧ T ≠ S →
          Desc (sumRel (dom M)) T (fun a => Desc (sumRel (dom N)) T (fun b => a = b))) ∧
        ∀ R T, (P R Q ∧ R ≠ Q) ∧ T ∈ fld R →
          Desc (sumRel (dom M)) T (fun a => Desc (sumRel (dom N)) T (fun b => a = b)))

/-- ✱174·213. \[\begin{align}\vdash \colon\ldotp &RPQ.S\in CʻQ.T\in CʻR.S\neq T.\supset _{Q,R,S,T}.R\neq Q:P\in \text{Rel}^{2}\text{excl}:\supset :\\ &RPQ.S\in CʻQ.T\in CʻR.R\neq Q.\equiv .RPQ.S\in CʻQ.T\in CʻR.S\neq T\end{align}\] -/
theorem pm174_213 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} {Q R : (α → α → Prop) → (α → α → Prop) → Prop}
    {S T : α → α → Prop}
    (h : (∀ Q' R' S' T', ((P R' Q' ∧ S' ∈ fld Q') ∧ T' ∈ fld R') ∧ S' ≠ T' → R' ≠ Q') ∧
      P ∈ Rel2excl) :
    (((P R Q ∧ S ∈ fld Q) ∧ T ∈ fld R) ∧ R ≠ Q) ↔ (((P R Q ∧ S ∈ fld Q) ∧ T ∈ fld R) ∧ S ≠ T) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · rintro ⟨⟨⟨hRQ, hS⟩, hT⟩, hne⟩
    refine ⟨⟨⟨hRQ, hS⟩, hT⟩, fun e => ?_⟩
    have h0 := pm174_aux_inter_Null.1 (h2 R Q ⟨⟨⟨Q, Or.inl hRQ⟩, ⟨R, Or.inr hRQ⟩⟩, hne⟩)
    exact h0 S (e ▸ hT) hS
  · rintro ⟨⟨⟨hRQ, hS⟩, hT⟩, hne⟩
    exact ⟨⟨⟨hRQ, hS⟩, hT⟩, h1 Q R S T ⟨⟨⟨hRQ, hS⟩, hT⟩, hne⟩⟩

/-- ✱174·214. \[\begin{align}&\vdash \colon\colon P\in \text{Rel}^{2}\text{excl}:QPQ.\supset _{Q}.CʻQ\in 0\cup 1:\supset \colon\ldotp \\ &(\exists Q):Q\in CʻP:TQS.T\neq S.\lor.(\exists R).RPQ.R\neq Q.S\in CʻQ.T\in CʻR:\equiv .\\ &T(\Sigma ʻP)S.T\neq S\end{align}\] -/
theorem pm174_214 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} {S T : α → α → Prop}
    (h : P ∈ Rel2excl ∧ ∀ Q, P Q Q → fld Q ∈ (zero ∪ one : Set (Set (α → α → Prop)))) :
    (∃ Q, Q ∈ fld P ∧ ((Q T S ∧ T ≠ S) ∨ ∃ R, ((P R Q ∧ R ≠ Q) ∧ S ∈ fld Q) ∧ T ∈ fld R)) ↔
      (relSigma P T S ∧ T ≠ S) := by
  obtain ⟨hex, h2⟩ := h
  constructor
  · rintro ⟨Q, hQ, ⟨hq, hne⟩ | ⟨R, ⟨⟨hRQ, hRne⟩, hS⟩, hT⟩⟩
    · exact ⟨(relSigma_apply P T S).2 (Or.inl ⟨Q, hQ, hq⟩), hne⟩
    · refine ⟨(relSigma_apply P T S).2 (Or.inr ⟨R, Q, ⟨hT, hS⟩, hRQ⟩), fun e => ?_⟩
      have h0 := pm174_aux_inter_Null.1 (hex R Q ⟨⟨⟨Q, Or.inl hRQ⟩, hQ⟩, hRne⟩)
      exact h0 T hT (by rw [e]; exact hS)
  · rintro ⟨hSig, hne⟩
    rcases (relSigma_apply P T S).1 hSig with ⟨Q, hQ, hq⟩ | ⟨R, Q, ⟨hT, hS⟩, hRQ⟩
    · exact ⟨Q, hQ, Or.inl ⟨hq, hne⟩⟩
    · by_cases hRQ' : R = Q
      · subst hRQ'
        exfalso
        rcases h2 R hRQ with h0 | h1
        · have : fld R = Λ := h0
          rw [this] at hT; exact pm170_aux_Null T hT
        · obtain ⟨x, hx⟩ := mem_one_iff.1 h1
          exact hne (((hx T).1 hT).trans ((hx S).1 hS).symm)
      · exact ⟨Q, ⟨R, Or.inr hRQ⟩, Or.inr ⟨R, ⟨⟨hRQ, hRQ'⟩, hS⟩, hT⟩⟩

/-- ✱174·215. \[\begin{align}\vdash \colon\ldotp &P\in \text{Rel}^{2}\text{excl}:QPQ.\supset _{Q}.CʻQ\in 0\cup 1:\supset :\\ &M(\Pi ʻ\Pi ^{;}P)N.\equiv .\mu ,N\in F_{\Delta }ʻ\Pi ʻʻCʻP.(\dot{s} ʻ\text{D}ʻM )(\Pi ʻ\Sigma ʻP )(\dot{s} ʻ\text{D}ʻN)\end{align}\]

**Status.** stated (open here): as ✱174·161. Reading: the e-text prints `μ, N` for `M, N`. -/
def pm174_215 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop)
    (M N : (α → (α → α → Prop) → Prop) →
      ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) → Prop),
    P ∈ Rel2excl ∧ (∀ Q, P Q Q → fld Q ∈ (zero ∪ one : Set (Set (α → α → Prop)))) →
    (relPi (RelPi ⁏ P) M N ↔ (M ∈ sel F (RelPi ʻʻ fld P) ∧ N ∈ sel F (RelPi ʻʻ fld P)) ∧
      relPi (relSigma P) (sumRel (dom M)) (sumRel (dom N)))

/-- ✱174·216. \(\vdash \colon\ldotp P\,\unicode{x2abd}\, J.\supset :QPQ.\supset _{Q}.CʻQ\in 0\cup 1\) -/
theorem pm174_216 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} (h : P ⪽ J) :
    ∀ Q, P Q Q → fld Q ∈ (zero ∪ one : Set (Set (α → α → Prop))) :=
  fun Q hQ => absurd rfl (h Q Q hQ)

/-- ✱174·22. \[\begin{align}\vdash \colon\ldotp &P\in \text{Rel}^{2}\text{excl}.P\,\unicode{x2abd}\, J.\supset :\\ &M(\Pi ʻ\Pi ^{;}P)N.\equiv .M,N\in F_{\Delta }ʻ\Pi ʻʻCʻP.(\dot{s} ʻ\text{D}ʻM)(\Pi ʻ\Sigma ʻP)(\dot{s} ʻ\text{D}ʻN)\\ &[*174·215·216]\end{align}\]

**Status.** stated (open here): depends on ✱174·215. -/
def pm174_22 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop)
    (M N : (α → (α → α → Prop) → Prop) →
      ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) → Prop),
    P ∈ Rel2excl ∧ P ⪽ J →
    (relPi (RelPi ⁏ P) M N ↔ (M ∈ sel F (RelPi ʻʻ fld P) ∧ N ∈ sel F (RelPi ʻʻ fld P)) ∧
      relPi (relSigma P) (sumRel (dom M)) (sumRel (dom N)))

/-- ✱174·221. \[\begin{align}\vdash \colon\ldotp &P\in \text{Rel}^{2}\text{excl}:QPQ.\supset _{Q}.CʻQ\in 0\cup 1:\supset .\\ &\Pi ʻ\Sigma ʻP=\dot{s} ^{;}\text{D}^{;}\Pi ʻ\Pi ^{;}P .(\dot{s} \mid \text{D})\upharpoonright Cʻ\Pi ʻ\Pi ^{;}P \in (\Pi ʻ\Sigma ʻP )\,\overline{\text{smor}}\,(\Pi ʻ\Pi ^{;}P )\end{align}\]

**Status.** stated (open here): depends on ✱174·215. -/
def pm174_221 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel2excl ∧ (∀ Q, P Q Q → fld Q ∈ (zero ∪ one : Set (Set (α → α → Prop)))) →
    relPi (relSigma P) = sDotRel ⁏ D ⁏ relPi (RelPi ⁏ P) ∧
      (sDotRel ⨾ D) ↾ fld (relPi (RelPi ⁏ P)) ∈ smorbar (relPi (relSigma P)) (relPi (RelPi ⁏ P))

/-- ✱174·23. \[\begin{align}\vdash :P\in &\text{Rel}^{2}\text{excl}.P\,\unicode{x2abd}\, J.\supset .\Pi ʻSʻP=\dot{s} ^{;}\text{D}^{;}\Pi ʻ\Pi ^{;}P.\\ &(\dot{s} \mid \text{D})\upharpoonright Cʻ\Pi ʻ\Pi ^{;}P\in (\Pi ʻ\Sigma ʻP)\,\overline{\text{smor}}\,(\Pi ʻ\Pi ^{;}P) \quad[*174·221·216]\end{align}\]

**Status.** stated (open here): depends on ✱174·221. Reading: the e-text prints `Π'S'P` for `Π'Σ'P`. -/
def pm174_23 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel2excl ∧ P ⪽ J →
    relPi (relSigma P) = sDotRel ⁏ D ⁏ relPi (RelPi ⁏ P) ∧
      (sDotRel ⨾ D) ↾ fld (relPi (RelPi ⁏ P)) ∈ smorbar (relPi (relSigma P)) (relPi (RelPi ⁏ P))

/-- ✱174·231. \[\begin{align}\vdash :P\in &\text{Rel}^{2}\text{excl}:QPQ.\supset _{Q}.CʻQ\in 0\cup 1:\supset .\\ &\dot{s} \upharpoonright Cʻ\text{Prod}ʻ\Pi ^{;}P\in (\Pi ʻ\Sigma ʻP)\,\overline{\text{smor}}\,(\text{Prod}ʻ\Pi ^{;}P)\end{align}\]

**Status.** stated (open here): depends on ✱174·221. -/
def pm174_231 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel2excl ∧ (∀ Q, P Q Q → fld Q ∈ (zero ∪ one : Set (Set (α → α → Prop)))) →
    sDotRel ↾ fld (prodR (RelPi ⁏ P)) ∈ smorbar (relPi (relSigma P)) (prodR (RelPi ⁏ P))

/-- ✱174·24. \[\begin{align}\vdash :P\in &\text{Rel}^{2}\text{excl}.P\,\unicode{x2abd}\, J.\supset .\\ &\dot{s} \upharpoonright Cʻ\text{Prod}ʻ\Pi ^{;}P\in (\Pi ʻ\Sigma ʻP)\,\overline{\text{smor}}\,(\text{Prod}ʻ\Pi ^{;}P) \quad[*174·231·216]\end{align}\]

**Status.** stated (open here): depends on ✱174·231. -/
def pm174_24 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel2excl ∧ P ⪽ J →
    sDotRel ↾ fld (prodR (RelPi ⁏ P)) ∈ smorbar (relPi (relSigma P)) (prodR (RelPi ⁏ P))

/-- ✱174·241. \[\begin{align}\vdash \colon\ldotp P\in &\text{Rel}^{2}\text{excl}:QPQ.\supset _{Q}.CʻQ\in 0\cup 1:\supset .\\ &\Pi ʻ\Sigma ʻP \,\text{smor}\,\Pi ʻ\Pi ^{;}P.\Pi ʻ\Sigma ʻP \,\text{smor}\,\text{Prod}ʻ\Pi ^{;}P \quad[*174·221·231]\end{align}\]

**Status.** stated (open here): depends on ✱174·221·231. -/
def pm174_241 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel2excl ∧ (∀ Q, P Q Q → fld Q ∈ (zero ∪ one : Set (Set (α → α → Prop)))) →
    smor (relPi (relSigma P)) (relPi (RelPi ⁏ P)) ∧ smor (relPi (relSigma P)) (prodR (RelPi ⁏ P))

/-- ✱174·25. \[\begin{align}\vdash :P\in &\text{Rel}^{2}\text{excl}.P\,\unicode{x2abd}\, J.\supset .\\ &\Pi ʻ\Sigma ʻP \,\text{smor}\,\Pi ʻ\Pi ^{;}P.\Pi ʻ\Sigma ʻP \,\text{smor}\,\text{Prod}ʻ\Pi ^{;}P \quad[*174·23·24]\end{align}\]

**Status.** stated (open here): depends on ✱174·23·24. -/
def pm174_25 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel2excl ∧ P ⪽ J →
    smor (relPi (relSigma P)) (relPi (RelPi ⁏ P)) ∧ smor (relPi (relSigma P)) (prodR (RelPi ⁏ P))

/-- ✱174·3. \(\vdash :P\in \text{Rel}^{3}\text{arithm}.\equiv .P,\Sigma ʻP\in \text{Rel}^{2}\text{excl} \quad[(*174·01)]\) -/
theorem pm174_3 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} :
    P ∈ Rel3arithm ↔ P ∈ Rel2excl ∧ relSigma P ∈ Rel2excl := Iff.rfl

/-- ✱174·31. \[\begin{align}\vdash \colon\ldotp P\in &\text{Rel}^{3}\text{arithm}.\equiv :Q,Q'\in CʻP.Q\neq Qʻ.\supset _{Q,Q'}.CʻQ\cap CʻQ'=\Lambda:\\ &R,R'\in Cʻ\Sigma ʻP.R\neq R'.\supset _{R,R'}.CʻR\cap CʻR'=\Lambda \quad[*174·3.*163·1]\end{align}\] -/
theorem pm174_31 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} :
    P ∈ Rel3arithm ↔ (∀ Q Q', (Q ∈ fld P ∧ Q' ∈ fld P) ∧ Q ≠ Q' → fld Q ∩ fld Q' = Λ) ∧
      ∀ R R', (R ∈ fld (relSigma P) ∧ R' ∈ fld (relSigma P)) ∧ R ≠ R' → fld R ∩ fld R' = Λ :=
  Iff.rfl

/-- ✱174·311. \[\begin{align}\vdash \colon\ldotp P\in &\text{Rel}^{3}\text{arithm}.\equiv :Q,Q'\in CʻP.\exists !CʻQ\cap CʻQ'.\supset _{Q,Q'}.Q=Q':\\ &R,R'\in Cʻ\Sigma ʻP.\exists !CʻR\cap CʻRʻ.\supset _{R,Rʻ}.R=R' \quad[*174·3.*163·11]\end{align}\] -/
theorem pm174_311 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} :
    P ∈ Rel3arithm ↔
      (∀ Q Q', (Q ∈ fld P ∧ Q' ∈ fld P) ∧ (fld Q ∩ fld Q').Nonempty → Q = Q') ∧
      ∀ R R', (R ∈ fld (relSigma P) ∧ R' ∈ fld (relSigma P)) ∧ (fld R ∩ fld R').Nonempty → R = R' := by
  rw [pm174_31]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun Q Q' ⟨hQ, ⟨x, hx⟩⟩ => ?_, fun R R' ⟨hR, ⟨x, hx⟩⟩ => ?_⟩
    · by_contra hne; rw [h1 Q Q' ⟨hQ, hne⟩] at hx; exact pm170_aux_Null x hx
    · by_contra hne; rw [h2 R R' ⟨hR, hne⟩] at hx; exact pm170_aux_Null x hx
  · rintro ⟨h1, h2⟩
    refine ⟨fun Q Q' ⟨hQ, hne⟩ => pm174_aux_inter_Null.2 fun x hx hx' => hne (h1 Q Q' ⟨hQ, x, hx, hx'⟩),
      fun R R' ⟨hR, hne⟩ => pm174_aux_inter_Null.2 fun x hx hx' => hne (h2 R R' ⟨hR, x, hx, hx'⟩)⟩

/-- ✱174·32. \[\begin{align}\vdash :P\in \text{Rel}^{3}\text{arithm}.\equiv .F\upharpoonright CʻP,F\upharpoonright Cʻ\Sigma ʻP\in \text{Cls}&\rightarrow 1\\ &[*174·3.*163·12]\end{align}\] -/
theorem pm174_32 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} :
    P ∈ Rel3arithm ↔ F ↾ fld P ∈ arrow Cls one ∧ F ↾ fld (relSigma P) ∈ arrow Cls one := by
  rw [pm174_3, pm174_aux_excl_iff, pm174_aux_excl_iff]

/-- ✱174·321. \(\vdash :P\in \text{Rel}^{3}\text{arithm}.\supset .C\upharpoonright CʻP,C\upharpoonright Cʻ\Sigma ʻP\in 1\rightarrow 1 \quad[*174·3.*163·14]\) -/
theorem pm174_321 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} (h : P ∈ Rel3arithm) :
    C ↾ fld P ∈ arrow one one ∧ C ↾ fld (relSigma P) ∈ arrow one one :=
  ⟨pm173_aux_C_one_one h.1, pm173_aux_C_one_one h.2⟩

/-- ✱174·322. \(\vdash :P\in \text{Rel}^{3}\text{arithm}.Q,Q'\in CʻP.\exists !CʻʻCʻQ\cap CʻʻCʻQ'.\supset .Q=Q'\) -/
theorem pm174_322 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} {Q Q' : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : (P ∈ Rel3arithm ∧ (Q ∈ fld P ∧ Q' ∈ fld P)) ∧ (C ʻʻ fld Q ∩ C ʻʻ fld Q').Nonempty) :
    Q = Q' := by
  obtain ⟨⟨⟨h1, h2⟩, hQ, hQ'⟩, K, ⟨R, hR, hK⟩, ⟨R', hR', hK'⟩⟩ := h
  have e : fld R = fld R' := (show K = fld R from hK).symm.trans hK'
  have hRR : R = R' := by
    obtain ⟨-, h2'⟩ := mem_arrow_one_one.1 (pm173_aux_C_one_one h2)
    exact h2' (fld R) R R' ⟨⟨rfl, pm172_aux_mem_fld_relSigma hQ hR⟩,
      ⟨e, pm172_aux_mem_fld_relSigma hQ' hR'⟩⟩
  rw [← hRR] at hR'
  by_contra hne
  exact pm174_aux_inter_Null.1 (h1 Q Q' ⟨⟨hQ, hQ'⟩, hne⟩) R hR hR'

/-- ✱174·33. \(\vdash :P\in \text{Rel}^{3}\text{arithm}.\supset .CʻʻʻCʻʻCʻP\in \text{Cls}^{3}\,\text{arithm}\)

**Status.** stated (open here): not carried out here. -/
def pm174_33 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm → C ʻʻʻ (C ʻʻ fld P) ∈ Cls3arithm

/-- ✱174·34. \[\begin{align}\vdash :P\in &\text{Rel}^{3}\text{arithm}.\equiv .\\ &CʻʻʻCʻʻCʻP\in \text{Cls}^{3}\,\text{arithm}.C\upharpoonright CʻP,C\upharpoonright Cʻ\Sigma ʻP\in 1\rightarrow 1\end{align}\]

**Status.** stated (open here): depends on ✱174·33. -/
def pm174_34 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm ↔ C ʻʻʻ (C ʻʻ fld P) ∈ Cls3arithm ∧
      (C ↾ fld P ∈ arrow one one ∧ C ↾ fld (relSigma P) ∈ arrow one one)

/-- ✱174·35. \(\vdash :P\in \text{Rel}^{3}\text{arithm}.Q,Qʻ\in CʻP.Q\neq Qʻ.\supset .Cʻ\Sigma ʻQ\cap Cʻ\Sigma ʻQʻ=\Lambda\) -/
theorem pm174_35 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} {Q Q' : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : (P ∈ Rel3arithm ∧ (Q ∈ fld P ∧ Q' ∈ fld P)) ∧ Q ≠ Q') :
    fld (relSigma Q) ∩ fld (relSigma Q') = Λ := by
  obtain ⟨⟨⟨h1, h2⟩, hQ, hQ'⟩, hne⟩ := h
  refine pm174_aux_inter_Null.2 fun x hx hx' => ?_
  obtain ⟨R, hR, hxR⟩ := pm172_aux_fld_relSigma hx
  obtain ⟨R', hR', hxR'⟩ := pm172_aux_fld_relSigma hx'
  have hRR : R = R' := by
    by_contra hRne
    exact pm174_aux_inter_Null.1 (h2 R R' ⟨⟨pm172_aux_mem_fld_relSigma hQ hR,
      pm172_aux_mem_fld_relSigma hQ' hR'⟩, hRne⟩) x hxR hxR'
  rw [← hRR] at hR'
  exact pm174_aux_inter_Null.1 (h1 Q Q' ⟨⟨hQ, hQ'⟩, hne⟩) R hR hR'

/-- ✱174·36. \(\vdash :P\in \text{Rel}^{3}\text{arithm}.\supset .\Sigma ^{;}P\in \text{Rel}^{2}\text{excl}\) -/
theorem pm174_36 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} (h : P ∈ Rel3arithm) :
    RelSigma ⁏ P ∈ Rel2excl := by
  intro X Y ⟨⟨hX, hY⟩, hne⟩
  rw [show (RelSigma : (α → α → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) → Prop) =
    graph relSigma from rfl, fld_semi_graph] at hX hY
  obtain ⟨Q, hQ, rfl⟩ := hX
  obtain ⟨Q', hQ', rfl⟩ := hY
  exact pm174_35 ⟨⟨h, hQ, hQ'⟩, fun e => hne (by rw [e])⟩

/-- ✱174·361. \(\vdash :P\in \text{Rel}^{3}\text{arithm}.\supset .CʻP\subset \text{Rel}^{2}\text{excl}\) -/
theorem pm174_361 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} (h : P ∈ Rel3arithm) :
    fld P ⊆ Rel2excl := by
  intro Q hQ R R' ⟨⟨hR, hR'⟩, hne⟩
  exact h.2 R R' ⟨⟨pm172_aux_mem_fld_relSigma hQ hR, pm172_aux_mem_fld_relSigma hQ hR'⟩, hne⟩

/-- ✱174·362. \(\vdash :P\in \text{Rel}^{3}\text{arithm} .Q,Qʻ\in CʻP.CʻʻCʻQ=CʻʻCʻQʻ.\supset .Q=Qʻ\) -/
theorem pm174_362 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} {Q Q' : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : (P ∈ Rel3arithm ∧ (Q ∈ fld P ∧ Q' ∈ fld P)) ∧ C ʻʻ fld Q = C ʻʻ fld Q') : Q = Q' := by
  obtain ⟨⟨h1, hQ, hQ'⟩, e⟩ := h
  by_cases hne : (C ʻʻ fld Q).Nonempty
  · refine pm174_322 ⟨⟨h1, hQ, hQ'⟩, ?_⟩
    obtain ⟨K, hK⟩ := hne
    exact ⟨K, hK, e ▸ hK⟩
  · have h0 : ∀ R, R ∉ fld Q := fun R hR => hne ⟨fld R, R, hR, rfl⟩
    have h0' : ∀ R, R ∉ fld Q' := fun R hR => hne (by rw [e]; exact ⟨fld R, R, hR, rfl⟩)
    rw [pm173_aux_eq_rNull (Set.eq_empty_iff_forall_notMem.2 h0),
      pm173_aux_eq_rNull (Set.eq_empty_iff_forall_notMem.2 h0')]

/-- ✱174·363. \(\vdash :P\in \text{Rel}^{3}\text{arithm}.\supset .\text{Prod}^{;}P\in \text{Rel}^{2}\text{excl}\)

**Status.** stated (open here): not carried out here. -/
def pm174_363 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm → ProdR ⁏ P ∈ Rel2excl

/-- ✱174·4. \[\begin{align}\vdash :P\in \text{Rel}^{2}\text{excl}.&P\,\unicode{x2abd}\, J.\supset .\\ &\text{Prod}ʻ\Sigma ʻP=\text{D}^{;}\dot{s} ^{;}\text{Prod}ʻ\Pi ^{;}P=s^{;}\text{D}_{\in }^{;}\text{Prod}ʻ\Pi ^{;}P\end{align}\]

**Status.** stated (open here): the associative law for `Prod` is not carried out here. -/
def pm174_4 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel2excl ∧ P ⪽ J →
    prodR (relSigma P) = D ⁏ sDotRel ⁏ prodR (RelPi ⁏ P) ∧
      D ⁏ sDotRel ⁏ prodR (RelPi ⁏ P) = sRel ⁏ imgRel D ⁏ prodR (RelPi ⁏ P)

/-- ✱174·401. \(\vdash :P\in \text{Rel}^{3}\text{arithm}.\supset .\text{Prod}ʻ\text{Prod}^{;}P=\text{D}_{\in }^{;}\text{Prod}ʻ\Pi ^{;}P\)

**Status.** stated (open here): as ✱174·4. -/
def pm174_401 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm → prodR (ProdR ⁏ P) = imgRel D ⁏ prodR (RelPi ⁏ P)

/-- ✱174·41. \[\begin{align}&\vdash :P\in \text{Rel}^{3}\text{arithm}.P\,\unicode{x2abd}\, J.\supset .\text{Prod}ʻ\Sigma ʻP=s^{;}\text{Prod}ʻ\text{Prod}^{;}P\\ &[*174·4·401]\end{align}\]

**Status.** stated (open here): as ✱174·4. -/
def pm174_41 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm ∧ P ⪽ J → prodR (relSigma P) = sRel ⁏ prodR (ProdR ⁏ P)

/-- ✱174·42. \[\begin{align}\vdash :P\in &\text{Rel}^{3}\text{arithm}.P\,\unicode{x2abd}\, J.\supset .\\ &s\upharpoonright (Cʻ\text{Prod}ʻ\text{Prod}^{;}P)\in (\text{Prod}ʻ\Sigma ʻP)\,\overline{\text{smor}}\,(\text{Prod}ʻ\text{Prod}^{;}P)\end{align}\]

**Status.** stated (open here): as ✱174·4. -/
def pm174_42 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm ∧ P ⪽ J →
    sRel ↾ fld (prodR (ProdR ⁏ P)) ∈ smorbar (prodR (relSigma P)) (prodR (ProdR ⁏ P))

/-- ✱174·43. \[\begin{align}&\vdash :P\in \text{Rel}^{3}\text{arithm}.P\,\unicode{x2abd}\, J.\supset .\text{Prod}ʻ\Sigma ʻP\,\text{smor}\,\text{Prod}ʻ\text{Prod}^{;}P\\ &[*174·42]\end{align}\]

**Status.** stated (open here): as ✱174·4. -/
def pm174_43 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm ∧ P ⪽ J → smor (prodR (relSigma P)) (prodR (ProdR ⁏ P))

/-- ✱174·44. \[\begin{align}&\vdash :P\in \text{Rel}^{3}\text{arithm}.\supset .\text{Prod}ʻ\text{Prod}^{;}P=\text{D}_{\in }^{;}\text{D}^{;}\Pi ʻ\Pi ^{;}P\\ &[*174·401.*173·1]\end{align}\]

**Status.** stated (open here): as ✱174·4. -/
def pm174_44 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm → prodR (ProdR ⁏ P) = imgRel D ⁏ D ⁏ relPi (RelPi ⁏ P)

/-- ✱174·45. \[\begin{align}\vdash :P\in &\text{Rel}^{3}\text{arithm}.\supset .\\ &(\text{D}_{\in }\mid \text{D})\upharpoonright Cʻ\Pi ʻ\Pi ^{;}P\in (\text{Prod}ʻ\text{Prod}^{;}P)\,\overline{\text{smor}}\,(\Pi ʻ\Pi ^{;}P)\end{align}\]

**Status.** stated (open here): as ✱174·4. -/
def pm174_45 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm →
    (imgRel D ⨾ D) ↾ fld (relPi (RelPi ⁏ P)) ∈ smorbar (prodR (ProdR ⁏ P)) (relPi (RelPi ⁏ P))

/-- ✱174·46. \(\vdash :P\in \text{Rel}^{3}\text{arithm}.\supset .\text{Prod}ʻ\text{Prod}^{;}P\,\text{smor}\,\Pi ʻ\Pi ^{;}P \quad[*174·45]\)

**Status.** stated (open here): depends on ✱174·45. -/
def pm174_46 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm → smor (prodR (ProdR ⁏ P)) (relPi (RelPi ⁏ P))

/-- ✱174·461. \[\begin{align}&\vdash :P\in \text{Rel}^{3}\text{arithm}.P\,\unicode{x2abd}\, J.\supset .\text{Prod}ʻ\text{Prod}^{;}P\text{smor}\Pi ʻ\Sigma ʻP\\ &[*174·46·25]\end{align}\]

**Status.** stated (open here): depends on ✱174·46·25. -/
def pm174_461 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm ∧ P ⪽ J → smor (prodR (ProdR ⁏ P)) (relPi (relSigma P))

/-- ✱174·462. \[\begin{align}&\vdash :P\in \text{Rel}^{3}\text{arithm}.\supset .\Pi ʻ\text{Prod}^{;}P\,\text{smor}\,\text{Prod}ʻ\text{Prod}^{;}P\\ &[*174·363 . *173·16]\end{align}\]

**Status.** stated (open here): depends on ✱174·363. -/
def pm174_462 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm → smor (relPi (ProdR ⁏ P)) (prodR (ProdR ⁏ P))

/-- ✱174·47. \[\begin{align}&\vdash :P\in \text{Rel}^{3}\text{arithm}.P\,\unicode{x2abd}\, J.\supset .\\ &\text{Prod}ʻ\Sigma ʻP=s^{;}\text{Prod}ʻ\text{Prod}^{;}P=s^{;}\text{D}_{\in }^{;}\text{D}^{;}\Pi ʻ\Pi ^{;}P=\text{D}^{;}\dot{s} ^{;}\text{Prod}ʻ\Pi ^{;}P.\\ &s\upharpoonright Cʻ\text{Prod}ʻ\text{Prod}^{;}P,s\mid \text{D}_{\in }\mid \text{D}\upharpoonright Cʻ\Pi ʻ\Pi ^{;}P,\text{D}\mid \dot{s} \upharpoonright Cʻ\text{Prod}ʻ\Pi ^{;}P\in 1\rightarrow 1\\ &[*174·42·45·24.*41·43]\end{align}\]

**Status.** stated (open here): as ✱174·4. The chain of equations is the conjunction of its links. -/
def pm174_47 : Prop :=
  ∀ (α : Type u) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm ∧ P ⪽ J →
    ((prodR (relSigma P) = sRel ⁏ prodR (ProdR ⁏ P) ∧
      sRel ⁏ prodR (ProdR ⁏ P) = sRel ⁏ imgRel D ⁏ D ⁏ relPi (RelPi ⁏ P)) ∧
      sRel ⁏ imgRel D ⁏ D ⁏ relPi (RelPi ⁏ P) = D ⁏ sDotRel ⁏ prodR (RelPi ⁏ P)) ∧
    ((sRel ↾ fld (prodR (ProdR ⁏ P)) ∈ arrow one one ∧
      (sRel ⨾ imgRel D ⨾ D) ↾ fld (relPi (RelPi ⁏ P)) ∈ arrow one one) ∧
      (D ⨾ sDotRel) ↾ fld (prodR (RelPi ⁏ P)) ∈ arrow one one)

/-- ✱174·48. \[\begin{align}&\vdash :P\in \text{Rel}^{3}\text{arithm}.P\,\unicode{x2abd}\, J.\supset .\\ \text{Nr}ʻ\text{Prod}ʻ\text{Prod}^{;}P&=\text{Nr}ʻ\text{Prod}ʻ\Sigma ʻP=\text{Nr}ʻ\Pi ʻ\Sigma ʻP=\text{Nr}ʻ\Pi ʻ\Pi ^{;}P\\ &=\text{Nr}ʻ\text{Prod}ʻ\Pi ^{;}P=\text{Nr}ʻ\Pi ʻ\text{Prod}^{;}P\\ &[*174·43·46·25·462.*152·321]\end{align}\]

**Status.** stated (open here): depends on ✱174·43·46·25·462. The relation-numbers are taken in one
type `γ` (convention AT, Prefatory Statement); the chain is the conjunction of its links. -/
def pm174_48 : Prop :=
  ∀ (α : Type u) (γ : Type v) (P : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop),
    P ∈ Rel3arithm ∧ P ⪽ J →
    ((((nr γ (prodR (ProdR ⁏ P)) = nr γ (prodR (relSigma P)) ∧
      nr γ (prodR (relSigma P)) = nr γ (relPi (relSigma P))) ∧
      nr γ (relPi (relSigma P)) = nr γ (relPi (RelPi ⁏ P))) ∧
      nr γ (relPi (RelPi ⁏ P)) = nr γ (prodR (RelPi ⁏ P))) ∧
      nr γ (prodR (RelPi ⁏ P)) = nr γ (relPi (ProdR ⁏ P)))

/-!
## [✱176] Exponentiation

*(Vol. 2, p. 458)*

> *Summary of* *176.
>
> The definition of exponentiation is framed on the analogy of the definition in cardinals, *i.e.* we put \[ P\,\,\text{exp}\,\,Q=\text{Prod}ʻP\downarrow_{,.}^{;}Q \quad\text{Df}. \] We put also, what is often a more convenient form, \[ P^{Q}=\dot{s} ^{;}(P\,\,\text{exp}\,\,Q) \quad\text{Df}. \]
>
> …

**Lean reading.** `P exp Q` is `rexp P Q = prodR (coupleSemi P ⁏ Q)` and `P^Q` is
`rpow P Q = sDotRel ⁏ rexp P Q`; `(C'P) exp (C'Q)` is `clsExp (fld P) (fld Q)` (✱116),
`(C'P ↑ C'Q)_Δ'C'Q` is `sel (cross (fld P) (fld Q)) (fld Q)`, `(P exp);S` is `opL rexp P ⁏ S`,
`(U ∥ W̆)_∈` is `imgRel (U ∥ W˘)`, `|(Cnv'↓z)` is `relProdR (coupleR z)˘`, `(P↓.,)†` is
`daggerRel (coupleSemi P)`. The chains ✱176·1·11·13 are conjunctions of their links; the
hypothesis `Hp✱176·5` is the auxiliary `pm176_aux_Hp5`. ✱176·182 follows from ✱173·16, `P↓.,;Q`
being a relation of mutually exclusive relations (✱165·21, `pm176_aux_excl`). The identification
of `C'(P exp Q)` with `(C'P) exp (C'Q)`, the likeness and beginning theorems, and the index laws
✱176·4–·57 are not carried out here.

**Status.** stated (open here) (in part; the propositions not listed are proved): ✱176·01·02
definition; ✱176·12·14·15·151·16·18·181·19, ✱176·2·21·22·23·24,
✱176·3·31·311·32·321·33·34·341·35 and ✱176·4·41·42·43·44·5·501·502·503·51·52·53·54·541·55·56·57
stated (open here) (with readings of e-text misprints in ✱176·22·24·311·5·51, see their
docstrings).
-/

section Helpers176
variable {α : Type u} {β : Type v}

/-- The members of `C'P↓.,;Q` are the relations `P↓.,y`, `y ∈ C'Q`, which are mutually exclusive
(✱165·21). -/
theorem pm176_aux_excl (P : α → α → Prop) (Q : β → β → Prop) :
    coupleSemi P ⁏ Q ∈ Rel2excl := by
  intro X Y ⟨⟨hX, hY⟩, hne⟩
  rw [fld_coupleSemi_semi] at hX hY
  obtain ⟨y, -, rfl⟩ := hX
  obtain ⟨y', -, rfl⟩ := hY
  refine pm174_aux_inter_Null.2 fun U hU hU' => hne ?_
  rw [fld_opSemi_couple] at hU hU'
  obtain ⟨x, -, rfl⟩ := hU
  obtain ⟨x', -, e⟩ := hU'
  rw [(couple_eq_couple_iff.1 e).2]

end Helpers176

/-- ✱176·01 (Df). \(P \,\text{exp}\,\, Q = \text{Prod}ʻP\downarrow_{.,} ^{;}Q \quad\text{Df}\) -/
theorem pm176_01 (P : α → α → Prop) (Q : β → β → Prop) : rexp P Q = prodR (coupleSemi P ⁏ Q) := rfl

/-- ✱176·02 (Df). \(P^{Q} = \dot{s} ^{;}(P \,\text{exp}\,\, Q) \quad\text{Df}\) -/
theorem pm176_02 (P : α → α → Prop) (Q : β → β → Prop) : rpow P Q = sDotRel ⁏ rexp P Q := rfl

/-- ✱176·1. \(\vdash . P \,\text{exp}\,\, Q = \text{Prod}ʻP\downarrow_{.,} ^{;}Q = \text{D}^{;}\Pi ʻP\downarrow_{.,} ^{;}Q \quad[(*176·01)]\) -/
theorem pm176_1 (P : α → α → Prop) (Q : β → β → Prop) :
    rexp P Q = prodR (coupleSemi P ⁏ Q) ∧ prodR (coupleSemi P ⁏ Q) = D ⁏ relPi (coupleSemi P ⁏ Q) :=
  ⟨rfl, rfl⟩

/-- ✱176·11. \(\vdash . P^{Q} = \dot{s} ^{;}(P \,\text{exp}\,\, Q) = \dot{s} ^{;}\text{Prod}ʻP\downarrow_{.,} ^{;}Q = \dot{s} ^{;}\text{D}^{;}\Pi ʻP\downarrow_{.,} ^{;}Q \quad[(*176·02)]\) -/
theorem pm176_11 (P : α → α → Prop) (Q : β → β → Prop) :
    (rpow P Q = sDotRel ⁏ rexp P Q ∧ sDotRel ⁏ rexp P Q = sDotRel ⁏ prodR (coupleSemi P ⁏ Q)) ∧
      sDotRel ⁏ prodR (coupleSemi P ⁏ Q) = sDotRel ⁏ D ⁏ relPi (coupleSemi P ⁏ Q) :=
  ⟨⟨rfl, rfl⟩, rfl⟩

/-- ✱176·12. \[\begin{align}&\vdash \colon\colon \mu (P \,\text{exp}\,\, Q) \nu . \equiv \colon\ldotp \mu , \nu \in (CʻP) \,\text{exp}\,\, (CʻQ) \colon\ldotp \\ &(\exists y, x, x') : x \downarrow y \in \mu . x' \downarrow y \in \nu . xPx' : zQy . z \neq y . w \downarrow z \in \mu . \supset _{w, z} . w \downarrow z \in \nu \end{align}\]

**Status.** stated (open here): the identification of `C'(P exp Q)` with `(C'P) exp (C'Q)` (✱176·14)
is not carried out here. -/
def pm176_12 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop) (μ ν : Set (α → β → Prop)),
    rexp P Q μ ν ↔ (μ ∈ clsExp (fld P) (fld Q) ∧ ν ∈ clsExp (fld P) (fld Q)) ∧
      ∃ y x x', ((x ↓ y ∈ μ ∧ x' ↓ y ∈ ν) ∧ P x x') ∧
        ∀ w z, (Q z y ∧ z ≠ y) ∧ w ↓ z ∈ μ → w ↓ z ∈ ν

/-- ✱176·13. \(\vdash : \dot{\exists} ! (P \,\text{exp}\,\, Q) . \equiv . \dot{\exists} ! P^{Q} . \equiv . \dot{\exists} ! \Pi ʻP\downarrow_{.,} ^{;}Q \quad[*150·25 . *176·1·11]\) -/
theorem pm176_13 (P : α → α → Prop) (Q : β → β → Prop) :
    (rEx (rexp P Q) ↔ rEx (rpow P Q)) ∧ (rEx (rpow P Q) ↔ rEx (relPi (coupleSemi P ⁏ Q))) := by
  have h1 : rEx (rpow P Q) ↔ rEx (rexp P Q) := pm173_aux_rEx_semi_graph sumRel (rexp P Q)
  have h2 : rEx (rexp P Q) ↔ rEx (relPi (coupleSemi P ⁏ Q)) := pm173_21
  exact ⟨h1.symm, h1.trans h2⟩

/-- ✱176·131. \(\vdash : Q = \dot{\Lambda} . \supset . P \,\text{exp}\,\, Q = \dot{\Lambda} . P^{Q} = \dot{\Lambda} \quad[*165·241 . *173·2 . *150·42]\) -/
theorem pm176_131 {P : α → α → Prop} {Q : β → β → Prop} (h : Q = rNull) :
    rexp P Q = rNull ∧ rpow P Q = rNull := by
  have e : rexp P Q = rNull := by
    rw [pm176_01, h, pm173_aux_semi_rNull, pm173_2]
  exact ⟨e, by rw [pm176_02, e, pm173_aux_semi_rNull]⟩

/-- ✱176·132. \[\begin{align}&\vdash : P = \dot{\Lambda} . \dot{\exists} ! Q . \supset . P \,\text{exp}\,\, Q = \dot{\Lambda} . P^{Q} = \dot{\Lambda} \\ &[*165·244 . *172·14 . *176·13 . *150·42]\end{align}\] -/
theorem pm176_132 {P : α → α → Prop} {Q : β → β → Prop} (h : P = rNull ∧ rEx Q) :
    rexp P Q = rNull ∧ rpow P Q = rNull := by
  obtain ⟨hP, hQ⟩ := h
  obtain ⟨y, hy⟩ := pm170_aux_rEx_iff_fld.1 hQ
  have hN : rNull ∈ fld (coupleSemi P ⁏ Q) := by
    rw [fld_coupleSemi_semi]
    refine ⟨y, hy, ?_⟩
    rw [hP, opSemi, pm173_aux_semi_rNull]
  have e : rexp P Q = rNull := by
    rw [pm176_01, pm173_1, pm172_14 hN, pm173_aux_semi_rNull]
  exact ⟨e, by rw [pm176_02, e, pm173_aux_semi_rNull]⟩

/-- ✱176·133. \(\vdash . CʻP^{Q} = \dot{s} ʻʻCʻ(P \,\text{exp}\,\, Q) \quad[*176·11 . *150·22]\) -/
theorem pm176_133 (P : α → α → Prop) (Q : β → β → Prop) :
    fld (rpow P Q) = sDotRel ʻʻ fld (rexp P Q) := fld_semi_graph _ _

/-- ✱176·14. \(\vdash : \dot{\exists} ! Q . \supset . Cʻ(P \,\text{exp}\,\, Q) = (CʻP) \,\text{exp}\,\, (CʻQ) . CʻP^{Q} = (CʻP \uparrow CʻQ)_{\Delta }ʻCʻQ\)

**Status.** stated (open here): the identification of the selections from `C'P↓.,;Q` with the
classes `(C'P) exp (C'Q)` and the relations `(C'P ↑ C'Q)_Δ'C'Q` is not carried out here. -/
def pm176_14 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop), rEx Q →
    fld (rexp P Q) = clsExp (fld P) (fld Q) ∧ fld (rpow P Q) = sel (cross (fld P) (fld Q)) (fld Q)

/-- ✱176·15. \(\vdash : \dot{\exists} ! P . \dot{\exists} ! Q . \equiv . \dot{\exists} ! (P \,\text{exp}\,\, Q) . \equiv . \dot{\exists} ! P^{Q}\)

**Status.** stated (open here): not carried out here (existence of a selection from `C'P↓.,;Q`). -/
def pm176_15 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop),
    ((rEx P ∧ rEx Q) ↔ rEx (rexp P Q)) ∧ (rEx (rexp P Q) ↔ rEx (rpow P Q))

/-- ✱176·151. \(\vdash \colon\ldotp P = \dot{\Lambda} .\lor.Q = \dot{\Lambda} :\equiv .P \,\text{exp}\, Q = \dot{\Lambda} . \equiv . P^{Q} = \dot{\Lambda} \quad[*176·15]\)

**Status.** stated (open here): depends on ✱176·15. -/
def pm176_151 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop),
    ((P = rNull ∨ Q = rNull) ↔ rexp P Q = rNull) ∧ (rexp P Q = rNull ↔ rpow P Q = rNull)

/-- ✱176·16. \[\begin{align}&\vdash . Cʻ(P \,\text{exp}\,\, Q) \subset (CʻP) \,\text{exp}\,\, (CʻQ) . CʻP^{Q} \subset (CʻP \uparrow CʻQ)_{\Delta }ʻCʻQ\\ &[*176·14·151]\end{align}\]

**Status.** stated (open here): depends on ✱176·14. -/
def pm176_16 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop),
    fld (rexp P Q) ⊆ clsExp (fld P) (fld Q) ∧ fld (rpow P Q) ⊆ sel (cross (fld P) (fld Q)) (fld Q)

/-- ✱176·18. \(\vdash . \dot{s} \upharpoonright Cʻ(P \,\text{exp}\,Q) \in (P^{Q})\,\overline{\text{smor}}\,(P \,\text{exp}\,\, Q)\)

**Status.** stated (open here): not carried out here. -/
def pm176_18 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop),
    sDotRel ↾ fld (rexp P Q) ∈ smorbar (rpow P Q) (rexp P Q)

/-- ✱176·181. \(\vdash . P^{Q}\,\text{smor}\,(P \,\text{exp}\,\, Q) \quad[*176·18]\)

**Status.** stated (open here): depends on ✱176·18. -/
def pm176_181 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop), smor (rpow P Q) (rexp P Q)

/-- ✱176·182. \(\vdash . (P \,\text{exp}\,\, Q)\,\text{smor}\,(\Pi ʻP \downarrow_{.,} ^{;}Q) \quad[*176·1 . *173·16 . *165·21]\) -/
theorem pm176_182 (P : α → α → Prop) (Q : β → β → Prop) :
    smor (rexp P Q) (relPi (coupleSemi P ⁏ Q)) :=
  (pm173_16 (pm176_aux_excl P Q)).1

/-- ✱176·19. \[\begin{align}\vdash \colon\colon S(P^{Q})&T . \equiv \colon\ldotp S, T \in (CʻP \uparrow CʻQ)_{\Delta }ʻCʻQ \colon\ldotp \\ &(\exists y) : y \in CʻQ . (Sʻy) P (Tʻy) : y'Qy . y' \neq y . \supset _{yʻ} . Sʻy' = Tʻy'\end{align}\]

**Status.** stated (open here): depends on ✱176·14. -/
def pm176_19 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop) (S T : α → β → Prop),
    rpow P Q S T ↔ (S ∈ sel (cross (fld P) (fld Q)) (fld Q) ∧ T ∈ sel (cross (fld P) (fld Q)) (fld Q)) ∧
      ∃ y, (y ∈ fld Q ∧ Desc S y (fun a => Desc T y (fun b => P a b))) ∧
        ∀ y', Q y' y ∧ y' ≠ y → Desc S y' (fun a => Desc T y' (fun b => a = b))

/-- ✱176·2. \[\begin{align}\vdash : U \upharpoonright CʻR \in P\,\overline{\text{smor}}\,&R . W \upharpoonright CʻS \in Q \,\overline{\text{smor}}\,S . \supset .\\ &(U \parallel \breve{W} )_{\in } \upharpoonright Cʻ(R \,\text{exp}\,\, S) \in (P \,\text{exp}\,\, Q)\,\overline{\text{smor}}\,(R \,\text{exp}\,\, S)\end{align}\]

**Status.** stated (open here): not carried out here. -/
def pm176_2 : Prop :=
  ∀ (α : Type u) (β : Type v) (γ : Type w) (δ : Type u') (P : α → α → Prop) (Q : β → β → Prop)
    (R : γ → γ → Prop) (S : δ → δ → Prop) (U : α → γ → Prop) (W : β → δ → Prop),
    U ↾ fld R ∈ smorbar P R ∧ W ↾ fld S ∈ smorbar Q S →
    imgRel (U ∥ W˘) ↾ fld (rexp R S) ∈ smorbar (rexp P Q) (rexp R S)

/-- ✱176·21. \[\begin{align}\vdash : U \upharpoonright CʻR \in P\,\overline{\text{smor}}\, R . W \upharpoonright CʻS \in &Q\,\overline{\text{smor}}\,S . \supset .\\ &(U \parallel \breve{W} ) \upharpoonright Cʻ(R^{S}) \in (P^{Q})\,\overline{\text{smor}}\,(R^{S})\end{align}\]

**Status.** stated (open here): not carried out here. -/
def pm176_21 : Prop :=
  ∀ (α : Type u) (β : Type v) (γ : Type w) (δ : Type u') (P : α → α → Prop) (Q : β → β → Prop)
    (R : γ → γ → Prop) (S : δ → δ → Prop) (U : α → γ → Prop) (W : β → δ → Prop),
    U ↾ fld R ∈ smorbar P R ∧ W ↾ fld S ∈ smorbar Q S →
    (U ∥ W˘) ↾ fld (rpow R S) ∈ smorbar (rpow P Q) (rpow R S)

/-- ✱176·22. \[\begin{align}&\vdash : P \,\text{smor} R . Q\;\text{smor}\,S . \supset . (P \,\text{exp}\,\, Q)\,\text{smor}\,(P \,\text{exp}\,\, S) . P^{Q}\,\text{smor}\,R^{S}\\ &[*176·2·21]\end{align}\]

**Status.** stated (open here): depends on ✱176·2·21. Reading: the e-text prints `(P exp Q) smor (P
exp S)` for `(P exp Q) smor (R exp S)`. -/
def pm176_22 : Prop :=
  ∀ (α : Type u) (β : Type v) (γ : Type w) (δ : Type u') (P : α → α → Prop) (Q : β → β → Prop)
    (R : γ → γ → Prop) (S : δ → δ → Prop),
    smor P R ∧ smor Q S → smor (rexp P Q) (rexp R S) ∧ smor (rpow P Q) (rpow R S)

/-- ✱176·23. \(\vdash : R \,\text{smor smor}\, P \downarrow_{.,} ^{;}Q . \supset . \Pi ʻR\,\text{smor}\,(P \,\text{exp}\,\, Q)\)

**Status.** stated (open here): depends on ✱172·44. -/
def pm176_23 : Prop :=
  ∀ (α : Type u) (β : Type v) (γ : Type w) (P : α → α → Prop) (Q : β → β → Prop)
    (R : (γ → γ → Prop) → (γ → γ → Prop) → Prop),
    smorsmor R (coupleSemi P ⁏ Q) → smor (relPi R) (rexp P Q)

/-- ✱176·24. \[\begin{align}\vdash \colon\ldotp &\text{Mult ax} . \supset :\\ &R \in \text{Rel}^{2}\text{excl} \cap \text{Nr}ʻQ . CʻR \subset \text{Nr}ʻP . \supset . \Pi ʻP \,\text{smor}\,(P \,\text{exp}\,\, Q)\\ &[*165·38 . *176·23]\end{align}\]

**Status.** stated (open here): depends on ✱165·38 and ✱176·23. Reading: the e-text prints `Π'P` for
`Π'R`; `Mult ax` is taken at the type of the correlators of members of `C'R` with `P`. -/
def pm176_24 : Prop :=
  ∀ (α : Type u) (β : Type v) (γ : Type w) (P : α → α → Prop) (Q : β → β → Prop)
    (R : (γ → γ → Prop) → (γ → γ → Prop) → Prop), MultAx (γ → α → Prop) →
    (R ∈ Rel2excl ∧ R ∈ nr ((γ → γ → Prop)) Q) ∧ fld R ⊆ nr γ P → smor (relPi R) (rexp P Q)

/-- ✱176·3. \(\vdash . \text{Cnv}ʻ(P^{Q}) = (\breve{P} )^{Q}\)

**Status.** stated (open here): not carried out here. -/
def pm176_3 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop), (rpow P Q)˘ = rpow P˘ Q

/-- ✱176·31. \(\vdash : \dot{\exists} ! Q . \supset . \overrightarrow{B}ʻ(P \,\text{exp}\,\, Q) = (\overrightarrow{B}ʻP) \,\text{exp}\,\, (CʻQ)\)

**Status.** stated (open here): not carried out here. -/
def pm176_31 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop), rEx Q →
    refs Beg (rexp P Q) = clsExp (refs Beg P) (fld Q)

/-- ✱176·311. \[\begin{align}&\vdash : \dot{\exists} ! Q . \supset . \overrightarrow{B}ʻ\text{Cnv}ʻ(P \,\text{exp}\,\, Q) = (\overrightarrow{B}ʻP) \,\text{exp}\,\, (CʻQ)\\ &[\text{Proof as in *176·31}]\end{align} \]

**Status.** stated (open here): as ✱176·31. Reading: the e-text prints `(B⃗'P) exp (C'Q)` on the
right; as in ✱176·321·33 and the summary, the last terms of `P exp Q` correspond to `B⃗'P̆`. -/
def pm176_311 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop), rEx Q →
    refs Beg (rexp P Q)˘ = clsExp (refs Beg P˘) (fld Q)

/-- ✱176·32. \(\vdash :\dot{\exists} !Q.\supset .\overrightarrow{B}ʻ(P^{Q})=(\overrightarrow{B}ʻP\uparrow CʻQ)_{\Delta }ʻCʻQ\)

**Status.** stated (open here): not carried out here. -/
def pm176_32 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop), rEx Q →
    refs Beg (rpow P Q) = sel (cross (refs Beg P) (fld Q)) (fld Q)

/-- ✱176·321. \(\vdash :\dot{\exists} !Q.\supset .\overrightarrow{B}ʻ\text{Cnv}ʻ(P^{Q})=(\overrightarrow{B}ʻ\breve{P} \uparrow CʻQ)_{\Delta }ʻCʻQ \quad[*176·32·3]\)

**Status.** stated (open here): depends on ✱176·32·3. -/
def pm176_321 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop), rEx Q →
    refs Beg (rpow P Q)˘ = sel (cross (refs Beg P˘) (fld Q)) (fld Q)

/-- ✱176·33. \[\begin{align}\vdash \colon\ldotp \dot{\exists} !Q.\supset :&\exists !\overrightarrow{B}ʻ(P\,\text{exp}\,\,Q).\equiv .\exists !\overrightarrow{B}ʻ(P^{Q}).\equiv .\exists !\overrightarrow{B}ʻP:\\ &\exists !\overrightarrow{B}ʻ\text{Cnv}ʻ(P\,\text{exp}\,\,Q).\equiv .\exists !\overrightarrow{B}ʻ\text{Cnv}ʻ(P^{Q}).\equiv .\exists !\overrightarrow{B}ʻ\breve{P}\\ &[*176·31·311·32·321.*116·18·15]\end{align}\]

**Status.** stated (open here): depends on ✱176·31·311·32·321. -/
def pm176_33 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop), rEx Q →
    (((refs Beg (rexp P Q)).Nonempty ↔ (refs Beg (rpow P Q)).Nonempty) ∧
      ((refs Beg (rpow P Q)).Nonempty ↔ (refs Beg P).Nonempty)) ∧
    (((refs Beg (rexp P Q)˘).Nonempty ↔ (refs Beg (rpow P Q)˘).Nonempty) ∧
      ((refs Beg (rpow P Q)˘).Nonempty ↔ (refs Beg P˘).Nonempty))

/-- ✱176·34. \[\begin{align}\vdash :\dot{\exists} !Q.\text{E}!&BʻP.\supset .\\ &Bʻ(P\,\text{exp}\,\,Q)=(BʻP)\downarrowʻʻCʻQ.Bʻ(P^{Q})=(\iota ʻBʻP)\uparrow CʻQ\end{align}\]

**Status.** stated (open here): depends on ✱176·31·32. Of two descriptions the first has the larger
scope. -/
def pm176_34 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop), rEx Q ∧ EDesc Beg P →
    Desc Beg (rexp P Q) (fun X => Desc Beg P (fun b => X = coupleL b ʻʻ fld Q)) ∧
      Desc Beg (rpow P Q) (fun X => Desc Beg P (fun b => X = cross (ι b) (fld Q)))

/-- ✱176·341. \[\begin{align}\vdash :\dot{\exists} !Q.\text{E}!&Bʻ\breve{P} .\supset .\\ &Bʻ\text{Cnv}ʻ(P\,\text{exp}\,\,Q)=(Bʻ\breve{P} )\downarrowʻʻCʻQ.Bʻ\text{Cnv}ʻ(P^{Q})=(\iota ʻBʻ\breve{P} )\uparrow CʻQ\\ &[\text{Proof as in *176·34}]\end{align}\]

**Status.** stated (open here): as ✱176·34. -/
def pm176_341 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q : β → β → Prop), rEx Q ∧ EDesc Beg P˘ →
    Desc Beg (rexp P Q)˘ (fun X => Desc Beg P˘ (fun b => X = coupleL b ʻʻ fld Q)) ∧
      Desc Beg (rpow P Q)˘ (fun X => Desc Beg P˘ (fun b => X = cross (ι b) (fld Q)))

/-- ✱176·35. \(\vdash :P\,\unicode{x2abd}\, Q.\supset .P^{R}\,\unicode{x2abd}\, Q^{R}\)

**Status.** stated (open here): depends on ✱176·19. -/
def pm176_35 : Prop :=
  ∀ (α : Type u) (β : Type v) (P Q : α → α → Prop) (R : β → β → Prop),
    P ⪽ Q → rpow P R ⪽ rpow Q R

/-- ✱176·4. \[\begin{align}&\vdash :\dot{\exists} !Q.\dot{\exists} !R.PʻʻCʻQ\cap PʻʻCʻR=\Lambda.CʻQ\cup CʻR\subset \text{ᗡ}ʻP.\supset .\\ &\dot{s} \mid C\upharpoonright Cʻ\{(\Pi ʻP^{;}Q)\times (\Pi ʻP^{;}R)\}\in \{\Pi ʻP^{;}(Q\unicode{x2909}R)\}\,\overline{\text{smor}}\,\{(\Pi ʻP^{;}Q)\times (\Pi ʻP^{;}R)\}\end{align}\]

**Status.** stated (open here): depends on ✱172·34. -/
def pm176_4 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : (α → α → Prop) → β → Prop) (Q R : β → β → Prop),
    ((rEx Q ∧ rEx R) ∧ P ʻʻ fld Q ∩ P ʻʻ fld R = Λ) ∧ fld Q ∪ fld R ⊆ codom P →
    (sDotRel ⨾ C) ↾ fld (relPi (P ⁏ Q) ×ᵣ relPi (P ⁏ R)) ∈
      smorbar (relPi (P ⁏ (Q ⤉ R))) (relPi (P ⁏ Q) ×ᵣ relPi (P ⁏ R))

/-- ✱176·41. \[\begin{align}\vdash :\dot{\exists} !Q.\dot{\exists} !R.&PʻʻCʻQ\cap PʻʻCʻR=\Lambda.CʻQ\cup CʻR\subset \text{ᗡ}ʻP.\supset .\\ &\Pi ʻP^{;}(Q\unicode{x2909}R)\,\text{smor}\,(\Pi ʻP^{;}Q)\times (\Pi ʻP^{;}R) \quad[*176·4]\end{align}\]

**Status.** stated (open here): depends on ✱176·4. -/
def pm176_41 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : (α → α → Prop) → β → Prop) (Q R : β → β → Prop),
    ((rEx Q ∧ rEx R) ∧ P ʻʻ fld Q ∩ P ʻʻ fld R = Λ) ∧ fld Q ∪ fld R ⊆ codom P →
    smor (relPi (P ⁏ (Q ⤉ R))) (relPi (P ⁏ Q) ×ᵣ relPi (P ⁏ R))

/-- ✱176·42. \[\begin{align}\vdash :\dot{\exists} !Q.\dot{\exists} !R.CʻQ\cap &CʻR=\Lambda.\supset .P^{Q}\times P^{R} \text{smor} P^{Q\unicode{x2909}R}.\\ &(P \,\text{exp}\,\, Q)\times (P \,\text{exp}\,\, R)\,\text{smor}\,P \,\text{exp}\,\, (Q\unicode{x2909}R)\end{align}\]

**Status.** stated (open here): depends on ✱176·41. -/
def pm176_42 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (Q R : β → β → Prop),
    (rEx Q ∧ rEx R) ∧ fld Q ∩ fld R = Λ →
    smor (rpow P Q ×ᵣ rpow P R) (rpow P (Q ⤉ R)) ∧ smor (rexp P Q ×ᵣ rexp P R) (rexp P (Q ⤉ R))

/-- ✱176·43. \[\begin{align}\vdash :S\in &\text{Rel}^{2}\text{excl}.S\,\unicode{x2abd}\, J.\supset .\\ &s\upharpoonright Cʻ\text{Prod}ʻ(P \,\text{exp}\,\,)^{;}S\in {P \,\text{exp}\,\,(\Sigma ʻS)}\,\overline{\text{smor}}\,\text{Prod}ʻ(P \,\text{exp}\,\,)^{;}S\end{align}\]

**Status.** stated (open here): depends on ✱174·42. -/
def pm176_43 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (S : (β → β → Prop) → (β → β → Prop) → Prop),
    S ∈ Rel2excl ∧ S ⪽ J →
    sRel ↾ fld (prodR (opL rexp P ⁏ S)) ∈ smorbar (rexp P (relSigma S)) (prodR (opL rexp P ⁏ S))

/-- ✱176·44. \[\begin{align}&\vdash :S\in \text{Rel}^{2}\text{excl}.S\,\unicode{x2abd}\, J.\supset .\{\text{Prod}ʻ(P\,\text{exp}\,\,)^{;}S\}\,\text{smor}\,\{P\,\text{exp}\,\,(\Sigma ʻS)\} &[*176·43]\end{align}\]

**Status.** stated (open here): depends on ✱176·43. -/
def pm176_44 : Prop :=
  ∀ (α : Type u) (β : Type v) (P : α → α → Prop) (S : (β → β → Prop) → (β → β → Prop) → Prop),
    S ∈ Rel2excl ∧ S ⪽ J → smor (prodR (opL rexp P ⁏ S)) (rexp P (relSigma S))

/-- The hypothesis of ✱176·5 (`Hp✱176·5`), used in ✱176·501–·503: `M ↾ C'R ∈ 1 → 1 .
C'R ⊂ ᗡ'M . C'Q ⊂ p'ᗡ''M''C'R . M''C'R ⊂ 1 → 1 : z, z' ∈ C'R . ∃!D'M'z ∩ D'M'z' . ⊃_{z,z'} .
z = z' : T = x̂X̂{(∃u, z) . u ∈ C'Q . z ∈ C'R . x = (M'z)'u . X = u↓(M'z)}`. -/
def pm176_aux_Hp5 {α : Type u} {β : Type v} {δ : Type w} (M : (α → β → Prop) → δ → Prop)
    (R : δ → δ → Prop) (Q : β → β → Prop)
    (T : α → (β → (α → β → Prop) → Prop) → Prop) : Prop :=
  ((((M ↾ fld R ∈ arrow one one ∧ fld R ⊆ codom M) ∧ fld Q ⊆ prodCls (Dcnv ʻʻ (M ʻʻ fld R))) ∧
    M ʻʻ fld R ⊆ arrow one one) ∧
    ∀ z z', (z ∈ fld R ∧ z' ∈ fld R) ∧
      Desc M z (fun K => Desc M z' (fun K' => (dom K ∩ dom K').Nonempty)) → z = z') ∧
  T = fun x X => ∃ u z, ((u ∈ fld Q ∧ z ∈ fld R) ∧ Desc M z (fun K => Desc K u (fun v => x = v))) ∧
    Desc M z (fun K => X = u ↓ K)

/-- ✱176·5. \[\begin{align}\vdash \colon\ldotp &M\upharpoonright CʻR\in 1\rightarrow 1.CʻR\subset \text{ᗡ}ʻM.CʻQ\subset pʻ\text{ᗡ}ʻʻʻMʻʻCʻR.\\ &MʻʻCʻR\subset 1\rightarrow 1:z,z'\in CʻR.\exists !\text{D}ʻMʻz\cap \text{D}ʻMʻz'.\supset _{z,z'}.z=z':\\ &T=\hat{x} \hat{X} \{(\exists u,z).u\in CʻQ.z\in CʻR.x=(Mʻz)ʻu.X=u\downarrow (Mʻz)\}:\\ &\supset .T\in 1\rightarrow 1\end{align}\]

**Status.** stated (open here): the lemmas ✱176·5–·57 for the law `(P^Q)^R smor P^{R×Q}` are not
carried out here. Reading: the e-text prints `p'ᗡ'''M''C'R`; only `p'ᗡ''M''C'R` is significant (as
in ✱176·51). The hypothesis is `pm176_aux_Hp5`. -/
def pm176_5 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (M : (α → β → Prop) → δ → Prop) (R : δ → δ → Prop)
    (Q : β → β → Prop) (T : α → (β → (α → β → Prop) → Prop) → Prop),
    pm176_aux_Hp5 M R Q T → T ∈ arrow one one

/-- ✱176·501. \(\vdash :\text{Hp}*176·5.\supset .\text{ᗡ}ʻT=Cʻ\Sigma ʻQ\downarrow_{.,} ^{;}M^{;}R\)

**Status.** stated (open here): as ✱176·5. -/
def pm176_501 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (M : (α → β → Prop) → δ → Prop) (R : δ → δ → Prop)
    (Q : β → β → Prop) (T : α → (β → (α → β → Prop) → Prop) → Prop),
    pm176_aux_Hp5 M R Q T → codom T = fld (relSigma (coupleSemi Q ⁏ M ⁏ R))

/-- ✱176·502. \(\vdash :\text{Hp}*176·5.z\in CʻR.\supset .T^{;}Q\downarrow_{.,} ʻMʻz=\dagger QʻMʻz\)

**Status.** stated (open here): as ✱176·5. -/
def pm176_502 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (M : (α → β → Prop) → δ → Prop) (R : δ → δ → Prop)
    (Q : β → β → Prop) (T : α → (β → (α → β → Prop) → Prop) → Prop) (z : δ),
    pm176_aux_Hp5 M R Q T ∧ z ∈ fld R →
    Desc M z (fun K => T ⁏ opSemi couple Q K = daggerOp K Q)

/-- ✱176·503. \(\vdash :\text{Hp}*176·5.\supset .T\in (\dagger Q^{;}M^{;}R)\,\overline{\text{smor smor}}\, (Q\downarrow_{.,} ^{;}M^{;}R)\)

**Status.** stated (open here): as ✱176·5. -/
def pm176_503 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (M : (α → β → Prop) → δ → Prop) (R : δ → δ → Prop)
    (Q : β → β → Prop) (T : α → (β → (α → β → Prop) → Prop) → Prop),
    pm176_aux_Hp5 M R Q T → T ∈ smorsmorbar (opR daggerOp Q ⁏ M ⁏ R) (coupleSemi Q ⁏ M ⁏ R)

/-- ✱176·51. \[\begin{align}\vdash \colon\ldotp M\upharpoonright &CʻR\in 1\rightarrow 1.MʻʻCʻR\subset 1\rightarrow 1.\\ &CʻR\subset \text{ᗡ}ʻM.CʻQ\subset pʻ\text{ᗡ}ʻʻMʻʻCʻR:\\ &z,z'\in CʻR.\exists !\text{D}ʻMʻz\cap \text{D}ʻMʻz'.\supset _{z,z'}.z=z':\supset .\dagger Q^{;}M^{;}R\,\text{smor}\,\text{smor}Q\downarrow_{.,} ^{;}R\end{align}\]

**Status.** stated (open here): as ✱176·5. Reading: the e-text prints `smor smor` as `smor\,smor`. -/
def pm176_51 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (M : (α → β → Prop) → δ → Prop) (R : δ → δ → Prop)
    (Q : β → β → Prop),
    (((M ↾ fld R ∈ arrow one one ∧ M ʻʻ fld R ⊆ arrow one one) ∧ fld R ⊆ codom M) ∧
      fld Q ⊆ prodCls (Dcnv ʻʻ (M ʻʻ fld R))) ∧
    (∀ z z', (z ∈ fld R ∧ z' ∈ fld R) ∧
      Desc M z (fun K => Desc M z' (fun K' => (dom K ∩ dom K').Nonempty)) → z = z') →
    smorsmor (opR daggerOp Q ⁏ M ⁏ R) (coupleSemi Q ⁏ R)

/-- ✱176·52. \(\vdash \colon\ldotp z\in CʻR.\supset _{z}.Mʻz\in (Pʻz)\,\overline{\text{smor}}\,Q:\supset .P^{;}R=\dagger Q^{;}M^{;}R\)

**Status.** stated (open here): as ✱176·5. -/
def pm176_52 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (M : (α → β → Prop) → δ → Prop)
    (P : (α → α → Prop) → δ → Prop) (R : δ → δ → Prop) (Q : β → β → Prop),
    (∀ z, z ∈ fld R → Desc M z (fun K => Desc P z (fun Pz => K ∈ smorbar Pz Q))) →
    P ⁏ R = opR daggerOp Q ⁏ M ⁏ R

/-- ✱176·53. \[\begin{align}&\vdash \colon\ldotp M\upharpoonright CʻR\in 1\rightarrow 1:z\in CʻR.\supset _{z}.Mʻz\in (Pʻz)\,\overline{\text{smor}}\,Q:\\ &z,z'\in CʻR.\exists !CʻPʻz\cap CʻPʻz'.\supset _{z,z'}.z=z':\supset .P^{;}R\,\text{smor smor}\,Q\downarrow_{.,} ^{;}R\end{align}\]

**Status.** stated (open here): as ✱176·5. -/
def pm176_53 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (M : (α → β → Prop) → δ → Prop)
    (P : (α → α → Prop) → δ → Prop) (R : δ → δ → Prop) (Q : β → β → Prop),
    (M ↾ fld R ∈ arrow one one ∧
      ∀ z, z ∈ fld R → Desc M z (fun K => Desc P z (fun Pz => K ∈ smorbar Pz Q))) ∧
    (∀ z z', (z ∈ fld R ∧ z' ∈ fld R) ∧
      Desc P z (fun A => Desc P z' (fun B => (fld A ∩ fld B).Nonempty)) → z = z') →
    smorsmor (P ⁏ R) (coupleSemi Q ⁏ R)

/-- ✱176·54. \[\begin{align}&\vdash \colon\ldotp \dot{\exists} !P.\dot{\exists} !Q.M=\hat{Z} \hat{z} [z\in CʻR.Z=\{\mid (\text{Cnv}ʻ\downarrow z)\}_{\in }\upharpoonright Cʻ(P \,\text{exp}\,\, Q)].\supset :\\ &M\in 1\rightarrow 1:z\in CʻR.\supset _{z}.Mʻz\in (\text{Prod}ʻP\downarrow_{.,} ^{;}Q\downarrow_{.,} z)\,\overline{\text{smor}}\,(\text{Prod}ʻP\downarrow_{.,} ^{;}Q)\end{align}\]

**Status.** stated (open here): as ✱176·5. -/
def pm176_54 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (P : α → α → Prop) (Q : β → β → Prop)
    (R : δ → δ → Prop)
    (M : (Set (α → (β → δ → Prop) → Prop) → Set (α → β → Prop) → Prop) → δ → Prop),
    (rEx P ∧ rEx Q) ∧
      M = (fun Z z => z ∈ fld R ∧ Z = imgRel (relProdR ((coupleR z)˘ : β → (β → δ → Prop) → Prop)) ↾
        fld (rexp P Q)) →
    M ∈ arrow one one ∧ ∀ z, z ∈ fld R → Desc M z (fun K =>
      K ∈ smorbar (prodR (coupleSemi P ⁏ opSemi couple Q z)) (prodR (coupleSemi P ⁏ Q)))

/-- ✱176·541. \(\vdash .(P\downarrow_{.,} )\dagger ^{;}Q\downarrow_{.,} ^{;}R\in \text{Rel}^{3}\text{arithm}.\Sigma ʻ(P\downarrow_{.,} )\dagger ^{;}Q\downarrow_{.,} ^{;}R=P\downarrow_{.,} ^{;}\Sigma ʻQ\downarrow_{.,} ^{;}R\)

**Status.** stated (open here): as ✱176·5. -/
def pm176_541 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (P : α → α → Prop) (Q : β → β → Prop)
    (R : δ → δ → Prop),
    daggerRel (coupleSemi P) ⁏ coupleSemi Q ⁏ R ∈ Rel3arithm ∧
      relSigma (daggerRel (coupleSemi P) ⁏ coupleSemi Q ⁏ R) =
        coupleSemi P ⁏ relSigma (coupleSemi Q ⁏ R)

/-- ✱176·55. \(\vdash :\dot{\exists} !P.\dot{\exists} !Q.\supset .\text{Prod}^{;}(P\downarrow_{.,} )\dagger ^{;}Q\downarrow_{.,} ^{;}R\,\text{smor smor}\, (\text{Prod}ʻP\downarrow_{.,} ^{;}Q)\downarrow_{.,} ^{;}R\)

**Status.** stated (open here): as ✱176·5. -/
def pm176_55 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (P : α → α → Prop) (Q : β → β → Prop)
    (R : δ → δ → Prop), rEx P ∧ rEx Q →
    smorsmor (ProdR ⁏ daggerRel (coupleSemi P) ⁏ coupleSemi Q ⁏ R)
      (coupleSemi (prodR (coupleSemi P ⁏ Q)) ⁏ R)

/-- ✱176·56. \[\begin{align}\vdash :\dot{\exists} !P.\dot{\exists} !&Q.R\,\unicode{x2abd}\, J.\supset .\\ &\text{Prod}ʻ\Sigma ʻ(P\downarrow_{.,} )\dagger ^{;}Q\downarrow_{.,} ^{;}R\,\text{smor}\,\text{Prod}ʻ(\text{Prod}ʻP\downarrow_{.,} ^{;}Q)\downarrow_{.,} ^{;}R\end{align}\]

**Status.** stated (open here): as ✱176·5. -/
def pm176_56 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (P : α → α → Prop) (Q : β → β → Prop)
    (R : δ → δ → Prop), (rEx P ∧ rEx Q) ∧ R ⪽ J →
    smor (prodR (relSigma (daggerRel (coupleSemi P) ⁏ coupleSemi Q ⁏ R)))
      (prodR (coupleSemi (prodR (coupleSemi P ⁏ Q)) ⁏ R))

/-- ✱176·57. \(\vdash :R\,\unicode{x2abd}\, J.\supset .\{(P\,\text{exp}\,\,Q)\,\text{exp}\,\,R\}\,\text{smor}\,\{P\,\text{exp}\,\,(R\times Q)\}.(P^{Q})^{R}\,\text{smor}\,P^{R\times Q}\)

**Status.** stated (open here): depends on ✱176·56 and ✱174. -/
def pm176_57 : Prop :=
  ∀ (α : Type u) (β : Type v) (δ : Type w) (P : α → α → Prop) (Q : β → β → Prop)
    (R : δ → δ → Prop), R ⪽ J →
    smor (rexp (rexp P Q) R) (rexp P (R ×ᵣ Q)) ∧ smor (rpow (rpow P Q) R) (rpow P (R ×ᵣ Q))

/-!
## [✱177] Propositions connecting \(p_{\text{df}}\) with products and powers

*(Vol. 2, p. 471)*

> *Summary of* *177.
>
> The principal proposition on this subject is
>
> *177*13. \(\vdash :x\neq y.\supset .P_{\text{df}}\,\text{smor}\,\{(x\downarrow y)^{P}\}\)
>
> which is the analogue of *116·72, or rather leads to the analogue of *116·72 as soon as powers of relation-numbers have been defined; for then it becomes \[ P_{\text{df}}\in 2_{r}^{\text{Nr}ʻP}. \] Another proposition is an extension of *171·69, namely
>
> *177·22. \(\vdash :P\in \text{Rel}^{2}\text{excl}.P\,\unicode{x2abd}\, J.\supset .\text{Prod}ʻ\text{df}^{;}P \,\text{smor}\,(\Sigma ʻP)_{\text{df}}\)
>
> where we put \(\text{df}ʻQ=Q_{\text{df}}\).
>
> The remaining propositions of this number are lemmas for the above two.
>
> *177·13 shows, for example, that all classes of finite integers can be arranged in a series of which the relation-number is \(2_{r}^\omega\), where \(\omega\) is the relation-number of the series of finite integers. \(2_{r}^\omega\) is not the relation-number of the continuum, but is closely allied to it.

**Lean reading.** `df'Q = Q_df` (✱177·2, a Dft printed in the e-text as a proposition) is
`Desc dfRel Q (· = Pdf Q)`, and `df;P` is `dfRel ⁏ P`. `{(ι'x ∪ ι'y) ↑ α}_Δ'α` is
`sel (cross (ι x ∪ ι y) A) A`, `R⃖'x` is `rels R x`, `(x↓y)^P` is `rpow (x ↓ y) P`; `Hp✱177·1` is
written out in ✱177·11·12. ✱177·13 is read with `smor` (the e-text prints `smor̄`). The
correspondence of ✱116·71 and the results resting on ✱174 are not carried out here.

**Status.** stated (open here): ✱177·1·11·12·13·21·22; ✱177·2 definition (Dft).
-/

/-- ✱177·1. \[\begin{align}\vdash :x\neq y.T=\hat{\mu} \hat{R} &[R\in \{(\iota ʻx\cup \iota ʻy)\uparrow \alpha\}_{\Delta }ʻ\alpha .\mu =\overleftarrow{R}ʻx].\supset .\\ &T\in (\text{Cl}ʻ\alpha )\,\overline{\text{ sm }}\, \{(\iota ʻx\cup \iota ʻy)\uparrow \alpha\}_{\Delta }ʻ\alpha \quad[*116·712·713·715]\end{align}\]

**Status.** stated (open here): the correlation (✱116·712–·715) of `Cl'α` with the relations from
`α` to `ι'x ∪ ι'y` is not carried out here. -/
def pm177_1 : Prop :=
  ∀ (α : Type u) (β : Type v) (x y : β) (A : Set α) (T : Set α → (β → α → Prop) → Prop),
    x ≠ y ∧ T = (fun μ R => R ∈ sel (cross (ι x ∪ ι y) A) A ∧ μ = rels R x) →
    T ∈ smbar (cl A) (sel (cross (ι x ∪ ι y) A) A)

/-- ✱177·11. \(\vdash :\text{Hp}*177·1.\alpha =CʻP.\supset .T^;(x\downarrow y)^P=P_{\text{df}}\)

**Status.** stated (open here): as ✱177·1. -/
def pm177_11 : Prop :=
  ∀ (α : Type u) (β : Type v) (x y : β) (A : Set α) (T : Set α → (β → α → Prop) → Prop)
    (P : α → α → Prop),
    (x ≠ y ∧ T = (fun μ R => R ∈ sel (cross (ι x ∪ ι y) A) A ∧ μ = rels R x)) ∧ A = fld P →
    T ⁏ rpow (x ↓ y) P = Pdf P

/-- ✱177·12. \(\vdash :\text{Hp}*177·11.\supset .T\in P_{\text{df}}\,\overline{\text{smor}}\,\{(x\downarrow y)^{P}\} \quad[*177·1·11.*151·191]\)

**Status.** stated (open here): depends on ✱177·1·11. -/
def pm177_12 : Prop :=
  ∀ (α : Type u) (β : Type v) (x y : β) (A : Set α) (T : Set α → (β → α → Prop) → Prop)
    (P : α → α → Prop),
    (x ≠ y ∧ T = (fun μ R => R ∈ sel (cross (ι x ∪ ι y) A) A ∧ μ = rels R x)) ∧ A = fld P →
    T ∈ smorbar (Pdf P) (rpow (x ↓ y) P)

/-- ✱177·13. \(\vdash :x\neq y.\supset .P_{\text{df}}\,\overline{\text{smor}}\,\{(x\downarrow y)^{P}\} \quad[*177·12]\)

**Status.** stated (open here): depends on ✱177·12. Reading: the e-text prints `P_df smor̄
{(x↓y)^P}` (a class, not a proposition); PM's ✱177·13 (Summary of ✱177) is `P_df smor {(x↓y)^P}`. -/
def pm177_13 : Prop :=
  ∀ (α : Type u) (β : Type v) (x y : β) (P : α → α → Prop), x ≠ y → smor (Pdf P) (rpow (x ↓ y) P)

/-- ✱177·2. \(\text{df}ʻQ=Q_{\text{df}} \quad\text{Dft}[*177]\)

**Status.** definition: the temporary definition (Dft) of `df` for ✱177; the e-text prints it as a
proposition. -/
theorem pm177_2 (Q : α → α → Prop) : Desc dfRel Q (fun X => X = Pdf Q) := (desc_graph _ _ _).2 rfl

/-- ✱177·21. \(\vdash :P\in \text{Rel}^{2}\text{excl}.P\,\unicode{x2abd}\, J.\supset .s\upharpoonright Cʻ\text{Prod}ʻ\text{df}^{;}P\in (\Sigma ʻP)_{\text{df}}\,\overline{\text{smor}}\, (\text{Prod}ʻ\text{df}^{;}P)\)

**Status.** stated (open here): depends on ✱174·4 and ✱171. -/
def pm177_21 : Prop :=
  ∀ (α : Type u) (P : (α → α → Prop) → (α → α → Prop) → Prop), P ∈ Rel2excl ∧ P ⪽ J →
    sRel ↾ fld (prodR (dfRel ⁏ P)) ∈ smorbar (Pdf (relSigma P)) (prodR (dfRel ⁏ P))

/-- ✱177·22. \(\vdash :P\in \text{Rel}^{2}\text{excl}.P\,\unicode{x2abd}\, J.\supset .\text{Prod}ʻ\text{df}^{;}P \,\text{smor}(\Sigma ʻP)_{\text{df}} \quad[*177·21]\)

**Status.** stated (open here): depends on ✱177·21. -/
def pm177_22 : Prop :=
  ∀ (α : Type u) (P : (α → α → Prop) → (α → α → Prop) → Prop), P ∈ Rel2excl ∧ P ⪽ J →
    smor (prodR (dfRel ⁏ P)) (Pdf (relSigma P))

end PrincipiaMathematica
