import PrincipiaMathematica.Defs.Part1

/-!
# Part I, Section E: Products and sums of classes

Volume 1. Numbers: ✱40, ✱41, ✱42, ✱43.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w u' v'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'} {ε : Type v'}

/-- When `E!R'y`, `ψ(R'y)` holds iff every `A` with `A R y` satisfies `ψ`. -/
private theorem desc_iff_forall {R : α → β → Prop} {y : β} {ψ : α → Prop} (h : EDesc R y) :
    Desc R y ψ ↔ ∀ A, R A y → ψ A := by
  obtain ⟨b, hb⟩ := h
  constructor
  · rintro ⟨c, hc, hψ⟩ A hA
    have e : A = c := (hc A).1 hA
    exact e ▸ hψ
  · intro h'
    exact ⟨b, hb, h' b ((hb b).2 rfl)⟩

/-- When `E!R'y`, `ψ(R'y)` holds iff some `A` with `A R y` satisfies `ψ`. -/
private theorem desc_iff_exists {R : α → β → Prop} {y : β} {ψ : α → Prop} (h : EDesc R y) :
    Desc R y ψ ↔ ∃ A, R A y ∧ ψ A := by
  obtain ⟨b, hb⟩ := h
  constructor
  · rintro ⟨c, hc, hψ⟩
    exact ⟨c, (hc c).2 rfl, hψ⟩
  · rintro ⟨A, hA, hψ⟩
    have e : A = b := (hb A).1 hA
    exact ⟨b, hb, e ▸ hψ⟩

/-- PM ✱37·22. -/
private theorem img_union' (R : α → β → Prop) (A B : Set β) : R ʻʻ (A ∪ B) = R ʻʻ A ∪ R ʻʻ B := by
  ext x
  constructor
  · rintro ⟨y, hy | hy, h⟩
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr ⟨y, hy, h⟩
  · rintro (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
    · exact ⟨y, Or.inl hy, h⟩
    · exact ⟨y, Or.inr hy, h⟩

/-- PM ✱34·21 (associativity of the relative product). -/
private theorem relProd_assoc (R : α → β → Prop) (S : β → γ → Prop) (T : γ → δ → Prop) :
    R ⨾ S ⨾ T = R ⨾ (S ⨾ T) := by
  funext x w
  apply propext
  constructor
  · rintro ⟨z, ⟨y, hxy, hyz⟩, hzw⟩
    exact ⟨y, hxy, z, hyz, hzw⟩
  · rintro ⟨y, hxy, z, hyz, hzw⟩
    exact ⟨z, ⟨y, hxy, hyz⟩, hzw⟩

private theorem relProd_apply_iff (R : α → β → Prop) (S : β → γ → Prop) (x : α) (z : γ) :
    (R ⨾ S) x z ↔ ∃ y, R x y ∧ S y z := Iff.rfl

private theorem relProdL_iff (R : α → β → Prop) (P : α → γ → Prop) (Q : β → γ → Prop) :
    relProdL R P Q ↔ P = R ⨾ Q := Iff.rfl

private theorem relProdR_iff (S : β → γ → Prop) (P : α → γ → Prop) (Q : α → β → Prop) :
    relProdR S P Q ↔ P = Q ⨾ S := Iff.rfl

/-- PM ✱35·481. -/
private theorem relProd_cres_eq {Q : α → β → Prop} {P : β → γ → Prop} {A : Set β}
    (h : dom P ⊆ A) : Q ⨾ P = (Q ↾ A) ⨾ P := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨y, ⟨hxy, h (show y ∈ dom P from ⟨z, hyz⟩)⟩, hyz⟩
  · rintro ⟨y, ⟨hxy, -⟩, hyz⟩
    exact ⟨y, hxy, hyz⟩

/-- PM ✱35·48. -/
private theorem relProd_dres_eq {P : α → β → Prop} {R : β → γ → Prop} {B : Set β}
    (h : codom P ⊆ B) : P ⨾ R = P ⨾ (B ◁ R) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨y, hxy, h (show y ∈ codom P from ⟨x, hxy⟩), hyz⟩
  · rintro ⟨y, hxy, -, hyz⟩
    exact ⟨y, hxy, hyz⟩

/-- PM ✱37·32 (first half). -/
private theorem img_dom (R : α → β → Prop) (P : β → γ → Prop) : R ʻʻ dom P = dom (R ⨾ P) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hyz⟩, hxy⟩
    exact ⟨z, y, hxy, hyz⟩
  · rintro ⟨z, y, hxy, hyz⟩
    exact ⟨y, ⟨z, hyz⟩, hxy⟩

/-- PM ✱37·32 (second half). -/
private theorem img_codom (P : α → β → Prop) (R : β → γ → Prop) :
    R˘ ʻʻ codom P = codom (P ⨾ R) := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, hxy⟩, hyz⟩
    exact ⟨x, y, hxy, hyz⟩
  · rintro ⟨x, y, hxy, hyz⟩
    exact ⟨y, ⟨x, hxy⟩, hyz⟩

/-!
## [✱40] Products and sums of classes of classes

*(Vol. 1, p. 319)*

> *Summary of* *40.
>
> In this number, we introduce the two notations (explained above) \[ \begin{aligned} &pʻ\kappa = \hat{x} (\alpha\in\kappa . \supset_{\alpha} . x\in\alpha) \quad\text{Df}\\ &sʻ\kappa = \hat{x} \{(\exists\alpha) . \alpha\in\kappa . x\in \alpha\} \quad\text{Df} \end{aligned} \] Both these notions will be found increasingly useful as we proceed, but \(sʻ\kappa\) remains more useful than \(pʻ\kappa\) throughout. It is required for the significance of \(pʻ\kappa\) and \(sʻ\kappa\) that \(\kappa\) should be a class of classes.
>
> In the present number, the most useful propositions are the following:
>
> *40·12. \(\vdash : \alpha \in \kappa . \supset . pʻ\kappa \subset \alpha\)
>
> *I.e.* the product of \(\kappa\) is contained in every member of \(\kappa\).
>
> *40·13. \(\vdash : \alpha \in \kappa . \supset . \alpha \subset sʻ\kappa\)
>
> *I.e.* every member of \(\kappa\) is contained in the sum of \(\kappa\).
>
> *40·15. \(\vdash \colon\ldotp \beta \subset pʻ\kappa . \equiv : \gamma \in \kappa . \supset_{\gamma} . \beta \subset \gamma\)
>
> *I.e.* \(\beta\) is contained in the product of \(\kappa\) if \(\beta\) is contained in every member of \(\kappa\), and vice versa.
>
> …

**Lean reading.** A class of classes `κ` is `K : Set (Set α)`; the Dfs ✱40·01·02 are the Lean
definitions `prodCls K` (`p'κ`, `= ⋂₀ K`) and `sumCls K` (`s'κ`, `= ⋃₀ K`), whose defining
equations hold by `rfl`. PM's `⊂` is `⊆`, `∃!κ` is `K.Nonempty`, `Λ`, `V` are `Λ`, `V` at the
appropriate types (in ✱40·2·21 the two `Λ`'s, of different types, are two instances of `Λ`).
`R''β`, `R'''κ`, `R⃗`, `R⃖`, `C`, `D`, `ᗡ`, `F` are those of `Defs/Part1`; from ✱40·3 to ✱40·45 the
domain of `R` consists of classes (`R : Set α → β → Prop`), as PM requires for significance. The
descriptions `R'y` of ✱40·4–·45 (where `R` is arbitrary) are kept as `Desc R y ψ`, with the
hypothesis `E!!R''β` (`EE R B`) exactly where PM has it; in ✱40·42 and ✱40·45 the descriptions
occurring first have the larger scopes. `R⃗'x`, `R⃖'x` (graphs) are `refs R x`, `rels R x`. The
relations `α ♀,,` and `♀,, y` of ✱40·7·71 are ✱38·01·02 applied to the double function `♀,,`:
`opL (opImg f) A` and `opR (opImg f) y`. ✱40·81, printed in the e-text after the demonstration
of ✱40·8 without an entry of its own, is added as `pm40_81`. Proofs are direct.

**Status.** proved (all propositions; ✱40·01·02 definition; ✱40·221, ✱40·24, ✱40·25, ✱40·52,
✱40·61, ✱40·71 proved (reading): e-text transcription errors; ✱40·42, ✱40·44, ✱40·45, ✱40·451,
✱40·67 proved (reading): dots lost in the e-text; ✱40·69 proved (reading): arrows of the e-text
corrected (`C'P⃗` read `C'P`, and `P⃖` throughout, as in the corrected demonstration and in
✱213·18; the `P⃗` form is the extra lemma `pm40_69_aux_fwd`); see their docstrings).
-/

/-- ✱40·01 (Df). \(pʻ\kappa = \hat{x} (\alpha\in\kappa . \supset_{\alpha} . x\in\alpha) \quad\text{Df}\) -/
theorem pm40_01 {K : Set (Set α)} : prodCls K = {x | ∀ A, A ∈ K → x ∈ A} := rfl

/-- ✱40·02 (Df). \(sʻ\kappa = \hat{x} {(\exists\alpha) . \alpha\in\kappa . x\in\alpha} \quad\text{Df}\)

(The e-text drops the braces of the definiens.) -/
theorem pm40_02 {K : Set (Set α)} : sumCls K = {x | ∃ A, A ∈ K ∧ x ∈ A} := rfl

/-- ✱40·1. \(\vdash \colon\ldotp x\in pʻ\kappa . \equiv : \alpha\in\kappa . \supset_{\alpha} . x\in\alpha \quad[\text{*20·3.(*40·01)}]\) -/
theorem pm40_1 {K : Set (Set α)} {x : α} : x ∈ prodCls K ↔ ∀ A, A ∈ K → x ∈ A := Iff.rfl

/-- ✱40·11. \(\vdash : x\in sʻ\kappa . \equiv . (\exists\alpha). \alpha\in\kappa . x\in\alpha \quad[\text{*20·3.(*40·02)}]\) -/
theorem pm40_11 {K : Set (Set α)} {x : α} : x ∈ sumCls K ↔ ∃ A, A ∈ K ∧ x ∈ A := Iff.rfl

/-- ✱40·12. \(\vdash : \alpha\in\kappa . \supset . pʻ\kappa \subset \alpha\) -/
theorem pm40_12 {K : Set (Set α)} {A : Set α} : A ∈ K → prodCls K ⊆ A :=
  fun hA _ hx => hx A hA

/-- ✱40·13. \(\vdash : \alpha\in\kappa . \supset . \alpha \subset sʻ\kappa\) -/
theorem pm40_13 {K : Set (Set α)} {A : Set α} : A ∈ K → A ⊆ sumCls K :=
  fun hA _ hx => ⟨A, hA, hx⟩

/-- ✱40·14. \(\vdash : \alpha \in \kappa . x \in pʻ\kappa . \supset . x \in \alpha \quad[\text{*40·12 . Imp}]\) -/
theorem pm40_14 {K : Set (Set α)} {A : Set α} {x : α} : A ∈ K ∧ x ∈ prodCls K → x ∈ A :=
  fun h => h.2 A h.1

/-- ✱40·141. \(\vdash : \alpha \in \kappa . x \in \alpha . \supset . x \in sʻ\kappa \quad[\text{*40·11 . *10·24}]\) -/
theorem pm40_141 {K : Set (Set α)} {A : Set α} {x : α} : A ∈ K ∧ x ∈ A → x ∈ sumCls K :=
  fun h => ⟨A, h.1, h.2⟩

/-- ✱40·15. \(\vdash \colon\ldotp \beta \subset pʻ\kappa . \equiv : \gamma \in \kappa . \supset_{\gamma} . \beta \subset \gamma\) -/
theorem pm40_15 {K : Set (Set α)} {B : Set α} : B ⊆ prodCls K ↔ ∀ G, G ∈ K → B ⊆ G :=
  ⟨fun h G hG _ hx => h hx G hG, fun h _ hx G hG => h G hG hx⟩

/-- ✱40·151. \(\vdash \colon\ldotp sʻ\kappa \subset \beta . \equiv : \gamma \in \kappa . \supset_{\gamma} . \gamma \subset \beta\) -/
theorem pm40_151 {K : Set (Set α)} {B : Set α} : sumCls K ⊆ B ↔ ∀ G, G ∈ K → G ⊆ B := by
  constructor
  · intro h G hG x hx
    exact h ⟨G, hG, hx⟩
  · rintro h x ⟨G, hG, hx⟩
    exact h G hG hx

/-- ✱40·16. \(\vdash : \kappa \subset \lambda . \supset . pʻ\lambda \subset pʻ\kappa\) -/
theorem pm40_16 {K L : Set (Set α)} : K ⊆ L → prodCls L ⊆ prodCls K :=
  fun h _ hx G hG => hx G (h hG)

/-- ✱40·161. \(\vdash : \kappa \subset \lambda . \supset . sʻ\kappa \subset sʻ\lambda\) -/
theorem pm40_161 {K L : Set (Set α)} : K ⊆ L → sumCls K ⊆ sumCls L := by
  rintro h x ⟨G, hG, hx⟩
  exact ⟨G, h hG, hx⟩

/-- ✱40·17. \(\vdash . pʻ\kappa \cup pʻ\lambda \subset pʻ(\kappa \cap \lambda)\) -/
theorem pm40_17 {K L : Set (Set α)} : prodCls K ∪ prodCls L ⊆ prodCls (K ∩ L) := by
  rintro x (hx | hx) G ⟨hK, hL⟩
  · exact hx G hK
  · exact hx G hL

/-- ✱40·171. \(\vdash.sʻ\kappa\cup sʻ\lambda=sʻ(\kappa\cup\lambda)\) -/
theorem pm40_171 {K L : Set (Set α)} : sumCls K ∪ sumCls L = sumCls (K ∪ L) := by
  ext x
  constructor
  · rintro (⟨G, hG, hx⟩ | ⟨G, hG, hx⟩)
    · exact ⟨G, Or.inl hG, hx⟩
    · exact ⟨G, Or.inr hG, hx⟩
  · rintro ⟨G, hG | hG, hx⟩
    · exact Or.inl ⟨G, hG, hx⟩
    · exact Or.inr ⟨G, hG, hx⟩

/-- ✱40·18. \(\vdash.pʻ(\kappa\cup\lambda)=pʻ\kappa\cap pʻ\lambda\)

The enunciation erratum (Additional Errata to Vol. I, p. 322: `=` for `≡`) is already
incorporated in the e-text. -/
theorem pm40_18 {K L : Set (Set α)} : prodCls (K ∪ L) = prodCls K ∩ prodCls L := by
  ext x
  constructor
  · intro hx
    exact ⟨fun G hG => hx G (Or.inl hG), fun G hG => hx G (Or.inr hG)⟩
  · rintro ⟨hK, hL⟩ G (hG | hG)
    · exact hK G hG
    · exact hL G hG

/-- ✱40·181. \(\vdash.sʻ(\kappa\cap\lambda)\subset sʻ\kappa\cap sʻ\lambda\) -/
theorem pm40_181 {K L : Set (Set α)} : sumCls (K ∩ L) ⊆ sumCls K ∩ sumCls L := by
  rintro x ⟨G, ⟨hK, hL⟩, hx⟩
  exact ⟨⟨G, hK, hx⟩, ⟨G, hL, hx⟩⟩

/-- ✱40·19. \(\vdash\colon\colon x\in sʻ\kappa.\equiv\colon\ldotp\gamma\in\kappa.\supset_{\gamma}.\gamma\subset\beta:\supset_{\beta}.x\in\beta\) -/
theorem pm40_19 {K : Set (Set α)} {x : α} :
    x ∈ sumCls K ↔ ∀ B, (∀ G, G ∈ K → G ⊆ B) → x ∈ B := by
  constructor
  · rintro ⟨G, hG, hx⟩ B h
    exact h G hG hx
  · intro h
    exact h (sumCls K) fun G hG y hy => ⟨G, hG, hy⟩

/-- ✱40·2. \(\vdash\colon\kappa=\Lambda.\supset.pʻ\kappa=\text{V}\) -/
theorem pm40_2 {K : Set (Set α)} : K = Λ → prodCls K = V := by
  rintro rfl
  simp only [V_eq_univ, Null_eq_empty]
  ext x
  simp [prodCls]

/-- ✱40·21. \(\vdash\colon\kappa=\Lambda.\supset.sʻ\kappa=\Lambda\) -/
theorem pm40_21 {K : Set (Set α)} : K = Λ → sumCls K = Λ := by
  rintro rfl
  simp only [Null_eq_empty]
  ext x
  simp [sumCls]

/-- ✱40·22. \(\vdash\colon\colon\Lambda\in\kappa.\supset.pʻ\kappa=\Lambda\) -/
theorem pm40_22 {K : Set (Set α)} : Λ ∈ K → prodCls K = Λ := by
  intro h
  simp only [Null_eq_empty] at h ⊢
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  simpa using hx ∅ h

/-- ✱40·221. \(\vdash\colon=\text{V}\in\kappa.\supset.sʻ\kappa=\text{V}\)

**Status.** proved (reading): transcription error of the e-text, which prints a stray `=` before
the hypothesis (`⊢ : = V ∈ κ . ⊃ . …`); PM's ✱40·221 is `V ∈ κ . ⊃ . s'κ = V`, as its
demonstration (`Hp . ⊃ . V ⊂ s'κ`) shows. -/
theorem pm40_221 {K : Set (Set α)} : V ∈ K → sumCls K = V := by
  intro h
  simp only [V_eq_univ] at h ⊢
  exact Set.eq_univ_of_forall fun x => ⟨Set.univ, h, Set.mem_univ x⟩

/-- ✱40·23. \(\vdash\colon\exists!\kappa.\supset.pʻ\kappa\subset sʻ\kappa\) -/
theorem pm40_23 {K : Set (Set α)} : K.Nonempty → prodCls K ⊆ sumCls K := by
  rintro ⟨G, hG⟩ x hx
  exact ⟨G, hG, hx G hG⟩

/-- ✱40·24. \(\vdash\colon\ldotp\exists!\kappa\colon\gamma\in\kappa.\supset_{\gamma}.\beta\subset\gamma\colon\supset.\beta\subsetʻ\kappa\)

**Status.** proved (reading): transcription error of the e-text, which prints `β ⊂ ʻκ` (the `s` of
`s'κ` dropped); the demonstration concludes `β ⊂ s'κ` (from `β ⊂ p'κ . p'κ ⊂ s'κ`). -/
theorem pm40_24 {K : Set (Set α)} {B : Set α} :
    K.Nonempty ∧ (∀ G, G ∈ K → B ⊆ G) → B ⊆ sumCls K := by
  rintro ⟨⟨G, hG⟩, h⟩ x hx
  exact ⟨G, hG, h G hG hx⟩

/-- ✱40·25. \(\vdash\colon x\in sʻ\kappa.\equiv.\exists!\kappa\cap\hat{a}(x \in\alpha)\)

**Status.** proved (reading): transcription error of the e-text, which prints `â(x ∈ α)` for
`α̂(x ∈ α)` (the class of the classes containing `x`, as the demonstration uses it:
`γ ∈ α̂(x ∈ α) . ≡ . x ∈ γ`). -/
theorem pm40_25 {K : Set (Set α)} {x : α} : x ∈ sumCls K ↔ (K ∩ {A | x ∈ A}).Nonempty := by
  constructor
  · rintro ⟨G, hG, hx⟩
    exact ⟨G, hG, hx⟩
  · rintro ⟨G, hG, hx⟩
    exact ⟨G, hG, hx⟩

/-- ✱40·26. \(\vdash\colon\exists!sʻ\kappa.\equiv.(\exists \alpha).\alpha\in\kappa.\exists!\alpha\) -/
theorem pm40_26 {K : Set (Set α)} : (sumCls K).Nonempty ↔ ∃ A, A ∈ K ∧ A.Nonempty := by
  constructor
  · rintro ⟨x, G, hG, hx⟩
    exact ⟨G, hG, x, hx⟩
  · rintro ⟨G, hG, x, hx⟩
    exact ⟨x, G, hG, hx⟩

/-- ✱40·27. \(\vdash\colon\ldotp \alpha\cap sʻ\kappa=\Lambda.\equiv\colon \gamma\in\kappa.\supset_{\gamma}.\alpha\cap\gamma=\Lambda\) -/
theorem pm40_27 {K : Set (Set α)} {A : Set α} :
    A ∩ sumCls K = Λ ↔ ∀ G, G ∈ K → A ∩ G = Λ := by
  simp only [Null_eq_empty, Set.ext_iff, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false,
    not_and]
  constructor
  · intro h G hG x hA hx
    exact h x hA ⟨G, hG, hx⟩
  · rintro h x hA ⟨G, hG, hx⟩
    exact h G hG x hA hx

/-- ✱40·3. \(\vdash.pʻRʻʻ(\alpha\cup\beta)=pʻRʻʻ\alpha\cap pʻRʻʻ\beta \quad[\text{*37·22.*40·18}]\) -/
theorem pm40_3 {R : Set α → β → Prop} {A B : Set β} :
    prodCls (R ʻʻ (A ∪ B)) = prodCls (R ʻʻ A) ∩ prodCls (R ʻʻ B) := by
  rw [img_union']
  exact pm40_18

/-- ✱40·31. \(\vdash.sʻRʻʻ(\alpha\cup\beta)=sʻRʻʻ\alpha\cup sʻRʻʻ\beta \quad[\text{*37·22.*40·171}]\) -/
theorem pm40_31 {R : Set α → β → Prop} {A B : Set β} :
    sumCls (R ʻʻ (A ∪ B)) = sumCls (R ʻʻ A) ∪ sumCls (R ʻʻ B) := by
  rw [img_union']
  exact pm40_171.symm

/-- ✱40·32. \(\vdash.pʻRʻʻ\alpha\cup pʻRʻʻ\beta\subset pʻRʻʻ(\alpha\cap\beta)\) -/
theorem pm40_32 {R : Set α → β → Prop} {A B : Set β} :
    prodCls (R ʻʻ A) ∪ prodCls (R ʻʻ B) ⊆ prodCls (R ʻʻ (A ∩ B)) := by
  rintro x (hx | hx) G ⟨y, ⟨hyA, hyB⟩, hG⟩
  · exact hx G ⟨y, hyA, hG⟩
  · exact hx G ⟨y, hyB, hG⟩

/-- ✱40·33. \(\vdash . sʻRʻʻ(\alpha \cap \beta) \subset sʻRʻʻ\alpha \cap sʻRʻʻ\beta \quad[\text{*37·21.*40·161.*40·181}]\) -/
theorem pm40_33 {R : Set α → β → Prop} {A B : Set β} :
    sumCls (R ʻʻ (A ∩ B)) ⊆ sumCls (R ʻʻ A) ∩ sumCls (R ʻʻ B) := by
  rintro x ⟨G, ⟨y, ⟨hyA, hyB⟩, hG⟩, hx⟩
  exact ⟨⟨G, ⟨y, hyA, hG⟩, hx⟩, ⟨G, ⟨y, hyB, hG⟩, hx⟩⟩

/-- ✱40·35. \(\vdash . pʻRʻʻʻ\kappa = \hat{x}\{\beta \in \kappa . \supset_{\beta} . x \in Rʻʻ\beta\}\) -/
theorem pm40_35 {R : α → β → Prop} {K : Set (Set β)} :
    prodCls (R ʻʻʻ K) = {x | ∀ B, B ∈ K → x ∈ R ʻʻ B} := by
  ext x
  constructor
  · intro hx B hB
    exact hx _ ⟨B, hB, rfl⟩
  · rintro hx G ⟨B, hB, hG⟩
    obtain rfl : G = R ʻʻ B := hG
    exact hx B hB

/-- ✱40·36. \(\vdash . sʻRʻʻʻ\kappa = \hat{x}\{(\exists \beta) . \beta \in \kappa . x \in Rʻʻ\beta \} \quad [\text{Similar proof}]\) -/
theorem pm40_36 {R : α → β → Prop} {K : Set (Set β)} :
    sumCls (R ʻʻʻ K) = {x | ∃ B, B ∈ K ∧ x ∈ R ʻʻ B} := by
  ext x
  constructor
  · rintro ⟨G, ⟨B, hB, hG⟩, hx⟩
    obtain rfl : G = R ʻʻ B := hG
    exact ⟨B, hB, hx⟩
  · rintro ⟨B, hB, hx⟩
    exact ⟨R ʻʻ B, ⟨B, hB, rfl⟩, hx⟩

/-- ✱40·37. \(\vdash . Rʻʻpʻ\kappa \subset pʻRʻʻʻ\kappa\) -/
theorem pm40_37 {R : α → β → Prop} {K : Set (Set β)} : R ʻʻ prodCls K ⊆ prodCls (R ʻʻʻ K) := by
  rintro x ⟨y, hy, hxy⟩ G ⟨B, hB, hG⟩
  obtain rfl : G = R ʻʻ B := hG
  exact ⟨y, hy B hB, hxy⟩

/-- ✱40·38. \(\vdash . Rʻʻsʻ\kappa = sʻRʻʻʻ\kappa\) -/
theorem pm40_38 {R : α → β → Prop} {K : Set (Set β)} : R ʻʻ sumCls K = sumCls (R ʻʻʻ K) := by
  ext x
  constructor
  · rintro ⟨y, ⟨B, hB, hy⟩, hxy⟩
    exact ⟨R ʻʻ B, ⟨B, hB, rfl⟩, y, hy, hxy⟩
  · rintro ⟨G, ⟨B, hB, hG⟩, hx⟩
    obtain rfl : G = R ʻʻ B := hG
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨y, ⟨B, hB, hy⟩, hxy⟩

/-- ✱40·4. \(\vdash : \text{E} !! Rʻʻ\beta . \supset . sʻRʻʻ\beta = \hat{x}\{ (\exists y) . y \in \beta . x \in Rʻy \}\) -/
theorem pm40_4 {R : Set α → β → Prop} {B : Set β} :
    EE R B → sumCls (R ʻʻ B) = {x | ∃ y, y ∈ B ∧ Desc R y (fun G => x ∈ G)} := by
  intro hE
  ext x
  constructor
  · rintro ⟨G, ⟨y, hy, hG⟩, hx⟩
    exact ⟨y, hy, (desc_iff_exists (hE y hy)).2 ⟨G, hG, hx⟩⟩
  · rintro ⟨y, hy, hd⟩
    obtain ⟨G, hG, hx⟩ := (desc_iff_exists (hE y hy)).1 hd
    exact ⟨G, ⟨y, hy, hG⟩, hx⟩

/-- ✱40·41. \(\vdash : E‼Rʻʻ\beta .\supset. pʻRʻʻ\beta = \hat{x}\{ y \in \beta \supset_{y} x \in Rʻy\} \quad[\text{Similar proof}]\) -/
theorem pm40_41 {R : Set α → β → Prop} {B : Set β} :
    EE R B → prodCls (R ʻʻ B) = {x | ∀ y, y ∈ B → Desc R y (fun G => x ∈ G)} := by
  intro hE
  ext x
  constructor
  · intro hx y hy
    exact (desc_iff_forall (hE y hy)).2 fun G hG => hx G ⟨y, hy, hG⟩
  · rintro hx G ⟨y, hy, hG⟩
    exact (desc_iff_forall (hE y hy)).1 (hx y hy) G hG

/-- ✱40·42. \(\vdash : (x).Rʻx = Pʻx \cup Qʻx \supset sʻRʻʻ\alpha = sʻ(Pʻʻ\alpha \cup Qʻʻ\alpha) = sʻPʻʻ\alpha \cup sʻQʻʻ\alpha\)

**Status.** proved (reading): the e-text drops the dots of the enunciation; it is read
`⊢ : (x) . R'x = P'x ∪ Q'x . ⊃ . s'R''α = s'(P''α ∪ Q''α) = s'P''α ∪ s'Q''α`, the hypothesis
being the whole quantified proposition (as in the demonstration, `Hp . ⊃ . (x) . E!R'x …`), the
conclusion the chain of two identities (a conjunction, ✱13·03). In `R'x = P'x ∪ Q'x` the three
descriptions have, in order of occurrence, decreasing scopes (✱14·03 convention). -/
theorem pm40_42 {R P Q : Set α → β → Prop} {A : Set β} :
    (∀ x, Desc R x (fun G => Desc P x (fun H => Desc Q x (fun I => G = H ∪ I)))) →
      sumCls (R ʻʻ A) = sumCls (P ʻʻ A ∪ Q ʻʻ A) ∧
        sumCls (P ʻʻ A ∪ Q ʻʻ A) = sumCls (P ʻʻ A) ∪ sumCls (Q ʻʻ A) := by
  intro h
  refine ⟨?_, pm40_171.symm⟩
  ext z
  constructor
  · rintro ⟨G, ⟨y, hy, hG⟩, hz⟩
    obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h y
    have hGa : G = a := (ha G).1 hG
    rw [hGa, habc] at hz
    rcases hz with hz | hz
    · exact ⟨b, Or.inl ⟨y, hy, (hb b).2 rfl⟩, hz⟩
    · exact ⟨c, Or.inr ⟨y, hy, (hc c).2 rfl⟩, hz⟩
  · rintro ⟨G, ⟨y, hy, hG⟩ | ⟨y, hy, hG⟩, hz⟩
    · obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h y
      have hGb : G = b := (hb G).1 hG
      refine ⟨a, ⟨y, hy, (ha a).2 rfl⟩, ?_⟩
      rw [habc]
      exact Or.inl (hGb ▸ hz)
    · obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h y
      have hGc : G = c := (hc G).1 hG
      refine ⟨a, ⟨y, hy, (ha a).2 rfl⟩, ?_⟩
      rw [habc]
      exact Or.inr (hGc ▸ hz)

/-- ✱40·43. \(\vdash\colon\colon \text{E} ‼ Rʻʻ\beta \supset\colon\ldotp sʻRʻʻ\beta \subset \alpha. \equiv: y \in \beta \supset_{y}. Rʻy \subset \alpha\) -/
theorem pm40_43 {R : Set α → β → Prop} {B : Set β} {A : Set α} :
    EE R B → (sumCls (R ʻʻ B) ⊆ A ↔ ∀ y, y ∈ B → Desc R y (fun G => G ⊆ A)) := by
  intro hE
  constructor
  · intro h y hy
    exact (desc_iff_forall (hE y hy)).2 fun G hG x hx => h ⟨G, ⟨y, hy, hG⟩, hx⟩
  · rintro h x ⟨G, ⟨y, hy, hG⟩, hx⟩
    exact (desc_iff_forall (hE y hy)).1 (h y hy) G hG hx

/-- ✱40·44. \(\vdash \text{E}‼Rʻʻ\beta \supset \; \alpha \subset pʻRʻʻ\beta \equiv y \in \beta \supset_{y} \alpha \subset Rʻy\)

**Status.** proved (reading): the e-text drops all the dots of the enunciation; it is read, as
✱40·43 and the demonstration, `⊢ :: E!!R''β . ⊃ :. α ⊂ p'R''β . ≡ : y ∈ β . ⊃_y . α ⊂ R'y`. -/
theorem pm40_44 {R : Set α → β → Prop} {B : Set β} {A : Set α} :
    EE R B → (A ⊆ prodCls (R ʻʻ B) ↔ ∀ y, y ∈ B → Desc R y (fun G => A ⊆ G)) := by
  intro hE
  constructor
  · intro h y hy
    exact (desc_iff_forall (hE y hy)).2 fun G hG x hx => h hx G ⟨y, hy, hG⟩
  · rintro h x hx G ⟨y, hy, hG⟩
    exact (desc_iff_forall (hE y hy)).1 (h y hy) G hG hx

/-- ✱40·45. \(\vdash \colon\ldotp y \in \beta \supset_{y} Rʻy \subset Sʻy \supset sʻRʻʻ\beta \subset sʻSʻʻ\beta\)

**Status.** proved (reading): the e-text drops the dots of the enunciation; it is read
`⊢ :. y ∈ β . ⊃_y . R'y ⊂ S'y : ⊃ . s'R''β ⊂ s'S''β`, as the demonstration (`Hp . ⊃ …`) uses
it; in `R'y ⊂ S'y` the first description has the larger scope. -/
theorem pm40_45 {R S : Set α → β → Prop} {B : Set β} :
    (∀ y, y ∈ B → Desc R y (fun G => Desc S y (fun H => G ⊆ H))) →
      sumCls (R ʻʻ B) ⊆ sumCls (S ʻʻ B) := by
  rintro h x ⟨G, ⟨y, hy, hG⟩, hx⟩
  obtain ⟨a, ha, d, hd, had⟩ := h y hy
  have hGa : G = a := (ha G).1 hG
  exact ⟨d, ⟨y, hy, (hd d).2 rfl⟩, had (hGa ▸ hx)⟩

/-- ✱40·451. \(\vdash \colon\ldotp y \in \beta \supset_{y} Rʻy \subset Sʻy \supset pʻRʻʻ\beta \subset pʻSʻʻ\beta\)

**Status.** proved (reading): as ✱40·45, read
`⊢ :. y ∈ β . ⊃_y . R'y ⊂ S'y : ⊃ . p'R''β ⊂ p'S''β`. -/
theorem pm40_451 {R S : Set α → β → Prop} {B : Set β} :
    (∀ y, y ∈ B → Desc R y (fun G => Desc S y (fun H => G ⊆ H))) →
      prodCls (R ʻʻ B) ⊆ prodCls (S ʻʻ B) := by
  rintro h x hx H ⟨y, hy, hH⟩
  obtain ⟨a, ha, d, hd, had⟩ := h y hy
  have hHd : H = d := (hd H).1 hH
  rw [hHd]
  exact had (hx a ⟨y, hy, (ha a).2 rfl⟩)

/-- ✱40·5. \(\vdash.\, sʻ\overrightarrow{R}ʻʻ\beta = Rʻʻ\beta\) -/
theorem pm40_5 {R : α → β → Prop} {B : Set β} : sumCls (Rfwd R ʻʻ B) = R ʻʻ B := by
  ext x
  constructor
  · rintro ⟨G, ⟨y, hy, hG⟩, hx⟩
    obtain rfl : G = refs R y := hG
    exact ⟨y, hy, hx⟩
  · rintro ⟨y, hy, hx⟩
    exact ⟨refs R y, ⟨y, hy, rfl⟩, hx⟩

/-- ✱40·51. \(\vdash.\, pʻ\overrightarrow{R}ʻʻ\beta= \hat{x}\{y \in \beta.\, \supset_{y}. x R y\} \quad [\text{*32·12.*40·41.*32·18}]\) -/
theorem pm40_51 {R : α → β → Prop} {B : Set β} :
    prodCls (Rfwd R ʻʻ B) = {x | ∀ y, y ∈ B → R x y} := by
  ext x
  constructor
  · intro hx y hy
    exact hx (refs R y) ⟨y, hy, rfl⟩
  · rintro hx G ⟨y, hy, hG⟩
    obtain rfl : G = refs R y := hG
    exact hx y hy

/-- ✱40·52. \(\vdash. sʻ\overleftarrow{R}ʻʻ\beta = \overline{R}ʻʻ\beta \quad [\text{Proof as in *40·5}]\)

**Status.** proved (reading): transcription error of the e-text, which prints `R̄''β` (an overline)
for `R̆''β` (the converse, `\breve`), as in ✱40·61; `R̆''β` is the class of the relata of
members of `β` (✱37·1, ✱31·11), which is `s'R⃖''β`. -/
theorem pm40_52 {R : α → β → Prop} {B : Set α} : sumCls (Rbwd R ʻʻ B) = R˘ ʻʻ B := by
  ext y
  constructor
  · rintro ⟨G, ⟨x, hx, hG⟩, hy⟩
    obtain rfl : G = rels R x := hG
    exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨rels R x, ⟨x, hx, rfl⟩, hy⟩

/-- ✱40·53. \(\vdash.\, pʻ\overleftarrow{R}ʻʻ\beta= \hat{y}\{x \in \beta.\, \supset_{x}. x R y\} \quad [\text{Proof as in *40·51}]\) -/
theorem pm40_53 {R : α → β → Prop} {B : Set α} :
    prodCls (Rbwd R ʻʻ B) = {y | ∀ x, x ∈ B → R x y} := by
  ext y
  constructor
  · intro hy x hx
    exact hy (rels R x) ⟨x, hx, rfl⟩
  · rintro hy G ⟨x, hx, hG⟩
    obtain rfl : G = rels R x := hG
    exact hy x hx

/-- ✱40·54. \(\vdash. pʻ\overrightarrow{R}ʻʻ\beta= \hat{x}(\beta \subset \overleftarrow{R}ʻx) \quad [\text{*40·51.*32·181}]\) -/
theorem pm40_54 {R : α → β → Prop} {B : Set β} :
    prodCls (Rfwd R ʻʻ B) = {x | B ⊆ rels R x} := by
  rw [pm40_51]
  ext x
  exact ⟨fun h y hy => h y hy, fun h y hy => h hy⟩

/-- ✱40·55. \(\vdash. pʻ\overleftarrow{R}ʻʻ\alpha= \hat{y}(\alpha \subset \overrightarrow{R}ʻy) \quad [\text{*40·53.*32·18}]\) -/
theorem pm40_55 {R : α → β → Prop} {A : Set α} :
    prodCls (Rbwd R ʻʻ A) = {y | A ⊆ refs R y} := by
  rw [pm40_53]
  ext y
  exact ⟨fun h x hx => h x hx, fun h x hx => h hx⟩

/-- ✱40·56. \(\vdash.\, sʻCʻʻ\lambda = Fʻʻ\lambda \quad [*33·5.*40·5]\) -/
theorem pm40_56 {L : Set (α → α → Prop)} : sumCls (C ʻʻ L) = F ʻʻ L := by
  ext x
  constructor
  · rintro ⟨G, ⟨R, hR, hG⟩, hx⟩
    obtain rfl : G = fld R := hG
    exact ⟨R, hR, hx⟩
  · rintro ⟨R, hR, hx⟩
    exact ⟨fld R, ⟨R, hR, rfl⟩, hx⟩

/-- ✱40·57. \(\vdash.\, sʻCʻʻ\lambda = sʻ(\text{D}ʻʻ\lambda \cup \text{ᗡ}ʻʻ\lambda)= sʻDʻʻ\lambda \cup sʻ\text{ᗡ}ʻʻ\lambda \quad [\text{*40·42.*33·16}]\) -/
theorem pm40_57 {L : Set (α → α → Prop)} :
    sumCls (C ʻʻ L) = sumCls (D ʻʻ L ∪ Dcnv ʻʻ L) ∧
      sumCls (D ʻʻ L ∪ Dcnv ʻʻ L) = sumCls (D ʻʻ L) ∪ sumCls (Dcnv ʻʻ L) := by
  refine ⟨?_, pm40_171.symm⟩
  ext x
  constructor
  · rintro ⟨G, ⟨R, hR, hG⟩, hx⟩
    obtain rfl : G = fld R := hG
    obtain ⟨y, hxy | hyx⟩ := hx
    · exact ⟨dom R, Or.inl ⟨R, hR, rfl⟩, y, hxy⟩
    · exact ⟨codom R, Or.inr ⟨R, hR, rfl⟩, y, hyx⟩
  · rintro ⟨G, ⟨R, hR, hG⟩ | ⟨R, hR, hG⟩, hx⟩
    · obtain rfl : G = dom R := hG
      obtain ⟨y, hxy⟩ := hx
      exact ⟨fld R, ⟨R, hR, rfl⟩, y, Or.inl hxy⟩
    · obtain rfl : G = codom R := hG
      obtain ⟨y, hyx⟩ := hx
      exact ⟨fld R, ⟨R, hR, rfl⟩, y, Or.inr hyx⟩

/-- ✱40·6. \(\vdash.\, pʻ\overrightarrow{R}ʻʻ\Lambda = \text{V}. pʻ\overleftarrow{R}ʻʻ\Lambda = \text{V} \quad [\text{*37·29.*40·2}]\) -/
theorem pm40_6 {R : α → β → Prop} :
    prodCls (Rfwd R ʻʻ Λ) = V ∧ prodCls (Rbwd R ʻʻ Λ) = V := by
  refine ⟨?_, ?_⟩ <;> ext x <;> refine ⟨fun _ => rfl, ?_⟩ <;> rintro - G ⟨y, hy, -⟩ <;>
    simp [Null_eq_empty] at hy

/-- ✱40·61. \(\vdash: \exists!\beta. \supset. pʻ\overrightarrow{R}ʻʻ\beta \subset Rʻʻ\beta. pʻ\overleftarrow{R}ʻʻ\beta \subset \overline{R}ʻʻ\beta\)

**Status.** proved (reading): transcription error of the e-text, which prints `R̄''β` (an overline)
for `R̆''β`, as in ✱40·52 (the demonstration obtains it from `s'R⃖''β`). The relation is
homogeneous, since `β` is a class both of relata (in `R⃗''β`) and of referents (in `R⃖''β`). -/
theorem pm40_61 {R : α → α → Prop} {B : Set α} :
    B.Nonempty → prodCls (Rfwd R ʻʻ B) ⊆ R ʻʻ B ∧ prodCls (Rbwd R ʻʻ B) ⊆ R˘ ʻʻ B := by
  rintro ⟨y, hy⟩
  exact ⟨fun x hx => ⟨y, hy, hx (refs R y) ⟨y, hy, rfl⟩⟩,
    fun x hx => ⟨y, hy, hx (rels R y) ⟨y, hy, rfl⟩⟩⟩

/-- ✱40·62. \[\begin{align}&\vdash:\exists!\beta.\supset.pʻ\overrightarrow{R}ʻʻ\beta\subset CʻR.pʻ\overleftarrow{R}ʻʻ\beta\subset CʻR\\ &[\text{*40·61.*37·15·16.*33·161}]\end{align}\] -/
theorem pm40_62 {R : α → α → Prop} {B : Set α} :
    B.Nonempty → prodCls (Rfwd R ʻʻ B) ⊆ fld R ∧ prodCls (Rbwd R ʻʻ B) ⊆ fld R := by
  rintro ⟨y, hy⟩
  exact ⟨fun x hx => ⟨y, Or.inl (hx (refs R y) ⟨y, hy, rfl⟩)⟩,
    fun x hx => ⟨y, Or.inr (hx (rels R y) ⟨y, hy, rfl⟩)⟩⟩

/-- ✱40·63. \(\vdash:\exists!\beta-\text{ᗡ}ʻR.\supset.pʻ\overrightarrow{R}ʻʻ\beta=\Lambda\) -/
theorem pm40_63 {R : α → β → Prop} {B : Set β} :
    (B \ codom R).Nonempty → prodCls (Rfwd R ʻʻ B) = Λ := by
  rintro ⟨y, hyB, hy⟩
  rw [Null_eq_empty]
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hy ⟨x, hx (refs R y) ⟨y, hyB, rfl⟩⟩

/-- ✱40·64. \(\vdash:\exists!\beta-\text{D}ʻR.\supset.pʻ\overleftarrow{R}ʻʻ\beta=\Lambda \quad [\text{Proof as in *40·63}]\) -/
theorem pm40_64 {R : α → β → Prop} {B : Set α} :
    (B \ dom R).Nonempty → prodCls (Rbwd R ʻʻ B) = Λ := by
  rintro ⟨x, hxB, hx⟩
  rw [Null_eq_empty]
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  exact hx ⟨y, hy (rels R x) ⟨x, hxB, rfl⟩⟩

/-- ✱40·65. \(\vdash:\exists!\beta-CʻR.\supset.pʻ\overrightarrow{R}ʻʻ\beta=\Lambda.pʻ\overleftarrow{R}ʻʻ\beta=\Lambda \quad [\text{*40·63·64.*33·16}]\) -/
theorem pm40_65 {R : α → α → Prop} {B : Set α} :
    (B \ fld R).Nonempty → prodCls (Rfwd R ʻʻ B) = Λ ∧ prodCls (Rbwd R ʻʻ B) = Λ := by
  rintro ⟨y, hyB, hy⟩
  refine ⟨pm40_63 ⟨y, hyB, ?_⟩, pm40_64 ⟨y, hyB, ?_⟩⟩
  · rintro ⟨x, h⟩
    exact hy ⟨x, Or.inr h⟩
  · rintro ⟨x, h⟩
    exact hy ⟨x, Or.inl h⟩

/-- ✱40·66. \(\vdash\;\;\alpha\subset pʻ\overrightarrow{R}ʻʻ\beta.\equiv:x\in\alpha.y\in\beta.\supset_{x,y}.xRy\) -/
theorem pm40_66 {R : α → β → Prop} {A : Set α} {B : Set β} :
    A ⊆ prodCls (Rfwd R ʻʻ B) ↔ ∀ x y, x ∈ A ∧ y ∈ B → R x y := by
  rw [pm40_51]
  exact ⟨fun h x y hxy => h hxy.1 y hxy.2, fun h x hx y hy => h x y ⟨hx, hy⟩⟩

/-- ✱40·67. \(\vdash\;\;\beta\subset pʻ\overleftarrow{R}ʻʻ\alpha.\equiv:x\in\alpha.y\in\beta.\supset_{x,y}.xRy\equiv.\alpha\subset pʻ\overrightarrow{R}ʻʻ\beta \quad [\text{Proof as in *40·66}]\)

**Status.** proved (reading): the e-text loses the dots before the second `≡` (as printed, the
formula does not parse); it is read as the chain of equivalences (✱4·02)
`⊢ :. β ⊂ p'R⃖''α . ≡ : x ∈ α . y ∈ β . ⊃_{x,y} . xRy : ≡ . α ⊂ p'R⃗''β`, the conjunction of
its two links. -/
theorem pm40_67 {R : α → β → Prop} {A : Set α} {B : Set β} :
    (B ⊆ prodCls (Rbwd R ʻʻ A) ↔ ∀ x y, x ∈ A ∧ y ∈ B → R x y) ∧
      ((∀ x y, x ∈ A ∧ y ∈ B → R x y) ↔ A ⊆ prodCls (Rfwd R ʻʻ B)) := by
  refine ⟨?_, pm40_66.symm⟩
  rw [pm40_53]
  exact ⟨fun h x y hxy => h hxy.2 x hxy.1, fun h y hy x hx => h x y ⟨hx, hy⟩⟩

/-- ✱40·68. \( \vdash.\alpha\cap pʻ\overleftarrow{P}ʻʻ\alpha\subset\breve{P}ʻʻpʻ\overleftarrow{P}ʻʻ\alpha\) -/
theorem pm40_68 {P : α → α → Prop} {A : Set α} :
    A ∩ prodCls (Rbwd P ʻʻ A) ⊆ P˘ ʻʻ prodCls (Rbwd P ʻʻ A) := by
  rintro x ⟨hxA, hx⟩
  exact ⟨x, hx, hx (rels P x) ⟨x, hxA, rfl⟩⟩

/-- ✱40·681. \(\vdash.\alpha\cap pʻ\overrightarrow{P}ʻʻ\alpha\subset Pʻʻpʻ\overrightarrow{P}ʻʻ\alpha \quad [\text{Proof as in *40·68}]\) -/
theorem pm40_681 {P : α → α → Prop} {A : Set α} :
    A ∩ prodCls (Rfwd P ʻʻ A) ⊆ P ʻʻ prodCls (Rfwd P ʻʻ A) := by
  rintro x ⟨hxA, hx⟩
  exact ⟨x, hx, hx (refs P x) ⟨x, hxA, rfl⟩⟩

/-- ✱40·682. \(\vdash : \exists! \alpha \cap pʻ \overleftarrow{P} ʻʻ \beta. \supset. \beta \subset Pʻʻ \alpha \) -/
theorem pm40_682 {P : α → β → Prop} {A : Set β} {B : Set α} :
    (A ∩ prodCls (Rbwd P ʻʻ B)).Nonempty → B ⊆ P ʻʻ A := by
  rintro ⟨x, hxA, hx⟩ y hy
  exact ⟨x, hxA, hx (rels P y) ⟨y, hy, rfl⟩⟩

/-- ✱40·69. \(\vdash : \exists! Cʻ \overrightarrow{P} \cap pʻ \overrightarrow{P} ʻʻ \alpha .\equiv. \dot{\exists}! P . \exists! pʻ \overrightarrow{P} ʻʻ \alpha\)

**Status.** proved (reading): transcription error of the e-text in the arrows of the
enunciation, which is read `⊢ : ∃! C'P ∩ p'P⃖''α . ≡ . ∃̇!P . ∃! p'P⃖''α`. (i) The e-text prints
`C'P⃗`, which is not significant (`P⃗` relates classes to terms and has no field); the
demonstration has `C'P` (✱33·24, ✱40·62). (ii) The demonstration, as corrected by the erratum
(Additional Errata to Vol. I, p. 329: in the *Dem.*, for `P⃗` read `P⃖`, 3 times), proves the
proposition with `P⃖`: its steps (2)–(4) conclude `∃̇!P . ∃! p'P⃖''α . ⊃ . ∃! C'P ∩ p'P⃖''α`, and
"(1).(4) ⊃ Prop"; the erratum corrects the demonstration to agree with an enunciation in `P⃖`.
(iii) The only later use in Vols. I–II, ✱213·18 (step (4): `(2).(3).*40·69 . ⊃ … ∃! C'P ∩ p'P⃖''α` from
`∃! p'P⃖''α` and `∃̇!P`), uses it with `P⃖`. The form with `P⃗` throughout (also true) is
`pm40_69_aux_fwd`. -/
theorem pm40_69 {P : α → α → Prop} {A : Set α} :
    (fld P ∩ prodCls (Rbwd P ʻʻ A)).Nonempty ↔ rEx P ∧ (prodCls (Rbwd P ʻʻ A)).Nonempty := by
  constructor
  · rintro ⟨x, ⟨y, hxy | hyx⟩, hx⟩
    · exact ⟨⟨x, y, hxy⟩, x, hx⟩
    · exact ⟨⟨y, x, hyx⟩, x, hx⟩
  · rintro ⟨⟨a, b, hab⟩, x, hx⟩
    by_cases hA : A.Nonempty
    · obtain ⟨y, hy⟩ := hA
      exact ⟨x, ⟨y, Or.inr (hx (rels P y) ⟨y, hy, rfl⟩)⟩, hx⟩
    · refine ⟨a, ⟨b, Or.inl hab⟩, ?_⟩
      rintro G ⟨y, hy, -⟩
      exact absurd ⟨y, hy⟩ hA

/-- The form of PM ✱40·69 with `P⃗` throughout (the arrows as the e-text prints them, with `C'P`
for `C'P⃗`): `∃! C'P ∩ p'P⃗''α . ≡ . ∃̇!P . ∃! p'P⃗''α`. Also true; see ✱40·69. -/
theorem pm40_69_aux_fwd {P : α → α → Prop} {A : Set α} :
    (fld P ∩ prodCls (Rfwd P ʻʻ A)).Nonempty ↔ rEx P ∧ (prodCls (Rfwd P ʻʻ A)).Nonempty := by
  constructor
  · rintro ⟨x, ⟨y, hxy | hyx⟩, hx⟩
    · exact ⟨⟨x, y, hxy⟩, x, hx⟩
    · exact ⟨⟨y, x, hyx⟩, x, hx⟩
  · rintro ⟨⟨a, b, hab⟩, x, hx⟩
    by_cases hA : A.Nonempty
    · obtain ⟨y, hy⟩ := hA
      exact ⟨x, ⟨y, Or.inl (hx (refs P y) ⟨y, hy, rfl⟩)⟩, hx⟩
    · refine ⟨a, ⟨b, Or.inl hab⟩, ?_⟩
      rintro G ⟨y, hy, -⟩
      exact absurd ⟨y, hy⟩ hA

/-- ✱40·7. \(\vdash . sʻ \alpha \unicode{x2640}_{,,} ʻʻ \beta = \hat{z} \{( \exists x, y ). x \in \alpha . y \in \beta . z = x \, \unicode{x2640} y\}\) -/
theorem pm40_7 {f : α → β → γ} {A : Set α} {B : Set β} :
    sumCls (opL (opImg f) A ʻʻ B) = {z | ∃ x y, (x ∈ A ∧ y ∈ B) ∧ z = f x y} := by
  ext z
  constructor
  · rintro ⟨G, ⟨y, hy, hG⟩, hz⟩
    obtain rfl : G = opImg f A y := hG
    obtain ⟨x, hx, hzx⟩ := hz
    exact ⟨x, y, ⟨hx, hy⟩, hzx⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, hz⟩
    exact ⟨opImg f A y, ⟨y, hy, rfl⟩, x, hx, hz⟩

/-- ✱40·71. \(\vdash . sʻ\unicode{x2640}_{,,}yʻʻ\kappa = (sʻ\kappa)\unicode{x2640}_{,,}y = \unicode{x2640}ʻʻ sʻ\kappa\)

**Status.** proved (reading): transcription error of the e-text, which prints `♀''s'κ` (the `y`
dropped) for `♀y''s'κ`, as in the demonstration (`= ♀y''s'κ`, ✱40·38, ✱38·31). The relation
`♀,,y` (of `α ♀,, y` to `α`, ✱38·02 with `♀,,` for `♀`) is `opR (opImg f) y`. -/
theorem pm40_71 {f : α → β → γ} {K : Set (Set α)} {y : β} :
    sumCls (opR (opImg f) y ʻʻ K) = opImg f (sumCls K) y ∧
      opImg f (sumCls K) y = opR f y ʻʻ sumCls K := by
  refine ⟨?_, rfl⟩
  ext z
  constructor
  · rintro ⟨G, ⟨A, hA, hG⟩, hz⟩
    obtain rfl : G = opImg f A y := hG
    obtain ⟨x, hx, hzx⟩ := hz
    exact ⟨x, ⟨A, hA, hx⟩, hzx⟩
  · rintro ⟨x, ⟨A, hA, hx⟩, hzx⟩
    exact ⟨opImg f A y, ⟨A, hA, rfl⟩, x, hx, hzx⟩

/-- ✱40·8. \(\vdash\colon\ldotp \alpha \epsilon \kappa . \supset_{\alpha}. \breve{R}ʻʻ\alpha \subset \alpha : \supset . \breve{R}ʻʻ sʻ\kappa \subset sʻ\kappa\) -/
theorem pm40_8 {R : α → α → Prop} {K : Set (Set α)} :
    (∀ A, A ∈ K → R˘ ʻʻ A ⊆ A) → R˘ ʻʻ sumCls K ⊆ sumCls K := by
  rintro h y ⟨x, ⟨G, hG, hx⟩, hxy⟩
  exact ⟨G, hG, h G hG ⟨x, hx, hxy⟩⟩

/-- ✱40·81. \(\vdash\colon\ldotp \alpha \epsilon \kappa . \supset_{\alpha}. \breve{R}ʻʻ \alpha \subset \alpha : \supset \breve{R}ʻʻ pʻ \kappa \subset pʻ \kappa\)

(In the e-text this proposition is printed after the demonstration of ✱40·8 and has no entry of
its own; it is the analogue of ✱40·8 for products, read with the dots of ✱40·8.) -/
theorem pm40_81 {R : α → α → Prop} {K : Set (Set α)} :
    (∀ A, A ∈ K → R˘ ʻʻ A ⊆ A) → R˘ ʻʻ prodCls K ⊆ prodCls K := by
  rintro h y ⟨x, hx, hxy⟩ G hG
  exact h G hG ⟨x, hx G hG, hxy⟩

/-!
## [✱41] The product and sum of a class of relations

*(Vol. 1, p. 331)*

> *Summary of* *41.
>
> The propositions to be given in this number, down to *41·3 exclusive, are the analogues of those of *40, excluding those from *40·3 onwards, which have no analogues. Proofs will not be given, in this number, when they are exactly analogous to those of propositions with the same decimal part in *40. The smaller importance of \(\dot{p}ʻ\lambda\) and \(\dot{s}ʻ\lambda\), as compared with \(pʻ\lambda\) and \(sʻ\lambda\), is illustrated by the smaller number of propositions in *41 as compared with *40.
>
> Our definitions are
>
> *41·01. \(\dot{p}ʻ\lambda = \hat{x}\hat{y}\{R \in \lambda .\supset_{R}. xRy\} \quad \text{Df}\)

**Lean reading.** A class of relations `λ` is `L : Set (α → β → Prop)`; the Dfs ✱41·01·02 are the
Lean definitions `prodRel L` (`ṗ'λ`) and `sumRel L` (`ṡ'λ`), whose defining equations hold by
`rfl`. The dotted signs of ✱23 and ✱25 are `⪽`, `⩀`, `⊍`, `rV`, `rNull`, `rEx`; `Λ` in
`λ = Λ` is the null class of relations. `Cnv'P` is `P˘` (`desc_Cnv`), `Cnv''λ` is `Cnv ʻʻ L`,
and `D'R`, `ᗡ'R`, `C'R` are `dom R`, `codom R`, `fld R`. Where `ṗ`, `ṡ` occur as relations
(`ṗ''κ`, ✱41·32·33) they are the relations of `ṗ'λ`, `ṡ'λ` to `λ`, `graph prodRel` and
`graph sumRel`. The relations `α↿`, `↾α`, `⥏α`, `M↾`, `↿M` of ✱41·34–·351 are ✱38·01·02 applied
to `↿`, `↾`, `⥏`: `opL dres A`, `opR cres A`, `opR fres A`, `opL cres M`, `opR dres M`; and
`λ |,,` (✱41·5·51) is `opL (opImg relProd) L`. In ✱41·6 the three descriptions `P'y`, `Q'y`,
`R'y` of arbitrary relations are kept as `Desc`, the first having the largest scope.

**Status.** proved (all propositions; ✱41·01·02 definition; ✱41·34 proved (reading): e-text
transcription error, see its docstring).
-/

/-- ✱41·02 (Df). \(\dot{s}ʻ\lambda = \hat{x}\hat{y}\{(\exists R) . R \in \lambda . xRy\} \quad \text{Df}\) -/
theorem pm41_02 {L : Set (α → β → Prop)} : sumRel L = fun x y => ∃ R, R ∈ L ∧ R x y := rfl

/-- ✱41·01 (Df). \(\dot{p}ʻ\lambda = \hat{x}\hat{y}(R \in \lambda .\supset_{R}. xRy) \quad \text{Df}\) -/
theorem pm41_01 {L : Set (α → β → Prop)} : prodRel L = fun x y => ∀ R, R ∈ L → R x y := rfl

/-- ✱41·1. \(\vdash \colon\ldotp x(\dot{p}ʻ\lambda)y .\equiv: R \in \lambda .\supset_{R}. xRy\) -/
theorem pm41_1 {L : Set (α → β → Prop)} {x : α} {y : β} :
    prodRel L x y ↔ ∀ R, R ∈ L → R x y := Iff.rfl

/-- ✱41·11. \(\vdash :x(\dot{s}ʻ\lambda)y .\equiv. (\exists R) . R \in \lambda . xRy\) -/
theorem pm41_11 {L : Set (α → β → Prop)} {x : α} {y : β} :
    sumRel L x y ↔ ∃ R, R ∈ L ∧ R x y := Iff.rfl

/-- ✱41·12. \(\vdash : R \in \lambda .\supset. \dot{p}ʻ\lambda \unicode{x2abd} R\) -/
theorem pm41_12 {L : Set (α → β → Prop)} {R : α → β → Prop} : R ∈ L → prodRel L ⪽ R :=
  fun h _ _ hxy => hxy R h

/-- ✱41·13. \(\vdash : R \in \lambda .\supset. R \unicode{x2abd} \dot{s}ʻ\lambda\) -/
theorem pm41_13 {L : Set (α → β → Prop)} {R : α → β → Prop} : R ∈ L → R ⪽ sumRel L :=
  fun h _ _ hxy => ⟨R, h, hxy⟩

/-- ✱41·14. \(\vdash:R\in \lambda.x(\dot{p}ʻ\lambda)y.\supset.xRy\) -/
theorem pm41_14 {L : Set (α → β → Prop)} {R : α → β → Prop} {x : α} {y : β} :
    R ∈ L ∧ prodRel L x y → R x y :=
  fun h => h.2 R h.1

/-- ✱41·141. \(\vdash:R\in \lambda.xRy.\supset.x(\dot{s}ʻ\lambda)y\) -/
theorem pm41_141 {L : Set (α → β → Prop)} {R : α → β → Prop} {x : α} {y : β} :
    R ∈ L ∧ R x y → sumRel L x y :=
  fun h => ⟨R, h.1, h.2⟩

/-- ✱41·15. \(\vdash\colon\ldotp S\unicode{x2abd}\dot{p}ʻ\lambda.\equiv:R\in \lambda.\supset_{R}.S\unicode{x2abd}R\) -/
theorem pm41_15 {L : Set (α → β → Prop)} {S : α → β → Prop} :
    S ⪽ prodRel L ↔ ∀ R, R ∈ L → S ⪽ R :=
  ⟨fun h R hR x y hxy => h x y hxy R hR, fun h x y hxy R hR => h R hR x y hxy⟩

/-- ✱41·151. \(\vdash\colon\ldotp \dot{s}ʻ\lambda\unicode{x2abd}S.\equiv:R\in \lambda.\supset_{R}.R\unicode{x2abd}S\) -/
theorem pm41_151 {L : Set (α → β → Prop)} {S : α → β → Prop} :
    sumRel L ⪽ S ↔ ∀ R, R ∈ L → R ⪽ S := by
  constructor
  · intro h R hR x y hxy
    exact h x y ⟨R, hR, hxy⟩
  · rintro h x y ⟨R, hR, hxy⟩
    exact h R hR x y hxy

/-- ✱41·16. \(\vdash:\lambda\subset \mu.\supset.\dot{p}ʻ\mu\unicode{x2abd}\dot{p}ʻ\lambda\) -/
theorem pm41_16 {L M : Set (α → β → Prop)} : L ⊆ M → prodRel M ⪽ prodRel L :=
  fun h _ _ hxy R hR => hxy R (h hR)

/-- ✱41·161. \(\vdash:\lambda\subset \mu.\supset.\dot{s}ʻ\lambda\unicode{x2abd}\dot{s}ʻ\mu\) -/
theorem pm41_161 {L M : Set (α → β → Prop)} : L ⊆ M → sumRel L ⪽ sumRel M := by
  rintro h x y ⟨R, hR, hxy⟩
  exact ⟨R, h hR, hxy⟩

/-- ✱41·17. \(\vdash.\dot{p}ʻ\lambda\unicode{x228d}\dot{p}ʻ\mu\unicode{x2abd}\dot{p}ʻ(\lambda\cap \mu)\) -/
theorem pm41_17 {L M : Set (α → β → Prop)} : prodRel L ⊍ prodRel M ⪽ prodRel (L ∩ M) := by
  rintro x y (h | h) R ⟨hL, hM⟩
  · exact h R hL
  · exact h R hM

/-- ✱41·171. \(\vdash.\dot{s}ʻ\lambda\unicode{x228d}\dot{s}ʻ\mu=\dot{s}ʻ(\lambda\cup \mu)\) -/
theorem pm41_171 {L M : Set (α → β → Prop)} : sumRel L ⊍ sumRel M = sumRel (L ∪ M) := by
  rw [rel_eq_iff]
  intro x y
  constructor
  · rintro (⟨R, hR, h⟩ | ⟨R, hR, h⟩)
    · exact ⟨R, Or.inl hR, h⟩
    · exact ⟨R, Or.inr hR, h⟩
  · rintro ⟨R, hR | hR, h⟩
    · exact Or.inl ⟨R, hR, h⟩
    · exact Or.inr ⟨R, hR, h⟩

/-- ✱41·18. \(\vdash.\dot{p}ʻ(\lambda\cup \mu)=\dot{p}ʻ\lambda\dot{\cap}\dot{p}ʻ\mu\) -/
theorem pm41_18 {L M : Set (α → β → Prop)} : prodRel (L ∪ M) = prodRel L ⩀ prodRel M := by
  rw [rel_eq_iff]
  intro x y
  constructor
  · intro h
    exact ⟨fun R hR => h R (Or.inl hR), fun R hR => h R (Or.inr hR)⟩
  · rintro ⟨hL, hM⟩ R (hR | hR)
    · exact hL R hR
    · exact hM R hR

/-- ✱41·181. \(\vdash.\dot{s}ʻ(\lambda\cap \mu)\unicode{x2abd}\dot{s}ʻ\lambda\dot{\cap}\dot{s}ʻ\mu\) -/
theorem pm41_181 {L M : Set (α → β → Prop)} : sumRel (L ∩ M) ⪽ sumRel L ⩀ sumRel M := by
  rintro x y ⟨R, ⟨hL, hM⟩, h⟩
  exact ⟨⟨R, hL, h⟩, ⟨R, hM, h⟩⟩

/-- ✱41·19. \(\vdash\colon\colon x(\dot{s}ʻ\lambda)y.\equiv\colon\ldotp R\in \lambda.\supset_{R}.R\unicode{x2abd}S:\supset_{S}.xSy\) -/
theorem pm41_19 {L : Set (α → β → Prop)} {x : α} {y : β} :
    sumRel L x y ↔ ∀ S, (∀ R, R ∈ L → R ⪽ S) → S x y := by
  constructor
  · rintro ⟨R, hR, h⟩ S hS
    exact hS R hR x y h
  · intro h
    exact h (sumRel L) fun R hR x y hxy => ⟨R, hR, hxy⟩

/-- ✱41·2. \(\vdash:\lambda=\Lambda.\supset.\dot{p}ʻ\lambda=\dot{\text{V}}\) -/
theorem pm41_2 {L : Set (α → β → Prop)} : L = Λ → prodRel L = rV := by
  rintro rfl
  rw [rel_eq_iff]
  intro x y
  refine ⟨fun _ => ⟨rfl, rfl⟩, fun _ R hR => ?_⟩
  simp [Null_eq_empty] at hR

/-- ✱41·21. \(\vdash:\lambda=\Lambda.\supset.\dot{s}ʻ\lambda=\dot{\Lambda}\) -/
theorem pm41_21 {L : Set (α → β → Prop)} : L = Λ → sumRel L = rNull := by
  rintro rfl
  rw [rel_eq_iff]
  intro x y
  refine ⟨?_, fun h => (rNull_apply x y h).elim⟩
  rintro ⟨R, hR, -⟩
  simp [Null_eq_empty] at hR

/-- ✱41·22. \(\vdash:\dot{\Lambda}\in \lambda.\supset.\dot{p}ʻ\lambda=\dot{\Lambda}\) -/
theorem pm41_22 {L : Set (α → β → Prop)} : rNull ∈ L → prodRel L = rNull := by
  intro h
  rw [rel_eq_iff]
  intro x y
  exact ⟨fun hxy => hxy rNull h, fun h' => (rNull_apply x y h').elim⟩

/-- ✱41·221. \(\vdash:\dot{\text{V}}\in \lambda.\supset.\dot{s}ʻ\lambda=\dot{\text{V}}\) -/
theorem pm41_221 {L : Set (α → β → Prop)} : rV ∈ L → sumRel L = rV := by
  intro h
  rw [rel_eq_iff]
  intro x y
  exact ⟨fun _ => ⟨rfl, rfl⟩, fun hv => ⟨rV, h, hv⟩⟩

/-- ✱41·23. \(\vdash:\exists !\lambda.\supset.\dot{p}ʻ\lambda\unicode{x2abd}\dot{s}ʻ\lambda\) -/
theorem pm41_23 {L : Set (α → β → Prop)} : L.Nonempty → prodRel L ⪽ sumRel L := by
  rintro ⟨R, hR⟩ x y hxy
  exact ⟨R, hR, hxy R hR⟩

/-- ✱41·24. \(\vdash\colon\ldotp \exists !\lambda:R\in \lambda.\supset_{R}.S\unicode{x2abd}R:\supset.S\unicode{x2abd}\dot{s}ʻ\lambda\) -/
theorem pm41_24 {L : Set (α → β → Prop)} {S : α → β → Prop} :
    L.Nonempty ∧ (∀ R, R ∈ L → S ⪽ R) → S ⪽ sumRel L := by
  rintro ⟨⟨R, hR⟩, h⟩ x y hxy
  exact ⟨R, hR, h R hR x y hxy⟩

/-- ✱41·25. \(\vdash:x(\dot{s}ʻ\lambda)y.\equiv.\exists !\lambda\cap \hat{R}(xRy)\) -/
theorem pm41_25 {L : Set (α → β → Prop)} {x : α} {y : β} :
    sumRel L x y ↔ (L ∩ {R | R x y}).Nonempty := by
  constructor
  · rintro ⟨R, hR, h⟩
    exact ⟨R, hR, h⟩
  · rintro ⟨R, hR, h⟩
    exact ⟨R, hR, h⟩

/-- ✱41·26. \(\vdash:\dot{\exists}!\dot{s}ʻ\lambda.\equiv.(\exists R).R\in \lambda.\dot{\exists}!R\) -/
theorem pm41_26 {L : Set (α → β → Prop)} : rEx (sumRel L) ↔ ∃ R, R ∈ L ∧ rEx R := by
  constructor
  · rintro ⟨x, y, R, hR, h⟩
    exact ⟨R, hR, x, y, h⟩
  · rintro ⟨R, hR, x, y, h⟩
    exact ⟨x, y, R, hR, h⟩

/-- ✱41·27. \(\vdash\colon\ldotp P\dot{\cap}\dot{s}ʻ\lambda=\dot{\Lambda}.\equiv:R\in \lambda.\supset_{R}.P\dot{\cap}R=\dot{\Lambda}\) -/
theorem pm41_27 {L : Set (α → β → Prop)} {P : α → β → Prop} :
    P ⩀ sumRel L = rNull ↔ ∀ R, R ∈ L → P ⩀ R = rNull := by
  constructor
  · intro h R hR
    rw [rel_eq_iff]
    intro x y
    refine ⟨fun hxy => ?_, fun h' => (rNull_apply x y h').elim⟩
    exact (rNull_apply x y ((rel_eq_iff.1 h x y).1 ⟨hxy.1, R, hR, hxy.2⟩)).elim
  · intro h
    rw [rel_eq_iff]
    intro x y
    refine ⟨?_, fun h' => (rNull_apply x y h').elim⟩
    rintro ⟨hP, R, hR, hxy⟩
    exact (rel_eq_iff.1 (h R hR) x y).1 ⟨hP, hxy⟩

/-- ✱41·3. \(\vdash.\text{Cnv}ʻ\dot{p}ʻ\lambda =\dot{p}ʻ\text{Cnv}ʻʻ\lambda\) -/
theorem pm41_3 {L : Set (α → β → Prop)} : (prodRel L)˘ = prodRel (Cnv ʻʻ L) := by
  rw [rel_eq_iff]
  intro y x
  constructor
  · rintro h Q ⟨P, hP, hQ⟩
    exact (hQ y x).2 (h P hP)
  · intro h P hP
    exact h (P˘) ⟨P, hP, fun _ _ => Iff.rfl⟩

/-- ✱41·31. \(\vdash.\text{Cnv}ʻ\dot{s}ʻ\lambda=\dot{s}ʻ\text{Cnv}ʻʻ\lambda \quad[\text{Proof as in *41·3}]\) -/
theorem pm41_31 {L : Set (α → β → Prop)} : (sumRel L)˘ = sumRel (Cnv ʻʻ L) := by
  rw [rel_eq_iff]
  intro y x
  constructor
  · rintro ⟨P, hP, h⟩
    exact ⟨P˘, ⟨P, hP, fun _ _ => Iff.rfl⟩, h⟩
  · rintro ⟨Q, ⟨P, hP, hQ⟩, h⟩
    exact ⟨P, hP, (hQ y x).1 h⟩

/-- ✱41·32. \(\vdash.\text{Cnv}ʻʻ\dot{p}ʻʻ\kappa =\dot{p}ʻʻ\text{Cnv}ʻʻʻ\kappa \quad[\text{*41·3.*37·354}]\) -/
theorem pm41_32 {K : Set (Set (α → β → Prop))} :
    Cnv ʻʻ (graph prodRel ʻʻ K) = graph prodRel ʻʻ (Cnv ʻʻʻ K) := by
  ext T
  constructor
  · rintro ⟨S, ⟨L, hL, hS⟩, hT⟩
    obtain rfl : S = prodRel L := hS
    rw [Cnv_iff] at hT
    subst hT
    exact ⟨Cnv ʻʻ L, ⟨L, hL, rfl⟩, pm41_3⟩
  · rintro ⟨M, ⟨L, hL, hM⟩, hT⟩
    obtain rfl : M = Cnv ʻʻ L := hM
    obtain rfl : T = prodRel (Cnv ʻʻ L) := hT
    exact ⟨prodRel L, ⟨L, hL, rfl⟩, Cnv_iff.2 pm41_3.symm⟩

/-- ✱41·33. \(\vdash.\text{Cnv}ʻʻ\dot{s}ʻʻ\kappa =\dot{s}ʻʻ\text{Cnv}ʻʻʻ\kappa \quad[\text{*41·31.*37·354}]\) -/
theorem pm41_33 {K : Set (Set (α → β → Prop))} :
    Cnv ʻʻ (graph sumRel ʻʻ K) = graph sumRel ʻʻ (Cnv ʻʻʻ K) := by
  ext T
  constructor
  · rintro ⟨S, ⟨L, hL, hS⟩, hT⟩
    obtain rfl : S = sumRel L := hS
    rw [Cnv_iff] at hT
    subst hT
    exact ⟨Cnv ʻʻ L, ⟨L, hL, rfl⟩, pm41_31⟩
  · rintro ⟨M, ⟨L, hL, hM⟩, hT⟩
    obtain rfl : M = Cnv ʻʻ L := hM
    obtain rfl : T = sumRel (Cnv ʻʻ L) := hT
    exact ⟨sumRel L, ⟨L, hL, rfl⟩, Cnv_iff.2 pm41_31.symm⟩

/-- ✱41·34. \(\vdash.\dot{s}\alpha\upharpoonleft ʻʻ\lambda=\alpha\upharpoonleft \dot{s}ʻ\lambda\)

**Status.** proved (reading): transcription error of the e-text, which prints `ṡα↿''λ` (the `'`
after `ṡ` dropped) for `ṡ'α↿''λ`, as in the demonstration. The relation `α↿` (of `α ↿ P` to `P`,
✱38·01 with `↿` for `♀`) is `opL dres A`. -/
theorem pm41_34 {A : Set α} {L : Set (α → β → Prop)} :
    sumRel (opL dres A ʻʻ L) = A ◁ sumRel L := by
  rw [rel_eq_iff]
  intro x y
  constructor
  · rintro ⟨T, ⟨P, hP, hT⟩, h⟩
    obtain rfl : T = A ◁ P := hT
    exact ⟨h.1, P, hP, h.2⟩
  · rintro ⟨hx, P, hP, h⟩
    exact ⟨A ◁ P, ⟨P, hP, rfl⟩, hx, h⟩

/-- ✱41·341. \(\vdash. \dot{s}ʻ\upharpoonright \alphaʻʻ\lambda = (\dot{s}ʻ\lambda)\upharpoonright \alpha \quad[\text{Proof as in *41·34}]\) -/
theorem pm41_341 {A : Set β} {L : Set (α → β → Prop)} :
    sumRel (opR cres A ʻʻ L) = sumRel L ↾ A := by
  rw [rel_eq_iff]
  intro x y
  constructor
  · rintro ⟨T, ⟨P, hP, hT⟩, h⟩
    obtain rfl : T = P ↾ A := hT
    exact ⟨⟨P, hP, h.1⟩, h.2⟩
  · rintro ⟨⟨P, hP, h⟩, hy⟩
    exact ⟨P ↾ A, ⟨P, hP, rfl⟩, h, hy⟩

/-- ✱41·342. \(\vdash. \dot{s}ʻ\unicode{x0294f} \alphaʻʻ\lambda = (\dot{s}ʻ\lambda)\unicode{x0294f}\alpha\) -/
theorem pm41_342 {A : Set α} {L : Set (α → α → Prop)} :
    sumRel (opR fres A ʻʻ L) = sumRel L ⥏ A := by
  rw [rel_eq_iff]
  intro x y
  constructor
  · rintro ⟨T, ⟨P, hP, hT⟩, h⟩
    obtain rfl : T = P ⥏ A := hT
    exact ⟨⟨h.1.1, P, hP, h.1.2⟩, h.2⟩
  · rintro ⟨⟨hx, P, hP, h⟩, hy⟩
    exact ⟨P ⥏ A, ⟨P, hP, rfl⟩, ⟨hx, h⟩, hy⟩

/-- ✱41·35. \(\vdash. \dot{s}ʻM\upharpoonright ʻʻ\kappa = M\upharpoonright sʻ\kappa\) -/
theorem pm41_35 {M : α → β → Prop} {K : Set (Set β)} :
    sumRel (opL cres M ʻʻ K) = M ↾ sumCls K := by
  rw [rel_eq_iff]
  intro x y
  constructor
  · rintro ⟨T, ⟨A, hA, hT⟩, h⟩
    obtain rfl : T = M ↾ A := hT
    exact ⟨h.1, A, hA, h.2⟩
  · rintro ⟨h, A, hA, hy⟩
    exact ⟨M ↾ A, ⟨A, hA, rfl⟩, h, hy⟩

/-- ✱41·351. \(\vdash. \dot{s}ʻ\upharpoonleft Mʻʻ\kappa = (sʻ\kappa)\upharpoonleft M \quad[\text{Proof as in *41·35}]\) -/
theorem pm41_351 {M : α → β → Prop} {K : Set (Set α)} :
    sumRel (opR dres M ʻʻ K) = sumCls K ◁ M := by
  rw [rel_eq_iff]
  intro x y
  constructor
  · rintro ⟨T, ⟨A, hA, hT⟩, h⟩
    obtain rfl : T = A ◁ M := hT
    exact ⟨⟨A, hA, h.1⟩, h.2⟩
  · rintro ⟨⟨A, hA, hx⟩, h⟩
    exact ⟨A ◁ M, ⟨A, hA, rfl⟩, hx, h⟩

/-- ✱41·4. \(\vdash. \text{D}ʻ\dot{p}ʻ\lambda\subset pʻ\text{D}ʻʻ\lambda\) -/
theorem pm41_4 {L : Set (α → β → Prop)} : dom (prodRel L) ⊆ prodCls (D ʻʻ L) := by
  rintro x ⟨y, hxy⟩ G ⟨R, hR, hG⟩
  obtain rfl : G = dom R := hG
  exact ⟨y, hxy R hR⟩

/-- ✱41·41. \(\vdash.\text{ᗡ}ʻ\dot{p}ʻ\lambda\subset pʻ\text{ᗡ}ʻʻ\lambda \quad[\text{Proof as in *41·4}]\) -/
theorem pm41_41 {L : Set (α → β → Prop)} : codom (prodRel L) ⊆ prodCls (Dcnv ʻʻ L) := by
  rintro y ⟨x, hxy⟩ G ⟨R, hR, hG⟩
  obtain rfl : G = codom R := hG
  exact ⟨x, hxy R hR⟩

/-- ✱41·42. \(\vdash.Cʻ\dot{p}ʻ\lambda\subset pʻCʻʻ\lambda\) -/
theorem pm41_42 {L : Set (α → α → Prop)} : fld (prodRel L) ⊆ prodCls (C ʻʻ L) := by
  rintro x ⟨y, hxy | hyx⟩ G ⟨R, hR, hG⟩
  · obtain rfl : G = fld R := hG
    exact ⟨y, Or.inl (hxy R hR)⟩
  · obtain rfl : G = fld R := hG
    exact ⟨y, Or.inr (hyx R hR)⟩

/-- ✱41·43. \(\vdash.\text{D}ʻ\dot{s}ʻ\lambda = sʻ\text{D}ʻʻ\lambda\) -/
theorem pm41_43 {L : Set (α → β → Prop)} : dom (sumRel L) = sumCls (D ʻʻ L) := by
  ext x
  constructor
  · rintro ⟨y, R, hR, h⟩
    exact ⟨dom R, ⟨R, hR, rfl⟩, y, h⟩
  · rintro ⟨G, ⟨R, hR, hG⟩, hx⟩
    obtain rfl : G = dom R := hG
    obtain ⟨y, h⟩ := hx
    exact ⟨y, R, hR, h⟩

/-- ✱41·44. \(\vdash.\text{ᗡ}ʻ\dot{s}ʻ\lambda=sʻ\text{ᗡ}ʻʻ\lambda \quad[\text{Proof as in *41·43}]\) -/
theorem pm41_44 {L : Set (α → β → Prop)} : codom (sumRel L) = sumCls (Dcnv ʻʻ L) := by
  ext y
  constructor
  · rintro ⟨x, R, hR, h⟩
    exact ⟨codom R, ⟨R, hR, rfl⟩, x, h⟩
  · rintro ⟨G, ⟨R, hR, hG⟩, hy⟩
    obtain rfl : G = codom R := hG
    obtain ⟨x, h⟩ := hy
    exact ⟨x, R, hR, h⟩

/-- ✱41·45. \(\vdash.Cʻ\dot{s}ʻ\lambda=sʻCʻʻ\lambda\) -/
theorem pm41_45 {L : Set (α → α → Prop)} : fld (sumRel L) = sumCls (C ʻʻ L) := by
  ext x
  constructor
  · rintro ⟨y, ⟨R, hR, h⟩ | ⟨R, hR, h⟩⟩
    · exact ⟨fld R, ⟨R, hR, rfl⟩, y, Or.inl h⟩
    · exact ⟨fld R, ⟨R, hR, rfl⟩, y, Or.inr h⟩
  · rintro ⟨G, ⟨R, hR, hG⟩, hx⟩
    obtain rfl : G = fld R := hG
    obtain ⟨y, h | h⟩ := hx
    · exact ⟨y, Or.inl ⟨R, hR, h⟩⟩
    · exact ⟨y, Or.inr ⟨R, hR, h⟩⟩

/-- ✱41·5. \(\vdash.\dot{p}ʻ\lambda\mid \dot{p}ʻ\mu\unicode{x2abd}\dot{p}ʻ(sʻ\lambda\mid_{,,}ʻʻ\mu)\) -/
theorem pm41_5 {L : Set (α → β → Prop)} {M : Set (β → γ → Prop)} :
    prodRel L ⨾ prodRel M ⪽ prodRel (sumCls (opL (opImg relProd) L ʻʻ M)) := by
  rintro x z ⟨y, hxy, hyz⟩ T ⟨G, ⟨Q, hQ, hG⟩, hT⟩
  obtain rfl : G = opImg relProd L Q := hG
  obtain ⟨P, hP, hT⟩ := hT
  obtain rfl : T = P ⨾ Q := hT
  exact ⟨y, hxy P hP, hyz Q hQ⟩

/-- ✱41·51. \(\vdash.\dot{s}ʻ\lambda\mid \dot{s}ʻ\mu=\dot{s}ʻsʻ\lambda\mid_{,,}ʻʻ\mu\) -/
theorem pm41_51 {L : Set (α → β → Prop)} {M : Set (β → γ → Prop)} :
    sumRel L ⨾ sumRel M = sumRel (sumCls (opL (opImg relProd) L ʻʻ M)) := by
  rw [rel_eq_iff]
  intro x z
  constructor
  · rintro ⟨y, ⟨P, hP, hxy⟩, ⟨Q, hQ, hyz⟩⟩
    exact ⟨P ⨾ Q, ⟨opImg relProd L Q, ⟨Q, hQ, rfl⟩, P, hP, rfl⟩, y, hxy, hyz⟩
  · rintro ⟨T, ⟨G, ⟨Q, hQ, hG⟩, hT⟩, hxz⟩
    obtain rfl : G = opImg relProd L Q := hG
    obtain ⟨P, hP, hT⟩ := hT
    obtain rfl : T = P ⨾ Q := hT
    obtain ⟨y, hxy, hyz⟩ := hxz
    exact ⟨y, ⟨P, hP, hxy⟩, Q, hQ, hyz⟩

/-- ✱41·52. \(\vdash\colon\ldotp \alpha\upharpoonleft \dot{s}ʻ\lambda\unicode{x2abd}Q.\equiv:P\in \lambda.\supset_{P}.\alpha\upharpoonleft P\unicode{x2abd}Q\) -/
theorem pm41_52 {A : Set α} {L : Set (α → β → Prop)} {Q : α → β → Prop} :
    A ◁ sumRel L ⪽ Q ↔ ∀ P, P ∈ L → A ◁ P ⪽ Q := by
  constructor
  · rintro h P hP x y ⟨hx, hxy⟩
    exact h x y ⟨hx, P, hP, hxy⟩
  · rintro h x y ⟨hx, P, hP, hxy⟩
    exact h P hP x y ⟨hx, hxy⟩

/-- ✱41·6. \(\vdash\colon\ldotp y\in \beta.\supset_{y}.Pʻy=Qʻy\unicode{x228d}Rʻy:\supset.\dot{s}ʻPʻʻ\beta=\dot{s}ʻQʻʻ\beta\unicode{x228d}\dot{s}ʻRʻʻ\beta\) -/
theorem pm41_6 {P Q R : (α → β → Prop) → γ → Prop} {B : Set γ} :
    (∀ y, y ∈ B → Desc P y (fun S => Desc Q y (fun T => Desc R y (fun U => S = T ⊍ U)))) →
      sumRel (P ʻʻ B) = sumRel (Q ʻʻ B) ⊍ sumRel (R ʻʻ B) := by
  intro h
  rw [rel_eq_iff]
  intro u v
  constructor
  · rintro ⟨S, ⟨y, hy, hS⟩, huv⟩
    obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h y hy
    have hSa : S = a := (ha S).1 hS
    rw [hSa, habc] at huv
    rcases huv with huv | huv
    · exact Or.inl ⟨b, ⟨y, hy, (hb b).2 rfl⟩, huv⟩
    · exact Or.inr ⟨c, ⟨y, hy, (hc c).2 rfl⟩, huv⟩
  · rintro (⟨S, ⟨y, hy, hS⟩, huv⟩ | ⟨S, ⟨y, hy, hS⟩, huv⟩)
    · obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h y hy
      have hSb : S = b := (hb S).1 hS
      refine ⟨a, ⟨y, hy, (ha a).2 rfl⟩, ?_⟩
      rw [habc]
      exact Or.inl (hSb ▸ huv)
    · obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h y hy
      have hSc : S = c := (hc S).1 hS
      refine ⟨a, ⟨y, hy, (ha a).2 rfl⟩, ?_⟩
      rw [habc]
      exact Or.inr (hSc ▸ huv)

/-!
## [✱42] Miscellaneous propositions

*(Vol. 1, p. 336)*

> *Summary of* *42.
>
> The present number contains various propositions concerning products and sums of classes. They are concerned chiefly with classes of classes of classes, or with relations of relations of relations. These are required respectively in cardinal and in ordinal arithmetic. Thus *42·1 is used in *112 and *113, which are concerned with cardinal addition and multiplication, while *42·12·2 are used in *160 and *162, which are concerned with ordinal addition. *42·22, though not explicitly referred to, is useful in facilitating the comprehension of propositions on series of series of series, or rather on relations between relations between relations, which are required in connection with the associative law of multiplication in relation-arithmetic.

**Lean reading.** The relations `s`, `p`, `ṡ`, `ṗ` occurring in `s''κ`, `p''κ`, `ṡ''λ`, `ṗ''λ` are
the relations of `s'α`, … to `α`, i.e. `graph sumCls`, `graph prodCls`, `graph sumRel`,
`graph prodRel`; `κ` is a class of classes of classes (`Set (Set (Set α))`) and `λ` a class of
classes of relations. In ✱42·2–·22 `P` is a relation between relations (of relations), so that
`C`, `F`, `C'''` and `ṡ` are taken at the types the formulas require (typical ambiguity: Lean
infers the type parameters of `C` and `F` at each occurrence). `F⃗²` and `F⃗³` are `(F²)⃗` and
`(F³)⃗` (✱37·38, ✱37·3), where `F² = F | F` and `F³ = F² | F` are relative products of `F` at
different types; they are written `F ⨾ F` and `F ⨾ F ⨾ F` (Lean's `rsq`, `rcube` are
homogeneous), and `F⃗²'P` is `refs (F ⨾ F) P`. The chains of identities are conjunctions of
their links, nested to the left (✱13·03). ✱42·3·31 require the domain of `R` (resp. its
converse domain) to consist of classes.

**Status.** proved (all propositions; ✱42·2, ✱42·21, ✱42·22 proved (reading): `F²`, `F³` as
relative products of `F` at several types, see their docstrings).
-/

/-- ✱42·1. \(\vdash . sʻsʻʻ\kappa = sʻsʻ\kappa\) -/
theorem pm42_1 {K : Set (Set (Set α))} : sumCls (graph sumCls ʻʻ K) = sumCls (sumCls K) := by
  ext x
  constructor
  · rintro ⟨G, ⟨A, hA, hG⟩, hx⟩
    obtain rfl : G = sumCls A := hG
    obtain ⟨H, hH, hx⟩ := hx
    exact ⟨H, ⟨A, hA, hH⟩, hx⟩
  · rintro ⟨H, ⟨A, hA, hH⟩, hx⟩
    exact ⟨sumCls A, ⟨A, hA, rfl⟩, H, hH, hx⟩

/-- ✱42·11. \(\vdash.pʻpʻʻ\kappa=pʻsʻ\kappa\) -/
theorem pm42_11 {K : Set (Set (Set α))} :
    prodCls (graph prodCls ʻʻ K) = prodCls (sumCls K) := by
  ext x
  constructor
  · rintro hx H ⟨A, hA, hH⟩
    exact hx (prodCls A) ⟨A, hA, rfl⟩ H hH
  · rintro hx G ⟨A, hA, hG⟩
    obtain rfl : G = prodCls A := hG
    intro H hH
    exact hx H ⟨A, hA, hH⟩

/-- ✱42·12. \(\vdash.\dot{s}ʻ\dot{s}ʻʻ\lambda=\dot{s}ʻsʻ\lambda\) -/
theorem pm42_12 {L : Set (Set (α → β → Prop))} :
    sumRel (graph sumRel ʻʻ L) = sumRel (sumCls L) := by
  rw [rel_eq_iff]
  intro x y
  constructor
  · rintro ⟨T, ⟨M, hM, hT⟩, h⟩
    obtain rfl : T = sumRel M := hT
    obtain ⟨P, hP, h⟩ := h
    exact ⟨P, ⟨M, hM, hP⟩, h⟩
  · rintro ⟨P, ⟨M, hM, hP⟩, h⟩
    exact ⟨sumRel M, ⟨M, hM, rfl⟩, P, hP, h⟩

/-- ✱42·13. \(\vdash.\dot{p}ʻ\dot{p}ʻʻ\lambda=\dot{p}ʻsʻ\lambda\) -/
theorem pm42_13 {L : Set (Set (α → β → Prop))} :
    prodRel (graph prodRel ʻʻ L) = prodRel (sumCls L) := by
  rw [rel_eq_iff]
  intro x y
  constructor
  · rintro h P ⟨M, hM, hP⟩
    exact h (prodRel M) ⟨M, hM, rfl⟩ P hP
  · rintro h T ⟨M, hM, hT⟩
    obtain rfl : T = prodRel M := hT
    intro P hP
    exact h P ⟨M, hM, hP⟩

/-- ✱42·2. \(\vdash.Cʻ\dot{s}ʻCʻP=sʻCʻʻCʻP=FʻʻCʻP=\overrightarrow{F}^{2}ʻP\)

**Status.** proved (reading): `F⃗²` is `(F²)⃗` (✱37·38: `R⃗²'x = R''R⃗'x`), and `F² = F | F` is the
relative product of `F` with itself taken at two different types (typical ambiguity: the first
`F` relates individuals to relations of individuals, the second relations to relations of
relations). Lean's `rsq` is homogeneous, so `F²` is written `F ⨾ F` with the two typed instances
of `F`; `F⃗²'P` is then `refs (F ⨾ F) P` (✱32·13). The chain of identities is the conjunction of
its links (✱13·03). -/
theorem pm42_2 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    (fld (sumRel (fld P)) = sumCls (C ʻʻ fld P) ∧ sumCls (C ʻʻ fld P) = F ʻʻ fld P) ∧
      F ʻʻ fld P = refs (F ⨾ F) P := by
  refine ⟨⟨pm41_45, pm40_56⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨R, h1, h2⟩
    exact ⟨R, h2, h1⟩
  · rintro ⟨R, h1, h2⟩
    exact ⟨R, h2, h1⟩

/-- ✱42·21. \(\vdash.sʻCʻʻʻCʻʻCʻP=CʻʻsʻCʻʻCʻP=CʻʻCʻ\dot{s}ʻCʻP=CʻʻFʻʻCʻP=Cʻʻ\overrightarrow{F}^{2}ʻP\)

**Status.** proved (reading): `F⃗²'P` is `refs (F ⨾ F) P`, as in ✱42·2 (typical ambiguity of `F`);
the chain of identities is the conjunction of its links. -/
theorem pm42_21 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
      ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} :
    (((sumCls (C ʻʻʻ (C ʻʻ fld P)) = C ʻʻ sumCls (C ʻʻ fld P) ∧
      C ʻʻ sumCls (C ʻʻ fld P) = C ʻʻ fld (sumRel (fld P))) ∧
      C ʻʻ fld (sumRel (fld P)) = C ʻʻ (F ʻʻ fld P)) ∧
      C ʻʻ (F ʻʻ fld P) = C ʻʻ refs (F ⨾ F) P) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := pm42_2 (P := P)
  refine ⟨⟨⟨pm40_38.symm, ?_⟩, ?_⟩, ?_⟩
  · rw [h1]
  · rw [h1, h2]
  · rw [h3]

/-- ✱42·22. \[\begin{align}\vdash.sʻsʻCʻʻʻCʻʻCʻP&=sʻCʻʻsʻCʻʻCʻP=sʻCʻʻCʻ\dot{s}ʻCʻP\\ &=Cʻ\dot{s}ʻCʻ\dot{s}ʻCʻP=sʻCʻʻFʻʻCʻP\\ &=FʻʻFʻʻCʻP=Fʻʻ\overrightarrow{F}^{2}ʻP=\overrightarrow{F}^{3}ʻP\\ &\quad[\text{*42·21.*41·45.*40·56.*42·2.*37·3}]\end{align}\]

**Status.** proved (reading): `F⃗²'P` is `refs (F ⨾ F) P` and `F⃗³'P` is `refs (F ⨾ F ⨾ F) P`
(`F³ = F² | F`, ✱34·03, with `F` at three types; ✱37·3), as in ✱42·2; the chain of identities
is the conjunction of its seven links. -/
theorem pm42_22 {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
      ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} :
    (((((sumCls (sumCls (C ʻʻʻ (C ʻʻ fld P))) = sumCls (C ʻʻ sumCls (C ʻʻ fld P)) ∧
      sumCls (C ʻʻ sumCls (C ʻʻ fld P)) = sumCls (C ʻʻ fld (sumRel (fld P)))) ∧
      sumCls (C ʻʻ fld (sumRel (fld P))) = fld (sumRel (fld (sumRel (fld P))))) ∧
      fld (sumRel (fld (sumRel (fld P)))) = sumCls (C ʻʻ (F ʻʻ fld P))) ∧
      sumCls (C ʻʻ (F ʻʻ fld P)) = F ʻʻ (F ʻʻ fld P)) ∧
      F ʻʻ (F ʻʻ fld P) = F ʻʻ refs (F ⨾ F) P) ∧
      F ʻʻ refs (F ⨾ F) P = refs (F ⨾ F ⨾ F) P := by
  obtain ⟨⟨⟨l1, l2⟩, l3⟩, l4⟩ := pm42_21 (P := P)
  obtain ⟨⟨h1, h2⟩, h3⟩ := pm42_2 (P := P)
  refine ⟨⟨⟨⟨⟨⟨by rw [l1], by rw [l2]⟩, pm41_45.symm⟩, ?_⟩, pm40_56⟩, by rw [h3]⟩, ?_⟩
  · rw [pm41_45, h1, h2]
  · ext x
    constructor
    · rintro ⟨R, ⟨Q, hRQ, hQP⟩, hxR⟩
      exact ⟨Q, ⟨R, hxR, hRQ⟩, hQP⟩
    · rintro ⟨Q, ⟨R, hxR, hRQ⟩, hQP⟩
      exact ⟨R, ⟨Q, hRQ, hQP⟩, hxR⟩

/-- ✱42·3. \(\vdash.sʻsʻʻ\overrightarrow{R}ʻʻ\alpha=sʻRʻʻ\alpha\) -/
theorem pm42_3 {R : Set α → β → Prop} {A : Set β} :
    sumCls (graph sumCls ʻʻ (Rfwd R ʻʻ A)) = sumCls (R ʻʻ A) := by
  rw [pm42_1, pm40_5]

/-- ✱42·31. \(\vdash.sʻsʻʻ\overleftarrow{R}ʻʻ\alpha=sʻ\breve{R}ʻʻ\alpha \quad[\text{Proof as in *42·3}]\) -/
theorem pm42_31 {R : β → Set α → Prop} {A : Set β} :
    sumCls (graph sumCls ʻʻ (Rbwd R ʻʻ A)) = sumCls (R˘ ʻʻ A) := by
  rw [pm42_1, pm40_52]

/-!
## [✱43] The relations of a relative product to its factors

*(Vol. 1, p. 340)*

> *Summary of* *43.
>
> The purpose of the present number is to give certain propositions on the relation which holds between \(P\) and \(Q\) whenever \(P = Q \mid R\), or whenever \(P = R \mid Q\), or whenever \(P = R \mid Q \mid S\), where \(R\) and \(S\) are fixed. In virtue of the general definitions of *38, these relations are respectively \(\mid R\), \(R \mid\), and (\(R \mid) \mid (\mid S)\). Such relations are of great utility both in cardinal and in ordinal arithmetic; they are also much used in the theory of induction (Part II, Section E). In place of the notation (\(R \mid) \mid (\mid S)\), which is cumbrous, we adopt the more compact notation \(R \parallel S\). If \(\lambda\) is a class of relations, \(R \mid ʻʻ\lambda\) will be the class of relations \(R \mid P\) where \(P \in \lambda\), \(\mid Rʻʻ\lambda\) will be the class of relations \(P \mid R\) where \(P \in \lambda\), and (\(R \parallel S)ʻʻ\lambda\) will be the class of relations \(R \mid P \mid S\) where \(P \in \lambda\). These classes of relations are often required in subsequent work.
>
> In virtue of our definitions, we have
>
> *43·112. \(\vdash . (R \parallel S)ʻQ = R \mid Q \mid S\)
>
> …

**Lean reading.** `R |` and `| S` (✱38 with `♀ = |`) are `relProdL R` and `relProdR S`; the Df
✱43·01 is the Lean definition `R ∥ S = relProdL R ⨾ relProdR S` (`dpar`), with defining equation
by `rfl`. `R | Q | S` is `R ⨾ Q ⨾ S`, i.e. `(R ⨾ Q) ⨾ S` (✱34·22). The descriptive functions
`R |'Q`, `| R'Q`, `(R ‖ S)'Q` are kept as descriptions (`Desc`, `EDesc`) in the propositions
which state their existence or value (✱43·11–·122, ✱43·34, ✱43·4·401, ✱43·43, ✱43·48·481, ✱43·5);
`R |` and `| R` are graphs (`desc_graph`), while for `R ‖ S` existence and value are proved from
✱43·102. `D'R`, `ᗡ'R`, `C'R` are `dom R`, `codom R`, `fld R`, and `ᗡ'(R |)` etc. are taken at the
types of the relations involved (homogeneous where `C` occurs). Where the type of a relation
of relations is not determined by the formula (✱43·2–·202), it is given by an ascription.

**Status.** proved (all propositions; ✱43·01 definition; ✱43·21 proved (reading): e-text
transcription error; ✱43·491 proved (corrected), with `pm43_491_printed_false`; see their
docstrings).
-/

/-- ✱43·01 (Df). \(R \parallel S = (R \mid) \mid (\mid S) \quad \text{Df}\) -/
theorem pm43_01 {R : α → β → Prop} {S : γ → δ → Prop} : R ∥ S = relProdL R ⨾ relProdR S := rfl

/-- ✱43·1. \(\vdash:P(R\mid )Q.\equiv.P=R\mid Q\) -/
theorem pm43_1 {R : α → β → Prop} {P : α → γ → Prop} {Q : β → γ → Prop} :
    relProdL R P Q ↔ P = R ⨾ Q := Iff.rfl

/-- ✱43·101. \(\vdash:P(\mid R)Q.\equiv.P=Q\mid R\) -/
theorem pm43_101 {R : β → γ → Prop} {P : α → γ → Prop} {Q : α → β → Prop} :
    relProdR R P Q ↔ P = Q ⨾ R := Iff.rfl

/-- ✱43·102. \(\vdash:P(R\Arrowvert S)Q.\equiv.P=R\mid Q\mid S\) -/
theorem pm43_102 {R : α → β → Prop} {S : γ → δ → Prop} {P : α → δ → Prop} {Q : β → γ → Prop} :
    (R ∥ S) P Q ↔ P = R ⨾ Q ⨾ S := by
  rw [dpar_iff, relProd_assoc]

/-- ✱43·11. \(\vdash.R\mid ʻQ=R\mid Q\) -/
theorem pm43_11 {R : α → β → Prop} {Q : β → γ → Prop} :
    Desc (relProdL R) Q (fun T => T = R ⨾ Q) :=
  (desc_graph (relProd R) Q _).2 rfl

/-- ✱43·111. \(\vdash.\mid RʻQ=Q\mid R\) -/
theorem pm43_111 {R : β → γ → Prop} {Q : α → β → Prop} :
    Desc (relProdR R) Q (fun T => T = Q ⨾ R) :=
  (desc_graph (fun Q' => Q' ⨾ R) Q _).2 rfl

/-- ✱43·112. \(\vdash.(R\Arrowvert S)ʻQ=R\mid Q\mid S\) -/
theorem pm43_112 {R : α → β → Prop} {S : γ → δ → Prop} {Q : β → γ → Prop} :
    Desc (R ∥ S) Q (fun T => T = R ⨾ Q ⨾ S) :=
  ⟨R ⨾ Q ⨾ S, fun _ => pm43_102, rfl⟩

/-- ✱43·12. \(\vdash.\text{E}!R\mid ʻQ\) -/
theorem pm43_12 {R : α → β → Prop} {Q : β → γ → Prop} : EDesc (relProdL R) Q :=
  EDesc_graph (relProd R) Q

/-- ✱43·121. \(\vdash.\text{E}!\mid RʻQ\) -/
theorem pm43_121 {R : β → γ → Prop} {Q : α → β → Prop} : EDesc (relProdR R) Q :=
  EDesc_graph (fun Q' => Q' ⨾ R) Q

/-- ✱43·122. \(\vdash.\text{E}!(R\Arrowvert S)ʻQ\) -/
theorem pm43_122 {R : α → β → Prop} {S : γ → δ → Prop} {Q : β → γ → Prop} :
    EDesc (R ∥ S) Q :=
  ⟨R ⨾ Q ⨾ S, fun _ => pm43_102⟩

/-- ✱43·2. \(\vdash.(R\mid )\mid (S\mid )=(R\mid S)\mid \) -/
theorem pm43_2 {R : α → β → Prop} {S : β → γ → Prop} :
    (relProdL R ⨾ relProdL S : (α → δ → Prop) → (γ → δ → Prop) → Prop) = relProdL (R ⨾ S) := by
  rw [rel_eq_iff]
  intro L N
  simp only [relProd_apply_iff, relProdL_iff, exists_eq_right, relProd_assoc]

/-- ✱43·201. \(\vdash.(\mid R)\mid (\mid S)=\mid (S\mid R) \quad[\text{Proof as in *43·2}]\) -/
theorem pm43_201 {R : β → γ → Prop} {S : δ → β → Prop} :
    (relProdR R ⨾ relProdR S : (α → γ → Prop) → (α → δ → Prop) → Prop) = relProdR (S ⨾ R) := by
  rw [rel_eq_iff]
  intro L N
  simp only [relProd_apply_iff, relProdR_iff, exists_eq_right, relProd_assoc]

/-- ✱43·202. \(\vdash.(\mid R)\mid (S\mid )=(S\mid )\mid (\mid R)=S\Arrowvert R \quad[\text{Proof as in *43·2}]\) -/
theorem pm43_202 {R : β → γ → Prop} {S : α → δ → Prop} :
    (relProdR R ⨾ relProdL S : (α → γ → Prop) → (δ → β → Prop) → Prop) =
        relProdL S ⨾ relProdR R ∧
      relProdL S ⨾ relProdR R = S ∥ R := by
  refine ⟨?_, rfl⟩
  rw [rel_eq_iff]
  intro L N
  simp only [relProd_apply_iff, relProdL_iff, relProdR_iff, exists_eq_right, relProd_assoc]

/-- ✱43·21. \(\vdash.(P\mid Q)\mid (R\mid )=(P\mid R)\Arrowvert Q\)

**Status.** proved (reading): transcription error of the e-text, which prints `(P | Q) | (R |)` for
`(P ‖ Q) | (R |)`: as printed, `(P | Q)` would be a relative product of two relations of
relations, which is not significant with `(P | R) ‖ Q` on the right, and ✱43·21 is the first of the
group ✱43·21–·213 on `(P ‖ Q)` combined with `R |` or `| R` (its right side `(P | R) ‖ Q` is that of
`L = P | M | Q . M = R | N`). -/
theorem pm43_21 {P : α → β → Prop} {Q : γ → δ → Prop} {R : β → ε → Prop} :
    (P ∥ Q) ⨾ relProdL R = (P ⨾ R) ∥ Q := by
  rw [rel_eq_iff]
  intro L N
  simp only [relProd_apply_iff, relProdL_iff, dpar_iff, exists_eq_right, relProd_assoc]

/-- ✱43·211. \(\vdash.(R\mid )\mid (P\Arrowvert Q)=(R\mid P)\Arrowvert Q\) -/
theorem pm43_211 {R : α → β → Prop} {P : β → γ → Prop} {Q : δ → ε → Prop} :
    relProdL R ⨾ (P ∥ Q) = (R ⨾ P) ∥ Q := by
  rw [rel_eq_iff]
  intro L N
  simp only [relProd_apply_iff, relProdL_iff, dpar_iff, exists_eq_right, relProd_assoc]

/-- ✱43·212. \(\vdash.(P\Arrowvert Q)\mid (\mid R)=P\Arrowvert (R\mid Q)\) -/
theorem pm43_212 {P : α → β → Prop} {Q : γ → δ → Prop} {R : ε → γ → Prop} :
    (P ∥ Q) ⨾ relProdR R = P ∥ (R ⨾ Q) := by
  rw [rel_eq_iff]
  intro L N
  simp only [relProd_apply_iff, relProdR_iff, dpar_iff, exists_eq_right, relProd_assoc]

/-- ✱43·213. \(\vdash.(\mid R)\mid (P\Arrowvert Q)=P\Arrowvert (Q\mid R)\) -/
theorem pm43_213 {P : α → β → Prop} {Q : γ → δ → Prop} {R : δ → ε → Prop} :
    relProdR R ⨾ (P ∥ Q) = P ∥ (Q ⨾ R) := by
  rw [rel_eq_iff]
  intro L N
  simp only [relProd_apply_iff, relProdR_iff, dpar_iff, exists_eq_right, relProd_assoc]

/-- ✱43·22. \(\vdash.(P\Arrowvert Q)\mid (R\Arrowvert S)=(P\mid R)\Arrowvert (S\mid Q)\) -/
theorem pm43_22 {ζ : Type*} {P : α → β → Prop} {Q : γ → δ → Prop} {R : β → ε → Prop}
    {S : ζ → γ → Prop} : (P ∥ Q) ⨾ (R ∥ S) = (P ⨾ R) ∥ (S ⨾ Q) := by
  rw [rel_eq_iff]
  intro L N
  simp only [relProd_apply_iff, dpar_iff, exists_eq_right, relProd_assoc]

/-- ✱43·3. \(\vdash.(P).P\in \text{ᗡ}ʻR\mid \quad[\text{*43·12.*33·43}]\) -/
theorem pm43_3 {R : α → β → Prop} : ∀ P : β → γ → Prop, P ∈ codom (relProdL R) :=
  fun P => ⟨R ⨾ P, rfl⟩

/-- ✱43·301. \(\vdash.(P).P\in \text{ᗡ}ʻ\mid R\) -/
theorem pm43_301 {R : β → γ → Prop} : ∀ P : α → β → Prop, P ∈ codom (relProdR R) :=
  fun P => ⟨P ⨾ R, rfl⟩

/-- ✱43·302. \(\vdash.(P).P\in \text{ᗡ}ʻ(R\Arrowvert S)\) -/
theorem pm43_302 {R : α → β → Prop} {S : γ → δ → Prop} :
    ∀ P : β → γ → Prop, P ∈ codom (R ∥ S) :=
  fun P => ⟨R ⨾ P ⨾ S, pm43_102.2 rfl⟩

/-- ✱43·31. \(\vdash.P\upharpoonright \text{ᗡ}ʻR\mid =P\upharpoonright CʻR\mid =P\) -/
theorem pm43_31 {R : α → α → Prop} {P : δ → (α → γ → Prop) → Prop} :
    P ↾ codom (relProdL R) = P ↾ fld (relProdL R) ∧ P ↾ fld (relProdL R) = P := by
  have h1 : P ↾ codom (relProdL R) = P :=
    rel_eq_iff.2 fun _ Q => ⟨fun h => h.1, fun h => ⟨h, pm43_3 Q⟩⟩
  have h2 : P ↾ fld (relProdL R) = P :=
    rel_eq_iff.2 fun _ Q => ⟨fun h => h.1, fun h => ⟨h, R ⨾ Q, Or.inr rfl⟩⟩
  exact ⟨h1.trans h2.symm, h2⟩

/-- ✱43·311. \(\vdash.P\upharpoonright \text{ᗡ}ʻ\mid R=P\upharpoonright Cʻ\mid R=P\) -/
theorem pm43_311 {R : β → β → Prop} {P : δ → (α → β → Prop) → Prop} :
    P ↾ codom (relProdR R) = P ↾ fld (relProdR R) ∧ P ↾ fld (relProdR R) = P := by
  have h1 : P ↾ codom (relProdR R) = P :=
    rel_eq_iff.2 fun _ Q => ⟨fun h => h.1, fun h => ⟨h, pm43_301 Q⟩⟩
  have h2 : P ↾ fld (relProdR R) = P :=
    rel_eq_iff.2 fun _ Q => ⟨fun h => h.1, fun h => ⟨h, Q ⨾ R, Or.inr rfl⟩⟩
  exact ⟨h1.trans h2.symm, h2⟩

/-- ✱43·312. \(\vdash.P\upharpoonright \text{ᗡ}ʻ(R\Arrowvert S)=P\upharpoonright Cʻ(R\Arrowvert S)=P\) -/
theorem pm43_312 {R : α → α → Prop} {S : γ → γ → Prop} {P : δ → (α → γ → Prop) → Prop} :
    P ↾ codom (R ∥ S) = P ↾ fld (R ∥ S) ∧ P ↾ fld (R ∥ S) = P := by
  have h1 : P ↾ codom (R ∥ S) = P :=
    rel_eq_iff.2 fun _ Q => ⟨fun h => h.1, fun h => ⟨h, pm43_302 Q⟩⟩
  have h2 : P ↾ fld (R ∥ S) = P :=
    rel_eq_iff.2 fun _ Q => ⟨fun h => h.1, fun h => ⟨h, R ⨾ Q ⨾ S, Or.inr (pm43_102.2 rfl)⟩⟩
  exact ⟨h1.trans h2.symm, h2⟩

/-- ✱43·34. \(\vdash.R\mid ʻR=\mid RʻR=R^{2} \quad[\text{*43·11·111}]\) -/
theorem pm43_34 {R : α → α → Prop} :
    Desc (relProdL R) R (fun T => Desc (relProdR R) R (fun U => T = U)) ∧
      Desc (relProdR R) R (fun U => U = rsq R) :=
  ⟨(desc_graph (relProd R) R _).2 ((desc_graph (fun Q => Q ⨾ R) R _).2 rfl),
    (desc_graph (fun Q => Q ⨾ R) R _).2 rfl⟩

/-- ✱43·4. \(\vdash.Rʻʻ\text{D}ʻP=\text{D}ʻR\mid ʻP \quad[\text{*37·32.*43·1}]\) -/
theorem pm43_4 {R : α → β → Prop} {P : β → γ → Prop} :
    Desc (relProdL R) P (fun T => R ʻʻ dom P = dom T) :=
  (desc_graph (relProd R) P _).2 (img_dom R P)

/-- ✱43·401. \(\vdash.\breve{R}ʻʻ\text{ᗡ}ʻP=\text{ᗡ}ʻ\mid RʻP \quad[\text{*37·32.*43·101}]\) -/
theorem pm43_401 {R : β → γ → Prop} {P : α → β → Prop} :
    Desc (relProdR R) P (fun T => R˘ ʻʻ codom P = codom T) :=
  (desc_graph (fun Q => Q ⨾ R) P _).2 (img_codom P R)

/-- ✱43·41. \(\vdash.Rʻʻʻ\text{D}ʻʻ\lambda=\text{D}ʻʻR\mid ʻʻ\lambda \quad[\text{*43·4.*37·355}]\) -/
theorem pm43_41 {R : α → β → Prop} {L : Set (β → γ → Prop)} :
    R ʻʻʻ (D ʻʻ L) = D ʻʻ (relProdL R ʻʻ L) := by
  ext G
  constructor
  · rintro ⟨H, ⟨P, hP, hH⟩, hG⟩
    obtain rfl : H = dom P := hH
    obtain rfl : G = R ʻʻ dom P := hG
    exact ⟨R ⨾ P, ⟨P, hP, rfl⟩, img_dom R P⟩
  · rintro ⟨T, ⟨P, hP, hT⟩, hG⟩
    obtain rfl : T = R ⨾ P := hT
    obtain rfl : G = dom (R ⨾ P) := hG
    exact ⟨dom P, ⟨P, hP, rfl⟩, (img_dom R P).symm⟩

/-- ✱43·411. \(\vdash.\breve{R}ʻʻʻ\text{ᗡ}ʻʻ\lambda=\text{ᗡ}ʻʻ\mid Rʻʻ\lambda \quad[\text{*43·401.*37·355}]\) -/
theorem pm43_411 {R : β → γ → Prop} {L : Set (α → β → Prop)} :
    R˘ ʻʻʻ (Dcnv ʻʻ L) = Dcnv ʻʻ (relProdR R ʻʻ L) := by
  ext G
  constructor
  · rintro ⟨H, ⟨P, hP, hH⟩, hG⟩
    obtain rfl : H = codom P := hH
    obtain rfl : G = R˘ ʻʻ codom P := hG
    exact ⟨P ⨾ R, ⟨P, hP, rfl⟩, img_codom P R⟩
  · rintro ⟨T, ⟨P, hP, hT⟩, hG⟩
    obtain rfl : T = P ⨾ R := hT
    obtain rfl : G = codom (P ⨾ R) := hG
    exact ⟨codom P, ⟨P, hP, rfl⟩, (img_codom P R).symm⟩

/-- ✱43·42. \(\vdash.\dot{s}ʻR\mid ʻʻ\lambda=R\mid \dot{s}ʻ\lambda\) -/
theorem pm43_42 {R : α → β → Prop} {L : Set (β → γ → Prop)} :
    sumRel (relProdL R ʻʻ L) = R ⨾ sumRel L := by
  rw [rel_eq_iff]
  intro x z
  constructor
  · rintro ⟨T, ⟨P, hP, hT⟩, hxz⟩
    obtain rfl : T = R ⨾ P := hT
    obtain ⟨y, hxy, hyz⟩ := hxz
    exact ⟨y, hxy, P, hP, hyz⟩
  · rintro ⟨y, hxy, P, hP, hyz⟩
    exact ⟨R ⨾ P, ⟨P, hP, rfl⟩, y, hxy, hyz⟩

/-- ✱43·421. \(\vdash.\dot{s}ʻ\mid Rʻʻ\lambda=(\dot{s}ʻ\lambda)\mid R \quad[\text{Proof as in *43·42}]\) -/
theorem pm43_421 {R : β → γ → Prop} {L : Set (α → β → Prop)} :
    sumRel (relProdR R ʻʻ L) = sumRel L ⨾ R := by
  rw [rel_eq_iff]
  intro x z
  constructor
  · rintro ⟨T, ⟨P, hP, hT⟩, hxz⟩
    obtain rfl : T = P ⨾ R := hT
    obtain ⟨y, hxy, hyz⟩ := hxz
    exact ⟨y, ⟨P, hP, hxy⟩, hyz⟩
  · rintro ⟨y, ⟨P, hP, hxy⟩, hyz⟩
    exact ⟨P ⨾ R, ⟨P, hP, rfl⟩, y, hxy, hyz⟩

/-- ✱43·43. \(\vdash.\dot{s}ʻ(R\Arrowvert S)ʻʻ\lambda=(R\Arrowvert S)ʻ\dot{s}ʻ\lambda\) -/
theorem pm43_43 {R : α → β → Prop} {S : γ → δ → Prop} {L : Set (β → γ → Prop)} :
    Desc (R ∥ S) (sumRel L) (fun T => sumRel ((R ∥ S) ʻʻ L) = T) := by
  refine ⟨R ⨾ sumRel L ⨾ S, fun _ => pm43_102, ?_⟩
  show sumRel ((R ∥ S) ʻʻ L) = R ⨾ sumRel L ⨾ S
  rw [rel_eq_iff]
  intro x w
  constructor
  · rintro ⟨T, ⟨P, hP, hT⟩, hxw⟩
    rw [pm43_102] at hT
    subst hT
    obtain ⟨z, ⟨y, hxy, hyz⟩, hzw⟩ := hxw
    exact ⟨z, ⟨y, hxy, P, hP, hyz⟩, hzw⟩
  · rintro ⟨z, ⟨y, hxy, P, hP, hyz⟩, hzw⟩
    exact ⟨R ⨾ P ⨾ S, ⟨P, hP, pm43_102.2 rfl⟩, z, ⟨y, hxy, hyz⟩, hzw⟩

/-- ✱43·48. \(\vdash:\text{D}ʻP\subset \alpha.\supset.Q\mid ʻP=(Q\upharpoonright \alpha)\mid ʻP \quad[\text{*35·481}]\) -/
theorem pm43_48 {Q : α → β → Prop} {P : β → γ → Prop} {A : Set β} :
    dom P ⊆ A → Desc (relProdL Q) P (fun T => Desc (relProdL (Q ↾ A)) P (fun U => T = U)) :=
  fun h => (desc_graph (relProd Q) P _).2 ((desc_graph (relProd (Q ↾ A)) P _).2
    (relProd_cres_eq h))

/-- ✱43·481. \(\vdash:\text{ᗡ}ʻP\subset \beta.\supset.\mid RʻP=\mid (\beta\upharpoonleft R)ʻP \quad[\text{*35·48}]\) -/
theorem pm43_481 {R : β → γ → Prop} {P : α → β → Prop} {B : Set β} :
    codom P ⊆ B → Desc (relProdR R) P (fun T => Desc (relProdR (B ◁ R)) P (fun U => T = U)) :=
  fun h => (desc_graph (fun Q => Q ⨾ R) P _).2 ((desc_graph (fun Q => Q ⨾ (B ◁ R)) P _).2
    (relProd_dres_eq h))

/-- ✱43·49. \(\vdash:sʻ\text{D}ʻʻ\lambda\subset \alpha.\supset.(Q\mid )\upharpoonright \lambda=\{(Q\upharpoonright \alpha)\mid\}\upharpoonright \lambda\) -/
theorem pm43_49 {Q : α → β → Prop} {L : Set (β → γ → Prop)} {A : Set β} :
    sumCls (D ʻʻ L) ⊆ A → relProdL Q ↾ L = relProdL (Q ↾ A) ↾ L := by
  intro h
  rw [rel_eq_iff]
  intro T P
  have e : P ∈ L → Q ⨾ P = (Q ↾ A) ⨾ P := fun hP =>
    relProd_cres_eq fun y hy => h ⟨dom P, ⟨P, hP, rfl⟩, hy⟩
  constructor
  · rintro ⟨hT, hP⟩
    exact ⟨Eq.trans hT (e hP), hP⟩
  · rintro ⟨hT, hP⟩
    exact ⟨Eq.trans hT (e hP).symm, hP⟩

/-- ✱43·491. \(\vdash:sʻ\text{ᗡ}ʻʻ\lambda\subset \beta.\supset.(\mid R)\upharpoonright \lambda=\{\mid (\alpha\upharpoonleft R)\}\upharpoonright \lambda \quad[\text{Proof as in *43·49}]\)

**Status.** proved (corrected): as printed, the conclusion is `(| R) ↾ λ = {| (α ↿ R)} ↾ λ` with a
class `α` that does not occur in the hypothesis `s'ᗡ''λ ⊂ β`; so stated (for arbitrary `α`) the
proposition is false (for `λ = ι'V̇`, `β = V`, `α = Λ`, `R = V̇`, the left side relates `V̇ | V̇` to
`V̇` and the right side does not; `pm43_491_printed_false`). The errata do not list it. PM
intends `{| (β ↿ R)} ↾ λ`: the proposition is "proved as in ✱43·49", i.e. from ✱40·43 and ✱43·481,
whose hypothesis `ᗡ'P ⊂ β` gives `| R'P = | (β ↿ R)'P`. The corrected form is proved. -/
theorem pm43_491 {R : β → γ → Prop} {L : Set (α → β → Prop)} {B : Set β} :
    sumCls (Dcnv ʻʻ L) ⊆ B → relProdR R ↾ L = relProdR (B ◁ R) ↾ L := by
  intro h
  rw [rel_eq_iff]
  intro T P
  have e : P ∈ L → P ⨾ R = P ⨾ (B ◁ R) := fun hP =>
    relProd_dres_eq fun y hy => h ⟨codom P, ⟨P, hP, rfl⟩, hy⟩
  constructor
  · rintro ⟨hT, hP⟩
    exact ⟨Eq.trans hT (e hP), hP⟩
  · rintro ⟨hT, hP⟩
    exact ⟨Eq.trans hT (e hP).symm, hP⟩

/-- The printed form of ✱43·491 (with `α` for `β` in the conclusion) is false. -/
theorem pm43_491_printed_false :
    ¬ ∀ (L : Set (Unit → Unit → Prop)) (B A : Set Unit) (R : Unit → Unit → Prop),
      sumCls (Dcnv ʻʻ L) ⊆ B → relProdR R ↾ L = relProdR (A ◁ R) ↾ L := by
  intro h
  have e := h {rV} Set.univ ∅ rV (fun _ _ => Set.mem_univ _)
  have h1 : (relProdR (rV : Unit → Unit → Prop) ↾ ({rV} : Set (Unit → Unit → Prop)))
      ((rV : Unit → Unit → Prop) ⨾ (rV : Unit → Unit → Prop)) rV := ⟨rfl, rfl⟩
  rw [e] at h1
  have h2 : (rV : Unit → Unit → Prop) ⨾ (rV : Unit → Unit → Prop) =
      (rV : Unit → Unit → Prop) ⨾ ((∅ : Set Unit) ◁ (rV : Unit → Unit → Prop)) := h1.1
  have h3 : ((rV : Unit → Unit → Prop) ⨾ (rV : Unit → Unit → Prop)) () () :=
    ⟨(), ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  rw [h2] at h3
  obtain ⟨_, -, hx, -⟩ := h3
  simp at hx

/-- ✱43·5. \[\begin{align}&\vdash:\text{D}ʻP\subset \alpha.\text{ᗡ}ʻP\subset \beta.\supset.(Q\Arrowvert R)ʻP=\{(Q\upharpoonright \alpha)\Arrowvert (\beta\upharpoonleft R)\}ʻP\\ &\quad[\text{*35·48·481 .*43·112}]\end{align}\] -/
theorem pm43_5 {Q : α → β → Prop} {P : β → γ → Prop} {R : γ → δ → Prop} {A : Set β} {B : Set γ} :
    dom P ⊆ A ∧ codom P ⊆ B →
      Desc (Q ∥ R) P (fun T => Desc ((Q ↾ A) ∥ (B ◁ R)) P (fun U => T = U)) := by
  rintro ⟨hA, hB⟩
  refine ⟨Q ⨾ P ⨾ R, fun _ => pm43_102, (Q ↾ A) ⨾ P ⨾ (B ◁ R), fun _ => pm43_102, ?_⟩
  show Q ⨾ P ⨾ R = (Q ↾ A) ⨾ P ⨾ (B ◁ R)
  rw [← relProd_cres_eq hA, relProd_assoc, relProd_assoc, ← relProd_dres_eq hB]

/-- ✱43·51. \(\vdash:sʻDʻʻ\lambda\subset \alpha.sʻ\text{ᗡ}ʻʻ\lambda\subset \beta.\supset.(Q\Arrowvert R)\upharpoonright \lambda=\{(Q\upharpoonright \alpha)\Arrowvert (\beta\upharpoonleft R)\}\upharpoonright \lambda\) -/
theorem pm43_51 {Q : α → β → Prop} {L : Set (β → γ → Prop)} {R : γ → δ → Prop} {A : Set β}
    {B : Set γ} :
    sumCls (D ʻʻ L) ⊆ A ∧ sumCls (Dcnv ʻʻ L) ⊆ B →
      (Q ∥ R) ↾ L = ((Q ↾ A) ∥ (B ◁ R)) ↾ L := by
  rintro ⟨hA, hB⟩
  rw [rel_eq_iff]
  intro T P
  have e : P ∈ L → Q ⨾ P ⨾ R = (Q ↾ A) ⨾ P ⨾ (B ◁ R) := by
    intro hP
    rw [← relProd_cres_eq (fun y hy => hA ⟨dom P, ⟨P, hP, rfl⟩, hy⟩), relProd_assoc,
      relProd_assoc, ← relProd_dres_eq (fun z hz => hB ⟨codom P, ⟨P, hP, rfl⟩, hz⟩)]
  show (Q ∥ R) T P ∧ P ∈ L ↔ ((Q ↾ A) ∥ (B ◁ R)) T P ∧ P ∈ L
  rw [pm43_102, pm43_102]
  constructor
  · rintro ⟨hT, hP⟩
    exact ⟨hT.trans (e hP), hP⟩
  · rintro ⟨hT, hP⟩
    exact ⟨hT.trans (e hP).symm, hP⟩

end PrincipiaMathematica
