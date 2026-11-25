import PrincipiaMathematica.Defs.Part1

/-!
# Part I, Section D: Logic of relations

Volume 1. Numbers: ✱30, ✱31, ✱32, ✱33, ✱34, ✱35.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w u'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

/-! ### Helper lemmas for Section D (not PM propositions) -/

/-- If `R'y` is `b`, then `ψ(R'y)` is `ψ b`. -/
private theorem desc_of_eq {R : α → β → Prop} {y : β} {b : α} (hb : ∀ x, R x y ↔ x = b)
    (ψ : α → Prop) : Desc R y ψ ↔ ψ b :=
  TheIs_iff_of_unique hb

private theorem eq_Null_iff {A : Set α} : A = Λ ↔ ¬ A.Nonempty := by
  rw [Null_eq_empty, Set.not_nonempty_iff_eq_empty]

private theorem eq_rNull_iff {R : α → β → Prop} : R = rNull ↔ ¬ rEx R := by
  constructor
  · rintro rfl ⟨x, y, h⟩
    exact rNull_apply x y h
  · intro h
    funext x y
    exact propext ⟨fun hr => (h ⟨x, y, hr⟩).elim, fun hn => (rNull_apply x y hn).elim⟩

private theorem mem_dom_of {R : α → β → Prop} {x : α} {y : β} (h : R x y) : x ∈ dom R :=
  ⟨y, h⟩

private theorem mem_codom_of {R : α → β → Prop} {x : α} {y : β} (h : R x y) : y ∈ codom R :=
  ⟨x, h⟩

private theorem not_mem_Null (x : α) : x ∉ (Λ : Set α) := fun h => h rfl

private theorem rNull_rcup (S : α → β → Prop) : rNull ⊍ S = S := by
  funext x y
  apply propext
  constructor
  · rintro (h | h)
    · exact (rNull_apply x y h).elim
    · exact h
  · intro h
    exact Or.inr h

/-- Extensionality of relations, then unfolding the relation calculus and propositional logic. -/
local macro "rel_tac" : tactic =>
  `(tactic| (funext x y; apply propext; simp only [dres, cres, bres, rcap, rcup, rneg, rdiff,
      cross, cnv, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff] <;> tauto))

/-!
## [✱30] Descriptive functions

*(Vol. 1, p. 245)*

> *Summary of* *30.
>
> The functions hitherto considered, with the exception of a few particular functions such as \(\alpha \cap \beta\), have been propositional, *i.e.* have had propositions for their values. But the ordinary functions of mathematics, such as \(x^{2}\), \(\sin x\), \(\log x\), are not propositional. Functions of this kind always mean "the term having such and such a relation to \(x\)." For this reason they may be called *descriptive* functions, because they *describe* a certain term by means of its relation to their argument. Thus "\(\sin \dfrac{\pi}{2}\)" describes the number \(1\); yet propositions in which \(\sin \dfrac{\pi}{2}\) occurs are not the same as they would be if \(1\) were substituted for \(\sin\dfrac{\pi}{2}\). This appears *e.g.* from the proposition "\(\sin\dfrac{\pi}{2} = 1\)," which conveys valuable information, whereas "\(1 = 1\)" is trivial. Descriptive functions, like descriptions in general, have no meaning by themselves, but only as constituents of propositions [Note: Cf. *14, above.].
>
> The general definition of a descriptive function is:
>
> *30·01. \(Rʻy=({℩}x)(xRy) \quad \text{Df}\)
>
> …

**Lean reading.** A descriptive function `R'y` is the description `(℩x)(xRy)`, an incomplete
symbol, never a Lean term: a formula `ψ(R'y)` is `Desc R y ψ` (✱30·01), its scope being the
smallest bracketed proposition containing `R'y` unless PM marks it with `[R'y]` (Basic §5); of two
descriptive functions the first has the larger scope, so `R'y = S'z` is
`Desc R y (fun b => Desc S z (fun c => b = c))`. `E!R'y` is `EDesc R y`; `ψ(P'Q'z)` is
`Desc2 P Q z ψ` (✱30·02) and `E!P'Q'z` is `EBang (fun x => Desc Q z (fun w => P x w))`, the
existence of the description that defines `P'Q'z`. Relations are heterogeneous
(`R : α → β → Prop`). The e-text prints `∃!R'y` for `E!R'y` in the hypotheses of ✱30·12–✱30·142
and ✱30·18 (the cited ✱14·31–✱14·332, ✱14·18 have `E!`); these are read with `EDesc`. The proofs
unfold `Desc`/`TheIs` directly instead of citing ✱14.

**Status.** proved (all propositions; ✱30·01, ✱30·02 definition; ✱30·12, ✱30·13, ✱30·14,
✱30·141, ✱30·142, ✱30·18 proved (reading): `∃!` printed for `E!`, see their docstrings).
-/

/-- ✱30·01 (Df). \(Rʻy=({℩}x)(xRy) \quad\text{Df}\) -/
theorem pm30_01 {R : α → β → Prop} {y : β} {ψ : α → Prop} :
    Desc R y ψ ↔ TheIs (fun x => R x y) ψ := Iff.rfl

/-- ✱30·02 (Df). \(RʻSʻy=Rʻ(Sʻy) \quad\text{Df}\) -/
theorem pm30_02 {R : α → β → Prop} {S : β → γ → Prop} {y : γ} {ψ : α → Prop} :
    Desc2 R S y ψ ↔ TheIs (fun x => Desc S y (fun z => R x z)) ψ := Iff.rfl

/-- ✱30·1. \(\vdash:[Rʻy].f(Rʻy).\equiv.[({℩}x)(xRy)].f({℩}x)(xRy) \quad[\text{*4·2.(*30·01)}]\) -/
theorem pm30_1 {R : α → β → Prop} {y : β} {f : α → Prop} :
    Desc R y f ↔ TheIs (fun x => R x y) f := Iff.rfl

/-- ✱30·11. \(\vdash\colon\ldotp[Rʻy].f(Rʻy).\equiv:(\exists b):xRy.\equiv_{x}.x=b:fb \quad[\text{*30·1.*14·1}]\) -/
theorem pm30_11 {R : α → β → Prop} {y : β} {f : α → Prop} :
    Desc R y f ↔ ∃ b, (∀ x, R x y ↔ x = b) ∧ f b := Iff.rfl

/-- ✱30·12. \(\vdash\colon\colon\exists!Rʻy.\supset\colon\ldotp[Rʻy].p\lor\chi(Rʻy).\equiv:p.\lor.[Rʻy].\chi(Rʻy) \quad[\text{*14·31}]\)

**Status.** proved (reading): transcription error: the e-text prints `∃!R'y` (which is not significant
for a descriptive function in general) for `E!R'y`; the cited ✱14·31 has `E!(℩x)(φx)`. -/
theorem pm30_12 {R : α → β → Prop} {y : β} {p : Prop} {χ : α → Prop} :
    EDesc R y → (Desc R y (fun b => p ∨ χ b) ↔ p ∨ Desc R y χ) := by
  rintro ⟨b, hb⟩
  simp only [desc_of_eq hb]

/-- ✱30·13. \(\vdash\colon\colon\exists!Rʻy.\supset\colon\ldotp[Rʻy].{\sim}\chi(Rʻy).\equiv.{\sim}\{[Rʻy].\chi(Rʻy)\} \quad[\text{*14·32}]\)

**Status.** proved (reading): transcription error `∃!R'y` for `E!R'y`, as in ✱30·12 (cited ✱14·32). -/
theorem pm30_13 {R : α → β → Prop} {y : β} {χ : α → Prop} :
    EDesc R y → (Desc R y (fun b => ¬χ b) ↔ ¬Desc R y χ) := by
  rintro ⟨b, hb⟩
  simp only [desc_of_eq hb]

/-- ✱30·14. \(\vdash\colon\colon\exists!Rʻy.\supset\colon\ldotp[Rʻy].p\supset\chi(Rʻy).\equiv:p.\supset.[Rʻy].\chi(Rʻy) \quad[\text{*14·33}]\)

**Status.** proved (reading): transcription error `∃!R'y` for `E!R'y`, as in ✱30·12 (cited ✱14·33). -/
theorem pm30_14 {R : α → β → Prop} {y : β} {p : Prop} {χ : α → Prop} :
    EDesc R y → (Desc R y (fun b => p → χ b) ↔ (p → Desc R y χ)) := by
  rintro ⟨b, hb⟩
  simp only [desc_of_eq hb]

/-- ✱30·141. \(\vdash\colon\colon\exists!Rʻy.\supset\colon\ldotp[Rʻy].\chi(Rʻy)\supset p.\equiv:[Rʻy].\chi(Rʻy).\supset.p \quad[\text{*14·331}]\)

**Status.** proved (reading): transcription error `∃!R'y` for `E!R'y`, as in ✱30·12 (cited ✱14·331). -/
theorem pm30_141 {R : α → β → Prop} {y : β} {p : Prop} {χ : α → Prop} :
    EDesc R y → (Desc R y (fun b => χ b → p) ↔ (Desc R y χ → p)) := by
  rintro ⟨b, hb⟩
  simp only [desc_of_eq hb]

/-- ✱30·142. \(\vdash\colon\colon\exists!Rʻy.\supset\colon\ldotp[Rʻy].p\equiv \chi(Rʻy).\equiv:p.\equiv.[Rʻy].\chi(Rʻy) \quad[\text{*14·332}]\)

**Status.** proved (reading): transcription error `∃!R'y` for `E!R'y`, as in ✱30·12 (cited ✱14·332). -/
theorem pm30_142 {R : α → β → Prop} {y : β} {p : Prop} {χ : α → Prop} :
    EDesc R y → (Desc R y (fun b => p ↔ χ b) ↔ (p ↔ Desc R y χ)) := by
  rintro ⟨b, hb⟩
  simp only [desc_of_eq hb]

/-- ✱30·15. \(\vdash\colon\ldotp p:[Rʻy].\chi(Rʻy):\equiv:[Rʻy].p.\chi(Rʻy) \quad[\text{*14·34}]\) -/
theorem pm30_15 {R : α → β → Prop} {y : β} {p : Prop} {χ : α → Prop} :
    p ∧ Desc R y χ ↔ Desc R y (fun b => p ∧ χ b) := by
  constructor
  · rintro ⟨hp, b, hb, hχ⟩
    exact ⟨b, hb, hp, hχ⟩
  · rintro ⟨b, hb, hp, hχ⟩
    exact ⟨hp, b, hb, hχ⟩

/-- ✱30·16. \(\vdash\colon [Rʻy].f(Rʻy,Sʻz).\equiv.[Sʻz].f(Rʻy,Sʻz) \quad[\text{*14·113}]\) -/
theorem pm30_16 {R : α → β → Prop} {y : β} {S : γ → δ → Prop} {z : δ} {f : α → γ → Prop} :
    Desc R y (fun b => Desc S z (fun c => f b c)) ↔ Desc S z (fun c => Desc R y (fun b => f b c)) := by
  constructor
  · rintro ⟨b, hb, c, hc, h⟩
    exact ⟨c, hc, b, hb, h⟩
  · rintro ⟨c, hc, b, hb, h⟩
    exact ⟨b, hb, c, hc, h⟩

/-- ✱30·17. \[\begin{align}\vdash\colon\ldotp[Rʻy].&f(Rʻy,Sʻz).\equiv:\\ &(\exists b,c):xRy.\equiv_{x}.x=b:xSz.\equiv_{x}.x=c:f(b,c) \quad[\text{*14·112}]\end{align}\] -/
theorem pm30_17 {R : α → β → Prop} {y : β} {S : γ → δ → Prop} {z : δ} {f : α → γ → Prop} :
    Desc R y (fun b => Desc S z (fun c => f b c)) ↔
      ∃ b c, ((∀ x, R x y ↔ x = b) ∧ (∀ x, S x z ↔ x = c)) ∧ f b c := by
  constructor
  · rintro ⟨b, hb, c, hc, h⟩
    exact ⟨b, c, ⟨hb, hc⟩, h⟩
  · rintro ⟨b, c, ⟨hb, hc⟩, h⟩
    exact ⟨b, hb, c, hc, h⟩

/-- ✱30·18. \(\vdash\colon\ldotp\exists!Rʻy:(z).\phi z:\supset.\phi(Rʻy) \quad[\text{*14·18}]\)

**Status.** proved (reading): transcription error: the e-text prints `∃!R'y` for `E!R'y`; the cited
✱14·18 has `E!(℩x)(φx)` (Basic §9). -/
theorem pm30_18 {R : α → β → Prop} {y : β} {φ : α → Prop} :
    EDesc R y ∧ (∀ z, φ z) → Desc R y φ := by
  rintro ⟨⟨b, hb⟩, h⟩
  exact ⟨b, hb, h b⟩

/-- ✱30·19. \(\vdash\colon\ldotp Rʻy=b.\supset:\psi(Rʻy).\equiv.\psi b \quad[\text{*14·15}]\) -/
theorem pm30_19 {R : α → β → Prop} {y : β} {b : α} {ψ : α → Prop} :
    Desc R y (fun c => c = b) → (Desc R y ψ ↔ ψ b) := by
  rintro ⟨c, hc, rfl⟩
  exact desc_of_eq hc ψ

/-- ✱30·2. \(\vdash\colon\ldotp\text{E}!Rʻy.\equiv:(\exists b):xRy.\equiv_{x}.x=b \quad[\text{*4·2.*14·11.(*30·01)}]\) -/
theorem pm30_2 {R : α → β → Prop} {y : β} : EDesc R y ↔ ∃ b, ∀ x, R x y ↔ x = b := Iff.rfl

/-- ✱30·21. \[\begin{align}&\vdash\colon\colon\text{E}!Rʻy.\equiv\colon\ldotp(\exists x).xRy:xRy.zRy.\supset_{x,z}.x=z\\ &\quad[\text{*14·203.(*30·01)}]\end{align}\] -/
theorem pm30_21 {R : α → β → Prop} {y : β} :
    EDesc R y ↔ (∃ x, R x y) ∧ ∀ x z, R x y ∧ R z y → x = z := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨⟨b, (hb b).2 rfl⟩, ?_⟩
    rintro x z ⟨hx, hz⟩
    exact ((hb x).1 hx).trans ((hb z).1 hz).symm
  · rintro ⟨⟨b, hb⟩, h⟩
    refine ⟨b, fun x => ⟨fun hx => h x b ⟨hx, hb⟩, ?_⟩⟩
    rintro rfl
    exact hb

/-- ✱30·22. \(\vdash:\text{E}!Rʻy.\equiv.Rʻy=({℩}x)(xRy) \quad[\text{*14·28.(*30·01)}]\) -/
theorem pm30_22 {R : α → β → Prop} {y : β} :
    EDesc R y ↔ Desc R y (fun b => TheIs (fun x => R x y) (fun c => b = c)) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb, b, hb, rfl⟩
  · rintro ⟨b, hb, -⟩
    exact ⟨b, hb⟩

/-- ✱30·3. \(\vdash\colon\ldotp x=Rʻy.\equiv:zRy.\equiv_{z}.z=x \quad[\text{*14·202}]\) -/
theorem pm30_3 {R : α → β → Prop} {y : β} {x : α} :
    Desc R y (fun b => x = b) ↔ ∀ z, R z y ↔ z = x := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro h
    exact ⟨x, h, rfl⟩

/-- ✱30·31. \(\vdash\colon\ldotp x=Rʻy.\equiv:xRy:zRy.\supset_{z}.z=x \quad[\text{*14·122.*30·3}]\) -/
theorem pm30_31 {R : α → β → Prop} {y : β} {x : α} :
    Desc R y (fun b => x = b) ↔ R x y ∧ ∀ z, R z y → z = x := by
  rw [pm30_3]
  constructor
  · intro h
    exact ⟨(h x).2 rfl, fun z hz => (h z).1 hz⟩
  · rintro ⟨hx, h⟩ z
    refine ⟨h z, ?_⟩
    rintro rfl
    exact hx

/-- ✱30·32. \(\vdash:\text{E}!Rʻy.\equiv.(Rʻy)Ry \quad[\text{*14·22}]\) -/
theorem pm30_32 {R : α → β → Prop} {y : β} : EDesc R y ↔ Desc R y (fun b => R b y) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb, (hb b).2 rfl⟩
  · rintro ⟨b, hb, -⟩
    exact ⟨b, hb⟩

/-- ✱30·33. \[\begin{align}&\vdash\colon\colon\text{E}!Rʻy.\supset\colon\ldotp \psi(Rʻy):\equiv:(\exists x).xRy.\psi x:\equiv:xRy.\supset_{x}.\psi x\\ &\quad[\text{*14·26}]\end{align}\] -/
theorem pm30_33 {R : α → β → Prop} {y : β} {ψ : α → Prop} :
    EDesc R y →
      ((Desc R y ψ ↔ ∃ x, R x y ∧ ψ x) ∧ ((∃ x, R x y ∧ ψ x) ↔ ∀ x, R x y → ψ x)) := by
  rintro ⟨b, hb⟩
  rw [desc_of_eq hb]
  have h : ∀ x, R x y ↔ x = b := hb
  simp [h]

/-- ✱30·34. \(\vdash\colon\ldotp xRy.\equiv_{x}.xSy:\supset:\text{E}!Rʻy.\equiv.\text{E}!Sʻy \quad[\text{*14·271}]\) -/
theorem pm30_34 {R S : α → β → Prop} {y : β} :
    (∀ x, R x y ↔ S x y) → (EDesc R y ↔ EDesc S y) := by
  intro h
  simp only [EDesc, EBang, h]

/-- ✱30·341. \(\vdash\colon\ldotp xRy.\equiv_{x}.xSy:\supset:\text{E}!Rʻy.\equiv.Rʻy=Sʻy\) -/
theorem pm30_341 {R S : α → β → Prop} {y : β} :
    (∀ x, R x y ↔ S x y) → (EDesc R y ↔ Desc R y (fun b => Desc S y (fun c => b = c))) := by
  intro h
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb, b, fun x => (h x).symm.trans (hb x), rfl⟩
  · rintro ⟨b, hb, -⟩
    exact ⟨b, hb⟩

/-- ✱30·35. \(\vdash\colon\ldotp R=S.\supset:\text{E}!Rʻy.\equiv.\text{E}!Sʻy \quad[\text{*30·34.*21·43}]\) -/
theorem pm30_35 {R S : α → β → Prop} {y : β} : R = S → (EDesc R y ↔ EDesc S y) := by
  rintro rfl
  exact Iff.rfl

/-- ✱30·36. \(\vdash:\text{E}!Rʻy.R=S.\supset.Rʻy=Sʻy \quad[\text{*14·27.Imp.*21·43}]\) -/
theorem pm30_36 {R S : α → β → Prop} {y : β} :
    EDesc R y ∧ R = S → Desc R y (fun b => Desc S y (fun c => b = c)) := by
  rintro ⟨⟨b, hb⟩, rfl⟩
  exact ⟨b, hb, b, hb, rfl⟩

/-- ✱30·37. \(\vdash:\text{E}!Rʻy.y=z.\supset.Rʻy=Rʻz\) -/
theorem pm30_37 {R : α → β → Prop} {y z : β} :
    EDesc R y ∧ y = z → Desc R y (fun b => Desc R z (fun c => b = c)) := by
  rintro ⟨⟨b, hb⟩, rfl⟩
  exact ⟨b, hb, b, hb, rfl⟩

/-- ✱30·4. \(\vdash\colon\ldotp\text{E}!Rʻy.\supset:a=Rʻy.\equiv.aRy \quad[\text{*14·241}]\) -/
theorem pm30_4 {R : α → β → Prop} {y : β} {a : α} :
    EDesc R y → (Desc R y (fun b => a = b) ↔ R a y) := by
  rintro ⟨b, hb⟩
  rw [desc_of_eq hb]
  exact (hb a).symm

/-- ✱30·41. \(\vdash\colon\ldotp (y).Rʻy=Sʻy.\equiv:(y).\text{E}!Rʻy:R=S\) -/
theorem pm30_41 {R S : α → β → Prop} :
    (∀ y, Desc R y (fun b => Desc S y (fun c => b = c))) ↔ (∀ y, EDesc R y) ∧ R = S := by
  constructor
  · intro h
    refine ⟨fun y => ?_, ?_⟩
    · obtain ⟨b, hb, -⟩ := h y
      exact ⟨b, hb⟩
    · funext x y
      obtain ⟨b, hb, c, hc, rfl⟩ := h y
      exact propext ((hb x).trans (hc x).symm)
  · rintro ⟨h, rfl⟩ y
    obtain ⟨b, hb⟩ := h y
    exact ⟨b, hb, b, hb, rfl⟩

/-- ✱30·42. \(\vdash\colon\ldotp (y).\text{E}!Rʻy.\supset:(y).Rʻy=Sʻy.\equiv.R=S \quad[\text{*30·41}]\) -/
theorem pm30_42 {R S : α → β → Prop} :
    (∀ y, EDesc R y) → ((∀ y, Desc R y (fun b => Desc S y (fun c => b = c))) ↔ R = S) := by
  intro h
  rw [pm30_41]
  exact ⟨fun h' => h'.2, fun e => ⟨h, e⟩⟩

/-- ✱30·5. \(\vdash:\text{E}!PʻQʻz.\supset.\text{E}!Qʻz\) -/
theorem pm30_5 {P : α → β → Prop} {Q : β → γ → Prop} {z : γ} :
    EBang (fun x => Desc Q z (fun w => P x w)) → EDesc Q z := by
  rintro ⟨b, hb⟩
  obtain ⟨c, hc, -⟩ := (hb b).2 rfl
  exact ⟨c, hc⟩

/-- ✱30·501. \(\vdash:\phi(PʻQʻz).\equiv.(\exists b,c).c=Qʻz.b=Pʻc.\phi b\) -/
theorem pm30_501 {P : α → β → Prop} {Q : β → γ → Prop} {z : γ} {φ : α → Prop} :
    Desc2 P Q z φ ↔
      ∃ b c, (Desc Q z (fun d => c = d) ∧ Desc P c (fun d => b = d)) ∧ φ b := by
  rw [desc2_iff]
  constructor
  · rintro ⟨c, hc, b, hb, h⟩
    exact ⟨b, c, ⟨⟨c, hc, rfl⟩, ⟨b, hb, rfl⟩⟩, h⟩
  · rintro ⟨b, c, ⟨⟨c', hc, hcc⟩, ⟨b', hb, hbb⟩⟩, h⟩
    subst hcc hbb
    exact ⟨_, hc, _, hb, h⟩

/-- ✱30·51. \(\vdash:b=PʻQʻz.\equiv.(\exists c).b=Pʻc.c=Qʻz \quad[\text{*30·501.*13·195}]\) -/
theorem pm30_51 {P : α → β → Prop} {Q : β → γ → Prop} {z : γ} {b : α} :
    Desc2 P Q z (fun d => b = d) ↔
      ∃ c, Desc P c (fun d => b = d) ∧ Desc Q z (fun d => c = d) := by
  rw [desc2_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, h, c, hc, rfl⟩
  · rintro ⟨c, h, c', hc, hcc⟩
    subst hcc
    exact ⟨_, hc, h⟩

/-- ✱30·52. \(\vdash:\text{E}!PʻQʻz.\equiv.(\exists b,c).b=Pʻc.c=Qʻz \quad[\text{*30·51.*14·204}]\) -/
theorem pm30_52 {P : α → β → Prop} {Q : β → γ → Prop} {z : γ} :
    EBang (fun x => Desc Q z (fun w => P x w)) ↔
      ∃ b c, Desc P c (fun d => b = d) ∧ Desc Q z (fun d => c = d) := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨c, hc, hbc⟩ := (hb b).2 rfl
    refine ⟨b, c, ⟨b, fun x => ⟨fun hx => (hb x).1 ⟨c, hc, hx⟩, ?_⟩, rfl⟩, c, hc, rfl⟩
    rintro rfl
    exact hbc
  · rintro ⟨b, c, ⟨b', hb, hbb⟩, c', hc, hcc⟩
    subst hbb hcc
    refine ⟨b, fun x => ⟨?_, ?_⟩⟩
    · rintro ⟨d, hd, hx⟩
      have hdc := (hc d).1 ((hd d).2 rfl)
      rw [hdc] at hx
      exact (hb x).1 hx
    · rintro rfl
      exact ⟨_, hc, (hb _).2 rfl⟩

/-!
## [✱31] Converses of relations

*(Vol. 1, p. 251)*

> *Summary of* *31.
>
> If \(R\) is a relation, the relation which \(y\) has to \(x\) when \(x R y\) is called the *converse* of \(R\). Thus *greater* is the converse of *less*, *before* of *after*, *husband* of *wife*. The converse of identity is identity, and the converse of diversity is diversity. The converse of \(R\) is written \(\breve{R}\) (read "\(R\)-converse"). When \(R = \breve{R}\), \(R\) is called a *symmetrical* relation, otherwise it is called *not-symmetrical*. When \(R\) is incompatible with \(\breve{R}\), \(R\) is called *asymmetrical*. Thus "cousin" is symmetrical, "brother" is not-symmetrical (because when \(x\) is the brother of \(y\), \(y\) may be either the brother or the sister of \(x)\), and "husband" is asymmetrical.
>
> The relation of \(\breve{R}\) to \(R\) is called "\(\text{Cnv}\)." It will be shown that every relation has one, and only one, converse; hence, applying the notation of *30, that one is \(\text{Cnv}ʻR\). Thus \(\breve{R} = \text{Cnv}ʻR\). We have thus two notations for the converse of \(R\); the second is more convenient for the converse of a relation not denoted by a single letter.
>
> …

**Lean reading.** `Cnv` is the relation `Q̂P̂{xQy ≡_{x,y} yPx}` between relations of converse
types, and `P̆` is `P˘` (`cnv P`). In the propositions that assert the existence or the value of
`Cnv'P` (✱31·12, ✱31·13, ✱31·131, ✱31·132) and in ✱31·33 (`Cnv'Cnv'P`) the descriptive function is
kept as a description (`Desc Cnv P`, `EDesc Cnv P`, `Desc2 Cnv Cnv P`); elsewhere `Cnv'X` is written
`X˘`, as Basic §5 allows by `desc_Cnv`. Several identities (✱31·14–✱31·16) then hold by `rfl`,
because `P˘` is PM's definition ✱31·02 and `∩̇`, `∪̇`, `−̇` are defined pointwise. In ✱31·51–✱31·52
the bound `P` on the left ranges over `α → β → Prop` and on the right over `β → α → Prop`.

**Status.** proved (all propositions; ✱31·01, ✱31·02 definition).
-/

/-- ✱31·01 (Df). \(\text{Cnv}=\hat{Q}\hat{P}\{xQy.\equiv_{x,y}.yPx\} \quad\text{Df}\) -/
theorem pm31_01 :
    (Cnv : (β → α → Prop) → (α → β → Prop) → Prop) = fun Q P => ∀ x y, Q x y ↔ P y x := rfl

/-- ✱31·02 (Df). \(\breve{P}=\hat{x}\hat{y}(yPx) \quad\text{Df}\) -/
theorem pm31_02 {P : α → β → Prop} : P˘ = fun x y => P y x := rfl

/-- ✱31·1. \(\vdash\colon\ldotp Q\, \text{Cnv}\, P.\equiv:xQy.\equiv_{x,y}.yPx \quad[\text{*21·3.(*31·01)}]\) -/
theorem pm31_1 {Q : β → α → Prop} {P : α → β → Prop} : Cnv Q P ↔ ∀ x y, Q x y ↔ P y x :=
  Iff.rfl

/-- ✱31·101. \(\vdash:Q\, \text{Cnv}\, P.R\, \text{Cnv}\, P.\supset.Q=R\) -/
theorem pm31_101 {Q R : β → α → Prop} {P : α → β → Prop} : Cnv Q P ∧ Cnv R P → Q = R := by
  rintro ⟨hQ, hR⟩
  rw [Cnv_iff] at hQ hR
  rw [hQ, hR]

/-- ✱31·11. \(\vdash:x\breve{P}y.\equiv.yPx \quad[\text{*21·3.(*31·02)}]\) -/
theorem pm31_11 {P : α → β → Prop} {x : β} {y : α} : P˘ x y ↔ P y x := Iff.rfl

/-- ✱31·111. \(\vdash.\breve{P}\,\text{Cnv} P \quad[\text{*31·1·11}]\) -/
theorem pm31_111 {P : α → β → Prop} : Cnv P˘ P := fun _ _ => Iff.rfl

/-- ✱31·12. \(\vdash.\breve{P}=\text{Cnv}ʻP\) -/
theorem pm31_12 {P : α → β → Prop} : Desc Cnv P (fun Q => P˘ = Q) :=
  (desc_Cnv P (fun Q => P˘ = Q)).2 rfl

/-- ✱31·13. \(\vdash.\text{E}!\text{Cnv}ʻP \quad[\text{*14·21.*31·12}]\) -/
theorem pm31_13 {P : α → β → Prop} : EDesc Cnv P := ⟨P˘, fun _ => Cnv_iff⟩

/-- ✱31·131. \(\vdash:x(\text{Cnv}ʻP)y.\equiv.yPx \quad[\text{*31·11·12.*21·43}]\) -/
theorem pm31_131 {P : α → β → Prop} {x : β} {y : α} :
    Desc Cnv P (fun Q => Q x y) ↔ P y x :=
  desc_Cnv P (fun Q => Q x y)

/-- ✱31·132. \(\vdash:Q\, \text{Cnv}\, P.\equiv.Q=\text{Cnv}ʻP.\equiv.Q=\breve{P} \quad[\text{*30·4.*31·13·12}]\) -/
theorem pm31_132 {Q : β → α → Prop} {P : α → β → Prop} :
    (Cnv Q P ↔ Desc Cnv P (fun R => Q = R)) ∧ (Desc Cnv P (fun R => Q = R) ↔ Q = P˘) := by
  rw [desc_Cnv]
  exact ⟨Cnv_iff, Iff.rfl⟩

/-- ✱31·14. \(\vdash.\text{Cnv}ʻ(P\dot{\cap}Q)=\text{Cnv}ʻP\dot{\cap}\text{Cnv}ʻQ\) -/
theorem pm31_14 {P Q : α → β → Prop} : (P ⩀ Q)˘ = P˘ ⩀ Q˘ := rfl

/-- ✱31·15. \(\vdash.\text{Cnv}ʻ(P\unicode{x228d}Q)=\text{Cnv}ʻP\unicode{x228d}\text{Cnv}ʻQ \quad[\text{Similar proof}]\) -/
theorem pm31_15 {P Q : α → β → Prop} : (P ⊍ Q)˘ = P˘ ⊍ Q˘ := rfl

/-- ✱31·16. \(\vdash.\text{Cnv}ʻ\dot{-}P=\dot{-}(\text{Cnv}ʻP)\) -/
theorem pm31_16 {P : α → β → Prop} : (∸P)˘ = ∸(P˘) := rfl

/-- ✱31·17. \(\vdash\colon\ldotp y=\breve{P}ʻx.\equiv:xPz.\equiv_{z}.z=y \quad[\text{*30·3.*31·11}]\) -/
theorem pm31_17 {P : α → β → Prop} {x : α} {y : β} :
    Desc P˘ x (fun b => y = b) ↔ ∀ z, P x z ↔ z = y :=
  pm30_3

/-- ✱31·18. \(\vdash\colon\ldotp \text{E}!\breve{P}ʻx.\equiv:(\exists y):xPz.\equiv_{z}.z=y \quad[\text{*30·2.*31·11}]\) -/
theorem pm31_18 {P : α → β → Prop} {x : α} : EDesc P˘ x ↔ ∃ y, ∀ z, P x z ↔ z = y := Iff.rfl

/-- ✱31·21. \(\vdash.\text{Cnv}ʻ\dot{\Lambda}=\dot{\Lambda}\) -/
theorem pm31_21 : (rNull : α → β → Prop)˘ = rNull := by
  funext x y
  apply propext
  exact ⟨fun h hv => h ⟨hv.2, hv.1⟩, fun h hv => h ⟨hv.2, hv.1⟩⟩

/-- ✱31·22. \(\vdash.\text{Cnv}ʻ\dot{\text{V}}=\dot{\text{V}} \quad[\text{Similar proof}]\) -/
theorem pm31_22 : (rV : α → β → Prop)˘ = rV := by
  funext x y
  apply propext
  exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩

/-- ✱31·23. \(\vdash:\breve{P}=\dot{\text{V}}.\equiv.P=\dot{\text{V}}\) -/
theorem pm31_23 {P : α → β → Prop} : P˘ = rV ↔ P = rV := by
  constructor
  · intro h
    have := congrArg cnv h
    rw [pm31_22] at this
    exact this
  · rintro rfl
    exact pm31_22

/-- ✱31·24. \(\vdash:\breve{P}=\dot{\Lambda}.\equiv.P=\dot{\Lambda} \quad[\text{Similar proof}]\) -/
theorem pm31_24 {P : α → β → Prop} : P˘ = rNull ↔ P = rNull := by
  constructor
  · intro h
    have := congrArg cnv h
    rw [pm31_21] at this
    exact this
  · rintro rfl
    exact pm31_21

/-- ✱31·32. \(\vdash:P=Q.\equiv.\breve{P}=\breve{Q}\) -/
theorem pm31_32 {P Q : α → β → Prop} : P = Q ↔ P˘ = Q˘ :=
  ⟨congrArg cnv, congrArg cnv⟩

/-- ✱31·33. \(\vdash.\text{Cnv}ʻ\text{Cnv}ʻP=P\) -/
theorem pm31_33 {P : α → β → Prop} : Desc2 Cnv Cnv P (fun Q => Q = P) := by
  rw [desc2_iff, desc_Cnv]
  exact (desc_Cnv P˘ (fun Q => Q = P)).2 rfl

/-- ✱31·34. \(\vdash:P=\breve{Q}.\equiv.Q=\breve{P}\) -/
theorem pm31_34 {P : α → β → Prop} {Q : β → α → Prop} : P = Q˘ ↔ Q = P˘ := by
  constructor
  · rintro rfl
    rfl
  · rintro rfl
    rfl

/-- ✱31·4. \(\vdash:P\unicode{x2abd}Q.\equiv.\breve{P}\unicode{x2abd}\breve{Q} \quad[\text{*31·11.*11·33}]\) -/
theorem pm31_4 {P Q : α → β → Prop} : P ⪽ Q ↔ P˘ ⪽ Q˘ :=
  ⟨fun h x y => h y x, fun h x y => h y x⟩

/-- ✱31·41. \(\vdash:P\unicode{x2abd}\breve{Q}.\equiv.\breve{P}\unicode{x2abd}Q \quad[\text{*31·4·33·12}]\) -/
theorem pm31_41 {P : α → β → Prop} {Q : β → α → Prop} : P ⪽ Q˘ ↔ P˘ ⪽ Q :=
  ⟨fun h x y => h y x, fun h x y => h y x⟩

/-- ✱31·5. \(\vdash:\dot{\exists}!P.\equiv.\dot{\exists}!\breve{P} \quad[\text{*31·24.Transp.*25·54}]\) -/
theorem pm31_5 {P : α → β → Prop} : rEx P ↔ rEx P˘ := by
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨y, x, h⟩
  · rintro ⟨x, y, h⟩
    exact ⟨y, x, h⟩

/-- ✱31·51. \(\vdash:(P).f\breve{P}.\equiv.(P).fP\) -/
theorem pm31_51 {f : (β → α → Prop) → Prop} : (∀ P : α → β → Prop, f P˘) ↔ ∀ P, f P :=
  ⟨fun h P => h P˘, fun h P => h P˘⟩

/-- ✱31·52. \(\vdash:(\exists P).f\breve{P}.\equiv.(\exists P).fP \quad[\text{*31·51.Transp}]\) -/
theorem pm31_52 {f : (β → α → Prop) → Prop} : (∃ P : α → β → Prop, f P˘) ↔ ∃ P, f P := by
  constructor
  · rintro ⟨P, h⟩
    exact ⟨P˘, h⟩
  · rintro ⟨P, h⟩
    exact ⟨P˘, h⟩

/-!
## [✱32] Referents and relata of a given term with respect to a given relation

*(Vol. 1, p. 255)*

> *Summary of* *32.
>
> …

**Lean reading.** `R⃗` (`Rfwd R`) and `R⃖` (`Rbwd R`) are the relations of the class of referents
(relata) of a term to the term, and `sg`, `gs` the relations of `R⃗`, `R⃖` to `R`; all four are
`graph`s, so their descriptive functions always exist. The propositions asserting existence or
value of these descriptive functions (✱32·11–✱32·133, ✱32·21–✱32·251) are stated with
`Desc`/`EDesc`; elsewhere `R⃗'y`, `R⃖'x` are written `refs R y`, `rels R x`, and
`{sg'(R ∩̇ S)}'y` is written `refs (R ⩀ S) y` (by `desc_graph` twice, Basic §5). ✱32·24·241 keep
`sg'`, `gs'` as descriptions. In ✱32·31 and ✱32·33 the e-text prints `R⃖'x` twice on the right
for `R⃖'x … S⃖'x`; the intended statements are proved.

**Status.** proved (all propositions; ✱32·01–✱32·04 definition; ✱32·31, ✱32·33 proved (reading):
misprint `R⃖'x` for `S⃖'x`, see their docstrings).
-/

/-- ✱32·01 (Df). \(\overrightarrow{R} = \hat{\alpha}\hat{y}\{\alpha = \hat{x}(x R y)\} \quad \text{Df}\) -/
theorem pm32_01 {R : α → β → Prop} : Rfwd R = fun A y => A = {x | R x y} := rfl

/-- ✱32·02 (Df). \(\overleftarrow{R} = \hat{\beta}\hat{x}\{\beta = \hat{y}(xRy)\} \quad \text{Df}\) -/
theorem pm32_02 {R : α → β → Prop} : Rbwd R = fun B x => B = {y | R x y} := rfl

/-- ✱32·03 (Df). \(\text{sg}=\hat{A}\hat{R}(A=\overrightarrow{R}) \quad\text{Df}\) -/
theorem pm32_03 :
    (sg : (Set α → β → Prop) → (α → β → Prop) → Prop) = fun A R => A = Rfwd R := rfl

/-- ✱32·04 (Df). \(\text{gs}=\hat{A}\hat{R}(A=\overleftarrow{R}) \quad\text{Df}\) -/
theorem pm32_04 :
    (gs : (Set β → α → Prop) → (α → β → Prop) → Prop) = fun A R => A = Rbwd R := rfl

/-- ✱32·1. \(\vdash:\alpha\overrightarrow{R}y.\equiv.\alpha=\hat{x}(xRy) \quad[\text{*21·3.(*32·01)}]\) -/
theorem pm32_1 {R : α → β → Prop} {A : Set α} {y : β} : Rfwd R A y ↔ A = {x | R x y} :=
  Iff.rfl

/-- ✱32·101. \(\vdash:\beta\overleftarrow{R}x.\equiv.\beta=\hat{y}(xRy) \quad[\text{*21·3.(*32·02)}]\) -/
theorem pm32_101 {R : α → β → Prop} {B : Set β} {x : α} : Rbwd R B x ↔ B = {y | R x y} :=
  Iff.rfl

/-- ✱32·11. \(\vdash.\hat{x}(xRy)=\overrightarrow{R}ʻy \quad[\text{*32·1.*30·3}]\) -/
theorem pm32_11 {R : α → β → Prop} {y : β} : Desc (Rfwd R) y (fun A => {x | R x y} = A) :=
  (desc_graph (refs R) y _).2 rfl

/-- ✱32·111. \(\vdash.\hat{y}(xRy)=\overleftarrow{R}ʻx \quad[\text{*32·101.*30·3}]\) -/
theorem pm32_111 {R : α → β → Prop} {x : α} : Desc (Rbwd R) x (fun B => {y | R x y} = B) :=
  (desc_graph (rels R) x _).2 rfl

/-- ✱32·12. \(\vdash.\text{E}!\overrightarrow{R}ʻy \quad[\text{*32·11.*14·21}]\) -/
theorem pm32_12 {R : α → β → Prop} {y : β} : EDesc (Rfwd R) y := EDesc_graph (refs R) y

/-- ✱32·121. \(\vdash.\text{E}!\overleftarrow{R}ʻx \quad[\text{*32·111.*14·21}]\) -/
theorem pm32_121 {R : α → β → Prop} {x : α} : EDesc (Rbwd R) x := EDesc_graph (rels R) x

/-- ✱32·13. \(\vdash.\overrightarrow{R}ʻy=\hat{x}(xRy) \quad[\text{*32·11.*20·59}]\) -/
theorem pm32_13 {R : α → β → Prop} {y : β} : Desc (Rfwd R) y (fun A => A = {x | R x y}) :=
  (desc_graph (refs R) y _).2 rfl

/-- ✱32·131. \(\vdash.\overleftarrow{R}ʻx=\hat{y}(xRy) \quad[\text{*32·111.*20·59}]\) -/
theorem pm32_131 {R : α → β → Prop} {x : α} : Desc (Rbwd R) x (fun B => B = {y | R x y}) :=
  (desc_graph (rels R) x _).2 rfl

/-- ✱32·132. \(\vdash:\alpha\overrightarrow{R}y.\equiv.\alpha=\overrightarrow{R}ʻy.\equiv.\alpha=\hat{x}(xRy) \quad[\text{*32·1·13.*20·57}]\) -/
theorem pm32_132 {R : α → β → Prop} {A : Set α} {y : β} :
    (Rfwd R A y ↔ Desc (Rfwd R) y (fun B => A = B)) ∧
      (Desc (Rfwd R) y (fun B => A = B) ↔ A = {x | R x y}) :=
  ⟨(desc_graph (refs R) y (fun B => A = B)).symm, desc_graph (refs R) y (fun B => A = B)⟩

/-- ✱32·133. \(\vdash:\beta\overleftarrow{R}x.\equiv.\beta=\overleftarrow{R}ʻx.\equiv.\beta=\hat{y}(xRy) \quad[\text{*32·101·131.*20·57}]\) -/
theorem pm32_133 {R : α → β → Prop} {B : Set β} {x : α} :
    (Rbwd R B x ↔ Desc (Rbwd R) x (fun C => B = C)) ∧
      (Desc (Rbwd R) x (fun C => B = C) ↔ B = {y | R x y}) :=
  ⟨(desc_graph (rels R) x (fun C => B = C)).symm, desc_graph (rels R) x (fun C => B = C)⟩

/-- ✱32·14. \(\vdash:\overrightarrow{R}=\overrightarrow{S}.\equiv.R=S\) -/
theorem pm32_14 {R S : α → β → Prop} : Rfwd R = Rfwd S ↔ R = S := by
  constructor
  · intro h
    funext x y
    have e : refs R y = refs S y := (congrFun (congrFun h (refs R y)) y).mp rfl
    exact propext (Set.ext_iff.mp e x)
  · rintro rfl
    rfl

/-- ✱32·15. \(\vdash:\overleftarrow{R}=\overleftarrow{S}.\equiv.R=S \quad[\text{Similar proof}]\) -/
theorem pm32_15 {R S : α → β → Prop} : Rbwd R = Rbwd S ↔ R = S := by
  constructor
  · intro h
    funext x y
    have e : rels R x = rels S x := (congrFun (congrFun h (rels R x)) x).mp rfl
    exact propext (Set.ext_iff.mp e y)
  · rintro rfl
    rfl

/-- ✱32·16. \(\vdash:\overrightarrow{R}=\overrightarrow{S}.\equiv.\overleftarrow{R}=\overleftarrow{S}.\equiv.R=S \quad[\text{*32·14·15}]\) -/
theorem pm32_16 {R S : α → β → Prop} :
    (Rfwd R = Rfwd S ↔ Rbwd R = Rbwd S) ∧ (Rbwd R = Rbwd S ↔ R = S) :=
  ⟨pm32_14.trans pm32_15.symm, pm32_15⟩

/-- ✱32·18. \(\vdash:x\in \overrightarrow{R}ʻy.\equiv.xRy \quad[\text{*32·13.*20·33}]\) -/
theorem pm32_18 {R : α → β → Prop} {x : α} {y : β} : x ∈ refs R y ↔ R x y := Iff.rfl

/-- ✱32·181. \(\vdash:y\in \overleftarrow{R}ʻx.\equiv.xRy \quad[\text{*32·131.*20·33}]\) -/
theorem pm32_181 {R : α → β → Prop} {x : α} {y : β} : y ∈ rels R x ↔ R x y := Iff.rfl

/-- ✱32·182. \(\vdash:x\in \overrightarrow{R}ʻy.\equiv.y\in \overleftarrow{R}ʻx \quad[\text{*32·18·181}]\) -/
theorem pm32_182 {R : α → β → Prop} {x : α} {y : β} : x ∈ refs R y ↔ y ∈ rels R x := Iff.rfl

/-- ✱32·19. \(\vdash:R\unicode{x2abd}S.\supset.\overrightarrow{R}ʻy\subset\overrightarrow{S}ʻy.\overleftarrow{R}ʻx\subset\overleftarrow{S}ʻx\) -/
theorem pm32_19 {R S : α → β → Prop} {x : α} {y : β} :
    R ⪽ S → refs R y ⊆ refs S y ∧ rels R x ⊆ rels S x :=
  fun h => ⟨fun z hz => h z y hz, fun z hz => h x z hz⟩

/-- ✱32·2. \(\vdash:A \text{sg} R.\equiv.A=\overrightarrow{R} \quad[\text{*21·3.(*32·03)}]\) -/
theorem pm32_2 {A : Set α → β → Prop} {R : α → β → Prop} : sg A R ↔ A = Rfwd R := Iff.rfl

/-- ✱32·201. \(\vdash:A \text{gs} R.\equiv.A=\overleftarrow{R} \quad[\text{*21·3.(*32·04)}]\) -/
theorem pm32_201 {A : Set β → α → Prop} {R : α → β → Prop} : gs A R ↔ A = Rbwd R := Iff.rfl

/-- ✱32·21. \(\vdash.\overrightarrow{R}=\text{sg}ʻR \quad[\text{*32·2.*30·3}]\) -/
theorem pm32_21 {R : α → β → Prop} : Desc sg R (fun A => Rfwd R = A) :=
  (desc_graph Rfwd R _).2 rfl

/-- ✱32·211. \(\vdash.\overleftarrow{R}=\text{gs}ʻR \quad[\text{*32·201.*30·3}]\) -/
theorem pm32_211 {R : α → β → Prop} : Desc gs R (fun A => Rbwd R = A) :=
  (desc_graph Rbwd R _).2 rfl

/-- ✱32·22. \(\vdash.\text{E}!\text{sg}ʻR \quad[\text{*32·21.*14·21}]\) -/
theorem pm32_22 {R : α → β → Prop} : EDesc sg R := EDesc_graph Rfwd R

/-- ✱32·221. \(\vdash.\text{E}!gsʻR \quad[\text{*32·211.*14·21}]\) -/
theorem pm32_221 {R : α → β → Prop} : EDesc gs R := EDesc_graph Rbwd R

/-- ✱32·23. \(\vdash.\text{sg}ʻR=\overrightarrow{R} \quad[\text{*32·21.*21·2·57}]\) -/
theorem pm32_23 {R : α → β → Prop} : Desc sg R (fun A => A = Rfwd R) :=
  (desc_graph Rfwd R _).2 rfl

/-- ✱32·231. \(\vdash.\text{gs}ʻR=\overleftarrow{R} \quad[\text{*32·211.*21·2·57}]\) -/
theorem pm32_231 {R : α → β → Prop} : Desc gs R (fun A => A = Rbwd R) :=
  (desc_graph Rbwd R _).2 rfl

/-- ✱32·24. \(\vdash.\text{sg}ʻ\breve{R}=\text{gs}ʻR\) -/
theorem pm32_24 {R : α → β → Prop} : Desc sg R˘ (fun A => Desc gs R (fun B => A = B)) :=
  (desc_graph Rfwd R˘ _).2 ((desc_graph Rbwd R _).2 rfl)

/-- ✱32·241. \(\vdash.\text{gs}ʻ\breve{R}=\text{sg}ʻR \quad[\text{Similar proof}]\) -/
theorem pm32_241 {R : α → β → Prop} : Desc gs R˘ (fun A => Desc sg R (fun B => A = B)) :=
  (desc_graph Rbwd R˘ _).2 ((desc_graph Rfwd R _).2 rfl)

/-- ✱32·25. \(\vdash:A \text{sg} R.\equiv.A=\text{sg}ʻR \quad[\text{*30·4.*32·22}]\) -/
theorem pm32_25 {A : Set α → β → Prop} {R : α → β → Prop} :
    sg A R ↔ Desc sg R (fun B => A = B) :=
  (desc_graph Rfwd R (fun B => A = B)).symm

/-- ✱32·251. \(\vdash:A \text{gs} R.\equiv.A=\text{gs}ʻR \quad[\text{*30·4.*32·221}]\) -/
theorem pm32_251 {A : Set β → α → Prop} {R : α → β → Prop} :
    gs A R ↔ Desc gs R (fun B => A = B) :=
  (desc_graph Rbwd R (fun B => A = B)).symm

/-- ✱32·3. \(\vdash.{\text{sg}ʻ(R\dot{\cap}S)}ʻy=\overrightarrow{R}ʻy\cap \overrightarrow{S}ʻy\) -/
theorem pm32_3 {R S : α → β → Prop} {y : β} : refs (R ⩀ S) y = refs R y ∩ refs S y :=
  Set.ext fun _ => Iff.rfl

/-- ✱32·31. \(\vdash.\{\text{gs}ʻ(R\dot{\cap}S)\}ʻx=\overleftarrow{R}ʻx\cap \overleftarrow{R}ʻx\)

**Status.** proved (reading): misprint (not in the errata): the e-text prints `R⃖'x ∩ R⃖'x` for
`R⃖'x ∩ S⃖'x` on the right; as printed the proposition would say `gs'(R ∩̇ S)'x = R⃖'x`, which is
false (take `S` null and `R` not). PM says the proof is similar to that of ✱32·3. -/
theorem pm32_31 {R S : α → β → Prop} {x : α} : rels (R ⩀ S) x = rels R x ∩ rels S x :=
  Set.ext fun _ => Iff.rfl

/-- ✱32·32. \(\vdash.\{\text{sg}ʻ(R\unicode{x228d}S)\}ʻy=\overrightarrow{R}ʻy\cup \overrightarrow{S}ʻy\) -/
theorem pm32_32 {R S : α → β → Prop} {y : β} : refs (R ⊍ S) y = refs R y ∪ refs S y :=
  Set.ext fun _ => Iff.rfl

/-- ✱32·33. \(\vdash.\{\text{gs}ʻ(R\unicode{x228d}S)\}ʻx=\overleftarrow{R}ʻx\cup \overleftarrow{R}ʻx\)

**Status.** proved (reading): misprint (not in the errata): the e-text prints `R⃖'x ∪ R⃖'x` for
`R⃖'x ∪ S⃖'x` on the right (as in ✱32·31; the printed form is false for `R` null and `S` not). -/
theorem pm32_33 {R S : α → β → Prop} {x : α} : rels (R ⊍ S) x = rels R x ∪ rels S x :=
  Set.ext fun _ => Iff.rfl

/-- ✱32·34. \(\vdash.\{\text{sg}ʻ(\dot{-}R)\}ʻy=-\overrightarrow{R}ʻy\) -/
theorem pm32_34 {R : α → β → Prop} {y : β} : refs (∸R) y = (refs R y)ᶜ :=
  Set.ext fun _ => Iff.rfl

/-- ✱32·35. \(\vdash.\{\text{gs}ʻ(\dot{-}R)\}ʻx=-\overleftarrow{R}ʻx\) -/
theorem pm32_35 {R : α → β → Prop} {x : α} : rels (∸R) x = (rels R x)ᶜ :=
  Set.ext fun _ => Iff.rfl

/-- ✱32·4. \(\vdash\colon\ldotp \text{E}!Rʻz.\equiv:\exists !\overrightarrow{R}ʻz:x,y\in \overrightarrow{R}ʻz.\supset_{x,y}.x=y \quad[\text{*30·21.*32·18}]\) -/
theorem pm32_4 {R : α → β → Prop} {z : β} :
    EDesc R z ↔ (refs R z).Nonempty ∧ ∀ x y, x ∈ refs R z ∧ y ∈ refs R z → x = y :=
  pm30_21

/-- ✱32·41. \(\vdash\colon\ldotp \text{E}!Sʻy.\supset:\overrightarrow{R}ʻy=\overrightarrow{S}ʻy.\equiv.Rʻy=Sʻy\) -/
theorem pm32_41 {R S : α → β → Prop} {y : β} :
    EDesc S y → (refs R y = refs S y ↔ Desc R y (fun b => Desc S y (fun c => b = c))) := by
  rintro ⟨c, hc⟩
  constructor
  · intro h
    refine ⟨c, fun x => ?_, c, hc, rfl⟩
    exact (Set.ext_iff.mp h x).trans (hc x)
  · rintro ⟨b, hb, c', hc', hbc⟩
    subst hbc
    ext x
    exact (hb x).trans (hc' x).symm

/-- ✱32·42. \(\vdash\colon\ldotp \overrightarrow{R}ʻy=\overrightarrow{S}ʻy.\supset:\text{E}!Rʻy.\equiv.\text{E}!Sʻy \quad[\text{*30·34.*32·18}]\) -/
theorem pm32_42 {R S : α → β → Prop} {y : β} :
    refs R y = refs S y → (EDesc R y ↔ EDesc S y) :=
  fun h => pm30_34 (fun x => Set.ext_iff.mp h x)

/-!
## [✱33] Domains, converse domains, and fields of relations

*(Vol. 1, p. 260)*

> *Summary of* *33.
>
> If \(R\) is any relation, the *domain* of \(R\), which we denote by \(\text{D}ʻR\), is the class of terms which have the relation \(R\) to something or other; the *converse domain*, \(\text{ᗡ}ʻR\), is the class of terms to which something or other has the relation \(R\); and the *field*, \(CʻR\), is the sum of the domain and the converse domain. (Note that the field is only significant when \(R\) is a *homogeneous* relation.)
>
> The above notations \(\text{D}ʻR\), \(\text{ᗡ}ʻR\), \(CʻR\) are derivative from the notations \(\text{D}\), \(\text{ᗡ}\), \(C\) for the relations, to a relation, of its domain, converse domain, and field respectively. We are to have \[ \begin{align} \text{D}ʻR &= \hat{x}\{(\exists y).xRy\}\\ \text{ᗡ}ʻR &= \hat{y}\{(\exists x).xRy\}\\ CʻR &= \hat{x}\{(\exists y):xRy .\lor. yRx\}\text{;}\\ \end{align} \] hence we define \(\text{D}\), \(\text{ᗡ}\), \(C\) as follows:
>
> *33·01. \(\text{D} = \hat{\alpha}\hat{R}[\alpha = \hat{x}\{(\exists y).xRy\}] \quad \text{Df}\)
>
> *33·02. \(\text{ᗡ} = \hat{\beta}\hat{R}[\beta = \hat{y}\{(\exists x).xRy\}] \quad \text{Df}\)
>
> *33·03. \(C = \hat{\gamma}\hat{R}[\gamma = \hat{x}\{(\exists y):xRy .\lor. yRx\}] \quad \text{Df}\)
>
> …

**Lean reading.** `D`, `ᗡ`, `C` are the `graph`s of `dom`, `codom`, `fld` (`fld` and `C` only for
homogeneous relations `R : α → α → Prop`, as PM notes), and `F` relates a member of the field to
the relation. Existence and value of `D'R`, `ᗡ'R`, `C'R` (✱33·11–✱33·125) are stated with
`Desc`/`EDesc`; elsewhere `dom R`, `codom R`, `fld R` are used (Basic §5), and `D⃖'α` is
`rels D A`. Chains of identities (✱33·24, ✱33·241, ✱33·272, ✱33·28, ✱33·29) are conjunctions of
their links, bracketed to the left. PM's `∃!α` is `A.Nonempty`. In ✱33·28, ✱33·29, ✱33·32 the
e-text prints `V`, `Λ` where only `V̇`, `Λ̇` are significant (erratum Vol. I, p. 218); in ✱33·61,
✱33·62 it omits `α =` on the right. The e-text's misprinted citation `*32·123` in ✱33·125 does not
affect the statement.

**Status.** proved (all propositions; ✱33·01–✱33·04 definition (✱33·02 with a transcription
error in the definiens); ✱33·28, ✱33·29, ✱33·32 proved (reading): `V`/`Λ` for `V̇`/`Λ̇`; ✱33·61,
✱33·62 proved (reading): omitted `α =`).
-/

/-- ✱33·01 (Df). \(\text{D}=\hat{\alpha}\hat{R}[\alpha=\hat{x}\{(\exists y).xRy\}] \quad\text{Df}\) -/
theorem pm33_01 :
    (D : Set α → (α → β → Prop) → Prop) = fun A R => A = {x | ∃ y, R x y} := rfl

/-- ✱33·02 (Df). \(\text{ᗡ}=\hat{\beta}\hat{R}[\hat{\beta}=\hat{y}\{(\exists x).xRy\}] \quad\text{Df}\)

**Status.** definition: the e-text prints `β̂ =` for `β =` in the definiens (transcription error, Basic
§9); the defining equation is that of PM's `ᗡ = β̂R̂[β = ŷ{(∃x).xRy}]`. -/
theorem pm33_02 :
    (Dcnv : Set β → (α → β → Prop) → Prop) = fun B R => B = {y | ∃ x, R x y} := rfl

/-- ✱33·03 (Df). \(C=\hat{\gamma}\hat{R}[\gamma=\hat{x}\{(\exists y):xRy.\lor .yRx\}] \quad\text{Df}\) -/
theorem pm33_03 :
    (C : Set α → (α → α → Prop) → Prop) = fun G R => G = {x | ∃ y, R x y ∨ R y x} := rfl

/-- ✱33·04 (Df). \(F=\hat{x}\hat{R}\{(\exists y):xRy.\lor .yRx\} \quad\text{Df}\) -/
theorem pm33_04 : (F : α → (α → α → Prop) → Prop) = fun x R => ∃ y, R x y ∨ R y x := rfl

/-- ✱33·1. \(\vdash:\alpha\text{D}R.\equiv.\alpha=\hat{x}\{(\exists y).xRy\} \quad[\text{*21·3.(*33·01)}]\) -/
theorem pm33_1 {A : Set α} {R : α → β → Prop} : D A R ↔ A = {x | ∃ y, R x y} := Iff.rfl

/-- ✱33·101. \(\vdash:\beta\text{ᗡ}R.\equiv.\beta=\hat{y}\{(\exists x).xRy\}\) -/
theorem pm33_101 {B : Set β} {R : α → β → Prop} : Dcnv B R ↔ B = {y | ∃ x, R x y} := Iff.rfl

/-- ✱33·102. \(\vdash:\gamma CR.\equiv.\gamma=\hat{x}\{(\exists y):xRy.\lor .yRx\}\) -/
theorem pm33_102 {G : Set α} {R : α → α → Prop} : C G R ↔ G = {x | ∃ y, R x y ∨ R y x} :=
  Iff.rfl

/-- ✱33·103. \(\vdash\colon\ldotp xFR.\equiv:(\exists y):xRy.\lor .yRx\) -/
theorem pm33_103 {x : α} {R : α → α → Prop} : F x R ↔ ∃ y, R x y ∨ R y x := Iff.rfl

/-- ✱33·11. \(\vdash.\text{D}ʻR=\hat{x}\{(\exists y).xRy\} \quad[\text{*33·1.*30·3.*20·59}]\) -/
theorem pm33_11 {R : α → β → Prop} : Desc D R (fun A => A = {x | ∃ y, R x y}) :=
  (desc_graph dom R _).2 rfl

/-- ✱33·111. \(\vdash.\text{ᗡ}ʻR=\hat{y}\{(\exists x).xRy\}\) -/
theorem pm33_111 {R : α → β → Prop} : Desc Dcnv R (fun B => B = {y | ∃ x, R x y}) :=
  (desc_graph codom R _).2 rfl

/-- ✱33·112. \(\vdash.CʻR=\hat{x}\{(\exists y):xRy.\lor .yRx\}\) -/
theorem pm33_112 {R : α → α → Prop} : Desc C R (fun G => G = {x | ∃ y, R x y ∨ R y x}) :=
  (desc_graph fld R _).2 rfl

/-- ✱33·12. \(\vdash.\text{E}!\text{D}ʻR \quad[\text{*33·11.*14·21}]\) -/
theorem pm33_12 {R : α → β → Prop} : EDesc D R := EDesc_graph dom R

/-- ✱33·121. \(\vdash.\text{E}!\text{ᗡ}ʻR\) -/
theorem pm33_121 {R : α → β → Prop} : EDesc Dcnv R := EDesc_graph codom R

/-- ✱33·122. \(\vdash.\text{E}!CʻR\) -/
theorem pm33_122 {R : α → α → Prop} : EDesc C R := EDesc_graph fld R

/-- ✱33·123. \(\vdash:\alpha\text{D}R.\equiv.\alpha=\text{D}ʻR \quad[\text{*30·4.*33·12}]\) -/
theorem pm33_123 {A : Set α} {R : α → β → Prop} : D A R ↔ Desc D R (fun B => A = B) :=
  (desc_graph dom R (fun B => A = B)).symm

/-- ✱33·124. \(\vdash:\beta\text{ᗡ}R.\equiv.\beta=\text{ᗡ}ʻR \quad[\text{*30·4.*33·121}]\) -/
theorem pm33_124 {B : Set β} {R : α → β → Prop} : Dcnv B R ↔ Desc Dcnv R (fun A => B = A) :=
  (desc_graph codom R (fun A => B = A)).symm

/-- ✱33·125. \(\vdash:\gamma CR.\equiv.\gamma=CʻR \quad[\text{*30·4.*32·123}]\) -/
theorem pm33_125 {G : Set α} {R : α → α → Prop} : C G R ↔ Desc C R (fun A => G = A) :=
  (desc_graph fld R (fun A => G = A)).symm

/-- ✱33·13. \(\vdash:x\in \text{D}ʻR.\equiv.(\exists y).xRy \quad[\text{*33·11.*20·3·57}]\) -/
theorem pm33_13 {x : α} {R : α → β → Prop} : x ∈ dom R ↔ ∃ y, R x y := Iff.rfl

/-- ✱33·131. \(\vdash:y\in \text{ᗡ}ʻR.\equiv.(\exists x).xRy\) -/
theorem pm33_131 {y : β} {R : α → β → Prop} : y ∈ codom R ↔ ∃ x, R x y := Iff.rfl

/-- ✱33·132. \(\vdash\colon\ldotp x\in CʻR.\equiv:(\exists y):xRy.\lor .yRx\) -/
theorem pm33_132 {x : α} {R : α → α → Prop} : x ∈ fld R ↔ ∃ y, R x y ∨ R y x := Iff.rfl

/-- ✱33·14. \(\vdash:xRy.\supset.x\in \text{D}ʻR.y\in \text{ᗡ}ʻR\) -/
theorem pm33_14 {R : α → β → Prop} {x : α} {y : β} : R x y → x ∈ dom R ∧ y ∈ codom R :=
  fun h => ⟨mem_dom_of h, mem_codom_of h⟩

/-- ✱33·15. \(\vdash.\overrightarrow{R}ʻy\subset\text{D}ʻR\) -/
theorem pm33_15 {R : α → β → Prop} {y : β} : refs R y ⊆ dom R := fun _ hx => mem_dom_of hx

/-- ✱33·152. \(\vdash.\overrightarrow{R}ʻx\cup \overleftarrow{R}ʻx\subset CʻR\) -/
theorem pm33_152 {R : α → α → Prop} {x : α} : refs R x ∪ rels R x ⊆ fld R := by
  rintro z (h | h)
  · exact ⟨x, Or.inl h⟩
  · exact ⟨x, Or.inr h⟩

/-- ✱33·16. \(\vdash.CʻR=\text{D}ʻR\cup \text{ᗡ}ʻR\) -/
theorem pm33_16 {R : α → α → Prop} : fld R = dom R ∪ codom R := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact Or.inl ⟨y, h⟩
    · exact Or.inr ⟨y, h⟩
  · rintro (⟨y, h⟩ | ⟨y, h⟩)
    · exact ⟨y, Or.inl h⟩
    · exact ⟨y, Or.inr h⟩

/-- ✱33·161. \(\vdash.\text{D}ʻR\subset CʻR.\text{ᗡ}ʻR\subset CʻR \quad[\text{*33·16.*22·58}]\) -/
theorem pm33_161 {R : α → α → Prop} : dom R ⊆ fld R ∧ codom R ⊆ fld R := by
  rw [pm33_16]
  exact ⟨Set.subset_union_left, Set.subset_union_right⟩

/-- ✱33·17. \(\vdash:xRy.\supset.x,y\in CʻR \quad[\text{*33·14·161}]\) -/
theorem pm33_17 {R : α → α → Prop} {x y : α} : R x y → x ∈ fld R ∧ y ∈ fld R :=
  fun h => ⟨⟨y, Or.inl h⟩, ⟨x, Or.inr h⟩⟩

/-- ✱33·18. \(\vdash:\text{D}ʻR=\text{ᗡ}ʻR.\supset.\text{D}ʻR=CʻR\) -/
theorem pm33_18 {R : α → α → Prop} : dom R = codom R → dom R = fld R := by
  intro h
  rw [pm33_16, ← h, Set.union_self]

/-- ✱33·181. \(\vdash:\text{ᗡ}ʻR\subset \text{D}ʻR.\equiv.\text{D}ʻR=CʻR\) -/
theorem pm33_181 {R : α → α → Prop} : codom R ⊆ dom R ↔ dom R = fld R := by
  rw [pm33_16]
  constructor
  · intro h
    exact (Set.union_eq_left.2 h).symm
  · intro h
    rw [h]
    exact Set.subset_union_right

/-- ✱33·182. \(\vdash:\text{D}ʻR\subset\text{ᗡ}ʻR.\equiv.\text{ᗡ}ʻR=CʻR \quad[\text{Similar proof}]\) -/
theorem pm33_182 {R : α → α → Prop} : dom R ⊆ codom R ↔ codom R = fld R := by
  rw [pm33_16]
  constructor
  · intro h
    exact (Set.union_eq_right.2 h).symm
  · intro h
    rw [h]
    exact Set.subset_union_left

/-- ✱33·2. \(\vdash.\text{ᗡ}ʻR=\text{D}ʻ\breve{R}\) -/
theorem pm33_2 {R : α → β → Prop} : codom R = dom R˘ := rfl

/-- ✱33·21. \(\vdash.\text{D}ʻR=\text{ᗡ}ʻ\breve{R} \quad[\text{Similar proof}]\) -/
theorem pm33_21 {R : α → β → Prop} : dom R = codom R˘ := rfl

/-- ✱33·22. \(\vdash.CʻR=Cʻ\breve{R}\) -/
theorem pm33_22 {R : α → α → Prop} : fld R = fld R˘ :=
  Set.ext fun _ => exists_congr fun _ => or_comm

/-- ✱33·24. \(\vdash:\exists !\text{D}ʻR.\equiv.\exists !\text{ᗡ}ʻR.\equiv.\exists !CʻR.\equiv.\dot{\exists}!R\) -/
theorem pm33_24 {R : α → α → Prop} :
    (((dom R).Nonempty ↔ (codom R).Nonempty) ∧ ((codom R).Nonempty ↔ (fld R).Nonempty)) ∧
      ((fld R).Nonempty ↔ rEx R) := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨x, y, h⟩
    exact ⟨y, x, h⟩
  · rintro ⟨y, x, h⟩
    exact ⟨x, y, h⟩
  · rintro ⟨y, x, h⟩
    exact ⟨y, x, Or.inr h⟩
  · rintro ⟨x, y, h | h⟩
    · exact ⟨y, x, h⟩
    · exact ⟨x, y, h⟩
  · rintro ⟨x, y, h | h⟩
    · exact ⟨x, y, h⟩
    · exact ⟨y, x, h⟩
  · rintro ⟨x, y, h⟩
    exact ⟨x, y, Or.inl h⟩

/-- ✱33·241. \[\begin{align}&\vdash:\text{D}ʻR=\Lambda.\equiv.\text{ᗡ}ʻR=\Lambda.\equiv.CʻR=\Lambda.\equiv.R=\dot{\Lambda}\\ &[\text{*33·24.Transp.*24·51.*25·51}]\end{align}\] -/
theorem pm33_241 {R : α → α → Prop} :
    ((dom R = Λ ↔ codom R = Λ) ∧ (codom R = Λ ↔ fld R = Λ)) ∧ (fld R = Λ ↔ R = rNull) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := pm33_24 (R := R)
  simp only [eq_Null_iff, eq_rNull_iff, h1, h2, h3, and_self, iff_self]

/-- ✱33·25. \(\vdash.\text{D}ʻ(R\dot{\cap}S)\subset\text{D}ʻR\cap \text{D}ʻS\) -/
theorem pm33_25 {R S : α → β → Prop} : dom (R ⩀ S) ⊆ dom R ∩ dom S := by
  rintro x ⟨y, h1, h2⟩
  exact ⟨⟨y, h1⟩, ⟨y, h2⟩⟩

/-- ✱33·251. \(\vdash.\text{ᗡ}ʻ(R\dot{\cap}S)\subset\text{ᗡ}ʻR\cap \text{ᗡ}ʻS \quad[\text{Similar proof}]\) -/
theorem pm33_251 {R S : α → β → Prop} : codom (R ⩀ S) ⊆ codom R ∩ codom S := by
  rintro y ⟨x, h1, h2⟩
  exact ⟨⟨x, h1⟩, ⟨x, h2⟩⟩

/-- ✱33·252. \(\vdash.Cʻ(R\dot{\cap}S)\subset CʻR\cap CʻS \quad[\text{Similar proof}]\) -/
theorem pm33_252 {R S : α → α → Prop} : fld (R ⩀ S) ⊆ fld R ∩ fld S := by
  rintro x ⟨y, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact ⟨⟨y, Or.inl h1⟩, ⟨y, Or.inl h2⟩⟩
  · exact ⟨⟨y, Or.inr h1⟩, ⟨y, Or.inr h2⟩⟩

/-- ✱33·26. \(\vdash.\text{D}ʻ(R\unicode{x228d}S)=\text{D}ʻR\cup \text{D}ʻS\) -/
theorem pm33_26 {R S : α → β → Prop} : dom (R ⊍ S) = dom R ∪ dom S := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact Or.inl ⟨y, h⟩
    · exact Or.inr ⟨y, h⟩
  · rintro (⟨y, h⟩ | ⟨y, h⟩)
    · exact ⟨y, Or.inl h⟩
    · exact ⟨y, Or.inr h⟩

/-- ✱33·261. \(\vdash.\text{ᗡ}ʻ(R\unicode{x228d}S)=\text{ᗡ}ʻR\cup \text{ᗡ}ʻS \quad[\text{Similar proof}]\) -/
theorem pm33_261 {R S : α → β → Prop} : codom (R ⊍ S) = codom R ∪ codom S := by
  ext y
  constructor
  · rintro ⟨x, h | h⟩
    · exact Or.inl ⟨x, h⟩
    · exact Or.inr ⟨x, h⟩
  · rintro (⟨x, h⟩ | ⟨x, h⟩)
    · exact ⟨x, Or.inl h⟩
    · exact ⟨x, Or.inr h⟩

/-- ✱33·262. \(\vdash.Cʻ(R\unicode{x228d}S)=CʻR\cup CʻS \quad[\text{*33·26·261·16}]\) -/
theorem pm33_262 {R S : α → α → Prop} : fld (R ⊍ S) = fld R ∪ fld S := by
  ext x
  constructor
  · rintro ⟨y, (h | h) | (h | h)⟩
    · exact Or.inl ⟨y, Or.inl h⟩
    · exact Or.inr ⟨y, Or.inl h⟩
    · exact Or.inl ⟨y, Or.inr h⟩
    · exact Or.inr ⟨y, Or.inr h⟩
  · rintro (⟨y, h | h⟩ | ⟨y, h | h⟩)
    · exact ⟨y, Or.inl (Or.inl h)⟩
    · exact ⟨y, Or.inr (Or.inl h)⟩
    · exact ⟨y, Or.inl (Or.inr h)⟩
    · exact ⟨y, Or.inr (Or.inr h)⟩

/-- ✱33·263. \(\vdash:R\unicode{x2abd}S.\supset .\text{D}ʻR\subset\text{D}ʻS\) -/
theorem pm33_263 {R S : α → β → Prop} : R ⪽ S → dom R ⊆ dom S := by
  rintro h x ⟨y, hy⟩
  exact ⟨y, h x y hy⟩

/-- ✱33·264. \(\vdash:R\unicode{x2abd}S.\supset .\text{ᗡ}ʻR\subset\text{ᗡ}ʻS \quad[\text{Similar proof}]\) -/
theorem pm33_264 {R S : α → β → Prop} : R ⪽ S → codom R ⊆ codom S := by
  rintro h y ⟨x, hx⟩
  exact ⟨x, h x y hx⟩

/-- ✱33·265. \(\vdash:R\unicode{x2abd}S.\supset .CʻR\subset CʻS \quad[\text{*33·263·264·16.*22·72}]\) -/
theorem pm33_265 {R S : α → α → Prop} : R ⪽ S → fld R ⊆ fld S := by
  rintro h x ⟨y, hy | hy⟩
  · exact ⟨y, Or.inl (h x y hy)⟩
  · exact ⟨y, Or.inr (h y x hy)⟩

/-- ✱33·27. \(\vdash.CʻR=\text{D}ʻ(R\unicode{x228d}\breve{R})\) -/
theorem pm33_27 {R : α → α → Prop} : fld R = dom (R ⊍ R˘) := rfl

/-- ✱33·271. \(\vdash.CʻR=\text{ᗡ}ʻ(R\unicode{x228d}\breve{R}) \quad[\text{Similar proof}]\) -/
theorem pm33_271 {R : α → α → Prop} : fld R = codom (R ⊍ R˘) :=
  Set.ext fun _ => exists_congr fun _ => or_comm

/-- ✱33·272. \(\vdash.\text{D}ʻ(R\unicode{x228d}\breve{R})=\text{ᗡ}ʻ(R\unicode{x228d}\breve{R})=Cʻ(R\unicode{x228d}\breve{R})=CʻR \quad[\text{*33·27·271·16}]\) -/
theorem pm33_272 {R : α → α → Prop} :
    (dom (R ⊍ R˘) = codom (R ⊍ R˘) ∧ codom (R ⊍ R˘) = fld (R ⊍ R˘)) ∧
      fld (R ⊍ R˘) = fld R := by
  have h1 := (pm33_27 (R := R)).symm
  have h2 := (pm33_271 (R := R)).symm
  have h3 : fld (R ⊍ R˘) = fld R := by rw [pm33_16, h1, h2, Set.union_self]
  exact ⟨⟨h1.trans h2.symm, h2.trans h3.symm⟩, h3⟩

/-- ✱33·28. \(\vdash.\text{D}ʻ\text{V}=\text{ᗡ}ʻ\dot{\text{V}}=Cʻ\text{V}=\text{V}\)

**Status.** proved (reading): `V` is printed for `V̇` in `D'V` and `C'V` (only a relation is significant
there; the demonstration has `D'V̇`, `C'V̇`; cf. the erratum Vol. I, p. 218, on `Λ` for `Λ̇`).
The chain `D'V̇ = ᗡ'V̇ = C'V̇ = V` is the conjunction of its links; `C'` makes `V̇` homogeneous. -/
theorem pm33_28 :
    (dom (rV : α → α → Prop) = codom (rV : α → α → Prop) ∧
      codom (rV : α → α → Prop) = fld (rV : α → α → Prop)) ∧
      fld (rV : α → α → Prop) = V := by
  have h1 : dom (rV : α → α → Prop) = V :=
    Set.ext fun x => ⟨fun _ => rfl, fun _ => ⟨x, rfl, rfl⟩⟩
  have h2 : codom (rV : α → α → Prop) = V :=
    Set.ext fun x => ⟨fun _ => rfl, fun _ => ⟨x, rfl, rfl⟩⟩
  have h3 : fld (rV : α → α → Prop) = V :=
    Set.ext fun x => ⟨fun _ => rfl, fun _ => ⟨x, Or.inl ⟨rfl, rfl⟩⟩⟩
  exact ⟨⟨h1.trans h2.symm, h2.trans h3.symm⟩, h3⟩

/-- ✱33·29. \(\vdash.\text{D}ʻ\Lambda=\text{ᗡ}ʻ\Lambda=Cʻ\dot{\Lambda}=\Lambda \quad[\text{*33·241.*21·2}]\)

**Status.** proved (reading): erratum (Vol. I, p. 218): `Λ` is printed for `Λ̇` in `D'Λ` and `ᗡ'Λ`, where
only a relation is significant; the chain `D'Λ̇ = ᗡ'Λ̇ = C'Λ̇ = Λ` is the conjunction of its links. -/
theorem pm33_29 :
    (dom (rNull : α → α → Prop) = codom (rNull : α → α → Prop) ∧
      codom (rNull : α → α → Prop) = fld (rNull : α → α → Prop)) ∧
      fld (rNull : α → α → Prop) = Λ := by
  have h1 : dom (rNull : α → α → Prop) = Λ := by
    rw [eq_Null_iff]
    rintro ⟨x, y, h⟩
    exact rNull_apply x y h
  have h2 : codom (rNull : α → α → Prop) = Λ := by
    rw [eq_Null_iff]
    rintro ⟨y, x, h⟩
    exact rNull_apply x y h
  have h3 : fld (rNull : α → α → Prop) = Λ := by
    rw [eq_Null_iff]
    rintro ⟨x, y, h | h⟩
    · exact rNull_apply x y h
    · exact rNull_apply y x h
  exact ⟨⟨h1.trans h2.symm, h2.trans h3.symm⟩, h3⟩

/-- ✱33·3. \(\vdash\colon\ldotp \alpha\subset\text{D}ʻR.\equiv:x\in \alpha.\supset_{x}.\exists !\overleftarrow{R}ʻx\) -/
theorem pm33_3 {A : Set α} {R : α → β → Prop} :
    A ⊆ dom R ↔ ∀ x, x ∈ A → (rels R x).Nonempty := Iff.rfl

/-- ✱33·31. \(\vdash\colon\ldotp \beta\subset\text{ᗡ}ʻR.\equiv:y\in \beta.\supset_{y}.\exists !\overrightarrow{R}ʻy \quad[\text{Proof as in *33·3}]\) -/
theorem pm33_31 {B : Set β} {R : α → β → Prop} :
    B ⊆ codom R ↔ ∀ y, y ∈ B → (refs R y).Nonempty := Iff.rfl

/-- ✱33·32. \(\vdash:\text{D}ʻR\cap \text{D}ʻS=\Lambda.\supset.R\dot{\cap}S=\Lambda\)

**Status.** proved (reading): erratum (Vol. I, p. 218): `Λ` is printed for `Λ̇` in the consequent
`R ∩̇ S = Λ̇`, where only a relation is significant (✱33·33 has `Λ̇`). -/
theorem pm33_32 {R S : α → β → Prop} : dom R ∩ dom S = Λ → R ⩀ S = rNull := by
  intro h
  rw [eq_Null_iff] at h
  rw [eq_rNull_iff]
  rintro ⟨x, y, h1, h2⟩
  exact h ⟨x, mem_dom_of h1, mem_dom_of h2⟩

/-- ✱33·33. \(\vdash:\text{ᗡ}ʻR\cap \text{ᗡ}ʻS=\Lambda.\supset.R\dot{\cap}S=\dot{\Lambda} \quad[\text{Proof as in *33·32}]\) -/
theorem pm33_33 {R S : α → β → Prop} : codom R ∩ codom S = Λ → R ⩀ S = rNull := by
  intro h
  rw [eq_Null_iff] at h
  rw [eq_rNull_iff]
  rintro ⟨x, y, h1, h2⟩
  exact h ⟨y, mem_codom_of h1, mem_codom_of h2⟩

/-- ✱33·34. \(\vdash:CʻR\cap CʻS=\Lambda.\supset.R\dot{\cap}S=\dot{\Lambda}\) -/
theorem pm33_34 {R S : α → α → Prop} : fld R ∩ fld S = Λ → R ⩀ S = rNull := by
  intro h
  rw [eq_Null_iff] at h
  rw [eq_rNull_iff]
  rintro ⟨x, y, h1, h2⟩
  exact h ⟨x, ⟨y, Or.inl h1⟩, ⟨y, Or.inl h2⟩⟩

/-- ✱33·35. \(\vdash\colon\ldotp \text{D}ʻR\subset\alpha.\equiv:xRy.\supset_{x,y}.x\in \alpha\) -/
theorem pm33_35 {R : α → β → Prop} {A : Set α} : dom R ⊆ A ↔ ∀ x y, R x y → x ∈ A := by
  constructor
  · intro h x y hxy
    exact h (mem_dom_of hxy)
  · rintro h x ⟨y, hxy⟩
    exact h x y hxy

/-- ✱33·351. \(\vdash\colon\ldotp \text{ᗡ}ʻR\subset\alpha.\equiv:xRy.\supset_{x,y}.y\in \alpha \quad[\text{Proof as in *33·35}]\) -/
theorem pm33_351 {R : α → β → Prop} {A : Set β} : codom R ⊆ A ↔ ∀ x y, R x y → y ∈ A := by
  constructor
  · intro h x y hxy
    exact h (mem_codom_of hxy)
  · rintro h y ⟨x, hxy⟩
    exact h x y hxy

/-- ✱33·352. \(\vdash\colon\ldotp CʻR\subset\alpha.\equiv:xRy.\supset_{x,y}.x,y\in \alpha\) -/
theorem pm33_352 {R : α → α → Prop} {A : Set α} :
    fld R ⊆ A ↔ ∀ x y, R x y → x ∈ A ∧ y ∈ A := by
  constructor
  · intro h x y hxy
    exact ⟨h ⟨y, Or.inl hxy⟩, h ⟨x, Or.inr hxy⟩⟩
  · rintro h x ⟨y, hxy | hyx⟩
    · exact (h x y hxy).1
    · exact (h y x hyx).2

/-- ✱33·4. \(\vdash.\text{D}ʻR=\hat{x}\{\exists !\overleftarrow{R}ʻx\}\) -/
theorem pm33_4 {R : α → β → Prop} : dom R = {x | (rels R x).Nonempty} := rfl

/-- ✱33·41. \(\vdash.\text{ᗡ}ʻR=\hat{y}\{\exists !\overrightarrow{R}ʻy\} \quad[\text{Similar proof}]\) -/
theorem pm33_41 {R : α → β → Prop} : codom R = {y | (refs R y).Nonempty} := rfl

/-- ✱33·42. \(\vdash.CʻR=\hat{x}\{\exists !(\overrightarrow{R}ʻx\cup \overleftarrow{R}ʻx)\}\) -/
theorem pm33_42 {R : α → α → Prop} : fld R = {x | (refs R x ∪ rels R x).Nonempty} :=
  Set.ext fun _ => exists_congr fun _ => or_comm

/-- ✱33·43. \(\vdash:\text{E}!Rʻy.\supset.y\in \text{ᗡ}ʻR.Rʻy\in \text{D}ʻR\) -/
theorem pm33_43 {R : α → β → Prop} {y : β} :
    EDesc R y → y ∈ codom R ∧ Desc R y (fun b => b ∈ dom R) := by
  rintro ⟨b, hb⟩
  have h : R b y := (hb b).2 rfl
  exact ⟨mem_codom_of h, b, hb, mem_dom_of h⟩

/-- ✱33·431. \(\vdash:(y).\text{E}!Rʻy.\supset.(\beta).\beta\subset\text{ᗡ}ʻR\) -/
theorem pm33_431 {R : α → β → Prop} : (∀ y, EDesc R y) → ∀ B : Set β, B ⊆ codom R :=
  fun h _ y _ => (pm33_43 (h y)).1

/-- ✱33·432. \(\vdash:(y).\text{E}!Rʻy.\supset.\text{ᗡ}ʻR=\text{V}\) -/
theorem pm33_432 {R : α → β → Prop} : (∀ y, EDesc R y) → codom R = V :=
  fun h => Set.ext fun y => ⟨fun _ => rfl, fun _ => (pm33_43 (h y)).1⟩

/-- ✱33·44. \(\vdash:\text{E}!\breve{R}ʻx.\supset.x\in \text{D}ʻR.\breve{R}ʻx\in \text{ᗡ}ʻR\) -/
theorem pm33_44 {R : α → β → Prop} {x : α} :
    EDesc R˘ x → x ∈ dom R ∧ Desc R˘ x (fun b => b ∈ codom R) := by
  rintro ⟨b, hb⟩
  have h : R x b := (hb b).2 rfl
  exact ⟨mem_dom_of h, b, hb, mem_codom_of h⟩

/-- ✱33·45. \(\vdash\colon\ldotp y\in \text{ᗡ}ʻR\cup \text{ᗡ}ʻS.\supset_{y}.Rʻy=Sʻy:\supset.R=S\) -/
theorem pm33_45 {R S : α → β → Prop} :
    (∀ y, y ∈ codom R ∪ codom S → Desc R y (fun b => Desc S y (fun c => b = c))) → R = S := by
  intro h
  funext x y
  apply propext
  constructor
  · intro hxy
    obtain ⟨b, hb, c, hc, rfl⟩ := h y (Or.inl (mem_codom_of hxy))
    exact (hc x).2 ((hb x).1 hxy)
  · intro hxy
    obtain ⟨b, hb, c, hc, rfl⟩ := h y (Or.inr (mem_codom_of hxy))
    exact (hb x).2 ((hc x).1 hxy)

/-- ✱33·46. \(\vdash\colon\ldotp x\in \text{D}ʻR\cup \text{D}ʻS.\supset_{x}.\breve{R}ʻx=\breve{S}ʻx:\supset.R=S \quad[\text{Proof as in *33·45}]\) -/
theorem pm33_46 {R S : α → β → Prop} :
    (∀ x, x ∈ dom R ∪ dom S → Desc R˘ x (fun b => Desc S˘ x (fun c => b = c))) → R = S := by
  intro h
  funext x y
  apply propext
  constructor
  · intro hxy
    obtain ⟨b, hb, c, hc, rfl⟩ := h x (Or.inl (mem_dom_of hxy))
    exact (hc y).2 ((hb y).1 hxy)
  · intro hxy
    obtain ⟨b, hb, c, hc, rfl⟩ := h x (Or.inr (mem_dom_of hxy))
    exact (hb y).2 ((hc y).1 hxy)

/-- ✱33·47. \(\vdash\colon\ldotp y\in \text{ᗡ}ʻR\cup \text{ᗡ}ʻS.\supset_{y}.\overrightarrow{R}ʻy=\overrightarrow{S}ʻy:\supset.R=S\) -/
theorem pm33_47 {R S : α → β → Prop} :
    (∀ y, y ∈ codom R ∪ codom S → refs R y = refs S y) → R = S := by
  intro h
  funext x y
  apply propext
  constructor
  · intro hxy
    exact (Set.ext_iff.mp (h y (Or.inl (mem_codom_of hxy))) x).1 hxy
  · intro hxy
    exact (Set.ext_iff.mp (h y (Or.inr (mem_codom_of hxy))) x).2 hxy

/-- ✱33·48. \(\vdash\colon\ldotp x\in \text{D}ʻR\cup \text{D}ʻS.\supset_{x}.\overleftarrow{R}ʻx=\overleftarrow{S}ʻx:\supset.R=S \quad[\text{Proof as in *33·47}]\) -/
theorem pm33_48 {R S : α → β → Prop} :
    (∀ x, x ∈ dom R ∪ dom S → rels R x = rels S x) → R = S := by
  intro h
  funext x y
  apply propext
  constructor
  · intro hxy
    exact (Set.ext_iff.mp (h x (Or.inl (mem_dom_of hxy))) y).1 hxy
  · intro hxy
    exact (Set.ext_iff.mp (h x (Or.inr (mem_dom_of hxy))) y).2 hxy

/-- ✱33·5. \(\vdash.C=\overrightarrow{F}\) -/
theorem pm33_5 : (C : Set α → (α → α → Prop) → Prop) = Rfwd F := rfl

/-- ✱33·51. \(\vdash:x\in CʻR.\equiv.xFR \quad[\text{*33·132·103}]\) -/
theorem pm33_51 {x : α} {R : α → α → Prop} : x ∈ fld R ↔ F x R := Iff.rfl

/-- ✱33·6. \(\vdash:R\in \overleftarrow{\text{D}}ʻ\alpha.\equiv.\alpha=\text{D}ʻR\) -/
theorem pm33_6 {R : α → β → Prop} {A : Set α} : R ∈ rels D A ↔ A = dom R := Iff.rfl

/-- ✱33·61. \(\vdash:R\in \overleftarrow{ᗡ}ʻ\alpha.\equiv.\text{ᗡ}ʻR\)

**Status.** proved (reading): misprint (not in the errata): the e-text omits `α =` on the right, printing
`R ∈ ᗡ⃖'α . ≡ . ᗡ'R`, which is not significant; read `α = ᗡ'R`, as in ✱33·6. -/
theorem pm33_61 {R : α → β → Prop} {B : Set β} : R ∈ rels Dcnv B ↔ B = codom R := Iff.rfl

/-- ✱33·62. \(\vdash:R\in \overleftarrow{C}ʻ\alpha.\equiv.CʻR\)

**Status.** proved (reading): misprint (not in the errata): the e-text omits `α =` on the right, printing
`R ∈ C⃖'α . ≡ . C'R`, which is not significant; read `α = C'R`, as in ✱33·6. -/
theorem pm33_62 {R : α → α → Prop} {G : Set α} : R ∈ rels C G ↔ G = fld R := Iff.rfl

/-!
## [✱34] The relative product of two relations

*(Vol. 1, p. 269)*

> *Summary of* *34.
>
> The relative product of two relations \(R\) and \(S\) is the relation which holds between \(x\) and \(z\) when there is an intermediate term \(y\) such that \(x\) has the relation \(R\) to \(y\) and \(y\) has the relation \(S\) to \(z\). Thus *e.g.* the relative product of *brother* and *father* is *paternal uncle*; the relative product of *father* and *father* is *paternal grandfather*; and so on. The relative product of \(R\) and \(S\) is denoted by "\(R \mid S\)"; the definition is:
>
> *34·01. \(R \mid S = \hat{x}\hat{z}\{(\exists y).xRy.ySz\} \quad \text{Df}\)
>
> This definition is only significant when \(\text{ᗡ}ʻR\) and \(\text{D}ʻS\) belong to the same type.
>
> The relative product of \(R\) and \(R\) is called the square of \(R\); we put
>
> *34·02. \(R^{2} = R \mid R \quad \text{Df}\)
>
> *34·03. \(R^{3} = R^{2} \mid R \quad \text{Df}\)
>
> The most useful propositions in the present number are the following:
>
> *34·2. \(\vdash . \text{Cnv}ʻ(R \mid S) = \breve{S} \mid \breve{R}\)
>
> *I.e.* the converse of a relative product is obtained by turning each factor into its converse and reversing the order of the factors.
>
> *34·21. \(\vdash . (P \mid Q) \mid R = P \mid (Q \mid R)\)
>
> …

**Lean reading.** `R | S` is `R ⨾ S` (`relProd`, heterogeneous: `R : α → β → Prop`,
`S : β → γ → Prop`, so PM's condition that `ᗡ'R` and `D'S` be of the same type is typing), `R²`,
`R³` are `rsq R`, `rcube R`, and `P | Q | R` is `(P ⨾ Q) ⨾ R` by the left-associativity of `⨾`
(✱34·22). `Cnv'X` is written `X˘` (Basic §5). `b = P'c`, `P'Q'z`, `(P | Q)'z` in ✱34·4–✱34·42 are
descriptions (`Desc`, `Desc2`), and `E!P'Q'z` is as in ✱30·5. In ✱34·301, ✱34·32 `Λ` is printed
for `Λ̇` (erratum Vol. I, p. 218); in ✱34·12 `S⃗'x` for `S⃗'z`; in ✱34·34 `P Q` for `P | Q`; in
✱34·7, ✱34·701 `Cnv(…)` for `Cnv'(…)`. Products of hypotheses are left-bracketed conjunctions.

**Status.** proved (all propositions; ✱34·01–✱34·03, ✱34·22 definition; ✱34·12, ✱34·301, ✱34·32,
✱34·34, ✱34·7, ✱34·701 proved (reading): e-text misprints, see their docstrings).
-/

/-- ✱34·01 (Df). \( R\mid S=\hat{x}\hat{z}\{(\exists y).xRy.ySz\} \quad\text{Df}\) -/
theorem pm34_01 {R : α → β → Prop} {S : β → γ → Prop} :
    R ⨾ S = fun x z => ∃ y, R x y ∧ S y z := rfl

/-- ✱34·02 (Df). \(R^{2}=R\mid R \quad\text{Df}\) -/
theorem pm34_02 {R : α → α → Prop} : rsq R = R ⨾ R := rfl

/-- ✱34·03 (Df). \(R^{3}=R^{2}\mid R \quad\text{Df}\) -/
theorem pm34_03 {R : α → α → Prop} : rcube R = rsq R ⨾ R := rfl

/-- ✱34·1. \(\vdash:x(R\mid S)z.\equiv.(\exists y).xRy.ySz \quad[\text{*21·3.(*34·01)}]\) -/
theorem pm34_1 {R : α → β → Prop} {S : β → γ → Prop} {x : α} {z : γ} :
    (R ⨾ S) x z ↔ ∃ y, R x y ∧ S y z := Iff.rfl

/-- ✱34·11. \(\vdash:x(R\mid S)z.\equiv.\exists !(\overleftarrow{R}ʻx\cap \overrightarrow{S}ʻz)\) -/
theorem pm34_11 {R : α → β → Prop} {S : β → γ → Prop} {x : α} {z : γ} :
    (R ⨾ S) x z ↔ (rels R x ∩ refs S z).Nonempty := Iff.rfl

/-- ✱34·12. \(\vdash.R\mid S=\hat{x}\hat{z}\{\exists !(\overleftarrow{R}ʻx\cap \overrightarrow{S}ʻx)\} \quad[\text{*21·33.*34·11}]\)

**Status.** proved (reading): misprint (not in the errata): the e-text prints `S⃗'x` for `S⃗'z` in the
definiens (the bound variables are `x̂ẑ`, and the cited ✱34·11 has `S⃗'z`). -/
theorem pm34_12 {R : α → β → Prop} {S : β → γ → Prop} :
    R ⨾ S = fun x z => (rels R x ∩ refs S z).Nonempty := rfl

/-- ✱34·2. \(\vdash.\text{Cnv}ʻ(R\mid S)=\breve{S}\mid \breve{R}\) -/
theorem pm34_2 {R : α → β → Prop} {S : β → γ → Prop} : (R ⨾ S)˘ = S˘ ⨾ R˘ := by
  funext x z
  exact propext (exists_congr fun _ => and_comm)

/-- ✱34·202. \(\vdash.R\mid S=(\text{Cnv}ʻ\breve{R})\mid S\) -/
theorem pm34_202 {R : α → β → Prop} {S : β → γ → Prop} : R ⨾ S = (R˘)˘ ⨾ S := rfl

/-- ✱34·203. \(\vdash.R\mid S=R\mid (\text{Cnv}ʻ\breve{S}) \quad[\text{Similar proof}]\) -/
theorem pm34_203 {R : α → β → Prop} {S : β → γ → Prop} : R ⨾ S = R ⨾ (S˘)˘ := rfl

/-- ✱34·21. \(\vdash.(P\mid Q)\mid R=P\mid (Q\mid R)\) -/
theorem pm34_21 {P : α → β → Prop} {Q : β → γ → Prop} {R : γ → δ → Prop} :
    (P ⨾ Q) ⨾ R = P ⨾ (Q ⨾ R) := by
  funext x w
  apply propext
  constructor
  · rintro ⟨z, ⟨y, h1, h2⟩, h3⟩
    exact ⟨y, h1, z, h2, h3⟩
  · rintro ⟨y, h1, z, h2, h3⟩
    exact ⟨z, ⟨y, h1, h2⟩, h3⟩

/-- ✱34·22 (Df). \(P\mid Q\mid R=(P\mid Q)\mid R \quad\text{Df}\) -/
theorem pm34_22 {P : α → β → Prop} {Q : β → γ → Prop} {R : γ → δ → Prop} :
    P ⨾ Q ⨾ R = (P ⨾ Q) ⨾ R := rfl

/-- ✱34·23. \(\vdash.P\mid (Q\dot{\cap}R)\unicode{x2abd}(P\mid Q)\dot{\cap}(P\mid R)\) -/
theorem pm34_23 {P : α → β → Prop} {Q R : β → γ → Prop} :
    P ⨾ (Q ⩀ R) ⪽ (P ⨾ Q) ⩀ (P ⨾ R) := by
  rintro x z ⟨y, h1, h2, h3⟩
  exact ⟨⟨y, h1, h2⟩, ⟨y, h1, h3⟩⟩

/-- ✱34·24. \(\vdash.(P\dot{\cap}Q)\mid R\unicode{x2abd}(P\mid R)\dot{\cap}(Q\mid R) \quad[\text{Similar proof}]\) -/
theorem pm34_24 {P Q : α → β → Prop} {R : β → γ → Prop} :
    (P ⩀ Q) ⨾ R ⪽ (P ⨾ R) ⩀ (Q ⨾ R) := by
  rintro x z ⟨y, ⟨h1, h2⟩, h3⟩
  exact ⟨⟨y, h1, h3⟩, ⟨y, h2, h3⟩⟩

/-- ✱34·25. \(\vdash.P\mid (Q\unicode{x228d}R)=(P\mid Q)\unicode{x228d}(P\mid R)\) -/
theorem pm34_25 {P : α → β → Prop} {Q R : β → γ → Prop} :
    P ⨾ (Q ⊍ R) = (P ⨾ Q) ⊍ (P ⨾ R) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, h1, h2 | h2⟩
    · exact Or.inl ⟨y, h1, h2⟩
    · exact Or.inr ⟨y, h1, h2⟩
  · rintro (⟨y, h1, h2⟩ | ⟨y, h1, h2⟩)
    · exact ⟨y, h1, Or.inl h2⟩
    · exact ⟨y, h1, Or.inr h2⟩

/-- ✱34·26. \(\vdash.(P\unicode{x228d}Q)\mid R=(P\mid R)\unicode{x228d}(Q\mid R) \quad[\text{Similar proof}]\) -/
theorem pm34_26 {P Q : α → β → Prop} {R : β → γ → Prop} :
    (P ⊍ Q) ⨾ R = (P ⨾ R) ⊍ (Q ⨾ R) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, h1 | h1, h2⟩
    · exact Or.inl ⟨y, h1, h2⟩
    · exact Or.inr ⟨y, h1, h2⟩
  · rintro (⟨y, h1, h2⟩ | ⟨y, h1, h2⟩)
    · exact ⟨y, Or.inl h1, h2⟩
    · exact ⟨y, Or.inr h1, h2⟩

/-- ✱34·27. \(\vdash:R=R'.\supset.R\mid P=R'\mid P\) -/
theorem pm34_27 {R R' : α → β → Prop} {P : β → γ → Prop} : R = R' → R ⨾ P = R' ⨾ P := by
  rintro rfl
  rfl

/-- ✱34·28. \(\vdash:R=R'.\supset.P\mid R=P\mid R' \quad[\text{Similar proof}]\) -/
theorem pm34_28 {P : α → β → Prop} {R R' : β → γ → Prop} : R = R' → P ⨾ R = P ⨾ R' := by
  rintro rfl
  rfl

/-- ✱34·29. \(\vdash:R=R'.\supset.P\mid R\mid Q=P\mid R'\mid Q\) -/
theorem pm34_29 {P : α → β → Prop} {R R' : β → γ → Prop} {Q : γ → δ → Prop} :
    R = R' → P ⨾ R ⨾ Q = P ⨾ R' ⨾ Q := by
  rintro rfl
  rfl

/-- ✱34·3. \(\vdash:\dot{\exists}!(P\mid Q).\equiv.\exists !(\text{ᗡ}ʻP\cap \text{D}ʻQ)\) -/
theorem pm34_3 {P : α → β → Prop} {Q : β → γ → Prop} :
    rEx (P ⨾ Q) ↔ (codom P ∩ dom Q).Nonempty := by
  constructor
  · rintro ⟨x, z, y, h1, h2⟩
    exact ⟨y, mem_codom_of h1, mem_dom_of h2⟩
  · rintro ⟨y, ⟨x, h1⟩, ⟨z, h2⟩⟩
    exact ⟨x, z, y, h1, h2⟩

/-- ✱34·301. \(\vdash:\text{ᗡ}ʻP\cap \text{D}ʻQ=\Lambda.\equiv.P\mid Q=\Lambda \quad[\text{*34·3.Transp}]\)

**Status.** proved (reading): erratum (Vol. I, p. 218): `Λ` is printed for `Λ̇` in `P | Q = Λ̇`, where
only a relation is significant. -/
theorem pm34_301 {P : α → β → Prop} {Q : β → γ → Prop} :
    codom P ∩ dom Q = Λ ↔ P ⨾ Q = rNull := by
  rw [eq_Null_iff, eq_rNull_iff, pm34_3]

/-- ✱34·302. \(\vdash:CʻP\cap CʻQ=\Lambda.\supset.P\mid Q=\dot{\Lambda}.Q\mid P=\dot{\Lambda}\) -/
theorem pm34_302 {P Q : α → α → Prop} :
    fld P ∩ fld Q = Λ → P ⨾ Q = rNull ∧ Q ⨾ P = rNull := by
  intro h
  rw [eq_Null_iff] at h
  refine ⟨eq_rNull_iff.2 ?_, eq_rNull_iff.2 ?_⟩
  · rintro ⟨x, z, y, h1, h2⟩
    exact h ⟨y, ⟨x, Or.inr h1⟩, ⟨z, Or.inl h2⟩⟩
  · rintro ⟨x, z, y, h1, h2⟩
    exact h ⟨y, ⟨z, Or.inl h2⟩, ⟨x, Or.inr h1⟩⟩

/-- ✱34·31. \(\vdash:\dot{\exists}!(P\mid Q).\supset.\dot{\exists}!P.\dot{\exists}!Q\) -/
theorem pm34_31 {P : α → β → Prop} {Q : β → γ → Prop} : rEx (P ⨾ Q) → rEx P ∧ rEx Q := by
  rintro ⟨x, z, y, h1, h2⟩
  exact ⟨⟨x, y, h1⟩, ⟨y, z, h2⟩⟩

/-- ✱34·32. \(\vdash\colon\ldotp P=\Lambda.\lor .Q=\dot{\Lambda}:\supset.P\mid Q=\Lambda \quad[\text{*34·31.Transp.*25·51}]\)

**Status.** proved (reading): erratum (Vol. I, p. 218): `Λ` is printed for `Λ̇` in `P = Λ̇` and in
`P | Q = Λ̇`, where only relations are significant (the e-text has `Q = Λ̇`). -/
theorem pm34_32 {P : α → β → Prop} {Q : β → γ → Prop} :
    P = rNull ∨ Q = rNull → P ⨾ Q = rNull := by
  intro h
  rw [eq_rNull_iff]
  intro hx
  obtain ⟨hP, hQ⟩ := pm34_31 hx
  rcases h with h | h
  · exact eq_rNull_iff.1 h hP
  · exact eq_rNull_iff.1 h hQ

/-- ✱34·33. \(\vdash : x \in \text{D}ʻR . \equiv .x(R\mid \breve{R})x\) -/
theorem pm34_33 {R : α → β → Prop} {x : α} : x ∈ dom R ↔ (R ⨾ R˘) x x := by
  constructor
  · rintro ⟨y, h⟩
    exact ⟨y, h, h⟩
  · rintro ⟨y, h, -⟩
    exact ⟨y, h⟩

/-- ✱34·34. \(\vdash : R \unicode{x2abd} P . S \unicode{x2abd} Q . \supset . R\mid S \unicode{x2abd} P Q\)

**Status.** proved (reading): transcription error: the e-text prints `P Q` for `P | Q` in the consequent
(and drops the `|` in the demonstration, `x(R S)z`). -/
theorem pm34_34 {R P : α → β → Prop} {S Q : β → γ → Prop} :
    R ⪽ P ∧ S ⪽ Q → R ⨾ S ⪽ P ⨾ Q := by
  rintro ⟨h1, h2⟩ x z ⟨y, hr, hs⟩
  exact ⟨y, h1 x y hr, h2 y z hs⟩

/-- ✱34·35. \(\vdash : \dot{\exists} ! R . \text{ᗡ}ʻR \subset \text{D}ʻP . \supset . \dot{\exists} ! R\mid P\) -/
theorem pm34_35 {R : α → β → Prop} {P : β → γ → Prop} :
    rEx R ∧ codom R ⊆ dom P → rEx (R ⨾ P) := by
  rintro ⟨⟨x, y, h⟩, hsub⟩
  obtain ⟨z, hz⟩ := hsub (mem_codom_of h)
  exact ⟨x, z, y, h, hz⟩

/-- ✱34·351. \(\vdash : \dot{\exists} ! R . \text{D}ʻR \subset \text{ᗡ}ʻP . \supset . \dot{\exists} ! P\mid R \quad[\text{Proof as in *34·35}]\) -/
theorem pm34_351 {R : α → β → Prop} {P : γ → α → Prop} :
    rEx R ∧ dom R ⊆ codom P → rEx (P ⨾ R) := by
  rintro ⟨⟨x, y, h⟩, hsub⟩
  obtain ⟨w, hw⟩ := hsub (mem_dom_of h)
  exact ⟨w, y, x, hw, h⟩

/-- ✱34·36. \(\vdash . \text{D}ʻ(P\mid Q) \subset \text{D}ʻP . \text{ᗡ}ʻ(P\mid Q) \subset \text{ᗡ}ʻQ\) -/
theorem pm34_36 {P : α → β → Prop} {Q : β → γ → Prop} :
    dom (P ⨾ Q) ⊆ dom P ∧ codom (P ⨾ Q) ⊆ codom Q := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨z, y, h1, -⟩
    exact mem_dom_of h1
  · rintro z ⟨x, y, -, h2⟩
    exact mem_codom_of h2

/-- ✱34·361. \(\vdash : \dot{\exists} ! R . \text{D}ʻR \subset \text{ᗡ}ʻP . \text{ᗡ}ʻR \subset \text{D}ʻQ . \supset . \dot{\exists} ! P\mid R\mid Q\) -/
theorem pm34_361 {P : α → β → Prop} {R : β → γ → Prop} {Q : γ → δ → Prop} :
    (rEx R ∧ dom R ⊆ codom P) ∧ codom R ⊆ dom Q → rEx (P ⨾ R ⨾ Q) := by
  rintro ⟨⟨⟨x, y, h⟩, h1⟩, h2⟩
  obtain ⟨w, hw⟩ := h1 (mem_dom_of h)
  obtain ⟨z, hz⟩ := h2 (mem_codom_of h)
  exact ⟨w, z, y, ⟨x, hw, h⟩, hz⟩

/-- ✱34·37. \(\vdash.Cʻ(P\mid Q)\subset \text{D}ʻP\cup \text{ᗡ}ʻQ \quad[\text{*34·36.*33·161.*22·72}]\)

Only `P | Q` need be homogeneous (for `C'(P | Q)`): `P : α → β → Prop`, `Q : β → α → Prop`. -/
theorem pm34_37 {P : α → β → Prop} {Q : β → α → Prop} : fld (P ⨾ Q) ⊆ dom P ∪ codom Q := by
  rintro x ⟨z, ⟨y, h1, -⟩ | ⟨y, -, h2⟩⟩
  · exact Or.inl (mem_dom_of h1)
  · exact Or.inr (mem_codom_of h2)

/-- ✱34·38. \(\vdash.Cʻ(P\mid Q)\subset CʻP\cup CʻQ \quad[\text{*34·37.*33·161.*22·72}]\) -/
theorem pm34_38 {P Q : α → α → Prop} : fld (P ⨾ Q) ⊆ fld P ∪ fld Q := by
  rintro x ⟨z, ⟨y, h1, -⟩ | ⟨y, -, h2⟩⟩
  · exact Or.inl ⟨y, Or.inl h1⟩
  · exact Or.inr ⟨y, Or.inr h2⟩

/-- ✱34·4. \(\vdash:b=Pʻc.c=Qʻz.\supset.b=(P\mid Q)ʻz\) -/
theorem pm34_4 {P : α → β → Prop} {Q : β → γ → Prop} {b : α} {c : β} {z : γ} :
    Desc P c (fun d => b = d) ∧ Desc Q z (fun d => c = d) → Desc (P ⨾ Q) z (fun d => b = d) := by
  rintro ⟨⟨b', hb, hbb⟩, ⟨c', hc, hcc⟩⟩
  subst hbb hcc
  refine ⟨b, fun x => ⟨?_, ?_⟩, rfl⟩
  · rintro ⟨y, hxy, hyz⟩
    rw [(hc y).1 hyz] at hxy
    exact (hb x).1 hxy
  · rintro rfl
    exact ⟨_, (hb _).2 rfl, (hc _).2 rfl⟩

/-- ✱34·41. \(\vdash:\text{E}!PʻQʻz.\supset.PʻQʻz=(P\mid Q)ʻz\) -/
theorem pm34_41 {P : α → β → Prop} {Q : β → γ → Prop} {z : γ} :
    EBang (fun x => Desc Q z (fun w => P x w)) →
      Desc2 P Q z (fun b => Desc (P ⨾ Q) z (fun c => b = c)) := by
  intro h
  obtain ⟨b, c, h1, h2⟩ := pm30_52.1 h
  rw [desc2_iff]
  obtain ⟨c', hc, hcc⟩ := h2
  subst hcc
  obtain ⟨b', hb, hbb⟩ := h1
  subst hbb
  exact ⟨_, hc, _, hb, pm34_4 ⟨⟨_, hb, rfl⟩, ⟨_, hc, rfl⟩⟩⟩

/-- ✱34·42. \(\vdash:(z).Rʻz=PʻQʻz.\supset.R=P\mid Q\) -/
theorem pm34_42 {R : α → γ → Prop} {P : α → β → Prop} {Q : β → γ → Prop} :
    (∀ z, Desc R z (fun b => Desc2 P Q z (fun c => b = c))) → R = P ⨾ Q := by
  intro h
  funext x z
  obtain ⟨b, hb, hd⟩ := h z
  rw [desc2_iff] at hd
  obtain ⟨c, hc, b', hb', hbb⟩ := hd
  subst hbb
  apply propext
  rw [show R x z ↔ x = b from hb x]
  constructor
  · rintro rfl
    exact ⟨c, (hb' _).2 rfl, (hc c).2 rfl⟩
  · rintro ⟨y, hxy, hyz⟩
    rw [(hc y).1 hyz] at hxy
    exact (hb' x).1 hxy

/-- ✱34·5. \(\vdash:xR{^{2}}y.\equiv.(\exists z).xRz.zRy \quad[\text{*34·1.(*34·02)}]\) -/
theorem pm34_5 {R : α → α → Prop} {x y : α} : rsq R x y ↔ ∃ z, R x z ∧ R z y := Iff.rfl

/-- ✱34·51. \(\vdash:xR{^{3}}y.\equiv.(\exists z,w).xRz.zRw.wRy\) -/
theorem pm34_51 {R : α → α → Prop} {x y : α} :
    rcube R x y ↔ ∃ z w, (R x z ∧ R z w) ∧ R w y := by
  constructor
  · rintro ⟨w, ⟨z, h1, h2⟩, h3⟩
    exact ⟨z, w, ⟨h1, h2⟩, h3⟩
  · rintro ⟨z, w, ⟨h1, h2⟩, h3⟩
    exact ⟨w, ⟨z, h1, h2⟩, h3⟩

/-- ✱34·52. \(\vdash.R^{3}=R\mid R^{2} \quad[\text{*34·21}]\) -/
theorem pm34_52 {R : α → α → Prop} : rcube R = R ⨾ rsq R := pm34_21

/-- ✱34·53. \(\vdash:\dot{\exists}!R^{2}.\equiv.\exists !\text{D}ʻR\cap \text{ᗡ}ʻR \quad[\text{*34·3}]\) -/
theorem pm34_53 {R : α → α → Prop} : rEx (rsq R) ↔ (dom R ∩ codom R).Nonempty := by
  rw [rsq, pm34_3, Set.inter_comm]

/-- ✱34·531. \(\vdash:\text{D}ʻR\cap \text{ᗡ}ʻR=\Lambda.\equiv.R^{2}=\dot{\Lambda} \quad[\text{*34·53.Transp}]\) -/
theorem pm34_531 {R : α → α → Prop} : dom R ∩ codom R = Λ ↔ rsq R = rNull := by
  rw [eq_Null_iff, eq_rNull_iff, pm34_53]

/-- ✱34·54. \(\vdash:xRx.\supset.xR{^{2}}x\) -/
theorem pm34_54 {R : α → α → Prop} {x : α} : R x x → rsq R x x := fun h => ⟨x, h, h⟩

/-- ✱34·55. \(\vdash\colon\ldotp R{^{2}}\unicode{x2abd}S.\equiv:xRy.yRz.\supset_{x,y,z}.xSz \quad[\text{*34·5.*10·23}]\) -/
theorem pm34_55 {R S : α → α → Prop} : rsq R ⪽ S ↔ ∀ x y z, R x y ∧ R y z → S x z := by
  constructor
  · rintro h x y z ⟨h1, h2⟩
    exact h x z ⟨y, h1, h2⟩
  · rintro h x z ⟨y, h1, h2⟩
    exact h x y z ⟨h1, h2⟩

/-- ✱34·56. \(\vdash.\text{D}ʻR^{2}\subset\text{D}ʻR.\text{ᗡ}ʻR{^{2}}\subset\text{ᗡ}ʻR.CʻR{^{2}}\subset CʻR \quad[\text{*34·36·38}]\) -/
theorem pm34_56 {R : α → α → Prop} :
    (dom (rsq R) ⊆ dom R ∧ codom (rsq R) ⊆ codom R) ∧ fld (rsq R) ⊆ fld R := by
  refine ⟨pm34_36, fun x hx => ?_⟩
  have := pm34_38 hx
  rwa [Set.union_self] at this

/-- ✱34·6. \(\vdash.(R\dot{\cap}S){^{2}}\unicode{x2abd}R^{2}\dot{\cap}S^{2}\) -/
theorem pm34_6 {R S : α → α → Prop} : rsq (R ⩀ S) ⪽ rsq R ⩀ rsq S := by
  rintro x z ⟨y, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
  exact ⟨⟨y, h1, h3⟩, ⟨y, h2, h4⟩⟩

/-- ✱34·62. \(\vdash.(R\unicode{x228d}S)^{2}=R{^{2}}\unicode{x228d}R\mid S\unicode{x228d}S\mid R\unicode{x228d}S^{2}\) -/
theorem pm34_62 {R S : α → α → Prop} :
    rsq (R ⊍ S) = rsq R ⊍ R ⨾ S ⊍ S ⨾ R ⊍ rsq S := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, h1 | h1, h2 | h2⟩
    · exact Or.inl (Or.inl (Or.inl ⟨y, h1, h2⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨y, h1, h2⟩))
    · exact Or.inl (Or.inr ⟨y, h1, h2⟩)
    · exact Or.inr ⟨y, h1, h2⟩
  · rintro (((⟨y, h1, h2⟩ | ⟨y, h1, h2⟩) | ⟨y, h1, h2⟩) | ⟨y, h1, h2⟩)
    · exact ⟨y, Or.inl h1, Or.inl h2⟩
    · exact ⟨y, Or.inl h1, Or.inr h2⟩
    · exact ⟨y, Or.inr h1, Or.inl h2⟩
    · exact ⟨y, Or.inr h1, Or.inr h2⟩

/-- ✱34·63. \(\vdash.\text{Cnv}ʻ(R^{2})=(\text{Cnv}ʻR)^{2}\) -/
theorem pm34_63 {R : α → α → Prop} : (rsq R)˘ = rsq R˘ := pm34_2

/-- ✱34·7. \(\vdash.\text{Cnv}(S\mid \breve{S})=S\mid \breve{S}\)

**Status.** proved (reading): the e-text prints `Cnv(S | S̆)` (here and in the demonstration) for the
converse `Cnv'(S | S̆)`. -/
theorem pm34_7 {S : α → β → Prop} : (S ⨾ S˘)˘ = S ⨾ S˘ := pm34_2

/-- ✱34·701. \(\vdash.\text{Cnv}(\breve{S}\mid S)=\breve{S}\mid S \quad[\text{*34·2·203}]\)

**Status.** proved (reading): the e-text prints `Cnv(S̆ | S)` for `Cnv'(S̆ | S)`, as in ✱34·7. -/
theorem pm34_701 {S : α → β → Prop} : (S˘ ⨾ S)˘ = S˘ ⨾ S := pm34_2

/-- ✱34·702. \(\vdash.Cʻ(S\mid \breve{S})=\text{D}ʻS\) -/
theorem pm34_702 {S : α → β → Prop} : fld (S ⨾ S˘) = dom S := by
  ext x
  constructor
  · rintro ⟨y, ⟨w, h, -⟩ | ⟨w, -, h⟩⟩
    · exact ⟨w, h⟩
    · exact ⟨w, h⟩
  · rintro ⟨w, h⟩
    exact ⟨x, Or.inl ⟨w, h, h⟩⟩

/-- ✱34·703. \(\vdash.Cʻ(\breve{S}\mid S)=\text{ᗡ}ʻS \quad[\text{Similar proof}]\) -/
theorem pm34_703 {S : α → β → Prop} : fld (S˘ ⨾ S) = codom S := by
  ext x
  constructor
  · rintro ⟨y, ⟨w, h, -⟩ | ⟨w, -, h⟩⟩
    · exact ⟨w, h⟩
    · exact ⟨w, h⟩
  · rintro ⟨w, h⟩
    exact ⟨x, Or.inl ⟨w, h, h⟩⟩

/-- ✱34·73. \(\vdash:CʻP\cap CʻQ=\Lambda.\supset.(P\unicode{x228d}Q)^{2}=P^{2}\unicode{x228d}Q^{2}\) -/
theorem pm34_73 {P Q : α → α → Prop} :
    fld P ∩ fld Q = Λ → rsq (P ⊍ Q) = rsq P ⊍ rsq Q := by
  intro h
  obtain ⟨h1, h2⟩ := pm34_302 h
  rw [pm34_62, h1, h2]
  funext x z
  apply propext
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inl h
    · exact (rNull_apply x z h).elim
    · exact (rNull_apply x z h).elim
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inr h

/-- ✱34·8. \(\vdash:R=\breve{R}.R^{2}\unicode{x2abd}R.\supset.R=R^{2}=R\mid \breve{R}\) -/
theorem pm34_8 {R : α → α → Prop} : R = R˘ ∧ rsq R ⪽ R → R = rsq R ∧ rsq R = R ⨾ R˘ := by
  rintro ⟨hs, ht⟩
  have sym : ∀ x y, R x y → R y x := fun x y h => (congrFun (congrFun hs x) y).mp h
  refine ⟨?_, ?_⟩
  · funext x y
    apply propext
    constructor
    · intro h
      exact ⟨y, h, ht y y ⟨x, sym x y h, h⟩⟩
    · intro h
      exact ht x y h
  · funext x y
    apply propext
    constructor
    · rintro ⟨z, h1, h2⟩
      exact ⟨z, h1, sym z y h2⟩
    · rintro ⟨z, h1, h2⟩
      exact ⟨z, h1, sym y z h2⟩

/-- ✱34·81. \(\vdash:R=\breve{R}.R^{2}\unicode{x2abd}R.\equiv.R=\breve{R}.R^{2}=R \quad[\text{*34·8.*4·71}]\) -/
theorem pm34_81 {R : α → α → Prop} : R = R˘ ∧ rsq R ⪽ R ↔ R = R˘ ∧ rsq R = R := by
  constructor
  · intro h
    exact ⟨h.1, (pm34_8 h).1.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x y h => (congrFun (congrFun h2 x) y).mp h⟩

/-- ✱34·82. \(\vdash\colon\ldotp R=\breve{R}.R^{2}\unicode{x2abd}R.\supset:x\in \text{D}ʻR.\equiv.xRx\) -/
theorem pm34_82 {R : α → α → Prop} {x : α} :
    R = R˘ ∧ rsq R ⪽ R → (x ∈ dom R ↔ R x x) := by
  rintro ⟨hs, ht⟩
  constructor
  · rintro ⟨y, h⟩
    exact ht x x ⟨y, h, (congrFun (congrFun hs x) y).mp h⟩
  · intro h
    exact ⟨x, h⟩

/-- ✱34·83. \(\vdash:R=\breve{R}.R^{2}\unicode{x2abd}R.xRy.\supset.\overleftarrow{R}ʻx=\overleftarrow{R}ʻy\) -/
theorem pm34_83 {R : α → α → Prop} {x y : α} :
    (R = R˘ ∧ rsq R ⪽ R) ∧ R x y → rels R x = rels R y := by
  rintro ⟨⟨hs, ht⟩, h⟩
  have sym : ∀ a b, R a b → R b a := fun a b hab => (congrFun (congrFun hs a) b).mp hab
  ext z
  constructor
  · intro hz
    exact ht y z ⟨x, sym x y h, hz⟩
  · intro hz
    exact ht x z ⟨y, h, hz⟩

/-- ✱34·84. \(\vdash:R=\breve{R}.R^{2}\unicode{x2abd}R.y\in \text{D}ʻR.\overleftarrow{R}ʻx=\overleftarrow{R}ʻy.\supset.xRy\) -/
theorem pm34_84 {R : α → α → Prop} {x y : α} :
    ((R = R˘ ∧ rsq R ⪽ R) ∧ y ∈ dom R) ∧ rels R x = rels R y → R x y := by
  rintro ⟨⟨⟨hs, ht⟩, hy⟩, he⟩
  have hyy : R y y := (pm34_82 (x := y) ⟨hs, ht⟩).1 hy
  have : y ∈ rels R x := by
    rw [he]
    exact hyy
  exact this

/-- ✱34·841. \(\vdash:R=\breve{R}.R^{2}\unicode{x2abd}R.x\in \text{D}ʻR.\overleftarrow{R}ʻx=\overleftarrow{R}ʻy.\supset.xRy\) -/
theorem pm34_841 {R : α → α → Prop} {x y : α} :
    ((R = R˘ ∧ rsq R ⪽ R) ∧ x ∈ dom R) ∧ rels R x = rels R y → R x y := by
  rintro ⟨⟨⟨hs, ht⟩, hx⟩, he⟩
  have hxx : R x x := (pm34_82 (x := x) ⟨hs, ht⟩).1 hx
  have : x ∈ rels R y := by
    rw [← he]
    exact hxx
  exact (congrFun (congrFun hs y) x).mp this

/-- ✱34·85. \[\begin{align}&\vdash\colon\ldotp R=\breve{R}.R^{2}\unicode{x2abd}R.\supset:xRy.\equiv.x\in \text{D}ʻR.\overleftarrow{R}ʻx=\overleftarrow{R}ʻy\\ &\quad[\text{*34·83·841.*33·14}]\end{align}\] -/
theorem pm34_85 {R : α → α → Prop} {x y : α} :
    R = R˘ ∧ rsq R ⪽ R → (R x y ↔ x ∈ dom R ∧ rels R x = rels R y) := by
  intro h
  constructor
  · intro hxy
    exact ⟨mem_dom_of hxy, pm34_83 ⟨h, hxy⟩⟩
  · rintro ⟨hx, he⟩
    exact pm34_841 ⟨⟨h, hx⟩, he⟩

/-!
## [✱35] Relations with limited domains and converse domains

*(Vol. 1, p. 278)*

> *Summary of* *35.
>
> In this section, we have to consider the relation derived from a given relation \(R\) by limiting either its domain or its converse domain to members of some assigned class. A relation \(R\) with its domain limited to members of \(\alpha\) is written "\(\alpha \upharpoonleft R\)"; with its converse domain limited to members of \(\beta\), it is written "\(R \upharpoonright \beta\)"; with both limitations, it is written "\(\alpha \upharpoonleft R \upharpoonright \beta\)." Thus *e.g.* "brother" and "sister" express the same relation (that of a common parentage), with the domain limited in the first case to males, in the second to females. "The relation of white employers to coloured employees" is a relation limited both as to its domain and as to its converse domain. We put
>
> *35·01. \(\alpha \upharpoonright R =\hat{x}\hat{y}(x \in \alpha . xRy) \quad \text{Df}\)
>
> with similar definitions for \(R \upharpoonright \alpha\) and \(\alpha \upharpoonleft R \upharpoonright \beta\).
>
> …

**Lean reading.** `α ↿ R`, `R ↾ β`, `α ↿ R ↾ β`, `α ↑ β` are `A ◁ R`, `R ↾ B`, `bres A R B`
(= `A ◁ R ↾ B`) and `cross A B`; the precedences `◁` > `⨾` > `↾` > `⩀` > `⊍` realize the bracketing
Dfs ✱35·24·25·27 and PM's unbracketed formulas (✱35·16–✱35·18, ✱35·354, ✱35·41, ✱35·412). Chains of
identities (✱35·16–✱35·18, ✱35·21, ✱35·26, ✱35·75, ✱35·76, ✱35·9) are conjunctions of their links;
✱35·89 is the conjunction of its two implications; `∃!α` is `A.Nonempty`. `(R ↾ β)'y` and `R'y` in
✱35·7, ✱35·71 are descriptions. In ✱35·93–✱35·94·941 (with `D'R`, `ᗡ'R` of a heterogeneous `R`)
PM's tacit assumption that every type has a member is made explicit; ✱35·932·942 (with `C'R`) need
no hypothesis.

**Status.** proved (all propositions; ✱35·01–✱35·05, ✱35·24, ✱35·25, ✱35·27 definition; ✱35·26
proved (reading): unbalanced bracket; ✱35·93, ✱35·931, ✱35·94, ✱35·941 proved (reading):
`[Nonempty _]`).
-/

/-- ✱35·01 (Df). \(\alpha\upharpoonleft R=\hat{x}\hat{y}(x\in \alpha.xRy) \quad\text{Df}\) -/
theorem pm35_01 {A : Set α} {R : α → β → Prop} : A ◁ R = fun x y => x ∈ A ∧ R x y := rfl

/-- ✱35·02 (Df). \(R\upharpoonright \beta=\hat{x}\hat{y}(xRy.y\in \beta) \quad\text{Df}\) -/
theorem pm35_02 {R : α → β → Prop} {B : Set β} : R ↾ B = fun x y => R x y ∧ y ∈ B := rfl

/-- ✱35·03 (Df). \(\alpha\upharpoonleft R\upharpoonright \beta=\hat{x}\hat{y}(x\in \alpha.xRy.y\in \beta)\quad\text{Df}\) -/
theorem pm35_03 {A : Set α} {R : α → β → Prop} {B : Set β} :
    bres A R B = fun x y => (x ∈ A ∧ R x y) ∧ y ∈ B := rfl

/-- ✱35·04 (Df). \(\alpha\uparrow \beta=\hat{x}\hat{y}(x\in \alpha.y\in \beta) \quad\text{Df}\) -/
theorem pm35_04 {A : Set α} {B : Set β} : cross A B = fun x y => x ∈ A ∧ y ∈ B := rfl

/-- ✱35·05 (Df). \(Rʻx\uparrow \beta=(Rʻx)\uparrow \beta \quad\text{Df}\) -/
theorem pm35_05 {R : Set α → γ → Prop} {x : γ} {B : Set β} {ψ : (α → β → Prop) → Prop} :
    Desc R x (fun A => ψ (cross A B)) ↔ TheIs (fun A => R A x) (fun A => ψ (cross A B)) :=
  Iff.rfl

/-- ✱35·1. \(\vdash:x(\alpha\upharpoonleft R)y.\equiv.x\in \alpha.xRy \quad[\text{*21·3.(*35·01)}]\) -/
theorem pm35_1 {A : Set α} {R : α → β → Prop} {x : α} {y : β} :
    (A ◁ R) x y ↔ x ∈ A ∧ R x y := Iff.rfl

/-- ✱35·101. \(\vdash:x(R\upharpoonright \beta)y.\equiv.xRy.y\in \beta\) -/
theorem pm35_101 {R : α → β → Prop} {B : Set β} {x : α} {y : β} :
    (R ↾ B) x y ↔ R x y ∧ y ∈ B := Iff.rfl

/-- ✱35·102. \(\vdash:x(\alpha\upharpoonleft R\upharpoonright \beta)y.\equiv.x\in \alpha.xRy.y\in \beta\) -/
theorem pm35_102 {A : Set α} {R : α → β → Prop} {B : Set β} {x : α} {y : β} :
    (A ◁ R ↾ B) x y ↔ (x ∈ A ∧ R x y) ∧ y ∈ B := Iff.rfl

/-- ✱35·103. \(\vdash:x(\alpha\uparrow \beta)y.\equiv.x\in \alpha.y\in \beta\) -/
theorem pm35_103 {A : Set α} {B : Set β} {x : α} {y : β} :
    cross A B x y ↔ x ∈ A ∧ y ∈ B := Iff.rfl

/-- ✱35·11. \(\vdash.\alpha\upharpoonleft R\upharpoonright \beta=(\alpha\upharpoonleft R)\dot{\cap}(R\upharpoonright \beta)\) -/
theorem pm35_11 {A : Set α} {R : α → β → Prop} {B : Set β} :
    A ◁ R ↾ B = (A ◁ R) ⩀ (R ↾ B) := by
  rel_tac

/-- ✱35·12. \(\vdash.(\alpha\upharpoonleft R)\dot{\cap}(S\upharpoonright \beta)=\alpha\upharpoonleft (R\dot{\cap}S)\upharpoonright \beta\) -/
theorem pm35_12 {A : Set α} {R S : α → β → Prop} {B : Set β} :
    (A ◁ R) ⩀ (S ↾ B) = A ◁ (R ⩀ S) ↾ B := by
  rel_tac

/-- ✱35·13. \(\vdash.(\alpha\upharpoonleft R)\dot{\cap}(\beta\upharpoonleft S)=(\alpha \cap \beta)\upharpoonleft (R\dot{\cap}S)\) -/
theorem pm35_13 {A B : Set α} {R S : α → β → Prop} :
    (A ◁ R) ⩀ (B ◁ S) = (A ∩ B) ◁ (R ⩀ S) := by
  rel_tac

/-- ✱35·14. \(\vdash.(R\upharpoonright \alpha)\dot{\cap}(S\upharpoonright \beta)=(R\dot{\cap}S)\upharpoonright (\alpha \cap \beta) \quad[\text{Similar proof to *35·13}]\) -/
theorem pm35_14 {R S : α → β → Prop} {A B : Set β} :
    (R ↾ A) ⩀ (S ↾ B) = (R ⩀ S) ↾ (A ∩ B) := by
  rel_tac

/-- ✱35·15. \(\vdash.(\alpha\upharpoonleft R\upharpoonright \beta)\dot{\cap}(\alpha'\upharpoonleft S\upharpoonright \beta')=(\alpha \cap \alpha')\upharpoonleft (R\dot{\cap}S)\upharpoonright (\beta \cap \beta')\) -/
theorem pm35_15 {A A' : Set α} {R S : α → β → Prop} {B B' : Set β} :
    (A ◁ R ↾ B) ⩀ (A' ◁ S ↾ B') = (A ∩ A') ◁ (R ⩀ S) ↾ (B ∩ B') := by
  rel_tac

/-- ✱35·16. \(\vdash.(\alpha\upharpoonleft R)\dot{\cap}S=\alpha\upharpoonleft (R\dot{\cap}S)=R\dot{\cap}\alpha\upharpoonleft S \quad[\text{Similar proof to *35·13}]\) -/
theorem pm35_16 {A : Set α} {R S : α → β → Prop} :
    (A ◁ R) ⩀ S = A ◁ (R ⩀ S) ∧ A ◁ (R ⩀ S) = R ⩀ A ◁ S := by
  constructor <;> rel_tac

/-- ✱35·17. \(\vdash.(R\upharpoonright \beta)\dot{\cap}S=(R\dot{\cap}S)\upharpoonright \beta=R\dot{\cap}S\upharpoonright \beta \quad[\text{Similar proof to *35·13}]\) -/
theorem pm35_17 {R S : α → β → Prop} {B : Set β} :
    (R ↾ B) ⩀ S = (R ⩀ S) ↾ B ∧ (R ⩀ S) ↾ B = R ⩀ S ↾ B := by
  constructor <;> rel_tac

/-- ✱35·18. \[\begin{align}\vdash.(\alpha\upharpoonleft R\upharpoonright \beta)\dot{\cap}S=\alpha\upharpoonleft (R\dot{\cap}S)\upharpoonright \beta=R\dot{\cap}\alpha&\upharpoonleft S\upharpoonright \beta\\ &\qquad\qquad\qquad[\text{Similar proof to *35·15}]\end{align}\] -/
theorem pm35_18 {A : Set α} {R S : α → β → Prop} {B : Set β} :
    (A ◁ R ↾ B) ⩀ S = A ◁ (R ⩀ S) ↾ B ∧ A ◁ (R ⩀ S) ↾ B = R ⩀ A ◁ S ↾ B := by
  constructor <;> rel_tac

/-- ✱35·21. \(\vdash.\alpha\upharpoonleft R\upharpoonright \beta=(\alpha\upharpoonleft R)\upharpoonright \beta=\alpha\upharpoonleft (R\upharpoonright \beta)\) -/
theorem pm35_21 {A : Set α} {R : α → β → Prop} {B : Set β} :
    A ◁ R ↾ B = (A ◁ R) ↾ B ∧ (A ◁ R) ↾ B = A ◁ (R ↾ B) := by
  constructor <;> rel_tac

/-- ✱35·22. \(\vdash.(\alpha\upharpoonleft R)\mid S=\alpha\upharpoonleft (R\mid S)\) -/
theorem pm35_22 {A : Set α} {R : α → β → Prop} {S : β → γ → Prop} :
    (A ◁ R) ⨾ S = A ◁ (R ⨾ S) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, ⟨ha, h1⟩, h2⟩
    exact ⟨ha, y, h1, h2⟩
  · rintro ⟨ha, y, h1, h2⟩
    exact ⟨y, ⟨ha, h1⟩, h2⟩

/-- ✱35·23. \(\vdash.S\mid (R\upharpoonright \beta)=(S\mid R)\upharpoonright \beta \quad[\text{Similar proof to *35·22}]\) -/
theorem pm35_23 {S : α → β → Prop} {R : β → γ → Prop} {B : Set γ} :
    S ⨾ (R ↾ B) = (S ⨾ R) ↾ B := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, h1, h2, hb⟩
    exact ⟨⟨y, h1, h2⟩, hb⟩
  · rintro ⟨⟨y, h1, h2⟩, hb⟩
    exact ⟨y, h1, h2, hb⟩

/-- ✱35·24 (Df). \(\alpha\upharpoonleft R\mid S=(\alpha\upharpoonleft R)\mid S \quad\text{Df}\) -/
theorem pm35_24 {A : Set α} {R : α → β → Prop} {S : β → γ → Prop} :
    A ◁ R ⨾ S = (A ◁ R) ⨾ S := rfl

/-- ✱35·25 (Df). \(S\mid R\upharpoonright \beta=(S\mid R)\upharpoonright \beta \quad\text{Df}\) -/
theorem pm35_25 {S : α → β → Prop} {R : β → γ → Prop} {B : Set γ} :
    S ⨾ R ↾ B = (S ⨾ R) ↾ B := rfl

/-- ✱35·26. \[\begin{align}\vdash.(\alpha\upharpoonleft R)\mid (S\upharpoonright \beta)&=\alpha\upharpoonleft (R\mid S)\upharpoonright \beta=\{\alpha\upharpoonleft (R\mid S)\}\upharpoonright \beta=\alpha\upharpoonleft \{(R\mid S)\upharpoonright \beta\}\\ &=\{(\alpha\upharpoonleft R)\mid S)\}\upharpoonright \beta=\alpha\upharpoonleft \{R\mid (S\upharpoonright \beta)\}\\ &=(\alpha\upharpoonleft R\mid S)\upharpoonright \beta=\alpha\upharpoonleft (R\mid S\upharpoonright \beta)\end{align}\]

**Status.** proved (reading): the e-text has an unbalanced bracket in the fifth term,
`{(α ↿ R) | S)} ↾ β`, read `{(α ↿ R) | S} ↾ β`. The chain of eight terms is the conjunction of
its seven links (✱13·03), bracketed to the left. -/
theorem pm35_26 {A : Set α} {R : α → β → Prop} {S : β → γ → Prop} {B : Set γ} :
    ((((((A ◁ R) ⨾ (S ↾ B) = A ◁ (R ⨾ S) ↾ B ∧
      A ◁ (R ⨾ S) ↾ B = (A ◁ (R ⨾ S)) ↾ B) ∧
      (A ◁ (R ⨾ S)) ↾ B = A ◁ ((R ⨾ S) ↾ B)) ∧
      A ◁ ((R ⨾ S) ↾ B) = ((A ◁ R) ⨾ S) ↾ B) ∧
      ((A ◁ R) ⨾ S) ↾ B = A ◁ (R ⨾ (S ↾ B))) ∧
      A ◁ (R ⨾ (S ↾ B)) = (A ◁ R ⨾ S) ↾ B) ∧
      (A ◁ R ⨾ S) ↾ B = A ◁ (R ⨾ S ↾ B) := by
  have e1 : (A ◁ R) ⨾ (S ↾ B) = A ◁ ((R ⨾ S) ↾ B) := by rw [pm35_22, pm35_23]
  have e2 : (A ◁ (R ⨾ S)) ↾ B = A ◁ ((R ⨾ S) ↾ B) := (pm35_21 (R := R ⨾ S)).2
  have e3 : ((A ◁ R) ⨾ S) ↾ B = A ◁ ((R ⨾ S) ↾ B) := by rw [pm35_22, e2]
  have e4 : A ◁ (R ⨾ (S ↾ B)) = A ◁ ((R ⨾ S) ↾ B) := by rw [pm35_23]
  exact ⟨⟨⟨⟨⟨⟨e1.trans e2.symm, rfl⟩, e2⟩, e3.symm⟩, e3.trans e4.symm⟩, e4.trans e3.symm⟩, e3⟩

/-- ✱35·27 (Df). \(\alpha\upharpoonleft R\mid S\upharpoonright \beta=(\alpha\upharpoonleft R\mid S)\upharpoonright \beta \quad\text{Df}\) -/
theorem pm35_27 {A : Set α} {R : α → β → Prop} {S : β → γ → Prop} {B : Set γ} :
    A ◁ R ⨾ S ↾ B = ((A ◁ R) ⨾ S) ↾ B := rfl

/-- ✱35·31. \(\vdash.(R\upharpoonright \alpha)\upharpoonright \beta=R\upharpoonright (\alpha\cap \beta)\) -/
theorem pm35_31 {R : α → β → Prop} {A B : Set β} : (R ↾ A) ↾ B = R ↾ (A ∩ B) := by
  rel_tac

/-- ✱35·32. \(\vdash.\alpha\upharpoonleft (\beta\upharpoonleft R)=(\alpha\cap \beta)\upharpoonleft R \quad[\text{Proof similar to that of *35·31}]\) -/
theorem pm35_32 {A B : Set α} {R : α → β → Prop} : A ◁ (B ◁ R) = (A ∩ B) ◁ R := by
  rel_tac

/-- ✱35·33. \(\vdash.(\alpha\upharpoonleft R\upharpoonright \beta)\upharpoonright \gamma=\{\alpha\upharpoonleft R\upharpoonright (\beta\cap \gamma)\} \quad[\text{Proof similar to that of *35·31}]\) -/
theorem pm35_33 {A : Set α} {R : α → β → Prop} {B G : Set β} :
    (A ◁ R ↾ B) ↾ G = A ◁ R ↾ (B ∩ G) := by
  rel_tac

/-- ✱35·34. \(\vdash.\alpha\upharpoonleft (\beta\upharpoonleft R\upharpoonright \gamma)=\{(\alpha\cap \beta)\upharpoonleft R\upharpoonright \gamma\} \quad[\text{Proof similar to that of *35·31}]\) -/
theorem pm35_34 {A B : Set α} {R : α → β → Prop} {G : Set β} :
    A ◁ (B ◁ R ↾ G) = (A ∩ B) ◁ R ↾ G := by
  rel_tac

/-- ✱35·35. \(\vdash.\alpha\upharpoonleft R=(\alpha\cap \text{D}ʻR)\upharpoonleft R\) -/
theorem pm35_35 {A : Set α} {R : α → β → Prop} : A ◁ R = (A ∩ dom R) ◁ R := by
  funext x y
  apply propext
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨⟨ha, mem_dom_of h⟩, h⟩
  · rintro ⟨⟨ha, -⟩, h⟩
    exact ⟨ha, h⟩

/-- ✱35·351. \(\vdash.R\upharpoonright \beta=R\upharpoonright (\beta\cap \text{ᗡ}ʻR) \quad[\text{Proof as in *35·35}]\) -/
theorem pm35_351 {R : α → β → Prop} {B : Set β} : R ↾ B = R ↾ (B ∩ codom R) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨h, hb⟩
    exact ⟨h, hb, mem_codom_of h⟩
  · rintro ⟨h, hb, -⟩
    exact ⟨h, hb⟩

/-- ✱35·352. \(\vdash.\alpha\upharpoonleft R\upharpoonright \beta=(\alpha\cap \text{D}ʻR)\upharpoonleft R\upharpoonright (\beta\cap \text{ᗡ}ʻR) \quad[\text{Proof as in *35·35}]\) -/
theorem pm35_352 {A : Set α} {R : α → β → Prop} {B : Set β} :
    A ◁ R ↾ B = (A ∩ dom R) ◁ R ↾ (B ∩ codom R) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨ha, h⟩, hb⟩
    exact ⟨⟨⟨ha, mem_dom_of h⟩, h⟩, hb, mem_codom_of h⟩
  · rintro ⟨⟨⟨ha, -⟩, h⟩, hb, -⟩
    exact ⟨⟨ha, h⟩, hb⟩

/-- ✱35·354. \(\vdash.(R\upharpoonright \alpha)\mid S=R\mid \alpha\upharpoonleft S\) -/
theorem pm35_354 {R : α → β → Prop} {A : Set β} {S : β → γ → Prop} :
    (R ↾ A) ⨾ S = R ⨾ A ◁ S := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, ⟨h1, ha⟩, h2⟩
    exact ⟨y, h1, ha, h2⟩
  · rintro ⟨y, h1, ha, h2⟩
    exact ⟨y, ⟨h1, ha⟩, h2⟩

/-- ✱35·41. \(\vdash.(\alpha\cup \alpha')\upharpoonleft R=\alpha\upharpoonleft R\unicode{x228d}\alpha'\upharpoonleft R \quad[\text{*35·1.*22·34}]\) -/
theorem pm35_41 {A A' : Set α} {R : α → β → Prop} : (A ∪ A') ◁ R = A ◁ R ⊍ A' ◁ R := by
  rel_tac

/-- ✱35·412. \(\vdash.R\upharpoonright (\beta\cup \beta')=R\upharpoonright \beta\unicode{x228d}R\upharpoonright \beta' \quad[\text{*35·101.*22·34}]\) -/
theorem pm35_412 {R : α → β → Prop} {B B' : Set β} : R ↾ (B ∪ B') = R ↾ B ⊍ R ↾ B' := by
  rel_tac

/-- ✱35·413. \[\begin{align}\vdash.(\alpha\cup\alpha')\upharpoonleft R\upharpoonright (\beta\cup\beta')&=(\alpha\upharpoonleft R\upharpoonright \beta)\unicode{x228d}(\alpha\upharpoonleft R\upharpoonright \beta')\\ &\unicode{x228d}(\alpha'\upharpoonleft R\upharpoonright \beta)\unicode{x228d}(\alpha'\upharpoonleft R\upharpoonright \beta') \quad[\text{*35·102.*22·34}]\end{align}\] -/
theorem pm35_413 {A A' : Set α} {R : α → β → Prop} {B B' : Set β} :
    (A ∪ A') ◁ R ↾ (B ∪ B') =
      (A ◁ R ↾ B) ⊍ (A ◁ R ↾ B') ⊍ (A' ◁ R ↾ B) ⊍ (A' ◁ R ↾ B') := by
  rel_tac

/-- ✱35·42. \(\vdash.\alpha\upharpoonleft (R\unicode{x228d}S)=(\alpha\upharpoonleft R)\unicode{x228d}(\alpha\upharpoonleft S) \quad[\text{*35·1.*23·34}]\) -/
theorem pm35_42 {A : Set α} {R S : α → β → Prop} : A ◁ (R ⊍ S) = (A ◁ R) ⊍ (A ◁ S) := by
  rel_tac

/-- ✱35·421. \(\vdash.(R\unicode{x228d}S)\upharpoonright \beta=(R\upharpoonright \beta)\unicode{x228d}(S\upharpoonright \beta) \quad[\text{*35·101.*23·34}]\) -/
theorem pm35_421 {R S : α → β → Prop} {B : Set β} : (R ⊍ S) ↾ B = (R ↾ B) ⊍ (S ↾ B) := by
  rel_tac

/-- ✱35·422. \(\vdash.\alpha\upharpoonleft (R\unicode{x228d}S)\upharpoonright \beta=(\alpha\upharpoonleft R\upharpoonright \beta)\unicode{x228d}(\alpha\upharpoonleft S\upharpoonright \beta) \quad[\text{*35·102.*23·34}]\) -/
theorem pm35_422 {A : Set α} {R S : α → β → Prop} {B : Set β} :
    A ◁ (R ⊍ S) ↾ B = (A ◁ R ↾ B) ⊍ (A ◁ S ↾ B) := by
  rel_tac

/-- ✱35·43. \(\vdash:\alpha\subset\beta.\supset.\alpha\upharpoonleft R\unicode{x2abd}\beta\upharpoonleft R\) -/
theorem pm35_43 {A B : Set α} {R : α → β → Prop} : A ⊆ B → A ◁ R ⪽ B ◁ R := by
  rintro h x y ⟨ha, hr⟩
  exact ⟨h ha, hr⟩

/-- ✱35·431. \(\vdash:\beta\subset\gamma.\supset.R\upharpoonright \beta\unicode{x2abd}R\upharpoonright \gamma \quad[\text{Proof similar to that of *35·43}]\) -/
theorem pm35_431 {R : α → β → Prop} {B G : Set β} : B ⊆ G → R ↾ B ⪽ R ↾ G := by
  rintro h x y ⟨hr, hb⟩
  exact ⟨hr, h hb⟩

/-- ✱35·432. \[\begin{align}\vdash:\alpha\subset\gamma.\beta\subset\delta.\supset.\alpha\upharpoonleft R\upharpoonright \beta&\unicode{x2abd}\gamma\upharpoonleft R\upharpoonright \delta\\ &[\text{Proof similar to that of *35·43}]\end{align}\] -/
theorem pm35_432 {A G : Set α} {R : α → β → Prop} {B H : Set β} :
    A ⊆ G ∧ B ⊆ H → A ◁ R ↾ B ⪽ G ◁ R ↾ H := by
  rintro ⟨h1, h2⟩ x y ⟨⟨ha, hr⟩, hb⟩
  exact ⟨⟨h1 ha, hr⟩, h2 hb⟩

/-- ✱35·44. \(\vdash.\alpha\upharpoonleft R\unicode{x2abd}R\) -/
theorem pm35_44 {A : Set α} {R : α → β → Prop} : A ◁ R ⪽ R := by
  rintro x y ⟨-, h⟩
  exact h

/-- ✱35·441. \(\vdash.R\upharpoonright \beta\unicode{x2abd}R \quad[\text{Proof similar to that of *35·44}]\) -/
theorem pm35_441 {R : α → β → Prop} {B : Set β} : R ↾ B ⪽ R := by
  rintro x y ⟨h, -⟩
  exact h

/-- ✱35·442. \(\vdash.\alpha\upharpoonleft R\upharpoonright \beta\unicode{x2abd}R \quad[\text{Proof similar to that of *35·44}]\) -/
theorem pm35_442 {A : Set α} {R : α → β → Prop} {B : Set β} : A ◁ R ↾ B ⪽ R := by
  rintro x y ⟨⟨-, h⟩, -⟩
  exact h

/-- ✱35·451. \(\vdash:\text{D}ʻR\subset\alpha.\supset.\alpha\upharpoonleft R=R\) -/
theorem pm35_451 {A : Set α} {R : α → β → Prop} : dom R ⊆ A → A ◁ R = R := by
  intro h
  funext x y
  apply propext
  constructor
  · rintro ⟨-, hr⟩
    exact hr
  · intro hr
    exact ⟨h (mem_dom_of hr), hr⟩

/-- ✱35·452. \(\vdash:\text{ᗡ}ʻR\subset\beta.\supset.R\upharpoonright \beta=R \quad[\text{Similar proof}]\) -/
theorem pm35_452 {R : α → β → Prop} {B : Set β} : codom R ⊆ B → R ↾ B = R := by
  intro h
  funext x y
  apply propext
  constructor
  · rintro ⟨hr, -⟩
    exact hr
  · intro hr
    exact ⟨hr, h (mem_codom_of hr)⟩

/-- ✱35·453. \(\vdash:\text{D}ʻR\subset\alpha.\supset.\alpha\upharpoonleft R\upharpoonright \beta=R\upharpoonright \beta \quad[\text{Similar proof}]\) -/
theorem pm35_453 {A : Set α} {R : α → β → Prop} {B : Set β} :
    dom R ⊆ A → A ◁ R ↾ B = R ↾ B := by
  intro h
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨-, hr⟩, hb⟩
    exact ⟨hr, hb⟩
  · rintro ⟨hr, hb⟩
    exact ⟨⟨h (mem_dom_of hr), hr⟩, hb⟩

/-- ✱35·454. \(\vdash:\text{ᗡ}ʻR\subset\beta.\supset.\alpha\upharpoonleft R\upharpoonright \beta=\alpha\upharpoonleft R \quad[\text{Similar proof}]\) -/
theorem pm35_454 {A : Set α} {R : α → β → Prop} {B : Set β} :
    codom R ⊆ B → A ◁ R ↾ B = A ◁ R := by
  intro h
  funext x y
  apply propext
  constructor
  · rintro ⟨h1, -⟩
    exact h1
  · rintro ⟨ha, hr⟩
    exact ⟨⟨ha, hr⟩, h (mem_codom_of hr)⟩

/-- ✱35·46. \(\vdash:R\unicode{x2abd}S.\supset.\alpha\upharpoonleft R\unicode{x2abd}\alpha\upharpoonleft S\) -/
theorem pm35_46 {A : Set α} {R S : α → β → Prop} : R ⪽ S → A ◁ R ⪽ A ◁ S := by
  rintro h x y ⟨ha, hr⟩
  exact ⟨ha, h x y hr⟩

/-- ✱35·461. \(\vdash:R\unicode{x2abd}S.\supset.R\upharpoonright \beta\unicode{x2abd}S\upharpoonright \beta \quad[\text{Similar proof}]\) -/
theorem pm35_461 {R S : α → β → Prop} {B : Set β} : R ⪽ S → R ↾ B ⪽ S ↾ B := by
  rintro h x y ⟨hr, hb⟩
  exact ⟨h x y hr, hb⟩

/-- ✱35·462. \(\vdash:R\unicode{x2abd}S.\supset.\alpha\upharpoonleft R\upharpoonright \beta\unicode{x2abd}\alpha\upharpoonleft S\upharpoonright \beta \quad[\text{Similar proof}]\) -/
theorem pm35_462 {A : Set α} {R S : α → β → Prop} {B : Set β} :
    R ⪽ S → A ◁ R ↾ B ⪽ A ◁ S ↾ B := by
  rintro h x y ⟨⟨ha, hr⟩, hb⟩
  exact ⟨⟨ha, h x y hr⟩, hb⟩

/-- ✱35·471. \(\vdash:\text{ᗡ}ʻP\cap \alpha=\Lambda.\supset.P\mid (\alpha\upharpoonleft R)=\dot{\Lambda}\) -/
theorem pm35_471 {P : α → β → Prop} {A : Set β} {R : β → γ → Prop} :
    codom P ∩ A = Λ → P ⨾ (A ◁ R) = rNull := by
  intro h
  rw [eq_Null_iff] at h
  rw [eq_rNull_iff]
  rintro ⟨x, z, y, h1, ha, -⟩
  exact h ⟨y, mem_codom_of h1, ha⟩

/-- ✱35·472. \(\vdash:\text{D}ʻP\cap \alpha=\Lambda.\supset.(R\upharpoonright \alpha)\mid P=\dot{\Lambda}\) -/
theorem pm35_472 {P : β → γ → Prop} {A : Set β} {R : α → β → Prop} :
    dom P ∩ A = Λ → (R ↾ A) ⨾ P = rNull := by
  intro h
  rw [eq_Null_iff] at h
  rw [eq_rNull_iff]
  rintro ⟨x, z, y, ⟨-, ha⟩, h2⟩
  exact h ⟨y, mem_dom_of h2, ha⟩

/-- ✱35·473. \(\vdash:\text{ᗡ}ʻP\cap \alpha=\Lambda.\supset.P\mid (\alpha\upharpoonleft R\upharpoonright \beta)=\dot{\Lambda}\) -/
theorem pm35_473 {P : α → β → Prop} {A : Set β} {R : β → γ → Prop} {B : Set γ} :
    codom P ∩ A = Λ → P ⨾ (A ◁ R ↾ B) = rNull := by
  intro h
  rw [eq_Null_iff] at h
  rw [eq_rNull_iff]
  rintro ⟨x, z, y, h1, ⟨ha, -⟩, -⟩
  exact h ⟨y, mem_codom_of h1, ha⟩

/-- ✱35·474. \(\vdash:\text{D}ʻP\cap \beta=\Lambda.\supset.(\alpha\upharpoonleft R\upharpoonright \beta)\mid P=\dot{\Lambda}\) -/
theorem pm35_474 {P : β → γ → Prop} {A : Set α} {R : α → β → Prop} {B : Set β} :
    dom P ∩ B = Λ → (A ◁ R ↾ B) ⨾ P = rNull := by
  intro h
  rw [eq_Null_iff] at h
  rw [eq_rNull_iff]
  rintro ⟨x, z, y, ⟨-, hb⟩, h2⟩
  exact h ⟨y, mem_dom_of h2, hb⟩

/-- ✱35·48. \(\vdash:\text{ᗡ}ʻP\subset\alpha.\supset.P\mid (\alpha\upharpoonleft R)=P\mid R\) -/
theorem pm35_48 {P : α → β → Prop} {A : Set β} {R : β → γ → Prop} :
    codom P ⊆ A → P ⨾ (A ◁ R) = P ⨾ R := by
  intro h
  funext x z
  apply propext
  constructor
  · rintro ⟨y, h1, -, h2⟩
    exact ⟨y, h1, h2⟩
  · rintro ⟨y, h1, h2⟩
    exact ⟨y, h1, h (mem_codom_of h1), h2⟩

/-- ✱35·481. \(\vdash:\text{D}ʻR\subset\beta.\supset.(P\upharpoonright \beta)\mid R=P\mid R \quad[\text{Similar proof}]\) -/
theorem pm35_481 {P : α → β → Prop} {B : Set β} {R : β → γ → Prop} :
    dom R ⊆ B → (P ↾ B) ⨾ R = P ⨾ R := by
  intro h
  funext x z
  apply propext
  constructor
  · rintro ⟨y, ⟨h1, -⟩, h2⟩
    exact ⟨y, h1, h2⟩
  · rintro ⟨y, h1, h2⟩
    exact ⟨y, ⟨h1, h (mem_dom_of h2)⟩, h2⟩

/-- ✱35·51. \(\vdash.\text{Cnv}ʻ(\alpha\upharpoonleft R)=\breve{R}\upharpoonright \alpha\) -/
theorem pm35_51 {A : Set α} {R : α → β → Prop} : (A ◁ R)˘ = R˘ ↾ A := by
  rel_tac

/-- ✱35·52. \(\vdash.\text{Cnv}ʻ(R\upharpoonright \beta)=\beta\upharpoonleft \breve{R} \quad[\text{Proof similar to that of *35·51}]\) -/
theorem pm35_52 {R : α → β → Prop} {B : Set β} : (R ↾ B)˘ = B ◁ R˘ := by
  rel_tac

/-- ✱35·53. \(\vdash.\text{Cnv}ʻ(\alpha\upharpoonleft R\upharpoonright \beta)=\beta\upharpoonleft \breve{R}\upharpoonright \alpha \quad[\text{Proof similar to that of *35·51}]\) -/
theorem pm35_53 {A : Set α} {R : α → β → Prop} {B : Set β} : (A ◁ R ↾ B)˘ = B ◁ R˘ ↾ A := by
  rel_tac

/-- ✱35·61. \(\vdash.\text{D}ʻ(\alpha\upharpoonleft R)=\alpha\cap \text{D}ʻR\) -/
theorem pm35_61 {A : Set α} {R : α → β → Prop} : dom (A ◁ R) = A ∩ dom R := by
  ext x
  constructor
  · rintro ⟨y, ha, h⟩
    exact ⟨ha, y, h⟩
  · rintro ⟨ha, y, h⟩
    exact ⟨y, ha, h⟩

/-- ✱35·62. \(\vdash:\alpha\subset\text{D}ʻR.\supset.\text{D}ʻ(\alpha\upharpoonleft R)=\alpha \quad[\text{*35·61.*22·621}]\) -/
theorem pm35_62 {A : Set α} {R : α → β → Prop} : A ⊆ dom R → dom (A ◁ R) = A := by
  intro h
  rw [pm35_61]
  exact Set.inter_eq_left.2 h

/-- ✱35·63. \(\vdash:\text{D}ʻR\subset\alpha.\equiv.\alpha\upharpoonleft R=R\) -/
theorem pm35_63 {A : Set α} {R : α → β → Prop} : dom R ⊆ A ↔ A ◁ R = R := by
  constructor
  · exact pm35_451
  · rintro h x ⟨y, hr⟩
    have h' : (A ◁ R) x y := by
      rw [h]
      exact hr
    exact h'.1

/-- ✱35·64. \(\vdash.\text{ᗡ}ʻ(R\upharpoonright \beta)=\beta\cap \text{ᗡ}ʻR \quad[\text{Proof as in *35·61}]\) -/
theorem pm35_64 {R : α → β → Prop} {B : Set β} : codom (R ↾ B) = B ∩ codom R := by
  ext y
  constructor
  · rintro ⟨x, h, hb⟩
    exact ⟨hb, x, h⟩
  · rintro ⟨hb, x, h⟩
    exact ⟨x, h, hb⟩

/-- ✱35·641. \(\vdash:\alpha\cap \text{D}ʻR=\Lambda.\supset.\alpha\upharpoonleft R=\dot{\Lambda} \quad[\text{*35·61.*33·241}]\) -/
theorem pm35_641 {A : Set α} {R : α → β → Prop} : A ∩ dom R = Λ → A ◁ R = rNull := by
  intro h
  rw [eq_Null_iff] at h
  rw [eq_rNull_iff]
  rintro ⟨x, y, ha, hr⟩
  exact h ⟨x, ha, mem_dom_of hr⟩

/-- ✱35·642. \(\vdash:\alpha\cap \text{ᗡ}ʻR=\Lambda.\supset.R\upharpoonright \alpha=\dot{\Lambda} \quad[\text{*35·64.*33·241}]\) -/
theorem pm35_642 {A : Set β} {R : α → β → Prop} : A ∩ codom R = Λ → R ↾ A = rNull := by
  intro h
  rw [eq_Null_iff] at h
  rw [eq_rNull_iff]
  rintro ⟨x, y, hr, ha⟩
  exact h ⟨y, ha, mem_codom_of hr⟩

/-- ✱35·643. \(\vdash:\alpha\cap \text{D}ʻR=\Lambda.\supset.\alpha\upharpoonleft (R\unicode{x228d}S)=\alpha\upharpoonleft S \quad[\text{*35·641·42}]\) -/
theorem pm35_643 {A : Set α} {R S : α → β → Prop} :
    A ∩ dom R = Λ → A ◁ (R ⊍ S) = A ◁ S := by
  intro h
  rw [pm35_42, pm35_641 h, rNull_rcup]

/-- ✱35·644. \(\vdash:\alpha\cap \text{ᗡ}ʻR=\Lambda.\supset.(R\unicode{x228d}S)\upharpoonright \alpha=S\upharpoonright \alpha \quad[\text{*35·642·421}]\) -/
theorem pm35_644 {A : Set β} {R S : α → β → Prop} :
    A ∩ codom R = Λ → (R ⊍ S) ↾ A = S ↾ A := by
  intro h
  rw [pm35_421, pm35_642 h, rNull_rcup]

/-- ✱35·65. \(\vdash:\beta\subset\text{ᗡ}ʻR.\supset.\text{ᗡ}ʻ(R\upharpoonright \beta)=\beta \quad[\text{*35·64.*22·621}]\) -/
theorem pm35_65 {R : α → β → Prop} {B : Set β} : B ⊆ codom R → codom (R ↾ B) = B := by
  intro h
  rw [pm35_64]
  exact Set.inter_eq_left.2 h

/-- ✱35·66. \(\vdash:\text{ᗡ}ʻR\subset\beta.\equiv.R\upharpoonright \beta=R \quad[\text{Proof as in *35·63}]\) -/
theorem pm35_66 {R : α → β → Prop} {B : Set β} : codom R ⊆ B ↔ R ↾ B = R := by
  constructor
  · exact pm35_452
  · rintro h y ⟨x, hr⟩
    have h' : (R ↾ B) x y := by
      rw [h]
      exact hr
    exact h'.2

/-- ✱35·671. \(\vdash.\text{D}ʻ(R\mid S)=\text{D}ʻ(R\upharpoonright \text{D}ʻS)\) -/
theorem pm35_671 {R : α → β → Prop} {S : β → γ → Prop} : dom (R ⨾ S) = dom (R ↾ dom S) := by
  ext x
  constructor
  · rintro ⟨z, y, h1, h2⟩
    exact ⟨y, h1, mem_dom_of h2⟩
  · rintro ⟨y, h1, z, h2⟩
    exact ⟨z, y, h1, h2⟩

/-- ✱35·672. \(\vdash.\text{ᗡ}ʻ(R\mid S)=\text{ᗡ}ʻ(\text{ᗡ}ʻR\upharpoonleft S) \quad[\text{Similar proof}]\) -/
theorem pm35_672 {R : α → β → Prop} {S : β → γ → Prop} :
    codom (R ⨾ S) = codom (codom R ◁ S) := by
  ext z
  constructor
  · rintro ⟨x, y, h1, h2⟩
    exact ⟨y, mem_codom_of h1, h2⟩
  · rintro ⟨y, ⟨x, h1⟩, h2⟩
    exact ⟨x, y, h1, h2⟩

/-- ✱35·68. \(\vdash:\alpha\cap \beta=\Lambda.\supset.(\alpha\upharpoonleft R\upharpoonright \beta)^{2}=\dot{\Lambda}\) -/
theorem pm35_68 {A B : Set α} {R : α → α → Prop} :
    A ∩ B = Λ → rsq (A ◁ R ↾ B) = rNull := by
  intro h
  rw [eq_Null_iff] at h
  rw [eq_rNull_iff]
  rintro ⟨x, z, y, ⟨-, hb⟩, ⟨⟨ha, -⟩, -⟩⟩
  exact h ⟨y, ha, hb⟩

/-- ✱35·7. \(\vdash:\phi\{(R\upharpoonright \beta)ʻy\}.\equiv.y\in \beta.\phi(Rʻy)\) -/
theorem pm35_7 {R : α → β → Prop} {B : Set β} {y : β} {φ : α → Prop} :
    Desc (R ↾ B) y φ ↔ y ∈ B ∧ Desc R y φ := by
  constructor
  · rintro ⟨b, hb, hφ⟩
    have hRb : R b y ∧ y ∈ B := (hb b).2 rfl
    refine ⟨hRb.2, b, fun x => ⟨fun hx => (hb x).1 ⟨hx, hRb.2⟩, ?_⟩, hφ⟩
    rintro rfl
    exact hRb.1
  · rintro ⟨hy, b, hb, hφ⟩
    refine ⟨b, fun x => ⟨?_, fun e => ⟨(hb x).2 e, hy⟩⟩, hφ⟩
    rintro ⟨hx, -⟩
    exact (hb x).1 hx

/-- ✱35·71. \(\vdash\colon\ldotp y\in \beta.\supset_{y}.Rʻy=Sʻy:\supset.R\upharpoonright \beta=S\upharpoonright \beta\) -/
theorem pm35_71 {R S : α → β → Prop} {B : Set β} :
    (∀ y, y ∈ B → Desc R y (fun b => Desc S y (fun c => b = c))) → R ↾ B = S ↾ B := by
  intro h
  funext x y
  apply propext
  constructor
  · rintro ⟨hr, hy⟩
    obtain ⟨b, hb, c, hc, rfl⟩ := h y hy
    exact ⟨(hc x).2 ((hb x).1 hr), hy⟩
  · rintro ⟨hs, hy⟩
    obtain ⟨b, hb, c, hc, rfl⟩ := h y hy
    exact ⟨(hb x).2 ((hc x).1 hs), hy⟩

/-- ✱35·75. \(\vdash.\Lambda\upharpoonleft R=R\upharpoonright \Lambda=\Lambda\upharpoonleft R\upharpoonright \beta=\alpha\upharpoonleft R\upharpoonright \Lambda=\dot{\Lambda}\) -/
theorem pm35_75 {A : Set α} {R : α → β → Prop} {B : Set β} :
    (((Λ : Set α) ◁ R = R ↾ (Λ : Set β) ∧ R ↾ (Λ : Set β) = (Λ : Set α) ◁ R ↾ B) ∧
      (Λ : Set α) ◁ R ↾ B = A ◁ R ↾ (Λ : Set β)) ∧ A ◁ R ↾ (Λ : Set β) = rNull := by
  have h1 : (Λ : Set α) ◁ R = rNull := by
    rw [eq_rNull_iff]
    rintro ⟨x, y, hx, -⟩
    exact not_mem_Null x hx
  have h2 : R ↾ (Λ : Set β) = rNull := by
    rw [eq_rNull_iff]
    rintro ⟨x, y, -, hy⟩
    exact not_mem_Null y hy
  have h3 : (Λ : Set α) ◁ R ↾ B = rNull := by
    rw [eq_rNull_iff]
    rintro ⟨x, y, ⟨hx, -⟩, -⟩
    exact not_mem_Null x hx
  have h4 : A ◁ R ↾ (Λ : Set β) = rNull := by
    rw [eq_rNull_iff]
    rintro ⟨x, y, -, hy⟩
    exact not_mem_Null y hy
  exact ⟨⟨⟨h1.trans h2.symm, h2.trans h3.symm⟩, h3.trans h4.symm⟩, h4⟩

/-- ✱35·76. \(\vdash.\text{V}\upharpoonleft R=R\upharpoonright \text{V}=\text{V}\upharpoonleft R\upharpoonright \text{V}=R\) -/
theorem pm35_76 {R : α → β → Prop} :
    ((V : Set α) ◁ R = R ↾ (V : Set β) ∧ R ↾ (V : Set β) = (V : Set α) ◁ R ↾ (V : Set β)) ∧
      (V : Set α) ◁ R ↾ (V : Set β) = R := by
  have h1 : (V : Set α) ◁ R = R := by
    funext x y
    exact propext ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  have h2 : R ↾ (V : Set β) = R := by
    funext x y
    exact propext ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  have h3 : (V : Set α) ◁ R ↾ (V : Set β) = R := by
    funext x y
    exact propext ⟨fun h => h.1.2, fun h => ⟨⟨rfl, h⟩, rfl⟩⟩
  exact ⟨⟨h1.trans h2.symm, h2.trans h3.symm⟩, h3⟩

/-- ✱35·81. \(\vdash:x(\alpha\upharpoonleft \dot{\text{V}})y.\equiv.x\in \alpha \quad[\text{*35·1.*25·104}]\) -/
theorem pm35_81 {A : Set α} {x : α} {y : β} : (A ◁ rV) x y ↔ x ∈ A :=
  ⟨fun h => h.1, fun h => ⟨h, rfl, rfl⟩⟩

/-- ✱35·812. \(\vdash:x(\dot{\text{V}}\upharpoonright \beta)y.\equiv.y\in \beta \quad[\text{*35·101.*25·104}]\) -/
theorem pm35_812 {B : Set β} {x : α} {y : β} : (rV ↾ B) x y ↔ y ∈ B :=
  ⟨fun h => h.2, fun h => ⟨⟨rfl, rfl⟩, h⟩⟩

/-- ✱35·82. \(\vdash.\alpha\uparrow \beta=\alpha\upharpoonleft \dot{\text{V}}\upharpoonright \beta\) -/
theorem pm35_82 {A : Set α} {B : Set β} : cross A B = A ◁ rV ↾ B := by
  funext x y
  apply propext
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨⟨ha, rfl, rfl⟩, hb⟩
  · rintro ⟨⟨ha, -⟩, hb⟩
    exact ⟨ha, hb⟩

/-- ✱35·822. \(\vdash.\alpha\upharpoonleft R\upharpoonright \beta=R\dot{\cap}(\alpha\uparrow \beta)\) -/
theorem pm35_822 {A : Set α} {R : α → β → Prop} {B : Set β} :
    A ◁ R ↾ B = R ⩀ cross A B := by
  rel_tac

/-- ✱35·83. \(\vdash:\text{D}ʻR\subset \alpha.\text{ᗡ}ʻR\subset \beta.\equiv.R\unicode{x2abd}\alpha\uparrow \beta\) -/
theorem pm35_83 {R : α → β → Prop} {A : Set α} {B : Set β} :
    dom R ⊆ A ∧ codom R ⊆ B ↔ R ⪽ cross A B := by
  constructor
  · rintro ⟨h1, h2⟩ x y h
    exact ⟨h1 (mem_dom_of h), h2 (mem_codom_of h)⟩
  · intro h
    refine ⟨?_, ?_⟩
    · rintro x ⟨y, hr⟩
      exact (h x y hr).1
    · rintro y ⟨x, hr⟩
      exact (h x y hr).2

/-- ✱35·831. \(\vdash.\dot{-}(\alpha\uparrow \beta)=(-\alpha\uparrow \beta)\unicode{x228d}(\alpha\uparrow -\beta)\unicode{x228d}(-\alpha\uparrow -\beta)\) -/
theorem pm35_831 {A : Set α} {B : Set β} :
    ∸(cross A B) = cross Aᶜ B ⊍ cross A Bᶜ ⊍ cross Aᶜ Bᶜ := by
  rel_tac

/-- ✱35·832. \[\begin{align}&\dot{-}(\alpha\upharpoonleft R\upharpoonright \beta)=(-\alpha\uparrow \beta)\unicode{x228d}(\alpha\uparrow -\beta)\unicode{x228d}(-\alpha\uparrow -\beta)\unicode{x228d}\dot{-}R\\ &\quad[\text{*35·822·831.Transp.*23·84}]\end{align}\] -/
theorem pm35_832 {A : Set α} {R : α → β → Prop} {B : Set β} :
    ∸(A ◁ R ↾ B) = cross Aᶜ B ⊍ cross A Bᶜ ⊍ cross Aᶜ Bᶜ ⊍ ∸R := by
  rel_tac

/-- ✱35·834. \(\vdash.(\alpha\uparrow \beta)\dot{\cap}(\gamma\uparrow \delta)=(\alpha\cap \gamma)\uparrow (\beta\cap \delta)\) -/
theorem pm35_834 {A G : Set α} {B H : Set β} :
    cross A B ⩀ cross G H = cross (A ∩ G) (B ∩ H) := by
  rel_tac

/-- ✱35·84. \(\vdash.\text{Cnv}ʻ(\alpha\uparrow \beta)=\beta\uparrow \alpha \quad[\text{*35·103.*31·131}]\) -/
theorem pm35_84 {A : Set α} {B : Set β} : (cross A B)˘ = cross B A := by
  rel_tac

/-- ✱35·85. \(\vdash:\exists !\beta.\supset.\text{D}ʻ(\alpha\uparrow \beta)=\alpha\) -/
theorem pm35_85 {A : Set α} {B : Set β} : B.Nonempty → dom (cross A B) = A := by
  rintro ⟨b, hb⟩
  ext x
  constructor
  · rintro ⟨y, ha, -⟩
    exact ha
  · intro ha
    exact ⟨b, ha, hb⟩

/-- ✱35·86. \(\vdash:\exists !\alpha.\supset.\text{ᗡ}ʻ(\alpha\uparrow \beta)=\beta \quad[\text{Similar proof}]\) -/
theorem pm35_86 {A : Set α} {B : Set β} : A.Nonempty → codom (cross A B) = B := by
  rintro ⟨a, ha⟩
  ext y
  constructor
  · rintro ⟨x, -, hb⟩
    exact hb
  · intro hb
    exact ⟨a, ha, hb⟩

/-- ✱35·87. \(\vdash:\dot{\exists}!(\alpha\uparrow \beta).\equiv.\exists !\alpha.\exists !\beta\) -/
theorem pm35_87 {A : Set α} {B : Set β} : rEx (cross A B) ↔ A.Nonempty ∧ B.Nonempty := by
  constructor
  · rintro ⟨x, y, ha, hb⟩
    exact ⟨⟨x, ha⟩, ⟨y, hb⟩⟩
  · rintro ⟨⟨x, ha⟩, ⟨y, hb⟩⟩
    exact ⟨x, y, ha, hb⟩

/-- ✱35·88. \[\begin{align}&\vdash\colon\ldotp \alpha\uparrow \beta=\dot{\Lambda}.\equiv:\alpha=\Lambda.\lor.\beta=\Lambda\\ &\quad[\text{*35·87.Transp.*24·51.*25·51}]\end{align}\] -/
theorem pm35_88 {A : Set α} {B : Set β} : cross A B = rNull ↔ A = Λ ∨ B = Λ := by
  rw [eq_rNull_iff, eq_Null_iff, eq_Null_iff, pm35_87, not_and_or]

/-- ✱35·881. \(\vdash:\text{ᗡ}ʻR\subset\alpha.\supset.R\mid (\alpha\uparrow \beta)=\text{D}ʻR\uparrow \beta\) -/
theorem pm35_881 {R : α → β → Prop} {A : Set β} {B : Set γ} :
    codom R ⊆ A → R ⨾ cross A B = cross (dom R) B := by
  intro h
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hr, -, hb⟩
    exact ⟨mem_dom_of hr, hb⟩
  · rintro ⟨⟨y, hr⟩, hb⟩
    exact ⟨y, hr, h (mem_codom_of hr), hb⟩

/-- ✱35·882. \(\vdash:\text{D}ʻR\subset\beta.\supset.(\alpha\uparrow \beta)\mid R=\alpha\uparrow \text{ᗡ}ʻR \quad[\text{Similar proof}]\) -/
theorem pm35_882 {R : β → γ → Prop} {A : Set α} {B : Set β} :
    dom R ⊆ B → cross A B ⨾ R = cross A (codom R) := by
  intro h
  funext x z
  apply propext
  constructor
  · rintro ⟨y, ⟨ha, -⟩, hr⟩
    exact ⟨ha, mem_codom_of hr⟩
  · rintro ⟨ha, ⟨y, hr⟩⟩
    exact ⟨y, ⟨ha, h (mem_dom_of hr)⟩, hr⟩

/-- ✱35·89. \(\vdash:\exists !\beta.\supset.(\alpha\uparrow \beta)\mid (\beta\uparrow \gamma)=(\alpha\uparrow \gamma):{\sim}\exists !\beta.\supset.(\alpha\uparrow \beta)\mid (\beta\uparrow \gamma)=\dot{\Lambda}\) -/
theorem pm35_89 {A : Set α} {B : Set β} {G : Set γ} :
    (B.Nonempty → cross A B ⨾ cross B G = cross A G) ∧
      (¬B.Nonempty → cross A B ⨾ cross B G = rNull) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    funext x z
    apply propext
    constructor
    · rintro ⟨y, ⟨ha, -⟩, ⟨-, hg⟩⟩
      exact ⟨ha, hg⟩
    · rintro ⟨ha, hg⟩
      exact ⟨b, ⟨ha, hb⟩, ⟨hb, hg⟩⟩
  · intro hB
    rw [eq_rNull_iff]
    rintro ⟨x, z, y, ⟨-, hy⟩, -⟩
    exact hB ⟨y, hy⟩

/-- ✱35·891. \(\vdash\colon\ldotp \exists !\beta.\lor .{\sim}\exists !\alpha:\supset.(\alpha\uparrow \beta)\mid (\beta\uparrow \alpha)=(\alpha\uparrow \alpha)\) -/
theorem pm35_891 {A : Set α} {B : Set β} :
    B.Nonempty ∨ ¬A.Nonempty → cross A B ⨾ cross B A = cross A A := by
  rintro (hB | hA)
  · exact pm35_89.1 hB
  · funext x z
    apply propext
    constructor
    · rintro ⟨y, ⟨ha, -⟩, -⟩
      exact (hA ⟨x, ha⟩).elim
    · rintro ⟨ha, -⟩
      exact (hA ⟨x, ha⟩).elim

/-- ✱35·892. \(\vdash:(\alpha\uparrow \alpha)^{2}=(\alpha\uparrow \alpha) \quad\left[\text{*35·891}\, \frac{\alpha}{\beta}\right]\) -/
theorem pm35_892 {A : Set α} : rsq (cross A A) = cross A A := pm35_891 (em A.Nonempty)

/-- ✱35·895. \(\vdash:\alpha \cap \beta=\Lambda.\supset.(\alpha\uparrow \beta)^{2}=\dot{\Lambda} \quad[\text{*35·68·82}]\) -/
theorem pm35_895 {A B : Set α} : A ∩ B = Λ → rsq (cross A B) = rNull := by
  intro h
  rw [pm35_82]
  exact pm35_68 h

/-- ✱35·9. \(\vdash.\text{D}ʻ(\alpha\uparrow \alpha)=\text{ᗡ}ʻ(\alpha\uparrow \alpha)=Cʻ(\alpha\uparrow \alpha)=\alpha\) -/
theorem pm35_9 {A : Set α} :
    (dom (cross A A) = codom (cross A A) ∧ codom (cross A A) = fld (cross A A)) ∧
      fld (cross A A) = A := by
  have h1 : dom (cross A A) = A := by
    ext x
    constructor
    · rintro ⟨y, ha, -⟩
      exact ha
    · intro ha
      exact ⟨x, ha, ha⟩
  have h2 : codom (cross A A) = A := by
    ext x
    constructor
    · rintro ⟨y, -, ha⟩
      exact ha
    · intro ha
      exact ⟨x, ha, ha⟩
  have h3 : fld (cross A A) = A := by rw [pm33_16, h1, h2, Set.union_self]
  exact ⟨⟨h1.trans h2.symm, h2.trans h3.symm⟩, h3⟩

/-- ✱35·91. \(\vdash:R\unicode{x2abd}\alpha\uparrow \alpha.\equiv.CʻR\subset\alpha\) -/
theorem pm35_91 {R : α → α → Prop} {A : Set α} : R ⪽ cross A A ↔ fld R ⊆ A :=
  pm33_352.symm

/-- ✱35·92. \(\vdash\colon\ldotp (\exists \alpha).P=\alpha\uparrow \alpha.\supset:R\unicode{x2abd}P.\equiv.CʻR\subset CʻP \quad[\text{*35·9·91}]\) -/
theorem pm35_92 {P R : α → α → Prop} :
    (∃ A, P = cross A A) → (R ⪽ P ↔ fld R ⊆ fld P) := by
  rintro ⟨A, rfl⟩
  rw [pm35_91, (pm35_9 (A := A)).2]

/-- ✱35·93. \(\vdash:(R).\phi(\text{D}ʻR).\equiv.(\alpha).\phi\alpha\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): for
`R : α → β → Prop` the proposition is false when `β` is empty and `α` is not (every `D'R` is then
`Λ`), so `[Nonempty β]` is added. (PM's proof uses `α ↑ α`, i.e. a homogeneous `R`, for which no
hypothesis is needed; cf. ✱35·932.) -/
theorem pm35_93 [Nonempty β] {φ : Set α → Prop} :
    (∀ R : α → β → Prop, φ (dom R)) ↔ ∀ A : Set α, φ A := by
  constructor
  · intro h A
    have := h (cross A (V : Set β))
    rwa [pm35_85 ⟨Classical.ofNonempty, rfl⟩] at this
  · intro h R
    exact h _

/-- ✱35·931. \(\vdash:(R).\phi(\text{ᗡ}ʻR).\equiv.(\alpha).\phi\alpha \quad[\text{Proof as in *35·93}]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): for
`R : α → β → Prop` the proposition is false when `α` is empty and `β` is not, so `[Nonempty α]`
is added (as in ✱35·93). -/
theorem pm35_931 [Nonempty α] {φ : Set β → Prop} :
    (∀ R : α → β → Prop, φ (codom R)) ↔ ∀ B : Set β, φ B := by
  constructor
  · intro h B
    have := h (cross (V : Set α) B)
    rwa [pm35_86 ⟨Classical.ofNonempty, rfl⟩] at this
  · intro h R
    exact h _

/-- ✱35·932. \(\vdash:(R).\phi(CʻR).\equiv.(\alpha).\phi\alpha \quad[\text{Proof as in *35·93}]\) -/
theorem pm35_932 {φ : Set α → Prop} : (∀ R : α → α → Prop, φ (fld R)) ↔ ∀ A : Set α, φ A := by
  constructor
  · intro h A
    have := h (cross A A)
    rwa [(pm35_9 (A := A)).2] at this
  · intro h R
    exact h _

/-- ✱35·94. \(\vdash:(\exists R).\phi(\text{D}ʻR).\equiv.(\exists \alpha).\phi\alpha \quad[\text{*35·93.Transp}]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I); `[Nonempty β]` is
added as in ✱35·93 (without it, `(∃R).φ(D'R)` fails for `φα . = . α = V` when only `β` is
empty). -/
theorem pm35_94 [Nonempty β] {φ : Set α → Prop} :
    (∃ R : α → β → Prop, φ (dom R)) ↔ ∃ A : Set α, φ A := by
  constructor
  · rintro ⟨R, h⟩
    exact ⟨_, h⟩
  · rintro ⟨A, h⟩
    refine ⟨cross A (V : Set β), ?_⟩
    rwa [pm35_85 ⟨Classical.ofNonempty, rfl⟩]

/-- ✱35·941. \(\vdash:(\exists R).\phi(\text{ᗡ}ʻR).\equiv.(\exists \alpha).\phi\alpha \quad[\text{*35·931. Transp}]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I); `[Nonempty α]` is
added as in ✱35·931. -/
theorem pm35_941 [Nonempty α] {φ : Set β → Prop} :
    (∃ R : α → β → Prop, φ (codom R)) ↔ ∃ B : Set β, φ B := by
  constructor
  · rintro ⟨R, h⟩
    exact ⟨_, h⟩
  · rintro ⟨B, h⟩
    refine ⟨cross (V : Set α) B, ?_⟩
    rwa [pm35_86 ⟨Classical.ofNonempty, rfl⟩]

/-- ✱35·942. \(\vdash:(\exists R).\phi(CʻR).\equiv.(\exists \alpha).\phi\alpha \quad[\text{*35·932.Transp}]\) -/
theorem pm35_942 {φ : Set α → Prop} : (∃ R : α → α → Prop, φ (fld R)) ↔ ∃ A : Set α, φ A := by
  constructor
  · rintro ⟨R, h⟩
    exact ⟨_, h⟩
  · rintro ⟨A, h⟩
    refine ⟨cross A A, ?_⟩
    rwa [(pm35_9 (A := A)).2]

end PrincipiaMathematica
