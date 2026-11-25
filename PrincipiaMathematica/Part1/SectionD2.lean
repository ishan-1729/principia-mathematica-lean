import PrincipiaMathematica.Defs.Part1

/-!
# Part I, Section D: Logic of relations

Volume 1. Numbers: ✱36, ✱37, ✱38.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w u'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

/-! ### Helper lemmas (not PM propositions) -/

private theorem mem_Null_iff (x : α) : x ∈ (Λ : Set α) ↔ False := by
  simp [Null_eq_empty]

private theorem eq_Null_iff {S : Set α} : S = Λ ↔ ¬ S.Nonempty := by
  constructor
  · rintro rfl ⟨x, hx⟩
    exact (mem_Null_iff x).1 hx
  · intro h
    ext x
    exact ⟨fun hx => (h ⟨x, hx⟩).elim, fun hx => ((mem_Null_iff x).1 hx).elim⟩

private theorem not_mem_of_inter_eq_Null {A B : Set α} (h : A ∩ B = Λ) {x : α} (ha : x ∈ A)
    (hb : x ∈ B) : False := by
  have hx : x ∈ A ∩ B := ⟨ha, hb⟩
  rw [h] at hx
  exact (mem_Null_iff x).1 hx

/-- When `R'y` exists and is `b`, `ψ(R'y)` is `ψ b`. -/
private theorem desc_of_unique {R : α → β → Prop} {y : β} {b : α} (h : ∀ x, R x y ↔ x = b)
    {ψ : α → Prop} : Desc R y ψ ↔ ψ b :=
  TheIs_iff_of_unique h

/-- `R'y = S'z` makes `R` relate to `y` exactly what `S` relates to `z`. -/
private theorem rel_iff_of_desc_eq {R : α → β → Prop} {S : α → γ → Prop} {y : β} {z : γ}
    (h : Desc R y (fun a => Desc S z (fun b => a = b))) (x : α) : R x y ↔ S x z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact (ha x).trans (hb x).symm

/-- `ψ(R'S'z)` gives the value of `R'S'z`, which is then the only `x` with `x (R | S) z`
(cf. ✱34·41). -/
private theorem relProd_of_desc2 {R : α → β → Prop} {S : β → γ → Prop} {z : γ} {ψ : α → Prop}
    (h : Desc2 R S z ψ) : ∃ a, (∀ x, (R ⨾ S) x z ↔ x = a) ∧ ψ a := by
  rw [desc2_iff] at h
  obtain ⟨c, hc, a, ha, hψ⟩ := h
  refine ⟨a, fun x => ?_, hψ⟩
  rw [← ha x]
  constructor
  · rintro ⟨y, hxy, hyz⟩
    rwa [← (hc y).1 hyz]
  · intro hxc
    exact ⟨c, hxc, (hc c).2 rfl⟩

private theorem refs_relProd (P : α → β → Prop) (Q : β → γ → Prop) (z : γ) :
    refs (P ⨾ Q) z = P ʻʻ refs Q z := by
  ext x
  exact ⟨fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩, fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩⟩

private theorem rels_relProd (P : α → β → Prop) (Q : β → γ → Prop) (x : α) :
    rels (P ⨾ Q) x = Q˘ ʻʻ rels P x := by
  ext z
  exact ⟨fun ⟨y, h1, h2⟩ => ⟨y, h1, h2⟩, fun ⟨y, h1, h2⟩ => ⟨y, h1, h2⟩⟩

private theorem img_graph_nonempty (f : β → α) (B : Set β) :
    (graph f ʻʻ B).Nonempty ↔ B.Nonempty :=
  ⟨fun ⟨_, y, hy, _⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨f y, y, hy, rfl⟩⟩

private theorem img3_nonempty (R : α → β → Prop) (K : Set (Set β)) :
    (R ʻʻʻ K).Nonempty ↔ K.Nonempty :=
  img_graph_nonempty (img R) K

/-!
## [✱36] Relations with limited fields

*(Vol. 1, p. 291)*

> *Summary of* *36.
>
> In this number we are concerned with the special case in which the same limitation is imposed upon the domain and the converse domain of a relation. In this case, the same result is achieved by imposing the limitation on the field. It is convenient to be able to regard \(\alpha \upharpoonleft P \upharpoonright \alpha\) as a descriptive function of \(\alpha\) or of \(P\), which we secure by the notation \(P \unicode{x294f} \alpha\), whence, as will be explained in *38, \(P \unicode{x294f} ʻ\alpha\) and \(\unicode{x294f} \alphaʻP\) will both mean \(P \unicode{x294f} \alpha\). If \(P\) is a serial relation, and \(\alpha \subset CʻP\), "\(P \unicode{x294f} \alpha\)" will stand for "the terms of \(\alpha\) arranged in the order determined by \(P\)," or, as we may call it briefly, "\(\alpha\) in the \(P\)-order." \(P\unicode{x294f} \alpha\) is defined as follows:
>
> *36·01. \(P \unicode{x294f} \alpha = \alpha \upharpoonleft P \upharpoonright \alpha \quad \text{Df}\)
>
> We thus have
>
> *36·13. \(\vdash: x (P \unicode{x294f} \alpha) y .\equiv. x,y \in \alpha . x P y\)
>
> …

**Lean reading.** `P ⥏ α` is `P ⥏ A` (`fres`), for a homogeneous relation `P : α → α → Prop`
and `A : Set α`; by the Df ✱36·01 it is `A ◁ P ↾ A` (`bres A P A`), so ✱36·11 and the Df hold by
`rfl`, and `x (P ⥏ α) y` unfolds to `(x ∈ A ∧ P x y) ∧ y ∈ A`. `C'P` is `fld P`, `D'R`, `ᗡ'R` are
`dom R`, `codom R`, `Cnv'P` is `P˘` (`desc_Cnv`), `α ↑ α` is `cross A A`, `Λ̇` is `rNull`. PM's
unbracketed `P ⥏ α ∩̇ Q ⥏ β` parses by the precedences (`⥏` binds tighter than `∩̇`, `∪̇`). The
e-text prints the sign `⥏` (U+294F) in place of PM's `⊂̇` (U+2ABD) in ✱36·22, ✱36·24, ✱36·241 and
✱36·35 (the demonstrations and the cited ✱35·432·462 show an inclusion), and `a` for `α` in
✱36·31; these are read as PM intends. The proofs unfold the definitions.

**Status.** proved (all propositions; ✱36·01 definition; ✱36·22, ✱36·24, ✱36·241, ✱36·31,
✱36·35 proved (reading), transcription errors of the e-text, and ✱36·34 proved (reading), the
bracketing of `Cnv'P⥏α`; see their docstrings).
-/

/-- ✱36·01 (Df). \(P \unicode{x294f} \alpha = \alpha \upharpoonleft P \upharpoonright \alpha \quad \text{Df}\) -/
theorem pm36_01 {P : α → α → Prop} {A : Set α} : P ⥏ A = A ◁ P ↾ A := rfl

/-- ✱36·11. \(\vdash. P \unicode{x294f} \alpha = \alpha \upharpoonleft P \upharpoonright \alpha \quad\text{[(*36·01)]} \) -/
theorem pm36_11 {P : α → α → Prop} {A : Set α} : P ⥏ A = A ◁ P ↾ A := rfl

/-- ✱36·13. \(\vdash: x (P \unicode{x294f} \alpha) y .\equiv. x,y \in \alpha . xPy \quad\text{[*36·11.*35·102]}\) -/
theorem pm36_13 {P : α → α → Prop} {A : Set α} {x y : α} :
    (P ⥏ A) x y ↔ (x ∈ A ∧ y ∈ A) ∧ P x y := by
  simp only [fres, bres]; tauto

/-- ✱36·2. \(\vdash. P \unicode{x294f} \alpha \dot{\cap} Q \unicode{x294f} \beta = (P \dot{\cap} Q) \unicode{x294f} (\alpha \cap \beta) \quad \text{[*35·15]} \) -/
theorem pm36_2 {P Q : α → α → Prop} {A B : Set α} :
    P ⥏ A ⩀ Q ⥏ B = (P ⩀ Q) ⥏ (A ∩ B) := by
  funext x y
  apply propext
  simp only [fres, bres, rcap, Set.mem_inter_iff]
  tauto

/-- ✱36·201. \(\vdash. P \unicode{x294f} \alpha \dot{\cap} P \unicode{x294f} \beta = P \unicode{x294f} (\alpha \cap \beta) \quad \text{[*36·2]} \) -/
theorem pm36_201 {P : α → α → Prop} {A B : Set α} :
    P ⥏ A ⩀ P ⥏ B = P ⥏ (A ∩ B) := by
  funext x y
  apply propext
  simp only [fres, bres, rcap, Set.mem_inter_iff]
  tauto

/-- ✱36·202. \(\vdash. P \unicode{x294f} \alpha \dot{\cap} Q \unicode{x294f} \alpha = (P \dot{\cap} Q) \unicode{x294f} \alpha \quad \text{[*36·2]} \) -/
theorem pm36_202 {P Q : α → α → Prop} {A : Set α} :
    P ⥏ A ⩀ Q ⥏ A = (P ⩀ Q) ⥏ A := by
  funext x y
  apply propext
  simp only [fres, bres, rcap]
  tauto

/-- ✱36·203. \(\vdash. P \unicode{x294f} \alpha \dot{\cap} Q = (P \dot{\cap} Q) \unicode{x294f} \alpha \quad \text{[*35·18]} \) -/
theorem pm36_203 {P Q : α → α → Prop} {A : Set α} :
    P ⥏ A ⩀ Q = (P ⩀ Q) ⥏ A := by
  funext x y
  apply propext
  simp only [fres, bres, rcap]
  tauto

/-- ✱36·21. \(\vdash.(P \unicode{x294f} \alpha) \unicode{x294f} \beta = P \unicode{x294f}(\alpha \cap \beta) \quad \text{[*35·33·34]} \) -/
theorem pm36_21 {P : α → α → Prop} {A B : Set α} :
    (P ⥏ A) ⥏ B = P ⥏ (A ∩ B) := by
  funext x y
  apply propext
  simp only [fres, bres, Set.mem_inter_iff]
  tauto

/-- ✱36·22. \(\vdash.(P\unicode{x0294f}\alpha)\mid (Q\unicode{x0294f}\alpha)\unicode{x0294f}(P\mid Q)\unicode{x0294f}\alpha\)

**Status.** proved (reading): transcription error of the e-text, which prints the sign `⥏`
(U+294F) for PM's `⊂̇` (U+2ABD) between the two sides; the demonstration proves
`x{(P⥏α)|(Q⥏α)}z . ⊃ . x{(P|Q)⥏α}z`, an inclusion `(P⥏α)|(Q⥏α) ⊂̇ (P|Q)⥏α`, which is stated. -/
theorem pm36_22 {P Q : α → α → Prop} {A : Set α} :
    (P ⥏ A) ⨾ (Q ⥏ A) ⪽ (P ⨾ Q) ⥏ A := by
  rintro x z ⟨y, ⟨⟨hx, hxy⟩, _⟩, ⟨⟨_, hyz⟩, hz⟩⟩
  exact ⟨⟨hx, y, hxy, hyz⟩, hz⟩

/-- ✱36·23. \(\vdash.(P\unicode{x228d}Q)\unicode{x0294f}\alpha=P\unicode{x0294f}\alpha\unicode{x228d}Q\unicode{x0294f}\alpha \quad[\text{*35·422}]\) -/
theorem pm36_23 {P Q : α → α → Prop} {A : Set α} :
    (P ⊍ Q) ⥏ A = P ⥏ A ⊍ Q ⥏ A := by
  funext x y
  apply propext
  simp only [fres, bres, rcup]
  tauto

/-- ✱36·24. \(\vdash:\alpha\subset \beta.\supset.P\unicode{x0294f}\alpha\unicode{x0294f}P\unicode{x0294f}\beta \quad[\text{*35·432}]\)

**Status.** proved (reading): transcription error of the e-text, which prints `⥏` (U+294F)
for PM's `⊂̇` (U+2ABD) in the consequent `P⥏α ⊂̇ P⥏β` (the cited ✱35·432 is an inclusion). -/
theorem pm36_24 {P : α → α → Prop} {A B : Set α} : A ⊆ B → P ⥏ A ⪽ P ⥏ B := by
  rintro h x y ⟨⟨hx, hxy⟩, hy⟩
  exact ⟨⟨h hx, hxy⟩, h hy⟩

/-- ✱36·241. \(\vdash:P\unicode{x0294f}Q.\supset.P\unicode{x0294f}\alpha\unicode{x0294f}Q\unicode{x0294f}\alpha \quad[\text{*35·462}]\)

**Status.** proved (reading): transcription error of the e-text, which prints `⥏` (U+294F)
for PM's `⊂̇` (U+2ABD) both in the hypothesis `P ⊂̇ Q` and in the consequent
`P⥏α ⊂̇ Q⥏α` (the cited ✱35·462 is `R ⊂̇ S . ⊃ . α↿R↾β ⊂̇ α↿S↾β`). -/
theorem pm36_241 {P Q : α → α → Prop} {A : Set α} : P ⪽ Q → P ⥏ A ⪽ Q ⥏ A := by
  rintro h x y ⟨⟨hx, hxy⟩, hy⟩
  exact ⟨⟨hx, h x y hxy⟩, hy⟩

/-- ✱36·25. \(\vdash:CʻP\subset \alpha.\equiv.P\unicode{x0294f}\alpha=P\) -/
theorem pm36_25 {P : α → α → Prop} {A : Set α} : fld P ⊆ A ↔ P ⥏ A = P := by
  constructor
  · intro h
    funext x y
    apply propext
    exact ⟨fun hp => hp.1.2, fun hp => ⟨⟨h ⟨y, Or.inl hp⟩, hp⟩, h ⟨x, Or.inr hp⟩⟩⟩
  · rintro h x ⟨y, hxy | hyx⟩
    · exact ((rel_eq_iff.1 h x y).2 hxy).1.1
    · exact ((rel_eq_iff.1 h y x).2 hyx).2

/-- ✱36·26. \(\vdash:CʻP\cap \alpha=\Lambda.\supset.P\mid (Q\unicode{x0294f}\alpha)=\dot{\Lambda}.(Q\unicode{x0294f}\alpha)\mid P=\dot{\Lambda} \quad[\text{*35·473·474}]\) -/
theorem pm36_26 {P Q : α → α → Prop} {A : Set α} :
    fld P ∩ A = Λ → P ⨾ (Q ⥏ A) = rNull ∧ (Q ⥏ A) ⨾ P = rNull := by
  intro h
  constructor
  · funext x z
    apply propext
    refine ⟨?_, fun hn => (rNull_apply _ _ hn).elim⟩
    rintro ⟨y, hxy, ⟨⟨hy, _⟩, _⟩⟩
    exact (not_mem_of_inter_eq_Null h ⟨x, Or.inr hxy⟩ hy).elim
  · funext x z
    apply propext
    refine ⟨?_, fun hn => (rNull_apply _ _ hn).elim⟩
    rintro ⟨y, ⟨⟨_, _⟩, hy⟩, hyz⟩
    exact (not_mem_of_inter_eq_Null h ⟨z, Or.inl hyz⟩ hy).elim

/-- ✱36·27. \(\vdash:P\unicode{x0294f}\Lambda=\dot{\Lambda} \quad[\text{*35·75}]\) -/
theorem pm36_27 {P : α → α → Prop} : P ⥏ Λ = rNull := by
  funext x y
  apply propext
  refine ⟨fun h => ((mem_Null_iff x).1 h.1.1).elim, fun hn => (rNull_apply _ _ hn).elim⟩

/-- ✱36·28. \(\vdash.P\unicode{x0294f}\text{V}=P \quad[\text{*35·76}]\) -/
theorem pm36_28 {P : α → α → Prop} : P ⥏ V = P := by
  funext x y
  apply propext
  exact ⟨fun h => h.1.2, fun h => ⟨⟨rfl, h⟩, rfl⟩⟩

/-- ✱36·29. \(\vdash.P\unicode{x0294f}\alpha=P\dot{\cap}\alpha\uparrow \alpha \quad[\text{*35·822}]\) -/
theorem pm36_29 {P : α → α → Prop} {A : Set α} : P ⥏ A = P ⩀ cross A A := by
  funext x y
  apply propext
  simp only [fres, bres, rcap, cross]
  tauto

/-- ✱36·3. \(\vdash.P\unicode{x0294f}\alpha=P\unicode{x0294f}(\alpha\cap CʻP)\) -/
theorem pm36_3 {P : α → α → Prop} {A : Set α} : P ⥏ A = P ⥏ (A ∩ fld P) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨hx, h⟩, hy⟩
    exact ⟨⟨⟨hx, y, Or.inl h⟩, h⟩, ⟨hy, x, Or.inr h⟩⟩
  · rintro ⟨⟨⟨hx, _⟩, h⟩, ⟨hy, _⟩⟩
    exact ⟨⟨hx, h⟩, hy⟩

/-- ✱36·31. \(\vdash:\alpha\cap CʻP=\Lambda.\supset.P\unicode{x0294f}a=\dot{\Lambda} \quad[\text{*36·3·27}]\)

**Status.** proved (reading): transcription error of the e-text, which prints `P⥏a` for
`P⥏α` in the consequent (with a different class `a` the proposition would be false; the
references ✱36·3·27 concern `α`). -/
theorem pm36_31 {P : α → α → Prop} {A : Set α} : A ∩ fld P = Λ → P ⥏ A = rNull := by
  intro h
  rw [pm36_3, h]
  exact pm36_27

/-- ✱36·32. \(\vdash:\alpha\cap CʻP=\beta\cap CʻP.\supset.P\unicode{x0294f}\alpha=P\unicode{x0294f}\beta \quad[\text{*36·3}]\) -/
theorem pm36_32 {P : α → α → Prop} {A B : Set α} :
    A ∩ fld P = B ∩ fld P → P ⥏ A = P ⥏ B := by
  intro h
  rw [pm36_3, h]
  exact pm36_3.symm

/-- ✱36·33. \(\vdash.P\unicode{x0294f}CʻP=P \quad[\text{*36·25}]\) -/
theorem pm36_33 {P : α → α → Prop} : P ⥏ fld P = P :=
  pm36_25.1 fun _ h => h

/-- ✱36·34. \(\vdash.\text{Cnv}ʻP\unicode{x0294f}\alpha=(\breve{P})\unicode{x0294f}\alpha \quad[\text{*35·53}]\)

`Cnv'Q` is `Q˘` (`desc_Cnv`).

**Status.** proved (reading): the unbracketed `Cnv'P⥏α` is read `Cnv'(P⥏α)`, as the reference
✱35·53 (`Cnv'(α↿R↾β) = β↿R̆↾α`) and the bracket in `(P̆)⥏α` on the right show; the other parse
`(Cnv'P)⥏α` would make the proposition `P̆⥏α = P̆⥏α`. -/
theorem pm36_34 {P : α → α → Prop} {A : Set α} : (P ⥏ A)˘ = P˘ ⥏ A := by
  funext x y
  apply propext
  simp only [fres, bres, cnv]
  tauto

/-- ✱36·35. \(\vdash.(P\unicode{x0294f}\alpha)^{2}\unicode{x0294f}(P^{2})\unicode{x0294f}\alpha \quad[\text{*36·22}]\)

**Status.** proved (reading): transcription error of the e-text, which prints `⥏` (U+294F)
for PM's `⊂̇` (U+2ABD) between `(P⥏α)²` and `(P²)⥏α` (the reference is the inclusion ✱36·22
with `Q = P`). -/
theorem pm36_35 {P : α → α → Prop} {A : Set α} : rsq (P ⥏ A) ⪽ rsq P ⥏ A :=
  pm36_22

/-- ✱36·4. \(\vdash\colon\ldotp \alpha\cap \text{D}ʻR=\Lambda.\lor .\alpha\cap \text{ᗡ}ʻR=\Lambda:\supset.(R\unicode{x228d}S)\unicode{x0294f}\alpha=S\unicode{x0294f}\alpha\) -/
theorem pm36_4 {R S : α → α → Prop} {A : Set α} :
    A ∩ dom R = Λ ∨ A ∩ codom R = Λ → (R ⊍ S) ⥏ A = S ⥏ A := by
  intro h
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨hx, hr | hs⟩, hy⟩
    · rcases h with h | h
      · exact (not_mem_of_inter_eq_Null h hx ⟨y, hr⟩).elim
      · exact (not_mem_of_inter_eq_Null h hy ⟨x, hr⟩).elim
    · exact ⟨⟨hx, hs⟩, hy⟩
  · rintro ⟨⟨hx, hs⟩, hy⟩
    exact ⟨⟨hx, Or.inr hs⟩, hy⟩

/-!
## [✱37] Plural descriptive functions

*(Vol. 1, p. 293)*

> *Summary of* *37.
>
> In this number, we introduce what may be regarded as the plural of \(Rʻy\). "\(Rʻy\)" was defined to mean "the term which has the relation \(R\) to \(y\)." We now introduce the notation "\(Rʻʻ\beta\)" to mean "the terms which have the relation \(R\) to members of \(\beta\)." Thus if \(\beta\) is the class of great men, and \(R\) is the relation of wife to husband, \(Rʻʻ\beta\) will mean "wives of great men." If \(\beta\) is the class of fractions of the form \(1-\tfrac{1}{2}^{n}\) for integral values of \(n\), and \(R\) is the relation "less than," \(Rʻʻ\beta\) will be the class of fractions each of which is less than some member of this class of fractions, *i.e.* \(Rʻʻ\beta\) will be the class of proper fractions. Generally, \(Rʻʻ\beta\) is the class of those referents which have relata that are members of \(\beta\).
>
> We require also a notation for the relation of \(Rʻʻ\beta\) to \(\beta\). This relation we will call \(R_{\in}\). Thus \(R_{\in}\) is the relation which holds between two classes \(\alpha\) and \(\beta\) when \(\alpha\) consists of all terms which have the relation \(R\) to some member of \(\beta\).
>
> …

**Lean reading.** For `R : α → β → Prop` and `B : Set β`, `R''β` is `R ʻʻ B : Set α` (`img`),
`R_∈` is `imgRel R : Set α → Set β → Prop` (`graph (img R)`, so `R_∈'β` always exists and is
`R''β`), `R'''κ` is `R ʻʻʻ K` (`imgRel R ʻʻ K`), `E!!R''β` is `EE R B`, and `R_∈²` is
`imgRelSq R`; the Dfs ✱37·01–✱37·05 and ✱37·371 are their defining equations (✱37·03, whose
definiens is the description `Cnv'R_∈`, is stated with `Desc`). `(R̆)_∈` is `imgRel R˘` (Lean's
postfix `˘` binds tightest), while `R̆_∈` is `imgRelCnv R`; `R̆'''κ` is `R˘ ʻʻʻ K`. A descriptive
function `R'y` of an arbitrary relation is read by `Desc R y ψ` (scope: the smallest proposition
containing it), `E!R'y` by `EDesc R y`, `R'S'y` by `Desc2`, and `E!R'S'z` by
`EBang (fun x => Desc S z (fun w => R x w))` (✱14·02 with ✱30·02). Descriptive functions of
`graph` relations (`D'R`, `ᗡ'R`, `C'R`, `R⃗'y`, `R⃖'x`, `Cnv'P`) are written by their values
(`dom`, `codom`, `fld`, `refs`, `rels`, `˘`), except in ✱37·11–✱37·111 and ✱37·3–✱37·311, whose
content is the value of `R_∈'β`, `sg'(P|Q)`, `gs'(P|Q)`: these keep `Desc`/`EDesc`. In
✱37·3·301 `{sg'(P|Q)}'z` is a description whose relation is itself a description; as in ✱30·02
the inner description `sg'(P|Q)` has the smaller scope. Products `x ∈ α . y ∈ β . xRy` bracket to
the left (✱4·34); chains `A ≡ B ≡ C` are conjunctions of links. Propositions involving both
`R⃗''β` and `R⃖''β`, or both `R'''α` and `R̆'''α`, or `C'R` (✱37·265, ✱37·47, ✱37·73, ✱37·731), are
significant only for a homogeneous `R : α → α → Prop`, which is used there. The proofs unfold
the definitions; under `E!!R''β` they use the unique value of `R'y`.

**Status.** proved (all propositions; ✱37·01–✱37·05 and ✱37·371 definition; ✱37·202, ✱37·29,
✱37·311 proved (reading), transcription errors of the e-text, and ✱37·38 proved (reading), the
notation `R⃗²`; see their docstrings).
-/

/-- ✱37·01 (Df). \(Rʻʻ\beta=\hat{x}\{(\exists y).y\in \beta.xRy\} \quad\text{Df}\) -/
theorem pm37_01 {R : α → β → Prop} {B : Set β} :
    R ʻʻ B = {x | ∃ y, y ∈ B ∧ R x y} := rfl

/-- ✱37·02 (Df). \(R_{\in}=\hat{\alpha}\hat{\beta}(\alpha=Rʻʻ\beta) \quad\text{Df}\) -/
theorem pm37_02 {R : α → β → Prop} : imgRel R = fun A B => A = R ʻʻ B := rfl

/-- ✱37·03 (Df). \(\breve{R}_{\in}=\text{Cnv}ʻR_{\in} \quad\text{Df}\)

The definiens `Cnv'R_∈` is a descriptive function, so the Df is stated with `Desc` (Basic §5):
`R̆_∈` (`imgRelCnv R`) is the value of `Cnv'R_∈`. -/
theorem pm37_03 {R : α → β → Prop} : Desc Cnv (imgRel R) (fun Q => imgRelCnv R = Q) :=
  (desc_Cnv _ _).2 rfl

/-- ✱37·04 (Df). \(Rʻʻʻ\kappa=R_{\in}ʻʻ\kappa \quad\text{Df}\) -/
theorem pm37_04 {R : α → β → Prop} {K : Set (Set β)} : R ʻʻʻ K = imgRel R ʻʻ K := rfl

/-- ✱37·05 (Df). \(\text{E}‼Rʻʻ\beta.=:y\in \beta.\supset_{y}.\text{E}!Rʻy \quad\text{Df}\) -/
theorem pm37_05 {R : α → β → Prop} {B : Set β} : EE R B ↔ ∀ y, y ∈ B → EDesc R y :=
  Iff.rfl

/-- ✱37·1. \(\vdash:x\in Rʻʻ\beta.\equiv.(\exists y).y\in \beta.xRy \quad[\text{*20·3.(*37·01)}]\) -/
theorem pm37_1 {R : α → β → Prop} {B : Set β} {x : α} :
    x ∈ R ʻʻ B ↔ ∃ y, y ∈ B ∧ R x y := Iff.rfl

/-- ✱37·101. \(\vdash:\alpha R_{\in}\beta.\equiv.\alpha=Rʻʻ\beta \quad[\text{*21·3.(*37·02)}]\) -/
theorem pm37_101 {R : α → β → Prop} {A : Set α} {B : Set β} :
    imgRel R A B ↔ A = R ʻʻ B := Iff.rfl

/-- ✱37·102. \(\vdash:\alpha(\breve{R})_{\in}\beta.\equiv.\alpha=\breve{R}ʻʻ\beta \quad[\text{*37·101}]\) -/
theorem pm37_102 {R : α → β → Prop} {A : Set β} {B : Set α} :
    imgRel R˘ A B ↔ A = R˘ ʻʻ B := Iff.rfl

/-- ✱37·103. \[\begin{align}&\vdash:\alpha\in Rʻʻʻ\kappa.\equiv.(\exists \beta).\beta\in \kappa.\alpha=Rʻʻ\beta.\equiv.\alpha\in R_{\in}ʻʻ\kappa\\ &[\text{*37·1·101.(*37·04)}]\end{align}\] -/
theorem pm37_103 {R : α → β → Prop} {A : Set α} {K : Set (Set β)} :
    (A ∈ R ʻʻʻ K ↔ ∃ B, B ∈ K ∧ A = R ʻʻ B) ∧
      ((∃ B, B ∈ K ∧ A = R ʻʻ B) ↔ A ∈ imgRel R ʻʻ K) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ✱37·104. \(\vdash\colon\ldotp \text{E}‼Rʻʻ\beta.\equiv:y\in \beta.\supset_{y}.\text{E}!Rʻy \quad[\text{*4·2.(*37·05)}]\) -/
theorem pm37_104 {R : α → β → Prop} {B : Set β} : EE R B ↔ ∀ y, y ∈ B → EDesc R y :=
  Iff.rfl

/-- ✱37·105. \(\vdash:x\in \breve{R}ʻʻ\beta.\equiv.(\exists y).y\in \beta.yRx \quad[\text{*37·1.*31·11}]\) -/
theorem pm37_105 {R : α → β → Prop} {B : Set α} {x : β} :
    x ∈ R˘ ʻʻ B ↔ ∃ y, y ∈ B ∧ R y x := Iff.rfl

/-- ✱37·106. \(\vdash\colon\ldotp \text{E}!Rʻx.\supset:x\in \breve{R}ʻʻ\beta.\equiv.Rʻx\in \beta\) -/
theorem pm37_106 {R : α → β → Prop} {x : β} {B : Set α} :
    EDesc R x → (x ∈ R˘ ʻʻ B ↔ Desc R x (fun b => b ∈ B)) := by
  rintro ⟨b, hb⟩
  rw [desc_of_unique hb]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [(hb y).1 hyx] at hy
  · intro hbB
    exact ⟨b, hbB, (hb b).2 rfl⟩

/-- ✱37·11. \(\vdash.R_{\in}ʻ\beta=Rʻʻ\beta \quad[\text{*37·101.*30·3}]\)

Stated with `Desc`: the proposition gives the value of the descriptive function `R_∈'β`
(Basic §5). -/
theorem pm37_11 {R : α → β → Prop} {B : Set β} :
    Desc (imgRel R) B (fun A => A = R ʻʻ B) :=
  (desc_of_unique (fun _ => Iff.rfl)).2 rfl

/-- ✱37·111. \(\vdash.\text{E}!R_{\in}ʻ\beta \quad[\text{*37·11.*14·21}]\) -/
theorem pm37_111 {R : α → β → Prop} {B : Set β} : EDesc (imgRel R) B :=
  EDesc_graph (img R) B

/-- ✱37·12. \(\vdash:(\beta).Rʻʻ\beta=Qʻ\beta.\equiv.R_{\in}=Q \quad[\text{*30·42.*37·111·11}]\) -/
theorem pm37_12 {R : α → β → Prop} {Q : Set α → Set β → Prop} :
    (∀ B, Desc Q B (fun A => R ʻʻ B = A)) ↔ imgRel R = Q := by
  constructor
  · intro h
    funext A B
    obtain ⟨b, hb, rfl⟩ := h B
    exact propext (hb A).symm
  · rintro rfl B
    exact (desc_of_unique (fun _ => Iff.rfl)).2 rfl

/-- ✱37·13. \(\vdash:P=Q.\supset.Pʻʻ\beta=Qʻʻ\beta\) -/
theorem pm37_13 {P Q : α → β → Prop} {B : Set β} : P = Q → P ʻʻ B = Q ʻʻ B := by
  rintro rfl; rfl

/-- ✱37·131. \(\vdash:P=Q.\supset.P_{\in}=Q_{\in}\) -/
theorem pm37_131 {P Q : α → β → Prop} : P = Q → imgRel P = imgRel Q := by
  rintro rfl; rfl

/-- ✱37·14. \(\vdash:P=Q.\equiv.P_{\in}=Q_{\in}\) -/
theorem pm37_14 {P Q : α → β → Prop} : P = Q ↔ imgRel P = imgRel Q := by
  refine ⟨pm37_131, fun h => ?_⟩
  funext x w
  have e : imgRel P (P ʻʻ {w}) {w} := rfl
  rw [h] at e
  have hx := Set.ext_iff.1 e x
  apply propext
  constructor
  · intro hp
    obtain ⟨y, hy, hq⟩ := hx.1 ⟨w, rfl, hp⟩
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hq
  · intro hq
    obtain ⟨y, hy, hp⟩ := hx.2 ⟨w, rfl, hq⟩
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hp

/-- ✱37·15. \(\vdash.Rʻʻ\alpha\subset \text{D}ʻR\) -/
theorem pm37_15 {R : α → β → Prop} {A : Set β} : R ʻʻ A ⊆ dom R := by
  rintro x ⟨y, _, h⟩
  exact ⟨y, h⟩

/-- ✱37·16. \(\vdash.\breve{R}ʻʻ\alpha\subset \text{ᗡ}ʻR \quad\left[\text{*37·15}\, \frac{\breve{R}}{R}.\text{*33·2}\right]\) -/
theorem pm37_16 {R : α → β → Prop} {A : Set α} : R˘ ʻʻ A ⊆ codom R := by
  rintro y ⟨x, _, h⟩
  exact ⟨x, h⟩

/-- ✱37·17. \(\vdash\colon\ldotp Rʻʻ\beta\subset \alpha.\equiv:y\in \beta.xRy.\supset_{x,y}.x\in \alpha\) -/
theorem pm37_17 {R : α → β → Prop} {B : Set β} {A : Set α} :
    R ʻʻ B ⊆ A ↔ ∀ x y, y ∈ B ∧ R x y → x ∈ A := by
  constructor
  · rintro h x y ⟨hy, hxy⟩
    exact h ⟨y, hy, hxy⟩
  · rintro h x ⟨y, hy, hxy⟩
    exact h x y ⟨hy, hxy⟩

/-- ✱37·171. \(\vdash\colon\ldotp \breve{R}ʻʻ\alpha\subset \beta.\equiv:x\in \alpha.xRy.\supset_{x,y}.y\in \beta\) -/
theorem pm37_171 {R : α → β → Prop} {A : Set α} {B : Set β} :
    R˘ ʻʻ A ⊆ B ↔ ∀ x y, x ∈ A ∧ R x y → y ∈ B := by
  constructor
  · rintro h x y ⟨hx, hxy⟩
    exact h ⟨x, hx, hxy⟩
  · rintro h y ⟨x, hx, hxy⟩
    exact h x y ⟨hx, hxy⟩

/-- ✱37·18. \(\vdash:y\in \beta.\supset.\overrightarrow{R}ʻy\subset Rʻʻ\beta\) -/
theorem pm37_18 {R : α → β → Prop} {B : Set β} {y : β} : y ∈ B → refs R y ⊆ R ʻʻ B :=
  fun hy _ hx => ⟨y, hy, hx⟩

/-- ✱37·181. \(\vdash:x\in \alpha.\supset.\overleftarrow{R}ʻx\subset \breve{R}ʻʻ\alpha \quad[\text{Proof as in *37·18}]\) -/
theorem pm37_181 {R : α → β → Prop} {A : Set α} {x : α} :
    x ∈ A → rels R x ⊆ R˘ ʻʻ A :=
  fun hx _ hy => ⟨x, hx, hy⟩

/-- ✱37·2. \(\vdash:\alpha\subset \beta.\supset.Pʻʻ\alpha\subset Pʻʻ\beta\) -/
theorem pm37_2 {P : α → β → Prop} {A B : Set β} : A ⊆ B → P ʻʻ A ⊆ P ʻʻ B := by
  rintro h x ⟨y, hy, hxy⟩
  exact ⟨y, h hy, hxy⟩

/-- ✱37·201. \(\vdash:P\unicode{x2abd}Q.\supset.Pʻʻ\alpha\subset Qʻʻ\alpha \quad[\text{Similar proof}]\) -/
theorem pm37_201 {P Q : α → β → Prop} {A : Set β} : P ⪽ Q → P ʻʻ A ⊆ Q ʻʻ A := by
  rintro h x ⟨y, hy, hxy⟩
  exact ⟨y, hy, h x y hxy⟩

/-- ✱37·202. \(\vdash:a\subset \beta.P\unicode{x2abd}Q.\supset.Pʻʻ\alpha\subset Qʻʻ\beta \quad[\text{*37·2·201}]\)

**Status.** proved (reading): transcription error of the e-text, which prints `a ⊂ β` for
`α ⊂ β` in the hypothesis (with a class `a` other than `α` the proposition would be false; the
references ✱37·2·201 concern `α`). -/
theorem pm37_202 {P Q : α → β → Prop} {A B : Set β} :
    A ⊆ B ∧ P ⪽ Q → P ʻʻ A ⊆ Q ʻʻ B :=
  fun ⟨h1, h2⟩ => (pm37_2 h1).trans (pm37_201 h2)

/-- ✱37·21. \(\vdash.Pʻʻ(\alpha\cap \beta)\subset Pʻʻ\alpha\cap Pʻʻ\beta\) -/
theorem pm37_21 {P : α → β → Prop} {A B : Set β} :
    P ʻʻ (A ∩ B) ⊆ P ʻʻ A ∩ P ʻʻ B := by
  rintro x ⟨y, ⟨ha, hb⟩, h⟩
  exact ⟨⟨y, ha, h⟩, ⟨y, hb, h⟩⟩

/-- ✱37·211. \(\vdash.(P\dot{\cap}Q)ʻʻ\alpha\subset Pʻʻ\alpha\cap Qʻʻ\alpha \quad[\text{Similar proof}]\) -/
theorem pm37_211 {P Q : α → β → Prop} {A : Set β} :
    (P ⩀ Q) ʻʻ A ⊆ P ʻʻ A ∩ Q ʻʻ A := by
  rintro x ⟨y, hy, hp, hq⟩
  exact ⟨⟨y, hy, hp⟩, ⟨y, hy, hq⟩⟩

/-- ✱37·212. \(\vdash.(P\dot{\cap}Q)ʻʻ(\alpha\cap \beta)\subset Pʻʻ\alpha\cap Pʻʻ\beta\cap Qʻʻ\alpha\cap Qʻʻ\beta \quad[\text{*37·21·211}]\) -/
theorem pm37_212 {P Q : α → β → Prop} {A B : Set β} :
    (P ⩀ Q) ʻʻ (A ∩ B) ⊆ P ʻʻ A ∩ P ʻʻ B ∩ Q ʻʻ A ∩ Q ʻʻ B := by
  rintro x ⟨y, ⟨ha, hb⟩, hp, hq⟩
  exact ⟨⟨⟨⟨y, ha, hp⟩, ⟨y, hb, hp⟩⟩, ⟨y, ha, hq⟩⟩, ⟨y, hb, hq⟩⟩

/-- ✱37·22. \(\vdash.Pʻʻ(\alpha\cup \beta)=Pʻʻ\alpha\cup Pʻʻ\beta\) -/
theorem pm37_22 {P : α → β → Prop} {A B : Set β} :
    P ʻʻ (A ∪ B) = P ʻʻ A ∪ P ʻʻ B := by
  ext x
  constructor
  · rintro ⟨y, hy | hy, h⟩
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr ⟨y, hy, h⟩
  · rintro (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
    · exact ⟨y, Or.inl hy, h⟩
    · exact ⟨y, Or.inr hy, h⟩

/-- ✱37·221. \(\vdash.(P\unicode{x228d}Q)ʻʻ\alpha=Pʻʻ\alpha\cup Qʻʻ\alpha \quad[\text{Similar proof}]\) -/
theorem pm37_221 {P Q : α → β → Prop} {A : Set β} :
    (P ⊍ Q) ʻʻ A = P ʻʻ A ∪ Q ʻʻ A := by
  ext x
  constructor
  · rintro ⟨y, hy, h | h⟩
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr ⟨y, hy, h⟩
  · rintro (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
    · exact ⟨y, hy, Or.inl h⟩
    · exact ⟨y, hy, Or.inr h⟩

/-- ✱37·222. \(\vdash.(P\unicode{x228d}Q)ʻʻ(\alpha\cup \beta)=Pʻʻ\alpha\cup Pʻʻ\beta\cup Qʻʻ\alpha\cup Qʻʻ\beta \quad[\text{*37·22·221}]\) -/
theorem pm37_222 {P Q : α → β → Prop} {A B : Set β} :
    (P ⊍ Q) ʻʻ (A ∪ B) = P ʻʻ A ∪ P ʻʻ B ∪ Q ʻʻ A ∪ Q ʻʻ B := by
  rw [pm37_221, pm37_22, pm37_22, ← Set.union_assoc]

/-- ✱37·23. \(\vdash.DʻR_{\in}=\hat{\alpha}\{(\exists \beta).\alpha=Rʻʻ\beta\} \quad[\text{*37·101.*33·11}]\) -/
theorem pm37_23 {R : α → β → Prop} : dom (imgRel R) = {A | ∃ B, A = R ʻʻ B} := rfl

/-- ✱37·231. \(\vdash.\text{ᗡ}ʻR_{\in}=\text{Cls}\)

`Cls` is the class of all classes of the type of the members of `ᗡ'R` (PM's note), i.e.
`(Cls : Set (Set β))`. -/
theorem pm37_231 {R : α → β → Prop} : codom (imgRel R) = Cls := by
  rw [Cls_eq_univ]
  exact Set.eq_univ_of_forall fun B => ⟨R ʻʻ B, rfl⟩

/-- ✱37·24. \(\vdash:\alpha\in \text{D}ʻR_{\in}.\supset.\alpha\subset \text{D}ʻR\) -/
theorem pm37_24 {R : α → β → Prop} {A : Set α} : A ∈ dom (imgRel R) → A ⊆ dom R := by
  rintro ⟨B, rfl⟩ x ⟨y, _, h⟩
  exact ⟨y, h⟩

/-- ✱37·25. \(\vdash.\text{D}ʻR=Rʻʻ\text{ᗡ}ʻR.\text{ᗡ}ʻR=\breve{R}ʻʻ\text{D}ʻR\) -/
theorem pm37_25 {R : α → β → Prop} : dom R = R ʻʻ codom R ∧ codom R = R˘ ʻʻ dom R := by
  constructor
  · ext x
    exact ⟨fun ⟨y, h⟩ => ⟨y, ⟨x, h⟩, h⟩, fun ⟨y, _, h⟩ => ⟨y, h⟩⟩
  · ext y
    exact ⟨fun ⟨x, h⟩ => ⟨x, ⟨y, h⟩, h⟩, fun ⟨x, _, h⟩ => ⟨x, h⟩⟩

/-- ✱37·26. \(\vdash.Rʻʻ\beta=Rʻʻ(\beta\cap \text{ᗡ}ʻR)\) -/
theorem pm37_26 {R : α → β → Prop} {B : Set β} : R ʻʻ B = R ʻʻ (B ∩ codom R) := by
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, ⟨hy, x, h⟩, h⟩, fun ⟨y, ⟨hy, _⟩, h⟩ => ⟨y, hy, h⟩⟩

/-- ✱37·261. \(\vdash.\breve{R}ʻʻ\beta=\breve{R}ʻʻ(\beta\cap \text{D}ʻR) \quad[\text{*37·26.*33·21}]\) -/
theorem pm37_261 {R : α → β → Prop} {B : Set α} : R˘ ʻʻ B = R˘ ʻʻ (B ∩ dom R) :=
  pm37_26 (R := R˘)

/-- ✱37·262. \(\vdash:\alpha\cap \text{ᗡ}ʻR=\beta\cap \text{ᗡ}ʻR.\supset.Rʻʻ\alpha=Rʻʻ\beta \quad[\text{*37·26}]\) -/
theorem pm37_262 {R : α → β → Prop} {A B : Set β} :
    A ∩ codom R = B ∩ codom R → R ʻʻ A = R ʻʻ B := by
  intro h
  rw [pm37_26, h]
  exact pm37_26.symm

/-- ✱37·263. \(\vdash:\alpha\cap \text{D}ʻR=\beta\cap \text{D}ʻR.\supset.\breve{R}ʻʻ\alpha=\breve{R}ʻʻ\beta \quad[\text{*37·261}]\) -/
theorem pm37_263 {R : α → β → Prop} {A B : Set α} :
    A ∩ dom R = B ∩ dom R → R˘ ʻʻ A = R˘ ʻʻ B :=
  pm37_262 (R := R˘)

/-- ✱37·264. \(\vdash:\exists !\alpha\cap Rʻʻ\beta.\equiv.(\exists x,y).x\in \alpha.y\in \beta.xRy.\equiv.\exists !\beta\cap \breve{R}ʻʻ\alpha\) -/
theorem pm37_264 {R : α → β → Prop} {A : Set α} {B : Set β} :
    ((A ∩ R ʻʻ B).Nonempty ↔ ∃ x y, (x ∈ A ∧ y ∈ B) ∧ R x y) ∧
      ((∃ x y, (x ∈ A ∧ y ∈ B) ∧ R x y) ↔ (B ∩ R˘ ʻʻ A).Nonempty) := by
  constructor
  · exact ⟨fun ⟨x, hx, y, hy, h⟩ => ⟨x, y, ⟨hx, hy⟩, h⟩,
      fun ⟨x, y, ⟨hx, hy⟩, h⟩ => ⟨x, hx, y, hy, h⟩⟩
  · exact ⟨fun ⟨x, y, ⟨hx, hy⟩, h⟩ => ⟨y, hy, x, hx, h⟩,
      fun ⟨y, hy, x, hx, h⟩ => ⟨x, y, ⟨hx, hy⟩, h⟩⟩

/-- ✱37·265. \(\vdash.Rʻʻ\alpha=Rʻʻ(\alpha\cap CʻR).\breve{R}ʻʻ\alpha=\breve{R}ʻʻ(\alpha\cap CʻR)\) -/
theorem pm37_265 {R : α → α → Prop} {A : Set α} :
    R ʻʻ A = R ʻʻ (A ∩ fld R) ∧ R˘ ʻʻ A = R˘ ʻʻ (A ∩ fld R) := by
  constructor
  · ext x
    exact ⟨fun ⟨y, hy, h⟩ => ⟨y, ⟨hy, x, Or.inr h⟩, h⟩, fun ⟨y, ⟨hy, _⟩, h⟩ => ⟨y, hy, h⟩⟩
  · ext x
    exact ⟨fun ⟨y, hy, h⟩ => ⟨y, ⟨hy, x, Or.inl h⟩, h⟩, fun ⟨y, ⟨hy, _⟩, h⟩ => ⟨y, hy, h⟩⟩

/-- ✱37·27. \(\vdash:\text{ᗡ}ʻR\subset \beta.\supset.\text{D}ʻR=Rʻʻ\beta \quad[\text{*22·621.*37·25·26}]\) -/
theorem pm37_27 {R : α → β → Prop} {B : Set β} : codom R ⊆ B → dom R = R ʻʻ B := by
  intro hs
  ext x
  exact ⟨fun ⟨y, h⟩ => ⟨y, hs ⟨x, h⟩, h⟩, fun ⟨y, _, h⟩ => ⟨y, h⟩⟩

/-- ✱37·271. \(\vdash:\text{D}ʻR\subset \alpha.\supset.\text{ᗡ}ʻR=\breve{R}ʻʻ\alpha \quad[\text{*22·621.*37·25·261}]\) -/
theorem pm37_271 {R : α → β → Prop} {A : Set α} : dom R ⊆ A → codom R = R˘ ʻʻ A :=
  pm37_27 (R := R˘)

/-- ✱37·28. \(\vdash.Rʻʻ\text{V}=\text{D}ʻR.\breve{R}ʻʻ\text{V}=\text{ᗡ}ʻR \quad[\text{*37·27·271.*24·11}]\) -/
theorem pm37_28 {R : α → β → Prop} : R ʻʻ V = dom R ∧ R˘ ʻʻ V = codom R :=
  ⟨(pm37_27 fun y _ => (rfl : y = y)).symm, (pm37_271 fun x _ => (rfl : x = x)).symm⟩

/-- ✱37·29. \(\vdash.Rʻʻ\Lambda=\Lambda.\breve{R}ʻ\Lambda=\Lambda\)

**Status.** proved (reading): transcription error of the e-text, which prints `R̆'Λ` (a
descriptive function, not significant for a relation between individuals) for `R̆''Λ` in the
second conjunct; the demonstration ends with `(2) R̆/R . ⊃ ⊢ . R̆''Λ = Λ`. -/
theorem pm37_29 {R : α → β → Prop} : R ʻʻ Λ = Λ ∧ R˘ ʻʻ Λ = Λ := by
  constructor
  · rw [eq_Null_iff]
    rintro ⟨x, y, hy, _⟩
    exact (mem_Null_iff y).1 hy
  · rw [eq_Null_iff]
    rintro ⟨x, y, hy, _⟩
    exact (mem_Null_iff y).1 hy

/-- ✱37·3. \(\vdash.\{\text{sg}ʻ(P\mid Q)\}ʻz=Pʻʻ\overrightarrow{Q}ʻz\)

`{sg'(P|Q)}'z` is the description `(℩A)(A {sg'(P|Q)} z)`, in which the inner description
`sg'(P|Q)` has the smaller scope (as in ✱30·02); `Q⃗'z` is `refs Q z`. Stated with `Desc`/`TheIs`,
since the proposition gives the value of these descriptive functions. -/
theorem pm37_3 {P : α → β → Prop} {Q : β → γ → Prop} {z : γ} :
    TheIs (fun A => Desc sg (P ⨾ Q) (fun S => S A z)) (fun A => A = P ʻʻ refs Q z) :=
  (TheIs_iff_of_unique (b := refs (P ⨾ Q) z)
    (fun A => desc_graph Rfwd (P ⨾ Q) (fun S => S A z))).2 (refs_relProd P Q z)

/-- ✱37·301. \(\vdash.\{\text{gs}ʻ(P\mid Q)\}ʻx=\breve{Q}ʻʻ\overleftarrow{P}ʻx \quad[\text{Similar proof}]\)

Read as ✱37·3: `{gs'(P|Q)}'x` with the inner description `gs'(P|Q)` of smaller scope;
`P⃖'x` is `rels P x`. -/
theorem pm37_301 {P : α → β → Prop} {Q : β → γ → Prop} {x : α} :
    TheIs (fun B => Desc gs (P ⨾ Q) (fun S => S B x)) (fun B => B = Q˘ ʻʻ rels P x) :=
  (TheIs_iff_of_unique (b := rels (P ⨾ Q) x)
    (fun B => desc_graph Rbwd (P ⨾ Q) (fun S => S B x))).2 (rels_relProd P Q x)

/-- ✱37·302. \[\begin{align}&\vdash:R=P\mid Q.\supset.\overrightarrow{R}ʻz=Pʻʻ\overrightarrow{Q}ʻz.\overleftarrow{R}ʻx=\breve{Q}ʻʻ\overleftarrow{P}ʻx\\ &[\text{*37·3·301.*32·23·231·16}]\end{align}\] -/
theorem pm37_302 {R : α → γ → Prop} {P : α → β → Prop} {Q : β → γ → Prop} {z : γ} {x : α} :
    R = P ⨾ Q → refs R z = P ʻʻ refs Q z ∧ rels R x = Q˘ ʻʻ rels P x := by
  rintro rfl
  exact ⟨refs_relProd P Q z, rels_relProd P Q x⟩

/-- ✱37·31. \(\vdash.\text{sg}ʻ(P\mid Q)=P_{\in}\mid \overrightarrow{Q}\)

Stated with `Desc`, since the proposition gives the value of `sg'(P|Q)`. -/
theorem pm37_31 {P : α → β → Prop} {Q : β → γ → Prop} :
    Desc sg (P ⨾ Q) (fun S => S = imgRel P ⨾ Rfwd Q) := by
  refine (desc_graph Rfwd (P ⨾ Q) _).2 ?_
  funext A z
  apply propext
  show A = refs (P ⨾ Q) z ↔ ∃ B, A = P ʻʻ B ∧ B = refs Q z
  rw [refs_relProd]
  constructor
  · rintro rfl
    exact ⟨refs Q z, rfl, rfl⟩
  · rintro ⟨B, rfl, rfl⟩
    rfl

/-- ✱37·311. \(\vdash.\text{gs}ʻ(P\mid Q)=(\breve{Q}_{\in}\mid \overleftarrow{P} \quad[\text{Similar proof}]\)

Stated with `Desc`, as ✱37·31.

**Status.** proved (reading): transcription error of the e-text, which prints
`(\breve{Q}_{\in} | P⃖` with an unclosed bracket; PM's formula is `gs'(P|Q) = (Q̆)_∈ | P⃖` (the
analogue of ✱37·31 by "similar proof", since `{gs'(P|Q)}'x = Q̆''P⃖'x` by ✱37·301). By ✱37·03
`Q̆_∈` without the bracket would be `Cnv'Q_∈`, which is not meant. -/
theorem pm37_311 {P : α → β → Prop} {Q : β → γ → Prop} :
    Desc gs (P ⨾ Q) (fun S => S = imgRel Q˘ ⨾ Rbwd P) := by
  refine (desc_graph Rbwd (P ⨾ Q) _).2 ?_
  funext B x
  apply propext
  show B = rels (P ⨾ Q) x ↔ ∃ C, B = Q˘ ʻʻ C ∧ C = rels P x
  rw [rels_relProd]
  constructor
  · rintro rfl
    exact ⟨rels P x, rfl, rfl⟩
  · rintro ⟨C, rfl, rfl⟩
    rfl

/-- ✱37·32. \(\vdash.\text{D}ʻ(P\mid Q)=Pʻʻ\text{D}ʻQ. \text{ᗡ}ʻ(P\mid Q)=\breve{Q}ʻʻ\text{ᗡ}ʻP\) -/
theorem pm37_32 {P : α → β → Prop} {Q : β → γ → Prop} :
    dom (P ⨾ Q) = P ʻʻ dom Q ∧ codom (P ⨾ Q) = Q˘ ʻʻ codom P := by
  constructor
  · ext x
    exact ⟨fun ⟨z, y, hxy, hyz⟩ => ⟨y, ⟨z, hyz⟩, hxy⟩, fun ⟨y, ⟨z, hyz⟩, hxy⟩ => ⟨z, y, hxy, hyz⟩⟩
  · ext z
    exact ⟨fun ⟨x, y, hxy, hyz⟩ => ⟨y, ⟨x, hxy⟩, hyz⟩, fun ⟨y, ⟨x, hxy⟩, hyz⟩ => ⟨x, y, hxy, hyz⟩⟩

/-- ✱37·321. \(\vdash:\text{ᗡ}ʻP\subset\text{D}ʻQ.\supset.\text{D}ʻ(P\mid Q)=\text{D}ʻP \quad[\text{*37·32·27}]\) -/
theorem pm37_321 {P : α → β → Prop} {Q : β → γ → Prop} :
    codom P ⊆ dom Q → dom (P ⨾ Q) = dom P := by
  intro hs
  rw [pm37_32.1]
  ext x
  exact ⟨fun ⟨y, _, h⟩ => ⟨y, h⟩, fun ⟨y, h⟩ => ⟨y, hs ⟨x, h⟩, h⟩⟩

/-- ✱37·322. \(\vdash:\text{D}ʻQ\subset\text{ᗡ}ʻP.\supset.\text{ᗡ}ʻ(P\mid Q)=\text{ᗡ}ʻQ \quad[\text{*37·32·271}]\) -/
theorem pm37_322 {P : α → β → Prop} {Q : β → γ → Prop} :
    dom Q ⊆ codom P → codom (P ⨾ Q) = codom Q := by
  intro hs
  rw [pm37_32.2]
  ext z
  exact ⟨fun ⟨y, _, h⟩ => ⟨y, h⟩, fun ⟨y, h⟩ => ⟨y, hs ⟨z, h⟩, h⟩⟩

/-- ✱37·323. \(\vdash:\text{ᗡ}ʻP=\text{D}ʻQ.\supset.\text{D}ʻ(P\mid Q)=\text{D}ʻP.\text{ᗡ}ʻ(P\mid Q)=\text{ᗡ}ʻQ \quad[\text{*37·321·322}]\) -/
theorem pm37_323 {P : α → β → Prop} {Q : β → γ → Prop} :
    codom P = dom Q → dom (P ⨾ Q) = dom P ∧ codom (P ⨾ Q) = codom Q := by
  intro h
  exact ⟨pm37_321 (h ▸ fun _ hy => hy), pm37_322 (h ▸ fun _ hy => hy)⟩

/-- ✱37·33. \(\vdash.(P\mid Q)ʻʻ\gamma=PʻʻQʻʻ\gamma\) -/
theorem pm37_33 {P : α → β → Prop} {Q : β → γ → Prop} {G : Set γ} :
    (P ⨾ Q) ʻʻ G = P ʻʻ Q ʻʻ G := by
  ext x
  exact ⟨fun ⟨z, hz, y, hxy, hyz⟩ => ⟨y, ⟨z, hz, hyz⟩, hxy⟩,
    fun ⟨y, ⟨z, hz, hyz⟩, hxy⟩ => ⟨z, hz, y, hxy, hyz⟩⟩

/-- ✱37·34. \(\vdash.(P\mid Q)_{\in}=P_{\in}\mid Q_{\in}\) -/
theorem pm37_34 {P : α → β → Prop} {Q : β → γ → Prop} :
    imgRel (P ⨾ Q) = imgRel P ⨾ imgRel Q := by
  funext A G
  apply propext
  constructor
  · rintro rfl
    exact ⟨Q ʻʻ G, pm37_33, rfl⟩
  · rintro ⟨B, rfl, rfl⟩
    exact pm37_33.symm

/-- ✱37·341. \(\vdash.{\text{Cnv}ʻ(P\mid Q)}_{\in}=(\breve{Q})_{\in}\mid (\breve{P})_{\in} \quad[\text{*34·2.*37·34}]\)

`Cnv'(P|Q)` is `(P ⨾ Q)˘` (`desc_Cnv`). -/
theorem pm37_341 {P : α → β → Prop} {Q : β → γ → Prop} :
    imgRel (P ⨾ Q)˘ = imgRel Q˘ ⨾ imgRel P˘ := by
  have e : (P ⨾ Q)˘ = Q˘ ⨾ P˘ := by
    funext z x
    apply propext
    exact ⟨fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩, fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩⟩
  rw [e]
  exact pm37_34

/-- ✱37·35. \(\vdash:(z).Rʻz=PʻQʻz.\supset.(\gamma).Rʻʻ\gamma=PʻʻQʻʻ\gamma\)

`R'z = P'Q'z` has two descriptions, the first (`R'z`) with the larger scope (✱14·03), and
`P'Q'z` is read by ✱30·02 (`Desc2`). -/
theorem pm37_35 {R : α → γ → Prop} {P : α → β → Prop} {Q : β → γ → Prop} :
    (∀ z, Desc R z (fun a => Desc2 P Q z (fun b => a = b))) → ∀ G, R ʻʻ G = P ʻʻ Q ʻʻ G := by
  intro h G
  have e : R = P ⨾ Q := by
    funext x z
    obtain ⟨a, ha, hd⟩ := h z
    obtain ⟨b, hb, rfl⟩ := relProd_of_desc2 hd
    exact propext ((ha x).trans (hb x).symm)
  rw [e]
  exact pm37_33

/-- ✱37·351. \[\begin{align}&\vdash:(\alpha).Rʻ\alpha=PʻQʻʻ\alpha.\supset.(\kappa).Rʻʻ\kappa=PʻʻQʻʻʻ\kappa\\ &\left[\text{*37·35} \frac{Q_{\in}}{Q}.\text{*37·11.(*37·04)}\right]\end{align}\] -/
theorem pm37_351 {R : δ → Set γ → Prop} {P : δ → Set β → Prop} {Q : β → γ → Prop} :
    (∀ A, Desc R A (fun a => Desc P (Q ʻʻ A) (fun b => a = b))) →
      ∀ K, R ʻʻ K = P ʻʻ Q ʻʻʻ K := by
  intro h K
  ext x
  constructor
  · rintro ⟨A, hA, hx⟩
    exact ⟨Q ʻʻ A, ⟨A, hA, rfl⟩, (rel_iff_of_desc_eq (h A) x).1 hx⟩
  · rintro ⟨B, ⟨A, hA, rfl⟩, hx⟩
    exact ⟨A, hA, (rel_iff_of_desc_eq (h A) x).2 hx⟩

/-- ✱37·352. \[\begin{align}&\vdash:(\alpha).Rʻʻ\alpha=PʻQʻʻ\alpha.\supset.(\kappa).Rʻʻʻ\kappa=PʻʻQʻʻʻ\kappa\\ &\left[\text{*37·351}\, \frac{R_{\in}}{R}.\text{*37·11.(*37·04)}\right]\end{align}\] -/
theorem pm37_352 {R : α → γ → Prop} {P : Set α → Set β → Prop} {Q : β → γ → Prop} :
    (∀ A, Desc P (Q ʻʻ A) (fun b => R ʻʻ A = b)) → ∀ K, R ʻʻʻ K = P ʻʻ Q ʻʻʻ K := by
  intro h K
  have hP : ∀ A X, P X (Q ʻʻ A) ↔ X = R ʻʻ A := by
    intro A X
    obtain ⟨b, hb, hRb⟩ := h A
    subst hRb
    exact hb X
  ext X
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨Q ʻʻ A, ⟨A, hA, rfl⟩, (hP A _).2 rfl⟩
  · rintro ⟨B, ⟨A, hA, rfl⟩, hX⟩
    exact ⟨A, hA, (hP A X).1 hX⟩

/-- ✱37·353. \(\vdash:(z).RʻSʻz=PʻQʻz.\supset.(\gamma).RʻʻSʻʻ\gamma=PʻʻQʻʻ\gamma\) -/
theorem pm37_353 {R : α → β → Prop} {S : β → γ → Prop} {P : α → δ → Prop}
    {Q : δ → γ → Prop} :
    (∀ z, Desc2 R S z (fun a => Desc2 P Q z (fun b => a = b))) →
      ∀ G, R ʻʻ S ʻʻ G = P ʻʻ Q ʻʻ G := by
  intro h G
  have e : R ⨾ S = P ⨾ Q := by
    funext x z
    obtain ⟨a, ha, hd⟩ := relProd_of_desc2 (h z)
    obtain ⟨b, hb, rfl⟩ := relProd_of_desc2 hd
    exact propext ((ha x).trans (hb x).symm)
  rw [← pm37_33, e, pm37_33]

/-- ✱37·354. \(\vdash.(\alpha).RʻSʻ\alpha=PʻQʻʻ\alpha.\supset.(\kappa).RʻʻSʻʻ\kappa=PʻʻQʻʻʻ\kappa \quad\left[\text{*37·353}\, \frac{Q_{\in}}{Q}\right]\) -/
theorem pm37_354 {R : α → β → Prop} {S : β → Set γ → Prop} {P : α → Set δ → Prop}
    {Q : δ → γ → Prop} :
    (∀ A, Desc2 R S A (fun a => Desc P (Q ʻʻ A) (fun b => a = b))) →
      ∀ K, R ʻʻ S ʻʻ K = P ʻʻ Q ʻʻʻ K := by
  intro h K
  have e : R ⨾ S = P ⨾ imgRel Q := by
    funext x A
    obtain ⟨a, ha, b, hb, rfl⟩ := relProd_of_desc2 (h A)
    apply propext
    rw [ha x]
    constructor
    · intro hx
      exact ⟨Q ʻʻ A, (hb x).2 hx, rfl⟩
    · rintro ⟨B, hB, rfl⟩
      exact (hb x).1 hB
  rw [← pm37_33, e, pm37_33]
  rfl

/-- ✱37·355. \(\vdash:(z).RʻSʻz=PʻʻQʻz.\supset.(\gamma).RʻʻSʻʻ\gamma=PʻʻʻQʻʻ\gamma \quad\left[\text{*37·353}\, \frac{P_{\in}}{P}\right]\)

`R'S'z = P''Q'z`: the descriptions `R'S'z` (✱30·02) and `Q'z`, the first with the larger
scope. -/
theorem pm37_355 {R : Set α → β → Prop} {S : β → γ → Prop} {P : α → δ → Prop}
    {Q : Set δ → γ → Prop} :
    (∀ z, Desc2 R S z (fun a => Desc Q z (fun b => a = P ʻʻ b))) →
      ∀ G, R ʻʻ S ʻʻ G = P ʻʻʻ Q ʻʻ G := by
  intro h G
  have e : R ⨾ S = imgRel P ⨾ Q := by
    funext X z
    obtain ⟨a, ha, c, hc, rfl⟩ := relProd_of_desc2 (h z)
    apply propext
    rw [ha X]
    constructor
    · rintro rfl
      exact ⟨c, rfl, (hc c).2 rfl⟩
    · rintro ⟨B, rfl, hB⟩
      rw [(hc B).1 hB]
  rw [← pm37_33, e, pm37_33]
  rfl

/-- ✱37·36. \(\vdash.\text{D}ʻR^{2}=Rʻʻ\text{D}ʻR.\text{ᗡ}ʻR^{2}=\breve{R}ʻʻ\text{ᗡ}ʻR \quad[\text{*37·32}]\) -/
theorem pm37_36 {R : α → α → Prop} :
    dom (rsq R) = R ʻʻ dom R ∧ codom (rsq R) = R˘ ʻʻ codom R :=
  pm37_32

/-- ✱37·37. \(\vdash.(R^{2})_{\in}=(R_{\in})^{2} \quad[\text{*37·34}]\) -/
theorem pm37_37 {R : α → α → Prop} : imgRel (rsq R) = rsq (imgRel R) :=
  pm37_34

/-- ✱37·371 (Df). \(R_{\in}^{2}=(R_{\in})^{2} \quad\text{Df}\) -/
theorem pm37_371 {R : α → α → Prop} : imgRelSq R = rsq (imgRel R) := rfl

/-- ✱37·38. \(\vdash.\overrightarrow{R}^{2}ʻx=Rʻʻ\overrightarrow{R}ʻx \quad[\text{*37·3}]\)

**Status.** proved (reading): `R⃗²'x` is read `(R²)⃗'x`, i.e. `refs (rsq R) x`, since the square
of `R⃗ : Set α → α → Prop` is not significant; the reference is ✱37·3 with `P = Q = R`
(`sg'(R|R) = (R²)⃗`), and ✱91 uses `F⃗²'P = F''F⃗'P` the same way. -/
theorem pm37_38 {R : α → α → Prop} {x : α} : refs (rsq R) x = R ʻʻ refs R x :=
  refs_relProd R R x

/-- ✱37·39. \(\vdash.R^{2}ʻʻ\alpha=RʻʻRʻʻ\alpha \quad[\text{*37·33}]\) -/
theorem pm37_39 {R : α → α → Prop} {A : Set α} : rsq R ʻʻ A = R ʻʻ R ʻʻ A :=
  pm37_33

/-- ✱37·4. \(\vdash.\text{ᗡ}ʻ(\alpha\upharpoonleft R)=\breve{R}ʻʻ\alpha\) -/
theorem pm37_4 {R : α → β → Prop} {A : Set α} : codom (A ◁ R) = R˘ ʻʻ A := rfl

/-- ✱37·401. \(\vdash.\text{D}ʻ(R\upharpoonright \beta)=Rʻʻ\beta \quad[\text{Similar proof}]\) -/
theorem pm37_401 {R : α → β → Prop} {B : Set β} : dom (R ↾ B) = R ʻʻ B := by
  ext x
  exact ⟨fun ⟨y, h, hy⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, h, hy⟩⟩

/-- ✱37·402. \(\vdash.\text{D}ʻ(\alpha\upharpoonleft R\upharpoonright \beta)=\alpha\cap Rʻʻ\beta.\text{ᗡ}ʻ(\alpha\upharpoonleft R\upharpoonright \beta)=\beta\cap \breve{R}ʻʻ\alpha\) -/
theorem pm37_402 {R : α → β → Prop} {A : Set α} {B : Set β} :
    dom (A ◁ R ↾ B) = A ∩ R ʻʻ B ∧ codom (A ◁ R ↾ B) = B ∩ R˘ ʻʻ A := by
  constructor
  · ext x
    exact ⟨fun ⟨y, ⟨hx, h⟩, hy⟩ => ⟨hx, y, hy, h⟩, fun ⟨hx, y, hy, h⟩ => ⟨y, ⟨hx, h⟩, hy⟩⟩
  · ext y
    exact ⟨fun ⟨x, ⟨hx, h⟩, hy⟩ => ⟨hy, x, hx, h⟩, fun ⟨hy, x, hx, h⟩ => ⟨x, ⟨hx, h⟩, hy⟩⟩

/-- ✱37·41. \(\vdash.\text{D}ʻ(R\unicode{x0294f}\alpha)=\alpha\cap Rʻʻ\alpha.\text{ᗡ}ʻ(R\unicode{x0294f}\alpha)=\alpha\cap \breve{R}ʻʻ\alpha \quad[\text{*37·402.*36·11}]\) -/
theorem pm37_41 {R : α → α → Prop} {A : Set α} :
    dom (R ⥏ A) = A ∩ R ʻʻ A ∧ codom (R ⥏ A) = A ∩ R˘ ʻʻ A :=
  pm37_402

/-- ✱37·411. \(\vdash.(\alpha\upharpoonleft R)ʻʻ\beta=\text{D}ʻ(\alpha\upharpoonleft R\upharpoonright \beta)=\alpha\cap Rʻʻ\beta\) -/
theorem pm37_411 {R : α → β → Prop} {A : Set α} {B : Set β} :
    (A ◁ R) ʻʻ B = dom (A ◁ R ↾ B) ∧ dom (A ◁ R ↾ B) = A ∩ R ʻʻ B := by
  refine ⟨?_, pm37_402.1⟩
  ext x
  exact ⟨fun ⟨y, hy, hx, h⟩ => ⟨y, ⟨hx, h⟩, hy⟩, fun ⟨y, ⟨hx, h⟩, hy⟩ => ⟨y, hy, hx, h⟩⟩

/-- ✱37·412. \(\vdash.(R\upharpoonright \alpha)ʻʻ\beta=Rʻʻ(\alpha\cap \beta)\) -/
theorem pm37_412 {R : α → β → Prop} {A B : Set β} : (R ↾ A) ʻʻ B = R ʻʻ (A ∩ B) := by
  ext x
  exact ⟨fun ⟨y, hb, h, ha⟩ => ⟨y, ⟨ha, hb⟩, h⟩, fun ⟨y, ⟨ha, hb⟩, h⟩ => ⟨y, hb, h, ha⟩⟩

/-- ✱37·413. \(\vdash.(R\unicode{x0294f}\alpha)ʻʻ\beta=\alpha\cap Rʻʻ(\alpha\cap \beta)\) -/
theorem pm37_413 {R : α → α → Prop} {A B : Set α} :
    (R ⥏ A) ʻʻ B = A ∩ R ʻʻ (A ∩ B) := by
  ext x
  exact ⟨fun ⟨y, hb, ⟨hx, h⟩, ha⟩ => ⟨hx, y, ⟨ha, hb⟩, h⟩,
    fun ⟨hx, y, ⟨ha, hb⟩, h⟩ => ⟨y, hb, ⟨hx, h⟩, ha⟩⟩

/-- ✱37·42. \(\vdash:Rʻʻ\beta\subset \alpha.\supset.(\alpha\upharpoonleft R)ʻʻ\beta=Rʻʻ\beta \quad[\text{*37·411.*22·621}]\) -/
theorem pm37_42 {R : α → β → Prop} {A : Set α} {B : Set β} :
    R ʻʻ B ⊆ A → (A ◁ R) ʻʻ B = R ʻʻ B := by
  intro hs
  ext x
  exact ⟨fun ⟨y, hy, _, h⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, hs ⟨y, hy, h⟩, h⟩⟩

/-- ✱37·421. \(\vdash:\beta\subset \alpha.\supset.(R\upharpoonright \alpha)ʻʻ\beta=Rʻʻ\beta \quad[\text{*37·412.*22·621}]\) -/
theorem pm37_421 {R : α → β → Prop} {A B : Set β} :
    B ⊆ A → (R ↾ A) ʻʻ B = R ʻʻ B := by
  intro hs
  ext x
  exact ⟨fun ⟨y, hy, h, _⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h, hs hy⟩⟩

/-- ✱37·43. \(\vdash\colon\ldotp \beta\subset \text{ᗡ}ʻR.\supset:\exists !Rʻʻ\beta.\equiv.\exists !\beta\) -/
theorem pm37_43 {R : α → β → Prop} {B : Set β} :
    B ⊆ codom R → ((R ʻʻ B).Nonempty ↔ B.Nonempty) := by
  intro hs
  constructor
  · rintro ⟨x, y, hy, _⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, h⟩ := hs hy
    exact ⟨x, y, hy, h⟩

/-- ✱37·431. \(\vdash\colon\ldotp \alpha\subset \text{D}ʻR.\supset:\exists !\breve{R}ʻʻ\alpha.\equiv.\exists !\alpha \quad[\text{Proof as in *37·43}]\) -/
theorem pm37_431 {R : α → β → Prop} {A : Set α} :
    A ⊆ dom R → ((R˘ ʻʻ A).Nonempty ↔ A.Nonempty) :=
  pm37_43 (R := R˘)

/-- ✱37·44. \(\vdash\colon\ldotp \text{ᗡ}ʻR=V.\supset:\exists !Rʻʻ\beta.\equiv.\exists !\beta \quad[\text{*37·43.*24·11}]\) -/
theorem pm37_44 {R : α → β → Prop} {B : Set β} :
    codom R = V → ((R ʻʻ B).Nonempty ↔ B.Nonempty) := by
  intro h
  exact pm37_43 (by rw [h]; exact fun y _ => (rfl : y = y))

/-- ✱37·441. \(\vdash\colon\ldotp \text{D}ʻR=V.\supset:\exists !\breve{R}ʻʻ\alpha.\equiv.\exists !\alpha \quad[\text{Proof as in *37·44}]\) -/
theorem pm37_441 {R : α → β → Prop} {A : Set α} :
    dom R = V → ((R˘ ʻʻ A).Nonempty ↔ A.Nonempty) :=
  pm37_44 (R := R˘)

/-- ✱37·45. \(\vdash\colon\ldotp (y).\text{E}!Rʻy.\supset:\exists !Rʻʻ\beta.\equiv.\exists !\beta \quad[\text{*33·431.*37·43}]\) -/
theorem pm37_45 {R : α → β → Prop} {B : Set β} :
    (∀ y, EDesc R y) → ((R ʻʻ B).Nonempty ↔ B.Nonempty) := by
  intro h
  refine pm37_43 fun y _ => ?_
  obtain ⟨b, hb⟩ := h y
  exact ⟨b, (hb b).2 rfl⟩

/-- ✱37·451. \(\vdash\colon\ldotp (x).\text{E}!\breve{R}ʻx.\supset:\exists !\breve{R}ʻʻ\alpha.\equiv.\exists !\alpha \quad[\text{Proof as in *37·45}]\) -/
theorem pm37_451 {R : α → β → Prop} {A : Set α} :
    (∀ x, EDesc R˘ x) → ((R˘ ʻʻ A).Nonempty ↔ A.Nonempty) :=
  pm37_45 (R := R˘)

/-- ✱37·46. \(\vdash:x\in Rʻʻ\alpha.\equiv.\exists !\alpha\cap \overleftarrow{R}ʻx \quad[\text{*37·1.*32·181}]\) -/
theorem pm37_46 {R : α → β → Prop} {A : Set β} {x : α} :
    x ∈ R ʻʻ A ↔ (A ∩ rels R x).Nonempty := Iff.rfl

/-- ✱37·461. \(\vdash:x{\sim}\in Rʻʻ\alpha.\equiv.\alpha\cap \overleftarrow{R}ʻx=\Lambda.\equiv.\overleftarrow{R}ʻx\subset -\alpha \quad[\text{*37·46.*24·311}]\) -/
theorem pm37_461 {R : α → β → Prop} {A : Set β} {x : α} :
    (x ∉ R ʻʻ A ↔ A ∩ rels R x = Λ) ∧ (A ∩ rels R x = Λ ↔ rels R x ⊆ Aᶜ) := by
  constructor
  · rw [eq_Null_iff, pm37_46]
  · rw [eq_Null_iff]
    constructor
    · intro h y hy hyA
      exact h ⟨y, hyA, hy⟩
    · rintro h ⟨y, hyA, hy⟩
      exact h hy hyA

/-- ✱37·462. \(\vdash:x{\sim}\in \breve{R}ʻʻ\alpha.\equiv.\alpha\cap \overrightarrow{R}ʻx=\Lambda.\equiv.\overrightarrow{R}ʻx\subset -\alpha \quad[\text{*37·461.*32·241}]\) -/
theorem pm37_462 {R : α → β → Prop} {A : Set α} {x : β} :
    (x ∉ R˘ ʻʻ A ↔ A ∩ refs R x = Λ) ∧ (A ∩ refs R x = Λ ↔ refs R x ⊆ Aᶜ) :=
  pm37_461 (R := R˘)

/-- ✱37·47. \(\vdash:\exists !\alpha.\equiv.\exists !Rʻʻʻ\alpha.\equiv.\exists !\breve{R}ʻʻʻ\alpha\) -/
theorem pm37_47 {R : α → α → Prop} {K : Set (Set α)} :
    (K.Nonempty ↔ (R ʻʻʻ K).Nonempty) ∧ ((R ʻʻʻ K).Nonempty ↔ (R˘ ʻʻʻ K).Nonempty) := by
  rw [img3_nonempty, img3_nonempty]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- ✱37·5. \(\vdash:(\beta).Pʻʻ\beta=Qʻ\beta.\supset.(\kappa).Pʻʻʻ\kappa=Qʻʻ\kappa\) -/
theorem pm37_5 {P : α → β → Prop} {Q : Set α → Set β → Prop} :
    (∀ B, Desc Q B (fun A => P ʻʻ B = A)) → ∀ K, P ʻʻʻ K = Q ʻʻ K := by
  intro h K
  rw [← pm37_12.1 h]
  rfl

/-- ✱37·501. \(\vdash.\beta\cap \text{ᗡ}ʻR\subset \breve{R}ʻʻRʻʻ\beta\) -/
theorem pm37_501 {R : α → β → Prop} {B : Set β} : B ∩ codom R ⊆ R˘ ʻʻ R ʻʻ B := by
  rintro y ⟨hy, x, hx⟩
  exact ⟨x, ⟨y, hy, hx⟩, hx⟩

/-- ✱37·502. \(\vdash.\alpha\cap \text{D}ʻR\subset Rʻʻ\breve{R}ʻʻ\alpha \quad[\text{Similar proof}]\) -/
theorem pm37_502 {R : α → β → Prop} {A : Set α} : A ∩ dom R ⊆ R ʻʻ R˘ ʻʻ A :=
  pm37_501 (R := R˘)

/-- ✱37·51. \(\vdash:\beta\subset \text{ᗡ}ʻR.\equiv.\beta\subset \breve{R}ʻʻRʻʻ\beta\) -/
theorem pm37_51 {R : α → β → Prop} {B : Set β} : B ⊆ codom R ↔ B ⊆ R˘ ʻʻ R ʻʻ B :=
  ⟨fun h _ hy => pm37_501 ⟨hy, h hy⟩, fun h _ hy => pm37_16 (h hy)⟩

/-- ✱37·52. \(\vdash:\alpha\subset \text{D}ʻR.\equiv.\alpha\subset Rʻʻ\breve{R}ʻʻ\alpha \quad[\text{Similar proof}]\) -/
theorem pm37_52 {R : α → β → Prop} {A : Set α} : A ⊆ dom R ↔ A ⊆ R ʻʻ R˘ ʻʻ A :=
  pm37_51 (R := R˘)

/-- ✱37·6. \(\vdash:\text{E}‼Rʻʻ\beta.\supset.Rʻʻ\beta=\hat{x}\{(\exists y).y\in \beta.x=Rʻy\}\) -/
theorem pm37_6 {R : α → β → Prop} {B : Set β} :
    EE R B → R ʻʻ B = {x | ∃ y, y ∈ B ∧ Desc R y (fun b => x = b)} := by
  intro h
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨b, hb⟩ := h y hy
    exact ⟨y, hy, (desc_of_unique hb).2 ((hb x).1 hxy)⟩
  · rintro ⟨y, hy, hd⟩
    obtain ⟨b, hb⟩ := h y hy
    exact ⟨y, hy, (hb x).2 ((desc_of_unique hb).1 hd)⟩

/-- ✱37·601. \(\vdash:(x).\text{E}!Rʻx.\supset.Rʻʻ\text{V}=\hat{x}\{(\exists y).x=Rʻy\}\) -/
theorem pm37_601 {R : α → β → Prop} :
    (∀ x, EDesc R x) → R ʻʻ V = {x | ∃ y, Desc R y (fun b => x = b)} := by
  intro h
  rw [pm37_6 fun y _ => h y]
  ext x
  exact ⟨fun ⟨y, _, d⟩ => ⟨y, d⟩, fun ⟨y, d⟩ => ⟨y, rfl, d⟩⟩

/-- ✱37·61. \(\vdash\colon\colon \text{E}‼Rʻʻ\beta.\supset\colon\ldotp Rʻʻ\beta\subset\alpha.\equiv:y\in \beta.\supset_{y}.Rʻy\in \alpha\) -/
theorem pm37_61 {R : α → β → Prop} {B : Set β} {A : Set α} :
    EE R B → (R ʻʻ B ⊆ A ↔ ∀ y, y ∈ B → Desc R y (fun b => b ∈ A)) := by
  intro h
  constructor
  · intro hs y hy
    obtain ⟨b, hb⟩ := h y hy
    exact (desc_of_unique hb).2 (hs ⟨y, hy, (hb b).2 rfl⟩)
  · rintro hd x ⟨y, hy, hxy⟩
    obtain ⟨b, hb⟩ := h y hy
    rw [(hb x).1 hxy]
    exact (desc_of_unique hb).1 (hd y hy)

/-- ✱37·62. \(\vdash:\text{E}!Rʻy.y\in \alpha.\supset.Rʻy\in Rʻʻ\alpha\) -/
theorem pm37_62 {R : α → β → Prop} {y : β} {A : Set β} :
    EDesc R y ∧ y ∈ A → Desc R y (fun b => b ∈ R ʻʻ A) := by
  rintro ⟨⟨b, hb⟩, hy⟩
  exact (desc_of_unique hb).2 ⟨y, hy, (hb b).2 rfl⟩

/-- ✱37·63. \(\vdash\colon\colon \text{E}‼Rʻʻ\alpha.\supset\colon\ldotp x\in Rʻʻ\alpha.\supset_{x}.\psi x:\equiv:y\in \alpha.\supset_{y}.\psi(Rʻy)\) -/
theorem pm37_63 {R : α → β → Prop} {A : Set β} {ψ : α → Prop} :
    EE R A → ((∀ x, x ∈ R ʻʻ A → ψ x) ↔ ∀ y, y ∈ A → Desc R y ψ) := by
  intro h
  constructor
  · intro hs y hy
    obtain ⟨b, hb⟩ := h y hy
    exact (desc_of_unique hb).2 (hs b ⟨y, hy, (hb b).2 rfl⟩)
  · rintro hd x ⟨y, hy, hxy⟩
    obtain ⟨b, hb⟩ := h y hy
    rw [(hb x).1 hxy]
    exact (desc_of_unique hb).1 (hd y hy)

/-- ✱37·64. \(\vdash\colon\ldotp \text{E}‼Rʻʻ\alpha.\supset:(\exists y).y\in \alpha.\psi(Rʻy).\equiv.(\exists x).x\in Rʻʻ\alpha.\psi x\) -/
theorem pm37_64 {R : α → β → Prop} {A : Set β} {ψ : α → Prop} :
    EE R A → ((∃ y, y ∈ A ∧ Desc R y ψ) ↔ ∃ x, x ∈ R ʻʻ A ∧ ψ x) := by
  intro h
  constructor
  · rintro ⟨y, hy, hd⟩
    obtain ⟨b, hb⟩ := h y hy
    exact ⟨b, ⟨y, hy, (hb b).2 rfl⟩, (desc_of_unique hb).1 hd⟩
  · rintro ⟨x, ⟨y, hy, hxy⟩, hψ⟩
    obtain ⟨b, hb⟩ := h y hy
    rw [(hb x).1 hxy] at hψ
    exact ⟨y, hy, (desc_of_unique hb).2 hψ⟩

/-- ✱37·65. \(\vdash:\text{E}‼Rʻʻ\beta.\alpha\subset Rʻʻ\beta.\supset.\alpha=Rʻʻ(\breve{R}ʻʻ\alpha\cap \beta)\) -/
theorem pm37_65 {R : α → β → Prop} {B : Set β} {A : Set α} :
    EE R B ∧ A ⊆ R ʻʻ B → A = R ʻʻ (R˘ ʻʻ A ∩ B) := by
  rintro ⟨h, hs⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := hs hx
    exact ⟨y, ⟨⟨x, hx, hxy⟩, hy⟩, hxy⟩
  · rintro ⟨y, ⟨⟨z, hz, hzy⟩, hy⟩, hxy⟩
    obtain ⟨b, hb⟩ := h y hy
    rwa [(hb x).1 hxy, ← (hb z).1 hzy]

/-- ✱37·66. \(\vdash\colon\ldotp \text{E}‼Rʻʻ\beta.\supset:\alpha\subset Rʻʻ\beta.\equiv.(\exists \gamma).\gamma\subset \beta.\alpha=Rʻʻ\gamma\) -/
theorem pm37_66 {R : α → β → Prop} {B : Set β} {A : Set α} :
    EE R B → (A ⊆ R ʻʻ B ↔ ∃ G, G ⊆ B ∧ A = R ʻʻ G) := by
  intro h
  constructor
  · intro hs
    exact ⟨R˘ ʻʻ A ∩ B, fun _ hy => hy.2, pm37_65 ⟨h, hs⟩⟩
  · rintro ⟨G, hG, rfl⟩
    exact pm37_2 hG

/-- ✱37·67. \(\vdash\colon\ldotp z\in \gamma.\supset_{z}.\text{E}!RʻSʻz:\supset. RʻʻSʻʻ\gamma=\hat{x}\{(\exists z). z\in \gamma. x=RʻSʻz\}\)

`E!R'S'z` is `E!(℩x)(x R (S'z))` with the inner description of smaller scope (✱14·02,
✱30·02). -/
theorem pm37_67 {R : α → β → Prop} {S : β → γ → Prop} {G : Set γ} :
    (∀ z, z ∈ G → EBang (fun x => Desc S z (fun w => R x w))) →
      R ʻʻ S ʻʻ G = {x | ∃ z, z ∈ G ∧ Desc2 R S z (fun b => x = b)} := by
  intro h
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    refine ⟨z, hz, ?_⟩
    obtain ⟨b, hb⟩ := h z hz
    obtain ⟨c, hc, -⟩ := (hb b).2 rfl
    refine (TheIs_iff_of_unique hb).2 ((hb x).1 ((desc_of_unique hc).2 ?_))
    rwa [← (hc y).1 hyz]
  · rintro ⟨z, hz, hd⟩
    obtain ⟨b, hb⟩ := h z hz
    have hxb : x = b := (TheIs_iff_of_unique hb).1 hd
    subst hxb
    obtain ⟨c, hc, hxc⟩ := (hb x).2 rfl
    exact ⟨c, ⟨z, hz, (hc c).2 rfl⟩, hxc⟩

/-- ✱37·68. \(\vdash\colon\ldotp z\in \gamma. \supset_{z}. PʻQʻz = Rʻz:\supset. PʻʻQʻʻ\gamma = Rʻʻ\gamma\) -/
theorem pm37_68 {P : α → β → Prop} {Q : β → γ → Prop} {R : α → γ → Prop} {G : Set γ} :
    (∀ z, z ∈ G → Desc2 P Q z (fun a => Desc R z (fun b => a = b))) →
      P ʻʻ Q ʻʻ G = R ʻʻ G := by
  intro h
  have key : ∀ z, z ∈ G → ∀ x, (P ⨾ Q) x z ↔ R x z := by
    intro z hz x
    obtain ⟨a, ha, b, hb, rfl⟩ := relProd_of_desc2 (h z hz)
    exact (ha x).trans (hb x).symm
  rw [← pm37_33]
  ext x
  exact ⟨fun ⟨z, hz, hx⟩ => ⟨z, hz, (key z hz x).1 hx⟩,
    fun ⟨z, hz, hx⟩ => ⟨z, hz, (key z hz x).2 hx⟩⟩

/-- ✱37·69. \(\vdash\colon\ldotp y\in \beta. \supset_{y}. Rʻy = Sʻy: \supset. Rʻʻ\beta = Sʻʻ\beta\) -/
theorem pm37_69 {R S : α → β → Prop} {B : Set β} :
    (∀ y, y ∈ B → Desc R y (fun a => Desc S y (fun b => a = b))) → R ʻʻ B = S ʻʻ B := by
  intro h
  ext x
  exact ⟨fun ⟨y, hy, hx⟩ => ⟨y, hy, (rel_iff_of_desc_eq (h y hy) x).1 hx⟩,
    fun ⟨y, hy, hx⟩ => ⟨y, hy, (rel_iff_of_desc_eq (h y hy) x).2 hx⟩⟩

/-- ✱37·7. \(\vdash. \overrightarrow{R}ʻʻ\beta=\hat{\alpha}\{(\exists y) . y\in \beta. \alpha= \overrightarrow{R}ʻy\} \quad[\text{*37·6 . *32·12}]\) -/
theorem pm37_7 {R : α → β → Prop} {B : Set β} :
    Rfwd R ʻʻ B = {A | ∃ y, y ∈ B ∧ A = refs R y} := rfl

/-- ✱37·701. \(\vdash. \overleftarrow{R}ʻʻ\alpha = \hat{\beta}\{(\exists x) . x\in \alpha. \beta= \overleftarrow{R}ʻx\} \quad[\text{*37·6 . *32·121}]\) -/
theorem pm37_701 {R : α → β → Prop} {A : Set α} :
    Rbwd R ʻʻ A = {B | ∃ x, x ∈ A ∧ B = rels R x} := rfl

/-- ✱37·702. \(\vdash\colon\ldotp \overrightarrow{R}ʻʻ\beta\subset \kappa.\equiv:y\in \beta.\supset_{y}.\overrightarrow{R}ʻy\in \kappa \quad[\text{*37·61}]\) -/
theorem pm37_702 {R : α → β → Prop} {B : Set β} {K : Set (Set α)} :
    Rfwd R ʻʻ B ⊆ K ↔ ∀ y, y ∈ B → refs R y ∈ K := by
  constructor
  · intro h y hy
    exact h ⟨y, hy, rfl⟩
  · rintro h A ⟨y, hy, rfl⟩
    exact h y hy

/-- ✱37·703. \(\vdash\colon\ldotp \overleftarrow{R}ʻʻ\beta\subset \kappa.\equiv:x\in \beta.\supset_{x}.\overleftarrow{R}ʻx\in \kappa \quad[\text{*37·61}]\) -/
theorem pm37_703 {R : α → β → Prop} {B : Set α} {K : Set (Set β)} :
    Rbwd R ʻʻ B ⊆ K ↔ ∀ x, x ∈ B → rels R x ∈ K := by
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h A ⟨x, hx, rfl⟩
    exact h x hx

/-- ✱37·704. \(\vdash:y\in \alpha.\supset.\overrightarrow{R}ʻy\in \overrightarrow{R}ʻʻ\alpha \quad[\text{*37·62.*32·12}]\) -/
theorem pm37_704 {R : α → β → Prop} {A : Set β} {y : β} :
    y ∈ A → refs R y ∈ Rfwd R ʻʻ A :=
  fun hy => ⟨y, hy, rfl⟩

/-- ✱37·705. \(\vdash:x\in \alpha.\supset.\overleftarrow{R}ʻx\in \overleftarrow{R}ʻʻ\alpha \quad[\text{*37·62.*32·121}]\) -/
theorem pm37_705 {R : α → β → Prop} {A : Set α} {x : α} :
    x ∈ A → rels R x ∈ Rbwd R ʻʻ A :=
  fun hx => ⟨x, hx, rfl⟩

/-- ✱37·706. \(\vdash\colon\ldotp \alpha\in \overrightarrow{R}ʻʻ\beta.\supset_{\alpha}.\psi\alpha:\equiv:y\in \beta.\supset_{y}.\psi(\overrightarrow{R}ʻy) \quad[\text{*37·63}]\) -/
theorem pm37_706 {R : α → β → Prop} {B : Set β} {ψ : Set α → Prop} :
    (∀ A, A ∈ Rfwd R ʻʻ B → ψ A) ↔ ∀ y, y ∈ B → ψ (refs R y) := by
  constructor
  · intro h y hy
    exact h _ ⟨y, hy, rfl⟩
  · rintro h A ⟨y, hy, rfl⟩
    exact h y hy

/-- ✱37·707. \(\vdash\colon\ldotp \beta\in \overleftarrow{R}ʻʻ\alpha.\supset_{\beta}.\psi\beta:\equiv:x\in \alpha.\supset_{x}.\psi(\overleftarrow{R}ʻx) \quad[\text{*37·63}]\) -/
theorem pm37_707 {R : α → β → Prop} {A : Set α} {ψ : Set β → Prop} :
    (∀ B, B ∈ Rbwd R ʻʻ A → ψ B) ↔ ∀ x, x ∈ A → ψ (rels R x) := by
  constructor
  · intro h x hx
    exact h _ ⟨x, hx, rfl⟩
  · rintro h B ⟨x, hx, rfl⟩
    exact h x hx

/-- ✱37·708. \(\vdash\colon\ldotp (\exists \alpha).\alpha\in \overrightarrow{R}ʻʻ\beta.\psi\alpha.\equiv.(\exists y).y\in \beta.\psi(\overrightarrow{R}ʻy) \quad[\text{*37·64}]\) -/
theorem pm37_708 {R : α → β → Prop} {B : Set β} {ψ : Set α → Prop} :
    (∃ A, A ∈ Rfwd R ʻʻ B ∧ ψ A) ↔ ∃ y, y ∈ B ∧ ψ (refs R y) := by
  constructor
  · rintro ⟨A, ⟨y, hy, rfl⟩, h⟩
    exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨_, ⟨y, hy, rfl⟩, h⟩

/-- ✱37·709. \(\vdash\colon\ldotp (\exists \alpha).\alpha\in \overleftarrow{R}ʻʻ\beta.\psi\alpha.\equiv.(\exists x).x\in \beta.\psi(\overleftarrow{R}ʻx) \quad[\text{*37·64}]\) -/
theorem pm37_709 {R : α → β → Prop} {B : Set α} {ψ : Set β → Prop} :
    (∃ A, A ∈ Rbwd R ʻʻ B ∧ ψ A) ↔ ∃ x, x ∈ B ∧ ψ (rels R x) := by
  constructor
  · rintro ⟨A, ⟨x, hx, rfl⟩, h⟩
    exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨_, ⟨x, hx, rfl⟩, h⟩

/-- ✱37·71. \(\vdash:\kappa\subset \overrightarrow{R}ʻʻ\beta.\supset.\kappa=\overrightarrow{R}ʻʻ\{(\text{Cnv}ʻ\overrightarrow{R})ʻʻ\kappa\cap \beta\} \quad[\text{*37·65}]\)

`Cnv'R⃗` is `(Rfwd R)˘` (`desc_Cnv`). -/
theorem pm37_71 {R : α → β → Prop} {B : Set β} {K : Set (Set α)} :
    K ⊆ Rfwd R ʻʻ B → K = Rfwd R ʻʻ ((Rfwd R)˘ ʻʻ K ∩ B) :=
  fun hs => pm37_65 ⟨fun y _ => EDesc_graph (refs R) y, hs⟩

/-- ✱37·711. \(\vdash:\kappa\subset \overleftarrow{R}ʻʻ\beta.\supset.\kappa=\overleftarrow{R}ʻʻ\{(\text{Cnv}ʻ\overleftarrow{R})ʻʻ\kappa\cap \beta\} \quad[\text{*37·65}]\) -/
theorem pm37_711 {R : α → β → Prop} {B : Set α} {K : Set (Set β)} :
    K ⊆ Rbwd R ʻʻ B → K = Rbwd R ʻʻ ((Rbwd R)˘ ʻʻ K ∩ B) :=
  fun hs => pm37_65 ⟨fun x _ => EDesc_graph (rels R) x, hs⟩

/-- ✱37·712. \(\vdash:\kappa\subset \overrightarrow{R}ʻʻ\beta.\equiv.(\exists \gamma).\gamma\subset \beta.\kappa=\overrightarrow{R}ʻʻ\gamma \quad[\text{*37·66}]\) -/
theorem pm37_712 {R : α → β → Prop} {B : Set β} {K : Set (Set α)} :
    K ⊆ Rfwd R ʻʻ B ↔ ∃ G, G ⊆ B ∧ K = Rfwd R ʻʻ G :=
  pm37_66 fun y _ => EDesc_graph (refs R) y

/-- ✱37·713. \(\vdash:\kappa\subset \overleftarrow{R}ʻʻ\beta.\equiv.(\exists \gamma).\gamma\subset \beta.\kappa=\overleftarrow{R}ʻʻ\gamma \quad[\text{*37·66}]\) -/
theorem pm37_713 {R : α → β → Prop} {B : Set α} {K : Set (Set β)} :
    K ⊆ Rbwd R ʻʻ B ↔ ∃ G, G ⊆ B ∧ K = Rbwd R ʻʻ G :=
  pm37_66 fun x _ => EDesc_graph (rels R) x

/-- ✱37·72. \(\vdash:R=P\mid Q.\supset.\overrightarrow{R}ʻʻ\gamma=Pʻʻʻ\overrightarrow{Q}ʻʻ\gamma\) -/
theorem pm37_72 {R : α → γ → Prop} {P : α → β → Prop} {Q : β → γ → Prop} {G : Set γ} :
    R = P ⨾ Q → Rfwd R ʻʻ G = P ʻʻʻ Rfwd Q ʻʻ G := by
  rintro rfl
  ext A
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨refs Q z, ⟨z, hz, rfl⟩, refs_relProd P Q z⟩
  · rintro ⟨B, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (refs_relProd P Q z).symm⟩

/-- ✱37·721. \(\vdash:R=P\mid Q.\supset.\overleftarrow{R}ʻʻ\gamma=\breve{Q}ʻʻʻ\overleftarrow{P}ʻʻ\gamma \quad[\text{Proof as in *37·72}]\) -/
theorem pm37_721 {R : α → γ → Prop} {P : α → β → Prop} {Q : β → γ → Prop} {G : Set α} :
    R = P ⨾ Q → Rbwd R ʻʻ G = Q˘ ʻʻʻ Rbwd P ʻʻ G := by
  rintro rfl
  ext A
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rels P x, ⟨x, hx, rfl⟩, rels_relProd P Q x⟩
  · rintro ⟨B, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (rels_relProd P Q x).symm⟩

/-- ✱37·73. \(\vdash:\exists !\beta.\equiv.\exists !\overrightarrow{R}ʻʻ\beta.\equiv.\exists !\overleftarrow{R}ʻʻ\beta \quad[\text{*37·45.*32·12·121}]\) -/
theorem pm37_73 {R : α → α → Prop} {B : Set α} :
    (B.Nonempty ↔ (Rfwd R ʻʻ B).Nonempty) ∧ ((Rfwd R ʻʻ B).Nonempty ↔ (Rbwd R ʻʻ B).Nonempty) := by
  rw [show Rfwd R = graph (refs R) from rfl, show Rbwd R = graph (rels R) from rfl,
    img_graph_nonempty, img_graph_nonempty]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- ✱37·731. \(\vdash:\beta=\Lambda.\equiv.\overrightarrow{R}ʻʻ\beta=\Lambda.\equiv.\overleftarrow{R}ʻʻ\beta=\Lambda \quad[\text{*37·73.Transp}]\)

As PM observes, the `Λ`'s are of different types: `(Λ : Set α)` and `(Λ : Set (Set α))`. -/
theorem pm37_731 {R : α → α → Prop} {B : Set α} :
    (B = Λ ↔ Rfwd R ʻʻ B = Λ) ∧ (Rfwd R ʻʻ B = Λ ↔ Rbwd R ʻʻ B = Λ) := by
  rw [eq_Null_iff, eq_Null_iff, eq_Null_iff]
  exact ⟨not_congr pm37_73.1, not_congr pm37_73.2⟩

/-- ✱37·74. \(\vdash\colon\ldotp \beta\subset\text{ᗡ}ʻR.\equiv:\alpha\in \overrightarrow{R}ʻʻ\beta.\supset_{\alpha}.\exists !\alpha\) -/
theorem pm37_74 {R : α → β → Prop} {B : Set β} :
    B ⊆ codom R ↔ ∀ A, A ∈ Rfwd R ʻʻ B → A.Nonempty := by
  rw [pm37_706]
  exact Iff.rfl

/-- ✱37·75. \(\vdash\colon\ldotp \alpha\subset\text{D}ʻR.\equiv:\beta\in \overleftarrow{R}ʻʻ\alpha.\supset_{\beta}.\exists !\beta \quad[\text{Proof as in *37·74}]\) -/
theorem pm37_75 {R : α → β → Prop} {A : Set α} :
    A ⊆ dom R ↔ ∀ B, B ∈ Rbwd R ʻʻ A → B.Nonempty := by
  rw [pm37_707]
  exact Iff.rfl

/-- ✱37·76. \(\vdash.\overrightarrow{R}ʻʻ\beta\subset\text{Cls}\) -/
theorem pm37_76 {R : α → β → Prop} {B : Set β} : Rfwd R ʻʻ B ⊆ Cls := by
  rintro A ⟨y, _, rfl⟩
  exact ⟨fun x => R x y, rfl⟩

/-- ✱37·761. \(\vdash.\overleftarrow{R}ʻʻ\alpha \subset \text{Cls} \quad[\text{Proof as in *37·76}]\) -/
theorem pm37_761 {R : α → β → Prop} {A : Set α} : Rbwd R ʻʻ A ⊆ Cls := by
  rintro B ⟨x, _, rfl⟩
  exact ⟨fun y => R x y, rfl⟩

/-- ✱37·77. \(\vdash: \alpha\in \overrightarrow{R}ʻʻ\text{ᗡ}ʻR.\supset_{\alpha}.\exists !\alpha \quad[\text{*37·74.*22·42}]\) -/
theorem pm37_77 {R : α → β → Prop} : ∀ A, A ∈ Rfwd R ʻʻ codom R → A.Nonempty :=
  pm37_74.1 fun _ h => h

/-- ✱37·771. \(\vdash: \beta\in \overleftarrow{R}ʻʻ\text{D}ʻR.\supset_{\beta}.\exists !\beta \quad[\text{Proof as in *37·77}]\) -/
theorem pm37_771 {R : α → β → Prop} : ∀ B, B ∈ Rbwd R ʻʻ dom R → B.Nonempty :=
  pm37_75.1 fun _ h => h

/-- ✱37·772. \(\vdash. \Lambda{\sim}\in \overrightarrow{R}ʻʻ\text{ᗡ}ʻR \quad[\text{*37·77.*24·63}]\) -/
theorem pm37_772 {R : α → β → Prop} : (Λ : Set α) ∉ Rfwd R ʻʻ codom R := by
  intro h
  obtain ⟨x, hx⟩ := pm37_77 _ h
  exact (mem_Null_iff x).1 hx

/-- ✱37·773. \(\vdash. \Lambda{\sim}\in \overleftarrow{R}ʻʻ\text{D}ʻR \quad[\text{*37·771.*24·63}]\) -/
theorem pm37_773 {R : α → β → Prop} : (Λ : Set β) ∉ Rbwd R ʻʻ dom R := by
  intro h
  obtain ⟨y, hy⟩ := pm37_771 _ h
  exact (mem_Null_iff y).1 hy

/-- ✱37·78. \(\vdash. \text{D}ʻ\overrightarrow{R}=\overrightarrow{R}ʻʻ\text{V} \quad[\text{*37·28}]\) -/
theorem pm37_78 {R : α → β → Prop} : dom (Rfwd R) = Rfwd R ʻʻ V :=
  pm37_28.1.symm

/-- ✱37·781. \(\vdash. \text{D}ʻ\overleftarrow{R}=\overleftarrow{R}ʻʻ\text{V} \quad[\text{*37·28}]\) -/
theorem pm37_781 {R : α → β → Prop} : dom (Rbwd R) = Rbwd R ʻʻ V :=
  pm37_28.1.symm

/-- ✱37·79. \(\vdash. \overrightarrow{R}ʻʻ\text{V}= \hat{\alpha}\{\exists y).\alpha=\overrightarrow{R}ʻy\} \quad[\text{*37·601.*32·12}]\)

(The e-text omits the opening bracket of `(∃y)`.) -/
theorem pm37_79 {R : α → β → Prop} : Rfwd R ʻʻ V = {A | ∃ y, A = refs R y} := by
  ext A
  exact ⟨fun ⟨y, _, h⟩ => ⟨y, h⟩, fun ⟨y, h⟩ => ⟨y, rfl, h⟩⟩

/-- ✱37·791. \(\vdash. \overleftarrow{R}ʻʻ\text{V}= \hat{\beta}\{(\exists x).\beta=\overleftarrow{R}ʻx\} \quad[\text{*37·601.*32·121}]\) -/
theorem pm37_791 {R : α → β → Prop} : Rbwd R ʻʻ V = {B | ∃ x, B = rels R x} := by
  ext B
  exact ⟨fun ⟨x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, rfl, h⟩⟩

/-- ✱37·8. \(\vdash. (\alpha\uparrow \beta)\mid S=\alpha\uparrow \breve{S}ʻʻ\beta\) -/
theorem pm37_8 {A : Set α} {B : Set β} {S : β → γ → Prop} :
    cross A B ⨾ S = cross A (S˘ ʻʻ B) := by
  funext x z
  apply propext
  exact ⟨fun ⟨y, ⟨hx, hy⟩, h⟩ => ⟨hx, y, hy, h⟩, fun ⟨hx, y, hy, h⟩ => ⟨y, ⟨hx, hy⟩, h⟩⟩

/-- ✱37·81. \(\vdash.R\mid (\alpha\uparrow \beta)=(Rʻʻ\alpha)\uparrow \beta \quad[\text{Proof as in *37·8}]\) -/
theorem pm37_81 {R : α → β → Prop} {A : Set β} {B : Set γ} :
    R ⨾ cross A B = cross (R ʻʻ A) B := by
  funext x z
  apply propext
  exact ⟨fun ⟨y, h, hy, hz⟩ => ⟨⟨y, hy, h⟩, hz⟩, fun ⟨⟨y, hy, h⟩, hz⟩ => ⟨y, h, hy, hz⟩⟩

/-- ✱37·82. \(\vdash.R\mid (\alpha\uparrow \beta)\mid S=(Rʻʻ\alpha)\uparrow (\breve{S}ʻʻ\beta) \quad[\text{*37·8·81}]\) -/
theorem pm37_82 {R : α → β → Prop} {A : Set β} {B : Set γ} {S : γ → δ → Prop} :
    R ⨾ cross A B ⨾ S = cross (R ʻʻ A) (S˘ ʻʻ B) := by
  rw [pm37_81, pm37_8]

/-!
## [✱38] Relations and classes derived from a double descriptive function

*(Vol. 1, p. 311)*

> *Summary of* *38.
>
> …

**Lean reading.** PM's `♀` is any double descriptive function with `(x, y) . E!(x♀y)`; in Lean it
is a function `f : α → β → γ`, and `x♀y` is `f x y`. `x♀` is `opL f x : γ → β → Prop`, `♀y` is
`opR f y : γ → α → Prop` (both `graph`s), `α ♀,, y` is `opImg f A y`. The descriptive functions
`x♀'y`, `♀y'x` are kept as descriptions (`Desc`, `EDesc`) in ✱38·11·12·22·23, whose content is
their existence and value. `♀,,` is again a double descriptive function, `opImg f`, so
`α♀,,` is `opL (opImg f) A` and `♀,,y` is `opR (opImg f) y`. The chains of identities ✱38·11,
✱38·22, ✱38·3, ✱38·31 are conjunctions of their links (✱13·03), each description having the
smallest scope. Most propositions hold by unfolding the definitions, as PM says ("immediate
consequences of the definitions").

**Status.** proved (all propositions; ✱38·01–✱38·03 definition; ✱38·131 and ✱38·3 proved
(reading), transcription errors of the e-text, see their docstrings).
-/

/-- ✱38·01 (Df). \(x\unicode{x2640} =\hat{u}\hat{y}(u=x\unicode{x2640} y)\quad \text{Df}\) -/
theorem pm38_01 {f : α → β → γ} {x : α} : opL f x = fun u y => u = f x y := rfl

/-- ✱38·02 (Df). \(\unicode{x2640} y=\hat{u}\hat{x}(u=x\unicode{x2640} y)\quad \text{Df}\) -/
theorem pm38_02 {f : α → β → γ} {y : β} : opR f y = fun u x => u = f x y := rfl

/-- ✱38·03 (Df). \(\alpha \unicode{x2640}_{,,}y=\unicode{x2640} yʻʻ\alpha\quad \text{Df}\) -/
theorem pm38_03 {f : α → β → γ} {A : Set α} {y : β} : opImg f A y = opR f y ʻʻ A := rfl

/-- ✱38·1. \(\vdash :u(x\unicode{x2640} )y\ldotp \equiv \ldotp u=x\unicode{x2640} y\quad [\text{(*38·01)}]\) -/
theorem pm38_1 {f : α → β → γ} {x : α} {y : β} {u : γ} : opL f x u y ↔ u = f x y :=
  Iff.rfl

/-- ✱38·101. \(\vdash:u(\unicode{x2640}y)x.\equiv.u=x\unicode{x2640}y \quad[\text{(*38·02)}]\) -/
theorem pm38_101 {f : α → β → γ} {x : α} {y : β} {u : γ} : opR f y u x ↔ u = f x y :=
  Iff.rfl

/-- ✱38·11. \(\vdash.x\unicode{x2640}ʻy=\unicode{x2640}yʻx=x\unicode{x2640}y \quad[\text{*38·1·101.*30·3}]\)

Stated with `Desc` (Basic §5): the first link `x♀'y = ♀y'x` has two descriptions, the first
with the larger scope; the second link is `♀y'x = x♀y`. -/
theorem pm38_11 {f : α → β → γ} {x : α} {y : β} :
    Desc (opL f x) y (fun a => Desc (opR f y) x (fun b => a = b)) ∧
      Desc (opR f y) x (fun b => b = f x y) :=
  ⟨(desc_of_unique (fun _ => Iff.rfl)).2 ((desc_of_unique (fun _ => Iff.rfl)).2 rfl),
    (desc_of_unique (fun _ => Iff.rfl)).2 rfl⟩

/-- ✱38·12. \(\vdash.\text{E}!x\unicode{x2640}ʻy.\text{E}!\unicode{x2640}yʻx \quad[\text{*38·11.*14·21}]\) -/
theorem pm38_12 {f : α → β → γ} {x : α} {y : β} :
    EDesc (opL f x) y ∧ EDesc (opR f y) x :=
  ⟨EDesc_graph (f x) y, EDesc_graph (fun x => f x y) x⟩

/-- ✱38·13. \(\vdash:u\in x\unicode{x2640}ʻʻ\alpha.\equiv.(\exists y).y\in \alpha.u=x\unicode{x2640}y \quad[\text{*38·1.*37·1}]\) -/
theorem pm38_13 {f : α → β → γ} {x : α} {A : Set β} {u : γ} :
    u ∈ opL f x ʻʻ A ↔ ∃ y, y ∈ A ∧ u = f x y := Iff.rfl

/-- ✱38·131. \(\vdash:u\in \unicode{x2640}yʻʻ\alpha.=.(\exists x).x\in \alpha.u=x\unicode{x2640}y \quad[\text{*38·101.*37·1}]\)

**Status.** proved (reading): transcription error of the e-text, which prints `.=.` for
`.≡.` between the two propositions (identity is not significant between propositions; cf.
✱38·13). -/
theorem pm38_131 {f : α → β → γ} {y : β} {A : Set α} {u : γ} :
    u ∈ opR f y ʻʻ A ↔ ∃ x, x ∈ A ∧ u = f x y := Iff.rfl

/-- ✱38·2. \(\vdash.\alpha\unicode{x2640}_{,,}y=\unicode{x2640}yʻʻ\alpha \quad[\text{(*38·03)}]\) -/
theorem pm38_2 {f : α → β → γ} {A : Set α} {y : β} : opImg f A y = opR f y ʻʻ A := rfl

/-- ✱38·21. \(\vdash.\alpha\unicode{x2640}_{,,}y=\hat{u}\{(\exists x).x\in \alpha.u=x\unicode{x2640}y\} \quad[\text{*38·2·131}]\) -/
theorem pm38_21 {f : α → β → γ} {A : Set α} {y : β} :
    opImg f A y = {u | ∃ x, x ∈ A ∧ u = f x y} := rfl

/-- ✱38·22. \(\vdash.\alpha\unicode{x2640}_{,,}ʻy=\unicode{x2640}_{,,}yʻ\alpha=\alpha\unicode{x2640}_{,,}y \quad[\text{*38·11}]\)

✱38·11 for the double descriptive function `♀,,` (`opImg f`). -/
theorem pm38_22 {f : α → β → γ} {A : Set α} {y : β} :
    Desc (opL (opImg f) A) y (fun a => Desc (opR (opImg f) y) A (fun b => a = b)) ∧
      Desc (opR (opImg f) y) A (fun b => b = opImg f A y) :=
  pm38_11

/-- ✱38·23. \(\vdash.\text{E}!\alpha\unicode{x2640}_{,,}ʻy.\text{E}!\unicode{x2640}_{,,}yʻ\alpha \quad[\text{*38·22.*14·21}]\) -/
theorem pm38_23 {f : α → β → γ} {A : Set α} {y : β} :
    EDesc (opL (opImg f) A) y ∧ EDesc (opR (opImg f) y) A :=
  pm38_12

/-- ✱38·24. \(\vdash:\exists !\alpha\unicode{x2640}_{,,}y.\equiv.\exists !\alpha\) -/
theorem pm38_24 {f : α → β → γ} {A : Set α} {y : β} :
    (opImg f A y).Nonempty ↔ A.Nonempty :=
  ⟨fun ⟨_, x, hx, _⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨f x y, x, hx, rfl⟩⟩

/-- ✱38·3. \[\begin{align}&\vdash.\alpha\unicode{x2640}_{,,}ʻʻ\beta=\hat{\gamma}\{(\exists y).y\in \beta.\gamma=\alpha\unicode{x2640}_{,,}\gamma\}=\hat{\gamma}\{(\exists y).\gamma\in \beta.\gamma=\unicode{x2640}yʻʻ\alpha\}\\ &[\text{*38·13·2}]\end{align}\]

**Status.** proved (reading): transcription errors of the e-text, which prints
`γ = α♀,,γ` for `γ = α♀,,y` in the first class and `γ ∈ β` for `y ∈ β` in the second (both are
not significant as printed: `γ` would be a class and a member of the class `γ ∈ β` of `y`'s at
once; the reference ✱38·13 gives `y ∈ β . γ = α♀,,y`, cf. ✱38·31). -/
theorem pm38_3 {f : α → β → γ} {A : Set α} {B : Set β} :
    opL (opImg f) A ʻʻ B = {G | ∃ y, y ∈ B ∧ G = opImg f A y} ∧
      {G | ∃ y, y ∈ B ∧ G = opImg f A y} = {G | ∃ y, y ∈ B ∧ G = opR f y ʻʻ A} :=
  ⟨rfl, rfl⟩

/-- ✱38·31. \[\begin{align}&\vdash.\unicode{x2640}_{,,}yʻʻ\kappa=\hat{\gamma}\{(\exists \alpha).\alpha\in \kappa.\gamma=\alpha\unicode{x2640}_{,,}y\}=\hat{\gamma}\{(\exists \alpha).\alpha\in \kappa.\gamma=\unicode{x2640}yʻʻ\alpha\}=\unicode{x2640}yʻʻʻ\kappa\\ &[\text{*38·131·2.*37·103}]\end{align}\] -/
theorem pm38_31 {f : α → β → γ} {y : β} {K : Set (Set α)} :
    ((opR (opImg f) y ʻʻ K = {G | ∃ A, A ∈ K ∧ G = opImg f A y}) ∧
      ({G | ∃ A, A ∈ K ∧ G = opImg f A y} = {G | ∃ A, A ∈ K ∧ G = opR f y ʻʻ A})) ∧
      ({G | ∃ A, A ∈ K ∧ G = opR f y ʻʻ A} = opR f y ʻʻʻ K) :=
  ⟨⟨rfl, rfl⟩, rfl⟩

end PrincipiaMathematica
