import PrincipiaMathematica.Defs.Part2

/-!
# Part II, Section C: One-many, many-one, and one-one relations

Volume 1. Numbers: ✱70, ✱71, ✱72.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w u'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

/-! ### Helper lemmas (not PM propositions) -/

private theorem eqNull_iff {A : Set α} : A = Λ ↔ ¬ A.Nonempty := by
  rw [Null_eq_empty, Set.not_nonempty_iff_eq_empty]

private theorem not_mem_Null' (x : α) : x ∉ (Λ : Set α) := fun h => h rfl

private theorem refs_mem_iotaNull {R : α → β → Prop} {y : β} :
    refs R y ∈ ι (Λ : Set α) ↔ y ∉ codom R := eqNull_iff

/-- `ψ(R'y)` holds iff `R'y` exists and some referent of `y` satisfies `ψ`. -/
private theorem desc_iff {R : α → β → Prop} {y : β} {ψ : α → Prop} :
    Desc R y ψ ↔ EDesc R y ∧ ∃ x, R x y ∧ ψ x := by
  constructor
  · rintro ⟨b, hb, hψ⟩
    exact ⟨⟨b, hb⟩, b, (hb b).2 rfl, hψ⟩
  · rintro ⟨⟨b, hb⟩, x, hx, hψ⟩
    exact ⟨b, hb, ((hb x).1 hx) ▸ hψ⟩

private theorem edesc_of_desc {R : α → β → Prop} {y : β} {ψ : α → Prop} (h : Desc R y ψ) :
    EDesc R y := (desc_iff.1 h).1

private theorem desc_of_rel {R : α → β → Prop} {y : β} {x : α} {ψ : α → Prop} (h : EDesc R y)
    (hx : R x y) : Desc R y ψ ↔ ψ x := by
  obtain ⟨b, hb⟩ := h
  have e : x = b := (hb x).1 hx
  subst e
  exact TheIs_iff_of_unique hb

private theorem mem_codom_of_edesc {R : α → β → Prop} {y : β} (h : EDesc R y) : y ∈ codom R := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, (hb b).2 rfl⟩

/-- `R'y = S'z`, i.e. both descriptions exist and are equal. -/
private theorem desc_eq_desc_iff {R : α → β → Prop} {S : α → γ → Prop} {y : β} {z : γ} :
    Desc R y (fun b => Desc S z (fun c => b = c)) ↔
      ∃ b, (∀ x, R x y ↔ x = b) ∧ (∀ x, S x z ↔ x = b) := by
  constructor
  · rintro ⟨b, hb, c, hc, rfl⟩
    exact ⟨b, hb, hc⟩
  · rintro ⟨b, hb, hc⟩
    exact ⟨b, hb, b, hc, rfl⟩

private theorem arrow_cnv {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    R˘ ∈ arrow B A ↔ R ∈ arrow A B :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

private theorem mem_arrow_left {A : Set (Set α)} {R : α → β → Prop} :
    R ∈ arrow A Cls ↔ ∀ y, y ∈ codom R → refs R y ∈ A := by
  rw [mem_arrow_iff, Cls_eq_univ]
  simp only [Set.mem_univ, implies_true, and_true]

private theorem mem_arrow_right {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow Cls B ↔ ∀ x, x ∈ dom R → rels R x ∈ B := by
  rw [mem_arrow_iff, Cls_eq_univ]
  simp only [Set.mem_univ, implies_true, true_and]

private theorem arrow_eq_inter {A : Set (Set α)} {B : Set (Set β)} :
    arrow A B = arrow A Cls ∩ arrow Cls B := by
  ext R
  rw [Set.mem_inter_iff, mem_arrow_iff, mem_arrow_left, mem_arrow_right]

/-- The classes `f''B` for a `graph`: `(graph f)''β ⊂ κ . ≡ : y ∈ β . ⊃_y . f'y ∈ κ`. -/
private theorem graph_img_sub {f : β → α} {B : Set β} {K : Set α} :
    graph f ʻʻ B ⊆ K ↔ ∀ y, y ∈ B → f y ∈ K := by
  constructor
  · intro h y hy
    exact h ⟨y, hy, rfl⟩
  · rintro h X ⟨y, hy, rfl⟩
    exact h y hy

private theorem dom_graph_sub {f : β → α} {K : Set α} :
    dom (graph f) ⊆ K ↔ ∀ y, f y ∈ K := by
  constructor
  · intro h y
    exact h ⟨y, rfl⟩
  · rintro h X ⟨y, rfl⟩
    exact h y

/-- `(y) . R⃗'y ∈ α ∪ ι'Λ` is `y ∈ ᗡ'R . ⊃_y . R⃗'y ∈ α`. -/
private theorem all_refs_iff {R : α → β → Prop} {A : Set (Set α)} :
    (∀ y, refs R y ∈ A ∪ ι Λ) ↔ ∀ y, y ∈ codom R → refs R y ∈ A := by
  constructor
  · intro h y hy
    rcases h y with h1 | h1
    · exact h1
    · exact absurd hy (refs_mem_iotaNull.1 h1)
  · intro h y
    by_cases hy : y ∈ codom R
    · exact Or.inl (h y hy)
    · exact Or.inr (refs_mem_iotaNull.2 hy)

private theorem mem_arrow_union {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow A B ↔ (∀ y, refs R y ∈ A ∪ ι Λ) ∧ ∀ x, rels R x ∈ B ∪ ι Λ := by
  rw [mem_arrow_iff]
  exact and_congr all_refs_iff.symm (all_refs_iff (R := R˘)).symm

private theorem arrow_congr {A A' : Set (Set α)} {B B' : Set (Set β)}
    (hA : ∀ X : Set α, X.Nonempty → (X ∈ A ↔ X ∈ A'))
    (hB : ∀ Y : Set β, Y.Nonempty → (Y ∈ B ↔ Y ∈ B')) : arrow A B = arrow A' B' := by
  ext R
  rw [mem_arrow_iff, mem_arrow_iff]
  exact and_congr (forall_congr' fun y => forall_congr' fun hy => hA _ hy)
    (forall_congr' fun x => forall_congr' fun hx => hB _ hx)

/-- One-many relations: `R'y` exists for every `y ∈ ᗡ'R`. -/
private theorem oneCls_edesc {R : α → β → Prop} {y : β} (hR : R ∈ arrow one Cls)
    (hy : y ∈ codom R) : EDesc R y := by
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, fun z => ⟨fun hz => mem_arrow_one_Cls.1 hR z x y ⟨hz, hx⟩, fun e => e ▸ hx⟩⟩

private theorem oneCls_desc {R : α → β → Prop} {y : β} {x : α} {ψ : α → Prop}
    (hR : R ∈ arrow one Cls) (hx : R x y) : Desc R y ψ ↔ ψ x :=
  desc_of_rel (oneCls_edesc hR ⟨x, hx⟩) hx

private theorem oneCls_desc_eq {R : α → β → Prop} {y : β} {x : α} (hR : R ∈ arrow one Cls) :
    Desc R y (fun b => x = b) ↔ R x y := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (hb x).2 rfl
  · intro hx
    exact (oneCls_desc hR hx).2 rfl

private theorem oneCls_iff_edesc {R : α → β → Prop} :
    R ∈ arrow one Cls ↔ ∀ y, y ∈ codom R → EDesc R y := by
  constructor
  · intro hR y hy
    exact oneCls_edesc hR hy
  · intro h
    rw [mem_arrow_one_Cls]
    rintro x x' y ⟨hx, hx'⟩
    obtain ⟨b, hb⟩ := h y ⟨x, hx⟩
    exact ((hb x).1 hx).trans ((hb x').1 hx').symm

private theorem Cls_one_iff_cnv {R : α → β → Prop} : R ∈ arrow Cls one ↔ R˘ ∈ arrow one Cls :=
  arrow_cnv.symm

private theorem one_one_iff {R : α → β → Prop} :
    R ∈ arrow one one ↔ R ∈ arrow one Cls ∧ R ∈ arrow Cls one := by
  rw [arrow_eq_inter]
  exact Iff.rfl

private theorem oneCls_mono {R S : α → β → Prop} (hR : R ∈ arrow one Cls) (hS : S ⪽ R) :
    S ∈ arrow one Cls := by
  rw [mem_arrow_one_Cls] at hR ⊢
  rintro x y z ⟨hx, hy⟩
  exact hR x y z ⟨hS x z hx, hS y z hy⟩

private theorem img_Null {R : α → β → Prop} : R ʻʻ (Λ : Set β) = Λ := by
  rw [eqNull_iff]
  rintro ⟨x, y, hy, -⟩
  exact not_mem_Null' y hy

/-!
## [✱70] Relations whose classes of referents and of relata belong to given classes

*(Vol. 1, p. 439)*

> *Summary of* *70.
>
> If \(\alpha\) and \(\beta\) are two given classes of classes, a relation \(R\) is said to belong to the class \(\alpha \rightarrow\beta\) if \(\overrightarrow{R}ʻy \in \alpha\) whenever \(y \in\text{ᗡ}ʻR\), and \(\overleftarrow{R}ʻx \in \beta\) whenever \(x\in \text{D}ʻR\). If only one of these conditions is to be imposed, this result is secured by replacing the class involved in the other condition by "\(\text{Cls}\)," since "\(\overrightarrow{R}ʻy \in \text{Cls}\)" always holds, and so does "\(\overleftarrow{R}ʻx \in \text{Cls}\)," and therefore neither imposes any limitation on \(R\). In the most important cases, \(\alpha\) and \(\beta\) are either both cardinal numbers, or one is a cardinal number while the other is \(\text{Cls}\).
>
> In virtue of *37·702·703, the conditions above mentioned as imposed upon \(R\) by membership of \(\alpha \rightarrow \beta\) are equivalent to \[ \overrightarrow{R}ʻʻ\text{ᗡ}ʻR \subset \alpha.\overleftarrow{R}ʻʻ\text{D}ʻR \subset \beta\text{.} \]
>
> This form is used in the definition (*70·01).
>
> …

**Lean reading.** `α → β` is `arrow A B` (Defs, ✱70·01), with `A : Set (Set α)` (classes of
referents) and `B : Set (Set β)` (classes of relata). `R⃗'y`, `R⃖'x` are the values `refs R y`,
`rels R x` of `Rfwd R`, `Rbwd R` (which always exist), so `R⃗''ᗡ'R` is `Rfwd R ʻʻ codom R`,
`D'R⃗` is `dom (Rfwd R)`, `ι'Λ` is `ι Λ`, and `∃!R⃗'y` is `(refs R y).Nonempty`. Each `Cls` is
typically ambiguous and takes the type its position determines. Products of hypotheses are
conjunctions, `R, S ∈ κ` is `R ∈ κ ∧ S ∈ κ`, and the chains of identities ✱70·2·21 are
conjunctions of their links. PM's `γ`, `δ` are `G`, `H`. `C'R` (✱70·57) and `R'''α` together with
`R|S ∈ α → Cls` (✱70·6) force `R` to be homogeneous. Several formulas are misprinted in the
e-text (✱70·01, ✱70·461, ✱70·481, ✱70·5, ✱70·51, ✱70·54, ✱70·6, ✱70·62); PM's intended
statement is formalized, as each docstring explains.

**Status.** proved (all propositions; ✱70·01 definition; ✱70·461, ✱70·481, ✱70·5, ✱70·51,
✱70·54, ✱70·6, ✱70·62 proved (reading): transcription errors of the e-text, see their docstrings)
-/

/-- ✱70·01 (Df). \(\alpha\rightarrow\beta = \breve{R} (\overrightarrow{R}ʻʻ\text{ᗡ}ʻR \subset\alpha. \overleftarrow{R}ʻʻ\text{D}ʻR\subset\beta) \quad\text{Df}\)

**Status.** definition: the e-text prints `R̆` (the converse of `R`) where PM has `R̂` (the class
of relations `R` such that …), as in the Summary of Section C (transcription error). -/
theorem pm70_01 {A : Set (Set α)} {B : Set (Set β)} :
    arrow A B = {R | Rfwd R ʻʻ codom R ⊆ A ∧ Rbwd R ʻʻ dom R ⊆ B} := rfl

/-- ✱70·1. \(\vdash\colon R \in \alpha\rightarrow\beta.\equiv. \overrightarrow{R}ʻʻ\text{ᗡ}ʻR \subset\alpha. \overleftarrow{R}ʻʻ\text{D}ʻR\subset\beta \quad[\text{*20·3.(*70·01)}]\) -/
theorem pm70_1 {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow A B ↔ Rfwd R ʻʻ codom R ⊆ A ∧ Rbwd R ʻʻ dom R ⊆ B := Iff.rfl

/-- ✱70·11. \[\begin{align}\vdash\colon\ldotp R \in\alpha\rightarrow\beta.\equiv: y\in\text{ᗡ}ʻR. \supset_{y}.\overrightarrow{R}ʻy\in\alpha:x\in\text{D}ʻR.&\supset_{x}.\overleftarrow{R}ʻx\in\beta\\ &[\text{*37·702·703.*70·1}]\end{align}\] -/
theorem pm70_11 {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow A B ↔
      (∀ y, y ∈ codom R → refs R y ∈ A) ∧ ∀ x, x ∈ dom R → rels R x ∈ B :=
  mem_arrow_iff

/-- ✱70·12. \(\vdash\colon R \in\alpha\rightarrow\beta.\equiv. \overrightarrow{R}ʻʻ\text{V} \subset \alpha\cup\iotaʻ\Lambda.\overleftarrow{R}ʻʻ\text{V} \subset \beta\cup\iotaʻ\Lambda \quad[\text{*70·1.*53·62·621}]\) -/
theorem pm70_12 {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow A B ↔ Rfwd R ʻʻ V ⊆ A ∪ ι Λ ∧ Rbwd R ʻʻ V ⊆ B ∪ ι Λ := by
  rw [mem_arrow_union]
  refine and_congr ?_ ?_
  · rw [Rfwd, graph_img_sub, V_eq_univ]
    simp only [Set.mem_univ, forall_const]
  · rw [Rbwd, graph_img_sub, V_eq_univ]
    simp only [Set.mem_univ, forall_const]

/-- ✱70·13. \(\vdash\colon\ldotp R \in\alpha\rightarrow\beta.\equiv: (y). \overrightarrow{R}ʻy\in \alpha\cup\iotaʻ\Lambda : (x). \overleftarrow{R}ʻx\in\beta\cup\iotaʻ\Lambda\) -/
theorem pm70_13 {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow A B ↔ (∀ y, refs R y ∈ A ∪ ι Λ) ∧ ∀ x, rels R x ∈ B ∪ ι Λ :=
  mem_arrow_union

/-- ✱70·14. \[\begin{align}&\vdash\colon\colon R\in\alpha\rightarrow\beta. \equiv \colon\ldotp (y): \overrightarrow{R}ʻy\in\alpha .\lor. \overrightarrow{R}ʻy=\Lambda\colon\ldotp(x):\overleftarrow{R}ʻx\in\beta.\lor.\overleftarrow{R}ʻx=\Lambda\\ &[\text{*70·13.*51·236}]\end{align}\] -/
theorem pm70_14 {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow A B ↔
      (∀ y, refs R y ∈ A ∨ refs R y = Λ) ∧ ∀ x, rels R x ∈ B ∨ rels R x = Λ :=
  mem_arrow_union

/-- ✱70·15. \[\begin{align}&\vdash\colon\ldotp R\in\alpha\rightarrow\beta.\equiv: \exists!\overrightarrow{R}ʻy. \supset_{y}.\overrightarrow{R}ʻy\in\alpha : \exists! \overleftarrow{R}ʻx .\supset_{x} .\overleftarrow{R}ʻx\in\beta\\ &[\text{*24·51.*4·6.*70·14}]\end{align}\] -/
theorem pm70_15 {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow A B ↔
      (∀ y, (refs R y).Nonempty → refs R y ∈ A) ∧ ∀ x, (rels R x).Nonempty → rels R x ∈ B :=
  mem_arrow_iff

/-- ✱70·16. \(\vdash\colon R\in\alpha\rightarrow\beta.\equiv. \text{D}ʻ\overrightarrow{R} \subset \alpha\cup\iotaʻ\Lambda.\text{D}ʻ\overleftarrow{R} \subset \beta\cup\iotaʻ\Lambda \quad[\text{*37·78·781.*70·12}]\) -/
theorem pm70_16 {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow A B ↔ dom (Rfwd R) ⊆ A ∪ ι Λ ∧ dom (Rbwd R) ⊆ B ∪ ι Λ := by
  rw [mem_arrow_union, Rfwd, Rbwd, dom_graph_sub, dom_graph_sub]

/-- ✱70·17. \(\vdash\colon\colon \Lambda\in\alpha .\supset\colon\ldotp R\in\alpha\rightarrow\beta.\equiv: (y). \overrightarrow{R}ʻy\in\alpha: \exists!\overleftarrow{R}ʻx.\supset_{x}. \overleftarrow{R}ʻx\in\beta\) -/
theorem pm70_17 {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    Λ ∈ A → (R ∈ arrow A B ↔
      (∀ y, refs R y ∈ A) ∧ ∀ x, (rels R x).Nonempty → rels R x ∈ B) := by
  intro hA
  rw [mem_arrow_iff]
  refine and_congr ⟨fun h y => ?_, fun h y _ => h y⟩ Iff.rfl
  by_cases hy : y ∈ codom R
  · exact h y hy
  · rw [refs_mem_iotaNull.2 hy]
    exact hA

/-- ✱70·171. \[\begin{align}&\vdash\colon\colon \Lambda\in\beta.\supset\colon\ldotp R\in\alpha\rightarrow\beta .\equiv: \exists! \overrightarrow{R}ʻy.\supset_{y}.\overrightarrow{R}ʻy\in\alpha: (x). \overleftarrow{R}ʻx\in\beta\\ &[\text{Proof as in *70·17}]\end{align}\] -/
theorem pm70_171 {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    Λ ∈ B → (R ∈ arrow A B ↔
      (∀ y, (refs R y).Nonempty → refs R y ∈ A) ∧ ∀ x, rels R x ∈ B) := by
  intro hB
  rw [← arrow_cnv, pm70_17 hB, and_comm]
  exact Iff.rfl

/-- ✱70·18. \[\begin{align}&\vdash\colon\colon \Lambda\in\alpha.\Lambda\in\beta.\supset\colon\ldotp R\in\alpha\rightarrow\beta .\equiv:(y). \overrightarrow{R}ʻy\in\alpha:(x).\overleftarrow{R}ʻx\in\beta\\ &[\text{Proof as in *70·17}]\end{align}\] -/
theorem pm70_18 {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    Λ ∈ A ∧ Λ ∈ B → (R ∈ arrow A B ↔ (∀ y, refs R y ∈ A) ∧ ∀ x, rels R x ∈ B) := by
  rintro ⟨hA, hB⟩
  rw [pm70_17 hA]
  refine and_congr Iff.rfl ⟨fun h x => ?_, fun h x _ => h x⟩
  by_cases hx : (rels R x).Nonempty
  · exact h x hx
  · rw [eqNull_iff.2 hx]
    exact hB

private theorem nonempty_mem_union_iota {A : Set (Set α)} {X : Set α} (hX : X.Nonempty) :
    X ∈ A ↔ X ∈ A ∪ ι Λ := by
  refine ⟨Or.inl, fun h => h.elim id fun h' => absurd hX (eqNull_iff.1 h')⟩

private theorem nonempty_mem_diff_iota {A : Set (Set α)} {X : Set α} (hX : X.Nonempty) :
    X ∈ A ↔ X ∈ A \ ι Λ :=
  ⟨fun h => ⟨h, fun h' => eqNull_iff.1 h' hX⟩, fun h => h.1⟩

/-- ✱70·2. \(\vdash.\alpha\rightarrow\beta=(\alpha\cup\iotaʻ\Lambda)\rightarrow\beta=\alpha\rightarrow(\beta\cup\iotaʻ\Lambda)=(\alpha\cup\iotaʻ\Lambda)\rightarrow(\beta\cup\iotaʻ\Lambda)\) -/
theorem pm70_2 {A : Set (Set α)} {B : Set (Set β)} :
    (arrow A B = arrow (A ∪ ι Λ) B ∧ arrow (A ∪ ι Λ) B = arrow A (B ∪ ι Λ)) ∧
      arrow A (B ∪ ι Λ) = arrow (A ∪ ι Λ) (B ∪ ι Λ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply arrow_congr <;> intro X hX <;>
    first
    | exact Iff.rfl
    | exact nonempty_mem_union_iota hX
    | exact (nonempty_mem_union_iota hX).symm

/-- ✱70·21. \(\vdash.\alpha\rightarrow\beta=(\alpha-\iotaʻ\Lambda)\rightarrow\beta=\alpha\rightarrow(\beta-\iotaʻ\Lambda)=(\alpha-\iotaʻ\Lambda)\rightarrow(\beta-\iotaʻ\Lambda)\) -/
theorem pm70_21 {A : Set (Set α)} {B : Set (Set β)} :
    (arrow A B = arrow (A \ ι Λ) B ∧ arrow (A \ ι Λ) B = arrow A (B \ ι Λ)) ∧
      arrow A (B \ ι Λ) = arrow (A \ ι Λ) (B \ ι Λ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply arrow_congr <;> intro X hX <;>
    first
    | exact Iff.rfl
    | exact nonempty_mem_diff_iota hX
    | exact (nonempty_mem_diff_iota hX).symm

/-- ✱70·22. \(\vdash.\beta\rightarrow\alpha=\text{Cnv}ʻʻ(\alpha\rightarrow\beta)\) -/
theorem pm70_22 {A : Set (Set α)} {B : Set (Set β)} : arrow B A = Cnv ʻʻ arrow A B := by
  ext Q
  constructor
  · intro h
    exact ⟨Q˘, arrow_cnv.2 h, Cnv_iff.2 rfl⟩
  · rintro ⟨R, hR, hc⟩
    rw [Cnv_iff.1 hc]
    exact arrow_cnv.2 hR

/-- ✱70·3. \(\vdash.\alpha\subset\gamma.\beta\subset\delta.\supset.\alpha\rightarrow\beta\subset\gamma\rightarrow\delta\)

In this and the following propositions PM's `γ`, `δ` (classes of classes) are `G`, `H`. -/
theorem pm70_3 {A G : Set (Set α)} {B H : Set (Set β)} :
    A ⊆ G ∧ B ⊆ H → arrow A B ⊆ arrow G H := by
  rintro ⟨hAG, hBH⟩ R ⟨h1, h2⟩
  exact ⟨h1.trans hAG, h2.trans hBH⟩

/-- ✱70·31. \(\vdash.(\alpha\rightarrow\beta)\cap(\gamma\rightarrow\delta)=(\alpha\cap\gamma)\rightarrow(\beta\cap\delta)\) -/
theorem pm70_31 {A G : Set (Set α)} {B H : Set (Set β)} :
    arrow A B ∩ arrow G H = arrow (A ∩ G) (B ∩ H) := by
  ext R
  simp only [Set.mem_inter_iff, pm70_1, Set.subset_inter_iff]
  tauto

/-- ✱70·32. \(\vdash.(\alpha\rightarrow\beta)\cup(\gamma\rightarrow\delta)\subset(\alpha\cup\gamma)\rightarrow(\beta\cup\delta)\) -/
theorem pm70_32 {A G : Set (Set α)} {B H : Set (Set β)} :
    arrow A B ∪ arrow G H ⊆ arrow (A ∪ G) (B ∪ H) := by
  rintro R (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact ⟨h1.trans Set.subset_union_left, h2.trans Set.subset_union_left⟩
  · exact ⟨h1.trans Set.subset_union_right, h2.trans Set.subset_union_right⟩

/-- ✱70·4. \(\vdash.\alpha\rightarrow\text{Cls}=\hat{R}(\overrightarrow{R}ʻʻ\text{ᗡ}ʻR\subset\alpha)\) -/
theorem pm70_4 {A : Set (Set α)} :
    arrow A (Cls : Set (Set β)) = {R : α → β → Prop | Rfwd R ʻʻ codom R ⊆ A} := by
  ext R
  exact mem_arrow_left.trans graph_img_sub.symm

/-- ✱70·41. \(\vdash.\text{Cls}\rightarrow\beta=\hat{R}(\overleftarrow{R}ʻʻ\text{D}ʻR\subset\beta) \quad[\text{Proof as in *70·4}]\) -/
theorem pm70_41 {B : Set (Set β)} :
    arrow (Cls : Set (Set α)) B = {R : α → β → Prop | Rbwd R ʻʻ dom R ⊆ B} := by
  ext R
  exact mem_arrow_right.trans graph_img_sub.symm

/-- ✱70·42. \(\vdash.\alpha\rightarrow\beta=(\alpha\rightarrow\text{Cls})\cap(\text{Cls}\rightarrow\beta) \quad[\text{*70·4·41}]\) -/
theorem pm70_42 {A : Set (Set α)} {B : Set (Set β)} :
    arrow A B = arrow A Cls ∩ arrow Cls B := arrow_eq_inter

/-- ✱70·43. \(\vdash\colon\ldotp R\in\alpha\rightarrow\text{Cls}.\equiv:y\in\text{ᗡ}ʻR.\supset_{y}.\overrightarrow{R}ʻy\in\alpha \quad[\text{As in *70·11}]\) -/
theorem pm70_43 {A : Set (Set α)} {R : α → β → Prop} :
    R ∈ arrow A Cls ↔ ∀ y, y ∈ codom R → refs R y ∈ A := mem_arrow_left

/-- ✱70·431. \(\vdash\colon\ldotp R\in\text{Cls}\rightarrow\beta.\equiv:x\in\text{D}ʻR.\supset_{x}.\overleftarrow{R}ʻx\in\beta \quad[\text{As in *70·11}]\) -/
theorem pm70_431 {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow Cls B ↔ ∀ x, x ∈ dom R → rels R x ∈ B := mem_arrow_right

/-- ✱70·44. \(\vdash:R\in\alpha\rightarrow\text{Cls}.\equiv.\overrightarrow{R}ʻʻ\text{V}\subset\alpha\cup\iotaʻ\Lambda \quad[\text{As in *70·12}]\) -/
theorem pm70_44 {A : Set (Set α)} {R : α → β → Prop} :
    R ∈ arrow A Cls ↔ Rfwd R ʻʻ V ⊆ A ∪ ι Λ := by
  rw [mem_arrow_left, ← all_refs_iff, Rfwd, graph_img_sub, V_eq_univ]
  simp only [Set.mem_univ, forall_const]

/-- ✱70·441. \(\vdash:R\in\text{Cls}\rightarrow\beta.\equiv.\overleftarrow{R}ʻʻ\text{V}\subset\beta\cup\iotaʻ\Lambda \quad[\text{As in *70·12}]\) -/
theorem pm70_441 {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow Cls B ↔ Rbwd R ʻʻ V ⊆ B ∪ ι Λ := by
  rw [← arrow_cnv]
  exact pm70_44

/-- ✱70·45. \(\vdash:R\in\alpha\rightarrow\text{Cls}.\equiv.(y).\overrightarrow{R}ʻy\in\alpha\cup\iotaʻ\Lambda \quad[\text{As in *70·13}]\) -/
theorem pm70_45 {A : Set (Set α)} {R : α → β → Prop} :
    R ∈ arrow A Cls ↔ ∀ y, refs R y ∈ A ∪ ι Λ := by
  rw [mem_arrow_left, all_refs_iff]

/-- ✱70·451. \(\vdash:R\in\text{Cls}\rightarrow\beta.\equiv.(x).\overleftarrow{R}ʻx\in\beta\cup\iotaʻ\Lambda \quad[\text{As in *70·13}]\) -/
theorem pm70_451 {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow Cls B ↔ ∀ x, rels R x ∈ B ∪ ι Λ := by
  rw [← arrow_cnv]
  exact pm70_45

/-- ✱70·46. \(\vdash\colon\ldotp R\in\alpha\rightarrow\text{Cls}.\equiv:(y):\overrightarrow{R}ʻy\in\alpha.\lor.\overrightarrow{R}ʻy=\Lambda \quad[\text{As in *70·14}]\) -/
theorem pm70_46 {A : Set (Set α)} {R : α → β → Prop} :
    R ∈ arrow A Cls ↔ ∀ y, refs R y ∈ A ∨ refs R y = Λ := pm70_45

/-- ✱70·461. \(\vdash\colon\ldotp R\in\text{Cls}\rightarrow\beta.\equiv:(x):\overleftarrow{R}ʻx\in\beta.\lor.\overleftarrow{R}ʻx=\lambda \quad[\text{As in *70·14}]\)

**Status.** proved (reading): the e-text prints `λ` for `Λ` in `R⃖'x = Λ` (transcription error; cf.
✱70·14, of which this is the analogue). -/
theorem pm70_461 {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow Cls B ↔ ∀ x, rels R x ∈ B ∨ rels R x = Λ := pm70_451

/-- ✱70·47. \(\vdash\colon\ldotp R\in\alpha\rightarrow\text{Cls}.\equiv:\exists!\overrightarrow{R}ʻy.\supset_{y}.\overrightarrow{R}ʻy\in\alpha \quad[\text{As in *70·15}]\) -/
theorem pm70_47 {A : Set (Set α)} {R : α → β → Prop} :
    R ∈ arrow A Cls ↔ ∀ y, (refs R y).Nonempty → refs R y ∈ A := mem_arrow_left

/-- ✱70·471. \(\vdash\colon\ldotp R\in\text{Cls}\rightarrow\beta.\equiv:\exists!\overleftarrow{R}ʻx.\supset_{x}.\overleftarrow{R}ʻx\in\beta \quad[\text{As in *70·15}]\) -/
theorem pm70_471 {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow Cls B ↔ ∀ x, (rels R x).Nonempty → rels R x ∈ B := mem_arrow_right

/-- ✱70·48. \(\vdash\colon R\in\alpha\rightarrow\text{Cls}.\equiv.\text{D}ʻ\overrightarrow{R}\subset\alpha\cup\iotaʻ\Lambda \quad[\text{As in *70·16}]\) -/
theorem pm70_48 {A : Set (Set α)} {R : α → β → Prop} :
    R ∈ arrow A Cls ↔ dom (Rfwd R) ⊆ A ∪ ι Λ := by
  rw [pm70_45, Rfwd, dom_graph_sub]

/-- ✱70·481. \(\vdash\colon R\in\text{Cls}\rightarrow\beta.\equiv.\text{D}ʻ\overrightarrow{R}\subset\beta\cup\iotaʻ\Lambda \quad[\text{As in *70·16}]\)

**Status.** proved (reading): the e-text prints `D'R⃗` for `D'R⃖` (as printed the two sides are of
different types, `D'R⃗` being a class of classes of referents and `β` a class of classes of
relata); this is the analogue of ✱70·16's second half, as the reference "As in ✱70·16" shows
(transcription error). -/
theorem pm70_481 {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow Cls B ↔ dom (Rbwd R) ⊆ B ∪ ι Λ := by
  rw [pm70_451, Rbwd, dom_graph_sub]

/-- ✱70·5. \(\vdash.\text{Cls}\rightarrow\alpha=\text{Cnv}ʻʻ(\rightarrow\alpha\text{Cls}).\alpha\rightarrow\text{Cls}=\text{Cnv}ʻʻ(\text{Cls}\rightarrow\alpha) \quad[\text{*70·22}]\)

**Status.** proved (reading): the e-text prints `Cnv''(→α Cls)` for `Cnv''(α → Cls)` in the first
conjunct (transcription error; the reference is ✱70·22). The two signs `Cls` are typically
ambiguous; both are taken at the type `β`. -/
theorem pm70_5 {A : Set (Set α)} :
    arrow (Cls : Set (Set β)) A = Cnv ʻʻ arrow A Cls ∧
      arrow A (Cls : Set (Set β)) = Cnv ʻʻ arrow Cls A :=
  ⟨pm70_22, pm70_22⟩

/-- ✱70·51. \(\vdash\colon\ldotp \xi,\eta\in\alpha.\supset_{\xi,\eta}.\xi\cap\eta\in\alpha\cup\iotaʻ\Lambda:\supset:R,S\in\rightarrow\alpha\text{Cls}.\supset.R\dot{\cap}S\in\alpha\rightarrow\text{Cls}\)

**Status.** proved (reading): the e-text prints `R, S ∈ →α Cls` for `R, S ∈ α → Cls`
(transcription error, as in ✱70·5; the conclusion and the proof have `α → Cls`). -/
theorem pm70_51 {A : Set (Set α)} {R S : α → β → Prop} :
    (∀ ξ η, ξ ∈ A ∧ η ∈ A → ξ ∩ η ∈ A ∪ ι Λ) →
      (R ∈ arrow A Cls ∧ S ∈ arrow A Cls → R ⩀ S ∈ arrow A Cls) := by
  rintro hA ⟨hR, hS⟩
  rw [pm70_45] at hR hS ⊢
  intro y
  have e : refs (R ⩀ S) y = refs R y ∩ refs S y := rfl
  rw [e]
  rcases hR y with h1 | h1
  · rcases hS y with h2 | h2
    · exact hA _ _ ⟨h1, h2⟩
    · right
      show refs R y ∩ refs S y = Λ
      rw [show refs S y = Λ from h2, eqNull_iff]
      rintro ⟨x, -, hx⟩
      exact not_mem_Null' x hx
  · right
    show refs R y ∩ refs S y = Λ
    rw [show refs R y = Λ from h1, eqNull_iff]
    rintro ⟨x, hx, -⟩
    exact not_mem_Null' x hx

/-- ✱70·52. \[\begin{align}&\vdash\colon\ldotp\xi,\eta\in\beta.\supset_{\xi,\eta}.\xi\cap\eta\in\beta\cup\iotaʻ\Lambda:\supset:R,\,S\in\text{Cls}\rightarrow\beta.\supset.R\dot{\cap}S\in\text{Cls}\rightarrow\beta\\ &[\text{Proof as in *70·51}]\end{align}\] -/
theorem pm70_52 {B : Set (Set β)} {R S : α → β → Prop} :
    (∀ ξ η, ξ ∈ B ∧ η ∈ B → ξ ∩ η ∈ B ∪ ι Λ) →
      (R ∈ arrow Cls B ∧ S ∈ arrow Cls B → R ⩀ S ∈ arrow Cls B) := by
  rintro hB ⟨hR, hS⟩
  rw [← arrow_cnv] at hR hS ⊢
  exact pm70_51 hB ⟨hR, hS⟩

/-- ✱70·53. \[\begin{align}\vdash\colon\ldotp\xi,\eta\in\alpha.\supset_{\xi,\eta}.\xi\cap\eta\in\alpha\cup\iotaʻ\Lambda:\xi,\eta\in&\beta.\supset_{\xi,\eta}.\xi\cap\eta\in\beta\cup\iotaʻ\Lambda:\supset:\\ &R,S\in\alpha\rightarrow\beta.\supset.R\dot{\cap}S\in\alpha\rightarrow\beta\end{align}\] -/
theorem pm70_53 {A : Set (Set α)} {B : Set (Set β)} {R S : α → β → Prop} :
    (∀ ξ η, ξ ∈ A ∧ η ∈ A → ξ ∩ η ∈ A ∪ ι Λ) ∧ (∀ ξ η, ξ ∈ B ∧ η ∈ B → ξ ∩ η ∈ B ∪ ι Λ) →
      (R ∈ arrow A B ∧ S ∈ arrow A B → R ⩀ S ∈ arrow A B) := by
  rintro ⟨hA, hB⟩ ⟨hR, hS⟩
  rw [arrow_eq_inter] at hR hS ⊢
  exact ⟨pm70_51 hA ⟨hR.1, hS.1⟩, pm70_52 hB ⟨hR.2, hS.2⟩⟩

/-- ✱70·54. \(\vdash:\text{ᗡ}ʻR\cap\text{ᗡ}ʻS=\lambda.R,S\in\alpha\rightarrow\text{Cls}.\supset.R\unicode{x228d}S\in\alpha\rightarrow\text{Cls}\)

**Status.** proved (reading): the e-text prints `λ` for `Λ` in `ᗡ'R ∩ ᗡ'S = Λ` (transcription
error; the Summary of ✱70 and the proof have `Λ`). -/
theorem pm70_54 {A : Set (Set α)} {R S : α → β → Prop} :
    codom R ∩ codom S = Λ ∧ (R ∈ arrow A Cls ∧ S ∈ arrow A Cls) → R ⊍ S ∈ arrow A Cls := by
  rintro ⟨hd, hR, hS⟩
  rw [mem_arrow_left] at hR hS ⊢
  have hd' : ∀ y, y ∈ codom R → y ∈ codom S → False := fun y h1 h2 =>
    not_mem_Null' y (hd ▸ ⟨h1, h2⟩)
  rintro y ⟨x, hx | hx⟩
  · have e : refs (R ⊍ S) y = refs R y := by
      ext z
      exact ⟨fun h => h.elim id fun h' => absurd ⟨z, h'⟩ (hd' y ⟨x, hx⟩), Or.inl⟩
    rw [e]
    exact hR y ⟨x, hx⟩
  · have e : refs (R ⊍ S) y = refs S y := by
      ext z
      exact ⟨fun h => h.elim (fun h' => absurd ⟨x, hx⟩ (hd' y ⟨z, h'⟩)) id, Or.inr⟩
    rw [e]
    exact hS y ⟨x, hx⟩

/-- ✱70·55. \[\begin{align}&\vdash:\text{D}ʻR\cap\text{D}ʻS=\Lambda.R,S\in\text{Cls}\rightarrow\beta.\supset.R\unicode{x228d}S\in\text{Cls}\rightarrow\beta\\ &[\text{Proof as in *70·54}]\end{align}\] -/
theorem pm70_55 {B : Set (Set β)} {R S : α → β → Prop} :
    dom R ∩ dom S = Λ ∧ (R ∈ arrow Cls B ∧ S ∈ arrow Cls B) → R ⊍ S ∈ arrow Cls B := by
  rintro ⟨hd, hR, hS⟩
  rw [← arrow_cnv] at hR hS ⊢
  exact pm70_54 ⟨hd, hR, hS⟩

/-- ✱70·56. \[\begin{align}&\vdash:\text{D}ʻR\cap\text{D}ʻS=\Lambda.\text{ᗡ}ʻR\cap\text{ᗡ}ʻS=\Lambda.R,S\in\alpha\rightarrow\beta.\supset.R\unicode{x228d}S\in\alpha\rightarrow\beta\\ &[\text{*70·54·55·42}]\end{align}\] -/
theorem pm70_56 {A : Set (Set α)} {B : Set (Set β)} {R S : α → β → Prop} :
    (dom R ∩ dom S = Λ ∧ codom R ∩ codom S = Λ) ∧ (R ∈ arrow A B ∧ S ∈ arrow A B) →
      R ⊍ S ∈ arrow A B := by
  rintro ⟨⟨hd, hc⟩, hR, hS⟩
  rw [arrow_eq_inter] at hR hS ⊢
  exact ⟨pm70_54 ⟨hc, hR.1, hS.1⟩, pm70_55 ⟨hd, hR.2, hS.2⟩⟩

/-- ✱70·57. \(\vdash:CʻR\cap\text{C}ʻS=\Lambda.R,\,S\in\alpha\rightarrow\beta.\supset.R\unicode{x228d}S\in\alpha\rightarrow\beta\) -/
theorem pm70_57 {A B : Set (Set α)} {R S : α → α → Prop} :
    fld R ∩ fld S = Λ ∧ (R ∈ arrow A B ∧ S ∈ arrow A B) → R ⊍ S ∈ arrow A B := by
  rintro ⟨hf, hR, hS⟩
  have hf' : ∀ x, x ∈ fld R → x ∈ fld S → False := fun x h1 h2 =>
    not_mem_Null' x (hf ▸ ⟨h1, h2⟩)
  refine pm70_56 ⟨⟨?_, ?_⟩, hR, hS⟩ <;> rw [eqNull_iff]
  · rintro ⟨x, ⟨y, hy⟩, ⟨z, hz⟩⟩
    exact hf' x ⟨y, Or.inl hy⟩ ⟨z, Or.inl hz⟩
  · rintro ⟨x, ⟨y, hy⟩, ⟨z, hz⟩⟩
    exact hf' x ⟨y, Or.inr hy⟩ ⟨z, Or.inr hz⟩

/-- ✱70·6. \(\vdash:S\in\alpha\rightarrow\text{Cls}.Rʻʻʻ\alpha\supset\alpha\cup\iotaʻ\Lambda.\supset.R\mid S\in\alpha\rightarrow\text{Cls}\)

**Status.** proved (reading): the e-text prints `R'''α ⊃ α ∪ ι'Λ` for `R'''α ⊂ α ∪ ι'Λ`
(transcription error: `⊃` between classes is not significant, and the proof needs the inclusion
`R'''α ⊂ α ∪ ι'Λ`; cf. ✱70·61). Since `S ∈ α → Cls` and `R|S ∈ α → Cls` with the same `α`,
the referents of `R` and of `S` are of one type, and `R'''α` requires `R` to be homogeneous. -/
theorem pm70_6 {A : Set (Set α)} {R : α → α → Prop} {S : α → β → Prop} :
    S ∈ arrow A Cls ∧ R ʻʻʻ A ⊆ A ∪ ι Λ → R ⨾ S ∈ arrow A Cls := by
  rintro ⟨hS, hR⟩
  rw [pm70_45] at hS ⊢
  intro z
  have e : refs (R ⨾ S) z = R ʻʻ refs S z := by
    ext x
    exact ⟨fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩, fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩⟩
  rw [e]
  rcases hS z with h | h
  · exact hR ⟨refs S z, h, rfl⟩
  · right
    show R ʻʻ refs S z = Λ
    rw [show refs S z = Λ from h, img_Null]

/-- ✱70·61. \(\vdash:R\in\text{Cls}\rightarrow\beta.\breve{S}ʻʻʻ\beta\subset\beta\cup\iotaʻ\Lambda.\supset.R\mid S\in\text{Cls}\rightarrow\beta \quad[\text{As in *70·6}]\) -/
theorem pm70_61 {B : Set (Set β)} {R : α → β → Prop} {S : β → β → Prop} :
    R ∈ arrow Cls B ∧ S˘ ʻʻʻ B ⊆ B ∪ ι Λ → R ⨾ S ∈ arrow Cls B := by
  rintro ⟨hR, hS⟩
  rw [pm70_451] at hR ⊢
  intro x
  have e : rels (R ⨾ S) x = S˘ ʻʻ rels R x := by
    ext z
    exact Iff.rfl
  rw [e]
  rcases hR x with h | h
  · exact hS ⟨rels R x, h, rfl⟩
  · right
    show S˘ ʻʻ rels R x = Λ
    rw [show rels R x = Λ from h, img_Null]

/-- ✱70·62. \(\vdash:R\in\alpha\rightarrow\text{Cls}.\supset.R\upharpoonright\in\alpha\rightarrow\text{Cls}\)

**Status.** proved (reading): the e-text omits the `γ` of `R ↾ γ` (transcription error; the
Summary of ✱70, the proof, and ✱71·26, which cites this proposition, have `R ↾ γ`). PM's `γ` is
`G`. -/
theorem pm70_62 {A : Set (Set α)} {R : α → β → Prop} {G : Set β} :
    R ∈ arrow A Cls → R ↾ G ∈ arrow A Cls := by
  intro hR
  rw [mem_arrow_left] at hR ⊢
  rintro y ⟨x, hx, hy⟩
  have e : refs (R ↾ G) y = refs R y := by
    ext z
    exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩
  rw [e]
  exact hR y ⟨x, hx⟩

/-- ✱70·63. \(\vdash:R\in\text{Cls}\rightarrow\beta.\supset.\delta\upharpoonleft R\in\text{Cls}\rightarrow\beta \quad[\text{As in *70·62}]\)

PM's `δ` is `H`. -/
theorem pm70_63 {B : Set (Set β)} {R : α → β → Prop} {H : Set α} :
    R ∈ arrow Cls B → H ◁ R ∈ arrow Cls B := by
  intro hR
  rw [mem_arrow_right] at hR ⊢
  rintro x ⟨y, hx, hy⟩
  have e : rels (H ◁ R) x = rels R x := by
    ext z
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  rw [e]
  exact hR x ⟨y, hy⟩



private theorem desc_cres_eq {R : α → β → Prop} {B : Set β} {y z : β} :
    Desc (R ↾ B) y (fun b => Desc (R ↾ B) z (fun c => b = c)) ↔
      (y ∈ B ∧ z ∈ B) ∧ Desc R y (fun b => Desc R z (fun c => b = c)) := by
  rw [desc_eq_desc_iff, desc_eq_desc_iff]
  constructor
  · rintro ⟨b, hb, hc⟩
    have hy : y ∈ B := ((hb b).2 rfl).2
    have hz : z ∈ B := ((hc b).2 rfl).2
    exact ⟨⟨hy, hz⟩, b, fun x => ⟨fun h => (hb x).1 ⟨h, hy⟩, fun h => ((hb x).2 h).1⟩,
      fun x => ⟨fun h => (hc x).1 ⟨h, hz⟩, fun h => ((hc x).2 h).1⟩⟩
  · rintro ⟨⟨hy, hz⟩, b, hb, hc⟩
    exact ⟨b, fun x => ⟨fun h => (hb x).1 h.1, fun h => ⟨(hb x).2 h, hy⟩⟩,
      fun x => ⟨fun h => (hc x).1 h.1, fun h => ⟨(hc x).2 h, hz⟩⟩⟩

private theorem not_desc_of_not_codom {R : α → β → Prop} {y : β} {ψ : α → Prop}
    (hy : y ∉ codom R) : ¬ Desc R y ψ := fun h => hy (mem_codom_of_edesc (edesc_of_desc h))

/-!
## [✱71] One-many, many-one, and one-one relations

*(Vol. 1, p. 446)*

> *Summary of* *71.
>
> In this number we shall be concerned with the more elementary properties of one-many, many-one, and one-one relations. These properties are very numerous and very important. The properties of many-one relations (*i.e.* of relations belonging to the class \(\text{Cls} \rightarrow 1\)) result from those of one-many relations by means of *70·5, whence it follows that many-one relations are the converses of one-many relations. It is thus only necessary to interchange \(R\) and \(\breve{R}\), \(\text{D}\) and \(\text{ᗡ}\), \(\overrightarrow{R}\) and \(\overleftarrow{R}\) in order to obtain a property of a many-one relation from a property of a one-many relation. Or we may repeat the various steps of any proof, making the above interchanges at every step, and the analogous proposition will result. For this reason, in what follows, we shall omit all proofs of properties of many-one relations, confining ourselves to proving the analogous properties of one-many relations.
>
> …

**Lean reading.** `1 → Cls`, `Cls → 1`, `1 → 1` are `arrow one Cls`, `arrow Cls one`,
`arrow one one` (characterized by `mem_arrow_one_Cls`, … as ✱71·17·171·172). A descriptive
function `R'y` (`R̆'x`) is `Desc R y ψ` (`Desc R˘ x ψ`), with the smallest scope; `R'y = S'z` is
`Desc R y (fun b => Desc S z (fun c => b = c))`, `E!R'y` is `EDesc R y`, `E!!R''β` is `EE R B`,
and `ῐ'α` is `Desc iota˘ A ψ`. `Rl'R`, `Cl'α`, `Cl ex'α` are the values `rl R`, `cl A`, `clEx A`,
and `R_∈` is `imgRel R`. As PM says in the Summary, each many-one proposition is the one-many
proposition for `R̆`, and is proved by applying it to `R˘`. Where a real or apparent variable
occurs both as a referent and as a relatum (✱71·182, ✱71·532), `R` is homogeneous. The e-text
numbers ✱71·28 `*71.28.` (a full stop for the centred dot) and prints ✱71·341 as a plain paragraph
(not in bold).

**Status.** proved (all propositions; ✱71·01, ✱71·02, ✱71·03
proved (reading): `R̆` printed for `R̂`, as in ✱70·01)
-/

/-- ✱71·01. \(\vdash.1\rightarrow \text{Cls}=\breve{R}(\overrightarrow{R}ʻʻ\text{ᗡ}ʻR\subset 1) \quad[\text{*70·4}]\)

**Status.** proved (reading): the e-text prints `R̆` (the converse of `R`) for `R̂` (the class of
relations `R` such that …), as in ✱70·01 (transcription error). -/
theorem pm71_01 : (arrow one Cls : Set (α → β → Prop)) = {R | Rfwd R ʻʻ codom R ⊆ one} :=
  pm70_4

/-- ✱71·02. \(\vdash.\text{Cls}\rightarrow 1=\breve{R}(\overleftarrow{R}ʻʻ\text{D}ʻR\subset 1) \quad[\text{*70·41}]\)

**Status.** proved (reading): `R̆` printed for `R̂`, as in ✱71·01 (transcription error). -/
theorem pm71_02 : (arrow Cls one : Set (α → β → Prop)) = {R | Rbwd R ʻʻ dom R ⊆ one} :=
  pm70_41

/-- ✱71·03. \(\vdash.1\rightarrow 1=\breve{R}(\overrightarrow{R}ʻʻ\text{ᗡ}ʻR\subset 1.\overleftarrow{R}ʻʻ\text{D}ʻR\subset 1) \quad[\text{*20·2.(*70·01)}]\)

**Status.** proved (reading): `R̆` printed for `R̂`, as in ✱71·01 (transcription error). -/
theorem pm71_03 :
    (arrow one one : Set (α → β → Prop)) =
      {R | Rfwd R ʻʻ codom R ⊆ one ∧ Rbwd R ʻʻ dom R ⊆ one} := rfl

/-- ✱71·04. \(\vdash.1\rightarrow 1=(1\rightarrow \text{Cls})\cap (\text{Cls}\rightarrow 1) \quad[\text{*70·42}]\) -/
theorem pm71_04 : (arrow one one : Set (α → β → Prop)) = arrow one Cls ∩ arrow Cls one :=
  pm70_42

/-- ✱71·1. \(\vdash:R\in 1\rightarrow \text{Cls}.\equiv.\overrightarrow{R}ʻʻ\text{ᗡ}ʻR\subset 1 \quad[\text{*20·33.*71·01}]\) -/
theorem pm71_1 {R : α → β → Prop} : R ∈ arrow one Cls ↔ Rfwd R ʻʻ codom R ⊆ one :=
  Set.ext_iff.1 pm70_4 R

/-- ✱71·101. \(\vdash:R\in \text{Cls}\rightarrow 1.\equiv.\overleftarrow{R}ʻʻ\text{D}ʻR\subset 1 \quad[\text{*20·33.*71·02}]\) -/
theorem pm71_101 {R : α → β → Prop} : R ∈ arrow Cls one ↔ Rbwd R ʻʻ dom R ⊆ one :=
  Set.ext_iff.1 pm70_41 R

/-- ✱71·102. \(\vdash:R\in 1\rightarrow 1.\equiv.\overrightarrow{R}ʻʻ\text{ᗡ}ʻR\subset 1.\overleftarrow{R}ʻʻ\text{D}ʻR\subset 1 \quad[\text{*20·33.*71·03}]\) -/
theorem pm71_102 {R : α → β → Prop} :
    R ∈ arrow one one ↔ Rfwd R ʻʻ codom R ⊆ one ∧ Rbwd R ʻʻ dom R ⊆ one := Iff.rfl

/-- ✱71·103. \(\vdash:R\in 1\rightarrow 1.\equiv.R\in 1\rightarrow \text{Cls}.R\in \text{Cls}\rightarrow 1 \quad[\text{*22·33.*71·04}]\) -/
theorem pm71_103 {R : α → β → Prop} :
    R ∈ arrow one one ↔ R ∈ arrow one Cls ∧ R ∈ arrow Cls one := one_one_iff

/-- ✱71·11. \(\vdash:R\in 1\rightarrow \text{Cls}.\equiv.\overrightarrow{R}ʻʻ\text{V}\subset 1\cup \iotaʻ\Lambda \quad[\text{*70·44}]\) -/
theorem pm71_11 {R : α → β → Prop} : R ∈ arrow one Cls ↔ Rfwd R ʻʻ V ⊆ one ∪ ι Λ := pm70_44

/-- ✱71·111. \(\vdash:R\in \text{Cls}\rightarrow 1.\equiv.\overleftarrow{R}ʻʻ\text{V}\subset 1\cup \iotaʻ\Lambda \quad[\text{*70·441}]\) -/
theorem pm71_111 {R : α → β → Prop} : R ∈ arrow Cls one ↔ Rbwd R ʻʻ V ⊆ one ∪ ι Λ := pm70_441

/-- ✱71·112. \(\vdash:R\in 1\rightarrow 1.\equiv.\overrightarrow{R}ʻʻ\text{V}\subset 1\cup \iotaʻ\Lambda.\overleftarrow{R}ʻʻ\text{V}\subset 1\cup \iotaʻ\Lambda \quad[\text{*70·12}]\) -/
theorem pm71_112 {R : α → β → Prop} :
    R ∈ arrow one one ↔ Rfwd R ʻʻ V ⊆ one ∪ ι Λ ∧ Rbwd R ʻʻ V ⊆ one ∪ ι Λ := pm70_12

/-- ✱71·12. \(\vdash:R\in 1\rightarrow \text{Cls}.\equiv.(y).\overrightarrow{R}ʻy\in 1\cup \iotaʻ\Lambda \quad[\text{*70·45}]\) -/
theorem pm71_12 {R : α → β → Prop} : R ∈ arrow one Cls ↔ ∀ y, refs R y ∈ one ∪ ι Λ := pm70_45

/-- ✱71·121. \(\vdash:R\in \text{Cls}\rightarrow 1.\equiv.(x).\overleftarrow{R}ʻx\in 1\cup \iotaʻ\Lambda \quad[\text{*70·451}]\) -/
theorem pm71_121 {R : α → β → Prop} : R ∈ arrow Cls one ↔ ∀ x, rels R x ∈ one ∪ ι Λ :=
  pm70_451

/-- ✱71·122. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\equiv:(y).\overrightarrow{R}ʻy\in 1\cup \iotaʻ\Lambda:(x).\overleftarrow{R}ʻx\in 1\cup \iotaʻ\Lambda \quad[\text{*70·13}]\) -/
theorem pm71_122 {R : α → β → Prop} :
    R ∈ arrow one one ↔ (∀ y, refs R y ∈ one ∪ ι Λ) ∧ ∀ x, rels R x ∈ one ∪ ι Λ := pm70_13

/-- ✱71·13. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\equiv:(y):\overrightarrow{R}ʻy\in 1.\lor.\overrightarrow{R}ʻy=\Lambda \quad[\text{*70·46}]\) -/
theorem pm71_13 {R : α → β → Prop} :
    R ∈ arrow one Cls ↔ ∀ y, refs R y ∈ one ∨ refs R y = Λ := pm70_46

/-- ✱71·131. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\equiv:(x):\overleftarrow{R}ʻx\in 1.\lor.\overleftarrow{R}ʻx=\Lambda \quad[\text{*70·461}]\) -/
theorem pm71_131 {R : α → β → Prop} :
    R ∈ arrow Cls one ↔ ∀ x, rels R x ∈ one ∨ rels R x = Λ := pm70_461

/-- ✱71·132. \(\vdash\colon\colon R\in 1\rightarrow 1.\equiv\colon\ldotp (y):\overrightarrow{R}ʻy\in 1.\lor.\overrightarrow{R}ʻy=\Lambda\colon\ldotp (x):\overleftarrow{R}ʻx\in 1.\lor.\overleftarrow{R}ʻx=\Lambda \quad[\text{*70·14}]\) -/
theorem pm71_132 {R : α → β → Prop} :
    R ∈ arrow one one ↔
      (∀ y, refs R y ∈ one ∨ refs R y = Λ) ∧ ∀ x, rels R x ∈ one ∨ rels R x = Λ := pm70_14

/-- ✱71·14. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\equiv:\exists !\overrightarrow{R}ʻy.\supset_{y}.\overrightarrow{R}ʻy\in 1 \quad[\text{*70·47}]\) -/
theorem pm71_14 {R : α → β → Prop} :
    R ∈ arrow one Cls ↔ ∀ y, (refs R y).Nonempty → refs R y ∈ one := pm70_47

/-- ✱71·141. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\equiv:\exists !\overleftarrow{R}ʻx.\supset_{x}.\overleftarrow{R}ʻx\in 1 \quad[\text{*70·471}]\) -/
theorem pm71_141 {R : α → β → Prop} :
    R ∈ arrow Cls one ↔ ∀ x, (rels R x).Nonempty → rels R x ∈ one := pm70_471

/-- ✱71·142. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\equiv:\exists !\overrightarrow{R}ʻy.\supset_{y}.\overrightarrow{R}ʻy\in 1:\exists !\overleftarrow{R}ʻx.\supset_{x}.\overleftarrow{R}ʻx\in 1 \quad[\text{*70·15}]\) -/
theorem pm71_142 {R : α → β → Prop} :
    R ∈ arrow one one ↔
      (∀ y, (refs R y).Nonempty → refs R y ∈ one) ∧ ∀ x, (rels R x).Nonempty → rels R x ∈ one :=
  pm70_15

/-- ✱71·15. \(\vdash:R\in 1\rightarrow \text{Cls}.\equiv.\text{D}ʻ\overrightarrow{R}\subset 1\cup \iotaʻ\Lambda \quad[\text{*70·48}]\) -/
theorem pm71_15 {R : α → β → Prop} : R ∈ arrow one Cls ↔ dom (Rfwd R) ⊆ one ∪ ι Λ := pm70_48

/-- ✱71·151. \(\vdash:R\in \text{Cls}\rightarrow 1.\equiv.\text{D}ʻ\overleftarrow{R}\subset 1\cup \iotaʻ\Lambda \quad[\text{*70·481}]\) -/
theorem pm71_151 {R : α → β → Prop} : R ∈ arrow Cls one ↔ dom (Rbwd R) ⊆ one ∪ ι Λ := pm70_481

/-- ✱71·152. \(\vdash:R\in 1\rightarrow 1.\equiv.\text{D}ʻ\overrightarrow{R}\subset 1\cup \iotaʻ\Lambda.\text{D}ʻ\overleftarrow{R}\subset 1\cup \iotaʻ\Lambda \quad[\text{*70·16}]\) -/
theorem pm71_152 {R : α → β → Prop} :
    R ∈ arrow one one ↔ dom (Rfwd R) ⊆ one ∪ ι Λ ∧ dom (Rbwd R) ⊆ one ∪ ι Λ := pm70_16

/-- ✱71·16. \(\vdash:R\in 1\rightarrow \text{Cls}.\equiv.\text{E}‼Rʻʻ\text{ᗡ}ʻR\) -/
theorem pm71_16 {R : α → β → Prop} : R ∈ arrow one Cls ↔ EE R (codom R) := oneCls_iff_edesc

/-- ✱71·161. \(\vdash:R\in \text{Cls}\rightarrow 1.\equiv.\text{E}‼\breve{R}ʻʻ\text{D}ʻR\) -/
theorem pm71_161 {R : α → β → Prop} : R ∈ arrow Cls one ↔ EE R˘ (dom R) :=
  Cls_one_iff_cnv.trans oneCls_iff_edesc

/-- ✱71·162. \(\vdash:R\in 1\rightarrow 1.\equiv.\text{E}‼Rʻʻ\text{ᗡ}ʻR.\text{E}‼\breve{R}ʻʻ\text{D}ʻR\) -/
theorem pm71_162 {R : α → β → Prop} :
    R ∈ arrow one one ↔ EE R (codom R) ∧ EE R˘ (dom R) :=
  one_one_iff.trans (and_congr pm71_16 pm71_161)

/-- ✱71·163. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\equiv:y\in \text{ᗡ}ʻR.\equiv_{y}.\text{E}!Rʻy\) -/
theorem pm71_163 {R : α → β → Prop} : R ∈ arrow one Cls ↔ ∀ y, y ∈ codom R ↔ EDesc R y :=
  oneCls_iff_edesc.trans
    ⟨fun h y => ⟨h y, mem_codom_of_edesc⟩, fun h y => (h y).1⟩

/-- ✱71·164. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\equiv:x\in \text{D}ʻR.\equiv_{x}.\text{E}!\breve{R}ʻx\) -/
theorem pm71_164 {R : α → β → Prop} : R ∈ arrow Cls one ↔ ∀ x, x ∈ dom R ↔ EDesc R˘ x :=
  Cls_one_iff_cnv.trans pm71_163

/-- ✱71·165. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\equiv:y\in \text{ᗡ}ʻR.\equiv_{y}.\text{E}!Rʻy:x\in \text{D}ʻR.\equiv_{x}.\text{E}!\breve{R}ʻx\) -/
theorem pm71_165 {R : α → β → Prop} :
    R ∈ arrow one one ↔ (∀ y, y ∈ codom R ↔ EDesc R y) ∧ ∀ x, x ∈ dom R ↔ EDesc R˘ x :=
  one_one_iff.trans (and_congr pm71_163 pm71_164)

/-- ✱71·166. \(\vdash:(y).\text{E}!Rʻy.\supset.R\in 1\rightarrow \text{Cls}\) -/
theorem pm71_166 {R : α → β → Prop} : (∀ y, EDesc R y) → R ∈ arrow one Cls :=
  fun h => oneCls_iff_edesc.2 fun y _ => h y

/-- ✱71·167. \(\vdash:(x).\text{E}!\breve{R}ʻx.\supset.R\in \text{Cls}\rightarrow 1\) -/
theorem pm71_167 {R : α → β → Prop} : (∀ x, EDesc R˘ x) → R ∈ arrow Cls one :=
  fun h => Cls_one_iff_cnv.2 (pm71_166 h)

/-- ✱71·168. \(\vdash \colon\ldotp (y) . \text{E} ! Rʻy : (x) . \text{E} ! \breve{R}ʻx : \supset . R \in 1\rightarrow 1\) -/
theorem pm71_168 {R : α → β → Prop} :
    (∀ y, EDesc R y) ∧ (∀ x, EDesc R˘ x) → R ∈ arrow one one :=
  fun ⟨h1, h2⟩ => one_one_iff.2 ⟨pm71_166 h1, pm71_167 h2⟩

/-- ✱71·17. \(\vdash \colon\ldotp R \in 1\rightarrow \text{Cls} . \equiv : xRz . yRz . \supset_{x, y, z} . x = y\) -/
theorem pm71_17 {R : α → β → Prop} :
    R ∈ arrow one Cls ↔ ∀ x y z, R x z ∧ R y z → x = y := mem_arrow_one_Cls

/-- ✱71·171. \(\vdash \colon\ldotp R \in \text{Cls}\rightarrow 1 . \equiv : xRy . xRz . \supset_{x, y, z} . y = z\) -/
theorem pm71_171 {R : α → β → Prop} :
    R ∈ arrow Cls one ↔ ∀ x y z, R x y ∧ R x z → y = z := mem_arrow_Cls_one

/-- ✱71·172. \(\vdash \colon\ldotp R \in 1\rightarrow 1 . \equiv : xRz . yRz . \supset_{x, y, z} . x = y : xRy . xRz . \supset_{x, y, z} . y = z\) -/
theorem pm71_172 {R : α → β → Prop} :
    R ∈ arrow one one ↔
      (∀ x y z, R x z ∧ R y z → x = y) ∧ ∀ x y z, R x y ∧ R x z → y = z := mem_arrow_one_one

/-- ✱71·18. \(\vdash \colon\ldotp R \in 1\rightarrow \text{Cls} . \equiv : \exists ! \overleftarrow{R}ʻx \cap \overleftarrow{R}ʻy . \supset_{x, y} . x = y\) -/
theorem pm71_18 {R : α → β → Prop} :
    R ∈ arrow one Cls ↔ ∀ x y, (rels R x ∩ rels R y).Nonempty → x = y := by
  rw [mem_arrow_one_Cls]
  constructor
  · rintro h x y ⟨z, hx, hy⟩
    exact h x y z ⟨hx, hy⟩
  · rintro h x y z ⟨hx, hy⟩
    exact h x y ⟨z, hx, hy⟩

/-- ✱71·181. \(\vdash \colon\ldotp R \in \text{Cls}\rightarrow 1 . \equiv : \exists ! \overrightarrow{R}ʻy \cap \overrightarrow{R}ʻz . \supset_{y, z} . y = z\) -/
theorem pm71_181 {R : α → β → Prop} :
    R ∈ arrow Cls one ↔ ∀ y z, (refs R y ∩ refs R z).Nonempty → y = z :=
  Cls_one_iff_cnv.trans pm71_18

/-- ✱71·182. \(\vdash \colon\colon R \in 1\rightarrow 1 . \equiv \colon\ldotp \exists ! \overleftarrow{R}ʻx \cap \overleftarrow{R}ʻy . \lor . \exists ! \overrightarrow{R}ʻx \cap \overrightarrow{R}ʻy : \supset_{x, y} . x = y\)

The same apparent variables `x`, `y` occur as arguments of `R⃖` and of `R⃗`, so `R` is homogeneous. -/
theorem pm71_182 {R : α → α → Prop} :
    R ∈ arrow one one ↔
      ∀ x y, (rels R x ∩ rels R y).Nonempty ∨ (refs R x ∩ refs R y).Nonempty → x = y := by
  rw [one_one_iff, pm71_18, pm71_181]
  constructor
  · rintro ⟨h1, h2⟩ x y (h | h)
    · exact h1 x y h
    · exact h2 x y h
  · intro h
    exact ⟨fun x y hxy => h x y (Or.inl hxy), fun x y hxy => h x y (Or.inr hxy)⟩

/-- ✱71·19. \(\vdash : R \in 1\rightarrow \text{Cls} . \equiv . R\mid \breve{R} = I\upharpoonright \text{D}ʻR\) -/
theorem pm71_19 {R : α → β → Prop} : R ∈ arrow one Cls ↔ R ⨾ R˘ = I ↾ dom R := by
  rw [mem_arrow_one_Cls, rel_eq_iff]
  constructor
  · intro h x y
    constructor
    · rintro ⟨z, hxz, hyz⟩
      exact ⟨h x y z ⟨hxz, hyz⟩, z, hyz⟩
    · rintro ⟨e, z, hz⟩
      have e' : x = y := e
      subst e'
      exact ⟨z, hz, hz⟩
  · intro h x y z ⟨hx, hy⟩
    exact ((h x y).1 ⟨z, hx, hy⟩).1

/-- ✱71·191. \(\vdash : R \in \text{Cls}\rightarrow 1 . \equiv . \breve{R}\mid R = I\upharpoonright \text{ᗡ}ʻR\) -/
theorem pm71_191 {R : α → β → Prop} : R ∈ arrow Cls one ↔ R˘ ⨾ R = I ↾ codom R :=
  Cls_one_iff_cnv.trans pm71_19

/-- ✱71·192. \(\vdash : R \in 1\rightarrow 1 . \equiv . R\mid \breve{R} = I\upharpoonright \text{D}ʻR . \breve{R}\mid R = I\upharpoonright \text{ᗡ}ʻR\) -/
theorem pm71_192 {R : α → β → Prop} :
    R ∈ arrow one one ↔ R ⨾ R˘ = I ↾ dom R ∧ R˘ ⨾ R = I ↾ codom R :=
  one_one_iff.trans (and_congr pm71_19 pm71_191)

/-- ✱71·2. \[\begin{align}\vdash.\text{Cls}\rightarrow &1=\text{Cnv}ʻʻ(1\rightarrow \text{Cls}).\\ &1\rightarrow \text{Cls}=\text{Cnv}ʻʻ(\text{Cls}\rightarrow 1).1\rightarrow 1=\text{Cnv}ʻʻ(1\rightarrow 1) \quad[\text{*70·22}]\end{align}\] -/
theorem pm71_2 :
    (arrow (Cls : Set (Set β)) (one : Set (Set α)) = Cnv ʻʻ arrow one Cls ∧
        arrow (one : Set (Set β)) (Cls : Set (Set α)) = Cnv ʻʻ arrow Cls one) ∧
      arrow (one : Set (Set β)) (one : Set (Set α)) = Cnv ʻʻ arrow one one :=
  ⟨⟨pm70_22, pm70_22⟩, pm70_22⟩

/-- ✱71·21. \(\vdash:R\in 1\rightarrow \text{Cls}.\equiv.\breve{R}\in \text{Cls}\rightarrow 1\) -/
theorem pm71_21 {R : α → β → Prop} : R ∈ arrow one Cls ↔ R˘ ∈ arrow Cls one := arrow_cnv.symm

/-- ✱71·211. \(\vdash:R\in \text{Cls}\rightarrow 1.\equiv.\breve{R}\in 1\rightarrow \text{Cls}\) -/
theorem pm71_211 {R : α → β → Prop} : R ∈ arrow Cls one ↔ R˘ ∈ arrow one Cls := arrow_cnv.symm

/-- ✱71·212. \(\vdash:R\in 1\rightarrow 1.\equiv.\breve{R}\in 1\rightarrow 1\) -/
theorem pm71_212 {R : α → β → Prop} : R ∈ arrow one one ↔ R˘ ∈ arrow one one := arrow_cnv.symm

/-- ✱71·22. \(\vdash:R\in 1\rightarrow \text{Cls}.S\unicode{x2abd}R.\supset.S\in 1\rightarrow \text{Cls}\) -/
theorem pm71_22 {R S : α → β → Prop} : R ∈ arrow one Cls ∧ S ⪽ R → S ∈ arrow one Cls :=
  fun ⟨hR, hS⟩ => oneCls_mono hR hS

/-- ✱71·221. \(\vdash:R\in \text{Cls}\rightarrow 1.S\unicode{x2abd}R.\supset.S\in \text{Cls}\rightarrow 1\) -/
theorem pm71_221 {R S : α → β → Prop} : R ∈ arrow Cls one ∧ S ⪽ R → S ∈ arrow Cls one :=
  fun ⟨hR, hS⟩ => Cls_one_iff_cnv.2 (oneCls_mono (Cls_one_iff_cnv.1 hR) fun x y h => hS y x h)

/-- ✱71·222. \(\vdash:R\in 1\rightarrow 1.S\unicode{x2abd}R.\supset.S\in 1\rightarrow 1\) -/
theorem pm71_222 {R S : α → β → Prop} : R ∈ arrow one one ∧ S ⪽ R → S ∈ arrow one one :=
  fun ⟨hR, hS⟩ => one_one_iff.2
    ⟨pm71_22 ⟨(one_one_iff.1 hR).1, hS⟩, pm71_221 ⟨(one_one_iff.1 hR).2, hS⟩⟩

/-- ✱71·223. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.\text{Rl}ʻR\subset 1\rightarrow \text{Cls} \quad[\text{*71·22.*61·2}]\) -/
theorem pm71_223 {R : α → β → Prop} : R ∈ arrow one Cls → rl R ⊆ arrow one Cls :=
  fun hR _ hS => pm71_22 ⟨hR, hS⟩

/-- ✱71·224. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\text{Rl}ʻR\subset \text{Cls}\rightarrow 1\) -/
theorem pm71_224 {R : α → β → Prop} : R ∈ arrow Cls one → rl R ⊆ arrow Cls one :=
  fun hR _ hS => pm71_221 ⟨hR, hS⟩

/-- ✱71·225. \(\vdash:R\in 1\rightarrow 1.\supset.\text{Rl}ʻR\subset 1\rightarrow 1\) -/
theorem pm71_225 {R : α → β → Prop} : R ∈ arrow one one → rl R ⊆ arrow one one :=
  fun hR _ hS => pm71_222 ⟨hR, hS⟩

/-- ✱71·23. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.R\dot{\cap}S\in 1\rightarrow \text{Cls} \quad[\text{*71·22.*23·43}]\) -/
theorem pm71_23 {R S : α → β → Prop} : R ∈ arrow one Cls → R ⩀ S ∈ arrow one Cls :=
  fun hR => pm71_22 ⟨hR, fun _ _ h => h.1⟩

/-- ✱71·231. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.R\dot{\cap}S\in \text{Cls}\rightarrow 1\) -/
theorem pm71_231 {R S : α → β → Prop} : R ∈ arrow Cls one → R ⩀ S ∈ arrow Cls one :=
  fun hR => pm71_221 ⟨hR, fun _ _ h => h.1⟩

/-- ✱71·232. \(\vdash:R\in 1\rightarrow 1.\supset.R\dot{\cap}S\in 1\rightarrow 1\) -/
theorem pm71_232 {R S : α → β → Prop} : R ∈ arrow one one → R ⩀ S ∈ arrow one one :=
  fun hR => pm71_222 ⟨hR, fun _ _ h => h.1⟩

/-- ✱71·233. \(\vdash:R,\, S\in 1\rightarrow \text{Cls}.\supset.R\dot{\cap}\breve{S}\in 1\rightarrow 1\) -/
theorem pm71_233 {R : α → β → Prop} {S : β → α → Prop} :
    R ∈ arrow one Cls ∧ S ∈ arrow one Cls → R ⩀ S˘ ∈ arrow one one :=
  fun ⟨hR, hS⟩ => one_one_iff.2
    ⟨pm71_23 hR, pm71_221 ⟨pm71_21.1 hS, fun _ _ h => h.2⟩⟩

/-- ✱71·234. \(\vdash:R,\,S\in \text{Cls}\rightarrow 1.\supset.R\dot{\cap}\breve{S}\in 1\rightarrow 1\) -/
theorem pm71_234 {R : α → β → Prop} {S : β → α → Prop} :
    R ∈ arrow Cls one ∧ S ∈ arrow Cls one → R ⩀ S˘ ∈ arrow one one :=
  fun ⟨hR, hS⟩ => one_one_iff.2
    ⟨pm71_22 ⟨pm71_211.1 hS, fun _ _ h => h.2⟩, pm71_231 hR⟩

/-- ✱71·235. \(\vdash:R\in 1\rightarrow \text{Cls}.S\in \text{Cls}\rightarrow 1.\supset.R\dot{\cap}S\in 1\rightarrow 1\) -/
theorem pm71_235 {R S : α → β → Prop} :
    R ∈ arrow one Cls ∧ S ∈ arrow Cls one → R ⩀ S ∈ arrow one one :=
  fun ⟨hR, hS⟩ => one_one_iff.2 ⟨pm71_23 hR, pm71_221 ⟨hS, fun _ _ h => h.2⟩⟩

/-- ✱71·24. \(\vdash:R,\,S\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻR\cap \text{ᗡ}ʻS=\Lambda.\supset.R\unicode{x228d}S\in 1\rightarrow \text{Cls} \quad[\text{*70·54}]\) -/
theorem pm71_24 {R S : α → β → Prop} :
    (R ∈ arrow one Cls ∧ S ∈ arrow one Cls) ∧ codom R ∩ codom S = Λ → R ⊍ S ∈ arrow one Cls :=
  fun ⟨h, hc⟩ => pm70_54 ⟨hc, h⟩

/-- ✱71·241. \(\vdash:R,\,S\in \text{Cls}\rightarrow 1.\text{D}ʻR\cap \text{D}ʻS=\Lambda.\supset.R\unicode{x228d}S\in \text{Cls}\rightarrow 1 \quad[\text{*70·55}]\) -/
theorem pm71_241 {R S : α → β → Prop} :
    (R ∈ arrow Cls one ∧ S ∈ arrow Cls one) ∧ dom R ∩ dom S = Λ → R ⊍ S ∈ arrow Cls one :=
  fun ⟨h, hd⟩ => pm70_55 ⟨hd, h⟩

/-- ✱71·242. \(\vdash:R,\,S\in 1\rightarrow 1.\text{D}ʻR\cap \text{D}ʻS=\Lambda.\text{ᗡ}ʻR\cap \text{ᗡ}ʻS=\Lambda.\supset.R\unicode{x228d}S\in 1\rightarrow 1 \quad[\text{*70·56}]\) -/
theorem pm71_242 {R S : α → β → Prop} :
    ((R ∈ arrow one one ∧ S ∈ arrow one one) ∧ dom R ∩ dom S = Λ) ∧ codom R ∩ codom S = Λ →
      R ⊍ S ∈ arrow one one :=
  fun ⟨⟨h, hd⟩, hc⟩ => pm70_56 ⟨⟨hd, hc⟩, h⟩

/-- ✱71·243. \(\vdash:R,\,S\in 1\rightarrow 1.CʻR\cap CʻS=\Lambda.\supset.R\unicode{x228d}S\in 1\rightarrow 1 \quad[\text{*70·57}]\) -/
theorem pm71_243 {R S : α → α → Prop} :
    (R ∈ arrow one one ∧ S ∈ arrow one one) ∧ fld R ∩ fld S = Λ → R ⊍ S ∈ arrow one one :=
  fun ⟨h, hf⟩ => pm70_57 ⟨hf, h⟩

/-- ✱71·244. \(\vdash:R,\,S\in 1\rightarrow \text{Cls}.R\upharpoonright \text{ᗡ}ʻS\unicode{x2abd}S.\supset.R\unicode{x228d}S\in 1\rightarrow \text{Cls}\) -/
theorem pm71_244 {R S : α → β → Prop} :
    (R ∈ arrow one Cls ∧ S ∈ arrow one Cls) ∧ R ↾ codom S ⪽ S → R ⊍ S ∈ arrow one Cls := by
  rintro ⟨⟨hR, hS⟩, hsub⟩
  rw [mem_arrow_one_Cls] at hR hS ⊢
  rintro x y z ⟨hx | hx, hy | hy⟩
  · exact hR x y z ⟨hx, hy⟩
  · exact hS x y z ⟨hsub x z ⟨hx, y, hy⟩, hy⟩
  · exact hS x y z ⟨hx, hsub y z ⟨hy, x, hx⟩⟩
  · exact hS x y z ⟨hx, hy⟩

/-- ✱71·245. \(\vdash:R,S\in \text{Cls}\rightarrow 1.(\text{D}ʻS)\upharpoonleft R\unicode{x2abd}S.\supset.R\unicode{x228d}S\in \text{Cls}\rightarrow 1\) -/
theorem pm71_245 {R S : α → β → Prop} :
    (R ∈ arrow Cls one ∧ S ∈ arrow Cls one) ∧ dom S ◁ R ⪽ S → R ⊍ S ∈ arrow Cls one := by
  rintro ⟨⟨hR, hS⟩, hsub⟩
  rw [mem_arrow_Cls_one] at hR hS ⊢
  rintro x y z ⟨hy | hy, hz | hz⟩
  · exact hR x y z ⟨hy, hz⟩
  · exact hS x y z ⟨hsub x y ⟨⟨z, hz⟩, hy⟩, hz⟩
  · exact hS x y z ⟨hy, hsub x z ⟨⟨y, hy⟩, hz⟩⟩
  · exact hS x y z ⟨hy, hz⟩

/-- ✱71·25. \(\vdash:R,S\in 1\rightarrow \text{Cls}.\supset.R\mid S\in 1\rightarrow \text{Cls}\) -/
theorem pm71_25 {R : α → β → Prop} {S : β → γ → Prop} :
    R ∈ arrow one Cls ∧ S ∈ arrow one Cls → R ⨾ S ∈ arrow one Cls := by
  rintro ⟨hR, hS⟩
  rw [mem_arrow_one_Cls] at hR hS ⊢
  rintro u v x ⟨⟨y, huy, hyx⟩, ⟨z, hvz, hzx⟩⟩
  have e : y = z := hS y z x ⟨hyx, hzx⟩
  subst e
  exact hR u v y ⟨huy, hvz⟩

/-- ✱71·251. \(\vdash:R,\,S\in \text{Cls}\rightarrow 1.\supset.R\mid S\in \text{Cls}\rightarrow 1\) -/
theorem pm71_251 {R : α → β → Prop} {S : β → γ → Prop} :
    R ∈ arrow Cls one ∧ S ∈ arrow Cls one → R ⨾ S ∈ arrow Cls one := by
  rintro ⟨hR, hS⟩
  rw [mem_arrow_Cls_one] at hR hS ⊢
  rintro x y z ⟨⟨w, hxw, hwy⟩, ⟨w', hxw', hw'z⟩⟩
  have e : w = w' := hR x w w' ⟨hxw, hxw'⟩
  subst e
  exact hS w y z ⟨hwy, hw'z⟩

/-- ✱71·252. \(\vdash:R,\,S\in 1\rightarrow 1.\supset.R\mid S\in 1\rightarrow 1\) -/
theorem pm71_252 {R : α → β → Prop} {S : β → γ → Prop} :
    R ∈ arrow one one ∧ S ∈ arrow one one → R ⨾ S ∈ arrow one one := by
  rintro ⟨hR, hS⟩
  rw [one_one_iff] at hR hS ⊢
  exact ⟨pm71_25 ⟨hR.1, hS.1⟩, pm71_251 ⟨hR.2, hS.2⟩⟩

/-- ✱71·26. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.R\upharpoonright \gamma\in 1\rightarrow \text{Cls} \quad[\text{*70·62}]\)

PM's `γ` is `G`. -/
theorem pm71_26 {R : α → β → Prop} {G : Set β} : R ∈ arrow one Cls → R ↾ G ∈ arrow one Cls :=
  pm70_62

/-- ✱71·261. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\beta\upharpoonleft R\in \text{Cls}\rightarrow 1 \quad[\text{*70·63}]\) -/
theorem pm71_261 {R : α → β → Prop} {B : Set α} : R ∈ arrow Cls one → B ◁ R ∈ arrow Cls one :=
  pm70_63

/-- ✱71·27. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.\beta\upharpoonleft R\in 1\rightarrow \text{Cls} \quad[\text{*35·44.*71·22}]\) -/
theorem pm71_27 {R : α → β → Prop} {B : Set α} : R ∈ arrow one Cls → B ◁ R ∈ arrow one Cls :=
  fun hR => pm71_22 ⟨hR, fun _ _ h => h.2⟩

/-- ✱71·271. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.R\upharpoonright \gamma\in \text{Cls}\rightarrow 1\) -/
theorem pm71_271 {R : α → β → Prop} {G : Set β} : R ∈ arrow Cls one → R ↾ G ∈ arrow Cls one :=
  fun hR => pm71_221 ⟨hR, fun _ _ h => h.1⟩

/-- ✱71·28. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.\beta\upharpoonleft R\upharpoonright \gamma\in 1\rightarrow \text{Cls} \quad[\text{*35·442.*71·22}]\)

The e-text numbers it `*71.28.` (a full stop for the centred dot). -/
theorem pm71_28 {R : α → β → Prop} {B : Set α} {G : Set β} :
    R ∈ arrow one Cls → B ◁ R ↾ G ∈ arrow one Cls :=
  fun hR => pm71_22 ⟨hR, fun _ _ h => h.1.2⟩

/-- ✱71·281. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\beta\upharpoonleft R\upharpoonright \gamma\in \text{Cls}\rightarrow 1\) -/
theorem pm71_281 {R : α → β → Prop} {B : Set α} {G : Set β} :
    R ∈ arrow Cls one → B ◁ R ↾ G ∈ arrow Cls one :=
  fun hR => pm71_221 ⟨hR, fun _ _ h => h.1.2⟩

/-- ✱71·29. \(\vdash:R\in 1\rightarrow 1.\supset.\beta\upharpoonleft R,\,R\upharpoonright \gamma,\beta\upharpoonleft R\upharpoonright \gamma\in 1\rightarrow 1\) -/
theorem pm71_29 {R : α → β → Prop} {B : Set α} {G : Set β} :
    R ∈ arrow one one →
      (B ◁ R ∈ arrow one one ∧ R ↾ G ∈ arrow one one) ∧ B ◁ R ↾ G ∈ arrow one one :=
  fun hR => ⟨⟨pm71_222 ⟨hR, fun _ _ h => h.2⟩, pm71_222 ⟨hR, fun _ _ h => h.1⟩⟩,
    pm71_222 ⟨hR, fun _ _ h => h.1.2⟩⟩

/-- ✱71·31. \(\vdash:R\in 1\rightarrow \text{Cls}.y\in \text{ᗡ}ʻR.\supset.(Rʻy)Ry \quad[\text{*30·32.*71·163}]\) -/
theorem pm71_31 {R : α → β → Prop} {y : β} :
    R ∈ arrow one Cls ∧ y ∈ codom R → Desc R y (fun b => R b y) := by
  rintro ⟨hR, x, hx⟩
  exact (oneCls_desc hR hx).2 hx

/-- ✱71·311. \(\vdash:R\in \text{Cls}\rightarrow 1.x\in \text{D}ʻR.\supset.xR(\breve{R}ʻx)\) -/
theorem pm71_311 {R : α → β → Prop} {x : α} :
    R ∈ arrow Cls one ∧ x ∈ dom R → Desc R˘ x (fun b => R x b) :=
  fun ⟨hR, hx⟩ => pm71_31 ⟨Cls_one_iff_cnv.1 hR, hx⟩

/-- ✱71·312. \(\vdash:R\in 1\rightarrow 1.x\in \text{D}ʻR.y\in \text{ᗡ}ʻR.\supset.xR(\breve{R}ʻx).(Rʻy)Ry\) -/
theorem pm71_312 {R : α → β → Prop} {x : α} {y : β} :
    (R ∈ arrow one one ∧ x ∈ dom R) ∧ y ∈ codom R →
      Desc R˘ x (fun b => R x b) ∧ Desc R y (fun b => R b y) :=
  fun ⟨⟨hR, hx⟩, hy⟩ =>
    ⟨pm71_311 ⟨(one_one_iff.1 hR).2, hx⟩, pm71_31 ⟨(one_one_iff.1 hR).1, hy⟩⟩

/-- ✱71·32. \[\begin{align}&\vdash\colon\colon R\in 1\rightarrow \text{Cls}.y\in \text{ᗡ}ʻR.\supset\colon\ldotp \psi(Rʻy).\equiv:(\exists x).xRy.\psi x:\equiv:xRy.\supset_{x}.\psi x\\ &[\text{*30·33.*71·163}]\end{align}\] -/
theorem pm71_32 {R : α → β → Prop} {y : β} {ψ : α → Prop} :
    R ∈ arrow one Cls ∧ y ∈ codom R →
      (Desc R y ψ ↔ ∃ x, R x y ∧ ψ x) ∧ ((∃ x, R x y ∧ ψ x) ↔ ∀ x, R x y → ψ x) := by
  rintro ⟨hR, x, hx⟩
  have h := oneCls_edesc hR ⟨x, hx⟩
  refine ⟨desc_iff.trans (and_iff_right h), ⟨?_, fun h' => ⟨x, hx, h' x hx⟩⟩⟩
  rintro ⟨x', hx', hψ⟩ z hz
  rw [mem_arrow_one_Cls.1 hR z x' y ⟨hz, hx'⟩]
  exact hψ

/-- ✱71·321. \(\vdash\colon\colon R\in \text{Cls}\rightarrow 1.x\in \text{D}ʻR.\supset\colon\ldotp \psi(\breve{R}ʻx).\equiv:(\exists y).xRy.\psi y:\equiv:xRy.\supset_{y}.\psi y\) -/
theorem pm71_321 {R : α → β → Prop} {x : α} {ψ : β → Prop} :
    R ∈ arrow Cls one ∧ x ∈ dom R →
      (Desc R˘ x ψ ↔ ∃ y, R x y ∧ ψ y) ∧ ((∃ y, R x y ∧ ψ y) ↔ ∀ y, R x y → ψ y) :=
  fun ⟨hR, hx⟩ => pm71_32 ⟨Cls_one_iff_cnv.1 hR, hx⟩

/-- ✱71·33. \(\vdash\colon\colon R\in 1\rightarrow \text{Cls}.\supset\colon\ldotp \psi(Rʻy):\equiv:(\exists x).xRy.\psi x:\equiv:y\in \text{ᗡ}ʻR:xRy.\supset_{x}.\psi x\) -/
theorem pm71_33 {R : α → β → Prop} {y : β} {ψ : α → Prop} :
    R ∈ arrow one Cls →
      (Desc R y ψ ↔ ∃ x, R x y ∧ ψ x) ∧
        ((∃ x, R x y ∧ ψ x) ↔ y ∈ codom R ∧ ∀ x, R x y → ψ x) := by
  intro hR
  by_cases hy : y ∈ codom R
  · have h := pm71_32 (ψ := ψ) ⟨hR, hy⟩
    exact ⟨h.1, h.2.trans (and_iff_right hy).symm⟩
  · refine ⟨⟨fun h => absurd h (not_desc_of_not_codom hy), ?_⟩, ⟨?_, fun h => absurd h.1 hy⟩⟩
    · rintro ⟨x, hx, -⟩
      exact absurd ⟨x, hx⟩ hy
    · rintro ⟨x, hx, -⟩
      exact absurd ⟨x, hx⟩ hy

/-- ✱71·331. \[\begin{align}\vdash\colon\colon R\in \text{Cls}\rightarrow 1.\supset\colon\ldotp \psi(\breve{R}ʻx).\equiv:(\exists y).&xRy.\psi y:\equiv:\\ &x\in \text{D}ʻR:xRy.\supset_{y}.\psi y\end{align}\] -/
theorem pm71_331 {R : α → β → Prop} {x : α} {ψ : β → Prop} :
    R ∈ arrow Cls one →
      (Desc R˘ x ψ ↔ ∃ y, R x y ∧ ψ y) ∧
        ((∃ y, R x y ∧ ψ y) ↔ x ∈ dom R ∧ ∀ y, R x y → ψ y) :=
  fun hR => pm71_33 (Cls_one_iff_cnv.1 hR)

/-- ✱71·332. \[\begin{align}&\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\supset:Rʻy\in \alpha.\equiv.\exists !\overrightarrow{R}ʻy\cap \alpha.\equiv.y\in \text{ᗡ}ʻR.\overrightarrow{R}ʻy\subset \alpha\\ &\left[\text{*71·33}\, \frac{x\in \alpha}{\psi x}\right]\end{align}\] -/
theorem pm71_332 {R : α → β → Prop} {y : β} {A : Set α} :
    R ∈ arrow one Cls →
      (Desc R y (fun b => b ∈ A) ↔ (refs R y ∩ A).Nonempty) ∧
        ((refs R y ∩ A).Nonempty ↔ y ∈ codom R ∧ refs R y ⊆ A) :=
  fun hR => pm71_33 hR

/-- ✱71·333. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:\breve{R}ʻx\in \alpha.\equiv.\exists !\overleftarrow{R}ʻx\cap \alpha.\equiv.x\in \text{D}ʻR.\overleftarrow{R}ʻx\subset \alpha\) -/
theorem pm71_333 {R : α → β → Prop} {x : α} {A : Set β} :
    R ∈ arrow Cls one →
      (Desc R˘ x (fun b => b ∈ A) ↔ (rels R x ∩ A).Nonempty) ∧
        ((rels R x ∩ A).Nonempty ↔ x ∈ dom R ∧ rels R x ⊆ A) :=
  fun hR => pm71_332 (Cls_one_iff_cnv.1 hR)

/-- ✱71·34. \(\vdash:R\in 1\rightarrow \text{Cls}.R=S.y\in \text{ᗡ}ʻR.\supset.Rʻy=Sʻy \quad[\text{*30·36.*71·163}]\) -/
theorem pm71_34 {R S : α → β → Prop} {y : β} :
    (R ∈ arrow one Cls ∧ R = S) ∧ y ∈ codom R → Desc R y (fun b => Desc S y (fun c => b = c)) := by
  rintro ⟨⟨hR, rfl⟩, hy⟩
  obtain ⟨b, hb⟩ := oneCls_edesc hR hy
  exact ⟨b, hb, b, hb, rfl⟩

/-- ✱71·341. \(\vdash:R\in \text{Cls}\rightarrow 1.R=S.x\in \text{D}ʻR.\supset.\breve{R}ʻx=\breve{S}ʻx\)

The e-text prints it as a plain paragraph `*71·341.` (not in bold). -/
theorem pm71_341 {R S : α → β → Prop} {x : α} :
    (R ∈ arrow Cls one ∧ R = S) ∧ x ∈ dom R →
      Desc R˘ x (fun b => Desc S˘ x (fun c => b = c)) := by
  rintro ⟨⟨hR, rfl⟩, hx⟩
  exact pm71_34 ⟨⟨Cls_one_iff_cnv.1 hR, rfl⟩, hx⟩

/-- ✱71·35. \(\vdash\colon\colon R\in 1\rightarrow \text{Cls}.\supset\colon\ldotp y\in \text{ᗡ}ʻR\cup \text{ᗡ}ʻS.\supset_{y}.Rʻy=Sʻy:\equiv.R=S\) -/
theorem pm71_35 {R S : α → β → Prop} :
    R ∈ arrow one Cls →
      ((∀ y, y ∈ codom R ∪ codom S → Desc R y (fun b => Desc S y (fun c => b = c))) ↔ R = S) := by
  intro hR
  constructor
  · intro h
    rw [rel_eq_iff]
    intro x y
    constructor
    · intro hx
      obtain ⟨b, hb, hc⟩ := desc_eq_desc_iff.1 (h y (Or.inl ⟨x, hx⟩))
      exact (hc x).2 ((hb x).1 hx)
    · intro hx
      obtain ⟨b, hb, hc⟩ := desc_eq_desc_iff.1 (h y (Or.inr ⟨x, hx⟩))
      exact (hb x).2 ((hc x).1 hx)
  · rintro rfl y hy
    exact pm71_34 ⟨⟨hR, rfl⟩, hy.elim id id⟩

private theorem cnv_eq_cnv_iff {R S : α → β → Prop} : R˘ = S˘ ↔ R = S :=
  ⟨fun h => congrArg cnv h, fun h => congrArg cnv h⟩

/-- ✱71·351. \(\vdash\colon\colon R\in \text{Cls}\rightarrow 1.\supset\colon\ldotp x\in \text{D}ʻR\cup \text{D}ʻS.\supset_{x}.\breve{R}ʻx=\breve{S}ʻx:\equiv.R=S\) -/
theorem pm71_351 {R S : α → β → Prop} :
    R ∈ arrow Cls one →
      ((∀ x, x ∈ dom R ∪ dom S → Desc R˘ x (fun b => Desc S˘ x (fun c => b = c))) ↔ R = S) :=
  fun hR => (pm71_35 (Cls_one_iff_cnv.1 hR)).trans cnv_eq_cnv_iff

/-- ✱71·352. \[\begin{align}\vdash\colon\colon R\in 1\rightarrow 1.\supset\colon\ldotp y\in \text{ᗡ}ʻR\cup \text{ᗡ}ʻS.&\supset_{y}.Rʻy=Sʻy:\equiv:R=S:\\ &\equiv:x\in \text{D}ʻR\cup \text{D}ʻS.\supset_{x}.\breve{R}ʻx=\breve{S}ʻx\end{align}\] -/
theorem pm71_352 {R S : α → β → Prop} :
    R ∈ arrow one one →
      ((∀ y, y ∈ codom R ∪ codom S → Desc R y (fun b => Desc S y (fun c => b = c))) ↔ R = S) ∧
        (R = S ↔ ∀ x, x ∈ dom R ∪ dom S → Desc R˘ x (fun b => Desc S˘ x (fun c => b = c))) :=
  fun hR => ⟨pm71_35 (one_one_iff.1 hR).1, (pm71_351 (one_one_iff.1 hR).2).symm⟩

/-- ✱71·36. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\supset:x=Rʻy.\equiv.xRy\) -/
theorem pm71_36 {R : α → β → Prop} {x : α} {y : β} :
    R ∈ arrow one Cls → (Desc R y (fun b => x = b) ↔ R x y) := oneCls_desc_eq

/-- ✱71·361. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:y=\breve{R}ʻx.\equiv.xRy\) -/
theorem pm71_361 {R : α → β → Prop} {x : α} {y : β} :
    R ∈ arrow Cls one → (Desc R˘ x (fun b => y = b) ↔ R x y) :=
  fun hR => oneCls_desc_eq (Cls_one_iff_cnv.1 hR)

/-- ✱71·362. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\supset:x=Rʻy.\equiv.xRy.\equiv.y=\breve{R}ʻx\) -/
theorem pm71_362 {R : α → β → Prop} {x : α} {y : β} :
    R ∈ arrow one one →
      (Desc R y (fun b => x = b) ↔ R x y) ∧ (R x y ↔ Desc R˘ x (fun b => y = b)) :=
  fun hR => ⟨pm71_36 (one_one_iff.1 hR).1, (pm71_361 (one_one_iff.1 hR).2).symm⟩

/-- ✱71·37. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\supset:y\in \breve{R}ʻʻ\alpha.\equiv.Rʻy\in \alpha\) -/
theorem pm71_37 {R : α → β → Prop} {y : β} {A : Set α} :
    R ∈ arrow one Cls → (y ∈ R˘ ʻʻ A ↔ Desc R y (fun b => b ∈ A)) := by
  intro hR
  rw [(pm71_33 hR).1]
  exact ⟨fun ⟨x, h1, h2⟩ => ⟨x, h2, h1⟩, fun ⟨x, h1, h2⟩ => ⟨x, h2, h1⟩⟩

/-- ✱71·371. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:x\in Rʻʻ\alpha.\equiv.\breve{R}ʻx\in \alpha\) -/
theorem pm71_371 {R : α → β → Prop} {x : α} {A : Set β} :
    R ∈ arrow Cls one → (x ∈ R ʻʻ A ↔ Desc R˘ x (fun b => b ∈ A)) :=
  fun hR => pm71_37 (Cls_one_iff_cnv.1 hR)

/-- ✱71·38. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.\breve{R}ʻʻ(\alpha-\beta)=\breve{R}ʻʻ\alpha-\breve{R}ʻʻ\beta\) -/
theorem pm71_38 {R : α → β → Prop} {A B : Set α} :
    R ∈ arrow one Cls → R˘ ʻʻ (A \ B) = R˘ ʻʻ A \ R˘ ʻʻ B := by
  intro hR
  ext y
  rw [Set.mem_sdiff, pm71_37 hR, pm71_37 hR, pm71_37 hR]
  by_cases hy : y ∈ codom R
  · obtain ⟨x, hx⟩ := hy
    rw [oneCls_desc hR hx, oneCls_desc hR hx, oneCls_desc hR hx]
    exact Iff.rfl
  · simp only [not_desc_of_not_codom hy, false_and]

/-- ✱71·381. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.Rʻʻ(\alpha-\beta)=Rʻʻ\alpha-Rʻʻ\beta\) -/
theorem pm71_381 {R : α → β → Prop} {A B : Set β} :
    R ∈ arrow Cls one → R ʻʻ (A \ B) = R ʻʻ A \ R ʻʻ B :=
  fun hR => pm71_38 (Cls_one_iff_cnv.1 hR)

/-- ✱71·4. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.Rʻʻ\beta=\hat{x}\{(\exists y).y\in \beta.x=Rʻy\} \quad[\text{*37·1.*71·36}]\) -/
theorem pm71_4 {R : α → β → Prop} {B : Set β} :
    R ∈ arrow one Cls → R ʻʻ B = {x | ∃ y, y ∈ B ∧ Desc R y (fun b => x = b)} := by
  intro hR
  ext x
  exact exists_congr fun y => and_congr_right fun _ => (oneCls_desc_eq hR).symm

/-- ✱71·401. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\breve{R}ʻʻ\beta=\hat{y}\{(\exists x).x\in \beta.y=\breve{R}ʻx\}\) -/
theorem pm71_401 {R : α → β → Prop} {B : Set α} :
    R ∈ arrow Cls one → R˘ ʻʻ B = {y | ∃ x, x ∈ B ∧ Desc R˘ x (fun b => y = b)} :=
  fun hR => pm71_4 (Cls_one_iff_cnv.1 hR)

/-- ✱71·41. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.\text{D}ʻR=\hat{x}{(\exists y).x=Rʻy} \quad[\text{*33·11.*71·36}]\) -/
theorem pm71_41 {R : α → β → Prop} :
    R ∈ arrow one Cls → dom R = {x | ∃ y, Desc R y (fun b => x = b)} := by
  intro hR
  ext x
  exact exists_congr fun y => (oneCls_desc_eq hR).symm

/-- ✱71·411. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\text{ᗡ}ʻR=\hat{y}\{(\exists x).y=\breve{R}ʻx\}\) -/
theorem pm71_411 {R : α → β → Prop} :
    R ∈ arrow Cls one → codom R = {y | ∃ x, Desc R˘ x (fun b => y = b)} :=
  fun hR => pm71_41 (Cls_one_iff_cnv.1 hR)

/-- ✱71·42. \[\begin{align}&\vdash\colon\colon R\in 1\rightarrow \text{Cls}.\beta\subset \text{ᗡ}ʻR.\supset\colon\ldotp Rʻʻ\beta\subset \alpha.\equiv:y\in \beta.\supset_{y}.Rʻy\in \alpha\\ &[\text{*37·61.*71·16}]\end{align}\] -/
theorem pm71_42 {R : α → β → Prop} {A : Set α} {B : Set β} :
    R ∈ arrow one Cls ∧ B ⊆ codom R →
      (R ʻʻ B ⊆ A ↔ ∀ y, y ∈ B → Desc R y (fun b => b ∈ A)) := by
  rintro ⟨hR, hB⟩
  constructor
  · intro h y hy
    obtain ⟨x, hx⟩ := hB hy
    exact (oneCls_desc hR hx).2 (h ⟨y, hy, hx⟩)
  · rintro h x ⟨y, hy, hx⟩
    exact (oneCls_desc hR hx).1 (h y hy)

/-- ✱71·421. \(\vdash\colon\colon R\in \text{Cls}\rightarrow 1.\alpha\subset \text{D}ʻR.\supset\colon\ldotp \breve{R}ʻʻ\alpha\subset \beta.\equiv:x\in \alpha.\supset_{x}.\breve{R}ʻx\in \beta\) -/
theorem pm71_421 {R : α → β → Prop} {A : Set α} {B : Set β} :
    R ∈ arrow Cls one ∧ A ⊆ dom R →
      (R˘ ʻʻ A ⊆ B ↔ ∀ x, x ∈ A → Desc R˘ x (fun b => b ∈ B)) :=
  fun ⟨hR, hA⟩ => pm71_42 ⟨Cls_one_iff_cnv.1 hR, hA⟩

/-- ✱71·43. \(\vdash:R\in 1\rightarrow \text{Cls}.y\in \alpha\cap \text{ᗡ}ʻR.\supset.Rʻy\in Rʻʻ\alpha \quad[\text{*37·62.*71·16}]\) -/
theorem pm71_43 {R : α → β → Prop} {y : β} {A : Set β} :
    R ∈ arrow one Cls ∧ y ∈ A ∩ codom R → Desc R y (fun b => b ∈ R ʻʻ A) := by
  rintro ⟨hR, hyA, x, hx⟩
  exact (oneCls_desc hR hx).2 ⟨y, hyA, hx⟩

/-- ✱71·431. \(\vdash:R\in \text{Cls}\rightarrow 1.x\in \alpha\cap \text{D}ʻR.\supset.\breve{R}ʻx\in \breve{R}ʻʻ\alpha\) -/
theorem pm71_431 {R : α → β → Prop} {x : α} {A : Set α} :
    R ∈ arrow Cls one ∧ x ∈ A ∩ dom R → Desc R˘ x (fun b => b ∈ R˘ ʻʻ A) :=
  fun ⟨hR, hx⟩ => pm71_43 ⟨Cls_one_iff_cnv.1 hR, hx⟩

/-- ✱71·44. \[\begin{align}&\vdash\colon\colon R\in 1\rightarrow \text{Cls}.\alpha\subset \text{ᗡ}ʻR.\supset\colon\ldotp x\in Rʻʻ\alpha.\supset_{x}.\psi x:\equiv:y\in \alpha.\supset_{y}.\psi(Rʻy)\\ &[\text{*37·63.*71·16}]\end{align}\] -/
theorem pm71_44 {R : α → β → Prop} {A : Set β} {ψ : α → Prop} :
    R ∈ arrow one Cls ∧ A ⊆ codom R →
      ((∀ x, x ∈ R ʻʻ A → ψ x) ↔ ∀ y, y ∈ A → Desc R y ψ) := by
  rintro ⟨hR, hA⟩
  constructor
  · intro h y hy
    obtain ⟨x, hx⟩ := hA hy
    exact (oneCls_desc hR hx).2 (h x ⟨y, hy, hx⟩)
  · rintro h x ⟨y, hy, hx⟩
    exact (oneCls_desc hR hx).1 (h y hy)

/-- ✱71·441. \(\vdash\colon\colon R\in \text{Cls}\rightarrow 1.\alpha\subset \text{D}ʻR.\supset\colon\ldotp y\in \breve{R}ʻʻ\alpha.\supset_{y}.\psi y:\equiv:x\in \alpha.\supset_{x}.\psi(\breve{R}ʻx)\) -/
theorem pm71_441 {R : α → β → Prop} {A : Set α} {ψ : β → Prop} :
    R ∈ arrow Cls one ∧ A ⊆ dom R →
      ((∀ y, y ∈ R˘ ʻʻ A → ψ y) ↔ ∀ x, x ∈ A → Desc R˘ x ψ) :=
  fun ⟨hR, hA⟩ => pm71_44 ⟨Cls_one_iff_cnv.1 hR, hA⟩

/-- ✱71·45. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\supset:(\exists x).x\in Rʻʻ\alpha.\psi x.\equiv.(\exists y).y\in \alpha.\psi(Rʻy)\) -/
theorem pm71_45 {R : α → β → Prop} {A : Set β} {ψ : α → Prop} :
    R ∈ arrow one Cls → ((∃ x, x ∈ R ʻʻ A ∧ ψ x) ↔ ∃ y, y ∈ A ∧ Desc R y ψ) := by
  intro hR
  constructor
  · rintro ⟨x, ⟨y, hy, hx⟩, hψ⟩
    exact ⟨y, hy, (oneCls_desc hR hx).2 hψ⟩
  · rintro ⟨y, hy, b, hb, hψ⟩
    exact ⟨b, ⟨y, hy, (hb b).2 rfl⟩, hψ⟩

/-- ✱71·451. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:(\exists y).y\in \breve{R}ʻʻ\alpha.\psi y.\equiv.(\exists x).x\in \alpha.\psi(\breve{R}ʻx)\) -/
theorem pm71_451 {R : α → β → Prop} {A : Set α} {ψ : β → Prop} :
    R ∈ arrow Cls one → ((∃ y, y ∈ R˘ ʻʻ A ∧ ψ y) ↔ ∃ x, x ∈ A ∧ Desc R˘ x ψ) :=
  fun hR => pm71_45 (Cls_one_iff_cnv.1 hR)

/-- ✱71·46. \(\vdash:R\in 1\rightarrow \text{Cls}.\alpha\subset Rʻʻ\beta.\supset.\alpha=Rʻʻ(\breve{R}ʻʻ\alpha\cap \beta)\) -/
theorem pm71_46 {R : α → β → Prop} {A : Set α} {B : Set β} :
    R ∈ arrow one Cls ∧ A ⊆ R ʻʻ B → A = R ʻʻ (R˘ ʻʻ A ∩ B) := by
  rintro ⟨hR, hA⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, hyB, hxy⟩ := hA hx
    exact ⟨y, ⟨⟨x, hx, hxy⟩, hyB⟩, hxy⟩
  · rintro ⟨y, ⟨⟨x', hx'A, hx'y⟩, -⟩, hxy⟩
    rw [mem_arrow_one_Cls.1 hR x x' y ⟨hxy, hx'y⟩]
    exact hx'A

/-- ✱71·461. \(\vdash:R\in \text{Cls}\rightarrow 1.\beta\subset \breve{R}ʻʻ\alpha.\supset.\beta=\breve{R}ʻʻ(Rʻʻ\beta\cap \alpha)\) -/
theorem pm71_461 {R : α → β → Prop} {A : Set α} {B : Set β} :
    R ∈ arrow Cls one ∧ B ⊆ R˘ ʻʻ A → B = R˘ ʻʻ (R ʻʻ B ∩ A) :=
  fun ⟨hR, hB⟩ => pm71_46 ⟨Cls_one_iff_cnv.1 hR, hB⟩

/-- ✱71·47. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\supset:\alpha\subset Rʻʻ\beta.\equiv.(\exists \gamma).\gamma\subset \beta.\alpha=Rʻʻ\gamma\)

PM's `γ` is `G`. -/
theorem pm71_47 {R : α → β → Prop} {A : Set α} {B : Set β} :
    R ∈ arrow one Cls → (A ⊆ R ʻʻ B ↔ ∃ G, G ⊆ B ∧ A = R ʻʻ G) := by
  intro hR
  constructor
  · intro h
    exact ⟨R˘ ʻʻ A ∩ B, Set.inter_subset_right, pm71_46 ⟨hR, h⟩⟩
  · rintro ⟨G, hG, rfl⟩ x ⟨y, hy, hxy⟩
    exact ⟨y, hG hy, hxy⟩

/-- ✱71·471. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:\beta\subset \breve{R}ʻʻ\alpha.\equiv.(\exists \gamma).\gamma\subset \alpha.\beta=\breve{R}ʻʻ\gamma\) -/
theorem pm71_471 {R : α → β → Prop} {A : Set α} {B : Set β} :
    R ∈ arrow Cls one → (B ⊆ R˘ ʻʻ A ↔ ∃ G, G ⊆ A ∧ B = R˘ ʻʻ G) :=
  fun hR => pm71_47 (Cls_one_iff_cnv.1 hR)

/-- ✱71·48. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.\text{D}ʻR_{\in}=\text{Cl}ʻ\text{D}ʻR\) -/
theorem pm71_48 {R : α → β → Prop} : R ∈ arrow one Cls → dom (imgRel R) = cl (dom R) := by
  intro hR
  ext X
  constructor
  · rintro ⟨B, hB⟩
    show X ⊆ dom R
    rw [show X = R ʻʻ B from hB]
    rintro x ⟨y, -, hxy⟩
    exact ⟨y, hxy⟩
  · intro hX
    have hX' : X ⊆ R ʻʻ codom R := fun x hx => by
      obtain ⟨y, hy⟩ := (show X ⊆ dom R from hX) hx
      exact ⟨y, ⟨x, hy⟩, hy⟩
    obtain ⟨G, -, hG⟩ := (pm71_47 hR).1 hX'
    exact ⟨G, hG⟩

/-- ✱71·481. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\text{D}ʻ(\breve{R})_{\in}=\text{Cl}ʻ\text{ᗡ}ʻR\) -/
theorem pm71_481 {R : α → β → Prop} : R ∈ arrow Cls one → dom (imgRel R˘) = cl (codom R) :=
  fun hR => pm71_48 (Cls_one_iff_cnv.1 hR)

/-- ✱71·49. \(\vdash:R\in 1\rightarrow \text{Cls}.\alpha\subset \text{ᗡ}ʻR.\supset.Rʻʻʻ\text{Cl}ʻ\alpha=\text{Cl}ʻRʻʻ\alpha.Rʻʻʻ\text{Cl ex}ʻ\alpha=\text{Cl ex}ʻRʻʻ\alpha\) -/
theorem pm71_49 {R : α → β → Prop} {A : Set β} :
    R ∈ arrow one Cls ∧ A ⊆ codom R →
      R ʻʻʻ cl A = cl (R ʻʻ A) ∧ R ʻʻʻ clEx A = clEx (R ʻʻ A) := by
  rintro ⟨hR, hA⟩
  constructor
  · ext X
    constructor
    · rintro ⟨B, hB, hX⟩
      show X ⊆ R ʻʻ A
      rw [show X = R ʻʻ B from hX]
      rintro x ⟨y, hy, hxy⟩
      exact ⟨y, (show B ⊆ A from hB) hy, hxy⟩
    · intro hX
      obtain ⟨G, hG, e⟩ := (pm71_47 hR).1 (show X ⊆ R ʻʻ A from hX)
      exact ⟨G, hG, e⟩
  · ext X
    constructor
    · rintro ⟨B, ⟨hBA, y, hy⟩, hX⟩
      rw [show X = R ʻʻ B from hX]
      refine ⟨?_, ?_⟩
      · rintro x ⟨y', hy', hxy⟩
        exact ⟨y', hBA hy', hxy⟩
      · obtain ⟨x, hx⟩ := hA (hBA hy)
        exact ⟨x, y, hy, hx⟩
    · rintro ⟨hX, x, hx⟩
      obtain ⟨G, hG, e⟩ := (pm71_47 hR).1 hX
      have hne : G.Nonempty := by
        rw [e] at hx
        obtain ⟨y, hy, -⟩ := hx
        exact ⟨y, hy⟩
      exact ⟨G, ⟨hG, hne⟩, e⟩

/-- ✱71·491. \(\vdash:R\in \text{Cls}\rightarrow 1.\alpha\subset \text{D}ʻR.\supset.\breve{R}ʻʻʻ\text{Cl}ʻ\alpha=\text{Cl}ʻ\breve{R}ʻʻ\alpha.\breve{R}ʻʻʻ\text{Cl ex}ʻ\alpha=\text{Cl ex}ʻ\breve{R}ʻʻ\alpha\) -/
theorem pm71_491 {R : α → β → Prop} {A : Set α} :
    R ∈ arrow Cls one ∧ A ⊆ dom R →
      R˘ ʻʻʻ cl A = cl (R˘ ʻʻ A) ∧ R˘ ʻʻʻ clEx A = clEx (R˘ ʻʻ A) :=
  fun ⟨hR, hA⟩ => pm71_49 ⟨Cls_one_iff_cnv.1 hR, hA⟩

/-- ✱71·5. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\supset:xRy.\equiv.x=\breve{\iota}ʻ\overrightarrow{R}ʻy\) -/
theorem pm71_5 {R : α → β → Prop} {x : α} {y : β} :
    R ∈ arrow one Cls → (R x y ↔ Desc iota˘ (refs R y) (fun b => x = b)) := by
  intro hR
  rw [desc_iota_cnv]
  constructor
  · intro hx
    exact ⟨x, fun z => ⟨fun hz => mem_arrow_one_Cls.1 hR z x y ⟨hz, hx⟩, fun e => e ▸ hx⟩, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact (hb x).2 rfl

/-- ✱71·501. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:xRy.\equiv.y=\breve{\iota}ʻ\overleftarrow{R}ʻx\) -/
theorem pm71_501 {R : α → β → Prop} {x : α} {y : β} :
    R ∈ arrow Cls one → (R x y ↔ Desc iota˘ (rels R x) (fun b => y = b)) :=
  fun hR => pm71_5 (Cls_one_iff_cnv.1 hR)

/-- ✱71·51. \(\vdash:R\in 1\rightarrow \text{Cls}.y\in \text{ᗡ}ʻR.\supset.Rʻy=\breve{\iota}ʻ\overrightarrow{R}ʻy\) -/
theorem pm71_51 {R : α → β → Prop} {y : β} :
    R ∈ arrow one Cls ∧ y ∈ codom R →
      Desc R y (fun b => Desc iota˘ (refs R y) (fun c => b = c)) := by
  rintro ⟨hR, x, hx⟩
  rw [oneCls_desc hR hx]
  exact (pm71_5 hR).1 hx

/-- ✱71·511. \(\vdash:R\in \text{Cls}\rightarrow 1.x\in \text{D}ʻR.\supset.\breve{R}ʻx=\breve{\iota}ʻ\overleftarrow{R}ʻx\) -/
theorem pm71_511 {R : α → β → Prop} {x : α} :
    R ∈ arrow Cls one ∧ x ∈ dom R →
      Desc R˘ x (fun b => Desc iota˘ (rels R x) (fun c => b = c)) :=
  fun ⟨hR, hx⟩ => pm71_51 ⟨Cls_one_iff_cnv.1 hR, hx⟩

/-- ✱71·52. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.Rʻʻ\alpha=\breve{\iota}ʻʻ\overrightarrow{R}ʻʻ\alpha\) -/
theorem pm71_52 {R : α → β → Prop} {A : Set β} :
    R ∈ arrow one Cls → R ʻʻ A = iota˘ ʻʻ Rfwd R ʻʻ A := by
  intro hR
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨refs R y, ⟨y, hy, rfl⟩, ?_⟩
    show refs R y = refs I x
    ext z
    exact ⟨fun hz => mem_arrow_one_Cls.1 hR z x y ⟨hz, hxy⟩, fun e => (show z = x from e) ▸ hxy⟩
  · rintro ⟨X, ⟨y, hy, hX⟩, hι⟩
    have hx : x ∈ X := by
      rw [show X = refs I x from hι]
      exact rfl
    rw [show X = refs R y from hX] at hx
    exact ⟨y, hy, hx⟩

/-- ✱71·521. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\breve{R}ʻʻ\alpha=\breve{\iota}ʻʻ\overleftarrow{R}ʻʻ\alpha\) -/
theorem pm71_521 {R : α → β → Prop} {A : Set α} :
    R ∈ arrow Cls one → R˘ ʻʻ A = iota˘ ʻʻ Rbwd R ʻʻ A :=
  fun hR => pm71_52 (Cls_one_iff_cnv.1 hR)

/-- ✱71·53. \(\vdash:R\in 1\rightarrow \text{Cls}.\breve{R}ʻx=\breve{R}ʻy.\supset.x=y\) -/
theorem pm71_53 {R : α → β → Prop} {x y : α} :
    R ∈ arrow one Cls ∧ Desc R˘ x (fun b => Desc R˘ y (fun c => b = c)) → x = y := by
  rintro ⟨hR, h⟩
  obtain ⟨b, hb, hc⟩ := desc_eq_desc_iff.1 h
  exact mem_arrow_one_Cls.1 hR x y b ⟨(hb b).2 rfl, (hc b).2 rfl⟩

/-- ✱71·531. \(\vdash:R\in \text{Cls}\rightarrow 1.Rʻy=Rʻz.\supset.y=z\) -/
theorem pm71_531 {R : α → β → Prop} {y z : β} :
    R ∈ arrow Cls one ∧ Desc R y (fun b => Desc R z (fun c => b = c)) → y = z :=
  fun ⟨hR, h⟩ => pm71_53 (R := R˘) ⟨Cls_one_iff_cnv.1 hR, h⟩

/-- ✱71·532. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\supset:Rʻy=Rʻz.\supset.y=z:\breve{R}ʻx=\breve{R}ʻy.\supset.x=y\)

The real variable `y` occurs both as an argument of `R'` and as an argument of `R̆'`, so `R` is
homogeneous. -/
theorem pm71_532 {R : α → α → Prop} {x y z : α} :
    R ∈ arrow one one →
      (Desc R y (fun b => Desc R z (fun c => b = c)) → y = z) ∧
        (Desc R˘ x (fun b => Desc R˘ y (fun c => b = c)) → x = y) :=
  fun hR => ⟨fun h => pm71_531 ⟨(one_one_iff.1 hR).2, h⟩,
    fun h => pm71_53 ⟨(one_one_iff.1 hR).1, h⟩⟩

/-- ✱71·54. \(\vdash\colon\colon R\in 1\rightarrow \text{Cls}.\supset\colon\ldotp R\in 1\rightarrow 1.\equiv:Rʻy=Rʻz.\supset_{y,z}.y=z\) -/
theorem pm71_54 {R : α → β → Prop} :
    R ∈ arrow one Cls →
      (R ∈ arrow one one ↔ ∀ y z, Desc R y (fun b => Desc R z (fun c => b = c)) → y = z) := by
  intro hR
  rw [one_one_iff, and_iff_right hR]
  constructor
  · intro h y z hd
    exact pm71_531 ⟨h, hd⟩
  · intro h
    rw [mem_arrow_Cls_one]
    rintro x y z ⟨hy, hz⟩
    apply h
    exact desc_eq_desc_iff.2
      ⟨x, fun w => ⟨fun hw => mem_arrow_one_Cls.1 hR w x y ⟨hw, hy⟩, fun e => e ▸ hy⟩,
        fun w => ⟨fun hw => mem_arrow_one_Cls.1 hR w x z ⟨hw, hz⟩, fun e => e ▸ hz⟩⟩

/-- ✱71·55. \(\vdash\colon\colon R\in 1\rightarrow \text{Cls}.\supset\colon\ldotp R\upharpoonright \beta\in 1\rightarrow 1.\equiv:y,z\in \beta.Rʻy=Rʻz.\supset_{y,z}.y=z\) -/
theorem pm71_55 {R : α → β → Prop} {B : Set β} :
    R ∈ arrow one Cls →
      (R ↾ B ∈ arrow one one ↔
        ∀ y z, (y ∈ B ∧ z ∈ B) ∧ Desc R y (fun b => Desc R z (fun c => b = c)) → y = z) := by
  intro hR
  rw [pm71_54 (pm70_62 hR)]
  exact forall_congr' fun y => forall_congr' fun z => imp_congr_left desc_cres_eq

/-- ✱71·56. \(\vdash\colon\ldotp R\in 1\rightarrow 1.y\in \text{ᗡ}ʻR.\supset:Rʻy=Rʻz.\equiv.y=z\) -/
theorem pm71_56 {R : α → β → Prop} {y z : β} :
    R ∈ arrow one one ∧ y ∈ codom R →
      (Desc R y (fun b => Desc R z (fun c => b = c)) ↔ y = z) := by
  rintro ⟨hR, hy⟩
  constructor
  · exact fun h => pm71_531 ⟨(one_one_iff.1 hR).2, h⟩
  · rintro rfl
    exact pm71_34 ⟨⟨(one_one_iff.1 hR).1, rfl⟩, hy⟩

/-- ✱71·561. \(\vdash\colon\ldotp R\in 1\rightarrow 1.x\in \text{D}ʻR.\supset:\breve{R}ʻx=\breve{R}ʻy.\equiv.x=y\) -/
theorem pm71_561 {R : α → β → Prop} {x y : α} :
    R ∈ arrow one one ∧ x ∈ dom R →
      (Desc R˘ x (fun b => Desc R˘ y (fun c => b = c)) ↔ x = y) :=
  fun ⟨hR, hx⟩ => pm71_56 ⟨arrow_cnv.2 hR, hx⟩

/-- ✱71·57. \(\vdash\colon\ldotp Rʻy=Rʻz.\equiv_{y,z}.y=z:\equiv:R\in 1\rightarrow 1:(y).\text{E}!Rʻy\) -/
theorem pm71_57 {R : α → β → Prop} :
    (∀ y z, Desc R y (fun b => Desc R z (fun c => b = c)) ↔ y = z) ↔
      R ∈ arrow one one ∧ ∀ y, EDesc R y := by
  constructor
  · intro h
    have hE : ∀ y, EDesc R y := fun y => edesc_of_desc ((h y y).2 rfl)
    exact ⟨(pm71_54 (pm71_166 hE)).2 fun y z hd => (h y z).1 hd, hE⟩
  · rintro ⟨hR, hE⟩ y z
    exact pm71_56 ⟨hR, mem_codom_of_edesc (hE y)⟩

/-- ✱71·571. \(\vdash\colon\ldotp y\in \beta.\supset_{y}.\text{E}!Rʻy:\equiv.R\upharpoonright \beta\in 1\rightarrow \text{Cls}.\beta\subset \text{ᗡ}ʻR\) -/
theorem pm71_571 {R : α → β → Prop} {B : Set β} :
    (∀ y, y ∈ B → EDesc R y) ↔ R ↾ B ∈ arrow one Cls ∧ B ⊆ codom R := by
  constructor
  · intro h
    refine ⟨?_, fun y hy => mem_codom_of_edesc (h y hy)⟩
    rw [mem_arrow_one_Cls]
    rintro x x' y ⟨⟨hx, hyB⟩, hx', -⟩
    obtain ⟨b, hb⟩ := h y hyB
    exact ((hb x).1 hx).trans ((hb x').1 hx').symm
  · rintro ⟨h1, h2⟩ y hy
    obtain ⟨x, hx⟩ := h2 hy
    exact ⟨x, fun z => ⟨fun hz => mem_arrow_one_Cls.1 h1 z x y ⟨⟨hz, hy⟩, hx, hy⟩,
      fun e => e ▸ hx⟩⟩

/-- ✱71·572. \[\begin{align}&\vdash\colon\ldotp y\in \beta\cap \text{ᗡ}ʻR.\supset_{y}.\text{E}!Rʻy:\equiv.R\upharpoonright \beta\in 1\rightarrow \text{Cls}\\ &[\text{*71·571.*35·351.*22·43}]\end{align}\] -/
theorem pm71_572 {R : α → β → Prop} {B : Set β} :
    (∀ y, y ∈ B ∩ codom R → EDesc R y) ↔ R ↾ B ∈ arrow one Cls := by
  rw [pm71_571 (B := B ∩ codom R)]
  have e : R ↾ (B ∩ codom R) = R ↾ B := by
    funext x y
    exact propext ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, x, h.1⟩⟩
  rw [e]
  exact and_iff_left Set.inter_subset_right

/-- ✱71·58. \(\vdash\colon\colon y,\,z\in \beta.\supset_{y,z}:Rʻy=Rʻz.\equiv.y=z\colon\ldotp \supset.R\upharpoonright \beta\in 1\rightarrow 1.\beta\subset \text{ᗡ}ʻR\) -/
theorem pm71_58 {R : α → β → Prop} {B : Set β} :
    (∀ y z, y ∈ B ∧ z ∈ B → (Desc R y (fun b => Desc R z (fun c => b = c)) ↔ y = z)) →
      R ↾ B ∈ arrow one one ∧ B ⊆ codom R := by
  intro h
  have hE : ∀ y, y ∈ B → EDesc R y := fun y hy => edesc_of_desc ((h y y ⟨hy, hy⟩).2 rfl)
  obtain ⟨h1, h2⟩ := pm71_571.1 hE
  refine ⟨(pm71_54 h1).2 fun y z hd => ?_, h2⟩
  obtain ⟨⟨hy, hz⟩, hd'⟩ := desc_cres_eq.1 hd
  exact (h y z ⟨hy, hz⟩).1 hd'

/-- ✱71·59. \(\vdash\colon\colon y,z\in \beta.\supset_{y,z}:Rʻy=Rʻz.\equiv.y=z\colon\ldotp \equiv.R\upharpoonright \beta\in 1\rightarrow 1.\beta\subset \text{ᗡ}ʻR\) -/
theorem pm71_59 {R : α → β → Prop} {B : Set β} :
    (∀ y z, y ∈ B ∧ z ∈ B → (Desc R y (fun b => Desc R z (fun c => b = c)) ↔ y = z)) ↔
      R ↾ B ∈ arrow one one ∧ B ⊆ codom R := by
  refine ⟨pm71_58, ?_⟩
  rintro ⟨h1, h2⟩ y z ⟨hy, hz⟩
  constructor
  · intro hd
    exact pm71_531 ⟨(one_one_iff.1 h1).2, desc_cres_eq.2 ⟨⟨hy, hz⟩, hd⟩⟩
  · rintro rfl
    obtain ⟨b, hb⟩ := pm71_571.2 ⟨(one_one_iff.1 h1).1, h2⟩ y hy
    exact ⟨b, hb, b, hb, rfl⟩

/-- ✱71·6. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.R=\dot{s}ʻ\hat{P}\{(\exists y).y\in \text{ᗡ}ʻR.P=(Rʻy)\downarrow y\}\) -/
theorem pm71_6 {R : α → β → Prop} :
    R ∈ arrow one Cls → R = sumRel {P | ∃ y, y ∈ codom R ∧ Desc R y (fun b => P = b ↓ y)} := by
  intro hR
  rw [rel_eq_iff]
  intro x z
  constructor
  · intro hxz
    exact ⟨x ↓ z, ⟨z, ⟨x, hxz⟩, (oneCls_desc hR hxz).2 rfl⟩, rfl, rfl⟩
  · rintro ⟨P, ⟨y, ⟨w, hw⟩, hd⟩, hP⟩
    rw [oneCls_desc hR hw] at hd
    subst hd
    obtain ⟨rfl, rfl⟩ := hP
    exact hw

private theorem img_refs_of_oneCls {T : α → β → Prop} {Q : γ → α → Prop} {w : α} {y : β}
    (hT : T ∈ arrow one Cls) (hw : T w y) : Q ʻʻ refs T y = refs Q w := by
  ext v
  constructor
  · rintro ⟨u, hu, hvu⟩
    rw [mem_arrow_one_Cls.1 hT u w y ⟨hu, hw⟩] at hvu
    exact hvu
  · intro hv
    exact ⟨w, hw, hv⟩

/-- ✱71·61. \(\vdash:T\in 1\rightarrow \text{Cls}.\supset.Qʻʻʻ\overrightarrow{T}ʻʻ(\text{ᗡ}ʻT\cap \alpha)=\overrightarrow{Q}ʻʻTʻʻ\alpha\) -/
theorem pm71_61 {T : α → β → Prop} {Q : γ → α → Prop} {A : Set β} :
    T ∈ arrow one Cls → Q ʻʻʻ Rfwd T ʻʻ (codom T ∩ A) = Rfwd Q ʻʻ T ʻʻ A := by
  intro hT
  ext X
  constructor
  · rintro ⟨Y, ⟨y, ⟨⟨w, hw⟩, hyA⟩, hY⟩, hX⟩
    refine ⟨w, ⟨y, hyA, hw⟩, ?_⟩
    show X = refs Q w
    rw [show X = Q ʻʻ Y from hX, show Y = refs T y from hY, img_refs_of_oneCls hT hw]
  · rintro ⟨w, ⟨y, hyA, hw⟩, hX⟩
    refine ⟨refs T y, ⟨y, ⟨⟨w, hw⟩, hyA⟩, rfl⟩, ?_⟩
    show X = Q ʻʻ refs T y
    rw [show X = refs Q w from hX, img_refs_of_oneCls hT hw]

/-- ✱71·611. \(\vdash:T\in \text{Cls}\rightarrow 1.\supset.Qʻʻʻ\overleftarrow{T}ʻʻ(\text{D}ʻT\cap \alpha)=\overrightarrow{Q}ʻʻ\breve{T}ʻʻ\alpha\) -/
theorem pm71_611 {T : β → α → Prop} {Q : γ → α → Prop} {A : Set β} :
    T ∈ arrow Cls one → Q ʻʻʻ Rbwd T ʻʻ (dom T ∩ A) = Rfwd Q ʻʻ T˘ ʻʻ A :=
  fun hT => pm71_61 (Cls_one_iff_cnv.1 hT)

/-- ✱71·612. \(\vdash:T\in 1\rightarrow \text{Cls}.\supset.\breve{Q}ʻʻʻ\overrightarrow{T}ʻʻ(\text{ᗡ}ʻT\cap \alpha)=\overleftarrow{Q}ʻʻTʻʻ\alpha\) -/
theorem pm71_612 {T : α → β → Prop} {Q : α → γ → Prop} {A : Set β} :
    T ∈ arrow one Cls → Q˘ ʻʻʻ Rfwd T ʻʻ (codom T ∩ A) = Rbwd Q ʻʻ T ʻʻ A :=
  fun hT => pm71_61 hT

/-- ✱71·613. \(\vdash:T\in \text{Cls}\rightarrow 1.\supset.\breve{Q}ʻʻʻ\overleftarrow{T}ʻʻ(\text{D}ʻT\cap \alpha)=\overleftarrow{Q}ʻʻ\breve{T}ʻʻ\alpha\) -/
theorem pm71_613 {T : β → α → Prop} {Q : α → γ → Prop} {A : Set β} :
    T ∈ arrow Cls one → Q˘ ʻʻʻ Rbwd T ʻʻ (dom T ∩ A) = Rbwd Q ʻʻ T˘ ʻʻ A :=
  fun hT => pm71_61 (Cls_one_iff_cnv.1 hT)

/-- ✱71·7. \(\vdash\colon\ldotp Q\in 1\rightarrow \text{Cls}.\supset:xP\mid Qz.\equiv.xP(Qʻz)\) -/
theorem pm71_7 {P : α → β → Prop} {Q : β → γ → Prop} {x : α} {z : γ} :
    Q ∈ arrow one Cls → ((P ⨾ Q) x z ↔ Desc Q z (fun b => P x b)) := by
  intro hQ
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact (oneCls_desc hQ hyz).2 hxy
  · rintro ⟨b, hb, hP⟩
    exact ⟨b, hP, (hb b).2 rfl⟩

/-- ✱71·701. \(\vdash\colon\ldotp Q\in \text{Cls}\rightarrow 1.\supset:xQ\mid Pz.\equiv.(\breve{Q}ʻx)Pz\) -/
theorem pm71_701 {Q : α → β → Prop} {P : β → γ → Prop} {x : α} {z : γ} :
    Q ∈ arrow Cls one → ((Q ⨾ P) x z ↔ Desc Q˘ x (fun b => P b z)) := by
  intro hQ
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact (oneCls_desc (Cls_one_iff_cnv.1 hQ) hxy).2 hyz
  · rintro ⟨b, hb, hP⟩
    exact ⟨b, (hb b).2 rfl, hP⟩


private theorem oneCls_uniq {R : α → β → Prop} {x : α} {y : β} (hR : R ∈ arrow one Cls)
    (hx : R x y) : ∀ w, R w y ↔ w = x :=
  fun w => ⟨fun hw => mem_arrow_one_Cls.1 hR w x y ⟨hw, hx⟩, fun e => e ▸ hx⟩

private theorem graph_oneCls (f : β → α) : graph f ∈ arrow one Cls :=
  pm71_166 fun y => EDesc_graph f y

private theorem graph_inj {f g : β → α} (h : graph f = graph g) : f = g := by
  funext y
  have h' : graph g (f y) y := h ▸ (rfl : f y = f y)
  exact h'

private theorem refs_inj {R S : α → β → Prop} (h : refs R = refs S) : R = S := by
  funext x y
  exact propext (Set.ext_iff.1 (congrFun h y) x)

private theorem couple_inj_right {x : α} {y y' : β} (h : x ↓ y = x ↓ y') : y = y' := by
  have h' : (x ↓ y') x y := h ▸ (couple_apply x y x y).2 ⟨rfl, rfl⟩
  exact ((couple_apply _ _ _ _).1 h').2

private theorem couple_inj_left {x x' : α} {y : β} (h : x ↓ y = x' ↓ y) : x = x' := by
  have h' : (x' ↓ y) x y := h ▸ (couple_apply x y x y).2 ⟨rfl, rfl⟩
  exact ((couple_apply _ _ _ _).1 h').1

private theorem ebang_congr {φ ψ : α → Prop} (h : ∀ x, φ x ↔ ψ x) : EBang φ ↔ EBang ψ := by
  simp only [EBang, h]

private theorem relProd_cnv_iff {R : α → β → Prop} {S : β → γ → Prop} {x : α} {z : γ} :
    (S˘ ⨾ R˘) z x ↔ (R ⨾ S) x z :=
  ⟨fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩, fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩⟩

/-!
## [✱72] Miscellaneous propositions concerning one-many, many-one, and one-one relations

*(Vol. 1, p. 462)*

> *Summary of* *72.
>
> In this number we shall prove various propositions involving \(1 \rightarrow \text{Cls}\), \(\text{Cls} \rightarrow 1\), or \(1 \rightarrow 1\), but not embodying fundamental properties of these classes of relations.
>
> The present number begins with various propositions (*72·1-·191) showing that various special relations are one-many or one-one. The most useful of these are
>
> *72·182. \(\vdash. x \downarrow y \in 1 \rightarrow 1\)
>
> *72·184. \(\vdash .x\downarrow, \downarrow x \in 1 \rightarrow 1\)
>
> We have next a set of propositions concerning \(RʻSʻz\) when \(R\) and \(S\) are one-many, or \(Rʻ\breve{R}ʻz\) when \(R\) is one-one, and kindred matters. The most useful of these is
>
> *72·241. \(\vdash \colon\ldotp R \in 1 \rightarrow 1 .\supset: y \in \text{ᗡ}ʻR .\equiv. y = \breve{R}ʻRʻy\)
>
> We have next a set of propositions (*72·3-·341) concerning products and sums of classes of relations; of these the one most used is

**Lean reading.** The constant relations are taken at explicit types: `Λ̇` is `rNull`, `ι` is
`iota`, `ῐ` is `iota˘`, `x↓`, `↓x` are `coupleL x`, `coupleR x`, `(↓x)_∈` is
`imgRel (coupleR x)`, and `Cnv`, `sg`, `gs`, `D`, `ᗡ`, `C`, `I`, `Cl`, `Rl`, `Cl ex`, `Rl ex` are
the Defs constants. The relations `p`, `s`, `ṗ`, `ṡ` of ✱72·16–·163 are `graph prodCls`, … (PM
defines only their descriptive functions). `R'S'z` is `Desc2 R S z ψ` (✱30·02) and `E!R'S'z` is
`EBang (fun x => Desc S z (fun w => R x w))`; `Cnv'(…)` is written `(…)˘`; PM's relation `∈`
(✱72·26·27) is `memRel`; `S²` is `rsq S`; `R̆_∈` is `imgRelCnv R`. PM's `λ`, `μ`, `γ` are `L`, `M`,
`G`. A single variable used in two positions forces homogeneity (✱72·242; `C'P` in ✱72·323);
in ✱72·14 PM's comment applies the proposition to heterogeneous `♀` (`P↾`, `↿P`), so its real
variable `x` is taken in each conjunct at the type its position determines. In ✱72·65·66 the apparent variable `R` is taken at the type of the `R` constructed in
✱72·64. The e-text garbles ✱72·23, ✱72·25, ✱72·27 and ✱72·61; PM's statements are formalized.

**Status.** proved (all propositions; ✱72·14, ✱72·16, ✱72·161, ✱72·162, ✱72·163, ✱72·23,
✱72·25, ✱72·27, ✱72·61, ✱72·65, ✱72·66 proved (reading), see their docstrings)
-/

/-- ✱72·32. \(\vdash \colon\ldotp \lambda \subset 1 \rightarrow \text{Cls}: P,Q \in \lambda. \exists! \text{ᗡ}ʻP \cap \text{ᗡ}ʻQ .\supset_{P,Q}. P = Q :\supset.\dot{s}ʻ\lambda \in 1 \rightarrow \text{Cls}\)

(The e-text places this proposition in the Summary of ✱72; its demonstration follows ✱72·312.) -/
theorem pm72_32 {L : Set (α → β → Prop)} :
    (L ⊆ arrow one Cls ∧ ∀ P Q, (P ∈ L ∧ Q ∈ L) ∧ (codom P ∩ codom Q).Nonempty → P = Q) →
      sumRel L ∈ arrow one Cls := by
  rintro ⟨hL, hPQ⟩
  rw [mem_arrow_one_Cls]
  rintro x y z ⟨⟨P, hP, hx⟩, ⟨Q, hQ, hy⟩⟩
  have e : P = Q := hPQ P Q ⟨⟨hP, hQ⟩, z, ⟨x, hx⟩, ⟨y, hy⟩⟩
  subst e
  exact mem_arrow_one_Cls.1 (hL hP) x y z ⟨hx, hy⟩

/-- ✱72·1. \(\vdash.\dot{\Lambda} \in 1\rightarrow 1\) -/
theorem pm72_1 : (rNull : α → β → Prop) ∈ arrow one one :=
  mem_arrow_one_one.2
    ⟨fun x _ z h => absurd h.1 (rNull_apply x z), fun x y _ h => absurd h.1 (rNull_apply x y)⟩

/-- ✱72·11. \(\vdash.\text{Cnv} \in 1\rightarrow 1\) -/
theorem pm72_11 : (Cnv : (β → α → Prop) → (α → β → Prop) → Prop) ∈ arrow one one :=
  mem_arrow_one_one.2
    ⟨fun _ _ _ ⟨h1, h2⟩ => (Cnv_iff.1 h1).trans (Cnv_iff.1 h2).symm,
      fun _ _ _ ⟨h1, h2⟩ => cnv_eq_cnv_iff.1 ((Cnv_iff.1 h1).symm.trans (Cnv_iff.1 h2))⟩

/-- ✱72·12. \(\vdash.\overrightarrow{R},\overleftarrow{R} \in 1\rightarrow \text{Cls} \quad[\text{*32·12·121.*71·166}]\) -/
theorem pm72_12 {R : α → β → Prop} : Rfwd R ∈ arrow one Cls ∧ Rbwd R ∈ arrow one Cls :=
  ⟨graph_oneCls _, graph_oneCls _⟩

/-- ✱72·121. \(\vdash.\text{sg},\,\text{gs} \in 1\rightarrow 1\) -/
theorem pm72_121 :
    (sg : (Set α → β → Prop) → (α → β → Prop) → Prop) ∈ arrow one one ∧
      (gs : (Set β → α → Prop) → (α → β → Prop) → Prop) ∈ arrow one one := by
  refine ⟨one_one_iff.2 ⟨graph_oneCls _, ?_⟩, one_one_iff.2 ⟨graph_oneCls _, ?_⟩⟩
  · rw [mem_arrow_Cls_one]
    rintro A R S ⟨h1, h2⟩
    have e : Rfwd R = Rfwd S := (show A = Rfwd R from h1).symm.trans h2
    exact refs_inj (graph_inj e)
  · rw [mem_arrow_Cls_one]
    rintro A R S ⟨h1, h2⟩
    have e : Rbwd R = Rbwd S := (show A = Rbwd R from h1).symm.trans h2
    exact cnv_eq_cnv_iff.1 (refs_inj (R := R˘) (S := S˘) (graph_inj e))

/-- ✱72·13. \(\vdash.\text{D} \in 1\rightarrow \text{Cls} \quad[\text{*33·12.*71·166}]\) -/
theorem pm72_13 : (D : Set α → (α → β → Prop) → Prop) ∈ arrow one Cls := graph_oneCls _

/-- ✱72·131. \(\vdash.\text{ᗡ} \in 1\rightarrow \text{Cls} \quad[\text{*33·121.*71·166}]\) -/
theorem pm72_131 : (Dcnv : Set β → (α → β → Prop) → Prop) ∈ arrow one Cls := graph_oneCls _

/-- ✱72·132. \(\vdash:C \in 1\rightarrow \text{Cls} \quad[\text{*33·122.*71·166}]\) -/
theorem pm72_132 : (C : Set α → (α → α → Prop) → Prop) ∈ arrow one Cls := graph_oneCls _

/-- ✱72·14. \(\vdash.x\unicode{x2640},\unicode{x2640}x \in 1\rightarrow \text{Cls} \quad[\text{*38·12.*71·166}]\)

`♀` is any double descriptive function `f : α → β → γ` (Defs ✱38).

**Status.** proved (reading): the real variable `x` is the left argument of `♀` in `x♀` and its
right argument in `♀x`; PM's comment applies the proposition to `↿P`, `P↾`, `P⥏`, `P|`, `|P`,
`x↓`, `↓x`, where the two arguments of `♀` are of different types (a class and a relation in
`P↾`, `↿P`). So `x` is typically ambiguous and takes in each conjunct the type its position
determines: each conjunct is asserted for all `x` of that type (for a homogeneous `f` this is
the literal formula). -/
theorem pm72_14 {f : α → β → γ} :
    (∀ x : α, opL f x ∈ arrow one Cls) ∧ ∀ x : β, opR f x ∈ arrow one Cls :=
  ⟨fun _ => graph_oneCls _, fun _ => graph_oneCls _⟩

/-- ✱72·15. \(\vdash.P_{{\in}}\in 1\rightarrow \text{Cls} \quad[\text{*37·111.*71·166}]\) -/
theorem pm72_15 {P : α → β → Prop} : imgRel P ∈ arrow one Cls := graph_oneCls _

/-- ✱72·16. \(\vdash.p\in 1\rightarrow \text{Cls}\)

**Status.** proved (reading): `p` is the relation of `p'κ` to `κ`; PM defines only the
descriptive function `p'κ` (✱40·01), which by the convention of the Summary of Section E
defines the relation `p = α̂κ̂(α = p'κ)`, i.e. `graph prodCls`. -/
theorem pm72_16 : graph (prodCls : Set (Set α) → Set α) ∈ arrow one Cls := graph_oneCls _

/-- ✱72·161. \(\vdash.s\in 1\rightarrow \text{Cls} \quad[\text{Proof as in *72·16}]\)

**Status.** proved (reading): `s` is the relation `graph sumCls` of `s'κ` to `κ` (✱40·02), as in
✱72·16. -/
theorem pm72_161 : graph (sumCls : Set (Set α) → Set α) ∈ arrow one Cls := graph_oneCls _

/-- ✱72·162. \(\vdash.\dot{p}\in 1\rightarrow \text{Cls} \quad[\text{Proof as in *72·16}]\)

**Status.** proved (reading): `ṗ` is the relation `graph prodRel` of `ṗ'λ` to `λ` (✱41·01), as
in ✱72·16. -/
theorem pm72_162 : graph (prodRel : Set (α → β → Prop) → α → β → Prop) ∈ arrow one Cls :=
  graph_oneCls _

/-- ✱72·163. \(\vdash.\dot{s}\in 1\rightarrow \text{Cls} \quad[\text{Proof as in *72·16}]\)

**Status.** proved (reading): `ṡ` is the relation `graph sumRel` of `ṡ'λ` to `λ` (✱41·02), as
in ✱72·16. -/
theorem pm72_163 : graph (sumRel : Set (α → β → Prop) → α → β → Prop) ∈ arrow one Cls :=
  graph_oneCls _

/-- ✱72·17. \(\vdash.I\in 1\rightarrow 1\) -/
theorem pm72_17 : (I : α → α → Prop) ∈ arrow one one :=
  mem_arrow_one_one.2
    ⟨fun _ _ _ ⟨h1, h2⟩ => (show _ = _ from h1).trans (show _ = _ from h2).symm,
      fun _ _ _ ⟨h1, h2⟩ => (show _ = _ from h1).symm.trans (show _ = _ from h2)⟩

/-- ✱72·18. \(\vdash.\iota\in 1\rightarrow 1 \quad[\text{*51·23.*71·57}]\) -/
theorem pm72_18 : (iota : Set α → α → Prop) ∈ arrow one one := by
  refine one_one_iff.2 ⟨graph_oneCls _, ?_⟩
  rw [mem_arrow_Cls_one]
  rintro X x y ⟨h1, h2⟩
  exact unitCls_injective ((show X = ι x from h1).symm.trans (show X = ι y from h2))

/-- ✱72·181. \(\vdash.\breve{\iota}\in 1\rightarrow 1 \quad[\text{*72·18.*71·212}]\) -/
theorem pm72_181 : ((iota : Set α → α → Prop)˘) ∈ arrow one one := arrow_cnv.2 pm72_18

/-- ✱72·182. \(\vdash.x\downarrow y\in 1\rightarrow 1\) -/
theorem pm72_182 {x : α} {y : β} : x ↓ y ∈ arrow one one := by
  rw [mem_arrow_one_one]
  refine ⟨fun z z' w h => ?_, fun z w w' h => ?_⟩
  · rw [couple_apply, couple_apply] at h
    exact h.1.1.trans h.2.1.symm
  · rw [couple_apply, couple_apply] at h
    exact h.1.2.trans h.2.2.symm

/-- ✱72·184. \(\vdash.x\downarrow ,\downarrow x\in 1\rightarrow 1 \quad[\text{*55·2.*71·57}]\) -/
theorem pm72_184 {x : α} :
    (coupleL x : (α → β → Prop) → β → Prop) ∈ arrow one one ∧
      (coupleR x : (γ → α → Prop) → γ → Prop) ∈ arrow one one := by
  refine ⟨one_one_iff.2 ⟨graph_oneCls _, ?_⟩, one_one_iff.2 ⟨graph_oneCls _, ?_⟩⟩
  · rw [mem_arrow_Cls_one]
    rintro P y y' ⟨h1, h2⟩
    exact couple_inj_right ((show P = x ↓ y from h1).symm.trans (show P = x ↓ y' from h2))
  · rw [mem_arrow_Cls_one]
    rintro P z z' ⟨h1, h2⟩
    exact couple_inj_left ((show P = z ↓ x from h1).symm.trans (show P = z' ↓ x from h2))

/-- ✱72·185. \(\vdash.(\downarrow x)_{\in}\in 1\rightarrow 1 \quad[\text{*55·262.*37·11.*72·15.*71·54}]\) -/
theorem pm72_185 {x : α} : imgRel (coupleR x : (γ → α → Prop) → γ → Prop) ∈ arrow one one := by
  refine one_one_iff.2 ⟨graph_oneCls _, ?_⟩
  rw [mem_arrow_Cls_one]
  rintro X A B ⟨h1, h2⟩
  have key : ∀ (A B : Set γ), coupleR x ʻʻ A = coupleR x ʻʻ B → A ⊆ B := by
    intro A B e z hz
    have hm : z ↓ x ∈ coupleR x ʻʻ A := ⟨z, hz, rfl⟩
    rw [e] at hm
    obtain ⟨w, hw, hzw⟩ := hm
    rw [couple_inj_left (show z ↓ x = w ↓ x from hzw)]
    exact hw
  have e : coupleR x ʻʻ A = coupleR x ʻʻ B :=
    (show X = coupleR x ʻʻ A from h1).symm.trans (show X = coupleR x ʻʻ B from h2)
  exact Set.Subset.antisymm (key A B e) (key B A e.symm)

/-- ✱72·19. \(\vdash.\text{Cl}\in 1\rightarrow 1 \quad[\text{*60·55.*71·57}]\) -/
theorem pm72_19 : (Cl : Set (Set α) → Set α → Prop) ∈ arrow one one := by
  refine one_one_iff.2 ⟨graph_oneCls _, ?_⟩
  rw [mem_arrow_Cls_one]
  rintro K A B ⟨h1, h2⟩
  have e : cl A = cl B := (show K = cl A from h1).symm.trans (show K = cl B from h2)
  have hA : A ∈ cl B := e ▸ (le_refl A : A ⊆ A)
  have hB : B ∈ cl A := e ▸ (le_refl B : B ⊆ B)
  exact Set.Subset.antisymm hA hB

/-- ✱72·191. \(\vdash.\text{Rl}\in 1\rightarrow 1 \quad[\text{*61·55.*71·57}]\) -/
theorem pm72_191 : (Rl : Set (α → β → Prop) → (α → β → Prop) → Prop) ∈ arrow one one := by
  refine one_one_iff.2 ⟨graph_oneCls _, ?_⟩
  rw [mem_arrow_Cls_one]
  rintro L P Q ⟨h1, h2⟩
  have e : rl P = rl Q := (show L = rl P from h1).symm.trans (show L = rl Q from h2)
  have hP : P ∈ rl Q := e ▸ (fun _ _ h => h : P ⪽ P)
  have hQ : Q ∈ rl P := e ▸ (fun _ _ h => h : Q ⪽ Q)
  exact rel_eq_iff.2 fun x y => ⟨hP x y, hQ x y⟩

/-- ✱72·192. \(\vdash.\text{Cl ex}\in 1\rightarrow 1 \quad[\text{*60·56.*71·57}]\) -/
theorem pm72_192 : (ClEx : Set (Set α) → Set α → Prop) ∈ arrow one one := by
  refine one_one_iff.2 ⟨graph_oneCls _, ?_⟩
  rw [mem_arrow_Cls_one]
  rintro K A B ⟨h1, h2⟩
  have e : clEx A = clEx B := (show K = clEx A from h1).symm.trans (show K = clEx B from h2)
  have key : ∀ (A B : Set α), clEx A = clEx B → A ⊆ B := by
    intro A B e x hx
    have hm : ({x} : Set α) ∈ clEx A := ⟨Set.singleton_subset_iff.2 hx, x, rfl⟩
    rw [e] at hm
    exact Set.singleton_subset_iff.1 hm.1
  exact Set.Subset.antisymm (key A B e) (key B A e.symm)

/-- ✱72·193. \(\vdash.\text{Rl ex}\in 1\rightarrow 1 \quad[\text{*61·56.*71·57}]\) -/
theorem pm72_193 : (RlEx : Set (α → β → Prop) → (α → β → Prop) → Prop) ∈ arrow one one := by
  refine one_one_iff.2 ⟨graph_oneCls _, ?_⟩
  rw [mem_arrow_Cls_one]
  rintro L P Q ⟨h1, h2⟩
  have e : rlEx P = rlEx Q := (show L = rlEx P from h1).symm.trans (show L = rlEx Q from h2)
  have key : ∀ (P Q : α → β → Prop), rlEx P = rlEx Q → P ⪽ Q := by
    intro P Q e x y hxy
    have hm : x ↓ y ∈ rlEx P :=
      ⟨fun u v h => by
        obtain ⟨rfl, rfl⟩ := (couple_apply _ _ _ _).1 h
        exact hxy, x, y, (couple_apply _ _ _ _).2 ⟨rfl, rfl⟩⟩
    rw [e] at hm
    exact hm.1 x y ((couple_apply _ _ _ _).2 ⟨rfl, rfl⟩)
  exact rel_eq_iff.2 fun x y => ⟨key P Q e x y, key Q P e.symm x y⟩

/-- ✱72·2. \(\vdash\colon\ldotp R,\,S\in 1\rightarrow \text{Cls}.\supset:x=RʻSʻz.\equiv.x(R\mid S)z.\equiv.x=(R\mid S)ʻz\) -/
theorem pm72_2 {R : α → β → Prop} {S : β → γ → Prop} {x : α} {z : γ} :
    R ∈ arrow one Cls ∧ S ∈ arrow one Cls →
      (Desc2 R S z (fun b => x = b) ↔ (R ⨾ S) x z) ∧
        ((R ⨾ S) x z ↔ Desc (R ⨾ S) z (fun b => x = b)) := by
  rintro ⟨hR, hS⟩
  refine ⟨?_, (oneCls_desc_eq (pm71_25 ⟨hR, hS⟩)).symm⟩
  rw [desc2_iff]
  constructor
  · rintro ⟨w, hw, hd⟩
    exact ⟨w, (oneCls_desc_eq hR).1 hd, (hw w).2 rfl⟩
  · rintro ⟨w, hxw, hwz⟩
    exact (oneCls_desc hS hwz).2 ((oneCls_desc_eq hR).2 hxw)

/-- ✱72·201. \(\vdash\colon\ldotp R,\,S\in \text{Cls}\rightarrow 1.\supset:z=\breve{S}ʻ\breve{R}ʻx.\equiv.x(R\mid S)z.\equiv.z=(\breve{S}\mid \breve{R})ʻx\) -/
theorem pm72_201 {R : α → β → Prop} {S : β → γ → Prop} {x : α} {z : γ} :
    R ∈ arrow Cls one ∧ S ∈ arrow Cls one →
      (Desc2 S˘ R˘ x (fun b => z = b) ↔ (R ⨾ S) x z) ∧
        ((R ⨾ S) x z ↔ Desc (S˘ ⨾ R˘) x (fun b => z = b)) := by
  rintro ⟨hR, hS⟩
  obtain ⟨h1, h2⟩ := pm72_2 (x := z) (z := x) ⟨Cls_one_iff_cnv.1 hS, Cls_one_iff_cnv.1 hR⟩
  exact ⟨h1.trans relProd_cnv_iff, relProd_cnv_iff.symm.trans h2⟩

/-- ✱72·202. \(\vdash\colon\ldotp R,\,S\in 1\rightarrow 1.\supset:x=RʻSʻz.\equiv.x(R\mid S)z.\equiv.z=\breve{S}ʻ\breve{R}ʻx \quad[\text{*72·2·201}]\) -/
theorem pm72_202 {R : α → β → Prop} {S : β → γ → Prop} {x : α} {z : γ} :
    R ∈ arrow one one ∧ S ∈ arrow one one →
      (Desc2 R S z (fun b => x = b) ↔ (R ⨾ S) x z) ∧
        ((R ⨾ S) x z ↔ Desc2 S˘ R˘ x (fun b => z = b)) := by
  rintro ⟨hR, hS⟩
  rw [one_one_iff] at hR hS
  exact ⟨(pm72_2 ⟨hR.1, hS.1⟩).1, (pm72_201 ⟨hR.2, hS.2⟩).1.symm⟩

/-- ✱72·21. \(\vdash\colon\ldotp R,\,S\in 1\rightarrow \text{Cls}.\supset:z\in \breve{S}ʻʻ\text{ᗡ}ʻR.\equiv.\text{E}!RʻSʻz.\equiv.\text{E}!(R\mid S)ʻz\)

`E!R'S'z` is `E!(℩x)(x R (S'z))`, the inner description having the smaller scope (✱30·02). -/
theorem pm72_21 {R : α → β → Prop} {S : β → γ → Prop} {z : γ} :
    R ∈ arrow one Cls ∧ S ∈ arrow one Cls →
      (z ∈ S˘ ʻʻ codom R ↔ EBang (fun x => Desc S z (fun w => R x w))) ∧
        (EBang (fun x => Desc S z (fun w => R x w)) ↔ EDesc (R ⨾ S) z) := by
  rintro ⟨hR, hS⟩
  have h2 : EBang (fun x => Desc S z (fun w => R x w)) ↔ EDesc (R ⨾ S) z :=
    ebang_congr fun x => (pm71_7 hS).symm
  refine ⟨?_, h2⟩
  rw [h2, ← pm71_163.1 (pm71_25 ⟨hR, hS⟩) z]
  exact ⟨fun ⟨w, ⟨x, hx⟩, hw⟩ => ⟨x, w, hx, hw⟩, fun ⟨x, w, hx, hw⟩ => ⟨w, ⟨x, hx⟩, hw⟩⟩

/-- ✱72·211. \(\vdash\colon\ldotp R,\,S\in \text{Cls}\rightarrow 1.\supset:x\in Rʻʻ\text{D}ʻS.\equiv.\text{E}!\breve{S}ʻ\breve{R}ʻx.\equiv.\text{E}!(\breve{S}\mid \breve{R})ʻx\) -/
theorem pm72_211 {R : α → β → Prop} {S : β → γ → Prop} {x : α} :
    R ∈ arrow Cls one ∧ S ∈ arrow Cls one →
      (x ∈ R ʻʻ dom S ↔ EBang (fun z => Desc R˘ x (fun w => S˘ z w))) ∧
        (EBang (fun z => Desc R˘ x (fun w => S˘ z w)) ↔ EDesc (S˘ ⨾ R˘) x) :=
  fun ⟨hR, hS⟩ => pm72_21 ⟨Cls_one_iff_cnv.1 hS, Cls_one_iff_cnv.1 hR⟩

/-- ✱72·22. \(\vdash:R,\,S\in 1\rightarrow \text{Cls}.z\in \breve{S}ʻʻ\text{ᗡ}ʻR.\supset.RʻSʻz=(R\mid S)ʻz\) -/
theorem pm72_22 {R : α → β → Prop} {S : β → γ → Prop} {z : γ} :
    (R ∈ arrow one Cls ∧ S ∈ arrow one Cls) ∧ z ∈ S˘ ʻʻ codom R →
      Desc2 R S z (fun b => Desc (R ⨾ S) z (fun c => b = c)) := by
  rintro ⟨⟨hR, hS⟩, w, ⟨x, hxw⟩, hwz⟩
  exact (desc2_iff _ _ _ _).2 ((oneCls_desc hS hwz).2 ((oneCls_desc hR hxw).2
    ((oneCls_desc (pm71_25 ⟨hR, hS⟩) ⟨w, hxw, hwz⟩).2 rfl)))

/-- ✱72·221. \(\vdash:R,\,S\in \text{Cls}\rightarrow 1.x\in Rʻʻ\text{D}ʻS.\supset.\breve{S}ʻ\breve{R}ʻx=(\breve{S}\mid \breve{R})ʻx\) -/
theorem pm72_221 {R : α → β → Prop} {S : β → γ → Prop} {x : α} :
    (R ∈ arrow Cls one ∧ S ∈ arrow Cls one) ∧ x ∈ R ʻʻ dom S →
      Desc2 S˘ R˘ x (fun b => Desc (S˘ ⨾ R˘) x (fun c => b = c)) :=
  fun ⟨⟨hR, hS⟩, hx⟩ => pm72_22 ⟨⟨Cls_one_iff_cnv.1 hS, Cls_one_iff_cnv.1 hR⟩, hx⟩

/-- ✱72·23. \(\vdash:R,\,S\in 1\rightarrow \text{Cls}.\supset.RʻʻSʻʻ\gamma=\hat{x}\{(\exists z).z\in \gamma.x=RʻSʻ\gamma\}\)

**Status.** proved (reading): `R'S'γ` is printed (also in the demonstration) where `R'S'z` is
meant: `γ` is a class, and the apparent variable `z` would otherwise not occur in its scope. -/
theorem pm72_23 {R : α → β → Prop} {S : β → γ → Prop} {G : Set γ} :
    R ∈ arrow one Cls ∧ S ∈ arrow one Cls →
      R ʻʻ S ʻʻ G = {x | ∃ z, z ∈ G ∧ Desc2 R S z (fun b => x = b)} := by
  intro h
  ext x
  constructor
  · rintro ⟨w, ⟨z, hz, hwz⟩, hxw⟩
    exact ⟨z, hz, (pm72_2 h).1.2 ⟨w, hxw, hwz⟩⟩
  · rintro ⟨z, hz, hd⟩
    obtain ⟨w, hxw, hwz⟩ := (pm72_2 h).1.1 hd
    exact ⟨w, ⟨z, hz, hwz⟩, hxw⟩

/-- ✱72·24. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\supset:x\in \text{D}ʻR.\equiv.x=Rʻ\breve{R}ʻx\) -/
theorem pm72_24 {R : α → β → Prop} {x : α} :
    R ∈ arrow one one → (x ∈ dom R ↔ Desc2 R R˘ x (fun b => x = b)) := by
  intro hR
  rw [one_one_iff] at hR
  rw [(pm72_2 ⟨hR.1, Cls_one_iff_cnv.1 hR.2⟩).1]
  exact ⟨fun ⟨y, h⟩ => ⟨y, h, h⟩, fun ⟨y, h, _⟩ => ⟨y, h⟩⟩

/-- ✱72·241. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\supset:y\in \text{ᗡ}ʻR.\equiv.y=\breve{R}ʻRʻy\) -/
theorem pm72_241 {R : α → β → Prop} {y : β} :
    R ∈ arrow one one → (y ∈ codom R ↔ Desc2 R˘ R y (fun b => y = b)) :=
  fun hR => pm72_24 (arrow_cnv.2 hR)

private theorem desc2_cnv_iff {R : α → β → Prop} {z : α} {φ : α → Prop}
    (hR : R ∈ arrow one one) : Desc2 R R˘ z φ ↔ z ∈ dom R ∧ φ z := by
  rw [one_one_iff] at hR
  rw [desc2_iff]
  constructor
  · rintro ⟨w, hw, hd⟩
    have hzw : R z w := (hw w).2 rfl
    exact ⟨⟨w, hzw⟩, (oneCls_desc hR.1 hzw).1 hd⟩
  · rintro ⟨⟨w, hzw⟩, hφ⟩
    exact (oneCls_desc (Cls_one_iff_cnv.1 hR.2) hzw).2 ((oneCls_desc hR.1 hzw).2 hφ)

/-- ✱72·242. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\supset:\phi(Rʻ\breve{R}ʻz).\equiv.z\in \text{D}ʻR.\phi z:\phi(\breve{R}ʻRʻz).\equiv.z\in \text{ᗡ}ʻR.\phi z\)

The same `φ` takes `R'R̆'z` and `R̆'R'z` as arguments, so `R` is homogeneous. -/
theorem pm72_242 {R : α → α → Prop} {z : α} {φ : α → Prop} :
    R ∈ arrow one one →
      (Desc2 R R˘ z φ ↔ z ∈ dom R ∧ φ z) ∧ (Desc2 R˘ R z φ ↔ z ∈ codom R ∧ φ z) :=
  fun hR => ⟨desc2_cnv_iff hR, desc2_cnv_iff (arrow_cnv.2 hR)⟩

/-- ✱72·243. \(\vdash\colon\colon R\in 1\rightarrow 1.\supset\colon\ldotp z\in \text{D}ʻR.\phi z.\equiv_{z}.\psi(\breve{R}ʻz):\equiv:\phi(Rʻw).\equiv_{w}.w\in \text{ᗡ}ʻR.\psi w\) -/
theorem pm72_243 {R : α → β → Prop} {φ : α → Prop} {ψ : β → Prop} :
    R ∈ arrow one one →
      ((∀ z, z ∈ dom R ∧ φ z ↔ Desc R˘ z ψ) ↔ ∀ w, Desc R w φ ↔ w ∈ codom R ∧ ψ w) := by
  intro hR
  rw [one_one_iff] at hR
  have h1 := hR.1
  have h2 := Cls_one_iff_cnv.1 hR.2
  constructor
  · intro H w
    by_cases hw : w ∈ codom R
    · obtain ⟨z, hzw⟩ := hw
      rw [oneCls_desc h1 hzw]
      have := H z
      rw [oneCls_desc h2 hzw] at this
      exact ⟨fun hφ => ⟨⟨z, hzw⟩, this.1 ⟨⟨w, hzw⟩, hφ⟩⟩, fun h => (this.2 h.2).2⟩
    · exact ⟨fun h => absurd h (not_desc_of_not_codom hw), fun h => absurd h.1 hw⟩
  · intro H z
    by_cases hz : z ∈ dom R
    · obtain ⟨w, hzw⟩ := hz
      rw [oneCls_desc h2 hzw]
      have := H w
      rw [oneCls_desc h1 hzw] at this
      exact ⟨fun h => (this.1 h.2).2, fun hψ => ⟨⟨w, hzw⟩, this.2 ⟨⟨z, hzw⟩, hψ⟩⟩⟩
    · exact ⟨fun h => absurd h.1 hz, fun h => absurd h (not_desc_of_not_codom (R := R˘) hz)⟩

/-- ✱72·25. \(\vdash\colon\ldotp R \rightarrow 1 : (y) \text{E}! \supset. (y) . = \breve{R}ʻRʻy\)

**Status.** proved (reading): the e-text's formula is garbled (`R → 1 : (y) E! ⊃ . (y) . = R̆'R'y`);
the demonstration (✱71·165, ✱72·241 and Imp) and the comment show that PM has
`⊢ :. R ∈ 1 → 1 : (y) . E!R'y : ⊃ . (y) . y = R̆'R'y` (transcription error). -/
theorem pm72_25 {R : α → β → Prop} :
    R ∈ arrow one one ∧ (∀ y, EDesc R y) → ∀ y, Desc2 R˘ R y (fun b => y = b) :=
  fun ⟨hR, hE⟩ y => (pm72_241 hR).1 (mem_codom_of_edesc (hE y))

/-- ✱72·26. \(\vdash:(y).\text{E}!Rʻy.\supset.R=\overrightarrow{\in \mid R}\)

PM's relation `∈` is `memRel` (✱62·01); as PM notes, the domain of `R` consists of classes. -/
theorem pm72_26 {R : Set α → β → Prop} : (∀ y, EDesc R y) → R = Rfwd (memRel ⨾ R) := by
  intro hE
  rw [rel_eq_iff]
  intro A y
  obtain ⟨b, hb⟩ := hE y
  have e : refs (memRel ⨾ R) y = b := by
    ext x
    constructor
    · rintro ⟨B, hxB, hB⟩
      rw [← (hb B).1 hB]
      exact hxB
    · intro hx
      exact ⟨b, hx, (hb b).2 rfl⟩
  show R A y ↔ A = refs (memRel ⨾ R) y
  rw [e]
  exact hb A

/-- ✱72·27. \(\vdash.\text{D}=\overrightarrow{{\in}\mid \text{D}}.\text{ᗡ}=\overrightarrow{{\in}·\text{ᗡ}} \quad[\text{*72·26.*33·12·121}]\)

**Status.** proved (reading): the e-text prints `∈·ᗡ` for `∈|ᗡ` in the second conjunct
(transcription error; the proof cites ✱72·26). -/
theorem pm72_27 :
    (D : Set α → (α → β → Prop) → Prop) = Rfwd (memRel ⨾ D) ∧
      (Dcnv : Set β → (α → β → Prop) → Prop) = Rfwd (memRel ⨾ Dcnv) :=
  ⟨pm72_26 fun R => EDesc_graph dom R, pm72_26 fun R => EDesc_graph codom R⟩

/-- ✱72·3. \(\vdash: \exists ! \lambda \cap (1 \rightarrow \text{Cls}).\supset . \dot{p}ʻ\lambda \in 1 \rightarrow \text{Cls}\) -/
theorem pm72_3 {L : Set (α → β → Prop)} :
    (L ∩ arrow one Cls).Nonempty → prodRel L ∈ arrow one Cls :=
  fun ⟨R, hRL, hR⟩ => pm71_22 ⟨hR, fun _ _ h => h R hRL⟩

/-- ✱72·301. \(\vdash: \exists ! \lambda \cap (\text{Cls} \rightarrow 1) .\supset . \dot{p}ʻ\lambda \in \text{Cls} \rightarrow 1\) -/
theorem pm72_301 {L : Set (α → β → Prop)} :
    (L ∩ arrow Cls one).Nonempty → prodRel L ∈ arrow Cls one :=
  fun ⟨R, hRL, hR⟩ => pm71_221 ⟨hR, fun _ _ h => h R hRL⟩

/-- ✱72·302. \(\vdash: \exists ! \lambda \cap (1 \rightarrow 1) .\supset . \dot{p}ʻ\lambda \in 1 \rightarrow 1\) -/
theorem pm72_302 {L : Set (α → β → Prop)} :
    (L ∩ arrow one one).Nonempty → prodRel L ∈ arrow one one :=
  fun ⟨R, hRL, hR⟩ => pm71_222 ⟨hR, fun _ _ h => h R hRL⟩

/-- ✱72·303. \(\vdash: \exists ! \lambda \cap (1 \rightarrow \text{Cls}). \exists ! \lambda \cap (\text{Cls} \rightarrow 1).\supset.\dot{p}ʻ\lambda \in 1 \rightarrow 1 \quad[\text{*72·3·301}]\) -/
theorem pm72_303 {L : Set (α → β → Prop)} :
    (L ∩ arrow one Cls).Nonempty ∧ (L ∩ arrow Cls one).Nonempty → prodRel L ∈ arrow one one :=
  fun ⟨h1, h2⟩ => one_one_iff.2 ⟨pm72_3 h1, pm72_301 h2⟩

/-- ✱72·31. \(\vdash: \dot{s}ʻ\lambda \in 1 \rightarrow \text{Cls} . \supset . \lambda \subset 1 \rightarrow \text{Cls}\) -/
theorem pm72_31 {L : Set (α → β → Prop)} : sumRel L ∈ arrow one Cls → L ⊆ arrow one Cls :=
  fun h P hP => pm71_22 ⟨h, fun _ _ hxy => ⟨P, hP, hxy⟩⟩

/-- ✱72·311. \(\vdash: \dot{s}ʻ\lambda \in \text{Cls} \rightarrow 1 .\supset. \lambda \subset \text{Cls} \rightarrow 1\) -/
theorem pm72_311 {L : Set (α → β → Prop)} : sumRel L ∈ arrow Cls one → L ⊆ arrow Cls one :=
  fun h P hP => pm71_221 ⟨h, fun _ _ hxy => ⟨P, hP, hxy⟩⟩

/-- ✱72·312. \(\vdash: \dot{s}ʻ\lambda \in 1 \rightarrow 1 .\supset. \lambda \subset 1 \rightarrow 1\) -/
theorem pm72_312 {L : Set (α → β → Prop)} : sumRel L ∈ arrow one one → L ⊆ arrow one one :=
  fun h P hP => pm71_222 ⟨h, fun _ _ hxy => ⟨P, hP, hxy⟩⟩

/-- ✱72·321. \[\begin{align}&\vdash\colon\ldotp \lambda\subset \text{Cls}\rightarrow 1:P,\,Q\in \lambda.\exists !\text{D}ʻP\cap \text{D}ʻQ.\supset_{P,Q}.P=Q:\supset.\dot{s}ʻ\lambda\in \text{Cls}\rightarrow 1\\ &[\text{Proof as in *72·32}]\end{align}\] -/
theorem pm72_321 {L : Set (α → β → Prop)} :
    (L ⊆ arrow Cls one ∧ ∀ P Q, (P ∈ L ∧ Q ∈ L) ∧ (dom P ∩ dom Q).Nonempty → P = Q) →
      sumRel L ∈ arrow Cls one := by
  rintro ⟨hL, hPQ⟩
  rw [mem_arrow_Cls_one]
  rintro x y z ⟨⟨P, hP, hy⟩, ⟨Q, hQ, hz⟩⟩
  have e : P = Q := hPQ P Q ⟨⟨hP, hQ⟩, x, ⟨y, hy⟩, ⟨z, hz⟩⟩
  subst e
  exact mem_arrow_Cls_one.1 (hL hP) x y z ⟨hy, hz⟩

/-- ✱72·322. \[\begin{align}\vdash\colon\ldotp \lambda\subset 1\rightarrow 1:&P,\,Q\in \lambda.\exists !\text{ᗡ}ʻP\cap \text{ᗡ}ʻQ.\supset_{P,Q}.P=Q:\\ &P,\,Q\in \lambda.\exists !\text{D}ʻP\cap \text{D}ʻQ.\supset_{P,Q}.P=Q:\supset.\dot{s}ʻ\lambda\in 1\rightarrow 1\\ [\text{*72·32·321}]\end{align}\] -/
theorem pm72_322 {L : Set (α → β → Prop)} :
    (L ⊆ arrow one one ∧ ∀ P Q, (P ∈ L ∧ Q ∈ L) ∧ (codom P ∩ codom Q).Nonempty → P = Q) ∧
        (∀ P Q, (P ∈ L ∧ Q ∈ L) ∧ (dom P ∩ dom Q).Nonempty → P = Q) →
      sumRel L ∈ arrow one one :=
  fun ⟨⟨hL, h1⟩, h2⟩ => one_one_iff.2
    ⟨pm72_32 ⟨fun _ hP => (one_one_iff.1 (hL hP)).1, h1⟩,
      pm72_321 ⟨fun _ hP => (one_one_iff.1 (hL hP)).2, h2⟩⟩

/-- ✱72·323. \(\vdash\colon\ldotp \lambda\subset 1\rightarrow 1:P,\,Q\in \lambda.\exists !CʻP\cap CʻQ.\supset_{P,Q}.P=Q:\supset.\dot{s}ʻ\lambda\in 1\rightarrow 1\) -/
theorem pm72_323 {L : Set (α → α → Prop)} :
    (L ⊆ arrow one one ∧ ∀ P Q, (P ∈ L ∧ Q ∈ L) ∧ (fld P ∩ fld Q).Nonempty → P = Q) →
      sumRel L ∈ arrow one one := by
  rintro ⟨hL, h⟩
  refine pm72_322 ⟨⟨hL, ?_⟩, ?_⟩
  · rintro P Q ⟨hPQ, x, ⟨y, hy⟩, ⟨z, hz⟩⟩
    exact h P Q ⟨hPQ, x, ⟨y, Or.inr hy⟩, ⟨z, Or.inr hz⟩⟩
  · rintro P Q ⟨hPQ, x, ⟨y, hy⟩, ⟨z, hz⟩⟩
    exact h P Q ⟨hPQ, x, ⟨y, Or.inl hy⟩, ⟨z, Or.inl hz⟩⟩

/-- ✱72·34. \(\vdash:R\in 1\rightarrow \text{Cls}.\exists !\kappa.\supset.pʻ\breve{R}ʻʻʻ\kappa=\breve{R}ʻʻpʻ\kappa\) -/
theorem pm72_34 {R : α → β → Prop} {K : Set (Set α)} :
    R ∈ arrow one Cls ∧ K.Nonempty → prodCls (R˘ ʻʻʻ K) = R˘ ʻʻ prodCls K := by
  rintro ⟨hR, B0, hB0⟩
  ext y
  constructor
  · intro h
    obtain ⟨x0, hx0, hx0y⟩ := h (R˘ ʻʻ B0) ⟨B0, hB0, rfl⟩
    refine ⟨x0, fun B hB => ?_, hx0y⟩
    obtain ⟨x, hx, hxy⟩ := h (R˘ ʻʻ B) ⟨B, hB, rfl⟩
    rw [mem_arrow_one_Cls.1 hR x0 x y ⟨hx0y, hxy⟩]
    exact hx
  · rintro ⟨x, hx, hxy⟩ X ⟨B, hB, hX⟩
    rw [show X = R˘ ʻʻ B from hX]
    exact ⟨x, hx B hB, hxy⟩

/-- ✱72·341. \(\vdash:R\in \text{Cls}\rightarrow 1.\exists !\kappa.\supset.pʻRʻʻʻ\kappa=Rʻʻpʻ\kappa\) -/
theorem pm72_341 {R : α → β → Prop} {K : Set (Set β)} :
    R ∈ arrow Cls one ∧ K.Nonempty → prodCls (R ʻʻʻ K) = R ʻʻ prodCls K :=
  fun ⟨hR, hK⟩ => pm72_34 ⟨Cls_one_iff_cnv.1 hR, hK⟩

/-- ✱72·4. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.\breve{R}ʻʻ\alpha\cap \breve{R}ʻʻ\beta=\breve{R}ʻʻ(\alpha\cap \beta)\) -/
theorem pm72_4 {R : α → β → Prop} {A B : Set α} :
    R ∈ arrow one Cls → R˘ ʻʻ A ∩ R˘ ʻʻ B = R˘ ʻʻ (A ∩ B) := by
  intro hR
  ext y
  rw [Set.mem_inter_iff, pm71_37 hR, pm71_37 hR, pm71_37 hR]
  by_cases hy : y ∈ codom R
  · obtain ⟨x, hx⟩ := hy
    rw [oneCls_desc hR hx, oneCls_desc hR hx, oneCls_desc hR hx]
    exact Iff.rfl
  · simp only [not_desc_of_not_codom hy, and_false]

/-- ✱72·401. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.Rʻʻ\alpha\cap Rʻʻ\beta=Rʻʻ(\alpha\cap \beta)\) -/
theorem pm72_401 {R : α → β → Prop} {A B : Set β} :
    R ∈ arrow Cls one → R ʻʻ A ∩ R ʻʻ B = R ʻʻ (A ∩ B) :=
  fun hR => pm72_4 (Cls_one_iff_cnv.1 hR)

/-- ✱72·41. \(\vdash:R\in 1\rightarrow \text{Cls}.\alpha\cap \beta=\Lambda.\supset.\breve{R}ʻʻ\alpha\cap \breve{R}ʻʻ\beta=\Lambda \quad[\text{*72·4.*37·29}]\) -/
theorem pm72_41 {R : α → β → Prop} {A B : Set α} :
    R ∈ arrow one Cls ∧ A ∩ B = Λ → R˘ ʻʻ A ∩ R˘ ʻʻ B = Λ := by
  rintro ⟨hR, h⟩
  rw [pm72_4 hR, h, img_Null]

/-- ✱72·411. \(\vdash:R\in \text{Cls}\rightarrow 1.\alpha\cap \beta=\Lambda.\supset.Rʻʻ\alpha\cap Rʻʻ\beta=\Lambda\) -/
theorem pm72_411 {R : α → β → Prop} {A B : Set β} :
    R ∈ arrow Cls one ∧ A ∩ B = Λ → R ʻʻ A ∩ R ʻʻ B = Λ :=
  fun ⟨hR, h⟩ => pm72_41 ⟨Cls_one_iff_cnv.1 hR, h⟩

/-- ✱72·42. \(\vdash:R\in 1\rightarrow \text{Cls}.\exists !\breve{R}ʻʻ\alpha\cap\breve{R}ʻʻ\beta.\supset.\exists !\alpha\cap\beta \quad[\text{*72·41.Transp}]\) -/
theorem pm72_42 {R : α → β → Prop} {A B : Set α} :
    R ∈ arrow one Cls ∧ (R˘ ʻʻ A ∩ R˘ ʻʻ B).Nonempty → (A ∩ B).Nonempty := by
  rintro ⟨hR, h⟩
  rw [pm72_4 hR] at h
  obtain ⟨y, x, hx, -⟩ := h
  exact ⟨x, hx⟩

/-- ✱72·421. \(\vdash:R\in \text{Cls}\rightarrow 1.\exists !Rʻʻ\alpha\cap Rʻʻ\beta.\supset.\exists !\alpha\cap\beta\) -/
theorem pm72_421 {R : α → β → Prop} {A B : Set β} :
    R ∈ arrow Cls one ∧ (R ʻʻ A ∩ R ʻʻ B).Nonempty → (A ∩ B).Nonempty :=
  fun ⟨hR, h⟩ => pm72_42 ⟨Cls_one_iff_cnv.1 hR, h⟩

private theorem inter_dom_sub {R : α → β → Prop} {A B : Set α} (hR : R ∈ arrow one Cls)
    (h : R˘ ʻʻ A = R˘ ʻʻ B) : A ∩ dom R ⊆ B ∩ dom R := by
  rintro x ⟨hxA, y, hxy⟩
  have hy : y ∈ R˘ ʻʻ B := h ▸ ⟨x, hxA, hxy⟩
  obtain ⟨x', hx'B, hx'y⟩ := hy
  rw [mem_arrow_one_Cls.1 hR x x' y ⟨hxy, hx'y⟩]
  exact ⟨hx'B, y, hx'y⟩

/-- ✱72·43. \(\vdash:R\in 1\rightarrow \text{Cls}.\breve{R}ʻʻ\alpha=\breve{R}ʻʻ\beta.\supset.\alpha\cap\text{D}ʻR=\beta\cap\text{D}ʻR\) -/
theorem pm72_43 {R : α → β → Prop} {A B : Set α} :
    R ∈ arrow one Cls ∧ R˘ ʻʻ A = R˘ ʻʻ B → A ∩ dom R = B ∩ dom R :=
  fun ⟨hR, h⟩ => Set.Subset.antisymm (inter_dom_sub hR h) (inter_dom_sub hR h.symm)

/-- ✱72·431. \(\vdash:R\in \text{Cls}\rightarrow 1.Rʻʻ\alpha=Rʻʻ\beta.\supset.\alpha\cap\text{ᗡ}ʻR=\beta\cap\text{ᗡ}ʻR\) -/
theorem pm72_431 {R : α → β → Prop} {A B : Set β} :
    R ∈ arrow Cls one ∧ R ʻʻ A = R ʻʻ B → A ∩ codom R = B ∩ codom R :=
  fun ⟨hR, h⟩ => pm72_43 ⟨Cls_one_iff_cnv.1 hR, h⟩

/-- ✱72·44. \[\begin{align}&\vdash:R\in 1\rightarrow \text{Cls}.\alpha\subset \text{D}ʻR.\beta\subset \text{D}ʻR.\breve{R}ʻʻ\alpha=\breve{R}ʻʻ\beta.\supset.\alpha=\beta\\ &[\text{*72·43.*22·621}]\end{align}\] -/
theorem pm72_44 {R : α → β → Prop} {A B : Set α} :
    ((R ∈ arrow one Cls ∧ A ⊆ dom R) ∧ B ⊆ dom R) ∧ R˘ ʻʻ A = R˘ ʻʻ B → A = B := by
  rintro ⟨⟨⟨hR, hA⟩, hB⟩, h⟩
  have e := pm72_43 ⟨hR, h⟩
  rwa [Set.inter_eq_left.2 hA, Set.inter_eq_left.2 hB] at e

/-- ✱72·441. \(\vdash:R\in \text{Cls}\rightarrow 1.\alpha\subset \text{ᗡ}ʻR.\beta\subset \text{ᗡ}ʻR.Rʻʻ\alpha=Rʻʻ\beta.\supset.\alpha=\beta\) -/
theorem pm72_441 {R : α → β → Prop} {A B : Set β} :
    ((R ∈ arrow Cls one ∧ A ⊆ codom R) ∧ B ⊆ codom R) ∧ R ʻʻ A = R ʻʻ B → A = B :=
  fun ⟨⟨⟨hR, hA⟩, hB⟩, h⟩ => pm72_44 ⟨⟨⟨Cls_one_iff_cnv.1 hR, hA⟩, hB⟩, h⟩

/-- ✱72·45. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.(\breve{R})_{\in}\upharpoonright \text{Cl}ʻ\text{D}ʻR\in 1\rightarrow 1\) -/
theorem pm72_45 {R : α → β → Prop} :
    R ∈ arrow one Cls → imgRel R˘ ↾ cl (dom R) ∈ arrow one one := by
  intro hR
  refine one_one_iff.2 ⟨pm71_26 pm72_15, ?_⟩
  rw [mem_arrow_Cls_one]
  rintro X A B ⟨⟨h1, hA⟩, h2, hB⟩
  exact pm72_44 ⟨⟨⟨hR, hA⟩, hB⟩,
    (show X = R˘ ʻʻ A from h1).symm.trans (show X = R˘ ʻʻ B from h2)⟩

/-- ✱72·451. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.R_{\in}\upharpoonright \text{Cl}ʻ\text{ᗡ}ʻR\in 1\rightarrow 1\) -/
theorem pm72_451 {R : α → β → Prop} :
    R ∈ arrow Cls one → imgRel R ↾ cl (codom R) ∈ arrow one one :=
  fun hR => pm72_45 (Cls_one_iff_cnv.1 hR)

private theorem img_inter_dom {R : α → β → Prop} {A : Set α} : R˘ ʻʻ A = R˘ ʻʻ (A ∩ dom R) := by
  ext y
  exact ⟨fun ⟨x, hx, hxy⟩ => ⟨x, ⟨hx, y, hxy⟩, hxy⟩, fun ⟨x, hx, hxy⟩ => ⟨x, hx.1, hxy⟩⟩

/-- ✱72·46. \[\begin{align}&\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\supset:\breve{R}ʻʻ\alpha=\breve{R}ʻʻ\beta.\equiv.\alpha\cap\text{D}ʻR=\beta\cap\text{D}ʻR\\ &[\text{*72·43.*37·263}]\end{align}\] -/
theorem pm72_46 {R : α → β → Prop} {A B : Set α} :
    R ∈ arrow one Cls → (R˘ ʻʻ A = R˘ ʻʻ B ↔ A ∩ dom R = B ∩ dom R) := by
  intro hR
  refine ⟨fun h => pm72_43 ⟨hR, h⟩, fun h => ?_⟩
  rw [img_inter_dom, h, ← img_inter_dom]

/-- ✱72·461. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:Rʻʻ\alpha=Rʻʻ\beta.\equiv.\alpha\cap\text{ᗡ}ʻR=\beta\cap\text{ᗡ}ʻR\) -/
theorem pm72_461 {R : α → β → Prop} {A B : Set β} :
    R ∈ arrow Cls one → (R ʻʻ A = R ʻʻ B ↔ A ∩ codom R = B ∩ codom R) :=
  fun hR => pm72_46 (Cls_one_iff_cnv.1 hR)

/-- ✱72·47. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\supset:\breve{R}ʻʻ\alpha=\text{ᗡ}ʻR.\equiv.\text{D}ʻR\subset \alpha\) -/
theorem pm72_47 {R : α → β → Prop} {A : Set α} :
    R ∈ arrow one Cls → (R˘ ʻʻ A = codom R ↔ dom R ⊆ A) := by
  intro hR
  have e : codom R = R˘ ʻʻ dom R := by
    ext y
    exact ⟨fun ⟨x, hx⟩ => ⟨x, ⟨y, hx⟩, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
  rw [e, pm72_46 hR, Set.inter_self, Set.inter_eq_right]

/-- ✱72·471. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:Rʻʻ\alpha=\text{D}ʻR.\equiv.\text{ᗡ}ʻR\subset \alpha\) -/
theorem pm72_471 {R : α → β → Prop} {A : Set β} :
    R ∈ arrow Cls one → (R ʻʻ A = dom R ↔ codom R ⊆ A) :=
  fun hR => pm72_47 (Cls_one_iff_cnv.1 hR)

/-- ✱72·48. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\alpha,\beta\in \text{Cl}ʻ\text{D}ʻR.\supset:\breve{R}ʻʻ\alpha=\breve{R}ʻʻ\beta.\equiv.\alpha=\beta\) -/
theorem pm72_48 {R : α → β → Prop} {A B : Set α} :
    R ∈ arrow one Cls ∧ (A ∈ cl (dom R) ∧ B ∈ cl (dom R)) → (R˘ ʻʻ A = R˘ ʻʻ B ↔ A = B) :=
  fun ⟨hR, hA, hB⟩ => ⟨fun h => pm72_44 ⟨⟨⟨hR, hA⟩, hB⟩, h⟩, fun h => h ▸ rfl⟩

/-- ✱72·481. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\alpha,\beta\in \text{Cl}ʻ\text{ᗡ}ʻR.\supset:Rʻʻ\alpha=Rʻʻ\beta.\equiv.\alpha=\beta\) -/
theorem pm72_481 {R : α → β → Prop} {A B : Set β} :
    R ∈ arrow Cls one ∧ (A ∈ cl (codom R) ∧ B ∈ cl (codom R)) → (R ʻʻ A = R ʻʻ B ↔ A = B) :=
  fun ⟨hR, h⟩ => pm72_48 ⟨Cls_one_iff_cnv.1 hR, h⟩

/-- ✱72·49. \(\vdash\colon\ldotp Q\in 1\rightarrow \text{Cls}.\supset:\text{ᗡ}ʻ(P\mid Q)=\text{ᗡ}ʻQ.\equiv.\text{D}ʻQ\subset \text{ᗡ}ʻP\) -/
theorem pm72_49 {P : α → β → Prop} {Q : β → γ → Prop} :
    Q ∈ arrow one Cls → (codom (P ⨾ Q) = codom Q ↔ dom Q ⊆ codom P) := by
  intro hQ
  have e : codom (P ⨾ Q) = Q˘ ʻʻ codom P := by
    ext z
    exact ⟨fun ⟨x, y, hxy, hyz⟩ => ⟨y, ⟨x, hxy⟩, hyz⟩, fun ⟨y, ⟨x, hxy⟩, hyz⟩ => ⟨x, y, hxy, hyz⟩⟩
  rw [e]
  exact pm72_47 hQ

/-- ✱72·491. \(\vdash\colon\ldotp P\in \text{Cls}\rightarrow 1.\supset:\text{D}ʻ(P\mid Q)=\text{D}ʻP.\equiv.\text{ᗡ}ʻP\subset \text{D}ʻQ\) -/
theorem pm72_491 {P : α → β → Prop} {Q : β → γ → Prop} :
    P ∈ arrow Cls one → (dom (P ⨾ Q) = dom P ↔ codom P ⊆ dom Q) := by
  intro hP
  have e : dom (P ⨾ Q) = P ʻʻ dom Q := by
    ext x
    exact ⟨fun ⟨z, y, hxy, hyz⟩ => ⟨y, ⟨z, hyz⟩, hxy⟩, fun ⟨y, ⟨z, hyz⟩, hxy⟩ => ⟨z, y, hxy, hyz⟩⟩
  rw [e]
  exact pm72_471 hP

/-- ✱72·492. \[\begin{align}\vdash\colon\ldotp &P\in \text{Cls}\rightarrow 1.Q\in 1\rightarrow \text{Cls}.\supset:\\ &\text{D}ʻ(P\mid Q)=\text{D}ʻP.\text{ᗡ}ʻ(P\mid Q)=\text{ᗡ}ʻQ.\equiv.\text{ᗡ}ʻP=\text{D}ʻQ \quad[\text{*72·49·491}]\end{align}\] -/
theorem pm72_492 {P : α → β → Prop} {Q : β → γ → Prop} :
    P ∈ arrow Cls one ∧ Q ∈ arrow one Cls →
      (dom (P ⨾ Q) = dom P ∧ codom (P ⨾ Q) = codom Q ↔ codom P = dom Q) := by
  rintro ⟨hP, hQ⟩
  rw [pm72_491 hP, pm72_49 hQ]
  exact ⟨fun ⟨h1, h2⟩ => Set.Subset.antisymm h1 h2, fun h => ⟨h.le, h.ge⟩⟩

/-- ✱72·5. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.Rʻʻ\breve{R}ʻʻ\alpha=\alpha \cap \text{D}ʻR\) -/
theorem pm72_5 {R : α → β → Prop} {A : Set α} :
    R ∈ arrow one Cls → R ʻʻ R˘ ʻʻ A = A ∩ dom R := by
  intro hR
  ext x
  constructor
  · rintro ⟨y, ⟨x', hx'A, hx'y⟩, hxy⟩
    rw [mem_arrow_one_Cls.1 hR x x' y ⟨hxy, hx'y⟩]
    exact ⟨hx'A, y, hx'y⟩
  · rintro ⟨hxA, y, hxy⟩
    exact ⟨y, ⟨x, hxA, hxy⟩, hxy⟩

/-- ✱72·501. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\breve{R}ʻʻRʻʻ\alpha=\alpha \cap \text{ᗡ}ʻR\) -/
theorem pm72_501 {R : α → β → Prop} {A : Set β} :
    R ∈ arrow Cls one → R˘ ʻʻ R ʻʻ A = A ∩ codom R :=
  fun hR => pm72_5 (Cls_one_iff_cnv.1 hR)

/-- ✱72·502. \(\vdash:R\in 1\rightarrow \text{Cls}.\alpha\subset \text{D}ʻR.\supset.Rʻʻ\breve{R}ʻʻ\alpha=\alpha \quad[\text{*72·5.*22·621}]\) -/
theorem pm72_502 {R : α → β → Prop} {A : Set α} :
    R ∈ arrow one Cls ∧ A ⊆ dom R → R ʻʻ R˘ ʻʻ A = A := by
  rintro ⟨hR, hA⟩
  rw [pm72_5 hR, Set.inter_eq_left.2 hA]

/-- ✱72·503. \(\vdash:R\in \text{Cls}\rightarrow 1.\alpha\subset \text{ᗡ}ʻR.\supset.\breve{R}ʻʻRʻʻ\alpha=\alpha\) -/
theorem pm72_503 {R : α → β → Prop} {A : Set β} :
    R ∈ arrow Cls one ∧ A ⊆ codom R → R˘ ʻʻ R ʻʻ A = A :=
  fun ⟨hR, hA⟩ => pm72_502 ⟨Cls_one_iff_cnv.1 hR, hA⟩

/-- ✱72·504. \(\vdash:\lambda\subset \text{D}ʻR_{\in}.\supset.R_{\in}ʻʻ\breve{R}_{\in}ʻʻ\lambda=\lambda \quad[\text{*72·502·15}]\)

`R̆_∈` is `imgRelCnv R`, i.e. `Cnv'R_∈` (✱37·03), not `(R̆)_∈`, as PM notes. -/
theorem pm72_504 {R : α → β → Prop} {L : Set (Set α)} :
    L ⊆ dom (imgRel R) → imgRel R ʻʻ imgRelCnv R ʻʻ L = L :=
  fun hL => pm72_502 ⟨pm72_15, hL⟩

/-- ✱72·51. \(\vdash:R\in 1\rightarrow \text{Cls}.\alpha\subset \text{D}ʻR.\beta=\breve{R}ʻʻ\alpha.\supset.\alpha=Rʻʻ\beta \quad[\text{*72·502.*20·18}]\) -/
theorem pm72_51 {R : α → β → Prop} {A : Set α} {B : Set β} :
    (R ∈ arrow one Cls ∧ A ⊆ dom R) ∧ B = R˘ ʻʻ A → A = R ʻʻ B := by
  rintro ⟨h, rfl⟩
  exact (pm72_502 h).symm

/-- ✱72·511. \(\vdash:R\in \text{Cls}\rightarrow 1.\beta\subset \text{ᗡ}ʻR.\alpha=Rʻʻ\beta.\supset.\beta=\breve{R}ʻʻ\alpha \quad[\text{*72·503.*20·18}]\) -/
theorem pm72_511 {R : α → β → Prop} {A : Set α} {B : Set β} :
    (R ∈ arrow Cls one ∧ B ⊆ codom R) ∧ A = R ʻʻ B → B = R˘ ʻʻ A :=
  fun ⟨⟨hR, hB⟩, h⟩ => pm72_51 ⟨⟨Cls_one_iff_cnv.1 hR, hB⟩, h⟩

/-- ✱72·512. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\beta\subset \text{ᗡ}ʻR.\supset:y\in \beta.\equiv.Rʻy\in Rʻʻ\beta\) -/
theorem pm72_512 {R : α → β → Prop} {B : Set β} {y : β} :
    R ∈ arrow one one ∧ B ⊆ codom R → (y ∈ B ↔ Desc R y (fun b => b ∈ R ʻʻ B)) := by
  rintro ⟨hR, hB⟩
  rw [one_one_iff] at hR
  calc y ∈ B ↔ y ∈ R˘ ʻʻ R ʻʻ B := by rw [pm72_503 ⟨hR.2, hB⟩]
    _ ↔ Desc R y (fun b => b ∈ R ʻʻ B) := pm71_37 hR.1

/-- ✱72·513. \(\vdash\colon\ldotp R\in 1\rightarrow 1:(y).\text{E}!Rʻy:\supset:y\in \beta.\equiv.Rʻy\in Rʻʻ\beta \quad[\text{*72·512.*33·431}]\) -/
theorem pm72_513 {R : α → β → Prop} {B : Set β} {y : β} :
    R ∈ arrow one one ∧ (∀ y, EDesc R y) → (y ∈ B ↔ Desc R y (fun b => b ∈ R ʻʻ B)) :=
  fun ⟨hR, hE⟩ => pm72_512 ⟨hR, fun y _ => mem_codom_of_edesc (hE y)⟩

/-- ✱72·52. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\alpha\subset \text{D}ʻR.\beta\subset \text{ᗡ}ʻR.\supset:\alpha=Rʻʻ\beta.\equiv.\beta=\breve{R}ʻʻ\alpha \quad[\text{*72·51·511}]\) -/
theorem pm72_52 {R : α → β → Prop} {A : Set α} {B : Set β} :
    (R ∈ arrow one one ∧ A ⊆ dom R) ∧ B ⊆ codom R → (A = R ʻʻ B ↔ B = R˘ ʻʻ A) := by
  rintro ⟨⟨hR, hA⟩, hB⟩
  rw [one_one_iff] at hR
  exact ⟨fun h => pm72_511 ⟨⟨hR.2, hB⟩, h⟩, fun h => pm72_51 ⟨⟨hR.1, hA⟩, h⟩⟩

/-- ✱72·53. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\supset:\beta\subset \text{ᗡ}ʻR.\alpha=Rʻʻ\beta.\equiv.\alpha\subset \text{D}ʻR.\beta=\breve{R}ʻʻ\alpha\) -/
theorem pm72_53 {R : α → β → Prop} {A : Set α} {B : Set β} :
    R ∈ arrow one one → (B ⊆ codom R ∧ A = R ʻʻ B ↔ A ⊆ dom R ∧ B = R˘ ʻʻ A) := by
  intro hR
  have hR' := one_one_iff.1 hR
  constructor
  · rintro ⟨hB, rfl⟩
    refine ⟨?_, pm72_511 ⟨⟨hR'.2, hB⟩, rfl⟩⟩
    rintro x ⟨y, -, hxy⟩
    exact ⟨y, hxy⟩
  · rintro ⟨hA, rfl⟩
    refine ⟨?_, pm72_51 ⟨⟨hR'.1, hA⟩, rfl⟩⟩
    rintro y ⟨x, -, hxy⟩
    exact ⟨x, hxy⟩

/-- ✱72·54. \(\vdash:R\in 1\rightarrow 1.\supset.\text{Cnv}ʻ(R_{\in}\upharpoonright \text{Cl}ʻ\text{ᗡ}ʻR)=(\breve{R})_{\in}\upharpoonright \text{Cl}ʻ\text{D}ʻR\)

`Cnv'(…)` is written with the converse `(…)˘` (Basic §5, `desc_Cnv`). -/
theorem pm72_54 {R : α → β → Prop} :
    R ∈ arrow one one → (imgRel R ↾ cl (codom R))˘ = imgRel R˘ ↾ cl (dom R) := by
  intro hR
  rw [rel_eq_iff]
  intro B A
  exact and_comm.trans ((pm72_53 hR).trans and_comm)

/-- ✱72·541. \[\begin{align}&\vdash:R\in 1\rightarrow 1.S=\breve{R}.\supset.\text{Cnv}ʻ(R_{\in}\upharpoonright \text{D}ʻS_{\in})=S_{\in}\upharpoonright \text{D}ʻR_{\in}\\ &[\text{*71·48·481.*72·54}]\end{align}\] -/
theorem pm72_541 {R : α → β → Prop} {S : β → α → Prop} :
    R ∈ arrow one one ∧ S = R˘ → (imgRel R ↾ dom (imgRel S))˘ = imgRel S ↾ dom (imgRel R) := by
  rintro ⟨hR, rfl⟩
  have hR' := one_one_iff.1 hR
  rw [pm71_481 hR'.2, pm71_48 hR'.1]
  exact pm72_54 hR

/-- ✱72·55. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.\alpha\upharpoonleft R=R\upharpoonright \breve{R}ʻʻ\alpha=\alpha\upharpoonleft R\upharpoonright \breve{R}ʻʻ\alpha\) -/
theorem pm72_55 {R : α → β → Prop} {A : Set α} :
    R ∈ arrow one Cls → A ◁ R = R ↾ R˘ ʻʻ A ∧ R ↾ R˘ ʻʻ A = A ◁ R ↾ R˘ ʻʻ A := by
  intro hR
  have h1 : A ◁ R = R ↾ R˘ ʻʻ A := by
    rw [rel_eq_iff]
    intro x y
    constructor
    · rintro ⟨hx, hxy⟩
      exact ⟨hxy, x, hx, hxy⟩
    · rintro ⟨hxy, x', hx', hx'y⟩
      rw [mem_arrow_one_Cls.1 hR x x' y ⟨hxy, hx'y⟩]
      exact ⟨hx', hx'y⟩
  refine ⟨h1, ?_⟩
  rw [← h1]
  rw [rel_eq_iff]
  intro x y
  constructor
  · rintro ⟨hx, hxy⟩
    exact ⟨⟨hx, hxy⟩, x, hx, hxy⟩
  · rintro ⟨h, -⟩
    exact h

/-- ✱72·551. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.R\upharpoonright \beta=(Rʻʻ\beta)\upharpoonleft R=(Rʻʻ\beta)\upharpoonleft R\upharpoonright \beta\) -/
theorem pm72_551 {R : α → β → Prop} {B : Set β} :
    R ∈ arrow Cls one → R ↾ B = (R ʻʻ B) ◁ R ∧ (R ʻʻ B) ◁ R = (R ʻʻ B) ◁ R ↾ B := by
  intro hR
  have h1 : R ↾ B = (R ʻʻ B) ◁ R := by
    rw [rel_eq_iff]
    intro x y
    constructor
    · rintro ⟨hxy, hy⟩
      exact ⟨⟨y, hy, hxy⟩, hxy⟩
    · rintro ⟨⟨y', hy', hxy'⟩, hxy⟩
      rw [mem_arrow_Cls_one.1 hR x y y' ⟨hxy, hxy'⟩]
      exact ⟨hxy', hy'⟩
  refine ⟨h1, ?_⟩
  rw [← h1]
  rw [rel_eq_iff]
  intro x y
  constructor
  · rintro ⟨hxy, hy⟩
    exact ⟨⟨hxy, hy⟩, hy⟩
  · rintro ⟨h, -⟩
    exact h

/-- ✱72·57. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow \text{Cls}.\lambda=\breve{Q}ʻʻ\mu.\supset.\mu\cap \text{D}ʻQ=Qʻʻ\lambda\)

PM's `λ`, `μ` (classes) are `L`, `M`. -/
theorem pm72_57 {Q : α → β → Prop} {L : Set β} {M : Set α} :
    Q ↾ L ∈ arrow one Cls ∧ L = Q˘ ʻʻ M → M ∩ dom Q = Q ʻʻ L := by
  rintro ⟨hQ, rfl⟩
  ext x
  constructor
  · rintro ⟨hxM, y, hxy⟩
    exact ⟨y, ⟨x, hxM, hxy⟩, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    have ⟨x', hx'M, hx'y⟩ := hy
    have e : x = x' := mem_arrow_one_Cls.1 hQ x x' y ⟨⟨hxy, hy⟩, hx'y, hy⟩
    subst e
    exact ⟨hx'M, y, hxy⟩

/-- ✱72·59. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.S\mid R\mid \breve{R}=S\upharpoonright \text{D}ʻR\) -/
theorem pm72_59 {S : γ → α → Prop} {R : α → β → Prop} :
    R ∈ arrow one Cls → S ⨾ R ⨾ R˘ = S ↾ dom R := by
  intro hR
  rw [rel_eq_iff]
  intro u z
  constructor
  · rintro ⟨y, ⟨x, hux, hxy⟩, hzy⟩
    rw [mem_arrow_one_Cls.1 hR x z y ⟨hxy, hzy⟩] at hux
    exact ⟨hux, y, hzy⟩
  · rintro ⟨huz, y, hzy⟩
    exact ⟨y, ⟨z, huz, hzy⟩, hzy⟩

/-- ✱72·591. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.S\mid \breve{R}\mid R=S\upharpoonright \text{ᗡ}ʻR\) -/
theorem pm72_591 {S : γ → β → Prop} {R : α → β → Prop} :
    R ∈ arrow Cls one → S ⨾ R˘ ⨾ R = S ↾ codom R :=
  fun hR => pm72_59 (Cls_one_iff_cnv.1 hR)

/-- ✱72·6. \(\vdash:R\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻS\subset \text{D}ʻR.\supset.S\mid R\mid \breve{R}=S \quad[\text{*72·59.*35·452}]\) -/
theorem pm72_6 {S : γ → α → Prop} {R : α → β → Prop} :
    R ∈ arrow one Cls ∧ codom S ⊆ dom R → S ⨾ R ⨾ R˘ = S := by
  rintro ⟨hR, hS⟩
  rw [pm72_59 hR, rel_eq_iff]
  exact fun x y => ⟨And.left, fun h => ⟨h, hS ⟨x, h⟩⟩⟩

/-- ✱72·601. \(\vdash:R\in \text{Cls}\rightarrow 1.\text{ᗡ}ʻS\subset \text{ᗡ}ʻR.\supset.S\mid \breve{R}\mid R=S\) -/
theorem pm72_601 {S : γ → β → Prop} {R : α → β → Prop} :
    R ∈ arrow Cls one ∧ codom S ⊆ codom R → S ⨾ R˘ ⨾ R = S :=
  fun ⟨hR, hS⟩ => pm72_6 ⟨Cls_one_iff_cnv.1 hR, hS⟩

/-- ✱72·61. \(\vdash:R\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻSʻ\subset \text{D}ʻR.\supset.S\mid R\mid \breve{R}\mid \breve{S}=S\mid \breve{S} \quad[\text{*72·6.*34·27}]\)

**Status.** proved (reading): the e-text prints `ᗡ'S'` (with a stray `'`) for `ᗡ'S` in the
hypothesis (transcription error; cf. ✱72·6, ✱72·611). -/
theorem pm72_61 {S : γ → α → Prop} {R : α → β → Prop} :
    R ∈ arrow one Cls ∧ codom S ⊆ dom R → S ⨾ R ⨾ R˘ ⨾ S˘ = S ⨾ S˘ := by
  intro h
  rw [pm72_6 h]

/-- ✱72·611. \(\vdash:R\in \text{Cls}\rightarrow 1.\text{ᗡ}ʻS\subset \text{ᗡ}ʻR.\supset.S\mid \breve{R}\mid R\mid \breve{S}=S\mid \breve{S}\) -/
theorem pm72_611 {S : γ → β → Prop} {R : α → β → Prop} :
    R ∈ arrow Cls one ∧ codom S ⊆ codom R → S ⨾ R˘ ⨾ R ⨾ S˘ = S ⨾ S˘ := by
  intro h
  rw [pm72_601 h]

/-- ✱72·62. \(\vdash:R\in 1\rightarrow \text{Cls}.S=R\mid \breve{R}.\supset.S^{2}=S.S=\breve{S}\) -/
theorem pm72_62 {R : α → β → Prop} {S : α → α → Prop} :
    R ∈ arrow one Cls ∧ S = R ⨾ R˘ → rsq S = S ∧ S = S˘ := by
  rintro ⟨hR, rfl⟩
  refine ⟨?_, ?_⟩ <;> rw [rel_eq_iff] <;> intro x z
  · constructor
    · rintro ⟨y, ⟨w, hxw, hyw⟩, ⟨w', hyw', hzw'⟩⟩
      rw [mem_arrow_one_Cls.1 hR x y w ⟨hxw, hyw⟩]
      exact ⟨w', hyw', hzw'⟩
    · rintro ⟨w, hxw, hzw⟩
      exact ⟨x, ⟨w, hxw, hxw⟩, ⟨w, hxw, hzw⟩⟩
  · exact ⟨fun ⟨w, h1, h2⟩ => ⟨w, h2, h1⟩, fun ⟨w, h1, h2⟩ => ⟨w, h2, h1⟩⟩

/-- ✱72·621. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\supset:y(\breve{R}\mid R)z.\equiv.Rʻy=Rʻz\) -/
theorem pm72_621 {R : α → β → Prop} {y z : β} :
    R ∈ arrow one Cls → ((R˘ ⨾ R) y z ↔ Desc R y (fun b => Desc R z (fun c => b = c))) := by
  intro hR
  rw [desc_eq_desc_iff]
  constructor
  · rintro ⟨x, hxy, hxz⟩
    exact ⟨x, oneCls_uniq hR hxy, oneCls_uniq hR hxz⟩
  · rintro ⟨b, hb, hc⟩
    exact ⟨b, (hb b).2 rfl, (hc b).2 rfl⟩

/-- ✱72·622. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:y(R\mid \breve{R})z.\equiv.\breve{R}ʻy=\breve{R}ʻz\) -/
theorem pm72_622 {R : α → β → Prop} {y z : α} :
    R ∈ arrow Cls one → ((R ⨾ R˘) y z ↔ Desc R˘ y (fun b => Desc R˘ z (fun c => b = c))) :=
  fun hR => pm72_621 (Cls_one_iff_cnv.1 hR)

/-- ✱72·63. \(\vdash:R\in \text{Cls}\rightarrow 1.S=R\mid \breve{R}.\supset.S^{2}=S.S=\breve{S}\) -/
theorem pm72_63 {R : α → β → Prop} {S : α → α → Prop} :
    R ∈ arrow Cls one ∧ S = R ⨾ R˘ → rsq S = S ∧ S = S˘ := by
  rintro ⟨hR, rfl⟩
  refine ⟨?_, ?_⟩ <;> rw [rel_eq_iff] <;> intro x z
  · constructor
    · rintro ⟨y, ⟨w, hxw, hyw⟩, ⟨w', hyw', hzw'⟩⟩
      rw [mem_arrow_Cls_one.1 hR y w w' ⟨hyw, hyw'⟩] at hxw
      exact ⟨w', hxw, hzw'⟩
    · rintro ⟨w, hxw, hzw⟩
      exact ⟨x, ⟨w, hxw, hxw⟩, ⟨w, hxw, hzw⟩⟩
  · exact ⟨fun ⟨w, h1, h2⟩ => ⟨w, h2, h1⟩, fun ⟨w, h1, h2⟩ => ⟨w, h2, h1⟩⟩

/-- ✱72·64. \(\vdash:S^{2}=S.S=\breve{S}.R=\text{Cnv}ʻ(\overleftarrow{S}\upharpoonright \text{D}ʻS).\supset.R\in \text{Cls}\rightarrow 1.S=R\mid \breve{R}\)

`Cnv'(…)` is written with the converse `(…)˘`; `R` relates members of the field of `S` to
classes of them (its type is forced by the hypothesis `R = Cnv'(S⃖ ↾ D'S)`). -/
theorem pm72_64 {S : α → α → Prop} {R : α → Set α → Prop} :
    (rsq S = S ∧ S = S˘) ∧ R = (Rbwd S ↾ dom S)˘ → R ∈ arrow Cls one ∧ S = R ⨾ R˘ := by
  rintro ⟨⟨hsq, hsym⟩, rfl⟩
  have trans : ∀ a b c, S a b → S b c → S a c := by
    intro a b c h1 h2
    have h : rsq S a c := ⟨b, h1, h2⟩
    rw [hsq] at h
    exact h
  have symm : ∀ a b, S a b → S b a := by
    intro a b h
    rw [hsym]
    exact h
  refine ⟨?_, ?_⟩
  · rw [mem_arrow_Cls_one]
    rintro x A B ⟨⟨h1, -⟩, h2, -⟩
    exact (show A = rels S x from h1).trans (show B = rels S x from h2).symm
  · rw [rel_eq_iff]
    intro y z
    constructor
    · intro hyz
      refine ⟨rels S y, ⟨rfl, z, hyz⟩, ?_, y, symm y z hyz⟩
      show rels S y = rels S z
      ext w
      exact ⟨fun h => trans z y w (symm y z hyz) h, fun h => trans y z w hyz h⟩
    · rintro ⟨A, ⟨h1, -⟩, h2, w, hzw⟩
      have e : rels S y = rels S z :=
        (show A = rels S y from h1).symm.trans (show A = rels S z from h2)
      have hzz : S z z := trans z w z hzw (symm z w hzw)
      have hz : z ∈ rels S z := hzz
      rw [← e] at hz
      exact hz

/-- ✱72·65. \(\vdash:S^{2}=S.S=\breve{S}.\equiv.(\exists R).R\in \text{Cls}\rightarrow 1.S=R\mid \breve{R} \quad[\text{*72·63·64}]\)

**Status.** proved (reading): the apparent variable `R` of `(∃R)` is typically ambiguous; it is
taken at the type of relations from the members of the field of `S` to classes of them, the
type of the `R` constructed in ✱72·64 (from which the implication from left to right is
proved). The implication from right to left holds for `R` of any type (✱72·63). -/
theorem pm72_65 {S : α → α → Prop} :
    rsq S = S ∧ S = S˘ ↔ ∃ R : α → Set α → Prop, R ∈ arrow Cls one ∧ S = R ⨾ R˘ := by
  constructor
  · intro h
    exact ⟨_, pm72_64 ⟨h, rfl⟩⟩
  · rintro ⟨R, hR, hS⟩
    exact pm72_63 ⟨hR, hS⟩

/-- ✱72·66. \(\vdash:S^{2}\unicode{x2abd}S.S=\breve{S}.\equiv.(\exists R).R\in \text{Cls}\rightarrow 1.S=R\mid \breve{R} \quad[\text{*72·65.*34·81}]\)

**Status.** proved (reading): the type of the apparent variable `R` is chosen as in ✱72·65. -/
theorem pm72_66 {S : α → α → Prop} :
    rsq S ⪽ S ∧ S = S˘ ↔ ∃ R : α → Set α → Prop, R ∈ arrow Cls one ∧ S = R ⨾ R˘ := by
  rw [← pm72_65]
  constructor
  · rintro ⟨hsub, hsym⟩
    refine ⟨?_, hsym⟩
    rw [rel_eq_iff]
    intro x z
    refine ⟨hsub x z, fun h => ?_⟩
    have hzx : S z x := by
      rw [hsym]
      exact h
    exact ⟨z, h, hsub z z ⟨x, hzx, h⟩⟩
  · rintro ⟨hsq, hsym⟩
    refine ⟨fun x y h => ?_, hsym⟩
    rw [hsq] at h
    exact h

/-- ✱72·7. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.\overleftarrow{R}\upharpoonright \text{D}ʻR\in 1\rightarrow 1\) -/
theorem pm72_7 {R : α → β → Prop} : R ∈ arrow one Cls → Rbwd R ↾ dom R ∈ arrow one one := by
  intro hR
  refine one_one_iff.2 ⟨pm71_26 pm72_12.2, ?_⟩
  rw [mem_arrow_Cls_one]
  rintro X y z ⟨⟨h1, w, hyw⟩, h2, -⟩
  have e : rels R y = rels R z := (show X = rels R y from h1).symm.trans (show X = rels R z from h2)
  have hw : w ∈ rels R z := e ▸ hyw
  exact mem_arrow_one_Cls.1 hR y z w ⟨hyw, hw⟩

/-- ✱72·71. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\overrightarrow{R}\upharpoonright \text{ᗡ}ʻR\in 1\rightarrow 1\) -/
theorem pm72_71 {R : α → β → Prop} : R ∈ arrow Cls one → Rfwd R ↾ codom R ∈ arrow one one :=
  fun hR => pm72_7 (Cls_one_iff_cnv.1 hR)

/-- ✱72·72. \(\vdash:R\in 1\rightarrow 1.\supset.\overrightarrow{R}\upharpoonright \text{ᗡ}ʻR,\overleftarrow{R}\upharpoonright \text{D}ʻR\in 1\rightarrow 1\) -/
theorem pm72_72 {R : α → β → Prop} :
    R ∈ arrow one one → Rfwd R ↾ codom R ∈ arrow one one ∧ Rbwd R ↾ dom R ∈ arrow one one :=
  fun hR => ⟨pm72_71 (one_one_iff.1 hR).2, pm72_7 (one_one_iff.1 hR).1⟩

/-- ✱72·8. \(\vdash:\lambda\subset \text{D}ʻx\downarrow .\supset.\text{ᗡ}\upharpoonright \lambda\in 1\rightarrow 1 \quad[\text{*55·28·22.*71·58}]\)

PM's `λ` is `L`. -/
theorem pm72_8 {x : α} {L : Set (α → β → Prop)} :
    L ⊆ dom (coupleL x : (α → β → Prop) → β → Prop) →
      (Dcnv : Set β → (α → β → Prop) → Prop) ↾ L ∈ arrow one one := by
  intro hL
  refine one_one_iff.2 ⟨pm71_26 pm72_131, ?_⟩
  rw [mem_arrow_Cls_one]
  rintro B P Q ⟨⟨hP, hPL⟩, hQ, hQL⟩
  obtain ⟨y, hy⟩ := hL hPL
  obtain ⟨y', hy'⟩ := hL hQL
  rw [show P = x ↓ y from hy] at hP ⊢
  rw [show Q = x ↓ y' from hy'] at hQ ⊢
  have hyB : y ∈ B := by
    rw [show B = codom (x ↓ y) from hP]
    exact ⟨x, rfl, rfl⟩
  rw [show B = codom (x ↓ y') from hQ] at hyB
  obtain ⟨_, -, e⟩ := hyB
  rw [e]

/-- ✱72·81. \(\vdash:\lambda\subset \text{D}ʻ\downarrow x.\supset.\text{D}\upharpoonright \lambda\in 1\rightarrow 1 \quad[\text{*55·281·221.*71·58}]\)

PM's `λ` is `L`. -/
theorem pm72_81 {x : β} {L : Set (α → β → Prop)} :
    L ⊆ dom (coupleR x : (α → β → Prop) → α → Prop) →
      (D : Set α → (α → β → Prop) → Prop) ↾ L ∈ arrow one one := by
  intro hL
  refine one_one_iff.2 ⟨pm71_26 pm72_13, ?_⟩
  rw [mem_arrow_Cls_one]
  rintro A P Q ⟨⟨hP, hPL⟩, hQ, hQL⟩
  obtain ⟨y, hy⟩ := hL hPL
  obtain ⟨y', hy'⟩ := hL hQL
  rw [show P = y ↓ x from hy] at hP ⊢
  rw [show Q = y' ↓ x from hy'] at hQ ⊢
  have hyA : y ∈ A := by
    rw [show A = dom (y ↓ x) from hP]
    exact ⟨x, rfl, rfl⟩
  rw [show A = dom (y' ↓ x) from hQ] at hyA
  obtain ⟨_, e, -⟩ := hyA
  rw [e]

/-- ✱72·9. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.S\unicode{x2abd}R.\supset:\text{E}!Sʻy.\equiv.Rʻy=Sʻy.\equiv.y\in \text{ᗡ}ʻS\) -/
theorem pm72_9 {R S : α → β → Prop} {y : β} :
    R ∈ arrow one Cls ∧ S ⪽ R →
      (EDesc S y ↔ Desc R y (fun b => Desc S y (fun c => b = c))) ∧
        (Desc R y (fun b => Desc S y (fun c => b = c)) ↔ y ∈ codom S) := by
  rintro ⟨hR, hSR⟩
  have hS : S ∈ arrow one Cls := pm71_22 ⟨hR, hSR⟩
  have h1 : EDesc S y ↔ Desc R y (fun b => Desc S y (fun c => b = c)) := by
    rw [desc_eq_desc_iff]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, oneCls_uniq hR (hSR b y ((hb b).2 rfl)), hb⟩
    · rintro ⟨b, -, hc⟩
      exact ⟨b, hc⟩
  exact ⟨h1, h1.symm.trans (pm71_163.1 hS y).symm⟩

/-- ✱72·91. \(\vdash:R\in 1\rightarrow \text{Cls}.S\unicode{x2abd}R.\supset.\text{ᗡ}ʻ(R\dot{-}S)=\text{ᗡ}ʻR-\text{ᗡ}ʻS\) -/
theorem pm72_91 {R S : α → β → Prop} :
    R ∈ arrow one Cls ∧ S ⪽ R → codom (R ∸ S) = codom R \ codom S := by
  rintro ⟨hR, hSR⟩
  ext y
  constructor
  · rintro ⟨x, hxy, hn⟩
    refine ⟨⟨x, hxy⟩, ?_⟩
    rintro ⟨x', hx'⟩
    rw [mem_arrow_one_Cls.1 hR x' x y ⟨hSR x' y hx', hxy⟩] at hx'
    exact hn hx'
  · rintro ⟨⟨x, hx⟩, hn⟩
    exact ⟨x, hx, fun h => hn ⟨x, h⟩⟩

/-- ✱72·911. \(\vdash:R\in \text{Cls}\rightarrow 1.S\unicode{x2abd}R.\supset.\text{D}ʻ(R\dot{-}S)=\text{D}ʻR-\text{D}ʻS\) -/
theorem pm72_911 {R S : α → β → Prop} :
    R ∈ arrow Cls one ∧ S ⪽ R → dom (R ∸ S) = dom R \ dom S :=
  fun ⟨hR, hSR⟩ => pm72_91 (R := R˘) (S := S˘) ⟨Cls_one_iff_cnv.1 hR, fun x y h => hSR y x h⟩

/-- ✱72·92. \(\vdash:R\in 1\rightarrow \text{Cls}.S\unicode{x2abd}R.\supset.S=R\upharpoonright \text{ᗡ}ʻS\) -/
theorem pm72_92 {R S : α → β → Prop} : R ∈ arrow one Cls ∧ S ⪽ R → S = R ↾ codom S := by
  rintro ⟨hR, hSR⟩
  rw [rel_eq_iff]
  intro x y
  constructor
  · intro h
    exact ⟨hSR x y h, x, h⟩
  · rintro ⟨hxy, x', hx'⟩
    rw [mem_arrow_one_Cls.1 hR x x' y ⟨hxy, hSR x' y hx'⟩]
    exact hx'

/-- ✱72·921. \(\vdash:R\in \text{Cls}\rightarrow 1.S\unicode{x2abd}R.\supset.S=(\text{D}ʻS)\upharpoonleft R\) -/
theorem pm72_921 {R S : α → β → Prop} : R ∈ arrow Cls one ∧ S ⪽ R → S = dom S ◁ R := by
  rintro ⟨hR, hSR⟩
  rw [rel_eq_iff]
  intro x y
  constructor
  · intro h
    exact ⟨⟨y, h⟩, hSR x y h⟩
  · rintro ⟨⟨y', hy'⟩, hxy⟩
    rw [mem_arrow_Cls_one.1 hR x y y' ⟨hxy, hSR x y' hy'⟩]
    exact hy'

/-- ✱72·93. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.R\unicode{x2abd}S.\equiv:y\in \text{ᗡ}ʻR.\supset_{y}.(Rʻy)Sy\) -/
theorem pm72_93 {R S : α → β → Prop} :
    R ∈ arrow one Cls ∧ R ⪽ S ↔ ∀ y, y ∈ codom R → Desc R y (fun b => S b y) := by
  constructor
  · rintro ⟨hR, hsub⟩ y ⟨x, hx⟩
    exact (oneCls_desc hR hx).2 (hsub x y hx)
  · intro h
    have hR : R ∈ arrow one Cls := oneCls_iff_edesc.2 fun y hy => edesc_of_desc (h y hy)
    exact ⟨hR, fun x y hxy => (oneCls_desc hR hxy).1 (h y ⟨x, hxy⟩)⟩

/-- ✱72·931. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.R\unicode{x2abd}S.\equiv:x\in DʻR.\supset_{x}.xS(\breve{R}ʻx)\) -/
theorem pm72_931 {R S : α → β → Prop} :
    R ∈ arrow Cls one ∧ R ⪽ S ↔ ∀ x, x ∈ dom R → Desc R˘ x (fun b => S x b) :=
  (and_congr Cls_one_iff_cnv ⟨fun h x y => h y x, fun h x y => h y x⟩).trans
    (pm72_93 (R := R˘) (S := S˘))

/-- ✱72·94. \(\vdash\colon\ldotp R,\,S\in 1\rightarrow \text{Cls}.\supset:\dot{\exists}!R\dot{\cap}S.\equiv.(\exists y).Rʻy=Sʻy\) -/
theorem pm72_94 {R S : α → β → Prop} :
    R ∈ arrow one Cls ∧ S ∈ arrow one Cls →
      (rEx (R ⩀ S) ↔ ∃ y, Desc R y (fun b => Desc S y (fun c => b = c))) := by
  rintro ⟨hR, hS⟩
  constructor
  · rintro ⟨x, y, hRxy, hSxy⟩
    exact ⟨y, desc_eq_desc_iff.2 ⟨x, oneCls_uniq hR hRxy, oneCls_uniq hS hSxy⟩⟩
  · rintro ⟨y, hd⟩
    obtain ⟨b, hb, hc⟩ := desc_eq_desc_iff.1 hd
    exact ⟨b, y, (hb b).2 rfl, (hc b).2 rfl⟩

end PrincipiaMathematica
