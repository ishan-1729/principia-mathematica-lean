import PrincipiaMathematica.Defs.Part1

/-!
# Part I, Section C: Classes and relations

Volume 1. Numbers: ✱20, ✱21, ✱22.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w u'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

/-!
## [✱20] General theory of classes

*(Vol. 1, p. 196)*

> *Summary of* *20.
>
> The following theory of classes, although it provides a notation to represent them, avoids the assumption that there are such things as classes. This it does by merely defining propositions in whose expression the symbols representing classes occur, just as, in *14, we defined propositions containing descriptions.
>
> The characteristics of a class are that it consists of all the terms satisfying some propositional function, so that every propositional function determines a class, and two functions which are formally equivalent (*i.e.* such that whenever either is true, the other is true also) determine the same class, while conversely two functions which determine the same class are formally equivalent. When two functions are formally equivalent, we shall say that they have the same *extension*. The incomplete symbols which take the place of classes serve the purpose of technically providing something identical in the case of two functions having the same extension; without something to represent classes, we cannot, for example, count the combinations that can be formed out of a given set of objects.
>
> …

**Lean reading.** Classes are read as terms of `Set α` (Basic §6): `ẑ(ψz)` is `{z | ψ z}`, `x ∈ α`
is `x ∈ A`, a Greek apparent variable is `A : Set α`, and a function of classes `f{…}` is
`f : Set α → Prop`. PM's contextual definitions ✱20·01, ✱20·07, ✱20·071, ✱20·08 therefore become
theorems (each class is recovered as `{z | z ∈ A}`), and the characteristic property of classes
✱20·15/✱20·43 is `Set.ext`. Predicative functions `φ!` are arbitrary Lean functions, so the
analogues of reducibility (✱20·112, ✱20·7–✱20·703) hold with `g := f`; in ✱20·111 a function of
functions `f(φ!ẑ)` is `f : (α → Prop) → Prop`, and `f{ẑ(φ!z)}` is written out by ✱20·01.
Descriptions are `TheIs`, with PM's convention (stated before ✱20·5) that descriptions have a larger
scope than classes; descriptions of classes (✱20·55–✱20·59) are `TheIs` at type `Set α`. The
meta-level ✱20·62 and ✱20·633 are recorded as derivable rules and ✱20·631, ✱20·632 (significance) as
typing remarks.

**Status.** proved (all propositions; ✱20·01, ✱20·07, ✱20·071, ✱20·08 proved (reading) (contextual
Dfs); ✱20·111, ✱20·112, ✱20·62, ✱20·633, ✱20·7, ✱20·701, ✱20·702, ✱20·703 proved (reading); ✱20·631,
✱20·632 remark; the other Dfs definition)
-/

/-- ✱20·01 (Df). \(f\{\hat{z}(\psi z)\}.=:(\exists \phi):\phi!x.\equiv_{x}.\psi x:f(\phi!\hat{z}) \quad\text{Df}\)

**Status.** proved (reading): PM's contextual definition of classes (no-class theory); classes are
read as terms of `Set α` (Basic §6), so the definition becomes the theorem that `f{ẑ(ψz)}` agrees
with its definiens. -/
theorem pm20_01 {ψ : α → Prop} {f : Set α → Prop} :
    f {z | ψ z} ↔ ∃ φ : α → Prop, (∀ x, φ x ↔ ψ x) ∧ f {z | φ z} := by
  constructor
  · exact fun h => ⟨ψ, fun _ => Iff.rfl, h⟩
  · rintro ⟨φ, hφ, hf⟩
    rwa [setOf_eq_setOf_iff.2 hφ] at hf

/-- ✱20·02 (Df). \(x\in (\phi!\hat{z}).=.\phi!x \quad\text{Df}\) -/
theorem pm20_02 {φ : α → Prop} {x : α} : x ∈ {z | φ z} ↔ φ x := Iff.rfl

/-- ✱20·03 (Df). \(\text{Cls}=\hat{\alpha}\{(\exists \phi).\alpha=\hat{z}(\phi!z)\} \quad\text{Df}\) -/
theorem pm20_03 : (Cls : Set (Set α)) = {A | ∃ φ : α → Prop, A = {z | φ z}} := rfl

/-- ✱20·04 (Df). \(x,\,y\in \alpha.=.x\in \alpha.y\in \alpha \quad\text{Df}\) -/
theorem pm20_04 {x y : α} {A : Set α} : Mem2 x y A ↔ x ∈ A ∧ y ∈ A := Iff.rfl

/-- ✱20·05 (Df). \(x,\,y,\,z\in \alpha.=.x,\,y\in \alpha.z\in \alpha \quad\text{Df}\) -/
theorem pm20_05 {x y z : α} {A : Set α} : Mem3 x y z A ↔ Mem2 x y A ∧ z ∈ A := Iff.rfl

/-- ✱20·06 (Df). \(x{\sim}\in \alpha.=.{\sim}(x\in \alpha) \quad\text{Df}\) -/
theorem pm20_06 {x : α} {A : Set α} : x ∉ A ↔ ¬(x ∈ A) := Iff.rfl

/-- ✱20·07 (Df). (\(\alpha).f\alpha.=.(\phi).f\{\hat{z}(\phi!z)\} \quad\text{Df}\)

**Status.** proved (reading): apparent variables ranging over classes are `A : Set α`; PM defines
them through predicative functions, and in Lean the two quantifications are equivalent (not
`Iff.rfl`: `A` is recovered as `{z | z ∈ A}`). -/
theorem pm20_07 {f : Set α → Prop} : (∀ A : Set α, f A) ↔ ∀ φ : α → Prop, f {z | φ z} :=
  ⟨fun h _ => h _, fun h A => h (· ∈ A)⟩

/-- ✱20·071 (Df). (\(\exists \alpha).f\alpha.=.(\exists \phi).f\{\hat{z}(\phi!z)\} \quad\text{Df}\)

**Status.** proved (reading): as ✱20·07, for the existential quantifier over classes. -/
theorem pm20_071 {f : Set α → Prop} : (∃ A : Set α, f A) ↔ ∃ φ : α → Prop, f {z | φ z} :=
  ⟨fun ⟨A, h⟩ => ⟨(· ∈ A), h⟩, fun ⟨_, h⟩ => ⟨_, h⟩⟩

/-- ✱20·072 (Df). \([(℩\alpha)(\phi\alpha)].f(℩\alpha)(\phi\alpha).=:(\exists \gamma):\phi\alpha.\equiv_{\alpha}.\alpha=\gamma:f\gamma \quad\text{Df}\) -/
theorem pm20_072 {φ f : Set α → Prop} : TheIs φ f ↔ ∃ γ, (∀ A, φ A ↔ A = γ) ∧ f γ := Iff.rfl

/-- ✱20·08 (Df). \(f\{\hat{\alpha}(\psi\alpha)\}.=:(\exists \phi):\psi\alpha.\equiv_{\alpha}.\phi!\alpha:f(\phi!\hat{\alpha}) \quad\text{Df}\)

**Status.** proved (reading): classes of classes are read as terms of `Set (Set α)`, so the
contextual definition becomes a theorem, as ✱20·01. -/
theorem pm20_08 {ψ : Set α → Prop} {f : Set (Set α) → Prop} :
    f {A | ψ A} ↔ ∃ φ : Set α → Prop, (∀ A, ψ A ↔ φ A) ∧ f {A | φ A} := by
  constructor
  · exact fun h => ⟨ψ, fun _ => Iff.rfl, h⟩
  · rintro ⟨φ, hφ, hf⟩
    rwa [← setOf_eq_setOf_iff.2 hφ] at hf

/-- ✱20·081 (Df). \(\alpha\in \psi!\hat{\alpha}.=.\psi!\alpha \quad\text{Df}\) -/
theorem pm20_081 {ψ : Set α → Prop} {A : Set α} : A ∈ {B : Set α | ψ B} ↔ ψ A := Iff.rfl

/-- ✱20·1. \(\vdash\colon\ldotp f\{\hat{z}(\psi z)\}.\equiv:(\exists \phi):\phi!x.\equiv_{x}.\psi x:f\{\phi!\hat{z}\} \quad[\text{*4·2.(*20·01)}]\) -/
theorem pm20_1 {ψ : α → Prop} {f : Set α → Prop} :
    f {z | ψ z} ↔ ∃ φ : α → Prop, (∀ x, φ x ↔ ψ x) ∧ f {z | φ z} :=
  pm20_01

/-- ✱20·11. \(\vdash\colon\ldotp \psi x.\equiv_{x}.\chi x:\supset:f\{\hat{z}(\psi z)\}.\equiv.f\{\hat{z}(\chi z)\}\) -/
theorem pm20_11 {ψ χ : α → Prop} {f : Set α → Prop} :
    (∀ x, ψ x ↔ χ x) → (f {z | ψ z} ↔ f {z | χ z}) :=
  fun h => by rw [setOf_eq_setOf_iff.2 h]

/-- ✱20·111. \(\vdash\colon\ldotp f(\phi!\hat{z}).\equiv_{\phi}.g(\phi!\hat{z}):\supset:f\{\hat{z}(\phi!z)\}.\equiv_{\phi}.g\{\hat{z}(\phi!z)\}\)

**Status.** proved (reading): `f(φ!ẑ)` and `g(φ!ẑ)` are functions of the (predicative) function `φ`
(in PM possibly intensional), i.e. `f g : (α → Prop) → Prop` applied to `φ`. Such an `f` does not
apply to a class `Set α`, so `f{ẑ(φ!z)}` is written out by its definiens ✱20·01,
`(∃ψ) : ψ!x . ≡_x . φ!x : f(ψ!ẑ)`, which is how PM eliminates it (the proof cites ✱20·1). -/
theorem pm20_111 {f g : (α → Prop) → Prop} :
    (∀ φ : α → Prop, f φ ↔ g φ) → ∀ φ : α → Prop,
      (∃ ψ : α → Prop, (∀ x, ψ x ↔ φ x) ∧ f ψ) ↔ (∃ ψ : α → Prop, (∀ x, ψ x ↔ φ x) ∧ g ψ) :=
  fun h _ => ⟨fun ⟨ψ, hψ, hf⟩ => ⟨ψ, hψ, (h ψ).1 hf⟩, fun ⟨ψ, hψ, hg⟩ => ⟨ψ, hψ, (h ψ).2 hg⟩⟩

/-- ✱20·112. \(\vdash\colon\ldotp (\exists g)\colon\ldotp f\{\hat{z}(\phi!z)\}.\equiv_{\phi}.g!\{\hat{z}(\phi!z)\}\)

**Status.** proved (reading): the axiom of reducibility for classes as arguments; every Lean
function is predicative (Basic §4), so `g := f`. -/
theorem pm20_112 {f : Set α → Prop} :
    ∃ g : Set α → Prop, ∀ φ : α → Prop, f {z | φ z} ↔ g {z | φ z} :=
  ⟨f, fun _ => Iff.rfl⟩

/-- ✱20·12. \(\vdash:(\exists \phi):\phi!x.\equiv_{x}.\psi x:f\{\hat{z}(\psi z)\}.\equiv.f\{\hat{z}(\phi!z)\} \quad[\text{*20·11.*12·1}]\) -/
theorem pm20_12 {ψ : α → Prop} {f : Set α → Prop} :
    ∃ φ : α → Prop, (∀ x, φ x ↔ ψ x) ∧ (f {z | ψ z} ↔ f {z | φ z}) :=
  ⟨ψ, fun _ => Iff.rfl, Iff.rfl⟩

/-- ✱20·13. \(\vdash\colon\ldotp \psi x.\equiv_{x}.\chi x:\supset.\hat{z}(\psi z)=\hat{z}(\chi z)\) -/
theorem pm20_13 {ψ χ : α → Prop} : (∀ x, ψ x ↔ χ x) → {z | ψ z} = {z | χ z} :=
  fun h => setOf_eq_setOf_iff.2 h

/-- ✱20·14. \(\vdash\colon\ldotp \hat{z}(\psi z)=\hat{z}(\chi z).\supset:\psi x.\equiv_{x}.\chi x\) -/
theorem pm20_14 {ψ χ : α → Prop} : {z | ψ z} = {z | χ z} → ∀ x, ψ x ↔ χ x :=
  fun h => setOf_eq_setOf_iff.1 h

/-- ✱20·15. \(\vdash\colon\ldotp \psi x.\equiv_{x}.\chi x:\equiv.\hat{z}(\psi z)=\hat{z}(\chi z) \quad[\text{*20·13·14}]\) -/
theorem pm20_15 {ψ χ : α → Prop} : (∀ x, ψ x ↔ χ x) ↔ {z | ψ z} = {z | χ z} :=
  ⟨pm20_13, pm20_14⟩

/-- ✱20·151. \(\vdash.(\exists \phi).\hat{z}(\psi z)=\hat{z}(\phi!z)\) -/
theorem pm20_151 {ψ : α → Prop} : ∃ φ : α → Prop, {z | ψ z} = {z | φ z} := ⟨ψ, rfl⟩

/-- ✱20·16. \(\vdash:(\exists \phi):f\{\hat{z}(\psi z)\}.\equiv.f{\hat{z}(\phi!z)} \quad[\text{*20·12}]\) -/
theorem pm20_16 {ψ : α → Prop} {f : Set α → Prop} :
    ∃ φ : α → Prop, f {z | ψ z} ↔ f {z | φ z} :=
  ⟨ψ, Iff.rfl⟩

/-- ✱20·17. \(\vdash:(\phi).f\{\hat{z}(\phi!z)\}.\supset.f\{\hat{z}(\psi z)\} \quad[\text{*20·16.*10·1}]\) -/
theorem pm20_17 {ψ : α → Prop} {f : Set α → Prop} :
    (∀ φ : α → Prop, f {z | φ z}) → f {z | ψ z} :=
  fun h => h ψ

/-- ✱20·18. \(\vdash\colon\ldotp \hat{z}(\phi z)=\hat{z}(\psi z).\supset:f\{\hat{z}(\phi z)\}.\equiv.f\{\hat{z}(\psi z)\} \quad[\text{*20·11·15}]\) -/
theorem pm20_18 {φ ψ : α → Prop} {f : Set α → Prop} :
    {z | φ z} = {z | ψ z} → (f {z | φ z} ↔ f {z | ψ z}) :=
  fun h => by rw [h]

/-- ✱20·19. \(\vdash\colon\ldotp \hat{z}(\psi z)=\hat{z}(\chi z).\equiv:(f):f!\hat{z}(\psi z).\supset.f!\hat{z}(\chi z)\) -/
theorem pm20_19 {ψ χ : α → Prop} :
    {z | ψ z} = {z | χ z} ↔ ∀ f : Set α → Prop, f {z | ψ z} → f {z | χ z} :=
  ⟨fun h _ hf => h ▸ hf, fun h => h (fun A => {z | ψ z} = A) rfl⟩

/-- ✱20·191. \[\begin{align}\vdash\colon\ldotp \hat{z}(\psi z)=\hat{z}(\chi z).\equiv:(f):f!\hat{z}(\psi z).\equiv.&f!\hat{z}(\chi z)\\ &\quad[\text{*20·18·19.*10·22}]\end{align}\] -/
theorem pm20_191 {ψ χ : α → Prop} :
    {z | ψ z} = {z | χ z} ↔ ∀ f : Set α → Prop, f {z | ψ z} ↔ f {z | χ z} :=
  ⟨fun h _ => by rw [h], fun h => (h (fun A => {z | ψ z} = A)).1 rfl⟩

/-- ✱20·2. \(\vdash.\hat{z}(\phi z)=\hat{z}(\phi z)\) -/
theorem pm20_2 {φ : α → Prop} : {z | φ z} = {z | φ z} := rfl

/-- ✱20·21. \(\vdash:\hat{z}(\phi z)=\hat{z}(\psi z).\equiv.\hat{z}(\psi z)=\hat{z}(\phi z) \quad[\text{*20·15.*10·32}]\) -/
theorem pm20_21 {φ ψ : α → Prop} : {z | φ z} = {z | ψ z} ↔ {z | ψ z} = {z | φ z} := eq_comm

/-- ✱20·22. \[\begin{align}\vdash:\hat{z}(\phi z)=\hat{z}(\psi z).\hat{z}(\psi z)=\hat{z}(\chi z).\supset.\hat{z}(\phi z)&=\hat{z}(\chi z)\\ &\quad[\text{*20·15.*10·301}]\end{align}\] -/
theorem pm20_22 {φ ψ χ : α → Prop} :
    {z | φ z} = {z | ψ z} ∧ {z | ψ z} = {z | χ z} → {z | φ z} = {z | χ z} :=
  fun ⟨h1, h2⟩ => h1.trans h2

/-- ✱20·23. \(\vdash:\hat{z}(\phi z)=\hat{z}(\psi z).\hat{z}(\phi z)=\hat{z}(\chi z).\supset.\hat{z}(\psi z)=\hat{z}(\chi z) \quad[\text{*20·21·22}]\) -/
theorem pm20_23 {φ ψ χ : α → Prop} :
    {z | φ z} = {z | ψ z} ∧ {z | φ z} = {z | χ z} → {z | ψ z} = {z | χ z} :=
  fun ⟨h1, h2⟩ => h1.symm.trans h2

/-- ✱20·24. \(\vdash:\hat{z}(\psi z)=\hat{z}(\phi z).\hat{z}(\chi z)=\hat{z}(\phi z).\supset.\hat{z}(\psi z)=\hat{z}(\chi z) \quad[\text{*20·21·22}]\) -/
theorem pm20_24 {φ ψ χ : α → Prop} :
    {z | ψ z} = {z | φ z} ∧ {z | χ z} = {z | φ z} → {z | ψ z} = {z | χ z} :=
  fun ⟨h1, h2⟩ => h1.trans h2.symm

/-- ✱20·25. \(\vdash\colon\ldotp \alpha=\hat{z}(\phi z).\equiv_{\alpha}.\alpha=\hat{z}(\psi z):\equiv.\hat{z}(\phi z)=\hat{z}(\psi z)\) -/
theorem pm20_25 {φ ψ : α → Prop} :
    (∀ A : Set α, A = {z | φ z} ↔ A = {z | ψ z}) ↔ {z | φ z} = {z | ψ z} :=
  ⟨fun h => (h _).1 rfl, fun h _ => by rw [h]⟩

/-- ✱20·3. \(\vdash:x\in \hat{z}(\psi z).\equiv.\psi x\) -/
theorem pm20_3 {ψ : α → Prop} {x : α} : x ∈ {z | ψ z} ↔ ψ x := Iff.rfl

/-- ✱20·31. \(\vdash\colon\ldotp \hat{z}(\psi z)=\hat{z}(\chi z).\equiv:x\in \hat{z}(\psi z).\equiv_{x}.x\in \hat{z}(\chi z) \quad[\text{*20·15·3}]\) -/
theorem pm20_31 {ψ χ : α → Prop} :
    {z | ψ z} = {z | χ z} ↔ ∀ x, x ∈ {z | ψ z} ↔ x ∈ {z | χ z} :=
  Set.ext_iff

/-- ✱20·32. \(\vdash.\hat{x}\{x\in \hat{z}(\phi z)\}=\hat{z}(\phi z) \quad[\text{*20·3·15}]\) -/
theorem pm20_32 {φ : α → Prop} : {x | x ∈ {z | φ z}} = {z | φ z} := rfl

/-- ✱20·33. \(\vdash\colon\ldotp \alpha=\hat{z}(\phi z).\equiv:x\in \alpha.\equiv_{x}.\phi x\) -/
theorem pm20_33 {A : Set α} {φ : α → Prop} : A = {z | φ z} ↔ ∀ x, x ∈ A ↔ φ x :=
  Set.ext_iff

/-- ✱20·34. \(\vdash\colon\ldotp x=y.\equiv:x\in \alpha.\supset_{\alpha}.y\in \alpha\) -/
theorem pm20_34 {x y : α} : x = y ↔ ∀ A : Set α, x ∈ A → y ∈ A :=
  ⟨fun h _ hx => h ▸ hx, fun h => h {z | x = z} rfl⟩

/-- ✱20·35. \(\vdash\colon\ldotp x=y.\equiv:x\in \alpha.\equiv_{\alpha}.y\in \alpha \quad[\text{*20·3.*13·11}]\) -/
theorem pm20_35 {x y : α} : x = y ↔ ∀ A : Set α, x ∈ A ↔ y ∈ A :=
  ⟨fun h _ => by rw [h], fun h => (h {z | x = z}).1 rfl⟩

/-- ✱20·4. \(\vdash:\alpha\in \text{Cls}.\equiv.(\exists \phi).\alpha=\hat{z}(\phi!z) \quad[\text{*20·3.(*20·03)}]\) -/
theorem pm20_4 {A : Set α} : A ∈ Cls ↔ ∃ φ : α → Prop, A = {z | φ z} := Iff.rfl

/-- ✱20·41. \(\vdash.\hat{z}(\psi z)\in \text{Cls} \quad[\text{*20·4·151}]\) -/
theorem pm20_41 {ψ : α → Prop} : {z | ψ z} ∈ (Cls : Set (Set α)) := ⟨ψ, rfl⟩

/-- ✱20·42. \(\vdash.\hat{z}(z\in \alpha)=\alpha\) -/
theorem pm20_42 {A : Set α} : {z | z ∈ A} = A := rfl

/-- ✱20·43. \(\vdash\colon\ldotp \alpha=\beta.\equiv:x\in \alpha.\equiv_{x}.x\in \beta \quad[\text{*20·31}]\) -/
theorem pm20_43 {A B : Set α} : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B := Set.ext_iff

/-- ✱20·5. \(\vdash:(℩x)(\phi x)\in \hat{z}(\psi z).\equiv.\psi\{(℩x)(\phi x)\}\) -/
theorem pm20_5 {φ ψ : α → Prop} : TheIs φ (fun b => b ∈ {z | ψ z}) ↔ TheIs φ ψ := Iff.rfl

/-- ✱20·51. \(\vdash\colon\ldotp (℩x)(\phi x)=b.\equiv:(℩x)(\phi x)\in \alpha.\equiv_{\alpha}.b\in \alpha\) -/
theorem pm20_51 {φ : α → Prop} {b : α} :
    TheIs φ (fun c => c = b) ↔ ∀ A : Set α, TheIs φ (fun c => c ∈ A) ↔ b ∈ A := by
  constructor
  · rintro ⟨c, hc, rfl⟩ A
    exact TheIs_iff_of_unique hc
  · intro h
    obtain ⟨c, hc, hcb⟩ := (h {z | z = b}).2 rfl
    exact ⟨c, hc, hcb⟩

/-- ✱20·52. \(\vdash\colon\ldotp \text{E}!(℩x)(\phi x).\equiv:(\exists b):(℩x)(\phi x)\in \alpha.\equiv_{\alpha}.b\in \alpha\) -/
theorem pm20_52 {φ : α → Prop} :
    EBang φ ↔ ∃ b, ∀ A : Set α, TheIs φ (fun c => c ∈ A) ↔ b ∈ A := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, fun A => TheIs_iff_of_unique hb⟩
  · rintro ⟨b, h⟩
    obtain ⟨c, hc, -⟩ := (h {z | z = b}).2 rfl
    exact ⟨c, hc⟩

/-- ✱20·53. \(\vdash\colon\ldotp \beta=\alpha.\supset_{\beta}.\phi\beta:\equiv.\phi\alpha\) -/
theorem pm20_53 {φ : Set α → Prop} {A : Set α} : (∀ B : Set α, B = A → φ B) ↔ φ A :=
  ⟨fun h => h A rfl, fun h _ hB => hB ▸ h⟩

/-- ✱20·54. \(\vdash:(\exists \beta).\beta=\alpha.\phi\beta.\equiv.\phi\alpha\) -/
theorem pm20_54 {φ : Set α → Prop} {A : Set α} : (∃ B : Set α, B = A ∧ φ B) ↔ φ A :=
  ⟨fun ⟨_, hB, h⟩ => hB ▸ h, fun h => ⟨A, rfl, h⟩⟩

/-- ✱20·55. \(\vdash.\hat{z}(\phi z)=(℩\alpha)(x\in \alpha.\equiv_{x}.\phi x)\) -/
theorem pm20_55 {φ : α → Prop} :
    TheIs (fun A : Set α => ∀ x, x ∈ A ↔ φ x) (fun B => {z | φ z} = B) :=
  ⟨{z | φ z}, fun _ => pm20_33.symm, rfl⟩

/-- ✱20·56. \(\vdash.\text{E}!(℩\alpha)(x\in \alpha.\equiv_{x}.\phi x) \quad[\text{*20·55.*14·21}]\) -/
theorem pm20_56 {φ : α → Prop} : EBang (fun A : Set α => ∀ x, x ∈ A ↔ φ x) :=
  ⟨{z | φ z}, fun _ => pm20_33.symm⟩

/-- ✱20·57. \(\vdash\colon\ldotp \hat{z}(\phi z)=(℩\alpha)(f\alpha).\supset:g\{\hat{z}(\phi z)\}.\equiv.g\{(℩\alpha)(f\alpha)\}\) -/
theorem pm20_57 {φ : α → Prop} {f g : Set α → Prop} :
    TheIs f (fun B => {z | φ z} = B) → (g {z | φ z} ↔ TheIs f g) := by
  rintro ⟨B, hB, rfl⟩
  exact (TheIs_iff_of_unique hB).symm

/-- ✱20·58. \(\vdash.\hat{z}(\phi z)=(℩\alpha)\{\alpha=\hat{z}(\phi z)\}\) -/
theorem pm20_58 {φ : α → Prop} :
    TheIs (fun A : Set α => A = {z | φ z}) (fun B => {z | φ z} = B) :=
  ⟨{z | φ z}, fun _ => Iff.rfl, rfl⟩

/-- ✱20·59. \(\vdash:\hat{z}(\phi z)=(℩\alpha)(f\alpha).\equiv.(℩\alpha)(f\alpha)=\hat{z}(\phi z)\) -/
theorem pm20_59 {φ : α → Prop} {f : Set α → Prop} :
    TheIs f (fun B => {z | φ z} = B) ↔ TheIs f (fun B => B = {z | φ z}) :=
  ⟨fun ⟨B, hB, h⟩ => ⟨B, hB, h.symm⟩, fun ⟨B, hB, h⟩ => ⟨B, hB, h.symm⟩⟩

/-- ✱20·6. \(\vdash:(\exists \alpha).f\alpha.\equiv.{\sim}\{(\alpha).{\sim}f\alpha\}\) -/
theorem pm20_6 {f : Set α → Prop} : (∃ A : Set α, f A) ↔ ¬ ∀ A : Set α, ¬ f A :=
  not_forall_not.symm

/-- ✱20·61. \(\vdash:(\alpha).f\alpha.\supset.f\beta\) -/
theorem pm20_61 {f : Set α → Prop} {B : Set α} : (∀ A : Set α, f A) → f B := fun h => h B

/-- ✱20·62. When \(f\beta\) is true, whatever possible argument of the form \(\hat{z}(\phi!z)\) \(\beta\) may be, then (\(\alpha).f\alpha\) is true.

**Status.** proved (reading): a rule of inference, the analogue of ✱10·11 (generalization).
Asserting `fβ` for every possible argument `β` of the form `ẑ(φ!z)` is a proof of
`∀ φ, f {z | φ z}`; the declaration derives `(α).fα`, i.e. `∀ A : Set α, f A`, from it. -/
theorem pm20_62 {f : Set α → Prop} (h : ∀ φ : α → Prop, f {z | φ z}) : ∀ A : Set α, f A :=
  fun A => h (· ∈ A)

/-- ✱20·63. \(\vdash\colon\ldotp (\alpha).p\lor f\alpha.\supset :p.\lor .(\alpha).f\alpha\) -/
theorem pm20_63 {p : Prop} {f : Set α → Prop} :
    (∀ A : Set α, p ∨ f A) → p ∨ ∀ A : Set α, f A :=
  fun h => (Classical.em p).elim Or.inl fun hp => Or.inr fun A => (h A).resolve_left hp

/-- ✱20·631. If "\(f\alpha\)" is significant, then if \(\beta\) is of the same type as \(\alpha\), "\(f\beta\)" is significant, and vice versa.

**Status.** remark: the analogue of ✱10·121, about significance (meta-level). In Lean a function of
classes is `f : Set α → Prop`, and it applies to every class `B : Set α` of the type of `α`; the
declaration records this typing (`f B` is a proposition whenever `f A` is). -/
def pm20_631 (f : Set α → Prop) (_A B : Set α) : Prop := f B

/-- ✱20·632. If, for some \(\alpha\), there is a proposition \(f\alpha\), then there is a function \(f\hat{\alpha}\), and vice versa.

**Status.** remark: the analogue of ✱10·122 (meta-level): a proposition `fα` about a class gives the
function `fα̂`, here `fun A => f A : Set α → Prop`, and conversely `f A` is a value of it. -/
def pm20_632 (f : Set α → Prop) : Set α → Prop := fun A => f A

/-- ✱20·633. "Whatever possible class \(\alpha\) may be, \(f(\alpha,\beta)\) is true whatever possible class \(\beta\) may be" implies the corresponding statement with \(\alpha\) and \(\beta\) interchanged except in "\(f(\alpha,\beta)\)." (The corresponding exception is to be understood in *11·07.)

**Status.** proved (reading): the analogue of ✱11·07 (interchange of apparent variables), a
meta-level statement; it is recorded by the Lean counterpart, the interchange of `∀ A` and `∀ B`
(`forall_comm`). The classes may be of different types. -/
theorem pm20_633 {f : Set α → Set β → Prop} :
    (∀ A : Set α, ∀ B : Set β, f A B) → ∀ B : Set β, ∀ A : Set α, f A B :=
  fun h B A => h A B

/-- ✱20·64. \(\vdash\colon\ldotp (\alpha).f\alpha:(\alpha).g\alpha:\supset .f\beta.g\beta\) -/
theorem pm20_64 {f g : Set α → Prop} {B : Set α} :
    (∀ A : Set α, f A) ∧ (∀ A : Set α, g A) → f B ∧ g B :=
  fun ⟨hf, hg⟩ => ⟨hf B, hg B⟩

/-- ✱20·7. \(\vdash:(\exists g):f\alpha.\equiv_{\alpha}.g!\alpha \quad[\text{*20·112}]\)

**Status.** proved (reading): the analogue of the axiom of reducibility ✱12·1 for classes; every
Lean function is predicative (Basic §4), so `g := f`. -/
theorem pm20_7 {f : Set α → Prop} : ∃ g : Set α → Prop, ∀ A : Set α, f A ↔ g A :=
  ⟨f, fun _ => Iff.rfl⟩

/-- ✱20·701. \(\vdash:(\exists g):f\{\hat{z}(\phi!z),x\}.\equiv_{\phi,x}.g!\{\hat{z}(\phi!z),x\}\)

**Status.** proved (reading): the analogue of ✱12·11 with a class and an individual as arguments;
every Lean function is predicative (Basic §4), so `g := f`. -/
theorem pm20_701 {f : Set α → β → Prop} :
    ∃ g : Set α → β → Prop, ∀ φ : α → Prop, ∀ x, f {z | φ z} x ↔ g {z | φ z} x :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- ✱20·702. \(\vdash:(\exists g):f\{x,\hat{z}(\phi!z)\}.\equiv_{\phi,x}.g!\{x,\hat{z}(\phi!z)\}\)

**Status.** proved (reading): as ✱20·701, with the arguments in the other order. -/
theorem pm20_702 {f : β → Set α → Prop} :
    ∃ g : β → Set α → Prop, ∀ φ : α → Prop, ∀ x, f x {z | φ z} ↔ g x {z | φ z} :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- ✱20·703. \(\vdash:(\exists g):f\{\hat{z}(\phi!z),\hat{z}(\psi!z)\}.\equiv_{\phi,\psi}.g!\{\hat{z}(\phi!z),\hat{z}(\psi!z)\}\)

**Status.** proved (reading): as ✱20·701, with two classes (possibly of different types) as
arguments. -/
theorem pm20_703 {f : Set α → Set β → Prop} :
    ∃ g : Set α → Set β → Prop, ∀ (φ : α → Prop) (ψ : β → Prop),
      f {z | φ z} {z | ψ z} ↔ g {z | φ z} {z | ψ z} :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- ✱20·71. \(\vdash\colon\ldotp \alpha=\beta.\equiv :g!\alpha.\supset_{g}.g!\beta \quad[\text{*20·19}]\) -/
theorem pm20_71 {A B : Set α} : A = B ↔ ∀ g : Set α → Prop, g A → g B :=
  ⟨fun h _ hg => h ▸ hg, fun h => h (fun C => A = C) rfl⟩

/-- ✱20·8. \(\vdash:\phi a \lor {\sim}\phi a.\supset.\hat{x}(\phi x \lor {\sim} \phi x)=\hat{x}(x=a.\lor.x \neq a)\) -/
theorem pm20_8 {φ : α → Prop} {a : α} :
    φ a ∨ ¬φ a → {x | φ x ∨ ¬φ x} = {x | x = a ∨ x ≠ a} :=
  fun _ => setOf_eq_setOf_iff.2 fun _ => ⟨fun _ => Classical.em _, fun _ => Classical.em _⟩

/-- ✱20·81. \(\vdash:\phi a \lor {\sim} \phi a.\psi a \lor {\sim} \psi a.\supset.\hat{x}(\phi x \lor {\sim}\phi x)=\hat{x}(\psi x \lor {\sim} \psi x)\) -/
theorem pm20_81 {φ ψ : α → Prop} {a : α} :
    (φ a ∨ ¬φ a) ∧ (ψ a ∨ ¬ψ a) → {x | φ x ∨ ¬φ x} = {x | ψ x ∨ ¬ψ x} :=
  fun _ => setOf_eq_setOf_iff.2 fun _ => ⟨fun _ => Classical.em _, fun _ => Classical.em _⟩

/-!
## [✱21] General theory of relations

*(Vol. 1, p. 211)*

> *Summary of* *21.
>
> The definitions and propositions of this number are exactly analogous to those of *20, from which they differ by being concerned with functions of two variables instead of one. A *relation*, as we shall use the word, will be understood in extension: it may be regarded as the class of couples (\(x,y)\) for which some given function \(\psi(x,y)\) is true. Its relation to the function \(\psi(\hat{x},\hat{y})\) is just like that of the class to its determining function. We put
>
> *21·01. \(f\{\hat{x}\hat{y}\psi(x,y)\} .=: (\exists \phi):{\phi}!(x,y).\equiv_{x,y}.\psi(x,y): f\{{\phi}!(\hat{u}, \hat{v})\} \quad \text{Df}\)
>
> Here "\(\hat{x}\hat{y}\psi(x, y)\)" has no meaning in isolation, but only in certain of its uses. In *21·01 the *alphabetical* order of \(u\) and \(v\) corresponds to the *typographical* order of \(\hat{x}\) and \(\hat{y}\) in \(f\{\hat{x}\hat{y}\psi(x,y)\}\), so that \[ f\{\hat{y}\hat{x}\psi(x,y)\} .=: (\exists \phi):{\phi}!(x,y).\equiv_{x,y}.\psi(x,y):f\{{\phi}!(\hat{v}, \hat{u})\} \quad \text{Df} \] This is important in relation to the substitution-convention below.
>
> …

**Lean reading.** Relations in extension are read as terms `fun x y => ψ x y : α → β → Prop` (Basic
§6; `x̂ŷψ(x,y)` is written with the λ so that the formula keeps its shape), `xRy` is `R x y`, a
capital apparent variable is `R : α → β → Prop` (heterogeneous), and a function of relations is
`f : (α → β → Prop) → Prop`. PM's alphabetical/typographical convention for `x̂ŷ` is Lean's argument
order of the λ. The contextual Dfs ✱21·01, ✱21·08, ✱21·082 become theorems; ✱21·07, ✱21·071 hold by
`Iff.rfl` (η). Extensionality ✱21·15/✱21·43 is `rel_eq_iff` (`funext`, `propext`). As in ✱20, the
analogues of reducibility are proved with `g := f`, descriptions of relations are `TheIs` at type
`α → β → Prop`, and the meta-level ✱21·62, ✱21·631, ✱21·632, ✱21·633 are recorded as rules or typing
remarks. The e-text's ✱21·111 lacks the circumflexes of `g{φ!(x̂,ŷ)}`; as in ✱20·111, its functions
of functions `f g : (α → β → Prop) → Prop` are applied to a relation through the definiens ✱21·01.
✱21·702 is stated as printed (`g!(R, x)`).

**Status.** proved (all propositions; ✱21·01, ✱21·08, ✱21·082 proved (reading) (contextual Dfs);
✱21·111 (e-text misprint), ✱21·112, ✱21·62, ✱21·633, ✱21·7, ✱21·701–✱21·705 proved (reading);
✱21·631, ✱21·632 remark; the other Dfs definition)
-/

/-- ✱21·01 (Df). \(f\{\hat{x}\hat{y}\psi(x,y)\}.=:(\exists \phi):\phi!(x,y).\equiv_{x,y}.\psi(x,y):f\{\phi!(\hat{u},\hat{v})\} \quad\text{Df}\)

**Status.** proved (reading): PM's contextual definition of relations in extension; relations are
read as terms `fun x y => ψ x y : α → β → Prop` (Basic §6), so the definition becomes the theorem
that `f{x̂ŷψ(x,y)}` agrees with its definiens. -/
theorem pm21_01 {ψ : α → β → Prop} {f : (α → β → Prop) → Prop} :
    f (fun x y => ψ x y) ↔
      ∃ φ : α → β → Prop, (∀ x y, φ x y ↔ ψ x y) ∧ f (fun u v => φ u v) := by
  constructor
  · exact fun h => ⟨ψ, fun _ _ => Iff.rfl, h⟩
  · rintro ⟨φ, hφ, hf⟩
    rwa [rel_eq_iff.2 hφ] at hf

/-- ✱21·02 (Df). \(a\{\phi!(\hat{x},\hat{y})\}b.=.\phi!(a,b) \quad\text{Df}\) -/
theorem pm21_02 {φ : α → β → Prop} {a : α} {b : β} : (fun x y => φ x y) a b ↔ φ a b := Iff.rfl

/-- ✱21·03 (Df). \(\text{Rel}=\hat{R}\{(\exists \phi).R=\hat{x}\hat{y}\phi!(x,y)\} \quad\text{Df}\) -/
theorem pm21_03 :
    (Rel : Set (α → β → Prop)) = {R | ∃ φ : α → β → Prop, R = fun x y => φ x y} := rfl

/-- ✱21·07 (Df). (\(R).fR.=.(\phi).f\{\hat{x}\hat{y}\phi!(x,y)\} \quad\text{Df}\) -/
theorem pm21_07 {f : (α → β → Prop) → Prop} :
    (∀ R : α → β → Prop, f R) ↔ ∀ φ : α → β → Prop, f (fun x y => φ x y) := Iff.rfl

/-- ✱21·071 (Df). (\(\exists R).fR.=.(\exists \phi).f\{\hat{x}\hat{y}\phi!(x,y)\} \quad\text{Df}\) -/
theorem pm21_071 {f : (α → β → Prop) → Prop} :
    (∃ R : α → β → Prop, f R) ↔ ∃ φ : α → β → Prop, f (fun x y => φ x y) := Iff.rfl

/-- ✱21·072 (Df). \([({℩}R)(\phi R)].f({℩}R)(\phi R).=:(\exists S):\phi R.\equiv_{R}.R=S:fS \quad\text{Df}\) -/
theorem pm21_072 {φ f : (α → β → Prop) → Prop} :
    TheIs φ f ↔ ∃ S, (∀ R, φ R ↔ R = S) ∧ f S := Iff.rfl

/-- ✱21·08 (Df). \(f\{\hat{R}\hat{S}\psi(R,S)\}.=:(\exists \phi):\psi(R,S).\equiv_{R,S}.\phi!(R,S):f\{\phi!(\hat{R},\hat{S})\} \quad\text{Df}\)

**Status.** proved (reading): relations between relations are read as terms of type
`(α → β → Prop) → (γ → δ → Prop) → Prop`, so the contextual definition becomes a theorem, as ✱21·01. -/
theorem pm21_08 {ψ : (α → β → Prop) → (γ → δ → Prop) → Prop}
    {f : ((α → β → Prop) → (γ → δ → Prop) → Prop) → Prop} :
    f (fun R S => ψ R S) ↔ ∃ φ : (α → β → Prop) → (γ → δ → Prop) → Prop,
      (∀ R S, ψ R S ↔ φ R S) ∧ f (fun R S => φ R S) := by
  constructor
  · exact fun h => ⟨ψ, fun _ _ => Iff.rfl, h⟩
  · rintro ⟨φ, hφ, hf⟩
    rwa [← rel_eq_iff.2 hφ] at hf

/-- ✱21·081 (Df). \(P\{\phi!(\hat{R},\hat{S})\}Q.=.\phi!(P,Q) \quad\text{Df}\) -/
theorem pm21_081 {φ : (α → β → Prop) → (γ → δ → Prop) → Prop} {P : α → β → Prop}
    {Q : γ → δ → Prop} : (fun R S => φ R S) P Q ↔ φ P Q := Iff.rfl

/-- ✱21·082 (Df). \(f\{\hat{R}(\psi R)\}.=:(\exists \phi):\psi R.\equiv_{R}.\phi!R:f(\phi!\hat{R}) \quad\text{Df}\)

**Status.** proved (reading): classes of relations are read as terms of `Set (α → β → Prop)`, so the
contextual definition becomes a theorem, as ✱20·08. -/
theorem pm21_082 {ψ : (α → β → Prop) → Prop} {f : Set (α → β → Prop) → Prop} :
    f {R | ψ R} ↔ ∃ φ : (α → β → Prop) → Prop, (∀ R, ψ R ↔ φ R) ∧ f {R | φ R} := by
  constructor
  · exact fun h => ⟨ψ, fun _ => Iff.rfl, h⟩
  · rintro ⟨φ, hφ, hf⟩
    rwa [← setOf_eq_setOf_iff.2 hφ] at hf

/-- ✱21·083 (Df). \(R\in \phi!\hat{R}.=.\phi!R \quad\text{Df}\) -/
theorem pm21_083 {φ : (α → β → Prop) → Prop} {R : α → β → Prop} :
    R ∈ {S : α → β → Prop | φ S} ↔ φ R := Iff.rfl

/-- ✱21·1. \[\begin{align}&\vdash\colon\ldotp f\{\hat{x}\hat{y}\psi(x,y)\}.\equiv:(\exists \phi):\phi!(x,y).\equiv_{x,y}.\psi(x,y):f\{\phi!(\hat{u},\hat{v})\}\\ &\quad[\text{*4·2.(*21·01)}]\end{align}\] -/
theorem pm21_1 {ψ : α → β → Prop} {f : (α → β → Prop) → Prop} :
    f (fun x y => ψ x y) ↔
      ∃ φ : α → β → Prop, (∀ x y, φ x y ↔ ψ x y) ∧ f (fun u v => φ u v) :=
  pm21_01

/-- ✱21·11. \[\begin{align}&\vdash\colon\ldotp\psi(x,y).\equiv_{x,y}.\chi(x,y):\supset:f\{\hat{x}\hat{y}\psi(x,y)\}.\equiv.f\{\hat{x}\hat{y}\chi(x,y)\}\\ &\quad[\text{*4·86·36.*10·281.*21·1}]\end{align}\] -/
theorem pm21_11 {ψ χ : α → β → Prop} {f : (α → β → Prop) → Prop} :
    (∀ x y, ψ x y ↔ χ x y) → (f (fun x y => ψ x y) ↔ f (fun x y => χ x y)) :=
  fun h => by rw [rel_eq_iff.2 h]

/-- ✱21·111. \[\begin{align}&\vdash\colon\ldotp f\{\phi!(\hat{x},\hat{y})\}.\equiv_{\phi}.g\{\phi!(x,y)\}:\supset:f\{\hat{x}\hat{y}\phi!(x,y)\}.\equiv_{\phi}.g\{\hat{x}\hat{y}\phi!(x,y)\}\\ &\quad[\text{Fact.*11·11·3.*10·281.*21·1}]\end{align}\]

**Status.** proved (reading): the e-text prints `g{φ!(x,y)}` in the hypothesis without circumflexes;
only `g{φ!(x̂,ŷ)}` is significant (`g` is a function of the function `φ!(x̂,ŷ)`, as `f` is, and as
in ✱20·111), so it is read so. As in ✱20·111, `f{φ!(x̂,ŷ)}` and `g{φ!(x̂,ŷ)}` are functions of the
(predicative) function `φ`, `f g : (α → β → Prop) → Prop` applied to `φ`, and `f{x̂ŷφ!(x,y)}` is
written out by its definiens ✱21·01, `(∃ψ) : ψ!(x,y) . ≡_{x,y} . φ!(x,y) : f{ψ!(û,v̂)}`, which is
how PM eliminates it (the proof cites ✱21·1). (Reading it as `f (fun x y => φ x y)` would make the
conclusion the hypothesis itself, since in Lean that term is `φ`.) -/
theorem pm21_111 {f g : (α → β → Prop) → Prop} :
    (∀ φ : α → β → Prop, f φ ↔ g φ) → ∀ φ : α → β → Prop,
      (∃ ψ : α → β → Prop, (∀ x y, ψ x y ↔ φ x y) ∧ f (fun u v => ψ u v)) ↔
        (∃ ψ : α → β → Prop, (∀ x y, ψ x y ↔ φ x y) ∧ g (fun u v => ψ u v)) :=
  fun h _ => ⟨fun ⟨ψ, hψ, hf⟩ => ⟨ψ, hψ, (h ψ).1 hf⟩, fun ⟨ψ, hψ, hg⟩ => ⟨ψ, hψ, (h ψ).2 hg⟩⟩

/-- ✱21·112. \(\vdash\colon\ldotp(\exists g)\colon\ldotp f\{\hat{x}\hat{y}\phi!(x,y)\}.\equiv_{\phi}.g!\{\hat{x}\hat{y}\phi!(x,y)\} \quad[\text{*12·1.*21·111}]\)

**Status.** proved (reading): the axiom of reducibility for relations as arguments; every Lean
function is predicative (Basic §4), so `g := f`. -/
theorem pm21_112 {f : (α → β → Prop) → Prop} :
    ∃ g : (α → β → Prop) → Prop, ∀ φ : α → β → Prop,
      f (fun x y => φ x y) ↔ g (fun x y => φ x y) :=
  ⟨f, fun _ => Iff.rfl⟩

/-- ✱21·12. \[\begin{align}&\vdash\colon\ldotp (\exists \phi)\colon\ldotp \phi!(x,y).\equiv_{x,y}.\psi(x,y):f\{\hat{x}\hat{y}\psi(x,y)\}.\equiv.f\{\hat{x}\hat{y}\phi!(x,y)\}\\ &\quad[\text{*21·11.*12·11}]\end{align}\] -/
theorem pm21_12 {ψ : α → β → Prop} {f : (α → β → Prop) → Prop} :
    ∃ φ : α → β → Prop, (∀ x y, φ x y ↔ ψ x y) ∧
      (f (fun x y => ψ x y) ↔ f (fun x y => φ x y)) :=
  ⟨ψ, fun _ _ => Iff.rfl, Iff.rfl⟩

/-- ✱21·13. \[\begin{align}&\vdash\colon\ldotp \psi(x,y).\equiv_{x,y}.\chi(x,y):\supset.\hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\chi(x,y)\\ &\quad[\text{*21·1.*12·11.*13·195}]\end{align}\] -/
theorem pm21_13 {ψ χ : α → β → Prop} :
    (∀ x y, ψ x y ↔ χ x y) → (fun x y => ψ x y) = (fun x y => χ x y) :=
  fun h => rel_eq_iff.2 h

/-- ✱21·14. \[\begin{align}&\vdash\colon\ldotp \hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\chi(x,y).\supset:\psi(x,y).\equiv_{x,y}.\chi(x,y)\\ &\quad[\text{Proof as in *20·14}]\end{align}\] -/
theorem pm21_14 {ψ χ : α → β → Prop} :
    (fun x y => ψ x y) = (fun x y => χ x y) → ∀ x y, ψ x y ↔ χ x y :=
  fun h => rel_eq_iff.1 h

/-- ✱21·15. \(\vdash\colon\ldotp \psi(x,y).\equiv_{x,y}.\chi(x,y):\equiv.\hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\chi(x,y) \quad[\text{*21·13·14}]\) -/
theorem pm21_15 {ψ χ : α → β → Prop} :
    (∀ x y, ψ x y ↔ χ x y) ↔ (fun x y => ψ x y) = (fun x y => χ x y) :=
  ⟨pm21_13, pm21_14⟩

/-- ✱21·151. \(\vdash.(\exists \phi).\hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\phi!(x,y) \quad[\text{*21·15.*12·11}]\) -/
theorem pm21_151 {ψ : α → β → Prop} :
    ∃ φ : α → β → Prop, (fun x y => ψ x y) = (fun x y => φ x y) :=
  ⟨ψ, rfl⟩

/-- ✱21·16. \(\vdash:(\exists \phi):f\{\hat{x}\hat{y}\psi(x,y)\}.\equiv.f\{\hat{x}\hat{y}\phi!(x,y)\} \quad[\text{*21·12}]\) -/
theorem pm21_16 {ψ : α → β → Prop} {f : (α → β → Prop) → Prop} :
    ∃ φ : α → β → Prop, f (fun x y => ψ x y) ↔ f (fun x y => φ x y) :=
  ⟨ψ, Iff.rfl⟩

/-- ✱21·17. \(\vdash:(\phi).f\{\hat{x}\hat{y}\phi!(x,y)\}.\supset.f\{\hat{x}\hat{y}\psi(x,y)\} \quad[\text{*21·16.*10·1}]\) -/
theorem pm21_17 {ψ : α → β → Prop} {f : (α → β → Prop) → Prop} :
    (∀ φ : α → β → Prop, f (fun x y => φ x y)) → f (fun x y => ψ x y) :=
  fun h => h ψ

/-- ✱21·18. \[\begin{align}\vdash\colon\ldotp \hat{x}\hat{y}\phi(x,y)=\hat{x}\hat{y}\psi(x,y).\supset:f\{\hat{x}\hat{y}\phi(x,y)\}.&\equiv.f\{\hat{x}\hat{y}\psi(x,y)\}\\ &\quad[\text{*21·11·15}]\end{align}\] -/
theorem pm21_18 {φ ψ : α → β → Prop} {f : (α → β → Prop) → Prop} :
    (fun x y => φ x y) = (fun x y => ψ x y) →
      (f (fun x y => φ x y) ↔ f (fun x y => ψ x y)) :=
  fun h => h ▸ Iff.rfl

/-- ✱21·19. \[\begin{align}&\vdash\colon\ldotp \hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\chi(x,y).\equiv:(f):f!\hat{x}\hat{y}\psi(x,y).\supset.f!\hat{x}\hat{y}\chi(x,y)\\ &\quad[\text{*21·18.*10·11·21.*21·1.*10·35.(*13·01).*21·112.*10·301}]\end{align}\] -/
theorem pm21_19 {ψ χ : α → β → Prop} :
    (fun x y => ψ x y) = (fun x y => χ x y) ↔
      ∀ f : (α → β → Prop) → Prop, f (fun x y => ψ x y) → f (fun x y => χ x y) :=
  ⟨fun h _ hf => h ▸ hf, fun h => h (fun R => (fun x y => ψ x y) = R) rfl⟩

/-- ✱21·191. \[\begin{align}\vdash\colon\ldotp \hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\chi(x,y).&\equiv:(f):f!\hat{x}\hat{y}\psi(x,y).\equiv.f!\hat{x}\hat{y}\chi(x,y)\\ &\quad[\text{*21·18·19}]\end{align}\] -/
theorem pm21_191 {ψ χ : α → β → Prop} :
    (fun x y => ψ x y) = (fun x y => χ x y) ↔
      ∀ f : (α → β → Prop) → Prop, f (fun x y => ψ x y) ↔ f (fun x y => χ x y) :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => (h (fun R => (fun x y => ψ x y) = R)).1 rfl⟩

/-- ✱21·2. \(\vdash.\hat{x}\hat{y}\phi(x,y)=\hat{x}\hat{y}\phi(x,y) \quad[\text{*21·15.*4·2}]\) -/
theorem pm21_2 {φ : α → β → Prop} : (fun x y => φ x y) = (fun x y => φ x y) := rfl

/-- ✱21·21. \(\vdash:\hat{x}\hat{y}\phi(x,y)=\hat{x}\hat{y}\psi(x,y).\equiv.\hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\phi(x,y) \quad[\text{*21·15.*10·32}]\) -/
theorem pm21_21 {φ ψ : α → β → Prop} :
    (fun x y => φ x y) = (fun x y => ψ x y) ↔ (fun x y => ψ x y) = (fun x y => φ x y) :=
  eq_comm

/-- ✱21·22. \[\begin{align}\vdash:\hat{x}\hat{y}\phi(x,y)=\hat{x}\hat{y}\psi(x,y).&\hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\chi(x,y).\supset.\\ &\hat{x}\hat{y}\phi(x,y)=\hat{x}\hat{y}\chi(x,y) \quad[\text{*21·15.*10·301}]\end{align}\] -/
theorem pm21_22 {φ ψ χ : α → β → Prop} :
    (fun x y => φ x y) = (fun x y => ψ x y) ∧ (fun x y => ψ x y) = (fun x y => χ x y) →
      (fun x y => φ x y) = (fun x y => χ x y) :=
  fun ⟨h1, h2⟩ => h1.trans h2

/-- ✱21·23. \[\begin{align}\vdash:\hat{x}\hat{y}\phi(x,y)=\hat{x}\hat{y}\psi(x,y).&\hat{x}\hat{y}\phi(x,y)=\hat{x}\hat{y}\chi(x,y).\supset.\\ &\hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\chi(x,y) \quad[\text{*21·21·22}]\end{align}\] -/
theorem pm21_23 {φ ψ χ : α → β → Prop} :
    (fun x y => φ x y) = (fun x y => ψ x y) ∧ (fun x y => φ x y) = (fun x y => χ x y) →
      (fun x y => ψ x y) = (fun x y => χ x y) :=
  fun ⟨h1, h2⟩ => h1.symm.trans h2

/-- ✱21·24. \[\begin{align}\vdash:\hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\phi(x,y).&\hat{x}\hat{y}\chi(x,y)=\hat{x}\hat{y}\phi(x,y).\supset.\\ &\hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\chi(x,y) \quad[\text{*21·21·22}]\end{align}\] -/
theorem pm21_24 {φ ψ χ : α → β → Prop} :
    (fun x y => ψ x y) = (fun x y => φ x y) ∧ (fun x y => χ x y) = (fun x y => φ x y) →
      (fun x y => ψ x y) = (fun x y => χ x y) :=
  fun ⟨h1, h2⟩ => h1.trans h2.symm

/-- ✱21·3. \(\vdash:x{\hat{x}\hat{y}\psi(x,y)}y.\equiv.\psi(x,y) \quad[\text{*21·1·02.*10·43·35.*12·11}]\) -/
theorem pm21_3 {ψ : α → β → Prop} {x : α} {y : β} : (fun x y => ψ x y) x y ↔ ψ x y := Iff.rfl

/-- ✱21·31. \[\begin{align}\vdash\colon\ldotp \hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\chi(x, y).\equiv:x\{\hat{x}\hat{y}\psi(x,y)\}y.&\equiv_{x,y}.x\{\hat{x}\hat{y}\chi(x, y)\}y\\ &\quad[\text{*21·15·3}]\end{align}\] -/
theorem pm21_31 {ψ χ : α → β → Prop} :
    (fun x y => ψ x y) = (fun x y => χ x y) ↔
      ∀ x y, (fun x y => ψ x y) x y ↔ (fun x y => χ x y) x y :=
  rel_eq_iff

/-- ✱21·32. \(\vdash.\hat{x}\hat{y}[x\{\hat{x}\hat{y}\phi(x,y)\}y]=\hat{x}\hat{y}\phi(x,y) \quad[\text{*21·3·15}]\) -/
theorem pm21_32 {φ : α → β → Prop} :
    (fun x y => (fun x y => φ x y) x y) = (fun x y => φ x y) := rfl

/-- ✱21·33. \(\vdash\colon\ldotp R=\hat{x}\hat{y}\phi(x, y).\equiv:xRy.\equiv_{x, y}.\phi(x, y) \quad[\text{*21·31·3}]\) -/
theorem pm21_33 {R φ : α → β → Prop} : R = (fun x y => φ x y) ↔ ∀ x y, R x y ↔ φ x y :=
  rel_eq_iff

/-- ✱21·4. \(\vdash:R\in \text{Rel}.\equiv.(\exists \phi).R=\hat{x}\hat{y}\phi!(x,y) \quad[\text{*20·3.(*21·03)}]\) -/
theorem pm21_4 {R : α → β → Prop} : R ∈ Rel ↔ ∃ φ : α → β → Prop, R = fun x y => φ x y :=
  Iff.rfl

/-- ✱21·41. \(\vdash.\hat{x}\hat{y}\phi(x, y)\in \text{Rel} \quad[\text{*21·4·151}]\) -/
theorem pm21_41 {φ : α → β → Prop} : (fun x y => φ x y) ∈ (Rel : Set (α → β → Prop)) :=
  ⟨φ, rfl⟩

/-- ✱21·42. \(\vdash.\hat{x}\hat{y}(xRy)=R \quad[\text{*21·3·15}]\) -/
theorem pm21_42 {R : α → β → Prop} : (fun x y => R x y) = R := rfl

/-- ✱21·43. \(\vdash\colon\ldotp R=S.\equiv:xRy.\equiv_{x,y}.xSy \quad[\text{*21·15·3}]\) -/
theorem pm21_43 {R S : α → β → Prop} : R = S ↔ ∀ x y, R x y ↔ S x y := rel_eq_iff

/-- ✱21·53. \(\vdash\colon\ldotp S=R.\supset_{S}.\phi S:\equiv.\phi R \quad[\text{*10·1.*21·2·18·21.Comm.*10·11·21}]\) -/
theorem pm21_53 {φ : (α → β → Prop) → Prop} {R : α → β → Prop} :
    (∀ S : α → β → Prop, S = R → φ S) ↔ φ R :=
  ⟨fun h => h R rfl, fun h _ hS => hS ▸ h⟩

/-- ✱21·54. \(\vdash\colon\ldotp (\exists S).S=R.\phi S.\equiv.\phi R \quad[\text{*21·18.*10·11·23.*21·2.*10·24}]\) -/
theorem pm21_54 {φ : (α → β → Prop) → Prop} {R : α → β → Prop} :
    (∃ S : α → β → Prop, S = R ∧ φ S) ↔ φ R :=
  ⟨fun ⟨_, hS, h⟩ => hS ▸ h, fun h => ⟨R, rfl, h⟩⟩

/-- ✱21·55. \(\vdash.\hat{x}\hat{y}\phi(x,y)=(℩R)\{xRy.\equiv_{x, y}.\phi(x,y)\} \quad[\text{*21·33·54.*14·1}]\) -/
theorem pm21_55 {φ : α → β → Prop} :
    TheIs (fun R : α → β → Prop => ∀ x y, R x y ↔ φ x y) (fun S => (fun x y => φ x y) = S) :=
  ⟨fun x y => φ x y, fun _ => pm21_33.symm, rfl⟩

/-- ✱21·56. \(\vdash.\text{E}!(℩R)\{xRy.\equiv_{x,y}.\phi(x,y)\} \quad[\text{*21·55.*14·21}]\) -/
theorem pm21_56 {φ : α → β → Prop} : EBang (fun R : α → β → Prop => ∀ x y, R x y ↔ φ x y) :=
  ⟨fun x y => φ x y, fun _ => pm21_33.symm⟩

/-- ✱21·57. \[\begin{align}\vdash\colon\ldotp \hat{x}\hat{y}\phi(x,y)=(℩R)(fR).\supset:g\{\hat{x}\hat{y}\phi(x,y)\}.&\equiv.g\{(℩R)(fR)\}\\ &\quad[\text{*14·1.*21·54.*13·183}]\end{align}\] -/
theorem pm21_57 {φ : α → β → Prop} {f g : (α → β → Prop) → Prop} :
    TheIs f (fun S => (fun x y => φ x y) = S) → (g (fun x y => φ x y) ↔ TheIs f g) := by
  rintro ⟨S, hS, rfl⟩
  exact (TheIs_iff_of_unique hS).symm

/-- ✱21·58. \(\vdash.\hat{x}\hat{y}\phi(x,y)=({℩}R)\{R=\hat{x}\hat{y}\phi(x,y)\} \quad[\text{*4·2.*10·11.*21·54.*14·1}]\) -/
theorem pm21_58 {φ : α → β → Prop} :
    TheIs (fun R : α → β → Prop => R = fun x y => φ x y) (fun S => (fun x y => φ x y) = S) :=
  ⟨fun x y => φ x y, fun _ => Iff.rfl, rfl⟩

/-- ✱21·6. \(\vdash:(\exists R).fR.\equiv.{\sim}\{(R).{\sim}fR\} \quad[\text{Proof as in *20·6}]\) -/
theorem pm21_6 {f : (α → β → Prop) → Prop} :
    (∃ R : α → β → Prop, f R) ↔ ¬ ∀ R : α → β → Prop, ¬ f R :=
  not_forall_not.symm

/-- ✱21·61. \(\vdash:(R).fR.\supset.fS \quad[\text{Proof as in *20·61}]\) -/
theorem pm21_61 {f : (α → β → Prop) → Prop} {S : α → β → Prop} :
    (∀ R : α → β → Prop, f R) → f S :=
  fun h => h S

/-- ✱21·62. When \(fR\) is true, whatever possible argument of the form \(\hat{x}\hat{y}\phi!(x,y)\) \(R\) may be, (\(R).fR\) is true. [Proof as in *20·62]

**Status.** proved (reading): a rule of inference, the analogue of ✱10·11 for relations, as ✱20·62:
from `∀ φ, f (fun x y => φ x y)` the declaration derives `(R).fR`. -/
theorem pm21_62 {f : (α → β → Prop) → Prop} (h : ∀ φ : α → β → Prop, f (fun x y => φ x y)) :
    ∀ R : α → β → Prop, f R :=
  fun R => h R

/-- ✱21·63. \(\vdash\colon\ldotp (R).p\lor fR.\supset:p.\lor.(R).fR \quad[\text{Proof as in *20·63}]\) -/
theorem pm21_63 {p : Prop} {f : (α → β → Prop) → Prop} :
    (∀ R : α → β → Prop, p ∨ f R) → p ∨ ∀ R : α → β → Prop, f R :=
  fun h => (Classical.em p).elim Or.inl fun hp => Or.inr fun R => (h R).resolve_left hp

/-- ✱21·631. If "\(fR\)" is significant, then if \(S\) is of the same type as \(R\), "\(fS\)" is significant, and vice versa.

**Status.** remark: as ✱20·631, about significance (meta-level); a function of relations is
`f : (α → β → Prop) → Prop` and applies to every relation `S` of the type of `R`. -/
def pm21_631 (f : (α → β → Prop) → Prop) (_R S : α → β → Prop) : Prop := f S

/-- ✱21·632. If, for some \(R\), there is a proposition \(fR\), then there is a function \(f\hat{R}\), and vice versa.

**Status.** remark: as ✱20·632 (meta-level): a proposition `fR` gives the function `fR̂`, here
`fun R => f R`. -/
def pm21_632 (f : (α → β → Prop) → Prop) : (α → β → Prop) → Prop := fun R => f R

/-- ✱21·633. "Whatever possible relation \(R\) may be, \(f(R,S)\) is true whatever possible relation \(S\) may be" implies "whatever possible relation \(S\) may be, \(f(R,S)\) is true whatever possible relation \(R\) may be."

**Status.** proved (reading): as ✱20·633, the interchange of apparent variables (meta-level),
recorded by its Lean counterpart; the relations may be of different types. -/
theorem pm21_633 {f : (α → β → Prop) → (γ → δ → Prop) → Prop} :
    (∀ R : α → β → Prop, ∀ S : γ → δ → Prop, f R S) →
      ∀ S : γ → δ → Prop, ∀ R : α → β → Prop, f R S :=
  fun h S R => h R S

/-- ✱21·64. \(\vdash\colon\ldotp (R).fR:(R).gR:\supset.fS.gS \quad[\text{Proof as in *20·64}]\) -/
theorem pm21_64 {f g : (α → β → Prop) → Prop} {S : α → β → Prop} :
    (∀ R : α → β → Prop, f R) ∧ (∀ R : α → β → Prop, g R) → f S ∧ g S :=
  fun ⟨hf, hg⟩ => ⟨hf S, hg S⟩

/-- ✱21·7. \(\vdash:(\exists g):fR.\equiv_{R}.g!R \quad[\text{Proof as in *20·7}]\)

**Status.** proved (reading): the analogue of the axiom of reducibility for relations; every Lean
function is predicative (Basic §4), so `g := f`. -/
theorem pm21_7 {f : (α → β → Prop) → Prop} :
    ∃ g : (α → β → Prop) → Prop, ∀ R : α → β → Prop, f R ↔ g R :=
  ⟨f, fun _ => Iff.rfl⟩

/-- ✱21·701. \(\vdash:(\exists g):f(R, x).\equiv_{R,x}.g!(R, x) \quad[\text{Proof as in *20·701}]\)

**Status.** proved (reading): the analogue of the axiom of reducibility for relations; every Lean
function is predicative (Basic §4), so `g := f`. -/
theorem pm21_701 {f : (α → β → Prop) → γ → Prop} :
    ∃ g : (α → β → Prop) → γ → Prop, ∀ (R : α → β → Prop) (x : γ), f R x ↔ g R x :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- ✱21·702. \(\vdash:(\exists g):f(x, R).\equiv_{R,x}.g!(R, x) \quad[\text{Proof as in *20·702}]\)

**Status.** proved (reading): the analogue of the axiom of reducibility for relations; every Lean
function is predicative (Basic §4), so `g := f`. Stated as printed, with the arguments of `g!(R, x)`
in the order `(R, x)` (unlike ✱20·702, where `g!` takes them in the order of `f`); so
`g := fun R x => f x R`. -/
theorem pm21_702 {f : γ → (α → β → Prop) → Prop} :
    ∃ g : (α → β → Prop) → γ → Prop, ∀ (R : α → β → Prop) (x : γ), f x R ↔ g R x :=
  ⟨fun R x => f x R, fun _ _ => Iff.rfl⟩

/-- ✱21·703. \(\vdash:(\exists g):f(R, S).\equiv_{R,S}.g!(R, S) \quad[\text{Proof as in *20·703}]\)

**Status.** proved (reading): the analogue of the axiom of reducibility for relations; every Lean
function is predicative (Basic §4), so `g := f`. -/
theorem pm21_703 {f : (α → β → Prop) → (γ → δ → Prop) → Prop} :
    ∃ g : (α → β → Prop) → (γ → δ → Prop) → Prop,
      ∀ (R : α → β → Prop) (S : γ → δ → Prop), f R S ↔ g R S :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- ✱21·704. \(\vdash:(\exists g):f(R, \alpha).\equiv_{R,\alpha}.g!(R, \alpha) \quad[\text{Proof as in *20·703}]\)

**Status.** proved (reading): the analogue of the axiom of reducibility for relations; every Lean
function is predicative (Basic §4), so `g := f`. -/
theorem pm21_704 {f : (α → β → Prop) → Set γ → Prop} :
    ∃ g : (α → β → Prop) → Set γ → Prop, ∀ (R : α → β → Prop) (A : Set γ), f R A ↔ g R A :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- ✱21·705. \(\vdash:(\exists g):f(\alpha, R).\equiv_{\alpha,R}.g!(\alpha, R) \quad[\text{Proof as in *20·703}]\)

**Status.** proved (reading): the analogue of the axiom of reducibility for relations; every Lean
function is predicative (Basic §4), so `g := f`. -/
theorem pm21_705 {f : Set γ → (α → β → Prop) → Prop} :
    ∃ g : Set γ → (α → β → Prop) → Prop, ∀ (A : Set γ) (R : α → β → Prop), f A R ↔ g A R :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- ✱21·71. \(\vdash\colon\ldotp R=S.\equiv:g!R.\supset_{g}.g!S \quad[\text{Proof as in *20·71}]\) -/
theorem pm21_71 {R S : α → β → Prop} : R = S ↔ ∀ g : (α → β → Prop) → Prop, g R → g S :=
  ⟨fun h _ hg => h ▸ hg, fun h => h (fun T => R = T) rfl⟩

/-!
## [✱22] Calculus of classes

*(Vol. 1, p. 217)*

> *Summary of* *22.
>
> In this number we reach what was historically the starting-point of symbolic logic. The Greek letters used (except \(\phi\), \(\psi\), \(\chi\), \(\theta\)) are always to stand for expressions of the form \(\hat{x}({\phi}!x)\), or, where the Greek letters are not apparent variables, \(\hat{x}({\phi}x)\). The small Latin letters may either be such as have a meaning in isolation, or may represent classes or relations; this is possible in virtue of the notes at the ends of *20 and *21. We put:
>
> *22·01. \(\alpha \subset \beta .=: x \in \alpha .\supset_{x}. x \in \beta \quad \text{Df}\)
>
> This defines "the class \(\alpha\) is contained in the class \(\beta\)," or "all \(\alpha\)'s are \(\beta\)'s."
>
> *22·02. \(\alpha \cap \beta = \hat{x}(x \in \alpha . x \in \beta) \quad \text{Df}\)
>
> This defines the logical product or common part of two classes \(\alpha\) and \(\beta\).
>
> *22·03. \(\alpha \cup \beta = \hat{x}(x \in \alpha .\lor. x \in \beta) \quad \text{Df}\)
>
> This defines the logical sum of two classes; it is the class consisting of all the members of one together with all the members of the other.
>
> *22·04. \(-\alpha = \hat{x}(x {\sim}{\in} \alpha) \quad \text{Df}\)
>
> …

**Lean reading.** The calculus of classes is mathlib's Boolean algebra of `Set α`: PM's `α ⊂ β` is
`A ⊆ B` (inclusion, never Lean's strict `⊂`), `∩`, `∪` are `∩`, `∪`, `−α` is `Aᶜ` and `α − β` is
`A \ B`, all with the defining equations of ✱22·01–✱22·05 holding by `rfl`; the bracketing Dfs
✱22·53, ✱22·71 hold because `∩`, `∪` are left-associative. Hypotheses that are products are
conjunctions (`A ⊆ B ∧ B ⊆ C → A ⊆ C`), and apparent class variables (✱22·6, ✱22·94, ✱22·95) are
`∀ C : Set α`/`∃ A : Set α`. ✱22·351 (`−α ≠ α`) needs a member of the type, which PM assumes
(`[Nonempty α]`). The e-text prints `∨` for `∪` in ✱22·84 and ✱22·85.

**Status.** proved (all propositions; ✱22·351 proved (reading) (`[Nonempty α]`); ✱22·84, ✱22·85
proved (reading) (e-text prints `∨` for `∪`); the Dfs definition)
-/

/-- ✱22·01 (Df). \(\alpha \subset \beta .=: x \in \alpha .\supset_{x}. x \in \beta \quad \text{Df}\) -/
theorem pm22_01 {A B : Set α} : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := Iff.rfl

/-- ✱22·02 (Df). \(\alpha \cap \beta = \hat{x}(x \in \alpha . x \in \beta) \quad \text{Df}\) -/
theorem pm22_02 {A B : Set α} : A ∩ B = {x | x ∈ A ∧ x ∈ B} := rfl

/-- ✱22·03 (Df). \(\alpha \cup \beta = \hat{x}(x \in \alpha .\lor. x \in \beta) \quad \text{Df}\) -/
theorem pm22_03 {A B : Set α} : A ∪ B = {x | x ∈ A ∨ x ∈ B} := rfl

/-- ✱22·04 (Df). \(-\alpha = \hat{x}(x \mathop{{\sim}{\in}} \alpha) \quad \text{Df}\) -/
theorem pm22_04 {A : Set α} : Aᶜ = {x | x ∉ A} := rfl

/-- ✱22·05 (Df). \(\alpha-\beta=\alpha\cap -\beta \quad\text{Df}\) -/
theorem pm22_05 {A B : Set α} : A \ B = A ∩ Bᶜ := rfl

/-- ✱22·1. \(\vdash\colon\ldotp \alpha\subset\beta.\equiv:x\in \alpha.\supset_{x}.x\in \beta \quad[\text{*4·2.(*22·01)}]\) -/
theorem pm22_1 {A B : Set α} : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := Iff.rfl

/-- ✱22·2. \(\vdash.\alpha\cap \beta=\hat{x}(x\in \alpha.x\in \beta) \quad[\text{*20·2.(*22·02)}]\) -/
theorem pm22_2 {A B : Set α} : A ∩ B = {x | x ∈ A ∧ x ∈ B} := rfl

/-- ✱22·3. \(\vdash.\alpha\cup \beta=\hat{x}(x\in \alpha.\lor .x\in \beta) \quad[\text{*20·2.(*22·03)}]\) -/
theorem pm22_3 {A B : Set α} : A ∪ B = {x | x ∈ A ∨ x ∈ B} := rfl

/-- ✱22·31. \(\vdash.-\alpha=\hat{x}(x{\sim}\in \alpha) \quad[\text{*20·2.(*22·04)}]\) -/
theorem pm22_31 {A : Set α} : Aᶜ = {x | x ∉ A} := rfl

/-- ✱22·32. \(\vdash.\alpha-\beta=\hat{x}(x\in \alpha.x{\sim}\in \beta) \quad[\text{*20·2.(*22·05).*22·2.*20·32}]\) -/
theorem pm22_32 {A B : Set α} : A \ B = {x | x ∈ A ∧ x ∉ B} := rfl

/-- ✱22·33. \(\vdash:x\in \alpha\cap \beta.\equiv.x\in \alpha.x\in \beta \quad[\text{*20·3.*22·2}]\) -/
theorem pm22_33 {x : α} {A B : Set α} : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := Iff.rfl

/-- ✱22·34. \(\vdash\colon\ldotp x\in \alpha\cup \beta.\equiv:x\in \alpha.\lor .x\in \beta \quad[\text{*20·3.*22·3}]\) -/
theorem pm22_34 {x : α} {A B : Set α} : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := Iff.rfl

/-- ✱22·35. \(\vdash:x\in -\alpha.\equiv.x{\sim}\in \alpha \quad[\text{*20·3.*22·31}]\) -/
theorem pm22_35 {x : α} {A : Set α} : x ∈ Aᶜ ↔ x ∉ A := Iff.rfl

/-- ✱22·351. \(\vdash.-\alpha \neq \alpha\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I); PM's proof
passes from `(x) . ∼{x ∈ −α . ≡ . x ∈ α}` to `∼{(x) : x ∈ −α . ≡ . x ∈ α}` (✱10·251), which needs a
member. The hypothesis `[Nonempty α]` makes this explicit; for the empty type the statement fails
(`pm22_351_aux_empty`). -/
theorem pm22_351 [Nonempty α] {A : Set α} : Aᶜ ≠ A := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty α›
  have h1 : x ∉ A ↔ x ∈ A := Set.ext_iff.1 h x
  by_cases hx : x ∈ A
  · exact h1.2 hx hx
  · exact hx (h1.1 hx)

/-- Without a member of the type, ✱22·351 fails: every class of the empty type is its own
complement. -/
theorem pm22_351_aux_empty (A : Set Empty) : Aᶜ = A := Set.ext fun x => x.elim

/-- ✱22·36. \(\vdash.\alpha\cap \beta\in \text{Cls} \quad[\text{*20·41}]\) -/
theorem pm22_36 {A B : Set α} : A ∩ B ∈ (Cls : Set (Set α)) := ⟨fun x => x ∈ A ∩ B, rfl⟩

/-- ✱22·37. \(\vdash.\alpha\cup \beta\in \text{Cls} \quad[\text{*20·41}]\) -/
theorem pm22_37 {A B : Set α} : A ∪ B ∈ (Cls : Set (Set α)) := ⟨fun x => x ∈ A ∪ B, rfl⟩

/-- ✱22·38. \(\vdash.-\alpha\in \text{Cls} \quad[\text{*20·41}]\) -/
theorem pm22_38 {A : Set α} : Aᶜ ∈ (Cls : Set (Set α)) := ⟨fun x => x ∈ Aᶜ, rfl⟩

/-- ✱22·39. \(\vdash.\hat{z}(\phi z)\cap \hat{z}(\psi z)=\hat{z}(\phi z.\psi z)\) -/
theorem pm22_39 {φ ψ : α → Prop} : {z | φ z} ∩ {z | ψ z} = {z | φ z ∧ ψ z} := rfl

/-- ✱22·391. \(\vdash.\hat{z}(\phi z)\cup \hat{z}(\psi z)=\hat{z}(\phi z\lor \psi z) \quad[\text{Similar proof}]\) -/
theorem pm22_391 {φ ψ : α → Prop} : {z | φ z} ∪ {z | ψ z} = {z | φ z ∨ ψ z} := rfl

/-- ✱22·392. \(\vdash.-\hat{z}(\phi z)=\hat{z}({\sim}\phi z) \quad[\text{Similar proof}]\) -/
theorem pm22_392 {φ : α → Prop} : {z | φ z}ᶜ = {z | ¬φ z} := rfl

/-- ✱22·4. \(\vdash\colon\ldotp \alpha\subset\beta.\beta\subset\alpha.\equiv:x\in \alpha.\equiv_{x}.x\in \beta\) -/
theorem pm22_4 {A B : Set α} : A ⊆ B ∧ B ⊆ A ↔ ∀ x, x ∈ A ↔ x ∈ B :=
  ⟨fun ⟨h1, h2⟩ _ => ⟨fun hx => h1 hx, fun hx => h2 hx⟩,
    fun h => ⟨fun x hx => (h x).1 hx, fun x hx => (h x).2 hx⟩⟩

/-- ✱22·41. \(\vdash:\alpha\subset\beta.\beta\subset\alpha.\equiv.\alpha=\beta \quad[\text{*22·4.*20·43}]\) -/
theorem pm22_41 {A B : Set α} : A ⊆ B ∧ B ⊆ A ↔ A = B :=
  pm22_4.trans Set.ext_iff.symm

/-- ✱22·42. \(\vdash . \alpha \subset \alpha \quad[\text{Id.*10·11}]\) -/
theorem pm22_42 {A : Set α} : A ⊆ A := fun _ hx => hx

/-- ✱22·43. \(\vdash : \alpha \cap \beta \subset \alpha \quad[\text{*3·26.*10·11}]\) -/
theorem pm22_43 {A B : Set α} : A ∩ B ⊆ A := fun _ hx => hx.1

/-- ✱22·44. \(\vdash : \alpha \subset \beta . \beta \subset \gamma . \supset . \alpha \subset \gamma \quad[\text{*10·3}]\) -/
theorem pm22_44 {A B C : Set α} : A ⊆ B ∧ B ⊆ C → A ⊆ C := fun ⟨h1, h2⟩ _ hx => h2 (h1 hx)

/-- ✱22·441. \(\vdash : \alpha \subset \beta . x \in \alpha . \supset . x \in \beta \quad[\text{*10·1.Imp}]\) -/
theorem pm22_441 {A B : Set α} {x : α} : A ⊆ B ∧ x ∈ A → x ∈ B := fun ⟨h, hx⟩ => h hx

/-- ✱22·45. \(\vdash : \alpha \subset \beta . \alpha \subset \gamma . \equiv . \alpha \subset \beta \cap \gamma\) -/
theorem pm22_45 {A B C : Set α} : A ⊆ B ∧ A ⊆ C ↔ A ⊆ B ∩ C :=
  ⟨fun ⟨h1, h2⟩ _ hx => ⟨h1 hx, h2 hx⟩,
    fun h => ⟨fun _ hx => (h hx).1, fun _ hx => (h hx).2⟩⟩

/-- ✱22·46. \(\vdash : x \in \alpha . \alpha \subset \beta . \supset . x \in \beta \quad[\text{*22·441 . Perm}]\) -/
theorem pm22_46 {A B : Set α} {x : α} : x ∈ A ∧ A ⊆ B → x ∈ B := fun ⟨hx, h⟩ => h hx

/-- ✱22·47. \(\vdash : \alpha \subset \gamma . \supset . \alpha \cap \beta \subset \gamma \quad[\text{*22·43·44}]\) -/
theorem pm22_47 {A B C : Set α} : A ⊆ C → A ∩ B ⊆ C := fun h _ hx => h hx.1

/-- ✱22·48. \(\vdash : \alpha \subset \beta . \supset . \alpha \cap \gamma \subset \beta \cap \gamma \quad[\text{*10·31}]\) -/
theorem pm22_48 {A B C : Set α} : A ⊆ B → A ∩ C ⊆ B ∩ C := fun h _ hx => ⟨h hx.1, hx.2⟩

/-- ✱22·481. \(\vdash : \alpha = \beta . \supset . \alpha \cap \gamma = \beta \cap \gamma\) -/
theorem pm22_481 {A B C : Set α} : A = B → A ∩ C = B ∩ C := fun h => h ▸ rfl

/-- ✱22·49. \(\vdash : \alpha \subset \beta . \gamma \subset \delta . \supset . \alpha \cap \gamma \subset \beta \cap \delta \quad[\text{*10·39}]\) -/
theorem pm22_49 {A B C D : Set α} : A ⊆ B ∧ C ⊆ D → A ∩ C ⊆ B ∩ D :=
  fun ⟨h1, h2⟩ _ hx => ⟨h1 hx.1, h2 hx.2⟩

/-- ✱22·5. \(\vdash . \alpha \cap \alpha = \alpha\) -/
theorem pm22_5 {A : Set α} : A ∩ A = A := by
  ext x
  simp only [Set.mem_inter_iff]
  tauto

/-- ✱22·51. \(\vdash . \alpha \cap \beta = \beta \cap \alpha \quad[\text{*22·33.*4·3.*10·11.*20·43}]\) -/
theorem pm22_51 {A B : Set α} : A ∩ B = B ∩ A := by
  ext x
  simp only [Set.mem_inter_iff]
  tauto

/-- ✱22·52. \(\vdash . (\alpha \cap \beta) \cap \gamma = \alpha \cap (\beta \cap \gamma) \quad[\text{*22·33.*4·32.*10·11.*20·43}]\) -/
theorem pm22_52 {A B C : Set α} : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  simp only [Set.mem_inter_iff]
  tauto

/-- ✱22·53 (Df). \(\alpha \cap \beta \cap \gamma = (\alpha \cap \beta) \cap \gamma \quad\text{Df}\)

Lean's `∩` is left-associative, so `A ∩ B ∩ C` already is `(A ∩ B) ∩ C`. -/
theorem pm22_53 {A B C : Set α} : A ∩ B ∩ C = (A ∩ B) ∩ C := rfl

/-- ✱22·54. \(\vdash \colon\ldotp \alpha = \beta . \supset : \alpha \subset \gamma . \equiv . \beta \subset \gamma \quad[\text{*20·18}]\) -/
theorem pm22_54 {A B C : Set α} : A = B → (A ⊆ C ↔ B ⊆ C) := fun h => h ▸ Iff.rfl

/-- ✱22·55. \(\vdash \colon\ldotp \alpha = \beta . \supset : \gamma \subset \alpha . \equiv . \gamma \subset \beta \quad[\text{*20·18}]\) -/
theorem pm22_55 {A B C : Set α} : A = B → (C ⊆ A ↔ C ⊆ B) := fun h => h ▸ Iff.rfl

/-- ✱22·551. \(\vdash : \alpha = \beta . \supset . \alpha \cup \gamma = \beta \cup \gamma \quad[\text{*10·411}]\) -/
theorem pm22_551 {A B C : Set α} : A = B → A ∪ C = B ∪ C := fun h => h ▸ rfl

/-- ✱22·56. \(\vdash . \alpha \cup \alpha = \alpha \quad[\text{*4·25.*10·11}]\) -/
theorem pm22_56 {A : Set α} : A ∪ A = A := by
  ext x
  simp only [Set.mem_union]
  tauto

/-- ✱22·57. \(\vdash.\alpha\cup\beta=\beta\cup\alpha \quad[\text{*4·31.*10·11}]\) -/
theorem pm22_57 {A B : Set α} : A ∪ B = B ∪ A := by
  ext x
  simp only [Set.mem_union]
  tauto

/-- ✱22·58. \(\vdash.\alpha\subset\alpha\cup\beta.\beta\subset\alpha\cup\beta \quad[\text{*1·3.*2·2}]\) -/
theorem pm22_58 {A B : Set α} : A ⊆ A ∪ B ∧ B ⊆ A ∪ B :=
  ⟨fun _ hx => Or.inl hx, fun _ hx => Or.inr hx⟩

/-- ✱22·59. \(\vdash:\alpha\subset\gamma.\beta\subset\gamma.\equiv.\alpha\cup\beta\subset\gamma\) -/
theorem pm22_59 {A B C : Set α} : A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C :=
  ⟨fun ⟨h1, h2⟩ _ hx => hx.elim (fun h => h1 h) (fun h => h2 h),
    fun h => ⟨fun _ hx => h (Or.inl hx), fun _ hx => h (Or.inr hx)⟩⟩

/-- ✱22·6. \(\vdash\colon\ldotp x\in\alpha\cup\beta.\equiv:\alpha\subset\gamma.\beta\subset\gamma.\supset_{\gamma}.x\in\gamma\) -/
theorem pm22_6 {x : α} {A B : Set α} : x ∈ A ∪ B ↔ ∀ C : Set α, A ⊆ C ∧ B ⊆ C → x ∈ C :=
  ⟨fun hx _ ⟨h1, h2⟩ => hx.elim (fun h => h1 h) (fun h => h2 h),
    fun h => h (A ∪ B) pm22_58⟩

/-- ✱22·61. \(\vdash:\alpha\subset\beta.\supset.\alpha\subset\beta\cup\gamma \quad[\text{*22*44·58}]\) -/
theorem pm22_61 {A B C : Set α} : A ⊆ B → A ⊆ B ∪ C := fun h _ hx => Or.inl (h hx)

/-- ✱22·62. \(\vdash:\alpha\subset\beta.\equiv.\alpha\cup\beta=\beta\) -/
theorem pm22_62 {A B : Set α} : A ⊆ B ↔ A ∪ B = B :=
  ⟨fun h => Set.ext fun _ => ⟨fun hx => hx.elim (fun hA => h hA) id, Or.inr⟩,
    fun h x hx => (Set.ext_iff.1 h x).1 (Or.inl hx)⟩

/-- ✱22·621. \(\vdash:\alpha\subset\beta.\equiv.\alpha\cap\beta=\alpha \quad[\text{*4·71}]\) -/
theorem pm22_621 {A B : Set α} : A ⊆ B ↔ A ∩ B = A :=
  ⟨fun h => Set.ext fun _ => ⟨fun hx => hx.1, fun hx => ⟨hx, h hx⟩⟩,
    fun h x hx => ((Set.ext_iff.1 h x).2 hx).2⟩

/-- ✱22·63. \(\vdash:\alpha\cup(\alpha\cap\beta)=\alpha \quad[\text{*4·44}]\) -/
theorem pm22_63 {A B : Set α} : A ∪ (A ∩ B) = A := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

/-- ✱22·631. \(\vdash.\alpha\cap(\alpha\cup\beta)=\alpha \quad[\text{*22·58·621}]\) -/
theorem pm22_631 {A B : Set α} : A ∩ (A ∪ B) = A := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

/-- ✱22·632. \(\vdash:\alpha=\beta.\supset.\alpha=\alpha\cap\beta \quad[\text{*22·42·621}]\) -/
theorem pm22_632 {A B : Set α} : A = B → A = A ∩ B := by
  rintro rfl
  exact pm22_5.symm

/-- ✱22·633. \(\vdash:\alpha\subset\beta.\supset.\alpha\cup\gamma=(\alpha\cap\beta)\cup\gamma \quad[\text{*22·551·621}]\) -/
theorem pm22_633 {A B C : Set α} : A ⊆ B → A ∪ C = (A ∩ B) ∪ C := by
  intro h
  ext x
  have hx := @h x
  simp only [Set.mem_union, Set.mem_inter_iff]
  tauto

/-- ✱22·64. \(\vdash\colon\ldotp\alpha\subset\gamma.\lor.\beta\subset\gamma:\supset.\alpha\cap\beta\subset\gamma\) -/
theorem pm22_64 {A B C : Set α} : A ⊆ C ∨ B ⊆ C → A ∩ B ⊆ C :=
  fun h _ hx => h.elim (fun h1 => h1 hx.1) (fun h2 => h2 hx.2)

/-- ✱22·65. \(\vdash\colon\ldotp\alpha\subset\beta.\lor.\alpha\subset\gamma:\supset.\alpha\subset\beta\cup\gamma \quad[\text{*22·61·57.*4·77}]\) -/
theorem pm22_65 {A B C : Set α} : A ⊆ B ∨ A ⊆ C → A ⊆ B ∪ C :=
  fun h _ hx => h.elim (fun h1 => Or.inl (h1 hx)) (fun h2 => Or.inr (h2 hx))

/-- ✱22·66. \(\vdash:\alpha\subset\beta.\supset.\alpha\cup\gamma\subset\beta\cup\gamma \quad[\text{*2·38}]\) -/
theorem pm22_66 {A B C : Set α} : A ⊆ B → A ∪ C ⊆ B ∪ C :=
  fun h _ hx => hx.imp (fun h' => h h') id

/-- ✱22·68. \(\vdash.(\alpha\cap\beta)\cup(\alpha\cap\gamma)=\alpha\cap(\beta\cup\gamma)\) -/
theorem pm22_68 {A B C : Set α} : (A ∩ B) ∪ (A ∩ C) = A ∩ (B ∪ C) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

/-- ✱22·69. \(\vdash.(\alpha\cup\beta)\cap(\alpha\cup\gamma)=\alpha\cup(\beta\cap\gamma) \quad[\text{Similar proof, by *4·41}]\) -/
theorem pm22_69 {A B C : Set α} : (A ∪ B) ∩ (A ∪ C) = A ∪ (B ∩ C) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  tauto

/-- ✱22·7. \(\vdash.(\alpha\cup\beta)\cup\gamma=\alpha\cup(\beta\cup\gamma) \quad[\text{*4·33}]\) -/
theorem pm22_7 {A B C : Set α} : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  simp only [Set.mem_union]
  tauto

/-- ✱22·71 (Df). \(\alpha\cup\beta\cup\gamma=(\alpha\cup\beta)\cup\gamma \quad\text{Df}\)

Lean's `∪` is left-associative, so `A ∪ B ∪ C` already is `(A ∪ B) ∪ C`. -/
theorem pm22_71 {A B C : Set α} : A ∪ B ∪ C = (A ∪ B) ∪ C := rfl

/-- ✱22·72. \(\vdash:\alpha\subset\gamma.\beta\subset\delta.\supset.\alpha\cup\beta\subset\gamma\cup\delta \quad[\text{*3·48}]\) -/
theorem pm22_72 {A B C D : Set α} : A ⊆ C ∧ B ⊆ D → A ∪ B ⊆ C ∪ D :=
  fun ⟨h1, h2⟩ _ hx => hx.imp (fun h => h1 h) (fun h => h2 h)

/-- ✱22·73. \(\vdash:\alpha=\gamma.\beta=\delta.\supset.\alpha\cup\beta=\gamma\cup\delta \quad[\text{*10·411}]\) -/
theorem pm22_73 {A B C D : Set α} : A = C ∧ B = D → A ∪ B = C ∪ D := by
  rintro ⟨rfl, rfl⟩
  rfl

/-- ✱22·74. \(\vdash:\alpha\cap\beta\subset\gamma.\alpha\cap\gamma\subset\beta.\equiv.\alpha\cap\beta=\alpha\cap\gamma\) -/
theorem pm22_74 {A B C : Set α} : A ∩ B ⊆ C ∧ A ∩ C ⊆ B ↔ A ∩ B = A ∩ C := by
  constructor
  · rintro ⟨h1, h2⟩
    exact Set.ext fun _ => ⟨fun hx => ⟨hx.1, h1 hx⟩, fun hx => ⟨hx.1, h2 hx⟩⟩
  · intro h
    exact ⟨fun x hx => ((Set.ext_iff.1 h x).1 hx).2, fun x hx => ((Set.ext_iff.1 h x).2 hx).2⟩

/-- ✱22·8. \(\vdash.-(-\alpha)=\alpha \quad[\text{*4·13}]\) -/
theorem pm22_8 {A : Set α} : Aᶜᶜ = A := by
  ext x
  simp only [Set.mem_compl_iff]
  tauto

/-- ✱22·81. \(\vdash:\alpha\subset\beta.\equiv.-\beta\subset-\alpha \quad[\text{*4·1}]\) -/
theorem pm22_81 {A B : Set α} : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  simp only [Set.subset_def, Set.mem_compl_iff]
  exact ⟨fun h x hB hA => hB (h x hA), fun h x hA => by_contra fun hB => h x hB hA⟩

/-- ✱22·811. \(\vdash:\alpha\subset-\beta.\equiv.\beta\subset-\alpha \quad[\text{*4·1.*22·8}]\) -/
theorem pm22_811 {A B : Set α} : A ⊆ Bᶜ ↔ B ⊆ Aᶜ := by
  simp only [Set.subset_def, Set.mem_compl_iff]
  exact ⟨fun h x hB hA => h x hA hB, fun h x hA hB => h x hB hA⟩

/-- ✱22·82. \(\vdash:\alpha\cap\beta\subset\gamma.\equiv.\alpha-\gamma\subset-\beta \quad[\text{*4·14}]\) -/
theorem pm22_82 {A B C : Set α} : A ∩ B ⊆ C ↔ A \ C ⊆ Bᶜ := by
  simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff]
  exact forall_congr' fun x => by tauto

/-- ✱22·83. \(\vdash:\alpha=\beta.\equiv.-\alpha=-\beta \quad[\text{*4·11}]\) -/
theorem pm22_83 {A B : Set α} : A = B ↔ Aᶜ = Bᶜ :=
  ⟨fun h => h ▸ rfl, fun h => by rw [← pm22_8 (A := A), h, pm22_8]⟩

/-- ✱22·831. \(\vdash:\alpha=-\beta.\equiv.\beta=-\alpha \quad[\text{*4·12}]\) -/
theorem pm22_831 {A B : Set α} : A = Bᶜ ↔ B = Aᶜ :=
  ⟨fun h => by rw [h, pm22_8], fun h => by rw [h, pm22_8]⟩

/-- ✱22·84. \(\vdash.-(\alpha\cap\beta)=-\alpha\lor-\beta \quad[\text{*4·51}]\)

**Status.** proved (reading): transcription error of the e-text, which prints `∨` (between classes,
where it is not significant) for `∪`; this is De Morgan's formula, from ✱4·51 as cited, cf.
✱22·86·87. -/
theorem pm22_84 {A B : Set α} : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
  tauto

/-- ✱22·85. \(\vdash.\alpha\cap\beta=-(-\alpha\lor-\beta) \quad[\text{*22·84·831}]\)

**Status.** proved (reading): transcription error of the e-text, which prints `∨` for `∪`, as in
✱22·84 (from which it is derived). -/
theorem pm22_85 {A B : Set α} : A ∩ B = (Aᶜ ∪ Bᶜ)ᶜ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
  tauto

/-- ✱22·86. \(\vdash.-(-\alpha\cap-\beta)=\alpha\cup\beta \quad[\text{*4·57}]\) -/
theorem pm22_86 {A B : Set α} : (Aᶜ ∩ Bᶜ)ᶜ = A ∪ B := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
  tauto

/-- ✱22·87. \(\vdash.-\alpha\cap-\beta=-(\alpha\cup\beta) \quad[\text{*22·86·831}]\) -/
theorem pm22_87 {A B : Set α} : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
  tauto

/-- ✱22·88. \(\vdash.(x).x\in(\alpha\cup-\alpha) \quad[\text{*2·11}]\) -/
theorem pm22_88 {A : Set α} : ∀ x, x ∈ A ∪ Aᶜ := fun x => Classical.em (x ∈ A)

/-- ✱22·89. \(\vdash.(x).x{\sim}\in(\alpha-\alpha) \quad[\text{*3·24}]\) -/
theorem pm22_89 {A : Set α} : ∀ x, x ∉ A \ A := fun _ hx => hx.2 hx.1

/-- ✱22·9. \(\vdash.(\alpha\cup\beta)-\beta=\alpha-\beta \quad[\text{*5·61}]\) -/
theorem pm22_9 {A B : Set α} : (A ∪ B) \ B = A \ B := by
  ext x
  simp only [Set.mem_union, Set.mem_sdiff]
  tauto

/-- ✱22·91. \(\vdash.\alpha\cup\beta=\alpha\cup(\beta-\alpha)\) -/
theorem pm22_91 {A B : Set α} : A ∪ B = A ∪ (B \ A) := by
  ext x
  simp only [Set.mem_union, Set.mem_sdiff]
  tauto

/-- ✱22·92. \(\vdash:\alpha\subset\beta.\supset.\beta=\alpha\cup(\beta-\alpha) \quad[\text{*22·91·62}]\) -/
theorem pm22_92 {A B : Set α} : A ⊆ B → B = A ∪ (B \ A) := by
  intro h
  ext x
  have hx := @h x
  simp only [Set.mem_union, Set.mem_sdiff]
  tauto

/-- ✱22·93. \(\vdash.\alpha-\beta=\alpha-(\alpha\cap\beta)\) -/
theorem pm22_93 {A B : Set α} : A \ B = A \ (A ∩ B) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff]
  tauto

/-- ✱22·94. \(\vdash:(\alpha).f\alpha.\equiv.(\alpha).f(-\alpha)\) -/
theorem pm22_94 {f : Set α → Prop} : (∀ A : Set α, f A) ↔ ∀ A : Set α, f Aᶜ :=
  ⟨fun h _ => h _, fun h A => pm22_8 (A := A) ▸ h Aᶜ⟩

/-- ✱22·95. \(\vdash:(\exists \alpha).f\alpha.\equiv.(\exists \alpha).f(-\alpha)\) -/
theorem pm22_95 {f : Set α → Prop} : (∃ A : Set α, f A) ↔ ∃ A : Set α, f Aᶜ :=
  ⟨fun ⟨A, h⟩ => ⟨Aᶜ, (pm22_8 (A := A)).symm ▸ h⟩, fun ⟨A, h⟩ => ⟨Aᶜ, h⟩⟩

end PrincipiaMathematica
