import PrincipiaMathematica.Basic

/-!
# Part I (Mathematical Logic): the definitions

Every definition (Df) of ✱1–✱43, in PM's order. Each entry is headed `**✱N·M Df.**` with the formula
as printed (MathJax TeX, from `data/principia.json`) and says how the Df is read in Lean
(conventions: `PrincipiaMathematica/Basic.lean`). Two kinds of entries:

* a `def` (or a mathlib operation) for a Df that defines a *term*; its defining equation holds by
  `rfl`/`Iff.rfl`, and the Section file states it as `pmN_M` (status `definition`);
* a *translation rule* (a `/-! … -/` block) for a Df that is a notational convention or a
  contextual definition, or whose definiendum is read by a Lean primitive; the block gives the
  *target statement* of `pmN_M` and its status.

The file ends with sanity lemmas showing that the encodings behave (identity is `Eq`, `TheIs` is
`∃!`, descriptions of `graph`s reduce, classes and relations are extensional, reducibility);
Section agents may use them.
-/

namespace PrincipiaMathematica

universe u v w u' v'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'} {ε : Type v'}

/-! ## Section A: the theory of deduction (✱1–✱5) -/

/-!
**✱1·01 Df.** \(p\supset q.=.\sim {p} \lor q \qquad \text{Df}.\)

Read `p ⊃ q` as Lean's `p → q`. Target (status `proved (reading)`):
`theorem pm1_01 {p q : Prop} : (p → q) ↔ ¬p ∨ q`.
-/

/-- **✱2·33 Df.** \(p\lor q \lor r.=.(p \lor q) \lor r\, \quad\text{Df}\)

The three-term disjunction brackets to the left. In formulas write `(p ∨ q) ∨ r` (Lean's `∨` is
right-associative). Target: `pm2_33 : Disj3 p q r ↔ (p ∨ q) ∨ r := Iff.rfl`. -/
def Disj3 (p q r : Prop) : Prop := (p ∨ q) ∨ r

/-!
**✱3·01 Df.** \(p . q . = {\sim} ({\sim} p \lor {\sim} q) \quad \text{Df}\)

Read `p . q` as Lean's `p ∧ q`. Target (status `proved (reading)`):
`theorem pm3_01 {p q : Prop} : p ∧ q ↔ ¬(¬p ∨ ¬q)`.
-/

/-- **✱3·02 Df.** \(p\supset q\supset r.=.p\supset q.q \supset r \quad \text{Df}\)

An undotted chain of implications is the *conjunction* of the links, **not** `p → q → r`. In
formulas write `(p → q) ∧ (q → r)`. Target: `pm3_02 : ImpChain p q r ↔ (p → q) ∧ (q → r) :=
Iff.rfl`. -/
def ImpChain (p q r : Prop) : Prop := (p → q) ∧ (q → r)

/-!
**✱4·01 Df.** \(p\equiv q.=.p\supset q.q\supset p\quad \text{Df}\)

Read `p ≡ q` as Lean's `p ↔ q`. Target (status `proved (reading)`, e.g. by `iff_def`):
`theorem pm4_01 {p q : Prop} : (p ↔ q) ↔ (p → q) ∧ (q → p)`.
-/

/-- **✱4·02 Df.** \(p\equiv q\equiv r.=.p\equiv q.q\equiv r \quad\text{Df}\)

A chain of equivalences is the conjunction of the links. In formulas write
`(p ↔ q) ∧ (q ↔ r)` (and so on for longer chains, as in ✱14·202). Target:
`pm4_02 : EqvChain p q r ↔ (p ↔ q) ∧ (q ↔ r) := Iff.rfl`. -/
def EqvChain (p q r : Prop) : Prop := (p ↔ q) ∧ (q ↔ r)

/-- **✱4·34 Df.** \(p.q.r.=.(p.q).r \quad\text{Df}\)

A product of three brackets to the left. In formulas write `(p ∧ q) ∧ r`. Target:
`pm4_34 : Conj3 p q r ↔ (p ∧ q) ∧ r := Iff.rfl`. -/
def Conj3 (p q r : Prop) : Prop := (p ∧ q) ∧ r

/-! ## Section B: the theory of apparent variables (✱9–✱14) -/

/-!
**✱9·01 Df.** \(\sim \{(x)\ldotp \phi x\}\ldotp =\ldotp (\exists x)\ldotp \sim \phi x \quad \text{Df}\)

**✱9·02 Df.** \(\sim \{(\exists x)\ldotp \phi x\}\ldotp =\ldotp (x)\ldotp \sim \phi x \quad \text{Df}\)

PM defines the negation of a quantified proposition (∼ is primitive only for elementary
propositions); Lean's `¬` applies to every proposition, so these Dfs are theorems. Targets (status
`proved (reading)`), with `{φ : α → Prop}`:
`pm9_01 : ¬(∀ x, φ x) ↔ ∃ x, ¬φ x`; `pm9_02 : ¬(∃ x, φ x) ↔ ∀ x, ¬φ x`.

**✱9·011 Df.** \(\sim (x)\ldotp \phi x\ldotp =\ldotp \sim \{(x)\ldotp \phi x\} \quad \text{Df}\)

**✱9·021 Df.** \(\sim (\exists x)\ldotp \phi x\ldotp =\ldotp \sim \{(\exists x)\ldotp \phi x\} \quad \text{Df}\)

Bracketing conventions: `∼` before a quantifier prefix negates the whole quantified proposition.
Targets (status `definition`): `pm9_011 : (¬ ∀ x, φ x) ↔ ¬(∀ x, φ x) := Iff.rfl`,
`pm9_021 : (¬ ∃ x, φ x) ↔ ¬(∃ x, φ x) := Iff.rfl`.

**✱9·03 Df.** (\(x)\ldotp \phi x\ldotp \lor \ldotp p\colon=\ldotp (x)\ldotp \phi x \lor p \quad \text{Df}\)

**✱9·04 Df.** \(p\ldotp \lor \ldotp (x)\ldotp \phi x\colon=\ldotp (x)\ldotp p \lor \phi x \quad \text{Df}\)

**✱9·05 Df.** (\(\exists x)\ldotp \phi x\ldotp \lor \ldotp p\colon=\ldotp (\exists x)\ldotp \phi x \lor p \quad \text{Df}\)

**✱9·06 Df.** \(p\ldotp \lor \ldotp (\exists x)\ldotp \phi x\colon=\ldotp (\exists x)\ldotp p \lor \phi x \quad \text{Df}\)

**✱9·07 Df.** (\(x)\ldotp \phi x\ldotp \lor \ldotp (\exists y)\ldotp \psi y \colon=\colon(x)\colon(\exists y)\ldotp \phi x \lor \psi y \quad \text{Df}\)

**✱9·08 Df.** (\(\exists y)\ldotp \psi y\ldotp \lor \ldotp (x)\ldotp \phi x\colon=\colon(x)\colon(\exists y)\ldotp \psi y \lor \phi x \quad \text{Df}\)

Disjunctions with quantified disjuncts are defined by prenex forms; in Lean they are theorems
(status `proved (reading)`), with `{p : Prop} {φ : α → Prop} {ψ : β → Prop}`:
`pm9_03 : (∀ x, φ x) ∨ p ↔ ∀ x, φ x ∨ p`; `pm9_04 : p ∨ (∀ x, φ x) ↔ ∀ x, p ∨ φ x`;
`pm9_05 [Nonempty α] : (∃ x, φ x) ∨ p ↔ ∃ x, φ x ∨ p`;
`pm9_06 [Nonempty α] : p ∨ (∃ x, φ x) ↔ ∃ x, p ∨ φ x`;
`pm9_07 [Nonempty β] : (∀ x, φ x) ∨ (∃ y, ψ y) ↔ ∀ x, ∃ y, φ x ∨ ψ y`;
`pm9_08 [Nonempty β] : (∃ y, ψ y) ∨ (∀ x, φ x) ↔ ∀ x, ∃ y, ψ y ∨ φ x`.
The `[Nonempty _]` hypotheses are PM's tacit assumption that every type has a member (Basic §3):
without them ✱9·05–✱9·08 fail for an empty type; say so in the status.
-/

/-!
**✱10·01 Df.** (\(\exists x).\phi x.=.{\sim}(x).{\sim}\phi x \quad\text{Df}\)

In ✱10 `∃` is defined from `(x)`; Lean's `∃` is primitive. Target (status `proved (reading)`):
`pm10_01 : (∃ x, φ x) ↔ ¬ ∀ x, ¬φ x`.
-/

/-- **✱10·02 Df.** \(\phi x\supset_{x}\psi x.=.(x).\phi x\supset\psi x \quad\text{Df}\)

Formal implication. In formulas write `∀ x, φ x → ψ x` directly. Target:
`pm10_02 : FImp φ ψ ↔ ∀ x, φ x → ψ x := Iff.rfl`. -/
def FImp (φ ψ : α → Prop) : Prop := ∀ x, φ x → ψ x

/-- **✱10·03 Df.** \(\phi x\equiv_{x}\psi x.=.(x).\phi x\equiv\psi x \quad\text{Df}\)

Formal equivalence. In formulas write `∀ x, φ x ↔ ψ x`. Target:
`pm10_03 : FEqv φ ψ ↔ ∀ x, φ x ↔ ψ x := Iff.rfl`. -/
def FEqv (φ ψ : α → Prop) : Prop := ∀ x, φ x ↔ ψ x

/-!
**✱11·01 Df.** (\(x,y).\phi(x,y).=:(x):(y).\phi(x,y) \quad\text{Df}\)

**✱11·02 Df.** (\(x,y,z).\phi(x,y,z).=:(x):(y,z).\phi(x,y,z) \quad\text{Df}\)

**✱11·03 Df.** (\(\exists x,y).\phi(x,y).=:(\exists x):(\exists y).\phi(x,y) \quad\text{Df}\)

**✱11·04 Df.** (\(\exists x,y,z).\phi(x,y,z).=:(\exists x):(\exists y,z).\phi(x,y,z) \quad\text{Df}\)

Several apparent variables: Lean's `∀ x y` *is* `∀ x, ∀ y`, and `∃ x y` is `∃ x, ∃ y`. Functions
of several variables are curried: `φ(x, y)` is `φ x y` with `φ : α → β → Prop`. Targets (status
`definition`, all `Iff.rfl`): `pm11_01 : (∀ x y, φ x y) ↔ ∀ x, ∀ y, φ x y`;
`pm11_02 : (∀ x y z, φ x y z) ↔ ∀ x, ∀ y z, φ x y z`; `pm11_03 : (∃ x y, φ x y) ↔ ∃ x, ∃ y, φ x y`;
`pm11_04 : (∃ x y z, φ x y z) ↔ ∃ x, ∃ y z, φ x y z`.
-/

/-- **✱11·05 Df.** \(\phi(x,y).\supset_{x,y}.\psi(x,y):=:(x,y):\phi(x,y).\supset.\psi(x,y) \quad\text{Df}\)

In formulas write `∀ x y, φ x y → ψ x y`. Target:
`pm11_05 : FImp2 φ ψ ↔ ∀ x y, φ x y → ψ x y := Iff.rfl`. -/
def FImp2 (φ ψ : α → β → Prop) : Prop := ∀ x y, φ x y → ψ x y

/-- **✱11·06 Df.** \(\phi(x,y).\equiv_{x,y}.\psi(x,y):=:(x,y):\phi(x,y).\equiv.\psi(x,y) \quad\text{Df}\)

In formulas write `∀ x y, φ x y ↔ ψ x y`. Target:
`pm11_06 : FEqv2 φ ψ ↔ ∀ x y, φ x y ↔ ψ x y := Iff.rfl`. -/
def FEqv2 (φ ψ : α → β → Prop) : Prop := ∀ x y, φ x y ↔ ψ x y

/-!
✱12 has no Df. Its primitive propositions are the axiom of reducibility, read in Lean (Basic §4):
✱12·1 `pm12_1 : ∃ f : α → Prop, ∀ x, φ x ↔ f x` and ✱12·11
`pm12_11 : ∃ f : α → β → Prop, ∀ x y, φ x y ↔ f x y`, status
`proved (reading): every Lean function is predicative` (see `reducibility` below).
-/

/-- **✱13·01 Df.** \(x=y.=:(\phi):\phi!x.\supset.\phi!y \quad\text{Df}\)

The definiens of PM's identity (Leibniz identity over predicative functions, which in Lean are all
functions `α → Prop`). PM's `=` is read as Lean's `=` everywhere (`PMIdent_iff_eq`). Target
(status `proved (reading)`): `pm13_01 {x y : α} : x = y ↔ PMIdent x y`. -/
def PMIdent (x y : α) : Prop := ∀ φ : α → Prop, φ x → φ y

/-!
**✱13·02 Df.** \(x\neq y.=.{\sim}(x=y) \quad\text{Df}\)

Lean's `x ≠ y` is `¬(x = y)` by definition. Target (status `definition`):
`pm13_02 {x y : α} : x ≠ y ↔ ¬(x = y) := Iff.rfl`.
-/

/-- **✱13·03 Df.** \(x=y=z.=.x=y.y=z \quad\text{Df}\)

A chain of identities is the conjunction of the links; in formulas write `x = y ∧ y = z` (also for
classes, relations and descriptive expressions: `A = B = C` with descriptions is the conjunction of
the two identities, each translated with its own descriptions). Target:
`pm13_03 : EqChain x y z ↔ x = y ∧ y = z := Iff.rfl`. -/
def EqChain (x y z : α) : Prop := x = y ∧ y = z

/-- **✱14·01 Df.** \([({℩}x)(\phi x)].\psi ({℩}x)(\phi x).=:(\exists b):\phi x.\equiv_{x}.x=b:\psi b \quad\text{Df}\)

`TheIs φ ψ` is "the `x` satisfying `φ` satisfies `ψ`", i.e. `ψ(℩x)(φx)` with the description
having scope `ψ`. A description is an incomplete symbol: it is never a Lean term. Every formula
containing `(℩x)(φx)` is translated by choosing its scope (by default the smallest proposition in
dots or brackets containing it; Basic §5) and replacing that proposition `ψ(℩x)(φx)` by
`TheIs φ ψ`. E.g. `a = (℩x)(φx)` is `TheIs φ (fun b => a = b)`; `∼{ψ(℩x)(φx)}` is
`¬ TheIs φ ψ`; `[(℩x)(φx)] : ψ(℩x)(φx) . ⊃ . p` is `TheIs φ (fun b => ψ b → p)`. Descriptions of
classes (✱20·072) and relations (✱21·072) use the same `TheIs` at type `Set α`,
`α → β → Prop`. Target: `pm14_01 : TheIs φ ψ ↔ ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b := Iff.rfl`. -/
def TheIs (φ ψ : α → Prop) : Prop := ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b

/-- **✱14·02 Df.** \(\text{E}!({℩}x)(\phi x).=:(\exists b):\phi x.\equiv_{x}.x=b \quad\text{Df}\)

"The `x` satisfying `φ` exists": `E!(℩x)(φx)`. It is Lean's `∃! x, φ x` (`EBang_iff_existsUnique`),
but keep `EBang` in statements. Do not confuse with PM's `∃!α` (✱24·03, `A.Nonempty`). Target:
`pm14_02 : EBang φ ↔ ∃ b, ∀ x, φ x ↔ x = b := Iff.rfl`. -/
def EBang (φ : α → Prop) : Prop := ∃ b, ∀ x, φ x ↔ x = b

/-- **✱14·03 Df.**
\[\begin{align}[({℩}x)(\phi x),({℩}x)&(\psi x)].f\{({℩}x)(\phi x),\,({℩}x)(\psi x)\}.=:\\ &[({℩}x)(\phi x)]:[({℩}x)(\psi x)].f\{({℩}x)(\phi x),({℩}x)(\psi x)\} \quad\text{Df}\end{align}\]

Two descriptions, the first having the larger scope. By PM's convention (stated between ✱14·03
and ✱14·04, justified by ✱14·113) this is also the reading of `f{(℩x)(φx), (℩x)(ψx)}` when no scope is indicated: the description occurring
first typographically has the larger scope. Target:
`pm14_03 : TheIs2 φ ψ f ↔ TheIs φ (fun b => TheIs ψ (fun c => f b c)) := Iff.rfl`. -/
def TheIs2 (φ : α → Prop) (ψ : β → Prop) (f : α → β → Prop) : Prop :=
  TheIs φ (fun b => TheIs ψ (fun c => f b c))

/-- **✱14·04 Df.**
\[\begin{align}[({℩}x)(\psi x)].&f\{({℩}x)(\phi x),\,({℩}x)(\psi x)\}.=.\\ &[({℩}x)(\psi x),({℩}x)(\phi x)].f\{({℩}x)(\phi x),\,({℩}x)(\psi x)\} \quad\text{Df}\end{align}\]

Two descriptions where the *second* (`(℩x)(ψx)`) is given the larger scope. Target:
`pm14_04 : TheIs2Rev φ ψ f ↔ TheIs2 ψ φ (fun c b => f b c) := Iff.rfl`. -/
def TheIs2Rev (φ : α → Prop) (ψ : β → Prop) (f : α → β → Prop) : Prop :=
  TheIs ψ (fun c => TheIs φ (fun b => f b c))

/-! ## Section C: classes and relations (✱20–✱25) -/

/-!
**✱20·01 Df.** \(f\{\hat{z}(\psi z)\}.=:(\exists \phi):\phi!x.\equiv_{x}.\psi x:f(\phi!\hat{z}) \quad\text{Df}\)

PM's contextual definition of classes ("no-class theory"). Lean reads the class `ẑ(ψz)` as the
term `{z | ψ z} : Set α` (Basic §6); the Df becomes a theorem (status
`proved (reading): classes are read as terms of Set α`), with `{ψ : α → Prop} {f : Set α → Prop}`:
`pm20_01 : f {z | ψ z} ↔ ∃ φ : α → Prop, (∀ x, φ x ↔ ψ x) ∧ f {z | φ z}`.

**✱20·02 Df.** \(x\in (\phi!\hat{z}).=.\phi!x \quad\text{Df}\)

Membership. Target (status `definition`): `pm20_02 : x ∈ {z | φ z} ↔ φ x := Iff.rfl`.
-/

/-- **✱20·03 Df.** \(\text{Cls}=\hat{\alpha}\{(\exists \phi).\alpha=\hat{z}(\phi!z)\} \quad\text{Df}\)

The class of classes (of α-things; typically ambiguous). It is `Set.univ` (`Cls_eq_univ`). Target:
`pm20_03 : (Cls : Set (Set α)) = {A | ∃ φ : α → Prop, A = {z | φ z}} := rfl`. -/
def Cls : Set (Set α) := {A | ∃ φ : α → Prop, A = {z | φ z}}

/-- **✱20·04 Df.** \(x,\,y\in \alpha.=.x\in \alpha.y\in \alpha \quad\text{Df}\)

In formulas write `x ∈ A ∧ y ∈ A`. Target: `pm20_04 : Mem2 x y A ↔ x ∈ A ∧ y ∈ A := Iff.rfl`. -/
def Mem2 (x y : α) (A : Set α) : Prop := x ∈ A ∧ y ∈ A

/-- **✱20·05 Df.** \(x,\,y,\,z\in \alpha.=.x,\,y\in \alpha.z\in \alpha \quad\text{Df}\)

In formulas write `(x ∈ A ∧ y ∈ A) ∧ z ∈ A`. Target:
`pm20_05 : Mem3 x y z A ↔ Mem2 x y A ∧ z ∈ A := Iff.rfl`. -/
def Mem3 (x y z : α) (A : Set α) : Prop := Mem2 x y A ∧ z ∈ A

/-!
**✱20·06 Df.** \(x{\sim}\in \alpha.=.{\sim}(x\in \alpha) \quad\text{Df}\)

`x ∼∈ α` is Lean's `x ∉ A`. Target (status `definition`): `pm20_06 : x ∉ A ↔ ¬(x ∈ A) := Iff.rfl`.

**✱20·07 Df.** (\(\alpha).f\alpha.=.(\phi).f\{\hat{z}(\phi!z)\} \quad\text{Df}\)

**✱20·071 Df.** (\(\exists \alpha).f\alpha.=.(\exists \phi).f\{\hat{z}(\phi!z)\} \quad\text{Df}\)

Apparent variables ranging over classes are `A : Set α`. Targets (status `proved (reading)`;
not `Iff.rfl`, but `⟨fun h _ => h _, fun h A => h (· ∈ A)⟩`), with `{f : Set α → Prop}`:
`pm20_07 : (∀ A : Set α, f A) ↔ ∀ φ : α → Prop, f {z | φ z}`;
`pm20_071 : (∃ A : Set α, f A) ↔ ∃ φ : α → Prop, f {z | φ z}`.

**✱20·072 Df.** \([(℩\alpha)(\phi\alpha)].f(℩\alpha)(\phi\alpha).=:(\exists \gamma):\phi\alpha.\equiv_{\alpha}.\alpha=\gamma:f\gamma \quad\text{Df}\)

Descriptions of classes are `TheIs` at type `Set α`. Target (status `definition`), with
`{φ f : Set α → Prop}`: `pm20_072 : TheIs φ f ↔ ∃ γ, (∀ A, φ A ↔ A = γ) ∧ f γ := Iff.rfl`.

**✱20·08 Df.** \(f\{\hat{\alpha}(\psi\alpha)\}.=:(\exists \phi):\psi\alpha.\equiv_{\alpha}.\phi!\alpha:f(\phi!\hat{\alpha}) \quad\text{Df}\)

Classes of classes are `Set (Set α)`. Target (status `proved (reading)`), with
`{ψ : Set α → Prop} {f : Set (Set α) → Prop}`:
`pm20_08 : f {A | ψ A} ↔ ∃ φ : Set α → Prop, (∀ A, ψ A ↔ φ A) ∧ f {A | φ A}`.

**✱20·081 Df.** \(\alpha\in \psi!\hat{\alpha}.=.\psi!\alpha \quad\text{Df}\)

Target (status `definition`): `pm20_081 : A ∈ {B : Set α | ψ B} ↔ ψ A := Iff.rfl`.

**✱21·01 Df.** \(f\{\hat{x}\hat{y}\psi(x,y)\}.=:(\exists \phi):\phi!(x,y).\equiv_{x,y}.\psi(x,y):f\{\phi!(\hat{u},\hat{v})\} \quad\text{Df}\)

A relation `x̂ŷ ψ(x, y)` is the term `fun x y => ψ x y : α → β → Prop`. Target (status
`proved (reading)`), with `{ψ : α → β → Prop} {f : (α → β → Prop) → Prop}`:
`pm21_01 : f (fun x y => ψ x y) ↔ ∃ φ : α → β → Prop, (∀ x y, φ x y ↔ ψ x y) ∧ f (fun u v => φ u v)`.

**✱21·02 Df.** \(a\{\phi!(\hat{x},\hat{y})\}b.=.\phi!(a,b) \quad\text{Df}\)

`xRy` is `R x y`. Target (status `definition`):
`pm21_02 : (fun x y => φ x y) a b ↔ φ a b := Iff.rfl`.
-/

/-- **✱21·03 Df.** \(\text{Rel}=\hat{R}\{(\exists \phi).R=\hat{x}\hat{y}\phi!(x,y)\} \quad\text{Df}\)

The class of relations (from α-things to β-things; typically ambiguous). It is `Set.univ`
(`Rel_eq_univ`). Inside the namespace `Rel` is this definition, not mathlib's `Rel`. Target:
`pm21_03 : (Rel : Set (α → β → Prop)) = {R | ∃ φ : α → β → Prop, R = fun x y => φ x y} := rfl`. -/
def Rel : Set (α → β → Prop) := {R | ∃ φ : α → β → Prop, R = fun x y => φ x y}

/-!
**✱21·07 Df.** (\(R).fR.=.(\phi).f\{\hat{x}\hat{y}\phi!(x,y)\} \quad\text{Df}\)

**✱21·071 Df.** (\(\exists R).fR.=.(\exists \phi).f\{\hat{x}\hat{y}\phi!(x,y)\} \quad\text{Df}\)

Apparent variables ranging over relations are `R : α → β → Prop`. Targets (status `definition`,
both hold by `Iff.rfl`), with `{f : (α → β → Prop) → Prop}`:
`pm21_07 : (∀ R : α → β → Prop, f R) ↔ ∀ φ : α → β → Prop, f (fun x y => φ x y)`;
`pm21_071 : (∃ R : α → β → Prop, f R) ↔ ∃ φ : α → β → Prop, f (fun x y => φ x y)`.

**✱21·072 Df.** \([({℩}R)(\phi R)].f({℩}R)(\phi R).=:(\exists S):\phi R.\equiv_{R}.R=S:fS \quad\text{Df}\)

Descriptions of relations are `TheIs` at type `α → β → Prop`. Target (status `definition`):
`pm21_072 : TheIs φ f ↔ ∃ S, (∀ R, φ R ↔ R = S) ∧ f S := Iff.rfl`.

**✱21·08 Df.** \(f\{\hat{R}\hat{S}\psi(R,S)\}.=:(\exists \phi):\psi(R,S).\equiv_{R,S}.\phi!(R,S):f\{\phi!(\hat{R},\hat{S})\} \quad\text{Df}\)

Relations between relations are `(α → β → Prop) → (γ → δ → Prop) → Prop`. Target (status
`proved (reading)`), with `{ψ : (α → β → Prop) → (γ → δ → Prop) → Prop}` and `f` on such relations:
`pm21_08 : f (fun R S => ψ R S) ↔ ∃ φ, (∀ R S, ψ R S ↔ φ R S) ∧ f (fun R S => φ R S)`.

**✱21·081 Df.** \(P\{\phi!(\hat{R},\hat{S})\}Q.=.\phi!(P,Q) \quad\text{Df}\)

Target (status `definition`): `pm21_081 : (fun R S => φ R S) P Q ↔ φ P Q := Iff.rfl`.

**✱21·082 Df.** \(f\{\hat{R}(\psi R)\}.=:(\exists \phi):\psi R.\equiv_{R}.\phi!R:f(\phi!\hat{R}) \quad\text{Df}\)

Classes of relations are `Set (α → β → Prop)`. Target (status `proved (reading)`):
`pm21_082 : f {R | ψ R} ↔ ∃ φ : (α → β → Prop) → Prop, (∀ R, ψ R ↔ φ R) ∧ f {R | φ R}`.

**✱21·083 Df.** \(R\in \phi!\hat{R}.=.\phi!R \quad\text{Df}\)

Target (status `definition`): `pm21_083 : R ∈ {S : α → β → Prop | φ S} ↔ φ R := Iff.rfl`.
-/

/-!
**✱22·01 Df.** \(\alpha \subset \beta .=: x \in \alpha .\supset_{x}. x \in \beta \quad \text{Df}\)

**PM's `α ⊂ β` is mathlib's `A ⊆ B`** (inclusion; Lean's `⊂` is *strict* inclusion and must not
be used for PM's `⊂`). Target (status `definition`):
`pm22_01 : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := Iff.rfl`.

**✱22·02 Df.** \(\alpha \cap \beta = \hat{x}(x \in \alpha . x \in \beta) \quad \text{Df}\)

mathlib's `A ∩ B`. Target: `pm22_02 : A ∩ B = {x | x ∈ A ∧ x ∈ B} := rfl`.

**✱22·03 Df.** \(\alpha \cup \beta = \hat{x}(x \in \alpha .\lor. x \in \beta) \quad \text{Df}\)

mathlib's `A ∪ B`. Target: `pm22_03 : A ∪ B = {x | x ∈ A ∨ x ∈ B} := rfl`.

**✱22·04 Df.** \(-\alpha = \hat{x}(x \mathop{{\sim}{\in}} \alpha) \quad \text{Df}\)

mathlib's `Aᶜ`. Target: `pm22_04 : Aᶜ = {x | x ∉ A} := rfl`.

**✱22·05 Df.** \(\alpha-\beta=\alpha\cap -\beta \quad\text{Df}\)

mathlib's `A \ B`. Target: `pm22_05 : A \ B = A ∩ Bᶜ := rfl`.

**✱22·53 Df.** \(\alpha \cap \beta \cap \gamma = (\alpha \cap \beta) \cap \gamma \quad\text{Df}\)

**✱22·71 Df.** \(\alpha\cup\beta\cup\gamma=(\alpha\cup\beta)\cup\gamma \quad\text{Df}\)

Bracketing conventions; Lean's `∩`, `∪` are left-associative, so `A ∩ B ∩ C` already means
`(A ∩ B) ∩ C`. Targets (status `definition`): `pm22_53 : A ∩ B ∩ C = (A ∩ B) ∩ C := rfl`,
`pm22_71 : A ∪ B ∪ C = (A ∪ B) ∪ C := rfl`.
-/

/-- **✱23·01 Df.** \(R \unicode{x2abd} S.=:xRy.\supset_{x,y}.xSy \quad \text{Df}\)

Inclusion of relations `R ⊂̇ S`, notation `R ⪽ S`. Target:
`pm23_01 : R ⪽ S ↔ ∀ x y, R x y → S x y := Iff.rfl`. -/
def RSub (R S : α → β → Prop) : Prop := ∀ x y, R x y → S x y

@[inherit_doc] scoped infix:50 " ⪽ " => RSub

/-- **✱23·02 Df.** \(\dot{\cap} S = \hat{x}\hat{y}(xRy.xSy) \quad \text{Df}\)

(The e-text omits the `R`: PM has \(R \dot{\cap} S = \hat{x}\hat{y}(xRy.xSy)\), cf. Introduction
p. 31.) Logical product of relations `R ∩̇ S`, notation `R ⩀ S`. Target:
`pm23_02 : R ⩀ S = fun x y => R x y ∧ S x y := rfl` (status `definition`; mention the
transcription error). -/
def rcap (R S : α → β → Prop) : α → β → Prop := fun x y => R x y ∧ S x y

@[inherit_doc] scoped infixl:67 " ⩀ " => rcap

/-- **✱23·03 Df.** \(R \unicode{x228d} S = \hat{x}\hat{y}(xRy .\lor. xSy) \quad \text{Df}\)

Logical sum of relations `R ∪̇ S`, notation `R ⊍ S`. Target:
`pm23_03 : R ⊍ S = fun x y => R x y ∨ S x y := rfl`. -/
def rcup (R S : α → β → Prop) : α → β → Prop := fun x y => R x y ∨ S x y

@[inherit_doc] scoped infixl:65 " ⊍ " => rcup

/-- **✱23·04 Df.** \(\unicode{x2238} R = \hat{x}\hat{y}\{{\sim}(xRy)\} \quad \text{Df}\)

Negation of a relation `−̇R`, notation `∸R`. Target: `pm23_04 : ∸R = fun x y => ¬R x y := rfl`. -/
def rneg (R : α → β → Prop) : α → β → Prop := fun x y => ¬R x y

@[inherit_doc] scoped prefix:75 "∸" => rneg

/-- **✱23·05 Df.** \(R \unicode{x2238}S = R \dot{\cap} \unicode{x2238}S \quad \text{Df}\)

Difference of relations `R −̇ S`, notation `R ∸ S`. Target: `pm23_05 : R ∸ S = R ⩀ ∸S := rfl`. -/
def rdiff (R S : α → β → Prop) : α → β → Prop := R ⩀ ∸S

@[inherit_doc] scoped infixl:65 " ∸ " => rdiff

/-!
**✱23·53 Df.** \(R\dot{\cap}S\dot{\cap}T=(R\dot{\cap}S)\dot{\cap}T \quad\text{Df}\)

**✱23·71 Df.** \(R\unicode{x228d}S\unicode{x228d}T=(R\unicode{x228d}S)\unicode{x228d}T \quad{\text{Df}}\)

`⩀` and `⊍` are left-associative. Targets (status `definition`):
`pm23_53 : R ⩀ S ⩀ T = (R ⩀ S) ⩀ T := rfl`, `pm23_71 : R ⊍ S ⊍ T = (R ⊍ S) ⊍ T := rfl`.
-/

/-- **✱24·01 Df.** \(\text{V} =\hat{x}(x=x) \quad\text{Df}\)

The universal class (of the type of α; typically ambiguous). `V_eq_univ : V = Set.univ`. Target:
`pm24_01 : (V : Set α) = {x | x = x} := rfl`. -/
def V : Set α := {x | x = x}

/-- **✱24·02 Df.** \(\Lambda =- \text{V} \quad\text{Df}\)

The null class, notation `Λ`. `Null_eq_empty : Λ = ∅`. Target:
`pm24_02 : (Λ : Set α) = Vᶜ := rfl`. -/
def Null : Set α := Vᶜ

@[inherit_doc] scoped notation "Λ" => Null

/-!
**✱24·03 Df.** \(\exists!\alpha.=.(\exists x).x \in \alpha \quad\text{Df} \quad\text{Df}\)

"α exists" (has at least one member) is mathlib's `A.Nonempty` (`Set.Nonempty A :≡ ∃ x, x ∈ A`).
**Not Lean's `∃!`** (unique existence, which is PM's `E!`). Target (status `definition`):
`pm24_03 : A.Nonempty ↔ ∃ x, x ∈ A := Iff.rfl`. (The e-text repeats "Df".)
-/

/-- **✱25·01 Df.** \(\dot{\text{V}} = \hat{x}\hat{y}(x = x . y = y) \quad \text{Df}\)

The universal relation `V̇`. Target: `pm25_01 : (rV : α → β → Prop) = fun x y => x = x ∧ y = y :=
rfl`. -/
def rV : α → β → Prop := fun x y => x = x ∧ y = y

/-- **✱25·02 Df.** \(\dot{\Lambda} = \dot{-}\dot{\text{V}} \quad \text{Df}\)

The null relation `Λ̇`. Target: `pm25_02 : (rNull : α → β → Prop) = ∸rV := rfl`. -/
def rNull : α → β → Prop := ∸rV

/-- **✱25·03 Df.** \(\dot{\exists}!R .=. (\exists x,y) . xRy \quad \text{Df}\)

"`R` exists" (holds between some pair) `∃̇!R`. Target: `pm25_03 : rEx R ↔ ∃ x y, R x y :=
Iff.rfl`. -/
def rEx (R : α → β → Prop) : Prop := ∃ x y, R x y

/-! ## Section D: logic of relations (✱30–✱38) -/

/-- **✱30·01 Df.** \(Rʻy=({℩}x)(xRy) \quad\text{Df}\)

The descriptive function `R'y` ("the `R` of `y`") is an incomplete symbol. A formula `ψ(R'y)`
(scope: the smallest proposition in dots or brackets containing `R'y`, Basic §5) is
`Desc R y ψ`; e.g. `x = R'y` is `Desc R y (fun b => x = b)`, `R'y = S'z` is
`Desc R y (fun b => Desc S z (fun c => b = c))`. Target:
`pm30_01 : Desc R y ψ ↔ TheIs (fun x => R x y) ψ := Iff.rfl`. -/
def Desc (R : α → β → Prop) (y : β) (ψ : α → Prop) : Prop := TheIs (fun x => R x y) ψ

/-- `E!R'y`: the descriptive function `R'y` exists (✱14·02 applied to ✱30·01). -/
def EDesc (R : α → β → Prop) (y : β) : Prop := EBang (fun x => R x y)

/-- **✱30·02 Df.** \(RʻSʻy=Rʻ(Sʻy) \quad\text{Df}\)

`ψ(R'S'y)`: the outer description `R'(…)` has the larger scope, and the inner `S'y` has the
smallest scope, inside `x R (S'y)` (PM's explanation after ✱30·02). Target:
`pm30_02 : Desc2 R S y ψ ↔ TheIs (fun x => Desc S y (fun z => R x z)) ψ := Iff.rfl`.
(`desc2_iff` shows `Desc2 R S y ψ ↔ Desc S y (fun z => Desc R z ψ)`.) -/
def Desc2 (R : α → β → Prop) (S : β → γ → Prop) (y : γ) (ψ : α → Prop) : Prop :=
  TheIs (fun x => Desc S y (fun z => R x z)) ψ

/-- **✱31·01 Df.** \(\text{Cnv}=\hat{Q}\hat{P}\{xQy.\equiv_{x,y}.yPx\} \quad\text{Df}\)

The relation `Cnv` of the converse `Q` of a relation to the relation `P`. `Cnv'P` is `cnv P`
(`desc_Cnv`). Target: `pm31_01 : (Cnv : (β → α → Prop) → (α → β → Prop) → Prop) =
fun Q P => ∀ x y, Q x y ↔ P y x := rfl`. -/
def Cnv : (β → α → Prop) → (α → β → Prop) → Prop := fun Q P => ∀ x y, Q x y ↔ P y x

/-- **✱31·02 Df.** \(\breve{P}=\hat{x}\hat{y}(yPx) \quad\text{Df}\)

The converse `P̆`, notation `P˘`. Target: `pm31_02 : P˘ = fun x y => P y x := rfl`. -/
def cnv (P : α → β → Prop) : β → α → Prop := fun x y => P y x

@[inherit_doc] scoped postfix:max "˘" => cnv

/-- `R⃗'y`, the class of referents of `y`: `x̂(xRy)` (✱32·13). Value function of `Rfwd R`. -/
def refs (R : α → β → Prop) (y : β) : Set α := {x | R x y}

/-- `R⃖'x`, the class of relata of `x`: `ŷ(xRy)` (✱32·131). Value function of `Rbwd R`. -/
def rels (R : α → β → Prop) (x : α) : Set β := {y | R x y}

/-- **✱32·01 Df.** \(\overrightarrow{R} = \hat{\alpha}\hat{y}\{\alpha = \hat{x}(x R y)\} \quad \text{Df}\)

The relation `R⃗` of the class of referents of `y` to `y`. `R⃗'y` is `refs R y`
(`desc_graph`). Target: `pm32_01 : Rfwd R = fun A y => A = {x | R x y} := rfl`. -/
def Rfwd (R : α → β → Prop) : Set α → β → Prop := graph (refs R)

/-- **✱32·02 Df.** \(\overleftarrow{R} = \hat{\beta}\hat{x}\{\beta = \hat{y}(xRy)\} \quad \text{Df}\)

The relation `R⃖` of the class of relata of `x` to `x`. `R⃖'x` is `rels R x`. Target:
`pm32_02 : Rbwd R = fun B x => B = {y | R x y} := rfl`. -/
def Rbwd (R : α → β → Prop) : Set β → α → Prop := graph (rels R)

/-- **✱32·03 Df.** \(\text{sg}=\hat{A}\hat{R}(A=\overrightarrow{R}) \quad\text{Df}\)

The relation of `R⃗` to `R`; `sg'R` is `Rfwd R`. Target:
`pm32_03 : (sg : (Set α → β → Prop) → (α → β → Prop) → Prop) = fun A R => A = Rfwd R := rfl`. -/
def sg : (Set α → β → Prop) → (α → β → Prop) → Prop := graph Rfwd

/-- **✱32·04 Df.** \(\text{gs}=\hat{A}\hat{R}(A=\overleftarrow{R}) \quad\text{Df}\)

The relation of `R⃖` to `R`; `gs'R` is `Rbwd R`. Target:
`pm32_04 : (gs : (Set β → α → Prop) → (α → β → Prop) → Prop) = fun A R => A = Rbwd R := rfl`. -/
def gs : (Set β → α → Prop) → (α → β → Prop) → Prop := graph Rbwd

/-- `D'R`, the domain `x̂{(∃y).xRy}` (✱33·11). Value function of `D`. -/
def dom (R : α → β → Prop) : Set α := {x | ∃ y, R x y}

/-- `ᗡ'R`, the converse domain `ŷ{(∃x).xRy}` (✱33·111). Value function of `Dcnv`. -/
def codom (R : α → β → Prop) : Set β := {y | ∃ x, R x y}

/-- `C'R`, the field `x̂{(∃y) : xRy . ∨ . yRx}` (✱33·112), for a homogeneous relation. Value
function of `C`. -/
def fld (R : α → α → Prop) : Set α := {x | ∃ y, R x y ∨ R y x}

/-- **✱33·01 Df.** \(\text{D}=\hat{\alpha}\hat{R}[\alpha=\hat{x}\{(\exists y).xRy\}] \quad\text{Df}\)

The relation of the domain of `R` to `R`. `D'R` is `dom R`. Target:
`pm33_01 : (D : Set α → (α → β → Prop) → Prop) = fun A R => A = {x | ∃ y, R x y} := rfl`. -/
def D : Set α → (α → β → Prop) → Prop := graph dom

/-- **✱33·02 Df.** \(\text{ᗡ}=\hat{\beta}\hat{R}[\hat{\beta}=\hat{y}\{(\exists x).xRy\}] \quad\text{Df}\)

(The e-text prints \(\hat{\beta}=\) for \(\beta=\) in the definiens.) The relation `ᗡ` of the
converse domain of `R` to `R`. `ᗡ'R` is `codom R`. Target:
`pm33_02 : (Dcnv : Set β → (α → β → Prop) → Prop) = fun B R => B = {y | ∃ x, R x y} := rfl`. -/
def Dcnv : Set β → (α → β → Prop) → Prop := graph codom

/-- **✱33·03 Df.** \(C=\hat{\gamma}\hat{R}[\gamma=\hat{x}\{(\exists y):xRy.\lor .yRx\}] \quad\text{Df}\)

The relation `C` of the field of `R` to `R` (homogeneous `R`). `C'R` is `fld R`. Target:
`pm33_03 : (C : Set α → (α → α → Prop) → Prop) = fun G R => G = {x | ∃ y, R x y ∨ R y x} :=
rfl`. -/
def C : Set α → (α → α → Prop) → Prop := graph fld

/-- **✱33·04 Df.** \(F=\hat{x}\hat{R}\{(\exists y):xRy.\lor .yRx\} \quad\text{Df}\)

The relation of a member of the field of `R` to `R`. Target:
`pm33_04 : (F : α → (α → α → Prop) → Prop) = fun x R => ∃ y, R x y ∨ R y x := rfl`. -/
def F : α → (α → α → Prop) → Prop := fun x R => ∃ y, R x y ∨ R y x

/-- **✱34·01 Df.** \( R\mid S=\hat{x}\hat{z}\{(\exists y).xRy.ySz\} \quad\text{Df}\)

The relative product `R | S`, notation `R ⨾ S` (Lean's `|` is reserved). Target:
`pm34_01 : R ⨾ S = fun x z => ∃ y, R x y ∧ S y z := rfl`. -/
def relProd (R : α → β → Prop) (S : β → γ → Prop) : α → γ → Prop := fun x z => ∃ y, R x y ∧ S y z

@[inherit_doc] scoped infixl:70 " ⨾ " => relProd

/-- **✱34·02 Df.** \(R^{2}=R\mid R \quad\text{Df}\)

Target: `pm34_02 : rsq R = R ⨾ R := rfl`. -/
def rsq (R : α → α → Prop) : α → α → Prop := R ⨾ R

/-- **✱34·03 Df.** \(R^{3}=R^{2}\mid R \quad\text{Df}\)

Target: `pm34_03 : rcube R = rsq R ⨾ R := rfl`. -/
def rcube (R : α → α → Prop) : α → α → Prop := rsq R ⨾ R

/-!
**✱34·22 Df.** \(P\mid Q\mid R=(P\mid Q)\mid R \quad\text{Df}\)

`⨾` is left-associative. Target (status `definition`): `pm34_22 : P ⨾ Q ⨾ R = (P ⨾ Q) ⨾ R := rfl`.
-/

/-- **✱35·01 Df.** \(\alpha\upharpoonleft R=\hat{x}\hat{y}(x\in \alpha.xRy) \quad\text{Df}\)

`R` with domain limited to `α`, `α ↿ R`, notation `A ◁ R`. Target:
`pm35_01 : A ◁ R = fun x y => x ∈ A ∧ R x y := rfl`. -/
def dres (A : Set α) (R : α → β → Prop) : α → β → Prop := fun x y => x ∈ A ∧ R x y

@[inherit_doc] scoped infixr:75 " ◁ " => dres

/-- **✱35·02 Df.** \(R\upharpoonright \beta=\hat{x}\hat{y}(xRy.y\in \beta) \quad\text{Df}\)

`R` with converse domain limited to `β`, `R ↾ β`, notation `R ↾ B`. Target:
`pm35_02 : R ↾ B = fun x y => R x y ∧ y ∈ B := rfl`. -/
def cres (R : α → β → Prop) (B : Set β) : α → β → Prop := fun x y => R x y ∧ y ∈ B

@[inherit_doc] scoped infixl:68 " ↾ " => cres

/-- **✱35·03 Df.** \(\alpha\upharpoonleft R\upharpoonright \beta=\hat{x}\hat{y}(x\in \alpha.xRy.y\in \beta)\quad\text{Df}\)

The definiens is a product of three, bracketed `(x ∈ α . xRy) . y ∈ β` (✱4·34). With the
precedences above, `A ◁ R ↾ B` parses as `(A ◁ R) ↾ B`, which is `bres A R B` by `rfl`. Target:
`pm35_03 : bres A R B = fun x y => (x ∈ A ∧ R x y) ∧ y ∈ B := rfl`. -/
def bres (A : Set α) (R : α → β → Prop) (B : Set β) : α → β → Prop :=
  fun x y => (x ∈ A ∧ R x y) ∧ y ∈ B

/-- **✱35·04 Df.** \(\alpha\uparrow \beta=\hat{x}\hat{y}(x\in \alpha.y\in \beta) \quad\text{Df}\)

The relation `α ↑ β` of every member of `α` to every member of `β` (Lean's `↑` is the coercion
arrow, so it is the name `cross`). Target: `pm35_04 : cross A B = fun x y => x ∈ A ∧ y ∈ B :=
rfl`. -/
def cross (A : Set α) (B : Set β) : α → β → Prop := fun x y => x ∈ A ∧ y ∈ B

/-!
**✱35·05 Df.** \(Rʻx\uparrow \beta=(Rʻx)\uparrow \beta \quad\text{Df}\)

Bracketing convention: `R'x ↑ β` is `(R'x) ↑ β`, the description `R'x` (a class) taken as the
first argument of `↑`; with descriptions, `ψ(R'x ↑ β)` is `Desc R x (fun A => ψ (cross A B))`.
Target (status `definition`): `pm35_05 : Desc R x (fun A => ψ (cross A B)) ↔
TheIs (fun A => R A x) (fun A => ψ (cross A B)) := Iff.rfl`, with `R : Set α → γ → Prop`.

**✱35·24 Df.** \(\alpha\upharpoonleft R\mid S=(\alpha\upharpoonleft R)\mid S \quad\text{Df}\)

**✱35·25 Df.** \(S\mid R\upharpoonright \beta=(S\mid R)\upharpoonright \beta \quad\text{Df}\)

**✱35·27 Df.** \(\alpha\upharpoonleft R\mid S\upharpoonright \beta=(\alpha\upharpoonleft R\mid S)\upharpoonright \beta \quad\text{Df}\)

Bracketing conventions, realized by the precedences `◁` (75) > `⨾` (70) > `↾`, `⥏` (68). Targets
(status `definition`): `pm35_24 : A ◁ R ⨾ S = (A ◁ R) ⨾ S := rfl`;
`pm35_25 : S ⨾ R ↾ B = (S ⨾ R) ↾ B := rfl`; `pm35_27 : A ◁ R ⨾ S ↾ B = ((A ◁ R) ⨾ S) ↾ B := rfl`.

PM's practice (no Df) also makes `↿`, `↾`, `⥏` bind tighter than `∩̇`, `∪̇`, `−̇`: ✱35·17
`R ∩̇ S ↾ β` is `R ⩀ (S ↾ B)`, ✱35·412 `R ↾ β ∪̇ R ↾ β'` is `(R ↾ B) ⊍ (R ↾ B')`, ✱36·2
`P ⥏ α ∩̇ Q ⥏ β` is `(P ⥏ A) ⩀ (Q ⥏ B)`; and `|` binds tighter than `∪̇`, `−̇` (✱34·62, ✱172·161).
Hence `⩀` is 67 and `⊍`, binary `∸` are 65, so that these formulas parse as PM means them.
-/

/-- **✱36·01 Df.** \(P \unicode{x294f} \alpha = \alpha \upharpoonleft P \upharpoonright \alpha \quad \text{Df}\)

`P` with field limited to `α`, `P ⥏ α`, notation `P ⥏ A`. Target:
`pm36_01 : P ⥏ A = A ◁ P ↾ A := rfl`. -/
def fres (P : α → α → Prop) (A : Set α) : α → α → Prop := bres A P A

@[inherit_doc] scoped infixl:68 " ⥏ " => fres

/-- **✱37·01 Df.** \(Rʻʻ\beta=\hat{x}\{(\exists y).y\in \beta.xRy\} \quad\text{Df}\)

The plural descriptive function `R''β` (the referents of members of `β`), notation `R ʻʻ B`
(U+02BB twice; mathlib's `''` is `Set.image`, a different thing). Target:
`pm37_01 : R ʻʻ B = {x | ∃ y, y ∈ B ∧ R x y} := rfl`. -/
def img (R : α → β → Prop) (B : Set β) : Set α := {x | ∃ y, y ∈ B ∧ R x y}

@[inherit_doc] scoped infixr:80 " ʻʻ " => img

/-- **✱37·02 Df.** \(R_{\in}=\hat{\alpha}\hat{\beta}(\alpha=Rʻʻ\beta) \quad\text{Df}\)

The relation `R_∈` of `R''β` to `β`; `R_∈'β` is `R ʻʻ β`. Target:
`pm37_02 : imgRel R = fun A B => A = R ʻʻ B := rfl`. -/
def imgRel (R : α → β → Prop) : Set α → Set β → Prop := graph (img R)

/-- **✱37·03 Df.** \(\breve{R}_{\in}=\text{Cnv}ʻR_{\in} \quad\text{Df}\)

`R̆_∈` is the converse of `R_∈`. The definiens is the descriptive function `Cnv'R_∈`, so the
target keeps the description (Basic §5): `pm37_03 : Desc Cnv (imgRel R) (fun Q => imgRelCnv R = Q)
:= (desc_Cnv _ _).2 rfl` (status `definition`); `imgRelCnv R = (imgRel R)˘` holds by `rfl`. -/
def imgRelCnv (R : α → β → Prop) : Set β → Set α → Prop := (imgRel R)˘

/-- **✱37·04 Df.** \(Rʻʻʻ\kappa=R_{\in}ʻʻ\kappa \quad\text{Df}\)

`R'''κ`, the class of the classes `R''β` for `β ∈ κ`, notation `R ʻʻʻ K`. Target:
`pm37_04 : R ʻʻʻ K = imgRel R ʻʻ K := rfl`. -/
def img3 (R : α → β → Prop) (K : Set (Set β)) : Set (Set α) := imgRel R ʻʻ K

@[inherit_doc] scoped infixr:80 " ʻʻʻ " => img3

/-- **✱37·05 Df.** \(\text{E}‼Rʻʻ\beta.=:y\in \beta.\supset_{y}.\text{E}!Rʻy \quad\text{Df}\)

`E!! R''β`: `R'y` exists for every member `y` of `β`. Target:
`pm37_05 : EE R B ↔ ∀ y, y ∈ B → EDesc R y := Iff.rfl`. -/
def EE (R : α → β → Prop) (B : Set β) : Prop := ∀ y, y ∈ B → EDesc R y

/-- **✱37·371 Df.** \(R_{\in}^{2}=(R_{\in})^{2} \quad\text{Df}\)

Bracketing convention: the square of `R_∈` (for homogeneous `R`). Target:
`pm37_371 : imgRelSq R = rsq (imgRel R) := rfl`. -/
def imgRelSq (R : α → α → Prop) : Set α → Set α → Prop := rsq (imgRel R)

/-- **✱38·01 Df.** \(x\unicode{x2640} =\hat{u}\hat{y}(u=x\unicode{x2640} y)\quad \text{Df}\)

PM's `♀` is any double descriptive function with `(x, y) . E!(x♀y)` (e.g. `∩`, `∪`, `⩀`, `⊍`,
`⨾`, `◁`, `↾`, `⥏`); in Lean it is a function `f : α → β → γ`, and `x♀y` is `f x y`. `x♀` is the
relation of `x♀y` to `y`: `opL f x`; `(x♀)'y` is `f x y` (`desc_graph`). Target:
`pm38_01 : opL f x = fun u y => u = f x y := rfl`. -/
def opL (f : α → β → γ) (x : α) : γ → β → Prop := graph (f x)

/-- **✱38·02 Df.** \(\unicode{x2640} y=\hat{u}\hat{x}(u=x\unicode{x2640} y)\quad \text{Df}\)

`♀y` is the relation of `x♀y` to `x`: `opR f y`. Target:
`pm38_02 : opR f y = fun u x => u = f x y := rfl`. -/
def opR (f : α → β → γ) (y : β) : γ → α → Prop := graph (fun x => f x y)

/-- **✱38·03 Df.** \(\alpha \unicode{x2640}_{,,}y=\unicode{x2640} yʻʻ\alpha\quad \text{Df}\)

`α ♀,, y`, the class of the values `x♀y` for `x ∈ α`. Target:
`pm38_03 : opImg f A y = opR f y ʻʻ A := rfl`. -/
def opImg (f : α → β → γ) (A : Set α) (y : β) : Set γ := opR f y ʻʻ A

/-- `R |` (✱38·01 with `♀ = |`): the relation of `R ⨾ S` to `S` (✱43·1). Not a separate Df. -/
def relProdL (R : α → β → Prop) : (α → γ → Prop) → (β → γ → Prop) → Prop :=
  opL (relProd (γ := γ)) R

/-- `| S` (✱38·02 with `♀ = |`): the relation of `Q ⨾ S` to `Q` (✱43·101). Not a separate Df. -/
def relProdR (S : β → γ → Prop) : (α → γ → Prop) → (α → β → Prop) → Prop :=
  opR (relProd (α := α)) S

/-! ## Section E: products and sums of classes (✱40–✱43) -/

/-- **✱40·01 Df.** \(pʻ\kappa = \hat{x} (\alpha\in\kappa . \supset_{\alpha} . x\in\alpha) \quad\text{Df}\)

The product (common part) of a class of classes, `p'κ`; it is `⋂₀ K` (`prodCls_eq_sInter`). PM
defines `p'κ` directly (no relation `p`), so it is a term. Target:
`pm40_01 : prodCls K = {x | ∀ A, A ∈ K → x ∈ A} := rfl`. -/
def prodCls (K : Set (Set α)) : Set α := {x | ∀ A, A ∈ K → x ∈ A}

/-- **✱40·02 Df.** \(sʻ\kappa = \hat{x} {(\exists\alpha) . \alpha\in\kappa . x\in\alpha} \quad\text{Df}\)

The sum of a class of classes, `s'κ`; it is `⋃₀ K` (`sumCls_eq_sUnion`). (The e-text drops the
braces of the definiens.) Target: `pm40_02 : sumCls K = {x | ∃ A, A ∈ K ∧ x ∈ A} := rfl`. -/
def sumCls (K : Set (Set α)) : Set α := {x | ∃ A, A ∈ K ∧ x ∈ A}

/-- **✱41·01 Df.** \(\dot{p}ʻ\lambda = \hat{x}\hat{y}(R \in \lambda .\supset_{R}. xRy) \quad \text{Df}\)

The product of a class of relations, `ṗ'λ`. Target:
`pm41_01 : prodRel L = fun x y => ∀ R, R ∈ L → R x y := rfl`. -/
def prodRel (L : Set (α → β → Prop)) : α → β → Prop := fun x y => ∀ R, R ∈ L → R x y

/-- **✱41·02 Df.** \(\dot{s}ʻ\lambda = \hat{x}\hat{y}\{(\exists R) . R \in \lambda . xRy\} \quad \text{Df}\)

The sum of a class of relations, `ṡ'λ`. Target:
`pm41_02 : sumRel L = fun x y => ∃ R, R ∈ L ∧ R x y := rfl`. -/
def sumRel (L : Set (α → β → Prop)) : α → β → Prop := fun x y => ∃ R, R ∈ L ∧ R x y

/-- **✱43·01 Df.** \(R \parallel S = (R \mid) \mid (\mid S) \quad \text{Df}\)

`R ‖ S`, the relation of `R | Q | S` to `Q`, notation `R ∥ S`. Target:
`pm43_01 : R ∥ S = relProdL R ⨾ relProdR S := rfl`. -/
def dpar (R : α → β → Prop) (S : γ → δ → Prop) : (α → δ → Prop) → (β → γ → Prop) → Prop :=
  relProdL R ⨾ relProdR S

@[inherit_doc] scoped infixl:70 " ∥ " => dpar

/-! ## Sanity lemmas: the encodings behave -/

section Sanity

/-- PM's identity (✱13·01) is Lean's `Eq` (cf. ✱13·1, ✱13·12). -/
theorem PMIdent_iff_eq {x y : α} : PMIdent x y ↔ x = y :=
  ⟨fun h => h (fun z => x = z) rfl, fun h _ hx => h ▸ hx⟩

/-- PM's `E!(℩x)(φx)` is Lean's `∃! x, φ x`. -/
theorem EBang_iff_existsUnique {φ : α → Prop} : EBang φ ↔ ∃! x, φ x := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, (hb b).2 rfl, fun x hx => (hb x).1 hx⟩
  · rintro ⟨b, hb, hu⟩
    exact ⟨b, fun x => ⟨hu x, fun h => h ▸ hb⟩⟩

/-- `ψ(℩x)(φx)` holds iff the description exists and everything satisfying `φ` satisfies `ψ`. -/
theorem TheIs_iff {φ ψ : α → Prop} : TheIs φ ψ ↔ EBang φ ∧ ∀ x, φ x → ψ x := by
  constructor
  · rintro ⟨b, hb, hψ⟩
    exact ⟨⟨b, hb⟩, fun x hx => ((hb x).1 hx) ▸ hψ⟩
  · rintro ⟨⟨b, hb⟩, h⟩
    exact ⟨b, hb, h b ((hb b).2 rfl)⟩

/-- `TheIs` in terms of Lean's `∃!`. -/
theorem TheIs_iff_existsUnique {φ ψ : α → Prop} :
    TheIs φ ψ ↔ (∃! x, φ x) ∧ ∀ x, φ x → ψ x := by
  rw [TheIs_iff, EBang_iff_existsUnique]

/-- If `φ` is satisfied by `b` and by nothing else, `ψ(℩x)(φx)` is `ψ b` (cf. ✱14·18, ✱14·202). -/
theorem TheIs_iff_of_unique {φ ψ : α → Prop} {b : α} (h : ∀ x, φ x ↔ x = b) :
    TheIs φ ψ ↔ ψ b := by
  constructor
  · rintro ⟨c, hc, hψ⟩
    have : c = b := (h c).1 ((hc c).2 rfl)
    exact this ▸ hψ
  · exact fun hψ => ⟨b, h, hψ⟩

/-- The descriptive function of `graph f` always exists. -/
theorem EDesc_graph (f : β → α) (y : β) : EDesc (graph f) y := ⟨f y, fun _ => Iff.rfl⟩

/-- The descriptive function of `graph f` is `f`: `ψ((graph f)'y) ↔ ψ (f y)`. This justifies
writing `D'R` as `dom R`, `Cnv'P` as `cnv P`, `R⃗'y` as `refs R y`, etc. (Basic §5). -/
theorem desc_graph (f : β → α) (y : β) (ψ : α → Prop) : Desc (graph f) y ψ ↔ ψ (f y) :=
  TheIs_iff_of_unique (fun _ => Iff.rfl)

/-- `ψ(R'S'y)` eliminates the inner description first (✱30·02 and PM's explanation). -/
theorem desc2_iff (R : α → β → Prop) (S : β → γ → Prop) (y : γ) (ψ : α → Prop) :
    Desc2 R S y ψ ↔ Desc S y (fun z => Desc R z ψ) := by
  constructor
  · rintro ⟨b, hb, hψ⟩
    obtain ⟨c, hc, hRbc⟩ := (hb b).2 rfl
    refine ⟨c, hc, b, fun x => ⟨fun hx => (hb x).1 ⟨c, hc, hx⟩, fun hx => hx ▸ hRbc⟩, hψ⟩
  · rintro ⟨c, hc, b, hb, hψ⟩
    refine ⟨b, fun x => ?_, hψ⟩
    constructor
    · rintro ⟨c', hc', hx'⟩
      have : c' = c := (hc c').1 ((hc' c').2 rfl)
      exact (hb x).1 (this ▸ hx')
    · intro hx
      exact ⟨c, hc, (hb x).2 hx⟩

/-- The relation `ûx̂(u = S'x)` (Summary of Section E): when PM defines a descriptive
function by `R'x = S'x . Df` (or by any definiens containing a description that may fail to exist,
e.g. ✱121·04 `ν_P`), the relation `R` is "tacitly assumed to be defined" as `ûx̂(u = S'x)`, i.e.
`descRel S`, and `desc_descRel` shows `R'x` is then `S'x` in every context. Not itself a PM Df. -/
def descRel (S : α → β → Prop) : α → β → Prop := fun u x => Desc S x (fun v => u = v)

/-- `(ûx̂(u = S'x))'x` is `S'x`, with any scope. -/
theorem desc_descRel (S : α → β → Prop) (x : β) (ψ : α → Prop) :
    Desc (descRel S) x ψ ↔ Desc S x ψ := by
  constructor
  · rintro ⟨b, hb, hψ⟩
    obtain ⟨c, hc, rfl⟩ := (hb b).2 rfl
    exact ⟨b, hc, hψ⟩
  · rintro ⟨b, hb, hψ⟩
    refine ⟨b, fun u => ⟨?_, fun h => ⟨b, hb, h⟩⟩, hψ⟩
    rintro ⟨c, hc, rfl⟩
    exact (hb u).1 ((hc u).2 rfl)

/-- `Cnv` holds exactly of the converse. -/
theorem Cnv_iff {Q : β → α → Prop} {P : α → β → Prop} : Cnv Q P ↔ Q = P˘ := by
  constructor
  · intro h; funext x y; exact propext (h x y)
  · rintro rfl x y; exact Iff.rfl

/-- `Cnv'P` is `P˘`. -/
theorem desc_Cnv (P : α → β → Prop) (ψ : (β → α → Prop) → Prop) : Desc Cnv P ψ ↔ ψ P˘ :=
  TheIs_iff_of_unique (fun _ => Cnv_iff)

theorem cnv_cnv (P : α → β → Prop) : P˘˘ = P := rfl

/-- Extensionality of classes, PM's ✱20·43 `α = β . ≡ : x ∈ α . ≡_x . x ∈ β`. -/
theorem set_eq_iff {A B : Set α} : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B := Set.ext_iff

/-- PM's ✱20·15: formally equivalent functions determine the same class. -/
theorem setOf_eq_setOf_iff {φ ψ : α → Prop} : {z | φ z} = {z | ψ z} ↔ ∀ x, φ x ↔ ψ x := by
  simp [Set.ext_iff]

/-- Extensionality of relations, PM's ✱21·43 `R = S . ≡ : xRy . ≡_{x,y} . xSy`. -/
theorem rel_eq_iff {R S : α → β → Prop} : R = S ↔ ∀ x y, R x y ↔ S x y :=
  ⟨fun h _ _ => h ▸ Iff.rfl, fun h => funext fun x => funext fun y => propext (h x y)⟩

/-- The axiom of reducibility ✱12·1 is provable: every function is predicative. -/
theorem reducibility (φ : α → Prop) : ∃ f : α → Prop, ∀ x, φ x ↔ f x := ⟨φ, fun _ => Iff.rfl⟩

/-- The axiom of reducibility ✱12·11 for two variables. -/
theorem reducibility₂ (φ : α → β → Prop) : ∃ f : α → β → Prop, ∀ x y, φ x y ↔ f x y :=
  ⟨φ, fun _ _ => Iff.rfl⟩

theorem Cls_eq_univ : (Cls : Set (Set α)) = Set.univ :=
  Set.eq_univ_of_forall fun A => ⟨fun z => z ∈ A, rfl⟩

theorem Rel_eq_univ : (Rel : Set (α → β → Prop)) = Set.univ :=
  Set.eq_univ_of_forall fun R => ⟨R, rfl⟩

theorem V_eq_univ : (V : Set α) = Set.univ := Set.eq_univ_of_forall fun _ => rfl

theorem Null_eq_empty : (Λ : Set α) = ∅ := by
  ext x; simp [Null, V]

theorem rNull_apply (x : α) (y : β) : ¬ rNull x y := fun h => h ⟨rfl, rfl⟩

theorem prodCls_eq_sInter (K : Set (Set α)) : prodCls K = ⋂₀ K := by
  ext x; simp [prodCls]

theorem sumCls_eq_sUnion (K : Set (Set α)) : sumCls K = ⋃₀ K := by
  ext x; simp [sumCls]

/-- The precedences realize PM's bracketing Dfs ✱35·03, ✱35·24·25·27 and ✱36·01. -/
example (A : Set α) (B : Set β) (R : α → β → Prop) (S : β → γ → Prop) (T : γ → δ → Prop)
    (E : Set δ) :
    (A ◁ R ↾ B = bres A R B) ∧ (A ◁ R ⨾ S = (A ◁ R) ⨾ S) ∧ (R ⨾ S ↾ (∅ : Set γ) = (R ⨾ S) ↾ ∅) ∧
    (A ◁ R ⨾ S ⨾ T ↾ E = ((A ◁ R) ⨾ S ⨾ T) ↾ E) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The precedences realize PM's unbracketed formulas ✱35·17, ✱35·18, ✱35·41, ✱35·412, ✱36·2,
✱34·62, ✱73·69, ✱172·161. -/
example (A A' : Set α) (B B' : Set β) (R S : α → β → Prop) (P Q : α → α → Prop) (C D : Set α) :
    (R ⩀ S ↾ B = R ⩀ (S ↾ B)) ∧ (R ⩀ A ◁ S ↾ B = R ⩀ ((A ◁ S) ↾ B)) ∧
    (A ◁ R ⊍ A' ◁ R = (A ◁ R) ⊍ (A' ◁ R)) ∧ (R ↾ B ⊍ R ↾ B' = (R ↾ B) ⊍ (R ↾ B')) ∧
    (P ⥏ C ⩀ Q ⥏ D = (P ⥏ C) ⩀ (Q ⥏ D)) ∧
    (rsq P ⊍ P ⨾ Q ⊍ Q ⨾ P ⊍ rsq Q = ((rsq P ⊍ (P ⨾ Q)) ⊍ (Q ⨾ P)) ⊍ rsq Q) ∧
    (P ⊍ Q ↾ C = P ⊍ (Q ↾ C)) ∧ (P ∸ Q ⨾ P = P ∸ (Q ⨾ P)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example (R S T : α → β → Prop) : R ∸ S ⩀ T = R ∸ (S ⩀ T) ∧ ∸R ⩀ S = (∸R) ⩀ S ∧ R ⩀ ∸S = rdiff R S :=
  ⟨rfl, rfl, rfl⟩

/-- `P (R ‖ S) Q` iff `P = R | (Q | S)` (cf. ✱43·102). -/
theorem dpar_iff (R : α → β → Prop) (S : γ → δ → Prop) (P : α → δ → Prop) (Q : β → γ → Prop) :
    (R ∥ S) P Q ↔ P = R ⨾ (Q ⨾ S) := by
  constructor
  · rintro ⟨M, hM, hQ⟩
    exact hM.trans (congrArg (relProd R) hQ)
  · intro h
    exact ⟨Q ⨾ S, h, rfl⟩

end Sanity

end PrincipiaMathematica
