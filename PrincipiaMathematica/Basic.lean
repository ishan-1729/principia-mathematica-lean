import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Tactic.Common
import Mathlib.Tactic.Tauto

/-!
# *Principia Mathematica* in Lean: conventions

This project formalizes A. N. Whitehead and B. Russell, *Principia Mathematica*, Volume I (1910)
and Volume II (1912) (Project Gutenberg #78050 and #78255; public domain in the US), proposition
by proposition; Volume III will be added later. The text, with every starred number ✱N and every
proposition ✱N·M (formula as printed, demonstration and comments), is in `data/principia.json`.

This file fixes *how PM is read in Lean*. Every other file builds on it:
`PrincipiaMathematica/Defs/PartN.lean` gives every definition (Df) of Part N as a Lean definition
or as a translation rule, and `PrincipiaMathematica/PartN/SectionX.lean` states and proves the
propositions. Section files import only `Defs/PartN`. Part I, ✱1, in `Part1/SectionA.lean` is
the worked example of the house style.

## 1. The logic of ✱1–✱5 (Part I, Section A)

PM's primitive ideas are `∼p` and `p ∨ q` (and the assertion-sign ⊢); `⊃`, `.` and `≡` are
defined. In Lean all of them are read as Lean's own connectives on `Prop`:

| PM                 | Lean          | PM's definition, which becomes a theorem               |
|--------------------|---------------|--------------------------------------------------------|
| `∼p`               | `¬p`          | primitive                                              |
| `p ∨ q`            | `p ∨ q`       | primitive                                              |
| `p ⊃ q`            | `p → q`       | ✱1·01 `p ⊃ q . = . ∼p ∨ q`: `(p → q) ↔ ¬p ∨ q`          |
| `p . q`            | `p ∧ q`       | ✱3·01 `p . q . = . ∼(∼p ∨ ∼q)`: `p ∧ q ↔ ¬(¬p ∨ ¬q)`    |
| `p ≡ q`            | `p ↔ q`       | ✱4·01 `p ≡ q . = . p ⊃ q . q ⊃ p`: `(p ↔ q) ↔ (p → q) ∧ (q → p)` |
| `⊢ . p`            | `theorem … : p` | the assertion-sign = "this Lean statement is a theorem" |

These three Dfs are not Lean definitions: the declarations `pm1_01`, `pm3_01`, `pm4_01` state the
equivalence of Lean's connective with PM's definiens (classical logic) and carry the status
`proved (reading)`. Lean's logic is classical here (`Classical.em` etc. are allowed; the axiom
audit admits `propext`, `Classical.choice`, `Quot.sound`).

*Elementary propositions.* In Section A PM's variables `p, q, r` range over *elementary*
propositions (no apparent variables), and ✱9 extends the results to propositions of every order.
Lean's `Prop` is one impredicative type of all propositions, so the restriction disappears and the
propositions of ✱1–✱5 are stated for arbitrary `p q r : Prop`.

*Meta-level primitive propositions.* ✱1·1 (anything implied by a true elementary proposition is
true) and ✱1·11 (the same for asserted propositional functions) are rules of inference, which PM
says cannot be expressed in its symbolism; in Lean they are application of a proof of `p → q` to a
proof of `p`. They are recorded as the derivable rules (`pm1_1 : p → (p → q) → q`, …) with status
`proved (reading)`. ✱1·7, ✱1·71, ✱1·72 (that `∼p`, `p ∨ q`, `φp ∨ ψp` are elementary, and
identification of real variables) are typing facts (`Not : Prop → Prop`, …): status `remark`.
The meta-level primitive propositions of ✱9 and ✱11 are treated the same way: ✱9·12 (inference)
and ✱9·13 (a real variable may be turned into an apparent one: `(∀ x, φ x)` from a proof for an
arbitrary `x`) are `proved (reading)` as derivable rules; ✱9·15 (a proposition `φa` gives a
function `φx̂`, and vice versa) and ✱11·07 (interchange of apparent variables) are `remark` or
`proved (reading)` by their Lean counterparts (`fun x => φ x`; `forall_comm`). ✱9·1 and ✱9·11 are
ordinary theorems. See `Part1/SectionA.lean`, ✱1.

## 2. Dots: how to bracket a PM formula

PM uses dots on the line both as brackets and as the sign of logical product (Introduction, Ch. I,
pp. 9–10). Read the dots *first*: they give the structure.

* *Groups.* Dots adjoining `⊃`, `≡`, `∨`, or `= Df` are Group I (strongest); dots after an
  apparent-variable prefix `(x)`, `(x, y)`, `(∃x)`, `[(℩x)(φx)]`, `[R'y]` are Group II; dots between
  propositions that mark a logical product are Group III (weakest). `.` is one dot, `:` two,
  `:.` (written `\colon\ldotp` in the TeX) three, `::` four.
* *Scope.* A bracket indicated by a collection of dots extends (backwards or forwards) past any
  smaller number of dots, and past an equal number of a weaker group, and stops at a larger
  number of dots, at an equal number of an equal or stronger group, or at the end of the asserted
  proposition. Product dots work both ways; dots at `⊃ ≡ ∨` work away from the sign; dots after a
  quantifier prefix work forwards. The `⊃`/`≡` with the most dots is the principal connective.
* *Undotted signs bind tightest.* `∼` applies to the smallest following proposition: `∼p ∨ q` is
  `¬p ∨ q`; `∼(x).φx` is `¬ ∀ x, φ x` (✱9·011). Relational signs (`x = y`, `x ∈ α`, `xRy`, `α ⊂ β`)
  bind tighter than any connective. PM does not mix undotted `∨`, `⊃`, `≡`, except in the chain
  conventions below.
* *Chains (Dfs).* `p ∨ q ∨ r` is `(p ∨ q) ∨ r` (✱2·33); `p . q . r` is `(p ∧ q) ∧ r` (✱4·34);
  `p ⊃ q ⊃ r` is `(p → q) ∧ (q → r)` (✱3·02), **not** `p → q → r`; `p ≡ q ≡ r` is
  `(p ↔ q) ∧ (q ↔ r)` (✱4·02); `x = y = z` is `x = y ∧ y = z` (✱13·03); the same for `⊂`, `=` and
  `≡` chains of classes and relations, and for chains separated by dots, e.g. ✱14·202
  `A :≡: B :≡: C :≡: D` is `((A ↔ B) ∧ (B ↔ C)) ∧ (C ↔ D)`. Lean's `∨`, `∧` associate to the
  right, so write PM's flat products and sums (and the conjunctions of chain links) with the
  explicit left parentheses `(p ∧ q) ∧ r`, `(p ∨ q) ∨ r` (✱2·33, ✱4·34; as in Defs).
* *Brackets PM leaves to the types.* PM occasionally omits brackets where only one reading is
  significant (e.g. ✱50·61 `I ↾ α | R` is `(I ↾ α) | R`, since `α | R` is meaningless). Lean
  parses by precedence, not by type: write the brackets. Likewise the converse of a compound term
  needs brackets, `(imgRel R)˘` (`imgRel R˘` is `imgRel (R˘)`).
* *Hypothesis.* In a formula `A . ⊃ . B` (or with more dots) the principal `⊃` becomes `→`; when the
  antecedent is a product `p . q . ⊃ . r` it becomes `p ∧ q → r` (keep the conjunction: do *not*
  curry it into `p → q → r` in the statement).

Worked examples (from the Introduction and ✱1–✱14):

| PM                                                   | Lean                                              |
|------------------------------------------------------|---------------------------------------------------|
| `⊢ : p ∨ q . ⊃ . q ∨ p`                              | `p ∨ q → q ∨ p`                                   |
| `p : ∨ : q . ⊃ . q ∨ p`                              | `p ∨ (q → q ∨ p)`                                 |
| `p ∨ q . ⊃ . q : ∨ : p`                              | `(p ∨ q → q) ∨ p`                                 |
| `⊢ :. p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r`                 | `(p → q) → ((q → r) → (p → r))`                   |
| `p ⊃ q . ⊃ . q ⊃ r : ⊃ . p ⊃ r`                      | `((p → q) → (q → r)) → (p → r)`                   |
| `p ⊃ q . q ⊃ r . ⊃ . p ⊃ r`                          | `(p → q) ∧ (q → r) → (p → r)`                     |
| `p ⊃ q : q ⊃ r . ⊃ . p ⊃ r`                          | `(p → q) ∧ ((q → r) → (p → r))`                   |
| `⊢ :: p ∨ q . ⊃ :. p . ∨ . q ⊃ r : ⊃ . p ∨ r` (✱2·75) | `p ∨ q → ((p ∨ (q → r)) → p ∨ r)`                |
| `⊢ :. p ∨ q : p . ∨ . q ⊃ r : ⊃ . p ∨ r`             | `(p ∨ q) ∧ (p ∨ (q → r)) → p ∨ r`                 |
| `⊢ :. p . ⊃ . q ⊃ r : ⊃ : q . ⊃ . p ⊃ r` (✱2·04)     | `(p → (q → r)) → (q → (p → r))`                   |
| `⊢ : p ⊃ q . ⊃ . ∼q ⊃ ∼p` (✱2·16)                    | `(p → q) → (¬q → ¬p)`                             |
| `(x) : φx . ⊃ . ψx`                                  | `∀ x, φ x → ψ x`                                  |
| `(x) . φx . ψx` (product dot is weaker than Group II) | `∀ x, φ x ∧ ψ x`                                 |
| `⊢ : ψ(℩x)(φx) . ≡ . (∃b) . b = (℩x)(φx) . ψb` (✱14·205) | `TheIs φ ψ ↔ ∃ b, TheIs φ (fun c => b = c) ∧ ψ b` |
| `(x) . φx . ⊃ . ψx` (`x` in `ψx` real)               | `(∀ x, φ x) → ψ x`                                |
| `⊢ : (x) . φx . ⊃ . (∃x) . φx` (✱10·25)               | `(∀ x, φ x) → ∃ x, φ x` (with `[Nonempty α]`, §3) |
| `φx . ⊃_x . ψx` (✱10·02)                             | `∀ x, φ x → ψ x`                                  |
| `⊢ :. φx . ⊃_x . ψx : ⊃ : (x) . φx . ⊃ . (x) . ψx`   | `(∀ x, φ x → ψ x) → ((∀ x, φ x) → ∀ x, ψ x)`      |
| `⊢ : x = y . y = z . ⊃ . x = z`                      | `x = y ∧ y = z → x = z`                           |
| `⊢ :. ψ(℩x)(φx) . ≡ : (∃b) : φx . ≡_x . x = b : ψb`  | `TheIs φ ψ ↔ ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b`       |
| `⊢ : x ∈ α ∩ β . ≡ . x ∈ α . x ∈ β`                  | `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`                       |

A letter not bound by any prefix (the `x` of `ψx` in `(x) . φx . ⊃ . ψx`) is a *real* variable,
i.e. an argument of the theorem (§3).

## 3. Apparent and real variables (✱9–✱11)

* `(x) . φx` is `∀ x, φ x`; `(∃x) . φx` is `∃ x, φ x`; `(x, y) . φ(x, y)` is `∀ x y, φ x y`
  (= `∀ x, ∀ y, …`, ✱11·01); `(∃x, y)` is `∃ x y, …`. The scope of the prefix is given by its dots.
* Formal implication and equivalence: `φx . ⊃_x . ψx` is `∀ x, φ x → ψ x` (✱10·02),
  `φx . ≡_x . ψx` is `∀ x, φ x ↔ ψ x` (✱10·03), `⊃_{x,y}`, `≡_{x,y}` likewise (✱11·05·06).
  Write the `∀` directly; `FImp`, `FEqv`, … in Defs only name the Dfs.
* A *real variable* (a free letter of an asserted formula, "ambiguous assertion") is an argument
  of the theorem, by default implicit (`{p q : Prop}`, `{x : α}`, `{φ : α → Prop}`), explicit when
  it cannot be inferred from the statement. Its type is a type variable (see §4), bound as
  `{α : Type*}` (or with a `universe` and `variable` line in the Section file).
* ✱9's negation, disjunction and implication of quantified propositions are *defined* in PM
  (✱9·01–✱9·08); Lean's connectives apply to all propositions, so these Dfs become theorems
  (status `proved (reading)` unless they hold by `Iff.rfl`).
* *Something exists.* PM's logic assumes that every type has a member ("what holds of all, holds
  of any", Introduction, Ch. I, "Propositions connecting real and apparent variables"; ✱9·1 with
  a real variable `x`; ✱10·25 `(x).φx ⊃ (∃x).φx`). Lean
  types may be empty. Where (and only where) a proposition is false for an empty type, add the
  instance hypothesis `[Nonempty α]` for that type and give the status
  `proved (reading): PM assumes every type has a member (Introduction, Ch. I)`. Types of classes
  and relations (`Set α`, `α → β → Prop`) are always inhabited.

## 4. Types, typical ambiguity, reducibility (✱12, Introduction Ch. II, Prefatory Statement)

PM's ramified theory of types is read in Lean's simple type theory:

* Individuals of a type: `α : Type u` (any universe). A propositional function of one variable is
  `φ : α → Prop`; of two variables `φ : α → β → Prop`. A class of α-things is `Set α`; a class of
  classes is `Set (Set α)`; a relation is `R : α → β → Prop` (heterogeneous: the referents and
  relata may be of different types, as in PM); relations of classes, classes of relations etc. are
  built the same way (`Set α → Set β → Prop`, `Set (α → β → Prop)`, …).
* *Typical ambiguity* = type (and universe) polymorphism: every PM proposition is stated for
  arbitrary type variables `{α : Type u} {β : Type v} …`. Where PM requires two variables to be of
  the same type (homogeneous relations, `C'R`, `R²`, `R ⥏ α`, …) use the same type variable; where PM
  speaks of *relative types* or *typical definiteness* (Prefatory Statement; ✱63–✱65, Part III),
  make the types explicit parameters, never coerce between types. `t'x` (the type of `x`, ✱63·01
  `ι'x ∪ −ι'x`) is defined as PM defines it and is then `Set.univ : Set α`.
* *The type conventions of Vol. II.* The Prefatory Statement of Symbolic Conventions (Vol. II)
  fixes how the types of ambiguous symbols are chosen in Parts III–V: real variables first, then
  constants; conventions IT, IIT (identification of types; "adequate" actual types of formal
  numbers such as `Nc'α`, `μ +_c ν`), AT (arithmetical equations), Infin T; and the relative-type
  notations of ✱63–✱65 (`α_x`, `Nc(ξ)'α`, `NC^β(α)`, …). These conventions are part of the
  meaning of PM's enunciations. Realize them by the choice of the type parameters (e.g. `Nc'α`
  as a class of classes of an explicit type `γ`; `μ, ν ∈ NC` does *not* identify the types of `μ`
  and `ν`) and, where a convention restricts a type to one that is adequate (`∃!` of the formal
  number in that type, or all inductive cardinals exist in it), by an explicit hypothesis saying
  so, citing the convention in the status (`proved (reading): convention AT, Prefatory Statement`).
  Every statement of Parts III–V follows the Prefatory Statement.
* *Orders and predicative functions.* PM distinguishes orders of functions and writes `φ!x` for a
  predicative function. Lean's `α → Prop` is one type for all functions with arguments in `α`
  (Prop is impredicative), so **every function is predicative**: `φ!x` is read `φ x`, and the
  quantifiers `(φ)`, `(∃φ)` over predicative functions are `∀ φ : α → Prop`, `∃ φ : α → Prop`.
  The *axiom of reducibility* ✱12·1 `⊢ : (∃f) : φx . ≡_x . f!x` becomes the provable
  `∃ f : α → Prop, ∀ x, φ x ↔ f x` (take `f := φ`), and ✱12·11 likewise; status
  `proved (reading)`.
* *What is lost.* The ramification (orders), the vicious-circle principle and the
  restriction of Section A to elementary propositions have no Lean counterpart; nor has PM's
  "no-class" theory (classes and descriptions as incomplete symbols are read as Lean terms or as
  explicit quantifications, §5–§6). The propositions that only express these restrictions are
  `remark`s; the theorems stated about them are their Lean readings.
* *What becomes provable.* Lean's `Classical.choice` proves the multiplicative axiom ✱88·03
  (`Mult ax`); reducibility ✱12·1·11 is provable (above). `Infin ax` (✱120·03) is not provable
  (it fails for finite types). Keep `Mult ax` as a hypothesis exactly where PM has it (§10); a
  proposition such as `Mult ax . ≡ . p` is still stated as PM prints it, even though both sides
  are provable in Lean (say so in its status: `proved (reading): Mult ax is a theorem of Lean`).

## 5. Identity and descriptions (✱13, ✱14, ✱30)

* PM defines `x = y . = : (φ) : φ!x . ⊃ . φ!y` (✱13·01). Lean's `=` (`Eq`) is primitive. Defs
  gives the definiens as `PMIdent x y := ∀ φ : α → Prop, φ x → φ y` with `PMIdent_iff_eq`; in all
  formulas PM's `=` is Lean's `=` (between classes, `Set` equality; between relations, function
  equality), and `pm13_01` states `x = y ↔ PMIdent x y` (`proved (reading)`). `x ≠ y` is `x ≠ y`.
* A description `(℩x)(φx)` is an *incomplete symbol*, defined only in use (✱14·01):
  `[(℩x)(φx)] . ψ(℩x)(φx) . = : (∃b) : φx . ≡_x . x = b : ψb`. Lean: `TheIs φ ψ` ("the φ is ψ")
  `:= ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b`; `E!(℩x)(φx)` is `EBang φ := ∃ b, ∀ x, φ x ↔ x = b`
  (`EBang φ ↔ ∃! x, φ x`: PM's `E!` is Lean's `∃!`).
* *Scope.* The scope of a description is the proposition `ψ(…)` replaced by `TheIs φ ψ`.
  Unless PM indicates otherwise (by `[(℩x)(φx)]` with dots), the scope is the *smallest*
  proposition enclosed in dots or brackets in which the description occurs; so `∼{a = (℩x)(φx)}` is
  `¬ TheIs φ (fun b => a = b)` but `a ≠ (℩x)(φx)` is `TheIs φ (fun b => a ≠ b)`. With two
  descriptions, the one occurring first has the larger scope (stated after ✱14·03; ✱14·113):
  `(℩x)(φx) = (℩x)(ψx)` is `TheIs φ (fun b => TheIs ψ (fun c => b = c))` (`TheIs2`).
* *Descriptive functions* (✱30): `R'y = (℩x)(xRy)`. A formula `ψ(R'y)` is `Desc R y ψ`
  (`:= TheIs (fun x => R x y) ψ`), `E!R'y` is `EDesc R y`, `ψ(R'S'y)` (✱30·02) is
  `Desc2 R S y ψ`. Translate by *rewriting with the contextual definition*; never introduce a
  `Classical.choose`/`Classical.epsilon` value for `R'y`.
* *Constant relations whose descriptive function always exists* (`R⃗`, `R⃖`, `sg`, `gs`, `D`, `ᗡ`,
  `C`, `R_∈`, `x♀`, `♀y`, …) are defined in Defs as `graph f` for a Lean function `f`
  (`graph f u y :≡ u = f y`), exactly as PM defines them (`α̂y{α = …}`); `Cnv`, defined by PM
  extensionally, has `desc_Cnv` instead. Then `desc_graph : Desc (graph f) y ψ ↔ ψ (f y)`, so in formulas
  `D'R` may be written `dom R`, `ᗡ'R` `codom R`, `C'R` `fld R`, `R⃗'y` `refs R y`, `Cnv'P` `cnv P`,
  `R_∈'β` `R ʻʻ β`, etc. **Exception:** the propositions in which PM proves that such a descriptive
  function exists or what its value is (e.g. ✱31·12–✱31·13, ✱32·13, ✱33·11–✱33·12, ✱37·…, ✱38·11)
  must be stated with `Desc`/`EDesc` (`Desc D R (fun A => A = {x | ∃ y, R x y})`), not with the
  value function, so that they keep their content. Likewise a Df whose definiens contains a
  descriptive function (✱37·03 `R̆_∈ = Cnv'R_∈`, ✱90·02, ✱170·02, …) is stated with `Desc`.
* *Definitions of descriptive functions* (Summary of Section E): a Df `R'x = S'x` (or `R'x = …`
  with a definiens that is a description) defines the relation `R = ûx̂(u = S'x)`. When `S'x`
  always exists, `R` is `graph` of the value function; otherwise `R` is `descRel S`
  (`fun u x => Desc S x (fun v => u = v)`, with `desc_descRel : Desc (descRel S) x ψ ↔ Desc S x ψ`).
  A relation whose descriptive function may fail to exist (`min_P`, `B`, `ν_P`, a selection `M`,
  …) is never replaced by a total Lean function.

## 6. Classes and relations (✱20–✱25)

* PM's classes are incomplete symbols (✱20·01 `f{ẑ(ψz)} . = : (∃φ) : φ!x . ≡_x . ψx : f{φ!ẑ}`);
  Lean reads a class of α-things as a term `A : Set α`: `ẑ(ψz)` is `{z | ψ z}`, `x ∈ α` is
  `x ∈ A`, `x ∼∈ α` is `x ∉ A`, `(α) . fα` is `∀ A : Set α, f A`. The contextual Dfs ✱20·01,
  ✱20·07, ✱20·08, ✱21·01, … become theorems (`proved (reading)`). Since `Set α` is `α → Prop`,
  classes are extensional by `Set.ext` (PM's ✱20·43 `α = β . ≡ : x ∈ α . ≡_x . x ∈ β`), as PM
  obtains them by reducibility; and `Cls = Set.univ`.
* A relation is `R : α → β → Prop`; `x̂ŷ φ(x, y)` is `fun x y => φ x y`, `xRy` is `R x y`;
  extensionality is `funext`/`propext` (PM's ✱21·43 `R = S . ≡ : xRy . ≡_{x,y} . xSy`).
* Class calculus (✱22, ✱24): **PM's `⊂` is Lean's `⊆`** (inclusion, not strict!), `∩`, `∪` are
  `∩`, `∪`, `−α` is `Aᶜ`, `α − β` is `A \ B`, `V` is `V` (`= Set.univ`), `Λ` is `Λ` (`= ∅`).
  **PM's `∃!α` ("α has members", ✱24·03) is `A.Nonempty`, not Lean's `∃!`.**
* Relation calculus (✱23, ✱25), PM's dotted signs: `R ⊂̇ S` is `R ⪽ S`, `R ∩̇ S` is `R ⩀ S`,
  `R ∪̇ S` is `R ⊍ S`, `−̇R` is `∸R`, `R −̇ S` is `R ∸ S`, `V̇` is `rV`, `Λ̇` is `rNull`,
  `∃̇!R` is `rEx R`.

## 7. Symbol table: PM → Lean (namespace `PrincipiaMathematica`; notation is `scoped`)

The notations are `scoped`, hence active inside `namespace PrincipiaMathematica` (as in every
Section file) or after `open PrincipiaMathematica`.

| PM | Df | Lean |
|----|----|------|
| `∼p`, `p ∨ q`, `p ⊃ q`, `p . q`, `p ≡ q` | ✱1·01, ✱3·01, ✱4·01 | `¬p`, `p ∨ q`, `p → q`, `p ∧ q`, `p ↔ q` |
| `p ∨ q ∨ r`, `p ⊃ q ⊃ r`, `p ≡ q ≡ r`, `p . q . r` | ✱2·33, ✱3·02, ✱4·02, ✱4·34 | `Disj3`, `ImpChain`, `EqvChain`, `Conj3` (write them out) |
| `(x) . φx`, `(∃x) . φx` | ✱9, ✱10·01 | `∀ x, φ x`, `∃ x, φ x` |
| `φx ⊃_x ψx`, `φx ≡_x ψx` | ✱10·02·03 | `∀ x, φ x → ψ x` (`FImp`), `∀ x, φ x ↔ ψ x` (`FEqv`) |
| `(x, y)`, `(∃x, y)`, `⊃_{x,y}`, `≡_{x,y}` | ✱11 | `∀ x y`, `∃ x y`, `FImp2`, `FEqv2` |
| `φ!x`, `(φ)`, `(∃φ)` | ✱12 | `φ x`, `∀ φ : α → Prop`, `∃ φ : α → Prop` |
| `x = y`, `x ≠ y`, `x = y = z` | ✱13·01–·03 | `x = y` (`PMIdent`), `x ≠ y`, `EqChain` |
| `ψ(℩x)(φx)`, `E!(℩x)(φx)` | ✱14·01·02 | `TheIs φ ψ`, `EBang φ` |
| two descriptions | ✱14·03·04 | `TheIs2 φ ψ f`, `TheIs2Rev φ ψ f` |
| `ẑ(φz)`, `x ∈ α`, `x ∼∈ α`, `x, y ∈ α` | ✱20 | `{z \| φ z}`, `x ∈ A`, `x ∉ A`, `Mem2 x y A` |
| `Cls`, `Rel` | ✱20·03, ✱21·03 | `Cls`, `Rel` |
| `x̂ŷ φ(x, y)`, `xRy` | ✱21 | `fun x y => φ x y`, `R x y` |
| `α ⊂ β`, `α ∩ β`, `α ∪ β`, `−α`, `α − β` | ✱22·01–·05 | `A ⊆ B`, `A ∩ B`, `A ∪ B`, `Aᶜ`, `A \ B` |
| `R ⊂̇ S`, `R ∩̇ S`, `R ∪̇ S`, `−̇R`, `R −̇ S` | ✱23·01–·05 | `R ⪽ S` (`RSub`), `R ⩀ S` (`rcap`), `R ⊍ S` (`rcup`), `∸R` (`rneg`), `R ∸ S` (`rdiff`) |
| `V`, `Λ`, `∃!α` | ✱24·01–·03 | `V`, `Λ` (`Null`), `A.Nonempty` |
| `V̇`, `Λ̇`, `∃̇!R` | ✱25·01–·03 | `rV`, `rNull`, `rEx R` |
| `R'y`, `E!R'y`, `R'S'y` | ✱30·01·02 | `Desc R y ψ`, `EDesc R y`, `Desc2 R S y ψ` |
| relation with value `f'y` | — | `graph f` (always exists); `descRel S` for `ûx̂(u = S'x)` |
| `Cnv`, `P̆` (`Cnv'P`) | ✱31·01·02 | `Cnv`, `P˘` (`cnv P`) |
| `R⃗`, `R⃖`, `R⃗'y`, `R⃖'x` | ✱32·01·02 | `Rfwd R`, `Rbwd R`, `refs R y`, `rels R x` |
| `sg`, `gs` | ✱32·03·04 | `sg`, `gs` |
| `D`, `ᗡ`, `C`, `F`; `D'R`, `ᗡ'R`, `C'R` | ✱33·01–·04 | `D`, `Dcnv`, `C`, `F`; `dom R`, `codom R`, `fld R` |
| `R \| S`, `R²`, `R³` | ✱34·01–·03 | `R ⨾ S` (`relProd`), `rsq R`, `rcube R` |
| `α ↿ R`, `R ↾ β`, `α ↿ R ↾ β`, `α ↑ β` | ✱35·01–·04 | `A ◁ R` (`dres`), `R ↾ B` (`cres`), `bres A R B`, `cross A B` |
| `P ⥏ α` | ✱36·01 | `P ⥏ A` (`fres`) |
| `R''β`, `R_∈`, `R̆_∈`, `R'''κ`, `E!!R''β`, `R_∈²` | ✱37 | `R ʻʻ B` (`img`), `imgRel R`, `imgRelCnv R`, `R ʻʻʻ K` (`img3`), `EE R B`, `imgRelSq R` |
| `x♀`, `♀y`, `α ♀,, y` | ✱38·01–·03 | `opL f x`, `opR f y`, `opImg f A y` |
| `R \|` , `\| S` | ✱38 with `♀ = \|` | `relProdL R`, `relProdR S` |
| `p'κ`, `s'κ` | ✱40·01·02 | `prodCls K`, `sumCls K` (`= ⋂₀ K`, `⋃₀ K`) |
| `ṗ'λ`, `ṡ'λ` | ✱41·01·02 | `prodRel L`, `sumRel L` |
| `R ‖ S` | ✱43·01 | `R ∥ S` (`dpar`) |

Precedences (chosen to realize PM's bracketing Dfs ✱34·22, ✱35·24·25·27 and PM's unbracketed
formulas such as ✱35·17, ✱35·412, ✱36·2, ✱34·62): `ʻʻ`, `ʻʻʻ` 80 (right); prefix `∸` 75; `◁` 75
(right); `⨾`, `∥` 70 (left); `↾`, `⥏` 68 (left); `⩀` 67 (left); `⊍`, binary `∸` 65 (left);
postfix `˘` max; `⪽` 50. So `↿` > `|` > `↾`, `⥏` > `∩̇` > `∪̇`, `−̇`, as in PM. When PM writes
brackets, write the same brackets (and see §2 for brackets PM leaves to the types).

*Later Parts.* Signs that clash with Lean syntax or with numerals get names in `Defs/PartN`
(e.g. `α → β` of ✱70·01, `1`, `0`, `2` of ✱52–✱54, the relation `∈` of ✱62·01, `S;Q` of ✱150·01);
`scoped` Unicode notation may be added when it does not clash. Each Defs file extends this table
in its module docstring.

## 8. Definitions (Df) and primitive propositions (Pp)

* Every Df of Part N is in `Defs/PartN.lean`, in a docstring headed `**✱N·M Df.**` with the
  formula as printed and its reading. A Df that defines a *term* (`Cls`, `α ∩ β`, `D`, `R | S`, …)
  is a Lean `def` (noncomputable where needed), stated so that its defining equation holds by
  `rfl`/`Iff.rfl`/`Set.ext`. A Df that is a *notational convention or contextual definition*
  (✱1·01, ✱9·01, ✱14·01, ✱20·01, ✱22·53, ✱30·02, ✱35·24, …) is a translation rule; Defs gives
  the rule and the exact target statement. All targets given in `Defs/Part1` have been checked to
  elaborate (and to hold by the indicated proof); copy them.
* In the Section files the Df ✱N·M is the theorem `pmN_M` stating the defining equation of the
  Lean definition (status `definition`, the default for a Df), or, for a Df read by a Lean
  primitive, the equivalence of the primitive with PM's definiens (status `definition` when it
  holds by `Iff.rfl`, `proved (reading)` otherwise).
* A Pp is a theorem like any other (Lean proves PM's axioms); the meta-level Pps are §1.

## 9. Status vocabulary

The docstring of a proposition may end with a paragraph `**Status.** <status>: <explanation>`
(the status word(s) first, on the same line); without it the status is `proved` (a Df:
`definition`). `scripts/prop_table.py` collects them. See ✱1 in `Part1/SectionA.lean`.

* `proved` — PM's statement, at full strength, with exactly PM's hypotheses, is proved.
* `proved (reading): …` — proved under a stated reading: a Lean primitive replaces PM's definition
  (✱1·01), a meta-level principle is recorded by its Lean counterpart (✱1·1), an erratum or a
  transcription error of the e-text has been applied (say which), PM's tacit assumption that
  something exists was made explicit (`[Nonempty α]`), or PM's statement involves an
  incomplete-symbol convention that needed choosing.
* `proved (corrected): …` — PM's statement is false even after the errata; the corrected statement
  (minimal correction, explained) is proved. If feasible, also prove the failure of the printed
  form as an extra lemma `pmN_M_printed_false`.
* `definition` — a Df whose defining equation is proved.
* `remark: …` — not a mathematical proposition in Lean's sense (a rule about notation, types,
  elementarity); the declaration records the Lean counterpart.
* `stated (open here): …` — the statement is given as `def pmN_M : Prop := …` but not proved.

*Errata.* There are three lists, all in `data/principia.json` (`volumes[].front`): ERRATA (Vol. I),
ADDITIONAL ERRATA TO VOLUME I and ERRATA TO VOLUME II (both printed in Vol. II, in the same front
entry). Every proposition is formalized **as corrected by the errata**. *First check whether the
e-text already incorporates the correction*: it does for the enunciation errata ✱2·52, ✱10·23,
✱23·81, ✱25·37, ✱25·412, ✱40·18, ✱55·281, ✱73·511, ✱205·7 (formalize the e-text as printed, status
`proved`, and mention the erratum in a sentence; never "re-apply" a correction that is already
made); it does **not** for ✱81·23 (`ι'R⃗'y` must be read `ι'R'y`), which gets
`proved (reading): erratum (Additional Errata to Vol. I, p. 522): …`; check ✱112·23 (dots)
likewise. The Vol. I ERRATA warn (p. 218) that `Λ` is liable to be printed for `Λ̇`: where PM prints `Λ` in a place where
only a relation is significant, read `Λ̇` (`rNull`), status `proved (reading): erratum (Vol. I,
p. 218) …`. Errata to demonstrations only (✱5·11, ✱5·12, ✱14·111, ✱31·16, …) do not affect
statements. The Project Gutenberg e-text also has its own transcription errors (e.g. ✱1·4 prints
`p ∨ p` for `q ∨ p`; ✱23·02 omits the `R` of `R ∩̇ S`; ✱33·02 prints `β̂ =` for `β =`; ✱30·18
prints `∃!R'y` for `E!R'y`): formalize PM's intended statement, checked against the comments, the
proofs, the summaries and later uses, with status `proved (reading): transcription error …` (for a
Df: `definition`, with the remark).

## 10. House rules

* State every proposition at **full strength with exactly PM's hypotheses**: never add a
  hypothesis PM does not have (the only exceptions are `[Nonempty α]` in §3 and the explicit
  rendering of a type convention of the Prefatory Statement in §4, each named in the status), never
  weaken a conclusion, never split a proposition into weaker pieces. PM's hypotheses `E!R'y` (`EDesc R y`),
  `∃!α` (`A.Nonempty`), `∃̇!R` (`rEx R`), typical definiteness (explicit type parameters), the
  multiplicative axiom `Mult ax` and the axiom of infinity `Infin ax` (Prop-valued definitions in
  `Defs/Part2`/`Part3`) are explicit hypotheses exactly where PM has them (as antecedents
  `Mult ax . ⊃ . …` are hypotheses or premisses of the implication, as printed). `Mult ax` and
  `Infin ax` are typically ambiguous: take them at the type(s) PM's enunciation and conventions
  determine (`Infin ax(x)` of ✱120·04 at the type of `x`), never as `∀` over all types.
* Never trivialize via definitions: a definition must be PM's, and a theorem may not hold by
  `rfl` merely because a definition was chosen to make it so (see the exception in §5 for
  descriptive functions).
* Translate *every* conjunct, quantifier and description of the formula; for an asserted chain
  `A = B = C` (✱13·03) state the conjunction of the links.
* Proofs are complete: no `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by`, `unsafe`.
  Any proof is acceptable (it need not follow PM's demonstration); citing earlier `pmN_M`
  theorems is encouraged where natural.
* Names: the proposition ✱N·M is `pmN_M` (`✱2·01` ↦ `pm2_01`, `✱1·1` ↦ `pm1_1`); helper lemmas
  are `private` or named `pmN_M_aux…`.
-/

namespace PrincipiaMathematica

universe u v

/-- The relation whose descriptive function is `f` (PM ✱30): `graph f u y` holds when
`u = f y`, so that `f'y`, i.e. `(℩u)(u (graph f) y)`, always exists and is `f y`
(`desc_graph` in `Defs/Part1`). PM's constant relations `R⃗`, `sg`, `D`, `ᗡ`, `C`, `R_∈`,
`x♀`, `♀y`, … are of this form. Not itself a PM definition. -/
def graph {α : Type u} {β : Type v} (f : β → α) : α → β → Prop := fun u y => u = f y

@[simp] theorem graph_apply {α : Type u} {β : Type v} (f : β → α) (u : α) (y : β) :
    graph f u y ↔ u = f y := Iff.rfl

end PrincipiaMathematica
