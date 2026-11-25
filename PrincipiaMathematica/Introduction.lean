import PrincipiaMathematica.Defs.Part2
import Mathlib.SetTheory.Ordinal.Univ
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-!
# The Introduction, the Summaries and the explanatory Notes

Volume I: the Preface, the Introduction (Chapter I, *Preliminary explanations of ideas and
notations*; Chapter II, *The theory of logical types*; Chapter III, *Incomplete symbols*), the
Summary of Part I, the Note to Section D and the Summary of Part II. Volume II: the Prefatory
Statement of Symbolic Conventions and the General Note on Cardinal Correlators.

PM's Preface says that these texts "are wholly explanatory, and form no part of the chain of
deductions". They nevertheless make many *mathematical* claims: laws of the calculus of
propositions, classes and relations stated in advance, the behaviour of descriptions and class
symbols under changes of scope, the contradictions of Chapter II § VIII and their resolution by
the theory of types, and the claims of the Prefatory Statement about the existence of cardinals in
the various types. This file formalizes those claims. Pure prose (motivation, philosophy,
history) has no unit. The Introduction's examples of the dots (Basic §2) are asserted
propositions and have a unit. Sections II–V and VII of the Prefatory Statement explain the
conventions on formal numbers (IT, IIT, AT, the Rule of Indefinite Numbers), illustrated by
starred propositions of ✱100–✱126 stated with Part III notions (`Nc`, `NC`, `+_c`, `sm''`); these
conventions are realized in the Part III files (Basic §4) and the illustrations are formalized
there. Only their claims that need no Part III notion have units here.

The notions of Part II that the texts use (`ι'x`, `1`, `0`, `2`, `ῐ`, `Cl`, `sm`) are taken from
`Defs/Part2.lean`, so that "`α ∈ 1`", "`∃!2`", "`α` is similar to `β`" are PM's own.

Each claim (or group of claims) is a unit block `## [intro.<slug>] Title` giving the place in the
text, a verbatim quotation, the **Lean reading** and the **Status** (vocabulary of `Basic.lean` §9),
followed by the Lean declarations, each with its own docstring (the formula as printed, where
there is one, and a `**Status.**` paragraph when it is not plainly `proved`). Declarations live in
the namespace `PrincipiaMathematica.Intro`. Docstrings never begin with a starred number: the
numbered propositions of the body are formalized in the Part files; where the Introduction states
one of them in advance, it is restated and proved here directly.

Conventions special to this file. *Cardinals*: where the Introduction or the Prefatory Statement
speaks of the number of members of a class, the Lean reading is mathlib's `Cardinal.mk` (`#A`,
for `A : Set τ`, coerced to a type); "the cardinal `c` exists in the type `τ`" (PM's `∃!c` with
`c` determined in the type of classes of `τ`-objects) is `∃ A : Set τ, #A = c` (for `0`, `1`,
`2`, which Part II defines, PM's own `∃!0`, `∃!1`, `∃!2` are used), and "`α` is similar to `β`" is
✱73·02's `sm A B` (`sm_iff_nonempty_equiv`: a bijection between the classes). *Ordinals*:
mathlib's `Ordinal`. Both are used only in this file (the Part III–V files have their own PM
definitions). The universe levels `Type u`, `Type (u+1)` of Lean play the part of PM's "types"
where the Introduction appeals to the hierarchy (Burali-Forti, the greatest cardinal).

The errata lists touch the Introduction only at pages already corrected in the e-text (p. 14,
p. 15, p. 34, p. 36, p. 44, p. 68, p. 86 are incorporated); transcription slips of the e-text in the
Introduction are noted where they occur (e.g. the law of absorption labelled `*4·24` for ✱4·71;
`ψx ≡_x x = c` for `x = d` in Chapter III's formula (4)).
-/

namespace PrincipiaMathematica

namespace Intro

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-! # Volume I, Introduction, Chapter I: preliminary explanations of ideas and notations -/

/-!
## [intro.truth-values] Equivalence, truth-values and truth-functions

*(Vol. 1, Introduction, Chapter I, "Equivalence", "Truth-values")*

> It is easily seen that two propositions are equivalent when, and only when, they are both true
> or are both false. […] It will be observed that the truth-values of \(p \lor q\), \(p . q\),
> \(p \supset q\), \({\sim} p\), \(p \equiv q\) depend only upon those of \(p\) and \(q\) […]
> Hence it is easy to see (though it cannot be formally proved except in each particular case)
> that if a proposition \(p\) occurs in any proposition \(f(p)\) which we shall ever have occasion
> to deal with, the truth-value of \(f(p)\) will depend, not upon the particular proposition
> \(p\), but only upon its truth-value; *i.e.* if \(p \equiv q\), we shall have
> \(f(p) \equiv f(q)\).

**Lean reading.** Propositions are terms of `Prop`; "equivalent" is `↔`. The truth-value of a
compound depends only on those of its components: if `p ↔ p'` and `q ↔ q'` then each of the five
connectives gives equivalent results. PM's claim that every function of propositions it uses is a
*truth-function* "cannot be formally proved except in each particular case", because PM admits
intensional functions such as "`A` believes `p`". In Lean every `f : Prop → Prop` is a
truth-function, by propositional extensionality (`propext`): the general statement is a theorem.

**Status.** complete. Equivalence as sameness of truth-value and the truth-tables proved;
the truth-function principle proved (reading) (holds for *all* functions of propositions in
Lean).
-/

/-- Intro, Ch. I: two propositions are equivalent when, and only when, they are both true or both
false. -/
theorem equiv_iff_same_truth_value {p q : Prop} : (p ↔ q) ↔ (p ∧ q) ∨ (¬p ∧ ¬q) := by
  tauto

/-- Intro, Ch. I: the truth-values of `p ∨ q`, `p . q`, `p ⊃ q`, `∼p`, `p ≡ q` depend only upon
those of `p` and `q`. -/
theorem connectives_truth_functional {p q p' q' : Prop} (hp : p ↔ p') (hq : q ↔ q') :
    (p ∨ q ↔ p' ∨ q') ∧ (p ∧ q ↔ p' ∧ q') ∧ ((p → q) ↔ (p' → q')) ∧ (¬p ↔ ¬p') ∧
      ((p ↔ q) ↔ (p' ↔ q')) := by
  cases propext hp
  cases propext hq
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Intro, Ch. I: "if \(p \equiv q\), we shall have \(f(p) \equiv f(q)\)."

**Status.** proved (reading): PM asserts this only of the functions of propositions it will
construct ("it cannot be formally proved except in each particular case"), since it admits
intensional functions of propositions. Lean's functions of propositions are all truth-functions
(propositional extensionality), so the statement is proved for every `f : Prop → Prop`. -/
theorem truth_function (f : Prop → Prop) {p q : Prop} (h : p ↔ q) : f p ↔ f q := by
  rw [propext h]

/-!
## [intro.dots] The use of dots: the asserted examples

*(Vol. 1, Introduction, Chapter I, "The use of dots")*

> When we *assert* this proposition, instead of merely considering it, we write
> \(\unicode{x201c}\vdash : p \lor q \ldotp \supset \ldotp q \lor p,\unicode{x201d}\) […]
> "\(p \supset q \ldotp \supset : q \supset r \ldotp \supset \ldotp p \supset r\)" will mean "if
> \(p\) implies \(q\), then if \(q\) implies \(r,~p\) implies \(r\)." If we wish to assert this
> (which is true) we write
> \(\unicode{x201c}\vdash \colon\ldotp p \supset q \ldotp \supset : q \supset r \ldotp \supset \ldotp p \supset r.\unicode{x201d}\)
> Again "\(p \supset q \ldotp \supset \ldotp q \supset r : \supset \ldotp p \supset r\)" will mean
> "if '\(p\) implies \(q\)' implies '\(q\) implies \(r\),' then \(p\) implies \(r\)." This is in
> general untrue. […] "\(p \supset q : q \supset r \ldotp \supset \ldotp p \supset r\)" will mean
> "\(p\) implies \(q\); and if \(q\) implies \(r\), then \(p\) implies \(r\)." (This is not true
> in general.) […]
> \(\unicode{x201c}\vdash \colon\colon p \lor q.\supset \colon\ldotp p. \lor .q \supset r \colon \supset .p \lor r.\unicode{x201d}\)
> (This proposition is proved in the body of the work; it is *2·75.) If we wish to assert (what
> is equivalent to the above) the proposition: […] we write
> \(\unicode{x201c}\vdash \colon\ldotp p \lor q \colon p. \lor .q \supset r \colon \supset .p \lor r.\unicode{x201d}\)

**Lean reading.** The bracketing is Basic §2 (whose worked examples are exactly these formulas).
The asserted ones are theorems; "in general untrue" is the failure of the universal closure, shown
by a choice of truth-values; "what is equivalent to the above" is the equivalence of the curried
and the product forms.

**Status.** complete. All proved.
-/

/-- Intro, Ch. I, dots. \(\vdash : p \lor q \ldotp \supset \ldotp q \lor p\) -/
theorem dots_perm {p q : Prop} : p ∨ q → q ∨ p := Or.symm

/-- Intro, Ch. I, dots.
\(\vdash \colon\ldotp p \supset q \ldotp \supset : q \supset r \ldotp \supset \ldotp p \supset r\) -/
theorem dots_syll {p q r : Prop} : (p → q) → ((q → r) → (p → r)) := fun h1 h2 hp => h2 (h1 hp)

/-- Intro, Ch. I, dots: "\(p \supset q \ldotp \supset \ldotp q \supset r : \supset \ldotp p \supset r\)
[…] is in general untrue". -/
theorem dots_untrue_imp : ¬ ∀ p q r : Prop, ((p → q) → (q → r)) → (p → r) :=
  fun h => h True False False (fun hpq _ => hpq trivial) trivial

/-- Intro, Ch. I, dots: "\(p \supset q : q \supset r \ldotp \supset \ldotp p \supset r\)
[…] (This is not true in general.)" -/
theorem dots_untrue_prod : ¬ ∀ p q r : Prop, (p → q) ∧ ((q → r) → (p → r)) :=
  fun h => (h True False False).1 trivial

/-- Intro, Ch. I, dots (✱2·75).
\(\vdash \colon\colon p \lor q.\supset \colon\ldotp p. \lor .q \supset r \colon \supset .p \lor r\) -/
theorem dots_2_75 {p q r : Prop} : p ∨ q → ((p ∨ (q → r)) → p ∨ r) := by
  tauto

/-- Intro, Ch. I, dots.
\(\vdash \colon\ldotp p \lor q \colon p. \lor .q \supset r \colon \supset .p \lor r\) -/
theorem dots_2_75_prod {p q r : Prop} : (p ∨ q) ∧ (p ∨ (q → r)) → p ∨ r := by
  tauto

/-- Intro, Ch. I, dots: the product form is "equivalent to the above". -/
theorem dots_2_75_equiv {p q r : Prop} :
    (p ∨ q → ((p ∨ (q → r)) → p ∨ r)) ↔ ((p ∨ q) ∧ (p ∨ (q → r)) → p ∨ r) :=
  ⟨fun h hc => h hc.1 hc.2, fun h h1 h2 => h ⟨h1, h2⟩⟩

/-!
## [intro.definitions] The three definitions of the theory of deduction

*(Vol. 1, Introduction, Chapter I, "Equivalence", "Definitions", "Summary of preceding statements")*

> Thus "\(p \equiv q\)" stands for "\((p \supset q) \ldotp (q \supset p)\)." […] An example of a
> definition is \(p \supset q \ldotp = \ldotp {\sim} p \lor q \qquad \text{Df.}\) […] Three
> definitions have been introduced:
> \(p \ldotp q \ldotp = \ldotp {\sim} ({\sim} p \lor {\sim} q) \quad \text{Df},\)
> \(p \supset q \ldotp = \ldotp {\sim} p \lor q \quad \text{Df},\)
> \(p \equiv q \ldotp = \ldotp p \supset q \ldotp q \supset p \quad \text{Df}.\)

**Lean reading.** These are ✱3·01, ✱1·01, ✱4·01; as there (Basic §1), Lean's `∧`, `→`, `↔` are
primitive and each Df becomes the equivalence of the primitive with PM's definiens.

**Status.** complete. proved (reading): Lean's connectives are primitive (as ✱1·01, ✱3·01, ✱4·01).
-/

/-- Intro, Ch. I: the three definitions, `p . q`, `p ⊃ q`, `p ≡ q`.

**Status.** proved (reading): Lean's `∧`, `→`, `↔` are primitive; the Dfs become equivalences with
PM's definientia (as ✱3·01, ✱1·01, ✱4·01). -/
theorem three_definitions {p q : Prop} :
    ((p ∧ q ↔ ¬(¬p ∨ ¬q)) ∧ ((p → q) ↔ ¬p ∨ q)) ∧ ((p ↔ q) ↔ (p → q) ∧ (q → p)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> tauto

/-!
## [intro.primitive-propositions] The primitive propositions of the theory of deduction

*(Vol. 1, Introduction, Chapter I, "Primitive propositions")*

> (1) Anything implied by a true premiss is true Pp. […]
> (2) \(\vdash \colon p \lor p \ldotp \supset \ldotp p \quad \text{Pp}\), […]
> (3) \(\vdash \colon q \ldotp \supset \ldotp p \lor q \quad \text{Pp}\), […]
> (4) \(\vdash \colon p \lor q \ldotp \supset \ldotp q \lor p \quad \text{Pp}\), […]
> (5) \(\vdash \colon p \lor (q \lor r) \ldotp \supset \ldotp q \lor (p \lor r) \quad \text{Pp}\), […]
> (6) \(\vdash \colon \ldotp q \supset r \ldotp \supset \colon p \lor q \ldotp \supset \ldotp p \lor r \quad \text{Pp}\), […]
> (7) Besides the above primitive propositions, we require a primitive proposition called "the
> axiom of identification of real variables." […]

**Lean reading.** These are PM's ✱1·1–✱1·72 (formalized in `Part1/SectionA.lean`); the
Introduction prints them with (4) correct (`q ∨ p`, which the e-text of ✱1·4 misprints). Read as in
✱1: (1) is the rule of inference (modus ponens), (2)–(6) are theorems of Lean's logic, (7) (and
✱1·7–✱1·72) are typing facts.

**Status.** complete. (1) proved (reading) (rule of inference); (2)–(6) proved; (7) remark (see
✱1·72 in `Part1/SectionA.lean`).
-/

/-- Intro, Ch. I, primitive proposition (1): "Anything implied by a true premiss is true."

**Status.** proved (reading): a rule of inference, recorded as modus ponens (as ✱1·1). -/
theorem pp_inference {p q : Prop} (hp : p) (hpq : p → q) : q := hpq hp

/-- Intro, Ch. I, primitive proposition (2). \(\vdash \colon p \lor p \ldotp \supset \ldotp p\) -/
theorem pp_taut {p : Prop} : p ∨ p → p := fun h => h.elim id id

/-- Intro, Ch. I, primitive proposition (3). \(\vdash \colon q \ldotp \supset \ldotp p \lor q\) -/
theorem pp_add {p q : Prop} : q → p ∨ q := Or.inr

/-- Intro, Ch. I, primitive proposition (4). \(\vdash \colon p \lor q \ldotp \supset \ldotp q \lor p\) -/
theorem pp_perm {p q : Prop} : p ∨ q → q ∨ p := Or.symm

/-- Intro, Ch. I, primitive proposition (5).
\(\vdash \colon p \lor (q \lor r) \ldotp \supset \ldotp q \lor (p \lor r)\) -/
theorem pp_assoc {p q r : Prop} : p ∨ (q ∨ r) → q ∨ (p ∨ r) := by
  tauto

/-- Intro, Ch. I, primitive proposition (6).
\(\vdash \colon \ldotp q \supset r \ldotp \supset \colon p \lor q \ldotp \supset \ldotp p \lor r\) -/
theorem pp_sum {p q r : Prop} : (q → r) → (p ∨ q → p ∨ r) := fun h => Or.imp_right h

/-!
## [intro.simple-propositions] Some simple propositions of the calculus of propositions

*(Vol. 1, Introduction, Chapter I, "Some simple propositions")*

> The law of excluded middle: \(\vdash . p \lor {\sim}p.\) […] The law of contradiction (*3·24):
> \(\vdash . {\sim}(p.{\sim}p).\) The law of double negation (*4·13): \(\vdash . p \equiv
> {\sim}({\sim}p).\) The principle of *transposition* […] (*4·1) \(\vdash \colon p \supset q.
> \equiv .{\sim}q \supset {\sim}p\), (*4·11) \(\vdash \colon p \equiv q. \equiv . {\sim}p \equiv
> {\sim}q\), (*4·14) \(\vdash \colon\ldotp p . q. \supset . r \equiv \colon p. {\sim}r . \supset.
> {\sim}q\) […] The law of tautology, in the two forms: (*4·24) \(\vdash \colon p. \equiv .p\, .
> p\), (*4·25) \(\vdash \colon p. \equiv .p \lor p\) […] The law of absorption : (*4·24)
> \(\vdash \colon\ldotp p \supset q. \equiv \colon p. \equiv . p . q\) […] (*4·73)
> \(\vdash \colon \ldotp q \ldotp \supset \colon p \ldotp \equiv \ldotp p \ldotp q.\) Logical
> addition and multiplication of propositions obey the associative and commutative laws, and the
> distributive law in two forms, namely (*4·4) \(\vdash \colon\ldotp p \ldotp q \lor r \ldotp
> \equiv \colon p \ldotp q \ldotp \lor \ldotp p \ldotp r\text{,}\) (*4·41) \(\vdash \colon \ldotp p
> \ldotp \lor \ldotp q \ldotp r \colon \equiv \colon p \lor q \ldotp p \lor r\text{.}\)

**Lean reading.** Each is the Lean reading of the body proposition cited (Basic §1–§2). Two slips
of the text: the law of absorption is labelled `(*4·24)`, but it is ✱4·71 of the body (✱4·24 is
the law of tautology printed just before); and in ✱4·14 the e-text drops the colon before the
principal `≡` (the body has `p.q.⊃.r : ≡ : p.∼r.⊃.∼q`).

**Status.** complete. All proved.
-/

/-- Intro, Ch. I: the law of excluded middle (✱2·11). \(\vdash . p \lor {\sim}p.\) -/
theorem excluded_middle {p : Prop} : p ∨ ¬p := Classical.em p

/-- Intro, Ch. I: the law of contradiction (✱3·24). \(\vdash . {\sim}(p.{\sim}p).\) -/
theorem law_of_contradiction {p : Prop} : ¬(p ∧ ¬p) := fun h => h.2 h.1

/-- Intro, Ch. I: the law of double negation (✱4·13). \(\vdash . p \equiv {\sim}({\sim}p).\) -/
theorem double_negation {p : Prop} : p ↔ ¬¬p := not_not.symm

/-- Intro, Ch. I: transposition (✱4·1). \(\vdash \colon p \supset q. \equiv .{\sim}q \supset {\sim}p\) -/
theorem transposition {p q : Prop} : (p → q) ↔ (¬q → ¬p) := by
  tauto

/-- Intro, Ch. I: transposition (✱4·11). \(\vdash \colon p \equiv q. \equiv . {\sim}p \equiv {\sim}q\) -/
theorem transposition_equiv {p q : Prop} : (p ↔ q) ↔ (¬p ↔ ¬q) := by
  tauto

/-- Intro, Ch. I: transposition (✱4·14).
\(\vdash \colon\ldotp p . q. \supset . r \equiv \colon p. {\sim}r . \supset. {\sim}q\)
(the e-text drops the colon before the principal `≡`). -/
theorem transposition_product {p q r : Prop} : (p ∧ q → r) ↔ (p ∧ ¬r → ¬q) := by
  tauto

/-- Intro, Ch. I: the law of tautology (✱4·24). \(\vdash \colon p. \equiv .p\, . p\) -/
theorem tautology_and {p : Prop} : p ↔ p ∧ p := (and_self_iff).symm

/-- Intro, Ch. I: the law of tautology (✱4·25). \(\vdash \colon p. \equiv .p \lor p\) -/
theorem tautology_or {p : Prop} : p ↔ p ∨ p := (or_self_iff).symm

/-- Intro, Ch. I: the law of absorption, printed with the label `(*4·24)`; it is ✱4·71.
\(\vdash \colon\ldotp p \supset q. \equiv \colon p. \equiv . p . q\) -/
theorem absorption {p q : Prop} : (p → q) ↔ (p ↔ p ∧ q) := by
  tauto

/-- Intro, Ch. I (✱4·73). \(\vdash \colon \ldotp q \ldotp \supset \colon p \ldotp \equiv \ldotp p \ldotp q.\) -/
theorem absorption_of_true {p q : Prop} : q → (p ↔ p ∧ q) := by
  tauto

/-- Intro, Ch. I: logical addition and multiplication obey the commutative and associative laws
(✱4·3, ✱4·31, ✱4·32, ✱4·33). -/
theorem comm_assoc {p q r : Prop} :
    ((p ∧ q ↔ q ∧ p) ∧ (p ∨ q ↔ q ∨ p)) ∧ (((p ∧ q) ∧ r ↔ p ∧ (q ∧ r)) ∧
      ((p ∨ q) ∨ r ↔ p ∨ (q ∨ r))) := by
  tauto

/-- Intro, Ch. I: the distributive law (✱4·4).
\(\vdash \colon\ldotp p \ldotp q \lor r \ldotp \equiv \colon p \ldotp q \ldotp \lor \ldotp p \ldotp r\) -/
theorem distrib_and_or {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  tauto

/-- Intro, Ch. I: the distributive law (✱4·41).
\(\vdash \colon \ldotp p \ldotp \lor \ldotp q \ldotp r \colon \equiv \colon p \lor q \ldotp p \lor r\) -/
theorem distrib_or_and {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  tauto

/-!
## [intro.total-variation] The range of values and total variation

*(Vol. 1, Introduction, Chapter I, "The range of values and total variation")*

> Now in respect to the truth or falsehood of propositions of this range three important cases
> must be noted and symbolised. These cases are given by three propositions of which one at
> least must be true. Either (1) all propositions of the range are true, or (2) some
> propositions of the range are true, or (3) no proposition of the range is true. […] It is an
> obvious error, though one easy to commit, to assume that cases (1) and (3) are each other's
> contradictories.

**Lean reading.** (1) is `∀ x, φ x`, (2) is `∃ x, φ x`, (3) is `∀ x, ¬φ x`. "One at least must be
true" is a theorem; that (1) and (3) are not contradictories is shown by a function on `Bool` for
which neither holds.

**Status.** complete. Both proved.
-/

/-- Intro, Ch. I: of (1) `(x).φx`, (2) `(∃x).φx`, (3) `(x).∼φx`, one at least must be true. -/
theorem three_cases (φ : α → Prop) : (∀ x, φ x) ∨ (∃ x, φ x) ∨ (∀ x, ¬φ x) := by
  by_cases h : ∃ x, φ x
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr fun x hx => h ⟨x, hx⟩)

/-- Intro, Ch. I: cases (1) and (3) are not each other's contradictories: for some function
neither holds. -/
theorem total_variation_not_contradictory :
    ∃ φ : Bool → Prop, ¬(∀ x, φ x) ∧ ¬(∀ x, ¬φ x) :=
  ⟨fun x => x = true, fun h => Bool.noConfusion (h false), fun h => h true rfl⟩

/-!
## [intro.quantifier-definitions] Negation and disjunction of general propositions

*(Vol. 1, Introduction, Chapter I, "The range of values and total variation", "Ambiguous
assertion and the real variable", "Definition and real variables"; Chapter II, § III)*

> For the sake of brevity of symbolism a definition is made, namely
> \({\sim}(x) \ldotp {\phi}x \ldotp = \ldotp {\sim}\{(x) \ldotp {\phi}x\} \quad \text{Df}\text{.}\)
> […] Thus we put
> \({\sim}\{(x) \ldotp {\phi}x\} \ldotp = \ldotp (\exists x) \ldotp {\sim}{\phi}x \quad \text{Df}\text{,}\)
> \({\sim}\{(\exists x) \ldotp {\phi}x\} \ldotp = \ldotp (x) \ldotp {\sim}{\phi}x \quad \text{Df}\text{.}\)
> In like manner we define a disjunction in which one of the propositions is of the form
> "\((x) \ldotp {\phi}x\)" or "(\(\exists x) \ldotp{\phi}x\)" in terms of a disjunction of
> propositions not of this form, putting
> \((x) \ldotp {\phi}x \ldotp \lor \ldotp p \colon = \ldotp (x) \ldotp {\phi}x \lor p \quad \text{Df}\text{,}\)
> […] Thus in the above instance, since we have \(\vdash \ldotp x = x\) we may infer
> \(\vdash \ldotp (x) \ldotp x = x.\) […] Our definition gives
> \({\sim}\{(x) . x = a\}. = .(\exists x). {\sim}(x = a) \qquad \text{Df.}\) […]
> (Chapter II:) Similarly we will define \(\unicode{x201c}p \ldotp \lor \ldotp (\exists x) \ldotp {\phi}x\unicode{x201d}\)
> as meaning "\((\exists x) \ldotp p \lor {\phi}x\)," […] "\((x) \ldotp {\phi}x \ldotp \lor \ldotp (y)\ldotp {\psi}y\)"
> will be defined as meaning "\((x, y) \ldotp {\phi}x \lor {\psi}y\),"

**Lean reading.** Lean's `¬`, `∨` apply to propositions of every order, so these Dfs (✱9·01–✱9·06
of the body; `∼(x).φx` is ✱9·011, a notation) become equivalences, proved as in ✱9 (Basic §3). `p ∨ (∃x).φx ≡ (∃x).(p ∨ φx)` needs
a member of the type, and fails for the empty type. Ch. II's "second truth" of `(x).φx` ("every
value has first truth") and "second falsehood" ("some value has first falsehood") are the first
two equivalences read with truth as Lean's `Prop`.

**Status.** complete. proved (reading): the Dfs become equivalences of Lean's connectives;
`p ∨ (∃x).φx` with `[Nonempty α]` (PM assumes every type has a member), its failure for the empty
type proved.
-/

/-- Intro, Ch. I: \({\sim}\{(x) \ldotp {\phi}x\} \ldotp = \ldotp (\exists x) \ldotp {\sim}{\phi}x\)
(✱9·01).

**Status.** proved (reading): a Df of PM, an equivalence of Lean's connectives. -/
theorem not_forall_def {φ : α → Prop} : ¬(∀ x, φ x) ↔ ∃ x, ¬φ x := not_forall

/-- Intro, Ch. I: \({\sim}\{(\exists x) \ldotp {\phi}x\} \ldotp = \ldotp (x) \ldotp {\sim}{\phi}x\)
(✱9·02).

**Status.** proved (reading): a Df of PM, an equivalence of Lean's connectives. -/
theorem not_exists_def {φ : α → Prop} : ¬(∃ x, φ x) ↔ ∀ x, ¬φ x := not_exists

/-- Intro, Ch. I: \((x) \ldotp {\phi}x \ldotp \lor \ldotp p \colon = \ldotp (x) \ldotp {\phi}x \lor p\)
(✱9·03), and Ch. II's \(p \ldotp \lor \ldotp (x) \ldotp {\phi}x\) defined as
\((x) \ldotp p \lor {\phi}x\) (✱9·04).

**Status.** proved (reading): Dfs of PM, equivalences of Lean's connectives. -/
theorem forall_or_def {φ : α → Prop} {p : Prop} :
    ((∀ x, φ x) ∨ p ↔ ∀ x, φ x ∨ p) ∧ (p ∨ (∀ x, φ x) ↔ ∀ x, p ∨ φ x) :=
  ⟨forall_or_right.symm, forall_or_left.symm⟩

/-- Intro, Ch. II: \(p \ldotp \lor \ldotp (\exists x) \ldotp {\phi}x\) defined as
\((\exists x) \ldotp p \lor {\phi}x\) (✱9·06).

**Status.** proved (reading): a Df of PM, an equivalence of Lean's connectives; PM assumes every
type has a member, `[Nonempty α]` (`or_exists_def_fails` for the empty type). -/
theorem or_exists_def [Nonempty α] {φ : α → Prop} {p : Prop} :
    (p ∨ ∃ x, φ x) ↔ ∃ x, p ∨ φ x := by
  constructor
  · rintro (h | ⟨x, hx⟩)
    · obtain ⟨x⟩ := ‹Nonempty α›
      exact ⟨x, Or.inl h⟩
    · exact ⟨x, Or.inr hx⟩
  · rintro ⟨x, h | h⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, h⟩

/-- Intro, Ch. II: for the empty type the definiens of \(p \ldotp \lor \ldotp (\exists x) \ldotp
{\phi}x\) is not equivalent to it. -/
theorem or_exists_def_fails :
    ¬ ∀ (φ : Empty → Prop) (p : Prop), (p ∨ ∃ x, φ x) ↔ ∃ x, p ∨ φ x :=
  fun h => ((h (fun _ => True) True).1 (Or.inl trivial)).elim fun x _ => x.elim

/-- Intro, Ch. II: \((x) \ldotp {\phi}x \ldotp \lor \ldotp (y)\ldotp {\psi}y\) defined as
\((x, y) \ldotp {\phi}x \lor {\psi}y\).

**Status.** proved (reading): a definition of Ch. II (derived in ✱9), an equivalence of Lean's
connectives. -/
theorem forall_or_forall_def {φ : α → Prop} {ψ : β → Prop} :
    ((∀ x, φ x) ∨ ∀ y, ψ y) ↔ ∀ x y, φ x ∨ ψ y := by
  constructor
  · rintro (h | h) x y
    · exact Or.inl (h x)
    · exact Or.inr (h y)
  · intro h
    by_contra hc
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := not_or.1 hc |>.imp not_forall.1 not_forall.1
    exact (h x y).elim hx hy

/-- Intro, Ch. I: \({\sim}\{(x) . x = a\}. = .(\exists x). {\sim}(x = a)\).

**Status.** proved (reading): an instance of `not_forall_def`. -/
theorem not_forall_eq_def {a : α} : ¬(∀ x, x = a) ↔ ∃ x, ¬(x = a) := not_forall

/-- Intro, Ch. I: since we have \(\vdash \ldotp x = x\), we may infer \(\vdash \ldotp (x) \ldotp
x = x\). -/
theorem all_eq_self : ∀ x : α, x = x := fun _ => rfl

/-- Intro, Ch. I: \(\vdash \ldotp (\exists x) \ldotp x = x\), cited as an assertion of "*some*
value".

**Status.** proved (reading): PM assumes every type has a member; `[Nonempty α]`. -/
theorem some_eq_self [Nonempty α] : ∃ x : α, x = x := let ⟨x⟩ := ‹Nonempty α›; ⟨x, rfl⟩

/-!
## [intro.real-apparent] Propositions connecting real and apparent variables

*(Vol. 1, Introduction, Chapter I, "Propositions connecting real and apparent variables")*

> (2) "What holds of all, holds of any," *i.e.* \(\vdash \colon (x). \phi x . \supset . \phi y.\)
> […] (3) "If \(\phi y\) is true, then \(\phi x\) is sometimes true," *i.e.*
> \(\vdash \colon \phi y . \supset . (\exists x). \phi x.\) […] we have
> "\(\vdash \colon (x) . \phi x . \supset . (\exists x). \phi x\)," *i.e.* "what is always true
> is sometimes true." This would not be the case if nothing existed; thus our assumptions contain
> the assumption that there is something. […] (4) […]
> \(\vdash \colon\ldotp (x) . \phi x \colon (x) . \psi x : \supset . (x) . \phi x . \psi x.\) […]
> The converse also holds […] The primitive propositions assumed, on this subject, in the body of
> the work (*9), are the following: (1) \(\vdash \colon \phi x . \supset. (\exists z) . \phi z.\)
> (2) \(\vdash \colon \phi x \lor \phi y. \supset . (\exists z) . \phi z\) […]

**Lean reading.** Real variables are arguments (Basic §3). "What is always true is sometimes true"
needs a member of the type: proved with `[Nonempty α]`, and its failure for the empty type is
proved, which is exactly PM's remark that the principle "would not be the case if nothing
existed". The rules (1) and (3) of the first list (generalization) are Lean's `fun x => …`, as in
✱9·13; they have no separate declaration.

**Status.** complete. `(x).φx ⊃ (∃x).φx` proved (reading) (`[Nonempty α]`); the rest proved.
-/

/-- Intro, Ch. I: "what holds of all, holds of any." \(\vdash \colon (x). \phi x . \supset . \phi y.\) -/
theorem all_to_any {φ : α → Prop} {y : α} : (∀ x, φ x) → φ y := fun h => h y

/-- Intro, Ch. I: \(\vdash \colon \phi y . \supset . (\exists x). \phi x.\) -/
theorem any_to_some {φ : α → Prop} {y : α} : φ y → ∃ x, φ x := fun h => ⟨y, h⟩

/-- Intro, Ch. I: "what is always true is sometimes true."
\(\vdash \colon (x) . \phi x . \supset . (\exists x). \phi x\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I: "our
assumptions contain the assumption that there is something"); `[Nonempty α]`. -/
theorem always_to_sometimes [Nonempty α] {φ : α → Prop} : (∀ x, φ x) → ∃ x, φ x :=
  fun h => let ⟨y⟩ := ‹Nonempty α›; ⟨y, h y⟩

/-- Intro, Ch. I: "This would not be the case if nothing existed": for the empty type,
`(x).φx ⊃ (∃x).φx` fails. -/
theorem always_to_sometimes_fails_if_nothing_exists :
    ¬ ∀ φ : Empty → Prop, (∀ x, φ x) → ∃ x, φ x :=
  fun h => (h (fun _ => True) (fun x => x.elim)).elim fun x _ => x.elim

/-- Intro, Ch. I, (4). \(\vdash \colon\ldotp (x) . \phi x \colon (x) . \psi x : \supset . (x) . \phi x . \psi x.\) -/
theorem forall_and_of_and {φ ψ : α → Prop} : (∀ x, φ x) ∧ (∀ x, ψ x) → ∀ x, φ x ∧ ψ x :=
  fun h x => ⟨h.1 x, h.2 x⟩

/-- Intro, Ch. I, converse of (4).
\(\vdash \colon\ldotp (x) . \phi x . \psi x . \supset \colon (x) . \phi x : (x) . \psi x.\) -/
theorem and_of_forall_and {φ ψ : α → Prop} : (∀ x, φ x ∧ ψ x) → (∀ x, φ x) ∧ (∀ x, ψ x) :=
  fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩

/-- Intro, Ch. I, the first primitive proposition of ✱9 (✱9·1).
\(\vdash \colon \phi x . \supset. (\exists z) . \phi z.\) -/
theorem pp_exists {φ : α → Prop} {x : α} : φ x → ∃ z, φ z := fun h => ⟨x, h⟩

/-- Intro, Ch. I, the second primitive proposition of ✱9 (✱9·11).
\(\vdash \colon \phi x \lor \phi y. \supset . (\exists z) . \phi z\) -/
theorem pp_exists_or {φ : α → Prop} {x y : α} : φ x ∨ φ y → ∃ z, φ z :=
  fun h => h.elim (fun h => ⟨x, h⟩) (fun h => ⟨y, h⟩)

/-!
## [intro.formal-equivalence] Formal equivalence and extensional functions

*(Vol. 1, Introduction, Chapter I, "Formal implication and formal equivalence")*

> In virtue of what was said about truth-values, if \(\phi x\) and \(\psi x\) are formally
> equivalent, either may replace the other in any truth-function. Hence for all the purposes of
> mathematics or of the present work, \(\phi \hat{z}\) may replace \(\psi \hat{z}\) or vice
> versa in any proposition with which we shall be concerned. […] A proposition containing a
> function \(\phi \hat{z}\) and having this property […] will be called an *extensional*
> function of \(\phi \hat{z}\).

**Lean reading.** `φ x ≡_x ψ x` is `∀ x, φ x ↔ ψ x`. By function and propositional extensionality
formally equivalent functions are equal, so *every* function of functions `f : (α → Prop) → Prop`
is extensional in Lean.

**Status.** complete. proved (reading): stated for every function of functions, PM's "any
proposition with which we shall be concerned".
-/

/-- Intro, Ch. I: formally equivalent functions may replace each other in any proposition.

**Status.** proved (reading): PM claims this for the functions of functions it deals with
(extensional ones, as opposed to "A believes …"); in Lean every function of functions is
extensional (function and propositional extensionality), so it is proved for every `f`. -/
theorem formal_equiv_subst (f : (α → Prop) → Prop) {φ ψ : α → Prop} (h : ∀ x, φ x ↔ ψ x) :
    f φ ↔ f ψ := by
  rw [show φ = ψ from funext fun x => propext (h x)]

/-!
## [intro.identity] Identity

*(Vol. 1, Introduction, Chapter I, "Identity")*

> We have, of course, \(\vdash . x = x\,\, \text{(the law of identity)}\),
> \(\vdash \colon x = y . \equiv . y = x\), \(\vdash : x = y . y = z . \supset . x = z.\) […] If
> \(x\) and \(y\) are identical, either can replace the other in any proposition without altering
> the truth-value of the proposition; thus we have
> \(\vdash \colon x = y \ldotp \supset \ldotp {\phi}x \equiv {\phi}y.\)

**Lean reading.** PM's `=` is Lean's `Eq` (Basic §5; ✱13).

**Status.** complete. All proved.
-/

/-- Intro, Ch. I: the law of identity. \(\vdash . x = x\) -/
theorem identity_refl {x : α} : x = x := rfl

/-- Intro, Ch. I. \(\vdash \colon x = y . \equiv . y = x\) -/
theorem identity_symm {x y : α} : x = y ↔ y = x := eq_comm

/-- Intro, Ch. I. \(\vdash : x = y . y = z . \supset . x = z.\) -/
theorem identity_trans {x y z : α} : x = y ∧ y = z → x = z := fun h => h.1.trans h.2

/-- Intro, Ch. I. \(\vdash \colon x = y \ldotp \supset \ldotp {\phi}x \equiv {\phi}y.\) -/
theorem identity_subst {φ : α → Prop} {x y : α} : x = y → (φ x ↔ φ y) := fun h => h ▸ Iff.rfl

/-!
## [intro.classes] Classes

*(Vol. 1, Introduction, Chapter I, "Classes and relations")*

> We have \(\vdash \colon x \in \hat{z}({\phi}z) \ldotp \equiv \ldotp {\phi}x\text{,}\) […] Thus
> we have \(\vdash \colon\ldotp \hat{z}({\phi}z) = \hat{z}({\psi}z) \ldotp \equiv \colon {\phi}x
> \ldotp \equiv_{x} \ldotp {\psi}x\text{.}\) The following propositions are obvious and
> important: \(\vdash \colon \ldotp \alpha = \hat{z}({\phi}z) \ldotp \equiv \colon x \in \alpha
> \ldotp \equiv_{x} \ldotp {\phi}x\text{,}\) […] \(\vdash \colon \ldotp \alpha = \beta \ldotp
> \equiv \colon x \in \alpha \ldotp \equiv_{x} \ldotp x \in \beta\text{,}\) […]
> \(\vdash \ldotp \hat{x}(x \in \alpha) = \alpha\text{,}\) […] \(\vdash \ldotp \hat{z}({\phi}z)
> \in \text{Cls}\text{,}\) […] It will be seen that, according to the above, any function of
> one variable can be replaced by an equivalent function of the form "\(x \in \alpha\)."

**Lean reading.** Classes are `Set α` (Basic §6): `ẑ(φz)` is `{z | φ z}`, `Cls` is the Defs
`Cls`.

**Status.** complete. All proved.
-/

/-- Intro, Ch. I. \(\vdash \colon x \in \hat{z}({\phi}z) \ldotp \equiv \ldotp {\phi}x\) -/
theorem mem_class {φ : α → Prop} {x : α} : x ∈ {z | φ z} ↔ φ x := Iff.rfl

/-- Intro, Ch. I. \(\vdash \colon\ldotp \hat{z}({\phi}z) = \hat{z}({\psi}z) \ldotp \equiv \colon {\phi}x \ldotp \equiv_{x} \ldotp {\psi}x\) -/
theorem class_eq_class {φ ψ : α → Prop} : {z | φ z} = {z | ψ z} ↔ ∀ x, φ x ↔ ψ x :=
  setOf_eq_setOf_iff

/-- Intro, Ch. I. \(\vdash \colon \ldotp \alpha = \hat{z}({\phi}z) \ldotp \equiv \colon x \in \alpha \ldotp \equiv_{x} \ldotp {\phi}x\) -/
theorem eq_class {A : Set α} {φ : α → Prop} : A = {z | φ z} ↔ ∀ x, x ∈ A ↔ φ x :=
  set_eq_iff

/-- Intro, Ch. I: classes with the same membership are identical.
\(\vdash \colon \ldotp \alpha = \beta \ldotp \equiv \colon x \in \alpha \ldotp \equiv_{x} \ldotp x \in \beta\) -/
theorem class_ext {A B : Set α} : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B := set_eq_iff

/-- Intro, Ch. I. \(\vdash \ldotp \hat{x}(x \in \alpha) = \alpha\) -/
theorem class_of_members {A : Set α} : {x | x ∈ A} = A := rfl

/-- Intro, Ch. I. \(\vdash \ldotp \hat{z}({\phi}z) \in \text{Cls}\) -/
theorem class_mem_Cls {φ : α → Prop} : {z | φ z} ∈ (Cls : Set (Set α)) := ⟨φ, rfl⟩

/-- Intro, Ch. I: any function of one variable can be replaced by an equivalent function of the
form "`x ∈ α`". -/
theorem function_eq_membership (φ : α → Prop) : ∃ A : Set α, ∀ x, φ x ↔ x ∈ A :=
  ⟨{x | φ x}, fun _ => Iff.rfl⟩

/-!
## [intro.relations] Relations in extension

*(Vol. 1, Introduction, Chapter I, "Classes and relations")*

> Owing to our taking relations in extension, we shall have \(\vdash \colon\ldotp
> \hat{x}\hat{y} \phi(x,y) = \hat{x}\hat{y} \psi(x,y).\equiv \colon \phi(x,y). \equiv_{x,y} .
> \psi(x,y),\) […] We have \(\vdash. z \{\hat{x}\hat{y} \phi(x,y)\} w . \equiv . \phi(z,w),\)
> […] \(\vdash \colon\ldotp R = \hat{x}\hat{y} \phi(x,y). \equiv \colon xRy. \equiv_{x,y} .
> \phi(x,y),\) \(\vdash \colon\ldotp R = S .\equiv \colon xRy. \equiv_{x,y} . xSy,\)
> \(\vdash . \hat{x}\hat{y} (xRy) = R,\) \(\vdash . \{\hat{x}\hat{y} \phi(x,y)\} \in\,
> \text{Rel}.\) […] It results from them that any function of two variables is formally
> equivalent to some function of the form \(xRy\).

**Lean reading.** Relations are `α → β → Prop` (Basic §6); `x̂ŷ φ(x, y)` is `fun x y => φ x y`.

**Status.** complete. All proved.
-/

/-- Intro, Ch. I. \(\vdash \colon\ldotp \hat{x}\hat{y} \phi(x,y) = \hat{x}\hat{y} \psi(x,y).\equiv \colon \phi(x,y). \equiv_{x,y} . \psi(x,y)\) -/
theorem rel_eq_rel {φ ψ : α → β → Prop} :
    (fun x y => φ x y) = (fun x y => ψ x y) ↔ ∀ x y, φ x y ↔ ψ x y :=
  rel_eq_iff

/-- Intro, Ch. I. \(\vdash. z \{\hat{x}\hat{y} \phi(x,y)\} w . \equiv . \phi(z,w)\) -/
theorem rel_apply {φ : α → β → Prop} {z : α} {w : β} : (fun x y => φ x y) z w ↔ φ z w := Iff.rfl

/-- Intro, Ch. I. \(\vdash \colon\ldotp R = \hat{x}\hat{y} \phi(x,y). \equiv \colon xRy. \equiv_{x,y} . \phi(x,y)\) -/
theorem eq_rel {R : α → β → Prop} {φ : α → β → Prop} :
    R = (fun x y => φ x y) ↔ ∀ x y, R x y ↔ φ x y :=
  rel_eq_iff

/-- Intro, Ch. I. \(\vdash \colon\ldotp R = S .\equiv \colon xRy. \equiv_{x,y} . xSy\) -/
theorem rel_ext {R S : α → β → Prop} : R = S ↔ ∀ x y, R x y ↔ S x y := rel_eq_iff

/-- Intro, Ch. I. \(\vdash . \hat{x}\hat{y} (xRy) = R\) -/
theorem rel_of_pairs {R : α → β → Prop} : (fun x y => R x y) = R := rfl

/-- Intro, Ch. I. \(\vdash . \{\hat{x}\hat{y} \phi(x,y)\} \in\, \text{Rel}\) -/
theorem rel_mem_Rel {φ : α → β → Prop} : (fun x y => φ x y) ∈ (Rel : Set (α → β → Prop)) :=
  ⟨φ, rfl⟩

/-- Intro, Ch. I: any function of two variables is formally equivalent to some function of the
form `xRy`. -/
theorem function_eq_relation (φ : α → β → Prop) : ∃ R : α → β → Prop, ∀ x y, φ x y ↔ R x y :=
  ⟨φ, fun _ _ => Iff.rfl⟩

/-!
## [intro.class-calculus] The calculus of classes and relations; existence, `V`, `Λ`

*(Vol. 1, Introduction, Chapter I, "Classes and relations")*

> This gives us \(\vdash \colon x \in \alpha \cap \beta . \equiv . x \in \alpha . x \in \beta,\)
> […] \(\vdash \colon\ldotp x \in \alpha \cup \beta . \equiv \colon x \in \alpha . \lor . x \in
> \beta.\) […] \(\vdash \colon x \in -\alpha . \equiv . x {\sim \in \alpha}.\) […] In place of
> equivalence, we substitute identity; for […] "\(\alpha \subset \beta . \beta \subset \alpha\)"
> gives "\(x \in \alpha . \equiv_{x} . x \in\beta\)," whence \(\alpha = \beta\). […]
> \(\vdash \ldotp \alpha \cap \beta = -(-\alpha \cup -\beta)\text{,}\) […]
> \(\vdash \ldotp x \in (\alpha \cup -\alpha)\text{,}\) […] \(\vdash \ldotp x \sim\in(\alpha \cap
> -\alpha),\) […] \(\vdash \ldotp \alpha = -(-\alpha)\text{,}\) \(\vdash \colon \alpha \subset
> \beta \ldotp \equiv \ldotp -\beta \subset -\alpha\text{,}\) \(\vdash \colon \alpha = \beta
> \ldotp \equiv \ldotp -\alpha = -\beta\text{,}\) \(\vdash \colon \alpha = \alpha \cap
> \alpha\text{,}\) \(\vdash \colon \alpha = \alpha \cup \alpha\text{.}\) […] The law of
> absorption holds in the form \(\vdash \colon \alpha \subset \beta \ldotp \equiv \ldotp \alpha =
> \alpha \cap \beta\text{.}\) […] Just as we have \(\vdash \colon p \supset q \ldotp q \supset r
> \ldotp \supset \ldotp p \supset r,\) so we have \(\vdash \colon \alpha \subset \beta \ldotp \beta
> \subset \gamma \ldotp \supset \ldotp \alpha \subset \gamma.\) […] \(\vdash \colon x \in \beta \ldotp \beta
> \subset \gamma \ldotp \supset \ldotp x \in \gamma\text{,}\) […] \(\vdash \colon x (R
> \dot{\cap} S) y \ldotp \equiv \ldotp xRy \ldotp xSy.\) […] \(\Lambda = \hat{x}(x \neq x)
> \quad \text{Df}\text{.}\) […] \(\text{V} = \hat{x}(x = x) \quad \text{Df}\text{.}\) Thus
> \(\Lambda\) is the negation of \(\text{V}\). We have \(\vdash \ldotp (x) \ldotp x \in
> \text{V}\text{,}\) […] \(\vdash \ldotp (x) \ldotp x
> {\sim}\in \Lambda,\) […] \(\vdash \colon \alpha = \Lambda \ldotp \equiv \ldotp {\sim}\exists!
> \alpha\text{,}\) […] \(\dot{\Lambda}\) will be the relation \(\hat{x}\hat{y}(x \neq x . y \neq
> y)\). We have \(\vdash \ldotp (x, y) \ldotp {\sim}(x \dot{\Lambda} y),\) and \(\vdash \colon R
> = \dot{\Lambda} \ldotp \equiv \ldotp {\sim}\dot{\exists}! R\text{.}\) There are no classes
> which contain objects of more than one type.

**Lean reading.** Basic §6: `⊂` is `⊆`, `−α` is `Aᶜ`, `∃!α` is `A.Nonempty`, the dotted signs are
`⩀ ⊍ ∸ ⪽`. The Introduction defines `Λ` as `x̂(x ≠ x)` and `Λ̇` as `x̂ŷ(x ≠ x . y ≠ y)`, whereas
✱24·02 and ✱25·02 define them as `−V` and `−̇V̇` (the Defs): the two definitions are proved to
agree. "No classes contain objects of more than one type" is Lean's typing (`Set α` has members
of type `α` only).

**Status.** complete. All proved; the Introduction's definitions of `Λ`, `Λ̇` proved (reading)
(equal to the Defs).
-/

/-- Intro, Ch. I. \(\vdash \colon x \in \alpha \cap \beta . \equiv . x \in \alpha . x \in \beta\) -/
theorem mem_inter {A B : Set α} {x : α} : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := Iff.rfl

/-- Intro, Ch. I. \(\vdash \colon\ldotp x \in \alpha \cup \beta . \equiv \colon x \in \alpha . \lor . x \in \beta\) -/
theorem mem_union {A B : Set α} {x : α} : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := Iff.rfl

/-- Intro, Ch. I. \(\vdash \colon x \in -\alpha . \equiv . x {\sim \in \alpha}\) -/
theorem mem_compl {A : Set α} {x : α} : x ∈ Aᶜ ↔ x ∉ A := Iff.rfl

/-- Intro, Ch. I: mutual inclusion gives identity (the analogue of `p ≡ q . = . p ⊃ q . q ⊃ p`). -/
theorem subset_antisymm_iff {A B : Set α} : A ⊆ B ∧ B ⊆ A ↔ A = B :=
  ⟨fun h => Set.Subset.antisymm h.1 h.2, fun h => h ▸ ⟨subset_rfl, subset_rfl⟩⟩

/-- Intro, Ch. I. \(\vdash \ldotp \alpha \cap \beta = -(-\alpha \cup -\beta)\) -/
theorem inter_eq_compl_union {A B : Set α} : A ∩ B = (Aᶜ ∪ Bᶜ)ᶜ := by
  rw [Set.compl_union, compl_compl, compl_compl]

/-- Intro, Ch. I. \(\vdash \ldotp x \in (\alpha \cup -\alpha)\) -/
theorem mem_union_compl_self {A : Set α} {x : α} : x ∈ A ∪ Aᶜ := Classical.em (x ∈ A)

/-- Intro, Ch. I. \(\vdash \ldotp x \sim\in(\alpha \cap -\alpha)\) -/
theorem not_mem_inter_compl_self {A : Set α} {x : α} : x ∉ A ∩ Aᶜ := fun h => h.2 h.1

/-- Intro, Ch. I. \(\vdash \ldotp \alpha = -(-\alpha)\) -/
theorem eq_compl_compl {A : Set α} : A = Aᶜᶜ := (compl_compl A).symm

/-- Intro, Ch. I. \(\vdash \colon \alpha \subset \beta \ldotp \equiv \ldotp -\beta \subset -\alpha\) -/
theorem subset_iff_compl_subset {A B : Set α} : A ⊆ B ↔ Bᶜ ⊆ Aᶜ :=
  Set.compl_subset_compl.symm

/-- Intro, Ch. I. \(\vdash \colon \alpha = \beta \ldotp \equiv \ldotp -\alpha = -\beta\) -/
theorem eq_iff_compl_eq {A B : Set α} : A = B ↔ Aᶜ = Bᶜ := compl_inj_iff.symm

/-- Intro, Ch. I: the law of tautology for classes. \(\vdash \colon \alpha = \alpha \cap \alpha\) -/
theorem eq_inter_self {A : Set α} : A = A ∩ A := (Set.inter_self A).symm

/-- Intro, Ch. I: the law of tautology for classes. \(\vdash \colon \alpha = \alpha \cup \alpha\) -/
theorem eq_union_self {A : Set α} : A = A ∪ A := (Set.union_self A).symm

/-- Intro, Ch. I: the law of absorption for classes.
\(\vdash \colon \alpha \subset \beta \ldotp \equiv \ldotp \alpha = \alpha \cap \beta\) -/
theorem class_absorption {A B : Set α} : A ⊆ B ↔ A = A ∩ B := by
  rw [eq_comm, Set.inter_eq_left]

/-- Intro, Ch. I: the syllogism in Barbara.
\(\vdash \colon \alpha \subset \beta \ldotp \beta \subset \gamma \ldotp \supset \ldotp \alpha \subset \gamma\) -/
theorem barbara {A B G : Set α} : A ⊆ B ∧ B ⊆ G → A ⊆ G := fun h => h.1.trans h.2

/-- Intro, Ch. I: the syllogism for propositions, of which Barbara is the analogue (✱3·33).
\(\vdash \colon p \supset q \ldotp q \supset r \ldotp \supset \ldotp p \supset r\) -/
theorem syll_prop {p q r : Prop} : (p → q) ∧ (q → r) → (p → r) := fun h hp => h.2 (h.1 hp)

/-- Intro, Ch. I: Barbara with an individual subject in the minor premiss (which is not a
particular case of the previous one).
\(\vdash \colon x \in \beta \ldotp \beta \subset \gamma \ldotp \supset \ldotp x \in \gamma\) -/
theorem barbara_individual {B G : Set α} {x : α} : x ∈ B ∧ B ⊆ G → x ∈ G := fun h => h.2 h.1

/-- Intro, Ch. I: the dotted signs for relations.
\(\vdash \colon x (R \dot{\cap} S) y \ldotp \equiv \ldotp xRy \ldotp xSy\), and likewise for
`∪̇`, `−̇`, `⊂̇`. -/
theorem rel_calculus {R S : α → β → Prop} {x : α} {y : β} :
    (((R ⩀ S) x y ↔ R x y ∧ S x y) ∧ ((R ⊍ S) x y ↔ R x y ∨ S x y)) ∧ ((∸R) x y ↔ ¬R x y) ∧
      (R ⪽ S ↔ ∀ x y, R x y → S x y) :=
  ⟨⟨Iff.rfl, Iff.rfl⟩, Iff.rfl, Iff.rfl⟩

/-- Intro, Ch. I: the Introduction's definition \(\Lambda = \hat{x}(x \neq x)\).

**Status.** proved (reading): the Introduction defines `Λ` as `x̂(x ≠ x)`, ✱24·02 as `−V`; they
are the same class. -/
theorem null_eq_ne_self : (Λ : Set α) = {x | x ≠ x} := by
  ext x; simp [Null, V]

/-- Intro, Ch. I: \(\text{V} = \hat{x}(x = x)\), as ✱24·01. -/
theorem V_def : (V : Set α) = {x | x = x} := rfl

/-- Intro, Ch. I: "\(\Lambda\) is the negation of \(\text{V}\)" (✱24·02). -/
theorem Null_eq_compl_V : (Λ : Set α) = Vᶜ := rfl

/-- Intro, Ch. I. \(\vdash \ldotp (x) \ldotp x \in \text{V}\) -/
theorem mem_V : ∀ x : α, x ∈ (V : Set α) := fun _ => rfl

/-- Intro, Ch. I. \(\vdash \ldotp (x) \ldotp x {\sim}\in \Lambda\) -/
theorem not_mem_null : ∀ x : α, x ∉ (Λ : Set α) := fun _ h => h rfl

/-- Intro, Ch. I. \(\vdash \colon \alpha = \Lambda \ldotp \equiv \ldotp {\sim}\exists! \alpha\) -/
theorem eq_null_iff {A : Set α} : A = Λ ↔ ¬A.Nonempty := by
  rw [Null_eq_empty, Set.not_nonempty_iff_eq_empty]

/-- Intro, Ch. I: the Introduction's \(\dot{\Lambda} = \hat{x}\hat{y}(x \neq x . y \neq y)\).

**Status.** proved (reading): the Introduction's definition of `Λ̇` agrees with ✱25·02 (`−̇V̇`). -/
theorem rNull_eq_ne_self : (rNull : α → β → Prop) = fun x y => x ≠ x ∧ y ≠ y := by
  funext x y
  exact propext ⟨fun h => (h ⟨rfl, rfl⟩).elim, fun h => (h.1 rfl).elim⟩

/-- Intro, Ch. I. \(\vdash \ldotp (x, y) \ldotp {\sim}(x \dot{\Lambda} y)\) -/
theorem not_rNull : ∀ (x : α) (y : β), ¬rNull x y := rNull_apply

/-- Intro, Ch. I. \(\vdash \colon R = \dot{\Lambda} \ldotp \equiv \ldotp {\sim}\dot{\exists}! R\) -/
theorem eq_rNull_iff {R : α → β → Prop} : R = rNull ↔ ¬rEx R := by
  constructor
  · rintro rfl ⟨x, y, h⟩
    exact h ⟨rfl, rfl⟩
  · intro h
    funext x y
    exact propext ⟨fun hr => (h ⟨x, y, hr⟩).elim, fun hn => (hn ⟨rfl, rfl⟩).elim⟩

/-!
## [intro.descriptions] Descriptions: existence

*(Vol. 1, Introduction, Chapter I, "Descriptions")*

> \(\text{E}! ({℩}x) (\phi x) . =: (\exists c): \phi x . \equiv_{x} . x = c\quad \text{Df,}\)
> […] The following are equivalent forms:
> \(\vdash \colon\ldotp \text{E}! ({℩}x) (\phi x) . \equiv : (\exists c) : \phi c : \phi x .
> \supset_{x} . x = c,\)
> \(\vdash \colon\ldotp \text{E}! ({℩}x) (\phi x) . \equiv : (\exists c) . \phi c : \phi x .
> \phi y . \supset_{x, y} . x = y,\)
> \(\vdash \colon\ldotp \text{E}! ({℩}x) (\phi x) . \equiv : (\exists c) : \phi c : x \neq c .
> \supset_{x} . \sim\phi x.\)

**Lean reading.** `E!(℩x)(φx)` is `EBang φ` (✱14·02, Basic §5). In the second form, `(∃c) . φc`
has one dot, so the two-dot product sign ends its scope: `(∃ c, φ c) ∧ ∀ x y, φ x ∧ φ y → x = y`.

**Status.** complete. All proved.
-/

/-- Intro, Ch. I.
\(\vdash \colon\ldotp \text{E}! ({℩}x) (\phi x) . \equiv : (\exists c) : \phi c : \phi x . \supset_{x} . x = c\) -/
theorem EBang_iff_exists_forall {φ : α → Prop} : EBang φ ↔ ∃ c, φ c ∧ ∀ x, φ x → x = c := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (hc c).2 rfl, fun x hx => (hc x).1 hx⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, fun x => ⟨h x, fun e => by subst e; exact hc⟩⟩

/-- Intro, Ch. I.
\(\vdash \colon\ldotp \text{E}! ({℩}x) (\phi x) . \equiv : (\exists c) . \phi c : \phi x . \phi y . \supset_{x, y} . x = y\) -/
theorem EBang_iff_exists_unique {φ : α → Prop} :
    EBang φ ↔ (∃ c, φ c) ∧ ∀ x y, φ x ∧ φ y → x = y := by
  rw [EBang_iff_exists_forall]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨⟨c, hc⟩, fun x y hxy => (h x hxy.1).trans (h y hxy.2).symm⟩
  · rintro ⟨⟨c, hc⟩, h⟩
    exact ⟨c, hc, fun x hx => h x c ⟨hx, hc⟩⟩

/-- Intro, Ch. I.
\(\vdash \colon\ldotp \text{E}! ({℩}x) (\phi x) . \equiv : (\exists c) : \phi c : x \neq c . \supset_{x} . \sim\phi x\) -/
theorem EBang_iff_exists_ne {φ : α → Prop} : EBang φ ↔ ∃ c, φ c ∧ ∀ x, x ≠ c → ¬φ x := by
  rw [EBang_iff_exists_forall]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun x hne hx => hne (h x hx)⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun x hx => Classical.byContradiction fun hne => h x hne hx⟩

/-!
## [intro.descriptive-functions] Descriptive functions of relations

*(Vol. 1, Introduction, Chapter I, "Various descriptive functions of relations")*

> The converse of \(R\) is written […] \(\text{Cnv}ʻR\) or \(\breve{R}\). The definition is
> \(\breve{R} = \hat{x}\hat{y} (yRx) \quad \text{Df},\) \(\text{Cnv}ʻR = \breve{R} \quad
> \text{Df}.\) […] A relation is called *symmetrical* if \(R = \breve{R}\), *i.e.* if it holds
> between \(y\) and \(x\) whenever it holds between \(x\) and \(y\) (and therefore vice versa).
> Identity, diversity, agreement or disagreement in any respect, are symmetrical relations. A
> relation is called *asymmetrical* when it is incompatible with its converse, *i.e.* when
> \(R \dot{\cap}\breve{R} = \dot{\Lambda}\), or, what is equivalent,
> \(xRy . \supset_{x, y} . \sim{(yRx)}.\) […] A relation maybe neither symmetrical nor
> asymmetrical; for example, this holds of the relation of inclusion between classes:
> \(\alpha \subset \beta\) and \(\beta \subset \alpha\) will both be true if \(\alpha = \beta\),
> but otherwise only one of them, at most, will be true. […] We have \(\vdash \colon x \in
> \overrightarrow{R}ʻy . \equiv . xRy\) and \(\vdash \colon y \in \overleftarrow{R}ʻx . \equiv .
> xRy.\) […] \(\text{sg}ʻR = \overrightarrow{R} \qquad \text{Df}\) […]
> \(\text{D}ʻR = \hat{x} \{(\exists y) . xRy\} \qquad \text{Df}.\) Similarly the class of all
> terms to which something or other has the relation \(R\) is called the *converse domain* of
> \(R\); it is the same as the domain of the converse of \(R\). The converse domain of \(R\) is
> represented by "\(\text{ᗡ}ʻR\)"; thus \(\text{ᗡ}ʻR = \hat{y} \{(\exists x) . xRy\} \qquad
> \text{Df}.\) […] \(CʻR = \text{D}ʻR \cup
> \text{ᗡ}ʻR \qquad \text{Df}.\) […] The condition that a series should have no end is
> \(\text{ᗡ}ʻR \subset \text{D}ʻR\) […] the condition for no beginning is \(\text{D}ʻR \subset
> \text{ᗡ}ʻR\). These conditions are equivalent respectively to \(\text{D}ʻR = CʻR\) and
> \(\text{ᗡ}ʻR = CʻR\).

**Lean reading.** Descriptive functions are read by `Desc` (Basic §5): `Cnv'R`, `R⃗'y`, `sg'R`
are stated with `Desc` so as to keep their content (that the description exists and has the
value claimed). The Introduction defines `C'R` as `D'R ∪ ᗡ'R` (✱33·03 defines it directly): the
two agree. The conditions on series hold for every homogeneous relation.

**Status.** complete. All proved; `Cnv'R = R̆` (which the Introduction itself calls "not a
formally correct definition") and `C'R = D'R ∪ ᗡ'R` proved (reading).
-/

/-- Intro, Ch. I: \(\text{Cnv}ʻR = \breve{R}\).

**Status.** proved (reading): PM gives this as a (not formally correct) definition; read with
✱31·01's `Cnv`, the description `Cnv'R` exists and is `R˘`. -/
theorem Cnv_desc {R : α → β → Prop} : Desc Cnv R (fun Q => Q = R˘) := (desc_Cnv _ _).2 rfl

/-- Intro, Ch. I: \(\breve{R} = \hat{x}\hat{y} (yRx)\), as ✱31·02. -/
theorem cnv_def {R : α → β → Prop} : R˘ = fun x y => R y x := rfl

/-- Intro, Ch. I: "Identity, diversity […] are symmetrical relations." -/
theorem identity_diversity_symmetrical :
    (fun x y : α => x = y) = (fun x y : α => x = y)˘ ∧
      (fun x y : α => x ≠ y) = (fun x y : α => x ≠ y)˘ :=
  ⟨funext fun _ => funext fun _ => propext eq_comm, funext fun _ => funext fun _ => propext ne_comm⟩

/-- Intro, Ch. I: inclusion between classes is neither symmetrical nor asymmetrical: `α ⊂ β` and
`β ⊂ α` are both true when `α = β`, and otherwise at most one of them is.

**Status.** proved (reading): "neither symmetrical" needs two different classes, i.e. a member
of the type: `[Nonempty α]` (PM assumes every type has a member). -/
theorem inclusion_neither_symm_nor_asymm [Nonempty α] :
    (¬(∀ A B : Set α, A ⊆ B → B ⊆ A) ∧ ¬(∀ A B : Set α, A ⊆ B → ¬B ⊆ A)) ∧
      ∀ A B : Set α, (A ⊆ B ∧ B ⊆ A ↔ A = B) := by
  refine ⟨⟨fun h => ?_, fun h => h ∅ ∅ subset_rfl subset_rfl⟩, fun A B =>
    ⟨fun h => Set.Subset.antisymm h.1 h.2, fun h => h ▸ ⟨subset_rfl, subset_rfl⟩⟩⟩
  obtain ⟨x⟩ := ‹Nonempty α›
  exact h ∅ Set.univ (Set.empty_subset _) (Set.mem_univ x)

/-- Intro, Ch. I: a relation is symmetrical, `R = R̆`, iff it holds between `y` and `x` whenever
it holds between `x` and `y`. -/
theorem symmetrical_iff {R : α → α → Prop} : R = R˘ ↔ ∀ x y, R x y → R y x := by
  constructor
  · intro h x y hxy
    have := congrFun (congrFun h y) x
    exact (Iff.of_eq this).2 hxy
  · intro h
    funext x y
    exact propext ⟨h x y, h y x⟩

/-- Intro, Ch. I: \(R \dot{\cap}\breve{R} = \dot{\Lambda}\) is equivalent to
\(xRy . \supset_{x, y} . \sim{(yRx)}\). -/
theorem asymmetrical_iff {R : α → α → Prop} : R ⩀ R˘ = rNull ↔ ∀ x y, R x y → ¬R y x := by
  rw [eq_rNull_iff]
  constructor
  · intro h x y hxy hyx
    exact h ⟨x, y, hxy, hyx⟩
  · rintro h ⟨x, y, hxy, hyx⟩
    exact h x y hxy hyx

/-- Intro, Ch. I. \(\vdash \colon x \in \overrightarrow{R}ʻy . \equiv . xRy\) -/
theorem mem_refs_desc {R : α → β → Prop} {x : α} {y : β} :
    Desc (Rfwd R) y (fun A => x ∈ A) ↔ R x y :=
  desc_graph _ _ _

/-- Intro, Ch. I. \(\vdash \colon y \in \overleftarrow{R}ʻx . \equiv . xRy\) -/
theorem mem_rels_desc {R : α → β → Prop} {x : α} {y : β} :
    Desc (Rbwd R) x (fun B => y ∈ B) ↔ R x y :=
  desc_graph _ _ _

/-- Intro, Ch. I. \(\text{sg}ʻR = \overrightarrow{R}\), \(\text{gs}ʻR = \overleftarrow{R}\) -/
theorem sg_gs_desc {R : α → β → Prop} :
    Desc sg R (fun A => A = Rfwd R) ∧ Desc gs R (fun A => A = Rbwd R) :=
  ⟨(desc_graph _ _ _).2 rfl, (desc_graph _ _ _).2 rfl⟩

/-- Intro, Ch. I: \(\text{D}ʻR = \hat{x} \{(\exists y) . xRy\}\) and
\(\text{ᗡ}ʻR = \hat{y} \{(\exists x) . xRy\}\) (✱33·01·02, stated with `Desc`: the descriptions
exist and have these values). -/
theorem dom_codom_desc {R : α → β → Prop} :
    Desc D R (fun A => A = {x | ∃ y, R x y}) ∧ Desc Dcnv R (fun B => B = {y | ∃ x, R x y}) :=
  ⟨(desc_graph _ _ _).2 rfl, (desc_graph _ _ _).2 rfl⟩

/-- Intro, Ch. I: the converse domain is the domain of the converse. -/
theorem codom_eq_dom_cnv {R : α → β → Prop} : codom R = dom R˘ := rfl

/-- Intro, Ch. I: \(CʻR = \text{D}ʻR \cup \text{ᗡ}ʻR\).

**Status.** proved (reading): the Introduction's definition of the field; ✱33·03 defines `C'R`
as `x̂{(∃y) : xRy . ∨ . yRx}`, and the two agree. -/
theorem fld_eq_dom_union_codom {R : α → α → Prop} : fld R = dom R ∪ codom R := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact Or.inl ⟨y, h⟩
    · exact Or.inr ⟨y, h⟩
  · rintro (⟨y, h⟩ | ⟨y, h⟩)
    · exact ⟨y, Or.inl h⟩
    · exact ⟨y, Or.inr h⟩

/-- Intro, Ch. I: "no end" \(\text{ᗡ}ʻR \subset \text{D}ʻR\) is equivalent to
\(\text{D}ʻR = CʻR\). -/
theorem no_end_iff {R : α → α → Prop} : codom R ⊆ dom R ↔ dom R = fld R := by
  rw [fld_eq_dom_union_codom, eq_comm, Set.union_eq_left]

/-- Intro, Ch. I: "no beginning" \(\text{D}ʻR \subset \text{ᗡ}ʻR\) is equivalent to
\(\text{ᗡ}ʻR = CʻR\). -/
theorem no_beginning_iff {R : α → α → Prop} : dom R ⊆ codom R ↔ codom R = fld R := by
  rw [fld_eq_dom_union_codom, eq_comm, Set.union_eq_right]

/-!
## [intro.relative-product] The relative product

*(Vol. 1, Introduction, Chapter I, "Various descriptive functions of relations")*

> \(\vdash \colon x(R \mid S) z . \equiv . (\exists y) . xRy. ySz.\) […] The relative product is
> not commutative, but it obeys the associative law, *i.e.* \(\vdash \ldotp (P\mid Q)\mid R =
> P\mid (Q\mid R)\text{.}\) It also obeys the distributive law with regard to the logical
> addition of relations, *i.e.* we have \(\vdash \ldotp P\mid (Q \unicode{x228d} R) = (P\mid Q)
> \unicode{x228d} (P\mid R)\text{,}\) \(\vdash \ldotp (Q \unicode{x228d} R) \mid P = (Q\mid P)
> \unicode{x228d} (R\mid P)\text{.}\) But with regard to the logical *product*, we have only
> \(\vdash \ldotp P\mid (Q\dot{\cap}R)\unicode{x2abd}(P\mid Q)\dot{\cap}(P\mid R)\text{,}\)
> \(\vdash \ldotp (Q\dot{\cap}R)\mid P\unicode{x2abd}(Q\mid P)\dot{\cap}(R\mid P)\text{.}\) The
> relative product does not obey the law of tautology, *i.e.* we do not have in general \(R\mid
> R = R\). […] A relation is called *transitive* when \(R^{2}\unicode{x2abd}R\), *i.e.* […]
> \(xRy \ldotp yRz \ldotp \supset_{x, y, z} \ldotp xRz\text{.}\) Relations which generate series
> are always transitive; thus *e.g.* \(x \gt y \ldotp y \gt z \ldotp \supset_{x, y, z} \ldotp x
> \gt z\text{.}\) […] The class of relations which generate series are partially characterized
> by the fact that they are transitive and asymmetrical, and never relate a term to itself. […]
> if we have not merely \(P^{2}\unicode{x2abd}P\), but \(P^{2}=P\), then \(P\) generates a series
> which is *compact* […] For in this case we have \(xPz \ldotp \supset \ldotp (\exists y) \ldotp
> xPy \ldotp yPz\text{,}\) […] Many relations which do not generate series are transitive, for
> example, identity, or the relation of inclusion between classes.

**Lean reading.** `R | S` is `R ⨾ S` (✱34). The negative claims (not commutative, no tautology,
only inclusion for `∩̇`) are proved by counterexamples on `Bool`.

**Status.** complete. All proved.
-/

/-- Intro, Ch. I. \(\vdash \colon x(R \mid S) z . \equiv . (\exists y) . xRy. ySz\) -/
theorem relProd_apply {R : α → β → Prop} {S : β → γ → Prop} {x : α} {z : γ} :
    (R ⨾ S) x z ↔ ∃ y, R x y ∧ S y z := Iff.rfl

/-- Intro, Ch. I: the relative product is associative.
\(\vdash \ldotp (P\mid Q)\mid R = P\mid (Q\mid R)\) -/
theorem relProd_assoc {δ : Type*} {P : α → β → Prop} {Q : β → γ → Prop} {R : γ → δ → Prop} :
    (P ⨾ Q) ⨾ R = P ⨾ (Q ⨾ R) := by
  refine rel_eq_iff.2 fun x w => ⟨?_, ?_⟩
  · rintro ⟨z, ⟨y, h1, h2⟩, h3⟩
    exact ⟨y, h1, z, h2, h3⟩
  · rintro ⟨y, h1, z, h2, h3⟩
    exact ⟨z, ⟨y, h1, h2⟩, h3⟩

/-- Intro, Ch. I. \(\vdash \ldotp P\mid (Q \unicode{x228d} R) = (P\mid Q) \unicode{x228d} (P\mid R)\) -/
theorem relProd_rcup {P : α → β → Prop} {Q R : β → γ → Prop} :
    P ⨾ (Q ⊍ R) = (P ⨾ Q) ⊍ (P ⨾ R) := by
  refine rel_eq_iff.2 fun x z => ⟨?_, ?_⟩
  · rintro ⟨y, h1, h2 | h2⟩
    · exact Or.inl ⟨y, h1, h2⟩
    · exact Or.inr ⟨y, h1, h2⟩
  · rintro (⟨y, h1, h2⟩ | ⟨y, h1, h2⟩)
    · exact ⟨y, h1, Or.inl h2⟩
    · exact ⟨y, h1, Or.inr h2⟩

/-- Intro, Ch. I. \(\vdash \ldotp (Q \unicode{x228d} R) \mid P = (Q\mid P) \unicode{x228d} (R\mid P)\) -/
theorem rcup_relProd {Q R : α → β → Prop} {P : β → γ → Prop} :
    (Q ⊍ R) ⨾ P = (Q ⨾ P) ⊍ (R ⨾ P) := by
  refine rel_eq_iff.2 fun x z => ⟨?_, ?_⟩
  · rintro ⟨y, h1 | h1, h2⟩
    · exact Or.inl ⟨y, h1, h2⟩
    · exact Or.inr ⟨y, h1, h2⟩
  · rintro (⟨y, h1, h2⟩ | ⟨y, h1, h2⟩)
    · exact ⟨y, Or.inl h1, h2⟩
    · exact ⟨y, Or.inr h1, h2⟩

/-- Intro, Ch. I. \(\vdash \ldotp P\mid (Q\dot{\cap}R)\unicode{x2abd}(P\mid Q)\dot{\cap}(P\mid R)\) -/
theorem relProd_rcap {P : α → β → Prop} {Q R : β → γ → Prop} :
    P ⨾ (Q ⩀ R) ⪽ (P ⨾ Q) ⩀ (P ⨾ R) := by
  rintro x z ⟨y, h1, h2, h3⟩
  exact ⟨⟨y, h1, h2⟩, ⟨y, h1, h3⟩⟩

/-- Intro, Ch. I. \(\vdash \ldotp (Q\dot{\cap}R)\mid P\unicode{x2abd}(Q\mid P)\dot{\cap}(R\mid P)\) -/
theorem rcap_relProd {Q R : α → β → Prop} {P : β → γ → Prop} :
    (Q ⩀ R) ⨾ P ⪽ (Q ⨾ P) ⩀ (R ⨾ P) := by
  rintro x z ⟨y, ⟨h1, h2⟩, h3⟩
  exact ⟨⟨y, h1, h3⟩, ⟨y, h2, h3⟩⟩

/-- Intro, Ch. I: "with regard to the logical *product*, we have only" inclusion: the converse of
`relProd_rcap` fails. -/
theorem relProd_rcap_not_eq :
    ∃ P Q R : Bool → Bool → Prop, P ⨾ (Q ⩀ R) ≠ (P ⨾ Q) ⩀ (P ⨾ R) := by
  refine ⟨fun _ _ => True, fun y _ => y = true, fun y _ => y = false, fun h => ?_⟩
  have h1 := congrFun (congrFun h false) false
  obtain ⟨y, -, hy1, hy2⟩ := (Iff.of_eq h1).2 ⟨⟨true, trivial, rfl⟩, ⟨false, trivial, rfl⟩⟩
  exact absurd (hy1.symm.trans hy2) (by decide)

/-- Intro, Ch. I: the relative product is not commutative. -/
theorem relProd_not_comm : ∃ R S : Bool → Bool → Prop, R ⨾ S ≠ S ⨾ R := by
  refine ⟨fun _ y => y = true, fun x _ => x = false, fun h => ?_⟩
  have h1 := congrFun (congrFun h false) true
  obtain ⟨y, hy1, hy2⟩ := (Iff.of_eq h1).2 ⟨true, rfl, rfl⟩
  exact absurd (hy1.symm.trans hy2) (by decide)

/-- Intro, Ch. I: the relative product does not obey the law of tautology: we do not have in
general \(R\mid R = R\). -/
theorem relProd_not_taut : ∃ R : Bool → Bool → Prop, rsq R ≠ R := by
  refine ⟨fun x y => x = false ∧ y = true, fun h => ?_⟩
  have h1 := congrFun (congrFun h false) true
  obtain ⟨y, ⟨-, hy1⟩, hy2, -⟩ := (Iff.of_eq h1).2 ⟨rfl, rfl⟩
  exact absurd (hy1.symm.trans hy2) (by decide)

/-- Intro, Ch. I: `R` is transitive when \(R^{2}\unicode{x2abd}R\), *i.e.* when
\(xRy \ldotp yRz \ldotp \supset_{x, y, z} \ldotp xRz\). -/
theorem transitive_iff {R : α → α → Prop} :
    rsq R ⪽ R ↔ ∀ x y z, R x y ∧ R y z → R x z :=
  ⟨fun h x y z hxyz => h x z ⟨y, hxyz.1, hxyz.2⟩, fun h x z ⟨y, h1, h2⟩ => h x y z ⟨h1, h2⟩⟩

/-- Intro, Ch. I: \(x \gt y \ldotp y \gt z \ldotp \supset_{x, y, z} \ldotp x \gt z\) (for the
natural numbers). -/
theorem gt_transitive : ∀ x y z : ℕ, x > y ∧ y > z → x > z := fun _ _ _ h => lt_trans h.2 h.1

/-- Intro, Ch. I: an asymmetrical relation never relates a term to itself. -/
theorem asymmetrical_irreflexive {R : α → α → Prop} (h : R ⩀ R˘ = rNull) : ∀ x, ¬R x x := by
  intro x hx
  exact rNull_apply x x ((Iff.of_eq (congrFun (congrFun h x) x)).1 ⟨hx, hx⟩)

/-- Intro, Ch. I: identity and the inclusion between classes are transitive. -/
theorem identity_inclusion_transitive :
    rsq (fun x y : α => x = y) ⪽ (fun x y => x = y) ∧
      rsq (fun A B : Set α => A ⊆ B) ⪽ (fun A B => A ⊆ B) :=
  ⟨fun _ _ ⟨_, h1, h2⟩ => h1.trans h2, fun _ _ ⟨_, h1, h2⟩ => h1.trans h2⟩

/-- Intro, Ch. I: if \(P^{2}=P\), then \(xPz \ldotp \supset \ldotp (\exists y) \ldotp xPy \ldotp yPz\)
(the series is compact). -/
theorem compact_of_sq_eq {P : α → α → Prop} (h : rsq P = P) {x z : α} :
    P x z → ∃ y, P x y ∧ P y z := by
  intro hxz
  have := congrFun (congrFun h x) z
  exact (Iff.of_eq this).2 hxz

/-!
## [intro.plural-descriptive] Plural descriptive functions

*(Vol. 1, Introduction, Chapter I, "Plural descriptive functions")*

> The class of terms \(x\) which have the relation \(R\) to some member of a class \(\alpha\) is
> denoted by \(Rʻʻ\alpha\) or \(R_{\in}ʻ\alpha\). The definition is \(Rʻʻ\alpha =
> \hat{x}\{(\exists y) \ldotp y \in \alpha \ldotp xRy\} \quad \text{Df}\text{.}\) […]
> If \(P\) is a relation such that \(Pʻy\) always exists when \(y \in \alpha\), \(Pʻʻ\alpha\)
> will be the class of all terms of the form \(Pʻy\) for values of \(y\) which are members of
> \(\alpha\); *i.e.* \(Pʻʻ\alpha = \hat{x}\{(\exists y) \ldotp y \in \alpha \ldotp x =
> Pʻy\}\text{.}\) […] In other cases, this will not hold; for instance, let \(P\) be the relation
> of a number to any number of which it is a factor […]

**Lean reading.** `R''α` is `R ʻʻ A` and `R_∈` is `imgRel R` (✱37·01·02); `x = P'y` is `Desc P y (fun b => x = b)`. The
hypothesis "`P'y` always exists when `y ∈ α`" is `∀ y, y ∈ A → EDesc P y` (✱37·05 `E!! P''α`).
That the formula fails in other cases is shown with the universal relation on `Bool` (PM's
example is "factor of", on the even numbers).

**Status.** complete. Both proved.
-/

/-- Intro, Ch. I: \(R_{\in}ʻ\alpha = Rʻʻ\alpha = \hat{x}\{(\exists y) \ldotp y \in \alpha \ldotp
xRy\}\) (✱37·01·02, stated with `Desc`: the description `R_∈'α` exists and has this value). -/
theorem img_desc {R : α → β → Prop} {A : Set β} :
    Desc (imgRel R) A (fun B => B = {x | ∃ y, y ∈ A ∧ R x y}) ∧
      R ʻʻ A = {x | ∃ y, y ∈ A ∧ R x y} :=
  ⟨(desc_graph _ _ _).2 rfl, rfl⟩

/-- Intro, Ch. I: if `P'y` exists for `y ∈ α`, then
\(Pʻʻ\alpha = \hat{x}\{(\exists y) \ldotp y \in \alpha \ldotp x = Pʻy\}\). -/
theorem img_eq_of_EE {P : α → β → Prop} {A : Set β} (h : ∀ y, y ∈ A → EDesc P y) :
    P ʻʻ A = {x | ∃ y, y ∈ A ∧ Desc P y (fun b => x = b)} := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨b, hb⟩ := h y hy
    exact ⟨y, hy, b, hb, (hb x).1 hxy⟩
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact ⟨y, hy, (hb x).2 rfl⟩

/-- Intro, Ch. I: "In other cases, this will not hold." -/
theorem img_ne_of_not_EE :
    ∃ (P : Bool → Bool → Prop) (A : Set Bool),
      P ʻʻ A ≠ {x | ∃ y, y ∈ A ∧ Desc P y (fun b => x = b)} := by
  refine ⟨fun _ _ => True, Set.univ, fun h => ?_⟩
  have hmem : true ∈ (fun _ _ => True : Bool → Bool → Prop) ʻʻ (Set.univ : Set Bool) :=
    ⟨true, trivial, trivial⟩
  rw [h] at hmem
  obtain ⟨y, -, b, hb, -⟩ := hmem
  exact absurd (((hb true).1 trivial).trans ((hb false).1 trivial).symm) (by decide)

/-!
## [intro.unit-classes] Unit classes and the number 1

*(Vol. 1, Introduction, Chapter I, "Unit classes")*

> The class whose only member is \(x\) might be thought to be identical with \(x\), but Peano and
> Frege have shown that this is not the case. […] We denote by "\(\iotaʻx\)" the class whose only
> member is \(x\): thus \(\iotaʻx = \hat{y}(y = x) \quad \text{Df}\text{,}\) […] This number is
> defined as the class of unit classes, *i.e.* \(1 = \hat{\alpha} \{(\exists x) \ldotp \alpha =
> \iotaʻx\} \quad \text{Df}\text{.}\) This leads to \(\vdash \colon\ldotp \alpha \in 1 \ldotp
> \equiv \colon (\exists x) \colon y \in \alpha \ldotp \equiv_{y} \ldotp y = x\text{.}\) From this
> it appears further that \(\vdash \colon \alpha \in 1 \ldotp \equiv \ldotp \text{E}! ({℩}x) (x
> \in \alpha)\text{,}\) whence \(\vdash \colon \hat{z} ({\phi}z) \in 1 \ldotp \equiv \ldotp
> \text{E}! ({℩}x) ({\phi}x)\text{,}\) […] If \(\alpha \in 1\), \(\breve{\iota}ʻ\alpha\) is the
> only member of \(\alpha\), for the only member of \(\alpha\) is the only term to which
> \(\alpha\) has the relation \(\iota\). Thus "\(\iota ʻ\alpha\)" takes the place of
> "(\({{℩}}x)(\phi x)\)," if \(\alpha\) stands for \(\hat{z}(\phi z)\).

**Lean reading.** `ι'x` (✱51), `1` (✱52·01) and the relation `ι` (✱51·01) are those of
`Defs/Part2.lean`: `ι x`, `one`, `iota`; `ῐ'α` ("the only member of `α`") is the description
`Desc iota˘ A ψ`. ("`ι'α`" in the last sentence is printed for `ῐ'α`.) That the unit class `ι'x`
is not `x` (and that "`x = ι'x`" is meaningless) is Lean's typing: `ι x : Set α` and `x : α`
cannot be compared.

**Status.** complete. All proved.
-/

/-- Intro, Ch. I: \(\iotaʻx = \hat{y}(y = x)\) and \(1 = \hat{\alpha} \{(\exists x) \ldotp \alpha
= \iotaʻx\}\) (as in Part II). -/
theorem unit_class_def (x : α) : ι x = {y | y = x} ∧ (one : Set (Set α)) = {A | ∃ x, A = ι x} :=
  ⟨rfl, rfl⟩

/-- Intro, Ch. I.
\(\vdash \colon\ldotp \alpha \in 1 \ldotp \equiv \colon (\exists x) \colon y \in \alpha \ldotp \equiv_{y} \ldotp y = x\) -/
theorem mem_one_iff_unique {A : Set α} : A ∈ one ↔ ∃ x, ∀ y, y ∈ A ↔ y = x := mem_one_iff

/-- Intro, Ch. I. \(\vdash \colon \alpha \in 1 \ldotp \equiv \ldotp \text{E}! ({℩}x) (x \in \alpha)\) -/
theorem mem_one_iff_EBang {A : Set α} : A ∈ one ↔ EBang (fun x => x ∈ A) := mem_one_iff

/-- Intro, Ch. I. \(\vdash \colon \hat{z} ({\phi}z) \in 1 \ldotp \equiv \ldotp \text{E}! ({℩}x) ({\phi}x)\) -/
theorem class_mem_one_iff_EBang {φ : α → Prop} : {z | φ z} ∈ one ↔ EBang φ := mem_one_iff

/-- Intro, Ch. I: if \(\alpha \in 1\), \(\breve{\iota}ʻ\alpha\) is the only member of \(\alpha\).

**Status.** proved (reading): `ῐ'α` is a description, stated with `Desc` (Basic §5). -/
theorem iota_cnv_only_member {A : Set α} (h : A ∈ one) :
    Desc iota˘ A (fun x => ∀ y, y ∈ A ↔ y = x) := by
  rw [desc_iota_cnv]
  obtain ⟨b, hb⟩ := mem_one_iff.1 h
  exact (TheIs_iff_of_unique hb).2 hb

/-- Intro, Ch. I: "\(\breve{\iota}ʻ\alpha\) takes the place of (℩x)(φx), if `α` stands for
`ẑ(φz)`": a proposition about `ῐ'ẑ(φz)` is the same proposition about `(℩x)(φx)`.

**Status.** proved (reading): the e-text prints `ι'α` for `ῐ'α`; both descriptions are read
with `Desc`/`TheIs` (Basic §5). -/
theorem iota_cnv_eq_description {φ : α → Prop} (ψ : α → Prop) :
    Desc iota˘ {z | φ z} ψ ↔ TheIs φ ψ := desc_iota_cnv _ _

/-! # Volume I, Introduction, Chapter II: the theory of logical types -/

/-!
## [intro.vicious-circle] The vicious-circle principle; why a function requires arguments of a certain type

*(Vol. 1, Introduction, Chapter II, §§ I, IV)*

> The principle which enables us to avoid illegitimate totalities may be stated as follows:
> "Whatever involves all of a collection must not be one of the collection"; or, conversely: "If,
> provided a certain collection had a total, it would have members only definable in terms of
> that total, then the said collection has no total." […] Take, for example, the law of excluded
> middle, in the form "all propositions are true or false." If from this law we argue that,
> because the law of excluded middle is a proposition, therefore the law of excluded middle is
> true or false, we incur a vicious-circle fallacy. […] not only is it impossible for a function
> \(\phi\hat{z}\) to have itself or anything derived from it as argument, but that, if
> \(\psi\hat{z}\) is another function such that there are arguments \(a\) with which both
> "\({\phi}a\)" and "\(\psi a\)" are significant, then \(\psi\hat{z}\) and anything derived from
> it cannot significantly be argument to \(\phi\hat{z}\).

**Lean reading.** Lean's simple types realize the second half: a function `φ : α → Prop` takes
arguments of type `α` only, and `φ φ`, `φ {z | φ z}` are ill-typed (not false: meaningless). The
classes of `α`-things form the type `Set α`, which is never among the `α`-things: there is not
even an injection of `Set α` into `α` (Cantor). Lean does *not* adopt the vicious-circle principle
for propositions: `Prop` is impredicative, so `∀ p : Prop, p ∨ ¬p` is itself a `Prop` and may be
instantiated at itself. The inference PM calls a vicious-circle fallacy is therefore valid in Lean
(and harmless: impredicative `Prop` is consistent relative to the usual set theories). The ramified
hierarchy of orders has no counterpart (Basic §4).

**Status.** complete. The totality of classes is not among its members: proved (reading). The
law of excluded middle applied to itself: proved (reading) (Lean's `Prop` is impredicative).
-/

/-- Intro, Ch. II § I: "whatever involves all of a collection must not be one of the collection":
the classes of `α`-things cannot be found among the `α`-things, not even by an injection.

**Status.** proved (reading): PM's principle concerns definability; its formal content in Lean's
typed setting is that `Set α` is a different type which does not inject into `α` (Cantor). -/
theorem classes_not_among_members : ¬ ∃ f : Set α → α, Function.Injective f :=
  fun ⟨f, hf⟩ => Function.cantor_injective f hf

/-- Intro, Ch. II § I: "the law of excluded middle is true or false", inferred from the law of
excluded middle itself.

**Status.** proved (reading): PM calls this inference a vicious-circle fallacy. In Lean `Prop` is
impredicative: `∀ p : Prop, p ∨ ¬p` is a proposition and the law may be applied to it. -/
theorem excluded_middle_of_itself : (∀ p : Prop, p ∨ ¬p) ∨ ¬(∀ p : Prop, p ∨ ¬p) :=
  (fun h : ∀ p : Prop, p ∨ ¬p => h (∀ p : Prop, p ∨ ¬p)) Classical.em

/-!
## [intro.reducibility] The axiom of reducibility

*(Vol. 1, Introduction, Chapter II, §§ V, VI; Chapter III, (2))*

> (Chapter II, § V:) Let us take as an illustration the definition of identity. […] Thus for
> example "\(x\) is identical with \(a\)" is a function of \(x\); hence, if it is a legitimate
> value of \(\phi\) in "\(\phi x\) always implies \(\phi y\)" we shall be able to infer, by means
> of the above definition, that if \(x\) is identical with \(a\), and \(x\) is identical with
> \(y\), then \(y\) is identical with \(a\). Although the conclusion is sound, the reasoning
> embodies a vicious-circle fallacy, […]
> (§ VI:) The axiom of reducibility is the assumption that, given any function \(\phi \hat{x}\),
> there is a formally equivalent *predicative* function, […] In symbols, the axiom is:
> \(\vdash \colon (\exists \psi) \colon {\phi}x \ldotp \equiv_{x} \ldotp {\psi}!x\text{.}\) For two
> variables, we require a similar axiom, namely: Given any function \(\phi(\hat{x}, \hat{y})\),
> there is a formally equivalent *predicative* function, *i.e.* \(\vdash \colon (\exists \psi)
> \colon \phi(x, y) \ldotp \equiv_{x, y} \ldotp \psi!(x, y)\text{.}\) […] Then the identity of
> indiscernibles will state that if \(x\) and \(y\) agree as to all their predicates, they are
> identical. This can be proved if we assume the axiom of reducibility. […] We therefore adopt
> the following definition of identity […]: \(x = y . = \colon (\phi) \colon \phi !x . \supset .
> \phi !y \qquad \text{Df}.\) […] It should be observed, in the first place, that if we assume
> the existence of classes, the axiom of reducibility can be proved. […] The axiom of
> reducibility is equivalent to the assumption that "any combination or disjunction of
> predicates […] is equivalent to a single predicate," *i.e.* to the assumption that, if we
> assert that \(x\) has all the predicates that satisfy a function \(f(\phi !\hat{z})\) there is
> some one predicate which \(x\) will have whenever our assertion is true, and will not have
> whenever it is false, and similarly if we assert that \(x\) has some one of the predicates
> that satisfy a function \(f(\phi ! \hat{z}\)).
> (Chapter III:) If we now extend the axiom of reducibility so as to apply to functions of
> functions, *i.e.* if we assume \((\exists g)\colon f(\psi !\hat{z}).\equiv_{\psi}.g!(\psi
> !\hat{z}),\) […] In virtue of the axiom of reducibility, if \(\phi \hat{z}\) is any function,
> there is a formally equivalent predicative function \(\psi ! \hat{z}\); then the class
> \(\hat{z}(\phi z\)) is identical with the class \(\hat{z}(\psi !z\)), so that every class can
> be defined by a *predicative* function.

**Lean reading.** Every Lean function is predicative (Basic §4), so the axiom (✱12·1·11), its
extension to functions of functions and the "combination of predicates" form are provable (take
the function itself). Identity is Lean's `=`; ✱13·01's definiens is `PMIdent` (Basic §5), and the
identity of indiscernibles is provable (take `φ := (x = ·)`). Since Lean's quantifier over
`α → Prop` is impredicative, the inference PM calls a vicious-circle fallacy (instantiating
`PMIdent` with the function `(· = a)` defined by `PMIdent` itself) is a valid Lean proof.

**Status.** complete. proved (reading): every Lean function is predicative.
-/

/-- Intro, Ch. II § VI: the axiom of reducibility for one variable (✱12·1).
\(\vdash \colon (\exists \psi) \colon {\phi}x \ldotp \equiv_{x} \ldotp {\psi}!x\)

**Status.** proved (reading): every Lean function is predicative (Basic §4). -/
theorem reducibility_one (φ : α → Prop) : ∃ ψ : α → Prop, ∀ x, φ x ↔ ψ x := reducibility φ

/-- Intro, Ch. II § VI: the axiom of reducibility for two variables (✱12·11).
\(\vdash \colon (\exists \psi) \colon \phi(x, y) \ldotp \equiv_{x, y} \ldotp \psi!(x, y)\)

**Status.** proved (reading): every Lean function is predicative (Basic §4). -/
theorem reducibility_two (φ : α → β → Prop) : ∃ ψ : α → β → Prop, ∀ x y, φ x y ↔ ψ x y :=
  reducibility₂ φ

/-- Intro, Ch. II § VI: the identity of indiscernibles: if `x` and `y` agree as to all their
predicates, they are identical.

**Status.** proved (reading): "all predicates" is `∀ φ : α → Prop` (every Lean function is
predicative); PM proves it from reducibility, Lean by taking `φ := (x = ·)`. -/
theorem indiscernibles {x y : α} : (∀ φ : α → Prop, φ x → φ y) → x = y :=
  fun h => h (fun z => x = z) rfl

/-- Intro, Ch. II § VI: \(x = y . = \colon (\phi) \colon \phi !x . \supset . \phi !y\) (✱13·01).

**Status.** proved (reading): Lean's `=` is primitive; the Df becomes the equivalence of `=` with
PM's definiens `PMIdent` (as `pm13_01`). -/
theorem identity_def {x y : α} : x = y ↔ PMIdent x y := PMIdent_iff_eq.symm

/-- Intro, Ch. II § V: "if `x` is identical with `a`, and `x` is identical with `y`, then `y` is
identical with `a`", inferred from the definition of identity by taking "`x` is identical with
`a`" as a value of `φ`.

**Status.** proved (reading): PM calls the inference a vicious-circle fallacy (the value of `φ`
refers to all values of `φ`); Lean's quantifier over `α → Prop` is impredicative, so it is a valid
proof (with identity read as PM's definiens `PMIdent`). -/
theorem identity_impredicative {x y a : α} : PMIdent x a ∧ PMIdent x y → PMIdent y a :=
  fun ⟨hxa, hxy⟩ => hxy (fun z => PMIdent z a) hxa

/-- Intro, Ch. II § VI: "if we assume the existence of classes, the axiom of reducibility can be
proved": every function is equivalent to "`x` belongs to `α`" for some class `α`. -/
theorem classes_give_reducibility (φ : α → Prop) : ∃ A : Set α, ∀ x, φ x ↔ x ∈ A :=
  ⟨{x | φ x}, fun _ => Iff.rfl⟩

/-- Intro, Ch. II § VI: any combination or disjunction of predicates is equivalent to a single
predicate: "`x` has all the predicates satisfying `f`" and "`x` has some one of them" are each
equivalent to a single predicate of `x`.

**Status.** proved (reading): every Lean function is predicative. -/
theorem combination_of_predicates (f : (α → Prop) → Prop) :
    (∃ ψ : α → Prop, ∀ x, (∀ φ, f φ → φ x) ↔ ψ x) ∧
      ∃ ψ : α → Prop, ∀ x, (∃ φ, f φ ∧ φ x) ↔ ψ x :=
  ⟨⟨_, fun _ => Iff.rfl⟩, ⟨_, fun _ => Iff.rfl⟩⟩

/-- Intro, Ch. III: the axiom of reducibility extended to functions of functions.
\((\exists g)\colon f(\psi !\hat{z}).\equiv_{\psi}.g!(\psi !\hat{z})\)

**Status.** proved (reading): every Lean function is predicative (Basic §4). -/
theorem reducibility_fun_fun (f : (α → Prop) → Prop) :
    ∃ g : (α → Prop) → Prop, ∀ ψ, f ψ ↔ g ψ :=
  ⟨f, fun _ => Iff.rfl⟩

/-- Intro, Ch. III: if `φẑ` is any function, there is a formally equivalent predicative function
`ψ!ẑ`, and the class `ẑ(φz)` is identical with the class `ẑ(ψ!z)`.

**Status.** proved (reading): every Lean function is predicative. -/
theorem class_predicative (φ : α → Prop) :
    ∃ ψ : α → Prop, (∀ x, φ x ↔ ψ x) ∧ {z | φ z} = {z | ψ z} :=
  ⟨φ, fun _ => Iff.rfl, rfl⟩

/-!
## [intro.epimenides] The Epimenides ("I am lying")

*(Vol. 1, Introduction, Chapter II, § VIII, (1))*

> The simplest form of this contradiction is afforded by the man who says "I am lying"; if he is
> lying, he is speaking the truth, and vice versa. […] If we regard the statement "I am lying" as a
> compact way of simultaneously making all the following statements: "I am asserting a false
> proposition of the first order," "I am asserting a false proposition of the second order," and so
> on, we find the following curious state of things: As no proposition of the first order is being
> asserted, the statement "I am asserting a false proposition of the first order" is false. This
> statement is of the second order, hence the statement "I am making a false statement of the
> second order" is true. […] Thus we see that the statement "I am making a false statement of order
> \(2n + 1\)" is false, while the statement "I am making a false statement of order \(2n\)" is
> true. But in this state of things there is no contradiction.

**Lean reading.** The liar's formal content is a proposition equivalent to its own negation; there
is none. PM's resolution by orders is modelled by a sequence `L n` ("I am asserting a false
proposition of order `n`"): `L 1` is false (no first-order proposition is asserted), and the only
proposition of order `n + 1` asserted is `L n`, so `L (n + 1) ↔ ¬L n` for `n ≥ 1`. Then `L (2n+1)`
is false and `L (2n+2)` true, and such a sequence exists ("there is no contradiction").

**Status.** complete. All proved.
-/

/-- Intro, Ch. II § VIII (1): no proposition is equivalent to its own negation ("if he is lying, he
is speaking the truth, and vice versa"). -/
theorem no_liar : ¬ ∃ p : Prop, p ↔ ¬p := fun ⟨_, h⟩ => iff_not_self h

/-- Intro, Ch. II § VIII (1): "I am making a false statement of order \(2n + 1\)" is false, "of order
\(2n\)" is true. -/
theorem liar_orders (L : ℕ → Prop) (h1 : ¬L 1) (hs : ∀ n, 1 ≤ n → (L (n + 1) ↔ ¬L n)) :
    ∀ n, ¬L (2 * n + 1) ∧ L (2 * n + 2) := by
  intro n
  induction n with
  | zero => exact ⟨h1, (hs 1 le_rfl).2 h1⟩
  | succ k ih =>
    have a : L (2 * (k + 1) + 1) ↔ ¬L (2 * k + 2) := by
      have := hs (2 * k + 2) (by omega)
      rwa [show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by omega] at this
    have b : L (2 * (k + 1) + 2) ↔ ¬L (2 * (k + 1) + 1) := by
      have := hs (2 * (k + 1) + 1) (by omega)
      rwa [show 2 * (k + 1) + 1 + 1 = 2 * (k + 1) + 2 by omega] at this
    have c : ¬L (2 * (k + 1) + 1) := fun h => a.1 h ih.2
    exact ⟨c, b.2 c⟩

/-- Intro, Ch. II § VIII (1): "in this state of things there is no contradiction": the hierarchy
of statements is consistent. -/
theorem liar_orders_consistent :
    ∃ L : ℕ → Prop, ¬L 1 ∧ ∀ n, 1 ≤ n → (L (n + 1) ↔ ¬L n) :=
  ⟨fun n => n % 2 = 0, by decide, fun n _ => by omega⟩

/-!
## [intro.russell-classes] The class of all classes which are not members of themselves

*(Vol. 1, Introduction, Chapter II, § VIII, (2); Chapter III, (2), fifth requisite)*

> (2) Let \(w\) be the class of all those classes which are not members of themselves. Then,
> whatever class \(x\) may be, "\(x\) is a \(w\)" is equivalent to "\(x\) is not an \(x\)."
> Hence, giving to \(x\) the value \(w\), "\(w\) is a \(w\)" is equivalent to "\(w\) is not a
> \(w\)." […] Thus if \(\alpha\) is a class, the statement "\(\alpha\) is not a member of
> \(\alpha\)" is always meaningless, and there is therefore no sense in the phrase "the class of
> those classes which are not members of themselves." Hence the contradiction which results from
> supposing that there is such a class disappears.

**Lean reading.** In Lean `A ∈ A` is ill-typed, so the class `w` cannot be written: this is PM's
solution. The paradox itself is the theorem that if classes and their members are put in *one*
type `α`, with membership a relation `mem : α → α → Prop`, no `w : α` satisfies
`∀ x, mem x w ↔ ¬mem x x`; hence no single type can carry naive comprehension (an object
`c A : α` for every class `A : Set α` with `mem x (c A) ↔ x ∈ A`). In the typed setting, the
"universal set of sets" fails too: no `f : α → Set α` is onto (Cantor), *i.e.* the classes of
`α`-things cannot all be named by `α`-things.

**Status.** complete. All proved (reading): the single-type formulations make the paradox's
formal content explicit; Lean itself is typed.
-/

/-- Intro, Ch. II § VIII (2): in a single type with membership a relation, there is no class of
all classes which are not members of themselves.

**Status.** proved (reading): the untyped setting PM rejects is modelled by one type `α` with a
membership relation. -/
theorem russell (mem : α → α → Prop) : ¬ ∃ w : α, ∀ x, mem x w ↔ ¬mem x x :=
  fun ⟨w, hw⟩ => iff_not_self (hw w)

/-- Intro, Ch. II § VIII (2), Ch. III (2): no single type can contain, for every class of its
members, an object having exactly those members ("by (1) and (4), there would be a class of all
classes satisfying the function `α ∼∈ α`").

**Status.** proved (reading): as `russell`. -/
theorem no_naive_comprehension (mem : α → α → Prop) :
    ¬ ∃ c : Set α → α, ∀ (A : Set α) x, mem x (c A) ↔ x ∈ A :=
  fun ⟨c, hc⟩ => russell mem ⟨c {x | ¬mem x x}, fun x => hc _ x⟩

/-- Intro, Ch. II § VIII (2): in the typed setting, the classes of `α`-things are not all values of
a function on `α` (Cantor's theorem).

**Status.** proved (reading): the typed form of the impossibility of a universal set of sets. -/
theorem no_surjection_onto_classes (f : α → Set α) : ¬ Function.Surjective f :=
  Function.cantor_surjective f

/-!
## [intro.russell-relations] The relation which holds between `R` and `S` when `R` does not have `R` to `S`

*(Vol. 1, Introduction, Chapter II, § VIII, (3))*

> (3) Let \(T\) be the relation which subsists between two relations \(R\) and \(S\) whenever \(R\)
> does not have the relation \(R\) to \(S\). Then, whatever relations \(R\) and \(S\) may be,
> "\(R\) has the relation \(T\) to \(S\)" is equivalent to "\(R\) does not have the relation
> \(R\) to \(S\)." Hence, giving the value \(T\) to both \(R\) and \(S\), "\(T\) has the relation
> \(T\) to \(T\)" is equivalent to "\(T\) does not have the relation \(T\) to \(T\)." […] Hence
> "\(R\) has the relation \(R\) to \(S\)" is meaningless, and the contradiction ceases.

**Lean reading.** As for classes: in Lean `R R S` is ill-typed. In one type `α` whose members are
relations, with `rel r x y` for "`x` has the relation `r` to `y`", no `T : α` satisfies
`∀ R S, rel T R S ↔ ¬rel R R S`; typed, no `f : α → (α → α → Prop)` is onto.

**Status.** complete. All proved (reading), as for classes.
-/

/-- Intro, Ch. II § VIII (3): in a single type of relations, there is no relation `T` with
`R T S ↔ ∼(R R S)`.

**Status.** proved (reading): the untyped setting is modelled by one type with an application
relation. -/
theorem russell_relations (rel : α → α → α → Prop) : ¬ ∃ T : α, ∀ R S, rel T R S ↔ ¬rel R R S :=
  fun ⟨T, hT⟩ => iff_not_self (hT T T)

/-- Intro, Ch. II § VIII (3): in the typed setting, the relations between `α`-things are not all
values of a function on `α`.

**Status.** proved (reading): the typed form of the relational contradiction. -/
theorem no_surjection_onto_relations (f : α → (α → α → Prop)) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf (fun x y => ¬f x x y)
  exact iff_not_self (Iff.of_eq (congrFun (congrFun ha a) a))

/-!
## [intro.burali-forti] Burali-Forti's contradiction

*(Vol. 1, Introduction, Chapter II, § VIII, (4))*

> (4) […] It can be shown that every well-ordered series has an ordinal number, that the series of
> ordinals up to and including any given ordinal exceeds the given ordinal by one, and (on certain
> very natural assumptions) that the series of all ordinals (in order of magnitude) is
> well-ordered. It follows that the series of all ordinals has an ordinal number, \(\Omega\) say.
> But in that case the series of all ordinals including \(\Omega\) has the ordinal number
> \(\Omega + 1\), which must be greater than \(\Omega\). Hence \(\Omega\) is not the ordinal
> number of all ordinals. […] Burali-Forti's "ordinal number of all ordinals" must be the ordinal
> number of all ordinals of a given type, and must therefore be of higher type than any of these
> ordinals. Hence it is not one of these ordinals, and there is no contradiction in its being
> greater than any of them.

**Lean reading.** mathlib's `Ordinal.{u}` (the order types of well-orders in `Type u`) is a type in
`Type (u+1)`. The series of all ordinals of type `u` is well-ordered, and its ordinal number is
`Ordinal.univ.{u, u+1} : Ordinal.{u+1}`, of the next type. It exceeds every ordinal of type `u`
(lifted to type `u+1`), so it is none of them: exactly PM's resolution. Within one type there is
no greatest ordinal (`Ω < Ω + 1`).

**Status.** complete. All proved (reading): Lean's universe levels stand for PM's types.
-/

/-- Intro, Ch. II § VIII (4): \(\Omega + 1\) "must be greater than \(\Omega\)". -/
theorem ordinal_lt_add_one (Ω : Ordinal.{u}) : Ω < Ω + 1 := Order.lt_add_one_iff.mpr le_rfl

/-- Intro, Ch. II § VIII (4): "the series of ordinals up to and including any given ordinal
exceeds the given ordinal by one".

**Status.** proved (reading): the series of ordinals `≤ o` of type `u` is a series of type
`u + 1`; its ordinal is compared with `o + 1` lifted to that type. -/
theorem ordinals_upto_including (o : Ordinal.{u}) :
    Ordinal.type (α := Set.Iic o) (· < ·) = Ordinal.lift.{u + 1} (o + 1) := by
  rw [← Ordinal.type_lt_Iio, ← Order.Iio_succ, Order.succ_eq_add_one]

/-- Intro, Ch. II § VIII (4): the series of all ordinals (of a given type) is well-ordered. -/
theorem ordinals_well_ordered : WellFounded ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop) :=
  Ordinal.lt_wf

/-- Intro, Ch. II § VIII (4): the ordinal number of the series of all ordinals of type `u` is
`Ordinal.univ.{u, u+1}`, an ordinal of the next type.

**Status.** proved (reading): universe levels stand for PM's types. -/
theorem ordinal_of_all_ordinals :
    Ordinal.type (α := Ordinal.{u}) (· < ·) = Ordinal.univ.{u, u + 1} :=
  Ordinal.type_lt_ordinal

/-- Intro, Ch. II § VIII (4): the ordinal number of all ordinals of a given type is greater than
any of them ("there is no contradiction in its being greater than any of them").

**Status.** proved (reading): universe levels stand for PM's types; an ordinal of type `u` is
compared with it after lifting to type `u+1`. -/
theorem lt_ordinal_of_all_ordinals (o : Ordinal.{u}) :
    Ordinal.lift.{u + 1} o < Ordinal.univ.{u, u + 1} := by
  simpa using (Ordinal.liftPrincipalSeg.{u, u + 1}).lt_top o

/-- Intro, Ch. II § VIII (4): the ordinal number of all ordinals of a given type is not one of
these ordinals.

**Status.** proved (reading): universe levels stand for PM's types. -/
theorem not_ordinal_of_all_ordinals :
    ¬ ∃ Ω : Ordinal.{u}, Ordinal.lift.{u + 1} Ω = Ordinal.univ.{u, u + 1} :=
  fun ⟨Ω, h⟩ => (lt_ordinal_of_all_ordinals Ω).ne h

/-- Intro, Ch. II § VIII (4): "Hence \(\Omega\) is not the ordinal number of all ordinals": no
ordinal of a given type is greatest among the ordinals of that type. -/
theorem no_greatest_ordinal : ¬ ∃ Ω : Ordinal.{u}, ∀ o : Ordinal.{u}, o ≤ Ω :=
  fun ⟨Ω, h⟩ => absurd (h (Ω + 1)) (not_le.mpr (ordinal_lt_add_one Ω))

/-!
## [intro.berry] The least integer not nameable in fewer than nineteen syllables

*(Vol. 1, Introduction, Chapter II, § VIII, (5))*

> (5) The number of syllables in the English names of finite integers tends to increase as the
> integers grow larger, and must gradually increase indefinitely, since only a finite number of
> names can be made with a given finite number of syllables. Hence the names of some integers must
> consist of at least nineteen syllables, and among these there must be a least. […] any name in
> which the phrase "nameable by names of order \(n\)" occurs is necessarily of a higher order than
> the \(n\)th. Thus the paradox disappears.

**Lean reading.** The formal part of the argument: the integers nameable (by names of a given order)
in fewer than nineteen syllables form a finite set, so there is a least integer outside it. The
contradiction would need the name "the least integer not nameable …" to belong to the same finite
stock of names; PM's resolution is that it is of higher order. Lean has no "nameable" predicate on
its own terms, so only the finite-set part is a theorem.

**Status.** complete. proved (reading): "nameable in fewer than nineteen syllables" is modelled by
an arbitrary finite set of integers.
-/

/-- Intro, Ch. II § VIII (5): among the integers outside a finite set of named integers there is a
least.

**Status.** proved (reading): the integers nameable by names of a given order with fewer than
nineteen syllables are modelled by an arbitrary finite set. -/
theorem least_unnamed (S : Finset ℕ) : ∃ n, n ∉ S ∧ ∀ m, m ∉ S → n ≤ m := by
  classical
  have h : ∃ n, n ∉ S :=
    S.exists_nat_subset_range.elim fun k hk => ⟨k, fun h => by simpa using hk h⟩
  exact ⟨Nat.find h, Nat.find_spec h, fun m hm => Nat.find_min' h hm⟩

/-!
## [intro.konig] The least indefinable ordinal

*(Vol. 1, Introduction, Chapter II, § VIII, (6))*

> (6) Among transfinite ordinals some can be defined, while others can not; for the total number of
> possible definitions is \(\aleph_{0}\) […], while the number of transfinite ordinals exceeds
> \(\aleph_{0}\). Hence there must be indefinable ordinals, and among these there must be a least.
> But this is defined as "the least indefinable ordinal," which is a contradiction. […] And however
> the type may be specified, "the least ordinal not definable by definitions of this type" is a
> definition of a higher type.

**Lean reading.** The definitions (of a given type) are at most `ℵ₀`, so the definable ordinals are
the values of some `d : ℕ → Ordinal`; there is an ordinal not among them, and (ordinals being
well-ordered) a least such. That the phrase defining it is a definition of a higher type is PM's
resolution; Lean has no "definable" predicate on its own terms.

**Status.** complete. proved (reading): "definable by definitions of a given type" is modelled by
the range of a sequence of ordinals.
-/

/-- Intro, Ch. II § VIII (6): for any countable family of ("definable") ordinals there is a least
ordinal outside it.

**Status.** proved (reading): the ordinals definable by definitions of a given type are modelled
by the range of a sequence. -/
theorem least_indefinable_ordinal (d : ℕ → Ordinal.{u}) :
    ∃ o, o ∉ Set.range d ∧ ∀ o', o' ∉ Set.range d → o ≤ o' := by
  have h : (Set.range d)ᶜ.Nonempty := by
    refine ⟨⨆ n, Order.succ (d n), ?_⟩
    rintro ⟨n, hn⟩
    have := Ordinal.le_iSup (fun n => Order.succ (d n)) n
    rw [hn] at this
    exact absurd this (not_le.mpr (Order.lt_succ _))
  exact ⟨sInf (Set.range d)ᶜ, csInf_mem h, fun o' ho' => csInf_le' ho'⟩

/-!
## [intro.richard] Richard's paradox

*(Vol. 1, Introduction, Chapter II, § VIII, (7))*

> Consider all decimals that can be defined by means of a finite number of words; let \(E\) be the
> class of such decimals. Then \(E\) has \(\aleph_{0}\) terms; hence its members can be ordered as
> the 1st, 2nd, 3rd,.... Let \(N\) be a number defined as follows. If the \(n\)th figure in the
> \(n\)th decimal is \(p\), let the \(n\)th figure in \(N\) be \(p + 1\) (or 0, if \(p = 9\)). Then
> \(N\) is different from all the members of \(E\) […] in Richard's paradox, when we confine
> ourselves, as we must, to decimals that have a definition of a given type, the number \(N\),
> which causes the paradox, is found to have a definition which belongs to a higher type.

**Lean reading.** A decimal is a sequence of figures `ℕ → Fin 10`; an enumeration of `E` is
`E : ℕ → ℕ → Fin 10`. The diagonal decimal `N k = E k k + 1` (in `Fin 10`, `9 + 1 = 0`, exactly
PM's rule) differs from every `E n`: the formal content is Cantor's diagonal argument. That `N`
is "defined in a finite number of words" is the step PM rejects (its definition is of a higher
type).

**Status.** complete. proved (reading): the decimals definable by definitions of a given type are
modelled by an arbitrary enumeration.
-/

/-- Intro, Ch. II § VIII (7): the diagonal decimal differs from every decimal of the enumeration.

**Status.** proved (reading): the class `E` of decimals definable (by definitions of a given type)
is modelled by an arbitrary enumeration. -/
theorem richard_diagonal (E : ℕ → ℕ → Fin 10) : ∀ n, (fun k => E k k + 1) ≠ E n := by
  intro n h
  have := congrFun h n
  exact absurd this (by generalize E n n = p; revert p; decide)

/-!
## [intro.existence-theorems] Existence-theorems in the different types; the greatest cardinal

*(Vol. 1, Introduction, Chapter II, § VIII, end)*

> Among propositions wholly expressed in terms of typically ambiguous notions practically the only
> ones which may differ, in respect of truth or falsehood, according to the typical determination
> which they receive, are existence-theorems. If we assume that the total number of individuals is
> \(n\), then the total number of classes of individuals is \(2^{n}\), the total number of classes
> of classes of individuals is \(2^{2^{{}n}}\), and so on. Here \(n\) may be either finite or
> infinite, and in either case \(2^{n} \gt n\). Thus cardinals greater than \(n\) but not greater
> than \(2^{n}\) exist as applied to classes of classes, but not as applied to classes of
> individuals […] For example, any type has at least one member; hence any type which consists of
> classes, of whatever order, has at least two members.

**Lean reading.** The number of members of a type `α` is `#α` (mathlib's `Cardinal.mk`); a cardinal
`c` "exists as applied to classes of individuals" when some `A : Set α` has `#A = c`, and "as
applied to classes of classes" when some `K : Set (Set α)` has `#K = c`. `2^n > n` for every
cardinal is Cantor's theorem, which is also the root of the contradiction of the greatest
cardinal: there is no greatest cardinal of a type, and the cardinal of all cardinals of type `u`
(`Cardinal.univ.{u, u+1}`) is of the next type and exceeds them all, as for Burali-Forti.

**Status.** complete. The cardinal counts and Cantor's theorem proved; "any type has at least one
member" proved (reading) (`[Nonempty α]`); the greatest cardinal proved (reading) (universe levels
for types).
-/

open Cardinal in
/-- Intro, Ch. II § VIII: with `n` individuals there are \(2^{n}\) classes of individuals and
\(2^{2^{n}}\) classes of classes. -/
theorem card_classes (α : Type u) : #(Set α) = 2 ^ #α ∧ #(Set (Set α)) = 2 ^ (2 ^ #α : Cardinal) :=
  ⟨mk_set, by rw [mk_set, mk_set]⟩

open Cardinal in
/-- Intro, Ch. II § VIII: "\(n\) may be either finite or infinite, and in either case
\(2^{n} \gt n\)" (Cantor). -/
theorem two_pow_gt (c : Cardinal.{u}) : c < 2 ^ c := cantor c

open Cardinal in
/-- Intro, Ch. II § VIII: "cardinals greater than \(n\) but not greater than \(2^{n}\) exist as
applied to classes of classes, but not as applied to classes of individuals." -/
theorem cardinals_between (α : Type u) (c : Cardinal.{u}) (h1 : #α < c) (h2 : c ≤ 2 ^ #α) :
    (∃ K : Set (Set α), #K = c) ∧ ¬ ∃ A : Set α, #A = c := by
  refine ⟨le_mk_iff_exists_set.mp (by rwa [mk_set]), ?_⟩
  rintro ⟨A, hA⟩
  exact absurd (hA ▸ mk_set_le A) (not_le.mpr h1)

/-- Intro, Ch. II § VIII: "any type has at least one member; hence any type which consists of
classes, of whatever order, has at least two members."

**Status.** proved (reading): PM's assumption that every type has a member is `[Nonempty α]`. -/
theorem two_classes [Nonempty α] : ∃ A B : Set α, A ≠ B := ⟨∅, Set.univ, Set.empty_ne_univ⟩

open Cardinal in
/-- Intro, Ch. II § VIII: the contradiction of the greatest cardinal: by Cantor's theorem no
cardinal of a given type is greatest. -/
theorem no_greatest_cardinal : ¬ ∃ c : Cardinal.{u}, ∀ d : Cardinal.{u}, d ≤ c :=
  fun ⟨c, h⟩ => absurd (h (2 ^ c)) (not_le.mpr (cantor c))

/-- Intro, Ch. II § VIII: the cardinal number of all cardinals (of a given type) is of higher type
and greater than any of them.

**Status.** proved (reading): universe levels stand for PM's types. -/
theorem lt_cardinal_of_all_cardinals (c : Cardinal.{u}) :
    Cardinal.lift.{u + 1} c < Cardinal.univ.{u, u + 1} :=
  Cardinal.lift_lt_univ c

/-! # Volume I, Introduction, Chapter III: incomplete symbols -/

/-!
## [intro.description-incomplete] Descriptions are incomplete symbols

*(Vol. 1, Introduction, Chapter III, (1) and end of (3))*

> Suppose we say: "The round square does not exist." […] Generally, when "the so-and-so" is said
> not to exist, we have a proposition of the form […] "\({\sim}\text{E}!({℩}x)({\phi}x),\)"
> \(\textit{i.e.} \quad {\sim}\{(\exists c) \colon \phi x \ldotp \equiv_{x} \ldotp x = c\}\text{,}\)
> or some equivalent. […] any statement apparently about (\({℩}x)({\phi}x)\) requires (1)
> (\(\exists x).({\phi}x)\) and (2) \({\phi}x . {\phi}y . \supset_{x, y} . x = y\); […] The two
> together are equivalent to \((\exists c) \colon {\phi}x \ldotp \equiv_{x} \ldotp x = c\text{,}\)
> which we defined as \(\text{E}!({℩}x)({\phi}x).\) […] Thus we have
> \(f\{({℩}x)({\phi}x)\} \ldotp = : (\exists c) : {\phi}x . \equiv_{x} . x = c:fc \quad
> \text{Df}\text{,}\) […] The proposition "\(a = ({℩}x)({\phi}x)\)" is easily shown to be
> equivalent to "\({\phi}x . \equiv_{x} . x = a\)." […] (end of (3):) Thus for example we have
> (\(x).x=x\), but we do not have the round square = the round square.

**Lean reading.** `a = (℩x)(φx)` is `TheIs φ (fun b => a = b)` (✱14·01). "The round square" is
the description of an unsatisfiable function `fun _ => False`; "the round square = the round
square" has two descriptions, the first with the larger scope (`TheIs2`, ✱14·03 and the
convention after it).

**Status.** complete. All proved.
-/

/-- Intro, Ch. III: \(f\{({℩}x)({\phi}x)\} \ldotp = : (\exists c) : {\phi}x . \equiv_{x} . x =
c:fc\) (✱14·01). -/
theorem description_def {φ f : α → Prop} : TheIs φ f ↔ ∃ c, (∀ x, φ x ↔ x = c) ∧ f c := Iff.rfl

/-- Intro, Ch. III: (1) \((\exists x).({\phi}x)\) and (2) \({\phi}x . {\phi}y . \supset_{x, y} . x =
y\) "together are equivalent to" \(\text{E}!({℩}x)({\phi}x)\), and a statement about the
description requires both. -/
theorem description_requires {φ f : α → Prop} :
    ((∃ x, φ x) ∧ (∀ x y, φ x ∧ φ y → x = y) ↔ EBang φ) ∧
      (TheIs φ f → (∃ x, φ x) ∧ ∀ x y, φ x ∧ φ y → x = y) := by
  have h : (∃ x, φ x) ∧ (∀ x y, φ x ∧ φ y → x = y) ↔ EBang φ := EBang_iff_exists_unique.symm
  exact ⟨h, fun ht => h.2 (TheIs_iff.1 ht).1⟩

/-- Intro, Ch. III: "\(a = ({℩}x)({\phi}x)\)" is equivalent to "\({\phi}x . \equiv_{x} . x = a\)". -/
theorem eq_description_iff {φ : α → Prop} {a : α} :
    TheIs φ (fun b => a = b) ↔ ∀ x, φ x ↔ x = a :=
  ⟨fun ⟨_, hc, e⟩ => e ▸ hc, fun h => ⟨a, h, rfl⟩⟩

/-- Intro, Ch. III: "the round square does not exist". -/
theorem round_square_not_exists : ¬EBang (fun _ : α => False) := fun ⟨b, hb⟩ => (hb b).2 rfl

/-- Intro, Ch. III: "we have (\(x).x=x\), but we do not have the round square = the round
square". -/
theorem round_square_ne_round_square :
    (∀ x : α, x = x) ∧ ¬TheIs2 (fun _ : α => False) (fun _ : α => False) (fun b c => b = c) :=
  ⟨fun _ => rfl, fun ⟨b, hb, _⟩ => (hb b).2 rfl⟩

/-!
## [intro.description-scope] The scope of a description

*(Vol. 1, Introduction, Chapter III, (1))*

> When \(f\{({℩}x)(\phi x)\}\), as above defined, forms part of some other proposition, we shall
> say that (\({℩}x)(\phi x)\) has a *secondary* occurrence. […] "There is no such person as the
> King of France." We may interpret this as \(\sim{\{\text{E}!({℩}x)(\phi x)\}}\), or as
> \(\sim{\{(\exists c) . c = ({℩}x)(\phi x)\}}\) […]
> \([({℩}x)(\phi x)] . \psi({℩}x)(\phi x) . \supset . p\) will mean \((\exists c) \colon \phi x .
> \equiv_{x} . x = c \colon \psi c \colon \supset . p,\) but \([({℩}x)(\phi x)] \colon
> \psi({℩}x)(\phi x) . \supset . p\) will mean \((\exists c) \colon \phi x . \equiv_{x} . x = c
> \colon \psi c . \supset . p.\) It is important to distinguish these two, for if (\({℩}x)(\phi
> x)\) does not exist, the first is true and the second false. Again \([({℩}x)(\phi x)] .
> \sim{\psi({℩}x)(\phi x)}\) will mean \((\exists c) \colon \phi x . \equiv_{x} . x = c \colon
> \sim{\psi c},\) while \(\sim{\{[({℩}x)(\phi x)] . \psi({℩}x)(\phi x)\}}\) will mean
> \(\sim{\{(\exists c) \colon \phi x . \equiv_{x} . x = c \colon \sim{\psi c}\}}.\) Here again,
> when (\({℩}x)(\phi x)\) does not exist, the first is false and the second true. […] when
> (\({℩}x)(\phi x)\) has the whole of the proposition concerned for its scope, the proposition
> concerned cannot be true unless \(\text{E} !({℩}x)(\phi x)\) […] when \(\text{E}
> !({℩}x)(\phi x)\), we may enlarge or diminish the scope of (\({℩}x)(\phi x)\) as much as we
> please without altering the truth-value of any proposition in which it occurs. […]
> (4) and (5) are equivalent, so that the truth-value of a proposition containing two descriptions
> is independent of the question which has the larger scope. […] "\(a \neq ({℩}x)(\phi x)\)" is
> to be read "\(a\) is not the so-and-so," which would ordinarily be regarded as implying that
> "the so-and-so" exists; but "\({\sim}\{a=({℩}x)(\phi x)\}\)" is to be read "it is not true that
> \(a\) is the so-and-so," which would generally be allowed to hold if "the so-and-so" does not
> exist. […] \(({℩}x)(\phi x) = ({℩}x)(\psi x)\) will mean \((\exists c)\colon \phi x.\equiv_{x}.x
> = c\colon [({℩}x)(\psi x)].c = ({℩}x)(\psi x),\) while \(({℩}x)(\psi x) = ({℩}x)(\phi x)\) will
> mean \((\exists d)\colon \psi x.\equiv_{x}.x = d\colon[(℩x)(\phi x)].({℩}x)(\phi x) = d.\) These
> two propositions are easily shown to be equivalent.

**Lean reading.** A description with scope `ψ(…)` is `TheIs φ ψ` (Basic §5). Two slips of the
text: the definiens printed for `∼{[(℩x)(φx)] . ψ(℩x)(φx)}` has `∼ψc` inside the braces, where
the definition gives `ψc` (the claim about truth-values holds either way; the definiendum is
formalized); and formula (4) prints `ψx . ≡_x . x = c` for `x = d`. PM's "truth-value of any
proposition" for scope changes under `E!` concerns truth-functions; in Lean every function of
propositions is one, so the statement is proved for every `F : Prop → Prop`.

**Status.** complete. All proved; the scope-change principle proved (reading) (every `F`), (4)≡(5)
and the default-scope example of `¬{…}` proved (reading) (slips of the text).
-/

/-- Intro, Ch. III: "There is no such person as the King of France": \(\sim{\{\text{E}!({℩}x)(\phi
x)\}}\) and \(\sim{\{(\exists c) . c = ({℩}x)(\phi x)\}}\) are the same. -/
theorem king_of_france {φ : α → Prop} : (¬ ∃ c, TheIs φ (fun b => c = b)) ↔ ¬EBang φ :=
  ⟨fun h ⟨b, hb⟩ => h ⟨b, b, hb, rfl⟩, fun h ⟨_, ht⟩ => h (TheIs_iff.1 ht).1⟩

/-- Intro, Ch. III: if (℩x)(φx) does not exist,
\([({℩}x)(\phi x)] . \psi({℩}x)(\phi x) . \supset . p\) is true and
\([({℩}x)(\phi x)] \colon \psi({℩}x)(\phi x) . \supset . p\) is false. -/
theorem scope_implication {φ ψ : α → Prop} {p : Prop} (h : ¬EBang φ) :
    (TheIs φ ψ → p) ∧ ¬TheIs φ (fun c => ψ c → p) :=
  ⟨fun ht => (h (TheIs_iff.1 ht).1).elim, fun ht => h (TheIs_iff.1 ht).1⟩

/-- Intro, Ch. III: if (℩x)(φx) does not exist, \([({℩}x)(\phi x)] . \sim{\psi({℩}x)(\phi x)}\)
is false and \(\sim{\{[({℩}x)(\phi x)] . \psi({℩}x)(\phi x)\}}\) is true.

**Status.** proved (reading): the printed definiens of the second has `∼ψc` inside the braces,
a slip for `ψc` (the definition of `[(℩x)(φx)] . ψ(℩x)(φx)`); the claim holds either way. -/
theorem scope_negation {φ ψ : α → Prop} (h : ¬EBang φ) :
    ¬TheIs φ (fun c => ¬ψ c) ∧ ¬TheIs φ ψ :=
  ⟨fun ht => h (TheIs_iff.1 ht).1, fun ht => h (TheIs_iff.1 ht).1⟩

/-- Intro, Ch. III: when the description has the whole proposition for its scope, the proposition
cannot be true unless \(\text{E} !({℩}x)(\phi x)\). -/
theorem whole_scope_exists {φ ψ : α → Prop} : TheIs φ ψ → EBang φ := fun ht => (TheIs_iff.1 ht).1

/-- Intro, Ch. III: "when \(\text{E} !({℩}x)(\phi x)\), we may enlarge or diminish the scope of
(\({℩}x)(\phi x)\) as much as we please without altering the truth-value of any proposition in
which it occurs."

**Status.** proved (reading): PM's claim concerns truth-functions of the scope; every
`F : Prop → Prop` is one in Lean (`truth_function`). -/
theorem scope_irrelevant {φ ψ : α → Prop} (h : EBang φ) (F : Prop → Prop) :
    TheIs φ (fun c => F (ψ c)) ↔ F (TheIs φ ψ) := by
  obtain ⟨b, hb⟩ := h
  rw [TheIs_iff_of_unique hb, TheIs_iff_of_unique hb]

/-- Intro, Ch. III: with two descriptions, (4) and (5) are equivalent: the truth-value is
independent of which has the larger scope.

**Status.** proved (reading): formula (4) prints `ψx . ≡_x . x = c` for `x = d`. -/
theorem two_descriptions_scope {φ : α → Prop} {ψ : β → Prop} {f : α → β → Prop} :
    TheIs φ (fun c => TheIs ψ (fun d => f c d)) ↔ TheIs ψ (fun d => TheIs φ (fun c => f c d)) :=
  ⟨fun ⟨c, hc, d, hd, h⟩ => ⟨d, hd, c, hc, h⟩, fun ⟨d, hd, c, hc, h⟩ => ⟨c, hc, d, hd, h⟩⟩

/-- Intro, Ch. III: \(({℩}x)(\phi x) = ({℩}x)(\psi x)\) and \(({℩}x)(\psi x) = ({℩}x)(\phi x)\),
each with the earlier description having the larger scope, "are easily shown to be equivalent". -/
theorem description_eq_comm {φ ψ : α → Prop} :
    TheIs φ (fun c => TheIs ψ (fun d => c = d)) ↔ TheIs ψ (fun d => TheIs φ (fun c => c = d)) :=
  two_descriptions_scope

/-- Intro, Ch. III: "\(a \neq ({℩}x)(\phi x)\)" implies that the so-and-so exists, while
"\({\sim}\{a=({℩}x)(\phi x)\}\)" holds if the so-and-so does not exist (the default scopes). -/
theorem ne_description_vs_not_eq {φ : α → Prop} {a : α} :
    (TheIs φ (fun b => a ≠ b) → EBang φ) ∧ (¬EBang φ → ¬TheIs φ (fun b => a = b)) :=
  ⟨whole_scope_exists, fun h ht => h (whole_scope_exists ht)⟩

/-!
## [intro.description-identity] Descriptions obey the formal rules of identity

*(Vol. 1, Introduction, Chapter III, end of (3))*

> The use of the symbol "(\({℩}x)(\phi x)\)" as if in "\(f({℩}x)(\phi x)\)" it *directly*
> represented an argument to the function \(f\hat{z}\) is rendered possible by the theorems
> \(\vdash \colon\ldotp \text{E}!(℩x)(\phi x).\supset \colon (x).fx.\supset.f(℩x)(\phi x),\)
> \(\vdash \colon(℩x)(\phi x)=(℩x)(\psi x).\supset.f(℩x)((\phi x)\equiv f(℩x)(\psi x),\)
> \(\vdash \colon \text{E}!(℩x)(\phi x).\supset.(℩x)(\phi x)=(℩x)(\phi x),\)
> \(\vdash \colon(℩x)(\phi x)=(℩x)(\psi x).\equiv.(℩x)(\psi x)=(℩x)(\phi x),\)
> \(\vdash \colon(℩x)(\phi x)=(℩x)(\psi x).(℩x)(\psi x)=(℩x)(\chi x).\supset.(℩x)(\phi x)=(℩x)(\chi x).\)
> […] the chief way in which its incompleteness is relevant is that we do not always have
> \((x).fx.\supset.f({℩}x)(\phi x),\) […] The inference \((x).fx.\supset.f({℩}x)(\phi x)\) is
> only valid when \(\text{E}!({℩}x)(\phi x)\).

**Lean reading.** As in ✱14 (`Part1/SectionB.lean`, ✱14·18, ✱14·16, ✱14·28, ✱14·131, ✱14·144):
an identity of two descriptions is `TheIs2 φ ψ (· = ·)`; in `f(℩x)(φx) ≡ f(℩x)(ψx)` each description
has the smallest scope `f(…)`. The e-text prints `f(℩x)((φx)`. "Only valid when `E!`" is the
equivalence of `E!(℩x)(φx)` with the validity of the inference for all `f`.

**Status.** complete. All proved.
-/

/-- Intro, Ch. III. \(\vdash \colon\ldotp \text{E}!(℩x)(\phi x).\supset \colon (x).fx.\supset.f(℩x)(\phi x)\) -/
theorem desc_of_forall {φ f : α → Prop} : EBang φ → ((∀ x, f x) → TheIs φ f) :=
  fun ⟨b, hb⟩ h => ⟨b, hb, h b⟩

/-- Intro, Ch. III. \(\vdash \colon(℩x)(\phi x)=(℩x)(\psi x).\supset.f(℩x)(\phi x)\equiv f(℩x)(\psi x)\)
(the e-text prints `f(℩x)((φx)`). -/
theorem desc_eq_subst {φ ψ f : α → Prop} :
    TheIs2 φ ψ (fun b c => b = c) → (TheIs φ f ↔ TheIs ψ f) := by
  rintro ⟨c, hc, d, hd, e⟩
  rw [TheIs_iff_of_unique hc, TheIs_iff_of_unique hd, show c = d from e]

/-- Intro, Ch. III. \(\vdash \colon \text{E}!(℩x)(\phi x).\supset.(℩x)(\phi x)=(℩x)(\phi x)\) -/
theorem desc_eq_self {φ : α → Prop} : EBang φ → TheIs2 φ φ (fun b c => b = c) :=
  fun ⟨b, hb⟩ => ⟨b, hb, b, hb, rfl⟩

/-- Intro, Ch. III. \(\vdash \colon(℩x)(\phi x)=(℩x)(\psi x).\equiv.(℩x)(\psi x)=(℩x)(\phi x)\) -/
theorem desc_eq_symm {φ ψ : α → Prop} :
    TheIs2 φ ψ (fun b c => b = c) ↔ TheIs2 ψ φ (fun b c => b = c) :=
  ⟨fun ⟨c, hc, d, hd, e⟩ => ⟨d, hd, c, hc, e.symm⟩, fun ⟨c, hc, d, hd, e⟩ => ⟨d, hd, c, hc, e.symm⟩⟩

/-- Intro, Ch. III.
\(\vdash \colon(℩x)(\phi x)=(℩x)(\psi x).(℩x)(\psi x)=(℩x)(\chi x).\supset.(℩x)(\phi x)=(℩x)(\chi x)\) -/
theorem desc_eq_trans {φ ψ χ : α → Prop} :
    TheIs2 φ ψ (fun b c => b = c) ∧ TheIs2 ψ χ (fun b c => b = c) →
      TheIs2 φ χ (fun b c => b = c) := by
  rintro ⟨⟨c, hc, d, hd, e1⟩, ⟨d', hd', g, hg, e2⟩⟩
  have e : d = d' := (hd' d).1 ((hd d).2 rfl)
  exact ⟨c, hc, g, hg, e1.trans (e.trans e2)⟩

/-- Intro, Ch. III: "The inference \((x).fx.\supset.f({℩}x)(\phi x)\) is only valid when
\(\text{E}!({℩}x)(\phi x)\)." -/
theorem desc_of_forall_iff {φ : α → Prop} :
    (∀ f : α → Prop, (∀ x, f x) → TheIs φ f) ↔ EBang φ :=
  ⟨fun h => (TheIs_iff.1 (h (fun _ => True) fun _ => trivial)).1, fun h _ => desc_of_forall h⟩

/-!
## [intro.classes-incomplete] Classes as incomplete symbols

*(Vol. 1, Introduction, Chapter III, (2))*

> Two propositional functions are said to be *formally* equivalent when they are equivalent with
> every possible argument, […] "\(\hat{x}\) is an even prime" is formally equivalent to
> "\(\hat{x}\) is identical with 2." […]
> The derived function, written "\(f\{\hat{z}(\phi z)\}\)," is defined as follows: Given a
> function \(f(\psi ! \hat{z}\)), our derived function is to be "there is a predicative function
> which is formally equivalent to \(\phi \hat{z}\) and satisfies \(f\)." […] If \(f(\phi
> \hat{z}\)) is an extensional function, and \(\phi \hat{z}\) is a predicative function, our
> derived function will not be true unless \(f(\phi \hat{z}\)) is true; thus in this case, our
> derived function is equivalent to \(f(\phi \hat{z}\)). […] But in any case the derived function
> is always extensional. […] (1) Every propositional function must determine a class […] the
> "null-class" must be just as good a class as any other. […] from the definition of
> \(\unicode{x201c}\chi !\hat{z} = \theta!\hat{z}, \unicode{x201d}\) \(\text{which is}\quad \chi
> !\hat{z}= \theta!.\hat{z}=\colon (f)\colon f!\chi !\hat{z}.\supset.f!\theta !\hat{z}\,
> \quad\text{Df}\) by the general definition of identity. […] which, by eliminating
> \(\hat{z}(\psi z\)), becomes \((\exists \chi) \colon\ldotp \phi x.\equiv_{x}.\chi !x
> \colon\ldotp (\exists \theta)\colon \psi x.\equiv_{x}.\theta !x\colon \chi !\hat{z} = \theta
> !\hat{z},\) […] which, again, is equivalent to \((\exists \chi) \colon \phi x \ldotp \equiv_{x}
> \ldotp \chi!x \colon \psi x \ldotp \equiv_{x} \ldotp \chi!x,\) which, in virtue of the axiom of
> reducibility, is equivalent to \(\phi x \ldotp \equiv_{x} \ldotp \psi x.\) […] the meaning it
> gives is, in virtue of the definition of \(f\{\hat{z}(\phi z)\}\), \((\exists\psi) \colon \phi
> y \ldotp \equiv_{y} \ldotp \psi!y \colon \psi!x.\) […] Thus in
> virtue of the axiom of reducibility we have \(\vdash \colon x \in \hat{z}(\phi z) \ldotp \equiv
> \ldotp \phi x,\) […] \(\vdash \colon\ldotp \gamma \in \hat{\alpha} (f\alpha) \ldotp \equiv :
> (\exists g) : f\beta \ldotp \equiv_{\beta} \ldotp g!\beta : g!\gamma.\) […] Thus \(\vdash
> \colon \gamma \in \hat{\alpha}(f \alpha).\equiv.f \gamma.\) […] it might appear as if the class
> of all classes were a class, *i.e.* as if […] "\(\text{Cls}\,\in\, \text{Cls}\)" were a true
> proposition. But this combination of symbols must be meaningless; unless, indeed, an ambiguity
> exists in the meaning of "Cls," so that, in "\(\text{Cls}\, \in\, \text{Cls}\)," the first
> "Cls" can be supposed to have a different meaning from the second. […] it follows that the
> truth-value of any proposition in which \(\hat{z}(\phi z)\) occurs is the same whatever scope
> we may give to \(\hat{z}(\phi z)\), provided the proposition is an extensional function of
> whatever functions it may contain. […] Similarly when two class symbols occur, *e.g.* in a
> proposition of the form \(f\{\hat{z}(\phi z),\hat{z}(\psi z)\}\), we need not remember rules
> for the scopes of the two symbols, since all choices give equivalent results, as it is easy to
> prove. […] the easily proved
> proposition: "\(\vdash :\phi x\equiv_{x}\psi x.\supset .f\{\hat{z}(\phi z)\}\equiv f\{\hat{z}(\psi
> z)\}.\)" […] \(\vdash \colon(\alpha).f_{\alpha}.\supset.f\{\hat{x}(\phi x)\},\) \(\vdash \colon
> \hat{x}(\phi x)=\hat{x}(\psi x).\supset.f\{\hat{x}(\phi x)\}\equiv f\{\hat{x}(\psi x)\},\)
> \(\vdash .\hat{x}(\phi x)=\hat{x}(\phi x),\) \(\vdash \colon \hat{x}(\phi x)=\hat{x}(\psi
> x).\equiv.\hat{x}(\psi x)=\hat{x}(\phi x),\) \(\vdash \colon \hat{x}(\phi x)=\hat{x}(\psi
> x).\hat{x}(\psi x)=\hat{x}(\chi x).\supset.\hat{x}(\phi x)=\hat{x}(\chi x).\)

**Lean reading.** The derived function `f{ẑ(φz)}` is written out as PM defines it,
`∃ χ : α → Prop, (∀ x, φ x ↔ χ x) ∧ f χ`, for an arbitrary function of functions `f`; its
properties are proved without assuming `f` extensional. The class-symbol `ẑ(φz)` itself is
`{z | φ z} : Set α` (✱20, Basic §6). The fifth requisite ("`α ∈ α` meaningless") is Lean's typing;
`Cls ∈ Cls` is significant exactly when the two `Cls` have different types, and then true. The
e-text prints `(α).f_α` for `(α).fα`.

**Status.** complete. All proved; `Cls ∈ Cls` proved (reading) (the two `Cls` at different types,
PM's "ambiguity in the meaning of Cls").
-/

/-- Intro, Ch. III: "\(\hat{x}\) is an even prime" is formally equivalent to "\(\hat{x}\) is
identical with 2" (for the natural numbers). -/
theorem even_prime_iff_eq_two : ∀ n : ℕ, (Even n ∧ n.Prime) ↔ n = 2 := by
  intro n
  constructor
  · rintro ⟨he, hp⟩
    exact (Nat.Prime.even_iff hp).1 he
  · rintro rfl
    exact ⟨even_two, Nat.prime_two⟩

/-- Intro, Ch. III: the definition of identity of functions,
\(\chi !\hat{z}= \theta!\hat{z}.=\colon (f)\colon f!\chi !\hat{z}.\supset.f!\theta !\hat{z}\) (the
e-text prints `θ!.ẑ`).

**Status.** proved (reading): Lean's `=` between functions is primitive; the Df becomes the
equivalence of `=` with PM's definiens (every function of functions is predicative). -/
theorem function_identity_def {χ θ : α → Prop} :
    χ = θ ↔ ∀ f : (α → Prop) → Prop, f χ → f θ :=
  ⟨fun h _ hf => h ▸ hf, fun h => h (fun g => χ = g) rfl⟩

/-- Intro, Ch. III: the derived function \(f\{\hat{z}(\phi z)\}\) is always extensional, even when
`f` is not. -/
theorem derived_extensional {f : (α → Prop) → Prop} {φ ψ : α → Prop} (h : ∀ x, φ x ↔ ψ x) :
    (∃ χ : α → Prop, (∀ x, φ x ↔ χ x) ∧ f χ) ↔ ∃ χ : α → Prop, (∀ x, ψ x ↔ χ x) ∧ f χ :=
  ⟨fun ⟨χ, hχ, hf⟩ => ⟨χ, fun x => (h x).symm.trans (hχ x), hf⟩,
    fun ⟨χ, hχ, hf⟩ => ⟨χ, fun x => (h x).trans (hχ x), hf⟩⟩

/-- Intro, Ch. III: if `f` is extensional, the derived function is equivalent to `f(φẑ)`
("at this point, we make use of the axiom of reducibility"). -/
theorem derived_eq_of_extensional {f : (α → Prop) → Prop} {φ : α → Prop}
    (hf : ∀ χ θ : α → Prop, (∀ x, χ x ↔ θ x) → (f χ ↔ f θ)) :
    (∃ χ : α → Prop, (∀ x, φ x ↔ χ x) ∧ f χ) ↔ f φ :=
  ⟨fun ⟨χ, hχ, h⟩ => (hf φ χ hχ).2 h, fun h => ⟨φ, fun _ => Iff.rfl, h⟩⟩

/-- Intro, Ch. III, first requisite: every propositional function determines a class, and the
null-class is as good a class as any other. -/
theorem every_function_determines_class (φ : α → Prop) :
    (∃ A : Set α, ∀ x, x ∈ A ↔ φ x) ∧ ∃ A : Set α, ∀ x, x ∉ A :=
  ⟨⟨{x | φ x}, fun _ => Iff.rfl⟩, ⟨∅, fun _ h => h⟩⟩

/-- Intro, Ch. III, second and third requisites: eliminating both class symbols in
\(\hat{z}(\phi z) = \hat{z}(\psi z)\) gives
\((\exists \chi) \colon\ldotp \phi x.\equiv_{x}.\chi !x \colon\ldotp (\exists \theta)\colon \psi
x.\equiv_{x}.\theta !x\colon \chi !\hat{z} = \theta !\hat{z}\), which is equivalent to
\(\phi x \ldotp \equiv_{x} \ldotp \psi x\). -/
theorem class_eq_eliminated {φ ψ : α → Prop} :
    (∃ χ : α → Prop, (∀ x, φ x ↔ χ x) ∧ ∃ θ : α → Prop, (∀ x, ψ x ↔ θ x) ∧ χ = θ) ↔
      ∀ x, φ x ↔ ψ x :=
  ⟨fun ⟨_, hχ, _, hθ, e⟩ => fun x => (hχ x).trans (e ▸ (hθ x).symm),
    fun h => ⟨φ, fun _ => Iff.rfl, φ, fun x => (h x).symm, rfl⟩⟩

/-- Intro, Ch. III: \((\exists \chi) \colon \phi x \ldotp \equiv_{x} \ldotp \chi!x \colon \psi x
\ldotp \equiv_{x} \ldotp \chi!x\) is equivalent to \(\phi x \ldotp \equiv_{x} \ldotp \psi x\). -/
theorem common_predicative_iff {φ ψ : α → Prop} :
    (∃ χ : α → Prop, (∀ x, φ x ↔ χ x) ∧ ∀ x, ψ x ↔ χ x) ↔ ∀ x, φ x ↔ ψ x :=
  ⟨fun ⟨_, h1, h2⟩ x => (h1 x).trans (h2 x).symm, fun h => ⟨φ, fun _ => Iff.rfl, fun x => (h x).symm⟩⟩

/-- Intro, Ch. III: "\(x \in \hat{z}(\phi z)\)" means
\((\exists\psi) \colon \phi y \ldotp \equiv_{y} \ldotp \psi!y \colon \psi!x\), which is
equivalent to \(\phi x\). -/
theorem mem_class_eliminated {φ : α → Prop} {x : α} :
    (∃ ψ : α → Prop, (∀ y, φ y ↔ ψ y) ∧ ψ x) ↔ φ x :=
  ⟨fun ⟨_, h, hx⟩ => (h x).2 hx, fun h => ⟨φ, fun _ => Iff.rfl, h⟩⟩

/-- Intro, Ch. III, fourth requisite: classes of classes.
\(\vdash \colon\ldotp \gamma \in \hat{\alpha} (f\alpha) \ldotp \equiv : (\exists g) : f\beta \ldotp
\equiv_{\beta} \ldotp g!\beta : g!\gamma\), and \(\vdash \colon \gamma \in \hat{\alpha}(f
\alpha).\equiv.f \gamma\). -/
theorem mem_class_of_classes {f : Set α → Prop} {G : Set α} :
    ((G ∈ {A : Set α | f A}) ↔ ∃ g : Set α → Prop, (∀ B, f B ↔ g B) ∧ g G) ∧
      (G ∈ {A : Set α | f A} ↔ f G) :=
  ⟨⟨fun h => ⟨f, fun _ => Iff.rfl, h⟩, fun ⟨_, hg, h⟩ => (hg G).2 h⟩, Iff.rfl⟩

/-- Intro, Ch. III: "\(\text{Cls}\, \in\, \text{Cls}\)" is significant only if "the first `Cls`
can be supposed to have a different meaning from the second", and then it is true.

**Status.** proved (reading): `Cls` is typically ambiguous; the first is the class of classes of
`α`-things, the second the class of classes of classes of `α`-things. -/
theorem Cls_mem_Cls : (Cls : Set (Set α)) ∈ (Cls : Set (Set (Set α))) := by
  rw [Cls_eq_univ (α := Set α)]
  exact Set.mem_univ _

/-- Intro, Ch. III: the truth-value of a proposition in which `ẑ(φz)` occurs is the same whatever
scope is given to `ẑ(φz)`: with the derived function written out, the scope `F(f ẑ(φz))` and the
scope `f ẑ(φz)` inside `F` agree, for every `F` and `f`.

**Status.** proved (reading): PM's proviso "provided the proposition is an extensional function of
whatever functions it may contain" always holds in Lean (function and propositional
extensionality). -/
theorem class_scope_irrelevant (f : (α → Prop) → Prop) (φ : α → Prop) (F : Prop → Prop) :
    (∃ χ : α → Prop, (∀ x, φ x ↔ χ x) ∧ F (f χ)) ↔
      F (∃ χ : α → Prop, (∀ x, φ x ↔ χ x) ∧ f χ) := by
  have key : ∀ χ : α → Prop, (∀ x, φ x ↔ χ x) ↔ χ = φ := fun χ =>
    ⟨fun h => funext fun x => propext (h x).symm, fun h => h ▸ fun _ => Iff.rfl⟩
  simp only [key, exists_eq_left]

/-- Intro, Ch. III: with two class symbols, `f{ẑ(φz), ẑ(ψz)}`, "all choices [of scope] give
equivalent results".

**Status.** proved (reading): the class symbols are eliminated by the derived-function definition
in either order. -/
theorem two_class_symbols_scope (f : (α → Prop) → (α → Prop) → Prop) (φ ψ : α → Prop) :
    (∃ χ : α → Prop, (∀ x, φ x ↔ χ x) ∧ ∃ θ : α → Prop, (∀ x, ψ x ↔ θ x) ∧ f χ θ) ↔
      ∃ θ : α → Prop, (∀ x, ψ x ↔ θ x) ∧ ∃ χ : α → Prop, (∀ x, φ x ↔ χ x) ∧ f χ θ :=
  ⟨fun ⟨χ, hχ, θ, hθ, h⟩ => ⟨θ, hθ, χ, hχ, h⟩, fun ⟨θ, hθ, χ, hχ, h⟩ => ⟨χ, hχ, θ, hθ, h⟩⟩

/-- Intro, Ch. III: the easily proved proposition
\(\vdash :\phi x\equiv_{x}\psi x.\supset .f\{\hat{z}(\phi z)\}\equiv f\{\hat{z}(\psi z)\}\). -/
theorem class_subst_of_formal_equiv {f : Set α → Prop} {φ ψ : α → Prop} (h : ∀ x, φ x ↔ ψ x) :
    f {z | φ z} ↔ f {z | ψ z} := by
  rw [setOf_eq_setOf_iff.2 h]

/-- Intro, Ch. III. \(\vdash \colon(\alpha).f\alpha.\supset.f\{\hat{x}(\phi x)\}\) (the e-text
prints `f_α`). -/
theorem class_of_forall {f : Set α → Prop} {φ : α → Prop} : (∀ A : Set α, f A) → f {x | φ x} :=
  fun h => h _

/-- Intro, Ch. III.
\(\vdash \colon \hat{x}(\phi x)=\hat{x}(\psi x).\supset.f\{\hat{x}(\phi x)\}\equiv f\{\hat{x}(\psi x)\}\) -/
theorem class_eq_subst {f : Set α → Prop} {φ ψ : α → Prop} :
    {x | φ x} = {x | ψ x} → (f {x | φ x} ↔ f {x | ψ x}) := fun h => by rw [h]

/-- Intro, Ch. III. \(\vdash .\hat{x}(\phi x)=\hat{x}(\phi x)\) -/
theorem class_eq_refl {φ : α → Prop} : {x | φ x} = {x | φ x} := rfl

/-- Intro, Ch. III. \(\vdash \colon \hat{x}(\phi x)=\hat{x}(\psi x).\equiv.\hat{x}(\psi x)=\hat{x}(\phi x)\) -/
theorem class_eq_symm {φ ψ : α → Prop} : {x | φ x} = {x | ψ x} ↔ {x | ψ x} = {x | φ x} := eq_comm

/-- Intro, Ch. III.
\(\vdash \colon \hat{x}(\phi x)=\hat{x}(\psi x).\hat{x}(\psi x)=\hat{x}(\chi x).\supset.\hat{x}(\phi x)=\hat{x}(\chi x)\) -/
theorem class_eq_trans {φ ψ χ : α → Prop} :
    {x | φ x} = {x | ψ x} ∧ {x | ψ x} = {x | χ x} → {x | φ x} = {x | χ x} :=
  fun h => h.1.trans h.2

/-!
## [intro.functions-extensional] Functions and classes coincide in Lean

*(Vol. 1, Introduction, Chapter III, (2); Vol. II, Prefatory Statement, I)*

> In regard to classes, the relevance of their incompleteness is somewhat different. It may be
> illustrated by the fact that we may have \(\hat{z}(\phi z)=\psi !\hat{z}.\hat{z}(\phi z)=\chi
> !\hat{z}\) without having \(\psi!\hat{z}=\chi!\hat{z}.\) For, by a direct application of the
> definitions, we find that \(\vdash \colon\hat{z}(\phi z)=\psi !\hat{z}.\equiv.\phi
> x\equiv_{x}\psi !x.\) […] for two functions may well be formally equivalent without being
> identical […] Hence there is a propositional function, namely \(x=y.x=z.\supset.y=z,\) which
> holds without any exception, and yet does not hold when for \(x\) we substitute a class, and
> for \(y\) and \(z\) we substitute functions. […] If we take the whole of the product as the
> scope of \(\hat{z}(\phi z)\), the product is equivalent to \((\exists \theta)\colon \phi
> x\equiv_{x}\theta !x.\theta !\hat{z}=\psi !\hat{z}.\theta!\hat{z}=\chi !\hat{z},\) and this
> *does* imply \(\psi !\hat{z}=\chi !\hat{z}.\) […] (Vol. II:) But identity between a function and a
> class does not have the usual properties of identity; in fact, though every function is identical
> with some class, and vice versa, the number of functions is likely to be greater than the number
> of classes.

**Lean reading.** PM's functions are intensional ("George IV wished to know whether …"). Lean's
are extensional: classes `Set α` correspond exactly to functions `α → Prop`, formally equivalent
functions are equal (function and propositional extensionality), and the identity of a class with
functions is transitive. PM's contrary possibilities therefore do not arise; the declarations
record the Lean facts.

**Status.** complete. remark: Lean's functions are extensional, so the intensional distinctions of
the text vanish; the declarations prove the Lean counterparts.
-/

/-- Intro, Ch. III: "two functions may well be formally equivalent without being identical".

**Status.** remark: PM's functions are intensional; in Lean formally equivalent functions are
identical (function and propositional extensionality), which this declaration proves. -/
theorem formally_equivalent_functions_eq {ψ χ : α → Prop} (h : ∀ x, ψ x ↔ χ x) : ψ = χ :=
  funext fun x => propext (h x)

/-- Intro, Ch. III: "we may have \(\hat{z}(\phi z)=\psi !\hat{z}.\hat{z}(\phi z)=\chi !\hat{z}\)
without having \(\psi!\hat{z}=\chi!\hat{z}\)".

**Status.** remark: PM's functions are intensional. In Lean, "`ẑ(φz) = ψ!ẑ`" and "`ẑ(φz) = χ!ẑ`",
each with its own scope (as in `class_eq_function_iff`), do give `ψ = χ`, since formally equivalent
functions are equal; the declaration proves this. -/
theorem class_function_identity {φ ψ χ : α → Prop}
    (h1 : ∃ θ : α → Prop, (∀ x, φ x ↔ θ x) ∧ θ = ψ)
    (h2 : ∃ θ : α → Prop, (∀ x, φ x ↔ θ x) ∧ θ = χ) : ψ = χ := by
  obtain ⟨_, h1, rfl⟩ := h1
  obtain ⟨_, h2, rfl⟩ := h2
  exact funext fun x => propext ((h1 x).symm.trans (h2 x))

/-- Intro, Ch. III: \(\vdash \colon\hat{z}(\phi z)=\psi !\hat{z}.\equiv.\phi x\equiv_{x}\psi !x\),
with `ẑ(φz) = ψ!ẑ` read by the definition of `f{ẑ(φz)}`. -/
theorem class_eq_function_iff {φ ψ : α → Prop} :
    (∃ θ : α → Prop, (∀ x, φ x ↔ θ x) ∧ θ = ψ) ↔ ∀ x, φ x ↔ ψ x :=
  ⟨fun ⟨_, h, e⟩ => e ▸ h, fun h => ⟨ψ, h, rfl⟩⟩

/-- Intro, Ch. III: \(x=y.x=z.\supset.y=z\) "holds without any exception". -/
theorem eq_eq_imp_eq {x y z : α} : x = y ∧ x = z → y = z := fun h => h.1.symm.trans h.2

/-- Intro, Ch. III: with the whole product as the scope of `ẑ(φz)`,
\((\exists \theta)\colon \phi x\equiv_{x}\theta !x.\theta !\hat{z}=\psi !\hat{z}.\theta!\hat{z}=\chi
!\hat{z}\) "*does* imply" \(\psi !\hat{z}=\chi !\hat{z}\). -/
theorem class_function_whole_scope {φ ψ χ : α → Prop} :
    (∃ θ : α → Prop, (∀ x, φ x ↔ θ x) ∧ θ = ψ ∧ θ = χ) → ψ = χ :=
  fun ⟨_, _, e1, e2⟩ => e1.symm.trans e2

/-- Vol. II, Prefatory Statement I: "every function is identical with some class, and vice versa".

**Status.** remark: in Lean the classes of `α`-things correspond exactly to the functions
`α → Prop` (`A ↦ (· ∈ A)` and `φ ↦ {z | φ z}` are mutually inverse). -/
theorem classes_are_functions : Nonempty (Set α ≃ (α → Prop)) :=
  ⟨⟨fun A x => x ∈ A, fun φ => {z | φ z}, fun _ => rfl, fun _ => rfl⟩⟩

/-!
## [intro.relations-incomplete] Relations as incomplete symbols

*(Vol. 1, Introduction, Chapter III, (3))*

> \(f\{\hat{x}\hat{y} \phi(x,y)\}.=\colon(\exists \psi)\colon \phi(x,y).\equiv_{x,y}.\psi
> !(x,y)\colon f\{\psi!(\hat{x},\hat{y}\} \quad \text{Df}.\) […] Thus we have always \(\vdash
> \colon x\{\hat{x}\hat{y} \phi(x,y)\}y.\equiv.\phi(x,y).\) […] \(\vdash \colon\ldotp R=S.\equiv
> \colon xRy.\equiv_{x,y}.xSy,\) \(\vdash \colon\ldotp R=\hat{x}\hat{y} \phi(x,y).\equiv \colon
> xRy.\equiv_{x,y}.\phi(x,y),\) and \(\vdash .R=\hat{x}\hat{y}(xRy).\) […] \(\vdash \colon(R).fR
> .\supset.f\{\hat{x}\hat{y} \phi(x,y)\},\) \(\vdash \colon \hat{x}\hat{y} \phi(x,y)=\hat{x}\hat{y}
> \psi(x,y).\supset.f\{\hat{x}\hat{y}\phi (x,y)\}\equiv f\{\hat{x}\hat{y} \psi(x,y)\},\) \(\vdash
> .\hat{x}\hat{y} \phi(x,y)=\hat{x}\hat{y} \phi(x,y),\) \(\vdash \colon \hat{x}\hat{y}
> \phi(x,y)=\hat{x}\hat{y} \psi(x,y).\equiv.\hat{x}\hat{y} \psi(x,y)=\hat{x}\hat{y} \phi(x,y),\)
> \(\vdash \colon \hat{x}\hat{y} \phi(x,y)=\hat{x}\hat{y} \psi(x,y).\hat{x}\hat{y}\psi(x,y)=
> \hat{x}\hat{y} \chi(x,y).\supset.\hat{x}\hat{y} \phi(x,y)=\hat{x}\hat{y} \chi(x,y).\)

**Lean reading.** As for classes, with relations `α → β → Prop` (✱21). The membership and
extensionality theorems are in `[intro.relations]`; here the derived function and the identity
rules.

**Status.** complete. All proved.
-/

/-- Intro, Ch. III: the derived function of a function of relations is extensional, even when `f`
is not. -/
theorem derived_rel_extensional {f : (α → β → Prop) → Prop} {φ ψ : α → β → Prop}
    (h : ∀ x y, φ x y ↔ ψ x y) :
    (∃ χ : α → β → Prop, (∀ x y, φ x y ↔ χ x y) ∧ f χ) ↔
      ∃ χ : α → β → Prop, (∀ x y, ψ x y ↔ χ x y) ∧ f χ :=
  ⟨fun ⟨χ, hχ, hf⟩ => ⟨χ, fun x y => (h x y).symm.trans (hχ x y), hf⟩,
    fun ⟨χ, hχ, hf⟩ => ⟨χ, fun x y => (h x y).trans (hχ x y), hf⟩⟩

/-- Intro, Ch. III: \(x\{\hat{x}\hat{y} \phi(x,y)\}y\) means
\((\exists \psi)\colon \phi(x,y).\equiv_{x,y}. \psi !(x,y)\colon \psi !(x,y)\), which is
equivalent to \(\phi(x,y)\). -/
theorem rel_apply_eliminated {φ : α → β → Prop} {x : α} {y : β} :
    (∃ ψ : α → β → Prop, (∀ x y, φ x y ↔ ψ x y) ∧ ψ x y) ↔ φ x y :=
  ⟨fun ⟨_, h, hxy⟩ => (h x y).2 hxy, fun h => ⟨φ, fun _ _ => Iff.rfl, h⟩⟩

/-- Intro, Ch. III. \(\vdash \colon(R).fR .\supset.f\{\hat{x}\hat{y} \phi(x,y)\}\) -/
theorem rel_of_forall {f : (α → β → Prop) → Prop} {φ : α → β → Prop} :
    (∀ R : α → β → Prop, f R) → f (fun x y => φ x y) := fun h => h _

/-- Intro, Ch. III.
\(\vdash \colon \hat{x}\hat{y} \phi(x,y)=\hat{x}\hat{y} \psi(x,y).\supset.f\{\hat{x}\hat{y}\phi (x,y)\}\equiv f\{\hat{x}\hat{y} \psi(x,y)\}\) -/
theorem rel_eq_subst {f : (α → β → Prop) → Prop} {φ ψ : α → β → Prop} :
    (fun x y => φ x y) = (fun x y => ψ x y) → (f (fun x y => φ x y) ↔ f (fun x y => ψ x y)) :=
  fun h => by rw [h]

/-- Intro, Ch. III. \(\vdash .\hat{x}\hat{y} \phi(x,y)=\hat{x}\hat{y} \phi(x,y)\) -/
theorem rel_eq_refl {φ : α → β → Prop} : (fun x y => φ x y) = (fun x y => φ x y) := rfl

/-- Intro, Ch. III.
\(\vdash \colon \hat{x}\hat{y} \phi(x,y)=\hat{x}\hat{y} \psi(x,y).\equiv.\hat{x}\hat{y} \psi(x,y)=\hat{x}\hat{y} \phi(x,y)\) -/
theorem rel_eq_symm {φ ψ : α → β → Prop} :
    (fun x y => φ x y) = (fun x y => ψ x y) ↔ (fun x y => ψ x y) = (fun x y => φ x y) := eq_comm

/-- Intro, Ch. III.
\(\vdash \colon \hat{x}\hat{y} \phi(x,y)=\hat{x}\hat{y} \psi(x,y).\hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y} \chi(x,y).\supset.\hat{x}\hat{y} \phi(x,y)=\hat{x}\hat{y} \chi(x,y)\) -/
theorem rel_eq_trans {φ ψ χ : α → β → Prop} :
    (fun x y => φ x y) = (fun x y => ψ x y) ∧ (fun x y => ψ x y) = (fun x y => χ x y) →
      (fun x y => φ x y) = (fun x y => χ x y) :=
  fun h => h.1.trans h.2

/-! # Volume I: the Summaries and the Note to Section D -/

/-!
## [intro.summary-part1] The threefold division of classes

*(Vol. 1, Summary of Part I)*

> But classes have certain properties not possessed by propositions: these arise from the fact that
> classes have not a *two-fold* division corresponding to the division of propositions into true
> and false, but a *threefold* division, namely into (1) the universal class, which contains the
> whole of a certain type, (2) the null-class, which has no members, (3) all other classes, which
> neither contain nothing nor contain everything of the appropriate type.

**Lean reading.** Every `A : Set α` is `V`, or `Λ`, or has members and non-members. (The remark
that "`α` is contained in `β`" is not a class is Lean's typing: `A ⊆ B : Prop`.)

**Status.** complete. Proved.
-/

/-- Summary of Part I: every class is the universal class, the null-class, or neither contains
nothing nor contains everything of its type. -/
theorem threefold_division (A : Set α) : A = V ∨ A = Λ ∨ (A.Nonempty ∧ Aᶜ.Nonempty) := by
  by_cases h1 : A.Nonempty
  · by_cases h2 : Aᶜ.Nonempty
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · left
      rw [V_eq_univ, ← Set.compl_empty_iff]
      exact Set.not_nonempty_iff_eq_empty.1 h2
  · right; left
    rw [Null_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.1 h1

/-- Summary of Part I: the *two-fold* division of propositions into true and false.

**Status.** proved (reading): Lean's `Prop` with propositional extensionality; every proposition
is equal to `True` or to `False`. -/
theorem twofold_division (p : Prop) : p = True ∨ p = False := by
  by_cases h : p
  · exact Or.inl (propext ⟨fun _ => trivial, fun _ => h⟩)
  · exact Or.inr (propext ⟨h, False.elim⟩)

/-!
## [intro.note-section-d] General observations on relations

*(Vol. 1, Note to Section D)*

> (1) In order that a relation \(R\) may give rise to a descriptive function, it must be such that
> the referent is unique when the relatum is given. Thus, for example, the relations
> \(\text{Cnv}\), \(\overrightarrow{R}\), \(\overleftarrow{R}\), \(\text{D}\), \(\text{ᗡ}\),
> \(C\), \(R_{\in}\), defined above, all give rise to descriptive functions. […]
> The domain of a relation which gives rise to a descriptive function without limiting its domain or
> converse domain consists of all possible values of the function; the converse domain consists of
> all possible arguments to the function. Again, if \(R\) gives rise to a descriptive function,
> \(\overleftarrow{R}ʻx\) will be the class of those arguments for which the value of the function
> is \(x\). […] In this case, the relation is "one-one," […] We generally, in such cases, have some
> class \(\beta\) contained in the converse domain of our relation \(S\), and we have a class
> \(\alpha\) such that \(\alpha=Sʻʻ\beta\). In this case, the relation \(S\) correlates the members
> of \(\alpha\) and the members of \(\beta\). We shall have also \(\beta=\breve{S}ʻʻ\alpha\), so
> that, for such a relation, the correlation is reciprocal. […] the relation \(+1\) […] correlates
> with any class \(\alpha\) of numbers the class obtained by adding 1 to each member of \(\alpha\),
> *i.e.* (\(+1)ʻʻ\alpha\). This correlation may be used to prove that the number of finite
> integers is infinite […] for if we take as our class \(\alpha\) all the natural numbers including
> 0, the class (\(+1)ʻʻ\alpha\) consists of all the natural numbers except 0, so that the natural
> numbers can be correlated with a proper part […] of themselves.

**Lean reading.** "`R` gives rise to a descriptive function" is: no term has more than one
referent (`R x y ∧ R x' y → x = x'`); then the converse domain is `{y | E!R'y}`, the domain is the
class of values `R'y`, and `R⃖'x` is the class of `y` with `R'y = x`. A one-one `S` is one in which
moreover no term has more than one relatum. The relation `+1` is `graph (· + 1)` on `ℕ`.

**Status.** complete. All proved.
-/

/-- Note to Section D: "the relations \(\text{Cnv}\), \(\overrightarrow{R}\),
\(\overleftarrow{R}\), \(\text{D}\), \(\text{ᗡ}\), \(C\), \(R_{\in}\) […] all give rise to
descriptive functions": their descriptive functions exist for every argument. -/
theorem constant_relations_descriptive (R : α → β → Prop) (S : α → α → Prop) (x : α) (y : β)
    (A : Set β) :
    ((EDesc Cnv R ∧ EDesc (Rfwd R) y) ∧ (EDesc (Rbwd R) x ∧ EDesc D R)) ∧
      ((EDesc Dcnv R ∧ EDesc C S) ∧ EDesc (imgRel R) A) :=
  ⟨⟨⟨⟨R˘, fun _ => Cnv_iff⟩, EDesc_graph _ _⟩, EDesc_graph _ _, EDesc_graph _ _⟩,
    ⟨EDesc_graph _ _, EDesc_graph _ _⟩, EDesc_graph _ _⟩

/-- Note to Section D: the converse domain of a relation giving rise to a descriptive function
consists of all possible arguments to the function. -/
theorem codom_eq_args {R : α → β → Prop} (h : ∀ x x' y, R x y → R x' y → x = x') :
    codom R = {y | EDesc R y} := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun z => ⟨fun hz => h z x y hz hx, fun e => e ▸ hx⟩⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, (hb b).2 rfl⟩

/-- Note to Section D: the domain of a relation giving rise to a descriptive function consists of
all possible values of the function. -/
theorem dom_eq_values {R : α → β → Prop} (h : ∀ x x' y, R x y → R x' y → x = x') :
    dom R = {x | ∃ y, Desc R y (fun b => x = b)} := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, x, fun z => ⟨fun hz => h z x y hz hy, fun e => e ▸ hy⟩, rfl⟩
  · rintro ⟨y, b, hb, e⟩
    subst e
    exact ⟨y, (hb x).2 rfl⟩

/-- Note to Section D: \(\overleftarrow{R}ʻx\) is the class of those arguments for which the value
of the function is `x`. -/
theorem rels_eq_preimage {R : α → β → Prop} (h : ∀ x x' y, R x y → R x' y → x = x') (x : α) :
    rels R x = {y | Desc R y (fun b => x = b)} := by
  ext y
  constructor
  · intro hy
    exact ⟨x, fun z => ⟨fun hz => h z x y hz hy, fun e => e ▸ hy⟩, rfl⟩
  · rintro ⟨b, hb, e⟩
    subst e
    exact (hb x).2 rfl

/-- Note to Section D: for a one-one `S`, if \(\beta \subset \text{ᗡ}ʻS\) and
\(\alpha=Sʻʻ\beta\), then \(\beta=\breve{S}ʻʻ\alpha\): the correlation is reciprocal. (Only the
half "no term has more than one relatum" of one-one is used.) -/
theorem correlation_reciprocal {S : α → β → Prop} {A : Set α} {B : Set β}
    (h1 : ∀ x y y', S x y → S x y' → y = y') (_h2 : ∀ x x' y, S x y → S x' y → x = x')
    (hB : B ⊆ codom S) (hA : A = S ʻʻ B) : B = S˘ ʻʻ A := by
  subst hA
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := hB hy
    exact ⟨x, ⟨y, hy, hx⟩, hx⟩
  · rintro ⟨x, ⟨y', hy', hxy'⟩, hxy⟩
    rwa [h1 x y y' hxy hxy']

/-- Note to Section D: (\(+1)ʻʻ\alpha\), for \(\alpha\) all the natural numbers, consists of all the
natural numbers except 0, and `+1` is one-one: the natural numbers are correlated with a proper
part of themselves. -/
theorem succ_correlates_proper_part :
    graph (fun n : ℕ => n + 1) ʻʻ Set.univ = {n : ℕ | n ≠ 0} ∧
      Function.Injective (fun n : ℕ => n + 1) := by
  refine ⟨?_, fun a b h => Nat.succ_injective h⟩
  ext n
  constructor
  · rintro ⟨y, -, h⟩
    rw [graph_apply] at h
    show n ≠ 0
    omega
  · intro hn
    refine ⟨n - 1, trivial, ?_⟩
    rw [graph_apply]
    have : n ≠ 0 := hn
    omega

/-!
## [intro.summary-part2] The Schröder–Bernstein theorem

*(Vol. 1, Summary of Part II)*

> In this section, we define the notion of *similarity*, upon which all cardinal arithmetic is
> based: two classes are said to be *similar* when there is a one-one relation whose domain is the
> one and whose converse domain is the other. We prove the elementary properties of similarity,
> including the Schröder-Bernstein theorem, namely: If \(\alpha\) is similar to part of \(\beta\),
> and \(\beta\) is similar to part of \(\alpha\), then \(\alpha\) is similar to \(\beta\).

**Lean reading.** "`α` is similar to `β`" is ✱73·02's `sm A B` (`Defs/Part2`): some one-one
relation has domain `α` and converse domain `β`. "Part of `β`" is a subclass `β' ⊂ β`. PM proves the
theorem at ✱73·88; here it is the statement of the Summary, proved through mathlib's
Schröder–Bernstein theorem (`sm_iff_nonempty_equiv`).

**Status.** complete. Proved.
-/

/-- Summary of Part II: if `α` is similar to part of `β`, and `β` is similar to part of `α`, then
`α` is similar to `β`. -/
theorem schroeder_bernstein {β : Type u} {A : Set α} {B : Set β}
    (h1 : ∃ B' ⊆ B, sm A B') (h2 : ∃ A' ⊆ A, sm B A') : sm A B := by
  obtain ⟨B', hB', h1⟩ := h1
  obtain ⟨A', hA', h2⟩ := h2
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h1
  obtain ⟨f⟩ := sm_iff_nonempty_equiv.1 h2
  have i1 : A ↪ B := e.toEmbedding.trans (Set.embeddingOfSubset _ _ hB')
  have i2 : B ↪ A := f.toEmbedding.trans (Set.embeddingOfSubset _ _ hA')
  obtain ⟨g, hg⟩ := Function.Embedding.schroeder_bernstein i1.injective i2.injective
  exact sm_iff_nonempty_equiv.2 ⟨Equiv.ofBijective g hg⟩

/-! # Volume II: the Prefatory Statement of Symbolic Conventions -/

/-!
## [intro.prefatory-functions] The number of predicative functions of individuals

*(Vol. 2, Prefatory Statement, I)*

> It is to be observed, further, that, given the number of individuals, there is nothing in our
> axioms to show how many predicative functions of individuals there are, *i.e.* their number is
> not a function of the number of individuals: we only know that their number \(\geq
> 2^{\text{Nc}ʻ\text{Indiv}}\), where "\(\text{Indiv}\)" stands for the class of individuals.

**Lean reading.** The predicative functions of individuals of type `α` are `α → Prop`; their
number is `#(α → Prop)`. Lean's functions are extensional, so there are exactly `2 ^ #α` of them:
PM's inequality holds with equality (and the number *is* a function of the number of
individuals).

**Status.** complete. proved (reading): equality, since Lean's functions are extensional.
-/

open Cardinal in
/-- Prefatory Statement I: the number of predicative functions of individuals is
\(\geq 2^{\text{Nc}ʻ\text{Indiv}}\).

**Status.** proved (reading): PM's functions are intensional, so it can only assert `≥`; Lean's
functions of individuals are the classes of individuals, and their number is exactly `2 ^ #α`. -/
theorem card_functions (α : Type u) : #(α → Prop) = 2 ^ #α := by
  rw [← mk_set]
  exact mk_congr ⟨fun φ => {z | φ z}, fun A x => x ∈ A, fun _ => rfl, fun _ => rfl⟩

/-!
## [intro.prefatory-existence] Existence-theorems for cardinals in the various types

*(Vol. 2, Prefatory Statement, I)*

> In Vol. I. only two propositions occur which can be proved for higher but not for lower types.
> These are \(\exists !2\) and \(\exists !2_{r}\). These can be proved for any type except that of
> individuals. […] If, for example, \(\text{Nc}ʻ{\text{Indiv}} = \nu\), then this proposition is
> false for any higher type; but this proposition, \(\text{Nc}ʻ{\text{Indiv}} = \nu\), is one
> which cannot be proved logically; […] The propositions which can be proved in some types but not in others all are or
> depend upon existence-theorems for cardinals. We can prove \(\exists !0,\, \exists !1,\,
> \text{universally}\), \(\exists !2,\, \text{except for}\,\, \text{Indiv}\), \(\exists !3,\,
> \exists !4,\, \text{except for}\,\, \text{Indiv},\, \text{Cl}ʻ\text{Indiv},\,
> \text{Rl}ʻ\text{Indiv};\,\, \text{and so on}.\) […] Suppose there is only one individual,
> \(x\). Then \(\hat{y}=x\), \(\hat{y}\neq x\) are two different functions, which, by the axiom of
> reducibility, are equivalent to two different predicative functions. Hence there are at least
> two predicative functions of \(x\), and at least two classes \(\iotaʻx\), \(\Lambda_{x}\).

**Lean reading.** For `0`, `1`, `2`, `2_r` PM's own classes of `Defs/Part2` are used (✱54·01,
✱52·01, ✱54·02, ✱56·02): "`∃!2` in the type `Cl'Indiv`" is `(two : Set (Set (Set α))).Nonempty`,
the couples of classes of individuals. `3` and `4` belong to Part III; "`∃!n` in the type `τ`" is
read `∃ A : Set τ, #A = n`, which holds iff `n ≤ #τ`. "Can be proved for `τ`" is proved for every
type of that form (`Set α`, `Set (Set α)`, with PM's assumption that the type of individuals `α`
is nonempty); "cannot be proved for Indiv, `Cl'Indiv`, `Rl'Indiv`" is shown by the case of a
single individual (`α = Unit`), where they are false. "`Nc'Indiv = ν` is false for any higher
type": the number of classes of individuals is never the number of individuals (Cantor).

**Status.** complete. Proved; the positive claims proved (reading) (`[Nonempty α]`, PM's
assumption that every type has a member).
-/

open Cardinal in
/-- Prefatory Statement I: the cardinal `c` exists (as applied to classes of `τ`-objects) iff it
does not exceed the number of `τ`-objects. -/
theorem exists_card_iff (τ : Type u) (c : Cardinal.{u}) : (∃ A : Set τ, #A = c) ↔ c ≤ #τ :=
  le_mk_iff_exists_set.symm

/-- Prefatory Statement I: \(\exists !0\) universally. -/
theorem exists_zero (τ : Type u) : (zero : Set (Set τ)).Nonempty := ⟨Λ, rfl⟩

/-- Prefatory Statement I: \(\exists !1\) universally.

**Status.** proved (reading): PM assumes every type has a member; `[Nonempty τ]`. -/
theorem exists_one (τ : Type u) [Nonempty τ] : (one : Set (Set τ)).Nonempty :=
  let ⟨x⟩ := ‹Nonempty τ›; ⟨ι x, x, rfl⟩

/-- Prefatory Statement I: \(\exists !2\) can be proved for classes of individuals and for
relations of individuals (any type except that of individuals).

**Status.** proved (reading): PM assumes every type has a member; `[Nonempty α]`. -/
theorem exists_two_classes (α : Type u) [Nonempty α] :
    (two : Set (Set (Set α))).Nonempty ∧ (two : Set (Set (α → α → Prop))).Nonempty := by
  refine ⟨⟨ι ∅ ∪ ι Set.univ, ∅, Set.univ, Set.empty_ne_univ, rfl⟩,
    ⟨ι rNull ∪ ι rV, rNull, rV, fun h => ?_, rfl⟩⟩
  obtain ⟨x⟩ := ‹Nonempty α›
  exact rNull_apply x x ((congrFun (congrFun h x) x).symm ▸ ⟨rfl, rfl⟩)

/-- Prefatory Statement I: \(\exists !2_{r}\) can be proved for any type except that of
individuals: there are ordinal couples `x ↓ y` (`x ≠ y`) of classes of individuals.

**Status.** proved (reading): PM assumes every type has a member; `[Nonempty α]`. -/
theorem exists_two_r_classes (α : Type u) [Nonempty α] :
    (two_r : Set (Set α → Set α → Prop)).Nonempty :=
  ⟨∅ ↓ Set.univ, ∅, Set.univ, Set.empty_ne_univ, rfl⟩

/-- Prefatory Statement I: \(\exists !2\) and \(\exists !2_{r}\) cannot be proved for individuals:
they are false if there is only one individual. -/
theorem not_exists_two_one_individual :
    ¬ (two : Set (Set Unit)).Nonempty ∧ ¬ (two_r : Set (Unit → Unit → Prop)).Nonempty :=
  ⟨fun ⟨_, x, y, hxy, _⟩ => hxy (Subsingleton.elim x y),
    fun ⟨_, x, y, hxy, _⟩ => hxy (Subsingleton.elim x y)⟩

open Cardinal in
/-- Prefatory Statement I: \(\exists !3\) and \(\exists !4\) can be proved for classes of classes
of individuals.

**Status.** proved (reading): PM assumes every type has a member; `[Nonempty α]`. -/
theorem exists_three_four (α : Type u) [Nonempty α] :
    (∃ K : Set (Set (Set α)), #K = 3) ∧ ∃ K : Set (Set (Set α)), #K = 4 := by
  have h2 : (2 : Cardinal) ≤ #(Set α) := two_le_iff.mpr ⟨∅, Set.univ, Set.empty_ne_univ⟩
  have h4 : (4 : Cardinal) ≤ #(Set (Set α)) := by
    rw [mk_set]
    calc (4 : Cardinal) = 2 ^ (2 : Cardinal) := by
          rw [show (2 : Cardinal) = ((2 : ℕ) : Cardinal) from rfl, power_natCast]; norm_num
      _ ≤ 2 ^ #(Set α) := power_le_power_left two_ne_zero h2
  refine ⟨(exists_card_iff _ _).2 (le_trans ?_ h4), (exists_card_iff _ _).2 h4⟩
  exact_mod_cast (by decide : (3 : ℕ) ≤ 4)

open Cardinal in
/-- Prefatory Statement I: \(\exists !3\) (and so \(\exists !4\)) cannot be proved for
`Cl'Indiv` or `Rl'Indiv` (nor for `Indiv`): with a single individual there are only two classes
and two relations of individuals. -/
theorem not_exists_three_one_individual :
    (¬ ∃ A : Set Unit, #A = 3) ∧ (¬ ∃ K : Set (Set Unit), #K = 3) ∧
      ¬ ∃ L : Set (Unit → Unit → Prop), #L = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [exists_card_iff] <;> simp <;> exact_mod_cast (by decide : (2 : ℕ) < 3)

/-- Prefatory Statement I: with only one individual `x` there are at least two classes,
\(\iotaʻx\) and \(\Lambda_{x}\). -/
theorem two_classes_of_one_individual (x : α) : ι x ≠ (Λ : Set α) := by
  rw [Null_eq_empty]
  exact Set.nonempty_iff_ne_empty.1 ⟨x, rfl⟩

open Cardinal in
/-- Prefatory Statement I: "if `Nc'Indiv = ν`, then this proposition is false for any higher
type": the number of classes of individuals is never the number of individuals. -/
theorem census_false_in_higher_type (α : Type u) : #(Set α) ≠ #α := by
  rw [mk_set]
  exact (cantor #α).ne'

/-!
## [intro.prefatory-cantor-types] A cardinal can be null in one type and not in another

*(Vol. 2, Prefatory Statement, I)*

> Taking \(\text{Indiv}\) as a primitive idea, put \(\text{Kl} = \text{Cl}ʻ\text{Indiv}
> \quad\text{Df}\), \(\text{Kl}^{2} = \text{Cl}ʻ\text{Kl} \quad\text{Df}\), etc. Then consider the
> proposition \(\text{Nc}ʻ\text{Kl} = \Lambda\). We can prove \(\text{Nc}ʻ\text{Kl} \cap
> tʻ\text{Indiv} = \Lambda . \exists ! \text{Nc}ʻ\text{Kl} \cap tʻ\text{Kl} . \exists !
> \text{Nc}ʻ\text{Kl} \cap tʻ\text{Kl}^{2}.\) etc. Thus \(\text{Nc}ʻ\text{Kl} = \Lambda\) can be
> proved in the lowest type in which it is significant, and disproved in any other. The difficulty,
> however, is avoided if Indiv is replaced by a variable \(\alpha\), and \(\text{Kl}\) by
> \(\text{Cl}ʻt_{0}ʻ\alpha\). Then we have \(\text{Nc}ʻ\text{Cl}ʻt_{0}ʻ\alpha \cap tʻ\alpha =
> \Lambda,\) and this holds whatever the type of \(\alpha\) may be. […] *e.g.* we have \(\exists
> !\text{Nc}(\text{Kl})ʻ\text{Indiv}.{\sim}\exists!\text{Nc}(\text{Kl})ʻ\text{Kl}^{2}\). […] For
> it may happen that a class in one type has no class similar to it in some lower type (cf.
> *102·72·73).

**Lean reading.** With individuals of type `τ`, `Kl = Cl'Indiv` is `cl V : Set (Set τ)` (✱60·01,
`Defs/Part2`), `Kl² = Cl'Kl` is `cl (cl V)`, and `Nc'Kl ∩ t'σ` is the class of classes of
`σ`-objects similar (✱73·02 `sm`) to `Kl` (the definition ✱100·01 `Nc = sm⃗` restricted to the type
`σ`). "`Nc'Kl ∩ t'Indiv = Λ`" says no class of individuals is similar to `Kl`: Cantor's theorem,
which holds whatever the type `τ` ("`Nc'Cl't₀'α ∩ t'α = Λ`"). The cardinal `Nc'Kl` exists in the
types of `Kl` and of `Kl²` (witnesses `Kl` itself and the unit classes of classes).
`Nc(Kl)'Indiv`, the cardinal of the individuals taken in the type of `Kl`, exists (the unit
classes of individuals), while `Nc(Kl)'Kl²` is null: no class of classes of individuals is
similar to `Kl²`.

**Status.** complete. All proved.
-/

/-- Prefatory Statement I: \(\text{Nc}ʻ\text{Cl}ʻt_{0}ʻ\alpha \cap tʻ\alpha = \Lambda\) (and
\(\text{Nc}ʻ\text{Kl} \cap tʻ\text{Indiv} = \Lambda\)): no class of `τ`-objects is similar to the
class of all classes of `τ`-objects, whatever the type `τ`. -/
theorem Nc_Kl_null_in_Indiv (τ : Type u) : ¬ ∃ A : Set τ, sm A (cl (V : Set τ)) := by
  rintro ⟨A, h⟩
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
  have h1 := Cardinal.mk_set_le A
  have hcl : cl (V : Set τ) = Set.univ := Set.eq_univ_of_forall fun _ _ _ => rfl
  rw [Cardinal.mk_congr e, hcl, Cardinal.mk_univ, Cardinal.mk_set] at h1
  exact absurd h1 (not_le.mpr (Cardinal.cantor _))

/-- Prefatory Statement I: \(\exists ! \text{Nc}ʻ\text{Kl} \cap tʻ\text{Kl}\) and
\(\exists ! \text{Nc}ʻ\text{Kl} \cap tʻ\text{Kl}^{2}\). -/
theorem Nc_Kl_exists_in_Kl (τ : Type u) :
    (∃ K : Set (Set τ), sm K (cl (V : Set τ))) ∧
      ∃ K : Set (Set (Set τ)), sm K (cl (V : Set τ)) := by
  have hcl : cl (V : Set τ) = Set.univ := Set.eq_univ_of_forall fun _ _ _ => rfl
  refine ⟨⟨_, sm_refl _⟩, Set.range (fun A : Set τ => ({A} : Set (Set τ))),
    sm_iff_nonempty_equiv.2 ⟨?_⟩⟩
  rw [hcl]
  exact (Equiv.ofInjective _ Set.singleton_injective).symm.trans (Equiv.Set.univ _).symm

/-- Prefatory Statement I:
\(\exists !\text{Nc}(\text{Kl})ʻ\text{Indiv}.{\sim}\exists!\text{Nc}(\text{Kl})ʻ\text{Kl}^{2}\). -/
theorem Nc_Kl_Indiv_exists_Kl2_null (τ : Type u) :
    (∃ K : Set (Set τ), sm K (V : Set τ)) ∧
      ¬ ∃ K : Set (Set τ), sm K (cl (cl (V : Set τ))) := by
  have hV : (V : Set τ) = Set.univ := V_eq_univ
  refine ⟨⟨Set.range (fun x : τ => ({x} : Set τ)), sm_iff_nonempty_equiv.2 ⟨?_⟩⟩, ?_⟩
  · rw [hV]
    exact (Equiv.ofInjective _ Set.singleton_injective).symm.trans (Equiv.Set.univ _).symm
  · rintro ⟨K, h⟩
    have hcl : cl (V : Set τ) = Set.univ := Set.eq_univ_of_forall fun _ _ _ => rfl
    have hcl2 : cl (cl (V : Set τ)) = Set.univ := Set.eq_univ_of_forall fun _ _ _ => by
      rw [hcl]; trivial
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
    have h1 := Cardinal.mk_set_le K
    rw [Cardinal.mk_congr e, hcl2, Cardinal.mk_univ, Cardinal.mk_set] at h1
    exact absurd h1 (not_le.mpr (Cardinal.cantor _))

/-!
## [intro.prefatory-stable] Permanent, fluctuating and stable truth-values: `2 +_c 3 = 5`

*(Vol. 2, Prefatory Statement, I)*

> For example, anticipating our definitions of elementary arithmetic, consider \(2 +_{c} 3 = 5\).
> There is no abstract logical proof that there are two individuals; so suppose 2 and 3 refer to
> classes of individuals, but 5 refers to classes of a high enough type, then with these
> determinations \(2 +_{c} 3 = 5\) cannot be proved. But \(2 +_{c} 3 = 5\) has a *stable*
> truth-value, since it can always be proved when all the types are high enough.

**Lean reading.** The arithmetical content of `2 +_c 3 = 5` (the union of disjoint classes of 2 and
3 members has 5 members) holds in every type. What fluctuates is existence: in the type of
individuals, with one individual, no class has 5 members (5 is null there), while in a high enough
type (classes of classes of classes of individuals, of which there are at least 16 when there is
one individual) the classes of 2, 3 and 5 members exist.

**Status.** complete. Proved; the existence in a high type proved (reading) (`[Nonempty α]`).
-/

open Cardinal in
/-- Prefatory Statement I: in any type, the union of disjoint classes of 2 and 3 members has 5
members. -/
theorem two_add_three (τ : Type u) (A B : Set τ) (hAB : Disjoint A B) (hA : #A = 2) (hB : #B = 3) :
    #(A ∪ B : Set τ) = 5 := by
  rw [mk_union_of_disjoint hAB, hA, hB]
  norm_num

open Cardinal in
/-- Prefatory Statement I: with a single individual, 5 is null in the type of individuals. -/
theorem five_null_one_individual : ¬ ∃ A : Set Unit, #A = 5 := by
  rw [exists_card_iff]
  simp

open Cardinal in
/-- Prefatory Statement I: in a high enough type all of 2, 3 and 5 exist.

**Status.** proved (reading): PM assumes every type has a member; `[Nonempty α]`. -/
theorem two_three_five_exist_high (α : Type u) [Nonempty α] :
    ∀ n : ℕ, n ≤ 16 → ∃ K : Set (Set (Set (Set α))), #K = n := by
  intro n hn
  have h2 : (2 : Cardinal) ≤ #(Set α) := two_le_iff.mpr ⟨∅, Set.univ, Set.empty_ne_univ⟩
  have h4 : (4 : Cardinal) ≤ #(Set (Set α)) := by
    rw [mk_set]
    calc (4 : Cardinal) = 2 ^ (2 : Cardinal) := by
          rw [show (2 : Cardinal) = ((2 : ℕ) : Cardinal) from rfl, power_natCast]; norm_num
      _ ≤ 2 ^ #(Set α) := power_le_power_left two_ne_zero h2
  have h16 : (16 : Cardinal) ≤ #(Set (Set (Set α))) := by
    rw [mk_set]
    calc (16 : Cardinal) = 2 ^ (4 : Cardinal) := by
          rw [show (4 : Cardinal) = ((4 : ℕ) : Cardinal) from rfl, power_natCast]; norm_num
      _ ≤ 2 ^ #(Set (Set α)) := power_le_power_left two_ne_zero h4
  refine (exists_card_iff _ _).2 (le_trans ?_ h16)
  exact_mod_cast hn

/-!
## [intro.prefatory-infinity] The axiom of infinity and the convention Infin T

*(Vol. 2, Prefatory Statement, VI)*

> One other convention, which we will call "\(\text{Infin T}\)," is required in certain propositions
> where the hypothesis implies that there are types in which every inductive cardinal exists,
> *i.e.* in which \(\text{V}\) is not an inductive class. […] This requires that the \(\nu\) should
> not be taken in a type in which we have \(\exists !\nu. \nu +_c 1 = \Lambda\). […] It is to be
> observed that this convention would be unnecessary if we confined ourselves to one extensional
> hierarchy, for in any one such hierarchy all types are inductive or all are non-inductive, so
> that if every inductive cardinal exists in one type in the hierarchy, the same holds for any other
> type in the hierarchy. But when we no longer confine ourselves to one extensional hierarchy, this
> result may not follow. For example, it may be the case that the number of individuals is
> inductive, but the number of predicative functions of individuals is not inductive […]

**Lean reading.** "Every inductive cardinal exists in the type `τ`" (the axiom of infinity in that
type, cf. ✱120·03) is `∀ n : ℕ, ∃ A : Set τ, #A = n`; it holds exactly when `τ` is infinite, so it
is not provable by logic (it fails for a type with one member). In a finite type there is an
inductive `ν` with `∃!ν . ν +_c 1 = Λ`. In one extensional hierarchy all types are inductive or all
non-inductive: `Set τ` is infinite iff `τ` is. Since Lean's functions of individuals *are* the
classes of individuals, the possibility PM leaves open (finitely many individuals but infinitely many
predicative functions of them) does not arise in Lean.

**Status.** complete. Proved; finitely many individuals with infinitely many predicative
functions: remark (it does not arise in Lean).
-/

open Cardinal in
/-- Prefatory Statement VI: every inductive cardinal exists in the type `τ` iff `τ` is infinite. -/
theorem infin_ax_iff (τ : Type u) : (∀ n : ℕ, ∃ A : Set τ, #A = n) ↔ Infinite τ := by
  rw [infinite_iff]
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := lt_aleph0.mp hlt
    obtain ⟨A, hA⟩ := h (n + 1)
    have h1 : #A ≤ #τ := mk_set_le A
    rw [hA, hn] at h1
    exact absurd (by exact_mod_cast h1 : n + 1 ≤ n) (Nat.not_succ_le_self n)
  · intro h n
    exact le_mk_iff_exists_set.mp ((natCast_lt_aleph0 (n := n)).le.trans h)

open Cardinal in
/-- Prefatory Statement VI: the axiom of infinity is not provable by logic: it fails in a type with
a single member. -/
theorem infin_ax_fails_one_individual : ¬ ∀ n : ℕ, ∃ A : Set Unit, #A = n := by
  rw [infin_ax_iff]
  exact not_infinite_iff_finite.mpr inferInstance

open Cardinal in
/-- Prefatory Statement VI: in a type in which not every inductive cardinal exists, there is an
inductive `ν` with \(\exists !\nu. \nu +_c 1 = \Lambda\). -/
theorem finite_type_null_successor (τ : Type u) [Finite τ] :
    ∃ n : ℕ, (∃ A : Set τ, #A = n) ∧ ¬ ∃ A : Set τ, #A = (n + 1 : ℕ) := by
  classical
  have h : ∃ n : ℕ, ¬ ∃ A : Set τ, #A = n := by
    by_contra h'
    exact not_infinite_iff_finite.mpr ‹Finite τ›
      ((infin_ax_iff τ).1 fun n => Classical.byContradiction fun hn => h' ⟨n, hn⟩)
  obtain ⟨k, hk⟩ : ∃ k, Nat.find h = k + 1 := Nat.exists_eq_succ_of_ne_zero (by
    intro h0
    have := Nat.find_spec h
    rw [h0] at this
    exact this ⟨∅, by simp⟩)
  refine ⟨k, ?_, ?_⟩
  · by_contra hc
    exact Nat.find_min h (by omega : k < Nat.find h) hc
  · have := Nat.find_spec h
    rwa [hk] at this

/-- Prefatory Statement VI: "in any one such hierarchy all types are inductive or all are
non-inductive": the classes of `τ`-objects are infinite in number iff the `τ`-objects are. -/
theorem infinite_classes_iff (τ : Type u) : Infinite (Set τ) ↔ Infinite τ := by
  constructor
  · intro h
    by_contra hτ
    rw [not_infinite_iff_finite] at hτ
    exact not_finite (Set τ)
  · intro _
    exact Infinite.of_injective (fun x : τ => ({x} : Set τ)) Set.singleton_injective

/-- Prefatory Statement VI: "it may be the case that the number of individuals is inductive, but
the number of predicative functions of individuals is not inductive". In Lean this cannot happen.

**Status.** remark: PM's functions are intensional; Lean's predicative functions of individuals
are `α → Prop`, finite in number whenever the individuals are (`card_functions`). -/
theorem finite_functions_of_finite (α : Type u) [Finite α] : Finite (α → Prop) := inferInstance

/-!
## [intro.prefatory-indefinite] The Rule of Indefinite Numbers

*(Vol. 2, Prefatory Statement, VII)*

> For by combining *126·121 *126·122 and *120·4232·4622, we see that it is always possible to
> take the type high enough so that no definitely determined inductive number shall be null
> (\(\Lambda)\), and that all the inductive reasoning can take place within this type.

**Lean reading.** The types of the extensional hierarchy starting from individuals of type `α` are
`Set^[k] α` (`k` applications of `Set`). For every inductive number `n` there is a `k` such that
`n` is not null in `Set^[k] α` (`∃ A : Set (Set^[k] α), #A = n`), given PM's assumption that there
are individuals.

**Status.** complete. proved (reading): `[Nonempty α]` (PM assumes every type has a member).
-/

open Cardinal in
/-- Prefatory Statement VII: for every inductive number there is a type, high enough in the
hierarchy over the individuals, in which it is not null.

**Status.** proved (reading): PM assumes every type has a member; `[Nonempty α]`. -/
theorem indefinite_numbers (α : Type u) [Nonempty α] :
    ∀ n : ℕ, ∃ k : ℕ, ∃ A : Set (Set^[k] α), #A = n := by
  have key : ∀ k : ℕ, ((k : ℕ) : Cardinal) < #(Set^[k] α) := by
    intro k
    induction k with
    | zero => simpa using pos_iff_ne_zero.mpr (mk_ne_zero α)
    | succ k ih =>
      rw [Function.iterate_succ_apply', mk_set, Nat.cast_succ]
      exact lt_of_le_of_lt (natCast_add_one_le_iff.mpr ih) (cantor _)
  intro n
  exact ⟨n, le_mk_iff_exists_set.mp (key n).le⟩

/-!
## [intro.cardinal-correlators] The General Note on cardinal correlators

*(Vol. 2, General Note on Cardinal Correlators, after ✱117)*

> Such correlators always depend upon *55·61. \(\vdash :\text{E}!Rʻx.\text{E}!Sʻy.\supset
> .(R\parallel \breve{S} )ʻ(x\downarrow y)=(Rʻx)\downarrow (Sʻy)\) together with the propositions
> *74·77 *seq.* […] It follows from *55·61 that if \(R\) and \(S\) are correlators whose converse
> domains include the domain and converse domain respectively of a relation \(P\), then
> \((R\parallel\breve{S})ʻP\) will be a relation holding between \(Rʻx\) and \(Sʻy\) whenever \(P\)
> holds between \(x\) and \(y\). […] Thus it will be seen that *116·192 in the above list is an
> immediate consequence of *113·127 and *115·502, since \(\alpha \,\,\text{exp}\,\,\beta
> =\text{Prod}ʻ\alpha \downarrow_{,,}ʻʻ\beta\,\text{and}\,sʻ\text{Prod}ʻ\gamma
> \downarrow_{,,}ʻʻ\delta =\delta \times \gamma\).

**Lean reading.** The Note's starred formulas are numbered propositions of Parts II–III, formalized
in their own sections. Its one new claim stated with Part I notions is the consequence of ✱55·61:
for correlators `R`, `S` (`R'x` exists for `x ∈ D'P`, `S'y` for `y ∈ ᗡ'P`), the relation
`(R ‖ S̆)'P` holds between `R'x` and `S'y` whenever `xPy`; it is stated with the descriptions
`R'x`, `S'y`, `(R ‖ S̆)'P` (`Desc`, ✱43·01 `∥`). The derivation of ✱116·192 from ✱113·127 and
✱115·502 uses the Part III notions `exp`, `Prod`, `↓,,` and is a remark here.

**Status.** complete. The consequence of ✱55·61 proved (reading) ("correlators whose converse
domains include …" read as the existence of `R'x`, `S'y` on `D'P`, `ᗡ'P`); the derivation of
✱116·192: remark (Part III).
-/

/-- General Note on Cardinal Correlators: if `R'x` exists for every `x ∈ D'P` and `S'y` for every
`y ∈ ᗡ'P`, then \((R\parallel\breve{S})ʻP\) holds between \(Rʻx\) and \(Sʻy\) whenever \(P\)
holds between \(x\) and \(y\).

**Status.** proved (reading): "correlators whose converse domains include the domain and converse
domain respectively of `P`" is read as the existence of the descriptions `R'x`, `S'y` there. -/
theorem correlator_dpar {δ : Type*} {R : α → β → Prop} {S : δ → γ → Prop} {P : β → γ → Prop}
    (hR : ∀ x, x ∈ dom P → EDesc R x) (hS : ∀ y, y ∈ codom P → EDesc S y) :
    ∀ x y, P x y → Desc R x (fun a => Desc S y (fun b => Desc (R ∥ S˘) P (fun Q => Q a b))) := by
  intro x y hxy
  obtain ⟨a, ha⟩ := hR x ⟨y, hxy⟩
  obtain ⟨b, hb⟩ := hS y ⟨x, hxy⟩
  refine (TheIs_iff_of_unique ha).2 ((TheIs_iff_of_unique hb).2
    ((TheIs_iff_of_unique (fun Q => dpar_iff R S˘ Q P)).2 ?_))
  exact ⟨x, (ha a).2 rfl, y, hxy, (hb b).2 rfl⟩

end Intro

end PrincipiaMathematica
