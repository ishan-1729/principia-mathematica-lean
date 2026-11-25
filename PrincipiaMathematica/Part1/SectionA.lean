import PrincipiaMathematica.Defs.Part1

/-!
# Part I, Section A: The theory of deduction

Volume 1. Numbers: ✱1, ✱2, ✱3, ✱4, ✱5.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

/-!
## [✱1] Primitive ideas and propositions

*(Vol. 1, p. 95)*

> Since all definitions of terms are effected by means of other terms, every system of definitions which is not circular must start from a certain apparatus of undefined terms. It is to some extent optional what ideas we take as undefined in mathematics; the motives guiding our choice will be (1) to make the number of undefined ideas as small as possible, (2) as between two systems in which the number is equal, to choose the one which seems the simpler and easier. We know no way of proving that such and such a system of undefined ideas contains as few as will give such and such results [Note: The recognized methods of proving independence are not applicable, without reserve, to fundamentals. Cf. *Principles of Mathematics*, § 17. What is there said concerning primitive propositions applies with even greater force to primitive ideas.]. Hence we can only say that such and such ideas are undefined in such and such a system, not that they are indefinable. Following Peano, we shall call the undefined ideas and the undemonstrated propositions *primitive* ideas and *primitive* propositions respectively. The primitive ideas are *explained* by means of descriptions intended to point out to the reader what is meant; but the explanations do not constitute definitions, because they really involve the ideas they explain.
>
> …

**Lean reading.** The primitive ideas `∼p`, `p ∨ q` and the assertion-sign are Lean's `¬p`,
`p ∨ q` and "this is a theorem"; `p ⊃ q` is Lean's `p → q`, so the Df ✱1·01 becomes the classical
equivalence `(p → q) ↔ ¬p ∨ q`. PM's propositional variables (elementary propositions) are
arbitrary `p q r : Prop`, bound as implicit arguments (real variables). The primitive propositions
✱1·2–✱1·6 are theorems. ✱1·1 and ✱1·11 are rules of inference (modus ponens for propositions and
for asserted propositional functions), which PM itself says cannot be expressed in its symbolism:
they are recorded as the derivable rules. ✱1·7–✱1·72 say which expressions are elementary
propositions (and that `φ` and `ψ` must take arguments of the same type): in Lean these are typing
facts, recorded as the corresponding typed functions. The e-text misprints ✱1·4.

**Status.** complete. ✱1·01 proved (reading); ✱1·1, ✱1·11 proved (reading) (rules of inference);
✱1·4 proved (reading) (e-text misprint); ✱1·7, ✱1·71, ✱1·72 remark (elementarity, typing);
✱1·2, ✱1·3, ✱1·5, ✱1·6 proved.
-/

/-- ✱1·01 (Df). \(p\supset q.=.\sim {p} \lor q \qquad \text{Df}.\)

**Status.** proved (reading): `⊃` is read as Lean's primitive `→`, so PM's definition of
`p ⊃ q` becomes the classical equivalence of `p → q` with the definiens `∼p ∨ q`. -/
theorem pm1_01 {p q : Prop} : (p → q) ↔ ¬p ∨ q := imp_iff_not_or

/-- ✱1·1 (Pp). Anything implied by a true elementary proposition is true. Pp [Note: The letters "Pp" stand for "primitive proposition," as with Peano.].

**Status.** proved (reading): a rule of inference, which PM says cannot be expressed in its
symbolism (it asserts that `p` *is* true, not the hypothesis `p`). In Lean, inference is the
application of a proof of `p → q` to a proof of `p`; the declaration records this rule for
arbitrary propositions. -/
theorem pm1_1 {p q : Prop} (hp : p) (hpq : p → q) : q := hpq hp

/-- ✱1·11 (Pp). When \(\phi x\) can be asserted, where \(x\) is a real variable, and \(\phi x \supset \psi x\) can be asserted, where \(x\) is a real variable, then \(\psi x\) can be asserted, where \(x\) is a real variable. Pp.

**Status.** proved (reading): the rule of inference for asserted propositional functions. The
real variable `x` ranges over a type `α`, and asserting `φx` is proving `∀ x, φ x`; PM's
"axiom of identification of type" is Lean's typing (`φ` and `ψ` take arguments of the
same type `α`). -/
theorem pm1_11 {α : Type*} {φ ψ : α → Prop} (hφ : ∀ x, φ x) (hφψ : ∀ x, φ x → ψ x) :
    ∀ x, ψ x :=
  fun x => hφψ x (hφ x)

/-- ✱1·2 (Pp). \(\vdash \colon p \lor p.\supset.p \quad \text{Pp}.\) -/
theorem pm1_2 {p : Prop} : p ∨ p → p := fun h => h.elim id id

/-- ✱1·3 (Pp). \(\vdash \colon q.\supset .p \lor q \qquad \text{Pp}.\) -/
theorem pm1_3 {p q : Prop} : q → p ∨ q := Or.inr

/-- ✱1·4 (Pp). \(\vdash \colon p \lor q.\supset.p \lor p \qquad \text{Pp}.\)

**Status.** proved (reading): transcription error of the e-text, which prints `p ∨ p` as the
consequent; PM's ✱1·4 ("Perm") is `p ∨ q . ⊃ . q ∨ p`, as stated in the comment that
follows it, in the Introduction (Chapter I, primitive proposition (4)), and in its uses
(e.g. the proof of ✱9·36 cites ✱1·4 as `p ∨ φx . ⊃ . φx ∨ p`). -/
theorem pm1_4 {p q : Prop} : p ∨ q → q ∨ p := Or.symm

/-- ✱1·5 (Pp). \(\vdash \colon p \lor (q \lor r).\supset.q \lor (p\lor r) \qquad \text{Pp}\). -/
theorem pm1_5 {p q r : Prop} : p ∨ (q ∨ r) → q ∨ (p ∨ r) :=
  fun h => h.elim (fun hp => Or.inr (Or.inl hp)) (Or.imp_right Or.inr)

/-- ✱1·6 (Pp). \(\vdash \colon\ldotp q\supset r.\supset\colon p \lor q.\supset.p \lor r \qquad \text{Pp}\). -/
theorem pm1_6 {p q r : Prop} : (q → r) → (p ∨ q → p ∨ r) := fun h => Or.imp_right h

/-- ✱1·7 (Pp). If \(p\) is an elementary proposition, \(\sim{p}\) is an elementary proposition. Pp.

**Status.** remark: a statement about which expressions are elementary propositions
(meta-level). In Lean `Prop` is closed under negation by typing; the declaration records
the typing `Not : Prop → Prop`. -/
def pm1_7 : Prop → Prop := fun p => ¬p

/-- ✱1·71 (Pp). If \(p\) and \(q\) are elementary propositions, \(p \lor q\) is an elementary proposition. Pp.

**Status.** remark: meta-level, as ✱1·7; the declaration records the typing
`Or : Prop → Prop → Prop`. -/
def pm1_71 : Prop → Prop → Prop := fun p q => p ∨ q

/-- ✱1·72 (Pp). If \(\phi p\) and \(\psi p\) are elementary propositional functions which take elementary propositions as arguments, \(\phi p \lor \psi p\) is an elementary propositional function. Pp.

**Status.** remark: the "axiom of identification of real variables" (meta-level): `φp ∨ ψp`
is a function only when `φ` and `ψ` take arguments of the same type. In Lean this is
typing: the declaration forms `fun p => φ p ∨ ψ p` from `φ ψ : Prop → Prop` (✱9 extends it
to arguments of any type `α`, where it is again typing). -/
def pm1_72 (φ ψ : Prop → Prop) : Prop → Prop := fun p => φ p ∨ ψ p

/-!
## [✱2] Immediate consequences of the primitive propositions

*(Vol. 1, p. 102)*

> *Summary of* *2.
>
> …

**Lean reading.** Every proposition of ✱2 is a propositional tautology stated for arbitrary
`p q r s : Prop` (real variables, implicit arguments); PM's dots are read by Basic §2, so that
e.g. ✱2·25 `p : ∨ : p ∨ q . ⊃ . q` is `p ∨ (p ∨ q → q)` and ✱2·81 has three nested implications.
PM's undotted flat sums `p ∨ q ∨ r` (✱2·73, ✱2·74, ✱2·82) bracket to the left by the Df ✱2·33,
which becomes the defining equation of `Disj3`. The proofs use Lean's classical logic (`tauto`
or direct terms) rather than PM's derivations from ✱1·2–✱1·6. The enunciation erratum to ✱2·52
is already incorporated in the e-text.

**Status.** proved (all propositions; ✱2·33 definition).
-/

/-- ✱2·01. \(\vdash \colon p \supset \sim{p} . \supset . \sim{p}\) -/
theorem pm2_01 {p : Prop} : (p → ¬p) → ¬p := fun h hp => h hp hp

/-- ✱2·02. \(\vdash \colon q . \supset . p \supset q\) -/
theorem pm2_02 {p q : Prop} : q → (p → q) := fun hq _ => hq

/-- ✱2·03. \(\vdash \colon p \supset \sim{q} . \supset . q \supset \sim{p}\) -/
theorem pm2_03 {p q : Prop} : (p → ¬q) → (q → ¬p) := fun h hq hp => h hp hq

/-- ✱2·04. \(\vdash \colon\ldotp p . \supset . q \supset r \colon \supset \colon q . \supset . p \supset r\) -/
theorem pm2_04 {p q r : Prop} : (p → (q → r)) → (q → (p → r)) :=
  fun h hq hp => h hp hq

/-- ✱2·05. \(\vdash \colon\ldotp q \supset r . \supset \colon p \supset q . \supset . p \supset r\) -/
theorem pm2_05 {p q r : Prop} : (q → r) → ((p → q) → (p → r)) :=
  fun hqr hpq hp => hqr (hpq hp)

/-- ✱2·06. \(\vdash \colon\ldotp p \supset q . \supset \colon q \supset r . \supset . p \supset r\) -/
theorem pm2_06 {p q r : Prop} : (p → q) → ((q → r) → (p → r)) := fun hpq hqr hp => hqr (hpq hp)

/-- ✱2·07. \(\vdash:p\ldotp\supset \ldotp p\lor p \quad\left[\text{*1·3}\, \frac{p}{q}\right]\) -/
theorem pm2_07 {p : Prop} : p → p ∨ p := Or.inl

/-- ✱2·08. \(\vdash\ldotp p\supset p\) -/
theorem pm2_08 {p : Prop} : p → p := id

/-- ✱2·1. \(\vdash.\sim p\lor p \quad[\text{Id. (*1·01)}]\) -/
theorem pm2_1 {p : Prop} : ¬p ∨ p := (em p).symm

/-- ✱2·11. \(\vdash.p\lor \sim p\) -/
theorem pm2_11 {p : Prop} : p ∨ ¬p := em p

/-- ✱2·12. \(\vdash\ldotp p\supset \sim (\sim p)\) -/
theorem pm2_12 {p : Prop} : p → ¬(¬p) := fun hp hnp => hnp hp

/-- ✱2·13. \(\vdash.p \lor {\sim}\{{{\sim}({\sim}p)\}}\) -/
theorem pm2_13 {p : Prop} : p ∨ ¬(¬(¬p)) := by tauto

/-- ✱2·14. \(\vdash.{\sim}({\sim}p) \supset p\) -/
theorem pm2_14 {p : Prop} : ¬(¬p) → p := Classical.not_not.mp

/-- ✱2·15. \(\vdash \colon {\sim}p \supset q.\supset.{\sim}q \supset p\) -/
theorem pm2_15 {p q : Prop} : (¬p → q) → (¬q → p) := by tauto

/-- ✱2·16. \(\vdash\colon p\supset q.\supset .{\sim}q\supset {\sim}p\) -/
theorem pm2_16 {p q : Prop} : (p → q) → (¬q → ¬p) := fun h hnq hp => hnq (h hp)

/-- ✱2·17. \(\vdash\colon {\sim}q\supset{\sim}p.\supset.p\supset q\) -/
theorem pm2_17 {p q : Prop} : (¬q → ¬p) → (p → q) := by tauto

/-- ✱2·18. \(\vdash\colon{\sim}p\supset p.\supset.p\) -/
theorem pm2_18 {p : Prop} : (¬p → p) → p := by tauto

/-- ✱2·2. \(\vdash\colon p.\supset.p \lor q\) -/
theorem pm2_2 {p q : Prop} : p → p ∨ q := Or.inl

/-- ✱2·21. \(\vdash\colon{\sim}p.\supset.p\supset q \quad\left[\text{*2·2}\, \frac{{\sim}p}{p}\right]\) -/
theorem pm2_21 {p q : Prop} : ¬p → (p → q) := fun hnp hp => absurd hp hnp

/-- ✱2·24. \(\vdash\colon p.\supset.{\sim}p\supset q \quad[\text{*2·21.Comm}]\) -/
theorem pm2_24 {p q : Prop} : p → (¬p → q) := fun hp hnp => absurd hp hnp

/-- ✱2·25. \(\vdash \colon\ldotp p\colon \lor \colon p \lor q.\supset.q\) -/
theorem pm2_25 {p q : Prop} : p ∨ (p ∨ q → q) := by tauto

/-- ✱2·26. \(\vdash \colon\ldotp {\sim}p\colon \lor \colon p\supset q.\supset.q \quad\left[\text{*2·25}\, \frac{{\sim}p}{p}\right]\) -/
theorem pm2_26 {p q : Prop} : ¬p ∨ ((p → q) → q) := by tauto

/-- ✱2·27. \(\vdash \colon\ldotp p.\supset\colon p\supset q.\supset.q\, \quad[\text{*2·26}]\) -/
theorem pm2_27 {p q : Prop} : p → ((p → q) → q) := fun hp h => h hp

/-- ✱2·3. \(\vdash \colon p \lor (q \lor r).\supset.p \lor(r \lor q)\) -/
theorem pm2_3 {p q r : Prop} : p ∨ (q ∨ r) → p ∨ (r ∨ q) := by tauto

/-- ✱2·31. \(\vdash \colon p \lor (q \lor r).\supset.(p \lor q) \lor r\) -/
theorem pm2_31 {p q r : Prop} : p ∨ (q ∨ r) → (p ∨ q) ∨ r := by tauto

/-- ✱2·32. \(\vdash\colon (p\lor q) \lor r.\supset.p \lor (q \lor r)\) -/
theorem pm2_32 {p q r : Prop} : (p ∨ q) ∨ r → p ∨ (q ∨ r) := by tauto

/-- ✱2·33 (Df). \(p\lor q \lor r.=.(p \lor q) \lor r\, \quad\text{Df}\) -/
theorem pm2_33 {p q r : Prop} : Disj3 p q r ↔ (p ∨ q) ∨ r := Iff.rfl

/-- ✱2·36. \(\vdash\colon\ldotp q\supset r.\supset\colon p \lor q.\supset.r \lor p\) -/
theorem pm2_36 {p q r : Prop} : (q → r) → (p ∨ q → r ∨ p) := by tauto

/-- ✱2·37. \[\begin{align}\vdash\colon\ldotp q\supset r.\supset\colon q \lor p.&\supset.p \lor r\\ &[\text{Syll.Perm.Sum}]\end{align}\] -/
theorem pm2_37 {p q r : Prop} : (q → r) → (q ∨ p → p ∨ r) := by tauto

/-- ✱2·38. \[\begin{align}\vdash\colon\ldotp q\supset r.\supset\colon q \lor p.&\supset.r\lor p\\ &[\text{Syll.Perm.Sum}]\end{align}\] -/
theorem pm2_38 {p q r : Prop} : (q → r) → (q ∨ p → r ∨ p) := by tauto

/-- ✱2·4. \(\vdash\colon\ldotp p.\lor.p\lor q:\supset.p\lor q\) -/
theorem pm2_4 {p q : Prop} : p ∨ (p ∨ q) → p ∨ q := by tauto

/-- ✱2·41. \(\vdash\colon\ldotp q.\lor.p\lor q\colon\supset p\lor q\) -/
theorem pm2_41 {p q : Prop} : q ∨ (p ∨ q) → p ∨ q := by tauto

/-- ✱2·42. \(\vdash\colon\ldotp{\sim}p.\lor.p\supset q\colon \supset.p\supset q \quad\left[\text{*2·4}\, \tfrac{{\sim}p}{p}\right]\) -/
theorem pm2_42 {p q : Prop} : ¬p ∨ (p → q) → (p → q) := by tauto

/-- ✱2·43. \(\vdash\colon\ldotp p.\supset.p\supset q:\supset.p\supset q \quad [\text{*2·42}]\) -/
theorem pm2_43 {p q : Prop} : (p → (p → q)) → (p → q) := fun h hp => h hp hp

/-- ✱2·45. \(\vdash\colon{\sim}(p\lor q).\supset.{\sim}p \quad [\text{*2·2.Transp}]\) -/
theorem pm2_45 {p q : Prop} : ¬(p ∨ q) → ¬p := fun h hp => h (Or.inl hp)

/-- ✱2·46. \(\vdash\colon{\sim}(p \lor q).\supset.{\sim}q \quad [\text{*1·3.Transp}]\) -/
theorem pm2_46 {p q : Prop} : ¬(p ∨ q) → ¬q := fun h hq => h (Or.inr hq)

/-- ✱2·47. \(\vdash\colon{\sim}(p \lor q).\supset.{\sim}p \lor q \quad\left[\text{*2·45.*2·2}\, \frac{{\sim}p}{p}.\text{Syll}\right]\) -/
theorem pm2_47 {p q : Prop} : ¬(p ∨ q) → ¬p ∨ q := by tauto

/-- ✱2·48. \(\vdash\colon{\sim}(p\lor q).\supset.p \lor {\sim}q \quad\left[\text{*2·46.*1·3}\, \frac{{\sim}q}{q}.\text{Syll}\right]\) -/
theorem pm2_48 {p q : Prop} : ¬(p ∨ q) → p ∨ ¬q := by tauto

/-- ✱2·49. \(\vdash\colon{\sim}(p\lor q).\supset.{\sim}p \lor{\sim}q \quad\left[\text{*2·45.*2·2}\, \frac{{\sim}p,\,{\sim}q}{p,\,q}.\text{Syll}\right]\) -/
theorem pm2_49 {p q : Prop} : ¬(p ∨ q) → ¬p ∨ ¬q := by tauto

/-- ✱2·5. \(\vdash\colon{\sim}(p\supset q).\supset.{\sim}p\supset q \quad\left[\text{*2·47}\, \frac{{\sim}p}{p}\right]\) -/
theorem pm2_5 {p q : Prop} : ¬(p → q) → (¬p → q) := by tauto

/-- ✱2·51. \(\vdash\colon{\sim}(p\supset q).\supset.p\supset{\sim}q \quad\left[\text{*2·48}\, \frac{{\sim}p}{p}\right]\) -/
theorem pm2_51 {p q : Prop} : ¬(p → q) → (p → ¬q) := by tauto

/-- ✱2·52. \(\vdash\colon{\sim}(p\supset q).\supset.{\sim}p\supset{\sim}q \quad\left[\text{*2·49}\, \frac{{\sim}p}{p}\right]\)

The Additional Errata to Volume I (printed in Volume II) correct, on p. 112, the consequent
`p ⊃ ∼q` of the first printing to `∼p ⊃ ∼q`; the e-text already prints the corrected formula,
which is stated here. -/
theorem pm2_52 {p q : Prop} : ¬(p → q) → (¬p → ¬q) := by tauto

/-- ✱2·521. \(\vdash\colon{\sim}(p\supset q).\supset.q\supset p \quad[\text{*2·52·17}]\) -/
theorem pm2_521 {p q : Prop} : ¬(p → q) → (q → p) := by tauto

/-- ✱2·53. \(\vdash\colon p\lor q.\supset.{\sim}p\supset q\) -/
theorem pm2_53 {p q : Prop} : p ∨ q → (¬p → q) := by tauto

/-- ✱2·54. \(\vdash\colon{\sim}p\supset q.\supset.p\lor q \quad[\text{*2·14·38}]\) -/
theorem pm2_54 {p q : Prop} : (¬p → q) → p ∨ q := by tauto

/-- ✱2·55. \(\vdash\colon\ldotp{\sim}p.\supset.\colon p\lor q.\supset.q \quad[\text{*2·53.Comm}]\) -/
theorem pm2_55 {p q : Prop} : ¬p → (p ∨ q → q) := by tauto

/-- ✱2·56. \(\vdash\colon\ldotp{\sim}q.\supset\colon p\lor q.\supset.p \quad\left[\text{*2·55}\, \frac{q,\,p}{p,\,q}.\,\text{Perm}\right]\) -/
theorem pm2_56 {p q : Prop} : ¬q → (p ∨ q → p) := by tauto

/-- ✱2·6. \(\vdash\colon\ldotp{\sim}p\supset q.\supset\colon p\supset q.\supset.q\) -/
theorem pm2_6 {p q : Prop} : (¬p → q) → ((p → q) → q) := by tauto

/-- ✱2·61. \(\vdash\colon\ldotp p\supset q.\supset\colon{\sim}p\supset q.\supset.q \quad[\text{*2·6.Comm}]\) -/
theorem pm2_61 {p q : Prop} : (p → q) → ((¬p → q) → q) := by tauto

/-- ✱2·62. \(\vdash\colon\ldotp p \lor q.\supset\colon p\supset q.\supset.q \quad[\text{*2·53·6.Syll}]\) -/
theorem pm2_62 {p q : Prop} : p ∨ q → ((p → q) → q) := by tauto

/-- ✱2·621. \(\vdash\colon\ldotp p\supset q.\supset\colon p \lor q.\supset.q \quad[\text{*2·62.Comm}]\) -/
theorem pm2_621 {p q : Prop} : (p → q) → (p ∨ q → q) := by tauto

/-- ✱2·63. \(\vdash\colon\ldotp p \lor q.\supset\colon{\sim}p \lor q.\supset.q \quad[\text{*2·62}]\) -/
theorem pm2_63 {p q : Prop} : p ∨ q → (¬p ∨ q → q) := by tauto

/-- ✱2·64. \(\vdash\colon\ldotp p \lor q.\supset\colon p\lor{\sim}q.\supset.p \quad\left[\text{*2·63}\, \frac{q,\,p}{p,\,q}.\text{Perm}\right]\) -/
theorem pm2_64 {p q : Prop} : p ∨ q → (p ∨ ¬q → p) := by tauto

/-- ✱2·65. \(\vdash\colon\ldotp p\supset q.\supset\colon p\supset{\sim}q.\supset.{\sim}p \quad\left[\text{*2·64}\, \frac{{\sim}p}{p}\right]\) -/
theorem pm2_65 {p q : Prop} : (p → q) → ((p → ¬q) → ¬p) := fun h1 h2 hp => h2 hp (h1 hp)

/-- ✱2·67. \(\vdash\colon\ldotp p\lor q.\supset.q\colon\supset.p\supset q\) -/
theorem pm2_67 {p q : Prop} : (p ∨ q → q) → (p → q) := fun h hp => h (Or.inl hp)

/-- ✱2·68. \(\vdash\colon\ldotp p\supset q.\supset.q\colon\supset.p\lor q\) -/
theorem pm2_68 {p q : Prop} : ((p → q) → q) → p ∨ q := by tauto

/-- ✱2·69. \(\vdash\colon\ldotp p\supset q.\supset.q\colon\supset\colon q\supset p.\supset.p \quad\left[\text{*2·68.Perm.*2·62}\, \frac{q,\,p}{p,\,q}\right]\) -/
theorem pm2_69 {p q : Prop} : ((p → q) → q) → ((q → p) → p) := by tauto

/-- ✱2·73. \(\vdash\colon\ldotp p\supset q.\supset\colon p \lor q\lor r.\supset.q\lor r \quad[\text{*2·621·38}]\) -/
theorem pm2_73 {p q r : Prop} : (p → q) → ((p ∨ q) ∨ r → q ∨ r) := by tauto

/-- ✱2·74. \(\vdash\colon\ldotp q\supset p.\supset\colon p\lor q\lor r.\supset.p\lor r \quad\left[\text{*2·73}\, \frac{q,\,p}{p,\,q}.\text{Assoc.Syll}\right]\) -/
theorem pm2_74 {p q r : Prop} : (q → p) → ((p ∨ q) ∨ r → p ∨ r) := by tauto

/-- ✱2·75. \(\vdash\colon\colon p\lor q.\supset\colon\ldotp p.\lor.q\supset r\colon\supset.p\lor r \quad\left[\text{*2·74}\, \frac{{\sim}q}{q}.\text{*2·53·31}\right]\) -/
theorem pm2_75 {p q r : Prop} : p ∨ q → (p ∨ (q → r) → p ∨ r) := by tauto

/-- ✱2·76. \(\vdash\colon\ldotp p.\lor.q\supset r\colon\supset\colon p\lor q.\supset.p\lor r \quad[\text{*2·75.Comm}]\) -/
theorem pm2_76 {p q r : Prop} : p ∨ (q → r) → (p ∨ q → p ∨ r) := by tauto

/-- ✱2·77. \(\vdash\colon\ldotp p.\supset.q\supset r\colon\supset\colon p\supset q.\supset.p\supset r \quad\left[\text{*2·76}\, \frac{{\sim}p}{p}\right]\) -/
theorem pm2_77 {p q r : Prop} : (p → (q → r)) → ((p → q) → (p → r)) := fun h1 h2 hp => h1 hp (h2 hp)

/-- ✱2·8. \(\vdash\colon\ldotp q\lor r.\supset\colon{\sim}r\lor s.\supset.q\lor s\) -/
theorem pm2_8 {q r s : Prop} : q ∨ r → (¬r ∨ s → q ∨ s) := by tauto

/-- ✱2·81. \(\vdash\colon\colon q.\supset.r\supset s\colon\supset\colon\ldotp p\lor q.\supset\colon p\lor r.\supset.p\lor s\) -/
theorem pm2_81 {p q r s : Prop} : (q → (r → s)) → (p ∨ q → (p ∨ r → p ∨ s)) := by tauto

/-- ✱2·82. \[\begin{align}\vdash\colon\ldotp p\lor q\lor r.&\supset\colon p\lor {\sim}r\lor s.\supset.p\lor q\lor s\\ &\left[\text{*2·8.*2·81}\, \frac{q\lor r,{\sim}r\lor s,q \lor s}{q,\,r,\,s}\right]\end{align}\] -/
theorem pm2_82 {p q r s : Prop} : (p ∨ q) ∨ r → ((p ∨ ¬r) ∨ s → (p ∨ q) ∨ s) := by tauto

/-- ✱2·83. \[\begin{align}\vdash\colon\colon p.\supset.q\supset r\colon\supset\colon\ldotp p.\supset.r\supset s\colon&\supset\colon p.\supset.q\supset s\\ &\left[\text{*2·82}\, \frac{{\sim}p,{\sim}q}{p,q}\right]\end{align}\] -/
theorem pm2_83 {p q r s : Prop} : (p → (q → r)) → ((p → (r → s)) → (p → (q → s))) :=
  fun h1 h2 hp hq => h2 hp (h1 hp hq)

/-- ✱2·85. \(\vdash\colon\ldotp p\lor q.\supset.p\lor r\colon\supset\colon p.\lor.q\supset r\) -/
theorem pm2_85 {p q r : Prop} : (p ∨ q → p ∨ r) → p ∨ (q → r) := by tauto

/-- ✱2·86. \(\vdash\colon\ldotp p\supset q.\supset.p\supset r\colon\supset\colon p.\supset.q\supset r \quad\left[\text{*2·85}\, \frac{{\sim}p}{p}\right]\) -/
theorem pm2_86 {p q r : Prop} : ((p → q) → (p → r)) → (p → (q → r)) :=
  fun h hp hq => h (fun _ => hq) hp

/-!
## [✱3] The logical product of two propositions

*(Vol. 1, p. 114)*

> *Summary of* *3.
>
> The logical product of two propositions \(p\) and \(q\) is practically the proposition "\(p\) and \(q\) are both true." But this as it stands would have to be a new primitive idea. We therefore take as the logical product the proposition \({\sim}({\sim}p\lor {\sim}q)\), *i.e.* "it is false that either \(p\) is false or \(q\) is false," which is obviously true when and only when \(p\) and \(q\) are both true. Thus we put
>
> *3·01. \(p.q .=. {\sim}({\sim}p \lor {\sim}q) \quad \text{Df}\)
>
> where "\(p . q\)" is the logical product of \(p\) and \(q\).
>
> *3·02. \(p \supset q \supset r.=. p \supset q . q \supset r \quad \text{Df}\)
>
> This definition serves merely to abbreviate proofs.
>
> When we are given two asserted propositional functions "\(\vdash \ldotp{\phi}x\)" and "\(\vdash \ldotp {\psi}x\)," we shall have "\(\vdash\ldotp {\phi}x \ldotp {\psi}x\)" whenever \(\phi\) and \(\psi\) take arguments of the same type. This will be proved for any functions in *9; for the present, we are confined to *elementary* propositional functions of elementary propositions. In this case, the result is proved as follows:
>
> …

**Lean reading.** The logical product `p . q` is Lean's `p ∧ q`, so the Df ✱3·01 becomes the
classical equivalence `p ∧ q ↔ ¬(¬p ∨ ¬q)`; the chain Df ✱3·02 (`p ⊃ q ⊃ r` is the
*conjunction* of the links) is the defining equation of `ImpChain`. A product of propositions
as antecedent (`p . q . ⊃ . r`, ✱3·33, ✱3·43, ✱3·47) stays a conjunction and is not curried;
✱3·12 `∼p . ∨ . ∼q . ∨ . p . q` is `(¬p ∨ ¬q) ∨ (p ∧ q)` (✱2·11 with `∼p ∨ ∼q` for `p`, as in
PM's proof). ✱3·03 is a rule of inference for asserted functions and is recorded as the
derivable rule, as ✱1·11 is.

**Status.** proved (all propositions; ✱3·01 proved (reading), ✱3·03 proved (reading), ✱3·02
definition; see their docstrings).
-/

/-- ✱3·01 (Df). \(p . q . = {\sim} ({\sim} p \lor {\sim} q) \quad \text{Df}\)

**Status.** proved (reading): the logical product `p . q` is read as Lean's primitive `p ∧ q`,
so PM's definition becomes the classical equivalence of `p ∧ q` with the definiens
`∼(∼p ∨ ∼q)`. -/
theorem pm3_01 {p q : Prop} : p ∧ q ↔ ¬(¬p ∨ ¬q) := by tauto

/-- ✱3·02 (Df). \(p\supset q\supset r.=.p\supset q.q \supset r \quad \text{Df}\) -/
theorem pm3_02 {p q r : Prop} : ImpChain p q r ↔ (p → q) ∧ (q → r) := Iff.rfl

/-- ✱3·03. Given two asserted elementary propositional functions "\(\vdash.\phi p\)" and "\(\vdash.\psi p\)" whose arguments are elementary propositions, we have \(\vdash.\phi p.\psi p\).

**Status.** proved (reading): a rule of inference on asserted propositional functions
(meta-level, like ✱1·11), which PM proves from ✱1·7·72, ✱2·11, ✱2·32 and ✱1·11. Asserting `φp` with `p` a real variable is proving `∀ p, φ p`; the
rule becomes: from proofs of `∀ p, φ p` and `∀ p, ψ p` (`φ ψ : Prop → Prop`, functions of
elementary propositions, Basic §1) follows `∀ p, φ p ∧ ψ p`. -/
theorem pm3_03 {φ ψ : Prop → Prop} (hφ : ∀ p, φ p) (hψ : ∀ p, ψ p) :
    ∀ p, φ p ∧ ψ p :=
  fun p => ⟨hφ p, hψ p⟩

/-- ✱3·1. \(\vdash : p . q . \supset . {\sim} ({\sim} p \lor {\sim} q) \quad [\text{Id. (*3·01)}]\) -/
theorem pm3_1 {p q : Prop} : p ∧ q → ¬(¬p ∨ ¬q) := by tauto

/-- ✱3·11. \(\vdash : {\sim} ({\sim} p \lor {\sim} q) . \supset . p . q \quad [\text{Id.} (*3·01)]\) -/
theorem pm3_11 {p q : Prop} : ¬(¬p ∨ ¬q) → p ∧ q := by tauto

/-- ✱3·12. \(\vdash : {\sim} p . \lor . {\sim} q . \lor . p . q \quad \left[\text{*2·11} \frac{{\sim} p \lor {\sim} q}{p}\right]\) -/
theorem pm3_12 {p q : Prop} : (¬p ∨ ¬q) ∨ (p ∧ q) := by tauto

/-- ✱3·13. \(\vdash : {\sim} (p . q) . \supset . {\sim} p \lor {\sim} q \quad [\text{*3·11.Transp}]\) -/
theorem pm3_13 {p q : Prop} : ¬(p ∧ q) → ¬p ∨ ¬q := by tauto

/-- ✱3·14. \(\vdash : {\sim} p \lor {\sim} q . \supset . {\sim} (p . q) \quad [\text{*3·1.Transp}]\) -/
theorem pm3_14 {p q : Prop} : ¬p ∨ ¬q → ¬(p ∧ q) := by tauto

/-- ✱3·2. \(\vdash\colon\ldotp p . \supset : q . \supset . p . q \quad [\text{*3·12}] \) -/
theorem pm3_2 {p q : Prop} : p → (q → p ∧ q) := fun hp hq => ⟨hp, hq⟩

/-- ✱3·21. \(\vdash\colon\ldotp q . \supset : p . \supset . p . q \quad [\text{*3·2.Comm}]\) -/
theorem pm3_21 {p q : Prop} : q → (p → p ∧ q) := fun hq hp => ⟨hp, hq⟩

/-- ✱3·22. \(\vdash : p . q . \supset . q . p\) -/
theorem pm3_22 {p q : Prop} : p ∧ q → q ∧ p := And.symm

/-- ✱3·24. \(\vdash\ldotp\sim (p\ldotp\sim p)\) -/
theorem pm3_24 {p : Prop} : ¬(p ∧ ¬p) := fun h => h.2 h.1

/-- ✱3·26. \(\vdash\colon p\ldotp q\ldotp\supset\ldotp p\) -/
theorem pm3_26 {p q : Prop} : p ∧ q → p := And.left

/-- ✱3·27. \(\vdash\colon p\ldotp q\ldotp\supset\ldotp q\) -/
theorem pm3_27 {p q : Prop} : p ∧ q → q := And.right

/-- ✱3·3. \(\vdash\colon\ldotp p\ldotp q\ldotp \supset \ldotp r\colon \supset \colon p\ldotp \supset \ldotp q \supset r\) -/
theorem pm3_3 {p q r : Prop} : (p ∧ q → r) → (p → (q → r)) := fun h hp hq => h ⟨hp, hq⟩

/-- ✱3·31. \(\vdash\colon\ldotp p\ldotp \supset \ldotp q \supset r\colon \supset \colon p\ldotp q\ldotp \supset\ldotp r\) -/
theorem pm3_31 {p q r : Prop} : (p → (q → r)) → (p ∧ q → r) := fun h hpq => h hpq.1 hpq.2

/-- ✱3·33. \(\vdash :p\supset q .q\supset r. \supset .p\supset r \quad[\text{Syll. Imp}]\) -/
theorem pm3_33 {p q r : Prop} : (p → q) ∧ (q → r) → (p → r) := fun h hp => h.2 (h.1 hp)

/-- ✱3·34. \(\vdash:q\supset r.p\supset q.\supset.p\supset r \quad[\text{Syll. Imp}]\) -/
theorem pm3_34 {p q r : Prop} : (q → r) ∧ (p → q) → (p → r) := fun h hp => h.1 (h.2 hp)

/-- ✱3·35. \(\vdash : p. p \supset q . \supset . q \quad[\text{*2·27. Imp}]\) -/
theorem pm3_35 {p q : Prop} : p ∧ (p → q) → q := fun h => h.2 h.1

/-- ✱3·37. \(\vdash \colon\ldotp p . q . \supset . r :\supset: p. {\sim} r. \supset . {\sim} q\) -/
theorem pm3_37 {p q r : Prop} : (p ∧ q → r) → (p ∧ ¬r → ¬q) := fun h hpr hq => hpr.2 (h ⟨hpr.1, hq⟩)

/-- ✱3·4. \(\vdash:p.q.\supset.p\supset q \quad[\text{*2·51.Transp.(*1·01. *3·01)}]\) -/
theorem pm3_4 {p q : Prop} : p ∧ q → (p → q) := fun h _ => h.2

/-- ✱3·41. \(\vdash \colon\ldotp p \supset r . \supset : p . q . \supset . r \quad[\text{*3·26.Syll}]\) -/
theorem pm3_41 {p q r : Prop} : (p → r) → (p ∧ q → r) := fun h hpq => h hpq.1

/-- ✱3·42. \(\vdash \colon\ldotp q \supset r . \supset : p . q . \supset . r \quad[\text{*3·27.Syll}]\) -/
theorem pm3_42 {p q r : Prop} : (q → r) → (p ∧ q → r) := fun h hpq => h hpq.2

/-- ✱3·43. \(\vdash\colon\ldotp p\supset q.p\supset r. \supset : p . \supset . q . r\) -/
theorem pm3_43 {p q r : Prop} : (p → q) ∧ (p → r) → (p → q ∧ r) := fun h hp => ⟨h.1 hp, h.2 hp⟩

/-- ✱3·44. \(\vdash \colon\ldotp q \supset p . r \supset p . \supset : q \lor r . \supset . p\) -/
theorem pm3_44 {p q r : Prop} : (q → p) ∧ (r → p) → (q ∨ r → p) := fun h hqr => hqr.elim h.1 h.2

/-- ✱3·45. \(\vdash\colon\ldotp p\supset q.\supset :p.r.\supset .q.r\) -/
theorem pm3_45 {p q r : Prop} : (p → q) → (p ∧ r → q ∧ r) := fun h hpr => ⟨h hpr.1, hpr.2⟩

/-- ✱3·47. \(\vdash\colon\ldotp p\supset r.q\supset s.\supset :p.q.\supset .r.s\) -/
theorem pm3_47 {p q r s : Prop} : (p → r) ∧ (q → s) → (p ∧ q → r ∧ s) :=
  fun h hpq => ⟨h.1 hpq.1, h.2 hpq.2⟩

/-- ✱3·48. \(\vdash\colon\ldotp p\supset r.q\supset s.\supset :p\lor q.\supset .r\lor s\) -/
theorem pm3_48 {p q r s : Prop} : (p → r) ∧ (q → s) → (p ∨ q → r ∨ s) :=
  fun h hpq => hpq.imp h.1 h.2

/-!
## [✱4] Equivalence and formal rules

*(Vol. 1, p. 120)*

> *Summary of* *4.
>
> …

**Lean reading.** Equivalence `p ≡ q` is Lean's `p ↔ q`, so the Df ✱4·01 becomes
`(p ↔ q) ↔ (p → q) ∧ (q → p)`; the Dfs ✱4·02 (chains of equivalences are conjunctions of their
links) and ✱4·34 (`p . q . r` is `(p . q) . r`) are the defining equations of `EqvChain` and
`Conj3`. Accordingly ✱4·87, a chain of four propositions joined by `:≡:`, is the left-nested
conjunction of its three links `((A ↔ B) ∧ (B ↔ C)) ∧ (C ↔ D)`. Undotted `∨` binds tighter than
a product dot (✱4·4 `p . q ∨ r` is `p ∧ (q ∨ r)`). All propositions are tautologies in
`p q r s : Prop`, proved classically.

**Status.** proved (all propositions; ✱4·01 proved (reading), ✱4·02 and ✱4·34 definition; see
their docstrings).
-/

/-- ✱4·01 (Df). \(p\equiv q.=.p\supset q.q\supset p\quad \text{Df}\)

**Status.** proved (reading): equivalence `p ≡ q` is read as Lean's primitive `p ↔ q`, so PM's
definition becomes the equivalence of `p ↔ q` with the definiens `(p → q) ∧ (q → p)`. -/
theorem pm4_01 {p q : Prop} : (p ↔ q) ↔ (p → q) ∧ (q → p) := iff_def

/-- ✱4·02 (Df). \(p\equiv q\equiv r.=.p\equiv q.q\equiv r \quad\text{Df}\) -/
theorem pm4_02 {p q r : Prop} : EqvChain p q r ↔ (p ↔ q) ∧ (q ↔ r) := Iff.rfl

/-- ✱4·1. \(\vdash:p\supset q.\equiv.{\sim} q\supset{\sim} p \quad[\text{*2·16·17}]\) -/
theorem pm4_1 {p q : Prop} : (p → q) ↔ (¬q → ¬p) := by tauto

/-- ✱4·11. \(\vdash:p\equiv q.\equiv.{\sim} p\equiv{\sim} q \quad[\text{*2·16·17.*3·47·22}]\) -/
theorem pm4_11 {p q : Prop} : (p ↔ q) ↔ (¬p ↔ ¬q) := by tauto

/-- ✱4·12. \(\vdash:p\equiv{\sim} q.\equiv.q\equiv{\sim} p \quad[\text{*2·03·15}]\) -/
theorem pm4_12 {p q : Prop} : (p ↔ ¬q) ↔ (q ↔ ¬p) := by tauto

/-- ✱4·13. \(\vdash.p\equiv{\sim}({\sim} p) \quad\text{[*2·12·14}]\) -/
theorem pm4_13 {p : Prop} : p ↔ ¬(¬p) := by tauto

/-- ✱4·14. \(\vdash\colon\ldotp p.q.\supset.r:\equiv:p.{\sim} r.\supset.{\sim} q \quad[\text{*3·37.*4·13}]\) -/
theorem pm4_14 {p q r : Prop} : (p ∧ q → r) ↔ (p ∧ ¬r → ¬q) := by tauto

/-- ✱4·15. \(\vdash\colon\ldotp p.q.\supset.{\sim} r:\equiv:q.r.\supset.{\sim} p \quad[\text{*3·22.*4·13·14}]\) -/
theorem pm4_15 {p q r : Prop} : (p ∧ q → ¬r) ↔ (q ∧ r → ¬p) := by tauto

/-- ✱4·2. \(\vdash.p\equiv p \quad[\text{Id.*3·2}]\) -/
theorem pm4_2 {p : Prop} : p ↔ p := Iff.rfl

/-- ✱4·21. \(\vdash:p\equiv q.\equiv.q\equiv p \quad[\text{*3·22}]\) -/
theorem pm4_21 {p q : Prop} : (p ↔ q) ↔ (q ↔ p) := Iff.comm

/-- ✱4·22. \(\vdash:p\equiv q.q\equiv r.\supset.p\equiv r\) -/
theorem pm4_22 {p q r : Prop} : (p ↔ q) ∧ (q ↔ r) → (p ↔ r) := fun h => h.1.trans h.2

/-- ✱4·24. \(\vdash:p.\equiv.p.p\) -/
theorem pm4_24 {p : Prop} : p ↔ p ∧ p := by tauto

/-- ✱4·25. \(\vdash:p.\equiv.p\lor p \quad\left[\text{Taut.Add}\,\frac{p}{q}\right]\) -/
theorem pm4_25 {p : Prop} : p ↔ p ∨ p := by tauto

/-- ✱4·3. \(\vdash:p.q.\equiv.q.p \quad[\text{*3·22}]\) -/
theorem pm4_3 {p q : Prop} : p ∧ q ↔ q ∧ p := And.comm

/-- ✱4·31. \(\vdash:p\lor q.\equiv.q\lor p \quad[\text{Perm}]\) -/
theorem pm4_31 {p q : Prop} : p ∨ q ↔ q ∨ p := Or.comm

/-- ✱4·32. \(\vdash:(p.q).r.\equiv.p.(q.r)\) -/
theorem pm4_32 {p q r : Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := and_assoc

/-- ✱4·33. \(\vdash:(p\lor q)\lor r.\equiv.p\lor (q\lor r) \quad[\text{*2·31·32}]\) -/
theorem pm4_33 {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := or_assoc

/-- ✱4·34 (Df). \(p.q.r.=.(p.q).r \quad\text{Df}\) -/
theorem pm4_34 {p q r : Prop} : Conj3 p q r ↔ (p ∧ q) ∧ r := Iff.rfl

/-- ✱4·36. \(\vdash\colon\ldotp p\equiv q.\supset:p.r.\equiv .q.r \quad[\text{Fact. *3·47}]\) -/
theorem pm4_36 {p q r : Prop} : (p ↔ q) → (p ∧ r ↔ q ∧ r) := by tauto

/-- ✱4·37. \(\vdash\colon\ldotp p\equiv q.\supset:p\lor r.\equiv .q\lor r \quad[\text{Sum. *3·47}]\) -/
theorem pm4_37 {p q r : Prop} : (p ↔ q) → (p ∨ r ↔ q ∨ r) := by tauto

/-- ✱4·38. \(\vdash\colon\ldotp p\equiv r.q\equiv s.\supset:p.q.\equiv .r.s \quad[\text{*3·47. *4·32. *3·22}]\) -/
theorem pm4_38 {p q r s : Prop} : (p ↔ r) ∧ (q ↔ s) → (p ∧ q ↔ r ∧ s) := by tauto

/-- ✱4·39. \(\vdash\colon\ldotp p\equiv r.q\equiv s.\supset:p\lor q.\equiv .r\lor s \quad[\text{*3·48·47. *4·32. *3·22}]\) -/
theorem pm4_39 {p q r s : Prop} : (p ↔ r) ∧ (q ↔ s) → (p ∨ q ↔ r ∨ s) := by tauto

/-- ✱4·4. \(\vdash\colon\ldotp p.q\lor r.\equiv :p.q.\lor .p.r\) -/
theorem pm4_4 {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by tauto

/-- ✱4·41. \(\vdash\colon\ldotp p.\lor .q.r:\equiv .p\lor q.p\lor r\) -/
theorem pm4_41 {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by tauto

/-- ✱4·42. \(\vdash\colon\ldotp p.\equiv :p.q.\lor .p.{\sim}q\) -/
theorem pm4_42 {p q : Prop} : p ↔ (p ∧ q) ∨ (p ∧ ¬q) := by tauto

/-- ✱4·43. \(\vdash\colon\ldotp p.\equiv :p\lor q.p\lor {\sim}q\) -/
theorem pm4_43 {p q : Prop} : p ↔ (p ∨ q) ∧ (p ∨ ¬q) := by tauto

/-- ✱4·44. \(\vdash\colon\ldotp p.\equiv :p.\lor.p.q\) -/
theorem pm4_44 {p q : Prop} : p ↔ p ∨ (p ∧ q) := by tauto

/-- ✱4·45. \(\vdash:p.\equiv .p.p\lor q \quad[\text{*3·26.*2·2}]\) -/
theorem pm4_45 {p q : Prop} : p ↔ p ∧ (p ∨ q) := by tauto

/-- ✱4·5. \(\vdash: p.q.\equiv .{\sim}({\sim}p\lor{\sim}q) \quad[\text{*4·2. (*3·01)}]\) -/
theorem pm4_5 {p q : Prop} : p ∧ q ↔ ¬(¬p ∨ ¬q) := by tauto

/-- ✱4·51. \(\vdash: {\sim}(p.q).\equiv .{\sim}p\lor{\sim}q \quad[\text{*4·5·12}]\) -/
theorem pm4_51 {p q : Prop} : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by tauto

/-- ✱4·52. \(\vdash: p.{\sim}q.\equiv .{\sim}({\sim}p\lor q) \quad\left[\text{*4·5}\, \frac{{\sim}q}{q}.\text{*4·13}\right]\) -/
theorem pm4_52 {p q : Prop} : p ∧ ¬q ↔ ¬(¬p ∨ q) := by tauto

/-- ✱4·53. \(\vdash: {\sim}(p.{\sim}q).\equiv .{\sim}p\lor q \quad[\text{*4·52·12}]\) -/
theorem pm4_53 {p q : Prop} : ¬(p ∧ ¬q) ↔ ¬p ∨ q := by tauto

/-- ✱4·54. \(\vdash: {\sim}p.q.\equiv .{\sim}(p\lor{\sim}q) \quad\left[\text{*4·5}\, \frac{{\sim}p}{p}.\text{*4·13}\right]\) -/
theorem pm4_54 {p q : Prop} : ¬p ∧ q ↔ ¬(p ∨ ¬q) := by tauto

/-- ✱4·55. \(\vdash: {\sim}({\sim}p.q).\equiv .p\lor{\sim}q \quad[\text{*4·54·12}]\) -/
theorem pm4_55 {p q : Prop} : ¬(¬p ∧ q) ↔ p ∨ ¬q := by tauto

/-- ✱4·56. \(\vdash: {\sim}p.{\sim}q.\equiv .{\sim}(p\lor q) \quad\left[\text{*4·54} \frac{{\sim}q}{q}.\text{*4·13}\right]\) -/
theorem pm4_56 {p q : Prop} : ¬p ∧ ¬q ↔ ¬(p ∨ q) := by tauto

/-- ✱4·57. \(\vdash: {\sim}({\sim}p.{\sim}q).\equiv .p\lor q \quad[\text{*4·56·12}]\) -/
theorem pm4_57 {p q : Prop} : ¬(¬p ∧ ¬q) ↔ p ∨ q := by tauto

/-- ✱4·6. \(\vdash: p\supset q.\equiv.{\sim}p\lor q \quad[\text{*4·2.(*1·01)}]\) -/
theorem pm4_6 {p q : Prop} : (p → q) ↔ ¬p ∨ q := by tauto

/-- ✱4·61. \(\vdash: {\sim}(p\supset q).\equiv.p.{\sim}q \quad[\text{*4·6·11·52}]\) -/
theorem pm4_61 {p q : Prop} : ¬(p → q) ↔ p ∧ ¬q := by tauto

/-- ✱4·62. \(\vdash: p\supset {\sim}q.\equiv.{\sim}p\lor {\sim}q \quad\left[\text{*4·6}\, \frac{{\sim}q}{q}\right]\) -/
theorem pm4_62 {p q : Prop} : (p → ¬q) ↔ ¬p ∨ ¬q := by tauto

/-- ✱4·63. \(\vdash: {\sim}(p\supset {\sim}q).\equiv.p.q \quad[\text{*4·62·11·5}]\) -/
theorem pm4_63 {p q : Prop} : ¬(p → ¬q) ↔ p ∧ q := by tauto

/-- ✱4·64. \(\vdash: {\sim}p\supset q.\equiv.p\lor q \quad[\text{*2·53·54}]\) -/
theorem pm4_64 {p q : Prop} : (¬p → q) ↔ p ∨ q := by tauto

/-- ✱4·65. \(\vdash: {\sim}({\sim}p\supset q).\equiv.{\sim}p.{\sim}q \quad[\text{*4·64·11·56}]\) -/
theorem pm4_65 {p q : Prop} : ¬(¬p → q) ↔ ¬p ∧ ¬q := by tauto

/-- ✱4·66. \(\vdash: {\sim}p\supset {\sim}q.\equiv.p\lor {\sim}q \quad\left[\text{*4·64}\, \frac{{\sim}q}{q}\right]\) -/
theorem pm4_66 {p q : Prop} : (¬p → ¬q) ↔ p ∨ ¬q := by tauto

/-- ✱4·67. \(\vdash:{\sim}({\sim}p\supset {\sim}q).\equiv.{\sim}p.q \quad[\text{*4·66·11·54}]\) -/
theorem pm4_67 {p q : Prop} : ¬(¬p → ¬q) ↔ ¬p ∧ q := by tauto

/-- ✱4·7. \(\vdash\colon\ldotp p\supset q.\equiv:p.\supset .p.q\) -/
theorem pm4_7 {p q : Prop} : (p → q) ↔ (p → p ∧ q) := by tauto

/-- ✱4·71. \(\vdash\colon\ldotp p\supset q.\equiv:p.\equiv.p.q\) -/
theorem pm4_71 {p q : Prop} : (p → q) ↔ (p ↔ p ∧ q) := by tauto

/-- ✱4·72. \(\vdash\colon\ldotp p\supset q.\equiv:q.\equiv.p\lor q\) -/
theorem pm4_72 {p q : Prop} : (p → q) ↔ (q ↔ p ∨ q) := by tauto

/-- ✱4·73. \(\vdash\colon\ldotp q.\supset :p.\equiv.p.q \quad[\text{Simp.*4·71}]\) -/
theorem pm4_73 {p q : Prop} : q → (p ↔ p ∧ q) := by tauto

/-- ✱4·74. \(\vdash\colon\ldotp {\sim}p.\supset :q.\equiv.p\lor q \quad[\text{*2·21.*4·72}]\) -/
theorem pm4_74 {p q : Prop} : ¬p → (q ↔ p ∨ q) := by tauto

/-- ✱4·76. \(\vdash\colon\ldotp p\supset q.p\supset r.\equiv:p.\supset .q.r \quad\left[\text{*4·41}\, \frac{{\sim}p}{p}.\text{(*1·01)}\right]\) -/
theorem pm4_76 {p q r : Prop} : (p → q) ∧ (p → r) ↔ (p → q ∧ r) := by tauto

/-- ✱4·77. \(\vdash\colon\ldotp q\supset p.r\supset p.\equiv:q\lor r.\supset .p \quad[\text{*3·44. Add. *2·2}]\) -/
theorem pm4_77 {p q r : Prop} : (q → p) ∧ (r → p) ↔ (q ∨ r → p) := by tauto

/-- ✱4·78. \(\vdash\colon\ldotp p\supset q.\lor .p\supset r:\equiv:p.\supset .q\lor r\) -/
theorem pm4_78 {p q r : Prop} : (p → q) ∨ (p → r) ↔ (p → q ∨ r) := by tauto

/-- ✱4·79. \(\vdash\colon\ldotp q\supset p.\lor .r\supset p:\equiv:q.r.\supset .p\) -/
theorem pm4_79 {p q r : Prop} : (q → p) ∨ (r → p) ↔ (q ∧ r → p) := by tauto

/-- ✱4·8. \(\vdash:p\supset {\sim}p.\equiv.{\sim}p \quad[\text{*2·01. Simp}]\) -/
theorem pm4_8 {p : Prop} : (p → ¬p) ↔ ¬p := by tauto

/-- ✱4·81. \(\vdash:{\sim}p\supset p.\equiv.p \quad[\text{*2·18. Simp}]\) -/
theorem pm4_81 {p : Prop} : (¬p → p) ↔ p := by tauto

/-- ✱4·82. \(\vdash:p\supset q.p\supset {\sim}q.\equiv.{\sim}p \quad[\text{*2·65. Imp.*2·21. Comp}]\) -/
theorem pm4_82 {p q : Prop} : (p → q) ∧ (p → ¬q) ↔ ¬p := by tauto

/-- ✱4·83. \(\vdash:p\supset q.{\sim}p\supset q.\equiv.q \quad[\text{*2·61.Imp. Simp. Comp}]\) -/
theorem pm4_83 {p q : Prop} : (p → q) ∧ (¬p → q) ↔ q := by tauto

/-- ✱4·84. \(\vdash\colon\ldotp p\equiv q.\supset :p\supset r.\equiv.q\supset r \quad[\text{*2·06.*3·47}]\) -/
theorem pm4_84 {p q r : Prop} : (p ↔ q) → ((p → r) ↔ (q → r)) := by tauto

/-- ✱4·85. \(\vdash\colon\ldotp p\equiv q.\supset :r\supset p.\equiv.r\supset q \quad[\text{*2·05.*3·47}]\) -/
theorem pm4_85 {p q r : Prop} : (p ↔ q) → ((r → p) ↔ (r → q)) := by tauto

/-- ✱4·86. \(\vdash\colon\ldotp p\equiv q.\supset :p\equiv r.\equiv.q\equiv r \quad[\text{*4·21·22}]\) -/
theorem pm4_86 {p q r : Prop} : (p ↔ q) → ((p ↔ r) ↔ (q ↔ r)) := by tauto

/-- ✱4·87. \[\begin{align}\vdash\colon\ldotp p.q.\supset .r:\equiv:p.\supset .q\supset &r:\equiv:q.\supset .p\supset r:\equiv:q.p.\supset .r\\ &\quad[\text{Exp. Comm. Imp}]\end{align}\] -/
theorem pm4_87 {p q r : Prop} :
    (((p ∧ q → r) ↔ (p → (q → r))) ∧ ((p → (q → r)) ↔ (q → (p → r)))) ∧
      ((q → (p → r)) ↔ (q ∧ p → r)) :=
  by tauto

/-!
## [✱5] Miscellaneous propositions

*(Vol. 1, p. 128)*

> *Summary of* *5.
>
> The present number consists chiefly of propositions of two sorts: (1) those which will be required as lemmas in one or more subsequent proofs, (2) those which are on their own account illustrative, or would be important in other developments than those that we wish to make. A few of the propositions of this number, however, will be used very frequently. These are:
>
> *5·1. \(\vdash : p . q .\supset. p \equiv q\)
>
> *I.e.* two propositions are equivalent if they are both true. (The statement that two propositions are equivalent if they are both false is *5·21.)
>
> *5·32. \(\vdash \colon\ldotp p .\supset. q \equiv r :\equiv: p . q .\equiv. p.r\)
>
> *I.e.* to say that, on the hypothesis \(p\), \(q\) and \(r\) are equivalent, is equivalent to saying that the joint assertion of \(p\) and \(q\) is equivalent to the joint assertion of \(p\) and \(r\). This is a very useful rule in inference.
>
> *5·6. \(\vdash \colon\ldotp p . {\sim}q .\supset. r :\equiv: p.\supset.q \lor r\)
>
> *I.e.* "\(p\) and not-\(q\) imply \(r\)" is equivalent to "\(p\) implies \(q\) or \(r\)."
>
> …

**Lean reading.** All propositions of ✱5 are propositional tautologies in `p q r s : Prop`,
proved classically. The dots are read by Basic §2: e.g. ✱5·33 `p . q ⊃ r . ≡ : p : p . q . ⊃ . r`
is `p ∧ (q → r) ↔ p ∧ (p ∧ q → r)`, ✱5·44 is `(p → q) → ((p → r) ↔ (p → q ∧ r))`, and ✱5·75
`r ⊃ ∼q : p . ≡ . q ∨ r : ⊃ : p . ∼q . ≡ . r` has the product antecedent
`(r → ¬q) ∧ (p ↔ q ∨ r)`. The flat sum of ✱5·53 brackets to the left (✱2·33) and its flat
product to the left (✱4·34). The errata to ✱5·11 and ✱5·12 concern only the references of
their proofs.

**Status.** proved (all propositions).
-/

/-- ✱5·1. \(\vdash:p.q.\supset .p\equiv q \quad[\text{*3·4·22}]\) -/
theorem pm5_1 {p q : Prop} : p ∧ q → (p ↔ q) := by tauto

/-- ✱5·11. \(\vdash:p\supset q.\lor .{\sim}p\supset q \quad[\text{*2·5·54}]\) -/
theorem pm5_11 {p q : Prop} : (p → q) ∨ (¬p → q) := by tauto

/-- ✱5·12. \(\vdash:p\supset q.\lor .p\supset {\sim}q \quad[\text{*2·51·54}]\) -/
theorem pm5_12 {p q : Prop} : (p → q) ∨ (p → ¬q) := by tauto

/-- ✱5·13. \(\vdash:p\supset q.\lor .q\supset p \quad[\text{*2·521}]\) -/
theorem pm5_13 {p q : Prop} : (p → q) ∨ (q → p) := by tauto

/-- ✱5·14. \(\vdash:p\supset q.\lor .q\supset r \quad[\text{Simp. Transp.*2·21}]\) -/
theorem pm5_14 {p q r : Prop} : (p → q) ∨ (q → r) := by tauto

/-- ✱5·15. \(\vdash:p\equiv q.\lor .p\equiv {\sim}q\) -/
theorem pm5_15 {p q : Prop} : (p ↔ q) ∨ (p ↔ ¬q) := by tauto

/-- ✱5·16. \(\vdash.{\sim}(p\equiv q.p\equiv {\sim}q)\) -/
theorem pm5_16 {p q : Prop} : ¬((p ↔ q) ∧ (p ↔ ¬q)) := by tauto

/-- ✱5·17. \(\vdash:p\lor q.{\sim}(p.q).\equiv .p\equiv {\sim}q\) -/
theorem pm5_17 {p q : Prop} : (p ∨ q) ∧ ¬(p ∧ q) ↔ (p ↔ ¬q) := by tauto

/-- ✱5·18. \(\vdash:p\equiv q.\equiv .{\sim}(p\equiv {\sim}q) \quad\left[\text{*5·15·16.*5·17}\, \frac{p\equiv q,\,p\equiv {\sim}q}{p,\,\,\,q}\right]\) -/
theorem pm5_18 {p q : Prop} : (p ↔ q) ↔ ¬(p ↔ ¬q) := by tauto

/-- ✱5·19. \(\vdash.{\sim}(p\equiv {\sim}p) \quad\left[\text{*5·18}\, \frac{p}{q}.\text{*4·2}\right]\) -/
theorem pm5_19 {p : Prop} : ¬(p ↔ ¬p) := by tauto

/-- ✱5·21. \(\vdash:{\sim}p.{\sim}q.\supset .p\equiv q \quad[\text{*5·1.*4·11}]\) -/
theorem pm5_21 {p q : Prop} : ¬p ∧ ¬q → (p ↔ q) := by tauto

/-- ✱5·22. \(\vdash\colon\ldotp {\sim}(p\equiv q).\equiv :p.{\sim}q.\lor .q.{\sim}p \quad[\text{*4·61·51·39}]\) -/
theorem pm5_22 {p q : Prop} : ¬(p ↔ q) ↔ (p ∧ ¬q) ∨ (q ∧ ¬p) := by tauto

/-- ✱5·23. \(\vdash\colon\ldotp p\equiv q.\equiv :p.q.\lor .{\sim}p.{\sim}q \quad\left[\text{*5·18.*5·22}\, \frac{{\sim}q}{q}.\text{*4·13·36}\right]\) -/
theorem pm5_23 {p q : Prop} : (p ↔ q) ↔ (p ∧ q) ∨ (¬p ∧ ¬q) := by tauto

/-- ✱5·24. \(\vdash\colon\ldotp {\sim}(p.q.\lor .{\sim}p.{\sim}q).\equiv :p.{\sim}q.\lor .q.{\sim}p \quad[\text{*5·22·23}]\) -/
theorem pm5_24 {p q : Prop} : ¬((p ∧ q) ∨ (¬p ∧ ¬q)) ↔ (p ∧ ¬q) ∨ (q ∧ ¬p) := by tauto

/-- ✱5·25. \(\vdash\colon\ldotp p\lor q.\equiv :p\supset q.\supset .q \quad[\text{*2·62·68}]\) -/
theorem pm5_25 {p q : Prop} : p ∨ q ↔ ((p → q) → q) := by tauto

/-- ✱5·3. \(\vdash\colon\ldotp p.q.\supset .r:\equiv :p.q.\supset .p.r \quad[\text{Simp. Comp. Syll}]\) -/
theorem pm5_3 {p q r : Prop} : (p ∧ q → r) ↔ (p ∧ q → p ∧ r) := by tauto

/-- ✱5·31. \(\vdash\colon\ldotp r.p\supset q:\supset :p.\supset .q.r \quad[\text{Simp. Comp}]\) -/
theorem pm5_31 {p q r : Prop} : r ∧ (p → q) → (p → q ∧ r) := by tauto

/-- ✱5·32. \(\vdash\colon\ldotp p.\supset .q\equiv r:\equiv :p.q.\equiv .p.r \quad[\text{*4·76.*3·3·31.*5·3}]\) -/
theorem pm5_32 {p q r : Prop} : (p → (q ↔ r)) ↔ (p ∧ q ↔ p ∧ r) := by tauto

/-- ✱5·33. \(\vdash\colon\ldotp p.q\supset r.\equiv :p:p.q.\supset .r \quad[\text{*4·73·84.*5·32}]\) -/
theorem pm5_33 {p q r : Prop} : p ∧ (q → r) ↔ p ∧ (p ∧ q → r) := by tauto

/-- ✱5·35. \(\vdash\colon\ldotp p\supset q.p\supset r.\supset :p.\supset .q\equiv r \quad[\text{Comp. *5·1}]\) -/
theorem pm5_35 {p q r : Prop} : (p → q) ∧ (p → r) → (p → (q ↔ r)) := by tauto

/-- ✱5·36. \(\vdash:p.p\equiv q.\equiv .q.p\equiv q \quad[\text{Ass. *4·38}]\) -/
theorem pm5_36 {p q : Prop} : p ∧ (p ↔ q) ↔ q ∧ (p ↔ q) := by tauto

/-- ✱5·4. \(\vdash\colon\ldotp p.\supset .p\supset q:\equiv .p\supset q \quad[\text{Simp. *2·43}]\) -/
theorem pm5_4 {p q : Prop} : (p → (p → q)) ↔ (p → q) := by tauto

/-- ✱5·41. \(\vdash\colon\ldotp p\supset q.\supset .p\supset r:\equiv :p.\supset .q\supset r \quad[\text{*2·77·86}]\) -/
theorem pm5_41 {p q r : Prop} : ((p → q) → (p → r)) ↔ (p → (q → r)) := by tauto

/-- ✱5·42. \(\vdash\colon\colon p.\supset .q\supset r:\equiv \colon\ldotp p.\supset :q.\supset .p.r \quad[\text{*5·3.*4·87}]\) -/
theorem pm5_42 {p q r : Prop} : (p → (q → r)) ↔ (p → (q → p ∧ r)) := by tauto

/-- ✱5·44. \(\vdash\colon\colon p\supset q.\supset \colon\ldotp p\supset r.\equiv :p.\supset .q.r \quad[\text{*4·76.*5·3·32}]\) -/
theorem pm5_44 {p q r : Prop} : (p → q) → ((p → r) ↔ (p → q ∧ r)) := by tauto

/-- ✱5·5. \(\vdash\colon\ldotp p.\supset :p\supset q.\equiv .q \quad[\text{Ass. Exp. Simp}]\) -/
theorem pm5_5 {p q : Prop} : p → ((p → q) ↔ q) := by tauto

/-- ✱5·501. \(\vdash\colon\ldotp p.\supset :q.\equiv .p\equiv q \quad[\text{*5·1.Exp. Ass}]\) -/
theorem pm5_501 {p q : Prop} : p → (q ↔ (p ↔ q)) := by tauto

/-- ✱5·53. \(\vdash\colon\ldotp p\lor q\lor r.\supset .s:\equiv :p\supset s.q\supset s.r\supset s \quad[\text{*4·77}]\) -/
theorem pm5_53 {p q r s : Prop} : ((p ∨ q) ∨ r → s) ↔ ((p → s) ∧ (q → s)) ∧ (r → s) := by tauto

/-- ✱5·54. \(\vdash\colon\ldotp p.q.\equiv .p:\lor :p.q.\equiv .q \quad[\text{*4·73.*4·44.Transp. *5·1}]\) -/
theorem pm5_54 {p q : Prop} : (p ∧ q ↔ p) ∨ (p ∧ q ↔ q) := by tauto

/-- ✱5·55. \(\vdash\colon\ldotp p\lor q.\equiv .p:\lor :p\lor q.\equiv .q \quad[\text{*1·3.*5·1.*4·74}]\) -/
theorem pm5_55 {p q : Prop} : (p ∨ q ↔ p) ∨ (p ∨ q ↔ q) := by tauto

/-- ✱5·6. \(\vdash\colon\ldotp p.{\sim}q.\supset .r:\equiv :p.\supset .q\lor r \quad\left[\text{*4·87}\, \frac{{\sim}q}{q}.\text{*4·64·85}\right]\) -/
theorem pm5_6 {p q r : Prop} : (p ∧ ¬q → r) ↔ (p → q ∨ r) := by tauto

/-- ✱5·61. \(\vdash:p\lor q.{\sim}q.\equiv .p.{\sim}q \quad[\text{*4·74.*5·32}]\) -/
theorem pm5_61 {p q : Prop} : (p ∨ q) ∧ ¬q ↔ p ∧ ¬q := by tauto

/-- ✱5·62. \(\vdash\colon\ldotp p.q.\lor .{\sim}q:\equiv .p\lor {\sim}q \quad\left[\text{*4·7}\, \frac{q,\,p}{p,\,q}\right]\) -/
theorem pm5_62 {p q : Prop} : (p ∧ q) ∨ ¬q ↔ p ∨ ¬q := by tauto

/-- ✱5·63. \(\vdash\colon\ldotp p\lor q.\equiv :p.\lor .{\sim}p.q \quad\left[\text{*5·62}\, \frac{{\sim}p,\,q}{q,\,p}\right]\) -/
theorem pm5_63 {p q : Prop} : p ∨ q ↔ p ∨ (¬p ∧ q) := by tauto

/-- ✱5·7. \(\vdash\colon\ldotp p\lor r.\equiv .q\lor r:\equiv :r.\lor .p\equiv q \quad[\text{*4·74.*1·3.*5·1.*4·37}]\) -/
theorem pm5_7 {p q r : Prop} : (p ∨ r ↔ q ∨ r) ↔ r ∨ (p ↔ q) := by tauto

/-- ✱5·71. \(\vdash\colon\ldotp q\supset {\sim}r.\supset :p\lor q.r.\equiv .p.r\) -/
theorem pm5_71 {p q r : Prop} : (q → ¬r) → ((p ∨ q) ∧ r ↔ p ∧ r) := by tauto

/-- ✱5·74. \(\vdash\colon\ldotp p.\supset .q\equiv r:\equiv :p\supset q.\equiv .p\supset r\) -/
theorem pm5_74 {p q r : Prop} : (p → (q ↔ r)) ↔ ((p → q) ↔ (p → r)) := by tauto

/-- ✱5·75. \(\vdash\colon\ldotp r\supset {\sim}q:p.\equiv .q\lor r:\supset :p.{\sim}q.\equiv .r\) -/
theorem pm5_75 {p q r : Prop} : (r → ¬q) ∧ (p ↔ q ∨ r) → (p ∧ ¬q ↔ r) := by tauto

end PrincipiaMathematica
