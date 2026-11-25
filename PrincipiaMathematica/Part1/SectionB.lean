import PrincipiaMathematica.Defs.Part1

/-!
# Part I, Section B: Theory of apparent variables

Volume 1. Numbers: ✱9, ✱10, ✱11, ✱12, ✱13, ✱14.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-!
## [✱9] Extension of the theory of deduction from lower to higher types of propositions

*(Vol. 1, p. 132)*

> *Summary of* *9.
>
> …

**Lean reading.** PM introduces `(x).φx` and `(∃x).φx` as primitive ideas and *defines* the
negation and disjunction of quantified propositions by prenex forms (✱9·01–✱9·08), because `∼` and
`∨` are primitive only for elementary propositions. In Lean `∀ x, φ x` and `∃ x, φ x` are Lean's
quantifiers and `¬`, `∨` apply to every proposition, so these Dfs become classical equivalences
(`proved (reading)`; ✱9·011, ✱9·021 hold by `Iff.rfl`); ✱9·05–✱9·08 need `[Nonempty _]`, PM's
tacit assumption that every type has a member. The primitive propositions ✱9·1, ✱9·11 are
theorems; ✱9·12 (inference) and ✱9·13 (generalization of a real variable) are recorded as derivable
rules. ✱9·131, ✱9·14, ✱9·15 and ✱9·6–✱9·63 concern types, significance and the existence of
functions: in Lean they are typing facts, recorded as `remark`s by the corresponding typed terms.
The theorems ✱9·2–✱9·521 show that `(x).φx`, `(∃x).φx` may replace `p, q, r` in ✱1·2–✱1·6; in
Lean they are instances of the propositional laws.

**Status.** proved (all propositions; ✱9·01–✱9·08 except ✱9·011, ✱9·021 (definition), ✱9·12,
✱9·13 proved (reading), ✱9·05–✱9·08 with `[Nonempty _]`; ✱9·131, ✱9·14, ✱9·15, ✱9·6, ✱9·61,
✱9·62, ✱9·63 remark)
-/

/-- ✱9·01 (Df). \(\sim \{(x)\ldotp \phi x\}\ldotp =\ldotp (\exists x)\ldotp \sim \phi x \quad \text{Df}\)

**Status.** proved (reading): PM defines the negation of `(x).φx`; Lean's `¬` is primitive for
all propositions, so the Df is the classical equivalence of `¬ ∀ x, φ x` with the definiens. -/
theorem pm9_01 {φ : α → Prop} : ¬(∀ x, φ x) ↔ ∃ x, ¬φ x :=
  ⟨fun h => Classical.byContradiction fun h' =>
      h fun x => Classical.byContradiction fun hx => h' ⟨x, hx⟩,
    fun ⟨x, hx⟩ h => hx (h x)⟩

/-- ✱9·02 (Df). \(\sim \{(\exists x)\ldotp \phi x\}\ldotp =\ldotp (x)\ldotp \sim \phi x \quad \text{Df}\)

**Status.** proved (reading): as ✱9·01, for the negation of `(∃x).φx`. -/
theorem pm9_02 {φ : α → Prop} : ¬(∃ x, φ x) ↔ ∀ x, ¬φ x :=
  ⟨fun h x hx => h ⟨x, hx⟩, fun h ⟨x, hx⟩ => h x hx⟩

/-- ✱9·011 (Df). \(\sim (x)\ldotp \phi x\ldotp =\ldotp \sim \{(x)\ldotp \phi x\} \quad \text{Df}\)

**Status.** definition: a bracketing convention (`∼` before a prefix negates the whole quantified
proposition); it holds by `Iff.rfl`. -/
theorem pm9_011 {φ : α → Prop} : (¬ ∀ x, φ x) ↔ ¬(∀ x, φ x) := Iff.rfl

/-- ✱9·021 (Df). \(\sim (\exists x)\ldotp \phi x\ldotp =\ldotp \sim \{(\exists x)\ldotp \phi x\} \quad \text{Df}\)

**Status.** definition: a bracketing convention, as ✱9·011; it holds by `Iff.rfl`. -/
theorem pm9_021 {φ : α → Prop} : (¬ ∃ x, φ x) ↔ ¬(∃ x, φ x) := Iff.rfl

/-- ✱9·03 (Df). (\(x)\ldotp \phi x\ldotp \lor \ldotp p\colon=\ldotp (x)\ldotp \phi x \lor p \quad \text{Df}\)

**Status.** proved (reading): PM defines the disjunction by its prenex form; Lean's `∨` applies
to all propositions, so the Df is a (classical) equivalence. -/
theorem pm9_03 {p : Prop} {φ : α → Prop} : (∀ x, φ x) ∨ p ↔ ∀ x, φ x ∨ p := by
  constructor
  · rintro (h | h) x
    · exact Or.inl (h x)
    · exact Or.inr h
  · intro h
    by_cases hp : p
    · exact Or.inr hp
    · exact Or.inl fun x => (h x).resolve_right hp

/-- ✱9·04 (Df). \(p\ldotp \lor \ldotp (x)\ldotp \phi x\colon=\ldotp (x)\ldotp p \lor \phi x \quad \text{Df}\)

**Status.** proved (reading): as ✱9·03. -/
theorem pm9_04 {p : Prop} {φ : α → Prop} : p ∨ (∀ x, φ x) ↔ ∀ x, p ∨ φ x := by
  constructor
  · rintro (h | h) x
    · exact Or.inl h
    · exact Or.inr (h x)
  · intro h
    by_cases hp : p
    · exact Or.inl hp
    · exact Or.inr fun x => (h x).resolve_left hp

/-- ✱9·05 (Df). (\(\exists x)\ldotp \phi x\ldotp \lor \ldotp p\colon=\ldotp (\exists x)\ldotp \phi x \lor p \quad \text{Df}\)

**Status.** proved (reading): as ✱9·03; with `[Nonempty α]`: PM assumes every type has a member
(Introduction, Ch. I); for an empty `α` the left side is `p` and the right side is false. -/
theorem pm9_05 [Nonempty α] {p : Prop} {φ : α → Prop} : (∃ x, φ x) ∨ p ↔ ∃ x, φ x ∨ p := by
  constructor
  · rintro (⟨x, hx⟩ | hp)
    · exact ⟨x, Or.inl hx⟩
    · exact ⟨Classical.arbitrary α, Or.inr hp⟩
  · rintro ⟨x, hx | hp⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr hp

/-- ✱9·06 (Df). \(p\ldotp \lor \ldotp (\exists x)\ldotp \phi x\colon=\ldotp (\exists x)\ldotp p \lor \phi x \quad \text{Df}\)

**Status.** proved (reading): as ✱9·05, with `[Nonempty α]`: PM assumes every type has a member
(Introduction, Ch. I). -/
theorem pm9_06 [Nonempty α] {p : Prop} {φ : α → Prop} : p ∨ (∃ x, φ x) ↔ ∃ x, p ∨ φ x := by
  constructor
  · rintro (hp | ⟨x, hx⟩)
    · exact ⟨Classical.arbitrary α, Or.inl hp⟩
    · exact ⟨x, Or.inr hx⟩
  · rintro ⟨x, hp | hx⟩
    · exact Or.inl hp
    · exact Or.inr ⟨x, hx⟩

/-- ✱9·07 (Df). (\(x)\ldotp \phi x\ldotp \lor \ldotp (\exists y)\ldotp \psi y \colon=\colon(x)\colon(\exists y)\ldotp \phi x \lor \psi y \quad \text{Df}\)

**Status.** proved (reading): as ✱9·03; with `[Nonempty β]` (the type of `y`): PM assumes every
type has a member (Introduction, Ch. I); for an empty `β` and a nonempty `α` with `φ` always true
the left side holds and the right side fails. -/
theorem pm9_07 [Nonempty β] {φ : α → Prop} {ψ : β → Prop} :
    (∀ x, φ x) ∨ (∃ y, ψ y) ↔ ∀ x, ∃ y, φ x ∨ ψ y := by
  constructor
  · rintro (h | ⟨y, hy⟩) x
    · exact ⟨Classical.arbitrary β, Or.inl (h x)⟩
    · exact ⟨y, Or.inr hy⟩
  · intro h
    by_cases hψ : ∃ y, ψ y
    · exact Or.inr hψ
    · refine Or.inl fun x => ?_
      obtain ⟨y, hy | hy⟩ := h x
      · exact hy
      · exact absurd ⟨y, hy⟩ hψ

/-- ✱9·08 (Df). (\(\exists y)\ldotp \psi y\ldotp \lor \ldotp (x)\ldotp \phi x\colon=\colon(x)\colon(\exists y)\ldotp \psi y \lor \phi x \quad \text{Df}\)

**Status.** proved (reading): as ✱9·07, with `[Nonempty β]`: PM assumes every type has a member
(Introduction, Ch. I). -/
theorem pm9_08 [Nonempty β] {φ : α → Prop} {ψ : β → Prop} :
    (∃ y, ψ y) ∨ (∀ x, φ x) ↔ ∀ x, ∃ y, ψ y ∨ φ x := by
  constructor
  · rintro (⟨y, hy⟩ | h) x
    · exact ⟨y, Or.inl hy⟩
    · exact ⟨Classical.arbitrary β, Or.inr (h x)⟩
  · intro h
    by_cases hψ : ∃ y, ψ y
    · exact Or.inl hψ
    · refine Or.inr fun x => ?_
      obtain ⟨y, hy | hy⟩ := h x
      · exact absurd ⟨y, hy⟩ hψ
      · exact hy

/-- ✱9·1 (Pp). \(\vdash: \phi x .\supset. (\exists z).\phi z \quad \text{Pp}\) -/
theorem pm9_1 {φ : α → Prop} {x : α} : φ x → ∃ z, φ z := fun h => ⟨x, h⟩

/-- ✱9·11 (Pp). \(\vdash: \phi x \lor \phi y .\supset. (\exists z) . \phi z \quad \text{Pp}\) -/
theorem pm9_11 {φ : α → Prop} {x y : α} : φ x ∨ φ y → ∃ z, φ z :=
  fun h => h.elim (fun hx => ⟨x, hx⟩) (fun hy => ⟨y, hy⟩)

/-- ✱9·12 (Pp). \(\text{What is implied by a true premiss is true.} \quad \text{Pp}\text{.}\)

**Status.** proved (reading): a rule of inference (meta-level, as ✱1·1), now for propositions that
need not be elementary; in Lean, inference is the application of a proof of `p → q` to a proof of
`p`, for arbitrary `p q : Prop` (the form for asserted functions is ✱1·11's). -/
theorem pm9_12 {p q : Prop} (hp : p) (hpq : p → q) : q := hpq hp

/-- ✱9·13 (Pp). In any assertion containing a real variable, this real variable may be turned into an apparent variable of which all possible values are asserted to satisfy the function in question. Pp.

**Status.** proved (reading): a rule of inference (meta-level): an assertion `φy` with a real
variable `y` is, in Lean, a proof of `φ y` for an arbitrary `y`, i.e. of `∀ y, φ y`; the rule
passes to the apparent variable `(x).φx`. -/
theorem pm9_13 {φ : α → Prop} (h : ∀ y, φ y) : ∀ x, φ x := h

/-- ✱9·131. *Definition of "being of the same type."* The following is a step-by-step definition, the definition for higher types presupposing that for lower types. We say that \(u\) and \(v\) "are of the same type" if (1) both are individuals, (2) both are elementary functions taking arguments of the same type, (3) \(u\) is a function and \(v\) is its negation, (4) \(u\) is \(\phi \hat{x}\) or \(\psi\hat{x}\) and \(v\) is \(\phi \hat{x} \lor \psi \hat{x}\), where \(\phi \hat{x}\) and \(\psi \hat{x}\) are elementary functions, (5) \(u\) is \((y). \phi (\hat{x},y)\) and \(v\) is (\(z). \psi (\hat{x},z)\), where \(\phi (\hat{x}, \hat{y})\), \(\psi (\hat{x}, \hat{y})\) are of the same type, (6) both are elementary propositions, (7) \(u\) is a proposition and \(v\) is \({\sim}u\), or (8) \(u\) is (\(x).\phi x\) and \(v\) is (\(y).\psi y\), where \(\phi \hat{x}\) and \(\psi \hat{x}\) are of the same type.

**Status.** remark: a (step-by-step, meta-level) definition of "being of the same type". In Lean
every term has a type and two terms are of the same type when their Lean types coincide; clauses
(1)–(8) become typing facts (`¬`, `∨`, `∀`, `∃` preserve the type `Prop` and functions with
arguments in `α` all have type `α → Prop`). The declaration records the relation as the equality
of the Lean types. -/
def pm9_131 {σ τ : Sort u} (_u : σ) (_v : τ) : Prop := σ = τ

/-- ✱9·14. If "\(\phi x\)" is significant, then if \(x\) is of the same type as \(a\), "\(\phi a\)" is significant, and vice versa. Pp. (Cf. note on *10·121, p. 146.)

**Status.** remark: a primitive proposition about significance (meta-level). In Lean a function
`φ : α → Prop` is significant exactly for the arguments of type `α`, and then for every one of
them; the declaration records the typing: `φ a` is a proposition for every `a : α`. -/
def pm9_14 (φ : α → Prop) (a : α) : Prop := φ a

/-- ✱9·15 (Pp). If, for some \(a\), there is a proposition \(\phi a\), then there is a function \(\phi \hat{x}\), and vice versa. Pp.

**Status.** remark: a meta-level primitive proposition (a proposition `φa` yields the function
`φx̂`, and vice versa). In Lean the function is the term `fun x => φ x`, whose values are the
propositions `φ a`; the declaration records it. -/
def pm9_15 (φ : α → Prop) : α → Prop := fun x => φ x

/-- ✱9·2. \(\vdash:(x). \phi x .\supset. \phi y\) -/
theorem pm9_2 {φ : α → Prop} {y : α} : (∀ x, φ x) → φ y := fun h => h y

/-- ✱9·21. \(\vdash \colon\ldotp (x) . \phi x \supset \psi x . \supset : (x) . \phi x . \supset . (x) . \psi x\) -/
theorem pm9_21 {φ ψ : α → Prop} : (∀ x, φ x → ψ x) → ((∀ x, φ x) → ∀ x, ψ x) :=
  fun h h' x => h x (h' x)

/-- ✱9·22. \(\vdash \colon\ldotp (x) . \phi x \supset \psi x . \supset : (\exists x) . \phi x . \supset . (\exists x) . \psi x\) -/
theorem pm9_22 {φ ψ : α → Prop} : (∀ x, φ x → ψ x) → ((∃ x, φ x) → ∃ x, ψ x) :=
  fun h ⟨x, hx⟩ => ⟨x, h x hx⟩

/-- ✱9·23. \(\vdash:(x).\phi x.\supset .(x).\phi x \quad[\text{Id.*9·13·21}]\) -/
theorem pm9_23 {φ : α → Prop} : (∀ x, φ x) → ∀ x, φ x := id

/-- ✱9·24. \(\vdash:(\exists x).\phi x.\supset .(\exists x).\phi x \quad[\text{Id.*9·13·22}]\) -/
theorem pm9_24 {φ : α → Prop} : (∃ x, φ x) → ∃ x, φ x := id

/-- ✱9·25. \(\vdash\colon\ldotp (x).p\lor \phi x.\supset :p.\lor .(x).\phi x \quad[\text{*9·23.(*9·04)}]\) -/
theorem pm9_25 {p : Prop} {φ : α → Prop} : (∀ x, p ∨ φ x) → p ∨ ∀ x, φ x := pm9_04.2

/-- ✱9·3. \(\vdash\colon\ldotp (x).\phi x.\lor .(x).\phi x:\supset .(x).\phi x\) -/
theorem pm9_3 {φ : α → Prop} : (∀ x, φ x) ∨ (∀ x, φ x) → ∀ x, φ x := fun h => h.elim id id

/-- ✱9·31. \(\vdash\colon\ldotp (\exists x).\phi x.\lor .(\exists x).\phi x:\supset .(\exists x).\phi x\) -/
theorem pm9_31 {φ : α → Prop} : (∃ x, φ x) ∨ (∃ x, φ x) → ∃ x, φ x := fun h => h.elim id id

/-- ✱9·32. \(\vdash\colon\ldotp q.\supset :(x).\phi x.\lor .q\) -/
theorem pm9_32 {q : Prop} {φ : α → Prop} : q → (∀ x, φ x) ∨ q := Or.inr

/-- ✱9·33. \(\vdash\colon\ldotp q.\supset :(\exists x).\phi x.\lor .q \quad[\text{Proof as above}]\) -/
theorem pm9_33 {q : Prop} {φ : α → Prop} : q → (∃ x, φ x) ∨ q := Or.inr

/-- ✱9·34. \(\vdash\colon\ldotp (x).\phi x.\supset :p.\lor .(x).\phi x\) -/
theorem pm9_34 {p : Prop} {φ : α → Prop} : (∀ x, φ x) → p ∨ ∀ x, φ x := Or.inr

/-- ✱9·35. \(\vdash\colon\ldotp (\exists x).\phi x.\supset :p.\lor .(\exists x).\phi x \quad[\text{Proof as above}]\) -/
theorem pm9_35 {p : Prop} {φ : α → Prop} : (∃ x, φ x) → p ∨ ∃ x, φ x := Or.inr

/-- ✱9·36. \(\vdash\colon\ldotp p.\lor .(x).\phi x:\supset :(x).\phi x.\lor .p\) -/
theorem pm9_36 {p : Prop} {φ : α → Prop} : p ∨ (∀ x, φ x) → (∀ x, φ x) ∨ p := Or.symm

/-- ✱9·361. \(\vdash\colon\ldotp (x).\phi x.\lor .p:\supset :p.\lor .(x).\phi x \quad[\text{Similar proof}]\) -/
theorem pm9_361 {p : Prop} {φ : α → Prop} : (∀ x, φ x) ∨ p → p ∨ ∀ x, φ x := Or.symm

/-- ✱9·37. \(\vdash\colon\ldotp p.\lor .(\exists x).\phi x:\supset :(\exists x).\phi x.\lor .p \quad[\text{Similar proof}]\) -/
theorem pm9_37 {p : Prop} {φ : α → Prop} : p ∨ (∃ x, φ x) → (∃ x, φ x) ∨ p := Or.symm

/-- ✱9·371. \(\vdash\colon\ldotp (\exists x).\phi x.\lor .p:\supset :p.\lor .(\exists x).\phi x \quad[\text{Similar proof}]\) -/
theorem pm9_371 {p : Prop} {φ : α → Prop} : (∃ x, φ x) ∨ p → p ∨ ∃ x, φ x := Or.symm

/-- ✱9·4. \(\vdash\colon\colon p:\lor :q.\lor .(x).\phi x\colon\ldotp \supset \colon\ldotp q:\lor :p.\lor .(x).\phi x\) -/
theorem pm9_4 {p q : Prop} {φ : α → Prop} :
    p ∨ (q ∨ ∀ x, φ x) → q ∨ (p ∨ ∀ x, φ x) :=
  fun h => h.elim (fun hp => Or.inr (Or.inl hp)) (Or.imp_right Or.inr)

/-- ✱9·401. \(\vdash\colon\colon p:\lor :q.\lor .(\exists x).\phi x\colon\ldotp \supset \colon\ldotp q:\lor :p.\lor .(\exists x).\phi x \quad[\text{As above}]\) -/
theorem pm9_401 {p q : Prop} {φ : α → Prop} :
    p ∨ (q ∨ ∃ x, φ x) → q ∨ (p ∨ ∃ x, φ x) :=
  fun h => h.elim (fun hp => Or.inr (Or.inl hp)) (Or.imp_right Or.inr)

/-- ✱9·41. \(\vdash\colon\colon p:\lor :(x).\phi x.\lor .r\colon\ldotp \supset \colon\ldotp (x).\phi x:\lor :p\lor r \quad[\text{As above}]\) -/
theorem pm9_41 {p r : Prop} {φ : α → Prop} :
    p ∨ ((∀ x, φ x) ∨ r) → (∀ x, φ x) ∨ (p ∨ r) :=
  fun h => h.elim (fun hp => Or.inr (Or.inl hp)) (Or.imp_right Or.inr)

/-- ✱9·411. \(\vdash\colon\colon p:\lor :(\exists x).\phi x.\lor .r\colon\ldotp \supset \colon\ldotp (\exists x).\phi x:\lor :p\lor r \quad[\text{As above}]\) -/
theorem pm9_411 {p r : Prop} {φ : α → Prop} :
    p ∨ ((∃ x, φ x) ∨ r) → (∃ x, φ x) ∨ (p ∨ r) :=
  fun h => h.elim (fun hp => Or.inr (Or.inl hp)) (Or.imp_right Or.inr)

/-- ✱9·42. \(\vdash\colon\colon (x).\phi x:\lor :q\lor r\colon\ldotp \supset \colon\ldotp q:\lor :(x).\phi x.\lor .r \quad[\text{As above}]\) -/
theorem pm9_42 {q r : Prop} {φ : α → Prop} :
    (∀ x, φ x) ∨ (q ∨ r) → q ∨ ((∀ x, φ x) ∨ r) :=
  fun h => h.elim (fun hp => Or.inr (Or.inl hp)) (Or.imp_right Or.inr)

/-- ✱9·421. \(\vdash\colon\colon (\exists x).\phi x:\lor :q\lor r\colon\ldotp \supset \colon\ldotp q:\lor :(\exists x).\phi x.\lor .r \quad[\text{As above}]\) -/
theorem pm9_421 {q r : Prop} {φ : α → Prop} :
    (∃ x, φ x) ∨ (q ∨ r) → q ∨ ((∃ x, φ x) ∨ r) :=
  fun h => h.elim (fun hp => Or.inr (Or.inl hp)) (Or.imp_right Or.inr)

/-- ✱9·5. \(\vdash\colon\colon p\supset q.\supset \colon\ldotp p.\lor .(x).\phi x:\supset :q.\lor .(x).\phi x\) -/
theorem pm9_5 {p q : Prop} {φ : α → Prop} :
    (p → q) → (p ∨ (∀ x, φ x) → q ∨ ∀ x, φ x) :=
  fun h => Or.imp_left h

/-- ✱9·501. \(\vdash\colon\colon p\supset q.\supset \colon\ldotp p.\lor .(\exists x).\phi x:\supset :q.\lor .(\exists x).\phi x \quad[\text{As above}]\) -/
theorem pm9_501 {p q : Prop} {φ : α → Prop} :
    (p → q) → (p ∨ (∃ x, φ x) → q ∨ ∃ x, φ x) :=
  fun h => Or.imp_left h

/-- ✱9·51. \(\vdash\colon\colon p.\supset .(x).\phi x:\supset \colon\ldotp p\lor r.\supset :(x).\phi x.\lor .r\) -/
theorem pm9_51 {p r : Prop} {φ : α → Prop} :
    (p → ∀ x, φ x) → (p ∨ r → (∀ x, φ x) ∨ r) :=
  fun h => Or.imp_left h

/-- ✱9·511. \(\vdash\colon\colon p.\supset .(\exists x).\phi x:\supset \colon\ldotp p\lor r.\supset :(\exists x).\phi x.\lor .r \quad[\text{As above}]\) -/
theorem pm9_511 {p r : Prop} {φ : α → Prop} :
    (p → ∃ x, φ x) → (p ∨ r → (∃ x, φ x) ∨ r) :=
  fun h => Or.imp_left h

/-- ✱9·52. \(\vdash\colon\colon (x).\phi x.\supset .q:\supset \colon\ldotp (x).\phi x.\lor .r:\supset .q\lor r\) -/
theorem pm9_52 {q r : Prop} {φ : α → Prop} :
    ((∀ x, φ x) → q) → ((∀ x, φ x) ∨ r → q ∨ r) :=
  fun h => Or.imp_left h

/-- ✱9·521. \(\vdash\colon\colon (\exists x).\phi x.\supset .q:\supset \colon\ldotp (\exists x).\phi x.\lor .r:\supset .q\lor r \quad[\text{As above}]\) -/
theorem pm9_521 {q r : Prop} {φ : α → Prop} :
    ((∃ x, φ x) → q) → ((∃ x, φ x) ∨ r → q ∨ r) :=
  fun h => Or.imp_left h

/-- ✱9·6. \[\begin{align}(x).\phi x,\, {\sim}(x).\phi x\,\, (\exists x).\phi x\,\, \text{and}\,\, {\sim}(\exists x).\phi x\,\, &\text{are of the same type}.\\ &[\text{*9·131, (7) and (8)}]\end{align}\]

**Status.** remark: a statement about types (meta-level). In Lean the four are propositions, terms
of the one type `Prop`; the declaration records them together, which typechecks only because they
are of the same type. -/
def pm9_6 (φ : α → Prop) : List Prop := [∀ x, φ x, ¬ ∀ x, φ x, ∃ x, φ x, ¬ ∃ x, φ x]

/-- ✱9·61. If \(\phi\hat{x}\) and \(\psi\hat{x}\) are elementary functions of the same type, there is a function \(\phi\hat{x} \lor \psi\hat{x}\).

**Status.** remark: existence of a function (meta-level). In Lean the function `φx̂ ∨ ψx̂` is the
term `fun x => φ x ∨ ψ x`, formed when `φ` and `ψ` take arguments of the same type `α`. -/
def pm9_61 (φ ψ : α → Prop) : α → Prop := fun x => φ x ∨ ψ x

/-- ✱9·62. If \(\phi(\hat{x},\hat{y})\) and \(\psi\hat{z}\) are elementary functions, and the \(x\)-argument to \(\phi\) is of the same type as the argument to \(\psi\), there are functions \[ (y).\phi(\hat{x},y). \lor .\psi\hat{x}, (\exists y).\phi(\hat{x},y). \lor .\psi\hat{x}. \]

**Status.** remark: existence of functions (meta-level), as ✱9·61: the declaration forms the two
functions `(y).φ(x̂, y) . ∨ . ψx̂` and `(∃y).φ(x̂, y) . ∨ . ψx̂` as Lean terms. -/
def pm9_62 (φ : α → β → Prop) (ψ : α → Prop) : (α → Prop) × (α → Prop) :=
  (fun x => (∀ y, φ x y) ∨ ψ x, fun x => (∃ y, φ x y) ∨ ψ x)

/-- ✱9·63. If \(\phi(\hat{x},\hat{y})\), \(\psi\hat{x},\hat{y})\) are elementary functions of the same type, there are functions (\(y).\phi(\hat{x},y).\lor .(z).\psi(\hat{x},z)\), etc. [Proof as above]

**Status.** remark: existence of functions (meta-level), as ✱9·61; the declaration forms
`(y).φ(x̂, y) . ∨ . (z).ψ(x̂, z)` (the "etc." cases are formed in the same way). The e-text's
`ψx̂,ŷ)` lacks the opening bracket of `ψ(x̂, ŷ)`. -/
def pm9_63 (φ ψ : α → β → Prop) : α → Prop := fun x => (∀ y, φ x y) ∨ ∀ z, ψ x z

/-!
## [✱10] Theory of propositions containing one apparent variable

*(Vol. 1, p. 143)*

> *Summary of* *10.
>
> The chief purpose of the propositions of this number is to extend to formal implications (*i.e.* to propositions of the form \((x).{\phi}x \supset {\psi}x\)) as many as possible of the propositions proved previously for material implications, *i.e.* for propositions of the form \(p \supset q\). Thus *e.g.* we have proved in *3·33 that \[ p \supset q . q \supset r .\supset. p \supset r\text{.} \]
>
> \[ \begin{align} \text{Put}\quad &p &=~ &\text{Socrates is a Greek}\text{,}\\ &q &=~ &\text{Socrates is a man}\text{,}\\ &r &=~ &\text{Socrates is a mortal}\text{.}\\ \end{align} \] Then we have "if 'Socrates is a Greek' implies 'Socrates is a man,' and 'Socrates is a man' implies 'Socrates is a mortal,' it follows that 'Socrates is a Greek' implies 'Socrates is a mortal.'" But this does not of itself prove that if all Greeks are men, and all men are mortals, then all Greeks are mortals.
>
> …

**Lean reading.** `(∃x).φx` (defined in ✱10·01 from `(x)`) is Lean's primitive `∃`, so ✱10·01 is a
classical equivalence; formal implication and equivalence (✱10·02·03) are `FImp`/`FEqv`, written
out as `∀ x, φ x → ψ x` and `∀ x, φ x ↔ ψ x` in the statements. Real variables (`y` in ✱10·1,
✱10·24, …) are implicit arguments; a product of hypotheses `A : B : ⊃ . C` stays the conjunction
`A ∧ B → C`. ✱10·11, ✱10·13 are rules of inference (meta-level) recorded as the derivable rules,
and ✱10·121, ✱10·122, ✱10·221 (types and significance) are `remark`s, as in ✱9. Where a
proposition is false for an empty type (✱10·25, ✱10·251, ✱10·33, ✱10·34, ✱10·36, ✱10·37) the
hypothesis `[Nonempty α]` makes PM's assumption that every type has a member explicit. ✱10·23 is
printed in the e-text as corrected by the Errata (p. 144).

**Status.** proved (all propositions; ✱10·01, ✱10·11, ✱10·13, ✱10·25, ✱10·251, ✱10·33, ✱10·34,
✱10·36, ✱10·37 proved (reading); ✱10·02, ✱10·03 definition; ✱10·121, ✱10·122, ✱10·221 remark)
-/

/-- ✱10·01 (Df). (\(\exists x).\phi x.=.{\sim}(x).{\sim}\phi x \quad\text{Df}\)

**Status.** proved (reading): `∃` is Lean's primitive, so PM's definition of `(∃x).φx` becomes the
classical equivalence with the definiens `∼(x).∼φx`. -/
theorem pm10_01 {φ : α → Prop} : (∃ x, φ x) ↔ ¬ ∀ x, ¬φ x :=
  ⟨fun ⟨x, hx⟩ h => h x hx,
    fun h => Classical.byContradiction fun h' => h fun x hx => h' ⟨x, hx⟩⟩

/-- ✱10·02 (Df). \(\phi x\supset_{x}\psi x.=.(x).\phi x\supset\psi x \quad\text{Df}\) -/
theorem pm10_02 {φ ψ : α → Prop} : FImp φ ψ ↔ ∀ x, φ x → ψ x := Iff.rfl

/-- ✱10·03 (Df). \(\phi x\equiv_{x}\psi x.=.(x).\phi x\equiv\psi x \quad\text{Df}\) -/
theorem pm10_03 {φ ψ : α → Prop} : FEqv φ ψ ↔ ∀ x, φ x ↔ ψ x := Iff.rfl

/-- ✱10·1. \(\vdash:(x).\phi x.\supset \phi y \quad[\text{*9·2}]\) -/
theorem pm10_1 {φ : α → Prop} {y : α} : (∀ x, φ x) → φ y := fun h => h y

/-- ✱10·11. If \(\phi y\) is true whatever possible argument \(y\) may be, then (\(x).\phi x\) is true. [*9·13]

**Status.** proved (reading): a rule of inference (meta-level, ✱9·13): a proof of `φ y` for an
arbitrary `y` is a proof of `∀ y, φ y`, which gives `(x).φx`. -/
theorem pm10_11 {φ : α → Prop} (h : ∀ y, φ y) : ∀ x, φ x := h

/-- ✱10·12. \(\vdash\colon\ldotp (x).p\lor\phi x.\supset:p.\lor.(x).\phi x \quad[\text{*9·25}]\) -/
theorem pm10_12 {p : Prop} {φ : α → Prop} : (∀ x, p ∨ φ x) → p ∨ ∀ x, φ x := pm9_04.2

/-- ✱10·121. If "\(\phi x\)" is significant, then if \(a\) is of the same type as \(x\), "\(\phi a\)" is significant, and vice versa. [*9·14]

**Status.** remark: as ✱9·14 (significance, meta-level): in Lean `φ : α → Prop` is significant
for every argument of type `α`; the declaration records the typing. -/
def pm10_121 (φ : α → Prop) (a : α) : Prop := φ a

/-- ✱10·122. If, for some \(a\), there is a proposition \(\phi a\), then there is a function \(\phi\hat{x}\), and vice versa. [*9·15]

**Status.** remark: as ✱9·15: the function `φx̂` is the Lean term `fun x => φ x`. -/
def pm10_122 (φ : α → Prop) : α → Prop := fun x => φ x

/-- ✱10·13. If \(\phi\hat{x}\) and \(\psi\hat{x}\) take arguments of the same type, and we have "\(\vdash.\phi x\)" and "\(\vdash.\psi x\)," we shall have "\(\vdash.\phi x.\psi x\)."

**Status.** proved (reading): a rule of inference (meta-level): from the assertions `⊢ . φx` and
`⊢ . ψx` (proofs of `∀ x, φ x` and `∀ x, ψ x`, the real variable ranging over one type `α`, which is
PM's hypothesis that `φ` and `ψ` take arguments of the same type) follows `⊢ . φx . ψx`. -/
theorem pm10_13 {φ ψ : α → Prop} (hφ : ∀ x, φ x) (hψ : ∀ x, ψ x) : ∀ x, φ x ∧ ψ x :=
  fun x => ⟨hφ x, hψ x⟩

/-- ✱10·14. \(\vdash\colon\ldotp (x).\phi x:(x).\psi x:\supset.\phi y.\psi y\) -/
theorem pm10_14 {φ ψ : α → Prop} {y : α} : (∀ x, φ x) ∧ (∀ x, ψ x) → φ y ∧ ψ y :=
  fun ⟨h1, h2⟩ => ⟨h1 y, h2 y⟩

/-- ✱10·2. \(\vdash\colon\ldotp (x).p\lor \phi x.\equiv:p.\lor .(x)\phi x\) -/
theorem pm10_2 {p : Prop} {φ : α → Prop} : (∀ x, p ∨ φ x) ↔ p ∨ ∀ x, φ x := pm9_04.symm

/-- ✱10·21. \(\vdash\colon\ldotp (x).p\supset\phi x.\equiv:p.\supset.(x).\phi x \quad\left[\text{*10·2}\, \frac{{\sim}p}{p}\right]\) -/
theorem pm10_21 {p : Prop} {φ : α → Prop} : (∀ x, p → φ x) ↔ (p → ∀ x, φ x) :=
  ⟨fun h hp x => h x hp, fun h x hp => h hp x⟩

/-- ✱10·22. \(\vdash\colon\ldotp (x).\phi x.\psi x.\equiv:(x).\phi x:(x).\psi x\) -/
theorem pm10_22 {φ ψ : α → Prop} : (∀ x, φ x ∧ ψ x) ↔ (∀ x, φ x) ∧ ∀ x, ψ x :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun h x => ⟨h.1 x, h.2 x⟩⟩

/-- ✱10·221. If \(\phi x\) contains a constituent \(\chi(x, y, z, ...)\) and \(\psi x\) contains a constituent \(\chi(x, u, v, \ldots)\), where \(\chi\) is an elementary function and \(y, z, \ldots u, v, \ldots\) are either constants or apparent variables, then \(\phi\hat{x}\) and \(\psi\hat{x}\) take arguments of the same type. This can be proved in each particular case, though not generally, provided that, in obtaining \(\phi\) and \(\psi\) from \(\chi\), \(\chi\) is only submitted to negations, disjunctions and generalizations. The process may be illustrated by an example. Suppose \(\phi x\) is (\(y).\chi(x,y).\supset.\theta x\), and \(\psi x\) is \(fx.\supset.(y).\chi(x,y)\). By the definitions of *9, \(\phi x\) is (\(\exists y).{\sim}\chi(x,y)\lor \theta x\), and \(\psi x\) is (\(y).{\sim}fx\lor \chi(x,y)\). Hence since the primitive ideas (\(x).Fx\) and (\(\exists x).Fx\) only apply to functions, there are functions \({\sim}\chi(\hat{x},\hat{y})\lor \theta\hat{x}\), \({\sim}f\hat{x}\lor \chi(\hat{x},\hat{y})\). Hence there is a proposition \({\sim}\chi(a,b)\lor \theta a\). Hence, since "\(p\lor q\)" and "\({\sim}p\)" are only significant when \(p\) and \(q\) are propositions, there is a proposition \(\chi(a, b)\). Similarly, for some \(u\) and \(v\), there are propositions \({\sim}fu \lor \chi(u,v)\) and \(\chi(u, v)\). Hence by *9·14, \(u\) and \(a\), \(v\) and \(b\) are respectively of the same type, and (again by *9·14) there is a proposition \({\sim}fa\lor \chi(a, b)\). Hence (*9·15) there are functions \({\sim}\chi(a, \hat{y}) \lor \theta a\), \({\sim}fa \lor \chi(a, \hat{y})\), therefore there are propositions \[ (\exists y).{\sim}\chi(a, y) \lor \theta a, (y).{\sim}fa \lor \chi(a, y), \] *i.e.* there are propositions \(\phi a\), \(\psi a\), which was to be proved. This process can be applied similarly in any other instance.

**Status.** remark: a meta-level statement about the types of arguments (with PM's example). In
Lean, functions built from `χ` by negation, disjunction and generalization take their arguments in
the argument type of `χ` by typing; the declaration forms PM's two example functions
`(y).χ(x̂, y) . ⊃ . θx̂` and `fx̂ . ⊃ . (y).χ(x̂, y)`, both of type `α → Prop`. -/
def pm10_221 (χ : α → β → Prop) (θ f : α → Prop) : (α → Prop) × (α → Prop) :=
  (fun x => (∀ y, χ x y) → θ x, fun x => f x → ∀ y, χ x y)

/-- ✱10·23. \(\vdash\colon\ldotp (x).\phi x\supset p.\equiv:(\exists x).\phi x.\supset.p\)

**Status.** proved: the e-text prints ✱10·23 as corrected by the Errata to Vol. I (p. 144). -/
theorem pm10_23 {p : Prop} {φ : α → Prop} : (∀ x, φ x → p) ↔ ((∃ x, φ x) → p) :=
  ⟨fun h ⟨x, hx⟩ => h x hx, fun h x hx => h ⟨x, hx⟩⟩

/-- ✱10·24. \(\vdash:\phi y.\supset.(\exists x).\phi x\) -/
theorem pm10_24 {φ : α → Prop} {y : α} : φ y → ∃ x, φ x := fun h => ⟨y, h⟩

/-- ✱10·25. \(\vdash:(x).\phi x.\supset.(\exists x).\phi x \quad[\text{*10·1·24}]\)

**Status.** proved (reading): with `[Nonempty α]`: PM assumes every type has a member
(Introduction, Ch. I); for an empty `α` the hypothesis holds and the conclusion fails. -/
theorem pm10_25 [Nonempty α] {φ : α → Prop} : (∀ x, φ x) → ∃ x, φ x :=
  fun h => ⟨Classical.arbitrary α, h _⟩

/-- ✱10·251. \(\vdash:(x).{\sim}\phi x.\supset.{\sim}\{(x).\phi x\} \quad[\text{*10·25.Transp}]\)

**Status.** proved (reading): with `[Nonempty α]`, as ✱10·25 (PM assumes every type has a member,
Introduction, Ch. I); for an empty `α` both `(x).∼φx` and `(x).φx` hold. -/
theorem pm10_251 [Nonempty α] {φ : α → Prop} : (∀ x, ¬φ x) → ¬(∀ x, φ x) :=
  fun h h' => h (Classical.arbitrary α) (h' _)

/-- ✱10·252. \(\vdash:{\sim}\{(\exists x).\phi x\}.\equiv.(x).{\sim}\phi x \quad[\text{*4·13.(*10·01)}]\) -/
theorem pm10_252 {φ : α → Prop} : ¬(∃ x, φ x) ↔ ∀ x, ¬φ x := pm9_02

/-- ✱10·253. \(\vdash:{\sim}\{(x).\phi x\}.\equiv.(\exists x).{\sim}\phi x\) -/
theorem pm10_253 {φ : α → Prop} : ¬(∀ x, φ x) ↔ ∃ x, ¬φ x := pm9_01

/-- ✱10·26. \(\vdash\colon\ldotp (z).\phi z\supset\psi z:\phi x:\supset.\psi x \quad[\text{*10·1. Imp}]\) -/
theorem pm10_26 {φ ψ : α → Prop} {x : α} : (∀ z, φ z → ψ z) ∧ φ x → ψ x :=
  fun ⟨h, hx⟩ => h x hx

/-- ✱10·27. \(\vdash\colon\ldotp (z).\phi z\supset\psi z.\supset:(z).\phi z.\supset.(z).\psi z\) -/
theorem pm10_27 {φ ψ : α → Prop} : (∀ z, φ z → ψ z) → ((∀ z, φ z) → ∀ z, ψ z) :=
  fun h h' z => h z (h' z)

/-- ✱10·271. \(\vdash\colon\ldotp (z).\phi z\equiv\psi z.\supset:(z).\phi z.\equiv.(z).\psi z\) -/
theorem pm10_271 {φ ψ : α → Prop} : (∀ z, φ z ↔ ψ z) → ((∀ z, φ z) ↔ ∀ z, ψ z) :=
  fun h => ⟨fun h' z => (h z).1 (h' z), fun h' z => (h z).2 (h' z)⟩

/-- ✱10·28. \(\vdash\colon\ldotp (x).\phi x\supset\psi x.\supset:(\exists x).\phi x.\supset.(\exists x).\psi x\) -/
theorem pm10_28 {φ ψ : α → Prop} : (∀ x, φ x → ψ x) → ((∃ x, φ x) → ∃ x, ψ x) :=
  fun h ⟨x, hx⟩ => ⟨x, h x hx⟩

/-- ✱10·281. \(\vdash\colon\ldotp (x).\phi x\equiv\psi x.\supset:(\exists x).\phi x.\equiv.(\exists x).\psi x \quad[\text{*10·22·28.Comp}]\) -/
theorem pm10_281 {φ ψ : α → Prop} : (∀ x, φ x ↔ ψ x) → ((∃ x, φ x) ↔ ∃ x, ψ x) :=
  fun h => ⟨fun ⟨x, hx⟩ => ⟨x, (h x).1 hx⟩, fun ⟨x, hx⟩ => ⟨x, (h x).2 hx⟩⟩

/-- ✱10·29. \(\vdash\colon\ldotp (x).\phi x\supset\psi x:(x).\phi x\supset\chi x:\equiv:(x):\phi x.\supset.\psi x.\chi x.\) -/
theorem pm10_29 {φ ψ χ : α → Prop} :
    (∀ x, φ x → ψ x) ∧ (∀ x, φ x → χ x) ↔ ∀ x, φ x → ψ x ∧ χ x :=
  ⟨fun ⟨h1, h2⟩ x hx => ⟨h1 x hx, h2 x hx⟩,
    fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩⟩

/-- ✱10·3. \(\vdash\colon\ldotp (x).\phi x\supset\psi x:(x).\psi x\supset\chi x:\supset.(x).\phi x\supset\chi x\) -/
theorem pm10_3 {φ ψ χ : α → Prop} :
    (∀ x, φ x → ψ x) ∧ (∀ x, ψ x → χ x) → ∀ x, φ x → χ x :=
  fun ⟨h1, h2⟩ x hx => h2 x (h1 x hx)

/-- ✱10·301. \(\vdash\colon\ldotp (x).\phi x\equiv\psi x:(x).\psi x\equiv\chi x:\supset.(x).\phi x\equiv\chi x\) -/
theorem pm10_301 {φ ψ χ : α → Prop} :
    (∀ x, φ x ↔ ψ x) ∧ (∀ x, ψ x ↔ χ x) → ∀ x, φ x ↔ χ x :=
  fun ⟨h1, h2⟩ x => (h1 x).trans (h2 x)

/-- ✱10·31. \(\vdash\colon\ldotp (x).\phi x\supset\psi x.\supset:(x):\phi x.\chi x.\supset.\psi x.\chi x\) -/
theorem pm10_31 {φ ψ χ : α → Prop} :
    (∀ x, φ x → ψ x) → ∀ x, φ x ∧ χ x → ψ x ∧ χ x :=
  fun h x ⟨h1, h2⟩ => ⟨h x h1, h2⟩

/-- ✱10·311. \(\vdash\colon\ldotp (x).\phi x\equiv\psi x.\supset:(x)\phi x.\chi x.\equiv.\psi x.\chi x\) -/
theorem pm10_311 {φ ψ χ : α → Prop} :
    (∀ x, φ x ↔ ψ x) → ∀ x, (φ x ∧ χ x ↔ ψ x ∧ χ x) :=
  fun h x => ⟨fun ⟨h1, h2⟩ => ⟨(h x).1 h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(h x).2 h1, h2⟩⟩

/-- ✱10·32. \(\vdash:\phi x\equiv_{x}\psi x.\equiv.\psi x\equiv_{x}\phi x\) -/
theorem pm10_32 {φ ψ : α → Prop} : (∀ x, φ x ↔ ψ x) ↔ ∀ x, ψ x ↔ φ x :=
  ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩

/-- ✱10·321. \(\vdash:\phi x\equiv_{x}\psi x.\phi x\equiv_{x}\chi x.\supset.\psi x\equiv_{x}\chi x\) -/
theorem pm10_321 {φ ψ χ : α → Prop} :
    (∀ x, φ x ↔ ψ x) ∧ (∀ x, φ x ↔ χ x) → ∀ x, ψ x ↔ χ x :=
  fun ⟨h1, h2⟩ x => (h1 x).symm.trans (h2 x)

/-- ✱10·322. \(\vdash:\psi x\equiv_{x}\phi x.\chi x\equiv_{x}\phi x.\supset.\psi x\equiv_{x}\chi x\) -/
theorem pm10_322 {φ ψ χ : α → Prop} :
    (∀ x, ψ x ↔ φ x) ∧ (∀ x, χ x ↔ φ x) → ∀ x, ψ x ↔ χ x :=
  fun ⟨h1, h2⟩ x => (h1 x).trans (h2 x).symm

/-- ✱10·33. \(\vdash\colon\ldotp (x):\phi x.p:\equiv:(x).\phi x:p\)

**Status.** proved (reading): with `[Nonempty α]`: PM assumes every type has a member
(Introduction, Ch. I); for an empty `α` and a false `p` the left side holds and the right fails. -/
theorem pm10_33 [Nonempty α] {p : Prop} {φ : α → Prop} :
    (∀ x, φ x ∧ p) ↔ (∀ x, φ x) ∧ p :=
  ⟨fun h => ⟨fun x => (h x).1, (h (Classical.arbitrary α)).2⟩, fun h x => ⟨h.1 x, h.2⟩⟩

/-- ✱10·34. \(\vdash\colon\ldotp (\exists x).\phi x\supset p.\equiv:(x).\phi x.\supset.p\)

**Status.** proved (reading): with `[Nonempty α]`: PM assumes every type has a member
(Introduction, Ch. I); for an empty `α` and a true `p` the right side holds and the left fails. -/
theorem pm10_34 [Nonempty α] {p : Prop} {φ : α → Prop} :
    (∃ x, φ x → p) ↔ ((∀ x, φ x) → p) := by
  constructor
  · rintro ⟨x, hx⟩ h
    exact hx (h x)
  · intro h
    by_cases hp : p
    · exact ⟨Classical.arbitrary α, fun _ => hp⟩
    · obtain ⟨x, hx⟩ := pm9_01.1 fun h' => hp (h h')
      exact ⟨x, fun h' => absurd h' hx⟩

/-- ✱10·35. \(\vdash\colon\ldotp (\exists x).p.\phi x.\equiv:p:(\exists x).\phi x\) -/
theorem pm10_35 {p : Prop} {φ : α → Prop} : (∃ x, p ∧ φ x) ↔ p ∧ ∃ x, φ x :=
  ⟨fun ⟨x, hp, hx⟩ => ⟨hp, x, hx⟩, fun ⟨hp, x, hx⟩ => ⟨x, hp, hx⟩⟩

/-- ✱10·36. \(\vdash\colon\ldotp (\exists x).\phi x\lor p.\equiv:(\exists x).\phi x.\lor .p\)

**Status.** proved (reading): with `[Nonempty α]`: PM assumes every type has a member
(Introduction, Ch. I); for an empty `α` and a true `p` the right side holds and the left fails. -/
theorem pm10_36 [Nonempty α] {p : Prop} {φ : α → Prop} :
    (∃ x, φ x ∨ p) ↔ (∃ x, φ x) ∨ p :=
  pm9_05.symm

/-- ✱10·37. \(\vdash\colon\ldotp (\exists x).p\supset\phi x.\equiv:p.\supset.(\exists x).\phi x \quad\left[\text{*10·36}\, \frac{{\sim}p}{p}\right]\)

**Status.** proved (reading): with `[Nonempty α]`: PM assumes every type has a member
(Introduction, Ch. I); for an empty `α` and a false `p` the right side holds and the left fails. -/
theorem pm10_37 [Nonempty α] {p : Prop} {φ : α → Prop} :
    (∃ x, p → φ x) ↔ (p → ∃ x, φ x) := by
  constructor
  · rintro ⟨x, hx⟩ hp
    exact ⟨x, hx hp⟩
  · intro h
    by_cases hp : p
    · obtain ⟨x, hx⟩ := h hp
      exact ⟨x, fun _ => hx⟩
    · exact ⟨Classical.arbitrary α, fun h' => absurd h' hp⟩

/-- ✱10·39. \(\vdash\colon\ldotp \phi x\supset_{x}\chi x:\psi x\supset_{x}\theta x:\supset:\phi x.\psi x.\supset_{x}.\chi x.\theta x\) -/
theorem pm10_39 {φ ψ χ θ : α → Prop} :
    (∀ x, φ x → χ x) ∧ (∀ x, ψ x → θ x) → ∀ x, φ x ∧ ψ x → χ x ∧ θ x :=
  fun ⟨h1, h2⟩ x ⟨a, b⟩ => ⟨h1 x a, h2 x b⟩

/-- ✱10·4. \(\vdash\colon\ldotp \phi x\equiv_{x}\chi x.\psi x\equiv_{x}\theta x.\supset:\phi x.\psi x.\equiv_{x}.\chi x.\theta x\) -/
theorem pm10_4 {φ ψ χ θ : α → Prop} :
    (∀ x, φ x ↔ χ x) ∧ (∀ x, ψ x ↔ θ x) → ∀ x, (φ x ∧ ψ x ↔ χ x ∧ θ x) :=
  fun ⟨h1, h2⟩ x => and_congr (h1 x) (h2 x)

/-- ✱10·41. \(\vdash\colon\ldotp (x).\phi x.\lor .(x).\psi x:\supset.(x).\phi x\lor \psi x\) -/
theorem pm10_41 {φ ψ : α → Prop} : (∀ x, φ x) ∨ (∀ x, ψ x) → ∀ x, φ x ∨ ψ x :=
  fun h x => h.elim (fun h => Or.inl (h x)) (fun h => Or.inr (h x))

/-- ✱10·411. \(\vdash\colon\ldotp \phi x\equiv_{x}\chi x.\psi x\equiv_{x}\theta x.\supset:\phi x\lor \psi x.\equiv_{x}.\chi x\lor \theta x\) -/
theorem pm10_411 {φ ψ χ θ : α → Prop} :
    (∀ x, φ x ↔ χ x) ∧ (∀ x, ψ x ↔ θ x) → ∀ x, (φ x ∨ ψ x ↔ χ x ∨ θ x) :=
  fun ⟨h1, h2⟩ x => or_congr (h1 x) (h2 x)

/-- ✱10·412. \(\vdash:\phi x\equiv_{x}\psi x.\equiv.{\sim}\phi x\equiv_{x}{\sim}\psi x \quad[\text{*4·11.*10·11·271}]\) -/
theorem pm10_412 {φ ψ : α → Prop} : (∀ x, φ x ↔ ψ x) ↔ ∀ x, (¬φ x ↔ ¬ψ x) :=
  ⟨fun h x => not_congr (h x), fun h x => not_iff_not.mp (h x)⟩

/-- ✱10·413. \(\vdash\colon\ldotp \phi x\equiv_{x}\chi x.\psi x\equiv_{x}\theta x.\supset:\phi x\supset\psi x.\equiv_{x}.\chi x\supset\theta x\) -/
theorem pm10_413 {φ ψ χ θ : α → Prop} :
    (∀ x, φ x ↔ χ x) ∧ (∀ x, ψ x ↔ θ x) → ∀ x, ((φ x → ψ x) ↔ (χ x → θ x)) :=
  fun ⟨h1, h2⟩ x => imp_congr (h1 x) (h2 x)

/-- ✱10·414. \(\vdash\colon\ldotp \phi x\equiv_{x}\chi x.\psi x\equiv_{x}\theta x.\supset:\phi x\equiv\psi x.\equiv_{x}.\chi x\equiv\theta x\) -/
theorem pm10_414 {φ ψ χ θ : α → Prop} :
    (∀ x, φ x ↔ χ x) ∧ (∀ x, ψ x ↔ θ x) → ∀ x, ((φ x ↔ ψ x) ↔ (χ x ↔ θ x)) :=
  fun ⟨h1, h2⟩ x => iff_congr (h1 x) (h2 x)

/-- ✱10·42. \(\vdash\colon\ldotp (\exists x).\phi x.\lor .(\exists x).\psi x:\equiv.(\exists x).\phi x\lor \psi x\) -/
theorem pm10_42 {φ ψ : α → Prop} : (∃ x, φ x) ∨ (∃ x, ψ x) ↔ ∃ x, φ x ∨ ψ x :=
  ⟨fun h => h.elim (fun ⟨x, hx⟩ => ⟨x, Or.inl hx⟩) (fun ⟨x, hx⟩ => ⟨x, Or.inr hx⟩),
    fun ⟨x, hx⟩ => hx.elim (fun h => Or.inl ⟨x, h⟩) (fun h => Or.inr ⟨x, h⟩)⟩

/-- ✱10·43. \(\vdash : \phi z \equiv_{z} \psi z . \phi x . \equiv . \phi z \equiv_{z} \psi z . \psi x\) -/
theorem pm10_43 {φ ψ : α → Prop} {x : α} :
    (∀ z, φ z ↔ ψ z) ∧ φ x ↔ (∀ z, φ z ↔ ψ z) ∧ ψ x :=
  ⟨fun ⟨h, hx⟩ => ⟨h, (h x).1 hx⟩, fun ⟨h, hx⟩ => ⟨h, (h x).2 hx⟩⟩

/-- ✱10·5. \(\vdash \colon\ldotp (\exists x) . \phi x . \psi x . \supset : (\exists x) . \phi x : (\exists x) . \psi x\) -/
theorem pm10_5 {φ ψ : α → Prop} : (∃ x, φ x ∧ ψ x) → (∃ x, φ x) ∧ ∃ x, ψ x :=
  fun ⟨x, h1, h2⟩ => ⟨⟨x, h1⟩, ⟨x, h2⟩⟩

/-- ✱10·51. \(\vdash \colon\ldotp {\sim}\{(\exists x) . \phi x . \psi x\} . \equiv : \phi x . \supset_{x} . {\sim}\psi x\) -/
theorem pm10_51 {φ ψ : α → Prop} : ¬(∃ x, φ x ∧ ψ x) ↔ ∀ x, φ x → ¬ψ x :=
  ⟨fun h x h1 h2 => h ⟨x, h1, h2⟩, fun h ⟨x, h1, h2⟩ => h x h1 h2⟩

/-- ✱10·52. \(\vdash \colon\ldotp (\exists x) . \phi x . \supset : (x) . \phi x \supset p . \equiv . p\) -/
theorem pm10_52 {p : Prop} {φ : α → Prop} : (∃ x, φ x) → ((∀ x, φ x → p) ↔ p) :=
  fun ⟨x, hx⟩ => ⟨fun h => h x hx, fun hp _ _ => hp⟩

/-- ✱10·53. \(\vdash \colon\ldotp {\sim}(\exists x) . \phi x . \supset : \phi x . \supset_{x} . \psi x\) -/
theorem pm10_53 {φ ψ : α → Prop} : ¬(∃ x, φ x) → ∀ x, φ x → ψ x :=
  fun h x hx => absurd ⟨x, hx⟩ h

/-- ✱10·541. \(\vdash \colon\colon \phi y . \supset_{y} . p \lor \psi y : \equiv : p . \lor . \phi y \supset_{y} \psi y\) -/
theorem pm10_541 {p : Prop} {φ ψ : α → Prop} :
    (∀ y, φ y → p ∨ ψ y) ↔ p ∨ ∀ y, φ y → ψ y := by
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inl hp
    · exact Or.inr fun y hy => (h y hy).resolve_left hp
  · rintro (hp | h) y hy
    · exact Or.inl hp
    · exact Or.inr (h y hy)

/-- ✱10·542. \(\vdash\colon\ldotp \phi y.\supset_{y}.p\supset\psi y:\equiv:p.\supset.\phi y\supset_{y}\psi y \quad\left[\text{*10·541}\, \frac{{\sim}p}{p}\right]\) -/
theorem pm10_542 {p : Prop} {φ ψ : α → Prop} :
    (∀ y, φ y → (p → ψ y)) ↔ (p → ∀ y, φ y → ψ y) :=
  ⟨fun h hp y hy => h y hy hp, fun h y hy hp => h hp y hy⟩

/-- ✱10·55. \(\vdash\colon\ldotp (\exists x).\phi x.\psi x:\phi x\supset_{x}\psi x:\equiv:(\exists x).\phi x:\phi x\supset_{x}\psi x\) -/
theorem pm10_55 {φ ψ : α → Prop} :
    (∃ x, φ x ∧ ψ x) ∧ (∀ x, φ x → ψ x) ↔ (∃ x, φ x) ∧ ∀ x, φ x → ψ x :=
  ⟨fun ⟨⟨x, h1, _⟩, h⟩ => ⟨⟨x, h1⟩, h⟩, fun ⟨⟨x, h1⟩, h⟩ => ⟨⟨x, h1, h x h1⟩, h⟩⟩

/-- ✱10·56. \(\vdash\colon\ldotp \phi x\supset_{x}.\psi x:(\exists x).\phi x.\chi x:\supset.(\exists x).\psi x.\chi x\) -/
theorem pm10_56 {φ ψ χ : α → Prop} :
    (∀ x, φ x → ψ x) ∧ (∃ x, φ x ∧ χ x) → ∃ x, ψ x ∧ χ x :=
  fun ⟨h, x, h1, h2⟩ => ⟨x, h x h1, h2⟩

/-- ✱10·57. \(\vdash\colon\ldotp \phi x.\supset_{x}.\psi x\lor \chi x:\supset:\phi x\supset_{x}\psi x.\lor .(\exists x).\phi x.\chi x\) -/
theorem pm10_57 {φ ψ χ : α → Prop} :
    (∀ x, φ x → ψ x ∨ χ x) → (∀ x, φ x → ψ x) ∨ ∃ x, φ x ∧ χ x := by
  intro h
  by_cases hc : ∃ x, φ x ∧ χ x
  · exact Or.inr hc
  · refine Or.inl fun x hx => ?_
    rcases h x hx with h1 | h1
    · exact h1
    · exact absurd ⟨x, hx, h1⟩ hc

/-!
## [✱11] Theory of two apparent variables

*(Vol. 1, p. 157)*

> *Summary of* *11.
>
> In this number, the propositions proved for one variable in *10 are to be extended to two variables, with the addition of a few propositions having no analogues for one variable, such as *11·2·21·23·24 and *11·53·55·6·7. "\(\phi(x,y)\)" stands for a proposition containing \(x\) and containing \(y\); when \(x\) and \(y\) are unassigned, \(\phi(x,y)\) is a propositional function of \(x\) and \(y\). The definition *11·01 shows that "the truth of all values of \(\phi(x,y)\)" does not need to be taken as a new primitive idea, but is definable in terms of "the truth of all values of \(\psi x\)." The reason is that, when \(x\) is assigned, \(\phi(x,y)\) becomes a function of one variable, namely \(y\), whence it follows that, for every possible value of \(x\), "(\(y).\phi(x,y)\)" embodies merely the primitive idea introduced in *9. But "(\(y).\phi(x,y)\)" is again only a function of one variable, namely \(x\), since \(y\) has here become an apparent variable. Hence the definition *11·01 below is legitimate. We put:
>
> *11·01. (\(x,y).\phi(x,y).=:(x):(y).\phi(x,y) \quad \text{Df}\)
>
> *11·02. (\(x,y,z).\phi(x,y,z).=:(x):(y,z).\phi(x,y,z) \quad \text{Df}\)
>
> …

**Lean reading.** Functions of two (three) variables are curried, `φ(x, y)` is `φ x y` with
`φ : α → β → Prop` (the variables may be of different types); `(x, y)` and `(∃x, y)` are Lean's
`∀ x y` and `∃ x y`, which *are* `∀ x, ∀ y` and `∃ x, ∃ y`, so the Dfs ✱11·01–✱11·04 hold by
`Iff.rfl` and `⊃_{x,y}`, `≡_{x,y}` (✱11·05·06) are `FImp2`, `FEqv2`, written out with `∀`. The
primitive proposition ✱11·07 (interchange of apparent variables) and the rules ✱11·11, ✱11·13,
✱11·311 are recorded as derivable rules. Where a proposition is false for an empty type (✱11·43,
✱11·46, ✱11·47, ✱11·56), `[Nonempty α] [Nonempty β]` make PM's assumption that every type has a
member explicit. ✱11·521 and ✱11·53 are numbered `*11.521`, `*11.53` in the e-text and are
missing from `data/principia.json`; they are formalized here from the source.

**Status.** proved (all propositions; ✱11·07, ✱11·11, ✱11·13, ✱11·311, ✱11·39, ✱11·43, ✱11·46,
✱11·47, ✱11·56 proved (reading); ✱11·01–✱11·06 definition)
-/

/-- ✱11·01 (Df). (\(x,y).\phi(x,y).=:(x):(y).\phi(x,y) \quad\text{Df}\) -/
theorem pm11_01 {φ : α → β → Prop} : (∀ x y, φ x y) ↔ ∀ x, ∀ y, φ x y := Iff.rfl

/-- ✱11·02 (Df). (\(x,y,z).\phi(x,y,z).=:(x):(y,z).\phi(x,y,z) \quad\text{Df}\) -/
theorem pm11_02 {φ : α → β → γ → Prop} : (∀ x y z, φ x y z) ↔ ∀ x, ∀ y z, φ x y z := Iff.rfl

/-- ✱11·03 (Df). (\(\exists x,y).\phi(x,y).=:(\exists x):(\exists y).\phi(x,y) \quad\text{Df}\) -/
theorem pm11_03 {φ : α → β → Prop} : (∃ x y, φ x y) ↔ ∃ x, ∃ y, φ x y := Iff.rfl

/-- ✱11·04 (Df). (\(\exists x,y,z).\phi(x,y,z).=:(\exists x):(\exists y,z).\phi(x,y,z) \quad\text{Df}\) -/
theorem pm11_04 {φ : α → β → γ → Prop} : (∃ x y z, φ x y z) ↔ ∃ x, ∃ y z, φ x y z := Iff.rfl

/-- ✱11·05 (Df). \(\phi(x,y).\supset_{x,y}.\psi(x,y):=:(x,y):\phi(x,y).\supset.\psi(x,y) \quad\text{Df}\) -/
theorem pm11_05 {φ ψ : α → β → Prop} : FImp2 φ ψ ↔ ∀ x y, φ x y → ψ x y := Iff.rfl

/-- ✱11·06 (Df). \(\phi(x,y).\equiv_{x,y}.\psi(x,y):=:(x,y):\phi(x,y).\equiv.\psi(x,y) \quad\text{Df}\) -/
theorem pm11_06 {φ ψ : α → β → Prop} : FEqv2 φ ψ ↔ ∀ x y, φ x y ↔ ψ x y := Iff.rfl

/-- ✱11·07 (Pp). "Whatever possible argument \(x\) may be, \(\phi(x,y)\) is true whatever possible argument \(y\) may be" implies the corresponding statement with \(x\) and \(y\) interchanged. Pp.

**Status.** proved (reading): a primitive proposition stated in words (the interchange of two
apparent variables); in Lean it is a theorem, `(x) : (y) . φ(x, y)` implies `(y) : (x) . φ(x, y)`. -/
theorem pm11_07 {φ : α → β → Prop} : (∀ x, ∀ y, φ x y) → ∀ y, ∀ x, φ x y :=
  fun h y x => h x y

/-- ✱11·1. \(\vdash:(x,y).\phi(x,y).\supset.\phi(z,w)\) -/
theorem pm11_1 {φ : α → β → Prop} {z : α} {w : β} : (∀ x y, φ x y) → φ z w := fun h => h z w

/-- ✱11·11. If \(\phi(x,y)\) is true whatever possible arguments \(z\) and \(w\) may be, then (\(x,y).\phi(x,y)\) is true.

**Status.** proved (reading): a rule of inference (meta-level, from ✱10·11): a proof of `φ(z, w)`
for arbitrary `z`, `w` is a proof of `∀ z w, φ z w`, which gives `(x, y).φ(x, y)`. -/
theorem pm11_11 {φ : α → β → Prop} (h : ∀ z w, φ z w) : ∀ x y, φ x y := h

/-- ✱11·12. \(\vdash\colon\ldotp(x,y).p\lor\phi(x,y).\supset:p.\lor.(x,y).\phi(x,y)\) -/
theorem pm11_12 {p : Prop} {φ : α → β → Prop} : (∀ x y, p ∨ φ x y) → p ∨ ∀ x y, φ x y := by
  intro h
  by_cases hp : p
  · exact Or.inl hp
  · exact Or.inr fun x y => (h x y).resolve_left hp

/-- ✱11·13. If \(\phi(\hat{x},\hat{y})\), \(\psi(\hat{x},\hat{y})\) take their first and second arguments respectively of the same type, and we have "\(\vdash.\phi(x,y)\)" and "\(\vdash.\psi(x,y)\)," we shall have "\(\vdash.\phi(x,y).\psi(x,y)\)." [Proof as in *10·13]

**Status.** proved (reading): a rule of inference (meta-level, as ✱10·13): from proofs of
`∀ x y, φ x y` and `∀ x y, ψ x y` (the first and second arguments ranging over the same types
`α`, `β`) follows `∀ x y, φ x y ∧ ψ x y`. -/
theorem pm11_13 {φ ψ : α → β → Prop} (hφ : ∀ x y, φ x y) (hψ : ∀ x y, ψ x y) :
    ∀ x y, φ x y ∧ ψ x y :=
  fun x y => ⟨hφ x y, hψ x y⟩

/-- ✱11·14. \(\vdash\colon\ldotp(x,y).\phi(x,y):(x,y).\psi(x,y):\supset:\phi(z,w).\psi(z,w)\) -/
theorem pm11_14 {φ ψ : α → β → Prop} {z : α} {w : β} :
    (∀ x y, φ x y) ∧ (∀ x y, ψ x y) → φ z w ∧ ψ z w :=
  fun ⟨h1, h2⟩ => ⟨h1 z w, h2 z w⟩

/-- ✱11·2. \(\vdash:(x,y).\phi(x,y).\equiv.(y,x).\phi(x,y)\) -/
theorem pm11_2 {φ : α → β → Prop} : (∀ x y, φ x y) ↔ ∀ y x, φ x y :=
  ⟨fun h y x => h x y, fun h x y => h y x⟩

/-- ✱11·21. \(\vdash:(x,y,z).\phi(x,y,z).\equiv.(y,z,x).\phi(x,y,z)\) -/
theorem pm11_21 {φ : α → β → γ → Prop} : (∀ x y z, φ x y z) ↔ ∀ y z x, φ x y z :=
  ⟨fun h y z x => h x y z, fun h x y z => h y z x⟩

/-- ✱11·22. \(\vdash:(\exists x,y).\phi(x,y).\equiv.{\sim}\{(x,y).{\sim}\phi(x,y)\}\) -/
theorem pm11_22 {φ : α → β → Prop} : (∃ x y, φ x y) ↔ ¬ ∀ x y, ¬φ x y :=
  ⟨fun ⟨x, y, h⟩ h' => h' x y h,
    fun h => Classical.byContradiction fun h' => h fun x y hxy => h' ⟨x, y, hxy⟩⟩

/-- ✱11·23. \(\vdash:(\exists x,y).\phi(x,y).\equiv.(\exists y,x).\phi(x,y)\) -/
theorem pm11_23 {φ : α → β → Prop} : (∃ x y, φ x y) ↔ ∃ y x, φ x y :=
  ⟨fun ⟨x, y, h⟩ => ⟨y, x, h⟩, fun ⟨y, x, h⟩ => ⟨x, y, h⟩⟩

/-- ✱11·24. \(\vdash:(\exists x,y,z).\phi(x,y,z).\equiv.(\exists y,z,x).\phi(x,y,z)\) -/
theorem pm11_24 {φ : α → β → γ → Prop} : (∃ x y z, φ x y z) ↔ ∃ y z x, φ x y z :=
  ⟨fun ⟨x, y, z, h⟩ => ⟨y, z, x, h⟩, fun ⟨y, z, x, h⟩ => ⟨x, y, z, h⟩⟩

/-- ✱11·25. \(\vdash:{\sim}\{(\exists x,y).\phi(x,y)\}.\equiv.(x,y).{\sim}\phi(x,y) \quad[\text{*11·22.Transp}]\) -/
theorem pm11_25 {φ : α → β → Prop} : ¬(∃ x y, φ x y) ↔ ∀ x y, ¬φ x y :=
  ⟨fun h x y hxy => h ⟨x, y, hxy⟩, fun h ⟨x, y, hxy⟩ => h x y hxy⟩

/-- ✱11·26. \(\vdash\colon\ldotp(\exists x):(y).\phi(x,y):\supset:(y):(\exists x).\phi(x,y)\) -/
theorem pm11_26 {φ : α → β → Prop} : (∃ x, ∀ y, φ x y) → ∀ y, ∃ x, φ x y :=
  fun ⟨x, h⟩ y => ⟨x, h y⟩

/-- ✱11·27. \[\begin{align}\vdash\colon\ldotp(\exists x,y):(\exists z).\phi(x,y,z):&\equiv:(\exists x):(\exists y,z).\phi(x,y,z):\\ &\equiv:(\exists x,y,z).\phi(x,y,z)\end{align}\] -/
theorem pm11_27 {φ : α → β → γ → Prop} :
    ((∃ x y, ∃ z, φ x y z) ↔ ∃ x, ∃ y z, φ x y z) ∧
      ((∃ x, ∃ y z, φ x y z) ↔ ∃ x y z, φ x y z) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ✱11·3. \(\vdash\colon\ldotp p.\supset.(x,y).\phi(x,y):\equiv:(x,y):p.\supset.\phi(x,y)\) -/
theorem pm11_3 {p : Prop} {φ : α → β → Prop} : (p → ∀ x y, φ x y) ↔ ∀ x y, p → φ x y :=
  ⟨fun h x y hp => h hp x y, fun h hp x y => h x y hp⟩

/-- ✱11·31. \(\vdash\colon\ldotp(x,y).\phi(x,y):(x,y).\psi(x,y):\equiv:(x,y):\phi(x,y).\psi(x,y)\) -/
theorem pm11_31 {φ ψ : α → β → Prop} :
    (∀ x y, φ x y) ∧ (∀ x y, ψ x y) ↔ ∀ x y, φ x y ∧ ψ x y :=
  ⟨fun ⟨h1, h2⟩ x y => ⟨h1 x y, h2 x y⟩,
    fun h => ⟨fun x y => (h x y).1, fun x y => (h x y).2⟩⟩

/-- ✱11·311. If \(\phi(\hat{x},\hat{y})\), \(\psi(\hat{x},\hat{y})\) take arguments of the same type, and we have "\(\vdash.\phi(x,y)\)" and "\(\vdash.\psi(x,y)\)," we shall have "\(\vdash.\phi(x,y).\psi(x,y)\)." [Proof as in *10·13.]

**Status.** proved (reading): a rule of inference (meta-level), as ✱11·13. -/
theorem pm11_311 {φ ψ : α → β → Prop} (hφ : ∀ x y, φ x y) (hψ : ∀ x y, ψ x y) :
    ∀ x y, φ x y ∧ ψ x y :=
  fun x y => ⟨hφ x y, hψ x y⟩

/-- ✱11·32. \(\vdash\colon\ldotp(x,y):\phi(x,y).\supset.\psi(x,y):\supset:(x,y).\phi(x,y).\supset.(x,y).\psi(x,y) \quad[\text{*10·27}]\) -/
theorem pm11_32 {φ ψ : α → β → Prop} :
    (∀ x y, φ x y → ψ x y) → ((∀ x y, φ x y) → ∀ x y, ψ x y) :=
  fun h h' x y => h x y (h' x y)

/-- ✱11·33. \(\vdash\colon\ldotp(x,y):\phi(x,y).\equiv.\psi(x,y):\supset:(x,y).\phi(x,y).\equiv.(x,y).\psi(x,y) \quad[\text{*10·271}]\) -/
theorem pm11_33 {φ ψ : α → β → Prop} :
    (∀ x y, φ x y ↔ ψ x y) → ((∀ x y, φ x y) ↔ ∀ x y, ψ x y) :=
  fun h => ⟨fun h' x y => (h x y).1 (h' x y), fun h' x y => (h x y).2 (h' x y)⟩

/-- ✱11·34. \[\begin{align}\vdash\colon\ldotp(x,y):\phi(x,y).&\supset.\psi(x,y):\supset:\\ &(\exists x,y).\phi(x,y).\supset.(\exists x,y).\psi(x,y) \quad[\text{*10·27·28}]\end{align}\] -/
theorem pm11_34 {φ ψ : α → β → Prop} :
    (∀ x y, φ x y → ψ x y) → ((∃ x y, φ x y) → ∃ x y, ψ x y) :=
  fun h ⟨x, y, hxy⟩ => ⟨x, y, h x y hxy⟩

/-- ✱11·341. \[\begin{align}\vdash\colon\ldotp(x,y):\phi(x,y).&\equiv.\psi(x,y):\supset:\\ &(\exists x,y).\phi(x,y).\equiv.(\exists x,y).\psi(x,y) \quad[\text{*10·271·281}]\end{align}\] -/
theorem pm11_341 {φ ψ : α → β → Prop} :
    (∀ x y, φ x y ↔ ψ x y) → ((∃ x y, φ x y) ↔ ∃ x y, ψ x y) :=
  fun h => ⟨fun ⟨x, y, hxy⟩ => ⟨x, y, (h x y).1 hxy⟩, fun ⟨x, y, hxy⟩ => ⟨x, y, (h x y).2 hxy⟩⟩

/-- ✱11·35. \(\vdash\colon\ldotp(x,y):\phi(x,y).\supset.p:\equiv:(\exists x,y).\phi(x,y).\supset.p \quad[\text{*10·23·271}]\) -/
theorem pm11_35 {p : Prop} {φ : α → β → Prop} :
    (∀ x y, φ x y → p) ↔ ((∃ x y, φ x y) → p) :=
  ⟨fun h ⟨x, y, hxy⟩ => h x y hxy, fun h x y hxy => h ⟨x, y, hxy⟩⟩

/-- ✱11·36. \(\vdash:\phi(z,w).\supset.(\exists x,y).\phi(x,y)\) -/
theorem pm11_36 {φ : α → β → Prop} {z : α} {w : β} : φ z w → ∃ x y, φ x y :=
  fun h => ⟨z, w, h⟩

/-- ✱11·37. \[\begin{align}\vdash\colon\colon(x,y):\phi(x,y).\supset.\psi(x,y)&\colon\ldotp(x,y):\psi(x,y).\supset.\chi(x,y)\colon\ldotp\\ &\supset:(x,y):\phi(x,y).\supset.\chi(x,y)\end{align}\] -/
theorem pm11_37 {φ ψ χ : α → β → Prop} :
    (∀ x y, φ x y → ψ x y) ∧ (∀ x y, ψ x y → χ x y) → ∀ x y, φ x y → χ x y :=
  fun ⟨h1, h2⟩ x y h => h2 x y (h1 x y h)

/-- ✱11·371. \[\begin{align}\vdash\colon\colon(x,y):\phi(x,y).&\equiv.\psi(x,y)\colon\ldotp(x,y):\psi(x,y).\equiv.\chi(x,y)\colon\ldotp\\ &\supset\colon\ldotp(x,y):\phi(x,y).\equiv.\chi(x,y) \quad[\text{*11·31·11·33}]\end{align}\] -/
theorem pm11_371 {φ ψ χ : α → β → Prop} :
    (∀ x y, φ x y ↔ ψ x y) ∧ (∀ x y, ψ x y ↔ χ x y) → ∀ x y, φ x y ↔ χ x y :=
  fun ⟨h1, h2⟩ x y => (h1 x y).trans (h2 x y)

/-- ✱11·38. \[\begin{align}\vdash\colon\colon&(x,y):\phi(x,y).\supset.\psi(x,y)\colon\ldotp\supset\colon\ldotp\\ &(x,y):\phi(x,y).\chi(x,y).\supset.\psi(x,y).\chi(x,y) \quad[\text{Fact.*11·11·32}]\end{align}\] -/
theorem pm11_38 {φ ψ χ : α → β → Prop} :
    (∀ x y, φ x y → ψ x y) → ∀ x y, φ x y ∧ χ x y → ψ x y ∧ χ x y :=
  fun h x y ⟨h1, h2⟩ => ⟨h x y h1, h2⟩

/-- ✱11·39. \[\begin{align}\vdash\colon\colon&(x,y):\phi(x,y).\supset.\psi(x,y)\colon\ldotp(x,y):\chi(x,y).\supset.\theta(x,y)\colon\ldotp\supset\colon\ldotp\\ &(x,y):\phi(x,y).\chi(x,y).\supset.\psi(x,y).\theta(x,y)) \quad[\text{*3·47.*11·11·32}]\end{align}\]

**Status.** proved (reading): transcription error of the e-text, a stray closing bracket after
`θ(x, y)`, which is dropped (the formula is otherwise PM's, as the proof `*3·47.*11·11·32` shows). -/
theorem pm11_39 {φ ψ χ θ : α → β → Prop} :
    (∀ x y, φ x y → ψ x y) ∧ (∀ x y, χ x y → θ x y) →
      ∀ x y, φ x y ∧ χ x y → ψ x y ∧ θ x y :=
  fun ⟨h1, h2⟩ x y ⟨a, b⟩ => ⟨h1 x y a, h2 x y b⟩

/-- ✱11·391. \[\begin{align}\vdash\colon\colon(x,y):\phi(x,y).\supset.&\psi(x,y)\colon\ldotp(x,y):\phi(x,y).\supset.\chi(x,y)\colon\ldotp\\ &\equiv:(x,y):\phi(x,y).\supset.\psi(x,y).\chi(x,y)\end{align}\] -/
theorem pm11_391 {φ ψ χ : α → β → Prop} :
    (∀ x y, φ x y → ψ x y) ∧ (∀ x y, φ x y → χ x y) ↔ ∀ x y, φ x y → ψ x y ∧ χ x y :=
  ⟨fun ⟨h1, h2⟩ x y h => ⟨h1 x y h, h2 x y h⟩,
    fun h => ⟨fun x y hh => (h x y hh).1, fun x y hh => (h x y hh).2⟩⟩

/-- ✱11·4. \[\begin{align}\vdash\colon\colon&(x,y):\phi(x,y).\equiv.\psi(x,y)\colon\ldotp(x,y):\chi(x,y).\equiv.\theta(x,y)\colon\ldotp\supset\colon\ldotp\\ &(x,y):\phi(x,y).\chi(x,y).\equiv.\psi(x,y).\theta(x,y)\end{align}\] -/
theorem pm11_4 {φ ψ χ θ : α → β → Prop} :
    (∀ x y, φ x y ↔ ψ x y) ∧ (∀ x y, χ x y ↔ θ x y) →
      ∀ x y, (φ x y ∧ χ x y ↔ ψ x y ∧ θ x y) :=
  fun ⟨h1, h2⟩ x y => and_congr (h1 x y) (h2 x y)

/-- ✱11·401. \[\begin{align}\vdash\colon\colon&(x,y):\phi(x,y).\equiv.\psi(x,y):\supset\colon\ldotp\\ &(x,y):\phi(x,y).\chi(x,y).\equiv.\psi(x,y).\chi(x,y) \quad\left[\text{*11·4}\, \frac{\chi}{\theta}.\text{Id}\right]\end{align}\] -/
theorem pm11_401 {φ ψ χ : α → β → Prop} :
    (∀ x y, φ x y ↔ ψ x y) → ∀ x y, (φ x y ∧ χ x y ↔ ψ x y ∧ χ x y) :=
  fun h x y => and_congr (h x y) Iff.rfl

/-- ✱11·41. \[\begin{align}\vdash\colon\ldotp(\exists x,y).\phi(x,y)&:\lor:(\exists x,y).\psi(x,y):\\ &\equiv:(\exists x,y):\phi(x,y).\lor.\psi(x,y) \quad[\text{*10·42·281}]\end{align}\] -/
theorem pm11_41 {φ ψ : α → β → Prop} :
    (∃ x y, φ x y) ∨ (∃ x y, ψ x y) ↔ ∃ x y, φ x y ∨ ψ x y :=
  ⟨fun h => h.elim (fun ⟨x, y, h⟩ => ⟨x, y, Or.inl h⟩) (fun ⟨x, y, h⟩ => ⟨x, y, Or.inr h⟩),
    fun ⟨x, y, h⟩ => h.elim (fun h => Or.inl ⟨x, y, h⟩) (fun h => Or.inr ⟨x, y, h⟩)⟩

/-- ✱11·42. \(\vdash\colon\ldotp(\exists x,y).\phi(x,y).\psi(x,y).\supset:(\exists x,y).\phi(x,y):(\exists x,y).\psi(x,y) \quad[\text{*10·5}]\) -/
theorem pm11_42 {φ ψ : α → β → Prop} :
    (∃ x y, φ x y ∧ ψ x y) → (∃ x y, φ x y) ∧ ∃ x y, ψ x y :=
  fun ⟨x, y, h1, h2⟩ => ⟨⟨x, y, h1⟩, x, y, h2⟩

/-- ✱11·421. \[\begin{align}\vdash\colon\ldotp(x,y).\phi(x,y).\lor.(x,y).&\psi(x,y):\supset:(x,y):\phi(x,y).\lor.\psi(x,y)\\ &\left[\text{*11·42}\, \frac{{\sim}\phi,\,{\sim}\psi}{\phi,\,\psi}.\, \text{Transp.*4·56}\right]\end{align}\] -/
theorem pm11_421 {φ ψ : α → β → Prop} :
    (∀ x y, φ x y) ∨ (∀ x y, ψ x y) → ∀ x y, φ x y ∨ ψ x y :=
  fun h x y => h.elim (fun h => Or.inl (h x y)) (fun h => Or.inr (h x y))

/-- ✱11·43. \(\vdash\colon\ldotp(\exists x,y):\phi(x,y).\supset.p:\equiv:(x,y).\phi(x,y).\supset.p \quad[\text{*10·34·281}]\)

**Status.** proved (reading): with `[Nonempty α] [Nonempty β]`: PM assumes every type has a member
(Introduction, Ch. I); for an empty `α` and a true `p` the right side holds and the left fails. -/
theorem pm11_43 [Nonempty α] [Nonempty β] {p : Prop} {φ : α → β → Prop} :
    (∃ x y, φ x y → p) ↔ ((∀ x y, φ x y) → p) := by
  constructor
  · rintro ⟨x, y, h⟩ h'
    exact h (h' x y)
  · intro h
    by_cases hp : p
    · exact ⟨Classical.arbitrary α, Classical.arbitrary β, fun _ => hp⟩
    · obtain ⟨x, hx⟩ := pm9_01.1 fun h' => hp (h h')
      obtain ⟨y, hy⟩ := pm9_01.1 hx
      exact ⟨x, y, fun h' => absurd h' hy⟩

/-- ✱11·44. \(\vdash\colon\ldotp(x,y):\phi(x,y).\lor.p:\equiv:(x,y).\phi(x,y).\lor.p \quad[\text{*10·2·271}]\) -/
theorem pm11_44 {p : Prop} {φ : α → β → Prop} :
    (∀ x y, φ x y ∨ p) ↔ (∀ x y, φ x y) ∨ p := by
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inr hp
    · exact Or.inl fun x y => (h x y).resolve_right hp
  · intro h x y
    exact h.elim (fun h => Or.inl (h x y)) Or.inr

/-- ✱11·45. \(\vdash \colon\ldotp (\exists x, y) : p . \phi (x, y) : \equiv : p : (\exists x, y) . \phi(x, y) \quad[\text{*10·35·281}]\) -/
theorem pm11_45 {p : Prop} {φ : α → β → Prop} :
    (∃ x y, p ∧ φ x y) ↔ p ∧ ∃ x y, φ x y :=
  ⟨fun ⟨x, y, hp, h⟩ => ⟨hp, x, y, h⟩, fun ⟨hp, x, y, h⟩ => ⟨x, y, hp, h⟩⟩

/-- ✱11·46. \(\vdash \colon\ldotp (\exists x, y) : p . \supset . \phi (x, y) : \equiv : p . \supset . (\exists x, y) . \phi(x, y) \quad[\text{*10·37·281}]\)

**Status.** proved (reading): with `[Nonempty α] [Nonempty β]`: PM assumes every type has a member
(Introduction, Ch. I); for an empty `α` and a false `p` the right side holds and the left fails. -/
theorem pm11_46 [Nonempty α] [Nonempty β] {p : Prop} {φ : α → β → Prop} :
    (∃ x y, p → φ x y) ↔ (p → ∃ x y, φ x y) := by
  constructor
  · rintro ⟨x, y, h⟩ hp
    exact ⟨x, y, h hp⟩
  · intro h
    by_cases hp : p
    · obtain ⟨x, y, hxy⟩ := h hp
      exact ⟨x, y, fun _ => hxy⟩
    · exact ⟨Classical.arbitrary α, Classical.arbitrary β, fun h' => absurd h' hp⟩

/-- ✱11·47. \(\vdash \colon\ldotp (x, y) : p . \phi(x, y) : \equiv : p : (x, y) . \phi(x, y) \quad[\text{*10·33·271}]\)

**Status.** proved (reading): with `[Nonempty α] [Nonempty β]`: PM assumes every type has a member
(Introduction, Ch. I); for an empty `α` and a false `p` the left side holds and the right fails. -/
theorem pm11_47 [Nonempty α] [Nonempty β] {p : Prop} {φ : α → β → Prop} :
    (∀ x y, p ∧ φ x y) ↔ p ∧ ∀ x y, φ x y :=
  ⟨fun h => ⟨(h (Classical.arbitrary α) (Classical.arbitrary β)).1, fun x y => (h x y).2⟩,
    fun ⟨hp, h⟩ x y => ⟨hp, h x y⟩⟩

/-- ✱11·5. \(\vdash \colon\ldotp (\exists x) : {\sim}\{(y) . \phi(x, y)\} : \equiv : {\sim}\{(x, y) . \phi(x, y)\} : \equiv : (\exists x, y) . {\sim}\phi(x, y)\) -/
theorem pm11_5 {φ : α → β → Prop} :
    ((∃ x, ¬ ∀ y, φ x y) ↔ ¬ ∀ x y, φ x y) ∧ (¬(∀ x y, φ x y) ↔ ∃ x y, ¬φ x y) := by
  refine ⟨⟨fun ⟨x, hx⟩ h => hx (h x), fun h => pm9_01.1 h⟩,
    ⟨fun h => ?_, fun ⟨x, y, hxy⟩ h => hxy (h x y)⟩⟩
  obtain ⟨x, hx⟩ := pm9_01.1 h
  obtain ⟨y, hy⟩ := pm9_01.1 hx
  exact ⟨x, y, hy⟩

/-- ✱11·51. \(\vdash \colon\ldotp (\exists x) : (y) . \phi(x, y) : \equiv : {\sim}{(x) : (\exists y) . {\sim}\phi(x, y)}\) -/
theorem pm11_51 {φ : α → β → Prop} : (∃ x, ∀ y, φ x y) ↔ ¬ ∀ x, ∃ y, ¬φ x y := by
  constructor
  · rintro ⟨x, hx⟩ h
    obtain ⟨y, hy⟩ := h x
    exact hy (hx y)
  · intro h
    obtain ⟨x, hx⟩ := pm9_01.1 h
    exact ⟨x, fun y => Classical.byContradiction fun hy => hx ⟨y, hy⟩⟩

/-- ✱11·52. \(\vdash \colon\ldotp (\exists x, y) . \phi(x, y) . \psi(x, y) . \equiv . {\sim}{(x, y) : \phi(x, y) . \supset . {\sim}\psi(x, y)}\) -/
theorem pm11_52 {φ ψ : α → β → Prop} :
    (∃ x y, φ x y ∧ ψ x y) ↔ ¬ ∀ x y, φ x y → ¬ψ x y := by
  constructor
  · rintro ⟨x, y, h1, h2⟩ h
    exact h x y h1 h2
  · intro h
    obtain ⟨x, hx⟩ := pm9_01.1 h
    obtain ⟨y, hy⟩ := pm9_01.1 hx
    exact ⟨x, y, Classical.byContradiction fun h' => hy fun h1 h2 => h' ⟨h1, h2⟩⟩

/-- ✱11·521. \[\begin{align}\vdash \colon\ldotp {\sim}(\exists x,y) . \phi(x, y) . {\sim}\psi(x, y) . &\equiv : (x, y) : \phi(x, y) . \supset . \psi(x, y)\\ &\left[\text{*11·52.Transp}.\, \frac{{\sim}\psi(x,y)}{\psi(x, y)}\right]\end{align}\]

Not in `data/principia.json`: the e-text numbers it `*11.521` (a full stop for the centred dot),
so the extraction missed it; the formula is quoted from the source (Vol. I, p. 164). `∼(∃x, y)`
negates the whole quantified proposition (✱9·021), whose scope extends past the product dots. -/
theorem pm11_521 {φ ψ : α → β → Prop} :
    ¬(∃ x y, φ x y ∧ ¬ψ x y) ↔ ∀ x y, φ x y → ψ x y := by
  constructor
  · intro h x y hxy
    exact Classical.byContradiction fun hn => h ⟨x, y, hxy, hn⟩
  · rintro h ⟨x, y, h1, h2⟩
    exact h2 (h x y h1)

/-- ✱11·53. \(\vdash \colon\ldotp (x, y) . \phi x \supset \psi y . \equiv : (\exists x) . \phi x . \supset . (y) . \psi y\)

Not in `data/principia.json`: the e-text numbers it `*11.53` (a full stop for the centred dot), so
the extraction missed it; the formula is quoted from the source (Vol. I, p. 164). -/
theorem pm11_53 {φ : α → Prop} {ψ : β → Prop} :
    (∀ x y, φ x → ψ y) ↔ ((∃ x, φ x) → ∀ y, ψ y) :=
  ⟨fun h ⟨x, hx⟩ y => h x y hx, fun h x y hx => h ⟨x, hx⟩ y⟩

/-- ✱11·54. \(\vdash \colon\ldotp (\exists x, y) . \phi x . \psi y . \equiv : (\exists x) . \phi x : (\exists y) . \psi y\) -/
theorem pm11_54 {φ : α → Prop} {ψ : β → Prop} :
    (∃ x y, φ x ∧ ψ y) ↔ (∃ x, φ x) ∧ ∃ y, ψ y :=
  ⟨fun ⟨x, y, h1, h2⟩ => ⟨⟨x, h1⟩, y, h2⟩, fun ⟨⟨x, h1⟩, y, h2⟩ => ⟨x, y, h1, h2⟩⟩

/-- ✱11·55. \(\vdash\colon\ldotp(\exists x,y).\phi x.\psi(x,y).\equiv:(\exists x):\phi x:(\exists y).\psi(x,y)\) -/
theorem pm11_55 {φ : α → Prop} {ψ : α → β → Prop} :
    (∃ x y, φ x ∧ ψ x y) ↔ ∃ x, φ x ∧ ∃ y, ψ x y :=
  ⟨fun ⟨x, y, h1, h2⟩ => ⟨x, h1, y, h2⟩, fun ⟨x, h1, y, h2⟩ => ⟨x, y, h1, h2⟩⟩

/-- ✱11·56. \(\vdash\colon\ldotp(x).\phi x:(y).\psi y:\equiv:(x,y).\phi x.\psi y\)

**Status.** proved (reading): with `[Nonempty α] [Nonempty β]`: PM assumes every type has a member
(Introduction, Ch. I); for an empty `α` the right side holds while `(y).ψy` may fail. -/
theorem pm11_56 [Nonempty α] [Nonempty β] {φ : α → Prop} {ψ : β → Prop} :
    (∀ x, φ x) ∧ (∀ y, ψ y) ↔ ∀ x y, φ x ∧ ψ y :=
  ⟨fun ⟨h1, h2⟩ x y => ⟨h1 x, h2 y⟩,
    fun h => ⟨fun x => (h x (Classical.arbitrary β)).1, fun y => (h (Classical.arbitrary α) y).2⟩⟩

/-- ✱11·57. \(\vdash:(x).\phi x.\equiv.(x,y).\phi x.\phi y \quad[\text{*11·56.*4·24}]\) -/
theorem pm11_57 {φ : α → Prop} : (∀ x, φ x) ↔ ∀ x y, φ x ∧ φ y :=
  ⟨fun h x y => ⟨h x, h y⟩, fun h x => (h x x).1⟩

/-- ✱11·58. \(\vdash:(\exists x).\phi x.\equiv.(\exists x,y).\phi x.\phi y \quad[\text{*11·54.*4·24}]\) -/
theorem pm11_58 {φ : α → Prop} : (∃ x, φ x) ↔ ∃ x y, φ x ∧ φ y :=
  ⟨fun ⟨x, hx⟩ => ⟨x, x, hx, hx⟩, fun ⟨x, _, hx, _⟩ => ⟨x, hx⟩⟩

/-- ✱11·59. \(\vdash\colon\ldotp\phi x.\supset_{x}.\psi x:\equiv:\phi x.\phi y.\supset_{x,y}.\psi x.\psi y\) -/
theorem pm11_59 {φ ψ : α → Prop} :
    (∀ x, φ x → ψ x) ↔ ∀ x y, φ x ∧ φ y → ψ x ∧ ψ y :=
  ⟨fun h x y ⟨h1, h2⟩ => ⟨h x h1, h y h2⟩, fun h x hx => (h x x ⟨hx, hx⟩).1⟩

/-- ✱11·6. \(\vdash\colon\colon(\exists x)\colon\ldotp(\exists y).\phi(x,y).\psi y:\chi x\colon\ldotp\equiv\colon\ldotp(\exists y)\colon\ldotp(\exists x).\phi(x,y).\chi x:\psi y\) -/
theorem pm11_6 {φ : α → β → Prop} {ψ : β → Prop} {χ : α → Prop} :
    (∃ x, (∃ y, φ x y ∧ ψ y) ∧ χ x) ↔ ∃ y, (∃ x, φ x y ∧ χ x) ∧ ψ y :=
  ⟨fun ⟨x, ⟨y, h1, h2⟩, h3⟩ => ⟨y, ⟨x, h1, h3⟩, h2⟩,
    fun ⟨y, ⟨x, h1, h3⟩, h2⟩ => ⟨x, ⟨y, h1, h2⟩, h3⟩⟩

/-- ✱11·61. \(\vdash\colon\ldotp(\exists y):\phi x.\supset_{x}.\psi(x,y):\supset:\phi x.\supset_{x}.(\exists y).\psi(x,y)\) -/
theorem pm11_61 {φ : α → Prop} {ψ : α → β → Prop} :
    (∃ y, ∀ x, φ x → ψ x y) → ∀ x, φ x → ∃ y, ψ x y :=
  fun ⟨y, h⟩ x hx => ⟨y, h x hx⟩

/-- ✱11·62. \(\vdash\colon\colon\phi x.\psi(x,y).\supset_{x,y}.\chi(x,y):\equiv\colon\ldotp\phi x.\supset_{x}:\psi(x,y).\supset_{y}.\chi(x,y)\) -/
theorem pm11_62 {φ : α → Prop} {ψ χ : α → β → Prop} :
    (∀ x y, φ x ∧ ψ x y → χ x y) ↔ ∀ x, φ x → ∀ y, ψ x y → χ x y :=
  ⟨fun h x hx y hy => h x y ⟨hx, hy⟩, fun h x y ⟨hx, hy⟩ => h x hx y hy⟩

/-- ✱11·63. \(\vdash\colon\ldotp{\sim}(\exists x,y).\phi(x,y).\supset:\phi(x,y).\supset_{x,y}.\psi(x,y)\) -/
theorem pm11_63 {φ ψ : α → β → Prop} : ¬(∃ x y, φ x y) → ∀ x y, φ x y → ψ x y :=
  fun h x y hxy => absurd ⟨x, y, hxy⟩ h

/-- ✱11·7. \(\vdash\colon\ldotp(\exists x,y):\phi(x,y).\lor.\phi(y,x):\equiv.(\exists x,y).\phi(x,y)\) -/
theorem pm11_7 {φ : α → α → Prop} : (∃ x y, φ x y ∨ φ y x) ↔ ∃ x y, φ x y :=
  ⟨fun ⟨x, y, h⟩ => h.elim (fun h => ⟨x, y, h⟩) (fun h => ⟨y, x, h⟩),
    fun ⟨x, y, h⟩ => ⟨x, y, Or.inl h⟩⟩

/-- ✱11·71. \[\begin{align}\vdash\colon\colon(\exists z).\phi z:&(\exists w).\chi w:\supset\colon\ldotp\\ &\phi z.\supset_{z}.\psi z:\chi w.\supset_{w}.\theta w:\equiv:\phi z.\chi w.\supset_{z,w}.\psi z.\theta w\end{align}\] -/
theorem pm11_71 {φ ψ : α → Prop} {χ θ : β → Prop} :
    (∃ z, φ z) ∧ (∃ w, χ w) →
      ((∀ z, φ z → ψ z) ∧ (∀ w, χ w → θ w) ↔ ∀ z w, φ z ∧ χ w → ψ z ∧ θ w) :=
  fun ⟨⟨z0, hz0⟩, ⟨w0, hw0⟩⟩ =>
    ⟨fun ⟨h1, h2⟩ z w ⟨a, b⟩ => ⟨h1 z a, h2 w b⟩,
      fun h => ⟨fun z hz => (h z w0 ⟨hz, hw0⟩).1, fun w hw => (h z0 w ⟨hz0, hw⟩).2⟩⟩

/-!
## [✱12] The hierarchy of types and the axiom of reducibility

*(Vol. 1, p. 168)*

> The primitive idea "\((x).{\phi}x\)" has been explained to mean "\({\phi}x\) is always true," *i.e.* "all values of \({\phi}x\) are true." But whatever function \(\phi\) may be, there will be arguments \(x\) with which \({\phi}x\) is meaningless, *i.e.* with which as arguments \(\phi\) does not have any value. The arguments with which \({\phi}x\) has values form what we will call the "range of significance" of \({\phi}x\). A "*type*" is defined as the range of significance of some function. In virtue of *9·14, if \({\phi}x\), \({\phi}y\), and \({\psi}x\) are significant, *i.e.* either true or false, so is \({\psi}y\). From this it follows that two types which have a common member coincide, and that two different types are mutually exclusive. Any proposition of the form \((x).{\phi}x\), *i.e.* any proposition containing an apparent variable, determines some type as the range of the apparent variable, the type being fixed by the function \(\phi\).
>
> …

**Lean reading.** ✱12 introduces the hierarchy of orders and predicative functions `φ!x`. Lean's
`α → Prop` is one type for all functions with arguments in `α` (`Prop` is impredicative), so every
function is predicative: `φ!x` is `φ x` and `(∃f)` over predicative functions is
`∃ f : α → Prop` (Basic §4). The axiom of reducibility ✱12·1, ✱12·11 then becomes provable
(take `f := φ`); the distinction of orders it bridges has no Lean counterpart.

**Status.** proved (reading) (both propositions: every Lean function is predicative)
-/

/-- ✱12·1 (Pp). \(\vdash:(\exists f):\phi x.\equiv_{x}.f!x\quad\text{Pp}\)

**Status.** proved (reading): every Lean function is predicative (Basic §4), so the axiom of
reducibility holds with `f := φ`. -/
theorem pm12_1 {φ : α → Prop} : ∃ f : α → Prop, ∀ x, φ x ↔ f x := reducibility φ

/-- ✱12·11 (Pp). \(\vdash:(\exists f):\phi(x,y).\equiv_{x,y}.f!(x,y)\quad\text{Pp}\)

**Status.** proved (reading): as ✱12·1, for functions of two variables. -/
theorem pm12_11 {φ : α → β → Prop} : ∃ f : α → β → Prop, ∀ x y, φ x y ↔ f x y :=
  reducibility₂ φ

/-!
## [✱13] Identity

*(Vol. 1, p. 176)*

> *Summary of* *13.
>
> The propositional function "\(x\) is identical with \(y\)" will be written "\(x = y\)." We shall find that this use of the sign of equality covers all the common uses of equality that occur in mathematics. The definition is as follows:
>
> *13·01. \(x = y .=: (\phi):{\phi}!x.\supset. {\phi}!y \quad \text{Df}\)
>
> This definition states that \(x\) and \(y\) are to be called identical when every predicative function satisfied by \(x\) is also satisfied by \(y\). We cannot state that *every* function satisfied by \(x\) is to be satisfied by \(y\), because \(x\) satisfies functions of various orders, and these cannot all be covered by one apparent variable. But in virtue of the axiom of reducibility it follows that, if \(x = y\) and \(x\) satisfies \({\psi}x\), where \(\psi\) is any function, predicative or non-predicative, then \(y\) also satisfies \({\psi}y\) (cf. *13·101, below). Hence in effect the definition is as powerful as it would be if it could be extended to cover *all* functions of \(x\).
>
> …

**Lean reading.** PM's identity `x = y` (defined in ✱13·01 by Leibniz's principle over predicative
functions) is Lean's `Eq`; the Df becomes `x = y ↔ PMIdent x y` (`proved (reading)`), and the
quantifier `(φ)` over predicative functions `φ!` is `∀ φ : α → Prop` (✱13·1, ✱13·11). Since every
Lean function is predicative, ✱13·101 and ✱13·12 hold for every `ψ : α → Prop`, which is the
content PM obtains from reducibility. `x ≠ y` is Lean's `x ≠ y` (✱13·02, `Iff.rfl`) and the chain
`x = y = z` is the conjunction of its links (✱13·03, `EqChain`). Functions of two variables in
✱13·21·22 may have arguments of different types.

**Status.** proved (all propositions; ✱13·01 proved (reading); ✱13·02, ✱13·03 definition)
-/

/-- ✱13·01 (Df). \(x=y.=:(\phi):\phi!x.\supset.\phi!y \quad\text{Df}\)

**Status.** proved (reading): `=` is read as Lean's primitive `Eq`; PM's definiens
`(φ) : φ!x . ⊃ . φ!y` is `PMIdent x y`, and the Df becomes their equivalence. -/
theorem pm13_01 {x y : α} : x = y ↔ PMIdent x y := PMIdent_iff_eq.symm

/-- ✱13·02 (Df). \(x\neq y.=.{\sim}(x=y) \quad\text{Df}\) -/
theorem pm13_02 {x y : α} : x ≠ y ↔ ¬(x = y) := Iff.rfl

/-- ✱13·03 (Df). \(x=y=z.=.x=y.y=z \quad\text{Df}\) -/
theorem pm13_03 {x y z : α} : EqChain x y z ↔ x = y ∧ y = z := Iff.rfl

/-- ✱13·1. \(\vdash\colon\ldotp x=y.\equiv:\phi!x.\supset_{\phi}.\phi!y \quad[\text{*4·2.(*13·01).(*10·02)}]\) -/
theorem pm13_1 {x y : α} : x = y ↔ ∀ φ : α → Prop, φ x → φ y :=
  ⟨fun h _ hx => h ▸ hx, fun h => h (fun z => x = z) rfl⟩

/-- ✱13·101. \(\vdash:x=y.\supset.\psi x\supset\psi y\) -/
theorem pm13_101 {ψ : α → Prop} {x y : α} : x = y → (ψ x → ψ y) := fun h hx => h ▸ hx

/-- ✱13·11. \(\vdash\colon\ldotp x=y.\equiv:\phi!x.\equiv_{\phi}.\phi!y\) -/
theorem pm13_11 {x y : α} : x = y ↔ ∀ φ : α → Prop, (φ x ↔ φ y) :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => (h (fun z => x = z)).1 rfl⟩

/-- ✱13·12. \(\vdash : x = y . \supset . \psi x \equiv \psi y\) -/
theorem pm13_12 {ψ : α → Prop} {x y : α} : x = y → (ψ x ↔ ψ y) := fun h => h ▸ Iff.rfl

/-- ✱13·13. \(\vdash : \psi x . x = y . \supset . \psi y \quad[\text{*13·101 . Comm . Imp}]\) -/
theorem pm13_13 {ψ : α → Prop} {x y : α} : ψ x ∧ x = y → ψ y := fun ⟨hx, h⟩ => h ▸ hx

/-- ✱13·14. \(\vdash : \psi x . {\sim}\psi y . \supset . x \neq y \quad[\text{*13·13 . *4·14}]\) -/
theorem pm13_14 {ψ : α → Prop} {x y : α} : ψ x ∧ ¬ψ y → x ≠ y :=
  fun ⟨hx, hy⟩ h => hy (h ▸ hx)

/-- ✱13·15. \(\vdash . x = x \quad[\text{Id . *10·11 . *13·1}]\) -/
theorem pm13_15 {x : α} : x = x := rfl

/-- ✱13·16. \(\vdash : x = y . \equiv . y = x \quad[\text{*13·11 . *10·32}]\) -/
theorem pm13_16 {x y : α} : x = y ↔ y = x := eq_comm

/-- ✱13·17. \(\vdash : x = y . y = z . \supset . x = z\) -/
theorem pm13_17 {x y z : α} : x = y ∧ y = z → x = z := fun ⟨h1, h2⟩ => h1.trans h2

/-- ✱13·171. \(\vdash : x = y . x = z . \supset . y = z \quad[\text{*13·16·17}]\) -/
theorem pm13_171 {x y z : α} : x = y ∧ x = z → y = z := fun ⟨h1, h2⟩ => h1.symm.trans h2

/-- ✱13·172. \(\vdash : y = x . z = x . \supset . y = z \quad[\text{*13·16·17}]\) -/
theorem pm13_172 {x y z : α} : y = x ∧ z = x → y = z := fun ⟨h1, h2⟩ => h1.trans h2.symm

/-- ✱13·18. \(\vdash : x = y . x \neq z . \supset . y \neq z \quad[\text{*13·17 . *4·14}]\) -/
theorem pm13_18 {x y z : α} : x = y ∧ x ≠ z → y ≠ z := fun ⟨h1, h2⟩ h => h2 (h1.trans h)

/-- ✱13·181. \(\vdash : x = y . y \neq z . \supset . x \neq z \quad[\text{*13·171 . *4·14}]\) -/
theorem pm13_181 {x y z : α} : x = y ∧ y ≠ z → x ≠ z :=
  fun ⟨h1, h2⟩ h => h2 (h1.symm.trans h)

/-- ✱13·182. \(\vdash \colon\ldotp x = y . \supset : z = x . \equiv . z = y \quad[\text{*13·17·172 . Exp . Comp}]\) -/
theorem pm13_182 {x y z : α} : x = y → (z = x ↔ z = y) := fun h => h ▸ Iff.rfl

/-- ✱13·183. \(\vdash \colon\ldotp x = y . \equiv : z = x . \equiv_z . z = y\) -/
theorem pm13_183 {x y : α} : x = y ↔ ∀ z, (z = x ↔ z = y) :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => (h x).1 rfl⟩

/-- ✱13·19. \(\vdash . (\exists y) . y = x \quad[\text{*13·15 . *10·24}]\) -/
theorem pm13_19 {x : α} : ∃ y, y = x := ⟨x, rfl⟩

/-- ✱13·191. \(\vdash \colon\ldotp y = x . \supset_y . \phi y : \equiv . \phi x\) -/
theorem pm13_191 {φ : α → Prop} {x : α} : (∀ y, y = x → φ y) ↔ φ x :=
  ⟨fun h => h x rfl, fun h _ hy => hy ▸ h⟩

/-- ✱13·192. \(\vdash\colon\ldotp(\exists c):x=b.\equiv_{x}.x=c:\psi c:\equiv.\psi b\) -/
theorem pm13_192 {ψ : α → Prop} {b : α} : (∃ c, (∀ x, x = b ↔ x = c) ∧ ψ c) ↔ ψ b := by
  constructor
  · rintro ⟨c, hc, hψ⟩
    rw [(hc b).1 rfl]
    exact hψ
  · intro h
    exact ⟨b, fun _ => Iff.rfl, h⟩

/-- ✱13·193. \(\vdash:\phi x.x=y.\equiv.\phi y.x=y\) -/
theorem pm13_193 {φ : α → Prop} {x y : α} : φ x ∧ x = y ↔ φ y ∧ x = y :=
  ⟨fun ⟨h1, h2⟩ => ⟨h2 ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2 ▸ h1, h2⟩⟩

/-- ✱13·194. \(\vdash:\phi x.x=y.\equiv.\phi x.\phi y.x=y \quad[\text{*13·13.*4·71}]\) -/
theorem pm13_194 {φ : α → Prop} {x y : α} : φ x ∧ x = y ↔ (φ x ∧ φ y) ∧ x = y :=
  ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, h2 ▸ h1⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩

/-- ✱13·195. \(\vdash:(\exists y).y=x.\phi y.\equiv.\phi x\) -/
theorem pm13_195 {φ : α → Prop} {x : α} : (∃ y, y = x ∧ φ y) ↔ φ x :=
  ⟨fun ⟨_, hy, h⟩ => hy ▸ h, fun h => ⟨x, rfl, h⟩⟩

/-- ✱13·196. \(\vdash\colon\ldotp{\sim}\phi x.\equiv:\phi y.\supset_{y}.y\neq x \quad[\text{*13·195.Transp.*10·51}]\) -/
theorem pm13_196 {φ : α → Prop} {x : α} : ¬φ x ↔ ∀ y, φ y → y ≠ x :=
  ⟨fun h _ hy hyx => h (hyx ▸ hy), fun h hx => h x hx rfl⟩

/-- ✱13·21. \(\vdash\colon\ldotp z=x.w=y.\supset_{z,w}.\phi(z,w):\equiv.\phi(x,y)\) -/
theorem pm13_21 {φ : α → β → Prop} {x : α} {y : β} :
    (∀ z w, z = x ∧ w = y → φ z w) ↔ φ x y := by
  constructor
  · intro h
    exact h x y ⟨rfl, rfl⟩
  · rintro h z w ⟨rfl, rfl⟩
    exact h

/-- ✱13·22. \(\vdash:(\exists z,w).z=x.w=y.\phi(z,w).\equiv.\phi(x,y)\) -/
theorem pm13_22 {φ : α → β → Prop} {x : α} {y : β} :
    (∃ z w, (z = x ∧ w = y) ∧ φ z w) ↔ φ x y := by
  constructor
  · rintro ⟨z, w, ⟨rfl, rfl⟩, h⟩
    exact h
  · intro h
    exact ⟨x, y, ⟨rfl, rfl⟩, h⟩

/-- ✱13·3. \(\vdash\colon\colon\phi a\lor{\sim}\phi a.\supset\colon\ldotp\phi x\lor{\sim}\phi x.\equiv:x=a.\lor.x\neq a\) -/
theorem pm13_3 {φ : α → Prop} {x a : α} :
    (φ a ∨ ¬φ a) → ((φ x ∨ ¬φ x) ↔ (x = a ∨ x ≠ a)) :=
  fun _ => ⟨fun _ => em _, fun _ => em _⟩

/-!
## [✱14] Descriptions

*(Vol. 1, p. 181)*

> *Summary of* *14.
>
> …

**Lean reading.** A description `(℩x)(φx)` is an incomplete symbol: it is never a Lean term. A
proposition `ψ(℩x)(φx)` in which it has scope `ψ` is `TheIs φ ψ` (✱14·01), and `E!(℩x)(φx)` is
`EBang φ` (✱14·02); the scope is the one PM marks by `[(℩x)(φx)]`, otherwise the smallest
proposition in dots or brackets containing the description (so `a = (℩x)(φx)` is
`TheIs φ (fun c => a = c)` and, in ✱14·241, only `y = (℩x)(φx)` is the scope). With two
descriptions the first has the larger scope (`TheIs2`, ✱14·03; ✱14·04 `TheIs2Rev` gives it to
the second), so `(℩x)(φx) = (℩x)(ψx)` is `TheIs2 φ ψ (fun b c => b = c)`. The description's
argument types are arbitrary (`φ : α → Prop`, with `ψ : β → Prop` where PM's formula allows two
types). In ✱14·3 the apparent variables `p, q` range over `Prop` and `f : Prop → Prop`. Chains
(✱14·122, ✱14·123, ✱14·202, ✱14·26) are conjunctions of their links.

**Status.** proved (all propositions; ✱14·01–✱14·04 definition)
-/

/-- ✱14·01 (Df). \([({℩}x)(\phi x)].\psi ({℩}x)(\phi x).=:(\exists b):\phi x.\equiv_{x}.x=b:\psi b \quad\text{Df}\) -/
theorem pm14_01 {φ ψ : α → Prop} : TheIs φ ψ ↔ ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b := Iff.rfl

/-- ✱14·02 (Df). \(\text{E}!({℩}x)(\phi x).=:(\exists b):\phi x.\equiv_{x}.x=b \quad\text{Df}\) -/
theorem pm14_02 {φ : α → Prop} : EBang φ ↔ ∃ b, ∀ x, φ x ↔ x = b := Iff.rfl

/-- ✱14·03 (Df). \[\begin{align}[({℩}x)(\phi x),({℩}x)&(\psi x)].f\{({℩}x)(\phi x),\,({℩}x)(\psi x)\}.=:\\ &[({℩}x)(\phi x)]:[({℩}x)(\psi x)].f\{({℩}x)(\phi x),({℩}x)(\psi x)\} \quad\text{Df}\end{align}\] -/
theorem pm14_03 {φ : α → Prop} {ψ : β → Prop} {f : α → β → Prop} :
    TheIs2 φ ψ f ↔ TheIs φ (fun b => TheIs ψ (fun c => f b c)) := Iff.rfl

/-- ✱14·04 (Df). \[\begin{align}[({℩}x)(\psi x)].&f\{({℩}x)(\phi x),\,({℩}x)(\psi x)\}.=.\\ &[({℩}x)(\psi x),({℩}x)(\phi x)].f\{({℩}x)(\phi x),\,({℩}x)(\psi x)\} \quad\text{Df}\end{align}\] -/
theorem pm14_04 {φ : α → Prop} {ψ : β → Prop} {f : α → β → Prop} :
    TheIs2Rev φ ψ f ↔ TheIs2 ψ φ (fun c b => f b c) := Iff.rfl

/-- ✱14·1. \[\begin{align}\vdash\colon\ldotp[({℩}x)(\phi x)].\psi(℩x)(\phi x).\equiv:(\exists b):\phi x.\equiv_{x}.&x=b:\psi b &[\text{*4·2.(*14·01)}]\end{align}\] -/
theorem pm14_1 {φ ψ : α → Prop} : TheIs φ ψ ↔ ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b := Iff.rfl

/-- ✱14·101. \(\vdash\colon\ldotp \psi({℩}x)(\phi x).\equiv:(\exists b):\phi x.\equiv_{x}.x=b:\psi b \quad[\text{*14·1}]\) -/
theorem pm14_101 {φ ψ : α → Prop} : TheIs φ ψ ↔ ∃ b, (∀ x, φ x ↔ x = b) ∧ ψ b := pm14_1

/-- ✱14·11. \(\vdash\colon\ldotp\text{E}!({℩}x)(\phi x).\equiv:(\exists b):\phi x.\equiv_{x}.x=b \quad[\text{*4·2.(*14·02)}]\) -/
theorem pm14_11 {φ : α → Prop} : EBang φ ↔ ∃ b, ∀ x, φ x ↔ x = b := Iff.rfl

/-- ✱14·111. \[\begin{align}\vdash\colon\ldotp[({℩}x)(\psi x)].&f\{({℩}x)(\phi x),\,({℩}x)(\psi x)\}.\equiv:\\ &(\exists b,c):\phi x.\equiv_{x}.x=b:\psi x.\equiv_{x}.x=c:f(b,c)\end{align}\] -/
theorem pm14_111 {φ : α → Prop} {ψ : β → Prop} {f : α → β → Prop} :
    TheIs2Rev φ ψ f ↔
      ∃ b c, ((∀ x, φ x ↔ x = b) ∧ (∀ x, ψ x ↔ x = c)) ∧ f b c := by
  constructor
  · rintro ⟨c, hc, b, hb, hf⟩
    exact ⟨b, c, ⟨hb, hc⟩, hf⟩
  · rintro ⟨b, c, ⟨hb, hc⟩, hf⟩
    exact ⟨c, hc, b, hb, hf⟩

/-- ✱14·112. \[\begin{align}\vdash\colon\ldotp f\{(℩x)&(\phi x),\,({℩}x)(\psi x)\}.\equiv:\\ &(\exists b,c):\phi x.\equiv_{x}.x=b:\psi x.\equiv_{x}.x=c:f(b,c)\\ [\text{Proof as in *14·111}]\end{align}\] -/
theorem pm14_112 {φ : α → Prop} {ψ : β → Prop} {f : α → β → Prop} :
    TheIs2 φ ψ f ↔
      ∃ b c, ((∀ x, φ x ↔ x = b) ∧ (∀ x, ψ x ↔ x = c)) ∧ f b c := by
  constructor
  · rintro ⟨b, hb, c, hc, hf⟩
    exact ⟨b, c, ⟨hb, hc⟩, hf⟩
  · rintro ⟨b, c, ⟨hb, hc⟩, hf⟩
    exact ⟨b, hb, c, hc, hf⟩

/-- `(℩x)(φx) = (℩x)(ψx)`: both descriptions exist and describe the same object. -/
private theorem theIs2_eq_iff {φ ψ : α → Prop} :
    TheIs2 φ ψ (fun b c => b = c) ↔ ∃ b, (∀ x, φ x ↔ x = b) ∧ (∀ x, ψ x ↔ x = b) := by
  rw [pm14_112]
  constructor
  · rintro ⟨b, c, ⟨hb, hc⟩, hbc⟩
    have e : b = c := hbc
    exact ⟨b, hb, fun x => by rw [e]; exact hc x⟩
  · rintro ⟨b, hb, hc⟩
    exact ⟨b, b, ⟨hb, hc⟩, rfl⟩

/-- ✱14·113. \[\begin{align}&\vdash:[({℩}x)(\psi x)].f\{({℩}x)(\phi x),({℩}x)(\psi x)\}.\equiv.f\{({℩}x)(\phi x),\,({℩}x)(\psi x)\}\\ &[\text{*14·111·112}]\end{align}\] -/
theorem pm14_113 {φ : α → Prop} {ψ : β → Prop} {f : α → β → Prop} :
    TheIs2Rev φ ψ f ↔ TheIs2 φ ψ f :=
  pm14_111.trans pm14_112.symm

/-- ✱14·12. \(\vdash\colon\ldotp\text{E}!({℩}x)(\phi x).\supset:\phi x.\phi y.\supset_{x,y}.x=y\) -/
theorem pm14_12 {φ : α → Prop} : EBang φ → ∀ x y, φ x ∧ φ y → x = y := by
  rintro ⟨b, hb⟩ x y ⟨hx, hy⟩
  rw [(hb x).1 hx, (hb y).1 hy]

/-- ✱14·121. \(\vdash\colon\ldotp\phi x.\equiv_{x}.x=b:\phi x.\equiv_{x}.x=c:\supset.b=c\) -/
theorem pm14_121 {φ : α → Prop} {b c : α} :
    (∀ x, φ x ↔ x = b) ∧ (∀ x, φ x ↔ x = c) → b = c :=
  fun ⟨hb, hc⟩ => (hc b).1 ((hb b).2 rfl)

/-- ✱14·122. \[\begin{align}\vdash\colon\ldotp\phi x.&\equiv_{x}.x=b:\equiv:\phi x.\supset_{x}.x=b:\phi b:\\ &\equiv:\phi x.\supset_{x}.x=b:(\exists x).\phi x\end{align}\] -/
theorem pm14_122 {φ : α → Prop} {b : α} :
    ((∀ x, φ x ↔ x = b) ↔ (∀ x, φ x → x = b) ∧ φ b) ∧
      ((∀ x, φ x → x = b) ∧ φ b ↔ (∀ x, φ x → x = b) ∧ ∃ x, φ x) := by
  refine ⟨⟨fun h => ⟨fun x => (h x).1, (h b).2 rfl⟩, ?_⟩, ⟨fun ⟨h1, h2⟩ => ⟨h1, b, h2⟩, ?_⟩⟩
  · rintro ⟨h1, h2⟩ x
    exact ⟨h1 x, fun hx => hx ▸ h2⟩
  · rintro ⟨h1, x, hx⟩
    exact ⟨h1, h1 x hx ▸ hx⟩

/-- ✱14·123. \[\begin{align}\vdash\colon\ldotp \phi(z,w).\equiv_{z,w}.z&=x.w=y:\\ &\equiv:\phi(z,w).\supset_{z,w}.z=x.w=y:\phi(x,y):\\ &\equiv:\phi(z,w).\supset_{z,w}.z=x.w=y:(\exists z,w).\phi(z,w)\end{align}\] -/
theorem pm14_123 {φ : α → β → Prop} {x : α} {y : β} :
    ((∀ z w, φ z w ↔ z = x ∧ w = y) ↔ (∀ z w, φ z w → z = x ∧ w = y) ∧ φ x y) ∧
      ((∀ z w, φ z w → z = x ∧ w = y) ∧ φ x y ↔
        (∀ z w, φ z w → z = x ∧ w = y) ∧ ∃ z w, φ z w) := by
  refine ⟨⟨fun h => ⟨fun z w => (h z w).1, (h x y).2 ⟨rfl, rfl⟩⟩, ?_⟩,
    ⟨fun ⟨h1, h2⟩ => ⟨h1, x, y, h2⟩, ?_⟩⟩
  · rintro ⟨h1, h2⟩ z w
    refine ⟨h1 z w, ?_⟩
    rintro ⟨rfl, rfl⟩
    exact h2
  · rintro ⟨h1, z, w, h⟩
    obtain ⟨hz, hw⟩ := h1 z w h
    subst hz hw
    exact ⟨h1, h⟩

/-- ✱14·124. \[\begin{align}\vdash\colon\ldotp(\exists x,y):&\phi(z,w).\equiv_{z,w}.z=x.w=y:\\ &\equiv:(\exists x,y).\phi(x,y):\phi(z,w).\phi(u,v).\supset_{z,w,u,v}.z=u.w=v\end{align}\] -/
theorem pm14_124 {φ : α → β → Prop} :
    (∃ x y, ∀ z w, φ z w ↔ z = x ∧ w = y) ↔
      (∃ x y, φ x y) ∧ ∀ z w u v, φ z w ∧ φ u v → z = u ∧ w = v := by
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨⟨x, y, (h x y).2 ⟨rfl, rfl⟩⟩, ?_⟩
    rintro z w u v ⟨h1, h2⟩
    obtain ⟨hz, hw⟩ := (h z w).1 h1
    obtain ⟨hu, hv⟩ := (h u v).1 h2
    exact ⟨hz.trans hu.symm, hw.trans hv.symm⟩
  · rintro ⟨⟨x, y, hxy⟩, h⟩
    refine ⟨x, y, fun z w => ⟨fun hzw => h z w x y ⟨hzw, hxy⟩, ?_⟩⟩
    rintro ⟨rfl, rfl⟩
    exact hxy

/-- ✱14·13. \(\vdash:a=({℩}x)(\phi x).\equiv.({℩}x)(\phi x)=a\) -/
theorem pm14_13 {φ : α → Prop} {a : α} :
    TheIs φ (fun c => a = c) ↔ TheIs φ (fun c => c = a) := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, Eq.symm h⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, Eq.symm h⟩

/-- ✱14·131. \(\vdash:({℩}x)(\phi x)=(℩x)(\psi x).\equiv.({℩}x)(\psi x)=({℩}x)(\phi x)\) -/
theorem pm14_131 {φ ψ : α → Prop} :
    TheIs2 φ ψ (fun b c => b = c) ↔ TheIs2 ψ φ (fun c b => c = b) := by
  rw [theIs2_eq_iff, theIs2_eq_iff]
  exact ⟨fun ⟨b, h1, h2⟩ => ⟨b, h2, h1⟩, fun ⟨b, h1, h2⟩ => ⟨b, h2, h1⟩⟩

/-- ✱14·14. \(\vdash:a=b.b=({℩}x)(\phi x).\supset.a=({℩}x)(\phi x) \quad[\text{*13·13}]\) -/
theorem pm14_14 {φ : α → Prop} {a b : α} :
    a = b ∧ TheIs φ (fun c => b = c) → TheIs φ (fun c => a = c) := by
  rintro ⟨rfl, h⟩
  exact h

/-- ✱14·142. \(\vdash:a=({℩}x)(\phi x).({℩}x)(\phi x)=({℩}x)(\psi x).\supset.a=({℩}x)(\psi x)\) -/
theorem pm14_142 {φ ψ : α → Prop} {a : α} :
    TheIs φ (fun c => a = c) ∧ TheIs2 φ ψ (fun b c => b = c) → TheIs ψ (fun c => a = c) := by
  rintro ⟨⟨b, hb, hab⟩, h⟩
  rw [theIs2_eq_iff] at h
  obtain ⟨c, hc1, hc2⟩ := h
  exact ⟨c, hc2, (hc1 a).1 ((hb a).2 hab)⟩

/-- ✱14·144. \(\vdash:({℩}x)(\phi x)=({℩}x)(\psi x).({℩}x)(\psi x)=({℩}x)(\chi x).\supset.({℩}x)(\phi x)=({℩}x)(\chi x)\) -/
theorem pm14_144 {φ ψ χ : α → Prop} :
    TheIs2 φ ψ (fun b c => b = c) ∧ TheIs2 ψ χ (fun b c => b = c) →
      TheIs2 φ χ (fun b c => b = c) := by
  rintro ⟨h1, h2⟩
  rw [theIs2_eq_iff] at h1 h2 ⊢
  obtain ⟨b, hb1, hb2⟩ := h1
  obtain ⟨c, hc1, hc2⟩ := h2
  have e : b = c := (hc1 b).1 ((hb2 b).2 rfl)
  exact ⟨b, hb1, fun x => by rw [e]; exact hc2 x⟩

/-- ✱14·145. \(\vdash:a=({℩}x)(\phi x).a=({℩}x)(\psi x).\supset.({℩}x)(\phi x)=({℩}x)(\psi x)\) -/
theorem pm14_145 {φ ψ : α → Prop} {a : α} :
    TheIs φ (fun c => a = c) ∧ TheIs ψ (fun c => a = c) → TheIs2 φ ψ (fun b c => b = c) := by
  rintro ⟨⟨b, hb, hab⟩, ⟨c, hc, hac⟩⟩
  have e : b = c := (Eq.symm hab).trans hac
  rw [theIs2_eq_iff]
  exact ⟨b, hb, fun x => by rw [e]; exact hc x⟩

/-- ✱14·15. \(\vdash \colon\ldotp ({℩}x)(\phi x) = b . \supset : \psi \{({℩}x)(\phi x)\} . \equiv . \psi b\) -/
theorem pm14_15 {φ ψ : α → Prop} {b : α} :
    TheIs φ (fun c => c = b) → (TheIs φ ψ ↔ ψ b) := by
  rintro ⟨c, hc, hcb⟩
  have e : c = b := hcb
  rw [e] at hc
  exact TheIs_iff_of_unique hc

/-- ✱14·16. \(\vdash \colon\ldotp ({℩}x)(\phi x) = ({℩}x)(\psi x) . \supset : \chi \{({℩}x)(\phi x)\} . \equiv . \chi \{({℩}x)(\psi x)\}\) -/
theorem pm14_16 {φ ψ χ : α → Prop} :
    TheIs2 φ ψ (fun b c => b = c) → (TheIs φ χ ↔ TheIs ψ χ) := by
  rw [theIs2_eq_iff]
  rintro ⟨b, h1, h2⟩
  rw [TheIs_iff_of_unique h1, TheIs_iff_of_unique h2]

/-- ✱14·17. \(\vdash \colon\ldotp ({℩}x)(\phi x) = b . \equiv : \psi ! ({℩}x)(\phi x) . \equiv_{\psi} . \psi ! b\) -/
theorem pm14_17 {φ : α → Prop} {b : α} :
    TheIs φ (fun c => c = b) ↔ ∀ ψ : α → Prop, (TheIs φ ψ ↔ ψ b) :=
  ⟨fun h _ => pm14_15 h, fun h => (h (fun c => c = b)).2 rfl⟩

/-- ✱14·171. \(\vdash\colon\ldotp ({℩}x)(\phi x)=b.\equiv:\psi!b.\supset_{\psi}.\psi!({℩}x)(\phi x)\) -/
theorem pm14_171 {φ : α → Prop} {b : α} :
    TheIs φ (fun c => c = b) ↔ ∀ ψ : α → Prop, ψ b → TheIs φ ψ :=
  ⟨fun h _ hψ => (pm14_15 h).2 hψ, fun h => h (fun c => c = b) rfl⟩

/-- ✱14·18. \(\vdash\colon\ldotp \text{E}!({℩}x)(\phi x).\supset:(x).\psi x.\supset.\psi({℩}x)(\phi x)\) -/
theorem pm14_18 {φ ψ : α → Prop} : EBang φ → ((∀ x, ψ x) → TheIs φ ψ) := by
  rintro ⟨b, hb⟩ h
  exact ⟨b, hb, h b⟩

/-- ✱14·2. \(\vdash.({℩}x)(x=a)=a\) -/
theorem pm14_2 {a : α} : TheIs (fun x => x = a) (fun c => c = a) :=
  ⟨a, fun _ => Iff.rfl, rfl⟩

/-- ✱14·201. \(\vdash:\text{E}!({℩}x)(\phi x).\supset.(\exists x).\phi x\) -/
theorem pm14_201 {φ : α → Prop} : EBang φ → ∃ x, φ x := by
  rintro ⟨b, hb⟩
  exact ⟨b, (hb b).2 rfl⟩

/-- ✱14·202. \(\vdash\colon\ldotp \phi x.\equiv_{x}.x=b:\equiv:({℩}x)(\phi x)=b:\equiv:\phi x.\equiv_{x}.b=x:\equiv:b=({℩}x)(\phi x)\) -/
theorem pm14_202 {φ : α → Prop} {b : α} :
    (((∀ x, φ x ↔ x = b) ↔ TheIs φ (fun c => c = b)) ∧
        (TheIs φ (fun c => c = b) ↔ ∀ x, φ x ↔ b = x)) ∧
      ((∀ x, φ x ↔ b = x) ↔ TheIs φ (fun c => b = c)) := by
  have h1 : (∀ x, φ x ↔ x = b) ↔ TheIs φ (fun c => c = b) := by
    constructor
    · intro h
      exact ⟨b, h, rfl⟩
    · rintro ⟨c, hc, hcb⟩
      have e : c = b := hcb
      rw [← e]
      exact hc
  have h2 : (∀ x, φ x ↔ x = b) ↔ ∀ x, φ x ↔ b = x :=
    ⟨fun h x => (h x).trans eq_comm, fun h x => (h x).trans eq_comm⟩
  exact ⟨⟨h1, h1.symm.trans h2⟩, h2.symm.trans (h1.trans pm14_13.symm)⟩

/-- ✱14·203. \(\vdash\colon\ldotp \text{E}!({℩}x)(\phi x).\equiv:(\exists x).\phi x:\phi x.\phi y.\supset_{x,y}.x=y\) -/
theorem pm14_203 {φ : α → Prop} :
    EBang φ ↔ (∃ x, φ x) ∧ ∀ x y, φ x ∧ φ y → x = y := by
  constructor
  · intro h
    exact ⟨pm14_201 h, pm14_12 h⟩
  · rintro ⟨⟨b, hb⟩, h⟩
    exact ⟨b, fun x => ⟨fun hx => h x b ⟨hx, hb⟩, fun e => e ▸ hb⟩⟩

/-- ✱14·204. \(\vdash\colon\ldotp \text{E}!({℩}x)(\phi x).\equiv:(\exists b).({℩}x)(\phi x)=b\) -/
theorem pm14_204 {φ : α → Prop} : EBang φ ↔ ∃ b, TheIs φ (fun c => c = b) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, b, hb, rfl⟩
  · rintro ⟨_, c, hc, _⟩
    exact ⟨c, hc⟩

/-- ✱14·205. \(\vdash:\psi({℩}x)(\phi x).\equiv.(\exists b).b=({℩}x)(\phi x).\psi b \quad[\text{*14·202·1}]\) -/
theorem pm14_205 {φ ψ : α → Prop} : TheIs φ ψ ↔ ∃ b, TheIs φ (fun c => b = c) ∧ ψ b := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, ⟨b, hb, rfl⟩, h⟩
  · rintro ⟨b, ⟨c, hc, hbc⟩, h⟩
    have e : b = c := hbc
    rw [e] at h
    exact ⟨c, hc, h⟩

/-- ✱14·21. \(\vdash:\psi({℩}x)(\phi x).\supset.\text{E}!({℩}x)(\phi x)\) -/
theorem pm14_21 {φ ψ : α → Prop} : TheIs φ ψ → EBang φ := by
  rintro ⟨b, hb, _⟩
  exact ⟨b, hb⟩

/-- ✱14·22. \(\vdash:\text{E}!({℩}x)(\phi x).\equiv.\phi({℩}x)(\phi x)\) -/
theorem pm14_22 {φ : α → Prop} : EBang φ ↔ TheIs φ φ := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb, (hb b).2 rfl⟩
  · exact pm14_21

/-- ✱14·23. \(\vdash: \text{E}!({℩}x)(\phi x.\psi x).\equiv.\phi \{({℩}x)(\phi x.\psi x)\}\) -/
theorem pm14_23 {φ ψ : α → Prop} :
    EBang (fun x => φ x ∧ ψ x) ↔ TheIs (fun x => φ x ∧ ψ x) φ := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb, ((hb b).2 rfl).1⟩
  · exact pm14_21

/-- ✱14·24. \(\vdash\colon\ldotp \text{E}!({℩}x)(\phi x).\equiv:[({℩}x)(\phi x)]:\phi y.\equiv_{y}.y=({℩}x)(\phi x)\) -/
theorem pm14_24 {φ : α → Prop} : EBang φ ↔ TheIs φ (fun c => ∀ y, φ y ↔ y = c) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb, hb⟩
  · exact pm14_21

/-- ✱14·241. \(\vdash\colon\ldotp \text{E}!({℩}x)(\phi x).\supset:\phi y.\equiv_{y}.y=({℩}x)(\phi x)\) -/
theorem pm14_241 {φ : α → Prop} : EBang φ → ∀ y, φ y ↔ TheIs φ (fun c => y = c) := by
  rintro ⟨b, hb⟩ y
  rw [TheIs_iff_of_unique hb]
  exact hb y

/-- ✱14·242. \(\vdash\colon\ldotp \phi x.\equiv_{x}.x=b:\supset:\psi b.\equiv.\psi({℩}x)(\phi x) \quad[\text{*14·202·15}]\) -/
theorem pm14_242 {φ ψ : α → Prop} {b : α} : (∀ x, φ x ↔ x = b) → (ψ b ↔ TheIs φ ψ) :=
  fun h => (TheIs_iff_of_unique h).symm

/-- ✱14·25. \(\vdash\colon\ldotp \text{E}!({℩}x)(\phi x).\supset:\phi x\supset_{x}\psi x.\equiv.\psi({℩}x)(\phi x)\) -/
theorem pm14_25 {φ ψ : α → Prop} : EBang φ → ((∀ x, φ x → ψ x) ↔ TheIs φ ψ) := by
  rintro ⟨b, hb⟩
  rw [TheIs_iff_of_unique hb]
  exact ⟨fun h => h b ((hb b).2 rfl), fun h x hx => ((hb x).1 hx) ▸ h⟩

/-- ✱14·26. \(\vdash\colon\ldotp \text{E}!({℩}x)(\phi x).\supset:(\exists x).\phi x.\psi x.\equiv.\psi \{({℩}x)(\phi x)\}.\equiv.\phi x\supset_{x}\psi x\) -/
theorem pm14_26 {φ ψ : α → Prop} :
    EBang φ → ((∃ x, φ x ∧ ψ x) ↔ TheIs φ ψ) ∧ (TheIs φ ψ ↔ ∀ x, φ x → ψ x) := by
  rintro ⟨b, hb⟩
  rw [TheIs_iff_of_unique hb]
  refine ⟨⟨?_, fun h => ⟨b, (hb b).2 rfl, h⟩⟩,
    ⟨fun h x hx => ((hb x).1 hx) ▸ h, fun h => h b ((hb b).2 rfl)⟩⟩
  rintro ⟨x, hx, hψ⟩
  exact ((hb x).1 hx) ▸ hψ

/-- ✱14·27. \(\vdash\colon\ldotp \text{E}!({℩}x)(\phi x).\supset:\phi x\equiv_{x}\psi x.\equiv.({℩}x)(\phi x)=({℩}x)(\psi x)\) -/
theorem pm14_27 {φ ψ : α → Prop} :
    EBang φ → ((∀ x, φ x ↔ ψ x) ↔ TheIs2 φ ψ (fun b c => b = c)) := by
  rintro ⟨b, hb⟩
  rw [theIs2_eq_iff]
  constructor
  · intro h
    exact ⟨b, hb, fun x => (h x).symm.trans (hb x)⟩
  · rintro ⟨c, hc1, hc2⟩ x
    exact (hc1 x).trans (hc2 x).symm

/-- ✱14·271. \(\vdash\colon\ldotp \phi x.\equiv_{x}.\psi x:\supset:\text{E}!({℩}x)(\phi x).\equiv.\text{E}!({℩}x)(\psi x)\) -/
theorem pm14_271 {φ ψ : α → Prop} : (∀ x, φ x ↔ ψ x) → (EBang φ ↔ EBang ψ) := by
  intro h
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, fun x => (h x).symm.trans (hb x)⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, fun x => (h x).trans (hb x)⟩

/-- ✱14·272. \(\vdash\colon\ldotp \phi x.\equiv_{x}.\psi x:\supset:\chi(℩x)(\phi x).\equiv.\chi({℩}x)(\psi x)\) -/
theorem pm14_272 {φ ψ χ : α → Prop} : (∀ x, φ x ↔ ψ x) → (TheIs φ χ ↔ TheIs ψ χ) := by
  intro h
  have e : φ = ψ := funext fun x => propext (h x)
  rw [e]

/-- ✱14·28. \(\vdash:\text{E}!({℩}x)(\phi x).\equiv.(℩x)(\phi x)=({℩}x)(\phi x)\) -/
theorem pm14_28 {φ : α → Prop} : EBang φ ↔ TheIs2 φ φ (fun b c => b = c) := by
  rw [theIs2_eq_iff]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb, hb⟩
  · rintro ⟨b, hb, _⟩
    exact ⟨b, hb⟩

/-- ✱14·3. \[\begin{align}&\vdash\colon\ldotp p\equiv q.\supset_{p,q}.f(p)\equiv f(q):\text{E}!({℩}x)(\phi x):\supset:\\ &f\{[({℩}x)(\phi x)].\chi({℩}x)(\phi x)\}.\equiv.[({℩}x)(\phi x)].f\{\chi(℩x)(\phi x)\}\end{align}\] -/
theorem pm14_3 {φ χ : α → Prop} {f : Prop → Prop} :
    (∀ p q : Prop, (p ↔ q) → (f p ↔ f q)) ∧ EBang φ →
      (f (TheIs φ χ) ↔ TheIs φ (fun b => f (χ b))) := by
  rintro ⟨hf, b, hb⟩
  exact (hf _ _ (TheIs_iff_of_unique hb)).trans
    (TheIs_iff_of_unique (ψ := fun b => f (χ b)) hb).symm

/-- ✱14·31. \[\begin{align}\vdash\colon\colon \text{E}!(℩x)(\phi x).\supset\colon\ldotp [(℩x)(\phi x)].&p\lor \chi(℩x)(\phi x).\\ &\equiv:p.\lor.[(℩x)(\phi x)].\chi(℩x)(\phi x)\end{align}\] -/
theorem pm14_31 {p : Prop} {φ χ : α → Prop} :
    EBang φ → (TheIs φ (fun b => p ∨ χ b) ↔ p ∨ TheIs φ χ) := by
  rintro ⟨b, hb⟩
  rw [TheIs_iff_of_unique hb, TheIs_iff_of_unique hb]

/-- ✱14·32. \[\begin{align}\vdash\colon\ldotp \text{E}!(℩x)(\phi x).\equiv:[(℩x)(\phi x)].{\sim}&\chi(℩x)(\phi x).\\ &\equiv.{\sim}\{[(℩x)(\phi x)].\chi(℩x)(\phi x)\}\\ \quad[\text{*14·242.*4·11.*10·23.*14·11}]\end{align}\] -/
theorem pm14_32 {φ χ : α → Prop} :
    EBang φ ↔ (TheIs φ (fun b => ¬χ b) ↔ ¬TheIs φ χ) := by
  constructor
  · rintro ⟨b, hb⟩
    rw [TheIs_iff_of_unique hb, TheIs_iff_of_unique hb]
  · intro h
    by_contra hE
    exact hE (pm14_21 (h.2 fun h' => hE (pm14_21 h')))

/-- ✱14·33. \[\begin{align}\vdash\colon\colon \text{E}!(℩x)(\phi x).\supset\colon\ldotp [(℩x)(\phi x)].&p\supset\chi(℩x)(\phi x).\\ &\equiv:p.\supset.[(℩x)(\phi x)].\chi(℩x)(\phi x)\\ \qquad[\text{*14·242.*4·85.*10·23.*14·11}]\end{align}\] -/
theorem pm14_33 {p : Prop} {φ χ : α → Prop} :
    EBang φ → (TheIs φ (fun b => p → χ b) ↔ (p → TheIs φ χ)) := by
  rintro ⟨b, hb⟩
  rw [TheIs_iff_of_unique hb, TheIs_iff_of_unique hb]

/-- ✱14·331. \[\begin{align}\vdash\colon\colon \text{E}!(℩x)(\phi x).\supset\colon\ldotp [(℩x)(\phi x)].&\chi(℩x)(\phi x)\supset p.\\ &\equiv:[(℩x)(\phi x)].\chi(℩x)(\phi x).\supset.p\\ \qquad[\text{*4·84.*14·242.*10·23.*14·11}]\end{align}\] -/
theorem pm14_331 {p : Prop} {φ χ : α → Prop} :
    EBang φ → (TheIs φ (fun b => χ b → p) ↔ (TheIs φ χ → p)) := by
  rintro ⟨b, hb⟩
  rw [TheIs_iff_of_unique hb, TheIs_iff_of_unique hb]

/-- ✱14·332. \[\begin{align}\vdash\colon\colon \text{E}!(℩x)(\phi x).\supset\colon\ldotp [(℩x)(\phi x)].p&\equiv\chi(℩x)(\phi x).\equiv\\ &:p.\equiv.[(℩x)(\phi x)].\chi (℩x)(\phi x)\\ \qquad[\text{*4·86.*14·242.*10·23.*14·11}]\end{align}\] -/
theorem pm14_332 {p : Prop} {φ χ : α → Prop} :
    EBang φ → (TheIs φ (fun b => p ↔ χ b) ↔ (p ↔ TheIs φ χ)) := by
  rintro ⟨b, hb⟩
  rw [TheIs_iff_of_unique hb, TheIs_iff_of_unique hb]

/-- ✱14·34. \(\vdash\colon\ldotp p:[(℩x)(\phi x)].\chi(℩x)(\phi x):\equiv:[(℩x)(\phi x)]:p.\chi(℩x)(\phi x)\) -/
theorem pm14_34 {p : Prop} {φ χ : α → Prop} :
    p ∧ TheIs φ χ ↔ TheIs φ (fun b => p ∧ χ b) := by
  constructor
  · rintro ⟨hp, b, hb, h⟩
    exact ⟨b, hb, hp, h⟩
  · rintro ⟨b, hb, hp, h⟩
    exact ⟨hp, b, hb, h⟩

end PrincipiaMathematica
