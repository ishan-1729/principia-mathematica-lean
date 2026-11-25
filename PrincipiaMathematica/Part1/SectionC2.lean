import PrincipiaMathematica.Defs.Part1

/-!
# Part I, Section C: Classes and relations

Volume 1. Numbers: ✱23, ✱24, ✱25.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v

variable {α : Type u} {β : Type v}

/-- Rewrites a statement about classes into a statement about membership, pointwise
(`V`, `Λ`, `∩`, `∪`, `−`, `⊂` and `=` of classes unfolded). -/
local macro "cls_simp" : tactic =>
  `(tactic| simp only [Null_eq_empty, V_eq_univ, Set.ext_iff, Set.subset_def, Set.mem_inter_iff,
    Set.mem_union, Set.mem_sdiff, Set.mem_compl_iff, Set.mem_empty_iff_false, Set.mem_univ,
    Set.mem_ofPred_eq, iff_false, iff_true, ← forall_and])

/-- Proves a statement of the class calculus that holds pointwise by propositional logic. -/
local macro "pm_cls" : tactic =>
  `(tactic| (cls_simp <;> first
    | (intro x; tauto)
    | exact forall_congr' fun x => by tauto
    | (intro h x; have := h x; tauto)
    | (intro h; exact forall_congr' fun x => by have := h x; tauto)))

/-- Rewrites a statement about relations into a statement about pairs, pointwise
(`V̇`, `Λ̇`, `∩̇`, `∪̇`, `−̇`, `⊂̇` and `=` of relations unfolded). -/
local macro "rel_simp" : tactic =>
  `(tactic| simp only [rel_eq_iff, RSub, rcap, rcup, rneg, rdiff, rNull, rV, eq_self_iff_true,
    and_self, not_true_eq_false, iff_false, iff_true, ← forall_and])

/-- Proves a statement of the relation calculus that holds pointwise by propositional logic. -/
local macro "pm_rel" : tactic =>
  `(tactic| (rel_simp <;> first
    | (intro x y; tauto)
    | exact forall_congr' fun x => forall_congr' fun y => by tauto
    | (intro h x y; have := h x y; tauto)
    | (intro h; exact forall_congr' fun x => forall_congr' fun y => by have := h x y; tauto)))

/-!
## [✱23] Calculus of relations

*(Vol. 1, p. 226)*

> *Summary of* *23.
>
> The definitions and propositions of this number are to be exact analogues of those of *22. Properties of relations which have no analogues for classes will not be dealt with till Section D. Proofs will be omitted in the present number, as they are precisely analogous to those of analogous propositions in *22. In this number, as always in future, capital Latin letters stand for expressions of the form \(\hat{x}\hat{y}{\phi}!(x, y)\), or, where they are not being used as apparent variables, for \(\hat{x}\hat{y}{\phi}(x, y)\). The principal propositions of this number are the analogues of those of *22.

**Lean reading.** A relation is `R : α → β → Prop` (heterogeneous; PM's capital letters), and
the relation `x̂ŷ φ(x, y)` is `fun x y => φ x y`. The dotted signs are the definitions of
`Defs/Part1`: `R ⊂̇ S` is `R ⪽ S`, `R ∩̇ S` is `R ⩀ S`, `R ∪̇ S` is `R ⊍ S`, `−̇R` is `∸R` and
`R −̇ S` is `R ∸ S`; identity of relations is Lean's `=` on `α → β → Prop`, so extensionality
(✱23·41) is `rel_eq_iff` (funext and propext). `R ∩̇ S ∈ Rel` is membership in the defined class
`Rel` of ✱21·03. Hypotheses `A . B . ⊃ . C` are conjunctions `A ∧ B → C`. The Dfs ✱23·01–·05,
·53, ·71 state the defining equations (✱23·02 with the `R` that the e-text omits). ✱23·351 needs
inhabited types (PM's tacit assumption). ✱23·81 is printed as corrected by the Additional Errata.

**Status.** proved (all propositions; ✱23·01–·05, ✱23·53, ✱23·71 definition; ✱23·351 proved
(reading): `[Nonempty α] [Nonempty β]`, see its docstring).
-/

/-- ✱23·01 (Df). \(R \unicode{x2abd} S.=:xRy.\supset_{x,y}.xSy \quad \text{Df}\) -/
theorem pm23_01 {R S : α → β → Prop} : R ⪽ S ↔ ∀ x y, R x y → S x y := Iff.rfl

/-- ✱23·02 (Df). \(\dot{\cap} S = \hat{x}\hat{y}(xRy.xSy) \quad \text{Df}\)

(The e-text omits the `R` of the definiendum: PM has `R ∩̇ S = x̂ŷ(xRy . xSy)`, cf. ✱23·2 and the
Introduction, p. 31.)

**Status.** definition: the transcription error of the e-text (missing `R`) is corrected. -/
theorem pm23_02 {R S : α → β → Prop} : R ⩀ S = fun x y => R x y ∧ S x y := rfl

/-- ✱23·03 (Df). \(R \unicode{x228d} S = \hat{x}\hat{y}(xRy .\lor. xSy) \quad \text{Df}\) -/
theorem pm23_03 {R S : α → β → Prop} : R ⊍ S = fun x y => R x y ∨ S x y := rfl

/-- ✱23·04 (Df). \(\unicode{x2238} R = \hat{x}\hat{y}\{{\sim}(xRy)\} \quad \text{Df}\) -/
theorem pm23_04 {R : α → β → Prop} : ∸R = fun x y => ¬R x y := rfl

/-- ✱23·05 (Df). \(R \unicode{x2238}S = R \dot{\cap} \unicode{x2238}S \quad \text{Df}\) -/
theorem pm23_05 {R S : α → β → Prop} : R ∸ S = R ⩀ ∸S := rfl

/-- ✱23·1. \(\vdash \colon\ldotp R \unicode{x2abd} S .\equiv: xRy .\supset_{x,y}. xSy\) -/
theorem pm23_1 {R S : α → β → Prop} : R ⪽ S ↔ ∀ x y, R x y → S x y := Iff.rfl

/-- ✱23·2. \(\vdash . R \dot{\cap} S = \hat{x}\hat{y}(xRy . xSy)\) -/
theorem pm23_2 {R S : α → β → Prop} : R ⩀ S = fun x y => R x y ∧ S x y := rfl

/-- ✱23·3. \(\vdash . R \unicode{x228d} S = \hat{x}\hat{y}(xRy .\lor. xSy)\) -/
theorem pm23_3 {R S : α → β → Prop} : R ⊍ S = fun x y => R x y ∨ S x y := rfl

/-- ✱23·31. \(\vdash . \unicode{x2238}R = \hat{x}\hat{y}\{{\sim}(xRy)\}\) -/
theorem pm23_31 {R : α → β → Prop} : ∸R = fun x y => ¬R x y := rfl

/-- ✱23·32. \(\vdash . R \unicode{x2238} S = \hat{x}\hat{y}\{xRy . {\sim}(xSy)\}\) -/
theorem pm23_32 {R S : α → β → Prop} : R ∸ S = fun x y => R x y ∧ ¬S x y := rfl

/-- ✱23·33. \(\vdash :x(R \dot{\cap} S)y .\equiv. xRy . xSy\) -/
theorem pm23_33 {R S : α → β → Prop} {x : α} {y : β} : (R ⩀ S) x y ↔ R x y ∧ S x y := Iff.rfl

/-- ✱23·34. \(\vdash \colon\ldotp x(R \unicode{x228d} S)y .\equiv: x R y .\lor. x S y\) -/
theorem pm23_34 {R S : α → β → Prop} {x : α} {y : β} : (R ⊍ S) x y ↔ R x y ∨ S x y := Iff.rfl

/-- ✱23·35. \(\vdash : x \unicode{x2238}R y .\equiv. {\sim}(x R y)\) -/
theorem pm23_35 {R : α → β → Prop} {x : α} {y : β} : (∸R) x y ↔ ¬R x y := Iff.rfl

/-- ✱23·351. \(\vdash . \unicode{x2238}R \neq R\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; cf. the
note after ✱24·52, which traces ✱24·1 back to ✱23·351 and ✱10·1). If `α` or `β` is empty there
is only one relation `α → β → Prop`, and `−̇R = R`; so `[Nonempty α] [Nonempty β]` is added. -/
theorem pm23_351 [Nonempty α] [Nonempty β] {R : α → β → Prop} : ∸R ≠ R := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty α›
  obtain ⟨y⟩ := ‹Nonempty β›
  have h' : ¬R x y ↔ R x y := Iff.of_eq (congrFun (congrFun h x) y)
  exact iff_not_self h'.symm

/-- ✱23·36. \(\vdash . R \dot{\cap} S \in \text{Rel}\) -/
theorem pm23_36 {R S : α → β → Prop} : R ⩀ S ∈ (Rel : Set (α → β → Prop)) := ⟨R ⩀ S, rfl⟩

/-- ✱23·37. \(\vdash . R \unicode{x228d} S \in \text{Rel}\) -/
theorem pm23_37 {R S : α → β → Prop} : R ⊍ S ∈ (Rel : Set (α → β → Prop)) := ⟨R ⊍ S, rfl⟩

/-- ✱23·38. \(\vdash . \unicode{x2238}R \in \text{Rel}\) -/
theorem pm23_38 {R : α → β → Prop} : ∸R ∈ (Rel : Set (α → β → Prop)) := ⟨∸R, rfl⟩

/-- ✱23·39. \(\vdash.\hat{x}\hat{y}\phi(x,y)\dot{\cap}\hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\{\phi(x,y).\psi(x,y)\}\) -/
theorem pm23_39 {φ ψ : α → β → Prop} :
    (fun x y => φ x y) ⩀ (fun x y => ψ x y) = fun x y => φ x y ∧ ψ x y := rfl

/-- ✱23·391. \(\vdash.\hat{x}\hat{y}\phi(x,y)\unicode{x228d}\hat{x}\hat{y}\psi(x,y)=\hat{x}\hat{y}\{\phi(x,y).\lor.\psi(x,y)\}\) -/
theorem pm23_391 {φ ψ : α → β → Prop} :
    (fun x y => φ x y) ⊍ (fun x y => ψ x y) = fun x y => φ x y ∨ ψ x y := rfl

/-- ✱23·392. \(\vdash.\dot{-}\hat{x}\hat{y}\phi(x,y)=\hat{x}\hat{y}\{{\sim}\phi(x,y)\}\) -/
theorem pm23_392 {φ : α → β → Prop} : ∸(fun x y => φ x y) = fun x y => ¬φ x y := rfl

/-- ✱23·4. \(\vdash\colon\ldotp R\unicode{x2abd}S.S\unicode{x2abd}R.\equiv:xRy.\equiv_{x,y}.xSy\) -/
theorem pm23_4 {R S : α → β → Prop} : R ⪽ S ∧ S ⪽ R ↔ ∀ x y, R x y ↔ S x y :=
  ⟨fun h x y => ⟨h.1 x y, h.2 x y⟩, fun h => ⟨fun x y => (h x y).1, fun x y => (h x y).2⟩⟩

/-- ✱23·41. \(\vdash:R\unicode{x2abd}S.S\unicode{x2abd}R.\equiv.R=S\) -/
theorem pm23_41 {R S : α → β → Prop} : R ⪽ S ∧ S ⪽ R ↔ R = S := pm23_4.trans rel_eq_iff.symm

/-- ✱23·42. \(\vdash.R\unicode{x2abd}R\) -/
theorem pm23_42 {R : α → β → Prop} : R ⪽ R := fun _ _ => id

/-- ✱23·43. \(\vdash.R\dot{\cap}S\unicode{x2abd}R\) -/
theorem pm23_43 {R S : α → β → Prop} : R ⩀ S ⪽ R := fun _ _ h => h.1

/-- ✱23·44. \(\vdash:R\unicode{x2abd}S.S\unicode{x2abd}T.\supset.R\unicode{x2abd}T\) -/
theorem pm23_44 {R S T : α → β → Prop} : R ⪽ S ∧ S ⪽ T → R ⪽ T :=
  fun h x y hR => h.2 x y (h.1 x y hR)

/-- ✱23·441. \(\vdash:R\unicode{x2abd}S.xRy.\supset.xSy\) -/
theorem pm23_441 {R S : α → β → Prop} {x : α} {y : β} : R ⪽ S ∧ R x y → S x y :=
  fun h => h.1 x y h.2

/-- ✱23·45. \(\vdash:R\unicode{x2abd}S.R\unicode{x2abd}T.\supset.R\unicode{x2abd}S\dot{\cap}T\) -/
theorem pm23_45 {R S T : α → β → Prop} : R ⪽ S ∧ R ⪽ T → R ⪽ S ⩀ T :=
  fun h x y hR => ⟨h.1 x y hR, h.2 x y hR⟩

/-- ✱23·46. \(\vdash:xRy.R\unicode{x2abd}S.\supset.xSy\) -/
theorem pm23_46 {R S : α → β → Prop} {x : α} {y : β} : R x y ∧ R ⪽ S → S x y :=
  fun h => h.2 x y h.1

/-- ✱23·47. \(\vdash:R\unicode{x2abd}T.\supset.R\dot{\cap}S\unicode{x2abd}T\) -/
theorem pm23_47 {R S T : α → β → Prop} : R ⪽ T → R ⩀ S ⪽ T := fun h x y hRS => h x y hRS.1

/-- ✱23·48. \(\vdash:R\unicode{x2abd}S.\supset.R\dot{\cap}T\unicode{x2abd}S\dot{\cap}T\) -/
theorem pm23_48 {R S T : α → β → Prop} : R ⪽ S → R ⩀ T ⪽ S ⩀ T :=
  fun h x y hRT => ⟨h x y hRT.1, hRT.2⟩

/-- ✱23·481. \(\vdash:R=S.\supset.R\dot{\cap}T=S\dot{\cap}T\) -/
theorem pm23_481 {R S T : α → β → Prop} : R = S → R ⩀ T = S ⩀ T := fun h => h ▸ rfl

/-- ✱23·49. \(\vdash:P\unicode{x2abd}Q.R\unicode{x2abd}S.\supset.P\dot{\cap}R\unicode{x2abd}Q\dot{\cap}S\) -/
theorem pm23_49 {P Q R S : α → β → Prop} : P ⪽ Q ∧ R ⪽ S → P ⩀ R ⪽ Q ⩀ S :=
  fun h x y hPR => ⟨h.1 x y hPR.1, h.2 x y hPR.2⟩

/-- ✱23·5. \(\vdash.R\dot{\cap}R=R\) -/
theorem pm23_5 {R : α → β → Prop} : R ⩀ R = R := by pm_rel

/-- ✱23·51. \(\vdash.R\dot{\cap}S=S\dot{\cap}R\) -/
theorem pm23_51 {R S : α → β → Prop} : R ⩀ S = S ⩀ R := by pm_rel

/-- ✱23·52. \(\vdash.(R\dot{\cap}S)\dot{\cap}T=R\dot{\cap}(S\dot{\cap}T)\) -/
theorem pm23_52 {R S T : α → β → Prop} : (R ⩀ S) ⩀ T = R ⩀ (S ⩀ T) := by pm_rel

/-- ✱23·53 (Df). \(R\dot{\cap}S\dot{\cap}T=(R\dot{\cap}S)\dot{\cap}T \quad\text{Df}\) -/
theorem pm23_53 {R S T : α → β → Prop} : R ⩀ S ⩀ T = (R ⩀ S) ⩀ T := rfl

/-- ✱23·54. \(\vdash\colon\ldotp R=S.\supset:R\unicode{x2abd}T.\equiv.S\unicode{x2abd}T\) -/
theorem pm23_54 {R S T : α → β → Prop} : R = S → (R ⪽ T ↔ S ⪽ T) := fun h => h ▸ Iff.rfl

/-- ✱23·55. \(\vdash\colon\ldotp R=S.\supset:T\unicode{x2abd}R.\equiv.T\unicode{x2abd}S\) -/
theorem pm23_55 {R S T : α → β → Prop} : R = S → (T ⪽ R ↔ T ⪽ S) := fun h => h ▸ Iff.rfl

/-- ✱23·551. \(\vdash:R=S.\supset.R\unicode{x228d}T=S\unicode{x228d}T\) -/
theorem pm23_551 {R S T : α → β → Prop} : R = S → R ⊍ T = S ⊍ T := fun h => h ▸ rfl

/-- ✱23·56. \(\vdash.R\unicode{x228d}R=R\) -/
theorem pm23_56 {R : α → β → Prop} : R ⊍ R = R := by pm_rel

/-- ✱23·57. \(\vdash.R\unicode{x228d}S=S\unicode{x228d}R\) -/
theorem pm23_57 {R S : α → β → Prop} : R ⊍ S = S ⊍ R := by pm_rel

/-- ✱23·58. \(\vdash.R\unicode{x2abd}R\unicode{x228d}S.S\unicode{x2abd}R\unicode{x228d}S\) -/
theorem pm23_58 {R S : α → β → Prop} : R ⪽ R ⊍ S ∧ S ⪽ R ⊍ S :=
  ⟨fun _ _ => Or.inl, fun _ _ => Or.inr⟩

/-- ✱23·59. \(\vdash:R\unicode{x2abd}T.S\unicode{x2abd}T.\equiv.R\unicode{x228d}S\unicode{x2abd}T\) -/
theorem pm23_59 {R S T : α → β → Prop} : R ⪽ T ∧ S ⪽ T ↔ R ⊍ S ⪽ T := by pm_rel

/-- ✱23·6. \(\vdash\colon\ldotp x(R\unicode{x228d}S)y.\equiv:R\unicode{x2abd}T.S\unicode{x2abd}T.\supset_{T}.xTy\) -/
theorem pm23_6 {R S : α → β → Prop} {x : α} {y : β} :
    (R ⊍ S) x y ↔ ∀ T : α → β → Prop, R ⪽ T ∧ S ⪽ T → T x y := by
  constructor
  · rintro (h | h) T ⟨hR, hS⟩
    exacts [hR x y h, hS x y h]
  · intro h
    exact h (R ⊍ S) ⟨fun _ _ => Or.inl, fun _ _ => Or.inr⟩

/-- ✱23·61. \(\vdash:R\unicode{x2abd}S.\supset.R\unicode{x2abd}S\unicode{x228d}T\) -/
theorem pm23_61 {R S T : α → β → Prop} : R ⪽ S → R ⪽ S ⊍ T := fun h x y hR => Or.inl (h x y hR)

/-- ✱23·62. \(\vdash:R\unicode{x2abd}S.\equiv.R\unicode{x228d}S=S\) -/
theorem pm23_62 {R S : α → β → Prop} : R ⪽ S ↔ R ⊍ S = S := by pm_rel

/-- ✱23·621. \(\vdash:R\unicode{x2abd}S.\equiv.R\dot{\cap}S=R\) -/
theorem pm23_621 {R S : α → β → Prop} : R ⪽ S ↔ R ⩀ S = R := by pm_rel

/-- ✱23·63. \(\vdash.R\unicode{x228d}(R\dot{\cap}S)=R\) -/
theorem pm23_63 {R S : α → β → Prop} : R ⊍ (R ⩀ S) = R := by pm_rel

/-- ✱23·631. \(\vdash.R\dot{\cap}(R\unicode{x228d}S)=R\) -/
theorem pm23_631 {R S : α → β → Prop} : R ⩀ (R ⊍ S) = R := by pm_rel

/-- ✱23·632. \(\vdash:R=S.\supset.R=R\dot{\cap}S\) -/
theorem pm23_632 {R S : α → β → Prop} : R = S → R = R ⩀ S := by pm_rel

/-- ✱23·633. \(\vdash:R\unicode{x2abd}S.\supset.R\unicode{x228d}T=(R\dot{\cap}S)\unicode{x228d}T\) -/
theorem pm23_633 {R S T : α → β → Prop} : R ⪽ S → R ⊍ T = (R ⩀ S) ⊍ T := by pm_rel

/-- ✱23·64. \(\vdash\colon\ldotp R\unicode{x2abd}T.\lor.S\unicode{x2abd}T:\supset.R\dot{\cap}S\unicode{x2abd}T\) -/
theorem pm23_64 {R S T : α → β → Prop} : (R ⪽ T ∨ S ⪽ T) → R ⩀ S ⪽ T := by
  rintro (h | h) x y ⟨hR, hS⟩
  exacts [h x y hR, h x y hS]

/-- ✱23·65. \(\vdash\colon\ldotp R\unicode{x2abd}S.\lor.R\unicode{x2abd}T:\supset.R\unicode{x2abd}S\unicode{x228d}T\) -/
theorem pm23_65 {R S T : α → β → Prop} : (R ⪽ S ∨ R ⪽ T) → R ⪽ S ⊍ T := by
  rintro (h | h) x y hR
  exacts [Or.inl (h x y hR), Or.inr (h x y hR)]

/-- ✱23·66. \(\vdash:R\unicode{x2abd}S.\supset.R\unicode{x228d}T\unicode{x2abd}S\unicode{x228d}T\) -/
theorem pm23_66 {R S T : α → β → Prop} : R ⪽ S → R ⊍ T ⪽ S ⊍ T := by pm_rel

/-- ✱23·68. \(\vdash.(R\dot{\cap}S)\unicode{x228d}(R\dot{\cap}T)=R\dot{\cap}(S\unicode{x228d}T)\) -/
theorem pm23_68 {R S T : α → β → Prop} : (R ⩀ S) ⊍ (R ⩀ T) = R ⩀ (S ⊍ T) := by pm_rel

/-- ✱23·69. \(\vdash.(R\unicode{x228d}S)\dot{\cap}(R\unicode{x228d}T)=R\unicode{x228d}(S\dot{\cap}T)\) -/
theorem pm23_69 {R S T : α → β → Prop} : (R ⊍ S) ⩀ (R ⊍ T) = R ⊍ (S ⩀ T) := by pm_rel

/-- ✱23·7. \(\vdash.(R\unicode{x228d}S)\unicode{x228d}T=R\unicode{x228d}(S\unicode{x228d}T)\) -/
theorem pm23_7 {R S T : α → β → Prop} : (R ⊍ S) ⊍ T = R ⊍ (S ⊍ T) := by pm_rel

/-- ✱23·71 (Df). \(R\unicode{x228d}S\unicode{x228d}T=(R\unicode{x228d}S)\unicode{x228d}T \quad{\text{Df}}\) -/
theorem pm23_71 {R S T : α → β → Prop} : R ⊍ S ⊍ T = (R ⊍ S) ⊍ T := rfl

/-- ✱23·72. \(\vdash:P\unicode{x2abd}R.Q\unicode{x2abd}S.\supset.P\unicode{x228d}Q\unicode{x2abd}R\unicode{x228d}S\) -/
theorem pm23_72 {P Q R S : α → β → Prop} : P ⪽ R ∧ Q ⪽ S → P ⊍ Q ⪽ R ⊍ S := by pm_rel

/-- ✱23·73. \(\vdash:P=R.Q=S.\supset.P\unicode{x228d}Q=R\unicode{x228d}S\) -/
theorem pm23_73 {P Q R S : α → β → Prop} : P = R ∧ Q = S → P ⊍ Q = R ⊍ S := by
  rintro ⟨rfl, rfl⟩
  rfl

/-- ✱23·74. \(\vdash:P\dot{\cap}Q\unicode{x2abd}R.P\dot{\cap}R\unicode{x2abd}Q.\equiv.P\dot{\cap}Q=P\dot{\cap}R\) -/
theorem pm23_74 {P Q R : α → β → Prop} :
    P ⩀ Q ⪽ R ∧ P ⩀ R ⪽ Q ↔ P ⩀ Q = P ⩀ R := by pm_rel

/-- ✱23·8. \(\vdash.\dot{-}(\dot{-}R)=R\) -/
theorem pm23_8 {R : α → β → Prop} : ∸(∸R) = R := by pm_rel

/-- ✱23·81. \(\vdash:R\unicode{x2abd}S.\equiv.\dot{-}S\unicode{x2abd}\dot{-}R\)

**Status.** proved: the e-text already incorporates the erratum (Additional Errata to Vol. I,
p. 228: read `−̇S ⊂̇ −̇R` for `−̇R ⊂̇ −̇S`). -/
theorem pm23_81 {R S : α → β → Prop} : R ⪽ S ↔ ∸S ⪽ ∸R := by pm_rel

/-- ✱23·811. \(\vdash:R\unicode{x2abd}\dot{-}S.\equiv.S\unicode{x2abd}\dot{-}R\) -/
theorem pm23_811 {R S : α → β → Prop} : R ⪽ ∸S ↔ S ⪽ ∸R := by pm_rel

/-- ✱23·82. \(\vdash:R\dot{\cap}S\unicode{x2abd}T.\equiv.R\dot{-}T\unicode{x2abd}\dot{-}S\) -/
theorem pm23_82 {R S T : α → β → Prop} : R ⩀ S ⪽ T ↔ R ∸ T ⪽ ∸S := by pm_rel

/-- ✱23·83. \(\vdash:R=S.\equiv.\dot{-}R=\dot{-}S\) -/
theorem pm23_83 {R S : α → β → Prop} : R = S ↔ ∸R = ∸S := by pm_rel

/-- ✱23·831. \(\vdash:R=\dot{-}S.\equiv.S=\dot{-}R\) -/
theorem pm23_831 {R S : α → β → Prop} : R = ∸S ↔ S = ∸R := by pm_rel

/-- ✱23·84. \(\vdash.\dot{-}(R\dot{\cap}S)=\dot{-}R\unicode{x228d}\dot{-}S\) -/
theorem pm23_84 {R S : α → β → Prop} : ∸(R ⩀ S) = ∸R ⊍ ∸S := by pm_rel

/-- ✱23·85. \(\vdash.R\dot{\cap}S=\dot{-}(\dot{-}R\unicode{x228d}\dot{-}S)\) -/
theorem pm23_85 {R S : α → β → Prop} : R ⩀ S = ∸(∸R ⊍ ∸S) := by pm_rel

/-- ✱23·86. \(\vdash.\dot{-}(\dot{-}R\dot{\cap}\dot{-}S)=R\unicode{x228d}S\) -/
theorem pm23_86 {R S : α → β → Prop} : ∸(∸R ⩀ ∸S) = R ⊍ S := by pm_rel

/-- ✱23·87. \(\vdash.\dot{-}R\dot{\cap}\dot{-}S=\dot{-}(R\unicode{x228d}S)\) -/
theorem pm23_87 {R S : α → β → Prop} : ∸R ⩀ ∸S = ∸(R ⊍ S) := by pm_rel

/-- ✱23·88. \(\vdash.(x,y).x(R\unicode{x228d}\dot{-}R)y\) -/
theorem pm23_88 {R : α → β → Prop} : ∀ x y, (R ⊍ ∸R) x y := fun x y => em (R x y)

/-- ✱23·89. \(\vdash.(x,y).{\sim}\{x(R\dot{-}R)y\}\) -/
theorem pm23_89 {R : α → β → Prop} : ∀ x y, ¬(R ∸ R) x y := fun _ _ h => h.2 h.1

/-- ✱23·9. \(\vdash.(R\unicode{x228d}S)\dot{-}S=R\dot{-}S\) -/
theorem pm23_9 {R S : α → β → Prop} : (R ⊍ S) ∸ S = R ∸ S := by pm_rel

/-- ✱23·91. \(\vdash.R\unicode{x228d}S=R\unicode{x228d}(S\dot{-}R)\) -/
theorem pm23_91 {R S : α → β → Prop} : R ⊍ S = R ⊍ (S ∸ R) := by pm_rel

/-- ✱23·92. \(\vdash:R\unicode{x2abd}S.\supset.S=R\unicode{x228d}(S\dot{-}R)\) -/
theorem pm23_92 {R S : α → β → Prop} : R ⪽ S → S = R ⊍ (S ∸ R) := by pm_rel

/-- ✱23·93. \(\vdash.R\dot{-}S=R\dot{-}(R\dot{\cap}S)\) -/
theorem pm23_93 {R S : α → β → Prop} : R ∸ S = R ∸ (R ⩀ S) := by pm_rel

/-- ✱23·94. \(\vdash:(R).fR.\equiv.(R).f(\dot{-}R)\) -/
theorem pm23_94 {f : (α → β → Prop) → Prop} : (∀ R, f R) ↔ ∀ R, f (∸R) :=
  ⟨fun h _ => h _, fun h R => by simpa only [pm23_8] using h (∸R)⟩

/-- ✱23·95. \(\vdash:(\exists R).fR.\equiv.(\exists R).f(\dot{-}R)\) -/
theorem pm23_95 {f : (α → β → Prop) → Prop} : (∃ R, f R) ↔ ∃ R, f (∸R) :=
  ⟨fun ⟨R, hR⟩ => ⟨∸R, by simpa only [pm23_8] using hR⟩, fun ⟨_, hR⟩ => ⟨_, hR⟩⟩

/-!
## [✱24] The universal class, the null-class, and the existence of classes

*(Vol. 1, p. 229)*

> *Summary of* *24.
>
> The universal class, denoted by \(\text{V}\), is the class of all objects of the type which, in the given context, is being denoted by small Latin letters, *i.e.* of the lowest type concerned. Thus \(\text{V}\), like "\(\text{Cls}\)," is ambiguous as to type. Its definition is as follows:
>
> *24·01. \(\text{V} = \hat{x}(x = x) \quad \text{Df}\)
>
> Any other property possessed by everything would do as well as "\(x = x\)," but this is the only such property which we have hitherto studied.
>
> The null-class, denoted by \(\Lambda\), is the class which has no members. Like \(\text{V}\), it is ambiguous as to type. We use the same symbol, \(\Lambda\), for null-classes of various types; but these null-classes differ. The type of \(\Lambda\) is determined by that of the terms \(x\) concerning which "\(x \in \Lambda\)" is false: whatever \(x\) may be, "\(x \in \Lambda\)" will not represent a *true* proposition, but unless \(x\) is of the appropriate type, "\(x \in \Lambda\)" will be meaningless, not false. Thus \(\Lambda\) is of the type next above that of an \(x\) concerning which "\(x \in \Lambda\)" is significant and false. The definition of \(\Lambda\) is
>
> …

**Lean reading.** Classes are `Set α`; `V` and `Λ` are PM's definitions (`V_eq_univ`,
`Null_eq_empty`), `−α` is `Aᶜ`, `α − β` is `A \ B`, PM's `⊂` is `⊆`, and PM's `∃!α` ("α has
members") is `A.Nonempty`. The letters α, β, γ, ξ, ξ', η, η', κ are `A, B, C, X, X', Y, Y', K`.
Products of hypotheses are left-nested conjunctions; chains (✱24·4) are conjunctions of the links.
✱24·1 and ✱24·52 need an inhabited type (`[Nonempty α]`, PM's tacit assumption, explained by PM
after ✱24·52). The e-text misprints ✱24·21 and ✱24·311 (`V` for `Λ`), ✱24·45 (a stray `⊂`) and
✱24·55·58·6 (`⊃` for `⊂`); the corrections are confirmed by the summary of ✱24, the
demonstrations and later uses. ✱24·431 is false as printed (and the errata do not correct it);
the intended form, which ✱24·44 needs, is proved, with the failure of the printed form. ✱24·51,
which the e-text runs into the comment after ✱24·5, is added as `pm24_51`.

**Status.** proved (all propositions; ✱24·01–·03 definition; ✱24·1, ✱24·52 proved (reading):
`[Nonempty α]`; ✱24·21, ✱24·311, ✱24·45, ✱24·55, ✱24·58, ✱24·6 proved (reading): e-text
transcription errors; ✱24·431 proved (corrected); see their docstrings).
-/

/-- ✱24·01 (Df). \(\text{V} =\hat{x}(x=x) \quad\text{Df}\) -/
theorem pm24_01 : (V : Set α) = {x | x = x} := rfl

/-- ✱24·02 (Df). \(\Lambda =- \text{V} \quad\text{Df}\) -/
theorem pm24_02 : (Λ : Set α) = Vᶜ := rfl

/-- ✱24·03 (Df). \(\exists!\alpha.=.(\exists x).x \in \alpha \quad\text{Df} \quad\text{Df}\)

(The e-text prints "Df" twice.) -/
theorem pm24_03 {A : Set α} : A.Nonempty ↔ ∃ x, x ∈ A := Iff.rfl

/-- ✱24·1. \(\vdash.\Lambda\neq\text{V} \quad[\text{*22·351.(*24·02)}]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; see the
note after ✱24·52). For an empty type `α`, `Λ = V`; so `[Nonempty α]` is added. -/
theorem pm24_1 [Nonempty α] : (Λ : Set α) ≠ V := by
  rw [Null_eq_empty, V_eq_univ]
  exact Set.empty_ne_univ

/-- ✱24·101. \(\vdash.\text{V} = -\Lambda \quad[\text{*22·831.(*24·02)}]\) -/
theorem pm24_101 : (V : Set α) = Λᶜ := by
  rw [Null, compl_compl]

/-- ✱24·102. \(\vdash\colon(x).\phi x.\equiv.\hat{z}(\phi z) = \text{V}\) -/
theorem pm24_102 {φ : α → Prop} : (∀ x, φ x) ↔ {z | φ z} = V := by pm_cls

/-- ✱24·103. \(\vdash\colon(x).{\sim}\phi x.\equiv.\hat{z}(\phi z)=\Lambda\) -/
theorem pm24_103 {φ : α → Prop} : (∀ x, ¬φ x) ↔ {z | φ z} = Λ := by pm_cls

/-- ✱24·104. \(\vdash.(x).x\in\text{V}\) -/
theorem pm24_104 : ∀ x : α, x ∈ V := fun x => (rfl : x = x)

/-- ✱24·105. \(\vdash.(x).x{\sim}\in\Lambda\) -/
theorem pm24_105 : ∀ x : α, x ∉ Λ := fun _ h => h rfl

/-- ✱24·11. \(\vdash.(\alpha).\alpha\subset\text{V}\) -/
theorem pm24_11 : ∀ A : Set α, A ⊆ V := fun _ x _ => (rfl : x = x)

/-- ✱24·12. \(\vdash.(\alpha).\Lambda\subset\alpha\) -/
theorem pm24_12 : ∀ A : Set α, Λ ⊆ A := fun _ x h => absurd h (pm24_105 x)

/-- ✱24·13. \(\vdash\colon \alpha=\Lambda.\equiv.\alpha\subset\Lambda\) -/
theorem pm24_13 {A : Set α} : A = Λ ↔ A ⊆ Λ := by pm_cls

/-- ✱24·14. \(\vdash\colon(x).x \in \alpha.\equiv.\alpha=\text{V}\) -/
theorem pm24_14 {A : Set α} : (∀ x, x ∈ A) ↔ A = V := by pm_cls

/-- ✱24·141. \(\vdash\colon\text{V}\subset\alpha.\equiv.\text{V}=\alpha\) -/
theorem pm24_141 {A : Set α} : V ⊆ A ↔ V = A := by pm_cls

/-- ✱24·15. \(\vdash\colon(x).x{\sim}\in\alpha.\equiv.\alpha=\Lambda\) -/
theorem pm24_15 {A : Set α} : (∀ x, x ∉ A) ↔ A = Λ := by pm_cls

/-- ✱24·17. \(\vdash\colon \alpha=\text{V}.\equiv.- \alpha=\Lambda \quad[\text{*22·83.(*24·02)}]\) -/
theorem pm24_17 {A : Set α} : A = V ↔ Aᶜ = Λ := by pm_cls

/-- ✱24·21. \(\vdash.\alpha\cap - \alpha=\text{V} \quad[\text{*24·103.*22·89}]\)

**Status.** proved (reading): transcription error of the e-text, which prints `V` for `Λ` (as
printed the proposition is false for every inhabited type). PM's ✱24·21 is `α ∩ −α = Λ`, the law
of contradiction: so stated in the Introduction to Section C (Huntington's postulate V) and in
the summary of ✱24 ("nothing is both α and not-α"), cited from ✱24·103 and ✱22·89, and used
as `γ − γ = Λ` in the proofs of ✱24·431, ✱24·495 and ✱24·6. -/
theorem pm24_21 {A : Set α} : A ∩ Aᶜ = Λ := by pm_cls

/-- ✱24·22. \(\vdash.\alpha\cup - \alpha=\text{V} \quad[\text{*22·88.*24·102}]\) -/
theorem pm24_22 {A : Set α} : A ∪ Aᶜ = V := by pm_cls

/-- ✱24·23. \(\vdash.\alpha\cap\Lambda=\Lambda \quad[\text{*24·12.*22·621}]\) -/
theorem pm24_23 {A : Set α} : A ∩ Λ = Λ := by pm_cls

/-- ✱24·24. \(\vdash.\alpha\cup\Lambda=\alpha \quad[\text{*24·12.*22·62}]\) -/
theorem pm24_24 {A : Set α} : A ∪ Λ = A := by pm_cls

/-- ✱24·26. \(\vdash.\alpha\cap\text{V}=\alpha \quad[\text{*22·621.*24·11}]\) -/
theorem pm24_26 {A : Set α} : A ∩ V = A := by pm_cls

/-- ✱24·27. \(\vdash.\alpha\cup\text{V}=\text{V} \quad[\text{*22·62.*24·11}]\) -/
theorem pm24_27 {A : Set α} : A ∪ V = V := by pm_cls

/-- ✱24·3. \(\vdash\colon\alpha\subset\beta.\equiv.\alpha - \beta=\Lambda\) -/
theorem pm24_3 {A B : Set α} : A ⊆ B ↔ A \ B = Λ := by pm_cls

/-- ✱24·31. \(\vdash\colon \alpha\subset\beta.\equiv.-\alpha\cup\beta=\text{V}\) -/
theorem pm24_31 {A B : Set α} : A ⊆ B ↔ Aᶜ ∪ B = V := by pm_cls

/-- ✱24·311. \(\vdash\colon \alpha\subset - \beta.\equiv.\alpha\cap\beta=\text{V}\)

**Status.** proved (reading): transcription error of the e-text, which prints `V` for `Λ` (false
as printed). PM's ✱24·311 is `α ⊂ −β . ≡ . α ∩ β = Λ`: so printed in the summary of ✱24 ("no α
is a β" is equivalent to "nothing is both α and β"), obtained by the last line of the
demonstration (✱24·15), and so used in ✱24·313, ✱24·39, ✱24·4, ✱24·46, ✱24·47 and ✱37·461. -/
theorem pm24_311 {A B : Set α} : A ⊆ Bᶜ ↔ A ∩ B = Λ := by pm_cls

/-- ✱24·312. \(\vdash\colon - \alpha\subset\beta.\equiv.\alpha\cup\beta=\text{V}\) -/
theorem pm24_312 {A B : Set α} : Aᶜ ⊆ B ↔ A ∪ B = V := by pm_cls

/-- ✱24·313. \(\vdash\colon\alpha\cap\beta=\Lambda.\equiv.\alpha=\alpha -\beta \quad[\text{*24·311.*22·621}]\) -/
theorem pm24_313 {A B : Set α} : A ∩ B = Λ ↔ A = A \ B := by pm_cls

/-- ✱24·32. \(\vdash\colon\ldotp\alpha\cup\beta=\Lambda.\equiv.\alpha=\Lambda.\beta=\Lambda\) -/
theorem pm24_32 {A B : Set α} : A ∪ B = Λ ↔ A = Λ ∧ B = Λ := by pm_cls

/-- ✱24·33. \(\vdash\colon\alpha=\text{V}.\supset.\alpha\cup\beta=\text{V}\) -/
theorem pm24_33 {A B : Set α} : A = V → A ∪ B = V := by pm_cls

/-- ✱24·34. \(\vdash\colon \alpha=\Lambda.\supset.\alpha\cap\beta=\Lambda \quad[\text{*22·481.*24·23}]\) -/
theorem pm24_34 {A B : Set α} : A = Λ → A ∩ B = Λ := by pm_cls

/-- ✱24·35. \(\vdash\colon \alpha=\text{V}.\supset.\alpha\cap\beta=\beta \quad[\text{*22·481.*24·26}]\) -/
theorem pm24_35 {A B : Set α} : A = V → A ∩ B = B := by pm_cls

/-- ✱24·36. \(\vdash\colon \alpha=\Lambda.\supset.\alpha\cup\beta=\beta \quad[\text{*22·551.*24·24}]\) -/
theorem pm24_36 {A B : Set α} : A = Λ → A ∪ B = B := by pm_cls

/-- ✱24·37. \(\vdash\colon\ldotp \alpha\cap\beta=\Lambda.\equiv\colon x\in \alpha.y\in \beta.\supset_{x,y}.x\neq y\) -/
theorem pm24_37 {A B : Set α} : A ∩ B = Λ ↔ ∀ x y, x ∈ A ∧ y ∈ B → x ≠ y := by
  rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]
  constructor
  · rintro h x y ⟨hx, hy⟩ rfl
    exact h x ⟨hx, hy⟩
  · rintro h x ⟨hx, hy⟩
    exact h x x ⟨hx, hy⟩ rfl

/-- ✱24·38. \(\vdash\colon\ldotp \alpha\cap\beta=\Lambda.\supset\colon \alpha\neq\beta.\lor.\alpha=\Lambda.\beta=\Lambda\) -/
theorem pm24_38 {A B : Set α} : A ∩ B = Λ → A ≠ B ∨ (A = Λ ∧ B = Λ) := by
  intro h
  by_cases hAB : A = B
  · subst hAB
    rw [Set.inter_self] at h
    exact Or.inr ⟨h, h⟩
  · exact Or.inl hAB

/-- ✱24·39. \(\vdash\colon\ldotp \alpha\cap\beta=\Lambda.\equiv\colon x\in \alpha.\supset_{x}.x{\sim}\in\beta \quad[\text{*24·311.*22·35}]\) -/
theorem pm24_39 {A B : Set α} : A ∩ B = Λ ↔ ∀ x, x ∈ A → x ∉ B := by pm_cls

/-- ✱24·4. \(\vdash\colon \alpha\cap\beta=\Lambda.\equiv.(\alpha\cup\beta)- \alpha=\beta.\equiv.(\alpha\cup\beta)- \beta=\alpha\) -/
theorem pm24_4 {A B : Set α} :
    (A ∩ B = Λ ↔ (A ∪ B) \ A = B) ∧ ((A ∪ B) \ A = B ↔ (A ∪ B) \ B = A) := by
  cls_simp
  exact ⟨forall_congr' fun x => by tauto, forall_congr' fun x => by tauto⟩

/-- ✱24·401. \(\vdash\colon \beta\subset\alpha.\supset.(\beta\cup\gamma)- \alpha=\gamma- \alpha\) -/
theorem pm24_401 {A B C : Set α} : B ⊆ A → (B ∪ C) \ A = C \ A := by pm_cls

/-- ✱24·402. \(\vdash\colon\alpha\cap\beta=\Lambda.\xi\subset\alpha.\eta\subset\beta.\supset.\xi\cap\eta=\Lambda\) -/
theorem pm24_402 {A B X Y : Set α} : (A ∩ B = Λ ∧ X ⊆ A) ∧ Y ⊆ B → X ∩ Y = Λ := by
  pm_cls

/-- ✱24·41. \(\vdash.\alpha =(\alpha\cap\beta)\cup(\alpha - \beta\)) -/
theorem pm24_41 {A B : Set α} : A = (A ∩ B) ∪ (A \ B) := by pm_cls

/-- ✱24·411. \(\vdash\colon\beta\subset\alpha.\supset.\alpha =\beta\cup(\alpha - \beta\)) -/
theorem pm24_411 {A B : Set α} : B ⊆ A → A = B ∪ (A \ B) := by pm_cls

/-- ✱24·412. \(\vdash\colon\beta\subset\alpha.\gamma\subset\beta.\supset.(\alpha - \beta)\cup(\beta - \gamma)= \alpha - \gamma\) -/
theorem pm24_412 {A B C : Set α} : B ⊆ A ∧ C ⊆ B → (A \ B) ∪ (B \ C) = A \ C := by pm_cls

/-- ✱24·42. \(\vdash\colon\alpha\cap\beta\subset\gamma.\alpha - \beta\subset\gamma.\equiv.\alpha\subset\gamma\) -/
theorem pm24_42 {A B C : Set α} : A ∩ B ⊆ C ∧ A \ B ⊆ C ↔ A ⊆ C := by pm_cls

/-- ✱24·43. \(\vdash\colon \alpha - \beta\subset\gamma.\equiv.\alpha\subset\beta\cup\gamma\) -/
theorem pm24_43 {A B C : Set α} : A \ B ⊆ C ↔ A ⊆ B ∪ C := by pm_cls

/-- ✱24·431. \(\vdash.(\alpha\cup\gamma)\cap(\beta\cup - \gamma)=(\alpha\cap\gamma)\cup(\alpha - \gamma)\cup(\beta\cap\gamma\))

**Status.** proved (corrected): as printed, with first summand `α ∩ γ`, the right side is
`α ∪ (β ∩ γ)`, which is not the left side (for `α = γ = V`, `β = Λ` the left side is `Λ` and the
right side `V`; `pm24_431_printed_false`). The errata do not list it. PM intends
`(α ∩ β) ∪ (α − γ) ∪ (β ∩ γ)`: this is the right side of ✱24·432, with which ✱24·431 is combined
in ✱24·44 (`[*24·431·432]`); the first step of the demonstration (✱22·68) gives
`{(α ∪ γ) ∩ β} ∪ {(α ∪ γ) ∩ −γ}`, whose expansion is `(α ∩ β) ∪ (γ ∩ β) ∪ (α − γ) ∪ (γ − γ)`
(the e-text's demonstration repeats `α ∩ γ` for `α ∩ β`, and its last line prints `β ∩ −γ` for
`β ∩ γ`); and the analogue ✱25·431 has `P ∩̇ Q`. The corrected form is proved. Whether the
misprint is PM's or the e-text's cannot be decided from the e-text (the source scan is not
available here); in either case the formula as printed is false and is not in the errata. -/
theorem pm24_431 {A B C : Set α} :
    (A ∪ C) ∩ (B ∪ Cᶜ) = (A ∩ B) ∪ (A \ C) ∪ (B ∩ C) := by pm_cls

/-- The printed form of ✱24·431 (first summand `α ∩ γ`) is false: take `α = γ = V`, `β = Λ` in a
one-element type. -/
theorem pm24_431_printed_false :
    ¬ ∀ A B C : Set Unit, (A ∪ C) ∩ (B ∪ Cᶜ) = (A ∩ C) ∪ (A \ C) ∪ (B ∩ C) := by
  intro h
  have := Set.ext_iff.1 (h Set.univ ∅ Set.univ) ()
  simp at this

/-- ✱24·432. \(\vdash.(\alpha - \gamma)\cup(\beta\cap\gamma)=(\alpha\cap\beta)\cup(\alpha - \gamma)\cup(\beta\cap\gamma)\) -/
theorem pm24_432 {A B C : Set α} : (A \ C) ∪ (B ∩ C) = (A ∩ B) ∪ (A \ C) ∪ (B ∩ C) := by pm_cls

/-- ✱24·44. \(\vdash.(\alpha\cup\gamma)\cap(\beta\cup - \gamma)=(\alpha\cap - \gamma)\cup(\beta\cap\gamma) \quad[\text{*24·431·432}]\) -/
theorem pm24_44 {A B C : Set α} : (A ∪ C) ∩ (B ∪ Cᶜ) = (A ∩ Cᶜ) ∪ (B ∩ C) := by pm_cls

/-- ✱24·45. \(\vdash\colon(\alpha\cap\gamma)\cup(\beta - \gamma)=\Lambda.\equiv.\beta\subset\gamma\subset.\gamma\subset - \alpha\)

**Status.** proved (reading): transcription error of the e-text, which prints the right side as
`β ⊂ γ ⊂ . γ ⊂ −α` (a stray `⊂`). It is read `β ⊂ γ . γ ⊂ −α` (equivalently the chain
`β ⊂ γ ⊂ −α`), as the demonstration concludes (`γ ⊂ −α . β ⊂ γ`) and as ✱24·46 uses it. -/
theorem pm24_45 {A B C : Set α} : (A ∩ C) ∪ (B \ C) = Λ ↔ B ⊆ C ∧ C ⊆ Aᶜ := by pm_cls

/-- ✱24·46. \(\vdash\colon(\alpha\cap\gamma)\cup(\beta - \gamma)=\Lambda.\supset.\alpha\cap\beta=\Lambda\) -/
theorem pm24_46 {A B C : Set α} : (A ∩ C) ∪ (B \ C) = Λ → A ∩ B = Λ := by pm_cls

/-- ✱24·47. \(\vdash\colon\alpha\cap\beta=\Lambda.\alpha\cup\beta=\gamma.\equiv.\alpha\subset\gamma.\beta=\gamma - \alpha\) -/
theorem pm24_47 {A B C : Set α} : A ∩ B = Λ ∧ A ∪ B = C ↔ A ⊆ C ∧ B = C \ A := by pm_cls

/-- ✱24·48. \[\begin{align}\vdash\colon\ldotp \xi\subset\alpha.\xi'\subset\alpha.\eta\subset\beta.\eta'\subset\beta.\alpha\cap\beta&=\Lambda.\supset\colon\\ &\xi\cup\eta=\xi'\cup\eta'.\equiv.\xi=\xi'.\eta=\eta'\end{align}\] -/
theorem pm24_48 {A B X X' Y Y' : Set α} :
    (((X ⊆ A ∧ X' ⊆ A) ∧ Y ⊆ B) ∧ Y' ⊆ B) ∧ A ∩ B = Λ →
      (X ∪ Y = X' ∪ Y' ↔ X = X' ∧ Y = Y') := by
  pm_cls

/-- ✱24·481. \(\vdash\colon\ldotp \alpha\cap\beta=\Lambda.\alpha\cap\gamma=\Lambda.\supset\colon \alpha\cup\beta=\alpha\cup\gamma.\equiv.\beta=\gamma\) -/
theorem pm24_481 {A B C : Set α} :
    A ∩ B = Λ ∧ A ∩ C = Λ → (A ∪ B = A ∪ C ↔ B = C) := by
  pm_cls

/-- ✱24·482. \[\begin{align}&\vdash\colon\ldotp \xi\subset\alpha.\eta\subset\beta.\alpha\cap\beta=\Lambda.\supset\colon \xi\cup\eta=\alpha\cup\beta.\equiv.\xi=\alpha.\eta=\beta\\ &\quad\left[\text{*24·48} \frac{\alpha,\,\beta}{\xi',\,\eta'}.\text{*22·42}\right]\end{align}\] -/
theorem pm24_482 {A B X Y : Set α} :
    (X ⊆ A ∧ Y ⊆ B) ∧ A ∩ B = Λ → (X ∪ Y = A ∪ B ↔ X = A ∧ Y = B) := by
  pm_cls

/-- ✱24·49. \(\vdash\colon\ldotp\alpha\cap\beta=\Lambda.\supset\colon\alpha\subset\beta\cup\gamma.\equiv.\alpha\subset\gamma\) -/
theorem pm24_49 {A B C : Set α} : A ∩ B = Λ → (A ⊆ B ∪ C ↔ A ⊆ C) := by pm_cls

/-- ✱24·491. \[\begin{align}\vdash\colon\beta\cap\gamma=\Lambda.&\alpha\subset\beta\cup\gamma.\\ &\supset.\alpha - \beta=\alpha\cap\gamma.\alpha - \gamma=\alpha\cap\beta.\alpha=(\alpha - \beta)\cup(\alpha - \gamma)\end{align}\] -/
theorem pm24_491 {A B C : Set α} :
    B ∩ C = Λ ∧ A ⊆ B ∪ C →
      (A \ B = A ∩ C ∧ A \ C = A ∩ B) ∧ A = (A \ B) ∪ (A \ C) := by
  pm_cls

/-- ✱24·492. \(\vdash\colon\beta\subset\alpha.\alpha - \beta=\gamma.\supset.\alpha - \gamma=\beta\) -/
theorem pm24_492 {A B C : Set α} : B ⊆ A ∧ A \ B = C → A \ C = B := by pm_cls

/-- ✱24·493. \(\vdash\colon\beta\cap\gamma=\Lambda.\supset.\alpha=(\alpha - \beta)\cup(\alpha - \gamma)\) -/
theorem pm24_493 {A B C : Set α} : B ∩ C = Λ → A = (A \ B) ∪ (A \ C) := by pm_cls

/-- ✱24·494. \(\vdash\colon\xi\subset\alpha.\eta\subset\beta.\alpha\cap\beta=\Lambda.\supset.(\xi\cup\eta)- \alpha=\eta.(\xi\cup\eta)- \beta=\xi\) -/
theorem pm24_494 {A B X Y : Set α} :
    (X ⊆ A ∧ Y ⊆ B) ∧ A ∩ B = Λ → (X ∪ Y) \ A = Y ∧ (X ∪ Y) \ B = X := by
  pm_cls

/-- ✱24·495. \(\vdash\colon\alpha\cap\gamma=\Lambda.\supset.(\alpha\cup\gamma)-(\beta\cup\gamma)=\alpha - \beta\) -/
theorem pm24_495 {A B C : Set α} : A ∩ C = Λ → (A ∪ C) \ (B ∪ C) = A \ B := by pm_cls

/-- ✱24·5. \(\vdash\colon\exists!\alpha.\equiv.(\exists x).x \in \alpha \quad[\text{*4·2.(*24·03)}]\) -/
theorem pm24_5 {A : Set α} : A.Nonempty ↔ ∃ x, x ∈ A := Iff.rfl

/-- ✱24·51. \(\vdash\colon{\sim}\exists!\alpha.\equiv.\alpha=\Lambda\)

(Not a separate entry of `data/principia.json`: the e-text runs ✱24·51 into the comment after
✱24·5. It is cited in ✱24·52·53·54·57·61·62 and often later.) -/
theorem pm24_51 {A : Set α} : ¬A.Nonempty ↔ A = Λ := by
  rw [Null_eq_empty]
  exact Set.not_nonempty_iff_eq_empty

/-- ✱24·52. \(\vdash.\exists!\text{V} \quad [\text{*24·51·1.Transp}]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I), as the
note after this proposition explains ("the assumption that there is something ... is implicit
in the proposition ✱10·1"); `[Nonempty α]` is that assumption, made explicit. -/
theorem pm24_52 [Nonempty α] : (V : Set α).Nonempty := by
  rw [V_eq_univ]
  exact Set.univ_nonempty

/-- ✱24·53. \(\vdash.{\sim}\exists!\Lambda \quad[\text{*24·51.*20·2}]\) -/
theorem pm24_53 : ¬(Λ : Set α).Nonempty := fun ⟨x, h⟩ => pm24_105 x h

/-- ✱24·54. \(\vdash\colon\exists!\alpha.\equiv.\alpha\neq\Lambda \quad[\text{*24·51.Transp}]\) -/
theorem pm24_54 {A : Set α} : A.Nonempty ↔ A ≠ Λ := by
  rw [Null_eq_empty]
  exact Set.nonempty_iff_ne_empty

/-- ✱24·55. \(\vdash\colon{\sim}(\alpha\supset\beta).\equiv.\exists!\alpha - \beta \quad[\text{*24·3.Transp.*24·54]}\)

**Status.** proved (reading): transcription error of the e-text, which prints `α ⊃ β` for
`α ⊂ β` (PM has no sign `⊃` between classes; read as reverse inclusion the proposition would be
false). The summary of ✱24 prints it `∼(α ⊂ β) . ≡ . ∃!α − β` ("the contradictory of the
universal affirmative is the particular negative"), and it is cited from ✱24·3. -/
theorem pm24_55 {A B : Set α} : ¬(A ⊆ B) ↔ (A \ B).Nonempty := by
  constructor
  · intro h
    by_contra hc
    exact h fun x hx => by_contra fun hxB => hc ⟨x, hx, hxB⟩
  · rintro ⟨x, hx, hxB⟩ h
    exact hxB (h hx)

/-- ✱24·56. \(\vdash\colon\ldotp \exists!(\alpha\cup\beta).\equiv\colon\exists!\alpha.\lor.\exists!\beta \quad[\text{*10·42.*22·34}]\) -/
theorem pm24_56 {A B : Set α} : (A ∪ B).Nonempty ↔ A.Nonempty ∨ B.Nonempty := Set.union_nonempty

/-- ✱24·561. \(\vdash\colon \exists!(\alpha\cap\beta).\supset.\exists!\alpha.\exists!\beta \quad[\text{*10·5.*22·33}]\) -/
theorem pm24_561 {A B : Set α} : (A ∩ B).Nonempty → A.Nonempty ∧ B.Nonempty :=
  fun ⟨x, hA, hB⟩ => ⟨⟨x, hA⟩, ⟨x, hB⟩⟩

/-- ✱24·57. \(\vdash\colon\ldotp \alpha\cap\beta=\Lambda.\supset\colon\exists!\alpha.\supset.\alpha\neq \beta\) -/
theorem pm24_57 {A B : Set α} : A ∩ B = Λ → (A.Nonempty → A ≠ B) := by
  rintro h ⟨x, hx⟩ rfl
  rw [Set.inter_self] at h
  exact pm24_105 x (h ▸ hx)

/-- ✱24·571. \(\vdash\colon\exists!\alpha.\alpha=\beta.\supset.\exists!(\alpha\cap\beta)\) -/
theorem pm24_571 {A B : Set α} : A.Nonempty ∧ A = B → (A ∩ B).Nonempty := by
  rintro ⟨⟨x, hx⟩, rfl⟩
  exact ⟨x, hx, hx⟩

/-- ✱24·58. \(\vdash\colon\ldotp\alpha\supset\beta.\supset\colon\exists!\alpha.\supset.\exists!\beta \qquad\quad[\text{*10·28}]\)

**Status.** proved (reading): transcription error of the e-text, which prints `α ⊃ β` for
`α ⊂ β`, as in ✱24·55 (the reference ✱10·28 is `φx ⊃_x ψx . ⊃ : (∃x).φx . ⊃ . (∃x).ψx`). -/
theorem pm24_58 {A B : Set α} : A ⊆ B → (A.Nonempty → B.Nonempty) := fun h hA => hA.mono h

/-- ✱24·6. \(\vdash\colon\ldotp\alpha\supset\beta.\supset\colon\alpha\neq\beta.\equiv.\exists!\beta - \alpha\)

**Status.** proved (reading): transcription error of the e-text, which prints `α ⊃ β` for
`α ⊂ β`, as in ✱24·55 (the demonstration uses ✱22·41 and ✱24·55, i.e. inclusion). -/
theorem pm24_6 {A B : Set α} : A ⊆ B → (A ≠ B ↔ (B \ A).Nonempty) := by
  intro h
  constructor
  · intro hne
    by_contra hc
    exact hne (Set.Subset.antisymm h fun x hx => by_contra fun hxA => hc ⟨x, hx, hxA⟩)
  · rintro ⟨x, hxB, hxA⟩ rfl
    exact hxA hxB

/-- ✱24·61. \(\vdash\colon{\sim}\exists!\beta.\supset.\alpha\cup\beta=\alpha \quad[\text{*24·51·24}]\) -/
theorem pm24_61 {A B : Set α} : ¬B.Nonempty → A ∪ B = A := by
  intro h
  rw [pm24_51.1 h, pm24_24]

/-- ✱24·62. \(\vdash\colon{\sim}\exists!\beta.\supset.\alpha\cap\beta=\Lambda \quad[\text{*24·51·23}]\) -/
theorem pm24_62 {A B : Set α} : ¬B.Nonempty → A ∩ B = Λ := by
  intro h
  rw [pm24_51.1 h, pm24_23]

/-- ✱24·63. \(\vdash\colon\ldotp\Lambda{\sim}\in\kappa.\equiv:\alpha\in\kappa.\supset_{\alpha}.\exists!\alpha\) -/
theorem pm24_63 {K : Set (Set α)} : Λ ∉ K ↔ ∀ A, A ∈ K → A.Nonempty := by
  constructor
  · intro h A hA
    rw [pm24_54]
    rintro rfl
    exact h hA
  · intro h hK
    exact pm24_53 (h _ hK)

/-!
## [✱25] The universal relation, the null relation, and the existence of relations

*(Vol. 1, p. 241)*

> *Summary of* *25.
>
> This number contains the analogues, for relations, of the definitions and propositions of *24. Proofs will not be given, as they proceed precisely as in *24.
>
> The universal relation, denoted by \(\dot{\text{V}}\), is the relation which holds between any two terms whatever of the appropriate types, whatever these may be in the given context. The null relation, \(\dot{\Lambda}\), is the relation which does not hold between any pair of terms whatever, its type being fixed by the types of the terms concerning which the denial that it holds is significant. A relation \(R\) is said to *exist* when there is at least one pair of terms between which it holds; "\(R\) exists" is written "\(\dot{\exists}!R\)."
>
> The propositions of this number are much less often referred to than those of *24, but for the sake of uniformity we have given the analogues of all propositions in *24, with the same numeration (except for the integral part).
>
> All the remarks made in *24 apply, *mutatis mutandis*, in the present number.

**Lean reading.** The relational analogue of ✱24: `V̇` is `rV`, `Λ̇` is `rNull` (both PM's
definitions, `rV x y` is `x = x ∧ y = y`, `rNull_apply`), and `∃̇!R` ("R holds between some pair")
is `rEx R`. Relations are `α → β → Prop` with the dotted operations of ✱23 (`⪽`, `⩀`, `⊍`, `∸`),
and identity of relations is Lean's `=` (`rel_eq_iff`). Products of hypotheses are left-nested
conjunctions; the chain of ✱25·4 is the conjunction of its links. ✱25·1 and ✱25·52 need inhabited
types (PM's tacit assumption). ✱25·37 and ✱25·412 are printed as corrected by the Additional
Errata; ✱25·431, unlike ✱24·431, is correct as printed.

**Status.** proved (all propositions; ✱25·01–·03 definition; ✱25·1, ✱25·52 proved (reading):
`[Nonempty α] [Nonempty β]`, see their docstrings).
-/

/-- ✱25·01 (Df). \(\dot{\text{V}} = \hat{x}\hat{y}(x = x . y = y) \quad \text{Df}\) -/
theorem pm25_01 : (rV : α → β → Prop) = fun x y => x = x ∧ y = y := rfl

/-- ✱25·02 (Df). \(\dot{\Lambda} = \dot{-}\dot{\text{V}} \quad \text{Df}\) -/
theorem pm25_02 : (rNull : α → β → Prop) = ∸rV := rfl

/-- ✱25·03 (Df). \(\dot{\exists}!R .=. (\exists x,y) . xRy \quad \text{Df}\) -/
theorem pm25_03 {R : α → β → Prop} : rEx R ↔ ∃ x y, R x y := Iff.rfl

/-- ✱25·1. \(\vdash. \dot{\Lambda} \neq \dot{\text{V}}\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; cf. the
note after ✱24·52). If `α` or `β` is empty, `Λ̇ = V̇`; so `[Nonempty α] [Nonempty β]` is added. -/
theorem pm25_1 [Nonempty α] [Nonempty β] : (rNull : α → β → Prop) ≠ rV := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty α›
  obtain ⟨y⟩ := ‹Nonempty β›
  have h' : rNull x y ↔ rV x y := Iff.of_eq (congrFun (congrFun h x) y)
  exact rNull_apply x y (h'.2 ⟨rfl, rfl⟩)

/-- ✱25·101. \(\vdash. \dot{\text{V}} = \dot{-}\dot{\Lambda}\) -/
theorem pm25_101 : (rV : α → β → Prop) = ∸rNull := by pm_rel

/-- ✱25·102. \(\vdash: (x,y).\phi(x,y) .\equiv. \hat{x}\hat{y}\phi(x,y) = \dot{\text{V}}\) -/
theorem pm25_102 {φ : α → β → Prop} : (∀ x y, φ x y) ↔ (fun x y => φ x y) = rV := by
  pm_rel

/-- ✱25·103. \(\vdash: (x,y).{\sim}\phi(x,y) .\equiv. \hat{x}\hat{y}\phi(x,y) = \dot{\Lambda}\) -/
theorem pm25_103 {φ : α → β → Prop} :
    (∀ x y, ¬φ x y) ↔ (fun x y => φ x y) = rNull := by
  pm_rel

/-- ✱25·104. \(\vdash. (x,y).x\dot{\text{V}}y\) -/
theorem pm25_104 : ∀ (x : α) (y : β), rV x y := fun _ _ => ⟨rfl, rfl⟩

/-- ✱25·105. \(\vdash.(x,y).{\sim}(x \dot{\Lambda} y)\) -/
theorem pm25_105 : ∀ (x : α) (y : β), ¬rNull x y := rNull_apply

/-- ✱25·11. \(\vdash. (R).R \unicode{x2abd} \dot{\text{V}}\) -/
theorem pm25_11 : ∀ R : α → β → Prop, R ⪽ rV := fun _ _ _ _ => ⟨rfl, rfl⟩

/-- ✱25·12. \(\vdash. (R).\dot{\Lambda} \unicode{x2abd} R\) -/
theorem pm25_12 : ∀ R : α → β → Prop, rNull ⪽ R :=
  fun _ x y h => absurd h (rNull_apply x y)

/-- ✱25·13. \(\vdash:R=\dot{\Lambda}.\equiv.R\unicode{x2abd}\dot{\Lambda}\) -/
theorem pm25_13 {R : α → β → Prop} : R = rNull ↔ R ⪽ rNull := by pm_rel

/-- ✱25·14. \(\vdash:(x,y).xRy.\equiv.R=\dot{\text{V}}\) -/
theorem pm25_14 {R : α → β → Prop} : (∀ x y, R x y) ↔ R = rV := by pm_rel

/-- ✱25·141. \(\vdash:\dot{\text{V}}\unicode{x2abd}R.\equiv.\dot{\text{V}}=R\) -/
theorem pm25_141 {R : α → β → Prop} : rV ⪽ R ↔ rV = R := by pm_rel

/-- ✱25·15. \(\vdash:(x,y).{\sim}(xRy).\equiv.R=\dot{\Lambda}\) -/
theorem pm25_15 {R : α → β → Prop} : (∀ x y, ¬R x y) ↔ R = rNull := by pm_rel

/-- ✱25·17. \(\vdash:R=\dot{\text{V}}.\equiv.\dot{-}R=\dot{\Lambda}\) -/
theorem pm25_17 {R : α → β → Prop} : R = rV ↔ ∸R = rNull := by pm_rel

/-- ✱25·21. \(\vdash.R\dot{\cap}\dot{-}R=\dot{\Lambda}\) -/
theorem pm25_21 {R : α → β → Prop} : R ⩀ ∸R = rNull := by pm_rel

/-- ✱25·22. \(\vdash.R\unicode{x228d}\dot{-}R=\dot{\text{V}}\) -/
theorem pm25_22 {R : α → β → Prop} : R ⊍ ∸R = rV := by pm_rel

/-- ✱25·23. \(\vdash.R\dot{\cap}\dot{\Lambda}=\dot{\Lambda}\) -/
theorem pm25_23 {R : α → β → Prop} : R ⩀ rNull = rNull := by pm_rel

/-- ✱25·24. \(\vdash.R\unicode{x228d}\dot{\Lambda}=R\) -/
theorem pm25_24 {R : α → β → Prop} : R ⊍ rNull = R := by pm_rel

/-- ✱25·26. \(\vdash.R\dot{\cap}\dot{\text{V}}=R\) -/
theorem pm25_26 {R : α → β → Prop} : R ⩀ rV = R := by pm_rel

/-- ✱25·27. \(\vdash.R\unicode{x228d}\dot{\text{V}}=\dot{\text{V}}\) -/
theorem pm25_27 {R : α → β → Prop} : R ⊍ rV = rV := by pm_rel

/-- ✱25·3. \(\vdash:R\unicode{x2abd}S.\equiv.R\dot{-}S=\dot{\Lambda}\) -/
theorem pm25_3 {R S : α → β → Prop} : R ⪽ S ↔ R ∸ S = rNull := by pm_rel

/-- ✱25·31. \(\vdash:R\unicode{x2abd}S.\equiv.\dot{-}R\unicode{x228d}S=\dot{\text{V}}\) -/
theorem pm25_31 {R S : α → β → Prop} : R ⪽ S ↔ ∸R ⊍ S = rV := by pm_rel

/-- ✱25·311. \(\vdash:R\unicode{x2abd}\dot{-}S.\equiv.R\dot{\cap}S=\dot{\Lambda}\) -/
theorem pm25_311 {R S : α → β → Prop} : R ⪽ ∸S ↔ R ⩀ S = rNull := by pm_rel

/-- ✱25·312. \(\vdash:\dot{-}R\unicode{x2abd}S.\equiv.R\unicode{x228d}S=\dot{\text{V}}\) -/
theorem pm25_312 {R S : α → β → Prop} : ∸R ⪽ S ↔ R ⊍ S = rV := by pm_rel

/-- ✱25·313. \(\vdash:R\dot{\cap}S=\dot{\Lambda}.\equiv.R\dot{-}S=R\) -/
theorem pm25_313 {R S : α → β → Prop} : R ⩀ S = rNull ↔ R ∸ S = R := by pm_rel

/-- ✱25·32. \(\vdash:R\unicode{x228d}S=\dot{\Lambda}.\equiv.R=\dot{\Lambda}.S=\dot{\Lambda}\) -/
theorem pm25_32 {R S : α → β → Prop} : R ⊍ S = rNull ↔ R = rNull ∧ S = rNull := by pm_rel

/-- ✱25·33. \(\vdash:R=\dot{\text{V}}.\supset.R\unicode{x228d}S=\dot{\text{V}}\) -/
theorem pm25_33 {R S : α → β → Prop} : R = rV → R ⊍ S = rV := by pm_rel

/-- ✱25·34. \(\vdash:R=\dot{\Lambda}.\supset.R\dot{\cap}S=\dot{\Lambda}\) -/
theorem pm25_34 {R S : α → β → Prop} : R = rNull → R ⩀ S = rNull := by pm_rel

/-- ✱25·35. \(\vdash:R=\dot{\text{V}}.\supset.R\dot{\cap}S=S\) -/
theorem pm25_35 {R S : α → β → Prop} : R = rV → R ⩀ S = S := by pm_rel

/-- ✱25·36. \(\vdash:R=\dot{\Lambda}.\supset.R\unicode{x228d}S=S\) -/
theorem pm25_36 {R S : α → β → Prop} : R = rNull → R ⊍ S = S := by pm_rel

/-- ✱25·37. \(\vdash\colon\ldotp R\dot{\cap}S=\dot{\Lambda}.\equiv\colon\ldotp xRy.zSw.\supset_{x,y,z,w}:x\neq z.\lor.y\neq w\)

**Status.** proved: the e-text already incorporates the erratum (Additional Errata to Vol. I,
p. 242: read `zSw` for `zRw`). -/
theorem pm25_37 {R S : α → β → Prop} :
    R ⩀ S = rNull ↔ ∀ x y z w, R x y ∧ S z w → x ≠ z ∨ y ≠ w := by
  rw [rel_eq_iff]
  constructor
  · rintro h x y z w ⟨hR, hS⟩
    by_contra hc
    obtain ⟨hxz, hyw⟩ := not_or.1 hc
    obtain rfl := not_not.1 hxz
    obtain rfl := not_not.1 hyw
    exact rNull_apply x y ((h x y).1 ⟨hR, hS⟩)
  · intro h x y
    refine ⟨fun hRS => ?_, fun h' => absurd h' (rNull_apply x y)⟩
    exact ((h x y x y hRS).elim (fun h => h rfl) (fun h => h rfl)).elim

/-- ✱25·38. \(\vdash\colon\ldotp R\dot{\cap}S=\dot{\Lambda}.\supset:R\neq S.\lor.R=\dot{\Lambda}.S=\dot{\Lambda}\) -/
theorem pm25_38 {R S : α → β → Prop} : R ⩀ S = rNull → R ≠ S ∨ (R = rNull ∧ S = rNull) := by
  intro h
  by_cases hRS : R = S
  · subst hRS
    rw [pm23_5] at h
    exact Or.inr ⟨h, h⟩
  · exact Or.inl hRS

/-- ✱25·39. \(\vdash\colon\ldotp R\dot{\cap}S=\dot{\Lambda}.\equiv:xRy.\supset_{x,y}.{\sim}(xSy)\) -/
theorem pm25_39 {R S : α → β → Prop} : R ⩀ S = rNull ↔ ∀ x y, R x y → ¬S x y := by pm_rel

/-- ✱25·4. \(\vdash:P\dot{\cap}Q=\dot{\Lambda}.\equiv.(P\unicode{x228d}Q)\dot{-}P=Q.\equiv.(P\unicode{x228d}Q)\dot{-}Q=P\) -/
theorem pm25_4 {P Q : α → β → Prop} :
    (P ⩀ Q = rNull ↔ (P ⊍ Q) ∸ P = Q) ∧ ((P ⊍ Q) ∸ P = Q ↔ (P ⊍ Q) ∸ Q = P) := by
  rel_simp
  exact ⟨forall_congr' fun x => forall_congr' fun y => by tauto,
    forall_congr' fun x => forall_congr' fun y => by tauto⟩

/-- ✱25·401. \(\vdash:Q\unicode{x2abd}P.\supset.(Q\unicode{x228d}R)\dot{-}P=R\dot{-}P\) -/
theorem pm25_401 {P Q R : α → β → Prop} : Q ⪽ P → (Q ⊍ R) ∸ P = R ∸ P := by pm_rel

/-- ✱25·402. \(\vdash:P\dot{\cap}Q=\dot{\Lambda}.R\unicode{x2abd}P.S\unicode{x2abd}Q.\supset.R\dot{\cap}S=\dot{\Lambda}\) -/
theorem pm25_402 {P Q R S : α → β → Prop} :
    (P ⩀ Q = rNull ∧ R ⪽ P) ∧ S ⪽ Q → R ⩀ S = rNull := by
  pm_rel

/-- ✱25·41. \(\vdash.R=(R\dot{\cap}S)\unicode{x228d}(R\dot{-}S)\) -/
theorem pm25_41 {R S : α → β → Prop} : R = (R ⩀ S) ⊍ (R ∸ S) := by pm_rel

/-- ✱25·411. \(\vdash:S\unicode{x2abd}R.\supset.R=S\unicode{x228d}(R\dot{-}S)\) -/
theorem pm25_411 {R S : α → β → Prop} : S ⪽ R → R = S ⊍ (R ∸ S) := by pm_rel

/-- ✱25·412. \(\vdash:Q\unicode{x2abd}P.S\unicode{x2abd}Q.\supset.(P\dot{-}Q)\unicode{x228d}(Q\dot{-}S)=P\dot{-}S\)

**Status.** proved: the e-text already incorporates the erratum (Additional Errata to Vol. I,
p. 242: read `S` for `R`). -/
theorem pm25_412 {P Q S : α → β → Prop} : Q ⪽ P ∧ S ⪽ Q → (P ∸ Q) ⊍ (Q ∸ S) = P ∸ S := by
  pm_rel

/-- ✱25·42. \(\vdash:P\dot{\cap}Q\unicode{x2abd}R.P\dot{-}Q\unicode{x2abd}R.\equiv.P\unicode{x2abd}R\) -/
theorem pm25_42 {P Q R : α → β → Prop} : P ⩀ Q ⪽ R ∧ P ∸ Q ⪽ R ↔ P ⪽ R := by pm_rel

/-- ✱25·43. \(\vdash:P\dot{-}Q\unicode{x2abd}R.\equiv.P\unicode{x2abd}Q\unicode{x228d}R\) -/
theorem pm25_43 {P Q R : α → β → Prop} : P ∸ Q ⪽ R ↔ P ⪽ Q ⊍ R := by pm_rel

/-- ✱25·431. \(\vdash.(P\unicode{x228d}R)\dot{\cap}(Q\unicode{x228d}\dot{-}R)=(P\dot{\cap}Q)\unicode{x228d}(P\dot{-}R)\unicode{x228d}(Q\dot{\cap}R)\) -/
theorem pm25_431 {P Q R : α → β → Prop} :
    (P ⊍ R) ⩀ (Q ⊍ ∸R) = (P ⩀ Q) ⊍ (P ∸ R) ⊍ (Q ⩀ R) := by
  pm_rel

/-- ✱25·432. \(\vdash.(P\dot{-}R)\unicode{x228d}(Q\dot{\cap}R)=(P\dot{\cap}Q)\unicode{x228d}(P\dot{-}R)\unicode{x228d}(Q\dot{\cap}R)\) -/
theorem pm25_432 {P Q R : α → β → Prop} :
    (P ∸ R) ⊍ (Q ⩀ R) = (P ⩀ Q) ⊍ (P ∸ R) ⊍ (Q ⩀ R) := by
  pm_rel

/-- ✱25·44. \(\vdash.(P\unicode{x228d}R)\dot{\cap}(Q\unicode{x228d}\dot{-}R)=(P\dot{\cap}\dot{-}R)\unicode{x228d}(Q\dot{\cap}R)\) -/
theorem pm25_44 {P Q R : α → β → Prop} : (P ⊍ R) ⩀ (Q ⊍ ∸R) = (P ⩀ ∸R) ⊍ (Q ⩀ R) := by pm_rel

/-- ✱25·45. \(\vdash:(P\dot{\cap}R)\unicode{x228d}(Q\dot{-}R)=\dot{\Lambda}.\equiv.Q\unicode{x2abd}R.R\unicode{x2abd}\dot{-}P\) -/
theorem pm25_45 {P Q R : α → β → Prop} : (P ⩀ R) ⊍ (Q ∸ R) = rNull ↔ Q ⪽ R ∧ R ⪽ ∸P := by pm_rel

/-- ✱25·46. \(\vdash:(P\dot{\cap}R)\unicode{x228d}(Q\dot{-}R)=\dot{\Lambda}.\supset.P\dot{\cap}Q=\dot{\Lambda}\) -/
theorem pm25_46 {P Q R : α → β → Prop} : (P ⩀ R) ⊍ (Q ∸ R) = rNull → P ⩀ Q = rNull := by pm_rel

/-- ✱25·47. \(\vdash:(P\dot{\cap}Q)=\dot{\Lambda}.P\unicode{x228d}Q=R.\equiv.P\unicode{x2abd}R.Q=R\dot{-}P\) -/
theorem pm25_47 {P Q R : α → β → Prop} : P ⩀ Q = rNull ∧ P ⊍ Q = R ↔ P ⪽ R ∧ Q = R ∸ P := by pm_rel

/-- ✱25·48. \[\begin{align}\vdash\colon\ldotp R\unicode{x2abd}P.R'\unicode{x2abd}P.S\unicode{x2abd}Q.S'\unicode{x2abd}Q.&P\dot{\cap}Q=\dot{\Lambda}.\supset:\\ &R\unicode{x228d}S=R'\unicode{x228d}S'.\equiv.R=R'.S=S'\end{align}\] -/
theorem pm25_48 {P Q R R' S S' : α → β → Prop} :
    (((R ⪽ P ∧ R' ⪽ P) ∧ S ⪽ Q) ∧ S' ⪽ Q) ∧ P ⩀ Q = rNull →
      (R ⊍ S = R' ⊍ S' ↔ R = R' ∧ S = S') := by
  pm_rel

/-- ✱25·481. \(\vdash\colon\ldotp P\dot{\cap}Q=\dot{\Lambda}.P\dot{\cap}R=\dot{\Lambda}.\supset:P\unicode{x228d}Q=P\unicode{x228d}R.\equiv.Q=R\) -/
theorem pm25_481 {P Q R : α → β → Prop} :
    P ⩀ Q = rNull ∧ P ⩀ R = rNull → (P ⊍ Q = P ⊍ R ↔ Q = R) := by
  pm_rel

/-- ✱25·482. \(\vdash\colon\ldotp R\unicode{x2abd}P.S\unicode{x2abd}Q.P\dot{\cap}Q=\dot{\Lambda}.\supset:R\unicode{x228d}S=P\unicode{x228d}Q.\equiv.R=P.S=Q\) -/
theorem pm25_482 {P Q R S : α → β → Prop} :
    (R ⪽ P ∧ S ⪽ Q) ∧ P ⩀ Q = rNull → (R ⊍ S = P ⊍ Q ↔ R = P ∧ S = Q) := by
  pm_rel

/-- ✱25·49. \(\vdash\colon\ldotp P\dot{\cap}Q=\dot{\Lambda}.\supset:P\unicode{x2abd}Q\unicode{x228d}R.\equiv.P\unicode{x2abd}R\) -/
theorem pm25_49 {P Q R : α → β → Prop} : P ⩀ Q = rNull → (P ⪽ Q ⊍ R ↔ P ⪽ R) := by pm_rel

/-- ✱25·491. \[\begin{align}\vdash:Q\dot{\cap}R=\dot{\Lambda}.&P\unicode{x2abd}Q\unicode{x228d}R.\supset.\\ &P\dot{-}Q=P\dot{\cap}R.P\dot{-}R=P\dot{\cap}Q.P=(P\dot{-}Q)\unicode{x228d}(P\dot{-}R)\end{align}\] -/
theorem pm25_491 {P Q R : α → β → Prop} :
    Q ⩀ R = rNull ∧ P ⪽ Q ⊍ R →
      (P ∸ Q = P ⩀ R ∧ P ∸ R = P ⩀ Q) ∧ P = (P ∸ Q) ⊍ (P ∸ R) := by
  pm_rel

/-- ✱25·492. \(\vdash:Q\unicode{x2abd}P.P\dot{-}Q=R.\supset.P\dot{-}R=Q\) -/
theorem pm25_492 {P Q R : α → β → Prop} : Q ⪽ P ∧ P ∸ Q = R → P ∸ R = Q := by pm_rel

/-- ✱25·493. \(\vdash:Q\dot{\cap}R=\dot{\Lambda}.\supset.P=(P\dot{-}Q)\unicode{x228d}(P\dot{-}R)\) -/
theorem pm25_493 {P Q R : α → β → Prop} : Q ⩀ R = rNull → P = (P ∸ Q) ⊍ (P ∸ R) := by pm_rel

/-- ✱25·494. \(\vdash:R\unicode{x2abd}P.S\unicode{x2abd}Q.P\dot{\cap}Q=\dot{\Lambda}.\supset.(R\unicode{x228d}S)\dot{-}P=S.(R\unicode{x228d}S)\dot{-}Q=R\) -/
theorem pm25_494 {P Q R S : α → β → Prop} :
    (R ⪽ P ∧ S ⪽ Q) ∧ P ⩀ Q = rNull → (R ⊍ S) ∸ P = S ∧ (R ⊍ S) ∸ Q = R := by
  pm_rel

/-- ✱25·495. \(\vdash:P\dot{\cap}R=\dot{\Lambda}.\supset.(P\unicode{x228d}R)\dot{-}(Q\unicode{x228d}R)=P\dot{-}Q\) -/
theorem pm25_495 {P Q R : α → β → Prop} : P ⩀ R = rNull → (P ⊍ R) ∸ (Q ⊍ R) = P ∸ Q := by pm_rel

/-- ✱25·5. \(\vdash:\dot{\exists}!R.\equiv.(\exists x,y).xRy\) -/
theorem pm25_5 {R : α → β → Prop} : rEx R ↔ ∃ x y, R x y := Iff.rfl

/-- ✱25·51. \(\vdash:{\sim}\dot{\exists}!R.\equiv.R=\dot{\Lambda}\) -/
theorem pm25_51 {R : α → β → Prop} : ¬rEx R ↔ R = rNull := by
  rw [rel_eq_iff]
  simp only [rEx, not_exists]
  exact forall_congr' fun x => forall_congr' fun y =>
    ⟨fun h => ⟨fun hR => absurd hR h, fun h' => absurd h' (rNull_apply x y)⟩,
      fun h hR => rNull_apply x y (h.1 hR)⟩

/-- ✱25·52. \(\vdash.\dot{\exists}!\dot{\text{V}}\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the note
after ✱24·52 applies, *mutatis mutandis*); `[Nonempty α] [Nonempty β]` makes it explicit. -/
theorem pm25_52 [Nonempty α] [Nonempty β] : rEx (rV : α → β → Prop) := by
  obtain ⟨x⟩ := ‹Nonempty α›
  obtain ⟨y⟩ := ‹Nonempty β›
  exact ⟨x, y, rfl, rfl⟩

/-- ✱25·53. \(\vdash.{\sim}\dot{\exists}!\dot{\Lambda}\) -/
theorem pm25_53 : ¬rEx (rNull : α → β → Prop) := fun ⟨x, y, h⟩ => rNull_apply x y h

/-- ✱25·54. \(\vdash:\dot{\exists}!R.\equiv.R\neq\dot{\Lambda}\) -/
theorem pm25_54 {R : α → β → Prop} : rEx R ↔ R ≠ rNull := by
  rw [ne_eq, ← pm25_51, not_not]

/-- ✱25·55. \(\vdash:{\sim}(R\unicode{x2abd}S).\equiv.\dot{\exists}!R\dot{-}S\) -/
theorem pm25_55 {R S : α → β → Prop} : ¬(R ⪽ S) ↔ rEx (R ∸ S) := by
  constructor
  · intro h
    by_contra hc
    exact h fun x y hR => by_contra fun hS => hc ⟨x, y, hR, hS⟩
  · rintro ⟨x, y, hR, hS⟩ h
    exact hS (h x y hR)

/-- ✱25·56. \(\vdash\colon\ldotp\dot{\exists}!R\unicode{x228d}S.\equiv:\dot{\exists}!R.\lor.\dot{\exists}!S\) -/
theorem pm25_56 {R S : α → β → Prop} : rEx (R ⊍ S) ↔ rEx R ∨ rEx S := by
  constructor
  · rintro ⟨x, y, h | h⟩
    exacts [Or.inl ⟨x, y, h⟩, Or.inr ⟨x, y, h⟩]
  · rintro (⟨x, y, h⟩ | ⟨x, y, h⟩)
    exacts [⟨x, y, Or.inl h⟩, ⟨x, y, Or.inr h⟩]

/-- ✱25·561. \(\vdash:\dot{\exists}!(R\dot{\cap}S).\supset.\dot{\exists}!R.\dot{\exists}!S\) -/
theorem pm25_561 {R S : α → β → Prop} : rEx (R ⩀ S) → rEx R ∧ rEx S :=
  fun ⟨x, y, hR, hS⟩ => ⟨⟨x, y, hR⟩, ⟨x, y, hS⟩⟩

/-- ✱25·57. \(\vdash\colon\ldotp R\dot{\cap}S=\dot{\Lambda}.\supset:\dot{\exists}!R.\supset.R\neq S\) -/
theorem pm25_57 {R S : α → β → Prop} : R ⩀ S = rNull → (rEx R → R ≠ S) := by
  rintro h ⟨x, y, hR⟩ rfl
  rw [pm23_5] at h
  exact rNull_apply x y (h ▸ hR)

/-- ✱25·571. \(\vdash:\dot{\exists}!R.R=S.\supset.\dot{\exists}!(R\dot{\cap}S)\) -/
theorem pm25_571 {R S : α → β → Prop} : rEx R ∧ R = S → rEx (R ⩀ S) := by
  rintro ⟨⟨x, y, h⟩, rfl⟩
  exact ⟨x, y, h, h⟩

/-- ✱25·58. \(\vdash\colon\ldotp R\unicode{x2abd}S.\supset:\dot{\exists}!R.\supset.\dot{\exists}!S\) -/
theorem pm25_58 {R S : α → β → Prop} : R ⪽ S → (rEx R → rEx S) :=
  fun h ⟨x, y, hR⟩ => ⟨x, y, h x y hR⟩

/-- ✱25·6. \(\vdash\colon\ldotp R\unicode{x2abd}S.\supset:R\neq S.\equiv.\dot{\exists}!S\dot{-}R\) -/
theorem pm25_6 {R S : α → β → Prop} : R ⪽ S → (R ≠ S ↔ rEx (S ∸ R)) := by
  intro h
  constructor
  · intro hne
    by_contra hc
    refine hne (rel_eq_iff.2 fun x y => ⟨h x y, fun hS => ?_⟩)
    exact by_contra fun hR => hc ⟨x, y, hS, hR⟩
  · rintro ⟨x, y, hS, hR⟩ rfl
    exact hR hS

/-- ✱25·61. \(\vdash:{\sim}\dot{\exists}!S.\supset.R\unicode{x228d}S=R\) -/
theorem pm25_61 {R S : α → β → Prop} : ¬rEx S → R ⊍ S = R := by
  intro h
  rw [pm25_51.1 h, pm25_24]

/-- ✱25·62. \(\vdash:{\sim}\dot{\exists}!S.\supset.R\dot{\cap}S=\dot{\Lambda}\) -/
theorem pm25_62 {R S : α → β → Prop} : ¬rEx S → R ⩀ S = rNull := by
  intro h
  rw [pm25_51.1 h, pm25_23]

/-- ✱25·63. \(\vdash\colon\ldotp\dot{\Lambda}{\sim}\in\kappa.\equiv:R\in\kappa.\supset_{R}.\dot{\exists}!R\) -/
theorem pm25_63 {K : Set (α → β → Prop)} : rNull ∉ K ↔ ∀ R, R ∈ K → rEx R := by
  constructor
  · intro h R hR
    rw [pm25_54]
    rintro rfl
    exact h hR
  · intro h hK
    exact pm25_53 (h _ hK)

end PrincipiaMathematica
