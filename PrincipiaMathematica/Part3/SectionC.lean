import PrincipiaMathematica.Defs.Part3
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Basic.Finite.Sum
import Mathlib.Basic.Finite.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Finite.Lattice

/-!
# Part III, Section C: Finite and infinite

Volume 2. Numbers: ✱118, ✱119, ✱120, ✱121.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

/-!
## [✱118] Arithmetical substitution and uniform formal numbers

*(Vol. 2, p. 193)*

> *Summary of* *118.
>
> A difficulty arises respecting substitution in arithmetic. For if \(\mu\) is a formal number and its occurrence in \(f\mu\) is arithmetical, then by \(\text{IIT}\) \(\mu\) is always to be taken in an existential type. Hence we can only substitute a real variable \(\xi\) for \(\mu\) under the hypothesis \(\exists !\xi\), and we can only substitute another formal number \(\sigma\) for \(\mu\) provided that the equation \(\mu = \sigma\), which justifies the substitution, is arithmetical, *i.e.* provided that in this equation the type of \(\mu\) is such that \(\exists !\mu\).
>
> The result is that the application of *20·18 is apt to lead to fallacies owing to the different meanings which a formal number may possess in different occurrences. Hitherto we have considered each case in detail, *e.g.* note on *110·61, and proof of *110·56.
>
> The condition for the safe application of *20·18 is given in *118·01, namely
>
> *118·01. \(\vdash \colon\ldotp \exists !\mu .\mu =\sigma .\supset :f\mu .\equiv .f\sigma \quad[*20·18]\)
>
> …

**Lean reading.** Uniform formal numbers: a type PM indicates expressly (`(μ +_c ν)_ξ`,
`sm_ξ''μ`, `Nc(ξ)'β`) is an ascription to the type `T` of `ξ` (`(μ +ᶜ ν : Set (Set T))`,
`(sm ʻʻ μ : Set (Set T))`, `nc T B`) with no adequacy hypothesis; an unsubscripted arithmetical
component (the inner `μ +_c ν` of `(μ +_c ν +_c ϖ)_ξ`, the exponent `ν ×_c ϖ` of
`(μ^{ν ×_c ϖ})_ξ`, the factor `μ^ν` of `{μ^ν ×_c (μ^ϖ)_ξ}_ξ`) gets its own type `W` and the IIT
hypothesis `AdeqAdd`/`AdeqMul`/`AdeqExp W …`. In ✱118·201·301·401 the logical and argumental
occurrences of the sum are bound by IT. The real variables `μ`, `ν`, `ϖ` have independent types, and
`μ, ν ∈ NC` is `μ ∈ NC β₁ ∧ ν ∈ NC β₂`. ✱118·01 (arithmetical substitution) is ✱20·18 in Lean,
since an equation puts its sides in one type. The proofs compute every formal number as `Λ` or the
class of classes equinumerous with a type (`ncT`), and reduce the propositions to equivalences and
embeddings of types (`clsTimesEquiv`, `clsExpEquiv`: `α × β`, `α exp β` are a product and a
function space). Where an empty type breaks a proposition (`1 = Λ` in it) `[Nonempty …]` is added
(✱118·461·462·463·472·473).

**Status.** proved (all propositions; ✱118·01·12·201·25·301·35·351·401·45·451·46·461·462·463·47·
471·472·473 proved (reading), see their docstrings)
-/

/-! ## Helpers (private): cardinals as classes of equinumerous classes

Every formal number of this Section is, in a given type `T`, either `Λ` or the class `ncT T X` of
the classes of `T`-things equinumerous with some type `X`; the lemmas below compute
`+_c`, `×_c`, `^`, `sm''`, `>`, `≥` on such classes, so that each proposition reduces to a fact
about equivalences and embeddings of types. -/

section Helpers

open Classical

universe uA uB uC uT uX uY uZ

/-- The classes of `T`-things equinumerous with the type `X`. -/
private def ncT (T : Type uT) (X : Type uX) : Set (Set T) := {Y | Nonempty (↥Y ≃ X)}

private theorem mem_ncT {T : Type uT} {X : Type uX} {Y : Set T} :
    Y ∈ ncT T X ↔ Nonempty (↥Y ≃ X) := Iff.rfl

private theorem nc_eq_ncT (T : Type uT) {α : Type uA} (A : Set α) : nc T A = ncT T A := by
  ext Y; exact mem_nc_iff_equiv

private theorem n₀c_eq_ncT {α : Type uA} (A : Set α) : n₀c A = ncT α A := by
  rw [n₀c_eq_nc, nc_eq_ncT]

private theorem ncT_congr {T : Type uT} {X : Type uX} {Y : Type uY} (e : X ≃ Y) :
    ncT T X = ncT T Y := by
  ext Z; exact ⟨fun ⟨f⟩ => ⟨f.trans e⟩, fun ⟨f⟩ => ⟨f.trans e.symm⟩⟩

private theorem ncT_nonempty_iff {T : Type uT} {X : Type uX} :
    (ncT T X).Nonempty ↔ Nonempty (X ↪ T) := by
  constructor
  · rintro ⟨Y, ⟨e⟩⟩; exact ⟨e.symm.toEmbedding.trans (Function.Embedding.subtype _)⟩
  · rintro ⟨f⟩; exact ⟨Set.range f, ⟨(Equiv.ofInjective f f.injective).symm⟩⟩

private theorem ncT_eq_empty_iff {T : Type uT} {X : Type uX} :
    ncT T X = ∅ ↔ IsEmpty (X ↪ T) := by
  rw [← Set.not_nonempty_iff_eq_empty, ncT_nonempty_iff, not_nonempty_iff]

private theorem ncT_eq_empty {T : Type uT} {X : Type uX} (h : ¬ Nonempty (X ↪ T)) :
    ncT T X = ∅ := ncT_eq_empty_iff.2 (not_nonempty_iff.1 h)

/-- Two cardinals `ncT` in one type are equal iff the types are equinumerous or neither exists. -/
private theorem ncT_eq_ncT_iff {T : Type uT} {X : Type uX} {Y : Type uY} :
    ncT T X = ncT T Y ↔ Nonempty (X ≃ Y) ∨ (¬ Nonempty (X ↪ T) ∧ ¬ Nonempty (Y ↪ T)) := by
  constructor
  · intro h
    by_cases hX : Nonempty (X ↪ T)
    · obtain ⟨Z, hZ⟩ := ncT_nonempty_iff.2 hX
      have hZ' : Z ∈ ncT T Y := h ▸ hZ
      obtain ⟨e⟩ := hZ; obtain ⟨e'⟩ := hZ'
      exact Or.inl ⟨e.symm.trans e'⟩
    · refine Or.inr ⟨hX, fun hY => hX ?_⟩
      rw [← ncT_nonempty_iff, h]; exact ncT_nonempty_iff.2 hY
  · rintro (⟨⟨e⟩⟩ | ⟨hX, hY⟩)
    · exact ncT_congr e
    · rw [ncT_eq_empty hX, ncT_eq_empty hY]

private theorem ncT_eq_n₀c_of_mem {T : Type uT} {X : Type uX} {Y : Set T} (h : Y ∈ ncT T X) :
    ncT T X = n₀c Y := by
  obtain ⟨e⟩ := h
  rw [n₀c_eq_ncT]; exact ncT_congr e.symm

private theorem ncT_eq_n₀c {α : Type uA} {X : Type uX} (h : Nonempty (X ↪ α)) :
    ∃ A : Set α, ncT α X = n₀c A := by
  obtain ⟨A, hA⟩ := ncT_nonempty_iff.2 h
  exact ⟨A, ncT_eq_n₀c_of_mem hA⟩

private theorem n₀c_ne_empty' {α : Type uA} : ∀ B : Set α, (∅ : Set (Set α)) ≠ n₀c B :=
  fun B h => n₀c_ne_empty B h.symm

/-- An embedding of a class into its type. -/
private def setEmb {α : Type uA} (A : Set α) : ↥A ↪ α := Function.Embedding.subtype _

private theorem emb_self {α : Type uA} (A : Set α) : Nonempty (↥A ↪ α) := ⟨setEmb A⟩

/-- `N₀c'α` exists as a member of `NC`: a cardinal of `NC` is `Λ` or homogeneous. -/
private theorem NC_cases {α : Type uA} {β : Type uB} {μ : Set (Set α)} (h : μ ∈ NC β) :
    μ = ∅ ∨ ∃ A : Set α, μ = n₀c A := by
  obtain ⟨B, rfl⟩ := h
  rcases (nc α B).eq_empty_or_nonempty with h | ⟨X, hX⟩
  · exact Or.inl h
  · exact Or.inr ⟨X, nc_eq_n₀c_of_mem hX⟩

private theorem n₀c_mem_NC {α : Type uA} (A : Set α) : n₀c A ∈ (NC α : Set (Set (Set α))) :=
  ⟨A, n₀c_eq_nc A⟩

private theorem n₀c_mem_N₀C {α : Type uA} (A : Set α) : n₀c A ∈ (N₀C : Set (Set (Set α))) :=
  ⟨A, rfl⟩

private theorem eq_n₀c_iff_equiv {α : Type uA} {A B : Set α} : n₀c A = n₀c B ↔ Nonempty (↥A ≃ ↥B) := by
  rw [n₀c_eq_n₀c_iff, sm_iff_nonempty_equiv]

private theorem n₀c_eq_zero_iff {α : Type uA} {A : Set α} : n₀c A = zero ↔ A = ∅ := by
  rw [zero_eq_n₀c_empty, eq_n₀c_iff_equiv]
  constructor
  · rintro ⟨e⟩; exact Set.eq_empty_iff_forall_notMem.2 fun a ha => (e ⟨a, ha⟩).2
  · rintro rfl; exact ⟨Equiv.refl _⟩

private theorem n₀c_eq_one_iff {α : Type uA} {A : Set α} :
    n₀c A = one ↔ ∃ x, A = {x} := by
  constructor
  · intro h
    have : A ∈ (one : Set (Set α)) := h ▸ self_mem_n₀c A
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩; exact (one_eq_n₀c_singleton x).symm

/-! ### Similarity images -/

private theorem sm_img_empty {α : Type uA} {T : Type uT} :
    (sm ʻʻ (∅ : Set (Set α)) : Set (Set T)) = ∅ := by
  ext X; simp [img]

private theorem sm_img_ncT {α : Type uA} {T : Type uT} {X : Type uX} (h : Nonempty (X ↪ α)) :
    (sm ʻʻ ncT α X : Set (Set T)) = ncT T X := by
  obtain ⟨A, hA⟩ := ncT_eq_n₀c h
  have hAX : A ∈ ncT α X := hA ▸ self_mem_n₀c A
  rw [hA, sm_img_n₀c, nc_eq_ncT]
  obtain ⟨e⟩ := hAX
  exact ncT_congr e

private theorem sm_img_ncT_of_not {α : Type uA} {T : Type uT} {X : Type uX}
    (h : ¬ Nonempty (X ↪ α)) : (sm ʻʻ ncT α X : Set (Set T)) = ∅ := by
  rw [ncT_eq_empty h, sm_img_empty]

private theorem sm_img_n₀c' {α : Type uA} {T : Type uT} (A : Set α) :
    (sm ʻʻ n₀c A : Set (Set T)) = ncT T A := by
  rw [sm_img_n₀c, nc_eq_ncT]

/-! ### Sums -/

private theorem cardAdd_n₀c {α : Type uA} {β : Type uB} {T : Type uT} (A : Set α) (B : Set β) :
    (n₀c A +ᶜ n₀c B : Set (Set T)) = ncT T (↥A ⊕ ↥B) := by
  rw [n₀c_cardAdd_n₀c, nc_eq_ncT]; exact ncT_congr (clsSumEquiv A B)

private theorem cardAdd_ncT {α : Type uA} {β : Type uB} {T : Type uT} {X : Type uX} {Y : Type uY}
    (hX : Nonempty (X ↪ α)) (hY : Nonempty (Y ↪ β)) :
    (ncT α X +ᶜ ncT β Y : Set (Set T)) = ncT T (X ⊕ Y) := by
  obtain ⟨A, hA⟩ := ncT_eq_n₀c hX
  obtain ⟨B, hB⟩ := ncT_eq_n₀c hY
  have hAX : A ∈ ncT α X := hA ▸ self_mem_n₀c A
  have hBY : B ∈ ncT β Y := hB ▸ self_mem_n₀c B
  obtain ⟨e⟩ := hAX; obtain ⟨f⟩ := hBY
  rw [hA, hB, cardAdd_n₀c]; exact ncT_congr (e.sumCongr f)

private theorem cardAdd_empty_left {α : Type uA} {β : Type uB} {T : Type uT} (ν : Set (Set β)) :
    ((∅ : Set (Set α)) +ᶜ ν : Set (Set T)) = ∅ :=
  cardAdd_eq_empty_of_left (n₀c_ne_empty') ν

private theorem cardAdd_empty_right {α : Type uA} {β : Type uB} {T : Type uT} (μ : Set (Set α)) :
    (μ +ᶜ (∅ : Set (Set β)) : Set (Set T)) = ∅ :=
  cardAdd_eq_empty_of_right μ (n₀c_ne_empty')

/-! ### Products -/

private theorem mem_clsTimes {α : Type uA} {β : Type uB} {A : Set α} {B : Set β}
    {R : α → β → Prop} : R ∈ B ×ₐ A ↔ ∃ x y, (x ∈ A ∧ y ∈ B) ∧ R = x ↓ y := by
  constructor
  · rintro ⟨S, ⟨y, hy, hS⟩, hR⟩
    rw [hS] at hR
    obtain ⟨x, hx, h⟩ := hR
    exact ⟨x, y, ⟨hx, hy⟩, h⟩
  · rintro ⟨x, y, hxy, rfl⟩
    exact couple_mem_clsTimes.2 hxy

private noncomputable def clsTimesEquiv {α : Type uA} {β : Type uB} (B : Set β) (A : Set α) :
    ↥(B ×ₐ A) ≃ ↥A × ↥B :=
  (Equiv.ofBijective (fun p : ↥A × ↥B => (⟨(p.1 : α) ↓ (p.2 : β),
      couple_mem_clsTimes.2 ⟨p.1.2, p.2.2⟩⟩ : ↥(B ×ₐ A)))
    ⟨fun p q h => by
      have h' := couple_eq_couple_iff.1 (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext h'.1) (Subtype.ext h'.2),
     fun ⟨R, hR⟩ => by
      obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 hR
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩⟩).symm

private theorem cardMul_n₀c {α : Type uA} {β : Type uB} {T : Type uT} (A : Set α) (B : Set β) :
    (n₀c A ×ᶜ n₀c B : Set (Set T)) = ncT T (↥A × ↥B) := by
  ext ξ
  constructor
  · rintro ⟨A', B', ⟨hA, hB⟩, h⟩
    obtain ⟨eA⟩ := eq_n₀c_iff_equiv.1 hA
    obtain ⟨eB⟩ := eq_n₀c_iff_equiv.1 hB
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
    exact ⟨e.trans ((clsTimesEquiv A' B').trans ((Equiv.prodComm _ _).trans
      (eA.symm.prodCongr eB.symm)))⟩
  · rintro ⟨e⟩
    exact ⟨A, B, ⟨rfl, rfl⟩, sm_iff_nonempty_equiv.2 ⟨e.trans ((Equiv.prodComm _ _).trans
      (clsTimesEquiv A B).symm)⟩⟩

end Helpers

section Helpers2

open Classical

universe uA uB uC uT uX uY uZ

private theorem cardMul_eq_empty_of_left {α : Type uA} {β : Type uB} {T : Type uT}
    {μ : Set (Set α)} (h : ∀ A, μ ≠ n₀c A) (ν : Set (Set β)) : (μ ×ᶜ ν : Set (Set T)) = ∅ := by
  ext ξ; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨hA, -⟩, -⟩; exact h A hA

private theorem cardMul_eq_empty_of_right {α : Type uA} {β : Type uB} {T : Type uT}
    (μ : Set (Set α)) {ν : Set (Set β)} (h : ∀ B, ν ≠ n₀c B) : (μ ×ᶜ ν : Set (Set T)) = ∅ := by
  ext ξ; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨-, hB⟩, -⟩; exact h B hB

private theorem cardExp_eq_empty_of_left {α : Type uA} {β : Type uB} {T : Type uT}
    {μ : Set (Set α)} (h : ∀ A, μ ≠ n₀c A) (ν : Set (Set β)) : (μ ^ᶜ ν : Set (Set T)) = ∅ := by
  ext ξ; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨hA, -⟩, -⟩; exact h A hA

private theorem cardExp_eq_empty_of_right {α : Type uA} {β : Type uB} {T : Type uT}
    (μ : Set (Set α)) {ν : Set (Set β)} (h : ∀ B, ν ≠ n₀c B) : (μ ^ᶜ ν : Set (Set T)) = ∅ := by
  ext ξ; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨-, hB⟩, -⟩; exact h B hB

private theorem cardMul_ncT {α : Type uA} {β : Type uB} {T : Type uT} {X : Type uX} {Y : Type uY}
    (hX : Nonempty (X ↪ α)) (hY : Nonempty (Y ↪ β)) :
    (ncT α X ×ᶜ ncT β Y : Set (Set T)) = ncT T (X × Y) := by
  obtain ⟨A, hA⟩ := ncT_eq_n₀c hX
  obtain ⟨B, hB⟩ := ncT_eq_n₀c hY
  have hAX : A ∈ ncT α X := hA ▸ self_mem_n₀c A
  have hBY : B ∈ ncT β Y := hB ▸ self_mem_n₀c B
  obtain ⟨e⟩ := hAX; obtain ⟨f⟩ := hBY
  rw [hA, hB, cardMul_n₀c]; exact ncT_congr (e.prodCongr f)

/-! ### Exponentiation: `α exp β` is the class of graphs of functions from `β` to `α` -/

/-- The class of couples `f'y ↓ y` (the "graph" of `f : β → α` in PM's sense). -/
private def graphCls {α : Type uA} {β : Type uB} {A : Set α} {B : Set β} (f : ↥B → ↥A) :
    Set (α → β → Prop) := {R | ∃ y : ↥B, R = (f y : α) ↓ (y : β)}

private theorem graphCls_mem_clsExp {α : Type uA} {β : Type uB} {A : Set α} {B : Set β}
    (f : ↥B → ↥A) : graphCls f ∈ clsExp A B := by
  refine ⟨fun r k => r ∈ graphCls f ∧ k ∈ coupleImg A ʻʻ B ∧ r ∈ k, ?_, ?_⟩
  · refine mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩
    · rintro r r' k ⟨⟨⟨y, rfl⟩, ⟨y0, hy0, rfl⟩, ⟨x, hx, h1⟩⟩, ⟨⟨y', rfl⟩, -, ⟨x', hx', h2⟩⟩⟩
      have e1 := (couple_eq_couple_iff.1 h1).2
      have e2 := (couple_eq_couple_iff.1 h2).2
      have : y = y' := Subtype.ext (e1.trans e2.symm)
      subst this; rfl
    · rintro r k ⟨-, -, h⟩; exact h
    · ext k
      constructor
      · rintro ⟨r, -, hk, -⟩; exact hk
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(f ⟨y, hy⟩ : α) ↓ y, ⟨⟨y, hy⟩, rfl⟩, ⟨y, hy, rfl⟩, ⟨_, (f ⟨y, hy⟩).2, rfl⟩⟩
  · show graphCls f = dom _
    ext r
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, ⟨y, rfl⟩, ⟨y, y.2, rfl⟩, ⟨_, (f y).2, rfl⟩⟩
    · rintro ⟨k, h, -, -⟩; exact h

private theorem exists_graphCls_of_mem {α : Type uA} {β : Type uB} {A : Set α} {B : Set β}
    {S : Set (α → β → Prop)} (hS : S ∈ clsExp A B) : ∃ f : ↥B → ↥A, S = graphCls f := by
  obtain ⟨M, hM, hSM⟩ := hS
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_sel_iff.1 hM
  have h1' := mem_arrow_one_Cls.1 h1
  have hSM' : S = dom M := hSM
  have key : ∀ y : ↥B, ∃ x : ↥A, M ((x : α) ↓ (y : β)) (opImg couple A y) := by
    intro y
    have hk : opImg couple A (y : β) ∈ codom M := by rw [h3]; exact ⟨y, y.2, rfl⟩
    obtain ⟨r, hr⟩ := hk
    obtain ⟨x, hx, rfl⟩ := h2 r _ hr
    exact ⟨⟨x, hx⟩, hr⟩
  choose f hf using key
  refine ⟨f, ?_⟩
  rw [hSM']
  ext r
  constructor
  · rintro ⟨k, hrk⟩
    have hk : k ∈ codom M := ⟨r, hrk⟩
    rw [h3] at hk
    obtain ⟨y, hy, rfl⟩ := hk
    exact ⟨⟨y, hy⟩, h1' r _ _ ⟨hrk, hf ⟨y, hy⟩⟩⟩
  · rintro ⟨y, rfl⟩; exact ⟨_, hf y⟩

private theorem graphCls_injective {α : Type uA} {β : Type uB} {A : Set α} {B : Set β} :
    Function.Injective (graphCls : (↥B → ↥A) → Set (α → β → Prop)) := by
  intro f g h
  funext y
  have : (f y : α) ↓ (y : β) ∈ graphCls g := h ▸ ⟨y, rfl⟩
  obtain ⟨y', h'⟩ := this
  obtain ⟨e1, e2⟩ := couple_eq_couple_iff.1 h'
  have : y = y' := Subtype.ext e2
  subst this
  exact Subtype.ext e1

private noncomputable def clsExpEquiv {α : Type uA} {β : Type uB} (A : Set α) (B : Set β) :
    ↥(clsExp A B) ≃ (↥B → ↥A) :=
  (Equiv.ofBijective (fun f => (⟨graphCls f, graphCls_mem_clsExp f⟩ : ↥(clsExp A B)))
    ⟨fun f g h => graphCls_injective (congrArg Subtype.val h),
     fun ⟨S, hS⟩ => by
      obtain ⟨f, rfl⟩ := exists_graphCls_of_mem hS
      exact ⟨f, rfl⟩⟩).symm

private theorem cardExp_n₀c {α : Type uA} {β : Type uB} {T : Type uT} (A : Set α) (B : Set β) :
    (n₀c A ^ᶜ n₀c B : Set (Set T)) = ncT T (↥B → ↥A) := by
  ext ξ
  constructor
  · rintro ⟨A', B', ⟨hA, hB⟩, h⟩
    obtain ⟨eA⟩ := eq_n₀c_iff_equiv.1 hA
    obtain ⟨eB⟩ := eq_n₀c_iff_equiv.1 hB
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
    exact ⟨e.trans ((clsExpEquiv A' B').trans (Equiv.arrowCongr eB.symm eA.symm))⟩
  · rintro ⟨e⟩
    exact ⟨A, B, ⟨rfl, rfl⟩, sm_iff_nonempty_equiv.2 ⟨e.trans (clsExpEquiv A B).symm⟩⟩

private theorem cardExp_ncT {α : Type uA} {β : Type uB} {T : Type uT} {X : Type uX} {Y : Type uY}
    (hX : Nonempty (X ↪ α)) (hY : Nonempty (Y ↪ β)) :
    (ncT α X ^ᶜ ncT β Y : Set (Set T)) = ncT T (Y → X) := by
  obtain ⟨A, hA⟩ := ncT_eq_n₀c hX
  obtain ⟨B, hB⟩ := ncT_eq_n₀c hY
  have hAX : A ∈ ncT α X := hA ▸ self_mem_n₀c A
  have hBY : B ∈ ncT β Y := hB ▸ self_mem_n₀c B
  obtain ⟨e⟩ := hAX; obtain ⟨f⟩ := hBY
  rw [hA, hB, cardExp_n₀c]; exact ncT_congr (Equiv.arrowCongr f e)

/-! ### Comparison -/

private theorem cl_inter_nc_nonempty {α : Type uA} {β : Type uB} {A : Set α} {B : Set β} :
    (cl A ∩ nc α B).Nonempty ↔ Nonempty (↥B ↪ ↥A) := by
  constructor
  · rintro ⟨C, hCA, hCB⟩
    obtain ⟨e⟩ := mem_nc_iff_equiv.1 hCB
    exact ⟨e.symm.toEmbedding.trans ⟨Set.inclusion hCA, Set.inclusion_injective hCA⟩⟩
  · rintro ⟨f⟩
    refine ⟨Set.range (fun b => (f b : α)), ?_, ?_⟩
    · rintro _ ⟨b, rfl⟩; exact (f b).2
    · exact mem_nc_iff_equiv.2
        ⟨(Equiv.ofInjective _ (Subtype.val_injective.comp f.injective)).symm⟩

private theorem emb_congr {X : Type uX} {Y : Type uY} {X' : Type uA} {Y' : Type uB}
    (e : X ≃ X') (f : Y ≃ Y') : Nonempty (X ↪ Y) ↔ Nonempty (X' ↪ Y') :=
  ⟨fun ⟨g⟩ => ⟨e.symm.toEmbedding.trans (g.trans f.toEmbedding)⟩,
   fun ⟨g⟩ => ⟨e.toEmbedding.trans (g.trans f.symm.toEmbedding)⟩⟩

private theorem cardGt_n₀c {α : Type uA} {β : Type uB} {A : Set α} {B : Set β} :
    n₀c A >ᶜ n₀c B ↔ Nonempty (↥B ↪ ↥A) ∧ ¬ Nonempty (↥A ↪ ↥B) := by
  constructor
  · rintro ⟨A', B', ⟨⟨hA, hB⟩, h1⟩, h2⟩
    obtain ⟨eA⟩ := eq_n₀c_iff_equiv.1 hA
    obtain ⟨eB⟩ := eq_n₀c_iff_equiv.1 hB
    rw [cl_inter_nc_nonempty] at h1 h2
    exact ⟨(emb_congr eB eA).2 h1, fun h => h2 ((emb_congr eA eB).1 h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨A, B, ⟨⟨rfl, rfl⟩, cl_inter_nc_nonempty.2 h1⟩, fun h => h2 (cl_inter_nc_nonempty.1 h)⟩

private theorem cardGt_iff {α : Type uA} {β : Type uB} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ >ᶜ ν ↔ ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧
      (Nonempty (↥B ↪ ↥A) ∧ ¬ Nonempty (↥A ↪ ↥B)) := by
  constructor
  · intro h
    obtain ⟨A, B, ⟨⟨hA, hB⟩, -⟩, -⟩ := id h
    subst hA hB
    exact ⟨A, B, ⟨rfl, rfl⟩, cardGt_n₀c.1 h⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩; exact cardGt_n₀c.2 h

private theorem cardGe_n₀c {α : Type uA} {β : Type uB} {A : Set α} {B : Set β} :
    n₀c A ≥ᶜ n₀c B ↔ Nonempty (↥B ↪ ↥A) := by
  have key : n₀c A = (sm ʻʻ n₀c B : Set (Set α)) ↔ Nonempty (↥A ≃ ↥B) := by
    rw [sm_img_n₀c, n₀c_eq_nc, nc_eq_nc_iff ⟨A, self_mem_nc A⟩, sm_iff_nonempty_equiv]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact (cardGt_n₀c.1 h).1
    · obtain ⟨e⟩ := key.1 h; exact ⟨e.symm.toEmbedding⟩
  · intro h
    by_cases h' : Nonempty (↥A ↪ ↥B)
    · obtain ⟨f⟩ := h; obtain ⟨g⟩ := h'
      exact Or.inr ⟨⟨n₀c_mem_N₀C A, n₀c_mem_N₀C B⟩, key.2 (Function.Embedding.antisymm g f)⟩
    · exact Or.inl (cardGt_n₀c.2 ⟨h, h'⟩)

private theorem cardGe_iff {α : Type uA} {β : Type uB} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ≥ᶜ ν ↔ ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ Nonempty (↥B ↪ ↥A) := by
  constructor
  · intro h
    have : ∃ (A : Set α) (B : Set β), μ = n₀c A ∧ ν = n₀c B := by
      rcases h with ⟨A, B, ⟨⟨hA, hB⟩, -⟩, -⟩ | ⟨⟨⟨A, hA⟩, ⟨B, hB⟩⟩, -⟩
      · exact ⟨A, B, hA, hB⟩
      · exact ⟨A, B, hA, hB⟩
    obtain ⟨A, B, rfl, rfl⟩ := this
    exact ⟨A, B, ⟨rfl, rfl⟩, cardGe_n₀c.1 h⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩; exact cardGe_n₀c.2 h

end Helpers2

section Helpers3

open Classical

universe uA uB uC uT uX uY uZ

private theorem emb_sum_left {X : Type uX} {Y : Type uY} {T : Type uT} :
    Nonempty (X ⊕ Y ↪ T) → Nonempty (X ↪ T) := fun ⟨f⟩ => ⟨Function.Embedding.inl.trans f⟩

private theorem emb_sum_right {X : Type uX} {Y : Type uY} {T : Type uT} :
    Nonempty (X ⊕ Y ↪ T) → Nonempty (Y ↪ T) := fun ⟨f⟩ => ⟨Function.Embedding.inr.trans f⟩

private theorem emb_prod_left {X : Type uX} {Y : Type uY} {T : Type uT} (hY : Nonempty Y) :
    Nonempty (X × Y ↪ T) → Nonempty (X ↪ T) := fun ⟨f⟩ =>
  ⟨(Function.Embedding.sectL X hY.some).trans f⟩

private theorem emb_prod_right {X : Type uX} {Y : Type uY} {T : Type uT} (hX : Nonempty X) :
    Nonempty (X × Y ↪ T) → Nonempty (Y ↪ T) := fun ⟨f⟩ =>
  ⟨(Function.Embedding.sectR hX.some Y).trans f⟩

private theorem emb_arrow_const {X : Type uX} {Y : Type uY} {T : Type uT} (hY : Nonempty Y) :
    Nonempty ((Y → X) ↪ T) → Nonempty (X ↪ T) := fun ⟨f⟩ =>
  ⟨(⟨Function.const Y, Function.const_injective⟩ : X ↪ (Y → X)).trans f⟩

/-- `Y ↪ (Y → X)` when `X` has two members. -/
private noncomputable def embIndicator {X : Type uX} {Y : Type uY} (a b : X) (hab : a ≠ b) :
    Y ↪ (Y → X) :=
  ⟨fun y y' => if y' = y then b else a, fun y y' h => by
    by_contra hne
    have h1 : (if y = y then b else a) = (if y = y' then b else a) := congrFun h y
    have h2 : (if y = y then b else a) = b := by simp
    have h3 : (if y = y' then b else a) = a := by simp [hne]
    exact hab (h3.symm.trans (h1.symm.trans h2))⟩

private theorem emb_arrow_dom {X : Type uX} {Y : Type uY} {T : Type uT} {a b : X} (hab : a ≠ b) :
    Nonempty ((Y → X) ↪ T) → Nonempty (Y ↪ T) := fun ⟨f⟩ =>
  ⟨(embIndicator a b hab).trans f⟩

private theorem nonempty_of_n₀c_ne_zero {α : Type uA} {A : Set α} (h : n₀c A ≠ zero) :
    Nonempty ↥A := by
  rw [Ne, n₀c_eq_zero_iff, ← Set.not_nonempty_iff_eq_empty, not_not] at h
  exact h.to_subtype

private theorem two_of_n₀c_ne {α : Type uA} {A : Set α} (h0 : n₀c A ≠ zero) (h1 : n₀c A ≠ one) :
    ∃ a b : ↥A, a ≠ b := by
  obtain ⟨a⟩ := nonempty_of_n₀c_ne_zero h0
  by_contra h
  push Not at h
  exact h1 (n₀c_eq_one_iff.2 ⟨a, Set.eq_singleton_iff_unique_mem.2 ⟨a.2, fun x hx =>
    congrArg Subtype.val (h ⟨x, hx⟩ a)⟩⟩)

end Helpers3

section Helpers4

open Classical

universe uA uB uC uT uX uY uZ

/-- `ncT α X` "behaves" in the type `T`: it exists in its own type, or `X` does not fit in `T`. -/
private def Good (α : Type uA) (X : Type uX) (T : Type uT) : Prop :=
  Nonempty (X ↪ α) ∨ ¬ Nonempty (X ↪ T)

private theorem good_self {α : Type uA} (A : Set α) (T : Type uT) : Good α ↥A T := Or.inl (emb_self A)

private theorem good_T (T : Type uT) (X : Type uX) : Good T X T := by
  by_cases h : Nonempty (X ↪ T)
  · exact Or.inl h
  · exact Or.inr h

private theorem cardAdd_gen {α : Type uA} {β : Type uB} {T : Type uT} {X : Type uX} {Y : Type uY}
    (hX : Good α X T) (hY : Good β Y T) :
    (ncT α X +ᶜ ncT β Y : Set (Set T)) = ncT T (X ⊕ Y) := by
  rcases hX with hX | hX
  · rcases hY with hY | hY
    · exact cardAdd_ncT hX hY
    · by_cases hY' : Nonempty (Y ↪ β)
      · exact cardAdd_ncT hX hY'
      · rw [ncT_eq_empty hY', cardAdd_empty_right]
        exact (ncT_eq_empty fun h => hY (emb_sum_right h)).symm
  · by_cases hX' : Nonempty (X ↪ α)
    · rcases hY with hY | hY
      · exact cardAdd_ncT hX' hY
      · by_cases hY' : Nonempty (Y ↪ β)
        · exact cardAdd_ncT hX' hY'
        · rw [ncT_eq_empty hY', cardAdd_empty_right]
          exact (ncT_eq_empty fun h => hY (emb_sum_right h)).symm
    · rw [ncT_eq_empty hX', cardAdd_empty_left]
      exact (ncT_eq_empty fun h => hX (emb_sum_left h)).symm

private theorem cardMul_empty_left {α : Type uA} {β : Type uB} {T : Type uT} (ν : Set (Set β)) :
    ((∅ : Set (Set α)) ×ᶜ ν : Set (Set T)) = ∅ :=
  cardMul_eq_empty_of_left n₀c_ne_empty' ν

private theorem cardMul_empty_right {α : Type uA} {β : Type uB} {T : Type uT} (μ : Set (Set α)) :
    (μ ×ᶜ (∅ : Set (Set β)) : Set (Set T)) = ∅ :=
  cardMul_eq_empty_of_right μ n₀c_ne_empty'

private theorem cardExp_empty_left {α : Type uA} {β : Type uB} {T : Type uT} (ν : Set (Set β)) :
    ((∅ : Set (Set α)) ^ᶜ ν : Set (Set T)) = ∅ :=
  cardExp_eq_empty_of_left n₀c_ne_empty' ν

private theorem cardExp_empty_right {α : Type uA} {β : Type uB} {T : Type uT} (μ : Set (Set α)) :
    (μ ^ᶜ (∅ : Set (Set β)) : Set (Set T)) = ∅ :=
  cardExp_eq_empty_of_right μ n₀c_ne_empty'

/-- Products: if a factor does not exist in its type, both sides vanish, provided the other factor
is not empty. -/
private theorem cardMul_gen' {α : Type uA} {β : Type uB} {T : Type uT} {X : Type uX} {Y : Type uY}
    (hX : Good α X T) (hY : Good β Y T) (hXn : Nonempty X) (hYn : Nonempty Y) :
    (ncT α X ×ᶜ ncT β Y : Set (Set T)) = ncT T (X × Y) := by
  by_cases hX' : Nonempty (X ↪ α)
  · by_cases hY' : Nonempty (Y ↪ β)
    · exact cardMul_ncT hX' hY'
    · rw [ncT_eq_empty hY', cardMul_empty_right]
      refine (ncT_eq_empty fun h => ?_).symm
      rcases hY with hY | hY
      · exact hY' hY
      · exact hY (emb_prod_right hXn h)
  · rw [ncT_eq_empty hX', cardMul_empty_left]
    refine (ncT_eq_empty fun h => ?_).symm
    rcases hX with hX | hX
    · exact hX' hX
    · exact hX (emb_prod_left hYn h)

private theorem cardAdd_nonempty_iff {α : Type uA} {β : Type uB} {T : Type uT}
    {μ : Set (Set α)} {ν : Set (Set β)} : (μ +ᶜ ν : Set (Set T)).Nonempty ↔
      ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ Nonempty (↥A ⊕ ↥B ↪ T) := by
  constructor
  · rintro ⟨ξ, A, B, ⟨rfl, rfl⟩, h⟩
    refine ⟨A, B, ⟨rfl, rfl⟩, ncT_nonempty_iff.1 ?_⟩
    rw [← cardAdd_n₀c]; exact ⟨ξ, A, B, ⟨rfl, rfl⟩, h⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    rw [cardAdd_n₀c]; exact ncT_nonempty_iff.2 h

private theorem cardMul_nonempty_iff {α : Type uA} {β : Type uB} {T : Type uT}
    {μ : Set (Set α)} {ν : Set (Set β)} : (μ ×ᶜ ν : Set (Set T)).Nonempty ↔
      ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ Nonempty (↥A × ↥B ↪ T) := by
  constructor
  · rintro ⟨ξ, A, B, ⟨rfl, rfl⟩, h⟩
    refine ⟨A, B, ⟨rfl, rfl⟩, ncT_nonempty_iff.1 ?_⟩
    rw [← cardMul_n₀c]; exact ⟨ξ, A, B, ⟨rfl, rfl⟩, h⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    rw [cardMul_n₀c]; exact ncT_nonempty_iff.2 h

private theorem cardExp_nonempty_iff {α : Type uA} {β : Type uB} {T : Type uT}
    {μ : Set (Set α)} {ν : Set (Set β)} : (μ ^ᶜ ν : Set (Set T)).Nonempty ↔
      ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ Nonempty ((↥B → ↥A) ↪ T) := by
  constructor
  · rintro ⟨ξ, A, B, ⟨rfl, rfl⟩, h⟩
    refine ⟨A, B, ⟨rfl, rfl⟩, ncT_nonempty_iff.1 ?_⟩
    rw [← cardExp_n₀c]; exact ⟨ξ, A, B, ⟨rfl, rfl⟩, h⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, h⟩
    rw [cardExp_n₀c]; exact ncT_nonempty_iff.2 h

private theorem sm_img_nonempty_iff {α : Type uA} {T : Type uT} {μ : Set (Set α)} :
    (sm ʻʻ μ : Set (Set T)).Nonempty ↔ ∃ A : Set α, A ∈ μ ∧ Nonempty (↥A ↪ T) := by
  constructor
  · rintro ⟨X, A, hA, hXA⟩
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hXA
    exact ⟨A, hA, ⟨e.symm.toEmbedding.trans (setEmb X)⟩⟩
  · rintro ⟨A, hA, h⟩
    obtain ⟨X, ⟨e⟩⟩ := ncT_nonempty_iff.2 h
    exact ⟨X, A, hA, sm_iff_nonempty_equiv.2 ⟨e⟩⟩

end Helpers4

section Helpers5

open Classical

universe uA uB uC uT uX uY uZ uW

/-- Adequacy of `W` for `μ +_c ν` gives room in `W` for `α + β` (`α`, `β` of the types of the
members of `μ`, `ν`). -/
private theorem adeqAdd_emb {α : Type uA} {β : Type uB} {W : Type uW} {μ : Set (Set α)}
    {ν : Set (Set β)} (h : AdeqAdd W μ ν) (A : Set α) (B : Set β) :
    Nonempty (↥A ⊕ ↥B ↪ W) := by
  obtain ⟨f, hf⟩ := adeqAdd_iff.1 h
  exact ⟨⟨fun s => f (Sum.map Subtype.val Subtype.val s),
    hf.comp (Sum.map_injective.2 ⟨Subtype.val_injective, Subtype.val_injective⟩)⟩⟩

private def typ₁_emb {α : Type uA} (μ : Set (Set α)) (A : Set α) : ↥A ↪ ↥(typ₁ μ) :=
  ⟨fun a => ⟨a, by rw [typ₁, typ₀_eq_univ]; trivial⟩, fun a b h =>
    Subtype.ext (congrArg Subtype.val h :)⟩

private theorem adeqMul_emb {α : Type uA} {β : Type uB} {W : Type uW} {μ : Set (Set α)}
    {ν : Set (Set β)} (h : AdeqMul W μ ν) (A : Set α) (B : Set β) :
    Nonempty (↥A × ↥B ↪ W) := by
  rw [AdeqMul, cardMul_n₀c, ncT_nonempty_iff] at h
  obtain ⟨f⟩ := h
  exact ⟨((typ₁_emb μ A).prodMap (typ₁_emb ν B)).trans f⟩

private theorem adeqExp_emb {α : Type uA} {β : Type uB} {W : Type uW} [Nonempty W]
    {μ : Set (Set α)} {ν : Set (Set β)} (h : AdeqExp W μ ν) (A : Set α) (B : Set β) :
    Nonempty ((↥B → ↥A) ↪ W) := by
  rw [AdeqExp, cardExp_n₀c, ncT_nonempty_iff] at h
  obtain ⟨f⟩ := h
  have e1 : ↥(typ₁ μ) ≃ α :=
    (Set.equivOfEq (show typ₁ μ = Set.univ by rw [typ₁, typ₀_eq_univ])).trans (Equiv.Set.univ α)
  have e2 : ↥(typ₁ ν) ≃ β :=
    (Set.equivOfEq (show typ₁ ν = Set.univ by rw [typ₁, typ₀_eq_univ])).trans (Equiv.Set.univ β)
  have f' : (β → α) ↪ W := (Equiv.arrowCongr e2 e1).symm.toEmbedding.trans f
  by_cases hA : Nonempty ↥A
  · obtain ⟨a⟩ := hA
    refine ⟨(⟨fun g y => if h : y ∈ B then (g ⟨y, h⟩ : α) else (a : α), fun g g' hg => ?_⟩ :
      (↥B → ↥A) ↪ (β → α)).trans f'⟩
    funext y
    have h1 := congrFun hg (y : β)
    simp only [y.2, dite_true] at h1
    exact Subtype.ext h1
  · rw [not_nonempty_iff] at hA
    by_cases hB : Nonempty ↥B
    · have : IsEmpty (↥B → ↥A) := by
        obtain ⟨b⟩ := hB; exact ⟨fun g => isEmptyElim (g b)⟩
      exact ⟨⟨isEmptyElim, fun x => isEmptyElim x⟩⟩
    · rw [not_nonempty_iff] at hB
      have : Subsingleton (↥B → ↥A) := ⟨fun f g => funext fun b => isEmptyElim b⟩
      exact ⟨⟨fun _ => Classical.arbitrary W, fun x y _ => Subsingleton.elim x y⟩⟩

private theorem nat_mul_le_pow {m : ℕ} (hm : 2 ≤ m) : ∀ n : ℕ, m * n ≤ m ^ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    have ih := nat_mul_le_pow hm (n + 1)
    have h3 : m ≤ m ^ (n + 1) := Nat.le_self_pow (by omega) m
    have h4 := Nat.mul_le_mul_left (m ^ (n + 1)) hm
    rw [pow_succ]
    nlinarith

/-- `μ × ν ≤ μ^ν` when `μ ≥ 2`. -/
private theorem card_mul_le_pow {a b : Cardinal} (ha : 2 ≤ a) : a * b ≤ a ^ b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have h1 : a ≤ a ^ b := Cardinal.self_le_power a (Cardinal.one_le_iff_ne_zero.2 hb)
  have h2 : b ≤ a ^ b := ((Cardinal.cantor b).trans_le (Cardinal.power_le_power_right ha)).le
  rcases lt_or_ge (a ^ b) Cardinal.aleph0 with hf | hf
  · obtain ⟨m, rfl⟩ := Cardinal.lt_aleph0.1 (h1.trans_lt hf)
    obtain ⟨n, rfl⟩ := Cardinal.lt_aleph0.1 (h2.trans_lt hf)
    have hm : 2 ≤ m := by exact_mod_cast ha
    rw [Cardinal.power_natCast, ← Nat.cast_mul, ← Nat.cast_pow, Nat.cast_le]
    exact nat_mul_le_pow hm n
  · exact (mul_le_mul' h1 h2).trans (Cardinal.mul_eq_self hf).le

private theorem emb_prod_arrow {X : Type uX} {Y : Type uY} {T : Type uT} {a b : X} (hab : a ≠ b) :
    Nonempty ((Y → X) ↪ T) → Nonempty (X × Y ↪ T) := by
  rintro ⟨f⟩
  have h : Cardinal.mk (X × Y) ≤ Cardinal.mk (Y → X) := by
    rw [Cardinal.mk_prod, Cardinal.mk_arrow]
    apply card_mul_le_pow
    rw [← Cardinal.lift_two.{uY, uX}, Cardinal.lift_le]
    exact Cardinal.two_le_iff.2 ⟨a, b, hab⟩
  obtain ⟨g⟩ := (Cardinal.le_def _ _).1 h
  exact ⟨g.trans f⟩

private theorem emb_arrow_sum_left {X : Type uX} {Y : Type uY} {A : Type uA} {T : Type uT}
    [Nonempty T] : Nonempty ((X ⊕ Y → A) ↪ T) → Nonempty ((X → A) ↪ T) := by
  rintro ⟨f⟩
  by_cases h : Nonempty (X ⊕ Y → A)
  · obtain ⟨g⟩ := h
    exact ⟨(⟨fun k => Sum.elim k (g ∘ Sum.inr), fun k k' hk => funext fun x => by
      simpa using congrFun hk (Sum.inl x)⟩ : (X → A) ↪ (X ⊕ Y → A)).trans f⟩
  · by_cases hA : Nonempty A
    · obtain ⟨a⟩ := hA; exact absurd ⟨fun _ => a⟩ h
    · have : Subsingleton (X → A) := ⟨fun k k' => funext fun x => absurd ⟨k x⟩ hA⟩
      exact ⟨⟨fun _ => Classical.arbitrary T, fun x y _ => Subsingleton.elim x y⟩⟩

private theorem emb_arrow_sum_right {X : Type uX} {Y : Type uY} {A : Type uA} {T : Type uT}
    [Nonempty T] : Nonempty ((X ⊕ Y → A) ↪ T) → Nonempty ((Y → A) ↪ T) := fun ⟨f⟩ =>
  emb_arrow_sum_left ⟨(Equiv.arrowCongr (Equiv.sumComm Y X) (Equiv.refl A)).toEmbedding.trans f⟩

private theorem emb_arrow_prod_left {X : Type uX} {Y : Type uY} {C : Type uC} {T : Type uT}
    (hY : Nonempty (C → Y)) : Nonempty ((C → X × Y) ↪ T) → Nonempty ((C → X) ↪ T) := by
  rintro ⟨f⟩
  obtain ⟨g⟩ := hY
  exact ⟨(⟨fun k c => (k c, g c), fun k k' hk => funext fun c => by
    simpa using congrFun hk c⟩ : (C → X) ↪ (C → X × Y)).trans f⟩

private theorem emb_arrow_prod_right {X : Type uX} {Y : Type uY} {C : Type uC} {T : Type uT}
    (hX : Nonempty (C → X)) : Nonempty ((C → X × Y) ↪ T) → Nonempty ((C → Y) ↪ T) := fun ⟨f⟩ =>
  emb_arrow_prod_left hX ⟨(Equiv.arrowCongr (Equiv.refl C) (Equiv.prodComm Y X)).toEmbedding.trans f⟩

/-- One factor exists in its type and is not empty; the other behaves in `T`. -/
private theorem cardMul_goodR {α : Type uA} {β : Type uB} {T : Type uT} {X : Type uX}
    {Y : Type uY} (hX : Nonempty (X ↪ α)) (hY : Good β Y T) (hXn : Nonempty X) :
    (ncT α X ×ᶜ ncT β Y : Set (Set T)) = ncT T (X × Y) := by
  by_cases hY' : Nonempty (Y ↪ β)
  · exact cardMul_ncT hX hY'
  · rw [ncT_eq_empty hY', cardMul_empty_right]
    refine (ncT_eq_empty fun h => ?_).symm
    rcases hY with hY | hY
    · exact hY' hY
    · exact hY (emb_prod_right hXn h)

private theorem cardMul_goodL {α : Type uA} {β : Type uB} {T : Type uT} {X : Type uX}
    {Y : Type uY} (hX : Good α X T) (hY : Nonempty (Y ↪ β)) (hYn : Nonempty Y) :
    (ncT α X ×ᶜ ncT β Y : Set (Set T)) = ncT T (X × Y) := by
  by_cases hX' : Nonempty (X ↪ α)
  · exact cardMul_ncT hX' hY
  · rw [ncT_eq_empty hX', cardMul_empty_left]
    refine (ncT_eq_empty fun h => ?_).symm
    rcases hX with hX | hX
    · exact hX' hX
    · exact hX (emb_prod_left hYn h)

private theorem cardExp_goodBase {α : Type uA} {β : Type uB} {T : Type uT} {X : Type uX}
    {Y : Type uY} (hX : Good α X T) (hY : Nonempty (Y ↪ β)) (hYn : Nonempty Y) :
    (ncT α X ^ᶜ ncT β Y : Set (Set T)) = ncT T (Y → X) := by
  by_cases hX' : Nonempty (X ↪ α)
  · exact cardExp_ncT hX' hY
  · rw [ncT_eq_empty hX', cardExp_empty_left]
    refine (ncT_eq_empty fun h => ?_).symm
    rcases hX with hX | hX
    · exact hX' hX
    · exact hX (emb_arrow_const hYn h)

private theorem cardExp_goodExp {α : Type uA} {β : Type uB} {T : Type uT} {X : Type uX}
    {Y : Type uY} (hX : Nonempty (X ↪ α)) (hY : Good β Y T) {a b : X} (hab : a ≠ b) :
    (ncT α X ^ᶜ ncT β Y : Set (Set T)) = ncT T (Y → X) := by
  by_cases hY' : Nonempty (Y ↪ β)
  · exact cardExp_ncT hX hY'
  · rw [ncT_eq_empty hY', cardExp_empty_right]
    refine (ncT_eq_empty fun h => ?_).symm
    rcases hY with hY | hY
    · exact hY' hY
    · exact hY (emb_arrow_dom hab h)

/-- Each of two factors behaves in `T`, and the product of the types embeds only if both do. -/
private theorem cardMul_goodLR {α : Type uA} {β : Type uB} {T : Type uT} {X : Type uX}
    {Y : Type uY} (hX : Good α X T) (hY : Good β Y T)
    (hXY : Nonempty (X × Y ↪ T) → Nonempty (X ↪ T) ∧ Nonempty (Y ↪ T)) :
    (ncT α X ×ᶜ ncT β Y : Set (Set T)) = ncT T (X × Y) := by
  by_cases hX' : Nonempty (X ↪ α)
  · by_cases hY' : Nonempty (Y ↪ β)
    · exact cardMul_ncT hX' hY'
    · rw [ncT_eq_empty hY', cardMul_empty_right]
      refine (ncT_eq_empty fun h => ?_).symm
      rcases hY with hY | hY
      · exact hY' hY
      · exact hY (hXY h).2
  · rw [ncT_eq_empty hX', cardMul_empty_left]
    refine (ncT_eq_empty fun h => ?_).symm
    rcases hX with hX | hX
    · exact hX' hX
    · exact hX (hXY h).1

end Helpers5

/-- ✱118·01. \(\vdash \colon\ldotp \exists !\mu .\mu =\sigma .\supset :f\mu .\equiv .f\sigma \quad[*20·18]\)

The principle of arithmetical substitution. In Lean an equation `μ = σ` puts both sides in one
type, and `f` is a function on that type, so the substitution is ✱20·18 itself and the hypothesis
`∃!μ`, which PM needs because a formal number may be taken in different types in its different
occurrences (Prefatory Statement, V), is idle.

**Status.** proved (reading): Lean's equation fixes one type for `μ` and `σ` (Prefatory
Statement, V), so `∃!μ` is not used. -/
theorem pm118_01 {α : Type*} {μ σ : Set (Set α)} {f : Set (Set α) → Prop} :
    μ.Nonempty ∧ μ = σ → (f μ ↔ f σ) := by
  rintro ⟨-, rfl⟩; exact Iff.rfl

/-- ✱118·11. \(\vdash :\exists !\text{Nc}(\xi )ʻ\beta .\alpha \subset \beta .\supset .\exists !\text{Nc}(\xi )ʻ\alpha\)

`Nc(ξ)'β` is `nc T B` with `ξ : Set T`; `α ⊂ β` puts `α`, `β` in one type. -/
theorem pm118_11 {α T : Type*} {A B : Set α} :
    (nc T B).Nonempty ∧ A ⊆ B → (nc T A).Nonempty := by
  rintro ⟨h, hAB⟩
  rw [nc_eq_ncT, ncT_nonempty_iff] at h ⊢
  obtain ⟨f⟩ := h
  exact ⟨(⟨Set.inclusion hAB, Set.inclusion_injective hAB⟩ : ↥A ↪ ↥B).trans f⟩

/-- ✱118·12. \[\begin{align}&\vdash \colon\ldotp \text{Nc}ʻ\alpha \leq \text{Nc}ʻ\beta .\supset :\exists !\text{Nc}(\xi )ʻ\beta .\supset .\exists !\text{Nc}(\xi )ʻ\alpha \\ &[*117·32·107.*100·511]\end{align}\]

**Status.** proved (reading): the sides `Nc'α`, `Nc'β` of `≤` are `N₀c'α`, `N₀c'β` (✱117·02·03
and the note to ✱117·06, normal adjustment). -/
theorem pm118_12 {α β T : Type*} {A : Set α} {B : Set β} :
    n₀c A ≤ᶜ n₀c B → ((nc T B).Nonempty → (nc T A).Nonempty) := by
  intro h hB
  obtain ⟨f⟩ := cardGe_n₀c.1 h
  rw [nc_eq_ncT, ncT_nonempty_iff] at hB ⊢
  obtain ⟨g⟩ := hB
  exact ⟨f.trans g⟩

/-- ✱118·13. \(\vdash \colon\ldotp \mu \leq \nu .\supset :\exists !\text{ sm }_{\xi }ʻʻ\nu .\supset .\exists !\text{ sm }_{\xi }ʻʻ\mu \quad[*117·32]\)

`sm_ξ''μ` is `(sm ʻʻ μ : Set (Set T))` (`ξ : Set T`). -/
theorem pm118_13 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ≤ᶜ ν → ((sm ʻʻ ν : Set (Set T)).Nonempty → (sm ʻʻ μ : Set (Set T)).Nonempty) := by
  intro h hν
  obtain ⟨B, A, ⟨rfl, rfl⟩, ⟨f⟩⟩ := cardGe_iff.1 h
  rw [sm_img_n₀c', ncT_nonempty_iff] at hν ⊢
  obtain ⟨g⟩ := hν
  exact ⟨f.trans g⟩

/-- ✱118·2. \[\begin{align}&\vdash .(\mu +_{c}\nu )_{\xi }=\hat{\eta} \{(\exists \alpha ,\beta ).\mu =\text{N}_{0}\text{c}ʻ\alpha .\nu =\text{N}_{0}\text{c}ʻ\beta .\eta \text{ sm }_{\xi }(\alpha +\beta )\}\\ &[(*65·01·03).*110·2]\end{align}\]

`(μ +_c ν)_ξ` is the sum in the type `T` of `ξ` (ascription); `η sm_ξ (α + β)` is `sm η (A +ₐ B)`
with `η : Set T`. -/
theorem pm118_2 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ +ᶜ ν : Set (Set T)) =
      {η | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm η (A +ₐ B)} :=
  rfl

/-- ✱118·201. \[\begin{align}&\vdash :\exists !(\mu +_{c}\nu ).\supset .\text{ sm }_{\xi }ʻʻ(\mu +_{c}\nu )=(\mu +_{c}\nu )_{\xi }\\ &[\text{*110·44. Note Erratum in enunciation}]\end{align}\]

The logical occurrence of `μ +_c ν` (in `∃!`) and its argumental occurrence (in `sm_ξ''`) are
bound by IT (one type `W`); the equational occurrence is in the type `T` of `ξ`.

**Status.** proved (reading): convention IT (Prefatory Statement, IV): the logical and the
argumental occurrences of `μ +_c ν` share one type parameter `W`. -/
theorem pm118_201 {α β W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ +ᶜ ν : Set (Set W)).Nonempty →
      (sm ʻʻ (μ +ᶜ ν : Set (Set W)) : Set (Set T)) = (μ +ᶜ ν : Set (Set T)) := by
  intro h
  obtain ⟨A, B, ⟨rfl, rfl⟩, hW⟩ := cardAdd_nonempty_iff.1 h
  rw [cardAdd_n₀c, cardAdd_n₀c, sm_img_ncT hW]

/-- ✱118·21. \(\vdash :\exists !(\mu +_{c}\nu )_{\xi }.\supset .\exists !\text{ sm }_{\xi }ʻʻ\mu .\exists !\text{ sm }_{\xi }ʻʻ\nu\) -/
theorem pm118_21 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ +ᶜ ν : Set (Set T)).Nonempty →
      (sm ʻʻ μ : Set (Set T)).Nonempty ∧ (sm ʻʻ ν : Set (Set T)).Nonempty := by
  intro h
  obtain ⟨A, B, ⟨rfl, rfl⟩, hT⟩ := cardAdd_nonempty_iff.1 h
  rw [sm_img_n₀c', sm_img_n₀c', ncT_nonempty_iff, ncT_nonempty_iff]
  exact ⟨emb_sum_left hT, emb_sum_right hT⟩

private theorem add_sm_right {α β β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (hν : ν ∈ NC β₂) : (μ +ᶜ ν : Set (Set T)) = (μ +ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)) := by
  rcases NC_cases hν with rfl | ⟨B, rfl⟩
  · rw [sm_img_empty, cardAdd_empty_right, cardAdd_empty_right]
  · by_cases hμ : ∃ A, μ = n₀c A
    · obtain ⟨A, rfl⟩ := hμ
      rw [sm_img_n₀c', n₀c_eq_ncT A, n₀c_eq_ncT B, cardAdd_gen (good_self A T) (good_self B T),
        cardAdd_gen (good_self A T) (good_T T B)]
    · push Not at hμ
      rw [cardAdd_eq_empty_of_left hμ, cardAdd_eq_empty_of_left hμ]

private theorem add_sm_left {α β β₁ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (hμ : μ ∈ NC β₁) : (μ +ᶜ ν : Set (Set T)) = ((sm ʻʻ μ : Set (Set T)) +ᶜ ν : Set (Set T)) := by
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [sm_img_empty, cardAdd_empty_left, cardAdd_empty_left]
  · by_cases hν : ∃ B, ν = n₀c B
    · obtain ⟨B, rfl⟩ := hν
      rw [sm_img_n₀c', n₀c_eq_ncT A, n₀c_eq_ncT B, cardAdd_gen (good_self A T) (good_self B T),
        cardAdd_gen (good_T T A) (good_self B T)]
    · push Not at hν
      rw [cardAdd_eq_empty_of_right _ hν, cardAdd_eq_empty_of_right _ hν]

/-- ✱118·22. \[\begin{align}\vdash \colon\ldotp \mu ,\nu \in \text{NC}.\supset :&\exists !(\mu +_{c}\nu )_{\xi }.\equiv .\exists !(\text{ sm }_{\xi }ʻʻ\mu +_{c}\text{ sm }_{\xi }ʻʻ\nu )_{\xi }.\equiv .\\ &\exists !(\mu +_{c}\text{ sm }_{\xi }ʻʻ\nu )_{\xi }.\equiv .\exists !(\text{ sm }_{\xi }ʻʻ\mu +_{c}\nu )_{\xi }\end{align}\]

`μ, ν ∈ NC` is `μ ∈ NC β₁ ∧ ν ∈ NC β₂` (Prefatory Statement, V); the chain of three `≡` is the
conjunction of its links. -/
theorem pm118_22 {α β β₁ β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NC β₁ ∧ ν ∈ NC β₂ →
      (((μ +ᶜ ν : Set (Set T)).Nonempty ↔
          ((sm ʻʻ μ : Set (Set T)) +ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)).Nonempty) ∧
        (((sm ʻʻ μ : Set (Set T)) +ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)).Nonempty ↔
          (μ +ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)).Nonempty)) ∧
      ((μ +ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)).Nonempty ↔
          ((sm ʻʻ μ : Set (Set T)) +ᶜ ν : Set (Set T)).Nonempty) := by
  rintro ⟨hμ, hν⟩
  have e2 : (μ +ᶜ ν : Set (Set T)) =
      ((sm ʻʻ μ : Set (Set T)) +ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)) := by
    rw [add_sm_right hν, add_sm_left hμ]
  have e3 := add_sm_right (μ := μ) (T := T) hν
  have e4 := add_sm_left (ν := ν) (T := T) hμ
  rw [← e2, ← e3, ← e4]
  exact ⟨⟨Iff.rfl, Iff.rfl⟩, Iff.rfl⟩

/-- ✱118·23. \(\vdash :\mu ,\nu \in \text{NC}.\supset .(\mu +_{c}\nu )_{\xi }=(\text{ sm }_{\xi }ʻʻ\mu +_{c}\text{ sm }_{\xi }ʻʻ\nu )_{\xi }\) -/
theorem pm118_23 {α β β₁ β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NC β₁ ∧ ν ∈ NC β₂ → (μ +ᶜ ν : Set (Set T)) =
      ((sm ʻʻ μ : Set (Set T)) +ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)) := by
  rintro ⟨hμ, hν⟩
  rw [add_sm_right hν, add_sm_left hμ]

/-- ✱118·24. \(\vdash : \nu \in \text{NC} . \supset . (\mu +_{c} \nu )_{\xi } = (\mu +_{c} \text{ sm }_{\xi }ʻʻ\nu )_{\xi }\) -/
theorem pm118_24 {α β β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    ν ∈ NC β₂ → (μ +ᶜ ν : Set (Set T)) = (μ +ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)) :=
  add_sm_right

/-- ✱118·241. \(\vdash : \mu \in \text{NC} . \supset . (\mu +_{c} \nu )_{\xi } = (\text{ sm }_{\xi }ʻʻ\mu +_{c} \nu )_{\xi } \quad[*118·24 . *110·51]\) -/
theorem pm118_241 {α β β₁ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NC β₁ → (μ +ᶜ ν : Set (Set T)) = ((sm ʻʻ μ : Set (Set T)) +ᶜ ν : Set (Set T)) :=
  add_sm_left

/-- ✱118·25. \(\vdash . (\mu +_{c} \nu +_{c} \varpi )_{\xi } = \{(\mu +_{c} \nu )_{\xi } +_{c} \varpi\}_{\xi } = \{\mu +_{c} (\nu +_{c} \varpi )_{\xi }\}_{\xi}\)

`μ +_c ν +_c ϖ` is `(μ +_c ν) +_c ϖ` (✱110·561); its inner sum is an unsubscripted arithmetical
component, which IIT takes in an adequate type `W`; the subscripted sums are in the type `T` of
`ξ` and get no hypothesis. The chain is the conjunction of its links.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
unsubscripted arithmetical component `μ +_c ν` is adequate. -/
theorem pm118_25 {α β γ W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set γ)}
    (hW : AdeqAdd W μ ν) :
    ((μ +ᶜ ν : Set (Set W)) +ᶜ ϖ : Set (Set T)) = ((μ +ᶜ ν : Set (Set T)) +ᶜ ϖ : Set (Set T)) ∧
      ((μ +ᶜ ν : Set (Set T)) +ᶜ ϖ : Set (Set T)) =
        (μ +ᶜ (ν +ᶜ ϖ : Set (Set T)) : Set (Set T)) := by
  by_cases hμ : ∃ A, μ = n₀c A
  · by_cases hν : ∃ B, ν = n₀c B
    · obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν
      by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨C, rfl⟩ := hϖ
        rw [cardAdd_n₀c, cardAdd_n₀c, cardAdd_n₀c, n₀c_eq_ncT A, n₀c_eq_ncT C,
          cardAdd_gen (Or.inl (adeqAdd_emb hW A B)) (good_self C T),
          cardAdd_gen (good_T T _) (good_self C T), cardAdd_gen (good_self A T) (good_T T _)]
        exact ⟨rfl, ncT_congr (Equiv.sumAssoc _ _ _)⟩
      · push Not at hϖ
        simp only [cardAdd_eq_empty_of_right _ hϖ, cardAdd_empty_right, and_self]
    · push Not at hν
      simp only [cardAdd_eq_empty_of_right _ hν, cardAdd_eq_empty_of_left hν, cardAdd_empty_left,
        cardAdd_empty_right, and_self]
  · push Not at hμ
    simp only [cardAdd_eq_empty_of_left hμ, cardAdd_empty_left, and_self]

/-- ✱118·3. \[\begin{align}&\vdash . (\mu \times _{c} \nu )_{\xi } = \hat{\eta} \{(\exists \alpha , \beta ) . \mu = \text{N}_{0}\text{c}ʻ\alpha . \nu = \text{N}_{0}\text{c}ʻ\beta . \eta \text{ sm }_{\xi } (\alpha \times \beta )\}\\ &[(*65·01·03) . *113·2]\end{align}\] -/
theorem pm118_3 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ×ᶜ ν : Set (Set T)) =
      {η | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm η (A ×ₐ B)} :=
  rfl

/-- ✱118·301. \(\vdash : \exists ! (\mu \times _{c} \nu ) . \supset . \text{ sm }_{\xi }ʻʻ(\mu \times _{c} \nu ) = (\mu \times _{c} \nu )_{\xi } \quad[\text{Proof as in *118·201}]\)

**Status.** proved (reading): convention IT (Prefatory Statement, IV): the logical and the
argumental occurrences of `μ ×_c ν` share one type parameter `W`. -/
theorem pm118_301 {α β W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ×ᶜ ν : Set (Set W)).Nonempty →
      (sm ʻʻ (μ ×ᶜ ν : Set (Set W)) : Set (Set T)) = (μ ×ᶜ ν : Set (Set T)) := by
  intro h
  obtain ⟨A, B, ⟨rfl, rfl⟩, hW⟩ := cardMul_nonempty_iff.1 h
  rw [cardMul_n₀c, cardMul_n₀c, sm_img_ncT hW]

/-- ✱118·31. \(\vdash : \exists ! (\mu \times _{c} \nu )_{\xi } . \nu \neq 0 . \supset . \exists ! \text{ sm }_{\xi }ʻʻ\mu \) -/
theorem pm118_31 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ×ᶜ ν : Set (Set T)).Nonempty ∧ ν ≠ zero → (sm ʻʻ μ : Set (Set T)).Nonempty := by
  rintro ⟨h, hν⟩
  obtain ⟨A, B, ⟨rfl, rfl⟩, hT⟩ := cardMul_nonempty_iff.1 h
  rw [sm_img_n₀c', ncT_nonempty_iff]
  exact emb_prod_left (nonempty_of_n₀c_ne_zero hν) hT

/-- ✱118·311. \(\vdash : \exists ! (\mu \times _{c} \nu )_{\xi } . \mu \neq 0 . \supset . \exists ! \text{ sm }_{\xi }ʻʻ\nu \quad[*118·31 . *113·27]\) -/
theorem pm118_311 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ×ᶜ ν : Set (Set T)).Nonempty ∧ μ ≠ zero → (sm ʻʻ ν : Set (Set T)).Nonempty := by
  rintro ⟨h, hμ⟩
  obtain ⟨A, B, ⟨rfl, rfl⟩, hT⟩ := cardMul_nonempty_iff.1 h
  rw [sm_img_n₀c', ncT_nonempty_iff]
  exact emb_prod_right (nonempty_of_n₀c_ne_zero hμ) hT

private theorem mul_sm_right {α β β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (hν : ν ∈ NC β₂) (hμ0 : μ ≠ zero) :
    (μ ×ᶜ ν : Set (Set T)) = (μ ×ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)) := by
  rcases NC_cases hν with rfl | ⟨B, rfl⟩
  · rw [sm_img_empty, cardMul_empty_right, cardMul_empty_right]
  · by_cases hμ : ∃ A, μ = n₀c A
    · obtain ⟨A, rfl⟩ := hμ
      have hA := nonempty_of_n₀c_ne_zero hμ0
      rw [sm_img_n₀c', n₀c_eq_ncT A, n₀c_eq_ncT B, cardMul_ncT (emb_self A) (emb_self B),
        cardMul_goodR (emb_self A) (good_T T B) hA]
    · push Not at hμ
      rw [cardMul_eq_empty_of_left hμ, cardMul_eq_empty_of_left hμ]

private theorem mul_sm_left {α β β₁ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (hμ : μ ∈ NC β₁) (hν0 : ν ≠ zero) :
    (μ ×ᶜ ν : Set (Set T)) = ((sm ʻʻ μ : Set (Set T)) ×ᶜ ν : Set (Set T)) := by
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [sm_img_empty, cardMul_empty_left, cardMul_empty_left]
  · by_cases hν : ∃ B, ν = n₀c B
    · obtain ⟨B, rfl⟩ := hν
      have hB := nonempty_of_n₀c_ne_zero hν0
      rw [sm_img_n₀c', n₀c_eq_ncT A, n₀c_eq_ncT B, cardMul_ncT (emb_self A) (emb_self B),
        cardMul_goodL (good_T T A) (emb_self B) hB]
    · push Not at hν
      rw [cardMul_eq_empty_of_right _ hν, cardMul_eq_empty_of_right _ hν]

/-- ✱118·32. \(\vdash \colon\ldotp \nu \in \text{NC} . \mu \neq 0 . \supset : \exists ! (\mu \times _{c} \nu )_{\xi } . \equiv . \exists ! (\mu \times _{c} \text{ sm }_{\xi }ʻʻ\nu )_{\xi }\) -/
theorem pm118_32 {α β β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    ν ∈ NC β₂ ∧ μ ≠ zero → ((μ ×ᶜ ν : Set (Set T)).Nonempty ↔
      (μ ×ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)).Nonempty) := by
  rintro ⟨hν, hμ⟩
  rw [mul_sm_right hν hμ]

/-- ✱118·33. \[\begin{align}&\vdash :\mu ,\nu \in \text{NC}-\iota ʻ0.\supset .(\mu \times _{c}\nu )_{\xi }=(\text{ sm }_{\xi }ʻʻ\mu \times _{c}\text{ sm }_{\xi }ʻʻ\nu )_{\xi }\\ &[\text{Proof as in *118·23, using *118·31·311. *113·203·26}]\end{align}\] -/
theorem pm118_33 {α β β₁ β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NC β₁ \ ι zero ∧ ν ∈ NC β₂ \ ι zero → (μ ×ᶜ ν : Set (Set T)) =
      ((sm ʻʻ μ : Set (Set T)) ×ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)) := by
  rintro ⟨⟨hμ, hμ0⟩, ⟨hν, hν0⟩⟩
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [sm_img_empty, cardMul_empty_left, cardMul_empty_left]
  rcases NC_cases hν with rfl | ⟨B, rfl⟩
  · rw [sm_img_empty, cardMul_empty_right, cardMul_empty_right]
  have hA := nonempty_of_n₀c_ne_zero hμ0
  have hB := nonempty_of_n₀c_ne_zero hν0
  rw [sm_img_n₀c', sm_img_n₀c', n₀c_eq_ncT A, n₀c_eq_ncT B,
    cardMul_ncT (emb_self A) (emb_self B), cardMul_gen' (good_T T A) (good_T T B) hA hB]

/-- ✱118·34. \(\vdash :\nu \in \text{NC}.\mu \neq 0.\supset .(\mu \times _{c}\nu )_{\xi }=(\mu \times _{c}\text{ sm }_{\xi }ʻʻ\nu )_{\xi }\) -/
theorem pm118_34 {α β β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    ν ∈ NC β₂ ∧ μ ≠ zero →
      (μ ×ᶜ ν : Set (Set T)) = (μ ×ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)) :=
  fun ⟨hν, hμ⟩ => mul_sm_right hν hμ

/-- ✱118·341. \(\vdash :\mu \in \text{NC}.\nu \neq 0.\supset .(\mu \times _{c}\nu )_{\xi }=(\text{sm }_{\xi }ʻʻ\mu \times _{c}\nu )_{\xi } \quad[*118·34.*113·27]\) -/
theorem pm118_341 {α β β₁ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NC β₁ ∧ ν ≠ zero →
      (μ ×ᶜ ν : Set (Set T)) = ((sm ʻʻ μ : Set (Set T)) ×ᶜ ν : Set (Set T)) :=
  fun ⟨hμ, hν⟩ => mul_sm_left hμ hν

/-- ✱118·35. \[\begin{align}&\vdash :\varpi \neq 0.\supset .(\mu \times _{c}\nu \times _{c}\varpi )_{\xi }=\{(\mu \times _{c}\nu )_{\xi }\times _{c}\varpi \}_{\xi }\\ &[\text{Proof similar to *118·25, using *118·341·301.*113·203·23}]\end{align}\]

`μ ×_c ν ×_c ϖ` is `(μ ×_c ν) ×_c ϖ` (✱113·541), with its inner product in an adequate type `W`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
unsubscripted arithmetical component `μ ×_c ν` is adequate. -/
theorem pm118_35 {α β γ W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set γ)}
    (hW : AdeqMul W μ ν) : ϖ ≠ zero →
    ((μ ×ᶜ ν : Set (Set W)) ×ᶜ ϖ : Set (Set T)) = ((μ ×ᶜ ν : Set (Set T)) ×ᶜ ϖ : Set (Set T)) := by
  intro hϖ0
  by_cases hμ : ∃ A, μ = n₀c A
  · by_cases hν : ∃ B, ν = n₀c B
    · obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν
      by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨C, rfl⟩ := hϖ
        have hC := nonempty_of_n₀c_ne_zero hϖ0
        rw [cardMul_n₀c, cardMul_n₀c, n₀c_eq_ncT C, cardMul_ncT (adeqMul_emb hW A B) (emb_self C),
          cardMul_goodL (good_T T _) (emb_self C) hC]
      · push Not at hϖ
        simp only [cardMul_eq_empty_of_right _ hϖ]
    · push Not at hν
      simp only [cardMul_eq_empty_of_right _ hν, cardMul_empty_left]
  · push Not at hμ
    simp only [cardMul_eq_empty_of_left hμ, cardMul_empty_left]

/-- ✱118·351. \(\vdash :\mu \neq 0.\supset .(\mu \times _{c}\nu \times _{c}\varpi )_{\xi }=\{\mu \times _{c}(\nu \times _{c}\varpi )_{\xi }\}_{\xi } \quad[*118·35.*113·27]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
unsubscripted arithmetical component `μ ×_c ν` is adequate. -/
theorem pm118_351 {α β γ W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set γ)}
    (hW : AdeqMul W μ ν) : μ ≠ zero →
    ((μ ×ᶜ ν : Set (Set W)) ×ᶜ ϖ : Set (Set T)) = (μ ×ᶜ (ν ×ᶜ ϖ : Set (Set T)) : Set (Set T)) := by
  intro hμ0
  by_cases hμ : ∃ A, μ = n₀c A
  · by_cases hν : ∃ B, ν = n₀c B
    · obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν
      by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨C, rfl⟩ := hϖ
        have hA := nonempty_of_n₀c_ne_zero hμ0
        rw [cardMul_n₀c, cardMul_n₀c, n₀c_eq_ncT C, n₀c_eq_ncT A,
          cardMul_ncT (adeqMul_emb hW A B) (emb_self C),
          cardMul_goodR (emb_self A) (good_T T _) hA]
        exact ncT_congr (Equiv.prodAssoc _ _ _)
      · push Not at hϖ
        simp only [cardMul_eq_empty_of_right _ hϖ, cardMul_empty_right]
    · push Not at hν
      simp only [cardMul_eq_empty_of_right _ hν, cardMul_eq_empty_of_left hν, cardMul_empty_left,
        cardMul_empty_right]
  · push Not at hμ
    simp only [cardMul_eq_empty_of_left hμ, cardMul_empty_left]

/-- ✱118·352. \[\begin{align}&\vdash :\mu \neq 0.\varpi \neq 0.\supset .\{\mu \times _{c}(\nu \times _{c}\varpi )_{\xi }\}_{\xi }=\{(\mu \times _{c}\nu )_{\xi }\times _{c}\varpi \}_{\xi }\\ &[*118·35·351]\end{align}\] -/
theorem pm118_352 {α β γ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set γ)} :
    μ ≠ zero ∧ ϖ ≠ zero →
    (μ ×ᶜ (ν ×ᶜ ϖ : Set (Set T)) : Set (Set T)) = ((μ ×ᶜ ν : Set (Set T)) ×ᶜ ϖ : Set (Set T)) := by
  rintro ⟨hμ0, hϖ0⟩
  by_cases hμ : ∃ A, μ = n₀c A
  · by_cases hν : ∃ B, ν = n₀c B
    · obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν
      by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨C, rfl⟩ := hϖ
        have hA := nonempty_of_n₀c_ne_zero hμ0
        have hC := nonempty_of_n₀c_ne_zero hϖ0
        rw [cardMul_n₀c, cardMul_n₀c, n₀c_eq_ncT C, n₀c_eq_ncT A,
          cardMul_goodR (emb_self A) (good_T T _) hA, cardMul_goodL (good_T T _) (emb_self C) hC]
        exact ncT_congr (Equiv.prodAssoc _ _ _).symm
      · push Not at hϖ
        simp only [cardMul_eq_empty_of_right _ hϖ, cardMul_empty_right]
    · push Not at hν
      simp only [cardMul_eq_empty_of_right _ hν, cardMul_eq_empty_of_left hν, cardMul_empty_left,
        cardMul_empty_right]
  · push Not at hμ
    simp only [cardMul_eq_empty_of_left hμ, cardMul_empty_left]

/-- ✱118·4. \[\begin{align}&\vdash .(\mu ^\nu )_{\xi }=\hat{\eta} \{(\exists \alpha ,\beta ).\mu =\text{N}_{0}\text{c}ʻ\alpha .\nu =\text{N}_{0}\text{c}ʻ\beta .\eta \text{ sm }_{\xi }(\alpha \,\,\text{exp}\,\,\beta )\}\\ &[(*65·01·03).*116·2]\end{align}\] -/
theorem pm118_4 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ^ᶜ ν : Set (Set T)) =
      {η | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm η (clsExp A B)} :=
  rfl

/-- ✱118·401. \(\vdash :\exists !\mu ^\nu .\supset .\text{ sm }_{\xi }ʻʻ\mu ^\nu =(\mu ^\nu )_{\xi } \quad[\text{Proof as in *118·201}]\)

**Status.** proved (reading): convention IT (Prefatory Statement, IV): the logical and the
argumental occurrences of `μ^ν` share one type parameter `W`. -/
theorem pm118_401 {α β W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ^ᶜ ν : Set (Set W)).Nonempty →
      (sm ʻʻ (μ ^ᶜ ν : Set (Set W)) : Set (Set T)) = (μ ^ᶜ ν : Set (Set T)) := by
  intro h
  obtain ⟨A, B, ⟨rfl, rfl⟩, hW⟩ := cardExp_nonempty_iff.1 h
  rw [cardExp_n₀c, cardExp_n₀c, sm_img_ncT hW]

/-- ✱118·402. \(\vdash \colon\ldotp \mu ,\nu \in \text{N}_{0}\text{C}.\mu \neq 0.\mu \neq 1.\supset :\exists !(\mu ^\nu )_{\xi }.\supset .\exists !(\mu \times _{c}\nu )_{\xi }\)

`μ, ν ∈ N₀C` is `μ ∈ N₀C ∧ ν ∈ N₀C`, the first factor of a product of three. -/
theorem pm118_402 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    ((μ ∈ N₀C ∧ ν ∈ N₀C) ∧ μ ≠ zero) ∧ μ ≠ one →
      ((μ ^ᶜ ν : Set (Set T)).Nonempty → (μ ×ᶜ ν : Set (Set T)).Nonempty) := by
  rintro ⟨⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, h0⟩, h1⟩ h
  obtain ⟨a, b, hab⟩ := two_of_n₀c_ne h0 h1
  rw [cardExp_n₀c, ncT_nonempty_iff] at h
  rw [cardMul_n₀c, ncT_nonempty_iff]
  exact emb_prod_arrow hab h

/-- ✱118·41. \(\vdash :\exists !(\mu ^\nu )_{\xi }.\nu \neq 0.\supset .\exists !\text{ sm }_{\xi }ʻʻ\mu\) -/
theorem pm118_41 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ^ᶜ ν : Set (Set T)).Nonempty ∧ ν ≠ zero → (sm ʻʻ μ : Set (Set T)).Nonempty := by
  rintro ⟨h, hν⟩
  obtain ⟨A, B, ⟨rfl, rfl⟩, hT⟩ := cardExp_nonempty_iff.1 h
  rw [sm_img_n₀c', ncT_nonempty_iff]
  exact emb_arrow_const (nonempty_of_n₀c_ne_zero hν) hT

/-- ✱118·411. \(\vdash :\exists !(\mu ^\nu )_{\xi }.\mu \neq 0.\mu \neq 1.\supset .\exists !\text{ sm }_{\xi }ʻʻ\nu \quad[*118·402·311]\) -/
theorem pm118_411 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    ((μ ^ᶜ ν : Set (Set T)).Nonempty ∧ μ ≠ zero) ∧ μ ≠ one → (sm ʻʻ ν : Set (Set T)).Nonempty := by
  rintro ⟨⟨h, h0⟩, h1⟩
  obtain ⟨A, B, ⟨rfl, rfl⟩, hT⟩ := cardExp_nonempty_iff.1 h
  obtain ⟨a, b, hab⟩ := two_of_n₀c_ne h0 h1
  rw [sm_img_n₀c', ncT_nonempty_iff]
  exact emb_arrow_dom hab hT

private theorem exp_sm_right {α β β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (hν : ν ∈ NC β₂) (h0 : μ ≠ zero) (h1 : μ ≠ one) :
    (μ ^ᶜ ν : Set (Set T)) = (μ ^ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)) := by
  rcases NC_cases hν with rfl | ⟨B, rfl⟩
  · rw [sm_img_empty, cardExp_empty_right, cardExp_empty_right]
  · by_cases hμ : ∃ A, μ = n₀c A
    · obtain ⟨A, rfl⟩ := hμ
      obtain ⟨a, b, hab⟩ := two_of_n₀c_ne h0 h1
      rw [sm_img_n₀c', n₀c_eq_ncT A, n₀c_eq_ncT B, cardExp_ncT (emb_self A) (emb_self B),
        cardExp_goodExp (emb_self A) (good_T T B) hab]
    · push Not at hμ
      rw [cardExp_eq_empty_of_left hμ, cardExp_eq_empty_of_left hμ]

private theorem exp_sm_left {α β β₁ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (hμ : μ ∈ NC β₁) (hν0 : ν ≠ zero) :
    (μ ^ᶜ ν : Set (Set T)) = ((sm ʻʻ μ : Set (Set T)) ^ᶜ ν : Set (Set T)) := by
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [sm_img_empty, cardExp_empty_left, cardExp_empty_left]
  · by_cases hν : ∃ B, ν = n₀c B
    · obtain ⟨B, rfl⟩ := hν
      have hB := nonempty_of_n₀c_ne_zero hν0
      rw [sm_img_n₀c', n₀c_eq_ncT A, n₀c_eq_ncT B, cardExp_ncT (emb_self A) (emb_self B),
        cardExp_goodBase (good_T T A) (emb_self B) hB]
    · push Not at hν
      rw [cardExp_eq_empty_of_right _ hν, cardExp_eq_empty_of_right _ hν]

/-- ✱118·42. \[\begin{align}&\vdash \colon\ldotp \nu \in \text{NC}.\mu \neq 0.\mu \neq 1.\supset :\exists !(\mu ^\nu )_{\xi }.\equiv .\exists !(\mu ^{\text{ sm }_{\xi }ʻʻ\nu })_{\xi }\\ &[\text{Proof as in *118·32, using *116·203·26.*118·411}]\end{align}\] -/
theorem pm118_42 {α β β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (ν ∈ NC β₂ ∧ μ ≠ zero) ∧ μ ≠ one → ((μ ^ᶜ ν : Set (Set T)).Nonempty ↔
      (μ ^ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)).Nonempty) := by
  rintro ⟨⟨hν, h0⟩, h1⟩
  rw [exp_sm_right hν h0 h1]

/-- ✱118·421. \[\begin{align}&\vdash \colon\ldotp \mu \in \text{NC}.\nu \neq 0.\supset :\exists !(\mu ^\nu )_{\xi }.\equiv .\exists !\{(\text{ sm }_{\xi }ʻʻ\mu )^\nu\}_{\xi }\\ &[\text{Proof as in *118·32, using *116·203·26.*118·41}]\end{align}\] -/
theorem pm118_421 {α β β₁ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NC β₁ ∧ ν ≠ zero → ((μ ^ᶜ ν : Set (Set T)).Nonempty ↔
      ((sm ʻʻ μ : Set (Set T)) ^ᶜ ν : Set (Set T)).Nonempty) := by
  rintro ⟨hμ, hν⟩
  rw [exp_sm_left hμ hν]

/-- ✱118·43. \[\begin{align}&\vdash :\mu ,\nu \in \text{NC}-\iota ʻ0.\mu \neq 1.\supset .(\mu ^\nu )_{\xi }=\{(\text{ sm }_{\xi }ʻʻ\mu )^{\text{ sm }_{\xi }ʻʻ\nu }\}_{\xi }\\ &[\text{Proof as in *118·23, using *118·41·411.*116·203·26}]\end{align}\] -/
theorem pm118_43 {α β β₁ β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ∈ NC β₁ \ ι zero ∧ ν ∈ NC β₂ \ ι zero) ∧ μ ≠ one → (μ ^ᶜ ν : Set (Set T)) =
      ((sm ʻʻ μ : Set (Set T)) ^ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)) := by
  rintro ⟨⟨⟨hμ, hμ0⟩, ⟨hν, hν0⟩⟩, h1⟩
  rw [exp_sm_right hν hμ0 h1, exp_sm_left hμ]
  intro h
  rcases NC_cases hν with rfl | ⟨B, rfl⟩
  · rw [sm_img_empty, zero_eq] at h
    exact (Set.singleton_ne_empty _) h.symm
  · rw [sm_img_n₀c'] at h
    have : (∅ : Set T) ∈ ncT T ↥B := by rw [h, zero_eq]; exact Set.mem_singleton _
    obtain ⟨e⟩ := this
    exact hν0 (n₀c_eq_zero_iff.2 (Set.eq_empty_iff_forall_notMem.2 fun b hb =>
      (e.symm ⟨b, hb⟩).2))

/-- ✱118·44. \[\begin{align}&\vdash :\nu \in \text{NC}.\mu \neq 0.\mu \neq 1.\supset .(\mu ^\nu )_{\xi }=(\mu ^{\text{ sm }_{\xi }ʻʻ\nu })_{\xi }\\ &[\text{Proof as in *118·34, using *116·203·26.*118·411·42}]\end{align}\] -/
theorem pm118_44 {α β β₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (ν ∈ NC β₂ ∧ μ ≠ zero) ∧ μ ≠ one →
      (μ ^ᶜ ν : Set (Set T)) = (μ ^ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set T)) :=
  fun ⟨⟨hν, h0⟩, h1⟩ => exp_sm_right hν h0 h1

/-- ✱118·441. \[\begin{align}&\vdash :\mu \in \text{NC}.\nu \neq 0.\supset .(\mu ^\nu )_{\xi }=\{(\text{ sm }_{\xi }ʻʻ\mu )^\nu\}_{\xi }\\ &[\text{Proof as in *118·34, using *116·203·26.*118·41·421}]\end{align}\] -/
theorem pm118_441 {α β β₁ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NC β₁ ∧ ν ≠ zero →
      (μ ^ᶜ ν : Set (Set T)) = ((sm ʻʻ μ : Set (Set T)) ^ᶜ ν : Set (Set T)) :=
  fun ⟨hμ, hν⟩ => exp_sm_left hμ hν

/-- ✱118·45. \(\vdash :\mu \neq 0.\mu \neq 1.\supset .(\mu ^{\nu \times _{c}\varpi })_{\xi }=\{\mu ^{(\nu \times _{c}\varpi )_{\xi }}\}_{\xi }\)

The unsubscripted exponent `ν ×_c ϖ` on the left is an arithmetical component (IIT: adequate type
`W`).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
unsubscripted arithmetical component `ν ×_c ϖ` is adequate. -/
theorem pm118_45 {α β γ W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set γ)}
    (hW : AdeqMul W ν ϖ) : μ ≠ zero ∧ μ ≠ one →
    (μ ^ᶜ (ν ×ᶜ ϖ : Set (Set W)) : Set (Set T)) = (μ ^ᶜ (ν ×ᶜ ϖ : Set (Set T)) : Set (Set T)) := by
  rintro ⟨h0, h1⟩
  by_cases hμ : ∃ A, μ = n₀c A
  · obtain ⟨A, rfl⟩ := hμ
    obtain ⟨a, b, hab⟩ := two_of_n₀c_ne h0 h1
    by_cases hν : ∃ B, ν = n₀c B
    · by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨B, rfl⟩ := hν; obtain ⟨C, rfl⟩ := hϖ
        rw [cardMul_n₀c, cardMul_n₀c, n₀c_eq_ncT A, cardExp_ncT (emb_self A) (adeqMul_emb hW B C),
          cardExp_goodExp (emb_self A) (good_T T _) hab]
      · push Not at hϖ
        simp only [cardMul_eq_empty_of_right _ hϖ, cardExp_empty_right]
    · push Not at hν
      simp only [cardMul_eq_empty_of_left hν, cardExp_empty_right]
  · push Not at hμ
    simp only [cardExp_eq_empty_of_left hμ]

/-- ✱118·451. \(\vdash :\varpi \neq 0.\supset .(\mu ^{\nu \times _{c}\varpi })_{\xi } =[\{(\mu ^\nu )_{\xi }\}^\varpi ]_{\xi }\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
unsubscripted arithmetical component `ν ×_c ϖ` is adequate. -/
theorem pm118_451 {α β γ W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set γ)}
    (hW : AdeqMul W ν ϖ) : ϖ ≠ zero →
    (μ ^ᶜ (ν ×ᶜ ϖ : Set (Set W)) : Set (Set T)) = ((μ ^ᶜ ν : Set (Set T)) ^ᶜ ϖ : Set (Set T)) := by
  intro hϖ0
  by_cases hμ : ∃ A, μ = n₀c A
  · obtain ⟨A, rfl⟩ := hμ
    by_cases hν : ∃ B, ν = n₀c B
    · by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨B, rfl⟩ := hν; obtain ⟨C, rfl⟩ := hϖ
        have hC := nonempty_of_n₀c_ne_zero hϖ0
        rw [cardMul_n₀c, cardExp_n₀c, n₀c_eq_ncT A, n₀c_eq_ncT C,
          cardExp_ncT (emb_self A) (adeqMul_emb hW B C),
          cardExp_goodBase (good_T T _) (emb_self C) hC]
        exact ncT_congr ((Equiv.arrowCongr (Equiv.prodComm _ _) (Equiv.refl _)).trans
          (Equiv.curry _ _ _))
      · push Not at hϖ
        simp only [cardMul_eq_empty_of_right _ hϖ, cardExp_empty_right,
          cardExp_eq_empty_of_right _ hϖ]
    · push Not at hν
      simp only [cardMul_eq_empty_of_left hν, cardExp_empty_right, cardExp_empty_left,
        cardExp_eq_empty_of_right _ hν]
  · push Not at hμ
    simp only [cardExp_eq_empty_of_left hμ, cardExp_empty_left]

/-- ✱118·46. \[\begin{align}&\vdash :\mu \neq 0.\mu \neq 1.\supset .(\mu ^{\nu +_{c}\varpi })_{\xi }=\{\mu ^{(\nu +_{c}\varpi )}_{\xi}\}_{\xi }\\ &[\text{Proof as in *118·45, using *118·44·201.*116·203.*110·4·42}]\end{align}\]

(The e-text misplaces the subscript of the exponent: the Summary of ✱118 prints
`{μ^{(ν +_c ϖ)_ξ}}_ξ`, the analogue of ✱118·45.)

**Status.** proved (reading): transcription error (the subscript `ξ` belongs to the exponent
`ν +_c ϖ`, as in the Summary of ✱118); convention IIT (Prefatory Statement, IV): the actual type
`W` of the unsubscripted arithmetical component `ν +_c ϖ` is adequate. -/
theorem pm118_46 {α β γ W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set γ)}
    (hW : AdeqAdd W ν ϖ) : μ ≠ zero ∧ μ ≠ one →
    (μ ^ᶜ (ν +ᶜ ϖ : Set (Set W)) : Set (Set T)) = (μ ^ᶜ (ν +ᶜ ϖ : Set (Set T)) : Set (Set T)) := by
  rintro ⟨h0, h1⟩
  by_cases hμ : ∃ A, μ = n₀c A
  · obtain ⟨A, rfl⟩ := hμ
    obtain ⟨a, b, hab⟩ := two_of_n₀c_ne h0 h1
    by_cases hν : ∃ B, ν = n₀c B
    · by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨B, rfl⟩ := hν; obtain ⟨C, rfl⟩ := hϖ
        rw [cardAdd_n₀c, cardAdd_n₀c, n₀c_eq_ncT A, cardExp_ncT (emb_self A) (adeqAdd_emb hW B C),
          cardExp_goodExp (emb_self A) (good_T T _) hab]
      · push Not at hϖ
        simp only [cardAdd_eq_empty_of_right _ hϖ, cardExp_empty_right]
    · push Not at hν
      simp only [cardAdd_eq_empty_of_left hν, cardExp_empty_right]
  · push Not at hμ
    simp only [cardExp_eq_empty_of_left hμ]

/-- ✱118·461. \(\vdash .(\mu ^{\nu +_{c}\varpi })_{\xi }=\{(\mu ^\nu )_{\xi }\times _{c}(\mu ^\varpi )_{\xi }\}_{\xi }\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
unsubscripted arithmetical component `ν +_c ϖ` is adequate; PM assumes every type has a member
(Introduction, Ch. I): `[Nonempty T]` (for an empty `T`, `0^{0 +_c 1} = 0` exists but `0^0 = 1`
does not). -/
theorem pm118_461 {α β γ W T : Type*} [Nonempty T] {μ : Set (Set α)} {ν : Set (Set β)}
    {ϖ : Set (Set γ)} (hW : AdeqAdd W ν ϖ) :
    (μ ^ᶜ (ν +ᶜ ϖ : Set (Set W)) : Set (Set T)) =
      ((μ ^ᶜ ν : Set (Set T)) ×ᶜ (μ ^ᶜ ϖ : Set (Set T)) : Set (Set T)) := by
  by_cases hμ : ∃ A, μ = n₀c A
  · obtain ⟨A, rfl⟩ := hμ
    by_cases hν : ∃ B, ν = n₀c B
    · by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨B, rfl⟩ := hν; obtain ⟨C, rfl⟩ := hϖ
        rw [cardAdd_n₀c, cardExp_n₀c, cardExp_n₀c, n₀c_eq_ncT A,
          cardExp_ncT (emb_self A) (adeqAdd_emb hW B C),
          cardMul_goodLR (good_T T _) (good_T T _) fun h => ?_]
        · exact ncT_congr (Equiv.sumArrowEquivProdArrow _ _ _)
        · have h' : Nonempty ((↥B ⊕ ↥C → ↥A) ↪ T) :=
            let ⟨f⟩ := h; ⟨(Equiv.sumArrowEquivProdArrow _ _ _).toEmbedding.trans f⟩
          exact ⟨emb_arrow_sum_left h', emb_arrow_sum_right h'⟩
      · push Not at hϖ
        simp only [cardAdd_eq_empty_of_right _ hϖ, cardExp_empty_right,
          cardExp_eq_empty_of_right _ hϖ, cardMul_empty_right]
    · push Not at hν
      simp only [cardAdd_eq_empty_of_left hν, cardExp_empty_right,
        cardExp_eq_empty_of_right _ hν, cardMul_empty_left]
  · push Not at hμ
    simp only [cardExp_eq_empty_of_left hμ, cardMul_empty_left]

/-- ✱118·462. \(\vdash .(\mu ^{\nu +_{c}\varpi })_{\xi }=\{\mu ^\nu \times _{c}(\mu ^\varpi )_{\xi }\}_{\xi } \quad[\text{Proof as in *118·461, using *118·34}]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types `W` of
`ν +_c ϖ` and `W₂` of `μ^ν` (unsubscripted arithmetical components) are adequate; PM assumes every
type has a member (Introduction, Ch. I): `[Nonempty T]`, `[Nonempty W₂]` (otherwise
`0^{ν +_c 0} = 0` exists while `0^0 = 1` or `0^ν ×_c 0^0` does not). -/
theorem pm118_462 {α β γ W W₂ T : Type*} [Nonempty T] [Nonempty W₂] {μ : Set (Set α)}
    {ν : Set (Set β)} {ϖ : Set (Set γ)} (hW : AdeqAdd W ν ϖ) (hW₂ : AdeqExp W₂ μ ν) :
    (μ ^ᶜ (ν +ᶜ ϖ : Set (Set W)) : Set (Set T)) =
      ((μ ^ᶜ ν : Set (Set W₂)) ×ᶜ (μ ^ᶜ ϖ : Set (Set T)) : Set (Set T)) := by
  by_cases hμ : ∃ A, μ = n₀c A
  · obtain ⟨A, rfl⟩ := hμ
    by_cases hν : ∃ B, ν = n₀c B
    · by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨B, rfl⟩ := hν; obtain ⟨C, rfl⟩ := hϖ
        rw [cardAdd_n₀c, cardExp_n₀c, cardExp_n₀c, n₀c_eq_ncT A,
          cardExp_ncT (emb_self A) (adeqAdd_emb hW B C),
          cardMul_goodLR (Or.inl (adeqExp_emb hW₂ A B)) (good_T T _) fun h => ?_]
        · exact ncT_congr (Equiv.sumArrowEquivProdArrow _ _ _)
        · have h' : Nonempty ((↥B ⊕ ↥C → ↥A) ↪ T) :=
            let ⟨f⟩ := h; ⟨(Equiv.sumArrowEquivProdArrow _ _ _).toEmbedding.trans f⟩
          exact ⟨emb_arrow_sum_left h', emb_arrow_sum_right h'⟩
      · push Not at hϖ
        simp only [cardAdd_eq_empty_of_right _ hϖ, cardExp_empty_right,
          cardExp_eq_empty_of_right _ hϖ, cardMul_empty_right]
    · push Not at hν
      simp only [cardAdd_eq_empty_of_left hν, cardExp_empty_right,
        cardExp_eq_empty_of_right _ hν, cardMul_empty_left]
  · push Not at hμ
    simp only [cardExp_eq_empty_of_left hμ, cardMul_empty_left]

/-- ✱118·463. \(\vdash .(\mu ^{\nu +_{c}\varpi })_{\xi }=\{(\mu ^\nu )_{\xi }\times _{c}\mu ^\varpi\}_{\xi } \quad[\text{Proof as in *118·461, using *118·341}]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types `W` of
`ν +_c ϖ` and `W₂` of `μ^ϖ` (unsubscripted arithmetical components) are adequate; PM assumes every
type has a member (Introduction, Ch. I): `[Nonempty T]`, `[Nonempty W₂]`. -/
theorem pm118_463 {α β γ W W₂ T : Type*} [Nonempty T] [Nonempty W₂] {μ : Set (Set α)}
    {ν : Set (Set β)} {ϖ : Set (Set γ)} (hW : AdeqAdd W ν ϖ) (hW₂ : AdeqExp W₂ μ ϖ) :
    (μ ^ᶜ (ν +ᶜ ϖ : Set (Set W)) : Set (Set T)) =
      ((μ ^ᶜ ν : Set (Set T)) ×ᶜ (μ ^ᶜ ϖ : Set (Set W₂)) : Set (Set T)) := by
  by_cases hμ : ∃ A, μ = n₀c A
  · obtain ⟨A, rfl⟩ := hμ
    by_cases hν : ∃ B, ν = n₀c B
    · by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨B, rfl⟩ := hν; obtain ⟨C, rfl⟩ := hϖ
        rw [cardAdd_n₀c, cardExp_n₀c, cardExp_n₀c, n₀c_eq_ncT A,
          cardExp_ncT (emb_self A) (adeqAdd_emb hW B C),
          cardMul_goodLR (good_T T _) (Or.inl (adeqExp_emb hW₂ A C)) fun h => ?_]
        · exact ncT_congr (Equiv.sumArrowEquivProdArrow _ _ _)
        · have h' : Nonempty ((↥B ⊕ ↥C → ↥A) ↪ T) :=
            let ⟨f⟩ := h; ⟨(Equiv.sumArrowEquivProdArrow _ _ _).toEmbedding.trans f⟩
          exact ⟨emb_arrow_sum_left h', emb_arrow_sum_right h'⟩
      · push Not at hϖ
        simp only [cardAdd_eq_empty_of_right _ hϖ, cardExp_empty_right,
          cardExp_eq_empty_of_right _ hϖ, cardMul_empty_right]
    · push Not at hν
      simp only [cardAdd_eq_empty_of_left hν, cardExp_empty_right,
        cardExp_eq_empty_of_right _ hν, cardMul_empty_left]
  · push Not at hμ
    simp only [cardExp_eq_empty_of_left hμ, cardMul_empty_left]

/-- ✱118·47. \[\begin{align}&\vdash :\varpi \neq 0.\supset .\{(\mu _{c}\nu )^\varpi\}_{\xi }=[\{(\mu \times _{c}\nu )_{\xi }\}^\varpi ]_{\xi }\\ &[\text{Proof as in *118·45, using *118·441}]\end{align}\]

(The e-text drops the `×` of `μ ×_c ν` on the left.)

**Status.** proved (reading): transcription error (`μ _c ν` for `μ ×_c ν`); convention IIT
(Prefatory Statement, IV): the actual type `W` of the unsubscripted arithmetical component
`μ ×_c ν` is adequate. -/
theorem pm118_47 {α β γ W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set γ)}
    (hW : AdeqMul W μ ν) : ϖ ≠ zero →
    ((μ ×ᶜ ν : Set (Set W)) ^ᶜ ϖ : Set (Set T)) = ((μ ×ᶜ ν : Set (Set T)) ^ᶜ ϖ : Set (Set T)) := by
  intro hϖ0
  by_cases hμ : ∃ A, μ = n₀c A
  · by_cases hν : ∃ B, ν = n₀c B
    · obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν
      by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨C, rfl⟩ := hϖ
        have hC := nonempty_of_n₀c_ne_zero hϖ0
        rw [cardMul_n₀c, cardMul_n₀c, n₀c_eq_ncT C, cardExp_ncT (adeqMul_emb hW A B) (emb_self C),
          cardExp_goodBase (good_T T _) (emb_self C) hC]
      · push Not at hϖ
        simp only [cardExp_eq_empty_of_right _ hϖ]
    · push Not at hν
      simp only [cardMul_eq_empty_of_right _ hν, cardExp_empty_left]
  · push Not at hμ
    simp only [cardMul_eq_empty_of_left hμ, cardExp_empty_left]

/-- The non-uniform cases of ✱118·471–·473: some argument is not homogeneous, and both sides are
`Λ`. -/
private theorem mul_exp_aux {α β γ W W₁ W₂ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    {ϖ : Set (Set γ)} (h : ¬((μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ϖ ∈ N₀C)) :
    ((μ ×ᶜ ν : Set (Set W)) ^ᶜ ϖ : Set (Set T)) = ∅ ∧
      ((μ ^ᶜ ϖ : Set (Set W₁)) ×ᶜ (ν ^ᶜ ϖ : Set (Set W₂)) : Set (Set T)) = ∅ := by
  by_cases hμ : ∃ A, μ = n₀c A
  · by_cases hν : ∃ B, ν = n₀c B
    · have hϖ : ∀ C, ϖ ≠ n₀c C := fun C hC => h ⟨⟨hμ, hν⟩, ⟨C, hC⟩⟩
      simp only [cardExp_eq_empty_of_right _ hϖ, cardMul_empty_left, and_self]
    · push Not at hν
      simp only [cardMul_eq_empty_of_right _ hν, cardExp_empty_left,
        cardExp_eq_empty_of_left hν, cardMul_empty_right, and_self]
  · push Not at hμ
    simp only [cardMul_eq_empty_of_left hμ, cardExp_empty_left, cardExp_eq_empty_of_left hμ,
      cardMul_empty_left, and_self]

private theorem arrow_nonempty_of {C : Type*} {A : Type*} (h : Nonempty A ∨ IsEmpty C) :
    Nonempty (C → A) := by
  rcases h with ⟨⟨a⟩⟩ | h
  · exact ⟨fun _ => a⟩
  · exact ⟨fun c => isEmptyElim c⟩

private theorem isEmpty_of_n₀c_eq_zero {α : Type*} {C : Set α} (h : n₀c C = zero) : IsEmpty ↥C := by
  rw [n₀c_eq_zero_iff] at h; subst h; infer_instance

/-- ✱118·471. \[\begin{align}\vdash \colon\ldotp \mu \neq 0.\nu \neq 0.\lor.\varpi =0.\lor.{\sim}&(\mu ,\nu ,\varpi \in \text{N}_{0}\text{C}):\supset .\\ &\{(\mu \times _{c}\nu )^\varpi\}_{\xi }=\{(\mu ^\varpi )_{\xi }\times _{c}(\nu ^\varpi )_{\xi }\}_{\xi }\end{align}\]

The antecedent is a sum of three, bracketed to the left; `μ, ν, ϖ ∈ N₀C` is the product of three
memberships.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
unsubscripted arithmetical component `μ ×_c ν` is adequate. -/
theorem pm118_471 {α β γ W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set γ)}
    (hW : AdeqMul W μ ν) :
    ((μ ≠ zero ∧ ν ≠ zero) ∨ ϖ = zero) ∨ ¬((μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ϖ ∈ N₀C) →
      ((μ ×ᶜ ν : Set (Set W)) ^ᶜ ϖ : Set (Set T)) =
        ((μ ^ᶜ ϖ : Set (Set T)) ×ᶜ (ν ^ᶜ ϖ : Set (Set T)) : Set (Set T)) := by
  intro hyp
  by_cases hN : (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ϖ ∈ N₀C
  · obtain ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, ⟨C, rfl⟩⟩ := hN
    have hne : Nonempty (↥C → ↥A) ∧ Nonempty (↥C → ↥B) := by
      rcases hyp with (⟨h1, h2⟩ | h3) | h4
      · exact ⟨arrow_nonempty_of (Or.inl (nonempty_of_n₀c_ne_zero h1)),
          arrow_nonempty_of (Or.inl (nonempty_of_n₀c_ne_zero h2))⟩
      · exact ⟨arrow_nonempty_of (Or.inr (isEmpty_of_n₀c_eq_zero h3)),
          arrow_nonempty_of (Or.inr (isEmpty_of_n₀c_eq_zero h3))⟩
      · exact absurd ⟨⟨n₀c_mem_N₀C A, n₀c_mem_N₀C B⟩, n₀c_mem_N₀C C⟩ h4
    rw [cardMul_n₀c, cardExp_n₀c, cardExp_n₀c, n₀c_eq_ncT C,
      cardExp_ncT (adeqMul_emb hW A B) (emb_self C),
      cardMul_goodLR (good_T T _) (good_T T _) fun h =>
        ⟨emb_prod_left hne.2 h, emb_prod_right hne.1 h⟩]
    exact ncT_congr (Equiv.arrowProdEquivProdArrow _ _ _)
  · obtain ⟨h1, h2⟩ := mul_exp_aux (W := W) (W₁ := T) (W₂ := T) (T := T) hN
    rw [h1, h2]

/-- ✱118·472. \[\begin{align}&\vdash \colon\ldotp \mu \neq 0.\lor.\varpi =0.\lor.{\sim}(\mu ,\nu ,\varpi \in \text{N}_{0}\text{C}):\supset .\{(\mu \times _{c}\nu )^\varpi\}_{\xi }=\{\mu ^\varpi \times _{c}\nu ^\varpi )_{\xi }\}_{\xi }\\ &[\text{Proof as in *118·471, using *118·34}]\end{align}\]

(The e-text garbles the brackets of the right side; PM's proof "as in ✱118·471, using ✱118·34"
gives `{μ^ϖ ×_c (ν^ϖ)_ξ}_ξ`.)

**Status.** proved (reading): transcription error (the right side is `{μ^ϖ ×_c (ν^ϖ)_ξ}_ξ`);
convention IIT (Prefatory Statement, IV): the actual types `W` of `μ ×_c ν` and `W₂` of `μ^ϖ`
(unsubscripted arithmetical components) are adequate; PM assumes every type has a member
(Introduction, Ch. I): `[Nonempty W₂]` (for an empty `W₂`, `μ^0 = 1` does not exist there). -/
theorem pm118_472 {α β γ W W₂ T : Type*} [Nonempty W₂] {μ : Set (Set α)} {ν : Set (Set β)}
    {ϖ : Set (Set γ)} (hW : AdeqMul W μ ν) (hW₂ : AdeqExp W₂ μ ϖ) :
    (μ ≠ zero ∨ ϖ = zero) ∨ ¬((μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ϖ ∈ N₀C) →
      ((μ ×ᶜ ν : Set (Set W)) ^ᶜ ϖ : Set (Set T)) =
        ((μ ^ᶜ ϖ : Set (Set W₂)) ×ᶜ (ν ^ᶜ ϖ : Set (Set T)) : Set (Set T)) := by
  intro hyp
  by_cases hN : (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ϖ ∈ N₀C
  · obtain ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, ⟨C, rfl⟩⟩ := hN
    have hne : Nonempty (↥C → ↥A) := by
      rcases hyp with (h1 | h3) | h4
      · exact arrow_nonempty_of (Or.inl (nonempty_of_n₀c_ne_zero h1))
      · exact arrow_nonempty_of (Or.inr (isEmpty_of_n₀c_eq_zero h3))
      · exact absurd ⟨⟨n₀c_mem_N₀C A, n₀c_mem_N₀C B⟩, n₀c_mem_N₀C C⟩ h4
    rw [cardMul_n₀c, cardExp_n₀c, cardExp_n₀c, n₀c_eq_ncT C,
      cardExp_ncT (adeqMul_emb hW A B) (emb_self C),
      cardMul_goodR (adeqExp_emb hW₂ A C) (good_T T _) hne]
    exact ncT_congr (Equiv.arrowProdEquivProdArrow _ _ _)
  · obtain ⟨h1, h2⟩ := mul_exp_aux (W := W) (W₁ := W₂) (W₂ := T) (T := T) hN
    rw [h1, h2]

/-- ✱118·473. \[\begin{align}&\vdash \colon\ldotp \nu \neq 0.\lor.\varpi =0.\lor.{\sim}(\mu ,\nu ,\varpi \in \text{N}_{0}\text{C}):\supset .\{(\mu \times _{c}\nu )^\varpi\}_{\xi }=\{(\mu ^\varpi )_{\xi }\times _{c}\nu ^\varpi\}_{\xi }\\ &[\text{Proof as in *118·471, using *118·341}]\end{align}\]

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types `W` of
`μ ×_c ν` and `W₂` of `ν^ϖ` (unsubscripted arithmetical components) are adequate; PM assumes every
type has a member (Introduction, Ch. I): `[Nonempty W₂]`. -/
theorem pm118_473 {α β γ W W₂ T : Type*} [Nonempty W₂] {μ : Set (Set α)} {ν : Set (Set β)}
    {ϖ : Set (Set γ)} (hW : AdeqMul W μ ν) (hW₂ : AdeqExp W₂ ν ϖ) :
    (ν ≠ zero ∨ ϖ = zero) ∨ ¬((μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ϖ ∈ N₀C) →
      ((μ ×ᶜ ν : Set (Set W)) ^ᶜ ϖ : Set (Set T)) =
        ((μ ^ᶜ ϖ : Set (Set T)) ×ᶜ (ν ^ᶜ ϖ : Set (Set W₂)) : Set (Set T)) := by
  intro hyp
  by_cases hN : (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ ϖ ∈ N₀C
  · obtain ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, ⟨C, rfl⟩⟩ := hN
    have hne : Nonempty (↥C → ↥B) := by
      rcases hyp with (h1 | h3) | h4
      · exact arrow_nonempty_of (Or.inl (nonempty_of_n₀c_ne_zero h1))
      · exact arrow_nonempty_of (Or.inr (isEmpty_of_n₀c_eq_zero h3))
      · exact absurd ⟨⟨n₀c_mem_N₀C A, n₀c_mem_N₀C B⟩, n₀c_mem_N₀C C⟩ h4
    rw [cardMul_n₀c, cardExp_n₀c, cardExp_n₀c, n₀c_eq_ncT C,
      cardExp_ncT (adeqMul_emb hW A B) (emb_self C),
      cardMul_goodL (good_T T _) (adeqExp_emb hW₂ B C) hne]
    exact ncT_congr (Equiv.arrowProdEquivProdArrow _ _ _)
  · obtain ⟨h1, h2⟩ := mul_exp_aux (W := W) (W₁ := T) (W₂ := W₂) (T := T) hN
    rw [h1, h2]

/-!
## [✱119] Subtraction

*(Vol. 2, p. 201)*

> *Summary of* *119.
>
> The treatment of subtraction follows the same general lines as that of addition, and is simplified by the results in *110. A difficulty arises from the fact that subtraction (in any ordinary sense of the term) is not always possible; and also from the fact that the result, when possible, is not always a cardinal number.
>
> We put
>
> *119·01. \(\gamma -_{c}\nu =\hat{\xi} \{\text{Nc}ʻ\xi +_{c}\nu =\gamma .\exists !\text{Nc}ʻ\xi +_{c}\nu\} \quad\text{Df}\)
>
> Thus when subtraction (in the ordinary sense of the term) is not possible, \[ \gamma -_{c}\nu =\Lambda . \]
>
> The question of existential adjustment of types is dealt with by \(\text{IIT}\) of the prefatory statement combined with the following definitions:
>
> *119·02. \(\text{Nc}ʻ\alpha -_{c}\nu =\text{N}_{0}\text{c}ʻ\alpha -_{c}\nu \quad\text{Df}\)
>
> *119·03. \(\gamma -_{c}\text{Nc}ʻ\beta =\gamma -_{c}\text{N}_{0}\text{c}ʻ\beta \quad\text{Df}\)
>
> We then proceed to deduce the elementary properties derivable from these definitions.
>
> *119·11. \(\vdash :\exists !\gamma -_{c}\nu .\supset .\gamma ,\nu \in \text{N}_{0}\text{C}\)
>
> *119·12 \(\vdash :\xi \in \text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta .\equiv .\alpha \text{ sm }\xi +\beta\)
>
> …

**Lean reading.** `γ −_c ν` is `G -ᶜ ν` (✱119·01; `Defs/Part3`), whose actual type is fixed by
context or ascription; ✱119·02·03 are rules of translation (an argument `Nc'α` of `−_c` is
`N₀c'α`). Membership in a difference is `ξ + β sm α` (`mem_cardSub`). Arithmetical components
(`γ +_c ν` in `(γ +_c ν) −_c ν`, `Nc'α +_c Nc'β` in ✱119·41·42) are in adequate types (IIT). When
a difference has both a logical occurrence (`∈ N₀C`) and an arithmetical one (✱119·33·34·35·42·43),
the two are taken in one adequate type, as PM's proofs (by ✱118·01) require; with independent types
the propositions fail for infinite subtrahends. `sm_{δ,γ}` is `relTT sm d g` (✱65·1) and `SM(δ, γ)`
is `SM d g` (✱119·54). ✱119·32 needs a member in the type of the difference (in an empty type it
fails for infinite `ν`, `pm119_32_aux_empty`); `[Nonempty δ]` is added.

**Status.** proved (all propositions;
✱119·04·1·101·102·103·12·13·21·22·23·24·31·32·33·34·35·41·42·43·44·45·51 proved (reading);
✱119·01·02·03·54 definition)
-/

section Helpers6

open Classical

universe uA uB uC uT uX uY uZ uW

/-- Membership in `γ −_c ν`: `ξ + β sm α` where `γ = N₀c'α`, `ν = N₀c'β`. -/
private theorem mem_cardSub {γ : Type uC} {β : Type uB} {δ : Type uA} {G : Set (Set γ)}
    {ν : Set (Set β)} {ξ : Set δ} : ξ ∈ (G -ᶜ ν : Set (Set δ)) ↔
      ∃ (A : Set γ) (B : Set β), (G = n₀c A ∧ ν = n₀c B) ∧ Nonempty (↥ξ ⊕ ↥B ≃ ↥A) := by
  constructor
  · rintro ⟨hG, hne⟩
    obtain ⟨X, B, ⟨hX, rfl⟩, -⟩ := cardAdd_nonempty_iff.1 hne
    rw [cardAdd_n₀c] at hG hne
    obtain ⟨A, hA⟩ := hne
    refine ⟨A, B, ⟨?_, rfl⟩, ?_⟩
    · rw [← hG]; exact ncT_eq_n₀c_of_mem hA
    · obtain ⟨e⟩ := hA
      exact ⟨e.symm⟩
  · rintro ⟨A, B, ⟨rfl, rfl⟩, ⟨e⟩⟩
    show (n₀c ξ +ᶜ n₀c B : Set (Set γ)) = n₀c A ∧ (n₀c ξ +ᶜ n₀c B : Set (Set γ)).Nonempty
    rw [cardAdd_n₀c, n₀c_eq_ncT A]
    refine ⟨ncT_congr e, ⟨A, ⟨e.symm⟩⟩⟩

private theorem cardSub_nonempty_iff {γ : Type uC} {β : Type uB} {δ : Type uA} {G : Set (Set γ)}
    {ν : Set (Set β)} : (G -ᶜ ν : Set (Set δ)).Nonempty ↔
      ∃ (A : Set γ) (B : Set β) (ξ : Set δ), (G = n₀c A ∧ ν = n₀c B) ∧ Nonempty (↥ξ ⊕ ↥B ≃ ↥A) := by
  constructor
  · rintro ⟨ξ, h⟩
    obtain ⟨A, B, hAB, e⟩ := mem_cardSub.1 h
    exact ⟨A, B, ξ, hAB, e⟩
  · rintro ⟨A, B, ξ, hAB, e⟩
    exact ⟨ξ, mem_cardSub.2 ⟨A, B, hAB, e⟩⟩

/-- The remainder of an embedding: `α = δ + β` for some `δ ⊂ α` when `β` embeds in `α`. -/
private theorem exists_compl_of_emb {α : Type uA} {β : Type uB} {A : Set α} {B : Set β}
    (f : ↥B ↪ ↥A) : ∃ D : Set α, D ⊆ A ∧ Nonempty (↥D ⊕ ↥B ≃ ↥A) := by
  let R : Set α := Set.range (fun b => (f b : α))
  have hR : R ⊆ A := by rintro _ ⟨b, rfl⟩; exact (f b).2
  have eR : ↥B ≃ ↥R := Equiv.ofInjective _ (Subtype.val_injective.comp f.injective)
  refine ⟨A \ R, Set.sdiff_subset, ⟨?_⟩⟩
  exact ((Equiv.refl _).sumCongr eR).trans ((Equiv.sumComm _ _).trans (Equiv.Set.sumDiffSubset hR))

/-- A cardinal difference, when it exists, has members in any type into which the minuend fits. -/
private theorem cardSub_nonempty_of_emb {α : Type uA} {β : Type uB} {T : Type uT} {A : Set α}
    {B : Set β} (f : ↥B ↪ ↥A) (hA : Nonempty (↥A ↪ T)) :
    ∃ ξ : Set T, Nonempty (↥ξ ⊕ ↥B ≃ ↥A) := by
  obtain ⟨D, -, ⟨e⟩⟩ := exists_compl_of_emb f
  obtain ⟨g⟩ := hA
  obtain ⟨ξ, ⟨e'⟩⟩ := ncT_nonempty_iff.2
    (⟨(Function.Embedding.inl.trans e.toEmbedding).trans g⟩ : Nonempty (↥D ↪ T))
  exact ⟨ξ, ⟨(e'.sumCongr (Equiv.refl _)).trans e⟩⟩

private theorem emb_of_sum_equiv {X : Type uX} {Y : Type uY} {Z : Type uZ} (e : X ⊕ Y ≃ Z) :
    Nonempty (Y ↪ Z) := ⟨Function.Embedding.inr.trans e.toEmbedding⟩

private theorem n₀c_eq_of_mem {α : Type uA} {μ : Set (Set α)} {X : Set α} (hμ : μ ∈ N₀C)
    (hX : X ∈ μ) : μ = n₀c X := by
  obtain ⟨A, rfl⟩ := hμ
  rw [eq_n₀c_iff_equiv]
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (mem_n₀c.1 hX)
  exact ⟨e.symm⟩

private theorem mem_relTT_img {Δ : Type uA} {Γ : Type uB} {d : Set Δ} {g : Set Γ}
    {K : Set (Set Γ)} {ζ : Set Δ} : ζ ∈ relTT sm d g ʻʻ K ↔ ∃ η, η ∈ K ∧ sm ζ η := by
  rw [relTT_eq]; exact Iff.rfl

private theorem mem_dom_relTT {Δ : Type uA} {Γ : Type uB} {d : Set Δ} {g : Set Γ} {ζ : Set Δ} :
    ζ ∈ dom (relTT sm d g) ↔ ∃ η : Set Γ, sm ζ η := by
  rw [relTT_eq]; exact Iff.rfl

end Helpers6

/-- ✱119·01 (Df). \(\gamma -_{c}\nu =\hat{\xi} \{\text{Nc}ʻ\xi +_{c}\nu =\gamma .\exists !\text{Nc}ʻ\xi +_{c}\nu\} \quad\text{Df}\)

Cardinal subtraction `G -ᶜ ν` (`Defs/Part3`); `Nc'ξ +_c ν` is `N₀c'ξ +_c ν` (✱110·03), its
logical occurrence bound to the equational one (IT), in the type of `γ`. -/
theorem pm119_01 {γ β δ : Type*} {G : Set (Set γ)} {ν : Set (Set β)} :
    (G -ᶜ ν : Set (Set δ)) =
      {ξ | (n₀c ξ +ᶜ ν : Set (Set γ)) = G ∧ (n₀c ξ +ᶜ ν : Set (Set γ)).Nonempty} :=
  rfl

/-- ✱119·02 (Df). \(\text{Nc}ʻ\alpha -_{c}\nu =\text{N}_{0}\text{c}ʻ\alpha -_{c}\nu \quad\text{Df}\)

A rule of translation (normal adjustment, encoding decision 5): an argument `Nc'α` of `−_c` is
written `N₀c'α`. -/
theorem pm119_02 {α β δ : Type*} {A : Set α} {ν : Set (Set β)} :
    (n₀c A -ᶜ ν : Set (Set δ)) = n₀c A -ᶜ ν :=
  rfl

/-- ✱119·03 (Df). \(\gamma -_{c}\text{Nc}ʻ\beta =\gamma -_{c}\text{N}_{0}\text{c}ʻ\beta \quad\text{Df}\)

A rule of translation, as ✱119·02. -/
theorem pm119_03 {γ β δ : Type*} {G : Set (Set γ)} {B : Set β} :
    (G -ᶜ n₀c B : Set (Set δ)) = G -ᶜ n₀c B :=
  rfl

/-- ✱119·04. \(\vdash .\text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta =\text{N}_{0}\text{c}ʻ\alpha -_{c}\text{N}_{0}\text{c}ʻ\beta \quad[*119·02·03]\)

**Status.** proved (reading): by the Dfs ✱119·02·03 the arguments `Nc'α`, `Nc'β` of `−_c` are
read `N₀c'α`, `N₀c'β`, so the equation is the identity of the two readings. -/
theorem pm119_04 {α β δ : Type*} {A : Set α} {B : Set β} :
    (n₀c A -ᶜ n₀c B : Set (Set δ)) = n₀c A -ᶜ n₀c B :=
  rfl

/-- ✱119·1. \(\vdash :\xi \in \gamma -_{c}\nu .\equiv .\text{Nc}ʻ\xi +_{c}\nu =\gamma .\exists !\text{Nc}ʻ\xi +_{c}\nu \quad [(*119·01)]\)

**Status.** proved (reading): the argument `Nc'ξ` of `+_c` is `N₀c'ξ` (✱110·03, normal
adjustment). -/
theorem pm119_1 {γ β δ : Type*} {G : Set (Set γ)} {ν : Set (Set β)} {ξ : Set δ} :
    ξ ∈ (G -ᶜ ν : Set (Set δ)) ↔
      (n₀c ξ +ᶜ ν : Set (Set γ)) = G ∧ (n₀c ξ +ᶜ ν : Set (Set γ)).Nonempty :=
  Iff.rfl

/-- ✱119·101. \(\vdash :\xi \in \text{Nc}ʻ\alpha -_{c}\nu .\equiv .\text{Nc}ʻ\xi +_{c}\nu =\text{N}_{0}\text{c}ʻ\alpha \quad[(*119·02).*103·13]\)

**Status.** proved (reading): the arguments `Nc'α`, `Nc'ξ` are `N₀c'α`, `N₀c'ξ` (✱119·02,
✱110·03, normal adjustment). -/
theorem pm119_101 {α β δ : Type*} {A : Set α} {ν : Set (Set β)} {ξ : Set δ} :
    ξ ∈ (n₀c A -ᶜ ν : Set (Set δ)) ↔ (n₀c ξ +ᶜ ν : Set (Set α)) = n₀c A := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, h ▸ n₀c_nonempty A⟩

/-- ✱119·102. \[\begin{align}&\vdash :\xi \in \gamma -_{c}\text{Nc}ʻ\beta .\equiv .\text{Nc}ʻ\xi +_{c}\text{Nc}ʻ\beta =\gamma .\exists !\text{Nc}ʻ\xi +_{c}\text{Nc}ʻ\beta\\ &[(*119·03).*110·3]\end{align}\]

**Status.** proved (reading): the arguments `Nc'β`, `Nc'ξ` are `N₀c'β`, `N₀c'ξ` (✱119·03,
✱110·03·04, normal adjustment). -/
theorem pm119_102 {γ β δ : Type*} {G : Set (Set γ)} {B : Set β} {ξ : Set δ} :
    ξ ∈ (G -ᶜ n₀c B : Set (Set δ)) ↔
      (n₀c ξ +ᶜ n₀c B : Set (Set γ)) = G ∧ (n₀c ξ +ᶜ n₀c B : Set (Set γ)).Nonempty :=
  Iff.rfl

/-- ✱119·103. \[\begin{align}&\vdash :\xi \in \text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta .\equiv .\text{Nc}ʻ\xi +_{c}\text{Nc}ʻ\beta =\text{N}_{0}\text{c}ʻ\alpha\\ &[*119·04.*110·3.*103·13]\end{align}\]

**Status.** proved (reading): the arguments `Nc'α`, `Nc'β`, `Nc'ξ` of `−_c`, `+_c` are
`N₀c'α`, `N₀c'β`, `N₀c'ξ` (normal adjustment). -/
theorem pm119_103 {α β δ : Type*} {A : Set α} {B : Set β} {ξ : Set δ} :
    ξ ∈ (n₀c A -ᶜ n₀c B : Set (Set δ)) ↔ (n₀c ξ +ᶜ n₀c B : Set (Set α)) = n₀c A :=
  pm119_101

/-- ✱119·11. \(\vdash :\exists !\gamma -_{c}\nu .\supset .\gamma ,\nu \in \text{N}_{0}\text{C} \quad[*110·4·42.*103·34]\) -/
theorem pm119_11 {γ β δ : Type*} {G : Set (Set γ)} {ν : Set (Set β)} :
    (G -ᶜ ν : Set (Set δ)).Nonempty → G ∈ N₀C ∧ ν ∈ N₀C := by
  intro h
  obtain ⟨A, B, ξ, ⟨rfl, rfl⟩, -⟩ := cardSub_nonempty_iff.1 h
  exact ⟨n₀c_mem_N₀C A, n₀c_mem_N₀C B⟩

/-- ✱119·12. \(\vdash :\xi \in \text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta .\equiv .\alpha \text{ sm }\xi +\beta\)

**Status.** proved (reading): the arguments `Nc'α`, `Nc'β` of `−_c` are `N₀c'α`, `N₀c'β`
(✱119·02·03, normal adjustment). -/
theorem pm119_12 {α β δ : Type*} {A : Set α} {B : Set β} {ξ : Set δ} :
    ξ ∈ (n₀c A -ᶜ n₀c B : Set (Set δ)) ↔ sm A (ξ +ₐ B) := by
  rw [mem_cardSub, sm_iff_nonempty_equiv]
  constructor
  · rintro ⟨A', B', ⟨hA, hB⟩, ⟨e⟩⟩
    obtain ⟨eA⟩ := eq_n₀c_iff_equiv.1 hA
    obtain ⟨eB⟩ := eq_n₀c_iff_equiv.1 hB
    exact ⟨eA.trans (e.symm.trans (((Equiv.refl _).sumCongr eB.symm).trans
      (clsSumEquiv ξ B).symm))⟩
  · rintro ⟨e⟩
    exact ⟨A, B, ⟨rfl, rfl⟩, ⟨(clsSumEquiv ξ B).symm.trans e.symm⟩⟩

/-- ✱119·13. \(\vdash :\text{N}_{0}\text{c}ʻ\gamma \subset \text{Nc}ʻa-_{c}\text{Nc}ʻ\beta .\equiv .\alpha \text{ sm }(\gamma +\beta )\)

(The e-text prints `Nc'a` for `Nc'α`.) `N₀c'γ ⊂ …` puts the difference in the type of `γ`.

**Status.** proved (reading): transcription error (`a` for `α`); the arguments `Nc'α`, `Nc'β` of
`−_c` are `N₀c'α`, `N₀c'β` (normal adjustment). -/
theorem pm119_13 {α β δ : Type*} {A : Set α} {B : Set β} {G : Set δ} :
    n₀c G ⊆ (n₀c A -ᶜ n₀c B : Set (Set δ)) ↔ sm A (G +ₐ B) := by
  constructor
  · intro h; exact pm119_12.1 (h (self_mem_n₀c G))
  · intro h ξ hξ
    exact pm119_12.2 (sm_trans h (sm_clsSum (sm_symm (mem_n₀c.1 hξ)) (sm_refl B)))

/-- ✱119·14. \(\vdash :\xi \in \gamma -_{c}\nu .\supset .\text{N}_{0}\text{c}ʻ\xi \subset \gamma -_{c}\nu \quad[*119·1.*100·31·321]\) -/
theorem pm119_14 {γ β δ : Type*} {G : Set (Set γ)} {ν : Set (Set β)} {ξ : Set δ} :
    ξ ∈ (G -ᶜ ν : Set (Set δ)) → n₀c ξ ⊆ (G -ᶜ ν : Set (Set δ)) := by
  intro h η hη
  obtain ⟨A, B, hAB, ⟨e⟩⟩ := mem_cardSub.1 h
  obtain ⟨e'⟩ := sm_iff_nonempty_equiv.1 (mem_n₀c.1 hη)
  exact mem_cardSub.2 ⟨A, B, hAB, ⟨(e'.sumCongr (Equiv.refl _)).trans e⟩⟩

/-- ✱119·21. \(\vdash :\beta \subset \alpha .\supset .\exists !(\text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta )_{\alpha }\)

`(…)_α` is the difference in the type of `α` (✱65·01).

**Status.** proved (reading): the arguments `Nc'α`, `Nc'β` of `−_c` are `N₀c'α`, `N₀c'β`
(normal adjustment). -/
theorem pm119_21 {α : Type*} {A B : Set α} :
    B ⊆ A → (n₀c A -ᶜ n₀c B : Set (Set α)).Nonempty := by
  intro h
  obtain ⟨D, -, e⟩ := exists_compl_of_emb (⟨Set.inclusion h, Set.inclusion_injective h⟩ : ↥B ↪ ↥A)
  exact ⟨D, mem_cardSub.2 ⟨A, B, ⟨rfl, rfl⟩, e⟩⟩

/-- ✱119·22. \(\vdash :\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta .\supset .\exists !(\text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta )_{\alpha }\)

**Status.** proved (reading): the occurrences of `Nc'α`, `Nc'β` as sides of `≥` and arguments of
`−_c` are `N₀c'α`, `N₀c'β` (normal adjustment). -/
theorem pm119_22 {α β : Type*} {A : Set α} {B : Set β} :
    n₀c A ≥ᶜ n₀c B → (n₀c A -ᶜ n₀c B : Set (Set α)).Nonempty := by
  intro h
  obtain ⟨f⟩ := cardGe_n₀c.1 h
  obtain ⟨D, -, e⟩ := exists_compl_of_emb f
  exact ⟨D, mem_cardSub.2 ⟨A, B, ⟨rfl, rfl⟩, e⟩⟩

/-- ✱119·23. \(\vdash :\exists !(\text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta ).\supset .(\exists \delta ).\delta \text{ sm }\beta .\delta \subset \alpha\)

**Status.** proved (reading): the arguments `Nc'α`, `Nc'β` of `−_c` are `N₀c'α`, `N₀c'β`
(normal adjustment). -/
theorem pm119_23 {α β δ : Type*} {A : Set α} {B : Set β} :
    (n₀c A -ᶜ n₀c B : Set (Set δ)).Nonempty → ∃ D : Set α, sm D B ∧ D ⊆ A := by
  intro h
  obtain ⟨A', B', ξ, ⟨hA, hB⟩, ⟨e⟩⟩ := cardSub_nonempty_iff.1 h
  obtain ⟨eA⟩ := eq_n₀c_iff_equiv.1 hA
  obtain ⟨eB⟩ := eq_n₀c_iff_equiv.1 hB
  obtain ⟨f⟩ := emb_of_sum_equiv (e.trans eA.symm)
  let g : ↥B ↪ ↥A := eB.toEmbedding.trans f
  refine ⟨Set.range (fun b => (g b : α)), ?_, ?_⟩
  · exact sm_iff_nonempty_equiv.2
      ⟨(Equiv.ofInjective _ (Subtype.val_injective.comp g.injective)).symm⟩
  · rintro _ ⟨b, rfl⟩; exact (g b).2

/-- ✱119·24. \(\vdash :\exists !(\text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta ).\supset .\text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta \quad[*119·23.*117·221]\)

**Status.** proved (reading): the arithmetical occurrences of `Nc'α`, `Nc'β` are `N₀c'α`,
`N₀c'β` (normal adjustment). -/
theorem pm119_24 {α β δ : Type*} {A : Set α} {B : Set β} :
    (n₀c A -ᶜ n₀c B : Set (Set δ)).Nonempty → n₀c A ≥ᶜ n₀c B := by
  intro h
  obtain ⟨D, hD, hDA⟩ := pm119_23 h
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hD
  exact cardGe_n₀c.2 ⟨e.symm.toEmbedding.trans ⟨Set.inclusion hDA, Set.inclusion_injective hDA⟩⟩

private theorem mem_cardSub_of_eq {γ β δ Z : Type*} {G : Set (Set γ)} (hG : G = ncT γ Z)
    (hZ : Nonempty (Z ↪ γ)) {B : Set β} {ξ : Set δ} :
    ξ ∈ (G -ᶜ n₀c B : Set (Set δ)) ↔ Nonempty (↥ξ ⊕ ↥B ≃ Z) := by
  rw [mem_cardSub]
  constructor
  · rintro ⟨A', B', ⟨hA', hB'⟩, ⟨e⟩⟩
    have hA'Z : A' ∈ ncT γ Z := by rw [← hG, hA']; exact self_mem_n₀c A'
    obtain ⟨eA⟩ := hA'Z
    obtain ⟨eB⟩ := eq_n₀c_iff_equiv.1 hB'
    exact ⟨((Equiv.refl _).sumCongr eB).trans (e.trans eA)⟩
  · rintro ⟨e⟩
    obtain ⟨Y, hY⟩ := ncT_nonempty_iff.2 hZ
    obtain ⟨eY⟩ := id hY
    exact ⟨Y, B, ⟨hG ▸ ncT_eq_n₀c_of_mem hY, rfl⟩, ⟨e.trans eY.symm⟩⟩

private theorem mem_cardSub_n₀c {α β δ : Type*} {A : Set α} {ν : Set (Set β)} {ξ : Set δ} :
    ξ ∈ (n₀c A -ᶜ ν : Set (Set δ)) ↔ ∃ B : Set β, ν = n₀c B ∧ Nonempty (↥ξ ⊕ ↥B ≃ ↥A) := by
  rw [mem_cardSub]
  constructor
  · rintro ⟨A', B, ⟨hA, hB⟩, ⟨e⟩⟩
    obtain ⟨eA⟩ := eq_n₀c_iff_equiv.1 hA
    exact ⟨B, hB, ⟨e.trans eA.symm⟩⟩
  · rintro ⟨B, hB, e⟩
    exact ⟨A, B, ⟨rfl, hB⟩, e⟩

private theorem cardSub_empty_right {γ β δ : Type*} (G : Set (Set γ)) :
    (G -ᶜ (∅ : Set (Set β)) : Set (Set δ)) = ∅ := by
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨A, B, ⟨-, hB⟩, -⟩ := mem_cardSub.1 h
  exact n₀c_ne_empty B hB.symm

/-- ✱119·25. \(\vdash :\gamma \geq \nu .\supset .\exists !(\gamma -_{c}\nu )\cap t_{0}ʻ\gamma\)

`t₀'γ` is `typ₀ G`: it puts the difference in the type of the members of `γ`. -/
theorem pm119_25 {γ β : Type*} {G : Set (Set γ)} {ν : Set (Set β)} :
    G ≥ᶜ ν → ((G -ᶜ ν : Set (Set γ)) ∩ typ₀ G).Nonempty := by
  intro h
  obtain ⟨A, B, ⟨rfl, rfl⟩, ⟨f⟩⟩ := cardGe_iff.1 h
  obtain ⟨D, -, e⟩ := exists_compl_of_emb f
  exact ⟨D, mem_cardSub.2 ⟨A, B, ⟨rfl, rfl⟩, e⟩, by rw [typ₀_eq_univ]; trivial⟩

/-- ✱119·26. \(\vdash :\exists !\gamma -_{c}\nu .\supset .\gamma \geq \nu\) -/
theorem pm119_26 {γ β δ : Type*} {G : Set (Set γ)} {ν : Set (Set β)} :
    (G -ᶜ ν : Set (Set δ)).Nonempty → G ≥ᶜ ν := by
  intro h
  obtain ⟨A, B, ξ, ⟨rfl, rfl⟩, ⟨e⟩⟩ := cardSub_nonempty_iff.1 h
  exact cardGe_iff.2 ⟨A, B, ⟨rfl, rfl⟩, emb_of_sum_equiv e⟩

/-- ✱119·27. \(\vdash :\gamma \geq \nu .\equiv .\exists !(\gamma -_{c}\nu )\cap t_{0}ʻ\gamma \quad[*119·25·26]\) -/
theorem pm119_27 {γ β : Type*} {G : Set (Set γ)} {ν : Set (Set β)} :
    G ≥ᶜ ν ↔ ((G -ᶜ ν : Set (Set γ)) ∩ typ₀ G).Nonempty :=
  ⟨pm119_25, fun ⟨ξ, h, _⟩ => pm119_26 ⟨ξ, h⟩⟩

/-- ✱119·31. \(\vdash :\gamma ,\nu \in \text{N}_{0}\text{C}.\supset .\text{ sm }ʻʻ\gamma \subset (\gamma +_{c}\nu )-_{c}\nu\)

`γ +_c ν` is an arithmetical component (an argument of `−_c`): IIT takes it in an adequate type
`W` (PM's proof cites IIT). `sm''γ` and the difference are in one type `δ` (`⊂`).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
arithmetical component `γ +_c ν` is adequate. -/
theorem pm119_31 {γ β W δ : Type*} {G : Set (Set γ)} {ν : Set (Set β)} (hW : AdeqAdd W G ν) :
    G ∈ N₀C ∧ ν ∈ N₀C →
      (sm ʻʻ G : Set (Set δ)) ⊆ ((G +ᶜ ν : Set (Set W)) -ᶜ ν : Set (Set δ)) := by
  rintro ⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩ ξ hξ
  rw [sm_img_n₀c'] at hξ
  obtain ⟨e⟩ := hξ
  rw [mem_cardSub_of_eq (cardAdd_n₀c A B) (adeqAdd_emb hW A B)]
  exact ⟨e.sumCongr (Equiv.refl _)⟩

section Helpers6b

open Classical

universe uA uB uX uY u

/-- Absorption: an infinite class absorbs a summand that embeds in it. -/
private theorem sum_absorb_core {Y B : Type u} [Infinite B] (f : Y ↪ B) : Nonempty (Y ⊕ B ≃ B) := by
  apply Cardinal.eq.1
  rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.add_eq_right (Cardinal.infinite_iff.1 ‹_›) (Cardinal.mk_le_of_injective f.injective)

private theorem sum_absorb {Y : Type uY} {B : Type uB} [Infinite B] (f : Y ↪ B) :
    Nonempty (Y ⊕ B ≃ B) := by
  obtain ⟨e⟩ := sum_absorb_core.{max uY uB}
    ((Equiv.ulift.{uB} (α := Y)).toEmbedding.trans (f.trans Equiv.ulift.symm.toEmbedding))
  exact ⟨(Equiv.ulift.symm.sumCongr Equiv.ulift.symm).trans (e.trans Equiv.ulift)⟩

/-- Cancellation of a summand: `ξ + β sm α + β` gives `ξ sm α`, unless `β` is infinite and
both `ξ` and `α` embed in it. -/
private theorem sum_cancel_or_core {X A B : Type u} (e : X ⊕ B ≃ A ⊕ B) :
    Nonempty (X ≃ A) ∨ (Infinite B ∧ Nonempty (A ↪ B) ∧ Nonempty (X ↪ B)) := by
  have h : Cardinal.mk X + Cardinal.mk B = Cardinal.mk A + Cardinal.mk B := by
    have := Cardinal.eq.2 ⟨e⟩
    simpa [Cardinal.mk_sum] using this
  rcases lt_or_ge (Cardinal.mk B) Cardinal.aleph0 with hB | hB
  · exact Or.inl (Cardinal.eq.1 (Cardinal.eq_of_add_eq_add_right h hB))
  · by_cases hXA : Nonempty (X ≃ A)
    · exact Or.inl hXA
    right
    have hne : Cardinal.mk X ≠ Cardinal.mk A := fun h' => hXA (Cardinal.eq.1 h')
    rw [Cardinal.add_eq_max' hB, Cardinal.add_eq_max' hB] at h
    have hA : Cardinal.mk A ≤ Cardinal.mk B := by
      by_contra hlt
      push Not at hlt
      rw [max_eq_left hlt.le] at h
      rcases le_total (Cardinal.mk X) (Cardinal.mk B) with h1 | h1
      · rw [max_eq_right h1] at h; exact absurd h hlt.ne
      · rw [max_eq_left h1] at h; exact hne h
    have hX : Cardinal.mk X ≤ Cardinal.mk B := by
      by_contra hlt
      push Not at hlt
      rw [max_eq_left hlt.le, max_eq_right hA] at h
      exact absurd h hlt.ne'
    exact ⟨Cardinal.infinite_iff.2 hB, (Cardinal.le_def _ _).1 hA, (Cardinal.le_def _ _).1 hX⟩

private theorem sum_cancel_or {X : Type uX} {A : Type uA} {B : Type uB} (e : X ⊕ B ≃ A ⊕ B) :
    Nonempty (X ≃ A) ∨ (Infinite B ∧ Nonempty (A ↪ B) ∧ Nonempty (X ↪ B)) := by
  have e' : ULift.{max uA uB} X ⊕ ULift.{max uX uA} B ≃ ULift.{max uX uB} A ⊕ ULift.{max uX uA} B :=
    (Equiv.ulift.sumCongr Equiv.ulift).trans (e.trans (Equiv.ulift.sumCongr Equiv.ulift).symm)
  rcases sum_cancel_or_core e' with ⟨⟨f⟩⟩ | ⟨hB, ⟨f⟩, ⟨g⟩⟩
  · exact Or.inl ⟨Equiv.ulift.symm.trans (f.trans Equiv.ulift)⟩
  · refine Or.inr ⟨?_, ⟨Equiv.ulift.symm.toEmbedding.trans (f.trans Equiv.ulift.toEmbedding)⟩,
      ⟨Equiv.ulift.symm.toEmbedding.trans (g.trans Equiv.ulift.toEmbedding)⟩⟩
    exact Infinite.of_injective (β := ULift.{max uX uA} B) _ Equiv.ulift.injective

end Helpers6b

/-- ✱119·32. \[\begin{align}&\vdash :(\gamma +_{c}\nu )-_{c}\nu \in \text{N}_{0}\text{C}.\supset .\text{ sm }ʻʻ\gamma =(\gamma +_{c}\nu )-_{c}\nu\\ &[*119·11·31.*103·22.*100·52·42]\end{align}\]
u )-_{c}
u \in 	ext{N}_{0}	ext{C}.\supset .	ext{ sm }ʻʻ\gamma =(\gamma +_{c}
u )-_{c}
u\ &[*119·11·31.*103·22.*100·52·42]\end{align}\]

The difference `(γ +_c ν) −_c ν` and `sm''γ` are in one type `δ`. In an empty type `δ` the
proposition fails for infinite `ν` (`pm119_32_aux_empty`: `γ = ν = N₀c'ℕ`; the null class alone
is a `ξ` with `ξ + ν sm γ + ν`, so the difference is `0 ∈ N₀C`, while `sm''γ = Λ`). In a type with
a member it holds as printed: if `ν` is infinite and `γ ≤ ν`, the difference contains both `Λ` and
a unit class, so it is not in `N₀C`; otherwise cancellation gives `ξ sm γ`.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty δ]` for the type of the difference (`pm119_32_aux_empty`); convention IIT (Prefatory
Statement, IV): the actual type `W` of the arithmetical component `γ +_c ν` is adequate. -/
theorem pm119_32 {γ β W δ : Type*} [Nonempty δ] {G : Set (Set γ)} {ν : Set (Set β)}
    (hW : AdeqAdd W G ν) :
    ((G +ᶜ ν : Set (Set W)) -ᶜ ν : Set (Set δ)) ∈ N₀C →
      (sm ʻʻ G : Set (Set δ)) = ((G +ᶜ ν : Set (Set W)) -ᶜ ν : Set (Set δ)) := by
  intro hN
  have hne : ((G +ᶜ ν : Set (Set W)) -ᶜ ν : Set (Set δ)).Nonempty := by
    obtain ⟨X, hX⟩ := hN; rw [hX]; exact n₀c_nonempty X
  obtain ⟨h1, h2⟩ := pm119_11 hne
  obtain ⟨Y, hY⟩ := h1
  have hGN : G ∈ N₀C := by
    have : (G +ᶜ ν : Set (Set W)).Nonempty := by rw [hY]; exact n₀c_nonempty Y
    obtain ⟨A, B, ⟨rfl, -⟩, -⟩ := cardAdd_nonempty_iff.1 this
    exact n₀c_mem_N₀C A
  obtain ⟨A, rfl⟩ := hGN
  obtain ⟨B, rfl⟩ := h2
  have hmem : ∀ ξ : Set δ, ξ ∈ ((n₀c A +ᶜ n₀c B : Set (Set W)) -ᶜ n₀c B : Set (Set δ)) ↔
      Nonempty (↥ξ ⊕ ↥B ≃ ↥A ⊕ ↥B) := fun ξ =>
    mem_cardSub_of_eq (cardAdd_n₀c A B) (adeqAdd_emb hW A B)
  obtain ⟨X, hX⟩ := hN
  have hXm : X ∈ ((n₀c A +ᶜ n₀c B : Set (Set W)) -ᶜ n₀c B : Set (Set δ)) :=
    hX ▸ self_mem_n₀c X
  obtain ⟨e⟩ := (hmem X).1 hXm
  have key : Nonempty (↥X ≃ ↥A) := by
    rcases sum_cancel_or e with h | ⟨hB, ⟨fA⟩, -⟩
    · exact h
    · exfalso
      obtain ⟨d⟩ := ‹Nonempty δ›
      have := hB
      obtain ⟨b⟩ := hB.nonempty
      obtain ⟨eAB⟩ := sum_absorb fA
      obtain ⟨e0⟩ := sum_absorb (Y := ↥(∅ : Set δ)) (B := ↥B) ⟨fun z => z.2.elim, fun z => z.2.elim⟩
      obtain ⟨e1⟩ := sum_absorb (Y := ↥({d} : Set δ)) (B := ↥B)
        ⟨fun _ => b, fun _ _ _ => Subsingleton.elim _ _⟩
      have h0 := (hmem ∅).2 ⟨e0.trans eAB.symm⟩
      have h1 := (hmem {d}).2 ⟨e1.trans eAB.symm⟩
      rw [hX] at h0 h1
      obtain ⟨g0⟩ := sm_iff_nonempty_equiv.1 (mem_n₀c.1 h0)
      obtain ⟨g1⟩ := sm_iff_nonempty_equiv.1 (mem_n₀c.1 h1)
      exact (g0.symm (g1 ⟨d, rfl⟩)).2
  rw [hX, sm_img_n₀c']
  exact ncT_eq_n₀c_of_mem key

/-- `[Nonempty δ]` cannot be dropped from ✱119·32: `γ = ν = N₀c'ℕ`, `W = ℕ` (adequate for
`γ +_c ν`), and an empty type `δ`, in which `(γ +_c ν) −_c ν = 0` while `sm''γ = Λ`. -/
theorem pm119_32_aux_empty :
    ¬ ∀ {γ β W δ : Type} {G : Set (Set γ)} {ν : Set (Set β)}, AdeqAdd W G ν →
      ((G +ᶜ ν : Set (Set W)) -ᶜ ν : Set (Set δ)) ∈ N₀C →
        (sm ʻʻ G : Set (Set δ)) = ((G +ᶜ ν : Set (Set W)) -ᶜ ν : Set (Set δ)) := by
  intro h
  have hW : AdeqAdd ℕ (n₀c (Set.univ : Set ℕ)) (n₀c (Set.univ : Set ℕ)) :=
    adeqAdd_iff.2 ⟨Equiv.natSumNatEquivNat, Equiv.natSumNatEquivNat.injective⟩
  have eNN : (↥(Set.univ : Set ℕ) ⊕ ↥(Set.univ : Set ℕ)) ≃ ↥(Set.univ : Set ℕ) :=
    ((Equiv.Set.univ ℕ).sumCongr (Equiv.Set.univ ℕ)).trans
      (Equiv.natSumNatEquivNat.trans (Equiv.Set.univ ℕ).symm)
  have hmem : (∅ : Set Empty) ∈ ((n₀c (Set.univ : Set ℕ) +ᶜ n₀c (Set.univ : Set ℕ) :
      Set (Set ℕ)) -ᶜ n₀c (Set.univ : Set ℕ) : Set (Set Empty)) := by
    rw [mem_cardSub_of_eq (cardAdd_n₀c _ _) (adeqAdd_emb hW _ _)]
    exact ⟨(Equiv.emptySum _ _).trans eNN.symm⟩
  have hN : ((n₀c (Set.univ : Set ℕ) +ᶜ n₀c (Set.univ : Set ℕ) : Set (Set ℕ)) -ᶜ
      n₀c (Set.univ : Set ℕ) : Set (Set Empty)) ∈ N₀C := by
    refine ⟨∅, Set.ext fun ξ => ?_⟩
    rw [Set.eq_empty_of_isEmpty ξ]
    exact ⟨fun _ => self_mem_n₀c _, fun _ => hmem⟩
  have e := h hW hN
  rw [← e, sm_img_n₀c'] at hmem
  obtain ⟨f⟩ := hmem
  exact isEmptyElim (f.symm ⟨0, trivial⟩)

/-- ✱119·33. \(\vdash :\text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta \in \text{N}_{0}\text{C}.\supset .(\text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta )+_{c}\text{Nc}ʻ\beta =\text{Nc}ʻ\alpha\)

`Nc'α −_c Nc'β` has a logical occurrence (`∈ N₀C`) and an arithmetical one (an argument of
`+_c`). PM's proof passes from the one to the other by ✱118·01, i.e. takes them in one type `W`;
we do so (with independent types the proposition fails: `Nc'ℕ −_c Nc'ℕ` is `0` in an empty type,
while in `ℕ` it contains every class of `ℕ` and is not in `N₀C`, so that its sum with `Nc'ℕ` is
`Λ`). The adequacy of `W` that IIT would add is not needed. The equation is in a type `E`.

**Status.** proved (reading): the logical and the arithmetical occurrences of `Nc'α −_c Nc'β` are
in one type `W`, as PM's proof (by ✱118·01) requires (convention IIT, Prefatory Statement, IV;
its adequacy hypothesis is not needed); the arguments `Nc'α`, `Nc'β` are `N₀c'α`, `N₀c'β` (normal
adjustment). -/
theorem pm119_33 {α β W E : Type*} {A : Set α} {B : Set β} :
    (n₀c A -ᶜ n₀c B : Set (Set W)) ∈ N₀C →
      ((n₀c A -ᶜ n₀c B : Set (Set W)) +ᶜ n₀c B : Set (Set E)) = nc E A := by
  rintro ⟨X, hX⟩
  have hXm : X ∈ (n₀c A -ᶜ n₀c B : Set (Set W)) := hX ▸ self_mem_n₀c X
  obtain ⟨B', hB, ⟨e⟩⟩ := mem_cardSub_n₀c.1 hXm
  obtain ⟨eB⟩ := eq_n₀c_iff_equiv.1 hB
  rw [hX, cardAdd_n₀c, nc_eq_ncT]
  exact ncT_congr (((Equiv.refl _).sumCongr eB).trans e)

/-- ✱119·34. \[\begin{align}&\vdash :\gamma -_{c}\nu \in \text{N}_{0}\text{C}.\supset .(\gamma -_{c}\nu )+_{c}\nu =\text{ sm }ʻʻ\gamma\\ &[*119·11·33.*103·2.*100·51.*118·01]\end{align}\]

As ✱119·33: the logical and arithmetical occurrences of `γ −_c ν` are in one type `W` (whose
adequacy is not needed).

**Status.** proved (reading): the logical and the arithmetical occurrences of `γ −_c ν` are in one
type `W`, as PM's proof (by ✱118·01) requires (convention IIT, Prefatory Statement, IV; its
adequacy hypothesis is not needed). -/
theorem pm119_34 {γ β W E : Type*} {G : Set (Set γ)} {ν : Set (Set β)} :
    (G -ᶜ ν : Set (Set W)) ∈ N₀C →
      ((G -ᶜ ν : Set (Set W)) +ᶜ ν : Set (Set E)) = (sm ʻʻ G : Set (Set E)) := by
  rintro ⟨X, hX⟩
  have hXm : X ∈ (G -ᶜ ν : Set (Set W)) := hX ▸ self_mem_n₀c X
  obtain ⟨A, B, ⟨rfl, rfl⟩, ⟨e⟩⟩ := mem_cardSub.1 hXm
  rw [hX, cardAdd_n₀c, sm_img_n₀c']
  exact ncT_congr e

/-- ✱119·35. \(\vdash :\gamma -_{c}\nu \in \text{N}_{0}\text{C}.\supset .\alpha +_{c}\gamma =(\alpha +_{c}\nu )+_{c}(\gamma -_{c}\nu )\)

PM's cardinal `α` is `μ`. The arithmetical component `α +_c ν` is in an adequate type `W₁` (IIT);
the arithmetical and the logical occurrences of `γ −_c ν` are in one type `W₂` (as ✱119·33; its
adequacy is not needed).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W₁` of
`α +_c ν` is adequate; the arithmetical and the logical occurrences of `γ −_c ν` are in one type
`W₂`, as PM's proof (by ✱119·34) requires. -/
theorem pm119_35 {α γ β W₁ W₂ E : Type*} {μ : Set (Set α)} {G : Set (Set γ)} {ν : Set (Set β)}
    (h₁ : AdeqAdd W₁ μ ν) :
    (G -ᶜ ν : Set (Set W₂)) ∈ N₀C →
      (μ +ᶜ G : Set (Set E)) = ((μ +ᶜ ν : Set (Set W₁)) +ᶜ (G -ᶜ ν : Set (Set W₂)) : Set (Set E)) := by
  rintro ⟨X, hX⟩
  have hXm : X ∈ (G -ᶜ ν : Set (Set W₂)) := hX ▸ self_mem_n₀c X
  obtain ⟨A, B, ⟨rfl, rfl⟩, ⟨e⟩⟩ := mem_cardSub.1 hXm
  rw [hX]
  by_cases hμ : ∃ C, μ = n₀c C
  · obtain ⟨C, rfl⟩ := hμ
    rw [cardAdd_n₀c, cardAdd_n₀c, n₀c_eq_ncT X, cardAdd_ncT (adeqAdd_emb h₁ C B) (emb_self X)]
    exact ncT_congr (((Equiv.refl _).sumCongr (e.symm.trans (Equiv.sumComm _ _))).trans
      (Equiv.sumAssoc _ _ _).symm)
  · push Not at hμ
    simp only [cardAdd_eq_empty_of_left hμ, cardAdd_empty_left]

/-- ✱119·41. \[\begin{align}\vdash \colon\ldotp \delta \in \text{Nc}ʻ\beta& -_{c}\text{Nc}ʻ\gamma .\supset :\\ &\xi \in (\text{Nc}ʻ\alpha +_{c}\text{Nc}ʻ\beta )-_{c}\text{Nc}ʻ\gamma .\equiv .{(\alpha +\delta )+\gamma }\text{ sm }(\xi +\gamma )\end{align}\]

`Nc'α +_c Nc'β` (an argument of `−_c`) is in an adequate type `W` (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
arithmetical component `Nc'α +_c Nc'β` is adequate; the arguments `Nc'α`, `Nc'β`, `Nc'γ` are
`N₀c'α`, `N₀c'β`, `N₀c'γ` (normal adjustment). -/
theorem pm119_41 {α β γ W D X : Type*} {A : Set α} {B : Set β} {G : Set γ} {δ : Set D}
    {ξ : Set X} (hW : AdeqAdd W (n₀c A) (n₀c B)) :
    δ ∈ (n₀c B -ᶜ n₀c G : Set (Set D)) →
      (ξ ∈ ((n₀c A +ᶜ n₀c B : Set (Set W)) -ᶜ n₀c G : Set (Set X)) ↔
        sm (A +ₐ δ +ₐ G) (ξ +ₐ G)) := by
  intro hδ
  obtain ⟨G', hG, ⟨e⟩⟩ := mem_cardSub_n₀c.1 hδ
  obtain ⟨eG⟩ := eq_n₀c_iff_equiv.1 hG
  have eδ : ↥δ ⊕ ↥G ≃ ↥B := ((Equiv.refl _).sumCongr eG).trans e
  rw [mem_cardSub_of_eq (cardAdd_n₀c A B) (adeqAdd_emb hW A B), sm_iff_nonempty_equiv]
  have k : ↥(A +ₐ δ +ₐ G) ≃ ↥A ⊕ ↥B :=
    (clsSumEquiv _ _).trans (((clsSumEquiv A δ).sumCongr (Equiv.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans ((Equiv.refl _).sumCongr eδ)))
  constructor
  · rintro ⟨f⟩; exact ⟨k.trans (f.symm.trans (clsSumEquiv ξ G).symm)⟩
  · rintro ⟨f⟩; exact ⟨(clsSumEquiv ξ G).symm.trans (f.symm.trans k)⟩

/-- ✱119·42. \[\begin{align}\vdash \colon\ldotp \text{Nc}ʻ\beta -_{c}\text{Nc}ʻ\gamma &\in \text{N}_{0}\text{C}.\eta \in \text{Nc}ʻ\alpha +_{c}(\text{Nc}ʻ\beta -_{c}\text{Nc}ʻ\gamma ).\supset :\\ &\xi \in (\text{Nc}ʻ\alpha +_{c}\text{Nc}ʻ\beta )-_{c}\text{Nc}ʻ\gamma .\equiv .(\eta +\gamma )\text{ sm }(\xi +\gamma )\end{align}\]

`Nc'β −_c Nc'γ` occurs logically (`∈ N₀C`) and arithmetically; as in ✱119·33 both are in one
type `V` (whose adequacy is not needed). `Nc'α +_c Nc'β` is in an adequate type `W`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of
`Nc'α +_c Nc'β` is adequate; the logical and the arithmetical occurrences of `Nc'β −_c Nc'γ` are in
one type `V`, as PM's proof (by ✱118·01) requires; the arguments `Nc'α`, `Nc'β`, `Nc'γ` are
`N₀c'α`, `N₀c'β`, `N₀c'γ` (normal adjustment). -/
theorem pm119_42 {α β γ V W H X : Type*} {A : Set α} {B : Set β} {G : Set γ} {η : Set H}
    {ξ : Set X} (hW : AdeqAdd W (n₀c A) (n₀c B)) :
    (n₀c B -ᶜ n₀c G : Set (Set V)) ∈ N₀C ∧
        η ∈ (n₀c A +ᶜ (n₀c B -ᶜ n₀c G : Set (Set V)) : Set (Set H)) →
      (ξ ∈ ((n₀c A +ᶜ n₀c B : Set (Set W)) -ᶜ n₀c G : Set (Set X)) ↔
        sm (η +ₐ G) (ξ +ₐ G)) := by
  rintro ⟨⟨D, hD⟩, hη⟩
  have hDm : D ∈ (n₀c B -ᶜ n₀c G : Set (Set V)) := hD ▸ self_mem_n₀c D
  obtain ⟨G', hG, ⟨e⟩⟩ := mem_cardSub_n₀c.1 hDm
  obtain ⟨eG⟩ := eq_n₀c_iff_equiv.1 hG
  have eD : ↥D ⊕ ↥G ≃ ↥B := ((Equiv.refl _).sumCongr eG).trans e
  rw [hD, cardAdd_n₀c] at hη
  obtain ⟨eη⟩ := hη
  rw [mem_cardSub_of_eq (cardAdd_n₀c A B) (adeqAdd_emb hW A B), sm_iff_nonempty_equiv]
  have k : ↥(η +ₐ G) ≃ ↥A ⊕ ↥B :=
    (clsSumEquiv _ _).trans ((eη.sumCongr (Equiv.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans ((Equiv.refl _).sumCongr eD)))
  constructor
  · rintro ⟨f⟩; exact ⟨k.trans (f.symm.trans (clsSumEquiv ξ G).symm)⟩
  · rintro ⟨f⟩; exact ⟨(clsSumEquiv ξ G).symm.trans (f.symm.trans k)⟩

/-- ✱119·43. \[\begin{align}\vdash :\text{Nc}ʻ\beta -_{c}\text{Nc}ʻ\gamma &\in \text{N}_{0}\text{C}.\supset .\\ &\text{Nc}ʻ\alpha +_{c}(\text{Nc}ʻ\beta -_{c}\text{Nc}ʻ\gamma )\subset (\text{Nc}ʻ\alpha +_{c}\text{Nc}ʻ\beta )-_{c}\text{Nc}ʻ\gamma \end{align}\]

**Status.** proved (reading): as ✱119·42 (convention IIT for `Nc'α +_c Nc'β`; the logical and
arithmetical occurrences of `Nc'β −_c Nc'γ` in one type `V`; normal adjustment). -/
theorem pm119_43 {α β γ V W X : Type*} {A : Set α} {B : Set β} {G : Set γ}
    (hW : AdeqAdd W (n₀c A) (n₀c B)) :
    (n₀c B -ᶜ n₀c G : Set (Set V)) ∈ N₀C →
      (n₀c A +ᶜ (n₀c B -ᶜ n₀c G : Set (Set V)) : Set (Set X)) ⊆
        ((n₀c A +ᶜ n₀c B : Set (Set W)) -ᶜ n₀c G : Set (Set X)) :=
  fun hN _ hη => (pm119_42 hW ⟨hN, hη⟩).2 (sm_refl _)

/-- ✱119·44. \(\vdash :\mu +_{c}(\nu -_{c}\varpi )\subset (\mu +_{c}\nu )-_{c}\varpi\)

The arithmetical components `ν −_c ϖ` and `μ +_c ν` are in types `W₁`, `W₂`; IIT takes them
adequate, and only the adequacy of `W₂` is needed.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W₂` of
`μ +_c ν` is adequate (that of `ν −_c ϖ`, `W₁`, is arbitrary). -/
theorem pm119_44 {α β γ W₁ W₂ X : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ϖ : Set (Set γ)}
    (h₂ : AdeqAdd W₂ μ ν) :
    (μ +ᶜ (ν -ᶜ ϖ : Set (Set W₁)) : Set (Set X)) ⊆
      ((μ +ᶜ ν : Set (Set W₂)) -ᶜ ϖ : Set (Set X)) := by
  rintro η ⟨M, D, ⟨rfl, hD⟩, hsm⟩
  have hDm : D ∈ (ν -ᶜ ϖ : Set (Set W₁)) := hD ▸ self_mem_n₀c D
  obtain ⟨B, C, ⟨rfl, rfl⟩, ⟨e⟩⟩ := mem_cardSub.1 hDm
  obtain ⟨f⟩ := sm_iff_nonempty_equiv.1 hsm
  rw [mem_cardSub_of_eq (cardAdd_n₀c M B) (adeqAdd_emb h₂ M B)]
  exact ⟨((f.trans (clsSumEquiv M D)).sumCongr (Equiv.refl _)).trans
    ((Equiv.sumAssoc _ _ _).trans ((Equiv.refl _).sumCongr e))⟩

/-- ✱119·45. \[\begin{align}&\vdash :(\mu +_{c} \nu )-_{c}\varpi \in \text{NC}.\exists !\{\mu +_{c}(\nu -_{c}\varpi )\}.\supset .\mu +_{c}(\nu -_{c}\varpi )=(\mu +_{c}\nu )-_{c}\varpi \\ &[*119·44.*100·33·321.*110·42]\end{align}\]

IT binds the equational occurrences of `(μ +_c ν) −_c ϖ` and `μ +_c (ν −_c ϖ)` to their logical
ones (one type `X`, also by meaning); the converse domain of `NC` is a free type `Y`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W₂` of
`μ +_c ν` is adequate (that of `ν −_c ϖ`, `W₁`, is arbitrary). -/
theorem pm119_45 {α β γ W₁ W₂ X Y : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    {ϖ : Set (Set γ)} (h₂ : AdeqAdd W₂ μ ν) :
    ((μ +ᶜ ν : Set (Set W₂)) -ᶜ ϖ : Set (Set X)) ∈ NC Y ∧
        (μ +ᶜ (ν -ᶜ ϖ : Set (Set W₁)) : Set (Set X)).Nonempty →
      (μ +ᶜ (ν -ᶜ ϖ : Set (Set W₁)) : Set (Set X)) =
        ((μ +ᶜ ν : Set (Set W₂)) -ᶜ ϖ : Set (Set X)) := by
  rintro ⟨hNC, ⟨η, hη⟩⟩
  have hη' := pm119_44 (X := X) (W₁ := W₁) h₂ hη
  have hR : ((μ +ᶜ ν : Set (Set W₂)) -ᶜ ϖ : Set (Set X)) = n₀c η := by
    rcases NC_cases hNC with h | h
    · rw [h] at hη'; exact absurd hη' (Set.notMem_empty η)
    · exact n₀c_eq_of_mem h hη'
  obtain ⟨M, D, ⟨rfl, hD⟩, -⟩ := id hη
  rw [hR, hD, cardAdd_n₀c]
  rw [hD, cardAdd_n₀c] at hη
  exact ncT_eq_n₀c_of_mem hη

/-- `sm_{δ,γ}''(μ −_c ν)_γ = (μ −_c ν)_δ ∩ D'sm_{δ,γ}`, the common form of ✱119·51·52. -/
private theorem relTT_sm_img_cardSub {α β Δ Γ : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (d : Set Δ) (g : Set Γ) :
    relTT sm d g ʻʻ (μ -ᶜ ν : Set (Set Γ)) = (μ -ᶜ ν : Set (Set Δ)) ∩ dom (relTT sm d g) := by
  ext ζ
  rw [mem_relTT_img, Set.mem_inter_iff, mem_dom_relTT]
  constructor
  · rintro ⟨η, hη, hζη⟩
    obtain ⟨A, B, hAB, ⟨e⟩⟩ := mem_cardSub.1 hη
    obtain ⟨f⟩ := sm_iff_nonempty_equiv.1 hζη
    exact ⟨mem_cardSub.2 ⟨A, B, hAB, ⟨(f.sumCongr (Equiv.refl _)).trans e⟩⟩, η, hζη⟩
  · rintro ⟨hζ, η, hζη⟩
    obtain ⟨A, B, hAB, ⟨e⟩⟩ := mem_cardSub.1 hζ
    obtain ⟨f⟩ := sm_iff_nonempty_equiv.1 hζη
    exact ⟨η, mem_cardSub.2 ⟨A, B, hAB, ⟨(f.symm.sumCongr (Equiv.refl _)).trans e⟩⟩, hζη⟩

/-- ✱119·51. \(\vdash :\text{ sm }_{\delta ,\gamma }ʻʻ(\text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta )_{\gamma }=(\text{Nc}ʻ\alpha -_{c}\text{Nc}ʻ\beta )_{\delta }\cap \text{D}ʻ\text{ sm }_{\delta ,\gamma }\)

`sm_{δ,γ}` is `relTT sm d g` (✱65·1) for classes `d : Set Δ`, `g : Set Γ`; `(…)_γ` is the
difference in the type `Γ` of the members of `γ`.

**Status.** proved (reading): the arguments `Nc'α`, `Nc'β` of `−_c` are `N₀c'α`, `N₀c'β`
(normal adjustment). -/
theorem pm119_51 {α β Δ Γ : Type*} {A : Set α} {B : Set β} {d : Set Δ} {g : Set Γ} :
    relTT sm d g ʻʻ (n₀c A -ᶜ n₀c B : Set (Set Γ)) =
      (n₀c A -ᶜ n₀c B : Set (Set Δ)) ∩ dom (relTT sm d g) :=
  relTT_sm_img_cardSub d g

/-- ✱119·52. \(\vdash :\text{ sm }_{\delta ,\gamma }ʻʻ(\mu -_{c}\nu )_{\gamma }=(\mu -_{c}\nu )_{\delta }\cap \text{D}ʻ\text{ sm }_{\delta ,\gamma } \quad[*119·51·11]\) -/
theorem pm119_52 {α β Δ Γ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {d : Set Δ} {g : Set Γ} :
    relTT sm d g ʻʻ (μ -ᶜ ν : Set (Set Γ)) = (μ -ᶜ ν : Set (Set Δ)) ∩ dom (relTT sm d g) :=
  relTT_sm_img_cardSub d g

/-- ✱119·53. \(\vdash \colon\ldotp tʻ\delta =\text{D}ʻ\text{ sm }_{\delta ,\gamma }.\supset :\text{ sm }_{\delta ,\gamma }ʻʻ(\mu -_{c}\nu )_{\gamma }=(\mu -_{c}\nu )_{\delta } \quad[*119·52.(*65·01)]\) -/
theorem pm119_53 {α β Δ Γ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {d : Set Δ} {g : Set Γ} :
    typ d = dom (relTT sm d g) →
      relTT sm d g ʻʻ (μ -ᶜ ν : Set (Set Γ)) = (μ -ᶜ ν : Set (Set Δ)) := by
  intro h
  rw [pm119_52, ← h, typ_eq_univ, Set.inter_univ]

/-- ✱119·531. \(\vdash :tʻ\delta =\text{D}ʻ\text{ sm }_{\delta ,\gamma }.(\mu -_{c}\nu )_{\delta }\in \text{N}_{0}\text{C}.\supset .\text{ sm }_{\gamma ,\delta }ʻʻ(\mu -_{c}\nu )_{\delta }\in \text{N}_{0}\text{C}\) -/
theorem pm119_531 {α β Δ Γ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {d : Set Δ}
    {g : Set Γ} :
    typ d = dom (relTT sm d g) ∧ (μ -ᶜ ν : Set (Set Δ)) ∈ N₀C →
      relTT sm g d ʻʻ (μ -ᶜ ν : Set (Set Δ)) ∈ N₀C := by
  rintro ⟨h, ⟨X, hX⟩⟩
  have hXd : X ∈ dom (relTT sm d g) := by rw [← h, typ_eq_univ]; trivial
  obtain ⟨η, hη⟩ := mem_dom_relTT.1 hXd
  refine ⟨η, Set.ext fun η' => ?_⟩
  rw [mem_relTT_img, hX, mem_n₀c]
  constructor
  · rintro ⟨ζ, hζ, h'⟩; exact sm_trans h' (sm_trans (mem_n₀c.1 hζ) hη)
  · intro h'; exact ⟨X, self_mem_n₀c X, sm_trans h' (sm_symm hη)⟩

/-- ✱119·532. \[\begin{align}\vdash : tʻ\delta = \text{D}ʻ\text{ sm }_{\delta ,\gamma }.(\mu -_{c}\nu )_{\delta } \in \text{N}_{0}\text{C}.&(\mu -_{c}\nu )_{\gamma } \in \text{NC}.\supset .\\ &\text{ sm }_{\gamma ,\delta }ʻʻ(\mu -_{c}\nu )_{\delta } = (\mu -_{c}\nu )_{\gamma }\end{align}\] -/
theorem pm119_532 {α β Δ Γ Y : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {d : Set Δ}
    {g : Set Γ} :
    (typ d = dom (relTT sm d g) ∧ (μ -ᶜ ν : Set (Set Δ)) ∈ N₀C) ∧
        (μ -ᶜ ν : Set (Set Γ)) ∈ NC Y →
      relTT sm g d ʻʻ (μ -ᶜ ν : Set (Set Δ)) = (μ -ᶜ ν : Set (Set Γ)) := by
  rintro ⟨h, hNC⟩
  obtain ⟨Z, hZ⟩ := pm119_531 h
  have hsub : relTT sm g d ʻʻ (μ -ᶜ ν : Set (Set Δ)) ⊆ (μ -ᶜ ν : Set (Set Γ)) := by
    rw [relTT_sm_img_cardSub g d]; exact Set.inter_subset_left
  have hZm : Z ∈ (μ -ᶜ ν : Set (Set Γ)) := hsub (hZ ▸ self_mem_n₀c Z)
  rcases NC_cases hNC with h0 | h0
  · rw [h0] at hZm; exact absurd hZm (Set.notMem_empty Z)
  · rw [hZ, n₀c_eq_of_mem h0 hZm]

/-- ✱119·54 (Df). \(\text{SM} (\delta ,\gamma ). = : tʻ\delta = \text{D}ʻ\text{ sm }_{\delta ,\gamma } . \lor . tʻ\gamma = \text{D}ʻ\text{ sm }_{\gamma ,\delta } \quad\text{Df}\) -/
theorem pm119_54 {Δ Γ : Type*} {d : Set Δ} {g : Set Γ} :
    SM d g ↔ typ d = dom (relTT sm d g) ∨ typ g = dom (relTT sm g d) :=
  Iff.rfl

/-- ✱119·541. \[\begin{align}\vdash : SM(\delta ,\gamma ).(\mu -_{c}\nu )_{\gamma } \in &\text{N}_{0}\text{C} . (\mu -_{c}\nu )_{\delta } \in \text{NC}.\supset .\\ &\text{ sm }_{\delta ,\gamma }ʻʻ(\mu -_{c}\nu )_{\gamma } = (\mu -_{c}\nu )_{\delta } \quad[*119·53·532]\end{align}\] -/
theorem pm119_541 {α β Δ Γ Y : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {d : Set Δ}
    {g : Set Γ} :
    (SM d g ∧ (μ -ᶜ ν : Set (Set Γ)) ∈ N₀C) ∧ (μ -ᶜ ν : Set (Set Δ)) ∈ NC Y →
      relTT sm d g ʻʻ (μ -ᶜ ν : Set (Set Γ)) = (μ -ᶜ ν : Set (Set Δ)) := by
  rintro ⟨⟨h | h, hN⟩, hNC⟩
  · exact pm119_53 h
  · exact pm119_532 ⟨⟨h, hN⟩, hNC⟩

/-- ✱119·61. \(\vdash : \mu \in \text{N}_{0}\text{C} . \exists ! \text{ sm }_{\xi }ʻʻ\mu . \supset . \mu -_{c}\nu = \text{ sm }_{\xi }ʻʻ\mu -_{c}\nu\)

The two differences, sides of one equation, are in one type `X`. -/
theorem pm119_61 {α β T X : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ N₀C ∧ (sm ʻʻ μ : Set (Set T)).Nonempty →
      (μ -ᶜ ν : Set (Set X)) = ((sm ʻʻ μ : Set (Set T)) -ᶜ ν : Set (Set X)) := by
  rintro ⟨⟨A, rfl⟩, hne⟩
  rw [sm_img_n₀c'] at hne ⊢
  obtain ⟨A', hA'⟩ := hne
  obtain ⟨e⟩ := id hA'
  rw [ncT_eq_n₀c_of_mem hA']
  ext ξ
  rw [mem_cardSub_n₀c, mem_cardSub_n₀c]
  constructor
  · rintro ⟨B, hB, ⟨f⟩⟩; exact ⟨B, hB, ⟨f.trans e.symm⟩⟩
  · rintro ⟨B, hB, ⟨f⟩⟩; exact ⟨B, hB, ⟨f.trans e⟩⟩

/-- ✱119·62. \(\vdash : \nu \in \text{N}_{0}\text{C} . \exists ! \text{ sm }_{\xi }ʻʻ\nu . \supset .\mu -_{c}\nu = \mu -_{c} \text{ sm }_{\xi }ʻʻ\nu\) -/
theorem pm119_62 {α β T X : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    ν ∈ N₀C ∧ (sm ʻʻ ν : Set (Set T)).Nonempty →
      (μ -ᶜ ν : Set (Set X)) = (μ -ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set X)) := by
  rintro ⟨⟨B, rfl⟩, hne⟩
  rw [sm_img_n₀c'] at hne ⊢
  obtain ⟨B', hB'⟩ := hne
  obtain ⟨e⟩ := id hB'
  rw [ncT_eq_n₀c_of_mem hB']
  ext ξ
  rw [mem_cardSub, mem_cardSub]
  constructor
  · rintro ⟨A, B₁, ⟨hA, hB⟩, ⟨f⟩⟩
    obtain ⟨g⟩ := eq_n₀c_iff_equiv.1 hB
    exact ⟨A, B', ⟨hA, rfl⟩, ⟨((Equiv.refl _).sumCongr (e.trans g)).trans f⟩⟩
  · rintro ⟨A, B₁, ⟨hA, hB⟩, ⟨f⟩⟩
    obtain ⟨g⟩ := eq_n₀c_iff_equiv.1 hB
    exact ⟨A, B, ⟨hA, rfl⟩, ⟨((Equiv.refl _).sumCongr (e.symm.trans g)).trans f⟩⟩

/-- ✱119·63. \(\vdash : \mu , \nu \in \text{N}_{0}\text{C} . \exists ! \text{ sm }_{\xi }ʻʻ\mu .\supset .\mu -_{c}\nu = \text{ sm }_{\xi }ʻʻ\mu -_{c} \text{ sm }_{\xi }ʻʻ\nu\) -/
theorem pm119_63 {α β T X : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ∈ N₀C ∧ ν ∈ N₀C) ∧ (sm ʻʻ μ : Set (Set T)).Nonempty →
      (μ -ᶜ ν : Set (Set X)) =
        ((sm ʻʻ μ : Set (Set T)) -ᶜ (sm ʻʻ ν : Set (Set T)) : Set (Set X)) := by
  rintro ⟨⟨hμ, ⟨B, rfl⟩⟩, hne⟩
  by_cases hB : Nonempty (↥B ↪ T)
  · have hνT : (sm ʻʻ n₀c B : Set (Set T)).Nonempty := by
      rw [sm_img_n₀c']; exact ncT_nonempty_iff.2 hB
    rw [pm119_61 ⟨hμ, hne⟩, pm119_62 ⟨n₀c_mem_N₀C B, hνT⟩]
  · obtain ⟨A, rfl⟩ := hμ
    rw [sm_img_n₀c' B, ncT_eq_empty hB, cardSub_empty_right]
    ext ξ
    simp only [Set.mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨B', hB', ⟨e⟩⟩ := mem_cardSub_n₀c.1 h
    obtain ⟨g⟩ := eq_n₀c_iff_equiv.1 hB'
    rw [sm_img_n₀c', ncT_nonempty_iff] at hne
    obtain ⟨f⟩ := hne
    exact hB ⟨(g.toEmbedding.trans (Function.Embedding.inr.trans e.toEmbedding)).trans f⟩

/-- ✱119·64. \(\vdash \colon\ldotp \exists ! \text{ sm }_{\xi }ʻʻ\mu .\supset :\mu \geq \nu .\equiv . \exists !(\mu -_{c}\nu )_{\xi }\) -/
theorem pm119_64 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (sm ʻʻ μ : Set (Set T)).Nonempty → (μ ≥ᶜ ν ↔ (μ -ᶜ ν : Set (Set T)).Nonempty) := by
  intro hne
  constructor
  · intro h
    obtain ⟨A, B, ⟨rfl, rfl⟩, ⟨f⟩⟩ := cardGe_iff.1 h
    rw [sm_img_n₀c', ncT_nonempty_iff] at hne
    obtain ⟨ξ, e⟩ := cardSub_nonempty_of_emb f hne
    exact ⟨ξ, mem_cardSub.2 ⟨A, B, ⟨rfl, rfl⟩, e⟩⟩
  · exact pm119_26

/-!
## [✱120] Inductive cardinals

*(Vol. 2, p. 207)*

> *Summary of* *120.
>
> Inductive Cardinals are those that obey mathematical induction starting from 0, *i.e.* in the language of Part II, Section E, they are the posterity of 0 with respect to the relation of \(\nu\) to \(\nu+_{c}1\), or, in more popular language, they are those that can be reached from 0 by successive additions of 1. In former days, these were supposed to be all the cardinals, and mathematical induction was treated as a kind of self-evident axiom. We now know that only certain cardinals obey mathematical induction starting from 0. It is these cardinals which are to be considered in this number. They embrace 0, 1, 2, ... and generally all those cardinals which would be commonly called finite, all those which can be expressed in the usual Arabic system of numeration, and no others. The propositions to be proved concerning them in this number are elementary and familiar; the interest lies entirely in the definition and method of proof, not in the propositions themselves.
>
> Put \(\text{NC induct} = \hat{\alpha} \{\alpha (+_{c}1)_{*}0\}\quad\text{Df}.\)
>
> …

**Lean reading.** `NC induct` is `NCinduct` (the posterity of `0` under `+_c 1`, `plusC1`,
homogeneous; `1` in the type of its other argument); `N_ξC induct` is `NCinductAt ξ` (equal to
`NCinduct` of the type of `ξ`); `Cls induct` is `ClsInduct` (the finite classes); `Infin ax` is
`InfinAx α`, `Infin ax(x)` is `InfinAxAt x`; `spec'β` is `spec B`. `α, β ∈ NC induct` does not
identify types (Prefatory Statement, V). IT binds the logical and equational occurrences of a formal
number (e.g. `α +_c 1` in ✱120·31·311·41·51·53·55); arithmetical components and sides of `>`, `≥`
are in adequate types (IIT: ✱120·416·417·418·428·429·54·541·542), and an argument or side `Nc'α`
is `N₀c'α` (normal adjustment). AT is not used (Prefatory Statement, VI). PM's cardinal variables
`α`, `β`, `γ` are `μ`, `ν`, `ρ` in Lean. Every inductive cardinal is `N₀c` of a finite class or,
in a finite type, `Λ`; the proofs use finite cardinality. The data file lost the conclusions of
✱120·441·442 (an HTML `<`); they are supplied from the Gutenberg source.

**Status.** proved (all propositions; ✱120·14·151·221·25·31·311·41·416·417·418·426·428·429·433·
436·438·441·442·472·492·493·51·53·54·541·542·55·57·6·64·7·764·765·766 proved (reading), see their
docstrings; ✱120·01·011·02·021·03·04·43 definition)
-/

section Helpers7

open Classical

universe uA uB uC uT uX uY uZ uW

private theorem NCinductAt_eq {α : Type uA} (ξ : Set α) : NCinductAt ξ = NCinduct := by
  rw [NCinductAt, clsT_eq]; rfl

private theorem one_eq_ncT {α : Type uA} : (one : Set (Set α)) = ncT α PUnit.{uX + 1} := by
  ext B
  constructor
  · rintro ⟨x, rfl⟩; rw [mem_ncT, unitCls_eq_singleton]; exact ⟨Equiv.ofUnique _ _⟩
  · rintro ⟨e⟩
    refine ⟨(e.symm PUnit.unit : α), Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
    · have : e ⟨z, hz⟩ = PUnit.unit := Subsingleton.elim _ _
      exact congrArg Subtype.val (e.symm_apply_eq.2 this.symm).symm
    · rw [mem_unitCls.1 hz]; exact (e.symm PUnit.unit).2

private theorem zero_eq_ncT {α : Type uA} : (zero : Set (Set α)) = ncT α PEmpty.{uX + 1} := by
  rw [zero_eq_n₀c_empty, n₀c_eq_ncT]
  exact ncT_congr (Equiv.equivOfIsEmpty _ _)

private theorem two_eq_ncT {α : Type uA} : (two : Set (Set α)) = ncT α (ULift.{uX} Bool) := by
  ext B
  rw [mem_two_iff, mem_ncT]
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    refine ⟨(Equiv.ofBijective (fun b : ULift.{uX} Bool => (⟨if b.down then x else y, by
      cases b.down <;> simp⟩ : ↥({x, y} : Set α))) ⟨?_, ?_⟩).symm⟩
    · rintro ⟨a⟩ ⟨b⟩ h
      have h' := congrArg Subtype.val h
      cases a <;> cases b <;> simp at h' <;> first | rfl | exact absurd h' hxy | exact absurd h'.symm hxy
    · rintro ⟨z, hz⟩
      rcases hz with rfl | rfl
      · exact ⟨⟨true⟩, rfl⟩
      · exact ⟨⟨false⟩, rfl⟩
  · rintro ⟨e⟩
    refine ⟨(e.symm ⟨true⟩ : α), (e.symm ⟨false⟩ : α), fun h => ?_, ?_⟩
    · have := e.symm.injective (Subtype.ext h)
      exact Bool.noConfusion (congrArg ULift.down this)
    · ext z
      constructor
      · intro hz
        have : e ⟨z, hz⟩ = ⟨true⟩ ∨ e ⟨z, hz⟩ = ⟨false⟩ := by
          rcases e ⟨z, hz⟩ with ⟨_ | _⟩ <;> simp
        rcases this with h | h
        · left; exact congrArg Subtype.val ((e.symm_apply_eq.2 h.symm).symm)
        · right; exact congrArg Subtype.val ((e.symm_apply_eq.2 h.symm).symm)
      · rintro (rfl | rfl)
        · exact (e.symm _).2
        · exact (e.symm _).2

private theorem empty_mem_NCinduct_iff {α : Type uA} :
    (∅ : Set (Set α)) ∈ NCinduct ↔ Finite α := by
  constructor
  · intro h
    rcases NCinduct_cases h with ⟨A, -, hA⟩ | ⟨hf, -⟩
    · exact absurd hA.symm (n₀c_ne_empty A)
    · exact hf
  · intro hf
    rw [← n₀c_univ_cardAdd_one]
    exact cardAdd_one_mem_NCinduct (n₀c_mem_NCinduct Set.finite_univ)

private theorem n₀c_mem_NCinduct_iff {α : Type uA} {A : Set α} :
    n₀c A ∈ NCinduct ↔ A.Finite := by
  constructor
  · intro h
    rcases NCinduct_cases h with ⟨B, hB, hAB⟩ | ⟨-, hA⟩
    · obtain ⟨e⟩ := eq_n₀c_iff_equiv.1 hAB
      have : Finite ↥B := hB.to_subtype
      exact Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)
    · exact absurd hA (n₀c_ne_empty A)
  · exact n₀c_mem_NCinduct

/-- Every `ncT α X` with `X` finite is an inductive cardinal (it is `Λ` only in a finite type). -/
private theorem ncT_mem_NCinduct {α : Type uA} {X : Type uX} [Finite X] : ncT α X ∈ NCinduct := by
  by_cases h : Nonempty (X ↪ α)
  · obtain ⟨A, hA⟩ := ncT_nonempty_iff.2 h
    rw [ncT_eq_n₀c_of_mem hA, n₀c_mem_NCinduct_iff]
    obtain ⟨e⟩ := hA
    exact Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)
  · rw [ncT_eq_empty h, empty_mem_NCinduct_iff]
    by_contra hα
    rw [not_finite_iff_infinite] at hα
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin X
    exact h ⟨e.toEmbedding.trans (Fin.valEmbedding.trans (Infinite.natEmbedding α))⟩

private theorem mem_NCinduct_iff' {α : Type uA} {μ : Set (Set α)} :
    μ ∈ NCinduct ↔ (∃ A : Set α, A.Finite ∧ μ = n₀c A) ∨ (Finite α ∧ μ = ∅) := by
  constructor
  · exact NCinduct_cases
  · rintro (⟨A, hA, rfl⟩ | ⟨hf, rfl⟩)
    · exact n₀c_mem_NCinduct hA
    · exact empty_mem_NCinduct_iff.2 hf

private theorem ncT_mem_NCinduct_iff {α : Type uA} {X : Type uX} (h : Nonempty (X ↪ α)) :
    ncT α X ∈ NCinduct ↔ Finite X := by
  obtain ⟨A, hA⟩ := ncT_nonempty_iff.2 h
  rw [ncT_eq_n₀c_of_mem hA, n₀c_mem_NCinduct_iff]
  obtain ⟨e⟩ := hA
  rw [← Set.finite_coe_iff]
  exact ⟨fun _ => Finite.of_equiv _ e, fun _ => Finite.of_equiv _ e.symm⟩

/-- The cancellation of a finite summand: `α + n sm β + n . ⊃ . α sm β` (`n` finite). -/
private theorem equiv_cancel_fin {X : Type uX} {Y : Type uY} :
    ∀ n : ℕ, (X ⊕ Fin n ≃ Y ⊕ Fin n) → Nonempty (X ≃ Y)
  | 0, e => ⟨(Equiv.sumEmpty X (Fin 0)).symm.trans (e.trans (Equiv.sumEmpty Y (Fin 0)))⟩
  | n + 1, e => by
    let o : ∀ (Z : Type uX), Z ⊕ Fin (n + 1) ≃ Option (Z ⊕ Fin n) := fun Z =>
      ((Equiv.refl Z).sumCongr (finSuccEquiv n)).trans
        { toFun := fun s => match s with
            | Sum.inl z => some (Sum.inl z)
            | Sum.inr none => none
            | Sum.inr (some k) => some (Sum.inr k)
          invFun := fun s => match s with
            | none => Sum.inr none
            | some (Sum.inl z) => Sum.inl z
            | some (Sum.inr k) => Sum.inr (some k)
          left_inv := by rintro (z | _ | k) <;> rfl
          right_inv := by rintro (_ | z | k) <;> rfl }
    let o' : ∀ (Z : Type uY), Z ⊕ Fin (n + 1) ≃ Option (Z ⊕ Fin n) := fun Z =>
      ((Equiv.refl Z).sumCongr (finSuccEquiv n)).trans
        { toFun := fun s => match s with
            | Sum.inl z => some (Sum.inl z)
            | Sum.inr none => none
            | Sum.inr (some k) => some (Sum.inr k)
          invFun := fun s => match s with
            | none => Sum.inr none
            | some (Sum.inl z) => Sum.inl z
            | some (Sum.inr k) => Sum.inr (some k)
          left_inv := by rintro (z | _ | k) <;> rfl
          right_inv := by rintro (_ | z | k) <;> rfl }
    exact equiv_cancel_fin n (Equiv.removeNone ((o X).symm.trans (e.trans (o' Y))))

private theorem equiv_cancel {X : Type uX} {Y : Type uY} {N : Type uZ} {N' : Type uW} [Finite N]
    (eN : N ≃ N') (e : X ⊕ N ≃ Y ⊕ N') : Nonempty (X ≃ Y) := by
  obtain ⟨n, ⟨f⟩⟩ := Finite.exists_equiv_fin N
  exact equiv_cancel_fin n (((Equiv.refl X).sumCongr f.symm).trans
    (e.trans ((Equiv.refl Y).sumCongr (eN.symm.trans f))))

end Helpers7

section Helpers8

open Classical

universe uA uB uC uT uX uY uZ uW

private theorem emb_of_finite_card_le {X : Type uX} {Y : Type uY} [Finite X]
    (h : ¬ Finite Y ∨ Nat.card X ≤ Nat.card Y) : Nonempty (X ↪ Y) := by
  rcases h with h | h
  · rw [not_finite_iff_infinite] at h
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin X
    exact ⟨e.toEmbedding.trans (Fin.valEmbedding.trans (Infinite.natEmbedding Y))⟩
  · by_cases hY : Finite Y
    · exact ⟨(Finite.equivFin X).toEmbedding.trans ((Fin.castLEEmb h).trans
        (Finite.equivFin Y).symm.toEmbedding)⟩
    · rw [not_finite_iff_infinite] at hY
      obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin X
      exact ⟨e.toEmbedding.trans (Fin.valEmbedding.trans (Infinite.natEmbedding Y))⟩

private theorem card_le_of_emb {X : Type uX} {Y : Type uY} [Finite Y] (h : Nonempty (X ↪ Y)) :
    Nat.card X ≤ Nat.card Y := let ⟨f⟩ := h; Finite.card_le_of_embedding f

private theorem finite_of_emb {X : Type uX} {Y : Type uY} [Finite Y] (h : Nonempty (X ↪ Y)) :
    Finite X := let ⟨f⟩ := h; Finite.of_injective f f.injective

/-- `ν + 1 ≤ μ . ≡ . ν < μ` for finite `ν`. -/
private theorem emb_sum_unit_iff {N : Type uX} {M : Type uY} [Finite N] :
    Nonempty (N ⊕ PUnit.{uZ + 1} ↪ M) ↔ Nonempty (N ↪ M) ∧ ¬ Nonempty (M ↪ N) := by
  constructor
  · rintro ⟨f⟩
    refine ⟨⟨Function.Embedding.inl.trans f⟩, fun ⟨g⟩ => ?_⟩
    have := Finite.card_le_of_embedding ((f.trans g))
    have h1 : Nat.card PUnit.{uZ + 1} = 1 := Nat.card_unique
    rw [Nat.card_sum, h1] at this
    omega
  · rintro ⟨⟨f⟩, hg⟩
    by_cases hM : Finite M
    · apply emb_of_finite_card_le (Or.inr _)
      have h0 : Nat.card PUnit.{uZ + 1} = 1 := Nat.card_unique
      rw [Nat.card_sum, h0]
      have h1 := Finite.card_le_of_embedding f
      by_contra hlt
      exact hg (emb_of_finite_card_le (Or.inr (by omega)))
    · exact emb_of_finite_card_le (Or.inl hM)

/-- `γ = α + 1` (members of `γ` minus one member). -/
private theorem sub_one_eq {α δ : Type*} {A : Set α} {Y : Type*} (e : ↥A ≃ Y ⊕ PUnit.{1}) :
    (n₀c A -ᶜ (one : Set (Set α)) : Set (Set δ)) = ncT δ Y := by
  ext η
  rw [mem_cardSub_n₀c, mem_ncT]
  constructor
  · rintro ⟨O, hO, ⟨f⟩⟩
    obtain ⟨o, rfl⟩ : O ∈ (one : Set (Set α)) := hO ▸ self_mem_n₀c O
    have : Finite ↥(ι o) := by rw [unitCls_eq_singleton]; exact (Set.finite_singleton o).to_subtype
    exact equiv_cancel ((Equiv.ofUnique ↥({o} : Set α) PUnit.{1})) (f.trans e)
  · rintro ⟨f⟩
    let a : α := e.symm (Sum.inr PUnit.unit)
    refine ⟨{a}, one_eq_n₀c_singleton a, ⟨(f.sumCongr (Equiv.ofUnique _ _)).trans e.symm⟩⟩

private noncomputable def equiv_diff_singleton {α : Type*} {B : Set α} {b : α} (hb : b ∈ B) :
    ↥B ≃ ↥(B \ {b}) ⊕ PUnit.{1} := by
  classical
  exact (Equiv.Set.sumDiffSubset (Set.singleton_subset_iff.2 hb)).symm.trans
    ((Equiv.sumComm _ _).trans ((Equiv.refl _).sumCongr (Equiv.ofUnique _ _)))

end Helpers8

/-- ✱120·26. \(\vdash \colon\ldotp \rho \in \text{Cls induct}:\phi\eta .\supset _{\eta ,x}.\phi(\eta \cup \iota ʻx):\phi\Lambda :\supset .\phi\rho\)

(The e-text places this proposition at the head of ✱120; PM proves it from ✱120·25·251 by
✱90·112.) The antecedent is the product of three, bracketed to the left. -/
theorem pm120_26 {α : Type*} {ρ : Set α} {φ : Set α → Prop} :
    (ρ ∈ ClsInduct ∧ ∀ η x, φ η → φ (η ∪ ι x)) ∧ φ Λ → φ ρ := by
  rintro ⟨⟨hρ, hstep⟩, h0⟩
  have hfin : ρ.Finite := mem_ClsInduct.1 hρ
  induction ρ, hfin using Set.Finite.induction_on with
  | empty => rw [← Null_eq_empty]; exact h0
  | @insert x s _ _ ih =>
    have := hstep s x (ih (mem_ClsInduct.2 ‹_›))
    rwa [unitCls_eq_singleton, Set.union_singleton] at this

/-- ✱120·01 (Df). \(\text{NC induct} = \hat{\alpha}\{\alpha (+_{c}1)_{*}0\} \quad\text{Df}\) -/
theorem pm120_01 {α : Type*} : (NCinduct : Set (Set (Set α))) = {μ | anc plusC1 μ zero} :=
  rfl

/-- ✱120·011 (Df). \(\text{N}_{\xi }\text{C induct} =\hat{\alpha} \{\alpha (+_{c}1)_{*}0_{\xi }\} \quad\text{Df}\) -/
theorem pm120_011 {α : Type*} {ξ : Set α} :
    NCinductAt ξ = {μ | anc plusC1 μ (clsT zero ξ)} :=
  rfl

/-- ✱120·02 (Df). \(\text{Cls induct} = sʻ\text{NC induct} \quad\text{Df}\) -/
theorem pm120_02 {α : Type*} : (ClsInduct : Set (Set α)) = sumCls NCinduct :=
  rfl

/-- ✱120·021 (Df). \(\text{Cls}_{\xi }\text{induct} = sʻ\text{N}_{\xi }\text{C induct} \quad\text{Df}\) -/
theorem pm120_021 {α : Type*} {ξ : Set α} : ClsInductAt ξ = sumCls (NCinductAt ξ) :=
  rfl

/-- ✱120·03 (Df). \(\text{Infin ax}.=:\alpha \in \text{NC induct}.\supset _{a}.\exists !\alpha \quad\text{Df}\)

(The e-text's `⊃_a` is `⊃_α`.) -/
theorem pm120_03 {α : Type*} : InfinAx α ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → μ.Nonempty :=
  Iff.rfl

/-- ✱120·04 (Df). \(\text{Infin ax}(x).=:\alpha \in \text{NC induct}.\supset _{a}.\exists !\alpha (x) \quad\text{Df}\) -/
theorem pm120_04 {α : Type*} {x : α} :
    InfinAxAt x ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → (clsT2 μ x).Nonempty :=
  Iff.rfl

/-- ✱120·1. \(\vdash :\alpha \in \text{NC induct}.\equiv .\alpha (+_{c}1)_{*}0 \quad[(*120·01)]\)

PM's cardinal variable `α` is `μ : Set (Set α)`. -/
theorem pm120_1 {α : Type*} {μ : Set (Set α)} : μ ∈ NCinduct ↔ anc plusC1 μ zero :=
  Iff.rfl

private theorem ancestral_induction_iff {α : Type*} {μ ζ : Set (Set α)} :
    anc plusC1 μ ζ ↔ ∀ M : Set (Set (Set α)),
      (∀ ξ, ξ ∈ M → (ξ +ᶜ (one : Set (Set α)) : Set (Set α)) ∈ M) ∧ ζ ∈ M → μ ∈ M := by
  rw [anc_iff_reflTransGen]
  constructor
  · rintro ⟨-, h⟩ M ⟨hstep, h0⟩
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact h0
    | head hab _ ih => rw [plusC1_iff.1 hab]; exact hstep _ ih
  · intro h
    refine ⟨mem_fld_plusC1 μ, h {ν | Relation.ReflTransGen plusC1 ν ζ} ⟨fun ξ hξ => ?_,
      Relation.ReflTransGen.refl⟩⟩
    exact Relation.ReflTransGen.head rfl hξ

/-- ✱120·101. \[\begin{align}&\vdash \colon\colon \alpha \in \text{NC induct}. \equiv \colon\ldotp \xi \in \mu .\supset _{\xi }.\xi +_{c}1\in \mu :0\in \mu :\supset _{\mu }.\alpha \in \mu \\ &[*120·1.*90·131.*38·12]\end{align}\]

"The conditions of significance require that `ξ +_c 1` should be taken in the same type as
`ξ`" (PM); the class variable `μ` is `M`. -/
theorem pm120_101 {α : Type*} {μ : Set (Set α)} :
    μ ∈ NCinduct ↔ ∀ M : Set (Set (Set α)),
      (∀ ξ, ξ ∈ M → (ξ +ᶜ (one : Set (Set α)) : Set (Set α)) ∈ M) ∧ zero ∈ M → μ ∈ M :=
  ancestral_induction_iff

/-- ✱120·102. \(\vdash :\alpha \in \text{N}_{\eta }\text{C induct}. \equiv .\alpha (+_{c} 1)_{*}0_{\eta } \quad[(*120·011)]\) -/
theorem pm120_102 {α : Type*} {η : Set α} {μ : Set (Set α)} :
    μ ∈ NCinductAt η ↔ anc plusC1 μ (clsT zero η) :=
  Iff.rfl

/-- ✱120·103. \[\begin{align}&\vdash \colon\colon \alpha \in \text{N}_{\eta }\text{C induct}. \equiv \colon\ldotp \xi \in \mu .\supset _{\xi }.(\xi +_{c}1)_{\eta }\in \mu :0_{\eta }\in \mu :\supset _{\mu }.\alpha \in \mu \\ &[*120·101]\end{align}\] -/
theorem pm120_103 {α : Type*} {η : Set α} {μ : Set (Set α)} :
    μ ∈ NCinductAt η ↔ ∀ M : Set (Set (Set α)),
      (∀ ξ, ξ ∈ M → (ξ +ᶜ (one : Set (Set α)) : Set (Set α)) ∈ M) ∧ clsT zero η ∈ M → μ ∈ M :=
  ancestral_induction_iff

/-- ✱120·11. \[\begin{align}&\vdash \colon\ldotp \alpha \in \text{N}_{\eta }\text{C induct}:\phi\xi .\supset _{\xi }.\phi (\xi +_{c}1):\phi 0_{\eta }:\supset .\phi \alpha \\ &[*120·102.*90·112]\end{align}\] -/
theorem pm120_11 {α : Type*} {η : Set α} {μ : Set (Set α)} {φ : Set (Set α) → Prop} :
    (μ ∈ NCinductAt η ∧ ∀ ξ, φ ξ → φ (ξ +ᶜ (one : Set (Set α)) : Set (Set α))) ∧
      φ (clsT zero η) → φ μ := by
  rintro ⟨⟨h, hstep⟩, h0⟩
  exact pm120_103.1 h {ξ | φ ξ} ⟨hstep, h0⟩

/-- ✱120·12. \(\vdash .0\in \text{NC induct} \quad\left[*120·101 \frac{0}{\alpha}\right]\) -/
theorem pm120_12 {α : Type*} : (zero : Set (Set α)) ∈ NCinduct :=
  zero_mem_NCinduct

/-- ✱120·121. \(\vdash :\alpha \in \text{N}_{\xi }\text{C induct}.\supset .(\alpha +_{c}1)_{\xi }\in \text{N}_{\xi }\text{C induct} \quad[*90·172.*120·102]\) -/
theorem pm120_121 {α : Type*} {ξ : Set α} {μ : Set (Set α)} :
    μ ∈ NCinductAt ξ → (μ +ᶜ (one : Set (Set α)) : Set (Set α)) ∈ NCinductAt ξ := by
  rw [NCinductAt_eq]; exact cardAdd_one_mem_NCinduct

/-- ✱120·122. \(\vdash .1\in \text{NC induct} \quad[*120·12·121.*110·641]\) -/
theorem pm120_122 {α : Type*} : (one : Set (Set α)) ∈ NCinduct := by
  rw [one_eq_ncT.{_, 0}]; exact ncT_mem_NCinduct

/-- ✱120·123. \(\vdash .2\in \text{NC induct}. \text{etc}. \quad[*120·122·121.*110·643]\)

("etc.": the same for `3`, `4`, …; stated for `2`.) -/
theorem pm120_123 {α : Type*} : (two : Set (Set α)) ∈ NCinduct := by
  rw [two_eq_ncT.{_, 0}]; exact ncT_mem_NCinduct

/-- ✱120·124. \(\vdash .\alpha +_{c}1\neq 0\)

The `1` is in the type of `α` (encoding decision 10); the two sides of `≠` are in one type. -/
theorem pm120_124 {β γ : Type*} {μ : Set (Set β)} :
    (μ +ᶜ (one : Set (Set β)) : Set (Set γ)) ≠ zero := by
  intro h
  have h0 : (∅ : Set γ) ∈ (μ +ᶜ (one : Set (Set β)) : Set (Set γ)) := by
    rw [h, zero_eq]; exact Set.mem_singleton _
  obtain ⟨A, B, ⟨-, hB⟩, hsm⟩ := h0
  have hBone : B ∈ (one : Set (Set β)) := hB ▸ self_mem_n₀c B
  obtain ⟨x, rfl⟩ := hBone
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hsm
  exact Set.notMem_empty _ (e.symm ((clsSumEquiv A (ι x)).symm (Sum.inr ⟨x, rfl⟩))).2

/-- ✱120·13. \(\vdash \colon\ldotp \alpha \in \text{N}_{\eta }\text{C induct}:\xi \in \text{N}_{\eta }\text{C induct}.\phi \xi .\supset _{\xi }.\phi (\xi +_{c}1):\phi 0_{\eta }:\supset .\phi \alpha\) -/
theorem pm120_13 {α : Type*} {η : Set α} {μ : Set (Set α)} {φ : Set (Set α) → Prop} :
    (μ ∈ NCinductAt η ∧ ∀ ξ, ξ ∈ NCinductAt η ∧ φ ξ →
        φ (ξ +ᶜ (one : Set (Set α)) : Set (Set α))) ∧ φ (clsT zero η) → φ μ := by
  rintro ⟨⟨h, hstep⟩, h0⟩
  refine (pm120_103.1 h {ξ | ξ ∈ NCinductAt η ∧ φ ξ} ⟨fun ξ hξ => ⟨pm120_121 hξ.1, hstep ξ hξ⟩,
    ⟨?_, h0⟩⟩).2
  rw [NCinductAt_eq, clsT_eq]; exact zero_mem_NCinduct

/-- ✱120·14. \(\vdash .\text{NC induct} \subset \text{NC}\)

The converse domain of `NC` is taken in the type `Set α` of the members of the inductive cardinals
(classes of `α`) raised by one: an inductive cardinal is `Nc'` of a class of unit classes, and
`Λ` (inductive when `α` is finite) is `Nc'` of `V` of that type (Cantor), as in PM's proof
(✱101·11, ✱110·42, which use `NC` in a type where `Λ ∈ NC`). In the type `α` itself the inclusion
fails for finite `α` (`Λ ∉ NC α`).

**Status.** proved (reading): the converse domain of `NC` is the type `Set α`, one above that of
the members of the members of the inductive cardinals (`NC` is typically ambiguous; in the type
`α` the proposition fails for finite `α`). -/
theorem pm120_14 {α : Type*} : (NCinduct : Set (Set (Set α))) ⊆ NC (Set α) := by
  intro μ hμ
  rcases NCinduct_cases hμ with ⟨A, -, rfl⟩ | ⟨-, rfl⟩
  · refine mem_NC.2 ⟨(fun a : α => ({a} : Set α)) '' A, ?_⟩
    rw [n₀c_eq_ncT, nc_eq_ncT]
    exact ncT_congr (Equiv.Set.image _ A (fun a b h => Set.singleton_injective h))
  · refine mem_NC.2 ⟨Set.univ, ?_⟩
    rw [nc_eq_ncT, ncT_eq_empty]
    rintro ⟨f⟩
    exact Function.cantor_injective (fun s => f ⟨s, trivial⟩) fun s t h =>
      congrArg Subtype.val (f.injective h)

/-- ✱120·15. \(\vdash :\alpha \in \text{NC induct}.\exists !\alpha .\supset .\text{ sm }ʻʻ\alpha \in \text{NC induct}\)

"A cardinal which is not null and is inductive in any one type is also inductive in any other
type" (PM): `sm''α` in any type `T`. -/
theorem pm120_15 {α T : Type*} {μ : Set (Set α)} :
    μ ∈ NCinduct ∧ μ.Nonempty → (sm ʻʻ μ : Set (Set T)) ∈ NCinduct := by
  rintro ⟨h, hne⟩
  rcases NCinduct_cases h with ⟨A, hA, rfl⟩ | ⟨-, rfl⟩
  · rw [sm_img_n₀c']
    have : Finite ↥A := hA.to_subtype
    exact ncT_mem_NCinduct
  · exact absurd hne Set.not_nonempty_empty

/-- ✱120·151. \(\vdash :\alpha \in \text{NC induct}.\exists !\alpha .\supset .\alpha +_{c}1\in \text{NC induct}\)

The `1` is in the type of `α`; the sum, as in PM's proof, in any type `T`.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty α]` (for an empty `α`, `1 = Λ` there and `0 +_c 1 = Λ`, which is not inductive in an
infinite type). -/
theorem pm120_151 {α T : Type*} [Nonempty α] {μ : Set (Set α)} :
    μ ∈ NCinduct ∧ μ.Nonempty → (μ +ᶜ (one : Set (Set α)) : Set (Set T)) ∈ NCinduct := by
  rintro ⟨h, hne⟩
  rcases NCinduct_cases h with ⟨A, hA, rfl⟩ | ⟨-, rfl⟩
  · have hu : Nonempty (PUnit.{1} ↪ α) := ⟨⟨fun _ => Classical.arbitrary α, fun _ _ _ => rfl⟩⟩
    have : Finite ↥A := hA.to_subtype
    have : Finite (↥A ⊕ PUnit.{1}) := inferInstance
    rw [one_eq_ncT.{_, 0}, n₀c_eq_ncT, cardAdd_gen (good_self A T) (Or.inl hu)]
    exact ncT_mem_NCinduct
  · exact absurd hne Set.not_nonempty_empty

/-- ✱120·152. \(\vdash :\alpha \in \text{NC}.\text{ sm }ʻʻ\alpha \in \text{NC induct}-\iota ʻ\Lambda .\supset .\alpha \in \text{NC induct}-\iota ʻ\Lambda\) -/
theorem pm120_152 {α β T : Type*} {μ : Set (Set α)} :
    μ ∈ NC β ∧ (sm ʻʻ μ : Set (Set T)) ∈ NCinduct \ ι Λ → μ ∈ NCinduct \ ι Λ := by
  rintro ⟨hμ, h1, h2⟩
  have hne : (sm ʻʻ μ : Set (Set T)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ← Null_eq_empty]; exact h2
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [sm_img_empty] at hne; exact absurd hne Set.not_nonempty_empty
  · rw [sm_img_n₀c'] at h1 hne
    have hA : Finite ↥A := (ncT_mem_NCinduct_iff (ncT_nonempty_iff.1 hne)).1 h1
    refine ⟨n₀c_mem_NCinduct (Set.finite_coe_iff.1 hA), ?_⟩
    show ¬ n₀c A = Λ
    rw [Null_eq_empty]; exact n₀c_ne_empty A

/-- ✱120·2. \(\vdash :\rho \in \text{Cls induct}.\equiv .(\exists \alpha ).\alpha \in \text{NC induct}.\rho \in \alpha \quad[(*120·02)]\) -/
theorem pm120_2 {α : Type*} {ρ : Set α} :
    ρ ∈ ClsInduct ↔ ∃ μ : Set (Set α), μ ∈ NCinduct ∧ ρ ∈ μ :=
  Iff.rfl

/-- ✱120·201. \(\vdash \colon\ldotp \rho \text{ sm }\sigma .\supset :\text{N}_{0}\text{c}ʻ\rho \in \text{NC induct}.\equiv .\text{N}_{0}\text{c}ʻ\sigma \in \text{NC induct}\) -/
theorem pm120_201 {α β : Type*} {ρ : Set α} {σ : Set β} :
    sm ρ σ → (n₀c ρ ∈ NCinduct ↔ n₀c σ ∈ NCinduct) := by
  intro h
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
  rw [n₀c_mem_NCinduct_iff, n₀c_mem_NCinduct_iff, ← Set.finite_coe_iff, ← Set.finite_coe_iff]
  exact ⟨fun _ => Finite.of_equiv _ e, fun _ => Finite.of_equiv _ e.symm⟩

/-- ✱120·21. \(\vdash :\rho \in \text{Cls induct}.\equiv .\text{N}_{0}\text{c}ʻ\rho \in \text{NC induct}\) -/
theorem pm120_21 {α : Type*} {ρ : Set α} : ρ ∈ ClsInduct ↔ n₀c ρ ∈ NCinduct := by
  rw [mem_ClsInduct, n₀c_mem_NCinduct_iff]

/-- ✱120·211. \(\vdash :\text{Nc}ʻ\rho \in \text{NC induct} - \iota ʻ\Lambda .\supset .\rho \in \text{Cls induct}\)

`Nc'ρ` is in any type `T` ("it might be possible to determine the ambiguity of `Nc'ρ` so that
`Nc'ρ = Λ`", PM). -/
theorem pm120_211 {α T : Type*} {ρ : Set α} : nc T ρ ∈ NCinduct \ ι Λ → ρ ∈ ClsInduct := by
  rintro ⟨h1, h2⟩
  have hne : (nc T ρ).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ← Null_eq_empty]; exact h2
  rw [nc_eq_ncT] at h1 hne
  have := (ncT_mem_NCinduct_iff (ncT_nonempty_iff.1 hne)).1 h1
  exact mem_ClsInduct.2 (Set.finite_coe_iff.1 this)

/-- ✱120·212. \(\vdash .\Lambda \in \text{Cls induct} \quad[*120·211·12]\) -/
theorem pm120_212 {α : Type*} : (Λ : Set α) ∈ ClsInduct := by
  rw [mem_ClsInduct, Null_eq_empty]; exact Set.finite_empty

/-- ✱120·213. \(\vdash .\iota ʻ\alpha \in \text{Cls induct} \quad [*120·211·122]\)

(`α` here is any object; it is `x`.) -/
theorem pm120_213 {α : Type*} {x : α} : ι x ∈ ClsInduct := by
  rw [mem_ClsInduct, unitCls_eq_singleton]; exact Set.finite_singleton x

/-- ✱120·214. \(\vdash \colon\ldotp \rho \text{ sm }\sigma .\supset :\rho \in \text{Cls induct}.\equiv .\sigma \in \text{Cls induct} \quad[*120·201·21]\) -/
theorem pm120_214 {α β : Type*} {ρ : Set α} {σ : Set β} :
    sm ρ σ → (ρ ∈ ClsInduct ↔ σ ∈ ClsInduct) := by
  intro h
  rw [pm120_21, pm120_21]; exact pm120_201 h

/-- ✱120·22. \(\vdash \colon\colon \eta \in \mu .\supset _{\eta ,y}.\eta \cup \iota ʻy\in \mu :\Lambda \in \mu :\supset _{\mu }.\rho \in \mu \colon\ldotp \supset .\rho \in \text{Cls induct}\) -/
theorem pm120_22 {α : Type*} {ρ : Set α} :
    (∀ M : Set (Set α), (∀ η y, η ∈ M → η ∪ ι y ∈ M) ∧ Λ ∈ M → ρ ∈ M) → ρ ∈ ClsInduct := by
  intro h
  refine h ClsInduct ⟨fun η y hη => ?_, pm120_212⟩
  rw [mem_ClsInduct] at hη ⊢
  rw [unitCls_eq_singleton]; exact hη.union (Set.finite_singleton y)

/-- A class similar to `α + ι'b` is `η ∪ ι'y` with `η sm α` (cf. ✱110·63). -/
private theorem exists_union_unit_of_sm {α β γ : Type*} {ζ : Set γ} {A : Set α} {O : Set β}
    (hO : O ∈ (one : Set (Set β))) (h : sm ζ (A +ₐ O)) :
    ∃ (η : Set γ) (y : γ), sm η A ∧ ζ = η ∪ ι y := by
  classical
  obtain ⟨b, rfl⟩ := hO
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
  let e' : ↥ζ ≃ ↥A ⊕ ↥(ι b) := e.trans (clsSumEquiv A (ι b))
  let y : ↥ζ := e'.symm (Sum.inr ⟨b, rfl⟩)
  have hy : ({(y : γ)} : Set γ) ⊆ ζ := Set.singleton_subset_iff.2 y.2
  have e2 : ↥(ζ \ {(y : γ)}) ⊕ ↥({(y : γ)} : Set γ) ≃ ↥A ⊕ ↥(ι b) :=
    (Equiv.sumComm _ _).trans ((Equiv.Set.sumDiffSubset hy).trans e')
  have hfin : Finite ↥({(y : γ)} : Set γ) := Set.finite_singleton _ |>.to_subtype
  obtain ⟨f⟩ := equiv_cancel ((Equiv.ofUnique PUnit.{1} ↥({(y : γ)} : Set γ)).symm.trans
    (Equiv.ofUnique PUnit.{1} ↥({b} : Set β))) e2
  refine ⟨ζ \ {(y : γ)}, y, sm_iff_nonempty_equiv.2 ⟨f⟩, ?_⟩
  rw [unitCls_eq_singleton, Set.sdiff_union_self, Set.union_eq_left.2 hy]

/-- ✱120·221. \(\vdash \colon\ldotp \eta \in \mu .\supset _{\eta ,y}.\eta \cup \iota ʻy\in \mu :\text{Nc}ʻ\rho \subset \mu :\supset .\text{Nc}ʻ\rho +_{c}1\subset \mu \)

`Nc'ρ ⊂ μ` puts `Nc'ρ` in the type of the members of `μ`; `Nc'ρ +_c 1` is `N₀c'ρ +_c 1`
(✱110·03), the `1` in the type of `ρ`.

**Status.** proved (reading): the argument `Nc'ρ` of `+_c` is `N₀c'ρ` (✱110·03, normal
adjustment). -/
theorem pm120_221 {α β : Type*} {M : Set (Set α)} {ρ : Set β} :
    (∀ η y, η ∈ M → η ∪ ι y ∈ M) ∧ nc α ρ ⊆ M →
      (n₀c ρ +ᶜ (one : Set (Set β)) : Set (Set α)) ⊆ M := by
  rintro ⟨hM, hρ⟩ ζ ⟨A, O, ⟨hA, hO⟩, hsm⟩
  obtain ⟨η, y, hη, rfl⟩ := exists_union_unit_of_sm (hO ▸ self_mem_n₀c O) hsm
  refine hM η y (hρ ?_)
  exact sm_trans hη (mem_n₀c.1 (hA ▸ self_mem_n₀c A))

/-- ✱120·222. \(\vdash \colon\ldotp \eta \in \mu .\supset _{\eta ,y}.\eta \cup \iota ʻy\in \mu :\xi \in \text{NC}.\xi \subset \mu :\supset .\xi +_{c}1\subset \mu\) -/
theorem pm120_222 {α β : Type*} {M : Set (Set α)} {ξ : Set (Set α)} :
    (∀ η y, η ∈ M → η ∪ ι y ∈ M) ∧ (ξ ∈ NC β ∧ ξ ⊆ M) →
      (ξ +ᶜ (one : Set (Set α)) : Set (Set α)) ⊆ M := by
  rintro ⟨hM, hξ, hsub⟩ ζ ⟨A, O, ⟨rfl, hO⟩, hsm⟩
  obtain ⟨η, y, hη, rfl⟩ := exists_union_unit_of_sm (hO ▸ self_mem_n₀c O) hsm
  exact hM η y (hsub (mem_n₀c.2 hη))

/-- ✱120·23. \(\vdash \colon\ldotp \eta \in \mu .\supset _{\eta ,y}.\eta \cup \iota ʻy\in \mu :\Lambda \in \mu :\supset .\text{Cls induct}\subset \mu\) -/
theorem pm120_23 {α : Type*} {M : Set (Set α)} :
    (∀ η y, η ∈ M → η ∪ ι y ∈ M) ∧ Λ ∈ M → (ClsInduct : Set (Set α)) ⊆ M := by
  rintro ⟨hM, h0⟩ ρ hρ
  exact pm120_26 ⟨⟨hρ, fun η x => hM η x⟩, h0⟩

/-- ✱120·24. \(\vdash \colon\colon \rho \in \text{Cls induct}.\equiv \colon\ldotp \eta \in \mu .\supset _{\eta ,y}.\eta \cup \iota ʻy\in \mu :\Lambda \in \mu :\supset _{\mu }.\rho \in \mu\) -/
theorem pm120_24 {α : Type*} {ρ : Set α} :
    ρ ∈ ClsInduct ↔ ∀ M : Set (Set α), (∀ η y, η ∈ M → η ∪ ι y ∈ M) ∧ Λ ∈ M → ρ ∈ M :=
  ⟨fun h _ hM => pm120_23 hM h, pm120_22⟩

/-- ✱120·25. \[\begin{align}&\vdash :M=\hat{\eta} \hat{\zeta}\{(\exists y).\zeta =\eta \cup \iota ʻy\}.\supset .\text{Cls induct}=\overleftarrow{M}_{*}ʻ\Lambda\\ &[*120·24.*90·131]\end{align}\]

`M⃖_*'Λ` is `rels (anc M) Λ`, the posterity of `Λ`.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty α]` (for an empty `α`, `M` is empty, `Λ` is not in its field and `M⃖_*'Λ = Λ`). -/
theorem pm120_25 {α : Type*} [Nonempty α] {M : Set α → Set α → Prop} :
    M = (fun η ζ => ∃ y, ζ = η ∪ ι y) → (ClsInduct : Set (Set α)) = rels (anc M) Λ := by
  rintro rfl
  have hfld : (Λ : Set α) ∈ fld (fun η ζ : Set α => ∃ y, ζ = η ∪ ι y) :=
    ⟨Λ ∪ ι (Classical.arbitrary α), Or.inl ⟨_, rfl⟩⟩
  ext ζ
  show ζ ∈ ClsInduct ↔ anc _ Λ ζ
  rw [anc_iff_reflTransGen, mem_ClsInduct]
  constructor
  · intro hζ
    refine ⟨hfld, ?_⟩
    induction ζ, hζ using Set.Finite.induction_on with
    | empty => rw [← Null_eq_empty]
    | @insert x s _ _ ih =>
      refine Relation.ReflTransGen.tail ih ⟨x, ?_⟩
      rw [unitCls_eq_singleton, Set.union_singleton]
  · rintro ⟨-, h⟩
    induction h with
    | refl => rw [Null_eq_empty]; exact Set.finite_empty
    | tail _ hbc ih =>
      obtain ⟨y, rfl⟩ := hbc
      rw [unitCls_eq_singleton]; exact ih.union (Set.finite_singleton y)

/-- ✱120·251. \(\vdash :\eta \in \text{Cls induct}.\supset .\eta \cup \iota ʻy\in \text{Cls induct} \quad[*90·172.*120·25]\) -/
theorem pm120_251 {α : Type*} {η : Set α} {y : α} : η ∈ ClsInduct → η ∪ ι y ∈ ClsInduct := by
  rw [mem_ClsInduct, mem_ClsInduct, unitCls_eq_singleton]
  exact fun h => h.union (Set.finite_singleton y)

/-- ✱120·261. \[\begin{align}&\vdash \colon\ldotp \rho \in \text{Cls induct}:\eta \in \text{Cls induct}.\phi\eta .\supset _{\eta ,x}.\phi(\eta \cup \iota ʻx):\phi\Lambda :\supset .\phi\rho \\ &[*120·26·251·212]\end{align}\] -/
theorem pm120_261 {α : Type*} {ρ : Set α} {φ : Set α → Prop} :
    (ρ ∈ ClsInduct ∧ ∀ η x, η ∈ ClsInduct ∧ φ η → φ (η ∪ ι x)) ∧ φ Λ → φ ρ := by
  rintro ⟨⟨hρ, hstep⟩, h0⟩
  exact (pm120_26 (φ := fun η => η ∈ ClsInduct ∧ φ η) ⟨⟨hρ, fun η x h =>
    ⟨pm120_251 h.1, hstep η x h⟩⟩, ⟨pm120_212, h0⟩⟩).2

/-- ✱120·27. \(\vdash :\rho \in \text{Cls induct}.\supset .\text{Nc}ʻ\rho \cap tʻ\gamma \in \text{NC induct}\)

`γ : Set Γ` is any class; `Nc'ρ ∩ t'γ` is `Nc'ρ` in the type `Γ`. -/
theorem pm120_27 {α Γ : Type*} {ρ : Set α} {G : Set Γ} :
    ρ ∈ ClsInduct → nc Γ ρ ∩ typ G ∈ NCinduct := by
  intro h
  rw [typ_eq_univ, Set.inter_univ, nc_eq_ncT]
  have : Finite ↥ρ := (mem_ClsInduct.1 h).to_subtype
  exact ncT_mem_NCinduct

/-- ✱120·3. \(\vdash \colon\ldotp \text{Infin ax}.\equiv :\alpha \in \text{NC induct}.\supset _{\alpha }.\exists !\alpha \quad[(*120·03)]\)

`Infin ax` and `NC induct` are at one type, that of the cardinals `α` (worked example of
`Defs/Part3`). -/
theorem pm120_3 {α : Type*} : InfinAx α ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → μ.Nonempty :=
  Iff.rfl

/-- ✱120·301. \(\vdash \colon\ldotp \text{Infin ax}(x).\equiv :\alpha \in \text{NC induct}.\supset _{\alpha }.\exists !\alpha (x) \quad[(*120·04)]\) -/
theorem pm120_301 {α : Type*} {x : α} :
    InfinAxAt x ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → (clsT2 μ x).Nonempty :=
  Iff.rfl

/-- ✱120·31. \(\vdash :\exists !\text{Nc}ʻ\alpha +_{c}1.\text{Nc}ʻ\alpha +_{c}1=\text{Nc}ʻ\beta +_{c}1.\supset .\text{Nc}ʻ\alpha =\text{Nc}ʻ\beta .\alpha \text{ sm }\beta \)

`Nc'α +_c 1` is `N₀c'α +_c 1` (✱110·03), the `1` in the type of `α`; its logical and equational
occurrences are in one type `T` (IT); the conclusion `Nc'α = Nc'β` is in a free type `E`.

**Status.** proved (reading): the arguments `Nc'α`, `Nc'β` of `+_c` are `N₀c'α`, `N₀c'β`
(✱110·03, normal adjustment); convention IT (Prefatory Statement, IV) binds the logical and the
equational occurrences of `Nc'α +_c 1`. -/
theorem pm120_31 {α β T E : Type*} {A : Set α} {B : Set β} :
    (n₀c A +ᶜ (one : Set (Set α)) : Set (Set T)).Nonempty ∧
        (n₀c A +ᶜ (one : Set (Set α)) : Set (Set T)) = (n₀c B +ᶜ (one : Set (Set β)) : Set (Set T)) →
      nc E A = nc E B ∧ sm A B := by
  rintro ⟨⟨ξ, hξ⟩, h⟩
  have hξ' : ξ ∈ (n₀c B +ᶜ (one : Set (Set β)) : Set (Set T)) := h ▸ hξ
  obtain ⟨A₁, O₁, ⟨hA, hO₁⟩, h1⟩ := hξ
  obtain ⟨B₁, O₂, ⟨hB, hO₂⟩, h2⟩ := hξ'
  obtain ⟨eA⟩ := eq_n₀c_iff_equiv.1 hA
  obtain ⟨eB⟩ := eq_n₀c_iff_equiv.1 hB
  obtain ⟨a, ha⟩ : O₁ ∈ (one : Set (Set α)) := hO₁ ▸ self_mem_n₀c O₁
  obtain ⟨b, hb⟩ : O₂ ∈ (one : Set (Set β)) := hO₂ ▸ self_mem_n₀c O₂
  subst ha hb
  obtain ⟨f1⟩ := sm_iff_nonempty_equiv.1 h1
  obtain ⟨f2⟩ := sm_iff_nonempty_equiv.1 h2
  have hfin : Finite ↥(ι a) := by rw [unitCls_eq_singleton]; exact Set.finite_singleton a |>.to_subtype
  have k : ↥A₁ ⊕ ↥(ι a) ≃ ↥B₁ ⊕ ↥(ι b) :=
    (clsSumEquiv _ _).symm.trans (f1.symm.trans (f2.trans (clsSumEquiv _ _)))
  have u : ↥(ι a) ≃ ↥(ι b) :=
    (Equiv.ofUnique PUnit.{1} ↥({a} : Set α)).symm.trans (Equiv.ofUnique PUnit.{1} ↥({b} : Set β))
  obtain ⟨g⟩ := equiv_cancel u k
  have hsm : sm A B := sm_iff_nonempty_equiv.2 ⟨eA.trans (g.trans eB.symm)⟩
  exact ⟨nc_eq_nc_of_sm hsm, hsm⟩

private theorem mem_cardAdd' {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ξ : Set T} :
    ξ ∈ (μ +ᶜ ν : Set (Set T)) ↔
      ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ Nonempty (↥ξ ≃ ↥A ⊕ ↥B) := by
  constructor
  · rintro ⟨A, B, hAB, h⟩
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
    exact ⟨A, B, hAB, ⟨e.trans (clsSumEquiv A B)⟩⟩
  · rintro ⟨A, B, hAB, ⟨e⟩⟩
    exact ⟨A, B, hAB, sm_iff_nonempty_equiv.2 ⟨e.trans (clsSumEquiv A B).symm⟩⟩

private theorem unit_of_mem_one {α : Type*} {O : Set α} (h : O ∈ (one : Set (Set α))) :
    Nonempty (↥O ≃ PUnit.{1}) := by
  rw [one_eq_ncT.{_, 0}] at h; exact h

/-- ✱120·311. \[\begin{align}&\vdash :\exists !\alpha +_{c}1.\alpha +_{c}1=\beta +_{c}1.\supset .\alpha =\text{ sm }ʻʻ\beta .\exists !\alpha\\ &[*120·31.*110·4.*103·16·4·2]\end{align}\]

The logical and equational occurrences of `α +_c 1` are in one type `T` (IT); each `1` is in the
type of its other argument.

**Status.** proved (reading): convention IT (Prefatory Statement, IV) binds the logical and the
equational occurrences of `α +_c 1`. -/
theorem pm120_311 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ +ᶜ (one : Set (Set α)) : Set (Set T)).Nonempty ∧
        (μ +ᶜ (one : Set (Set α)) : Set (Set T)) = (ν +ᶜ (one : Set (Set β)) : Set (Set T)) →
      μ = (sm ʻʻ ν : Set (Set α)) ∧ μ.Nonempty := by
  rintro ⟨⟨ξ, hξ⟩, h⟩
  have hξ' : ξ ∈ (ν +ᶜ (one : Set (Set β)) : Set (Set T)) := h ▸ hξ
  obtain ⟨A, O₁, ⟨rfl, hO₁⟩, ⟨e1⟩⟩ := mem_cardAdd'.1 hξ
  obtain ⟨B, O₂, ⟨rfl, hO₂⟩, ⟨e2⟩⟩ := mem_cardAdd'.1 hξ'
  obtain ⟨u1⟩ := unit_of_mem_one (hO₁ ▸ self_mem_n₀c O₁)
  obtain ⟨u2⟩ := unit_of_mem_one (hO₂ ▸ self_mem_n₀c O₂)
  have : Finite ↥O₁ := Finite.of_equiv _ u1.symm
  obtain ⟨g⟩ := equiv_cancel (u1.trans u2.symm) (e1.symm.trans e2)
  refine ⟨?_, n₀c_nonempty A⟩
  rw [sm_img_n₀c', n₀c_eq_ncT]; exact ncT_congr g

/-- ✱120·32. \(\vdash :\alpha \in \text{NC induct}.\exists !\alpha .\supset .\alpha \neq \alpha +_{c}1\)

The `1` is in the type of `α`; the two sides of `≠` are in one type. -/
theorem pm120_32 {α : Type*} {μ : Set (Set α)} :
    μ ∈ NCinduct ∧ μ.Nonempty → μ ≠ (μ +ᶜ (one : Set (Set α)) : Set (Set α)) := by
  rintro ⟨h, hne⟩ heq
  rcases NCinduct_cases h with ⟨A, hA, rfl⟩ | ⟨-, rfl⟩
  · have hA' : A ∈ (n₀c A +ᶜ (one : Set (Set α)) : Set (Set α)) := heq ▸ self_mem_n₀c A
    obtain ⟨A₁, O, ⟨h1, hO⟩, ⟨e⟩⟩ := mem_cardAdd'.1 hA'
    obtain ⟨eA⟩ := eq_n₀c_iff_equiv.1 h1
    obtain ⟨u⟩ := unit_of_mem_one (hO ▸ self_mem_n₀c O)
    have : Finite ↥A := hA.to_subtype
    have : Finite ↥A₁ := Finite.of_equiv _ eA
    have : Finite ↥O := Finite.of_equiv _ u.symm
    have k := Nat.card_congr (e.trans ((Equiv.refl _).sumCongr u))
    have h0 : Nat.card PUnit.{1} = 1 := Nat.card_unique
    rw [Nat.card_sum, h0, ← Nat.card_congr eA] at k
    omega
  · exact absurd hne Set.not_nonempty_empty

/-- ✱120·321. \(\vdash :\alpha \neq \alpha +_{c}1.\supset .\exists !\alpha\) -/
theorem pm120_321 {α : Type*} {μ : Set (Set α)} :
    μ ≠ (μ +ᶜ (one : Set (Set α)) : Set (Set α)) → μ.Nonempty := by
  intro h
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  exact h (cardAdd_empty_left _).symm

/-- ✱120·322. \(\vdash \colon\ldotp \alpha \in \text{NC induct}.\supset :\exists !\alpha .\equiv .\alpha \neq \alpha +_{c}1 \quad[*120·32·321]\) -/
theorem pm120_322 {α : Type*} {μ : Set (Set α)} :
    μ ∈ NCinduct → (μ.Nonempty ↔ μ ≠ (μ +ᶜ (one : Set (Set α)) : Set (Set α))) :=
  fun h => ⟨fun hne => pm120_32 ⟨h, hne⟩, pm120_321⟩

/-- ✱120·33. \(\vdash \colon\ldotp \text{Infin ax}.\equiv :\alpha \in \text{NC induct}.\supset _{\alpha }.\alpha \neq \alpha +_{c}1 \quad[*120·3·322]\) -/
theorem pm120_33 {α : Type*} :
    InfinAx α ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → μ ≠ (μ +ᶜ (one : Set (Set α)) : Set (Set α)) :=
  ⟨fun h μ hμ => (pm120_322 hμ).1 (h μ hμ), fun h μ hμ => (pm120_322 hμ).2 (h μ hμ)⟩

/-- ✱120·41. \(\vdash \colon\ldotp \nu \in \text{NC induct}.\exists !\alpha +_{c}\nu .\supset :\alpha +_{c}\nu =\beta +_{c}\nu .\supset .\alpha =\text{ sm }ʻʻ\beta\)

PM's cardinals `α`, `β` are `μ`, `ρ`; the logical and the equational occurrences of `α +_c ν` are
in one type `T` (IT), and so is `β +_c ν` (an opposed side).

**Status.** proved (reading): convention IT (Prefatory Statement, IV) binds the logical and the
equational occurrences of `α +_c ν`. -/
theorem pm120_41 {α β ν' T : Type*} {μ : Set (Set α)} {ρ : Set (Set β)} {ν : Set (Set ν')} :
    ν ∈ NCinduct ∧ (μ +ᶜ ν : Set (Set T)).Nonempty →
      ((μ +ᶜ ν : Set (Set T)) = (ρ +ᶜ ν : Set (Set T)) → μ = (sm ʻʻ ρ : Set (Set α))) := by
  rintro ⟨hν, ⟨ξ, hξ⟩⟩ h
  have hξ' : ξ ∈ (ρ +ᶜ ν : Set (Set T)) := h ▸ hξ
  obtain ⟨A, N, ⟨rfl, rfl⟩, ⟨e1⟩⟩ := mem_cardAdd'.1 hξ
  obtain ⟨B, N', ⟨rfl, hN⟩, ⟨e2⟩⟩ := mem_cardAdd'.1 hξ'
  obtain ⟨eN⟩ := eq_n₀c_iff_equiv.1 hN
  have : Finite ↥N := (n₀c_mem_NCinduct_iff.1 hν).to_subtype
  obtain ⟨g⟩ := equiv_cancel eN (e1.symm.trans e2)
  rw [sm_img_n₀c', n₀c_eq_ncT]; exact ncT_congr g

/-- A nonempty difference by an inductive cardinal is a homogeneous cardinal. -/
private theorem cardSub_eq_n₀c {γ β δ : Type*} {G : Set (Set γ)} {ν : Set (Set β)}
    (hν : ν ∈ NCinduct) {ξ : Set δ} (hξ : ξ ∈ (G -ᶜ ν : Set (Set δ))) :
    (G -ᶜ ν : Set (Set δ)) = n₀c ξ := by
  ext η
  constructor
  · intro hη
    obtain ⟨A, B, ⟨hA, hB⟩, ⟨e⟩⟩ := mem_cardSub.1 hξ
    obtain ⟨A', B', ⟨hA', hB'⟩, ⟨e'⟩⟩ := mem_cardSub.1 hη
    obtain ⟨fA⟩ := eq_n₀c_iff_equiv.1 (hA.symm.trans hA')
    obtain ⟨fB⟩ := eq_n₀c_iff_equiv.1 (hB.symm.trans hB')
    rw [hB] at hν
    have : Finite ↥B := (n₀c_mem_NCinduct_iff.1 hν).to_subtype
    have : Finite ↥B' := Finite.of_equiv _ fB
    obtain ⟨g⟩ := equiv_cancel fB.symm (e'.trans (fA.symm.trans e.symm))
    exact mem_n₀c.2 (sm_iff_nonempty_equiv.2 ⟨g⟩)
  · intro hη; exact pm119_14 hξ hη

private theorem cardSub_mem_N₀C {γ β δ : Type*} {G : Set (Set γ)} {ν : Set (Set β)}
    (hν : ν ∈ NCinduct) (h : (G -ᶜ ν : Set (Set δ)).Nonempty) : (G -ᶜ ν : Set (Set δ)) ∈ N₀C :=
  let ⟨ξ, hξ⟩ := h; ⟨ξ, cardSub_eq_n₀c hν hξ⟩

/-- ✱120·411. \[\begin{align}\vdash \colon\ldotp \nu \in &\text{NC induct}.\supset :\\ &\exists !\gamma -_{c}\nu .\supset .\gamma -_{c}\nu \in \text{N}_{0}\text{C}:\gamma \geq \nu .\equiv .(\gamma -_{c}\nu )\cap t_{0}ʻ\gamma \in \text{N}_{0}\text{C}\end{align}\]

The first conjunct's difference is in any type `δ`; `∩ t₀'γ` puts the second in the type of the
members of `γ`. -/
theorem pm120_411 {γ β δ : Type*} {G : Set (Set γ)} {ν : Set (Set β)} :
    ν ∈ NCinduct →
      (((G -ᶜ ν : Set (Set δ)).Nonempty → (G -ᶜ ν : Set (Set δ)) ∈ N₀C) ∧
        (G ≥ᶜ ν ↔ (G -ᶜ ν : Set (Set γ)) ∩ typ₀ G ∈ N₀C)) := by
  intro hν
  refine ⟨cardSub_mem_N₀C hν, ?_⟩
  rw [pm119_27, typ₀_eq_univ, Set.inter_univ]
  exact ⟨cardSub_mem_N₀C hν, fun ⟨X, hX⟩ => ⟨X, hX ▸ self_mem_n₀c X⟩⟩

/-- ✱120·4111. \(\vdash \colon\ldotp \nu \in \text{NC induct}.\exists !\text{ sm }_{\xi }ʻʻ\gamma .\supset :\gamma \geq \nu .\equiv .(\gamma -_{c}\nu )_{\xi }\in \text{N}_{0}\text{C}\) -/
theorem pm120_4111 {γ β T : Type*} {G : Set (Set γ)} {ν : Set (Set β)} :
    ν ∈ NCinduct ∧ (sm ʻʻ G : Set (Set T)).Nonempty →
      (G ≥ᶜ ν ↔ (G -ᶜ ν : Set (Set T)) ∈ N₀C) := by
  rintro ⟨hν, hG⟩
  rw [pm119_64 hG]
  exact ⟨cardSub_mem_N₀C hν, fun ⟨X, hX⟩ => ⟨X, hX ▸ self_mem_n₀c X⟩⟩

/-- ✱120·412. \(\vdash :\nu \in \text{NC induct}.\gamma \geq \nu .\exists !\text{ sm }_{\xi }ʻʻ\gamma .\supset .(\gamma -_{c}\nu )_{\xi }=\{({℩}\alpha )(\alpha +_{c}\nu =\gamma )\}_{\xi }\)

`{(℩α)(α +_c ν = γ)}_ξ` is the description over cardinals `α` of the type `T` of `ξ`; its scope
is the equation. -/
theorem pm120_412 {γ β T : Type*} {G : Set (Set γ)} {ν : Set (Set β)} :
    (ν ∈ NCinduct ∧ G ≥ᶜ ν) ∧ (sm ʻʻ G : Set (Set T)).Nonempty →
      TheIs (fun a : Set (Set T) => (a +ᶜ ν : Set (Set γ)) = G)
        (fun a => (G -ᶜ ν : Set (Set T)) = a) := by
  rintro ⟨⟨hν, hge⟩, hG⟩
  obtain ⟨ξ, hξ⟩ := (pm119_64 hG).1 hge
  refine ⟨G -ᶜ ν, fun a => ⟨fun ha => ?_, fun ha => ?_⟩, rfl⟩
  · obtain ⟨A, B, ⟨rfl, -⟩, -⟩ := cardGe_iff.1 hge
    have hne : (a +ᶜ ν : Set (Set γ)).Nonempty := by rw [ha]; exact n₀c_nonempty A
    obtain ⟨X, B', ⟨rfl, -⟩, -⟩ := cardAdd_nonempty_iff.1 hne
    rw [cardSub_eq_n₀c hν hξ]
    have hX : X ∈ (n₀c A -ᶜ ν : Set (Set T)) := ⟨ha, hne⟩
    rw [← cardSub_eq_n₀c hν hX, cardSub_eq_n₀c hν hξ]
  · subst ha
    rw [cardSub_eq_n₀c hν hξ]
    exact hξ.1

/-- ✱120·413. \(\vdash :\mu \in \text{N}_{0}\text{C}.\supset .\mu -_{c}0=\text{ sm }ʻʻ\mu\)

The `0` is in the type of `μ` (encoding decision 10); both sides are in one type `T`. -/
theorem pm120_413 {α T : Type*} {μ : Set (Set α)} :
    μ ∈ N₀C → (μ -ᶜ (zero : Set (Set α)) : Set (Set T)) = (sm ʻʻ μ : Set (Set T)) := by
  rintro ⟨A, rfl⟩
  rw [sm_img_n₀c']
  ext ξ
  rw [mem_cardSub_n₀c, mem_ncT]
  constructor
  · rintro ⟨B, hB, ⟨e⟩⟩
    have hB' : B = ∅ := n₀c_eq_zero_iff.1 hB.symm
    subst hB'
    exact ⟨(Equiv.sumEmpty _ _).symm.trans e⟩
  · rintro ⟨e⟩
    exact ⟨∅, zero_eq_n₀c_empty, ⟨(Equiv.sumEmpty _ _).trans e⟩⟩

private theorem sub_mem_N₀C_of_ge {γ β T : Type*} {G : Set (Set γ)} {ν : Set (Set β)}
    (hν : ν ∈ NCinduct) (hge : G ≥ᶜ ν) (hG : (sm ʻʻ G : Set (Set T)).Nonempty) :
    (G -ᶜ ν : Set (Set T)) ∈ N₀C :=
  cardSub_mem_N₀C hν ((pm119_64 hG).1 hge)

/-- ✱120·414. \[\begin{align}&\vdash :\mu \in \text{N}_{0}\text{C}-\iota ʻ0.\exists !\text{ sm }_{\xi }ʻʻ\mu .\supset .(\mu -_{c}1)_{\xi }\in \text{N}_{0}\text{C}\\ &[*120·4111.*117·53]\end{align}\]

The `1` is in the type of `μ`. -/
theorem pm120_414 {α T : Type*} {μ : Set (Set α)} :
    μ ∈ N₀C \ ι zero ∧ (sm ʻʻ μ : Set (Set T)).Nonempty →
      (μ -ᶜ (one : Set (Set α)) : Set (Set T)) ∈ N₀C := by
  rintro ⟨⟨⟨A, rfl⟩, h0⟩, hG⟩
  obtain ⟨a⟩ := nonempty_of_n₀c_ne_zero h0
  refine sub_mem_N₀C_of_ge pm120_122 ?_ hG
  rw [one_eq_n₀c_singleton (a : α)]
  exact cardGe_n₀c.2 ⟨⟨fun _ => a, fun _ _ _ => Subsingleton.elim _ _⟩⟩

/-- ✱120·415. \[\begin{align}&\vdash :\mu \in \text{N}_{0}\text{C}-\iota ʻ0-\iota ʻ1.\exists !\text{ sm }_{\xi }ʻʻ\mu .\supset .(\mu -_{c}2)_{\xi }\in \text{N}_{0}\text{C}\\ &[*120·4111.*117·551]\end{align}\]

The `2` is in the type of `μ`. -/
theorem pm120_415 {α T : Type*} {μ : Set (Set α)} :
    μ ∈ (N₀C \ ι zero) \ ι one ∧ (sm ʻʻ μ : Set (Set T)).Nonempty →
      (μ -ᶜ (two : Set (Set α)) : Set (Set T)) ∈ N₀C := by
  rintro ⟨⟨⟨⟨A, rfl⟩, h0⟩, h1⟩, hG⟩
  obtain ⟨a, b, hab⟩ := two_of_n₀c_ne h0 h1
  refine sub_mem_N₀C_of_ge pm120_123 ?_ hG
  have hmem : ({(a : α), (b : α)} : Set α) ∈ (two : Set (Set α)) :=
    mem_two_iff.2 ⟨a, b, fun h => hab (Subtype.ext h), rfl⟩
  rw [two_eq_ncT.{_, 0}] at hmem ⊢
  rw [ncT_eq_n₀c_of_mem hmem]
  refine cardGe_n₀c.2 ⟨⟨fun x => ⟨x, ?_⟩, fun x y h => Subtype.ext (congrArg Subtype.val h :)⟩⟩
  rcases x.2 with h | h <;> rw [h]
  · exact a.2
  · exact b.2

private theorem adeqSub_emb {γ β W : Type*} {G : Set (Set γ)} {ν : Set (Set β)}
    (h : AdeqSub W G ν) (A : Set γ) : Nonempty (↥A ↪ W) := by
  obtain ⟨ξ, hξ⟩ := h
  obtain ⟨B, hB, ⟨e⟩⟩ := mem_cardSub_n₀c.1 hξ
  rw [typ₀_eq_univ, Set.inter_univ] at hB
  have hB' : B = ∅ := n₀c_eq_zero_iff.1 hB.symm
  subst hB'
  exact ⟨(typ₁_emb G A).trans (((Equiv.sumEmpty _ _).symm.trans e).symm.toEmbedding.trans
    (setEmb ξ))⟩

/-- ✱120·416. \[\begin{align}&\vdash :\nu \in \text{NC induct}.\exists !\gamma -_{c}\nu .\supset .(\gamma -_{c}\nu )+_{c}\nu =\text{ sm }ʻʻ\gamma \\ &[*120·411.*119·34]\end{align}\]

The logical occurrence of `γ −_c ν` is in a free type `D`; its arithmetical occurrence is in an
adequate type `W` (IIT); since `ν` is inductive the difference is the same cardinal in both (unlike
✱119·34).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
arithmetical component `γ −_c ν` is adequate. -/
theorem pm120_416 {γ β D W E : Type*} {G : Set (Set γ)} {ν : Set (Set β)} (hW : AdeqSub W G ν) :
    ν ∈ NCinduct ∧ (G -ᶜ ν : Set (Set D)).Nonempty →
      ((G -ᶜ ν : Set (Set W)) +ᶜ ν : Set (Set E)) = (sm ʻʻ G : Set (Set E)) := by
  rintro ⟨hν, hne⟩
  obtain ⟨A, B, ξ, ⟨rfl, rfl⟩, ⟨e⟩⟩ := cardSub_nonempty_iff.1 hne
  obtain ⟨X, ⟨eX⟩⟩ := cardSub_nonempty_of_emb (emb_of_sum_equiv e).some (adeqSub_emb hW A)
  have hX : X ∈ (n₀c A -ᶜ n₀c B : Set (Set W)) := mem_cardSub.2 ⟨A, B, ⟨rfl, rfl⟩, ⟨eX⟩⟩
  rw [cardSub_eq_n₀c hν hX, cardAdd_n₀c, sm_img_n₀c']
  exact ncT_congr eX

/-- ✱120·417. \[\begin{align}&\vdash :\mu \in \text{N}_{0}\text{C}-\iota ʻ0 .\exists !\text{ sm }_{\xi }ʻʻ\gamma .\supset .\alpha +_{c}\gamma =(\alpha +_{c}1)+_{c}(\gamma -_{c}1)_{\xi }\\ &[*120·414.*119·35]\end{align}\]

The hypothesis `μ ∈ N₀C − ι'0` is to be read `γ ∈ N₀C − ι'0` (PM's proof by ✱120·414 applies it to
`γ`; `μ` does not occur in the conclusion). PM's cardinal `α` is `μ`. `α +_c 1` is an arithmetical
component (IIT: adequate type `W`), its `1` in the type of `α`; the `1` of `γ −_c 1` is in the
type of `γ`.

**Status.** proved (reading): misprint (`μ` for `γ` in the hypothesis); convention IIT
(Prefatory Statement, IV): the actual type `W` of `α +_c 1` is adequate; PM assumes every type has
a member (Introduction, Ch. I): `[Nonempty α]` (otherwise `1 = Λ` in the type of `α`). -/
theorem pm120_417 {α γ W T E : Type*} [Nonempty α] {μ : Set (Set α)} {G : Set (Set γ)}
    (hW : AdeqAdd W μ (one : Set (Set α))) :
    G ∈ N₀C \ ι zero ∧ (sm ʻʻ G : Set (Set T)).Nonempty →
      (μ +ᶜ G : Set (Set E)) = ((μ +ᶜ (one : Set (Set α)) : Set (Set W)) +ᶜ
        (G -ᶜ (one : Set (Set γ)) : Set (Set T)) : Set (Set E)) := by
  rintro ⟨⟨⟨A, rfl⟩, h0⟩, hG⟩
  obtain ⟨a⟩ := nonempty_of_n₀c_ne_zero h0
  have hsub := pm120_414 (T := T) ⟨⟨⟨A, rfl⟩, h0⟩, hG⟩
  obtain ⟨X, hX⟩ := hsub
  have hXm : X ∈ (n₀c A -ᶜ (one : Set (Set γ)) : Set (Set T)) := hX ▸ self_mem_n₀c X
  obtain ⟨O, hO, ⟨e⟩⟩ := mem_cardSub_n₀c.1 hXm
  obtain ⟨u⟩ := unit_of_mem_one (hO ▸ self_mem_n₀c O)
  rw [hX]
  by_cases hμ : ∃ M, μ = n₀c M
  · obtain ⟨M, rfl⟩ := hμ
    let x : α := Classical.arbitrary α
    have hW' := adeqAdd_emb hW M {x}
    rw [one_eq_n₀c_singleton x, cardAdd_n₀c, cardAdd_n₀c, n₀c_eq_ncT X, cardAdd_ncT hW' (emb_self X)]
    exact ncT_congr (((Equiv.refl _).sumCongr (e.symm.trans ((Equiv.refl _).sumCongr
      (u.trans (Equiv.ofUnique _ _))))).trans (((Equiv.refl _).sumCongr (Equiv.sumComm _ _)).trans
        (Equiv.sumAssoc _ _ _).symm))
  · push Not at hμ
    simp only [cardAdd_eq_empty_of_left hμ, cardAdd_empty_left]

/-- ✱120·418. \[\begin{align}&\vdash :\nu \in \text{NC induct}.\exists !\text{ sm }_{\xi }ʻʻ\gamma .\gamma \geq \nu .\supset .\alpha +_{c}\gamma =(\alpha +_{c}\nu )+_{c}(\gamma -_{c}\nu )_{\xi }\\ &[*120·4111.*119·35]\end{align}\]

PM's cardinal `α` is `μ`; `α +_c ν` is in an adequate type `W` (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
arithmetical component `α +_c ν` is adequate. -/
theorem pm120_418 {α γ β W T E : Type*} {μ : Set (Set α)} {G : Set (Set γ)} {ν : Set (Set β)}
    (hW : AdeqAdd W μ ν) :
    (ν ∈ NCinduct ∧ (sm ʻʻ G : Set (Set T)).Nonempty) ∧ G ≥ᶜ ν →
      (μ +ᶜ G : Set (Set E)) =
        ((μ +ᶜ ν : Set (Set W)) +ᶜ (G -ᶜ ν : Set (Set T)) : Set (Set E)) := by
  rintro ⟨⟨hν, hG⟩, hge⟩
  obtain ⟨X, hX⟩ := sub_mem_N₀C_of_ge hν hge hG
  have hXm : X ∈ (G -ᶜ ν : Set (Set T)) := hX ▸ self_mem_n₀c X
  obtain ⟨A, B, ⟨rfl, rfl⟩, ⟨e⟩⟩ := mem_cardSub.1 hXm
  rw [hX]
  by_cases hμ : ∃ M, μ = n₀c M
  · obtain ⟨M, rfl⟩ := hμ
    rw [cardAdd_n₀c, cardAdd_n₀c, n₀c_eq_ncT X, cardAdd_ncT (adeqAdd_emb hW M B) (emb_self X)]
    exact ncT_congr (((Equiv.refl _).sumCongr (e.symm.trans (Equiv.sumComm _ _))).trans
      (Equiv.sumAssoc _ _ _).symm)
  · push Not at hμ
    simp only [cardAdd_eq_empty_of_left hμ, cardAdd_empty_left]

/-- ✱120·42. \(\vdash :\nu \in \text{NC induct}.\exists !\nu .\alpha \neq 0.\supset .\nu \neq \alpha +_{c}\nu \)

The sides of `≠` are in the type of `ν`; PM's `α` is `μ`. -/
theorem pm120_42 {α β : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (ν ∈ NCinduct ∧ ν.Nonempty) ∧ μ ≠ zero → ν ≠ (μ +ᶜ ν : Set (Set β)) := by
  rintro ⟨⟨hν, hne⟩, h0⟩ heq
  rcases NCinduct_cases hν with ⟨N, hN, rfl⟩ | ⟨-, rfl⟩
  · have hN' : N ∈ (μ +ᶜ n₀c N : Set (Set β)) := heq ▸ self_mem_n₀c N
    obtain ⟨M, N', ⟨rfl, h1⟩, ⟨e⟩⟩ := mem_cardAdd'.1 hN'
    obtain ⟨eN⟩ := eq_n₀c_iff_equiv.1 h1
    obtain ⟨m⟩ := nonempty_of_n₀c_ne_zero h0
    have : Finite ↥N := hN.to_subtype
    have : Finite ↥N' := Finite.of_equiv _ eN
    have : Finite ↥M := Finite.of_injective (fun x => e.symm (Sum.inl x))
      (fun x y h => Sum.inl_injective (e.symm.injective h))
    have k := Nat.card_congr e
    rw [Nat.card_sum, ← Nat.card_congr eN] at k
    have : Nonempty ↥M := ⟨m⟩
    have : 0 < Nat.card ↥M := Nat.card_pos (α := ↥M)
    omega
  · exact absurd hne Set.not_nonempty_empty

/-- ✱120·422. \(\vdash :\alpha +_{c}1\in \text{NC induct}-\iota ʻ\Lambda .\supset .\alpha \in \text{NC induct}-\iota ʻ\Lambda\)

The `1` is in the type of `α`, the sum in any type `T`. -/
theorem pm120_422 {α T : Type*} {μ : Set (Set α)} :
    (μ +ᶜ (one : Set (Set α)) : Set (Set T)) ∈ NCinduct \ ι Λ → μ ∈ NCinduct \ ι Λ := by
  rintro ⟨h1, h2⟩
  have hne : (μ +ᶜ (one : Set (Set α)) : Set (Set T)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ← Null_eq_empty]; exact h2
  obtain ⟨A, O, ⟨rfl, hO⟩, hT⟩ := cardAdd_nonempty_iff.1 hne
  rw [hO, cardAdd_n₀c] at h1
  have hfin := (ncT_mem_NCinduct_iff hT).1 h1
  refine ⟨n₀c_mem_NCinduct (Set.finite_coe_iff.1 (Finite.of_injective (fun a => (Sum.inl a :
    ↥A ⊕ ↥O)) Sum.inl_injective)), ?_⟩
  show ¬ n₀c A = Λ
  rw [Null_eq_empty]; exact n₀c_ne_empty A

/-- ✱120·423. \(\vdash :\alpha \in \text{N}_{\eta }\text{C induct}-\iota ʻ0.\equiv .(\exists \beta ).\beta \in \text{N}_{\eta }\text{C induct}.\alpha =(\beta +_{c}1)_{\eta }\) -/
theorem pm120_423 {α : Type*} {η : Set α} {μ : Set (Set α)} :
    μ ∈ NCinductAt η \ ι zero ↔
      ∃ ν : Set (Set α), ν ∈ NCinductAt η ∧ μ = (ν +ᶜ (one : Set (Set α)) : Set (Set α)) := by
  rw [NCinductAt_eq]
  constructor
  · rintro ⟨h, h0⟩
    rcases Relation.ReflTransGen.cases_head (mem_NCinduct_iff.1 h) with h' | ⟨c, hc, hc'⟩
    · exact absurd h' h0
    · exact ⟨c, mem_NCinduct_iff.2 hc', plusC1_iff.1 hc⟩
  · rintro ⟨ν, hν, rfl⟩
    exact ⟨cardAdd_one_mem_NCinduct hν, pm120_124⟩

/-- ✱120·4231. \(\vdash :\alpha \in \text{N}_{\eta }\text{C induct}.\supset .(\exists \beta ).\beta \in \text{N}_{\eta }\text{C induct}-\iota ʻ\Lambda .(\alpha +_{c}1)_{\eta }=(\beta +_{c} 1)_{\eta }\) -/
theorem pm120_4231 {α : Type*} {η : Set α} {μ : Set (Set α)} :
    μ ∈ NCinductAt η → ∃ ν : Set (Set α), ν ∈ NCinductAt η \ ι Λ ∧
      (μ +ᶜ (one : Set (Set α)) : Set (Set α)) = (ν +ᶜ (one : Set (Set α)) : Set (Set α)) := by
  rw [NCinductAt_eq]
  intro h
  rcases NCinduct_cases h with ⟨A, hA, rfl⟩ | ⟨hf, rfl⟩
  · refine ⟨n₀c A, ⟨h, ?_⟩, rfl⟩
    show ¬ n₀c A = Λ
    rw [Null_eq_empty]; exact n₀c_ne_empty A
  · refine ⟨n₀c Set.univ, ⟨n₀c_mem_NCinduct Set.finite_univ, ?_⟩, ?_⟩
    · show ¬ n₀c Set.univ = Λ
      rw [Null_eq_empty]; exact n₀c_ne_empty _
    · rw [cardAdd_empty_left, n₀c_univ_cardAdd_one]

/-- ✱120·4232. \[\begin{align}&\vdash :\alpha \in \text{N}_{\eta }\text{C induct}-\iota ʻ0.\equiv .(\exists \beta ).\beta \in \text{N}_{\eta }\text{C induct}-\iota ʻ\Lambda .\alpha =(\beta +_{c}1)_{\eta }\\ &[*120·423·4231]\end{align}\] -/
theorem pm120_4232 {α : Type*} {η : Set α} {μ : Set (Set α)} :
    μ ∈ NCinductAt η \ ι zero ↔
      ∃ ν : Set (Set α), ν ∈ NCinductAt η \ ι Λ ∧
        μ = (ν +ᶜ (one : Set (Set α)) : Set (Set α)) := by
  rw [pm120_423]
  constructor
  · rintro ⟨ν, hν, rfl⟩
    obtain ⟨ν', hν', e⟩ := pm120_4231 hν
    exact ⟨ν', hν', e⟩
  · rintro ⟨ν, hν, rfl⟩
    exact ⟨ν, hν.1, rfl⟩

/-- ✱120·424. \(\vdash :\beta \neq 0.\exists !(\alpha +_{c}\beta )_{\xi }.\supset .(\alpha +_{c}\beta )_{\xi }-_{c}1=\alpha +_{c}(\beta -_{c}1)_{\xi }\)

PM's cardinals `α`, `β` are `μ`, `ρ`. The `1` of `(α +_c β)_ξ −_c 1` is in the type `T` of `ξ`,
that of `β −_c 1` in the type of `β`; the two sides of the equation are in one type `E`. -/
theorem pm120_424 {α β T E : Type*} {μ : Set (Set α)} {ρ : Set (Set β)} :
    ρ ≠ zero ∧ (μ +ᶜ ρ : Set (Set T)).Nonempty →
      ((μ +ᶜ ρ : Set (Set T)) -ᶜ (one : Set (Set T)) : Set (Set E)) =
        (μ +ᶜ (ρ -ᶜ (one : Set (Set β)) : Set (Set T)) : Set (Set E)) := by
  rintro ⟨h0, hne⟩
  obtain ⟨M, B, ⟨rfl, rfl⟩, ⟨fT⟩⟩ := cardAdd_nonempty_iff.1 hne
  obtain ⟨b⟩ := nonempty_of_n₀c_ne_zero h0
  have eB := equiv_diff_singleton b.2
  obtain ⟨S, hS⟩ := hne
  rw [cardAdd_n₀c] at hS
  have hsum : (n₀c M +ᶜ n₀c B : Set (Set T)) = n₀c S := by
    rw [cardAdd_n₀c]; exact ncT_eq_n₀c_of_mem hS
  obtain ⟨eS⟩ := hS
  have hfit : Nonempty (↥(B \ {(b : β)}) ↪ T) :=
    ⟨(Function.Embedding.inl.trans eB.symm.toEmbedding).trans (Function.Embedding.inr.trans fT)⟩
  rw [hsum, sub_one_eq (eS.trans (((Equiv.refl _).sumCongr eB).trans (Equiv.sumAssoc _ _ _).symm)),
    sub_one_eq eB, n₀c_eq_ncT M, cardAdd_ncT (emb_self M) hfit]

/-- ✱120·425. \[\begin{align}\vdash \colon\ldotp &(\alpha +_{c}\beta )_{\xi }\in \text{N}_{0}\text{C}-\iota ʻ0.\supset :\\ &(\alpha +_{c}\beta )_{\xi }-_{c}1=\alpha +_{c}(\beta -_{c}1)_{\xi }.\lor.(\alpha +_{c}\beta )_{\xi }-_{c}1=(\alpha -_{c}1)_{\xi }+_{c}\beta \end{align}\] -/
theorem pm120_425 {α β T E : Type*} {μ : Set (Set α)} {ρ : Set (Set β)} :
    (μ +ᶜ ρ : Set (Set T)) ∈ N₀C \ ι zero →
      ((μ +ᶜ ρ : Set (Set T)) -ᶜ (one : Set (Set T)) : Set (Set E)) =
          (μ +ᶜ (ρ -ᶜ (one : Set (Set β)) : Set (Set T)) : Set (Set E)) ∨
        ((μ +ᶜ ρ : Set (Set T)) -ᶜ (one : Set (Set T)) : Set (Set E)) =
          ((μ -ᶜ (one : Set (Set α)) : Set (Set T)) +ᶜ ρ : Set (Set E)) := by
  rintro ⟨⟨S₀, hS₀⟩, h0⟩
  have hne : (μ +ᶜ ρ : Set (Set T)).Nonempty := by rw [hS₀]; exact n₀c_nonempty S₀
  obtain ⟨M, B, ⟨rfl, rfl⟩, ⟨fT⟩⟩ := cardAdd_nonempty_iff.1 hne
  by_cases hB : B.Nonempty
  · refine Or.inl (pm120_424 ⟨fun h => ?_, hne⟩)
    obtain ⟨b, hb⟩ := hB
    rw [n₀c_eq_zero_iff] at h
    rw [h] at hb; exact hb
  · right
    rw [Set.not_nonempty_iff_eq_empty] at hB
    subst hB
    have hM : M.Nonempty := by
      by_contra hM
      rw [Set.not_nonempty_iff_eq_empty] at hM
      subst hM
      apply h0
      show _ = zero
      rw [cardAdd_n₀c, zero_eq_ncT.{_, 0}]
      exact ncT_congr ((Equiv.sumEmpty _ _).trans (Equiv.equivOfIsEmpty _ _))
    obtain ⟨m, hm⟩ := hM
    have eM := equiv_diff_singleton hm
    obtain ⟨S, hS⟩ := hne
    rw [cardAdd_n₀c] at hS
    have hsum : (n₀c M +ᶜ n₀c (∅ : Set β) : Set (Set T)) = n₀c S := by
      rw [cardAdd_n₀c]; exact ncT_eq_n₀c_of_mem hS
    obtain ⟨eS⟩ := hS
    have hfit : Nonempty (↥(M \ {m}) ↪ T) :=
      ⟨(Function.Embedding.inl.trans eM.symm.toEmbedding).trans (Function.Embedding.inl.trans fT)⟩
    rw [hsum, sub_one_eq (eS.trans ((eM.sumCongr (Equiv.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans (((Equiv.refl _).sumCongr (Equiv.sumComm _ _)).trans
        (Equiv.sumAssoc _ _ _).symm)))), sub_one_eq eM, n₀c_eq_ncT (∅ : Set β),
      cardAdd_ncT hfit (emb_self _)]

/-- `ρ` finite, `ρ ⊂ σ`, `σ − ρ` existent: `σ` cannot be embedded in `ρ`. -/
private theorem not_emb_of_finite_ssubset {α : Type*} {ρ σ : Set α} (hρ : ρ.Finite)
    (hsub : ρ ⊆ σ) (hne : (σ \ ρ).Nonempty) : ¬ Nonempty (↥σ ↪ ↥ρ) := by
  rintro ⟨f⟩
  have : Finite ↥ρ := hρ.to_subtype
  have hσ : Finite ↥σ := Finite.of_injective f f.injective
  have h1 := Finite.card_le_of_embedding f
  have hss : ρ ⊂ σ := Set.ssubset_iff_subset_ne.2 ⟨hsub, fun h => by
    obtain ⟨x, hx1, hx2⟩ := hne; exact hx2 (h ▸ hx1)⟩
  have h2 := Set.ncard_lt_ncard hss (Set.finite_coe_iff.1 hσ)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h2
  omega

/-- ✱120·426. \(\vdash :\rho \in \text{Cls induct}.\rho \subset \sigma .\exists !\sigma -\rho .\supset .{\sim}(\rho \text{ sm }\sigma ).\text{Nc}ʻ\rho <\text{Nc}ʻ\sigma\)

**Status.** proved (reading): the sides `Nc'ρ`, `Nc'σ` of `<` are `N₀c'ρ`, `N₀c'σ` (✱117·02·03
and the note to ✱117·06, normal adjustment). -/
theorem pm120_426 {α : Type*} {ρ σ : Set α} :
    (ρ ∈ ClsInduct ∧ ρ ⊆ σ) ∧ (σ \ ρ).Nonempty → ¬ sm ρ σ ∧ n₀c ρ <ᶜ n₀c σ := by
  rintro ⟨⟨hρ, hsub⟩, hne⟩
  have hn := not_emb_of_finite_ssubset (mem_ClsInduct.1 hρ) hsub hne
  refine ⟨fun h => hn ?_, cardGt_n₀c.2 ⟨⟨⟨Set.inclusion hsub, Set.inclusion_injective hsub⟩⟩, hn⟩⟩
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
  exact ⟨e.symm.toEmbedding⟩

/-- ✱120·427. \[\begin{align}&\vdash :R\in 1\rightarrow 1.\text{ᗡ}ʻR\subset \text{D}ʻR.\exists !\text{D}ʻR-\text{ᗡ}ʻR.\supset .\text{D}ʻR{\sim}\in \text{Cls induct}\\ &[*120·426.\text{Transp}]\end{align}\]

"No reflexive class is inductive" (PM). -/
theorem pm120_427 {α : Type*} {R : α → α → Prop} :
    (R ∈ arrow one one ∧ codom R ⊆ dom R) ∧ (dom R \ codom R).Nonempty → dom R ∉ ClsInduct := by
  rintro ⟨⟨hR, hsub⟩, hne⟩ hD
  have hC : codom R ∈ ClsInduct := mem_ClsInduct.2 ((mem_ClsInduct.1 hD).subset hsub)
  exact (pm120_426 ⟨⟨hC, hsub⟩, hne⟩).1 (sm_symm ⟨R, ⟨hR, rfl⟩, rfl⟩)

/-- ✱120·428. \(\vdash :\nu \in \text{NC induct}.\exists !\alpha +_{c}\nu .\alpha \neq 0.\supset .\alpha +_{c}\nu >\nu \)

PM's `α` is `μ`. The logical occurrence of `α +_c ν` (in `∃!`) is in a free type `D`; its
occurrence as a side of `>` is arithmetical, in an adequate type `W` (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
arithmetical occurrence of `α +_c ν` is adequate. -/
theorem pm120_428 {α β D W : Type*} {μ : Set (Set α)} {ν : Set (Set β)} (hW : AdeqAdd W μ ν) :
    (ν ∈ NCinduct ∧ (μ +ᶜ ν : Set (Set D)).Nonempty) ∧ μ ≠ zero →
      (μ +ᶜ ν : Set (Set W)) >ᶜ ν := by
  rintro ⟨⟨hν, hne⟩, h0⟩
  obtain ⟨M, N, ⟨rfl, rfl⟩, -⟩ := cardAdd_nonempty_iff.1 hne
  obtain ⟨S, hS⟩ := ncT_nonempty_iff.2 (adeqAdd_emb hW M N)
  rw [cardAdd_n₀c, ncT_eq_n₀c_of_mem hS]
  obtain ⟨e⟩ := hS
  obtain ⟨m⟩ := nonempty_of_n₀c_ne_zero h0
  have : Finite ↥N := (n₀c_mem_NCinduct_iff.1 hν).to_subtype
  refine cardGt_n₀c.2 ⟨⟨Function.Embedding.inr.trans e.symm.toEmbedding⟩, fun ⟨g⟩ => ?_⟩
  have : Finite ↥M := Finite.of_injective (fun x => g (e.symm (Sum.inl x)))
    (fun x y h => Sum.inl_injective (e.symm.injective (g.injective h)))
  have k := Finite.card_le_of_embedding (e.symm.toEmbedding.trans g)
  rw [Nat.card_sum] at k
  have : Nonempty ↥M := ⟨m⟩
  have : 0 < Nat.card ↥M := Nat.card_pos
  omega

/-- ✱120·429. \(\vdash \colon\ldotp \nu \in \text{NC induct}.\supset :\mu >\nu .\equiv .\mu \geq \nu +_{c}1\)

`ν +_c 1` (a side of `≥`, an arithmetical occurrence) is in an adequate type `W` (IIT), its `1` in
the type of `ν`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of
`ν +_c 1` is adequate; PM assumes every type has a member (Introduction, Ch. I): `[Nonempty β]`
(otherwise `1 = Λ` in the type of `ν`). -/
theorem pm120_429 {α β W : Type*} [Nonempty β] {μ : Set (Set α)} {ν : Set (Set β)}
    (hW : AdeqAdd W ν (one : Set (Set β))) :
    ν ∈ NCinduct → (μ >ᶜ ν ↔ μ ≥ᶜ (ν +ᶜ (one : Set (Set β)) : Set (Set W))) := by
  intro hν
  rcases NCinduct_cases hν with ⟨N, hN, rfl⟩ | ⟨-, rfl⟩
  · have : Finite ↥N := hN.to_subtype
    let y : β := Classical.arbitrary β
    obtain ⟨S, hS⟩ := ncT_nonempty_iff.2 (adeqAdd_emb hW N {y})
    rw [one_eq_n₀c_singleton y, cardAdd_n₀c, ncT_eq_n₀c_of_mem hS]
    obtain ⟨e⟩ := hS
    have e' : ↥S ≃ ↥N ⊕ PUnit.{1} := e.trans ((Equiv.refl _).sumCongr (Equiv.ofUnique _ _))
    constructor
    · intro h
      obtain ⟨A, B, ⟨rfl, hB⟩, h1, h2⟩ := cardGt_iff.1 h
      obtain ⟨fB⟩ := eq_n₀c_iff_equiv.1 hB
      have := (emb_sum_unit_iff (N := ↥N) (M := ↥A)).2
        ⟨(emb_congr fB (Equiv.refl _)).2 h1, fun hg => h2 ((emb_congr (Equiv.refl _) fB).1 hg)⟩
      exact cardGe_n₀c.2 ((emb_congr e'.symm (Equiv.refl _)).1 this)
    · intro h
      obtain ⟨A, B, ⟨rfl, hB⟩, h1⟩ := cardGe_iff.1 h
      obtain ⟨fB⟩ := eq_n₀c_iff_equiv.1 hB
      obtain ⟨h1', h2'⟩ := (emb_sum_unit_iff (N := ↥N) (M := ↥A)).1
        ((emb_congr (fB.symm.trans e') (Equiv.refl _)).1 h1)
      exact cardGt_n₀c.2 ⟨h1', h2'⟩
  · rw [cardAdd_empty_left]
    constructor
    · rintro ⟨A, B, ⟨⟨-, hB⟩, -⟩, -⟩; exact absurd hB.symm (n₀c_ne_empty B)
    · intro h
      obtain ⟨A, B, ⟨-, hB⟩, -⟩ := cardGe_iff.1 h
      exact absurd hB.symm (n₀c_ne_empty B)

/-- ✱120·43 (Df). \(\text{spec}ʻ\beta =\hat{\alpha} \{\alpha <\beta .\lor.\alpha \geq \beta\} \quad\text{Df}\) -/
theorem pm120_43 {α β : Type*} {B : Set (Set β)} :
    (spec B : Set (Set (Set α))) = {μ | μ <ᶜ B ∨ μ ≥ᶜ B} :=
  rfl

/-- ✱120·431. \(\vdash \colon\ldotp \alpha \in \text{spec}ʻ\beta .\equiv :\alpha <\beta .\lor.\alpha \geq \beta \quad[(*120·43)]\) -/
theorem pm120_431 {α β : Type*} {μ : Set (Set α)} {B : Set (Set β)} :
    μ ∈ (spec B : Set (Set (Set α))) ↔ μ <ᶜ B ∨ μ ≥ᶜ B :=
  Iff.rfl

private theorem cardLt_iff {α β : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ <ᶜ ν ↔ ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧
      (Nonempty (↥A ↪ ↥B) ∧ ¬ Nonempty (↥B ↪ ↥A)) := by
  show ν >ᶜ μ ↔ _
  rw [cardGt_iff]
  exact ⟨fun ⟨B, A, ⟨h1, h2⟩, h⟩ => ⟨A, B, ⟨h2, h1⟩, h⟩, fun ⟨A, B, ⟨h1, h2⟩, h⟩ =>
    ⟨B, A, ⟨h2, h1⟩, h⟩⟩

private theorem cardLe_iff {α β : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ≤ᶜ ν ↔ ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ Nonempty (↥A ↪ ↥B) := by
  show ν ≥ᶜ μ ↔ _
  rw [cardGe_iff]
  exact ⟨fun ⟨B, A, ⟨h1, h2⟩, h⟩ => ⟨A, B, ⟨h2, h1⟩, h⟩, fun ⟨A, B, ⟨h1, h2⟩, h⟩ =>
    ⟨B, A, ⟨h2, h1⟩, h⟩⟩

/-- ✱120·432. \(\vdash \colon\ldotp \alpha \in \text{spec}ʻ\beta .\equiv :\alpha \leq \beta .\lor.\alpha \geq \beta \quad[*117·281.*120·431]\) -/
theorem pm120_432 {α β : Type*} {μ : Set (Set α)} {B : Set (Set β)} :
    μ ∈ (spec B : Set (Set (Set α))) ↔ μ ≤ᶜ B ∨ μ ≥ᶜ B := by
  rw [pm120_431, cardLt_iff, cardLe_iff, cardGe_iff]
  constructor
  · rintro (⟨A, B', hAB, h, -⟩ | h)
    · exact Or.inl ⟨A, B', hAB, h⟩
    · exact Or.inr h
  · rintro (⟨A, B', hAB, h⟩ | h)
    · by_cases h' : Nonempty (↥B' ↪ ↥A)
      · exact Or.inr ⟨A, B', hAB, h'⟩
      · exact Or.inl ⟨A, B', hAB, h, h'⟩
    · exact Or.inr h

/-- Any two homogeneous cardinals are comparable (by choice). -/
private theorem mem_spec_of_N₀C {α β : Type*} {μ : Set (Set α)} {B : Set (Set β)}
    (hμ : μ ∈ N₀C) (hB : B ∈ N₀C) : μ ∈ (spec B : Set (Set (Set α))) := by
  obtain ⟨A, rfl⟩ := hμ
  obtain ⟨B', rfl⟩ := hB
  rw [pm120_432]
  rcases Function.Embedding.total ↥A ↥B' with h | h
  · exact Or.inl (cardGe_n₀c.2 h)
  · exact Or.inr (cardGe_n₀c.2 h)

/-- ✱120·433. \[\begin{align}&\vdash \colon\ldotp \text{Nc}ʻ\rho \in \text{spec}ʻ\text{Nc}ʻ\sigma .\equiv :\exists !\text{Cl}ʻ\rho \cap \text{Nc}ʻ\sigma .\lor.\exists !\text{Cl}ʻ\sigma \cap \text{Nc}ʻ\rho \\ &[*117·22.*120·432]\end{align}\]

`spec'β` is defined by the inequalities `α < β`, `α ≥ β`, whose sides `Nc'ρ`, `Nc'σ` are
`N₀c'ρ`, `N₀c'σ` (✱117·02·03); in `Cl'ρ ∩ Nc'σ` the `Nc'σ` is in the type of `ρ` (significance).

**Status.** proved (reading): the occurrences of `Nc'ρ`, `Nc'σ` in `Nc'ρ ∈ spec'Nc'σ` are read
`N₀c'ρ`, `N₀c'σ`, as the sides of the inequalities defining `spec` (✱117·02·03, normal
adjustment). -/
theorem pm120_433 {α β : Type*} {ρ : Set α} {σ : Set β} :
    n₀c ρ ∈ (spec (n₀c σ) : Set (Set (Set α))) ↔
      (cl ρ ∩ nc α σ).Nonempty ∨ (cl σ ∩ nc β ρ).Nonempty := by
  rw [pm120_432, cl_inter_nc_nonempty, cl_inter_nc_nonempty]
  show n₀c σ ≥ᶜ n₀c ρ ∨ n₀c ρ ≥ᶜ n₀c σ ↔ _
  rw [cardGe_n₀c, cardGe_n₀c]
  exact Or.comm

/-- ✱120·434. \(\vdash .\text{spec}ʻ\beta \subset \text{N}_{0}\text{C} \quad[*117·105·104·12.*120·432]\) -/
theorem pm120_434 {α β : Type*} {B : Set (Set β)} :
    (spec B : Set (Set (Set α))) ⊆ N₀C := by
  intro μ h
  rw [pm120_432, cardLe_iff, cardGe_iff] at h
  rcases h with ⟨A, -, ⟨rfl, -⟩, -⟩ | ⟨A, -, ⟨rfl, -⟩, -⟩ <;> exact n₀c_mem_N₀C A

private theorem N₀C_of_mem_spec {α β : Type*} {μ : Set (Set α)} {B : Set (Set β)}
    (h : μ ∈ (spec B : Set (Set (Set α)))) : B ∈ N₀C := by
  rw [pm120_432, cardLe_iff, cardGe_iff] at h
  rcases h with ⟨-, B', ⟨-, rfl⟩, -⟩ | ⟨-, B', ⟨-, rfl⟩, -⟩ <;> exact n₀c_mem_N₀C B'

/-- ✱120·437. \(\vdash :\beta \in \text{N}_{0}\text{C}.\supset .0\in \text{spec}ʻ\beta \quad[*117·5.*120·432]\) -/
theorem pm120_437 {α β : Type*} {B : Set (Set β)} :
    B ∈ N₀C → (zero : Set (Set α)) ∈ (spec B : Set (Set (Set α))) := by
  intro hB
  rw [zero_eq_n₀c_empty]
  exact mem_spec_of_N₀C (n₀c_mem_N₀C _) hB

/-- ✱120·435. \(\vdash :\beta \in \text{N}_{0}\text{C}.\equiv .\beta \in \text{spec}ʻ\beta .\equiv .\exists !\text{spec}ʻ\beta \quad[*117·104.*120·434]\)

In `β ∈ spec'β` the members of `spec'β` are in the type of `β`; in `∃!spec'β` their type `α'` is
free. -/
theorem pm120_435 {α α' : Type*} {B : Set (Set α)} :
    (B ∈ N₀C ↔ B ∈ (spec B : Set (Set (Set α)))) ∧
      (B ∈ (spec B : Set (Set (Set α))) ↔ (spec B : Set (Set (Set α'))).Nonempty) := by
  refine ⟨⟨fun h => mem_spec_of_N₀C h h, fun h => pm120_434 h⟩, ⟨fun h => ?_, fun ⟨μ, hμ⟩ => ?_⟩⟩
  · exact ⟨zero, pm120_437 (N₀C_of_mem_spec h)⟩
  · have hB := N₀C_of_mem_spec hμ
    exact mem_spec_of_N₀C hB hB

/-- ✱120·436. \[\begin{align}&\vdash \colon\ldotp \alpha \in \text{spec}ʻ\beta .\equiv :\alpha ,\beta \in \text{N}_{0}\text{C}:(\exists \gamma ):\alpha +_{c}\gamma =\beta .\lor.\beta +_{c}\gamma =\alpha \\ &[*120·432 . *117·31]\end{align}\]

`α +_c γ = β` is in the type of `β`, `β +_c γ = α` in that of `α`. The apparent variable `γ`, an
argument of `+_c`, ranges over the cardinals of a type `Γ` taken adequate: the types of the members
of `α` and `β` inject into it.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV) applied to the arithmetical
apparent variable `γ`: its type `Γ` is one into which the types of the members of `α` and `β`
inject (in a smaller type the right side can fail). -/
theorem pm120_436 {α β Γ : Type*} (hΓ : Nonempty (α ↪ Γ) ∧ Nonempty (β ↪ Γ))
    {μ : Set (Set α)} {B : Set (Set β)} :
    μ ∈ (spec B : Set (Set (Set α))) ↔
      (μ ∈ N₀C ∧ B ∈ N₀C) ∧
        ∃ G : Set (Set Γ), (μ +ᶜ G : Set (Set β)) = B ∨ (B +ᶜ G : Set (Set α)) = μ := by
  obtain ⟨⟨fα⟩, ⟨fβ⟩⟩ := hΓ
  constructor
  · intro h
    have hμ := pm120_434 h
    have hB := N₀C_of_mem_spec h
    refine ⟨⟨hμ, hB⟩, ?_⟩
    obtain ⟨A, rfl⟩ := hμ
    obtain ⟨B', rfl⟩ := hB
    rcases Function.Embedding.total ↥A ↥B' with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · obtain ⟨D, -, ⟨e⟩⟩ := exists_compl_of_emb f
      obtain ⟨D', ⟨eD⟩⟩ := ncT_nonempty_iff.2
        (⟨(setEmb D).trans fβ⟩ : Nonempty (↥D ↪ Γ))
      refine ⟨n₀c D', Or.inl ?_⟩
      rw [cardAdd_n₀c, n₀c_eq_ncT B']
      exact ncT_congr (((Equiv.refl _).sumCongr eD).trans ((Equiv.sumComm _ _).trans e))
    · obtain ⟨D, -, ⟨e⟩⟩ := exists_compl_of_emb f
      obtain ⟨D', ⟨eD⟩⟩ := ncT_nonempty_iff.2
        (⟨(setEmb D).trans fα⟩ : Nonempty (↥D ↪ Γ))
      refine ⟨n₀c D', Or.inr ?_⟩
      rw [cardAdd_n₀c, n₀c_eq_ncT A]
      exact ncT_congr (((Equiv.refl _).sumCongr eD).trans ((Equiv.sumComm _ _).trans e))
  · rintro ⟨⟨⟨A, rfl⟩, ⟨B', rfl⟩⟩, G, h | h⟩
    · have hB' : B' ∈ (n₀c A +ᶜ G : Set (Set β)) := h ▸ self_mem_n₀c B'
      obtain ⟨A₁, D, ⟨hA, -⟩, ⟨e⟩⟩ := mem_cardAdd'.1 hB'
      obtain ⟨eA⟩ := eq_n₀c_iff_equiv.1 hA
      rw [pm120_432]
      exact Or.inl (cardGe_n₀c.2 ⟨eA.toEmbedding.trans (Function.Embedding.inl.trans
        e.symm.toEmbedding)⟩)
    · have hA' : A ∈ (n₀c B' +ᶜ G : Set (Set α)) := h ▸ self_mem_n₀c A
      obtain ⟨B₁, D, ⟨hB, -⟩, ⟨e⟩⟩ := mem_cardAdd'.1 hA'
      obtain ⟨eB⟩ := eq_n₀c_iff_equiv.1 hB
      rw [pm120_432]
      exact Or.inr (cardGe_n₀c.2 ⟨eB.toEmbedding.trans (Function.Embedding.inl.trans
        e.symm.toEmbedding)⟩)

/-- ✱120·438. \(\vdash :\alpha \in \text{spec}ʻ\beta .\exists !\alpha +_{c}1.\supset .\alpha +_{c}1\in \text{spec}ʻ\beta\)

The two (logical) occurrences of `α +_c 1` are in one type `T` (IT); its `1` is in the type of
`α`.

**Status.** proved (reading): convention IT (Prefatory Statement, IV) binds the two logical
occurrences of `α +_c 1`. -/
theorem pm120_438 {α β T : Type*} {μ : Set (Set α)} {B : Set (Set β)} :
    μ ∈ (spec B : Set (Set (Set α))) ∧ (μ +ᶜ (one : Set (Set α)) : Set (Set T)).Nonempty →
      (μ +ᶜ (one : Set (Set α)) : Set (Set T)) ∈ (spec B : Set (Set (Set T))) := by
  rintro ⟨h, ⟨ξ, hξ⟩⟩
  have hN : (μ +ᶜ (one : Set (Set α)) : Set (Set T)) ∈ N₀C := by
    obtain ⟨A, O, ⟨rfl, hO⟩, -⟩ := cardAdd_nonempty_iff.1 ⟨ξ, hξ⟩
    rw [hO, cardAdd_n₀c] at hξ ⊢
    exact ⟨ξ, ncT_eq_n₀c_of_mem hξ⟩
  exact mem_spec_of_N₀C hN (N₀C_of_mem_spec h)

/-- ✱120·44. \(\vdash :\beta \in \text{N}_{0}\text{C}.\supset .\text{NC induct}-\iota ʻ\Lambda \subset \text{spec}ʻ\beta\) -/
theorem pm120_44 {α β : Type*} {B : Set (Set β)} :
    B ∈ N₀C → (NCinduct \ ι Λ : Set (Set (Set α))) ⊆ spec B := by
  rintro hB μ ⟨h1, h2⟩
  rcases NCinduct_cases h1 with ⟨A, -, rfl⟩ | ⟨-, rfl⟩
  · exact mem_spec_of_N₀C (n₀c_mem_N₀C A) hB
  · exact absurd (Null_eq_empty).symm h2

private theorem NC_ne_empty_N₀C {α β : Type*} {μ : Set (Set α)} (h : μ ∈ NC β \ ι Λ) :
    ∃ A, μ = n₀c A := by
  rcases NC_cases h.1 with h' | h'
  · exact absurd (h'.trans Null_eq_empty.symm) h.2
  · exact h'

/-- ✱120·441. \[\begin{align}&\vdash \colon\ldotp \alpha \in \text{NC induct}-\iota ʻ\Lambda .\beta \in \text{NC}-\iota ʻ\Lambda .\supset :\alpha \beta \\ &[*120·44.*103·34]\end{align}\]

The data file has lost the text between `α` and `β` (read as an HTML tag); the proposition printed
in the source is `α < β . ∨ . α = sm''β . ∨ . α > β` (a sum of three, bracketed to the left).

**Status.** proved (reading): transcription error (the conclusion is
`α < β . ∨ . α = sm''β . ∨ . α > β`, as in the Gutenberg source). -/
theorem pm120_441 {α β Y : Type*} {μ : Set (Set α)} {B : Set (Set β)} :
    μ ∈ NCinduct \ ι Λ ∧ B ∈ NC Y \ ι Λ →
      (μ <ᶜ B ∨ μ = (sm ʻʻ B : Set (Set α))) ∨ μ >ᶜ B := by
  rintro ⟨hμ, hB⟩
  obtain ⟨A, rfl⟩ := NC_ne_empty_N₀C ⟨pm120_14 hμ.1, hμ.2⟩
  obtain ⟨B', rfl⟩ := NC_ne_empty_N₀C hB
  by_cases h1 : Nonempty (↥A ↪ ↥B')
  · by_cases h2 : Nonempty (↥B' ↪ ↥A)
    · obtain ⟨f⟩ := h1; obtain ⟨g⟩ := h2
      obtain ⟨e⟩ := Function.Embedding.antisymm f g
      refine Or.inl (Or.inr ?_)
      rw [sm_img_n₀c', n₀c_eq_ncT]; exact ncT_congr e
    · exact Or.inl (Or.inl (cardGt_n₀c.2 ⟨h1, h2⟩))
  · rcases Function.Embedding.total ↥A ↥B' with h | h
    · exact absurd h h1
    · exact Or.inr (cardGt_n₀c.2 ⟨h, h1⟩)

/-- ✱120·442. \[\begin{align}\vdash \colon\ldotp \alpha \in \text{NC induct}&-\iota ʻ\Lambda .\beta \in \text{NC}-\iota ʻ\Lambda .\supset :\\ &\alpha \beta .\equiv .{\sim}(\alpha \leq \beta )\end{align}\]

The data file has lost the text between `α` and `β`; the proposition printed in the source is
`α < β . ≡ . ∼(α ≥ β) : α > β . ≡ . ∼(α ≤ β)`.

**Status.** proved (reading): transcription error (the conclusion is
`α < β . ≡ . ∼(α ≥ β) : α > β . ≡ . ∼(α ≤ β)`, as in the Gutenberg source). -/
theorem pm120_442 {α β Y : Type*} {μ : Set (Set α)} {B : Set (Set β)} :
    μ ∈ NCinduct \ ι Λ ∧ B ∈ NC Y \ ι Λ →
      ((μ <ᶜ B ↔ ¬ μ ≥ᶜ B) ∧ (μ >ᶜ B ↔ ¬ μ ≤ᶜ B)) := by
  rintro ⟨hμ, hB⟩
  obtain ⟨A, rfl⟩ := NC_ne_empty_N₀C ⟨pm120_14 hμ.1, hμ.2⟩
  obtain ⟨B', rfl⟩ := NC_ne_empty_N₀C hB
  show (n₀c B' >ᶜ n₀c A ↔ ¬ n₀c A ≥ᶜ n₀c B') ∧ (n₀c A >ᶜ n₀c B' ↔ ¬ n₀c B' ≥ᶜ n₀c A)
  rw [cardGt_n₀c, cardGt_n₀c, cardGe_n₀c, cardGe_n₀c]
  have ht := Function.Embedding.total ↥A ↥B'
  constructor
  · exact ⟨fun h => h.2, fun h => ⟨ht.resolve_right h, h⟩⟩
  · exact ⟨fun h => h.2, fun h => ⟨ht.resolve_left h, h⟩⟩

/-- Associativity of addition with all sums in one type (the second link of ✱118·25). -/
private theorem add_assoc_T {α β γ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    {ϖ : Set (Set γ)} :
    ((μ +ᶜ ν : Set (Set T)) +ᶜ ϖ : Set (Set T)) = (μ +ᶜ (ν +ᶜ ϖ : Set (Set T)) : Set (Set T)) := by
  by_cases hμ : ∃ A, μ = n₀c A
  · by_cases hν : ∃ B, ν = n₀c B
    · obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν
      by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨C, rfl⟩ := hϖ
        rw [cardAdd_n₀c, cardAdd_n₀c, n₀c_eq_ncT A, n₀c_eq_ncT C,
          cardAdd_gen (good_T T _) (good_self C T), cardAdd_gen (good_self A T) (good_T T _)]
        exact ncT_congr (Equiv.sumAssoc _ _ _)
      · push Not at hϖ
        simp only [cardAdd_eq_empty_of_right _ hϖ, cardAdd_empty_right]
    · push Not at hν
      simp only [cardAdd_eq_empty_of_right _ hν, cardAdd_eq_empty_of_left hν, cardAdd_empty_left,
        cardAdd_empty_right]
  · push Not at hμ
    simp only [cardAdd_eq_empty_of_left hμ, cardAdd_empty_left]

private theorem add_zero_NC {α β H : Type*} {μ : Set (Set α)} (hμ : μ ∈ NC β) :
    (μ +ᶜ (zero : Set (Set H)) : Set (Set H)) = (sm ʻʻ μ : Set (Set H)) := by
  rcases NC_cases hμ with rfl | ⟨A, rfl⟩
  · rw [cardAdd_empty_left, sm_img_empty]
  · rw [zero_eq_ncT.{_, 0}, sm_img_n₀c', n₀c_eq_ncT, cardAdd_gen (good_self A H) (good_T H _)]
    exact ncT_congr (Equiv.sumEmpty _ _)

private theorem finite_of_N₀C_inductive {α : Type*} {A : Set α} (h : n₀c A ∈ NCinduct) :
    Finite ↥A := (n₀c_mem_NCinduct_iff.1 h).to_subtype

/-- ✱120·45. \(\vdash :\alpha ,\beta \in \text{N}_{\xi }\text{C induct}.\supset .(\alpha +_{c}\beta )_{\xi }\in \text{N}_{\xi }\text{C induct}\) -/
theorem pm120_45 {α : Type*} {ξ : Set α} {μ ν : Set (Set α)} :
    μ ∈ NCinductAt ξ ∧ ν ∈ NCinductAt ξ → (μ +ᶜ ν : Set (Set α)) ∈ NCinductAt ξ := by
  rw [NCinductAt_eq]
  rintro ⟨hμ, hν⟩
  rcases NCinduct_cases hμ with ⟨A, hA, rfl⟩ | ⟨hf, rfl⟩
  · rcases NCinduct_cases hν with ⟨B, hB, rfl⟩ | ⟨hf, rfl⟩
    · have : Finite ↥A := hA.to_subtype
      have : Finite ↥B := hB.to_subtype
      rw [cardAdd_n₀c]; exact ncT_mem_NCinduct
    · rw [cardAdd_empty_right]; exact empty_mem_NCinduct_iff.2 hf
  · rw [cardAdd_empty_left]; exact empty_mem_NCinduct_iff.2 hf

/-- ✱120·4501. \(\vdash :\alpha ,\beta \in \text{NC induct}-\iota ʻ\Lambda .\supset .\alpha +_{c}\beta \in \text{NC induct}\)

`α`, `β` and the sum may be of three types (Prefatory Statement, V). -/
theorem pm120_4501 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NCinduct \ ι Λ ∧ ν ∈ NCinduct \ ι Λ → (μ +ᶜ ν : Set (Set T)) ∈ NCinduct := by
  rintro ⟨⟨hμ, hμ0⟩, ⟨hν, hν0⟩⟩
  rcases NCinduct_cases hμ with ⟨A, hA, rfl⟩ | ⟨-, rfl⟩
  · rcases NCinduct_cases hν with ⟨B, hB, rfl⟩ | ⟨-, rfl⟩
    · have : Finite ↥A := hA.to_subtype
      have : Finite ↥B := hB.to_subtype
      rw [cardAdd_n₀c]; exact ncT_mem_NCinduct
    · exact absurd Null_eq_empty.symm hν0
  · exact absurd Null_eq_empty.symm hμ0

private theorem mem_NCinduct_sub_null {α : Type*} {A : Set α} (hA : A.Finite) :
    n₀c A ∈ NCinduct \ ι Λ :=
  ⟨n₀c_mem_NCinduct hA, fun h => n₀c_ne_empty A (h.trans Null_eq_empty)⟩

/-- ✱120·451. \[\begin{align}&\vdash \colon\ldotp \gamma =(\alpha +_{c}\beta )_{\xi }.\supset _{\alpha ,\beta }.\alpha ,\beta \in \text{NC induct}-\iota ʻ\Lambda :\\ &\exists !(\gamma +_{c}1)_{\xi }.(\gamma +_{c}1)_{\xi }=(\alpha ʻ+_{c}\beta ʻ)_{\xi }:\supset .\alpha ʻ,\beta ʻ\in \text{NC induct}-\iota ʻ\Lambda\end{align}\]

`α'`, `β'` (printed `αʻ`, `βʻ`) are `μ'`, `ν'`; the apparent `α`, `β` are taken in their types
("this proposition could be extended to greater generality as regards types", PM); `γ` and the
sums are in the type `T` of `ξ`, the `1` too. The antecedent is the product of the formal
implication and the one-dot product. -/
theorem pm120_451 {α β T : Type*} {G : Set (Set T)} {μ' : Set (Set α)} {ν' : Set (Set β)} :
    (∀ (μ : Set (Set α)) (ν : Set (Set β)), G = (μ +ᶜ ν : Set (Set T)) →
        μ ∈ NCinduct \ ι Λ ∧ ν ∈ NCinduct \ ι Λ) ∧
      ((G +ᶜ (one : Set (Set T)) : Set (Set T)).Nonempty ∧
        (G +ᶜ (one : Set (Set T)) : Set (Set T)) = (μ' +ᶜ ν' : Set (Set T))) →
      μ' ∈ NCinduct \ ι Λ ∧ ν' ∈ NCinduct \ ι Λ := by
  classical
  rintro ⟨hyp, ⟨ξ, hξ⟩, heq⟩
  have hξ' : ξ ∈ (μ' +ᶜ ν' : Set (Set T)) := heq ▸ hξ
  obtain ⟨Γ₀, O, ⟨rfl, hO⟩, ⟨e1⟩⟩ := mem_cardAdd'.1 hξ
  obtain ⟨A, B, ⟨rfl, rfl⟩, ⟨e2⟩⟩ := mem_cardAdd'.1 hξ'
  obtain ⟨u⟩ := unit_of_mem_one (hO ▸ self_mem_n₀c O)
  have hfin : Finite ↥O := Finite.of_equiv _ u.symm
  have k : ↥A ⊕ ↥B ≃ ↥Γ₀ ⊕ ↥O := e2.symm.trans e1
  by_cases hB : B.Nonempty
  · obtain ⟨b, hb⟩ := hB
    have eB := equiv_diff_singleton hb
    obtain ⟨g⟩ := equiv_cancel u.symm ((Equiv.sumAssoc _ _ _).trans
      (((Equiv.refl _).sumCongr eB.symm).trans k) :
        (↥A ⊕ ↥(B \ {b})) ⊕ PUnit.{1} ≃ ↥Γ₀ ⊕ ↥O)
    have hG : n₀c Γ₀ = (n₀c A +ᶜ n₀c (B \ {b}) : Set (Set T)) := by
      rw [cardAdd_n₀c, n₀c_eq_ncT]; exact ncT_congr g.symm
    obtain ⟨hA, hB'⟩ := hyp _ _ hG
    have : Finite ↥(B \ {b}) := finite_of_N₀C_inductive hB'.1
    exact ⟨hA, mem_NCinduct_sub_null (Set.finite_coe_iff.1 (Finite.of_equiv _ eB.symm))⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hB
    subst hB
    have hA : A.Nonempty := by
      by_contra hA
      rw [Set.not_nonempty_iff_eq_empty] at hA
      subst hA
      obtain ⟨o⟩ := (Equiv.nonempty_congr u).2 ⟨PUnit.unit⟩
      exact (k.symm (Sum.inr o)).elim (fun x => x.2) (fun x => x.2)
    obtain ⟨a, ha⟩ := hA
    have eA := equiv_diff_singleton ha
    obtain ⟨g⟩ := equiv_cancel u.symm ((Equiv.sumAssoc _ _ _).trans
      (((Equiv.refl _).sumCongr (Equiv.sumComm _ _)).trans ((Equiv.sumAssoc _ _ _).symm.trans
        ((eA.symm.sumCongr (Equiv.refl _)).trans k))) :
        (↥(A \ {a}) ⊕ ↥(∅ : Set β)) ⊕ PUnit.{1} ≃ ↥Γ₀ ⊕ ↥O)
    have hG : n₀c Γ₀ = (n₀c (A \ {a}) +ᶜ n₀c (∅ : Set β) : Set (Set T)) := by
      rw [cardAdd_n₀c, n₀c_eq_ncT]; exact ncT_congr g.symm
    obtain ⟨hA', hB'⟩ := hyp _ _ hG
    have : Finite ↥(A \ {a}) := finite_of_N₀C_inductive hA'.1
    exact ⟨mem_NCinduct_sub_null (Set.finite_coe_iff.1 (Finite.of_equiv _ eA.symm)), hB'⟩

/-- ✱120·452. \(\vdash :\alpha +_{c}\beta \in \text{NC induct}-\iota ʻ\Lambda .\supset .\alpha ,\beta \in \text{NC induct}-\iota ʻ\Lambda \) -/
theorem pm120_452 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ +ᶜ ν : Set (Set T)) ∈ NCinduct \ ι Λ → μ ∈ NCinduct \ ι Λ ∧ ν ∈ NCinduct \ ι Λ := by
  rintro ⟨h1, h2⟩
  have hne : (μ +ᶜ ν : Set (Set T)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ← Null_eq_empty]; exact h2
  obtain ⟨A, B, ⟨rfl, rfl⟩, hT⟩ := cardAdd_nonempty_iff.1 hne
  rw [cardAdd_n₀c] at h1
  have := (ncT_mem_NCinduct_iff hT).1 h1
  exact ⟨mem_NCinduct_sub_null (Set.finite_coe_iff.1
      (Finite.of_injective (Sum.inl : ↥A → ↥A ⊕ ↥B) Sum.inl_injective)),
    mem_NCinduct_sub_null (Set.finite_coe_iff.1
      (Finite.of_injective (Sum.inr : ↥B → ↥A ⊕ ↥B) Sum.inr_injective))⟩

/-- ✱120·46. \(\vdash :\alpha \in \text{NC}.\gamma \in \text{N}_{\eta }\text{C induct}.\supset .(\alpha +_{c}\gamma )_{\eta }(+_{c}1)_{*}\text{ sm }_{\eta }ʻʻ\alpha \)

PM's `α` is `μ`; `η : Set H` fixes the type of `γ` and of the sum. -/
theorem pm120_46 {α β H : Type*} {η : Set H} {μ : Set (Set α)} {G : Set (Set H)} :
    μ ∈ NC β ∧ G ∈ NCinductAt η → anc plusC1 (μ +ᶜ G : Set (Set H)) (sm ʻʻ μ : Set (Set H)) := by
  rintro ⟨hμ, hG⟩
  rw [NCinductAt_eq, mem_NCinduct_iff] at hG
  rw [anc_iff_reflTransGen]
  refine ⟨mem_fld_plusC1 _, ?_⟩
  induction hG using Relation.ReflTransGen.head_induction_on with
  | refl => rw [add_zero_NC hμ]
  | head hab _ ih =>
    rw [plusC1_iff.1 hab, ← add_assoc_T]
    exact Relation.ReflTransGen.head rfl ih

/-- ✱120·461. \(\vdash :\alpha \in \text{NC}.\beta (+_{c}1)_{*}\text{ sm }_{\eta }ʻʻ\alpha .\supset .(\exists \gamma ).\gamma \in \text{N}_{\eta }\text{C induct}.\beta =(\alpha +_{c}\gamma )_{\eta }\) -/
theorem pm120_461 {α β H : Type*} {η : Set H} {μ : Set (Set α)} {ν : Set (Set H)} :
    μ ∈ NC β ∧ anc plusC1 ν (sm ʻʻ μ : Set (Set H)) →
      ∃ G : Set (Set H), G ∈ NCinductAt η ∧ ν = (μ +ᶜ G : Set (Set H)) := by
  rintro ⟨hμ, h⟩
  rw [anc_iff_reflTransGen] at h
  obtain ⟨-, h⟩ := h
  rw [NCinductAt_eq]
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨zero, zero_mem_NCinduct, (add_zero_NC hμ).symm⟩
  | head hab _ ih =>
    obtain ⟨G, hG, e⟩ := ih
    refine ⟨(G +ᶜ (one : Set (Set H)) : Set (Set H)), cardAdd_one_mem_NCinduct hG, ?_⟩
    rw [plusC1_iff.1 hab, e, add_assoc_T]

/-- ✱120·462. \[\begin{align}&\vdash \colon\ldotp \alpha \in \text{NC}.\supset :(\exists \gamma ).\gamma \in \text{N}_{\eta }\text{C induct}.\beta =(\alpha +_{c}\gamma )_{\eta }.\equiv .\beta (+_{c}1)_{*}\text{ sm }_{\eta }ʻʻ\alpha \\ &[*120·46·461]\end{align}\] -/
theorem pm120_462 {α β H : Type*} {η : Set H} {μ : Set (Set α)} {ν : Set (Set H)} :
    μ ∈ NC β → ((∃ G : Set (Set H), G ∈ NCinductAt η ∧ ν = (μ +ᶜ G : Set (Set H))) ↔
      anc plusC1 ν (sm ʻʻ μ : Set (Set H))) := by
  intro hμ
  constructor
  · rintro ⟨G, hG, rfl⟩; exact pm120_46 ⟨hμ, hG⟩
  · intro h; exact pm120_461 ⟨hμ, h⟩

/-- ✱120·4621. \(\vdash \colon\ldotp \alpha \in \text{NC}.\exists !\beta .\supset :\beta (+_{c}1)_{*}\text{ sm }_{\eta }ʻʻ\alpha .\supset .\text{ sm }_{\xi }ʻʻ\beta (+_{c}1)_{*}\text{ sm }_{\xi }ʻʻ\alpha \) -/
theorem pm120_4621 {α β H T : Type*} {μ : Set (Set α)} {ν : Set (Set H)} :
    μ ∈ NC β ∧ ν.Nonempty →
      (anc plusC1 ν (sm ʻʻ μ : Set (Set H)) →
        anc plusC1 (sm ʻʻ ν : Set (Set T)) (sm ʻʻ μ : Set (Set T))) := by
  rintro ⟨hμ, hne⟩ h
  obtain ⟨G, hG, rfl⟩ := pm120_461 (η := (∅ : Set H)) ⟨hμ, h⟩
  rw [NCinductAt_eq] at hG
  obtain ⟨A, D, ⟨rfl, rfl⟩, hH⟩ := cardAdd_nonempty_iff.1 hne
  have : Finite ↥D := finite_of_N₀C_inductive hG
  have key : (sm ʻʻ (n₀c A +ᶜ n₀c D : Set (Set H)) : Set (Set T)) =
      (n₀c A +ᶜ ncT T ↥D : Set (Set T)) := by
    rw [cardAdd_n₀c, sm_img_ncT hH, n₀c_eq_ncT A, cardAdd_gen (good_self A T) (good_T T _)]
  rw [key]
  exact pm120_46 (η := (∅ : Set T)) ⟨hμ, by rw [NCinductAt_eq]; exact ncT_mem_NCinduct⟩

/-- ✱120·4622. \[\begin{align}&\vdash \colon\ldotp \alpha \in \text{NC}.\beta \in \text{NC}(\eta ).\exists !\text{ sm }_{\xi }ʻʻ\beta .\supset :\\ &\beta (+_{c}1)_{*}\text{ sm }_{\eta }ʻʻ\alpha .\equiv .\text{ sm }_{\xi }ʻʻ\beta (+_{c}1)_{*}\text{ sm }_{\xi }ʻʻ\alpha \end{align}\]

`β ∈ NC(η)`: `β` is a cardinal whose members are classes of the type `H` of `η` (`ν : Set (Set H)`,
`ν ∈ NC β'`). "It is on this proposition that the irrelevance of types in the consideration of
inductive cardinals depends" (PM). -/
theorem pm120_4622 {α β β' H T : Type*} {μ : Set (Set α)} {ν : Set (Set H)} :
    (μ ∈ NC β ∧ ν ∈ NC β') ∧ (sm ʻʻ ν : Set (Set T)).Nonempty →
      (anc plusC1 ν (sm ʻʻ μ : Set (Set H)) ↔
        anc plusC1 (sm ʻʻ ν : Set (Set T)) (sm ʻʻ μ : Set (Set T))) := by
  rintro ⟨⟨hμ, hν⟩, hsm⟩
  have hne : ν.Nonempty := by
    obtain ⟨X, Y, hY, -⟩ := hsm; exact ⟨Y, hY⟩
  refine ⟨pm120_4621 ⟨hμ, hne⟩, fun h => ?_⟩
  obtain ⟨G, hG, e⟩ := pm120_461 (η := (∅ : Set T)) ⟨hμ, h⟩
  rw [NCinductAt_eq] at hG
  rcases NC_cases hν with rfl | ⟨C, rfl⟩
  · exact absurd hne Set.not_nonempty_empty
  rw [sm_img_n₀c'] at e hsm
  have hne' : (μ +ᶜ G : Set (Set T)).Nonempty := e ▸ hsm
  obtain ⟨A, D, ⟨rfl, rfl⟩, -⟩ := cardAdd_nonempty_iff.1 hne'
  have : Finite ↥D := finite_of_N₀C_inductive hG
  rw [cardAdd_n₀c] at e
  rcases ncT_eq_ncT_iff.1 e with ⟨⟨g⟩⟩ | ⟨h1, -⟩
  · have hH : (n₀c C : Set (Set H)) = (n₀c A +ᶜ ncT H ↥D : Set (Set H)) := by
      rw [n₀c_eq_ncT A, cardAdd_gen (good_self A H) (good_T H _), n₀c_eq_ncT]
      exact ncT_congr g
    rw [hH]
    exact pm120_46 (η := (∅ : Set H)) ⟨hμ, by rw [NCinductAt_eq]; exact ncT_mem_NCinduct⟩
  · exact absurd (ncT_nonempty_iff.1 hsm) h1

/-- ✱120·463. \[\begin{align}\vdash \colon\colon .\alpha \in \text{NC}.\supset \colon\colon &(\exists \gamma ).\gamma \in \text{N}_{\eta }\text{C induct}.\beta =(\alpha +_{c}\gamma )_{\eta }.\equiv \colon\ldotp \\ &\xi \in \mu .\supset _{\xi }.(\xi +_{c}1)_{\eta }\in \mu :\text{ sm }_{\eta }ʻʻ\alpha \in \mu :\supset _{\mu }.\beta \in \mu \\ [*120·462.*90·11]\end{align}\]

The class variable `μ` is `M`. -/
theorem pm120_463 {α β H : Type*} {η : Set H} {μ : Set (Set α)} {ν : Set (Set H)} :
    μ ∈ NC β → ((∃ G : Set (Set H), G ∈ NCinductAt η ∧ ν = (μ +ᶜ G : Set (Set H))) ↔
      ∀ M : Set (Set (Set H)), (∀ ξ, ξ ∈ M → (ξ +ᶜ (one : Set (Set H)) : Set (Set H)) ∈ M) ∧
        (sm ʻʻ μ : Set (Set H)) ∈ M → ν ∈ M) := by
  intro hμ
  rw [pm120_462 hμ]
  exact ancestral_induction_iff

private theorem zero_add_one {H : Type*} :
    ((zero : Set (Set H)) +ᶜ (one : Set (Set H)) : Set (Set H)) = one := by
  rw [zero_eq_ncT.{_, 0}, one_eq_ncT.{_, 0}, cardAdd_gen (good_T H _) (good_T H _)]
  exact ncT_congr (Equiv.emptySum _ _)

private theorem one_ne_zero' {H : Type*} : (one : Set (Set H)) ≠ zero := by
  intro h
  have : (∅ : Set H) ∈ (one : Set (Set H)) := by rw [h, zero_eq]; exact Set.mem_singleton _
  rw [one_eq_ncT.{_, 0}] at this
  obtain ⟨e⟩ := this
  exact (e.symm PUnit.unit).2

/-- ✱120·47. \[\begin{align}&\vdash \colon\colon \beta \in \text{N}_{\eta }\text{C induct}-\iota ʻ0.\equiv \colon\ldotp \xi \in \mu .\supset _{\xi }.(\xi +_{c}1)_{\eta }\in \mu :1_{\eta }\in \mu :\supset _{\mu }.\beta \in \mu \\ &[*120·423·463]\end{align}\]

"Mathematical induction starting from 1 will apply to all inductive cardinals except 0" (PM).
`1_η` is `clsT one η`. -/
theorem pm120_47 {H : Type*} {η : Set H} {ν : Set (Set H)} :
    ν ∈ NCinductAt η \ ι zero ↔ ∀ M : Set (Set (Set H)),
      (∀ ξ, ξ ∈ M → (ξ +ᶜ (one : Set (Set H)) : Set (Set H)) ∈ M) ∧ clsT one η ∈ M → ν ∈ M := by
  rw [clsT_eq]
  constructor
  · intro h M ⟨hstep, h1⟩
    obtain ⟨ν', hν', rfl⟩ := pm120_423.1 h
    clear h
    rw [NCinductAt_eq, mem_NCinduct_iff] at hν'
    induction hν' using Relation.ReflTransGen.head_induction_on with
    | refl => rw [zero_add_one]; exact h1
    | head hab _ ih => rw [plusC1_iff.1 hab]; exact hstep _ ih
  · intro h
    refine h (NCinductAt η \ ι zero) ⟨fun ξ hξ => pm120_423.2 ⟨ξ, hξ.1, rfl⟩, ?_⟩
    rw [NCinductAt_eq]
    exact ⟨pm120_122, one_ne_zero'⟩

/-- ✱120·471. \(\vdash :(\exists \alpha ).\alpha \in \text{NC induct}-\iota ʻ0.f\alpha .\equiv .(\exists \beta ).\beta \in \text{NC induct}.f(\beta +_{c}1)\) -/
theorem pm120_471 {α : Type*} {f : Set (Set α) → Prop} :
    (∃ μ : Set (Set α), μ ∈ NCinduct \ ι zero ∧ f μ) ↔
      ∃ ν : Set (Set α), ν ∈ NCinduct ∧ f (ν +ᶜ (one : Set (Set α)) : Set (Set α)) := by
  constructor
  · rintro ⟨μ, hμ, hf⟩
    rw [← NCinductAt_eq (∅ : Set α)] at hμ
    obtain ⟨ν, hν, rfl⟩ := pm120_423.1 hμ
    rw [NCinductAt_eq] at hν
    exact ⟨ν, hν, hf⟩
  · rintro ⟨ν, hν, hf⟩
    exact ⟨_, ⟨cardAdd_one_mem_NCinduct hν, pm120_124⟩, hf⟩

private theorem one_add_one {α : Type*} :
    ((one : Set (Set α)) +ᶜ (one : Set (Set α)) : Set (Set α)) = two := by
  rw [one_eq_ncT.{_, 0}, two_eq_ncT.{_, 0}, cardAdd_gen (good_T α _) (good_T α _)]
  exact ncT_congr ((Equiv.boolEquivPUnitSumPUnit).symm.trans Equiv.ulift.symm)

/-- ✱120·472. \[\begin{align}\vdash :&(\exists \alpha ).\alpha \in \text{NC induct}-\iota ʻ0-\iota ʻ1.f\alpha .\equiv .\\ &(\exists \beta ).\beta \in \text{NC induct}-\iota ʻ0.f(\beta +_{c}1).\equiv .(\exists \gamma ).\gamma \in \text{NC induct}.f(\gamma +_{c}2)\end{align}\]

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty α]` (in an empty type `1 = Λ`, an inductive cardinal other than `0`, and the first
equivalence fails). -/
theorem pm120_472 {α : Type*} [Nonempty α] {f : Set (Set α) → Prop} :
    ((∃ μ : Set (Set α), μ ∈ (NCinduct \ ι zero) \ ι one ∧ f μ) ↔
        ∃ ν : Set (Set α), ν ∈ NCinduct \ ι zero ∧ f (ν +ᶜ (one : Set (Set α)) : Set (Set α))) ∧
      ((∃ ν : Set (Set α), ν ∈ NCinduct \ ι zero ∧ f (ν +ᶜ (one : Set (Set α)) : Set (Set α))) ↔
        ∃ G : Set (Set α), G ∈ NCinduct ∧ f (G +ᶜ (two : Set (Set α)) : Set (Set α))) := by
  have h1ne : (one : Set (Set α)).Nonempty := by
    rw [one_eq_ncT.{_, 0}]
    exact ncT_nonempty_iff.2 ⟨⟨fun _ => Classical.arbitrary α, fun _ _ _ => rfl⟩⟩
  constructor
  · constructor
    · rintro ⟨μ, ⟨hμ, hμ1⟩, hf⟩
      rw [← NCinductAt_eq (∅ : Set α)] at hμ
      obtain ⟨ν, hν, rfl⟩ := pm120_423.1 hμ
      rw [NCinductAt_eq] at hν
      refine ⟨ν, ⟨hν, fun h => hμ1 ?_⟩, hf⟩
      rw [mem_unitCls] at h ⊢
      rw [h, zero_add_one]
    · rintro ⟨ν, ⟨hν, hν0⟩, hf⟩
      refine ⟨_, ⟨⟨cardAdd_one_mem_NCinduct hν, pm120_124⟩, fun h => hν0 ?_⟩, hf⟩
      rw [mem_unitCls] at h ⊢
      have e : (ν +ᶜ (one : Set (Set α)) : Set (Set α)) =
          ((zero : Set (Set α)) +ᶜ (one : Set (Set α)) : Set (Set α)) := by rw [h, zero_add_one]
      have hne : (ν +ᶜ (one : Set (Set α)) : Set (Set α)).Nonempty := by rw [h]; exact h1ne
      obtain ⟨h2, -⟩ := pm120_311 ⟨hne, e⟩
      rw [h2, zero_eq_n₀c_empty, sm_img_n₀c', n₀c_eq_ncT]
  · constructor
    · rintro ⟨ν, hν, hf⟩
      rw [← NCinductAt_eq (∅ : Set α)] at hν
      obtain ⟨G, hG, rfl⟩ := pm120_423.1 hν
      rw [NCinductAt_eq] at hG
      refine ⟨G, hG, ?_⟩
      rwa [add_assoc_T, one_add_one] at hf
    · rintro ⟨G, hG, hf⟩
      refine ⟨(G +ᶜ (one : Set (Set α)) : Set (Set α)), ⟨cardAdd_one_mem_NCinduct hG, pm120_124⟩, ?_⟩
      rwa [add_assoc_T, one_add_one]

/-- ✱120·473. \[\begin{align}\vdash \colon\ldotp \phi 1:\xi \in \text{N}_{\eta }\text{C induct}-\iota ʻ0.\phi \xi .&\supset _{\xi }.\phi (\xi +_{c}1):\supset :\\ &\xi \in \text{N}_{\eta }\text{C induct}-\iota ʻ0.\supset .\phi \xi\end{align}\]

The `ξ` of the consequent is a real variable. -/
theorem pm120_473 {H : Type*} {η : Set H} {φ : Set (Set H) → Prop} {ξ : Set (Set H)} :
    φ one ∧ (∀ ζ, ζ ∈ NCinductAt η \ ι zero ∧ φ ζ → φ (ζ +ᶜ (one : Set (Set H)) : Set (Set H))) →
      (ξ ∈ NCinductAt η \ ι zero → φ ξ) := by
  rintro ⟨h1, hstep⟩ hξ
  refine (pm120_47.1 hξ {ζ | ζ ∈ NCinductAt η \ ι zero ∧ φ ζ}
    ⟨fun ζ hζ => ⟨pm120_423.2 ⟨ζ, hζ.1.1, rfl⟩, hstep ζ hζ⟩, ?_⟩).2
  rw [clsT_eq, NCinductAt_eq]
  exact ⟨⟨pm120_122, one_ne_zero'⟩, h1⟩

/-- ✱120·48. \[\begin{align}&\vdash :\beta \in \text{NC induct}.\beta \geq \alpha .\supset .\alpha \in \text{NC induct}-\iota ʻ\Lambda \\ &[*120·452.*117·31]\end{align}\] -/
theorem pm120_48 {α β : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    ν ∈ NCinduct ∧ ν ≥ᶜ μ → μ ∈ NCinduct \ ι Λ := by
  rintro ⟨hν, h⟩
  obtain ⟨B, A, ⟨rfl, rfl⟩, ⟨f⟩⟩ := cardGe_iff.1 h
  have : Finite ↥B := finite_of_N₀C_inductive hν
  exact mem_NCinduct_sub_null (Set.finite_coe_iff.1 (Finite.of_injective f f.injective))

/-- ✱120·481. \(\vdash :\eta \in \text{Cls induct}.\xi \subset \eta .\supset .\xi \in \text{Cls induct} \quad[*117·222.*120·21·48]\) -/
theorem pm120_481 {α : Type*} {η ξ : Set α} : η ∈ ClsInduct ∧ ξ ⊆ η → ξ ∈ ClsInduct := by
  rintro ⟨h, hsub⟩
  exact mem_ClsInduct.2 ((mem_ClsInduct.1 h).subset hsub)

/-- ✱120·49. \(\vdash :\alpha \in \text{NC}-\text{NC induct}-\iota ʻ\Lambda .\beta \in \text{NC induct}-\iota ʻ\Lambda .\supset .\alpha >\beta\) -/
theorem pm120_49 {α β Y : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ (NC Y \ NCinduct) \ ι Λ ∧ ν ∈ NCinduct \ ι Λ → μ >ᶜ ν := by
  rintro ⟨⟨⟨hμ, hμi⟩, hμ0⟩, hν⟩
  obtain ⟨A, rfl⟩ := NC_ne_empty_N₀C ⟨hμ, hμ0⟩
  obtain ⟨B, rfl⟩ := NC_ne_empty_N₀C ⟨pm120_14 hν.1, hν.2⟩
  have hB : Finite ↥B := finite_of_N₀C_inductive hν.1
  have hA : ¬ Finite ↥A := fun h => hμi (n₀c_mem_NCinduct (Set.finite_coe_iff.1 h))
  refine cardGt_n₀c.2 ⟨emb_of_finite_card_le (Or.inl hA), fun ⟨f⟩ => hA ?_⟩
  exact Finite.of_injective f f.injective

/-- ✱120·491. \(\vdash \colon\ldotp \xi {\sim}\in \text{Cls induct}.\equiv :\beta \in \text{NC induct}.\supset _{\beta }.\exists !\beta \cap \text{Cl}ʻ\xi\) -/
theorem pm120_491 {α : Type*} {ξ : Set α} :
    ξ ∉ ClsInduct ↔ ∀ ν : Set (Set α), ν ∈ NCinduct → (ν ∩ cl ξ).Nonempty := by
  rw [mem_ClsInduct]
  constructor
  · intro hξ ν hν
    have hξ' : ¬ Finite ↥ξ := fun h => hξ (Set.finite_coe_iff.1 h)
    rcases NCinduct_cases hν with ⟨B, hB, rfl⟩ | ⟨hf, rfl⟩
    · have : Finite ↥B := hB.to_subtype
      rw [Set.inter_comm, n₀c_eq_nc]
      exact cl_inter_nc_nonempty.2 (emb_of_finite_card_le (Or.inl hξ'))
    · exact absurd (Set.toFinite ξ) hξ
  · intro h hξ
    have : Finite ↥ξ := hξ.to_subtype
    obtain ⟨C, hC, hCξ⟩ := h _ (cardAdd_one_mem_NCinduct (n₀c_mem_NCinduct hξ))
    obtain ⟨A, O, ⟨hA, hO⟩, ⟨e⟩⟩ := mem_cardAdd'.1 hC
    obtain ⟨eA⟩ := eq_n₀c_iff_equiv.1 hA
    obtain ⟨u⟩ := unit_of_mem_one (hO ▸ self_mem_n₀c O)
    have k := Finite.card_le_of_embedding
      ((e.symm.toEmbedding.trans ⟨Set.inclusion hCξ, Set.inclusion_injective hCξ⟩) :
        ↥A ⊕ ↥O ↪ ↥ξ)
    have : Finite ↥O := Finite.of_equiv _ u.symm
    have : Finite ↥A := Finite.of_equiv _ eA
    rw [Nat.card_sum, ← Nat.card_congr eA, Nat.card_congr u] at k
    have h0 : Nat.card PUnit.{1} = 1 := Nat.card_unique
    omega

/-- ✱120·492. \[\begin{align}&\vdash :\alpha \in \text{NC}-\text{NC induct}.\beta \geq \alpha .\supset .\beta \in \text{NC}-\text{NC induct}\\ &[*120·48.\text{Transp}]\end{align}\]

The converse domain of the second `NC` is the type of the members of `β` (as in ✱100·41).

**Status.** proved (reading): the converse domain of the `NC` in the conclusion is the type of the
members of the members of `β` (`NC` is typically ambiguous; with a smaller converse domain
`β ∈ NC` can fail). -/
theorem pm120_492 {α β Y : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ NC Y \ NCinduct ∧ ν ≥ᶜ μ → ν ∈ (NC β : Set (Set (Set β))) \ NCinduct := by
  rintro ⟨⟨hμ, hμi⟩, h⟩
  obtain ⟨B, A, ⟨rfl, rfl⟩, ⟨f⟩⟩ := cardGe_iff.1 h
  refine ⟨n₀c_mem_NC B, fun hB => hμi ?_⟩
  have : Finite ↥B := finite_of_N₀C_inductive hB
  exact n₀c_mem_NCinduct (Set.finite_coe_iff.1 (Finite.of_injective f f.injective))

/-- ✱120·493. \[\begin{align}&\vdash \colon\ldotp \sigma \in \text{Cls induct}.\supset :\\ &\text{Nc}ʻ\xi <\text{Nc}ʻ\sigma .\equiv .(\exists \rho ).\rho \text{ sm }\xi .\rho \subset \sigma .\exists !\sigma -\rho .\equiv .\exists !\text{Nc}ʻ\xi \cap \text{Cl}ʻ\sigma -\iota ʻ\sigma\end{align}\]

`Nc'ξ ∩ Cl'σ − ι'σ` is `(Nc'ξ ∩ Cl'σ) − ι'σ`, its `Nc'ξ` in the type of `σ`.

**Status.** proved (reading): the sides `Nc'ξ`, `Nc'σ` of `<` are `N₀c'ξ`, `N₀c'σ` (✱117·02·03,
normal adjustment). -/
theorem pm120_493 {α β : Type*} {σ : Set α} {ξ : Set β} :
    σ ∈ ClsInduct →
      ((n₀c ξ <ᶜ n₀c σ ↔ ∃ ρ : Set α, (sm ρ ξ ∧ ρ ⊆ σ) ∧ (σ \ ρ).Nonempty) ∧
        ((∃ ρ : Set α, (sm ρ ξ ∧ ρ ⊆ σ) ∧ (σ \ ρ).Nonempty) ↔
          ((nc α ξ ∩ cl σ) \ ι σ).Nonempty)) := by
  intro hσ
  have hσf := mem_ClsInduct.1 hσ
  refine ⟨⟨fun h => ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨f⟩ := (cardGt_n₀c.1 h).1
    have h2 := (cardGt_n₀c.1 h).2
    let ρ : Set α := Set.range (fun x => (f x : α))
    have hρσ : ρ ⊆ σ := by rintro _ ⟨x, rfl⟩; exact (f x).2
    have eρ : ↥ξ ≃ ↥ρ := Equiv.ofInjective _ (Subtype.val_injective.comp f.injective)
    refine ⟨ρ, ⟨sm_iff_nonempty_equiv.2 ⟨eρ.symm⟩, hρσ⟩, ?_⟩
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hne
    have : ρ = σ := Set.Subset.antisymm hρσ hne
    apply h2
    exact ⟨(Set.equivOfEq this.symm).toEmbedding.trans eρ.symm.toEmbedding⟩
  · rintro ⟨ρ, ⟨hρξ, hρσ⟩, hne⟩
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hρξ
    refine cardGt_n₀c.2 ⟨⟨e.symm.toEmbedding.trans ⟨Set.inclusion hρσ, Set.inclusion_injective hρσ⟩⟩,
      fun ⟨g⟩ => not_emb_of_finite_ssubset (hσf.subset hρσ) hρσ hne ⟨g.trans e.symm.toEmbedding⟩⟩
  · rintro ⟨ρ, ⟨hρξ, hρσ⟩, ⟨x, hxσ, hxρ⟩⟩
    refine ⟨ρ, ⟨hρξ, hρσ⟩, fun h => hxρ ?_⟩
    rw [mem_unitCls.1 h]; exact hxσ
  · rintro ⟨ρ, ⟨hρξ, hρσ⟩, hρ⟩
    refine ⟨ρ, ⟨hρξ, hρσ⟩, ?_⟩
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hne
    exact hρ (mem_unitCls.2 (Set.Subset.antisymm hρσ hne))

/-- ✱120·5. \(\vdash :\alpha ,\beta \in \text{NC induct}.\exists !\alpha \times _{c}\beta .\supset .\alpha \times _{c}\beta \in \text{NC induct}\) -/
theorem pm120_5 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ∈ NCinduct ∧ ν ∈ NCinduct) ∧ (μ ×ᶜ ν : Set (Set T)).Nonempty →
      (μ ×ᶜ ν : Set (Set T)) ∈ NCinduct := by
  rintro ⟨⟨hμ, hν⟩, hne⟩
  obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := cardMul_nonempty_iff.1 hne
  have : Finite ↥A := finite_of_N₀C_inductive hμ
  have : Finite ↥B := finite_of_N₀C_inductive hν
  rw [cardMul_n₀c]; exact ncT_mem_NCinduct

/-- ✱120·51. \(\vdash :\alpha ,\beta ,\gamma ,\in \text{NC induct}.\alpha \neq 0.\exists !\alpha \times _{c}\beta .\alpha\times _{c}\beta =\alpha \times _{c}\gamma .\supset .\beta =\text{ sm }ʻʻ\gamma\)

PM's `α`, `β`, `γ` are `μ`, `ν`, `ρ`; the logical and equational occurrences of `α ×_c β` are in
one type `T` (IT), and `α ×_c γ` with them.

**Status.** proved (reading): convention IT (Prefatory Statement, IV) binds the logical and the
equational occurrences of `α ×_c β`. -/
theorem pm120_51 {α β γ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ρ : Set (Set γ)} :
    ((((μ ∈ NCinduct ∧ ν ∈ NCinduct) ∧ ρ ∈ NCinduct) ∧ μ ≠ zero) ∧
        (μ ×ᶜ ν : Set (Set T)).Nonempty) ∧ (μ ×ᶜ ν : Set (Set T)) = (μ ×ᶜ ρ : Set (Set T)) →
      ν = (sm ʻʻ ρ : Set (Set β)) := by
  rintro ⟨⟨⟨⟨⟨hμ, hν⟩, hρ⟩, h0⟩, ⟨ξ, hξ⟩⟩, heq⟩
  have hξ' : ξ ∈ (μ ×ᶜ ρ : Set (Set T)) := heq ▸ hξ
  obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := cardMul_nonempty_iff.1 ⟨ξ, hξ⟩
  obtain ⟨A', C, ⟨-, rfl⟩, -⟩ := cardMul_nonempty_iff.1 ⟨ξ, hξ'⟩
  rw [cardMul_n₀c] at hξ hξ'
  obtain ⟨e1⟩ := hξ
  obtain ⟨e2⟩ := hξ'
  have : Finite ↥A := finite_of_N₀C_inductive hμ
  have : Finite ↥B := finite_of_N₀C_inductive hν
  have : Finite ↥C := finite_of_N₀C_inductive hρ
  have hAne : Nonempty ↥A := nonempty_of_n₀c_ne_zero h0
  have k := Nat.card_congr (e1.symm.trans e2)
  rw [Nat.card_prod, Nat.card_prod] at k
  have hpos : 0 < Nat.card ↥A := Nat.card_pos
  have hBC : Nat.card ↥B = Nat.card ↥C := Nat.eq_of_mul_eq_mul_left hpos k
  obtain ⟨g⟩ := Finite.card_eq.1 hBC
  rw [sm_img_n₀c', n₀c_eq_ncT]; exact ncT_congr g

/-- ✱120·511. \(\vdash :\alpha ,\beta \in \text{NC induct}.\alpha \neq 0.\exists !\alpha .\alpha \times _{c}\beta =\alpha .\supset .\beta =1\)

The equation `α ×_c β = α` is in the type of `α`; `1` is in the type of `β`. -/
theorem pm120_511 {α β : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (((μ ∈ NCinduct ∧ ν ∈ NCinduct) ∧ μ ≠ zero) ∧ μ.Nonempty) ∧ (μ ×ᶜ ν : Set (Set α)) = μ →
      ν = (one : Set (Set β)) := by
  rintro ⟨⟨⟨⟨hμ, hν⟩, h0⟩, hne⟩, heq⟩
  rcases NCinduct_cases hμ with ⟨A, hA, rfl⟩ | ⟨-, rfl⟩
  · have hA' : A ∈ (n₀c A ×ᶜ ν : Set (Set α)) := by rw [heq]; exact self_mem_n₀c A
    obtain ⟨A₁, B, ⟨-, rfl⟩, -⟩ := cardMul_nonempty_iff.1 ⟨A, hA'⟩
    rw [cardMul_n₀c] at hA'
    obtain ⟨e⟩ := hA'
    have : Finite ↥A := hA.to_subtype
    have : Finite ↥B := finite_of_N₀C_inductive hν
    have : Nonempty ↥A := nonempty_of_n₀c_ne_zero h0
    have k := Nat.card_congr e
    rw [Nat.card_prod] at k
    have hpos : 0 < Nat.card ↥A := Nat.card_pos
    have hB1 : Nat.card ↥B = 1 := by
      have : Nat.card ↥A * 1 = Nat.card ↥A * Nat.card ↥B := by rw [mul_one]; exact k
      exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
    rw [Nat.card_coe_set_eq, Set.ncard_eq_one] at hB1
    obtain ⟨b, rfl⟩ := hB1
    exact (one_eq_n₀c_singleton b).symm
  · exact absurd hne Set.not_nonempty_empty

private theorem n₀c_notMem_iota_zero {δ : Type*} {C : Set δ} (c : C) :
    n₀c C ∉ ι (zero : Set (Set δ)) := by
  intro h
  have := n₀c_eq_zero_iff.1 (mem_unitCls.1 h)
  exact (Set.eq_empty_iff_forall_notMem.1 this) c c.2

/-- ✱120·512. \(\vdash :\alpha \times _{c}\beta \in \text{NC induct}-\iota ʻ0-\iota ʻ\Lambda .\supset .\alpha ,\beta \in \text{NC induct}-\iota ʻ0-\iota ʻ\Lambda \) -/
theorem pm120_512 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ×ᶜ ν : Set (Set T)) ∈ (NCinduct \ ι zero) \ ι Λ →
      μ ∈ (NCinduct \ ι zero) \ ι Λ ∧ ν ∈ (NCinduct \ ι zero) \ ι Λ := by
  rintro ⟨⟨h1, h0⟩, hΛ⟩
  have hne : (μ ×ᶜ ν : Set (Set T)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ← Null_eq_empty]; exact hΛ
  obtain ⟨A, B, ⟨rfl, rfl⟩, hT⟩ := cardMul_nonempty_iff.1 hne
  rw [cardMul_n₀c] at h1 h0
  have hfin := (ncT_mem_NCinduct_iff hT).1 h1
  have hAB : Nonempty (↥A × ↥B) := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply h0
    show _ = zero
    rw [zero_eq_ncT.{_, 0}]; exact ncT_congr (Equiv.equivOfIsEmpty _ _)
  obtain ⟨⟨a, b⟩⟩ := hAB
  have hA : Finite ↥A := Finite.of_injective (fun x => (x, b)) (fun x y h => (Prod.mk.inj h).1)
  have hB : Finite ↥B := Finite.of_injective (fun y => (a, y)) (fun x y h => (Prod.mk.inj h).2)
  exact ⟨⟨⟨n₀c_mem_NCinduct (Set.finite_coe_iff.1 hA), n₀c_notMem_iota_zero a⟩, (mem_NCinduct_sub_null
      (Set.finite_coe_iff.1 hA)).2⟩,
    ⟨⟨n₀c_mem_NCinduct (Set.finite_coe_iff.1 hB), n₀c_notMem_iota_zero b⟩, (mem_NCinduct_sub_null
      (Set.finite_coe_iff.1 hB)).2⟩⟩

/-- ✱120·513. \(\vdash :\alpha \in \text{NC induct}-\iota ʻ0-\iota ʻ\Lambda .\alpha \times _{c}\beta =\alpha .\supset .\beta =1 \quad[*120·511·512]\) -/
theorem pm120_513 {α β : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ∈ (NCinduct \ ι zero) \ ι Λ ∧ (μ ×ᶜ ν : Set (Set α)) = μ → ν = (one : Set (Set β)) := by
  rintro ⟨hμ, heq⟩
  have hμν : (μ ×ᶜ ν : Set (Set α)) ∈ (NCinduct \ ι zero) \ ι Λ := by rw [heq]; exact hμ
  have hν := (pm120_512 hμν).2
  refine pm120_511 ⟨⟨⟨⟨hμ.1.1, hν.1.1⟩, hμ.1.2⟩, ?_⟩, heq⟩
  rw [Set.nonempty_iff_ne_empty, ← Null_eq_empty]; exact hμ.2

/-- ✱120·52. \(\vdash :\alpha ,\beta \in \text{NC induct}.\exists !\alpha ^\beta .\supset .\alpha ^\beta \in \text{NC induct}\) -/
theorem pm120_52 {α β T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    (μ ∈ NCinduct ∧ ν ∈ NCinduct) ∧ (μ ^ᶜ ν : Set (Set T)).Nonempty →
      (μ ^ᶜ ν : Set (Set T)) ∈ NCinduct := by
  rintro ⟨⟨hμ, hν⟩, hne⟩
  obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := cardExp_nonempty_iff.1 hne
  have : Finite ↥A := finite_of_N₀C_inductive hμ
  have : Finite ↥B := finite_of_N₀C_inductive hν
  rw [cardExp_n₀c]; exact ncT_mem_NCinduct

/-- ✱120·53. \(\vdash :\alpha ,\beta ,\gamma \in \text{NC induct}.\alpha \neq 0.a\neq 1.\exists !\alpha ^\beta .\alpha ^\beta =\alpha ^\gamma .\supset .\beta =\text{ sm }ʻʻ\gamma \)

(The e-text prints `a ≠ 1` for `α ≠ 1`.) As ✱120·51.

**Status.** proved (reading): transcription error (`a` for `α`); convention IT (Prefatory
Statement, IV) binds the logical and the equational occurrences of `α^β`. -/
theorem pm120_53 {α β γ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ρ : Set (Set γ)} :
    (((((μ ∈ NCinduct ∧ ν ∈ NCinduct) ∧ ρ ∈ NCinduct) ∧ μ ≠ zero) ∧ μ ≠ one) ∧
        (μ ^ᶜ ν : Set (Set T)).Nonempty) ∧ (μ ^ᶜ ν : Set (Set T)) = (μ ^ᶜ ρ : Set (Set T)) →
      ν = (sm ʻʻ ρ : Set (Set β)) := by
  rintro ⟨⟨⟨⟨⟨⟨hμ, hν⟩, hρ⟩, h0⟩, h1⟩, ⟨ξ, hξ⟩⟩, heq⟩
  have hξ' : ξ ∈ (μ ^ᶜ ρ : Set (Set T)) := heq ▸ hξ
  obtain ⟨A, B, ⟨rfl, rfl⟩, -⟩ := cardExp_nonempty_iff.1 ⟨ξ, hξ⟩
  obtain ⟨A', C, ⟨-, rfl⟩, -⟩ := cardExp_nonempty_iff.1 ⟨ξ, hξ'⟩
  rw [cardExp_n₀c] at hξ hξ'
  obtain ⟨e1⟩ := hξ
  obtain ⟨e2⟩ := hξ'
  have : Finite ↥A := finite_of_N₀C_inductive hμ
  have : Finite ↥B := finite_of_N₀C_inductive hν
  have : Finite ↥C := finite_of_N₀C_inductive hρ
  obtain ⟨a, b, hab⟩ := two_of_n₀c_ne h0 h1
  have : Nontrivial ↥A := ⟨⟨a, b, hab⟩⟩
  have h2 : 1 < Nat.card ↥A := Finite.one_lt_card
  have k := Nat.card_congr (e1.symm.trans e2)
  rw [Nat.card_fun, Nat.card_fun] at k
  have hBC : Nat.card ↥B = Nat.card ↥C := Nat.pow_right_injective h2 k
  obtain ⟨g⟩ := Finite.card_eq.1 hBC
  rw [sm_img_n₀c', n₀c_eq_ncT]; exact ncT_congr g

private theorem adeqExp_emb' {α β W : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (h : AdeqExp W μ ν) (A : Set α) (B : Set β) (hB : Nonempty ↥B) :
    Nonempty ((↥B → ↥A) ↪ W) := by
  by_cases hA : Nonempty ↥A
  · obtain ⟨a⟩ := hA
    have : Nonempty W := by
      rw [AdeqExp, cardExp_n₀c, ncT_nonempty_iff] at h
      obtain ⟨f⟩ := h
      exact ⟨f (fun _ => ⟨a, by rw [typ₁, typ₀_eq_univ]; trivial⟩)⟩
    exact adeqExp_emb h A B
  · rw [not_nonempty_iff] at hA
    obtain ⟨b⟩ := hB
    have : IsEmpty (↥B → ↥A) := ⟨fun g => isEmptyElim (g b)⟩
    exact ⟨⟨isEmptyElim, fun x => isEmptyElim x⟩⟩

/-- `β < γ . ⊃ . β^α < γ^α` for finite `α ≠ 0` and finite `β`. -/
private theorem exp_lt_aux {A B C : Type*} [Finite A] [Nonempty A] [Finite B]
    (hBC : Nonempty (B ↪ C)) (hCB : ¬ Nonempty (C ↪ B)) :
    Nonempty ((A → B) ↪ (A → C)) ∧ ¬ Nonempty ((A → C) ↪ (A → B)) := by
  obtain ⟨f⟩ := hBC
  refine ⟨⟨⟨fun g => f ∘ g, fun g g' h => funext fun a => f.injective (congrFun h a)⟩⟩, ?_⟩
  rintro ⟨k⟩
  have hC : Finite C := Finite.of_injective (fun c => k (fun _ => c)) (fun c c' h => by
    simpa using congrFun (k.injective h) (Classical.arbitrary A))
  have hlt : Nat.card B < Nat.card C := by
    by_contra hle
    exact hCB (emb_of_finite_card_le (Or.inr (by omega)))
  have k2 := Finite.card_le_of_embedding k
  rw [Nat.card_fun, Nat.card_fun] at k2
  have hA : Nat.card A ≠ 0 := Nat.card_pos.ne'
  exact absurd k2 (not_le.2 (Nat.pow_lt_pow_left hlt hA))

private theorem exp_gt_core {α β γ W₁ W₂ : Type*} {A : Set α} {B : Set β} {C : Set γ}
    [Finite ↥A] [Nonempty ↥A] [Finite ↥B] (hBC : Nonempty (↥B ↪ ↥C))
    (hCB : ¬ Nonempty (↥C ↪ ↥B)) (h₁ : AdeqExp W₁ (n₀c B) (n₀c A))
    (h₂ : AdeqExp W₂ (n₀c C) (n₀c A)) :
    (n₀c C ^ᶜ n₀c A : Set (Set W₂)) >ᶜ (n₀c B ^ᶜ n₀c A : Set (Set W₁)) := by
  obtain ⟨X₁, hX₁⟩ := ncT_nonempty_iff.2 (adeqExp_emb' h₁ B A inferInstance)
  obtain ⟨X₂, hX₂⟩ := ncT_nonempty_iff.2 (adeqExp_emb' h₂ C A inferInstance)
  rw [cardExp_n₀c, cardExp_n₀c, ncT_eq_n₀c_of_mem hX₁, ncT_eq_n₀c_of_mem hX₂]
  obtain ⟨e1⟩ := hX₁
  obtain ⟨e2⟩ := hX₂
  obtain ⟨h1, h2⟩ := exp_lt_aux (A := ↥A) hBC hCB
  exact cardGt_n₀c.2 ⟨(emb_congr e1.symm e2.symm).1 h1,
    fun h => h2 ((emb_congr e2 e1).1 h)⟩

/-- ✱120·54. \(\vdash :\xi ,\rho \in \text{Cls induct}.\exists !\xi .\rho \subset \sigma .\exists !\sigma - \rho .\supset .(\text{Nc}ʻ\rho )^{\text{Nc}ʻ\xi }<(\text{Nc}ʻ\sigma )^{\text{Nc}ʻ\xi }\)

The arguments `Nc'ρ`, `Nc'ξ`, `Nc'σ` of the powers are `N₀c'ρ`, … (✱116·03·04); the powers, sides
of `<`, are in adequate types `W₁`, `W₂` (IIT).

**Status.** proved (reading): the arguments `Nc'ρ`, `Nc'σ`, `Nc'ξ` are `N₀c'ρ`, `N₀c'σ`, `N₀c'ξ`
(normal adjustment); convention IIT (Prefatory Statement, IV): the actual types `W₁`, `W₂` of the
two powers are adequate. -/
theorem pm120_54 {α β W₁ W₂ : Type*} {ξ : Set β} {ρ σ : Set α}
    (h₁ : AdeqExp W₁ (n₀c ρ) (n₀c ξ)) (h₂ : AdeqExp W₂ (n₀c σ) (n₀c ξ)) :
    (((ξ ∈ ClsInduct ∧ ρ ∈ ClsInduct) ∧ ξ.Nonempty) ∧ ρ ⊆ σ) ∧ (σ \ ρ).Nonempty →
      (n₀c ρ ^ᶜ n₀c ξ : Set (Set W₁)) <ᶜ (n₀c σ ^ᶜ n₀c ξ : Set (Set W₂)) := by
  rintro ⟨⟨⟨⟨hξ, hρ⟩, hne⟩, hsub⟩, hdiff⟩
  have : Finite ↥ξ := (mem_ClsInduct.1 hξ).to_subtype
  have : Nonempty ↥ξ := hne.to_subtype
  have : Finite ↥ρ := (mem_ClsInduct.1 hρ).to_subtype
  exact exp_gt_core ⟨⟨Set.inclusion hsub, Set.inclusion_injective hsub⟩⟩
    (not_emb_of_finite_ssubset (mem_ClsInduct.1 hρ) hsub hdiff) h₁ h₂

/-- ✱120·541. \(\vdash :\alpha ,\beta \in \text{NC induct}-\iota ʻ\Lambda .\alpha \neq 0.\beta <\gamma .\supset .\beta ^\alpha <\gamma ^\alpha \quad[*120·54·493]\)

PM's `α`, `β`, `γ` are `μ`, `ν`, `ρ`; the powers (sides of `<`) are in adequate types (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types `W₁`, `W₂`
of `β^α`, `γ^α` are adequate. -/
theorem pm120_541 {α β γ W₁ W₂ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ρ : Set (Set γ)}
    (h₁ : AdeqExp W₁ ν μ) (h₂ : AdeqExp W₂ ρ μ) :
    ((μ ∈ NCinduct \ ι Λ ∧ ν ∈ NCinduct \ ι Λ) ∧ μ ≠ zero) ∧ ν <ᶜ ρ →
      (ν ^ᶜ μ : Set (Set W₁)) <ᶜ (ρ ^ᶜ μ : Set (Set W₂)) := by
  rintro ⟨⟨⟨hμ, hν⟩, h0⟩, hlt⟩
  obtain ⟨B, C, ⟨rfl, rfl⟩, hBC, hCB⟩ := cardLt_iff.1 hlt
  obtain ⟨A, rfl⟩ := NC_ne_empty_N₀C ⟨pm120_14 hμ.1, hμ.2⟩
  have : Finite ↥A := finite_of_N₀C_inductive hμ.1
  have : Nonempty ↥A := nonempty_of_n₀c_ne_zero h0
  have : Finite ↥B := finite_of_N₀C_inductive hν.1
  exact exp_gt_core hBC hCB h₁ h₂

/-- ✱120·542. \(\vdash :\alpha ,\gamma \in \text{NC induct}-\iota ʻ\Lambda .\alpha \neq 0.\beta >\gamma .\supset .\beta ^\alpha >\gamma ^\alpha \quad[*120·541]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types `W₁`, `W₂`
of `β^α`, `γ^α` are adequate. -/
theorem pm120_542 {α β γ W₁ W₂ : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ρ : Set (Set γ)}
    (h₁ : AdeqExp W₁ ν μ) (h₂ : AdeqExp W₂ ρ μ) :
    ((μ ∈ NCinduct \ ι Λ ∧ ρ ∈ NCinduct \ ι Λ) ∧ μ ≠ zero) ∧ ν >ᶜ ρ →
      (ν ^ᶜ μ : Set (Set W₁)) >ᶜ (ρ ^ᶜ μ : Set (Set W₂)) := by
  rintro ⟨⟨⟨hμ, hρ⟩, h0⟩, hgt⟩
  obtain ⟨B, C, ⟨rfl, rfl⟩, hCB, hBC⟩ := cardGt_iff.1 hgt
  obtain ⟨A, rfl⟩ := NC_ne_empty_N₀C ⟨pm120_14 hμ.1, hμ.2⟩
  have : Finite ↥A := finite_of_N₀C_inductive hμ.1
  have : Nonempty ↥A := nonempty_of_n₀c_ne_zero h0
  have : Finite ↥C := finite_of_N₀C_inductive hρ.1
  exact exp_gt_core hCB hBC h₂ h₁

/-- ✱120·55. \(\vdash :\alpha ,\beta ,\gamma \in \text{NC induct}.\alpha \neq 0.\exists !\beta ^\alpha .\beta ^\alpha =\gamma ^\alpha .\supset .\beta =\text{ sm }ʻʻ\gamma\)

**Status.** proved (reading): convention IT (Prefatory Statement, IV) binds the logical and the
equational occurrences of `β^α`. -/
theorem pm120_55 {α β γ T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} {ρ : Set (Set γ)} :
    ((((μ ∈ NCinduct ∧ ν ∈ NCinduct) ∧ ρ ∈ NCinduct) ∧ μ ≠ zero) ∧
        (ν ^ᶜ μ : Set (Set T)).Nonempty) ∧ (ν ^ᶜ μ : Set (Set T)) = (ρ ^ᶜ μ : Set (Set T)) →
      ν = (sm ʻʻ ρ : Set (Set β)) := by
  rintro ⟨⟨⟨⟨⟨hμ, hν⟩, hρ⟩, h0⟩, ⟨ξ, hξ⟩⟩, heq⟩
  have hξ' : ξ ∈ (ρ ^ᶜ μ : Set (Set T)) := heq ▸ hξ
  obtain ⟨B, A, ⟨rfl, rfl⟩, -⟩ := cardExp_nonempty_iff.1 ⟨ξ, hξ⟩
  obtain ⟨C, A', ⟨rfl, -⟩, -⟩ := cardExp_nonempty_iff.1 ⟨ξ, hξ'⟩
  rw [cardExp_n₀c] at hξ hξ'
  obtain ⟨e1⟩ := hξ
  obtain ⟨e2⟩ := hξ'
  have : Finite ↥A := finite_of_N₀C_inductive hμ
  have : Finite ↥B := finite_of_N₀C_inductive hν
  have : Finite ↥C := finite_of_N₀C_inductive hρ
  have : Nonempty ↥A := nonempty_of_n₀c_ne_zero h0
  have k := Nat.card_congr (e1.symm.trans e2)
  rw [Nat.card_fun, Nat.card_fun] at k
  have hBC : Nat.card ↥B = Nat.card ↥C := Nat.pow_left_injective Nat.card_pos.ne' k
  obtain ⟨g⟩ := Finite.card_eq.1 hBC
  rw [sm_img_n₀c', n₀c_eq_ncT]; exact ncT_congr g

/-- ✱120·56. \(\vdash :\alpha \geq 2.\alpha ^\beta \in \text{NC induct}-\iota ʻ\Lambda .\supset .\beta \in \text{NC induct}\)

The `2` (a side of `≥`) is in any type `W` (its existence there, which IIT would require, is implied
by `α ≥ 2`); `α^β` in any type `T`. -/
theorem pm120_56 {α β W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    μ ≥ᶜ (two : Set (Set W)) ∧ (μ ^ᶜ ν : Set (Set T)) ∈ NCinduct \ ι Λ → ν ∈ NCinduct := by
  rintro ⟨hge, h1, h2⟩
  obtain ⟨A, P, ⟨rfl, hP⟩, ⟨f⟩⟩ := cardGe_iff.1 hge
  have hP2 : P ∈ (two : Set (Set W)) := hP ▸ self_mem_n₀c P
  obtain ⟨x, y, hxy, rfl⟩ := mem_two_iff.1 hP2
  have hab : f ⟨x, Or.inl rfl⟩ ≠ f ⟨y, Or.inr rfl⟩ := fun h =>
    hxy (congrArg Subtype.val (f.injective h))
  have hne : (n₀c A ^ᶜ ν : Set (Set T)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ← Null_eq_empty]; exact h2
  have hν : ∃ B, ν = n₀c B := by
    obtain ⟨_, B, ⟨-, hB⟩, -⟩ := cardExp_nonempty_iff.1 hne; exact ⟨B, hB⟩
  obtain ⟨B, rfl⟩ := hν
  rw [cardExp_n₀c] at h1 hne
  have := (ncT_mem_NCinduct_iff (ncT_nonempty_iff.1 hne)).1 h1
  have : Finite ↥B := Finite.of_injective (embIndicator _ _ hab) (embIndicator _ _ hab).injective
  exact n₀c_mem_NCinduct (Set.finite_coe_iff.1 this)

/-- ✱120·561. \(\vdash :\beta \geq 1.\alpha ^\beta \in \text{NC induct}-\iota ʻ\Lambda .\supset .\alpha \in \text{NC induct}\)

The `1` (a side of `≥`) is in any type `W`. -/
theorem pm120_561 {α β W T : Type*} {μ : Set (Set α)} {ν : Set (Set β)} :
    ν ≥ᶜ (one : Set (Set W)) ∧ (μ ^ᶜ ν : Set (Set T)) ∈ NCinduct \ ι Λ → μ ∈ NCinduct := by
  rintro ⟨hge, h1, h2⟩
  obtain ⟨B, P, ⟨rfl, hP⟩, ⟨f⟩⟩ := cardGe_iff.1 hge
  obtain ⟨w, rfl⟩ : P ∈ (one : Set (Set W)) := hP ▸ self_mem_n₀c P
  have hB : Nonempty ↥B := ⟨f ⟨w, rfl⟩⟩
  have hne : (μ ^ᶜ n₀c B : Set (Set T)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ← Null_eq_empty]; exact h2
  have hμ : ∃ A, μ = n₀c A := by
    obtain ⟨A, _, ⟨hA, -⟩, -⟩ := cardExp_nonempty_iff.1 hne; exact ⟨A, hA⟩
  obtain ⟨A, rfl⟩ := hμ
  rw [cardExp_n₀c] at h1 hne
  have := (ncT_mem_NCinduct_iff (ncT_nonempty_iff.1 hne)).1 h1
  have : Finite ↥A := Finite.of_injective (fun a => (fun _ => a : ↥B → ↥A))
    (fun a a' h => congrFun h hB.some)
  exact n₀c_mem_NCinduct (Set.finite_coe_iff.1 this)

/-- ✱120·57. \(\vdash :\mu \in \text{NC induct}-\iota ʻ\Lambda .\supset .\text{Nc}ʻ\hat{\nu} (\nu \leq \mu )=\mu +_{c}1\)

`ν̂(ν ≤ μ)` is the class of the cardinals of the type of `μ` that are `≤ μ` ("`μ +_c 1` is
necessarily in a higher type than `μ`, because it applies to a class of which `μ` is a member",
PM); its `Nc'` and `μ +_c 1` (sides of one equation) are in a free type `E`, the `1` in the type
of `μ`.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty α]` (for an empty `α`, `1 = Λ` there and `μ +_c 1 = Λ`, while `ν̂(ν ≤ 0) = ι'0`). -/
theorem pm120_57 {α E : Type*} [Nonempty α] {μ : Set (Set α)} :
    μ ∈ NCinduct \ ι Λ →
      nc E {ν : Set (Set α) | ν ≤ᶜ μ} = (μ +ᶜ (one : Set (Set α)) : Set (Set E)) := by
  rintro ⟨h, h0⟩
  obtain ⟨A, rfl⟩ := NC_ne_empty_N₀C ⟨pm120_14 h, h0⟩
  have hAf : Finite ↥A := finite_of_N₀C_inductive h
  have hu : Nonempty (PUnit.{1} ↪ α) := ⟨⟨fun _ => Classical.arbitrary α, fun _ _ _ => rfl⟩⟩
  rw [one_eq_ncT.{_, 0}, n₀c_eq_ncT A, cardAdd_gen (good_self A E) (Or.inl hu), nc_eq_ncT]
  rw [← n₀c_eq_ncT A]
  apply ncT_congr
  set n := Nat.card ↥A with hn
  have hS : ∀ k : Fin (n + 1), ∃ S ⊆ A, S.ncard = (k : ℕ) := fun k =>
    Set.exists_subset_card_eq (by rw [← Nat.card_coe_set_eq]; omega)
  choose S hSA hSc using hS
  have hle : ∀ k, n₀c (S k) ≤ᶜ n₀c A := fun k =>
    cardGe_n₀c.2 ⟨⟨Set.inclusion (hSA k), Set.inclusion_injective (hSA k)⟩⟩
  have hSf : ∀ k, (S k).Finite := fun k => (Set.toFinite A).subset (hSA k)
  let g : Fin (n + 1) → ↥{ν : Set (Set α) | ν ≤ᶜ n₀c A} := fun k => ⟨n₀c (S k), hle k⟩
  have hg : Function.Bijective g := by
    constructor
    · intro k j hkj
      have := congrArg Subtype.val hkj
      obtain ⟨e⟩ := eq_n₀c_iff_equiv.1 this
      have : Finite ↥(S k) := (hSf k).to_subtype
      have h1 := Nat.card_congr e
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, hSc, hSc] at h1
      exact Fin.ext h1
    · rintro ⟨ν, hν⟩
      obtain ⟨C, A', ⟨rfl, hA'⟩, ⟨f⟩⟩ := cardLe_iff.1 hν
      obtain ⟨eA⟩ := eq_n₀c_iff_equiv.1 hA'
      have hC : Finite ↥C := Finite.of_injective (f.trans eA.symm.toEmbedding)
        (f.trans eA.symm.toEmbedding).injective
      have hk := Finite.card_le_of_embedding (f.trans eA.symm.toEmbedding)
      refine ⟨⟨Nat.card ↥C, by omega⟩, Subtype.ext ?_⟩
      show n₀c (S _) = n₀c C
      have : Finite ↥(S ⟨Nat.card ↥C, by omega⟩) := (hSf _).to_subtype
      apply eq_n₀c_iff_equiv.2
      apply Finite.card_eq.1
      rw [Nat.card_coe_set_eq, hSc]
  refine (Equiv.ofBijective g hg).symm.trans ?_
  have : Finite (↥A ⊕ PUnit.{1}) := inferInstance
  apply Classical.choice
  apply Finite.card_eq.1
  have h1 : Nat.card PUnit.{1} = 1 := Nat.card_unique
  rw [Nat.card_fin, Nat.card_sum, h1, hn]

universe u v

/-- If `α < γ` then `α + 1 ≤ γ`. -/
private theorem emb_sum_unit_of_lt {A : Type u} {C : Type v} (h1 : Nonempty (A ↪ C))
    (h2 : ¬ Nonempty (C ↪ A)) : Nonempty (A ⊕ PUnit.{u + 1} ↪ C) := by
  by_cases hA : Finite A
  · exact emb_sum_unit_iff.2 ⟨h1, h2⟩
  · rw [not_finite_iff_infinite] at hA
    have : Nonempty (A ⊕ PUnit.{u + 1} ↪ A) := by
      rw [← Cardinal.le_def, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_punit]
      exact (Cardinal.add_one_eq (Cardinal.infinite_iff.1 hA)).le
    obtain ⟨f⟩ := this; obtain ⟨g⟩ := h1
    exact ⟨f.trans g⟩

/-- ✱120·6. \(\vdash :(\exists \gamma ).\gamma >\alpha .\gamma \subset tʻ\eta .\supset .\exists !(\alpha +_{c}1)\cap tʻ\eta \)

`γ ⊂ t'η` (`η : Set H`) puts `γ` among the cardinals of `H`; `(α +_c 1) ∩ t'η` is the sum in the
type `H`, the `1` in the type of `α`.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty α]` (otherwise `1 = Λ` in the type of `α`). -/
theorem pm120_6 {α H : Type*} [Nonempty α] {μ : Set (Set α)} {η : Set H} :
    (∃ G : Set (Set H), G >ᶜ μ ∧ G ⊆ typ η) →
      ((μ +ᶜ (one : Set (Set α)) : Set (Set H)) ∩ typ η).Nonempty := by
  rintro ⟨G, hG, -⟩
  obtain ⟨C, A, ⟨rfl, rfl⟩, h1, h2⟩ := cardGt_iff.1 hG
  obtain ⟨f⟩ := emb_sum_unit_of_lt h1 h2
  have hu : Nonempty (PUnit.{1} ↪ α) := ⟨⟨fun _ => Classical.arbitrary α, fun _ _ _ => rfl⟩⟩
  rw [typ_eq_univ, Set.inter_univ, one_eq_ncT.{_, 0}, n₀c_eq_ncT A,
    cardAdd_gen (good_self A H) (Or.inl hu), ncT_nonempty_iff]
  exact ⟨(((Equiv.refl _).sumCongr (Equiv.ofUnique _ _)).toEmbedding.trans f).trans (setEmb C)⟩

/-- ✱120·61. \(\vdash :\exists !\text{N}_{0}\text{C}\cap t^{3}ʻx-\text{NC induct}.\supset .\text{Infin ax}(x)\)

`N₀C ∩ t³'x − NC induct` is `(N₀C ∩ typ3 x) \ NCinduct`. -/
theorem pm120_61 {α : Type*} {x : α} :
    (((N₀C : Set (Set (Set α))) ∩ typ3 x) \ NCinduct).Nonempty → InfinAxAt x := by
  rintro ⟨μ, ⟨⟨A, rfl⟩, -⟩, hA⟩
  rw [infinAxAt_iff, infinAx_iff_infinite]
  by_contra h
  rw [not_infinite_iff_finite] at h
  exact hA (n₀c_mem_NCinduct (Set.toFinite A))

/-- ✱120·611. \(\vdash :\beta \in \text{Cls induct}.\beta \subset \text{ᗡ}ʻP.\supset .\exists !P_{\Delta }ʻ\beta\) -/
theorem pm120_611 {α β : Type*} {P : α → β → Prop} {B : Set β} :
    B ∈ ClsInduct ∧ B ⊆ codom P → (sel P B).Nonempty := by
  rintro ⟨-, hB⟩
  choose f hf using fun y : ↥B => hB y.2
  refine ⟨fun x y => ∃ h : y ∈ B, x = f ⟨y, h⟩, mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩⟩
  · rintro x x' y ⟨⟨h, rfl⟩, ⟨h', rfl⟩⟩; rfl
  · rintro x y ⟨h, rfl⟩; exact hf _
  · ext y; exact ⟨fun ⟨x, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

/-- ✱120·62. \(\vdash :\kappa \in \text{Cls induct}.\Lambda {\sim}\in \kappa .\supset .\exists !{\in}_{\Delta}ʻ\kappa \) -/
theorem pm120_62 {α : Type*} {K : Set (Set α)} :
    K ∈ ClsInduct ∧ Λ ∉ K → (sel memRel K).Nonempty := by
  rintro ⟨hK, h0⟩
  refine pm120_611 ⟨hK, fun A hA => ?_⟩
  by_contra h
  have : A = Λ := by
    rw [Null_eq_empty]; exact Set.eq_empty_iff_forall_notMem.2 fun x hx => h ⟨x, hx⟩
  exact h0 (this ▸ hA)

/-- ✱120·63. \(\vdash .\text{Cls induct} - \overleftarrow{{\in}}ʻ\Lambda \subset \text{Cls}^{2}\, \text{mult} \quad[*120·62.*88·2]\)

`∈⃖'Λ` is `rels memRel Λ` (the classes of which `Λ` is a member). -/
theorem pm120_63 {α : Type*} : (ClsInduct : Set (Set (Set α))) \ rels memRel Λ ⊆ Cls2Mult :=
  fun _ ⟨hK, h0⟩ => pm120_62 ⟨hK, h0⟩

/-- ✱120·64. \(\vdash : \text{Infin ax}.\lor.\text{Mult ax}\)

Both axioms are at the type `α` (PM's proof: if `Infin ax` fails in a type, every class of
classes of that type is inductive, and ✱120·63 gives `Mult ax` there).

**Status.** proved (reading): `Mult ax` is a theorem of Lean (Basic §4, `multAx_holds`); both
axioms are taken at the type `α`. -/
theorem pm120_64 {α : Type*} : InfinAx α ∨ MultAx α :=
  Or.inr (multAx_holds α)

/-- ✱120·7. \(\vdash :\alpha \in \text{Cls induct}.\alpha \subset \beta .\alpha \neq \beta .\supset .\text{Nc}ʻ\alpha < \text{Nc}ʻ\beta \quad[*120·426.*24·6]\)

**Status.** proved (reading): the sides `Nc'α`, `Nc'β` of `<` are `N₀c'α`, `N₀c'β` (✱117·02·03,
normal adjustment). -/
theorem pm120_7 {α : Type*} {A B : Set α} :
    (A ∈ ClsInduct ∧ A ⊆ B) ∧ A ≠ B → n₀c A <ᶜ n₀c B := by
  rintro ⟨⟨hA, hsub⟩, hne⟩
  refine (pm120_426 ⟨⟨hA, hsub⟩, ?_⟩).2
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h
  exact hne (Set.Subset.antisymm hsub h)

/-- ✱120·71. \(\vdash :\rho ,\sigma \in \text{Cls induct}.\equiv .\rho \cup \sigma \in \text{Cls induct}.\equiv .\rho + \sigma \in \text{Cls induct}\)

`ρ ∪ σ` puts `ρ`, `σ` in one type; `ρ + σ` is the arithmetical sum `ρ +ₐ σ`. -/
theorem pm120_71 {α : Type*} {ρ σ : Set α} :
    ((ρ ∈ ClsInduct ∧ σ ∈ ClsInduct) ↔ ρ ∪ σ ∈ ClsInduct) ∧
      (ρ ∪ σ ∈ ClsInduct ↔ ρ +ₐ σ ∈ ClsInduct) := by
  refine ⟨⟨fun ⟨h1, h2⟩ => mem_ClsInduct.2 ((mem_ClsInduct.1 h1).union (mem_ClsInduct.1 h2)),
    fun h => ⟨mem_ClsInduct.2 ((mem_ClsInduct.1 h).subset Set.subset_union_left),
      mem_ClsInduct.2 ((mem_ClsInduct.1 h).subset Set.subset_union_right)⟩⟩, ?_⟩
  rw [mem_ClsInduct, mem_ClsInduct, Set.finite_union, ← Set.finite_coe_iff, ← Set.finite_coe_iff,
    ← Set.finite_coe_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact Finite.of_equiv _ (clsSumEquiv ρ σ).symm
  · intro h
    have : Finite (↥ρ ⊕ ↥σ) := Finite.of_equiv _ (clsSumEquiv ρ σ)
    exact ⟨Finite.of_injective (Sum.inl : ↥ρ → ↥ρ ⊕ ↥σ) Sum.inl_injective,
      Finite.of_injective (Sum.inr : ↥σ → ↥ρ ⊕ ↥σ) Sum.inr_injective⟩

/-- ✱120·72. \(\vdash :\rho ,\sigma \in \text{Cls induct}.\supset .\rho \times \sigma \in \text{Cls induct}\) -/
theorem pm120_72 {α β : Type*} {ρ : Set α} {σ : Set β} :
    ρ ∈ ClsInduct ∧ σ ∈ ClsInduct → ρ ×ₐ σ ∈ ClsInduct := by
  rintro ⟨hρ, hσ⟩
  have : Finite ↥ρ := (mem_ClsInduct.1 hρ).to_subtype
  have : Finite ↥σ := (mem_ClsInduct.1 hσ).to_subtype
  exact mem_ClsInduct.2 (Set.finite_coe_iff.1 (Finite.of_equiv _ (clsTimesEquiv ρ σ).symm))

/-- ✱120·721. \(\vdash \colon\ldotp \exists !\rho .\exists !\sigma .\supset :\rho ,\sigma \in \text{Cls induct}.\equiv .\rho \times \sigma \in \text{Cls induct}\) -/
theorem pm120_721 {α β : Type*} {ρ : Set α} {σ : Set β} :
    ρ.Nonempty ∧ σ.Nonempty → ((ρ ∈ ClsInduct ∧ σ ∈ ClsInduct) ↔ ρ ×ₐ σ ∈ ClsInduct) := by
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  refine ⟨pm120_72, fun h => ?_⟩
  have : Finite ↥(ρ ×ₐ σ) := (mem_ClsInduct.1 h).to_subtype
  have : Finite (↥σ × ↥ρ) := Finite.of_equiv _ (clsTimesEquiv ρ σ)
  exact ⟨mem_ClsInduct.2 (Set.finite_coe_iff.1 (Finite.of_injective (fun a : ↥ρ => ((⟨y, hy⟩ : ↥σ), a))
      (fun a b h => (Prod.mk.inj h).2))),
    mem_ClsInduct.2 (Set.finite_coe_iff.1 (Finite.of_injective (fun b : ↥σ => (b, (⟨x, hx⟩ : ↥ρ)))
      (fun a b h => (Prod.mk.inj h).1)))⟩

/-- ✱120·73. \(\vdash :\rho ,\sigma \in \text{Cls induct}.\supset .(\rho \,\,\text{exp}\,\,\sigma )\in \text{Cls induct} \quad[*120·52.*116·251]\) -/
theorem pm120_73 {α β : Type*} {ρ : Set α} {σ : Set β} :
    ρ ∈ ClsInduct ∧ σ ∈ ClsInduct → clsExp ρ σ ∈ ClsInduct := by
  rintro ⟨hρ, hσ⟩
  have : Finite ↥ρ := (mem_ClsInduct.1 hρ).to_subtype
  have : Finite ↥σ := (mem_ClsInduct.1 hσ).to_subtype
  exact mem_ClsInduct.2 (Set.finite_coe_iff.1 (Finite.of_equiv _ (clsExpEquiv ρ σ).symm))

/-- ✱120·731. \[\begin{align}&\vdash \colon\ldotp \exists !\rho .\exists !\sigma .\rho {\sim}\in 1.\supset :\rho ,\sigma \in \text{Cls induct}.\equiv .(\rho \,\,\text{exp}\,\,\sigma )\in \text{Cls induct}\\ &[*120·56·561·73]\end{align}\] -/
theorem pm120_731 {α β : Type*} {ρ : Set α} {σ : Set β} :
    (ρ.Nonempty ∧ σ.Nonempty) ∧ ρ ∉ (one : Set (Set α)) →
      ((ρ ∈ ClsInduct ∧ σ ∈ ClsInduct) ↔ clsExp ρ σ ∈ ClsInduct) := by
  rintro ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, h1⟩
  refine ⟨pm120_73, fun h => ?_⟩
  have : Finite ↥(clsExp ρ σ) := (mem_ClsInduct.1 h).to_subtype
  have hF : Finite (↥σ → ↥ρ) := Finite.of_equiv _ (clsExpEquiv ρ σ)
  have hab : ∃ a b : ↥ρ, a ≠ b := by
    by_contra hc
    push Not at hc
    exact h1 ⟨x, Set.ext fun z => ⟨fun hz => congrArg Subtype.val (hc ⟨z, hz⟩ ⟨x, hx⟩),
      fun hz => by rw [mem_unitCls.1 hz]; exact hx⟩⟩
  obtain ⟨a, b, hab⟩ := hab
  exact ⟨mem_ClsInduct.2 (Set.finite_coe_iff.1 (Finite.of_injective
      (fun c : ↥ρ => (fun _ => c : ↥σ → ↥ρ)) (fun c c' h => congrFun h ⟨y, hy⟩))),
    mem_ClsInduct.2 (Set.finite_coe_iff.1 (Finite.of_injective (embIndicator a b hab)
      (embIndicator a b hab).injective))⟩

/-- ✱120·74. \(\vdash :\rho \in \text{Cls induct}.\equiv .\text{Cl}ʻ\rho \in \text{Cls induct}\) -/
theorem pm120_74 {α : Type*} {ρ : Set α} : ρ ∈ ClsInduct ↔ cl ρ ∈ ClsInduct := by
  rw [mem_ClsInduct, mem_ClsInduct, cl_eq_powerset]
  refine ⟨Set.Finite.powerset, fun h => ?_⟩
  refine Set.Finite.of_finite_image (h.subset ?_) (fun a _ b _ hab => Set.singleton_injective hab)
  rintro _ ⟨a, ha, rfl⟩
  exact Set.singleton_subset_iff.2 ha

/-- ✱120·741. \(\vdash :sʻ\kappa \in \text{Cls induct}.\supset .\kappa \in \text{Cls induct}.\kappa \subset \text{Cls induct}\) -/
theorem pm120_741 {α : Type*} {K : Set (Set α)} :
    sumCls K ∈ ClsInduct → K ∈ ClsInduct ∧ K ⊆ ClsInduct := by
  intro h
  rw [mem_ClsInduct] at h
  refine ⟨mem_ClsInduct.2 (h.powerset.subset fun A hA x hx => ⟨A, hA, hx⟩),
    fun A hA => mem_ClsInduct.2 (h.subset fun x hx => ⟨A, hA, hx⟩)⟩

/-- ✱120·75. \(\vdash :sʻ\kappa \in \text{Cls induct}.\equiv .\kappa \in \text{Cls induct}.\kappa \subset \text{Cls induct}\) -/
theorem pm120_75 {α : Type*} {K : Set (Set α)} :
    sumCls K ∈ ClsInduct ↔ K ∈ ClsInduct ∧ K ⊆ ClsInduct := by
  refine ⟨pm120_741, fun ⟨hK, hsub⟩ => ?_⟩
  rw [mem_ClsInduct, sumCls_eq_sUnion]
  exact Set.Finite.sUnion (mem_ClsInduct.1 hK) fun A hA => mem_ClsInduct.1 (hsub hA)

/-- ✱120·76. \(\vdash :\kappa \in \text{Cls induct}.\kappa \subset \text{Cls induct}.\supset .{\in}_{\Delta}ʻ\kappa \in \text{Cls induct}\) -/
theorem pm120_76 {α : Type*} {K : Set (Set α)} :
    K ∈ ClsInduct ∧ K ⊆ ClsInduct → sel memRel K ∈ ClsInduct := by
  rintro ⟨hK, hsub⟩
  have hS : Finite ↥(sumCls K) := (mem_ClsInduct.1 (pm120_75.2 ⟨hK, hsub⟩)).to_subtype
  have : Finite ↥K := (mem_ClsInduct.1 hK).to_subtype
  let φ : (α → Set α → Prop) → Set (↥(sumCls K) × ↥K) := fun M => {p | M p.1 p.2}
  rw [mem_ClsInduct]
  refine Set.Finite.of_finite_image (f := φ) (Set.toFinite _) ?_
  intro M hM M' hM' h
  obtain ⟨⟨-, hMP⟩, hMK⟩ := mem_sel_iff.1 hM
  obtain ⟨⟨-, hMP'⟩, hMK'⟩ := mem_sel_iff.1 hM'
  funext x A
  apply propext
  have key : ∀ {N : α → Set α → Prop}, N ⪽ memRel → codom N = K → N x A →
      ∃ (hx : x ∈ sumCls K) (hA : A ∈ K), (⟨⟨x, hx⟩, ⟨A, hA⟩⟩ : ↥(sumCls K) × ↥K) ∈ φ N := by
    intro N hN hNK hxA
    have hA : A ∈ K := hNK ▸ ⟨x, hxA⟩
    exact ⟨⟨A, hA, hN x A hxA⟩, hA, hxA⟩
  constructor
  · intro hxA
    obtain ⟨hx, hA, hp⟩ := key hMP hMK hxA
    have : (⟨⟨x, hx⟩, ⟨A, hA⟩⟩ : ↥(sumCls K) × ↥K) ∈ φ M' := h ▸ hp
    exact this
  · intro hxA
    obtain ⟨hx, hA, hp⟩ := key hMP' hMK' hxA
    have : (⟨⟨x, hx⟩, ⟨A, hA⟩⟩ : ↥(sumCls K) × ↥K) ∈ φ M := h ▸ hp
    exact this

/-- A selection modified at one class `A` to choose `a`. -/
private def modSel {α : Type*} (M : α → Set α → Prop) (A : Set α) (a : α) : α → Set α → Prop :=
  fun x B => (B = A ∧ x = a) ∨ (B ≠ A ∧ M x B)

private theorem modSel_mem {α : Type*} {M : α → Set α → Prop} {L : Set (Set α)} {A : Set α}
    {a : α} (hM : M ∈ sel memRel L) (hA : A ∈ L) (ha : a ∈ A) : modSel M A a ∈ sel memRel L := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_sel_iff.1 hM
  have h1' := mem_arrow_one_Cls.1 h1
  refine mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩
  · rintro x y B ⟨(⟨hBA, rfl⟩ | ⟨hB, hx⟩), (⟨hBA', rfl⟩ | ⟨hB', hy⟩)⟩
    · rfl
    · exact absurd hBA hB'
    · exact absurd hBA' hB
    · exact h1' x y B ⟨hx, hy⟩
  · rintro x B (⟨rfl, rfl⟩ | ⟨-, hx⟩)
    · exact ha
    · exact h2 x B hx
  · ext B
    constructor
    · rintro ⟨x, ⟨rfl, -⟩ | ⟨-, hx⟩⟩
      · exact hA
      · rw [← h3]; exact ⟨x, hx⟩
    · intro hB
      by_cases hBA : B = A
      · exact ⟨a, Or.inl ⟨hBA, rfl⟩⟩
      · rw [← h3] at hB
        obtain ⟨x, hx⟩ := hB
        exact ⟨x, Or.inr ⟨hBA, hx⟩⟩

/-- A selection choosing `f B` in each `B ∈ K` and agreeing with `M` outside `K`. -/
private def chooseSel {α : Type*} (M : α → Set α → Prop) (K : Set (Set α))
    (f : ∀ B, B ∈ K → α) : α → Set α → Prop :=
  fun x B => (∃ hB : B ∈ K, x = f B hB) ∨ (B ∉ K ∧ M x B)

private theorem chooseSel_mem {α : Type*} {M : α → Set α → Prop} {K L : Set (Set α)}
    {f : ∀ B, B ∈ K → α} (hM : M ∈ sel memRel L) (hKL : K ⊆ L) (hf : ∀ B hB, f B hB ∈ B) :
    chooseSel M K f ∈ sel memRel L := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_sel_iff.1 hM
  have h1' := mem_arrow_one_Cls.1 h1
  refine mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩
  · rintro x y B ⟨(⟨hB, rfl⟩ | ⟨hB, hx⟩), (⟨hB', rfl⟩ | ⟨hB', hy⟩)⟩
    · rfl
    · exact absurd hB hB'
    · exact absurd hB' hB
    · exact h1' x y B ⟨hx, hy⟩
  · rintro x B (⟨hB, rfl⟩ | ⟨-, hx⟩)
    · exact hf B hB
    · exact h2 x B hx
  · ext B
    constructor
    · rintro ⟨x, ⟨hB, -⟩ | ⟨-, hx⟩⟩
      · exact hKL hB
      · rw [← h3]; exact ⟨x, hx⟩
    · intro hB
      by_cases hBK : B ∈ K
      · exact ⟨f B hBK, Or.inl ⟨hBK, rfl⟩⟩
      · rw [← h3] at hB
        obtain ⟨x, hx⟩ := hB
        exact ⟨x, Or.inr ⟨hBK, hx⟩⟩

/-- ✱120·761. \(\vdash :\exists !{\in}_{\Delta}ʻ\kappa .{\in}_{\Delta}ʻ\kappa \in \text{Cls induct}.\supset .\kappa \subset \text{Cls induct}\) -/
theorem pm120_761 {α : Type*} {K : Set (Set α)} :
    (sel memRel K).Nonempty ∧ sel memRel K ∈ ClsInduct → K ⊆ ClsInduct := by
  rintro ⟨⟨M, hM⟩, hfin⟩ A hA
  have : Finite ↥(sel memRel K) := (mem_ClsInduct.1 hfin).to_subtype
  rw [mem_ClsInduct, ← Set.finite_coe_iff]
  refine Finite.of_injective (fun a : ↥A => (⟨modSel M A a, modSel_mem hM hA a.2⟩ :
    ↥(sel memRel K))) ?_
  intro a b h
  have h' : modSel M A a a A = modSel M A b a A :=
    congrFun (congrFun (congrArg Subtype.val h) (a : α)) A
  have : modSel M A b a A := by rw [← h']; exact Or.inl ⟨rfl, rfl⟩
  rcases this with ⟨-, h⟩ | ⟨hne, -⟩
  · exact Subtype.ext h
  · exact absurd rfl hne

/-- In a class of classes none of which is `Λ` or a unit class, each member has two members. -/
private theorem two_of_not_one {α : Type*} {K : Set (Set α)} (h0 : Λ ∉ K)
    (h1 : ¬ ((one : Set (Set α)) ∩ K).Nonempty) :
    ∀ B, B ∈ K → ∃ x y, x ∈ B ∧ y ∈ B ∧ x ≠ y := by
  intro B hB
  have hne : B.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact h0 (by rw [Null_eq_empty, ← h]; exact hB)
  obtain ⟨x, hx⟩ := hne
  by_contra h
  push Not at h
  exact h1 ⟨B, ⟨x, Set.ext fun z => ⟨fun hz => h z x hz hx, fun hz => by
    rw [mem_unitCls.1 hz]; exact hx⟩⟩, hB⟩

/-- The core of ✱120·762–·767: `κ` embeds in `∈_Δ'λ` (`κ ⊂ λ`, `∃!∈_Δ'λ`). -/
private theorem emb_sel {α : Type*} {K L : Set (Set α)} (h0 : Λ ∉ K)
    (h1 : ¬ ((one : Set (Set α)) ∩ K).Nonempty) (hKL : K ⊆ L) (hL : (sel memRel L).Nonempty) :
    Nonempty (↥K ↪ ↥(sel memRel L)) := by
  obtain ⟨M, hM⟩ := hL
  choose fx fy hfx hfy hxy using fun B : Set α => fun hB : B ∈ K => two_of_not_one h0 h1 B hB
  have hbase := chooseSel_mem hM hKL hfx
  refine ⟨⟨fun A => ⟨modSel (chooseSel M K fx) A (fy A A.2), modSel_mem hbase (hKL A.2)
    (hfy A A.2)⟩, fun A B h => ?_⟩⟩
  have h' : modSel (chooseSel M K fx) A (fy A A.2) (fy A A.2) A =
      modSel (chooseSel M K fx) B (fy B B.2) (fy A A.2) A :=
    congrFun (congrFun (congrArg Subtype.val h) (fy A A.2)) A
  have : modSel (chooseSel M K fx) B (fy B B.2) (fy A A.2) A := by
    rw [← h']; exact Or.inl ⟨rfl, rfl⟩
  rcases this with ⟨hAB, -⟩ | ⟨-, (⟨_, hc⟩ | ⟨hc, -⟩)⟩
  · exact Subtype.ext hAB
  · exact absurd hc.symm (hxy A A.2)
  · exact absurd A.2 hc

/-- ✱120·762. \(\vdash :\kappa \in \text{Cls induct}.\Lambda {\sim}\in \kappa .{\sim}\exists !1\cap \kappa .\supset .(\exists R,S).R,S\in {\in}_{\Delta}ʻ\kappa .R\dot{\cap} S=\dot{\Lambda} \) -/
theorem pm120_762 {α : Type*} {K : Set (Set α)} :
    (K ∈ ClsInduct ∧ Λ ∉ K) ∧ ¬ ((one : Set (Set α)) ∩ K).Nonempty →
      ∃ R S : α → Set α → Prop, Mem2 R S (sel memRel K) ∧ R ⩀ S = rNull := by
  rintro ⟨⟨hK, h0⟩, h1⟩
  obtain ⟨M, hM⟩ := pm120_62 ⟨hK, h0⟩
  choose fx fy hfx hfy hxy using fun B : Set α => fun hB : B ∈ K => two_of_not_one h0 h1 B hB
  have hM3 := (mem_sel_iff.1 hM).2
  refine ⟨chooseSel M K fx, chooseSel M K fy, ⟨chooseSel_mem hM subset_rfl hfx,
    chooseSel_mem hM subset_rfl hfy⟩, ?_⟩
  funext x B
  apply propext
  refine ⟨?_, fun h => absurd h (rNull_apply x B)⟩
  rintro ⟨(⟨hB, rfl⟩ | ⟨hB, hx⟩), (⟨hB', hy⟩ | ⟨hB', -⟩)⟩
  · exact (hxy B hB hy).elim
  · exact absurd hB hB'
  · exact absurd hB' hB
  · exact absurd (hM3 ▸ ⟨x, hx⟩ : B ∈ K) hB

/-- ✱120·764. \[\begin{align}&\vdash :\kappa \in \text{Cls induct}.\Lambda {\sim}\in \kappa .{\sim}\exists !(1\cap \kappa ).\supset .\text{Nc}ʻ{\in}_{\Delta}ʻ\kappa \geq \text{Nc}ʻ\kappa \\ &[*120·762.*117·681]\end{align}\]

**Status.** proved (reading): the sides `Nc'∈_Δ'κ`, `Nc'κ` of `≥` are `N₀c'∈_Δ'κ`, `N₀c'κ`
(✱117·02·03 and the note to ✱117·06, normal adjustment). -/
theorem pm120_764 {α : Type*} {K : Set (Set α)} :
    (K ∈ ClsInduct ∧ Λ ∉ K) ∧ ¬ ((one : Set (Set α)) ∩ K).Nonempty →
      n₀c (sel memRel K) ≥ᶜ n₀c K := by
  rintro ⟨⟨hK, h0⟩, h1⟩
  exact cardGe_n₀c.2 (emb_sel h0 h1 subset_rfl (pm120_62 ⟨hK, h0⟩))

/-- ✱120·765. \[\begin{align}\vdash :\kappa \in \text{Cls induct}.\Lambda {\sim}\in \kappa .{\sim}&\exists !(1\cap \kappa ).\kappa \subset \lambda .\exists !{\in}_{\Delta}ʻ\lambda .\supset .\\ &\text{Nc}ʻ{\in}_{\Delta}ʻ\lambda \geq \text{Nc}ʻ\kappa \quad[*120·762.*117·684]\end{align}\]

**Status.** proved (reading): the sides of `≥` are `N₀c'∈_Δ'λ`, `N₀c'κ` (✱117·02·03, normal
adjustment). -/
theorem pm120_765 {α : Type*} {K L : Set (Set α)} :
    (((K ∈ ClsInduct ∧ Λ ∉ K) ∧ ¬ ((one : Set (Set α)) ∩ K).Nonempty) ∧ K ⊆ L) ∧
        (sel memRel L).Nonempty →
      n₀c (sel memRel L) ≥ᶜ n₀c K := by
  rintro ⟨⟨⟨⟨-, h0⟩, h1⟩, hKL⟩, hL⟩
  exact cardGe_n₀c.2 (emb_sel h0 h1 hKL hL)

/-- ✱120·766. \[\begin{align}\vdash :\lambda {\sim}\in \text{Cls induct}.\Lambda {\sim}\in \lambda.{\sim}\exists !(1\cap \lambda ).&\exists !{\in}_{\Delta}ʻ\lambda .\supset .\\ &\text{Nc}ʻ{\in}_{\Delta}ʻ\lambda {\sim}\in \text{NC induct}\end{align}\]

`Nc'∈_Δ'λ` is taken homogeneous (`N₀c'∈_Δ'λ`), as in ✱120·21 and the Df ✱124·021 for `NC refl`:
in a finite type `Nc'∈_Δ'λ` could be `Λ`, which is an inductive cardinal there.

**Status.** proved (reading): `Nc'∈_Δ'λ ∼∈ NC induct` is read with `N₀c'∈_Δ'λ` (as ✱120·21,
✱124·021); with `Nc'` in an arbitrary type the proposition fails for a finite type. -/
theorem pm120_766 {α : Type*} {L : Set (Set α)} :
    ((L ∉ ClsInduct ∧ Λ ∉ L) ∧ ¬ ((one : Set (Set α)) ∩ L).Nonempty) ∧
        (sel memRel L).Nonempty →
      n₀c (sel memRel L) ∉ NCinduct := by
  rintro ⟨⟨⟨hL, h0⟩, h1⟩, hne⟩ hi
  obtain ⟨f⟩ := emb_sel h0 h1 subset_rfl hne
  have : Finite ↥(sel memRel L) := finite_of_N₀C_inductive hi
  exact hL (mem_ClsInduct.2 (Set.finite_coe_iff.1 (Finite.of_injective f f.injective)))

/-- ✱120·767. \[\begin{align}&\vdash :{\in}_{\Delta}ʻ\lambda \in \text{Cls induct}.\Lambda {\sim}\in \lambda .{\sim}\exists !(1\cap \lambda ).\exists !{\in}_{\Delta}ʻ\lambda .\supset .\lambda \in \text{Cls induct}\\ &[*120·766.\text{Transp}]\end{align}\] -/
theorem pm120_767 {α : Type*} {L : Set (Set α)} :
    ((sel memRel L ∈ ClsInduct ∧ Λ ∉ L) ∧ ¬ ((one : Set (Set α)) ∩ L).Nonempty) ∧
        (sel memRel L).Nonempty →
      L ∈ ClsInduct := by
  rintro ⟨⟨⟨hs, h0⟩, h1⟩, hne⟩
  obtain ⟨f⟩ := emb_sel h0 h1 subset_rfl hne
  have : Finite ↥(sel memRel L) := (mem_ClsInduct.1 hs).to_subtype
  exact mem_ClsInduct.2 (Set.finite_coe_iff.1 (Finite.of_injective f f.injective))

/-- ✱120·77. \[\begin{align}\vdash \colon\ldotp \Lambda {\sim}\in \kappa .{\sim}&\exists !(1\cap \kappa ).\exists !{\in}_{\Delta}ʻ\kappa .\supset :\\ &{\in}_{\Delta}ʻ\kappa \in \text{Cls induct}.\equiv .\kappa \in \text{Cls induct}.\kappa \subset \text{Cls induct}\\ &[*120·76·761·767]\end{align}\] -/
theorem pm120_77 {α : Type*} {K : Set (Set α)} :
    (Λ ∉ K ∧ ¬ ((one : Set (Set α)) ∩ K).Nonempty) ∧ (sel memRel K).Nonempty →
      (sel memRel K ∈ ClsInduct ↔ K ∈ ClsInduct ∧ K ⊆ ClsInduct) := by
  rintro ⟨⟨h0, h1⟩, hne⟩
  exact ⟨fun h => ⟨pm120_767 ⟨⟨⟨h, h0⟩, h1⟩, hne⟩, pm120_761 ⟨hne, h⟩⟩, pm120_76⟩

/-!
## [✱121] Intervals

*(Vol. 2, p. 233)*

> *Summary of* *121.
>
> …

**Lean reading.** The intervals `P(x–y)`, `P(x⊣y)`, `P(x⟝y)`, `P(x⊢⊣y)` are `itvOO`, `itvOC`,
`itvCO`, `itvCC` (homogeneous `P`); `P_ν` is `Pnu P ν`, the type `β` of `ν` free and the `1` of
`ν +_c 1` in it (`Pnu_iff`: `P(x⊢⊣y) sm β + 1` where `ν = N₀c'β`, and `1` exists in the type of `ν`);
`finid'P`, `fin'P` take the type of their apparent `ν` explicitly; `ν_P` is the relation `nuP ν`
(`ψ(ν_P)` is `Desc (nuP ν) P ψ`). The `1` of ✱121·3 is PM's `I`. Where an empty type of `ν` would
make `P₀` or `P₁` null (✱121·301·302·304·308·31) `[Nonempty β]` is added; subscripts and sides that
are arithmetical (`ν +_c 1` in ✱121·272·273·331, `μ +_c ν`, `μ ×_c ν`) are in adequate types (IIT).
The interval calculus (✱121·1–·327, ·33, ·37–·39, ·4–·42) is proved, with the interval identities
for `(Cls → 1) ∪ (1 → Cls)` (✱121·371–·374), the cycle identities (✱121·382–·384), the finiteness
of the intervals of a many-one or one-many relation (✱121·44–·481: the posterity of a term of a
cycle is a periodic orbit) and ✱121·7. The arithmetic of the `P_ν` of a one-many or many-one
relation without cycles (✱121·331–·361) is proved by reading `xP_νy` as `x (P^k) y` for the number
`k` of members of a finite class with cardinal `ν` (`Pnu_pwr`), and PM's analysis of a cycle by the
term `a` preceding `z` (✱121·43–·434) by the orbit of `z` under the function `R` is on the cycle
(`cycle_orbit`). `finid'P`, `fin'P` are identified with `Potid'P`, `Pot'P` (✱121·5–·52)
through the powers `P^k` (`mem_potid_iff`, `mem_pot_iff'`); the terms `ν_P` (✱121·6–·66) are
computed by `Pnu_sub_one` (`x P_{ν −_c 1} y` iff `ν = N₀c'ξ` for an existent `ξ` similar to
`P(x⊢⊣y)`); ✱121·71·72 use the generations of ✱93 only through `gen_beg` (a member of a
generation is reached from a beginning by a power of `R`), with ✱121·7 and ✱121·381·46. In
these statements the type of the apparent `ν` of `finid'P`, `fin'P` (✱121·5–·52, ·61·62) is one
into which the type of `C'P` injects (Prefatory Statement, VII: the type is taken high enough),
real variables `ν`, `μ` have their own types, and the hypotheses `[Nonempty …]` (for the `1` of
`P_ν`) and IIT (for arithmetical subscripts and constants) are added where the statement would
otherwise fail (✱121·35·351·5·51·601·602·632·633·634·638·65·66).

**Status.** proved (all propositions; ✱121·27·271·272·273·3·301·302·303·304·308·31·331·332·333·
35·351·36·5·501·502·51·52·601·602·61·62·632·633·634·638·641·65·66 proved (reading), see their
docstrings; ✱121·01·011·012·013·02·03·031·04 definition)
-/

/-! ### Helpers for ✱121 -/

private theorem po_cnv {α : Type*} {P : α → α → Prop} {a b : α} : po P˘ a b ↔ po P b a := by
  rw [po_iff_transGen, po_iff_transGen]
  exact Relation.transGen_swap

private theorem anc_cnv {α : Type*} {P : α → α → Prop} {a b : α} : anc P˘ a b ↔ anc P b a :=
  ancCnv_iff.symm

private theorem fld_of_po_left {α : Type*} {P : α → α → Prop} {a b : α} (h : po P a b) :
    a ∈ fld P := by
  rw [po_iff_transGen] at h
  obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 h
  exact ⟨c, Or.inl hc⟩

private theorem fld_of_po_right {α : Type*} {P : α → α → Prop} {a b : α} (h : po P a b) :
    b ∈ fld P := by
  rw [po_iff_transGen] at h
  obtain ⟨c, -, hc⟩ := Relation.TransGen.tail'_iff.1 h
  exact ⟨c, Or.inr hc⟩

private theorem fld_of_anc_left {α : Type*} {P : α → α → Prop} {a b : α} (h : anc P a b) :
    a ∈ fld P := h.1

private theorem fld_of_anc_right {α : Type*} {P : α → α → Prop} {a b : α} (h : anc P a b) :
    b ∈ fld P := by
  rcases anc_iff_po.1 h with ⟨rfl, ha⟩ | h
  · exact ha
  · exact fld_of_po_right h

private theorem anc_refl {α : Type*} {P : α → α → Prop} {a : α} (h : a ∈ fld P) : anc P a a :=
  anc_iff_po.2 (Or.inl ⟨rfl, h⟩)

private theorem anc_trans {α : Type*} {P : α → α → Prop} {a b c : α} (h1 : anc P a b)
    (h2 : anc P b c) : anc P a c := by
  rw [anc_iff_reflTransGen] at *
  exact ⟨h1.1, h1.2.trans h2.2⟩

private theorem po_of_anc_po {α : Type*} {P : α → α → Prop} {a b c : α} (h1 : anc P a b)
    (h2 : po P b c) : po P a c := by
  rw [anc_iff_reflTransGen] at h1
  rw [po_iff_transGen] at *
  exact Relation.TransGen.trans_right h1.2 h2

private theorem po_of_po_anc {α : Type*} {P : α → α → Prop} {a b c : α} (h1 : po P a b)
    (h2 : anc P b c) : po P a c := by
  rw [anc_iff_reflTransGen] at h2
  rw [po_iff_transGen] at *
  exact Relation.TransGen.trans_left h1 h2.2

private theorem anc_of_po {α : Type*} {P : α → α → Prop} {a b : α} (h : po P a b) :
    anc P a b := anc_iff_po.2 (Or.inr h)

/-- ✱121·01 (Df). \(P(x \unicode{x2013} y) = \overleftarrow{P}_{\text{po}}ʻx \cap \overrightarrow{P}_{\text{po}}ʻy \quad\text{Df}\) -/
theorem pm121_01 {α : Type*} {P : α → α → Prop} {x y : α} :
    itvOO P x y = rels (po P) x ∩ refs (po P) y :=
  rfl

/-- ✱121·011 (Df). \(P(x \dashv y) = \overleftarrow{P}_{\text{po}} ʻx \cap \overrightarrow{P}_{*} ʻy \quad\text{Df}\) -/
theorem pm121_011 {α : Type*} {P : α → α → Prop} {x y : α} :
    itvOC P x y = rels (po P) x ∩ refs (anc P) y :=
  rfl

/-- ✱121·012 (Df). \(P(x \unicode{x27dd} y) = \overleftarrow{P}_{*} ʻx \cap \overrightarrow{P}_{\text{po}} ʻy \quad\text{Df}\) -/
theorem pm121_012 {α : Type*} {P : α → α → Prop} {x y : α} :
    itvCO P x y = rels (anc P) x ∩ refs (po P) y :=
  rfl

/-- ✱121·013 (Df). \(P(x \vdash\dashv y) = \overleftarrow{P}_{*} ʻx \cap \overrightarrow{P}_{*} ʻy \quad\text{Df}\) -/
theorem pm121_013 {α : Type*} {P : α → α → Prop} {x y : α} :
    itvCC P x y = rels (anc P) x ∩ refs (anc P) y :=
  rfl

/-- ✱121·02 (Df). \(P_\nu = \hat{x} \hat{y} \{\text{N}_0\text{c} ʻP (x \vdash\dashv y) = \nu +_{c} 1\} \quad\text{Df}\)

The type `β` of `ν` is free (Prefatory Statement, VI); the `1` is in the type of `ν`. -/
theorem pm121_02 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    Pnu P ν = fun x y => n₀c (itvCC P x y) = ν +ᶜ (one : Set (Set β)) :=
  rfl

/-- ✱121·03 (Df). \(\text{finid} ʻP = \hat{R} \{(\exists \nu ) . \nu \in \text{NC induct} - \iota ʻ\Lambda . R = P_{\nu }\} \quad\text{Df}\)

The type `β` of the apparent variable `ν` is the explicit argument of `finid`. -/
theorem pm121_03 {α β : Type*} {P : α → α → Prop} :
    finid β P = {R | ∃ ν : Set (Set β), ν ∈ NCinduct \ ι Λ ∧ R = Pnu P ν} :=
  rfl

/-- ✱121·031 (Df). \(\text{fin} ʻP = \hat{R} \{(\exists \nu ). \nu \in \text{NC induct} - \iota ʻ\Lambda - \iota ʻ0 . R = P_{\nu }\} \quad\text{Df}\) -/
theorem pm121_031 {α β : Type*} {P : α → α → Prop} :
    fin β P = {R | ∃ ν : Set (Set β), ν ∈ (NCinduct \ ι Λ) \ ι zero ∧ R = Pnu P ν} :=
  rfl

/-- ✱121·04 (Df). \(\nu _{P} = \breve{P} _{\nu -_{c} 1} ʻBʻP \quad\text{Df}\)

The Df defines the relation `nuP ν` of `ν_P` to `P` (`Defs/Part3`); `P̆_{ν −_c 1}` is
`(P_{ν −_c 1})˘`. -/
theorem pm121_04 {α β : Type*} {ν : Set (Set β)} :
    (nuP ν : α → (α → α → Prop) → Prop) = descRel (fun v P => Desc Beg P (fun b =>
      (Pnu P (ν -ᶜ (one : Set (Set β)) : Set (Set β)))˘ v b)) :=
  rfl

/-- ✱121·1. \(\vdash : z \in P (x \unicode{x2013} y) . \equiv . xP_{\text{po}}z . zP_{\text{po}}y \quad[(*121·01)]\) -/
theorem pm121_1 {α : Type*} {P : α → α → Prop} {x y z : α} :
    z ∈ itvOO P x y ↔ po P x z ∧ po P z y :=
  Iff.rfl

/-- ✱121·101. \(\vdash : z \in P (x \dashv y) . \equiv . xP_{\text{po}}z . zP_{*}y\) -/
theorem pm121_101 {α : Type*} {P : α → α → Prop} {x y z : α} :
    z ∈ itvOC P x y ↔ po P x z ∧ anc P z y :=
  Iff.rfl

/-- ✱121·102. \(\vdash : z \in P (x \unicode{x27dd} y) . \equiv . xP_{*}z . zP_{\text{po}}y\) -/
theorem pm121_102 {α : Type*} {P : α → α → Prop} {x y z : α} :
    z ∈ itvCO P x y ↔ anc P x z ∧ po P z y :=
  Iff.rfl

/-- ✱121·103. \(\vdash : z \in P (x \vdash\dashv y) . \equiv . xP_{*}z . zP_{*}y\) -/
theorem pm121_103 {α : Type*} {P : α → α → Prop} {x y z : α} :
    z ∈ itvCC P x y ↔ anc P x z ∧ anc P z y :=
  Iff.rfl

/-- ✱121·11. \(\vdash : xP_{\nu }y . \equiv . \text{N}_0\text{c} ʻP (x \vdash\dashv y) = \nu +_{c} 1 \quad[(*121·02)]\) -/
theorem pm121_11 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} {x y : α} :
    Pnu P ν x y ↔ n₀c (itvCC P x y) = (ν +ᶜ (one : Set (Set β)) : Set (Set α)) :=
  Iff.rfl

/-- ✱121·12. \(\vdash : R \in \text{finid} ʻP . \equiv . (\exists \nu ) . \nu \in \text{NC induct} - \iota ʻ\Lambda . R = P_\nu \quad[(*121·03)]\) -/
theorem pm121_12 {α β : Type*} {P R : α → α → Prop} :
    R ∈ finid β P ↔ ∃ ν : Set (Set β), ν ∈ NCinduct \ ι Λ ∧ R = Pnu P ν :=
  Iff.rfl

/-- ✱121·121. \(\vdash : R \in \text{fin} ʻP . \equiv . (\exists \nu ) . \nu \in \text{NC induct} - \iota ʻ\Lambda - \iota ʻ0 . R = P_\nu \quad[(*121·031)]\) -/
theorem pm121_121 {α β : Type*} {P R : α → α → Prop} :
    R ∈ fin β P ↔ ∃ ν : Set (Set β), ν ∈ (NCinduct \ ι Λ) \ ι zero ∧ R = Pnu P ν :=
  Iff.rfl

/-- ✱121·13. \(\vdash : f (\nu _{P}) . \equiv . f(\breve{P} _{\nu -_{c} 1} ʻBʻP) \quad[(*121·04)]\)

`f(P̆_{ν−_c1}'B'P)` is the double description `Desc2` (the inner `B'P` with the smaller scope). -/
theorem pm121_13 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} {f : α → Prop} :
    Desc (nuP ν) P f ↔ Desc2 (Pnu P (ν -ᶜ (one : Set (Set β)) : Set (Set β)))˘ Beg P f :=
  desc_nuP ν P f

/-- ✱121·14. \(\vdash . P (x \unicode{x2013} y) = \breve{P} (y \unicode{x2013} x) \quad[*121·1 . *91·53]\) -/
theorem pm121_14 {α : Type*} {P : α → α → Prop} {x y : α} : itvOO P x y = itvOO P˘ y x := by
  ext z; simp only [pm121_1, po_cnv]; exact And.comm

/-- ✱121·141. \(\vdash . P (x \dashv y) = \breve{P} (y \unicode{x27dd} x)\) -/
theorem pm121_141 {α : Type*} {P : α → α → Prop} {x y : α} : itvOC P x y = itvCO P˘ y x := by
  ext z; simp only [pm121_101, pm121_102, po_cnv, anc_cnv]; exact And.comm

/-- ✱121·142. \(\vdash . P (x \unicode{x27dd} y) = \breve{P} (y \dashv x)\) -/
theorem pm121_142 {α : Type*} {P : α → α → Prop} {x y : α} : itvCO P x y = itvOC P˘ y x := by
  ext z; simp only [pm121_101, pm121_102, po_cnv, anc_cnv]; exact And.comm

/-- ✱121·143. \(\vdash . P (x \vdash\dashv y) = \breve{P} (y \vdash\dashv x)\) -/
theorem pm121_143 {α : Type*} {P : α → α → Prop} {x y : α} : itvCC P x y = itvCC P˘ y x := by
  ext z; simp only [pm121_103, anc_cnv]; exact And.comm

/-- ✱121·2. \(\vdash : {\sim} (xP_{\text{po}}x) . \supset . x {\sim} \in P (x \unicode{x2013} y) \quad[*121·1]\) -/
theorem pm121_2 {α : Type*} {P : α → α → Prop} {x y : α} : ¬ po P x x → x ∉ itvOO P x y :=
  fun h hx => h hx.1

/-- ✱121·201. \(\vdash : {\sim} (yP_{\text{po}}y) . \supset . y {\sim} \in P (x \unicode{x2013} y)\) -/
theorem pm121_201 {α : Type*} {P : α → α → Prop} {x y : α} : ¬ po P y y → y ∉ itvOO P x y :=
  fun h hy => h hy.2

/-- ✱121·202. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\supset .x,y{\sim}\in P(x\unicode{x2013}y) \quad[*121·2·201]\)

`x, y ∼∈ α` is `x ∼∈ α . y ∼∈ α`. -/
theorem pm121_202 {α : Type*} {P : α → α → Prop} {x y : α} :
    po P ⪽ J → x ∉ itvOO P x y ∧ y ∉ itvOO P x y :=
  fun h => ⟨pm121_2 fun hx => h x x hx rfl, pm121_201 fun hy => h y y hy rfl⟩

/-- ✱121·22. \(\vdash :xP_{\text{po}}y.\equiv .x\in P(x\unicode{x27dd} y).\equiv .\exists !P(x\unicode{x27dd} y)\) -/
theorem pm121_22 {α : Type*} {P : α → α → Prop} {x y : α} :
    (po P x y ↔ x ∈ itvCO P x y) ∧ (x ∈ itvCO P x y ↔ (itvCO P x y).Nonempty) := by
  refine ⟨⟨fun h => ⟨anc_refl (fld_of_po_left h), h⟩, fun h => h.2⟩,
    ⟨fun h => ⟨x, h⟩, fun ⟨z, hz⟩ => ⟨anc_refl hz.1.1, po_of_anc_po hz.1 hz.2⟩⟩⟩

/-- ✱121·23. \(\vdash :xP_{*}y.\equiv .x,y\in P(x\vdash\dashv y).\equiv .\exists !P(x\vdash\dashv y)\)

`x, y ∈ α` is `Mem2 x y α`. -/
theorem pm121_23 {α : Type*} {P : α → α → Prop} {x y : α} :
    (anc P x y ↔ Mem2 x y (itvCC P x y)) ∧ (Mem2 x y (itvCC P x y) ↔ (itvCC P x y).Nonempty) := by
  refine ⟨⟨fun h => ⟨⟨anc_refl h.1, h⟩, ⟨h, anc_refl (fld_of_anc_right h)⟩⟩, fun h => h.1.2⟩,
    ⟨fun h => ⟨x, h.1⟩, fun ⟨z, hz⟩ => ?_⟩⟩
  have h := anc_trans hz.1 hz.2
  exact ⟨⟨anc_refl h.1, h⟩, ⟨h, anc_refl (fld_of_anc_right h)⟩⟩

/-- ✱121·231. \(\vdash :x\in CʻP.\equiv .x\in P(x\vdash\dashv x).\equiv .\exists !P(x\vdash\dashv x) \quad[*121·23.*90·12]\) -/
theorem pm121_231 {α : Type*} {P : α → α → Prop} {x : α} :
    (x ∈ fld P ↔ x ∈ itvCC P x x) ∧ (x ∈ itvCC P x x ↔ (itvCC P x x).Nonempty) := by
  refine ⟨⟨fun h => ⟨anc_refl h, anc_refl h⟩, fun h => h.1.1⟩, ⟨fun h => ⟨x, h⟩, fun ⟨z, hz⟩ => ?_⟩⟩
  exact ⟨anc_refl hz.1.1, anc_refl hz.1.1⟩

/-- ✱121·24. \(\vdash :xP_{\text{po}}y.\supset .P(x\dashv y)=P(x\unicode{x2013}y)\cup \iota ʻy\) -/
theorem pm121_24 {α : Type*} {P : α → α → Prop} {x y : α} :
    po P x y → itvOC P x y = itvOO P x y ∪ ι y := by
  intro h
  ext z
  simp only [pm121_101, Set.mem_union, pm121_1, mem_unitCls]
  constructor
  · rintro ⟨h1, h2⟩
    rcases anc_iff_po.1 h2 with ⟨rfl, -⟩ | h2
    · exact Or.inr rfl
    · exact Or.inl ⟨h1, h2⟩
  · rintro (⟨h1, h2⟩ | rfl)
    · exact ⟨h1, anc_of_po h2⟩
    · exact ⟨h, anc_refl (fld_of_po_right h)⟩

/-- ✱121·241. \(\vdash :xP_{\text{po}}y.\supset .P(x \unicode{x27dd} y)=P(x\unicode{x2013}y)\cup \iota ʻx\) -/
theorem pm121_241 {α : Type*} {P : α → α → Prop} {x y : α} :
    po P x y → itvCO P x y = itvOO P x y ∪ ι x := by
  intro h
  ext z
  simp only [pm121_102, Set.mem_union, pm121_1, mem_unitCls]
  constructor
  · rintro ⟨h1, h2⟩
    rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h1
    · exact Or.inr rfl
    · exact Or.inl ⟨h1, h2⟩
  · rintro (⟨h1, h2⟩ | rfl)
    · exact ⟨anc_of_po h1, h2⟩
    · exact ⟨anc_refl (fld_of_po_left h), h⟩

/-- ✱121·242. \[\begin{align}\vdash :xP_{*}y.\supset .P(x\vdash\dashv y)&=P(x\dashv y)\cup \iota ʻx=P(x \unicode{x27dd} y)\cup \iota ʻy\\ &=P(x-y)\cup \iota ʻx\cup \iota ʻy\end{align}\]

The chain of three equations is the conjunction of its links. -/
theorem pm121_242 {α : Type*} {P : α → α → Prop} {x y : α} :
    anc P x y →
      (itvCC P x y = itvOC P x y ∪ ι x ∧ itvOC P x y ∪ ι x = itvCO P x y ∪ ι y) ∧
        itvCO P x y ∪ ι y = itvOO P x y ∪ ι x ∪ ι y := by
  intro h
  have hx := h.1
  have hy := fld_of_anc_right h
  have e1 : itvCC P x y = itvOC P x y ∪ ι x := by
    ext z
    simp only [pm121_103, pm121_101, Set.mem_union, mem_unitCls]
    constructor
    · rintro ⟨h1, h2⟩
      rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h1
      · exact Or.inr rfl
      · exact Or.inl ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | rfl)
      · exact ⟨anc_of_po h1, h2⟩
      · exact ⟨anc_refl hx, h⟩
  have e2 : itvCC P x y = itvCO P x y ∪ ι y := by
    ext z
    simp only [pm121_103, pm121_102, Set.mem_union, mem_unitCls]
    constructor
    · rintro ⟨h1, h2⟩
      rcases anc_iff_po.1 h2 with ⟨rfl, -⟩ | h2
      · exact Or.inr rfl
      · exact Or.inl ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | rfl)
      · exact ⟨h1, anc_of_po h2⟩
      · exact ⟨h, anc_refl hy⟩
  have e3 : itvCC P x y = itvOO P x y ∪ ι x ∪ ι y := by
    ext z
    simp only [pm121_103, pm121_1, Set.mem_union, mem_unitCls]
    constructor
    · rintro ⟨h1, h2⟩
      rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h1
      · exact Or.inl (Or.inr rfl)
      · rcases anc_iff_po.1 h2 with ⟨rfl, -⟩ | h2
        · exact Or.inr rfl
        · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · rintro ((⟨h1, h2⟩ | rfl) | rfl)
      · exact ⟨anc_of_po h1, anc_of_po h2⟩
      · exact ⟨anc_refl hx, h⟩
      · exact ⟨h, anc_refl hy⟩
  exact ⟨⟨e1, e1.symm.trans e2⟩, e2.symm.trans e3⟩

private theorem fld_po {α : Type*} {P : α → α → Prop} : fld (po P) = fld P := by
  ext a
  constructor
  · rintro ⟨b, h | h⟩
    · exact fld_of_po_left h
    · exact fld_of_po_right h
  · rintro ⟨b, h | h⟩
    · exact ⟨b, Or.inl (po_iff_transGen.2 (Relation.TransGen.single h))⟩
    · exact ⟨b, Or.inr (po_iff_transGen.2 (Relation.TransGen.single h))⟩

private theorem po_po {α : Type*} {P : α → α → Prop} {a b : α} : po (po P) a b ↔ po P a b := by
  have : (po P) = Relation.TransGen P := by funext a b; exact propext po_iff_transGen
  rw [po_iff_transGen, this]
  constructor
  · intro h
    induction h with
    | single h => exact h
    | tail _ h ih => exact ih.trans h
  · exact Relation.TransGen.single

private theorem anc_po {α : Type*} {P : α → α → Prop} {a b : α} : anc (po P) a b ↔ anc P a b := by
  rw [anc_iff_po, anc_iff_po, po_po, fld_po]

/-- `x P_ν y` unfolded: `ν = N₀c'β` and `P(x⊢⊣y) sm β + 1` (with `1` existing in the type of `ν`). -/
private theorem Pnu_iff {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} {x y : α} :
    Pnu P ν x y ↔ Nonempty β ∧
      ∃ B : Set β, ν = n₀c B ∧ Nonempty (↥(itvCC P x y) ≃ ↥B ⊕ PUnit.{1}) := by
  constructor
  · intro h
    have hI : itvCC P x y ∈ (ν +ᶜ (one : Set (Set β)) : Set (Set α)) := by
      rw [← pm121_11.1 h]; exact self_mem_n₀c _
    obtain ⟨B, O, ⟨hB, hO⟩, ⟨e⟩⟩ := mem_cardAdd'.1 hI
    obtain ⟨o, ho⟩ : O ∈ (one : Set (Set β)) := hO ▸ self_mem_n₀c O
    obtain ⟨u⟩ := unit_of_mem_one (hO ▸ self_mem_n₀c O)
    exact ⟨⟨o⟩, B, hB, ⟨e.trans ((Equiv.refl _).sumCongr u)⟩⟩
  · rintro ⟨⟨b⟩, B, rfl, ⟨e⟩⟩
    show n₀c _ = _
    rw [one_eq_n₀c_singleton b, cardAdd_n₀c, n₀c_eq_ncT]
    exact ncT_congr (e.trans ((Equiv.refl _).sumCongr (Equiv.ofUnique _ _)))

private theorem itvCC_self {α : Type*} {P : α → α → Prop} {x : α} (h : ¬ po P x x)
    (hx : x ∈ fld P) : itvCC P x x = {x} := by
  ext z
  simp only [pm121_103, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h1
    · rfl
    · exact absurd (po_of_po_anc h1 h2) h
  · rintro rfl; exact ⟨anc_refl hx, anc_refl hx⟩

/-- Two distinct terms in `P(x⊢⊣y)` force `x P_po y`. -/
private theorem po_of_two {α : Type*} {P : α → α → Prop} {x y a b : α}
    (ha : a ∈ itvCC P x y) (hb : b ∈ itvCC P x y) (hab : a ≠ b) : po P x y := by
  have h := anc_trans ha.1 ha.2
  rcases anc_iff_po.1 h with ⟨rfl, hx⟩ | h
  · by_contra hp
    rw [itvCC_self hp hx] at ha hb
    exact hab (ha.trans hb.symm)
  · exact h

/-- ✱121·251. \(\vdash .P_{\text{po}}(x\dashv y)=P(x\dashv y)\) -/
theorem pm121_251 {α : Type*} {P : α → α → Prop} {x y : α} : itvOC (po P) x y = itvOC P x y := by
  ext z; simp only [pm121_101, po_po, anc_po]

/-- ✱121·252. \(\vdash .P_{\text{po}}(x\unicode{x27dd} y)=P(x \unicode{x27dd} y)\) -/
theorem pm121_252 {α : Type*} {P : α → α → Prop} {x y : α} : itvCO (po P) x y = itvCO P x y := by
  ext z; simp only [pm121_102, po_po, anc_po]

/-- ✱121·253. \(\vdash .P_{\text{po}}(x\vdash\dashv y)=P(x\vdash\dashv y)\) -/
theorem pm121_253 {α : Type*} {P : α → α → Prop} {x y : α} : itvCC (po P) x y = itvCC P x y := by
  ext z; simp only [pm121_103, anc_po]

/-- ✱121·254. \(\vdash .P_{\nu }=(P_{\text{po}})_{\nu } \quad[*121·253·11]\) -/
theorem pm121_254 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    Pnu P ν = Pnu (po P) ν := by
  funext x y; rw [Pnu, Pnu, pm121_253]

/-- ✱121·26. \(\vdash .\breve{P} _{\nu }=(\breve{P} )_{\nu }\)

`P̆_ν` is the converse of `P_ν`, `(P̆)_ν` the `P_ν` of `P̆`. -/
theorem pm121_26 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    (Pnu P ν)˘ = Pnu P˘ ν := by
  funext x y; show Pnu P ν y x = Pnu P˘ ν x y; rw [Pnu, Pnu, pm121_143]

/-- ✱121·27. \(\vdash :xP_{\nu }y.\supset .\nu ,\nu +_{c}1\in \text{NC}-\iota ʻ\Lambda\)

`ν +_c 1` is in the type of `N₀c'P(x⊢⊣y)` (✱121·02); the converse domains of the two `NC`s are the
types of the members of their members (as ✱100·41).

**Status.** proved (reading): `ν +_c 1` is taken in the type of `N₀c'P(x⊢⊣y)` (the type in which
`xP_νy` asserts it to exist, ✱121·02); the converse domain of each `NC` is the type of the members
of the members of `ν`, `ν +_c 1` (`NC` is typically ambiguous; with an arbitrary converse domain
`ν ∈ NC` can fail). -/
theorem pm121_27 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} {x y : α} :
    Pnu P ν x y → ν ∈ (NC β : Set (Set (Set β))) \ ι Λ ∧
      (ν +ᶜ (one : Set (Set β)) : Set (Set α)) ∈ (NC α : Set (Set (Set α))) \ ι Λ := by
  intro h
  obtain ⟨-, B, rfl, -⟩ := Pnu_iff.1 h
  have h2 := pm121_11.1 h
  refine ⟨⟨n₀c_mem_NC B, fun h0 => n₀c_ne_empty B (h0.trans Null_eq_empty)⟩, ?_⟩
  rw [← h2]
  exact ⟨n₀c_mem_NC _, fun h0 => n₀c_ne_empty _ (h0.trans Null_eq_empty)⟩

/-- ✱121·271. \(\vdash :{\sim}(\nu ,\nu +_{c}1\in \text{NC}-\iota ʻ\Lambda ).\supset .P_{\nu }=\dot{\Lambda} \quad[*121·27.\text{Transp}]\)

**Status.** proved (reading): as ✱121·27. -/
theorem pm121_271 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    ¬ (ν ∈ (NC β : Set (Set (Set β))) \ ι Λ ∧
        (ν +ᶜ (one : Set (Set β)) : Set (Set α)) ∈ (NC α : Set (Set (Set α))) \ ι Λ) →
      Pnu P ν = rNull := by
  intro h
  funext x y
  exact propext ⟨fun hp => absurd (pm121_27 hp) h, fun hp => (rNull_apply x y hp).elim⟩

/-- ✱121·272. \(\vdash :\dot{\exists} !P_{\nu }.\supset .\nu \geq 0.\nu +_{c}1>0.\nu +_{c}1\geq 1\)

The two occurrences of `ν +_c 1` (sides of `>`, `≥`) are in adequate types `W₂`, `W₃` (IIT); the
constants `0`, `1` are in free types (`∃!1` there: `[Nonempty W₄]`).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical occurrences of `ν +_c 1` are adequate, and `1` is taken where it exists. -/
theorem pm121_272 {α β Z₁ Z₂ W₂ W₃ W₄ : Type*} [Nonempty W₄] {P : α → α → Prop}
    {ν : Set (Set β)} (h₂ : AdeqAdd W₂ ν (one : Set (Set β)))
    (h₃ : AdeqAdd W₃ ν (one : Set (Set β))) :
    rEx (Pnu P ν) →
      (ν ≥ᶜ (zero : Set (Set Z₁)) ∧ (ν +ᶜ (one : Set (Set β)) : Set (Set W₂)) >ᶜ
          (zero : Set (Set Z₂))) ∧
        (ν +ᶜ (one : Set (Set β)) : Set (Set W₃)) ≥ᶜ (one : Set (Set W₄)) := by
  rintro ⟨x, y, h⟩
  obtain ⟨⟨b⟩, B, rfl, -⟩ := Pnu_iff.1 h
  rw [one_eq_n₀c_singleton b, cardAdd_n₀c, cardAdd_n₀c, zero_eq_n₀c_empty, zero_eq_n₀c_empty,
    one_eq_n₀c_singleton (Classical.arbitrary W₄)]
  obtain ⟨S₂, hS₂⟩ := ncT_nonempty_iff.2 (adeqAdd_emb h₂ B {b})
  obtain ⟨S₃, hS₃⟩ := ncT_nonempty_iff.2 (adeqAdd_emb h₃ B {b})
  rw [ncT_eq_n₀c_of_mem hS₂, ncT_eq_n₀c_of_mem hS₃]
  obtain ⟨e2⟩ := hS₂
  obtain ⟨e3⟩ := hS₃
  refine ⟨⟨cardGe_n₀c.2 ⟨⟨fun z => z.2.elim, fun z => z.2.elim⟩⟩,
    cardGt_n₀c.2 ⟨⟨⟨fun z => z.2.elim, fun z => z.2.elim⟩⟩, fun ⟨f⟩ => ?_⟩⟩, ?_⟩
  · exact (f (e2.symm (Sum.inr ⟨b, rfl⟩))).2
  · exact cardGe_n₀c.2 ⟨⟨fun _ => e3.symm (Sum.inr ⟨b, rfl⟩), fun _ _ _ => Subsingleton.elim _ _⟩⟩

/-- ✱121·273. \(\vdash :\dot{\exists} !P_{\nu +_{c}1}.\supset .\nu +_{c}1>0\)

The subscript `ν +_c 1` is in a free type `W`; the side of `>` in an adequate type `W'` (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W'` of the
arithmetical occurrence of `ν +_c 1` is adequate. -/
theorem pm121_273 {α β W W' Z : Type*} {P : α → α → Prop} {ν : Set (Set β)}
    (h : AdeqAdd W' ν (one : Set (Set β))) :
    rEx (Pnu P (ν +ᶜ (one : Set (Set β)) : Set (Set W))) →
      (ν +ᶜ (one : Set (Set β)) : Set (Set W')) >ᶜ (zero : Set (Set Z)) := by
  rintro ⟨x, y, hp⟩
  obtain ⟨-, X, hX, -⟩ := Pnu_iff.1 hp
  have hne : (ν +ᶜ (one : Set (Set β)) : Set (Set W)).Nonempty := by
    rw [hX]; exact n₀c_nonempty X
  obtain ⟨B, O, ⟨rfl, hO⟩, -⟩ := cardAdd_nonempty_iff.1 hne
  obtain ⟨b, hb⟩ : O ∈ (one : Set (Set β)) := hO ▸ self_mem_n₀c O
  rw [one_eq_n₀c_singleton b, cardAdd_n₀c, zero_eq_n₀c_empty]
  obtain ⟨S, hS⟩ := ncT_nonempty_iff.2 (adeqAdd_emb h B {b})
  rw [ncT_eq_n₀c_of_mem hS]
  obtain ⟨e⟩ := hS
  exact cardGt_n₀c.2 ⟨⟨⟨fun z => z.2.elim, fun z => z.2.elim⟩⟩,
    fun ⟨f⟩ => (f (e.symm (Sum.inr ⟨b, rfl⟩))).2⟩

/-- ✱121·3. \(\vdash .P_{0}\,\unicode{x2abd}\, 1\upharpoonright CʻP\)

The `1` of the e-text is PM's `I` (the identity relation): `1 ↾ C'P` would be meaningless, and
✱121·302 gives `P₀ = I ↾ C'P`.

**Status.** proved (reading): transcription error (`1` for `I`). -/
theorem pm121_3 {α β : Type*} {P : α → α → Prop} : Pnu P (zero : Set (Set β)) ⪽ I ↾ fld P := by
  intro x y h
  obtain ⟨-, B, hB, ⟨e⟩⟩ := Pnu_iff.1 h
  have hB' : B = ∅ := n₀c_eq_zero_iff.1 hB.symm
  subst hB'
  have hne : (itvCC P x y).Nonempty := ⟨_, (e.symm (Sum.inr PUnit.unit)).2⟩
  have hxy := (pm121_23.2.2 hne)
  have hsub : ∀ a b : ↥(itvCC P x y), a = b := fun a b =>
    e.injective (by rcases e a with ⟨⟨_, h⟩⟩ | ⟨⟩ <;> rcases e b with ⟨⟨_, h'⟩⟩ | ⟨⟩ <;> first
      | exact (Set.notMem_empty _ h).elim | exact (Set.notMem_empty _ h').elim | rfl)
  have := congrArg Subtype.val (hsub ⟨x, hxy.1⟩ ⟨y, hxy.2⟩)
  exact ⟨this, fld_of_anc_right hxy.1.2⟩

private theorem Pnu_zero_iff {α β : Type*} [Nonempty β] {P : α → α → Prop} {x y : α} :
    Pnu P (zero : Set (Set β)) x y ↔ Nonempty (↥(itvCC P x y) ≃ PUnit.{1}) := by
  rw [Pnu_iff]
  constructor
  · rintro ⟨-, B, hB, ⟨e⟩⟩
    have hB' : B = ∅ := n₀c_eq_zero_iff.1 hB.symm
    subst hB'
    exact ⟨e.trans (Equiv.emptySum _ _)⟩
  · rintro ⟨e⟩
    exact ⟨inferInstance, ∅, zero_eq_n₀c_empty, ⟨e.trans (Equiv.emptySum _ _).symm⟩⟩

/-- ✱121·301. \(\vdash :{\sim}(xP_{\text{po}}x).\supset :xP_{0}y.\equiv .x\in CʻP.x=y\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty β]` for the type of the `0` (for an empty `β`, `1 = Λ` there and `P₀ = Λ̇`). -/
theorem pm121_301 {α β : Type*} [Nonempty β] {P : α → α → Prop} {x y : α} :
    ¬ po P x x → (Pnu P (zero : Set (Set β)) x y ↔ x ∈ fld P ∧ x = y) := by
  intro hx
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := pm121_3 x y h
    exact ⟨h1 ▸ h2, h1⟩
  · rintro ⟨hf, rfl⟩
    rw [Pnu_zero_iff, itvCC_self hx hf]
    exact ⟨Equiv.ofUnique _ _⟩

/-- ✱121·302. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\supset .P_{0}=I\upharpoonright CʻP \quad[*121·301]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty β]` for the type of the `0`. -/
theorem pm121_302 {α β : Type*} [Nonempty β] {P : α → α → Prop} :
    po P ⪽ J → Pnu P (zero : Set (Set β)) = I ↾ fld P := by
  intro hJ
  funext x y
  apply propext
  rw [pm121_301 (fun h => hJ x x h rfl)]
  constructor
  · rintro ⟨h1, rfl⟩; exact ⟨rfl, h1⟩
  · rintro ⟨rfl, h⟩; exact ⟨h, rfl⟩

/-- ✱121·303. \(\vdash :\text{Nc}ʻP(x\vdash\dashv y)>1.\supset .xP_{\text{po}}y\)

The side `Nc'P(x⊢⊣y)` of `>` is `N₀c'P(x⊢⊣y)` (normal adjustment); `1` is in a free type `W`.

**Status.** proved (reading): the side `Nc'P(x⊢⊣y)` of `>` is `N₀c'P(x⊢⊣y)` (✱117·02·03, normal
adjustment). -/
theorem pm121_303 {α W : Type*} {P : α → α → Prop} {x y : α} :
    n₀c (itvCC P x y) >ᶜ (one : Set (Set W)) → po P x y := by
  intro h
  obtain ⟨I', O, ⟨hI, hO⟩, ⟨f⟩, hn⟩ := cardGt_iff.1 h
  obtain ⟨eI⟩ := eq_n₀c_iff_equiv.1 hI
  obtain ⟨o, rfl⟩ : O ∈ (one : Set (Set W)) := hO ▸ self_mem_n₀c O
  let a := eI.symm (f ⟨o, rfl⟩)
  by_contra hp
  have hxy : anc P x y := anc_trans a.2.1 a.2.2
  rcases anc_iff_po.1 hxy with ⟨rfl, hx⟩ | hp'
  · apply hn
    refine ⟨⟨fun _ => ⟨o, rfl⟩, fun u v _ => ?_⟩⟩
    have hs := itvCC_self hp hx
    have hu := (Set.ext_iff.1 hs _).1 (eI.symm u).2
    have hv := (Set.ext_iff.1 hs _).1 (eI.symm v).2
    exact eI.symm.injective (Subtype.ext (hu.trans hv.symm))
  · exact hp hp'

/-- ✱121·304. \(\vdash \colon\ldotp P_{\text{po}}\,\unicode{x2abd}\, J.\supset :xP_{1}y.\equiv .P(x\vdash\dashv y)={℩}ʻx\cup {℩}ʻy.x\neq y\)

(The e-text prints `℩'x` for `ι'x`.)

**Status.** proved (reading): transcription error (`℩` for `ι`); PM assumes every type has a member
(Introduction, Ch. I): `[Nonempty β]` for the type of the `1` (otherwise `P₁ = Λ̇`). -/
theorem pm121_304 {α β : Type*} [Nonempty β] {P : α → α → Prop} {x y : α} :
    po P ⪽ J → (Pnu P (one : Set (Set β)) x y ↔ itvCC P x y = ι x ∪ ι y ∧ x ≠ y) := by
  intro hJ
  rw [Pnu_iff]
  constructor
  · rintro ⟨-, B, hB, ⟨e⟩⟩
    obtain ⟨u⟩ := unit_of_mem_one (hB ▸ self_mem_n₀c B : B ∈ (one : Set (Set β)))
    have hfin : Finite ↥(itvCC P x y) := Finite.of_equiv _ (e.trans (u.sumCongr (Equiv.refl _))).symm
    have hc : Nat.card ↥(itvCC P x y) = 2 := by
      rw [Nat.card_congr (e.trans (u.sumCongr (Equiv.refl _))), Nat.card_sum, Nat.card_unique]
    have hne : (itvCC P x y).Nonempty := ⟨_, (e.symm (Sum.inr PUnit.unit)).2⟩
    have hm := pm121_23.2.2 hne
    have hxy : x ≠ y := by
      rintro rfl
      rw [itvCC_self (fun h => hJ x x h rfl) hm.1.1.1, Nat.card_unique] at hc
      exact absurd hc (by norm_num)
    refine ⟨?_, hxy⟩
    rw [unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]
    symm
    apply Set.eq_of_subset_of_ncard_le
    · rintro z (rfl | rfl)
      · exact hm.1
      · exact hm.2
    · rw [Set.ncard_pair hxy, ← Nat.card_coe_set_eq, hc]
    · exact Set.finite_coe_iff.1 hfin
  · rintro ⟨h, hxy⟩
    let b : β := Classical.arbitrary β
    refine ⟨inferInstance, {b}, one_eq_n₀c_singleton b, ?_⟩
    rw [h, unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]
    have : Finite ↥({x, y} : Set α) := Set.toFinite _
    apply Finite.card_eq.1
    rw [Nat.card_coe_set_eq, Set.ncard_pair hxy, Nat.card_sum, Nat.card_unique, Nat.card_unique]

/-- ✱121·305. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\supset .P_{1}\,\unicode{x2abd}\, P\) -/
theorem pm121_305 {α β : Type*} {P : α → α → Prop} :
    po P ⪽ J → Pnu P (one : Set (Set β)) ⪽ P := by
  intro hJ x y h
  have : Nonempty β := (Pnu_iff.1 h).1
  obtain ⟨hI, hxy⟩ := (pm121_304 hJ).1 h
  have hy : y ∈ itvCC P x y := by rw [hI]; exact Or.inr rfl
  have hp : po P x y := by
    rcases anc_iff_po.1 hy.1 with ⟨rfl, -⟩ | hp
    · exact absurd rfl hxy
    · exact hp
  rw [po_iff_transGen] at hp
  obtain ⟨w, hxw, hwy⟩ := Relation.TransGen.head'_iff.1 hp
  have hw : w ∈ itvCC P x y :=
    ⟨anc_iff_reflTransGen.2 ⟨⟨w, Or.inl hxw⟩, Relation.ReflTransGen.single hxw⟩,
      anc_iff_reflTransGen.2 ⟨⟨x, Or.inr hxw⟩, hwy⟩⟩
  rw [hI] at hw
  rcases hw with hw | hw
  · rw [mem_unitCls.1 hw] at hxw
    exact absurd rfl (hJ x x (po_iff_transGen.2 (Relation.TransGen.single hxw)))
  · rw [mem_unitCls.1 hw] at hxw; exact hxw

/-- ✱121·306. \(\vdash :P\in 1\rightarrow \text{Cls}.{\sim}(xP_{\text{po}}x).xPy.\supset .P(x\vdash\dashv y)=\iota ʻx\cup \iota ʻy.x\neq y\) -/
theorem pm121_306 {α : Type*} {P : α → α → Prop} {x y : α} :
    (P ∈ arrow one Cls ∧ ¬ po P x x) ∧ P x y → itvCC P x y = ι x ∪ ι y ∧ x ≠ y := by
  rintro ⟨⟨hP, hx⟩, hxy⟩
  have h1 := mem_arrow_one_Cls.1 hP
  have hne : x ≠ y := by
    rintro rfl; exact hx (po_iff_transGen.2 (Relation.TransGen.single hxy))
  refine ⟨?_, hne⟩
  have hA : anc P x y := anc_iff_reflTransGen.2 ⟨⟨y, Or.inl hxy⟩, Relation.ReflTransGen.single hxy⟩
  ext z
  simp only [pm121_103, Set.mem_union, mem_unitCls]
  constructor
  · rintro ⟨hxz, hzy⟩
    by_cases hzy' : z = y
    · exact Or.inr hzy'
    · left
      rcases anc_iff_po.1 hzy with ⟨rfl, -⟩ | hp
      · exact absurd rfl hzy'
      rw [po_iff_transGen] at hp
      obtain ⟨w, hzw, hwy⟩ := Relation.TransGen.tail'_iff.1 hp
      have hwx : w = x := h1 w x y ⟨hwy, hxy⟩
      subst hwx
      by_contra hzx
      have hxz' := (anc_iff_reflTransGen.1 hxz).2
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 hxz' with h | h
      · exact hzx h
      · exact hx (po_iff_transGen.2 (Relation.TransGen.trans_left h hzw))
  · rintro (rfl | rfl)
    · exact ⟨anc_refl hA.1, hA⟩
    · exact ⟨hA, anc_refl (fld_of_anc_right hA)⟩

private theorem arrow_cnv {α : Type*} {P : α → α → Prop} :
    P ∈ arrow Cls one ↔ P˘ ∈ arrow one Cls := by
  rw [mem_arrow_Cls_one, mem_arrow_one_Cls]
  exact ⟨fun h x y z hh => h z x y hh, fun h x y z hh => h y z x hh⟩

/-- ✱121·307. \[\begin{align}&\vdash :P\in \text{Cls}\rightarrow 1.{\sim}(yP_{\text{po}}y).xPy.\supset .P(x\vdash\dashv y)=\iota ʻx\cup \iota ʻy.x\neq y\\ &[*121·306·143]\end{align}\] -/
theorem pm121_307 {α : Type*} {P : α → α → Prop} {x y : α} :
    (P ∈ arrow Cls one ∧ ¬ po P y y) ∧ P x y → itvCC P x y = ι x ∪ ι y ∧ x ≠ y := by
  rintro ⟨⟨hP, hy⟩, hxy⟩
  obtain ⟨h1, h2⟩ := pm121_306 (P := P˘) ⟨⟨arrow_cnv.1 hP, fun h => hy (po_cnv.1 h)⟩, hxy⟩
  rw [pm121_143, h1, Set.union_comm]
  exact ⟨rfl, Ne.symm h2⟩

/-- ✱121·308. \[\begin{align}&\vdash :P\in (1\rightarrow \text{Cls})\cup (\text{Cls}\rightarrow 1).P_{\text{po}}\,\unicode{x2abd}\, J.\supset .P\,\unicode{x2abd}\, P_{1}\\ &[*121·306·307·11.*54·101]\end{align}\]

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty β]` for the type of the `1` (otherwise `P₁ = Λ̇`). -/
theorem pm121_308 {α β : Type*} [Nonempty β] {P : α → α → Prop} :
    P ∈ arrow one Cls ∪ arrow Cls one ∧ po P ⪽ J → P ⪽ Pnu P (one : Set (Set β)) := by
  rintro ⟨hP, hJ⟩ x y hxy
  have h : itvCC P x y = ι x ∪ ι y ∧ x ≠ y := by
    rcases hP with hP | hP
    · exact pm121_306 ⟨⟨hP, fun h => hJ x x h rfl⟩, hxy⟩
    · exact pm121_307 ⟨⟨hP, fun h => hJ y y h rfl⟩, hxy⟩
  exact (pm121_304 hJ).2 h

/-- ✱121·31. \(\vdash :P\in (1\rightarrow \text{Cls})\cup (\text{Cls}\rightarrow 1).P_{\text{po}}\,\unicode{x2abd}\, J.\supset .P_{1}=P \quad[*121·305·308]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty β]` for the type of the `1`. -/
theorem pm121_31 {α β : Type*} [Nonempty β] {P : α → α → Prop} :
    P ∈ arrow one Cls ∪ arrow Cls one ∧ po P ⪽ J → Pnu P (one : Set (Set β)) = P := by
  intro h
  funext x y
  exact propext ⟨pm121_305 h.2 x y, pm121_308 h x y⟩

private theorem anc_of_Pnu {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} {x y : α}
    (h : Pnu P ν x y) : anc P x y := by
  obtain ⟨-, B, -, ⟨e⟩⟩ := Pnu_iff.1 h
  exact pm121_23.2.2 ⟨_, (e.symm (Sum.inr PUnit.unit)).2⟩ |>.1.2

/-- ✱121·32. \(\vdash .P_{\nu }\,\unicode{x2abd}\, P_{*}\) -/
theorem pm121_32 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} : Pnu P ν ⪽ anc P :=
  fun _ _ h => anc_of_Pnu h

private theorem po_of_Pnu_ne_zero {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} {x y : α}
    (h : Pnu P ν x y) (hB : ∀ B : Set β, ν = n₀c B → B.Nonempty) : po P x y := by
  obtain ⟨-, B, hνB, ⟨e⟩⟩ := Pnu_iff.1 h
  obtain ⟨b, hb⟩ := hB B hνB
  refine po_of_two (e.symm (Sum.inl ⟨b, hb⟩)).2 (e.symm (Sum.inr PUnit.unit)).2 fun h' => ?_
  exact Sum.inl_ne_inr (e.symm.injective (Subtype.ext h'))

/-- ✱121·321. \(\vdash :\nu >0.\supset .P_{\nu }\,\unicode{x2abd}\, P_{\text{po}}\)

The `0` is in a free type `W`. -/
theorem pm121_321 {α β W : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    ν >ᶜ (zero : Set (Set W)) → Pnu P ν ⪽ po P := by
  intro hν x y h
  obtain ⟨B, Z, ⟨hB, hZ⟩, -, hn⟩ := cardGt_iff.1 hν
  refine po_of_Pnu_ne_zero h fun B' hB' => ?_
  obtain ⟨e⟩ := eq_n₀c_iff_equiv.1 (hB.symm.trans hB')
  have hZ' : Z = ∅ := n₀c_eq_zero_iff.1 hZ.symm
  subst hZ'
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  exact hn ⟨⟨fun b => (e b).2.elim, fun b => (e b).2.elim⟩⟩

/-- ✱121·322. \(\vdash .CʻP_{\nu }\subset CʻP \quad[*121·32.*90·14]\) -/
theorem pm121_322 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    fld (Pnu P ν) ⊆ fld P := by
  rintro z ⟨w, h | h⟩
  · exact fld_of_anc_left (anc_of_Pnu h)
  · exact fld_of_anc_right (anc_of_Pnu h)

private theorem dom_codom_of_po {α : Type*} {P : α → α → Prop} {x y : α} (h : po P x y) :
    x ∈ dom P ∧ y ∈ codom P := by
  rw [po_iff_transGen] at h
  obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 h
  obtain ⟨d, -, hd⟩ := Relation.TransGen.tail'_iff.1 h
  exact ⟨⟨c, hc⟩, ⟨d, hd⟩⟩

/-- ✱121·323. \(\vdash :\nu >0.\supset .\text{D}ʻP_{\nu }\subset \text{D}ʻP.\text{ᗡ}ʻP_{\nu }\subset \text{ᗡ}ʻP \quad[*121·321.*91·504]\) -/
theorem pm121_323 {α β W : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    ν >ᶜ (zero : Set (Set W)) → dom (Pnu P ν) ⊆ dom P ∧ codom (Pnu P ν) ⊆ codom P := by
  intro hν
  exact ⟨fun x ⟨y, h⟩ => (dom_codom_of_po (pm121_321 hν x y h)).1,
    fun y ⟨x, h⟩ => (dom_codom_of_po (pm121_321 hν x y h)).2⟩

/-- ✱121·324. \(\vdash .\text{D}ʻP_{\nu +_{c}1}\subset \text{D}ʻP.\text{ᗡ}ʻP_{\nu +_{c}1}\subset \text{ᗡ}ʻP\)

The subscript `ν +_c 1` is in a free type `W`, its `1` in the type of `ν`. -/
theorem pm121_324 {α β W : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    dom (Pnu P (ν +ᶜ (one : Set (Set β)) : Set (Set W))) ⊆ dom P ∧
      codom (Pnu P (ν +ᶜ (one : Set (Set β)) : Set (Set W))) ⊆ codom P := by
  have key : ∀ x y, Pnu P (ν +ᶜ (one : Set (Set β)) : Set (Set W)) x y → po P x y := by
    intro x y h
    refine po_of_Pnu_ne_zero h fun X hX => ?_
    have hX' : X ∈ (ν +ᶜ (one : Set (Set β)) : Set (Set W)) := hX ▸ self_mem_n₀c X
    obtain ⟨B, O, ⟨-, hO⟩, ⟨e⟩⟩ := mem_cardAdd'.1 hX'
    obtain ⟨o, rfl⟩ : O ∈ (one : Set (Set β)) := hO ▸ self_mem_n₀c O
    exact ⟨_, (e.symm (Sum.inr ⟨o, rfl⟩)).2⟩
  exact ⟨fun x ⟨y, h⟩ => (dom_codom_of_po (key x y h)).1,
    fun y ⟨x, h⟩ => (dom_codom_of_po (key x y h)).2⟩

/-- ✱121·325. \(\vdash :\dot{\exists} !P_{\mu }\dot{\cap} P_{\nu }.\supset .\mu =\nu\)

`μ = ν` puts `μ`, `ν` in one type. -/
theorem pm121_325 {α β : Type*} {P : α → α → Prop} {μ ν : Set (Set β)} :
    rEx (Pnu P μ ⩀ Pnu P ν) → μ = ν := by
  rintro ⟨x, y, h1, h2⟩
  obtain ⟨-, B, rfl, ⟨e1⟩⟩ := Pnu_iff.1 h1
  obtain ⟨-, C, rfl, ⟨e2⟩⟩ := Pnu_iff.1 h2
  obtain ⟨g⟩ := equiv_cancel (Equiv.refl PUnit.{1}) (e1.symm.trans e2)
  exact eq_n₀c_iff_equiv.2 ⟨g⟩

/-- ✱121·326. \(\vdash .\text{fin}ʻP\subset \text{finid}ʻP.\text{finid}ʻP-\iota ʻP_{0}\subset \text{fin}ʻP \quad[*121·12·121]\)

`P₀` is `P_ν` for the `0` of the type `β` of the apparent `ν`. -/
theorem pm121_326 {α β : Type*} {P : α → α → Prop} :
    fin β P ⊆ finid β P ∧ finid β P \ ι (Pnu P (zero : Set (Set β))) ⊆ fin β P := by
  refine ⟨fun R ⟨ν, ⟨hν, _⟩, hR⟩ => ⟨ν, hν, hR⟩, fun R ⟨⟨ν, hν, hR⟩, hR0⟩ => ⟨ν, ⟨hν, ?_⟩, hR⟩⟩
  intro h
  apply hR0
  rw [mem_unitCls] at h ⊢
  rw [hR, h]

/-- ✱121·327. \(\vdash :\dot{\exists} !P_{0}.\supset .\text{fin}ʻP=\text{finid}ʻP-\iota ʻP_{0}\) -/
theorem pm121_327 {α β : Type*} {P : α → α → Prop} :
    rEx (Pnu P (zero : Set (Set β))) → fin β P = finid β P \ ι (Pnu P (zero : Set (Set β))) := by
  rintro ⟨x, y, h0⟩
  refine Set.Subset.antisymm (fun R hR => ⟨pm121_326.1 hR, fun hR0 => ?_⟩) pm121_326.2
  obtain ⟨ν, ⟨-, hν0⟩, rfl⟩ := hR
  rw [mem_unitCls] at hR0
  apply hν0
  rw [mem_unitCls]
  have hν' : Pnu P ν x y := by rw [hR0]; exact h0
  exact pm121_325 ⟨x, y, hν', h0⟩

/-- In a many-one relation, two descendants of one term are comparable. -/
private theorem rtg_comparable {α : Type*} {R : α → α → Prop} (hR : R ∈ arrow Cls one)
    {x a b : α} (ha : Relation.ReflTransGen R x a) (hb : Relation.ReflTransGen R x b) :
    Relation.ReflTransGen R a b ∨ Relation.ReflTransGen R b a := by
  have h1 := mem_arrow_Cls_one.1 hR
  induction hb with
  | refl => exact Or.inr ha
  | @tail b' b _ hbb ih =>
    rcases ih with h | h
    · exact Or.inl (h.tail hbb)
    · rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with rfl | h
      · exact Or.inl (Relation.ReflTransGen.single hbb)
      · obtain ⟨c, hc, hca⟩ := Relation.TransGen.head'_iff.1 h
        have : c = b := h1 b' c b ⟨hc, hbb⟩
        subst this
        exact Or.inr hca

/-- ✱121·33. \[\begin{align}\vdash \colon\ldotp P\in 1\rightarrow \text{Cls}.\supset :&z\in P(x-y).\equiv .z\in P(x\dashv Pʻy):\\ &z\in P(x \unicode{x27dd} y).\equiv .z\in P(x\vdash\dashv Pʻy)\end{align}\]

`z ∈ P(x ⊣ P'y)` is `Desc P y (fun w => z ∈ itvOC P x w)` (the description `P'y` with the smallest
scope); "this does not follow unless `y ∈ ᗡ'P`" (PM) for the equation of the classes, but the
membership equivalences hold for every `z`. -/
theorem pm121_33 {α : Type*} {P : α → α → Prop} {x y z : α} :
    P ∈ arrow one Cls →
      ((z ∈ itvOO P x y ↔ Desc P y (fun w => z ∈ itvOC P x w)) ∧
        (z ∈ itvCO P x y ↔ Desc P y (fun w => z ∈ itvCC P x w))) := by
  intro hP
  have h1 := mem_arrow_one_Cls.1 hP
  have key : ∀ a, po P a y ↔ Desc P y (fun w => anc P a w) := by
    intro a
    constructor
    · intro h
      rw [po_iff_transGen] at h
      obtain ⟨w, haw, hwy⟩ := Relation.TransGen.tail'_iff.1 h
      refine ⟨w, fun u => ⟨fun hu => h1 u w y ⟨hu, hwy⟩, fun hu => hu ▸ hwy⟩, ?_⟩
      exact anc_iff_reflTransGen.2 ⟨by
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 haw with rfl | h'
        · exact ⟨y, Or.inl hwy⟩
        · exact fld_of_po_left (po_iff_transGen.2 h'), haw⟩
    · rintro ⟨w, hw, haw⟩
      have hwy : P w y := (hw w).2 rfl
      rw [po_iff_transGen]
      exact Relation.TransGen.tail' (anc_iff_reflTransGen.1 haw).2 hwy
  have desc_and : ∀ (p : Prop) (ψ : α → Prop), (p ∧ Desc P y ψ) ↔ Desc P y (fun w => p ∧ ψ w) :=
    fun p ψ => ⟨fun ⟨hp, w, hw, hψ⟩ => ⟨w, hw, hp, hψ⟩, fun ⟨w, hw, hp, hψ⟩ => ⟨hp, w, hw, hψ⟩⟩
  constructor
  · rw [pm121_1, key z]
    exact desc_and _ _
  · rw [pm121_102, key z]
    exact desc_and _ _

/-- The `k`th power of `P` on its field. -/
private def pwr {α : Type*} (P : α → α → Prop) : ℕ → α → α → Prop
  | 0 => fun x y => x = y ∧ x ∈ fld P
  | k + 1 => fun x y => ∃ w, pwr P k x w ∧ P w y

private theorem pwr_succ {α : Type*} {P : α → α → Prop} {k : ℕ} {x y : α} :
    pwr P (k + 1) x y ↔ ∃ w, pwr P k x w ∧ P w y := Iff.rfl

private theorem pwr_right_fld {α : Type*} {P : α → α → Prop} :
    ∀ {k : ℕ} {x y : α}, pwr P k x y → y ∈ fld P
  | 0, _, _, ⟨rfl, h⟩ => h
  | _ + 1, _, _, ⟨w, _, h⟩ => ⟨w, Or.inr h⟩

private theorem anc_of_step {α : Type*} {P : α → α → Prop} {x y : α} (h : P x y) : anc P x y :=
  anc_iff_reflTransGen.2 ⟨⟨y, Or.inl h⟩, Relation.ReflTransGen.single h⟩

private theorem pwr_anc {α : Type*} {P : α → α → Prop} :
    ∀ {k : ℕ} {x y : α}, pwr P k x y → anc P x y
  | 0, _, _, ⟨rfl, h⟩ => anc_refl h
  | _ + 1, _, _, ⟨_, hw, h⟩ => anc_trans (pwr_anc hw) (anc_of_step h)

private theorem anc_pwr {α : Type*} {P : α → α → Prop} {x y : α} (h : anc P x y) :
    ∃ k, pwr P k x y := by
  obtain ⟨hx, h'⟩ := anc_iff_reflTransGen.1 h
  clear h
  induction h' with
  | refl => exact ⟨0, rfl, hx⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, _, hk, hbc⟩

private theorem pwr_add {α : Type*} {P : α → α → Prop} {a : ℕ} :
    ∀ {b : ℕ} {x z : α}, pwr P (a + b) x z ↔ ∃ y, pwr P a x y ∧ pwr P b y z
  | 0, _, z => ⟨fun h => ⟨z, h, rfl, pwr_right_fld h⟩, fun ⟨_, h, rfl, _⟩ => h⟩
  | b + 1, x, z => by
    show (∃ w, pwr P (a + b) x w ∧ P w z) ↔ ∃ y, pwr P a x y ∧ ∃ w, pwr P b y w ∧ P w z
    constructor
    · rintro ⟨w, hw, hwz⟩
      obtain ⟨y, hy, hyw⟩ := (pwr_add (b := b)).1 hw
      exact ⟨y, hy, w, hyw, hwz⟩
    · rintro ⟨y, hy, w, hyw, hwz⟩
      exact ⟨w, (pwr_add (b := b)).2 ⟨y, hy, hyw⟩, hwz⟩

private theorem pwr_one {α : Type*} {P : α → α → Prop} {x y : α} : pwr P 1 x y ↔ P x y :=
  ⟨fun ⟨_, ⟨rfl, _⟩, h⟩ => h, fun h => ⟨x, ⟨rfl, ⟨y, Or.inl h⟩⟩, h⟩⟩

private theorem pwr_succ' {α : Type*} {P : α → α → Prop} {k : ℕ} {x y : α} :
    pwr P (k + 1) x y ↔ ∃ w, P x w ∧ pwr P k w y := by
  rw [Nat.add_comm, pwr_add]
  exact exists_congr fun w => and_congr_left' pwr_one

private theorem fld_cnv {α : Type*} {P : α → α → Prop} : fld P˘ = fld P := by
  ext x
  exact ⟨fun ⟨w, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, h.symm⟩⟩

private theorem pwr_cnv {α : Type*} {P : α → α → Prop} :
    ∀ {k : ℕ} {x y : α}, pwr P˘ k y x ↔ pwr P k x y
  | 0, x, y => by
    show (y = x ∧ y ∈ fld P˘) ↔ (x = y ∧ x ∈ fld P)
    rw [fld_cnv]
    constructor <;> rintro ⟨rfl, h⟩ <;> exact ⟨rfl, h⟩
  | k + 1, x, y => by
    rw [pwr_succ, pwr_succ']
    exact exists_congr fun w => by rw [pwr_cnv]; exact And.comm

private theorem J_cnv {α : Type*} {P : α → α → Prop} (hJ : po P ⪽ J) : po P˘ ⪽ J :=
  fun a b h e => hJ b a (po_cnv.1 h) e.symm

private theorem Pnu_cnv {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} {x y : α} :
    Pnu P˘ ν x y ↔ Pnu P ν y x := by
  rw [pm121_11, pm121_11, ← pm121_143]

/-- In a one-many relation without cycles, `P(x⊢⊣y) = P(x⊢⊣P'y) ∪ ι'y` (`y` not in the first). -/
private theorem itv_step {α : Type*} {P : α → α → Prop} (hP : P ∈ arrow one Cls) (hJ : po P ⪽ J)
    {x w y : α} (hxw : anc P x w) (hwy : P w y) :
    itvCC P x y = insert y (itvCC P x w) ∧ y ∉ itvCC P x w := by
  have h1 := mem_arrow_one_Cls.1 hP
  have hwy' : anc P w y := anc_of_step hwy
  refine ⟨?_, fun h => hJ y y (po_of_anc_po h.2 (po_iff_transGen.2 (Relation.TransGen.single hwy)))
    rfl⟩
  ext z
  simp only [Set.mem_insert_iff, pm121_103]
  constructor
  · rintro ⟨hxz, hzy⟩
    rcases anc_iff_po.1 hzy with ⟨rfl, -⟩ | h
    · exact Or.inl rfl
    · obtain ⟨u, hzu, huy⟩ := Relation.TransGen.tail'_iff.1 (po_iff_transGen.1 h)
      have : u = w := h1 u w y ⟨huy, hwy⟩
      subst this
      exact Or.inr ⟨hxz, anc_iff_reflTransGen.2 ⟨fld_of_anc_right hxz, hzu⟩⟩
  · rintro (rfl | ⟨hxz, hzw⟩)
    · exact ⟨anc_trans hxw hwy', anc_refl (fld_of_anc_right hwy')⟩
    · exact ⟨hxz, anc_trans hzw hwy'⟩

/-- In a one-many relation without cycles, `x (P^k) y` gives `k + 1` terms in `P(x⊢⊣y)`. -/
private theorem pwr_card {α : Type*} {P : α → α → Prop} (hP : P ∈ arrow one Cls) (hJ : po P ⪽ J) :
    ∀ {k : ℕ} {x y : α}, pwr P k x y → (itvCC P x y).Finite ∧ (itvCC P x y).ncard = k + 1
  | 0, x, _, ⟨rfl, hx⟩ => by
    rw [itvCC_self (fun h => hJ x x h rfl) hx]
    exact ⟨Set.finite_singleton x, Set.ncard_singleton x⟩
  | k + 1, _, y, ⟨_, hw, hwy⟩ => by
    obtain ⟨hf, hc⟩ := pwr_card hP hJ hw
    obtain ⟨e, hy⟩ := itv_step hP hJ (pwr_anc hw) hwy
    rw [e]
    exact ⟨hf.insert y, by rw [Set.ncard_insert_of_notMem hy hf, hc]⟩

private theorem finite_left_of_equiv {X Y Z : Type*} [Finite Z] (e : Z ≃ X ⊕ Y) : Finite X :=
  Finite.of_injective (fun a => e.symm (Sum.inl a)) fun _ _ h => Sum.inl_injective (e.symm.injective h)

private theorem finite_right_of_equiv {X Y Z : Type*} [Finite Z] (e : Z ≃ X ⊕ Y) : Finite Y :=
  Finite.of_injective (fun a => e.symm (Sum.inr a)) fun _ _ h => Sum.inr_injective (e.symm.injective h)

private theorem Pnu_pwr_aux {α β : Type*} {P : α → α → Prop} (hP : P ∈ arrow one Cls)
    (hJ : po P ⪽ J) {ν : Set (Set β)} {x y : α} :
    Pnu P ν x y ↔ Nonempty β ∧ ∃ A : Set β, A.Finite ∧ ν = n₀c A ∧ pwr P (Nat.card A) x y := by
  constructor
  · intro h
    obtain ⟨hβ, B, hB, ⟨e⟩⟩ := Pnu_iff.1 h
    obtain ⟨k, hk⟩ := anc_pwr (anc_of_Pnu h)
    obtain ⟨hf, hc⟩ := pwr_card hP hJ hk
    have : Finite ↥(itvCC P x y) := hf.to_subtype
    have : Finite ↥B := finite_left_of_equiv e
    have hcard : Nat.card ↥(itvCC P x y) = Nat.card ↥B + 1 := by
      rw [Nat.card_congr e, Nat.card_sum, Nat.card_unique (α := PUnit.{1})]
    rw [Nat.card_coe_set_eq (itvCC P x y), hc] at hcard
    refine ⟨hβ, B, Set.toFinite B, hB, ?_⟩
    rw [show Nat.card ↥B = k by omega]
    exact hk
  · rintro ⟨hβ, A, hA, rfl, hk⟩
    obtain ⟨hf, hc⟩ := pwr_card hP hJ hk
    have : Finite ↥(itvCC P x y) := hf.to_subtype
    have : Finite ↥A := hA.to_subtype
    refine Pnu_iff.2 ⟨hβ, A, rfl, ?_⟩
    apply Finite.card_eq.1
    rw [Nat.card_sum, Nat.card_unique (α := PUnit.{1}), Nat.card_coe_set_eq (itvCC P x y), hc]

/-- `x P_ν y` for a one-many or many-one relation without cycles: `ν` is the cardinal of a finite
class of `k` terms and `x (P^k) y`. -/
private theorem Pnu_pwr {α β : Type*} {P : α → α → Prop} (hP : P ∈ arrow one Cls ∪ arrow Cls one)
    (hJ : po P ⪽ J) {ν : Set (Set β)} {x y : α} :
    Pnu P ν x y ↔ Nonempty β ∧ ∃ A : Set β, A.Finite ∧ ν = n₀c A ∧ pwr P (Nat.card A) x y := by
  rcases hP with hP | hP
  · exact Pnu_pwr_aux hP hJ
  · rw [← Pnu_cnv, Pnu_pwr_aux (arrow_cnv.1 hP) (J_cnv hJ)]
    simp only [pwr_cnv]

private theorem Pnu_n₀c_pwr {α β : Type*} {P : α → α → Prop}
    (hP : P ∈ arrow one Cls ∪ arrow Cls one) (hJ : po P ⪽ J) {A : Set β} {x y : α} :
    Pnu P (n₀c A) x y ↔ Nonempty β ∧ A.Finite ∧ pwr P (Nat.card A) x y := by
  rw [Pnu_pwr hP hJ]
  constructor
  · rintro ⟨hβ, B, hB, hAB, hk⟩
    obtain ⟨e⟩ := eq_n₀c_iff_equiv.1 hAB
    have : Finite ↥B := hB.to_subtype
    have : Finite ↥A := Finite.of_equiv _ e.symm
    exact ⟨hβ, Set.toFinite A, by rwa [Nat.card_congr e]⟩
  · rintro ⟨hβ, hA, hk⟩
    exact ⟨hβ, A, hA, rfl, hk⟩

private theorem Pnu_empty {α β : Type*} {P : α → α → Prop} {x y : α} :
    ¬ Pnu P (∅ : Set (Set β)) x y := fun h => by
  obtain ⟨-, B, hB, -⟩ := Pnu_iff.1 h
  exact n₀c_ne_empty B hB.symm

private theorem pwr_one_many {α : Type*} {P : α → α → Prop} (hP : P ∈ arrow one Cls) :
    ∀ {k : ℕ} {x y z : α}, pwr P k x z → pwr P k y z → x = y
  | 0, _, _, _, ⟨rfl, _⟩, ⟨rfl, _⟩ => rfl
  | _ + 1, _, _, z, ⟨w, hw, hwz⟩, ⟨w', hw', hw'z⟩ => by
    have : w = w' := mem_arrow_one_Cls.1 hP w w' z ⟨hwz, hw'z⟩
    subst this
    exact pwr_one_many hP hw hw'

/-- ✱121·331. \(\vdash \colon\ldotp P \in 1\rightarrow \text{Cls}.P_{\text{po}}\,\unicode{x2abd}\, J.\supset :xP_{\nu }(Pʻy).\equiv .xP_{\nu +_{c}1}y\)

The subscript `ν +_c 1` (by ✱121·02 an argument of `+_c`) is in an adequate type `W` (IIT); `P'y` is a description with the smallest scope.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
subscript `ν +_c 1` is adequate. -/
theorem pm121_331 {α β W : Type*} {P : α → α → Prop} {ν : Set (Set β)} {x y : α} :
    AdeqAdd W ν (one : Set (Set β)) → (P ∈ arrow one Cls ∧ po P ⪽ J) →
    (Desc P y (fun w => Pnu P ν x w) ↔ Pnu P (ν +ᶜ (one : Set (Set β)) : Set (Set W)) x y) := by
  rintro hW ⟨hP, hJ⟩
  have h1 := mem_arrow_one_Cls.1 hP
  have hU : P ∈ arrow one Cls ∪ arrow Cls one := Or.inl hP
  rw [Pnu_pwr hU hJ]
  constructor
  · rintro ⟨w, hw, hν⟩
    have hwy : P w y := (hw w).2 rfl
    obtain ⟨⟨b⟩, A, hA, rfl, hk⟩ := (Pnu_pwr hU hJ).1 hν
    obtain ⟨f⟩ := adeqAdd_emb hW A {b}
    have : Finite ↥A := hA.to_subtype
    refine ⟨⟨f (Sum.inr ⟨b, rfl⟩)⟩, Set.range f, Set.finite_range f, ?_, ?_⟩
    · rw [one_eq_n₀c_singleton b, cardAdd_n₀c, n₀c_eq_ncT]
      exact ncT_congr (Equiv.ofInjective f f.injective)
    · rw [← Nat.card_congr (Equiv.ofInjective f f.injective), Nat.card_sum,
        Nat.card_unique (α := ↥({b} : Set β))]
      exact ⟨w, hk, hwy⟩
  · rintro ⟨-, C, hC, hCe, hk⟩
    have hC' : C ∈ (ν +ᶜ (one : Set (Set β)) : Set (Set W)) := hCe ▸ self_mem_n₀c C
    obtain ⟨A, O, ⟨hA, hO⟩, ⟨e⟩⟩ := mem_cardAdd'.1 hC'
    obtain ⟨o, -⟩ : O ∈ (one : Set (Set β)) := hO ▸ self_mem_n₀c O
    obtain ⟨u⟩ := unit_of_mem_one (hO ▸ self_mem_n₀c O)
    have : Finite ↥C := hC.to_subtype
    have : Finite ↥A := finite_left_of_equiv e
    have hcard : Nat.card ↥C = Nat.card ↥A + 1 := by
      rw [Nat.card_congr (e.trans ((Equiv.refl _).sumCongr u)), Nat.card_sum,
        Nat.card_unique (α := PUnit.{1})]
    rw [hcard] at hk
    obtain ⟨w, hw, hwy⟩ := hk
    refine ⟨w, fun u' => ⟨fun h => h1 u' w y ⟨h, hwy⟩, fun h => h ▸ hwy⟩, ?_⟩
    exact (Pnu_pwr hU hJ).2 ⟨⟨o⟩, A, Set.toFinite A, hA, hw⟩

/-- ✱121·332. \(\vdash : P \in 1 \rightarrow \text{Cls}. P_{\text{po}} \,\unicode{x2abd}\, J. \supset . P_{\nu +_{c} 1} = P_{\nu } \mid P \quad[*121·331]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
subscript `ν +_c 1` is adequate. -/
theorem pm121_332 {α β W : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    AdeqAdd W ν (one : Set (Set β)) → (P ∈ arrow one Cls ∧ po P ⪽ J) →
      Pnu P (ν +ᶜ (one : Set (Set β)) : Set (Set W)) = Pnu P ν ⨾ P := by
  intro hW h
  have h1 := mem_arrow_one_Cls.1 h.1
  funext x y
  apply propext
  rw [← pm121_331 hW h]
  constructor
  · rintro ⟨w, hw, hν⟩
    exact ⟨w, hν, (hw w).2 rfl⟩
  · rintro ⟨w, hν, hwy⟩
    exact ⟨w, fun u => ⟨fun h' => h1 u w y ⟨h', hwy⟩, fun h' => h' ▸ hwy⟩, hν⟩

/-- ✱121·333. \(\vdash : P \in \text{Cls} \rightarrow 1. P_{\text{po}} \,\unicode{x2abd}\, J. \supset . P_{\nu +_{c} 1} = P \mid P_{\nu }\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
subscript `ν +_c 1` is adequate. -/
theorem pm121_333 {α β W : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    AdeqAdd W ν (one : Set (Set β)) → (P ∈ arrow Cls one ∧ po P ⪽ J) →
      Pnu P (ν +ᶜ (one : Set (Set β)) : Set (Set W)) = P ⨾ Pnu P ν := by
  rintro hW ⟨hP, hJ⟩
  have h := pm121_332 (P := P˘) hW ⟨arrow_cnv.1 hP, J_cnv hJ⟩
  funext x y
  have := congrFun (congrFun h y) x
  apply propext
  rw [← Pnu_cnv, this]
  constructor
  · rintro ⟨w, hw, hwx⟩
    exact ⟨w, hwx, Pnu_cnv.1 hw⟩
  · rintro ⟨w, hxw, hw⟩
    exact ⟨w, Pnu_cnv.2 hw, hxw⟩

/-- ✱121·34. \(\vdash : P \in 1 \rightarrow \text{Cls}. P_{\text{po}} \,\unicode{x2abd}\, J. \nu \in \text{NC induct}. \supset . P_{\nu } \in 1 \rightarrow \text{Cls}\) -/
theorem pm121_34 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    ((P ∈ arrow one Cls ∧ po P ⪽ J) ∧ ν ∈ NCinduct) → Pnu P ν ∈ arrow one Cls := by
  rintro ⟨⟨hP, hJ⟩, -⟩
  refine mem_arrow_one_Cls.2 fun x y z ⟨hx, hy⟩ => ?_
  obtain ⟨-, A, -, rfl, hkA⟩ := (Pnu_pwr (Or.inl hP) hJ).1 hx
  obtain ⟨-, B, -, hB, hkB⟩ := (Pnu_pwr (Or.inl hP) hJ).1 hy
  obtain ⟨e⟩ := eq_n₀c_iff_equiv.1 hB
  rw [Nat.card_congr e] at hkA
  exact pwr_one_many hP hkA hkB

/-- ✱121·341. \(\vdash : P \in \text{Cls} \rightarrow 1. P_{\text{po}} \,\unicode{x2abd}\, J. \nu \in \text{NC induct}. \supset . P_{\nu } \in \text{Cls} \rightarrow 1\) -/
theorem pm121_341 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    ((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ ν ∈ NCinduct) → Pnu P ν ∈ arrow Cls one := by
  rintro ⟨⟨hP, hJ⟩, hν⟩
  rw [arrow_cnv, pm121_26]
  exact pm121_34 ⟨⟨arrow_cnv.1 hP, J_cnv hJ⟩, hν⟩

/-- ✱121·342. \(\vdash : P \in 1 \rightarrow 1. P_{\text{po}} \,\unicode{x2abd}\, J. \nu \in \text{NC induct}. \supset . P_{\nu } \in 1 \rightarrow 1 \quad[*121·34·341]\) -/
theorem pm121_342 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    ((P ∈ arrow one one ∧ po P ⪽ J) ∧ ν ∈ NCinduct) → Pnu P ν ∈ arrow one one := by
  rintro ⟨⟨hP, hJ⟩, hν⟩
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hP
  have a := pm121_34 ⟨⟨mem_arrow_one_Cls.2 h1, hJ⟩, hν⟩
  have b := pm121_341 ⟨⟨mem_arrow_Cls_one.2 h2, hJ⟩, hν⟩
  exact mem_arrow_one_one.2 ⟨mem_arrow_one_Cls.1 a, mem_arrow_Cls_one.1 b⟩

private theorem comp_Pnu_pwr {α β γ : Type*} {P : α → α → Prop}
    (hP : P ∈ arrow one Cls ∪ arrow Cls one) (hJ : po P ⪽ J) {μ : Set (Set β)}
    {ν : Set (Set γ)} {x z : α} :
    (Pnu P μ ⨾ Pnu P ν) x z ↔ (Nonempty β ∧ Nonempty γ) ∧ ∃ (A : Set β) (B : Set γ),
      (A.Finite ∧ B.Finite) ∧ (μ = n₀c A ∧ ν = n₀c B) ∧ pwr P (Nat.card A + Nat.card B) x z := by
  constructor
  · rintro ⟨y, h1, h2⟩
    obtain ⟨hβ, A, hA, hμ, hk1⟩ := (Pnu_pwr hP hJ).1 h1
    obtain ⟨hγ, B, hB, hν, hk2⟩ := (Pnu_pwr hP hJ).1 h2
    exact ⟨⟨hβ, hγ⟩, A, B, ⟨hA, hB⟩, ⟨hμ, hν⟩, pwr_add.2 ⟨y, hk1, hk2⟩⟩
  · rintro ⟨⟨hβ, hγ⟩, A, B, ⟨hA, hB⟩, ⟨hμ, hν⟩, hk⟩
    obtain ⟨y, hk1, hk2⟩ := pwr_add.1 hk
    exact ⟨y, (Pnu_pwr hP hJ).2 ⟨hβ, A, hA, hμ, hk1⟩, (Pnu_pwr hP hJ).2 ⟨hγ, B, hB, hν, hk2⟩⟩

private theorem Pnu_add {α β γ W : Type*} [Nonempty β] [Nonempty γ] {P : α → α → Prop}
    {μ : Set (Set β)} {ν : Set (Set γ)} (hW : AdeqAdd W μ ν)
    (hP : P ∈ arrow one Cls ∪ arrow Cls one) (hJ : po P ⪽ J) :
    Pnu P μ ⨾ Pnu P ν = Pnu P (μ +ᶜ ν : Set (Set W)) := by
  funext x z
  apply propext
  rw [comp_Pnu_pwr hP hJ, Pnu_pwr hP hJ]
  constructor
  · rintro ⟨-, A, B, ⟨hA, hB⟩, ⟨rfl, rfl⟩, hk⟩
    obtain ⟨f⟩ := adeqAdd_emb hW A B
    have : Finite ↥A := hA.to_subtype
    have : Finite ↥B := hB.to_subtype
    refine ⟨?_, Set.range f, Set.finite_range f, ?_, ?_⟩
    · obtain ⟨g, -⟩ := adeqAdd_iff.1 hW
      exact ⟨g (Sum.inl (Classical.arbitrary β))⟩
    · rw [cardAdd_n₀c, n₀c_eq_ncT]
      exact ncT_congr (Equiv.ofInjective f f.injective)
    · rwa [← Nat.card_congr (Equiv.ofInjective f f.injective), Nat.card_sum]
  · rintro ⟨-, C, hC, hCe, hk⟩
    have hC' : C ∈ (μ +ᶜ ν : Set (Set W)) := hCe ▸ self_mem_n₀c C
    obtain ⟨A, B, ⟨hA, hB⟩, ⟨e⟩⟩ := mem_cardAdd'.1 hC'
    have : Finite ↥C := hC.to_subtype
    have : Finite ↥A := finite_left_of_equiv e
    have : Finite ↥B := finite_right_of_equiv e
    refine ⟨⟨inferInstance, inferInstance⟩, A, B, ⟨Set.toFinite A, Set.toFinite B⟩, ⟨hA, hB⟩, ?_⟩
    rwa [Nat.card_congr e, Nat.card_sum] at hk

/-- ✱121·35. \(\vdash : P \in 1 \rightarrow \text{Cls}. P_{\text{po}} \,\unicode{x2abd}\, J. \mu , \nu \in \text{NC induct}. \supset . P_{\mu } \mid P_{\nu } = P_{\mu +_{c} \nu }\)

`μ, ν ∈ NC induct` does not identify their types; the subscript `μ +_c ν` is in an adequate type `W` (IIT).

`[Nonempty β]`, `[Nonempty γ]`: the `1`s of `μ +_c 1`, `ν +_c 1` (✱121·02) are in the types of `μ`,
`ν`; in an empty type `P₀ = Λ̇` and the law fails (`μ = 0`).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
subscript `μ +_c ν` is adequate; PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty β]`, `[Nonempty γ]`. -/
theorem pm121_35 {α β γ W : Type*} [Nonempty β] [Nonempty γ] {P : α → α → Prop}
    {μ : Set (Set β)} {ν : Set (Set γ)} :
    AdeqAdd W μ ν → ((P ∈ arrow one Cls ∧ po P ⪽ J) ∧ (μ ∈ NCinduct ∧ ν ∈ NCinduct)) →
      Pnu P μ ⨾ Pnu P ν = Pnu P (μ +ᶜ ν : Set (Set W)) :=
  fun hW h => Pnu_add hW (Or.inl h.1.1) h.1.2

/-- ✱121·351. \(\vdash : P \in \text{Cls} \rightarrow 1. P_{\text{po}} \,\unicode{x2abd}\, J. \mu , \nu \in \text{NC induct}. \supset . P_{\mu } \mid P_{\nu } = P_{\mu +_{c} \nu }\)

**Status.** proved (reading): as ✱121·35 (convention IIT for the type `W` of `μ +_c ν`;
`[Nonempty β]`, `[Nonempty γ]`, PM assumes every type has a member). -/
theorem pm121_351 {α β γ W : Type*} [Nonempty β] [Nonempty γ] {P : α → α → Prop}
    {μ : Set (Set β)} {ν : Set (Set γ)} :
    AdeqAdd W μ ν → ((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ (μ ∈ NCinduct ∧ ν ∈ NCinduct)) →
      Pnu P μ ⨾ Pnu P ν = Pnu P (μ +ᶜ ν : Set (Set W)) :=
  fun hW h => Pnu_add hW (Or.inr h.1.1) h.1.2

/-- ✱121·352. \[\begin{align}\vdash : P \in (1 \rightarrow \text{Cls}) \cup (\text{Cls} \rightarrow 1). &P_{\text{po}} \,\unicode{x2abd}\, J. \mu , \nu \in \text{NC induct}. \supset .\\ &P_{\mu } \mid P_{\nu } = P_{\nu } \mid P_{\mu } \quad[*121·35·351.*110·51]\end{align}\] -/
theorem pm121_352 {α β γ : Type*} {P : α → α → Prop} {μ : Set (Set β)} {ν : Set (Set γ)} :
    ((P ∈ arrow one Cls ∪ arrow Cls one ∧ po P ⪽ J) ∧ (μ ∈ NCinduct ∧ ν ∈ NCinduct)) →
      Pnu P μ ⨾ Pnu P ν = Pnu P ν ⨾ Pnu P μ := by
  rintro ⟨⟨hP, hJ⟩, -⟩
  funext x z
  apply propext
  rw [comp_Pnu_pwr hP hJ, comp_Pnu_pwr hP hJ]
  constructor
  · rintro ⟨⟨h1, h2⟩, A, B, ⟨hA, hB⟩, ⟨hμ, hν⟩, hk⟩
    exact ⟨⟨h2, h1⟩, B, A, ⟨hB, hA⟩, ⟨hν, hμ⟩, by rwa [Nat.add_comm]⟩
  · rintro ⟨⟨h1, h2⟩, A, B, ⟨hA, hB⟩, ⟨hμ, hν⟩, hk⟩
    exact ⟨⟨h2, h1⟩, B, A, ⟨hB, hA⟩, ⟨hν, hμ⟩, by rwa [Nat.add_comm]⟩

private theorem NCinduct_ne_zero_cases {β : Type*} {μ : Set (Set β)} (h : μ ∈ NCinduct \ ι zero) :
    μ = ∅ ∨ ∃ A : Set β, A.Finite ∧ A.Nonempty ∧ μ = n₀c A := by
  obtain ⟨h1, h2⟩ := h
  rcases NCinduct_cases h1 with ⟨A, hA, rfl⟩ | ⟨-, rfl⟩
  · refine Or.inr ⟨A, hA, ?_, rfl⟩
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact h2 (mem_unitCls.2 zero_eq_n₀c_empty.symm)
  · exact Or.inl rfl

private theorem pwr_pwr {α : Type*} {P R : α → α → Prop} {m : ℕ}
    (hR : ∀ x y, R x y ↔ pwr P m x y) :
    ∀ (n : ℕ) {x z : α}, pwr R (n + 1) x z ↔ pwr P ((n + 1) * m) x z
  | 0, x, z => by
    simp only [Nat.zero_add, Nat.one_mul]
    rw [pwr_one, hR]
  | n + 1, x, z => by
    rw [pwr_succ, Nat.add_mul, Nat.one_mul, pwr_add]
    exact exists_congr fun w => and_congr (pwr_pwr hR n) (hR w z)

private theorem transGen_of_pwr {α : Type*} {P : α → α → Prop} :
    ∀ {k : ℕ} {x y : α}, pwr P (k + 1) x y → Relation.TransGen P x y
  | 0, _, _, ⟨_, ⟨rfl, _⟩, h⟩ => Relation.TransGen.single h
  | _ + 1, _, _, ⟨_, hw, h⟩ => (transGen_of_pwr hw).tail h

/-- `(P_μ)_ν` for `μ, ν ∈ NC induct − ι'0`: `x (P^{mn}) z` for `m`, `n` the numbers of terms of
finite classes with cardinals `μ`, `ν`. -/
private theorem Pnu_Pnu {α β γ : Type*} {P : α → α → Prop}
    (hP : P ∈ arrow one Cls ∪ arrow Cls one) (hJ : po P ⪽ J) {μ : Set (Set β)}
    {ν : Set (Set γ)} (hμ : μ ∈ NCinduct \ ι zero) (hν : ν ∈ NCinduct \ ι zero) {x z : α} :
    Pnu (Pnu P μ) ν x z ↔ ∃ (A : Set β) (B : Set γ), (A.Finite ∧ A.Nonempty) ∧
      (B.Finite ∧ B.Nonempty) ∧ (μ = n₀c A ∧ ν = n₀c B) ∧ pwr P (Nat.card A * Nat.card B) x z := by
  rcases NCinduct_ne_zero_cases hμ with rfl | ⟨A, hA, hAne, rfl⟩
  · constructor
    · intro h
      obtain ⟨u, hu | hu⟩ := (anc_of_Pnu h).1 <;> exact absurd hu Pnu_empty
    · rintro ⟨A, B, -, -, ⟨hA, -⟩, -⟩
      exact absurd hA.symm (n₀c_ne_empty A)
  rcases NCinduct_ne_zero_cases hν with rfl | ⟨B, hB, hBne, rfl⟩
  · constructor
    · intro h; exact absurd h Pnu_empty
    · rintro ⟨A', B, -, -, ⟨-, hB⟩, -⟩
      exact absurd hB.symm (n₀c_ne_empty B)
  have hβ : Nonempty β := ⟨hAne.some⟩
  have hγ : Nonempty γ := ⟨hBne.some⟩
  have : Finite ↥A := hA.to_subtype
  have : Finite ↥B := hB.to_subtype
  have : Nonempty ↥A := hAne.to_subtype
  have : Nonempty ↥B := hBne.to_subtype
  have hR : ∀ a b, Pnu P (n₀c A) a b ↔ pwr P (Nat.card ↥A) a b := fun a b => by
    rw [Pnu_n₀c_pwr hP hJ]
    exact ⟨fun h => h.2.2, fun h => ⟨hβ, hA, h⟩⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥A = k + 1 := Nat.exists_eq_succ_of_ne_zero Nat.card_pos.ne'
  have hRP : Pnu P (n₀c A) ∈ arrow one Cls ∪ arrow Cls one := by
    rcases hP with hP | hP
    · exact Or.inl (pm121_34 ⟨⟨hP, hJ⟩, hμ.1⟩)
    · exact Or.inr (pm121_341 ⟨⟨hP, hJ⟩, hμ.1⟩)
  have hRJ : po (Pnu P (n₀c A)) ⪽ J := by
    intro a b h e
    subst e
    have key : ∀ a b, Relation.TransGen (Pnu P (n₀c A)) a b → Relation.TransGen P a b := by
      intro a b h
      induction h with
      | single h => rw [hR, hk] at h; exact transGen_of_pwr h
      | tail _ h ih => rw [hR, hk] at h; exact ih.trans (transGen_of_pwr h)
    exact hJ a a (po_iff_transGen.2 (key a a (po_iff_transGen.1 h))) rfl
  obtain ⟨n, hn⟩ : ∃ n, Nat.card ↥B = n + 1 := Nat.exists_eq_succ_of_ne_zero Nat.card_pos.ne'
  rw [Pnu_n₀c_pwr hRP hRJ, hn, pwr_pwr hR n]
  constructor
  · rintro ⟨-, -, h⟩
    exact ⟨A, B, ⟨hA, hAne⟩, ⟨hB, hBne⟩, ⟨rfl, rfl⟩, by rwa [hn, Nat.mul_comm]⟩
  · rintro ⟨A', B', -, -, ⟨hA', hB'⟩, h⟩
    obtain ⟨e1⟩ := eq_n₀c_iff_equiv.1 hA'
    obtain ⟨e2⟩ := eq_n₀c_iff_equiv.1 hB'
    rw [← Nat.card_congr e1, ← Nat.card_congr e2, hn, Nat.mul_comm] at h
    exact ⟨hγ, hB, h⟩

/-- ✱121·36. \[\begin{align}\vdash : P \in (1 \rightarrow \text{Cls}) \cup (\text{Cls} \rightarrow 1). &P_{\text{po}} \,\unicode{x2abd}\, J. \mu , \nu \in \text{NC induct} -\iota ʻ0.\supset .\\ &(P_{\mu })_{\nu } = P_{\mu \times _{c} \nu }\end{align}\]

The subscript `μ ×_c ν` is in an adequate type `W` (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
subscript `μ ×_c ν` is adequate. -/
theorem pm121_36 {α β γ W : Type*} {P : α → α → Prop} {μ : Set (Set β)} {ν : Set (Set γ)} :
    AdeqMul W μ ν → ((P ∈ arrow one Cls ∪ arrow Cls one ∧ po P ⪽ J) ∧
      (μ ∈ NCinduct \ ι zero ∧ ν ∈ NCinduct \ ι zero)) →
        Pnu (Pnu P μ) ν = Pnu P (μ ×ᶜ ν : Set (Set W)) := by
  rintro hW ⟨⟨hP, hJ⟩, hμ, hν⟩
  funext x z
  apply propext
  rw [Pnu_Pnu hP hJ hμ hν]
  rcases NCinduct_ne_zero_cases hμ with rfl | ⟨A, hA, hAne, rfl⟩
  · rw [cardMul_eq_empty_of_left (fun A h => n₀c_ne_empty A h.symm)]
    exact ⟨fun ⟨A, _, _, _, ⟨h, _⟩, _⟩ => absurd h.symm (n₀c_ne_empty A),
      fun h => absurd h Pnu_empty⟩
  rcases NCinduct_ne_zero_cases hν with rfl | ⟨B, hB, hBne, rfl⟩
  · rw [cardMul_eq_empty_of_right _ (fun B h => n₀c_ne_empty B h.symm)]
    exact ⟨fun ⟨_, B, _, _, ⟨_, h⟩, _⟩ => absurd h.symm (n₀c_ne_empty B),
      fun h => absurd h Pnu_empty⟩
  obtain ⟨f⟩ := adeqMul_emb hW A B
  have : Finite ↥A := hA.to_subtype
  have : Finite ↥B := hB.to_subtype
  have hD : (n₀c A ×ᶜ n₀c B : Set (Set W)) = n₀c (Set.range f) := by
    rw [cardMul_n₀c, n₀c_eq_ncT]
    exact ncT_congr (Equiv.ofInjective f f.injective)
  rw [hD, Pnu_n₀c_pwr hP hJ, ← Nat.card_congr (Equiv.ofInjective f f.injective), Nat.card_prod]
  constructor
  · rintro ⟨A', B', -, -, ⟨hA', hB'⟩, h⟩
    obtain ⟨e1⟩ := eq_n₀c_iff_equiv.1 hA'
    obtain ⟨e2⟩ := eq_n₀c_iff_equiv.1 hB'
    rw [← Nat.card_congr e1, ← Nat.card_congr e2] at h
    exact ⟨⟨f (⟨hAne.some, hAne.some_mem⟩, ⟨hBne.some, hBne.some_mem⟩)⟩, Set.finite_range f, h⟩
  · rintro ⟨-, -, h⟩
    exact ⟨A, B, ⟨hA, hAne⟩, ⟨hB, hBne⟩, ⟨rfl, rfl⟩, h⟩

/-- ✱121·361. \[\begin{align}\vdash :P\in (1\rightarrow \text{Cls})\cup (\text{Cls}\rightarrow 1).&P_{\text{po}}\,\unicode{x2abd}\, J.\mu ,\nu \in \text{NC induct}-\iota ʻ0.\supset .\\ &(P_{\mu })_{\nu }=(P_{\nu })_{\mu } [*121·36.*113·27]\end{align}\] -/
theorem pm121_361 {α β γ : Type*} {P : α → α → Prop} {μ : Set (Set β)} {ν : Set (Set γ)} :
    ((P ∈ arrow one Cls ∪ arrow Cls one ∧ po P ⪽ J) ∧
      (μ ∈ NCinduct \ ι zero ∧ ν ∈ NCinduct \ ι zero)) → Pnu (Pnu P μ) ν = Pnu (Pnu P ν) μ := by
  rintro ⟨⟨hP, hJ⟩, hμ, hν⟩
  funext x z
  apply propext
  rw [Pnu_Pnu hP hJ hμ hν, Pnu_Pnu hP hJ hν hμ]
  constructor
  · rintro ⟨A, B, h1, h2, ⟨e1, e2⟩, h⟩
    exact ⟨B, A, h2, h1, ⟨e2, e1⟩, by rwa [Nat.mul_comm]⟩
  · rintro ⟨A, B, h1, h2, ⟨e1, e2⟩, h⟩
    exact ⟨B, A, h2, h1, ⟨e2, e1⟩, by rwa [Nat.mul_comm]⟩

/-- ✱121·37. \(\vdash :P\in \text{Cls}\rightarrow 1.y\in P(x\vdash\dashv z).\supset .P(x\vdash\dashv z)=P(x\vdash\dashv y)\cup P(y\vdash\dashv z)\) -/
theorem pm121_37 {α : Type*} {P : α → α → Prop} {x y z : α} :
    P ∈ arrow Cls one ∧ y ∈ itvCC P x z → itvCC P x z = itvCC P x y ∪ itvCC P y z := by
  rintro ⟨hP, hxy, hyz⟩
  ext w
  simp only [pm121_103, Set.mem_union]
  constructor
  · rintro ⟨hxw, hwz⟩
    rcases rtg_comparable hP (anc_iff_reflTransGen.1 hxw).2 (anc_iff_reflTransGen.1 hxy).2
      with h | h
    · exact Or.inl ⟨hxw, anc_iff_reflTransGen.2 ⟨hwz.1, h⟩⟩
    · exact Or.inr ⟨anc_iff_reflTransGen.2 ⟨hyz.1, h⟩, hwz⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, anc_trans h2 hyz⟩
    · exact ⟨anc_trans hxy h1, h2⟩

/-- Two terms of an interval are comparable for `P ∈ (Cls → 1) ∪ (1 → Cls)`. -/
private theorem anc_comparable {α : Type*} {P : α → α → Prop}
    (hP : P ∈ arrow Cls one ∪ arrow one Cls) {x z a b : α} (hxa : anc P x a) (haz : anc P a z)
    (hxb : anc P x b) (hbz : anc P b z) : anc P a b ∨ anc P b a := by
  rcases hP with hP | hP
  · rcases rtg_comparable hP (anc_iff_reflTransGen.1 hxa).2 (anc_iff_reflTransGen.1 hxb).2
      with h | h
    · exact Or.inl (anc_iff_reflTransGen.2 ⟨haz.1, h⟩)
    · exact Or.inr (anc_iff_reflTransGen.2 ⟨hbz.1, h⟩)
  · have hP' : P˘ ∈ arrow Cls one := (arrow_cnv (P := P˘)).2 hP
    have hza : anc P˘ z a := anc_cnv.2 haz
    have hzb : anc P˘ z b := anc_cnv.2 hbz
    rcases rtg_comparable hP' (anc_iff_reflTransGen.1 hza).2 (anc_iff_reflTransGen.1 hzb).2
      with h | h
    · exact Or.inr (anc_cnv.1 (anc_iff_reflTransGen.2 ⟨fld_of_anc_right hza, h⟩))
    · exact Or.inl (anc_cnv.1 (anc_iff_reflTransGen.2 ⟨fld_of_anc_right hzb, h⟩))

/-- ✱121·371. \[\begin{align}\vdash :&P\in (\text{Cls}\rightarrow 1)\cup (1\rightarrow \text{Cls}).y\in P(x\vdash\dashv z).\supset .\\ &P(x\vdash\dashv z)=P(x\vdash\dashv y)\cup P(y\vdash\dashv z)=P(x \unicode{x27dd} y)\cup P(y\vdash\dashv z)\\ &=P(x\vdash\dashv y)\cup P(y\dashv z) \quad [\text{Proof as in *121·37}]\end{align}\]

The chain of three equations is the conjunction of its links. -/
theorem pm121_371 {α : Type*} {P : α → α → Prop} {x y z : α} :
    (P ∈ arrow Cls one ∪ arrow one Cls ∧ y ∈ itvCC P x z) →
    ((itvCC P x z = itvCC P x y ∪ itvCC P y z ∧
        itvCC P x y ∪ itvCC P y z = itvCO P x y ∪ itvCC P y z) ∧
      itvCO P x y ∪ itvCC P y z = itvCC P x y ∪ itvOC P y z) := by
  rintro ⟨hP, hxy, hyz⟩
  have e1 : itvCC P x z = itvCC P x y ∪ itvCC P y z := by
    ext w
    simp only [pm121_103, Set.mem_union]
    constructor
    · rintro ⟨hxw, hwz⟩
      rcases anc_comparable hP hxw hwz hxy hyz with h | h
      · exact Or.inl ⟨hxw, h⟩
      · exact Or.inr ⟨h, hwz⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, anc_trans h2 hyz⟩
      · exact ⟨anc_trans hxy h1, h2⟩
  have e2 : itvCC P x y ∪ itvCC P y z = itvCO P x y ∪ itvCC P y z := by
    ext w
    simp only [pm121_103, pm121_102, Set.mem_union]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · rcases anc_iff_po.1 h2 with ⟨rfl, -⟩ | h2
        · exact Or.inr ⟨anc_refl (fld_of_anc_right h1), hyz⟩
        · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr h
    · rintro (⟨h1, h2⟩ | h)
      · exact Or.inl ⟨h1, anc_of_po h2⟩
      · exact Or.inr h
  have e3 : itvCC P x y ∪ itvCC P y z = itvCC P x y ∪ itvOC P y z := by
    ext w
    simp only [pm121_103, pm121_101, Set.mem_union]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h1
        · exact Or.inl ⟨hxy, anc_refl (fld_of_anc_right hxy)⟩
        · exact Or.inr ⟨h1, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨anc_of_po h1, h2⟩
  exact ⟨⟨e1, e2⟩, e2.symm.trans e3⟩

/-- ✱121·372. \[\begin{align}\vdash :&P\in (\text{Cls}\rightarrow 1)\cup (1\rightarrow \text{Cls}).y\in P(x\dashv z).\supset .\\ &P(x\dashv z)=P(x\dashv y)\cup P(y\dashv z)=P(x\dashv y)\cup P(y\vdash\dashv z)\end{align}\] -/
theorem pm121_372 {α : Type*} {P : α → α → Prop} {x y z : α} :
    (P ∈ arrow Cls one ∪ arrow one Cls ∧ y ∈ itvOC P x z) →
    (itvOC P x z = itvOC P x y ∪ itvOC P y z ∧ itvOC P x y ∪ itvOC P y z = itvOC P x y ∪ itvCC P y z) := by
  rintro ⟨hP, hxy, hyz⟩
  refine ⟨?_, ?_⟩
  · ext w
    simp only [pm121_101, Set.mem_union]
    constructor
    · rintro ⟨hxw, hwz⟩
      rcases anc_comparable hP (anc_of_po hxw) hwz (anc_of_po hxy) hyz with h | h
      · exact Or.inl ⟨hxw, h⟩
      · rcases anc_iff_po.1 h with ⟨rfl, -⟩ | h
        · exact Or.inl ⟨hxw, anc_refl (fld_of_po_right hxw)⟩
        · exact Or.inr ⟨h, hwz⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, anc_trans h2 hyz⟩
      · exact ⟨po_of_po_anc hxy (anc_of_po h1), h2⟩
  · ext w
    simp only [pm121_101, pm121_103, Set.mem_union]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨anc_of_po h1, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h1
        · exact Or.inl ⟨hxy, anc_refl (fld_of_po_right hxy)⟩
        · exact Or.inr ⟨h1, h2⟩

/-- ✱121·373. \[\begin{align}\vdash :&P\in (\text{Cls}\rightarrow 1)\cup (1\rightarrow \text{Cls}).y\in P(x \unicode{x27dd} z).\supset .\\ &P(x \unicode{x27dd} z)=P(x \unicode{x27dd} y)\cup P(y \unicode{x27dd} z)= P(x\vdash\dashv y)\cup P(y \unicode{x27dd} z)\end{align}\] -/
theorem pm121_373 {α : Type*} {P : α → α → Prop} {x y z : α} :
    (P ∈ arrow Cls one ∪ arrow one Cls ∧ y ∈ itvCO P x z) →
    (itvCO P x z = itvCO P x y ∪ itvCO P y z ∧ itvCO P x y ∪ itvCO P y z = itvCC P x y ∪ itvCO P y z) := by
  rintro ⟨hP, hxy, hyz⟩
  refine ⟨?_, ?_⟩
  · ext w
    simp only [pm121_102, Set.mem_union]
    constructor
    · rintro ⟨hxw, hwz⟩
      rcases anc_comparable hP hxw (anc_of_po hwz) hxy (anc_of_po hyz) with h | h
      · rcases anc_iff_po.1 h with ⟨rfl, -⟩ | h
        · exact Or.inr ⟨anc_refl (fld_of_po_left hwz), hwz⟩
        · exact Or.inl ⟨hxw, h⟩
      · exact Or.inr ⟨h, hwz⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, po_of_po_anc h2 (anc_of_po hyz)⟩
      · exact ⟨anc_trans hxy h1, h2⟩
  · ext w
    simp only [pm121_102, pm121_103, Set.mem_union]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact Or.inl ⟨h1, anc_of_po h2⟩
      · exact Or.inr h
    · rintro (⟨h1, h2⟩ | h)
      · rcases anc_iff_po.1 h2 with ⟨rfl, -⟩ | h2
        · exact Or.inr ⟨anc_refl (fld_of_po_left hyz), hyz⟩
        · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr h

/-- ✱121·374. \[\begin{align}\vdash :&P\in (\text{Cls}\rightarrow 1)\cup (1\rightarrow \text{Cls}).y\in P(x\unicode{x2013}z).\supset .\\ &P(x\unicode{x2013}z)=P(x\dashv y)\cup P(y-z)=P(x\unicode{x2013}y)\cup P(y \unicode{x27dd} z)\\ &=P(x\dashv y)\cup P(y \unicode{x27dd} z)\end{align}\]

The e-text's `P(y-z)` is `P(y – z)`. -/
theorem pm121_374 {α : Type*} {P : α → α → Prop} {x y z : α} :
    (P ∈ arrow Cls one ∪ arrow one Cls ∧ y ∈ itvOO P x z) →
    ((itvOO P x z = itvOC P x y ∪ itvOO P y z ∧ itvOC P x y ∪ itvOO P y z = itvOO P x y ∪ itvCO P y z) ∧
      itvOO P x y ∪ itvCO P y z = itvOC P x y ∪ itvCO P y z) := by
  rintro ⟨hP, hxy, hyz⟩
  have e1 : itvOO P x z = itvOC P x y ∪ itvOO P y z := by
    ext w
    simp only [pm121_1, pm121_101, Set.mem_union]
    constructor
    · rintro ⟨hxw, hwz⟩
      rcases anc_comparable hP (anc_of_po hxw) (anc_of_po hwz) (anc_of_po hxy) (anc_of_po hyz)
        with h | h
      · exact Or.inl ⟨hxw, h⟩
      · rcases anc_iff_po.1 h with ⟨rfl, -⟩ | h
        · exact Or.inl ⟨hxw, anc_refl (fld_of_po_right hxw)⟩
        · exact Or.inr ⟨h, hwz⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, po_of_anc_po h2 hyz⟩
      · exact ⟨po_of_po_anc hxy (anc_of_po h1), h2⟩
  refine ⟨⟨e1, ?_⟩, ?_⟩
  · rw [pm121_24 hxy, pm121_241 hyz]; ext w; simp only [Set.mem_union]; tauto
  · rw [pm121_24 hxy, pm121_241 hyz]; ext w; simp only [Set.mem_union]; tauto

/-- On a cycle of a many-one relation every descendant of `x` is an ancestor of `x`. -/
private theorem rtg_back_of_cycle {α : Type*} {R : α → α → Prop} (hR : R ∈ arrow Cls one)
    {x w : α} (hx : Relation.TransGen R x x) (h : Relation.ReflTransGen R x w) :
    Relation.ReflTransGen R w x := by
  have h1 := mem_arrow_Cls_one.1 hR
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail v w _ hvw ih =>
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 ih with h | h
    · subst h
      obtain ⟨s, hs, hsx⟩ := Relation.TransGen.head'_iff.1 hx
      have : s = w := h1 _ s w ⟨hs, hvw⟩
      exact this ▸ hsx
    · obtain ⟨s, hs, hsx⟩ := Relation.TransGen.head'_iff.1 h
      have : s = w := h1 v s w ⟨hs, hvw⟩
      exact this ▸ hsx

/-- ✱121·38. \(\vdash :R\in \text{Cls}\rightarrow 1.xR_{\text{po}}x.\supset .R(x\vdash\dashv x)=\overleftarrow{R}_{*}ʻx \quad[*97·5]\) -/
theorem pm121_38 {α : Type*} {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one ∧ po R x x → itvCC R x x = rels (anc R) x := by
  rintro ⟨hR, hx⟩
  ext w
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [po_iff_transGen] at hx
  exact anc_iff_reflTransGen.2 ⟨fld_of_anc_right h,
    rtg_back_of_cycle hR hx (anc_iff_reflTransGen.1 h).2⟩

/-- ✱121·381. \(\vdash :R\in 1\rightarrow \text{Cls}.xR_{\text{po}}x.\supset .R(x\vdash\dashv x)=\overrightarrow{R}_{*}ʻx \quad[*97·501]\) -/
theorem pm121_381 {α : Type*} {R : α → α → Prop} {x : α} :
    R ∈ arrow one Cls ∧ po R x x → itvCC R x x = refs (anc R) x := by
  rintro ⟨hR, hx⟩
  have hR' : R˘ ∈ arrow Cls one := by rw [arrow_cnv]; exact hR
  rw [pm121_143, pm121_38 ⟨hR', po_cnv.2 hx⟩]
  ext w
  exact anc_cnv

/-- On a cycle of a many-one relation all four intervals between two of its terms are the
posterity of either. -/
private theorem cyc_itv_eq {α : Type*} {R : α → α → Prop} (hR : R ∈ arrow Cls one) {x y : α}
    (hx : po R x x) (hy : y ∈ itvCC R x x) :
    (itvCC R x x = rels (anc R) x ∧ itvCC R x y = rels (anc R) x) ∧
      (itvCC R y x = rels (anc R) x ∧ itvCC R y y = rels (anc R) x) := by
  have hxx : Relation.TransGen R x x := po_iff_transGen.1 hx
  have back : ∀ w, anc R x w → anc R w x := fun w h =>
    anc_iff_reflTransGen.2 ⟨fld_of_anc_right h, rtg_back_of_cycle hR hxx (anc_iff_reflTransGen.1 h).2⟩
  obtain ⟨hxy, hyx⟩ := hy
  refine ⟨⟨pm121_38 ⟨hR, hx⟩, ?_⟩, ?_, ?_⟩
  · ext w
    exact ⟨fun h => h.1, fun h => ⟨h, anc_trans (back w h) hxy⟩⟩
  · ext w
    exact ⟨fun h => anc_trans hxy h.1, fun h => ⟨anc_trans hyx h, back w h⟩⟩
  · ext w
    exact ⟨fun h => anc_trans hxy h.1, fun h => ⟨anc_trans hyx h, anc_trans (back w h) hxy⟩⟩

/-- ✱121·382. \[\begin{align}\vdash :&R\in \text{Cls}\rightarrow 1.xR_{\text{po}}x.xR_{\text{po}}y.\supset .\\ &R(x\vdash\dashv x)=R(x\vdash\dashv y)=\overleftarrow{R}_{*}ʻx= R(y\vdash\dashv y) \quad[*97·5.*91·56]\end{align}\] -/
theorem pm121_382 {α : Type*} {R : α → α → Prop} {x y : α} :
    ((R ∈ arrow Cls one ∧ po R x x) ∧ po R x y) →
    ((itvCC R x x = itvCC R x y ∧ itvCC R x y = rels (anc R) x) ∧ rels (anc R) x = itvCC R y y) := by
  rintro ⟨⟨hR, hx⟩, hxy⟩
  have hy : y ∈ itvCC R x x := by
    rw [pm121_38 ⟨hR, hx⟩]; exact anc_of_po hxy
  obtain ⟨⟨a, b⟩, -, d⟩ := cyc_itv_eq hR hx hy
  exact ⟨⟨a.trans b.symm, b⟩, d.symm⟩

/-- ✱121·383. \[\begin{align}\vdash :&R\in 1\rightarrow \text{Cls}.xR_{\text{po}}x.yR_{\text{po}}x.\supset .\\ &R(x\vdash\dashv x)=R(y\vdash\dashv x)=\overrightarrow{R}_{*}ʻx=R(y\vdash\dashv y)\end{align}\] -/
theorem pm121_383 {α : Type*} {R : α → α → Prop} {x y : α} :
    ((R ∈ arrow one Cls ∧ po R x x) ∧ po R y x) →
    ((itvCC R x x = itvCC R y x ∧ itvCC R y x = refs (anc R) x) ∧ refs (anc R) x = itvCC R y y) := by
  rintro ⟨⟨hR, hx⟩, hyx⟩
  have t : ∀ a b, itvCC R˘ a b = itvCC R b a := fun a b => (pm121_143 (P := R) (x := b) (y := a)).symm
  have hr : rels (anc R˘) x = refs (anc R) x := by ext w; exact anc_cnv
  obtain ⟨⟨h1, h2⟩, h3⟩ := pm121_382 (R := R˘) (x := x) (y := y)
    ⟨⟨(arrow_cnv (P := R˘)).2 hR, po_cnv.2 hx⟩, po_cnv.2 hyx⟩
  rw [t, t] at h1
  rw [t, hr] at h2
  rw [t, hr] at h3
  exact ⟨⟨h1, h2⟩, h3⟩

/-- ✱121·384. \[\begin{align}\vdash :&R\in (\text{Cls}\rightarrow 1)\cup (1\rightarrow \text{Cls}).xR_{\text{po}}x.y\in R(x\vdash\dashv x).\supset .\\ &R(x\vdash\dashv x)= R(x\vdash\dashv y)=R(y\vdash\dashv x)=R(y\vdash\dashv y) \quad[*121·382·383]\end{align}\] -/
theorem pm121_384 {α : Type*} {R : α → α → Prop} {x y : α} :
    ((R ∈ arrow Cls one ∪ arrow one Cls ∧ po R x x) ∧ y ∈ itvCC R x x) →
    ((itvCC R x x = itvCC R x y ∧ itvCC R x y = itvCC R y x) ∧ itvCC R y x = itvCC R y y) := by
  rintro ⟨⟨hR, hx⟩, hy⟩
  rcases hR with hR | hR
  · obtain ⟨⟨a, b⟩, c, d⟩ := cyc_itv_eq hR hx hy
    exact ⟨⟨a.trans b.symm, b.trans c.symm⟩, c.trans d.symm⟩
  · have t : ∀ a b, itvCC R˘ a b = itvCC R b a := fun a b =>
      (pm121_143 (P := R) (x := b) (y := a)).symm
    have hy' : y ∈ itvCC R˘ x x := by rw [t]; exact hy
    obtain ⟨⟨a, b⟩, c, d⟩ := cyc_itv_eq ((arrow_cnv (P := R˘)).2 hR) (po_cnv.2 hx) hy'
    rw [t] at a b c d
    exact ⟨⟨a.trans c.symm, c.trans b.symm⟩, b.trans d.symm⟩

/-- ✱121·39. \(\vdash \colon\ldotp R\in \text{Cls}\rightarrow 1.\supset :R(x\vdash\dashv y)\subset R(x\vdash\dashv z).\lor.R(x\vdash\dashv z)\subset R(x\vdash\dashv y)\) -/
theorem pm121_39 {α : Type*} {R : α → α → Prop} {x y z : α} :
    R ∈ arrow Cls one → (itvCC R x y ⊆ itvCC R x z ∨ itvCC R x z ⊆ itvCC R x y) := by
  intro hR
  by_cases hy : (itvCC R x y).Nonempty
  · by_cases hz : (itvCC R x z).Nonempty
    · have hxy := (pm121_23.2.2 hy).1.2
      have hxz := (pm121_23.2.2 hz).1.2
      rcases rtg_comparable hR (anc_iff_reflTransGen.1 hxy).2 (anc_iff_reflTransGen.1 hxz).2
        with h | h
      · exact Or.inl fun w hw => ⟨hw.1, anc_trans hw.2 (anc_iff_reflTransGen.2
          ⟨fld_of_anc_right hxy, h⟩)⟩
      · exact Or.inr fun w hw => ⟨hw.1, anc_trans hw.2 (anc_iff_reflTransGen.2
          ⟨fld_of_anc_right hxz, h⟩)⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hz
      exact Or.inr (hz ▸ Set.empty_subset _)
  · rw [Set.not_nonempty_iff_eq_empty] at hy
    exact Or.inl (hy ▸ Set.empty_subset _)

/-- ✱121·4. \(\vdash :R\in \text{Cls}\rightarrow 1.xRy.yR_{*}z.\supset .R(x\vdash\dashv z)=\iota ʻx\cup R(y\vdash\dashv z)\) -/
theorem pm121_4 {α : Type*} {R : α → α → Prop} {x y z : α} :
    (R ∈ arrow Cls one ∧ R x y) ∧ anc R y z → itvCC R x z = ι x ∪ itvCC R y z := by
  rintro ⟨⟨hR, hxy⟩, hyz⟩
  have h1 := mem_arrow_Cls_one.1 hR
  have hxy' : anc R x y :=
    anc_iff_reflTransGen.2 ⟨⟨y, Or.inl hxy⟩, Relation.ReflTransGen.single hxy⟩
  have hxz := anc_trans hxy' hyz
  ext w
  simp only [pm121_103, Set.mem_union, mem_unitCls]
  constructor
  · rintro ⟨hxw, hwz⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 (anc_iff_reflTransGen.1 hxw).2 with h | h
    · exact Or.inl h
    · obtain ⟨s, hs, hsw⟩ := Relation.TransGen.head'_iff.1 h
      have : s = y := h1 x s y ⟨hs, hxy⟩
      subst this
      exact Or.inr ⟨anc_iff_reflTransGen.2 ⟨hyz.1, hsw⟩, hwz⟩
  · rintro (rfl | ⟨h1', h2⟩)
    · exact ⟨anc_refl hxz.1, hxz⟩
    · exact ⟨anc_trans hxy' h1', h2⟩

/-- ✱121·41. \(\vdash :R\in \text{Cls}\rightarrow 1.R(z\vdash\dashv z)\in \text{Cls induct}.\supset .R(x\vdash\dashv z)\in \text{Cls induct}\) -/
theorem pm121_41 {α : Type*} {R : α → α → Prop} {x z : α} :
    R ∈ arrow Cls one ∧ itvCC R z z ∈ ClsInduct → itvCC R x z ∈ ClsInduct := by
  rintro ⟨hR, hz⟩
  by_cases hxz : anc R x z
  · have h := (anc_iff_reflTransGen.1 hxz).2
    clear hxz
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact hz
    | @head a b hab hbz ih =>
      rw [pm121_4 ⟨⟨hR, hab⟩, anc_iff_reflTransGen.2 ⟨⟨a, Or.inr hab⟩, hbz⟩⟩]
      rw [mem_ClsInduct] at ih ⊢
      rw [unitCls_eq_singleton]
      exact (Set.finite_singleton a).union ih
  · have : itvCC R x z = ∅ := by
      by_contra h
      exact hxz (pm121_23.2.2 (Set.nonempty_iff_ne_empty.2 h)).1.2
    rw [this, mem_ClsInduct]; exact Set.finite_empty

/-- ✱121·42. \(\vdash :R\in \text{Cls}\rightarrow 1.{\sim}(zR_{\text{po}}z).\supset .R(x\vdash\dashv z)\in \text{Cls induct}\) -/
theorem pm121_42 {α : Type*} {R : α → α → Prop} {x z : α} :
    R ∈ arrow Cls one ∧ ¬ po R z z → itvCC R x z ∈ ClsInduct := by
  rintro ⟨hR, hz⟩
  refine pm121_41 ⟨hR, mem_ClsInduct.2 ?_⟩
  by_cases hf : z ∈ fld R
  · rw [itvCC_self hz hf]; exact Set.finite_singleton z
  · refine Set.Finite.subset Set.finite_empty fun w hw => hf hw.1.1

private theorem rtg_dres {α : Type*} {A : Set α} {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen (A ◁ R) a b) : Relation.ReflTransGen R a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail hbc.2

/-- A cycle of a many-one relation through `z` is the orbit `z, f z, …, f^{n-1} z` of `z` under
the function `f` that `R` is on it, with `n` the minimal period. -/
private theorem cycle_orbit {α : Type*} {R : α → α → Prop} (hR : R ∈ arrow Cls one) {z : α}
    (hz : Relation.TransGen R z z) :
    ∃ (f : α → α) (n : ℕ), 0 < n ∧ f^[n] z = z ∧ (∀ i, R (f^[i] z) (f^[i + 1] z)) ∧
      (∀ w, Relation.ReflTransGen R z w ↔ ∃ i < n, f^[i] z = w) ∧
      (∀ i j, i < n → j < n → f^[i] z = f^[j] z → i = j) ∧
      (∀ i, f^[i] z = z → n ∣ i) := by
  classical
  have h1 := mem_arrow_Cls_one.1 hR
  have : Nonempty α := ⟨z⟩
  let f : α → α := fun w => Classical.epsilon (fun y => R w y)
  have hf : ∀ w y, R w y → f w = y := fun w y h =>
    h1 w _ y ⟨Classical.epsilon_spec (p := fun y => R w y) ⟨y, h⟩, h⟩
  have hit : ∀ w, Relation.ReflTransGen R z w → ∃ k, f^[k] z = w := by
    intro w h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, by rw [Function.iterate_succ_apply', hk, hf _ _ hbc]⟩
  have hRf : ∀ w, Relation.ReflTransGen R z w → R w (f w) := by
    intro w hw
    obtain ⟨y, hy⟩ : ∃ y, R w y := by
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 (rtg_back_of_cycle hR hz hw) with h | h
      · obtain ⟨y, hy, -⟩ := Relation.TransGen.head'_iff.1 hz
        exact ⟨y, h ▸ hy⟩
      · obtain ⟨y, hy, -⟩ := Relation.TransGen.head'_iff.1 h
        exact ⟨y, hy⟩
    rw [hf w y hy]
    exact hy
  have hdesc : ∀ i, Relation.ReflTransGen R z (f^[i] z) := by
    intro i
    induction i with
    | zero => exact Relation.ReflTransGen.refl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact ih.tail (hRf _ ih)
  have hstep : ∀ i, R (f^[i] z) (f^[i + 1] z) := fun i => by
    rw [Function.iterate_succ_apply']
    exact hRf _ (hdesc i)
  have hex : ∃ n, 0 < n ∧ f^[n] z = z := by
    obtain ⟨w, hzw, hwz⟩ := Relation.TransGen.tail'_iff.1 hz
    obtain ⟨k, hk⟩ := hit w hzw
    exact ⟨k + 1, Nat.succ_pos k, by rw [Function.iterate_succ_apply', hk, hf _ _ hwz]⟩
  obtain ⟨hn, hper⟩ := Nat.find_spec hex
  have hmin : ∀ m, 0 < m → m < Nat.find hex → f^[m] z ≠ z :=
    fun m hm hlt h => Nat.find_min hex hlt ⟨hm, h⟩
  have hmod : ∀ k, f^[k] z = f^[k % Nat.find hex] z := fun k => by
    conv_lhs => rw [← Nat.mod_add_div k (Nat.find hex)]
    rw [Function.iterate_add_apply, Function.iterate_mul, Function.iterate_fixed hper]
  refine ⟨f, Nat.find hex, hn, hper, hstep, fun w => ⟨fun hw => ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := hit w hw
    exact ⟨k % Nat.find hex, Nat.mod_lt _ hn, (hmod k).symm⟩
  · rintro ⟨i, -, rfl⟩
    exact hdesc i
  · have key : ∀ i j, i < j → j < Nat.find hex → f^[i] z = f^[j] z → False := by
      intro i j hij hj h
      apply hmin (Nat.find hex - j + i) (by omega) (by omega)
      rw [Function.iterate_add_apply, h, ← Function.iterate_add_apply, Nat.sub_add_cancel hj.le,
        hper]
    intro i j hi hj h
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · exact (key i j hij hj h).elim
    · exact hij
    · exact (key j i hij hi h.symm).elim
  · intro i h
    apply Nat.dvd_of_mod_eq_zero
    by_contra h0
    exact hmin _ (Nat.pos_of_ne_zero h0) (Nat.mod_lt _ hn) ((hmod i).symm.trans h)

/-- On a cycle of a many-one relation the predecessor of `z` that descends from `z` is
`f^{n-1} z`. -/
private theorem cycle_pred {α : Type*} {R : α → α → Prop} (hR : R ∈ arrow Cls one) {z : α}
    {f : α → α} {n : ℕ} (hn : 0 < n) (hper : f^[n] z = z) (hstep : ∀ i, R (f^[i] z) (f^[i + 1] z))
    (horb : ∀ w, Relation.ReflTransGen R z w ↔ ∃ i < n, f^[i] z = w)
    (hdvd : ∀ i, f^[i] z = z → n ∣ i) :
    refs R z ∩ rels (anc R) z = ι (f^[n - 1] z) := by
  have h1 := mem_arrow_Cls_one.1 hR
  have hzf : z ∈ fld R := ⟨_, Or.inl (hstep 0)⟩
  ext w
  simp only [Set.mem_inter_iff, mem_unitCls]
  constructor
  · rintro ⟨hwz, hzw⟩
    obtain ⟨i, hi, rfl⟩ := (horb _).1 (anc_iff_reflTransGen.1 hzw).2
    have h' : f^[i + 1] z = z := h1 _ _ _ ⟨hstep i, hwz⟩
    have := Nat.le_of_dvd (Nat.succ_pos i) (hdvd _ h')
    rw [show i = n - 1 by omega]
  · rintro rfl
    refine ⟨?_, anc_iff_reflTransGen.2 ⟨hzf, (horb _).2 ⟨n - 1, by omega, rfl⟩⟩⟩
    have := hstep (n - 1)
    rwa [Nat.sub_add_cancel hn, hper] at this

/-- ✱121·43. \(\vdash :R\in \text{Cls}\rightarrow 1.zR_{\text{po}}z.\supset .\text{E}!\breve{\iota} ʻ(\overrightarrow{R}ʻz\cap \overleftarrow{R}_{*}ʻz)\)

`E!ῐ'(R⃗'z ∩ R⃖_*'z)` is `EDesc iota˘ (refs R z ∩ rels (anc R) z)`: the class is a unit class. -/
theorem pm121_43 {α : Type*} {R : α → α → Prop} {z : α} :
    (R ∈ arrow Cls one ∧ po R z z) → EDesc iota˘ (refs R z ∩ rels (anc R) z) := by
  rintro ⟨hR, hz⟩
  obtain ⟨f, n, hn, hper, hstep, horb, -, hdvd⟩ := cycle_orbit hR (po_iff_transGen.1 hz)
  have key := cycle_pred hR hn hper hstep horb hdvd
  exact ⟨f^[n - 1] z, fun x => ⟨fun h => unitCls_injective ((h : _ = ι x).symm.trans key),
    fun h => by rw [h]; exact key⟩⟩

/-- ✱121·431. \[\begin{align}\vdash :R\in \text{Cls}\rightarrow 1.zR_{\text{po}}z.a=\breve{\iota} ʻ(\overrightarrow{R}ʻz\cap \overleftarrow{R}_{*}ʻz).&\alpha =\overleftarrow{R}_{*}ʻz-\iota ʻa.\\ &S=\alpha \upharpoonleft R.\supset .{\sim}(aS_{\text{po}}a)\end{align}\]

The hypothesis is a product of five, bracketed to the left; `a = ῐ'(…)` is a description. -/
theorem pm121_431 {α : Type*} {R : α → α → Prop} {z a : α} {A : Set α} {S : α → α → Prop} :
    ((((R ∈ arrow Cls one ∧ po R z z) ∧
        Desc iota˘ (refs R z ∩ rels (anc R) z) (fun b => a = b)) ∧
      A = rels (anc R) z \ ι a) ∧ S = A ◁ R) → ¬ po S a a := by
  rintro ⟨⟨-, rfl⟩, rfl⟩ h
  obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 (po_iff_transGen.1 h)
  exact hc.1.2 rfl

/-- ✱121·432. \(\vdash :\text{Hp}*121·431.\supset .S(z\vdash\dashv a)\in \text{Cls induct}\)

`Hp ✱121·431` is the hypothesis of ✱121·431. -/
theorem pm121_432 {α : Type*} {R : α → α → Prop} {z a : α} {A : Set α} {S : α → α → Prop} :
    ((((R ∈ arrow Cls one ∧ po R z z) ∧
        Desc iota˘ (refs R z ∩ rels (anc R) z) (fun b => a = b)) ∧
      A = rels (anc R) z \ ι a) ∧ S = A ◁ R) → itvCC S z a ∈ ClsInduct := by
  rintro ⟨⟨⟨⟨hR, hz⟩, -⟩, rfl⟩, rfl⟩
  rw [mem_ClsInduct]
  obtain ⟨f, n, -, -, -, horb, -, -⟩ := cycle_orbit hR (po_iff_transGen.1 hz)
  refine ((Set.finite_lt_nat n).image (fun k => f^[k] z)).subset ?_
  intro w hw
  have h1 : Relation.ReflTransGen R z w :=
    rtg_dres (anc_iff_reflTransGen.1 hw.1).2
  obtain ⟨i, hi, rfl⟩ := (horb w).1 h1
  exact ⟨i, hi, rfl⟩

/-- ✱121·433. \(\vdash :\text{Hp}*121·431.z\neq a.\supset .S(z\vdash\dashv a)=\overleftarrow{R}_{*}ʻz=R(z\vdash\dashv z)\) -/
theorem pm121_433 {α : Type*} {R : α → α → Prop} {z a : α} {A : Set α} {S : α → α → Prop} :
    (((((R ∈ arrow Cls one ∧ po R z z) ∧
        Desc iota˘ (refs R z ∩ rels (anc R) z) (fun b => a = b)) ∧
      A = rels (anc R) z \ ι a) ∧ S = A ◁ R) ∧ z ≠ a) →
        (itvCC S z a = rels (anc R) z ∧ rels (anc R) z = itvCC R z z) := by
  rintro ⟨⟨⟨⟨⟨hR, hz⟩, hD⟩, rfl⟩, rfl⟩, hza⟩
  refine ⟨?_, (pm121_38 ⟨hR, hz⟩).symm⟩
  obtain ⟨f, n, hn, hper, hstep, horb, hinj, hdvd⟩ := cycle_orbit hR (po_iff_transGen.1 hz)
  have hpred := cycle_pred hR hn hper hstep horb hdvd
  obtain ⟨b, hb, hab⟩ := hD
  have ha : a = f^[n - 1] z := by
    rw [hab]
    exact unitCls_injective (((hb b).2 rfl : _ = ι b).symm.trans hpred)
  subst ha
  have hn2 : 2 ≤ n := by
    by_contra h
    apply hza
    rw [show n - 1 = 0 by omega]
    rfl
  have hzf : z ∈ fld R := ⟨_, Or.inl (hstep 0)⟩
  have hA : ∀ j, j < n - 1 → f^[j] z ∈ rels (anc R) z \ ι (f^[n - 1] z) := fun j hj =>
    ⟨anc_iff_reflTransGen.2 ⟨hzf, (horb _).2 ⟨j, by omega, rfl⟩⟩,
      fun h => absurd (hinj j (n - 1) (by omega) (by omega) h) (by omega)⟩
  have hS : ∀ j, j < n - 1 →
      ((rels (anc R) z \ ι (f^[n - 1] z)) ◁ R) (f^[j] z) (f^[j + 1] z) :=
    fun j hj => ⟨hA j hj, hstep j⟩
  have hpath : ∀ i j, i ≤ j → j ≤ n - 1 →
      Relation.ReflTransGen ((rels (anc R) z \ ι (f^[n - 1] z)) ◁ R) (f^[i] z) (f^[j] z) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact Relation.ReflTransGen.refl
    | succ j _ ih => intro hj; exact (ih (by omega)).tail (hS j (by omega))
  have hfldS : ∀ i, i ≤ n - 1 → f^[i] z ∈ fld ((rels (anc R) z \ ι (f^[n - 1] z)) ◁ R) := by
    intro i hi
    rcases Nat.lt_or_ge i (n - 1) with h | h
    · exact ⟨_, Or.inl (hS i h)⟩
    · have e : n - 2 + 1 = i := by omega
      have := hS (n - 2) (by omega)
      rw [e] at this
      exact ⟨_, Or.inr this⟩
  ext w
  constructor
  · rintro ⟨hzw, -⟩
    exact anc_iff_reflTransGen.2 ⟨hzf,
      rtg_dres (anc_iff_reflTransGen.1 hzw).2⟩
  · intro hw
    obtain ⟨i, hi, rfl⟩ := (horb _).1 (anc_iff_reflTransGen.1 hw).2
    exact ⟨anc_iff_reflTransGen.2 ⟨hfldS 0 (by omega), hpath 0 i (Nat.zero_le _) (by omega)⟩,
      anc_iff_reflTransGen.2 ⟨hfldS i (by omega), hpath i (n - 1) (by omega) le_rfl⟩⟩

/-- ✱121·434. \(\vdash :\text{Hp}*121·431.z=a.\supset .\overleftarrow{R}_{*}ʻz=R(z\vdash\dashv z)=\iota ʻz\) -/
theorem pm121_434 {α : Type*} {R : α → α → Prop} {z a : α} {A : Set α} {S : α → α → Prop} :
    (((((R ∈ arrow Cls one ∧ po R z z) ∧
        Desc iota˘ (refs R z ∩ rels (anc R) z) (fun b => a = b)) ∧
      A = rels (anc R) z \ ι a) ∧ S = A ◁ R) ∧ z = a) →
        (rels (anc R) z = itvCC R z z ∧ itvCC R z z = ι z) := by
  rintro ⟨⟨⟨⟨⟨hR, hz⟩, ⟨b, hb, hab⟩⟩, -⟩, -⟩, hza⟩
  refine ⟨(pm121_38 ⟨hR, hz⟩).symm, ?_⟩
  have hT : refs R z ∩ rels (anc R) z = ι z := by
    have h : refs R z ∩ rels (anc R) z = ι b := (hb b).2 rfl
    rw [← hab, ← hza] at h
    exact h
  have hmem : z ∈ refs R z ∩ rels (anc R) z := by
    rw [hT]
    exact mem_unitCls.2 rfl
  have hzz : R z z := hmem.1
  have h1 := mem_arrow_Cls_one.1 hR
  rw [pm121_38 ⟨hR, hz⟩]
  ext w
  rw [mem_unitCls]
  constructor
  · intro hw
    have h := (anc_iff_reflTransGen.1 hw).2
    clear hw
    induction h with
    | refl => rfl
    | tail _ hbc ih =>
      rw [ih] at hbc
      exact (h1 _ _ _ ⟨hzz, hbc⟩).symm
  · intro h
    rw [h]
    exact anc_refl ⟨z, Or.inl hzz⟩

/-- The posterity of a term of a cycle of a many-one relation is finite: it is the orbit of the
term under the (partial) function `R`, which is periodic. -/
private theorem orbit_finite_of_cycle {α : Type*} {R : α → α → Prop} (hR : R ∈ arrow Cls one)
    {z : α} (hz : Relation.TransGen R z z) : {w | Relation.ReflTransGen R z w}.Finite := by
  classical
  have h1 := mem_arrow_Cls_one.1 hR
  have : Nonempty α := ⟨z⟩
  let f : α → α := fun w => Classical.epsilon (fun y => R w y)
  have hf : ∀ w y, R w y → f w = y := fun w y h =>
    h1 w _ y ⟨Classical.epsilon_spec (p := fun y => R w y) ⟨y, h⟩, h⟩
  have hit : ∀ w, Relation.ReflTransGen R z w → ∃ k, f^[k] z = w := by
    intro w h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, by rw [Function.iterate_succ_apply', hk, hf _ _ hbc]⟩
  obtain ⟨n, hn, hper⟩ : ∃ n, 0 < n ∧ f^[n] z = z := by
    obtain ⟨w, hzw, hwz⟩ := Relation.TransGen.tail'_iff.1 hz
    obtain ⟨k, hk⟩ := hit w hzw
    exact ⟨k + 1, Nat.succ_pos k, by rw [Function.iterate_succ_apply', hk, hf _ _ hwz]⟩
  have hmod : ∀ k, f^[k] z = f^[k % n] z := fun k => by
    conv_lhs => rw [← Nat.mod_add_div k n]
    rw [Function.iterate_add_apply, Function.iterate_mul, Function.iterate_fixed hper]
  refine ((Set.finite_lt_nat n).image (fun k => f^[k] z)).subset ?_
  intro w hw
  obtain ⟨k, rfl⟩ := hit w hw
  exact ⟨k % n, Nat.mod_lt _ hn, (hmod k).symm⟩

/-- ✱121·44. \(\vdash :R\in \text{Cls}\rightarrow 1.zR_{\text{po}}z.\supset .R(z\vdash\dashv z)\in \text{Cls induct}\) -/
theorem pm121_44 {α : Type*} {R : α → α → Prop} {z : α} :
    (R ∈ arrow Cls one ∧ po R z z) → itvCC R z z ∈ ClsInduct := by
  rintro ⟨hR, hz⟩
  rw [pm121_38 ⟨hR, hz⟩, mem_ClsInduct]
  exact (orbit_finite_of_cycle hR (po_iff_transGen.1 hz)).subset
    fun w (hw : anc R z w) => (anc_iff_reflTransGen.1 hw).2

/-- ✱121·441. \(\vdash :R\in \text{Cls}\rightarrow 1.zR_{\text{po}}z.\supset .R(x\vdash\dashv z)\in \text{Cls induct} \quad[*121·44·41]\) -/
theorem pm121_441 {α : Type*} {R : α → α → Prop} {x z : α} :
    (R ∈ arrow Cls one ∧ po R z z) → itvCC R x z ∈ ClsInduct :=
  fun h => pm121_41 ⟨h.1, pm121_44 h⟩

/-- ✱121·45. \(\vdash :R\in \text{Cls}\rightarrow 1.\supset .R(x\vdash\dashv z)\in \text{Cls induct} \quad[*121·42·441]\) -/
theorem pm121_45 {α : Type*} {R : α → α → Prop} {x z : α} :
    R ∈ arrow Cls one → itvCC R x z ∈ ClsInduct := by
  intro hR
  by_cases hz : po R z z
  · exact pm121_441 ⟨hR, hz⟩
  · exact pm121_42 ⟨hR, hz⟩

/-- ✱121·46. \(\vdash :R\in 1\rightarrow \text{Cls}.\supset .R(x\vdash\dashv z)\in \text{Cls induct} \quad[*121·45·143]\) -/
theorem pm121_46 {α : Type*} {R : α → α → Prop} {x z : α} :
    R ∈ arrow one Cls → itvCC R x z ∈ ClsInduct := by
  intro hR
  rw [pm121_143]
  exact pm121_45 ((arrow_cnv (P := R˘)).2 hR)

/-- ✱121·47. \(\vdash :R\in (\text{Cls}\rightarrow 1)\cup (1\rightarrow \text{Cls}).\supset .R(x\vdash\dashv z)\in \text{Cls induct} \quad[*121·45·46]\) -/
theorem pm121_47 {α : Type*} {R : α → α → Prop} {x z : α} :
    R ∈ arrow Cls one ∪ arrow one Cls → itvCC R x z ∈ ClsInduct := by
  rintro (hR | hR)
  · exact pm121_45 hR
  · exact pm121_46 hR

/-- ✱121·48. \[\begin{align}\vdash \colon\ldotp &R\in \text{Cls}\rightarrow 1.\supset :\\ &\text{Nc}ʻR(x\vdash\dashv y)<\text{Nc}ʻR(x\vdash\dashv z).\equiv .\exists !R(x\vdash\dashv z)-R(x\vdash\dashv y)\end{align}\]

The sides of `<` are `N₀c'R(x⊢⊣y)`, `N₀c'R(x⊢⊣z)` (normal adjustment). -/
theorem pm121_48 {α : Type*} {R : α → α → Prop} {x y z : α} :
    R ∈ arrow Cls one →
      (n₀c (itvCC R x y) <ᶜ n₀c (itvCC R x z) ↔ (itvCC R x z \ itvCC R x y).Nonempty) := by
  intro hR
  have hfin' : (itvCC R x z).Finite := mem_ClsInduct.1 (pm121_45 hR)
  show n₀c (itvCC R x z) >ᶜ n₀c (itvCC R x y) ↔ _
  rw [cardGt_n₀c]
  constructor
  · rintro ⟨-, hn⟩
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h
    exact hn ⟨⟨Set.inclusion h, Set.inclusion_injective h⟩⟩
  · rintro ⟨w, hwz, hwy⟩
    have hsub : itvCC R x y ⊆ itvCC R x z := by
      rcases pm121_39 (x := x) (y := y) (z := z) hR with h | h
      · exact h
      · exact absurd (h hwz) hwy
    refine ⟨⟨⟨Set.inclusion hsub, Set.inclusion_injective hsub⟩⟩, ?_⟩
    rintro ⟨g⟩
    have hss : itvCC R x y ⊂ itvCC R x z :=
      Set.ssubset_iff_subset_ne.2 ⟨hsub, fun e => hwy (e.symm ▸ hwz)⟩
    have h1 := Set.ncard_lt_ncard hss hfin'
    have : Finite ↥(itvCC R x y) := (hfin'.subset hsub).to_subtype
    have h2 := Nat.card_le_card_of_injective g g.injective
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h2
    omega

/-- ✱121·481. \[\begin{align}\vdash \colon\ldotp R\in \text{Cls}\rightarrow 1.\supset :\text{Nc}ʻR(x\vdash\dashv y)\leq \text{Nc}ʻ&R(x\vdash\dashv z).\equiv .\\ &R(x\vdash\dashv y)\subset R(x\vdash\dashv z)\end{align}\]

The sides of `≤` are `N₀c'R(x⊢⊣y)`, `N₀c'R(x⊢⊣z)` (normal adjustment). -/
theorem pm121_481 {α : Type*} {R : α → α → Prop} {x y z : α} :
    R ∈ arrow Cls one → (n₀c (itvCC R x y) ≤ᶜ n₀c (itvCC R x z) ↔ itvCC R x y ⊆ itvCC R x z) := by
  intro hR
  have hfin : (itvCC R x y).Finite := mem_ClsInduct.1 (pm121_45 hR)
  show n₀c (itvCC R x z) ≥ᶜ n₀c (itvCC R x y) ↔ _
  rw [cardGe_n₀c]
  constructor
  · rintro ⟨g⟩
    rcases pm121_39 (x := x) (y := y) (z := z) hR with h | h
    · exact h
    · by_contra hn
      have hss : itvCC R x z ⊂ itvCC R x y :=
        Set.ssubset_iff_subset_ne.2 ⟨h, fun e => hn e.symm.subset⟩
      have h1 := Set.ncard_lt_ncard hss hfin
      have : Finite ↥(itvCC R x z) := (hfin.subset h).to_subtype
      have h2 := Nat.card_le_card_of_injective g g.injective
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h2
      omega
  · intro h; exact ⟨⟨Set.inclusion h, Set.inclusion_injective h⟩⟩

section C121late

open Classical

/-! ### Helpers for ✱121·5–·72 -/

private theorem desc_of_eq {α β : Type*} {R : α → β → Prop} {y : β} {x : α}
    (h : Desc R y (fun v => x = v)) {ψ : α → Prop} : Desc R y ψ ↔ ψ x := by
  obtain ⟨b, hb, rfl⟩ := h
  exact TheIs_iff_of_unique hb

private theorem desc_unique {α β : Type*} {R : α → β → Prop} {y : β} {b : α}
    (h : ∀ x, R x y ↔ x = b) {ψ : α → Prop} : Desc R y ψ ↔ ψ b :=
  TheIs_iff_of_unique h

private theorem edesc_iff_desc {α β : Type*} {R : α → β → Prop} {y : β} :
    EDesc R y ↔ Desc R y (fun _ => True) := by
  rw [Desc, TheIs_iff]
  exact ⟨fun h => ⟨h, fun _ _ => trivial⟩, fun h => h.1⟩

private theorem desc_congr {α β : Type*} {R : α → β → Prop} {y : β} {φ ψ : α → Prop}
    (h : ∀ x, φ x ↔ ψ x) : Desc R y φ ↔ Desc R y ψ :=
  exists_congr fun _ => and_congr Iff.rfl (h _)

/-- `ψ(ν_P)`: `B'P` exists, and `P_{ν −_c 1}` relates it to exactly one term, which is `ψ`. -/
private theorem desc_nuP_iff {α β : Type*} {P : α → α → Prop} {μ : Set (Set β)}
    {ψ : α → Prop} :
    Desc (nuP μ) P ψ ↔ ∃ b, (∀ x, Beg x P ↔ x = b) ∧
      ∃ v, (∀ u, Pnu P (μ -ᶜ (one : Set (Set β)) : Set (Set β)) b u ↔ u = v) ∧ ψ v := by
  rw [desc_nuP, desc2_iff]
  exact Iff.rfl

private theorem pwr_succ_eq {α : Type*} {P : α → α → Prop} {k : ℕ} :
    pwr P (k + 1) = pwr P k ⨾ P := rfl

private theorem pwr_zero_eq {α : Type*} {P : α → α → Prop} : pwr P 0 = I ↾ fld P := by
  funext x y
  apply propext
  show (x = y ∧ x ∈ fld P) ↔ (I x y ∧ y ∈ fld P)
  rw [I_apply]
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩

private theorem pwr_one_eq {α : Type*} {P : α → α → Prop} : pwr P 1 = P := by
  funext x y
  exact propext pwr_one

private theorem rts_iff {α : Type*} {P S T : α → α → Prop} :
    Rts P S T ↔ ∃ k, S = (fun X => X ⨾ P)^[k] T := by
  show anc (relProdR P) S T ↔ _
  rw [anc_iff_reflTransGen]
  constructor
  · rintro ⟨-, h⟩
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | head hac _ ih =>
      obtain ⟨k, hk⟩ := ih
      rw [relProdR_apply] at hac
      exact ⟨k + 1, by rw [Function.iterate_succ_apply', ← hk, hac]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨⟨_, Or.inr rfl⟩, ?_⟩
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Relation.ReflTransGen.head rfl ih

private theorem iter_pwr {α : Type*} {P : α → α → Prop} (j : ℕ) :
    ∀ k : ℕ, (fun X => X ⨾ P)^[k] (pwr P j) = pwr P (j + k)
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply', iter_pwr j k]; rfl

/-- `Potid'P` is the class of the powers `P^k` (`k ≥ 0`, `P⁰ = I ↾ C'P`). -/
private theorem mem_potid_iff {α : Type*} {P S : α → α → Prop} :
    S ∈ potid P ↔ ∃ k, S = pwr P k := by
  show Rts P S (I ↾ fld P) ↔ _
  rw [rts_iff, ← pwr_zero_eq]
  simp only [iter_pwr, Nat.zero_add]

/-- `Pot'P` is the class of the powers `P^k` (`k ≥ 1`). -/
private theorem mem_pot_iff' {α : Type*} {P S : α → α → Prop} :
    S ∈ pot P ↔ ∃ k, S = pwr P (k + 1) := by
  show Rts P S P ↔ _
  have key : ∀ k, (fun X => X ⨾ P)^[k] P = pwr P (k + 1) := fun k => by
    rw [Nat.add_comm, ← iter_pwr 1 k, pwr_one_eq]
  rw [rts_iff]
  simp only [key]

private theorem pwr_left_fld {α : Type*} {P : α → α → Prop} {k : ℕ} {x y : α}
    (h : pwr P k x y) : x ∈ fld P := fld_of_anc_left (pwr_anc h)

/-- A member of a generation of `P` is reached from a beginning of `P` by some power of `P`. -/
private theorem gen_beg {α : Type*} {P : α → α → Prop} {x : α} (hx : x ∈ sumCls (gen P)) :
    ∃ a k, Beg a P ∧ pwr P k a x := by
  obtain ⟨A, ⟨C, ⟨S, hS, hCS⟩, hAC⟩, hxA⟩ := hx
  obtain ⟨k, rfl⟩ := mem_potid_iff.1 hS
  have hC : C = codom (pwr P k) := hCS
  have hA : A = refs (minP P) C := hAC
  subst hC hA
  obtain ⟨⟨⟨a, hax⟩, -⟩, hmin⟩ := (minP_apply _ _ _).1 hxA
  refine ⟨a, k, ⟨?_, fun ⟨a', ha'⟩ => ?_⟩, hax⟩
  · obtain ⟨y, hy | hy⟩ := pwr_left_fld hax
    · exact ⟨y, hy⟩
    · obtain ⟨w, hw, hwx⟩ := pwr_succ.1 (pwr_succ'.2 ⟨a, hy, hax⟩)
      exact (hmin ⟨w, ⟨y, hw⟩, hwx⟩).elim
  · obtain ⟨w, hw, hwx⟩ := pwr_succ.1 (pwr_succ'.2 ⟨a, ha', hax⟩)
    exact hmin ⟨w, ⟨a', hw⟩, hwx⟩

/-- `x P_{ν −_c 1} y` unfolded: `ν = N₀c'ξ` for an existent `ξ` with `P(x⊢⊣y) sm ξ`. -/
private theorem Pnu_sub_one {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} {x y : α} :
    Pnu P (ν -ᶜ (one : Set (Set β)) : Set (Set β)) x y ↔
      ∃ X : Set β, X.Nonempty ∧ ν = n₀c X ∧ Nonempty (↥(itvCC P x y) ≃ ↥X) := by
  rw [Pnu_iff]
  constructor
  · rintro ⟨⟨b⟩, B, hB, ⟨e⟩⟩
    have hBm : B ∈ (ν -ᶜ (one : Set (Set β)) : Set (Set β)) := hB ▸ self_mem_n₀c B
    obtain ⟨hBν, X, hX⟩ := hBm
    obtain ⟨B', O, ⟨hB', hO⟩, ⟨f⟩⟩ := mem_cardAdd'.1 hX
    obtain ⟨u⟩ := unit_of_mem_one (hO ▸ self_mem_n₀c O)
    obtain ⟨g⟩ := eq_n₀c_iff_equiv.1 hB'
    refine ⟨X, ⟨_, (f.symm (Sum.inr (u.symm PUnit.unit))).2⟩, ?_,
      ⟨e.trans ((g.sumCongr u.symm).trans f.symm)⟩⟩
    rw [← hBν]
    rw [one_eq_n₀c_singleton b, cardAdd_n₀c] at hX ⊢
    exact ncT_eq_n₀c_of_mem hX
  · rintro ⟨X, ⟨x0, hx0⟩, rfl, ⟨e⟩⟩
    refine ⟨⟨x0⟩, X \ {x0}, ?_, ⟨e.trans (equiv_diff_singleton hx0)⟩⟩
    rw [sub_one_eq (equiv_diff_singleton hx0), n₀c_eq_ncT]

/-- For `ν ≠ 0` in the type of `C'P`: `x P_{ν −_c 1} y . ≡ . N₀c'P(x⊢⊣y) = ν`. -/
private theorem Pnu_sub_one_iff_eq {α : Type*} {P : α → α → Prop} {ν : Set (Set α)} {x y : α}
    (hν : ν ≠ zero) :
    Pnu P (ν -ᶜ (one : Set (Set α)) : Set (Set α)) x y ↔ n₀c (itvCC P x y) = ν := by
  rw [Pnu_sub_one]
  constructor
  · rintro ⟨X, -, rfl, e⟩
    exact eq_n₀c_iff_equiv.2 e
  · intro h
    refine ⟨itvCC P x y, ?_, h.symm, ⟨Equiv.refl _⟩⟩
    rw [Set.nonempty_iff_ne_empty]
    intro he
    rw [he, ← zero_eq_n₀c_empty] at h
    exact hν h.symm

private theorem pwr_card' {α : Type*} {P : α → α → Prop}
    (hP : P ∈ arrow one Cls ∪ arrow Cls one) (hJ : po P ⪽ J) {k : ℕ} {x y : α}
    (h : pwr P k x y) : (itvCC P x y).Finite ∧ (itvCC P x y).ncard = k + 1 := by
  rcases hP with hP | hP
  · exact pwr_card hP hJ h
  · have := pwr_card (arrow_cnv.1 hP) (J_cnv hJ) (pwr_cnv.2 h)
    rwa [← pm121_143] at this

private theorem pwr_many_one {α : Type*} {P : α → α → Prop} (hP : P ∈ arrow Cls one)
    {k : ℕ} {x y z : α} (h1 : pwr P k x y) (h2 : pwr P k x z) : y = z :=
  pwr_one_many (arrow_cnv.1 hP) (pwr_cnv.2 h1) (pwr_cnv.2 h2)

/-- `P(x⊢⊣y)` is similar to an existent finite `X` iff `x P^k y` where `X` has `k + 1` terms. -/
private theorem itv_equiv_iff {α : Type*} {P : α → α → Prop}
    (hP : P ∈ arrow one Cls ∪ arrow Cls one) (hJ : po P ⪽ J) {x y : α} {X : Type*} [Finite X]
    [Nonempty X] : Nonempty (↥(itvCC P x y) ≃ X) ↔ ∃ k, Nat.card X = k + 1 ∧ pwr P k x y := by
  constructor
  · rintro ⟨e⟩
    have hw := (e.symm (Classical.arbitrary X)).2
    obtain ⟨k, hk⟩ := anc_pwr (anc_trans hw.1 hw.2)
    obtain ⟨-, hc⟩ := pwr_card' hP hJ hk
    refine ⟨k, ?_, hk⟩
    rw [← Nat.card_congr e, Nat.card_coe_set_eq, hc]
  · rintro ⟨k, hk, h⟩
    obtain ⟨hf, hc⟩ := pwr_card' hP hJ h
    have : Finite ↥(itvCC P x y) := hf.to_subtype
    apply Finite.card_eq.1
    rw [Nat.card_coe_set_eq, hc, hk]

/-- For a finite `A` of `k + 1` terms: `x P_{N₀c'A −_c 1} y . ≡ . x P^k y`. -/
private theorem Pnu_sub_one_n₀c {α β : Type*} {P : α → α → Prop}
    (hP : P ∈ arrow one Cls ∪ arrow Cls one) (hJ : po P ⪽ J) {A : Set β} (hA : A.Finite)
    {k : ℕ} (hk : Nat.card A = k + 1) {x y : α} :
    Pnu P (n₀c A -ᶜ (one : Set (Set β)) : Set (Set β)) x y ↔ pwr P k x y := by
  have : Finite ↥A := hA.to_subtype
  have : Nonempty ↥A := by
    have h0 : 0 < Nat.card ↥A := by omega
    exact (Nat.card_pos_iff.1 h0).1
  rw [Pnu_sub_one]
  constructor
  · rintro ⟨X, -, hAX, ⟨e⟩⟩
    obtain ⟨g⟩ := eq_n₀c_iff_equiv.1 hAX
    obtain ⟨j, hj, h⟩ := (itv_equiv_iff hP hJ (X := ↥A)).1 ⟨e.trans g.symm⟩
    rwa [show k = j by omega]
  · intro h
    obtain ⟨e⟩ := (itv_equiv_iff hP hJ (X := ↥A)).2 ⟨k, hk, h⟩
    exact ⟨A, ⟨_, (Classical.arbitrary ↥A).2⟩, rfl, ⟨e⟩⟩

/-- `P_{ν −_c 1}` relates `x` to at most one term (`P` many-one without cycles). -/
private theorem Pnu_sub_one_unique {α γ : Type*} {P : α → α → Prop} (hP : P ∈ arrow Cls one)
    (hJ : po P ⪽ J) {μ : Set (Set γ)} {x u u' : α}
    (h1 : Pnu P (μ -ᶜ (one : Set (Set γ)) : Set (Set γ)) x u)
    (h2 : Pnu P (μ -ᶜ (one : Set (Set γ)) : Set (Set γ)) x u') : u = u' := by
  obtain ⟨X, hX, hμX, ⟨e⟩⟩ := Pnu_sub_one.1 h1
  have hf : (itvCC P x u).Finite := mem_ClsInduct.1 (pm121_45 hP)
  have : Finite ↥(itvCC P x u) := hf.to_subtype
  have : Finite ↥X := Finite.of_equiv _ e
  have : Nonempty ↥X := hX.to_subtype
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥X = k + 1 := Nat.exists_eq_succ_of_ne_zero Nat.card_pos.ne'
  subst hμX
  rw [Pnu_sub_one_n₀c (Or.inr hP) hJ (Set.toFinite X) hk] at h1 h2
  exact pwr_many_one hP h1 h2

/-- `ψ(ν_P)` for `P` many-one without cycles. -/
private theorem desc_nuP_iff_mo {α γ : Type*} {P : α → α → Prop} (hP : P ∈ arrow Cls one)
    (hJ : po P ⪽ J) {μ : Set (Set γ)} {ψ : α → Prop} :
    Desc (nuP μ) P ψ ↔ ∃ b, (∀ x, Beg x P ↔ x = b) ∧
      ∃ v, Pnu P (μ -ᶜ (one : Set (Set γ)) : Set (Set γ)) b v ∧ ψ v := by
  rw [desc_nuP_iff]
  constructor
  · rintro ⟨b, hb, v, hv, hψ⟩
    exact ⟨b, hb, v, (hv v).2 rfl, hψ⟩
  · rintro ⟨b, hb, v, hv, hψ⟩
    exact ⟨b, hb, v, fun u => ⟨fun hu => Pnu_sub_one_unique hP hJ hu hv, fun e => e ▸ hv⟩, hψ⟩

/-- `x P_ν y` for a finite `A` with `ν = N₀c'A`. -/
private theorem Pnu_n₀c_eq {α β : Type*} [Nonempty β] {P : α → α → Prop}
    (hP : P ∈ arrow one Cls ∪ arrow Cls one) (hJ : po P ⪽ J) {A : Set β} (hA : A.Finite) :
    Pnu P (n₀c A) = pwr P (Nat.card A) := by
  funext x y
  apply propext
  rw [Pnu_n₀c_pwr hP hJ]
  exact ⟨fun h => h.2.2, fun h => ⟨inferInstance, hA, h⟩⟩

private theorem exists_set_card {β : Type*} {m : ℕ} (h : ¬ Finite β ∨ m ≤ Nat.card β) :
    ∃ A : Set β, A.Finite ∧ Nat.card A = m := by
  obtain ⟨f⟩ := emb_of_finite_card_le (X := Fin m) (Y := β) (by rwa [Nat.card_fin])
  refine ⟨Set.range f, Set.finite_range f, ?_⟩
  rw [← Nat.card_congr (Equiv.ofInjective f f.injective), Nat.card_fin]

/-- A chain `x P^k y` has `k + 1` distinct terms, so a type into which `α` injects has them. -/
private theorem card_bound {α β : Type*} {P : α → α → Prop} (hαβ : Nonempty (α ↪ β))
    (hP : P ∈ arrow one Cls ∪ arrow Cls one) (hJ : po P ⪽ J) {k : ℕ} {x y : α}
    (h : pwr P k x y) : ¬ Finite β ∨ k + 1 ≤ Nat.card β := by
  by_cases hβ : Finite β
  · right
    obtain ⟨f⟩ := hαβ
    have : Finite α := Finite.of_injective f f.injective
    obtain ⟨-, hc⟩ := pwr_card' hP hJ h
    rw [← hc, ← Nat.card_coe_set_eq]
    exact (Finite.card_subtype_le _).trans (Finite.card_le_of_embedding f)
  · exact Or.inl hβ

/-- In a finite type, `P^m = Λ̇` once `m` reaches the number of terms of the type. -/
private theorem pwr_bot {α : Type*} [Finite α] {P : α → α → Prop}
    (hP : P ∈ arrow one Cls ∪ arrow Cls one) (hJ : po P ⪽ J) {m : ℕ} (hm : Nat.card α ≤ m)
    {x y : α} : ¬ pwr P m x y := fun h => by
  obtain ⟨-, hc⟩ := pwr_card' hP hJ h
  have := Finite.card_subtype_le (fun z => z ∈ itvCC P x y)
  rw [Nat.card_coe_set_eq, hc] at this
  omega

/-- Every power `P^k` is `P^n` for some `n` that is the number of terms of a finite class of
the type `β` (and `n ≥ 1` if `k ≥ 1`). -/
private theorem realize {α β : Type*} [Nonempty β] {P : α → α → Prop} (hαβ : Nonempty (α ↪ β))
    (hP : P ∈ arrow one Cls ∪ arrow Cls one) (hJ : po P ⪽ J) (k : ℕ) :
    ∃ A : Set β, A.Finite ∧ (0 < k → A.Nonempty) ∧ pwr P (Nat.card A) = pwr P k := by
  by_cases hk : ¬ Finite β ∨ k ≤ Nat.card β
  · obtain ⟨A, hA, hc⟩ := exists_set_card hk
    refine ⟨A, hA, fun h => ?_, by rw [hc]⟩
    have : Finite ↥A := hA.to_subtype
    rw [← hc, Nat.card_pos_iff] at h
    exact Set.nonempty_coe_sort.1 h.1
  · push Not at hk
    obtain ⟨hβ, hkβ⟩ := hk
    obtain ⟨f⟩ := hαβ
    have : Finite α := Finite.of_injective f f.injective
    have hαβc : Nat.card α ≤ Nat.card β := Finite.card_le_of_embedding f
    have hβ1 : 1 ≤ Nat.card β := Nat.card_pos
    obtain ⟨A, hA, hc⟩ := exists_set_card (β := β) (m := max 1 (Nat.card α))
      (Or.inr (max_le hβ1 hαβc))
    refine ⟨A, hA, fun _ => ?_, ?_⟩
    · have : Finite ↥A := hA.to_subtype
      have h0 : 0 < Nat.card ↥A := by rw [hc]; exact lt_max_of_lt_left Nat.one_pos
      exact Set.nonempty_coe_sort.1 (Nat.card_pos_iff.1 h0).1
    · funext x y
      apply propext
      exact ⟨fun h => absurd h (pwr_bot hP hJ (by rw [hc]; exact le_max_right _ _)),
        fun h => absurd h (pwr_bot hP hJ (by omega))⟩

private theorem mem_NCinduct_sub_Null {β : Type*} {ν : Set (Set β)} (h : ν ∈ NCinduct \ ι Λ) :
    ∃ A : Set β, A.Finite ∧ ν = n₀c A := by
  obtain ⟨h1, h2⟩ := h
  rcases NCinduct_cases h1 with ⟨A, hA, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨A, hA, rfl⟩
  · exact absurd (mem_unitCls.2 Null_eq_empty.symm) h2

/-- `ν + 1` in a type `T` with room for it. -/
private theorem cardAdd_one_eq {β T : Type*} {X : Set β} (x0 : β)
    (h : Nonempty (↥X ⊕ PUnit.{1} ↪ T)) :
    ∃ Y : Set T, (n₀c X +ᶜ (one : Set (Set β)) : Set (Set T)) = n₀c Y ∧
      Nonempty (↥Y ≃ ↥X ⊕ PUnit.{1}) := by
  rw [one_eq_n₀c_singleton x0, cardAdd_n₀c,
    ncT_congr ((Equiv.refl ↥X).sumCongr (Equiv.ofUnique ↥({x0} : Set β) PUnit.{1}))]
  obtain ⟨Y, hY⟩ := ncT_nonempty_iff.2 h
  exact ⟨Y, ncT_eq_n₀c_of_mem hY, hY⟩

private theorem adeq_emb_unit {β W : Type*} {ν : Set (Set β)} (hW : AdeqAdd W ν (one : Set (Set β)))
    (X : Set β) (x0 : β) : Nonempty (↥X ⊕ PUnit.{1} ↪ W) := by
  obtain ⟨f⟩ := adeqAdd_emb hW X {x0}
  exact ⟨((Equiv.refl ↥X).sumCongr (Equiv.ofUnique PUnit.{1} ↥({x0} : Set β))).toEmbedding.trans f⟩

/-- If no term is `j` steps before `x` (`R` one-many), the ancestors of `x` are fewer than `j`. -/
private theorem emb_fin_of_no_pwr {α : Type*} {R : α → α → Prop} (hR : R ∈ arrow one Cls)
    {x : α} {j : ℕ} (h : ∀ z, ¬ pwr R j z x) : Nonempty (↥(refs (anc R) x) ↪ Fin j) := by
  have hF : ∀ w : ↥(refs (anc R) x), ∃ i : Fin j, pwr R i w x := by
    rintro ⟨w, hw⟩
    obtain ⟨i, hi⟩ := anc_pwr hw
    by_cases hij : i < j
    · exact ⟨⟨i, hij⟩, hi⟩
    · exfalso
      have hi' : pwr R (i - j + j) w x := by rwa [Nat.sub_add_cancel (Nat.le_of_not_lt hij)]
      obtain ⟨y, -, hy⟩ := pwr_add.1 hi'
      exact h y hy
  choose F hF using hF
  refine ⟨⟨F, fun w1 w2 e => Subtype.ext (pwr_one_many hR (hF w1) ?_)⟩⟩
  rw [e]
  exact hF w2

private theorem pwr_two_eq {α : Type*} {P : α → α → Prop} : pwr P 2 = rsq P := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pwr_succ_eq, pwr_one_eq]; rfl

private theorem pwr_three_eq {α : Type*} {P : α → α → Prop} : pwr P 3 = rcube P := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pwr_succ_eq, pwr_two_eq]; rfl

/-- `ν_P = y . yPz . ⊃ . (ν +_c 1)_P = z`, with `ν_P = y` unfolded (`P` many-one without cycles). -/
private theorem nuP_succ {α β W : Type*} {P : α → α → Prop} (hP : P ∈ arrow Cls one)
    (hJ : po P ⪽ J) {ν : Set (Set β)} (hW : AdeqAdd W ν (one : Set (Set β))) {b y z : α}
    (hb : ∀ x, Beg x P ↔ x = b)
    (hy : Pnu P (ν -ᶜ (one : Set (Set β)) : Set (Set β)) b y) (hyz : P y z) :
    Desc (nuP (ν +ᶜ (one : Set (Set β)) : Set (Set W))) P (fun v => z = v) := by
  have hU : P ∈ arrow one Cls ∪ arrow Cls one := Or.inr hP
  obtain ⟨X, ⟨x0, hx0⟩, rfl, ⟨e⟩⟩ := Pnu_sub_one.1 hy
  have hf : (itvCC P b y).Finite := mem_ClsInduct.1 (pm121_45 hP)
  have : Finite ↥(itvCC P b y) := hf.to_subtype
  have hXf : X.Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e)
  have : Finite ↥X := hXf.to_subtype
  have : Nonempty ↥X := ⟨⟨x0, hx0⟩⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥X = k + 1 := Nat.exists_eq_succ_of_ne_zero Nat.card_pos.ne'
  have hpw := (Pnu_sub_one_n₀c hU hJ hXf hk).1 hy
  obtain ⟨Y, hY, ⟨eY⟩⟩ := cardAdd_one_eq (T := W) x0 (adeq_emb_unit hW X x0)
  have hYf : Y.Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ eY.symm)
  have hYc : Nat.card ↥Y = (k + 1) + 1 := by
    rw [Nat.card_congr eY, Nat.card_sum, hk, Nat.card_unique]
  rw [hY, desc_nuP_iff_mo hP hJ]
  exact ⟨b, hb, z, (Pnu_sub_one_n₀c hU hJ hYf hYc).2 ⟨y, hpw, hyz⟩, rfl⟩

end C121late

/-- ✱121·5. \[\begin{align}\vdash :P\in (\text{Cls}\rightarrow 1)\cup (1\rightarrow \text{Cls}).&P_{\text{po}}\,\unicode{x2abd}\, J.\supset .\\ &\text{finid}ʻP=\text{Potid}ʻP.\text{fin}ʻP=\text{Pot}ʻP\end{align}\]

The type `β` of the apparent `ν` of `finid`, `fin` is explicit; by the Final Working Rule
(Prefatory Statement, VII: the type is taken "high enough so that no definitely determined
inductive number shall be null") it is one into which the type of `C'P` injects, so that every
`ν` with `ν +_c 1 = N₀c'P(x⊢⊣y)` exists in it (in a smaller type `finid'P` omits powers of `P`).

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): `[Nonempty
β]` for the type of `ν` (for empty `α`, `β`, `fin'P = Λ` but `Pot'P = ι'P`: `pm121_5_aux_empty`);
the type of `ν` is taken with `Nonempty (α ↪ β)` (Prefatory Statement, VII). -/
theorem pm121_5 {α β : Type*} [Nonempty β] {P : α → α → Prop} :
    Nonempty (α ↪ β) →
      (P ∈ arrow Cls one ∪ arrow one Cls ∧ po P ⪽ J) → (finid β P = potid P ∧ fin β P = pot P) := by
  rintro hαβ ⟨hP', hJ⟩
  have hP : P ∈ arrow one Cls ∪ arrow Cls one := hP'.symm
  constructor
  · ext R
    constructor
    · rintro ⟨ν, hν, rfl⟩
      obtain ⟨A, hA, rfl⟩ := mem_NCinduct_sub_Null hν
      exact mem_potid_iff.2 ⟨_, Pnu_n₀c_eq hP hJ hA⟩
    · intro hR
      obtain ⟨k, rfl⟩ := mem_potid_iff.1 hR
      obtain ⟨A, hA, -, hAk⟩ := realize hαβ hP hJ k
      refine ⟨n₀c A, ⟨n₀c_mem_NCinduct hA, fun h => ?_⟩, by rw [Pnu_n₀c_eq hP hJ hA, hAk]⟩
      rw [mem_unitCls, Null_eq_empty] at h
      exact n₀c_ne_empty A h
  · ext R
    constructor
    · rintro ⟨ν, ⟨hν, hν0⟩, rfl⟩
      obtain ⟨A, hA, rfl⟩ := mem_NCinduct_sub_Null hν
      have hA0 : A.Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        rintro rfl
        exact hν0 (mem_unitCls.2 zero_eq_n₀c_empty.symm)
      have : Finite ↥A := hA.to_subtype
      have : Nonempty ↥A := hA0.to_subtype
      obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥A = k + 1 := Nat.exists_eq_succ_of_ne_zero Nat.card_pos.ne'
      exact mem_pot_iff'.2 ⟨k, by rw [Pnu_n₀c_eq hP hJ hA, hk]⟩
    · intro hR
      obtain ⟨k, rfl⟩ := mem_pot_iff'.1 hR
      obtain ⟨A, hA, hA0, hAk⟩ := realize hαβ hP hJ (k + 1)
      have hA0 := hA0 (Nat.succ_pos k)
      refine ⟨n₀c A, ⟨⟨n₀c_mem_NCinduct hA, fun h => ?_⟩, fun h => ?_⟩,
        by rw [Pnu_n₀c_eq hP hJ hA, hAk]⟩
      · rw [mem_unitCls, Null_eq_empty] at h
        exact n₀c_ne_empty A h
      · rw [mem_unitCls, n₀c_eq_zero_iff] at h
        exact hA0.ne_empty h

/-- Without `[Nonempty β]` ✱121·5 fails when `α` and `β` are empty: then `fin'P = Λ` (the
only inductive cardinals of the type are `0` and `Λ`), while `Pot'P = ι'P`. -/
theorem pm121_5_aux_empty :
    ¬ ∀ P : PEmpty.{1} → PEmpty.{1} → Prop, Nonempty (PEmpty.{1} ↪ PEmpty.{1}) →
      (P ∈ arrow Cls one ∪ arrow one Cls ∧ po P ⪽ J) →
        (finid PEmpty.{1} P = potid P ∧ fin PEmpty.{1} P = pot P) := by
  intro h
  let P : PEmpty.{1} → PEmpty.{1} → Prop := fun x _ => x.elim
  have hP : P ∈ arrow Cls one ∪ arrow one Cls :=
    Or.inl (mem_arrow_Cls_one.2 fun x => x.elim)
  have hJ : po P ⪽ J := fun x => x.elim
  have h2 := (h P ⟨Function.Embedding.refl _⟩ ⟨hP, hJ⟩).2
  have hmem : P ∈ pot P := self_mem_pot P
  rw [← h2] at hmem
  obtain ⟨ν, ⟨⟨hν, hνΛ⟩, hν0⟩, -⟩ := hmem
  rcases NCinduct_cases hν with ⟨A, -, rfl⟩ | ⟨-, rfl⟩
  · apply hν0
    rw [mem_unitCls, n₀c_eq_zero_iff]
    exact Set.eq_empty_of_isEmpty A
  · exact hνΛ (mem_unitCls.2 Null_eq_empty.symm)

/-- ✱121·501. \[\begin{align}\vdash :P\in (\text{Cls}\rightarrow 1)\cup (1\rightarrow \text{Cls}).P_{\text{po}}\,\unicode{x2abd}\, &J.\dot{\exists} !P.\supset .\\ &\text{Pot}ʻP=\text{finid}ʻP-\iota ʻP_{0}=\text{fin}ʻP\end{align}\]

**Status.** proved (reading): the type of `ν` is taken with `Nonempty (α ↪ β)` (Prefatory Statement,
VII). -/
theorem pm121_501 {α β : Type*} {P : α → α → Prop} :
    Nonempty (α ↪ β) → ((P ∈ arrow Cls one ∪ arrow one Cls ∧ po P ⪽ J) ∧ rEx P) →
      (pot P = finid β P \ ι (Pnu P (zero : Set (Set β))) ∧
        finid β P \ ι (Pnu P (zero : Set (Set β))) = fin β P) := by
  rintro ⟨f⟩ ⟨⟨hP, hJ⟩, x, y, hxy⟩
  have : Nonempty β := ⟨f x⟩
  have h5 := pm121_5 ⟨f⟩ ⟨hP, hJ⟩
  have h0 : rEx (Pnu P (zero : Set (Set β))) :=
    ⟨x, x, (pm121_301 (fun h => hJ x x h rfl)).2 ⟨⟨y, Or.inl hxy⟩, rfl⟩⟩
  have h327 := pm121_327 h0
  exact ⟨h5.2.symm.trans h327, h327.symm⟩

/-- ✱121·502. \[\begin{align}\vdash :P\in (\text{Cls}\rightarrow 1)\cup (1\rightarrow \text{Cls}).P_{\text{po}}&\,\unicode{x2abd}\, J.\supset .\\ &\dot{s} ʻ(\text{finid}ʻP-\iota ʻP_{0})=P_{\text{po}}=\dot{s} ʻ\text{fin}ʻP\end{align}\]

**Status.** proved (reading): the type of `ν` is taken with `Nonempty (α ↪ β)` (Prefatory Statement,
VII). -/
theorem pm121_502 {α β : Type*} {P : α → α → Prop} :
    Nonempty (α ↪ β) → (P ∈ arrow Cls one ∪ arrow one Cls ∧ po P ⪽ J) →
      (sumRel (finid β P \ ι (Pnu P (zero : Set (Set β)))) = po P ∧ po P = sumRel (fin β P)) := by
  rintro ⟨f⟩ ⟨hP', hJ⟩
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a⟩⟩
  · exact ⟨funext fun x => isEmptyElim x, funext fun x => isEmptyElim x⟩
  have : Nonempty β := ⟨f a⟩
  have hP : P ∈ arrow one Cls ∪ arrow Cls one := hP'.symm
  have h5 := pm121_5 ⟨f⟩ ⟨hP', hJ⟩
  have h0 : Pnu P (zero : Set (Set β)) = pwr P 0 := by
    rw [zero_eq_n₀c_empty, Pnu_n₀c_eq hP hJ Set.finite_empty, Nat.card_coe_set_eq, Set.ncard_empty]
  refine ⟨?_, by show sumRel (pot P) = _; rw [h5.2]⟩
  funext x y
  apply propext
  constructor
  · rintro ⟨R, ⟨hR, hR0⟩, hRxy⟩
    rw [h5.1] at hR
    obtain ⟨k, rfl⟩ := mem_potid_iff.1 hR
    rcases k with _ | k
    · exact absurd (mem_unitCls.2 h0.symm) hR0
    · exact po_iff_transGen.2 (transGen_of_pwr hRxy)
  · intro hxy
    obtain ⟨k, hk⟩ := anc_pwr (anc_of_po hxy)
    refine ⟨pwr P k, ⟨by rw [h5.1]; exact mem_potid_iff.2 ⟨k, rfl⟩, fun h => ?_⟩, hk⟩
    rw [mem_unitCls, h0] at h
    rw [h] at hk
    obtain ⟨rfl, -⟩ := hk
    exact hJ x x hxy rfl

/-- ✱121·51. \(\vdash :P\in (\text{Cls}\rightarrow 1)\cup (1\rightarrow \text{Cls}).P_{\text{po}}\,\unicode{x2abd}\, J.\supset .P_{2}=P^{2}.P_{3}=P^{3}.\text{etc}.\)

"etc." is stated for `2` and `3` (`3 = 2 +_c 1`, in the type of `2`). The constant subscripts are
arguments of `+_c` (✱121·02), so they are taken in a type in which they exist (convention IIT):
`∃!(2 +_c 1)` there (in a smaller type `P_2` or `P_3` is `Λ̇`).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): hypothesis `∃!(2 +_c 1)` in
the type of the subscripts. -/
theorem pm121_51 {α β : Type*} {P : α → α → Prop} :
    ((two : Set (Set β)) +ᶜ (one : Set (Set β)) : Set (Set β)).Nonempty →
    (P ∈ arrow Cls one ∪ arrow one Cls ∧ po P ⪽ J) →
      (Pnu P (two : Set (Set β)) = rsq P ∧
        Pnu P ((two : Set (Set β)) +ᶜ (one : Set (Set β)) : Set (Set β)) = rcube P) := by
  rintro hne ⟨hP', hJ⟩
  have hP : P ∈ arrow one Cls ∪ arrow Cls one := hP'.symm
  obtain ⟨A, B, ⟨hA, hB⟩, ⟨g⟩⟩ := cardAdd_nonempty_iff.1 hne
  obtain ⟨x, y, hxy, hAxy⟩ := mem_two_iff.1 (hA ▸ self_mem_n₀c A : A ∈ (two : Set (Set β)))
  obtain ⟨u⟩ := unit_of_mem_one (hB ▸ self_mem_n₀c B : B ∈ (one : Set (Set β)))
  have : Nonempty β := ⟨x⟩
  have : Finite ↥B := Finite.of_equiv _ u.symm
  have hAf : A.Finite := by rw [hAxy]; exact Set.toFinite _
  have hA2 : Nat.card ↥A = 2 := by rw [Nat.card_coe_set_eq, hAxy, Set.ncard_pair hxy]
  have : Finite ↥A := hAf.to_subtype
  let C : Set β := Set.range g
  have eC : ↥C ≃ ↥A ⊕ ↥B := (Equiv.ofInjective g g.injective).symm
  have hCf : C.Finite := Set.finite_range g
  have hC3 : Nat.card ↥C = 3 := by
    rw [Nat.card_congr (eC.trans ((Equiv.refl _).sumCongr u)), Nat.card_sum, hA2,
      Nat.card_unique]
  have hsum : ((two : Set (Set β)) +ᶜ (one : Set (Set β)) : Set (Set β)) = n₀c C := by
    rw [hA, hB, cardAdd_n₀c, n₀c_eq_ncT]
    exact ncT_congr eC.symm
  refine ⟨?_, ?_⟩
  · rw [hA, Pnu_n₀c_eq hP hJ hAf, hA2, pwr_two_eq]
  · rw [hsum, Pnu_n₀c_eq hP hJ hCf, hC3, pwr_three_eq]

/-- ✱121·52. \[\begin{align}&\vdash :P\in (\text{Cls}\rightarrow 1)\cup (1\rightarrow \text{Cls}).P_{\text{po}}\,\unicode{x2abd}\, J.\supset .\dot{s} ʻ\text{finid}ʻP=P_{*}\\ &[*121·5.*91·55]\end{align}\]

**Status.** proved (reading): the type of `ν` is taken with `Nonempty (α ↪ β)` (Prefatory Statement,
VII). -/
theorem pm121_52 {α β : Type*} {P : α → α → Prop} :
    Nonempty (α ↪ β) → (P ∈ arrow Cls one ∪ arrow one Cls ∧ po P ⪽ J) →
      sumRel (finid β P) = anc P := by
  rintro ⟨f⟩ h
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a⟩⟩
  · exact funext fun x => isEmptyElim x
  have : Nonempty β := ⟨f a⟩
  rw [(pm121_5 ⟨f⟩ h).1]
  funext x y
  apply propext
  constructor
  · rintro ⟨R, hR, hxy⟩
    obtain ⟨k, rfl⟩ := mem_potid_iff.1 hR
    exact pwr_anc hxy
  · intro hxy
    obtain ⟨k, hk⟩ := anc_pwr hxy
    exact ⟨pwr P k, mem_potid_iff.2 ⟨k, rfl⟩, hk⟩

/-- ✱121·6. \(\vdash \colon\ldotp \nu \neq 0.\supset .f(\nu _{P}).\equiv .f[\breve{\iota} ʻ\hat{y} \{\text{N}_{0}\text{c}ʻP(BʻP\vdash\dashv y)=\nu\}]\)

`ῐ'ŷ{N₀c'P(B'P⊢⊣y) = ν}` is `Desc iota˘` of the class, the inner `B'P` with the smallest scope; the
equation puts `ν` in the type of `P`'s field. -/
theorem pm121_6 {α : Type*} {P : α → α → Prop} {ν : Set (Set α)} {f : α → Prop} :
    ν ≠ zero → (Desc (nuP ν) P f ↔
      Desc iota˘ {y | Desc Beg P (fun b => n₀c (itvCC P b y) = ν)} f) := by
  intro hν
  rw [desc_nuP_iff, desc_iota_cnv]
  simp only [Pnu_sub_one_iff_eq hν]
  constructor
  · rintro ⟨b, hb, v, hv, hf⟩
    refine ⟨v, fun y => ?_, hf⟩
    show Desc Beg P (fun b => n₀c (itvCC P b y) = ν) ↔ y = v
    rw [desc_unique hb]
    exact hv y
  · rintro ⟨v, hv, hf⟩
    obtain ⟨b, hb, hbv⟩ := (hv v).2 rfl
    refine ⟨b, hb, v, fun u => ⟨fun hu => (hv u).1 ⟨b, hb, hu⟩, fun e => e ▸ hbv⟩, hf⟩

/-- ✱121·601. \(\vdash :\text{E}!BʻP.\supset .BʻP=1_{P}.{\sim}{(BʻP)P_{\text{po}}(BʻP)}\)

`B'P = 1_P` has two descriptions, the first with the larger scope; the `1` is in a type `β`, with
a member (otherwise `1 = Λ` there and `1_P` does not exist). In `∼{(B'P)P_po(B'P)}` the description
has the scope of the bracket.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): `[Nonempty
β]` for the type of the `1`. -/
theorem pm121_601 {α β : Type*} [Nonempty β] {P : α → α → Prop} :
    EDesc Beg P → (Desc Beg P (fun b => Desc (nuP (one : Set (Set β))) P (fun c => b = c)) ∧
      ¬ Desc Beg P (fun b => po P b b)) := by
  rintro ⟨b, hb⟩
  have hbB : Beg b P := (hb b).2 rfl
  have hbp : ¬ po P b b := fun h => hbB.2 (dom_codom_of_po h).2
  have hbf : b ∈ fld P := let ⟨c, hc⟩ := hbB.1; ⟨c, Or.inl hc⟩
  have key : ∀ u, Pnu P ((one : Set (Set β)) -ᶜ (one : Set (Set β)) : Set (Set β)) b u ↔ u = b := by
    intro u
    rw [Pnu_sub_one]
    constructor
    · rintro ⟨X, -, hX, ⟨e⟩⟩
      obtain ⟨t⟩ := unit_of_mem_one (hX ▸ self_mem_n₀c X : X ∈ (one : Set (Set β)))
      have hw := (e.symm (t.symm PUnit.unit)).2
      have hbu : anc P b u := anc_trans hw.1 hw.2
      have h1 : b ∈ itvCC P b u := ⟨anc_refl hbf, hbu⟩
      have h2 : u ∈ itvCC P b u := ⟨hbu, anc_refl (fld_of_anc_right hbu)⟩
      have := (e.trans t).injective (Subsingleton.elim ((e.trans t) ⟨u, h2⟩) ((e.trans t) ⟨b, h1⟩))
      exact congrArg Subtype.val this
    · rintro rfl
      let b0 : β := Classical.arbitrary β
      refine ⟨{b0}, Set.singleton_nonempty b0, one_eq_n₀c_singleton b0, ?_⟩
      rw [itvCC_self hbp hbf]
      exact ⟨Equiv.ofUnique _ _⟩
  refine ⟨(desc_unique hb).2 (desc_nuP_iff.2 ⟨b, hb, b, key, rfl⟩), fun h => ?_⟩
  exact hbp ((desc_unique hb (ψ := fun b => po P b b)).1 h)

/-- ✱121·602. \(\vdash :\text{E}!BʻP.P\in 1\rightarrow 1.\supset \breve{P} ʻBʻP=2_{P}\)

`P̆'B'P` is the double description `Desc2 P˘ Beg P`. The `2` of `2_P` (an argument of `−_c`,
✱121·04) is taken in a type where it exists (convention IIT; otherwise `2_P` does not exist).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): hypothesis `∃!2` in the type
of the `2`. -/
theorem pm121_602 {α β : Type*} {P : α → α → Prop} :
    (two : Set (Set β)).Nonempty → (EDesc Beg P ∧ P ∈ arrow one one) →
      Desc2 P˘ Beg P (fun c => Desc (nuP (two : Set (Set β))) P (fun d => c = d)) := by
  rintro ⟨X2, hX2⟩ ⟨⟨b, hb⟩, hP⟩
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hP
  have hbB : Beg b P := (hb b).2 rfl
  have hbp : ¬ po P b b := fun h => hbB.2 (dom_codom_of_po h).2
  obtain ⟨c, hbc⟩ := hbB.1
  have hbf : b ∈ fld P := ⟨c, Or.inl hbc⟩
  have hc : ∀ u, P b u ↔ u = c := fun u => ⟨fun h => h2 b u c ⟨h, hbc⟩, fun e => e ▸ hbc⟩
  have hbc' : b ≠ c := fun e => hbB.2 ⟨b, e ▸ hbc⟩
  obtain ⟨x1, x2, hx12, hX2e⟩ := mem_two_iff.1 hX2
  have htwo : (two : Set (Set β)) = n₀c X2 := by
    rw [two_eq_ncT.{_, 0}] at hX2 ⊢
    exact ncT_eq_n₀c_of_mem hX2
  have hX2c : Nat.card ↥X2 = 2 := by rw [Nat.card_coe_set_eq, hX2e, Set.ncard_pair hx12]
  have key : ∀ u, Pnu P ((two : Set (Set β)) -ᶜ (one : Set (Set β)) : Set (Set β)) b u ↔
      u = c := by
    intro u
    rw [Pnu_sub_one]
    constructor
    · rintro ⟨X, -, hX, ⟨e⟩⟩
      rw [htwo] at hX
      obtain ⟨g⟩ := eq_n₀c_iff_equiv.1 hX
      have hcard : (itvCC P b u).ncard = 2 := by
        rw [← Nat.card_coe_set_eq, Nat.card_congr (e.trans g.symm), hX2c]
      have hfin : (itvCC P b u).Finite := Set.finite_of_ncard_pos (by omega)
      have hw := (e.symm (g ⟨x1, by rw [hX2e]; exact Or.inl rfl⟩)).2
      have hbu : anc P b u := anc_trans hw.1 hw.2
      by_contra huc
      have hub : u ≠ b := by
        rintro rfl
        rw [itvCC_self hbp hbf, Set.ncard_singleton] at hcard
        omega
      have hpo : po P b u := by
        rcases anc_iff_po.1 hbu with ⟨e', -⟩ | h
        · exact absurd e'.symm hub
        · exact h
      obtain ⟨c', hbc'', hc'u⟩ := Relation.TransGen.head'_iff.1 (po_iff_transGen.1 hpo)
      have hc'c : c' = c := (hc c').1 hbc''
      subst hc'c
      have hsub : ({b, c', u} : Set α) ⊆ itvCC P b u := by
        rintro z (rfl | rfl | rfl)
        · exact ⟨anc_refl hbf, hbu⟩
        · exact ⟨anc_of_step hbc'', anc_iff_reflTransGen.2 ⟨⟨b, Or.inr hbc''⟩, hc'u⟩⟩
        · exact ⟨hbu, anc_refl (fld_of_anc_right hbu)⟩
      have h3 : ({b, c', u} : Set α).ncard = 3 :=
        Set.ncard_eq_three.2 ⟨b, c', u, hbc', fun e => hub e.symm, fun e => huc e.symm, rfl⟩
      have := Set.ncard_le_ncard hsub hfin
      omega
    · rintro rfl
      obtain ⟨hI, -⟩ := pm121_306 ⟨⟨mem_arrow_one_Cls.2 h1, hbp⟩, hbc⟩
      refine ⟨X2, ⟨x1, by rw [hX2e]; exact Or.inl rfl⟩, htwo, ?_⟩
      rw [hI, unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]
      have : Finite ↥X2 := by rw [hX2e]; exact Set.toFinite _
      apply Finite.card_eq.1
      rw [hX2c, Nat.card_coe_set_eq, Set.ncard_pair hbc']
  rw [desc2_iff, desc_unique hb]
  show TheIs (fun u => P b u) _
  rw [TheIs_iff_of_unique hc]
  exact desc_nuP_iff.2 ⟨b, hb, c, key, rfl⟩

/-- ✱121·61. \[\begin{align}\vdash :P\in 1\rightarrow \text{Cls}.P_{\text{po}}\,\unicode{x2abd}\, J.x\in &sʻ\text{gen}ʻP.\supset .\\ &(\exists a,\nu ).a BP.\nu \in \text{NC induct}.a P_{\nu }x\end{align}\]

`aBP` is `Beg a P`; the type `β` of the apparent `ν` is one into which the type of `C'P` injects
(as ✱121·5: Prefatory Statement, VII), so that the cardinal `ν` with `ν +_c 1 = N₀c'P(a⊢⊣x)`
exists in it.

**Status.** proved (reading): the type of `ν` is taken with `Nonempty (α ↪ β)` (Prefatory Statement,
VII). -/
theorem pm121_61 {α β : Type*} {P : α → α → Prop} {x : α} :
    Nonempty (α ↪ β) → ((P ∈ arrow one Cls ∧ po P ⪽ J) ∧ x ∈ sumCls (gen P)) →
      ∃ (a : α) (ν : Set (Set β)), (Beg a P ∧ ν ∈ NCinduct) ∧ Pnu P ν a x := by
  rintro ⟨f⟩ ⟨⟨hP, hJ⟩, hx⟩
  have hU : P ∈ arrow one Cls ∪ arrow Cls one := Or.inl hP
  obtain ⟨a, k, ha, hk⟩ := gen_beg hx
  have : Nonempty β := ⟨f a⟩
  obtain ⟨A, hA, hc⟩ := exists_set_card (β := β) (m := k)
    ((card_bound ⟨f⟩ hU hJ hk).imp_right fun h => by omega)
  exact ⟨a, n₀c A, ⟨ha, n₀c_mem_NCinduct hA⟩, by rw [Pnu_n₀c_eq hU hJ hA, hc]; exact hk⟩

/-- ✱121·62. \[\begin{align}\vdash :P\in \text{Cls}\rightarrow 1.P_{\text{po}}\,\unicode{x2abd}\, J.(BʻP)&P_{*}x.\supset .\\ &(\exists \nu ).\nu \in \text{NC induct}-\iota ʻ0.x=\nu _{P}\end{align}\]

The type `β` of the apparent `ν` is taken as in ✱121·61.

**Status.** proved (reading): the type of `ν` is taken with `Nonempty (α ↪ β)` (Prefatory Statement,
VII). -/
theorem pm121_62 {α β : Type*} {P : α → α → Prop} {x : α} :
    Nonempty (α ↪ β) → ((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ Desc Beg P (fun b => anc P b x)) →
      ∃ ν : Set (Set β), ν ∈ (NCinduct \ ι zero) ∧ Desc (nuP ν) P (fun v => x = v) := by
  rintro hαβ ⟨⟨hP, hJ⟩, b, hb, hbx⟩
  have hU : P ∈ arrow one Cls ∪ arrow Cls one := Or.inr hP
  obtain ⟨k, hk⟩ := anc_pwr hbx
  obtain ⟨A, hA, hc⟩ := exists_set_card (β := β) (card_bound hαβ hU hJ hk)
  refine ⟨n₀c A, ⟨n₀c_mem_NCinduct hA, fun h => ?_⟩, ?_⟩
  · rw [mem_unitCls, n₀c_eq_zero_iff] at h
    subst h
    rw [Nat.card_coe_set_eq, Set.ncard_empty] at hc
    omega
  · exact (desc_nuP_iff_mo hP hJ).2 ⟨b, hb, x, (Pnu_sub_one_n₀c hU hJ hA hc).2 hk, rfl⟩

/-- ✱121·63. \(\vdash :\text{E}!\nu _{P}.\supset .\text{N}_{0}\text{c}ʻP(BʻP\vdash\dashv \nu _{P})=\nu\)

The equation puts `ν` in the type of `P`'s field. -/
theorem pm121_63 {α : Type*} {P : α → α → Prop} {ν : Set (Set α)} :
    EDesc (nuP ν) P → Desc (nuP ν) P (fun v => Desc Beg P (fun b => n₀c (itvCC P b v) = ν)) := by
  intro h
  obtain ⟨b, hb, v, hv, -⟩ := desc_nuP_iff.1 (edesc_iff_desc.1 h)
  refine desc_nuP_iff.2 ⟨b, hb, v, hv, (desc_unique hb).2 ?_⟩
  obtain ⟨X, -, rfl, e⟩ := Pnu_sub_one.1 ((hv v).2 rfl)
  exact eq_n₀c_iff_equiv.2 e

/-- ✱121·631. \[\begin{align}\vdash \colon\ldotp P\in \text{Cls}\rightarrow 1.&P_{\text{po}}\,\unicode{x2abd}\, J.\nu \in \text{NC induct}-\iota ʻ0.\supset :\\ &\text{N}_{0}\text{c}ʻP(BʻP\vdash\dashv y)=\nu .\equiv .y=\nu _{P}.\equiv .(BʻP)P_{\nu -_{c}1}y\end{align}\] -/
theorem pm121_631 {α : Type*} {P : α → α → Prop} {ν : Set (Set α)} {y : α} :
    ((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ ν ∈ NCinduct \ ι zero) →
      ((Desc Beg P (fun b => n₀c (itvCC P b y) = ν) ↔ Desc (nuP ν) P (fun v => y = v)) ∧
        (Desc (nuP ν) P (fun v => y = v) ↔
          Desc Beg P (fun b => Pnu P (ν -ᶜ (one : Set (Set α)) : Set (Set α)) b y))) := by
  rintro ⟨⟨hP, hJ⟩, -, hν0⟩
  have hν : ν ≠ zero := fun h => hν0 (mem_unitCls.2 h)
  have h2 : Desc (nuP ν) P (fun v => y = v) ↔
      Desc Beg P (fun b => Pnu P (ν -ᶜ (one : Set (Set α)) : Set (Set α)) b y) := by
    rw [desc_nuP_iff_mo hP hJ]
    constructor
    · rintro ⟨b, hb, v, hv, rfl⟩
      exact ⟨b, hb, hv⟩
    · rintro ⟨b, hb, hv⟩
      exact ⟨b, hb, y, hv, rfl⟩
  refine ⟨?_, h2⟩
  rw [h2]
  exact desc_congr fun b => (Pnu_sub_one_iff_eq hν).symm

/-- ✱121·632. \(\vdash :P\in \text{Cls}\rightarrow 1.P_{\text{po}}\,\unicode{x2abd}\, J.\nu \in \text{NC induct}-\iota ʻ0.y=\nu _{P}.yPz.\supset .z=(\nu +_{c}1)_{P}\)

The real variable `ν` has its own type `β`; the subscript `ν +_c 1` (an argument of `−_c`,
✱121·04) is in an adequate type `W` (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
subscript `ν +_c 1` is adequate. -/
theorem pm121_632 {α β W : Type*} {P : α → α → Prop} {ν : Set (Set β)} {y z : α} :
    AdeqAdd W ν (one : Set (Set β)) →
    ((((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ ν ∈ NCinduct \ ι zero) ∧
        Desc (nuP ν) P (fun v => y = v)) ∧ P y z) →
      Desc (nuP (ν +ᶜ (one : Set (Set β)) : Set (Set W))) P (fun v => z = v) := by
  rintro hW ⟨⟨⟨⟨hP, hJ⟩, -⟩, hy⟩, hyz⟩
  obtain ⟨b, hb, v, hv, rfl⟩ := (desc_nuP_iff_mo hP hJ).1 hy
  exact nuP_succ hP hJ hW hb hv hyz

/-- ✱121·633. \[\begin{align}\vdash :P\in \text{Cls}\rightarrow 1.P_{\text{po}}\,\unicode{x2abd}\, J.\nu \in &\text{NC induct}-\iota ʻ0.\nu _{P}\in \text{D}ʻP.\supset .\\ &\text{E}!(\nu +_{c}1)_{P}.(\nu +_{c}1)_{P}=\breve{P} ʻ\nu _{P}\\ &[*121·632]\end{align}\]

As ✱121·632 (`ν` in its own type `β`, `ν +_c 1` in an adequate type `W`).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
subscript `ν +_c 1` is adequate. -/
theorem pm121_633 {α β W : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    AdeqAdd W ν (one : Set (Set β)) →
    (((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ ν ∈ NCinduct \ ι zero) ∧
        Desc (nuP ν) P (fun v => v ∈ dom P)) →
      (EDesc (nuP (ν +ᶜ (one : Set (Set β)) : Set (Set W))) P ∧
        Desc (nuP (ν +ᶜ (one : Set (Set β)) : Set (Set W))) P
          (fun w => Desc (nuP ν) P (fun v => Desc P˘ v (fun u => w = u)))) := by
  rintro hW ⟨⟨⟨hP, hJ⟩, -⟩, hy⟩
  obtain ⟨b, hb, y, hv, z, hyz⟩ := (desc_nuP_iff_mo hP hJ).1 hy
  have h := nuP_succ hP hJ hW hb hv hyz
  have hy' : Desc (nuP ν) P (fun v => y = v) := (desc_nuP_iff_mo hP hJ).2 ⟨b, hb, y, hv, rfl⟩
  refine ⟨edesc_iff_desc.2 ((desc_of_eq h).2 trivial), (desc_of_eq h).2 ((desc_of_eq hy').2 ?_)⟩
  exact ⟨z, fun u => ⟨fun hu => mem_arrow_Cls_one.1 hP y u z ⟨hu, hyz⟩, fun e => e ▸ hyz⟩, rfl⟩

/-- ✱121·634. \[\begin{align}&\vdash \colon\ldotp P\in \text{Cls}\rightarrow 1.P_{\text{po}}\,\unicode{x2abd}\, J.\nu \in \text{NC induct}-\iota ʻ0.\supset :\nu _{P}\in \text{D}ʻP.\equiv .\text{E}!(\nu +_{c}1)_{P}\\ &[*121·633·631·333·352]\end{align}\]

As ✱121·632 (`ν` in its own type `β`, `ν +_c 1` in an adequate type `W`).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
subscript `ν +_c 1` is adequate. -/
theorem pm121_634 {α β W : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    AdeqAdd W ν (one : Set (Set β)) →
    ((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ ν ∈ NCinduct \ ι zero) →
      (Desc (nuP ν) P (fun v => v ∈ dom P) ↔
        EDesc (nuP (ν +ᶜ (one : Set (Set β)) : Set (Set W))) P) := by
  rintro hW ⟨⟨hP, hJ⟩, hν⟩
  refine ⟨fun h => (pm121_633 hW ⟨⟨⟨hP, hJ⟩, hν⟩, h⟩).1, fun h => ?_⟩
  have hU : P ∈ arrow one Cls ∪ arrow Cls one := Or.inr hP
  obtain ⟨b, hb, v, hv, -⟩ := (desc_nuP_iff_mo hP hJ).1 (edesc_iff_desc.1 h)
  obtain ⟨Y, -, hY, ⟨e⟩⟩ := Pnu_sub_one.1 hv
  have hYm : Y ∈ (ν +ᶜ (one : Set (Set β)) : Set (Set W)) := hY ▸ self_mem_n₀c Y
  obtain ⟨A, O, ⟨rfl, hO⟩, ⟨g⟩⟩ := mem_cardAdd'.1 hYm
  obtain ⟨u⟩ := unit_of_mem_one (hO ▸ self_mem_n₀c O)
  have hf : (itvCC P b v).Finite := mem_ClsInduct.1 (pm121_45 hP)
  have : Finite ↥(itvCC P b v) := hf.to_subtype
  have : Finite ↥Y := Finite.of_equiv _ e
  have : Finite ↥A := finite_left_of_equiv g
  have hA0 : A.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hν.2 (mem_unitCls.2 zero_eq_n₀c_empty.symm)
  have : Nonempty ↥A := hA0.to_subtype
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥A = k + 1 := Nat.exists_eq_succ_of_ne_zero Nat.card_pos.ne'
  have hYc : Nat.card ↥Y = (k + 1) + 1 := by
    rw [Nat.card_congr (g.trans ((Equiv.refl _).sumCongr u)), Nat.card_sum, hk, Nat.card_unique]
  have hpw := (Pnu_sub_one_n₀c hU hJ (Set.toFinite Y) hYc).1 (hY ▸ hv)
  obtain ⟨w, hw, hwv⟩ := pwr_succ.1 hpw
  exact (desc_nuP_iff_mo hP hJ).2 ⟨b, hb, w, (Pnu_sub_one_n₀c hU hJ (Set.toFinite A) hk).2 hw,
    v, hwv⟩

/-- ✱121·635. \(\vdash :P\in \text{Cls}\rightarrow 1.P_{\text{po}}\,\unicode{x2abd}\, J.\text{E}!\nu _{P}.\supset .\nu \in \text{NC induct}-\iota ʻ0\) -/
theorem pm121_635 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    ((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ EDesc (nuP ν) P) → ν ∈ NCinduct \ ι zero := by
  rintro ⟨⟨hP, -⟩, h⟩
  obtain ⟨b, -, v, hv, -⟩ := desc_nuP_iff.1 (edesc_iff_desc.1 h)
  obtain ⟨X, hX, rfl, ⟨e⟩⟩ := Pnu_sub_one.1 ((hv v).2 rfl)
  have hf : (itvCC P b v).Finite := mem_ClsInduct.1 (pm121_45 hP)
  have : Finite ↥(itvCC P b v) := hf.to_subtype
  have hXf : X.Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e)
  refine ⟨n₀c_mem_NCinduct hXf, fun h0 => ?_⟩
  rw [mem_unitCls, n₀c_eq_zero_iff] at h0
  exact hX.ne_empty h0

/-- ✱121·636. \[\begin{align}\vdash :P\in \text{Cls}\rightarrow 1.P_{\text{po}}\,\unicode{x2abd}\, J.&\text{E}!\nu _{P}.{\sim}\text{E}!(\nu +_{c}1)_{P}.\supset .\\ &\overleftarrow{P}_{*}ʻBʻP=P(BʻP\vdash\dashv \nu _{P}).\text{N}_{0}\text{c}ʻ\overleftarrow{P}_{*}ʻBʻP=\nu\end{align}\] -/
theorem pm121_636 {α : Type*} {P : α → α → Prop} {ν : Set (Set α)} :
    (((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ EDesc (nuP ν) P) ∧
        ¬ EDesc (nuP (ν +ᶜ (one : Set (Set α)) : Set (Set α))) P) →
      (Desc Beg P (fun b => Desc (nuP ν) P (fun v => rels (anc P) b = itvCC P b v)) ∧
        Desc Beg P (fun b => n₀c (rels (anc P) b) = ν)) := by
  rintro ⟨⟨⟨hP, hJ⟩, h⟩, hn⟩
  have hU : P ∈ arrow one Cls ∪ arrow Cls one := Or.inr hP
  obtain ⟨b, hb, v, hv, -⟩ := (desc_nuP_iff_mo hP hJ).1 (edesc_iff_desc.1 h)
  obtain ⟨X, ⟨x0, hx0⟩, hνX, ⟨e⟩⟩ := Pnu_sub_one.1 hv
  have hf : (itvCC P b v).Finite := mem_ClsInduct.1 (pm121_45 hP)
  have : Finite ↥(itvCC P b v) := hf.to_subtype
  have hXf : X.Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e)
  have : Finite ↥X := hXf.to_subtype
  have : Nonempty ↥X := ⟨⟨x0, hx0⟩⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥X = k + 1 := Nat.exists_eq_succ_of_ne_zero Nat.card_pos.ne'
  subst hνX
  have hpw := (Pnu_sub_one_n₀c hU hJ hXf hk).1 hv
  have hvd : v ∉ dom P := by
    rintro ⟨v', hvv'⟩
    apply hn
    have hpw' : pwr P (k + 1) b v' := ⟨v, hpw, hvv'⟩
    obtain ⟨hf', hc'⟩ := pwr_card' hU hJ hpw'
    have : Finite ↥(itvCC P b v') := hf'.to_subtype
    have hemb : Nonempty (↥X ⊕ PUnit.{1} ↪ α) := by
      have : Nonempty (↥X ⊕ PUnit.{1} ≃ ↥(itvCC P b v')) := by
        apply Finite.card_eq.1
        rw [Nat.card_sum, hk, Nat.card_unique, Nat.card_coe_set_eq, hc']
      obtain ⟨g⟩ := this
      exact ⟨g.toEmbedding.trans (Function.Embedding.subtype _)⟩
    obtain ⟨Y, hY, ⟨eY⟩⟩ := cardAdd_one_eq (T := α) x0 hemb
    have hYf : Y.Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ eY.symm)
    have hYc : Nat.card ↥Y = (k + 1) + 1 := by
      rw [Nat.card_congr eY, Nat.card_sum, hk, Nat.card_unique]
    rw [hY, edesc_iff_desc, desc_nuP_iff_mo hP hJ]
    exact ⟨b, hb, v', (Pnu_sub_one_n₀c hU hJ hYf hYc).2 hpw', trivial⟩
  have hpost : rels (anc P) b = itvCC P b v := by
    ext w
    refine ⟨fun hw => ⟨hw, ?_⟩, fun hw => hw.1⟩
    have hbv := pwr_anc hpw
    rcases rtg_comparable hP (anc_iff_reflTransGen.1 hw).2 (anc_iff_reflTransGen.1 hbv).2
      with h' | h'
    · exact anc_iff_reflTransGen.2 ⟨fld_of_anc_right hw, h'⟩
    · rcases Relation.reflTransGen_iff_eq_or_transGen.1 h' with rfl | h''
      · exact anc_refl (fld_of_anc_right hw)
      · exact absurd (dom_codom_of_po (po_iff_transGen.2 h'')).1 hvd
  refine ⟨(desc_unique hb).2 ((desc_nuP_iff_mo hP hJ).2 ⟨b, hb, v, hv, hpost⟩),
    (desc_unique hb).2 ?_⟩
  rw [hpost]
  exact eq_n₀c_iff_equiv.2 ⟨e⟩

/-- ✱121·637. \(\vdash :\text{E}!\nu _{P}.\supset .\nu _{P}\in CʻP\) -/
theorem pm121_637 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    EDesc (nuP ν) P → Desc (nuP ν) P (fun v => v ∈ fld P) := by
  intro h
  refine TheIs_iff.2 ⟨h, fun v hv => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨c, -, hc⟩ := (hu v).2 rfl
  exact fld_of_anc_right (anc_of_Pnu hc)

/-- ✱121·638. \(\vdash \colon\ldotp \text{E}!(\nu +_{c}1)_{P}.\supset :(BʻP)P_{\nu }x.\equiv .x=(\nu +_{c}1)_{P}:(\nu +_{c}1)-_{c}1=\nu \)

The real variable `ν` has its own type `β`; `(ν +_c 1) −_c 1 = ν` is in the type of `ν`. The two
occurrences of `ν +_c 1` (the subscript, an argument of `−_c` by ✱121·04, and the minuend) are
arithmetical, in adequate types `W`, `W'` (IIT). No `[Nonempty β]` is needed: in an empty `β`,
`1 = Λ`, so `ν +_c 1 = Λ` and `E!(ν +_c 1)_P` is false.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types `W`, `W'`
of the two occurrences of `ν +_c 1` are adequate. -/
theorem pm121_638 {α β W W' : Type*} {P : α → α → Prop} {ν : Set (Set β)} {x : α} :
    AdeqAdd W ν (one : Set (Set β)) → AdeqAdd W' ν (one : Set (Set β)) →
    EDesc (nuP (ν +ᶜ (one : Set (Set β)) : Set (Set W))) P →
      ((Desc Beg P (fun b => Pnu P ν b x) ↔
          Desc (nuP (ν +ᶜ (one : Set (Set β)) : Set (Set W))) P (fun v => x = v)) ∧
        ((ν +ᶜ (one : Set (Set β)) : Set (Set W')) -ᶜ (one : Set (Set W')) : Set (Set β)) = ν) := by
  intro _ hW' h
  obtain ⟨b, hb, v, hv, -⟩ := desc_nuP_iff.1 (edesc_iff_desc.1 h)
  obtain ⟨Y, -, hY, ⟨eY⟩⟩ := Pnu_sub_one.1 ((hv v).2 rfl)
  have hYm : Y ∈ (ν +ᶜ (one : Set (Set β)) : Set (Set W)) := hY ▸ self_mem_n₀c Y
  obtain ⟨A, O, ⟨rfl, hO⟩, ⟨g⟩⟩ := mem_cardAdd'.1 hYm
  obtain ⟨o, -⟩ : O ∈ (one : Set (Set β)) := hO ▸ self_mem_n₀c O
  obtain ⟨u⟩ := unit_of_mem_one (hO ▸ self_mem_n₀c O)
  have : Nonempty β := ⟨o⟩
  have key : ∀ w, Pnu P (n₀c A) b w ↔
      Pnu P ((n₀c A +ᶜ (one : Set (Set β)) : Set (Set W)) -ᶜ (one : Set (Set W)) :
        Set (Set W)) b w := by
    intro w
    rw [Pnu_iff, Pnu_sub_one]
    constructor
    · rintro ⟨-, B, hB, ⟨e⟩⟩
      obtain ⟨gB⟩ := eq_n₀c_iff_equiv.1 hB
      exact ⟨Y, ⟨_, (g.symm (Sum.inr (u.symm PUnit.unit))).2⟩, hY,
        ⟨e.trans ((gB.symm.sumCongr u.symm).trans g.symm)⟩⟩
    · rintro ⟨Z, -, hZ, ⟨e⟩⟩
      obtain ⟨gZ⟩ := eq_n₀c_iff_equiv.1 (hZ.symm.trans hY)
      exact ⟨inferInstance, A, rfl, ⟨e.trans (gZ.trans (g.trans ((Equiv.refl _).sumCongr u)))⟩⟩
  have hdesc : Desc (nuP (n₀c A +ᶜ (one : Set (Set β)) : Set (Set W))) P (fun w => v = w) :=
    desc_nuP_iff.2 ⟨b, hb, v, hv, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [desc_unique hb, desc_of_eq hdesc, key, hv]
  · obtain ⟨Y', hY', ⟨eY'⟩⟩ := cardAdd_one_eq (T := W') o (adeq_emb_unit hW' A o)
    rw [hY', sub_one_eq eY', n₀c_eq_ncT]

/-- ✱121·641. \[\begin{align}\vdash \colon\ldotp P\in \text{Cls}\rightarrow 1.P_{\text{po}}\,\unicode{x2abd}\, J.\nu \in &\text{NC induct}-\iota ʻ0.\supset :\\ &\text{Nc}ʻ\overleftarrow{P}_{*}ʻBʻP\geq \nu .\equiv .\text{E}!\nu _{P}\\ &[*121·64·63·32]\end{align}\]

The side `Nc'P⃖_*'B'P` of `≥` is `N₀c'P⃖_*'B'P` (normal adjustment); `ν` has its own type `β`.

**Status.** proved (reading): the side `Nc'P⃖_*'B'P` of `≥` is `N₀c'P⃖_*'B'P` (the analogue of
✱117·02·03 for `≥`, PM's note after ✱117·06, normal adjustment). -/
theorem pm121_641 {α β : Type*} {P : α → α → Prop} {ν : Set (Set β)} :
    ((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ ν ∈ NCinduct \ ι zero) →
      (Desc Beg P (fun b => n₀c (rels (anc P) b) ≥ᶜ ν) ↔ EDesc (nuP ν) P) := by
  rintro ⟨⟨hP, hJ⟩, hν⟩
  have hU : P ∈ arrow one Cls ∪ arrow Cls one := Or.inr hP
  rcases NCinduct_ne_zero_cases hν with rfl | ⟨A, hA, hA0, rfl⟩
  · constructor
    · rintro ⟨b, -, hge⟩
      obtain ⟨A, B, ⟨-, hB⟩, -⟩ := cardGe_iff.1 hge
      exact absurd hB.symm (n₀c_ne_empty B)
    · intro h
      obtain ⟨b, -, v, hv, -⟩ := desc_nuP_iff.1 (edesc_iff_desc.1 h)
      obtain ⟨X, -, hX, -⟩ := Pnu_sub_one.1 ((hv v).2 rfl)
      exact absurd hX.symm (n₀c_ne_empty X)
  have : Finite ↥A := hA.to_subtype
  have : Nonempty ↥A := hA0.to_subtype
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥A = k + 1 := Nat.exists_eq_succ_of_ne_zero Nat.card_pos.ne'
  constructor
  · rintro ⟨b, hb, hge⟩
    obtain ⟨gA⟩ := cardGe_n₀c.1 hge
    have hex : ∃ v, pwr P k b v := by
      by_contra hno
      push Not at hno
      obtain ⟨F⟩ := emb_fin_of_no_pwr (arrow_cnv.1 hP) (x := b) (j := k)
        (fun z hz => hno z (pwr_cnv.1 hz))
      have hpost : refs (anc P˘) b = rels (anc P) b := Set.ext fun w => anc_cnv
      rw [hpost] at F
      have := Finite.card_le_of_embedding (gA.trans F)
      rw [Nat.card_fin, hk] at this
      omega
    obtain ⟨v, hv⟩ := hex
    rw [edesc_iff_desc, desc_nuP_iff_mo hP hJ]
    exact ⟨b, hb, v, (Pnu_sub_one_n₀c hU hJ hA hk).2 hv, trivial⟩
  · intro h
    obtain ⟨b, hb, v, hv, -⟩ := (desc_nuP_iff_mo hP hJ).1 (edesc_iff_desc.1 h)
    have hpw := (Pnu_sub_one_n₀c hU hJ hA hk).1 hv
    obtain ⟨e⟩ := (itv_equiv_iff hU hJ (X := ↥A)).2 ⟨k, hk, hpw⟩
    refine (desc_unique hb).2 (cardGe_n₀c.2 ⟨e.symm.toEmbedding.trans ?_⟩)
    exact ⟨fun w => ⟨w.1, w.2.1⟩, fun w1 w2 h => Subtype.ext (congrArg Subtype.val h :)⟩

/-- ✱121·65. \(\vdash :P\in \text{Cls}\rightarrow 1.P_{\text{po}}\,\unicode{x2abd}\, J.\mu \neq 0.\text{E}!(\mu +_{c}\nu )_{P}.\supset .\mu _{P}P_{\nu }(\mu +_{c}\nu )_{P}\)

The real variables `μ`, `ν` have independent types `β₁`, `β₂` (the latter with a member, for the
`1` of `P_ν`); the subscript `μ +_c ν` (an argument of `−_c`, ✱121·04) is in an adequate type `W`
(IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of the
subscript `μ +_c ν` is adequate; PM assumes every type has a member (Introduction, Ch. I):
`[Nonempty β₂]` for the type of the `1` of `P_ν`. -/
theorem pm121_65 {α β₁ β₂ W : Type*} [Nonempty β₂] {P : α → α → Prop} {μ : Set (Set β₁)}
    {ν : Set (Set β₂)} :
    AdeqAdd W μ ν →
    (((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ μ ≠ zero) ∧
        EDesc (nuP (μ +ᶜ ν : Set (Set W))) P) →
      Desc (nuP μ) P (fun a => Desc (nuP (μ +ᶜ ν : Set (Set W))) P (fun c => Pnu P ν a c)) := by
  rintro - ⟨⟨⟨hP, hJ⟩, hμ⟩, h⟩
  have hU : P ∈ arrow one Cls ∪ arrow Cls one := Or.inr hP
  obtain ⟨b, hb, c, hc, -⟩ := (desc_nuP_iff_mo hP hJ).1 (edesc_iff_desc.1 h)
  have hdc : Desc (nuP (μ +ᶜ ν : Set (Set W))) P (fun w => c = w) :=
    (desc_nuP_iff_mo hP hJ).2 ⟨b, hb, c, hc, rfl⟩
  obtain ⟨Y, hY0, hY, ⟨e⟩⟩ := Pnu_sub_one.1 hc
  have hYm : Y ∈ (μ +ᶜ ν : Set (Set W)) := hY ▸ self_mem_n₀c Y
  obtain ⟨A, B, ⟨rfl, rfl⟩, ⟨g⟩⟩ := mem_cardAdd'.1 hYm
  have hf : (itvCC P b c).Finite := mem_ClsInduct.1 (pm121_45 hP)
  have : Finite ↥(itvCC P b c) := hf.to_subtype
  have : Finite ↥Y := Finite.of_equiv _ e
  have : Finite ↥A := finite_left_of_equiv g
  have : Finite ↥B := finite_right_of_equiv g
  have hA0 : A.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hμ zero_eq_n₀c_empty.symm
  have : Nonempty ↥A := hA0.to_subtype
  have : Nonempty ↥Y := hY0.to_subtype
  obtain ⟨m, hm⟩ : ∃ m, Nat.card ↥A = m + 1 := Nat.exists_eq_succ_of_ne_zero Nat.card_pos.ne'
  obtain ⟨j, hj, hpw⟩ := (itv_equiv_iff hU hJ (X := ↥Y)).1 ⟨e⟩
  rw [Nat.card_congr g, Nat.card_sum, hm] at hj
  have hpw' : pwr P (m + Nat.card ↥B) b c := by rwa [show m + Nat.card ↥B = j by omega]
  obtain ⟨a, hba, hac⟩ := pwr_add.1 hpw'
  refine (desc_nuP_iff_mo hP hJ).2 ⟨b, hb, a, (Pnu_sub_one_n₀c hU hJ (Set.toFinite A) hm).2 hba,
    (desc_of_eq hdc).2 ?_⟩
  rw [Pnu_n₀c_eq hU hJ (Set.toFinite B)]
  exact hac

/-- ✱121·66. \(\vdash :P\in \text{Cls}\rightarrow 1.P_{\text{po}}\,\unicode{x2abd}\, J.\text{Nc}ʻP(BʻP\vdash\dashv x)>\nu .\supset .x\in \text{ᗡ}ʻP_{\nu }\)

The side `Nc'P(B'P⊢⊣x)` of `>` is `N₀c'P(B'P⊢⊣x)` (normal adjustment); the type `β` of `ν` has a
member (for the `1` of `P_ν`; in an empty type `P₀ = Λ̇`).

**Status.** proved (reading): the side `Nc'P(B'P⊢⊣x)` of `>` is `N₀c'P(B'P⊢⊣x)` (✱117·02·03,
normal adjustment); PM assumes every type has a member (Introduction, Ch. I): `[Nonempty β]` for
the type of the `1` of `P_ν`. -/
theorem pm121_66 {α β : Type*} [Nonempty β] {P : α → α → Prop} {ν : Set (Set β)} {x : α} :
    ((P ∈ arrow Cls one ∧ po P ⪽ J) ∧ Desc Beg P (fun b => n₀c (itvCC P b x) >ᶜ ν)) →
      x ∈ codom (Pnu P ν) := by
  rintro ⟨⟨hP, hJ⟩, b, -, hgt⟩
  have hU : P ∈ arrow one Cls ∪ arrow Cls one := Or.inr hP
  obtain ⟨A', B, ⟨hA', rfl⟩, ⟨f⟩, hn⟩ := cardGt_iff.1 hgt
  obtain ⟨gA⟩ := eq_n₀c_iff_equiv.1 hA'
  have hf : (itvCC P b x).Finite := mem_ClsInduct.1 (pm121_45 hP)
  have : Finite ↥(itvCC P b x) := hf.to_subtype
  have hne : (itvCC P b x).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    apply hn
    have : IsEmpty ↥(itvCC P b x) := by rw [he]; infer_instance
    exact ⟨gA.symm.toEmbedding.trans (Function.Embedding.ofIsEmpty)⟩
  obtain ⟨w, hw⟩ := hne
  obtain ⟨k, hk⟩ := anc_pwr (anc_trans hw.1 hw.2)
  obtain ⟨-, hc⟩ := pwr_card' hU hJ hk
  have : Finite ↥B := Finite.of_injective _ (f.trans gA.symm.toEmbedding).injective
  have hBk : Nat.card ↥B ≤ k := by
    by_contra hlt
    apply hn
    obtain ⟨g⟩ := emb_of_finite_card_le (X := ↥(itvCC P b x)) (Y := ↥B)
      (Or.inr (by rw [Nat.card_coe_set_eq, hc]; omega))
    exact ⟨gA.symm.toEmbedding.trans g⟩
  have hk' : pwr P (k - Nat.card ↥B + Nat.card ↥B) b x := by rwa [Nat.sub_add_cancel hBk]
  obtain ⟨a, -, hax⟩ := pwr_add.1 hk'
  exact ⟨a, by rw [Pnu_n₀c_eq hU hJ (Set.toFinite B)]; exact hax⟩

/-- ✱121·7. \(\vdash :R\in 1\rightarrow 1.aBR.aR_{*}x.\supset .\overrightarrow{R}_{*}ʻx=R(a\vdash\dashv x).\overrightarrow{R}_{*}ʻx\in \text{Cls induct}\)

`aBR` is `Beg a R`. -/
theorem pm121_7 {α : Type*} {R : α → α → Prop} {a x : α} :
    ((R ∈ arrow one one ∧ Beg a R) ∧ anc R a x) →
      (refs (anc R) x = itvCC R a x ∧ refs (anc R) x ∈ ClsInduct) := by
  rintro ⟨⟨hR, ha⟩, hax⟩
  have hR1 : R ∈ arrow one Cls := mem_arrow_one_Cls.2 (mem_arrow_one_one.1 hR).1
  have hP' : R˘ ∈ arrow Cls one := (arrow_cnv (P := R˘)).2 hR1
  have e : refs (anc R) x = itvCC R a x := by
    ext w
    refine ⟨fun (hw : anc R w x) => ⟨?_, hw⟩, fun hw => hw.2⟩
    have hxa : anc R˘ x a := anc_cnv.2 hax
    have hxw : anc R˘ x w := anc_cnv.2 hw
    rcases rtg_comparable hP' (anc_iff_reflTransGen.1 hxa).2 (anc_iff_reflTransGen.1 hxw).2
      with h | h
    · have hwa : anc R w a := anc_cnv.1 (anc_iff_reflTransGen.2 ⟨fld_of_anc_right hxa, h⟩)
      rcases anc_iff_po.1 hwa with ⟨rfl, -⟩ | hp
      · exact anc_refl (fld_of_anc_left hax)
      · exact absurd (dom_codom_of_po hp).2 ha.2
    · exact anc_cnv.1 (anc_iff_reflTransGen.2 ⟨fld_of_anc_right hxw, h⟩)
  refine ⟨e, ?_⟩
  rw [e]
  exact pm121_46 hR1

/-- ✱121·71. \[\begin{align}\vdash \colon\ldotp R\in 1\rightarrow 1:x\in sʻ\text{gen}ʻR.\lor.(\exists y).y\in &\overleftrightarrow{R}_{*}ʻx.yR_{\text{po}}y:\supset .\\ &\overrightarrow{R}_{*}ʻx\in \text{Cls induct}\end{align}\] -/
theorem pm121_71 {α : Type*} {R : α → α → Prop} {x : α} :
    (R ∈ arrow one one ∧ (x ∈ sumCls (gen R) ∨ ∃ y, y ∈ refsRels (anc R) x ∧ po R y y)) →
      refs (anc R) x ∈ ClsInduct := by
  rintro ⟨hR, hx | ⟨y, hy, hyy⟩⟩
  · obtain ⟨a, k, ha, hk⟩ := gen_beg hx
    exact (pm121_7 ⟨⟨hR, ha⟩, pwr_anc hk⟩).2
  · obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
    have hR1 : R ∈ arrow one Cls := mem_arrow_one_Cls.2 h1
    have hR2 : R ∈ arrow Cls one := mem_arrow_Cls_one.2 h2
    have hR1' : R˘ ∈ arrow Cls one := (arrow_cnv (P := R˘)).2 hR1
    rw [po_iff_transGen] at hyy
    have hyx : Relation.ReflTransGen R y x ∧ Relation.ReflTransGen R x y := by
      rcases hy with (hy | ⟨hy, -⟩) | hy
      · have h := (anc_iff_reflTransGen.1 hy).2
        exact ⟨h, rtg_back_of_cycle hR2 hyy h⟩
      · rw [mem_unitCls.1 hy]; exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
      · have h := (anc_iff_reflTransGen.1 hy).2
        have h' := rtg_back_of_cycle hR1' (Relation.transGen_swap.2 hyy)
          (Relation.reflTransGen_swap.2 h)
        exact ⟨Relation.reflTransGen_swap.1 h', h⟩
    have hxx : po R x x := po_iff_transGen.2
      (Relation.TransGen.trans_left (Relation.TransGen.trans_right hyx.2 hyy) hyx.1)
    rw [← pm121_381 ⟨hR1, hxx⟩]
    exact pm121_46 hR1

/-- ✱121·72. \[\begin{align}&\vdash :R\in 1\rightarrow 1.\overrightarrow{R}_{*}ʻx{\sim}\in \text{Cls induct}.\supset .x\in pʻ\text{ᗡ}ʻʻ\text{Pot}ʻR.R_{\text{po}}\unicode{x0294f}\overleftrightarrow{R}_{*}ʻx\,\unicode{x2abd}\, J\\ &[*121·71.\text{Transp}.*93·271.*120·212.*50·24]\end{align}\]

`R_po ⥏ R⃡_*'x` is `po R ⥏ refsRels (anc R) x`. -/
theorem pm121_72 {α : Type*} {R : α → α → Prop} {x : α} :
    (R ∈ arrow one one ∧ refs (anc R) x ∉ ClsInduct) →
      (x ∈ prodCls (Dcnv ʻʻ pot R) ∧ po R ⥏ refsRels (anc R) x ⪽ J) := by
  rintro ⟨hR, hn⟩
  have hR1 : R ∈ arrow one Cls := mem_arrow_one_Cls.2 (mem_arrow_one_one.1 hR).1
  refine ⟨?_, ?_⟩
  · rintro C ⟨S, hS, hCS⟩
    have hC : C = codom S := hCS
    obtain ⟨k, rfl⟩ := mem_pot_iff'.1 hS
    subst hC
    by_contra hno
    apply hn
    obtain ⟨F⟩ := emb_fin_of_no_pwr hR1 (x := x) (j := k + 1) (fun z hz => hno ⟨z, hz⟩)
    exact mem_ClsInduct.2 (Set.finite_coe_iff.1 (Finite.of_injective F F.injective))
  · rintro u w ⟨⟨hu, huw⟩, -⟩ e
    rw [I_apply] at e
    subst e
    exact hn (pm121_71 ⟨hR, Or.inr ⟨u, hu, huw⟩⟩)

end PrincipiaMathematica
