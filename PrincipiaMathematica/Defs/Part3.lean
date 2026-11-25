import PrincipiaMathematica.Defs.Part2
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Part III (Cardinal arithmetic): the definitions

Every definition (Df, and the temporary definitions Dft of ✱116 and ✱123) of ✱100–✱126, in PM's
order, in the format of `Defs/Part1.lean`: each entry is headed `**✱N·M Df.**` with the formula as
printed (MathJax TeX, from `data/principia.json`), says how it is read in Lean and gives the
*target statement* of `pmN_M` (status `definition` unless said otherwise; every target below has
been checked to elaborate and to hold by the indicated proof). Then come the *adequacy*
predicates of the Prefatory Statement (II), the sanity lemmas the Section files use
(`Nc'α` and similarity, `N₀c'α`, the arithmetical class-sum, `N₀c'α +_c N₀c'β = Nc'(α + β)`,
`0`, `1`, `μ +_c 1`, inductive cardinals and classes are the finite ones, `Infin ax` is
`Infinite α`, …), and worked examples of the type conventions: normal adjustment ✱110·3; IIT
✱110·56 (with a proof that IIT cannot be dropped) and ✱110·643; AT ✱103·16 and ✱117·108;
Infin T ✱123·43 (with a proof that it cannot be dropped); `Infin ax` ✱120·3·301, ✱123·18,
✱125·13. All are proved except the statements of ✱123·18 and ✱123·43. The worked examples
✱100·01·02·1·2·3·35·4·42·511 (✱100·35 with and without AT; IT with argumental occurrences in
✱100·511) are finished declarations in `Part3/SectionA.lean`.

The Dfs ✱106·012·02·021·03·041 are printed in the e-text as propositions (with "Df etc."), and
the Dfts ✱116·529 and ✱123·02 likewise; they are Dfs all the same and are given here.

**Read the Prefatory Statement of Symbolic Conventions (Vol. II) before stating anything.** Its
conventions are part of the meaning of PM's enunciations; the rules below say how each becomes
Lean.

## Encoding decisions: types (in addition to Basic §1–§10, Defs/Part2)

1. *Actual types are type parameters.* A typically ambiguous formal number has its actual type
   (the type of the classes that are its members) as a type parameter:
   * `Nc'α` is `nc γ A : Set (Set γ)`, the classes of `γ`-things similar to `A : Set β` —
     **the target type `γ` is an explicit argument** (PM's `Nc(ξ)'α` for `ξ : Set γ`, ✱65·04;
     `Nc(α)'β` is `nc α' B` for `α : Set α'`). Likewise `ΣNc'κ` is `sigmaNc γ K`, `ΠNc'κ` is
     `piNc γ K`. The relation `Nc` (✱100·01) has both types implicit.
   * The arithmetical formal numbers `μ +_c ν`, `μ ×_c ν`, `μ^ν`, `μ −_c ν` (notations `μ +ᶜ ν`,
     `μ ×ᶜ ν`, `μ ^ᶜ ν`, `μ -ᶜ ν`) and `sm''μ` (`sm ʻʻ μ`) have their actual type as an
     *implicit* argument, fixed by the context (an equation, `ξ ∈ …`, `∩ t'…`) or by an ascription
     `(μ +ᶜ ν : Set (Set γ))`. PM's typically definite forms `(μ +_c ν)_ξ`, `sm_ξ''μ`,
     `Nc(ξ)'α` (✱65) are the ascribed forms; `σ_ξ` may also be written literally `clsT σ ξ`
     (`clsT_eq` removes it).
   * The homogeneous, ascending, descending and relational cardinals (`N₀c'α`, `N¹c'α`, `N₁c'α`,
     `N₀₀c'α`, …, `μ^{(1)}`, `μ_{(1)}`, …) are typically definite: `n₀c A`, `n1c A`, `n₁c A`, …,
     `up1 μ`, `down1 μ`, …, whose types are fixed by the definition.
2. *Assignment order* (Prefatory Statement, I): the types of the real variables are assigned
   first (type parameters of the theorem, as usual), then those of the constant symbols. Every
   typically ambiguous constant (`NC`, `NC induct`, `0`, `1`, `2`, `sm`, `Nc`, a formal number)
   whose type is not fixed by significance gets its own type parameter of the theorem (the form
   is asserted for every determination). Never identify two types that neither significance nor
   a convention identifies.
3. *`NC` and its relatives.* `NC = D'Nc` leaves the type of the *converse domain* of `Nc`
   undetermined (Summary of Section A: `NC(α)` is "not sufficiently definite"), so `NC β` takes it
   as an explicit argument: `μ ∈ NC β ↔ ∃ A : Set β, μ = nc γ A` (`mem_NC`). PM's `NC^β(α)`
   (✱102·01) is `NCT A B`, equal to `NC β'` (`NCT_eq_NC`). "**`μ, ν ∈ NC` does not identify the
   types of `μ` and `ν`**" (Prefatory Statement, V, "Ambiguity of NC"): write
   `μ ∈ NC β ∧ ν ∈ NC β'` with independent `β`, `β'` (and independent member types unless
   significance, e.g. `μ ∩ ν`, identifies them). The same for `N₀C`, `NC induct`, `NC ind`.
4. *Convention IT* (Prefatory Statement, IV): all logical occurrences of the same formal number
   are in one type; argumental occurrences (`sm''σ`) are bound to logical and attributive ones
   (`ξ ∈ σ`); without argumental occurrences, equational occurrences are bound to logical ones.
   Realize "bound" by using **one** type parameter for the bound occurrences. Occurrences that IT
   does not bind get separate parameters: in particular, when there *are* argumental occurrences,
   the equational ones are not bound to the logical ones (✱100·511 `∃!Nc'β . ⊃ . sm''Nc'β =
   Nc'β` is `(nc γ B).Nonempty → (sm ʻʻ nc γ B : Set (Set δ)) = nc δ B`: the logical and the
   argumental `Nc'β` in `γ`, the equation in `δ`; worked example `pm100_511` in
   `Part3/SectionA.lean`). Arithmetical occurrences are never bound by IT (they are adjusted by
   ✱110·03·04 etc. and IIT). (Worked example: ✱100·35 in `Part3/SectionA.lean`:
   `∃!Nc'α ∨ ∃!Nc'β : ⊃ : Nc'α = Nc'β ≡ α ∈ Nc'β ≡ …` is `(nc γ A).Nonempty ∨ (nc γ B).Nonempty →
   (((nc γ A = nc γ B ↔ A ∈ nc α B) ∧ …`, PM's own reading `Nc(ξ)'α … α ∈ Nc(α)'β`.)
5. *Normal adjustment* (✱110·03·04, ✱113·04·05, ✱116·03·04, ✱117·02·03, ✱119·02·03,
   ✱124·021): `Nc'α` occurring as an argument of `+_c`, `×_c`, `^`, `−_c`, as a side of `>`, `<`,
   `≥`, `≤`, or in `Nc'ρ ∈ NC refl`, **is written `n₀c A`** (these Dfs are translation rules).
   So ✱110·3 `Nc'α +_c Nc'β = N₀c'α +_c N₀c'β = Nc'(α + β)` is
   `(n₀c A +ᶜ n₀c B : Set (Set γ)) = n₀c A +ᶜ n₀c B ∧ (n₀c A +ᶜ n₀c B : Set (Set γ)) = nc γ (A +ₐ B)`
   (worked example below).
6. *Convention IIT*: any *other* formal number `σ` occurring where `Nc'α` would have to be
   adequate (an arithmetical component of an arithmetical formal number, a side of an arithmetical
   inequality, e.g. the inner `ν +_c ϖ` of `μ +_c (ν +_c ϖ)`) gets **its own type parameter `W`
   and the hypothesis that `W` is adequate for `σ`**: `AdeqAdd W ν ϖ`, `AdeqMul W ν ϖ`,
   `AdeqExp W ν ϖ`, `AdeqSub W ν ϖ`, `AdeqNc W A`, `AdeqSigmaNc W K`, `AdeqPiNc W K`
   (the definitions (i)–(ii) of the Prefatory Statement, II, below); for a constant formal number
   `σ` (`1`, `2`, `1 +_c 2`, …) the hypothesis is `(σ : Set (Set W)).Nonempty`, where an `ℵ₀` in
   `σ` is first replaced by `N₀c't₁'ℵ₀`, i.e. `n₀c (typ₁ (aleph0 : Set (Set X)))` ((iii));
   for `1` this is equivalent to `[Nonempty W]`
   (`one_eq_n₀c_singleton`), which may be written instead, and for `0` it is provable, so it is
   omitted. Status `proved (reading): convention IIT (Prefatory Statement, IV)`. (Worked
   examples, proved below: ✱110·56, with a proof that the hypotheses cannot be dropped, and
   ✱110·643.) IIT does not touch the argument of an argumental formal number (`ν +_c ρ` in
   `μ +_c sm''(ν +_c ρ)`): IT binds it to the logical and attributive occurrences of the same
   formal number; the argumental formal number `sm''σ` itself, in an arithmetical position, gets
   `AdeqSm W …`. IIT concerns only types *left ambiguous*: a type PM indicates expressly
   (`(μ +_c ν)_ξ`, `sm_ξ''μ`, `Nc(ξ)'α`, the uniform formal numbers of ✱118) is an ascription to
   the type of `ξ` with **no** adequacy hypothesis (✱118·25 `(μ +_c ν +_c ϖ)_ξ =
   {(μ +_c ν)_ξ +_c ϖ}_ξ` has an IIT parameter only for the unsubscripted inner `μ +_c ν`). Real
   variables get no adequacy hypothesis (their types are assigned first, and are independent:
   in ✱110·56 `μ`, `ν`, `ϖ` have three types). Since the inner types are parameters, a nested
   arithmetical term always needs ascriptions: ✱110·643 `1 +_c 1 = 2` is
   `((one : Set (Set W₁)) +ᶜ (one : Set (Set W₂)) : Set (Set γ)) = two` with `[Nonempty W₁]`,
   `[Nonempty W₂]` (the two `1`s are arithmetical occurrences, which IT does not bind).
7. *Convention AT* (Prefatory Statement, VI): in the propositions where PM applies AT (✱103·16,
   ✱110·71·72, all of ✱117, and, with the Rule of Indefinite Numbers, ✱126) every *equation
   between pure arithmetical formal numbers* is arithmetical: its type parameter gets the adequacy hypotheses of both sides (e.g.
   `AdeqNc γ A`, `AdeqNc γ B` for `Nc'α = Nc'β`); status `proved (reading): convention AT,
   Prefatory Statement`. (PM's "holds in any type" is the universal quantification over the type
   parameter that a theorem with a type parameter already expresses.) AT is *not* applied where
   PM does not apply it: ✱100·35 is stated with its printed hypothesis (worked example
   `pm100_35`; its AT form is `pm100_35_aux_AT`). Worked examples below: ✱103·16 (an equation
   with a typically definite side) and ✱117·108 (an equation beside arithmetical inequalities,
   whose sides are normally adjusted). Only the *equations* get AT hypotheses; when an apparent
   variable occurs in a side, see "Adequate actual types" below.
8. *Convention Infin T*: when the hypothesis of a proposition implies that some type has every
   inductive cardinal (`Infin ax`, `∃!Prog`, `∃!ℵ₀`, `R ∈ Prog`, `α ∈ ℵ₀`), an occurrence of
   `NC induct` whose type is otherwise undetermined is taken at a type parameter `X` with the
   hypothesis `InfinAx X`; status `proved (reading): convention Infin T`. The convention applies
   to every occurrence of `NC induct` in such a proposition except where PM indicates its type
   expressly (`NC induct ∩ t³'x`, `N_ξC induct`); when significance ties the occurrence to a
   real variable (✱123·3: `ᗡ'S = NC induct`, the type of the relata of `S`), the hypothesis is
   on that type, and the status says so. Worked example (statement below, with a proof that the
   hypothesis is needed): ✱123·43 `∃!ℵ₀ . ⊃ : ν ∈ NC induct . ⊃_ν . ℵ₀ > ν` is
   `InfinAx X → (aleph0 : Set (Set α)).Nonempty → ∀ ν : Set (Set X), ν ∈ NCinduct →
   (aleph0 : Set (Set α)) >ᶜ ν`.
   `Infin ax` itself is typically ambiguous: `InfinAx X` at the type PM's enunciation determines
   (✱120·04 `Infin ax(x)` is `InfinAxAt x`, at the type of `x`, Basic §10); in ✱120·3, ✱125·13
   (worked examples below) `Infin ax` and `NC induct` are in one type, which is the theorem's
   type parameter, and Infin T adds nothing.
9. *Rule of Indefinite Numbers* (✱126, Prefatory Statement, VII): a symbol for a particular
   inductive number (`1`, `2`, …) or a member of `NC ind` is taken in a type where it is not `Λ`:
   the hypothesis `(σ : Set (Set W)).Nonempty`; status `proved (reading): Rule of Indefinite
   Numbers (✱126)`.
10. *`+_c 1` and other constants as arguments.* When the type of a constant argument (`1` in
   `ν +_c 1`, `ν −_c 1`, ✱120·01, ✱121·02·04, ✱123·02) is fixed by nothing, take it in the type of
   the other argument (`(one : Set (Set β))` for `ν : Set (Set β)`): this is PM's "standard
   arithmetical adjustment … making every use of `sm` homogeneous" (Prefatory Statement, II), and
   the value does not depend on the choice as long as `1` exists (✱110·25). The relation `+_c 1`
   (✱120·01) is `plusC1`, homogeneous. Where a proposition needs it, the type of a cardinal
   apparent variable that nothing determines (`ν` in `finid'P`, ✱121·03) is an explicit
   argument (`finid β P`).
11. *Empty types.* PM assumes every type has members (Basic §3); in Lean `one : Set (Set α)` is
   `Λ` when `α` is empty. Add `[Nonempty α]` exactly where a proposition fails for an empty type.

## Encoding decisions: other

* *Descriptive functions* (Basic §5, Defs/Part2): every relation of this Part whose descriptive
  function always exists is `graph` of its value function: `Nc`, `N₀c`, `N1c`, …, `ClsSigma`,
  `SigmaNc`, `PiNc`, `ProdK`, `Spec`; in formulas `Nc'α` is `nc γ A`, `N₀c'α` is `n₀c A`, etc.
  Rewrite descriptions with `desc_Nc`, `desc_N₀c`, `desc_relT2_Nc`, …, or `(desc_graph _ _ _)`.
  `Crp(S)'β` (✱111·02) and `ν_P` (✱121·04) contain descriptions that may fail to exist: they are
  relations (`Crp S`, `nuP ν`) with `desc_Crp`, `desc_nuP`. A Df `X = D'Y` (✱100·02, ✱102·01,
  ✱103·02, ✱104·02·021, ✱105·02·021, ✱106·03) keeps the description in its target (Basic §5).
* *Formal numbers in definitions.* The definiens of ✱119·01 (`Nc'ξ +_c ν`) is read by ✱110·03
  (`n₀c ξ +ᶜ ν`), and its logical occurrence is bound to the equational one by IT.
* *Names that shadow.* Do not bind variables named `D`, `I`, `J`, `SM`, `fin`, `spec`, `one`,
  `zero`, `two`, … . The letters `Σ`, `Π`, `λ` are not identifiers in Lean: `Σ'κ` is `clsSigma K`.

## Symbol table: PM → Lean (extends Basic §7 and Defs/Part2)

| PM | Df | Lean |
|----|----|------|
| `Nc`, `Nc'α`, `Nc(ξ)'α` | ✱100·01 | `Nc`, `nc γ A` (`ξ : Set γ`) |
| `NC` | ✱100·02 | `NC β` (`μ ∈ NC β ↔ ∃ A : Set β, μ = nc γ A`) |
| `NC^β(α)` | ✱102·01 | `NCT A B` |
| `N₀c'α`, `N₀c`, `N₀C` | ✱103·01·02 | `n₀c A`, `N₀c`, `N₀C` |
| `N¹c'α`, `N²c'α`, `N¹C`, `N²C` | ✱104·01–·021 | `n1c A`, `n2c A`, `N1C`, `N2C` (relations `N1c`, `N2c`) |
| `μ^{(1)}`, `μ^{(2)}` | ✱104·03·031 | `up1 μ`, `up2 μ` |
| `N₁c'α`, `N₂c'α`, `N₁C`, `N₂C` | ✱105·01–·021 | `n₁c A`, `n₂c A`, `N₁C`, `N₂C` (relations `N₁c`, `N₂c`) |
| `μ_{(1)}`, `μ_{(2)}` | ✱105·03·031 | `down1 μ`, `down2 μ` |
| `N₀₀c'α`, `N¹¹c'α`, `N₀₁c'α`, `N₀¹c'α`, `¹N₀c'α` | ✱106·01–·021 | `n₀₀c A`, `n11c A`, `n₀₁c A`, `n₀1c A`, `n1₀c A` |
| `N₀₀C`, `μ_{(00)}`, `μ^{(11)}` | ✱106·03·04·041 | `N₀₀C` (relation `N₀₀c`), `down00 μ`, `up11 μ` |
| `α + β` (class-sum) | ✱110·01 | `A +ₐ B` (`clsSum`) |
| `μ +_c ν` | ✱110·02 | `μ +ᶜ ν` (`cardAdd`) |
| `κ sm̄ sm̄ λ`, `Crp(S)`, `sm sm` | ✱111·01–·03 | `smsmbar K L`, `Crp S`, `smsm K L` |
| `Σ'κ`, `ΣNc'κ` | ✱112·01·02 | `clsSigma K`, `sigmaNc γ K` (relations `ClsSigma`, `SigmaNc`) |
| `α ↓,,` (relation), `β × α` | ✱38·03, ✱113·02 | `coupleImg A`, `B ×ₐ A` (`clsTimes B A`) |
| `μ ×_c ν` | ✱113·03 | `μ ×ᶜ ν` (`cardMul`) |
| `ΠNc'κ` | ✱114·01 | `piNc γ K` (relation `PiNc`) |
| `Prod'κ`, `Cls³ arithm` | ✱115·01·02 | `prodK K` (relation `ProdK`), `Cls3arithm` |
| `α exp β`, `μ^ν` | ✱116·01·02 | `clsExp A B`, `μ ^ᶜ ν` (`cardExp`) |
| `R†` (Dft ✱116) | ✱116·529 | `dagger R` |
| `μ > ν`, `μ < ν`, `μ ≥ ν`, `μ ≤ ν` | ✱117·01–·06 | `μ >ᶜ ν`, `μ <ᶜ ν`, `μ ≥ᶜ ν`, `μ ≤ᶜ ν` |
| `γ −_c ν`, `SM(δ, γ)` | ✱119·01·54 | `G -ᶜ ν` (`cardSub`), `SM d g` |
| `+_c 1` (relation), `NC induct`, `N_ξC induct` | ✱120·01·011 | `plusC1`, `NCinduct`, `NCinductAt ξ` |
| `Cls induct`, `Cls_ξ induct` | ✱120·02·021 | `ClsInduct`, `ClsInductAt ξ` |
| `Infin ax`, `Infin ax(x)` | ✱120·03·04 | `InfinAx α`, `InfinAxAt x` |
| `spec'β` | ✱120·43 | `spec B` (relation `Spec`) |
| `P(x–y)`, `P(x⊣y)`, `P(x⟝y)`, `P(x⊢⊣y)` | ✱121·01–·013 | `itvOO P x y`, `itvOC P x y`, `itvCO P x y`, `itvCC P x y` |
| `P_ν`, `finid'P`, `fin'P`, `ν_P` | ✱121·02–·04 | `Pnu P ν`, `finid β P`, `fin β P`, `Desc (nuP ν) P ψ` |
| `Prog`, `ℵ₀`, `N` (Dft ✱123–4) | ✱122·01, ✱123·01·02 | `Prog`, `aleph0`, `Nsucc` |
| `Cls refl`, `NC refl`, `NC mult` | ✱124·01–·03 | `ClsRefl`, `NCrefl`, `NCmult β` |
| `NC ind` | ✱126·01 | `NCind` |
| adequate actual type (Prefatory Statement, II) | — | `AdeqNc`, `AdeqSigmaNc`, `AdeqPiNc`, `AdeqSm`, `AdeqAdd`, `AdeqMul`, `AdeqExp`, `AdeqSub` |

Precedences: `+ₐ`, `+ᶜ`, `-ᶜ` 65 (left), `×ₐ`, `×ᶜ` 70 (left), `^ᶜ` 75 (right), `>ᶜ`, `<ᶜ`,
`≥ᶜ`, `≤ᶜ` 50; so `μ +ᶜ ν +ᶜ ϖ` is `(μ +ᶜ ν) +ᶜ ϖ` (✱110·561), `A ×ₐ B ×ₐ G` is `(A ×ₐ B) ×ₐ G`
(✱113·511), `μ ^ᶜ ν ×ᶜ μ ^ᶜ ϖ` is `(μ ^ᶜ ν) ×ᶜ (μ ^ᶜ ϖ)` (✱116·52), `sm ʻʻ μ +ᶜ ν` is
`(sm ʻʻ μ) +ᶜ ν` (✱110·25). PM always brackets mixed sums and products; write the same brackets,
and brackets for every exponent and every `∩ t'…` (`(μ +ᶜ ν) ∩ typ₀ μ`). Lean's `\` is not
associative: write `(NCinduct \ ι Λ) \ ι zero` (✱121·031). Never use Lean's `+`, `×`, `^`, `-`,
`<`, `>` on classes (`Set` has its own `<`: strict inclusion).
-/

namespace PrincipiaMathematica

universe u v w u' v' w'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

/-! ## Section A: definition and logical properties of cardinal numbers (✱100–✱106) -/

/-- `Nc'α` in the type `γ` (PM's `Nc(ξ)'α` with `ξ : Set γ`): the class of all classes of
`γ`-things similar to `A`, i.e. `sm⃗'α` (`β̂(β sm α)`, ✱100·1). The target type `γ` is explicit
(encoding decision 1). Value function of `Nc`. -/
def nc (γ : Type w) {β : Type v} (A : Set β) : Set (Set γ) := refs sm A

/-- **✱100·01 Df.** \(\text{Nc}=\overrightarrow{\text{ sm }} \quad\text{Df}\)

The relation of a cardinal number to any class of which it is the number. Typically ambiguous in
both its domain (cardinals whose members are classes of `γ`) and converse domain (classes of
`β`). `Nc'α` is `nc γ A` (`desc_Nc`). Target:
`pm100_01 : (Nc : Set (Set γ) → Set β → Prop) = Rfwd sm := rfl`. -/
def Nc {γ : Type w} {β : Type v} : Set (Set γ) → Set β → Prop := Rfwd sm

/-- **✱100·02 Df.** \(\text{NC}=\text{D}ʻ\text{Nc} \quad \text{Df}\)

The class of cardinal numbers (whose members are classes of `γ`) of classes of `β`; the type `β`
of the converse domain of `Nc`, which PM leaves ambiguous, is the explicit argument (encoding
decision 3). `mem_NC : μ ∈ NC β ↔ ∃ A : Set β, μ = nc γ A`. The definiens is the descriptive
function `D'Nc`, so the target keeps it (Basic §5):
`pm100_02 : Desc D (Nc : Set (Set γ) → Set β → Prop) (fun K => NC β = K) :=
(desc_graph _ _ _).2 rfl`. -/
def NC {γ : Type w} (β : Type v) : Set (Set (Set γ)) := dom (Nc : Set (Set γ) → Set β → Prop)

/-- **✱102·01 Df.** \(\text{NC}^\beta (\alpha ) = \text{D}ʻ\text{Nc}(\alpha _{\beta }) \quad\text{Df}\)

`NC^β(α)`: the cardinals of classes of the type of `β`, taken in the type of `α` (members are
classes of the type of `α`). `Nc(α_β)` is `Nc` with domain in `t²'α` and converse domain in
`t'β`, ✱65·11 `relT2T Nc A B`. `NCT A B = NC β` (`NCT_eq_NC`). Target (definiens a descriptive
function): `pm102_01 : Desc D (relT2T Nc A B) (fun K => NCT A B = K) := (desc_graph _ _ _).2 rfl`. -/
def NCT (A : Set α) (B : Set β) : Set (Set (Set α)) :=
  dom (relT2T (Nc : Set (Set α) → Set β → Prop) A B)

/-- **✱103·01 Df.** \(\text{N}_{0}\text{c}ʻ\alpha =\text{Nc}ʻ\alpha \cap tʻ\alpha \quad\text{Df}\)

The homogeneous cardinal of `α`: the classes of the type of `α` similar to `α` (`n₀c_eq_nc`:
it is `nc α A`). Value function of `N₀c`. Target: `pm103_01 : n₀c A = nc α A ∩ typ A := rfl`. -/
def n₀c (A : Set α) : Set (Set α) := nc α A ∩ typ A

/-- The relation `N₀c` of `N₀c'α` to `α` (✱103·01 defines its descriptive function). -/
def N₀c : Set (Set α) → Set α → Prop := graph n₀c

/-- **✱103·02 Df.** \(\text{N}_{0}\text{C}=\text{D}ʻ\text{N}_{0}\text{c} \quad\text{Df}\)

The homogeneous cardinals (of classes of `α`). `mem_N₀C : μ ∈ N₀C ↔ ∃ A, μ = n₀c A`. Target:
`pm103_02 : Desc D N₀c (fun K => (N₀C : Set (Set (Set α))) = K) := (desc_graph _ _ _).2 rfl`. -/
def N₀C : Set (Set (Set α)) := dom (N₀c : Set (Set α) → Set α → Prop)

/-- **✱104·01 Df.** \(\text{N}^{1}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻtʻ\alpha \quad\text{Df}\)

The ascending cardinal of `α` one type up: classes of classes of `α`-things similar to `α`.
Target: `pm104_01 : n1c A = nc (Set α) A ∩ typ (typ A) := rfl`. -/
def n1c (A : Set α) : Set (Set (Set α)) := nc (Set α) A ∩ typ (typ A)

/-- **✱104·011 Df.** \(\text{N}^{2}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻt^{2}ʻ\alpha \quad\text{Df}\)

Target: `pm104_011 : n2c A = nc (Set (Set α)) A ∩ typ (typ2 A) := rfl`. -/
def n2c (A : Set α) : Set (Set (Set (Set α))) := nc (Set (Set α)) A ∩ typ (typ2 A)

/-- The relation `N¹c` of `N¹c'α` to `α`. -/
def N1c : Set (Set (Set α)) → Set α → Prop := graph n1c

/-- The relation `N²c` of `N²c'α` to `α`. -/
def N2c : Set (Set (Set (Set α))) → Set α → Prop := graph n2c

/-- **✱104·02 Df.** \(\text{N}^{1}\text{C} = \text{D}ʻ\text{N}^{1}\text{c} \quad\text{Df}\)

Target: `pm104_02 : Desc D N1c (fun K => (N1C : Set (Set (Set (Set α)))) = K) :=
(desc_graph _ _ _).2 rfl`. -/
def N1C : Set (Set (Set (Set α))) := dom (N1c : Set (Set (Set α)) → Set α → Prop)

/-- **✱104·021 Df.** \(\text{N}^{2}\text{C} = \text{D}ʻ\text{N}^{2}\text{c} \quad\text{Df}\)

Target: `pm104_021 : Desc D N2c (fun K => (N2C : Set (Set (Set (Set (Set α))))) = K) :=
(desc_graph _ _ _).2 rfl`. -/
def N2C : Set (Set (Set (Set (Set α)))) := dom (N2c : Set (Set (Set (Set α))) → Set α → Prop)

/-- **✱104·03 Df.** \(\mu ^{(1)} = \text{ sm }ʻʻ\mu \cap tʻ\mu \quad\text{Df}\)

"The same cardinal in the next type": the classes of classes of `α`-things similar to some
member of `μ : Set (Set α)`. Target: `pm104_03 : up1 μ = sm ʻʻ μ ∩ typ μ := rfl`. -/
def up1 (μ : Set (Set α)) : Set (Set (Set α)) := sm ʻʻ μ ∩ typ μ

/-- **✱104·031 Df.** \(\mu ^{(2)} = \text{ sm }ʻʻ\mu \cap t^{2}ʻ\mu \quad\text{Df}\)

Target: `pm104_031 : up2 μ = sm ʻʻ μ ∩ typ2 μ := rfl`. -/
def up2 (μ : Set (Set α)) : Set (Set (Set (Set α))) := sm ʻʻ μ ∩ typ2 μ

/-- **✱105·01 Df.** \(\text{N}_{1}\text{c}ʻ\alpha =\text{Nc}ʻ\alpha \cap tʻt_{1}ʻ\alpha \quad\text{Df}\)

The descending cardinal of a class of classes `A : Set (Set α)`: the classes of `α`-things
similar to `A`. Target: `pm105_01 : n₁c A = nc α A ∩ typ (typ₁ A) := rfl`. -/
def n₁c (A : Set (Set α)) : Set (Set α) := nc α A ∩ typ (typ₁ A)

/-- **✱105·011 Df.** \(\text{N}_{2}\text{c}ʻ\alpha =\text{Nc}ʻ\alpha \cap tʻt_{2}ʻ\alpha \quad\text{Df}\)

Target: `pm105_011 : n₂c A = nc α A ∩ typ (typ₂ A) := rfl`. -/
def n₂c (A : Set (Set (Set α))) : Set (Set α) := nc α A ∩ typ (typ₂ A)

/-- The relation `N₁c` of `N₁c'α` to `α`. -/
def N₁c : Set (Set α) → Set (Set α) → Prop := graph n₁c

/-- The relation `N₂c` of `N₂c'α` to `α`. -/
def N₂c : Set (Set α) → Set (Set (Set α)) → Prop := graph n₂c

/-- **✱105·02 Df.** \(\text{N}_{1}\text{C}=\text{D}ʻ\text{N}_{1}\text{c} \quad\text{Df}\)

Target: `pm105_02 : Desc D N₁c (fun K => (N₁C : Set (Set (Set α))) = K) :=
(desc_graph _ _ _).2 rfl`. -/
def N₁C : Set (Set (Set α)) := dom (N₁c : Set (Set α) → Set (Set α) → Prop)

/-- **✱105·021 Df.** \(\text{N}_{2}\text{C}=\text{D}ʻ\text{N}_{2}\text{c} \quad\text{Df}\)

Target: `pm105_021 : Desc D N₂c (fun K => (N₂C : Set (Set (Set α))) = K) :=
(desc_graph _ _ _).2 rfl`. -/
def N₂C : Set (Set (Set α)) := dom (N₂c : Set (Set α) → Set (Set (Set α)) → Prop)

/-- **✱105·03 Df.** \(\mu _{(1)}=\text{ sm }ʻʻ\mu \cap t_{1}ʻ\mu \quad\text{Df}\)

The same cardinal one type down: `μ : Set (Set (Set α))`, `μ_{(1)} : Set (Set α)`. Target:
`pm105_03 : down1 μ = sm ʻʻ μ ∩ typ₁ μ := rfl`. -/
def down1 (μ : Set (Set (Set α))) : Set (Set α) := sm ʻʻ μ ∩ typ₁ μ

/-- **✱105·031 Df.** \(\mu _{(2)}=\text{ sm }ʻʻ\mu \cap t_{2}ʻ\mu \quad\text{Df}\)

Two types down: `μ : Set (Set (Set (Set α)))`. Target:
`pm105_031 : down2 μ = sm ʻʻ μ ∩ typ₂ μ := rfl`. -/
def down2 (μ : Set (Set (Set (Set α)))) : Set (Set α) := sm ʻʻ μ ∩ typ₂ μ

/-- **✱106·01 Df.** \(\text{N}_{00}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻt_{00}ʻ\alpha \quad\text{Df}\)

The relational cardinal: classes of relations between `α`-things similar to `α`. Target:
`pm106_01 : n₀₀c A = nc (α → α → Prop) A ∩ typ (typ₀₀ A) := rfl`. -/
def n₀₀c (A : Set α) : Set (Set (α → α → Prop)) := nc (α → α → Prop) A ∩ typ (typ₀₀ A)

/-- **✱106·011 Df.** \(\text{N}^{11}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻt^{11}ʻ\alpha \quad\text{Df}\)

Target: `pm106_011 : n11c A = nc (Set α → Set α → Prop) A ∩ typ (typ11 A) := rfl`. -/
def n11c (A : Set α) : Set (Set (Set α → Set α → Prop)) :=
  nc (Set α → Set α → Prop) A ∩ typ (typ11 A)

/-- **✱106·012 Df.** \(\text{N}_{01}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻt_{01}ʻ\alpha \quad\text{Df etc.}\)

(Printed in the e-text as a proposition.) `α` a class of classes. Target:
`pm106_012 : n₀₁c A = nc (Set α → α → Prop) A ∩ typ (typ₀₁ A) := rfl`. -/
def n₀₁c (A : Set (Set α)) : Set (Set (Set α → α → Prop)) :=
  nc (Set α → α → Prop) A ∩ typ (typ₀₁ A)

/-- **✱106·02 Df.** \(\text{N}^{1}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻt_{0}^{1}ʻ\alpha \quad\text{Df etc.}\)

(Printed in the e-text as a proposition, and with `N¹c` for `N₀¹c`: the definiendum is `N₀¹c'α`,
as `t₀¹` and ✱106·22 show; `N¹c` is ✱104·01. Mention the transcription error.) Target:
`pm106_02 : n₀1c A = nc (α → Set α → Prop) A ∩ typ (typ₀1 A) := rfl`. -/
def n₀1c (A : Set α) : Set (Set (α → Set α → Prop)) := nc (α → Set α → Prop) A ∩ typ (typ₀1 A)

/-- **✱106·021 Df.** \(^{1}\text{N}_{0}\text{c}ʻ\alpha = \text{Nc}ʻ\alpha \cap tʻ^{1}t_{0}ʻ\alpha \quad\text{Df etc.}\)

(Printed in the e-text as a proposition.) Target:
`pm106_021 : n1₀c A = nc (Set α → α → Prop) A ∩ typ (typ1₀ A) := rfl`. -/
def n1₀c (A : Set α) : Set (Set (Set α → α → Prop)) := nc (Set α → α → Prop) A ∩ typ (typ1₀ A)

/-- The relation `N₀₀c` of `N₀₀c'α` to `α`. -/
def N₀₀c : Set (Set (α → α → Prop)) → Set α → Prop := graph n₀₀c

/-- **✱106·03 Df.** \(\text{N}_{00}\text{C} = \text{D}ʻ\text{N}_{00}\text{c} \quad\text{Df etc.}\)

(Printed in the e-text as a proposition.) Target:
`pm106_03 : Desc D N₀₀c (fun K => (N₀₀C : Set (Set (Set (α → α → Prop)))) = K) :=
(desc_graph _ _ _).2 rfl`. -/
def N₀₀C : Set (Set (Set (α → α → Prop))) := dom (N₀₀c : Set (Set (α → α → Prop)) → Set α → Prop)

/-- **✱106·04 Df.** \(\mu _{(00)} = \text{ sm }ʻʻ\mu \cap tʻt_{00}ʻt_{1}ʻ\mu \quad\text{Df}\)

`μ : Set (Set α)`; `μ_{(00)}` is the "same" cardinal among classes of relations between
`α`-things. Target: `pm106_04 : down00 μ = sm ʻʻ μ ∩ typ (typ₀₀ (typ₁ μ)) := rfl`. -/
def down00 (μ : Set (Set α)) : Set (Set (α → α → Prop)) := sm ʻʻ μ ∩ typ (typ₀₀ (typ₁ μ))

/-- **✱106·041 Df.** \(\mu ^{(11)} = \text{ sm }ʻʻ\mu \cap tʻt^{11}ʻt_{1}ʻ\mu \quad\text{Df etc.}\)

(Printed in the e-text as a proposition.) Target:
`pm106_041 : up11 μ = sm ʻʻ μ ∩ typ (typ11 (typ₁ μ)) := rfl`. -/
def up11 (μ : Set (Set α)) : Set (Set (Set α → Set α → Prop)) := sm ʻʻ μ ∩ typ (typ11 (typ₁ μ))

/-! ## Section B: addition, multiplication and exponentiation (✱110–✱117) -/

/-- **✱110·01 Df.** \(\alpha +\beta = \downarrow (\Lambda \cap \beta )ʻʻ\iota ʻʻ\alpha \cup (\Lambda \cap \alpha ) \downarrow ʻʻ\iota ʻʻ\beta \quad\text{Df}\)

The arithmetical class-sum `α + β`, notation `A +ₐ B` (Lean's `+` is not used on classes): the
couples `ι'x ↓ Λ_β` (`x ∈ α`) and `Λ_α ↓ ι'y` (`y ∈ β`). `α`, `β` may be of different types.
`↓(Λ ∩ β)` is `coupleR (Λ ∩ B)`, `(Λ ∩ α)↓` is `coupleL (Λ ∩ A)`, `ι''α` is `iota ʻʻ A`.
`mem_clsSum`, `clsSumEquiv : ↥(A +ₐ B) ≃ A ⊕ B`. Target:
`pm110_01 : A +ₐ B = coupleR (Λ ∩ B) ʻʻ iota ʻʻ A ∪ coupleL (Λ ∩ A) ʻʻ iota ʻʻ B := rfl`. -/
def clsSum (A : Set α) (B : Set β) : Set (Set α → Set β → Prop) :=
  coupleR (Λ ∩ B) ʻʻ iota ʻʻ A ∪ coupleL (Λ ∩ A) ʻʻ iota ʻʻ B

@[inherit_doc] scoped infixl:65 " +ₐ " => clsSum

/-- **✱110·02 Df.** \(\mu +_{\text{c}}\nu = \hat{\xi} \{(\exists \alpha ,\beta ).\mu = \text{N}_{0}\text{c}ʻ\alpha .\nu = \text{N}_{0}\text{c}ʻ\beta .\xi \text{ sm }(\alpha +\beta )\} \quad\text{Df}\)

The arithmetical sum of two cardinals, `μ +ᶜ ν`; its actual type `γ` is implicit (fixed by the
context or an ascription; encoding decision 1). The definiens is a product of three
(left-bracketed). If `μ` or `ν` is not of the form `N₀c'α`, the sum is `Λ`. Target:
`pm110_02 : (μ +ᶜ ν : Set (Set γ)) =
{ξ | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm ξ (A +ₐ B)} := rfl`. -/
def cardAdd {α : Type u} {β : Type v} {γ : Type w} (μ : Set (Set α)) (ν : Set (Set β)) :
    Set (Set γ) :=
  {ξ | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm ξ (A +ₐ B)}

@[inherit_doc] scoped infixl:65 " +ᶜ " => cardAdd

/-!
**✱110·03 Df.** \(\text{Nc}ʻ\alpha +_{\text{c}}\mu = \text{N}_{0}\text{c}ʻ\alpha +_{\text{c}}\mu \quad\text{Df}\)

**✱110·04 Df.** \(\mu +_{\text{c}}\text{Nc}ʻ\alpha = \mu +_{\text{c}}\text{N}_{0}\text{c}ʻ\alpha \quad\text{Df}\)

Translation rules (normal adjustment, encoding decision 5): an argument `Nc'α` of `+_c` is
written `n₀c A`; "these definitions are extended by IIT" (PM): any other formal number in that
position gets an adequate type (encoding decision 6). Targets (status `definition`; say that the
Df is a rule of translation): `pm110_03 : (n₀c A +ᶜ μ : Set (Set γ)) = n₀c A +ᶜ μ := rfl`;
`pm110_04 : (μ +ᶜ n₀c A : Set (Set γ)) = μ +ᶜ n₀c A := rfl` (with `μ : Set (Set δ)`).

**✱110·531 Df.** \(\alpha + \beta + \gamma =(\alpha + \beta ) + \gamma \quad\text{Df}\)

Realized by `infixl`. Target: `pm110_531 : A +ₐ B +ₐ G = (A +ₐ B) +ₐ G := rfl`.

**✱110·561 Df.** \(\mu +_{\text{c}} \nu +_{\text{c}} \varpi = (\mu +_{\text{c}} \nu ) +_{\text{c}} \varpi \quad\text{Df}\)

Realized by `infixl`; the inner sum is an arithmetical component, so its type is a separate
parameter `W` (IIT). Target: `pm110_561 : ((μ +ᶜ ν : Set (Set W)) +ᶜ ϖ : Set (Set γ)) =
((μ +ᶜ ν : Set (Set W)) +ᶜ ϖ : Set (Set γ)) := rfl`.
-/

/-- **✱111·01 Df.** \(\kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda = (1\rightarrow 1)\cap \overleftarrow{\text{ᗡ}}ʻsʻ\lambda \cap \hat{T} (\kappa = T_{\in }ʻʻ\lambda ) \quad\text{Df}\)

The double correlators of `κ` with `λ`: one-one relations `T` with converse domain `s'λ` such
that `κ = T_∈''λ`. `ᗡ⃖'s'λ` is `rels Dcnv (sumCls L)`; the products bracket to the left. Target:
`pm111_01 : smsmbar K L = arrow one one ∩ rels Dcnv (sumCls L) ∩ {T | K = imgRel T ʻʻ L} := rfl`. -/
def smsmbar (K : Set (Set α)) (L : Set (Set β)) : Set (α → β → Prop) :=
  arrow one one ∩ rels Dcnv (sumCls L) ∩ {T | K = imgRel T ʻʻ L}

/-- **✱111·02 Df.** \(\text{Crp}(S)ʻ\beta = (Sʻ\beta ) \,\overline{\text{ sm }}\, \beta \quad \text{Df}\)

Defines the descriptive function `Crp(S)'β`, the correlators of `S'β` with `β`. Since `S'β` may
not exist, `Crp S` is the relation `ûβ̂{u = (S'β) sm̄ β}` (Summary of Part I Section E; Basic §5),
with `desc_Crp : Desc (Crp S) B ψ ↔ Desc S B (fun A => ψ (smbar A B))`. Target:
`pm111_02 : Crp S = fun U B => Desc S B (fun A => U = smbar A B) := rfl`. -/
def Crp (S : Set α → Set β → Prop) : Set (α → β → Prop) → Set β → Prop :=
  fun U B => Desc S B (fun A => U = smbar A B)

/-- **✱111·03 Df.** \(\text{ sm } \text{ sm } = \hat{\kappa} \hat{\lambda} (\exists ! \kappa \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, \lambda ) \quad\text{Df}\)

Double similarity (one symbol `sm sm`). Target:
`pm111_03 : (smsm : Set (Set α) → Set (Set β) → Prop) = fun K L => (smsmbar K L).Nonempty :=
rfl`. -/
def smsm : Set (Set α) → Set (Set β) → Prop := fun K L => (smsmbar K L).Nonempty

/-- `Σ'κ`, the arithmetical sum of a class of classes (value function of `ClsSigma`). -/
def clsSigma (K : Set (Set α)) : Set (α → Set α → Prop) := sumCls (opL downCls memRel ʻʻ K)

/-- **✱112·01 Df.** \(\Sigma ʻ\kappa = sʻ\in \unicode{x21A7} ʻʻ\kappa \quad\text{Df}\)

`∈↧` is the relation of `∈ ↧ α` (`↓α''α`) to `α`, i.e. `opL downCls memRel` (✱85·5, ✱38·01).
`Σ'κ` is `clsSigma K` (the couples `x ↓ α` with `x ∈ α ∈ κ`); the relation `Σ` is `ClsSigma`.
Target: `pm112_01 : clsSigma K = sumCls (opL downCls memRel ʻʻ K) := rfl`. -/
def ClsSigma : Set (α → Set α → Prop) → Set (Set α) → Prop := graph clsSigma

/-- `ΣNc'κ` in the type `γ` (explicit, as for `nc`). Value function of `SigmaNc`. -/
def sigmaNc (γ : Type w) (K : Set (Set α)) : Set (Set γ) := nc γ (clsSigma K)

/-- **✱112·02 Df.** \(\Sigma \text{Nc}ʻ\kappa = \text{Nc}ʻ\Sigma ʻ\kappa \quad\text{Df}\)

The sum of the cardinals of the members of `κ` (a primary formal number). Target:
`pm112_02 : sigmaNc γ K = nc γ (clsSigma K) := rfl`. -/
def SigmaNc : Set (Set γ) → Set (Set α) → Prop := graph (sigmaNc γ)

/-- The relation `α ↓,,` of `α ↓,, y` (`= ↓y''α`, ✱38·03) to `y`; `α↓,,''β` is
`coupleImg A ʻʻ B`. -/
def coupleImg (A : Set α) : Set (α → β → Prop) → β → Prop := graph (opImg couple A)

/-- **✱113·02 Df.** \(\beta \times \alpha = sʻ\alpha \downarrow_{,,} ʻʻ\beta \quad\text{Df}\)

The arithmetical class-product `β × α` (PM's order!), notation `B ×ₐ A`: the couples `x ↓ y` with
`x ∈ α`, `y ∈ β` (✱113·101). Target: `pm113_02 : B ×ₐ A = sumCls (coupleImg A ʻʻ B) := rfl`. -/
def clsTimes (B : Set β) (A : Set α) : Set (α → β → Prop) := sumCls (coupleImg A ʻʻ B)

@[inherit_doc] scoped infixl:70 " ×ₐ " => clsTimes

/-- **✱113·03 Df.** \(\mu \times _{c} \nu = \hat{\xi} \{(\exists \alpha , \beta ) . \mu = \text{N}_{0}\text{c}ʻ\alpha . \nu \text{N}_{0}\text{c}ʻ\beta . \xi \text{ sm } (\alpha \times \beta )\} \quad\text{Df}\)

(The e-text omits the `=` of `ν = N₀c'β`; mention the transcription error.) The arithmetical
product of two cardinals, `μ ×ᶜ ν`, actual type implicit. Target:
`pm113_03 : (μ ×ᶜ ν : Set (Set γ)) =
{ξ | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm ξ (A ×ₐ B)} := rfl`. -/
def cardMul {α : Type u} {β : Type v} {γ : Type w} (μ : Set (Set α)) (ν : Set (Set β)) :
    Set (Set γ) :=
  {ξ | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm ξ (A ×ₐ B)}

@[inherit_doc] scoped infixl:70 " ×ᶜ " => cardMul

/-!
**✱113·04 Df.** \(\text{Nc}ʻ\beta \times _{c} \mu = \text{N}_{0}\text{c}ʻ\beta \times _{c} \mu \quad\text{Df}\)

**✱113·05 Df.** \(\mu \times _{c} \text{Nc}ʻ\alpha = \mu \times _{c} \text{N}_{0}\text{c}ʻ\alpha \quad\text{Df}\)

Translation rules, as ✱110·03·04. Targets (status `definition`):
`pm113_04 : (n₀c B ×ᶜ μ : Set (Set γ)) = n₀c B ×ᶜ μ := rfl`;
`pm113_05 : (μ ×ᶜ n₀c A : Set (Set γ)) = μ ×ᶜ n₀c A := rfl`.

**✱113·511 Df.** \(\alpha \times \beta \times \gamma = (\alpha \times \beta ) \times \gamma \quad\text{Df}\)

Target: `pm113_511 : A ×ₐ B ×ₐ G = (A ×ₐ B) ×ₐ G := rfl`.

**✱113·541 Df.** \(\mu \times _{c} \nu \times _{c} \varpi = (\mu \times _{c} \nu ) \times _{c} \varpi \quad\text{Df}\)

As ✱110·561. Target: `pm113_541 : ((μ ×ᶜ ν : Set (Set W)) ×ᶜ ϖ : Set (Set γ)) =
((μ ×ᶜ ν : Set (Set W)) ×ᶜ ϖ : Set (Set γ)) := rfl`.
-/

/-- `ΠNc'κ` in the type `γ` (explicit). Value function of `PiNc`. -/
def piNc (γ : Type w) (K : Set (Set α)) : Set (Set γ) := nc γ (sel memRel K)

/-- **✱114·01 Df.** \(\Pi \text{Nc}ʻ\kappa = \text{Nc}ʻ{\in}_{\Delta }ʻ\kappa \quad\text{Df}\)

The product of the cardinals of the members of `κ`: the number of the `∈`-selections from `κ`
(`∈_Δ'κ` is `sel memRel K`). Target: `pm114_01 : piNc γ K = nc γ (sel memRel K) := rfl`. -/
def PiNc : Set (Set γ) → Set (Set α) → Prop := graph (piNc γ)

/-- `Prod'κ`, the classes formed by one member of each member of `κ` (value function of
`ProdK`). (Not `Prod`, which is Lean's product type.) -/
def prodK (K : Set (Set α)) : Set (Set α) := D ʻʻ sel memRel K

/-- **✱115·01 Df.** \(\text{Prod}ʻ\kappa =\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa \quad\text{Df}\)

`D''∈_Δ'κ`, the domains of the selections. Target: `pm115_01 : prodK K = D ʻʻ sel memRel K :=
rfl`. -/
def ProdK : Set (Set α) → Set (Set α) → Prop := graph prodK

/-- **✱115·02 Df.** \(\text{Cls}^{3}\,\text{arithm}=\hat{\kappa} (\kappa ,sʻ\kappa \in \text{Cls}^{2} \text{excl}) \quad\text{Df}\)

`κ, s'κ ∈ Cls² excl` is `κ ∈ Cls² excl . s'κ ∈ Cls² excl` (✱20·04), where the two `Cls² excl`
are of different types (`κ : Set (Set (Set α))`, `s'κ : Set (Set α)`), so it is a conjunction,
not `Mem2`. Target: `pm115_02 : (Cls3arithm : Set (Set (Set (Set α)))) =
{K | K ∈ Cls2excl ∧ sumCls K ∈ Cls2excl} := rfl`. -/
def Cls3arithm : Set (Set (Set (Set α))) := {K | K ∈ Cls2excl ∧ sumCls K ∈ Cls2excl}

/-- **✱116·01 Df.** \(\alpha \,\text{exp}\,\,\beta = \text{Prod}ʻ\alpha \downarrow_{,,}ʻʻ\beta \quad\text{Df}\)

`α exp β`, the classes of couples `x ↓ y` taking one `x ∈ α` for each `y ∈ β` (the functions
from `β` to `α`). Target: `pm116_01 : clsExp A B = prodK (coupleImg A ʻʻ B) := rfl`. -/
def clsExp (A : Set α) (B : Set β) : Set (Set (α → β → Prop)) := prodK (coupleImg A ʻʻ B)

/-- **✱116·02 Df.** \(\mu ^\nu =\hat{\gamma}\{(\exists \alpha ,\beta ).\mu = \text{N}_{0}\text{c}ʻ\alpha .\nu = \text{N}_{0}\text{c}ʻ\beta .\gamma \text{ sm }(\alpha \,\text{exp}\,\,\beta )\} \quad\text{Df}\)

Cardinal exponentiation `μ ^ᶜ ν`, actual type implicit. Target:
`pm116_02 : (μ ^ᶜ ν : Set (Set γ)) =
{G | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm G (clsExp A B)} := rfl`. -/
def cardExp {α : Type u} {β : Type v} {γ : Type w} (μ : Set (Set α)) (ν : Set (Set β)) :
    Set (Set γ) :=
  {G | ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm G (clsExp A B)}

@[inherit_doc] scoped infixr:75 " ^ᶜ " => cardExp

/-!
**✱116·03 Df.** \((\text{Nc}ʻ\alpha )^\nu = (\text{N}_{0}\text{c}ʻ\alpha )^\nu \quad\text{Df}\)

**✱116·04 Df.** \(\mu ^{\text{Nc}ʻ\beta } = \mu ^{\text{N}_{0}\text{c}ʻ\beta } \quad\text{Df}\)

Translation rules, as ✱110·03·04. Targets (status `definition`):
`pm116_03 : (n₀c A ^ᶜ ν : Set (Set γ)) = n₀c A ^ᶜ ν := rfl`;
`pm116_04 : (μ ^ᶜ n₀c B : Set (Set γ)) = μ ^ᶜ n₀c B := rfl`.
-/

/-- **✱116·529 Dft [✱116].** \(R\dagger = R\parallel \breve{R} \quad\text{Dft}[*116]\)

(Printed in the e-text as a proposition.) A temporary definition for ✱116 (made permanent in
✱150): `R† = R ‖ R̆`, the relation of `R | Q | R̆` to `Q`. Target (status `definition`; say it is a
Dft): `pm116_529 : dagger R = R ∥ R˘ := rfl`. -/
def dagger (R : α → β → Prop) : (α → α → Prop) → (β → β → Prop) → Prop := R ∥ R˘

/-- **✱117·01 Df.** \[\begin{align}\mu \gt \nu . = . (\exists \alpha , \beta ) . &\mu = \text{N}_{0}\text{c}ʻ\alpha . \nu = \text{N}_{0}\text{c}ʻ\beta .\\ &\exists ! \text{Cl}ʻ\alpha \cap \text{Nc}ʻ\beta . {\sim} \exists ! \text{Cl}ʻ\beta \cap \text{Nc}ʻ\alpha \quad\text{Df}\end{align}\]

`μ >ᶜ ν` (Lean's `>` on `Set` is strict inclusion; never use it). A product of four, bracketed to
the left; `Cl'α ∩ Nc'β` forces `Nc'β` into the type of `α` (`nc α B`), and `Cl'β ∩ Nc'α` gives
`nc β A`. Target: `pm117_01 : μ >ᶜ ν ↔ ∃ (A : Set α) (B : Set β),
((μ = n₀c A ∧ ν = n₀c B) ∧ (cl A ∩ nc α B).Nonempty) ∧ ¬(cl B ∩ nc β A).Nonempty := Iff.rfl`. -/
def cardGt (μ : Set (Set α)) (ν : Set (Set β)) : Prop :=
  ∃ (A : Set α) (B : Set β),
    ((μ = n₀c A ∧ ν = n₀c B) ∧ (cl A ∩ nc α B).Nonempty) ∧ ¬(cl B ∩ nc β A).Nonempty

@[inherit_doc] scoped infix:50 " >ᶜ " => cardGt

/-!
**✱117·02 Df.** \(\mu \gt \text{Nc}ʻ\alpha . = . \mu \gt \text{N}_{0}\text{c}ʻ\alpha \quad\text{Df}\)

**✱117·03 Df.** \(\text{Nc}ʻ\alpha \gt \nu . = . \text{N}_{0}\text{c}ʻ\alpha \gt \nu \quad\text{Df}\)

Translation rules: a side `Nc'α` of `>` (and, by PM's note after ✱117·06, of `<`, `≥`, `≤`) is
written `n₀c A`. Targets (status `definition`): `pm117_02 : μ >ᶜ n₀c A ↔ μ >ᶜ n₀c A := Iff.rfl`;
`pm117_03 : n₀c A >ᶜ ν ↔ n₀c A >ᶜ ν := Iff.rfl`.
-/

/-- **✱117·04 Df.** \(\mu \lt \nu . = . \nu \gt \mu \quad\text{Df}\)

Target: `pm117_04 : μ <ᶜ ν ↔ ν >ᶜ μ := Iff.rfl`. -/
def cardLt (μ : Set (Set α)) (ν : Set (Set β)) : Prop := ν >ᶜ μ

@[inherit_doc] scoped infix:50 " <ᶜ " => cardLt

/-- **✱117·05 Df.** \(\mu \geq \nu . = : \mu \gt \nu . \lor . \mu , \nu \in \text{N}_{0}\text{C} .\mu = \text{ sm }ʻʻ\nu \quad\text{Df}\)

`μ, ν ∈ N₀C . μ = sm''ν` is the product `(μ ∈ N₀C ∧ ν ∈ N₀C) ∧ μ = sm ʻʻ ν` (the two `N₀C` of
different types). Target: `pm117_05 : μ ≥ᶜ ν ↔ μ >ᶜ ν ∨ ((μ ∈ N₀C ∧ ν ∈ N₀C) ∧ μ = sm ʻʻ ν) :=
Iff.rfl`. -/
def cardGe (μ : Set (Set α)) (ν : Set (Set β)) : Prop :=
  μ >ᶜ ν ∨ ((μ ∈ N₀C ∧ ν ∈ N₀C) ∧ μ = sm ʻʻ ν)

@[inherit_doc] scoped infix:50 " ≥ᶜ " => cardGe

/-- **✱117·06 Df.** \(\mu \leq \nu . = . \nu \geq \mu \quad\text{Df}\)

"The analogues of ✱117·02·03 are to be applied also to ✱117·04·05·06" (PM). Target:
`pm117_06 : μ ≤ᶜ ν ↔ ν ≥ᶜ μ := Iff.rfl`. -/
def cardLe (μ : Set (Set α)) (ν : Set (Set β)) : Prop := ν ≥ᶜ μ

@[inherit_doc] scoped infix:50 " ≤ᶜ " => cardLe

/-! ## Section C: finite and infinite (✱118–✱126) -/

/-- **✱119·01 Df.** \(\gamma -_{c}\nu =\hat{\xi} \{\text{Nc}ʻ\xi +_{c}\nu =\gamma .\exists !\text{Nc}ʻ\xi +_{c}\nu\} \quad\text{Df}\)

Cardinal subtraction `G -ᶜ ν` (actual type `δ` of the difference implicit; `G : Set (Set γ)`).
`Nc'ξ +_c ν` is `n₀c ξ +ᶜ ν` (✱110·03), and its logical occurrence `∃!…` is bound to the
equational one (IT), so both are in the type of `γ`. Target:
`pm119_01 : (G -ᶜ ν : Set (Set δ)) =
{ξ | (n₀c ξ +ᶜ ν : Set (Set γ)) = G ∧ (n₀c ξ +ᶜ ν : Set (Set γ)).Nonempty} := rfl`. -/
def cardSub {γ : Type w} {β : Type v} {δ : Type u'} (G : Set (Set γ)) (ν : Set (Set β)) :
    Set (Set δ) :=
  {ξ | (n₀c ξ +ᶜ ν : Set (Set γ)) = G ∧ (n₀c ξ +ᶜ ν : Set (Set γ)).Nonempty}

@[inherit_doc] scoped infixl:65 " -ᶜ " => cardSub

/-!
**✱119·02 Df.** \(\text{Nc}ʻ\alpha -_{c}\nu =\text{N}_{0}\text{c}ʻ\alpha -_{c}\nu \quad\text{Df}\)

**✱119·03 Df.** \(\gamma -_{c}\text{Nc}ʻ\beta =\gamma -_{c}\text{N}_{0}\text{c}ʻ\beta \quad\text{Df}\)

Translation rules, as ✱110·03·04. Targets (status `definition`):
`pm119_02 : (n₀c A -ᶜ ν : Set (Set δ)) = n₀c A -ᶜ ν := rfl`;
`pm119_03 : (G -ᶜ n₀c B : Set (Set δ)) = G -ᶜ n₀c B := rfl`.
-/

/-- **✱119·54 Df.** \(\text{SM} (\delta ,\gamma ). = : tʻ\delta = \text{D}ʻ\text{ sm }_{\delta ,\gamma } . \lor . tʻ\gamma = \text{D}ʻ\text{ sm }_{\gamma ,\delta } \quad\text{Df}\)

`sm_{δ,γ}` is ✱65·1's `sm_{(δ,γ)}` (`relTT sm d g`: domain in `t'δ`, converse domain in `t'γ`):
every class of the type of `δ` is similar to some class of the type of `γ`, or conversely.
Target: `pm119_54 : SM d g ↔ typ d = dom (relTT sm d g) ∨ typ g = dom (relTT sm g d) :=
Iff.rfl`. -/
def SM (d : Set δ) (g : Set γ) : Prop := typ d = dom (relTT sm d g) ∨ typ g = dom (relTT sm g d)

/-- **✱120·01 Df.** \(\text{NC induct} = \hat{\alpha}\{\alpha (+_{c}1)_{*}0\} \quad\text{Df}\)

The relation `+_c 1` "of a cardinal to its immediate predecessor" (`α̂β̂(α = β +_c 1)`, ✱38·02 with
`♀ = +_c`), homogeneous (the ancestral needs it), `1` in the same type (encoding decision 10):
`plusC1 μ ν ↔ μ = ν +ᶜ one`. The definiens of `NC induct` is `{μ | anc plusC1 μ zero}`. -/
def plusC1 : Set (Set α) → Set (Set α) → Prop :=
  opR (fun μ ν : Set (Set α) => (μ +ᶜ ν : Set (Set α))) (one : Set (Set α))

/-- **✱120·01 Df.** \(\text{NC induct} = \hat{\alpha}\{\alpha (+_{c}1)_{*}0\} \quad\text{Df}\)

The inductive cardinals (of classes of `α`): the cardinals reached from `0` by adding `1`
(`mem_NCinduct_iff`; they are `Λ` and the `N₀c'ρ` for finite `ρ`, `NCinduct_cases`). Target:
`pm120_01 : (NCinduct : Set (Set (Set α))) = {μ | anc plusC1 μ zero} := rfl`. -/
def NCinduct : Set (Set (Set α)) := {μ | anc plusC1 μ zero}

/-- **✱120·011 Df.** \(\text{N}_{\xi }\text{C induct} =\hat{\alpha} \{\alpha (+_{c}1)_{*}0_{\xi }\} \quad\text{Df}\)

`0_ξ` is `0 ∩ t'ξ` (✱65·01 `clsT zero ξ`), with `ξ : Set α`. Target:
`pm120_011 : NCinductAt ξ = {μ | anc plusC1 μ (clsT zero ξ)} := rfl`. -/
def NCinductAt (ξ : Set α) : Set (Set (Set α)) := {μ | anc plusC1 μ (clsT zero ξ)}

/-- **✱120·02 Df.** \(\text{Cls induct} = sʻ\text{NC induct} \quad\text{Df}\)

The inductive classes; they are the finite classes (`mem_ClsInduct`). Target:
`pm120_02 : (ClsInduct : Set (Set α)) = sumCls NCinduct := rfl`. -/
def ClsInduct : Set (Set α) := sumCls NCinduct

/-- **✱120·021 Df.** \(\text{Cls}_{\xi }\text{induct} = sʻ\text{N}_{\xi }\text{C induct} \quad\text{Df}\)

Target: `pm120_021 : ClsInductAt ξ = sumCls (NCinductAt ξ) := rfl`. -/
def ClsInductAt (ξ : Set α) : Set (Set α) := sumCls (NCinductAt ξ)

/-- **✱120·03 Df.** \(\text{Infin ax}.=:\alpha \in \text{NC induct}.\supset _{a}.\exists !\alpha \quad\text{Df}\)

The axiom of infinity, a proposition, typically ambiguous: `InfinAx α` says that every inductive
cardinal of classes of `α`-things exists. It is `Infinite α` (`infinAx_iff_infinite`), so it is
not a theorem of Lean; keep it as a hypothesis exactly where PM has it, at the type PM's
enunciation (and convention Infin T) determines. (The e-text's `⊃_a` is `⊃_α`.) Target:
`pm120_03 : InfinAx α ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → μ.Nonempty := Iff.rfl`. -/
def InfinAx (α : Type u) : Prop := ∀ μ : Set (Set α), μ ∈ NCinduct → μ.Nonempty

/-- **✱120·04 Df.** \(\text{Infin ax}(x).=:\alpha \in \text{NC induct}.\supset _{a}.\exists !\alpha (x) \quad\text{Df}\)

The axiom of infinity at the type of `x`: `α(x)` is `α ∩ t't'x` (✱65·02 `clsT2 μ x`), which
forces `NC induct` into the type of classes of classes of `x`'s type. `InfinAxAt x ↔ InfinAx α`
(`infinAxAt_iff`). Target:
`pm120_04 : InfinAxAt x ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → (clsT2 μ x).Nonempty := Iff.rfl`. -/
def InfinAxAt (x : α) : Prop := ∀ μ : Set (Set α), μ ∈ NCinduct → (clsT2 μ x).Nonempty

/-- `spec'β`, the cardinals comparable with `β` (value function of `Spec`; the type of its
members is implicit). -/
def spec (B : Set (Set β)) : Set (Set (Set α)) := {μ | μ <ᶜ B ∨ μ ≥ᶜ B}

/-- **✱120·43 Df.** \(\text{spec}ʻ\beta =\hat{\alpha} \{\alpha <\beta .\lor.\alpha \geq \beta\} \quad\text{Df}\)

Target: `pm120_43 : (spec B : Set (Set (Set α))) = {μ | μ <ᶜ B ∨ μ ≥ᶜ B} := rfl`. -/
def Spec : Set (Set (Set α)) → Set (Set β) → Prop := graph spec

/-- **✱121·01 Df.** \(P(x \unicode{x2013} y) = \overleftarrow{P}_{\text{po}}ʻx \cap \overrightarrow{P}_{\text{po}}ʻy \quad\text{Df}\)

The interval without end-points: `P⃖_po'x` is `rels (po P) x`, `P⃗_po'y` is `refs (po P) y`.
Target: `pm121_01 : itvOO P x y = rels (po P) x ∩ refs (po P) y := rfl`. -/
def itvOO (P : α → α → Prop) (x y : α) : Set α := rels (po P) x ∩ refs (po P) y

/-- **✱121·011 Df.** \(P(x \dashv y) = \overleftarrow{P}_{\text{po}} ʻx \cap \overrightarrow{P}_{*} ʻy \quad\text{Df}\)

Target: `pm121_011 : itvOC P x y = rels (po P) x ∩ refs (anc P) y := rfl`. -/
def itvOC (P : α → α → Prop) (x y : α) : Set α := rels (po P) x ∩ refs (anc P) y

/-- **✱121·012 Df.** \(P(x \unicode{x27dd} y) = \overleftarrow{P}_{*} ʻx \cap \overrightarrow{P}_{\text{po}} ʻy \quad\text{Df}\)

Target: `pm121_012 : itvCO P x y = rels (anc P) x ∩ refs (po P) y := rfl`. -/
def itvCO (P : α → α → Prop) (x y : α) : Set α := rels (anc P) x ∩ refs (po P) y

/-- **✱121·013 Df.** \(P(x \vdash\dashv y) = \overleftarrow{P}_{*} ʻx \cap \overrightarrow{P}_{*} ʻy \quad\text{Df}\)

Target: `pm121_013 : itvCC P x y = rels (anc P) x ∩ refs (anc P) y := rfl`. -/
def itvCC (P : α → α → Prop) (x y : α) : Set α := rels (anc P) x ∩ refs (anc P) y

/-- **✱121·02 Df.** \(P_\nu = \hat{x} \hat{y} \{\text{N}_0\text{c} ʻP (x \vdash\dashv y) = \nu +_{c} 1\} \quad\text{Df}\)

`x P_ν y`: the interval `P(x⊢⊣y)` has `ν +_c 1` members. The equation is in the type of
`N₀c'P(x⊢⊣y)`; the type of `ν` is left free by PM (Prefatory Statement, VI), so `ν : Set (Set β)`
is any type, and `1` is taken in the type of `ν` (encoding decision 10). Target:
`pm121_02 : Pnu P ν = fun x y => n₀c (itvCC P x y) = ν +ᶜ (one : Set (Set β)) := rfl`. -/
def Pnu (P : α → α → Prop) (ν : Set (Set β)) : α → α → Prop :=
  fun x y => n₀c (itvCC P x y) = ν +ᶜ (one : Set (Set β))

/-- **✱121·03 Df.** \(\text{finid} ʻP = \hat{R} \{(\exists \nu ) . \nu \in \text{NC induct} - \iota ʻ\Lambda . R = P_{\nu }\} \quad\text{Df}\)

The type `β` of the apparent variable `ν` (and of `NC induct`) is the explicit argument. Target:
`pm121_03 : finid β P = {R | ∃ ν : Set (Set β), ν ∈ NCinduct \ ι Λ ∧ R = Pnu P ν} := rfl`. -/
def finid (β : Type v) (P : α → α → Prop) : Set (α → α → Prop) :=
  {R | ∃ ν : Set (Set β), ν ∈ NCinduct \ ι Λ ∧ R = Pnu P ν}

/-- **✱121·031 Df.** \(\text{fin} ʻP = \hat{R} \{(\exists \nu ). \nu \in \text{NC induct} - \iota ʻ\Lambda - \iota ʻ0 . R = P_{\nu }\} \quad\text{Df}\)

`α − β − γ` brackets to the left; Lean's `\` is not associative, so write the bracket. Target:
`pm121_031 : fin β P = {R | ∃ ν : Set (Set β), ν ∈ (NCinduct \ ι Λ) \ ι zero ∧ R = Pnu P ν} :=
rfl`. -/
def fin (β : Type v) (P : α → α → Prop) : Set (α → α → Prop) :=
  {R | ∃ ν : Set (Set β), ν ∈ (NCinduct \ ι Λ) \ ι zero ∧ R = Pnu P ν}

/-- **✱121·04 Df.** \(\nu _{P} = \breve{P} _{\nu -_{c} 1} ʻBʻP \quad\text{Df}\)

`ν_P`, "the `ν`th term of the posterity of `B'P`": `(P_{ν−_c1})˘'B'P`, a double description
(✱30·02: `B'P` has the smaller scope). `P̆_{ν−_c1}` is read `(P_{ν −_c 1})˘` (equal to
`(P̆)_{ν−_c1}`, since `P̆(x⊢⊣y) = P(y⊢⊣x)`); `ν −_c 1` and `1` are in the type of `ν`
(encoding decision 10). The Df defines the relation `nuP ν` of `ν_P` to `P` (Basic §5):
`ψ(ν_P)` is `Desc (nuP ν) P ψ`, and `desc_nuP` gives
`Desc (nuP ν) P ψ ↔ Desc2 (Pnu P (ν -ᶜ one))˘ Beg P ψ` (then `desc2_iff`). Target:
`pm121_04 : nuP ν = descRel (fun v P => Desc Beg P (fun b =>
(Pnu P (ν -ᶜ (one : Set (Set β)) : Set (Set β)))˘ v b)) := rfl`. -/
def nuP (ν : Set (Set β)) : α → (α → α → Prop) → Prop :=
  descRel (fun v P => Desc Beg P (fun b => (Pnu P (ν -ᶜ (one : Set (Set β)) : Set (Set β)))˘ v b))

/-- **✱122·01 Df.** \(\text{Prog} = (1\rightarrow 1)\cap \hat{R} (\text{D}ʻR = \overleftarrow{R}_{*}ʻBʻR) \quad\text{Df}\)

Progressions: one-one relations whose domain is the posterity of their beginning. `B'R` is a
description with scope `D'R = R⃖_*'B'R`. Target: `pm122_01 : (Prog : Set (α → α → Prop)) =
arrow one one ∩ {R | Desc Beg R (fun b => dom R = rels (anc R) b)} := rfl`. -/
def Prog : Set (α → α → Prop) := arrow one one ∩ {R | Desc Beg R (fun b => dom R = rels (anc R) b)}

/-- **✱123·01 Df.** \(\aleph _{0}=\text{D}ʻʻ\text{Prog} \quad\text{Df}\)

`ℵ₀`, the domains of progressions (of `α`-things). Target:
`pm123_01 : (aleph0 : Set (Set α)) = D ʻʻ Prog := rfl`. -/
def aleph0 : Set (Set α) := D ʻʻ Prog

/-- **✱123·02 Dft [✱123—4].** \(N=\hat{\mu} \hat{\nu} \{\mu \in \text{NC induct}.\nu =(\mu +_{c}1)\cap t_{0}ʻ\mu\} \quad\text{Dft} [*123—4]\)

(Printed in the e-text as a proposition.) A temporary definition for ✱123–✱124: the relation of
an inductive cardinal to its successor in the same type (`t₀'μ` puts `μ +_c 1` in the type of
`μ`'s members; `1` in that type, encoding decision 10). Target (status `definition`; say it is a
Dft): `pm123_02 : (Nsucc : Set (Set α) → Set (Set α) → Prop) =
fun μ ν => μ ∈ NCinduct ∧ ν = (μ +ᶜ (one : Set (Set α)) : Set (Set α)) ∩ typ₀ μ := rfl`. -/
def Nsucc : Set (Set α) → Set (Set α) → Prop :=
  fun μ ν => μ ∈ NCinduct ∧ ν = (μ +ᶜ (one : Set (Set α)) : Set (Set α)) ∩ typ₀ μ

/-- **✱124·01 Df.** \(\text{Cls refl} = \hat{\rho} \{(\exists R) . R \in 1 \rightarrow 1 . \text{ᗡ}ʻR \subset \text{D}ʻR . \exists ! \overrightarrow{B}ʻR . \rho = \text{D}ʻR\} \quad\text{Df}\)

Reflexive classes: domains of one-one relations into themselves with a beginning (similar to a
proper part). `B⃗'R` is `refs Beg R`; a product of four, bracketed to the left. Target:
`pm124_01 : (ClsRefl : Set (Set α)) = {ρ | ∃ R : α → α → Prop,
((R ∈ arrow one one ∧ codom R ⊆ dom R) ∧ (refs Beg R).Nonempty) ∧ ρ = dom R} := rfl`. -/
def ClsRefl : Set (Set α) :=
  {ρ | ∃ R : α → α → Prop, ((R ∈ arrow one one ∧ codom R ⊆ dom R) ∧ (refs Beg R).Nonempty) ∧
    ρ = dom R}

/-- **✱124·02 Df.** \(\text{NC refl} = \text{N}_{0}\text{c}ʻʻ\text{Cls refl} \quad\text{Df}\)

Target: `pm124_02 : (NCrefl : Set (Set (Set α))) = N₀c ʻʻ ClsRefl := rfl`. -/
def NCrefl : Set (Set (Set α)) := N₀c ʻʻ ClsRefl

/-!
**✱124·021 Df.** \(\text{Nc}ʻ\rho \in \text{NC refl} . = . \text{N}_{0}\text{c}ʻ\rho \in \text{NC refl} \quad\text{Df}\)

Translation rule: `Nc'ρ ∈ NC refl` is written `n₀c ρ ∈ NCrefl` (encoding decision 5). Target
(status `definition`): `pm124_021 : n₀c ρ ∈ NCrefl ↔ n₀c ρ ∈ NCrefl := Iff.rfl`.
-/

/-- **✱124·03 Df.** \(\text{NC mult} = \text{NC} \cap \hat{\alpha} \{\kappa \in \alpha \cap \text{Cls ex}^{2}\,\text{excl}. \supset _{\kappa } . \exists ! {\in}_{\Delta}ʻ\kappa \} \quad\text{Df}\)

Multiplicative cardinals: cardinals (of classes of classes) every exclusive existent member of
which has a selection. The members of `μ ∈ NC mult` are classes of classes of `α`; the type `β`
of the converse domain of `Nc` in `NC` is explicit (encoding decision 3). Target:
`pm124_03 : NCmult β = NC β ∩ {μ : Set (Set (Set α)) |
∀ K, K ∈ μ ∩ ClsEx2excl → (sel memRel K).Nonempty} := rfl`. -/
def NCmult (β : Type v) : Set (Set (Set (Set α))) :=
  NC β ∩ {μ | ∀ K, K ∈ μ ∩ ClsEx2excl → (sel memRel K).Nonempty}

/-- **✱126·01 Df.** \(\text{NC ind}=\text{Nc induct}-\iota ʻ\Lambda \quad\text{Df}\)

(The e-text prints `Nc induct` for `NC induct`, as the Prefatory Statement and the Summary of
✱126 show; mention the transcription error.) The "indefinite inductive cardinals", used under the
Rule of Indefinite Numbers (encoding decision 9). Target:
`pm126_01 : (NCind : Set (Set (Set α))) = NCinduct \ ι Λ := rfl`. -/
def NCind : Set (Set (Set α)) := NCinduct \ ι Λ

/-! ## Adequate actual types (Prefatory Statement, II)

PM defines a type to be *adequate* for a formal number `σ` when "we can logically prove `∃!σ'`"
for a related `σ'` in which every argument is replaced by the greatest class (or cardinal) of
its type. In Lean "can be proved" is replaced by "holds" (a hypothesis on the type parameter),
and the definitions are PM's (i)–(ii) literally, `t₀'α` being `typ₀ A` (`= Set.univ`) and
`N₀c't₁'μ` being `n₀c (typ₁ μ)` (the greatest cardinal of the type of `μ`), except `AdeqSm`,
whose literal form is vacuous (see there). They are used by the conventions IIT and AT
(encoding decisions 6, 7). Adequacy depends only on the *types* of the arguments, not on their
values (`adeqNc_iff`, `adeqAdd_iff`, `adeqSm_iff`): for an argument that is an apparent variable
(e.g. the `μ` of `(∃μ) . Nc'α = Nc'β +_c μ`, ✱110·71) pass any term of its type, e.g.
`AdeqAdd γ (n₀c B) (Λ : Set (Set W))`, and state the hypothesis outside the quantifier. -/

/-- The type `γ` is adequate for `Nc'α` (`∃!Nc't₀'α`, (i)); `adeqNc_iff`: there is an injection
of `α` into `γ`. -/
def AdeqNc (γ : Type w) (A : Set α) : Prop := (nc γ (typ₀ A)).Nonempty

/-- The type `γ` is adequate for `ΣNc'κ` (`∃!ΣNc't₀'κ`, (i)). -/
def AdeqSigmaNc (γ : Type w) (K : Set (Set α)) : Prop := (sigmaNc γ (typ₀ K)).Nonempty

/-- The type `γ` is adequate for `ΠNc'κ` (`∃!ΠNc't₀'κ`, (i)). -/
def AdeqPiNc (γ : Type w) (K : Set (Set α)) : Prop := (piNc γ (typ₀ K)).Nonempty

/-- The type `γ` is adequate for `sm''μ`. PM's (i) literally asks for `∃!sm''t₀'μ`, which holds in
every type (`Λ ∈ t₀'μ` and `Λ sm Λ`: `adeqSm_literal_holds`), so it would not yield PM's stated
consequence "`(μ) . ∃!sm''μ`" in an adequate type, nor the step `α +_c sm''β = α +_c β` of the
Prefatory Statement (V). We therefore read "the `V` of the appropriate type" for the argument `μ`
of `sm''`, as in (ii), as the greatest cardinal `N₀c't₁'μ` of the type of `μ`:
`∃!sm''N₀c't₁'μ`. `adeqSm_iff`: `α` injects into `γ`; `AdeqSm.sm_img_nonempty`: then
`∃!sm''μ` for every `μ ∈ NC − ι'Λ` of the type of `μ`. (No proposition of Part III has `sm''σ` in
an arithmetical position; IIT needs this only for such forms.) -/
def AdeqSm (γ : Type w) (μ : Set (Set α)) : Prop := (sm ʻʻ n₀c (typ₁ μ) : Set (Set γ)).Nonempty

/-- The type `γ` is adequate for `μ +_c ν` (`∃!N₀c't₁'μ +_c N₀c't₁'ν`, (ii)); `adeqAdd_iff`:
there is an injection of `α ⊕ β` into `γ`. -/
def AdeqAdd (γ : Type w) (μ : Set (Set α)) (ν : Set (Set β)) : Prop :=
  (n₀c (typ₁ μ) +ᶜ n₀c (typ₁ ν) : Set (Set γ)).Nonempty

/-- The type `γ` is adequate for `μ ×_c ν` (`∃!N₀c't₁'μ ×_c N₀c't₁'ν`, (ii)). -/
def AdeqMul (γ : Type w) (μ : Set (Set α)) (ν : Set (Set β)) : Prop :=
  (n₀c (typ₁ μ) ×ᶜ n₀c (typ₁ ν) : Set (Set γ)).Nonempty

/-- The type `γ` is adequate for `μ^ν` (`∃!N₀c't₁'μ^{N₀c't₁'ν}`, (ii)). -/
def AdeqExp (γ : Type w) (μ : Set (Set α)) (ν : Set (Set β)) : Prop :=
  (n₀c (typ₁ μ) ^ᶜ n₀c (typ₁ ν) : Set (Set γ)).Nonempty

/-- The type `γ` is adequate for `μ −_c ν` (`∃!N₀c't₁'μ −_c 0 ∩ t₀'ν`, (ii)). -/
def AdeqSub (γ : Type w) (μ : Set (Set α)) (ν : Set (Set β)) : Prop :=
  (n₀c (typ₁ μ) -ᶜ (zero ∩ typ₀ ν) : Set (Set γ)).Nonempty

/-! ## Sanity lemmas: the encodings behave -/

section Sanity

/-! ### `Nc'α` and `NC` -/

/-- `β ∈ Nc'α . ≡ . β sm α` (✱100·1). -/
theorem mem_nc {A : Set β} {B : Set γ} : B ∈ nc γ A ↔ sm B A := Iff.rfl

/-- `ψ(Nc'α) ↔ ψ(nc γ A)`: the descriptive function of `Nc` always exists (✱100·2). -/
theorem desc_Nc (A : Set β) (ψ : Set (Set γ) → Prop) :
    Desc (Nc : Set (Set γ) → Set β → Prop) A ψ ↔ ψ (nc γ A) := desc_graph _ _ _

theorem EDesc_Nc (A : Set β) : EDesc (Nc : Set (Set γ) → Set β → Prop) A := EDesc_graph _ _

/-- The typically definite `Nc(ξ)'α` (✱65·04, `t²'ξ ↿ Nc`) is `nc γ A`. -/
theorem desc_relT2_Nc (ξ : Set γ) (A : Set β) (ψ : Set (Set γ) → Prop) :
    Desc (relT2 (Nc : Set (Set γ) → Set β → Prop) ξ) A ψ ↔ ψ (nc γ A) := by
  have h : relT2 (Nc : Set (Set γ) → Set β → Prop) ξ = Nc := by
    funext K B
    simp [relT2, dres, typ2, typ_eq_univ]
  rw [h]
  exact desc_Nc A ψ

/-- `β ∈ Nc'α` iff there is a bijection between `β` and `α`. -/
theorem mem_nc_iff_equiv {A : Set β} {B : Set γ} : B ∈ nc γ A ↔ Nonempty (B ≃ A) :=
  sm_iff_nonempty_equiv

/-- `α ∈ Nc'α` (✱100·3). -/
theorem self_mem_nc (A : Set α) : A ∈ nc α A := sm_refl A

/-- `α sm β . ⊃ . Nc'α = Nc'β` (✱100·321), in any type. -/
theorem nc_eq_nc_of_sm {A : Set α} {B : Set β} (h : sm A B) : nc γ A = nc γ B := by
  ext C
  exact ⟨fun hC => sm_trans hC h, fun hC => sm_trans hC (sm_symm h)⟩

/-- `∃!Nc'α ∩ Nc'β . ⊃ . α sm β` (✱100·33). -/
theorem sm_of_mem_nc_of_mem_nc {A : Set α} {B : Set β} {C : Set γ} (hA : C ∈ nc γ A)
    (hB : C ∈ nc γ B) : sm A B := sm_trans (sm_symm hA) hB

/-- When `Nc'α` exists in the type `γ`, `Nc'α = Nc'β` in `γ` iff `α sm β` (cf. ✱100·35). -/
theorem nc_eq_nc_iff {A : Set α} {B : Set β} (h : (nc γ A).Nonempty) :
    nc γ A = nc γ B ↔ sm A B := by
  refine ⟨fun e => ?_, nc_eq_nc_of_sm⟩
  obtain ⟨C, hC⟩ := h
  have hC' : C ∈ nc γ B := by rw [← e]; exact hC
  exact sm_of_mem_nc_of_mem_nc hC hC'

/-- `∃!Nc'α` in the type `γ` iff `α` can be injected into `γ`. -/
theorem nc_nonempty_iff {A : Set β} : (nc γ A).Nonempty ↔ ∃ f : A → γ, Function.Injective f := by
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨e⟩ := mem_nc_iff_equiv.1 hB
    exact ⟨fun a => (e.symm a : γ), Subtype.val_injective.comp e.symm.injective⟩
  · rintro ⟨f, hf⟩
    exact ⟨Set.range f, mem_nc_iff_equiv.2 ⟨(Equiv.ofInjective f hf).symm⟩⟩

/-- `μ ∈ NC . ≡ . (∃α) . μ = Nc'α` (✱100·4), with the type of `α` explicit. -/
theorem mem_NC {μ : Set (Set γ)} : μ ∈ NC β ↔ ∃ A : Set β, μ = nc γ A := Iff.rfl

/-- `Nc'α ∈ NC` (✱100·41). -/
theorem nc_mem_NC (A : Set β) : nc γ A ∈ NC β := ⟨A, rfl⟩

/-- `NC^β(α)` is `NC` with the types of `α` and `β`. -/
theorem NCT_eq_NC (A : Set α) (B : Set β) : NCT A B = NC β := by
  ext μ
  simp [NCT, NC, relT2T, dres, cres, dom, typ2, typ_eq_univ]

/-! ### Homogeneous cardinals -/

theorem n₀c_eq_nc (A : Set α) : n₀c A = nc α A := by
  rw [n₀c, typ_eq_univ, Set.inter_univ]

theorem mem_n₀c {A B : Set α} : B ∈ n₀c A ↔ sm B A := by
  rw [n₀c_eq_nc]; exact Iff.rfl

theorem self_mem_n₀c (A : Set α) : A ∈ n₀c A := mem_n₀c.2 (sm_refl A)

/-- `∃!N₀c'α` (✱103·13). -/
theorem n₀c_nonempty (A : Set α) : (n₀c A).Nonempty := ⟨A, self_mem_n₀c A⟩

theorem n₀c_eq_n₀c_iff {A B : Set α} : n₀c A = n₀c B ↔ sm A B := by
  rw [n₀c_eq_nc, n₀c_eq_nc]
  exact nc_eq_nc_iff ⟨A, self_mem_nc A⟩

theorem desc_N₀c (A : Set α) (ψ : Set (Set α) → Prop) : Desc N₀c A ψ ↔ ψ (n₀c A) :=
  desc_graph _ _ _

theorem mem_N₀C {μ : Set (Set α)} : μ ∈ N₀C ↔ ∃ A, μ = n₀c A := Iff.rfl

theorem n₀c_ne_empty (A : Set α) : n₀c A ≠ ∅ := (n₀c_nonempty A).ne_empty

/-! ### Adequacy -/

/-- An existence statement about injections is invariant under a bijection of the source. -/
private theorem exists_injective_congr {σ : Sort*} {τ : Sort*} (e : σ ≃ τ) :
    (∃ f : σ → γ, Function.Injective f) ↔ ∃ g : τ → γ, Function.Injective g :=
  ⟨fun ⟨f, hf⟩ => ⟨f ∘ e.symm, hf.comp e.symm.injective⟩,
    fun ⟨g, hg⟩ => ⟨g ∘ e, hg.comp e.injective⟩⟩

/-- `γ` is adequate for `Nc'α` iff `α` injects into `γ`. -/
theorem adeqNc_iff {A : Set α} : AdeqNc γ A ↔ ∃ f : α → γ, Function.Injective f := by
  rw [AdeqNc, nc_nonempty_iff, typ₀_eq_univ]
  exact exists_injective_congr (Equiv.Set.univ α)

/-- In an adequate type, every `Nc'β` with `β` of the type of `α` exists. -/
theorem AdeqNc.nc_nonempty {A : Set α} (h : AdeqNc γ A) (B : Set α) : (nc γ B).Nonempty := by
  obtain ⟨f, hf⟩ := adeqNc_iff.1 h
  exact nc_nonempty_iff.2 ⟨fun b => f b, hf.comp Subtype.val_injective⟩

/-- PM's literal condition `∃!sm''t₀'μ` for the adequacy of `sm''μ` holds in every type: `Λ` is
similar to `Λ`. (Hence `AdeqSm` reads `t₀'μ` as `N₀c't₁'μ`.) -/
theorem adeqSm_literal_holds (μ : Set (Set α)) : (sm ʻʻ typ₀ μ : Set (Set γ)).Nonempty :=
  ⟨∅, ∅, by rw [typ₀_eq_univ]; exact Set.mem_univ _,
    sm_iff_nonempty_equiv.2 ⟨Equiv.equivOfIsEmpty _ _⟩⟩

/-- `sm''N₀c'β = Nc'β`, in the type fixed by the context (cf. ✱100·511, ✱103·4). -/
theorem sm_img_n₀c (B : Set β) : (sm ʻʻ n₀c B : Set (Set γ)) = nc γ B := by
  ext X
  constructor
  · rintro ⟨Y, hY, hXY⟩
    exact sm_trans hXY (mem_n₀c.1 hY)
  · intro h
    exact ⟨B, self_mem_n₀c B, h⟩

/-- `γ` is adequate for `sm''μ` iff `α` injects into `γ` (`μ : Set (Set α)`). -/
theorem adeqSm_iff {μ : Set (Set α)} : AdeqSm γ μ ↔ ∃ f : α → γ, Function.Injective f := by
  rw [AdeqSm, sm_img_n₀c, nc_nonempty_iff, typ₁, typ₀_eq_univ]
  exact exists_injective_congr (Equiv.Set.univ α)

/-- In an adequate type, `∃!sm''μ` for every existent cardinal `μ` of the type of `μ`. -/
theorem AdeqSm.sm_img_nonempty {μ : Set (Set α)} (h : AdeqSm γ μ) (hμ : μ ∈ NC β)
    (hne : μ.Nonempty) : (sm ʻʻ μ : Set (Set γ)).Nonempty := by
  obtain ⟨A, rfl⟩ := hμ
  obtain ⟨X, hX⟩ := hne
  obtain ⟨f, hf⟩ := adeqSm_iff.1 h
  obtain ⟨Y, hY⟩ := nc_nonempty_iff.2 ⟨fun x : X => f x, hf.comp Subtype.val_injective⟩
  exact ⟨Y, X, hX, hY⟩

/-! ### The arithmetical class-sum -/

theorem couple_eq_couple_iff {x x' : α} {y y' : β} : x ↓ y = x' ↓ y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have : (x' ↓ y') x y := by rw [← h]; exact (couple_apply x y x y).2 ⟨rfl, rfl⟩
    exact (couple_apply x' y' x y).1 this
  · rintro ⟨rfl, rfl⟩; rfl

/-- `R ∈ α + β . ≡ : (∃x) . x ∈ α . R = ι'x ↓ Λ_β : ∨ : (∃y) . y ∈ β . R = Λ_α ↓ ι'y` (cf. ✱110·1). -/
theorem mem_clsSum {A : Set α} {B : Set β} {R : Set α → Set β → Prop} :
    R ∈ A +ₐ B ↔ (∃ x, x ∈ A ∧ R = ι x ↓ (Λ ∩ B)) ∨ (∃ y, y ∈ B ∧ R = (Λ ∩ A) ↓ ι y) := by
  constructor
  · rintro (⟨u, ⟨x, hx, rfl⟩, h⟩ | ⟨u, ⟨y, hy, rfl⟩, h⟩)
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨y, hy, h⟩
  · rintro (⟨x, hx, h⟩ | ⟨y, hy, h⟩)
    · exact Or.inl ⟨ι x, ⟨x, hx, rfl⟩, h⟩
    · exact Or.inr ⟨ι y, ⟨y, hy, rfl⟩, h⟩

private theorem unitCls_ne_null_inter (x : α) (A : Set α) : ι x ≠ Λ ∩ A := by
  intro h
  have hx : x ∈ Λ ∩ A := h ▸ (rfl : x = x)
  exact hx.1 rfl

/-- The map `α ⊕ β → α + β`, `x ↦ ι'x ↓ Λ_β`, `y ↦ Λ_α ↓ ι'y`. -/
private def clsSumMap (A : Set α) (B : Set β) : A ⊕ B → ↥(A +ₐ B)
  | Sum.inl a => ⟨ι (a : α) ↓ (Λ ∩ B), mem_clsSum.2 (Or.inl ⟨a, a.2, rfl⟩)⟩
  | Sum.inr b => ⟨(Λ ∩ A) ↓ ι (b : β), mem_clsSum.2 (Or.inr ⟨b, b.2, rfl⟩)⟩

private theorem clsSumMap_bijective (A : Set α) (B : Set β) :
    Function.Bijective (clsSumMap A B) := by
  constructor
  · rintro (a | b) (a' | b') h <;> simp only [clsSumMap, Subtype.mk.injEq] at h
    · rw [couple_eq_couple_iff] at h
      exact congrArg Sum.inl (Subtype.ext (unitCls_injective h.1))
    · exact absurd (couple_eq_couple_iff.1 h).1 (unitCls_ne_null_inter _ _)
    · exact absurd (couple_eq_couple_iff.1 h).1.symm (unitCls_ne_null_inter _ _)
    · rw [couple_eq_couple_iff] at h
      exact congrArg Sum.inr (Subtype.ext (unitCls_injective h.2))
  · rintro ⟨R, hR⟩
    rcases mem_clsSum.1 hR with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨y, hy⟩, rfl⟩

/-- `α + β` is a disjoint union of copies of `α` and `β` (cf. ✱110·11·12). -/
noncomputable def clsSumEquiv (A : Set α) (B : Set β) : ↥(A +ₐ B) ≃ A ⊕ B :=
  (Equiv.ofBijective _ (clsSumMap_bijective A B)).symm

/-- `γ sm α . δ sm β . ⊃ . (γ + δ) sm (α + β)` (✱110·15). -/
theorem sm_clsSum {A : Set α} {B : Set β} {A' : Set γ} {B' : Set δ} (hA : sm A A')
    (hB : sm B B') : sm (A +ₐ B) (A' +ₐ B') := by
  obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 hA
  obtain ⟨eB⟩ := sm_iff_nonempty_equiv.1 hB
  exact sm_iff_nonempty_equiv.2
    ⟨(clsSumEquiv A B).trans ((eA.sumCongr eB).trans (clsSumEquiv A' B').symm)⟩

/-- `ξ ∈ μ +_c ν . ≡ . (∃α, β) . μ = N₀c'α . ν = N₀c'β . ξ sm (α + β)` (✱110·02). -/
theorem mem_cardAdd {μ : Set (Set α)} {ν : Set (Set β)} {ξ : Set γ} :
    ξ ∈ μ +ᶜ ν ↔ ∃ (A : Set α) (B : Set β), (μ = n₀c A ∧ ν = n₀c B) ∧ sm ξ (A +ₐ B) := Iff.rfl

/-- `N₀c'α +_c N₀c'β = Nc'(α + β)` (✱110·22), in any type `γ`. -/
theorem n₀c_cardAdd_n₀c (A : Set α) (B : Set β) :
    (n₀c A +ᶜ n₀c B : Set (Set γ)) = nc γ (A +ₐ B) := by
  ext ξ
  constructor
  · rintro ⟨A', B', ⟨hA, hB⟩, h⟩
    have hA' : sm A A' := mem_n₀c.1 (hA ▸ self_mem_n₀c A)
    have hB' : sm B B' := mem_n₀c.1 (hB ▸ self_mem_n₀c B)
    exact sm_trans h (sm_clsSum (sm_symm hA') (sm_symm hB'))
  · intro h
    exact ⟨A, B, ⟨rfl, rfl⟩, h⟩

/-- If `μ` is not a homogeneous cardinal, `μ +_c ν = Λ` (cf. ✱110·4). -/
theorem cardAdd_eq_empty_of_left {μ : Set (Set α)} (h : ∀ A, μ ≠ n₀c A) (ν : Set (Set β)) :
    (μ +ᶜ ν : Set (Set γ)) = ∅ := by
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨hA, -⟩, -⟩
  exact h A hA

/-- If `ν` is not a homogeneous cardinal, `μ +_c ν = Λ` (cf. ✱110·4). -/
theorem cardAdd_eq_empty_of_right (μ : Set (Set α)) {ν : Set (Set β)} (h : ∀ B, ν ≠ n₀c B) :
    (μ +ᶜ ν : Set (Set γ)) = ∅ := by
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨-, hB⟩, -⟩
  exact h B hB

/-- An existent `Nc(ξ)'α` is the homogeneous cardinal of any of its members (cf. ✱103·4). -/
theorem nc_eq_n₀c_of_mem {A : Set α} {X : Set γ} (h : X ∈ nc γ A) : nc γ A = n₀c X := by
  rw [n₀c_eq_nc]; exact (nc_eq_nc_of_sm h).symm

/-- `(α + β) + γ sm α + (β + γ)` (cf. ✱110·56). -/
theorem sm_clsSum_assoc (A : Set α) (B : Set β) (G : Set γ) :
    sm (A +ₐ B +ₐ G) (A +ₐ (B +ₐ G)) :=
  sm_iff_nonempty_equiv.2 ⟨(clsSumEquiv _ _).trans
    (((clsSumEquiv A B).sumCongr (Equiv.refl _)).trans ((Equiv.sumAssoc _ _ _).trans
      (((Equiv.refl _).sumCongr (clsSumEquiv B G).symm).trans (clsSumEquiv A (B +ₐ G)).symm)))⟩

/-- `x ↓ y ∈ β × α . ≡ . x ∈ α . y ∈ β` (cf. ✱113·101). -/
theorem couple_mem_clsTimes {A : Set α} {B : Set β} {x : α} {y : β} :
    x ↓ y ∈ B ×ₐ A ↔ x ∈ A ∧ y ∈ B := by
  constructor
  · rintro ⟨S, ⟨y', hy', hS⟩, hxy⟩
    rw [hS] at hxy
    obtain ⟨x', hx', h⟩ := hxy
    obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 h
    exact ⟨hx', hy'⟩
  · rintro ⟨hx, hy⟩
    exact ⟨_, ⟨y, hy, rfl⟩, x, hx, rfl⟩

/-- `γ` is adequate for `μ +_c ν` iff `α ⊕ β` injects into `γ`. -/
theorem adeqAdd_iff {μ : Set (Set α)} {ν : Set (Set β)} :
    AdeqAdd γ μ ν ↔ ∃ f : α ⊕ β → γ, Function.Injective f := by
  rw [AdeqAdd, n₀c_cardAdd_n₀c, nc_nonempty_iff]
  refine exists_injective_congr ((clsSumEquiv _ _).trans (Equiv.sumCongr ?_ ?_))
  · exact (Set.equivOfEq (typ₀_eq_univ _)).trans (Equiv.Set.univ α)
  · exact (Set.equivOfEq (typ₀_eq_univ _)).trans (Equiv.Set.univ β)

/-- In a type adequate for `μ +_c ν`, `Nc'(α + β)` exists for all `α`, `β` of the types of the
members of `μ`, `ν`. -/
theorem AdeqAdd.nc_nonempty {μ : Set (Set α)} {ν : Set (Set β)} (h : AdeqAdd γ μ ν) (A : Set α)
    (B : Set β) : (nc γ (A +ₐ B)).Nonempty := by
  obtain ⟨f, hf⟩ := adeqAdd_iff.1 h
  exact nc_nonempty_iff.2 ⟨fun r => f (Sum.map Subtype.val Subtype.val (clsSumEquiv A B r)),
    hf.comp ((Sum.map_injective.2 ⟨Subtype.val_injective, Subtype.val_injective⟩).comp
      (clsSumEquiv A B).injective)⟩

/-- In a type with no members, `Nc'α = Λ` for every existent `α`. -/
theorem nc_eq_empty_of_isEmpty [IsEmpty γ] {A : Set α} (h : A.Nonempty) : nc γ A = ∅ := by
  ext Y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hY
  obtain ⟨e⟩ := mem_nc_iff_equiv.1 hY
  obtain ⟨x, hx⟩ := h
  exact isEmptyElim (e.symm ⟨x, hx⟩ : γ)

/-! ### `0`, `1` and `+_c 1` -/

/-- `0 = N₀c'Λ` (cf. ✱101·1). -/
theorem zero_eq_n₀c_empty : (zero : Set (Set α)) = n₀c ∅ := by
  ext B
  rw [mem_n₀c, sm_iff_nonempty_equiv]
  show B = Λ ↔ _
  rw [Null_eq_empty]
  constructor
  · rintro rfl; exact ⟨Equiv.refl _⟩
  · rintro ⟨e⟩
    exact Set.eq_empty_iff_forall_notMem.2 fun b hb => (e ⟨b, hb⟩).2

/-- `1 = N₀c'ι'x` (cf. ✱101·2). -/
theorem one_eq_n₀c_singleton (x : α) : (one : Set (Set α)) = n₀c {x} := by
  ext B
  rw [mem_n₀c, sm_iff_nonempty_equiv]
  constructor
  · rintro ⟨y, rfl⟩
    rw [unitCls_eq_singleton]; exact ⟨Equiv.ofUnique _ _⟩
  · rintro ⟨e⟩
    refine ⟨(e.symm ⟨x, rfl⟩ : α), Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
    · have : e ⟨z, hz⟩ = ⟨x, rfl⟩ := Subsingleton.elim _ _
      exact congrArg Subtype.val (e.symm_apply_eq.2 this.symm).symm
    · rw [mem_unitCls.1 hz]
      exact (e.symm ⟨x, rfl⟩).2

theorem plusC1_iff {μ ν : Set (Set α)} : plusC1 μ ν ↔ μ = ν +ᶜ (one : Set (Set α)) := Iff.rfl

/-- Every cardinal is in the field of `+_c 1`. -/
theorem mem_fld_plusC1 (μ : Set (Set α)) : μ ∈ fld (plusC1 : Set (Set α) → Set (Set α) → Prop) :=
  ⟨μ +ᶜ one, Or.inr rfl⟩

/-- `μ ∈ NC induct` iff `μ` is reached from `0` by finitely many additions of `1`. -/
theorem mem_NCinduct_iff {μ : Set (Set α)} :
    μ ∈ NCinduct ↔ Relation.ReflTransGen plusC1 μ zero := by
  show anc plusC1 μ zero ↔ _
  rw [anc_iff_reflTransGen]
  exact and_iff_right (mem_fld_plusC1 μ)

/-- `0 ∈ NC induct` (✱120·12). -/
theorem zero_mem_NCinduct : (zero : Set (Set α)) ∈ NCinduct :=
  mem_NCinduct_iff.2 Relation.ReflTransGen.refl

/-- `μ ∈ NC induct . ⊃ . μ +_c 1 ∈ NC induct` (homogeneous; cf. ✱120·121). -/
theorem cardAdd_one_mem_NCinduct {μ : Set (Set α)} (h : μ ∈ NCinduct) :
    (μ +ᶜ (one : Set (Set α)) : Set (Set α)) ∈ NCinduct :=
  mem_NCinduct_iff.2 (Relation.ReflTransGen.head rfl (mem_NCinduct_iff.1 h))

/-- `x ∼∈ ρ . ⊃ . N₀c'(ρ ∪ ι'x) = N₀c'ρ +_c 1` (cf. ✱110·631). -/
theorem n₀c_insert {A : Set α} {x : α} (hx : x ∉ A) :
    n₀c (insert x A) = (n₀c A +ᶜ (one : Set (Set α)) : Set (Set α)) := by
  classical
  rw [one_eq_n₀c_singleton x, n₀c_cardAdd_n₀c, n₀c_eq_nc]
  apply nc_eq_nc_of_sm
  exact sm_iff_nonempty_equiv.2 ⟨(Equiv.Set.insert hx).trans
    (((Equiv.refl A).sumCongr (Equiv.Set.singleton x).symm).trans (clsSumEquiv A {x}).symm)⟩

/-- In a finite type, the successor of the greatest cardinal is `Λ`. -/
theorem n₀c_univ_cardAdd_one [Finite α] :
    (n₀c (Set.univ : Set α) +ᶜ (one : Set (Set α)) : Set (Set α)) = ∅ := by
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A', B', ⟨hA, hB⟩, h⟩
  have hA' : sm Set.univ A' := mem_n₀c.1 (hA ▸ self_mem_n₀c Set.univ)
  obtain ⟨y, rfl⟩ : B' ∈ one := hB ▸ self_mem_n₀c B'
  obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 hA'
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
  have h1 : Nat.card ξ = Nat.card α + 1 := by
    rw [Nat.card_congr (e.trans (clsSumEquiv A' (ι y))), Nat.card_sum,
      ← Nat.card_congr eA, Nat.card_univ, unitCls_eq_singleton,
      Nat.card_unique (α := ({y} : Set α))]
  have h2 : Nat.card ξ ≤ Nat.card α := Finite.card_subtype_le _
  omega

/-- The inductive cardinals are the cardinals of finite classes, and, in a finite type, `Λ`. -/
theorem NCinduct_cases {μ : Set (Set α)} (h : μ ∈ NCinduct) :
    (∃ A : Set α, A.Finite ∧ μ = n₀c A) ∨ (Finite α ∧ μ = ∅) := by
  classical
  induction mem_NCinduct_iff.1 h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl ⟨∅, Set.finite_empty, zero_eq_n₀c_empty⟩
  | head hab _ ih =>
    rw [plusC1_iff.1 hab]
    rcases ih (mem_NCinduct_iff.2 ‹_›) with ⟨A, hA, rfl⟩ | ⟨hfin, rfl⟩
    · by_cases hx : ∃ x, x ∉ A
      · obtain ⟨x, hx⟩ := hx
        exact Or.inl ⟨insert x A, hA.insert x, (n₀c_insert hx).symm⟩
      · push Not at hx
        have hAu : A = Set.univ := Set.eq_univ_of_forall hx
        subst hAu
        have : Finite α := Set.finite_univ_iff.1 hA
        exact Or.inr ⟨this, n₀c_univ_cardAdd_one⟩
    · exact Or.inr ⟨hfin, cardAdd_eq_empty_of_left (fun A h => n₀c_ne_empty A h.symm) _⟩

/-- `ρ` finite `⊃ N₀c'ρ ∈ NC induct` (cf. ✱120·21). -/
theorem n₀c_mem_NCinduct {A : Set α} (hA : A.Finite) : n₀c A ∈ NCinduct := by
  classical
  induction A, hA using Set.Finite.induction_on with
  | empty => rw [← zero_eq_n₀c_empty]; exact zero_mem_NCinduct
  | insert hx _ ih => rw [n₀c_insert hx]; exact cardAdd_one_mem_NCinduct ih

/-- The inductive classes are the finite classes (cf. ✱120·21). -/
theorem mem_ClsInduct {A : Set α} : A ∈ ClsInduct ↔ A.Finite := by
  constructor
  · rintro ⟨μ, hμ, hA⟩
    rcases NCinduct_cases hμ with ⟨B, hB, rfl⟩ | ⟨-, rfl⟩
    · obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (mem_n₀c.1 hA)
      have : Finite B := hB.to_subtype
      exact Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)
    · exact hA.elim
  · intro h
    exact ⟨n₀c A, n₀c_mem_NCinduct h, self_mem_n₀c A⟩

/-- The axiom of infinity in the type of classes of `α`-things is `Infinite α`. -/
theorem infinAx_iff_infinite : InfinAx α ↔ Infinite α := by
  constructor
  · intro h
    by_contra hinf
    have : Finite α := not_infinite_iff_finite.1 hinf
    have hmem := cardAdd_one_mem_NCinduct (n₀c_mem_NCinduct (Set.finite_univ (α := α)))
    have hne := h _ hmem
    rw [n₀c_univ_cardAdd_one] at hne
    exact Set.not_nonempty_empty hne
  · intro hinf μ hμ
    rcases NCinduct_cases hμ with ⟨A, -, rfl⟩ | ⟨hfin, -⟩
    · exact n₀c_nonempty A
    · exact absurd hfin (not_finite_iff_infinite.2 hinf)

/-- `Infin ax(x)` is `Infin ax` at the type of `x`. -/
theorem infinAxAt_iff (x : α) : InfinAxAt x ↔ InfinAx α := by
  have h : ∀ μ : Set (Set α), clsT2 μ x = μ := fun μ => by
    rw [clsT2, typ_eq_univ, Set.inter_univ]
  simp only [InfinAxAt, InfinAx, h]

/-! ### Descriptive functions of the relations of this Part -/

theorem desc_SigmaNc (K : Set (Set α)) (ψ : Set (Set γ) → Prop) :
    Desc (SigmaNc : Set (Set γ) → Set (Set α) → Prop) K ψ ↔ ψ (sigmaNc γ K) := desc_graph _ _ _

theorem desc_PiNc (K : Set (Set α)) (ψ : Set (Set γ) → Prop) :
    Desc (PiNc : Set (Set γ) → Set (Set α) → Prop) K ψ ↔ ψ (piNc γ K) := desc_graph _ _ _

theorem desc_ClsSigma (K : Set (Set α)) (ψ : Set (α → Set α → Prop) → Prop) :
    Desc ClsSigma K ψ ↔ ψ (clsSigma K) := desc_graph _ _ _

theorem desc_ProdK (K : Set (Set α)) (ψ : Set (Set α) → Prop) : Desc ProdK K ψ ↔ ψ (prodK K) :=
  desc_graph _ _ _

/-- `ψ(Crp(S)'β) ↔ ψ((S'β) sm̄ β)`, the description `S'β` having the larger scope. -/
theorem desc_Crp (S : Set α → Set β → Prop) (B : Set β) (ψ : Set (α → β → Prop) → Prop) :
    Desc (Crp S) B ψ ↔ Desc S B (fun A => ψ (smbar A B)) := by
  have : Crp S = descRel (fun U B => Desc S B (fun A => U = smbar A B)) := by
    funext U B'
    apply propext
    show Desc S B' (fun A => U = smbar A B') ↔ _
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact ⟨smbar A B', fun V => ⟨fun ⟨A', hA', hV⟩ => by
        rw [hV, show A' = A from (hA A').1 ((hA' A').2 rfl)], fun hV => ⟨A, hA, hV⟩⟩, rfl⟩
    · rintro ⟨V, hV, hUV⟩
      obtain ⟨A, hA, hV'⟩ := (hV V).2 rfl
      exact ⟨A, hA, hUV.trans hV'⟩
  rw [this, desc_descRel]
  constructor
  · rintro ⟨V, hV, hψ⟩
    obtain ⟨A, hA, rfl⟩ := (hV V).2 rfl
    exact ⟨A, hA, hψ⟩
  · rintro ⟨A, hA, hψ⟩
    refine ⟨smbar A B, fun V => ⟨fun ⟨A', hA', hV⟩ => ?_, fun hV => ⟨A, hA, hV⟩⟩, hψ⟩
    rw [hV, show A' = A from (hA A').1 ((hA' A').2 rfl)]

/-- `ψ(ν_P) ↔ ψ((P_{ν−_c1})˘'B'P)` (✱121·04 with ✱30·02; then `desc2_iff`). -/
theorem desc_nuP (ν : Set (Set β)) (P : α → α → Prop) (ψ : α → Prop) :
    Desc (nuP ν) P ψ ↔ Desc2 (Pnu P (ν -ᶜ (one : Set (Set β)) : Set (Set β)))˘ Beg P ψ :=
  desc_descRel _ _ _

/-- `α ∈ ℵ₀ . ≡ . (∃R) . R ∈ Prog . α = D'R` (✱123·1). -/
theorem mem_aleph0 {A : Set α} : A ∈ aleph0 ↔ ∃ R, R ∈ Prog ∧ D A R := Iff.rfl

/-- The precedences realize PM's bracketing of class-sums and class-products (✱110·531,
✱113·511). (Inner arithmetical formal numbers need a type ascription: encoding decision 6.) -/
example (A : Set α) (B : Set β) (G : Set γ) :
    (A +ₐ B +ₐ G = (A +ₐ B) +ₐ G) ∧ (A ×ₐ B ×ₐ G = (A ×ₐ B) ×ₐ G) ∧
    (A +ₐ B ×ₐ G = A +ₐ (B ×ₐ G)) :=
  ⟨rfl, rfl, rfl⟩

end Sanity

/-! ## Worked examples of the type conventions

The Section files state these as the declarations `pmN_M` (`Part3/SectionA.lean` has
✱100·01·02·1·2·3·35·4·42·511 as finished declarations, with the AT form of ✱100·35). They are
`example`s here so that the names `pmN_M` stay free for the Section files. -/

section WorkedExamples

/-- **✱110·3** \(\vdash .\text{Nc}ʻ\alpha +_{\text{c}}\text{Nc}ʻ\beta = \text{N}_{0}\text{c}ʻ\alpha +_{\text{c}}\text{N}_{0}\text{c}ʻ\beta = \text{Nc}ʻ(\alpha +\beta )\)
(normal adjustment, encoding decision 5). The arguments `Nc'α`, `Nc'β` of `+_c` are `n₀c A`,
`n₀c B` by ✱110·03·04, so the first link is the Df itself; the opposed sides of the equation
are in one type `γ` ("meaning"), which is otherwise free. The chain is the conjunction of its
links. Copy as `theorem pm110_3 {A : Set α} {B : Set β} : …` with
**Status.** `proved (reading): by the Dfs ✱110·03·04 the arguments Nc'α, Nc'β of +_c are read
N₀c'α, N₀c'β, so the first equation is the identity of the two readings`. -/
example {A : Set α} {B : Set β} :
    (n₀c A +ᶜ n₀c B : Set (Set γ)) = n₀c A +ᶜ n₀c B ∧
      (n₀c A +ᶜ n₀c B : Set (Set γ)) = nc γ (A +ₐ B) :=
  ⟨rfl, n₀c_cardAdd_n₀c A B⟩

/-- **✱110·56** \(\vdash .(\mu +_{c}\nu ) +_{c}\varpi = \mu +_{c}(\nu +_{c}\varpi )\) (convention
IIT, encoding decision 6). The real variables `μ`, `ν`, `ϖ` have independent types (assigned
first). The inner sums are arithmetical components: each gets its own type (`W₁`, `W₂`) and the
hypothesis that it is adequate; the two sides of the equation share the type `γ` ("meaning").
Copy as `theorem pm110_56 …` with
**Status.** `proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components μ +_c ν and ν +_c ϖ are adequate`. -/
example {α₁ α₂ α₃ W₁ W₂ : Type*} {μ : Set (Set α₁)} {ν : Set (Set α₂)} {ϖ : Set (Set α₃)}
    (h₁ : AdeqAdd W₁ μ ν) (h₂ : AdeqAdd W₂ ν ϖ) :
    ((μ +ᶜ ν : Set (Set W₁)) +ᶜ ϖ : Set (Set γ)) = μ +ᶜ (ν +ᶜ ϖ : Set (Set W₂)) := by
  by_cases hμ : ∃ A, μ = n₀c A
  · by_cases hν : ∃ B, ν = n₀c B
    · by_cases hϖ : ∃ C, ϖ = n₀c C
      · obtain ⟨A, rfl⟩ := hμ; obtain ⟨B, rfl⟩ := hν; obtain ⟨C, rfl⟩ := hϖ
        obtain ⟨X, hX⟩ := h₁.nc_nonempty A B
        obtain ⟨Y, hY⟩ := h₂.nc_nonempty B C
        rw [n₀c_cardAdd_n₀c, nc_eq_n₀c_of_mem hX, n₀c_cardAdd_n₀c, n₀c_cardAdd_n₀c,
          nc_eq_n₀c_of_mem hY, n₀c_cardAdd_n₀c]
        exact nc_eq_nc_of_sm (sm_trans (sm_clsSum hX (sm_refl C))
          (sm_trans (sm_clsSum_assoc A B C) (sm_clsSum (sm_refl A) (sm_symm hY))))
      · push Not at hϖ
        rw [cardAdd_eq_empty_of_right _ hϖ, cardAdd_eq_empty_of_right (ν := ϖ) _ hϖ,
          cardAdd_eq_empty_of_right _ (fun X h => n₀c_ne_empty X h.symm)]
    · push Not at hν
      rw [cardAdd_eq_empty_of_right (ν := ν) _ hν, cardAdd_eq_empty_of_left (μ := ν) hν,
        cardAdd_eq_empty_of_left (fun X h => n₀c_ne_empty X h.symm),
        cardAdd_eq_empty_of_right _ (fun X h => n₀c_ne_empty X h.symm)]
  · push Not at hμ
    rw [cardAdd_eq_empty_of_left (μ := μ) hμ, cardAdd_eq_empty_of_left (μ := μ) hμ,
      cardAdd_eq_empty_of_left (fun X h => n₀c_ne_empty X h.symm)]

/-- Without IIT ✱110·56 is false: with the inner sum `1 +_c 0` in a type with no members it is
`Λ`, while `1 +_c (0 +_c 0)` (all in `Bool`) is not. -/
example : ¬ ∀ {μ ν ϖ : Set (Set Bool)},
    ((μ +ᶜ ν : Set (Set Empty)) +ᶜ ϖ : Set (Set Bool)) = μ +ᶜ (ν +ᶜ ϖ : Set (Set Bool)) := by
  intro h
  have e := @h (n₀c {true}) (n₀c ∅) (n₀c ∅)
  rw [n₀c_cardAdd_n₀c, nc_eq_empty_of_isEmpty ⟨_, ((clsSumEquiv _ _).symm (Sum.inl ⟨true, rfl⟩)).2⟩,
    cardAdd_eq_empty_of_left (fun X hX => n₀c_ne_empty X hX.symm)] at e
  have hin : ({true} : Set Bool) ∈ (n₀c ({true} : Set Bool) +ᶜ
      (n₀c (∅ : Set Bool) +ᶜ n₀c (∅ : Set Bool) : Set (Set Bool)) : Set (Set Bool)) := by
    rw [n₀c_cardAdd_n₀c (A := (∅ : Set Bool)),
      nc_eq_n₀c_of_mem (sm_iff_nonempty_equiv.2 ⟨((clsSumEquiv (∅ : Set Bool)
        (∅ : Set Bool)).trans (Equiv.sumEmpty _ _)).symm⟩ :
          (∅ : Set Bool) ∈ nc Bool ((∅ : Set Bool) +ₐ (∅ : Set Bool))),
      n₀c_cardAdd_n₀c]
    exact sm_iff_nonempty_equiv.2 ⟨((clsSumEquiv _ _).trans (Equiv.sumEmpty _ _)).symm⟩
  rw [← e] at hin
  exact hin

/-- **✱110·643** \(\vdash .1+_{c}1=2\) (constant formal numbers under IIT). The two `1`s are
arithmetical occurrences (IT does not bind them): each has its own type with the IIT hypothesis
`∃!1` (here `[Nonempty W]`); the equation is in a free type `γ` (in which `2` may be `Λ`, and
then so is `1 +_c 1`). Copy as `theorem pm110_643 …` with
**Status.** `proved (reading): convention IIT (Prefatory Statement, IV): the 1s are taken in types
in which they exist (PM assumes every type has a member, Introduction, Ch. I)`. -/
example {W₁ W₂ : Type*} [Nonempty W₁] [Nonempty W₂] :
    ((one : Set (Set W₁)) +ᶜ (one : Set (Set W₂)) : Set (Set γ)) = two := by
  obtain ⟨a⟩ := ‹Nonempty W₁›
  obtain ⟨b⟩ := ‹Nonempty W₂›
  rw [one_eq_n₀c_singleton a, one_eq_n₀c_singleton b, n₀c_cardAdd_n₀c]
  have hc : Nat.card ↥(({a} : Set W₁) +ₐ ({b} : Set W₂)) = 2 := by
    rw [Nat.card_congr (clsSumEquiv _ _), Nat.card_sum]; simp
  have hfin : Finite ↥(({a} : Set W₁) +ₐ ({b} : Set W₂)) :=
    Finite.of_equiv _ (clsSumEquiv _ _).symm
  ext X
  rw [mem_nc_iff_equiv]
  constructor
  · rintro ⟨e⟩
    have h2 : X.ncard = 2 := by rw [← Nat.card_coe_set_eq, Nat.card_congr e, hc]
    obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.1 h2
    exact ⟨x, y, hxy, by rw [unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]⟩
  · rintro ⟨x, y, hxy, rfl⟩
    rw [unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]
    have : Finite ↥({x, y} : Set γ) := Set.toFinite _
    apply Finite.card_eq.1
    rw [Nat.card_coe_set_eq, Set.ncard_pair hxy, hc]

/-- **✱103·16** \(\vdash : \text{N}_{0}\text{c}ʻ\alpha = \text{Nc}ʻ\beta . \equiv . \text{Nc}ʻ\alpha = \text{Nc}ʻ\beta\)
(convention AT: "the equation `Nc'α = Nc'β` must be supposed to hold in any type for which it is
significant"). The `Nc'β` of the first equation is in the type of `α` (meaning); the second
equation is in a type `γ` adequate for both sides. Copy as `theorem pm103_16 …` with
**Status.** `proved (reading): convention AT (Prefatory Statement, VI): the equation
Nc'α = Nc'β is taken in a type adequate for both sides`. -/
example {A : Set α} {B : Set β} (hA : AdeqNc γ A) (_hB : AdeqNc γ B) :
    n₀c A = nc α B ↔ nc γ A = nc γ B := by
  rw [n₀c_eq_nc, nc_eq_nc_iff ⟨A, self_mem_nc A⟩, nc_eq_nc_iff (hA.nc_nonempty A)]

/-- **✱117·108** \(\vdash \colon\ldotp \text{Nc}ʻ\alpha \geq \text{Nc}ʻ\beta . \equiv : \text{Nc}ʻ\alpha > \text{Nc}ʻ\beta . \lor . \text{Nc}ʻ\alpha = \text{Nc}ʻ\beta\)
(normal adjustment and AT; PM's own example in the Prefatory Statement, III–IV). The sides of
`≥`, `>` are `n₀c A`, `n₀c B` (✱117·02·03 and PM's note to ✱117·06); the equation is in a type
`γ` adequate for both sides (AT). Copy as `theorem pm117_108 …` with
**Status.** `proved (reading): convention AT (Prefatory Statement, VI); the arithmetical
occurrences of Nc'α, Nc'β are N₀c'α, N₀c'β by ✱117·02·03`. -/
example {A : Set α} {B : Set β} (hA : AdeqNc γ A) (_hB : AdeqNc γ B) :
    n₀c A ≥ᶜ n₀c B ↔ n₀c A >ᶜ n₀c B ∨ nc γ A = nc γ B := by
  have key : n₀c A = sm ʻʻ n₀c B ↔ nc γ A = nc γ B := by
    rw [sm_img_n₀c, n₀c_eq_nc, nc_eq_nc_iff ⟨A, self_mem_nc A⟩,
      nc_eq_nc_iff (hA.nc_nonempty A)]
  exact or_congr Iff.rfl ⟨fun h => key.1 h.2, fun h => ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, key.2 h⟩⟩

/-- **✱120·3** \(\vdash \colon\ldotp \text{Infin ax}.\equiv :\alpha \in \text{NC induct}.\supset _{\alpha }.\exists !\alpha\)
`Infin ax` and `NC induct` are at the same type (the types of the cardinals `α` of the
enunciation), a type parameter of the theorem. Copy as `theorem pm120_3 : InfinAx α ↔ …`. -/
example : InfinAx α ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → μ.Nonempty := Iff.rfl

/-- **✱120·301** \(\vdash \colon\ldotp \text{Infin ax}(x).\equiv :\alpha \in \text{NC induct}.\supset _{\alpha }.\exists !\alpha (x)\)
`Infin ax(x)` is at the type of `x`. -/
example (x : α) : InfinAxAt x ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → (clsT2 μ x).Nonempty :=
  Iff.rfl

/-- **✱125·13** \(\vdash :\text{Infin ax}.\equiv .\Lambda {\sim}\in \text{NC induct}\)
`Λ` is the null class of the type of the inductive cardinals. -/
example : InfinAx α ↔ (Λ : Set (Set α)) ∉ NCinduct := by
  rw [Null_eq_empty]
  constructor
  · intro h hΛ
    exact Set.not_nonempty_empty (h _ hΛ)
  · intro h μ hμ
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact h hμ

/-- **✱123·18** \(\vdash :\exists !\aleph _{0}(x).\supset .\text{Infin ax}(x)\): the typically
definite `ℵ₀(x)` is `ℵ₀ ∩ t't'x` (✱65·02, `clsT2 aleph0 x`). The statement is: -/
example : Prop := ∀ x : α, (clsT2 aleph0 x).Nonempty → InfinAxAt x

/-- **✱123·43** \(\vdash \colon\ldotp \exists !\aleph _{0}.\supset :\nu \in \text{NC induct}.\supset _{\nu }.\aleph _{0}>\nu\)
(convention Infin T, encoding decision 8). `ℵ₀` is a constant in a type `α` (parameter, with the
hypothesis `∃!ℵ₀` as printed); the type of the apparent variable `ν`, i.e. of `NC induct`, is
determined by nothing, so it is a parameter `X`, and since `∃!ℵ₀` implies that some type has
every inductive cardinal, Infin T takes it with `InfinAx X`. The statement (to be proved in
✱123 with **Status.** `proved (reading): convention Infin T (Prefatory Statement, VI)`) is: -/
example : Prop :=
  ∀ {X : Type w}, InfinAx X → (aleph0 : Set (Set α)).Nonempty →
    ∀ ν : Set (Set X), ν ∈ NCinduct → (aleph0 : Set (Set α)) >ᶜ ν

/-- The hypothesis `InfinAx X` of ✱123·43 cannot be dropped: in a finite type `Λ` is an inductive
cardinal (✱125·13), and `ℵ₀ > Λ` is false (✱117·01). -/
example {X : Type w} [Finite X] :
    (∅ : Set (Set X)) ∈ NCinduct ∧ ¬ ((aleph0 : Set (Set α)) >ᶜ (∅ : Set (Set X))) := by
  refine ⟨?_, ?_⟩
  · by_contra h
    have hi : InfinAx X := by
      intro μ hμ
      rw [Set.nonempty_iff_ne_empty]
      rintro rfl
      exact h hμ
    exact (not_infinite_iff_finite.2 ‹Finite X›) (infinAx_iff_infinite.1 hi)
  · rintro ⟨A, B, ⟨⟨-, hB⟩, -⟩, -⟩
    exact n₀c_ne_empty B hB.symm

end WorkedExamples

end PrincipiaMathematica
