import PrincipiaMathematica.Defs.Part1
import Mathlib.Logic.Relation
import Mathlib.Logic.Equiv.Defs

/-!
# Part II (Prolegomena to cardinal arithmetic): the definitions

Every definition (Df, and the temporary definitions Dft of ✱95 and ✱96) of ✱50–✱97, in PM's
order, in the format of `Defs/Part1.lean`: each entry is headed `**✱N·M Df.**` with the formula as
printed (MathJax TeX, from `data/principia.json`), says how it is read in Lean, and gives the
*target statement* of `pmN_M` (status `definition` unless said otherwise; every target below has
been checked to elaborate and to hold by the indicated proof). The file ends with sanity lemmas
(ι'x is `{x}`, one-many relations, similarity is an equivalence and is `Nonempty (A ≃ B)`, the
ancestral is the reflexive-transitive closure restricted to the field, `R_po` is the transitive
closure, `Mult ax` is provable by choice, …) that the Section agents may use.

## Encoding decisions (in addition to Basic §1–§10)

* *Descriptive functions.* Every relation of this Part whose descriptive function always exists is
  `graph f` for its value function `f` (Basic §5), and in formulas `F'x` is written `f x`:
  `ι'x` is `ι x`, `Cl'α` is `cl A`, `t'x` is `typ x`, `P_Δ'κ` is `sel P K`, `Pot'R` is `pot R`,
  `gen'P` is `gen P`, `R⃡'x` is `refsRels R x`, … . Relations whose descriptive function may fail
  to exist are *not* functions: `ῐ` (`iota˘`; `ῐ'α`, "the only member of α", is
  `Desc iota˘ A ψ`, see `desc_iota_cnv`), `B` (`Beg`; `B'P` is `Desc Beg P ψ`), `min_P`, `max_P`
  (`minP P`, `maxP P`; `min_P'α` is `Desc (minP P) A ψ`). (The Dfts ✱96·01·02 define the
  descriptive functions `I_R'x`, `J_R'x` directly; their values always exist, so they are the
  functions `IR R x`, `JR R x`.)
  A Df of the form `X = F'Y` whose definiendum is a constant term and whose definiens is a
  descriptive function of a constant (✱54·01, ✱56·03, ✱60·03·04, ✱61·03·04, ✱90·02, ✱95·01; and
  ✱91·05 `R_po = ṡ'Pot'R`, where `Pot'R` is kept) is stated with `Desc` (Basic §5, as ✱37·03);
  a Df that itself defines a descriptive function (`Cl'α`, `Pot'R`, `gen'P`, `R⃡'x`, …) is the
  equation of its value function.
* *Rewriting descriptions.* The relations above are `def`s equal to `graph f`, so `rw [desc_graph]`
  does not see through them: use the lemmas `desc_iota`, `desc_Cl`, `desc_ClEx`, `desc_Rl`,
  `desc_RlEx`, `desc_coupleL`, `desc_coupleR`, `desc_selRel`, `desc_ClExcl`, `desc_Pot`,
  `desc_Potid`, `desc_Gen`, `desc_Rboth`, `desc_eqf` (end of file), or `(desc_graph f _ _)` as a
  term. Where PM proves that such a descriptive function exists or what its value is (✱51·11·12,
  ✱55·11·12·121, ✱60·12–·15, ✱61·12–·15, ✱80·11–·13, …), state it with `Desc`/`EDesc`
  (Basic §5, exception), e.g. ✱60·12 `Desc Cl A (fun K => K = {B | B ⊆ A})`.
* *Typical ambiguity.* `1`, `0`, `2`, `2̇`, `2_r`, `0_r`, `Cls²`, `Rel²`, `Cls² excl`, `1 → 1`,
  `sm`, `Rel Mult`, `Mult ax`, … are polymorphic constants; their type is fixed by the context
  (Basic §4). `Mult ax` takes the type explicitly: `MultAx α` is the multiplicative axiom for
  classes of classes of `α`-things; state it at the type PM's enunciation determines.
* *Relative types* (✱63–✱65). PM's `t'x` ("the type of x") is defined as PM defines it,
  `ι'x ∪ −ι'x`, and is then `Set.univ : Set α` (`typ_eq_univ`); likewise every `t…` of ✱63–✱64 is
  `Set.univ` of the appropriate Lean type, and the "typically definite" symbols `α_x`, `R_x`, … of
  ✱65 are `α ∩ t'x`, `t'x ↿ R`, …, which equal `α`, `R` (`clsT_eq`, …): in Lean the type of a
  symbol is always definite, and these notations become explicit typings. The types of
  `t'x`, `t²'x`, `t₀'α`, `t₁'κ`, … are forced by Lean's typing exactly as PM describes (e.g.
  `typ₁ : Set (Set α) → Set α`, "the type next below that in which κ is contained").
* *Homogeneity.* `C'R` needs a homogeneous `R`, so `R_*`, `R_po`, `Pot'R`, `B`, `min_P`, `gen'P`,
  `I_R`, `R⃡` take `R : α → α → Prop`. `2̇` and `x ↓ y` are heterogeneous; `2_r` (which needs
  `x ≠ y`) is homogeneous.
* *Converse conventions.* `R̆_*` is `ancCnv R`, i.e. `(anc R)˘` (✱90·02), not `anc R˘` (✱90·132
  proves them equal). `R⃗_*'x` is `refs (anc R) x` (the ancestors of `x`), `R⃖_*'x` is
  `rels (anc R) x` (the posterity of `x`), `R⃡_*'x` is `refsRels (anc R) x` (its family).
* *Membership as a relation* (✱62·01). PM's relation `∈` is `memRel`; Lean's `x ∈ A` keeps its
  meaning (`memRel x A ↔ x ∈ A` by `Iff.rfl`). So `∈_Δ'κ` is `sel memRel K`, `∈⃖'Λ` is
  `rels memRel Λ`, `∈ ↾ κ` is `memRel ↾ K`, `ε''κ` is `memRel ʻʻ K`.
* *Names that shadow.* The scoped token `ι` (prefix, for `ι'x`) makes `ι` unusable as a variable
  name in files that open the namespace; PM never uses `ι` as a variable. Do not bind variables
  named `I`, `J`, `Beg`, `one`, `two`, `zero`, … (they would shadow these definitions).
  The relation `ι` itself (as in `ι''α`, `ῐ`, `ι ↾ α`) is `iota`: `iota ʻʻ A`, `iota˘`.

## Symbol table: PM → Lean (extends Basic §7)

| PM | Df | Lean |
|----|----|------|
| `I`, `J` | ✱50·01·02 | `I`, `J` (`I x y ↔ x = y`, `J x y ↔ x ≠ y`) |
| `ι` (relation), `ι'x`, `ῐ`, `ῐ'α` | ✱51·01 | `iota`, `ι x` (`unitCls x`, `= {x}`), `iota˘`, `Desc iota˘ A ψ` |
| `1`, `0`, `2` | ✱52·01, ✱54·01·02 | `one`, `zero`, `two` (each `: Set (Set α)`) |
| `x ↓ y`, `x↓`, `↓y`, `α ↓,, y` | ✱55·01, ✱38 | `x ↓ y` (`couple`), `coupleL x`, `coupleR y`, `coupleR y ʻʻ A` |
| `R'x↓y` | ✱55·02 | `Desc R (x ↓ y) ψ` |
| `2̇`, `2_r`, `0_r` | ✱56·01–·03 | `twoDot`, `two_r`, `zero_r` |
| `Cl`, `Cl'α`, `Cl ex`, `Cl ex'α` | ✱60·01·02 | `Cl`, `cl A` (`= 𝒫 A`), `ClEx`, `clEx A` |
| `Cls²`, `Cls³` | ✱60·03·04 | `Cls2`, `Cls3` |
| `Rl`, `Rl'P`, `Rl ex`, `Rl ex'P` | ✱61·01·02 | `Rl`, `rl P`, `RlEx`, `rlEx P` |
| `Rel²`, `Rel³` | ✱61·03·04 | `Rel2`, `Rel3` |
| `∈` (relation) | ✱62·01 | `memRel` |
| `t'x`, `t¹'x`, `t²'x`, `t³'x` | ✱63·01·011·04·041 | `typ x`, `typ1 x`, `typ2 x`, `typ3 x` |
| `t₀'α`, `t₁'κ`, `t₂'κ`, `t₃'κ` | ✱63·02·03·05·051 | `typ₀ A`, `typ₁ K`, `typ₂ K`, `typ₃ K` |
| `t₀₀'α`, `t^{mn}'x`, `t_{mn}'α`, `t_m^n'α`, `^m t_n'α` | ✱64·01–·041 | `typ₀₀ A`, `typ11 x` …, `typ₀₁ A` …, `typ₀1 A` …, `typ1₀ A` … |
| `α_x`, `α(x)` | ✱65·01·02 | `clsT A x`, `clsT2 A x` |
| `R_x`, `R(x)`, `R_{(x,y)}`, `R(x_y)`, `R(x,y)` | ✱65·03·04·1·11·12 | `relT R x`, `relT2 R x`, `relTT R x y`, `relT2T R x y`, `relT2T2 R x y` |
| `α → β`; `1 → Cls`, `Cls → 1`, `1 → 1` | ✱70·01 | `arrow A B`; `arrow one Cls`, `arrow Cls one`, `arrow one one` |
| `α sm̄ β`, `sm` | ✱73·01·02 | `smbar A B`, `sm A B` |
| `P_Δ`, `P_Δ'κ`, `∈_Δ'κ` | ✱80·01 | `selRel P`, `sel P K`, `sel memRel K` |
| `Cls² excl`, `Cl excl'γ`, `Cls ex² excl` | ✱84·01–·03 | `Cls2excl`, `clExcl G` (relation `ClExcl`), `ClsEx2excl` |
| `P ↧ y`, `P↧` | ✱85·5 | `P ↧ y` (`downCls`), `opL downCls P` |
| `Rel Mult`, `Cls² Mult`, `Mult ax` | ✱88·01–·03 | `RelMult`, `Cls2Mult`, `MultAx α` |
| `R_*`, `R̆_*` | ✱90·01·02 | `anc R`, `ancCnv R` (`= (anc R)˘`) |
| `R_st`, `R_ts` | ✱91·01·02 | `Rst R`, `Rts R` |
| `Pot`, `Pot'R`, `Potid`, `Potid'R`, `R_po` | ✱91·03–·05 | `Pot`, `pot R`, `Potid`, `potid R`, `po R` |
| `B`, `min_P` (`min(P)`), `max_P` (`max(P)`) | ✱93·01·02·021 | `Beg`, `minP P`, `maxP P` |
| `gen`, `gen'P` | ✱93·03 | `Gen`, `gen P` |
| `(P∗Q)` (Dft, ✱95 only) | ✱95·01 | `eqf P Q` |
| `I_R'x`, `J_R'x` (Dft, ✱96 only) | ✱96·01·02 | `IR R x`, `JR R x` |
| `R⃡`, `R⃡'x` | ✱97·01 | `Rboth R`, `refsRels R x` |

Precedences: prefix `ι` max (so `ι x ∪ ι y` is `(ι x) ∪ (ι y)`; write `ι (f x)`, `(ι x)ᶜ`);
`↓` and `↧` 78 (non-associative), i.e. tighter than `◁` (75), `⨾` (70), `↾` (68), `⩀`, `⊍`, `∸`,
`∪`, `∩` and looser than `ʻʻ` (80) and application, so that `x ↓ y ⊍ z ↓ w` is
`(x ↓ y) ⊍ (z ↓ w)` (✱55·5) and `R ⨾ x ↓ y` is `R ⨾ (x ↓ y)`. `arrow`, `sm`, … are plain names.
In ✱93·02 write `(A ∩ fld P) \ P˘ ʻʻ A` with the brackets (Lean's `∩` and `\` do not mix).
-/

namespace PrincipiaMathematica

universe u v w u' v' w' u'' v''

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

/-! ## Section A: unit classes and couples (✱50–✱56) -/

/-- **✱50·01 Df.** \(I=\hat{x}\hat{y}(x=y) \quad\text{Df}\)

The relation of identity (homogeneous). `I'y` always exists and is `y` (`desc_I`). Target:
`pm50_01 : (I : α → α → Prop) = fun x y => x = y := rfl`. -/
def I : α → α → Prop := fun x y => x = y

/-- **✱50·02 Df.** \(J=\dot{-}I \quad\text{Df}\)

Diversity, the negation of identity. Target: `pm50_02 : (J : α → α → Prop) = ∸I := rfl`. -/
def J : α → α → Prop := ∸I

/-- `ι'x`, the unit class `ŷ(y = x)` whose only member is `x`, i.e. `I⃗'x` (Summary of ✱51). Value
function of `iota`; notation `ι x`. It is `{x}` (`unitCls_eq_singleton`). -/
def unitCls (x : α) : Set α := refs I x

@[inherit_doc] scoped prefix:max "ι" => unitCls

/-- **✱51·01 Df.** \(\iota=\overrightarrow{I} \quad\text{Df}\)

The relation `ι` of `ι'x` to `x`. `ι'x` is `ι x` (`desc_iota`); `ι''α` is `iota ʻʻ A`; the
converse `ῐ` is `iota˘`, whose descriptive function `ῐ'α` ("the only member of α") exists only when
`α` is a unit class: `ψ(ῐ'α)` is `Desc iota˘ A ψ` (`desc_iota_cnv`). Target:
`pm51_01 : (iota : Set α → α → Prop) = Rfwd I := rfl`. -/
def iota : Set α → α → Prop := Rfwd I

/-- **✱52·01 Df.** \(\hat{\alpha }\{(\exists x) \ldotp \alpha = \iota ʻx\}\quad \text{Df}\)

(The e-text omits the definiendum: PM has `1 = α̂{(∃x) . α = ι'x} Df`, as the Summary of ✱52, the
Summary of Section A and ✱52·1 show.) The cardinal number 1, the class of unit classes (of the
type in question). Target (status `definition`; mention the transcription error):
`pm52_01 : (one : Set (Set α)) = {A | ∃ x, A = ι x} := rfl`. -/
def one : Set (Set α) := {A | ∃ x, A = ι x}

/-- **✱54·01 Df.** \(0=\iotaʻ\Lambda \quad\text{Df}\)

The cardinal number 0, the class whose only member is `Λ`. The definiens is a descriptive function,
so the target keeps it (Basic §5): `pm54_01 : Desc iota Λ (fun K => (zero : Set (Set α)) = K) :=
(desc_graph _ _ _).2 rfl`. (`zero_eq : zero = {∅}`.) -/
def zero : Set (Set α) := ι Λ

/-- **✱54·02 Df.** \(2=\hat{\alpha}\{(\exists x,y).x\neq y.\alpha=\iotaʻx\cup \iotaʻy\} \quad\text{Df}\)

The cardinal number 2, the class of cardinal couples. Target:
`pm54_02 : (two : Set (Set α)) = {A | ∃ x y, x ≠ y ∧ A = ι x ∪ ι y} := rfl`. -/
def two : Set (Set α) := {A | ∃ x y, x ≠ y ∧ A = ι x ∪ ι y}

/-- **✱55·01 Df.** \(x\downarrow y=\iotaʻx\uparrow \iotaʻy \quad\text{Df}\)

The ordinal couple `x ↓ y` (heterogeneous: `x : α`, `y : β`), the relation which holds only
between `x` and `y` (`couple_apply`). By ✱38 it gives the relations `x↓` (`coupleL x`, of `x ↓ y`
to `y`) and `↓y` (`coupleR y`, of `x ↓ y` to `x`); `x↓''β` is `coupleL x ʻʻ B`, `↓y''α` (=
`α ↓,, y`) is `coupleR y ʻʻ A`. Target: `pm55_01 : x ↓ y = cross (ι x) (ι y) := rfl`. -/
def couple (x : α) (y : β) : α → β → Prop := cross (ι x) (ι y)

@[inherit_doc] scoped infix:78 " ↓ " => couple

/-- `x↓` (✱38·01 with `♀ = ↓`): the relation of `x ↓ y` to `y`. Not a separate Df. -/
def coupleL (x : α) : (α → β → Prop) → β → Prop := opL couple x

/-- `↓y` (✱38·02 with `♀ = ↓`): the relation of `x ↓ y` to `x`. Not a separate Df. -/
def coupleR (y : β) : (α → β → Prop) → α → Prop := opR couple y

/-!
**✱55·02 Df.** \(Rʻx\downarrow y=Rʻ(x\downarrow y) \quad\text{Df}\)

Bracketing convention ("merely for the avoidance of brackets"): `R'x↓y` is the descriptive
function `R'` applied to the couple `x ↓ y`, not `(R'x) ↓ y`. With descriptions, `ψ(R'x↓y)` is
`Desc R (x ↓ y) ψ`; with a value function, write the bracket: `D'x↓y` (✱55·15) is
`dom (x ↓ y)` (`dom x ↓ y` would be `(dom x) ↓ y`). Target (status `definition`), with
`R : γ → (α → β → Prop) → Prop`:
`pm55_02 : Desc R (x ↓ y) ψ ↔ TheIs (fun u => R u (x ↓ y)) ψ := Iff.rfl`.
-/

/-- **✱56·01 Df.** \(\dot{2}=\hat{R}\{(\exists x,y).R=x\downarrow y\} \text{Df}\)

The class of relations consisting of a single couple (not an ordinal number). Target:
`pm56_01 : (twoDot : Set (α → β → Prop)) = {R | ∃ x y, R = x ↓ y} := rfl`. -/
def twoDot : Set (α → β → Prop) := {R | ∃ x y, R = x ↓ y}

/-- **✱56·02 Df.** \(2_{r}=\hat{R}\{(\exists x,y).x \neq y.R=x\downarrow y\} \text{Df}\)

The ordinal number `2_r` (homogeneous, since `x ≠ y`). Target:
`pm56_02 : (two_r : Set (α → α → Prop)) = {R | ∃ x y, x ≠ y ∧ R = x ↓ y} := rfl`. -/
def two_r : Set (α → α → Prop) := {R | ∃ x y, x ≠ y ∧ R = x ↓ y}

/-- **✱56·03 Df.** \(0_{r}=\iotaʻ\dot{\Lambda} \text{Df}\)

The relation-number `0_r`, the class whose only member is `Λ̇`. Target (definiens is a descriptive
function, Basic §5):
`pm56_03 : Desc iota rNull (fun L => (zero_r : Set (α → β → Prop)) = L) := (desc_graph _ _ _).2 rfl`. -/
def zero_r : Set (α → β → Prop) := ι rNull

/-! ## Section B: sub-classes, sub-relations, and relative types (✱60–✱65) -/

/-- `Cl'α`, the class `β̂(β ⊂ α)` of sub-classes of `α`; it is `𝒫 A` (`cl_eq_powerset`). Value
function of `Cl`. -/
def cl (A : Set α) : Set (Set α) := {B | B ⊆ A}

/-- `Cl ex'α`, the class `β̂(β ⊂ α . ∃!β)` of existent sub-classes of `α`. Value function of
`ClEx`. -/
def clEx (A : Set α) : Set (Set α) := {B | B ⊆ A ∧ B.Nonempty}

/-- **✱60·01 Df.** \(\text{Cl}=\hat{\kappa}\hat{\alpha}\{\kappa=\hat{\beta}(\beta\subset \alpha)\} \quad\text{Df}\)

The relation `Cl` of the class of sub-classes of `α` to `α`; `Cl'α` is `cl A`. Target:
`pm60_01 : (Cl : Set (Set α) → Set α → Prop) = fun K A => K = {B | B ⊆ A} := rfl`. -/
def Cl : Set (Set α) → Set α → Prop := graph cl

/-- **✱60·02 Df.** \(\text{Cl ex}=\hat{\kappa}\hat{\alpha}\{\kappa=\hat{\beta}(\beta\subset \alpha.\exists !\beta)\} \quad\text{Df}\)

The relation `Cl ex` of the class of existent sub-classes of `α` to `α`; `Cl ex'α` is `clEx A`.
Target: `pm60_02 : (ClEx : Set (Set α) → Set α → Prop) = fun K A => K = {B | B ⊆ A ∧ B.Nonempty} :=
rfl`. -/
def ClEx : Set (Set α) → Set α → Prop := graph clEx

/-- **✱60·03 Df.** \(\text{Cls}^{2}=\text{Cl}ʻ\text{Cls} \quad\text{Df}\)

The class of classes of classes (all of `Set (Set α)`). Target (definiens a descriptive function):
`pm60_03 : Desc Cl Cls (fun K => (Cls2 : Set (Set (Set α))) = K) := (desc_graph _ _ _).2 rfl`. -/
def Cls2 : Set (Set (Set α)) := cl Cls

/-- **✱60·04 Df.** \(\text{Cls}^{3} = \text{Cl}ʻ\text{Cls}^{2} \quad\text{Df}\)

Target: `pm60_04 : Desc Cl Cls2 (fun K => (Cls3 : Set (Set (Set (Set α)))) = K) :=
(desc_graph _ _ _).2 rfl`. -/
def Cls3 : Set (Set (Set (Set α))) := cl Cls2

/-- `Rl'P`, the class `R̂(R ⊂̇ P)` of sub-relations of `P`. Value function of `Rl`. -/
def rl (P : α → β → Prop) : Set (α → β → Prop) := {R | R ⪽ P}

/-- `Rl ex'P`, the class `R̂(R ⊂̇ P . ∃̇!R)` of existent sub-relations of `P`. Value function of
`RlEx`. -/
def rlEx (P : α → β → Prop) : Set (α → β → Prop) := {R | R ⪽ P ∧ rEx R}

/-- **✱61·01 Df.** \(\text{Rl}=\hat{\lambda}\hat{P}\{\lambda=\hat{R}(R\unicode{x2abd}P)\} \quad\text{Df}\)

The relation `Rl` of the class of sub-relations of `P` to `P`; `Rl'P` is `rl P`. Target:
`pm61_01 : (Rl : Set (α → β → Prop) → (α → β → Prop) → Prop) = fun L P => L = {R | R ⪽ P} :=
rfl`. -/
def Rl : Set (α → β → Prop) → (α → β → Prop) → Prop := graph rl

/-- **✱61·02 Df.** \(\text{Rl ex}=\hat{\lambda}\hat{P}\{\lambda=\hat{R}(R\unicode{x2abd}P.\dot{\exists}!R)\} \quad\text{Df}\)

Target: `pm61_02 : (RlEx : Set (α → β → Prop) → (α → β → Prop) → Prop) =
fun L P => L = {R | R ⪽ P ∧ rEx R} := rfl`. -/
def RlEx : Set (α → β → Prop) → (α → β → Prop) → Prop := graph rlEx

/-- **✱61·03 Df.** \(\text{Rel}^{2}=\text{Rl}ʻ (\text{Rel}\uparrow\text{Rel}) \quad\text{Df}\)

The class of relations of relations (the two `Rel`s may be of different types). Target:
`pm61_03 : Desc Rl (cross Rel Rel)
  (fun L => (Rel2 : Set ((α → β → Prop) → (γ → δ → Prop) → Prop)) = L) := (desc_graph _ _ _).2 rfl`. -/
def Rel2 : Set ((α → β → Prop) → (γ → δ → Prop) → Prop) := rl (cross Rel Rel)

/-- **✱61·04 Df.** \(\text{Rel}^{3}=\text{Rl}ʻ (\text{Rel}^{2}\uparrow\text{Rel}^{2}) \quad\text{Df}\)

The class of relations of relations of relations. Target:
`pm61_04 : Desc Rl (cross Rel2 Rel2) (fun L => Rel3 = L) := (desc_graph _ _ _).2 rfl` (with the
eight type variables fixed by an ascription of `Rel3`). -/
def Rel3 {α' : Type u} {β' : Type v} {γ' : Type w} {δ' : Type u'} {ε : Type v'} {ζ : Type w'}
    {η : Type u''} {θ : Type v''} :
    Set (((α' → β' → Prop) → (γ' → δ' → Prop) → Prop) → ((ε → ζ → Prop) → (η → θ → Prop) → Prop) →
      Prop) :=
  rl (cross Rel2 Rel2)

/-- **✱62·01 Df.** \(\in =\hat{x}\hat{\alpha}(x\in \alpha) \text{Df}\)

Membership as a relation, `memRel`. PM says the Df is "strictly incorrect" (it gives two meanings
to `∈`) but harmless, since `x ∈ α` in either sense is the same; in Lean `x ∈ A` is mathlib's
membership and the relation is the separate name `memRel` (`memRel x A ↔ x ∈ A` by `Iff.rfl`).
Target: `pm62_01 : (memRel : α → Set α → Prop) = fun x A => x ∈ A := rfl`. -/
def memRel : α → Set α → Prop := fun x A => x ∈ A

/-- **✱63·01 Df.** \(tʻx = \iotaʻx \cup - \iotaʻx \quad \text{Df}\)

`t'x`, the type of `x`: everything identical or not identical with `x`. In Lean it is `Set.univ`
of the type of `x` (`typ_eq_univ`). The relation `t` is `graph typ`. Target:
`pm63_01 : typ x = ι x ∪ (ι x)ᶜ := rfl`. -/
def typ (x : α) : Set α := ι x ∪ (ι x)ᶜ

/-- **✱63·011 Df.** \(t^{1}ʻx = tʻx \quad \text{Df}\)

Target: `pm63_011 : typ1 x = typ x := rfl`. -/
def typ1 (x : α) : Set α := typ x

/-- **✱63·02 Df.** \(t_{0}ʻ\alpha = \alpha \cup -\alpha \quad \text{Df}\)

`t₀'α`, the type of the members of `α` (`= Set.univ`, `typ₀_eq_univ`). Target:
`pm63_02 : typ₀ A = A ∪ Aᶜ := rfl`. -/
def typ₀ (A : Set α) : Set α := A ∪ Aᶜ

/-- **✱63·03 Df.** \(t_{1}ʻ\kappa = t_{0}ʻsʻ\kappa \quad \text{Df}\)

`t₁'κ`, the type next below that in which `κ` is contained (`κ : Set (Set α)`, `t₁'κ : Set α`).
Target: `pm63_03 : typ₁ K = typ₀ (sumCls K) := rfl`. -/
def typ₁ (K : Set (Set α)) : Set α := typ₀ (sumCls K)

/-- **✱63·04 Df.** \(t^{2}ʻx = tʻtʻx \quad \text{Df}\)

Target: `pm63_04 : typ2 x = typ (typ x) := rfl`. -/
def typ2 (x : α) : Set (Set α) := typ (typ x)

/-- **✱63·041 Df.** \(t^{3}ʻx = tʻt^{2}ʻx \quad \text{Df}\)

("and so on", Summary of ✱63.) Target: `pm63_041 : typ3 x = typ (typ2 x) := rfl`. -/
def typ3 (x : α) : Set (Set (Set α)) := typ (typ2 x)

/-- **✱63·05 Df.** \(t_{2}ʻ\kappa = t_{1}ʻt_{1}ʻ\kappa \quad \text{Df}\)

(`κ : Set (Set (Set α))`, `t₂'κ : Set α`.) Target: `pm63_05 : typ₂ K = typ₁ (typ₁ K) := rfl`. -/
def typ₂ (K : Set (Set (Set α))) : Set α := typ₁ (typ₁ K)

/-- **✱63·051 Df.** \(t_{3}ʻ\kappa = t_{1}ʻt_{2}ʻ\kappa \quad\text{Df}\)

("and so on".) Target: `pm63_051 : typ₃ K = typ₁ (typ₂ K) := rfl`. -/
def typ₃ (K : Set (Set (Set (Set α)))) : Set α := typ₁ (typ₂ K)

/-!
### ✱64: relative types of relations

The Dfs of ✱64 are printed in the e-text inside the Summary of ✱64 (with ✱64·1·11·12), not as
separate propositions of `data/principia.json`; they are PM's Dfs ✱64·01–✱64·041 all the same
(PM adds "etc." after each group: further indices are formed in the same way). Naming rule: the two
indices are written in the order of the two factors of `↑`, a superscript as a plain digit and a
subscript as a subscript digit: `t^{mn}` ↦ `typmn`, `t_{mn}` ↦ `typₘₙ`, `t_m^n` ↦ `typₘn`,
`^m t_n` ↦ `typmₙ`.
-/

/-- **✱64·01 Df.** \(t_{00}ʻ\alpha=tʻ(t_{0}ʻ\alpha\uparrow t_{0}ʻ\alpha) \quad\text{Df}\)

The type of relations whose referents and relata are of the type of members of `α`. Target:
`pm64_01 : typ₀₀ A = typ (cross (typ₀ A) (typ₀ A)) := rfl`. -/
def typ₀₀ (A : Set α) : Set (α → α → Prop) := typ (cross (typ₀ A) (typ₀ A))

/-- **✱64·011 Df.** \(t^{11}ʻx=tʻ(tʻx\uparrow tʻx) \quad\text{Df}\)

Target: `pm64_011 : typ11 x = typ (cross (typ x) (typ x)) := rfl`. -/
def typ11 (x : α) : Set (α → α → Prop) := typ (cross (typ x) (typ x))

/-- **✱64·012 Df.** \(t^{12}ʻx=tʻ(tʻx\uparrow t^{2}ʻx) \quad\text{Df}\)

Target: `pm64_012 : typ12 x = typ (cross (typ x) (typ2 x)) := rfl`. -/
def typ12 (x : α) : Set (α → Set α → Prop) := typ (cross (typ x) (typ2 x))

/-- **✱64·013 Df.** \(t^{21}ʻx=tʻ(t^{2}ʻx\uparrow tʻx) \quad\text{Df}\)

Target: `pm64_013 : typ21 x = typ (cross (typ2 x) (typ x)) := rfl`. -/
def typ21 (x : α) : Set (Set α → α → Prop) := typ (cross (typ2 x) (typ x))

/-- **✱64·014 Df.** \(t^{22}ʻx=tʻ(t^{2}ʻx\uparrow t^{2}ʻx) \quad\text{Df}\)

Target: `pm64_014 : typ22 x = typ (cross (typ2 x) (typ2 x)) := rfl`. -/
def typ22 (x : α) : Set (Set α → Set α → Prop) := typ (cross (typ2 x) (typ2 x))

/-- **✱64·02 Df.** \(t_{01}ʻ\alpha=tʻ(t_{0}ʻ\alpha\uparrow t_{1}ʻ\alpha) \quad\text{Df}\)

(`α` a class of classes.) Target: `pm64_02 : typ₀₁ A = typ (cross (typ₀ A) (typ₁ A)) := rfl`. -/
def typ₀₁ (A : Set (Set α)) : Set (Set α → α → Prop) := typ (cross (typ₀ A) (typ₁ A))

/-- **✱64·021 Df.** \(t_{10}ʻ\alpha=tʻ(t_{1}ʻ\alpha\uparrow t_{0}ʻ\alpha) \quad\text{Df}\)

Target: `pm64_021 : typ₁₀ A = typ (cross (typ₁ A) (typ₀ A)) := rfl`. -/
def typ₁₀ (A : Set (Set α)) : Set (α → Set α → Prop) := typ (cross (typ₁ A) (typ₀ A))

/-- **✱64·022 Df.** \(t_{11}ʻ\alpha=tʻ(t_{1}ʻ\alpha\uparrow t_{1}ʻ\alpha) \quad\text{Df}\)

Target: `pm64_022 : typ₁₁ A = typ (cross (typ₁ A) (typ₁ A)) := rfl`. -/
def typ₁₁ (A : Set (Set α)) : Set (α → α → Prop) := typ (cross (typ₁ A) (typ₁ A))

/-- **✱64·03 Df.** \(t_{0}^{1}ʻ\alpha=tʻ(t_{0}ʻ\alpha\uparrow tʻ\alpha) \quad\text{Df}\)

Target: `pm64_03 : typ₀1 A = typ (cross (typ₀ A) (typ A)) := rfl`. -/
def typ₀1 (A : Set α) : Set (α → Set α → Prop) := typ (cross (typ₀ A) (typ A))

/-- **✱64·031 Df.** \(t_{1}^{1}ʻ\alpha=tʻ(t_{1}ʻ\alpha\uparrow tʻ\alpha) \quad\text{Df}\)

Target: `pm64_031 : typ₁1 A = typ (cross (typ₁ A) (typ A)) := rfl`. -/
def typ₁1 (A : Set (Set α)) : Set (α → Set (Set α) → Prop) := typ (cross (typ₁ A) (typ A))

/-- **✱64·04 Df.** \(^{1}t_{0}ʻ\alpha=tʻ(tʻ\alpha\uparrow t_{0}ʻ\alpha) \quad\text{Df}\)

Target: `pm64_04 : typ1₀ A = typ (cross (typ A) (typ₀ A)) := rfl`. -/
def typ1₀ (A : Set α) : Set (Set α → α → Prop) := typ (cross (typ A) (typ₀ A))

/-- **✱64·041 Df.** \(^{1}t_{1}ʻ\alpha=tʻ(tʻ\alpha\uparrow t_{1}ʻ\alpha) \quad\text{Df}\)

Target: `pm64_041 : typ1₁ A = typ (cross (typ A) (typ₁ A)) := rfl`. -/
def typ1₁ (A : Set (Set α)) : Set (Set (Set α) → α → Prop) := typ (cross (typ A) (typ₁ A))

/-!
### ✱65: typical definition of ambiguous symbols

In ✱65 `α` and `R` stand for typically ambiguous *symbols* (`Λ`, `V`, `1`, `Λ̇`, `V̇`, …), and
`α_x` etc. give them the type determined by `x`. In Lean every term has a definite type, so these
are the intersections/restrictions PM writes, at the type forced by `x` (they equal `α`, `R`:
`clsT_eq`, `relT_eq`, …); a Section agent states e.g. `1_x` as `clsT one x` with `x : Set γ`.
-/

/-- **✱65·01 Df.** \(\alpha_{x}=\alpha\cap tʻx \quad\text{Df}\)

`α_x`: `α` with members of the type of `x`. Target: `pm65_01 : clsT A x = A ∩ typ x := rfl`. -/
def clsT (A : Set α) (x : α) : Set α := A ∩ typ x

/-- **✱65·02 Df.** \(\alpha(x)=\alpha\cap tʻtʻx \quad\text{Df}\)

`α(x)`: `α` with members of the type of `t'x` (classes of `x`'s type). Target:
`pm65_02 : clsT2 A x = A ∩ typ (typ x) := rfl`. -/
def clsT2 (A : Set (Set α)) (x : α) : Set (Set α) := A ∩ typ (typ x)

/-- **✱65·03 Df.** \(R_{x}=(tʻx)\upharpoonleft R \quad\text{Df}\)

`R_x`: `R` with domain within the type of `x`. Target: `pm65_03 : relT R x = typ x ◁ R := rfl`. -/
def relT (R : α → β → Prop) (x : α) : α → β → Prop := typ x ◁ R

/-- **✱65·04 Df.** \(R(x)=(t^{2}ʻx)\upharpoonleft R \quad\text{Df}\)

`R(x)`: `R` with domain within the type of `t'x`. Target:
`pm65_04 : relT2 R x = typ2 x ◁ R := rfl`. -/
def relT2 (R : Set α → β → Prop) (x : α) : Set α → β → Prop := typ2 x ◁ R

/-- **✱65·1 Df.** \(R_{(x,y)}=(tʻx)\upharpoonleft R\upharpoonright(tʻy) \quad\text{Df}\)

`R_{(x,y)}`: domain within the type of `x`, converse domain within the type of `y` (✱35·03:
`typ x ◁ R ↾ typ y` is `bres (typ x) R (typ y)`). Target:
`pm65_1 : relTT R x y = typ x ◁ R ↾ typ y := rfl`. -/
def relTT (R : α → β → Prop) (x : α) (y : β) : α → β → Prop := typ x ◁ R ↾ typ y

/-- **✱65·11 Df.** \(R(x_{y})=(t^{2}ʻx)\upharpoonleft R\upharpoonright(tʻy) \quad\text{Df}\)

Target: `pm65_11 : relT2T R x y = typ2 x ◁ R ↾ typ y := rfl`. -/
def relT2T (R : Set α → β → Prop) (x : α) (y : β) : Set α → β → Prop := typ2 x ◁ R ↾ typ y

/-- **✱65·12 Df.** \(R(x,y)=(t^{2}ʻx)\upharpoonleft R\upharpoonright(t^{2}ʻy) \quad\text{Df}\)

Target: `pm65_12 : relT2T2 R x y = typ2 x ◁ R ↾ typ2 y := rfl`. -/
def relT2T2 (R : Set α → Set β → Prop) (x : α) (y : β) : Set α → Set β → Prop :=
  typ2 x ◁ R ↾ typ2 y

/-! ## Section C: one-many, many-one, and one-one relations (✱70–✱74) -/

/-- **✱70·01 Df.** \(\alpha\rightarrow\beta = \breve{R} (\overrightarrow{R}ʻʻ\text{ᗡ}ʻR \subset\alpha. \overleftarrow{R}ʻʻ\text{D}ʻR\subset\beta) \quad\text{Df}\)

(The e-text prints `R̆` for `R̂`: PM has `α → β = R̂(R⃗''ᗡ'R ⊂ α . R⃖''D'R ⊂ β) Df`, as in the
Summary of Section C.) `α → β` (Lean's `→` is the function type, so it is the name `arrow`) is the
class of relations `R` such that the class of referents of every member of `ᗡ'R` is in `α` and
the class of relata of every member of `D'R` is in `β`; `α`, `β` are classes of classes. So
`1 → Cls` (one-many) is `arrow one Cls`, `Cls → 1` (many-one) is `arrow Cls one`, `1 → 1`
(one-one) is `arrow one one` (`mem_arrow_one_Cls`, `mem_arrow_Cls_one`, `mem_arrow_one_one`).
Target (status `definition`; mention the transcription error):
`pm70_01 : arrow A B = {R | Rfwd R ʻʻ codom R ⊆ A ∧ Rbwd R ʻʻ dom R ⊆ B} := rfl`. -/
def arrow (A : Set (Set α)) (B : Set (Set β)) : Set (α → β → Prop) :=
  {R | Rfwd R ʻʻ codom R ⊆ A ∧ Rbwd R ʻʻ dom R ⊆ B}

/-- **✱73·01 Df.** \(\alpha\overline{\text{ sm }}\beta=1\rightarrow 1\cap \overleftarrow{\text{D}}ʻ\alpha\cap \overleftarrow{\text{ᗡ}}ʻ\beta \quad{\text{Df}}\)

`α sm̄ β`, the class of correlators of `α` with `β`: one-one relations with domain `α` and converse
domain `β`. `D⃖'α` is `rels D A` (`= {R | A = dom R}`), `ᗡ⃖'β` is `rels Dcnv B`; the products
bracket to the left (✱22·53). `α` and `β` may be of different types. Target:
`pm73_01 : smbar A B = arrow one one ∩ rels D A ∩ rels Dcnv B := rfl`. -/
def smbar (A : Set α) (B : Set β) : Set (α → β → Prop) := arrow one one ∩ rels D A ∩ rels Dcnv B

/-- **✱73·02 Df.** \(\text{ sm }=\hat{\alpha}\hat{\beta}(\exists !\alpha\overline{\text{ sm }}\beta) \quad{\text{Df}}\)

Similarity: `α sm β` iff some one-one relation has domain `α` and converse domain `β`; written
`sm A B`. It is an equivalence (`sm_refl`, `sm_symm`, `sm_trans`) and is `Nonempty (A ≃ B)`
(`sm_iff_nonempty_equiv`). Target:
`pm73_02 : (sm : Set α → Set β → Prop) = fun A B => (smbar A B).Nonempty := rfl`. -/
def sm : Set α → Set β → Prop := fun A B => (smbar A B).Nonempty

/-! ## Section D: selections (✱80–✱88) -/

/-- `P_Δ'κ`, the class of `P`-selectors from `κ`: one-many relations contained in `P` with converse
domain `κ` (`mem_sel_iff`). Value function of `selRel P`. `∈_Δ'κ` is `sel memRel K`. -/
def sel (P : α → β → Prop) (K : Set β) : Set (α → β → Prop) := arrow one Cls ∩ rl P ∩ rels Dcnv K

/-- **✱80·01 Df.** \(P_{\Delta}=\hat{\lambda}\hat{\kappa}\{\lambda=(1\rightarrow \text{Cls})\cap \text{Rl}ʻP\cap \overleftarrow{\text{ᗡ}}ʻ\kappa\} \quad\text{Df}\)

The relation `P_Δ` of the class of `P`-selections from `κ` to `κ`; `P_Δ'κ` is `sel P K`,
`P_Δ''κ` is `selRel P ʻʻ K`. Target:
`pm80_01 : selRel P = fun L K => L = arrow one Cls ∩ rl P ∩ rels Dcnv K := rfl`. -/
def selRel (P : α → β → Prop) : Set (α → β → Prop) → Set β → Prop := graph (sel P)

/-- **✱84·01 Df.** \(\text{Cls}^2\, \text{excl}=\hat{\kappa}(\alpha,\beta\in \kappa.\alpha \neq \beta.\supset_{\alpha,\beta}.\alpha\cap \beta=\Lambda) \quad\text{Df}\)

Classes of mutually exclusive classes. `α, β ∈ κ` is `A ∈ K ∧ B ∈ K` (✱20·04) and the antecedent
is the product `α, β ∈ κ . α ≠ β`. Target:
`pm84_01 : (Cls2excl : Set (Set (Set α))) = {K | ∀ A B, (A ∈ K ∧ B ∈ K) ∧ A ≠ B → A ∩ B = Λ} :=
rfl`. -/
def Cls2excl : Set (Set (Set α)) := {K | ∀ A B, (A ∈ K ∧ B ∈ K) ∧ A ≠ B → A ∩ B = Λ}

/-- `Cl excl'γ`, the classes of mutually exclusive classes contained in `γ`. Value function of
`ClExcl`. -/
def clExcl (G : Set (Set α)) : Set (Set (Set α)) := Cls2excl ∩ cl G

/-- **✱84·02 Df.** \(\text{Cl excl}ʻ\gamma=\text{Cls}^2\, \text{excl}\cap \text{Cl}ʻ\gamma \quad\text{Df}\)

The descriptive function `Cl excl'γ` (the relation `Cl excl` is `ClExcl = graph clExcl`). Target:
`pm84_02 : clExcl G = Cls2excl ∩ cl G := rfl`. -/
def ClExcl : Set (Set (Set α)) → Set (Set α) → Prop := graph clExcl

/-- **✱84·03 Df.** \(\text{Cls}^2\, \text{excl}=\text{Cls}^2\, \text{excl}-\overleftarrow{\in}ʻ\Lambda \quad\text{Df}\)

(The e-text prints the definiendum as `Cls² excl`; PM has `Cls ex² excl = Cls² excl − ∈⃖'Λ Df`, as
the Summary of ✱84 and ✱84·13 show.) Classes of mutually exclusive classes none of which is null:
`∈⃖'Λ` is `rels memRel Λ`, the classes having `Λ` as a member. Target (status `definition`;
mention the transcription error):
`pm84_03 : (ClsEx2excl : Set (Set (Set α))) = Cls2excl \ rels memRel Λ := rfl`. -/
def ClsEx2excl : Set (Set (Set α)) := Cls2excl \ rels memRel Λ

/-- **✱85·5 Df.** \(P\unicode{x21A7}y=\downarrow yʻʻ\overrightarrow{P}ʻy \quad\text{Df}\)

`P ↧ y`, the class of couples `x ↓ y` whose referent `x` has the relation `P` to `y`. It is a
double descriptive function (✱38), so `P↧` (the relation of `P ↧ y` to `y`) is `opL downCls P`
and `P↧''α` is `opL downCls P ʻʻ A`. Target: `pm85_5 : P ↧ y = coupleR y ʻʻ refs P y := rfl`. -/
def downCls (P : α → β → Prop) (y : β) : Set (α → β → Prop) := coupleR y ʻʻ refs P y

@[inherit_doc] scoped infix:78 " ↧ " => downCls

/-- **✱88·01 Df.** \(\text{Rel}\,\text{Mult}=\hat{P}\{\exists!P_{\Delta}ʻ \text{ᗡ}ʻ P\} \quad\text{Df}\)

Multipliable relations: those having a `P`-selection from their whole converse domain. (The
Summary of ✱88 prints `P̆` for `P̂`.) Target:
`pm88_01 : (RelMult : Set (α → β → Prop)) = {P | (sel P (codom P)).Nonempty} := rfl`. -/
def RelMult : Set (α → β → Prop) := {P | (sel P (codom P)).Nonempty}

/-- **✱88·02 Df.** \(\text{Cls}^{2}\,\text{Mult}=\hat{\kappa} \{\exists!{\in}_{\Delta}ʻ \kappa\} \quad\text{Df}\)

Multipliable classes of classes. Target:
`pm88_02 : (Cls2Mult : Set (Set (Set α))) = {K | (sel memRel K).Nonempty} := rfl`. -/
def Cls2Mult : Set (Set (Set α)) := {K | (sel memRel K).Nonempty}

/-- **✱88·03 Df.** \(\text{Mult ax}.=\colon\ldotp \kappa\in \text{Cls}\,\text{ex}^{2}\,\text{excl}.\supset_{\kappa}:(\exists \mu ):\alpha \in \kappa.\supset_{\alpha }.\mu \cap \alpha \in 1 \quad\text{Df}\)

The multiplicative axiom, a proposition (typically ambiguous: `MultAx α` is the axiom for classes
of classes of `α`-things; take it at the type PM's enunciation determines, Basic §10). It is
provable in Lean (`multAx_holds`, by `Classical.choice`), but stays a hypothesis wherever PM has
it. (The e-text entries of ✱88·3, ✱88·31 and ✱88·32 print `Cls² excl` where PM has
`Cls ex² excl`, as the Summary of ✱88 and the proof of ✱88·3 `[✱4·2.(✱88·03)]` show; with
`Cls² excl` the right-hand sides would be false, since `Λ ∈ κ` is allowed. Likewise the Summary's
✱88·37 prints `Λ ∈ κ` for `Λ ∼∈ κ`.) Target:
`pm88_03 : MultAx α ↔ ∀ K : Set (Set α), K ∈ ClsEx2excl → ∃ M : Set α, ∀ A, A ∈ K → M ∩ A ∈ one :=
Iff.rfl`. -/
def MultAx (α : Type u) : Prop :=
  ∀ K : Set (Set α), K ∈ ClsEx2excl → ∃ M : Set α, ∀ A, A ∈ K → M ∩ A ∈ one

/-! ## Section E: inductive relations (✱90–✱97) -/

/-- **✱90·01 Df.** \(R_{\unicode{x2217}} = \hat{x}\hat{y}\{x\in CʻR:\breve{R}ʻʻ\mu\subset \mu.x\in \mu.\supset_{\mu}.y\in \mu\} \quad\text{Df}\)

The ancestral `R_*` (homogeneous `R`): `x R_* y` iff `x` is in the field of `R` and `y` belongs to
every hereditary class (`R̆''μ ⊂ μ`: successors of members are members) containing `x`. The colon
is a product, the hypothesis of `⊃_μ` is the product `R̆''μ ⊂ μ . x ∈ μ`. It is the
reflexive-transitive closure restricted to the field (`anc_iff_reflTransGen`). Target:
`pm90_01 : anc R = fun x y => x ∈ fld R ∧ ∀ M : Set α, R˘ ʻʻ M ⊆ M ∧ x ∈ M → y ∈ M := rfl`. -/
def anc (R : α → α → Prop) : α → α → Prop :=
  fun x y => x ∈ fld R ∧ ∀ M : Set α, R˘ ʻʻ M ⊆ M ∧ x ∈ M → y ∈ M

/-- **✱90·02 Df.** \(\breve{R}_{\unicode{x2217}} = \text{Cnv}ʻR_{\unicode{x2217}} \quad\text{Df}\)

Decides the ambiguity of `R̆_*`: it is the converse of `R_*`, `ancCnv R = (anc R)˘` (not
`anc R˘`, which ✱90·132 proves equal). The definiens is a descriptive function (Basic §5), so the
target is `pm90_02 : Desc Cnv (anc R) (fun Q => ancCnv R = Q) := (desc_Cnv _ _).2 rfl`. -/
def ancCnv (R : α → α → Prop) : α → α → Prop := (anc R)˘

/-- **✱91·01 Df.** \(R_{\text{st}}=(R\mid)_{\unicode{x2217}} \quad\text{Df}\)

The ancestral of `R|` (the relation of `R | S` to `S`). The relations it relates are of an
ambiguous type `α → γ → Prop`. Target:
`pm91_01 : (Rst R : (α → γ → Prop) → (α → γ → Prop) → Prop) = anc (relProdL R) := rfl`. -/
def Rst (R : α → α → Prop) : (α → γ → Prop) → (α → γ → Prop) → Prop := anc (relProdL R)

/-- **✱91·02 Df.** \(R_{\text{ts}}=(\mid R)_{\unicode{x2217}} \quad\text{Df}\)

The ancestral of `|R` (the relation of `S | R` to `S`). Target:
`pm91_02 : (Rts R : (γ → α → Prop) → (γ → α → Prop) → Prop) = anc (relProdR R) := rfl`. -/
def Rts (R : α → α → Prop) : (γ → α → Prop) → (γ → α → Prop) → Prop := anc (relProdR R)

/-- `Pot'R`, the powers `R, R², R³, …` of `R` (`mem_pot_iff`). Value function of `Pot`. -/
def pot (R : α → α → Prop) : Set (α → α → Prop) := refs (Rts R) R

/-- **✱91·03 Df.** \(\text{Pot}ʻR=\overrightarrow{R}_{\text{ts}}ʻR \quad\text{Df}\)

`R⃗_ts'R` is `refs (Rts R) R` (the relations having `R_ts` to `R`); the relation `Pot` is
`graph pot`. Target: `pm91_03 : pot R = refs (Rts R) R := rfl`. -/
def Pot : Set (α → α → Prop) → (α → α → Prop) → Prop := graph pot

/-- `Potid'R`, the powers of `R` together with `I ↾ C'R`. Value function of `Potid`. -/
def potid (R : α → α → Prop) : Set (α → α → Prop) := refs (Rts R) (I ↾ fld R)

/-- **✱91·04 Df.** \(\text{Potid}ʻR=\overrightarrow{R}_{\text{ts}}ʻ(I\upharpoonright CʻR) \quad\text{Df}\)

Target: `pm91_04 : potid R = refs (Rts R) (I ↾ fld R) := rfl`. -/
def Potid : Set (α → α → Prop) → (α → α → Prop) → Prop := graph potid

/-- **✱91·05 Df.** \(R_{\text{po}}=\dot{s}ʻ\text{Pot}ʻR \quad\text{Df}\)

The "proper ancestral", the sum of the powers of `R`; it is the transitive closure
(`po_iff_transGen`). The definiens is the descriptive function `Pot'R` inside `ṡ'…` (a term, ✱41·02),
so the target keeps it: `pm91_05 : Desc Pot R (fun L => po R = sumRel L) := (desc_graph _ _ _).2
rfl`. -/
def po (R : α → α → Prop) : α → α → Prop := sumRel (pot R)

/-- **✱93·01 Df.** \(B=\hat{x}\hat{P}(x\in \text{D}ʻP-\text{ᗡ}ʻP) \quad\text{Df}\)

`x B P`: `x` "begins" `P` (is a referent but not a relatum); named `Beg`. `B'P` need not exist:
`ψ(B'P)` is `Desc Beg P ψ`, and `B⃗'P` is `refs Beg P`. Target:
`pm93_01 : (Beg : α → (α → α → Prop) → Prop) = fun x P => x ∈ dom P \ codom P := rfl`. -/
def Beg : α → (α → α → Prop) → Prop := fun x P => x ∈ dom P \ codom P

/-- **✱93·02 Df.** \(\text{min}_{P}=\text{min}(P)=\hat{x}\hat{\alpha}(x\in \alpha\cap CʻP-\breve{P}ʻʻ\alpha) \quad\text{Df}\)

`x min_P α`: `x` is a member of `α` and of `C'P` which follows no member of `α`. `min(P)` is
another notation for the same relation `minP P`. `min_P'α` need not exist (`Desc (minP P) A ψ`);
`min⃗_P'α` is `refs (minP P) A`. Target:
`pm93_02 : minP P = fun x A => x ∈ (A ∩ fld P) \ P˘ ʻʻ A := rfl`. -/
def minP (P : α → α → Prop) : α → Set α → Prop := fun x A => x ∈ (A ∩ fld P) \ P˘ ʻʻ A

/-- **✱93·021 Df.** \(\text{max}_{P}=\text{max}(P)=\text{min}(\breve{P}) \quad\text{Df}\)

Target: `pm93_021 : maxP P = minP P˘ := rfl`. -/
def maxP (P : α → α → Prop) : α → Set α → Prop := minP P˘

/-- `gen'P`, the generations of `P`. Value function of `Gen`. -/
def gen (P : α → α → Prop) : Set (Set α) := Rfwd (minP P) ʻʻ Dcnv ʻʻ potid P

/-- **✱93·03 Df.** \(\text{gen}ʻP=\overrightarrow{\text{min}}_{P}ʻʻ\text{ᗡ}ʻʻ\text{Potid}ʻP \quad\text{Df}\)

`ᗡ''Potid'P` is `Dcnv ʻʻ potid P` (the converse domains of the powers), `min⃗_P` is
`Rfwd (minP P)`. The relation `gen` is `Gen = graph gen`. Target:
`pm93_03 : gen P = Rfwd (minP P) ʻʻ Dcnv ʻʻ potid P := rfl`. -/
def Gen : Set (Set α) → (α → α → Prop) → Prop := graph gen

/-- **✱95·01 Dft [✱95].** \((P\unicode{x2217}Q)=\text{sg}ʻ\{(P\Arrowvert Q)_{\unicode{x2217}}\} \quad\text{Dft}\, [\text{*95}]\)

A temporary definition, used in ✱95 only (✱257 gives `(P∗Q)` an unconnected meaning, hence the
distinct name `eqf`, "equi-factor"). `(P∗Q)'R` is `refs (anc (P ∥ Q)) R`, the relations
`P^ν | R | Q^ν`. The definiens is the descriptive function `sg'…`, so the target is
`pm95_01 : Desc sg (anc (P ∥ Q)) (fun X => eqf P Q = X) := (desc_graph _ _ _).2 rfl`
(status `definition`; say it is a Dft). -/
def eqf (P : α → α → Prop) (Q : β → β → Prop) : Set (α → β → Prop) → (α → β → Prop) → Prop :=
  Rfwd (anc (P ∥ Q))

/-- **✱96·01 Dft [✱96].** \(I_{R}ʻx=\overleftarrow{R}_{\unicode{x2217}}ʻx\cap \hat{z}(zR_{\text{po}}z) \quad\text{Dft}\, [\text{*96}]\)

The circular part of the posterity of `x` (temporary definition for ✱96). `R⃖_*'x` is
`rels (anc R) x`. Target: `pm96_01 : IR R x = rels (anc R) x ∩ {z | po R z z} := rfl`. -/
def IR (R : α → α → Prop) (x : α) : Set α := rels (anc R) x ∩ {z | po R z z}

/-- **✱96·02 Dft [✱96].** \(J_{R}ʻx=\overleftarrow{R}_{\unicode{x2217}}ʻx-I_{R}ʻx \quad\text{Dft}\, [\text{*96}]\)

The open part of the posterity of `x`. (The Summary of ✱96 misprints it as
`R⃖_*'x ∪ ẑ{∼(z R_po z)}`, for `∩`; the Dft is as here.) Target:
`pm96_02 : JR R x = rels (anc R) x \ IR R x := rfl`. -/
def JR (R : α → α → Prop) (x : α) : Set α := rels (anc R) x \ IR R x

/-- `R⃡'x`, the referents and relata of `x`, and `x` itself if it is in `C'R`. Value function of
`Rboth R`. The family of `x` is `R⃡_*'x`, i.e. `refsRels (anc R) x`. -/
def refsRels (R : α → α → Prop) (x : α) : Set α := refs R x ∪ (ι x ∩ fld R) ∪ rels R x

/-- **✱97·01 Df.** \(\overleftrightarrow{R}ʻx=\overrightarrow{R}ʻx\cup(\iotaʻx\cap CʻR)\cup\overleftarrow{R}ʻx \quad\text{Df}\)

The sums bracket to the left (✱22·71). The relation `R⃡` is `Rboth R = graph (refsRels R)`.
Target: `pm97_01 : refsRels R x = refs R x ∪ (ι x ∩ fld R) ∪ rels R x := rfl`. -/
def Rboth (R : α → α → Prop) : Set α → α → Prop := graph (refsRels R)

/-! ## Sanity lemmas: the encodings behave -/

section Sanity

theorem I_apply (x y : α) : I x y ↔ x = y := Iff.rfl

theorem J_apply (x y : α) : J x y ↔ x ≠ y := Iff.rfl

/-- `I'y` always exists and is `y` (cf. ✱50·14). -/
theorem desc_I (y : α) (ψ : α → Prop) : Desc I y ψ ↔ ψ y :=
  TheIs_iff_of_unique (fun _ => Iff.rfl)

/-- `y ∈ ι'x . ≡ . y = x` (✱51·15). -/
theorem mem_unitCls {x y : α} : y ∈ ι x ↔ y = x := Iff.rfl

/-- PM's `ι'x` is mathlib's `{x}`. -/
theorem unitCls_eq_singleton (x : α) : ι x = {x} := rfl

theorem unitCls_injective : Function.Injective (unitCls : α → Set α) := fun x y h =>
  show x ∈ ι y from h ▸ (rfl : x = x)

/-- `(ι)'x` is `ι'x`. -/
theorem desc_iota (x : α) (ψ : Set α → Prop) : Desc iota x ψ ↔ ψ (ι x) := desc_graph _ _ _

/-- `ψ(ῐ'α)` is `ψ(℩x)(x ∈ α)`: `ῐ'α` is the only member of `α` (cf. ✱51·51·59). -/
theorem desc_iota_cnv (A : Set α) (ψ : α → Prop) :
    Desc iota˘ A ψ ↔ TheIs (fun x => x ∈ A) ψ := by
  have key : ∀ b, (∀ x, iota˘ x A ↔ x = b) ↔ (∀ x, x ∈ A ↔ x = b) := by
    intro b
    constructor
    · intro h
      have hA : A = ι b := (h b).2 rfl
      intro x
      rw [hA]
      exact Iff.rfl
    · intro h x
      have hA : A = ι b := Set.ext h
      show A = ι x ↔ x = b
      rw [hA]
      exact ⟨fun e => (unitCls_injective e).symm, fun e => by rw [e]⟩
  exact ⟨fun ⟨b, hb, hψ⟩ => ⟨b, (key b).1 hb, hψ⟩, fun ⟨b, hb, hψ⟩ => ⟨b, (key b).2 hb, hψ⟩⟩

/-- A class is a member of `1` iff it has exactly one member. -/
theorem mem_one_iff {A : Set α} : A ∈ one ↔ ∃ x, ∀ z, z ∈ A ↔ z = x := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, fun _ => Iff.rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Set.ext hx⟩

theorem mem_one_iff_existsUnique {A : Set α} : A ∈ one ↔ ∃! x, x ∈ A := by
  rw [mem_one_iff]
  exact (EBang_iff_existsUnique (φ := fun x => x ∈ A))

/-- `E!R'y . ≡ . R⃗'y ∈ 1` (✱53·3). -/
theorem refs_mem_one_iff (R : α → β → Prop) (y : β) : refs R y ∈ one ↔ EDesc R y := mem_one_iff

theorem rels_mem_one_iff (R : α → β → Prop) (x : α) : rels R x ∈ one ↔ EDesc R˘ x := mem_one_iff

/-- `0` is `{∅}`. -/
theorem zero_eq : (zero : Set (Set α)) = {∅} := by
  rw [zero, Null_eq_empty]
  rfl

theorem mem_two_iff {A : Set α} : A ∈ two ↔ ∃ x y, x ≠ y ∧ A = {x, y} := by
  show (∃ x y, x ≠ y ∧ A = ι x ∪ ι y) ↔ _
  simp only [unitCls_eq_singleton, Set.singleton_union]

/-- `z(x ↓ y)w . ≡ . z = x . w = y` (✱55·13). -/
theorem couple_apply (x : α) (y : β) (z : α) (w : β) : (x ↓ y) z w ↔ z = x ∧ w = y := Iff.rfl

theorem coupleR_apply (y : β) (R : α → β → Prop) (x : α) : coupleR y R x ↔ R = x ↓ y := Iff.rfl

theorem mem_cl {A B : Set α} : B ∈ cl A ↔ B ⊆ A := Iff.rfl

theorem cl_eq_powerset (A : Set α) : cl A = 𝒫 A := rfl

theorem mem_rl {P R : α → β → Prop} : R ∈ rl P ↔ R ⪽ P := Iff.rfl

theorem typ_eq_univ (x : α) : typ x = Set.univ := Set.union_compl_self _

theorem typ₀_eq_univ (A : Set α) : typ₀ A = Set.univ := Set.union_compl_self _

theorem clsT_eq (A : Set α) (x : α) : clsT A x = A := by
  rw [clsT, typ_eq_univ, Set.inter_univ]

theorem relT_eq (R : α → β → Prop) (x : α) : relT R x = R := by
  funext a b
  simp [relT, dres, typ_eq_univ]

theorem relTT_eq (R : α → β → Prop) (x : α) (y : β) : relTT R x y = R := by
  funext a b
  simp [relTT, dres, cres, typ_eq_univ]

/-- `R ∈ α → β . ≡ . R⃗''ᗡ'R ⊂ α . R⃖''D'R ⊂ β`, unfolded (cf. ✱70·1). -/
theorem mem_arrow_iff {A : Set (Set α)} {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow A B ↔ (∀ y, y ∈ codom R → refs R y ∈ A) ∧ (∀ x, x ∈ dom R → rels R x ∈ B) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun y hy => h1 ⟨y, hy, rfl⟩, fun x hx => h2 ⟨x, hx, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rintro X ⟨y, hy, rfl⟩
      exact h1 y hy
    · rintro X ⟨x, hx, rfl⟩
      exact h2 x hx

private theorem refs_mem_one_of {R : α → β → Prop} {y : β} (hy : y ∈ codom R) :
    refs R y ∈ one ↔ ∀ x x', R x y ∧ R x' y → x = x' := by
  constructor
  · intro h x x' ⟨hx, hx'⟩
    obtain ⟨b, hb⟩ := mem_one_iff.1 h
    exact ((hb x).1 hx).trans ((hb x').1 hx').symm
  · intro h
    obtain ⟨x, hx⟩ := hy
    exact mem_one_iff.2 ⟨x, fun z => ⟨fun hz => h z x ⟨hz, hx⟩, fun e => e ▸ hx⟩⟩

private theorem rels_mem_one_of {R : α → β → Prop} {x : α} (hx : x ∈ dom R) :
    rels R x ∈ one ↔ ∀ y y', R x y ∧ R x y' → y = y' := by
  constructor
  · intro h y y' ⟨hy, hy'⟩
    obtain ⟨b, hb⟩ := mem_one_iff.1 h
    exact ((hb y).1 hy).trans ((hb y').1 hy').symm
  · intro h
    obtain ⟨y, hy⟩ := hx
    exact mem_one_iff.2 ⟨y, fun z => ⟨fun hz => h z y ⟨hz, hy⟩, fun e => e ▸ hy⟩⟩

/-- One-many relations (cf. ✱71·17): `R ∈ 1 → Cls . ≡ : xRz . yRz . ⊃_{x,y,z} . x = y`. -/
theorem mem_arrow_one_Cls {R : α → β → Prop} :
    R ∈ arrow one Cls ↔ ∀ x y z, R x z ∧ R y z → x = y := by
  rw [mem_arrow_iff, Cls_eq_univ]
  simp only [Set.mem_univ, implies_true, and_true]
  constructor
  · intro h x y z ⟨hx, hy⟩
    exact (refs_mem_one_of ⟨x, hx⟩).1 (h z ⟨x, hx⟩) x y ⟨hx, hy⟩
  · intro h y hy
    exact (refs_mem_one_of hy).2 (fun x x' hxx' => h x x' y hxx')

/-- Many-one relations (cf. ✱71·171): `R ∈ Cls → 1 . ≡ : xRy . xRz . ⊃_{x,y,z} . y = z`. -/
theorem mem_arrow_Cls_one {R : α → β → Prop} :
    R ∈ arrow Cls one ↔ ∀ x y z, R x y ∧ R x z → y = z := by
  rw [mem_arrow_iff, Cls_eq_univ]
  simp only [Set.mem_univ, implies_true, true_and]
  constructor
  · intro h x y z ⟨hy, hz⟩
    exact (rels_mem_one_of ⟨y, hy⟩).1 (h x ⟨y, hy⟩) y z ⟨hy, hz⟩
  · intro h x hx
    exact (rels_mem_one_of hx).2 (fun y y' hyy' => h x y y' hyy')

/-- One-one relations: both one-many and many-one (cf. ✱71·172). -/
theorem mem_arrow_one_one {R : α → β → Prop} :
    R ∈ arrow one one ↔
      (∀ x y z, R x z ∧ R y z → x = y) ∧ (∀ x y z, R x y ∧ R x z → y = z) := by
  rw [mem_arrow_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun x y z ⟨hx, hy⟩ => (refs_mem_one_of ⟨x, hx⟩).1 (h1 z ⟨x, hx⟩) x y ⟨hx, hy⟩,
      fun x y z ⟨hy, hz⟩ => (rels_mem_one_of ⟨y, hy⟩).1 (h2 x ⟨y, hy⟩) y z ⟨hy, hz⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun y hy => (refs_mem_one_of hy).2 (fun x x' h => h1 x x' y h),
      fun x hx => (rels_mem_one_of hx).2 (fun y y' h => h2 x y y' h)⟩

/-- `α sm β . ≡ . (∃R) . R ∈ 1 → 1 . α = D'R . β = ᗡ'R` (Summary of ✱73). -/
theorem sm_iff {A : Set α} {B : Set β} :
    sm A B ↔ ∃ R : α → β → Prop, (R ∈ arrow one one ∧ A = dom R) ∧ B = codom R := Iff.rfl

/-- Similarity is equinumerosity: `α sm β` iff there is a bijection between `α` and `β`. -/
theorem sm_iff_nonempty_equiv {A : Set α} {B : Set β} : sm A B ↔ Nonempty (A ≃ B) := by
  rw [sm_iff]
  constructor
  · rintro ⟨R, ⟨hR, rfl⟩, rfl⟩
    obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
    have hex : ∀ x : dom R, ∃ y, R x y := fun x => x.2
    choose f hf using hex
    refine ⟨Equiv.ofBijective (fun x => ⟨f x, x, hf x⟩) ⟨?_, ?_⟩⟩
    · intro a b hab
      have e : f a = f b := congrArg Subtype.val hab
      apply Subtype.ext
      have hb : R b (f a) := by rw [e]; exact hf b
      exact h1 a b (f a) ⟨hf a, hb⟩
    · rintro ⟨y, x, hxy⟩
      exact ⟨⟨x, y, hxy⟩, Subtype.ext (h2 x _ _ ⟨hf ⟨x, y, hxy⟩, hxy⟩)⟩
  · rintro ⟨e⟩
    refine ⟨fun x y => ∃ h : x ∈ A, (e ⟨x, h⟩ : β) = y, ⟨?_, ?_⟩, ?_⟩
    · refine mem_arrow_one_one.2 ⟨?_, ?_⟩
      · rintro x y z ⟨⟨hx, hxz⟩, ⟨hy, hyz⟩⟩
        have : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext (hxz.trans hyz.symm)
        exact congrArg Subtype.val (e.injective this)
      · rintro x y z ⟨⟨hx, hxy⟩, ⟨hx', hxz⟩⟩
        exact hxy.symm.trans hxz
    · ext x
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
    · ext y
      constructor
      · intro hy
        refine ⟨(e.symm ⟨y, hy⟩ : α), (e.symm ⟨y, hy⟩).2, ?_⟩
        simp
      · rintro ⟨x, h, rfl⟩
        exact (e ⟨x, h⟩).2

/-- Similarity is reflexive (✱73·3). -/
theorem sm_refl (A : Set α) : sm A A := sm_iff_nonempty_equiv.2 ⟨Equiv.refl _⟩

/-- Similarity is symmetrical (✱73·31). -/
theorem sm_symm {A : Set α} {B : Set β} (h : sm A B) : sm B A :=
  sm_iff_nonempty_equiv.2 ⟨(Classical.choice (sm_iff_nonempty_equiv.1 h)).symm⟩

/-- Similarity is transitive (✱73·32). -/
theorem sm_trans {A : Set α} {B : Set β} {G : Set γ} (h₁ : sm A B) (h₂ : sm B G) : sm A G :=
  sm_iff_nonempty_equiv.2
    ⟨(Classical.choice (sm_iff_nonempty_equiv.1 h₁)).trans
      (Classical.choice (sm_iff_nonempty_equiv.1 h₂))⟩

/-- `R ∈ P_Δ'κ . ≡ . R ∈ 1 → Cls . R ⊂̇ P . ᗡ'R = κ` (✱80·14). -/
theorem mem_sel_iff {P M : α → β → Prop} {K : Set β} :
    M ∈ sel P K ↔ (M ∈ arrow one Cls ∧ M ⪽ P) ∧ codom M = K :=
  ⟨fun ⟨h, e⟩ => ⟨h, e.symm⟩, fun ⟨h, e⟩ => ⟨h, e.symm⟩⟩

/-- The multiplicative axiom is a theorem of Lean (by `Classical.choice`; Basic §4). Keep `Mult ax`
as a hypothesis wherever PM has it. -/
theorem multAx_holds (α : Type u) : MultAx α := by
  intro K hK
  obtain ⟨hexcl, hnull⟩ := hK
  have hne : ∀ A, A ∈ K → A.Nonempty := by
    intro A hA
    by_contra h
    apply hnull
    show Λ ∈ K
    rw [Null_eq_empty, ← Set.not_nonempty_iff_eq_empty.1 h]
    exact hA
  refine ⟨{x | ∃ B, ∃ hB : B ∈ K, x = (hne B hB).some}, fun A hA => ?_⟩
  refine ⟨(hne A hA).some, Set.ext fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨B, hB, rfl⟩, hzA⟩
    have hAB : A = B := by
      by_contra hAB
      have hcap := hexcl A B ⟨⟨hA, hB⟩, hAB⟩
      have hmem : (hne B hB).some ∈ A ∩ B := ⟨hzA, (hne B hB).some_mem⟩
      rw [hcap, Null_eq_empty] at hmem
      exact hmem
    subst hAB
    rfl
  · rintro rfl
    exact ⟨⟨A, hA, rfl⟩, (hne A hA).some_mem⟩

/-- The ancestral is the reflexive-transitive closure, restricted (as PM restricts it) to
referents in the field: `x R_* y . ≡ . x ∈ C'R . x (R*) y`. -/
theorem anc_iff_reflTransGen {R : α → α → Prop} {x y : α} :
    anc R x y ↔ x ∈ fld R ∧ Relation.ReflTransGen R x y := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, h {z | Relation.ReflTransGen R x z} ⟨?_, Relation.ReflTransGen.refl⟩⟩
    rintro z ⟨w, hw, hwz⟩
    exact Relation.ReflTransGen.tail hw hwz
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun M ⟨hM, hxM⟩ => ?_⟩
    induction h with
    | refl => exact hxM
    | tail _ hbc ih => exact hM ⟨_, ih, hbc⟩

theorem relProdR_apply (S : β → γ → Prop) (U : α → γ → Prop) (X : α → β → Prop) :
    relProdR S U X ↔ U = X ⨾ S := Iff.rfl

theorem relProdL_apply (R : α → β → Prop) (U : α → γ → Prop) (X : β → γ → Prop) :
    relProdL R U X ↔ U = R ⨾ X := Iff.rfl

/-- `S ∈ Pot'R` iff `S` is reached from `R` by finitely many steps `S ↦ S | R`. -/
theorem mem_pot_iff {R S : α → α → Prop} :
    S ∈ pot R ↔ S ∈ fld (relProdR R) ∧ Relation.ReflTransGen (relProdR R) S R :=
  anc_iff_reflTransGen

theorem self_mem_pot (R : α → α → Prop) : R ∈ pot R :=
  mem_pot_iff.2 ⟨⟨R ⨾ R, Or.inr rfl⟩, Relation.ReflTransGen.refl⟩

theorem relProd_mem_pot {R S : α → α → Prop} (h : S ∈ pot R) : S ⨾ R ∈ pot R :=
  mem_pot_iff.2 ⟨⟨S, Or.inl rfl⟩, Relation.ReflTransGen.head rfl (mem_pot_iff.1 h).2⟩

/-- `R_po` is the transitive closure of `R`. -/
theorem po_iff_transGen {R : α → α → Prop} {x y : α} :
    po R x y ↔ Relation.TransGen R x y := by
  constructor
  · rintro ⟨S, hS, hxy⟩
    have key : ∀ S, Relation.ReflTransGen (relProdR R) S R →
        ∀ x y, S x y → Relation.TransGen R x y := by
      intro S h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => exact fun x y h => Relation.TransGen.single h
      | head hac _ ih =>
        intro x y hxy
        rw [relProdR_apply] at hac
        rw [hac] at hxy
        obtain ⟨z, hxz, hzy⟩ := hxy
        exact Relation.TransGen.tail (ih x z hxz) hzy
    exact key S (mem_pot_iff.1 hS).2 x y hxy
  · intro h
    induction h with
    | single hxy => exact ⟨R, self_mem_pot R, hxy⟩
    | tail _ hbc ih =>
      obtain ⟨S, hS, hxb⟩ := ih
      exact ⟨S ⨾ R, relProd_mem_pot hS, _, hxb, hbc⟩

/-- `R_* = I ↾ C'R ∪̇ R_po` (✱91·54), pointwise. -/
theorem anc_iff_po {R : α → α → Prop} {x y : α} :
    anc R x y ↔ (x = y ∧ x ∈ fld R) ∨ po R x y := by
  rw [anc_iff_reflTransGen, po_iff_transGen, Relation.reflTransGen_iff_eq_or_transGen]
  constructor
  · rintro ⟨hx, rfl | h⟩
    · exact Or.inl ⟨rfl, hx⟩
    · exact Or.inr h
  · rintro (⟨rfl, hx⟩ | h)
    · exact ⟨hx, Or.inl rfl⟩
    · obtain ⟨b, hxb, -⟩ := Relation.TransGen.head'_iff.1 h
      exact ⟨⟨b, Or.inl hxb⟩, Or.inr h⟩

/-- `R̆_*` is `(R̆)_*` (✱90·132), pointwise. -/
theorem ancCnv_iff {R : α → α → Prop} {x y : α} : ancCnv R x y ↔ anc R˘ x y := by
  show anc R y x ↔ anc R˘ x y
  rw [anc_iff_reflTransGen, anc_iff_reflTransGen]
  have hfld : fld R˘ = fld R := by
    ext z
    exact ⟨fun ⟨w, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, h.symm⟩⟩
  rw [hfld]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨?_, Relation.reflTransGen_swap.2 h⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with rfl | h'
    · exact hy
    · obtain ⟨b, -, hbx⟩ := Relation.TransGen.tail'_iff.1 h'
      exact ⟨b, Or.inr hbx⟩
  · rintro ⟨hx, h⟩
    refine ⟨?_, Relation.reflTransGen_swap.1 h⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with rfl | h'
    · exact hx
    · obtain ⟨b, -, hby⟩ := Relation.TransGen.tail'_iff.1 h'
      exact ⟨b, Or.inl hby⟩

/-- `x B P . ≡ . x ∈ D'P − ᗡ'P` (✱93·1). -/
theorem Beg_apply (x : α) (P : α → α → Prop) : Beg x P ↔ x ∈ dom P ∧ x ∉ codom P := Iff.rfl

theorem minP_apply (P : α → α → Prop) (x : α) (A : Set α) :
    minP P x A ↔ (x ∈ A ∧ x ∈ fld P) ∧ ¬ ∃ y, y ∈ A ∧ P y x := Iff.rfl

theorem coupleL_apply (x : α) (R : α → β → Prop) (y : β) : coupleL x R y ↔ R = x ↓ y := Iff.rfl

/-! The descriptive functions of the `graph` relations of this Part, in a form `rw` can use
(`ψ(F'y) ↔ ψ (f y)`, Basic §5). -/

/-- `ψ((x↓)'y) ↔ ψ(x ↓ y)` (cf. ✱55·11). -/
theorem desc_coupleL (x : α) (y : β) (ψ : (α → β → Prop) → Prop) :
    Desc (coupleL x) y ψ ↔ ψ (x ↓ y) := desc_graph _ _ _

/-- `ψ((↓y)'x) ↔ ψ(x ↓ y)` (cf. ✱55·121). -/
theorem desc_coupleR (y : β) (x : α) (ψ : (α → β → Prop) → Prop) :
    Desc (coupleR y) x ψ ↔ ψ (x ↓ y) := desc_graph _ _ _

theorem desc_Cl (A : Set α) (ψ : Set (Set α) → Prop) : Desc Cl A ψ ↔ ψ (cl A) := desc_graph _ _ _

theorem desc_ClEx (A : Set α) (ψ : Set (Set α) → Prop) : Desc ClEx A ψ ↔ ψ (clEx A) :=
  desc_graph _ _ _

theorem desc_Rl (P : α → β → Prop) (ψ : Set (α → β → Prop) → Prop) : Desc Rl P ψ ↔ ψ (rl P) :=
  desc_graph _ _ _

theorem desc_RlEx (P : α → β → Prop) (ψ : Set (α → β → Prop) → Prop) :
    Desc RlEx P ψ ↔ ψ (rlEx P) := desc_graph _ _ _

theorem desc_selRel (P : α → β → Prop) (K : Set β) (ψ : Set (α → β → Prop) → Prop) :
    Desc (selRel P) K ψ ↔ ψ (sel P K) := desc_graph _ _ _

theorem desc_ClExcl (G : Set (Set α)) (ψ : Set (Set (Set α)) → Prop) :
    Desc ClExcl G ψ ↔ ψ (clExcl G) := desc_graph _ _ _

theorem desc_Pot (R : α → α → Prop) (ψ : Set (α → α → Prop) → Prop) : Desc Pot R ψ ↔ ψ (pot R) :=
  desc_graph _ _ _

theorem desc_Potid (R : α → α → Prop) (ψ : Set (α → α → Prop) → Prop) :
    Desc Potid R ψ ↔ ψ (potid R) := desc_graph _ _ _

theorem desc_Gen (P : α → α → Prop) (ψ : Set (Set α) → Prop) : Desc Gen P ψ ↔ ψ (gen P) :=
  desc_graph _ _ _

theorem desc_Rboth (R : α → α → Prop) (x : α) (ψ : Set α → Prop) :
    Desc (Rboth R) x ψ ↔ ψ (refsRels R x) := desc_graph _ _ _

/-- `ψ((P∗Q)'R) ↔ ψ((P‖Q)⃗_*'R)` (✱95·01): `(P∗Q)'R` is `refs (anc (P ∥ Q)) R`. -/
theorem desc_eqf (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop)
    (ψ : Set (α → β → Prop) → Prop) : Desc (eqf P Q) R ψ ↔ ψ (refs (anc (P ∥ Q)) R) :=
  desc_graph _ _ _

/-- The precedences realize PM's bracketing of couples (✱55·5, ✱80·41) and of ✱93·02. -/
example (x z : α) (y w : β) (R : α → β → Prop) (S : γ → α → Prop) (P : α → α → Prop)
    (A : Set α) :
    (x ↓ y ⊍ z ↓ w = (x ↓ y) ⊍ (z ↓ w)) ∧ (S ⨾ x ↓ y = S ⨾ (x ↓ y)) ∧
    (R ∸ z ↓ y = R ∸ (z ↓ y)) ∧ (ι x ∪ ι z = (ι x) ∪ (ι z)) ∧
    ((A ∩ fld P) \ P˘ ʻʻ A = (A ∩ fld P) \ (P˘ ʻʻ A)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Sanity

end PrincipiaMathematica
