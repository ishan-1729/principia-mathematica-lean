import PrincipiaMathematica.Defs.Part4

/-!
# Part V (Series): the definitions

Every definition (Df) of ✱200–✱234 (Volume II: Section A, general theory of series, ✱200–✱208;
Section B, sections, segments, stretches and derivatives, ✱210–✱217; Section C, convergence and
the limits of functions, ✱230–✱234), in PM's order, in the format of `Defs/Part1.lean`: each entry
is headed `**✱N·M Df.**` with the formula as printed (MathJax TeX, from `data/principia.json`),
says how it is read in Lean and gives the *target statement* of `pmN_M` (status `definition`;
every target below has been checked to elaborate and to hold by `rfl`). ✱200, ✱205, ✱210, ✱217
have no Df (`max_P`, `min_P` are ✱93·02·021, `minP`, `maxP` in `Defs/Part2`). Then come the sanity
lemmas the Section files use (unfolded forms of `trans`, `connex`, `Ser`, `min_P`, `max_P`,
`seq_P`, `lt_P`, `limax_P`, `sect`, `ς`, `cror`, the segments of `P_*` (= `sect'P`), `Q_cn`, `P R̄_sc Q`; `prec_P = seq(P̆)`,
`tl_P = lt(P̆)`, `limin_P = limax(P̆)`; for transitive `P`, `P_po = P` and
`P_* = P ∪̇ I ↾ C'P`; `P_1` is the relation of `x` to `y` when `P(x⊢⊣y)` has two members, and is `P −̇ P²` when `P`
is transitive and contained in diversity; and the `desc_…` lemmas of the new relations).

## Encoding decisions (in addition to Basic §1–§10 and Defs/Part2–Part4)

1. *Homogeneity and types.* Serial notions are about homogeneous relations: `trans`, `connex`,
   `Ser`, `Ded`, `semi Ded` are classes `Set (α → α → Prop)`; `seq_P`, `prec_P`, `lt_P`, `tl_P`,
   `limax_P`, `limin_P` (like `min_P`, `max_P`) are relations `α → Set α → Prop` of a term to a
   class; `sect'P`, `str'P`, `dense'P`, `closed'P`, `perf'P` are `Set (Set α)`; `ς'P`, `sgm'P`
   are relations of classes (`Set α → Set α → Prop`); `P_ς` is a relation of relations
   (`(α → α → Prop) → (α → α → Prop) → Prop`). In Section C (Summary of Section C), `Q` is the
   *argument-series* `Q : β → β → Prop`, `P` the *value-series* `P : α → α → Prop`, and the
   function `R : α → β → Prop` is the relation of the value to the argument (`x R y`: `x` is a
   value for the argument `y`; `R'y` is the value when `R` is one-many). `P`, `Q` may be of
   different types.
2. *Descriptive functions* (Basic §5). The relations `seq_P`, `prec_P`, `lt_P`, `tl_P`, `limax_P`,
   `limin_P`, `(P R̄ Q)_lmx`, `R(PQ)` (like `min_P`, `max_P`, `B`) are many-valued in general, so
   their descriptive functions are **never** Lean functions: `ψ(seq_P'α)` is
   `Desc (seqP P) A ψ`, `E!lt_P'α` is `EDesc (ltP P) A`, `ψ(R(PQ)'a)` is `Desc (rlim R P Q) a ψ`,
   `ψ((P R̄ Q)_lmx'α)` is `Desc (lmx P R Q) A ψ`; the classes of values are written with `refs`:
   `seq⃗_P'α` is `refs (seqP P) A`, `lt⃗_P'α` is `refs (ltP P) A`, `limax⃗_P'α` is
   `refs (limaxP P) A`. In ✱234·03 the value `R'a` of the function is a description, kept as
   `Desc R a ψ`.
   The descriptive functions *defined* by a Df of this Part always exist, and are written by their
   value functions: `sect'P` is `sect P`, `cror'P` is `cror P`, `ς'P` is `segSer P`, `sgm'P` is
   `sgm P`, `str'P` is `str P`, `δ_P'α` is `derivCls P A`, `dense'P` is `dense P`,
   `closed'P` is `closed P`, `perf'P` is `perf P`, `∇'P` is `nabla P`, `(P R̄ Q)_sc'α` is
   `scFun P R Q A`, `(P R̄ Q)_os'α` is `osFun P R Q A`, `sc(P,Q)'R` is `scPQ P Q R`,
   `os(P,Q)'R` is `osPQ P Q R`, `ct(PQ)'R` is `ct P Q R`, `contin(PQ)'R` is `contin P Q R`.
   The relations themselves (Summary of Part I, Section E: `R'x = …` defines `R = ûx̂(u = …)`) are
   `graph` of these functions: `Sect`, `Cror`, `SegSer`, `Sgm`, `Str`, `DerivRel P` (`δ_P`),
   `DenseRel`, `ClosedRel`, `PerfRel`, `Nabla`, `scRel P R Q` (`(P R̄ Q)_sc`, which ✱233·01
   uses as a relation), `osRel P R Q`, `ScPQ P Q`, `OsPQ P Q`, `Ct P Q`, `Contin P Q`; rewrite
   descriptions with the `desc_…` lemmas at the end of this file.
   `R Q̄_cn α`, `P R̄_sc Q`, `P R̄_os Q` are terms (functions of three arguments, like `α sm̄ β`):
   `cnBar R Q A`, `scBar P R Q`, `osBar P R Q`. `Q_cn` is the relation `cn Q`, and
   `Q⃖_cn'R` is `rels (cn Q) R`. `P contin̄ Q` is the class `continBar P Q`.
3. *The constant `P_1`* (✱121·02 with `ν = 1`). `P_ν` (`Pnu P ν`) leaves the type of `ν` free; in
   `P_1` the `1` is taken in the type of the field of `P`: `P_1` is `P1 P := Pnu P (one : Set (Set
   α))`. The value is the same in every type in which `1` exists (`Pnu_one_eq_P1`), and
   `P1_iff`: `x P_1 y` iff `P(x⊢⊣y)` has exactly two members. Write `P1 P` for PM's `P_1`
   (e.g. `C'P_1` is `fld (P1 P)`, `xP_1y` is `P1 P x y`).
4. *Converses.* PM proves facts about `prec_P`, `tl_P`, `limin_P`, `max_P` from those about
   `seq_P`, `lt_P`, `limax_P`, `min_P` by `prec_P = seq(P̆)` (✱206·101), `tl_P = lt(P̆)` (✱207·101),
   `limin_P = limax(P̆)` (✱207·401), `max_P = min(P̆)` (✱93·021). The first three are
   propositional equalities here (`precP_eq_seqP_cnv`, `tlP_eq_ltP_cnv`,
   `liminP_eq_limaxP_cnv`; `fld P˘ = fld P` is `fld_cnv`), the last holds by `rfl`.
   `seq(P̆)` is `seqP P˘`, `lt(ς'P)` is `ltP (segSer P)`, `limax(ς'P_*)` is
   `limaxP (segSer (anc P))`, `max(P⃗;P)` is `maxP (Rfwd P ⁏ P)`.
5. *Names that shadow.* PM's `trans` is `transR` (Lean's root `trans` would be shadowed inside
   the namespace). Do not bind variables named `Ser`, `Ded`, `P1`, `Sect`, `Str`, `Cror`, `Sgm`,
   `Nabla`, `Ct`, `Contin`, `cn`, `ct`, `sgm`, `str`, `sect`.
6. *Errata.* The only erratum to the enunciations of Part V (✱205·7, `max⃗_P` for `max_P`, Errata
   to Volume II) is already incorporated in the e-text (Basic §9). The e-text prints a lower-case
   subscript `p` for `P` in ✱216·01–·05 (`δ_p`, `lt_p`, `min⃗_p`, `limax_p`), and the Summary of
   ✱232 prints `P R̄_{os}` without roman type: these are typographical only.

## Symbol table: PM → Lean (extends Basic §7 and Defs/Part2–Part4)

| PM | Df | Lean |
|----|----|------|
| `trans` | ✱201·01 | `transR` |
| `connex` | ✱202·01 | `connex` |
| `Ser` | ✱204·01 | `Ser` |
| `seq_P`, `seq⃗_P'α`, `seq_P'α` | ✱206·01 | `seqP P`, `refs (seqP P) A`, `Desc (seqP P) A ψ` |
| `prec_P` | ✱206·02 | `precP P` |
| `lt_P`, `lt(P)`, `tl_P`, `tl(P)` | ✱207·01·02 | `ltP P`, `tlP P` |
| `limax_P`, `limin_P` | ✱207·03·04 | `limaxP P`, `liminP P` |
| `cror'P` | ✱208·01 | `cror P` (relation `Cror`) |
| `sect'P` | ✱211·01 | `sect P` (relation `Sect`) |
| `ς'P`, `sgm'P` | ✱212·01·02 | `segSer P`, `sgm P` (relations `SegSer`, `Sgm`) |
| `P_ς` | ✱213·01 | `Psec P` |
| `Ded`, `semi Ded` | ✱214·01·02 | `Ded`, `semiDed` |
| `str'P` | ✱215·01 | `str P` (relation `Str`) |
| `δ_P'α`, `δ_P` | ✱216·01 | `derivCls P A`, `DerivRel P` |
| `dense'P`, `closed'P`, `perf'P` | ✱216·02–·04 | `dense P`, `closed P`, `perf P` |
| `∇'P` | ✱216·05 | `nabla P` (relation `Nabla`) |
| `R Q̄_cn α`, `Q_cn`, `Q⃖_cn'R` | ✱230·01·02 | `cnBar R Q A`, `cn Q`, `rels (cn Q) R` |
| `P R̄_sc Q`, `P R̄_os Q` | ✱231·01·02 | `scBar P R Q`, `osBar P R Q` |
| `(P R̄ Q)_sc'α`, `(P R̄ Q)_sc` | ✱232·01 | `scFun P R Q A`, `scRel P R Q` |
| `(P R̄ Q)_os'α`, `(P R̄ Q)_os` | ✱232·02 | `osFun P R Q A`, `osRel P R Q` |
| `(P R̄ Q)_lmx` | ✱233·01 | `lmx P R Q` |
| `R(PQ)` | ✱233·02 | `rlim R P Q` |
| `sc(P,Q)'R`, `os(P,Q)'R` | ✱234·01·02 | `scPQ P Q R`, `osPQ P Q R` (relations `ScPQ P Q`, `OsPQ P Q`) |
| `ct(PQ)'R`, `contin(PQ)'R` | ✱234·03·04 | `ct P Q R`, `contin P Q R` (relations `Ct P Q`, `Contin P Q`) |
| `P contin̄ Q` | ✱234·05 | `continBar P Q` |
| `P_1` (✱121·02, `ν = 1`) | — | `P1 P` |

Precedences: Part V adds no infix notation; every sign is a name, and application binds tightest
(`refs (seqP P) A ∩ fld P`, `ltP P ʻʻ clEx (A ∩ fld P)`, `rels (cn Q) R`). PM's bracketing is
realized with the precedences of Basic §7 and Defs/Part4: in ✱213·01 `P⥏;(ς'P_*)⥏(−ι'Λ)` is
`opL fres P ⁏ (segSer (anc P) ⥏ (ι Λ)ᶜ)` (`⥏` 68 binds tighter than `⁏` 66, so the brackets may
be omitted, as PM omits them: the field of `ς'P_*` is limited to the non-null sections, Summary of
✱213); `P⥏` is the relation `opL fres P` of `P ⥏ α` to `α` (✱38·01); `−ᗡ'max_P` is
`(codom (maxP P))ᶜ`; `P''α ∩ P̆''α` is `P ʻʻ A ∩ P˘ ʻʻ A` (`ʻʻ` 80 binds tighter than `∩`).
-/

namespace PrincipiaMathematica

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Section A: general theory of series (✱200–✱208) -/

/-- **✱201·01 Df.** \(\text{trans}=\hat{P} (P^{2}\,\unicode{x2abd}\, P) \quad\text{Df}\)

The class of transitive relations, PM's `trans` (named `transR`: Lean's root `trans` would be
shadowed inside the namespace). Homogeneous. Target:
`pm201_01 : (transR : Set (α → α → Prop)) = {P | rsq P ⪽ P} := rfl`. -/
def transR : Set (α → α → Prop) := {P | rsq P ⪽ P}

/-- **✱202·01 Df.** \(\text{connex} =\hat{P} \{x\in CʻP.\supset _{x}.\overleftrightarrow{P}ʻx=CʻP\} \quad\text{Df}\)

Connected relations: for every `x` in the field, `P⃡'x` (`refsRels P x`, ✱97·01: the
predecessors, `x` itself, and the successors of `x`) is the whole field. Target:
`pm202_01 : (connex : Set (α → α → Prop)) = {P | ∀ x, x ∈ fld P → refsRels P x = fld P} := rfl`.
(`mem_connex` gives the form ✱202·103.) -/
def connex : Set (α → α → Prop) := {P | ∀ x, x ∈ fld P → refsRels P x = fld P}

/-- **✱204·01 Df.** \(\text{Ser} = \text{Rl}ʻJ \cap \text{trans} \cap \text{connex} \quad\text{Df}\)

Serial relations: contained in diversity (`Rl'J` is `rl J`), transitive and connected; the
product of three brackets to the left (✱22·53). `mem_Ser` unfolds it. Target:
`pm204_01 : (Ser : Set (α → α → Prop)) = rl J ∩ transR ∩ connex := rfl`. -/
def Ser : Set (α → α → Prop) := rl J ∩ transR ∩ connex

/-- **✱206·01 Df.** \(\text{seq}_{P}=\hat{x} \hat{\alpha} \{x\text{min}_{P}pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\} \quad\text{Df}\)

`x seq_P α`: `x` is a minimum of the terms that follow every member of `α ∩ C'P`, i.e. a
"sequent" of `α`. `P⃖''(α ∩ C'P)` is `Rbwd P ʻʻ (A ∩ fld P)` (the classes of successors of the
members), `p'` is `prodCls`. `seq_P'α` need not exist: `Desc (seqP P) A ψ`; `seq⃗_P'α` is
`refs (seqP P) A`. `seqP_iff` unfolds it. Target:
`pm206_01 : seqP P = fun x A => minP P x (prodCls (Rbwd P ʻʻ (A ∩ fld P))) := rfl`. -/
def seqP (P : α → α → Prop) : α → Set α → Prop :=
  fun x A => minP P x (prodCls (Rbwd P ʻʻ (A ∩ fld P)))

/-- **✱206·02 Df.** \(\text{prec}_{P}=\hat{x} \hat{\alpha} \{x\text{max}_{P}pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)\} \quad\text{Df}\)

`x prec_P α`: `x` is a maximum of the terms that precede every member of `α ∩ C'P` (the
"precedent" of `α`). `precP P = seqP P˘` (`precP_eq_seqP_cnv`, ✱206·101). Target:
`pm206_02 : precP P = fun x A => maxP P x (prodCls (Rfwd P ʻʻ (A ∩ fld P))) := rfl`. -/
def precP (P : α → α → Prop) : α → Set α → Prop :=
  fun x A => maxP P x (prodCls (Rfwd P ʻʻ (A ∩ fld P)))

/-- **✱207·01 Df.** \(\text{lt}_P=\text{lt}(P)=\text{seq}_{P}\upharpoonright (-\text{ᗡ}ʻ\text{max}_{P}) \quad\text{Df}\)

The upper limit: a sequent of a class which has no maximum. `lt(P)` is another notation for the
same relation `ltP P`. `−ᗡ'max_P` is `(codom (maxP P))ᶜ`. `lt_P'α` need not exist
(`Desc (ltP P) A ψ`). Target: `pm207_01 : ltP P = seqP P ↾ (codom (maxP P))ᶜ := rfl`. -/
def ltP (P : α → α → Prop) : α → Set α → Prop := seqP P ↾ (codom (maxP P))ᶜ

/-- **✱207·02 Df.** \(\text{tl}_P=tl(P)=\text{prec}_{P}\upharpoonright (-\text{ᗡ}ʻ\text{min}_{P}) \quad\text{Df}\)

The lower limit; `tlP P = ltP P˘` (`tlP_eq_ltP_cnv`, ✱207·101). Target:
`pm207_02 : tlP P = precP P ↾ (codom (minP P))ᶜ := rfl`. -/
def tlP (P : α → α → Prop) : α → Set α → Prop := precP P ↾ (codom (minP P))ᶜ

/-- **✱207·03 Df.** \(\text{limax}_P=\text{max}_{P}\unicode{x228d} \text{lt}_P \quad\text{Df}\)

"Limit or maximum". Target: `pm207_03 : limaxP P = maxP P ⊍ ltP P := rfl`. -/
def limaxP (P : α → α → Prop) : α → Set α → Prop := maxP P ⊍ ltP P

/-- **✱207·04 Df.** \(\text{limin}_P=\text{min}_{P}\unicode{x228d} \text{tl}_P \quad\text{Df}\)

"Lower limit or minimum"; `liminP P = limaxP P˘` (`liminP_eq_limaxP_cnv`, ✱207·401). Target:
`pm207_04 : liminP P = minP P ⊍ tlP P := rfl`. -/
def liminP (P : α → α → Prop) : α → Set α → Prop := minP P ⊍ tlP P

/-- **✱208·01 Df.** \(\text{cror}ʻP=sʻ\,\overline{\,\text{smor}\,}\,Pʻʻ\text{Rl}ʻP \quad\text{Df}\)

The correlators of `P` with parts (or the whole) of itself. `smor̄ P` is the relation of
`Q smor̄ P` to `Q` (✱38·02 with `♀ = smor̄`), i.e. `opR smorbar P`; `Rl'P` is `rl P`; `s'` is
`sumCls`. So `S ∈ cror'P` iff `S` correlates some `Q ⊂̇ P` with `P` (`mem_cror`, ✱208·1:
`S ∈ 1 → 1 . ᗡ'S = C'P . S;P ⊂̇ P`). Value function of `Cror`. Target:
`pm208_01 : cror P = sumCls (opR smorbar P ʻʻ rl P) := rfl`. -/
def cror (P : α → α → Prop) : Set (α → α → Prop) := sumCls (opR smorbar P ʻʻ rl P)

/-- The relation `cror` of `cror'P` to `P` (✱208·01 defines its descriptive function). -/
def Cror : Set (α → α → Prop) → (α → α → Prop) → Prop := graph cror

/-! ## Section B: sections, segments, stretches, and derivatives (✱210–✱217) -/

/-- **✱211·01 Df.** \(\text{sect}ʻP=\hat{\alpha} (\alpha \subset CʻP.Pʻʻ\alpha \subset \alpha ) \quad\text{Df}\)

The sections of `P`: sub-classes of the field containing all predecessors of their members
(`P''α` is `P ʻʻ A`). Value function of `Sect`. Target:
`pm211_01 : sect P = {A | A ⊆ fld P ∧ P ʻʻ A ⊆ A} := rfl`. -/
def sect (P : α → α → Prop) : Set (Set α) := {A | A ⊆ fld P ∧ P ʻʻ A ⊆ A}

/-- The relation `sect` of `sect'P` to `P`. -/
def Sect : Set (Set α) → (α → α → Prop) → Prop := graph sect

/-- **✱212·01 Df.** \(\varsigma ʻP=P_{\text{lc}}\unicode{x0294f}\text{D}ʻP_{\in } \quad\text{Df}\)

`ς'P`, the series of segments of `P` (named `segSer`): `P_lc` (`Plc P`, ✱170·02) with field
limited to the segments `D'P_∈` (`dom (imgRel P)`, the classes `P''β`). Value function of
`SegSer`. Target: `pm212_01 : segSer P = Plc P ⥏ dom (imgRel P) := rfl`. -/
def segSer (P : α → α → Prop) : Set α → Set α → Prop := Plc P ⥏ dom (imgRel P)

/-- The relation `ς` of `ς'P` to `P`. -/
def SegSer : (Set α → Set α → Prop) → (α → α → Prop) → Prop := graph segSer

/-- **✱212·02 Df.** \(\text{sgm}ʻP=P_{\text{lc}}\unicode{x0294f}\text{D}ʻ(P_{\in }\dot{\cap} I) \quad\text{Df}\)

The series of segments having no maximum: `D'(P_∈ ∩̇ I)` is `dom (imgRel P ⩀ I)`, the classes
`α` with `α = P''α`. Value function of `Sgm`. Target:
`pm212_02 : sgm P = Plc P ⥏ dom (imgRel P ⩀ I) := rfl`. -/
def sgm (P : α → α → Prop) : Set α → Set α → Prop := Plc P ⥏ dom (imgRel P ⩀ I)

/-- The relation `sgm` of `sgm'P` to `P`. -/
def Sgm : (Set α → Set α → Prop) → (α → α → Prop) → Prop := graph sgm

/-- **✱213·01 Df.** \(P_{\varsigma }=P\unicode{x0294f}^{;}(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda ) \quad\text{Df}\)

`P_ς`, the series of sectional relations `P ⥏ α` (named `Psec`). `ς'P_*` is
`segSer (anc P)` (the series of sections, Summary of Section B), its field limited to the
non-null sections (`−ι'Λ` is `(ι Λ)ᶜ`), then carried over by the relation `P⥏` of `P ⥏ α` to
`α` (`opL fres P`, ✱38·01). The bracketing is `P⥏;{(ς'P_*)⥏(−ι'Λ)}`: ✱213·12 writes
`D'(ς'P_*)⥏(−ι'Λ)` for the series of non-null sections, and the Summary of ✱213 says "we confine
ourselves to sections which are not null". (The other bracketing `(P⥏;ς'P_*)⥏(−ι'Λ̇)`, with `Λ`
read as `Λ̇` by the Vol. I erratum of p. 218, would also exclude every non-null section `α` with
`P ⥏ α = Λ̇`, e.g. `ι'B'P` when `P ⊂̇ J`; it is not PM's.) `⁏` (66) is looser than `⥏` (68). With this reading
✱213·1 (`Q P_ς R ≡ (∃α,β) . α,β ∈ sect'P − ι'Λ . ∃!β − α . Q = P⥏α . R = P⥏β`) has been checked
to hold (via `segSer_apply`, `Psec_apply` and `mem_dom_imgRel_anc`). Target:
`pm213_01 : Psec P = opL fres P ⁏ (segSer (anc P) ⥏ (ι Λ)ᶜ) := rfl`. -/
def Psec (P : α → α → Prop) : (α → α → Prop) → (α → α → Prop) → Prop :=
  opL fres P ⁏ (segSer (anc P) ⥏ (ι Λ)ᶜ)

/-- **✱214·01 Df.** \(\text{Ded} = \hat{P}\{(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}\} \quad\text{Df}\)

Dedekindian relations: every class has a maximum or a sequent. Target:
`pm214_01 : (Ded : Set (α → α → Prop)) =
{P | ∀ A : Set α, A ∈ codom (maxP P) ∪ codom (seqP P)} := rfl`. -/
def Ded : Set (α → α → Prop) := {P | ∀ A : Set α, A ∈ codom (maxP P) ∪ codom (seqP P)}

/-- **✱214·02 Df.** \(\text{semi Ded} = \hat{P} (\text{sect}ʻP-\iota ʻCʻP\subset \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}) \quad\text{Df}\)

Semi-Dedekindian relations: every section other than the whole field has a maximum or a sequent.
(PM prints this Df in the Summary of ✱214; `data/principia.json` also lists it as ✱214·02.)
Target:
`pm214_02 : (semiDed : Set (α → α → Prop)) =
{P | sect P \ ι (fld P) ⊆ codom (maxP P) ∪ codom (seqP P)} := rfl`. -/
def semiDed : Set (α → α → Prop) := {P | sect P \ ι (fld P) ⊆ codom (maxP P) ∪ codom (seqP P)}

/-- **✱215·01 Df.** \(\text{str}ʻP=\hat{\alpha} (\alpha \subset CʻP.Pʻʻ\alpha \cap \breve{P} ʻʻ\alpha \subset \alpha ) \quad\text{Df}\)

The stretches of `P`: sub-classes of the field containing every term that comes between two of
their members. Value function of `Str`. Target:
`pm215_01 : str P = {A | A ⊆ fld P ∧ P ʻʻ A ∩ P˘ ʻʻ A ⊆ A} := rfl`. -/
def str (P : α → α → Prop) : Set (Set α) := {A | A ⊆ fld P ∧ P ʻʻ A ∩ P˘ ʻʻ A ⊆ A}

/-- The relation `str` of `str'P` to `P`. -/
def Str : Set (Set α) → (α → α → Prop) → Prop := graph str

/-- **✱216·01 Df.** \(\delta _{p}ʻ\alpha =\text{lt}_{p}ʻʻ\text{Cl ex}ʻ(\alpha \cap CʻP)\quad\text{Df}\)

The derivative `δ_P'α` of `α` with respect to `P` (the e-text prints the subscript `p`): the
limits of existent sub-classes of `α ∩ C'P` (`Cl ex'` is `clEx`). Value function of the relation
`δ_P` (`DerivRel P`); `δ_P²'α` is `derivCls P (derivCls P A)`. Target:
`pm216_01 : derivCls P A = ltP P ʻʻ clEx (A ∩ fld P) := rfl`. -/
def derivCls (P : α → α → Prop) (A : Set α) : Set α := ltP P ʻʻ clEx (A ∩ fld P)

/-- The relation `δ_P` of `δ_P'α` to `α`. -/
def DerivRel (P : α → α → Prop) : Set α → Set α → Prop := graph (derivCls P)

/-- **✱216·02 Df.** \(\text{dense}ʻP=\hat{\alpha} (\alpha -\overrightarrow{\text{min}}_{p}ʻ\alpha \subset \delta _{p}ʻ\alpha ) \quad\text{Df}\)

The classes dense in `P`: all members except the minimum belong to the derivative
(`min⃗_P'α` is `refs (minP P) A`). Target:
`pm216_02 : dense P = {A | A \ refs (minP P) A ⊆ derivCls P A} := rfl`. -/
def dense (P : α → α → Prop) : Set (Set α) := {A | A \ refs (minP P) A ⊆ derivCls P A}

/-- The relation `dense` of `dense'P` to `P`. -/
def DenseRel : Set (Set α) → (α → α → Prop) → Prop := graph dense

/-- **✱216·03 Df.** \(\text{closed}ʻP=\hat{\alpha} \{\text{Cl ex}ʻ(\alpha \cap CʻP)\subset \text{ᗡ}ʻ\text{limax}_{p}.\delta _{p}ʻ\alpha \subset \alpha\} \quad\text{Df}\)

The classes closed in `P`: every existent sub-class of `α ∩ C'P` has a limit or maximum, and the
derivative is contained in `α`. Target:
`pm216_03 : closed P = {A | clEx (A ∩ fld P) ⊆ codom (limaxP P) ∧ derivCls P A ⊆ A} := rfl`. -/
def closed (P : α → α → Prop) : Set (Set α) :=
  {A | clEx (A ∩ fld P) ⊆ codom (limaxP P) ∧ derivCls P A ⊆ A}

/-- The relation `closed` of `closed'P` to `P`. -/
def ClosedRel : Set (Set α) → (α → α → Prop) → Prop := graph closed

/-- **✱216·04 Df.** \(\text{perf}ʻP=\text{dense}ʻP\cap \text{closed}ʻP \quad\text{Df}\)

The perfect classes. Target: `pm216_04 : perf P = dense P ∩ closed P := rfl`. -/
def perf (P : α → α → Prop) : Set (Set α) := dense P ∩ closed P

/-- The relation `perf` of `perf'P` to `P`. -/
def PerfRel : Set (Set α) → (α → α → Prop) → Prop := graph perf

/-- **✱216·05 Df.** \(\nablaʻP=P\unicode{x0294f}\text{D}ʻ\text{lt}_{p} \quad\text{Df}\)

The derivative `∇'P` of the series `P`: the series of its limit-points (named `nabla`). Value
function of `Nabla`. Target: `pm216_05 : nabla P = P ⥏ dom (ltP P) := rfl`. -/
def nabla (P : α → α → Prop) : α → α → Prop := P ⥏ dom (ltP P)

/-- The relation `∇` of `∇'P` to `P`. -/
def Nabla : (α → α → Prop) → (α → α → Prop) → Prop := graph nabla

/-! ## Section C: convergence, and the limits of functions (✱230–✱234)

`P : α → α → Prop` is the value-series, `Q : β → β → Prop` the argument-series, and
`R : α → β → Prop` the function (the relation of the value to the argument). -/

/-- **✱230·01 Df.** \(R\overline{Q} _{\text{cn}}\alpha =CʻQ\cap \text{ᗡ}ʻR\cap \hat{y} (Rʻʻ\overleftarrow{Q}_{*}ʻy\subset \alpha ) \quad\text{Df}\)

`R Q̄_cn α`: the arguments `y` (in `C'Q ∩ ᗡ'R`) from which on all values of `R` are in `α`
(`Q⃖_*'y` is `rels (anc Q) y`, `y` and its `Q`-successors). The product of three brackets to the
left (✱22·53). Target:
`pm230_01 : cnBar R Q A = fld Q ∩ codom R ∩ {y | R ʻʻ rels (anc Q) y ⊆ A} := rfl`. -/
def cnBar (R : α → β → Prop) (Q : β → β → Prop) (A : Set α) : Set β :=
  fld Q ∩ codom R ∩ {y | R ʻʻ rels (anc Q) y ⊆ A}

/-- **✱230·02 Df.** \(Q_{\text{cn}}=\hat{R} \hat{\alpha} (\exists !R\overline{Q} _{\text{cn}}\alpha ) \quad\text{Df}\)

`R Q_cn α`: `R` is `Q`-convergent into `α` (`∃!` is PM's "exists", `Set.Nonempty`).
`Q⃖_cn'R` is `rels (cn Q) R`. Target:
`pm230_02 : cn Q = fun R A => (cnBar R Q A).Nonempty := rfl`, with `R : α → β → Prop`. -/
def cn (Q : β → β → Prop) : (α → β → Prop) → Set α → Prop := fun R A => (cnBar R Q A).Nonempty

/-- **✱231·01 Df.** \(P\overline{R} _{\text{sc}}Q=pʻP_{*}ʻʻʻ\overleftarrow{Q}_{\text{cn}}ʻR\cap CʻP \quad\text{Df}\)

The limiting section `P R̄_sc Q`: `p'(P_*'''Q⃖_cn'R) ∩ C'P` (the other bracketing is not
significant), where `P_*'''κ` is `anc P ʻʻʻ K` (the classes `P_*''α`, `α ∈ κ`). `mem_scBar`
unfolds it. Target:
`pm231_01 : scBar P R Q = prodCls (anc P ʻʻʻ rels (cn Q) R) ∩ fld P := rfl`. -/
def scBar (P : α → α → Prop) (R : α → β → Prop) (Q : β → β → Prop) : Set α :=
  prodCls (anc P ʻʻʻ rels (cn Q) R) ∩ fld P

/-- **✱231·02 Df.** \(P\overline{R} _{\text{os}}Q=P\overline{R} _{\text{sc}}Q\cap \breve{P} \overline{R} _{\text{sc}}Q \quad\text{Df}\)

The ultimate oscillation `P R̄_os Q`. Target:
`pm231_02 : osBar P R Q = scBar P R Q ∩ scBar P˘ R Q := rfl`. -/
def osBar (P : α → α → Prop) (R : α → β → Prop) (Q : β → β → Prop) : Set α :=
  scBar P R Q ∩ scBar P˘ R Q

/-- **✱232·01 Df.** \((P\overline{R}Q)_{\text{sc}}ʻ\alpha = P\overline{R}_{\text{sc}}(Q_{*} \unicode{x0294f} \alpha ) \quad\text{Df}\)

The limiting section as the argument increases in `α`, `(P R̄ Q)_sc'α`, a descriptive function of
`α` (value function `scFun P R Q`, relation `scRel P R Q`, used as a relation in ✱233·01). Target:
`pm232_01 : scFun P R Q A = scBar P R (anc Q ⥏ A) := rfl`. -/
def scFun (P : α → α → Prop) (R : α → β → Prop) (Q : β → β → Prop) (A : Set β) : Set α :=
  scBar P R (anc Q ⥏ A)

/-- The relation `(P R̄ Q)_sc` of `(P R̄ Q)_sc'α` to `α`. -/
def scRel (P : α → α → Prop) (R : α → β → Prop) (Q : β → β → Prop) : Set α → Set β → Prop :=
  graph (scFun P R Q)

/-- **✱232·02 Df.** \((P\overline{R}Q)_{\text{os}}ʻ\alpha = P\overline{R}_{\text{os}}(Q_{*} \unicode{x0294f} \alpha ) \quad\text{Df}\)

The ultimate oscillation as the argument increases in `α`. Target:
`pm232_02 : osFun P R Q A = osBar P R (anc Q ⥏ A) := rfl`. -/
def osFun (P : α → α → Prop) (R : α → β → Prop) (Q : β → β → Prop) (A : Set β) : Set α :=
  osBar P R (anc Q ⥏ A)

/-- The relation `(P R̄ Q)_os` of `(P R̄ Q)_os'α` to `α`. -/
def osRel (P : α → α → Prop) (R : α → β → Prop) (Q : β → β → Prop) : Set α → Set β → Prop :=
  graph (osFun P R Q)

/-- **✱233·01 Df.** \((P\overline{R} Q)_{\text{lmx}}=\text{limax}_P\mid (P\overline{R} Q)_{\text{sc}} \quad\text{Df}\)

`y (P R̄ Q)_lmx α` iff `y` is a limit or maximum of `(P R̄ Q)_sc'α` (✱233·1). Many-valued in
general: `(P R̄ Q)_lmx'α` is `Desc (lmx P R Q) A ψ`. Target:
`pm233_01 : lmx P R Q = limaxP P ⨾ scRel P R Q := rfl`. -/
def lmx (P : α → α → Prop) (R : α → β → Prop) (Q : β → β → Prop) : α → Set β → Prop :=
  limaxP P ⨾ scRel P R Q

/-- **✱233·02 Df.** \(R(PQ)=(P\overline{R} Q)_{\text{lmx}}\mid \overrightarrow{Q} \quad\text{Df}\)

`R(PQ)`, the relation of the upper limit (or maximum) of the ultimate values as the argument
approaches `a` from below to `a` (named `rlim R P Q`); `R(PQ)'a` is `Desc (rlim R P Q) a ψ`
(`= limax_P'(P R̄ Q)_sc'Q⃗'a`, Summary of ✱233; `Q⃗` is `Rfwd Q`). Target:
`pm233_02 : rlim R P Q = lmx P R Q ⨾ Rfwd Q := rfl`. -/
def rlim (R : α → β → Prop) (P : α → α → Prop) (Q : β → β → Prop) : α → β → Prop :=
  lmx P R Q ⨾ Rfwd Q

/-- **✱234·01 Df.** \(\text{sc}(P,Q)ʻR=CʻP\cap \hat{x} (\overrightarrow{P}_{\text{po}}ʻʻ\overleftarrow{P}_{\text{po}}ʻx\subset \overleftarrow{Q}_{\text{cn}}ʻR) \quad\text{Df}\)

`sc(P,Q)'R`: the members `x` of `C'P` such that, for every later `w`, `R` is `Q`-convergent into
`P⃗_po'w` (the predecessors of `w`). `P⃗_po''P⃖_po'x` is `Rfwd (po P) ʻʻ rels (po P) x`.
Value function of the relation `sc(P,Q)` (`ScPQ P Q`). Target:
`pm234_01 : scPQ P Q R = fld P ∩ {x | Rfwd (po P) ʻʻ rels (po P) x ⊆ rels (cn Q) R} := rfl`. -/
def scPQ (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop) : Set α :=
  fld P ∩ {x | Rfwd (po P) ʻʻ rels (po P) x ⊆ rels (cn Q) R}

/-- The relation `sc(P,Q)` of `sc(P,Q)'R` to `R`. -/
def ScPQ (P : α → α → Prop) (Q : β → β → Prop) : Set α → (α → β → Prop) → Prop :=
  graph (scPQ P Q)

/-- **✱234·02 Df.** \(\text{os}(P,Q)ʻR=\text{sc}(P,Q)ʻR\cap \text{sc}(\breve{P},Q)ʻR \quad\text{Df}\)

Target: `pm234_02 : osPQ P Q R = scPQ P Q R ∩ scPQ P˘ Q R := rfl`. -/
def osPQ (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop) : Set α :=
  scPQ P Q R ∩ scPQ P˘ Q R

/-- The relation `os(P,Q)` of `os(P,Q)'R` to `R`. -/
def OsPQ (P : α → α → Prop) (Q : β → β → Prop) : Set α → (α → β → Prop) → Prop :=
  graph (osPQ P Q)

/-- `P_1` (✱121·02 with `ν = 1`), the relation of `x` to `y` when `P(x⊢⊣y)` has two members
("immediately preceding", Summary of Section A). The type of the `1` is free in PM; it is taken in
the type of the field of `P` (encoding decision 3; `Pnu_one_eq_P1`, `P1_iff`). Not a Df of Part V. -/
def P1 (P : α → α → Prop) : α → α → Prop := Pnu P (one : Set (Set α))

/-- **✱234·03 Df.** \(\text{ct}(PQ)ʻR=\hat{a} \{Rʻa\in \text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}_{\text{po}}ʻa)ʻR-CʻP_{1}\} \quad\text{Df}\)

The arguments `a` at which `R` is continuous from below: the value `R'a` (a description, scope
the proposition in braces) is in the ultimate oscillation as the argument approaches `a` from
below, and has no immediate predecessor or successor in `P` (`C'P_1` is `fld (P1 P)`;
`Q⃗_po'a` is `refs (po Q) a`; `os(…)'R − C'P_1` is the class difference). Value function of the
relation `ct(PQ)` (`Ct P Q`). (The Summary of ✱234 writes `Q⃗'a` for `Q⃗_po'a` once, in its
informal derivation; the Df and ✱234·5 have `Q⃗_po'a`.) Target:
`pm234_03 : ct P Q R = {a | Desc R a (fun v => v ∈ osPQ P (anc Q ⥏ refs (po Q) a) R \ fld (P1 P))}
:= rfl`. -/
def ct (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop) : Set β :=
  {a | Desc R a (fun v => v ∈ osPQ P (anc Q ⥏ refs (po Q) a) R \ fld (P1 P))}

/-- The relation `ct(PQ)` of `ct(PQ)'R` to `R`. -/
def Ct (P : α → α → Prop) (Q : β → β → Prop) : Set β → (α → β → Prop) → Prop := graph (ct P Q)

/-- **✱234·04 Df.** \(\text{contin}(PQ)ʻR=\text{ct}(PQ)ʻR\cap \text{ct}(P\breve{Q})ʻR \quad\text{Df}\)

The points of continuity of `R` (from below and from above). Target:
`pm234_04 : contin P Q R = ct P Q R ∩ ct P Q˘ R := rfl`. -/
def contin (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop) : Set β :=
  ct P Q R ∩ ct P Q˘ R

/-- The relation `contin(PQ)` of `contin(PQ)'R` to `R`. -/
def Contin (P : α → α → Prop) (Q : β → β → Prop) : Set β → (α → β → Prop) → Prop :=
  graph (contin P Q)

/-- **✱234·05 Df.** \(P\overline{\text{contin}} Q=\hat{R} \{\exists !CʻQ\cap \text{ᗡ}ʻR.CʻQ\cap \text{ᗡ}ʻR\subset \text{contin}(PQ)ʻR\} \quad\text{Df}\)

The functions continuous with respect to `P` and `Q`: having arguments in `C'Q` and continuous
at all of them. Target:
`pm234_05 : continBar P Q = {R | (fld Q ∩ codom R).Nonempty ∧ fld Q ∩ codom R ⊆ contin P Q R}
:= rfl`. -/
def continBar (P : α → α → Prop) (Q : β → β → Prop) : Set (α → β → Prop) :=
  {R | (fld Q ∩ codom R).Nonempty ∧ fld Q ∩ codom R ⊆ contin P Q R}

/-! ## Sanity lemmas: the encodings behave -/

section Sanity

/-- `C'P̆ = C'P` (✱33·22). -/
theorem fld_cnv (P : α → α → Prop) : fld P˘ = fld P := by
  ext z
  exact ⟨fun ⟨w, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, h.symm⟩⟩

theorem mem_img {R : α → β → Prop} {B : Set β} {x : α} : x ∈ R ʻʻ B ↔ ∃ y, y ∈ B ∧ R x y :=
  Iff.rfl

/-- `P ∈ trans . ≡ : xPy . yPz . ⊃_{x,y,z} . xPz`. -/
theorem mem_transR {P : α → α → Prop} :
    P ∈ transR ↔ ∀ x y z, P x y ∧ P y z → P x z := by
  constructor
  · intro h x y z ⟨hxy, hyz⟩
    exact h x z ⟨y, hxy, hyz⟩
  · rintro h x z ⟨y, hxy, hyz⟩
    exact h x y z ⟨hxy, hyz⟩

/-- `P ∈ Rl'J . ≡ . P ⊂̇ J`, i.e. `P` is irreflexive. -/
theorem mem_rl_J {P : α → α → Prop} : P ∈ rl J ↔ ∀ x, ¬P x x := by
  constructor
  · intro h x hx
    exact h x x hx rfl
  · intro h x y hxy hxy'
    exact h x (hxy' ▸ hxy)

/-- `y ∈ P⃡'x . ≡ : yPx . ∨ . y = x . y ∈ C'P : ∨ . xPy` (✱97·1). -/
theorem mem_refsRels {P : α → α → Prop} {x y : α} :
    y ∈ refsRels P x ↔ (P y x ∨ (y = x ∧ y ∈ fld P)) ∨ P x y := Iff.rfl

/-- The form ✱202·103 of connexity: `x, y ∈ C'P . ⊃_{x,y} : xPy . ∨ . x = y . ∨ . yPx`. -/
theorem mem_connex {P : α → α → Prop} :
    P ∈ connex ↔ ∀ x y, x ∈ fld P ∧ y ∈ fld P → (P x y ∨ x = y) ∨ P y x := by
  constructor
  · intro h x y ⟨hx, hy⟩
    have : y ∈ refsRels P x := by rw [h x hx]; exact hy
    rcases this with (h1 | ⟨rfl, -⟩) | h2
    · exact Or.inr h1
    · exact Or.inl (Or.inr rfl)
    · exact Or.inl (Or.inl h2)
  · intro h x hx
    ext y
    constructor
    · rintro ((h1 | ⟨rfl, -⟩) | h2)
      · exact ⟨x, Or.inl h1⟩
      · exact hx
      · exact ⟨x, Or.inr h2⟩
    · intro hy
      rcases h x y ⟨hx, hy⟩ with (h1 | rfl) | h2
      · exact Or.inr h1
      · exact Or.inl (Or.inr ⟨rfl, hx⟩)
      · exact Or.inl (Or.inl h2)

/-- `P ∈ Ser` unfolded: irreflexive, transitive, connected. -/
theorem mem_Ser {P : α → α → Prop} :
    P ∈ Ser ↔ ((∀ x, ¬P x x) ∧ ∀ x y z, P x y ∧ P y z → P x z) ∧
      ∀ x y, x ∈ fld P ∧ y ∈ fld P → (P x y ∨ x = y) ∨ P y x := by
  show (P ∈ rl J ∧ P ∈ transR) ∧ P ∈ connex ↔ _
  rw [mem_rl_J, mem_transR, mem_connex]

/-- For transitive `P`, `P_po = P` (✱201·18). -/
theorem po_eq_of_transR {P : α → α → Prop} (h : P ∈ transR) : po P = P := by
  have : IsTrans α P := ⟨fun x y z hxy hyz => mem_transR.1 h x y z ⟨hxy, hyz⟩⟩
  funext x y
  apply propext
  rw [po_iff_transGen, Relation.transGen_eq_self]

/-- For transitive `P`, `xP_*y . ≡ : x = y . x ∈ C'P . ∨ . xPy` (✱201·18: `P_* = P ∪̇ I ↾ C'P`). -/
theorem anc_iff_of_transR {P : α → α → Prop} (h : P ∈ transR) {x y : α} :
    anc P x y ↔ (x = y ∧ x ∈ fld P) ∨ P x y := by
  rw [anc_iff_po, po_eq_of_transR h]

/-- `z ∈ p'P⃖''α . ≡ . (y) . y ∈ α ⊃ yPz` (`z` follows every member of `α`). -/
theorem mem_prodCls_Rbwd {P : α → α → Prop} {A : Set α} {z : α} :
    z ∈ prodCls (Rbwd P ʻʻ A) ↔ ∀ y, y ∈ A → P y z := by
  constructor
  · intro h y hy
    exact h _ ⟨y, hy, rfl⟩
  · rintro h K ⟨y, hy, rfl⟩
    exact h y hy

/-- `z ∈ p'P⃗''α . ≡ . (y) . y ∈ α ⊃ zPy` (`z` precedes every member of `α`). -/
theorem mem_prodCls_Rfwd {P : α → α → Prop} {A : Set α} {z : α} :
    z ∈ prodCls (Rfwd P ʻʻ A) ↔ ∀ y, y ∈ A → P z y := by
  constructor
  · intro h y hy
    exact h _ ⟨y, hy, rfl⟩
  · rintro h K ⟨y, hy, rfl⟩
    exact h y hy

/-- `x min_P α . ≡ : x ∈ α ∩ C'P : y ∈ α . ⊃_y . ∼(yPx)` (cf. ✱205·14). -/
theorem minP_iff {P : α → α → Prop} {x : α} {A : Set α} :
    minP P x A ↔ (x ∈ A ∧ x ∈ fld P) ∧ ∀ y, y ∈ A → ¬P y x := by
  constructor
  · rintro ⟨hx, hn⟩
    exact ⟨hx, fun y hy hyx => hn ⟨y, hy, hyx⟩⟩
  · rintro ⟨hx, hn⟩
    exact ⟨hx, fun ⟨y, hy, hyx⟩ => hn y hy hyx⟩

/-- `x max_P α . ≡ : x ∈ α ∩ C'P : y ∈ α . ⊃_y . ∼(xPy)`. -/
theorem maxP_iff {P : α → α → Prop} {x : α} {A : Set α} :
    maxP P x A ↔ (x ∈ A ∧ x ∈ fld P) ∧ ∀ y, y ∈ A → ¬P x y := by
  show minP P˘ x A ↔ _
  rw [minP_iff, fld_cnv]
  rfl

/-- `x seq_P α` unfolded: `x ∈ C'P` follows every member of `α ∩ C'P`, and no term that follows
every member of `α ∩ C'P` precedes `x`. -/
theorem seqP_iff {P : α → α → Prop} {x : α} {A : Set α} :
    seqP P x A ↔ ((∀ y, y ∈ A ∩ fld P → P y x) ∧ x ∈ fld P) ∧
      ∀ z, (∀ y, y ∈ A ∩ fld P → P y z) → ¬P z x := by
  show minP P x _ ↔ _
  rw [minP_iff, mem_prodCls_Rbwd]
  exact and_congr Iff.rfl (forall_congr' fun z => imp_congr mem_prodCls_Rbwd Iff.rfl)

/-- `x prec_P α` unfolded. -/
theorem precP_iff {P : α → α → Prop} {x : α} {A : Set α} :
    precP P x A ↔ ((∀ y, y ∈ A ∩ fld P → P x y) ∧ x ∈ fld P) ∧
      ∀ z, (∀ y, y ∈ A ∩ fld P → P z y) → ¬P x z := by
  show maxP P x _ ↔ _
  rw [maxP_iff, mem_prodCls_Rfwd]
  exact and_congr Iff.rfl (forall_congr' fun z => imp_congr mem_prodCls_Rfwd Iff.rfl)

/-- `prec_P = seq(P̆)` (✱206·101). -/
theorem precP_eq_seqP_cnv (P : α → α → Prop) : precP P = seqP P˘ := by
  funext x A
  show maxP P x (prodCls (Rfwd P ʻʻ (A ∩ fld P))) = minP P˘ x (prodCls (Rbwd P˘ ʻʻ (A ∩ fld P˘)))
  rw [fld_cnv]
  rfl

/-- `x lt_P α . ≡ . x seq_P α . ∼E!!…`: a sequent of a class without a maximum (✱207·1). -/
theorem ltP_iff {P : α → α → Prop} {x : α} {A : Set α} :
    ltP P x A ↔ seqP P x A ∧ ¬∃ y, maxP P y A := Iff.rfl

theorem limaxP_iff {P : α → α → Prop} {x : α} {A : Set α} :
    limaxP P x A ↔ maxP P x A ∨ ltP P x A := Iff.rfl

theorem liminP_iff {P : α → α → Prop} {x : α} {A : Set α} :
    liminP P x A ↔ minP P x A ∨ tlP P x A := Iff.rfl

/-- `tl_P = lt(P̆)` (✱207·101). -/
theorem tlP_eq_ltP_cnv (P : α → α → Prop) : tlP P = ltP P˘ := by
  show precP P ↾ (codom (minP P))ᶜ = seqP P˘ ↾ (codom (minP P˘˘))ᶜ
  rw [precP_eq_seqP_cnv]
  rfl

/-- `limin_P = limax(P̆)` (✱207·401). -/
theorem liminP_eq_limaxP_cnv (P : α → α → Prop) : liminP P = limaxP P˘ := by
  show minP P ⊍ tlP P = minP P˘˘ ⊍ ltP P˘
  rw [tlP_eq_ltP_cnv]
  rfl

/-- `S ∈ cror'P . ≡ . S ∈ 1 → 1 . ᗡ'S = C'P . S;P ⊂̇ P` (✱208·1). -/
theorem mem_cror {P S : α → α → Prop} :
    S ∈ cror P ↔ (S ∈ arrow one one ∧ codom S = fld P) ∧ S ⁏ P ⪽ P := by
  constructor
  · rintro ⟨K, ⟨Q, hQ, rfl⟩, ⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2.symm⟩, h3 ▸ hQ⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨_, ⟨S ⁏ P, h3, rfl⟩, ⟨h1, h2.symm⟩, rfl⟩

theorem mem_sect {P : α → α → Prop} {A : Set α} :
    A ∈ sect P ↔ A ⊆ fld P ∧ ∀ x y, P x y ∧ y ∈ A → x ∈ A := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x y ⟨hxy, hy⟩ => h2 ⟨y, hy, hxy⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x ⟨y, hy, hxy⟩ => h2 x y ⟨hxy, hy⟩⟩

theorem mem_str {P : α → α → Prop} {A : Set α} :
    A ∈ str P ↔ A ⊆ fld P ∧ ∀ x, (∃ y, y ∈ A ∧ P x y) ∧ (∃ z, z ∈ A ∧ P z x) → x ∈ A := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x hx => h2 hx⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x hx => h2 x hx⟩

/-- The segments: `α ∈ D'P_∈ . ≡ . (∃β) . α = P''β`. -/
theorem mem_dom_imgRel {P : α → α → Prop} {A : Set α} :
    A ∈ dom (imgRel P) ↔ ∃ B, A = P ʻʻ B := Iff.rfl

/-- The segments without maximum: `α ∈ D'(P_∈ ∩̇ I) . ≡ . α = P''α` (cf. ✱211·12). -/
theorem mem_dom_imgRel_rcap_I {P : α → α → Prop} {A : Set α} :
    A ∈ dom (imgRel P ⩀ I) ↔ A = P ʻʻ A := by
  constructor
  · rintro ⟨B, h, rfl⟩
    exact h
  · intro h
    exact ⟨A, h, rfl⟩

/-- The segments of `P_*` are the sections of `P`: `α ∈ D'(P_*)_∈ . ≡ . α ∈ sect'P` (cf. ✱211·13).
With it, `ς'P_*` and `P_ς` (✱212·12, ✱213·1) are stated in terms of `sect'P`. -/
theorem mem_dom_imgRel_anc {P : α → α → Prop} {A : Set α} :
    A ∈ dom (imgRel (anc P)) ↔ A ∈ sect P := by
  constructor
  · rintro ⟨C, rfl⟩
    refine ⟨fun x ⟨c, _, hxc⟩ => hxc.1, ?_⟩
    rintro x ⟨y, ⟨c, hc, hyc⟩, hxy⟩
    refine ⟨c, hc, ?_⟩
    rw [anc_iff_reflTransGen] at hyc ⊢
    exact ⟨⟨y, Or.inl hxy⟩, Relation.ReflTransGen.head hxy hyc.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨A, Set.ext fun x => ⟨fun hx => ⟨x, hx, anc_iff_po.2 (Or.inl ⟨rfl, h1 hx⟩)⟩, ?_⟩⟩
    rintro ⟨a, ha, hxa⟩
    obtain ⟨-, hr⟩ := anc_iff_reflTransGen.1 hxa
    clear hxa
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => exact ha
    | head hxy _ ih => exact h2 ⟨_, ih, hxy⟩

/-- `α (ς'P) β . ≡ . α, β ∈ D'P_∈ . α P_lc β`. -/
theorem segSer_apply {P : α → α → Prop} {A B : Set α} :
    segSer P A B ↔ (A ∈ dom (imgRel P) ∧ Plc P A B) ∧ B ∈ dom (imgRel P) := Iff.rfl

/-- `Q P_ς R . ≡ . (∃α, β) . Q = P ⥏ α . R = P ⥏ β . α {(ς'P_*) ⥏ (−ι'Λ)} β`. -/
theorem Psec_apply {P Q R : α → α → Prop} :
    Psec P Q R ↔ ∃ A B, (Q = P ⥏ A ∧ R = P ⥏ B) ∧ (segSer (anc P) ⥏ (ι Λ)ᶜ) A B :=
  semi_graph_apply _ _ _ _

theorem mem_Ded {P : α → α → Prop} :
    P ∈ Ded ↔ ∀ A : Set α, (∃ x, maxP P x A) ∨ ∃ x, seqP P x A := Iff.rfl

theorem mem_derivCls {P : α → α → Prop} {A : Set α} {x : α} :
    x ∈ derivCls P A ↔ ∃ B, (B ⊆ A ∩ fld P ∧ B.Nonempty) ∧ ltP P x B := Iff.rfl

/-- `y ∈ R Q̄_cn α . ≡ . y ∈ C'Q ∩ ᗡ'R . R''Q⃖_*'y ⊂ α` (✱230·1), unfolded. -/
theorem mem_cnBar {R : α → β → Prop} {Q : β → β → Prop} {A : Set α} {y : β} :
    y ∈ cnBar R Q A ↔ (y ∈ fld Q ∧ y ∈ codom R) ∧ ∀ x z, anc Q y z ∧ R x z → x ∈ A := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x z ⟨hyz, hxz⟩ => h2 ⟨z, hyz, hxz⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x ⟨z, hyz, hxz⟩ => h2 x z ⟨hyz, hxz⟩⟩

/-- `R Q_cn α . ≡ . (∃y) . y ∈ R Q̄_cn α` (✱230·11). -/
theorem cn_iff {R : α → β → Prop} {Q : β → β → Prop} {A : Set α} :
    cn Q R A ↔ ∃ y, y ∈ cnBar R Q A := Iff.rfl

/-- `x ∈ P R̄_sc Q . ≡ : R Q_cn α . ⊃_α . x ∈ P_*''α : x ∈ C'P`. -/
theorem mem_scBar {P : α → α → Prop} {R : α → β → Prop} {Q : β → β → Prop} {x : α} :
    x ∈ scBar P R Q ↔ (∀ A, cn Q R A → x ∈ anc P ʻʻ A) ∧ x ∈ fld P := by
  refine and_congr ⟨fun h A hA => h _ ⟨A, hA, rfl⟩, ?_⟩ Iff.rfl
  rintro h B ⟨A, hA, rfl⟩
  exact h A hA

/-- `x ∈ sc(P,Q)'R . ≡ : x ∈ C'P : x P_po w . ⊃_w . R Q_cn (P⃗_po'w)` (✱234·1). -/
theorem mem_scPQ {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} {x : α} :
    x ∈ scPQ P Q R ↔ x ∈ fld P ∧ ∀ w, po P x w → cn Q R (refs (po P) w) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w hw => h2 ⟨w, hw, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun B ⟨w, hw, hB⟩ => hB ▸ h2 w hw⟩

/-! ### `P_1` -/

/-- `x P_ν y` with `ν = 1` in any type `β` where `1` exists: `P(x⊢⊣y)` has exactly two members. -/
theorem Pnu_one_iff {β : Type v} [Nonempty β] {P : α → α → Prop} {x y : α} :
    Pnu P (one : Set (Set β)) x y ↔ ∃ u v, u ≠ v ∧ itvCC P x y = {u, v} := by
  obtain ⟨b⟩ := ‹Nonempty β›
  show n₀c (itvCC P x y) = ((one : Set (Set β)) +ᶜ (one : Set (Set β)) : Set (Set α)) ↔ _
  rw [one_eq_n₀c_singleton b, n₀c_cardAdd_n₀c, n₀c_eq_nc,
    nc_eq_nc_iff ⟨_, self_mem_nc _⟩, sm_iff_nonempty_equiv]
  have hS : Nat.card ↥(({b} : Set β) +ₐ ({b} : Set β)) = 2 := by
    rw [Nat.card_congr (clsSumEquiv _ _), Nat.card_sum]
    simp
  have hSfin : Finite ↥(({b} : Set β) +ₐ ({b} : Set β)) :=
    Finite.of_equiv _ (clsSumEquiv _ _).symm
  constructor
  · rintro ⟨e⟩
    have : Finite ↥(itvCC P x y) := Finite.of_equiv _ e.symm
    rw [← Set.ncard_eq_two, ← Nat.card_coe_set_eq, Nat.card_congr e, hS]
  · intro h
    have h2 := Set.ncard_eq_two.2 h
    have hfin : (itvCC P x y).Finite := Set.finite_of_ncard_ne_zero (by omega)
    have := hfin.to_subtype
    exact Finite.card_eq.1 (by rw [Nat.card_coe_set_eq, h2, hS])

/-- `x P_1 y . ≡ . P(x⊢⊣y)` has two members. -/
theorem P1_iff {P : α → α → Prop} {x y : α} :
    P1 P x y ↔ ∃ u v, u ≠ v ∧ itvCC P x y = {u, v} := by
  have : Nonempty α := ⟨x⟩
  exact Pnu_one_iff

/-- `P_1` does not depend on the type of its `1`, provided `1` exists there. -/
theorem Pnu_one_eq_P1 {β : Type v} [Nonempty β] (P : α → α → Prop) :
    Pnu P (one : Set (Set β)) = P1 P := by
  funext x y
  exact propext (Pnu_one_iff.trans P1_iff.symm)

/-- For `P ∈ trans ∩ Rl'J`, `x P_1 y . ≡ . x (P −̇ P²) y` (✱201·63, pointwise): `y` immediately
follows `x`. -/
theorem P1_iff_of_transR {P : α → α → Prop} (ht : P ∈ transR) (hJ : P ∈ rl J) {x y : α} :
    P1 P x y ↔ P x y ∧ ¬∃ z, P x z ∧ P z y := by
  have tr := mem_transR.1 ht
  have irr := mem_rl_J.1 hJ
  have mem : ∀ z, z ∈ itvCC P x y ↔
      ((x = z ∧ x ∈ fld P) ∨ P x z) ∧ ((z = y ∧ z ∈ fld P) ∨ P z y) :=
    fun z => and_congr (anc_iff_of_transR ht) (anc_iff_of_transR ht)
  have between : ∀ z, z ∈ itvCC P x y → (z = x ∨ z = y) ∨ (P x z ∧ P z y) := by
    intro z hz
    rcases (mem z).1 hz with ⟨⟨rfl, -⟩ | h1, ⟨rfl, -⟩ | h2⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨h1, h2⟩
  rw [P1_iff]
  constructor
  · rintro ⟨u, v, huv, h⟩
    have hu : u ∈ itvCC P x y := h ▸ Or.inl rfl
    have hv : v ∈ itvCC P x y := h ▸ Or.inr rfl
    have hxy : P x y := by
      by_contra hn
      have key : ∀ z, z ∈ itvCC P x y → z = x := by
        intro z hz
        rcases (mem z).1 hz with ⟨⟨rfl, -⟩ | h1, ⟨rfl, -⟩ | h2⟩
        · rfl
        · rfl
        · exact absurd h1 hn
        · exact absurd (tr x z y ⟨h1, h2⟩) hn
      exact huv ((key u hu).trans (key v hv).symm)
    refine ⟨hxy, ?_⟩
    rintro ⟨z, hxz, hzy⟩
    have hx : x ∈ itvCC P x y := (mem x).2 ⟨Or.inl ⟨rfl, ⟨y, Or.inl hxy⟩⟩, Or.inr hxy⟩
    have hy : y ∈ itvCC P x y := (mem y).2 ⟨Or.inr hxy, Or.inl ⟨rfl, ⟨x, Or.inr hxy⟩⟩⟩
    have hz : z ∈ itvCC P x y := (mem z).2 ⟨Or.inr hxz, Or.inr hzy⟩
    have hxz' : x ≠ z := fun e => irr x (e ▸ hxz)
    have hzy' : z ≠ y := fun e => irr z (e ▸ hzy)
    have hxy' : x ≠ y := fun e => irr x (e ▸ hxy)
    rw [h] at hx hy hz
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
      simp_all
  · rintro ⟨hxy, hn⟩
    refine ⟨x, y, fun e => irr x (e ▸ hxy), Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
    · rcases between z hz with h | h
      · exact h
      · exact absurd ⟨z, h⟩ hn
    · rcases hz with rfl | rfl
      · exact (mem z).2 ⟨Or.inl ⟨rfl, ⟨y, Or.inl hxy⟩⟩, Or.inr hxy⟩
      · exact (mem z).2 ⟨Or.inr hxy, Or.inl ⟨rfl, ⟨x, Or.inr hxy⟩⟩⟩

/-! ### Descriptive functions of the new relations -/

theorem desc_Cror (P : α → α → Prop) (ψ : Set (α → α → Prop) → Prop) :
    Desc Cror P ψ ↔ ψ (cror P) := desc_graph _ _ _

theorem desc_Sect (P : α → α → Prop) (ψ : Set (Set α) → Prop) :
    Desc Sect P ψ ↔ ψ (sect P) := desc_graph _ _ _

theorem desc_SegSer (P : α → α → Prop) (ψ : (Set α → Set α → Prop) → Prop) :
    Desc SegSer P ψ ↔ ψ (segSer P) := desc_graph _ _ _

theorem desc_Sgm (P : α → α → Prop) (ψ : (Set α → Set α → Prop) → Prop) :
    Desc Sgm P ψ ↔ ψ (sgm P) := desc_graph _ _ _

theorem desc_Str (P : α → α → Prop) (ψ : Set (Set α) → Prop) :
    Desc Str P ψ ↔ ψ (str P) := desc_graph _ _ _

theorem desc_DerivRel (P : α → α → Prop) (A : Set α) (ψ : Set α → Prop) :
    Desc (DerivRel P) A ψ ↔ ψ (derivCls P A) := desc_graph _ _ _

theorem desc_DenseRel (P : α → α → Prop) (ψ : Set (Set α) → Prop) :
    Desc DenseRel P ψ ↔ ψ (dense P) := desc_graph _ _ _

theorem desc_ClosedRel (P : α → α → Prop) (ψ : Set (Set α) → Prop) :
    Desc ClosedRel P ψ ↔ ψ (closed P) := desc_graph _ _ _

theorem desc_PerfRel (P : α → α → Prop) (ψ : Set (Set α) → Prop) :
    Desc PerfRel P ψ ↔ ψ (perf P) := desc_graph _ _ _

theorem desc_Nabla (P : α → α → Prop) (ψ : (α → α → Prop) → Prop) :
    Desc Nabla P ψ ↔ ψ (nabla P) := desc_graph _ _ _

theorem desc_scRel (P : α → α → Prop) (R : α → β → Prop) (Q : β → β → Prop) (A : Set β)
    (ψ : Set α → Prop) : Desc (scRel P R Q) A ψ ↔ ψ (scFun P R Q A) := desc_graph _ _ _

theorem desc_osRel (P : α → α → Prop) (R : α → β → Prop) (Q : β → β → Prop) (A : Set β)
    (ψ : Set α → Prop) : Desc (osRel P R Q) A ψ ↔ ψ (osFun P R Q A) := desc_graph _ _ _

theorem desc_ScPQ (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop) (ψ : Set α → Prop) :
    Desc (ScPQ P Q) R ψ ↔ ψ (scPQ P Q R) := desc_graph _ _ _

theorem desc_OsPQ (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop) (ψ : Set α → Prop) :
    Desc (OsPQ P Q) R ψ ↔ ψ (osPQ P Q R) := desc_graph _ _ _

theorem desc_Ct (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop) (ψ : Set β → Prop) :
    Desc (Ct P Q) R ψ ↔ ψ (ct P Q R) := desc_graph _ _ _

theorem desc_Contin (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop)
    (ψ : Set β → Prop) : Desc (Contin P Q) R ψ ↔ ψ (contin P Q R) := desc_graph _ _ _

/-- `y (P R̄ Q)_lmx α . ≡ . y limax_P {(P R̄ Q)_sc'α}` (✱233·1). -/
theorem lmx_apply {P : α → α → Prop} {R : α → β → Prop} {Q : β → β → Prop} {y : α} {A : Set β} :
    lmx P R Q y A ↔ limaxP P y (scFun P R Q A) := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact hB
  · intro h
    exact ⟨_, h, rfl⟩

/-- `y R(PQ) a . ≡ . y limax_P {(P R̄ Q)_sc'Q⃗'a}` (Summary of ✱233). -/
theorem rlim_apply {R : α → β → Prop} {P : α → α → Prop} {Q : β → β → Prop} {y : α} {a : β} :
    rlim R P Q y a ↔ limaxP P y (scFun P R Q (refs Q a)) := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact lmx_apply.1 hB
  · intro h
    exact ⟨_, lmx_apply.2 h, rfl⟩

end Sanity

end PrincipiaMathematica
