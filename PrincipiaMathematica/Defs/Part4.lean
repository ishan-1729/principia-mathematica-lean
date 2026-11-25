import PrincipiaMathematica.Defs.Part3

/-!
# Part IV (Relation-arithmetic): the definitions

Every definition (Df, and the temporary definition Dft ✱177·2) of ✱150–✱186, in PM's order, in
the format of `Defs/Part1.lean`: each entry is headed `**✱N·M Df.**` with the formula as printed
(MathJax TeX, from `data/principia.json`), says how it is read in Lean and gives the *target
statement* of `pmN_M` (status `definition` unless said otherwise; every target below has been
checked to elaborate and to hold by the indicated proof). Then come the adequacy predicates for
relation-numbers (the conventions IT, IIT, AT "apply to relation-numbers as to cardinals",
Summary of Section A) and the sanity lemmas the Section files use: `S;Q` unfolded, likeness
(`smor`) is an equivalence and is "an isomorphism between the fields", `Nr'P` and `N₀r'P`, the
existence of `Nr(γ)'P`, and the unfolded forms of `P ⤉ Q`, `P ⇸ x`, `Σ'P`, `Q × P`, `C'(P + Q)`.

(✱177·2 `df'Q = Q_df Dft[✱177]` is printed in the e-text as a proposition; it is a Dft all the
same and is given here.)

## Encoding decisions (in addition to Basic §1–§10 and Defs/Part2, Part3)

1. *Homogeneity.* "The relations of which ordinal similarity is affirmed or denied must be
   homogeneous; the correlators, on the contrary, need not be" (Summary of Section A). So `smor`,
   `Nr'P`, `N₀r'P`, `P ⤉ Q`, `P ⇸ x`, `Σ'P`, `P_cl`, `Π'P`, … take `P : α → α → Prop`; a
   correlator is `S : α → β → Prop`; a relation of relations is
   `P : (α → α → Prop) → (α → α → Prop) → Prop`.
2. *Actual types* (as for cardinals, Defs/Part3 decisions 1–4). `Nr'P` is `nr γ P : Set (γ → γ →
   Prop)`, the relations on `γ` like `P` — **the type `γ` (of the field of the members) is an
   explicit argument**, PM's `Nr(X)'P` with `X : γ → γ → Prop` (✱65·04). The same for `ΣNr'P`
   (`sigmaNr γ P`) and `ΠNr'P` (`piNr γ P`). `NR = D'Nr` leaves the type of the converse domain
   ambiguous: `NR β` (`μ ∈ NR β ↔ ∃ P : β → β → Prop, μ = nr γ P`), and `μ, ν ∈ NR` does not
   identify the types of `μ` and `ν`. `N₀r'P` (`n₀r P`) is typically definite. The arithmetical
   formal numbers `μ +̇ ν`, `μ ×̇ ν`, `μ exp_r ν` (`μ ∔ ν`, `μ ⨰ ν`, `nrExp μ ν`) have their actual
   type implicit (fixed by the context or by an ascription `(μ ∔ ν : Set (γ → γ → Prop))`).
3. *`μ +̇ 1̇` and `1̇ +̇ μ`* (✱181·02·021): the definiens has an apparent variable `x` whose type
   nothing determines ("`x` and `P` may be of any relative types", Summary of ✱181), so that type
   is an explicit argument: `nrAddOne β μ`, `nrOneAdd β μ` (as `finid β P` in Defs/Part3). The
   value is the same for every nonempty `β` (✱181·3); a proposition about `μ +̇ 1̇` takes `β` as
   its own type parameter, with `[Nonempty β]` where it fails for an empty type (Basic §3).
   `1̇` has no meaning in isolation (PM): there is no Lean term for it.
4. *Normal adjustment* (✱180·03·031, ✱181·03·031, ✱184·02·03, ✱186·02·03): an argument `Nr'P` of
   `+̇`, `×̇`, `exp_r`, `+̇ 1̇`, `1̇ +̇` is written `n₀r P`. IIT: any other formal number in an
   arithmetical position gets its own type parameter `W` and the adequacy hypothesis
   `AdeqNr W P`, `AdeqNrAdd W μ ν`, `AdeqNrMul W μ ν`, `AdeqNrExp W μ ν`, `AdeqSigmaNr W P`,
   `AdeqPiNr W P`, `AdeqNrAddOne W β μ`, `AdeqNrOneAdd W β μ` (below; e.g. the `ν +̇ 1̇` of
   ✱181·54), exactly as in Defs/Part3 decision 6; AT likewise (decision 7), e.g.
   ✱155·16 "requires that the equation `Nr'P = Nr'Q` on the right-hand side should be subject to
   the convention AT" (Summary of ✱155).
5. *Descriptive functions* (Basic §5). Every relation of this Part whose descriptive function
   always exists is `graph` of its value function, and in formulas its value is written directly:
   `Nr'P` is `nr γ P`, `N₀r'P` is `n₀r P`, `Σ'P` is `relSigma P`, `Π'P` is `relPi P`, `Prod'P` is
   `prodR P`, `S†'Q` is `daggerOp S Q`, `(P↓.,)'y` is `opSemi couple P y`, `df'Q` is `Pdf Q`,
   `ΣNr'P` is `sigmaNr γ P`, `ΠNr'P` is `piNr γ P`, `ṡ'λ` is `sumRel L`. Rewrite descriptions with
   the `desc_…` lemmas at the end of this file. The descriptions `M'Q` of a selection `M` in
   ✱172·01 may fail to exist and are kept as `Desc`. A Df `X = D'Y` / `X = Cnv'Y` (✱152·02,
   ✱154·01, ✱155·02, ✱170·02, ✱171·02) keeps the description in its target.
6. *The semicolon.* `S;Q` (✱150·01) is `S ⁏ Q` (U+204F, Lean's `;` is reserved), right
   associative (✱150·05), at precedence 66: looser than `◁`, `⨾`, `×ᵣ`, `↾`, `⥏`, `⩀`, tighter than
   `⊍`, `⤉`, `⇸`, `⇷`, `+ᵣ`. So `S ⁏ α ◁ Q ↾ β` is PM's `S;α↿Q↾β = S;(α↿Q↾β)` (✱150·34, the
   only unbracketed mixture with `↿`, `↾`), and `S ⁏ P ⤉ S ⁏ Q`, `S ⁏ Q ⇸ S'x`, `S ⁏ Q ⊍ T ⁏ Q`
   are `(S;P) ⤉ (S;Q)` (✱160·44), `(S;Q) ⇸ S'x` (✱161·4), `(S;Q) ∪̇ (T;Q)` (✱150·74), as PM
   reads them. Elsewhere PM brackets the mixtures (`(R | S);Q` ✱150·13, `(S ↾ C'Q);Q` ✱150·32,
   `(S;Q) ⥏ α` ✱150·361, `S;(Q ∩̇ R)` ✱150·301): write the same brackets. `R'S;Q` is `R'(S;Q)`
   (✱150·04).
   Any relation can stand before `;`: `ι;P` is `iota ⁏ P`, `C;Q` is `C ⁏ Q`, `D;Π'P` is
   `D ⁏ relPi P`, `F;P` is `F ⁏ P`, `↓x;P` is `coupleR x ⁏ P`, `x↓;P` is `coupleL x ⁏ P`,
   `S†;Q` is `daggerRel S ⁏ Q`, `Σ;P` is `RelSigma ⁏ P`, `Π;P` is `RelPi ⁏ P`, `Prod;P` is
   `ProdR ⁏ P`, `df;P` is `dfRel ⁏ P`, `ṡ;R` is `sDotRel ⁏ R`, `×P;Q` is `opR rtimes P ⁏ Q`,
   `(ι'x ∪);P` is `opL (· ∪ ·) (ι x) ⁏ P`. In general a relation `x♀` is `opL f x` and `♀y` is
   `opR f y` (✱38): `(P exp);S` is `opL rexp P ⁏ S` (✱176·43), `P⤉;Q` is `opL rsum P ⁏ Q`
   (✱213·53), `†(Q↓P);Π'(P↓Q)` is `opR daggerOp (Q ↓ P) ⁏ relPi (P ↓ Q)` (✱172·21),
   `(C'P −);R` is `opL (· \ ·) (fld P) ⁏ R` (✱217·4).
7. *`S†`.* ✱150·02 defines the *term* `S†Q` (`daggerOp S Q`, with the same definiens as `S;Q`);
   the *relation* `S†` is then given by ✱38·01, `S† = ûQ̂(u = S†Q)`: `daggerRel S :=
   opL daggerOp S`. ✱150·141 `S† = S ‖ S̆` is a theorem (`daggerRel_eq_dpar`), not a definition.
   (Defs/Part3's `dagger R := R ∥ R˘` is the temporary Dft ✱116·529, for ✱116 only; in Part IV
   write `daggerRel`.)
8. *`P ↓., y` and `↓̆.,`.* `Q♀.,y` (✱150·03) is `opSemi f Q y` for the double function
   `f : α → β → γ` (`♀`); the relation `Q♀.,` (of `Q♀.,y` to `y`, ✱38·01) is `opL (opSemi f) Q`;
   for `♀ = ↓`, `P↓.,` is `coupleSemi P` and `P↓.,;Q` is `coupleSemi P ⁏ Q`. `♀̆` (✱182·01) is
   `opDiag f` (the relation of `x♀x` to `x`); `↓̆.,` is `opDiag (opSemi couple)` and the
   *separated relation* `↓̆.,;P` (✱182) is `sepRel P`.
9. *Order of factors.* `Q × P` (✱166·01) is `Q ×ᵣ P` (`rtimes Q P`): the couples `x ↓ z` with
   `x ∈ C'P`, `z ∈ C'Q`, ordered first by `Q` (on `z`), then by `P` (on `x`) (✱166·11, proved
   below as `rtimes_apply`); `C'(P × Q) = C'P × C'Q` with Defs/Part3's `B ×ₐ A`.
10. *Names that shadow.* Do not bind variables named `F`, `C`, `D`, `I`, `J`, `Nr`, `NR`, `one_s`,
   … . `Σ`, `Π` are not identifiers: `Σ'P` is `relSigma P`, `Π'P` is `relPi P`.

## Symbol table: PM → Lean (extends Basic §7 and Defs/Part2, Part3)

| PM | Df | Lean |
|----|----|------|
| `S;Q` | ✱150·01·05 | `S ⁏ Q` (`semi S Q`) |
| `S†Q`, `S†` (relation), `S†'Q` | ✱150·02, ✱38·01 | `daggerOp S Q`, `daggerRel S` |
| `Q♀.,y`, `Q♀.,` (relation) | ✱150·03 | `opSemi f Q y`, `opL (opSemi f) Q` |
| `P↓.,y`, `P↓.,`, `P↓.,;Q` | ✱150·03 | `opSemi couple P y`, `coupleSemi P`, `coupleSemi P ⁏ Q` |
| `R'S;Q` | ✱150·04 | `Desc R (S ⁏ Q) ψ` |
| `P smor̄ Q`, `smor` | ✱151·01·02 | `smorbar P Q`, `smor P Q` |
| `Nr`, `Nr'P`, `Nr(X)'P`, `NR` | ✱152·01·02 | `Nr`, `nr γ P` (`X : γ → γ → Prop`), `NR β` |
| `1_s` | ✱153·01 | `one_s` (`0_r`, `2_r`: `zero_r`, `two_r` of ✱56) |
| `NR^Y(X)` | ✱154·01 | `NRT X Y` |
| `N₀r'P`, `N₀r`, `N₀R` | ✱155·01·02 | `n₀r P`, `N₀r`, `N₀R` |
| `P ⤉ Q` | ✱160·01·32 | `P ⤉ Q` (`rsum`) |
| `P ⇸ x`, `x ⇷ P` | ✱161·01·02·212·213 | `P ⇸ x` (`addLast`), `x ⇷ P` (`addFirst`) |
| `Σ'P`, `Σ` | ✱162·01 | `relSigma P`, `RelSigma` |
| `Rel² excl` | ✱163·01 | `Rel2excl` |
| `P smor̄smor̄ Q`, `smor smor` | ✱164·01·02 | `smorsmorbar P Q`, `smorsmor P Q` |
| `Q × P` | ✱166·01·421 | `Q ×ᵣ P` (`rtimes`) |
| `P_cl`, `P_lc` | ✱170·01·02 | `Pcl P`, `Plc P` |
| `P_df`, `P_fd` | ✱171·01·02 | `Pdf P`, `Pfd P` |
| `Π'P`, `Π` | ✱172·01 | `relPi P`, `RelPi` |
| `Prod'P`, `Prod` | ✱173·01 | `prodR P`, `ProdR` |
| `Rel³ arithm` | ✱174·01 | `Rel3arithm` |
| `P exp Q`, `P^Q` | ✱176·01·02 | `rexp P Q`, `rpow P Q` |
| `ṡ` (relation), `s` (relation) | ✱41·02, ✱40·02 | `sDotRel` (`graph sumRel`), `sRel` (`graph sumCls`) |
| `df`, `df'Q` (Dft ✱177) | ✱177·2 | `dfRel`, `Pdf Q` |
| `P + Q` | ✱180·01·531 | `P +ᵣ Q` (`rplus`) |
| `μ +̇ ν` | ✱180·02·561 | `μ ∔ ν` (`nrAdd`) |
| `P ⇸̇ x`, `x ⇷̇ P` | ✱181·01·011 | `addLastDot P x`, `addFirstDot x P` |
| `μ +̇ 1̇`, `1̇ +̇ μ`, `1̇ +̇ 1̇` | ✱181·02·021·04 | `nrAddOne β μ`, `nrOneAdd β μ`, `two_r` |
| `♀̆`, `↓̆`, `↓̆.,`, `↓̆.,;P` | ✱182·01 | `opDiag f`, `opDiag couple`, `opDiag (opSemi couple)`, `sepRel P` |
| `ΣNr'P` | ✱183·01 | `sigmaNr γ P` (relation `SigmaNr`) |
| `μ ×̇ ν` | ✱184·01·32 | `μ ⨰ ν` (`nrMul`) |
| `ΠNr'P` | ✱185·01 | `piNr γ P` (relation `PiNr`) |
| `μ exp_r ν` | ✱186·01 | `nrExp μ ν` |
| adequate actual type (relation-numbers) | — | `AdeqNr`, `AdeqNrAdd`, `AdeqNrMul`, `AdeqNrExp`, `AdeqSigmaNr`, `AdeqPiNr`, `AdeqNrAddOne`, `AdeqNrOneAdd` |

Precedences: `⁏` 66 (right); `⤉`, `⇸`, `+ᵣ`, `∔` 65 (left), `⇷` 65 (right); `×ᵣ`, `⨰` 70 (left).
So `S ⁏ P ⤉ S ⁏ Q` is `(S ⁏ P) ⤉ (S ⁏ Q)` (✱160·44), `sumRel (fld P) ⊍ F ⁏ P` is
`sumRel (fld P) ⊍ (F ⁏ P)` (✱162·01), `S ⁏ A ◁ Q ↾ B` is `S ⁏ (A ◁ Q ↾ B)` (✱150·34; `⨾`, `↾`,
`⥏`, `⩀`, `×ᵣ` bind tighter than `⁏`), `↓Λ_x;ι;P ⇸ (Λ ∩ C'P)↓ι'x` is
`(coupleR (clsT Λ x) ⁏ iota ⁏ P) ⇸ ((Λ ∩ fld P) ↓ ι x)` (✱181·01; `↓` is 78), `x ↓ y ⇸ z` is
`(x ↓ y) ⇸ z`. PM brackets every mixture of `⤉`, `⇸`, `⇷`, `×` with `∪̇` or with each other:
write the same brackets. Application binds tightest: `daggerRel S ↾ fld Q` is `(S†) ↾ C'Q`,
`Pcl P˘` is `(P̆)_cl`, and the converse of a compound needs brackets, `(Pcl P˘)˘`.
-/

namespace PrincipiaMathematica

universe u v w u' v' w'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

/-! ## Section A: ordinal similarity and relation-numbers (✱150–✱155) -/

/-- **✱150·01 Df.** \(S^{;}Q=S\mid Q\mid \breve{S} \quad\text{Df}\)

`S;Q`, notation `S ⁏ Q`: the relation of `S'z` to `S'w` when `zQw` (for one-many `S`;
`semi_apply`: `x(S;Q)y ≡ (∃z,w) . xSz . ySw . zQw`, ✱150·11). `S` may be heterogeneous, `Q` is
homogeneous (on the converse domain type of `S`), and `S;Q` is homogeneous. `S | Q | S̆` is
`(S | Q) | S̆` (✱34·22). Target: `pm150_01 : S ⁏ Q = S ⨾ Q ⨾ S˘ := rfl`. -/
def semi (S : α → β → Prop) (Q : β → β → Prop) : α → α → Prop := S ⨾ Q ⨾ S˘

@[inherit_doc] scoped infixr:66 " ⁏ " => semi

/-- **✱150·02 Df.** \(S\dagger Q=S\mid Q\mid \breve{S} \quad \text{Df}\)

The term `S†Q` (same definiens as `S;Q`; "merely an alternative to `S;Q`, just as `R_∈'α` is an
alternative to `R''α`"). The *relation* `S†` is `daggerRel S` (✱38·01; encoding decision 7).
Target: `pm150_02 : daggerOp S Q = S ⨾ Q ⨾ S˘ := rfl`. -/
def daggerOp (S : α → β → Prop) (Q : β → β → Prop) : α → α → Prop := S ⨾ Q ⨾ S˘

/-- The relation `S†` of `S†Q` to `Q` (✱38·01 with `♀ = †`); `S†'Q` is `daggerOp S Q`
(`desc_daggerRel`), `S†''λ` is `daggerRel S ʻʻ L`, `S†;Q` is `daggerRel S ⁏ Q`. Not itself a Df. -/
def daggerRel (S : α → β → Prop) : (α → α → Prop) → (β → β → Prop) → Prop := opL daggerOp S

/-- **✱150·03 Df.** \(Q\unicode{x2640}_{.,}y=\unicode{x2640}y^{;}Q \quad\text{Df}\)

`♀` is any double descriptive function (✱38), a Lean `f : α → β → γ`; `♀y` is `opR f y` (the
relation of `x♀y` to `x`). `Q♀.,y` is `opSemi f Q y` (`Q : α → α → Prop`); the relation `Q♀.,`
(of `Q♀.,y` to `y`) is `opL (opSemi f) Q`. For `♀ = ↓`: `P↓.,y = ↓y;P` is
`opSemi couple P y` and `P↓.,` is `coupleSemi P`. Target:
`pm150_03 : opSemi f Q y = opR f y ⁏ Q := rfl`. -/
def opSemi (f : α → β → γ) (Q : α → α → Prop) (y : β) : γ → γ → Prop := opR f y ⁏ Q

/-- `P↓.,`, the relation of `P↓.,y` (`= ↓y;P`) to `y` (✱150·03 with ✱38·01); `P↓.,;Q` is
`coupleSemi P ⁏ Q`, `P↓.,''β` is `coupleSemi P ʻʻ B`. -/
def coupleSemi (P : α → α → Prop) : ((α → β → Prop) → (α → β → Prop) → Prop) → β → Prop :=
  opL (opSemi couple) P

/-!
**✱150·04 Df.** \(RʻS^{;}Q=Rʻ(S^{;}Q) \quad\text{Df}\)

Bracketing convention: `R'S;Q` is the descriptive function `R'` applied to `S;Q`; with
descriptions, `ψ(R'S;Q)` is `Desc R (S ⁏ Q) ψ`, and for a relation `R = graph f` it is
`ψ (f (S ⁏ Q))` (e.g. `C'S;Q` is `fld (S ⁏ Q)`, `Σ'P↓.,;Q` is `relSigma (coupleSemi P ⁏ Q)`).
Target (status `definition`), with `R : γ → (α → α → Prop) → Prop`:
`pm150_04 : Desc R (S ⁏ Q) ψ ↔ TheIs (fun x => R x (S ⁏ Q)) ψ := Iff.rfl`.

**✱150·05 Df.** \(R^{;}S^{;}Q=R^{;}(S^{;}Q) \quad\text{Df}\)

Realized by `infixr`. Target (status `definition`): `pm150_05 : R ⁏ S ⁏ Q = R ⁏ (S ⁏ Q) := rfl`.
-/

/-- **✱151·01 Df.** \(P\,\overline{\text{smor}}\,Q=\hat{S}\{S\in 1\rightarrow 1.CʻQ=\text{ᗡ}ʻS.P=S^{;}Q\} \quad\text{Df}\)

The ordinal correlators of `P` with `Q`: one-one relations `S` with converse domain `C'Q` such that
`P = S;Q`. The definiens is a product of three, bracketed to the left (✱4·34). Target:
`pm151_01 : smorbar P Q = {S | (S ∈ arrow one one ∧ fld Q = codom S) ∧ P = S ⁏ Q} := rfl`. -/
def smorbar (P : α → α → Prop) (Q : β → β → Prop) : Set (α → β → Prop) :=
  {S | (S ∈ arrow one one ∧ fld Q = codom S) ∧ P = S ⁏ Q}

/-- **✱151·02 Df.** \(\text{smor}=\hat{P} \hat{Q}\{\exists !P\,\overline{\text{smor}}\,Q\} \quad\text{Df}\)

Ordinal similarity (likeness), written `smor P Q`. It is an equivalence (`smor_refl`, `smor_symm`,
`smor_trans`) and is "a bijection of the fields preserving the relation"
(`smor_iff_exists_equiv`). Target:
`pm151_02 : (smor : (α → α → Prop) → (β → β → Prop) → Prop) = fun P Q => (smorbar P Q).Nonempty
:= rfl`. -/
def smor : (α → α → Prop) → (β → β → Prop) → Prop := fun P Q => (smorbar P Q).Nonempty

/-- `Nr'P` in the type `γ` (PM's `Nr(X)'P` with `X : γ → γ → Prop`): the relations on `γ` like
`P`, `smor⃗'P` (✱152·1). The type `γ` is explicit (encoding decision 2). Value function of `Nr`. -/
def nr (γ : Type w) {β : Type v} (P : β → β → Prop) : Set (γ → γ → Prop) := refs smor P

/-- **✱152·01 Df.** \(\text{Nr} = \overrightarrow{\text{smor}} \quad\text{Df}\)

The relation of a relation-number to any relation of which it is the number; typically ambiguous
in both its domain and converse domain. `Nr'P` is `nr γ P` (`desc_Nr`). Target:
`pm152_01 : (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) = Rfwd smor := rfl`. -/
def Nr {γ : Type w} {β : Type v} : Set (γ → γ → Prop) → (β → β → Prop) → Prop := Rfwd smor

/-- **✱152·02 Df.** \(\text{NR}= \text{D}ʻ\text{Nr} \quad\text{Df}\)

The relation-numbers (whose members are relations on `γ`) of relations on `β`; the type `β`, left
ambiguous by PM, is the explicit argument (as `NC β`). `mem_NR`. The definiens is the descriptive
function `D'Nr` (Basic §5): `pm152_02 : Desc D (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop)
(fun K => NR β = K) := (desc_graph _ _ _).2 rfl`. -/
def NR {γ : Type w} (β : Type v) : Set (Set (γ → γ → Prop)) :=
  dom (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop)

/-- **✱153·01 Df.** \(1_{s}=\hat{R}\{(\exists x).R=x\downarrow x\} \quad\text{Df}\)

The relation-number of relations whose field has one term (not called `1_r`: PM defines `ν_r`
later so that `1_r = Λ`). Homogeneous (`x ↓ x : α → α → Prop`). Target:
`pm153_01 : (one_s : Set (α → α → Prop)) = {R | ∃ x, R = x ↓ x} := rfl`. -/
def one_s : Set (α → α → Prop) := {R | ∃ x, R = x ↓ x}

/-- **✱154·01 Df.** \(\text{NR}^{Y}(X) = \text{D}ʻ\text{Nr}(X_{Y}) \quad\text{Df}\)

`NR^Y(X)`: the relation-numbers of relations of the type of `Y`, taken in the type of `X`.
`Nr(X_Y)` is ✱65·11 `relT2T Nr X Y` (domain in `t²'X`, converse domain in `t'Y`).
`NRT X Y = NR β` (`NRT_eq_NR`). Target (definiens a descriptive function):
`pm154_01 : Desc D (relT2T (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) X Y)
(fun K => NRT X Y = K) := (desc_graph _ _ _).2 rfl`. -/
def NRT (X : γ → γ → Prop) (Y : β → β → Prop) : Set (Set (γ → γ → Prop)) :=
  dom (relT2T (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) X Y)

/-- **✱155·01 Df.** \(\text{N}_{0}\text{r}ʻP=\text{Nr}ʻP\cap tʻP \quad\text{Df}\)

The homogeneous relation-number of `P`: the relations of the type of `P` like `P` (`n₀r_eq_nr`:
it is `nr α P`). Value function of `N₀r`. Target: `pm155_01 : n₀r P = nr α P ∩ typ P := rfl`. -/
def n₀r (P : α → α → Prop) : Set (α → α → Prop) := nr α P ∩ typ P

/-- The relation `N₀r` of `N₀r'P` to `P` (✱155·01 defines its descriptive function). -/
def N₀r : Set (α → α → Prop) → (α → α → Prop) → Prop := graph n₀r

/-- **✱155·02 Df.** \(\text{N}_{0}\text{R}=\text{D}ʻ\text{N}_{0}\text{r} \quad\text{Df}\)

The homogeneous relation-numbers (of relations on `α`). `mem_N₀R`. Target:
`pm155_02 : Desc D N₀r (fun K => (N₀R : Set (Set (α → α → Prop))) = K) :=
(desc_graph _ _ _).2 rfl`. -/
def N₀R : Set (Set (α → α → Prop)) := dom (N₀r : Set (α → α → Prop) → (α → α → Prop) → Prop)

/-! ## Section B: addition of relations, and the product of two relations (✱160–✱166) -/

/-- **✱160·01 Df.** \(P\unicode{x2909}Q=P\unicode{x228d} Q\unicode{x228d} CʻP\uparrow CʻQ \quad\text{Df}\)

The ordinal sum `P ⤉ Q` of two relations of the same type: `P`, then `Q`, every term of `C'P`
before every term of `C'Q`. `∪̇` brackets to the left (✱23·71) and `↑` is the name `cross`.
`rsum_apply` (✱160·11). Target: `pm160_01 : P ⤉ Q = P ⊍ Q ⊍ cross (fld P) (fld Q) := rfl`. -/
def rsum (P Q : α → α → Prop) : α → α → Prop := P ⊍ Q ⊍ cross (fld P) (fld Q)

@[inherit_doc] scoped infixl:65 " ⤉ " => rsum

/-!
**✱160·32 Df.** \(P\unicode{x2909}Q\unicode{x2909}R=(P\unicode{x2909}Q)\unicode{x2909}R \quad\text{Df}\)

Realized by `infixl`. Target (status `definition`): `pm160_32 : P ⤉ Q ⤉ R = (P ⤉ Q) ⤉ R := rfl`.
-/

/-- **✱161·01 Df.** \(P\unicode{x21f8} x = P\unicode{x228d} CʻP\uparrow {℩}ʻx \quad\text{Df}\)

`P ⇸ x`: `x` added at the end of `P` (every member of `C'P` before `x`, `x` not before itself;
`Λ̇ ⇸ x = Λ̇`, ✱161·2). `addLast_apply` (✱161·11). Target:
`pm161_01 : P ⇸ x = P ⊍ cross (fld P) (ι x) := rfl`. -/
def addLast (P : α → α → Prop) (x : α) : α → α → Prop := P ⊍ cross (fld P) (ι x)

@[inherit_doc] scoped infixl:65 " ⇸ " => addLast

/-- **✱161·02 Df.** \(x\unicode{x21f7}P = {℩}ʻx\uparrow CʻP\unicode{x228d} P \quad\text{Df}\)

`x ⇷ P`: `x` added at the beginning of `P`. `ι'x ↑ C'P ∪̇ P` is `(ι'x ↑ C'P) ∪̇ P`. Target:
`pm161_02 : x ⇷ P = cross (ι x) (fld P) ⊍ P := rfl`. -/
def addFirst (x : α) (P : α → α → Prop) : α → α → Prop := cross (ι x) (fld P) ⊍ P

@[inherit_doc] scoped infixr:65 " ⇷ " => addFirst

/-!
**✱161·212 Df.** \(P\unicode{x21f8} x\unicode{x21f8} y=(P\unicode{x21f8} x)\unicode{x21f8} y \quad\text{Df}\)

**✱161·213 Df.** \(x\unicode{x21f7}y\unicode{x21f7}P=x\unicode{x21f7}(y\unicode{x21f7}P) \quad\text{Df}\)

Realized by `infixl` for `⇸` and `infixr` for `⇷`. Targets (status `definition`):
`pm161_212 : P ⇸ x ⇸ y = (P ⇸ x) ⇸ y := rfl`; `pm161_213 : x ⇷ y ⇷ P = x ⇷ (y ⇷ P) := rfl`.
-/

/-- **✱162·01 Df.** \(\Sigma ʻP=\dot{s} ʻCʻP\unicode{x228d} F^{;}P \quad\text{Df}\)

The sum `Σ'P` of the relations of the field of a relation of relations `P`, in the order `P`:
`x (Σ'P) y` when `xQy` for some `Q ∈ C'P`, or `x ∈ C'Q`, `y ∈ C'R` with `QPR` (`relSigma_apply`,
✱162·12). `F` is ✱33·04 (`F x Q ↔ x ∈ fld Q`); `F;P` is `F ⁏ P`. The relation `Σ` is
`RelSigma`. Target: `pm162_01 : relSigma P = sumRel (fld P) ⊍ F ⁏ P := rfl`. -/
def relSigma (P : (α → α → Prop) → (α → α → Prop) → Prop) : α → α → Prop :=
  sumRel (fld P) ⊍ F ⁏ P

/-- The relation `Σ` of `Σ'P` to `P`; `Σ;P` is `RelSigma ⁏ P`. -/
def RelSigma : (α → α → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) → Prop :=
  graph relSigma

/-- **✱163·01 Df.** \(\text{Rel}^{2}\text{excl}=\hat{P} \{Q,R\in CʻP.Q\neq R.\supset _{Q,R}.CʻQ\cap CʻR=\Lambda\} \quad\text{Df}\)

Relations of mutually exclusive relations: distinct members of `C'P` have disjoint fields.
`Q, R ∈ C'P` is `Q ∈ fld P ∧ R ∈ fld P` (✱20·04), and the hypothesis is the product
`Q, R ∈ C'P . Q ≠ R`. Target: `pm163_01 : (Rel2excl : Set ((α → α → Prop) → (α → α → Prop) →
Prop)) = {P | ∀ Q R, (Q ∈ fld P ∧ R ∈ fld P) ∧ Q ≠ R → fld Q ∩ fld R = Λ} := rfl`. -/
def Rel2excl : Set ((α → α → Prop) → (α → α → Prop) → Prop) :=
  {P | ∀ Q R, (Q ∈ fld P ∧ R ∈ fld P) ∧ Q ≠ R → fld Q ∩ fld R = Λ}

/-- **✱164·01 Df.** \(P\,\overline{\text{smor}} \,\overline{\text{smor}}\, Q=(1\rightarrow 1)\cap \overleftarrow{\text{ᗡ}}ʻCʻ\Sigma ʻQ\cap \hat{S} (P=S\dagger ^{;}Q) \quad\text{Df}\)

The double (ordinal) correlators of `P` with `Q` (relations of relations): one-one `S` with
converse domain `C'Σ'Q` and `P = S†;Q`. `ᗡ⃖'C'Σ'Q` is `rels Dcnv (fld (relSigma Q))`
(`= {S | fld (relSigma Q) = codom S}`); the products bracket to the left. Target:
`pm164_01 : smorsmorbar P Q = arrow one one ∩ rels Dcnv (fld (relSigma Q)) ∩
{S | P = daggerRel S ⁏ Q} := rfl`. -/
def smorsmorbar (P : (α → α → Prop) → (α → α → Prop) → Prop)
    (Q : (β → β → Prop) → (β → β → Prop) → Prop) : Set (α → β → Prop) :=
  arrow one one ∩ rels Dcnv (fld (relSigma Q)) ∩ {S | P = daggerRel S ⁏ Q}

/-- **✱164·02 Df.** \(\text{smor} \text{smor} =\hat{P} \hat{Q} (\exists !P\,\overline{\text{smor}} \,\overline{\text{smor}}\, Q) \quad\text{Df}\)

Double likeness (one symbol `smor smor`). Target:
`pm164_02 : (smorsmor : ((α → α → Prop) → (α → α → Prop) → Prop) →
((β → β → Prop) → (β → β → Prop) → Prop) → Prop) = fun P Q => (smorsmorbar P Q).Nonempty := rfl`. -/
def smorsmor : ((α → α → Prop) → (α → α → Prop) → Prop) →
    ((β → β → Prop) → (β → β → Prop) → Prop) → Prop :=
  fun P Q => (smorsmorbar P Q).Nonempty

/-- **✱166·01 Df.** \(Q\times P=\Sigma ʻP\downarrow_{.,} ^{;}Q \quad\text{Df}\)

The ordinal product `Q × P` (PM's order, as `β × α` in ✱113·02), notation `Q ×ᵣ P`. By ✱150·04
`Σ'P↓.,;Q` is `Σ'((P↓.,);Q)`: the couples `x ↓ z` (`x ∈ C'P`, `z ∈ C'Q`), ordered first by `Q` on
`z`, then by `P` on `x` (`rtimes_apply`, ✱166·11). Target:
`pm166_01 : Q ×ᵣ P = relSigma (coupleSemi P ⁏ Q) := rfl`. -/
def rtimes (Q : β → β → Prop) (P : α → α → Prop) : (α → β → Prop) → (α → β → Prop) → Prop :=
  relSigma (coupleSemi P ⁏ Q)

@[inherit_doc] scoped infixl:70 " ×ᵣ " => rtimes

/-!
**✱166·421 Df.** \(P \times Q \times R = (P \times Q) \times R \quad\text{Df}\)

Realized by `infixl`. Target (status `definition`): `pm166_421 : P ×ᵣ Q ×ᵣ R = (P ×ᵣ Q) ×ᵣ R :=
rfl` (with `P : α → α → Prop`, `Q : β → β → Prop`, `R : γ → γ → Prop`).
-/

/-! ## Section C: first differences, multiplication and exponentiation of relations (✱170–✱177) -/

/-- **✱170·01 Df.** \(P_{\text{cl}}=\hat{\alpha} \hat{\beta} \{\alpha ,\beta \in \text{Cl}ʻCʻP.\exists !\alpha -\beta -\breve{P} ʻʻ(\beta -\alpha )\} \quad\text{Df}\)

`α P_cl β`: `α`, `β` are sub-classes of `C'P` and some member of `α − β` is preceded by no member
of `β − α`. `α, β ∈ Cl'C'P` is `A ∈ cl (fld P) ∧ B ∈ cl (fld P)` (✱20·04); `α − β − P̆''(β − α)`
is `(α − β) − P̆''(β − α)`. Target:
`pm170_01 : Pcl P = fun A B => (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧
((A \ B) \ P˘ ʻʻ (B \ A)).Nonempty := rfl`. -/
def Pcl (P : α → α → Prop) : Set α → Set α → Prop :=
  fun A B => (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧ ((A \ B) \ P˘ ʻʻ (B \ A)).Nonempty

/-- **✱170·02 Df.** \(P_{\text{lc}} = \text{Cnv}ʻ(\breve{P} )_{\text{cl}} \quad\text{Df}\)

`P_lc`, the converse of `(P̆)_cl`, written `Plc P` (`= (Pcl P˘)˘` by `rfl`). The definiens is the
descriptive function `Cnv'…` (Basic §5): `pm170_02 : Desc Cnv (Pcl P˘) (fun X => Plc P = X) :=
(desc_Cnv _ _).2 rfl`. -/
def Plc (P : α → α → Prop) : Set α → Set α → Prop := (Pcl P˘)˘

/-- **✱171·01 Df.** \(P_{\text{df}}=\hat{\alpha} \hat{\beta} \{\alpha ,\beta \in \text{Cl}ʻCʻP:(\exists z).z\in \alpha -\beta .\overrightarrow{P}ʻz\cap \alpha -\iota ʻz=\overrightarrow{P}ʻz\cap \beta\} \quad\text{Df}\)

`α P_df β`: the first difference of `α` and `β` is a member of `α`. The colon is a product, the
scope of `(∃z)` is the rest; `P⃗'z ∩ α − ι'z` is `(P⃗'z ∩ α) − ι'z` (`= P⃗'z ∩ (α − ι'z)`); Lean's
`∩` and `\` need the brackets. Target:
`pm171_01 : Pdf P = fun A B => (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧
∃ z, z ∈ A \ B ∧ (refs P z ∩ A) \ ι z = refs P z ∩ B := rfl`. -/
def Pdf (P : α → α → Prop) : Set α → Set α → Prop :=
  fun A B => (A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧
    ∃ z, z ∈ A \ B ∧ (refs P z ∩ A) \ ι z = refs P z ∩ B

/-- **✱171·02 Df.** \(P_\text{fd}=\text{Cnv}ʻ(\breve{P} )_{\text{df}} \quad\text{Df}\)

As ✱170·02: `pm171_02 : Desc Cnv (Pdf P˘) (fun X => Pfd P = X) := (desc_Cnv _ _).2 rfl`. -/
def Pfd (P : α → α → Prop) : Set α → Set α → Prop := (Pdf P˘)˘

/-- **✱172·01 Df.** \[\begin{align}\Pi ʻP=\hat{M} \hat{N} &\{M,N\in F_{\Delta }ʻCʻP\colon\ldotp \\ &(\exists Q):(MʻQ)Q(NʻQ):RPQ.R\neq Q.\supset _{R}.MʻR=NʻR\} \quad\text{Df}\end{align}\]

The product `Π'P` of the relations of the field of a relation of relations `P`: it orders the
`F`-selections `M` from `C'P` (one representative `M'Q ∈ C'Q` for each `Q ∈ C'P`;
`F_Δ'C'P` is `sel F (fld P)`) by first differences. The three dots make `M,N ∈ F_Δ'C'P` one
factor and `(∃Q) : … : …` the other; within the scope of `(∃Q)` the colon is a product, and the
hypothesis of `⊃_R` is the product `RPQ . R ≠ Q`. The descriptions `M'Q`, `N'Q` are kept
(`Desc`; the first one has the larger scope, ✱14·03): `(M'Q)Q(N'Q)` is
`Desc M Q (fun x => Desc N Q (fun y => Q x y))`, `M'R = N'R` is
`Desc M R (fun x => Desc N R (fun y => x = y))`. The relation `Π` is `RelPi`. Target:
`pm172_01 : relPi P = fun M N => (M ∈ sel F (fld P) ∧ N ∈ sel F (fld P)) ∧
∃ Q, Desc M Q (fun x => Desc N Q (fun y => Q x y)) ∧
∀ R, P R Q ∧ R ≠ Q → Desc M R (fun x => Desc N R (fun y => x = y)) := rfl`. -/
def relPi (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    (α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop :=
  fun M N => (M ∈ sel F (fld P) ∧ N ∈ sel F (fld P)) ∧
    ∃ Q, Desc M Q (fun x => Desc N Q (fun y => Q x y)) ∧
      ∀ R, P R Q ∧ R ≠ Q → Desc M R (fun x => Desc N R (fun y => x = y))

/-- The relation `Π` of `Π'P` to `P`; `Π;P` is `RelPi ⁏ P`. -/
def RelPi : ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop :=
  graph relPi

/-- **✱173·01 Df.** \(\text{Prod}ʻP=\text{D}^{;}\Pi ʻP \quad\text{Df}\)

`Prod'P`, the relation of the domains of the selections related by `Π'P` (the ordinal analogue of
`Prod'κ`, ✱115·01); named `prodR` (Defs/Part3's `prodK` is `Prod'κ`). `D;Π'P` is `D ⁏ relPi P`.
The relation `Prod` is `ProdR`. The Df defines the descriptive function, so the target is the
equation of its value function: `pm173_01 : prodR P = D ⁏ relPi P := rfl`. -/
def prodR (P : (α → α → Prop) → (α → α → Prop) → Prop) : Set α → Set α → Prop := D ⁏ relPi P

/-- The relation `Prod` of `Prod'P` to `P`; `Prod;P` is `ProdR ⁏ P`. -/
def ProdR : (Set α → Set α → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) → Prop :=
  graph prodR

/-- **✱174·01 Df.** \(\text{Rel}^{3}\text{arithm}=\hat{P} (P,\Sigma ʻP\in \text{Rel}^{2}\text{excl}) \quad\text{Df}\)

Arithmetical relations: `P` and `Σ'P` are both relations of mutually exclusive relations.
`P, Σ'P ∈ Rel² excl` is the product `P ∈ Rel² excl . Σ'P ∈ Rel² excl`, the two `Rel² excl` being
of different types, so it is a conjunction, not `Mem2` (as ✱115·02). Target:
`pm174_01 : (Rel3arithm : Set (((α → α → Prop) → (α → α → Prop) → Prop) →
((α → α → Prop) → (α → α → Prop) → Prop) → Prop)) =
{P | P ∈ Rel2excl ∧ relSigma P ∈ Rel2excl} := rfl`. -/
def Rel3arithm : Set (((α → α → Prop) → (α → α → Prop) → Prop) →
    ((α → α → Prop) → (α → α → Prop) → Prop) → Prop) :=
  {P | P ∈ Rel2excl ∧ relSigma P ∈ Rel2excl}

/-- The relation `ṡ` of `ṡ'λ` to `λ` (✱41·02 defines `ṡ'λ`; the relation is
`ûλ̂(u = ṡ'λ)`, Summary of Part I Section E). `ṡ;R` is `sDotRel ⁏ R`. -/
def sDotRel : (α → β → Prop) → Set (α → β → Prop) → Prop := graph sumRel

/-- The relation `s` of `s'κ` to `κ` (✱40·02), as in `s ↾ C'Prod'df;P` (✱177·21). -/
def sRel : Set α → Set (Set α) → Prop := graph sumCls

/-- **✱176·01 Df.** \(P \,\text{exp}\,\, Q = \text{Prod}ʻP\downarrow_{.,} ^{;}Q \quad\text{Df}\)

`P exp Q`, by ✱150·04 `Prod'((P↓.,);Q)`: it orders the classes of couples `x ↓ y` selecting one
`x ∈ C'P` for each `y ∈ C'Q` by first differences (✱176·12). Target:
`pm176_01 : rexp P Q = prodR (coupleSemi P ⁏ Q) := rfl`. -/
def rexp (P : α → α → Prop) (Q : β → β → Prop) :
    Set (α → β → Prop) → Set (α → β → Prop) → Prop :=
  prodR (coupleSemi P ⁏ Q)

/-- **✱176·02 Df.** \(P^{Q} = \dot{s} ^{;}(P \,\text{exp}\,\, Q) \quad\text{Df}\)

`P^Q`, the corresponding relation of the relations `ṡ'μ` (the "Belegungen" `M`, `N`);
`ṡ;(…)` is `sDotRel ⁏ …`. Target: `pm176_02 : rpow P Q = sDotRel ⁏ rexp P Q := rfl`. -/
def rpow (P : α → α → Prop) (Q : β → β → Prop) : (α → β → Prop) → (α → β → Prop) → Prop :=
  sDotRel ⁏ rexp P Q

/-- **✱177·2 Dft [✱177].** \(\text{df}ʻQ=Q_{\text{df}} \quad\text{Dft}[*177]\)

(Printed in the e-text as a proposition.) A temporary definition for ✱177: the relation `df` of
`Q_df` to `Q`, `dfRel = graph Pdf`, so that `df;P` is `dfRel ⁏ P` and `df''C'P` is
`dfRel ʻʻ fld P`. The Dft defines the descriptive function `df'Q`, whose value is the term `Q_df`;
the target states it with the description: `pm177_2 : Desc dfRel Q (fun X => X = Pdf Q) :=
(desc_graph _ _ _).2 rfl` (status `definition`; say it is a Dft). -/
def dfRel : (Set α → Set α → Prop) → (α → α → Prop) → Prop := graph Pdf

/-! ## Section D: arithmetic of relation-numbers (✱180–✱186) -/

/-- **✱180·01 Df.** \(P + Q = {\downarrow (\Lambda \cap CʻQ)^{;}{℩}^{;}P} \unicode{x2909} \{(\Lambda \cap CʻP) \downarrow ^{;}\iota ^{;}Q\} \quad\text{Df}\)

The arithmetical sum `P + Q` of two relations of any types, notation `P +ᵣ Q` (the analogue of
`α + β`, ✱110·01; the e-text's first pair of braces is invisible TeX grouping, PM prints
`{↓(Λ ∩ C'Q);ι;P} ⤉ {(Λ ∩ C'P)↓;ι;Q}`, Summary of ✱180). `ι;P` is `iota ⁏ P`, `↓(Λ ∩ C'Q)` is
`coupleR (Λ ∩ fld Q)`, `(Λ ∩ C'P)↓` is `coupleL (Λ ∩ fld P)`, and `R;S;Q` is `R;(S;Q)` (✱150·05).
`C'(P + Q) = C'P + C'Q` (`fld_rplus`, ✱180·111). Target:
`pm180_01 : P +ᵣ Q = (coupleR (Λ ∩ fld Q) ⁏ iota ⁏ P) ⤉ (coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q) :=
rfl`. -/
def rplus (P : α → α → Prop) (Q : β → β → Prop) :
    (Set α → Set β → Prop) → (Set α → Set β → Prop) → Prop :=
  (coupleR (Λ ∩ fld Q) ⁏ iota ⁏ P) ⤉ (coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q)

@[inherit_doc] scoped infixl:65 " +ᵣ " => rplus

/-- **✱180·02 Df.** \(\mu \dot{+} \nu = \hat{R} \{(\exists P,Q) . \mu = \text{N}_0\text{r}ʻP . \nu = \text{N}_0\text{r}ʻQ . R\,\text{smor}\,(P + Q)\} \quad\text{Df}\)

The sum of two relation-numbers, `μ ∔ ν` (U+2214); actual type implicit (encoding decision 2).
The definiens is a product of three, bracketed to the left. It is `Λ` unless `μ`, `ν` are
homogeneous relation-numbers. Target: `pm180_02 : (μ ∔ ν : Set (γ → γ → Prop)) =
{R | ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (P +ᵣ Q)} :=
rfl`. -/
def nrAdd {α : Type u} {β : Type v} {γ : Type w} (μ : Set (α → α → Prop))
    (ν : Set (β → β → Prop)) : Set (γ → γ → Prop) :=
  {R | ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (P +ᵣ Q)}

@[inherit_doc] scoped infixl:65 " ∔ " => nrAdd

/-!
**✱180·03 Df.** \(\text{Nr}ʻP \dot{+} \nu = \text{N}_0\text{r}ʻP \dot{+} \nu \quad\text{Df}\)

**✱180·031 Df.** \(\mu \dot{+} \text{Nr}ʻQ = \mu \dot{+} \text{N}_0\text{r}ʻQ \quad\text{Df}\)

Translation rules (normal adjustment, encoding decision 4; "see the remarks on the corresponding
definitions in ✱110 and IIT"): an argument `Nr'P` of `+̇` is written `n₀r P`. Targets (status
`definition`; say that the Df is a rule of translation):
`pm180_03 : (n₀r P ∔ ν : Set (γ → γ → Prop)) = n₀r P ∔ ν := rfl`;
`pm180_031 : (μ ∔ n₀r Q : Set (γ → γ → Prop)) = μ ∔ n₀r Q := rfl`.

**✱180·531 Df.** \(P + Q + R = (P + Q) + R \quad\text{Df}\)

Realized by `infixl`. Target: `pm180_531 : P +ᵣ Q +ᵣ R = (P +ᵣ Q) +ᵣ R := rfl`.

**✱180·561 Df.** \(\mu \dot{+} \nu \dot{+} \omega = (\mu \dot{+} \nu ])\dot{+} \omega \quad\text{Df}\)

(The e-text has a stray `]`: PM has `(μ +̇ ν) +̇ ω`.) Realized by `infixl`; the inner sum is an
arithmetical component, so its type is a separate parameter `W` (IIT). Target:
`pm180_561 : ((μ ∔ ν : Set (W → W → Prop)) ∔ ω : Set (γ → γ → Prop)) =
((μ ∔ ν : Set (W → W → Prop)) ∔ ω : Set (γ → γ → Prop)) := rfl`.
-/

/-- **✱181·01 Df.** \(P \dot{\unicode{x21f8}} x = \downarrow \Lambda _{x}^{;}{℩}^{;}P \unicode{x21f8} (\Lambda \cap CʻP) \downarrow {℩}ʻx \quad\text{Df}\)

`P ⇸̇ x`: a relation like `P` (`↓Λ_x;ι;P`, the couples `ι'y ↓ Λ_x`) with the couple
`(Λ ∩ C'P) ↓ ι'x` added at the end; `x` and `P` may be of any relative types. `Λ_x` is ✱65·01
`clsT Λ x` (`Λ ∩ t'x`). Only the bracketing `(↓Λ_x;ι;P) ⇸ ((Λ ∩ C'P)↓ι'x)` is significant (✱181·1).
Target: `pm181_01 : addLastDot P x = (coupleR (clsT Λ x) ⁏ iota ⁏ P) ⇸ ((Λ ∩ fld P) ↓ ι x) :=
rfl`. -/
def addLastDot (P : α → α → Prop) (x : β) :
    (Set α → Set β → Prop) → (Set α → Set β → Prop) → Prop :=
  (coupleR (clsT Λ x) ⁏ iota ⁏ P) ⇸ ((Λ ∩ fld P) ↓ ι x)

/-- **✱181·011 Df.** \(x \dot{\unicode{x21f7}} P = ({℩}ʻx) \downarrow (\Lambda \cap CʻP) \unicode{x21f7} \Lambda _{x} \downarrow ^{;}{℩}^{;}P \quad\text{Df}\)

`x ⇷̇ P`: the couple `ι'x ↓ (Λ ∩ C'P)` added at the beginning of `Λ_x↓;ι;P` (the couples
`Λ_x ↓ ι'y`). Target: `pm181_011 : addFirstDot x P =
(ι x ↓ (Λ ∩ fld P)) ⇷ (coupleL (clsT Λ x) ⁏ iota ⁏ P) := rfl`. -/
def addFirstDot (x : β) (P : α → α → Prop) :
    (Set β → Set α → Prop) → (Set β → Set α → Prop) → Prop :=
  (ι x ↓ (Λ ∩ fld P)) ⇷ (coupleL (clsT Λ x) ⁏ iota ⁏ P)

/-- **✱181·02 Df.** \(\mu \dot{+} \dot{1} = \hat{R} \{(\exists P, x) . \text{N}_{0}\text{r}ʻP = \mu . R \,\text{smor}\, (P \dot{\unicode{x21f8}} x)\} \quad\text{Df}\)

`μ +̇ 1̇` (one symbol; `1̇` has no meaning by itself). The type `β` of the apparent variable `x` is
determined by nothing and is an explicit argument (encoding decision 3); the actual type `γ` is
implicit. Note PM's order `N₀r'P = μ`. Target: `pm181_02 : (nrAddOne β μ : Set (γ → γ → Prop)) =
{R | ∃ (P : α → α → Prop) (x : β), n₀r P = μ ∧ smor R (addLastDot P x)} := rfl`. -/
def nrAddOne (β : Type v) {α : Type u} {γ : Type w} (μ : Set (α → α → Prop)) :
    Set (γ → γ → Prop) :=
  {R | ∃ (P : α → α → Prop) (x : β), n₀r P = μ ∧ smor R (addLastDot P x)}

/-- **✱181·021 Df.** \(\dot{1} \dot{+} \mu = \hat{R} \{(\exists P, x) . \text{N}_{0}\text{r}ʻP = \mu . R \,\text{smor}\, (x \dot{\unicode{x21f7}} P)\} \quad\text{Df}\)

`1̇ +̇ μ`, as ✱181·02. Target: `pm181_021 : (nrOneAdd β μ : Set (γ → γ → Prop)) =
{R | ∃ (P : α → α → Prop) (x : β), n₀r P = μ ∧ smor R (addFirstDot x P)} := rfl`. -/
def nrOneAdd (β : Type v) {α : Type u} {γ : Type w} (μ : Set (α → α → Prop)) :
    Set (γ → γ → Prop) :=
  {R | ∃ (P : α → α → Prop) (x : β), n₀r P = μ ∧ smor R (addFirstDot x P)}

/-!
**✱181·03 Df.** \(\text{Nr}ʻP \dot{+} \dot{1} = \text{N}_{0}\text{r}ʻP \dot{+} \dot{1} \quad\text{Df}\)

**✱181·031 Df.** \(\dot{1} \dot{+} \text{Nr}ʻP = \dot{1} \dot{+} \text{N}_{0}\text{r}ʻP \quad\text{Df}\)

Translation rules, as ✱180·03·031. Targets (status `definition`):
`pm181_03 : (nrAddOne β (n₀r P) : Set (γ → γ → Prop)) = nrAddOne β (n₀r P) := rfl`;
`pm181_031 : (nrOneAdd β (n₀r P) : Set (γ → γ → Prop)) = nrOneAdd β (n₀r P) := rfl`.

**✱181·04 Df.** \(\dot{1} \dot{+} \dot{1} = 2_{r} \quad\text{Df}\)

"Purely formal" (PM): the symbol `1̇ +̇ 1̇` is written `two_r` (✱56·02, homogeneous). Target
(status `definition`; say that the Df is a rule of translation):
`pm181_04 : (two_r : Set (α → α → Prop)) = {R | ∃ x y, x ≠ y ∧ R = x ↓ y} := rfl`.

**✱181·561 Df.** \(\mu \dot{+} \dot{1} \dot{+} \dot{1} =\mu \dot{+} (\dot{1} \dot{+} \dot{1} ) \quad\text{Df}\)

**✱181·571 Df.** \(\dot{1} \dot{+} \dot{1} \dot{+} \mu =(\dot{1} \dot{+} \dot{1} )\dot{+} \mu \quad\text{Df}\)

Bracketing conventions ("the opposite convention to that usually adopted", PM): `μ +̇ 1̇ +̇ 1̇` is
`μ ∔ two_r`, *not* `nrAddOne β (nrAddOne β' μ)`, and `1̇ +̇ 1̇ +̇ μ` is `two_r ∔ μ`; the `2_r` is an
arithmetical component with its own type `W` (IIT). Targets (status `definition`):
`pm181_561 : (μ ∔ (two_r : Set (W → W → Prop)) : Set (γ → γ → Prop)) =
μ ∔ (two_r : Set (W → W → Prop)) := rfl`;
`pm181_571 : ((two_r : Set (W → W → Prop)) ∔ μ : Set (γ → γ → Prop)) =
(two_r : Set (W → W → Prop)) ∔ μ := rfl`.
-/

/-- **✱182·01 Df.** \(\breve{\unicode{x2640}}=\hat{y} \hat{x} (y=x\unicode{x2640}x) \quad\text{Df}\)

For a double descriptive function `♀` (`f : α → α → γ`), `♀̆` is the relation of `x♀x` to `x`,
`opDiag f`, so that `♀̆'x = x♀x` (`desc_opDiag`). `↓̆` is `opDiag couple` (`↓̆'x = x ↓ x`), `|̆` is
`opDiag relProd` (`|̆'R = R²`), and `↓̆.,` is `opDiag (opSemi couple)` (`↓̆.,'Q = Q↓.,Q = ↓Q;Q`);
the separated relation `↓̆.,;P` is `sepRel P`. Target:
`pm182_01 : opDiag f = fun y x => y = f x x := rfl`. -/
def opDiag (f : α → α → γ) : γ → α → Prop := graph (fun x => f x x)

/-- The separated relation `↓̆.,;P` of a relation of relations `P` (✱182): every member `x` of
`C'Q` (`Q ∈ C'P`) replaced by `x ↓ Q`. Not itself a Df. -/
def sepRel (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) →
    ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) → Prop :=
  opDiag (opSemi couple) ⁏ P

/-- `ΣNr'P` in the type `γ` (explicit, as for `nr`). Value function of `SigmaNr`. -/
def sigmaNr (γ : Type w) (P : (α → α → Prop) → (α → α → Prop) → Prop) : Set (γ → γ → Prop) :=
  nr γ (relSigma (sepRel P))

/-- **✱183·01 Df.** \(\Sigma \text{Nr}ʻP=\text{Nr}ʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}P \quad\text{Df}\)

The sum of the relation-numbers of the members of `C'P`, in the order `P`: by ✱30·02 and ✱150·04,
`Nr'(Σ'(↓̆.,;P))`. Target: `pm183_01 : sigmaNr γ P = nr γ (relSigma (opDiag (opSemi couple) ⁏ P))
:= rfl`. -/
def SigmaNr : Set (γ → γ → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) → Prop :=
  graph (sigmaNr γ)

/-- **✱184·01 Df.** \(\mu \dot{\times} \nu =\hat{R} \{(\exists P,Q).\mu =\text{N}_{0}\text{r}ʻP.\nu =\text{N}_{0}\text{r}ʻQ.R\,\text{smor}\,(P\times Q)\} \quad\text{Df}\)

The product of two relation-numbers, `μ ⨰ ν` (U+2A30); actual type implicit. `P × Q` is
`P ×ᵣ Q`. Target: `pm184_01 : (μ ⨰ ν : Set (γ → γ → Prop)) =
{R | ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (P ×ᵣ Q)} :=
rfl`. -/
def nrMul {α : Type u} {β : Type v} {γ : Type w} (μ : Set (α → α → Prop))
    (ν : Set (β → β → Prop)) : Set (γ → γ → Prop) :=
  {R | ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (P ×ᵣ Q)}

@[inherit_doc] scoped infixl:70 " ⨰ " => nrMul

/-!
**✱184·02 Df.** \(\text{Nr}ʻP\dot{\times} \nu =\text{N}_{0}\text{r}ʻP\dot{\times} \nu \quad\text{Df}\)

**✱184·03 Df.** \(\mu \dot{\times} \text{Nr}ʻQ=\mu \dot{\times} \text{N}_{0}\text{r}ʻQ \quad\text{Df}\)

Translation rules, as ✱180·03·031. Targets (status `definition`):
`pm184_02 : (n₀r P ⨰ ν : Set (γ → γ → Prop)) = n₀r P ⨰ ν := rfl`;
`pm184_03 : (μ ⨰ n₀r Q : Set (γ → γ → Prop)) = μ ⨰ n₀r Q := rfl`.

**✱184·32 Df.** \(\mu \dot{\times} \nu \dot{\times} \varpi =(\mu \dot{\times} \nu )\dot{\times} \varpi \quad\text{Df}\)

As ✱180·561. Target: `pm184_32 : ((μ ⨰ ν : Set (W → W → Prop)) ⨰ ϖ : Set (γ → γ → Prop)) =
((μ ⨰ ν : Set (W → W → Prop)) ⨰ ϖ : Set (γ → γ → Prop)) := rfl`.
-/

/-- `ΠNr'P` in the type `γ` (explicit). Value function of `PiNr`. -/
def piNr (γ : Type w) (P : (α → α → Prop) → (α → α → Prop) → Prop) : Set (γ → γ → Prop) :=
  nr γ (relPi P)

/-- **✱185·01 Df.** \(\Pi \text{Nr}ʻP=\text{Nr}ʻ\Pi ʻP \quad\text{Df}\)

The product of the relation-numbers of the members of `C'P`, in the order `P`. Target:
`pm185_01 : piNr γ P = nr γ (relPi P) := rfl`. -/
def PiNr : Set (γ → γ → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) → Prop :=
  graph (piNr γ)

/-- **✱186·01 Df.** \(\mu \,\text{exp}\,\,_{r}\nu =\hat{R} \{(\exists P,Q).\mu =\text{N}_{0}\text{r}ʻP.\nu =\text{N}_{0}\text{r}ʻQ.R\,\text{smor}\,(P\,\text{exp}\,\,Q)\} \quad\text{Df}\)

`μ exp_r ν`, the `ν`th power of the relation-number `μ`; actual type implicit. Target:
`pm186_01 : (nrExp μ ν : Set (γ → γ → Prop)) =
{R | ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (rexp P Q)} :=
rfl` (`P exp Q` is a relation on `Set (α → β → Prop)`, the natural actual type; any `γ` into
which that type injects is adequate). -/
def nrExp {α : Type u} {β : Type v} {γ : Type w} (μ : Set (α → α → Prop))
    (ν : Set (β → β → Prop)) : Set (γ → γ → Prop) :=
  {R | ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (rexp P Q)}

/-!
**✱186·02 Df.** \((\text{Nr}ʻP)\,\text{exp}\,\,_{r}\nu =(\text{N}_{0}\text{r}ʻP)\,\text{exp}\,\,_{r}\nu \quad\text{Df}\)

**✱186·03 Df.** \(\mu \,\text{exp}\,\,_{r}(\text{Nr}ʻQ)=\mu \,\text{exp}\,\,_{r}(\text{N}_{0}\text{r}ʻQ) \quad\text{Df}\)

Translation rules, as ✱180·03·031. Targets (status `definition`):
`pm186_02 : (nrExp (n₀r P) ν : Set (γ → γ → Prop)) = nrExp (n₀r P) ν := rfl`;
`pm186_03 : (nrExp μ (n₀r Q) : Set (γ → γ → Prop)) = nrExp μ (n₀r Q) := rfl`.
-/

/-! ## Adequate actual types for relation-numbers (Prefatory Statement, II; Summary of Section A)

"The conventions IT, IIT and AT apply to relation-numbers as to cardinals" (Summary of Section A).
PM gives no further definition; as in Defs/Part3, a type is adequate for a formal relation-number
when the formal number, with every argument replaced by the greatest relation of its type
(`t₀'C'P ↑ t₀'C'P`, i.e. `V̇`, ✱154·121), exists in that type (for `ΠNr`, the greatest relation
of *existent* relations, see `AdeqPiNr`). These are this formalization's analogue of the
Prefatory Statement's (i)–(ii), not PM definitions. `AdeqNr W P` holds iff the type `α` of `C'P`
injects into `W` (`adeqNr_iff`); in general existence in a type depends only on the cardinal of
the field (`nr_nonempty_iff`, ✱154·14). In an adequate type the formal number exists for every
value of its argument (`AdeqNr.nr_nonempty`, `AdeqSigmaNr.sigmaNr_nonempty`,
`AdeqPiNr.piNr_nonempty`). As in Defs/Part3, adequacy depends only on the types of the
arguments; for an argument that is an apparent variable pass any term of its type. A constant
formal number such as `2_r` in an arithmetical position is adequate in `W` when it exists there
(Prefatory Statement (iii)): `(two_r : Set (W → W → Prop)).Nonempty`. -/

/-- The type `γ` is adequate for `Nr'P` (`∃!Nr't₀'C'P ↑ t₀'C'P`). -/
def AdeqNr (γ : Type w) (P : α → α → Prop) : Prop :=
  (nr γ (cross (typ₀ (fld P)) (typ₀ (fld P)))).Nonempty

/-- The type `γ` is adequate for `μ +̇ ν` (`∃!N₀r'V̇ +̇ N₀r'V̇`, with `V̇` of the types of the
members of `μ`, `ν`). -/
def AdeqNrAdd (γ : Type w) (_μ : Set (α → α → Prop)) (_ν : Set (β → β → Prop)) : Prop :=
  (n₀r (rV : α → α → Prop) ∔ n₀r (rV : β → β → Prop) : Set (γ → γ → Prop)).Nonempty

/-- The type `γ` is adequate for `μ ×̇ ν`. -/
def AdeqNrMul (γ : Type w) (_μ : Set (α → α → Prop)) (_ν : Set (β → β → Prop)) : Prop :=
  (n₀r (rV : α → α → Prop) ⨰ n₀r (rV : β → β → Prop) : Set (γ → γ → Prop)).Nonempty

/-- The type `γ` is adequate for `μ exp_r ν`. -/
def AdeqNrExp (γ : Type w) (_μ : Set (α → α → Prop)) (_ν : Set (β → β → Prop)) : Prop :=
  (nrExp (n₀r (rV : α → α → Prop)) (n₀r (rV : β → β → Prop)) : Set (γ → γ → Prop)).Nonempty

/-- The type `γ` is adequate for `ΣNr'P` (`∃!ΣNr'V̇`, `V̇` the greatest relation of relations of the
type of `P`). -/
def AdeqSigmaNr (γ : Type w) (_P : (α → α → Prop) → (α → α → Prop) → Prop) : Prop :=
  (sigmaNr γ (rV : (α → α → Prop) → (α → α → Prop) → Prop)).Nonempty

/-- The type `γ` is adequate for `ΠNr'P`: `∃!ΠNr'(Rl ex'V̇ ↑ Rl ex'V̇)`, the greatest relation
between the *existent* relations of the type of the members of `C'P`. (`∃!ΠNr'V̇` would be
vacuous: `Λ̇ ∈ C'V̇`, so `Π'V̇ = Λ̇` by ✱172·14 and `Nr'Λ̇` exists in every type; the same flaw
affects PM's literal "`∃!ΠNc't₀'κ`" for cardinals, since `Λ ∈ t₀'κ`.) With this reading an
adequate type gives `(P) . ∃!ΠNr'P` (`AdeqPiNr.piNr_nonempty`), as PM requires of adequacy. -/
def AdeqPiNr (γ : Type w) (_P : (α → α → Prop) → (α → α → Prop) → Prop) : Prop :=
  (piNr γ (cross (rlEx rV) (rlEx rV) : (α → α → Prop) → (α → α → Prop) → Prop)).Nonempty

/-- The type `γ` is adequate for `μ +̇ 1̇` (with `x` of type `β`, ✱181·02): `∃!N₀r'V̇ +̇ 1̇`. -/
def AdeqNrAddOne (γ : Type w) (β : Type v) (_μ : Set (α → α → Prop)) : Prop :=
  (nrAddOne β (n₀r (rV : α → α → Prop)) : Set (γ → γ → Prop)).Nonempty

/-- The type `γ` is adequate for `1̇ +̇ μ` (with `x` of type `β`, ✱181·021): `∃!1̇ +̇ N₀r'V̇`. -/
def AdeqNrOneAdd (γ : Type w) (β : Type v) (_μ : Set (α → α → Prop)) : Prop :=
  (nrOneAdd β (n₀r (rV : α → α → Prop)) : Set (γ → γ → Prop)).Nonempty

/-! ## Sanity lemmas: the encodings behave -/

section Sanity

/-! ### `S;Q` -/

/-- `x(S;Q)y . ≡ . (∃z,w) . xSz . ySw . zQw` (✱150·11). -/
theorem semi_apply (S : α → β → Prop) (Q : β → β → Prop) (x y : α) :
    (S ⁏ Q) x y ↔ ∃ z w, (S x z ∧ S y w) ∧ Q z w := by
  constructor
  · rintro ⟨w, ⟨z, hxz, hzw⟩, hyw⟩
    exact ⟨z, w, ⟨hxz, hyw⟩, hzw⟩
  · rintro ⟨z, w, ⟨hxz, hyw⟩, hzw⟩
    exact ⟨w, ⟨z, hxz, hzw⟩, hyw⟩

/-- For a relation with a total descriptive function (`graph f`): `x(S;Q)y` iff
`x = S'z . y = S'w . zQw` (✱150·4). -/
theorem semi_graph_apply (f : β → α) (Q : β → β → Prop) (x y : α) :
    (graph f ⁏ Q) x y ↔ ∃ z w, (x = f z ∧ y = f w) ∧ Q z w :=
  semi_apply _ _ _ _

theorem mem_img_graph {f : β → α} {B : Set β} {x : α} : x ∈ graph f ʻʻ B ↔ ∃ y, y ∈ B ∧ x = f y :=
  Iff.rfl

/-- `C'(S;Q) = S''C'Q` for `S = graph f` (✱150·22). -/
theorem fld_semi_graph (f : β → α) (Q : β → β → Prop) : fld (graph f ⁏ Q) = graph f ʻʻ fld Q := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · obtain ⟨z, w, ⟨hx, -⟩, hzw⟩ := (semi_graph_apply f Q x y).1 h
      exact ⟨z, ⟨w, Or.inl hzw⟩, hx⟩
    · obtain ⟨z, w, ⟨-, hx⟩, hzw⟩ := (semi_graph_apply f Q y x).1 h
      exact ⟨w, ⟨z, Or.inr hzw⟩, hx⟩
  · rintro ⟨z, ⟨w, hzw | hwz⟩, rfl⟩
    · exact ⟨f w, Or.inl ((semi_graph_apply f Q _ _).2 ⟨z, w, ⟨rfl, rfl⟩, hzw⟩)⟩
    · exact ⟨f w, Or.inr ((semi_graph_apply f Q _ _).2 ⟨w, z, ⟨rfl, rfl⟩, hwz⟩)⟩

/-- `R;S;Q = (R | S);Q` (✱150·13). -/
theorem semi_semi (R : α → β → Prop) (S : β → γ → Prop) (Q : γ → γ → Prop) :
    R ⁏ S ⁏ Q = (R ⨾ S) ⁏ Q := by
  funext x y
  apply propext
  rw [semi_apply, semi_apply]
  constructor
  · rintro ⟨z, w, ⟨hxz, hyw⟩, h⟩
    obtain ⟨z', w', ⟨hzz', hww'⟩, h'⟩ := (semi_apply S Q z w).1 h
    exact ⟨z', w', ⟨⟨z, hxz, hzz'⟩, ⟨w, hyw, hww'⟩⟩, h'⟩
  · rintro ⟨z', w', ⟨⟨z, hxz, hzz'⟩, ⟨w, hyw, hww'⟩⟩, h'⟩
    exact ⟨z, w, ⟨hxz, hyw⟩, (semi_apply S Q z w).2 ⟨z', w', ⟨hzz', hww'⟩, h'⟩⟩

/-- `Cnv'S;Q = S;Q̆` (✱150·12). -/
theorem cnv_semi (S : α → β → Prop) (Q : β → β → Prop) : (S ⁏ Q)˘ = S ⁏ Q˘ := by
  funext x y
  apply propext
  show (S ⁏ Q) y x ↔ (S ⁏ Q˘) x y
  rw [semi_apply, semi_apply]
  constructor
  · rintro ⟨z, w, ⟨h1, h2⟩, h⟩
    exact ⟨w, z, ⟨h2, h1⟩, h⟩
  · rintro ⟨z, w, ⟨h1, h2⟩, h⟩
    exact ⟨w, z, ⟨h2, h1⟩, h⟩

/-- `S†Q = S;Q` (✱150·1). -/
theorem daggerOp_eq_semi (S : α → β → Prop) (Q : β → β → Prop) : daggerOp S Q = S ⁏ Q := rfl

/-- `S† = S ‖ S̆` (✱150·141); in particular `daggerRel S` is Defs/Part3's `dagger S`. -/
theorem daggerRel_eq_dpar (S : α → β → Prop) : daggerRel S = S ∥ S˘ := by
  funext X Q
  apply propext
  rw [dpar_iff]
  show X = S ⨾ Q ⨾ S˘ ↔ X = S ⨾ (Q ⨾ S˘)
  have : S ⨾ Q ⨾ S˘ = S ⨾ (Q ⨾ S˘) := by
    funext x y
    apply propext
    constructor
    · rintro ⟨w, ⟨z, h1, h2⟩, h3⟩
      exact ⟨z, h1, w, h2, h3⟩
    · rintro ⟨z, h1, w, h2, h3⟩
      exact ⟨w, ⟨z, h1, h2⟩, h3⟩
  rw [this]

theorem daggerRel_eq_dagger (S : α → β → Prop) : daggerRel S = dagger S := daggerRel_eq_dpar S

/-- `(P↓.,y)` relates `x ↓ y` to `x' ↓ y` when `xPx'` (✱150·61, ✱165·11). -/
theorem opSemi_couple_apply (P : α → α → Prop) (y : β) (X X' : α → β → Prop) :
    opSemi couple P y X X' ↔ ∃ x x', (X = x ↓ y ∧ X' = x' ↓ y) ∧ P x x' :=
  semi_graph_apply _ _ _ _

/-- `C'(P↓.,y) = ↓y''C'P`. -/
theorem fld_opSemi_couple (P : α → α → Prop) (y : β) :
    fld (opSemi couple P y) = {X | ∃ x, x ∈ fld P ∧ X = x ↓ y} :=
  fld_semi_graph _ _

/-- `R(P↓.,;Q)S . ≡ . (∃z,w) . zQw . R = ↓z;P . S = ↓w;P` (✱165·1). -/
theorem coupleSemi_semi_apply (P : α → α → Prop) (Q : β → β → Prop)
    (X Y : (α → β → Prop) → (α → β → Prop) → Prop) :
    (coupleSemi P ⁏ Q) X Y ↔ ∃ z w, (X = opSemi couple P z ∧ Y = opSemi couple P w) ∧ Q z w :=
  semi_graph_apply _ _ _ _

/-- `C'P↓.,;Q = P↓.,''C'Q` (✱165·12). -/
theorem fld_coupleSemi_semi (P : α → α → Prop) (Q : β → β → Prop) :
    fld (coupleSemi P ⁏ Q) = {X | ∃ z, z ∈ fld Q ∧ X = opSemi couple P z} :=
  fld_semi_graph _ _

/-! ### Likeness -/

/-- `P smor Q . ≡ . (∃S) . S ∈ 1 → 1 . C'Q = ᗡ'S . P = S;Q` (✱151·1). -/
theorem smor_iff {P : α → α → Prop} {Q : β → β → Prop} :
    smor P Q ↔ ∃ S : α → β → Prop, (S ∈ arrow one one ∧ fld Q = codom S) ∧ P = S ⁏ Q := Iff.rfl

/-- Likeness is the existence of a bijection between the fields that carries `P` to `Q`
(cf. ✱151·29). -/
theorem smor_iff_exists_equiv {P : α → α → Prop} {Q : β → β → Prop} :
    smor P Q ↔ ∃ e : fld P ≃ fld Q, ∀ a b : fld P, P a b ↔ Q (e a) (e b) := by
  constructor
  · rintro ⟨S, ⟨hS, hcod⟩, rfl⟩
    obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS
    have hcodQ : ∀ x z, S x z → z ∈ fld Q := fun x z h => by rw [hcod]; exact ⟨x, h⟩
    have hdom : ∀ x, x ∈ fld (S ⁏ Q) → ∃ z, S x z := by
      rintro x ⟨y, h | h⟩
      · obtain ⟨z, w, ⟨hxz, -⟩, -⟩ := (semi_apply S Q x y).1 h
        exact ⟨z, hxz⟩
      · obtain ⟨z, w, ⟨-, hxw⟩, -⟩ := (semi_apply S Q y x).1 h
        exact ⟨w, hxw⟩
    have hfld : ∀ x w, S x w → x ∈ fld (S ⁏ Q) := by
      intro x w hxw
      obtain ⟨v, hwv | hvw⟩ := hcodQ x w hxw
      · have : v ∈ codom S := by rw [← hcod]; exact ⟨w, Or.inr hwv⟩
        obtain ⟨y, hyv⟩ := this
        exact ⟨y, Or.inl ((semi_apply S Q x y).2 ⟨w, v, ⟨hxw, hyv⟩, hwv⟩)⟩
      · have : v ∈ codom S := by rw [← hcod]; exact ⟨w, Or.inl hvw⟩
        obtain ⟨y, hyv⟩ := this
        exact ⟨y, Or.inr ((semi_apply S Q y x).2 ⟨v, w, ⟨hyv, hxw⟩, hvw⟩)⟩
    choose g hg using fun a : fld (S ⁏ Q) => hdom a a.2
    have huniq : ∀ (a : fld (S ⁏ Q)) z, S a z → z = g a := fun a z h => h2 a z (g a) ⟨h, hg a⟩
    refine ⟨Equiv.ofBijective (fun a => ⟨g a, hcodQ a (g a) (hg a)⟩) ⟨?_, ?_⟩, ?_⟩
    · intro a b hab
      have e : g a = g b := congrArg Subtype.val hab
      apply Subtype.ext
      exact h1 a b (g a) ⟨hg a, e ▸ hg b⟩
    · rintro ⟨w, hw⟩
      have : w ∈ codom S := by rw [← hcod]; exact hw
      obtain ⟨x, hxw⟩ := this
      exact ⟨⟨x, hfld x w hxw⟩, Subtype.ext (huniq ⟨x, hfld x w hxw⟩ w hxw).symm⟩
    · intro a b
      show (S ⁏ Q) a b ↔ Q (g a) (g b)
      rw [semi_apply]
      constructor
      · rintro ⟨z, w, ⟨haz, hbw⟩, hzw⟩
        rw [huniq a z haz, huniq b w hbw] at hzw
        exact hzw
      · intro h
        exact ⟨g a, g b, ⟨hg a, hg b⟩, h⟩
  · rintro ⟨e, he⟩
    refine ⟨fun x z => ∃ h : x ∈ fld P, (e ⟨x, h⟩ : β) = z, ⟨?_, ?_⟩, ?_⟩
    · refine mem_arrow_one_one.2 ⟨?_, ?_⟩
      · rintro x y z ⟨⟨hx, hxz⟩, ⟨hy, hyz⟩⟩
        have : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext (hxz.trans hyz.symm)
        exact congrArg Subtype.val (e.injective this)
      · rintro x y z ⟨⟨hx, hxy⟩, ⟨hx', hxz⟩⟩
        exact hxy.symm.trans hxz
    · ext w
      constructor
      · intro hw
        exact ⟨(e.symm ⟨w, hw⟩ : α), (e.symm ⟨w, hw⟩).2, by simp⟩
      · rintro ⟨x, hx, rfl⟩
        exact (e ⟨x, hx⟩).2
    · funext x y
      apply propext
      rw [semi_apply]
      constructor
      · intro h
        have hx : x ∈ fld P := ⟨y, Or.inl h⟩
        have hy : y ∈ fld P := ⟨x, Or.inr h⟩
        exact ⟨e ⟨x, hx⟩, e ⟨y, hy⟩, ⟨⟨hx, rfl⟩, ⟨hy, rfl⟩⟩, (he ⟨x, hx⟩ ⟨y, hy⟩).1 h⟩
      · rintro ⟨z, w, ⟨⟨hx, rfl⟩, ⟨hy, rfl⟩⟩, hzw⟩
        exact (he ⟨x, hx⟩ ⟨y, hy⟩).2 hzw

/-- Likeness is reflexive (✱151·13). -/
theorem smor_refl (P : α → α → Prop) : smor P P :=
  smor_iff_exists_equiv.2 ⟨Equiv.refl _, fun _ _ => Iff.rfl⟩

/-- Likeness is symmetrical (✱151·14). -/
theorem smor_symm {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q) : smor Q P := by
  obtain ⟨e, he⟩ := smor_iff_exists_equiv.1 h
  refine smor_iff_exists_equiv.2 ⟨e.symm, fun a b => ?_⟩
  have := he (e.symm a) (e.symm b)
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

/-- Likeness is transitive (✱151·15). -/
theorem smor_trans {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop} (h₁ : smor P Q)
    (h₂ : smor Q R) : smor P R := by
  obtain ⟨e, he⟩ := smor_iff_exists_equiv.1 h₁
  obtain ⟨e', he'⟩ := smor_iff_exists_equiv.1 h₂
  exact smor_iff_exists_equiv.2 ⟨e.trans e', fun a b => (he a b).trans (he' (e a) (e b))⟩

/-- Like relations have similar fields (✱151·18). -/
theorem sm_fld_of_smor {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q) :
    sm (fld P) (fld Q) := by
  obtain ⟨e, -⟩ := smor_iff_exists_equiv.1 h
  exact sm_iff_nonempty_equiv.2 ⟨e⟩

/-! ### `Nr'P`, `NR`, `N₀r'P` -/

/-- `Q ∈ Nr'P . ≡ . Q smor P` (✱152·11). -/
theorem mem_nr {P : β → β → Prop} {Q : γ → γ → Prop} : Q ∈ nr γ P ↔ smor Q P := Iff.rfl

/-- `ψ(Nr'P) ↔ ψ(nr γ P)`: `E!Nr'P` (✱152·2). -/
theorem desc_Nr (P : β → β → Prop) (ψ : Set (γ → γ → Prop) → Prop) :
    Desc (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) P ψ ↔ ψ (nr γ P) := desc_graph _ _ _

theorem EDesc_Nr (P : β → β → Prop) : EDesc (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) P :=
  EDesc_graph _ _

/-- The typically definite `Nr(X)'P` (✱65·04, `t²'X ↿ Nr`) is `nr γ P`. -/
theorem desc_relT2_Nr (X : γ → γ → Prop) (P : β → β → Prop) (ψ : Set (γ → γ → Prop) → Prop) :
    Desc (relT2 (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) X) P ψ ↔ ψ (nr γ P) := by
  have h : relT2 (Nr : Set (γ → γ → Prop) → (β → β → Prop) → Prop) X = Nr := by
    funext K Q
    simp [relT2, dres, typ2, typ_eq_univ]
  rw [h]
  exact desc_Nr P ψ

/-- `P ∈ Nr'P` (✱152·3). -/
theorem self_mem_nr (P : α → α → Prop) : P ∈ nr α P := smor_refl P

/-- `P smor Q . ⊃ . Nr'P = Nr'Q` (✱152·321), in any type. -/
theorem nr_eq_nr_of_smor {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q) :
    nr γ P = nr γ Q := by
  ext R
  exact ⟨fun hR => smor_trans hR h, fun hR => smor_trans hR (smor_symm h)⟩

/-- When `Nr'P` exists in `γ`, `Nr'P = Nr'Q` in `γ` iff `P smor Q` (cf. ✱152·35). -/
theorem nr_eq_nr_iff {P : α → α → Prop} {Q : β → β → Prop} (h : (nr γ P).Nonempty) :
    nr γ P = nr γ Q ↔ smor P Q := by
  refine ⟨fun e => ?_, nr_eq_nr_of_smor⟩
  obtain ⟨R, hR⟩ := h
  have hR' : R ∈ nr γ Q := by rw [← e]; exact hR
  exact smor_trans (smor_symm hR) hR'

/-- `∃!Nr(γ)'P` iff the field of `P` injects into `γ` (cf. ✱154·14
`∃!Nr(P)'Q . ≡ . ∃!Nc(C'P)'C'Q`). -/
theorem nr_nonempty_iff {P : β → β → Prop} :
    (nr γ P).Nonempty ↔ ∃ f : fld P → γ, Function.Injective f := by
  constructor
  · rintro ⟨R, hR⟩
    obtain ⟨e, -⟩ := smor_iff_exists_equiv.1 hR
    exact ⟨fun p => (e.symm p : γ), Subtype.val_injective.comp e.symm.injective⟩
  · rintro ⟨f, hf⟩
    let R : γ → γ → Prop := fun a b => ∃ x y : fld P, (f x = a ∧ f y = b) ∧ P x y
    have hfld : fld R = Set.range f := by
      ext a
      constructor
      · rintro ⟨b, ⟨x, y, ⟨rfl, -⟩, -⟩ | ⟨x, y, ⟨-, rfl⟩, -⟩⟩
        · exact ⟨x, rfl⟩
        · exact ⟨y, rfl⟩
      · rintro ⟨⟨x, ⟨y, hxy | hyx⟩⟩, rfl⟩
        · exact ⟨f ⟨y, ⟨x, Or.inr hxy⟩⟩, Or.inl ⟨_, _, ⟨rfl, rfl⟩, hxy⟩⟩
        · exact ⟨f ⟨y, ⟨x, Or.inl hyx⟩⟩, Or.inr ⟨_, _, ⟨rfl, rfl⟩, hyx⟩⟩
    let e : fld R ≃ fld P := (Set.equivOfEq hfld).trans (Equiv.ofInjective f hf).symm
    have he : ∀ (x : fld P) (h : f x ∈ fld R), e ⟨f x, h⟩ = x := by
      intro x h
      apply (Equiv.ofInjective f hf).injective
      apply Subtype.ext
      simp [e]
    refine ⟨R, smor_iff_exists_equiv.2 ⟨e, ?_⟩⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : a ∈ Set.range f := hfld ▸ ha
    have hb' : b ∈ Set.range f := hfld ▸ hb
    obtain ⟨x, rfl⟩ := ha'
    obtain ⟨y, rfl⟩ := hb'
    rw [he x ha, he y hb]
    constructor
    · rintro ⟨x', y', ⟨h1, h2⟩, h⟩
      rw [← hf h1, ← hf h2]
      exact h
    · intro h
      exact ⟨x, y, ⟨rfl, rfl⟩, h⟩

/-- `μ ∈ NR . ≡ . (∃P) . μ = Nr'P` (✱152·4), with the type of `P` explicit. -/
theorem mem_NR {μ : Set (γ → γ → Prop)} : μ ∈ NR β ↔ ∃ P : β → β → Prop, μ = nr γ P := Iff.rfl

theorem nr_mem_NR (P : β → β → Prop) : nr γ P ∈ NR β := ⟨P, rfl⟩

/-- `NR^Y(X)` is `NR` with the types of `X` and `Y`. -/
theorem NRT_eq_NR (X : γ → γ → Prop) (Y : β → β → Prop) : NRT X Y = NR β := by
  ext μ
  simp [NRT, NR, relT2T, dres, cres, dom, typ2, typ_eq_univ]

theorem n₀r_eq_nr (P : α → α → Prop) : n₀r P = nr α P := by
  rw [n₀r, typ_eq_univ, Set.inter_univ]

/-- `Q ∈ N₀r'P . ≡ . Q smor P` (✱155·11; `Q ∈ t'P` is automatic). -/
theorem mem_n₀r {P Q : α → α → Prop} : Q ∈ n₀r P ↔ smor Q P := by
  rw [n₀r_eq_nr]; exact Iff.rfl

/-- `P ∈ N₀r'P` (✱155·12). -/
theorem self_mem_n₀r (P : α → α → Prop) : P ∈ n₀r P := mem_n₀r.2 (smor_refl P)

/-- `∃!N₀r'P` (✱155·13). -/
theorem n₀r_nonempty (P : α → α → Prop) : (n₀r P).Nonempty := ⟨P, self_mem_n₀r P⟩

theorem n₀r_eq_n₀r_iff {P Q : α → α → Prop} : n₀r P = n₀r Q ↔ smor P Q := by
  rw [n₀r_eq_nr, n₀r_eq_nr]
  exact nr_eq_nr_iff ⟨P, self_mem_nr P⟩

theorem desc_N₀r (P : α → α → Prop) (ψ : Set (α → α → Prop) → Prop) :
    Desc N₀r P ψ ↔ ψ (n₀r P) := desc_graph _ _ _

/-- `μ ∈ N₀R . ≡ . (∃P) . μ = N₀r'P` (✱155·2). -/
theorem mem_N₀R {μ : Set (α → α → Prop)} : μ ∈ N₀R ↔ ∃ P, μ = n₀r P := Iff.rfl

theorem mem_one_s {R : α → α → Prop} : R ∈ one_s ↔ ∃ x, R = x ↓ x := Iff.rfl

/-! ### Adequacy -/

private theorem fld_cross_univ : fld (cross (Set.univ : Set α) (Set.univ : Set α)) = Set.univ :=
  Set.eq_univ_of_forall fun x => ⟨x, Or.inl ⟨trivial, trivial⟩⟩

/-- `γ` is adequate for `Nr'P` iff the type of `C'P` injects into `γ`. -/
theorem adeqNr_iff {P : α → α → Prop} : AdeqNr γ P ↔ ∃ f : α → γ, Function.Injective f := by
  rw [AdeqNr, nr_nonempty_iff, typ₀_eq_univ, fld_cross_univ]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨fun x => f ⟨x, trivial⟩, fun x y h => congrArg Subtype.val (hf h)⟩
  · rintro ⟨f, hf⟩
    exact ⟨fun x => f x, fun x y h => Subtype.ext (hf h)⟩

/-- `P ⊂̇ Q . ⊃ . C'P ⊂ C'Q`. -/
theorem fld_mono {P Q : α → α → Prop} (h : P ⪽ Q) : fld P ⊆ fld Q := by
  rintro x ⟨y, hxy | hyx⟩
  · exact ⟨y, Or.inl (h _ _ hxy)⟩
  · exact ⟨y, Or.inr (h _ _ hyx)⟩

/-- `Q ⊂̇ Q' . ⊃ . S;Q ⊂̇ S;Q'` (cf. ✱150·31). -/
theorem semi_mono (S : α → β → Prop) {Q Q' : β → β → Prop} (h : Q ⪽ Q') : S ⁏ Q ⪽ S ⁏ Q' := by
  intro x y hxy
  obtain ⟨z, w, hzw, hq⟩ := (semi_apply S Q x y).1 hxy
  exact (semi_apply S Q' x y).2 ⟨z, w, hzw, h _ _ hq⟩

/-- `P ⊂̇ P' . ⊃ . Σ'P ⊂̇ Σ'P'`. -/
theorem relSigma_mono {P P' : (α → α → Prop) → (α → α → Prop) → Prop} (h : P ⪽ P') :
    relSigma P ⪽ relSigma P' := by
  intro x y hxy
  rcases hxy with ⟨R, hR, hR'⟩ | hF
  · exact Or.inl ⟨R, fld_mono h hR, hR'⟩
  · exact Or.inr (semi_mono F h _ _ hF)

/-- `Nr(γ)'P` exists whenever `Nr(γ)'Q` does and `P ⊂̇ Q`. -/
theorem nr_nonempty_of_rsub {P Q : α → α → Prop} (hQ : (nr γ Q).Nonempty) (h : P ⪽ Q) :
    (nr γ P).Nonempty := by
  obtain ⟨f, hf⟩ := nr_nonempty_iff.1 hQ
  exact nr_nonempty_iff.2 ⟨fun p => f ⟨p.1, fld_mono h p.2⟩,
    fun p q e => by
      have h2 := hf e
      simp only [Subtype.mk.injEq] at h2
      exact Subtype.ext h2⟩

/-- In a type adequate for `Nr'P'`, `Nr'P` exists for every `P` of the type of `P'`. -/
theorem AdeqNr.nr_nonempty {P' : α → α → Prop} (h : AdeqNr γ P') (P : α → α → Prop) :
    (nr γ P).Nonempty :=
  nr_nonempty_of_rsub h fun x y _ => ⟨by rw [typ₀_eq_univ]; trivial, by rw [typ₀_eq_univ]; trivial⟩

/-- In a type adequate for `ΣNr'P'`, `ΣNr'P` exists for every `P` of the type of `P'`. -/
theorem AdeqSigmaNr.sigmaNr_nonempty {P' : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : AdeqSigmaNr γ P') (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    (sigmaNr γ P).Nonempty :=
  nr_nonempty_of_rsub h (relSigma_mono (semi_mono _ fun _ _ _ => ⟨rfl, rfl⟩))

private theorem mem_fld_of_sel {M : α → (α → α → Prop) → Prop} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    (hM : M ∈ sel F (fld P)) {x : α} {Q : α → α → Prop} (h : M x Q) : Q ∈ fld P := by
  rw [← (mem_sel_iff.1 hM).2]; exact ⟨x, h⟩

/-- In a type adequate for `ΠNr'P'`, `ΠNr'P` exists for every `P` of the type of `P'`
(`Π'P` is like a relation of selections from the existent relations, which extend those from
`C'P`). -/
theorem AdeqPiNr.piNr_nonempty {P' : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : AdeqPiNr γ P') (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    (piNr γ P).Nonempty := by
  set V : (α → α → Prop) → (α → α → Prop) → Prop := cross (rlEx rV) (rlEx rV) with hV
  obtain ⟨f, hf⟩ := nr_nonempty_iff.1 h
  apply nr_nonempty_iff.2
  rcases isEmpty_or_nonempty (fld (relPi P)) with hE | ⟨⟨M₀, hM₀⟩⟩
  · exact ⟨fun p => isEmptyElim p, fun p => isEmptyElim p⟩
  -- a selection exists, so every member of `C'P` is existent and `α` is inhabited
  have hsel : ∀ M, M ∈ fld (relPi P) → M ∈ sel F (fld P) := by
    rintro M ⟨N, ⟨⟨hM, -⟩, -⟩ | ⟨⟨-, hM⟩, -⟩⟩ <;> exact hM
  have hM₀s := hsel M₀ hM₀
  have hex : ∀ Q, Q ∈ fld P → ∃ x, x ∈ fld Q := by
    intro Q hQ
    rw [← (mem_sel_iff.1 hM₀s).2] at hQ
    obtain ⟨x, hx⟩ := hQ
    exact ⟨x, (mem_sel_iff.1 hM₀s).1.2 _ _ hx⟩
  have hne : Nonempty α := by
    obtain ⟨N, hN | hN⟩ := hM₀
    · obtain ⟨-, Q, ⟨x, -⟩, -⟩ := hN; exact ⟨x⟩
    · obtain ⟨-, Q, ⟨x, -⟩, -⟩ := hN; exact ⟨x⟩
  obtain ⟨a⟩ := hne
  have : Nonempty α := ⟨a⟩
  -- extend a selection `M` from `C'P` to a selection from all existent relations
  let c : (α → α → Prop) → α := fun Q => Classical.epsilon (· ∈ fld Q)
  have hc : ∀ Q : α → α → Prop, rEx Q → c Q ∈ fld Q := by
    rintro Q ⟨x, y, hxy⟩; exact Classical.epsilon_spec ⟨x, ⟨y, Or.inl hxy⟩⟩
  let ext : (α → (α → α → Prop) → Prop) → α → (α → α → Prop) → Prop := fun M x Q =>
    (Q ∈ fld P ∧ M x Q) ∨ (Q ∉ fld P ∧ rEx Q ∧ x = c Q)
  have rEx_of_fld : ∀ {Q : α → α → Prop} {x}, x ∈ fld Q → rEx Q := by
    rintro Q x ⟨y, h | h⟩
    · exact ⟨x, y, h⟩
    · exact ⟨y, x, h⟩
  have hfldV : fld V = rlEx rV := by
    ext Q
    constructor
    · rintro ⟨R, ⟨h1, -⟩ | ⟨-, h1⟩⟩ <;> exact h1
    · intro hQ; exact ⟨Q, Or.inl ⟨hQ, hQ⟩⟩
  have hext : ∀ M, M ∈ sel F (fld P) → ext M ∈ sel F (fld V) := by
    intro M hM
    obtain ⟨⟨hM1, hM2⟩, hM3⟩ := mem_sel_iff.1 hM
    refine mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩
    · rintro x y Q ⟨(⟨-, hx⟩ | ⟨hQ, -, rfl⟩), (⟨-, hy⟩ | ⟨hQ', -, rfl⟩)⟩
      · exact mem_arrow_one_Cls.1 hM1 x y Q ⟨hx, hy⟩
      · exact absurd (mem_fld_of_sel hM hx) hQ'
      · exact absurd (mem_fld_of_sel hM hy) hQ
      · rfl
    · rintro x Q (⟨-, hx⟩ | ⟨-, hQ, rfl⟩)
      · exact hM2 _ _ hx
      · exact hc Q hQ
    · rw [hfldV]
      ext Q
      constructor
      · rintro ⟨x, ⟨hQ, hx⟩ | ⟨-, hQ, -⟩⟩
        · exact ⟨fun _ _ _ => ⟨rfl, rfl⟩, rEx_of_fld (hM2 _ _ hx)⟩
        · exact ⟨fun _ _ _ => ⟨rfl, rfl⟩, hQ⟩
      · rintro ⟨-, hQ⟩
        by_cases hP : Q ∈ fld P
        · have : Q ∈ codom M := by rw [hM3]; exact hP
          obtain ⟨x, hx⟩ := this
          exact ⟨x, Or.inl ⟨hP, hx⟩⟩
        · exact ⟨c Q, Or.inr ⟨hP, hQ, rfl⟩⟩
  have hextfld : ∀ M, M ∈ sel F (fld P) → ext M ∈ fld (relPi V) := by
    intro M hM
    have hs := hext M hM
    have hfun : ∀ Q, Q ∈ rlEx rV → ∃ x, ∀ y, ext M y Q ↔ y = x := by
      intro Q hQ
      have : Q ∈ codom (ext M) := by rw [(mem_sel_iff.1 hs).2, hfldV]; exact hQ
      obtain ⟨x, hx⟩ := this
      exact ⟨x, fun y => ⟨fun hy => mem_arrow_one_Cls.1 (mem_sel_iff.1 hs).1.1 y x Q ⟨hy, hx⟩,
        fun e => e ▸ hx⟩⟩
    have haa : (a ↓ a : α → α → Prop) ∈ rlEx rV := ⟨fun _ _ _ => ⟨rfl, rfl⟩, a, a, rfl, rfl⟩
    refine ⟨ext M, Or.inl ⟨⟨hs, hs⟩, a ↓ a, ?_, ?_⟩⟩
    · obtain ⟨x, hx⟩ := hfun _ haa
      have hxa : x = a := by
        have := (mem_sel_iff.1 hs).1.2 x _ ((hx x).2 rfl)
        obtain ⟨y, ⟨h1, -⟩ | ⟨-, h1⟩⟩ := this <;> exact h1
      subst hxa
      exact ⟨x, hx, x, hx, rfl, rfl⟩
    · rintro R ⟨⟨hR, -⟩, -⟩
      obtain ⟨x, hx⟩ := hfun R hR
      exact ⟨x, hx, x, hx, rfl⟩
  have hinj : ∀ M M', M ∈ sel F (fld P) → M' ∈ sel F (fld P) → ext M = ext M' → M = M' := by
    intro M M' hM hM' e
    funext x Q
    apply propext
    have key : ∀ N, N ∈ sel F (fld P) → (N x Q ↔ Q ∈ fld P ∧ ext N x Q) := by
      intro N hN
      constructor
      · intro hx; exact ⟨mem_fld_of_sel hN hx, Or.inl ⟨mem_fld_of_sel hN hx, hx⟩⟩
      · rintro ⟨hQ, ⟨-, hx⟩ | ⟨hQ', -⟩⟩
        · exact hx
        · exact absurd hQ hQ'
    rw [key M hM, key M' hM', e]
  refine ⟨fun p => f ⟨ext p.1, hextfld p.1 (hsel p.1 p.2)⟩, ?_⟩
  intro p q hpq
  have := congrArg Subtype.val (hf hpq)
  exact Subtype.ext (hinj p.1 q.1 (hsel p.1 p.2) (hsel q.1 q.2) this)

/-! ### Sums and products of relations -/

/-- `x(P ⤉ Q)y . ≡ : xPy . ∨ . xQy . ∨ . x ∈ C'P . y ∈ C'Q` (✱160·11). -/
theorem rsum_apply (P Q : α → α → Prop) (x y : α) :
    (P ⤉ Q) x y ↔ (P x y ∨ Q x y) ∨ x ∈ fld P ∧ y ∈ fld Q := Iff.rfl

/-- `C'(P ⤉ Q) = C'P ∪ C'Q` (✱160·14). -/
theorem fld_rsum (P Q : α → α → Prop) : fld (P ⤉ Q) = fld P ∪ fld Q := by
  ext x
  constructor
  · rintro ⟨y, ((h | h) | ⟨h, -⟩) | ((h | h) | ⟨-, h⟩)⟩
    · exact Or.inl ⟨y, Or.inl h⟩
    · exact Or.inr ⟨y, Or.inl h⟩
    · exact Or.inl h
    · exact Or.inl ⟨y, Or.inr h⟩
    · exact Or.inr ⟨y, Or.inr h⟩
    · exact Or.inr h
  · rintro (⟨y, h | h⟩ | ⟨y, h | h⟩)
    · exact ⟨y, Or.inl (Or.inl (Or.inl h))⟩
    · exact ⟨y, Or.inr (Or.inl (Or.inl h))⟩
    · exact ⟨y, Or.inl (Or.inl (Or.inr h))⟩
    · exact ⟨y, Or.inr (Or.inl (Or.inr h))⟩

/-- `y(P ⇸ x)z . ≡ : yPz . ∨ . y ∈ C'P . z = x` (✱161·11). -/
theorem addLast_apply (P : α → α → Prop) (x y z : α) :
    (P ⇸ x) y z ↔ P y z ∨ y ∈ fld P ∧ z = x := Iff.rfl

theorem addFirst_apply (x : α) (P : α → α → Prop) (y z : α) :
    (x ⇷ P) y z ↔ (y = x ∧ z ∈ fld P) ∨ P y z := Iff.rfl

/-- `x(Σ'P)y . ≡ : (∃Q) . Q ∈ C'P . xQy . ∨ . (∃Q,R) . xFQ . yFR . QPR` (✱162·12; `xFQ` is
`x ∈ C'Q`). -/
theorem relSigma_apply (P : (α → α → Prop) → (α → α → Prop) → Prop) (x y : α) :
    relSigma P x y ↔
      (∃ Q, Q ∈ fld P ∧ Q x y) ∨ ∃ Q R, (x ∈ fld Q ∧ y ∈ fld R) ∧ P Q R :=
  or_congr Iff.rfl (semi_apply F P x y)

theorem mem_Rel2excl {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ↔ ∀ Q R, (Q ∈ fld P ∧ R ∈ fld P) ∧ Q ≠ R → fld Q ∩ fld R = Λ := Iff.rfl

/-- `M(Q × P)N . ≡ : (∃x,y,z,w) : x,y ∈ C'P . z,w ∈ C'Q : zQw . ∨ . z = w . xPy :
M = x↓z . N = y↓w` (✱166·11), in the form: either `M`, `N` are in one block `P↓.,z`
(`z ∈ C'Q`), or in the blocks of `z`, `w` with `zQw`. -/
theorem rtimes_apply (Q : β → β → Prop) (P : α → α → Prop) (u v : α → β → Prop) :
    (Q ×ᵣ P) u v ↔
      (∃ z, z ∈ fld Q ∧ ∃ x y, (u = x ↓ z ∧ v = y ↓ z) ∧ P x y) ∨
      ∃ z w, Q z w ∧ ∃ x y, (x ∈ fld P ∧ y ∈ fld P) ∧ u = x ↓ z ∧ v = y ↓ w := by
  show relSigma (coupleSemi P ⁏ Q) u v ↔ _
  rw [relSigma_apply, fld_coupleSemi_semi]
  constructor
  · rintro (⟨R, ⟨z, hz, rfl⟩, hR⟩ | ⟨R, R', ⟨hu, hv⟩, hRR'⟩)
    · exact Or.inl ⟨z, hz, (opSemi_couple_apply P z u v).1 hR⟩
    · obtain ⟨z, w, ⟨rfl, rfl⟩, hzw⟩ := (coupleSemi_semi_apply P Q R R').1 hRR'
      rw [fld_opSemi_couple] at hu hv
      obtain ⟨x, hx, rfl⟩ := hu
      obtain ⟨y, hy, rfl⟩ := hv
      exact Or.inr ⟨z, w, hzw, x, y, ⟨hx, hy⟩, rfl, rfl⟩
  · rintro (⟨z, hz, h⟩ | ⟨z, w, hzw, x, y, ⟨hx, hy⟩, rfl, rfl⟩)
    · exact Or.inl ⟨_, ⟨z, hz, rfl⟩, (opSemi_couple_apply P z u v).2 h⟩
    · refine Or.inr ⟨opSemi couple P z, opSemi couple P w, ⟨?_, ?_⟩,
        (coupleSemi_semi_apply P Q _ _).2 ⟨z, w, ⟨rfl, rfl⟩, hzw⟩⟩
      · rw [fld_opSemi_couple]; exact ⟨x, hx, rfl⟩
      · rw [fld_opSemi_couple]; exact ⟨y, hy, rfl⟩

/-- `C'(P + Q) = C'P + C'Q` (✱180·111): the field of the arithmetical sum of two relations is the
arithmetical sum (✱110·01) of their fields. -/
theorem fld_rplus (P : α → α → Prop) (Q : β → β → Prop) : fld (P +ᵣ Q) = fld P +ₐ fld Q := by
  have h1 : fld (coupleR (Λ ∩ fld Q) ⁏ iota ⁏ P) = coupleR (Λ ∩ fld Q) ʻʻ iota ʻʻ fld P := by
    rw [show coupleR (Λ ∩ fld Q) = graph (fun x : Set α => x ↓ (Λ ∩ fld Q)) from rfl,
      fld_semi_graph, show (iota : Set α → α → Prop) = graph (refs I) from rfl, fld_semi_graph]
  have h2 : fld (coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q) = coupleL (Λ ∩ fld P) ʻʻ iota ʻʻ fld Q := by
    rw [show coupleL (Λ ∩ fld P) = graph (fun y : Set β => (Λ ∩ fld P) ↓ y) from rfl,
      fld_semi_graph, show (iota : Set β → β → Prop) = graph (refs I) from rfl, fld_semi_graph]
  rw [rplus, fld_rsum, h1, h2]
  rfl

/-! ### Descriptive functions of the relations of this Part -/

theorem desc_daggerRel (S : α → β → Prop) (Q : β → β → Prop) (ψ : (α → α → Prop) → Prop) :
    Desc (daggerRel S) Q ψ ↔ ψ (daggerOp S Q) := desc_graph _ _ _

theorem desc_coupleSemi (P : α → α → Prop) (y : β)
    (ψ : ((α → β → Prop) → (α → β → Prop) → Prop) → Prop) :
    Desc (coupleSemi P) y ψ ↔ ψ (opSemi couple P y) := desc_graph _ _ _

theorem desc_RelSigma (P : (α → α → Prop) → (α → α → Prop) → Prop) (ψ : (α → α → Prop) → Prop) :
    Desc RelSigma P ψ ↔ ψ (relSigma P) := desc_graph _ _ _

theorem desc_RelPi (P : (α → α → Prop) → (α → α → Prop) → Prop)
    (ψ : ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) → Prop) :
    Desc RelPi P ψ ↔ ψ (relPi P) := desc_graph _ _ _

theorem desc_ProdR (P : (α → α → Prop) → (α → α → Prop) → Prop)
    (ψ : (Set α → Set α → Prop) → Prop) : Desc ProdR P ψ ↔ ψ (prodR P) := desc_graph _ _ _

theorem desc_sDotRel (L : Set (α → β → Prop)) (ψ : (α → β → Prop) → Prop) :
    Desc sDotRel L ψ ↔ ψ (sumRel L) := desc_graph _ _ _

theorem desc_sRel (K : Set (Set α)) (ψ : Set α → Prop) : Desc sRel K ψ ↔ ψ (sumCls K) :=
  desc_graph _ _ _

theorem desc_dfRel (Q : α → α → Prop) (ψ : (Set α → Set α → Prop) → Prop) :
    Desc dfRel Q ψ ↔ ψ (Pdf Q) := desc_graph _ _ _

theorem desc_opDiag (f : α → α → γ) (x : α) (ψ : γ → Prop) : Desc (opDiag f) x ψ ↔ ψ (f x x) :=
  desc_graph _ _ _

theorem desc_SigmaNr (P : (α → α → Prop) → (α → α → Prop) → Prop) (ψ : Set (γ → γ → Prop) → Prop) :
    Desc (SigmaNr : Set (γ → γ → Prop) → _ → Prop) P ψ ↔ ψ (sigmaNr γ P) := desc_graph _ _ _

theorem desc_PiNr (P : (α → α → Prop) → (α → α → Prop) → Prop) (ψ : Set (γ → γ → Prop) → Prop) :
    Desc (PiNr : Set (γ → γ → Prop) → _ → Prop) P ψ ↔ ψ (piNr γ P) := desc_graph _ _ _

/-- The precedences realize PM's bracketing Dfs ✱150·05, ✱160·32, ✱161·212·213, ✱166·421,
✱180·531, and the unbracketed ✱150·34, ✱150·74, ✱160·44, ✱161·4, ✱162·01, ✱181·01. -/
example (R : δ → α → Prop) (S : α → β → Prop) (Q : β → β → Prop) (P P' : α → α → Prop)
    (x y : α) (T : β → β → Prop) (A B : Set β) (S' : α → β → Prop) :
    (R ⁏ S ⁏ Q = R ⁏ (S ⁏ Q)) ∧ (P ⤉ P' ⤉ P = (P ⤉ P') ⤉ P) ∧ (P ⇸ x ⇸ y = (P ⇸ x) ⇸ y) ∧
    (x ⇷ y ⇷ P = x ⇷ (y ⇷ P)) ∧ (P ×ᵣ T ×ᵣ Q = (P ×ᵣ T) ×ᵣ Q) ∧
    (P +ᵣ T +ᵣ Q = (P +ᵣ T) +ᵣ Q) ∧ (S ⁏ Q ⤉ S ⁏ T = (S ⁏ Q) ⤉ (S ⁏ T)) ∧
    (x ↓ y ⇸ x = (x ↓ y) ⇸ x) ∧ (S ⁏ A ◁ Q ↾ B = S ⁏ (A ◁ Q ↾ B)) ∧
    (S ⁏ Q ⇸ x = (S ⁏ Q) ⇸ x) ∧ (S ⁏ Q ⊍ S' ⁏ Q ⊍ S ⨾ Q ⨾ S'˘ = ((S ⁏ Q) ⊍ (S' ⁏ Q)) ⊍ (S ⨾ Q ⨾ S'˘)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Sanity

end PrincipiaMathematica
