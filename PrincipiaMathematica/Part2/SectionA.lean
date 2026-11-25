import PrincipiaMathematica.Defs.Part2

/-!
# Part II, Section A: Unit classes and couples

Volume 1. Numbers: ✱50, ✱51, ✱52, ✱53, ✱54, ✱55, ✱56.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w u'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

/-! ### Unfolding lemmas

Private `Iff.rfl` lemmas used by the proofs below (made local `simp` lemmas); they only unfold the
definitions of `Defs/Part1` and `Defs/Part2`. -/

section Unfold

private theorem mem_dom' {R : α → β → Prop} {x : α} : x ∈ dom R ↔ ∃ y, R x y := Iff.rfl
private theorem mem_codom' {R : α → β → Prop} {y : β} : y ∈ codom R ↔ ∃ x, R x y := Iff.rfl
private theorem mem_fld' {R : α → α → Prop} {x : α} : x ∈ fld R ↔ ∃ y, R x y ∨ R y x := Iff.rfl
private theorem mem_img' {R : α → β → Prop} {B : Set β} {x : α} :
    x ∈ R ʻʻ B ↔ ∃ y, y ∈ B ∧ R x y := Iff.rfl
private theorem mem_refs' {R : α → β → Prop} {x : α} {y : β} : x ∈ refs R y ↔ R x y := Iff.rfl
private theorem mem_rels' {R : α → β → Prop} {x : α} {y : β} : y ∈ rels R x ↔ R x y := Iff.rfl
private theorem cnv_apply' {R : α → β → Prop} {x : β} {y : α} : R˘ x y ↔ R y x := Iff.rfl
private theorem relProd_apply' {R : α → β → Prop} {S : β → γ → Prop} {x : α} {z : γ} :
    (R ⨾ S) x z ↔ ∃ y, R x y ∧ S y z := Iff.rfl
private theorem rcap_apply' {R S : α → β → Prop} {x : α} {y : β} :
    (R ⩀ S) x y ↔ R x y ∧ S x y := Iff.rfl
private theorem rcup_apply' {R S : α → β → Prop} {x : α} {y : β} :
    (R ⊍ S) x y ↔ R x y ∨ S x y := Iff.rfl
private theorem rdiff_apply' {R S : α → β → Prop} {x : α} {y : β} :
    (R ∸ S) x y ↔ R x y ∧ ¬S x y := Iff.rfl
private theorem dres_apply' {A : Set α} {R : α → β → Prop} {x : α} {y : β} :
    (A ◁ R) x y ↔ x ∈ A ∧ R x y := Iff.rfl
private theorem cres_apply' {R : α → β → Prop} {B : Set β} {x : α} {y : β} :
    (R ↾ B) x y ↔ R x y ∧ y ∈ B := Iff.rfl
private theorem bres_apply' {A : Set α} {R : α → β → Prop} {B : Set β} {x : α} {y : β} :
    bres A R B x y ↔ (x ∈ A ∧ R x y) ∧ y ∈ B := Iff.rfl
private theorem fres_apply' {P : α → α → Prop} {A : Set α} {x y : α} :
    (P ⥏ A) x y ↔ (x ∈ A ∧ P x y) ∧ y ∈ A := Iff.rfl
private theorem cross_apply' {A : Set α} {B : Set β} {x : α} {y : β} :
    cross A B x y ↔ x ∈ A ∧ y ∈ B := Iff.rfl
private theorem rsq_apply' {R : α → α → Prop} {x z : α} :
    rsq R x z ↔ ∃ y, R x y ∧ R y z := Iff.rfl
private theorem rNull_iff {x : α} {y : β} : rNull x y ↔ False :=
  ⟨fun h => h ⟨rfl, rfl⟩, False.elim⟩
private theorem rEx_iff {R : α → β → Prop} : rEx R ↔ ∃ x y, R x y := Iff.rfl
private theorem RSub_iff {R S : α → β → Prop} : R ⪽ S ↔ ∀ x y, R x y → S x y := Iff.rfl
private theorem mem_V' {x : α} : x ∈ (V : Set α) ↔ True := ⟨fun _ => trivial, fun _ => rfl⟩
private theorem mem_Null' {x : α} : x ∈ (Λ : Set α) ↔ False := ⟨fun h => h rfl, False.elim⟩
private theorem mem_Cls' {A : Set α} : A ∈ (Cls : Set (Set α)) ↔ True := by
  rw [Cls_eq_univ]; exact ⟨fun _ => trivial, fun _ => Set.mem_univ _⟩
private theorem mem_Rel' {R : α → β → Prop} : R ∈ (Rel : Set (α → β → Prop)) ↔ True := by
  rw [Rel_eq_univ]; exact ⟨fun _ => trivial, fun _ => Set.mem_univ _⟩
private theorem mem_one' {A : Set α} : A ∈ one ↔ ∃ x, A = ι x := Iff.rfl
private theorem mem_two' {A : Set α} : A ∈ two ↔ ∃ x y, x ≠ y ∧ A = ι x ∪ ι y := Iff.rfl
private theorem mem_zero' {A : Set α} : A ∈ zero ↔ A = Λ := Iff.rfl
private theorem mem_twoDot' {R : α → β → Prop} : R ∈ twoDot ↔ ∃ x y, R = x ↓ y := Iff.rfl
private theorem mem_two_r' {R : α → α → Prop} : R ∈ two_r ↔ ∃ x y, x ≠ y ∧ R = x ↓ y := Iff.rfl
private theorem mem_zero_r' {R : α → β → Prop} : R ∈ zero_r ↔ R = rNull := Iff.rfl
private theorem mem_prodCls' {K : Set (Set α)} {x : α} : x ∈ prodCls K ↔ ∀ A, A ∈ K → x ∈ A :=
  Iff.rfl
private theorem mem_sumCls' {K : Set (Set α)} {x : α} : x ∈ sumCls K ↔ ∃ A, A ∈ K ∧ x ∈ A :=
  Iff.rfl
private theorem prodRel_apply' {L : Set (α → β → Prop)} {x : α} {y : β} :
    prodRel L x y ↔ ∀ R, R ∈ L → R x y := Iff.rfl
private theorem sumRel_apply' {L : Set (α → β → Prop)} {x : α} {y : β} :
    sumRel L x y ↔ ∃ R, R ∈ L ∧ R x y := Iff.rfl
private theorem iota_apply' {A : Set α} {x : α} : iota A x ↔ A = ι x := Iff.rfl
private theorem Rfwd_apply' {R : α → β → Prop} {A : Set α} {y : β} :
    Rfwd R A y ↔ A = refs R y := Iff.rfl
private theorem Rbwd_apply' {R : α → β → Prop} {B : Set β} {x : α} :
    Rbwd R B x ↔ B = rels R x := Iff.rfl
private theorem D_apply' {A : Set α} {R : α → β → Prop} : D A R ↔ A = dom R := Iff.rfl
private theorem Dcnv_apply' {B : Set β} {R : α → β → Prop} : Dcnv B R ↔ B = codom R := Iff.rfl
private theorem C_apply' {A : Set α} {R : α → α → Prop} : C A R ↔ A = fld R := Iff.rfl

/-- A class is `ι'x` iff its members are exactly `x` (✱51·14). -/
private theorem eq_unitCls_iff {A : Set α} {x : α} : A = ι x ↔ ∀ y, y ∈ A ↔ y = x := Set.ext_iff

/-- Two relations are equal iff they hold of the same pairs. -/
private theorem rel_ext_iff {R S : α → β → Prop} : R = S ↔ ∀ x y, R x y ↔ S x y := rel_eq_iff

/-- `ψ(ῐ'α)` holds iff `α = ι'b` for some `b` with `ψ b`. -/
private theorem desc_iota_cnv_iff {A : Set α} {ψ : α → Prop} :
    Desc iota˘ A ψ ↔ ∃ b, A = ι b ∧ ψ b := by
  rw [desc_iota_cnv]
  constructor
  · rintro ⟨b, hb, h⟩; exact ⟨b, eq_unitCls_iff.2 hb, h⟩
  · rintro ⟨b, hb, h⟩; exact ⟨b, eq_unitCls_iff.1 hb, h⟩

/-- `E!ῐ'α` holds iff `α` is a unit class. -/
private theorem edesc_iota_cnv_iff {A : Set α} : EDesc iota˘ A ↔ ∃ b, A = ι b := by
  constructor
  · rintro ⟨b, h⟩; exact ⟨b, (h b).2 rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, fun x => ⟨fun e => (unitCls_injective e).symm, fun e => by subst e; exact rfl⟩⟩

/-- `R⃗'y = Λ` iff `y` is not in `ᗡ'R`. -/
private theorem refs_eq_Null_iff {R : α → β → Prop} {y : β} : refs R y = Λ ↔ y ∉ codom R := by
  rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]
  simp only [mem_refs', mem_codom', not_exists]

/-- `R⃖'x = Λ` iff `x` is not in `D'R`. -/
private theorem rels_eq_Null_iff {R : α → β → Prop} {x : α} : rels R x = Λ ↔ x ∉ dom R := by
  rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]
  simp only [mem_rels', mem_dom', not_exists]

/-- `∃̇!R` iff `R ≠ Λ̇`. -/
private theorem rEx_iff_ne_rNull {R : α → β → Prop} : (∃ x y, R x y) ↔ ¬R = rNull := by
  constructor
  · rintro ⟨x, y, h⟩ e; rw [e] at h; exact rNull_apply _ _ h
  · intro h
    by_contra hc
    apply h
    funext x y
    exact propext ⟨fun h' => absurd ⟨x, y, h'⟩ hc, fun h' => absurd h' (rNull_apply x y)⟩

/-- `x ↓ y = z ↓ w` iff `x = z` and `y = w`. -/
private theorem couple_eq_iff {x z : α} {y w : β} : x ↓ y = z ↓ w ↔ x = z ∧ y = w := by
  constructor
  · intro h
    have : (z ↓ w) x y := by rw [← h]; exact ⟨rfl, rfl⟩
    exact this
  · rintro ⟨rfl, rfl⟩; rfl

private theorem dom_couple {x : α} {y : β} : dom (x ↓ y) = ι x := by
  ext z
  exact ⟨fun ⟨_, h, _⟩ => h, fun (h : z = x) => ⟨y, h, rfl⟩⟩

private theorem codom_couple {x : α} {y : β} : codom (x ↓ y) = ι y := by
  ext w
  exact ⟨fun ⟨_, _, h⟩ => h, fun (h : w = y) => ⟨x, rfl, h⟩⟩

private theorem fld_couple {x y : α} : fld (x ↓ y) = ι x ∪ ι y := by
  ext z
  constructor
  · rintro ⟨w, ⟨h, -⟩ | ⟨-, h⟩⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro ((h : z = x) | (h : z = y))
    · exact ⟨y, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨x, Or.inr ⟨rfl, h⟩⟩

/-- The relative product is associative (✱34·21). -/
private theorem relProd_assoc' {R : α → β → Prop} {S : β → γ → Prop} {T : γ → δ → Prop} :
    (R ⨾ S) ⨾ T = R ⨾ (S ⨾ T) := by
  funext x w; apply propext
  constructor
  · rintro ⟨z, ⟨y, h1, h2⟩, h3⟩; exact ⟨y, h1, z, h2, h3⟩
  · rintro ⟨y, h1, z, h2, h3⟩; exact ⟨z, ⟨y, h1, h2⟩, h3⟩

/-- `(R ‖ S)'X` always exists and is `R | X | S` (✱43·112). -/
private theorem desc_dpar {R : α → β → Prop} {S : γ → δ → Prop} {X : β → γ → Prop}
    {ψ : (α → δ → Prop) → Prop} : Desc (R ∥ S) X ψ ↔ ψ (R ⨾ (X ⨾ S)) :=
  TheIs_iff_of_unique (fun Q => dpar_iff R S Q X)

private theorem dpar_eq_iff {P R : α → β → Prop} {Q S : γ → δ → Prop} :
    P ∥ Q = R ∥ S ↔ ∀ X, P ⨾ (X ⨾ Q) = R ⨾ (X ⨾ S) := by
  constructor
  · intro h X
    have h2 : (R ∥ S) (P ⨾ (X ⨾ Q)) X := by rw [← h]; exact (dpar_iff P Q _ _).2 rfl
    exact (dpar_iff R S _ _).1 h2
  · intro h
    funext M X; apply propext
    rw [dpar_iff, dpar_iff, h X]

private theorem relProd_couple_apply {P : α → β → Prop} {Q : γ → δ → Prop} {x : α} {y : β}
    {a : γ} {c : δ} : (P ⨾ ((y ↓ a) ⨾ Q)) x c ↔ P x y ∧ Q a c := by
  constructor
  · rintro ⟨m, hP, n, ⟨rfl, rfl⟩, hQ⟩; exact ⟨hP, hQ⟩
  · rintro ⟨hP, hQ⟩; exact ⟨y, hP, a, ⟨rfl, rfl⟩, hQ⟩

/-- The set of pairs of a relation (used to compare relations consisting of couples). -/
private def toSet (R : α → β → Prop) : Set (α × β) := {p | R p.1 p.2}

private theorem toSet_inj {R S : α → β → Prop} : toSet R = toSet S ↔ R = S := by
  constructor
  · intro h
    funext a b; apply propext
    exact Set.ext_iff.1 h (a, b)
  · rintro rfl; rfl

private theorem toSet_sub {R S : α → β → Prop} : toSet R ⊆ toSet S ↔ R ⪽ S :=
  ⟨fun h a b hab => h (show (a, b) ∈ toSet R from hab), fun h p hp => h p.1 p.2 hp⟩

private theorem toSet_couple {x : α} {y : β} : toSet (x ↓ y) = {(x, y)} := by
  ext ⟨a, b⟩; simp [toSet, couple_apply]

private theorem toSet_rcup {R S : α → β → Prop} : toSet (R ⊍ S) = toSet R ∪ toSet S := rfl

private theorem toSet_rNull : toSet (rNull : α → β → Prop) = ∅ := by
  ext ⟨a, b⟩; simp [toSet, rNull_iff]

private theorem mem_D_cnv_img {R : α → β → Prop} {K : Set (Set α)} : R ∈ D˘ ʻʻ K ↔ dom R ∈ K :=
  ⟨fun ⟨_, hA, (h : _ = dom R)⟩ => h ▸ hA, fun h => ⟨dom R, h, rfl⟩⟩

private theorem mem_Dcnv_cnv_img {R : α → β → Prop} {K : Set (Set β)} :
    R ∈ Dcnv˘ ʻʻ K ↔ codom R ∈ K :=
  ⟨fun ⟨_, hA, (h : _ = codom R)⟩ => h ▸ hA, fun h => ⟨codom R, h, rfl⟩⟩

private theorem mem_C_cnv_img {R : α → α → Prop} {K : Set (Set α)} : R ∈ C˘ ʻʻ K ↔ fld R ∈ K :=
  ⟨fun ⟨_, hA, (h : _ = fld R)⟩ => h ▸ hA, fun h => ⟨fld R, h, rfl⟩⟩

private theorem couple_mem_two_r {x y : α} : x ↓ y ∈ two_r ↔ x ≠ y := by
  constructor
  · rintro ⟨a, b, hab, h⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 h
    exact hab
  · intro h; exact ⟨x, y, h, rfl⟩

end Unfold

attribute [local simp] mem_dom' mem_codom' mem_fld' mem_img' mem_refs' mem_rels' cnv_apply'
  relProd_apply' rcap_apply' rcup_apply' rdiff_apply' dres_apply' cres_apply' bres_apply'
  fres_apply' cross_apply' rsq_apply' rNull_iff rEx_iff RSub_iff mem_V' mem_Null' mem_Cls'
  mem_Rel' mem_prodCls' mem_sumCls' prodRel_apply' sumRel_apply' I_apply J_apply
  mem_unitCls couple_apply coupleL_apply coupleR_apply mem_zero_r' iota_apply' Rfwd_apply'
  Rbwd_apply' D_apply' Dcnv_apply' C_apply'

/-!
## [✱50] Identity and diversity as relations

*(Vol. 1, p. 349)*

> *Summary of *50.*
>
> The purpose of the present number is primarily notational. For notational reasons, we must be able to express identity and diversity as relations, and not merely as propositional functions, *i.e.* we require a notation for \(\hat{x}\hat{y}(x=y)\) and \(\hat{x}\hat{y}(x\neq y)\). We therefore put \[ \begin{array}{l} I=\hat{x}\hat{y}(x=y) & \text{Df,} \\ J=\dot{-}I & \text{Df.} \\ \end{array} \]
>
> In spite of the fact that diversity is merely the negation of identity, the kinds of propositions which employ diversity are quite different from the kinds that employ identity. Identity as a relation is required, to begin with, in the theory of unit classes, which is our reason for treating of it at this stage. It is next required, constantly, in the theory of mathematical induction (Part II, Section E). It is required also in showing that cardinal and ordinal similarity are reflexive. These are its principal uses.
>
> …

**Lean reading.** `I` and `J` are the homogeneous relations `I x y ↔ x = y`, `J x y ↔ x ≠ y` (Dfs ✱50·01·02, by
`rfl`); every proposition is stated at an arbitrary type `α` of individuals, with `R`, `P`
heterogeneous wherever PM's formula allows it (`R | I = I | R = R` holds with the two `I`s at
the two types of `R`). `I'y = y` (✱50·14) keeps the description (`Desc I y`), being a proposition
about its value; `D'I`, `ᗡ'I`, `C'I`, `R''α`, `Cnv'(α ↿ I)` are written with their value
functions (Basic §5). ✱50·7–·73 are about the descriptive functions `(R |)'S` and `(| R)'S` of
✱43, kept as descriptions of `relProdL R`, `relProdR R`; `R ‖ I` and `I ‖ R` (✱50·74·75) are
compared with `relProdL R` and `relProdR R`. ✱50·13, ✱50·34·35 need a member of the type
(`[Nonempty _]`), as do ✱50·76·761 for the type of the relata of the relations `P |`, `R |`.
The e-text prints `∃!` for `E!` in ✱50·15, `‖` for `|` in ✱50·72·73, and a stray bracket in ✱50·43.

**Status.** proved (all propositions; ✱50·01·02 definition; ✱50·13, ✱50·15, ✱50·34, ✱50·35, ✱50·72,
✱50·73, ✱50·76, ✱50·761 proved (reading), see their docstrings).
-/

/-- ✱50·01 (Df). \(I=\hat{x}\hat{y}(x=y) \quad\text{Df}\) -/
theorem pm50_01 : (I : α → α → Prop) = fun x y => x = y := rfl

/-- ✱50·02 (Df). \(J=\dot{-}I \quad\text{Df}\) -/
theorem pm50_02 : (J : α → α → Prop) = ∸I := rfl

/-- ✱50·1. \(\vdash:xIy.\equiv.x=y \quad[\text{*21·3.(*50·01)}]\) -/
theorem pm50_1 {x y : α} : I x y ↔ x = y := Iff.rfl

/-- ✱50·11. \(\vdash:xJy.\equiv.x\neq y \quad[\text{*23·35.*50·1.(*50·02)}]\) -/
theorem pm50_11 {x y : α} : J x y ↔ x ≠ y := Iff.rfl

/-- ✱50·12. \(\vdash.J=\hat{x}\hat{y}(x\neq y) \quad[\text{*50·11.*21·33}]\) -/
theorem pm50_12 : (J : α → α → Prop) = fun x y => x ≠ y := rfl

/-- ✱50·13. \(\vdash.\dot{\exists}!I \quad[\text{*13·19.*10·24·281.*50·1}]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I); for an
empty type `α` the relation `I` is null, so `[Nonempty α]` is added. -/
theorem pm50_13 [Nonempty α] : rEx (I : α → α → Prop) :=
  let ⟨x⟩ := ‹Nonempty α›
  ⟨x, x, rfl⟩

/-- ✱50·14. \(\vdash.Iʻy=y \quad[\text{*30·3.*50·1.*10·11}]\) -/
theorem pm50_14 {y : α} : Desc I y (fun b => b = y) := (desc_I y _).2 rfl

/-- ✱50·15. \(\vdash.(y).\exists!Iʻy \quad[\text{*50·14.*14·21.*10·11}]\)

**Status.** proved (reading): transcription error: the e-text prints `∃!I'y` for PM's `E!I'y` (the
proof cites ✱14·21, which concerns `E!`; `∃!` of ✱24·03 applies only to classes). -/
theorem pm50_15 : ∀ y : α, EDesc I y := fun y => ⟨y, fun _ => Iff.rfl⟩

/-- ✱50·16. \(\vdash.Iʻʻ\alpha=\alpha\) -/
theorem pm50_16 {A : Set α} : I ʻʻ A = A := by
  ext x; simp

/-- ✱50·17. \(\vdash\colon\ldotp x\in\alpha.\supset_{x}.Rʻx=x\colon\supset.Rʻʻ\alpha=\alpha\) -/
theorem pm50_17 {R : α → α → Prop} {A : Set α} :
    (∀ x, x ∈ A → Desc R x (fun b => b = x)) → R ʻʻ A = A := by
  intro h
  ext z
  constructor
  · rintro ⟨y, hy, hzy⟩
    obtain ⟨b, hb, hby⟩ := h y hy
    rw [(hb z).1 hzy, hby]; exact hy
  · intro hz
    obtain ⟨b, hb, hbz⟩ := h z hz
    exact ⟨z, hz, (hb z).2 hbz.symm⟩

/-- ✱50·2. \(\vdash.I=\breve{I}\) -/
theorem pm50_2 : (I : α → α → Prop) = I˘ := by
  funext x y; exact propext eq_comm

/-- ✱50·21. \(\vdash.J=\breve{J}\) -/
theorem pm50_21 : (J : α → α → Prop) = J˘ := by
  funext x y; exact propext ne_comm

/-- ✱50·22. \(\vdash\colon R \unicode{x2abd} I .\equiv. \breve{R} \unicode{x2abd} I \quad[\text{*31·4, *50·2}]\) -/
theorem pm50_22 {R : α → α → Prop} : R ⪽ I ↔ R˘ ⪽ I := by
  simp only [RSub_iff, cnv_apply', I_apply]
  exact ⟨fun h x y hxy => (h y x hxy).symm, fun h x y hxy => (h y x hxy).symm⟩

/-- ✱50·23. \(\vdash\colon R \unicode{x2abd} J .\equiv. \breve{R} \unicode{x2abd} J \quad[\text{*31·4, *50·21}]\) -/
theorem pm50_23 {R : α → α → Prop} : R ⪽ J ↔ R˘ ⪽ J := by
  simp only [RSub_iff, cnv_apply', J_apply]
  exact ⟨fun h x y hxy => (h y x hxy).symm, fun h x y hxy => (h y x hxy).symm⟩

/-- ✱50·24. \(\vdash\colon R \unicode{x2abd} J .\equiv. (x)\,{\sim}(xRx)\) -/
theorem pm50_24 {R : α → α → Prop} : R ⪽ J ↔ ∀ x, ¬R x x := by
  simp only [RSub_iff, J_apply]
  exact ⟨fun h x hx => h x x hx rfl, fun h x y hxy e => h x (e ▸ hxy)⟩

/-- ✱50·3. \(\vdash.(x).xIx \quad[\text{*50·1.*13·15}]\) -/
theorem pm50_3 : ∀ x : α, I x x := fun _ => rfl

/-- ✱50·31. \(\vdash.\text{D}ʻI=\text{V}.\text{ᗡ}ʻI=\text{V}\) -/
theorem pm50_31 : dom (I : α → α → Prop) = V ∧ codom (I : α → α → Prop) = V := by
  constructor <;> ext x <;> simp

/-- ✱50·32. \(\vdash.CʻI=\text{V} \quad[\text{*50·31.*33·16.*24·27}]\) -/
theorem pm50_32 : fld (I : α → α → Prop) = V := by
  ext x; simp

/-- ✱50·33. \(\vdash:\dot{\exists}!J.\supset.\text{D}ʻ J=\text{V}.\text{ᗡ}ʻJ=\text{V}.CʻJ=\text{V}\) -/
theorem pm50_33 :
    rEx (J : α → α → Prop) →
      (dom (J : α → α → Prop) = V ∧ codom (J : α → α → Prop) = V) ∧ fld (J : α → α → Prop) = V := by
  rintro ⟨a, b, hab⟩
  have key : ∀ z : α, ∃ w, z ≠ w := fun z => by
    by_cases h : z = a
    · exact ⟨b, h ▸ hab⟩
    · exact ⟨a, h⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> ext z <;> simp only [mem_dom', mem_codom', mem_fld', J_apply,
    mem_V', iff_true]
  · exact key z
  · obtain ⟨w, hw⟩ := key z; exact ⟨w, hw.symm⟩
  · obtain ⟨w, hw⟩ := key z; exact ⟨w, Or.inl hw⟩

/-- ✱50·34. \(\vdash.\dot{\exists}!J\unicode{x0294f}\text{Cls}\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): the proof
uses `Λ ≠ V`, which fails for an empty type `α` (then `Set α` has one member and `J` on
it is null), so `[Nonempty α]` is added. `J` is the diversity of classes of `α`-things. -/
theorem pm50_34 [Nonempty α] : rEx ((J : Set α → Set α → Prop) ⥏ (Cls : Set (Set α))) := by
  obtain ⟨x⟩ := ‹Nonempty α›
  refine ⟨Λ, V, ?_⟩
  simp only [fres_apply', mem_Cls', J_apply, true_and, and_true]
  intro h
  have : x ∈ (Λ : Set α) := h ▸ (rfl : x = x)
  exact this rfl

/-- ✱50·35. \(\vdash.\dot{\exists}!J\unicode{x0294f}\text{Rel} \quad[\text{Proof as in *50·34}]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): the proof
(as in ✱50·34) uses `Λ̇ ≠ V̇`, which fails when `α` or `β` is empty, so `[Nonempty α]`,
`[Nonempty β]` are added. `J` is the diversity of relations of type `α → β → Prop`. -/
theorem pm50_35 [Nonempty α] [Nonempty β] :
    rEx ((J : (α → β → Prop) → (α → β → Prop) → Prop) ⥏ (Rel : Set (α → β → Prop))) := by
  obtain ⟨x⟩ := ‹Nonempty α›
  obtain ⟨y⟩ := ‹Nonempty β›
  refine ⟨rNull, rV, ?_⟩
  simp only [fres_apply', mem_Rel', J_apply, true_and, and_true]
  intro h
  have : rNull x y := h ▸ (⟨rfl, rfl⟩ : rV x y)
  exact rNull_apply x y this

/-- ✱50·4. \(\vdash.R \mid I=I \mid R=R\) -/
theorem pm50_4 {R : α → β → Prop} : R ⨾ I = I ⨾ R ∧ I ⨾ R = R := by
  constructor <;> funext x y <;> apply propext <;> simp

/-- ✱50·41. \(\vdash:R \mid \breve{P}\unicode{x2abd}J.\equiv.\breve{R} \mid P\unicode{x2abd}J.\equiv.R\dot{\cap}P=\dot{\Lambda}\) -/
theorem pm50_41 {R P : α → β → Prop} :
    (R ⨾ P˘ ⪽ J ↔ R˘ ⨾ P ⪽ J) ∧ (R˘ ⨾ P ⪽ J ↔ R ⩀ P = rNull) := by
  simp only [RSub_iff, relProd_apply', cnv_apply', J_apply, rel_ext_iff, rcap_apply', rNull_iff,
    iff_false, not_and]
  constructor
  · constructor
    · intro h x z ⟨y, h1, h2⟩ e; subst e; exact h y y ⟨x, h1, h2⟩ rfl
    · intro h x z ⟨y, h1, h2⟩ e; subst e; exact h y y ⟨x, h1, h2⟩ rfl
  · constructor
    · intro h x y h1 h2; exact h y y ⟨x, h1, h2⟩ rfl
    · intro h x z ⟨y, h1, h2⟩ e; subst e; exact h y x h1 h2

/-- ✱50·42. \(\vdash. I^{2} = I\) -/
theorem pm50_42 : rsq (I : α → α → Prop) = I := by
  funext x y; apply propext; simp

/-- ✱50·43. \(\vdash: R^{2} \unicode{x2abd} J. \equiv . R\dot{\cap})\breve{R} = \dot{\Lambda} \quad\left[\text{*50·41}\, \frac{\breve{R}}{P}\right]\)

**Status.** proved: the e-text has a stray bracket, `R ∩̇) R̆ = Λ̇`, for `R ∩̇ R̆ = Λ̇`. -/
theorem pm50_43 {R : α → α → Prop} : rsq R ⪽ J ↔ R ⩀ R˘ = rNull := by
  simp only [RSub_iff, rsq_apply', J_apply, rel_ext_iff, rcap_apply', cnv_apply', rNull_iff,
    iff_false, not_and]
  constructor
  · intro h x y h1 h2; exact h x x ⟨y, h1, h2⟩ rfl
  · intro h x z ⟨y, h1, h2⟩ e; subst e; exact h x y h1 h2

/-- ✱50·44. \(\vdash: \dot{\exists}!(R \dot{\cap} I). \supset . \dot{\exists}! (R^{2} \dot{\cap} I)\) -/
theorem pm50_44 {R : α → α → Prop} : rEx (R ⩀ I) → rEx (rsq R ⩀ I) := by
  simp only [rEx_iff, rcap_apply', I_apply, rsq_apply']
  rintro ⟨x, y, h, rfl⟩
  exact ⟨x, x, ⟨x, h, h⟩, rfl⟩

/-- ✱50·45. \(\vdash: R^{2} \unicode{x2abd} J. \supset . R \unicode{x2abd} J \quad[\text{*50·44. Transp . *25·311}]\) -/
theorem pm50_45 {R : α → α → Prop} : rsq R ⪽ J → R ⪽ J := by
  simp only [RSub_iff, rsq_apply', J_apply]
  intro h x y hxy e; subst e; exact h x x ⟨x, hxy, hxy⟩ rfl

/-- ✱50·46. \(\vdash: R \dot{\cap}\breve{R} = \dot{\Lambda} .\supset. R \unicode{x2abd} J \quad[\text{*50·43·45}]\) -/
theorem pm50_46 {R : α → α → Prop} : R ⩀ R˘ = rNull → R ⪽ J := fun h =>
  pm50_45 (pm50_43.2 h)

/-- ✱50·47. \(\vdash\colon\ldotp R^{2} \unicode{x2abd} R. \supset : R \unicode{x2abd} J. \equiv . R^{2} \unicode{x2abd} J. \equiv . R\dot{\cap} \breve{R} = \dot{\Lambda}\) -/
theorem pm50_47 {R : α → α → Prop} :
    rsq R ⪽ R → ((R ⪽ J ↔ rsq R ⪽ J) ∧ (rsq R ⪽ J ↔ R ⩀ R˘ = rNull)) := by
  intro h
  exact ⟨⟨fun hJ x y hxy => hJ x y (h x y hxy), pm50_45⟩, pm50_43⟩

/-- ✱50·5. \(\vdash. \alpha\upharpoonleft I = I\upharpoonright \alpha = \alpha\upharpoonleft I\upharpoonright \alpha\) -/
theorem pm50_5 {A : Set α} : A ◁ I = I ↾ A ∧ I ↾ A = A ◁ I ↾ A := by
  constructor <;> funext x y <;> apply propext <;>
    simp only [dres_apply', cres_apply', I_apply] <;>
    aesop

/-- ✱50·51. \(\vdash.\text{Cnv}ʻ(\alpha\upharpoonleft I)=\alpha\upharpoonleft I \quad[\text{*35·51.*50·2·5}]\) -/
theorem pm50_51 {A : Set α} : (A ◁ I)˘ = A ◁ I := by
  funext x y; apply propext; simp only [cnv_apply', dres_apply', I_apply]
  constructor <;> rintro ⟨h, rfl⟩ <;> exact ⟨h, rfl⟩

/-- ✱50·52. \(\vdash.\text{D}ʻ(\alpha\upharpoonleft I)=\text{ᗡ}ʻ(\alpha\upharpoonleft I)=Cʻ(\alpha\upharpoonleft I)=\alpha\) -/
theorem pm50_52 {A : Set α} :
    (dom (A ◁ I) = codom (A ◁ I) ∧ codom (A ◁ I) = fld (A ◁ I)) ∧ fld (A ◁ I) = A := by
  have h1 : dom (A ◁ I) = A := by ext x; simp
  have h2 : codom (A ◁ I) = A := by ext x; simp
  have h3 : fld (A ◁ I) = A := by ext x; simp; aesop
  rw [h1, h2, h3]; exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- ✱50·53. \(\vdash.\alpha\upharpoonleft I\upharpoonright \beta=(\alpha\cap \beta)\upharpoonleft I=I\upharpoonright (\alpha\cap \beta)\) -/
theorem pm50_53 {A B : Set α} : A ◁ I ↾ B = (A ∩ B) ◁ I ∧ (A ∩ B) ◁ I = I ↾ (A ∩ B) := by
  constructor <;> funext x y <;> apply propext <;>
    simp only [dres_apply', cres_apply', I_apply, Set.mem_inter_iff] <;>
    aesop

/-- ✱50·54. \(\vdash.(\alpha\upharpoonleft I)^{2}=\alpha\upharpoonleft I\) -/
theorem pm50_54 {A : Set α} : rsq (A ◁ I) = A ◁ I := by
  funext x y; apply propext; simp only [rsq_apply', dres_apply', I_apply]
  constructor
  · rintro ⟨z, ⟨h, rfl⟩, -, rfl⟩; exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩; exact ⟨x, ⟨h, rfl⟩, h, rfl⟩

/-- ✱50·55. \(\vdash:\alpha\cap \beta=\Lambda.\equiv.\alpha\uparrow \beta\unicode{x2abd}J\) -/
theorem pm50_55 {A B : Set α} : A ∩ B = Λ ↔ cross A B ⪽ J := by
  rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]
  simp only [RSub_iff, cross_apply', J_apply, Set.mem_inter_iff, not_and]
  constructor
  · intro h x y ⟨hx, hy⟩ e; subst e; exact h x hx hy
  · intro h x hx hy; exact h x x ⟨hx, hy⟩ rfl

/-- ✱50·56. \(\vdash:\exists !(\alpha\cap \beta).\equiv.\dot{\exists}!\{(\alpha\uparrow \beta)\dot{\cap}I\}\) -/
theorem pm50_56 {A B : Set α} : (A ∩ B).Nonempty ↔ rEx (cross A B ⩀ I) := by
  simp only [rEx_iff, rcap_apply', cross_apply', I_apply]
  constructor
  · rintro ⟨x, hA, hB⟩; exact ⟨x, x, ⟨hA, hB⟩, rfl⟩
  · rintro ⟨x, y, ⟨hA, hB⟩, rfl⟩; exact ⟨x, hA, hB⟩

/-- ✱50·57. \(\vdash.I\dot{\cap}\alpha\upharpoonleft R=I\dot{\cap}R\upharpoonright \alpha=I\dot{\cap}\alpha\upharpoonleft R\upharpoonright \alpha\) -/
theorem pm50_57 {R : α → α → Prop} {A : Set α} :
    I ⩀ A ◁ R = I ⩀ R ↾ A ∧ I ⩀ R ↾ A = I ⩀ A ◁ R ↾ A := by
  constructor <;> funext x y <;> apply propext <;>
    simp only [rcap_apply', dres_apply', cres_apply', I_apply] <;>
    aesop

/-- ✱50·58. \(\vdash:\alpha\upharpoonleft R\unicode{x2abd}J.\equiv.R\upharpoonright \alpha\unicode{x2abd}J.\equiv.\alpha\upharpoonleft R\upharpoonright \alpha\unicode{x2abd}J\) -/
theorem pm50_58 {R : α → α → Prop} {A : Set α} :
    (A ◁ R ⪽ J ↔ R ↾ A ⪽ J) ∧ (R ↾ A ⪽ J ↔ A ◁ R ↾ A ⪽ J) := by
  simp only [RSub_iff, dres_apply', cres_apply', J_apply]
  refine ⟨⟨fun h x y ⟨h1, h2⟩ e => ?_, fun h x y ⟨h1, h2⟩ e => ?_⟩,
    ⟨fun h x y ⟨⟨_, h1⟩, h2⟩ e => h x y ⟨h1, h2⟩ e, fun h x y ⟨h1, h2⟩ e => ?_⟩⟩
  · subst e; exact h x x ⟨h2, h1⟩ rfl
  · subst e; exact h x x ⟨h2, h1⟩ rfl
  · subst e; exact h x x ⟨⟨h2, h1⟩, h2⟩ rfl

/-- ✱50·59. \(\vdash.(I\upharpoonright \alpha)ʻʻ\beta=\alpha\cap \beta\) -/
theorem pm50_59 {A B : Set α} : (I ↾ A) ʻʻ B = A ∩ B := by
  ext x; simp only [mem_img', cres_apply', I_apply, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, rfl, hA⟩; exact ⟨hA, hy⟩
  · rintro ⟨hA, hB⟩; exact ⟨x, hB, rfl, hA⟩

/-- ✱50·6. \(\vdash.R\mid (I\upharpoonright \alpha)=R\upharpoonright \alpha\) -/
theorem pm50_6 {R : α → β → Prop} {A : Set β} : R ⨾ (I ↾ A) = R ↾ A := by
  funext x y; apply propext; simp only [relProd_apply', cres_apply', I_apply]
  constructor
  · rintro ⟨z, h, rfl, hA⟩; exact ⟨h, hA⟩
  · rintro ⟨h, hA⟩; exact ⟨y, h, rfl, hA⟩

/-- ✱50·61. \(\vdash.I\upharpoonright \alpha\mid R=\alpha\upharpoonleft R\) -/
theorem pm50_61 {R : α → β → Prop} {A : Set α} : (I ↾ A) ⨾ R = A ◁ R := by
  funext x y; apply propext; simp only [relProd_apply', cres_apply', dres_apply', I_apply]
  constructor
  · rintro ⟨z, ⟨rfl, hA⟩, h⟩; exact ⟨hA, h⟩
  · rintro ⟨hA, h⟩; exact ⟨x, ⟨rfl, hA⟩, h⟩

/-- ✱50·62. \(\vdash:\text{ᗡ}ʻR\subset\alpha.\supset.R\mid (I\upharpoonright \alpha)=R \quad[\text{*50·6.*35·452}]\) -/
theorem pm50_62 {R : α → β → Prop} {A : Set β} : codom R ⊆ A → R ⨾ (I ↾ A) = R := by
  intro h
  rw [pm50_6]
  funext x y; apply propext
  exact ⟨fun h' => h'.1, fun h' => ⟨h', h ⟨x, h'⟩⟩⟩

/-- ✱50·63. \(\vdash:\text{D}ʻR\subset\alpha.\supset.I\upharpoonright \alpha\mid R=R \quad[\text{*50·61.*35·451}]\) -/
theorem pm50_63 {R : α → β → Prop} {A : Set α} : dom R ⊆ A → (I ↾ A) ⨾ R = R := by
  intro h
  rw [pm50_61]
  funext x y; apply propext
  exact ⟨fun h' => h'.2, fun h' => ⟨h ⟨y, h'⟩, h'⟩⟩

/-- ✱50·64. \(\vdash.R\mid (I\upharpoonright \text{ᗡ}ʻR)=R\mid (I\upharpoonright CʻR)=R \quad[\text{*50·62.*22·42.*33·161}]\) -/
theorem pm50_64 {R : α → α → Prop} :
    R ⨾ (I ↾ codom R) = R ⨾ (I ↾ fld R) ∧ R ⨾ (I ↾ fld R) = R := by
  rw [pm50_62 (subset_refl _), pm50_62 (fun y ⟨x, h⟩ => ⟨x, Or.inr h⟩)]
  exact ⟨rfl, rfl⟩

/-- ✱50·65. \(\vdash.I\upharpoonright (\text{D}ʻR)\mid R=I\upharpoonright (CʻR)\mid R=R \quad[\text{*50·63.*22·42.*33·161}]\) -/
theorem pm50_65 {R : α → α → Prop} :
    (I ↾ dom R) ⨾ R = (I ↾ fld R) ⨾ R ∧ (I ↾ fld R) ⨾ R = R := by
  rw [pm50_63 (subset_refl _), pm50_63 (fun x ⟨y, h⟩ => ⟨y, Or.inl h⟩)]
  exact ⟨rfl, rfl⟩

/-- ✱50·7. \(\vdash:\text{ᗡ}ʻR\subset\alpha.\supset.R\mid ʻI\upharpoonright \alpha=R \quad[\text{*50·62.*43·11}]\) -/
theorem pm50_7 {R : α → β → Prop} {A : Set β} :
    codom R ⊆ A → Desc (relProdL R) (I ↾ A) (fun Q => Q = R) := fun h =>
  (desc_graph (relProd R) (I ↾ A) _).2 (pm50_62 h)

/-- ✱50·71. \(\vdash:\text{D}ʻR\subset\alpha.\supset.\mid RʻI\upharpoonright \alpha=R \quad[\text{*50·63.*43·111}]\) -/
theorem pm50_71 {R : α → β → Prop} {A : Set α} :
    dom R ⊆ A → Desc (relProdR R) (I ↾ A) (fun Q => Q = R) := fun h =>
  (desc_graph (fun Q : α → α → Prop => Q ⨾ R) (I ↾ A) _).2 (pm50_63 h)

/-- ✱50·72. \(\vdash.R\Vert ʻ(I\upharpoonright CʻR)=\mid Rʻ(I\upharpoonright CʻR)=R \quad[\text{*50·7·71}]\)

**Status.** proved (reading): transcription error: the e-text prints `R ‖ '` for `R | '` (the
descriptive function of the relation `R |` of ✱43); the proof cites ✱50·7·71. -/
theorem pm50_72 {R : α → α → Prop} :
    Desc (relProdL R) (I ↾ fld R) (fun Q => Desc (relProdR R) (I ↾ fld R) (fun Q' => Q = Q')) ∧
      Desc (relProdR R) (I ↾ fld R) (fun Q => Q = R) := by
  have h1 := pm50_7 (R := R) (A := fld R) (fun y ⟨x, h⟩ => ⟨x, Or.inr h⟩)
  have h2 := pm50_71 (R := R) (A := fld R) (fun x ⟨y, h⟩ => ⟨y, Or.inl h⟩)
  refine ⟨?_, h2⟩
  obtain ⟨b, hb, hbR⟩ := h1
  obtain ⟨c, hc, hcR⟩ := h2
  exact ⟨b, hb, c, hc, hbR.trans hcR.symm⟩

/-- ✱50·73. \(\vdash.R\Vert ʻI=\mid RʻI=R \quad[\text{*50·4.*43·11·111}]\)

**Status.** proved (reading): transcription error: the e-text prints `R ‖ '` for `R | '`, as in
✱50·72 (the proof cites ✱43·11·111). -/
theorem pm50_73 {R : α → β → Prop} :
    Desc (relProdL R) I (fun Q => Desc (relProdR R) I (fun Q' => Q = Q')) ∧
      Desc (relProdR R) I (fun Q => Q = R) := by
  have h1 : Desc (relProdL R) I (fun Q => Q = R) :=
    (desc_graph (relProd R) I _).2 (pm50_4.1.trans pm50_4.2)
  have h2 : Desc (relProdR R) I (fun Q => Q = R) :=
    (desc_graph (fun Q : α → α → Prop => Q ⨾ R) I _).2 pm50_4.2
  refine ⟨?_, h2⟩
  obtain ⟨b, hb, hbR⟩ := h1
  obtain ⟨c, hc, hcR⟩ := h2
  exact ⟨b, hb, c, hc, hbR.trans hcR.symm⟩

/-- ✱50·74. \(\vdash.R\Vert I=R\mid\) -/
theorem pm50_74 {R : α → β → Prop} :
    R ∥ (I : γ → γ → Prop) = relProdL R := by
  funext P Q; apply propext
  rw [dpar_iff]
  show P = R ⨾ (Q ⨾ I) ↔ P = R ⨾ Q
  rw [pm50_4.1.trans pm50_4.2]

/-- ✱50·75. \(\vdash.I\Vert R=\mid R \quad[\text{Proof as in *50·74}]\) -/
theorem pm50_75 {R : α → β → Prop} :
    (I : γ → γ → Prop) ∥ R = relProdR R := by
  funext P Q; apply propext
  rw [dpar_iff]
  show P = I ⨾ (Q ⨾ R) ↔ P = Q ⨾ R
  rw [pm50_4.2]

/-- ✱50·76. \(\vdash:P\mid =R\mid .\equiv.P=R\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): if the type
`γ` of the relata of the relations `P | Q`, `R | Q` is empty, there is only one relation of each of
the types `α → γ → Prop`, `β → γ → Prop`, so `P |` and `R |` are both the universal relation
between them and the equivalence fails for `P ≠ R`; hence `[Nonempty γ]` is added. (PM's proof,
via ✱50·73, takes `γ` to be the type of the relata of `P`.) -/
theorem pm50_76 [Nonempty γ] {P R : α → β → Prop} :
    (relProdL P : (α → γ → Prop) → (β → γ → Prop) → Prop) = relProdL R ↔ P = R := by
  constructor
  · intro h
    obtain ⟨c⟩ := ‹Nonempty γ›
    funext x y; apply propext
    let S : β → γ → Prop := fun y' _ => y' = y
    have h1 : relProdL R (P ⨾ S) S := by rw [← h]; exact rfl
    have hS : P ⨾ S = R ⨾ S := h1
    have := congrFun (congrFun hS x) c
    simp only [relProd_apply', S, exists_eq_right] at this
    rw [this]
  · rintro rfl; rfl

/-- ✱50·761. \(\vdash:\mid P=\mid R.\equiv.P=R \quad[\text{Proof as in *50·76}]\)

**Status.** proved (reading): as ✱50·76, `[Nonempty γ]` is added for the type `γ` of the referents of
the relations `Q | P`, `Q | R`. -/
theorem pm50_761 [Nonempty γ] {P R : α → β → Prop} :
    (relProdR P : (γ → β → Prop) → (γ → α → Prop) → Prop) = relProdR R ↔ P = R := by
  constructor
  · intro h
    obtain ⟨c⟩ := ‹Nonempty γ›
    funext x y; apply propext
    let S : γ → α → Prop := fun _ x' => x' = x
    have h1 : relProdR R (S ⨾ P) S := by rw [← h]; exact rfl
    have hS : S ⨾ P = S ⨾ R := h1
    have := congrFun (congrFun hS c) y
    simp only [relProd_apply', S, exists_eq_left] at this
    rw [this]
  · rintro rfl; rfl

/-!
## [✱51] Unit classes

*(Vol. 1, p. 356)*

> *Summary of* *51.
>
> In this number we introduce a new descriptive function \(\iotaʻx\), meaning "the class of terms which are identical with \(x\)," which is the same thing as "the class whose only member is \(x\)." We are thus to have \[ \iotaʻx = \hat{y} (y = x)\text{.} \] But \(\hat{y}(y = x) = \overrightarrow{I}ʻx\). Hence we secure what we require by the following definition:
>
> *51·01. \(\iota = \overrightarrow{I} \quad \text{Df}\)
>
> As a matter of notation, it might be thought that \(\overrightarrow{I}\) would do as well as \(\iota\), and that this definition is superfluous. But we need also the converse of this relation, and "\(\text{Cnv}ʻ\overrightarrow{I}\)" is not a sufficiently convenient symbol.
>
> The propositions of this number are constantly used in what follows. It should be observed that the class whose members are \(x\) and \(y\) is \(\iota ʻx \cup \iotaʻy\), the class whose members are \(x\), \(y\), \(z\) is \(\iota ʻx \cup \iotaʻy \cup \iotaʻz\), the class formed by adding \(x\) to \(\alpha\) is \(\alpha \cup \iotaʻx\), and the class formed by taking \(x\) away from \(\alpha\) is \(\alpha - \iotaʻx\). (If \(x\) is not a member of \(\alpha\), this is equal to \(\alpha\).)
>
> …

**Lean reading.** `ι` is the relation `iota = I⃗` (✱51·01, by `rfl`), whose descriptive function always exists:
`ι'x` is the unit class `ι x` (`unitCls`, i.e. `{x}`; `α ι x` is `iota A x`). ✱51·11·12, which
give the value and the existence of `ι'x`, keep the description (`Desc iota x`, `EDesc iota x`);
elsewhere `ι'x` is written `ι x`. The converse `ῐ` is `iota˘`, whose descriptive function exists
only for unit classes, so `ψ(ῐ'α)` is always `Desc iota˘ A ψ` (✱51·51–·59). The class variables
`α, β` are `A B : Set α` and `φ, ψ` are functions `α → Prop`; chains of `≡` and `=` are
conjunctions of their links. The e-text prints `⊃` for `⊂` in ✱51·2 and ✱51·25 (the proof of
✱51·2 ends with `ι'x ⊂ α`, by ✱22·1); these are read with PM's `⊂` (`⊆`).

**Status.** proved (all propositions; ✱51·01 definition; ✱51·2, ✱51·25 proved (reading), see their
docstrings).
-/

/-- ✱51·01 (Df). \(\iota=\overrightarrow{I} \quad\text{Df}\) -/
theorem pm51_01 : (iota : Set α → α → Prop) = Rfwd I := rfl

/-- ✱51·1. \(\vdash\colon\alpha \iota x.\equiv.\alpha=\hat{y}(y=x)\) -/
theorem pm51_1 {A : Set α} {x : α} : iota A x ↔ A = {y | y = x} := Iff.rfl

/-- ✱51·11. \(\vdash.\iotaʻ x=\hat{y}(y=x) \quad[\text{*30·3.*51·1}]\) -/
theorem pm51_11 {x : α} : Desc iota x (fun A => A = {y | y = x}) := (desc_iota x _).2 rfl

/-- ✱51·12. \(\vdash._\text{E}!\iotaʻ x \quad[\text{*51·11.*14·21}]\)

**Status.** proved: the e-text prints a stray subscript, `⊢ ._E!ι'x`. -/
theorem pm51_12 {x : α} : EDesc iota x := EDesc_graph (refs I) x

/-- ✱51·13. \(\vdash\colon\alpha=\iotaʻ x.\equiv.\alpha=\hat{y}(y=x) \quad [\text{*20·57·2.*51·11}]\) -/
theorem pm51_13 {A : Set α} {x : α} : A = ι x ↔ A = {y | y = x} := Iff.rfl

/-- ✱51·131. \(\vdash\colon\alpha\iota x.\equiv.\alpha=\iotaʻ x \quad[\text{*51·1·13}]\) -/
theorem pm51_131 {A : Set α} {x : α} : iota A x ↔ A = ι x := Iff.rfl

/-- ✱51·14. \(\vdash\colon\ldotp \alpha=\iotaʻ x.\equiv\colon y\in\alpha.\equiv_{y}.y=x \quad[\text{*51·13.*20·33}]\) -/
theorem pm51_14 {A : Set α} {x : α} : A = ι x ↔ ∀ y, y ∈ A ↔ y = x := eq_unitCls_iff

/-- ✱51·141. \[\begin{align}\vdash\colon\ldotp \alpha=\iotaʻ x.\equiv:\exists!\alpha\colon y\in\alpha.\supset_{y}.y&=x\colon\equiv\colon x\in\alpha\colon y\in\alpha.\supset_{y}.y=x\\ &\quad[\text{*51·14.*14·122}]\end{align}\] -/
theorem pm51_141 {A : Set α} {x : α} :
    (A = ι x ↔ A.Nonempty ∧ ∀ y, y ∈ A → y = x) ∧
      (A.Nonempty ∧ (∀ y, y ∈ A → y = x) ↔ x ∈ A ∧ ∀ y, y ∈ A → y = x) := by
  rw [eq_unitCls_iff]
  refine ⟨⟨fun h => ⟨⟨x, (h x).2 rfl⟩, fun y hy => (h y).1 hy⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨⟨z, hz⟩, h⟩ y
    exact ⟨h y, fun e => e ▸ (h z hz) ▸ hz⟩
  · rintro ⟨⟨z, hz⟩, h⟩
    exact ⟨(h z hz) ▸ hz, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h⟩

/-- ✱51·15. \(\vdash:y\in\iotaʻ x.\equiv.y=x \quad[\text{*51·11.*20·33}]\) -/
theorem pm51_15 {x y : α} : y ∈ ι x ↔ y = x := Iff.rfl

/-- ✱51·16. \(\vdash.x\in\iotaʻ x \quad[\text{*51·15.*13·15}]\) -/
theorem pm51_16 {x : α} : x ∈ ι x := rfl

/-- ✱51·161. \(\vdash.\exists!\iotaʻ x \quad[\text{*51·16.*10·24}]\) -/
theorem pm51_161 {x : α} : (ι x).Nonempty := ⟨x, pm51_16⟩

/-- ✱51·17. \(\vdash.\text{ᗡ}ʻ\iota=\text{V}\) -/
theorem pm51_17 : codom (iota : Set α → α → Prop) = V := by
  ext x; simp

/-- ✱51·2. \(\vdash:x\in\alpha.\equiv.\iotaʻ x\supset \alpha\)

**Status.** proved (reading): transcription error: the e-text prints `ι'x ⊃ α` for PM's `ι'x ⊂ α`
(the demonstration ends with `ι'x ⊂ α`, by ✱22·1, and the comment speaks of replacing
membership by inclusion). As printed (`α ⊆ ι'x`) it would be false for `α = V` with two
members. -/
theorem pm51_2 {A : Set α} {x : α} : x ∈ A ↔ ι x ⊆ A :=
  ⟨fun h y (hy : y = x) => hy ▸ h, fun h => h (rfl : x = x)⟩

/-- ✱51·21. \(\vdash.x{\sim} \in\alpha -\iotaʻ x\) -/
theorem pm51_21 {A : Set α} {x : α} : x ∉ A \ ι x := fun h => h.2 rfl

/-- ✱51·211. \(\vdash:x{\sim} \in\alpha.\equiv.\iotaʻ x\cap\alpha=\Lambda\) -/
theorem pm51_211 {A : Set α} {x : α} : x ∉ A ↔ ι x ∩ A = Λ := by
  rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]
  constructor
  · rintro h y ⟨rfl, hy⟩; exact h hy
  · intro h hx; exact h x ⟨rfl, hx⟩

/-- ✱51·22. \(\vdash:\alpha\cap \iotaʻ x=\Lambda.\alpha\cup \iotaʻ x=\beta.\equiv.x\in\beta.\alpha=\beta -\iotaʻ x\) -/
theorem pm51_22 {A B : Set α} {x : α} :
    A ∩ ι x = Λ ∧ A ∪ ι x = B ↔ x ∈ B ∧ A = B \ ι x := by
  rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]
  constructor
  · rintro ⟨h1, rfl⟩
    refine ⟨Or.inr rfl, ?_⟩
    ext y
    constructor
    · intro hy; exact ⟨Or.inl hy, fun (e : y = x) => h1 y ⟨hy, e⟩⟩
    · rintro ⟨hy | hy, hn⟩
      · exact hy
      · exact absurd hy hn
  · rintro ⟨hx, rfl⟩
    refine ⟨fun y ⟨⟨_, hn⟩, hy⟩ => hn hy, ?_⟩
    ext y
    constructor
    · rintro (⟨hy, _⟩ | (rfl : y = x))
      · exact hy
      · exact hx
    · intro hy
      by_cases e : y = x
      · exact Or.inr e
      · exact Or.inl ⟨hy, e⟩

/-- ✱51·221. \(\vdash:x\in\alpha.\equiv.(\alpha -\iotaʻ x)\cup \iotaʻ x=\alpha\) -/
theorem pm51_221 {A : Set α} {x : α} : x ∈ A ↔ (A \ ι x) ∪ ι x = A := by
  constructor
  · intro hx
    ext y
    constructor
    · rintro (⟨hy, _⟩ | (rfl : y = x))
      · exact hy
      · exact hx
    · intro hy
      by_cases e : y = x
      · exact Or.inr e
      · exact Or.inl ⟨hy, e⟩
  · intro h
    rw [← h]; exact Or.inr rfl

/-- ✱51·222. \(\vdash:x{\sim} \in\alpha.\equiv.\alpha - \iotaʻ x=\alpha \quad[\text{*51·211.*24·313}]\) -/
theorem pm51_222 {A : Set α} {x : α} : x ∉ A ↔ A \ ι x = A := by
  constructor
  · intro hx
    ext y
    exact ⟨fun h => h.1, fun hy => ⟨hy, fun (e : y = x) => hx (e ▸ hy)⟩⟩
  · intro h hx
    rw [← h] at hx
    exact hx.2 rfl

/-- ✱51·23. \(\vdash:\iotaʻ x= \iotaʻ y.\equiv.y\in\iotaʻ x.\equiv.x\in\iotaʻ y.\equiv.x=y\) -/
theorem pm51_23 {x y : α} :
    ((ι x = ι y ↔ y ∈ ι x) ∧ (y ∈ ι x ↔ x ∈ ι y)) ∧ (x ∈ ι y ↔ x = y) := by
  refine ⟨⟨⟨fun h => ?_, fun (h : y = x) => by rw [h]⟩, ⟨fun (h : y = x) => h.symm,
    fun (h : x = y) => h.symm⟩⟩, Iff.rfl⟩
  exact (unitCls_injective h).symm

/-- ✱51·231. \(\vdash:\iotaʻ x\cap \iotaʻ y=\Lambda.\equiv.x\neq y\) -/
theorem pm51_231 {x y : α} : ι x ∩ ι y = Λ ↔ x ≠ y := by
  rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h e; subst e; exact h x ⟨rfl, rfl⟩
  · rintro h z ⟨(h1 : z = x), (h2 : z = y)⟩; exact h (h1 ▸ h2)

/-- ✱51·232. \(\vdash\colon\ldotp z\in(\iotaʻ x\cup \iotaʻ y).\equiv:z=x.\lor.z=y \quad[\text{*22·34.*51·15}]\) -/
theorem pm51_232 {x y z : α} : z ∈ ι x ∪ ι y ↔ z = x ∨ z = y := Iff.rfl

/-- ✱51·233. \[\begin{align}&\vdash\colon\colon \alpha=\iotaʻ x\cup \iotaʻ y.\supset\colon\ldotp(z)\colon\ldotp z\in\alpha.\equiv:z=x.\lor.z=y\\ &[\text{*51·232.*10·11.*20·18}]\end{align}\] -/
theorem pm51_233 {A : Set α} {x y : α} : A = ι x ∪ ι y → ∀ z, z ∈ A ↔ z = x ∨ z = y := by
  rintro rfl z; exact Iff.rfl

/-- ✱51·234. \(\vdash\colon\colon \alpha=\iotaʻ x\cup \iotaʻ y.\supset\colon\ldotp z\in\alpha.\supset_{z}.\phi z:\equiv.\phi x.\phi y\) -/
theorem pm51_234 {A : Set α} {x y : α} {φ : α → Prop} :
    A = ι x ∪ ι y → ((∀ z, z ∈ A → φ z) ↔ φ x ∧ φ y) := by
  rintro rfl
  constructor
  · intro h; exact ⟨h x (Or.inl rfl), h y (Or.inr rfl)⟩
  · rintro ⟨hx, hy⟩ z (rfl | rfl)
    · exact hx
    · exact hy

/-- ✱51·235. \(\vdash\colon\colon \alpha=\iotaʻ x\cup \iotaʻ y.\supset\colon\ldotp(\exists z).z\in\alpha.\phi z.\equiv:\phi x.\lor.\phi y\) -/
theorem pm51_235 {A : Set α} {x y : α} {φ : α → Prop} :
    A = ι x ∪ ι y → ((∃ z, z ∈ A ∧ φ z) ↔ φ x ∨ φ y) := by
  rintro rfl
  constructor
  · rintro ⟨z, (rfl | rfl), h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨x, Or.inl rfl, h⟩
    · exact ⟨y, Or.inr rfl, h⟩

/-- ✱51·236. \(\vdash\colon\ldotp z\in \iotaʻ x\cup \beta.\equiv:z=x.\lor.z\in\beta \quad[(\text{*22·34.*51·15}]\) -/
theorem pm51_236 {B : Set α} {x z : α} : z ∈ ι x ∪ B ↔ z = x ∨ z ∈ B := Iff.rfl

/-- ✱51·237. \[\begin{align}&\vdash\colon\colon \alpha=\iotaʻ x\cup \beta.\supset\colon\ldotp(z)\colon\ldotp z\in\alpha.\equiv:z=x.\lor.z\in\beta\\ &[(\text{*51·236.*10·11.*20·18}]\end{align}\] -/
theorem pm51_237 {A B : Set α} {x : α} : A = ι x ∪ B → ∀ z, z ∈ A ↔ z = x ∨ z ∈ B := by
  rintro rfl z; exact Iff.rfl

/-- ✱51·238. \(\vdash\colon\colon \alpha=\iotaʻ x\cup \beta.\supset\colon\ldotp z\in\alpha.\supset_{z}.\phi z:\equiv:\phi x:z\in\beta.\supset_{z}.\phi z\) -/
theorem pm51_238 {A B : Set α} {x : α} {φ : α → Prop} :
    A = ι x ∪ B → ((∀ z, z ∈ A → φ z) ↔ φ x ∧ ∀ z, z ∈ B → φ z) := by
  rintro rfl
  constructor
  · intro h; exact ⟨h x (Or.inl rfl), fun z hz => h z (Or.inr hz)⟩
  · rintro ⟨hx, hB⟩ z (rfl | hz)
    · exact hx
    · exact hB z hz

/-- ✱51·239. \(\vdash\colon\colon \alpha=\iotaʻ x\cup \beta.\supset\colon\ldotp(\exists z).z\in\alpha.\phi z.\equiv:\phi x.\lor.(\exists z).z\in\beta.\phi z\) -/
theorem pm51_239 {A B : Set α} {x : α} {φ : α → Prop} :
    A = ι x ∪ B → ((∃ z, z ∈ A ∧ φ z) ↔ φ x ∨ ∃ z, z ∈ B ∧ φ z) := by
  rintro rfl
  constructor
  · rintro ⟨z, (rfl | hz), h⟩
    · exact Or.inl h
    · exact Or.inr ⟨z, hz, h⟩
  · rintro (h | ⟨z, hz, h⟩)
    · exact ⟨x, Or.inl rfl, h⟩
    · exact ⟨z, Or.inr hz, h⟩

/-- ✱51·24. \(\vdash\colon\ldotp \iotaʻ y\subset \iotaʻ x\cup \beta.\equiv:y=x.\lor.y\in\beta\) -/
theorem pm51_24 {B : Set α} {x y : α} : ι y ⊆ ι x ∪ B ↔ y = x ∨ y ∈ B :=
  ⟨fun h => h (rfl : y = y), fun h z (hz : z = y) => hz ▸ h⟩

/-- ✱51·25. \(\vdash:\alpha\supset \iotaʻ x\cup \beta.x{\sim}\in\alpha.\supset.\alpha\subset \beta \quad[\text{*51·211.*24·49}]\)

**Status.** proved (reading): transcription error: the e-text prints `α ⊃ ι'x ∪ β` for PM's
`α ⊂ ι'x ∪ β` (as in ✱51·2; the cited ✱24·49 and ✱51·211 concern this inclusion). -/
theorem pm51_25 {A B : Set α} {x : α} : A ⊆ ι x ∪ B ∧ x ∉ A → A ⊆ B := by
  rintro ⟨h, hx⟩ y hy
  rcases h hy with (e | hB)
  · exact absurd ((e : y = x) ▸ hy) hx
  · exact hB

/-- ✱51·3. \(\vdash:y\in\alpha.y\neq x.\equiv.y\in\alpha -\iotaʻ x \quad[\text{*51·15.*22·33·35}]\) -/
theorem pm51_3 {A : Set α} {x y : α} : y ∈ A ∧ y ≠ x ↔ y ∈ A \ ι x := Iff.rfl

/-- ✱51·31. \(\vdash:\exists!\alpha\cap \iotaʻ x.\equiv.\iotaʻ x\subset \alpha.\equiv.\alpha\cap \iotaʻ x=\iotaʻ x.\equiv.x\in\alpha\) -/
theorem pm51_31 {A : Set α} {x : α} :
    (((A ∩ ι x).Nonempty ↔ ι x ⊆ A) ∧ (ι x ⊆ A ↔ A ∩ ι x = ι x)) ∧ (A ∩ ι x = ι x ↔ x ∈ A) := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, (e : y = x)⟩; exact pm51_2.1 (e ▸ hy)
  · intro h; exact ⟨x, h rfl, rfl⟩
  · intro h; exact Set.inter_eq_right.2 h
  · intro h; rw [← h]; exact Set.inter_subset_left
  · intro h; have : x ∈ A ∩ ι x := by rw [h]; exact rfl
    exact this.1
  · intro h; exact Set.inter_eq_right.2 (pm51_2.1 h)

/-- ✱51·34. \(\vdash:x\in\alpha.\equiv.-\alpha\subset-\iotaʻ x \quad[\text{*51·2.*22·81}]\) -/
theorem pm51_34 {A : Set α} {x : α} : x ∈ A ↔ Aᶜ ⊆ (ι x)ᶜ := by
  rw [Set.compl_subset_compl]; exact pm51_2

/-- ✱51·35. \(\vdash:x{\sim}\in\alpha.\equiv.\iotaʻ x\subset-\alpha \quad[\text{*51·2.* 22·35}]\) -/
theorem pm51_35 {A : Set α} {x : α} : x ∉ A ↔ ι x ⊆ Aᶜ :=
  pm51_2 (A := Aᶜ) (x := x)

/-- ✱51·36. \(\vdash:x\sim \in\alpha.\equiv.\alpha\subset-\iotaʻ x \quad[\text{*51·35.*22·811}]\) -/
theorem pm51_36 {A : Set α} {x : α} : x ∉ A ↔ A ⊆ (ι x)ᶜ := by
  rw [pm51_35]; exact Set.subset_compl_comm

/-- ✱51·37. \(\vdash.\alpha=\hat{x}(\iotaʻ x\subset \alpha) \quad[\text{*51·2.*20·33}]\) -/
theorem pm51_37 {A : Set α} : A = {x | ι x ⊆ A} := by
  ext x; exact pm51_2

/-- ✱51·4. \(\vdash:\exists!\alpha.\alpha\subset \iotaʻ x.\equiv.\alpha=\iotaʻ x\) -/
theorem pm51_4 {A : Set α} {x : α} : A.Nonempty ∧ A ⊆ ι x ↔ A = ι x := by
  constructor
  · rintro ⟨⟨y, hy⟩, h⟩
    ext z
    refine ⟨fun hz => h hz, fun (hz : z = x) => ?_⟩
    have : y = x := h hy
    rw [hz, ← this]; exact hy
  · rintro rfl; exact ⟨⟨x, rfl⟩, subset_refl _⟩

/-- ✱51·401. \(\vdash\colon\ldotp \alpha\subset \iotaʻ x.\equiv:\alpha=\Lambda.\lor.\alpha=\iotaʻ x\) -/
theorem pm51_401 {A : Set α} {x : α} : A ⊆ ι x ↔ A = Λ ∨ A = ι x := by
  rw [Null_eq_empty, unitCls_eq_singleton]; exact Set.subset_singleton_iff_eq

/-- ✱51·41. \(\vdash:\iotaʻ x\cup \iotaʻ y=\iotaʻ x\cup \iotaʻ z.\equiv.y=z\) -/
theorem pm51_41 {x y z : α} : ι x ∪ ι y = ι x ∪ ι z ↔ y = z := by
  simp only [unitCls_eq_singleton, Set.singleton_union]
  constructor
  · intro h
    rcases Set.pair_eq_pair_iff.1 h with ⟨-, h⟩ | ⟨rfl, rfl⟩
    · exact h
    · rfl
  · rintro rfl; rfl

/-- ✱51·42. \(\vdash\colon\ldotp \iotaʻ x\cup \iotaʻ y=\iotaʻ z\cup \iotaʻ w.\supset:x=z.y=w.\lor.x=w.y=z\) -/
theorem pm51_42 {x y z w : α} :
    ι x ∪ ι y = ι z ∪ ι w → (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  simp only [unitCls_eq_singleton, Set.singleton_union]
  exact Set.pair_eq_pair_iff.1

/-- ✱51·421. \(\vdash\colon\ldotp x=z.y=w.\lor.x=w.y=z:\supset.\iotaʻ x\cup \iotaʻ y=\iotaʻ z\cup \iotaʻ w \quad[\text{*51·41}]\) -/
theorem pm51_421 {x y z w : α} :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) → ι x ∪ ι y = ι z ∪ ι w := by
  simp only [unitCls_eq_singleton, Set.singleton_union]
  exact Set.pair_eq_pair_iff.2

/-- ✱51·43. \[\begin{align}\vdash\colon\ldotp \iotaʻ x\cup \iotaʻ y=\iotaʻ z\cup \iotaʻw.\equiv:x=z.y=w.\lor.x=w.y=z\\ &[\text{*51·42·421}]\end{align}\] -/
theorem pm51_43 {x y z w : α} :
    ι x ∪ ι y = ι z ∪ ι w ↔ (x = z ∧ y = w) ∨ (x = w ∧ y = z) :=
  ⟨pm51_42, pm51_421⟩

/-- ✱51·51. \(\vdash:\alpha=\iotaʻ x.\equiv.x=\breve{\iota}ʻ\alpha.\equiv.x\breve{\iota}\alpha\) -/
theorem pm51_51 {A : Set α} {x : α} :
    (A = ι x ↔ Desc iota˘ A (fun b => x = b)) ∧ (Desc iota˘ A (fun b => x = b) ↔ iota˘ x A) := by
  rw [desc_iota_cnv_iff]
  refine ⟨⟨fun h => ⟨x, h, rfl⟩, ?_⟩, ⟨?_, fun h => ⟨x, h, rfl⟩⟩⟩
  · rintro ⟨b, h, rfl⟩; exact h
  · rintro ⟨b, h, rfl⟩; exact h

/-- ✱51·511. \(\vdash.\breve{\iota}ʻ \iotaʻ x=x \quad\left[\text{*51·51} \frac{\iotaʻ x}{\alpha}.\,\text{*20·2}\right]\) -/
theorem pm51_511 {x : α} : Desc iota˘ (ι x) (fun b => b = x) :=
  desc_iota_cnv_iff.2 ⟨x, rfl, rfl⟩

/-- ✱51·52. \(\vdash:\text{E}!\breve{\iota}ʻ \alpha.\equiv.\alpha=\iotaʻ\breve{\iota}ʻ\alpha \quad\left[\text{*51·51}\, \frac{\breve{\iota}ʻ\alpha}{x}.\,\text{*14·21·18}\right]\) -/
theorem pm51_52 {A : Set α} : EDesc iota˘ A ↔ Desc iota˘ A (fun b => A = ι b) := by
  rw [edesc_iota_cnv_iff, desc_iota_cnv_iff]
  exact ⟨fun ⟨b, h⟩ => ⟨b, h, h⟩, fun ⟨b, h, _⟩ => ⟨b, h⟩⟩

/-- ✱51·53. \(\vdash:\text{E}!\breve{\iota}ʻ\alpha.\equiv.\breve{\iota}ʻ\alpha\in\alpha \quad[\text{*51·52·16.*14·21·18}]\) -/
theorem pm51_53 {A : Set α} : EDesc iota˘ A ↔ Desc iota˘ A (fun b => b ∈ A) := by
  rw [edesc_iota_cnv_iff, desc_iota_cnv_iff]
  exact ⟨fun ⟨b, h⟩ => ⟨b, h, h ▸ rfl⟩, fun ⟨b, h, _⟩ => ⟨b, h⟩⟩

/-- ✱51·54. \(\vdash:\text{E}!\breve{\iota}ʻ\alpha.\equiv.(\exists x).\alpha=\iotaʻ x \quad[\text{*51·51.*14·204}]\) -/
theorem pm51_54 {A : Set α} : EDesc iota˘ A ↔ ∃ x, A = ι x := edesc_iota_cnv_iff

/-- ✱51·55. \(\vdash:\text{E}!\breve{\iota}ʻ\alpha.\equiv.\text{E}!(℩x)(x\in\alpha)\) -/
theorem pm51_55 {A : Set α} : EDesc iota˘ A ↔ EBang (fun x => x ∈ A) := by
  rw [edesc_iota_cnv_iff]
  exact ⟨fun ⟨b, h⟩ => ⟨b, eq_unitCls_iff.1 h⟩, fun ⟨b, h⟩ => ⟨b, eq_unitCls_iff.2 h⟩⟩

/-- ✱51·56. \(\vdash:b=\breve{\iota}ʻ\hat{y}(\phi y).\equiv.\hat{y}(\phi y)=\iotaʻ b.\equiv.b=({℩}x)(\phi x)\) -/
theorem pm51_56 {φ : α → Prop} {b : α} :
    (Desc iota˘ {y | φ y} (fun c => b = c) ↔ {y | φ y} = ι b) ∧
      ({y | φ y} = ι b ↔ TheIs φ (fun c => b = c)) := by
  refine ⟨(pm51_51.1).symm, ?_⟩
  rw [eq_unitCls_iff]
  constructor
  · intro h; exact ⟨b, h, rfl⟩
  · rintro ⟨c, h, rfl⟩; exact h

/-- ✱51·57. \(\vdash:\text{E}!\breve{\iota}ʻ\hat{y}(\phi y).\equiv.\breve{\iota}ʻ\hat{y}(\phi y)=({℩}x)(\phi x).\equiv.\text{E}!({℩}x)(\phi x)\) -/
theorem pm51_57 {φ : α → Prop} :
    (EDesc iota˘ {y | φ y} ↔ Desc iota˘ {y | φ y} (fun b => TheIs φ (fun c => b = c))) ∧
      (Desc iota˘ {y | φ y} (fun b => TheIs φ (fun c => b = c)) ↔ EBang φ) := by
  have key : Desc iota˘ {y | φ y} (fun b => TheIs φ (fun c => b = c)) ↔ EBang φ := by
    rw [desc_iota_cnv_iff]
    constructor
    · rintro ⟨b, -, c, hc, -⟩; exact ⟨c, hc⟩
    · rintro ⟨c, hc⟩; exact ⟨c, eq_unitCls_iff.2 hc, c, hc, rfl⟩
  refine ⟨?_, key⟩
  rw [key]; exact pm51_55

/-- ✱51·58. \(\vdash:\text{E}!\breve{\iota}ʻ\alpha.\equiv.\breve{\iota}ʻ\alpha=({℩}x)(x\in\alpha) \quad[\text{*51·57.*20·3.*14·272}]\) -/
theorem pm51_58 {A : Set α} :
    EDesc iota˘ A ↔ Desc iota˘ A (fun b => TheIs (fun x => x ∈ A) (fun c => b = c)) :=
  (pm51_57 (φ := fun x => x ∈ A)).1

/-- ✱51·59. \(\vdash:\psi{\breve{\iota}ʻ\hat{z}(\phi z)}.\equiv.\psi({℩}x)(\phi x) \quad[\text{*51· 56.*14·205}]\) -/
theorem pm51_59 {φ : α → Prop} {ψ : α → Prop} : Desc iota˘ {z | φ z} ψ ↔ TheIs φ ψ :=
  desc_iota_cnv _ _

/-!
## [✱52] The cardinal number 1

*(Vol. 1, p. 363)*

> *Summary of *52.*
>
> In this number, we introduce the cardinal number 1, defined as the class of all unit classes. The fact that 1 so defined is a cardinal number is not relevant at present, and cannot of course be proved until "cardinal number" has been defined. For the present, therefore, 1 is to be regarded simply as the class of all unit classes, unit classes being such classes as are of the form \(\iotaʻx\) for some \(x\).
>
> Like \(\Lambda\) and \(\text{V}\), 1 is ambiguous as to type: it means "all unit classes of the type in question." The symbol "\(1(\alpha)\)," where \(\alpha\) is a type, will mean "all unit classes whose sole members belong to the type \(\alpha\)" (cf. *65). Thus *e.g.* "\(\xi\in 1(\text{Indiv}\))" will mean "\(\xi\) is a class consisting of one individual," if "\(\text{Indiv}\)" stands for the class of individuals.
>
> …

**Lean reading.** The cardinal number 1 is `one : Set (Set α)`, the class of unit classes `ι x` of `α`-things
(✱52·01, by `rfl`); its type is fixed by the context (typical ambiguity, Basic §4). `D'ι` is
`dom iota`, `ι''α` is `iota ʻʻ A`, and `ῐ'α` is kept as a description (`Desc iota˘ A`). The
products `α, β ∈ 1` are `A ∈ one ∧ B ∈ one` (✱20·04), `1 ∪ ι'Λ` is `one ∪ ι Λ`. ✱52·23 and the
first half of ✱52·24 need a member of `α` (`[Nonempty α]`), since `1` is null for an empty type.
The e-text omits the definiendum of ✱52·01, repeats `1 ≠ Λ ∩ Cls` in ✱52·24 (for
`1 ≠ V ∩ Cls`), and prints `⊃` for `⊂` in ✱52·3·31; these are read as PM has them.

**Status.** proved (all propositions; ✱52·01 definition (the e-text omits its definiendum); ✱52·23,
✱52·24, ✱52·3, ✱52·31 proved (reading), see their docstrings).
-/

/-- ✱52·46. \(\vdash\colon\ldotp \alpha ,\beta \in 1\ldotp \supset : \alpha \subset \beta \ldotp \equiv \ldotp \alpha = \beta \ldotp \equiv \ldotp \exists !(\alpha \cap \beta )\) -/
theorem pm52_46 {A B : Set α} :
    A ∈ one ∧ B ∈ one → ((A ⊆ B ↔ A = B) ∧ (A = B ↔ (A ∩ B).Nonempty)) := by
  rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  have e1 : ι a ⊆ ι b ↔ a = b := pm51_2.symm
  have e2 : ι a = ι b ↔ a = b := ⟨fun h => unitCls_injective h, fun h => by rw [h]⟩
  have e3 : (ι a ∩ ι b).Nonempty ↔ a = b :=
    ⟨fun ⟨_, (h1 : _ = a), (h2 : _ = b)⟩ => h1.symm.trans h2, fun h => ⟨a, rfl, h⟩⟩
  exact ⟨e1.trans e2.symm, e2.trans e3.symm⟩

/-- ✱52·01 (Df). \(\hat{\alpha }\{(\exists x) \ldotp \alpha = \iota ʻx\}\quad \text{Df}\)

**Status.** definition: the e-text omits the definiendum; PM has `1 = α̂{(∃x) . α = ι'x} Df`, as the
Summary of ✱52, the Summary of Section A and ✱52·1 show. -/
theorem pm52_01 : (one : Set (Set α)) = {A | ∃ x, A = ι x} := rfl

/-- ✱52·1. \(\vdash: \alpha \in 1 \ldotp \equiv \ldotp (\exists x) \ldotp \alpha = \iota ʻx\qquad\qquad\quad [*20·3.(*52·01)]\) -/
theorem pm52_1 {A : Set α} : A ∈ one ↔ ∃ x, A = ι x := Iff.rfl

/-- ✱52·11. \(\vdash\colon\ldotp \alpha \in 1 \ldotp \equiv : (\exists x): y \in \alpha \ldotp \equiv _{y} \ldotp y = x\quad [*52·1.*51·14]\) -/
theorem pm52_11 {A : Set α} : A ∈ one ↔ ∃ x, ∀ y, y ∈ A ↔ y = x := mem_one_iff

/-- ✱52·12. \(\vdash: \hat{z} (\phi z) \in 1 \ldotp \equiv \ldotp \text{E}! ({℩} x) (\phi x)\) -/
theorem pm52_12 {φ : α → Prop} : {z | φ z} ∈ one ↔ EBang φ := mem_one_iff

/-- ✱52·13. \(\vdash \ldotp 1 = \text{D}ʻ\iota \) -/
theorem pm52_13 : (one : Set (Set α)) = dom iota := by
  ext A; exact Iff.rfl

/-- ✱52·14. \(\vdash.1 = \iota ʻʻ\text{V} \quad [*52·13.*37·28]\) -/
theorem pm52_14 : (one : Set (Set α)) = iota ʻʻ V := by
  ext A; simp [mem_one']

/-- ✱52·15. \(\vdash: \alpha \in 1 \ldotp \equiv \ldotp \text{E}! \breve{\iota }ʻ\alpha \quad[\text{*51·54.*52·1}]\) -/
theorem pm52_15 {A : Set α} : A ∈ one ↔ EDesc iota˘ A := edesc_iota_cnv_iff.symm

/-- ✱52·16. \(\vdash\colon\ldotp \alpha \in 1 \ldotp \equiv :\exists !\alpha : x, y \in \alpha \ldotp \supset _{x,y} \ldotp x = y \quad[\text{*52·15.*51·55.*14·203}]\) -/
theorem pm52_16 {A : Set α} : A ∈ one ↔ A.Nonempty ∧ ∀ x y, x ∈ A ∧ y ∈ A → x = y := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, rfl⟩, fun x y ⟨(hx : x = a), (hy : y = a)⟩ => hx.trans hy.symm⟩
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨a, eq_unitCls_iff.2 fun y => ⟨fun hy => h y a ⟨hy, ha⟩, fun e => e ▸ ha⟩⟩

/-- ✱52·17. \(\vdash: \alpha \in 1 \ldotp \equiv \ldotp \breve{\iota }ʻ\alpha = ({℩}x) (x \in \alpha ) \quad\text{[*51·58.*52·15}]\) -/
theorem pm52_17 {A : Set α} :
    A ∈ one ↔ Desc iota˘ A (fun b => TheIs (fun x => x ∈ A) (fun c => b = c)) :=
  pm52_15.trans pm51_58

/-- ✱52·171. \(\vdash: \alpha \in 1 \ldotp \equiv \ldotp \text{E}! ({℩}x) (x \in \alpha ) \quad[\text{*51·55.*52·15}]\) -/
theorem pm52_171 {A : Set α} : A ∈ one ↔ EBang (fun x => x ∈ A) := pm52_15.trans pm51_55

/-- ✱52·172. \(\vdash: \alpha \in 1 \ldotp \equiv \ldotp \iota ʻ\breve{\iota }ʻ\alpha = \alpha \quad[\text{*51·52,*52·15}]\) -/
theorem pm52_172 {A : Set α} : A ∈ one ↔ Desc iota˘ A (fun b => ι b = A) := by
  rw [desc_iota_cnv_iff]
  exact ⟨fun ⟨b, h⟩ => ⟨b, h, h.symm⟩, fun ⟨b, h, _⟩ => ⟨b, h⟩⟩

/-- ✱52·173. \(\vdash: \alpha \in 1 \ldotp \equiv \ldotp \breve{\iota }ʻ\alpha \in \alpha \quad[\text{*51·53.*52·5}]\)

**Status.** proved: the e-text cites `✱52·5` for ✱52·15. -/
theorem pm52_173 {A : Set α} : A ∈ one ↔ Desc iota˘ A (fun b => b ∈ A) := pm52_15.trans pm51_53

/-- ✱52·18. \(\vdash\colon\ldotp \alpha \in 1 \ldotp \equiv : (\exists x) : x \in \alpha : y \in \alpha \ldotp \supset _{y} \ldotp y = x\) -/
theorem pm52_18 {A : Set α} : A ∈ one ↔ ∃ x, x ∈ A ∧ ∀ y, y ∈ A → y = x := by
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl, fun y hy => hy⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, eq_unitCls_iff.2 fun y => ⟨h y, fun e => e ▸ ha⟩⟩

/-- ✱52·181. \(\vdash\colon\ldotp \alpha \sim \in 1 \ldotp \equiv : x\in \alpha \ldotp \supset_{x}\ldotp (\exists y)y\in \alpha \ldotp y\neq x \quad[\text{*52·18.*10·51}]\) -/
theorem pm52_181 {A : Set α} : A ∉ one ↔ ∀ x, x ∈ A → ∃ y, y ∈ A ∧ y ≠ x := by
  rw [pm52_18]; push Not; exact Iff.rfl

/-- ✱52·2. \(\vdash \ldotp 1 \subset \text{Cls}\) -/
theorem pm52_2 : (one : Set (Set α)) ⊆ Cls := fun _ _ => mem_Cls'.2 trivial

/-- ✱52·21. \(\vdash.\Lambda{\sim}\in\text{1}\) -/
theorem pm52_21 : (Λ : Set α) ∉ one := by
  rintro ⟨x, h⟩
  have : x ∈ (Λ : Set α) := by rw [h]; exact rfl
  exact this rfl

/-- ✱52·22. \(\vdash.\iotaʻ x\in\text{1} \quad[\text{*51·12.*14·28.*10·24.*52·1}]\) -/
theorem pm52_22 {x : α} : ι x ∈ one := ⟨x, rfl⟩

/-- ✱52·23. \(\vdash.\exists!\text{1}.\exists!-\text{1}\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): for an empty
type `α` the class `1` of its unit classes is null, so `[Nonempty α]` is added. -/
theorem pm52_23 [Nonempty α] : (one : Set (Set α)).Nonempty ∧ (oneᶜ : Set (Set α)).Nonempty :=
  let ⟨x⟩ := ‹Nonempty α›
  ⟨⟨ι x, pm52_22⟩, ⟨Λ, pm52_21⟩⟩

/-- ✱52·24. \(\vdash.\text{1}\neq\Lambda\cap\text{Cls}.\text{1}\neq\Lambda\cap\text{Cls} \quad[\text{*52·23.*24·54.*24·17.Transp}]\)

**Status.** proved (reading): transcription error: the e-text prints `1 ≠ Λ ∩ Cls` twice; PM has
`1 ≠ Λ ∩ Cls . 1 ≠ V ∩ Cls`, the two halves following from `∃!1` and `∃!−1` of ✱52·23
(cited). The first half needs `[Nonempty α]`, as ✱52·23 (PM assumes every type has a
member). -/
theorem pm52_24 [Nonempty α] :
    (one : Set (Set α)) ≠ Λ ∩ Cls ∧ (one : Set (Set α)) ≠ V ∩ Cls := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := (pm52_23 (α := α)).1
    rw [h] at hA
    exact hA.1 rfl
  · intro h
    have : (Λ : Set α) ∈ (V ∩ Cls : Set (Set α)) := ⟨rfl, mem_Cls'.2 trivial⟩
    rw [← h] at this
    exact pm52_21 this

/-- ✱52·3. \(\vdash.\iotaʻʻ\alpha\supset\text{1}\)

**Status.** proved (reading): transcription error: the e-text prints `ι''α ⊃ 1` for PM's
`ι''α ⊂ 1` (the demonstration ends with `ι''α ⊂ 1`). -/
theorem pm52_3 {A : Set α} : iota ʻʻ A ⊆ one := by
  rintro B ⟨y, -, hB⟩; exact ⟨y, hB⟩

/-- ✱52·31. \(\vdash:\kappa\supset\text{1}.\equiv.(\exists \alpha).\kappa=\iotaʻʻ\alpha\)

**Status.** proved (reading): transcription error: the e-text prints `κ ⊃ 1` for PM's `κ ⊂ 1` (the
demonstration reads `κ ⊂ 1 . ≡ . κ ⊂ ι''V`); with `1 ⊂ κ` it would be false. -/
theorem pm52_31 {K : Set (Set α)} : K ⊆ one ↔ ∃ A, K = iota ʻʻ A := by
  constructor
  · intro h
    refine ⟨{x | ι x ∈ K}, ?_⟩
    ext B
    constructor
    · intro hB
      obtain ⟨y, rfl⟩ := h hB
      exact ⟨y, hB, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact hy
  · rintro ⟨A, rfl⟩; exact pm52_3

/-- ✱52·4. \(\vdash\colon\ldotp \alpha\in\text{1}\cup \iotaʻ\Lambda.\equiv:x,y\in\alpha.\supset_{x,y}.x=y\) -/
theorem pm52_4 {A : Set α} : A ∈ one ∪ ι Λ ↔ ∀ x y, x ∈ A ∧ y ∈ A → x = y := by
  constructor
  · rintro (⟨a, rfl⟩ | (h : A = Λ))
    · rintro x y ⟨(hx : x = a), (hy : y = a)⟩; exact hx.trans hy.symm
    · rintro x y ⟨hx, -⟩; rw [h] at hx; exact absurd rfl hx
  · intro h
    by_cases hA : A.Nonempty
    · exact Or.inl (pm52_16.2 ⟨hA, h⟩)
    · right
      show A = Λ
      rw [Null_eq_empty]; exact Set.not_nonempty_iff_eq_empty.1 hA

/-- ✱52·41. \(\vdash:\exists !\alpha.\alpha{\sim}\in\text{1}.\equiv.(\exists x,y).x,y\in\alpha.x\neq y\) -/
theorem pm52_41 {A : Set α} : A.Nonempty ∧ A ∉ one ↔ ∃ x y, (x ∈ A ∧ y ∈ A) ∧ x ≠ y := by
  rw [pm52_16]
  constructor
  · rintro ⟨hA, h⟩
    by_contra hc
    push Not at hc
    exact h ⟨hA, hc⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, hxy⟩
    exact ⟨⟨x, hx⟩, fun ⟨_, h⟩ => hxy (h x y ⟨hx, hy⟩)⟩

/-- ✱52·42. \(\vdash\colon\ldotp \alpha\in\text{1}.\supset: \exists !\alpha\cap\beta.\equiv.\alpha\cap\beta\in\text{1} \) -/
theorem pm52_42 {A B : Set α} : A ∈ one → ((A ∩ B).Nonempty ↔ A ∩ B ∈ one) := by
  rintro ⟨a, rfl⟩
  constructor
  · rintro ⟨z, (hz : z = a), hB⟩
    subst hz
    exact ⟨z, Set.inter_eq_left.2 (pm51_2.1 hB)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; exact rfl⟩

/-- ✱52·43. \(\vdash:\alpha\in\text{1}. \exists!\alpha\cap\beta.\equiv.\alpha\in\text{1}.\alpha\cap \beta\in\text{1} \quad[\text{*52· 42.*5·32}]\) -/
theorem pm52_43 {A B : Set α} : A ∈ one ∧ (A ∩ B).Nonempty ↔ A ∈ one ∧ A ∩ B ∈ one :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, (pm52_42 h1).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (pm52_42 h1).2 h2⟩⟩

/-- ✱52·44. \(\vdash\colon\ldotp \alpha\in\text{1}.\supset: \exists !\alpha\cap\beta.\equiv.\alpha\subset\beta.\equiv.\alpha\cap\beta=\alpha\) -/
theorem pm52_44 {A B : Set α} :
    A ∈ one → (((A ∩ B).Nonempty ↔ A ⊆ B) ∧ (A ⊆ B ↔ A ∩ B = A)) := by
  rintro ⟨a, rfl⟩
  refine ⟨⟨?_, fun h => ⟨a, rfl, h rfl⟩⟩, ⟨Set.inter_eq_left.2, fun h => h ▸ Set.inter_subset_right⟩⟩
  rintro ⟨z, (hz : z = a), hB⟩
  subst hz
  exact pm51_2.1 hB

/-- ✱52·45. \(\vdash\colon\colon\alpha,\beta\in\text{1}.\supset\colon\ldotp\alpha\subset\beta\cup\gamma.\equiv:\alpha=\beta.\lor.\alpha\subset\gamma\) -/
theorem pm52_45 {A B G : Set α} :
    A ∈ one ∧ B ∈ one → (A ⊆ B ∪ G ↔ A = B ∨ A ⊆ G) := by
  rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  rw [pm51_24, ← pm51_2]
  exact or_congr ⟨fun h => by rw [h], fun h => unitCls_injective h⟩ Iff.rfl

/-- ✱52·6. \(\vdash\colon\ldotp \alpha\in\text{1}.\supset:x\in\alpha.\equiv.\iotaʻ x=\alpha.\equiv.x=\breve{\iota}ʻ\alpha\) -/
theorem pm52_6 {A : Set α} {x : α} :
    A ∈ one → ((x ∈ A ↔ ι x = A) ∧ (ι x = A ↔ Desc iota˘ A (fun b => x = b))) := by
  rintro ⟨a, rfl⟩
  rw [desc_iota_cnv_iff]
  refine ⟨⟨fun (h : x = a) => by rw [h], fun h => unitCls_injective h⟩, ⟨fun h => ⟨x, h.symm, rfl⟩,
    ?_⟩⟩
  rintro ⟨b, h, rfl⟩; exact h.symm

/-- ✱52·601. \(\vdash\colon\colon \alpha\in\text{1}.\supset\colon\ldotp \phi(\breve{\iota}ʻ\alpha).\equiv:x\in\alpha.\supset_{x}.\phi x:\equiv:(\exists x).x\in\alpha.\phi x\) -/
theorem pm52_601 {A : Set α} {φ : α → Prop} :
    A ∈ one →
      ((Desc iota˘ A φ ↔ ∀ x, x ∈ A → φ x) ∧ ((∀ x, x ∈ A → φ x) ↔ ∃ x, x ∈ A ∧ φ x)) := by
  rintro ⟨a, rfl⟩
  rw [desc_iota_cnv_iff]
  refine ⟨⟨?_, fun h => ⟨a, rfl, h a rfl⟩⟩, ⟨fun h => ⟨a, rfl, h a rfl⟩, ?_⟩⟩
  · rintro ⟨b, hb, h⟩ x (hx : x = a)
    rw [hx, unitCls_injective hb]; exact h
  · rintro ⟨x, (hx : x = a), h⟩ y (hy : y = a)
    rw [hy, ← hx]; exact h

/-- ✱52·602. \[\begin{align}\vdash\colon\ldotp\hat{z}(\phi z)\in\text{1}.\supset:\psi(℩x)(\phi x).\equiv.\phi x\supset_{x}\psi x.&\equiv.(\exists x).\phi x.\psi x\\ &\quad[\text{*52·12.*14·26}]\end{align}\] -/
theorem pm52_602 {φ ψ : α → Prop} :
    {z | φ z} ∈ one →
      ((TheIs φ ψ ↔ ∀ x, φ x → ψ x) ∧ ((∀ x, φ x → ψ x) ↔ ∃ x, φ x ∧ ψ x)) := by
  intro h
  have := pm52_601 (A := {z | φ z}) (φ := ψ) h
  rw [pm51_59] at this
  exact this

/-- ✱52·61. \(\vdash\colon\ldotp \alpha\in\text{1}.\supset:\breve{\iota}ʻ \alpha\in\beta.\equiv.\alpha\subset \beta.\equiv.\exists!(\alpha\cap \beta) \quad\left[\text{*52·601} \frac{x\, \in \, \beta}{\phi x}\right]\) -/
theorem pm52_61 {A B : Set α} :
    A ∈ one → ((Desc iota˘ A (fun b => b ∈ B) ↔ A ⊆ B) ∧ (A ⊆ B ↔ (A ∩ B).Nonempty)) := by
  intro h
  refine ⟨(pm52_601 h).1.trans ⟨fun h' x hx => h' x hx, fun h' x hx => h' hx⟩, ?_⟩
  exact ((pm52_44 h).1).symm

/-- ✱52·62. \(\vdash\colon\ldotp \alpha,\beta\in\text{1}.\supset:\alpha=\beta.\equiv.\breve{\iota}ʻ \alpha=\breve{\iota}ʻ \beta\) -/
theorem pm52_62 {A B : Set α} :
    A ∈ one ∧ B ∈ one → (A = B ↔ Desc iota˘ A (fun b => Desc iota˘ B (fun c => b = c))) := by
  rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  simp only [desc_iota_cnv_iff]
  constructor
  · intro h; exact ⟨a, rfl, a, h.symm, rfl⟩
  · rintro ⟨a', ha, b', hb, rfl⟩
    rw [ha, hb]

/-- ✱52·63. \(\vdash:\alpha,\beta\in\text{1}.\alpha\neq \beta.\supset.\alpha\cap \beta=\Lambda \quad[\text{*52·46.Transp}]\) -/
theorem pm52_63 {A B : Set α} : (A ∈ one ∧ B ∈ one) ∧ A ≠ B → A ∩ B = Λ := by
  rintro ⟨h, hne⟩
  rw [Null_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  intro hn
  exact hne (((pm52_46 h).2).2 hn)

/-- ✱52·64. \(\vdash:\alpha\in\text{1}.\supset.\alpha\cap \beta\in\text{1}\cup \iotaʻ\Lambda\) -/
theorem pm52_64 {A B : Set α} : A ∈ one → A ∩ B ∈ one ∪ ι Λ := by
  intro h
  rw [pm52_4]
  rintro x y ⟨⟨hx, -⟩, ⟨hy, -⟩⟩
  exact (pm52_16.1 h).2 x y ⟨hx, hy⟩

/-- ✱52·7. \(\vdash\colon\ldotp \beta-\alpha\in\text{1}.\alpha\subset\xi.\xi\subset\beta.\supset:\xi=\alpha.\lor.\xi=\beta\) -/
theorem pm52_7 {A B X : Set α} : (B \ A ∈ one ∧ A ⊆ X) ∧ X ⊆ B → X = A ∨ X = B := by
  rintro ⟨⟨⟨b, hb⟩, hAX⟩, hXB⟩
  have hb' : ∀ z, z ∈ B ∧ z ∉ A ↔ z = b := eq_unitCls_iff.1 hb
  by_cases hbX : b ∈ X
  · right
    ext z
    refine ⟨fun hz => hXB hz, fun hz => ?_⟩
    by_cases hzA : z ∈ A
    · exact hAX hzA
    · rw [(hb' z).1 ⟨hz, hzA⟩]; exact hbX
  · left
    ext z
    refine ⟨fun hz => ?_, fun hz => hAX hz⟩
    by_contra hzA
    have : z = b := (hb' z).1 ⟨hXB hz, hzA⟩
    exact hbX (this ▸ hz)

/-!
## [✱53] Miscellaneous propositions involving unit classes

*(Vol. 1, p. 368)*

> *Summary of* *53.
>
> The propositions to be given in this number are mostly such as would have come more naturally at an earlier stage, but could not be given sooner because they involved unit classes. It is to be observed that \(\iotaʻx\cup\iotaʻy\) is the class consisting of the members \(x\) and \(y\), while \(\iotaʻx\uparrow\iotaʻy\) is the relation which holds only between \(x\) and \(y\). If \(\alpha\) and \(\beta\) are classes, \(\iotaʻ\alpha\cup\iotaʻ\beta\) is a class of classes, its members being \(\alpha\) and \(\beta\). If \(R\) and \(S\) are relations, \(\iotaʻR\uparrow\iotaʻS\) is a relation of relations; and so on.
>
> The present number begins by connecting products and sums \(pʻ\kappa\), \(sʻ\kappa\), \(\dot{p}ʻ\lambda\), \(\dot{s}ʻ\lambda\), in cases where the members of \(\kappa\) or \(\lambda\) are specified, with the products or sums \(\alpha\cap\beta\), \(\alpha\cup\beta\), \(R\dot{\cap}S\), \(R\unicode{x228d} S\). We have
>
> *53·01. \(\vdash.pʻ\iotaʻ\alpha=\alpha\)
>
> *53·1. \(\vdash.pʻ(\iotaʻ\alpha\cup\iotaʻ\beta)=\alpha\cap\beta\)
>
> *53·14. \(\vdash.pʻ(\kappa\cup\iotaʻ\alpha) =pʻ\kappa\cap\alpha\)
>
> with similar propositions for \(s\), \(\dot{p}\) and \(\dot{s}\).
>
> …

**Lean reading.** Products and sums of classes and relations are `prodCls`, `sumCls` (`p'κ`, `s'κ`) and `prodRel`,
`sumRel` (`ṗ'λ`, `ṡ'λ`); unit classes of classes or relations are `ι A`, `ι R` at the appropriate
types. ✱53·33–·35 use `s` as a *relation* (`s''ι'κ`): by the convention of the Summary of
Section E the relation whose descriptive function is `s'κ` is `ûκ̂(u = s'κ)`, i.e.
`graph sumCls`. `R⃗''α`, `R⃖''α`, `D'R⃗` are `Rfwd R ʻʻ A`, `Rbwd R ʻʻ A`, `dom (Rfwd R)`, and
`ι'R'x` (✱53·31·32, with `E!R'x`) keeps the description `R'x` (`Desc R x (fun b => … ι b …)`);
`ῐ'R⃗'y` (✱53·4) is `Desc iota˘ (refs R y)`. In ✱53·6 the formula (`R⃗''α` and `R⃖''α` with the
same `α`) forces `R` to be homogeneous. The e-text prints a stray `ι'` in ✱53·04, `⊂` for the
principal `⊃` of ✱53·25, `R⃗` for `R⃖` in the second half of ✱53·6, and `ᗡ'R` for `D'R` in ✱53·613;
these are read as PM has them.

**Status.** proved (all propositions; ✱53·25, ✱53·6, ✱53·613 proved (reading), see their docstrings).
-/

/-- ✱53·01. \(\vdash.pʻ\iotaʻ\alpha=\alpha\) -/
theorem pm53_01 {A : Set α} : prodCls (ι A) = A := by
  ext x; simp

/-- ✱53·02. \(\vdash.sʻ\iotaʻ\alpha=\alpha\) -/
theorem pm53_02 {A : Set α} : sumCls (ι A) = A := by
  ext x; simp

/-- ✱53·03. \(\vdash.\dot{p}ʻ\iotaʻR=R \quad[\text{Proof as in *53·01}]\) -/
theorem pm53_03 {R : α → β → Prop} : prodRel (ι R) = R := by
  funext x y; apply propext; simp

/-- ✱53·04. \(\vdash.\dot{s}ʻ\iotaʻR=R \iotaʻ \quad[\text{Proof as in *53·02}]\)

**Status.** proved: the e-text prints a stray `ι'` after the right-hand side `R`. -/
theorem pm53_04 {R : α → β → Prop} : sumRel (ι R) = R := by
  funext x y; apply propext; simp

/-- ✱53·1. \(\vdash .pʻ (\iotaʻ\alpha\cup\iotaʻ\beta)=\alpha\cap \beta\) -/
theorem pm53_1 {A B : Set α} : prodCls (ι A ∪ ι B) = A ∩ B := by
  ext x; simp [or_imp, forall_and]

/-- ✱53·11. \(\vdash.sʻ(\iotaʻ\alpha\cup\iotaʻ\beta)=\alpha\cup\beta\) -/
theorem pm53_11 {A B : Set α} : sumCls (ι A ∪ ι B) = A ∪ B := by
  ext x; simp [or_and_right, exists_or]

/-- ✱53·12. \(\vdash.\dot{p}ʻ (\iotaʻ R\cup \iotaʻ S)=R\dot{\cap}S \quad[\text{*41·18.*53·03}]\) -/
theorem pm53_12 {R S : α → β → Prop} : prodRel (ι R ∪ ι S) = R ⩀ S := by
  funext x y; apply propext; simp [or_imp, forall_and]

/-- ✱53·13. \(\vdash.\dot{s}ʻ(\iotaʻ R\cup \iotaʻ S)=R\unicode{x228d} S \quad[\text{*41·171.*53·04}]\) -/
theorem pm53_13 {R S : α → β → Prop} : sumRel (ι R ∪ ι S) = R ⊍ S := by
  funext x y; apply propext; simp [or_and_right, exists_or]

/-- ✱53·14. \(\vdash.pʻ (\kappa\cup\iotaʻ\alpha)=pʻ\kappa\cap\alpha\) -/
theorem pm53_14 {K : Set (Set α)} {A : Set α} : prodCls (K ∪ ι A) = prodCls K ∩ A := by
  ext x; simp [or_imp, forall_and]

/-- ✱53·15. \(\vdash.sʻ (\kappa\cup \iotaʻ \alpha)=sʻ \kappa\cup \alpha \quad[\text{Proof as in *53·14}]\) -/
theorem pm53_15 {K : Set (Set α)} {A : Set α} : sumCls (K ∪ ι A) = sumCls K ∪ A := by
  ext x; simp [or_and_right, exists_or]

/-- ✱53·16. \(\vdash.\dot{p}ʻ (\lambda\cup \iotaʻ R)=\dot{p}ʻ \lambda\dot{cap}R \quad[\text{Proof as in *53·14}]\) -/
theorem pm53_16 {L : Set (α → β → Prop)} {R : α → β → Prop} :
    prodRel (L ∪ ι R) = prodRel L ⩀ R := by
  funext x y; apply propext; simp [or_imp, forall_and]

/-- ✱53·17. \(\vdash.\dot{s}ʻ (\lambda\cup \iotaʻ R)=\dot{s}ʻ \lambda\unicode{x228d} R \quad[\text{Proof as in *53·14}]\) -/
theorem pm53_17 {L : Set (α → β → Prop)} {R : α → β → Prop} :
    sumRel (L ∪ ι R) = sumRel L ⊍ R := by
  funext x y; apply propext; simp [or_and_right, exists_or]

/-- ✱53·18. \(\vdash.sʻ (\alpha-\iotaʻ\Lambda)=sʻ \alpha\) -/
theorem pm53_18 {K : Set (Set α)} : sumCls (K \ ι Λ) = sumCls K := by
  ext x
  constructor
  · rintro ⟨B, ⟨hB, -⟩, hx⟩; exact ⟨B, hB, hx⟩
  · rintro ⟨B, hB, hx⟩
    refine ⟨B, ⟨hB, fun (e : B = Λ) => ?_⟩, hx⟩
    rw [e] at hx; exact hx rfl

/-- ✱53·181. \(\vdash.\dot{s}ʻ (\lambda-\iotaʻ\dot{\Lambda})=\dot{s}ʻ \lambda \quad[\text{Proof as in *53·18}]\) -/
theorem pm53_181 {L : Set (α → β → Prop)} : sumRel (L \ ι rNull) = sumRel L := by
  funext x y; apply propext
  constructor
  · rintro ⟨R, ⟨hR, -⟩, h⟩; exact ⟨R, hR, h⟩
  · rintro ⟨R, hR, h⟩
    refine ⟨R, ⟨hR, fun (e : R = rNull) => ?_⟩, h⟩
    rw [e] at h; exact rNull_apply _ _ h

/-- ✱53·2. \(\vdash:\kappa\in\text{1}.\supset.\breve{\iota}ʻ\kappa=pʻ\kappa=sʻ\kappa\) -/
theorem pm53_2 {K : Set (Set α)} :
    K ∈ one → Desc iota˘ K (fun b => b = prodCls K) ∧ prodCls K = sumCls K := by
  rintro ⟨A, rfl⟩
  exact ⟨desc_iota_cnv_iff.2 ⟨A, rfl, pm53_01.symm⟩, pm53_01.trans pm53_02.symm⟩

/-- ✱53·21. \(\vdash:\lambda\in\text{1}.\supset.\breve{\iota}ʻ \lambda=\dot{p}ʻ \lambda=\dot{s}ʻ \lambda \quad[\text{Similar proof}]\)

**Status.** proved: "Similar proof" (✱53·03·04 for ✱53·01·02). -/
theorem pm53_21 {L : Set (α → β → Prop)} :
    L ∈ one → Desc iota˘ L (fun b => b = prodRel L) ∧ prodRel L = sumRel L := by
  rintro ⟨R, rfl⟩
  exact ⟨desc_iota_cnv_iff.2 ⟨R, rfl, pm53_03.symm⟩, pm53_03.trans pm53_04.symm⟩

/-- ✱53·22. \(\vdash.sʻ \iotaʻʻ \alpha=\alpha\) -/
theorem pm53_22 {A : Set α} : sumCls (iota ʻʻ A) = A := by
  ext x
  constructor
  · rintro ⟨B, ⟨y, hy, hB⟩, hx⟩
    have : x = y := by rw [hB] at hx; exact hx
    exact this ▸ hy
  · intro hx; exact ⟨ι x, ⟨x, hx, rfl⟩, rfl⟩

/-- ✱53·221. \(\vdash.\iotaʻʻ (\iotaʻ x\cup \iotaʻ y)=\iotaʻ \iotaʻ x\cup \iotaʻ \iotaʻ y\) -/
theorem pm53_221 {x y : α} : iota ʻʻ (ι x ∪ ι y) = ι (ι x) ∪ ι (ι y) := by
  ext B
  constructor
  · rintro ⟨z, (hz | hz), hB⟩
    · left; rw [show z = x from hz] at hB; exact hB
    · right; rw [show z = y from hz] at hB; exact hB
  · rintro (hB | hB)
    · exact ⟨x, Or.inl rfl, hB⟩
    · exact ⟨y, Or.inr rfl, hB⟩

/-- ✱53·222. \(\vdash\colon\kappa=\iotaʻʻ\alpha.\supset.\alpha=\breve{\iota}ʻʻ\kappa\) -/
theorem pm53_222 {K : Set (Set α)} {A : Set α} : K = iota ʻʻ A → A = iota˘ ʻʻ K := by
  rintro rfl
  ext x
  constructor
  · intro hx; exact ⟨ι x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨B, ⟨y, hy, hB⟩, hBx⟩
    have : ι y = ι x := hB.symm.trans hBx
    rw [← unitCls_injective this]; exact hy

/-- ✱53·23. \(\vdash\colon\kappa\subset 1.\supset.sʻ\kappa=\breve{\iota}ʻʻ\kappa\) -/
theorem pm53_23 {K : Set (Set α)} : K ⊆ one → sumCls K = iota˘ ʻʻ K := by
  intro h
  ext x
  constructor
  · rintro ⟨B, hB, hx⟩
    obtain ⟨b, rfl⟩ := h hB
    have : x = b := hx
    subst this
    exact ⟨ι x, hB, rfl⟩
  · rintro ⟨B, hB, hBx⟩
    have : B = ι x := hBx
    subst this
    exact ⟨ι x, hB, rfl⟩

/-- ✱53·231. \(\vdash\colon\ldotp x\in\alpha.\supset_{x}.x=y:\equiv:\alpha=\Lambda.\lor.\alpha=\iotaʻy\) -/
theorem pm53_231 {A : Set α} {y : α} : (∀ x, x ∈ A → x = y) ↔ A = Λ ∨ A = ι y := pm51_401

/-- ✱53·24. \(\vdash\colon\ldotp sʻ\kappa=\Lambda.\equiv:\kappa=\Lambda\cap\text{Cls}.\lor.\kappa=\iotaʻ\Lambda\) -/
theorem pm53_24 {K : Set (Set α)} : sumCls K = Λ ↔ K = Λ ∩ Cls ∨ K = ι Λ := by
  have h1 : (Λ ∩ Cls : Set (Set α)) = Λ := by ext B; simp
  rw [h1, ← pm51_401]
  constructor
  · intro h B hB
    show B = Λ
    ext x
    simp only [mem_Null', iff_false]
    intro hx
    have : x ∈ sumCls K := ⟨B, hB, hx⟩
    rw [h] at this; exact this rfl
  · intro h
    ext x
    simp only [mem_sumCls', mem_Null', iff_false, not_exists, not_and]
    intro B hB hx
    have hB' : B = Λ := h hB
    rw [hB'] at hx; exact hx rfl

/-- ✱53·25. \(\vdash\colon\ldotp sʻ\kappa\cap sʻ\lambda=\Lambda.\subset\colon\kappa\cap\lambda=\Lambda\cap\text{Cls}.\lor.\kappa\cap\lambda=\iotaʻ\Lambda\)

**Status.** proved (reading): transcription error: the e-text prints `⊂` for the principal `⊃` (the
demonstration proves `Hp . ⊃ : κ ∩ λ = Λ ∩ Cls . ∨ . κ ∩ λ = ι'Λ`). -/
theorem pm53_25 {K L : Set (Set α)} :
    sumCls K ∩ sumCls L = Λ → K ∩ L = Λ ∩ Cls ∨ K ∩ L = ι Λ := by
  intro h
  apply pm53_24.1
  ext x
  simp only [mem_Null', iff_false]
  rintro ⟨B, ⟨hK, hL⟩, hx⟩
  have : x ∈ sumCls K ∩ sumCls L := ⟨⟨B, hK, hx⟩, ⟨B, hL, hx⟩⟩
  rw [h] at this; exact this rfl

/-- ✱53·3. \(\vdash:\text{E}!Rʻx.\equiv.\overrightarrow{R}ʻ x\in\text{1}\) -/
theorem pm53_3 {R : α → β → Prop} {x : β} : EDesc R x ↔ refs R x ∈ one :=
  (refs_mem_one_iff R x).symm

/-- ✱53·301. \(\vdash.Rʻʻ \iotaʻ x =\overrightarrow{R}ʻ x\) -/
theorem pm53_301 {R : α → β → Prop} {x : β} : R ʻʻ ι x = refs R x := by
  ext z; simp

/-- ✱53·302. \(\vdash.Rʻʻ (\iotaʻ x \cup \iotaʻ y) =\overrightarrow{R}ʻ x \cup \overrightarrow{R}ʻ y \quad[\text{*37·22.*53·301}]\) -/
theorem pm53_302 {R : α → β → Prop} {x y : β} : R ʻʻ (ι x ∪ ι y) = refs R x ∪ refs R y := by
  ext z; simp [or_and_right, exists_or]

/-- ✱53·31. \(\vdash:\text{E}!Rʻ x.\supset.Rʻʻ \iotaʻ x = \iotaʻ Rʻ x = \overrightarrow{R}ʻ x\) -/
theorem pm53_31 {R : α → β → Prop} {x : β} :
    EDesc R x → Desc R x (fun b => R ʻʻ ι x = ι b) ∧ Desc R x (fun b => ι b = refs R x) := by
  rintro ⟨b, hb⟩
  have e : refs R x = ι b := by ext z; exact hb z
  exact ⟨⟨b, hb, pm53_301.trans e⟩, ⟨b, hb, e.symm⟩⟩

/-- ✱53·32. \(\vdash:\text{E}!Rʻ x.\text{E}!Rʻ y.\supset.Rʻʻ (\iotaʻ x \cup \iotaʻ y) = \iotaʻ Rʻ x \cup \iotaʻ Rʻ y\) -/
theorem pm53_32 {R : α → β → Prop} {x y : β} :
    EDesc R x ∧ EDesc R y → Desc R x (fun b => Desc R y (fun c => R ʻʻ (ι x ∪ ι y) = ι b ∪ ι c)) := by
  rintro ⟨⟨b, hb⟩, ⟨c, hc⟩⟩
  have e1 : refs R x = ι b := by ext z; exact hb z
  have e2 : refs R y = ι c := by ext z; exact hc z
  exact ⟨b, hb, c, hc, by rw [pm53_302, e1, e2]⟩

/-- ✱53·33. \(\vdash. sʻʻ \iotaʻ \kappa = \iotaʻ sʻ \kappa \quad\left[\text{*53*31}\, \frac{s}{R}\right]\)

**Status.** proved: `s` is the relation `ûκ̂(u = s'κ)`, i.e. `graph sumCls` (Summary of Section E);
the e-text prints `✱53*31` for ✱53·31 in the reference. -/
theorem pm53_33 {K : Set (Set α)} : graph sumCls ʻʻ ι K = ι (sumCls K) := by
  ext B; simp

/-- ✱53·34. \(\vdash. sʻʻ (\iotaʻ \kappa \cup \iotaʻ \lambda) = \iotaʻ sʻ \kappa \cup \iotaʻ sʻ \lambda \quad\left[\text{*53*32}\, \frac{s}{R}\right]\) -/
theorem pm53_34 {K L : Set (Set α)} :
    graph sumCls ʻʻ (ι K ∪ ι L) = ι (sumCls K) ∪ ι (sumCls L) := by
  ext B; simp [or_and_right, exists_or]

/-- ✱53·35. \(\vdash. sʻ sʻʻ (\iotaʻ \kappa \cup \iotaʻ \lambda) = sʻ \kappa \cup sʻ \lambda = sʻ(\kappa \cup \lambda)\) -/
theorem pm53_35 {K L : Set (Set α)} :
    sumCls (graph sumCls ʻʻ (ι K ∪ ι L)) = sumCls K ∪ sumCls L ∧
      sumCls K ∪ sumCls L = sumCls (K ∪ L) := by
  refine ⟨by rw [pm53_34, pm53_11], ?_⟩
  ext x; simp [or_and_right, exists_or]

/-- ✱53·4. \(\vdash:x=Rʻ y.\equiv.\overrightarrow{R}ʻ y\in\text{1}.x\in\overrightarrow{R}ʻ y.\equiv.\iotaʻ x=\overrightarrow{R}ʻ y.\equiv.x=\breve{\iota}ʻ\overrightarrow{R}ʻ y\) -/
theorem pm53_4 {R : α → β → Prop} {x : α} {y : β} :
    ((Desc R y (fun b => x = b) ↔ refs R y ∈ one ∧ x ∈ refs R y) ∧
        (refs R y ∈ one ∧ x ∈ refs R y ↔ ι x = refs R y)) ∧
      (ι x = refs R y ↔ Desc iota˘ (refs R y) (fun b => x = b)) := by
  have e13 : Desc R y (fun b => x = b) ↔ ι x = refs R y := by
    constructor
    · rintro ⟨b, hb, rfl⟩; ext z; exact (hb z).symm
    · intro h; exact ⟨x, fun z => (Set.ext_iff.1 h z).symm, rfl⟩
  have e23 : refs R y ∈ one ∧ x ∈ refs R y ↔ ι x = refs R y := by
    constructor
    · rintro ⟨⟨b, hb⟩, hx⟩
      rw [hb] at hx
      have : x = b := hx
      rw [this, hb]
    · intro h
      exact ⟨⟨x, h.symm⟩, by rw [← h]; exact rfl⟩
  exact ⟨⟨e13.trans e23.symm, e23⟩, eq_comm.trans pm51_51.1⟩

/-- ✱53·5. \(\vdash:\exists!\alpha.\equiv.\alpha\in\text{Cls}-\iotaʻ\Lambda\) -/
theorem pm53_5 {A : Set α} : A.Nonempty ↔ A ∈ Cls \ ι Λ := by
  simp only [Set.mem_sdiff, mem_Cls', mem_unitCls, true_and, Null_eq_empty,
    Set.nonempty_iff_ne_empty]

/-- ✱53·51. \(\vdash:\dot{\exists}!R.\equiv.R\in\text{Rel}-\iotaʻ\dot{\Lambda} \quad[\text{Proof as in *53·5}]\) -/
theorem pm53_51 {R : α → β → Prop} : rEx R ↔ R ∈ Rel \ ι rNull := by
  simp only [Set.mem_sdiff, mem_Rel', mem_unitCls, true_and, rEx_iff]
  exact rEx_iff_ne_rNull

/-- ✱53·52. \(\vdash:\alpha\in\kappa.\exists!\alpha.\equiv.\alpha\in\kappa-\iotaʻ\Lambda\) -/
theorem pm53_52 {A : Set α} {K : Set (Set α)} : A ∈ K ∧ A.Nonempty ↔ A ∈ K \ ι Λ := by
  simp only [Set.mem_sdiff, mem_unitCls, Null_eq_empty, Set.nonempty_iff_ne_empty]

/-- ✱53·53. \(\vdash:R\in\lambda.\dot{\exists}!R.\equiv.R\in\lambda-\iotaʻ\dot{\Lambda} \quad[\text{Proof as in *53·52}]\) -/
theorem pm53_53 {R : α → β → Prop} {L : Set (α → β → Prop)} :
    R ∈ L ∧ rEx R ↔ R ∈ L \ ι rNull := by
  simp only [Set.mem_sdiff, mem_unitCls, rEx_iff]
  exact and_congr Iff.rfl rEx_iff_ne_rNull

/-- ✱53·6. \(\vdash:R=\dot{\Lambda}.\exists!\alpha.\supset.\overrightarrow{R}ʻʻ \alpha=\iotaʻ\Lambda.\overrightarrow{R}ʻʻ \alpha=\iotaʻ\Lambda\)

**Status.** proved (reading): transcription error: the e-text prints `R⃗''α = ι'Λ` twice; the second
is `R⃖''α = ι'Λ` (the demonstration: "Similarly `⊢ : Hp . ⊃ . R⃖''α = ι'Λ`"). The formula
(`R⃗''α`, `R⃖''α` with the same `α`) forces `R` to be homogeneous. -/
theorem pm53_6 {R : α → α → Prop} {A : Set α} :
    R = rNull ∧ A.Nonempty → Rfwd R ʻʻ A = ι Λ ∧ Rbwd R ʻʻ A = ι Λ := by
  rintro ⟨rfl, ⟨a, ha⟩⟩
  have hr : ∀ y, refs (rNull : α → α → Prop) y = Λ := fun y =>
    refs_eq_Null_iff.2 fun ⟨_, h⟩ => rNull_apply _ _ h
  have hl : ∀ y, rels (rNull : α → α → Prop) y = Λ := fun y =>
    rels_eq_Null_iff.2 fun ⟨_, h⟩ => rNull_apply _ _ h
  constructor
  · ext B
    constructor
    · rintro ⟨y, -, hB⟩; exact hB.trans (hr y)
    · intro (hB : B = Λ); exact ⟨a, ha, hB.trans (hr a).symm⟩
  · ext B
    constructor
    · rintro ⟨y, -, hB⟩; exact hB.trans (hl y)
    · intro (hB : B = Λ); exact ⟨a, ha, hB.trans (hl a).symm⟩

/-- ✱53·601. \(\vdash:\exists!\alpha.\alpha\cap\text{ᗡ}ʻ R=\Lambda.\supset.\overrightarrow{R}ʻʻ \alpha=\iotaʻ\Lambda\) -/
theorem pm53_601 {R : α → β → Prop} {A : Set β} :
    A.Nonempty ∧ A ∩ codom R = Λ → Rfwd R ʻʻ A = ι Λ := by
  rintro ⟨⟨a, ha⟩, h⟩
  have hn : ∀ y, y ∈ A → y ∉ codom R := fun y hy hc => by
    have : y ∈ A ∩ codom R := ⟨hy, hc⟩
    rw [h] at this; exact this rfl
  ext B
  constructor
  · rintro ⟨y, hy, hB⟩; exact hB.trans (refs_eq_Null_iff.2 (hn y hy))
  · intro (hB : B = Λ); exact ⟨a, ha, hB.trans (refs_eq_Null_iff.2 (hn a ha)).symm⟩

/-- ✱53·602. \(\vdash:\exists!\alpha.\alpha\cap\text{D}ʻ R=\Lambda.\supset.\overleftarrow{R}ʻʻ \alpha=\iotaʻ \Lambda \quad[\text{Proof as in *53·601}]\) -/
theorem pm53_602 {R : α → β → Prop} {A : Set α} :
    A.Nonempty ∧ A ∩ dom R = Λ → Rbwd R ʻʻ A = ι Λ := by
  rintro ⟨⟨a, ha⟩, h⟩
  have hn : ∀ y, y ∈ A → y ∉ dom R := fun y hy hc => by
    have : y ∈ A ∩ dom R := ⟨hy, hc⟩
    rw [h] at this; exact this rfl
  ext B
  constructor
  · rintro ⟨y, hy, hB⟩; exact hB.trans (rels_eq_Null_iff.2 (hn y hy))
  · intro (hB : B = Λ); exact ⟨a, ha, hB.trans (rels_eq_Null_iff.2 (hn a ha)).symm⟩

/-- ✱53·603. \(\vdash:\exists!-\text{ᗡ}ʻ R.\supset.\overrightarrow{R}ʻʻ (-\text{ᗡ}ʻ R)=\iotaʻ \Lambda \quad[\text{*24·21.*53·601}]\) -/
theorem pm53_603 {R : α → β → Prop} :
    (codom R)ᶜ.Nonempty → Rfwd R ʻʻ (codom R)ᶜ = ι Λ := fun h =>
  pm53_601 ⟨h, by rw [Null_eq_empty]; exact Set.compl_inter_self _⟩

/-- ✱53·604. \(\vdash:\exists!-\text{D}ʻ R.\supset.\overleftarrow{R}ʻʻ (-\text{D}ʻ R)=\iotaʻ\Lambda \quad[\text{*24·21.*53·602}]\) -/
theorem pm53_604 {R : α → β → Prop} :
    (dom R)ᶜ.Nonempty → Rbwd R ʻʻ (dom R)ᶜ = ι Λ := fun h =>
  pm53_602 ⟨h, by rw [Null_eq_empty]; exact Set.compl_inter_self _⟩

/-- ✱53·61. \(\vdash:\text{ᗡ}ʻ R\subset \alpha.\text{ᗡ}ʻR\neq \alpha.\supset.\overrightarrow{R}ʻʻ \alpha=\overrightarrow{R}ʻʻ\text{ᗡ}ʻ R\cup \iotaʻ\Lambda\) -/
theorem pm53_61 {R : α → β → Prop} {A : Set β} :
    codom R ⊆ A ∧ codom R ≠ A → Rfwd R ʻʻ A = (Rfwd R ʻʻ codom R) ∪ ι Λ := by
  rintro ⟨hs, hne⟩
  obtain ⟨y₀, hy₀A, hy₀⟩ : ∃ y, y ∈ A ∧ y ∉ codom R := by
    by_contra hc
    push Not at hc
    exact hne (Set.Subset.antisymm hs hc)
  ext B
  constructor
  · rintro ⟨y, hy, hB⟩
    by_cases hc : y ∈ codom R
    · exact Or.inl ⟨y, hc, hB⟩
    · exact Or.inr (hB.trans (refs_eq_Null_iff.2 hc))
  · rintro (⟨y, hy, hB⟩ | (hB : B = Λ))
    · exact ⟨y, hs hy, hB⟩
    · exact ⟨y₀, hy₀A, hB.trans (refs_eq_Null_iff.2 hy₀).symm⟩

/-- ✱53·611. \(\vdash:\text{D}ʻ R\subset \alpha.\text{D}ʻ R\neq \alpha.\supset.\overleftarrow{R}ʻʻ \alpha=\overleftarrow{R}ʻʻ \text{D}ʻ R\cup \iotaʻ\Lambda \quad[\text{Proof as in *53·61}]\) -/
theorem pm53_611 {R : α → β → Prop} {A : Set α} :
    dom R ⊆ A ∧ dom R ≠ A → Rbwd R ʻʻ A = (Rbwd R ʻʻ dom R) ∪ ι Λ := by
  rintro ⟨hs, hne⟩
  obtain ⟨y₀, hy₀A, hy₀⟩ : ∃ y, y ∈ A ∧ y ∉ dom R := by
    by_contra hc
    push Not at hc
    exact hne (Set.Subset.antisymm hs hc)
  ext B
  constructor
  · rintro ⟨y, hy, hB⟩
    by_cases hc : y ∈ dom R
    · exact Or.inl ⟨y, hc, hB⟩
    · exact Or.inr (hB.trans (rels_eq_Null_iff.2 hc))
  · rintro (⟨y, hy, hB⟩ | (hB : B = Λ))
    · exact ⟨y, hs hy, hB⟩
    · exact ⟨y₀, hy₀A, hB.trans (rels_eq_Null_iff.2 hy₀).symm⟩

/-- ✱53·612. \(\vdash:\text{ᗡ}ʻ R\neq\text{V}.\supset.\overrightarrow{R}ʻʻ\text{V}=\overrightarrow{R}ʻʻ\text{ᗡ}ʻ R\cup \iotaʻ\Lambda \quad[\text{*53·61.*24·11}]\) -/
theorem pm53_612 {R : α → β → Prop} :
    codom R ≠ V → Rfwd R ʻʻ V = (Rfwd R ʻʻ codom R) ∪ ι Λ := fun h =>
  pm53_61 ⟨fun _ _ => rfl, h⟩

/-- ✱53·613. \(\vdash:\text{D}ʻ R\neq\text{V}.\supset.\overleftarrow{R}ʻʻ \text{V}=\overleftarrow{R}ʻʻ \text{ᗡ}ʻ R\cup \iotaʻ\Lambda \quad[\text{*53·611.*24·11}]\)

**Status.** proved (reading): transcription error: the e-text prints `R⃖''ᗡ'R` for `R⃖''D'R` on the
right (the proof cites ✱53·611, whose right-hand side is `R⃖''D'R ∪ ι'Λ`; with `ᗡ'R` the
formula is not even significant for a heterogeneous `R`). -/
theorem pm53_613 {R : α → β → Prop} :
    dom R ≠ V → Rbwd R ʻʻ V = (Rbwd R ʻʻ dom R) ∪ ι Λ := fun h =>
  pm53_611 ⟨fun _ _ => rfl, h⟩

/-- ✱53·614. \(\vdash.\overrightarrow{R}ʻʻ\text{ᗡ}ʻ R=\overrightarrow{R}ʻʻ\text{V}-\iotaʻ\Lambda\) -/
theorem pm53_614 {R : α → β → Prop} : Rfwd R ʻʻ codom R = (Rfwd R ʻʻ V) \ ι Λ := by
  ext B
  constructor
  · rintro ⟨y, hy, hB⟩
    exact ⟨⟨y, rfl, hB⟩, fun (e : B = Λ) => (refs_eq_Null_iff.1 (hB.symm.trans e)) hy⟩
  · rintro ⟨⟨y, -, hB⟩, hn⟩
    refine ⟨y, ?_, hB⟩
    by_contra hc
    exact hn (hB.trans (refs_eq_Null_iff.2 hc))

/-- ✱53·615. \(\vdash.\overleftarrow{R}ʻʻ\text{D}ʻ R=\overleftarrow{R}ʻʻ\text{V}-\iotaʻ\Lambda \quad[\text{Proof as in *53·614}]\) -/
theorem pm53_615 {R : α → β → Prop} : Rbwd R ʻʻ dom R = (Rbwd R ʻʻ V) \ ι Λ := by
  ext B
  constructor
  · rintro ⟨y, hy, hB⟩
    exact ⟨⟨y, rfl, hB⟩, fun (e : B = Λ) => (rels_eq_Null_iff.1 (hB.symm.trans e)) hy⟩
  · rintro ⟨⟨y, -, hB⟩, hn⟩
    refine ⟨y, ?_, hB⟩
    by_contra hc
    exact hn (hB.trans (rels_eq_Null_iff.2 hc))

/-- ✱53·62. \(\vdash:\overrightarrow{R}ʻʻ\text{ᗡ}ʻ R\subset \gamma.\equiv.\overrightarrow{R}ʻʻ\text{V}\subset \gamma\cup \iotaʻ\Lambda\) -/
theorem pm53_62 {R : α → β → Prop} {G : Set (Set α)} :
    Rfwd R ʻʻ codom R ⊆ G ↔ Rfwd R ʻʻ V ⊆ G ∪ ι Λ := by
  constructor
  · rintro h B ⟨y, -, hB⟩
    by_cases hc : y ∈ codom R
    · exact Or.inl (h ⟨y, hc, hB⟩)
    · exact Or.inr (hB.trans (refs_eq_Null_iff.2 hc))
  · rintro h B ⟨y, hy, hB⟩
    rcases h ⟨y, rfl, hB⟩ with hG | (e : B = Λ)
    · exact hG
    · exact absurd hy (refs_eq_Null_iff.1 (hB.symm.trans e))

/-- ✱53·621. \(\vdash:\overleftarrow{R}ʻʻ\text{D}ʻ R\subset \gamma.\equiv.\overleftarrow{R}ʻʻ\text{V}\subset \gamma\cup \iotaʻ\Lambda \quad[\text{Proof as in *53·62}]\) -/
theorem pm53_621 {R : α → β → Prop} {G : Set (Set β)} :
    Rbwd R ʻʻ dom R ⊆ G ↔ Rbwd R ʻʻ V ⊆ G ∪ ι Λ := by
  constructor
  · rintro h B ⟨y, -, hB⟩
    by_cases hc : y ∈ dom R
    · exact Or.inl (h ⟨y, hc, hB⟩)
    · exact Or.inr (hB.trans (rels_eq_Null_iff.2 hc))
  · rintro h B ⟨y, hy, hB⟩
    rcases h ⟨y, rfl, hB⟩ with hG | (e : B = Λ)
    · exact hG
    · exact absurd hy (rels_eq_Null_iff.1 (hB.symm.trans e))

/-- ✱53·63. \(\vdash:\text{ᗡ}ʻ R\neq\text{V}.\supset.\text{D}ʻ\overrightarrow{R}=\overrightarrow{R}ʻʻ\text{ᗡ}ʻ R\cup \iotaʻ\Lambda \quad[\text{*37·78.*53·612}]\) -/
theorem pm53_63 {R : α → β → Prop} :
    codom R ≠ V → dom (Rfwd R) = (Rfwd R ʻʻ codom R) ∪ ι Λ := by
  intro h
  rw [← pm53_612 h]
  ext B; simp

/-- ✱53·631. \(\vdash:\text{D}ʻ R\neq\text{V}.\supset.\text{D}ʻ\overleftarrow{R}=\overleftarrow{R}ʻʻ\text{D}ʻ R\cup \iotaʻ\Lambda \quad[\text{*37·781.*53·613}]\) -/
theorem pm53_631 {R : α → β → Prop} :
    dom R ≠ V → dom (Rbwd R) = (Rbwd R ʻʻ dom R) ∪ ι Λ := by
  intro h
  rw [← pm53_613 h]
  ext B; simp

/-- ✱53·64. \(\vdash:\text{ᗡ}ʻR=\text{V}.\supset.\text{D}ʻ\overrightarrow{R}=\overrightarrow{R}ʻʻ \text{ᗡ}ʻR \quad[\text{*37·78}]\) -/
theorem pm53_64 {R : α → β → Prop} : codom R = V → dom (Rfwd R) = Rfwd R ʻʻ codom R := by
  intro h
  rw [h]
  ext B; simp

/-- ✱53·641. \(\vdash:\text{D}ʻ R=\text{V}.\supset.\text{D}ʻ\overleftarrow{R}=\overleftarrow{R}ʻʻ\text{D}ʻ R \quad[\text{*37·781}]\) -/
theorem pm53_641 {R : α → β → Prop} : dom R = V → dom (Rbwd R) = Rbwd R ʻʻ dom R := by
  intro h
  rw [h]
  ext B; simp

/-!
## [✱54] Cardinal couples

*(Vol. 1, p. 376)*

> Couples are of two kinds, namely (1) \(\iotaʻx\cup\iotaʻy\), in which there is no order as between \(x\) and \(y\), and (2) \(\iotaʻx\uparrow\iotaʻy\), in which there is an order. We may distinguish these two kinds of couples as cardinal and ordinal respectively, since (as will be shown hereafter) the class of all couples of the form \(\iotaʻx\cup\iotaʻy\) (where \(x\neq y\)) is the cardinal number 2, while the class of all couples of the form \(\iotaʻx\uparrow\iotaʻy\) (where \(x\neq y\)) is the ordinal number 2, to which, for the sake of distinction, we assign the symbol "\(2_{r}\)," where the suffix "\(r\)" stands for "relational," because the ordinal 2 is a class of relations. In the present and the following numbers, we shall define 2 and \(2_{r}\) as the classes of cardinal and ordinal couples respectively, leaving it to a later stage to show that 2 and \(2_{r}\), so defined, are respectively a cardinal and an ordinal number. An ordinal couple will also be called an *ordered* couple or a *couple with sense*. Thus a couple with sense is a couple of which one comes first and the other second.
>
> …

**Lean reading.** The cardinal numbers `0` and `2` are `zero` and `two : Set (Set α)` (`1` is `one`, ✱52). The Df
✱54·01 `0 = ι'Λ` has a descriptive function of a constant as definiens, so it is stated with
`Desc iota Λ` (Basic §5); ✱54·1 is the same identity with the value `ι Λ`. A cardinal couple
`ι'x ∪ ι'y` is `ι x ∪ ι y`; `x, y ∈ α` is `x ∈ A ∧ y ∈ A` and `x, y, z ∈ α` is
`(x ∈ A ∧ y ∈ A) ∧ z ∈ A` (✱20·04·05); `0 ∪ 1 ∪ 2` is `zero ∪ one ∪ two`, bracketed to the left
(✱22·71); `φ(z, w)` is `φ : α → α → Prop`. PM's `x'`, `y'` (✱54·6) are `x'`, `y'`. The e-text drops
the braces of the class abstract in ✱54·55.

**Status.** proved (all propositions; ✱54·01·02 definition).
-/

/-- ✱54·01 (Df). \(0=\iotaʻ\Lambda \quad\text{Df}\) -/
theorem pm54_01 : Desc iota Λ (fun K => (zero : Set (Set α)) = K) := (desc_graph _ _ _).2 rfl

/-- ✱54·02 (Df). \(2=\hat{\alpha}\{(\exists x,y).x\neq y.\alpha=\iotaʻx\cup \iotaʻy\} \quad\text{Df}\) -/
theorem pm54_02 : (two : Set (Set α)) = {A | ∃ x y, x ≠ y ∧ A = ι x ∪ ι y} := rfl

/-- ✱54·1. \(\vdash.0=\iotaʻ\Lambda \quad[\text{(*54·01)}]\) -/
theorem pm54_1 : (zero : Set (Set α)) = ι Λ := rfl

/-- ✱54·101. \(\vdash:\alpha\in 2.\equiv.(\exists x,y).x \neq y.\alpha=\iotaʻx\cup \iotaʻy \quad[\text{(*54·02)}]\) -/
theorem pm54_101 {A : Set α} : A ∈ two ↔ ∃ x y, x ≠ y ∧ A = ι x ∪ ι y := Iff.rfl

/-- ✱54·102. \(\vdash:\alpha\in 0.\equiv.\alpha=\Lambda \quad[\text{*54·1}]\) -/
theorem pm54_102 {A : Set α} : A ∈ zero ↔ A = Λ := Iff.rfl

/-- ✱54·21. \(\vdash:\iotaʻx\cup \iotaʻy=\iotaʻx\cup \iotaʻz.\equiv.y=z \quad[\text{*51·41}]\) -/
theorem pm54_21 {x y z : α} : ι x ∪ ι y = ι x ∪ ι z ↔ y = z := pm51_41

/-- ✱54·22. \(\vdash\colon\ldotp \iotaʻx\cup \iotaʻy=\iotaʻz\cup \iotaʻw.\equiv:x=z.y=w.\lor.x=w.y=z \quad[\text{*51·43}]\) -/
theorem pm54_22 {x y z w : α} :
    ι x ∪ ι y = ι z ∪ ι w ↔ (x = z ∧ y = w) ∨ (x = w ∧ y = z) := pm51_43

/-- ✱54·25. \(\vdash:\iotaʻx\cup \iotaʻy\in 1.\equiv.x=y\) -/
theorem pm54_25 {x y : α} : ι x ∪ ι y ∈ one ↔ x = y := by
  constructor
  · rintro ⟨a, h⟩
    have hx : x ∈ ι a := h ▸ Or.inl rfl
    have hy : y ∈ ι a := h ▸ Or.inr rfl
    exact (hx : x = a).trans (hy : y = a).symm
  · rintro rfl; exact ⟨x, Set.union_self _⟩

/-- ✱54·26. \(\vdash:\iotaʻx\cup \iotaʻy\in 2.\equiv.x\neq y\) -/
theorem pm54_26 {x y : α} : ι x ∪ ι y ∈ two ↔ x ≠ y := by
  constructor
  · rintro ⟨a, b, hab, h⟩ e
    subst e
    rw [Set.union_self] at h
    have ha : a ∈ ι x := h ▸ Or.inl rfl
    have hb : b ∈ ι x := h ▸ Or.inr rfl
    exact hab ((ha : a = x).trans (hb : b = x).symm)
  · intro h; exact ⟨x, y, h, rfl⟩

/-- ✱54·27. \(\vdash.\iotaʻx\cup \iotaʻy\in 1\cup 2 \quad[\text{*54·25·26}]\) -/
theorem pm54_27 {x y : α} : ι x ∪ ι y ∈ one ∪ two := by
  by_cases h : x = y
  · exact Or.inl (pm54_25.2 h)
  · exact Or.inr (pm54_26.2 h)

/-- ✱54·271. \(\vdash.1\cup 2=\hat{\alpha}\{(\exists x,y).\alpha=\iotaʻx\cup \iotaʻy\}\) -/
theorem pm54_271 : (one ∪ two : Set (Set α)) = {A | ∃ x y, A = ι x ∪ ι y} := by
  ext A
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, b, -, rfl⟩)
    · exact ⟨a, a, (Set.union_self _).symm⟩
    · exact ⟨a, b, rfl⟩
  · rintro ⟨x, y, rfl⟩; exact pm54_27

/-- ✱54·3. \(\vdash.2=\hat{\alpha}\{(\exists x).x\in\alpha.\alpha-\iotaʻ x\in 1\}\) -/
theorem pm54_3 : (two : Set (Set α)) = {A | ∃ x, x ∈ A ∧ A \ ι x ∈ one} := by
  ext A
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    refine ⟨x, Or.inl rfl, y, ?_⟩
    ext z
    constructor
    · rintro ⟨(h | h), hn⟩
      · exact absurd h hn
      · exact h
    · intro (h : z = y)
      subst h
      exact ⟨Or.inr rfl, fun (e : z = x) => hxy e.symm⟩
  · rintro ⟨x, hx, y, hy⟩
    have hy' : ∀ z, z ∈ A ∧ z ≠ x ↔ z = y := eq_unitCls_iff.1 hy
    have hyA := ((hy' y).2 rfl)
    refine ⟨x, y, fun e => hyA.2 e.symm, ?_⟩
    ext z
    constructor
    · intro hz
      by_cases e : z = x
      · exact Or.inl e
      · exact Or.inr ((hy' z).1 ⟨hz, e⟩)
    · rintro ((h : z = x) | (h : z = y))
      · exact h ▸ hx
      · exact h ▸ hyA.1

/-- ✱54·4. \(\vdash\colon\ldotp \beta\subset \iotaʻ x\cup \iotaʻ y.\equiv:\beta=\Lambda.\lor.\beta=\iotaʻ x.\lor.\beta=\iotaʻ y.\lor.\beta=\iotaʻ x\cup \iotaʻ y\) -/
theorem pm54_4 {B : Set α} {x y : α} :
    B ⊆ ι x ∪ ι y ↔ ((B = Λ ∨ B = ι x) ∨ B = ι y) ∨ B = ι x ∪ ι y := by
  simp only [Null_eq_empty, unitCls_eq_singleton, Set.singleton_union]
  rw [Set.subset_pair_iff_eq]
  simp only [or_assoc]

/-- ✱54·41. \(\vdash\colon\colon \alpha\in 2.\supset\colon\ldotp \beta\subset \alpha.\supset:\beta=\Lambda.\lor.\beta\in 1.\lor.\beta\in 2\) -/
theorem pm54_41 {A B : Set α} : A ∈ two → (B ⊆ A → (B = Λ ∨ B ∈ one) ∨ B ∈ two) := by
  rintro ⟨x, y, hxy, rfl⟩ h
  rcases pm54_4.1 h with ((h | h) | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr ⟨x, h⟩)
  · exact Or.inl (Or.inr ⟨y, h⟩)
  · exact Or.inr ⟨x, y, hxy, h⟩

/-- ✱54·411. \(\vdash\colon\ldotp \alpha\in 2.\supset:\beta\subset \alpha.\supset.\beta\in 0\cup 1\cup 2 \quad[\text{*54·41·02}]\) -/
theorem pm54_411 {A B : Set α} : A ∈ two → (B ⊆ A → B ∈ zero ∪ one ∪ two) := by
  rintro ⟨x, y, hxy, rfl⟩ h
  rcases pm54_4.1 h with ((h | h) | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr ⟨x, h⟩)
  · exact Or.inl (Or.inr ⟨y, h⟩)
  · exact Or.inr ⟨x, y, hxy, h⟩

/-- ✱54·42. \(\vdash\colon\colon\alpha\in 2 .\supset\colon\ldotp\beta\subset\alpha.\exists!\beta.\beta\neq\alpha .\equiv. \beta\in\iotaʻʻ\alpha\) -/
theorem pm54_42 {A B : Set α} :
    A ∈ two → ((B ⊆ A ∧ B.Nonempty) ∧ B ≠ A ↔ B ∈ iota ʻʻ A) := by
  rintro ⟨x, y, hxy, rfl⟩
  constructor
  · rintro ⟨⟨h, hne⟩, hB⟩
    rcases pm54_4.1 h with ((h | h) | h) | h
    · rw [h, Null_eq_empty] at hne; exact absurd hne Set.not_nonempty_empty
    · exact ⟨x, Or.inl rfl, h⟩
    · exact ⟨y, Or.inr rfl, h⟩
    · exact absurd h hB
  · rintro ⟨z, hz, (hB : B = ι z)⟩
    subst hB
    refine ⟨⟨pm51_2.1 hz, ⟨z, rfl⟩⟩, fun h => hxy ?_⟩
    have hx : x ∈ ι z := h ▸ Or.inl rfl
    have hy : y ∈ ι z := h ▸ Or.inr rfl
    exact (hx : x = z).trans (hy : y = z).symm

/-- ✱54·43. \(\vdash\colon\ldotp \alpha,\beta\in 1 .\supset: \alpha\cap\beta =\Lambda .\equiv. \alpha\cup\beta \in 2\) -/
theorem pm54_43 {A B : Set α} : A ∈ one ∧ B ∈ one → (A ∩ B = Λ ↔ A ∪ B ∈ two) := by
  rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  exact pm51_231.trans pm54_26.symm

/-- ✱54·44. \(\vdash\colon\ldotp z, w \in \iotaʻx \cup \iotaʻy . \supset_{z,w}.\phi(z,w) :\equiv. \phi(x,x).\phi(x,y).\phi(y,x).\phi(y,y)\) -/
theorem pm54_44 {x y : α} {φ : α → α → Prop} :
    (∀ z w, z ∈ ι x ∪ ι y ∧ w ∈ ι x ∪ ι y → φ z w) ↔ ((φ x x ∧ φ x y) ∧ φ y x) ∧ φ y y := by
  constructor
  · intro h
    exact ⟨⟨⟨h _ _ ⟨Or.inl rfl, Or.inl rfl⟩, h _ _ ⟨Or.inl rfl, Or.inr rfl⟩⟩,
      h _ _ ⟨Or.inr rfl, Or.inl rfl⟩⟩, h _ _ ⟨Or.inr rfl, Or.inr rfl⟩⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ z w ⟨(rfl | rfl), (rfl | rfl)⟩ <;> assumption

/-- ✱54·441. \(\vdash\colon\colon z,w \in \iotaʻx \cup \iotaʻy. z\neq w. \supset_{z,w}. \phi(z,w) :\equiv\colon\ldotp x = y: \lor :\phi(x,y).\phi(y,x)\) -/
theorem pm54_441 {x y : α} {φ : α → α → Prop} :
    (∀ z w, (z ∈ ι x ∪ ι y ∧ w ∈ ι x ∪ ι y) ∧ z ≠ w → φ z w) ↔ x = y ∨ (φ x y ∧ φ y x) := by
  constructor
  · intro h
    by_cases e : x = y
    · exact Or.inl e
    · exact Or.inr ⟨h _ _ ⟨⟨Or.inl rfl, Or.inr rfl⟩, e⟩, h _ _ ⟨⟨Or.inr rfl, Or.inl rfl⟩, Ne.symm e⟩⟩
  · rintro (rfl | ⟨h1, h2⟩) z w ⟨⟨(rfl | rfl), (rfl | rfl)⟩, hne⟩ <;>
      first | exact absurd rfl hne | assumption

/-- ✱54·442. \(\vdash\colon\colon x\neq y.\supset\colon\ldotp z,w\in \iotaʻ x\cup \iotaʻ y.z\neq w.\supset_{z,w}.\phi(z,w):\equiv.\phi(x,y).\phi(y,x) \quad[\text{*54·441}]\) -/
theorem pm54_442 {x y : α} {φ : α → α → Prop} :
    x ≠ y → ((∀ z w, (z ∈ ι x ∪ ι y ∧ w ∈ ι x ∪ ι y) ∧ z ≠ w → φ z w) ↔ φ x y ∧ φ y x) := by
  intro h
  rw [pm54_441]
  exact ⟨fun h' => h'.resolve_left h, Or.inr⟩

/-- ✱54·443. \[\begin{align}\vdash\colon\colon x\neq y:&\phi(x,y).\equiv.\phi(y,x):\supset\colon\ldotp\\ &z,w\in \iotaʻ x\cup \iotaʻ y.z\neq w.\supset_{z,w}.\phi(z,w):\equiv.\phi(x,y) \quad[\text{*54·442}]\end{align}\] -/
theorem pm54_443 {x y : α} {φ : α → α → Prop} :
    x ≠ y ∧ (φ x y ↔ φ y x) →
      ((∀ z w, (z ∈ ι x ∪ ι y ∧ w ∈ ι x ∪ ι y) ∧ z ≠ w → φ z w) ↔ φ x y) := by
  rintro ⟨h, he⟩
  rw [pm54_442 h]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', he.1 h'⟩⟩

/-- ✱54·45. \[\begin{align}\vdash\colon\ldotp(\exists z,w).&z,w\in \iotaʻ x\cup \iotaʻ y.\phi(z,w).\\ &\equiv:\phi(x,x).\lor.\phi(x,y).\lor.\phi(y,x).\lor.\phi(y,y) \quad[\text{*51·235}]\end{align}\] -/
theorem pm54_45 {x y : α} {φ : α → α → Prop} :
    (∃ z w, (z ∈ ι x ∪ ι y ∧ w ∈ ι x ∪ ι y) ∧ φ z w) ↔
      ((φ x x ∨ φ x y) ∨ φ y x) ∨ φ y y := by
  constructor
  · rintro ⟨z, w, ⟨(rfl | rfl), (rfl | rfl)⟩, h⟩
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · rintro (((h | h) | h) | h)
    · exact ⟨x, x, ⟨Or.inl rfl, Or.inl rfl⟩, h⟩
    · exact ⟨x, y, ⟨Or.inl rfl, Or.inr rfl⟩, h⟩
    · exact ⟨y, x, ⟨Or.inr rfl, Or.inl rfl⟩, h⟩
    · exact ⟨y, y, ⟨Or.inr rfl, Or.inr rfl⟩, h⟩

/-- ✱54·451. \[\begin{align}\vdash\colon\colon{\sim}\phi(x,x).{\sim} \phi(y,y).\supset\colon\ldotp(\exists z,w).&z,w\in \iotaʻ x\cup \iotaʻ y.\phi(z,w).\\ &\equiv:\phi(x,y).\lor.\phi(y,x) \quad[\text{*54·45}]\end{align}\] -/
theorem pm54_451 {x y : α} {φ : α → α → Prop} :
    ¬φ x x ∧ ¬φ y y →
      ((∃ z w, (z ∈ ι x ∪ ι y ∧ w ∈ ι x ∪ ι y) ∧ φ z w) ↔ φ x y ∨ φ y x) := by
  rintro ⟨h1, h2⟩
  rw [pm54_45]
  tauto

/-- ✱54·452. \[\begin{align}\vdash\colon\colon{\sim} \phi(x,x).&{\sim} \phi(y,y):\phi(x,y).\equiv.\phi(y,x):\supset:\\ &(\exists z,w).z,w \in \iotaʻ x\cup \iotaʻ y.\phi(z,w).\equiv.\phi(x,y) \quad[\text{*54·451}]\end{align}\] -/
theorem pm54_452 {x y : α} {φ : α → α → Prop} :
    (¬φ x x ∧ ¬φ y y) ∧ (φ x y ↔ φ y x) →
      ((∃ z w, (z ∈ ι x ∪ ι y ∧ w ∈ ι x ∪ ι y) ∧ φ z w) ↔ φ x y) := by
  rintro ⟨h, he⟩
  rw [pm54_451 h]
  tauto

/-- ✱54·46. \(\vdash:( \exists z,w).z,w\in \iotaʻ x\cup \iotaʻ y.z\neq w.\equiv.x\neq y \quad[\text{*54·452.*13·15·16}]\) -/
theorem pm54_46 {x y : α} :
    (∃ z w, (z ∈ ι x ∪ ι y ∧ w ∈ ι x ∪ ι y) ∧ z ≠ w) ↔ x ≠ y :=
  pm54_452 (φ := fun z w => z ≠ w) ⟨⟨fun h => h rfl, fun h => h rfl⟩, ne_comm⟩

/-- ✱54·5. \(\vdash\colon\ldotp \alpha\in 2.\supset:\alpha\subset\iotaʻ z\cup\iotaʻ w.\equiv.\alpha=\iotaʻ z\cup \iotaʻ w\) -/
theorem pm54_5 {A : Set α} {z w : α} : A ∈ two → (A ⊆ ι z ∪ ι w ↔ A = ι z ∪ ι w) := by
  rintro ⟨x, y, hxy, rfl⟩
  refine ⟨fun h => ?_, fun h => h ▸ subset_refl _⟩
  apply pm51_421
  rcases h (Or.inl rfl) with (hx | hx) <;> rcases h (Or.inr rfl) with (hy | hy)
  · exact absurd ((hx : x = z).trans (hy : y = z).symm) hxy
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact absurd ((hx : x = w).trans (hy : y = w).symm) hxy

/-- ✱54·51. \( \vdash\colon\ldotp \alpha\in 2.\beta\in 1\cup 2.\supset:\alpha\subset\beta.\equiv.\alpha=\beta\) -/
theorem pm54_51 {A B : Set α} : A ∈ two ∧ B ∈ one ∪ two → (A ⊆ B ↔ A = B) := by
  rintro ⟨hA, (⟨b, rfl⟩ | ⟨z, w, -, rfl⟩)⟩
  · obtain ⟨x, y, hxy, rfl⟩ := hA
    refine ⟨fun h => ?_, fun h => h ▸ subset_refl _⟩
    exact absurd (((h (Or.inl rfl)) : x = b).trans ((h (Or.inr rfl)) : y = b).symm) hxy
  · exact pm54_5 hA

/-- ✱54·52. \(\vdash\colon\ldotp \alpha,\beta\in 2.\supset:\alpha\subset \beta.\equiv.\alpha=\beta.\equiv.\beta\subset \alpha \quad[\text{*54·51}]\) -/
theorem pm54_52 {A B : Set α} :
    A ∈ two ∧ B ∈ two → ((A ⊆ B ↔ A = B) ∧ (A = B ↔ B ⊆ A)) := by
  rintro ⟨hA, hB⟩
  exact ⟨pm54_51 ⟨hA, Or.inr hB⟩, ⟨fun h => h ▸ subset_refl _,
    fun h => ((pm54_51 ⟨hB, Or.inr hA⟩).1 h).symm⟩⟩

/-- ✱54·53. \(\vdash:\alpha\in 2.x,y\in\alpha.x\neq y.\supset.\alpha=\iotaʻ x\cup \iotaʻ y\) -/
theorem pm54_53 {A : Set α} {x y : α} :
    (A ∈ two ∧ (x ∈ A ∧ y ∈ A)) ∧ x ≠ y → A = ι x ∪ ι y := by
  rintro ⟨⟨hA, hx, hy⟩, hxy⟩
  have hsub : ι x ∪ ι y ⊆ A := by
    rintro z ((h : z = x) | (h : z = y))
    · exact h ▸ hx
    · exact h ▸ hy
  obtain ⟨a, b, -, rfl⟩ := hA
  exact ((pm54_5 (pm54_26.2 hxy)).1 hsub).symm

/-- ✱54·531. \(\vdash\colon\ldotp \alpha\in 2.\supset:x,y\in\alpha.x\neq y.\equiv.\alpha=\iotaʻ x\cup \iotaʻ y\) -/
theorem pm54_531 {A : Set α} {x y : α} :
    A ∈ two → ((x ∈ A ∧ y ∈ A) ∧ x ≠ y ↔ A = ι x ∪ ι y) := by
  intro hA
  refine ⟨fun h => pm54_53 ⟨⟨hA, h.1⟩, h.2⟩, ?_⟩
  rintro rfl
  exact ⟨⟨Or.inl rfl, Or.inr rfl⟩, pm54_26.1 hA⟩

/-- ✱54·54. \(\vdash\colon\ldotp \alpha\in 2.\equiv:x,y\in\alpha.x\neq y.\supset_{x,y}.\alpha=\iotaʻ x\cup \iotaʻ y:(\exists x,y).x,y\in\alpha.x\neq y\) -/
theorem pm54_54 {A : Set α} :
    A ∈ two ↔
      (∀ x y, (x ∈ A ∧ y ∈ A) ∧ x ≠ y → A = ι x ∪ ι y) ∧ ∃ x y, (x ∈ A ∧ y ∈ A) ∧ x ≠ y := by
  constructor
  · intro hA
    refine ⟨fun x y h => pm54_53 ⟨⟨hA, h.1⟩, h.2⟩, ?_⟩
    obtain ⟨x, y, hxy, rfl⟩ := hA
    exact ⟨x, y, ⟨Or.inl rfl, Or.inr rfl⟩, hxy⟩
  · rintro ⟨h, x, y, hm, hxy⟩
    rw [h x y ⟨hm, hxy⟩]
    exact pm54_26.2 hxy

/-- ✱54·55. \(\vdash.0\cup 1\cup 2=\hat{\alpha}{x,y\in\alpha.x\neq y.\supset_{x,y}.\alpha=\iotaʻ x\cup \iotaʻ y}\) -/
theorem pm54_55 :
    (zero ∪ one ∪ two : Set (Set α)) = {A | ∀ x y, (x ∈ A ∧ y ∈ A) ∧ x ≠ y → A = ι x ∪ ι y} := by
  ext A
  constructor
  · rintro ((h | ⟨a, rfl⟩) | h) x y ⟨⟨hx, hy⟩, hxy⟩
    · rw [show A = Λ from h] at hx; exact absurd rfl hx
    · exact absurd ((hx : x = a).trans (hy : y = a).symm) hxy
    · exact pm54_53 ⟨⟨h, hx, hy⟩, hxy⟩
  · intro h
    by_cases hA : A.Nonempty
    · obtain ⟨a, ha⟩ := hA
      by_cases hb : ∃ b, b ∈ A ∧ b ≠ a
      · obtain ⟨b, hbA, hba⟩ := hb
        rw [h a b ⟨⟨ha, hbA⟩, Ne.symm hba⟩]
        exact Or.inr (pm54_26.2 (Ne.symm hba))
      · push Not at hb
        refine Or.inl (Or.inr ⟨a, eq_unitCls_iff.2 fun z => ⟨hb z, fun e => e ▸ ha⟩⟩)
    · left; left
      show A = Λ
      rw [Null_eq_empty]; exact Set.not_nonempty_iff_eq_empty.1 hA

/-- ✱54·56. \(\vdash:\alpha{\sim}\in 0\cup 1\cup 2.\equiv.(\exists x,y,z).x,y,z\in\alpha.x\neq y.x\neq z.y\neq z\) -/
theorem pm54_56 {A : Set α} :
    A ∉ zero ∪ one ∪ two ↔
      ∃ x y z, ((((x ∈ A ∧ y ∈ A) ∧ z ∈ A) ∧ x ≠ y) ∧ x ≠ z) ∧ y ≠ z := by
  rw [pm54_55]
  show (¬ ∀ x y, (x ∈ A ∧ y ∈ A) ∧ x ≠ y → A = ι x ∪ ι y) ↔ _
  constructor
  · intro h
    push Not at h
    obtain ⟨x, y, ⟨⟨hx, hy⟩, hxy⟩, hne⟩ := h
    have : ∃ z, z ∈ A ∧ z ≠ x ∧ z ≠ y := by
      by_contra hc
      push Not at hc
      apply hne
      ext z
      constructor
      · intro hz
        by_cases e : z = x
        · exact Or.inl e
        · exact Or.inr (hc z hz e)
      · rintro ((e : z = x) | (e : z = y))
        · exact e ▸ hx
        · exact e ▸ hy
    obtain ⟨z, hz, hzx, hzy⟩ := this
    exact ⟨x, y, z, ⟨⟨⟨⟨hx, hy⟩, hz⟩, hxy⟩, Ne.symm hzx⟩, Ne.symm hzy⟩
  · rintro ⟨x, y, z, ⟨⟨⟨⟨hx, hy⟩, hz⟩, hxy⟩, hxz⟩, hyz⟩ h
    have := h x y ⟨⟨hx, hy⟩, hxy⟩
    rw [this] at hz
    rcases hz with (e | e)
    · exact hxz (e : z = x).symm
    · exact hyz (e : z = y).symm

/-- ✱54·6. \(\vdash\colon\ldotp \alpha\cap \beta=\Lambda.x,xʻ\in\alpha.y,yʻ\in\beta.\supset: \iotaʻ x\cup \iotaʻ y=\iotaʻ xʻ\cup \iotaʻ yʻ.\equiv.x=xʻ.y=yʻ\) -/
theorem pm54_6 {A B : Set α} {x x' y y' : α} :
    (A ∩ B = Λ ∧ (x ∈ A ∧ x' ∈ A)) ∧ (y ∈ B ∧ y' ∈ B) →
      (ι x ∪ ι y = ι x' ∪ ι y' ↔ x = x' ∧ y = y') := by
  rintro ⟨⟨hAB, hx, hx'⟩, hy, hy'⟩
  rw [pm51_43]
  refine ⟨fun h => h.resolve_right ?_, Or.inl⟩
  rintro ⟨e, -⟩
  have : x ∈ A ∩ B := ⟨hx, e ▸ hy'⟩
  rw [hAB] at this; exact this rfl

/-!
## [✱55] Ordinal couples

*(Vol. 1, p. 383)*

> *Summary of* *55.
>
> Ordinal couples, which are now to be considered, are much more important, even in cardinal arithmetic, than cardinal couples. Their properties are in part analogous to those of cardinal couples, but in part also to those of unit classes; for they are the smallest existent relations, just as unit classes are the smallest existent classes. The properties which are analogous to those of unit classes do not demand that the two terms of the couple should be distinct, *i.e.* they hold for \(\iotaʻ x\downarrow \iotaʻ x\) as well as for \(\iotaʻ x\uparrow \iotaʻ x\) (where \(x\neq y\)); on the other hand, the properties which are analogous to those of cardinal couples do in general demand that the two terms of the ordinal couple should be distinct.
>
> …

**Lean reading.** The ordinal couple `x ↓ y` is the heterogeneous relation `cross (ι x) (ι y)` (`x : α`, `y : β`;
✱55·01 by `rfl`), with `(x ↓ y) z w ↔ z = x ∧ w = y`. By ✱38 it gives the relations `x↓`
(`coupleL x`, of `x ↓ y` to `y`) and `↓y` (`coupleR y`, of `x ↓ y` to `x`), whose descriptive
functions always exist; ✱55·11·12·121, which give their values and existence, keep the
descriptions (`Desc (coupleL x) y`, …), elsewhere `x↓''α` is `coupleL x ʻʻ A`. ✱55·02 is the
bracketing convention `R'x↓y = R'(x↓y)`: `D'x↓y` is `dom (x ↓ y)`. Wherever a formula contains
`C'…` (✱55·15, ✱55·27, ✱55·282·283, ✱55·292, ✱55·53·54) the couples are homogeneous; the
type of `x↓` and `↓x` in ✱55·21–·27 is fixed by the context. `ῐ'(…)` (✱55·161·17) and
`S'z`, `S̆'x` (✱55·62·621) are descriptions; `(R ‖ S̆)'(z↓w)` (✱55·6·61) is the description
`Desc (R ∥ S˘) (z ↓ w)`. The relative products `R | (x↓y) | S` bracket to the left (✱34·22).
The e-text prints `↓ι'x` for `↓y'x` in ✱55·11, `x↓y'x` for `↓y'x` in ✱55·121, `R̆` for `R̂` in
✱55·22·221, `∪̇` for `∩̇` in ✱55·3, and `Λ` for `Λ̇` in ✱55·35 (Vol. I errata, p. 218); the
erratum to ✱55·281 (third `=` read `≡`) is already incorporated in the e-text.

**Status.** proved (all propositions; ✱55·01 definition; ✱55·02 definition (bracketing convention);
✱55·11, ✱55·121, ✱55·22, ✱55·221, ✱55·3, ✱55·35 proved (reading), see their docstrings).
-/

/-- ✱55·01 (Df). \(x\downarrow y=\iotaʻx\uparrow \iotaʻy \quad\text{Df}\) -/
theorem pm55_01 {x : α} {y : β} : x ↓ y = cross (ι x) (ι y) := rfl

/-- ✱55·02 (Df). \(Rʻx\downarrow y=Rʻ(x\downarrow y) \quad\text{Df}\)

**Status.** definition: a bracketing convention; `ψ(R'x↓y)` is `Desc R (x ↓ y) ψ`. -/
theorem pm55_02 {R : γ → (α → β → Prop) → Prop} {x : α} {y : β} {ψ : γ → Prop} :
    Desc R (x ↓ y) ψ ↔ TheIs (fun u => R u (x ↓ y)) ψ := Iff.rfl

/-- ✱55·1. \(\vdash.x\downarrow y=\iotaʻx\uparrow \iotaʻy \quad[\text{(*55·01)}]\) -/
theorem pm55_1 {x : α} {y : β} : x ↓ y = cross (ι x) (ι y) := rfl

/-- ✱55·11. \(\vdash.x\downarrowʻy=\downarrow \iotaʻx=x\downarrow y=\iotaʻx\uparrow\iotaʻy \quad[\text{*38·11.*55·1}]\)

**Status.** proved (reading): transcription error: the e-text prints `↓ι'x` for PM's `↓y'x` (the
descriptive function of the relation `↓y`, cf. ✱55·121·123 and the cited ✱38·11). -/
theorem pm55_11 {x : α} {y : β} :
    (Desc (coupleL x) y (fun R => Desc (coupleR y) x (fun S => R = S)) ∧
        Desc (coupleR y) x (fun S => S = x ↓ y)) ∧
      x ↓ y = cross (ι x) (ι y) := by
  rw [desc_coupleL, desc_coupleR, desc_coupleR]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- ✱55·12. \(\vdash.\text{E}!x\downarrowʻy \quad[\text{*55·11.*14·21}]\) -/
theorem pm55_12 {x : α} {y : β} : EDesc (coupleL x) y := EDesc_graph (couple x) y

/-- ✱55·121. \(\vdash.\text{E}!x\downarrow yʻx\)

**Status.** proved (reading): transcription error: the e-text prints `E!x↓y'x` for PM's `E!↓y'x` (the
descriptive function of `↓y` at `x`; cf. ✱55·21, which cites ✱55·12·121 for `x↓` and `↓x`). -/
theorem pm55_121 {x : α} {y : β} : EDesc (coupleR y) x := EDesc_graph (fun x' => x' ↓ y) x

/-- ✱55·122. \(\vdash:R(x\downarrow)y.\equiv.R=x\downarrow y \quad[\text{*55·11}]\) -/
theorem pm55_122 {x : α} {y : β} {R : α → β → Prop} : coupleL x R y ↔ R = x ↓ y := Iff.rfl

/-- ✱55·123. \(\vdash:R(\downarrow y)x.\equiv.R=x\downarrow y \quad[\text{*55·11}]\) -/
theorem pm55_123 {x : α} {y : β} {R : α → β → Prop} : coupleR y R x ↔ R = x ↓ y := Iff.rfl

/-- ✱55·13. \(\vdash:z(x\downarrow y)w.\equiv.z=x.w=y\) -/
theorem pm55_13 {x z : α} {y w : β} : (x ↓ y) z w ↔ z = x ∧ w = y := Iff.rfl

/-- ✱55·132. \(\vdash.x(x\downarrow y)y \quad[\text{*55·13}]\) -/
theorem pm55_132 {x : α} {y : β} : (x ↓ y) x y := ⟨rfl, rfl⟩

/-- ✱55·134. \(\vdash.\dot{\exists}!(x\downarrow y) \quad[\text{*55·132}]\) -/
theorem pm55_134 {x : α} {y : β} : rEx (x ↓ y) := ⟨x, y, rfl, rfl⟩

/-- ✱55·14. \(\vdash.x\downarrow y=\text{Cnv}ʻy\downarrow x \quad[\text{*55·13.*31·131}]\) -/
theorem pm55_14 {x : α} {y : β} : x ↓ y = (y ↓ x)˘ := by
  funext z w; exact propext and_comm

/-- ✱55·15. \(\vdash.\text{D}ʻx\downarrow y=\iotaʻx.\text{ᗡ}ʻx\downarrow y=\iotaʻy.Cʻx\downarrow y=\iotaʻx\cup\iotaʻy \quad[\text{*35·85·86.*51·161}]\) -/
theorem pm55_15 {x y : α} :
    (dom (x ↓ y) = ι x ∧ codom (x ↓ y) = ι y) ∧ fld (x ↓ y) = ι x ∪ ι y :=
  ⟨⟨dom_couple, codom_couple⟩, fld_couple⟩

/-- ✱55·16. \(\vdash:\text{D}ʻR=\iotaʻx.\text{ᗡ}ʻR=\iotaʻy.\equiv.R=x\downarrow y\) -/
theorem pm55_16 {R : α → β → Prop} {x : α} {y : β} :
    dom R = ι x ∧ codom R = ι y ↔ R = x ↓ y := by
  constructor
  · rintro ⟨hd, hc⟩
    funext z w; apply propext
    constructor
    · intro h
      have h1 : z ∈ dom R := ⟨w, h⟩
      have h2 : w ∈ codom R := ⟨z, h⟩
      rw [hd] at h1; rw [hc] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨rfl, rfl⟩
      have h1 : z ∈ dom R := by rw [hd]; exact rfl
      obtain ⟨w', hw'⟩ := h1
      have h2 : w' ∈ codom R := ⟨z, hw'⟩
      rw [hc] at h2
      rw [← (h2 : w' = w)]; exact hw'
  · rintro rfl; exact ⟨dom_couple, codom_couple⟩

/-- ✱55·161. \(\vdash.x\downarrow y=\breve{\iota}ʻ \hat{R}(\text{D}ʻ R=\iotaʻ x.\text{ᗡ}ʻ R=\iotaʻ y)\) -/
theorem pm55_161 {x : α} {y : β} :
    Desc iota˘ {R : α → β → Prop | dom R = ι x ∧ codom R = ι y} (fun S => x ↓ y = S) := by
  rw [desc_iota_cnv_iff]
  refine ⟨x ↓ y, ?_, rfl⟩
  ext R; exact pm55_16

/-- ✱55·17. \(\vdash.x\downarrow y=\breve{\iota}ʻ (\overleftarrow{\text{D}}ʻ\iotaʻ x\cap\overleftarrow{\text{ᗡ}}ʻ \iotaʻ y) \quad[\text{*55·161.*33·6·61}]\) -/
theorem pm55_17 {x : α} {y : β} :
    Desc iota˘ (rels D (ι x) ∩ rels Dcnv (ι y) : Set (α → β → Prop)) (fun S => x ↓ y = S) := by
  rw [desc_iota_cnv_iff]
  refine ⟨x ↓ y, ?_, rfl⟩
  ext R
  show ι x = dom R ∧ ι y = codom R ↔ R = x ↓ y
  rw [eq_comm, @eq_comm _ (ι y)]
  exact pm55_16

/-- ✱55·2. \(\vdash:x\downarrow y=x\downarrow z.\equiv.y=z\) -/
theorem pm55_2 {x : α} {y z : β} : x ↓ y = x ↓ z ↔ y = z := by
  rw [couple_eq_iff]; exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- ✱55·201. \(\vdash:x\downarrow z=y\downarrow z.\equiv.x=y\) -/
theorem pm55_201 {x y : α} {z : β} : x ↓ z = y ↓ z ↔ x = y := by
  rw [couple_eq_iff]; exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

/-- ✱55·202. \(\vdash:x\downarrow y=z\downarrow w.\equiv.x=z.y=w.\equiv.y\downarrow x=w\downarrow z\) -/
theorem pm55_202 {x z : α} {y w : β} :
    (x ↓ y = z ↓ w ↔ x = z ∧ y = w) ∧ (x = z ∧ y = w ↔ y ↓ x = w ↓ z) := by
  rw [couple_eq_iff, couple_eq_iff]
  exact ⟨Iff.rfl, and_comm⟩

/-- ✱55·21. \(\vdash.\text{ᗡ}ʻx\downarrow=V.\text{ᗡ}ʻ\downarrow x=\text{V} \quad[\text{*33·432.*55·12·121}]\) -/
theorem pm55_21 {x : α} :
    codom (coupleL x : (α → β → Prop) → β → Prop) = V ∧
      codom (coupleR x : (β → α → Prop) → β → Prop) = V := by
  constructor <;> ext y <;> simp

/-- ✱55·22. \(\vdash.\text{D}ʻx\downarrow =\breve{R}\{(\exists y).R=x\downarrow y\} \quad[\text{*55·122}]\)

**Status.** proved (reading): transcription error: the e-text prints `R̆{…}` for the class abstract
`R̂{(∃y) . R = x↓y}` (as in ✱70·01). -/
theorem pm55_22 {x : α} :
    dom (coupleL x : (α → β → Prop) → β → Prop) = {R | ∃ y, R = x ↓ y} := rfl

/-- ✱55·221. \(\vdash.\text{D}ʻ\downarrow x=\breve{R}\{(\exists y).R=y\downarrow x\} \quad[\text{*55·123}]\)

**Status.** proved (reading): transcription error: the e-text prints `R̆{…}` for `R̂{…}`, as in ✱55·22. -/
theorem pm55_221 {x : α} :
    dom (coupleR x : (β → α → Prop) → β → Prop) = {R | ∃ y, R = y ↓ x} := rfl

/-- ✱55·222. \(\vdash:R\in\text{D}ʻ x\downarrow.\equiv.\text{D}ʻ R=\iotaʻ x.\text{ᗡ}ʻ R\in 1\) -/
theorem pm55_222 {R : α → β → Prop} {x : α} :
    R ∈ dom (coupleL x : (α → β → Prop) → β → Prop) ↔ dom R = ι x ∧ codom R ∈ one := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨dom_couple, y, codom_couple⟩
  · rintro ⟨hd, y, hc⟩
    exact ⟨y, pm55_16.1 ⟨hd, hc⟩⟩

/-- ✱55·223. \(\vdash:R\in\text{D}ʻ \downarrow x.\equiv.\text{ᗡ}ʻ R=\iotaʻ x.\text{D}ʻ R\in 1 \quad[\text{Proof as in *55·222}]\) -/
theorem pm55_223 {R : β → α → Prop} {x : α} :
    R ∈ dom (coupleR x : (β → α → Prop) → β → Prop) ↔ codom R = ι x ∧ dom R ∈ one := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨codom_couple, y, dom_couple⟩
  · rintro ⟨hc, y, hd⟩
    exact ⟨y, pm55_16.1 ⟨hd, hc⟩⟩

/-- ✱55·224. \(\vdash.\text{D}ʻx\downarrow\cap \text{D}ʻ\downarrow y=\iotaʻ (x\downarrow y)\) -/
theorem pm55_224 {x : α} {y : β} :
    dom (coupleL x : (α → β → Prop) → β → Prop) ∩ dom (coupleR y : (α → β → Prop) → α → Prop) =
      ι (x ↓ y) := by
  ext R
  constructor
  · rintro ⟨⟨y', h1⟩, ⟨x', h2⟩⟩
    have h1' : R = x ↓ y' := h1
    have h2' : R = x' ↓ y := h2
    obtain ⟨-, e⟩ := couple_eq_iff.1 (h1'.symm.trans h2')
    show R = x ↓ y
    rw [h1', e]
  · intro (h : R = x ↓ y)
    exact ⟨⟨y, h⟩, ⟨x, h⟩⟩

/-- ✱55·23. \(\vdash.x\downarrow ʻʻ\alpha=\hat{R}{(\exists y).y\in\alpha.R=x\downarrow y} \quad[\text{*38·13}]\)

**Status.** proved: the e-text drops the braces of the class abstract. -/
theorem pm55_23 {x : α} {A : Set β} :
    coupleL x ʻʻ A = {R | ∃ y, y ∈ A ∧ R = x ↓ y} := rfl

/-- ✱55·231. \(\vdash.\downarrow xʻʻ\alpha=\hat{R}{(\exists y).y\in\alpha.R=y\downarrow x} \quad[\text{*38·131}]\)

**Status.** proved: the e-text drops the braces of the class abstract. -/
theorem pm55_231 {x : α} {A : Set β} :
    coupleR x ʻʻ A = {R | ∃ y, y ∈ A ∧ R = y ↓ x} := rfl

/-- ✱55·232. \(\vdash:\exists !\downarrow xʻʻ\alpha\cap \downarrow yʻʻ\beta.\equiv.x=y.\exists !\alpha\cap \beta\) -/
theorem pm55_232 {x y : β} {A B : Set α} :
    (coupleR x ʻʻ A ∩ coupleR y ʻʻ B).Nonempty ↔ x = y ∧ (A ∩ B).Nonempty := by
  constructor
  · rintro ⟨R, ⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
    have h1' : R = a ↓ x := h1
    have h2' : R = b ↓ y := h2
    obtain ⟨e1, e2⟩ := couple_eq_iff.1 (h1'.symm.trans h2')
    exact ⟨e2, a, ha, e1 ▸ hb⟩
  · rintro ⟨rfl, a, ha, hb⟩
    exact ⟨a ↓ x, ⟨a, ha, rfl⟩, ⟨a, hb, rfl⟩⟩

/-- ✱55·233. \(\vdash:x\neq y.\supset.\downarrow xʻʻ\alpha\cap \downarrow yʻʻ\beta=\Lambda \quad[\text{*55·232.Transp}]\) -/
theorem pm55_233 {x y : β} {A B : Set α} :
    x ≠ y → coupleR x ʻʻ A ∩ coupleR y ʻʻ B = Λ := by
  intro h
  rw [Null_eq_empty, ← Set.not_nonempty_iff_eq_empty, pm55_232]
  exact fun h' => h h'.1

/-- ✱55·24. \(\vdash.\dot{s}ʻ x\downarrowʻʻ\alpha=\iotaʻ x\uparrow\alpha\) -/
theorem pm55_24 {x : α} {A : Set β} : sumRel (coupleL x ʻʻ A) = cross (ι x) A := by
  funext z w; apply propext
  constructor
  · rintro ⟨R, ⟨y, hy, hR⟩, h⟩
    have hR' : R = x ↓ y := hR
    rw [hR'] at h
    obtain ⟨h1, rfl⟩ := h
    exact ⟨h1, hy⟩
  · rintro ⟨(h1 : z = x), h2⟩
    exact ⟨x ↓ w, ⟨w, h2, rfl⟩, h1, rfl⟩

/-- ✱55·241. \(\vdash.\dot{s}ʻ \downarrow xʻʻ \alpha=\alpha\uparrow\iotaʻ x \quad[\text{Proof as in *55·24}]\) -/
theorem pm55_241 {x : α} {A : Set β} : sumRel (coupleR x ʻʻ A) = cross A (ι x) := by
  funext z w; apply propext
  constructor
  · rintro ⟨R, ⟨y, hy, hR⟩, h⟩
    have hR' : R = y ↓ x := hR
    rw [hR'] at h
    obtain ⟨rfl, h2⟩ := h
    exact ⟨hy, h2⟩
  · rintro ⟨h1, (h2 : w = x)⟩
    exact ⟨z ↓ x, ⟨z, h1, rfl⟩, rfl, h2⟩

/-- ✱55·25. \(\vdash:\exists !\alpha.\supset.\text{D}ʻʻx\downarrow ʻʻ\alpha=\iotaʻ\iotaʻx\) -/
theorem pm55_25 {x : α} {A : Set β} : A.Nonempty → D ʻʻ coupleL x ʻʻ A = ι (ι x) := by
  rintro ⟨a, ha⟩
  ext B
  constructor
  · rintro ⟨R, ⟨y, -, hR⟩, hB⟩
    have hR' : R = x ↓ y := hR
    have hB' : B = dom R := hB
    show B = ι x
    rw [hB', hR', dom_couple]
  · intro (hB : B = ι x)
    exact ⟨x ↓ a, ⟨a, ha, rfl⟩, hB.trans dom_couple.symm⟩

/-- ✱55·251. \(\vdash:\exists !\alpha.\supset.\text{ᗡ}ʻʻ\downarrow xʻʻ \alpha=\iotaʻ\iotaʻx \quad[\text{Proof as in *55·25}]\) -/
theorem pm55_251 {x : α} {A : Set β} : A.Nonempty → Dcnv ʻʻ coupleR x ʻʻ A = ι (ι x) := by
  rintro ⟨a, ha⟩
  ext B
  constructor
  · rintro ⟨R, ⟨y, -, hR⟩, hB⟩
    have hR' : R = y ↓ x := hR
    have hB' : B = codom R := hB
    show B = ι x
    rw [hB', hR', codom_couple]
  · intro (hB : B = ι x)
    exact ⟨a ↓ x, ⟨a, ha, rfl⟩, hB.trans codom_couple.symm⟩

/-- ✱55·26. \(\vdash.\text{ᗡ}ʻʻ x\downarrow ʻʻ\alpha=\iotaʻʻ\alpha \quad[\text{*55·15.*37·35}]\) -/
theorem pm55_26 {x : α} {A : Set β} : Dcnv ʻʻ coupleL x ʻʻ A = iota ʻʻ A := by
  ext B
  constructor
  · rintro ⟨R, ⟨y, hy, hR⟩, hB⟩
    have hR' : R = x ↓ y := hR
    have hB' : B = codom R := hB
    exact ⟨y, hy, show B = ι y by rw [hB', hR', codom_couple]⟩
  · rintro ⟨y, hy, (hB : B = ι y)⟩
    exact ⟨x ↓ y, ⟨y, hy, rfl⟩, hB.trans codom_couple.symm⟩

/-- ✱55·261. \(\vdash.\text{D}ʻʻ \downarrow xʻʻ\alpha=\iotaʻʻ\alpha \quad[\text{*55·15.*37·35}]\) -/
theorem pm55_261 {x : α} {A : Set β} : D ʻʻ coupleR x ʻʻ A = iota ʻʻ A := by
  ext B
  constructor
  · rintro ⟨R, ⟨y, hy, hR⟩, hB⟩
    have hR' : R = y ↓ x := hR
    have hB' : B = dom R := hB
    exact ⟨y, hy, show B = ι y by rw [hB', hR', dom_couple]⟩
  · rintro ⟨y, hy, (hB : B = ι y)⟩
    exact ⟨y ↓ x, ⟨y, hy, rfl⟩, hB.trans dom_couple.symm⟩

/-- ✱55·262. \(\vdash.\downarrow xʻʻ\alpha=\downarrow yʻʻ\beta.\supset.\alpha=\beta \quad[\text{*55·261.*53·22}]\) -/
theorem pm55_262 {x y : α} {A B : Set β} : coupleR x ʻʻ A = coupleR y ʻʻ B → A = B := by
  intro h
  have := congrArg (fun K => sumCls (D ʻʻ K)) h
  simp only [pm55_261, pm53_22] at this
  exact this

/-- ✱55·27. \(\vdash.Cʻʻ \downarrow xʻʻ\alpha=Cʻʻx\downarrow ʻʻ\alpha=\hat{\beta}\{(\exists y).y\in\alpha.\beta=\iotaʻx\cup\iotaʻy\} \quad[\text{*55·15}]\) -/
theorem pm55_27 {x : α} {A : Set α} :
    C ʻʻ coupleR x ʻʻ A = C ʻʻ coupleL x ʻʻ A ∧
      C ʻʻ coupleL x ʻʻ A = {B | ∃ y, y ∈ A ∧ B = ι x ∪ ι y} := by
  have e2 : C ʻʻ coupleL x ʻʻ A = {B | ∃ y, y ∈ A ∧ B = ι x ∪ ι y} := by
    ext B
    constructor
    · rintro ⟨R, ⟨y, hy, hR⟩, hB⟩
      have hR' : R = x ↓ y := hR
      have hB' : B = fld R := hB
      exact ⟨y, hy, by rw [hB', hR', fld_couple]⟩
    · rintro ⟨y, hy, hB⟩
      exact ⟨x ↓ y, ⟨y, hy, rfl⟩, hB.trans fld_couple.symm⟩
  refine ⟨?_, e2⟩
  rw [e2]
  ext B
  constructor
  · rintro ⟨R, ⟨y, hy, hR⟩, hB⟩
    have hR' : R = y ↓ x := hR
    have hB' : B = fld R := hB
    exact ⟨y, hy, by rw [hB', hR', fld_couple, Set.union_comm]⟩
  · rintro ⟨y, hy, hB⟩
    exact ⟨y ↓ x, ⟨y, hy, rfl⟩, by show B = fld (y ↓ x); rw [hB, fld_couple, Set.union_comm]⟩

/-- ✱55·28. \(\vdash.\text{ᗡ}ʻx\downarrow y=\text{ᗡ}ʻx\downarrow z.\equiv.y=z.\equiv.x\downarrow y=x\downarrow z \quad[\text{*55·15.*51·23.*55·2}]\) -/
theorem pm55_28 {x : α} {y z : β} :
    (codom (x ↓ y) = codom (x ↓ z) ↔ y = z) ∧ (y = z ↔ x ↓ y = x ↓ z) := by
  rw [codom_couple, codom_couple]
  exact ⟨⟨fun h => unitCls_injective h, fun h => by rw [h]⟩, pm55_2.symm⟩

/-- ✱55·281. \(\vdash.\text{D}ʻy\downarrow x=\text{D}ʻz\downarrow x.\equiv.y=z.\equiv.y\downarrow x=z\downarrow x\)

**Status.** proved: the erratum (Vol. I errata, p. 388: for the third `=` read `≡`) is already
incorporated in the e-text. -/
theorem pm55_281 {x : β} {y z : α} :
    (dom (y ↓ x) = dom (z ↓ x) ↔ y = z) ∧ (y = z ↔ y ↓ x = z ↓ x) := by
  rw [dom_couple, dom_couple]
  exact ⟨⟨fun h => unitCls_injective h, fun h => by rw [h]⟩, pm55_201.symm⟩

/-- ✱55·282. \(\vdash:Cʻx\downarrow y=Cʻx\downarrow z.\equiv.y=z.\equiv.x\downarrow y=x\downarrow z \quad[\text{*55·15·2.*54·21}]\) -/
theorem pm55_282 {x y z : α} :
    (fld (x ↓ y) = fld (x ↓ z) ↔ y = z) ∧ (y = z ↔ x ↓ y = x ↓ z) := by
  rw [fld_couple, fld_couple]
  exact ⟨pm51_41, pm55_2.symm⟩

/-- ✱55·283. \(\vdash:Cʻy\downarrow x=Cʻz\downarrow x.\equiv.y=z.\equiv.y\downarrow x=z\downarrow x\) -/
theorem pm55_283 {x y z : α} :
    (fld (y ↓ x) = fld (z ↓ x) ↔ y = z) ∧ (y = z ↔ y ↓ x = z ↓ x) := by
  rw [fld_couple, fld_couple, Set.union_comm, Set.union_comm (ι z)]
  exact ⟨pm51_41, pm55_201.symm⟩

/-- ✱55·29. \(\vdash.\text{ᗡ}\mid(x\downarrow)=\iota \quad[\text{*55·15.*34·42}]\) -/
theorem pm55_29 {x : α} : Dcnv ⨾ (coupleL x : (α → β → Prop) → β → Prop) = iota := by
  funext B y; apply propext
  constructor
  · rintro ⟨R, hB, hR⟩
    have hR' : R = x ↓ y := hR
    have hB' : B = codom R := hB
    show B = ι y
    rw [hB', hR', codom_couple]
  · intro (hB : B = ι y)
    exact ⟨x ↓ y, hB.trans codom_couple.symm, rfl⟩

/-- ✱55·291. \(\vdash.\text{D}\mid(\downarrow x)=\iota \quad[\text{*55·15.*34·42}]\) -/
theorem pm55_291 {x : α} : D ⨾ (coupleR x : (β → α → Prop) → β → Prop) = iota := by
  funext B y; apply propext
  constructor
  · rintro ⟨R, hB, hR⟩
    have hR' : R = y ↓ x := hR
    have hB' : B = dom R := hB
    show B = ι y
    rw [hB', hR', dom_couple]
  · intro (hB : B = ι y)
    exact ⟨y ↓ x, hB.trans dom_couple.symm, rfl⟩

/-- ✱55·292. \(\vdash.C\mid(x\downarrow)=C\mid(\downarrow x)=\hat{\alpha}\hat{y}(\alpha=\iotaʻx\cup\iotaʻy) \quad[\text{*55·15.*34·41}]\) -/
theorem pm55_292 {x : α} :
    C ⨾ coupleL x = C ⨾ coupleR x ∧ C ⨾ coupleR x = fun A y => A = ι x ∪ ι y := by
  have e1 : C ⨾ coupleL x = fun A y => A = ι x ∪ ι y := by
    funext B y; apply propext
    constructor
    · rintro ⟨R, hB, hR⟩
      have hR' : R = x ↓ y := hR
      have hB' : B = fld R := hB
      rw [hB', hR', fld_couple]
    · intro hB
      exact ⟨x ↓ y, hB.trans fld_couple.symm, rfl⟩
  have e2 : C ⨾ coupleR x = fun A y => A = ι x ∪ ι y := by
    funext B y; apply propext
    constructor
    · rintro ⟨R, hB, hR⟩
      have hR' : R = y ↓ x := hR
      have hB' : B = fld R := hB
      rw [hB', hR', fld_couple, Set.union_comm]
    · intro hB
      exact ⟨y ↓ x, by show B = fld (y ↓ x); rw [hB, fld_couple, Set.union_comm], rfl⟩
  exact ⟨e1.trans e2.symm, e2⟩

/-- ✱55·3. \(\vdash:xRy.\equiv.x\downarrow y\unicode{x2abd}R.\equiv.\dot{\exists}!(x\downarrow y)\unicode{x228d} R \quad[\text{*13·21·22.*55·13}]\)

**Status.** proved (reading): transcription error: the e-text prints `∃̇!(x↓y) ∪̇ R` for PM's
`∃̇!(x↓y) ∩̇ R` (the comment compares ✱51·31, `∃!α ∩ ι'x`; with `∪̇` the right-hand side
would always hold). -/
theorem pm55_3 {R : α → β → Prop} {x : α} {y : β} :
    (R x y ↔ x ↓ y ⪽ R) ∧ (x ↓ y ⪽ R ↔ rEx (x ↓ y ⩀ R)) := by
  refine ⟨⟨fun h a b ⟨ha, hb⟩ => ha ▸ hb ▸ h, fun h => h x y ⟨rfl, rfl⟩⟩, ⟨?_, ?_⟩⟩
  · intro h; exact ⟨x, y, ⟨rfl, rfl⟩, h x y ⟨rfl, rfl⟩⟩
  · rintro ⟨a, b, ⟨rfl, rfl⟩, h⟩ c d ⟨rfl, rfl⟩; exact h

/-- ✱55·31. \(\vdash:x\downarrow y=z\downarrow w.\equiv.z(x\downarrow y)w.\equiv.x(z\downarrow w)y.\equiv.x=z.y=w\) -/
theorem pm55_31 {x z : α} {y w : β} :
    ((x ↓ y = z ↓ w ↔ (x ↓ y) z w) ∧ ((x ↓ y) z w ↔ (z ↓ w) x y)) ∧
      ((z ↓ w) x y ↔ x = z ∧ y = w) := by
  rw [couple_eq_iff]
  refine ⟨⟨⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩,
    ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩⟩, Iff.rfl⟩

/-- ✱55·32. \(\vdash\colon\ldotp x\downarrow y\dot{\cap}z\downarrow w=\dot{\Lambda}.\equiv:x\neq z.\lor.y\neq w\) -/
theorem pm55_32 {x z : α} {y w : β} : x ↓ y ⩀ z ↓ w = rNull ↔ x ≠ z ∨ y ≠ w := by
  rw [← rEx_iff_ne_rNull.not_left]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact h ⟨x, y, ⟨rfl, rfl⟩, rfl, rfl⟩
  · rintro h ⟨a, b, ⟨rfl, rfl⟩, h1, h2⟩
    rcases h with h | h
    · exact h h1
    · exact h h2

/-- ✱55·33. \(\vdash:xRy.\equiv.x\downarrow y\dot{\cap}R=x\downarrow y \quad[\text{*55·3.*23·621}]\) -/
theorem pm55_33 {R : α → β → Prop} {x : α} {y : β} : R x y ↔ x ↓ y ⩀ R = x ↓ y := by
  constructor
  · intro h
    funext a b; apply propext
    exact ⟨fun h' => h'.1, fun h' => ⟨h', h'.1 ▸ h'.2 ▸ h⟩⟩
  · intro h
    have : (x ↓ y ⩀ R) x y := by rw [h]; exact ⟨rfl, rfl⟩
    exact this.2

/-- ✱55·34. \(\vdash:\dot{\exists}!R.R\unicode{x2abd}x\downarrow y.\equiv.R=x\downarrow y\) -/
theorem pm55_34 {R : α → β → Prop} {x : α} {y : β} : rEx R ∧ R ⪽ x ↓ y ↔ R = x ↓ y := by
  have h341 : R ⪽ x ↓ y ↔ R = rNull ∨ R = x ↓ y := by
    rw [← toSet_sub, ← toSet_inj, ← toSet_inj (R := R), toSet_couple, toSet_rNull]
    exact Set.subset_singleton_iff_eq
  rw [h341, rEx_iff, rEx_iff_ne_rNull]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact absurd h2 h1
    · exact h2
  · rintro rfl
    refine ⟨fun h => ?_, Or.inr rfl⟩
    have : (x ↓ y) x y := ⟨rfl, rfl⟩
    rw [h] at this; exact rNull_apply _ _ this

/-- ✱55·341. \(\vdash\colon\ldotp R\unicode{x2abd}x\downarrow y.\equiv:R=\dot{\Lambda}.\lor.R=x\downarrow y\) -/
theorem pm55_341 {R : α → β → Prop} {x : α} {y : β} : R ⪽ x ↓ y ↔ R = rNull ∨ R = x ↓ y := by
  rw [← toSet_sub, ← toSet_inj, ← toSet_inj (R := R), toSet_couple, toSet_rNull]
  exact Set.subset_singleton_iff_eq

/-- ✱55·35. \(\vdash:R\dot{\cap}x\downarrow y=\Lambda.R\unicode{x228d}x\downarrow y=S.\equiv.xSy.R=S\dot{-}x\downarrow y\)

**Status.** proved (reading): erratum (Vol. I, p. 218): the e-text prints `Λ` where only a relation is
significant (`R ∩̇ x↓y = Λ`); it is read `Λ̇`, as in the demonstration. -/
theorem pm55_35 {R S : α → β → Prop} {x : α} {y : β} :
    R ⩀ x ↓ y = rNull ∧ R ⊍ x ↓ y = S ↔ S x y ∧ R = S ∸ x ↓ y := by
  constructor
  · rintro ⟨h1, rfl⟩
    have hn : ¬R x y := fun h => by
      have : (R ⩀ x ↓ y) x y := ⟨h, rfl, rfl⟩
      rw [h1] at this; exact rNull_apply _ _ this
    refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
    funext a b; apply propext
    constructor
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro ⟨rfl, rfl⟩; exact hn h
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd h h'
  · rintro ⟨hS, rfl⟩
    refine ⟨?_, ?_⟩
    · funext a b; apply propext
      exact ⟨fun ⟨⟨_, h⟩, h'⟩ => absurd h' h, fun h => absurd h (rNull_apply a b)⟩
    · funext a b; apply propext
      constructor
      · rintro (⟨h, _⟩ | ⟨rfl, rfl⟩)
        · exact h
        · exact hS
      · intro h
        by_cases e : (x ↓ y) a b
        · exact Or.inr e
        · exact Or.inl ⟨h, e⟩

/-- ✱55·36. \(\vdash:xRy.\equiv.(R\dot{-}x\downarrow y)\unicode{x228d}x\downarrow y=R\) -/
theorem pm55_36 {R : α → β → Prop} {x : α} {y : β} : R x y ↔ (R ∸ x ↓ y) ⊍ x ↓ y = R := by
  constructor
  · intro h
    funext a b; apply propext
    constructor
    · rintro (⟨h', _⟩ | ⟨rfl, rfl⟩)
      · exact h'
      · exact h
    · intro h'
      by_cases e : (x ↓ y) a b
      · exact Or.inr e
      · exact Or.inl ⟨h', e⟩
  · intro h
    have : ((R ∸ x ↓ y) ⊍ x ↓ y) x y := Or.inr ⟨rfl, rfl⟩
    rw [h] at this; exact this

/-- ✱55·37. \(\vdash:x\in\alpha.y\in\beta.\equiv.x\downarrow y\unicode{x2abd}\alpha\uparrow \beta\) -/
theorem pm55_37 {A : Set α} {B : Set β} {x : α} {y : β} :
    x ∈ A ∧ y ∈ B ↔ x ↓ y ⪽ cross A B := by
  constructor
  · rintro ⟨hx, hy⟩ a b ⟨rfl, rfl⟩; exact ⟨hx, hy⟩
  · intro h; exact h x y ⟨rfl, rfl⟩

/-- ✱55·4. \[\begin{align}&\vdash\colon\ldotp a{x\downarrow y\unicode{x228d}z\downarrow w}b.\equiv:a=x.b=y.\lor.a=z.b=w\\ &[\text{*55·13.*23·34}]\end{align}\]

**Status.** proved: the e-text drops the braces of `a{x↓y ∪̇ z↓w}b` in the TeX. -/
theorem pm55_4 {x z a : α} {y w b : β} :
    (x ↓ y ⊍ z ↓ w) a b ↔ (a = x ∧ b = y) ∨ (a = z ∧ b = w) := Iff.rfl

/-- ✱55·41. \(\vdash\colon\colon R=x\downarrow y\unicode{x228d}z\downarrow w.\supset\colon\ldotp aRb.\supset_{a,b}.\phi(a,b):\equiv.\phi(x,y).\phi(z,w)\) -/
theorem pm55_41 {R : α → β → Prop} {x z : α} {y w : β} {φ : α → β → Prop} :
    R = x ↓ y ⊍ z ↓ w → ((∀ a b, R a b → φ a b) ↔ φ x y ∧ φ z w) := by
  rintro rfl
  constructor
  · intro h; exact ⟨h x y (Or.inl ⟨rfl, rfl⟩), h z w (Or.inr ⟨rfl, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact h1
    · exact h2

/-- ✱55·42. \(\vdash\colon\colon R=x\downarrow y\unicode{x228d}z\downarrow w.\supset\colon\ldotp(\exists a,b).aRb.\phi(a,b).\equiv:\phi(x,y).\lor.\phi(z,w)\) -/
theorem pm55_42 {R : α → β → Prop} {x z : α} {y w : β} {φ : α → β → Prop} :
    R = x ↓ y ⊍ z ↓ w → ((∃ a b, R a b ∧ φ a b) ↔ φ x y ∨ φ z w) := by
  rintro rfl
  constructor
  · rintro ⟨a, b, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨x, y, Or.inl ⟨rfl, rfl⟩, h⟩
    · exact ⟨z, w, Or.inr ⟨rfl, rfl⟩, h⟩

/-- ✱55·43. \(\vdash:x\downarrow y\unicode{x228d}z\downarrow w=x\downarrow y\unicode{x228d}c\downarrow d.\equiv.z=c.w=d.\equiv.z\downarrow w=c\downarrow d\) -/
theorem pm55_43 {x z c : α} {y w d : β} :
    (x ↓ y ⊍ z ↓ w = x ↓ y ⊍ c ↓ d ↔ z = c ∧ w = d) ∧ (z = c ∧ w = d ↔ z ↓ w = c ↓ d) := by
  refine ⟨?_, couple_eq_iff.symm⟩
  rw [← toSet_inj, toSet_rcup, toSet_rcup, toSet_couple, toSet_couple, toSet_couple]
  have := @pm51_41 (α × β) (x, y) (z, w) (c, d)
  simp only [unitCls_eq_singleton] at this
  rw [this, Prod.mk.injEq]

/-- ✱55·431. \[\begin{align}\vdash\colon\ldotp x\downarrow y\unicode{x228d}z&\downarrow w=a\downarrow b\unicode{x228d}c\downarrow d.\supset:\\ &x=a.y=b.z=c.w=d.\lor.x=c.y=d.z=a.w=b\end{align}\] -/
theorem pm55_431 {x z a c : α} {y w b d : β} :
    x ↓ y ⊍ z ↓ w = a ↓ b ⊍ c ↓ d →
      (((x = a ∧ y = b) ∧ z = c) ∧ w = d) ∨ (((x = c ∧ y = d) ∧ z = a) ∧ w = b) := by
  rw [← toSet_inj, toSet_rcup, toSet_rcup, toSet_couple, toSet_couple, toSet_couple,
    toSet_couple, Set.singleton_union, Set.singleton_union]
  intro h
  rcases Set.pair_eq_pair_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [Prod.mk.injEq] at h1 h2
    exact Or.inl ⟨⟨h1, h2.1⟩, h2.2⟩
  · simp only [Prod.mk.injEq] at h1 h2
    exact Or.inr ⟨⟨h1, h2.1⟩, h2.2⟩

/-- ✱55·44. \[\begin{align}\vdash\colon\ldotp x\downarrow y & \unicode{x228d}z\downarrow w=a\downarrow b\unicode{x228d}c\downarrow d.\\ &\equiv:x=a.y=b.z=c.w=d.\lor.x=c.y=d.z=a.w=b:\\ &\equiv:x\downarrow y=a\downarrow b.z\downarrow w=c\downarrow d.\lor.x\downarrow y=c\downarrow d.z\downarrow w=a\downarrow b\end{align}\] -/
theorem pm55_44 {x z a c : α} {y w b d : β} :
    (x ↓ y ⊍ z ↓ w = a ↓ b ⊍ c ↓ d ↔
        (((x = a ∧ y = b) ∧ z = c) ∧ w = d) ∨ (((x = c ∧ y = d) ∧ z = a) ∧ w = b)) ∧
      ((((x = a ∧ y = b) ∧ z = c) ∧ w = d) ∨ (((x = c ∧ y = d) ∧ z = a) ∧ w = b) ↔
        (x ↓ y = a ↓ b ∧ z ↓ w = c ↓ d) ∨ (x ↓ y = c ↓ d ∧ z ↓ w = a ↓ b)) := by
  have e2 : (((x = a ∧ y = b) ∧ z = c) ∧ w = d) ∨ (((x = c ∧ y = d) ∧ z = a) ∧ w = b) ↔
      (x ↓ y = a ↓ b ∧ z ↓ w = c ↓ d) ∨ (x ↓ y = c ↓ d ∧ z ↓ w = a ↓ b) := by
    simp only [couple_eq_iff, and_assoc]
  refine ⟨⟨pm55_431, fun h => ?_⟩, e2⟩
  rcases e2.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    funext a' b'; exact propext or_comm

/-- ✱55·5. \[\begin{align}\vdash\colon\ldotp R\unicode{x2abd}x&\downarrow y\unicode{x228d}z\downarrow w.\\ &\equiv:R=\dot{\Lambda}.\lor.R=x\downarrow y.\lor.R=z\downarrow w.\lor.R=x\downarrow y\unicode{x228d}z\downarrow w\end{align}\] -/
theorem pm55_5 {R : α → β → Prop} {x z : α} {y w : β} :
    R ⪽ x ↓ y ⊍ z ↓ w ↔
      ((R = rNull ∨ R = x ↓ y) ∨ R = z ↓ w) ∨ R = x ↓ y ⊍ z ↓ w := by
  rw [← toSet_sub, ← toSet_inj, ← toSet_inj (S := x ↓ y), ← toSet_inj (S := z ↓ w),
    ← toSet_inj (S := x ↓ y ⊍ z ↓ w), toSet_rcup, toSet_couple, toSet_couple, toSet_rNull,
    Set.singleton_union, Set.subset_pair_iff_eq]
  simp only [or_assoc]

/-- ✱55·51. \(\vdash\colon\ldotp R \unicode{x2abd} x \downarrow y \unicode{x228d} S .\supset: x R y .\lor. R \unicode{x2abd} S\) -/
theorem pm55_51 {R S : α → β → Prop} {x : α} {y : β} : R ⪽ x ↓ y ⊍ S → R x y ∨ R ⪽ S := by
  intro h
  by_cases hxy : R x y
  · exact Or.inl hxy
  · right
    intro a b hab
    rcases h a b hab with ⟨rfl, rfl⟩ | h'
    · exact absurd hab hxy
    · exact h'

/-- ✱55·52. \(\vdash. (\iotaʻ x\cup \iotaʻ y)\uparrow(\iotaʻ z\cup \iotaʻ w)= x\downarrow z\unicode{x228d}x\downarrow w\unicode{x228d}y\downarrow z\unicode{x228d}y\downarrow w \quad[\text{*35·82·413}]\) -/
theorem pm55_52 {x y : α} {z w : β} :
    cross (ι x ∪ ι y) (ι z ∪ ι w) = x ↓ z ⊍ x ↓ w ⊍ y ↓ z ⊍ y ↓ w := by
  funext a b; apply propext
  show (a ∈ ι x ∪ ι y ∧ b ∈ ι z ∪ ι w) ↔
    (((a = x ∧ b = z) ∨ (a = x ∧ b = w)) ∨ (a = y ∧ b = z)) ∨ (a = y ∧ b = w)
  simp only [Set.mem_union, mem_unitCls]
  tauto

/-- ✱55·521. \(\vdash: x\neq y. \equiv .x\downarrow y\unicode{x2abd}J \quad[\text{*55·3.*50·11}]\) -/
theorem pm55_521 {x y : α} : x ≠ y ↔ x ↓ y ⪽ J := by
  constructor
  · rintro h a b ⟨rfl, rfl⟩; exact h
  · intro h; exact h x y ⟨rfl, rfl⟩

/-- ✱55·53. \(\vdash\colon\ldotp x \neq y.\supset: CʻR = \iotaʻ x\cup \iotaʻ y .R \unicode{x2abd} J .\equiv.\dot{\exists}!R.R\unicode{x2abd}x\downarrow y\unicode{x228d}y\downarrow x\) -/
theorem pm55_53 {R : α → α → Prop} {x y : α} :
    x ≠ y → (fld R = ι x ∪ ι y ∧ R ⪽ J ↔ rEx R ∧ R ⪽ x ↓ y ⊍ y ↓ x) := by
  intro hxy
  constructor
  · rintro ⟨hf, hJ⟩
    have hmem : ∀ z, z ∈ fld R ↔ z = x ∨ z = y := fun z => by rw [hf]; exact Iff.rfl
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw | hw⟩ := (hmem x).2 (Or.inl rfl)
      · exact ⟨x, w, hw⟩
      · exact ⟨w, x, hw⟩
    · intro a b hab
      have ha := (hmem a).1 ⟨b, Or.inl hab⟩
      have hb := (hmem b).1 ⟨a, Or.inr hab⟩
      have hne : a ≠ b := hJ a b hab
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hne
  · rintro ⟨⟨a, b, hab⟩, hs⟩
    refine ⟨?_, ?_⟩
    · ext z
      constructor
      · rintro ⟨w, h | h⟩
        · rcases hs _ _ h with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rcases hs _ _ h with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact Or.inr rfl
          · exact Or.inl rfl
      · rcases hs _ _ hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rintro ((h : z = a) | (h : z = b))
          · exact ⟨b, Or.inl (h ▸ hab)⟩
          · exact ⟨a, Or.inr (h ▸ hab)⟩
        · rintro ((h : z = b) | (h : z = a))
          · exact ⟨a, Or.inr (h ▸ hab)⟩
          · exact ⟨b, Or.inl (h ▸ hab)⟩
    · intro c d hcd e
      subst e
      rcases hs _ _ hcd with ⟨(h1 : c = x), (h2 : c = y)⟩ | ⟨(h1 : c = y), (h2 : c = x)⟩
      · exact hxy (h1.symm.trans h2)
      · exact hxy (h2.symm.trans h1)

/-- ✱55·54. \(\vdash\colon\colon x\neq y.\supset\colon\ldotp CʻR = \iotaʻ x\cup \iotaʻ y.R\dot{\cap}\breve{R} = \dot{\Lambda} . \equiv:R=x\downarrow y.\lor.R=y\downarrow x\) -/
theorem pm55_54 {R : α → α → Prop} {x y : α} :
    x ≠ y → (fld R = ι x ∪ ι y ∧ R ⩀ R˘ = rNull ↔ R = x ↓ y ∨ R = y ↓ x) := by
  intro hxy
  have asym_iff : R ⩀ R˘ = rNull ↔ ∀ a b, R a b → ¬R b a := by
    rw [rel_ext_iff]
    simp only [rcap_apply', cnv_apply', rNull_iff, iff_false, not_and]
  rw [asym_iff]
  constructor
  · rintro ⟨hf, ha⟩
    have hJ : R ⪽ J := fun a b hab e => ha a b hab (e ▸ hab)
    obtain ⟨⟨a, b, hab⟩, hs⟩ := (pm55_53 hxy).1 ⟨hf, hJ⟩
    by_cases hR : R x y
    · left
      funext c d; apply propext
      constructor
      · intro hcd
        rcases hs c d hcd with h | ⟨rfl, rfl⟩
        · exact h
        · exact absurd hR (ha _ _ hcd)
      · rintro ⟨rfl, rfl⟩; exact hR
    · right
      funext c d; apply propext
      constructor
      · intro hcd
        rcases hs c d hcd with ⟨rfl, rfl⟩ | h
        · exact absurd hcd hR
        · exact h
      · rintro ⟨rfl, rfl⟩
        rcases hs a b hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd hab hR
        · exact hab
  · rintro (rfl | rfl)
    · refine ⟨fld_couple, ?_⟩
      rintro a b ⟨(h1 : a = x), -⟩ ⟨-, (h4 : a = y)⟩; exact hxy (h1.symm.trans h4)
    · refine ⟨by rw [fld_couple, Set.union_comm], ?_⟩
      rintro a b ⟨(h1 : a = y), -⟩ ⟨-, (h4 : a = x)⟩; exact hxy (h4.symm.trans h1)

/-- ✱55·57. \(\vdash.R\mid(x\downarrow y)=\overrightarrow{R}ʻ x\uparrow\iotaʻ y \quad[\text{*37·81.*55·1.*53·301}]\) -/
theorem pm55_57 {R : α → β → Prop} {x : β} {y : γ} : R ⨾ (x ↓ y) = cross (refs R x) (ι y) := by
  funext a c; apply propext
  constructor
  · rintro ⟨b, h, rfl, rfl⟩; exact ⟨h, rfl⟩
  · rintro ⟨h, (hc : c = y)⟩; exact ⟨x, h, rfl, hc⟩

/-- ✱55·571. \(\vdash.(x\downarrow y)\mid S=\iotaʻ x\uparrow\overleftarrow{S}ʻ y\) -/
theorem pm55_571 {x : α} {y : β} {S : β → γ → Prop} : (x ↓ y) ⨾ S = cross (ι x) (rels S y) := by
  funext a c; apply propext
  constructor
  · rintro ⟨b, ⟨rfl, rfl⟩, h⟩; exact ⟨rfl, h⟩
  · rintro ⟨(ha : a = x), h⟩; exact ⟨y, ⟨ha, rfl⟩, h⟩

/-- ✱55·572. \(\vdash.R\mid(x\downarrow y)\mid S=\overrightarrow{R}ʻ x\uparrow\overleftarrow{S}ʻy \quad[\text{*55·571.*37·81}]\) -/
theorem pm55_572 {R : α → β → Prop} {x : β} {y : γ} {S : γ → δ → Prop} :
    R ⨾ (x ↓ y) ⨾ S = cross (refs R x) (rels S y) := by
  funext a d; apply propext
  constructor
  · rintro ⟨c, ⟨b, h1, rfl, rfl⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨y, ⟨x, h1, rfl, rfl⟩, h2⟩

/-- ✱55·573. \(\vdash.R\mid(x\downarrow y)\mid\breve{S}=\overrightarrow{R}ʻ x\uparrow\overrightarrow{S}ʻy \quad\left[\text{*55·572}\, \frac{\breve{S}}{S}\right]\) -/
theorem pm55_573 {R : α → β → Prop} {x : β} {y : γ} {S : δ → γ → Prop} :
    R ⨾ (x ↓ y) ⨾ S˘ = cross (refs R x) (refs S y) := pm55_572

/-- ✱55·58. \(\vdash:\text{E}!Rʻ x.\supset.R\mid(x\downarrow y)=(Rʻx)\downarrow y \quad[\text{*55·57.*53·31.*55·1}]\) -/
theorem pm55_58 {R : α → β → Prop} {x : β} {y : γ} :
    EDesc R x → Desc R x (fun b => R ⨾ (x ↓ y) = b ↓ y) := by
  rintro ⟨b, hb⟩
  refine ⟨b, hb, ?_⟩
  rw [pm55_57]
  have : refs R x = ι b := by ext z; exact hb z
  rw [this]; rfl

/-- ✱55·581. \(\vdash:\text{E}!\breve{S}ʻ y.\supset.(x\downarrow y)\mid S=x\downarrow(\breve{S}ʻy)\) -/
theorem pm55_581 {x : α} {y : β} {S : β → γ → Prop} :
    EDesc S˘ y → Desc S˘ y (fun b => (x ↓ y) ⨾ S = x ↓ b) := by
  rintro ⟨b, hb⟩
  refine ⟨b, hb, ?_⟩
  rw [pm55_571]
  have : rels S y = ι b := by ext z; exact hb z
  rw [this]; rfl

/-- ✱55·582. \(\vdash:\text{E}!Rʻ x.\text{E}!\breve{S}ʻ y.\supset.R\mid(x\downarrow y)\mid S=(Rʻx)\downarrow(\breve{S}ʻ y) \quad[\text{*55·58·581}]\) -/
theorem pm55_582 {R : α → β → Prop} {x : β} {y : γ} {S : γ → δ → Prop} :
    EDesc R x ∧ EDesc S˘ y →
      Desc R x (fun b => Desc S˘ y (fun c => R ⨾ (x ↓ y) ⨾ S = b ↓ c)) := by
  rintro ⟨⟨b, hb⟩, ⟨c, hc⟩⟩
  refine ⟨b, hb, c, hc, ?_⟩
  rw [pm55_572]
  have h1 : refs R x = ι b := by ext z; exact hb z
  have h2 : rels S y = ι c := by ext z; exact hc z
  rw [h1, h2]; rfl

/-- ✱55·583. \(\vdash:\text{E}!Rʻ x.\text{E}!Sʻ y.\supset.R\mid(x\downarrow y)\mid\breve{S}=(Rʻx)\downarrow(Sʻy) \quad\left[\text{*55·582}\, \frac{\breve{S}}{S}\right]\) -/
theorem pm55_583 {R : α → β → Prop} {x : β} {y : γ} {S : δ → γ → Prop} :
    EDesc R x ∧ EDesc S y →
      Desc R x (fun b => Desc S y (fun c => R ⨾ (x ↓ y) ⨾ S˘ = b ↓ c)) := pm55_582

/-- ✱55·6. \(\vdash.(R\Arrowvert\breve{S})ʻ (z\downarrow w)=\overrightarrow{R}ʻ z\uparrow\overrightarrow{S}ʻ w \quad[\text{*55·573.*43·112}]\) -/
theorem pm55_6 {R : α → β → Prop} {S : γ → δ → Prop} {z : β} {w : δ} :
    Desc (R ∥ S˘) (z ↓ w) (fun Q => Q = cross (refs R z) (refs S w)) := by
  rw [desc_dpar, ← relProd_assoc']
  exact pm55_573

/-- ✱55·61. \[\begin{align}&\vdash:\text{E}!Rʻ z.\text{E}!Sʻ w.\supset.(R\Arrowvert\breve{S})ʻ (z\downarrow w)=(Rʻz)\downarrow(Sʻw)\\ &[\text{*55·583.*43·112}]\end{align}\] -/
theorem pm55_61 {R : α → β → Prop} {S : γ → δ → Prop} {z : β} {w : δ} :
    EDesc R z ∧ EDesc S w →
      Desc (R ∥ S˘) (z ↓ w) (fun Q => Desc R z (fun b => Desc S w (fun c => Q = b ↓ c))) := by
  intro h
  rw [desc_dpar, ← relProd_assoc']
  exact pm55_583 h

/-- ✱55·62. \(\vdash:z\neq w.S=x\downarrow z\unicode{x228d}y\downarrow w.\supset.Sʻz=x.Sʻw=y\) -/
theorem pm55_62 {S : α → β → Prop} {x y : α} {z w : β} :
    z ≠ w ∧ S = x ↓ z ⊍ y ↓ w → Desc S z (fun b => b = x) ∧ Desc S w (fun b => b = y) := by
  rintro ⟨hzw, rfl⟩
  refine ⟨⟨x, fun a => ?_, rfl⟩, ⟨y, fun a => ?_, rfl⟩⟩
  · constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact h
      · exact absurd h hzw
    · intro h; exact Or.inl ⟨h, rfl⟩
  · constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd h.symm hzw
      · exact h
    · intro h; exact Or.inr ⟨h, rfl⟩

/-- ✱55·621. \[\begin{align}&\vdash:x\neq y.S=x\downarrow z\unicode{x228d}y\downarrow w.\supset.\breve{S}ʻ x=z.\breve{S}ʻ y=w\\ &[\text{Proof as in *55·6}]\end{align}\]

**Status.** proved: the e-text cites "Proof as in ✱55·6" (for ✱55·62). -/
theorem pm55_621 {S : α → β → Prop} {x y : α} {z w : β} :
    x ≠ y ∧ S = x ↓ z ⊍ y ↓ w → Desc S˘ x (fun b => b = z) ∧ Desc S˘ y (fun b => b = w) := by
  rintro ⟨hxy, rfl⟩
  refine ⟨⟨z, fun a => ?_, rfl⟩, ⟨w, fun a => ?_, rfl⟩⟩
  · constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd h hxy
    · intro h; exact Or.inl ⟨rfl, h⟩
  · constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h.symm hxy
      · exact h
    · intro h; exact Or.inr ⟨rfl, h⟩

/-- ✱55·63. \(\vdash:\dot{\exists}!Q\dot{\cap}S.P\Arrowvert Q=R\Arrowvert S.\supset.P=R\) -/
theorem pm55_63 {P R : α → β → Prop} {Q S : γ → δ → Prop} :
    rEx (Q ⩀ S) ∧ P ∥ Q = R ∥ S → P = R := by
  rintro ⟨⟨a, b, hQ, hS⟩, h⟩
  rw [dpar_eq_iff] at h
  funext x y; apply propext
  have := congrFun (congrFun (h (y ↓ a)) x) b
  rw [eq_iff_iff, relProd_couple_apply, relProd_couple_apply] at this
  exact ⟨fun h' => (this.1 ⟨h', hQ⟩).1, fun h' => (this.2 ⟨h', hS⟩).1⟩

/-- ✱55·631. \(\vdash:\dot{\exists}!P\dot{\cap}R.P\Arrowvert Q=R\Arrowvert S.\supset.Q=S \quad[\text{Proof as in *55·63}]\) -/
theorem pm55_631 {P R : α → β → Prop} {Q S : γ → δ → Prop} :
    rEx (P ⩀ R) ∧ P ∥ Q = R ∥ S → Q = S := by
  rintro ⟨⟨x, y, hP, hR⟩, h⟩
  rw [dpar_eq_iff] at h
  funext a b; apply propext
  have := congrFun (congrFun (h (y ↓ a)) x) b
  rw [eq_iff_iff, relProd_couple_apply, relProd_couple_apply] at this
  exact ⟨fun h' => (this.1 ⟨hP, h'⟩).2, fun h' => (this.2 ⟨hR, h'⟩).2⟩

/-- ✱55·632. \(\vdash:P\Arrowvert Q=R\Arrowvert S.\dot{\exists}!P.\dot{\exists}!Q.\supset.\dot{\exists}!P\dot{\cap}R.\dot{\exists}!Q\dot{\cap}S\) -/
theorem pm55_632 {P R : α → β → Prop} {Q S : γ → δ → Prop} :
    (P ∥ Q = R ∥ S ∧ rEx P) ∧ rEx Q → rEx (P ⩀ R) ∧ rEx (Q ⩀ S) := by
  rintro ⟨⟨h, ⟨x, y, hP⟩⟩, ⟨a, b, hQ⟩⟩
  rw [dpar_eq_iff] at h
  have := congrFun (congrFun (h (y ↓ a)) x) b
  rw [eq_iff_iff, relProd_couple_apply, relProd_couple_apply] at this
  obtain ⟨hR, hS⟩ := this.1 ⟨hP, hQ⟩
  exact ⟨⟨x, y, hP, hR⟩, ⟨a, b, hQ, hS⟩⟩

/-- ✱55·64. \[\begin{align}&\vdash\colon\ldotp \dot{\exists}!P.\dot{\exists}!Q.\lor.\dot{\exists}!R.\dot{\exists}!S:\supset:P\Arrowvert Q=R\Arrowvert S.\equiv.P=R.Q=S\\ &[\text{*55·63·631·632}]\end{align}\] -/
theorem pm55_64 {P R : α → β → Prop} {Q S : γ → δ → Prop} :
    (rEx P ∧ rEx Q) ∨ (rEx R ∧ rEx S) → (P ∥ Q = R ∥ S ↔ P = R ∧ Q = S) := by
  intro hex
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  have key : rEx (P ⩀ R) ∧ rEx (Q ⩀ S) := by
    rcases hex with ⟨hP, hQ⟩ | ⟨hR, hS⟩
    · exact pm55_632 ⟨⟨h, hP⟩, hQ⟩
    · obtain ⟨⟨x, y, h1, h2⟩, ⟨a, b, h3, h4⟩⟩ := pm55_632 ⟨⟨h.symm, hR⟩, hS⟩
      exact ⟨⟨x, y, h2, h1⟩, ⟨a, b, h4, h3⟩⟩
  exact ⟨pm55_63 ⟨key.2, h⟩, pm55_631 ⟨key.1, h⟩⟩

/-!
## [✱56] The ordinal number \(2_{r}\)

*(Vol. 1, p. 395)*

> *Summary of* *56.
>
> In this number, we have to consider the class of those relations which are each constituted by a single couple. In case the two members of this couple are not identical, the class of such relations is (as will be shown later) the ordinal number 2, which, to distinguish it from the cardinal number 2, we denote by "\(2_{r}\)." (Here the suffix is intended to suggest "relational.") The class of all relations consisting of a single couple, without the restriction that the two members of the couple are to be distinct, will be denoted by "\(\dot{2}\)." This is not an ordinal number. It will be observed that there is no ordinal number 1, because ordinal numbers apply to series, and series must have more than one member if they have any members. This will appear more fully when we come to deal with series.
>
> The properties of \(\dot{2}\) are largely analogous to those of 1, while the properties of \(2_{r}\) are more analogous to those of 2.
>
> Most of the propositions of the present number are seldom referred to in the sequel, but such references as occur are important. The most useful propositions in the present number are the following.
>
> …

**Lean reading.** `2̇` is `twoDot : Set (α → β → Prop)`, the class of single couples `x ↓ y` (heterogeneous);
`2_r` is `two_r : Set (α → α → Prop)` (homogeneous, since it requires `x ≠ y`); `0_r` is
`zero_r = ι Λ̇`, whose Df ✱56·03 is stated with `Desc iota rNull` (Basic §5). `D̆''1`,
`ᗡ̆''1`, `C̆''2` are `D˘ ʻʻ one`, `Dcnv˘ ʻʻ one`, `C˘ ʻʻ two`; `D⃖'ι'x` is `rels D (ι x)`;
`D'(x↓)` is `dom (coupleL x)`; `Λ ∩ Rel`, `V ∩ Rel` are classes of relations. Every proposition
mentioning `2_r` or `C'R` is homogeneous. ✱56·24·25 need members of the types (`[Nonempty _]`),
since `2̇` is null when `α` or `β` is empty. The e-text prints `⊂̇` for `⊂` in ✱56·121 (an
inclusion of classes of relations) and `Λ` for `Λ̇` in ✱56·261 (Vol. I errata, p. 218).

**Status.** proved (all propositions; ✱56·01·02·03 definition; ✱56·121, ✱56·24, ✱56·25, ✱56·261 proved
(reading), see their docstrings).
-/

/-- ✱56·01 (Df). \(\dot{2}=\hat{R}\{(\exists x,y).R=x\downarrow y\} \text{Df}\) -/
theorem pm56_01 : (twoDot : Set (α → β → Prop)) = {R | ∃ x y, R = x ↓ y} := rfl

/-- ✱56·02 (Df). \(2_{r}=\hat{R}\{(\exists x,y).x \neq y.R=x\downarrow y\} \text{Df}\) -/
theorem pm56_02 : (two_r : Set (α → α → Prop)) = {R | ∃ x y, x ≠ y ∧ R = x ↓ y} := rfl

/-- ✱56·03 (Df). \(0_{r}=\iotaʻ\dot{\Lambda} \text{Df}\) -/
theorem pm56_03 : Desc iota rNull (fun L => (zero_r : Set (α → β → Prop)) = L) :=
  (desc_graph _ _ _).2 rfl

/-- ✱56·1. \(\vdash:R\in \dot{2}.\equiv.(\exists x,y).R=x\downarrow y \quad[\text{*20·3.(*56·01)}]\) -/
theorem pm56_1 {R : α → β → Prop} : R ∈ twoDot ↔ ∃ x y, R = x ↓ y := Iff.rfl

/-- ✱56·101. \(\vdash:R\in \dot{2}.\equiv.\text{D}ʻR,\text{ᗡ}ʻR\in 1\) -/
theorem pm56_101 {R : α → β → Prop} : R ∈ twoDot ↔ dom R ∈ one ∧ codom R ∈ one := by
  constructor
  · rintro ⟨x, y, rfl⟩; exact ⟨⟨x, dom_couple⟩, ⟨y, codom_couple⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩; exact ⟨x, y, pm55_16.1 ⟨hx, hy⟩⟩

/-- ✱56·102. \(\vdash.\dot{2}=\breve{\text{D}}ʻʻ1\cap \breve{\text{ᗡ}}ʻʻ1\) -/
theorem pm56_102 : (twoDot : Set (α → β → Prop)) = (D˘ ʻʻ one) ∩ (Dcnv˘ ʻʻ one) := by
  ext R
  rw [Set.mem_inter_iff, mem_D_cnv_img, mem_Dcnv_cnv_img]
  exact pm56_101

/-- ✱56·103. \(\vdash:R\in \dot{2}.\supset.\dot{\exists}!R\) -/
theorem pm56_103 {R : α → β → Prop} : R ∈ twoDot → rEx R := by
  rintro ⟨x, y, rfl⟩; exact pm55_134

/-- ✱56·104. \(\vdash:R\in 0_{r}.\equiv.R=\dot{\Lambda} \quad[\text{(*56·03)}]\) -/
theorem pm56_104 {R : α → β → Prop} : R ∈ zero_r ↔ R = rNull := Iff.rfl

/-- ✱56·11. \(\vdash:R\in 2_{r}.\equiv.(\exists x,y).x \neq y.R=x\downarrow y \quad[\text{*20·3.(*56·02)}]\) -/
theorem pm56_11 {R : α → α → Prop} : R ∈ two_r ↔ ∃ x y, x ≠ y ∧ R = x ↓ y := Iff.rfl

/-- ✱56·111. \(\vdash:R\in 2_{r}.\equiv.\text{D}ʻR,\text{ᗡ}ʻR\in 1.\text{D}ʻR\cap \text{ᗡ}ʻR=\Lambda\) -/
theorem pm56_111 {R : α → α → Prop} :
    R ∈ two_r ↔ (dom R ∈ one ∧ codom R ∈ one) ∧ dom R ∩ codom R = Λ := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    rw [dom_couple, codom_couple]
    exact ⟨⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩, pm51_231.2 hxy⟩
  · rintro ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, h⟩
    rw [hx, hy] at h
    exact ⟨x, y, pm51_231.1 h, pm55_16.1 ⟨hx, hy⟩⟩

/-- ✱56·112. \(\vdash:R\in 2_{r}.\equiv.\text{D}ʻR,\text{ᗡ}ʻR\in 1.CʻR\in 2\) -/
theorem pm56_112 {R : α → α → Prop} :
    R ∈ two_r ↔ (dom R ∈ one ∧ codom R ∈ one) ∧ fld R ∈ two := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    rw [dom_couple, codom_couple, fld_couple]
    exact ⟨⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩, pm54_26.2 hxy⟩
  · rintro ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, h⟩
    have e := pm55_16.1 ⟨hx, hy⟩
    rw [e, fld_couple] at h
    exact ⟨x, y, pm54_26.1 h, e⟩

/-- ✱56·113. \(\vdash.2_{r}=\dot{2}\cap \breve{C}ʻʻ2\) -/
theorem pm56_113 : (two_r : Set (α → α → Prop)) = twoDot ∩ C˘ ʻʻ two := by
  ext R
  rw [Set.mem_inter_iff, mem_C_cnv_img, pm56_101, pm56_112]

/-- ✱56·114. \(\vdash.2_{r}=\breve{\text{D}}ʻʻ1\cap \breve{\text{ᗡ}}ʻʻ1\cap \breve{C}ʻʻ2 \quad[\text{*56·113·102}]\) -/
theorem pm56_114 : (two_r : Set (α → α → Prop)) = D˘ ʻʻ one ∩ Dcnv˘ ʻʻ one ∩ C˘ ʻʻ two := by
  rw [pm56_113, pm56_102]

/-- ✱56·12. \(\vdash:R\in 2_{r}.\equiv.R\in \dot{2}.R\unicode{x2abd}J\) -/
theorem pm56_12 {R : α → α → Prop} : R ∈ two_r ↔ R ∈ twoDot ∧ R ⪽ J := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩; exact ⟨⟨x, y, rfl⟩, pm55_521.1 hxy⟩
  · rintro ⟨⟨x, y, rfl⟩, h⟩; exact ⟨x, y, pm55_521.2 h, rfl⟩

/-- ✱56·121. \(\vdash.2_{r}\unicode{x2abd}\dot{2} \quad[\text{*56·113}]\)

**Status.** proved (reading): transcription error: the e-text prints `2_r ⊂̇ 2̇` for PM's `2_r ⊂ 2̇`
(an inclusion of classes of relations, from ✱56·113 `2_r = 2̇ ∩ C̆''2`). -/
theorem pm56_121 : (two_r : Set (α → α → Prop)) ⊆ twoDot := by
  rintro R ⟨x, y, -, rfl⟩; exact ⟨x, y, rfl⟩

/-- ✱56·122. \(\vdash:R\in 2_{r}.\supset.\dot{\exists}!R \quad[\text{*56·121·103}]\) -/
theorem pm56_122 {R : α → α → Prop} : R ∈ two_r → rEx R := fun h => pm56_103 (pm56_121 h)

/-- ✱56·13. \(\vdash.\dot{2}-2_{r}=\hat{R}\{(\exists a).R=a\downarrow a\}\) -/
theorem pm56_13 : (twoDot \ two_r : Set (α → α → Prop)) = {R | ∃ a, R = a ↓ a} := by
  ext R
  constructor
  · rintro ⟨⟨x, y, rfl⟩, h⟩
    by_cases e : x = y
    · exact ⟨x, by rw [e]⟩
    · exact absurd ⟨x, y, e, rfl⟩ h
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, a, rfl⟩, fun h => couple_mem_two_r.1 h rfl⟩

/-- ✱56·14. \(\vdash.\text{D}ʻ(x\downarrow )=\dot{2}\cap \overleftarrow{\text{D}}ʻ\iotaʻx\) -/
theorem pm56_14 {x : α} :
    dom (coupleL x : (α → β → Prop) → β → Prop) = twoDot ∩ rels D (ι x) := by
  ext R
  constructor
  · rintro ⟨y, (h : R = x ↓ y)⟩
    subst h
    exact ⟨⟨x, y, rfl⟩, show ι x = dom (x ↓ y) from dom_couple.symm⟩
  · rintro ⟨⟨a, b, rfl⟩, (h : ι x = dom (a ↓ b))⟩
    rw [dom_couple] at h
    exact ⟨b, show a ↓ b = x ↓ b by rw [unitCls_injective h]⟩

/-- ✱56·141. \(\vdash.\text{D}ʻ\downarrow x=\dot{2}\cap \overleftarrow{\text{ᗡ}}ʻ\iotaʻx \quad[\text{Proof as in *56·14}]\)

**Status.** proved: the e-text cites "Proof as in ✱56·14". -/
theorem pm56_141 {x : α} :
    dom (coupleR x : (β → α → Prop) → β → Prop) = twoDot ∩ rels Dcnv (ι x) := by
  ext R
  constructor
  · rintro ⟨y, (h : R = y ↓ x)⟩
    subst h
    exact ⟨⟨y, x, rfl⟩, show ι x = codom (y ↓ x) from codom_couple.symm⟩
  · rintro ⟨⟨a, b, rfl⟩, (h : ι x = codom (a ↓ b))⟩
    rw [codom_couple] at h
    exact ⟨a, show a ↓ b = a ↓ x by rw [unitCls_injective h]⟩

/-- ✱56·15. \(\vdash.\text{D}ʻ(x\downarrow )-\iotaʻ(x\downarrow x)=2_{r}\cap \overleftarrow{\text{D}}ʻ\iotaʻx\) -/
theorem pm56_15 {x : α} :
    dom (coupleL x : (α → α → Prop) → α → Prop) \ ι (x ↓ x) = two_r ∩ rels D (ι x) := by
  ext R
  constructor
  · rintro ⟨⟨y, (h : R = x ↓ y)⟩, (hne : R ≠ x ↓ x)⟩
    subst h
    refine ⟨couple_mem_two_r.2 fun e => hne (by rw [e]), ?_⟩
    show ι x = dom (x ↓ y); exact dom_couple.symm
  · rintro ⟨⟨a, b, hab, rfl⟩, (h : ι x = dom (a ↓ b))⟩
    rw [dom_couple] at h
    have e := unitCls_injective h
    subst e
    refine ⟨⟨b, rfl⟩, fun (h' : x ↓ b = x ↓ x) => hab (pm55_2.1 h').symm⟩

/-- ✱56·151. \(\vdash.\text{D}ʻ(\downarrow x)-\iotaʻ(x\downarrow x)=2_{r}\cap \overleftarrow{\text{ᗡ}}ʻ\iotaʻx \quad[\text{Proof as in *56·15}]\)

**Status.** proved: the e-text cites "Proof as in ✱56·15". -/
theorem pm56_151 {x : α} :
    dom (coupleR x : (α → α → Prop) → α → Prop) \ ι (x ↓ x) = two_r ∩ rels Dcnv (ι x) := by
  ext R
  constructor
  · rintro ⟨⟨y, (h : R = y ↓ x)⟩, (hne : R ≠ x ↓ x)⟩
    subst h
    refine ⟨couple_mem_two_r.2 fun e => hne (by rw [e]), ?_⟩
    show ι x = codom (y ↓ x); exact codom_couple.symm
  · rintro ⟨⟨a, b, hab, rfl⟩, (h : ι x = codom (a ↓ b))⟩
    rw [codom_couple] at h
    have e := unitCls_injective h
    subst e
    refine ⟨⟨a, rfl⟩, fun (h' : a ↓ x = x ↓ x) => hab (pm55_201.1 h')⟩

/-- ✱56·16. \(\vdash.x\downarrow y\in \dot{2}\) -/
theorem pm56_16 {x : α} {y : β} : x ↓ y ∈ twoDot := ⟨x, y, rfl⟩

/-- ✱56·17. \(\vdash:x\downarrow y\in 2_{r}.\equiv.y\downarrow x\in 2_{r}.\equiv.x \neq y\) -/
theorem pm56_17 {x y : α} :
    (x ↓ y ∈ two_r ↔ y ↓ x ∈ two_r) ∧ (y ↓ x ∈ two_r ↔ x ≠ y) := by
  rw [couple_mem_two_r, couple_mem_two_r]
  exact ⟨ne_comm, ne_comm⟩

/-- ✱56·18. \(\vdash:x{\sim}\in \alpha.\equiv.x\downarrow ʻʻ\alpha\subset 2_{r}.\equiv.\downarrow xʻʻ\alpha\subset 2_{r}\) -/
theorem pm56_18 {x : α} {A : Set α} :
    (x ∉ A ↔ coupleL x ʻʻ A ⊆ two_r) ∧ (coupleL x ʻʻ A ⊆ two_r ↔ coupleR x ʻʻ A ⊆ two_r) := by
  have e1 : coupleL x ʻʻ A ⊆ two_r ↔ ∀ y, y ∈ A → x ≠ y := by
    constructor
    · intro h y hy; exact couple_mem_two_r.1 (h ⟨y, hy, rfl⟩)
    · rintro h R ⟨y, hy, (hR : R = x ↓ y)⟩; rw [hR]; exact couple_mem_two_r.2 (h y hy)
  have e2 : coupleR x ʻʻ A ⊆ two_r ↔ ∀ y, y ∈ A → x ≠ y := by
    constructor
    · intro h y hy; exact (couple_mem_two_r.1 (h ⟨y, hy, rfl⟩)).symm
    · rintro h R ⟨y, hy, (hR : R = y ↓ x)⟩; rw [hR]; exact couple_mem_two_r.2 (h y hy).symm
  rw [e1, e2]
  refine ⟨⟨fun h y hy e => h (e ▸ hy), fun h hx => h x hx rfl⟩, Iff.rfl⟩

/-- ✱56·19. \(\vdash:R\in 2_{r}.x\in \text{D}ʻR.\equiv.(\exists y).x \neq y.R=x\downarrow y.\equiv.R\in x\downarrow ʻʻ-\iotaʻx\) -/
theorem pm56_19 {R : α → α → Prop} {x : α} :
    (R ∈ two_r ∧ x ∈ dom R ↔ ∃ y, x ≠ y ∧ R = x ↓ y) ∧
      ((∃ y, x ≠ y ∧ R = x ↓ y) ↔ R ∈ coupleL x ʻʻ (ι x)ᶜ) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨⟨a, b, hab, rfl⟩, hx⟩
    rw [dom_couple] at hx
    have e : x = a := hx
    subst e
    exact ⟨b, hab, rfl⟩
  · rintro ⟨y, h, rfl⟩
    exact ⟨couple_mem_two_r.2 h, by rw [dom_couple]; exact rfl⟩
  · rintro ⟨y, h, rfl⟩
    exact ⟨y, fun (e : y = x) => h e.symm, rfl⟩
  · rintro ⟨y, hy, (h : R = x ↓ y)⟩
    exact ⟨y, fun e => hy (show y = x from e.symm), h⟩

/-- ✱56·191. \[\begin{align}&\vdash:R\in 2_{r}.x\in \text{ᗡ}ʻR.\equiv.(\exists y).x \neq y.R=y\downarrow x.\equiv.R\in \downarrow xʻʻ-\iotaʻx\\ &[\text{Proof as in *56*19}]\end{align}\]

**Status.** proved: the e-text cites "Proof as in ✱56·19". -/
theorem pm56_191 {R : α → α → Prop} {x : α} :
    (R ∈ two_r ∧ x ∈ codom R ↔ ∃ y, x ≠ y ∧ R = y ↓ x) ∧
      ((∃ y, x ≠ y ∧ R = y ↓ x) ↔ R ∈ coupleR x ʻʻ (ι x)ᶜ) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨⟨a, b, hab, rfl⟩, hx⟩
    rw [codom_couple] at hx
    have e : x = b := hx
    subst e
    exact ⟨a, Ne.symm hab, rfl⟩
  · rintro ⟨y, h, rfl⟩
    exact ⟨couple_mem_two_r.2 (Ne.symm h), by rw [codom_couple]; exact rfl⟩
  · rintro ⟨y, h, rfl⟩
    exact ⟨y, fun (e : y = x) => h e.symm, rfl⟩
  · rintro ⟨y, hy, (h : R = y ↓ x)⟩
    exact ⟨y, fun e => hy (show y = x from e.symm), h⟩

/-- ✱56·2. \(\vdash\colon\ldotp R\in \dot{2}.\equiv:(\exists x,y):zRw.\equiv_{z,w}.z=x.w=y \quad[\text{*55·13.*56·1}]\) -/
theorem pm56_2 {R : α → β → Prop} : R ∈ twoDot ↔ ∃ x y, ∀ z w, R z w ↔ z = x ∧ w = y := by
  simp only [mem_twoDot', rel_ext_iff, couple_apply]

/-- ✱56·21. \(\vdash\colon\ldotp R\in \dot{2}.\equiv:\dot{\exists}!R:xRy.zRw.\supset_{x,y,z,w}.x=z.y=w \quad[\text{*56·2.*14·124}]\) -/
theorem pm56_21 {R : α → β → Prop} :
    R ∈ twoDot ↔ rEx R ∧ ∀ x y z w, R x y ∧ R z w → x = z ∧ y = w := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨pm55_134, ?_⟩
    rintro x y z w ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨⟨a, b, hab⟩, h⟩
    refine ⟨a, b, ?_⟩
    funext z w; apply propext
    constructor
    · intro hzw; exact h z w a b ⟨hzw, hab⟩
    · rintro ⟨rfl, rfl⟩; exact hab

/-- ✱56·22. \(\vdash.\dot{\Lambda}{\sim}\in \dot{2} \quad[\text{*56·103.*25·53}]\) -/
theorem pm56_22 : (rNull : α → β → Prop) ∉ twoDot := fun h => by
  obtain ⟨x, y, hxy⟩ := pm56_103 h
  exact rNull_apply x y hxy

/-- ✱56·24. \(\vdash.\exists !\dot{2}.\exists !-\dot{2} \quad[\text{*56·22·16.*10·24}]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): `2̇` is null
when `α` or `β` is empty, so `[Nonempty α]`, `[Nonempty β]` are added. -/
theorem pm56_24 [Nonempty α] [Nonempty β] :
    (twoDot : Set (α → β → Prop)).Nonempty ∧ (twoDotᶜ : Set (α → β → Prop)).Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty α›
  obtain ⟨y⟩ := ‹Nonempty β›
  exact ⟨⟨x ↓ y, pm56_16⟩, ⟨rNull, pm56_22⟩⟩

/-- ✱56·25. \(\vdash.\dot{2} \neq \Lambda\cap \text{Rel}.\dot{2} \neq \text{V}\cap \text{Rel} \quad[\text{*56·24.*24·54·17}]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): the first
half fails when `α` or `β` is empty (then `2̇` is null), so `[Nonempty α]`, `[Nonempty β]`
are added, as in ✱56·24. -/
theorem pm56_25 [Nonempty α] [Nonempty β] :
    (twoDot : Set (α → β → Prop)) ≠ Λ ∩ Rel ∧ (twoDot : Set (α → β → Prop)) ≠ V ∩ Rel := by
  constructor
  · intro h
    obtain ⟨R, hR⟩ := (pm56_24 (α := α) (β := β)).1
    rw [h] at hR
    exact hR.1 rfl
  · intro h
    have : (rNull : α → β → Prop) ∈ (V ∩ Rel : Set (α → β → Prop)) := ⟨rfl, mem_Rel'.2 trivial⟩
    rw [← h] at this
    exact pm56_22 this

/-- ✱56·26. \(\vdash\colon\ldotp R\in \dot{2}\cup \iotaʻ\dot{\Lambda}.\equiv:xRy.zRw.\supset_{x,y,z,w}.x=z.y=w\) -/
theorem pm56_26 {R : α → β → Prop} :
    R ∈ twoDot ∪ ι rNull ↔ ∀ x y z w, R x y ∧ R z w → x = z ∧ y = w := by
  constructor
  · rintro (h | (h : R = rNull))
    · exact (pm56_21.1 h).2
    · rintro x y z w ⟨hxy, -⟩; rw [h] at hxy; exact absurd hxy (rNull_apply x y)
  · intro h
    by_cases hR : rEx R
    · exact Or.inl (pm56_21.2 ⟨hR, h⟩)
    · right
      show R = rNull
      by_contra hc
      exact hR (rEx_iff_ne_rNull.2 hc)

/-- ✱56·261. \(\vdash\colon\colon R\in \dot{2}.\supset\colon\ldotp S\unicode{x2abd}R.\equiv:S=\Lambda.\lor.S=R\)

**Status.** proved (reading): erratum (Vol. I, p. 218): the e-text prints `S = Λ` where only a relation is
significant; it is read `S = Λ̇`, as in the demonstration (from ✱55·341). -/
theorem pm56_261 {R S : α → β → Prop} : R ∈ twoDot → (S ⪽ R ↔ S = rNull ∨ S = R) := by
  rintro ⟨x, y, rfl⟩; exact pm55_341

/-- ✱56·262. \(\vdash\colon\ldotp R\in \dot{2}.\supset:S\unicode{x2abd}R.\dot{\exists}!S.\equiv.S=R\) -/
theorem pm56_262 {R S : α → β → Prop} : R ∈ twoDot → (S ⪽ R ∧ rEx S ↔ S = R) := by
  rintro ⟨x, y, rfl⟩
  rw [and_comm]; exact pm55_34

/-- ✱56·27. \(\vdash\colon\ldotp R\in \dot{2}.\supset:\dot{\exists}!R\dot{\cap}S.\equiv.R\dot{\cap}S\in \dot{2}\) -/
theorem pm56_27 {R S : α → β → Prop} : R ∈ twoDot → (rEx (R ⩀ S) ↔ R ⩀ S ∈ twoDot) := by
  rintro ⟨x, y, rfl⟩
  refine ⟨fun h => ?_, pm56_103⟩
  have hS : S x y := pm55_3.1.2 (pm55_3.2.2 h)
  rw [pm55_33.1 hS]; exact pm56_16

/-- ✱56·28. \(\vdash\colon\ldotp R\in \dot{2}.\supset:\dot{\exists}!R\dot{\cap}S.\equiv.R\unicode{x2abd}S.\equiv.R\dot{\cap}S=R\) -/
theorem pm56_28 {R S : α → β → Prop} :
    R ∈ twoDot → ((rEx (R ⩀ S) ↔ R ⪽ S) ∧ (R ⪽ S ↔ R ⩀ S = R)) := by
  rintro ⟨x, y, rfl⟩
  exact ⟨pm55_3.2.symm, pm55_3.1.symm.trans pm55_33⟩

/-- ✱56·281. \(\vdash\colon\ldotp R\in 2_{r}.\supset:\dot{\exists}!R\dot{\cap}S.\equiv.R\unicode{x2abd}S.\equiv.R\dot{\cap}S=R.\equiv.R\dot{\cap}S\in 2_{r}\) -/
theorem pm56_281 {R S : α → α → Prop} :
    R ∈ two_r →
      (((rEx (R ⩀ S) ↔ R ⪽ S) ∧ (R ⪽ S ↔ R ⩀ S = R)) ∧ (R ⩀ S = R ↔ R ⩀ S ∈ two_r)) := by
  intro h
  have h2 := pm56_28 (S := S) (pm56_121 h)
  refine ⟨h2, ⟨fun e => by rw [e]; exact h, fun h' => ?_⟩⟩
  exact h2.2.1 (h2.1.1 (pm56_122 h'))

/-- ✱56·29. \(\vdash\colon\colon P,\, Q\in \dot{2}.\supset\colon\ldotp P\unicode{x2abd}Q\unicode{x228d}R.\equiv:P=Q.\lor.P\unicode{x2abd}R\) -/
theorem pm56_29 {P Q R : α → β → Prop} :
    P ∈ twoDot ∧ Q ∈ twoDot → (P ⪽ Q ⊍ R ↔ P = Q ∨ P ⪽ R) := by
  rintro ⟨⟨x, y, rfl⟩, ⟨z, w, rfl⟩⟩
  constructor
  · intro h
    rcases h x y ⟨rfl, rfl⟩ with ⟨h1, h2⟩ | h
    · exact Or.inl (couple_eq_iff.2 ⟨h1, h2⟩)
    · exact Or.inr (pm55_3.1.1 h)
  · rintro (h | h)
    · rw [h]; intro a b hab; exact Or.inl hab
    · intro a b hab; exact Or.inr (h a b hab)

/-- ✱56·3. \(\vdash\colon\ldotp P,\,Q\in \dot{2}.\supset:P\unicode{x2abd}Q.\equiv.P=Q.\equiv.\dot{\exists}!P\dot{\cap}Q\) -/
theorem pm56_3 {P Q : α → β → Prop} :
    P ∈ twoDot ∧ Q ∈ twoDot → ((P ⪽ Q ↔ P = Q) ∧ (P = Q ↔ rEx (P ⩀ Q))) := by
  rintro ⟨⟨x, y, rfl⟩, ⟨z, w, rfl⟩⟩
  have e1 : x ↓ y ⪽ z ↓ w ↔ x ↓ y = z ↓ w := by
    rw [← pm55_3.1, couple_eq_iff]; exact Iff.rfl
  exact ⟨e1, e1.symm.trans pm55_3.2⟩

/-- ✱56·31. \(\vdash\colon\ldotp P,\,Q\in \dot{2}.\supset:P \neq Q.\equiv.P\dot{\cap}Q=\dot{\Lambda} \quad[\text{*56·3.Transp}]\) -/
theorem pm56_31 {P Q : α → β → Prop} :
    P ∈ twoDot ∧ Q ∈ twoDot → (P ≠ Q ↔ P ⩀ Q = rNull) := by
  intro h
  rw [ne_eq, (pm56_3 h).2, rEx_iff, rEx_iff_ne_rNull, not_not]

/-- ✱56·32. \(\vdash:P\in \dot{2}.\supset.P\dot{\cap}Q\in \dot{2}\cup \iotaʻ\dot{\Lambda}\) -/
theorem pm56_32 {P Q : α → β → Prop} : P ∈ twoDot → P ⩀ Q ∈ twoDot ∪ ι rNull := by
  intro h
  rw [pm56_26]
  rintro x y z w ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
  exact (pm56_21.1 h).2 x y z w ⟨h1, h2⟩

/-- ✱56·33. \(\vdash\colon\colon P,\, Q\in \dot{2}.\supset\colon\ldotp R\unicode{x2abd}P\unicode{x228d}Q.\equiv:R=\dot{\Lambda}.\lor.R=P.\lor.R=Q.\lor.R=P\unicode{x228d}Q\) -/
theorem pm56_33 {P Q R : α → β → Prop} :
    P ∈ twoDot ∧ Q ∈ twoDot →
      (R ⪽ P ⊍ Q ↔ ((R = rNull ∨ R = P) ∨ R = Q) ∨ R = P ⊍ Q) := by
  rintro ⟨⟨x, y, rfl⟩, ⟨z, w, rfl⟩⟩; exact pm55_5

/-- ✱56·34. \(\vdash\colon\colon P,\,Q\in \dot{2}.P \neq Q.\supset\colon\ldotp R\unicode{x2abd}P\unicode{x228d}Q.\dot{\exists}!R.R\neq P\unicode{x228d}Q.\equiv:R=P.\lor.R=Q\) -/
theorem pm56_34 {P Q R : α → β → Prop} :
    (P ∈ twoDot ∧ Q ∈ twoDot) ∧ P ≠ Q →
      ((R ⪽ P ⊍ Q ∧ rEx R) ∧ R ≠ P ⊍ Q ↔ R = P ∨ R = Q) := by
  rintro ⟨⟨hP, hQ⟩, hne⟩
  have hPQ : P ≠ P ⊍ Q := by
    intro e
    have : Q ⪽ P := fun a b h => by
      have : (P ⊍ Q) a b := Or.inr h
      rw [← e] at this; exact this
    exact hne ((pm56_3 ⟨hQ, hP⟩).1.1 this).symm
  have hQP : Q ≠ P ⊍ Q := by
    intro e
    have : P ⪽ Q := fun a b h => by
      have : (P ⊍ Q) a b := Or.inl h
      rw [← e] at this; exact this
    exact hne ((pm56_3 ⟨hP, hQ⟩).1.1 this)
  constructor
  · rintro ⟨⟨hs, hex⟩, hR⟩
    rcases (pm56_33 ⟨hP, hQ⟩).1 hs with ((h | h) | h) | h
    · rw [rEx_iff, rEx_iff_ne_rNull] at hex; exact absurd h hex
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hR
  · rintro (rfl | rfl)
    · exact ⟨⟨fun a b h => Or.inl h, pm56_103 hP⟩, hPQ⟩
    · exact ⟨⟨fun a b h => Or.inr h, pm56_103 hQ⟩, hQP⟩

/-- ✱56·35. \(\vdash:CʻR\in 2.R\dot{\cap}\breve{R}=\dot{\Lambda}.\supset.R\in 2_{r}\) -/
theorem pm56_35 {R : α → α → Prop} : fld R ∈ two ∧ R ⩀ R˘ = rNull → R ∈ two_r := by
  rintro ⟨⟨x, y, hxy, hf⟩, ha⟩
  rcases (pm55_54 hxy).1 ⟨hf, ha⟩ with rfl | rfl
  · exact couple_mem_two_r.2 hxy
  · exact couple_mem_two_r.2 (Ne.symm hxy)

/-- ✱56·36. \(\vdash:R\in 2_{r}.\supset.CʻR\in 2.R\dot{\cap}\breve{R}=\dot{\Lambda}\) -/
theorem pm56_36 {R : α → α → Prop} : R ∈ two_r → fld R ∈ two ∧ R ⩀ R˘ = rNull := by
  rintro ⟨x, y, hxy, rfl⟩
  exact ⟨by rw [fld_couple]; exact pm54_26.2 hxy, ((pm55_54 hxy).2 (Or.inl rfl)).2⟩

/-- ✱56·37. \(\vdash:R\in 2_{r}.\equiv.CʻR\in 2.R\dot{\cap}\breve{R}=\dot{\Lambda} \quad[\text{*56·35·36}]\) -/
theorem pm56_37 {R : α → α → Prop} : R ∈ two_r ↔ fld R ∈ two ∧ R ⩀ R˘ = rNull :=
  ⟨pm56_36, pm56_35⟩

/-- ✱56·38. \(\vdash.2_{r}=\breve{C}ʻʻ2\cap \hat{R}(R\dot{\cap}\breve{R}=\dot{\Lambda})\) -/
theorem pm56_38 :
    (two_r : Set (α → α → Prop)) = C˘ ʻʻ two ∩ {R | R ⩀ R˘ = rNull} := by
  ext R
  rw [Set.mem_inter_iff, mem_C_cnv_img]
  exact pm56_37

/-- ✱56·381. \(\vdash:CʻR=\iotaʻx.\equiv.R=x\downarrow x\) -/
theorem pm56_381 {R : α → α → Prop} {x : α} : fld R = ι x ↔ R = x ↓ x := by
  constructor
  · intro h
    have hm : ∀ z, z ∈ fld R ↔ z = x := fun z => by rw [h]; exact Iff.rfl
    funext a b; apply propext
    constructor
    · intro hab
      exact ⟨(hm a).1 ⟨b, Or.inl hab⟩, (hm b).1 ⟨a, Or.inr hab⟩⟩
    · rintro ⟨(ha : a = x), (hb : b = x)⟩
      rw [ha, hb]
      obtain ⟨w, hw | hw⟩ := (hm x).2 rfl
      · have : w = x := (hm w).1 ⟨x, Or.inr hw⟩
        rw [this] at hw; exact hw
      · have : w = x := (hm w).1 ⟨x, Or.inl hw⟩
        rw [this] at hw; exact hw
  · rintro rfl
    rw [fld_couple, Set.union_self]

/-- ✱56·39. \(\vdash.\dot{2}-2_{r}=\breve{C}ʻʻ1\) -/
theorem pm56_39 : (twoDot \ two_r : Set (α → α → Prop)) = C˘ ʻʻ one := by
  rw [pm56_13]
  ext R
  rw [mem_C_cnv_img]
  constructor
  · rintro ⟨a, h⟩; exact ⟨a, pm56_381.2 h⟩
  · rintro ⟨a, h⟩; exact ⟨a, pm56_381.1 h⟩

/-- ✱56·4. \(\vdash\colon\ldotp \mu\subset \dot{2}.\supset:x\downarrow y\in \mu.\equiv.x(\dot{s}ʻ\mu)y\) -/
theorem pm56_4 {M : Set (α → β → Prop)} {x : α} {y : β} :
    M ⊆ twoDot → (x ↓ y ∈ M ↔ sumRel M x y) := by
  intro hM
  constructor
  · intro h; exact ⟨x ↓ y, h, rfl, rfl⟩
  · rintro ⟨R, hR, hxy⟩
    obtain ⟨a, b, rfl⟩ := hM hR
    obtain ⟨rfl, rfl⟩ := hxy
    exact hR

end PrincipiaMathematica
