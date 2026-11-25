import PrincipiaMathematica.Defs.Part2

/-!
# Part II, Section D: Selections

Volume 1. Numbers: ✱80, ✱81, ✱82, ✱83, ✱84, ✱85, ✱88.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w u' v'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'} {ε : Type v'}

/-!
## [✱80] Elementary properties of selections

*(Vol. 1, p. 505)*

> *Summary of* *80.
>
> In this number, we shall give such properties of \(P_{\Delta}\) as follow most directly from the definition, without any restrictive hypothesis as to \(P\).
>
> If \(R \in P_{\Delta}ʻ\kappa\), \(R\) selects one member of \(\overrightarrow{P}ʻy\), whenever \(y \in \kappa\), as the selected referent of \(y\). For, since \(R \in 1 \rightarrow\text{Cls} . \text{ᗡ}ʻR = \kappa\), we have \(y \in \kappa .\supset.\text{E}!Rʻy\); and since \(R \unicode{x2abd} P\), we have \(y \in \kappa .\supset.(Rʻy)Py\), *i.e.* \(y \in \kappa .\supset. Rʻy \in \overrightarrow{P}ʻy\). Calling \(Rʻy\) the *selected referent* of \(y\), it is evident that we may replace \(Rʻy\) by any other member of \(\overrightarrow{P}ʻy\), and still have a member of \(P_{\Delta}ʻ\kappa\). (This is proved in *80·4.) Thus if \(P_{\Delta}ʻ\kappa\) has any members at all, we can get as many members as there are members of \(\overrightarrow{P}ʻy\) by merely altering the selected referent of \(y\), leaving the other selected referents unchanged.
>
> In the present section, we first prove various simple properties of \(P_{\Delta}ʻ\kappa\). Most of these are almost immediate consequences of
>
> …

**Lean reading.** `P_Δ` is `selRel P = graph (sel P)` (✱80·01), with `P : α → β → Prop`
heterogeneous and `κ : Set β`. Since `P_Δ'κ` always exists, it is written as its value `sel P K` (`=
(1 → Cls) ∩ Rl'P ∩ ᗡ⃖'κ`), except in ✱80·11–·13, where PM proves its existence and value and which
keep `Desc`/`EDesc`. `R ∈ P_Δ'κ` is unfolded by the lemma `sel_iff` (one-many, contained in `P`,
converse domain `κ`; cf. ✱80·14), and `R'y` is `Desc R y ψ` with the smallest scope. `Λ` is the null
class at the type the formula forces (of relations in ✱80·21·27·82, of classes of classes in
✱80·83), `Λ̇` is `rNull`, `x ↓ y` is `couple`, `D''λ` is `D ʻʻ λ` and `ṡ'λ` is `sumRel λ`. Flat
products of hypotheses are bracketed to the left, and chains such as ✱80·74 are conjunctions of
their links. Most proofs unfold everything to first-order logic and close it with `grind`.

**Status.** proved (all propositions; ✱80·01 definition; ✱80·13 proved (reading): transcription
error, see its docstring).
-/

/-- Membership in `P_Δ'κ`, fully unfolded (cf. ✱80·14): `M` is one-many, contained in `P`, and its
converse domain is `κ`. -/
theorem sel_iff {P M : α → β → Prop} {K : Set β} :
    M ∈ sel P K ↔ (∀ x y z, M x z → M y z → x = y) ∧ (∀ x y, M x y → P x y) ∧
      (∀ x y, M x y → y ∈ K) ∧ (∀ y, y ∈ K → ∃ x, M x y) := by
  rw [mem_sel_iff, mem_arrow_one_Cls]
  constructor
  · rintro ⟨⟨h1, h2⟩, rfl⟩
    exact ⟨fun x y z hx hy => h1 x y z ⟨hx, hy⟩, h2, fun x y h => ⟨x, h⟩, fun y h => h⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨fun x y z h => h1 x y z h.1 h.2, h2⟩, ?_⟩
    ext y; exact ⟨fun ⟨x, h⟩ => h3 x y h, h4 y⟩

/-- Unfold the selections, relations and classes of Section D to first-order logic. -/
local macro "sel_simp" : tactic => `(tactic| simp only [sel_iff, rcup, rcap, rdiff, rneg, cres,
  dres, bres, couple_apply, cross, mem_unitCls, refs, rels, img, dom, codom, Set.mem_ofPred_eq,
  Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff, RSub, relProd, sumRel,
  Null_eq_empty, Set.mem_empty_iff_false, mem_rl, rNull, rV, Set.subset_def, rel_eq_iff,
  Set.ext_iff, Set.Nonempty, D, Dcnv, graph, eq_iff_iff, ne_eq, false_iff, iff_false,
  not_exists, mem_arrow_Cls_one, mem_arrow_one_Cls, mem_arrow_one_one, cnv, exists_imp, and_imp] at *)

/-- `ψ(R'y)` when `b` is the only referent of `y`. -/
theorem desc_iff_of {R : α → β → Prop} {y : β} {ψ : α → Prop} {b : α} (hb : R b y)
    (hu : ∀ x, R x y → x = b) : Desc R y ψ ↔ ψ b :=
  TheIs_iff_of_unique (fun x => ⟨hu x, fun h => h ▸ hb⟩)

/-- `ψ(R'y) . ≡ . E!R'y . (x) . xRy ⊃ ψx` (✱14·22-like). -/
theorem desc_iff {R : α → β → Prop} {y : β} {ψ : α → Prop} :
    Desc R y ψ ↔ EDesc R y ∧ ∀ x, R x y → ψ x := TheIs_iff

/-- A member of `P_Δ'κ` has exactly one referent for each `y ∈ κ`. -/
theorem sel_ex {P M : α → β → Prop} {K : Set β} (h : M ∈ sel P K) {y : β} (hy : y ∈ K) :
    ∃ x, M x y ∧ ∀ x', M x' y → x' = x := by
  rw [sel_iff] at h
  obtain ⟨x, hx⟩ := h.2.2.2 y hy
  exact ⟨x, hx, fun x' hx' => h.1 x' x y hx' hx⟩

theorem sel_codom_iff {P M : α → β → Prop} {K : Set β} (h : M ∈ sel P K) {y : β} :
    y ∈ K ↔ ∃ x, M x y :=
  ⟨(sel_iff.1 h).2.2.2 y, fun ⟨x, hx⟩ => (sel_iff.1 h).2.2.1 x y hx⟩

theorem sel_edesc {P M : α → β → Prop} {K : Set β} (h : M ∈ sel P K) {y : β} (hy : y ∈ K) :
    EDesc M y := by
  obtain ⟨x, hx, hu⟩ := sel_ex h hy
  exact ⟨x, fun z => ⟨hu z, fun e => e ▸ hx⟩⟩

/-- ✱80·01 (Df). \(P_{\Delta}=\hat{\lambda}\hat{\kappa}\{\lambda=(1\rightarrow \text{Cls})\cap \text{Rl}ʻP\cap \overleftarrow{\text{ᗡ}}ʻ\kappa\} \quad\text{Df}\) -/
theorem pm80_01 {P : α → β → Prop} :
    selRel P = fun L K => L = arrow one Cls ∩ rl P ∩ rels Dcnv K := rfl

/-- ✱80·1. \(\vdash:\lambda P_{\Delta}\kappa.\equiv.\lambda=(1\rightarrow \text{Cls})\cap \text{Rl}ʻP\cap \overleftarrow{\text{ᗡ}}ʻ\kappa \quad[\text{*21·3.(*80·01)}]\) -/
theorem pm80_1 {P : α → β → Prop} {L : Set (α → β → Prop)} {K : Set β} :
    selRel P L K ↔ L = arrow one Cls ∩ rl P ∩ rels Dcnv K := Iff.rfl

/-- ✱80·11. \(\vdash.P_{\Delta}ʻ\kappa=(1\rightarrow \text{Cls})\cap \text{Rl}ʻP\cap \overleftarrow{\text{ᗡ}}ʻ\kappa \quad[\text{*80·1.*30·3}]\) -/
theorem pm80_11 {P : α → β → Prop} {K : Set β} :
    Desc (selRel P) K (fun L => L = arrow one Cls ∩ rl P ∩ rels Dcnv K) :=
  (desc_selRel P K _).2 rfl

/-- ✱80·12. \(\vdash.\text{E}!P_{\Delta}ʻ\kappa \quad[\text{*80·11.*14·21}]\) -/
theorem pm80_12 {P : α → β → Prop} {K : Set β} : EDesc (selRel P) K := EDesc_graph (sel P) K

/-- ✱80·13. \(\vdash:\lambda P_{\Delta}ʻ\kappa.\equiv.\lambda=P_{\Delta}ʻ\kappa \quad[\text{*80·12.*30·4}]\)

**Status.** proved (reading): transcription error: the e-text prints `λ P_Δ'κ` for `λ P_Δ κ` on the
left (PM cites ✱30·4, `E!R'y . ⊃ : x = R'y . ≡ . xRy`, with ✱80·12). -/
theorem pm80_13 {P : α → β → Prop} {L : Set (α → β → Prop)} {K : Set β} :
    selRel P L K ↔ Desc (selRel P) K (fun M => L = M) := by
  rw [desc_selRel]; exact Iff.rfl

/-- ✱80·14. \[\begin{align}&\vdash:R\in P_{\Delta}ʻ\kappa.\equiv.R\in 1\rightarrow \text{Cls}.R\unicode{x2abd}P.\text{ᗡ}ʻR=\kappa\\ &[\text{*80·11.*20·43.*22·33.*61·2.*33·61}]\end{align}\] -/
theorem pm80_14 {P R : α → β → Prop} {K : Set β} :
    R ∈ sel P K ↔ (R ∈ arrow one Cls ∧ R ⪽ P) ∧ codom R = K := mem_sel_iff

/-- ✱80·15. \(\vdash:P\unicode{x2abd}Q.\supset.P_{\Delta}ʻ\kappa\subset Q_{\Delta}ʻ\kappa \quad[\text{*80·14}]\) -/
theorem pm80_15 {P Q : α → β → Prop} {K : Set β} : P ⪽ Q → sel P K ⊆ sel Q K := by
  intro h M hM
  sel_simp
  grind

/-- ✱80·16. \(\vdash:R\in P_{\Delta}ʻ\kappa.R\unicode{x2abd}Q.\supset.R\in Q_{\Delta}ʻ\kappa\) -/
theorem pm80_16 {P Q R : α → β → Prop} {K : Set β} : R ∈ sel P K ∧ R ⪽ Q → R ∈ sel Q K := by
  intro h
  sel_simp
  grind

/-- ✱80·17. \(\vdash:Q\unicode{x2abd}P.\supset.Q_{\Delta}ʻ\kappa=P_{\Delta}ʻ\kappa\cap \text{Rl}ʻQ\) -/
theorem pm80_17 {P Q : α → β → Prop} {K : Set β} : Q ⪽ P → sel Q K = sel P K ∩ rl Q := by
  intro h
  sel_simp
  grind

/-- ✱80·2. \(\vdash:\exists !P_{\Delta}ʻ\kappa.\supset.\kappa\subset \text{ᗡ}ʻP\) -/
theorem pm80_2 {P : α → β → Prop} {K : Set β} : (sel P K).Nonempty → K ⊆ codom P := by
  intro h
  sel_simp
  grind

/-- ✱80·21. \(\vdash:{\sim}(\kappa\subset \text{ᗡ}ʻP).\supset.P_{\Delta}ʻ\kappa=\Lambda \quad[\text{*80·2.Transp}]\) -/
theorem pm80_21 {P : α → β → Prop} {K : Set β} : ¬(K ⊆ codom P) → sel P K = Λ := by
  intro h
  ext M
  refine ⟨fun hM => absurd (pm80_2 ⟨M, hM⟩) h, fun hM => ?_⟩
  rw [Null_eq_empty] at hM
  exact hM.elim

/-- ✱80·22. \(\vdash:P\upharpoonright \kappa=Q\upharpoonright \kappa.\supset.P_{\Delta}ʻ\kappa=Q_{\Delta}ʻ\kappa\) -/
theorem pm80_22 {P Q : α → β → Prop} {K : Set β} : P ↾ K = Q ↾ K → sel P K = sel Q K := by
  intro h
  sel_simp
  grind

/-- ✱80·23. \(\vdash.P_{\Delta}ʻ\kappa=(P\upharpoonright \kappa)_{\Delta}ʻ\kappa\) -/
theorem pm80_23 {P : α → β → Prop} {K : Set β} : sel P K = sel (P ↾ K) K := by
  sel_simp
  grind

/-- ✱80·24. \(\vdash:\kappa\subset \text{ᗡ}ʻP.Q=P\upharpoonright \kappa.\supset.P_{\Delta}ʻ\kappa=Q_{\Delta}ʻ\text{ᗡ}ʻQ \quad[\text{*35·65.*80·23}]\) -/
theorem pm80_24 {P Q : α → β → Prop} {K : Set β} :
    K ⊆ codom P ∧ Q = P ↾ K → sel P K = sel Q (codom Q) := by
  rintro ⟨h, rfl⟩
  sel_simp
  grind

/-- ✱80·25. \(\vdash:\exists !P_{\Delta}ʻ\kappa.Q=P\upharpoonright \kappa.\supset.P_{\Delta}ʻ\kappa=Q_{\Delta}ʻ\text{ᗡ}ʻQ \quad[\text{*80·2·24}]\) -/
theorem pm80_25 {P Q : α → β → Prop} {K : Set β} :
    (sel P K).Nonempty ∧ Q = P ↾ K → sel P K = sel Q (codom Q) :=
  fun ⟨h, e⟩ => pm80_24 ⟨pm80_2 h, e⟩

/-- ✱80·26. \(\vdash.P_{\Delta}ʻ\Lambda=\iotaʻ\dot{\Lambda}\) -/
theorem pm80_26 {P : α → β → Prop} : sel P (Λ : Set β) = ι (rNull : α → β → Prop) := by
  sel_simp
  grind

/-- ✱80·27. \(\vdash:\exists !\kappa.\supset.\dot{\Lambda}_{\Delta}ʻ\kappa=\Lambda\) -/
theorem pm80_27 {K : Set β} : K.Nonempty → sel (rNull : α → β → Prop) K = Λ := by
  intro h
  sel_simp
  grind

/-- ✱80·28. \(\vdash:\exists !\kappa.\supset.\dot{\Lambda}{\sim}\in P_{\Delta}ʻ\kappa\) -/
theorem pm80_28 {P : α → β → Prop} {K : Set β} : K.Nonempty → rNull ∉ sel P K := by
  intro h
  sel_simp
  grind

/-- ✱80·29. \(\vdash:R\in P_{\Delta}ʻ\kappa.\supset.R=R\upharpoonright \kappa\) -/
theorem pm80_29 {P R : α → β → Prop} {K : Set β} : R ∈ sel P K → R = R ↾ K := by
  intro h
  sel_simp
  grind

/-- ✱80·291. \(\vdash\colon\ldotp R\in P_{\Delta}ʻ\kappa.\supset.R\unicode{x2abd}P\upharpoonright \kappa\) -/
theorem pm80_291 {P R : α → β → Prop} {K : Set β} : R ∈ sel P K → R ⪽ P ↾ K := by
  intro h
  sel_simp
  grind

/-- ✱80·3. \(\vdash:R\in P_{\Delta}ʻ\kappa.y\in \kappa.\supset.\text{E}!Rʻy\) -/
theorem pm80_3 {P R : α → β → Prop} {K : Set β} {y : β} : R ∈ sel P K ∧ y ∈ K → EDesc R y :=
  fun ⟨h, hy⟩ => sel_edesc h hy

/-- ✱80·31. \(\vdash:R\in P_{\Delta}ʻ\kappa.y\in \kappa.\supset.Rʻy\in \overrightarrow{P}ʻy\) -/
theorem pm80_31 {P R : α → β → Prop} {K : Set β} {y : β} :
    R ∈ sel P K ∧ y ∈ K → Desc R y (fun x => x ∈ refs P y) := by
  rintro ⟨h, hy⟩
  obtain ⟨x, hx, hu⟩ := sel_ex h hy
  rw [desc_iff_of hx hu]
  exact (sel_iff.1 h).2.1 x y hx

/-- ✱80·32. \(\vdash\colon\ldotp R\in P_{\Delta}ʻ\kappa.\supset:y\in \kappa.\equiv.\text{E}!Rʻy.\equiv.Rʻy\in \overrightarrow{P}ʻy\) -/
theorem pm80_32 {P R : α → β → Prop} {K : Set β} {y : β} :
    R ∈ sel P K →
      ((y ∈ K ↔ EDesc R y) ∧ (EDesc R y ↔ Desc R y (fun x => x ∈ refs P y))) := by
  intro h
  have hK : y ∈ K ↔ EDesc R y := by
    refine ⟨fun hy => sel_edesc h hy, fun ⟨b, hb⟩ => ?_⟩
    exact (sel_iff.1 h).2.2.1 b y ((hb b).2 rfl)
  refine ⟨hK, fun he => pm80_31 ⟨h, hK.2 he⟩, fun hd => ?_⟩
  exact (desc_iff.1 hd).1

/-- ✱80·33. \(\vdash:R\in P_{\Delta}ʻ\kappa.\supset.\text{D}ʻR\subset Pʻʻ\kappa\) -/
theorem pm80_33 {P R : α → β → Prop} {K : Set β} : R ∈ sel P K → dom R ⊆ P ʻʻ K := by
  intro h
  sel_simp
  grind

/-- ✱80·34. \(\vdash:R\in P_{\Delta}ʻ\kappa.\supset.\text{E}‼Rʻʻ\kappa.Rʻʻ\kappa=\text{D}ʻR\) -/
theorem pm80_34 {P R : α → β → Prop} {K : Set β} : R ∈ sel P K → EE R K ∧ R ʻʻ K = dom R := by
  intro h
  refine ⟨fun y hy => sel_edesc h hy, ?_⟩
  sel_simp
  grind

/-- ✱80·35. \(\vdash:R\in P_{\Delta}ʻ\kappa.\supset.\text{D}ʻR=\hat{x}\{(\exists y).y\in \kappa.x=Rʻy\} \quad[\text{*37·6.*80·34}]\) -/
theorem pm80_35 {P R : α → β → Prop} {K : Set β} :
    R ∈ sel P K → dom R = {x | ∃ y, y ∈ K ∧ Desc R y (fun b => x = b)} := by
  intro h
  ext x
  constructor
  · rintro ⟨y, hxy⟩
    have hy : y ∈ K := (sel_iff.1 h).2.2.1 x y hxy
    exact ⟨y, hy, (desc_iff_of hxy (fun x' hx' => (sel_iff.1 h).1 x' x y hx' hxy)).2 rfl⟩
  · rintro ⟨y, -, hd⟩
    obtain ⟨⟨b, hb⟩, hψ⟩ := desc_iff.1 hd
    exact ⟨y, (hψ b ((hb b).2 rfl)) ▸ (hb b).2 rfl⟩

/-- ✱80·36. \(\vdash:R,\,S\in P_{\Delta}ʻ\kappa.\supset.R\upharpoonright \alpha\unicode{x228d}S\upharpoonright -\alpha\in P_{\Delta}ʻ\kappa\) -/
theorem pm80_36 {P R S : α → β → Prop} {K A : Set β} :
    R ∈ sel P K ∧ S ∈ sel P K → (R ↾ A) ⊍ (S ↾ Aᶜ) ∈ sel P K := by
  intro h
  sel_simp
  grind

/-- ✱80·4. \(\vdash:R\in P_{\Delta}ʻ\kappa.y\in \kappa.xRy.x'Py.\supset.\{(R\dot{-}x\downarrow y)\unicode{x228d}x'\downarrow y\}\in P_{\Delta}ʻ\kappa\) -/
theorem pm80_4 {P R : α → β → Prop} {K : Set β} {x x' : α} {y : β} :
    ((R ∈ sel P K ∧ y ∈ K) ∧ R x y) ∧ P x' y → (R ∸ x ↓ y) ⊍ x' ↓ y ∈ sel P K := by
  intro h
  sel_simp
  grind

/-- ✱80·41. \(\vdash:R\in P_{\Delta}ʻ\kappa.y\in \kappa.x'Py.\supset.[\{R\dot{-}(Rʻy)\downarrow y\}\unicode{x228d}x'\downarrow y]\in P_{\Delta}ʻ\kappa\) -/
theorem pm80_41 {P R : α → β → Prop} {K : Set β} {x' : α} {y : β} :
    (R ∈ sel P K ∧ y ∈ K) ∧ P x' y →
      Desc R y (fun x => (R ∸ x ↓ y) ⊍ x' ↓ y ∈ sel P K) := by
  rintro ⟨⟨h, hy⟩, hP⟩
  obtain ⟨x, hx, hu⟩ := sel_ex h hy
  rw [desc_iff_of hx hu]
  exact pm80_4 ⟨⟨⟨h, hy⟩, hx⟩, hP⟩

/-- ✱80·42. \(\vdash:\exists !P_{\Delta}ʻ\kappa.\supset.\dot{s}ʻP_{\Delta}ʻ\kappa=P\upharpoonright \kappa\) -/
theorem pm80_42 {P : α → β → Prop} {K : Set β} :
    (sel P K).Nonempty → sumRel (sel P K) = P ↾ K := by
  rintro ⟨M, hM⟩
  funext x y
  apply propext
  constructor
  · rintro ⟨N, hN, hxy⟩
    have := sel_iff.1 hN
    exact ⟨this.2.1 x y hxy, this.2.2.1 x y hxy⟩
  · rintro ⟨hxy, hy⟩
    obtain ⟨b, hb, -⟩ := sel_ex hM hy
    exact ⟨_, pm80_4 ⟨⟨⟨hM, hy⟩, hb⟩, hxy⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- ✱80·43. \(\vdash:xPy.\equiv.x\downarrow y\in P_{\Delta}ʻ\iotaʻy\) -/
theorem pm80_43 {P : α → β → Prop} {x : α} {y : β} : P x y ↔ x ↓ y ∈ sel P (ι y) := by
  constructor
  · intro h
    sel_simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · grind
    · grind
    · grind
    · intro z hz; exact ⟨x, rfl, hz⟩
  · intro h
    sel_simp
    grind

/-- ✱80·44. \(\vdash:R\in P_{\Delta}ʻ\iotaʻy.\supset.R=(Rʻy)\downarrow y\) -/
theorem pm80_44 {P R : α → β → Prop} {y : β} :
    R ∈ sel P (ι y) → Desc R y (fun x => R = x ↓ y) := by
  intro h
  obtain ⟨x, hx, hu⟩ := sel_ex h (rfl : y ∈ ι y)
  rw [desc_iff_of hx hu]
  have := sel_iff.1 h
  funext a b
  apply propext
  constructor
  · intro hab
    have hb : b = y := this.2.2.1 a b hab
    subst hb
    exact ⟨hu a hab, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact hx

/-- ✱80·45. \(\vdash.P_{\Delta}ʻ\iotaʻy=\downarrow yʻʻ\overrightarrow{P}ʻy\) -/
theorem pm80_45 {P : α → β → Prop} {y : β} : sel P (ι y) = coupleR y ʻʻ refs P y := by
  ext M
  constructor
  · intro h
    obtain ⟨x, hx, hu⟩ := sel_ex h (rfl : y ∈ ι y)
    have hM := (desc_iff_of hx hu).1 (pm80_44 h)
    exact ⟨x, (sel_iff.1 h).2.1 x y hx, hM⟩
  · rintro ⟨x, hx, hM⟩
    rw [coupleR_apply] at hM
    subst hM
    exact pm80_43.1 hx

/-- ✱80·46. \(\vdash:\exists !P_{\Delta}ʻ\iotaʻy.\equiv.\exists !\overrightarrow{P}ʻy.\equiv.y\in \text{ᗡ}ʻP \quad[\text{*80·45.*37·45.*33·41}]\) -/
theorem pm80_46 {P : α → β → Prop} {y : β} :
    ((sel P (ι y)).Nonempty ↔ (refs P y).Nonempty) ∧ ((refs P y).Nonempty ↔ y ∈ codom P) := by
  refine ⟨?_, ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx⟩⟩⟩
  rw [pm80_45]
  constructor
  · rintro ⟨M, x, hx, -⟩; exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩; exact ⟨_, x, hx, rfl⟩

/-- ✱80·5. \(\vdash:\kappa\cap \lambda=\Lambda.R\in P_{\Delta}ʻ\kappa.S\in Q_{\Delta}ʻ\lambda.\supset.R\unicode{x228d}S\in (P\unicode{x228d}Q)_{\Delta}ʻ(\kappa\cup \lambda)\) -/
theorem pm80_5 {P Q R S : α → β → Prop} {K L : Set β} :
    (K ∩ L = Λ ∧ R ∈ sel P K) ∧ S ∈ sel Q L → R ⊍ S ∈ sel (P ⊍ Q) (K ∪ L) := by
  intro h
  sel_simp
  grind

/-- ✱80·51. \(\vdash:\lambda\cap \text{ᗡ}ʻP=\Lambda.R\in P_{\Delta}ʻ\kappa.S\in Q_{\Delta}ʻ\lambda.\supset.R\unicode{x228d}S\in (P\unicode{x228d}Q)_{\Delta}ʻ(\kappa\cup \lambda)\) -/
theorem pm80_51 {P Q R S : α → β → Prop} {K L : Set β} :
    (L ∩ codom P = Λ ∧ R ∈ sel P K) ∧ S ∈ sel Q L → R ⊍ S ∈ sel (P ⊍ Q) (K ∪ L) := by
  intro h
  sel_simp
  grind

/-- ✱80·511. \[\begin{align}\vdash:\kappa\cap \text{ᗡ}ʻQ=\Lambda.\lambda\cap \text{ᗡ}ʻP=\Lambda.M\in &(P\unicode{x228d}Q)_{\Delta}ʻ(\kappa\cup \lambda).\supset.\\ & M\upharpoonright \kappa=M\dot{\cap}P.M\upharpoonright \lambda=M\dot{\cap}Q\end{align}\] -/
theorem pm80_511 {P Q M : α → β → Prop} {K L : Set β} :
    (K ∩ codom Q = Λ ∧ L ∩ codom P = Λ) ∧ M ∈ sel (P ⊍ Q) (K ∪ L) →
      M ↾ K = M ⩀ P ∧ M ↾ L = M ⩀ Q := by
  intro h
  sel_simp
  grind

/-- ✱80·52. \[\begin{align}\vdash:\kappa\cap \text{ᗡ}ʻQ=\Lambda.\lambda\cap \text{ᗡ}ʻP=\Lambda.M\in (P\unicode{x228d}Q)_{\Delta}ʻ&(\kappa\cup \lambda).\supset.\\ & M\upharpoonright \kappa\in P_{\Delta}ʻ\kappa.M\upharpoonright \lambda\in Q_{\Delta}ʻ\lambda\end{align}\] -/
theorem pm80_52 {P Q M : α → β → Prop} {K L : Set β} :
    (K ∩ codom Q = Λ ∧ L ∩ codom P = Λ) ∧ M ∈ sel (P ⊍ Q) (K ∪ L) →
      M ↾ K ∈ sel P K ∧ M ↾ L ∈ sel Q L := by
  intro h
  sel_simp
  grind

/-- ✱80·53. \[\begin{align}\vdash\colon\ldotp \kappa &\cap \text{ᗡ}ʻQ=\Lambda.\lambda\cap \text{ᗡ}ʻP=\Lambda.\supset:\\ & M\in (P\unicode{x228d}Q)_{\Delta}ʻ(\kappa\cup \lambda).\equiv.(\exists R,S).R\in P_{\Delta}ʻ\kappa.S\in Q_{\Delta}ʻ\lambda.M=R\unicode{x228d}S\end{align}\] -/
theorem pm80_53 {P Q M : α → β → Prop} {K L : Set β} :
    K ∩ codom Q = Λ ∧ L ∩ codom P = Λ →
      (M ∈ sel (P ⊍ Q) (K ∪ L) ↔ ∃ R S, (R ∈ sel P K ∧ S ∈ sel Q L) ∧ M = R ⊍ S) := by
  intro h
  constructor
  · intro hM
    refine ⟨M ↾ K, M ↾ L, pm80_52 ⟨h, hM⟩, ?_⟩
    sel_simp
    grind
  · rintro ⟨R, S, hRS, rfl⟩
    sel_simp
    grind

/-- ✱80·54. \[\begin{align}&\vdash\colon\ldotp \kappa\cap \text{ᗡ}ʻQ=\Lambda.\lambda\cap \text{ᗡ}ʻP=\Lambda.\supset:\\ & R\in P_{\Delta}ʻ\kappa.S\in Q_{\Delta}ʻ\lambda.\equiv.(\exists M).M\in (P\unicode{x228d}Q)_{\Delta}ʻ(\kappa\cup \lambda).R=M\upharpoonright \kappa.S=M\upharpoonright \lambda\end{align}\] -/
theorem pm80_54 {P Q R S : α → β → Prop} {K L : Set β} :
    K ∩ codom Q = Λ ∧ L ∩ codom P = Λ →
      (R ∈ sel P K ∧ S ∈ sel Q L ↔
        ∃ M, (M ∈ sel (P ⊍ Q) (K ∪ L) ∧ R = M ↾ K) ∧ S = M ↾ L) := by
  intro h
  constructor
  · intro hRS
    refine ⟨R ⊍ S, ⟨(pm80_53 h).2 ⟨R, S, hRS, rfl⟩, ?_⟩, ?_⟩
    · sel_simp
      grind
    · sel_simp
      grind
  · rintro ⟨M, ⟨hM, rfl⟩, rfl⟩
    exact pm80_52 ⟨h, hM⟩

/-- ✱80·6. \(\vdash:R\in P_{\Delta}ʻ\kappa.\lambda\subset \kappa.\supset.R\upharpoonright \lambda\in P_{\Delta}ʻ\lambda\) -/
theorem pm80_6 {P R : α → β → Prop} {K L : Set β} : R ∈ sel P K ∧ L ⊆ K → R ↾ L ∈ sel P L := by
  intro h
  sel_simp
  grind

/-- ✱80·61. \(\vdash:M\upharpoonright \kappa\in P_{\Delta}ʻ\kappa.M\upharpoonright \lambda\in P_{\Delta}ʻ\lambda.\supset.M\upharpoonright (\kappa\cup \lambda)\in P_{\Delta}ʻ(\kappa\cup \lambda)\) -/
theorem pm80_61 {P M : α → β → Prop} {K L : Set β} :
    M ↾ K ∈ sel P K ∧ M ↾ L ∈ sel P L → M ↾ (K ∪ L) ∈ sel P (K ∪ L) := by
  intro h
  sel_simp
  grind

/-- ✱80·62. \(\vdash:M\in P_{\Delta}ʻ(\kappa\cup \lambda).\supset.M\upharpoonright \kappa\in P_{\Delta}ʻ\kappa.M\upharpoonright \lambda\in P_{\Delta}ʻ\lambda \quad[\text{*80·6.*22·58}]\) -/
theorem pm80_62 {P M : α → β → Prop} {K L : Set β} :
    M ∈ sel P (K ∪ L) → M ↾ K ∈ sel P K ∧ M ↾ L ∈ sel P L := by
  intro h
  sel_simp
  grind

/-- ✱80·621. \(\vdash:M\upharpoonright (\kappa\cup \lambda)\in P_{\Delta}ʻ(\kappa\cup \lambda).\supset.M\upharpoonright \kappa\in P_{\Delta}ʻ\kappa.M\upharpoonright \lambda\in P_{\Delta}ʻ\lambda\) -/
theorem pm80_621 {P M : α → β → Prop} {K L : Set β} :
    M ↾ (K ∪ L) ∈ sel P (K ∪ L) → M ↾ K ∈ sel P K ∧ M ↾ L ∈ sel P L := by
  intro h
  sel_simp
  grind

/-- ✱80·63. \(\vdash:M\upharpoonright \kappa\in P_{\Delta}ʻ\kappa.M\upharpoonright \lambda\in P_{\Delta}ʻ\lambda.\equiv.M\upharpoonright (\kappa\cup \lambda)\in P_{\Delta}ʻ(\kappa\cup \lambda) \quad[\text{*80·61·621}]\) -/
theorem pm80_63 {P M : α → β → Prop} {K L : Set β} :
    M ↾ K ∈ sel P K ∧ M ↾ L ∈ sel P L ↔ M ↾ (K ∪ L) ∈ sel P (K ∪ L) :=
  ⟨pm80_61, pm80_621⟩

/-- ✱80·64. \(\vdash\colon\ldotp \text{ᗡ}ʻM=\kappa\cup \lambda.\supset:M\upharpoonright \kappa\in P_{\Delta}ʻ\kappa.M\upharpoonright \lambda\in P_{\Delta}ʻ\lambda.\equiv.M\in P_{\Delta}ʻ(\kappa\cup \lambda)\) -/
theorem pm80_64 {P M : α → β → Prop} {K L : Set β} :
    codom M = K ∪ L → (M ↾ K ∈ sel P K ∧ M ↾ L ∈ sel P L ↔ M ∈ sel P (K ∪ L)) := by
  intro h
  sel_simp
  grind

/-- ✱80·65. \[\begin{align}&\vdash:\kappa\cap \lambda=\Lambda.R\in P_{\Delta}ʻ\kappa.S\in P_{\Delta}ʻ\lambda.\supset.R\unicode{x228d}S\in P_{\Delta}ʻ(\kappa\cup \lambda)\\ &\left[\text{*80·5} \frac{P}{Q}.\text{*23·56}\right]\end{align}\] -/
theorem pm80_65 {P R S : α → β → Prop} {K L : Set β} :
    (K ∩ L = Λ ∧ R ∈ sel P K) ∧ S ∈ sel P L → R ⊍ S ∈ sel P (K ∪ L) := by
  intro h
  sel_simp
  grind

/-- ✱80·651. \(\vdash:R\in P_{\Delta}ʻ\kappa.S\in P_{\Delta}ʻ\lambda.\supset.R\unicode{x228d}S\upharpoonright (\lambda-\kappa)\in P_{\Delta}ʻ(\kappa\cup \lambda)\) -/
theorem pm80_651 {P R S : α → β → Prop} {K L : Set β} :
    R ∈ sel P K ∧ S ∈ sel P L → R ⊍ S ↾ (L \ K) ∈ sel P (K ∪ L) := by
  intro h
  sel_simp
  grind

/-- ✱80·66. \[\begin{align}\vdash\colon\ldotp \kappa\cap &\lambda=\Lambda.\supset:\\ & M\in P_{\Delta}ʻ(\kappa\cup \lambda).\equiv.(\exists R,S).R\in P_{\Delta}ʻ\kappa.S\in P_{\Delta}ʻ\lambda.M=R\unicode{x228d}S\end{align}\] -/
theorem pm80_66 {P M : α → β → Prop} {K L : Set β} :
    K ∩ L = Λ →
      (M ∈ sel P (K ∪ L) ↔ ∃ R S, (R ∈ sel P K ∧ S ∈ sel P L) ∧ M = R ⊍ S) := by
  intro h
  constructor
  · intro hM
    refine ⟨M ↾ K, M ↾ L, pm80_62 hM, ?_⟩
    sel_simp
    grind
  · rintro ⟨R, S, hRS, rfl⟩
    exact pm80_65 ⟨⟨h, hRS.1⟩, hRS.2⟩

/-- ✱80·661. \(\vdash:\kappa\cap \lambda=\Lambda.R\in P_{\Delta}ʻ\kappa.S\in P_{\Delta}ʻ\lambda.\supset.R=(R\unicode{x228d}S)\upharpoonright \kappa.S=(R\unicode{x228d}S)\upharpoonright \lambda\) -/
theorem pm80_661 {P R S : α → β → Prop} {K L : Set β} :
    (K ∩ L = Λ ∧ R ∈ sel P K) ∧ S ∈ sel P L → R = (R ⊍ S) ↾ K ∧ S = (R ⊍ S) ↾ L := by
  intro h
  sel_simp
  grind

/-- ✱80·67. \[\begin{align}\vdash\colon\ldotp \kappa\cap \lambda=\Lambda.\supset:R\in P_{\Delta}ʻ&\kappa.S\in P_{\Delta}ʻ\lambda.\equiv.\\ &(\exists M).M\in P_{\Delta}ʻ(\kappa\cup \lambda).R=M\upharpoonright \kappa.S=M\upharpoonright \lambda\end{align}\] -/
theorem pm80_67 {P R S : α → β → Prop} {K L : Set β} :
    K ∩ L = Λ →
      (R ∈ sel P K ∧ S ∈ sel P L ↔ ∃ M, (M ∈ sel P (K ∪ L) ∧ R = M ↾ K) ∧ S = M ↾ L) := by
  intro h
  constructor
  · intro hRS
    have := pm80_661 ⟨⟨h, hRS.1⟩, hRS.2⟩
    exact ⟨R ⊍ S, ⟨pm80_65 ⟨⟨h, hRS.1⟩, hRS.2⟩, this.1⟩, this.2⟩
  · rintro ⟨M, ⟨hM, rfl⟩, rfl⟩
    exact pm80_62 hM

/-- ✱80·68. \(\vdash:R\in P_{\Delta}ʻ(\kappa-\iotaʻy).y\in \kappa.xPy.\supset.R\unicode{x228d}x\downarrow y\in P_{\Delta}ʻ\kappa\) -/
theorem pm80_68 {P R : α → β → Prop} {K : Set β} {x : α} {y : β} :
    (R ∈ sel P (K \ ι y) ∧ y ∈ K) ∧ P x y → R ⊍ x ↓ y ∈ sel P K := by
  intro h
  sel_simp
  grind

/-- ✱80·69. \(\vdash:\exists !P_{\Delta}ʻ(\kappa\cup \lambda).\equiv.\exists !P_{\Delta}ʻ\kappa.\exists !P_{\Delta}ʻ\lambda\) -/
theorem pm80_69 {P : α → β → Prop} {K L : Set β} :
    (sel P (K ∪ L)).Nonempty ↔ (sel P K).Nonempty ∧ (sel P L).Nonempty := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨⟨_, (pm80_62 hM).1⟩, ⟨_, (pm80_62 hM).2⟩⟩
  · rintro ⟨⟨R, hR⟩, ⟨S, hS⟩⟩
    exact ⟨_, pm80_651 ⟨hR, hS⟩⟩

/-- ✱80·7. \[\begin{align}\vdash:\text{ᗡ}ʻP\cap \text{ᗡ}ʻQ=\Lambda.\kappa\subset \text{ᗡ}ʻP.\lambda\subset \text{ᗡ}ʻQ.&M\in (P\unicode{x228d}Q)_{\Delta}ʻ(\kappa\cup \lambda).\supset.\\ & M\dot{-}Q\in P_{\Delta}ʻ\kappa.M\dot{-}P\in Q_{\Delta}ʻ\lambda\end{align}\] -/
theorem pm80_7 {P Q M : α → β → Prop} {K L : Set β} :
    ((codom P ∩ codom Q = Λ ∧ K ⊆ codom P) ∧ L ⊆ codom Q) ∧ M ∈ sel (P ⊍ Q) (K ∪ L) →
      M ∸ Q ∈ sel P K ∧ M ∸ P ∈ sel Q L := by
  intro h
  sel_simp
  grind

/-- ✱80·71. \(\vdash:\text{ᗡ}ʻP\cap \text{ᗡ}ʻQ=\Lambda.M\dot{-}Q\in P_{\Delta}ʻ\kappa.M\dot{-}P\in Q_{\Delta}ʻ\lambda.\supset.M\in (P\unicode{x228d}Q)_{\Delta}ʻ(\kappa\cup \lambda)\) -/
theorem pm80_71 {P Q M : α → β → Prop} {K L : Set β} :
    (codom P ∩ codom Q = Λ ∧ M ∸ Q ∈ sel P K) ∧ M ∸ P ∈ sel Q L →
      M ∈ sel (P ⊍ Q) (K ∪ L) := by
  intro h
  sel_simp
  obtain ⟨⟨hd, a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := h
  refine ⟨fun x y z hx hy => ?_, fun x y hxy => ?_, fun x y hxy => ?_, fun y hy => ?_⟩
  · by_cases hq : Q x z <;> by_cases hq' : Q y z <;> grind
  · grind
  · grind
  · grind

/-- ✱80·72. \[\begin{align}\vdash\colon\ldotp &\text{ᗡ}ʻP\cap \text{ᗡ}ʻQ=\Lambda.\kappa\subset \text{ᗡ}ʻP.\lambda\subset \text{ᗡ}ʻQ.\supset:\\ & M\in (P\unicode{x228d}Q)_{\Delta}ʻ(\kappa\cup \lambda).\equiv.M\dot{-}Q\in P_{\Delta}ʻ\kappa.M\dot{-}P\in Q_{\Delta}ʻ\lambda \quad[\text{*80·7·71}]\end{align}\] -/
theorem pm80_72 {P Q M : α → β → Prop} {K L : Set β} :
    (codom P ∩ codom Q = Λ ∧ K ⊆ codom P) ∧ L ⊆ codom Q →
      (M ∈ sel (P ⊍ Q) (K ∪ L) ↔ M ∸ Q ∈ sel P K ∧ M ∸ P ∈ sel Q L) := by
  intro h
  exact ⟨fun hM => pm80_7 ⟨h, hM⟩, fun hM => pm80_71 ⟨⟨h.1.1, hM.1⟩, hM.2⟩⟩

/-- ✱80·73. \(\vdash:Q=P\upharpoonright \kappa.R=P\upharpoonright \lambda.\supset.P_{\Delta}ʻ(\kappa\cup \lambda)=(Q\unicode{x228d}R)_{\Delta}ʻ(\kappa\cup \lambda)\) -/
theorem pm80_73 {P Q R : α → β → Prop} {K L : Set β} :
    Q = P ↾ K ∧ R = P ↾ L → sel P (K ∪ L) = sel (Q ⊍ R) (K ∪ L) := by
  rintro ⟨rfl, rfl⟩
  sel_simp
  grind

/-- ✱80·731. \(\vdash:Q=P\upharpoonright \kappa.R=P\upharpoonright \lambda.\kappa\cup \lambda\subset \text{ᗡ}ʻP.\supset.\kappa=\text{ᗡ}ʻQ.\lambda=\text{ᗡ}ʻR\) -/
theorem pm80_731 {P Q R : α → β → Prop} {K L : Set β} :
    (Q = P ↾ K ∧ R = P ↾ L) ∧ K ∪ L ⊆ codom P → K = codom Q ∧ L = codom R := by
  rintro ⟨⟨rfl, rfl⟩, h⟩
  sel_simp
  grind

/-- ✱80·732. \(\vdash:Q=P\upharpoonright \kappa.R=P\upharpoonright \lambda.\kappa\cap \lambda=\Lambda.\supset.\text{ᗡ}ʻQ\cap \text{ᗡ}ʻR=\Lambda\) -/
theorem pm80_732 {P Q R : α → β → Prop} {K L : Set β} :
    (Q = P ↾ K ∧ R = P ↾ L) ∧ K ∩ L = Λ → codom Q ∩ codom R = Λ := by
  rintro ⟨⟨rfl, rfl⟩, h⟩
  sel_simp
  grind

/-- ✱80·74. \[\begin{align}\vdash:\kappa\cap \lambda=\Lambda.&M\in P_{\Delta}ʻ(\kappa\cup \lambda).\supset.\\ & M\upharpoonright \kappa=M\upharpoonright -\lambda=M\dot{-}P\upharpoonright \lambda.M\upharpoonright \lambda=M\upharpoonright -\kappa=M\dot{-}P\upharpoonright \kappa\end{align}\] -/
theorem pm80_74 {P M : α → β → Prop} {K L : Set β} :
    K ∩ L = Λ ∧ M ∈ sel P (K ∪ L) →
      (M ↾ K = M ↾ Lᶜ ∧ M ↾ Lᶜ = M ∸ P ↾ L) ∧ (M ↾ L = M ↾ Kᶜ ∧ M ↾ Kᶜ = M ∸ P ↾ K) := by
  intro h
  sel_simp
  grind

/-- ✱80·75. \[\begin{align}&\vdash:\kappa\cap \lambda=\Lambda.M\in P_{\Delta}ʻ(\kappa\cup \lambda).\supset.M\dot{-}P\upharpoonright \lambda\in P_{\Delta}ʻ\kappa.M\dot{-}P\upharpoonright \kappa\in P_{\Delta}ʻ\lambda\\ &[\text{*80·62·74}]\end{align}\] -/
theorem pm80_75 {P M : α → β → Prop} {K L : Set β} :
    K ∩ L = Λ ∧ M ∈ sel P (K ∪ L) → M ∸ P ↾ L ∈ sel P K ∧ M ∸ P ↾ K ∈ sel P L := by
  intro h
  sel_simp
  grind

/-- ✱80·76. \(\vdash:M\in P_{\Delta}ʻ\mu.R\in P_{\Delta}ʻ\kappa.R\unicode{x2abd}M.\supset.M\dot{-}R\in P_{\Delta}ʻ(\mu-\kappa)\) -/
theorem pm80_76 {P M R : α → β → Prop} {K μ : Set β} :
    (M ∈ sel P μ ∧ R ∈ sel P K) ∧ R ⪽ M → M ∸ R ∈ sel P (μ \ K) := by
  intro h
  sel_simp
  grind

/-- ✱80·761. \(\vdash:\kappa\cap \lambda=\Lambda.M\in P_{\Delta}ʻ(\kappa\cup \lambda).R\in P_{\Delta}ʻ\kappa.R\unicode{x2abd}M.\supset.M\dot{-}R\in P_{\Delta}ʻ\lambda\) -/
theorem pm80_761 {P M R : α → β → Prop} {K L : Set β} :
    ((K ∩ L = Λ ∧ M ∈ sel P (K ∪ L)) ∧ R ∈ sel P K) ∧ R ⪽ M → M ∸ R ∈ sel P L := by
  intro h
  sel_simp
  grind

/-- ✱80·77. \(\vdash:M\in P_{\Delta}ʻ\mu.M\dot{-}R\in P_{\Delta}ʻ(\mu-\kappa).R\unicode{x2abd}M.\kappa\subset \mu.\supset.R\in P_{\Delta}ʻ\kappa\) -/
theorem pm80_77 {P M R : α → β → Prop} {K μ : Set β} :
    ((M ∈ sel P μ ∧ M ∸ R ∈ sel P (μ \ K)) ∧ R ⪽ M) ∧ K ⊆ μ → R ∈ sel P K := by
  intro h
  sel_simp
  grind

/-- ✱80·771. \(\vdash:\kappa\cap \lambda=\Lambda.M\in P_{\Delta}ʻ(\kappa\cup \lambda).M\dot{-}R\in P_{\Delta}ʻ\lambda.R\unicode{x2abd}M.\supset.R\in P_{\Delta}ʻ\kappa\) -/
theorem pm80_771 {P M R : α → β → Prop} {K L : Set β} :
    ((K ∩ L = Λ ∧ M ∈ sel P (K ∪ L)) ∧ M ∸ R ∈ sel P L) ∧ R ⪽ M → R ∈ sel P K := by
  intro h
  sel_simp
  grind

/-- ✱80·78. \(\vdash:M\in P_{\Delta}ʻ\mu.xMy.\supset.M\dot{-}x\downarrow y\in P_{\Delta}ʻ(\mu-\iotaʻy)\) -/
theorem pm80_78 {P M : α → β → Prop} {μ : Set β} {x : α} {y : β} :
    M ∈ sel P μ ∧ M x y → M ∸ x ↓ y ∈ sel P (μ \ ι y) := by
  intro h
  sel_simp
  grind

/-- ✱80·8. \(\vdash:\exists !P_{\Delta}ʻ\kappa.\supset.\text{ᗡ}ʻ\dot{s}ʻP_{\Delta}ʻ\kappa=\kappa\) -/
theorem pm80_8 {P : α → β → Prop} {K : Set β} :
    (sel P K).Nonempty → codom (sumRel (sel P K)) = K := by
  intro h
  rw [pm80_42 h]
  have := pm80_2 h
  sel_simp
  grind

/-- ✱80·81. \(\vdash:\exists !P_{\Delta}ʻ\alpha.P_{\Delta}ʻ\alpha=P_{\Delta}ʻ\beta.\supset.\alpha=\beta\) -/
theorem pm80_81 {P : α → β → Prop} {A B : Set β} :
    (sel P A).Nonempty ∧ sel P A = sel P B → A = B := by
  rintro ⟨⟨M, hM⟩, h⟩
  have hM' : M ∈ sel P B := h ▸ hM
  ext y
  rw [sel_codom_iff hM, sel_codom_iff hM']

/-- ✱80·82. \(\vdash:\alpha \neq\beta.\supset.P_{\Delta}ʻ\alpha\cap P_{\Delta}ʻ\beta=\Lambda\) -/
theorem pm80_82 {P : α → β → Prop} {A B : Set β} : A ≠ B → sel P A ∩ sel P B = Λ := by
  intro h
  ext M
  rw [Null_eq_empty]
  refine ⟨fun ⟨hA, hB⟩ => h ?_, fun h => h.elim⟩
  ext y
  rw [sel_codom_iff hA, sel_codom_iff hB]

/-- ✱80·83. \(\vdash.(-\iotaʻ\Lambda)\upharpoonleft P_{\Delta}\in 1\rightarrow 1\) -/
theorem pm80_83 {P : α → β → Prop} :
    (ι (Λ : Set (α → β → Prop)))ᶜ ◁ selRel P ∈ arrow one one := by
  rw [mem_arrow_one_one]
  constructor
  · rintro L L' K ⟨⟨-, h⟩, ⟨-, h'⟩⟩
    exact h.trans h'.symm
  · rintro L K K' ⟨⟨hL, h⟩, ⟨-, h'⟩⟩
    have hne : (sel P K).Nonempty := by
      rw [← h]
      by_contra hc
      exact hL (Set.not_nonempty_iff_eq_empty.1 hc ▸ Null_eq_empty.symm)
    exact pm80_81 ⟨hne, h.symm.trans h'⟩

/-- ✱80·84. \(\vdash:\Lambda{\sim}\in P_{\Delta}ʻʻ\kappa.\supset.P_{\Delta}ʻʻ\kappa\text{ sm }\kappa\) -/
theorem pm80_84 {P : α → β → Prop} {K : Set (Set β)} :
    Λ ∉ selRel P ʻʻ K → sm (selRel P ʻʻ K) K := by
  intro h
  rw [sm_iff]
  refine ⟨fun L A => A ∈ K ∧ L = sel P A, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_arrow_one_one]
    constructor
    · rintro L L' A ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
    · rintro L A B ⟨⟨hA, rfl⟩, ⟨-, hB⟩⟩
      have hne : (sel P A).Nonempty := by
        by_contra hc
        exact h ⟨A, hA, (Set.not_nonempty_iff_eq_empty.1 hc).trans Null_eq_empty.symm |>.symm⟩
      exact pm80_81 ⟨hne, hB⟩
  · ext L
    exact ⟨fun ⟨A, hA, hL⟩ => ⟨A, hA, hL⟩, fun ⟨A, hA, hL⟩ => ⟨A, hA, hL⟩⟩
  · ext A
    exact ⟨fun hA => ⟨sel P A, hA, rfl⟩, fun ⟨_, hA, _⟩ => hA⟩

/-- ✱80·9. \(\vdash\colon\ldotp y \neq z.\supset:M\in P_{\Delta}ʻ(\iotaʻy\cup \iotaʻz).\equiv.(\exists u,v).uPy.vPz.M=u\downarrow y\unicode{x228d}v\downarrow z\) -/
theorem pm80_9 {P M : α → β → Prop} {y z : β} :
    y ≠ z →
      (M ∈ sel P (ι y ∪ ι z) ↔ ∃ u v, (P u y ∧ P v z) ∧ M = u ↓ y ⊍ v ↓ z) := by
  intro hyz
  constructor
  · intro h
    obtain ⟨u, hu, hu'⟩ := sel_ex h (Or.inl rfl : y ∈ ι y ∪ ι z)
    obtain ⟨v, hv, hv'⟩ := sel_ex h (Or.inr rfl : z ∈ ι y ∪ ι z)
    refine ⟨u, v, ?_, ?_⟩
    · sel_simp
      grind
    · sel_simp
      grind
  · rintro ⟨u, v, huv, rfl⟩
    sel_simp
    grind

/-- ✱80·91. \(\vdash:M\in P_{\Delta}ʻ(\iotaʻy\cup \iotaʻz).\supset.M=(Mʻy)\downarrow y\unicode{x228d}(Mʻz)\downarrow z\) -/
theorem pm80_91 {P M : α → β → Prop} {y z : β} :
    M ∈ sel P (ι y ∪ ι z) → Desc M y (fun a => Desc M z (fun b => M = a ↓ y ⊍ b ↓ z)) := by
  intro h
  obtain ⟨u, hu, hu'⟩ := sel_ex h (Or.inl rfl : y ∈ ι y ∪ ι z)
  obtain ⟨v, hv, hv'⟩ := sel_ex h (Or.inr rfl : z ∈ ι y ∪ ι z)
  rw [desc_iff_of hu hu', desc_iff_of hv hv']
  sel_simp
  grind

/-- ✱80·92. \(\vdash:y \neq z.\supset.\text{D}ʻʻP_{\Delta}ʻ(\iotaʻy\cup \iotaʻz)=\hat{\xi}\{(\exists u,v).uPy.vPz.\xi=\iotaʻu\cup \iotaʻv\}\) -/
theorem pm80_92 {P : α → β → Prop} {y z : β} :
    y ≠ z → D ʻʻ sel P (ι y ∪ ι z) = {ξ | ∃ u v, (P u y ∧ P v z) ∧ ξ = ι u ∪ ι v} := by
  intro hyz
  ext ξ
  constructor
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨u, v, huv, rfl⟩ := (pm80_9 hyz).1 hM
    refine ⟨u, v, huv, ?_⟩
    sel_simp
    grind
  · rintro ⟨u, v, huv, rfl⟩
    refine ⟨_, (pm80_9 hyz).2 ⟨u, v, huv, rfl⟩, ?_⟩
    show _ = dom _
    sel_simp
    grind

/-- ✱80·93. \(\vdash:\exists !P_{\Delta}ʻ(\iotaʻy\cup \iotaʻz).\equiv.y,z \in \text{ᗡ}ʻP \quad[\text{*80·46·69}]\) -/
theorem pm80_93 {P : α → β → Prop} {y z : β} :
    (sel P (ι y ∪ ι z)).Nonempty ↔ y ∈ codom P ∧ z ∈ codom P := by
  rw [pm80_69, pm80_46.1, pm80_46.2, pm80_46.1, pm80_46.2]

/-- ✱80·94. \(\vdash:\exists !P_{\Delta}ʻ(\beta\cup \iotaʻz).\equiv.\exists !P_{\Delta}ʻ\beta.z\in \text{ᗡ}ʻP \quad[\text{*80·46·69}]\) -/
theorem pm80_94 {P : α → β → Prop} {B : Set β} {z : β} :
    (sel P (B ∪ ι z)).Nonempty ↔ (sel P B).Nonempty ∧ z ∈ codom P := by
  rw [pm80_69, pm80_46.1, pm80_46.2]

/-!
## [✱81] Selections from many-one relations

*(Vol. 1, p. 519)*

> *Summary of* *81.
>
> When \(P\upharpoonright \kappa\) is a many-one relation, \(P_{\Delta}ʻ\kappa\) has many important properties which do not hold in the general case. In the first place, \(P_{\Delta}ʻ\kappa\) consists wholly of one-one relations. In the second place, if \(R \in P_{\Delta}ʻ\kappa\), \(\text{D}ʻR\) takes one term and no more out of each member of \(\overrightarrow{P}ʻʻ\kappa\). Again, if \(R \in P_{\Delta}ʻ\kappa\), \(R\) is determinate when \(\text{D}ʻR\) is given; *i.e.* \(R,\,S \in P_{\Delta}ʻ\kappa.\text{D}ʻR=\text{D}ʻS.\supset.R=S\). It follows that \(\text{D}ʻʻP_{\Delta}ʻ\kappa\) is similar to \(P_{\Delta}ʻ\kappa\); hence the number of members of \(P_{\Delta}ʻ\kappa\) is the number of ways of choosing one member out of each class belonging to \(\overrightarrow{P}ʻʻ\kappa\). It should be remembered that when \(P\upharpoonright \kappa\) is many-one, \(\overrightarrow{P}ʻʻ\kappa\) is a class of mutually exclusive classes, *i.e.* no two different members of \(\overrightarrow{P}ʻʻ\kappa\) have any common member. This follows immediately from *71·181.
>
> …

**Lean reading.** `P ↾ κ ∈ Cls → 1` is `P ↾ K ∈ arrow Cls one` (many-one, `mem_arrow_Cls_one`).
`R̆'x` is `Desc R˘ x ψ`, and `(℩y)(y ∈ κ . xPy)` is a `TheIs`; in the chain of identities of ✱81·12
the description written first has the larger scope in each link. `ι'R'y` is `ι` of the description
`R'y`, whose scope is the identity in which it occurs. `↿(P ↾ κ)` in ✱81·221 is the relation of `α ↿
(P ↾ κ)` to `α` (✱38·02 with `♀ = ↿`), i.e. `opR dres (P ↾ K)`. The class `μ̂{…}` of ✱81·211–·3 is a
set-builder with its conjunction written out. ✱81·23 is read with the erratum of the Additional
Errata.

**Status.** proved (all propositions; ✱81·23 proved (reading): erratum, see its docstring).
-/

/-- `μ ∈ D''λ . ≡ . (∃R) . R ∈ λ . μ = D'R`. -/
theorem mem_D_img {μ : Set α} {X : Set (α → β → Prop)} :
    μ ∈ D ʻʻ X ↔ ∃ R, R ∈ X ∧ μ = dom R := Iff.rfl

/-- The relatum of a member of `D'R` under a selection from a many-one `P ↾ κ` is unique. -/
theorem sel_cnv_unique {P R : α → β → Prop} {K : Set β} (hP : P ↾ K ∈ arrow Cls one)
    (hR : R ∈ sel P K) {x : α} {y y' : β} (hy : R x y) (hy' : P x y') (hK : y' ∈ K) : y' = y := by
  rw [mem_arrow_Cls_one] at hP
  have := sel_iff.1 hR
  exact hP x y' y ⟨⟨hy', hK⟩, ⟨this.2.1 _ _ hy, this.2.2.1 _ _ hy⟩⟩

/-- ✱81·1. \(\vdash:P\upharpoonright \kappa \in \text{Cls}\rightarrow 1.\supset.P_{\Delta}ʻ\kappa\subset 1\rightarrow 1\) -/
theorem pm81_1 {P : α → β → Prop} {K : Set β} :
    P ↾ K ∈ arrow Cls one → sel P K ⊆ arrow one one := by
  intro h M hM
  sel_simp
  grind

/-- ✱81·11. \(\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.R\in P_{\Delta}ʻ\kappa.x\in \text{D}ʻR.\supset.\text{E}!\breve{R}ʻx.x(P\upharpoonright \kappa)\breve{R}ʻx\) -/
theorem pm81_11 {P R : α → β → Prop} {K : Set β} {x : α} :
    (P ↾ K ∈ arrow Cls one ∧ R ∈ sel P K) ∧ x ∈ dom R →
      EDesc R˘ x ∧ Desc R˘ x (fun y => (P ↾ K) x y) := by
  rintro ⟨⟨hP, hR⟩, ⟨y, hy⟩⟩
  have hs := sel_iff.1 hR
  have hu : ∀ y', R˘ y' x → y' = y := fun y' hy' =>
    sel_cnv_unique hP hR hy (hs.2.1 _ _ hy') (hs.2.2.1 _ _ hy')
  refine ⟨⟨y, fun y' => ⟨hu y', fun e => e ▸ hy⟩⟩, (desc_iff_of (R := R˘) hy hu).2 ?_⟩
  exact ⟨hs.2.1 _ _ hy, hs.2.2.1 _ _ hy⟩

/-- ✱81·12. \[\begin{align}\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.R\in P_{\Delta}ʻ\kappa.x\in \text{D}ʻ&R.\supset.\\ &\breve{R}ʻx=(℩y)(y\in \kappa.xPy)=(\kappa\upharpoonleft \breve{P})ʻx\end{align}\] -/
theorem pm81_12 {P R : α → β → Prop} {K : Set β} {x : α} :
    (P ↾ K ∈ arrow Cls one ∧ R ∈ sel P K) ∧ x ∈ dom R →
      Desc R˘ x (fun a => TheIs (fun y => y ∈ K ∧ P x y) (fun b => a = b)) ∧
        TheIs (fun y => y ∈ K ∧ P x y) (fun b => Desc (K ◁ P˘) x (fun c => b = c)) := by
  rintro ⟨⟨hP, hR⟩, ⟨y, hy⟩⟩
  have hs := sel_iff.1 hR
  have hu : ∀ y', R˘ y' x → y' = y := fun y' hy' =>
    sel_cnv_unique hP hR hy (hs.2.1 _ _ hy') (hs.2.2.1 _ _ hy')
  have hyK : y ∈ K ∧ P x y := ⟨hs.2.2.1 _ _ hy, hs.2.1 _ _ hy⟩
  have hu' : ∀ y', y' ∈ K ∧ P x y' → y' = y := fun y' h' => sel_cnv_unique hP hR hy h'.2 h'.1
  have ht : ∀ ψ : β → Prop, TheIs (fun y' => y' ∈ K ∧ P x y') ψ ↔ ψ y :=
    fun ψ => TheIs_iff_of_unique (fun y' => ⟨hu' y', fun e => e ▸ hyK⟩)
  refine ⟨(desc_iff_of (R := R˘) hy hu).2 ((ht _).2 rfl), (ht _).2 ?_⟩
  exact (desc_iff_of (R := K ◁ P˘) hyK hu').2 rfl

/-- ✱81·13. \(\vdash\colon\ldotp P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.R\in P_{\Delta}ʻ\kappa.\supset:xRy.\equiv.x\in \text{D}ʻR.xPy.y\in \kappa\) -/
theorem pm81_13 {P R : α → β → Prop} {K : Set β} {x : α} {y : β} :
    P ↾ K ∈ arrow Cls one ∧ R ∈ sel P K → (R x y ↔ (x ∈ dom R ∧ P x y) ∧ y ∈ K) := by
  rintro ⟨hP, hR⟩
  have hs := sel_iff.1 hR
  constructor
  · intro h
    exact ⟨⟨⟨y, h⟩, hs.2.1 _ _ h⟩, hs.2.2.1 _ _ h⟩
  · rintro ⟨⟨⟨y', hy'⟩, hxy⟩, hy⟩
    rw [sel_cnv_unique hP hR hy' hxy hy]
    exact hy'

/-- ✱81·14. \[\begin{align}&\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.R\in P_{\Delta}ʻ\kappa.\supset.R=(\text{D}ʻR)\upharpoonleft P\upharpoonright \kappa=P\dot{\cap}\text{D}ʻR\uparrow \kappa\\ &[\text{*81·13.*35·102·822}]\end{align}\] -/
theorem pm81_14 {P R : α → β → Prop} {K : Set β} :
    P ↾ K ∈ arrow Cls one ∧ R ∈ sel P K →
      R = dom R ◁ P ↾ K ∧ dom R ◁ P ↾ K = P ⩀ cross (dom R) K := by
  intro h
  constructor
  · funext x y
    apply propext
    rw [pm81_13 h]
    rfl
  · funext x y
    apply propext
    simp only [dres, cres, rcap, cross]
    tauto

/-- ✱81·15. \(\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.R\in P_{\Delta}ʻ\kappa.y\in \kappa.\supset.\iotaʻRʻy=\text{D}ʻR\cap \overrightarrow{P}ʻy\) -/
theorem pm81_15 {P R : α → β → Prop} {K : Set β} {y : β} :
    (P ↾ K ∈ arrow Cls one ∧ R ∈ sel P K) ∧ y ∈ K →
      Desc R y (fun x => ι x = dom R ∩ refs P y) := by
  rintro ⟨⟨hP, hR⟩, hy⟩
  obtain ⟨x, hx, hu⟩ := sel_ex hR hy
  rw [desc_iff_of hx hu]
  have hs := sel_iff.1 hR
  ext z
  constructor
  · rintro rfl
    exact ⟨⟨y, hx⟩, hs.2.1 _ _ hx⟩
  · rintro ⟨⟨y', hy'⟩, hzy⟩
    have : y = y' := sel_cnv_unique hP hR hy' hzy hy
    subst this
    exact hu z hy'

/-- ✱81·2. \(\vdash\colon\ldotp P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.R,\,S\in P_{\Delta}ʻ\kappa.\supset:\text{D}ʻR=\text{D}ʻS.\equiv.R=S\) -/
theorem pm81_2 {P R S : α → β → Prop} {K : Set β} :
    P ↾ K ∈ arrow Cls one ∧ (R ∈ sel P K ∧ S ∈ sel P K) → (dom R = dom S ↔ R = S) := by
  rintro ⟨hP, hR, hS⟩
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [(pm81_14 ⟨hP, hR⟩).1, (pm81_14 ⟨hP, hS⟩).1, h]

/-- ✱81·21. \[\begin{align}&\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.\supset.\text{D}\upharpoonright P_{\Delta}ʻ\kappa\in 1\rightarrow 1.\text{D}ʻʻP_{\Delta}ʻ\kappa\text{ sm }P_{\Delta}ʻ\kappa\\ &[\text{*81·2.*71·59.*73·28}]\end{align}\] -/
theorem pm81_21 {P : α → β → Prop} {K : Set β} :
    P ↾ K ∈ arrow Cls one → D ↾ sel P K ∈ arrow one one ∧ sm (D ʻʻ sel P K) (sel P K) := by
  intro hP
  have h11 : D ↾ sel P K ∈ arrow one one := by
    rw [mem_arrow_one_one]
    constructor
    · rintro A A' R ⟨⟨h, -⟩, ⟨h', -⟩⟩
      exact h.trans h'.symm
    · rintro A R S ⟨⟨h, hR⟩, ⟨h', hS⟩⟩
      exact (pm81_2 ⟨hP, hR, hS⟩).1 (h.symm.trans h')
  refine ⟨h11, sm_iff.2 ⟨D ↾ sel P K, ⟨h11, ?_⟩, ?_⟩⟩
  · ext A
    exact ⟨fun ⟨R, hR, h⟩ => ⟨R, h, hR⟩, fun ⟨R, h, hR⟩ => ⟨R, hR, h⟩⟩
  · ext R
    exact ⟨fun hR => ⟨dom R, rfl, hR⟩, fun ⟨_, _, hR⟩ => hR⟩

/-- ✱81·211. \(\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.\supset.\text{D}ʻʻP_{\Delta}ʻ\kappa\subset \hat{\mu}\{y\in \kappa.\supset_{y}.\mu\cap \overrightarrow{P}ʻy\in 1:\mu\subset Pʻʻ\kappa\}\) -/
theorem pm81_211 {P : α → β → Prop} {K : Set β} :
    P ↾ K ∈ arrow Cls one →
      D ʻʻ sel P K ⊆ {μ | (∀ y, y ∈ K → μ ∩ refs P y ∈ one) ∧ μ ⊆ P ʻʻ K} := by
  rintro hP μ ⟨R, hR, rfl⟩
  have hs := sel_iff.1 hR
  refine ⟨fun y hy => ?_, ?_⟩
  · obtain ⟨x, hx, hu⟩ := sel_ex hR hy
    refine mem_one_iff.2 ⟨x, fun z => ⟨?_, ?_⟩⟩
    · rintro ⟨⟨y', hy'⟩, hzy⟩
      have : y = y' := sel_cnv_unique hP hR hy' hzy hy
      subst this
      exact hu z hy'
    · rintro rfl
      exact ⟨⟨y, hx⟩, hs.2.1 _ _ hx⟩
  · rintro x ⟨y, hy⟩
    exact ⟨y, hs.2.2.1 _ _ hy, hs.2.1 _ _ hy⟩

/-- ✱81·212. \(\vdash\colon\ldotp y\in \kappa.\supset_{y}.\mu\cap \overrightarrow{P}ʻy\in 1:\mu\subset Pʻʻ\kappa:\supset.\mu\in \text{D}ʻʻP_{\Delta}ʻ\kappa.\mu\upharpoonleft P\upharpoonright \kappa\in P_{\Delta}ʻ\kappa\) -/
theorem pm81_212 {P : α → β → Prop} {K : Set β} {μ : Set α} :
    (∀ y, y ∈ K → μ ∩ refs P y ∈ one) ∧ μ ⊆ P ʻʻ K →
      μ ∈ D ʻʻ sel P K ∧ μ ◁ P ↾ K ∈ sel P K := by
  rintro ⟨h1, h2⟩
  have hsel : μ ◁ P ↾ K ∈ sel P K := by
    rw [sel_iff]
    refine ⟨?_, fun x y h => h.1.2, fun x y h => h.2, fun y hy => ?_⟩
    · rintro x x' y ⟨⟨hx, hxy⟩, hy⟩ ⟨⟨hx', hxy'⟩, -⟩
      obtain ⟨b, hb⟩ := mem_one_iff.1 (h1 y hy)
      exact ((hb x).1 ⟨hx, hxy⟩).trans ((hb x').1 ⟨hx', hxy'⟩).symm
    · obtain ⟨b, hb⟩ := mem_one_iff.1 (h1 y hy)
      obtain ⟨hbμ, hbP⟩ := (hb b).2 rfl
      exact ⟨b, ⟨hbμ, hbP⟩, hy⟩
  refine ⟨⟨_, hsel, ?_⟩, hsel⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := h2 hx
    exact ⟨y, ⟨hx, hxy⟩, hy⟩
  · rintro ⟨y, ⟨hx, -⟩, -⟩
    exact hx

/-- ✱81·22. \[\begin{align}&\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.\supset.\text{D}ʻʻP_{\Delta}ʻ\kappa=\hat{\mu}\{y\in \kappa.\supset_{y}.\mu\cap \overrightarrow{P}ʻy\in 1:\mu\subset Pʻʻ\kappa\}\\ &[\text{*81·211·212}]\end{align}\] -/
theorem pm81_22 {P : α → β → Prop} {K : Set β} :
    P ↾ K ∈ arrow Cls one →
      D ʻʻ sel P K = {μ | (∀ y, y ∈ K → μ ∩ refs P y ∈ one) ∧ μ ⊆ P ʻʻ K} :=
  fun hP => Set.Subset.antisymm (pm81_211 hP) (fun _ h => (pm81_212 h).1)

/-- ✱81·221. \(\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.\supset.P_{\Delta}ʻ\kappa=\upharpoonleft (P\upharpoonright \kappa)ʻʻ\text{D}ʻʻP_{\Delta}ʻ\kappa\) -/
theorem pm81_221 {P : α → β → Prop} {K : Set β} :
    P ↾ K ∈ arrow Cls one → sel P K = opR dres (P ↾ K) ʻʻ D ʻʻ sel P K := by
  intro hP
  have key : ∀ R, R ∈ sel P K → R = dom R ◁ (P ↾ K) := by
    intro R hR
    refine (pm81_14 ⟨hP, hR⟩).1.trans ?_
    funext x y
    apply propext
    simp only [dres, cres, and_assoc]
  ext M
  constructor
  · intro hM
    exact ⟨dom M, ⟨M, hM, rfl⟩, key M hM⟩
  · rintro ⟨A, ⟨S, hS, rfl⟩, hM⟩
    have hM' : M = dom S ◁ (P ↾ K) := hM
    rw [hM', ← key S hS]
    exact hS

/-- ✱81·23. \(\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.R\in P_{\Delta}ʻ\kappa.y\in \kappa.\supset.\text{D}ʻR-\overrightarrow{P}ʻy=\text{D}ʻR-\iotaʻ\overrightarrow{R}ʻy\)

**Status.** proved (reading): erratum (Additional Errata to Vol. I, p. 522): for `ι'R⃗'y` read
`ι'R'y`; so the right-hand side is `D'R − ι'R'y`, with the description `R'y` scoped over the
identity. -/
theorem pm81_23 {P R : α → β → Prop} {K : Set β} {y : β} :
    (P ↾ K ∈ arrow Cls one ∧ R ∈ sel P K) ∧ y ∈ K →
      Desc R y (fun x => dom R \ refs P y = dom R \ ι x) := by
  rintro ⟨⟨hP, hR⟩, hy⟩
  obtain ⟨x, hx, hu⟩ := sel_ex hR hy
  rw [desc_iff_of hx hu]
  have h15 := (desc_iff_of hx hu).1 (pm81_15 ⟨⟨hP, hR⟩, hy⟩)
  ext z
  constructor
  · rintro ⟨hz, hz'⟩
    refine ⟨hz, fun e => hz' ?_⟩
    have : z ∈ ι x := e
    rw [h15] at this
    exact this.2
  · rintro ⟨hz, hz'⟩
    refine ⟨hz, fun e => hz' ?_⟩
    have : z ∈ dom R ∩ refs P y := ⟨hz, e⟩
    rw [← h15] at this
    exact this

/-- ✱81·24. \(\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.\mu\in \text{D}ʻʻP_{\Delta}ʻ\kappa.y\in \kappa.\supset.\mu-\overrightarrow{P}ʻy\in \text{D}ʻʻP_{\Delta}ʻ(\kappa-\iotaʻy)\) -/
theorem pm81_24 {P : α → β → Prop} {K : Set β} {μ : Set α} {y : β} :
    (P ↾ K ∈ arrow Cls one ∧ μ ∈ D ʻʻ sel P K) ∧ y ∈ K →
      μ \ refs P y ∈ D ʻʻ sel P (K \ ι y) := by
  rintro ⟨⟨hP, R, hR, rfl⟩, hy⟩
  refine ⟨R ↾ (K \ ι y), pm80_6 ⟨hR, Set.sdiff_subset⟩, ?_⟩
  have hs := sel_iff.1 hR
  ext x
  constructor
  · rintro ⟨⟨y', hy'⟩, hxy⟩
    refine ⟨y', hy', hs.2.2.1 _ _ hy', fun e => hxy ?_⟩
    have e' : y' = y := e
    subst e'
    exact hs.2.1 _ _ hy'
  · rintro ⟨y', hy', -, hne⟩
    refine ⟨⟨y', hy'⟩, fun hxy => hne ?_⟩
    exact (sel_cnv_unique hP hR hy' hxy hy).symm

/-- ✱81·25. \(\vdash: y \in \kappa . xPy. \mu \in \text{D}ʻʻP_{\Delta}ʻ(\kappa-\iotaʻy).\supset.\mu \cup \iotaʻx \in \text{D}ʻʻP_{\Delta}ʻ\kappa\) -/
theorem pm81_25 {P : α → β → Prop} {K : Set β} {μ : Set α} {x : α} {y : β} :
    (y ∈ K ∧ P x y) ∧ μ ∈ D ʻʻ sel P (K \ ι y) → μ ∪ ι x ∈ D ʻʻ sel P K := by
  rintro ⟨⟨hy, hxy⟩, R, hR, rfl⟩
  refine ⟨R ⊍ x ↓ y, pm80_68 ⟨⟨hR, hy⟩, hxy⟩, ?_⟩
  ext z
  simp only [Set.mem_union, mem_unitCls, dom, Set.mem_ofPred_eq, rcup, couple_apply]
  constructor
  · rintro (⟨w, hw⟩ | rfl)
    · exact ⟨w, Or.inl hw⟩
    · exact ⟨y, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨w, hw | ⟨rfl, -⟩⟩
    · exact Or.inl ⟨w, hw⟩
    · exact Or.inr rfl

/-- ✱81·26. \[\begin{align}\vdash\colon\ldotp P\upharpoonright \kappa \in \text{Cls} \rightarrow 1. y \in \kappa .\mu &\cap \overrightarrow{P}ʻy \in 1 . \supset :\\ &\mu - \overrightarrow{P}ʻy \in \text{D}ʻʻP_{\Delta}ʻ(\kappa-\iotaʻy).\equiv.\mu \in \text{D}ʻʻP_{\Delta}ʻ\kappa\end{align}\] -/
theorem pm81_26 {P : α → β → Prop} {K : Set β} {μ : Set α} {y : β} :
    (P ↾ K ∈ arrow Cls one ∧ y ∈ K) ∧ μ ∩ refs P y ∈ one →
      (μ \ refs P y ∈ D ʻʻ sel P (K \ ι y) ↔ μ ∈ D ʻʻ sel P K) := by
  rintro ⟨⟨hP, hy⟩, h1⟩
  refine ⟨fun h => ?_, fun h => pm81_24 ⟨⟨hP, h⟩, hy⟩⟩
  obtain ⟨x, hx⟩ := mem_one_iff.1 h1
  obtain ⟨hxμ, hxP⟩ := (hx x).2 rfl
  have e : μ = (μ \ refs P y) ∪ ι x := by
    ext z
    constructor
    · intro hz
      by_cases hzP : z ∈ refs P y
      · exact Or.inr ((hx z).1 ⟨hz, hzP⟩)
      · exact Or.inl ⟨hz, hzP⟩
    · rintro (⟨hz, -⟩ | rfl)
      · exact hz
      · exact hxμ
  rw [e]
  exact pm81_25 ⟨⟨hy, hxP⟩, h⟩

/-- ✱81·3. \(\vdash: P\upharpoonright \kappa\in \text{Cls}\rightarrow 1. \lambda=\overrightarrow{P}ʻʻ\kappa.\supset.\text{D}ʻʻP_{\Delta}ʻ\kappa=\hat{\mu}\{\alpha\in \lambda.\supset_{\alpha}.\mu\cap \alpha\in 1:\mu\subset sʻ\lambda\}\) -/
theorem pm81_3 {P : α → β → Prop} {K : Set β} {L : Set (Set α)} :
    P ↾ K ∈ arrow Cls one ∧ L = Rfwd P ʻʻ K →
      D ʻʻ sel P K = {μ | (∀ A, A ∈ L → μ ∩ A ∈ one) ∧ μ ⊆ sumCls L} := by
  rintro ⟨hP, rfl⟩
  rw [pm81_22 hP]
  ext μ
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rintro A ⟨y, hy, rfl⟩
      exact h1 y hy
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := h2 hx
      exact ⟨refs P y, ⟨y, hy, rfl⟩, hxy⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy => h1 _ ⟨y, hy, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨A, ⟨y, hy, rfl⟩, hxA⟩ := h2 hx
    exact ⟨y, hy, hxA⟩

/-- ✱81·31. \(\vdash : P\upharpoonright \kappa, Q\upharpoonright \kappa \in \text{Cls} \rightarrow 1. \overrightarrow{P}ʻʻ\kappa = \overrightarrow{Q}ʻʻ\kappa.\supset. \text{D}ʻʻP_{\Delta}ʻ\kappa = \text{D}ʻʻQ_{\Delta}ʻ\kappa\) -/
theorem pm81_31 {P Q : α → β → Prop} {K : Set β} :
    (P ↾ K ∈ arrow Cls one ∧ Q ↾ K ∈ arrow Cls one) ∧ Rfwd P ʻʻ K = Rfwd Q ʻʻ K →
      D ʻʻ sel P K = D ʻʻ sel Q K := by
  rintro ⟨⟨hP, hQ⟩, e⟩
  rw [pm81_3 ⟨hP, rfl⟩, pm81_3 ⟨hQ, rfl⟩, e]

/-!
## [✱82] Selections from relative products

*(Vol. 1, p. 524)*

> *Summary of* *82.
>
> The propositions contained in this number are not much used except in connection with the associative law for cardinal multiplication, but they have a certain intrinsic interest. We prove in this number that, with a suitable hypothesis, (\(P\mid Q)_{\Delta}ʻ\lambda\) results from \(P_{\Delta}ʻQʻʻ\lambda\) by multiplying each member by \(Q\), *i.e.*
>
> *82·272. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow 1.\lambda\in \text{D}ʻ(\breve{Q})_{\in}.\supset.(P\mid Q)_{\Delta}ʻ\lambda=\mid QʻʻP_{\Delta}ʻQʻʻ\lambda\)
>
> Also under a suitable hypothesis the domains of (\(P\mid Q)_{\Delta}ʻ\lambda\) are the domains of \(P_{\Delta}ʻQʻʻ\lambda\), *i.e.*
>
> *82·32. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow 1.\lambda\subset \text{ᗡ}ʻQ.\supset.\text{D}ʻʻ(P\mid Q)_{\Delta}ʻ\lambda=\text{D}ʻʻP_{\Delta}ʻQʻʻ\lambda\)
>
> In the applications of propositions of the present number in *85, \(P\) and \(Q\) are replaced by \({\in}\) and \(\overrightarrow{Q}\). By *62·26, \(\in \mid \overrightarrow{Q}=Q\); thus we obtain relations between \(Q_{\Delta}ʻ\lambda\) and \({\in}_{\Delta}ʻ\overrightarrow{Q}ʻʻ\lambda\).

**Lean reading.** `P | Q` is `P ⨾ Q` with `P : α → β → Prop`, `Q : β → γ → Prop`; `|Q` and `T|` are
the relations `relProdR Q` and `relProdL T` of ✱38, so `|Q''λ` is `relProdR Q ʻʻ λ`, and `T ‖ Q̆` is
`T ∥ Q˘`. `D'(Q̆)_∈` is `dom (imgRel Q˘)` and `D'Q_∈` is `dom (imgRel Q)`. `M | Q ↾ λ` is `(M | Q) ↾
λ` by ✱35·25 (Lean's precedences give the same), and `T | P ↾ λ | Q̆` in ✱82·43 is written `((T ⨾ P)
↾ L) ⨾ Q˘`. Four enunciations are false as printed: ✱82·23·231 need `Q ↾ λ ∈ 1 → 1` instead of `Cls
→ 1` (PM's proof uses ✱72·59, which needs `1 → Cls`), and ✱82·41·411 need `T ∈ 1 → 1` instead of
`Cls → 1`; the corrected versions are proved and the printed ones refuted in Lean
(`pm82_23_printed_false`, `pm82_231_printed_false`, `pm82_41_printed_false`,
`pm82_411_printed_false`). All later propositions of the number that PM derives from them already
have the stronger hypotheses.

**Status.** proved (corrected): ✱82·23, ✱82·231, ✱82·41, ✱82·411 proved (corrected) (hypothesis `Cls
→ 1` strengthened to `1 → 1`, printed forms refuted; see their docstrings); all other propositions
proved.
-/

theorem relProd_cres {M : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    M ⨾ (Q ↾ L) = M ⨾ Q ↾ L := by
  funext x z
  apply propext
  simp only [relProd, cres]
  constructor
  · rintro ⟨y, h1, h2, h3⟩; exact ⟨⟨y, h1, h2⟩, h3⟩
  · rintro ⟨⟨y, h1, h2⟩, h3⟩; exact ⟨y, h1, h2, h3⟩

theorem mem_relProdR_img {Q : β → γ → Prop} {X : Set (α → β → Prop)} {U : α → γ → Prop} :
    U ∈ relProdR Q ʻʻ X ↔ ∃ M, M ∈ X ∧ U = M ⨾ Q := Iff.rfl

theorem mem_relProdL_img {T : δ → α → Prop} {X : Set (α → β → Prop)} {U : δ → β → Prop} :
    U ∈ relProdL T ʻʻ X ↔ ∃ M, M ∈ X ∧ U = T ⨾ M := Iff.rfl

/-- ✱82·2. \(\vdash:M\in P_{\Delta}ʻ\kappa.N\in Q_{\Delta}ʻ\lambda.Qʻʻ\lambda\subset \kappa.\supset.M\mid N\in (P\mid Q)_{\Delta}ʻ\lambda\) -/
theorem pm82_2 {P M : α → β → Prop} {Q N : β → γ → Prop} {K : Set β} {L : Set γ} :
    (M ∈ sel P K ∧ N ∈ sel Q L) ∧ Q ʻʻ L ⊆ K → M ⨾ N ∈ sel (P ⨾ Q) L := by
  intro h
  sel_simp
  grind

/-- ✱82·21. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow \text{Cls}.\lambda\subset \text{ᗡ}ʻQ.\supset.Q_{\Delta}ʻ\lambda=\iotaʻQ\upharpoonright \lambda\) -/
theorem pm82_21 {Q : β → γ → Prop} {L : Set γ} :
    Q ↾ L ∈ arrow one Cls ∧ L ⊆ codom Q → sel Q L = ι (Q ↾ L) := by
  intro h
  sel_simp
  grind

/-- ✱82·22. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow \text{Cls}.\lambda=\breve{Q}ʻʻ\kappa.M\in P_{\Delta}ʻ\kappa.\supset.M\mid Q\in (P\mid Q)_{\Delta}ʻ\lambda\) -/
theorem pm82_22 {P M : α → β → Prop} {Q : β → γ → Prop} {K : Set β} {L : Set γ} :
    (Q ↾ L ∈ arrow one Cls ∧ L = Q˘ ʻʻ K) ∧ M ∈ sel P K → M ⨾ Q ∈ sel (P ⨾ Q) L := by
  intro h
  sel_simp
  grind

/-- ✱82·221. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow \text{Cls}.\lambda\subset \text{ᗡ}ʻQ.M\in P_{\Delta}ʻQʻʻ\lambda.\supset.M\mid Q\upharpoonright \lambda\in (P\mid Q)_{\Delta}ʻ\lambda\) -/
theorem pm82_221 {P M : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    (Q ↾ L ∈ arrow one Cls ∧ L ⊆ codom Q) ∧ M ∈ sel P (Q ʻʻ L) → M ⨾ Q ↾ L ∈ sel (P ⨾ Q) L := by
  intro h
  sel_simp
  grind

/-- ✱82·23. \(\vdash:Q\upharpoonright \lambda\in \text{Cls}\rightarrow 1.\kappa=Qʻʻ\lambda.R\in (P\mid Q)_{\Delta}ʻ\lambda.\supset.R\mid \breve{Q}\in P_{\Delta}ʻ\kappa\)

**Status.** proved (corrected): PM's hypothesis `Q ↾ λ ∈ Cls → 1` is too weak: its proof uses
✱72·59, which needs `Q ↾ λ ∈ 1 → Cls`, besides ✱71·25, which needs `Cls → 1`. With `Q ↾ λ` many-one
only, `R | Q̆` may relate `x` to a `b` with `∼(xPb)`: take `Q` relating two terms `b, b'` to one
`z`, `λ = ι'z`, `P = x ↓ b'` and `R = x ↓ z` (`pm82_23_printed_false`). The corrected hypothesis is
`Q ↾ λ ∈ 1 → 1` (as in ✱82·24). -/
theorem pm82_23 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} {L : Set γ}
    {R : α → γ → Prop} :
    (Q ↾ L ∈ arrow one one ∧ K = Q ʻʻ L) ∧ R ∈ sel (P ⨾ Q) L → R ⨾ Q˘ ∈ sel P K := by
  intro h
  sel_simp
  grind

/-- The printed form of ✱82·23 is false (with `Q ↾ λ ∈ Cls → 1`). -/
theorem pm82_23_printed_false :
    ¬ ∀ (P : Unit → Bool → Prop) (Q : Bool → Unit → Prop) (L : Set Unit) (K : Set Bool)
      (R : Unit → Unit → Prop),
      (Q ↾ L ∈ arrow Cls one ∧ K = Q ʻʻ L) ∧ R ∈ sel (P ⨾ Q) L → R ⨾ Q˘ ∈ sel P K := by
  intro h
  have hs := h (fun _ b => b = true) (fun _ _ => True) Set.univ _ (fun _ _ => True)
    ⟨⟨mem_arrow_Cls_one.2 (fun _ _ _ _ => rfl), rfl⟩,
      sel_iff.2 ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => ⟨true, rfl, trivial⟩, fun _ _ _ => trivial,
        fun _ _ => ⟨(), trivial⟩⟩⟩
  exact Bool.false_ne_true ((sel_iff.1 hs).2.1 () false ⟨(), trivial, trivial⟩)

/-- ✱82·231. \(\vdash:Q\upharpoonright \lambda\in \text{Cls}\rightarrow 1.R\in (P\mid Q)_{\Delta}ʻ\lambda.\supset.R\mid \breve{Q}\in P_{\Delta}ʻQʻʻ\lambda.R=R\mid \breve{Q}\mid Q\upharpoonright \lambda\)

**Status.** proved (corrected): as in ✱82·23 (which it cites), the hypothesis `Q ↾ λ ∈ Cls → 1` must
be `Q ↾ λ ∈ 1 → 1`; with the printed hypothesis the first conjunct fails for the same counterexample
(`pm82_231_printed_false`). -/
theorem pm82_231 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} {R : α → γ → Prop} :
    Q ↾ L ∈ arrow one one ∧ R ∈ sel (P ⨾ Q) L →
      R ⨾ Q˘ ∈ sel P (Q ʻʻ L) ∧ R = R ⨾ Q˘ ⨾ Q ↾ L := by
  intro h
  refine ⟨pm82_23 ⟨⟨h.1, rfl⟩, h.2⟩, ?_⟩
  sel_simp
  grind

/-- The printed form of ✱82·231 is false (with `Q ↾ λ ∈ Cls → 1`). -/
theorem pm82_231_printed_false :
    ¬ ∀ (P : Unit → Bool → Prop) (Q : Bool → Unit → Prop) (L : Set Unit)
      (R : Unit → Unit → Prop),
      Q ↾ L ∈ arrow Cls one ∧ R ∈ sel (P ⨾ Q) L →
        R ⨾ Q˘ ∈ sel P (Q ʻʻ L) ∧ R = R ⨾ Q˘ ⨾ Q ↾ L := by
  intro h
  have hs := h (fun _ b => b = true) (fun _ _ => True) Set.univ (fun _ _ => True)
    ⟨mem_arrow_Cls_one.2 (fun _ _ _ _ => rfl),
      sel_iff.2 ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => ⟨true, rfl, trivial⟩, fun _ _ _ => trivial,
        fun _ _ => ⟨(), trivial⟩⟩⟩
  exact Bool.false_ne_true ((sel_iff.1 hs.1).2.1 () false ⟨(), trivial, trivial⟩)

/-- ✱82·24. \[\begin{align}\vdash:Q\upharpoonright \lambda\in 1\rightarrow 1.\kappa\subset \text{D}ʻQ.\lambda=\breve{Q}ʻʻ&\kappa.R\in (P\mid Q)_{\Delta}ʻ\lambda.\supset.\\ &\kappa=Qʻʻ\lambda.R\mid \breve{Q}\in P_{\Delta}ʻ\kappa.R=R\mid \breve{Q}\mid Q\end{align}\] -/
theorem pm82_24 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} {L : Set γ}
    {R : α → γ → Prop} :
    ((Q ↾ L ∈ arrow one one ∧ K ⊆ dom Q) ∧ L = Q˘ ʻʻ K) ∧ R ∈ sel (P ⨾ Q) L →
      (K = Q ʻʻ L ∧ R ⨾ Q˘ ∈ sel P K) ∧ R = R ⨾ Q˘ ⨾ Q := by
  rintro ⟨⟨⟨h11, hK⟩, rfl⟩, hR⟩
  have hKe : K = Q ʻʻ (Q˘ ʻʻ K) := by
    sel_simp
    grind
  refine ⟨⟨hKe, pm82_23 ⟨⟨h11, hKe⟩, hR⟩⟩, ?_⟩
  sel_simp
  grind

/-- ✱82·241. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow 1.\lambda\in \text{D}ʻ(\breve{Q})_{\in}.R\in (P\mid Q)_{\Delta}ʻ\lambda.\supset.R=R\mid \breve{Q}\mid Q\) -/
theorem pm82_241 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} {R : α → γ → Prop} :
    (Q ↾ L ∈ arrow one one ∧ L ∈ dom (imgRel Q˘)) ∧ R ∈ sel (P ⨾ Q) L → R = R ⨾ Q˘ ⨾ Q := by
  rintro ⟨⟨h11, K, hK⟩, hR⟩
  have hK' : L = Q˘ ʻʻ K := hK
  subst hK'
  sel_simp
  grind

/-- ✱82·25. \[\begin{align}\vdash:Q\upharpoonright \lambda\in 1\rightarrow 1.\kappa\subset &\text{D}ʻQ.\lambda=\breve{Q}ʻʻ\kappa.R\in (P\mid Q)_{\Delta}ʻ\lambda.\supset.\\ & (\exists M).M\in P_{\Delta}ʻ\kappa.R=M\mid Q \quad[\text{*82·24.*10·24}]\end{align}\] -/
theorem pm82_25 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} {L : Set γ}
    {R : α → γ → Prop} :
    ((Q ↾ L ∈ arrow one one ∧ K ⊆ dom Q) ∧ L = Q˘ ʻʻ K) ∧ R ∈ sel (P ⨾ Q) L →
      ∃ M, M ∈ sel P K ∧ R = M ⨾ Q := by
  intro h
  have := pm82_24 h
  exact ⟨_, this.1.2, this.2⟩

/-- ✱82·251. \[\begin{align}&\vdash:Q\upharpoonright \lambda\in 1\rightarrow 1.R\in (P\mid Q)_{\Delta}ʻ\lambda.\supset.(\exists M).M\in P_{\Delta}ʻQʻʻ\lambda.R=M\mid Q\upharpoonright \lambda\\ &[\text{*82·231.*10·24}]\end{align}\] -/
theorem pm82_251 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} {R : α → γ → Prop} :
    Q ↾ L ∈ arrow one one ∧ R ∈ sel (P ⨾ Q) L → ∃ M, M ∈ sel P (Q ʻʻ L) ∧ R = M ⨾ Q ↾ L := by
  intro h
  have := pm82_231 h
  exact ⟨_, this.1, this.2⟩

/-- ✱82·26. \[\begin{align}\vdash\colon\ldotp Q\upharpoonright \lambda&\in 1\rightarrow 1.\kappa\subset \text{D}ʻQ.\lambda=\breve{Q}ʻʻ\kappa.\supset:\\ &R\in (P\mid Q)_{\Delta}ʻ\lambda.\equiv.(\exists M).M\in P_{\Delta}ʻ\kappa.R=M\mid Q \quad[\text{*82·22·25}]\end{align}\] -/
theorem pm82_26 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} {L : Set γ}
    {R : α → γ → Prop} :
    (Q ↾ L ∈ arrow one one ∧ K ⊆ dom Q) ∧ L = Q˘ ʻʻ K →
      (R ∈ sel (P ⨾ Q) L ↔ ∃ M, M ∈ sel P K ∧ R = M ⨾ Q) := by
  intro h
  refine ⟨fun hR => pm82_25 ⟨h, hR⟩, ?_⟩
  rintro ⟨M, hM, rfl⟩
  have h1 : Q ↾ L ∈ arrow one Cls := by
    have := h.1.1
    sel_simp
    grind
  exact pm82_22 ⟨⟨h1, h.2⟩, hM⟩

/-- ✱82·261. \[\begin{align}\vdash\colon\ldotp Q\upharpoonright &\lambda\in 1\rightarrow 1.\lambda\subset \text{ᗡ}ʻQ.\supset:\\ &R\in (P\mid Q)_{\Delta}ʻ\lambda.\equiv.(\exists M).M\in P_{\Delta}ʻQʻʻ\lambda.R=M\mid Q\upharpoonright \lambda\\ [\text{*82·221·251}]\end{align}\] -/
theorem pm82_261 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} {R : α → γ → Prop} :
    Q ↾ L ∈ arrow one one ∧ L ⊆ codom Q →
      (R ∈ sel (P ⨾ Q) L ↔ ∃ M, M ∈ sel P (Q ʻʻ L) ∧ R = M ⨾ Q ↾ L) := by
  intro h
  refine ⟨fun hR => pm82_251 ⟨h.1, hR⟩, ?_⟩
  rintro ⟨M, hM, rfl⟩
  have h1 : Q ↾ L ∈ arrow one Cls := by
    have := h.1
    sel_simp
    grind
  exact pm82_221 ⟨⟨h1, h.2⟩, hM⟩

/-- ✱82·27. \[\begin{align}&\vdash:Q\upharpoonright \lambda\in 1\rightarrow 1.\kappa\subset \text{D}ʻQ.\lambda=\breve{Q}ʻʻ\kappa.\supset.(P\mid Q)_{\Delta}ʻ\lambda=\mid QʻʻP_{\Delta}ʻ\kappa\\ &[\text{*82·26.*43·121.*37·6}]\end{align}\] -/
theorem pm82_27 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} {L : Set γ} :
    (Q ↾ L ∈ arrow one one ∧ K ⊆ dom Q) ∧ L = Q˘ ʻʻ K →
      sel (P ⨾ Q) L = relProdR Q ʻʻ sel P K := by
  intro h
  ext R
  rw [mem_relProdR_img, pm82_26 h]

/-- ✱82·271. \[\begin{align}&\vdash:Q\upharpoonright \lambda\in 1\rightarrow 1.\lambda\subset \text{ᗡ}ʻQ.\supset.(P\mid Q)_{\Delta}ʻ\lambda=\mid (Q\upharpoonright \lambda)ʻʻP_{\Delta}ʻQʻʻ\lambda\\ &[\text{*82·261.*43·121.*37·6}]\end{align}\] -/
theorem pm82_271 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    Q ↾ L ∈ arrow one one ∧ L ⊆ codom Q →
      sel (P ⨾ Q) L = relProdR (Q ↾ L) ʻʻ sel P (Q ʻʻ L) := by
  intro h
  ext R
  rw [mem_relProdR_img, pm82_261 h]
  simp only [relProd_cres]

/-- ✱82·272. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow 1.\lambda\in \text{D}ʻ(\breve{Q})_{\in}.\supset.(P\mid Q)_{\Delta}ʻ\lambda=\mid QʻʻP_{\Delta}ʻQʻʻ\lambda\) -/
theorem pm82_272 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    Q ↾ L ∈ arrow one one ∧ L ∈ dom (imgRel Q˘) →
      sel (P ⨾ Q) L = relProdR Q ʻʻ sel P (Q ʻʻ L) := by
  rintro ⟨h11, K, hK⟩
  have hK' : L = Q˘ ʻʻ K := hK
  ext R
  rw [mem_relProdR_img]
  constructor
  · intro hR
    exact ⟨R ⨾ Q˘, pm82_23 ⟨⟨h11, rfl⟩, hR⟩, pm82_241 ⟨⟨h11, K, hK⟩, hR⟩⟩
  · rintro ⟨M, hM, rfl⟩
    subst hK'
    sel_simp
    grind

/-- ✱82·28. \[\begin{align}\vdash\colon\ldotp \kappa\upharpoonleft Q\in 1\rightarrow 1.\lambda\subset \text{ᗡ}ʻ&Q.\kappa=Qʻʻ\lambda.\supset:\\ &R\in (P\mid Q)_{\Delta}ʻ\lambda.\equiv.(\exists M).M\in P_{\Delta}ʻ\kappa.R=M\mid Q\\ [\text{*82·26.*74·26}]\end{align}\] -/
theorem pm82_28 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} {L : Set γ}
    {R : α → γ → Prop} :
    (K ◁ Q ∈ arrow one one ∧ L ⊆ codom Q) ∧ K = Q ʻʻ L →
      (R ∈ sel (P ⨾ Q) L ↔ ∃ M, M ∈ sel P K ∧ R = M ⨾ Q) := by
  rintro ⟨⟨h11, hL⟩, rfl⟩
  apply pm82_26
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · sel_simp
    grind
  · sel_simp
    grind
  · sel_simp
    grind

/-- ✱82·29. \[\begin{align}&\vdash:\kappa\upharpoonleft Q\in 1\rightarrow 1.\lambda\subset \text{ᗡ}ʻQ.\kappa=Qʻʻ\lambda.\supset.(P\mid Q)_{\Delta}ʻ\lambda=\mid QʻʻP_{\Delta}ʻ\kappa\\ &[\text{*82·27.*74·26}]\end{align}\] -/
theorem pm82_29 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} {L : Set γ} :
    (K ◁ Q ∈ arrow one one ∧ L ⊆ codom Q) ∧ K = Q ʻʻ L →
      sel (P ⨾ Q) L = relProdR Q ʻʻ sel P K := by
  intro h
  ext R
  rw [mem_relProdR_img, pm82_28 h]

/-- ✱82·291. \[\begin{align}&\vdash:\kappa\upharpoonleft Q\in 1\rightarrow 1.\kappa\in \text{D}ʻQ_{\in}.\supset.(P\mid Q)_{\Delta}ʻ\breve{Q}ʻʻ\kappa=\mid QʻʻP_{\Delta}ʻ\kappa\\ &[\text{Proof as in *82·272}]\end{align}\] -/
theorem pm82_291 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} :
    K ◁ Q ∈ arrow one one ∧ K ∈ dom (imgRel Q) →
      sel (P ⨾ Q) (Q˘ ʻʻ K) = relProdR Q ʻʻ sel P K := by
  rintro ⟨h11, L, hL⟩
  have hL' : K = Q ʻʻ L := hL
  subst hL'
  apply pm82_27
  refine ⟨⟨?_, ?_⟩, rfl⟩
  · sel_simp
    grind
  · sel_simp
    grind

/-- ✱82·3. \(\vdash:M\in P_{\Delta}ʻQʻʻ\lambda.\supset.\text{D}ʻ(M\mid Q\upharpoonright \lambda)=\text{D}ʻM\) -/
theorem pm82_3 {P M : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    M ∈ sel P (Q ʻʻ L) → dom (M ⨾ Q ↾ L) = dom M := by
  intro h
  sel_simp
  grind

/-- ✱82·31. \(\vdash:R\in (P\mid Q)_{\Delta}ʻ\lambda.\supset.\text{D}ʻ(R\mid \breve{Q})=\text{D}ʻR\) -/
theorem pm82_31 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} {R : α → γ → Prop} :
    R ∈ sel (P ⨾ Q) L → dom (R ⨾ Q˘) = dom R := by
  intro h
  sel_simp
  grind

/-- ✱82·32. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow 1.\lambda\subset \text{ᗡ}ʻQ.\supset.\text{D}ʻʻ(P\mid Q)_{\Delta}ʻ\lambda=\text{D}ʻʻP_{\Delta}ʻQʻʻ\lambda\) -/
theorem pm82_32 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    Q ↾ L ∈ arrow one one ∧ L ⊆ codom Q → D ʻʻ sel (P ⨾ Q) L = D ʻʻ sel P (Q ʻʻ L) := by
  intro h
  ext μ
  simp only [mem_D_img]
  constructor
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨M, hM, rfl⟩ := (pm82_261 h).1 hR
    exact ⟨M, hM, pm82_3 hM⟩
  · rintro ⟨M, hM, rfl⟩
    exact ⟨_, (pm82_261 h).2 ⟨M, hM, rfl⟩, (pm82_3 hM).symm⟩

/-- ✱82·33. \(\vdash:\kappa\upharpoonleft Q\in 1\rightarrow 1.\kappa\in \text{D}ʻQ_{\in}.\supset.\text{D}ʻʻ(P\mid Q)_{\Delta}ʻ\breve{Q}ʻʻ\kappa=\text{D}ʻʻP_{\Delta}ʻ\kappa\) -/
theorem pm82_33 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} :
    K ◁ Q ∈ arrow one one ∧ K ∈ dom (imgRel Q) →
      D ʻʻ sel (P ⨾ Q) (Q˘ ʻʻ K) = D ʻʻ sel P K := by
  rintro ⟨h11, L, hL⟩
  have hL' : K = Q ʻʻ L := hL
  subst hL'
  have h1 : Q ↾ (Q˘ ʻʻ (Q ʻʻ L)) ∈ arrow one one := by
    sel_simp
    grind
  have h2 : Q˘ ʻʻ (Q ʻʻ L) ⊆ codom Q := by
    sel_simp
    grind
  rw [pm82_32 ⟨h1, h2⟩]
  congr 2
  sel_simp
  grind

/-- ✱82·4. \(\vdash:T\in 1\rightarrow \text{Cls}.Pʻʻ\lambda\subset \text{ᗡ}ʻT.\supset.T\mid ʻʻP_{\Delta}ʻ\lambda\subset (T\mid P)_{\Delta}ʻ\lambda\) -/
theorem pm82_4 {T : δ → α → Prop} {P : α → β → Prop} {L : Set β} :
    T ∈ arrow one Cls ∧ P ʻʻ L ⊆ codom T → relProdL T ʻʻ sel P L ⊆ sel (T ⨾ P) L := by
  rintro h U ⟨M, hM, hU⟩
  have hU' : U = T ⨾ M := hU
  subst hU'
  sel_simp
  grind

/-- ✱82·41. \(\vdash:T\in \text{Cls}\rightarrow 1.M\in (T\mid P)_{\Delta}ʻ\lambda.\supset.\breve{T}\mid M\in P_{\Delta}ʻ\lambda.M=T\mid \breve{T}\mid M\)

**Status.** proved (corrected): the second conjunct `M = T | T̆ | M` needs `T` one-many as well
(PM's proof establishes only the first); with `T ∈ Cls → 1` only it fails when two referents of `T`
share a relatum: `T = V̇` from `Bool` to `Unit`, `P = V̇`, `M = true ↓ ()`
(`pm82_41_printed_false`). The corrected hypothesis is `T ∈ 1 → 1` (as in ✱82·42). -/
theorem pm82_41 {T : δ → α → Prop} {P : α → β → Prop} {L : Set β} {M : δ → β → Prop} :
    T ∈ arrow one one ∧ M ∈ sel (T ⨾ P) L → T˘ ⨾ M ∈ sel P L ∧ M = T ⨾ T˘ ⨾ M := by
  intro h
  sel_simp
  grind

/-- The printed form of ✱82·41 is false (with `T ∈ Cls → 1`). -/
theorem pm82_41_printed_false :
    ¬ ∀ (T : Bool → Unit → Prop) (P : Unit → Unit → Prop) (L : Set Unit)
      (M : Bool → Unit → Prop),
      T ∈ arrow Cls one ∧ M ∈ sel (T ⨾ P) L → T˘ ⨾ M ∈ sel P L ∧ M = T ⨾ T˘ ⨾ M := by
  intro h
  have hs := h (fun _ _ => True) (fun _ _ => True) Set.univ (fun b _ => b = true)
    ⟨mem_arrow_Cls_one.2 (fun _ _ _ _ => rfl),
      sel_iff.2 ⟨fun x y _ hx hy => hx.trans hy.symm, fun _ _ _ => ⟨(), trivial, trivial⟩,
        fun _ _ _ => trivial, fun _ _ => ⟨true, rfl⟩⟩⟩
  have e := congrFun (congrFun hs.2 false) ()
  have h2 : ((fun (_ : Bool) (_ : Unit) => True) ⨾ (fun (_ : Bool) (_ : Unit) => True)˘ ⨾
      (fun (b : Bool) (_ : Unit) => b = true)) false () := ⟨true, ⟨(), trivial, trivial⟩, rfl⟩
  exact Bool.false_ne_true (cast e.symm h2)

/-- ✱82·411. \(\vdash:T\in \text{Cls}\rightarrow 1.\supset.(T\mid P)_{\Delta}ʻ\lambda\subset T\mid ʻʻP_{\Delta}ʻ\lambda \quad[\text{*82·41}]\)

**Status.** proved (corrected): as for ✱82·41 (which it cites), `T ∈ Cls → 1` must be `T ∈ 1 → 1`;
with the printed hypothesis the same counterexample gives a member of `(T|P)_Δ'λ` which is not of
the form `T|N` (`pm82_411_printed_false`). -/
theorem pm82_411 {T : δ → α → Prop} {P : α → β → Prop} {L : Set β} :
    T ∈ arrow one one → sel (T ⨾ P) L ⊆ relProdL T ʻʻ sel P L := by
  intro h M hM
  have := pm82_41 ⟨h, hM⟩
  exact ⟨_, this.1, this.2.trans (by funext x z; apply propext; simp only [relProd]; grind)⟩

/-- The printed form of ✱82·411 is false (with `T ∈ Cls → 1`). -/
theorem pm82_411_printed_false :
    ¬ ∀ (T : Bool → Unit → Prop) (P : Unit → Unit → Prop) (L : Set Unit),
      T ∈ arrow Cls one → sel (T ⨾ P) L ⊆ relProdL T ʻʻ sel P L := by
  intro h
  have hM : (fun b (_ : Unit) => b = true) ∈ sel ((fun (_ : Bool) (_ : Unit) => True) ⨾
      (fun (_ : Unit) (_ : Unit) => True)) Set.univ :=
    sel_iff.2 ⟨fun x y _ hx hy => hx.trans hy.symm, fun _ _ _ => ⟨(), trivial, trivial⟩,
      fun _ _ _ => trivial, fun _ _ => ⟨true, rfl⟩⟩
  obtain ⟨N, -, hN⟩ := h _ _ Set.univ (mem_arrow_Cls_one.2 (fun _ _ _ _ => rfl)) hM
  have hN' : (fun (b : Bool) (_ : Unit) => b = true) = (fun (_ : Bool) (_ : Unit) => True) ⨾ N :=
    hN
  have e1 := congrFun (congrFun hN' true) ()
  have e2 := congrFun (congrFun hN' false) ()
  have h1 : ((fun (_ : Bool) (_ : Unit) => True) ⨾ N) true () := cast e1 (rfl : true = true)
  obtain ⟨u, -, hu⟩ := h1
  have h2 : ((fun (_ : Bool) (_ : Unit) => True) ⨾ N) false () := ⟨u, trivial, hu⟩
  exact Bool.false_ne_true (cast e2.symm h2)

/-- ✱82·42. \(\vdash:T\in 1\rightarrow 1.Pʻʻ\lambda\subset \text{ᗡ}ʻT.\supset.(T\mid P)_{\Delta}ʻ\lambda=T\mid ʻʻP_{\Delta}ʻ\lambda \quad[\text{*82·4·411}]\) -/
theorem pm82_42 {T : δ → α → Prop} {P : α → β → Prop} {L : Set β} :
    T ∈ arrow one one ∧ P ʻʻ L ⊆ codom T → sel (T ⨾ P) L = relProdL T ʻʻ sel P L := by
  intro h
  have h1 : T ∈ arrow one Cls := by
    have := h.1
    sel_simp
    grind
  exact Set.Subset.antisymm (pm82_411 h.1) (pm82_4 ⟨h1, h.2⟩)

/-- ✱82·43. \[\begin{align}\vdash:T,\,Q\upharpoonright \lambda\in 1\rightarrow 1.Pʻʻ\lambda\subset \text{ᗡ}ʻT.\lambda\subset &\text{ᗡ}ʻQ.\kappa=Qʻʻ\lambda.\supset.\\ &(T\mid P\upharpoonright \lambda\mid \breve{Q})_{\Delta}ʻ\kappa=(T\Arrowvert \breve{Q})ʻʻP_{\Delta}ʻ\lambda\end{align}\] -/
theorem pm82_43 {T : δ → α → Prop} {P : α → β → Prop} {Q : γ → β → Prop} {L : Set β}
    {K : Set γ} :
    ((((T ∈ arrow one one ∧ Q ↾ L ∈ arrow one one) ∧ P ʻʻ L ⊆ codom T) ∧ L ⊆ codom Q) ∧
        K = Q ʻʻ L) →
      sel (((T ⨾ P) ↾ L) ⨾ Q˘) K = (T ∥ Q˘) ʻʻ sel P L := by
  rintro ⟨⟨⟨⟨hT, hQ⟩, hPT⟩, hLQ⟩, rfl⟩
  ext U
  constructor
  · intro hU
    refine ⟨fun x y => ∃ t c, T t x ∧ U t c ∧ Q c y ∧ y ∈ L, ?_, ?_⟩
    · sel_simp
      grind
    · rw [dpar_iff]
      sel_simp
      grind
  · rintro ⟨X, hX, hU⟩
    rw [dpar_iff] at hU
    subst hU
    sel_simp
    grind

theorem relProd_cres_inj {P M M' : α → β → Prop} {Q : β → γ → Prop} {L : Set γ}
    (hQ : Q ↾ L ∈ arrow one one) (hM : M ∈ sel P (Q ʻʻ L)) (hM' : M' ∈ sel P (Q ʻʻ L))
    (e : M ⨾ Q ↾ L = M' ⨾ Q ↾ L) : M = M' := by
  rw [mem_arrow_one_one] at hQ
  have key : ∀ {M M' : α → β → Prop}, M ∈ sel P (Q ʻʻ L) → M ⨾ Q ↾ L = M' ⨾ Q ↾ L →
      ∀ x y, M x y → M' x y := by
    intro M M' hM e x y hxy
    obtain ⟨z, hz, hyz⟩ := (sel_iff.1 hM).2.2.1 x y hxy
    have h1 : (M ⨾ Q ↾ L) x z := ⟨⟨y, hxy, hyz⟩, hz⟩
    rw [e] at h1
    obtain ⟨⟨y', hy', hyz'⟩, -⟩ := h1
    have : y' = y := hQ.1 y' y z ⟨⟨hyz', hz⟩, ⟨hyz, hz⟩⟩
    exact this ▸ hy'
  funext x y
  exact propext ⟨key hM e x y, key hM' e.symm x y⟩

/-- ✱82·45. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow 1.\lambda\subset \text{ᗡ}ʻQ.\supset.(P\mid Q)_{\Delta}ʻ\lambda\text{ sm }P_{\Delta}ʻQʻʻ\lambda\) -/
theorem pm82_45 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    Q ↾ L ∈ arrow one one ∧ L ⊆ codom Q → sm (sel (P ⨾ Q) L) (sel P (Q ʻʻ L)) := by
  intro h
  rw [sm_iff]
  refine ⟨fun U M => M ∈ sel P (Q ʻʻ L) ∧ U = M ⨾ Q ↾ L, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_arrow_one_one]
    constructor
    · rintro U U' M ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
    · rintro U M M' ⟨⟨hM, e⟩, ⟨hM', e'⟩⟩
      exact relProd_cres_inj h.1 hM hM' (e.symm.trans e')
  · ext U
    rw [pm82_261 h]
    rfl
  · ext M
    exact ⟨fun hM => ⟨_, hM, rfl⟩, fun ⟨_, hM, _⟩ => hM⟩

/-- ✱82·5. \[\begin{align}\vdash:P\upharpoonright Qʻʻ\lambda\in \text{Cls}\rightarrow 1.Q\upharpoonright \lambda&\in 1\rightarrow 1.\lambda\subset \text{ᗡ}ʻQ.\supset.\\ &(P\mid Q)_{\Delta}ʻ\lambda\text{ sm }\text{D}ʻʻP_{\Delta}ʻQʻʻ\lambda \quad[\text{*82·45.*81·21}]\end{align}\] -/
theorem pm82_5 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    (P ↾ Q ʻʻ L ∈ arrow Cls one ∧ Q ↾ L ∈ arrow one one) ∧ L ⊆ codom Q →
      sm (sel (P ⨾ Q) L) (D ʻʻ sel P (Q ʻʻ L)) := by
  rintro ⟨⟨hP, hQ⟩, hL⟩
  exact sm_trans (pm82_45 ⟨hQ, hL⟩) (sm_symm (pm81_21 hP).2)

/-- ✱82·51. \[\begin{align}\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.\kappa\upharpoonleft Q\in 1&\rightarrow 1.\lambda\subset \text{ᗡ}ʻQ.\kappa=Qʻʻ\lambda.\supset.\\ &(P\mid Q)_{\Delta}ʻ\lambda\text{ sm }\text{D}ʻʻP_{\Delta}ʻ\kappa \quad[\text{*82·5.*74·251}]\end{align}\] -/
theorem pm82_51 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} {L : Set γ} :
    ((P ↾ K ∈ arrow Cls one ∧ K ◁ Q ∈ arrow one one) ∧ L ⊆ codom Q) ∧ K = Q ʻʻ L →
      sm (sel (P ⨾ Q) L) (D ʻʻ sel P K) := by
  rintro ⟨⟨⟨hP, hQ⟩, hL⟩, rfl⟩
  refine pm82_5 ⟨⟨hP, ?_⟩, hL⟩
  sel_simp
  grind

/-- ✱82·52. \(\vdash:P\upharpoonright \kappa\in \text{Cls}\rightarrow 1.\kappa\upharpoonleft Q\in 1\rightarrow 1.\kappa\in \text{D}ʻQ_{\in}.\supset.(P\mid Q)_{\Delta}ʻ\breve{Q}ʻʻ\kappa\text{ sm }\text{D}ʻʻP_{\Delta}ʻ\kappa\) -/
theorem pm82_52 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} :
    (P ↾ K ∈ arrow Cls one ∧ K ◁ Q ∈ arrow one one) ∧ K ∈ dom (imgRel Q) →
      sm (sel (P ⨾ Q) (Q˘ ʻʻ K)) (D ʻʻ sel P K) := by
  rintro ⟨⟨hP, hQ⟩, L, hL⟩
  have hL' : K = Q ʻʻ L := hL
  subst hL'
  refine pm82_51 ⟨⟨⟨hP, hQ⟩, ?_⟩, ?_⟩
  · sel_simp
    grind
  · sel_simp
    grind

/-- ✱82·53. \[\begin{align}\vdash:&P\upharpoonright \kappa,R\upharpoonright \kappa\in \text{Cls}\rightarrow 1.\kappa\upharpoonleft Q\in 1\rightarrow 1.\kappa\in \text{D}ʻQ_\in .\overrightarrow{P}ʻʻ\kappa=\overrightarrow{R}ʻʻ\kappa.\supset.\\ &(P\mid Q)_{\Delta}ʻ\breve{Q}ʻʻ\kappa\,\text{ sm }\,(R\mid Q)_{\Delta}ʻ\breve{Q}ʻʻ\kappa.\\ &\text{D}ʻʻ(P\mid Q)_{\Delta}ʻ\breve{Q}ʻʻ\kappa=\text{D}ʻʻ(R\mid Q)_{\Delta}ʻ\breve{Q}ʻʻ\kappa=\\ &\qquad\qquad\qquad\qquad\hat{\mu}\{\alpha\in \overrightarrow{P}ʻʻ\kappa.\supset_{\alpha}.\mu\cap \alpha\in 1:\mu\subset Pʻʻ\kappa\}\\ &\qquad\qquad\qquad\qquad\qquad=\text{D}ʻʻP_{\Delta}ʻ\kappa=\text{D}ʻʻR_{\Delta}ʻ\kappa\end{align}\] -/
theorem pm82_53 {P R : α → β → Prop} {Q : β → γ → Prop} {K : Set β} :
    (((P ↾ K ∈ arrow Cls one ∧ R ↾ K ∈ arrow Cls one) ∧ K ◁ Q ∈ arrow one one) ∧
        K ∈ dom (imgRel Q)) ∧ Rfwd P ʻʻ K = Rfwd R ʻʻ K →
      sm (sel (P ⨾ Q) (Q˘ ʻʻ K)) (sel (R ⨾ Q) (Q˘ ʻʻ K)) ∧
        (((D ʻʻ sel (P ⨾ Q) (Q˘ ʻʻ K) = D ʻʻ sel (R ⨾ Q) (Q˘ ʻʻ K) ∧
          D ʻʻ sel (R ⨾ Q) (Q˘ ʻʻ K) =
            {μ | (∀ A, A ∈ Rfwd P ʻʻ K → μ ∩ A ∈ one) ∧ μ ⊆ P ʻʻ K}) ∧
          {μ | (∀ A, A ∈ Rfwd P ʻʻ K → μ ∩ A ∈ one) ∧ μ ⊆ P ʻʻ K} = D ʻʻ sel P K) ∧
          D ʻʻ sel P K = D ʻʻ sel R K) := by
  rintro ⟨⟨⟨⟨hP, hR⟩, hQ⟩, hK⟩, e⟩
  have e1 := pm82_33 (P := P) ⟨hQ, hK⟩
  have e2 := pm82_33 (P := R) ⟨hQ, hK⟩
  have e3 := pm81_31 ⟨⟨hP, hR⟩, e⟩
  have e4 : D ʻʻ sel P K = {μ | (∀ A, A ∈ Rfwd P ʻʻ K → μ ∩ A ∈ one) ∧ μ ⊆ sumCls (Rfwd P ʻʻ K)} :=
    pm81_3 ⟨hP, rfl⟩
  have e5 : sumCls (Rfwd P ʻʻ K) = P ʻʻ K := by
    ext x
    constructor
    · rintro ⟨A, ⟨y, hy, rfl⟩, hx⟩; exact ⟨y, hy, hx⟩
    · rintro ⟨y, hy, hx⟩; exact ⟨_, ⟨y, hy, rfl⟩, hx⟩
  rw [e5] at e4
  refine ⟨?_, ⟨⟨?_, ?_⟩, e4.symm⟩, e3⟩
  · exact sm_trans (pm82_52 ⟨⟨hP, hQ⟩, hK⟩)
      (e3 ▸ sm_symm (pm82_52 ⟨⟨hR, hQ⟩, hK⟩))
  · rw [e1, e2, e3]
  · rw [e2, ← e3, e4]

/-!
## [✱83] Selections from classes of classes

*(Vol. 1, p. 531)*

> *Summary of* *83.
>
> In this number, the general propositions which have been proved for \(P_{\Delta}ʻ\kappa\) are to be applied to the important special case where \(P\) is \(\in\). In this case, we have selections from classes of classes: if \(R \in \in_{\Delta}ʻ\kappa\), \(R\) picks out a *representative* \(Rʻ\alpha\) from each class \(\alpha\) which is a member of \(\kappa\); *i.e.* we have \[ \alpha \in \kappa .\supset_{\alpha}. Rʻ\alpha \in \alpha. \]
>
> The propositions of this number result from those of previous numbers either immediately, by the substitution of \(\in\) for \(P\), or by the use of propositions of *62, notably \(\overrightarrow{{\in}}ʻ\alpha = \alpha\) (*62·2), and \({\in}ʻʻ\kappa = sʻ\kappa\) (*62·3).
>
> The propositions of the present number follow, in the main, the same course as those of *80, with \(\in\) substituted for \(P\) (except that the special forms of propositions before *80·2 are not given). We have first a set of propositions resulting immediately from early propositions of *80. Of these the most used are:
>
> *83·11. \(\vdash: \Lambda \in \kappa .\supset. {\in}_{\Delta}ʻ\kappa = \Lambda\)
>
> …

**Lean reading.** PM's relation `∈` is `memRel`, so `∈_Δ'κ` is `sel memRel K` with `K : Set (Set
α)`. Since `∈⃗'α = α` (✱62·2) and `∈''κ = s'κ` (✱62·3) hold by definition in Lean, many propositions
are the ✱80 propositions at `P = memRel`, and are proved by them. `ι''α` is `iota ʻʻ A`, `ῐ` is
`iota˘`, `ι'(…)` is `ι (…)`, and `1` is `one` at the type of the classes concerned. In ✱83·8·81 the
relative types `t₁₀'κ`, `t'…`, `t₀'κ` (✱63–✱64) are `Set.univ` of the types that Lean's typing
gives, so these explicit typings hold trivially. ✱83·52 is ✱83·24 again (the e-text's braces are TeX
grouping).

**Status.** proved (all propositions).
-/

theorem memRel_apply {x : α} {A : Set α} : memRel x A ↔ x ∈ A := Iff.rfl

theorem iota_apply {B : Set α} {y : α} : iota B y ↔ B = ι y := Iff.rfl

theorem dom_rcup {R S : α → β → Prop} : dom (R ⊍ S) = dom R ∪ dom S := by
  ext x
  simp only [dom, rcup, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨y, h | h⟩
    · exact Or.inl ⟨y, h⟩
    · exact Or.inr ⟨y, h⟩
  · rintro (⟨y, h⟩ | ⟨y, h⟩)
    · exact ⟨y, Or.inl h⟩
    · exact ⟨y, Or.inr h⟩

/-- ✱83·1. \(\vdash:\exists !{\in}_{\Delta}ʻ\kappa.\supset.\Lambda{\sim}{\in}\kappa\) -/
theorem pm83_1 {K : Set (Set α)} : (sel memRel K).Nonempty → Λ ∉ K := by
  rintro ⟨M, hM⟩ h
  obtain ⟨x, hx, -⟩ := sel_ex hM h
  have : x ∈ (Λ : Set α) := (sel_iff.1 hM).2.1 _ _ hx
  rw [Null_eq_empty] at this
  exact this

/-- ✱83·11. \(\vdash:\Lambda \in \kappa.\supset.{\in}_{\Delta}ʻ\kappa=\Lambda \quad[\text{*83·1.Transp}]\) -/
theorem pm83_11 {K : Set (Set α)} : Λ ∈ K → sel (memRel : α → Set α → Prop) K = Λ := by
  intro h
  ext M
  rw [Null_eq_empty]
  exact ⟨fun hM => pm83_1 ⟨M, hM⟩ h, fun h => h.elim⟩

/-- ✱83·12. \(\vdash.{\in}_{\Delta}ʻ\kappa=({\in}\upharpoonright \kappa)_{\Delta}ʻ\kappa \quad[\text{*80·23}]\) -/
theorem pm83_12 {K : Set (Set α)} : sel memRel K = sel (memRel ↾ K) K := pm80_23

/-- ✱83·13. \(\vdash:\Lambda{\sim}\in \kappa.Q=\in \upharpoonright \kappa.\supset.{\in}_{\Delta}ʻ\kappa=Q_{\Delta}ʻ\text{ᗡ}ʻQ \quad[\text{*80·24.*62·231}]\) -/
theorem pm83_13 {K : Set (Set α)} {Q : α → Set α → Prop} :
    Λ ∉ K ∧ Q = memRel ↾ K → sel memRel K = sel Q (codom Q) := by
  rintro ⟨h, e⟩
  refine pm80_24 ⟨fun A hA => ?_, e⟩
  by_contra hc
  apply h
  convert hA
  rw [Null_eq_empty]
  ext x
  simp only [Set.mem_empty_iff_false, false_iff]
  exact fun hx => hc ⟨x, hx⟩

/-- ✱83·14. \(\vdash:\exists !{\in}_{\Delta}ʻ\kappa.Q=\in \upharpoonright \kappa.\supset.{\in}_{\Delta}ʻ\kappa=Q_{\Delta}ʻ\text{ᗡ}ʻQ \quad[\text{*83·1·13}]\) -/
theorem pm83_14 {K : Set (Set α)} {Q : α → Set α → Prop} :
    (sel memRel K).Nonempty ∧ Q = memRel ↾ K → sel memRel K = sel Q (codom Q) := pm80_25

/-- ✱83·15. \(\vdash.{\in}_{\Delta}ʻ\Lambda=\iotaʻ\dot{\Lambda} \quad[\text{*80·26}]\) -/
theorem pm83_15 : sel memRel (Λ : Set (Set α)) = ι (rNull : α → Set α → Prop) := pm80_26

/-- ✱83·16. \(\vdash:\exists !\kappa.\supset.\dot{\Lambda}{\sim}\in {\in}_{\Delta}ʻ\kappa \quad[\text{*80·28}]\) -/
theorem pm83_16 {K : Set (Set α)} : K.Nonempty → rNull ∉ sel memRel K := pm80_28

/-- ✱83·2. \(\vdash\colon\ldotp R\in {\in}_{\Delta}ʻ\kappa.\supset:\alpha\in \kappa.\equiv.\text{E}!Rʻ\alpha.\equiv.Rʻ\alpha\in \alpha \quad[\text{*80·32.*62·2}]\) -/
theorem pm83_2 {K : Set (Set α)} {R : α → Set α → Prop} {A : Set α} :
    R ∈ sel memRel K →
      ((A ∈ K ↔ EDesc R A) ∧ (EDesc R A ↔ Desc R A (fun x => x ∈ A))) := pm80_32

/-- ✱83·21. \(\vdash:R\in {\in}_{\Delta}ʻ\kappa.\supset.\text{D}ʻR\subset sʻ\kappa \quad[\text{*80·33.*62·3}]\) -/
theorem pm83_21 {K : Set (Set α)} {R : α → Set α → Prop} :
    R ∈ sel memRel K → dom R ⊆ sumCls K := pm80_33

/-- ✱83·22. \(\vdash:R\in {\in}_{\Delta}ʻ\kappa.\supset.\text{E}‼Rʻʻ\kappa.Rʻʻ\kappa=\text{D}ʻR \quad[\text{*80·34}]\) -/
theorem pm83_22 {K : Set (Set α)} {R : α → Set α → Prop} :
    R ∈ sel memRel K → EE R K ∧ R ʻʻ K = dom R := pm80_34

/-- ✱83·23. \(\vdash:R\in {\in}_{\Delta}ʻ\kappa.\supset.\text{D}ʻR=\hat{x}\{(\exists \alpha).\alpha\in \kappa.x=Rʻ\alpha\} \quad[\text{*80·35}]\) -/
theorem pm83_23 {K : Set (Set α)} {R : α → Set α → Prop} :
    R ∈ sel memRel K → dom R = {x | ∃ A, A ∈ K ∧ Desc R A (fun b => x = b)} := pm80_35

/-- ✱83·24. \(\vdash:R\in {\in}_{\Delta}ʻ\kappa.\alpha\in \kappa.x\in \alpha.\supset.[\{R\dot{-}(Rʻ\alpha)\downarrow \alpha\}\unicode{x228d}x\downarrow \alpha]\in {\in}_{\Delta}ʻ\kappa \quad[\text{*80·41}]\) -/
theorem pm83_24 {K : Set (Set α)} {R : α → Set α → Prop} {A : Set α} {x : α} :
    (R ∈ sel memRel K ∧ A ∈ K) ∧ x ∈ A →
      Desc R A (fun b => (R ∸ b ↓ A) ⊍ x ↓ A ∈ sel memRel K) := pm80_41

/-- ✱83·25. \(\vdash:\exists !{\in}_{\Delta}ʻ\kappa.\supset.\dot{s}ʻ{\in}_{\Delta}ʻ\kappa=\in \upharpoonright \kappa \quad[\text{*80·42}]\) -/
theorem pm83_25 {K : Set (Set α)} :
    (sel memRel K).Nonempty → sumRel (sel memRel K) = memRel ↾ K := pm80_42

/-- ✱83·26. \(\vdash:Q=\in \upharpoonright \kappa.\exists !Q_{\Delta}ʻ\kappa.\supset.\dot{s}ʻQ_{\Delta}ʻ\kappa=Q \quad[\text{*83·12·25}]\) -/
theorem pm83_26 {K : Set (Set α)} {Q : α → Set α → Prop} :
    Q = memRel ↾ K ∧ (sel Q K).Nonempty → sumRel (sel Q K) = Q := by
  rintro ⟨rfl, h⟩
  rw [pm80_42 h]
  funext x A
  apply propext
  simp only [cres, and_assoc, and_self]

/-- ✱83·27. \(\vdash\colon\ldotp R\unicode{x2abd}\in .R\in 1\rightarrow \text{Cls}.\equiv:\alpha\in \text{ᗡ}ʻR.\supset_{\alpha}.Rʻ\alpha\in \alpha \quad[\text{*62·45.*71·16}]\) -/
theorem pm83_27 {R : α → Set α → Prop} :
    (R ⪽ memRel ∧ R ∈ arrow one Cls) ↔ ∀ A, A ∈ codom R → Desc R A (fun x => x ∈ A) := by
  rw [mem_arrow_one_Cls]
  constructor
  · rintro ⟨h1, h2⟩ A ⟨x, hx⟩
    exact (desc_iff_of hx (fun x' hx' => h2 x' x A ⟨hx', hx⟩)).2 (h1 x A hx)
  · intro h
    refine ⟨fun x A hx => ?_, fun x y A ⟨hx, hy⟩ => ?_⟩
    · exact (desc_iff.1 (h A ⟨x, hx⟩)).2 x hx
    · obtain ⟨⟨b, hb⟩, -⟩ := desc_iff.1 (h A ⟨x, hx⟩)
      exact ((hb x).1 hx).trans ((hb y).1 hy).symm

/-- ✱83·271. \(\vdash\colon\ldotp R\in {\in}_{\Delta}ʻ\text{ᗡ}ʻR.\equiv:\alpha\in \text{ᗡ}ʻR.\supset_{\alpha}.Rʻ\alpha\in \alpha \quad[\text{*83·27.*80·14}]\) -/
theorem pm83_271 {R : α → Set α → Prop} :
    R ∈ sel memRel (codom R) ↔ ∀ A, A ∈ codom R → Desc R A (fun x => x ∈ A) := by
  rw [← pm83_27, mem_sel_iff]
  exact ⟨fun ⟨⟨h1, h2⟩, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨⟨h2, h1⟩, rfl⟩⟩

/-- ✱83·28. \[\begin{align}&\vdash\colon\ldotp R\in {\in}_{\Delta}ʻ\kappa.\equiv:\alpha\in \kappa.\supset_{\alpha}.Rʻ\alpha\in \alpha:\text{ᗡ}ʻR=\kappa\\ &[\text{*83·27.*80·14.*14·15}]\end{align}\] -/
theorem pm83_28 {K : Set (Set α)} {R : α → Set α → Prop} :
    R ∈ sel memRel K ↔ (∀ A, A ∈ K → Desc R A (fun x => x ∈ A)) ∧ codom R = K := by
  constructor
  · intro h
    have e := (mem_sel_iff.1 h).2
    subst e
    exact ⟨pm83_271.1 h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact pm83_271.2 h

/-- ✱83·29. \(\vdash\colon\ldotp R\in {\in}_{\Delta}ʻ\kappa.\equiv:\alpha\in \kappa.\equiv_{\alpha}.Rʻ\alpha\in \alpha:\text{ᗡ}ʻR=\kappa \quad[\text{*83·2·28}]\) -/
theorem pm83_29 {K : Set (Set α)} {R : α → Set α → Prop} :
    R ∈ sel memRel K ↔ (∀ A, A ∈ K ↔ Desc R A (fun x => x ∈ A)) ∧ codom R = K := by
  rw [pm83_28]
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun A => ⟨h A, fun hd => ?_⟩, rfl⟩
    obtain ⟨⟨b, hb⟩, -⟩ := desc_iff.1 hd
    exact ⟨b, (hb b).2 rfl⟩
  · rintro ⟨h, e⟩
    exact ⟨fun A hA => (h A).1 hA, e⟩

/-- ✱83·3. \[\begin{align}&\vdash\colon\ldotp \kappa\cap \lambda=\Lambda.\supset:M\in {\in}_{\Delta}ʻ(\kappa\cup \lambda).\equiv.\\ &(\exists R,\,S).R\in {\in}_{\Delta}ʻ\kappa.S\in {\in}_{\Delta}ʻ\lambda.M=R\unicode{x228d}S \quad[\text{*80·66}]\end{align}\] -/
theorem pm83_3 {K L : Set (Set α)} {M : α → Set α → Prop} :
    K ∩ L = Λ →
      (M ∈ sel memRel (K ∪ L) ↔
        ∃ R S, (R ∈ sel memRel K ∧ S ∈ sel memRel L) ∧ M = R ⊍ S) := pm80_66

/-- ✱83·31. \[\begin{align}&\vdash\colon\ldotp \kappa\cap \lambda=\Lambda.\supset:R\in {\in}_{\Delta}ʻ\kappa.S\in {\in}_{\Delta}ʻ\lambda.\equiv.\\ &(\exists M).M\in {\in}_{\Delta}ʻ(\kappa\cup \lambda).R=M\upharpoonright \kappa.S=M\upharpoonright \lambda \quad[\text{*80·67}]\end{align}\] -/
theorem pm83_31 {K L : Set (Set α)} {R S : α → Set α → Prop} :
    K ∩ L = Λ →
      (R ∈ sel memRel K ∧ S ∈ sel memRel L ↔
        ∃ M, (M ∈ sel memRel (K ∪ L) ∧ R = M ↾ K) ∧ S = M ↾ L) := pm80_67

/-- ✱83·4. \(\vdash.{\in}_{\Delta}ʻ\iotaʻ\alpha=\downarrow \alphaʻʻ\alpha \quad[\text{*80·45.*62·2}]\) -/
theorem pm83_4 {A : Set α} : sel memRel (ι A) = coupleR A ʻʻ A := pm80_45

/-- ✱83·41. \(\vdash.{\in}_{\Delta}ʻ\iotaʻ\alpha\text{ sm }\alpha \quad[\text{*83·4.*73·611}]\) -/
theorem pm83_41 {A : Set α} : sm (sel memRel (ι A)) A := by
  rw [sm_iff]
  refine ⟨fun M x => x ∈ A ∧ M = x ↓ A, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_arrow_one_one]
    constructor
    · rintro M M' x ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
    · rintro M x x' ⟨⟨-, rfl⟩, ⟨-, e⟩⟩
      have : (x ↓ A) x A := ⟨rfl, rfl⟩
      rw [e] at this
      exact this.1
  · rw [pm83_4]
    ext M
    exact ⟨fun ⟨x, hx, e⟩ => ⟨x, hx, e⟩, fun ⟨x, hx, e⟩ => ⟨x, hx, e⟩⟩
  · ext x
    exact ⟨fun hx => ⟨_, hx, rfl⟩, fun ⟨_, hx, _⟩ => hx⟩

/-- ✱83·42. \(\vdash.{\in}_{\Delta}ʻ\iotaʻʻ\alpha=\iotaʻ(\alpha\upharpoonleft \breve{\iota})=\iotaʻ(\breve{\iota}\upharpoonright \iotaʻʻ\alpha)\) -/
theorem pm83_42 {A : Set α} :
    sel memRel (iota ʻʻ A) = ι (A ◁ iota˘) ∧ ι (A ◁ iota˘) = ι (iota˘ ↾ (iota ʻʻ A)) := by
  have e2 : A ◁ iota˘ = iota˘ ↾ (iota ʻʻ A) := by
    funext x B
    apply propext
    simp only [dres, cres, cnv, img, iota_apply, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, rfl⟩; exact ⟨rfl, x, hx, rfl⟩
    · rintro ⟨rfl, y, hy, e⟩
      rw [unitCls_injective e]
      exact ⟨hy, rfl⟩
  refine ⟨?_, by rw [e2]⟩
  ext M
  rw [mem_unitCls]
  constructor
  · intro hM
    have hs := sel_iff.1 hM
    funext x B
    apply propext
    constructor
    · intro hxB
      obtain ⟨y, hy, rfl⟩ := hs.2.2.1 x B hxB
      have : x = y := hs.2.1 x _ hxB
      subst this
      exact ⟨hy, rfl⟩
    · rintro ⟨hx, rfl⟩
      obtain ⟨x', hx'⟩ := hs.2.2.2 (ι x) ⟨x, hx, rfl⟩
      have : x' = x := hs.2.1 x' _ hx'
      rw [this] at hx'
      exact hx'
  · rintro rfl
    rw [sel_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro x y B ⟨-, rfl⟩ ⟨-, e⟩
      exact unitCls_injective e
    · rintro x B ⟨-, rfl⟩
      exact (rfl : x = x)
    · rintro x B ⟨hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro B ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩

/-- ✱83·43. \(\vdash:\kappa\subset 1.\supset.{\in}_{\Delta}ʻ\kappa=\iotaʻ(\breve{\iota}\upharpoonright \kappa)=\iotaʻ(\in \upharpoonright \kappa)\) -/
theorem pm83_43 {K : Set (Set α)} :
    K ⊆ one → sel memRel K = ι (iota˘ ↾ K) ∧ ι (iota˘ ↾ K) = ι (memRel ↾ K) := by
  intro hK
  have e2 : iota˘ ↾ K = memRel ↾ K := by
    funext x B
    apply propext
    simp only [cres, cnv, iota_apply, memRel_apply]
    constructor
    · rintro ⟨rfl, hB⟩; exact ⟨rfl, hB⟩
    · rintro ⟨hx, hB⟩
      obtain ⟨b, rfl⟩ := hK hB
      have : x = b := hx
      subst this
      exact ⟨rfl, hB⟩
  refine ⟨?_, by rw [e2]⟩
  ext M
  rw [mem_unitCls, e2]
  constructor
  · intro hM
    have hs := sel_iff.1 hM
    funext x B
    apply propext
    constructor
    · intro h
      exact ⟨hs.2.1 x B h, hs.2.2.1 x B h⟩
    · rintro ⟨hx, hB⟩
      obtain ⟨x', hx'⟩ := hs.2.2.2 B hB
      obtain ⟨b, rfl⟩ := hK hB
      have e1 : x = b := hx
      have e2 : x' = b := hs.2.1 x' _ hx'
      rw [e1]
      rw [e2] at hx'
      exact hx'
  · rintro rfl
    rw [sel_iff]
    refine ⟨?_, fun x B h => h.1, fun x B h => h.2, ?_⟩
    · rintro x y B ⟨hx, hB⟩ ⟨hy, -⟩
      obtain ⟨b, rfl⟩ := hK hB
      exact (hx : x = b).trans (hy : y = b).symm
    · intro B hB
      obtain ⟨b, rfl⟩ := hK hB
      exact ⟨b, rfl, hB⟩

/-- ✱83·44. \(\vdash:\kappa\subset 1.\supset.{\in}_{\Delta}ʻ\kappa\in 1 \quad[\text{*83·43.*52·22}]\) -/
theorem pm83_44 {K : Set (Set α)} : K ⊆ one → sel memRel K ∈ one := by
  intro hK
  rw [(pm83_43 hK).1]
  exact ⟨_, rfl⟩

/-- ✱83·5. \(\vdash:R\in {\in}_{\Delta}ʻ\kappa.\alpha{\sim}\in \kappa.x\in \alpha.\supset.R\unicode{x228d}x\downarrow \alpha\in {\in}_{\Delta}ʻ(\kappa\cup \iotaʻ\alpha)\) -/
theorem pm83_5 {K : Set (Set α)} {R : α → Set α → Prop} {A : Set α} {x : α} :
    (R ∈ sel memRel K ∧ A ∉ K) ∧ x ∈ A → R ⊍ x ↓ A ∈ sel memRel (K ∪ ι A) := by
  rintro ⟨⟨hR, hA⟩, hx⟩
  have hs := sel_iff.1 hR
  rw [sel_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro a b B ha hb
    rcases ha with ha | ⟨rfl, rfl⟩ <;> rcases hb with hb | ⟨rfl, hB⟩
    · exact hs.1 a b B ha hb
    · exact absurd (hB ▸ hs.2.2.1 a _ ha) hA
    · exact absurd (hs.2.2.1 b _ hb) hA
    · rfl
  · rintro a B (h | ⟨rfl, rfl⟩)
    · exact hs.2.1 a B h
    · exact hx
  · rintro a B (h | ⟨rfl, rfl⟩)
    · exact Or.inl (hs.2.2.1 a B h)
    · exact Or.inr rfl
  · rintro B (hB | rfl)
    · obtain ⟨a, ha⟩ := hs.2.2.2 B hB
      exact ⟨a, Or.inl ha⟩
    · exact ⟨x, Or.inr ⟨rfl, rfl⟩⟩

/-- ✱83·51. \(\vdash:R\in {\in}_{\Delta}ʻ\kappa.\alpha\in \kappa.\supset.R\dot{-}(Rʻ\alpha)\downarrow \alpha\in {\in}_{\Delta}ʻ(\kappa-\iotaʻ\alpha) \quad[\text{*80·78}]\) -/
theorem pm83_51 {K : Set (Set α)} {R : α → Set α → Prop} {A : Set α} :
    R ∈ sel memRel K ∧ A ∈ K → Desc R A (fun b => R ∸ b ↓ A ∈ sel memRel (K \ ι A)) := by
  rintro ⟨hR, hA⟩
  obtain ⟨x, hx, hu⟩ := sel_ex hR hA
  rw [desc_iff_of hx hu]
  exact pm80_78 ⟨hR, hx⟩

/-- ✱83·52. \(\vdash:R\in {\in}_{\Delta}ʻ\kappa.\alpha\in \kappa.x\in \alpha.\supset.{R\dot{-}(Rʻ\alpha)\downarrow \alpha}\unicode{x228d}x\downarrow \alpha\in {\in}_{\Delta}ʻ\kappa \quad[\text{*80·41}]\)

**Status.** proved: the e-text's braces `{R −̇ (R'α) ↓ α}` are TeX grouping and are not printed; the
formula is `{R −̇ (R'α) ↓ α} ∪̇ x ↓ α` (as in ✱83·24, and as cited, ✱80·41), which is also how Lean
parses the unbracketed `R ∸ b ↓ A ⊍ x ↓ A`. -/
theorem pm83_52 {K : Set (Set α)} {R : α → Set α → Prop} {A : Set α} {x : α} :
    (R ∈ sel memRel K ∧ A ∈ K) ∧ x ∈ A →
      Desc R A (fun b => R ∸ b ↓ A ⊍ x ↓ A ∈ sel memRel K) := pm80_41

/-- ✱83·54. \(\vdash:\kappa\cap \lambda=\Lambda.\lambda\subset 1.R\in {\in}_{\Delta}ʻ\kappa.\supset.R\unicode{x228d}\breve{\iota}\upharpoonright \lambda\in {\in}_{\Delta}ʻ(\kappa\cup \lambda)\) -/
theorem pm83_54 {K L : Set (Set α)} {R : α → Set α → Prop} :
    (K ∩ L = Λ ∧ L ⊆ one) ∧ R ∈ sel memRel K → R ⊍ iota˘ ↾ L ∈ sel memRel (K ∪ L) := by
  rintro ⟨⟨hKL, hL⟩, hR⟩
  have hd : ∀ B, B ∈ K → B ∈ L → False := fun B h1 h2 => by
    have : B ∈ K ∩ L := ⟨h1, h2⟩
    rw [hKL, Null_eq_empty] at this
    exact this
  have hs := sel_iff.1 hR
  rw [sel_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro a b B (ha | ⟨ha, hB⟩) (hb | ⟨hb, hB'⟩)
    · exact hs.1 a b B ha hb
    · exact (hd B (hs.2.2.1 a B ha) hB').elim
    · exact (hd B (hs.2.2.1 b B hb) hB).elim
    · exact unitCls_injective (ha.symm.trans hb)
  · rintro a B (h | ⟨rfl, -⟩)
    · exact hs.2.1 a B h
    · exact (rfl : a = a)
  · rintro a B (h | ⟨-, hB⟩)
    · exact Or.inl (hs.2.2.1 a B h)
    · exact Or.inr hB
  · rintro B (hB | hB)
    · obtain ⟨a, ha⟩ := hs.2.2.2 B hB
      exact ⟨a, Or.inl ha⟩
    · obtain ⟨b, rfl⟩ := hL hB
      exact ⟨b, Or.inr ⟨rfl, hB⟩⟩

/-- A selection from a class of unit classes is `ῐ ↾ λ`. -/
theorem sel_unit_cres {L : Set (Set α)} {S : α → Set α → Prop} (hL : L ⊆ one)
    {K : Set (Set α)} (hS : S ∈ sel memRel K) : S ↾ L = iota˘ ↾ (K ∩ L) := by
  have hs := sel_iff.1 hS
  funext x B
  apply propext
  simp only [cres, cnv, iota_apply, Set.mem_inter_iff]
  constructor
  · rintro ⟨h, hB⟩
    obtain ⟨b, rfl⟩ := hL hB
    have : x = b := hs.2.1 x _ h
    subst this
    exact ⟨rfl, hs.2.2.1 _ _ h, hB⟩
  · rintro ⟨rfl, hK, hB⟩
    obtain ⟨x', hx'⟩ := hs.2.2.2 _ hK
    have : x' = x := hs.2.1 x' _ hx'
    exact ⟨this ▸ hx', hB⟩

/-- ✱83·55. \(\vdash:\kappa\cap \lambda=\Lambda.\lambda\subset 1.S\in {\in}_{\Delta}ʻ(\kappa\cup \lambda).\supset.S\dot{-}\breve{\iota}\upharpoonright \lambda\in {\in}_{\Delta}ʻ\kappa\) -/
theorem pm83_55 {K L : Set (Set α)} {S : α → Set α → Prop} :
    (K ∩ L = Λ ∧ L ⊆ one) ∧ S ∈ sel memRel (K ∪ L) → S ∸ iota˘ ↾ L ∈ sel memRel K := by
  rintro ⟨⟨hKL, hL⟩, hS⟩
  have hd : ∀ B, B ∈ K → B ∈ L → False := fun B h1 h2 => by
    have : B ∈ K ∩ L := ⟨h1, h2⟩
    rw [hKL, Null_eq_empty] at this
    exact this
  have e := sel_unit_cres hL hS
  have hs := sel_iff.1 hS
  have key : ∀ x B, (S ∸ iota˘ ↾ L) x B ↔ S x B ∧ B ∈ K := by
    intro x B
    simp only [rdiff, rcap, rneg]
    constructor
    · rintro ⟨h, hn⟩
      refine ⟨h, ?_⟩
      rcases (Set.mem_union _ _ _).1 (hs.2.2.1 x B h) with hB | hB
      · exact hB
      · have h2 : (S ↾ L) x B := ⟨h, hB⟩
        rw [e] at h2
        exact (hn ⟨h2.1, hB⟩).elim
    · rintro ⟨h, hB⟩
      exact ⟨h, fun ⟨_, hBL⟩ => hd B hB hBL⟩
  rw [sel_iff]
  refine ⟨fun a b B ha hb => hs.1 a b B ((key a B).1 ha).1 ((key b B).1 hb).1,
    fun a B h => hs.2.1 a B ((key a B).1 h).1, fun a B h => ((key a B).1 h).2, fun B hB => ?_⟩
  obtain ⟨a, ha⟩ := hs.2.2.2 B (Or.inl hB)
  exact ⟨a, (key a B).2 ⟨ha, hB⟩⟩

/-- ✱83·56. \(\vdash:\kappa\cap \lambda=\Lambda.\lambda\subset 1.\supset.{\in}_{\Delta}ʻ(\kappa\cup \lambda)=\hat{M}\{(\exists R).R\in {\in}_{\Delta}ʻ\kappa.M=R\unicode{x228d}\breve{\iota}\upharpoonright \lambda\}\) -/
theorem pm83_56 {K L : Set (Set α)} :
    K ∩ L = Λ ∧ L ⊆ one →
      sel memRel (K ∪ L) = {M | ∃ R, R ∈ sel memRel K ∧ M = R ⊍ iota˘ ↾ L} := by
  intro h
  ext M
  constructor
  · intro hM
    refine ⟨_, pm83_55 ⟨h, hM⟩, ?_⟩
    have e := sel_unit_cres h.2 hM
    have hs := sel_iff.1 hM
    funext x B
    apply propext
    simp only [rcup, rdiff, rcap, rneg]
    constructor
    · intro hxB
      by_cases hB : (iota˘ ↾ L) x B
      · exact Or.inr hB
      · exact Or.inl ⟨hxB, hB⟩
    · rintro (⟨h1, -⟩ | h2)
      · exact h1
      · have : (iota˘ ↾ ((K ∪ L) ∩ L)) x B := ⟨h2.1, Or.inr h2.2, h2.2⟩
        rw [← e] at this
        exact this.1
  · rintro ⟨R, hR, rfl⟩
    exact pm83_54 ⟨h, hR⟩

/-- ✱83·57. \(\vdash:\kappa\cap \lambda=\Lambda.\lambda\subset 1.\supset.{\in}_{\Delta}ʻ(\kappa\cup \lambda)\text{ sm }{\in}_{\Delta}ʻ\kappa\) -/
theorem pm83_57 {K L : Set (Set α)} :
    K ∩ L = Λ ∧ L ⊆ one → sm (sel memRel (K ∪ L)) (sel memRel K) := by
  intro h
  have hd : ∀ B, B ∈ K → B ∈ L → False := fun B h1 h2 => by
    have : B ∈ K ∩ L := ⟨h1, h2⟩
    rw [h.1, Null_eq_empty] at this
    exact this
  rw [sm_iff]
  refine ⟨fun M R => R ∈ sel memRel K ∧ M = R ⊍ iota˘ ↾ L, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_arrow_one_one]
    constructor
    · rintro M M' R ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
    · rintro M R R' ⟨⟨hR, rfl⟩, ⟨hR', e⟩⟩
      have key : ∀ {R R'}, R ∈ sel memRel K → R ⊍ iota˘ ↾ L = R' ⊍ iota˘ ↾ L →
          R' ∈ sel memRel K → ∀ x B, R x B → R' x B := by
        intro R R' hR e hR' x B hxB
        have := congrFun (congrFun e x) B
        have h1 : (R ⊍ iota˘ ↾ L) x B := Or.inl hxB
        rw [this] at h1
        rcases h1 with h1 | h1
        · exact h1
        · exact (hd B ((sel_iff.1 hR).2.2.1 x B hxB) h1.2).elim
      funext x B
      exact propext ⟨key hR e hR' x B, key hR' e.symm hR x B⟩
  · ext M
    rw [pm83_56 h]
    rfl
  · ext R
    exact ⟨fun hR => ⟨_, hR, rfl⟩, fun ⟨_, hR, _⟩ => hR⟩

/-- ✱83·58. \(\vdash.{\in}_{\Delta}ʻ\kappa \text{ sm } {\in}_{\Delta}ʻ(\kappa-1)\) -/
theorem pm83_58 {K : Set (Set α)} : sm (sel memRel K) (sel memRel (K \ one)) := by
  have e : K = (K \ one) ∪ (K ∩ one) := (Set.sdiff_union_inter K one).symm
  have h := pm83_57 (K := K \ one) (L := K ∩ one) ⟨?_, Set.inter_subset_right⟩
  · rw [← e] at h
    exact h
  · rw [Null_eq_empty]
    ext B
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, h1⟩, -, h2⟩
    exact h1 h2

/-- ✱83·6. \(\vdash:R\in {\in}_{\Delta}ʻ\kappa.\alpha\in \kappa.\supset.\exists !\alpha\cap \text{D}ʻR\) -/
theorem pm83_6 {K : Set (Set α)} {R : α → Set α → Prop} {A : Set α} :
    R ∈ sel memRel K ∧ A ∈ K → (A ∩ dom R).Nonempty := by
  rintro ⟨hR, hA⟩
  obtain ⟨x, hx, -⟩ := sel_ex hR hA
  exact ⟨x, (sel_iff.1 hR).2.1 x A hx, A, hx⟩

/-- ✱83·61. \(\vdash:R\in {\in}_{\Delta}ʻ\kappa.\alpha\in \kappa.\alpha\cap sʻ(\kappa-\iotaʻ\alpha)=\Lambda.\supset.\alpha\cap \text{D}ʻR=\iotaʻRʻ\alpha\) -/
theorem pm83_61 {K : Set (Set α)} {R : α → Set α → Prop} {A : Set α} :
    (R ∈ sel memRel K ∧ A ∈ K) ∧ A ∩ sumCls (K \ ι A) = Λ →
      Desc R A (fun x => A ∩ dom R = ι x) := by
  rintro ⟨⟨hR, hA⟩, hd⟩
  obtain ⟨x, hx, hu⟩ := sel_ex hR hA
  rw [desc_iff_of hx hu]
  have hs := sel_iff.1 hR
  ext z
  constructor
  · rintro ⟨hzA, B, hzB⟩
    by_cases e : B = A
    · subst e
      exact hu z hzB
    · have : z ∈ A ∩ sumCls (K \ ι A) := ⟨hzA, B, ⟨hs.2.2.1 z B hzB, e⟩, hs.2.1 z B hzB⟩
      rw [hd, Null_eq_empty] at this
      exact this.elim
  · rintro rfl
    exact ⟨hs.2.1 _ _ hx, A, hx⟩

/-- ✱83·62. \(\vdash:\mu\in \text{D}ʻʻ{\in}_{\Delta}ʻ\kappa.\supset.\mu\subset sʻ\kappa \quad[\text{*83·21.*37·63}]\) -/
theorem pm83_62 {K : Set (Set α)} {μ : Set α} :
    μ ∈ D ʻʻ sel memRel K → μ ⊆ sumCls K := by
  rintro ⟨R, hR, rfl⟩
  exact pm83_21 hR

/-- Lemma for ✱83·63–·65: the domain of `M ↾ κ`. -/
theorem dom_cres_sel {K L : Set (Set α)} {M : α → Set α → Prop}
    (hd : sumCls K ∩ sumCls L = Λ) (hM : M ∈ sel memRel (K ∪ L)) :
    dom (M ↾ K) = dom M ∩ sumCls K ∧ dom (M ↾ L) = dom M \ sumCls K := by
  have hs := sel_iff.1 hM
  have hd' : ∀ x, x ∈ sumCls K → x ∈ sumCls L → False := fun x h1 h2 => by
    have : x ∈ sumCls K ∩ sumCls L := ⟨h1, h2⟩
    rw [hd, Null_eq_empty] at this
    exact this
  constructor
  · ext x
    constructor
    · rintro ⟨B, hB, hBK⟩
      exact ⟨⟨B, hB⟩, B, hBK, hs.2.1 x B hB⟩
    · rintro ⟨⟨B, hB⟩, hK⟩
      refine ⟨B, hB, ?_⟩
      rcases hs.2.2.1 x B hB with h | h
      · exact h
      · exact (hd' x hK ⟨B, h, hs.2.1 x B hB⟩).elim
  · ext x
    constructor
    · rintro ⟨B, hB, hBL⟩
      exact ⟨⟨B, hB⟩, fun hK => hd' x hK ⟨B, hBL, hs.2.1 x B hB⟩⟩
    · rintro ⟨⟨B, hB⟩, hK⟩
      refine ⟨B, hB, ?_⟩
      rcases hs.2.2.1 x B hB with h | h
      · exact (hK ⟨B, h, hs.2.1 x B hB⟩).elim
      · exact h

/-- ✱83·63. \(\vdash:sʻ\kappa\cap sʻ\lambda=\Lambda.\mu\in \text{D}ʻʻ{\in}_{\Delta}ʻ(\kappa\cup \lambda).\supset.\mu\cap sʻ\kappa\in \text{D}ʻʻ{\in}_{\Delta}ʻ\kappa.\mu\cap sʻ\lambda\in \text{D}ʻʻ{\in}_{\Delta}ʻ\lambda\) -/
theorem pm83_63 {K L : Set (Set α)} {μ : Set α} :
    sumCls K ∩ sumCls L = Λ ∧ μ ∈ D ʻʻ sel memRel (K ∪ L) →
      μ ∩ sumCls K ∈ D ʻʻ sel memRel K ∧ μ ∩ sumCls L ∈ D ʻʻ sel memRel L := by
  rintro ⟨hd, M, hM, rfl⟩
  have hd' : sumCls L ∩ sumCls K = Λ := by rw [Set.inter_comm]; exact hd
  have hM' : M ∈ sel memRel (L ∪ K) := by rw [Set.union_comm]; exact hM
  exact ⟨⟨_, (pm80_62 hM).1, (dom_cres_sel hd hM).1.symm⟩,
    ⟨_, (pm80_62 hM).2, (dom_cres_sel hd' hM').1.symm⟩⟩

/-- ✱83·64. \[\begin{align}\vdash\colon\ldotp \kappa\cap &\lambda=\Lambda.\supset:\\ &\mu\in \text{D}ʻʻ{\in}_{\Delta}ʻ(\kappa\cup \lambda).\equiv.(\exists \rho,\sigma).\rho\in \text{D}ʻʻ{\in}_{\Delta}ʻ\kappa.\sigma\in \text{D}ʻʻ{\in}_{\Delta}ʻ\lambda.\mu=\rho\cup \sigma\end{align}\] -/
theorem pm83_64 {K L : Set (Set α)} {μ : Set α} :
    K ∩ L = Λ →
      (μ ∈ D ʻʻ sel memRel (K ∪ L) ↔
        ∃ ρ σ, (ρ ∈ D ʻʻ sel memRel K ∧ σ ∈ D ʻʻ sel memRel L) ∧ μ = ρ ∪ σ) := by
  intro h
  constructor
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨R, S, ⟨hR, hS⟩, rfl⟩ := (pm80_66 h).1 hM
    exact ⟨dom R, dom S, ⟨⟨R, hR, rfl⟩, ⟨S, hS, rfl⟩⟩, dom_rcup⟩
  · rintro ⟨ρ, σ, ⟨⟨R, hR, rfl⟩, ⟨S, hS, rfl⟩⟩, rfl⟩
    exact ⟨R ⊍ S, (pm80_66 h).2 ⟨R, S, ⟨hR, hS⟩, rfl⟩, dom_rcup.symm⟩

/-- ✱83·641. \[\begin{align}\vdash\colon\ldotp sʻ\kappa&\cap sʻ\lambda=\Lambda.\supset:\\ &\mu\in \text{D}ʻʻ{\in}_{\Delta}ʻ(\kappa\cup \lambda).\equiv.(\exists \rho,\sigma).\rho\in \text{D}ʻʻ{\in}_{\Delta}ʻ\kappa.\sigma\in \text{D}ʻʻ{\in}_{\Delta}ʻ\lambda.\mu=\rho\cup \sigma\end{align}\] -/
theorem pm83_641 {K L : Set (Set α)} {μ : Set α} :
    sumCls K ∩ sumCls L = Λ →
      (μ ∈ D ʻʻ sel memRel (K ∪ L) ↔
        ∃ ρ σ, (ρ ∈ D ʻʻ sel memRel K ∧ σ ∈ D ʻʻ sel memRel L) ∧ μ = ρ ∪ σ) := by
  intro hd
  constructor
  · rintro ⟨M, hM, rfl⟩
    have e := dom_cres_sel hd hM
    refine ⟨_, _, ⟨⟨_, (pm80_62 hM).1, rfl⟩, ⟨_, (pm80_62 hM).2, rfl⟩⟩, ?_⟩
    rw [e.1, e.2, Set.inter_union_sdiff]
  · rintro ⟨ρ, σ, ⟨⟨R, hR, rfl⟩, ⟨S, hS, rfl⟩⟩, rfl⟩
    refine ⟨_, pm80_651 ⟨hR, hS⟩, ?_⟩
    show _ = dom _
    rw [dom_rcup]
    congr 1
    ext x
    constructor
    · rintro ⟨B, hB⟩
      refine ⟨B, hB, (sel_iff.1 hS).2.2.1 x B hB, fun hBK => ?_⟩
      have : x ∈ sumCls K ∩ sumCls L :=
        ⟨⟨B, hBK, (sel_iff.1 hS).2.1 x B hB⟩, ⟨B, (sel_iff.1 hS).2.2.1 x B hB,
          (sel_iff.1 hS).2.1 x B hB⟩⟩
      rw [hd, Null_eq_empty] at this
      exact this
    · rintro ⟨B, hB, -⟩
      exact ⟨B, hB⟩

/-- ✱83·65. \[\begin{align}\vdash:sʻ\kappa\cap sʻ\lambda=\Lambda.\mu\in \text{D}ʻʻ{\in}_{\Delta}ʻ(\kappa\cup \lambda).&\supset.\\ &\mu-sʻ\kappa\in \text{D}ʻʻ{\in}_{\Delta}ʻ\lambda.\mu-sʻ\lambda\in \text{D}ʻʻ{\in}_{\Delta}ʻ\kappa\end{align}\] -/
theorem pm83_65 {K L : Set (Set α)} {μ : Set α} :
    sumCls K ∩ sumCls L = Λ ∧ μ ∈ D ʻʻ sel memRel (K ∪ L) →
      μ \ sumCls K ∈ D ʻʻ sel memRel L ∧ μ \ sumCls L ∈ D ʻʻ sel memRel K := by
  rintro ⟨hd, M, hM, rfl⟩
  have hd' : sumCls L ∩ sumCls K = Λ := by rw [Set.inter_comm]; exact hd
  have hM' : M ∈ sel memRel (L ∪ K) := by rw [Set.union_comm]; exact hM
  exact ⟨⟨_, (pm80_62 hM).2, (dom_cres_sel hd hM).2.symm⟩,
    ⟨_, (pm80_62 hM).1, (dom_cres_sel hd' hM').2.symm⟩⟩

/-- ✱83·66. \(\vdash:\exists !{\in}_{\Delta}ʻ\kappa.\supset.sʻ\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa=sʻ\kappa\) -/
theorem pm83_66 {K : Set (Set α)} :
    (sel memRel K).Nonempty → sumCls (D ʻʻ sel memRel K) = sumCls K := by
  rintro ⟨M, hM⟩
  apply Set.Subset.antisymm
  · rintro x ⟨μ, hμ, hx⟩
    exact pm83_62 hμ hx
  · rintro x ⟨A, hA, hx⟩
    obtain ⟨b, hb, -⟩ := sel_ex hM hA
    exact ⟨_, ⟨_, pm80_4 ⟨⟨⟨hM, hA⟩, hb⟩, hx⟩, rfl⟩, A, Or.inr ⟨rfl, rfl⟩⟩

/-- ✱83·7. \(\vdash.\text{D}ʻʻ{\in}_{\Delta}ʻ\iotaʻ\alpha=\iotaʻʻ\alpha \quad[\text{*83·4.*55·261}]\) -/
theorem pm83_7 {A : Set α} : D ʻʻ sel memRel (ι A) = iota ʻʻ A := by
  rw [pm83_4]
  ext μ
  constructor
  · rintro ⟨M, ⟨x, hx, hM⟩, rfl⟩
    rw [coupleR_apply] at hM
    subst hM
    refine ⟨x, hx, ?_⟩
    ext z
    exact ⟨fun ⟨_, hz, _⟩ => hz, fun hz => ⟨A, hz, rfl⟩⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x ↓ A, ⟨x, hx, rfl⟩, ?_⟩
    ext z
    exact ⟨fun hz => ⟨A, hz, rfl⟩, fun ⟨_, hz, _⟩ => hz⟩

/-- ✱83·71. \(\vdash.\text{D}ʻʻ{\in}_{\Delta}ʻ\iotaʻʻ\alpha=\iotaʻ\alpha.\text{D}ʻ\alpha\upharpoonleft \breve{\iota}=\alpha\) -/
theorem pm83_71 {A : Set α} :
    D ʻʻ sel memRel (iota ʻʻ A) = ι A ∧ dom (A ◁ iota˘) = A := by
  have e : dom (A ◁ iota˘) = A := by
    ext x
    exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨ι x, hx, rfl⟩⟩
  refine ⟨?_, e⟩
  rw [pm83_42.1]
  ext μ
  constructor
  · rintro ⟨M, hM, rfl⟩
    rw [mem_unitCls] at hM
    subst hM
    exact e
  · intro h
    rw [mem_unitCls] at h
    subst h
    exact ⟨_, rfl, e.symm⟩

/-- ✱83·72. \(\vdash:\kappa\subset 1.\supset.\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa=\iotaʻsʻ\kappa\) -/
theorem pm83_72 {K : Set (Set α)} : K ⊆ one → D ʻʻ sel memRel K = ι (sumCls K) := by
  intro hK
  rw [(pm83_43 hK).1]
  have e : dom (iota˘ ↾ K) = sumCls K := by
    ext x
    constructor
    · rintro ⟨B, rfl, hB⟩
      exact ⟨_, hB, rfl⟩
    · rintro ⟨B, hB, hx⟩
      obtain ⟨b, rfl⟩ := hK hB
      have : x = b := hx
      subst this
      exact ⟨_, rfl, hB⟩
  ext μ
  constructor
  · rintro ⟨M, hM, rfl⟩
    rw [mem_unitCls] at hM
    subst hM
    exact e
  · intro h
    rw [mem_unitCls] at h
    subst h
    exact ⟨_, rfl, e.symm⟩

/-- ✱83·73. \[\begin{align}\vdash:\kappa\cap \lambda=\Lambda.\lambda&\subset 1.\supset.\\ &\text{D}ʻʻ{\in}_{\Delta}ʻ(\kappa\cup \lambda)=\hat{\sigma}\{(\exists \rho).\rho\in \text{D}ʻʻ{\in}_{\Delta}ʻ\kappa.\sigma=\rho\cup sʻ\lambda\}\end{align}\] -/
theorem pm83_73 {K L : Set (Set α)} :
    K ∩ L = Λ ∧ L ⊆ one →
      D ʻʻ sel memRel (K ∪ L) = {σ | ∃ ρ, ρ ∈ D ʻʻ sel memRel K ∧ σ = ρ ∪ sumCls L} := by
  intro h
  have e : dom (iota˘ ↾ L) = sumCls L := by
    ext x
    constructor
    · rintro ⟨B, rfl, hB⟩
      exact ⟨_, hB, rfl⟩
    · rintro ⟨B, hB, hx⟩
      obtain ⟨b, rfl⟩ := h.2 hB
      have : x = b := hx
      subst this
      exact ⟨_, rfl, hB⟩
  rw [pm83_56 h]
  ext σ
  constructor
  · rintro ⟨M, ⟨R, hR, rfl⟩, rfl⟩
    exact ⟨dom R, ⟨R, hR, rfl⟩, by rw [dom_rcup, e]⟩
  · rintro ⟨ρ, ⟨R, hR, rfl⟩, rfl⟩
    exact ⟨_, ⟨R, hR, rfl⟩, show _ = dom _ by rw [dom_rcup, e]⟩

/-- ✱83·731. \(\vdash\colon\ldotp \lambda\subset 1.\supset:sʻ\kappa\cap sʻ\lambda=\Lambda.\supset.\kappa\cap \lambda=\Lambda\) -/
theorem pm83_731 {K L : Set (Set α)} :
    L ⊆ one → (sumCls K ∩ sumCls L = Λ → K ∩ L = Λ) := by
  intro hL hd
  rw [Null_eq_empty] at hd ⊢
  ext B
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hK, hLB⟩
  obtain ⟨b, rfl⟩ := hL hLB
  have : b ∈ sumCls K ∩ sumCls L := ⟨⟨_, hK, rfl⟩, ⟨_, hLB, rfl⟩⟩
  rw [hd] at this
  exact this

/-- ✱83·74. \(\vdash:sʻ\kappa\cap sʻ\lambda=\Lambda.\lambda\subset 1.\supset.\text{D}ʻʻ\in_{\Delta}ʻ(\kappa\cup \lambda)\text{ sm }\text{D}ʻʻ\in_{\Delta}ʻ\kappa\) -/
theorem pm83_74 {K L : Set (Set α)} :
    sumCls K ∩ sumCls L = Λ ∧ L ⊆ one →
      sm (D ʻʻ sel memRel (K ∪ L)) (D ʻʻ sel memRel K) := by
  rintro ⟨hd, hL⟩
  have hKL := pm83_731 hL hd
  rw [sm_iff]
  refine ⟨fun σ ρ => ρ ∈ D ʻʻ sel memRel K ∧ σ = ρ ∪ sumCls L, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_arrow_one_one]
    constructor
    · rintro σ σ' ρ ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
    · rintro σ ρ ρ' ⟨⟨hρ, rfl⟩, ⟨hρ', e⟩⟩
      have h1 := pm83_62 hρ
      have h2 := pm83_62 hρ'
      have hd' : ∀ x, x ∈ sumCls K → x ∈ sumCls L → False := fun x h1 h2 => by
        have : x ∈ sumCls K ∩ sumCls L := ⟨h1, h2⟩
        rw [hd, Null_eq_empty] at this
        exact this
      ext x
      constructor
      · intro hx
        have : x ∈ ρ' ∪ sumCls L := e ▸ Or.inl hx
        rcases this with h | h
        · exact h
        · exact (hd' x (h1 hx) h).elim
      · intro hx
        have : x ∈ ρ ∪ sumCls L := e.symm ▸ Or.inl hx
        rcases this with h | h
        · exact h
        · exact (hd' x (h2 hx) h).elim
  · rw [pm83_73 ⟨hKL, hL⟩]
    ext σ
    exact ⟨fun ⟨ρ, hρ, e⟩ => ⟨ρ, hρ, e⟩, fun ⟨ρ, hρ, e⟩ => ⟨ρ, hρ, e⟩⟩
  · ext ρ
    exact ⟨fun hρ => ⟨_, hρ, rfl⟩, fun ⟨_, hρ, _⟩ => hρ⟩

/-- ✱83·8. \(\vdash.\in_{\Delta}ʻ\kappa\subset .t_{10}ʻ\kappa.\in_{\Delta}ʻ\kappa\in tʻt_{10}ʻ\kappa\) -/
theorem pm83_8 {K : Set (Set α)} :
    sel memRel K ⊆ typ₁₀ K ∧ sel memRel K ∈ typ (typ₁₀ K) := by
  refine ⟨fun M _ => ?_, ?_⟩
  · rw [typ₁₀, typ_eq_univ]; trivial
  · rw [typ_eq_univ]; trivial

/-- ✱83·81. \(\vdash.\text{D}ʻʻ\in_{\Delta}ʻ\kappa\subset t_{0}ʻ\kappa.Dʻʻ\in_{\Delta}ʻ\kappa\in tʻ\kappa\) -/
theorem pm83_81 {K : Set (Set α)} :
    D ʻʻ sel memRel K ⊆ typ₀ K ∧ D ʻʻ sel memRel K ∈ typ K := by
  refine ⟨fun μ _ => ?_, ?_⟩
  · rw [typ₀_eq_univ]; trivial
  · rw [typ_eq_univ]; trivial

/-- ✱83·9. \(\vdash.\exists !\in_{\Delta}ʻ\Lambda \quad[\text{*83·15}]\) -/
theorem pm83_9 : (sel memRel (Λ : Set (Set α))).Nonempty := by
  rw [pm83_15]
  exact ⟨_, rfl⟩

/-- ✱83·901. \(\vdash:\exists !\in_{\Delta}ʻ\iotaʻ\alpha.\equiv.\exists !\alpha \quad[\text{*80·46.*62·2}]\) -/
theorem pm83_901 {A : Set α} : (sel memRel (ι A)).Nonempty ↔ A.Nonempty := pm80_46.1

/-- ✱83·902. \(\vdash:\exists !\in_{\Delta}ʻ(\kappa\cup \lambda).\equiv.\exists !\in_{\Delta}ʻ\kappa.\exists !\in_{\Delta}ʻ\lambda \quad[\text{*80·69}]\) -/
theorem pm83_902 {K L : Set (Set α)} :
    (sel memRel (K ∪ L)).Nonempty ↔ (sel memRel K).Nonempty ∧ (sel memRel L).Nonempty :=
  pm80_69

/-- ✱83·903. \(\vdash:\exists !\in_{\Delta}ʻ(\iotaʻ\alpha\cup \iotaʻ\beta).\equiv.\exists !\alpha.\exists !\beta \quad[\text{*83·901·902}]\) -/
theorem pm83_903 {A B : Set α} :
    (sel memRel (ι A ∪ ι B)).Nonempty ↔ A.Nonempty ∧ B.Nonempty := by
  rw [pm83_902, pm83_901, pm83_901]

/-- ✱83·904. \(\vdash:\exists !\in_{\Delta}ʻ(\kappa\cup \iotaʻ\beta).\equiv.\exists !\in_{\Delta}ʻ\kappa.\exists !\beta \quad[\text{*83·901·902}]\) -/
theorem pm83_904 {K : Set (Set α)} {B : Set α} :
    (sel memRel (K ∪ ι B)).Nonempty ↔ (sel memRel K).Nonempty ∧ B.Nonempty := by
  rw [pm83_902, pm83_901]

/-!
## [✱84] Classes of mutually exclusive classes

*(Vol. 1, p. 540)*

> *Summary of* *84.
>
> A class \(\kappa\) of mutually exclusive classes is one such that, if \(\alpha\) and \(\beta\) are two different members of \(\kappa\), \(\alpha\) and \(\beta\) have no common members; *i.e.* it is a class composed of non-overlapping classes. Classes of mutually exclusive classes have many important properties. They are important in cardinal arithmetic, among other reasons, because if \(\kappa\) is a class of mutually exclusive classes, the cardinal number of \(sʻ\kappa\) is the sum of the cardinal numbers of the members of \(\kappa\). Also if \(\kappa\) is a class of mutually exclusive classes, the number of selected classes of \(\kappa\) (*i.e.* \(\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa\)) is the same as the number of selective relations (*i.e.* \({\in}_{\Delta}ʻ\kappa\))
>
> "\(\kappa\) is a class of mutually exclusive classes" is written "\(\kappa \in \text{Cls}^2 ~ \text{excl}\)."
>
> An important case is when no member of \(\kappa\) is null; in this case we write \[ \kappa \in \text{Cls} ~ \text{ex}^2 ~ \text{excl}\text{.} \]
>
> …

**Lean reading.** `Cls² excl` is `Cls2excl`, `Cl excl'γ` is `clExcl G` (its value; the relation `Cl
excl` always has one), and `Cls ex² excl` is `ClsEx2excl`; the lemma `mem_Cls2excl` gives the form
of ✱84·11. The e-text prints `Cls² excl` for `Cls ex² excl` in the definiendum of ✱84·03, on the
left of ✱84·13–·135, in the hypothesis of ✱84·35 and in the conclusions of ✱84·5 and ✱84·52: these are read
with `Cls ex² excl` (PM's proofs and the Summary show it, and the printed forms are false or idle).
`1(Cls)` of ✱84·21 is `one` at type `Set (Set (Set α))`, and `Λ ∩ Cls` of ✱84·2 is the null class of
classes. `R'''κ` is `R ʻʻʻ K`, `R⃗''κ` is `Rfwd R ʻʻ K`, `P_Δ''κ` is `selRel P ʻʻ K`. ✱84·3–·422
follow from ✱81 by ✱84·14, as in PM. ✱84·422 prints `∈_Δ'α` for `∈_Δ'κ`.

**Status.** proved (all propositions; ✱84·01, ✱84·02, ✱84·03 definition; ✱84·13, ✱84·131, ✱84·132,
✱84·133, ✱84·134, ✱84·135, ✱84·21, ✱84·35, ✱84·422, ✱84·5, ✱84·52 proved (reading), see their
docstrings).
-/

/-- `κ ∈ Cls² excl` in the form of ✱84·11: classes of `κ` with a common member are identical. -/
theorem mem_Cls2excl {K : Set (Set α)} :
    K ∈ Cls2excl ↔ ∀ A B x, A ∈ K → B ∈ K → x ∈ A → x ∈ B → A = B := by
  constructor
  · intro h A B x hA hB hxA hxB
    by_contra hne
    have : x ∈ A ∩ B := ⟨hxA, hxB⟩
    rw [h A B ⟨⟨hA, hB⟩, hne⟩, Null_eq_empty] at this
    exact this
  · rintro h A B ⟨⟨hA, hB⟩, hne⟩
    rw [Null_eq_empty]
    ext x
    exact ⟨fun ⟨h1, h2⟩ => hne (h A B x hA hB h1 h2), False.elim⟩

/-- `Λ ∼∈ κ . ≡ : α ∈ κ . ⊃_α . ∃!α` (✱24·63). -/
theorem null_not_mem_iff {K : Set (Set α)} : Λ ∉ K ↔ ∀ A, A ∈ K → A.Nonempty := by
  constructor
  · intro h A hA
    by_contra hc
    apply h
    rw [Null_eq_empty, ← Set.not_nonempty_iff_eq_empty.1 hc]
    exact hA
  · intro h hK
    obtain ⟨x, hx⟩ := h _ hK
    rw [Null_eq_empty] at hx
    exact hx

theorem inter_eq_null_iff {A B : Set α} : A ∩ B = Λ ↔ ∀ x, x ∈ A → x ∈ B → False := by
  rw [Null_eq_empty]
  constructor
  · intro h x hA hB
    have : x ∈ A ∩ B := ⟨hA, hB⟩
    rw [h] at this
    exact this
  · intro h
    ext x
    exact ⟨fun ⟨hA, hB⟩ => h x hA hB, False.elim⟩

theorem mem_ClsEx2excl {K : Set (Set α)} :
    K ∈ ClsEx2excl ↔ K ∈ Cls2excl ∧ Λ ∉ K := Iff.rfl

/-- ✱84·01 (Df). \(\text{Cls}^2\, \text{excl}=\hat{\kappa}(\alpha,\beta\in \kappa.\alpha \neq \beta.\supset_{\alpha,\beta}.\alpha\cap \beta=\Lambda) \quad\text{Df}\) -/
theorem pm84_01 :
    (Cls2excl : Set (Set (Set α))) = {K | ∀ A B, (A ∈ K ∧ B ∈ K) ∧ A ≠ B → A ∩ B = Λ} := rfl

/-- ✱84·02 (Df). \(\text{Cl excl}ʻ\gamma=\text{Cls}^2\, \text{excl}\cap \text{Cl}ʻ\gamma \quad\text{Df}\) -/
theorem pm84_02 {G : Set (Set α)} : clExcl G = Cls2excl ∩ cl G := rfl

/-- ✱84·03 (Df). \(\text{Cls}^2\, \text{excl}=\text{Cls}^2\, \text{excl}-\overleftarrow{\in}ʻ\Lambda \quad\text{Df}\)

**Status.** definition: the e-text prints the definiendum as `Cls² excl`; PM has `Cls ex² excl =
Cls² excl − ∈⃖'Λ Df` (Summary of ✱84; ✱84·13). -/
theorem pm84_03 : (ClsEx2excl : Set (Set (Set α))) = Cls2excl \ rels memRel Λ := rfl

/-- ✱84·1. \[\begin{align}&\vdash\colon\ldotp \kappa\in \text{Cls}^2\, \text{excl}.\equiv:\alpha,\beta\in \kappa.\alpha \neq \beta.\supset_{\alpha,\beta}.\alpha\cap \beta=\Lambda\\ &[\text{*20·3.(*84·01)}]\end{align}\] -/
theorem pm84_1 {K : Set (Set α)} :
    K ∈ Cls2excl ↔ ∀ A B, (A ∈ K ∧ B ∈ K) ∧ A ≠ B → A ∩ B = Λ := Iff.rfl

/-- ✱84·11. \[\begin{align}&\vdash\colon\ldotp \kappa\in \text{Cls}^2\,\text{excl}.\equiv:\alpha,\,\beta\in \kappa.\exists !\alpha\cap \beta.\supset_{\alpha,\beta}.\alpha=\beta\\ &[\text{*84·1.Transp}]\end{align}\] -/
theorem pm84_11 {K : Set (Set α)} :
    K ∈ Cls2excl ↔ ∀ A B, (A ∈ K ∧ B ∈ K) ∧ (A ∩ B).Nonempty → A = B := by
  rw [mem_Cls2excl]
  constructor
  · rintro h A B ⟨⟨hA, hB⟩, x, hxA, hxB⟩
    exact h A B x hA hB hxA hxB
  · intro h A B x hA hB hxA hxB
    exact h A B ⟨⟨hA, hB⟩, x, hxA, hxB⟩

/-- ✱84·12. \[\begin{align}\vdash\colon\ldotp \kappa\in \text{Cl excl}ʻ\gamma.&\equiv:\alpha,\beta\in \kappa.\alpha \neq \beta.\supset_{\alpha,\beta}.\alpha\cap \beta=\Lambda:\kappa\subset \gamma:\equiv:\\ &\kappa\in \text{Cls}^2\,\text{excl}.\kappa\subset \gamma [\text{*20·3.(*84·02).*22·33.*84·1}]\end{align}\] -/
theorem pm84_12 {K G : Set (Set α)} :
    (K ∈ clExcl G ↔ (∀ A B, (A ∈ K ∧ B ∈ K) ∧ A ≠ B → A ∩ B = Λ) ∧ K ⊆ G) ∧
      ((∀ A B, (A ∈ K ∧ B ∈ K) ∧ A ≠ B → A ∩ B = Λ) ∧ K ⊆ G ↔ K ∈ Cls2excl ∧ K ⊆ G) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ✱84·121. \[\begin{align}&\vdash\colon\ldotp \kappa\in \text{Cl excl}ʻ\gamma.\equiv:\alpha,\beta\in \kappa.\exists !\alpha\cap \beta.\supset_{\alpha,\beta}.\alpha=\beta:\kappa\subset \gamma\\ &[\text{*20·3.(*84·02).*22·33.*84·11}]\end{align}\] -/
theorem pm84_121 {K G : Set (Set α)} :
    K ∈ clExcl G ↔ (∀ A B, (A ∈ K ∧ B ∈ K) ∧ (A ∩ B).Nonempty → A = B) ∧ K ⊆ G := by
  rw [← pm84_11]
  exact Iff.rfl

/-- ✱84·13. \(\vdash:\kappa\in \text{Cls}^2\,\text{excl}.\equiv.\kappa\in \text{Cls}^2\,\text{excl}.\Lambda{\sim}\in \kappa\)

**Status.** proved (reading): transcription error: the e-text prints `Cls² excl` for `Cls ex² excl`
on the left (PM's proof uses (✱84·03); Summary of ✱84). As printed the proposition would be false
(`κ = ι'Λ`). -/
theorem pm84_13 {K : Set (Set α)} : K ∈ ClsEx2excl ↔ K ∈ Cls2excl ∧ Λ ∉ K := Iff.rfl

/-- ✱84·131. \[\begin{align}&\vdash\colon\ldotp \kappa\in \text{Cls}^2\,\text{excl}.\equiv:\alpha,\,\beta\in \kappa.\alpha \neq\beta.\supset_{\alpha,\beta}.\alpha\cap \beta=\Lambda:\Lambda{\sim}\in \kappa\\ &[\text{*84·13·1}]\end{align}\]

**Status.** proved (reading): transcription error `Cls² excl` for `Cls ex² excl` on the left, as in
✱84·13 (which it cites). -/
theorem pm84_131 {K : Set (Set α)} :
    K ∈ ClsEx2excl ↔ (∀ A B, (A ∈ K ∧ B ∈ K) ∧ A ≠ B → A ∩ B = Λ) ∧ Λ ∉ K := Iff.rfl

/-- ✱84·132. \[\begin{align}&\vdash\colon\ldotp \kappa\in \text{Cls}^2\,\text{excl}.\equiv:\alpha,\,\beta\in \kappa.\exists !\alpha\cap \beta.\supset_{\alpha,\beta}.\alpha=\beta:\Lambda{\sim}\in \kappa\\ &[\text{*84·13·11}]\end{align}\]

**Status.** proved (reading): transcription error `Cls² excl` for `Cls ex² excl` on the left, as in
✱84·13 (which it cites). -/
theorem pm84_132 {K : Set (Set α)} :
    K ∈ ClsEx2excl ↔ (∀ A B, (A ∈ K ∧ B ∈ K) ∧ (A ∩ B).Nonempty → A = B) ∧ Λ ∉ K := by
  rw [mem_ClsEx2excl, pm84_11]

/-- ✱84·133. \[\begin{align}&\vdash\colon\ldotp \kappa\in \text{Cls}^2\,\text{excl}.\equiv:\alpha,\,\beta\in \kappa.\exists !\alpha\cap \beta.\supset_{\alpha,\beta}.\alpha=\beta:\alpha\in \kappa.\supset_{\alpha}.\exists !\alpha\\ &[\text{*84·132.*24·63}]\end{align}\]

**Status.** proved (reading): transcription error `Cls² excl` for `Cls ex² excl` on the left, as in
✱84·13 (✱84·132 is cited). -/
theorem pm84_133 {K : Set (Set α)} :
    K ∈ ClsEx2excl ↔
      (∀ A B, (A ∈ K ∧ B ∈ K) ∧ (A ∩ B).Nonempty → A = B) ∧ ∀ A, A ∈ K → A.Nonempty := by
  rw [pm84_132, null_not_mem_iff]

/-- ✱84·134. \(\vdash\colon\colon \kappa\in \text{Cls}^2\,\text{excl}.\equiv\colon\ldotp \alpha,\,\beta\in \kappa.\supset_{\alpha,\beta}:\exists !\alpha.\exists !\beta:\exists !\alpha\cap \beta.\supset.\alpha=\beta\)

**Status.** proved (reading): transcription error `Cls² excl` for `Cls ex² excl` on the left, as in
✱84·13 (with `Cls² excl` the conjunct `∃!α . ∃!β` would fail for `κ = ι'Λ`). -/
theorem pm84_134 {K : Set (Set α)} :
    K ∈ ClsEx2excl ↔
      ∀ A B, A ∈ K ∧ B ∈ K → (A.Nonempty ∧ B.Nonempty) ∧ ((A ∩ B).Nonempty → A = B) := by
  rw [pm84_133]
  constructor
  · rintro ⟨h1, h2⟩ A B ⟨hA, hB⟩
    exact ⟨⟨h2 A hA, h2 B hB⟩, fun h => h1 A B ⟨⟨hA, hB⟩, h⟩⟩
  · intro h
    exact ⟨fun A B ⟨hAB, hn⟩ => (h A B hAB).2 hn, fun A hA => (h A A ⟨hA, hA⟩).1.1⟩

/-- ✱84·135. \(\vdash\colon\colon \kappa\in \text{Cls}^2\,\text{excl}.\equiv\colon\ldotp \alpha,\beta\in \kappa.\supset_{\alpha,\beta}:\exists !\alpha\cap \beta.\equiv.\alpha=\beta\)

**Status.** proved (reading): transcription error `Cls² excl` for `Cls ex² excl` on the left, as in
✱84·13 (with `Cls² excl` it would fail for `κ = ι'Λ`, since `α = α` but `∼∃!Λ ∩ Λ`). -/
theorem pm84_135 {K : Set (Set α)} :
    K ∈ ClsEx2excl ↔ ∀ A B, A ∈ K ∧ B ∈ K → ((A ∩ B).Nonempty ↔ A = B) := by
  rw [pm84_134]
  constructor
  · intro h A B hAB
    refine ⟨(h A B hAB).2, ?_⟩
    rintro rfl
    obtain ⟨x, hx⟩ := (h A A ⟨hAB.1, hAB.1⟩).1.1
    exact ⟨x, hx, hx⟩
  · intro h A B hAB
    refine ⟨⟨?_, ?_⟩, (h A B hAB).1⟩
    · obtain ⟨x, hx, -⟩ := (h A A ⟨hAB.1, hAB.1⟩).2 rfl
      exact ⟨x, hx⟩
    · obtain ⟨x, hx, -⟩ := (h B B ⟨hAB.2, hAB.2⟩).2 rfl
      exact ⟨x, hx⟩

/-- ✱84·14. \(\vdash:\kappa\in \text{Cls}^2\,\text{excl}.\equiv.\in \upharpoonright \kappa\in \text{Cls}\rightarrow 1\) -/
theorem pm84_14 {K : Set (Set α)} : K ∈ Cls2excl ↔ memRel ↾ K ∈ arrow Cls one := by
  rw [mem_arrow_Cls_one, mem_Cls2excl]
  constructor
  · rintro h x A B ⟨⟨hxA, hA⟩, ⟨hxB, hB⟩⟩
    exact h A B x hA hB hxA hxB
  · intro h A B x hA hB hxA hxB
    exact h x A B ⟨⟨hxA, hA⟩, ⟨hxB, hB⟩⟩

/-- ✱84·2. \(\vdash.\Lambda\cap \text{Cls}\in \text{Cls}\,\text{ex}^{2}\,\text{excl}\) -/
theorem pm84_2 : (Λ ∩ Cls : Set (Set α)) ∈ ClsEx2excl := by
  rw [mem_ClsEx2excl, mem_Cls2excl, null_not_mem_iff]
  simp only [Null_eq_empty, Set.empty_inter, Set.mem_empty_iff_false, IsEmpty.forall_iff,
    implies_true, and_self]

/-- ✱84·21. \(\vdash.1(\text{Cls})\subset \text{Cls}^{2}\,\text{excl}\)

**Status.** proved (reading): `1(Cls)` (✱65·02) is `1` with its members determined as classes of
classes, i.e. (PM's note) the class of unit classes whose members are classes; in Lean this typing
is the explicit type `Set (Set (Set α))` of `one`. -/
theorem pm84_21 : (one : Set (Set (Set α))) ⊆ Cls2excl := by
  rintro K ⟨A, rfl⟩
  rw [mem_Cls2excl]
  intro B C x hB hC _ _
  exact (hB : B = A).trans (hC : C = A).symm

/-- ✱84·22. \(\vdash.1\in \text{Cls ex}^{2}\,\text{excl}\) -/
theorem pm84_22 : (one : Set (Set α)) ∈ ClsEx2excl := by
  rw [mem_ClsEx2excl, mem_Cls2excl, null_not_mem_iff]
  refine ⟨?_, ?_⟩
  · rintro A B x ⟨a, rfl⟩ ⟨b, rfl⟩ hxA hxB
    have e1 : x = a := hxA
    have e2 : x = b := hxB
    rw [← e1, ← e2]
  · rintro A ⟨a, rfl⟩
    exact ⟨a, rfl⟩

/-- ✱84·23. \(\vdash.\iotaʻ\alpha\in \text{Cls}^{2}\,\text{excl} \quad[\text{*84·21.*52·22}]\) -/
theorem pm84_23 {A : Set α} : ι A ∈ (Cls2excl : Set (Set (Set α))) := pm84_21 ⟨A, rfl⟩

/-- ✱84·24. \(\vdash:\exists !\alpha.\supset.\iotaʻ\alpha\in \text{Cls}\,\text{ex}^{2}\,\text{excl}\) -/
theorem pm84_24 {A : Set α} : A.Nonempty → ι A ∈ (ClsEx2excl : Set (Set (Set α))) := by
  intro h
  refine ⟨pm84_23, fun hn => (null_not_mem_iff (K := ι A)).2 ?_ hn⟩
  rintro B rfl
  exact h

/-- ✱84·241. \(\vdash.\iotaʻʻ\alpha\in \text{Cls}\,\text{ex}^{2}\,\text{excl}\) -/
theorem pm84_241 {A : Set α} : iota ʻʻ A ∈ ClsEx2excl := by
  rw [mem_ClsEx2excl, mem_Cls2excl, null_not_mem_iff]
  refine ⟨?_, ?_⟩
  · rintro B C x ⟨a, -, rfl⟩ ⟨b, -, rfl⟩ hxA hxB
    have e1 : x = a := hxA
    have e2 : x = b := hxB
    rw [← e1, ← e2]
  · rintro B ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩

/-- ✱84·242. \(\vdash:\kappa\subset 1.\supset.\kappa\in \text{Cls ex}^{2}\,\text{excl} \quad[\text{*52·46.*84·135}]\) -/
theorem pm84_242 {K : Set (Set α)} : K ⊆ one → K ∈ ClsEx2excl := by
  intro hK
  have h := pm84_22 (α := α)
  rw [mem_ClsEx2excl, mem_Cls2excl, null_not_mem_iff] at h ⊢
  exact ⟨fun A B x hA hB => h.1 A B x (hK hA) (hK hB), fun A hA => h.2 A (hK hA)⟩

/-- ✱84·25. \(\vdash:\kappa\in \text{Cls}^{2}\,\text{excl}.\lambda\subset \kappa.\supset.\lambda\in \text{Cls}^{2}\,\text{excl}\) -/
theorem pm84_25 {K L : Set (Set α)} : K ∈ Cls2excl ∧ L ⊆ K → L ∈ Cls2excl := by
  rintro ⟨h, hL⟩
  rw [mem_Cls2excl] at h ⊢
  exact fun A B x hA hB => h A B x (hL hA) (hL hB)

/-- ✱84·26. \(\vdash:\kappa\in \text{Cls ex}^{2}\,\text{excl}.\lambda\subset \kappa.\supset.\lambda\in \text{Cls ex}^{2}\,\text{excl}\) -/
theorem pm84_26 {K L : Set (Set α)} : K ∈ ClsEx2excl ∧ L ⊆ K → L ∈ ClsEx2excl := by
  rintro ⟨⟨h, hn⟩, hL⟩
  exact ⟨pm84_25 ⟨h, hL⟩, fun h' => hn (hL h')⟩

/-- ✱84·28. \(\vdash:\kappa\in \text{Cl excl}ʻ\gamma.\lambda\subset \kappa.\gamma\subset \delta.\supset.\lambda\in \text{Cl excl}ʻ\delta\) -/
theorem pm84_28 {K L G G' : Set (Set α)} :
    (K ∈ clExcl G ∧ L ⊆ K) ∧ G ⊆ G' → L ∈ clExcl G' := by
  rintro ⟨⟨⟨h, hKG⟩, hL⟩, hG⟩
  exact ⟨pm84_25 ⟨h, hL⟩, fun A hA => hG (hKG (hL hA))⟩

/-- ✱84·3. \(\vdash:\kappa\in \text{Cls}^{2}\,\text{excl}.\supset.{\in}_{\Delta}ʻ\kappa\subset 1\rightarrow 1 \quad[\text{*84·14.*81·1}]\) -/
theorem pm84_3 {K : Set (Set α)} : K ∈ Cls2excl → sel memRel K ⊆ arrow one one :=
  fun h => pm81_1 (pm84_14.1 h)

/-- ✱84·31. \(\vdash:\kappa\in \text{Cls}^{2}\,\text{excl}.R\in \in _{\Delta}ʻ\kappa.x\in \text{D}ʻR.\supset.\text{E}!\breve{R}ʻx \quad[\text{*84·14.*81·11}]\) -/
theorem pm84_31 {K : Set (Set α)} {R : α → Set α → Prop} {x : α} :
    (K ∈ Cls2excl ∧ R ∈ sel memRel K) ∧ x ∈ dom R → EDesc R˘ x :=
  fun ⟨⟨h, hR⟩, hx⟩ => (pm81_11 ⟨⟨pm84_14.1 h, hR⟩, hx⟩).1

/-- ✱84·32. \[\begin{align}&\vdash:\kappa\in \text{Cls}^{2}\,\text{excl}.R\in {\in} _{\Delta}ʻ\kappa.x\in \text{D}ʻR.\supset.x\in \breve{R}ʻx.\breve{R}ʻx\in \kappa\\ &[\text{*84·14.*81·11.*35·101}]\end{align}\] -/
theorem pm84_32 {K : Set (Set α)} {R : α → Set α → Prop} {x : α} :
    (K ∈ Cls2excl ∧ R ∈ sel memRel K) ∧ x ∈ dom R →
      Desc R˘ x (fun A => x ∈ A) ∧ Desc R˘ x (fun A => A ∈ K) := by
  rintro ⟨⟨h, hR⟩, hx⟩
  have := desc_iff.1 (pm81_11 ⟨⟨pm84_14.1 h, hR⟩, hx⟩).2
  exact ⟨desc_iff.2 ⟨this.1, fun A hA => (this.2 A hA).1⟩,
    desc_iff.2 ⟨this.1, fun A hA => (this.2 A hA).2⟩⟩

/-- ✱84·33. \[\begin{align}&\vdash:\kappa\in \text{Cls}^{2}\,\text{excl}.R\in {\in}_{\Delta}ʻ\kappa.x\in \text{D}ʻR.\supset.\breve{R}ʻx=(℩\alpha)(\alpha\in \kappa.x\in \alpha)=(\kappa\upharpoonleft \breve{\in})ʻx\\ &[\text{*84·14.*81·12}]\end{align}\] -/
theorem pm84_33 {K : Set (Set α)} {R : α → Set α → Prop} {x : α} :
    (K ∈ Cls2excl ∧ R ∈ sel memRel K) ∧ x ∈ dom R →
      Desc R˘ x (fun a => TheIs (fun A => A ∈ K ∧ x ∈ A) (fun b => a = b)) ∧
        TheIs (fun A => A ∈ K ∧ x ∈ A) (fun b => Desc (K ◁ memRel˘) x (fun c => b = c)) :=
  fun ⟨⟨h, hR⟩, hx⟩ => pm81_12 ⟨⟨pm84_14.1 h, hR⟩, hx⟩

/-- ✱84·34. \[\begin{align}&\vdash\colon\ldotp \kappa\in \text{Cls}^{2}\,\text{excl}.R\in {\in}_{\Delta}ʻ\kappa.\supset:xR\alpha.\equiv.x\in \alpha.x\in \text{D}ʻR.\alpha\in \kappa\\ &[\text{*81·13.*84·14}]\end{align}\] -/
theorem pm84_34 {K : Set (Set α)} {R : α → Set α → Prop} {x : α} {A : Set α} :
    K ∈ Cls2excl ∧ R ∈ sel memRel K → (R x A ↔ (x ∈ A ∧ x ∈ dom R) ∧ A ∈ K) := by
  rintro ⟨h, hR⟩
  rw [pm81_13 ⟨pm84_14.1 h, hR⟩]
  exact and_congr_left' and_comm

/-- ✱84·341. \[\begin{align}&\vdash:\kappa\in \text{Cls}^{2}\,\text{excl}.R\in {\in}_{\Delta}ʻ\kappa.\supset.R=\text{D}ʻR\upharpoonleft \in \upharpoonright \kappa=\in \dot{\cap}\text{D}ʻR\uparrow \kappa\\ &[\text{*81·14.*84·14}]\end{align}\] -/
theorem pm84_341 {K : Set (Set α)} {R : α → Set α → Prop} :
    K ∈ Cls2excl ∧ R ∈ sel memRel K →
      R = dom R ◁ memRel ↾ K ∧ dom R ◁ memRel ↾ K = memRel ⩀ cross (dom R) K :=
  fun ⟨h, hR⟩ => pm81_14 ⟨pm84_14.1 h, hR⟩

/-- ✱84·342. \[\begin{align}&\vdash:\kappa\in \text{Cls}^{2}\,\text{excl}. R\in {\in}_{\Delta}ʻ\kappa.\alpha\in \kappa.\supset.\iotaʻRʻ\alpha=\alpha\cap \text{D}ʻR\\ &[\text{*81·15.*84·14.*62·2}]\end{align}\] -/
theorem pm84_342 {K : Set (Set α)} {R : α → Set α → Prop} {A : Set α} :
    (K ∈ Cls2excl ∧ R ∈ sel memRel K) ∧ A ∈ K → Desc R A (fun x => ι x = A ∩ dom R) := by
  rintro ⟨⟨h, hR⟩, hA⟩
  have := pm81_15 ⟨⟨pm84_14.1 h, hR⟩, hA⟩
  rw [desc_iff] at this ⊢
  refine ⟨this.1, fun x hx => ?_⟩
  rw [this.2 x hx, Set.inter_comm]
  rfl

/-- ✱84·35. \(\vdash\colon\ldotp \kappa\in \text{Cls}^{2}\,\text{excl}.\supset:R\in {\in}_{\Delta}ʻ\kappa.\equiv.R\in 1\rightarrow 1.R\unicode{x2abd}\in \upharpoonright \kappa.\text{ᗡ}ʻR=\text{ᗡ}ʻ\in \upharpoonright \kappa\)

**Status.** proved (reading): transcription error `Cls² excl` for `Cls ex² excl` in the hypothesis
(PM's proof begins `✱84·13 . ⊃ ⊢ : Hp . ⊃ . Λ ∼∈ κ`); with `Cls² excl` it fails for `κ = ι'Λ`, `R =
Λ̇`. -/
theorem pm84_35 {K : Set (Set α)} {R : α → Set α → Prop} :
    K ∈ ClsEx2excl →
      (R ∈ sel memRel K ↔ (R ∈ arrow one one ∧ R ⪽ memRel ↾ K) ∧ codom R = codom (memRel ↾ K)) := by
  rintro ⟨h, hn'⟩
  have hn : Λ ∉ K := hn'
  rw [null_not_mem_iff] at hn
  have hc : codom (memRel ↾ K) = K := by
    ext A
    constructor
    · rintro ⟨x, -, hA⟩; exact hA
    · intro hA
      obtain ⟨x, hx⟩ := hn A hA
      exact ⟨x, hx, hA⟩
  rw [hc]
  constructor
  · intro hR
    exact ⟨⟨pm84_3 h hR, pm80_291 hR⟩, (mem_sel_iff.1 hR).2⟩
  · rintro ⟨⟨h11, hsub⟩, rfl⟩
    rw [mem_sel_iff]
    refine ⟨⟨?_, fun x A hxA => (hsub x A hxA).1⟩, rfl⟩
    rw [mem_arrow_one_one] at h11
    rw [mem_arrow_one_Cls]
    exact h11.1

/-- ✱84·37. \(\vdash:\kappa\in \text{Cls}^{2}\,\text{excl}.\exists !{\in}_{\Delta}ʻ\kappa.\supset.\kappa\in \text{Cls ex}^{2}\,\text{excl} \quad[\text{*83·1.*84·13}]\) -/
theorem pm84_37 {K : Set (Set α)} :
    K ∈ Cls2excl ∧ (sel memRel K).Nonempty → K ∈ ClsEx2excl :=
  fun ⟨h, hs⟩ => ⟨h, pm83_1 hs⟩

/-- ✱84·4. \(\vdash\colon\ldotp \kappa\in \text{Cls}^{2}\,\text{excl}.R,\,S\in {\in}_{\Delta}ʻ\kappa.\supset:\text{D}ʻR=\text{D}ʻS.\equiv.R=S \quad[\text{*81·2.*84·14}]\) -/
theorem pm84_4 {K : Set (Set α)} {R S : α → Set α → Prop} :
    K ∈ Cls2excl ∧ (R ∈ sel memRel K ∧ S ∈ sel memRel K) → (dom R = dom S ↔ R = S) :=
  fun ⟨h, hRS⟩ => pm81_2 ⟨pm84_14.1 h, hRS⟩

/-- ✱84·41. \(\vdash:\kappa\in \text{Cls}^{2}\,\text{excl}.\supset.\text{D}\upharpoonright {\in}_{\Delta}ʻ\kappa\in 1\rightarrow 1.\text{D}ʻʻ\in _{\Delta}ʻ\kappa\text{ sm }{\in}_{\Delta}ʻ\kappa \quad[\text{*81·21.*84·14}]\) -/
theorem pm84_41 {K : Set (Set α)} :
    K ∈ Cls2excl → D ↾ sel memRel K ∈ arrow one one ∧ sm (D ʻʻ sel memRel K) (sel memRel K) :=
  fun h => pm81_21 (pm84_14.1 h)

/-- ✱84·411. \(\vdash\colon\ldotp \alpha\in \kappa.\supset_{\alpha}.\mu\cap \alpha\in 1:\mu\subset sʻ\kappa:\supset.\mu\in \text{D}ʻʻ{\in}_{\Delta}ʻ\kappa \quad[\text{*81·212.*62·2·3}]\) -/
theorem pm84_411 {K : Set (Set α)} {μ : Set α} :
    (∀ A, A ∈ K → μ ∩ A ∈ one) ∧ μ ⊆ sumCls K → μ ∈ D ʻʻ sel memRel K :=
  fun h => (pm81_212 h).1

/-- ✱84·412. \[\begin{align}&\vdash:\kappa\in \text{Cls}^{2}\,\text{excl}.\supset.\text{D}ʻʻ{\in}_{\Delta}ʻ\kappa=\hat{\mu}\{\alpha\in \kappa.\supset_{\alpha}.\mu\cap \alpha\in 1:\mu\subset sʻ\kappa\}\\ &[\text{*81·22.*84·14.*62·2·3}]\end{align}\] -/
theorem pm84_412 {K : Set (Set α)} :
    K ∈ Cls2excl →
      D ʻʻ sel memRel K = {μ | (∀ A, A ∈ K → μ ∩ A ∈ one) ∧ μ ⊆ sumCls K} :=
  fun h => pm81_22 (pm84_14.1 h)

/-- ✱84·42. \[\begin{align}&\vdash:\kappa\in \text{Cls}^{2}\,\text{excl}.\alpha\in \kappa.\mu\in \text{D}ʻʻ{\in}_{\Delta}ʻ\kappa.\supset.\mu-\alpha\in \text{D}ʻʻ{\in}_{\Delta}ʻ(\kappa-\iotaʻ\alpha)\\ &[\text{*81·24.*84·14.*62·2}]\end{align}\] -/
theorem pm84_42 {K : Set (Set α)} {A μ : Set α} :
    (K ∈ Cls2excl ∧ A ∈ K) ∧ μ ∈ D ʻʻ sel memRel K → μ \ A ∈ D ʻʻ sel memRel (K \ ι A) :=
  fun ⟨⟨h, hA⟩, hμ⟩ => pm81_24 ⟨⟨pm84_14.1 h, hμ⟩, hA⟩

/-- ✱84·421. \[\begin{align}&\vdash:\alpha\in \kappa.x\in \alpha.\mu\in \text{D}ʻʻ{\in}_{\Delta}ʻ(\kappa-\iotaʻ\alpha).\supset.\mu\cup \iotaʻx\in \text{D}ʻʻ{\in}_{\Delta}ʻ\kappa\\ &[\text{*81·25}]\end{align}\] -/
theorem pm84_421 {K : Set (Set α)} {A μ : Set α} {x : α} :
    (A ∈ K ∧ x ∈ A) ∧ μ ∈ D ʻʻ sel memRel (K \ ι A) → μ ∪ ι x ∈ D ʻʻ sel memRel K :=
  fun h => pm81_25 (P := memRel) h

/-- ✱84·422. \[\begin{align}&\vdash\colon\ldotp \kappa\in \text{Cls}^{2}\,\text{excl}.\alpha\in \kappa.\mu\cap \alpha\in 1.\supset:\mu-\alpha\in \text{D}ʻʻ{\in}_{\Delta}ʻ(\kappa-\iotaʻ\alpha).\equiv.\mu\in \text{D}ʻʻ\in _{\Delta}ʻ\alpha\\ &[\text{*81·26.*84·14.*62·2}]\end{align}\]

**Status.** proved (reading): misprint `∈_Δ'α` for `∈_Δ'κ` on the right (only `κ` is significant:
`μ` is a class of members of members of `κ`, and the cited ✱81·26 has `P_Δ'κ`). -/
theorem pm84_422 {K : Set (Set α)} {A μ : Set α} :
    (K ∈ Cls2excl ∧ A ∈ K) ∧ μ ∩ A ∈ one →
      (μ \ A ∈ D ʻʻ sel memRel (K \ ι A) ↔ μ ∈ D ʻʻ sel memRel K) :=
  fun ⟨⟨h, hA⟩, h1⟩ => pm81_26 ⟨⟨pm84_14.1 h, hA⟩, h1⟩

/-- ✱84·43. \(\vdash\colon\ldotp \alpha,\,\beta\in \text{Cls}^{2}\,\text{excl}.sʻ\alpha=sʻ\beta.\supset:\alpha\subset \text{D}ʻʻ{\in}_{\Delta}ʻ\beta.\equiv.\beta\subset \text{D}ʻʻ{\in}_{\Delta}ʻ\alpha\) -/
theorem pm84_43 {K L : Set (Set α)} :
    (K ∈ Cls2excl ∧ L ∈ Cls2excl) ∧ sumCls K = sumCls L →
      (K ⊆ D ʻʻ sel memRel L ↔ L ⊆ D ʻʻ sel memRel K) := by
  rintro ⟨⟨hK, hL⟩, e⟩
  rw [pm84_412 hK, pm84_412 hL]
  constructor
  · intro h η hη
    refine ⟨fun ξ hξ => ?_, fun x hx => e ▸ ⟨η, hη, hx⟩⟩
    rw [Set.inter_comm]
    exact (h hξ).1 η hη
  · intro h ξ hξ
    refine ⟨fun η hη => ?_, fun x hx => e.symm ▸ ⟨ξ, hξ, hx⟩⟩
    rw [Set.inter_comm]
    exact (h hη).1 ξ hξ

/-- ✱84·5. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\overrightarrow{R}ʻʻ\text{ᗡ}ʻR\in \text{Cls}^{2}\,\text{excl}\)

**Status.** proved (reading): transcription error `Cls² excl` for `Cls ex² excl` in the conclusion,
as in ✱84·52: PM's proof derives `∃!R⃗'x . ∃!R⃗'y` for `x, y ∈ ᗡ'R` (✱33·41) and concludes by
✱84·134, the characterization of `Cls ex² excl`. -/
theorem pm84_5 {R : α → β → Prop} : R ∈ arrow Cls one → Rfwd R ʻʻ codom R ∈ ClsEx2excl := by
  intro h
  rw [mem_arrow_Cls_one] at h
  refine ⟨?_, fun hn => (null_not_mem_iff (K := Rfwd R ʻʻ codom R)).2 ?_ hn⟩
  · rw [mem_Cls2excl]
    rintro A B x ⟨y, -, rfl⟩ ⟨z, -, rfl⟩ hy hz
    rw [h x y z ⟨hy, hz⟩]
  · rintro A ⟨y, ⟨x, hx⟩, rfl⟩
    exact ⟨x, hx⟩

/-- ✱84·51. \(\vdash:R\upharpoonright \kappa\in Cls\rightarrow 1.\supset.\overrightarrow{R}ʻʻ\kappa\in\text{Cls}^{2}\,\text{excl}\) -/
theorem pm84_51 {R : α → β → Prop} {K : Set β} :
    R ↾ K ∈ arrow Cls one → Rfwd R ʻʻ K ∈ Cls2excl := by
  intro h
  rw [mem_arrow_Cls_one] at h
  rw [mem_Cls2excl]
  rintro A B x ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ hxy hxz
  rw [h x y z ⟨⟨hxy, hy⟩, ⟨hxz, hz⟩⟩]

/-- ✱84·52. \(\vdash:R\upharpoonright \kappa\in \text{Cls}\rightarrow 1.\kappa\subset \text{ᗡ}ʻR.\supset.\overrightarrow{R}ʻʻ\kappa\in \text{Cls}^{2}\,\text{excl}\)

**Status.** proved (reading): transcription error `Cls² excl` for `Cls ex² excl` in the conclusion
(PM's proof derives `∃!α` for `α ∈ R⃗''κ` and cites ✱84·13; with `Cls² excl` the hypothesis `κ ⊂
ᗡ'R` would be idle, by ✱84·51). -/
theorem pm84_52 {R : α → β → Prop} {K : Set β} :
    R ↾ K ∈ arrow Cls one ∧ K ⊆ codom R → Rfwd R ʻʻ K ∈ ClsEx2excl := by
  rintro ⟨h, hK⟩
  refine ⟨pm84_51 h, fun hn => (null_not_mem_iff (K := Rfwd R ʻʻ K)).2 ?_ hn⟩
  rintro A ⟨y, hy, rfl⟩
  obtain ⟨x, hx⟩ := hK hy
  exact ⟨x, hx⟩

/-- ✱84·521. \(\vdash:\overrightarrow{R}\upharpoonright \beta\in 1\rightarrow 1.\overrightarrow{R}ʻʻ\beta\in \text{Cls}^{2}\,\text{excl}.\supset.R\upharpoonright \beta\in \text{Cls}\rightarrow 1\) -/
theorem pm84_521 {R : α → β → Prop} {B : Set β} :
    Rfwd R ↾ B ∈ arrow one one ∧ Rfwd R ʻʻ B ∈ Cls2excl → R ↾ B ∈ arrow Cls one := by
  rintro ⟨h11, hex⟩
  rw [mem_arrow_one_one] at h11
  rw [mem_Cls2excl] at hex
  rw [mem_arrow_Cls_one]
  rintro x y z ⟨⟨hxy, hy⟩, ⟨hxz, hz⟩⟩
  have e : refs R y = refs R z := hex _ _ x ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ hxy hxz
  exact h11.2 (refs R y) y z ⟨⟨rfl, hy⟩, ⟨e, hz⟩⟩

/-- ✱84·522. \(\vdash\colon\ldotp \beta\subset \text{ᗡ}ʻR.\supset:R\upharpoonright \beta\in \text{Cls}\rightarrow 1.\equiv.\overrightarrow{R}\upharpoonright \beta\in 1\rightarrow 1.\overrightarrow{R}ʻʻ\beta\in \text{Cls}^{2}\,\text{excl}\) -/
theorem pm84_522 {R : α → β → Prop} {B : Set β} :
    B ⊆ codom R →
      (R ↾ B ∈ arrow Cls one ↔ Rfwd R ↾ B ∈ arrow one one ∧ Rfwd R ʻʻ B ∈ Cls2excl) := by
  intro hB
  refine ⟨fun h => ⟨?_, pm84_51 h⟩, pm84_521⟩
  have h' := h
  rw [mem_arrow_Cls_one] at h'
  rw [mem_arrow_one_one]
  constructor
  · rintro A A' y ⟨⟨e, -⟩, ⟨e', -⟩⟩
    exact e.trans e'.symm
  · rintro A y z ⟨⟨e, hy⟩, ⟨e', hz⟩⟩
    obtain ⟨x, hx⟩ := hB hy
    have hxz : R x z := by
      have : x ∈ refs R z := e'.symm.trans e ▸ hx
      exact this
    exact h' x y z ⟨⟨hx, hy⟩, ⟨hxz, hz⟩⟩

/-- ✱84·53. \(\vdash:R\in \text{Cls}\rightarrow 1.\kappa\in \text{Cls}^{2}\,\text{excl}.\supset.Rʻʻʻ\kappa\in \text{Cls}^{2}\,\text{excl}\) -/
theorem pm84_53 {R : α → β → Prop} {K : Set (Set β)} :
    R ∈ arrow Cls one ∧ K ∈ Cls2excl → R ʻʻʻ K ∈ Cls2excl := by
  rintro ⟨h, hK⟩
  rw [mem_arrow_Cls_one] at h
  rw [mem_Cls2excl] at hK ⊢
  rintro C C' x ⟨B, hB, rfl⟩ ⟨B', hB', rfl⟩ ⟨b, hb, hxb⟩ ⟨b', hb', hxb'⟩
  have e : b = b' := h x b b' ⟨hxb, hxb'⟩
  subst e
  rw [hK B B' b hB hB' hb hb']

/-- ✱84·54. \(\vdash:R\in 1\rightarrow \text{Cls}.\kappa\in \text{Cls}^{2}\,\text{excl}.\supset.\breve{R}ʻʻʻ\kappa\in \text{Cls}^{2}\,\text{excl} \quad\left[\text{*84·53} \frac{\breve{R}}{R}\right]\) -/
theorem pm84_54 {R : α → β → Prop} {K : Set (Set α)} :
    R ∈ arrow one Cls ∧ K ∈ Cls2excl → R˘ ʻʻʻ K ∈ Cls2excl := by
  rintro ⟨h, hK⟩
  refine pm84_53 ⟨?_, hK⟩
  rw [mem_arrow_one_Cls] at h
  rw [mem_arrow_Cls_one]
  rintro x y z ⟨h1, h2⟩
  exact h y z x ⟨h1, h2⟩

/-- ✱84·55. \(\vdash.P_{\Delta}ʻʻ\kappa\in \text{Cls}^{2}\,\text{excl} \quad[\text{*80·82}]\) -/
theorem pm84_55 {P : α → β → Prop} {K : Set (Set β)} : selRel P ʻʻ K ∈ Cls2excl := by
  rw [mem_Cls2excl]
  rintro L L' M ⟨A, -, rfl⟩ ⟨B, -, rfl⟩ hA hB
  have : A = B := by
    ext y
    rw [sel_codom_iff hA, sel_codom_iff hB]
  rw [this]

/-- ✱84·59. \(\vdash:\kappa\cup \lambda\in \text{Cls}^{2}\,\text{excl}.\equiv.\kappa,\,\lambda\in \text{Cls}^{2}\,\text{excl}.sʻ(\kappa-\lambda)\cap sʻ\lambda=\Lambda\) -/
theorem pm84_59 {K L : Set (Set α)} :
    K ∪ L ∈ Cls2excl ↔ (K ∈ Cls2excl ∧ L ∈ Cls2excl) ∧ sumCls (K \ L) ∩ sumCls L = Λ := by
  simp only [mem_Cls2excl, inter_eq_null_iff, sumCls, Set.mem_ofPred_eq, Set.mem_sdiff,
    Set.mem_union]
  constructor
  · intro h
    refine ⟨⟨fun A B x hA hB => h A B x (Or.inl hA) (Or.inl hB),
      fun A B x hA hB => h A B x (Or.inr hA) (Or.inr hB)⟩, ?_⟩
    rintro x ⟨A, ⟨hA, hAL⟩, hxA⟩ ⟨B, hB, hxB⟩
    exact hAL (h A B x (Or.inl hA) (Or.inr hB) hxA hxB ▸ hB)
  · rintro ⟨⟨hK, hL⟩, hd⟩ A B x hA hB hxA hxB
    have key : ∀ A B, A ∈ K → B ∈ L → x ∈ A → x ∈ B → A = B := by
      intro A B hA hB hxA hxB
      by_cases hAL : A ∈ L
      · exact hL A B x hAL hB hxA hxB
      · exact (hd x ⟨A, ⟨hA, hAL⟩, hxA⟩ ⟨B, hB, hxB⟩).elim
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact hK A B x hA hB hxA hxB
    · exact key A B hA hB hxA hxB
    · exact (key B A hB hA hxB hxA).symm
    · exact hL A B x hA hB hxA hxB

/-- ✱84·6. \[\begin{align}&\vdash\colon\ldotp \kappa\cap \lambda=\Lambda.\supset:\kappa\cup \lambda\in \text{Cls}^{2}\,\text{excl}.\equiv.\kappa,\,\lambda\in \text{Cls}^{2}\,\text{excl}.sʻ\kappa\cap sʻ\lambda=\Lambda\\ &[\text{*84·59.*24·313}]\end{align}\] -/
theorem pm84_6 {K L : Set (Set α)} :
    K ∩ L = Λ →
      (K ∪ L ∈ Cls2excl ↔ (K ∈ Cls2excl ∧ L ∈ Cls2excl) ∧ sumCls K ∩ sumCls L = Λ) := by
  intro h
  have e : K \ L = K := by
    ext A
    constructor
    · exact fun h' => h'.1
    · intro hA
      refine ⟨hA, fun hAL => ?_⟩
      have : A ∈ K ∩ L := ⟨hA, hAL⟩
      rw [h, Null_eq_empty] at this
      exact this
  rw [pm84_59, e]

/-- ✱84·61. \[\begin{align}&\vdash\colon\ldotp \beta{\sim}\in \kappa.\supset:\kappa\cup \iotaʻ\beta\in \text{Cls}^{2}\,\text{excl}.\equiv.\kappa\in \text{Cls}^{2}\,\text{excl}.\beta\cap sʻ\kappa=\Lambda\\ &[\text{*51·211.*53·02.*84·23·6}]\end{align}\] -/
theorem pm84_61 {K : Set (Set α)} {B : Set α} :
    B ∉ K → (K ∪ ι B ∈ Cls2excl ↔ K ∈ Cls2excl ∧ B ∩ sumCls K = Λ) := by
  intro hB
  have h : K ∩ ι B = Λ := by
    rw [Null_eq_empty]
    ext A
    simp only [Set.mem_inter_iff, mem_unitCls, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hA, rfl⟩
    exact hB hA
  have hs : sumCls (ι B) = B := by
    ext x
    exact ⟨fun ⟨A, hA, hx⟩ => (hA : A = B) ▸ hx, fun hx => ⟨B, rfl, hx⟩⟩
  rw [pm84_6 h, hs, Set.inter_comm B]
  exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, pm84_23⟩, h2⟩⟩

/-- ✱84·62. \[\begin{align}&\vdash\colon\ldotp \alpha \neq \beta.\supset:\iotaʻ\alpha\cup \iotaʻ\beta\in \text{Cls}^{2}\,\text{excl}.\equiv.\alpha\cap \beta=\Lambda\\ &[\text{*84·61.*51·15.*53·02.*84·23}]\end{align}\] -/
theorem pm84_62 {A B : Set α} : A ≠ B → (ι A ∪ ι B ∈ Cls2excl ↔ A ∩ B = Λ) := by
  intro h
  have hB : B ∉ ι A := fun e => h (e : B = A).symm
  rw [pm84_61 hB]
  have hs : sumCls (ι A) = A := by
    ext x
    exact ⟨fun ⟨C, hC, hx⟩ => (hC : C = A) ▸ hx, fun hx => ⟨A, rfl, hx⟩⟩
  rw [hs, Set.inter_comm]
  exact ⟨fun h => h.2, fun h => ⟨pm84_23, h⟩⟩

/-!
## [✱85] Miscellaneous propositions

*(Vol. 1, p. 549)*

> *Summary of* *85.
>
> In this number certain important propositions are proved, and the other propositions of this number are mainly lemmas. The most important propositions are the following:
>
> *85·1 and *85·14, which show that if \(Q \upharpoonright\lambda\) is a \(\text{Cls} \rightarrow 1\), then the domains of \(Q_{\Delta}ʻ\lambda\) are the same as the domains of \({\in}_{\Delta}ʻ\overrightarrow{Q}ʻʻ\lambda\), and \(Q_{\Delta}ʻ\lambda\) is similar to \({\in}_{\Delta}ʻ\overrightarrow{Q}ʻʻ\lambda\), thus reducing the problem of selections from many-one relations to that of selections from classes of classes.
>
> …

**Lean reading.** `Q⃗` is `Rfwd Q` and `Cnv'Q⃗` (✱85·13) is `(Rfwd Q)˘`. In ✱85·22 `M↾` is the
relation of `M ↾ α` to `α` (✱38·01 with `♀ = ↾`), `opL cres M`, and `κ ↿ P̆_Δ` is `K ◁ (selRel P)˘`
(`P̆_Δ` is `Cnv'P_Δ`, as `R̆_∈` in ✱37·03), so the relation is `opL cres M ⨾ (K ◁ (selRel P)˘)`.
`ṡ''λ` is `graph sumRel ʻʻ λ` (the descriptive function `ṡ'` always exists), `C''`, `D''`, `ᗡ''` are
`C ʻʻ`, `D ʻʻ`, `Dcnv ʻʻ`. `P ↧ y` is `downCls P y` (✱85·5) and `P↧` is `opL downCls P`. ✱85·31–·4
are proved from the general lemma `sel_eq_of_sumRel_dom`, and ✱85·53·54 from ✱85·27·43 applied to
`ι''α`, as in PM. Readings: ✱85·33 (missing `ʻ`), ✱85·51 (`P ↧` for `P ↧ x`), ✱85·72 (`S''β` for
`S''λ`), ✱85·81 (`s̆` for `ṡ`); in ✱85·45 the bracket `∈_Δ'(κ ∪ λ)` is written.

**Status.** proved (all propositions; ✱85·5 definition; ✱85·33, ✱85·51, ✱85·72, ✱85·81 proved
(reading), see their docstrings).
-/

/-- Similar classes are together null or together existent (✱73·36-like). -/
theorem sm_nonempty_iff {A : Set α} {B : Set β} (h : sm A B) : A.Nonempty ↔ B.Nonempty := by
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 h
  constructor
  · rintro ⟨x, hx⟩; exact ⟨_, (e ⟨x, hx⟩).2⟩
  · rintro ⟨y, hy⟩; exact ⟨_, (e.symm ⟨y, hy⟩).2⟩

/-- ✱85·1. \(\vdash\colon Q\upharpoonright \lambda\in\text{Cls}\rightarrow 1.\supset.DʻʻQ_{\Delta}ʻ\lambda=Dʻʻ{\in}_{\Delta}ʻ\overrightarrow{Q}ʻʻ\lambda\) -/
theorem pm85_1 {Q : α → β → Prop} {L : Set β} :
    Q ↾ L ∈ arrow Cls one → D ʻʻ sel Q L = D ʻʻ sel memRel (Rfwd Q ʻʻ L) := by
  intro h
  rw [pm81_3 ⟨h, rfl⟩, pm84_412 (pm84_51 h)]

/-- ✱85·11. \(\vdash\colon\overrightarrow{Q}\upharpoonright\lambda\in 1\rightarrow 1.\supset.\text{D}ʻʻ(P\mid\overrightarrow{Q})_{\Delta}ʻ\lambda=\text{D}ʻʻP_{\Delta}ʻ\overrightarrow{Q}ʻʻ\lambda\) -/
theorem pm85_11 {P : α → Set γ → Prop} {Q : γ → β → Prop} {L : Set β} :
    Rfwd Q ↾ L ∈ arrow one one → D ʻʻ sel (P ⨾ Rfwd Q) L = D ʻʻ sel P (Rfwd Q ʻʻ L) :=
  fun h => pm82_32 ⟨h, fun y _ => ⟨refs Q y, rfl⟩⟩

/-- ✱85·111. \(\vdash\colon M\in{\in}_{\Delta}ʻ\overrightarrow{Q}ʻʻ\lambda.\supset.\text{D}ʻ(M\mid\overrightarrow{Q}\upharpoonright\lambda)=DʻM \quad[\text{*82·3}]\) -/
theorem pm85_111 {Q : α → β → Prop} {L : Set β} {M : α → Set α → Prop} :
    M ∈ sel memRel (Rfwd Q ʻʻ L) → dom (M ⨾ Rfwd Q ↾ L) = dom M := pm82_3

/-- ✱85·112. \(\vdash\colon M\in{\in}_{\Delta}ʻ\overrightarrow{Q}ʻʻ\lambda.\supset.M\mid\overrightarrow{Q}\upharpoonright \lambda\in Q_{\Delta}ʻ\lambda \quad\left[\text{*82·221} \frac{{\in},\,\overrightarrow{Q}}{P,\,Q}.\text{*62·26}\right]\) -/
theorem pm85_112 {Q : α → β → Prop} {L : Set β} {M : α → Set α → Prop} :
    M ∈ sel memRel (Rfwd Q ʻʻ L) → M ⨾ Rfwd Q ↾ L ∈ sel Q L := by
  intro hM
  have hs := sel_iff.1 hM
  rw [sel_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x x' z ⟨⟨A, hA, rfl⟩, -⟩ ⟨⟨A', hA', e⟩, -⟩
    have e' : A' = refs Q z := e
    subst e'
    exact hs.1 x x' _ hA hA'
  · rintro x z ⟨⟨A, hA, rfl⟩, -⟩
    exact hs.2.1 x _ hA
  · rintro x z ⟨-, hz⟩
    exact hz
  · intro z hz
    obtain ⟨x, hx⟩ := hs.2.2.2 (refs Q z) ⟨z, hz, rfl⟩
    exact ⟨x, ⟨refs Q z, hx, rfl⟩, hz⟩

/-- The content of ✱85·13, used in ✱85·12. -/
theorem sel_comp_rfwd_cnv {Q : α → β → Prop} {L : Set β} {R : α → β → Prop} :
    Rfwd Q ↾ L ∈ arrow one one ∧ R ∈ sel Q L → R ⨾ (Rfwd Q)˘ ∈ sel memRel (Rfwd Q ʻʻ L) := by
  rintro ⟨h11, hR⟩
  rw [mem_arrow_one_one] at h11
  have hs := sel_iff.1 hR
  rw [sel_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x x' A ⟨y, hy, rfl⟩ ⟨y', hy', e⟩
    have e' : refs Q y = refs Q y' := e
    have : y = y' := h11.2 _ y y' ⟨⟨rfl, hs.2.2.1 _ _ hy⟩, ⟨e', hs.2.2.1 _ _ hy'⟩⟩
    subst this
    exact hs.1 x x' y hy hy'
  · rintro x A ⟨y, hy, rfl⟩
    exact hs.2.1 x y hy
  · rintro x A ⟨y, hy, rfl⟩
    exact ⟨y, hs.2.2.1 _ _ hy, rfl⟩
  · rintro A ⟨y, hy, rfl⟩
    obtain ⟨x, hx⟩ := hs.2.2.2 y hy
    exact ⟨x, y, hx, rfl⟩

/-- ✱85·12. \(\vdash\colon\overrightarrow{Q}\upharpoonright \lambda\in 1\rightarrow 1.\supset.DʻʻQ_{\Delta}ʻ\lambda=\text{D}ʻʻ{\in}_{\Delta}ʻ\overrightarrow{Q}ʻʻ\lambda\) -/
theorem pm85_12 {Q : α → β → Prop} {L : Set β} :
    Rfwd Q ↾ L ∈ arrow one one → D ʻʻ sel Q L = D ʻʻ sel memRel (Rfwd Q ʻʻ L) := by
  intro h
  ext μ
  constructor
  · rintro ⟨R, hR, rfl⟩
    refine ⟨_, sel_comp_rfwd_cnv ⟨h, hR⟩, ?_⟩
    show dom R = dom _
    ext x
    constructor
    · rintro ⟨y, hy⟩; exact ⟨refs Q y, y, hy, rfl⟩
    · rintro ⟨A, y, hy, -⟩; exact ⟨y, hy⟩
  · rintro ⟨M, hM, rfl⟩
    exact ⟨_, pm85_112 hM, (pm85_111 hM).symm⟩

/-- ✱85·13. \(\vdash:\overrightarrow{Q}\upharpoonright\lambda\in 1\rightarrow 1.R\in Q_{\Delta}ʻ\lambda.\supset.R\mid\text{Cnv}ʻ\overrightarrow{Q}\in{\in}_{\Delta}ʻ\overrightarrow{Q}ʻʻ\lambda\) -/
theorem pm85_13 {Q : α → β → Prop} {L : Set β} {R : α → β → Prop} :
    Rfwd Q ↾ L ∈ arrow one one ∧ R ∈ sel Q L → R ⨾ (Rfwd Q)˘ ∈ sel memRel (Rfwd Q ʻʻ L) :=
  sel_comp_rfwd_cnv

/-- ✱85·14. \(\vdash:Q\upharpoonright\lambda\in\text{Cls}\rightarrow 1.\supset.Q_{\Delta}ʻ\lambda\,\text{ sm }\,{\in}_{\Delta}ʻ\overrightarrow{Q}ʻʻ\lambda\) -/
theorem pm85_14 {Q : α → β → Prop} {L : Set β} :
    Q ↾ L ∈ arrow Cls one → sm (sel Q L) (sel memRel (Rfwd Q ʻʻ L)) := by
  intro h
  have h1 := sm_symm (pm81_21 h).2
  rw [pm85_1 h] at h1
  exact sm_trans h1 (pm84_41 (pm84_51 h)).2

/-- ✱85·21. \(\vdash:\alpha\in\kappa.M\in {P}_{\Delta}ʻsʻ\kappa.\supset.M\upharpoonright\alpha\in P_{\Delta}ʻ\alpha \quad[\text{*80·6.*40·13}]\) -/
theorem pm85_21 {P M : α → β → Prop} {K : Set (Set β)} {A : Set β} :
    A ∈ K ∧ M ∈ sel P (sumCls K) → M ↾ A ∈ sel P A :=
  fun ⟨hA, hM⟩ => pm80_6 ⟨hM, fun _ hx => ⟨A, hA, hx⟩⟩

/-- ✱85·22. \(\vdash:M\in {P}_{\Delta}ʻsʻ\kappa.\supset.M\upharpoonright \mid\kappa \upharpoonleft \breve{P}_{\Delta}\in {\in}_{\Delta}ʻP_{\Delta}ʻʻ\kappa.\dot{s}ʻ\text{D}ʻ(M\upharpoonright \mid\kappa \upharpoonleft \breve{P}_{\Delta})=M\) -/
theorem pm85_22 {P M : α → β → Prop} {K : Set (Set β)} :
    M ∈ sel P (sumCls K) →
      opL cres M ⨾ (K ◁ (selRel P)˘) ∈ sel memRel (selRel P ʻʻ K) ∧
        sumRel (dom (opL cres M ⨾ (K ◁ (selRel P)˘))) = M := by
  intro hM
  have hs := sel_iff.1 hM
  constructor
  · rw [sel_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro S S' L ⟨A, rfl, hA, rfl⟩ ⟨A', rfl, hA', e⟩
      have : A = A' := pm80_81 ⟨⟨_, pm85_21 ⟨hA, hM⟩⟩, e⟩
      rw [this]
    · rintro S L ⟨A, rfl, hA, rfl⟩
      exact pm85_21 ⟨hA, hM⟩
    · rintro S L ⟨A, -, hA, rfl⟩
      exact ⟨A, hA, rfl⟩
    · rintro L ⟨A, hA, rfl⟩
      exact ⟨M ↾ A, A, rfl, hA, rfl⟩
  · funext x y
    apply propext
    constructor
    · rintro ⟨S, ⟨L, A, rfl, -, -⟩, hxy, -⟩
      exact hxy
    · intro hxy
      obtain ⟨A, hA, hy⟩ := hs.2.2.1 x y hxy
      exact ⟨M ↾ A, ⟨sel P A, A, rfl, hA, rfl⟩, hxy, hy⟩

/-- ✱85·24. \(\vdash.P_{\Delta}ʻsʻ\kappa\subset\dot{s}ʻʻ\text{D}ʻʻ{\in}_{\Delta}ʻP_{\Delta}ʻʻ\kappa\) -/
theorem pm85_24 {P : α → β → Prop} {K : Set (Set β)} :
    sel P (sumCls K) ⊆ graph sumRel ʻʻ D ʻʻ sel memRel (selRel P ʻʻ K) := by
  intro M hM
  have h := pm85_22 hM
  exact ⟨_, ⟨_, h.1, rfl⟩, h.2.symm⟩

/-- ✱85·241. \(\vdash:X\in{\in}_{\Delta}ʻP_{\Delta}ʻʻ\kappa.\alpha\in\kappa.\supset.XʻP_{\Delta}ʻ\alpha\in P_{\Delta}ʻ\alpha\) -/
theorem pm85_241 {P : α → β → Prop} {K : Set (Set β)} {X : (α → β → Prop) → Set (α → β → Prop) → Prop}
    {A : Set β} :
    X ∈ sel memRel (selRel P ʻʻ K) ∧ A ∈ K → Desc X (sel P A) (fun S => S ∈ sel P A) := by
  rintro ⟨hX, hA⟩
  obtain ⟨S, hS, hu⟩ := sel_ex hX ⟨A, hA, rfl⟩
  rw [desc_iff_of hS hu]
  exact (sel_iff.1 hX).2.1 S _ hS

/-- The members of `D'X`, for `X ∈ ∈_Δ'P_Δ''κ`. -/
theorem mem_dom_selsel {P : α → β → Prop} {K : Set (Set β)}
    {X : (α → β → Prop) → Set (α → β → Prop) → Prop} (hX : X ∈ sel memRel (selRel P ʻʻ K))
    {S : α → β → Prop} (hS : S ∈ dom X) : ∃ A, A ∈ K ∧ X S (sel P A) ∧ S ∈ sel P A := by
  obtain ⟨L, hL⟩ := hS
  have hs := sel_iff.1 hX
  obtain ⟨A, hA, e⟩ := hs.2.2.1 S L hL
  have e' : L = sel P A := e
  subst e'
  exact ⟨A, hA, hL, hs.2.1 S _ hL⟩

/-- ✱85·243. \(\vdash:\kappa\in\text{Cls}^{2}\,\text{excl}.X\in{\in}_{\Delta}ʻP_{\Delta}ʻʻ\kappa.\supset.\dot{s}ʻ\text{D}ʻX\in 1\rightarrow\text{Cls}\) -/
theorem pm85_243 {P : α → β → Prop} {K : Set (Set β)}
    {X : (α → β → Prop) → Set (α → β → Prop) → Prop} :
    K ∈ Cls2excl ∧ X ∈ sel memRel (selRel P ʻʻ K) → sumRel (dom X) ∈ arrow one Cls := by
  rintro ⟨hK, hX⟩
  rw [mem_Cls2excl] at hK
  rw [mem_arrow_one_Cls]
  rintro x y z ⟨⟨S, hS, hxz⟩, ⟨S', hS', hyz⟩⟩
  obtain ⟨A, hA, hXS, hSA⟩ := mem_dom_selsel hX hS
  obtain ⟨A', hA', hXS', hSA'⟩ := mem_dom_selsel hX hS'
  have hzA : z ∈ A := (sel_iff.1 hSA).2.2.1 _ _ hxz
  have hzA' : z ∈ A' := (sel_iff.1 hSA').2.2.1 _ _ hyz
  have e : A = A' := hK A A' z hA hA' hzA hzA'
  subst e
  have e2 : S = S' := (sel_iff.1 hX).1 S S' _ hXS hXS'
  subst e2
  exact (sel_iff.1 hSA).1 x y z hxz hyz

/-- ✱85·244. \(\vdash:X\in {\in}_{\Delta}ʻP_{\Delta}ʻʻ\kappa.\supset.\dot{s}ʻ\text{D}ʻX\unicode{x2abd}P\) -/
theorem pm85_244 {P : α → β → Prop} {K : Set (Set β)}
    {X : (α → β → Prop) → Set (α → β → Prop) → Prop} :
    X ∈ sel memRel (selRel P ʻʻ K) → sumRel (dom X) ⪽ P := by
  rintro hX x y ⟨S, hS, hxy⟩
  obtain ⟨A, -, -, hSA⟩ := mem_dom_selsel hX hS
  exact (sel_iff.1 hSA).2.1 x y hxy

/-- ✱85·245. \(\vdash:X\in {\in}_{\Delta}ʻP_{\Delta}ʻʻ\kappa.\supset.\text{ᗡ}ʻ\dot{s}ʻ\text{D}ʻX=sʻ\kappa\) -/
theorem pm85_245 {P : α → β → Prop} {K : Set (Set β)}
    {X : (α → β → Prop) → Set (α → β → Prop) → Prop} :
    X ∈ sel memRel (selRel P ʻʻ K) → codom (sumRel (dom X)) = sumCls K := by
  intro hX
  ext y
  constructor
  · rintro ⟨x, S, hS, hxy⟩
    obtain ⟨A, hA, -, hSA⟩ := mem_dom_selsel hX hS
    exact ⟨A, hA, (sel_iff.1 hSA).2.2.1 _ _ hxy⟩
  · rintro ⟨A, hA, hy⟩
    obtain ⟨S, hS⟩ := (sel_iff.1 hX).2.2.2 (sel P A) ⟨A, hA, rfl⟩
    have hSA : S ∈ sel P A := (sel_iff.1 hX).2.1 S _ hS
    obtain ⟨x, hx⟩ := (sel_iff.1 hSA).2.2.2 y hy
    exact ⟨x, S, ⟨_, hS⟩, hx⟩

/-- ✱85·25. \[\begin{align}\vdash:\kappa\in\text{Cls}^{2}\,\text{excl}.X\in{\in}_{\Delta}ʻP_{\Delta}ʻʻ\kappa.\supset.\dot{s}ʻ\text{D}ʻX\in P_{\Delta}ʻsʻ\kappa\\ \quad[\text{*85·243·244·245.*80·14}]\end{align}\] -/
theorem pm85_25 {P : α → β → Prop} {K : Set (Set β)}
    {X : (α → β → Prop) → Set (α → β → Prop) → Prop} :
    K ∈ Cls2excl ∧ X ∈ sel memRel (selRel P ʻʻ K) → sumRel (dom X) ∈ sel P (sumCls K) :=
  fun h => mem_sel_iff.2 ⟨⟨pm85_243 h, pm85_244 h.2⟩, pm85_245 h.2⟩

/-- ✱85·26. \(\vdash\colon\kappa\in\text{Cls}^{2}\,\text{excl}.\supset.\dot{s}ʻʻ\text{D}ʻʻ{\in}_{\Delta}ʻP_{\Delta}ʻʻ\kappa\subset P_{\Delta}ʻsʻ\kappa\) -/
theorem pm85_26 {P : α → β → Prop} {K : Set (Set β)} :
    K ∈ Cls2excl → graph sumRel ʻʻ D ʻʻ sel memRel (selRel P ʻʻ K) ⊆ sel P (sumCls K) := by
  rintro hK M ⟨_, ⟨X, hX, rfl⟩, hM⟩
  have hM' : M = sumRel (dom X) := hM
  rw [hM']
  exact pm85_25 ⟨hK, hX⟩

/-- ✱85·27. \(\vdash\colon\kappa\in\text{Cls}^{2}\,\text{excl}.\supset.P_{\Delta}ʻsʻ\kappa=\dot{s}ʻʻ\text{D}ʻʻ{\in}_{\Delta}ʻP_{\Delta}ʻʻ\kappa \quad[\text{*85·24·26}]\) -/
theorem pm85_27 {P : α → β → Prop} {K : Set (Set β)} :
    K ∈ Cls2excl → sel P (sumCls K) = graph sumRel ʻʻ D ʻʻ sel memRel (selRel P ʻʻ K) :=
  fun hK => Set.Subset.antisymm pm85_24 (pm85_26 hK)

/-- ✱85·28. \(\vdash\colon\kappa\in\text{Cls}^{2}\,\text{excl}.\supset.{\in}_{\Delta}ʻsʻ\kappa=\dot{s}ʻʻ\text{D}ʻʻ{\in}_{\Delta}ʻ{\in}_{\Delta}ʻʻ\kappa \quad\left[\text{*85·27}\, \frac{{\in}}{P}\right]\) -/
theorem pm85_28 {K : Set (Set (Set α))} :
    K ∈ Cls2excl →
      sel memRel (sumCls K) = graph sumRel ʻʻ D ʻʻ sel memRel (selRel memRel ʻʻ K) := pm85_27

/-- ✱85·3. \(\vdash\colon M\in P_{\Delta}ʻ\alpha.z\in\alpha.\supset.Mʻz\unicode{x2abd}\dot{s}ʻ\text{D}ʻM.Mʻz\unicode{x2abd}\dot{s}ʻ\overrightarrow{P}ʻz\) -/
theorem pm85_3 {P M : (γ → δ → Prop) → β → Prop} {A : Set β} {z : β} :
    M ∈ sel P A ∧ z ∈ A →
      Desc M z (fun S => S ⪽ sumRel (dom M)) ∧ Desc M z (fun S => S ⪽ sumRel (refs P z)) := by
  rintro ⟨hM, hz⟩
  obtain ⟨S, hS, hu⟩ := sel_ex hM hz
  rw [desc_iff_of hS hu, desc_iff_of hS hu]
  exact ⟨fun a b hab => ⟨S, ⟨z, hS⟩, hab⟩,
    fun a b hab => ⟨S, (sel_iff.1 hM).2.1 S z hS, hab⟩⟩

/-- Lemma for ✱85·31–·4: selections whose selected relations come from "disjoint" families are
determined by the sum of their selected relations. -/
theorem sel_eq_of_sumRel_dom {P : (γ → δ → Prop) → β → Prop} {A : Set β}
    {M N : (γ → δ → Prop) → β → Prop}
    (hd : ∀ z w, z ∈ A → w ∈ A → z ≠ w → ∀ a b,
      (∃ S, P S z ∧ S a b) → (∃ S, P S w ∧ S a b) → False)
    (hM : M ∈ sel P A) (hN : N ∈ sel P A) (e : sumRel (dom M) = sumRel (dom N)) : M = N := by
  have key : ∀ {M N : (γ → δ → Prop) → β → Prop}, M ∈ sel P A → N ∈ sel P A →
      sumRel (dom M) = sumRel (dom N) → ∀ S z, M S z → ∀ T, N T z → S ⪽ T := by
    intro M N hM hN e S z hS T hT a b hab
    have h1 : sumRel (dom M) a b := ⟨S, ⟨z, hS⟩, hab⟩
    rw [e] at h1
    obtain ⟨T', ⟨w, hT'⟩, hab'⟩ := h1
    have hz : z ∈ A := (sel_iff.1 hM).2.2.1 _ _ hS
    have hw : w ∈ A := (sel_iff.1 hN).2.2.1 _ _ hT'
    by_cases hzw : z = w
    · subst hzw
      rw [(sel_iff.1 hN).1 T' T z hT' hT] at hab'
      exact hab'
    · exact (hd z w hz hw hzw a b ⟨S, (sel_iff.1 hM).2.1 _ _ hS, hab⟩
        ⟨T', (sel_iff.1 hN).2.1 _ _ hT', hab'⟩).elim
  have key2 : ∀ {M N : (γ → δ → Prop) → β → Prop}, M ∈ sel P A → N ∈ sel P A →
      sumRel (dom M) = sumRel (dom N) → ∀ S z, M S z → N S z := by
    intro M N hM hN e S z hS
    obtain ⟨T, hT⟩ := (sel_iff.1 hN).2.2.2 z ((sel_iff.1 hM).2.2.1 _ _ hS)
    have : S = T := funext fun a => funext fun b =>
      propext ⟨key hM hN e S z hS T hT a b, key hN hM e.symm T z hT S hS a b⟩
    exact this ▸ hT
  funext S z
  exact propext ⟨key2 hM hN e S z, key2 hN hM e.symm S z⟩

/-- ✱85·31. \[\begin{align}\vdash\colon\ldotp &z,w\in\alpha.z\neq w.\supset_{z,w}.\dot{s}ʻ\overrightarrow{P}ʻz\dot{\cap}\dot{s}ʻ\overrightarrow{P}ʻw=\dot{\Lambda}:\supset:\\ &M,N\in P_{\Delta}ʻ\alpha.\dot{s}ʻ\text{D}ʻM=\dot{s}ʻ\text{D}ʻN.\supset.M=N\end{align}\] -/
theorem pm85_31 {P M N : (γ → δ → Prop) → β → Prop} {A : Set β} :
    (∀ z w, (z ∈ A ∧ w ∈ A) ∧ z ≠ w → sumRel (refs P z) ⩀ sumRel (refs P w) = rNull) →
      ((M ∈ sel P A ∧ N ∈ sel P A) ∧ sumRel (dom M) = sumRel (dom N) → M = N) := by
  rintro h ⟨⟨hM, hN⟩, e⟩
  refine sel_eq_of_sumRel_dom (fun z w hz hw hzw a b h1 h2 => ?_) hM hN e
  have := congrFun (congrFun (h z w ⟨⟨hz, hw⟩, hzw⟩) a) b
  exact (cast this ⟨h1, h2⟩) ⟨rfl, rfl⟩

/-- ✱85·32. \[\begin{align}\vdash\colon\ldotp &z,w\in\alpha .z\neq w.\supset_{z,w}.sʻ Cʻʻ\overrightarrow{P}ʻ z\cap sʻ Cʻʻ\overrightarrow{P}ʻ w=\Lambda:\supset:\\ &M,N\in P_{\Delta}ʻ\alpha .\dot{s}ʻ \text{D}ʻ M=\dot{s}ʻ \text{D}ʻ N.\supset .M=N\end{align}\] -/
theorem pm85_32 {P M N : (γ → γ → Prop) → β → Prop} {A : Set β} :
    (∀ z w, (z ∈ A ∧ w ∈ A) ∧ z ≠ w →
        sumCls (C ʻʻ refs P z) ∩ sumCls (C ʻʻ refs P w) = Λ) →
      ((M ∈ sel P A ∧ N ∈ sel P A) ∧ sumRel (dom M) = sumRel (dom N) → M = N) := by
  rintro h ⟨⟨hM, hN⟩, e⟩
  refine sel_eq_of_sumRel_dom (fun z w hz hw hzw a b h1 h2 => ?_) hM hN e
  obtain ⟨S, hS, hab⟩ := h1
  obtain ⟨T, hT, hab'⟩ := h2
  exact inter_eq_null_iff.1 (h z w ⟨⟨hz, hw⟩, hzw⟩) a ⟨fld S, ⟨S, hS, rfl⟩, b, Or.inl hab⟩
    ⟨fld T, ⟨T, hT, rfl⟩, b, Or.inl hab'⟩

/-- ✱85·33. \[\begin{align}\vdash\colon\ldotp &z,w\in\alpha .z\neq w.\supset_{z,w}.sʻ \text{D}ʻʻ\overrightarrow{P}ʻ z\cap sʻ \text{D}ʻʻ\overrightarrow{P}ʻ w=\Lambda :\supset:\\ &M,N\in P_{\Delta}ʻ\alpha .\dot{s}\text{D}ʻ M=\dot{s}ʻ \text{D}ʻ N.\supset .M=N \quad[\text{*41·43.*33·32.*85·31}]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `ṡD'M` (without `ʻ`) for
`ṡ'D'M` in the conclusion. -/
theorem pm85_33 {P M N : (γ → δ → Prop) → β → Prop} {A : Set β} :
    (∀ z w, (z ∈ A ∧ w ∈ A) ∧ z ≠ w →
        sumCls (D ʻʻ refs P z) ∩ sumCls (D ʻʻ refs P w) = Λ) →
      ((M ∈ sel P A ∧ N ∈ sel P A) ∧ sumRel (dom M) = sumRel (dom N) → M = N) := by
  rintro h ⟨⟨hM, hN⟩, e⟩
  refine sel_eq_of_sumRel_dom (fun z w hz hw hzw a b h1 h2 => ?_) hM hN e
  obtain ⟨S, hS, hab⟩ := h1
  obtain ⟨T, hT, hab'⟩ := h2
  exact inter_eq_null_iff.1 (h z w ⟨⟨hz, hw⟩, hzw⟩) a ⟨dom S, ⟨S, hS, rfl⟩, b, hab⟩
    ⟨dom T, ⟨T, hT, rfl⟩, b, hab'⟩

/-- ✱85·34. \[\begin{align}\vdash\colon\ldotp &z,w\in\alpha.z \neq w.\supset_{z,w}.sʻ\text{ᗡ}ʻʻ\overrightarrow{P}ʻz\cap sʻ\text{ᗡ}ʻʻ\overrightarrow{P}ʻw=\Lambda:\supset:\\ &M,N\in P_{\Delta}ʻ\alpha.\dot{s}ʻDʻM=\dot{s}ʻ\text{D}ʻN.\supset.M=N \quad[\text{*41·44.*33·33.*85·31}]\end{align}\] -/
theorem pm85_34 {P M N : (γ → δ → Prop) → β → Prop} {A : Set β} :
    (∀ z w, (z ∈ A ∧ w ∈ A) ∧ z ≠ w →
        sumCls (Dcnv ʻʻ refs P z) ∩ sumCls (Dcnv ʻʻ refs P w) = Λ) →
      ((M ∈ sel P A ∧ N ∈ sel P A) ∧ sumRel (dom M) = sumRel (dom N) → M = N) := by
  rintro h ⟨⟨hM, hN⟩, e⟩
  refine sel_eq_of_sumRel_dom (fun z w hz hw hzw a b h1 h2 => ?_) hM hN e
  obtain ⟨S, hS, hab⟩ := h1
  obtain ⟨T, hT, hab'⟩ := h2
  exact inter_eq_null_iff.1 (h z w ⟨⟨hz, hw⟩, hzw⟩) b ⟨codom S, ⟨S, hS, rfl⟩, a, hab⟩
    ⟨codom T, ⟨T, hT, rfl⟩, a, hab'⟩

/-- ✱85·4. \[\begin{align}\vdash\colon\ldotp &\lambda,\mu\in\kappa.\lambda\neq\mu.\supset_{\lambda,\mu}.\dot{s}ʻ\lambda\dot{\cap}\dot{s}ʻ\mu=\dot{\Lambda}:\supset:\\ &M,N\in{\in}_{\Delta}ʻ\kappa.\dot{s}ʻDʻM=\dot{s}ʻDʻN.\supset.M=N \quad\left[\text{*85·31}\, \frac{{\in}}{P}.\text{*62·2}\right]\end{align}\] -/
theorem pm85_4 {K : Set (Set (γ → δ → Prop))} {M N : (γ → δ → Prop) → Set (γ → δ → Prop) → Prop} :
    (∀ L L', (L ∈ K ∧ L' ∈ K) ∧ L ≠ L' → sumRel L ⩀ sumRel L' = rNull) →
      ((M ∈ sel memRel K ∧ N ∈ sel memRel K) ∧ sumRel (dom M) = sumRel (dom N) → M = N) :=
  fun h => pm85_31 (P := memRel) h

/-- ✱85·41. \(\vdash\colon\ldotp \kappa\in\text{Cls}^{2}\,\text{excl}.\supset:\alpha,\beta\in\kappa.\alpha\neq\beta.\supset.\dot{s}ʻP_{\Delta}ʻ\alpha\dot{\cap}\dot{s}ʻP_{\Delta}ʻ\beta=\dot{\Lambda}\) -/
theorem pm85_41 {P : α → β → Prop} {K : Set (Set β)} {A B : Set β} :
    K ∈ Cls2excl → ((A ∈ K ∧ B ∈ K) ∧ A ≠ B → sumRel (sel P A) ⩀ sumRel (sel P B) = rNull) := by
  rintro hK h
  have hd := hK A B h
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨S, hS, hxy⟩, ⟨T, hT, hxy'⟩⟩
    exact (inter_eq_null_iff.1 hd y ((sel_iff.1 hS).2.2.1 _ _ hxy)
      ((sel_iff.1 hT).2.2.1 _ _ hxy')).elim
  · intro h'
    exact (rNull_apply x y h').elim

/-- ✱85·42. \(\vdash\colon \kappa\in\text{Cls}^{2}\,\text{excl}.M,N\in{\in}_{\Delta}ʻP_{\Delta}ʻʻ\kappa.\dot{s}ʻ\text{D}ʻM=\dot{s}ʻ\text{D}ʻN.\supset.M=N\) -/
theorem pm85_42 {P : α → β → Prop} {K : Set (Set β)}
    {M N : (α → β → Prop) → Set (α → β → Prop) → Prop} :
    (K ∈ Cls2excl ∧ (M ∈ sel memRel (selRel P ʻʻ K) ∧ N ∈ sel memRel (selRel P ʻʻ K))) ∧
        sumRel (dom M) = sumRel (dom N) → M = N := by
  rintro ⟨⟨hK, hMN⟩, e⟩
  refine pm85_4 (fun L L' h => ?_) ⟨hMN, e⟩
  obtain ⟨⟨⟨A, hA, rfl⟩, ⟨B, hB, rfl⟩⟩, hne⟩ := h
  exact pm85_41 hK ⟨⟨hA, hB⟩, fun e => hne (e ▸ rfl)⟩

/-- ✱85·43. \(\vdash\colon\kappa\in\text{Cls}^{2}\,\text{excl}.\supset.P_{\Delta}ʻsʻ\kappa\,\text{ sm }\,{\in}_{\Delta}ʻP_{\Delta}ʻʻ\kappa\) -/
theorem pm85_43 {P : α → β → Prop} {K : Set (Set β)} :
    K ∈ Cls2excl → sm (sel P (sumCls K)) (sel memRel (selRel P ʻʻ K)) := by
  intro hK
  rw [sm_iff]
  refine ⟨fun M X => X ∈ sel memRel (selRel P ʻʻ K) ∧ M = sumRel (dom X), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_arrow_one_one]
    constructor
    · rintro M M' X ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
    · rintro M X X' ⟨⟨hX, rfl⟩, ⟨hX', e⟩⟩
      exact pm85_42 ⟨⟨hK, hX, hX'⟩, e⟩
  · ext M
    constructor
    · intro hM
      have h := pm85_22 hM
      exact ⟨_, h.1, h.2.symm⟩
    · rintro ⟨X, hX, rfl⟩
      exact pm85_25 ⟨hK, hX⟩
  · ext X
    exact ⟨fun hX => ⟨_, hX, rfl⟩, fun ⟨_, hX, _⟩ => hX⟩

/-- ✱85·44. \(\vdash\colon\kappa\in\text{Cls}^{2}\,\text{excl}.\supset.{\in}_{\Delta}ʻsʻ\kappa\,\text{ sm }\,{\in}_{\Delta}ʻ{\in}_{\Delta}ʻʻ\kappa \quad\left[\text{*85·43}\,\frac{{\in}}{P}\right]\) -/
theorem pm85_44 {K : Set (Set (Set α))} :
    K ∈ Cls2excl → sm (sel memRel (sumCls K)) (sel memRel (selRel memRel ʻʻ K)) := pm85_43

/-- ✱85·45. \(\vdash\colon\kappa\cap\lambda=\Lambda.\supset.{\in}_{\Delta}ʻ\kappa\cup\lambda\,\text{ sm }\,{\in}_{\Delta}ʻ(\iotaʻ{\in}_{\Delta}ʻ\kappa\cup\iotaʻ{\in}_{\Delta}ʻ\lambda)\)

**Status.** proved: the e-text prints `∈_Δ'κ ∪ λ`; only `∈_Δ'(κ ∪ λ)` is significant (PM's proof has
`∈_Δ's'(ι'κ ∪ ι'λ)` with `s'(ι'κ ∪ ι'λ) = κ ∪ λ`), and the bracket is written. -/
theorem pm85_45 {K L : Set (Set α)} :
    K ∩ L = Λ → sm (sel memRel (K ∪ L)) (sel memRel (ι (sel memRel K) ∪ ι (sel memRel L))) := by
  intro h
  have hex : ι K ∪ ι L ∈ Cls2excl := by
    rw [mem_Cls2excl]
    rintro A B x (rfl | rfl) (rfl | rfl) hxA hxB
    · rfl
    · exact (inter_eq_null_iff.1 h x hxA hxB).elim
    · exact (inter_eq_null_iff.1 h x hxB hxA).elim
    · rfl
  have e1 : sumCls (ι K ∪ ι L) = K ∪ L := by
    ext x
    constructor
    · rintro ⟨A, rfl | rfl, hx⟩
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨K, Or.inl rfl, hx⟩
      · exact ⟨L, Or.inr rfl, hx⟩
  have e2 : selRel memRel ʻʻ (ι K ∪ ι L) = ι (sel memRel K) ∪ ι (sel memRel L) := by
    ext X
    constructor
    · rintro ⟨A, rfl | rfl, e⟩
      · exact Or.inl e
      · exact Or.inr e
    · rintro (e | e)
      · exact ⟨K, Or.inl rfl, e⟩
      · exact ⟨L, Or.inr rfl, e⟩
  have := pm85_44 hex
  rw [e1, e2] at this
  exact this

/-- ✱85·5 (Df). \(P\unicode{x21A7}y=\downarrow yʻʻ\overrightarrow{P}ʻy \quad\text{Df}\) -/
theorem pm85_5 {P : α → β → Prop} {y : β} : P ↧ y = coupleR y ʻʻ refs P y := rfl

/-- ✱85·51. \(\vdash .P_{\Delta}ʻ\iotaʻx=\downarrow xʻʻ\overrightarrow{P}ʻ x=P \unicode{x21A7} \quad[\text{*80·45.(*85·5)}]\)

**Status.** proved (reading): transcription error: the e-text prints `P ↧` for `P ↧ x` at the end of
the chain (PM cites (✱85·5), `P ↧ y = ↓y''P⃗'y`). -/
theorem pm85_51 {P : α → β → Prop} {x : β} :
    sel P (ι x) = coupleR x ʻʻ refs P x ∧ coupleR x ʻʻ refs P x = P ↧ x := ⟨pm80_45, rfl⟩

/-- ✱85·52. \(\vdash .P_{\Delta}ʻʻ\iotaʻʻ\alpha =P\unicode{x21A7}ʻʻ\alpha \quad[\text{*37·35.*85·51}]\) -/
theorem pm85_52 {P : α → β → Prop} {A : Set β} :
    selRel P ʻʻ (iota ʻʻ A) = opL downCls P ʻʻ A := by
  ext L
  constructor
  · rintro ⟨B, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (pm85_51.1.trans pm85_51.2 : sel P (ι y) = P ↧ y)⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ι y, ⟨y, hy, rfl⟩, (pm85_51.1.trans pm85_51.2).symm⟩

theorem sumCls_iota_img {A : Set β} : sumCls (iota ʻʻ A) = A := by
  ext y
  constructor
  · rintro ⟨B, ⟨z, hz, rfl⟩, hy⟩
    have : y = z := hy
    exact this ▸ hz
  · intro hy
    exact ⟨ι y, ⟨y, hy, rfl⟩, rfl⟩

/-- ✱85·53. \(\vdash .P_{\Delta}ʻ\alpha =\dot{s}ʻʻ Dʻʻ{\in}_{\Delta}ʻ P\unicode{x21A7}ʻʻ\alpha\) -/
theorem pm85_53 {P : α → β → Prop} {A : Set β} :
    sel P A = graph sumRel ʻʻ D ʻʻ sel memRel (opL downCls P ʻʻ A) := by
  have h := pm85_27 (P := P) (pm84_241 (A := A)).1
  rw [sumCls_iota_img, pm85_52] at h
  exact h

/-- ✱85·54. \(\vdash .P_{\Delta}ʻ\alpha \text{ sm } {\in}_{\Delta}ʻ P\unicode{x21A7}ʻʻ\alpha\) -/
theorem pm85_54 {P : α → β → Prop} {A : Set β} :
    sm (sel P A) (sel memRel (opL downCls P ʻʻ A)) := by
  have h := pm85_43 (P := P) (pm84_241 (A := A)).1
  rw [sumCls_iota_img, pm85_52] at h
  exact h

/-- ✱85·55. \(\vdash . P_{\Delta}ʻ\alpha\,\text{ sm }\,\text{D}ʻʻ{\in}_{\Delta}ʻ P\unicode{x21A7}ʻʻ\alpha .P\unicode{x21A7}ʻʻ\alpha\in\text{Cls}^{2}\,\text{excl}\) -/
theorem pm85_55 {P : α → β → Prop} {A : Set β} :
    sm (sel P A) (D ʻʻ sel memRel (opL downCls P ʻʻ A)) ∧ opL downCls P ʻʻ A ∈ Cls2excl := by
  have hex : opL downCls P ʻʻ A ∈ Cls2excl := by
    rw [mem_Cls2excl]
    rintro B C S ⟨y, -, rfl⟩ ⟨z, -, rfl⟩ ⟨x, -, hx⟩ ⟨x', -, hx'⟩
    have e1 : S = x ↓ y := hx
    have e2 : S = x' ↓ z := hx'
    have : (x' ↓ z) x y := e2 ▸ e1 ▸ (⟨rfl, rfl⟩ : (x ↓ y) x y)
    rw [this.2]
  exact ⟨sm_trans pm85_54 (sm_symm (pm84_41 hex).2), hex⟩

/-- ✱85·56. \(\vdash :P\upharpoonright\alpha\in\text{Cls}\rightarrow 1.\supset .{\in}_{\Delta}ʻ\overrightarrow{P}ʻʻ\alpha\,\text{ sm }\,{\in}_{\Delta}ʻ P\unicode{x21A7}ʻʻ\alpha \quad[\text{*85·14·54}]\) -/
theorem pm85_56 {P : α → β → Prop} {A : Set β} :
    P ↾ A ∈ arrow Cls one → sm (sel memRel (Rfwd P ʻʻ A)) (sel memRel (opL downCls P ʻʻ A)) :=
  fun h => sm_trans (sm_symm (pm85_14 h)) pm85_54

/-- ✱85·6. \(\vdash . {\in}_{\Delta}ʻʻ\iotaʻʻ\kappa = \hat{\mu}\{(\exists\beta).\beta\in\kappa .\mu = \downarrow \betaʻʻ\beta\}={\in}\unicode{x21A7}ʻʻ\kappa\) -/
theorem pm85_6 {K : Set (Set α)} :
    selRel memRel ʻʻ (iota ʻʻ K) = {μ | ∃ B, B ∈ K ∧ μ = coupleR B ʻʻ B} ∧
      {μ | ∃ B, B ∈ K ∧ μ = coupleR B ʻʻ B} = opL downCls memRel ʻʻ K := by
  constructor
  · ext L
    constructor
    · rintro ⟨C, ⟨B, hB, rfl⟩, rfl⟩
      exact ⟨B, hB, pm83_4⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨ι B, ⟨B, hB, rfl⟩, pm83_4.symm⟩
  · ext L
    exact ⟨fun ⟨B, hB, e⟩ => ⟨B, hB, e⟩, fun ⟨B, hB, e⟩ => ⟨B, hB, e⟩⟩

theorem downCls_memRel_inj {A B : Set α} : memRel ↧ A = memRel ↧ B → A = B := by
  intro e
  ext x
  constructor
  · intro hx
    have : x ↓ A ∈ memRel ↧ B := e ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, e'⟩ := this
    have h1 : (x ↓ A) x A := ⟨rfl, rfl⟩
    rw [show x ↓ A = y ↓ B from e'] at h1
    rw [h1.1]
    exact hy
  · intro hx
    have : x ↓ B ∈ memRel ↧ A := e.symm ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, e'⟩ := this
    have h1 : (x ↓ B) x B := ⟨rfl, rfl⟩
    rw [show x ↓ B = y ↓ A from e'] at h1
    rw [h1.1]
    exact hy

/-- ✱85·601. \(\vdash .\in \unicode{x21A7} \alpha =\downarrow \alphaʻʻ \alpha .\in \unicode{x21A7} \alpha \text{ sm }\alpha .\in \unicode{x21A7}ʻʻ \kappa \text{ sm }\kappa .\in \unicode{x21A7} \in 1\rightarrow 1.\text{E}!\in \unicode{x21A7}ʻ\alpha \) -/
theorem pm85_601 {A : Set α} {K : Set (Set α)} :
    (((memRel ↧ A = coupleR A ʻʻ A ∧ sm (memRel ↧ A) A) ∧ sm (opL downCls memRel ʻʻ K) K) ∧
        opL downCls (memRel : α → Set α → Prop) ∈ arrow one one) ∧
      EDesc (opL downCls memRel) A := by
  refine ⟨⟨⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩, EDesc_graph _ _⟩
  · have := pm83_41 (A := A)
    rw [pm83_4] at this
    exact this
  · rw [sm_iff]
    refine ⟨fun L B => B ∈ K ∧ L = memRel ↧ B, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_arrow_one_one]
      constructor
      · rintro L L' B ⟨⟨-, rfl⟩, ⟨-, rfl⟩⟩; rfl
      · rintro L B B' ⟨⟨-, rfl⟩, ⟨-, e⟩⟩
        exact downCls_memRel_inj e
    · ext L
      exact ⟨fun ⟨B, hB, e⟩ => ⟨B, hB, e⟩, fun ⟨B, hB, e⟩ => ⟨B, hB, e⟩⟩
    · ext B
      exact ⟨fun hB => ⟨_, hB, rfl⟩, fun ⟨_, hB, _⟩ => hB⟩
  · rw [mem_arrow_one_one]
    constructor
    · rintro L L' B ⟨h, h'⟩
      exact (h : L = memRel ↧ B).trans (h' : L' = memRel ↧ B).symm
    · rintro L B B' ⟨h, h'⟩
      exact downCls_memRel_inj ((h : L = memRel ↧ B).symm.trans h')

/-- ✱85·61. \(\vdash .\in \unicode{x21A7}ʻʻ \kappa \in \text{Cls}^{2}\text{excl}.{\in}_{\Delta}ʻ \kappa =\dot{s}ʻʻ \text{D}ʻʻ {\in}_{\Delta}ʻ \in \unicode{x21A7} ʻʻ \kappa .{\in}_{\Delta}ʻ \kappa \text{ sm }{\in}_{\Delta}ʻ \in \unicode{x21A7}ʻʻ \kappa \quad\left[\text{*85·53·54·55}\,\frac{{\in}}{P}\right]\) -/
theorem pm85_61 {K : Set (Set α)} :
    (opL downCls memRel ʻʻ K ∈ Cls2excl ∧
        sel memRel K = graph sumRel ʻʻ D ʻʻ sel memRel (opL downCls memRel ʻʻ K)) ∧
      sm (sel memRel K) (sel memRel (opL downCls memRel ʻʻ K)) :=
  ⟨⟨pm85_55.2, pm85_53⟩, pm85_54⟩

/-- ✱85·62. \(\vdash :\exists !{\in}_{\Delta}ʻ \kappa .\equiv .\exists !{\in}_{\Delta}ʻ \in \unicode{x21A7} ʻʻ \kappa \quad[\text{*85·61.*73·36}]\) -/
theorem pm85_62 {K : Set (Set α)} :
    (sel memRel K).Nonempty ↔ (sel memRel (opL downCls memRel ʻʻ K)).Nonempty :=
  sm_nonempty_iff pm85_54

/-- ✱85·63. \(\vdash :\in \unicode{x21A7}ʻʻ \text{Cl ex}ʻ \alpha \in \text{Cls ex}^{2}\text{excl}:\exists !{\in}_{\Delta}ʻ \text{Cl}\,\text{ex}ʻ \alpha .\equiv .\exists !{\in}_{\Delta}ʻ \in \unicode{x21A7}ʻʻ \text{Cl ex}ʻ \alpha\) -/
theorem pm85_63 {A : Set α} :
    opL downCls memRel ʻʻ clEx A ∈ ClsEx2excl ∧
      ((sel memRel (clEx A)).Nonempty ↔ (sel memRel (opL downCls memRel ʻʻ clEx A)).Nonempty) := by
  refine ⟨⟨pm85_55.2, fun hn => (null_not_mem_iff (K := opL downCls memRel ʻʻ clEx A)).2 ?_ hn⟩,
    pm85_62⟩
  rintro L ⟨B, ⟨-, ⟨x, hx⟩⟩, rfl⟩
  exact ⟨x ↓ B, x, hx, rfl⟩

/-- ✱85·7. \[\begin{align}\vdash \colon\ldotp \beta \in \lambda .\supset _{\beta }.Rʻ \beta \subset \beta :M\in\, &{\in}_{\Delta}ʻ Rʻʻ \lambda :\supset.\\ &M\mid R\upharpoonright \lambda \in {\in}_{\Delta}ʻ \lambda .\text{D}ʻ (M\mid R\upharpoonright \lambda )=\text{D}ʻ M\end{align}\] -/
theorem pm85_7 {R : Set α → Set α → Prop} {L : Set (Set α)} {M : α → Set α → Prop} :
    (∀ B, B ∈ L → Desc R B (fun C => C ⊆ B)) ∧ M ∈ sel memRel (R ʻʻ L) →
      M ⨾ R ↾ L ∈ sel memRel L ∧ dom (M ⨾ R ↾ L) = dom M := by
  rintro ⟨h, hM⟩
  have hs := sel_iff.1 hM
  have hu : ∀ B, B ∈ L → ∀ C C', R C B → R C' B → C = C' := by
    intro B hB C C' hC hC'
    obtain ⟨⟨b, hb⟩, -⟩ := desc_iff.1 (h B hB)
    exact ((hb C).1 hC).trans ((hb C').1 hC').symm
  refine ⟨?_, ?_⟩
  · rw [sel_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro x x' B ⟨⟨C, hxC, hCB⟩, hB⟩ ⟨⟨C', hxC', hCB'⟩, -⟩
      rw [hu B hB C C' hCB hCB'] at hxC
      exact hs.1 x x' C' hxC hxC'
    · rintro x B ⟨⟨C, hxC, hCB⟩, hB⟩
      exact (desc_iff.1 (h B hB)).2 C hCB (hs.2.1 x C hxC)
    · rintro x B ⟨-, hB⟩
      exact hB
    · intro B hB
      obtain ⟨⟨C, hC⟩, -⟩ := desc_iff.1 (h B hB)
      obtain ⟨x, hx⟩ := hs.2.2.2 C ⟨B, hB, (hC C).2 rfl⟩
      exact ⟨x, ⟨C, hx, (hC C).2 rfl⟩, hB⟩
  · ext x
    constructor
    · rintro ⟨B, ⟨C, hxC, -⟩, -⟩
      exact ⟨C, hxC⟩
    · rintro ⟨C, hxC⟩
      obtain ⟨B, hB, hCB⟩ := hs.2.2.1 x C hxC
      exact ⟨B, ⟨C, hxC, hCB⟩, hB⟩

/-- ✱85·701. \(\vdash \colon\ldotp \beta \in \lambda .\supset _{\beta }.Rʻ \beta \subset \beta :\supset .\text{D}ʻʻ {\in}_{\Delta}ʻ Rʻʻ \lambda \subset \text{D}ʻʻ {\in}_{\Delta}ʻ \lambda \quad[\text{*85·7}]\) -/
theorem pm85_701 {R : Set α → Set α → Prop} {L : Set (Set α)} :
    (∀ B, B ∈ L → Desc R B (fun C => C ⊆ B)) → D ʻʻ sel memRel (R ʻʻ L) ⊆ D ʻʻ sel memRel L := by
  rintro h μ ⟨M, hM, rfl⟩
  have := pm85_7 ⟨h, hM⟩
  exact ⟨_, this.1, this.2.symm⟩

/-- ✱85·702. \[\begin{align}&\vdash \colon\ldotp \beta \in \lambda .\supset _{\beta }.Rʻ\text{Cl}ʻ \beta \in\text{Cl}ʻ\beta :\supset .\text{D}ʻʻ {\in}_{\Delta}ʻ Rʻʻ\text{Cl}ʻʻ \lambda \subset \text{D}ʻʻ {\in}_{\Delta}ʻ \lambda\\ &\quad\left[\text{*85·701}\frac{R\mid \text{Cl}}{R}\right]\end{align}\] -/
theorem pm85_702 {R : Set α → Set (Set α) → Prop} {L : Set (Set α)} :
    (∀ B, B ∈ L → Desc R (cl B) (fun C => C ∈ cl B)) →
      D ʻʻ sel memRel (R ʻʻ Cl ʻʻ L) ⊆ D ʻʻ sel memRel L := by
  intro h
  have e : R ʻʻ Cl ʻʻ L = (R ⨾ Cl) ʻʻ L := by
    ext C
    constructor
    · rintro ⟨K, ⟨B, hB, hK⟩, hCK⟩
      exact ⟨B, hB, K, hCK, hK⟩
    · rintro ⟨B, hB, K, hCK, hK⟩
      exact ⟨K, ⟨B, hB, hK⟩, hCK⟩
  rw [e]
  apply pm85_701
  intro B hB
  have hf : (fun C => (R ⨾ Cl) C B) = (fun C => R C (cl B)) := by
    funext C
    apply propext
    constructor
    · rintro ⟨K, hCK, hK⟩
      have hK' : K = cl B := hK
      exact hK' ▸ hCK
    · intro hC
      exact ⟨cl B, hC, rfl⟩
  show TheIs (fun C => (R ⨾ Cl) C B) _
  rw [hf]
  exact h B hB

/-- ✱85·71. \(\vdash :R\in {\in}_{\Delta}ʻ\text{Cl}ʻʻ\lambda .\supset .\text{D}ʻʻ {\in}_{\Delta}ʻ\text{D}ʻ R\subset \text{D}ʻʻ {\in}_{\Delta}ʻ \lambda \quad[\text{*85·702.*83·2}]\) -/
theorem pm85_71 {R : Set α → Set (Set α) → Prop} {L : Set (Set α)} :
    R ∈ sel memRel (Cl ʻʻ L) → D ʻʻ sel memRel (dom R) ⊆ D ʻʻ sel memRel L := by
  intro hR
  have e : dom R = R ʻʻ Cl ʻʻ L := (pm80_34 hR).2.symm
  rw [e]
  apply pm85_702
  intro B hB
  exact (pm83_2 hR).2.1 ((pm83_2 hR).1.1 ⟨B, hB, rfl⟩)

/-- ✱85·72. \[\begin{align}\vdash \colon\ldotp (Sʻʻ \beta )\upharpoonleft S\in 1\rightarrow 1:\beta \in \lambda .\supset _{\beta }.Rʻ \beta &\subset Sʻ \beta :\supset.\\ &\text{D}ʻʻ {\in}_{\Delta}ʻ Rʻʻ \lambda \subset \text{D}ʻʻ {\in}_{\Delta}ʻ Sʻʻ \lambda\end{align}\]

**Status.** proved (reading): misprint `(S''β) ↿ S` for `(S''λ) ↿ S` in the first hypothesis: `β` is
bound only in the second conjunct, and `S''β` is not significant (the members of `β` are not of the
type of the relata of `S`); PM's proof uses ✱74·171 for `(S''λ) ↿ S`. -/
theorem pm85_72 {R S : Set γ → Set α → Prop} {L : Set (Set α)} :
    (S ʻʻ L) ◁ S ∈ arrow one one ∧
        (∀ B, B ∈ L → Desc R B (fun C => Desc S B (fun E => C ⊆ E))) →
      D ʻʻ sel memRel (R ʻʻ L) ⊆ D ʻʻ sel memRel (S ʻʻ L) := by
  rintro ⟨h11, h⟩ μ ⟨M, hM, rfl⟩
  rw [mem_arrow_one_one] at h11
  have hs := sel_iff.1 hM
  have hR : ∀ B, B ∈ L → ∃ C, R C B ∧ (∀ C', R C' B → C' = C) ∧
      ∃ E, S E B ∧ (∀ E', S E' B → E' = E) ∧ C ⊆ E := by
    intro B hB
    obtain ⟨C, hC, hψ⟩ := h B hB
    obtain ⟨E, hE, hCE⟩ := hψ
    exact ⟨C, (hC C).2 rfl, fun C' h' => (hC C').1 h', E, (hE E).2 rfl, fun E' h' => (hE E').1 h',
      hCE⟩
  refine ⟨fun x E => E ∈ S ʻʻ L ∧ ∃ C B, B ∈ L ∧ S E B ∧ R C B ∧ M x C, ?_, ?_⟩
  · rw [sel_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro x x' E ⟨hE, C, B, hB, hEB, hCB, hxC⟩ ⟨-, C', B', hB', hEB', hCB', hxC'⟩
      have e1 : B = B' := h11.2 E B B' ⟨⟨hE, hEB⟩, ⟨hE, hEB'⟩⟩
      subst e1
      obtain ⟨C0, -, hu, -⟩ := hR B hB
      rw [hu C hCB, ← hu C' hCB'] at hxC
      exact hs.1 x x' C' hxC hxC'
    · rintro x E ⟨-, C, B, hB, hEB, hCB, hxC⟩
      obtain ⟨C0, -, hu, E0, -, huE, hsub⟩ := hR B hB
      rw [huE E hEB]
      exact hsub (hu C hCB ▸ hs.2.1 x C hxC)
    · rintro x E ⟨hE, -⟩
      exact hE
    · rintro E ⟨B, hB, hEB⟩
      obtain ⟨C, hCB, -, -⟩ := hR B hB
      obtain ⟨x, hx⟩ := hs.2.2.2 C ⟨B, hB, hCB⟩
      exact ⟨x, ⟨B, hB, hEB⟩, C, B, hB, hEB, hCB, hx⟩
  · ext x
    constructor
    · rintro ⟨C, hxC⟩
      obtain ⟨B, hB, hCB⟩ := hs.2.2.1 x C hxC
      obtain ⟨-, -, -, E, hEB, -, -⟩ := hR B hB
      exact ⟨E, ⟨B, hB, hEB⟩, C, B, hB, hEB, hCB, hxC⟩
    · rintro ⟨E, -, C, B, -, -, -, hxC⟩
      exact ⟨C, hxC⟩

/-- ✱85·81. \[\begin{align}\vdash\colon\ldotp \lambda\in \text{Cls}^{2}\text{excl}:\beta\in\lambda.\supset_{\beta}.sʻ\text{ᗡ}ʻʻTʻ&\beta\subset\beta:R\in{\in}_{\Delta}ʻTʻʻ\lambda:\supset:\\ &\beta\in\lambda.\supset_{\beta}.(\breve{s}ʻ\text{D}ʻR)\upharpoonright \beta=RʻTʻ\beta\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `s̆'D'R` for `ṡ'D'R` (the
relational sum of ✱41, which PM's proof cites as ✱41·11·13). -/
theorem pm85_81 {T : Set (γ → δ → Prop) → Set δ → Prop} {L : Set (Set δ)}
    {R : (γ → δ → Prop) → Set (γ → δ → Prop) → Prop} :
    (L ∈ Cls2excl ∧ (∀ B, B ∈ L → Desc T B (fun X => sumCls (Dcnv ʻʻ X) ⊆ B))) ∧
        R ∈ sel memRel (T ʻʻ L) →
      ∀ B, B ∈ L → Desc2 R T B (fun S => sumRel (dom R) ↾ B = S) := by
  rintro ⟨⟨hL, hT⟩, hR⟩ B hB
  rw [mem_Cls2excl] at hL
  rw [desc2_iff]
  have hs := sel_iff.1 hR
  have hT' : ∀ X B', B' ∈ L → T X B' → sumCls (Dcnv ʻʻ X) ⊆ B' :=
    fun X B' hB' hX => (desc_iff.1 (hT B' hB')).2 X hX
  obtain ⟨⟨X, hX⟩, -⟩ := desc_iff.1 (hT B hB)
  rw [desc_iff_of ((hX X).2 rfl) (fun X' h' => (hX X').1 h')]
  obtain ⟨S, hS, hu⟩ := sel_ex hR ⟨B, hB, (hX X).2 rfl⟩
  rw [desc_iff_of hS hu]
  funext a b
  apply propext
  constructor
  · rintro ⟨⟨S', ⟨X', hS'X'⟩, hab⟩, hbB⟩
    obtain ⟨B', hB', hX'B'⟩ := hs.2.2.1 S' X' hS'X'
    have hS'mem : S' ∈ X' := hs.2.1 S' X' hS'X'
    have hbB' : b ∈ B' := hT' X' B' hB' hX'B' ⟨codom S', ⟨S', hS'mem, rfl⟩, a, hab⟩
    have e1 : B = B' := hL B B' b hB hB' hbB hbB'
    subst e1
    have e2 : X' = X := (hX X').1 hX'B'
    subst e2
    rw [← hu S' hS'X']
    exact hab
  · intro hab
    refine ⟨⟨S, ⟨X, hS⟩, hab⟩, ?_⟩
    exact hT' X B hB ((hX X).2 rfl) ⟨codom S, ⟨S, hs.2.1 S X hS, rfl⟩, a, hab⟩

/-!
## [✱88] Conditions for the existence of selections

*(Vol. 1, p. 561)*

> *Summary of* *88.
>
> The existence of selections cannot, so far as is known at present, be proved in general. That is, we cannot prove any of the following: \[ \begin{align} &(P,\kappa):\kappa\subset\text{ᗡ}ʻP.\supset.\exists!P_{\Delta}ʻ\kappa\\ &(P,\kappa):P\in\text{Cls}\rightarrow 1.\kappa\subset\text{ᗡ}ʻP.\supset.\exists!P_{\Delta}ʻ\kappa\\ &(P).\exists!P_{\Delta}ʻ\text{ᗡ}ʻ\\ &(\kappa):\Lambda{\sim}\in\kappa.\supset.\exists!{\in}_{\Delta}ʻ\kappa\\ &(\kappa):\kappa\in \text{Cls ex}^{2}\text{excl}.\supset.\exists!{\in}_{\Delta}ʻ\kappa\\ &(\alpha).\exists!{\in}_{\Delta}ʻ\text{Cl ex}ʻ\alpha\\ &(\kappa)\colon\ldotp \kappa\in \text{Cls ex}^{2}\text{excl}.\supset:(\exists \mu):\alpha\in\kappa.\supset_\alpha.\mu\cap\alpha\in 1 \end{align} \]
>
> These various propositions can be shown to be all equivalent *inter se*; and in virtue of Zermelo's theorem (cf. *258), they are equivalent to the proposition "every class can be well-ordered." In the present number we have to prove the above equivalences, as well as certain propositions giving the existence of selections in various particular cases.
>
> …

**Lean reading.** `Rel Mult`, `Cls² Mult` and `Mult ax` are `RelMult`, `Cls2Mult` and `MultAx α`.
`Mult ax` is typically ambiguous and is taken at the type that the enunciation determines: that of
the members of the classes concerned, and for relations that of their referents (whose classes
`R⃗'y` must be selected from). `Mult ax` is a theorem of Lean (`multAx_holds`), so each equivalence
`Mult ax . ≡ . p` (✱88·3–✱88·39) is proved (reading); where PM's argument goes through in Lean
(✱88·31·32·33·37·373·38·39) it is followed, and otherwise the right-hand side is proved by
`Classical.choice` (`sel_codom_nonempty`). ✱88·3·31·32 are read with `Cls ex² excl` where the e-text
prints `Cls² excl`. `Λ ∩ Cls` is the null class of classes, `Cls − ι'Λ` is `Cls \ ι Λ`, and `Cl'κ`,
`Cl ex'α` are the values `cl K`, `clEx A`.

**Status.** proved (all propositions; ✱88·01, ✱88·02, ✱88·03 definition; ✱88·3–✱88·39 proved
(reading): Mult ax is a theorem of Lean, and ✱88·3, ✱88·31, ✱88·32 transcription error, see their
docstrings).
-/

/-- Every relation has a selection from its whole converse domain (by `Classical.choice`). -/
theorem sel_codom_nonempty (P : α → β → Prop) : (sel P (codom P)).Nonempty := by
  refine ⟨fun x y => ∃ h : y ∈ codom P, x = h.choose, ?_⟩
  rw [sel_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x x' y ⟨h, rfl⟩ ⟨h', rfl⟩
    rfl
  · rintro x y ⟨h, rfl⟩
    exact h.choose_spec
  · rintro x y ⟨h, -⟩
    exact h
  · intro y hy
    exact ⟨_, hy, rfl⟩

theorem sel_nonempty_of_subset {P : α → β → Prop} {K : Set β} (h : K ⊆ codom P) :
    (sel P K).Nonempty := by
  obtain ⟨M, hM⟩ := sel_codom_nonempty P
  exact ⟨M ↾ K, pm80_6 ⟨hM, h⟩⟩

theorem sel_memRel_nonempty {K : Set (Set α)} (h : Λ ∉ K) : (sel memRel K).Nonempty := by
  apply sel_nonempty_of_subset
  intro A hA
  obtain ⟨x, hx⟩ := null_not_mem_iff.1 h A hA
  exact ⟨x, hx⟩

/-- ✱88·01 (Df). \(\text{Rel}\,\text{Mult}=\hat{P}\{\exists!P_{\Delta}ʻ \text{ᗡ}ʻ P\} \quad\text{Df}\) -/
theorem pm88_01 : (RelMult : Set (α → β → Prop)) = {P | (sel P (codom P)).Nonempty} := rfl

/-- ✱88·02 (Df). \(\text{Cls}^{2}\,\text{Mult}=\hat{\kappa} \{\exists!{\in}_{\Delta}ʻ \kappa\} \quad\text{Df}\) -/
theorem pm88_02 : (Cls2Mult : Set (Set (Set α))) = {K | (sel memRel K).Nonempty} := rfl

/-- ✱88·03 (Df). \(\text{Mult ax}.=\colon\ldotp \kappa\in \text{Cls}\,\text{ex}^{2}\,\text{excl}.\supset_{\kappa}:(\exists \mu ):\alpha \in \kappa.\supset_{\alpha }.\mu \cap \alpha \in 1 \quad\text{Df}\) -/
theorem pm88_03 :
    MultAx α ↔ ∀ K : Set (Set α), K ∈ ClsEx2excl → ∃ M : Set α, ∀ A, A ∈ K → M ∩ A ∈ one :=
  Iff.rfl

/-- ✱88·1. \(\vdash:P\in \text{Rel}\,\text{Mult}.\equiv .\exists !P_{\Delta}ʻ\text{ᗡ}ʻP \quad[\text{*20·3.(*88·01)}]\) -/
theorem pm88_1 {P : α → β → Prop} : P ∈ RelMult ↔ (sel P (codom P)).Nonempty := Iff.rfl

/-- ✱88·11. \(\vdash:P\in \text{Rel}\,\text{Mult}.\lambda \subset \text{ᗡ}ʻ P.\supset .\exists !P_{\Delta}ʻ\lambda\) -/
theorem pm88_11 {P : α → β → Prop} {L : Set β} :
    P ∈ RelMult ∧ L ⊆ codom P → (sel P L).Nonempty := by
  rintro ⟨⟨M, hM⟩, hL⟩
  exact ⟨M ↾ L, pm80_6 ⟨hM, hL⟩⟩

/-- ✱88·12. \(\vdash\colon\ldotp P\in \text{Rel Mult}\ldotp \equiv :\lambda \subset \text{ᗡ}ʻP\ldotp \supset _{\lambda }\ldotp \exists !P_{\Delta }ʻ\lambda \) -/
theorem pm88_12 {P : α → β → Prop} :
    P ∈ RelMult ↔ ∀ L, L ⊆ codom P → (sel P L).Nonempty :=
  ⟨fun h _ hL => pm88_11 ⟨h, hL⟩, fun h => h _ subset_rfl⟩

/-- ✱88·13. \(\vdash:P\in \text{Rel Mult}\ldotp \equiv \ldotp \exists !{\in}_{\Delta }ʻP\unicode{x21A7} ʻʻ\text{ᗡ}ʻP\quad [\text{*85·54.*73·36.*88·1}]\) -/
theorem pm88_13 {P : α → β → Prop} :
    P ∈ RelMult ↔ (sel memRel (opL downCls P ʻʻ codom P)).Nonempty := sm_nonempty_iff pm85_54

/-- ✱88·14. \(\vdash\colon\ldotp \kappa \subset \text{ᗡ}ʻP\ldotp \supset :P\upharpoonright \kappa \in \text{Rel Mult}\ldotp \equiv \ldotp \exists !P_{\Delta }ʻ\kappa \) -/
theorem pm88_14 {P : α → β → Prop} {K : Set β} :
    K ⊆ codom P → (P ↾ K ∈ RelMult ↔ (sel P K).Nonempty) := by
  intro h
  have e : codom (P ↾ K) = K := by
    ext y
    constructor
    · rintro ⟨x, -, hy⟩; exact hy
    · intro hy
      obtain ⟨x, hx⟩ := h hy
      exact ⟨x, hx, hy⟩
  rw [pm88_1, e, ← pm80_23]

/-- ✱88·15. \(\vdash\colon\ldotp \text{ᗡ}ʻP=\text{V}\ldotp \supset :P\upharpoonright \kappa \in \text{Rel Mult}\ldotp \equiv \ldotp \exists !P_{\Delta }ʻ\kappa \quad [\text{*88·14.*24·11}]\) -/
theorem pm88_15 {P : α → β → Prop} {K : Set β} :
    codom P = V → (P ↾ K ∈ RelMult ↔ (sel P K).Nonempty) := by
  intro h
  apply pm88_14
  rw [h, V_eq_univ]
  exact Set.subset_univ K

/-- ✱88·2. \(\vdash:\kappa \in \text{Cls}^{2}\text{Mult}\ldotp \equiv \ldotp \exists !{\in}_{\Delta }ʻ\kappa \quad [\text{*20·3.(*88·02)}]\) -/
theorem pm88_2 {K : Set (Set α)} : K ∈ Cls2Mult ↔ (sel memRel K).Nonempty := Iff.rfl

/-- ✱88·21. \(\vdash:P\in\text{Rel Mult}\ldotp \equiv \ldotp P\unicode{x21A7} ʻʻ\text{ᗡ}ʻP\in \text{Cls}^{2}\text{Mult} \quad [\text{*88·13·2}]\) -/
theorem pm88_21 {P : α → β → Prop} : P ∈ RelMult ↔ opL downCls P ʻʻ codom P ∈ Cls2Mult :=
  pm88_13

/-- ✱88·22. \(\vdash:\kappa \in \text{Cls}^{2}\text{Mult}\ldotp \lambda \subset \kappa \ldotp \supset \ldotp \lambda \in\text{Cls}^{2}\text{Mult}\) -/
theorem pm88_22 {K L : Set (Set α)} : K ∈ Cls2Mult ∧ L ⊆ K → L ∈ Cls2Mult := by
  rintro ⟨⟨M, hM⟩, hL⟩
  exact ⟨M ↾ L, pm80_6 ⟨hM, hL⟩⟩

/-- ✱88·23. \(\vdash:\kappa \in \text{Cls}^{2}\text{Mult}\ldotp \supset \ldotp \text{Cl}ʻ\kappa \subset \text{Cls}^{2}\text{Mult} \quad [\text{*88·22.*60·2}]\) -/
theorem pm88_23 {K : Set (Set α)} : K ∈ Cls2Mult → cl K ⊆ Cls2Mult :=
  fun h _ hL => pm88_22 ⟨h, hL⟩

/-- ✱88·24. \(\vdash\colon\ldotp P\in \text{Cls}\rightarrow 1\ldotp \supset :P\in \text{Rel Mult}\ldotp \equiv \ldotp \overrightarrow{P}ʻʻ\text{ᗡ}ʻP\in \text{Cls}^{2}\text{Mult}\) -/
theorem pm88_24 {P : α → β → Prop} :
    P ∈ arrow Cls one → (P ∈ RelMult ↔ Rfwd P ʻʻ codom P ∈ Cls2Mult) := by
  intro h
  have h' : P ↾ codom P ∈ arrow Cls one := by
    rw [mem_arrow_Cls_one] at h ⊢
    exact fun x y z ⟨h1, h2⟩ => h x y z ⟨h1.1, h2.1⟩
  exact sm_nonempty_iff (pm85_14 h')

/-- ✱88·25. \(\vdash\colon\ldotp P\upharpoonright \kappa \in \text{Cls}\rightarrow 1\ldotp \kappa \subset \text{ᗡ}ʻP\ldotp \supset :P\upharpoonright \kappa \in \text{Rel Mult}\ldotp \equiv \ldotp \overrightarrow{P}ʻʻ\kappa \in \text{Cls}^{2}\text{Mult}\) -/
theorem pm88_25 {P : α → β → Prop} {K : Set β} :
    P ↾ K ∈ arrow Cls one ∧ K ⊆ codom P →
      (P ↾ K ∈ RelMult ↔ Rfwd P ʻʻ K ∈ Cls2Mult) := by
  rintro ⟨h, hK⟩
  rw [pm88_14 hK]
  exact sm_nonempty_iff (pm85_14 h)

/-- ✱88·26. \(\vdash\colon\colon \kappa\in \text{Cls}^{2}\,\text{excl}.\supset\colon\ldotp \kappa\in \text{Cls}^{2}\,\text{Mult}.\equiv:(\exists \mu):\alpha\in \kappa.\supset_{\alpha}.\mu\cap \alpha\in 1\) -/
theorem pm88_26 {K : Set (Set α)} :
    K ∈ Cls2excl → (K ∈ Cls2Mult ↔ ∃ μ : Set α, ∀ A, A ∈ K → μ ∩ A ∈ one) := by
  intro hK
  constructor
  · rintro ⟨M, hM⟩
    have : dom M ∈ D ʻʻ sel memRel K := ⟨M, hM, rfl⟩
    rw [pm84_412 hK] at this
    exact ⟨dom M, this.1⟩
  · rintro ⟨μ, hμ⟩
    have h1 : μ ∩ sumCls K ∈ D ʻʻ sel memRel K := by
      apply pm84_411
      refine ⟨fun A hA => ?_, Set.inter_subset_right⟩
      have e : μ ∩ sumCls K ∩ A = μ ∩ A := by
        ext x
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, A, hA, h2⟩, h2⟩⟩
      rw [e]
      exact hμ A hA
    obtain ⟨M, hM, -⟩ := h1
    exact ⟨M, hM⟩

/-- ✱88·3. \[\begin{align}&\vdash\colon\colon \text{Mult ax}.\equiv\colon\ldotp \kappa\in \text{Cls}^{2}\,\text{excl}.\supset_{\kappa}:(\exists \mu):\alpha\in \kappa.\supset_{\alpha}.\mu\cap \alpha\in 1\\ &[\text{*4·2.(*88·03)}]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `Cls² excl` for `Cls ex² excl`
(PM's proof `[✱4·2.(✱88·03)]`; Summary of ✱88); with `Cls² excl` the right-hand side would be false
(`κ = ι'Λ`). Mult ax is a theorem of Lean (Basic §4); here both sides are the same proposition. -/
theorem pm88_3 :
    MultAx α ↔ ∀ K : Set (Set α), K ∈ ClsEx2excl → ∃ μ : Set α, ∀ A, A ∈ K → μ ∩ A ∈ one :=
  Iff.rfl

/-- ✱88·31. \(\vdash:\text{Mult ax}.\equiv.\text{Cls}^{2}\,\text{excl}\subset\text{Cls}^{2}\,\text{Mult}\)

**Status.** proved (reading): transcription error `Cls² excl` for `Cls ex² excl`, as in ✱88·3 (with
`Cls² excl` the right-hand side would be false: `ι'Λ ∼∈ Cls² Mult`). Mult ax is a theorem of Lean
(Basic §4); the equivalence is proved without using that. -/
theorem pm88_31 : MultAx α ↔ (ClsEx2excl : Set (Set (Set α))) ⊆ Cls2Mult := by
  constructor
  · intro h K hK
    exact (pm88_26 hK.1).2 (h K hK)
  · intro h K hK
    exact (pm88_26 hK.1).1 (h hK)

/-- ✱88·32. \(\vdash\colon\ldotp \text{Mult ax}.\equiv:\kappa\in \text{Cls}^{2}\,\text{excl}.\supset_{\kappa}.\exists !{\in}_{\Delta}ʻ\kappa \quad[\text{*88·31·2}]\)

**Status.** proved (reading): transcription error `Cls² excl` for `Cls ex² excl`, as in ✱88·3. Mult
ax is a theorem of Lean (Basic §4); the equivalence is proved without using that. -/
theorem pm88_32 :
    MultAx α ↔ ∀ K : Set (Set α), K ∈ ClsEx2excl → (sel memRel K).Nonempty := pm88_31

/-- The content of ✱88·44, used in ✱88·33. -/
theorem cls2Mult_diff_null {K : Set (Set α)} : clEx (sumCls K) ∈ Cls2Mult → K \ ι Λ ∈ Cls2Mult := by
  intro h
  refine pm88_22 ⟨h, ?_⟩
  rintro A ⟨hA, hne⟩
  refine ⟨fun x hx => ⟨A, hA, hx⟩, ?_⟩
  by_contra hc
  apply hne
  rw [mem_unitCls, Null_eq_empty]
  exact Set.not_nonempty_iff_eq_empty.1 hc

/-- The content of ✱88·441, used in ✱88·33. -/
theorem cls2Mult_of_clEx {K : Set (Set α)} : Λ ∉ K ∧ clEx (sumCls K) ∈ Cls2Mult → K ∈ Cls2Mult := by
  rintro ⟨hn, h⟩
  have e : K \ ι Λ = K := by
    ext A
    exact ⟨fun h' => h'.1, fun hA => ⟨hA, fun e => hn ((e : A = Λ) ▸ hA)⟩⟩
  rw [← e]
  exact cls2Mult_diff_null h

/-- ✱88·33. \(\vdash:\text{Mult ax}.\equiv.(\alpha).\exists !{\in}_{\Delta}ʻ\text{Cl ex}ʻ\alpha\)

**Status.** proved (reading): Mult ax is a theorem of Lean (Basic §4), taken here at the type of the
members of `α`; the implication from right to left is proved from ✱88·441·26, and the right-hand
side itself by `Classical.choice`. -/
theorem pm88_33 : MultAx α ↔ ∀ A : Set α, (sel memRel (clEx A)).Nonempty := by
  constructor
  · intro _ A
    apply sel_memRel_nonempty
    rintro ⟨-, x, hx⟩
    rw [Null_eq_empty] at hx
    exact hx
  · intro h K hK
    exact (pm88_26 hK.1).1 (cls2Mult_of_clEx ⟨hK.2, h _⟩)

/-- ✱88·34. \(\vdash:\text{Mult ax}.\equiv.\text{Cls}\rightarrow 1\subset \text{Rel Mult}\)

**Status.** proved (reading): Mult ax is a theorem of Lean (Basic §4), taken at the type of the
referents (`R⃗''ᗡ'R` is a class of classes of them); both sides are proved by `Classical.choice`. -/
theorem pm88_34 : MultAx α ↔ (arrow Cls one : Set (α → β → Prop)) ⊆ RelMult :=
  ⟨fun _ P _ => sel_codom_nonempty P, fun _ => multAx_holds α⟩

/-- ✱88·35. \(\vdash:\text{Mult ax}.\equiv.(R).R\in \text{Rel Mult}\)

**Status.** proved (reading): Mult ax is a theorem of Lean (Basic §4), taken at the type of the
referents; both sides are proved by `Classical.choice`. -/
theorem pm88_35 : MultAx α ↔ ∀ R : α → β → Prop, R ∈ RelMult :=
  ⟨fun _ R => sel_codom_nonempty R, fun _ => multAx_holds α⟩

/-- ✱88·36. \(\vdash\colon\ldotp \text{Mult ax}.\equiv:\kappa\subset \text{ᗡ}ʻR.\supset_{R,\kappa}.\exists !R_{\Delta}ʻ\kappa \quad[\text{*88·35·12}]\)

**Status.** proved (reading): Mult ax is a theorem of Lean (Basic §4), taken at the type of the
referents; both sides are proved by `Classical.choice`. -/
theorem pm88_36 :
    MultAx α ↔ ∀ (R : α → β → Prop) (K : Set β), K ⊆ codom R → (sel R K).Nonempty :=
  ⟨fun _ _ _ h => sel_nonempty_of_subset h, fun _ => multAx_holds α⟩

/-- ✱88·361. \(\vdash\colon\ldotp \text{Mult ax}.\equiv:\kappa\subset \text{ᗡ}ʻR.\equiv_{R,\kappa}.\exists !R_{\Delta}ʻ\kappa \quad[\text{*88·36.*80·2}]\)

**Status.** proved (reading): Mult ax is a theorem of Lean (Basic §4), taken at the type of the
referents; both sides are proved by `Classical.choice` (and ✱80·2). -/
theorem pm88_361 :
    MultAx α ↔ ∀ (R : α → β → Prop) (K : Set β), K ⊆ codom R ↔ (sel R K).Nonempty :=
  ⟨fun _ _ _ => ⟨sel_nonempty_of_subset, pm80_2⟩, fun _ => multAx_holds α⟩

/-- ✱88·37. \(\vdash\colon\ldotp \text{Mult ax}.\equiv:\Lambda{\sim}\in \kappa.\supset_{\kappa}.\exists !{\in}_{\Delta}ʻ\kappa\)

**Status.** proved (reading): Mult ax is a theorem of Lean (Basic §4); the implication from right to
left is proved from ✱88·26, the right-hand side itself by `Classical.choice`. (The Summary of ✱88
prints `Λ ∈ κ` for `Λ ∼∈ κ`; the enunciation is as stated.) -/
theorem pm88_37 : MultAx α ↔ ∀ K : Set (Set α), Λ ∉ K → (sel memRel K).Nonempty := by
  constructor
  · exact fun _ _ h => sel_memRel_nonempty h
  · intro h K hK
    exact (pm88_26 hK.1).1 (h K hK.2)

/-- ✱88·371. \(\vdash\colon\ldotp \text{Mult ax}.\equiv:\Lambda{\sim}\in \kappa.\equiv_{\kappa}.\exists !{\in}_{\Delta}ʻ\kappa \quad[\text{*88·37.*83·1}]\)

**Status.** proved (reading): Mult ax is a theorem of Lean (Basic §4); proved from ✱88·37 and ✱83·1. -/
theorem pm88_371 : MultAx α ↔ ∀ K : Set (Set α), Λ ∉ K ↔ (sel memRel K).Nonempty := by
  rw [pm88_37]
  exact ⟨fun h K => ⟨h K, pm83_1⟩, fun h K => (h K).1⟩

/-- ✱88·372. \(\vdash\colon\ldotp \text{Mult ax}.\equiv:\Lambda\in \kappa.\equiv_{\kappa}.{\in}_{\Delta}ʻ\kappa=\Lambda \quad[\text{*88·371.Transp}]\)

**Status.** proved (reading): Mult ax is a theorem of Lean (Basic §4); proved from ✱88·371. -/
theorem pm88_372 : MultAx α ↔ ∀ K : Set (Set α), Λ ∈ K ↔ sel memRel K = Λ := by
  rw [pm88_371]
  refine forall_congr' fun K => ?_
  have e : sel memRel K = Λ ↔ ¬(sel memRel K).Nonempty := by
    rw [Null_eq_empty, Set.not_nonempty_iff_eq_empty]
  rw [e]
  tauto

/-- ✱88·373. \(\vdash:\text{Mult ax}.\equiv.\text{Cl}ʻ(\text{Cls}-\iotaʻ\Lambda)\subset \text{Cls}^{2}\,\text{Mult}\)

**Status.** proved (reading): Mult ax is a theorem of Lean (Basic §4); the implication from right to
left is proved from ✱88·26, the right-hand side itself by `Classical.choice`. -/
theorem pm88_373 : MultAx α ↔ cl (Cls \ ι Λ) ⊆ (Cls2Mult : Set (Set (Set α))) := by
  constructor
  · intro _ K hK
    apply sel_memRel_nonempty
    intro h
    exact (hK h).2 rfl
  · intro h K hK
    refine (pm88_26 hK.1).1 (h ?_)
    intro A hA
    exact ⟨by rw [Cls_eq_univ]; trivial, fun e => hK.2 ((e : A = Λ) ▸ hA)⟩

/-- ✱88·38. \(\vdash:\text{Mult ax}.\equiv.\text{Cls}-\iotaʻ\Lambda\in \text{Cls}^{2}\,\text{Mult} \quad[\text{*88·23·373}]\)

**Status.** proved (reading): Mult ax is a theorem of Lean (Basic §4); proved from ✱88·23·373. -/
theorem pm88_38 : MultAx α ↔ (Cls \ ι Λ : Set (Set α)) ∈ Cls2Mult := by
  rw [pm88_373]
  exact ⟨fun h => h (mem_cl.2 subset_rfl), fun h => pm88_23 h⟩

/-- ✱88·39. \(\vdash:\text{Mult ax}.\equiv.(\exists R).R\in 1\rightarrow \text{Cls}.R\unicode{x2abd}\in .\text{D}ʻR=\text{V}.\text{ᗡ}ʻR=\text{Cls}-\iotaʻ\Lambda\)

**Status.** proved (reading): Mult ax is a theorem of Lean (Basic §4); proved from ✱88·38 and
✱80·14. -/
theorem pm88_39 :
    MultAx α ↔ ∃ R : α → Set α → Prop,
      ((R ∈ arrow one Cls ∧ R ⪽ memRel) ∧ dom R = V) ∧ codom R = Cls \ ι Λ := by
  rw [pm88_38]
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨R, ⟨⟨(mem_sel_iff.1 hR).1, ?_⟩, (mem_sel_iff.1 hR).2⟩⟩
    rw [V_eq_univ]
    ext x
    simp only [Set.mem_univ, iff_true]
    have hx : ι x ∈ (Cls \ ι Λ : Set (Set α)) := by
      refine ⟨by rw [Cls_eq_univ]; trivial, fun e => ?_⟩
      have : x ∈ (Λ : Set α) := (e : ι x = Λ) ▸ (rfl : x = x)
      rw [Null_eq_empty] at this
      exact this
    obtain ⟨y, hy, -⟩ := sel_ex hR hx
    have : y = x := (sel_iff.1 hR).2.1 y _ hy
    exact ⟨_, this ▸ hy⟩
  · rintro ⟨R, ⟨h, -⟩, e⟩
    exact ⟨R, mem_sel_iff.2 ⟨h, e⟩⟩

/-- ✱88·4. \(\vdash.\kappa\upharpoonleft \breve{\text{Cl}}\in {\in}_{\Delta}ʻ\text{Cl}ʻʻ\kappa\) -/
theorem pm88_4 {K : Set (Set α)} : K ◁ Cl˘ ∈ sel memRel (Cl ʻʻ K) := by
  rw [sel_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro A B L ⟨-, hA⟩ ⟨-, hB⟩
    have hA' : L = cl A := hA
    have hB' : L = cl B := hB
    apply Set.Subset.antisymm
    · have : A ∈ cl B := hB' ▸ hA' ▸ (subset_rfl : A ⊆ A)
      exact this
    · have : B ∈ cl A := hA' ▸ hB' ▸ (subset_rfl : B ⊆ B)
      exact this
  · rintro A L ⟨-, hA⟩
    have hA' : L = cl A := hA
    rw [hA']
    exact (subset_rfl : A ⊆ A)
  · rintro A L ⟨hA, hL⟩
    exact ⟨A, hA, hL⟩
  · rintro L ⟨A, hA, hL⟩
    exact ⟨A, hA, hL⟩

/-- ✱88·41. \(\vdash.\text{Cl}ʻʻ\kappa\in \text{Cls}^{2}\,\text{Mult} \quad[\text{*88·4·2}]\) -/
theorem pm88_41 {K : Set (Set α)} : Cl ʻʻ K ∈ Cls2Mult := ⟨_, pm88_4⟩

/-- ✱88·411. \(\vdash.\kappa\in \text{D}ʻʻ{\in}_{\Delta}ʻ\text{Cl}ʻʻ\kappa\) -/
theorem pm88_411 {K : Set (Set α)} : K ∈ D ʻʻ sel memRel (Cl ʻʻ K) := by
  refine ⟨_, pm88_4, ?_⟩
  ext A
  exact ⟨fun hA => ⟨cl A, hA, rfl⟩, fun ⟨_, hA, _⟩ => hA⟩

/-- ✱88·42. \(\vdash:\kappa\in \text{Cls}^{2}\,\text{Mult}.\exists !\alpha.\equiv.\kappa\cup \iotaʻ\alpha\in \text{Cls}^{2}\,\text{Mult} \quad[\text{*83·904.*88·2}]\) -/
theorem pm88_42 {K : Set (Set α)} {A : Set α} :
    K ∈ Cls2Mult ∧ A.Nonempty ↔ K ∪ ι A ∈ Cls2Mult := pm83_904.symm

/-- ✱88·43. \(\vdash:sʻ\kappa\in \text{Cls}^{2}\,\text{Mult}.\supset.{\in}_{\Delta}ʻʻ\kappa\in \text{Cls}^{2}\,\text{Mult}\) -/
theorem pm88_43 {K : Set (Set (Set α))} :
    sumCls K ∈ Cls2Mult → selRel memRel ʻʻ K ∈ Cls2Mult := by
  rintro ⟨M, hM⟩
  exact ⟨_, (pm85_22 hM).1⟩

/-- ✱88·431. \[\begin{align}&\vdash\colon\ldotp \kappa\in \text{Cls}^{2}\,\text{excl}.\supset:{\in}_{\Delta}ʻʻ\kappa\in \text{Cls}^{2}\,\text{Mult}.\equiv.sʻ\kappa\in \text{Cls}^{2}\,\text{Mult}\\ &[\text{*88·2.*85·28.*37·45}]\end{align}\] -/
theorem pm88_431 {K : Set (Set (Set α))} :
    K ∈ Cls2excl → (selRel memRel ʻʻ K ∈ Cls2Mult ↔ sumCls K ∈ Cls2Mult) := by
  intro hK
  refine ⟨?_, pm88_43⟩
  rintro ⟨X, hX⟩
  exact ⟨_, pm85_25 ⟨hK, hX⟩⟩

/-- ✱88·44. \(\vdash:\text{Cl ex}ʻsʻ\kappa\in \text{Cls}^{2}\,\text{Mult}.\supset.\kappa-\iotaʻ\Lambda\in \text{Cls}^{2}\,\text{Mult} \quad[\text{*60·57.*88·22}]\) -/
theorem pm88_44 {K : Set (Set α)} : clEx (sumCls K) ∈ Cls2Mult → K \ ι Λ ∈ Cls2Mult :=
  cls2Mult_diff_null

/-- ✱88·441. \(\vdash:\Lambda{\sim}\in \kappa.\text{Cl ex}ʻsʻ\kappa\in \text{Cls}^{2}\,\text{Mult}.\supset.\kappa\in \text{Cls}^{2}\,\text{Mult} \quad[\text{*88·44}]\) -/
theorem pm88_441 {K : Set (Set α)} : Λ ∉ K ∧ clEx (sumCls K) ∈ Cls2Mult → K ∈ Cls2Mult :=
  cls2Mult_of_clEx

/-- ✱88·45. \(\vdash:\text{D}ʻR\cap \text{ᗡ}ʻR=\Lambda.P=\hat{x}\hat{\alpha}\{x\in \text{ᗡ}ʻR.\alpha=\overrightarrow{R}ʻx\cup \iotaʻx\}.\supset.P\in {\in}_{\Delta}ʻ\text{ᗡ}ʻP\) -/
theorem pm88_45 {R : α → α → Prop} {P : α → Set α → Prop} :
    dom R ∩ codom R = Λ ∧ P = (fun x A => x ∈ codom R ∧ A = refs R x ∪ ι x) →
      P ∈ sel memRel (codom P) := by
  rintro ⟨hd, rfl⟩
  rw [sel_iff]
  refine ⟨?_, ?_, fun x A h => ⟨x, h⟩, fun A h => h⟩
  · rintro x y A ⟨hx, rfl⟩ ⟨hy, e⟩
    have hxA : x ∈ refs R y ∪ ι y := e ▸ (Or.inr rfl : x ∈ refs R x ∪ ι x)
    rcases hxA with h | h
    · exact (inter_eq_null_iff.1 hd x ⟨y, h⟩ hx).elim
    · exact h
  · rintro x A ⟨-, rfl⟩
    exact Or.inr rfl

/-- ✱88·46. \[\begin{align}\vdash:\text{D}ʻR\cap \text{ᗡ}ʻR=\Lambda.\lambda=\hat{\alpha}\{(\exists x).x\in \text{ᗡ}ʻR.\alpha=\overrightarrow{R}ʻx\cup &\iotaʻx\}.\supset.\\ &\lambda\in \text{Cls}^{2}\,\text{Mult}\end{align}\] -/
theorem pm88_46 {R : α → α → Prop} {L : Set (Set α)} :
    dom R ∩ codom R = Λ ∧ L = {A | ∃ x, x ∈ codom R ∧ A = refs R x ∪ ι x} → L ∈ Cls2Mult := by
  rintro ⟨hd, rfl⟩
  have h := pm88_45 (R := R) ⟨hd, rfl⟩
  exact ⟨_, h⟩

/-- ✱88·47. \(\vdash:P=\hat{\alpha}\hat{\beta}\{\alpha\in \kappa.\beta=\iotaʻʻ\alpha\cup \iotaʻ\alpha\}.\supset.P\in {\in}_{\Delta}ʻ\text{ᗡ}ʻP\) -/
theorem pm88_47 {K : Set (Set α)} {P : Set α → Set (Set α) → Prop} :
    P = (fun A B => A ∈ K ∧ B = iota ʻʻ A ∪ ι A) → P ∈ sel memRel (codom P) := by
  rintro rfl
  rw [sel_iff]
  refine ⟨?_, ?_, fun A B h => ⟨A, h⟩, fun B h => h⟩
  · rintro A A' B ⟨-, rfl⟩ ⟨-, e⟩
    have h1 : A ∈ iota ʻʻ A' ∪ ι A' := e ▸ (Or.inr rfl : A ∈ iota ʻʻ A ∪ ι A)
    have h2 : A' ∈ iota ʻʻ A ∪ ι A := e.symm ▸ (Or.inr rfl : A' ∈ iota ʻʻ A' ∪ ι A')
    rcases h1 with ⟨a', ha', h1⟩ | h1
    · rcases h2 with ⟨a, ha, h2⟩ | h2
      · have h1' : A = ι a' := h1
        have h2' : A' = ι a := h2
        subst h1' h2'
        have : a = a' := ha
        rw [this]
      · exact (h2 : A' = A).symm
    · exact h1
  · rintro A B ⟨-, rfl⟩
    exact Or.inr rfl

/-- ✱88·48. \(\vdash.\hat{\beta}\{(\exists \alpha).\alpha\in \kappa.\beta=\iotaʻʻ\alpha\cup \iotaʻ\alpha\}\in \text{Cls}^{2}\,\text{Mult} \quad[\text{*88·47}]\) -/
theorem pm88_48 {K : Set (Set α)} :
    {B | ∃ A, A ∈ K ∧ B = iota ʻʻ A ∪ ι A} ∈ Cls2Mult := by
  have h := pm88_47 (K := K) rfl
  exact ⟨_, h⟩

/-- ✱88·5. \(\vdash.\Lambda\cap \text{Cls}\in \text{Cls}^{2}\,\text{Mult} \quad[\text{*83·9.*88·2}]\) -/
theorem pm88_5 : (Λ ∩ Cls : Set (Set α)) ∈ Cls2Mult := by
  have e : (Λ ∩ Cls : Set (Set α)) = Λ := by
    rw [Null_eq_empty, Set.empty_inter]
  rw [e]
  exact pm83_9

/-- ✱88·51. \(\vdash:\exists !\alpha.\supset.\iotaʻ\alpha\in \text{Cls}^{2}\,\text{Mult} \quad[\text{*83·901.*88·2}]\) -/
theorem pm88_51 {A : Set α} : A.Nonempty → ι A ∈ Cls2Mult := pm83_901.2

/-- ✱88·52. \(\vdash.\iotaʻʻ\alpha\in \text{Cls}^{2}\,\text{Mult} \quad[\text{*83·42}]\) -/
theorem pm88_52 {A : Set α} : iota ʻʻ A ∈ Cls2Mult := by
  show (sel memRel (iota ʻʻ A)).Nonempty
  rw [pm83_42.1]
  exact ⟨_, rfl⟩

/-- ✱88·53. \(\vdash:\kappa\subset 1.\supset.\kappa\in \text{Cls}^{2}\,\text{Mult} \quad[\text{*83·44}]\) -/
theorem pm88_53 {K : Set (Set α)} : K ⊆ one → K ∈ Cls2Mult := by
  intro h
  obtain ⟨M, hM⟩ := pm83_44 h
  exact ⟨M, by rw [hM]; rfl⟩

end PrincipiaMathematica
