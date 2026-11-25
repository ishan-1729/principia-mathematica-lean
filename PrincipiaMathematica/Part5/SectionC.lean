import PrincipiaMathematica.Defs.Part5

/-!
# Part V, Section C: On convergence, and the limits of functions

Volume 2. Numbers: ✱230, ✱231, ✱232, ✱233, ✱234.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

variable {α β : Type*}

/-! ## Helper lemmas for Section C

Private lemmas about the ancestral `P_*` (`anc P`), the restriction `Q_* ⥏ α` and the classes of
✱230–✱234, used throughout this file. -/

section Helpers

private theorem anc_left {Q : β → β → Prop} {y z : β} (h : anc Q y z) : y ∈ fld Q := h.1

private theorem anc_right {Q : β → β → Prop} {y z : β} (h : anc Q y z) : z ∈ fld Q := by
  rcases anc_iff_po.1 h with ⟨rfl, hy⟩ | hp
  · exact hy
  · rw [po_iff_transGen] at hp
    obtain ⟨b, -, hbz⟩ := Relation.TransGen.tail'_iff.1 hp
    exact ⟨b, Or.inr hbz⟩

private theorem anc_rfl {Q : β → β → Prop} {y : β} (h : y ∈ fld Q) : anc Q y y :=
  anc_iff_po.2 (Or.inl ⟨rfl, h⟩)

private theorem anc_trans' {Q : β → β → Prop} {x y z : β} (h1 : anc Q x y) (h2 : anc Q y z) :
    anc Q x z := by
  rw [anc_iff_reflTransGen] at *
  exact ⟨h1.1, h1.2.trans h2.2⟩

private theorem anc_of {Q : β → β → Prop} {x y : β} (h : Q x y) : anc Q x y :=
  anc_iff_reflTransGen.2 ⟨⟨y, Or.inl h⟩, Relation.ReflTransGen.single h⟩

private theorem fld_ancFres {Q : β → β → Prop} {S : Set β} {y : β} :
    y ∈ fld (anc Q ⥏ S) ↔ y ∈ S ∧ y ∈ fld Q := by
  constructor
  · rintro ⟨z, ⟨⟨h1, h2⟩, _⟩ | ⟨⟨_, h2⟩, h3⟩⟩
    · exact ⟨h1, anc_left h2⟩
    · exact ⟨h3, anc_right h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨y, Or.inl ⟨⟨h1, anc_rfl h2⟩, h1⟩⟩

private theorem anc_ancFres {Q : β → β → Prop} {S : Set β} {x y : β} :
    anc (anc Q ⥏ S) x y ↔ (x ∈ S ∧ anc Q x y) ∧ y ∈ S := by
  constructor
  · intro h
    obtain ⟨hx, hr⟩ := anc_iff_reflTransGen.1 h
    obtain ⟨hxS, hxQ⟩ := fld_ancFres.1 hx
    clear h
    induction hr with
    | refl => exact ⟨⟨hxS, anc_rfl hxQ⟩, hxS⟩
    | tail _ hbc ih => exact ⟨⟨hxS, anc_trans' ih.1.2 hbc.1.2⟩, hbc.2⟩
  · intro h
    exact anc_of h

private theorem eq_null_of {S : Set α} (h : ∀ x, x ∉ S) : S = Λ := by
  rw [Null_eq_empty]
  exact Set.eq_empty_iff_forall_notMem.2 h

private theorem not_mem_null {x : α} : x ∉ (Λ : Set α) := by
  rw [Null_eq_empty]
  exact fun h => h


private theorem anc_cnv {P : α → α → Prop} {x y : α} : anc P˘ x y ↔ anc P y x := ancCnv_iff.symm

private theorem po_cnv {P : α → α → Prop} {x y : α} : po P˘ x y ↔ po P y x := by
  rw [po_iff_transGen, po_iff_transGen]
  exact Relation.transGen_swap

private theorem po_cnv_eq (P : α → α → Prop) : po P˘ = (po P)˘ := by
  funext x y
  exact propext po_cnv

private theorem po_trans' {P : α → α → Prop} {x y z : α} (h1 : po P x y) (h2 : po P y z) :
    po P x z := by
  rw [po_iff_transGen] at *
  exact h1.trans h2

private theorem po_of {P : α → α → Prop} {x y : α} (h : P x y) : po P x y :=
  po_iff_transGen.2 (Relation.TransGen.single h)

private theorem anc_of_po {P : α → α → Prop} {x y : α} (h : po P x y) : anc P x y :=
  anc_iff_po.2 (Or.inr h)

private theorem anc_po_trans {P : α → α → Prop} {x y z : α} (h1 : anc P x y) (h2 : po P y z) :
    po P x z := by
  rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h
  · exact h2
  · exact po_trans' h h2

private theorem po_anc_trans {P : α → α → Prop} {x y z : α} (h1 : po P x y) (h2 : anc P y z) :
    po P x z := by
  rcases anc_iff_po.1 h2 with ⟨rfl, -⟩ | h
  · exact h1
  · exact po_trans' h1 h

private theorem po_left {P : α → α → Prop} {x y : α} (h : po P x y) : x ∈ fld P :=
  anc_left (anc_of_po h)

private theorem po_right {P : α → α → Prop} {x y : α} (h : po P x y) : y ∈ fld P :=
  anc_right (anc_of_po h)

private theorem fld_po (P : α → α → Prop) : fld (po P) = fld P := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact po_left h
    · exact po_right h
  · rintro ⟨y, h | h⟩
    · exact ⟨y, Or.inl (po_of h)⟩
    · exact ⟨y, Or.inr (po_of h)⟩

private theorem fld_anc (P : α → α → Prop) : fld (anc P) = fld P := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact anc_left h
    · exact anc_right h
  · intro h
    exact ⟨x, Or.inl (anc_rfl h)⟩

private theorem po_po {P : α → α → Prop} {x y : α} : po (po P) x y ↔ po P x y := by
  rw [po_iff_transGen, po_iff_transGen]
  constructor
  · intro h
    induction h with
    | single h => exact po_iff_transGen.1 h
    | tail _ h ih => exact ih.trans (po_iff_transGen.1 h)
  · exact fun h => Relation.TransGen.single (po_iff_transGen.2 h)

private theorem anc_po_iff {P : α → α → Prop} {x y : α} : anc (po P) x y ↔ anc P x y := by
  rw [anc_iff_po, anc_iff_po, po_po, fld_po]

private theorem anc_anc_iff {P : α → α → Prop} {x y : α} : anc (anc P) x y ↔ anc P x y := by
  constructor
  · intro h
    obtain ⟨hx, hr⟩ := anc_iff_reflTransGen.1 h
    rw [fld_anc] at hx
    clear h
    induction hr with
    | refl => exact anc_rfl hx
    | tail _ hbc ih => exact anc_trans' ih hbc
  · exact anc_of

/-- A section is closed under `P_*`-predecessors. -/
private theorem sect_anc {P : α → α → Prop} {A : Set α} (hA : A ∈ sect P) {x v : α}
    (h : anc P x v) (hv : v ∈ A) : x ∈ A := by
  obtain ⟨-, hr⟩ := anc_iff_reflTransGen.1 h
  clear h
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hxb _ ih => exact hA.2 ⟨_, ih, hxb⟩

private theorem connex_anc {P : α → α → Prop} (h : P ∈ connex) : anc P ∈ connex := by
  rw [mem_connex] at h ⊢
  rw [fld_anc]
  intro x y hxy
  rcases h x y hxy with (h1 | h1) | h1
  · exact Or.inl (Or.inl (anc_of h1))
  · exact Or.inl (Or.inr h1)
  · exact Or.inr (anc_of h1)

private theorem connex_po {P : α → α → Prop} (h : P ∈ connex) : po P ∈ connex := by
  rw [mem_connex] at h ⊢
  rw [fld_po]
  intro x y hxy
  rcases h x y hxy with (h1 | h1) | h1
  · exact Or.inl (Or.inl (po_of h1))
  · exact Or.inl (Or.inr h1)
  · exact Or.inr (po_of h1)

/-- `P_po ∈ connex` gives `P_* ∈ connex`. -/
private theorem connex_anc_of_po {P : α → α → Prop} (h : po P ∈ connex) : anc P ∈ connex := by
  rw [mem_connex] at h ⊢
  rw [fld_anc]
  rw [fld_po] at h
  intro x y hxy
  rcases h x y hxy with (h1 | h1) | h1
  · exact Or.inl (Or.inl (anc_of_po h1))
  · exact Or.inl (Or.inr h1)
  · exact Or.inr (anc_of_po h1)

private theorem connex_cnv {P : α → α → Prop} (h : P ∈ connex) : P˘ ∈ connex := by
  rw [mem_connex] at h ⊢
  rw [fld_cnv]
  intro x y hxy
  rcases h x y hxy with (h1 | h1) | h1
  · exact Or.inr h1
  · exact Or.inl (Or.inr h1)
  · exact Or.inl (Or.inl h1)

private theorem Ser_cnv {P : α → α → Prop} (h : P ∈ Ser) : P˘ ∈ Ser := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨fun x y hxy e => h1 y x hxy e.symm, ?_⟩, connex_cnv h3⟩
  rintro x z ⟨y, hxy, hyz⟩
  exact h2 z x ⟨y, hyz, hxy⟩

/-- For `P ∈ Ser`: irreflexive, transitive, connected, in a usable form. -/
private theorem Ser_parts {P : α → α → Prop} (h : P ∈ Ser) :
    ((∀ x, ¬P x x) ∧ ∀ x y z, P x y → P y z → P x z) ∧
      ∀ x y, x ∈ fld P → y ∈ fld P → (P x y ∨ x = y) ∨ P y x := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_Ser.1 h
  exact ⟨⟨h1, fun x y z a b => h2 x y z ⟨a, b⟩⟩, fun x y hx hy => h3 x y ⟨hx, hy⟩⟩

private theorem Ser_transR {P : α → α → Prop} (h : P ∈ Ser) : P ∈ transR := h.1.2

private theorem Ser_rlJ {P : α → α → Prop} (h : P ∈ Ser) : P ∈ rl J := h.1.1

private theorem Ser_connex {P : α → α → Prop} (h : P ∈ Ser) : P ∈ connex := h.2

private theorem fld_of_left {P : α → α → Prop} {x y : α} (h : P x y) : x ∈ fld P := ⟨y, Or.inl h⟩

private theorem fld_of_right {P : α → α → Prop} {x y : α} (h : P x y) : y ∈ fld P :=
  ⟨x, Or.inr h⟩

/-! ### The limiting section, unfolded -/

/-- `x ∈ P R̄_sc Q . ≡ : y ∈ C'Q ∩ ᗡ'R . ⊃_y . x ∈ P_*''R''Q⃖_*'y : x ∈ C'P` (✱231·112). -/
private theorem mem_scBar' {P : α → α → Prop} {R : α → β → Prop} {Q : β → β → Prop} {x : α} :
    x ∈ scBar P R Q ↔
      (∀ y, y ∈ fld Q ∩ codom R → x ∈ anc P ʻʻ (R ʻʻ rels (anc Q) y)) ∧ x ∈ fld P := by
  rw [mem_scBar]
  refine and_congr ⟨fun h y hy => h _ ⟨y, hy, (fun _ h => h : R ʻʻ rels (anc Q) y ⊆ R ʻʻ rels (anc Q) y)⟩, fun h A ⟨y, hy, hA⟩ => ?_⟩ Iff.rfl
  obtain ⟨v, hv, hxv⟩ := h y hy
  exact ⟨v, hA hv, hxv⟩

/-- The limiting section is closed under `P_*`-predecessors. -/
private theorem scBar_down {P : α → α → Prop} {R : α → β → Prop} {Q : β → β → Prop} {x w : α}
    (hx : x ∈ scBar P R Q) (h : anc P w x) : w ∈ scBar P R Q := by
  rw [mem_scBar'] at hx ⊢
  refine ⟨fun y hy => ?_, anc_left h⟩
  obtain ⟨v, hv, hxv⟩ := hx.1 y hy
  exact ⟨v, hv, anc_trans' h hxv⟩

/-- The limiting upper section is closed under `P_*`-successors. -/
private theorem scBar_cnv_up {P : α → α → Prop} {R : α → β → Prop} {Q : β → β → Prop}
    {x w : α} (hx : x ∈ scBar P˘ R Q) (h : anc P x w) : w ∈ scBar P˘ R Q :=
  scBar_down hx (anc_cnv.2 h)

private theorem scBar_congr {P P' : α → α → Prop} {R : α → β → Prop} {Q : β → β → Prop}
    (h1 : ∀ x y, anc P x y ↔ anc P' x y) (h2 : fld P = fld P') :
    scBar P R Q = scBar P' R Q := by
  ext x
  rw [mem_scBar', mem_scBar', h2]
  refine and_congr (forall_congr' fun y => imp_congr Iff.rfl ?_) Iff.rfl
  exact exists_congr fun v => and_congr Iff.rfl (h1 x v)

/-- `C ∈ P_*'''R'''Q⃖_*''γ . ≡ . (∃z) . z ∈ γ . C = P_*''R''Q⃖_*'z`. -/
private theorem mem_img3_img3 {P : α → α → Prop} {R : α → β → Prop} {Q : β → β → Prop}
    {S : Set β} {C : Set α} :
    C ∈ anc P ʻʻʻ R ʻʻʻ Rbwd (anc Q) ʻʻ S ↔ ∃ z, z ∈ S ∧ C = anc P ʻʻ (R ʻʻ rels (anc Q) z) := by
  constructor
  · rintro ⟨B, ⟨B', ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩

private theorem mem_prodCls_img3 {P : α → α → Prop} {R : α → β → Prop} {Q : β → β → Prop}
    {S : Set β} {x : α} :
    x ∈ prodCls (anc P ʻʻʻ R ʻʻʻ Rbwd (anc Q) ʻʻ S) ↔
      ∀ z, z ∈ S → x ∈ anc P ʻʻ (R ʻʻ rels (anc Q) z) := by
  constructor
  · intro h z hz
    exact h _ (mem_img3_img3.2 ⟨z, hz, rfl⟩)
  · intro h C hC
    obtain ⟨z, hz, rfl⟩ := mem_img3_img3.1 hC
    exact h z hz

private theorem mem_prodCls_cn {P : α → α → Prop} {R : α → β → Prop} {Q : β → β → Prop}
    {x : α} :
    x ∈ prodCls (anc P ʻʻʻ rels (cn Q) R) ↔
      ∀ z, z ∈ fld Q ∩ codom R → x ∈ anc P ʻʻ (R ʻʻ rels (anc Q) z) := by
  constructor
  · intro h z hz
    exact h _ ⟨_, ⟨z, hz, (fun _ h => h : R ʻʻ rels (anc Q) z ⊆ R ʻʻ rels (anc Q) z)⟩, rfl⟩
  · rintro h C ⟨A, ⟨y, hy, hA⟩, rfl⟩
    obtain ⟨v, hv, hxv⟩ := h y hy
    exact ⟨v, hA hv, hxv⟩

/-- `x min_P α` is unique when `P` is connected. -/
private theorem minP_unique {P : α → α → Prop} (hc : P ∈ connex) {a b : α} {S : Set α}
    (ha : minP P a S) (hb : minP P b S) : a = b := by
  rw [minP_iff] at ha hb
  rcases mem_connex.1 hc a b ⟨ha.1.2, hb.1.2⟩ with (h | h) | h
  · exact absurd h (hb.2 a ha.1.1)
  · exact h
  · exact absurd h (ha.2 b hb.1.1)

private theorem maxP_unique {P : α → α → Prop} (hc : P ∈ connex) {a b : α} {S : Set α}
    (ha : maxP P a S) (hb : maxP P b S) : a = b :=
  minP_unique (connex_cnv hc) ha hb

end Helpers

variable {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} {A B : Set α}

/-!
## [✱230] On convergents

*(Vol. 2, p. 720)*

> *Summary of* *230.
>
> …

**Lean reading.** `R Q̄_cn α` is the term `cnBar R Q A` (✱230·01) and `Q_cn` the relation `cn Q`
(✱230·02), with `R : α → β → Prop` the function, `Q : β → β → Prop` the argument-series and
`A : Set α` a class of values. `Q⃖_*'y` is `rels (anc Q) y`, `Q̆_*` is `ancCnv Q` (✱90·02),
`Q⃖_cn'R` is `rels (cn Q) R` and `Q⃗_cn'β` is `refs (cn Q) B`. The plural descriptive
function `R Q̄_cn''κ` of the term `R Q̄_cn α` (with `R`, `Q` fixed) is the image of `κ` by the
relation `graph (cnBar R Q)` of `R Q̄_cn α` to `α`. `max_Q'ᗡ'R` in ✱230·53·54 is a
description (`Desc (maxP Q) (codom R) ψ`), with the hypothesis `E!max_Q'ᗡ'R` as
`EDesc (maxP Q) (codom R)`. Most proofs unfold the definitions with `mem_cnBar`.

**Status.** proved (all propositions; ✱230·01·02 definition; ✱230·141, ✱230·321, ✱230·54 proved
(reading): transcription errors; ✱230·511 proved (corrected): false when `Q = Λ̇`, the hypothesis
`∃̇!Q` (as in ✱230·513) is added; see their docstrings)
-/

/-- ✱230·01 (Df). \(R\overline{Q} _{\text{cn}}\alpha =CʻQ\cap \text{ᗡ}ʻR\cap \hat{y} (Rʻʻ\overleftarrow{Q}_{*}ʻy\subset \alpha ) \quad\text{Df}\) -/
theorem pm230_01 : cnBar R Q A = fld Q ∩ codom R ∩ {y | R ʻʻ rels (anc Q) y ⊆ A} := rfl

/-- ✱230·02 (Df). \(Q_{\text{cn}}=\hat{R} \hat{\alpha} (\exists !R\overline{Q} _{\text{cn}}\alpha ) \quad\text{Df}\) -/
theorem pm230_02 :
    (cn Q : (α → β → Prop) → Set α → Prop) = fun R A => (cnBar R Q A).Nonempty := rfl

/-- ✱230·1. \(\vdash :y\in R\overline{Q} _{\text{cn}}\alpha .\equiv .y\in CʻQ\cap \text{ᗡ}ʻR.Rʻʻ\overleftarrow{Q}_{*}ʻy\subset \alpha \quad[(*230·01)]\) -/
theorem pm230_1 {y : β} :
    y ∈ cnBar R Q A ↔ y ∈ fld Q ∩ codom R ∧ R ʻʻ rels (anc Q) y ⊆ A := Iff.rfl

/-- ✱230·11. \[\begin{align}&\vdash :RQ_{\text{cn}}\alpha .\equiv .\exists !R\overline{Q} _{\text{cn}}\alpha .\equiv .(\exists y).y\in CʻQ\cap \text{ᗡ}ʻR.Rʻʻ\overleftarrow{Q}_{*}ʻy\subset \alpha \\ &[(*230·02)]\end{align}\]

The chain of three is the conjunction of its two links. -/
theorem pm230_11 :
    (cn Q R A ↔ (cnBar R Q A).Nonempty) ∧
      ((cnBar R Q A).Nonempty ↔ ∃ y, y ∈ fld Q ∩ codom R ∧ R ʻʻ rels (anc Q) y ⊆ A) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ✱230·12. \(\vdash :y\in R\overline{Q} _{\text{cn}}\alpha .\supset .\overleftarrow{Q}_{*}ʻy\cap \text{ᗡ}ʻR\subset R\overline{Q} _{\text{cn}}\alpha\) -/
theorem pm230_12 {y : β} : y ∈ cnBar R Q A → rels (anc Q) y ∩ codom R ⊆ cnBar R Q A := by
  intro hy z ⟨hyz, hz⟩
  rw [mem_cnBar] at hy ⊢
  exact ⟨⟨anc_right hyz, hz⟩, fun x w ⟨hzw, hxw⟩ => hy.2 x w ⟨anc_trans' hyz hzw, hxw⟩⟩

/-- ✱230·13. \(\vdash .R\overline{Q} _{\text{cn}}\alpha =(R\upharpoonright CʻQ)\overline{Q} _{\text{cn}}\alpha\) -/
theorem pm230_13 : cnBar R Q A = cnBar (R ↾ fld Q) Q A := by
  ext y
  rw [mem_cnBar, mem_cnBar]
  constructor
  · rintro ⟨⟨hy, x, hx⟩, h⟩
    exact ⟨⟨hy, x, hx, hy⟩, fun u z ⟨hyz, huz, _⟩ => h u z ⟨hyz, huz⟩⟩
  · rintro ⟨⟨hy, x, hx, -⟩, h⟩
    exact ⟨⟨hy, x, hx⟩, fun u z ⟨hyz, huz⟩ => h u z ⟨hyz, huz, anc_right hyz⟩⟩

/-- ✱230·131. \(\vdash :R\upharpoonright CʻQ=T\upharpoonright CʻQ.\supset .R\overline{Q} _{\text{cn}}\alpha =T\overline{Q} _{\text{cn}}\alpha \quad[*230·13]\) -/
theorem pm230_131 {T : α → β → Prop} : R ↾ fld Q = T ↾ fld Q → cnBar R Q A = cnBar T Q A := by
  intro h
  rw [pm230_13 (R := R), h, ← pm230_13]

/-- ✱230·14. \(\vdash :y\in R\overline{Q} _{\text{cn}}\alpha .\supset .\exists !CʻQ\cap \text{ᗡ}ʻR.\exists !\alpha \cap \text{D}ʻR\) -/
theorem pm230_14 {y : β} :
    y ∈ cnBar R Q A → (fld Q ∩ codom R).Nonempty ∧ (A ∩ dom R).Nonempty := by
  rintro ⟨⟨hy, x, hx⟩, h⟩
  exact ⟨⟨y, hy, x, hx⟩, x, h ⟨y, anc_rfl hy, hx⟩, y, hx⟩

/-- ✱230·141. \(\vdash .R\overline{Q} _{\text{cn}}\lambda =\Lambda \quad[*230·14.\text{Transp}]\)

**Status.** proved (reading): transcription error: the e-text prints `R Q̄_cn λ = Λ` (a lower-case
`λ`, i.e. an arbitrary class, for which the formula is false) for `R Q̄_cn Λ = Λ`, as the
reference ✱230·14 Transp (`∃!α ∩ D'R` fails for `α = Λ`) requires. -/
theorem pm230_141 : cnBar R Q Λ = Λ := by
  refine eq_null_of fun y hy => ?_
  obtain ⟨-, x, hx, -⟩ := pm230_14 hy
  exact not_mem_null hx

/-- ✱230·142. \(\vdash \colon\ldotp R=\dot{\Lambda} .\lor.Q=\dot{\Lambda} :\supset .R\overline{Q} _{\text{cn}}\alpha =\Lambda \quad[*230·14.\text{Transp}.*33·24]\) -/
theorem pm230_142 : R = rNull ∨ Q = rNull → cnBar R Q A = Λ := by
  intro h
  refine eq_null_of fun y hy => ?_
  obtain ⟨⟨z, ⟨w, hw⟩, x, hx⟩, -⟩ := pm230_14 hy
  rcases h with rfl | rfl
  · exact rNull_apply _ _ hx
  · rcases hw with hw | hw <;> exact rNull_apply _ _ hw

/-- ✱230·15. \(\vdash :RQ_{\text{cn}}\alpha .\supset .\exists !CʻQ\cap \text{ᗡ}ʻR.\exists !\alpha \cap \text{D}ʻR \quad[*230·14·11]\) -/
theorem pm230_15 : cn Q R A → (fld Q ∩ codom R).Nonempty ∧ (A ∩ dom R).Nonempty :=
  fun ⟨_, hy⟩ => pm230_14 hy

/-- ✱230·151. \(\vdash :RQ_{\text{cn}}\alpha .\supset .\dot{\exists} !R.\dot{\exists} !Q.\exists !\alpha \quad[*230·15]\) -/
theorem pm230_151 : cn Q R A → (rEx R ∧ rEx Q) ∧ A.Nonempty := by
  intro h
  obtain ⟨⟨y, ⟨z, hz⟩, x, hx⟩, u, hu, -⟩ := pm230_15 h
  refine ⟨⟨⟨x, y, hx⟩, ?_⟩, u, hu⟩
  rcases hz with hz | hz
  · exact ⟨y, z, hz⟩
  · exact ⟨z, y, hz⟩

/-- ✱230·152. \(\vdash \colon\ldotp R=\dot{\Lambda} .\lor.Q=\dot{\Lambda} .\lor.\alpha =\Lambda :\supset .{\sim}(RQ_{\text{cn}}\alpha ) \quad[*230·151.\text{Transp}]\) -/
theorem pm230_152 : (R = rNull ∨ Q = rNull) ∨ A = Λ → ¬cn Q R A := by
  intro h hc
  obtain ⟨⟨⟨x, y, hx⟩, ⟨z, w, hz⟩⟩, u, hu⟩ := pm230_151 hc
  rcases h with (rfl | rfl) | rfl
  · exact rNull_apply _ _ hx
  · exact rNull_apply _ _ hz
  · exact not_mem_null hu

/-- ✱230·16. \(\vdash .R\overline{Q}_{\text{cn}}\alpha =R(\overline{Q_{*}\unicode{x0294f}\text{ᗡ}ʻR})_{\text{cn}}\alpha\)

`Q_* ⥏ ᗡ'R` is `anc Q ⥏ codom R`, and `R(Q_* ⥏ ᗡ'R)‾_cn α` is `cnBar R (anc Q ⥏ codom R) A`. -/
theorem pm230_16 : cnBar R Q A = cnBar R (anc Q ⥏ codom R) A := by
  ext y
  rw [mem_cnBar, mem_cnBar, fld_ancFres]
  constructor
  · rintro ⟨⟨hy, hyR⟩, h⟩
    exact ⟨⟨⟨hyR, hy⟩, hyR⟩, fun x z ⟨hyz, hxz⟩ => h x z ⟨(anc_ancFres.1 hyz).1.2, hxz⟩⟩
  · rintro ⟨⟨⟨hyR, hy⟩, -⟩, h⟩
    exact ⟨⟨hy, hyR⟩, fun x z ⟨hyz, hxz⟩ => h x z ⟨anc_ancFres.2 ⟨⟨hyR, hyz⟩, x, hxz⟩, hxz⟩⟩

/-- ✱230·161. \(\vdash :Q_{*}\unicode{x0294f}\text{ᗡ}ʻR=S_{*}\unicode{x0294f}\text{ᗡ}ʻR.\supset .R\overline{Q} _{\text{cn}}\alpha =R\overline{S} _{\text{cn}}\alpha \quad[*230·16]\) -/
theorem pm230_161 {S : β → β → Prop} :
    anc Q ⥏ codom R = anc S ⥏ codom R → cnBar R Q A = cnBar R S A := by
  intro h
  rw [pm230_16 (Q := Q), h, ← pm230_16]

/-- ✱230·17. \(\vdash :y\in CʻQ\cap \text{ᗡ}ʻR.\supset .\exists !Rʻʻ\overleftarrow{Q}_{*}ʻy\) -/
theorem pm230_17 {y : β} : y ∈ fld Q ∩ codom R → (R ʻʻ rels (anc Q) y).Nonempty :=
  fun ⟨hy, x, hx⟩ => ⟨x, y, anc_rfl hy, hx⟩

/-- ✱230·171. \(\vdash :y\in R\overline{Q}_{\text{cn}}(\overleftarrow{P}_{*}ʻx).\supset .x\in P_{*}ʻʻRʻʻ\overleftarrow{Q}_{*}ʻy\) -/
theorem pm230_171 {x : α} {y : β} :
    y ∈ cnBar R Q (rels (anc P) x) → x ∈ anc P ʻʻ (R ʻʻ rels (anc Q) y) := by
  rintro ⟨⟨hy, v, hv⟩, h⟩
  exact ⟨v, ⟨y, anc_rfl hy, hv⟩, h ⟨y, anc_rfl hy, hv⟩⟩

/-- ✱230·21. \(\vdash :\alpha \subset \beta .\supset .R\overline{Q}_{\text{cn}}\alpha \subset R\overline{Q}_{\text{cn}}\beta \quad[*230·1.*22·44]\) -/
theorem pm230_21 : A ⊆ B → cnBar R Q A ⊆ cnBar R Q B :=
  fun h _ ⟨h1, h2⟩ => ⟨h1, h2.trans h⟩

/-- ✱230·211. \(\vdash \colon\ldotp \alpha \subset \beta .\supset :RQ_{\text{cn}}\alpha .\supset .RQ_{\text{cn}}\beta \quad[*230·21·11]\) -/
theorem pm230_211 : A ⊆ B → (cn Q R A → cn Q R B) :=
  fun h ⟨y, hy⟩ => ⟨y, pm230_21 h hy⟩

/-- ✱230·22. \(\vdash .R\overline{Q}_{\text{cn}}\alpha \cup R\overline{Q}_{\text{cn}}\beta \subset R\overline{Q}_{\text{cn}}(\alpha \cup \beta ) \quad[*230·21]\) -/
theorem pm230_22 : cnBar R Q A ∪ cnBar R Q B ⊆ cnBar R Q (A ∪ B) :=
  Set.union_subset (pm230_21 Set.subset_union_left) (pm230_21 Set.subset_union_right)

/-- ✱230·221. \(\vdash \colon\ldotp RQ_{\text{cn}}\alpha .\lor.RQ_{\text{cn}}\beta :\supset .RQ_{\text{cn}}(\alpha \cup \beta ) \quad[*230·211]\) -/
theorem pm230_221 : cn Q R A ∨ cn Q R B → cn Q R (A ∪ B) := by
  rintro (h | h)
  · exact pm230_211 Set.subset_union_left h
  · exact pm230_211 Set.subset_union_right h

/-- ✱230·23. \(\vdash .R\overline{Q}_{\text{cn}}\alpha \cap R\overline{Q}_{\text{cn}}\beta =R\overline{Q}_{\text{cn}}(\alpha \cap \beta )\) -/
theorem pm230_23 : cnBar R Q A ∩ cnBar R Q B = cnBar R Q (A ∩ B) := by
  ext y
  exact ⟨fun ⟨⟨h1, h2⟩, ⟨_, h3⟩⟩ => ⟨h1, Set.subset_inter h2 h3⟩,
    fun ⟨h1, h2⟩ => ⟨⟨h1, h2.trans Set.inter_subset_left⟩, ⟨h1, h2.trans Set.inter_subset_right⟩⟩⟩

/-- ✱230·231. \(\vdash :RQ_{\text{cn}}(\alpha \cap \beta ).\supset .RQ_{\text{cn}}\alpha .RQ_{\text{cn}}\beta \quad[*230·211]\) -/
theorem pm230_231 : cn Q R (A ∩ B) → cn Q R A ∧ cn Q R B :=
  fun h => ⟨pm230_211 Set.inter_subset_left h, pm230_211 Set.inter_subset_right h⟩

/-- ✱230·24. \(\vdash .R\overline{Q}_{\text{cn}}\alpha \cap R\overline{Q}_{\text{cn}}(\beta -\alpha )=\Lambda \quad[*230·23·141]\) -/
theorem pm230_24 : cnBar R Q A ∩ cnBar R Q (B \ A) = Λ := by
  rw [pm230_23, Set.inter_sdiff_self, ← Null_eq_empty, pm230_141]

private theorem cnBar_inter {X : Set α}
    (hX : ∀ y, y ∈ fld Q ∩ codom R → R ʻʻ rels (anc Q) y ⊆ X) :
    cnBar R Q (A ∩ X) = cnBar R Q A := by
  ext y
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.trans Set.inter_subset_left⟩,
    fun ⟨h1, h2⟩ => ⟨h1, Set.subset_inter h2 (hX y h1)⟩⟩

/-- ✱230·25. \(\vdash .R\overline{Q}_{\text{cn}}\alpha =R\overline{Q}_{\text{cn}}(\alpha \cap \text{D}ʻR)=R\overline{Q}_{\text{cn}}(\alpha \cap Rʻʻ\breve{Q} _{*}ʻʻ\text{ᗡ}ʻR)=R\overline{Q}_{\text{cn}}(\alpha \cap RʻʻCʻQ)\)

`Q̆_*''ᗡ'R` is `ancCnv Q ʻʻ codom R` (`Q̆_*` is `Cnv'Q_*`, ✱90·02); the chain of four is the
conjunction of its three links. -/
theorem pm230_25 :
    (cnBar R Q A = cnBar R Q (A ∩ dom R) ∧
        cnBar R Q (A ∩ dom R) = cnBar R Q (A ∩ R ʻʻ (ancCnv Q ʻʻ codom R))) ∧
      cnBar R Q (A ∩ R ʻʻ (ancCnv Q ʻʻ codom R)) = cnBar R Q (A ∩ R ʻʻ fld Q) := by
  have h1 : cnBar R Q (A ∩ dom R) = cnBar R Q A :=
    cnBar_inter fun _ _ x ⟨z, _, hxz⟩ => ⟨z, hxz⟩
  have h2 : cnBar R Q (A ∩ R ʻʻ (ancCnv Q ʻʻ codom R)) = cnBar R Q A :=
    cnBar_inter fun y hy x ⟨z, hyz, hxz⟩ => ⟨z, ⟨y, hy.2, hyz⟩, hxz⟩
  have h3 : cnBar R Q (A ∩ R ʻʻ fld Q) = cnBar R Q A :=
    cnBar_inter fun _ _ x ⟨z, hyz, hxz⟩ => ⟨z, anc_right hyz, hxz⟩
  rw [h1, h2, h3]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- ✱230·251. \(\vdash .R\overline{Q}_{\text{cn}}(RʻʻCʻQ)=CʻQ\cap \text{ᗡ}ʻR\) -/
theorem pm230_251 : cnBar R Q (R ʻʻ fld Q) = fld Q ∩ codom R := by
  ext y
  exact ⟨fun h => h.1, fun h => ⟨h, fun x ⟨z, hyz, hxz⟩ => ⟨z, anc_right hyz, hxz⟩⟩⟩

/-- ✱230·252. \(\vdash :RʻʻCʻQ\subset \alpha .\supset .R\overline{Q}_{\text{cn}}\alpha =CʻQ\cap \text{ᗡ}ʻR \quad[*230·25·251]\) -/
theorem pm230_252 : R ʻʻ fld Q ⊆ A → cnBar R Q A = fld Q ∩ codom R := by
  intro hA
  refine Set.Subset.antisymm (fun y h => h.1) fun y h => ?_
  apply pm230_21 hA
  rw [pm230_251]
  exact h

/-- ✱230·253. \[\begin{align}\vdash \colon\ldotp &RʻʻCʻQ\subset \alpha .\supset:RQ_{\text{cn}}\alpha.\equiv.\exists !CʻQ\cap \text{ᗡ}ʻR.\equiv .\\ &\exists !RʻʻCʻQ.\equiv .\dot{\exists} !(R\upharpoonright CʻQ) \quad[*230·11·252.*37·401.*35·64]\end{align}\]

The chain of four equivalences is the conjunction of its three links. -/
theorem pm230_253 :
    R ʻʻ fld Q ⊆ A →
      ((cn Q R A ↔ (fld Q ∩ codom R).Nonempty) ∧
          ((fld Q ∩ codom R).Nonempty ↔ (R ʻʻ fld Q).Nonempty)) ∧
        ((R ʻʻ fld Q).Nonempty ↔ rEx (R ↾ fld Q)) := by
  intro hA
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show (cnBar R Q A).Nonempty ↔ _
    rw [pm230_252 hA]
  · exact ⟨fun ⟨y, hy, x, hx⟩ => ⟨x, y, hy, hx⟩, fun ⟨x, y, hy, hx⟩ => ⟨y, hy, x, hx⟩⟩
  · exact ⟨fun ⟨x, y, hy, hx⟩ => ⟨x, y, hx, hy⟩, fun ⟨x, y, hx, hy⟩ => ⟨x, y, hy, hx⟩⟩

/-- ✱230·31. \(\vdash .sʻR\overline{Q} _{\text{cn}}ʻʻ\kappa \subset R\overline{Q} _{\text{cn}}(sʻ\kappa )\)

`R Q̄_cn''κ` is `graph (cnBar R Q) ʻʻ K`: the classes `R Q̄_cn α` for `α ∈ κ`. -/
theorem pm230_31 {K : Set (Set α)} :
    sumCls (graph (cnBar R Q) ʻʻ K) ⊆ cnBar R Q (sumCls K) := by
  rintro y ⟨C, ⟨A, hA, rfl⟩, hy⟩
  exact pm230_21 (B := sumCls K) (fun x hx => ⟨A, hA, hx⟩) hy

/-- ✱230·311. \(\vdash .Q_{\text{cn}}ʻʻ\kappa \subset \overrightarrow{Q}_{\text{cn}}ʻsʻ\kappa\) -/
theorem pm230_311 {K : Set (Set α)} : cn Q ʻʻ K ⊆ refs (cn Q) (sumCls K) := by
  rintro T ⟨A, hA, hT⟩
  exact pm230_211 (B := sumCls K) (fun x hx => ⟨A, hA, hx⟩) hT

/-- ✱230·32. \(\vdash .R\overline{Q} _{\text{cn}}(pʻ\kappa )=CʻQ\cap \text{ᗡ}ʻR\cap pʻR\overline{Q} _{\text{cn}}ʻʻ\kappa\) -/
theorem pm230_32 {K : Set (Set α)} :
    cnBar R Q (prodCls K) = fld Q ∩ codom R ∩ prodCls (graph (cnBar R Q) ʻʻ K) := by
  ext y
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro C ⟨A, hA, rfl⟩
    exact pm230_21 (A := prodCls K) (fun x (hx : x ∈ prodCls K) => hx A hA) ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x hx A hA => (h2 _ ⟨A, hA, rfl⟩).2 hx⟩

/-- ✱230·321. \(\vdash :\exists !k.\supset .R\overline{Q} _{\text{cn}}(pʻ\kappa )=pʻR\overline{Q} _{\text{cn}}ʻʻ\kappa .pʻR\overline{Q} _{\text{cn}}ʻʻ\kappa \subset CʻQ\cap \text{ᗡ}ʻR\)

**Status.** proved (reading): transcription error: the e-text prints `∃!k` for `∃!κ`. -/
theorem pm230_321 {K : Set (Set α)} :
    K.Nonempty →
      cnBar R Q (prodCls K) = prodCls (graph (cnBar R Q) ʻʻ K) ∧
        prodCls (graph (cnBar R Q) ʻʻ K) ⊆ fld Q ∩ codom R := by
  rintro ⟨A, hA⟩
  have h2 : prodCls (graph (cnBar R Q) ʻʻ K) ⊆ fld Q ∩ codom R :=
    fun y hy => (hy _ ⟨A, hA, rfl⟩).1
  refine ⟨?_, h2⟩
  rw [pm230_32]
  exact Set.inter_eq_right.2 h2

/-- ✱230·4. \(\vdash .R\overline{Q} _{\text{cn}}\alpha =\text{ᗡ}ʻR\cap \breve{Q} _{*}ʻʻ(R\overline{Q} _{\text{cn}}\alpha )\) -/
theorem pm230_4 : cnBar R Q A = codom R ∩ ancCnv Q ʻʻ cnBar R Q A := by
  ext y
  constructor
  · intro h
    exact ⟨h.1.2, y, h, anc_rfl h.1.1⟩
  · rintro ⟨hyR, z, hz, hzy⟩
    exact pm230_12 hz ⟨hzy, hyR⟩

/-- ✱230·41. \(\vdash \colon\ldotp Q_{*}\in \text{connex} .\supset :R\overline{Q} _{\text{cn}}\alpha \subset R\overline{Q} _{\text{cn}}\beta .\lor.R\overline{Q} _{\text{cn}}\beta \subset R\overline{Q} _{\text{cn}}\alpha\) -/
theorem pm230_41 : anc Q ∈ connex → cnBar R Q A ⊆ cnBar R Q B ∨ cnBar R Q B ⊆ cnBar R Q A := by
  intro hc
  rw [mem_connex] at hc
  by_contra hn
  rw [not_or, Set.not_subset, Set.not_subset] at hn
  obtain ⟨⟨y1, hy1A, hy1B⟩, ⟨y2, hy2B, hy2A⟩⟩ := hn
  have f1 : y1 ∈ fld (anc Q) := ⟨y1, Or.inl (anc_rfl hy1A.1.1)⟩
  have f2 : y2 ∈ fld (anc Q) := ⟨y2, Or.inl (anc_rfl hy2B.1.1)⟩
  rcases hc y1 y2 ⟨f1, f2⟩ with (h | rfl) | h
  · exact hy2A (pm230_12 hy1A ⟨h, hy2B.1.2⟩)
  · exact hy1B hy2B
  · exact hy1B (pm230_12 hy2B ⟨h, hy1A.1.2⟩)

/-- ✱230·42. \(\vdash \colon\ldotp Q_{*}\in \text{connex} .\supset :RQ_{\text{cn}}\alpha .RQ_{\text{cn}}\beta .\equiv .RQ_{\text{cn}}(\alpha \cap \beta )\) -/
theorem pm230_42 : anc Q ∈ connex → (cn Q R A ∧ cn Q R B ↔ cn Q R (A ∩ B)) := by
  intro hc
  refine ⟨fun ⟨⟨y1, h1⟩, ⟨y2, h2⟩⟩ => ?_, pm230_231⟩
  show (cnBar R Q (A ∩ B)).Nonempty
  rw [← pm230_23]
  rcases pm230_41 (R := R) (A := A) (B := B) hc with h | h
  · exact ⟨y1, h1, h h1⟩
  · exact ⟨y2, h h2, h2⟩

/-- ✱230·421. \(\vdash :Q_{*}\in \text{connex} .\alpha \cap \beta =\Lambda .\supset .{\sim}\{RQ_{\text{cn}}\alpha .RQ_{\text{cn}}\beta\} \quad[*230·42·141]\) -/
theorem pm230_421 : anc Q ∈ connex ∧ A ∩ B = Λ → ¬(cn Q R A ∧ cn Q R B) := by
  rintro ⟨hc, hAB⟩ h
  obtain ⟨y, hy⟩ := (pm230_42 hc).1 h
  rw [hAB, pm230_141] at hy
  exact not_mem_null hy

/-- ✱230·51. \(\vdash :RQ_{\text{cn}}\alpha .\supset .pʻ\overleftarrow{Q}_{*}ʻʻCʻQ\cap \text{ᗡ}ʻR\subset R\overline{Q} _{\text{cn}}\alpha\)

`Q⃖_*''C'Q` is `Rbwd (anc Q) ʻʻ fld Q`, and `p'Q⃖_*''C'Q ∩ ᗡ'R` is
`prodCls (Rbwd (anc Q) ʻʻ fld Q) ∩ codom R`. -/
theorem pm230_51 : cn Q R A → prodCls (Rbwd (anc Q) ʻʻ fld Q) ∩ codom R ⊆ cnBar R Q A := by
  rintro ⟨y, hy⟩ z ⟨hz, hzR⟩
  rw [mem_prodCls_Rbwd] at hz
  exact pm230_12 hy ⟨hz y hy.1.1, hzR⟩

/-- ✱230·511. \(\vdash :y\in pʻ\overleftarrow{Q}_{*}ʻʻCʻQ.\supset .\overleftarrow{Q}_{*}ʻy=pʻ\overleftarrow{Q}_{*}ʻʻCʻQ\)

**Status.** proved (corrected): false as printed when `C'Q = Λ`: then `p'Q⃖_*''C'Q = p'Λ = V`
(✱40·2) contains every `y`, but `Q⃖_*'y = Λ` (`pm230_511_printed_false`, with `Q = Λ̇`). PM's
demonstration uses `y ∈ C'Q`, which follows from the hypothesis only when `C'Q` has a member.
The hypothesis `∃̇!Q` (as in ✱230·513, which uses ✱230·511 under it) is added. -/
theorem pm230_511 {y : β} :
    rEx Q ∧ y ∈ prodCls (Rbwd (anc Q) ʻʻ fld Q) →
      rels (anc Q) y = prodCls (Rbwd (anc Q) ʻʻ fld Q) := by
  rintro ⟨⟨a, b, hab⟩, hy⟩
  rw [mem_prodCls_Rbwd] at hy
  have hyQ : y ∈ fld Q := anc_right (hy a ⟨b, Or.inl hab⟩)
  ext z
  rw [mem_prodCls_Rbwd]
  exact ⟨fun hyz w hw => anc_trans' (hy w hw) hyz, fun h => h y hyQ⟩

/-- The printed form of ✱230·511 is false, for the null relation `Q` (on `Unit`). -/
theorem pm230_511_printed_false :
    ¬∀ (Q : Unit → Unit → Prop) (y : Unit),
      y ∈ prodCls (Rbwd (anc Q) ʻʻ fld Q) → rels (anc Q) y = prodCls (Rbwd (anc Q) ʻʻ fld Q) := by
  intro h
  have hf : ∀ y : Unit, y ∉ fld (fun _ _ : Unit => False) := fun y ⟨z, hz⟩ => by simp at hz
  have hp : () ∈ prodCls (Rbwd (anc (fun _ _ : Unit => False)) ʻʻ fld (fun _ _ : Unit => False)) :=
    mem_prodCls_Rbwd.2 fun x hx => absurd hx (hf x)
  have := h _ () hp
  rw [← this] at hp
  exact hf () hp.1

/-- ✱230·512. \(\vdash :\text{ᗡ}ʻR\cap pʻ\overleftarrow{Q}_{*}ʻʻCʻQ\subset R\overline{Q} _{\text{cn}}\alpha .\supset .Rʻʻpʻ\overleftarrow{Q}_{*}ʻʻCʻQ\subset \alpha\) -/
theorem pm230_512 :
    codom R ∩ prodCls (Rbwd (anc Q) ʻʻ fld Q) ⊆ cnBar R Q A →
      R ʻʻ prodCls (Rbwd (anc Q) ʻʻ fld Q) ⊆ A := by
  intro h x ⟨z, hz, hxz⟩
  have hzc := h ⟨⟨x, hxz⟩, hz⟩
  exact hzc.2 ⟨z, anc_rfl hzc.1.1, hxz⟩

/-- ✱230·513. \(\vdash \colon\ldotp \dot{\exists} !Q.\supset :Rʻʻpʻ\overleftarrow{Q}_{*}ʻʻCʻQ\subset \alpha .\equiv .\text{ᗡ}ʻR\cap pʻ\overleftarrow{Q}_{*}ʻʻCʻQ\subset R\overline{Q} _{\text{cn}}\alpha\) -/
theorem pm230_513 :
    rEx Q →
      (R ʻʻ prodCls (Rbwd (anc Q) ʻʻ fld Q) ⊆ A ↔
        codom R ∩ prodCls (Rbwd (anc Q) ʻʻ fld Q) ⊆ cnBar R Q A) := by
  intro hQ
  refine ⟨fun h y ⟨hyR, hy⟩ => ?_, pm230_512⟩
  have heq := pm230_511 ⟨hQ, hy⟩
  obtain ⟨a, b, hab⟩ := hQ
  rw [mem_prodCls_Rbwd] at hy
  refine ⟨⟨anc_right (hy a ⟨b, Or.inl hab⟩), hyR⟩, ?_⟩
  show R ʻʻ rels (anc Q) y ⊆ A
  rw [heq]
  exact h

/-- ✱230·514. \(\vdash : \dot{\exists} ! Q. \exists !pʻ\overleftarrow{Q}_{*}ʻʻCʻQ \cap \text{ᗡ}ʻR . Rʻʻpʻ\overleftarrow{Q}_{*}ʻʻCʻQ\subset \alpha . \supset . RQ_{\text{cn}}\alpha\) -/
theorem pm230_514 :
    (rEx Q ∧ (prodCls (Rbwd (anc Q) ʻʻ fld Q) ∩ codom R).Nonempty) ∧
        R ʻʻ prodCls (Rbwd (anc Q) ʻʻ fld Q) ⊆ A →
      cn Q R A := by
  rintro ⟨⟨hQ, y, hy, hyR⟩, h⟩
  exact ⟨y, (pm230_513 hQ).1 h ⟨hyR, hy⟩⟩

/-- ✱230·52. \(\vdash : \exists ! CʻQ \cap \text{ᗡ}ʻR . \exists ! \text{ᗡ}ʻR \cap pʻ\overleftarrow{Q}_{*} ʻʻsʻR\overline{Q} _{\text{cn}}ʻʻ\kappa .\kappa \subset \overleftarrow{Q}_{\text{cn}}ʻR .\supset . pʻ\kappa \in \overleftarrow{Q}_{\text{cn}}ʻR\)

`Q⃖_cn'R` is `rels (cn Q) R`, `s'R Q̄_cn''κ` is `sumCls (graph (cnBar R Q) ʻʻ K)`. -/
theorem pm230_52 {K : Set (Set α)} :
    ((fld Q ∩ codom R).Nonempty ∧
        (codom R ∩ prodCls (Rbwd (anc Q) ʻʻ sumCls (graph (cnBar R Q) ʻʻ K))).Nonempty) ∧
      K ⊆ rels (cn Q) R →
      prodCls K ∈ rels (cn Q) R := by
  rintro ⟨⟨⟨y0, hy0⟩, ⟨y, hyR, hy⟩⟩, hK⟩
  rw [mem_prodCls_Rbwd] at hy
  show (cnBar R Q (prodCls K)).Nonempty
  rcases K.eq_empty_or_nonempty with rfl | ⟨A0, hA0⟩
  · exact ⟨y0, hy0, fun x _ B hB => by simp at hB⟩
  · obtain ⟨y1, hy1⟩ := hK hA0
    have hyQ : y ∈ fld Q := anc_right (hy y1 ⟨_, ⟨A0, hA0, rfl⟩, hy1⟩)
    refine ⟨y, ⟨hyQ, hyR⟩, fun x ⟨z, hyz, hxz⟩ B hB => ?_⟩
    obtain ⟨yB, hyB⟩ := hK hB
    exact hyB.2 ⟨z, anc_trans' (hy yB ⟨_, ⟨B, hB, rfl⟩, hyB⟩) hyz, hxz⟩

/-- ✱230·53. \(\vdash \colon\ldotp Q \in \text{trans} \cap \text{connex} . \text{E}! \text{max}_Qʻ\text{ᗡ}ʻR . \supset : RQ_{\text{cn}}\alpha . \equiv . \overrightarrow{R}ʻ\text{max}_Qʻ\text{ᗡ}ʻR \subset \alpha\)

`R⃗'max_Q'ᗡ'R ⊂ α` is `Desc (maxP Q) (codom R) (fun m => refs R m ⊆ A)`. -/
theorem pm230_53 :
    Q ∈ transR ∩ connex ∧ EDesc (maxP Q) (codom R) →
      (cn Q R A ↔ Desc (maxP Q) (codom R) (fun m => refs R m ⊆ A)) := by
  rintro ⟨⟨htr, hcon⟩, m, hm⟩
  rw [Desc, TheIs_iff_of_unique hm]
  obtain ⟨⟨hmR, hmQ⟩, hmax⟩ := maxP_iff.1 ((hm m).2 rfl)
  rw [mem_connex] at hcon
  constructor
  · rintro ⟨y, ⟨hyQ, hyR⟩, h⟩ x hx
    rcases hcon y m ⟨hyQ, hmQ⟩ with (hym | rfl) | hmy
    · exact h ⟨m, anc_of hym, hx⟩
    · exact h ⟨y, anc_rfl hyQ, hx⟩
    · exact absurd hmy (hmax y hyR)
  · intro h
    refine ⟨m, ⟨hmQ, hmR⟩, fun x ⟨z, hmz, hxz⟩ => ?_⟩
    rcases anc_iff_po.1 hmz with ⟨rfl, -⟩ | hp
    · exact h hxz
    · rw [po_eq_of_transR htr] at hp
      exact absurd hp (hmax z ⟨x, hxz⟩)

/-- ✱230·54. \(\vdash \colon\ldotp Q \in \text{trans} \cap \text{connex} . \text{E}! \text{max}_Qʻ\text{ᗡ}ʻR . \supset : \kappa \subset \overleftarrow{{Q}_{\text{cn}}}ʻR . \equiv . P ʻ\kappa \in \overleftarrow{Q}{\text{cn}}ʻR\)

**Status.** proved (reading): transcription error: the e-text prints `Pʻκ` for `pʻκ` and
`\overleftarrow{Q}{\text{cn}}` for `Q⃖_cn` (✱230·53, ✱40·15 in the demonstration). -/
theorem pm230_54 {K : Set (Set α)} :
    Q ∈ transR ∩ connex ∧ EDesc (maxP Q) (codom R) →
      (K ⊆ rels (cn Q) R ↔ prodCls K ∈ rels (cn Q) R) := by
  rintro ⟨hQ, m, hm⟩
  have key : ∀ C, cn Q R C ↔ refs R m ⊆ C := fun C =>
    (pm230_53 (A := C) ⟨hQ, ⟨m, hm⟩⟩).trans (TheIs_iff_of_unique hm)
  constructor
  · intro h
    show cn Q R (prodCls K)
    rw [key]
    intro x hx C hC
    exact (key C).1 (h hC) hx
  · intro h C hC
    show cn Q R C
    have h' : cn Q R (prodCls K) := h
    rw [key] at h' ⊢
    exact h'.trans fun x hx => hx C hC

/-!
## [✱231] Limiting sections and ultimate oscillation of a function

*(Vol. 2, p. 727)*

> *Summary of* *231.
>
> …

**Lean reading.** `P R̄_sc Q` and `P R̄_os Q` are the terms `scBar P R Q`, `osBar P R Q` (✱231·01·02), with
`P : α → α → Prop` the value-series. `P_*'''κ` is `anc P ʻʻʻ K`, `Q⃖_cn'R` is `rels (cn Q) R`,
`R'''Q⃖_*''γ` is `R ʻʻʻ Rbwd (anc Q) ʻʻ S`, `P⃗_*'x` is `refs (anc P) x`, `B⃗'P` is
`refs Beg P`, `Q̆_*` is `ancCnv Q`. Descriptions that may fail (`B'P`, `max_P'…`, `min_P'…`,
`limax_P'…`, `limin_P'…`, `R'z`, `max_Q'ᗡ'R`) are `Desc` with the smallest scope; of two
descriptions in one equation the first has the larger scope. `R ∈ 1 → Cls` is
`R ∈ arrow one Cls`, `P R̄_os Q ∈ 0 ∪ 1` is `osBar P R Q ∈ zero ∪ one`, `x P_1 y` is
`P1 P x y`. "Hp ✱231·25" is written out. The proofs go through the characterization ✱231·112
(`mem_scBar'`) and, for ✱231·25, a cut lemma (`cut_limax`: for a series `P`, a section and its
complement in `C'P`, `limin_P` of the complement is the `limax_P` of the section or its
immediate successor).

**Status.** proved (all propositions; ✱231·01·02 definition; ✱231·103, ✱231·133, ✱231·171, ✱231·192,
✱231·24, ✱231·25, ✱231·252 proved (reading): transcription errors or misprints, see their
docstrings)
-/

/-- ✱231·01 (Df). \(P\overline{R} _{\text{sc}}Q=pʻP_{*}ʻʻʻ\overleftarrow{Q}_{\text{cn}}ʻR\cap CʻP \quad\text{Df}\) -/
theorem pm231_01 : scBar P R Q = prodCls (anc P ʻʻʻ rels (cn Q) R) ∩ fld P := rfl

/-- ✱231·02 (Df). \(P\overline{R} _{\text{os}}Q=P\overline{R} _{\text{sc}}Q\cap \breve{P} \overline{R} _{\text{sc}}Q \quad\text{Df}\) -/
theorem pm231_02 : osBar P R Q = scBar P R Q ∩ scBar P˘ R Q := rfl

/-- ✱231·1. \(\vdash .P\overline{R} _{\text{sc}}Q=pʻP_{*}ʻʻʻ\overleftarrow{Q}_{\text{cn}}ʻR\cap CʻP \quad[(*231·01)]\) -/
theorem pm231_1 : scBar P R Q = prodCls (anc P ʻʻʻ rels (cn Q) R) ∩ fld P := rfl

/-- ✱231·101. \(\vdash .P\overline{R} _{\text{os}}Q=P\overline{R} _{\text{sc}}Q\cap \breve{P} \overline{R} _{\text{sc}}Q \quad[(*231·02)]\) -/
theorem pm231_101 : osBar P R Q = scBar P R Q ∩ scBar P˘ R Q := rfl

/-- ✱231·102. \(\vdash .P\overline{R} _{\text{sc}}Q=P_{\text{po}}\overline{R} _{\text{sc}}Q=P_{*}\overline{R} _{\text{sc}}Q \quad[*231·1.*91·602.*90·4]\)

The chain of three is the conjunction of its two links. -/
theorem pm231_102 : scBar P R Q = scBar (po P) R Q ∧ scBar (po P) R Q = scBar (anc P) R Q :=
  ⟨scBar_congr (fun _ _ => anc_po_iff.symm) (fld_po P).symm,
    scBar_congr (fun _ _ => anc_po_iff.trans anc_anc_iff.symm)
      ((fld_po P).trans (fld_anc P).symm)⟩

private theorem scBar_cnv_po : scBar (po P)˘ R Q = scBar P˘ R Q :=
  scBar_congr (fun _ _ => anc_cnv.trans (anc_po_iff.trans anc_cnv.symm))
    (by rw [fld_cnv, fld_po, fld_cnv])

private theorem scBar_cnv_anc : scBar (anc P)˘ R Q = scBar P˘ R Q :=
  scBar_congr (fun _ _ => anc_cnv.trans (anc_anc_iff.trans anc_cnv.symm))
    (by rw [fld_cnv, fld_anc, fld_cnv])

/-- ✱231·103. \(\vdash .P\overline{R} _{\text{os}}Q=P_{\text{po}}\overline{R} _{\text{os}}Q=P{*}\overline{R} _{\text{os}}Q \quad[*231·102·101]\)

**Status.** proved (reading): transcription error: the e-text prints `P{*}` for `P_*` in the last
member. The chain of three is the conjunction of its two links. -/
theorem pm231_103 : osBar P R Q = osBar (po P) R Q ∧ osBar (po P) R Q = osBar (anc P) R Q := by
  obtain ⟨h1, h2⟩ := pm231_102 (P := P) (R := R) (Q := Q)
  refine ⟨?_, ?_⟩
  · show scBar P R Q ∩ scBar P˘ R Q = scBar (po P) R Q ∩ scBar (po P)˘ R Q
    rw [h1, scBar_cnv_po]
  · show scBar (po P) R Q ∩ scBar (po P)˘ R Q = scBar (anc P) R Q ∩ scBar (anc P)˘ R Q
    rw [h2, scBar_cnv_po, scBar_cnv_anc]

/-- ✱231·11. \(\vdash \colon\ldotp x\in P\overline{R} _{\text{sc}}Q.\equiv :RQ_{\text{cn}}\alpha .\supset _{\alpha }.x\in P_{*}ʻʻ\alpha :x\in CʻP \quad[*231·1]\) -/
theorem pm231_11 {x : α} :
    x ∈ scBar P R Q ↔ (∀ A, cn Q R A → x ∈ anc P ʻʻ A) ∧ x ∈ fld P :=
  mem_scBar

/-- ✱231·111. \[\begin{align}&\vdash \colon\ldotp x\in P\overline{R} _{\text{sc}}Q.\equiv :y\in CʻQ\cap \text{ᗡ}ʻR.Rʻʻ\overleftarrow{Q}_{*}ʻy\subset \alpha .\supset _{y,\alpha }.x\in P_{*}ʻʻ\alpha :x\in CʻP\\ &[*231·11.*230·11]\end{align}\] -/
theorem pm231_111 {x : α} :
    x ∈ scBar P R Q ↔
      (∀ y A, y ∈ fld Q ∩ codom R ∧ R ʻʻ rels (anc Q) y ⊆ A → x ∈ anc P ʻʻ A) ∧ x ∈ fld P := by
  rw [mem_scBar]
  exact and_congr ⟨fun h y A hyA => h A ⟨y, hyA⟩, fun h A ⟨y, hyA⟩ => h y A hyA⟩ Iff.rfl

/-- ✱231·112. \(\vdash \colon\ldotp x\in P\overline{R} _{\text{sc}}Q.\equiv :y\in CʻQ\cap \text{ᗡ}ʻR.\supset _{y}.x\in P_{*}ʻʻRʻʻ\overleftarrow{Q}_{*}ʻy:x\in CʻP\) -/
theorem pm231_112 {x : α} :
    x ∈ scBar P R Q ↔
      (∀ y, y ∈ fld Q ∩ codom R → x ∈ anc P ʻʻ (R ʻʻ rels (anc Q) y)) ∧ x ∈ fld P :=
  mem_scBar'

/-- ✱231·113. \[\begin{align}&\vdash \colon\ldotp x\in P\overline{R} _{\text{sc}}Q.\equiv :y\in CʻQ\cap \text{ᗡ}ʻR.\supset _{y}.x(P_{*}\mid R\mid \breve{Q} _{*})y:x\in CʻP\\ &[*231·112.*37·3]\end{align}\]

`P_* | R | Q̆_*` is `anc P ⨾ R ⨾ ancCnv Q`. -/
theorem pm231_113 {x : α} :
    x ∈ scBar P R Q ↔
      (∀ y, y ∈ fld Q ∩ codom R → (anc P ⨾ R ⨾ ancCnv Q) x y) ∧ x ∈ fld P := by
  rw [mem_scBar']
  refine and_congr (forall_congr' fun y => imp_congr Iff.rfl ?_) Iff.rfl
  constructor
  · rintro ⟨v, ⟨z, hyz, hvz⟩, hxv⟩
    exact ⟨z, ⟨v, hxv, hvz⟩, hyz⟩
  · rintro ⟨z, ⟨v, hxv, hvz⟩, hyz⟩
    exact ⟨v, ⟨z, hyz, hvz⟩, hxv⟩

/-- ✱231·12. \(\vdash .P\overline{R} _{\text{sc}}Q=pʻP_{*}ʻʻʻRʻʻʻ\overleftarrow{Q}_{*}ʻʻ(CʻQ\cap \text{ᗡ}ʻR)\cap CʻP \quad[*231·112]\)

`P_*'''R'''Q⃖_*''(C'Q ∩ ᗡ'R)` is `anc P ʻʻʻ R ʻʻʻ Rbwd (anc Q) ʻʻ (fld Q ∩ codom R)`. -/
theorem pm231_12 :
    scBar P R Q = prodCls (anc P ʻʻʻ R ʻʻʻ Rbwd (anc Q) ʻʻ (fld Q ∩ codom R)) ∩ fld P := by
  ext x
  rw [mem_scBar', Set.mem_inter_iff, mem_prodCls_img3]

/-- ✱231·121. \[\begin{align}\vdash :\exists !&CʻQ\cap \text{ᗡ}ʻR.\supset .\\ &P\overline{R} _{\text{sc}}Q=pʻP_{*}ʻʻʻ\overleftarrow{Q}_{\text{cn}}ʻR=pʻP_{*}ʻʻʻRʻʻʻ\overleftarrow{Q}_{*}ʻʻ(CʻQ\cap \text{ᗡ}ʻR)\end{align}\]

The chain of three is the conjunction of its two links. -/
theorem pm231_121 :
    (fld Q ∩ codom R).Nonempty →
      scBar P R Q = prodCls (anc P ʻʻʻ rels (cn Q) R) ∧
        prodCls (anc P ʻʻʻ rels (cn Q) R) =
          prodCls (anc P ʻʻʻ R ʻʻʻ Rbwd (anc Q) ʻʻ (fld Q ∩ codom R)) := by
  rintro ⟨y0, hy0⟩
  have h2 : prodCls (anc P ʻʻʻ rels (cn Q) R) =
      prodCls (anc P ʻʻʻ R ʻʻʻ Rbwd (anc Q) ʻʻ (fld Q ∩ codom R)) := by
    ext x
    rw [mem_prodCls_cn, mem_prodCls_img3]
  refine ⟨?_, h2⟩
  ext x
  rw [mem_scBar', mem_prodCls_cn]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  obtain ⟨v, -, hxv⟩ := h y0 hy0
  exact anc_left hxv

/-- ✱231·13. \(\vdash .P\overline{R}_{\text{sc}}Q\in \text{sect}ʻP \quad[*211·631·13.*231·12]\) -/
theorem pm231_13 : scBar P R Q ∈ sect P := by
  refine ⟨fun x hx => hx.2, ?_⟩
  rintro w ⟨x, hx, hwx⟩
  exact scBar_down hx (anc_of hwx)

/-- ✱231·131. \(\vdash .P\overline{R}_{\text{sc}}Q \subset CʻP \quad[*231·1]\) -/
theorem pm231_131 : scBar P R Q ⊆ fld P := fun _ hx => hx.2

/-- ✱231·132. \(\vdash :\exists !CʻQ\cap \text{ᗡ}ʻR.\supset .P\overline{R}_{\text{sc}}Q\subset P_{*}ʻʻRʻʻ\breve{Q} _{*}ʻʻ\text{ᗡ}ʻR\) -/
theorem pm231_132 :
    (fld Q ∩ codom R).Nonempty → scBar P R Q ⊆ anc P ʻʻ (R ʻʻ (ancCnv Q ʻʻ codom R)) := by
  rintro ⟨y, hy⟩ x hx
  obtain ⟨v, ⟨z, hyz, hvz⟩, hxv⟩ := (mem_scBar'.1 hx).1 y hy
  exact ⟨v, ⟨z, ⟨y, hy.2, hyz⟩, hvz⟩, hxv⟩

/-- ✱231·133. \(\vdash :CʻP\cap \text{ᗡ}ʻR=\Lambda .\supset .P\overline{R}_{\text{sc}}Q=CʻP \quad[*231·12.*37·29.*40·2]\)

**Status.** proved (reading): misprint: PM prints `C'P ∩ ᗡ'R = Λ`, which is not significant
(`C'P` is a class of values, `ᗡ'R` a class of arguments); the references (✱231·12, ✱37·29,
✱40·2: `p'Λ = V`) and the analogue ✱232·15 require `C'Q ∩ ᗡ'R = Λ`, which is read. -/
theorem pm231_133 : fld Q ∩ codom R = Λ → scBar P R Q = fld P := by
  intro h
  ext x
  rw [mem_scBar']
  refine ⟨fun h' => h'.2, fun hx => ⟨fun y hy => ?_, hx⟩⟩
  rw [h] at hy
  exact absurd hy not_mem_null

private theorem po_img_sect {A : Set α} (hA : A ∈ sect P) : po P ʻʻ A = P ʻʻ A := by
  ext x
  constructor
  · rintro ⟨v, hv, hxv⟩
    rw [po_iff_transGen] at hxv
    obtain ⟨b, hxb, hbv⟩ := Relation.TransGen.head'_iff.1 hxv
    exact ⟨b, sect_anc hA (anc_iff_reflTransGen.2 ⟨fld_of_right hxb, hbv⟩) hv, hxb⟩
  · rintro ⟨v, hv, hxv⟩
    exact ⟨v, hv, po_of hxv⟩

/-- ✱231·134. \(\vdash .P_{\text{po}}ʻʻ(P\overline{R}_{\text{sc}}Q)=Pʻʻ(P\overline{R}_{\text{sc}}Q) \quad[*211·131.*231·13]\) -/
theorem pm231_134 : po P ʻʻ scBar P R Q = P ʻʻ scBar P R Q := po_img_sect pm231_13

/-- ✱231·14. \[\begin{align}&\vdash \colon\colon R\in 1\rightarrow \text{Cls}.\supset \colon\ldotp x\in P\overline{R}_{\text{sc}}Q.\equiv :\\ &y\in CʻQ\cap \text{ᗡ}ʻR.\supset _{y}.(\exists z).yQ_{*}z.xP_{*}(Rʻz):x\in CʻP \quad[*71·7.*231·113]\end{align}\]

`R ∈ 1 → Cls` is `R ∈ arrow one Cls`; `x P_* (R'z)` is `Desc R z (fun v => anc P x v)`. -/
theorem pm231_14 {x : α} :
    R ∈ arrow one Cls →
      (x ∈ scBar P R Q ↔
        (∀ y, y ∈ fld Q ∩ codom R → ∃ z, anc Q y z ∧ Desc R z (fun v => anc P x v)) ∧
          x ∈ fld P) := by
  intro hR
  rw [mem_arrow_one_Cls] at hR
  rw [mem_scBar']
  refine and_congr (forall_congr' fun y => imp_congr Iff.rfl ?_) Iff.rfl
  constructor
  · rintro ⟨v, ⟨z, hyz, hvz⟩, hxv⟩
    exact ⟨z, hyz, v, fun w => ⟨fun hw => hR w v z ⟨hw, hvz⟩, fun e => e ▸ hvz⟩, hxv⟩
  · rintro ⟨z, hyz, hd⟩
    obtain ⟨v, hv, hxv⟩ := hd
    exact ⟨v, ⟨z, hyz, (hv v).2 rfl⟩, hxv⟩

/-- ✱231·141. \(\vdash :Q_{*}\in \text{connex} .RQ_{\text{cn}}(\overleftarrow{P}_{*}ʻx).\supset .x\in P\overline{R}_{\text{sc}}Q\) -/
theorem pm231_141 {x : α} : anc Q ∈ connex ∧ cn Q R (rels (anc P) x) → x ∈ scBar P R Q := by
  rintro ⟨hc, y0, ⟨hy0Q, v0, hv0⟩, h0⟩
  rw [mem_connex, fld_anc] at hc
  have hx : x ∈ fld P := anc_left (h0 ⟨y0, anc_rfl hy0Q, hv0⟩)
  rw [mem_scBar']
  refine ⟨fun y ⟨hyQ, v, hv⟩ => ?_, hx⟩
  rcases hc y0 y ⟨hy0Q, hyQ⟩ with (h | e) | h
  · exact ⟨v, ⟨y, anc_rfl hyQ, hv⟩, h0 ⟨y, h, hv⟩⟩
  · subst e
    exact ⟨v, ⟨y0, anc_rfl hy0Q, hv⟩, h0 ⟨y0, anc_rfl hy0Q, hv⟩⟩
  · exact ⟨v0, ⟨y0, h, hv0⟩, h0 ⟨y0, anc_rfl hy0Q, hv0⟩⟩

/-- ✱231·142. \(\vdash :\alpha \in \text{sect}ʻP.RQ_{\text{cn}}\alpha .\supset .P\overline{R}_{\text{sc}}Q\subset \alpha\) -/
theorem pm231_142 : A ∈ sect P ∧ cn Q R A → scBar P R Q ⊆ A := by
  rintro ⟨hA, hc⟩ x hx
  obtain ⟨v, hv, hxv⟩ := (mem_scBar.1 hx).1 A hc
  exact sect_anc hA hxv hv

private theorem refs_anc_sect {x : α} : refs (anc P) x ∈ sect P := by
  refine ⟨fun w hw => anc_left hw, ?_⟩
  rintro u ⟨w, hw, huw⟩
  exact anc_trans' (anc_of huw) hw

private theorem refs_po_sect {x : α} : refs (po P) x ∈ sect P := by
  refine ⟨fun w hw => po_left hw, ?_⟩
  rintro u ⟨w, hw, huw⟩
  exact po_trans' (po_of huw) hw

/-- ✱231·143. \(\vdash :RQ_{\text{cn}}(\overrightarrow{P}_{*}ʻx).\supset .P\overline{R}_{\text{sc}}Q\subset \overrightarrow{P}_{*}ʻx \quad[*231·142.*211·13]\) -/
theorem pm231_143 {x : α} : cn Q R (refs (anc P) x) → scBar P R Q ⊆ refs (anc P) x :=
  fun h => pm231_142 ⟨refs_anc_sect, h⟩

/-- ✱231·144. \(\vdash :RQ_{\text{cn}}(\overrightarrow{P}_{\text{po}}ʻx).\supset .P\overline{R}_{\text{sc}}Q\subset \overrightarrow{P}_{\text{po}}ʻx \quad[*231·142.*211·16]\) -/
theorem pm231_144 {x : α} : cn Q R (refs (po P) x) → scBar P R Q ⊆ refs (po P) x :=
  fun h => pm231_142 ⟨refs_po_sect, h⟩

/-- ✱231·15. \(\vdash :RʻʻCʻQ\subset CʻP.\supset .CʻP\cap pʻ\overrightarrow{P}_{*}ʻʻCʻP\subset P\overline{R}_{\text{sc}}Q\)

`p'P⃗_*''C'P` is `prodCls (Rfwd (anc P) ʻʻ fld P)`. -/
theorem pm231_15 :
    R ʻʻ fld Q ⊆ fld P → fld P ∩ prodCls (Rfwd (anc P) ʻʻ fld P) ⊆ scBar P R Q := by
  rintro h x ⟨hx, hp⟩
  rw [mem_prodCls_Rfwd] at hp
  rw [mem_scBar']
  exact ⟨fun y ⟨hyQ, v, hv⟩ => ⟨v, ⟨y, anc_rfl hyQ, hv⟩, hp v (h ⟨y, hyQ, hv⟩)⟩, hx⟩

/-- A beginning of `P` precedes every term of `C'P` when `P_*` is connected. -/
private theorem beg_first {x w : α} (hx : x ∈ refs Beg P) (hc : anc P ∈ connex)
    (hw : w ∈ fld P) : anc P x w := by
  obtain ⟨⟨y, hxy⟩, hxn⟩ := hx
  rw [mem_connex, fld_anc] at hc
  rcases hc x w ⟨fld_of_left hxy, hw⟩ with (h1 | e) | h1
  · exact h1
  · subst e
    exact anc_rfl hw
  · rcases anc_iff_po.1 h1 with ⟨e, -⟩ | hp
    · subst e
      exact anc_rfl hw
    · rw [po_iff_transGen] at hp
      obtain ⟨b, -, hbx⟩ := Relation.TransGen.tail'_iff.1 hp
      exact absurd ⟨b, hbx⟩ hxn

/-- ✱231·151. \[\begin{align}&\vdash :P_{*}\in \text{connex} .CʻP\cap pʻ\overrightarrow{P}_{*}ʻʻCʻP\subset P\overline{R} _{\text{sc}}Q.\supset .\overrightarrow{B}ʻP\subset P\overline{R} _{\text{sc}}Q\\ &[*202·521]\end{align}\]

`B⃗'P` is `refs Beg P`. -/
theorem pm231_151 :
    anc P ∈ connex ∧ fld P ∩ prodCls (Rfwd (anc P) ʻʻ fld P) ⊆ scBar P R Q →
      refs Beg P ⊆ scBar P R Q := by
  rintro ⟨hc, h⟩ x hx
  obtain ⟨⟨y, hxy⟩, -⟩ := id hx
  exact h ⟨fld_of_left hxy, mem_prodCls_Rfwd.2 fun w hw => beg_first hx hc hw⟩

private theorem beg_unique {x b : α} (hc : anc P ∈ connex) (hx : x ∈ refs Beg P)
    (hb : b ∈ refs Beg P) : x = b := by
  obtain ⟨⟨y, hby⟩, hbn⟩ := hb
  rcases anc_iff_po.1 (beg_first hx hc (fld_of_left hby)) with ⟨e, -⟩ | hp
  · exact e
  · rw [po_iff_transGen] at hp
    obtain ⟨c, -, hcb⟩ := Relation.TransGen.tail'_iff.1 hp
    exact absurd ⟨c, hcb⟩ hbn

/-- ✱231·152. \[\begin{align}&\vdash :P_{*}\in \text{connex} .CʻP\cap pʻ\overrightarrow{P}_{*}ʻʻCʻP\subset P\overline{R} _{\text{sc}}Q.\exists !\overrightarrow{B}ʻP.\supset .BʻP\in P\overline{R} _{\text{sc}}Q\\ &[*231·151.*202·523]\end{align}\]

`B'P ∈ P R̄_sc Q` is `Desc Beg P (fun b => b ∈ scBar P R Q)`. -/
theorem pm231_152 :
    (anc P ∈ connex ∧ fld P ∩ prodCls (Rfwd (anc P) ʻʻ fld P) ⊆ scBar P R Q) ∧
        (refs Beg P).Nonempty →
      Desc Beg P (fun b => b ∈ scBar P R Q) := by
  rintro ⟨h, b, hb⟩
  exact ⟨b, fun x => ⟨fun hx => beg_unique h.1 hx hb, fun e => e ▸ hb⟩, pm231_151 h hb⟩

/-- ✱231·153. \(\vdash :CʻQ\cap \text{ᗡ}ʻR\subset Q_{*}ʻʻ\breve{R} ʻʻCʻP.\supset .CʻP\cap pʻ\overrightarrow{P}_{*}ʻʻCʻP\subset P\overline{R} _{\text{sc}}Q\)

`Q_*''R̆''C'P` is `anc Q ʻʻ (R˘ ʻʻ fld P)`. -/
theorem pm231_153 :
    fld Q ∩ codom R ⊆ anc Q ʻʻ (R˘ ʻʻ fld P) →
      fld P ∩ prodCls (Rfwd (anc P) ʻʻ fld P) ⊆ scBar P R Q := by
  rintro h x ⟨hx, hp⟩
  rw [mem_prodCls_Rfwd] at hp
  rw [mem_scBar']
  refine ⟨fun y hy => ?_, hx⟩
  obtain ⟨z, ⟨v, hv, hvz⟩, hyz⟩ := h hy
  exact ⟨v, ⟨z, hyz, hvz⟩, hp v hv⟩

/-- ✱231·154. \(\vdash :RʻʻCʻQ\subset CʻP.\supset .CʻQ\cap \text{ᗡ}ʻR\subset \breve{R} ʻʻCʻP\) -/
theorem pm231_154 : R ʻʻ fld Q ⊆ fld P → fld Q ∩ codom R ⊆ R˘ ʻʻ fld P :=
  fun h _ ⟨hyQ, v, hv⟩ => ⟨v, h ⟨_, hyQ, hv⟩, hv⟩

/-- ✱231·155. \(\vdash :CʻQ\cap \text{ᗡ}ʻR\subset \breve{R} ʻʻCʻP.\supset .CʻQ\cap \text{ᗡ}ʻR\subset Q_{*}ʻʻ\breve{R} ʻʻCʻP\) -/
theorem pm231_155 :
    fld Q ∩ codom R ⊆ R˘ ʻʻ fld P → fld Q ∩ codom R ⊆ anc Q ʻʻ (R˘ ʻʻ fld P) :=
  fun h y hy => ⟨y, h hy, anc_rfl hy.1⟩

/-- ✱231·156. \[\begin{align}\vdash \colon\ldotp CʻQ\cap \text{ᗡ}ʻR\subset Q_{*}ʻʻ\breve{R} ʻʻCʻP.&\equiv :\Lambda {\sim}\in P_{*}ʻʻʻRʻʻʻ\overleftarrow{Q}_{*}ʻʻ(CʻQ\cap \text{ᗡ}ʻR):\\ &\equiv :z\in CʻQ\cap \text{ᗡ}ʻR.\supset _{z}.\exists !CʻP\cap Rʻʻ\overleftarrow{Q}_{*}ʻz\end{align}\]

The chain of three is the conjunction of its two links; `Λ ∼∈ κ` is `Λ ∉ K`. -/
theorem pm231_156 :
    (fld Q ∩ codom R ⊆ anc Q ʻʻ (R˘ ʻʻ fld P) ↔
        Λ ∉ anc P ʻʻʻ R ʻʻʻ Rbwd (anc Q) ʻʻ (fld Q ∩ codom R)) ∧
      (Λ ∉ anc P ʻʻʻ R ʻʻʻ Rbwd (anc Q) ʻʻ (fld Q ∩ codom R) ↔
        ∀ z, z ∈ fld Q ∩ codom R → (fld P ∩ R ʻʻ rels (anc Q) z).Nonempty) := by
  have key : Λ ∉ anc P ʻʻʻ R ʻʻʻ Rbwd (anc Q) ʻʻ (fld Q ∩ codom R) ↔
      ∀ z, z ∈ fld Q ∩ codom R → (fld P ∩ R ʻʻ rels (anc Q) z).Nonempty := by
    rw [mem_img3_img3, not_exists]
    refine forall_congr' fun z => ?_
    rw [not_and]
    refine imp_congr Iff.rfl ⟨fun h => ?_, ?_⟩
    · have hne : (anc P ʻʻ (R ʻʻ rels (anc Q) z)).Nonempty :=
        Set.nonempty_iff_ne_empty.2 fun e => h (by rw [Null_eq_empty, e])
      obtain ⟨x, v, hv, hxv⟩ := hne
      exact ⟨v, anc_right hxv, hv⟩
    · rintro ⟨v, hvP, hv⟩ e
      have : v ∈ anc P ʻʻ (R ʻʻ rels (anc Q) z) := ⟨v, hv, anc_rfl hvP⟩
      rw [← e] at this
      exact not_mem_null this
  refine ⟨?_, key⟩
  rw [key]
  constructor
  · intro h z hz
    obtain ⟨w, ⟨v, hvP, hvw⟩, hzw⟩ := h hz
    exact ⟨v, hvP, w, hzw, hvw⟩
  · intro h z hz
    obtain ⟨v, hvP, w, hzw, hvw⟩ := h z hz
    exact ⟨w, ⟨v, hvP, hvw⟩, hzw⟩

/-- ✱231·16. \[\begin{align}\vdash :P_{*}\in \text{connex} .\exists !\overrightarrow{B}ʻP.&CʻQ\cap \text{ᗡ}ʻR\subset Q_{*}ʻʻ\breve{R} ʻʻCʻP.\supset .\\ &\exists !P\overline{R} _{\text{sc}}Q.BʻP\in P\overline{R} _{\text{sc}}Q \quad[*231·152·153]\end{align}\] -/
theorem pm231_16 :
    (anc P ∈ connex ∧ (refs Beg P).Nonempty) ∧ fld Q ∩ codom R ⊆ anc Q ʻʻ (R˘ ʻʻ fld P) →
      (scBar P R Q).Nonempty ∧ Desc Beg P (fun b => b ∈ scBar P R Q) := by
  rintro ⟨⟨hc, b, hb⟩, h⟩
  have h153 := pm231_153 (P := P) h
  exact ⟨⟨b, pm231_151 ⟨hc, h153⟩ hb⟩, pm231_152 ⟨⟨hc, h153⟩, b, hb⟩⟩

/-- ✱231·161. \[\begin{align}&\vdash :P_{*}\in \text{connex} .\exists !\overrightarrow{B}ʻP.RʻʻCʻQ\subset CʻP.\supset .\exists !P\overline{R} _{\text{sc}}Q.BʻP\in P\overline{R} _{\text{sc}}Q\\ &[*231·154·155·16]\end{align}\] -/
theorem pm231_161 :
    (anc P ∈ connex ∧ (refs Beg P).Nonempty) ∧ R ʻʻ fld Q ⊆ fld P →
      (scBar P R Q).Nonempty ∧ Desc Beg P (fun b => b ∈ scBar P R Q) :=
  fun ⟨h1, h2⟩ => pm231_16 ⟨h1, pm231_155 (pm231_154 h2)⟩

/-- ✱231·17. \(\vdash :RʻʻCʻQ\subset CʻP.\supset .R\overline{Q} _{\text{cn}}\alpha \subset R\overline{Q} _{\text{cn}}(P_{*}ʻʻ\alpha )\) -/
theorem pm231_17 : R ʻʻ fld Q ⊆ fld P → cnBar R Q A ⊆ cnBar R Q (anc P ʻʻ A) := by
  rintro h y ⟨hy, hA⟩
  refine ⟨hy, fun v hv => ⟨v, hA hv, anc_rfl (h ?_)⟩⟩
  obtain ⟨z, hyz, hvz⟩ := hv
  exact ⟨z, anc_right hyz, hvz⟩

/-- ✱231·171. \(\vdash :RʻʻCʻQ\subset CʻP.R\overline{Q} _{\text{cn}}\alpha .\supset .R\overline{Q} _{\text{cn}}(P_{*}ʻʻ\alpha ) \quad[*231·17.*230·11]\)

**Status.** proved (reading): transcription error: the e-text prints the class `R Q̄_cn α` (with
the bar) for the proposition `R Q_cn α` in the hypothesis and the conclusion (the references are
✱231·17 and ✱230·11). -/
theorem pm231_171 : R ʻʻ fld Q ⊆ fld P ∧ cn Q R A → cn Q R (anc P ʻʻ A) :=
  fun ⟨h, y, hy⟩ => ⟨y, pm231_17 h hy⟩

/-- ✱231·18. \(\vdash :RʻʻCʻQ\subset CʻP.\supset .P\overline{R} _{\text{sc}}Q=pʻ(\text{sect}ʻP\cap \overleftarrow{Q}_{\text{cn}}ʻR)\cap CʻP\) -/
theorem pm231_18 :
    R ʻʻ fld Q ⊆ fld P → scBar P R Q = prodCls (sect P ∩ rels (cn Q) R) ∩ fld P := by
  intro h
  ext x
  constructor
  · intro hx
    exact ⟨fun C ⟨hC, hcn⟩ => pm231_142 ⟨hC, hcn⟩ hx, hx.2⟩
  · rintro ⟨hp, hx⟩
    rw [mem_scBar]
    refine ⟨fun A hA => hp _ ⟨?_, pm231_171 ⟨h, hA⟩⟩, hx⟩
    refine ⟨fun w ⟨v, _, hwv⟩ => anc_left hwv, ?_⟩
    rintro u ⟨w, ⟨v, hv, hwv⟩, huw⟩
    exact ⟨v, hv, anc_trans' (anc_of huw) hwv⟩

/-- ✱231·181. \(\vdash :P\in \text{Ser}.RʻʻCʻQ\subset CʻP.\supset .P\overline{R} _{\text{sc}}Q=CʻP\cap pʻ(\overrightarrow{P}ʻʻCʻP\cap \overleftarrow{Q}_{\text{cn}}ʻR)\)

`P⃗''C'P ∩ Q⃖_cn'R` is `Rfwd P ʻʻ fld P ∩ rels (cn Q) R`. -/
theorem pm231_181 :
    P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P →
      scBar P R Q = fld P ∩ prodCls (Rfwd P ʻʻ fld P ∩ rels (cn Q) R) := by
  rintro ⟨hS, h⟩
  obtain ⟨⟨hirr, htr⟩, hcon⟩ := Ser_parts hS
  rw [pm231_18 h]
  ext x
  constructor
  · rintro ⟨hp, hx⟩
    refine ⟨hx, ?_⟩
    rintro C ⟨⟨w, hw, rfl⟩, hcn⟩
    refine hp _ ⟨⟨fun u hu => fld_of_left hu, ?_⟩, hcn⟩
    rintro u ⟨v, hv, huv⟩
    exact htr u v w huv hv
  · rintro ⟨hx, hp⟩
    refine ⟨fun C ⟨hC, hcn⟩ => ?_, hx⟩
    by_contra hxC
    have hsub : C ⊆ refs P x := by
      intro v hv
      rcases hcon v x (hC.1 hv) hx with (h1 | e) | h1
      · exact h1
      · subst e
        exact absurd hv hxC
      · exact absurd (hC.2 ⟨v, hv, h1⟩) hxC
    exact hirr x (hp _ ⟨⟨x, hx, rfl⟩, pm230_211 hsub hcn⟩)

/-- ✱231·182. \[\begin{align}\vdash :P\in \text{Ser}.Rʻʻ&CʻQ\subset CʻP.\exists !CʻP-(P\overline{R} _{\text{sc}}Q).\supset .\\ &P\overline{R} _{\text{sc}}Q=pʻ(\overrightarrow{P}ʻʻCʻP\cap \overleftarrow{Q}_{\text{cn}}ʻR).\exists !(\overrightarrow{P} ʻʻCʻP \cap \overleftarrow{Q}_{\text{cn}}ʻR)\end{align}\] -/
theorem pm231_182 :
    (P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ (fld P \ scBar P R Q).Nonempty →
      scBar P R Q = prodCls (Rfwd P ʻʻ fld P ∩ rels (cn Q) R) ∧
        (Rfwd P ʻʻ fld P ∩ rels (cn Q) R).Nonempty := by
  rintro ⟨h, x, hx, hxs⟩
  have e := pm231_181 h
  have hne : (Rfwd P ʻʻ fld P ∩ rels (cn Q) R).Nonempty := by
    rw [e] at hxs
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    apply hxs
    refine ⟨hx, ?_⟩
    rw [hn]
    intro C hC
    simp at hC
  refine ⟨?_, hne⟩
  rw [e]
  obtain ⟨C, ⟨w, hw, rfl⟩, hcn⟩ := hne
  refine Set.inter_eq_right.2 fun z hz => ?_
  exact fld_of_left (hz _ ⟨⟨w, hw, rfl⟩, hcn⟩)

/-- ✱231·19. \[\begin{align}\vdash :P\in \text{trans}.Q_{*}\in \text{connex} .Rʻʻ&CʻQ\subset CʻP.\supset .\\ &P\overline{R} _{\text{os}}Q=pʻ(\text{str}ʻP\cap \overleftarrow{Q}_{\text{cn}}ʻR)\cap CʻP\end{align}\] -/
theorem pm231_19 :
    (P ∈ transR ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      osBar P R Q = prodCls (str P ∩ rels (cn Q) R) ∩ fld P := by
  rintro ⟨⟨htr, -⟩, h⟩
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun C ⟨hC, hcn⟩ => ?_, h1.2⟩
    obtain ⟨v1, hv1, hxv1⟩ := (mem_scBar.1 h1).1 C hcn
    obtain ⟨v2, hv2, hxv2⟩ := (mem_scBar.1 h2).1 C hcn
    rw [anc_cnv] at hxv2
    rw [anc_iff_of_transR htr] at hxv1 hxv2
    rcases hxv1 with ⟨e1, -⟩ | h1'
    · rw [e1]
      exact hv1
    rcases hxv2 with ⟨e2, -⟩ | h2'
    · rw [← e2]
      exact hv2
    exact hC.2 ⟨⟨v1, hv1, h1'⟩, ⟨v2, hv2, h2'⟩⟩
  · rintro ⟨hp, hx⟩
    have h' : R ʻʻ fld Q ⊆ fld P˘ := by
      rw [fld_cnv]
      exact h
    refine ⟨?_, ?_⟩
    · rw [pm231_18 h]
      exact ⟨fun C ⟨hC, hcn⟩ => hp C ⟨⟨hC.1, fun u ⟨hu, _⟩ => hC.2 hu⟩, hcn⟩, hx⟩
    · rw [pm231_18 h']
      refine ⟨fun C ⟨hC, hcn⟩ => hp C ⟨⟨?_, fun u ⟨_, hu⟩ => hC.2 hu⟩, hcn⟩, ?_⟩
      · rw [← fld_cnv P]
        exact hC.1
      · rw [fld_cnv]
        exact hx

/-- ✱231·191. \[\begin{align}\vdash :P_{\text{po}}\in \text{connex} .&\exists !P\overline{R} _{\text{os}}Q.\supset .\\ &P\overline{R} _{\text{sc}}Q=P_{*}ʻʻ(P\overline{R} _{\text{os}}Q).Pʻʻ(P\overline{R} _{\text{sc}}Q)=P_{\text{po}}ʻʻ(P\overline{R} _{\text{os}}Q)\\ &[*215·165.*231·13·101]\end{align}\] -/
theorem pm231_191 :
    po P ∈ connex ∧ (osBar P R Q).Nonempty →
      scBar P R Q = anc P ʻʻ osBar P R Q ∧ P ʻʻ scBar P R Q = po P ʻʻ osBar P R Q := by
  rintro ⟨hc, x0, hx0⟩
  rw [mem_connex, fld_po] at hc
  have h1 : scBar P R Q = anc P ʻʻ osBar P R Q := by
    ext u
    constructor
    · intro hu
      rcases hc u x0 ⟨hu.2, hx0.1.2⟩ with (h | e) | h
      · exact ⟨x0, hx0, anc_of_po h⟩
      · subst e
        exact ⟨_, hx0, anc_rfl hu.2⟩
      · exact ⟨u, ⟨hu, scBar_cnv_up hx0.2 (anc_of_po h)⟩, anc_rfl hu.2⟩
    · rintro ⟨v, hv, huv⟩
      exact scBar_down hv.1 huv
  refine ⟨h1, ?_⟩
  rw [← pm231_134, h1]
  ext u
  constructor
  · rintro ⟨w, ⟨v, hv, hwv⟩, huw⟩
    exact ⟨v, hv, po_anc_trans huw hwv⟩
  · rintro ⟨v, hv, huv⟩
    exact ⟨v, ⟨v, hv, anc_rfl (po_right huv)⟩, huv⟩

private theorem osBar_cnv (Q' : β → β → Prop) : osBar P˘ R Q' = osBar P R Q' := by
  show scBar P˘ R Q' ∩ scBar P R Q' = scBar P R Q' ∩ scBar P˘ R Q'
  exact Set.inter_comm _ _

/-- ✱231·192. \[\begin{align}\vdash \colon\ldotp P_{\text{po}}\in &\text{connex} .\exists !P\overline{R} _{\text{os}}Q.\exists !P\overline{R} _{\text{os}}Qʻ.\supset :\\ &P\overline{R} _{\text{os}}Q=P\overline{R} _{\text{os}}Qʻ.\equiv .P\overline{R} _{\text{sc}}Q=P\overline{R} _{\text{sc}}Qʻ.\breve{P} \overline{R} _{\text{sc}}Q=\breve{P} \overline{R} _{\text{sc}}Qʻ\\ &[*231·191·101]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `Qʻ` for `Q'` (a second
argument-series, `Q'`). -/
theorem pm231_192 {Q' : β → β → Prop} :
    (po P ∈ connex ∧ (osBar P R Q).Nonempty) ∧ (osBar P R Q').Nonempty →
      (osBar P R Q = osBar P R Q' ↔
        scBar P R Q = scBar P R Q' ∧ scBar P˘ R Q = scBar P˘ R Q') := by
  rintro ⟨⟨hc, h1⟩, h2⟩
  constructor
  · intro e
    have hc' : po P˘ ∈ connex := by
      rw [po_cnv_eq]
      exact connex_cnv hc
    refine ⟨?_, ?_⟩
    · rw [(pm231_191 ⟨hc, h1⟩).1, (pm231_191 ⟨hc, h2⟩).1, e]
    · have e' : osBar P˘ R Q = osBar P˘ R Q' := by rw [osBar_cnv, osBar_cnv, e]
      rw [(pm231_191 (P := P˘) ⟨hc', by rw [osBar_cnv]; exact h1⟩).1,
        (pm231_191 (P := P˘) ⟨hc', by rw [osBar_cnv]; exact h2⟩).1, e']
  · rintro ⟨e1, e2⟩
    show scBar P R Q ∩ scBar P˘ R Q = scBar P R Q' ∩ scBar P˘ R Q'
    rw [e1, e2]

/-- When `P_po ∈ Ser` and `P R̄_os Q = ι'x₀`, `x₀` is the maximum of `P R̄_sc Q`. -/
private theorem max_sc_of_os {x0 : α} (hS : po P ∈ Ser)
    (hos : ∀ z, z ∈ osBar P R Q ↔ z = x0) (m : α) : maxP P m (scBar P R Q) ↔ m = x0 := by
  obtain ⟨⟨hirr, -⟩, hcon⟩ := Ser_parts hS
  rw [fld_po] at hcon
  have hx0 : x0 ∈ osBar P R Q := (hos x0).2 rfl
  rw [maxP_iff]
  constructor
  · rintro ⟨⟨hm, hmP⟩, hmax⟩
    rcases hcon m x0 hmP hx0.1.2 with (h | h) | h
    · rw [po_iff_transGen] at h
      obtain ⟨b, hmb, hbx⟩ := Relation.TransGen.head'_iff.1 h
      exact absurd hmb
        (hmax b (scBar_down hx0.1 (anc_iff_reflTransGen.2 ⟨fld_of_right hmb, hbx⟩)))
    · exact h
    · exact (hos m).1 ⟨hm, scBar_cnv_up hx0.2 (anc_of_po h)⟩
  · intro e
    subst e
    refine ⟨⟨hx0.1, hx0.1.2⟩, fun y hy hmy => ?_⟩
    have e' : y = m := (hos y).1 ⟨hy, scBar_cnv_up hx0.2 (anc_of hmy)⟩
    subst e'
    exact hirr _ (po_of hmy)

/-- ✱231·193. \[\begin{align}\vdash :P_{\text{po}}\in \text{Ser}.P\overline{R} _{\text{os}}Q\in &1.\supset .\\ &P\overline{R} _{\text{os}}Q=\iota ʻ\text{max}_{P}ʻ(P\overline{R} _{\text{sc}}Q)=\iota ʻ\text{min}_{P}ʻ(\breve{P} \overline{R} _{\text{sc}}Q)\\ &[*215·166.*231·13·101]\end{align}\]

`ι'max_P'(P R̄_sc Q)` is a description inside `ι'`: `Desc (maxP P) (scBar P R Q) (fun m => … ι m …)`;
the chain of three is the conjunction of its two links, and in the second link the first
description has the larger scope. -/
theorem pm231_193 :
    po P ∈ Ser ∧ osBar P R Q ∈ one →
      Desc (maxP P) (scBar P R Q) (fun m => osBar P R Q = ι m) ∧
        Desc (maxP P) (scBar P R Q)
          (fun m => Desc (minP P) (scBar P˘ R Q) (fun n => ι m = ι n)) := by
  rintro ⟨hS, hone⟩
  obtain ⟨x0, hx0⟩ := mem_one_iff.1 hone
  have hm := max_sc_of_os hS hx0
  have hS' : po P˘ ∈ Ser := by
    rw [po_cnv_eq]
    exact Ser_cnv hS
  have hx0' : ∀ z, z ∈ osBar P˘ R Q ↔ z = x0 := fun z => by rw [osBar_cnv]; exact hx0 z
  have hn : ∀ n, minP P n (scBar P˘ R Q) ↔ n = x0 := max_sc_of_os hS' hx0'
  exact ⟨(TheIs_iff_of_unique hm).2 (Set.ext fun z => hx0 z),
    (TheIs_iff_of_unique hm).2 ((TheIs_iff_of_unique hn).2 rfl)⟩

/-- ✱231·2. \[\begin{align}\vdash :P_{*},Q_{*}\in \text{connex} .CʻQ\cap \text{ᗡ}ʻR\subset Q_{*}ʻʻ\breve{R} ʻʻ&CʻP.\supset .\\ &CʻP-(P\overline{R} _{\text{sc}}Q)\subset \breve{P} \overline{R} _{\text{sc}}Q\end{align}\]

`P_*, Q_* ∈ connex` is `anc P ∈ connex ∧ anc Q ∈ connex`. -/
theorem pm231_2 :
    (anc P ∈ connex ∧ anc Q ∈ connex) ∧ fld Q ∩ codom R ⊆ anc Q ʻʻ (R˘ ʻʻ fld P) →
      fld P \ scBar P R Q ⊆ scBar P˘ R Q := by
  rintro ⟨⟨hcP, hcQ⟩, h⟩ x ⟨hx, hxs⟩
  rw [mem_connex, fld_anc] at hcP hcQ
  have hxs' : ¬∀ y, y ∈ fld Q ∩ codom R → x ∈ anc P ʻʻ (R ʻʻ rels (anc Q) y) :=
    fun h' => hxs (mem_scBar'.2 ⟨h', hx⟩)
  simp only [not_forall] at hxs'
  obtain ⟨y0, hy0, hn⟩ := hxs'
  rw [mem_scBar', fld_cnv]
  refine ⟨fun y1 hy1 => ?_, hx⟩
  have key : ∀ z, z ∈ fld Q ∩ codom R → anc Q y0 z → anc Q y1 z →
      x ∈ anc P˘ ʻʻ (R ʻʻ rels (anc Q) y1) := by
    intro z hz h0 h1
    obtain ⟨w, ⟨u, huP, huw⟩, hzw⟩ := h hz
    have hu0 : u ∈ R ʻʻ rels (anc Q) y0 := ⟨w, anc_trans' h0 hzw, huw⟩
    refine ⟨u, ⟨w, anc_trans' h1 hzw, huw⟩, ?_⟩
    rw [anc_cnv]
    rcases hcP u x ⟨huP, hx⟩ with (h2 | e) | h2
    · exact h2
    · subst e
      exact anc_rfl hx
    · exact absurd ⟨u, hu0, h2⟩ hn
  rcases hcQ y0 y1 ⟨hy0.1, hy1.1⟩ with (h2 | e) | h2
  · exact key y1 hy1 h2 (anc_rfl hy1.1)
  · subst e
    exact key _ hy0 (anc_rfl hy0.1) (anc_rfl hy0.1)
  · exact key y0 hy0 (anc_rfl hy0.1) h2

/-- ✱231·201. \[\begin{align}&\vdash :P_{*},Q_{*}\in \text{connex} .RʻʻCʻQ\subset CʻP.\supset .CʻP-(P\overline{R} _{\text{sc}}Q)\subset \breve{P} \overline{R} _{\text{sc}}Q\\ &[*231·2·154·155]\end{align}\] -/
theorem pm231_201 :
    (anc P ∈ connex ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      fld P \ scBar P R Q ⊆ scBar P˘ R Q :=
  fun ⟨hc, h⟩ => pm231_2 ⟨hc, pm231_155 (pm231_154 h)⟩

/-- ✱231·202. \(\vdash :P_{*},Q_{*}\in \text{connex} .\exists !P\overline{R} _{\text{sc}}Q.\supset .CʻP-(P\overline{R} _{\text{sc}}Q)\subset \breve{P} \overline{R} _{\text{sc}}Q\) -/
theorem pm231_202 :
    (anc P ∈ connex ∧ anc Q ∈ connex) ∧ (scBar P R Q).Nonempty →
      fld P \ scBar P R Q ⊆ scBar P˘ R Q := by
  rintro ⟨hc, s, hs⟩
  refine pm231_2 ⟨hc, fun z hz => ?_⟩
  obtain ⟨v, ⟨w, hzw, hvw⟩, hsv⟩ := (mem_scBar'.1 hs).1 z hz
  exact ⟨w, ⟨v, anc_right hsv, hvw⟩, hzw⟩

/-- ✱231·21. \[\begin{align}\vdash :P_{*},Q_{*}\in \text{connex} .&CʻQ\cap \text{ᗡ}ʻR\subset Q_{*}ʻʻ\breve{R} ʻʻCʻP.\supset .\\ &CʻP=P\overline{R} _{\text{sc}}Q\cup \breve{P} \overline{R} _{\text{sc}}Q\end{align}\] -/
theorem pm231_21 :
    (anc P ∈ connex ∧ anc Q ∈ connex) ∧ fld Q ∩ codom R ⊆ anc Q ʻʻ (R˘ ʻʻ fld P) →
      fld P = scBar P R Q ∪ scBar P˘ R Q := by
  intro h
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hs : x ∈ scBar P R Q
    · exact Or.inl hs
    · exact Or.inr (pm231_2 h ⟨hx, hs⟩)
  · rintro x (hx | hx)
    · exact hx.2
    · rw [← fld_cnv P]
      exact hx.2

/-- ✱231·22. \[\begin{align}&\vdash :P_{*},Q_{*}\in \text{connex} .RʻʻCʻQ\subset CʻP.\supset .CʻP=P\overline{R} _{\text{sc}}Q\cup \breve{P} \overline{R} _{\text{sc}}Q\\ &[*231·201·13]\end{align}\] -/
theorem pm231_22 :
    (anc P ∈ connex ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      fld P = scBar P R Q ∪ scBar P˘ R Q :=
  fun ⟨hc, h⟩ => pm231_21 ⟨hc, pm231_155 (pm231_154 h)⟩

/-- ✱231·23. \[\begin{align}\vdash \colon\ldotp P_{*}\in \text{connex} .Rʻʻ&CʻQ\subset CʻP.\supset :\\ &\exists !Rʻʻ\overleftarrow{Q}_{*}ʻy-\overrightarrow{P}_{*}ʻx.\supset .\overrightarrow{P}_{*}ʻx\subset P_{\text{po}}ʻʻRʻʻ\overleftarrow{Q}_{*}ʻy\end{align}\] -/
theorem pm231_23 {x : α} {y : β} :
    anc P ∈ connex ∧ R ʻʻ fld Q ⊆ fld P →
      ((R ʻʻ rels (anc Q) y \ refs (anc P) x).Nonempty →
        refs (anc P) x ⊆ po P ʻʻ (R ʻʻ rels (anc Q) y)) := by
  rintro ⟨hc, h⟩ ⟨v, hv, hvx⟩ w hwx
  rw [mem_connex, fld_anc] at hc
  have hvP : v ∈ fld P := by
    obtain ⟨z, hyz, hvz⟩ := hv
    exact h ⟨z, anc_right hyz, hvz⟩
  have hxP : x ∈ fld P := anc_right hwx
  refine ⟨v, hv, ?_⟩
  rcases hc v x ⟨hvP, hxP⟩ with (h1 | e) | h1
  · exact absurd h1 hvx
  · subst e
    exact absurd (anc_rfl hvP) hvx
  · rcases anc_iff_po.1 h1 with ⟨e, -⟩ | hp
    · subst e
      exact absurd (anc_rfl hvP) hvx
    · exact anc_po_trans hwx hp

/-- ✱231·24. \(\vdash :P_{*}\in \text{connex} .RʻʻCʻQ\subset CʻP.{\sim}{RQ_{\text{cn}}(\overrightarrow{P}_{*}ʻx)}.\supset .\overrightarrow{P}_{*}x\subset P\overline{R} _{\text{sc}}Q\)

**Status.** proved (reading): transcription error: the e-text prints `P⃗_*x` for `P⃗_*'x` in the
conclusion. -/
theorem pm231_24 {x : α} :
    (anc P ∈ connex ∧ R ʻʻ fld Q ⊆ fld P) ∧ ¬cn Q R (refs (anc P) x) →
      refs (anc P) x ⊆ scBar P R Q := by
  rintro ⟨h, hn⟩ w hwx
  rw [mem_scBar']
  refine ⟨fun y hy => ?_, anc_left hwx⟩
  have hne : (R ʻʻ rels (anc Q) y \ refs (anc P) x).Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h0
    exact hn ⟨y, hy, h0⟩
  obtain ⟨u, hu, hwu⟩ := pm231_23 h hne hwx
  exact ⟨u, hu, anc_of_po hwu⟩

private theorem limax_of_max {S : Set α} {x0 : α} (hm : ∀ m, maxP P m S ↔ m = x0) (b : α) :
    limaxP P b S ↔ b = x0 := by
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact (hm b).1 h
    · exact absurd ⟨x0, (hm x0).2 rfl⟩ h
  · intro e
    exact Or.inl ((hm b).2 e)

private theorem limin_of_min {S : Set α} {x0 : α} (hm : ∀ m, minP P m S ↔ m = x0) (b : α) :
    liminP P b S ↔ b = x0 := by
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact (hm b).1 h
    · exact absurd ⟨x0, (hm x0).2 rfl⟩ h
  · intro e
    exact Or.inl ((hm b).2 e)

/-- The cut lemma (cf. ✱215·54·541): for a series `P`, a section `S` with complement `S'` in
`C'P` and a limit or maximum `l` of `S`: `limin_P'S'` is `l`, or it is the immediate successor
of `l`. -/
private theorem cut_limax (hS : P ∈ Ser) {S S' : Set α} (hsect : S ∈ sect P)
    (hS' : ∀ u, u ∈ S' ↔ u ∈ fld P ∧ u ∉ S) {l : α} (hl : limaxP P l S) :
    (∀ b, liminP P b S' ↔ b = l) ∨ ∃ n, (∀ b, liminP P b S' ↔ b = n) ∧ P1 P l n := by
  obtain ⟨⟨hirr, htr⟩, hcon⟩ := Ser_parts hS
  have hcP : P ∈ connex := Ser_connex hS
  have F : ∀ s u, s ∈ S → u ∈ S' → P s u := by
    intro s u hs hu
    obtain ⟨huP, huS⟩ := (hS' u).1 hu
    rcases hcon s u (hsect.1 hs) huP with (h | e) | h
    · exact h
    · subst e
      exact absurd hs huS
    · exact absurd (hsect.2 ⟨s, hs, h⟩) huS
  rcases hl with hmax | ⟨hseq, hnomax⟩
  · rw [maxP_iff] at hmax
    obtain ⟨⟨hlS, hlP⟩, hmax⟩ := hmax
    have charS' : ∀ u, u ∈ S' ↔ u ∈ fld P ∧ P l u := fun u =>
      ⟨fun hu => ⟨((hS' u).1 hu).1, F l u hlS hu⟩,
        fun ⟨huP, hlu⟩ => (hS' u).2 ⟨huP, fun huS => hmax u huS hlu⟩⟩
    by_cases hmin : ∃ n, minP P n S'
    · obtain ⟨n, hn⟩ := hmin
      right
      have hn' := hn
      rw [minP_iff] at hn'
      refine ⟨n, fun b => ⟨fun hb => ?_, fun e => e ▸ Or.inl hn⟩, ?_⟩
      · rcases hb with hb | ⟨-, hb⟩
        · exact minP_unique hcP hb hn
        · exact absurd ⟨n, hn⟩ hb
      · rw [P1_iff_of_transR (Ser_transR hS) (Ser_rlJ hS)]
        refine ⟨((charS' n).1 hn'.1.1).2, fun ⟨z, hlz, hzn⟩ => ?_⟩
        exact hn'.2 z ((charS' z).2 ⟨fld_of_right hlz, hlz⟩) hzn
    · left
      have hprec : ∀ b, precP P b S' ↔ b = l := by
        intro b
        rw [precP_iff]
        constructor
        · rintro ⟨⟨hlow, hbP⟩, hmaxb⟩
          rcases hcon b l hbP hlP with (h | e) | h
          · exact absurd h (hmaxb l fun y hy => ((charS' y).1 hy.1).2)
          · exact e
          · exact absurd (hlow b ⟨(charS' b).2 ⟨hbP, h⟩, hbP⟩) (hirr b)
        · intro e
          subst e
          refine ⟨⟨fun y hy => ((charS' y).1 hy.1).2, hlP⟩, fun z hz hlz => ?_⟩
          exact hirr z (hz z ⟨(charS' z).2 ⟨fld_of_right hlz, hlz⟩, fld_of_right hlz⟩)
      intro b
      constructor
      · rintro (hb | ⟨hb, -⟩)
        · exact absurd ⟨b, hb⟩ hmin
        · exact (hprec b).1 hb
      · intro e
        exact Or.inr ⟨(hprec b).2 e, hmin⟩
  · rw [seqP_iff] at hseq
    obtain ⟨⟨hup, hlP⟩, hleast⟩ := hseq
    have hlS : l ∉ S := fun h => hirr l (hup l ⟨h, hlP⟩)
    have hminl : minP P l S' := by
      rw [minP_iff]
      refine ⟨⟨(hS' l).2 ⟨hlP, hlS⟩, hlP⟩, fun y hy => ?_⟩
      exact hleast y fun s hs => F s y hs.1 hy
    left
    intro b
    constructor
    · rintro (hb | ⟨-, hb⟩)
      · exact minP_unique hcP hb hminl
      · exact absurd ⟨l, hminl⟩ hb
    · intro e
      exact e ▸ Or.inl hminl

/-- ✱231·25. \[\begin{align}\vdash \colon\ldotp &P\in \text{Ser}.Q_{*}\in \text{connex} .RʻʻCʻQ\subset CʻP.P\overline{R} _{\text{os}}Q=\Lambda .\\ &\text{E}!\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q).\supset :\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q=\text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q).\lor.\\ &\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q)P_{1}\text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q)\\ &[*215·54·541.*231·13·22]\end{align}\]

**Status.** proved (reading): transcription error: the e-text omits the closing bracket of
`limax_P'(P R̄_sc Q)` before `=`. The hypothesis is the product of five, bracketed to the left;
each disjunct is an equation (or `P_1`-relation) between two descriptions, the first having the
larger scope. -/
theorem pm231_25 :
    (((P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P) ∧ osBar P R Q = Λ) ∧
        EDesc (limaxP P) (scBar P R Q) →
      Desc (limaxP P) (scBar P R Q)
          (fun a => Desc (liminP P) (scBar P˘ R Q) (fun b => a = b)) ∨
        Desc (limaxP P) (scBar P R Q)
          (fun a => Desc (liminP P) (scBar P˘ R Q) (fun b => P1 P a b)) := by
  rintro ⟨⟨⟨⟨hS, hcQ⟩, h⟩, hos⟩, l, hl⟩
  have hU := pm231_22 ⟨⟨connex_anc (Ser_connex hS), hcQ⟩, h⟩
  have hS' : ∀ u, u ∈ scBar P˘ R Q ↔ u ∈ fld P ∧ u ∉ scBar P R Q := by
    intro u
    constructor
    · intro hu
      refine ⟨by rw [← fld_cnv P]; exact hu.2, fun hu' => ?_⟩
      have : u ∈ osBar P R Q := ⟨hu', hu⟩
      rw [hos] at this
      exact not_mem_null this
    · rintro ⟨huP, huS⟩
      rw [hU] at huP
      exact huP.resolve_left huS
  rcases cut_limax hS pm231_13 hS' ((hl l).2 rfl) with h1 | ⟨n, h1, h2⟩
  · left
    exact (TheIs_iff_of_unique hl).2 ((TheIs_iff_of_unique h1).2 rfl)
  · right
    exact (TheIs_iff_of_unique hl).2 ((TheIs_iff_of_unique h1).2 h2)

/-- ✱231·251. \[\begin{align}\vdash :\text{Hp}*231·25.&\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q){\sim}\in \text{D}ʻP_{1}.\supset .\\ &\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q)=\text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q) \quad[*231·25]\end{align}\]

"Hp ✱231·25" is the hypothesis of ✱231·25, written out. -/
theorem pm231_251 :
    ((((P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P) ∧ osBar P R Q = Λ) ∧
          EDesc (limaxP P) (scBar P R Q)) ∧
        Desc (limaxP P) (scBar P R Q) (fun l => l ∉ dom (P1 P)) →
      Desc (limaxP P) (scBar P R Q)
        (fun a => Desc (liminP P) (scBar P˘ R Q) (fun b => a = b)) := by
  rintro ⟨hp, hd⟩
  rcases pm231_25 hp with h | h
  · exact h
  · exfalso
    obtain ⟨l, hl⟩ := hp.2
    have hd' := (TheIs_iff_of_unique hl).1 hd
    obtain ⟨n, -, hP1⟩ := (TheIs_iff_of_unique hl).1 h
    exact hd' ⟨n, hP1⟩

/-- ✱231·252. \[\begin{align}\vdash :&P\in \text{Ser}.Q_{*}\in \text{connex} .RʻʻCʻQ\subset CʻP.P\overline{R} _{\text{os}}\in 0\cup 1.\\ &\text{E}!\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q).\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q){\sim}e\in \text{D}ʻP_{1}.\supset .\\ &\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q)=\text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q)\\ &[*215·543.*231·13·22]\end{align}\]

**Status.** proved (reading): transcription errors: the e-text prints `P R̄_os ∈ 0 ∪ 1` for
`P R̄_os Q ∈ 0 ∪ 1` and `∼e∈` for `∼∈`. -/
theorem pm231_252 :
    (((((P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P) ∧ osBar P R Q ∈ zero ∪ one) ∧
          EDesc (limaxP P) (scBar P R Q)) ∧
        Desc (limaxP P) (scBar P R Q) (fun l => l ∉ dom (P1 P))) →
      Desc (limaxP P) (scBar P R Q)
        (fun a => Desc (liminP P) (scBar P˘ R Q) (fun b => a = b)) := by
  rintro ⟨⟨⟨hSQ, h01⟩, hE⟩, hd⟩
  rcases h01 with h0 | h1
  · rw [zero_eq] at h0
    have : osBar P R Q = Λ := by
      rw [Null_eq_empty]
      exact h0
    exact pm231_251 ⟨⟨⟨hSQ, this⟩, hE⟩, hd⟩
  · obtain ⟨x0, hx0⟩ := mem_one_iff.1 h1
    have hS := hSQ.1.1
    have hpo : po P ∈ Ser := by
      rw [po_eq_of_transR (Ser_transR hS)]
      exact hS
    have hS' : po P˘ ∈ Ser := by
      rw [po_cnv_eq]
      exact Ser_cnv hpo
    have hx0' : ∀ z, z ∈ osBar P˘ R Q ↔ z = x0 := fun z => by rw [osBar_cnv]; exact hx0 z
    have hm := limax_of_max (max_sc_of_os hpo hx0)
    have hn : ∀ n, minP P n (scBar P˘ R Q) ↔ n = x0 := max_sc_of_os hS' hx0'
    exact (TheIs_iff_of_unique hm).2 ((TheIs_iff_of_unique (limin_of_min hn)).2 rfl)

/-- ✱231·4. \(\vdash :Q\in \text{trans}\cap \text{connex} .\text{E}!\text{max}_{Q}ʻ\text{ᗡ}ʻR.\supset .P\overline{R} _{\text{sc}}Q=P_{*}ʻʻ\overrightarrow{R}ʻ\text{max}_{Q}ʻ\text{ᗡ}ʻR\)

`P_*''R⃗'max_Q'ᗡ'R` is `Desc (maxP Q) (codom R) (fun m => … anc P ʻʻ refs R m)`. -/
theorem pm231_4 :
    Q ∈ transR ∩ connex ∧ EDesc (maxP Q) (codom R) →
      Desc (maxP Q) (codom R) (fun m => scBar P R Q = anc P ʻʻ refs R m) := by
  rintro ⟨hQ, m, hm⟩
  have key : ∀ C, cn Q R C ↔ refs R m ⊆ C := fun C =>
    (pm230_53 (A := C) ⟨hQ, ⟨m, hm⟩⟩).trans (TheIs_iff_of_unique hm)
  refine (TheIs_iff_of_unique hm).2 ?_
  ext x
  rw [mem_scBar]
  constructor
  · rintro ⟨h, -⟩
    exact h _ ((key _).2 le_rfl)
  · rintro ⟨v, hv, hxv⟩
    exact ⟨fun C hC => ⟨v, (key C).1 hC hv, hxv⟩, anc_left hxv⟩

/-- ✱231·41. \(\vdash :Q\in \text{trans}\cap \text{connex} .\text{E}!Rʻ\text{max}_{Q}ʻ\text{ᗡ}ʻR.\supset .P\overline{R} _{\text{sc}}Q=\overrightarrow{P}_{*}ʻRʻ\text{max}_{Q}ʻ\text{ᗡ}ʻR\)

`E!R'max_Q'ᗡ'R` is `Desc (maxP Q) (codom R) (fun m => EDesc R m)`, and `P⃗_*'R'max_Q'ᗡ'R` is the
double description `Desc2 R (maxP Q) (codom R) (fun v => … refs (anc P) v)` (✱30·02). -/
theorem pm231_41 :
    Q ∈ transR ∩ connex ∧ Desc (maxP Q) (codom R) (fun m => EDesc R m) →
      Desc2 R (maxP Q) (codom R) (fun v => scBar P R Q = refs (anc P) v) := by
  rintro ⟨hQ, m, hm, v, hv⟩
  rw [desc2_iff]
  refine (TheIs_iff_of_unique hm).2 ((TheIs_iff_of_unique hv).2 ?_)
  have h4 := (TheIs_iff_of_unique hm).1 (pm231_4 (P := P) ⟨hQ, ⟨m, hm⟩⟩)
  rw [h4]
  ext x
  constructor
  · rintro ⟨w, hw, hxw⟩
    rw [(hv w).1 hw] at hxw
    exact hxw
  · intro hx
    exact ⟨v, (hv v).2 rfl, hx⟩

/-!
## [✱232] On the oscillation of a function as the argument approaches a given limit

*(Vol. 2, p. 737)*

> *Summary of* *232.
>
> …

**Lean reading.** `(P R̄ Q)_sc'α` and `(P R̄ Q)_os'α` are `scFun P R Q S` and `osFun P R Q S` (value functions of
the relations `scRel P R Q`, `osRel P R Q`, ✱232·01·02), with `S : Set β` a class of
arguments; `Q_* ⥏ α` is `anc Q ⥏ S` and `Q_*''(α ∩ ᗡ'R)` is `anc Q ʻʻ (S ∩ codom R)`.
`(α ∩)` (✱38 with `♀ = ∩`) is the relation `opL (fun A B : Set β => A ∩ B) S` of `α ∩ β` to
`β`. `Q⃗'x` is `refs Q x`, `ι'x` (also printed `℩'x`) is `ι x`, `1 − Cl'ᗡ'P_1` is
`one \ cl (codom (P1 P))`, `0 ∪ 1` is `zero ∪ one`, `limax⃗_P'…` is `refs (limaxP P) …`,
`ῐ'…` is `Desc iota˘ … ψ`; `max_P`, `min_P`, `seq_P`, `prec_P`, `limax_P`, `limin_P` of a
class are descriptions (`Desc`), the first of two in one equation having the larger scope; an
equation chain is the conjunction of its links. "Hp ✱232·N" is written out. The proofs reduce
to ✱231 for the relation `anc Q ⥏ S` (whose ancestral is itself and whose field is `S ∩ C'Q`),
and to abstract lemmas about a lower section `A` and an upper section `B` of `P` with
`A ⊂ P⃗_*'x`, `B ⊂ P⃖_*'x` (✱232·35–·361).

**Status.** proved (all propositions; ✱232·01·02 definition; ✱232·341 proved (reading); ✱232·355,
✱232·357, ✱232·36, ✱232·52 proved (corrected): ✱232·355 needs `P_po ⊂̇ J`, ✱232·357 needs
`(P R̄ Q)_sc'α ∪ (P̆ R̄ Q)_sc'α = C'P`, the second clause of ✱232·36 interchanges `P` and `P̆`,
✱232·52 needs `Q ∈ trans`; see their docstrings)
-/

/-- ✱232·01 (Df). \((P\overline{R}Q)_{\text{sc}}ʻ\alpha = P\overline{R}_{\text{sc}}(Q_{*} \unicode{x0294f} \alpha ) \quad\text{Df}\) -/
theorem pm232_01 {S : Set β} : scFun P R Q S = scBar P R (anc Q ⥏ S) := rfl

/-- ✱232·02 (Df). \((P\overline{R}Q)_{\text{os}}ʻ\alpha = P\overline{R}_{\text{os}}(Q_{*} \unicode{x0294f} \alpha ) \quad\text{Df}\) -/
theorem pm232_02 {S : Set β} : osFun P R Q S = osBar P R (anc Q ⥏ S) := rfl

/-- ✱232·1. \(\vdash . (P\overline{R}Q)_{\text{sc}}ʻ\alpha = P\overline{R}_{\text{sc}}(Q_{*} \unicode{x0294f} \alpha ) \quad[(*232·01)]\) -/
theorem pm232_1 {S : Set β} : scFun P R Q S = scBar P R (anc Q ⥏ S) := rfl

/-- ✱232·101. \(\vdash . (P\overline{R}Q)_{\text{os}}ʻ\alpha = P\overline{R}_{\text{os}}(Q_{*} \unicode{x0294f} \alpha ) = (P\overline{R}Q)_{\text{sc}}ʻ\alpha \cap (\breve{P} \overline{R}Q)_{\text{sc}}ʻ\alpha \quad[(*232·02)]\)

The chain of three is the conjunction of its two links. -/
theorem pm232_101 {S : Set β} :
    osFun P R Q S = osBar P R (anc Q ⥏ S) ∧
      osBar P R (anc Q ⥏ S) = scFun P R Q S ∩ scFun P˘ R Q S :=
  ⟨rfl, rfl⟩

private theorem mem_scFun' {P : α → α → Prop} {S : Set β} {x : α} :
    x ∈ scFun P R Q S ↔
      (∀ y, y ∈ S ∩ fld Q ∩ codom R → x ∈ anc P ʻʻ (R ʻʻ (S ∩ rels (anc Q) y))) ∧
        x ∈ fld P := by
  show x ∈ scBar P R (anc Q ⥏ S) ↔ _
  rw [mem_scBar']
  refine and_congr ⟨fun h y ⟨⟨hyS, hyQ⟩, hyR⟩ => ?_, fun h y ⟨hy, hyR⟩ => ?_⟩ Iff.rfl
  · obtain ⟨v, ⟨z, hyz, hvz⟩, hxv⟩ := h y ⟨fld_ancFres.2 ⟨hyS, hyQ⟩, hyR⟩
    exact ⟨v, ⟨z, ⟨(anc_ancFres.1 hyz).2, (anc_ancFres.1 hyz).1.2⟩, hvz⟩, hxv⟩
  · obtain ⟨hyS, hyQ⟩ := fld_ancFres.1 hy
    obtain ⟨v, ⟨z, ⟨hzS, hyz⟩, hvz⟩, hxv⟩ := h y ⟨⟨hyS, hyQ⟩, hyR⟩
    exact ⟨v, ⟨z, anc_ancFres.2 ⟨⟨hyS, hyz⟩, hzS⟩, hvz⟩, hxv⟩

private theorem img_inter_eq {S : Set β} {y : β} :
    R ʻʻ (S ∩ rels (anc Q) y) = R ʻʻ (S ∩ fld Q ∩ codom R ∩ rels (anc Q) y) := by
  ext v
  exact ⟨fun ⟨z, ⟨hzS, hyz⟩, hvz⟩ => ⟨z, ⟨⟨⟨hzS, anc_right hyz⟩, v, hvz⟩, hyz⟩, hvz⟩,
    fun ⟨z, ⟨⟨⟨hzS, _⟩, _⟩, hyz⟩, hvz⟩ => ⟨z, ⟨hzS, hyz⟩, hvz⟩⟩

private theorem mem_scFun'' {P : α → α → Prop} {S : Set β} {x : α} :
    x ∈ scFun P R Q S ↔
      (∀ y, y ∈ S ∩ fld Q ∩ codom R →
        x ∈ anc P ʻʻ (R ʻʻ (S ∩ fld Q ∩ codom R ∩ rels (anc Q) y))) ∧ x ∈ fld P := by
  rw [mem_scFun']
  simp only [← img_inter_eq]

/-- ✱232·11. \[\begin{align}\vdash \colon\ldotp x \in (P\overline{R}Q)_{\text{sc}}ʻ&\alpha . \equiv :\\ &y \in \alpha \cap CʻQ \cap \text{ᗡ}ʻR . \supset _y . x \in P_{*}ʻʻRʻʻ(\alpha \cap \overleftarrow{Q}_*ʻy) : x \in CʻP\end{align}\] -/
theorem pm232_11 {S : Set β} {x : α} :
    x ∈ scFun P R Q S ↔
      (∀ y, y ∈ S ∩ fld Q ∩ codom R → x ∈ anc P ʻʻ (R ʻʻ (S ∩ rels (anc Q) y))) ∧
        x ∈ fld P :=
  mem_scFun'

private theorem mem_prodCls_img3' {T X : Set β} {x : α} :
    x ∈ prodCls (anc P ʻʻʻ R ʻʻʻ opL (fun A B : Set β => A ∩ B) T ʻʻ Rbwd (anc Q) ʻʻ X) ↔
      ∀ y, y ∈ X → x ∈ anc P ʻʻ (R ʻʻ (T ∩ rels (anc Q) y)) := by
  constructor
  · intro h y hy
    exact h _ ⟨_, ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  · rintro h C ⟨B, ⟨B', ⟨B'', ⟨y, hy, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact h y hy

/-- ✱232·12. \[\begin{align}&\vdash .(P\overline{R} Q)_{\text{sc}}ʻ\alpha =pʻP_{*}ʻʻʻRʻʻʻ(\alpha \cap )ʻʻ\overleftarrow{Q}_{*}ʻʻ(\alpha \cap CʻQ\cap \text{ᗡ}ʻR)\cap CʻP\\ &[*232·11]\end{align}\]

`(α ∩)` is the relation `opL (fun A B : Set β => A ∩ B) S` (✱38·01 with `♀ = ∩`), so
`R'''(α ∩)''Q⃖_*''γ` is `R ʻʻʻ opL (fun A B : Set β => A ∩ B) S ʻʻ Rbwd (anc Q) ʻʻ γ`. -/
theorem pm232_12 {S : Set β} :
    scFun P R Q S =
      prodCls (anc P ʻʻʻ R ʻʻʻ opL (fun A B : Set β => A ∩ B) S ʻʻ
        Rbwd (anc Q) ʻʻ (S ∩ fld Q ∩ codom R)) ∩ fld P := by
  ext x
  rw [mem_scFun', Set.mem_inter_iff, mem_prodCls_img3']

/-- ✱232·121. \(\vdash :\gamma =\alpha \cap CʻQ\cap \text{ᗡ}ʻR.\supset .(P\overline{R} Q)_{\text{sc}}ʻ\alpha =pʻP_{*}ʻʻʻRʻʻʻ(\gamma \cap )ʻʻ\overleftarrow{Q}_{*}ʻʻ\gamma \cap CʻP\) -/
theorem pm232_121 {S G : Set β} :
    G = S ∩ fld Q ∩ codom R →
      scFun P R Q S =
        prodCls (anc P ʻʻʻ R ʻʻʻ opL (fun A B : Set β => A ∩ B) G ʻʻ Rbwd (anc Q) ʻʻ G) ∩
          fld P := by
  rintro rfl
  ext x
  rw [mem_scFun'', Set.mem_inter_iff, mem_prodCls_img3']

/-- ✱232·13. \[\begin{align}&\vdash :\alpha \cap CʻQ\cap \text{ᗡ}ʻR=\beta \cap CʻQ\cap \text{ᗡ}ʻR.\supset .(P\overline{R} Q)_{\text{sc}}ʻ\alpha =(P\overline{R} Q)_{\text{sc}}ʻ\beta\\ &[*232·121]\end{align}\] -/
theorem pm232_13 {S T : Set β} :
    S ∩ fld Q ∩ codom R = T ∩ fld Q ∩ codom R → scFun P R Q S = scFun P R Q T := by
  intro h
  ext x
  rw [mem_scFun'', mem_scFun'', h]

/-- ✱232·131. \(\vdash .(P\overline{R} Q)_{\text{sc}}ʻ\alpha =(P\overline{R} Q)_{\text{sc}}ʻ(\alpha \cap CʻQ\cap \text{ᗡ}ʻR) \quad[*232·13]\) -/
theorem pm232_131 {S : Set β} : scFun P R Q S = scFun P R Q (S ∩ fld Q ∩ codom R) := by
  apply pm232_13
  ext y
  exact ⟨fun h => ⟨⟨h, h.1.2⟩, h.2⟩, fun h => h.1.1⟩

private theorem scBar_congrQ {Q Q' : β → β → Prop} (hf : ∀ y, y ∈ fld Q ↔ y ∈ fld Q')
    (ha : ∀ y z, anc Q y z ↔ anc Q' y z) : scBar P R Q = scBar P R Q' := by
  ext x
  rw [mem_scBar', mem_scBar']
  refine and_congr (forall_congr' fun y => ?_) Iff.rfl
  have e1 : y ∈ fld Q ∩ codom R ↔ y ∈ fld Q' ∩ codom R := and_congr (hf y) Iff.rfl
  have e2 : rels (anc Q) y = rels (anc Q') y := Set.ext fun z => ha y z
  rw [e1, e2]

/-- ✱232·14. \[\begin{align}&\vdash :Q\in \text{trans} \cap\text{connex} .\alpha \cap CʻQ{\sim}\in 1.\supset .(P\overline{R} Q)_{\text{sc}}ʻ\alpha =P\overline{R} _{\text{sc}}(Q\unicode{x0294f}\alpha )\\ &[*232·1.*202·54·541]\end{align}\]

`α ∩ C'Q ∼∈ 1` is `S ∩ fld Q ∉ one`. -/
theorem pm232_14 {S : Set β} :
    Q ∈ transR ∩ connex ∧ S ∩ fld Q ∉ one → scFun P R Q S = scBar P R (Q ⥏ S) := by
  rintro ⟨⟨htr, hcon⟩, hn1⟩
  rw [mem_connex] at hcon
  have tr := mem_transR.1 htr
  have hfld : ∀ y, y ∈ fld (Q ⥏ S) ↔ y ∈ S ∧ y ∈ fld Q := by
    intro y
    constructor
    · rintro ⟨z, ⟨⟨h1, h2⟩, _⟩ | ⟨⟨_, h2⟩, h3⟩⟩
      · exact ⟨h1, fld_of_left h2⟩
      · exact ⟨h3, fld_of_right h2⟩
    · rintro ⟨hyS, hyQ⟩
      by_contra hn
      apply hn1
      rw [mem_one_iff]
      refine ⟨y, fun z => ⟨fun ⟨hzS, hzQ⟩ => ?_, fun e => e ▸ ⟨hyS, hyQ⟩⟩⟩
      rcases hcon z y ⟨hzQ, hyQ⟩ with (h | e) | h
      · exact absurd ⟨z, Or.inr ⟨⟨hzS, h⟩, hyS⟩⟩ hn
      · exact e
      · exact absurd ⟨z, Or.inl ⟨⟨hyS, h⟩, hzS⟩⟩ hn
  have htrS : Q ⥏ S ∈ transR := mem_transR.2 fun a b c ⟨h1, h2⟩ =>
    ⟨⟨h1.1.1, tr a b c ⟨h1.1.2, h2.1.2⟩⟩, h2.2⟩
  show scBar P R (anc Q ⥏ S) = scBar P R (Q ⥏ S)
  refine scBar_congrQ (fun y => fld_ancFres.trans (hfld y).symm) fun y z => ?_
  rw [anc_ancFres, anc_iff_of_transR htrS, anc_iff_of_transR htr, hfld]
  constructor
  · rintro ⟨⟨hyS, ⟨rfl, hyQ⟩ | hyz⟩, hzS⟩
    · exact Or.inl ⟨rfl, hyS, hyQ⟩
    · exact Or.inr ⟨⟨hyS, hyz⟩, hzS⟩
  · rintro (⟨rfl, hyS, hyQ⟩ | ⟨⟨hyS, hyz⟩, hzS⟩)
    · exact ⟨⟨hyS, Or.inl ⟨rfl, hyQ⟩⟩, hyS⟩
    · exact ⟨⟨hyS, Or.inr hyz⟩, hzS⟩

/-- ✱232·15. \[\begin{align}&\vdash :\alpha \cap CʻQ\cap \text{ᗡ}ʻR=\Lambda .\supset .(P\overline{R} Q)_{\text{sc}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =(P\overline{R} Q)_{\text{os}}ʻ\alpha =CʻP\\ &[*232·12·101.*37·29.*40·2]\end{align}\]

The chain of four is the conjunction of its three links. -/
theorem pm232_15 {S : Set β} :
    S ∩ fld Q ∩ codom R = Λ →
      (scFun P R Q S = scFun P˘ R Q S ∧ scFun P˘ R Q S = osFun P R Q S) ∧
        osFun P R Q S = fld P := by
  intro h
  have h1 : ∀ P' : α → α → Prop, scFun P' R Q S = fld P' := fun P' => by
    ext x
    rw [mem_scFun']
    refine ⟨fun h' => h'.2, fun hx => ⟨fun y hy => ?_, hx⟩⟩
    rw [h] at hy
    exact absurd hy not_mem_null
  have h2 : osFun P R Q S = fld P := by
    show scFun P R Q S ∩ scFun P˘ R Q S = fld P
    rw [h1, h1, fld_cnv, Set.inter_self]
  rw [h2, h1, h1, fld_cnv]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- ✱232·151. \[\begin{align}&\vdash :\dot{\exists} !P.(P\overline{R} Q)_{\text{os}}ʻ\alpha =\Lambda .\supset .\exists !\alpha \cap CʻQ\cap \text{ᗡ}ʻR\\ &[*232·15.\text{Transp}.*33·24]\end{align}\] -/
theorem pm232_151 {S : Set β} : rEx P ∧ osFun P R Q S = Λ → (S ∩ fld Q ∩ codom R).Nonempty := by
  rintro ⟨⟨a, b, hab⟩, h⟩
  by_contra hn
  have e : S ∩ fld Q ∩ codom R = Λ := eq_null_of fun y hy => hn ⟨y, hy⟩
  have := (pm232_15 (P := P) e).2
  rw [h] at this
  have ha : a ∈ fld P := fld_of_left hab
  rw [← this] at ha
  exact not_mem_null ha

/-- ✱232·2. \(\vdash :CʻQ\cap \text{ᗡ}ʻR\subset \alpha .\supset .(P\overline{R} Q)_{\text{sc}}ʻ\alpha =P\overline{R} _{\text{sc}}Q\) -/
theorem pm232_2 {S : Set β} : fld Q ∩ codom R ⊆ S → scFun P R Q S = scBar P R Q := by
  intro h
  ext x
  rw [mem_scFun', mem_scBar']
  refine and_congr ⟨fun h' y hy => ?_, fun h' y hy => ?_⟩ Iff.rfl
  · obtain ⟨v, ⟨z, ⟨_, hyz⟩, hvz⟩, hxv⟩ := h' y ⟨⟨h hy, hy.1⟩, hy.2⟩
    exact ⟨v, ⟨z, hyz, hvz⟩, hxv⟩
  · obtain ⟨v, ⟨z, hyz, hvz⟩, hxv⟩ := h' y ⟨hy.1.2, hy.2⟩
    exact ⟨v, ⟨z, ⟨h ⟨anc_right hyz, v, hvz⟩, hyz⟩, hvz⟩, hxv⟩

private theorem anc_ancFres_eq {S : Set β} : anc (anc Q ⥏ S) = anc Q ⥏ S := by
  funext y z
  exact propext anc_ancFres

/-- ✱232·21. \[\begin{align}&\vdash :P_{*},Q_{*}\unicode{x0294f}\alpha \in \text{connex} .\alpha \cap CʻQ\cap \text{ᗡ}ʻR\subset Q_{*}ʻʻ(\alpha \cap \breve{R} ʻʻCʻP).\supset .\\ &CʻP=(P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha \\ &\left[*231·21 \frac{Q_{*}\unicode{x0294f}\alpha}{Q}\right]\end{align}\]

`Q_* ⥏ α ∈ connex` is `anc Q ⥏ S ∈ connex`; `Q_*''(α ∩ R̆''C'P)` is
`anc Q ʻʻ (S ∩ R˘ ʻʻ fld P)`. -/
theorem pm232_21 {S : Set β} :
    (anc P ∈ connex ∧ anc Q ⥏ S ∈ connex) ∧
        S ∩ fld Q ∩ codom R ⊆ anc Q ʻʻ (S ∩ R˘ ʻʻ fld P) →
      fld P = scFun P R Q S ∪ scFun P˘ R Q S := by
  rintro ⟨⟨hcP, hcQ⟩, h⟩
  have hcQ' : anc (anc Q ⥏ S) ∈ connex := by
    rw [anc_ancFres_eq]
    exact hcQ
  show fld P = scBar P R (anc Q ⥏ S) ∪ scBar P˘ R (anc Q ⥏ S)
  refine pm231_21 ⟨⟨hcP, hcQ'⟩, ?_⟩
  rintro y ⟨hy, hyR⟩
  obtain ⟨hyS, hyQ⟩ := fld_ancFres.1 hy
  obtain ⟨z, ⟨hzS, hz⟩, hyz⟩ := h ⟨⟨hyS, hyQ⟩, hyR⟩
  exact ⟨z, hz, anc_ancFres.2 ⟨⟨hyS, hyz⟩, hzS⟩⟩

/-- ✱232·22. \[\begin{align}\vdash :P_{*},Q_{*}\unicode{x0294f}\alpha \in \text{connex} .Rʻʻ&(\alpha \cap CʻQ)\subset CʻP.\supset .\\ &CʻP=(P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha \quad[*231·22]\end{align}\] -/
theorem pm232_22 {S : Set β} :
    (anc P ∈ connex ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P →
      fld P = scFun P R Q S ∪ scFun P˘ R Q S := by
  rintro ⟨⟨hcP, hcQ⟩, h⟩
  have hcQ' : anc (anc Q ⥏ S) ∈ connex := by
    rw [anc_ancFres_eq]
    exact hcQ
  show fld P = scBar P R (anc Q ⥏ S) ∪ scBar P˘ R (anc Q ⥏ S)
  refine pm231_22 ⟨⟨hcP, hcQ'⟩, ?_⟩
  rintro v ⟨y, hy, hvy⟩
  exact h ⟨y, fld_ancFres.1 hy, hvy⟩

/-- ✱232·23. \(\vdash :y\in CʻQ\cap \text{ᗡ}ʻR.\supset .(P\overline{R} Q)_{\text{sc}}ʻ\iota ʻy=P_{*}ʻʻ\overrightarrow{R}ʻy\) -/
theorem pm232_23 {y : β} : y ∈ fld Q ∩ codom R → scFun P R Q (ι y) = anc P ʻʻ refs R y := by
  intro hy
  ext x
  rw [mem_scFun']
  constructor
  · rintro ⟨h, -⟩
    obtain ⟨v, ⟨z, ⟨hz, -⟩, hvz⟩, hxv⟩ := h y ⟨⟨rfl, hy.1⟩, hy.2⟩
    rw [mem_unitCls] at hz
    rw [← hz]
    exact ⟨v, hvz, hxv⟩
  · rintro ⟨v, hv, hxv⟩
    refine ⟨fun y' ⟨⟨hy', _⟩, _⟩ => ?_, anc_left hxv⟩
    rw [mem_unitCls] at hy'
    rw [hy']
    exact ⟨v, ⟨y, ⟨rfl, anc_rfl hy.1⟩, hv⟩, hxv⟩

/-- ✱232·24. \[\begin{align}\vdash :Q\in \text{trans}\cap \text{connex} .\text{E}!\text{max}_{Q}ʻ&(\alpha \cap \text{ᗡ}ʻR).\supset .\\ &(P\overline{R} Q)_{\text{sc}}ʻ\alpha =P_{*}ʻʻ\overrightarrow{R}ʻ\text{max}_{Q}ʻ(\alpha \cap \text{ᗡ}ʻR)\end{align}\]

`P_*''R⃗'max_Q'(α ∩ ᗡ'R)` is `Desc (maxP Q) (S ∩ codom R) (fun m => … anc P ʻʻ refs R m)`. -/
theorem pm232_24 {S : Set β} :
    Q ∈ transR ∩ connex ∧ EDesc (maxP Q) (S ∩ codom R) →
      Desc (maxP Q) (S ∩ codom R) (fun m => scFun P R Q S = anc P ʻʻ refs R m) := by
  rintro ⟨⟨htr, hcon⟩, m, hm⟩
  refine (TheIs_iff_of_unique hm).2 ?_
  obtain ⟨⟨⟨hmS, hmR⟩, hmQ⟩, hmax⟩ := maxP_iff.1 ((hm m).2 rfl)
  rw [mem_connex] at hcon
  ext x
  rw [mem_scFun']
  constructor
  · rintro ⟨h, -⟩
    obtain ⟨v, ⟨z, ⟨hzS, hmz⟩, hvz⟩, hxv⟩ := h m ⟨⟨hmS, hmQ⟩, hmR⟩
    rcases anc_iff_po.1 hmz with ⟨e, -⟩ | hp
    · rw [e]
      exact ⟨v, hvz, hxv⟩
    · rw [po_eq_of_transR htr] at hp
      exact absurd hp (hmax z ⟨hzS, v, hvz⟩)
  · rintro ⟨v, hv, hxv⟩
    refine ⟨fun y ⟨⟨hyS, hyQ⟩, hyR⟩ => ⟨v, ⟨m, ⟨hmS, ?_⟩, hv⟩, hxv⟩, anc_left hxv⟩
    rcases hcon y m ⟨hyQ, hmQ⟩ with (h | e) | h
    · exact anc_of h
    · rw [e]
      exact anc_rfl hmQ
    · exact absurd h (hmax y ⟨hyS, hyR⟩)

/-- ✱232·3. \(\vdash :\alpha \subset \text{ᗡ}ʻR.\supset .(P\overline{R} Q)_{\text{sc}}ʻ\alpha \subset (P\overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ\alpha\) -/
theorem pm232_3 {S : Set β} : S ⊆ codom R → scFun P R Q S ⊆ scFun P R Q (anc Q ʻʻ S) := by
  intro hS x hx
  rw [mem_scFun'] at hx ⊢
  refine ⟨fun y ⟨⟨⟨z, hzS, hyz⟩, _⟩, _⟩ => ?_, hx.2⟩
  obtain ⟨v, ⟨w, ⟨hwS, hzw⟩, hvw⟩, hxv⟩ := hx.1 z ⟨⟨hzS, anc_right hyz⟩, hS hzS⟩
  exact ⟨v, ⟨w, ⟨⟨w, hwS, anc_rfl (anc_right hzw)⟩, anc_trans' hyz hzw⟩, hvw⟩, hxv⟩

/-- ✱232·301. \(\vdash .(P\overline{R} Q)_{\text{sc}}ʻ\alpha \subset (P\overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\) -/
theorem pm232_301 {S : Set β} : scFun P R Q S ⊆ scFun P R Q (anc Q ʻʻ (S ∩ codom R)) := by
  intro x hx
  rw [mem_scFun'] at hx ⊢
  refine ⟨fun y ⟨⟨⟨z, ⟨hzS, hzR⟩, hyz⟩, _⟩, _⟩ => ?_, hx.2⟩
  obtain ⟨v, ⟨w, ⟨hwS, hzw⟩, hvw⟩, hxv⟩ := hx.1 z ⟨⟨hzS, anc_right hyz⟩, hzR⟩
  exact ⟨v, ⟨w, ⟨⟨w, ⟨hwS, v, hvw⟩, anc_rfl (anc_right hzw)⟩, anc_trans' hyz hzw⟩, hvw⟩, hxv⟩

/-- ✱232·31. \(\vdash .(P\overline{R} Q)_{\text{os}}ʻ\alpha \subset (P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\) -/
theorem pm232_31 {S : Set β} : osFun P R Q S ⊆ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) :=
  fun _ h => ⟨pm232_301 h.1, pm232_301 (P := P˘) h.2⟩

private theorem zero_one_mono {X Y : Set α} (h : X ⊆ Y) (hY : Y ∈ zero ∪ one) :
    X ∈ zero ∪ one := by
  rcases hY with h0 | h1
  · left
    have hY0 : Y = Λ := h0
    show X = Λ
    exact eq_null_of fun x hx => not_mem_null (hY0 ▸ h hx)
  · obtain ⟨y, hy⟩ := mem_one_iff.1 h1
    by_cases hX : X.Nonempty
    · right
      obtain ⟨x, hx⟩ := hX
      refine mem_one_iff.2 ⟨x, fun z => ⟨fun hz => ?_, fun e => e ▸ hx⟩⟩
      exact ((hy z).1 (h hz)).trans ((hy x).1 (h hx)).symm
    · left
      show X = Λ
      exact eq_null_of fun x hx => hX ⟨x, hx⟩

/-- ✱232·32. \(\vdash :(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\in 0\cup 1.\supset .(P\overline{R} Q)_{\text{os}}ʻ\alpha \in 0\cup 1 \quad[*232·31]\) -/
theorem pm232_32 {S : Set β} :
    osFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∈ zero ∪ one → osFun P R Q S ∈ zero ∪ one :=
  zero_one_mono pm232_31

private theorem sc_union_sub {S : Set β} : scFun P R Q S ∪ scFun P˘ R Q S ⊆ fld P := by
  rintro x (hx | hx)
  · exact hx.2
  · rw [← fld_cnv P]
    exact hx.2

/-- ✱232·33. \[\begin{align}&\vdash :P_{*},Q_{*}\unicode{x0294f}\alpha \in \text{connex} .Rʻʻ(\alpha \cap CʻQ)\subset CʻP.\supset .\\ &(P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =(P\overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\cup (\breve{P} \overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)=CʻP\end{align}\]

The chain of three is the conjunction of its two links. -/
theorem pm232_33 {S : Set β} :
    (anc P ∈ connex ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P →
      scFun P R Q S ∪ scFun P˘ R Q S =
          scFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∪ scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R)) ∧
        scFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∪ scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R)) =
          fld P := by
  intro h
  have h22 := pm232_22 h
  have h2 : scFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∪ scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R)) =
      fld P := by
    refine Set.Subset.antisymm sc_union_sub ?_
    rw [h22]
    exact Set.union_subset_union pm232_301 pm232_301
  exact ⟨h22.symm.trans h2.symm, h2⟩

/-- ✱232·34. \[\begin{align}&\vdash :\text{Hp}*232·33.(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)=\Lambda .\supset .\\ &(P\overline{R} Q)_{\text{sc}}ʻ\alpha =(P\overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR).(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\\ &[*232·33·301.*24·482]\end{align}\] -/
theorem pm232_34 {S : Set β} :
    ((anc P ∈ connex ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧
        osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = Λ →
      scFun P R Q S = scFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∧
        scFun P˘ R Q S = scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R)) := by
  rintro ⟨h, h0⟩
  obtain ⟨e1, -⟩ := pm232_33 h
  have hdisj : ∀ x, x ∈ scFun P R Q (anc Q ʻʻ (S ∩ codom R)) →
      x ∉ scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R)) := by
    intro x h1 h2
    have : x ∈ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) := ⟨h1, h2⟩
    rw [h0] at this
    exact not_mem_null this
  refine ⟨Set.Subset.antisymm pm232_301 fun x hx => ?_,
    Set.Subset.antisymm pm232_301 fun x hx => ?_⟩
  · have : x ∈ scFun P R Q S ∪ scFun P˘ R Q S := by
      rw [e1]
      exact Or.inl hx
    rcases this with h1 | h1
    · exact h1
    · exact absurd (pm232_301 h1) (hdisj x hx)
  · have : x ∈ scFun P R Q S ∪ scFun P˘ R Q S := by
      rw [e1]
      exact Or.inr hx
    rcases this with h1 | h1
    · exact absurd hx (hdisj x (pm232_301 h1))
    · exact h1

private theorem connex_po_of_anc {P : α → α → Prop} (h : anc P ∈ connex) : po P ∈ connex := by
  rw [mem_connex] at h ⊢
  rw [fld_po]
  rw [fld_anc] at h
  intro x y hxy
  rcases h x y hxy with (h1 | h1) | h1
  · rcases anc_iff_po.1 h1 with ⟨e, -⟩ | h2
    · exact Or.inl (Or.inr e)
    · exact Or.inl (Or.inl h2)
  · exact Or.inl (Or.inr h1)
  · rcases anc_iff_po.1 h1 with ⟨e, -⟩ | h2
    · exact Or.inl (Or.inr e.symm)
    · exact Or.inr h2

/-- ✱232·341. \[\begin{align}&\vdash : P_{*} \in \text{connex} . \exists ! (P\overline{R} Q)_{\text{os}}ʻ\alpha .(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR) \in 1 . \supset .\\ &(P\overline{R} Q)_{\text{sc}}ʻ\alpha = (P\overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR) . (\breve{P} RQ)_{\text{sc}}ʻ\alpha = . (\breve{P} RQ)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\\ &[*231·192 . *232·31. *60·38]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `(P̆ R Q)_sc'α = .` (without
the bar over `R`, with a stray dot) for `(P̆ R̄ Q)_sc'α =` in the conclusion. -/
theorem pm232_341 {S : Set β} :
    (anc P ∈ connex ∧ (osFun P R Q S).Nonempty) ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∈ one →
      scFun P R Q S = scFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∧
        scFun P˘ R Q S = scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R)) := by
  rintro ⟨⟨hc, x, hx⟩, h1⟩
  have hpo : po P ∈ connex := connex_po_of_anc hc
  have hsub := pm232_31 (P := P) (R := R) (Q := Q) (S := S)
  obtain ⟨x0, hx0⟩ := mem_one_iff.1 h1
  have hxx0 : x = x0 := (hx0 x).1 (hsub hx)
  have heq : osFun P R Q S = osFun P R Q (anc Q ʻʻ (S ∩ codom R)) := by
    ext z
    refine ⟨fun hz => hsub hz, fun hz => ?_⟩
    rw [(hx0 z).1 hz, ← hxx0]
    exact hx
  exact (pm231_192 (Q := anc Q ⥏ S) (Q' := anc Q ⥏ anc Q ʻʻ (S ∩ codom R))
    ⟨⟨hpo, ⟨x, hx⟩⟩, ⟨x, hsub hx⟩⟩).1 heq

/-! Abstract forms of ✱232·351–·361: `A` is a lower section (`P R̄ Q)_sc'α`, `B` an upper one
`(P̆ R̄ Q)_sc'α`, with `A ⊂ P⃗_*'x` and `B ⊂ P⃖_*'x`. -/

private theorem absA_351 {A : Set α} {x : α}
    (hAd : ∀ u w, u ∈ A → anc P w u → w ∈ A) (hAx : A ⊆ refs (anc P) x) (hx : x ∈ A) :
    A = refs (anc P) x :=
  Set.Subset.antisymm hAx fun w hw => hAd x w hx hw

private theorem absA_352 {A : Set α} {x : α}
    (hAd : ∀ u w, u ∈ A → anc P w u → w ∈ A) (hAx : A ⊆ refs (anc P) x) (hx : x ∈ A)
    (hxP : x ∈ fld P) (hJ : po P ⪽ J) (m : α) : maxP P m A ↔ m = x := by
  rw [maxP_iff]
  constructor
  · rintro ⟨⟨hm, hmP⟩, hmax⟩
    rcases anc_iff_po.1 (hAx hm) with ⟨e, -⟩ | hp
    · exact e
    · rw [po_iff_transGen] at hp
      obtain ⟨b, hmb, hbx⟩ := Relation.TransGen.head'_iff.1 hp
      exact absurd hmb
        (hmax b (hAd x b hx (anc_iff_reflTransGen.2 ⟨fld_of_right hmb, hbx⟩)))
  · intro e
    subst e
    refine ⟨⟨hx, hxP⟩, fun y hy hmy => ?_⟩
    exact hJ _ _ (anc_po_trans (hAx hy) (po_of hmy)) rfl

private theorem absB_353 {A B : Set α} {x : α}
    (hBu : ∀ u w, u ∈ B → anc P u w → w ∈ B) (hBx : B ⊆ rels (anc P) x) (hxP : x ∈ fld P)
    (hU : A ∪ B = fld P) (hxA : x ∉ A) : B = rels (anc P) x := by
  have hxB : x ∈ B := by
    rw [← hU] at hxP
    exact hxP.resolve_left hxA
  exact Set.Subset.antisymm hBx fun w hw => hBu x w hxB hw

private theorem absB_354 {A B : Set α} {x : α}
    (hBu : ∀ u w, u ∈ B → anc P u w → w ∈ B) (hBx : B ⊆ rels (anc P) x) (hxP : x ∈ fld P)
    (hU : A ∪ B = fld P) (hxA : x ∉ A) (hJ : po P ⪽ J) (m : α) : minP P m B ↔ m = x := by
  have hxB : x ∈ B := by
    rw [← hU] at hxP
    exact hxP.resolve_left hxA
  have hJ' : po P˘ ⪽ J := fun a b h e => hJ b a (po_cnv.1 h) e.symm
  exact absA_352 (P := P˘) (fun u w hu h => hBu u w hu (anc_cnv.1 h))
    (fun w hw => anc_cnv.2 (hBx hw)) hxB (by rw [fld_cnv]; exact hxP) hJ' m

private theorem absA_355 {A B : Set α} {x : α}
    (hAx : A ⊆ refs (anc P) x) (hBx : B ⊆ rels (anc P) x) (hU : A ∪ B = fld P)
    (hxA : x ∉ A) (hJ : po P ⪽ J) : A = refs (po P) x := by
  apply Set.Subset.antisymm
  · intro u hu
    rcases anc_iff_po.1 (hAx hu) with ⟨e, -⟩ | hp
    · subst e
      exact absurd hu hxA
    · exact hp
  · intro u hu
    have huP : u ∈ fld P := po_left hu
    rw [← hU] at huP
    rcases huP with h | h
    · exact h
    · exact absurd rfl (hJ _ _ (po_anc_trans hu (hBx h)))

private theorem absA_358 {A B : Set α} {x m : α}
    (hAd : ∀ u w, u ∈ A → anc P w u → w ∈ A) (hAx : A ⊆ refs (anc P) x)
    (hBx : B ⊆ rels (anc P) x) (hxP : x ∈ fld P) (hU : A ∪ B = fld P) (hJ : po P ⪽ J)
    (hm : maxP P m A) (hmx : m ≠ x) : P1 P m x := by
  rw [maxP_iff] at hm
  obtain ⟨⟨hmA, hmP⟩, hmax⟩ := hm
  rw [P1_iff]
  refine ⟨m, x, hmx, Set.ext fun z => ⟨fun ⟨hmz, hzx⟩ => ?_, ?_⟩⟩
  · have hzP : z ∈ fld P := anc_right hmz
    rw [← hU] at hzP
    rcases hzP with hzA | hzB
    · rcases anc_iff_po.1 hmz with ⟨e, -⟩ | hp
      · exact Or.inl e.symm
      · rw [po_iff_transGen] at hp
        obtain ⟨b, hmb, hbz⟩ := Relation.TransGen.head'_iff.1 hp
        exact absurd hmb
          (hmax b (hAd z b hzA (anc_iff_reflTransGen.2 ⟨fld_of_right hmb, hbz⟩)))
    · rcases anc_iff_po.1 (hBx hzB) with ⟨e, -⟩ | hp
      · exact Or.inr e.symm
      · exact absurd rfl (hJ _ _ (po_anc_trans hp hzx))
  · rintro (rfl | rfl)
    · exact ⟨anc_rfl hmP, hAx hmA⟩
    · exact ⟨hAx hmA, anc_rfl hxP⟩

private theorem seqP_unique {P : α → α → Prop} (hc : P ∈ connex) {a b : α} {A : Set α}
    (ha : seqP P a A) (hb : seqP P b A) : a = b := by
  rw [seqP_iff] at ha hb
  rcases mem_connex.1 hc a b ⟨ha.1.2, hb.1.2⟩ with (h | h) | h
  · exact absurd h (hb.2 a ha.1.1)
  · exact h
  · exact absurd h (ha.2 b hb.1.1)

private theorem precP_unique {P : α → α → Prop} (hc : P ∈ connex) {a b : α} {A : Set α}
    (ha : precP P a A) (hb : precP P b A) : a = b := by
  rw [precP_eq_seqP_cnv] at ha hb
  exact seqP_unique (connex_cnv hc) ha hb

private theorem absA_356 {A B : Set α} {x : α} (hS : P ∈ Ser)
    (hAx : A ⊆ refs (anc P) x) (hBx : B ⊆ rels (anc P) x) (hxP : x ∈ fld P)
    (hU : A ∪ B = fld P) (hxA : x ∉ A) (s : α) : seqP P s A ↔ s = x := by
  obtain ⟨⟨hirr, htr⟩, -⟩ := Ser_parts hS
  have hJ : po P ⪽ J := fun a b h e => by
    rw [po_eq_of_transR (Ser_transR hS)] at h
    exact hirr a (e ▸ h)
  have hA := absA_355 hAx hBx hU hxA hJ
  rw [po_eq_of_transR (Ser_transR hS)] at hA
  have hseq : seqP P x A := by
    rw [seqP_iff]
    refine ⟨⟨fun y hy => ?_, hxP⟩, fun z hz hzx => ?_⟩
    · rw [hA] at hy
      exact hy.1
    · have hzA : z ∈ A := by rw [hA]; exact hzx
      exact hirr z (hz z ⟨hzA, fld_of_left hzx⟩)
  exact ⟨fun h => seqP_unique (Ser_connex hS) h hseq, fun e => e ▸ hseq⟩

private theorem absB_prec {A B : Set α} {x : α} (hS : P ∈ Ser)
    (hAx : A ⊆ refs (anc P) x) (hBx : B ⊆ rels (anc P) x) (hxP : x ∈ fld P)
    (hU : A ∪ B = fld P) (hxB : x ∉ B) (s : α) : precP P s B ↔ s = x := by
  rw [precP_eq_seqP_cnv]
  refine absA_356 (P := P˘) (A := B) (B := A) (Ser_cnv hS) (fun w hw => anc_cnv.2 (hBx hw))
    (fun w hw => anc_cnv.2 (hAx hw)) (by rw [fld_cnv]; exact hxP)
    (by rw [fld_cnv, Set.union_comm]; exact hU) hxB s

/-- The data of ✱232·35 for `α`, `x` with `(P R̄ Q)_os'Q_*''(α ∩ ᗡ'R) = ι'x`. -/
private theorem os_data {S : Set β} {x : α} (hc : anc P ∈ connex)
    (hos : osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) :
    ((scFun P R Q (anc Q ʻʻ (S ∩ codom R)) = refs (anc P) x ∧
        scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R)) = rels (anc P) x) ∧
      (scFun P R Q S ⊆ refs (anc P) x ∧ scFun P˘ R Q S ⊆ rels (anc P) x)) ∧ x ∈ fld P := by
  have hpo : po P ∈ connex := connex_po_of_anc hc
  have hos' : osBar P R (anc Q ⥏ anc Q ʻʻ (S ∩ codom R)) = ι x := hos
  have hne : (osBar P R (anc Q ⥏ anc Q ʻʻ (S ∩ codom R))).Nonempty := by
    rw [hos']
    exact ⟨x, rfl⟩
  have hpo' : po P˘ ∈ connex := by
    rw [po_cnv_eq]
    exact connex_cnv hpo
  have h1 := (pm231_191 ⟨hpo, hne⟩).1
  have h2 := (pm231_191 (P := P˘) ⟨hpo', by rw [osBar_cnv]; exact hne⟩).1
  rw [osBar_cnv, hos'] at h2
  rw [hos'] at h1
  have e1 : scFun P R Q (anc Q ʻʻ (S ∩ codom R)) = refs (anc P) x := by
    show scBar P R _ = _
    rw [h1]
    ext u
    exact ⟨fun ⟨v, hv, huv⟩ => (show v = x from hv) ▸ huv, fun hu => ⟨x, rfl, hu⟩⟩
  have e2 : scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R)) = rels (anc P) x := by
    show scBar P˘ R _ = _
    rw [h2]
    ext u
    exact ⟨fun ⟨v, hv, huv⟩ => anc_cnv.1 ((show v = x from hv) ▸ huv),
      fun hu => ⟨x, rfl, anc_cnv.2 hu⟩⟩
  have hxP : x ∈ fld P := by
    have : x ∈ scFun P R Q (anc Q ʻʻ (S ∩ codom R)) := by
      have hx : x ∈ osBar P R (anc Q ⥏ anc Q ʻʻ (S ∩ codom R)) := by rw [hos']; rfl
      exact hx.1
    exact this.2
  refine ⟨⟨⟨e1, e2⟩, ?_, ?_⟩, hxP⟩
  · rw [← e1]
    exact pm232_301
  · rw [← e2]
    exact pm232_301

/-- ✱232·35. \[\begin{align}&\vdash : P_{*} \in \text{connex} . (P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR) = {℩}ʻx . \supset .\\ &(P\overline{R} Q)_{\text{sc}}ʻ\alpha \subset \overrightarrow{P}_{*}ʻx . (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha \subset \overleftarrow{P}_{*}ʻx\\ &[*232·301.*231·191]\end{align}\]

`℩'x` (so printed) is `ι'x`, i.e. `ι x`. -/
theorem pm232_35 {S : Set β} {x : α} :
    anc P ∈ connex ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x →
      scFun P R Q S ⊆ refs (anc P) x ∧ scFun P˘ R Q S ⊆ rels (anc P) x :=
  fun ⟨hc, hos⟩ => (os_data hc hos).1.2

private theorem scFun_down {P : α → α → Prop} {S : Set β} :
    ∀ u w, u ∈ scFun P R Q S → anc P w u → w ∈ scFun P R Q S :=
  fun _ _ hu h => scBar_down hu h

private theorem scFun_up {P : α → α → Prop} {S : Set β} :
    ∀ u w, u ∈ scFun P˘ R Q S → anc P u w → w ∈ scFun P˘ R Q S :=
  fun _ _ hu h => scBar_cnv_up hu h

/-- ✱232·351. \(\vdash : \text{Hp} *232·35 . x \in (P\overline{R} Q)_{\text{sc}}ʻ\alpha . \supset . (P\overline{R} Q)_{\text{sc}}ʻ\alpha = \overrightarrow{P} _{*}ʻx\) -/
theorem pm232_351 {S : Set β} {x : α} :
    (anc P ∈ connex ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧ x ∈ scFun P R Q S →
      scFun P R Q S = refs (anc P) x :=
  fun ⟨⟨hc, hos⟩, hx⟩ => absA_351 scFun_down (os_data hc hos).1.2.1 hx

/-- ✱232·352. \[\begin{align}&\vdash : \text{Hp} *232·351 . P_{\text{po}} \,\unicode{x2abd}\, J . \supset . x = \text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha \\ &[*211·8 . *205·197 . *232·351]\end{align}\] -/
theorem pm232_352 {S : Set β} {x : α} :
    ((anc P ∈ connex ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧ x ∈ scFun P R Q S) ∧
        po P ⪽ J →
      Desc (maxP P) (scFun P R Q S) (fun m => x = m) := by
  rintro ⟨⟨⟨hc, hos⟩, hx⟩, hJ⟩
  obtain ⟨⟨-, hAx, -⟩, hxP⟩ := os_data hc hos
  exact (TheIs_iff_of_unique (absA_352 scFun_down hAx hx hxP hJ)).2 rfl

/-- ✱232·353. \[\begin{align}\vdash : \text{Hp} *232·35. (P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha = CʻP . &x{\sim}\in (P\overline{R} Q)_{\text{sc}}ʻ\alpha . \supset .\\ &(\breve{P}\overline{R} Q)_{\text{sc}}ʻ\alpha = \overleftarrow{P}_{*}ʻx\end{align}\] -/
theorem pm232_353 {S : Set β} {x : α} :
    ((anc P ∈ connex ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧
        scFun P R Q S ∪ scFun P˘ R Q S = fld P) ∧ x ∉ scFun P R Q S →
      scFun P˘ R Q S = rels (anc P) x := by
  rintro ⟨⟨⟨hc, hos⟩, hU⟩, hxA⟩
  obtain ⟨⟨-, -, hBx⟩, hxP⟩ := os_data hc hos
  exact absB_353 scFun_up hBx hxP hU hxA

/-- ✱232·354. \(\vdash : \text{Hp} *232·353 . P_{\text{po}} \,\unicode{x2abd}\, J. \supset . x = \text{min}_{P}ʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha \quad\left[*232·352 \frac{\breve{P}}{P}\right]\) -/
theorem pm232_354 {S : Set β} {x : α} :
    (((anc P ∈ connex ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧
          scFun P R Q S ∪ scFun P˘ R Q S = fld P) ∧ x ∉ scFun P R Q S) ∧ po P ⪽ J →
      Desc (minP P) (scFun P˘ R Q S) (fun m => x = m) := by
  rintro ⟨⟨⟨⟨hc, hos⟩, hU⟩, hxA⟩, hJ⟩
  obtain ⟨⟨-, -, hBx⟩, hxP⟩ := os_data hc hos
  exact (TheIs_iff_of_unique (absB_354 scFun_up hBx hxP hU hxA hJ)).2 rfl

/-- ✱232·355. \(\vdash : \text{Hp} *232·353. \supset . (P\overline{R} Q)_{\text{sc}}ʻ\alpha = \overrightarrow{P}_{\text{po}}ʻx\)

**Status.** proved (corrected): false as printed. PM's demonstration needs
`P⃗_po'x ⊂ C'P − P⃖_*'x`, which fails when `x P x`. Counterexample: values `v, x` with
`P = v ↓ x ∪̇ x ↓ x`; arguments `y₀, w, y₁, a` with `Q` relating `y₀` and `w` both ways and `y₁`
to `a`; `R` gives the value `v` at `y₀` and `x` at `w, y₁, a`; `α = ι'y₀ ∪ ι'a`. Then
`(P R̄ Q)_os'Q_*''(α ∩ ᗡ'R) = ι'x`, `(P R̄ Q)_sc'α = ι'v`, `(P̆ R̄ Q)_sc'α = ι'x`, so the
hypothesis holds, but `P⃗_po'x = ι'v ∪ ι'x`. The hypothesis `P_po ⊂̇ J` (that of ✱232·352·354,
which ✱232·356 supplies by `P ∈ Ser`) is added. -/
theorem pm232_355 {S : Set β} {x : α} :
    (((anc P ∈ connex ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧
          scFun P R Q S ∪ scFun P˘ R Q S = fld P) ∧ x ∉ scFun P R Q S) ∧ po P ⪽ J →
      scFun P R Q S = refs (po P) x := by
  rintro ⟨⟨⟨⟨hc, hos⟩, hU⟩, hxA⟩, hJ⟩
  obtain ⟨⟨-, hAx, hBx⟩, -⟩ := os_data hc hos
  exact absA_355 hAx hBx hU hxA hJ

/-- ✱232·356. \[\begin{align}&\vdash \colon\ldotp P \in \text{Ser}. (P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR) = \iota ʻx.\\ &(P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup (\breve{P}\overline{R} Q)_{\text{sc}}ʻ\alpha =CʻP . \supset : x{\sim}\in (P\overline{R} Q)_{\text{sc}}ʻ\alpha . \supset . x = \text{seq}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha \\ &[*206·172 . *231·13 . *232·355]\end{align}\] -/
theorem pm232_356 {S : Set β} {x : α} :
    (P ∈ Ser ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧
        scFun P R Q S ∪ scFun P˘ R Q S = fld P →
      (x ∉ scFun P R Q S → Desc (seqP P) (scFun P R Q S) (fun s => x = s)) := by
  rintro ⟨⟨hS, hos⟩, hU⟩ hxA
  obtain ⟨⟨-, hAx, hBx⟩, hxP⟩ := os_data (connex_anc (Ser_connex hS)) hos
  exact (TheIs_iff_of_unique (absA_356 hS hAx hBx hxP hU hxA)).2 rfl

/-- ✱232·357. \(\vdash : \text{Hp}*232·35 . P_{\text{po}} \,\unicode{x2abd}\, J. {\sim}\text{E}!\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha . \supset .x= \text{min}_{P}ʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha\)

**Status.** proved (corrected): false as printed. PM's demonstration (✱232·352 Transp, ✱232·354)
uses the hypothesis `(P R̄ Q)_sc'α ∪ (P̆ R̄ Q)_sc'α = C'P` of ✱232·354, which ✱232·357 omits.
Counterexample: values `p, x, w` with `P = p ↓ x`; arguments `y, a` with `Q` relating them both
ways; `R` gives the value `x` at `y` and `w` (not in `C'P`) at `a`; `α = ι'a`. Then
`(P R̄ Q)_os'Q_*''(α ∩ ᗡ'R) = ι'x`, `P_* ∈ connex`, `P_po ⊂̇ J`, and
`(P R̄ Q)_sc'α = (P̆ R̄ Q)_sc'α = Λ`, so `max_P'(P R̄ Q)_sc'α` does not exist but neither does
`min_P'(P̆ R̄ Q)_sc'α`. The omitted hypothesis is added. -/
theorem pm232_357 {S : Set β} {x : α} :
    (((anc P ∈ connex ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧ po P ⪽ J) ∧
          ¬EDesc (maxP P) (scFun P R Q S)) ∧
        scFun P R Q S ∪ scFun P˘ R Q S = fld P →
      Desc (minP P) (scFun P˘ R Q S) (fun m => x = m) := by
  rintro ⟨⟨⟨⟨hc, hos⟩, hJ⟩, hnE⟩, hU⟩
  obtain ⟨⟨-, hAx, hBx⟩, hxP⟩ := os_data hc hos
  have hxA : x ∉ scFun P R Q S := fun hx =>
    hnE ⟨x, absA_352 scFun_down hAx hx hxP hJ⟩
  exact (TheIs_iff_of_unique (absB_354 scFun_up hBx hxP hU hxA hJ)).2 rfl

/-- ✱232·358. \[\begin{align}&\vdash :\text{Hp}*232·35.P_{\text{po}}\,\unicode{x2abd}\, J.(P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =CʻP.\\ &\text{E}!\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha .\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha \neq x.\supset .\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha P_{1}x\end{align}\]

`max_P'… ≠ x` is `Desc (maxP P) … (fun m => m ≠ x)`. -/
theorem pm232_358 {S : Set β} {x : α} :
    ((((anc P ∈ connex ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧ po P ⪽ J) ∧
          scFun P R Q S ∪ scFun P˘ R Q S = fld P) ∧ EDesc (maxP P) (scFun P R Q S)) ∧
        Desc (maxP P) (scFun P R Q S) (fun m => m ≠ x) →
      Desc (maxP P) (scFun P R Q S) (fun m => P1 P m x) := by
  rintro ⟨⟨⟨⟨⟨hc, hos⟩, hJ⟩, hU⟩, m, hm⟩, hne⟩
  obtain ⟨⟨-, hAx, hBx⟩, hxP⟩ := os_data hc hos
  have hmx : m ≠ x := (TheIs_iff_of_unique hm).1 hne
  exact (TheIs_iff_of_unique hm).2
    (absA_358 scFun_down hAx hBx hxP hU hJ ((hm m).2 rfl) hmx)

private theorem Ser_J {P : α → α → Prop} (hS : P ∈ Ser) : po P ⪽ J := fun a b h e => by
  rw [po_eq_of_transR (Ser_transR hS)] at h
  exact (Ser_parts hS).1.1 a (e ▸ h)

/-- ✱232·36. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)=\iota ʻx.\\ &(P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =CʻP.\supset :\\ &x\in (P\overline{R} Q)_{os}ʻ\alpha .\supset .x=\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha =\text{min}_{P}ʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha :\\ &x\in (P\overline{R} Q)_{\text{sc}}ʻ\alpha -(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha .\supset .x=\text{max}_{P}ʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =\text{prec}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha :\\ &x\in (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha -(P\overline{R} Q)_{\text{sc}}ʻ\alpha .\supset .x=\text{seq}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha =\text{min}_{P}ʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha \\ &[*232·352·354·356]\end{align}\]

**Status.** proved (corrected): the second clause is false as printed: it reads
`x = max_P'(P̆ R̄ Q)_sc'α = prec_P'(P R̄ Q)_sc'α`, but a maximum of `(P̆ R̄ Q)_sc'α` would be a
member of it, while the clause supposes `x ∼∈ (P̆ R̄ Q)_sc'α` (e.g. values `1/n` at the
arguments of `α` and `0` at the others, in the series of rationals). The classes are
interchanged; the clause proved is `x = max_P'(P R̄ Q)_sc'α = prec_P'(P̆ R̄ Q)_sc'α` (✱232·352
and the converse of ✱232·356, as the first and third clauses). -/
theorem pm232_36 {S : Set β} {x : α} :
    (P ∈ Ser ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧
        scFun P R Q S ∪ scFun P˘ R Q S = fld P →
      ((x ∈ osFun P R Q S →
            Desc (maxP P) (scFun P R Q S) (fun m => x = m) ∧
              Desc (maxP P) (scFun P R Q S)
                (fun m => Desc (minP P) (scFun P˘ R Q S) (fun n => m = n))) ∧
          (x ∈ scFun P R Q S \ scFun P˘ R Q S →
            Desc (maxP P) (scFun P R Q S) (fun m => x = m) ∧
              Desc (maxP P) (scFun P R Q S)
                (fun m => Desc (precP P) (scFun P˘ R Q S) (fun n => m = n)))) ∧
        (x ∈ scFun P˘ R Q S \ scFun P R Q S →
          Desc (seqP P) (scFun P R Q S) (fun s => x = s) ∧
            Desc (seqP P) (scFun P R Q S)
              (fun s => Desc (minP P) (scFun P˘ R Q S) (fun n => s = n))) := by
  rintro ⟨⟨hS, hos⟩, hU⟩
  have hc := connex_anc (Ser_connex hS)
  have hJ := Ser_J hS
  obtain ⟨⟨-, hAx, hBx⟩, hxP⟩ := os_data hc hos
  -- `x` is the maximum of `A` when `x ∈ A`, and the minimum of `B` when `x ∈ B`
  have hmaxA : x ∈ scFun P R Q S → ∀ m, maxP P m (scFun P R Q S) ↔ m = x :=
    fun hx => absA_352 scFun_down hAx hx hxP hJ
  have hminB : x ∈ scFun P˘ R Q S → ∀ m, minP P m (scFun P˘ R Q S) ↔ m = x := by
    intro hx
    have hJ' : po P˘ ⪽ J := fun a b h e => hJ b a (po_cnv.1 h) e.symm
    exact absA_352 (P := P˘) (fun u w hu h => scFun_up u w hu (anc_cnv.1 h))
      (fun w hw => anc_cnv.2 (hBx hw)) hx (by rw [fld_cnv]; exact hxP) hJ'
  refine ⟨⟨fun hx => ?_, fun ⟨hxA, hxB⟩ => ?_⟩, fun ⟨hxB, hxA⟩ => ?_⟩
  · have h1 := hmaxA hx.1
    exact ⟨(TheIs_iff_of_unique h1).2 rfl,
      (TheIs_iff_of_unique h1).2 ((TheIs_iff_of_unique (hminB hx.2)).2 rfl)⟩
  · have h1 := hmaxA hxA
    exact ⟨(TheIs_iff_of_unique h1).2 rfl, (TheIs_iff_of_unique h1).2
      ((TheIs_iff_of_unique (absB_prec hS hAx hBx hxP hU hxB)).2 rfl)⟩
  · have h1 := absA_356 hS hAx hBx hxP hU hxA
    exact ⟨(TheIs_iff_of_unique h1).2 rfl,
      (TheIs_iff_of_unique h1).2 ((TheIs_iff_of_unique (hminB hxB)).2 rfl)⟩

/-- The value of `limax_P` of the lower section, for `x ∼∈ ᗡ'P_1` (abstract ✱232·361). -/
private theorem absA_361 {A B : Set α} {x : α} (hS : P ∈ Ser)
    (hAd : ∀ u w, u ∈ A → anc P w u → w ∈ A)
    (hAx : A ⊆ refs (anc P) x) (hBx : B ⊆ rels (anc P) x) (hxP : x ∈ fld P)
    (hU : A ∪ B = fld P) (hx1 : x ∉ codom (P1 P)) (l : α) : limaxP P l A ↔ l = x := by
  have hJ := Ser_J hS
  by_cases hxA : x ∈ A
  · exact limax_of_max (absA_352 hAd hAx hxA hxP hJ) l
  · have hseq := absA_356 hS hAx hBx hxP hU hxA
    have hnomax : ¬∃ m, maxP P m A := by
      rintro ⟨m, hm⟩
      by_cases hmx : m = x
      · exact hxA (hmx ▸ ((maxP_iff.1 hm).1.1))
      · exact hx1 ⟨m, absA_358 hAd hAx hBx hxP hU hJ hm hmx⟩
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact absurd ⟨l, h⟩ hnomax
      · exact (hseq l).1 h
    · intro e
      exact Or.inr ⟨(hseq l).2 e, hnomax⟩

private theorem P1_cnv {P : α → α → Prop} {a b : α} : P1 P˘ a b ↔ P1 P b a := by
  rw [P1_iff, P1_iff]
  have : itvCC P˘ a b = itvCC P b a := by
    ext z
    exact ⟨fun ⟨h1, h2⟩ => ⟨anc_cnv.1 h2, anc_cnv.1 h1⟩,
      fun ⟨h1, h2⟩ => ⟨anc_cnv.2 h2, anc_cnv.2 h1⟩⟩
  rw [this]

/-- The value of `limin_P` of the upper section, for `x ∼∈ D'P_1`. -/
private theorem absB_361 {A B : Set α} {x : α} (hS : P ∈ Ser)
    (hBu : ∀ u w, u ∈ B → anc P u w → w ∈ B)
    (hAx : A ⊆ refs (anc P) x) (hBx : B ⊆ rels (anc P) x) (hxP : x ∈ fld P)
    (hU : A ∪ B = fld P) (hx1 : x ∉ dom (P1 P)) (l : α) : liminP P l B ↔ l = x := by
  rw [liminP_eq_limaxP_cnv]
  refine absA_361 (P := P˘) (A := B) (B := A) (Ser_cnv hS)
    (fun u w hu h => hBu u w hu (anc_cnv.1 h)) (fun w hw => anc_cnv.2 (hBx hw))
    (fun w hw => anc_cnv.2 (hAx hw)) (by rw [fld_cnv]; exact hxP)
    (by rw [fld_cnv, Set.union_comm]; exact hU) (fun ⟨y, hy⟩ => hx1 ⟨y, P1_cnv.1 hy⟩) l

/-- ✱232·361. \(\vdash :\text{Hp}*232·36.x{\sim}\in \text{ᗡ}ʻP_{1}.\supset .x=\text{limax}_Pʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha\) -/
theorem pm232_361 {S : Set β} {x : α} :
    ((P ∈ Ser ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧
        scFun P R Q S ∪ scFun P˘ R Q S = fld P) ∧ x ∉ codom (P1 P) →
      Desc (limaxP P) (scFun P R Q S) (fun l => x = l) := by
  rintro ⟨⟨⟨hS, hos⟩, hU⟩, hx1⟩
  obtain ⟨⟨-, hAx, hBx⟩, hxP⟩ := os_data (connex_anc (Ser_connex hS)) hos
  exact (TheIs_iff_of_unique (absA_361 hS scFun_down hAx hBx hxP hU hx1)).2 rfl

/-- ✱232·37. \[\begin{align}&\vdash :P\in \text{Ser}.(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\in 1-\text{Cl}ʻ\text{ᗡ}ʻP_{1}.\\ &(P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =CʻP.\supset .\\ &\text{limax}_Pʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha =\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\\ &= \breve{\iota} ʻ(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\\ &[*232·361.*231·193]\end{align}\]

`1 − Cl'ᗡ'P_1` is `one \ cl (codom (P1 P))`; `ῐ'…` is `Desc iota˘ … ψ`. The chain of three is the
conjunction of its two links. -/
theorem pm232_37 {S : Set β} :
    (P ∈ Ser ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∈ one \ cl (codom (P1 P))) ∧
        scFun P R Q S ∪ scFun P˘ R Q S = fld P →
      Desc (limaxP P) (scFun P R Q S)
          (fun a => Desc (maxP P) (scFun P R Q (anc Q ʻʻ (S ∩ codom R))) (fun b => a = b)) ∧
        Desc (maxP P) (scFun P R Q (anc Q ʻʻ (S ∩ codom R)))
          (fun b => Desc iota˘ (osFun P R Q (anc Q ʻʻ (S ∩ codom R))) (fun c => b = c)) := by
  rintro ⟨⟨hS, h1, hcl⟩, hU⟩
  obtain ⟨x, hx⟩ := mem_one_iff.1 h1
  have hos : osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x := Set.ext hx
  have hx1 : x ∉ codom (P1 P) := fun h => hcl (by rw [hos]; rintro z rfl; exact h)
  obtain ⟨⟨⟨e1, -⟩, hAx, hBx⟩, hxP⟩ := os_data (connex_anc (Ser_connex hS)) hos
  have hl := absA_361 hS scFun_down hAx hBx hxP hU hx1
  have hm : ∀ m, maxP P m (scFun P R Q (anc Q ʻʻ (S ∩ codom R))) ↔ m = x := by
    rw [e1]
    exact absA_352 (fun u w hu h => anc_trans' h hu) (fun _ h => h) (anc_rfl hxP) hxP
      (Ser_J hS)
  refine ⟨(TheIs_iff_of_unique hl).2 ((TheIs_iff_of_unique hm).2 rfl),
    (TheIs_iff_of_unique hm).2 ?_⟩
  rw [desc_iota_cnv]
  exact (TheIs_iff_of_unique hx).2 rfl

/-- `limax_P` and `limin_P` of the limiting sections, when `(P R̄ Q)_os'Q_*''(α ∩ ᗡ'R) = ι'x`,
`x ∼∈ C'P_1`, for both `α` and `Q_*''(α ∩ ᗡ'R)`. -/
private theorem os_one_values {S : Set β} {x : α} (hS : P ∈ Ser)
    (hos : osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) (hx1 : x ∉ fld (P1 P))
    (hU : scFun P R Q S ∪ scFun P˘ R Q S = fld P) :
    ((∀ l, limaxP P l (scFun P R Q S) ↔ l = x) ∧
        ∀ l, limaxP P l (scFun P R Q (anc Q ʻʻ (S ∩ codom R))) ↔ l = x) ∧
      (∀ l, liminP P l (scFun P˘ R Q S) ↔ l = x) ∧
        ∀ l, liminP P l (scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R))) ↔ l = x := by
  obtain ⟨⟨⟨e1, e2⟩, hAx, hBx⟩, hxP⟩ := os_data (connex_anc (Ser_connex hS)) hos
  have hx1' : x ∉ codom (P1 P) := fun ⟨y, h⟩ => hx1 ⟨y, Or.inr h⟩
  have hx1'' : x ∉ dom (P1 P) := fun ⟨y, h⟩ => hx1 ⟨y, Or.inl h⟩
  have hU' : scFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∪ scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R)) =
      fld P := by
    refine Set.Subset.antisymm sc_union_sub ?_
    rw [← hU]
    exact Set.union_subset_union pm232_301 pm232_301
  refine ⟨⟨absA_361 hS scFun_down hAx hBx hxP hU hx1', ?_⟩,
    absB_361 hS scFun_up hAx hBx hxP hU hx1'', ?_⟩
  · exact absA_361 hS scFun_down e1.subset e2.subset hxP hU' hx1'
  · exact absB_361 hS scFun_up e1.subset e2.subset hxP hU' hx1''

/-- ✱232·38. \[\begin{align}&\vdash :P\in \text{Ser}.Q_{*}\unicode{x0294f}\alpha \in \text{connex} .Rʻʻ(\alpha \cap CʻQ)\subset CʻP.\\ &(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\in 0\cup (1-\text{Cl}ʻCʻP_{1}).\supset .\\ &\overrightarrow{\text{limax}} _{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha =\overrightarrow{\text{limax}} _{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR).\\ &\overrightarrow{\text{limin}} _{P}ʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =\overrightarrow{\text{limin}} _{P}ʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\\ &[*232·33·34·37]\end{align}\]

`0 ∪ (1 − Cl'C'P_1)` is `zero ∪ (one \ cl (fld (P1 P)))`; `limax⃗_P'…` is `refs (limaxP P) …`. -/
theorem pm232_38 {S : Set β} :
    ((P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧
        osFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∈ zero ∪ (one \ cl (fld (P1 P))) →
      refs (limaxP P) (scFun P R Q S) =
          refs (limaxP P) (scFun P R Q (anc Q ʻʻ (S ∩ codom R))) ∧
        refs (liminP P) (scFun P˘ R Q S) =
          refs (liminP P) (scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R))) := by
  rintro ⟨⟨⟨hS, hcQ⟩, hR⟩, h0 | ⟨h1, hcl⟩⟩
  · have hc := connex_anc (Ser_connex hS)
    obtain ⟨e1, e2⟩ := pm232_34 ⟨⟨⟨hc, hcQ⟩, hR⟩, (h0 : _ = Λ)⟩
    rw [e1, e2]
    exact ⟨rfl, rfl⟩
  · obtain ⟨x, hx⟩ := mem_one_iff.1 h1
    have hos : osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x := Set.ext hx
    have hx1 : x ∉ fld (P1 P) := fun h => hcl (by rw [hos]; rintro z rfl; exact h)
    have hU := (pm232_22 ⟨⟨connex_anc (Ser_connex hS), hcQ⟩, hR⟩).symm
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := os_one_values hS hos hx1 hU
    exact ⟨Set.ext fun l => (h1 l).trans (h2 l).symm, Set.ext fun l => (h3 l).trans (h4 l).symm⟩

private theorem P1_empty_of_dense {P : α → α → Prop} (hS : P ∈ Ser) (hd : rsq P = P) (a b : α) :
    ¬P1 P a b := by
  rw [P1_iff_of_transR (Ser_transR hS) (Ser_rlJ hS)]
  rintro ⟨hab, hn⟩
  have : rsq P a b := by rw [hd]; exact hab
  exact hn this

private theorem limax_exists {P : α → α → Prop} (hS : P ∈ Ser) (hD : P ∈ Ded) (A : Set α) :
    ∃ l, ∀ b, limaxP P b A ↔ b = l := by
  rcases mem_Ded.1 hD A with ⟨m, hm⟩ | ⟨s, hs⟩
  · exact ⟨m, limax_of_max fun b => ⟨fun hb => maxP_unique (Ser_connex hS) hb hm,
      fun e => e ▸ hm⟩⟩
  · by_cases hmax : ∃ m, maxP P m A
    · obtain ⟨m, hm⟩ := hmax
      exact ⟨m, limax_of_max fun b => ⟨fun hb => maxP_unique (Ser_connex hS) hb hm,
        fun e => e ▸ hm⟩⟩
    · refine ⟨s, fun b => ⟨?_, fun e => Or.inr ⟨e ▸ hs, hmax⟩⟩⟩
      rintro (hb | ⟨hb, -⟩)
      · exact absurd ⟨b, hb⟩ hmax
      · exact seqP_unique (Ser_connex hS) hb hs

private theorem dense_values
    (h : ((P ∈ Ser ∩ Ded ∧ rsq P = P) ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P) (S : Set β)
    (h01 : osFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∈ zero ∪ one) :
    ∃ l, ((∀ b, limaxP P b (scFun P R Q S) ↔ b = l) ∧
      ∀ b, limaxP P b (scFun P R Q (anc Q ʻʻ (S ∩ codom R))) ↔ b = l) ∧
      (∀ b, liminP P b (scFun P˘ R Q S) ↔ b = l) ∧
        ∀ b, liminP P b (scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R))) ↔ b = l := by
  obtain ⟨⟨⟨⟨hS, hD⟩, hd⟩, hcQ⟩, hR⟩ := h
  have hc := connex_anc (Ser_connex hS)
  have hcQS : anc Q ⥏ S ∈ connex := by
    rw [mem_connex] at hcQ ⊢
    rw [fld_anc] at hcQ
    intro y z ⟨hy, hz⟩
    obtain ⟨hyS, hyQ⟩ := fld_ancFres.1 hy
    obtain ⟨hzS, hzQ⟩ := fld_ancFres.1 hz
    rcases hcQ y z ⟨hyQ, hzQ⟩ with (h | h) | h
    · exact Or.inl (Or.inl ⟨⟨hyS, h⟩, hzS⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨⟨hzS, h⟩, hyS⟩
  have hRS : R ʻʻ (S ∩ fld Q) ⊆ fld P := fun v ⟨y, hy, hvy⟩ => hR ⟨y, hy.2, hvy⟩
  rcases h01 with h0 | h1
  · have h0' : osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = Λ := h0
    obtain ⟨e1, e2⟩ := pm232_34 ⟨⟨⟨hc, hcQS⟩, hRS⟩, h0'⟩
    rw [e1, e2]
    obtain ⟨l, hl⟩ := limax_exists hS hD (scFun P R Q (anc Q ʻʻ (S ∩ codom R)))
    have hU := (pm232_33 (S := S) ⟨⟨hc, hcQS⟩, hRS⟩).2
    have hS' : ∀ u, u ∈ scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R)) ↔
        u ∈ fld P ∧ u ∉ scFun P R Q (anc Q ʻʻ (S ∩ codom R)) := by
      intro u
      constructor
      · intro hu
        refine ⟨by rw [← hU]; exact Or.inr hu, fun hu' => ?_⟩
        have : u ∈ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) := ⟨hu', hu⟩
        rw [h0'] at this
        exact not_mem_null this
      · rintro ⟨huP, huS⟩
        rw [← hU] at huP
        exact huP.resolve_left huS
    rcases cut_limax hS pm231_13 hS' ((hl l).2 rfl) with h3 | ⟨n, -, h3⟩
    · exact ⟨l, ⟨hl, hl⟩, h3, h3⟩
    · exact absurd h3 (P1_empty_of_dense hS hd l n)
  · obtain ⟨x, hx⟩ := mem_one_iff.1 h1
    have hos : osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x := Set.ext hx
    have hx1 : x ∉ fld (P1 P) := by
      rintro ⟨y, h | h⟩
      · exact P1_empty_of_dense hS hd x y h
      · exact P1_empty_of_dense hS hd y x h
    have hU := (pm232_22 ⟨⟨hc, hcQS⟩, hRS⟩).symm
    exact ⟨x, os_one_values hS hos hx1 hU⟩

/-- ✱232·39. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}\cap &\text{Ded}.P^{2}=P.Q_{*}\in \text{connex} .RʻʻCʻQ\subset CʻP.\supset :\\ &(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\in 0\cup 1.\supset _{\alpha }.\\ &\text{limax}_Pʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha =\text{limax}_Pʻ(P\overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\\ &=\text{limin}_Pʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =\text{limin}_Pʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\end{align}\]

`P ∈ Ser ∩ Ded` and `P² = P` (`rsq P = P`); `⊃_α` is `∀ S`. The chain of four is the conjunction
of its three links. -/
theorem pm232_39 :
    ((P ∈ Ser ∩ Ded ∧ rsq P = P) ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      ∀ S : Set β, osFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∈ zero ∪ one →
        (Desc (limaxP P) (scFun P R Q S)
              (fun a => Desc (limaxP P) (scFun P R Q (anc Q ʻʻ (S ∩ codom R)))
                (fun b => a = b)) ∧
            Desc (limaxP P) (scFun P R Q (anc Q ʻʻ (S ∩ codom R)))
              (fun a => Desc (liminP P) (scFun P˘ R Q S) (fun b => a = b))) ∧
          Desc (liminP P) (scFun P˘ R Q S)
            (fun a => Desc (liminP P) (scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R)))
              (fun b => a = b)) := by
  intro h S h01
  obtain ⟨l, ⟨h1, h2⟩, h3, h4⟩ := dense_values h S h01
  exact ⟨⟨(TheIs_iff_of_unique h1).2 ((TheIs_iff_of_unique h2).2 rfl),
    (TheIs_iff_of_unique h2).2 ((TheIs_iff_of_unique h3).2 rfl)⟩,
    (TheIs_iff_of_unique h3).2 ((TheIs_iff_of_unique h4).2 rfl)⟩

/-- ✱232·5. \[\begin{align}&\vdash .(P\overline{R} Q)_{\text{sc}}ʻ\overrightarrow{Q}ʻx=CʻP\cap \hat{y} \{z\in \overrightarrow{Q}ʻx\cap \text{ᗡ}ʻR.\supset _{z}.y\in P_{*}ʻʻRʻʻ(\overrightarrow{Q}ʻx\cap \overleftarrow{Q}_{*}ʻz)\}\\ &[*232·11]\end{align}\] -/
theorem pm232_5 {x : β} :
    scFun P R Q (refs Q x) =
      fld P ∩ {y | ∀ z, z ∈ refs Q x ∩ codom R →
        y ∈ anc P ʻʻ (R ʻʻ (refs Q x ∩ rels (anc Q) z))} := by
  ext y
  rw [mem_scFun', Set.mem_inter_iff, and_comm]
  refine and_congr Iff.rfl ⟨fun h z hz => h z ⟨⟨hz.1, fld_of_left hz.1⟩, hz.2⟩,
    fun h z hz => h z ⟨hz.1.1, hz.2⟩⟩

/-- ✱232·51. \[\begin{align}\vdash :Q\in \text{trans}\cap &\text{connex} .\text{E}!\text{max}_{Q}ʻ(\overrightarrow{Q}ʻx\cap \text{ᗡ}ʻR).\supset .\\ &(P\overline{R} Q)_{\text{sc}}ʻ\overrightarrow{Q}ʻx=P_{*}ʻʻ\overrightarrow{R}ʻ\text{max}_{Q}ʻ(\overrightarrow{Q}ʻx\cap \text{ᗡ}ʻR) \quad[*232·24]\end{align}\] -/
theorem pm232_51 {x : β} :
    Q ∈ transR ∩ connex ∧ EDesc (maxP Q) (refs Q x ∩ codom R) →
      Desc (maxP Q) (refs Q x ∩ codom R)
        (fun m => scFun P R Q (refs Q x) = anc P ʻʻ refs R m) :=
  pm232_24

/-- ✱232·511. \[\begin{align}\vdash :Q\in \text{trans}\cap &\text{connex} .\text{E}!Rʻ\text{max}_{Q}ʻ(\overrightarrow{Q}ʻx\cap \text{ᗡ}ʻR).\supset .\\ &(P\overline{R} Q)_{\text{sc}}ʻ\overrightarrow{Q}ʻx=\overrightarrow{P}_{*}ʻRʻ\text{max}_{Q}ʻ(\overrightarrow{Q}ʻx\cap \text{ᗡ}ʻR) \quad[*232·51]\end{align}\]

`E!R'max_Q'(Q⃗'x ∩ ᗡ'R)` is `Desc (maxP Q) (refs Q x ∩ codom R) (fun m => EDesc R m)`. -/
theorem pm232_511 {x : β} :
    Q ∈ transR ∩ connex ∧ Desc (maxP Q) (refs Q x ∩ codom R) (fun m => EDesc R m) →
      Desc2 R (maxP Q) (refs Q x ∩ codom R)
        (fun v => scFun P R Q (refs Q x) = refs (anc P) v) := by
  rintro ⟨hQ, m, hm, v, hv⟩
  rw [desc2_iff]
  refine (TheIs_iff_of_unique hm).2 ((TheIs_iff_of_unique hv).2 ?_)
  have h4 := (TheIs_iff_of_unique hm).1 (pm232_51 (P := P) ⟨hQ, ⟨m, hm⟩⟩)
  rw [h4]
  ext u
  constructor
  · rintro ⟨w, hw, huw⟩
    rw [(hv w).1 hw] at huw
    exact huw
  · intro hu
    exact ⟨v, (hv v).2 rfl, hu⟩

/-- ✱232·52. \[\begin{align}\vdash :Q\in \text{connex} .yQx.\overrightarrow{Q}ʻx\cap &(\overleftarrow{Q}ʻy\cup {℩}ʻy)\cap \text{ᗡ}ʻR=\Lambda .\supset .\\ &(P\overline{R} Q)_{\text{sc}}ʻ\overrightarrow{Q}ʻx=(P\overline{R} Q)_{\text{sc}}ʻ\overrightarrow{Q}ʻy \quad[*232·13]\end{align}\]

**Status.** proved (corrected): false as printed, for `Q` connected but not transitive (the
reference ✱232·13 needs `Q⃗'x ∩ ᗡ'R = Q⃗'y ∩ ᗡ'R`, and `z Q y . y Q x` gives `z Q x` only for
transitive `Q`). Counterexample (`pm232_52_printed_false`): arguments `true, false` with
`Q = J` (connected, not transitive), `x = true`, `y = false`; values `false, true` with
`P = false ↓ true`, `R = false ↓ true`; then `(P R̄ Q)_sc'Q⃗'x = C'P` but
`(P R̄ Q)_sc'Q⃗'y = P_*''R⃗'x = ι'false`. The hypothesis `Q ∈ trans` (as in ✱232·51·511) is
added. `℩'y` (so printed) is `ι'y`. -/
theorem pm232_52 {x y : β} :
    (Q ∈ transR ∩ connex ∧ Q y x) ∧ refs Q x ∩ (rels Q y ∪ ι y) ∩ codom R = Λ →
      scFun P R Q (refs Q x) = scFun P R Q (refs Q y) := by
  rintro ⟨⟨⟨htr, hcon⟩, hyx⟩, h⟩
  rw [mem_connex] at hcon
  have hn : ∀ z, z ∈ refs Q x ∩ (rels Q y ∪ ι y) ∩ codom R → False := fun z hz => by
    rw [h] at hz
    exact not_mem_null hz
  apply pm232_13
  ext z
  constructor
  · rintro ⟨⟨hzx, hzQ⟩, hzR⟩
    refine ⟨⟨?_, hzQ⟩, hzR⟩
    rcases hcon z y ⟨hzQ, fld_of_left hyx⟩ with (h1 | e) | h1
    · exact h1
    · exact (hn z ⟨⟨hzx, Or.inr e⟩, hzR⟩).elim
    · exact (hn z ⟨⟨hzx, Or.inl h1⟩, hzR⟩).elim
  · rintro ⟨⟨hzy, hzQ⟩, hzR⟩
    exact ⟨⟨mem_transR.1 htr z y x ⟨hzy, hyx⟩, hzQ⟩, hzR⟩

private def cxQ : Bool → Bool → Prop := fun a b => a ≠ b

private def cxP : Bool → Bool → Prop := fun a b => a = false ∧ b = true

/-- The printed form of ✱232·52 (without `Q ∈ trans`) is false. -/
theorem pm232_52_printed_false :
    ¬∀ (P R Q : Bool → Bool → Prop) (x y : Bool),
      (Q ∈ connex ∧ Q y x) ∧ refs Q x ∩ (rels Q y ∪ ι y) ∩ codom R = Λ →
        scFun P R Q (refs Q x) = scFun P R Q (refs Q y) := by
  intro h
  have hc : cxQ ∈ connex := by
    rw [mem_connex]
    intro a b _
    cases a <;> cases b <;> simp [cxQ]
  have hnull : ∀ S : Set Bool, S ⊆ refs cxQ true → S ∩ codom cxP = Λ := by
    intro S hS
    refine eq_null_of fun z ⟨hz, w, hw⟩ => ?_
    have h1 : cxQ z true := hS hz
    exact h1 hw.2
  have hyp : refs cxQ true ∩ (rels cxQ false ∪ ι false) ∩ codom cxP = Λ :=
    hnull _ fun z hz => hz.1
  have e := h cxP cxP cxQ true false ⟨⟨hc, by simp [cxQ]⟩, hyp⟩
  have h15 := pm232_15 (P := cxP) (R := cxP) (Q := cxQ) (S := refs cxQ true)
    (hnull (refs cxQ true ∩ fld cxQ) fun z hz => hz.1)
  have e1 : scFun cxP cxP cxQ (refs cxQ true) = fld cxP := h15.1.1.trans (h15.1.2.trans h15.2)
  have e2 : refs cxQ false = ι true := by
    ext z
    show cxQ z false ↔ z = true
    cases z <;> simp [cxQ]
  have htQ : true ∈ fld cxQ := ⟨false, Or.inl (by simp [cxQ])⟩
  have e3 : scFun cxP cxP cxQ (ι true) = anc cxP ʻʻ refs cxP true :=
    pm232_23 ⟨htQ, ⟨false, rfl, rfl⟩⟩
  have ht : true ∈ fld cxP := ⟨false, Or.inr ⟨rfl, rfl⟩⟩
  rw [← e1, e, e2, e3] at ht
  obtain ⟨v, hv, hanc⟩ := ht
  have hv0 : v = false := hv.1
  subst hv0
  rcases anc_iff_po.1 hanc with ⟨h1, -⟩ | hp
  · exact absurd h1 (by decide)
  · rw [po_iff_transGen] at hp
    obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.1 hp
    exact absurd hb.1 (by decide)

/-- ✱232·53. \(\vdash :Q\in \text{connex} .z\in \overrightarrow{Q}ʻx\cap \text{ᗡ}ʻR.\supset .(P\overline{R} Q)_{\text{sc}}ʻ\overrightarrow{Q}ʻx=(P\overline{R} Q)_{\text{sc}}ʻ(\overrightarrow{Q}ʻx\cap \overleftarrow{Q}_{*}ʻz)\) -/
theorem pm232_53 {x z : β} :
    Q ∈ connex ∧ z ∈ refs Q x ∩ codom R →
      scFun P R Q (refs Q x) = scFun P R Q (refs Q x ∩ rels (anc Q) z) := by
  rintro ⟨hcon, hzx, hzR⟩
  rw [mem_connex] at hcon
  have hzQ : z ∈ fld Q := fld_of_left hzx
  ext y
  rw [mem_scFun', mem_scFun']
  refine and_congr ⟨fun h u hu => ?_, fun h u hu => ?_⟩ Iff.rfl
  · obtain ⟨⟨⟨hux, hzu⟩, huQ⟩, huR⟩ := hu
    obtain ⟨v, ⟨w, ⟨hwx, huw⟩, hvw⟩, hyv⟩ := h u ⟨⟨hux, huQ⟩, huR⟩
    exact ⟨v, ⟨w, ⟨⟨hwx, anc_trans' hzu huw⟩, huw⟩, hvw⟩, hyv⟩
  · obtain ⟨⟨hux, huQ⟩, huR⟩ := hu
    have hzu' : anc Q z u ∨ anc Q u z := by
      rcases hcon z u ⟨hzQ, huQ⟩ with (h1 | e) | h1
      · exact Or.inl (anc_of h1)
      · exact Or.inl (e ▸ anc_rfl hzQ)
      · exact Or.inr (anc_of h1)
    rcases hzu' with hzu | huz
    · obtain ⟨v, ⟨w, ⟨⟨hwx, -⟩, huw⟩, hvw⟩, hyv⟩ := h u ⟨⟨⟨hux, hzu⟩, huQ⟩, huR⟩
      exact ⟨v, ⟨w, ⟨hwx, huw⟩, hvw⟩, hyv⟩
    · obtain ⟨v, ⟨w, ⟨⟨hwx, hzw⟩, -⟩, hvw⟩, hyv⟩ := h z ⟨⟨⟨hzx, anc_rfl hzQ⟩, hzQ⟩, hzR⟩
      exact ⟨v, ⟨w, ⟨hwx, anc_trans' huz hzw⟩, hvw⟩, hyv⟩

/-!
## [✱233] On the limits of functions

*(Vol. 2, p. 745)*

> *Summary of* *233.
>
> There are four limits of a function as the argument approaches some term \(a\) in the argument-series, namely the upper and lower limits of the ultimate oscillation for approaches from below and above respectively. If the ultimate oscillation for approaches to \(a\) from below reduces to a single term, *i.e.* if \((P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa \in 1\), that one term is *the* limit of the function for approaches to \(a\) from below. If this one term is also the ultimate oscillation for approaches from above, we may call it simply the limit of the function for the argument \(a\). This may or may not (when it exists) be equal to the value for the argument \(a\). It is characteristic of *continuous* functions that *the* limit exists for every argument, and is always equal to the value for that argument. Continuous functions will be considered in *234.
>
> …

**Lean reading.** `(P R̄ Q)_lmx` is the relation `lmx P R Q` (✱233·01) and `R(PQ)` the relation `rlim R P Q`
(✱233·02); both may be many-valued, so `(P R̄ Q)_lmx'α` is `Desc (lmx P R Q) S ψ` and `R(PQ)'a`
is `Desc (rlim R P Q) a ψ`, with `E!` as `EDesc`; `(P̆ R̄ Q)_lmx` is `lmx P˘ R Q`, `R(P̆Q)` is
`rlim R P˘ Q`. An equation between two descriptions gives the first the larger scope, and an
equation chain is the conjunction of its links. `R'max_Q'…` and `R(PQ)'lt_Q'α` are double
descriptions (`Desc2`), `ῐ'…` is `Desc iota˘ … ψ`, `P_1 ∪̇ P̆_*` is `P1 P ⊍ ancCnv P`,
`B'P̆` is `Desc Beg P˘ ψ`. "Hp ✱233·N" is written out. The descriptions are reduced to
`limax_P` of the limiting sections by `lmx_apply`, `rlim_apply`, and the results of ✱231–✱232.
In ✱233·5–·53 the e-text often prints `α` for the argument `a` (`= lt_Q'(α ∩ ᗡ'R)`); `a` is
read.

**Status.** proved (all propositions; ✱233·01·02 definition; ✱233·2, ✱233·23, ✱233·421, ✱233·425,
✱233·43, ✱233·501, ✱233·51, ✱233·511, ✱233·512, ✱233·513, ✱233·514, ✱233·515, ✱233·52 proved
(reading): transcription errors; ✱233·516 proved (corrected): false as printed with `lt_Q'α`,
read with `lt_Q'(α ∩ ᗡ'R)` as in ✱233·515; see their docstrings)
-/

/-- ✱233·01 (Df). \((P\overline{R} Q)_{\text{lmx}}=\text{limax}_P\mid (P\overline{R} Q)_{\text{sc}} \quad\text{Df}\) -/
theorem pm233_01 : lmx P R Q = limaxP P ⨾ scRel P R Q := rfl

/-- ✱233·02 (Df). \(R(PQ)=(P\overline{R} Q)_{\text{lmx}}\mid \overrightarrow{Q} \quad\text{Df}\) -/
theorem pm233_02 : rlim R P Q = lmx P R Q ⨾ Rfwd Q := rfl

/-- ✱233·1. \(\vdash :y\{(P\overline{R} Q)_{\text{lmx}}\}\alpha .\equiv .y(\text{limax}_P)\{(P\overline{R} Q)_{\text{sc}}ʻ\alpha\} \quad[(*233·01)]\)

`(P R̄ Q)_sc'α` always exists (`scRel` is a `graph`), so it is written `scFun P R Q S`. -/
theorem pm233_1 {S : Set β} {y : α} : lmx P R Q y S ↔ limaxP P y (scFun P R Q S) :=
  lmx_apply

private theorem desc_lmx {P : α → α → Prop} {S : Set β} {ψ : α → Prop} :
    Desc (lmx P R Q) S ψ ↔ Desc (limaxP P) (scFun P R Q S) ψ := by
  have e : (fun z => lmx P R Q z S) = fun z => limaxP P z (scFun P R Q S) :=
    funext fun z => propext lmx_apply
  show TheIs (fun z => lmx P R Q z S) ψ ↔ TheIs (fun z => limaxP P z (scFun P R Q S)) ψ
  rw [e]

private theorem edesc_lmx {P : α → α → Prop} {S : Set β} :
    EDesc (lmx P R Q) S ↔ EDesc (limaxP P) (scFun P R Q S) := by
  have e : (fun z => lmx P R Q z S) = fun z => limaxP P z (scFun P R Q S) :=
    funext fun z => propext lmx_apply
  show EBang (fun z => lmx P R Q z S) ↔ EBang (fun z => limaxP P z (scFun P R Q S))
  rw [e]

private theorem desc_rlim {P : α → α → Prop} {a : β} {ψ : α → Prop} :
    Desc (rlim R P Q) a ψ ↔ Desc (limaxP P) (scFun P R Q (refs Q a)) ψ := by
  have e : (fun z => rlim R P Q z a) = fun z => limaxP P z (scFun P R Q (refs Q a)) :=
    funext fun z => propext rlim_apply
  show TheIs (fun z => rlim R P Q z a) ψ ↔ TheIs (fun z => limaxP P z (scFun P R Q (refs Q a))) ψ
  rw [e]

private theorem rlim_iff_lmx {P : α → α → Prop} {a : β} {y : α} :
    rlim R P Q y a ↔ lmx P R Q y (refs Q a) :=
  rlim_apply.trans lmx_apply.symm

private theorem eqDesc {φ₁ : α → Prop} {φ₂ : α → Prop} {v : α} (h1 : ∀ b, φ₁ b ↔ b = v)
    (h2 : ∀ b, φ₂ b ↔ b = v) : TheIs φ₁ (fun a => TheIs φ₂ (fun b => a = b)) :=
  (TheIs_iff_of_unique h1).2 ((TheIs_iff_of_unique h2).2 rfl)

private theorem limaxP_unique {P : α → α → Prop} (hc : P ∈ connex) {a b : α} {A : Set α}
    (ha : limaxP P a A) (hb : limaxP P b A) : a = b := by
  rcases ha with ha | ⟨ha, hna⟩ <;> rcases hb with hb | ⟨hb, hnb⟩
  · exact maxP_unique hc ha hb
  · exact absurd ⟨a, ha⟩ hnb
  · exact absurd ⟨b, hb⟩ hna
  · exact seqP_unique hc ha hb

private theorem limax_val {P : α → α → Prop} (hc : P ∈ connex) {l : α} {A : Set α}
    (hl : limaxP P l A) (b : α) : limaxP P b A ↔ b = l :=
  ⟨fun hb => limaxP_unique hc hb hl, fun e => e ▸ hl⟩

private theorem limax_exists' {P : α → α → Prop} (hc : P ∈ connex) (hD : P ∈ Ded) (A : Set α) :
    ∃ l, ∀ b, limaxP P b A ↔ b = l := by
  rcases mem_Ded.1 hD A with ⟨m, hm⟩ | ⟨s, hs⟩
  · exact ⟨m, limax_val hc (Or.inl hm)⟩
  · by_cases hmax : ∃ m, maxP P m A
    · obtain ⟨m, hm⟩ := hmax
      exact ⟨m, limax_val hc (Or.inl hm)⟩
    · exact ⟨s, limax_val hc (Or.inr ⟨hs, hmax⟩)⟩

private theorem lmxc_val {P : α → α → Prop} {S : Set β} {v : α}
    (h : ∀ b, liminP P b (scFun P˘ R Q S) ↔ b = v) (b : α) : lmx P˘ R Q b S ↔ b = v := by
  rw [lmx_apply, ← liminP_eq_limaxP_cnv]
  exact h b

private theorem lmx_val {P : α → α → Prop} {S : Set β} {v : α}
    (h : ∀ b, limaxP P b (scFun P R Q S) ↔ b = v) (b : α) : lmx P R Q b S ↔ b = v :=
  lmx_apply.trans (h b)

/-- ✱233·101. \(\vdash :y=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\equiv .y=\text{limax}_Pʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha \quad[*233·1]\) -/
theorem pm233_101 {S : Set β} {y : α} :
    Desc (lmx P R Q) S (fun z => y = z) ↔ Desc (limaxP P) (scFun P R Q S) (fun z => y = z) :=
  desc_lmx

/-- ✱233·102. \[\begin{align}\vdash :\text{E}!\text{limax}_Pʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha .&\equiv .(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =\text{limax}_Pʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha\\. &\equiv .\text{E}!(P\overline{R} Q)_{\text{lmx}}ʻ\alpha \quad[*233·101.*14·28]\end{align}\]

The chain of three equivalences is the conjunction of its two links. -/
theorem pm233_102 {S : Set β} :
    (EDesc (limaxP P) (scFun P R Q S) ↔
        Desc (lmx P R Q) S (fun a => Desc (limaxP P) (scFun P R Q S) (fun b => a = b))) ∧
      (Desc (lmx P R Q) S (fun a => Desc (limaxP P) (scFun P R Q S) (fun b => a = b)) ↔
        EDesc (lmx P R Q) S) := by
  have h1 : EDesc (limaxP P) (scFun P R Q S) →
      Desc (lmx P R Q) S (fun a => Desc (limaxP P) (scFun P R Q S) (fun b => a = b)) := by
    rintro ⟨l, hl⟩
    exact eqDesc (lmx_val hl) hl
  refine ⟨⟨h1, fun h => ?_⟩, ⟨fun h => (TheIs_iff.1 h).1, fun h => h1 (edesc_lmx.1 h)⟩⟩
  obtain ⟨b, -, h'⟩ := h
  exact (TheIs_iff.1 h').1

/-- ✱233·103. \(\vdash :P\in \text{connex} .\supset .(P\overline{R} Q)_{\text{lmx}}\in 1\rightarrow \text{Cls} \quad[*207·41.*233·1]\) -/
theorem pm233_103 : P ∈ connex → lmx P R Q ∈ arrow one Cls := fun hc =>
  mem_arrow_one_Cls.2 fun _ _ _ ⟨hx, hy⟩ =>
    limaxP_unique hc (lmx_apply.1 hx) (lmx_apply.1 hy)

private theorem desc_eq_iff {φ : α → Prop} {y : α} (hu : ∀ a b, φ a → φ b → a = b) :
    TheIs φ (fun z => y = z) ↔ φ y := by
  constructor
  · rintro ⟨b, hb, e⟩
    exact e ▸ (hb b).2 rfl
  · intro h
    exact ⟨y, fun z => ⟨fun hz => hu z y hz h, fun e => e ▸ h⟩, rfl⟩

/-- `y = limax_P'α . ≡ . y ∈ C'P . P⃗'y = P''α` for a series (cf. ✱207·51), pointwise. -/
private theorem limax_iff_Ser {P : α → α → Prop} (hS : P ∈ Ser) {y : α} {A : Set α} :
    limaxP P y A ↔ y ∈ fld P ∧ refs P y = P ʻʻ A := by
  obtain ⟨⟨hirr, htr⟩, hcon⟩ := Ser_parts hS
  constructor
  · rintro (hm | ⟨hs, hnm⟩)
    · rw [maxP_iff] at hm
      obtain ⟨⟨hyA, hyP⟩, hmax⟩ := hm
      refine ⟨hyP, Set.ext fun u => ⟨fun hu => ⟨y, hyA, hu⟩, fun ⟨v, hv, huv⟩ => ?_⟩⟩
      rcases hcon v y (fld_of_right huv) hyP with (h | e) | h
      · exact htr u v y huv h
      · exact e ▸ huv
      · exact absurd h (hmax v hv)
    · rw [seqP_iff] at hs
      obtain ⟨⟨hup, hyP⟩, hleast⟩ := hs
      refine ⟨hyP, Set.ext fun u => ⟨fun hu => ?_,
        fun ⟨v, hv, huv⟩ => htr u v y huv (hup v ⟨hv, fld_of_right huv⟩)⟩⟩
      by_contra hn
      refine hleast u (fun v ⟨hvA, hvP⟩ => ?_) hu
      rcases hcon v u hvP (fld_of_left hu) with (h | e) | h
      · exact h
      · subst e
        exfalso
        refine hnm ⟨v, ?_⟩
        rw [maxP_iff]
        exact ⟨⟨hvA, hvP⟩, fun w hw hvw => hn ⟨w, hw, hvw⟩⟩
      · exact absurd ⟨v, hvA, h⟩ hn
  · rintro ⟨hyP, he⟩
    have hin : ∀ u, u ∈ P ʻʻ A → P u y := fun u hu => by
      rw [← he] at hu
      exact hu
    by_cases hyA : y ∈ A
    · left
      rw [maxP_iff]
      exact ⟨⟨hyA, hyP⟩, fun v hv hyv => hirr y (hin y ⟨v, hv, hyv⟩)⟩
    · right
      have hub : ∀ v, v ∈ A ∩ fld P → P v y := by
        intro v ⟨hvA, hvP⟩
        rcases hcon v y hvP hyP with (h | e) | h
        · exact h
        · exact absurd (e ▸ hvA) hyA
        · exact absurd (hin y ⟨v, hvA, h⟩) (hirr y)
      refine ⟨?_, ?_⟩
      · rw [seqP_iff]
        refine ⟨⟨hub, hyP⟩, fun z hz hzy => ?_⟩
        have : z ∈ P ʻʻ A := by
          rw [← he]
          exact hzy
        obtain ⟨v, hv, hzv⟩ := this
        exact hirr z (htr z v z hzv (hz v ⟨hv, fld_of_right hzv⟩))
      · rintro ⟨m, hm⟩
        rw [maxP_iff] at hm
        have : m ∈ refs P y := hub m hm.1
        rw [he] at this
        obtain ⟨v, hv, hmv⟩ := this
        exact hm.2 v hv hmv

/-- ✱233·11. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.\supset :y=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\equiv .y\in CʻP.\overrightarrow{P}ʻy=Pʻʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha \\ &[*207·51.*233·101]\end{align}\] -/
theorem pm233_11 {S : Set β} {y : α} :
    P ∈ Ser →
      (Desc (lmx P R Q) S (fun z => y = z) ↔ y ∈ fld P ∧ refs P y = P ʻʻ scFun P R Q S) := by
  intro hS
  rw [desc_lmx, Desc, desc_eq_iff fun a b ha hb => limaxP_unique (Ser_connex hS) ha hb,
    limax_iff_Ser hS]

/-- ✱233·111. \[\begin{align}\vdash \colon\ldotp &P\in \text{Ser}.\exists !Pʻʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha .\supset :\\ &y=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\equiv .\overrightarrow{P}ʻy=Pʻʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha \quad[*207·52.*233·101]\end{align}\] -/
theorem pm233_111 {S : Set β} {y : α} :
    P ∈ Ser ∧ (P ʻʻ scFun P R Q S).Nonempty →
      (Desc (lmx P R Q) S (fun z => y = z) ↔ refs P y = P ʻʻ scFun P R Q S) := by
  rintro ⟨hS, u, hu⟩
  rw [pm233_11 hS]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [← h] at hu
  exact fld_of_right hu

/-- ✱233·12. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.{\sim}\text{E}!&\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha .\supset :\\ &y=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\equiv .y\in CʻP.\overrightarrow{P}ʻy=(P\overline{R} Q)_{\text{sc}}ʻ\alpha\end{align}\] -/
theorem pm233_12 {S : Set β} {y : α} :
    P ∈ Ser ∧ ¬EDesc (maxP P) (scFun P R Q S) →
      (Desc (lmx P R Q) S (fun z => y = z) ↔ y ∈ fld P ∧ refs P y = scFun P R Q S) := by
  rintro ⟨hS, hnE⟩
  have e : P ʻʻ scFun P R Q S = scFun P R Q S := by
    refine Set.Subset.antisymm pm231_13.2 fun u hu => ?_
    by_contra hn
    have hmu : maxP P u (scFun P R Q S) := by
      rw [maxP_iff]
      exact ⟨⟨hu, hu.2⟩, fun w hw huw => hn ⟨w, hw, huw⟩⟩
    exact hnE ⟨u, fun m => ⟨fun hm => maxP_unique (Ser_connex hS) hm hmu, fun e => e ▸ hmu⟩⟩
  rw [pm233_11 hS, e]

/-- ✱233·13. \[\begin{align}\vdash :P\in \text{connex} \cap &\text{Ded}.\supset .\\ &\text{E}!(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .(P\overline{R} Q)_{\text{lmx}}ʻ\alpha=\text{limax}_Pʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha\\ &[*233·102·103.*214·11]\end{align}\] -/
theorem pm233_13 {S : Set β} :
    P ∈ connex ∩ Ded →
      EDesc (lmx P R Q) S ∧
        Desc (lmx P R Q) S (fun a => Desc (limaxP P) (scFun P R Q S) (fun b => a = b)) := by
  rintro ⟨hc, hD⟩
  obtain ⟨l, hl⟩ := limax_exists' hc hD (scFun P R Q S)
  exact ⟨⟨l, lmx_val hl⟩, eqDesc (lmx_val hl) hl⟩

/-- `limax_P` of `P R̄_sc Q` and `limax_{P̆}` of `P̆ R̄_sc Q` when the oscillation is `ι'x` and
`P_po ∈ Ser` (✱231·193). -/
private theorem os_one_lmx {Q' : β → β → Prop} {x0 : α} (hS : po P ∈ Ser)
    (hx0 : ∀ z, z ∈ osBar P R Q' ↔ z = x0) :
    (∀ b, limaxP P b (scBar P R Q') ↔ b = x0) ∧ ∀ b, limaxP P˘ b (scBar P˘ R Q') ↔ b = x0 := by
  have hS' : po P˘ ∈ Ser := by
    rw [po_cnv_eq]
    exact Ser_cnv hS
  have hx0' : ∀ z, z ∈ osBar P˘ R Q' ↔ z = x0 := fun z => by rw [osBar_cnv]; exact hx0 z
  exact ⟨limax_of_max (max_sc_of_os hS hx0), limax_of_max (max_sc_of_os hS' hx0')⟩

/-- ✱233·14. \[\begin{align}&\vdash :P\in \text{Ser}.(P\overline{R} Q)_{\text{os}}ʻ\alpha \in 1.\supset .(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha =\breve{\iota} ʻ(P\overline{R} Q)_{\text{os}}ʻ\alpha \\ &[*231·193.*233·102]\end{align}\]

The chain of three is the conjunction of its two links; `ῐ'…` is `Desc iota˘ … ψ`. -/
theorem pm233_14 {S : Set β} :
    P ∈ Ser ∧ osFun P R Q S ∈ one →
      Desc (lmx P R Q) S (fun a => Desc (lmx P˘ R Q) S (fun b => a = b)) ∧
        Desc (lmx P˘ R Q) S (fun b => Desc iota˘ (osFun P R Q S) (fun c => b = c)) := by
  rintro ⟨hS, h1⟩
  obtain ⟨x0, hx0⟩ := mem_one_iff.1 h1
  have hpo : po P ∈ Ser := by
    rw [po_eq_of_transR (Ser_transR hS)]
    exact hS
  obtain ⟨ha, hb⟩ := os_one_lmx (Q' := anc Q ⥏ S) hpo hx0
  have hb' : ∀ b, lmx P˘ R Q b S ↔ b = x0 := fun b => lmx_apply.trans (hb b)
  refine ⟨eqDesc (lmx_val ha) hb', (TheIs_iff_of_unique hb').2 ?_⟩
  rw [desc_iota_cnv]
  exact (TheIs_iff_of_unique hx0).2 rfl

/-- The complement of the limiting section, when the oscillation is null. -/
private theorem compl_of_os_null {S : Set β} (hU : scFun P R Q S ∪ scFun P˘ R Q S = fld P)
    (h0 : osFun P R Q S = Λ) (u : α) :
    u ∈ scFun P˘ R Q S ↔ u ∈ fld P ∧ u ∉ scFun P R Q S := by
  constructor
  · intro hu
    refine ⟨by rw [← hU]; exact Or.inr hu, fun hu' => ?_⟩
    have : u ∈ osFun P R Q S := ⟨hu', hu⟩
    rw [h0] at this
    exact not_mem_null this
  · rintro ⟨huP, huS⟩
    rw [← hU] at huP
    exact huP.resolve_left huS

/-- ✱233·141. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.&(P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =CʻP.(P\overline{R} Q)_{\text{os}}ʻ\alpha =\Lambda .\supset :\\ &\text{E}!(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\equiv .\text{E}!(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha \\ &[*211·727.*233·102.*231·13]\end{align}\] -/
theorem pm233_141 {S : Set β} :
    (P ∈ Ser ∧ scFun P R Q S ∪ scFun P˘ R Q S = fld P) ∧ osFun P R Q S = Λ →
      (EDesc (lmx P R Q) S ↔ EDesc (lmx P˘ R Q) S) := by
  rintro ⟨⟨hS, hU⟩, h0⟩
  have hc := compl_of_os_null hU h0
  constructor
  · rintro ⟨l, hl⟩
    have hl' : limaxP P l (scFun P R Q S) := lmx_apply.1 ((hl l).2 rfl)
    rcases cut_limax hS pm231_13 hc hl' with h | ⟨n, h, -⟩
    · exact ⟨l, lmxc_val h⟩
    · exact ⟨n, lmxc_val h⟩
  · rintro ⟨l, hl⟩
    have hl' : limaxP P˘ l (scFun P˘ R Q S) := lmx_apply.1 ((hl l).2 rfl)
    have hc' : ∀ u, u ∈ scFun P R Q S ↔ u ∈ fld P˘ ∧ u ∉ scFun P˘ R Q S := by
      intro u
      rw [fld_cnv]
      constructor
      · intro hu
        exact ⟨hu.2, fun hu' => (hc u).1 hu' |>.2 hu⟩
      · rintro ⟨huP, huS⟩
        by_contra hn
        exact huS ((hc u).2 ⟨huP, hn⟩)
    have key : ∀ m : α, (∀ b, liminP P˘ b (scFun P R Q S) ↔ b = m) →
        ∀ b, lmx P R Q b S ↔ b = m := by
      intro m h b
      rw [lmx_apply]
      have := h b
      rwa [liminP_eq_limaxP_cnv] at this
    rcases cut_limax (Ser_cnv hS) (pm231_13 (P := P˘)) hc' hl' with h | ⟨n, h, -⟩
    · exact ⟨l, key l h⟩
    · exact ⟨n, key n h⟩

/-- ✱233·142. \[\begin{align}&\vdash :P\in \text{Ser}.Q_{*}\unicode{x0294f}\alpha \in \text{connex} .\\ &Rʻʻ(\alpha \cap CʻQ)\subset CʻP.(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\in 0\cup 1.\\ &\text{E}!(P\overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR).(P\overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR){\sim}\in CʻP_{1}.\supset .\\ (P\overline{R} Q)_{\text{lmx}}ʻ\alpha &=(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha =(P\overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\\ &= (\breve{P} \overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\end{align}\]

`(P R̄ Q)_lmx'Q_*''(α ∩ ᗡ'R) ∼∈ C'P_1` is `Desc (lmx P R Q) … (fun l => l ∉ fld (P1 P))`; the
chain of four is the conjunction of its three links. -/
theorem pm233_142 {S : Set β} :
    ((((P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧
            osFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∈ zero ∪ one) ∧
          EDesc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R))) ∧
        Desc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R)) (fun l => l ∉ fld (P1 P)) →
      (Desc (lmx P R Q) S (fun a => Desc (lmx P˘ R Q) S (fun b => a = b)) ∧
          Desc (lmx P˘ R Q) S
            (fun a => Desc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R)) (fun b => a = b))) ∧
        Desc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R))
          (fun a => Desc (lmx P˘ R Q) (anc Q ʻʻ (S ∩ codom R)) (fun b => a = b)) := by
  rintro ⟨⟨⟨⟨⟨hS, hcQ⟩, hR⟩, h01⟩, l, hl⟩, hd⟩
  have hl1 : l ∉ fld (P1 P) := (TheIs_iff_of_unique hl).1 hd
  have hc := connex_anc (Ser_connex hS)
  have hU := (pm232_22 ⟨⟨hc, hcQ⟩, hR⟩).symm
  suffices key : ∃ v, ((∀ b, limaxP P b (scFun P R Q S) ↔ b = v) ∧
      ∀ b, limaxP P b (scFun P R Q (anc Q ʻʻ (S ∩ codom R))) ↔ b = v) ∧
      (∀ b, liminP P b (scFun P˘ R Q S) ↔ b = v) ∧
        ∀ b, liminP P b (scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R))) ↔ b = v by
    obtain ⟨v, ⟨h1, h2⟩, h3, h4⟩ := key
    exact ⟨⟨eqDesc (lmx_val h1) (lmxc_val h3), eqDesc (lmxc_val h3) (lmx_val h2)⟩,
      eqDesc (lmx_val h2) (lmxc_val h4)⟩
  have hl' : ∀ b, limaxP P b (scFun P R Q (anc Q ʻʻ (S ∩ codom R))) ↔ b = l :=
    fun b => lmx_apply.symm.trans (hl b)
  rcases h01 with h0 | h1
  · have h0' : osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = Λ := h0
    obtain ⟨e1, e2⟩ := pm232_34 ⟨⟨⟨hc, hcQ⟩, hR⟩, h0'⟩
    have hU' := (pm232_33 (S := S) ⟨⟨hc, hcQ⟩, hR⟩).2
    rw [e1, e2]
    rcases cut_limax hS pm231_13 (compl_of_os_null hU' h0') ((hl' l).2 rfl) with h3 | ⟨n, -, h3⟩
    · exact ⟨l, ⟨hl', hl'⟩, h3, h3⟩
    · exact absurd ⟨n, Or.inl h3⟩ hl1
  · obtain ⟨x, hx⟩ := mem_one_iff.1 h1
    have hos : osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x := Set.ext hx
    obtain ⟨⟨⟨e1, -⟩, -⟩, hxP⟩ := os_data hc hos
    have hm : ∀ b, limaxP P b (scFun P R Q (anc Q ʻʻ (S ∩ codom R))) ↔ b = x := by
      rw [e1]
      exact limax_of_max (absA_352 (fun u w hu h => anc_trans' h hu) (fun _ h => h)
        (anc_rfl hxP) hxP (Ser_J hS))
    have hlx : l = x := (hm l).1 ((hl' l).2 rfl)
    subst hlx
    exact ⟨l, os_one_values hS hos hl1 hU⟩

/-- ✱233·15. \[\begin{align}\vdash \colon\ldotp P\in &\text{Ser}\cap \text{Ded}.(P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =CʻP.(P\overline{R} Q)_{\text{os}}ʻ\alpha =\Lambda .\supset :\\ &(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha .\lor.\{(P\overline{R} Q)_{\text{lmx}}ʻ\alpha \}P_{1}\{(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha\}\\ &[*214·43.*233·13.*231·13]\end{align}\] -/
theorem pm233_15 {S : Set β} :
    (P ∈ Ser ∩ Ded ∧ scFun P R Q S ∪ scFun P˘ R Q S = fld P) ∧ osFun P R Q S = Λ →
      Desc (lmx P R Q) S (fun a => Desc (lmx P˘ R Q) S (fun b => a = b)) ∨
        Desc (lmx P R Q) S (fun a => Desc (lmx P˘ R Q) S (fun b => P1 P a b)) := by
  rintro ⟨⟨⟨hS, hD⟩, hU⟩, h0⟩
  obtain ⟨l, hl⟩ := limax_exists' (Ser_connex hS) hD (scFun P R Q S)
  rcases cut_limax hS pm231_13 (compl_of_os_null hU h0) ((hl l).2 rfl) with h | ⟨n, h, hP1⟩
  · exact Or.inl (eqDesc (lmx_val hl) (lmxc_val h))
  · exact Or.inr ((TheIs_iff_of_unique (lmx_val hl)).2 ((TheIs_iff_of_unique (lmxc_val h)).2 hP1))

private theorem connex_ancFres {S : Set β} (hcQ : anc Q ∈ connex) : anc Q ⥏ S ∈ connex := by
  rw [mem_connex] at hcQ ⊢
  rw [fld_anc] at hcQ
  intro y z ⟨hy, hz⟩
  obtain ⟨hyS, hyQ⟩ := fld_ancFres.1 hy
  obtain ⟨hzS, hzQ⟩ := fld_ancFres.1 hz
  rcases hcQ y z ⟨hyQ, hzQ⟩ with (h | h) | h
  · exact Or.inl (Or.inl ⟨⟨hyS, h⟩, hzS⟩)
  · exact Or.inl (Or.inr h)
  · exact Or.inr ⟨⟨hzS, h⟩, hyS⟩

/-- ✱233·16. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}\cap &\text{Ded}.P^{2}=P.Q_{*}\in \text{connex} .RʻʻCʻQ\subset CʻP.\supset :\\ &(P\overline{R} Q)_{\text{os}}ʻ\alpha \in 0\cup 1.\supset _{\alpha }.(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha\end{align}\] -/
theorem pm233_16 :
    ((P ∈ Ser ∩ Ded ∧ rsq P = P) ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      ∀ S : Set β, osFun P R Q S ∈ zero ∪ one →
        Desc (lmx P R Q) S (fun a => Desc (lmx P˘ R Q) S (fun b => a = b)) := by
  rintro ⟨⟨⟨⟨hS, hD⟩, hd⟩, hcQ⟩, hR⟩ S h01
  rcases h01 with h0 | h1
  · have hU := (pm232_22 (S := S) ⟨⟨connex_anc (Ser_connex hS), connex_ancFres hcQ⟩,
      fun v ⟨y, hy, hvy⟩ => hR ⟨y, hy.2, hvy⟩⟩).symm
    rcases pm233_15 ⟨⟨⟨hS, hD⟩, hU⟩, (h0 : _ = Λ)⟩ with h | h
    · exact h
    · exfalso
      obtain ⟨l, -, h'⟩ := h
      obtain ⟨n, -, hP1⟩ := h'
      exact P1_empty_of_dense hS hd l n hP1
  · exact (pm233_14 ⟨hS, h1⟩).1

/-- `limax_P'C'P` is `B'P̆` (pointwise): a sequent of `C'P` would precede itself. -/
private theorem limax_fld_iff {P : α → α → Prop} {y : α} : limaxP P y (fld P) ↔ Beg y P˘ := by
  constructor
  · rintro (hm | ⟨hs, -⟩)
    · rw [maxP_iff] at hm
      obtain ⟨⟨hy, -⟩, hmax⟩ := hm
      obtain ⟨z, hz⟩ := hy
      refine ⟨?_, fun ⟨w, hw⟩ => hmax w (fld_of_right hw) hw⟩
      rcases hz with hz | hz
      · exact absurd hz (hmax z (fld_of_right hz))
      · exact ⟨z, hz⟩
    · rw [seqP_iff] at hs
      obtain ⟨⟨hup, hyP⟩, hleast⟩ := hs
      exact absurd (hup y ⟨hyP, hyP⟩) (hleast y fun v hv => hup v hv)
  · rintro ⟨⟨z, hz⟩, hn⟩
    left
    rw [maxP_iff]
    exact ⟨⟨fld_of_right hz, fld_of_right hz⟩, fun w _ hw => hn ⟨w, hw⟩⟩

/-- ✱233·17. \(\vdash \colon\ldotp \alpha \cap CʻQ\cap \text{ᗡ}ʻR=\Lambda .\supset :y=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\equiv .y=Bʻ\breve{P}\)

`y = B'P̆` is `Desc Beg P˘ (fun b => y = b)`. -/
theorem pm233_17 {S : Set β} {y : α} :
    S ∩ fld Q ∩ codom R = Λ →
      (Desc (lmx P R Q) S (fun z => y = z) ↔ Desc Beg P˘ (fun b => y = b)) := by
  intro h
  have e : scFun P R Q S = fld P := (pm232_15 h).1.1.trans ((pm232_15 h).1.2.trans (pm232_15 h).2)
  rw [desc_lmx, e]
  have e2 : (fun z => limaxP P z (fld P)) = fun z => Beg z P˘ :=
    funext fun z => propext limax_fld_iff
  show TheIs (fun z => limaxP P z (fld P)) _ ↔ TheIs (fun z => Beg z P˘) _
  rw [e2]

private theorem lmx_null_val {P : α → α → Prop} {S : Set β} (h : S ∩ fld Q ∩ codom R = Λ)
    (b : α) : lmx P R Q b S ↔ Beg b P˘ := by
  have e : scFun P R Q S = fld P := (pm232_15 h).1.1.trans ((pm232_15 h).1.2.trans (pm232_15 h).2)
  rw [lmx_apply, e, limax_fld_iff]

/-- ✱233·171. \(\vdash :\alpha \cap CʻQ\cap \text{ᗡ}ʻR=\Lambda .\supset .{\sim}\{(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha\}\) -/
theorem pm233_171 {S : Set β} :
    S ∩ fld Q ∩ codom R = Λ →
      ¬Desc (lmx P R Q) S (fun a => Desc (lmx P˘ R Q) S (fun b => a = b)) := by
  intro h hd
  obtain ⟨b, hb, b', hb', e⟩ := hd
  have h1 : Beg b P˘ := (lmx_null_val h b).1 ((hb b).2 rfl)
  have h2 : Beg b' P˘˘ := (lmx_null_val (P := P˘) h b').1 ((hb' b').2 rfl)
  subst e
  exact h2.2 h1.1

/-- ✱233·172. \[\begin{align}\vdash :\alpha \cap CʻQ\cap \text{ᗡ}ʻR=\Lambda .\text{E}!(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\text{E}!(\breve{P} &\overline{R} Q)_{\text{lmx}}ʻ\alpha .\supset .\\ &(P\overline{R} Q)_{\text{os}}ʻ\alpha {\sim}\in 0\cup 1\end{align}\] -/
theorem pm233_172 {S : Set β} :
    (S ∩ fld Q ∩ codom R = Λ ∧ EDesc (lmx P R Q) S) ∧ EDesc (lmx P˘ R Q) S →
      osFun P R Q S ∉ zero ∪ one := by
  rintro ⟨⟨h, b, hb⟩, b', hb'⟩ h01
  have h1 : Beg b P˘ := (lmx_null_val h b).1 ((hb b).2 rfl)
  have h2 : Beg b' P˘˘ := (lmx_null_val (P := P˘) h b').1 ((hb' b').2 rfl)
  have e : osFun P R Q S = fld P := (pm232_15 h).2
  rw [e] at h01
  have hbP : b ∈ fld P := by
    obtain ⟨z, hz⟩ := h1.1
    exact fld_of_right hz
  have hb'P : b' ∈ fld P := by
    obtain ⟨z, hz⟩ := h2.1
    exact fld_of_left hz
  have hne : b ≠ b' := fun e => h2.2 (e ▸ h1.1)
  rcases h01 with h0 | h1'
  · have : fld P = Λ := h0
    rw [this] at hbP
    exact not_mem_null hbP
  · obtain ⟨c, hc⟩ := mem_one_iff.1 h1'
    exact hne (((hc b).1 hbP).trans ((hc b').1 hb'P).symm)

/-- ✱233·173. \[\begin{align}\vdash :(P\overline{R} Q)_{\text{os}}ʻ\alpha \in 0\cup 1.\text{E}!&(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\text{E}!(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha .\supset .\\ &\exists !\alpha \cap CʻQ\cap \text{ᗡ}ʻR \quad[*233·172.\text{Transp}]\end{align}\] -/
theorem pm233_173 {S : Set β} :
    (osFun P R Q S ∈ zero ∪ one ∧ EDesc (lmx P R Q) S) ∧ EDesc (lmx P˘ R Q) S →
      (S ∩ fld Q ∩ codom R).Nonempty := by
  rintro ⟨⟨h01, h1⟩, h2⟩
  by_contra hn
  have e : S ∩ fld Q ∩ codom R = Λ := eq_null_of fun y hy => hn ⟨y, hy⟩
  exact pm233_172 ⟨⟨e, h1⟩, h2⟩ h01

/-- ✱233·174. \(\vdash :P \,\unicode{x2abd}\, J.(P\overline{R} Q)_{\text{os}}ʻ\alpha \in 1.\supset .\exists !\alpha \cap CʻQ\cap \text{ᗡ}ʻR\) -/
theorem pm233_174 {S : Set β} :
    P ⪽ J ∧ osFun P R Q S ∈ one → (S ∩ fld Q ∩ codom R).Nonempty := by
  rintro ⟨hJ, h1⟩
  by_contra hn
  have e : S ∩ fld Q ∩ codom R = Λ := eq_null_of fun y hy => hn ⟨y, hy⟩
  rw [(pm232_15 e).2] at h1
  obtain ⟨c, hc⟩ := mem_one_iff.1 h1
  obtain ⟨z, hz⟩ := ((hc c).2 rfl)
  rcases hz with hz | hz
  · exact hJ _ _ hz (((hc c).1 (fld_of_left hz)).trans ((hc z).1 (fld_of_right hz)).symm)
  · exact hJ _ _ hz (((hc z).1 (fld_of_left hz)).trans ((hc c).1 (fld_of_right hz)).symm)

/-- ✱233·2. \[\begin{align}&\vdash :Q_{*}\unicode{x0294f}\alpha \in \text{connex} .P\in \text{Ser}.Rʻʻ(\alpha \cap CʻQ)\subset CʻP.\\ &(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)=\Lambda .\text{E}!(P\overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR).\supset .\\ &(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(P\overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR).(\breve{P} R\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} R\overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\\ &[*232·34.*211·727.*233·102]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `(P̆ R R̄ Q)_lmx` for
`(P̆ R̄ Q)_lmx` (twice). -/
theorem pm233_2 {S : Set β} :
    ((((anc Q ⥏ S ∈ connex ∧ P ∈ Ser) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧
          osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = Λ) ∧
        EDesc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R))) →
      Desc (lmx P R Q) S
          (fun a => Desc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R)) (fun b => a = b)) ∧
        Desc (lmx P˘ R Q) S
          (fun a => Desc (lmx P˘ R Q) (anc Q ʻʻ (S ∩ codom R)) (fun b => a = b)) := by
  rintro ⟨⟨⟨⟨hcQ, hS⟩, hR⟩, h0⟩, l, hl⟩
  have hc := connex_anc (Ser_connex hS)
  obtain ⟨e1, e2⟩ := pm232_34 ⟨⟨⟨hc, hcQ⟩, hR⟩, h0⟩
  have hU' := (pm232_33 (S := S) ⟨⟨hc, hcQ⟩, hR⟩).2
  have hl' : ∀ b, limaxP P b (scFun P R Q (anc Q ʻʻ (S ∩ codom R))) ↔ b = l :=
    fun b => lmx_apply.symm.trans (hl b)
  have hl'' : ∀ b, limaxP P b (scFun P R Q S) ↔ b = l := by rw [e1]; exact hl'
  obtain ⟨n, hn⟩ : ∃ n, ∀ b, liminP P b (scFun P˘ R Q (anc Q ʻʻ (S ∩ codom R))) ↔ b = n := by
    rcases cut_limax hS pm231_13 (compl_of_os_null hU' h0) ((hl' l).2 rfl) with h | ⟨n, h, -⟩
    · exact ⟨l, h⟩
    · exact ⟨n, h⟩
  have hn' : ∀ b, liminP P b (scFun P˘ R Q S) ↔ b = n := by rw [e2]; exact hn
  exact ⟨eqDesc (lmx_val hl'') (lmx_val hl'), eqDesc (lmxc_val hn') (lmxc_val hn)⟩

/-- ✱233·21. \[\begin{align}\vdash :&P_{\text{po}}\in \text{Ser}.\exists !(P\overline{R} Q)_{\text{os}}ʻ\alpha .(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\in 1.\supset .\\ &(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha =(P\overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\\ &=(\breve{P} \overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)=\breve{\iota} ʻ(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\\ &[*232·341.*231·193]\end{align}\]

The chain of five is the conjunction of its four links. -/
theorem pm233_21 {S : Set β} :
    (po P ∈ Ser ∧ (osFun P R Q S).Nonempty) ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∈ one →
      ((Desc (lmx P R Q) S (fun a => Desc (lmx P˘ R Q) S (fun b => a = b)) ∧
          Desc (lmx P˘ R Q) S
            (fun a => Desc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R)) (fun b => a = b))) ∧
          Desc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R))
            (fun a => Desc (lmx P˘ R Q) (anc Q ʻʻ (S ∩ codom R)) (fun b => a = b))) ∧
        Desc (lmx P˘ R Q) (anc Q ʻʻ (S ∩ codom R))
          (fun a => Desc iota˘ (osFun P R Q (anc Q ʻʻ (S ∩ codom R))) (fun c => a = c)) := by
  rintro ⟨⟨hS, hne⟩, h1⟩
  have hc : anc P ∈ connex := connex_anc_of_po (Ser_connex hS)
  obtain ⟨e1, e2⟩ := pm232_341 ⟨⟨hc, hne⟩, h1⟩
  obtain ⟨x0, hx0⟩ := mem_one_iff.1 h1
  obtain ⟨ha, hb⟩ := os_one_lmx (Q' := anc Q ⥏ anc Q ʻʻ (S ∩ codom R)) hS hx0
  have ha' : ∀ b, lmx P R Q b (anc Q ʻʻ (S ∩ codom R)) ↔ b = x0 := fun b => lmx_apply.trans (ha b)
  have hb' : ∀ b, lmx P˘ R Q b (anc Q ʻʻ (S ∩ codom R)) ↔ b = x0 :=
    fun b => lmx_apply.trans (hb b)
  have ha'' : ∀ b, lmx P R Q b S ↔ b = x0 := fun b => by rw [lmx_apply, e1]; exact ha b
  have hb'' : ∀ b, lmx P˘ R Q b S ↔ b = x0 := fun b => by rw [lmx_apply, e2]; exact hb b
  refine ⟨⟨⟨eqDesc ha'' hb'', eqDesc hb'' ha'⟩, eqDesc ha' hb'⟩, (TheIs_iff_of_unique hb').2 ?_⟩
  rw [desc_iota_cnv]
  exact (TheIs_iff_of_unique hx0).2 rfl

/-- ✱233·22. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)=\iota ʻx.\\ &(P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup (\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha =CʻP.\supset :\\ &x=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\lor.(P\overline{R} Q)_{\text{lmx}}ʻ\alpha P_{1}x.(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha\end{align}\]

`x = (P R̄ Q)_lmx'α .∨. (P R̄ Q)_lmx'α P_1 x . (P R̄ Q)_lmx'α = max_P'…`: the `∨` (Group I) has
the product as its right member. -/
theorem pm233_22 {S : Set β} {x : α} :
    (P ∈ Ser ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧
        scFun P R Q S ∪ scFun P˘ R Q S = fld P →
      Desc (lmx P R Q) S (fun l => x = l) ∨
        Desc (lmx P R Q) S (fun l => P1 P l x) ∧
          Desc (lmx P R Q) S (fun l => Desc (maxP P) (scFun P R Q S) (fun m => l = m)) := by
  rintro ⟨⟨hS, hos⟩, hU⟩
  obtain ⟨⟨-, hAx, hBx⟩, hxP⟩ := os_data (connex_anc (Ser_connex hS)) hos
  have hJ := Ser_J hS
  by_cases hxA : x ∈ scFun P R Q S
  · left
    exact (TheIs_iff_of_unique (lmx_val (limax_of_max (absA_352 scFun_down hAx hxA hxP hJ)))).2 rfl
  · have hseq := absA_356 hS hAx hBx hxP hU hxA
    by_cases hmax : ∃ m, maxP P m (scFun P R Q S)
    · right
      obtain ⟨m, hm⟩ := hmax
      have hmu : ∀ b, maxP P b (scFun P R Q S) ↔ b = m :=
        fun b => ⟨fun hb => maxP_unique (Ser_connex hS) hb hm, fun e => e ▸ hm⟩
      have hlm := lmx_val (limax_of_max hmu)
      have hmx : m ≠ x := fun e => hxA (e ▸ (maxP_iff.1 hm).1.1)
      exact ⟨(TheIs_iff_of_unique hlm).2 (absA_358 scFun_down hAx hBx hxP hU hJ hm hmx),
        eqDesc hlm hmu⟩
    · left
      have hl : ∀ b, limaxP P b (scFun P R Q S) ↔ b = x := fun b =>
        ⟨fun hb => hb.elim (fun h => absurd ⟨b, h⟩ hmax) fun h => (hseq b).1 h.1,
          fun e => Or.inr ⟨(hseq b).2 e, hmax⟩⟩
      exact (TheIs_iff_of_unique (lmx_val hl)).2 rfl

/-- ✱233·23. \[\begin{align}&\vdash :\text{Hp}*233·22.\supset .\\ &x=(P\breve{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)=(\breve{P} \overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR) \quad[*231·193]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `(P R̆ Q)_lmx` for
`(P R̄ Q)_lmx`. The chain of three is the conjunction of its two links. -/
theorem pm233_23 {S : Set β} {x : α} :
    (P ∈ Ser ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧
        scFun P R Q S ∪ scFun P˘ R Q S = fld P →
      Desc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R)) (fun a => x = a) ∧
        Desc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R))
          (fun a => Desc (lmx P˘ R Q) (anc Q ʻʻ (S ∩ codom R)) (fun b => a = b)) := by
  rintro ⟨⟨hS, hos⟩, -⟩
  have hpo : po P ∈ Ser := by
    rw [po_eq_of_transR (Ser_transR hS)]
    exact hS
  have hx0 : ∀ z, z ∈ osBar P R (anc Q ⥏ anc Q ʻʻ (S ∩ codom R)) ↔ z = x := fun z => by
    rw [show osBar P R (anc Q ⥏ anc Q ʻʻ (S ∩ codom R)) = ι x from hos]
    exact Iff.rfl
  obtain ⟨ha, hb⟩ := os_one_lmx hpo hx0
  have ha' : ∀ b, lmx P R Q b (anc Q ʻʻ (S ∩ codom R)) ↔ b = x := fun b => lmx_apply.trans (ha b)
  have hb' : ∀ b, lmx P˘ R Q b (anc Q ʻʻ (S ∩ codom R)) ↔ b = x :=
    fun b => lmx_apply.trans (hb b)
  exact ⟨(TheIs_iff_of_unique ha').2 rfl, eqDesc ha' hb'⟩

/-- ✱233·24. \(\vdash :\text{Hp}*233·22.x{\sim}\in \text{ᗡ}ʻP_{1}.\supset .x=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha \quad[*233·22]\) -/
theorem pm233_24 {S : Set β} {x : α} :
    ((P ∈ Ser ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧
        scFun P R Q S ∪ scFun P˘ R Q S = fld P) ∧ x ∉ codom (P1 P) →
      Desc (lmx P R Q) S (fun a => x = a) := by
  rintro ⟨⟨⟨hS, hos⟩, hU⟩, hx1⟩
  obtain ⟨⟨-, hAx, hBx⟩, hxP⟩ := os_data (connex_anc (Ser_connex hS)) hos
  exact (TheIs_iff_of_unique (lmx_val (absA_361 hS scFun_down hAx hBx hxP hU hx1))).2 rfl

/-- ✱233·241. \[\begin{align}&\vdash :\text{Hp}*233·22.x{\sim}\in CʻP_{1}.\supset .x=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P}\overline{R} Q)_{\text{lmx}}ʻ\alpha \\ &\left[*233·24 \frac{\breve{P}}{P}.*233·24\right]\end{align}\] -/
theorem pm233_241 {S : Set β} {x : α} :
    ((P ∈ Ser ∧ osFun P R Q (anc Q ʻʻ (S ∩ codom R)) = ι x) ∧
        scFun P R Q S ∪ scFun P˘ R Q S = fld P) ∧ x ∉ fld (P1 P) →
      Desc (lmx P R Q) S (fun a => x = a) ∧
        Desc (lmx P R Q) S (fun a => Desc (lmx P˘ R Q) S (fun b => a = b)) := by
  rintro ⟨⟨⟨hS, hos⟩, hU⟩, hx1⟩
  obtain ⟨⟨h1, -⟩, h3, -⟩ := os_one_values hS hos hx1 hU
  exact ⟨(TheIs_iff_of_unique (lmx_val h1)).2 rfl, eqDesc (lmx_val h1) (lmxc_val h3)⟩

/-- ✱233·25. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}\cap \text{Ded}.P^{2}=P.Q_{*}\in \text{connex} .RʻʻCʻQ\subset CʻP.\supset :\\ &(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\in 0\cup 1.\supset .\\ &(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(P\overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)=(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻQ_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR)\\ &[*232·39]\end{align}\]

The chain of four is the conjunction of its three links. -/
theorem pm233_25 {S : Set β} :
    ((P ∈ Ser ∩ Ded ∧ rsq P = P) ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      (osFun P R Q (anc Q ʻʻ (S ∩ codom R)) ∈ zero ∪ one →
        (Desc (lmx P R Q) S
              (fun a => Desc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R)) (fun b => a = b)) ∧
            Desc (lmx P R Q) (anc Q ʻʻ (S ∩ codom R))
              (fun a => Desc (lmx P˘ R Q) S (fun b => a = b))) ∧
          Desc (lmx P˘ R Q) S
            (fun a => Desc (lmx P˘ R Q) (anc Q ʻʻ (S ∩ codom R)) (fun b => a = b))) := by
  intro h h01
  obtain ⟨l, ⟨h1, h2⟩, h3, h4⟩ := dense_values h S h01
  exact ⟨⟨eqDesc (lmx_val h1) (lmx_val h2), eqDesc (lmx_val h2) (lmxc_val h3)⟩,
    eqDesc (lmxc_val h3) (lmxc_val h4)⟩

/-- ✱233·4. \(\vdash :y{R(PQ)}\alpha .\equiv .y\{(P\overline{R} Q)_{\text{lmx}}\}\overrightarrow{Q}ʻ\alpha \quad[(*233·02)]\) -/
theorem pm233_4 {a : β} {y : α} : rlim R P Q y a ↔ lmx P R Q y (refs Q a) := rlim_iff_lmx

/-- ✱233·401. \(\vdash :y=R(PQ)ʻ\alpha .\equiv .y=(P\overline{R} Q)_{\text{lmx}}ʻ\overrightarrow{Q}ʻ\alpha \quad[*233·4]\) -/
theorem pm233_401 {a : β} {y : α} :
    Desc (rlim R P Q) a (fun z => y = z) ↔ Desc (lmx P R Q) (refs Q a) (fun z => y = z) := by
  rw [desc_rlim, desc_lmx]

/-- ✱233·402. \(\vdash :P\in \text{connex} .\supset .R(PQ)\in 1\rightarrow \text{Cls} \quad[*207·41]\) -/
theorem pm233_402 : P ∈ connex → rlim R P Q ∈ arrow one Cls := fun hc =>
  mem_arrow_one_Cls.2 fun _ _ _ ⟨hx, hy⟩ =>
    limaxP_unique hc (rlim_apply.1 hx) (rlim_apply.1 hy)

/-- ✱233·41. \(\vdash :y=R(PQ)ʻ\alpha .\equiv .y=(P\overline{R} Q)_{\text{lmx}}ʻ(\overrightarrow{Q}ʻ\alpha \cap \text{ᗡ}ʻR)\) -/
theorem pm233_41 {a : β} {y : α} :
    Desc (rlim R P Q) a (fun z => y = z) ↔
      Desc (lmx P R Q) (refs Q a ∩ codom R) (fun z => y = z) := by
  rw [desc_rlim, desc_lmx]
  have e : scFun P R Q (refs Q a) = scFun P R Q (refs Q a ∩ codom R) := by
    apply pm232_13
    ext z
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨⟨h1, h3⟩, h2⟩, h3⟩, fun ⟨⟨⟨h1, _⟩, h2⟩, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  rw [e]

/-- ✱233·42. \[\begin{align}\vdash :.Q\in \text{trans}&\cap \text{connex} .\text{E}!\text{max}_{Q}ʻ(\overrightarrow{Q}ʻ\alpha \cap \text{ᗡ}ʻR).\supset :\\ &y=R(PQ)ʻ\alpha .\equiv .y=\text{limax}_PʻP_{*}ʻʻ\overrightarrow{R}ʻ \text{max}_{Q}ʻ(\overrightarrow{Q}ʻ\alpha \cap \text{ᗡ}ʻR)\\ &[*232·24.*233·401·101]\end{align}\]

`limax_P'P_*''R⃗'max_Q'(Q⃗'α ∩ ᗡ'R)` is
`Desc (maxP Q) … (fun m => Desc (limaxP P) (anc P ʻʻ refs R m) ψ)`. -/
theorem pm233_42 {a : β} {y : α} :
    Q ∈ transR ∩ connex ∧ EDesc (maxP Q) (refs Q a ∩ codom R) →
      (Desc (rlim R P Q) a (fun z => y = z) ↔
        Desc (maxP Q) (refs Q a ∩ codom R)
          (fun m => Desc (limaxP P) (anc P ʻʻ refs R m) (fun z => y = z))) := by
  rintro ⟨hQ, m, hm⟩
  have h := (TheIs_iff_of_unique hm).1 (pm232_51 (P := P) (R := R) ⟨hQ, ⟨m, hm⟩⟩)
  rw [desc_rlim, h]
  exact (TheIs_iff_of_unique hm
    (ψ := fun m => Desc (limaxP P) (anc P ʻʻ refs R m) (fun z => y = z))).symm

/-- ✱233·421. \[\begin{align}&\vdash :P\in \text{ᗡ}ʻʻʻJ\cap \text{trans}.Q\in \text{trans}\cap \text{connex} .Rʻ\text{max}_{Q}ʻ(\alpha \cap \text{ᗡ}ʻR)\in C^{P}.\supset .\\ &R(PQ)ʻ\alpha =Rʻ\text{max}_{Q}ʻ(\overrightarrow{Q}ʻ\alpha \cap \text{ᗡ}ʻR)\end{align}\]

**Status.** proved (reading): the e-text is garbled here: it prints `P ∈ ᗡ'''J ∩ trans` for
`P ∈ Rl'J ∩ trans` (the hypothesis of the reference ✱205·197: `P` contained in diversity and
transitive), `C^P` for `C'P`, and `R'max_Q'(α ∩ ᗡ'R)` for `R'max_Q'(Q⃗'α ∩ ᗡ'R)` (as in the
conclusion and in ✱233·42). `R(PQ)'α` is `R(PQ)'a`. -/
theorem pm233_421 {a : β} :
    (P ∈ rl J ∩ transR ∧ Q ∈ transR ∩ connex) ∧
        Desc2 R (maxP Q) (refs Q a ∩ codom R) (fun v => v ∈ fld P) →
      Desc (rlim R P Q) a (fun r => Desc2 R (maxP Q) (refs Q a ∩ codom R) (fun v => r = v)) := by
  rintro ⟨⟨⟨hJ, htr⟩, hQ⟩, hd⟩
  rw [desc2_iff] at hd
  obtain ⟨m, hm, v, hv, hvP⟩ := hd
  have hirr := mem_rl_J.1 hJ
  have tr := mem_transR.1 htr
  have h := (TheIs_iff_of_unique hm).1 (pm232_51 (P := P) (R := R) ⟨hQ, ⟨m, hm⟩⟩)
  have hrefs : refs R m = ι v := Set.ext hv
  have hval : ∀ b, limaxP P b (scFun P R Q (refs Q a)) ↔ b = v := by
    rw [h, hrefs]
    refine limax_of_max fun b => ?_
    rw [maxP_iff]
    constructor
    · rintro ⟨⟨⟨w, hw, hbw⟩, -⟩, hmax⟩
      rw [mem_unitCls] at hw
      subst hw
      rcases anc_iff_po.1 hbw with ⟨e, -⟩ | hp
      · exact e
      · rw [po_eq_of_transR htr] at hp
        exact absurd hp (hmax w ⟨w, rfl, anc_rfl hvP⟩)
    · intro e
      subst e
      refine ⟨⟨⟨b, rfl, anc_rfl hvP⟩, hvP⟩, fun w ⟨u, hu, hwu⟩ hbw => ?_⟩
      rw [mem_unitCls] at hu
      subst hu
      rcases anc_iff_po.1 hwu with ⟨e, -⟩ | hp
      · subst e
        exact hirr _ hbw
      · rw [po_eq_of_transR htr] at hp
        exact hirr _ (tr _ _ _ ⟨hbw, hp⟩)
  rw [desc_rlim]
  refine (TheIs_iff_of_unique hval).2 ?_
  rw [desc2_iff]
  exact (TheIs_iff_of_unique hm).2 ((TheIs_iff_of_unique hv).2 rfl)

/-- ✱233·422. \(\vdash \colon\ldotp \overrightarrow{Q}ʻ\alpha \cap \text{ᗡ}ʻR=\Lambda .\supset :y=R(PQ)ʻ\alpha .\equiv .y=Bʻ\breve{P} \quad[*233·17]\) -/
theorem pm233_422 {a : β} {y : α} :
    refs Q a ∩ codom R = Λ →
      (Desc (rlim R P Q) a (fun z => y = z) ↔ Desc Beg P˘ (fun b => y = b)) := by
  intro h
  rw [pm233_401]
  apply pm233_17
  refine eq_null_of fun z ⟨⟨h1, _⟩, h3⟩ => ?_
  have : z ∈ refs Q a ∩ codom R := ⟨h1, h3⟩
  rw [h] at this
  exact not_mem_null this

private theorem null_of_refs {a : β} (h : refs Q a ∩ codom R = Λ) :
    refs Q a ∩ fld Q ∩ codom R = Λ := by
  refine eq_null_of fun z ⟨⟨h1, _⟩, h3⟩ => ?_
  have : z ∈ refs Q a ∩ codom R := ⟨h1, h3⟩
  rw [h] at this
  exact not_mem_null this

private theorem desc_rlim_lmx {P : α → α → Prop} {a : β} {ψ : α → Prop} :
    Desc (rlim R P Q) a ψ ↔ Desc (lmx P R Q) (refs Q a) ψ := by
  rw [desc_rlim, desc_lmx]

private theorem edesc_rlim_lmx {P : α → α → Prop} {a : β} :
    EDesc (rlim R P Q) a ↔ EDesc (lmx P R Q) (refs Q a) := by
  have e : (fun z => rlim R P Q z a) = fun z => lmx P R Q z (refs Q a) :=
    funext fun z => propext rlim_iff_lmx
  show EBang (fun z => rlim R P Q z a) ↔ EBang (fun z => lmx P R Q z (refs Q a))
  rw [e]

/-- ✱233·423. \(\vdash :\overrightarrow{Q}ʻa\cap \text{ᗡ}ʻR=\Lambda .\supset .{\sim}\{R(PQ)ʻa=R(\breve{P} Q)ʻa\} \quad[*233·171]\)

`R(P̆Q)` is `rlim R P˘ Q`. -/
theorem pm233_423 {a : β} :
    refs Q a ∩ codom R = Λ →
      ¬Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) := by
  intro h hd
  simp only [desc_rlim_lmx] at hd
  exact pm233_171 (null_of_refs h) hd

/-- ✱233·424. \[\begin{align}&\vdash :\overrightarrow{Q}ʻa\cap \text{ᗡ}ʻR=\Lambda .\text{E}!R(PQ)ʻa.\text{E}!R(\breve{P} Q)ʻa.\supset .(P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa{\sim}\in 0\cup 1\\ &[*233·172]\end{align}\] -/
theorem pm233_424 {a : β} :
    (refs Q a ∩ codom R = Λ ∧ EDesc (rlim R P Q) a) ∧ EDesc (rlim R P˘ Q) a →
      osFun P R Q (refs Q a) ∉ zero ∪ one := by
  rintro ⟨⟨h, h1⟩, h2⟩
  rw [edesc_rlim_lmx] at h1 h2
  exact pm233_172 ⟨⟨null_of_refs h, h1⟩, h2⟩

/-- ✱233·425. \[\begin{align}&\vdash :(P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa\in 0\cup 1.\text{E}!R(PQ)ʻa.\text{E}!P(\breve{P} Q)ʻa.\supset .\exists !\overrightarrow{Q}ʻa\cap \text{ᗡ}ʻR\\ &[*233·424.\text{Transp}]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `E!P(P̆Q)'a` for
`E!R(P̆Q)'a`. -/
theorem pm233_425 {a : β} :
    (osFun P R Q (refs Q a) ∈ zero ∪ one ∧ EDesc (rlim R P Q) a) ∧ EDesc (rlim R P˘ Q) a →
      (refs Q a ∩ codom R).Nonempty := by
  intro h
  by_contra hn
  exact pm233_424 ⟨⟨eq_null_of fun y hy => hn ⟨y, hy⟩, h.1.2⟩, h.2⟩ h.1.1

/-- ✱233·426. \(\vdash :P\,\unicode{x2abd}\, J.(P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa\in 1.\supset .\exists !\overrightarrow{Q}ʻa\cap \text{ᗡ}ʻR \quad[*233·174]\) -/
theorem pm233_426 {a : β} :
    P ⪽ J ∧ osFun P R Q (refs Q a) ∈ one → (refs Q a ∩ codom R).Nonempty := by
  intro h
  obtain ⟨y, ⟨⟨h1, _⟩, h3⟩⟩ := pm233_174 h
  exact ⟨y, h1, h3⟩

/-- ✱233·43. \[\begin{align}\vdash :P_{\text{po}}\in \text{Ser}.&(P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa\in 1.\supset.\\ &R(PQ)ʻa = R(\breve{P} Q)ʻa = \breve{\iota} ʻ(P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻ\alpha \quad[*231·193]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `Q⃗'α` for `Q⃗'a` at the
end. The chain of three is the conjunction of its two links. -/
theorem pm233_43 {a : β} :
    po P ∈ Ser ∧ osFun P R Q (refs Q a) ∈ one →
      Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ∧
        Desc (rlim R P˘ Q) a
          (fun s => Desc iota˘ (osFun P R Q (refs Q a)) (fun c => s = c)) := by
  rintro ⟨hS, h1⟩
  obtain ⟨x0, hx0⟩ := mem_one_iff.1 h1
  obtain ⟨ha, hb⟩ := os_one_lmx (Q' := anc Q ⥏ refs Q a) hS hx0
  have ha' : ∀ b, rlim R P Q b a ↔ b = x0 := fun b => rlim_apply.trans (ha b)
  have hb' : ∀ b, rlim R P˘ Q b a ↔ b = x0 := fun b => rlim_apply.trans (hb b)
  refine ⟨eqDesc ha' hb', (TheIs_iff_of_unique hb').2 ?_⟩
  rw [desc_iota_cnv]
  exact (TheIs_iff_of_unique hx0).2 rfl

/-- Two members `u ≠ w` of a class not in `0 ∪ 1`. -/
private theorem two_of_not_zero_one {X : Set α} (h : X ∉ zero ∪ one) :
    ∃ u w, (u ∈ X ∧ w ∈ X) ∧ u ≠ w := by
  by_contra hn
  simp only [not_exists, not_and, not_not] at hn
  apply h
  by_cases hX : X.Nonempty
  · obtain ⟨u, hu⟩ := hX
    exact Or.inr (mem_one_iff.2 ⟨u, fun z => ⟨fun hz => hn z u ⟨hz, hu⟩, fun e => e ▸ hu⟩⟩)
  · exact Or.inl (show X = Λ from eq_null_of fun x hx => hX ⟨x, hx⟩)

/-- ✱233·431. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .(P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa{\sim}\in 0\cup 1.\\ &\text{E}!R(PQ)ʻa.\text{E}!R(\breve{P} Q)ʻa.\supset .\{R(\breve{P} Q)ʻa\}P\{R(PQ)ʻa\}\\ &[*215·52.*231·13·101]\end{align}\]

`{R(P̆Q)'a} P {R(PQ)'a}`: the first description has the larger scope. -/
theorem pm233_431 {a : β} :
    ((P ∈ transR ∩ connex ∧ osFun P R Q (refs Q a) ∉ zero ∪ one) ∧ EDesc (rlim R P Q) a) ∧
        EDesc (rlim R P˘ Q) a →
      Desc (rlim R P˘ Q) a (fun s => Desc (rlim R P Q) a (fun r => P s r)) := by
  rintro ⟨⟨⟨⟨htr, hcon⟩, h2⟩, r, hr⟩, s, hs⟩
  have tr := mem_transR.1 htr
  have hcon' := mem_connex.1 hcon
  refine (TheIs_iff_of_unique hs).2 ((TheIs_iff_of_unique hr).2 ?_)
  have hr' : limaxP P r (scFun P R Q (refs Q a)) := rlim_apply.1 ((hr r).2 rfl)
  have hs' : limaxP P˘ s (scFun P˘ R Q (refs Q a)) := rlim_apply.1 ((hs s).2 rfl)
  obtain ⟨u, w, ⟨hu, hw⟩, huw⟩ := two_of_not_zero_one h2
  -- members of the limiting section are `P_*`-before `r`, members of the upper one after `s`
  have below : ∀ v, v ∈ scFun P R Q (refs Q a) → P v r ∨ v = r := by
    intro v hv
    rcases hr' with hm | ⟨hseq, -⟩
    · rw [maxP_iff] at hm
      rcases hcon' v r ⟨hv.2, hm.1.2⟩ with (h | e) | h
      · exact Or.inl h
      · exact Or.inr e
      · exact absurd h (hm.2 v hv)
    · exact Or.inl ((seqP_iff.1 hseq).1.1 v ⟨hv, hv.2⟩)
  have above : ∀ v, v ∈ scFun P˘ R Q (refs Q a) → P s v ∨ s = v := by
    intro v hv
    have hvP : v ∈ fld P := by rw [← fld_cnv P]; exact hv.2
    rcases hs' with hm | ⟨hseq, -⟩
    · rw [maxP_iff, fld_cnv] at hm
      rcases hcon' v s ⟨hvP, hm.1.2⟩ with (h | e) | h
      · exact absurd h (hm.2 v hv)
      · exact Or.inr e.symm
      · exact Or.inl h
    · rw [seqP_iff, fld_cnv] at hseq
      exact Or.inl (hseq.1.1 v ⟨hv, hvP⟩)
  have key : ∀ u w, u ∈ osFun P R Q (refs Q a) → w ∈ osFun P R Q (refs Q a) → P u w → P s r := by
    intro u w hu hw huw
    have h1 : P s w := by
      rcases above u hu.2 with h | e
      · exact tr s u w ⟨h, huw⟩
      · exact e ▸ huw
    rcases below w hw.1 with h | e
    · exact tr s w r ⟨h1, h⟩
    · exact e ▸ h1
  have huP : u ∈ fld P := hu.1.2
  have hwP : w ∈ fld P := hw.1.2
  rcases hcon' u w ⟨huP, hwP⟩ with (h | e) | h
  · exact key u w hu hw h
  · exact absurd e huw
  · exact key w u hw hu h

/-- ✱233·432. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .(P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa=\Lambda .\\ &\text{E}!R(PQ)ʻa.\text{E}!R(\breve{P} Q)ʻa.\supset .\{R(PQ)ʻa\}P_{*}\{R(\breve{P} Q)ʻa\} \quad[*215·53]\end{align}\] -/
theorem pm233_432 {a : β} :
    ((P ∈ transR ∩ connex ∧ osFun P R Q (refs Q a) = Λ) ∧ EDesc (rlim R P Q) a) ∧
        EDesc (rlim R P˘ Q) a →
      Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => anc P r s)) := by
  rintro ⟨⟨⟨⟨htr, hcon⟩, h0⟩, r, hr⟩, s, hs⟩
  have tr := mem_transR.1 htr
  have hcon' := mem_connex.1 hcon
  refine (TheIs_iff_of_unique hr).2 ((TheIs_iff_of_unique hs).2 ?_)
  have hr' : limaxP P r (scFun P R Q (refs Q a)) := rlim_apply.1 ((hr r).2 rfl)
  have hs' : limaxP P˘ s (scFun P˘ R Q (refs Q a)) := rlim_apply.1 ((hs s).2 rfl)
  set A := scFun P R Q (refs Q a)
  set B := scFun P˘ R Q (refs Q a)
  have hdisj : ∀ v, v ∈ A → v ∉ B := fun v h1 h2 => by
    have : v ∈ osFun P R Q (refs Q a) := ⟨h1, h2⟩
    rw [h0] at this
    exact not_mem_null this
  have hrP : r ∈ fld P := by
    rcases hr' with hm | ⟨hseq, -⟩
    · exact (maxP_iff.1 hm).1.2
    · exact (seqP_iff.1 hseq).1.2
  have hsP : s ∈ fld P := by
    rcases hs' with hm | ⟨hseq, -⟩
    · rw [← fld_cnv P]
      exact (maxP_iff.1 hm).1.2
    · rw [← fld_cnv P]
      exact (seqP_iff.1 hseq).1.2
  -- every member of `B` follows every member of `A`
  have F : ∀ v w, v ∈ A → w ∈ B → P v w := by
    intro v w hv hw
    have hwP : w ∈ fld P := by rw [← fld_cnv P]; exact hw.2
    rcases hcon' v w ⟨hv.2, hwP⟩ with (h | e) | h
    · exact h
    · exact absurd (e ▸ hw) (hdisj v hv)
    · exact absurd (scBar_down hv (anc_of h)) (hdisj w · hw)
  suffices hn : ¬P s r by
    rcases hcon' r s ⟨hrP, hsP⟩ with (h | e) | h
    · exact anc_of h
    · exact e ▸ anc_rfl hrP
    · exact absurd h hn
  intro hsr
  rcases hr' with hm | ⟨hseq, hnm⟩ <;> rcases hs' with hm' | ⟨hseq', hnm'⟩
  · rw [maxP_iff] at hm hm'
    exact hdisj s (scBar_down hm.1.1 (anc_of hsr)) hm'.1.1
  · -- `r` is a lower bound of `B`; `s` is the greatest lower bound
    rw [seqP_iff, fld_cnv] at hseq'
    rw [maxP_iff] at hm
    exact hseq'.2 r (fun v hv => F r v hm.1.1 hv.1) hsr
  · rw [maxP_iff, fld_cnv] at hm'
    rw [seqP_iff] at hseq
    exact hseq.2 s (fun v hv => F v s hv.1 hm'.1.1) hsr
  · rw [seqP_iff] at hseq
    rw [seqP_iff, fld_cnv] at hseq'
    -- no member of `B` precedes `r`; so `r` is a lower bound of `B` or the minimum of `B`
    have hlow : ∀ v, v ∈ B ∩ fld P → P r v := by
      intro v ⟨hv, hvP⟩
      rcases hcon' r v ⟨hrP, hvP⟩ with (h | e) | h
      · exact h
      · subst e
        exfalso
        refine hnm' ⟨r, ?_⟩
        rw [maxP_iff, fld_cnv]
        refine ⟨⟨hv, hrP⟩, fun w hw hwr => ?_⟩
        exact hseq.2 w (fun u hu => F u w hu.1 hw) hwr
      · exact absurd h (hseq.2 v (fun u hu => F u v hu.1 hv))
    exact hseq'.2 r hlow hsr

/-- ✱233·433. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa\in \text{connex} .Rʻʻ\overrightarrow{Q}ʻa\subset\\ &CʻP.(P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa=\Lambda . \text{E}!R(PQ)ʻa.\text{E}!R(\breve{P} Q)ʻa.\supset :R(PQ)ʻa=R(\breve{P} Q)ʻa.\lor.\{R(PQ)ʻa\}P_1\{R(\breve{P} Q)ʻa\}\\ &[*215·54.*232·22]\end{align}\] -/
theorem pm233_433 {a : β} :
    (((((P ∈ Ser ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
            osFun P R Q (refs Q a) = Λ) ∧ EDesc (rlim R P Q) a) ∧ EDesc (rlim R P˘ Q) a) →
      Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ∨
        Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => P1 P r s)) := by
  rintro ⟨⟨⟨⟨⟨hS, hcQ⟩, hR⟩, h0⟩, r, hr⟩, -⟩
  have hU := (pm232_22 (S := refs Q a) ⟨⟨connex_anc (Ser_connex hS), hcQ⟩,
    fun v ⟨y, hy, hvy⟩ => hR ⟨y, hy.1, hvy⟩⟩).symm
  have hr' : ∀ b, limaxP P b (scFun P R Q (refs Q a)) ↔ b = r :=
    fun b => rlim_apply.symm.trans (hr b)
  have key : ∀ n, (∀ b, liminP P b (scFun P˘ R Q (refs Q a)) ↔ b = n) →
      ∀ b, rlim R P˘ Q b a ↔ b = n := by
    intro n h b
    rw [rlim_apply, ← liminP_eq_limaxP_cnv]
    exact h b
  rcases cut_limax hS pm231_13 (compl_of_os_null hU h0) ((hr' r).2 rfl) with h | ⟨n, h, hP1⟩
  · exact Or.inl (eqDesc hr (key r h))
  · exact Or.inr ((TheIs_iff_of_unique hr).2 ((TheIs_iff_of_unique (key n h)).2 hP1))

/-- ✱233·434. \[\begin{align}&\vdash :P\in \text{Ser}.Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa\in \text{connex} .Rʻʻ\overrightarrow{Q}ʻa\subset CʻP.\text{E}!R(PQ)ʻa.\\ &\text{E}!R(\breve{P} Q)ʻa.\supset .\{R(PQ)ʻa\}(P_1\unicode{x228d} \breve{P} _*)\{R(\breve{P} Q)ʻa\} \quad[*233·43·431·433]\end{align}\]

`P_1 ∪̇ P̆_*` is `P1 P ⊍ ancCnv P` (`P̆_*` is `Cnv'P_*`, ✱90·02). -/
theorem pm233_434 {a : β} :
    ((((P ∈ Ser ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
          EDesc (rlim R P Q) a) ∧ EDesc (rlim R P˘ Q) a) →
      Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => (P1 P ⊍ ancCnv P) r s)) := by
  rintro ⟨⟨⟨⟨hS, hcQ⟩, hR⟩, ⟨r, hr⟩⟩, ⟨s, hs⟩⟩
  refine (TheIs_iff_of_unique hr).2 ((TheIs_iff_of_unique hs).2 ?_)
  have hpo : po P ∈ Ser := by
    rw [po_eq_of_transR (Ser_transR hS)]
    exact hS
  by_cases h01 : osFun P R Q (refs Q a) ∈ zero ∪ one
  · rcases h01 with h0 | h1
    · rcases pm233_433 ⟨⟨⟨⟨⟨hS, hcQ⟩, hR⟩, (h0 : _ = Λ)⟩, ⟨r, hr⟩⟩, ⟨s, hs⟩⟩ with h | h
      · have e := (TheIs_iff_of_unique hs).1 ((TheIs_iff_of_unique hr).1 h)
        subst e
        right
        have hrP : r ∈ fld P := by
          rcases rlim_apply.1 ((hr r).2 rfl) with hm | ⟨hseq, -⟩
          · exact (maxP_iff.1 hm).1.2
          · exact (seqP_iff.1 hseq).1.2
        exact anc_rfl hrP
      · exact Or.inl ((TheIs_iff_of_unique hs).1 ((TheIs_iff_of_unique hr).1 h))
    · have h := (pm233_43 ⟨hpo, h1⟩).1
      have e := (TheIs_iff_of_unique hs).1 ((TheIs_iff_of_unique hr).1 h)
      subst e
      right
      have hrP : r ∈ fld P := by
        rcases rlim_apply.1 ((hr r).2 rfl) with hm | ⟨hseq, -⟩
        · exact (maxP_iff.1 hm).1.2
        · exact (seqP_iff.1 hseq).1.2
      exact anc_rfl hrP
  · have h := pm233_431 ⟨⟨⟨⟨Ser_transR hS, Ser_connex hS⟩, h01⟩, ⟨r, hr⟩⟩, ⟨s, hs⟩⟩
    have hsr := (TheIs_iff_of_unique hr).1 ((TheIs_iff_of_unique hs).1 h)
    exact Or.inr (anc_of hsr)

/-- ✱233·435. \[\begin{align}&\vdash :P\in \text{Ser}.R(PQ)ʻa=R(\breve{P} Q)ʻa.\supset .(P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa\in 0\cup 1\\ &[*233·431.\text{Transp}]\end{align}\] -/
theorem pm233_435 {a : β} :
    P ∈ Ser ∧ Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) →
      osFun P R Q (refs Q a) ∈ zero ∪ one := by
  rintro ⟨hS, hd⟩
  by_contra h01
  obtain ⟨r, hr, s, hs, e⟩ := hd
  have h := pm233_431 ⟨⟨⟨⟨Ser_transR hS, Ser_connex hS⟩, h01⟩, ⟨r, hr⟩⟩, ⟨s, hs⟩⟩
  have hsr := (TheIs_iff_of_unique hr).1 ((TheIs_iff_of_unique hs).1 h)
  subst e
  exact (Ser_parts hS).1.1 r hsr

/-- ✱233·44. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa\in \text{connex} .Rʻʻ\overrightarrow{Q}ʻa\subset CʻP.\text{E}!R(PQ)ʻa.\\ &\text{E}!R(\breve{P} Q)ʻa.{\sim}{R(PQ)ʻa\in \text{D}ʻP_1.R(\breve{P} Q)ʻa\in \text{ᗡ}ʻP_1}.\supset :\\ &R(PQ)ʻa=R(\breve{P} Q)ʻa.\equiv .(P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa\in 0\cup 1 \quad[*233·426·43·433·435]\end{align}\] -/
theorem pm233_44 {a : β} :
    (((((P ∈ Ser ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
            EDesc (rlim R P Q) a) ∧ EDesc (rlim R P˘ Q) a) ∧
          ¬(Desc (rlim R P Q) a (fun r => r ∈ dom (P1 P)) ∧
            Desc (rlim R P˘ Q) a (fun s => s ∈ codom (P1 P)))) →
      (Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ↔
        osFun P R Q (refs Q a) ∈ zero ∪ one) := by
  rintro ⟨⟨⟨⟨⟨hS, hcQ⟩, hR⟩, ⟨r, hr⟩⟩, ⟨s, hs⟩⟩, hn⟩
  refine ⟨fun h => pm233_435 ⟨hS, h⟩, fun h01 => ?_⟩
  rcases h01 with h0 | h1
  · rcases pm233_433 ⟨⟨⟨⟨⟨hS, hcQ⟩, hR⟩, (h0 : _ = Λ)⟩, ⟨r, hr⟩⟩, ⟨s, hs⟩⟩ with h | h
    · exact h
    · have hP1 := (TheIs_iff_of_unique hs).1 ((TheIs_iff_of_unique hr).1 h)
      exact absurd ⟨(TheIs_iff_of_unique hr).2 ⟨s, hP1⟩, (TheIs_iff_of_unique hs).2 ⟨r, hP1⟩⟩ hn
  · have hpo : po P ∈ Ser := by
      rw [po_eq_of_transR (Ser_transR hS)]
      exact hS
    exact (pm233_43 ⟨hpo, h1⟩).1

/-- ✱233·45. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}\cap \text{Ded}.P^{2}&=P.Q_{*}\in \text{connex} .RʻʻCʻQ\subset CʻP.\supset :\\ &R(PQ)ʻa=R(\breve{P} Q)ʻa.\equiv _a.(P\overline{R}Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa\in 0\cup 1\\ &[*233·13.*201·65.*233·44]\end{align}\]

`≡_a` is `∀ a`. -/
theorem pm233_45 :
    ((P ∈ Ser ∩ Ded ∧ rsq P = P) ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      ∀ a : β, (Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ↔
        osFun P R Q (refs Q a) ∈ zero ∪ one) := by
  rintro ⟨⟨⟨⟨hS, hD⟩, hd⟩, hcQ⟩, hR⟩ a
  refine ⟨fun h => pm233_435 ⟨hS, h⟩, fun h01 => ?_⟩
  have h := pm233_16 ⟨⟨⟨⟨hS, hD⟩, hd⟩, hcQ⟩, hR⟩ (refs Q a) h01
  simp only [desc_rlim_lmx]
  exact h

/-- ✱233·5. \(\vdash :Q\in \text{Ser}.a=\text{lt}_Qʻ(\alpha \cap \text{ᗡ}ʻR).\supset .\overrightarrow{Q}ʻa=Q_{*}ʻʻ(\alpha \cap \text{ᗡ}ʻR) \quad[*207·291]\)

`a = lt_Q'(α ∩ ᗡ'R)` is `Desc (ltP Q) (S ∩ codom R) (fun l => a = l)`. -/
theorem pm233_5 {S : Set β} {a : β} :
    Q ∈ Ser ∧ Desc (ltP Q) (S ∩ codom R) (fun l => a = l) →
      refs Q a = anc Q ʻʻ (S ∩ codom R) := by
  rintro ⟨hS, l, hl, e⟩
  subst e
  have hlt : ltP Q a (S ∩ codom R) := (hl a).2 rfl
  obtain ⟨⟨hirr, htr⟩, hcon⟩ := Ser_parts hS
  obtain ⟨hseq, hnm⟩ := hlt
  rw [seqP_iff] at hseq
  obtain ⟨⟨hup, haQ⟩, hleast⟩ := hseq
  ext u
  constructor
  · intro hu
    by_contra hn
    refine hleast u (fun v ⟨hvS, hvQ⟩ => ?_) hu
    rcases hcon v u hvQ (fld_of_left hu) with (h | e) | h
    · exact h
    · subst e
      exact absurd ⟨v, hvS, anc_rfl hvQ⟩ hn
    · exact absurd ⟨v, hvS, anc_of h⟩ hn
  · rintro ⟨v, hv, huv⟩
    have hvQ : v ∈ fld Q := anc_right huv
    rcases anc_iff_po.1 huv with ⟨e, -⟩ | hp
    · exact e ▸ hup v ⟨hv, hvQ⟩
    · rw [po_eq_of_transR (Ser_transR hS)] at hp
      exact htr u v a hp (hup v ⟨hv, hvQ⟩)

/-- ✱233·501. \(\vdash \colon\ldotp Q\in \text{Ser}.\alpha=\text{lt}_{Q}ʻ(\alpha \cap \text{ᗡ}ʻR).\supset :\exists !\overrightarrow{Q}ʻa\cap \text{ᗡ}ʻR.\equiv .\exists !\alpha \cap CʻQ\cap \text{ᗡ}ʻR\)

**Status.** proved (reading): transcription error: the e-text prints `α = lt_Q'(α ∩ ᗡ'R)` for
`a = lt_Q'(α ∩ ᗡ'R)` (the hypothesis of ✱233·5). -/
theorem pm233_501 {S : Set β} {a : β} :
    Q ∈ Ser ∧ Desc (ltP Q) (S ∩ codom R) (fun l => a = l) →
      ((refs Q a ∩ codom R).Nonempty ↔ (S ∩ fld Q ∩ codom R).Nonempty) := by
  intro h
  rw [pm233_5 h]
  constructor
  · rintro ⟨u, ⟨v, ⟨hvS, hvR⟩, huv⟩, -⟩
    exact ⟨v, ⟨hvS, anc_right huv⟩, hvR⟩
  · rintro ⟨v, ⟨hvS, hvQ⟩, hvR⟩
    exact ⟨v, ⟨v, ⟨hvS, hvR⟩, anc_rfl hvQ⟩, hvR⟩

private theorem connex_ancFres_of {S : Set β} (hQ : Q ∈ connex) : anc Q ⥏ S ∈ connex :=
  connex_ancFres (connex_anc hQ)

/-- ✱233·51. \[\begin{align}\vdash :\text{Hp}*233·5.&P\in \text{Ser}.Rʻʻ(\alpha \cap CʻQ)\subset CʻP.(P\overline{R} Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa=\Lambda .\\ &\text{E}!R(PQ)ʻ\alpha.\supset .(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =R(PQ)ʻ\alpha \quad[*233·2·5]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `E!R(PQ)'α` and `R(PQ)'α`
for `E!R(PQ)'a` and `R(PQ)'a` (`a` of ✱233·5). -/
theorem pm233_51 {S : Set β} {a : β} :
    ((((Q ∈ Ser ∧ Desc (ltP Q) (S ∩ codom R) (fun l => a = l)) ∧ P ∈ Ser) ∧
          R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧ osFun P R Q (refs Q a) = Λ) ∧ EDesc (rlim R P Q) a →
      Desc (lmx P R Q) S (fun l => Desc (rlim R P Q) a (fun r => l = r)) := by
  rintro ⟨⟨⟨⟨hQa, hS⟩, hR⟩, h0⟩, hE⟩
  have e := pm233_5 hQa
  rw [edesc_rlim_lmx, e] at hE
  rw [e] at h0
  have h2 := (pm233_2 ⟨⟨⟨⟨connex_ancFres_of (Ser_connex hQa.1), hS⟩, hR⟩, h0⟩, hE⟩).1
  simp only [desc_rlim_lmx, e]
  exact h2

/-- ✱233·511. \[\begin{align}&\vdash :\text{Hp}*233·5.P\in \text{Ser}.\exists !(P\overline{R} Q)_{\text{os}}ʻ\alpha .(P\overline{R} Q)_{\text{os}}ʻ\overrightarrow{Q}ʻ\alpha\in 1.\supset .\\ &(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha =R(PQ)ʻa=R(\breve{P} Q)ʻa=\breve{\iota} ʻ(P\overline{R} Q)_{\text{os}}ʻ\overrightarrow{Q}ʻ\alpha\\ &[*233·501·5·21]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `Q⃗'α` for `Q⃗'a` (twice).
The chain of five is the conjunction of its four links. -/
theorem pm233_511 {S : Set β} {a : β} :
    (((Q ∈ Ser ∧ Desc (ltP Q) (S ∩ codom R) (fun l => a = l)) ∧ P ∈ Ser) ∧
          (osFun P R Q S).Nonempty) ∧ osFun P R Q (refs Q a) ∈ one →
      ((Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => l = m)) ∧
          Desc (lmx P˘ R Q) S (fun m => Desc (rlim R P Q) a (fun r => m = r))) ∧
          Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s))) ∧
        Desc (rlim R P˘ Q) a (fun s => Desc iota˘ (osFun P R Q (refs Q a)) (fun c => s = c)) := by
  rintro ⟨⟨⟨hQa, hS⟩, hne⟩, h1⟩
  have e := pm233_5 hQa
  have hpo : po P ∈ Ser := by
    rw [po_eq_of_transR (Ser_transR hS)]
    exact hS
  rw [e] at h1 ⊢
  have h := pm233_21 ⟨⟨hpo, hne⟩, h1⟩
  simp only [desc_rlim_lmx, e]
  exact h

/-- ✱233·512. \[\begin{align}&\vdash \colon\ldotp \text{Hp}*233·5.P\in \text{Ser}.Rʻʻ(\alpha \cap CʻQ)\subset CʻP.(P\overline{R} Q)_{\text{os}}ʻ\overrightarrow{Q}ʻ\alpha=\iota ʻx.\supset :\\ &x=R(PQ)ʻ\alpha=R(\breve{P} Q)ʻ\alpha:x=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\lor.(P\overline{R} Q)_{\text{lmx}}ʻ\alpha P_{1}x\\ &[*233·22·23.*232·22]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `Q⃗'α`, `R(PQ)'α` and
`R(P̆Q)'α` for `Q⃗'a`, `R(PQ)'a` and `R(P̆Q)'a` (`a` of ✱233·5; the Summary of ✱233 prints `a`
in the same formula). -/
theorem pm233_512 {S : Set β} {a : β} {x : α} :
    (((Q ∈ Ser ∧ Desc (ltP Q) (S ∩ codom R) (fun l => a = l)) ∧ P ∈ Ser) ∧
        R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧ osFun P R Q (refs Q a) = ι x →
      (Desc (rlim R P Q) a (fun r => x = r) ∧
          Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s))) ∧
        (Desc (lmx P R Q) S (fun l => x = l) ∨ Desc (lmx P R Q) S (fun l => P1 P l x)) := by
  rintro ⟨⟨⟨hQa, hS⟩, hR⟩, hos⟩
  have e := pm233_5 hQa
  rw [e] at hos
  have hU := (pm232_22 ⟨⟨connex_anc (Ser_connex hS), connex_ancFres_of (Ser_connex hQa.1)⟩,
    hR⟩).symm
  have h23 := pm233_23 ⟨⟨hS, hos⟩, hU⟩
  have h22 := pm233_22 ⟨⟨hS, hos⟩, hU⟩
  simp only [desc_rlim_lmx, e]
  exact ⟨h23, h22.imp id fun h => h.1⟩

/-- ✱233·513. \(\vdash :\text{Hp}*233·512.x{\sim}\in \text{ᗡ}ʻP_{1}.\supset .x=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha \quad[*233·512]\)

**Status.** proved (reading): "Hp ✱233·512" is read as in ✱233·512, with `Q⃗'a` for the
printed `Q⃗'α`. -/
theorem pm233_513 {S : Set β} {a : β} {x : α} :
    ((((Q ∈ Ser ∧ Desc (ltP Q) (S ∩ codom R) (fun l => a = l)) ∧ P ∈ Ser) ∧
        R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧ osFun P R Q (refs Q a) = ι x) ∧ x ∉ codom (P1 P) →
      Desc (lmx P R Q) S (fun l => x = l) := by
  rintro ⟨⟨⟨⟨hQa, hS⟩, hR⟩, hos⟩, hx1⟩
  have e := pm233_5 hQa
  rw [e] at hos
  have hU := (pm232_22 ⟨⟨connex_anc (Ser_connex hS), connex_ancFres_of (Ser_connex hQa.1)⟩,
    hR⟩).symm
  exact pm233_24 ⟨⟨⟨hS, hos⟩, hU⟩, hx1⟩

/-- ✱233·514. \[\begin{align}&\vdash :\text{Hp}*233·512.x{\sim}\in CʻP_{1}.\supset .x=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha \\ &\left[*233·513\frac{\breve{P}}{P}.*233·513\right]\end{align}\]

**Status.** proved (reading): "Hp ✱233·512" is read as in ✱233·512, with `Q⃗'a` for the
printed `Q⃗'α`. -/
theorem pm233_514 {S : Set β} {a : β} {x : α} :
    ((((Q ∈ Ser ∧ Desc (ltP Q) (S ∩ codom R) (fun l => a = l)) ∧ P ∈ Ser) ∧
        R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧ osFun P R Q (refs Q a) = ι x) ∧ x ∉ fld (P1 P) →
      Desc (lmx P R Q) S (fun l => x = l) ∧
        Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => l = m)) := by
  rintro ⟨⟨⟨⟨hQa, hS⟩, hR⟩, hos⟩, hx1⟩
  have e := pm233_5 hQa
  rw [e] at hos
  have hU := (pm232_22 ⟨⟨connex_anc (Ser_connex hS), connex_ancFres_of (Ser_connex hQa.1)⟩,
    hR⟩).symm
  exact pm233_241 ⟨⟨⟨hS, hos⟩, hU⟩, hx1⟩

/-- ✱233·515. \[\begin{align}\vdash :P,Q&\in \text{Ser}.a=\text{lt}_{Q}ʻ(\alpha \cap \text{ᗡ}ʻR).Rʻʻ(CʻQ\cap \alpha )\subset CʻP.\\ &(P\overline{R} Q)_{\text{os}}ʻ\overrightarrow{Q}ʻ\alpha\in 0\cup 1.\text{E}!R(PQ)ʻ\alpha.R(PQ)ʻ\alpha{\sim}\in CʻP_{1}.\supset .\\ &(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha =R(PQ)ʻ\alpha=R(\breve{P} Q)ʻ\alpha\\ &[*233·142·5]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `Q⃗'α`, `E!R(PQ)'α`,
`R(PQ)'α` and `R(P̆Q)'α` for `Q⃗'a`, `E!R(PQ)'a`, `R(PQ)'a`, `R(P̆Q)'a`. `P, Q ∈ Ser` is
`P ∈ Ser ∧ Q ∈ Ser`. The chain of four is the conjunction of its three links. -/
theorem pm233_515 {S : Set β} {a : β} :
    (((((P ∈ Ser ∧ Q ∈ Ser) ∧ Desc (ltP Q) (S ∩ codom R) (fun l => a = l)) ∧
            R ʻʻ (fld Q ∩ S) ⊆ fld P) ∧ osFun P R Q (refs Q a) ∈ zero ∪ one) ∧
          EDesc (rlim R P Q) a) ∧ Desc (rlim R P Q) a (fun r => r ∉ fld (P1 P)) →
      (Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => l = m)) ∧
          Desc (lmx P˘ R Q) S (fun m => Desc (rlim R P Q) a (fun r => m = r))) ∧
        Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) := by
  rintro ⟨⟨⟨⟨⟨⟨hS, hQ⟩, hlt⟩, hR⟩, h01⟩, hE⟩, hd⟩
  have e := pm233_5 ⟨hQ, hlt⟩
  have hR' : R ʻʻ (S ∩ fld Q) ⊆ fld P := by
    rw [Set.inter_comm]
    exact hR
  rw [e] at h01
  rw [edesc_rlim_lmx, e] at hE
  rw [desc_rlim_lmx, e] at hd
  have h := pm233_142 ⟨⟨⟨⟨⟨hS, connex_ancFres_of (Ser_connex hQ)⟩, hR'⟩, h01⟩, hE⟩, hd⟩
  simp only [desc_rlim_lmx, e]
  exact h

/-- ✱233·516. \[\begin{align}\vdash :P,Q&\in \text{Ser}.\text{E}!R(PQ)ʻ\text{lt}_{Q}ʻ\alpha .R(PQ)ʻ\text{lt}_{Q}ʻ\alpha {\sim}\in CʻP_{1}.\\ &Rʻʻ(CʻQ\cap \alpha )\subset CʻP.(P\overline{R} Q)_{\text{os}}ʻ\overrightarrow{Q}ʻ\text{lt}_{Q}ʻ\alpha \in 0\cup 1.\supset .\\ &(P\overline{R} Q)_{\text{lmx}}ʻ\alpha = (\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha = R(PQ)ʻ\text{lt}_{Q}ʻ\alpha = R(\breve{P} Q)ʻ\text{lt}_{Q}ʻ\alpha \\ &[*233·515]\end{align}\]

**Status.** proved (corrected): false as printed. With `a = lt_Q'α`, `Q⃗'a` is `Q_*''α`, which
determines the same limiting sections as `α` only when the arguments in `α` having values do not
stop short of `a`; the reference ✱233·515 has `a = lt_Q'(α ∩ ᗡ'R)`. Counterexample (series of
rationals, `P = Q`): `α = ẑ(−1 < z ≤ −1/2) ∪ ẑ(z = −1/(2n+1))`, `ᗡ'R = ẑ(−1 < z ≤ −1/2) ∪
ẑ(z = −1/(2n))` (`n ≥ 1`), `R'(−1/2) = 5`, `R'z = 0` elsewhere: then `lt_Q'α = 0`,
`R(PQ)'0 = 0 ∼∈ C'P_1`, `(P R̄ Q)_os'Q⃗'0 = ι'0`, but `(P R̄ Q)_lmx'α = 5`. `lt_Q'α` is read
`lt_Q'(α ∩ ᗡ'R)` throughout (as in the reference ✱233·515, and as ✱234·562 uses this
proposition); no hypothesis is added. (When `α ⊂ ᗡ'R`, as in ✱233·53, the two coincide.)
`R(PQ)'lt_Q'(α ∩ ᗡ'R)` is the double description `Desc2 (rlim R P Q) (ltP Q) (S ∩ codom R) ψ`. -/
theorem pm233_516 {S : Set β} :
    (((((P ∈ Ser ∧ Q ∈ Ser) ∧ Desc (ltP Q) (S ∩ codom R) (fun a => EDesc (rlim R P Q) a)) ∧
            Desc2 (rlim R P Q) (ltP Q) (S ∩ codom R) (fun r => r ∉ fld (P1 P))) ∧
          R ʻʻ (fld Q ∩ S) ⊆ fld P) ∧
        Desc (ltP Q) (S ∩ codom R) (fun a => osFun P R Q (refs Q a) ∈ zero ∪ one)) →
      (Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => l = m)) ∧
          Desc (lmx P˘ R Q) S
            (fun m => Desc2 (rlim R P Q) (ltP Q) (S ∩ codom R) (fun r => m = r))) ∧
        Desc2 (rlim R P Q) (ltP Q) (S ∩ codom R)
          (fun r => Desc2 (rlim R P˘ Q) (ltP Q) (S ∩ codom R) (fun s => r = s)) := by
  rintro ⟨⟨⟨⟨⟨hS, hQ⟩, a, ha, hE⟩, hd⟩, hR⟩, h01⟩
  have hd' := (TheIs_iff_of_unique ha).1 ((desc2_iff _ _ _ _).1 hd)
  have h01' := (TheIs_iff_of_unique ha).1 h01
  have hlt : Desc (ltP Q) (S ∩ codom R) (fun l => a = l) := (TheIs_iff_of_unique ha).2 rfl
  have h := pm233_515 ⟨⟨⟨⟨⟨⟨hS, hQ⟩, hlt⟩, hR⟩, h01'⟩, hE⟩, hd'⟩
  simp only [desc2_iff, Desc, TheIs_iff_of_unique ha]
  exact h

private theorem rlim_val {P : α → α → Prop} {a : β} {v : α}
    (h : ∀ b, limaxP P b (scFun P R Q (refs Q a)) ↔ b = v) (b : α) : rlim R P Q b a ↔ b = v :=
  rlim_apply.trans (h b)

private theorem rlimc_val {P : α → α → Prop} {a : β} {v : α}
    (h : ∀ b, liminP P b (scFun P˘ R Q (refs Q a)) ↔ b = v) (b : α) :
    rlim R P˘ Q b a ↔ b = v := by
  rw [rlim_apply, ← liminP_eq_limaxP_cnv]
  exact h b

/-- ✱233·52. \[\begin{align}\vdash \colon\ldotp &\text{Hp}*233·5.P\in \text{Ser}\cap \text{Ded}.P^{2}=P.RʻʻCʻQ\subset CʻP.\supset :\\ &(P\overline{R} Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa\in 0\cup 1.\supset .\\ &(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha =R(PQ)ʻ\alpha=R(\breve{P} Q)ʻa \quad[*233·25]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `R(PQ)'α` for `R(PQ)'a`.
The chain of four is the conjunction of its three links. -/
theorem pm233_52 {S : Set β} {a : β} :
    (((Q ∈ Ser ∧ Desc (ltP Q) (S ∩ codom R) (fun l => a = l)) ∧ P ∈ Ser ∩ Ded) ∧
        rsq P = P) ∧ R ʻʻ fld Q ⊆ fld P →
      (osFun P R Q (refs Q a) ∈ zero ∪ one →
        (Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => l = m)) ∧
            Desc (lmx P˘ R Q) S (fun m => Desc (rlim R P Q) a (fun r => m = r))) ∧
          Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s))) := by
  rintro ⟨⟨⟨hQa, hSD⟩, hd⟩, hR⟩ h01
  have e := pm233_5 hQa
  rw [e] at h01
  obtain ⟨l, ⟨h1, h2⟩, h3, h4⟩ :=
    dense_values ⟨⟨⟨hSD, hd⟩, connex_anc (Ser_connex hQa.1)⟩, hR⟩ S h01
  have h2' : ∀ b, limaxP P b (scFun P R Q (refs Q a)) ↔ b = l := by rw [e]; exact h2
  have h4' : ∀ b, liminP P b (scFun P˘ R Q (refs Q a)) ↔ b = l := by rw [e]; exact h4
  exact ⟨⟨eqDesc (lmx_val h1) (lmxc_val h3), eqDesc (lmxc_val h3) (rlim_val h2')⟩,
    eqDesc (rlim_val h2') (rlimc_val h4')⟩

/-- ✱233·53. \[\begin{align}\vdash :Q\in \text{Ser}.P\in &\text{Ser}\cap \text{Ded}.P^{2}=P.RʻʻCʻQ\subset CʻP.\alpha \subset \text{ᗡ}ʻR.\text{E}!\text{lt}_{Q}ʻ\alpha .\\ &(P\overline{R} Q)_{\text{os}}ʻQ_{*}ʻʻ\alpha \in 0\cup 1.\supset .\\ &(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha =R(PQ)ʻ\text{lt}_{Q}ʻ\alpha =R(\breve{P} Q)ʻ\text{lt}_{Q}ʻ\alpha\\ &[*233·52]\end{align}\]

`R(PQ)'lt_Q'α` is the double description `Desc2 (rlim R P Q) (ltP Q) S ψ` (✱30·02). The chain
of four is the conjunction of its three links. -/
theorem pm233_53 {S : Set β} :
    ((((((Q ∈ Ser ∧ P ∈ Ser ∩ Ded) ∧ rsq P = P) ∧ R ʻʻ fld Q ⊆ fld P) ∧ S ⊆ codom R) ∧
          EDesc (ltP Q) S) ∧ osFun P R Q (anc Q ʻʻ S) ∈ zero ∪ one) →
      (Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => l = m)) ∧
          Desc (lmx P˘ R Q) S (fun m => Desc2 (rlim R P Q) (ltP Q) S (fun r => m = r))) ∧
        Desc2 (rlim R P Q) (ltP Q) S
          (fun r => Desc2 (rlim R P˘ Q) (ltP Q) S (fun s => r = s)) := by
  rintro ⟨⟨⟨⟨⟨⟨hQ, hSD⟩, hd⟩, hR⟩, hSR⟩, a, ha⟩, h01⟩
  have hSS : S ∩ codom R = S := Set.inter_eq_left.2 hSR
  have hlt : Desc (ltP Q) (S ∩ codom R) (fun l => a = l) := by
    rw [hSS]
    exact (TheIs_iff_of_unique ha).2 rfl
  have e := pm233_5 ⟨hQ, hlt⟩
  rw [← hSS] at h01
  obtain ⟨l, ⟨h1, h2⟩, h3, h4⟩ :=
    dense_values ⟨⟨⟨hSD, hd⟩, connex_anc (Ser_connex hQ)⟩, hR⟩ S h01
  have h2' : ∀ b, limaxP P b (scFun P R Q (refs Q a)) ↔ b = l := by rw [e]; exact h2
  have h4' : ∀ b, liminP P b (scFun P˘ R Q (refs Q a)) ↔ b = l := by rw [e]; exact h4
  simp only [desc2_iff, Desc, TheIs_iff_of_unique ha]
  exact ⟨⟨eqDesc (lmx_val h1) (lmxc_val h3), eqDesc (lmxc_val h3) (rlim_val h2')⟩,
    eqDesc (rlim_val h2') (rlimc_val h4')⟩

/-!
## [✱234] Continuity of functions

*(Vol. 2, p. 753)*

> *Summary of* *234.
>
> In the present number we are concerned with the definition and analysis of the continuity of functions. The following definition of continuity is given by Dini [Note: *Theorie der Functionen einer veränderlichen reellen Grösse*, Chap. IV. § 30, p. 50.]:
>
> "We call it [the function] *continuous* for \(x = a\), or in the point \(a\), in which it has the value \(f(a)\), if, for every positive number \(\sigma\), different from 0 but as small as we please, there exists a positive number \({\in}\), different from 0, such that, for all values of \(\delta\) which are numerically less than \({\in}\), the difference \(f(a + \delta ) - f(a)\) is numerically less than \(\sigma\). In other words, \(f(x)\) is continuous in the point \(x =a\) where it has the value \(f(a)\), if the limit of its values to the right and left of \(a\) is the same and equal to \(f(a)\)...."
>
> …

**Lean reading.** `sc(P,Q)'R`, `os(P,Q)'R`, `ct(PQ)'R`, `contin(PQ)'R` are `scPQ P Q R`, `osPQ P Q R`,
`ct P Q R`, `contin P Q R`, and `P contin̄ Q` is `continBar P Q` (✱234·01–·05); `R'a` is a
description, `Desc R a ψ`, with the smallest scope (inside `⊃_{z,w}` when it occurs in the
antecedent). `P(z−w)` is `itvOO P z w`, `Q(y⟝a)` is `itvCO Q y a`, `Q(y⊢⊣y')` is
`itvCC Q y y'`, `Q⃡'a` is `refsRels Q a`, `P̆_po` is `po P˘` (`= (po P)˘`), `Q̆_po''ᗡ'R` is
`po Q˘ ʻʻ codom R`, `min(Q_po)` is `minP (po Q)`, `B'P` is `Desc Beg P ψ`, `0 ∪ 1 ∪ 2` is
`zero ∪ one ∪ two`, `max⃗_P`, `min⃗_P`, `limax⃗_P` are `refs (maxP P)` etc.; `R(PQ̆)` is
`rlim R P Q˘`. "Hp ✱234·N" is written out. The proofs rest on `sc(P,Q)'R = C'P − P''(P R̄_sc Q)`
(✱234·174) and on the description of `os(P,Q)'R` by the maximum of `P R̄_sc Q` and the minimum
of `P̆ R̄_sc Q` (✱234·2), then reduce ✱234·3–·562 to `Q_* ⥏ α` as in ✱232.

**Status.** proved (all propositions; ✱234·01–·05 definition; ✱234·203, ✱234·26, ✱234·3, ✱234·329,
✱234·43, ✱234·441, ✱234·521, ✱234·7 proved (reading): transcription errors; ✱234·141,
✱234·15, ✱234·562, ✱234·61, ✱234·64 proved (corrected): false as printed (✱234·562 read with
`R'lt_Q'(α ∩ ᗡ'R)`, no hypothesis added), see their docstrings)
-/

/-- ✱234·01 (Df). \(\text{sc}(P,Q)ʻR=CʻP\cap \hat{x} (\overrightarrow{P}_{\text{po}}ʻʻ\overleftarrow{P}_{\text{po}}ʻx\subset \overleftarrow{Q}_{\text{cn}}ʻR) \quad\text{Df}\) -/
theorem pm234_01 : scPQ P Q R = fld P ∩ {x | Rfwd (po P) ʻʻ rels (po P) x ⊆ rels (cn Q) R} :=
  rfl

/-- ✱234·02 (Df). \(\text{os}(P,Q)ʻR=\text{sc}(P,Q)ʻR\cap \text{sc}(\breve{P},Q)ʻR \quad\text{Df}\) -/
theorem pm234_02 : osPQ P Q R = scPQ P Q R ∩ scPQ P˘ Q R := rfl

/-- ✱234·03 (Df). \(\text{ct}(PQ)ʻR=\hat{a} \{Rʻa\in \text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}_{\text{po}}ʻa)ʻR-CʻP_{1}\} \quad\text{Df}\) -/
theorem pm234_03 :
    ct P Q R = {a | Desc R a (fun v => v ∈ osPQ P (anc Q ⥏ refs (po Q) a) R \ fld (P1 P))} :=
  rfl

/-- ✱234·04 (Df). \(\text{contin}(PQ)ʻR=\text{ct}(PQ)ʻR\cap \text{ct}(P\breve{Q})ʻR \quad\text{Df}\) -/
theorem pm234_04 : contin P Q R = ct P Q R ∩ ct P Q˘ R := rfl

/-- ✱234·05 (Df). \(P\overline{\text{contin}} Q=\hat{R} \{\exists !CʻQ\cap \text{ᗡ}ʻR.CʻQ\cap \text{ᗡ}ʻR\subset \text{contin}(PQ)ʻR\} \quad\text{Df}\) -/
theorem pm234_05 :
    continBar P Q = {R | (fld Q ∩ codom R).Nonempty ∧ fld Q ∩ codom R ⊆ contin P Q R} := rfl

/-- ✱234·1. \[\begin{align}\vdash \colon\ldotp &x\in \text{sc}(P,Q)ʻR.\equiv :x\in CʻP:xP_{\text{po}}w.\supset _{w}.RQ_{\text{cn}}(\overrightarrow{P} _{\text{pο}}ʻw):\\ &\equiv :x\in CʻP:xP_{\text{pο}}w.\supset _{w}.(\exists y).y\in CʻQ\cap \text{ᗡ}ʻR.Rʻʻ\overleftarrow{Q}_{*}ʻy\subset \overrightarrow{P}_{\text{po}}ʻw\\ &[*230·11.(*234·01)]\end{align}\]

The chain of three is the conjunction of its two links. -/
theorem pm234_1 {x : α} :
    (x ∈ scPQ P Q R ↔ x ∈ fld P ∧ ∀ w, po P x w → cn Q R (refs (po P) w)) ∧
      ((x ∈ fld P ∧ ∀ w, po P x w → cn Q R (refs (po P) w)) ↔
        x ∈ fld P ∧ ∀ w, po P x w →
          ∃ y, y ∈ fld Q ∩ codom R ∧ R ʻʻ rels (anc Q) y ⊆ refs (po P) w) :=
  ⟨mem_scPQ, Iff.rfl⟩

private theorem mem_scPQ_cnv {P : α → α → Prop} {x : α} :
    x ∈ scPQ P˘ Q R ↔ x ∈ fld P ∧ ∀ w, po P w x → cn Q R (rels (po P) w) := by
  rw [mem_scPQ, fld_cnv]
  refine and_congr Iff.rfl (forall_congr' fun w => imp_congr po_cnv ?_)
  have : refs (po P˘) w = rels (po P) w := Set.ext fun u => po_cnv
  rw [this]

private theorem poSer {P : α → α → Prop} (hS : po P ∈ Ser) :
    (∀ x, ¬po P x x) ∧ ∀ x y, x ∈ fld P → y ∈ fld P → anc P x y ∨ po P y x := by
  obtain ⟨⟨hirr, -⟩, hcon⟩ := Ser_parts hS
  rw [fld_po] at hcon
  refine ⟨hirr, fun x y hx hy => ?_⟩
  rcases hcon x y hx hy with (h | e) | h
  · exact Or.inl (anc_of_po h)
  · exact Or.inl (e ▸ anc_rfl hx)
  · exact Or.inr h

/-- ✱234·101. \(\vdash :P_{\text{po}}\in \text{Ser}.x\in \text{sc}(P,Q)ʻR.\supset .P\overline{R} _{\text{sc}}Q\subset \overrightarrow{P}_{*}ʻx\) -/
theorem pm234_101 {x : α} : po P ∈ Ser ∧ x ∈ scPQ P Q R → scBar P R Q ⊆ refs (anc P) x := by
  rintro ⟨hS, hx⟩ u hu
  obtain ⟨hirr, hcon⟩ := poSer hS
  rw [mem_scPQ] at hx
  rcases hcon u x hu.2 hx.1 with h | h
  · exact h
  · exact absurd (pm231_144 (hx.2 u h) hu) (hirr u)

private theorem scPQ_cnv_sub {x : α} (hS : po P ∈ Ser) (hx : x ∈ scPQ P˘ Q R) :
    scBar P˘ R Q ⊆ rels (anc P) x := by
  have hS' : po P˘ ∈ Ser := by
    rw [po_cnv_eq]
    exact Ser_cnv hS
  intro u hu
  exact anc_cnv.1 (pm234_101 (P := P˘) ⟨hS', hx⟩ hu)

/-- ✱234·102. \(\vdash :P_{\text{po}}\in \text{Ser}.x\in \text{os}(P,Q)ʻR.\supset .P\overline{R} _{\text{os}}Q\subset \iota ʻx\) -/
theorem pm234_102 {x : α} : po P ∈ Ser ∧ x ∈ osPQ P Q R → osBar P R Q ⊆ ι x := by
  rintro ⟨hS, hx1, hx2⟩ u ⟨hu1, hu2⟩
  have h1 := pm234_101 ⟨hS, hx1⟩ hu1
  have h2 := scPQ_cnv_sub hS hx2 hu2
  rcases anc_iff_po.1 h1 with ⟨e, -⟩ | hp
  · exact e
  · exact absurd (po_anc_trans hp h2) ((poSer hS).1 u)

/-- ✱234·103. \(\vdash :P_{\text{po}}\in \text{Ser}.\exists !\text{os}(P,Q)ʻR.\supset .P\overline{R} _{\text{os}}Q\in 0\cup 1\) -/
theorem pm234_103 : po P ∈ Ser ∧ (osPQ P Q R).Nonempty → osBar P R Q ∈ zero ∪ one :=
  fun ⟨hS, x, hx⟩ => zero_one_mono (pm234_102 ⟨hS, hx⟩) (Or.inr ⟨x, rfl⟩)

/-- ✱234·104. \(\vdash :RQ_{\text{cn}}(\overrightarrow{P}_{*}ʻx).\supset .x\in \text{sc}(P,Q)ʻR\) -/
theorem pm234_104 {x : α} : cn Q R (refs (anc P) x) → x ∈ scPQ P Q R := by
  intro h
  obtain ⟨y, ⟨hyQ, v, hv⟩, hy⟩ := id h
  have hvx : anc P v x := hy ⟨y, anc_rfl hyQ, hv⟩
  rw [mem_scPQ]
  exact ⟨anc_right hvx, fun w hw => pm230_211 (fun u hu => anc_po_trans hu hw) h⟩

/-- ✱234·105. \(\vdash :P_{\text{po}}\in \text{Ser}.x\in \text{sc}(P,Q)ʻR\cap \text{D}ʻP_{1}.\supset .RQ_{\text{cn}}(\overrightarrow{P}_{*}ʻx)\) -/
theorem pm234_105 {x : α} :
    po P ∈ Ser ∧ x ∈ scPQ P Q R ∩ dom (P1 P) → cn Q R (refs (anc P) x) := by
  rintro ⟨hS, hx, w, hw⟩
  obtain ⟨hirr, hcon⟩ := poSer hS
  obtain ⟨u0, v0, -, he⟩ := P1_iff.1 hw
  have hu0 : u0 ∈ itvCC P x w := by rw [he]; exact Or.inl rfl
  have hxw : anc P x w := anc_trans' hu0.1 hu0.2
  have hxP : x ∈ fld P := anc_left hxw
  have hmem : ∀ z, anc P x z → anc P z w → z = u0 ∨ z = v0 := fun z h1 h2 => by
    have : z ∈ itvCC P x w := ⟨h1, h2⟩
    rw [he] at this
    exact this
  have hpo : po P x w := by
    rcases anc_iff_po.1 hxw with ⟨e, -⟩ | hp
    · exfalso
      subst e
      have e0 : ∀ z, z ∈ itvCC P x x → z = x := fun z hz => by
        rcases anc_iff_po.1 hz.1 with ⟨e, -⟩ | hp
        · exact e.symm
        · exact absurd (po_anc_trans hp hz.2) (hirr x)
      obtain ⟨a, b, hab, hab'⟩ := P1_iff.1 hw
      have ha : a ∈ itvCC P x x := by rw [hab']; exact Or.inl rfl
      have hb : b ∈ itvCC P x x := by rw [hab']; exact Or.inr rfl
      exact hab ((e0 a ha).trans (e0 b hb).symm)
    · exact hp
  have heq : refs (po P) w = refs (anc P) x := by
    ext u
    constructor
    · intro hu
      rcases hcon u x (po_left hu) hxP with h | h
      · exact h
      · exfalso
        have hux : u ≠ x := fun e => by subst e; exact hirr _ h
        have huw : u ≠ w := fun e => by subst e; exact hirr _ hu
        have hxw' : x ≠ w := fun e => by subst e; exact hirr _ hpo
        rcases hmem u (anc_of_po h) (anc_of_po hu) with h1 | h1 <;>
        rcases hmem x (anc_rfl hxP) hxw with h2 | h2 <;>
        rcases hmem w hxw (anc_rfl (po_right hpo)) with h3 | h3
        all_goals first
          | exact hux (h1.trans h2.symm)
          | exact huw (h1.trans h3.symm)
          | exact hxw' (h2.trans h3.symm)
    · intro hu
      exact anc_po_trans hu hpo
  rw [← heq]
  exact (mem_scPQ.1 hx).2 w hpo

private theorem scPQ_congr {P P' : α → α → Prop} (hf : fld P = fld P')
    (hp : ∀ x y, po P x y ↔ po P' x y) : scPQ P Q R = scPQ P' Q R := by
  ext x
  rw [mem_scPQ, mem_scPQ, hf]
  refine and_congr Iff.rfl (forall_congr' fun w => imp_congr (hp x w) ?_)
  have : refs (po P) w = refs (po P') w := Set.ext fun u => hp u w
  rw [this]

/-- ✱234·106. \(\vdash .\text{sc}(P,Q)ʻR=\text{sc}(P_{\text{po}},Q)ʻR.\text{os}(P,Q)ʻR=\text{os}(P_{\text{po}},Q)ʻR \quad[*234·1]\) -/
theorem pm234_106 : scPQ P Q R = scPQ (po P) Q R ∧ osPQ P Q R = osPQ (po P) Q R := by
  have h1 : scPQ P Q R = scPQ (po P) Q R :=
    scPQ_congr (fld_po P).symm fun _ _ => po_po.symm
  have h2 : scPQ P˘ Q R = scPQ (po P)˘ Q R :=
    scPQ_congr (by rw [fld_cnv, fld_cnv, fld_po]) fun x y => by rw [po_cnv, po_cnv, po_po]
  refine ⟨h1, ?_⟩
  show scPQ P Q R ∩ scPQ P˘ Q R = scPQ (po P) Q R ∩ scPQ (po P)˘ Q R
  rw [← h1, ← h2]

/-- ✱234·107. \(\vdash \colon\ldotp x\in CʻP-\text{D}ʻP_{1}.\supset :x\in \text{sc}(P,Q)ʻR.\equiv .\overrightarrow{P}_{*}ʻʻ\overleftarrow{P}_{\text{po}}ʻx\subset \overleftarrow{Q}_{\text{cn}}ʻR\) -/
theorem pm234_107 {x : α} :
    x ∈ fld P \ dom (P1 P) →
      (x ∈ scPQ P Q R ↔ Rfwd (anc P) ʻʻ rels (po P) x ⊆ rels (cn Q) R) := by
  rintro ⟨hxP, hx1⟩
  rw [mem_scPQ]
  constructor
  · rintro ⟨-, h⟩ C ⟨w, hw, rfl⟩
    exact pm230_211 (fun u hu => anc_of_po hu) (h w hw)
  · intro h
    refine ⟨hxP, fun w hw => ?_⟩
    have hcn : ∀ v, po P x v → cn Q R (refs (anc P) v) := fun v hv => h ⟨v, hv, rfl⟩
    by_cases e : x = w
    · subst e
      have : refs (po P) x = refs (anc P) x := by
        ext u
        exact ⟨anc_of_po, fun hu => anc_po_trans hu hw⟩
      rw [this]
      exact hcn x hw
    · -- some `u` lies strictly between `x` and `w`
      have : ∃ u, (anc P x u ∧ anc P u w) ∧ u ≠ x ∧ u ≠ w := by
        by_contra hn
        simp only [not_exists, not_and, not_not] at hn
        apply hx1
        refine ⟨w, P1_iff.2 ⟨x, w, e, Set.ext fun u => ⟨fun hu => ?_, ?_⟩⟩⟩
        · by_cases hux : u = x
          · exact Or.inl hux
          · exact Or.inr (hn u hu hux)
        · rintro (rfl | rfl)
          · exact ⟨anc_rfl hxP, anc_of_po hw⟩
          · exact ⟨anc_of_po hw, anc_rfl (po_right hw)⟩
      obtain ⟨u, ⟨hxu, huw⟩, hux, huw'⟩ := this
      have hxu' : po P x u := (anc_iff_po.1 hxu).resolve_left fun h => hux h.1.symm
      have huw'' : po P u w := (anc_iff_po.1 huw).resolve_left fun h => huw' h.1
      exact pm230_211 (fun v hv => anc_po_trans hv huw'') (hcn u hxu')

/-- ✱234·11. \[\begin{align}\vdash \colon\ldotp &x\in \text{D}ʻP\cap \text{ᗡ}ʻP:x\in P(z-w).\supset _{z,w}.RQ_{\text{cn}}{P(z-w)}:\equiv :\\ &x\in \text{D}ʻP\cap \text{ᗡ}ʻP:x\in P(z-w).\supset _{z,w}.\\ &(\exists y).y\in CʻQ\cap \text{ᗡ}ʻR.Rʻʻ\overleftarrow{Q}_{*}ʻy\subset P(z-w) \quad[*230·11]\end{align}\]

The two sides differ only by ✱230·11. -/
theorem pm234_11 {x : α} :
    (x ∈ dom P ∩ codom P ∧ ∀ z w, x ∈ itvOO P z w → cn Q R (itvOO P z w)) ↔
      (x ∈ dom P ∩ codom P ∧ ∀ z w, x ∈ itvOO P z w →
        ∃ y, y ∈ fld Q ∩ codom R ∧ R ʻʻ rels (anc Q) y ⊆ itvOO P z w) :=
  Iff.rfl

/-- ✱234·111. \[\begin{align}\vdash \colon\ldotp x\in \text{D}ʻP\cap \text{ᗡ}ʻP:x\in P(z-w).\supset _{z,w}.&RQ_{\text{cn}}\{P(z-w)\}:\supset .\\ &x\in \text{os}(P,Q)ʻR\end{align}\] -/
theorem pm234_111 {x : α} :
    (x ∈ dom P ∩ codom P ∧ ∀ z w, x ∈ itvOO P z w → cn Q R (itvOO P z w)) →
      x ∈ osPQ P Q R := by
  rintro ⟨⟨⟨v, hxv⟩, ⟨z, hzx⟩⟩, h⟩
  refine ⟨mem_scPQ.2 ⟨fld_of_left hxv, fun w hw => ?_⟩,
    mem_scPQ_cnv.2 ⟨fld_of_left hxv, fun w hw => ?_⟩⟩
  · exact pm230_211 (fun u (hu : u ∈ itvOO P z w) => hu.2) (h z w ⟨po_of hzx, hw⟩)
  · exact pm230_211 (fun u (hu : u ∈ itvOO P w v) => hu.1) (h w v ⟨hw, po_of hxv⟩)

/-- ✱234·12. \[\begin{align}\vdash \colon\colon Q_{*}\in \text{connex} .&\supset \colon\ldotp x\in \text{os}(P,Q)ʻR\cap \text{D}ʻP\cap \text{ᗡ}ʻP.\equiv :\\ &x\in \text{D}ʻP\cap \text{ᗡ}ʻP:x\in P(z-w).\supset _{z,w}.RQ_{\text{cn}}\{P(z-w)\}\end{align}\] -/
theorem pm234_12 {x : α} :
    anc Q ∈ connex →
      (x ∈ osPQ P Q R ∩ dom P ∩ codom P ↔
        x ∈ dom P ∩ codom P ∧ ∀ z w, x ∈ itvOO P z w → cn Q R (itvOO P z w)) := by
  intro hc
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, hd⟩, hc'⟩
    refine ⟨⟨hd, hc'⟩, fun z w ⟨hzx, hxw⟩ => ?_⟩
    have a1 := (mem_scPQ.1 h1).2 w hxw
    have a2 := (mem_scPQ_cnv.1 h2).2 z hzx
    have := (pm230_42 hc).1 ⟨a2, a1⟩
    exact this
  · intro h
    exact ⟨⟨pm234_111 h, h.1.1⟩, h.1.2⟩

/-- ✱234·121. \(\vdash .\overrightarrow{B}ʻ\breve{P} \subset \text{sc}(P,Q)ʻR \quad[*93·104.(*234·01)]\)

`B⃗'P̆` is `refs Beg P˘`. -/
theorem pm234_121 : refs Beg P˘ ⊆ scPQ P Q R := by
  rintro x ⟨⟨z, hz⟩, hn⟩
  refine mem_scPQ.2 ⟨fld_of_right hz, fun w hw => ?_⟩
  rw [po_iff_transGen] at hw
  obtain ⟨b, hxb, -⟩ := Relation.TransGen.head'_iff.1 hw
  exact absurd ⟨b, hxb⟩ hn

/-- ✱234·122. \[\begin{align}\vdash \colon\ldotp P_{\text{po}}\in &\text{connex} .x=BʻP.\supset :\\ &x\in \text{os}(P,Q)ʻR.\equiv .x\in \text{sc}(P,Q)ʻR.\equiv .\overrightarrow{P}_{\text{po}}ʻʻ\text{ᗡ}ʻP\subset \overleftarrow{Q}_{\text{cn}}ʻR\\ &[*234·121.(*234·02).*234·1.*205·253]\end{align}\]

`x = B'P` is `Desc Beg P (fun b => x = b)`; the chain of three equivalences is the conjunction of
its two links. -/
theorem pm234_122 {x : α} :
    po P ∈ connex ∧ Desc Beg P (fun b => x = b) →
      (x ∈ osPQ P Q R ↔ x ∈ scPQ P Q R) ∧
        (x ∈ scPQ P Q R ↔ Rfwd (po P) ʻʻ codom P ⊆ rels (cn Q) R) := by
  rintro ⟨hc, b, hb, rfl⟩
  obtain ⟨⟨y, hxy⟩, hxn⟩ := (hb x).2 rfl
  rw [mem_connex, fld_po] at hc
  have hxP : x ∈ fld P := fld_of_left hxy
  have hcnv : x ∈ scPQ P˘ Q R := mem_scPQ_cnv.2 ⟨hxP, fun w hw => by
    rw [po_iff_transGen] at hw
    obtain ⟨c, -, hcx⟩ := Relation.TransGen.tail'_iff.1 hw
    exact absurd ⟨c, hcx⟩ hxn⟩
  refine ⟨⟨fun h => h.1, fun h => ⟨h, hcnv⟩⟩, ?_⟩
  rw [mem_scPQ]
  constructor
  · rintro ⟨-, h⟩ C ⟨w, ⟨u, huw⟩, rfl⟩
    refine h w ?_
    rcases hc x w ⟨hxP, fld_of_right huw⟩ with (h1 | e) | h1
    · exact h1
    · exact absurd (e ▸ ⟨u, huw⟩) hxn
    · rw [po_iff_transGen] at h1
      obtain ⟨c, -, hcx⟩ := Relation.TransGen.tail'_iff.1 h1
      exact absurd ⟨c, hcx⟩ hxn
  · intro h
    refine ⟨hxP, fun w hw => h ⟨w, ?_, rfl⟩⟩
    rw [po_iff_transGen] at hw
    obtain ⟨c, -, hcw⟩ := Relation.TransGen.tail'_iff.1 hw
    exact ⟨c, hcw⟩

/-- ✱234·13. \(\vdash :x\in \text{sc}(P,Q)ʻR.\supset .\overleftarrow{P}_{*}ʻx\subset \text{sc}(P,Q)ʻR\) -/
theorem pm234_13 {x : α} : x ∈ scPQ P Q R → rels (anc P) x ⊆ scPQ P Q R := by
  intro hx u hu
  rw [mem_scPQ] at hx ⊢
  exact ⟨anc_right hu, fun w hw => hx.2 w (anc_po_trans hu hw)⟩

/-- ✱234·131. \(\vdash .\text{sc}(P,Q)ʻR=\breve{P} _{*}ʻʻ\text{sc}(P,Q)ʻR.\text{sc}(P,Q)ʻR\in \text{sect}ʻ\breve{P}\)

`P̆_*''sc(P,Q)'R` is `ancCnv P ʻʻ scPQ P Q R` (✱90·02). -/
theorem pm234_131 : scPQ P Q R = ancCnv P ʻʻ scPQ P Q R ∧ scPQ P Q R ∈ sect P˘ := by
  refine ⟨Set.Subset.antisymm
    (fun x (hx : x ∈ scPQ P Q R) => ⟨x, hx, anc_rfl (mem_scPQ.1 hx).1⟩)
    fun u ⟨x, hx, hux⟩ => pm234_13 hx hux, ?_, ?_⟩
  · intro x hx
    rw [fld_cnv]
    exact (mem_scPQ.1 hx).1
  · rintro u ⟨x, hx, hux⟩
    exact pm234_13 hx (anc_of hux)

/-- ✱234·14. \(\vdash :Q_{*}\in \text{connex} .x\in \text{sc}(P,Q)ʻR.\supset .x\in CʻP.\overleftarrow{P}_{\text{po}}ʻx\subset \breve{P} \overline{R} _{\text{sc}}Q\) -/
theorem pm234_14 {x : α} :
    anc Q ∈ connex ∧ x ∈ scPQ P Q R → x ∈ fld P ∧ rels (po P) x ⊆ scBar P˘ R Q := by
  rintro ⟨hc, hx⟩
  rw [mem_scPQ] at hx
  refine ⟨hx.1, fun u hu => ?_⟩
  have hcn := hx.2 u hu
  have hcn' : cn Q R (rels (anc P˘) u) := pm230_211 (fun v hv => anc_cnv.2 (anc_of_po hv)) hcn
  exact pm231_141 (P := P˘) ⟨hc, hcn'⟩

/-- ✱234·141. \(\vdash :Q_{*}\in \text{connex} .\exists !\text{sc}(P,Q)ʻR.\supset .\exists !\breve{P} \overline{R} _{\text{sc}}Q \quad[*234·14]\)

**Status.** proved (corrected): false as printed: a member of `sc(P,Q)'R` with no successor in `P`
(an end of `P`) belongs to `sc(P,Q)'R` vacuously. Counterexample: `P = 0 ↓ 1` on `ℕ`,
`Q = I ↾ ι'y`, `R = 2 ↓ y` (the value `2` is not in `C'P`); then `1 ∈ sc(P,Q)'R` but
`P̆ R̄_sc Q = Λ`. The demonstration (✱234·14) needs a member of `sc(P,Q)'R ∩ D'P`; the hypothesis
`∃!sc(P,Q)'R ∩ D'P` (as in ✱234·142) is read. -/
theorem pm234_141 : anc Q ∈ connex ∧ (scPQ P Q R ∩ dom P).Nonempty → (scBar P˘ R Q).Nonempty := by
  rintro ⟨hc, x, hx, w, hxw⟩
  exact ⟨w, (pm234_14 ⟨hc, hx⟩).2 (po_of hxw)⟩

/-- ✱234·142. \(\vdash :\exists !\text{sc}(P,Q)ʻR\cap \text{D}ʻP.\supset .\exists !CʻQ\cap \text{ᗡ}ʻR\) -/
theorem pm234_142 : (scPQ P Q R ∩ dom P).Nonempty → (fld Q ∩ codom R).Nonempty := by
  rintro ⟨x, hx, w, hxw⟩
  obtain ⟨y, hy, -⟩ := (mem_scPQ.1 hx).2 w (po_of hxw)
  exact ⟨y, hy⟩

/-- ✱234·15. \(\vdash :P_{*},Q_{*}\in \text{connex} .\exists !\text{sc}(P,Q)ʻR.\supset .P\overline{R} _{\text{sc}}Q\cup \breve{P} \overline{R} _{\text{sc}}Q=CʻP\)

**Status.** proved (corrected): false as printed, for the reason given at ✱234·141, on which the
demonstration rests (in the counterexample there `P R̄_sc Q = P̆ R̄_sc Q = Λ ≠ C'P`). The hypothesis
`∃!sc(P,Q)'R ∩ D'P` is read for `∃!sc(P,Q)'R`. -/
theorem pm234_15 :
    (anc P ∈ connex ∧ anc Q ∈ connex) ∧ (scPQ P Q R ∩ dom P).Nonempty →
      scBar P R Q ∪ scBar P˘ R Q = fld P := by
  rintro ⟨⟨hcP, hcQ⟩, hne⟩
  have hne' := pm234_141 ⟨hcQ, hne⟩
  have hcP' : anc P˘ ∈ connex := by
    have : anc P˘ = (anc P)˘ := funext fun x => funext fun y => propext anc_cnv
    rw [this]
    exact connex_cnv hcP
  have h := pm231_202 (P := P˘) ⟨⟨hcP', hcQ⟩, hne'⟩
  rw [fld_cnv] at h
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · exact hx.2
    · rw [← fld_cnv P]
      exact hx.2
  · intro x hx
    by_cases h2 : x ∈ scBar P˘ R Q
    · exact Or.inr h2
    · exact Or.inl (h ⟨hx, h2⟩)

/-- ✱234·16. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.Q_{*}\in \text{connex} .\supset .\\ &P\overline{R} _{\text{sc}}Q\subset pʻ\overrightarrow{P}_{*}ʻʻ\text{sc}(P,Q)ʻR.\breve{P} _{\text{po}}ʻʻ\text{sc}(P,Q)ʻR\subset \breve{P} \overline{R} _{\text{sc}}Q \quad[*234·101·14]\end{align}\]

`P̆_po''sc(P,Q)'R` is `po P˘ ʻʻ scPQ P Q R`. -/
theorem pm234_16 :
    po P ∈ Ser ∧ anc Q ∈ connex →
      scBar P R Q ⊆ prodCls (Rfwd (anc P) ʻʻ scPQ P Q R) ∧
        po P˘ ʻʻ scPQ P Q R ⊆ scBar P˘ R Q := by
  rintro ⟨hS, hc⟩
  refine ⟨fun u hu => mem_prodCls_Rfwd.2 fun x hx => pm234_101 ⟨hS, hx⟩ hu, ?_⟩
  rintro u ⟨x, hx, hux⟩
  exact (pm234_14 ⟨hc, hx⟩).2 (po_cnv.1 hux)

/-- ✱234·161. \[\begin{align}\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.RʻʻCʻQ\subset CʻP.P\overline{R} _{\text{sc}}Q&\subset \overrightarrow{P}_{*}ʻx.\supset :\\ &P\overline{R} _{\text{sc}}Q=\overrightarrow{P}_{*}ʻx.\lor.RQ_{\text{cn}}(\overrightarrow{P}_{*}ʻx)\end{align}\] -/
theorem pm234_161 {x : α} :
    (po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ scBar P R Q ⊆ refs (anc P) x →
      scBar P R Q = refs (anc P) x ∨ cn Q R (refs (anc P) x) := by
  rintro ⟨⟨hS, hR⟩, hsub⟩
  by_cases h : cn Q R (refs (anc P) x)
  · exact Or.inr h
  · left
    exact Set.Subset.antisymm hsub
      (pm231_24 ⟨⟨connex_anc_of_po (Ser_connex hS), hR⟩, h⟩)

/-- The characterization ✱234·17 (`P_po ∈ Ser`, `R''C'Q ⊂ C'P`). -/
private theorem mem_scPQ_iff {x : α} (hS : po P ∈ Ser) (hR : R ʻʻ fld Q ⊆ fld P) :
    x ∈ scPQ P Q R ↔ x ∈ fld P ∧ scBar P R Q ⊆ refs (anc P) x := by
  obtain ⟨hirr, hcon⟩ := poSer hS
  refine ⟨fun hx => ⟨(mem_scPQ.1 hx).1, pm234_101 ⟨hS, hx⟩⟩, fun ⟨hxP, hsub⟩ => ?_⟩
  refine mem_scPQ.2 ⟨hxP, fun w hw => ?_⟩
  have hw' : w ∉ scBar P R Q := fun h => hirr w (anc_po_trans (hsub h) hw)
  have : ¬∀ y, y ∈ fld Q ∩ codom R → w ∈ anc P ʻʻ (R ʻʻ rels (anc Q) y) :=
    fun h => hw' (mem_scBar'.2 ⟨h, po_right hw⟩)
  simp only [not_forall] at this
  obtain ⟨y, hy, hn⟩ := this
  refine ⟨y, hy, fun v hv => ?_⟩
  have hvP : v ∈ fld P := by
    obtain ⟨z, hyz, hvz⟩ := hv
    exact hR ⟨z, anc_right hyz, hvz⟩
  rcases hcon w v (po_right hw) hvP with h | h
  · exact absurd ⟨v, hv, h⟩ hn
  · exact h

/-- ✱234·162. \[\begin{align}\vdash :P_{\text{po}}\in \text{Ser}.RʻʻCʻQ\subset &CʻP.\overrightarrow{P}_{*}ʻx=P\overline{R} _{\text{sc}}Q.x\in CʻP.\supset .\\ &x\in \text{sc}(P,Q)ʻR\end{align}\] -/
theorem pm234_162 {x : α} :
    ((po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ refs (anc P) x = scBar P R Q) ∧ x ∈ fld P →
      x ∈ scPQ P Q R :=
  fun ⟨⟨⟨hS, hR⟩, he⟩, hxP⟩ => (mem_scPQ_iff hS hR).2 ⟨hxP, he.symm.subset⟩

/-- ✱234·17. \[\begin{align}\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.RʻʻCʻQ\subset &CʻP.\supset :\\ &x\in \text{sc}(P,Q)ʻR.\equiv .x\in CʻP.P\overline{R} _{\text{sc}}Q\subset \overrightarrow{P}_{*}ʻx\end{align}\] -/
theorem pm234_17 {x : α} :
    po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P →
      (x ∈ scPQ P Q R ↔ x ∈ fld P ∧ scBar P R Q ⊆ refs (anc P) x) :=
  fun ⟨hS, hR⟩ => mem_scPQ_iff hS hR

/-- `C'P − sc(P,Q)'R = P''(P R̄_sc Q)` (cf. ✱234·174). -/
private theorem compl_scPQ (hS : po P ∈ Ser) (hR : R ʻʻ fld Q ⊆ fld P) :
    fld P \ scPQ P Q R = P ʻʻ scBar P R Q := by
  obtain ⟨hirr, hcon⟩ := poSer hS
  rw [← pm231_134]
  ext x
  rw [Set.mem_sdiff, mem_scPQ_iff hS hR]
  constructor
  · rintro ⟨hxP, hn⟩
    have : ¬scBar P R Q ⊆ refs (anc P) x := fun h => hn ⟨hxP, h⟩
    rw [Set.not_subset] at this
    obtain ⟨s, hs, hsx⟩ := this
    rcases hcon s x hs.2 hxP with h | h
    · exact absurd h hsx
    · exact ⟨s, hs, h⟩
  · rintro ⟨s, hs, hxs⟩
    exact ⟨po_left hxs, fun ⟨_, h⟩ => hirr x (po_anc_trans hxs (h hs))⟩

/-- ✱234·171. \[\begin{align}\vdash :P_{\text{po}}\in \text{Ser}.RʻʻCʻQ\subset CʻP.x\in CʻP-&\text{sc}(P,Q)ʻR.\supset .\\ &\overrightarrow{P}_{*}ʻx\subset Pʻʻ(P\overline{R} _{\text{sc}}Q)\end{align}\] -/
theorem pm234_171 {x : α} :
    (po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ x ∈ fld P \ scPQ P Q R →
      refs (anc P) x ⊆ P ʻʻ scBar P R Q := by
  rintro ⟨⟨hS, hR⟩, hx⟩ u hu
  rw [compl_scPQ hS hR] at hx
  rw [← pm231_134] at hx ⊢
  obtain ⟨s, hs, hxs⟩ := hx
  exact ⟨s, hs, anc_po_trans hu hxs⟩

/-- ✱234·172. \(\vdash :P_{\text{po}}\in \text{Ser}.\supset .CʻP-\text{sc}(P,Q)ʻR=CʻP\cap pʻ\overrightarrow{P}_{\text{po}}ʻʻ\text{sc}(P,Q)ʻR\) -/
theorem pm234_172 :
    po P ∈ Ser → fld P \ scPQ P Q R = fld P ∩ prodCls (Rfwd (po P) ʻʻ scPQ P Q R) := by
  intro hS
  obtain ⟨hirr, hcon⟩ := poSer hS
  ext x
  constructor
  · rintro ⟨hxP, hn⟩
    refine ⟨hxP, mem_prodCls_Rfwd.2 fun s hs => ?_⟩
    rcases hcon s x hs.1 hxP with h | h
    · exact absurd (pm234_13 hs h) hn
    · exact h
  · rintro ⟨hxP, hp⟩
    exact ⟨hxP, fun hx => hirr x (mem_prodCls_Rfwd.1 hp x hx)⟩

/-- ✱234·173. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.\exists !\text{sc}(P,Q)ʻR.\supset .CʻP-\text{sc}(P,Q)ʻR=pʻ\overrightarrow{P}_{\text{po}}ʻʻ\text{sc}(P,Q)ʻR\\ &[*234·172.*40·61.*37·15]\end{align}\] -/
theorem pm234_173 :
    po P ∈ Ser ∧ (scPQ P Q R).Nonempty →
      fld P \ scPQ P Q R = prodCls (Rfwd (po P) ʻʻ scPQ P Q R) := by
  rintro ⟨hS, s, hs⟩
  rw [pm234_172 hS]
  exact Set.inter_eq_right.2 fun x hx => po_left (mem_prodCls_Rfwd.1 hx s hs)

/-- ✱234·174. \[\begin{align}\vdash :P_{\text{po}}\in &\text{Ser}.Q_{*}\in \text{connex} .RʻʻCʻQ\subset CʻP.\supset .\\ &CʻP\cap pʻ\overrightarrow{P}_{\text{po}}ʻʻ\text{sc}(P,Q)ʻR=P ʻʻ(P \overline{R} _{\text{sc}}Q)=CʻP-\text{sc}(P,Q)ʻR\end{align}\]

The chain of three is the conjunction of its two links. -/
theorem pm234_174 :
    (po P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      fld P ∩ prodCls (Rfwd (po P) ʻʻ scPQ P Q R) = P ʻʻ scBar P R Q ∧
        P ʻʻ scBar P R Q = fld P \ scPQ P Q R := by
  rintro ⟨⟨hS, -⟩, hR⟩
  rw [← pm234_172 hS, compl_scPQ hS hR]
  exact ⟨rfl, rfl⟩

/-- ✱234·175. \[\begin{align}&\vdash :\text{Hp}*234·174.\exists !\text{sc}(P,Q)ʻR.\supset .pʻ\overrightarrow{P}_{\text{po}}ʻʻ\text{sc}(P,Q)ʻR=Pʻʻ(P \overline{R} _{\text{sc}}Q)\\ &[*234·174.*40·61.*37·15]\end{align}\] -/
theorem pm234_175 :
    ((po P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P) ∧ (scPQ P Q R).Nonempty →
      prodCls (Rfwd (po P) ʻʻ scPQ P Q R) = P ʻʻ scBar P R Q := by
  rintro ⟨⟨⟨hS, -⟩, hR⟩, hne⟩
  rw [← pm234_173 ⟨hS, hne⟩, compl_scPQ hS hR]

/-- ✱234·18. \[\begin{align}\vdash :&P_{\text{po}}\in \text{Ser}.Q_{*}\in \text{connex} .RʻʻCʻQ\subset CʻP.\supset .\\ &CʻP=\text{sc}(P,Q)ʻR\cup Pʻʻ(P\overline{R} _{\text{sc}}Q).\text{sc}(P,Q)ʻR\cap Pʻʻ(P\overline{R} _{\text{sc}}Q)=\Lambda .\\ &\text{sc}(P,Q)ʻR=CʻP-Pʻʻ(P\overline{R} _{\text{sc}}Q)\end{align}\]

The product of three is bracketed to the left. -/
theorem pm234_18 :
    (po P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      (fld P = scPQ P Q R ∪ P ʻʻ scBar P R Q ∧ scPQ P Q R ∩ P ʻʻ scBar P R Q = Λ) ∧
        scPQ P Q R = fld P \ P ʻʻ scBar P R Q := by
  rintro ⟨⟨hS, -⟩, hR⟩
  have e := compl_scPQ (Q := Q) (R := R) hS hR
  have hsub : scPQ P Q R ⊆ fld P := fun x (hx : x ∈ scPQ P Q R) => (mem_scPQ.1 hx).1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← e, Set.union_sdiff_cancel hsub]
  · rw [← e]
    exact eq_null_of fun x ⟨h1, h2⟩ => h2.2 h1
  · rw [← e, Set.sdiff_sdiff_cancel_left hsub]

/-- ✱234·181. \[\begin{align}\vdash :P_{\text{po}}\in \text{Ser}.Q_{*}\in &\text{connex} .RʻʻCʻQ\subset CʻP.\supset .\\ &P\overline{R} _{\text{sc}}Q\cap \text{sc}(P,Q)ʻR=\overrightarrow{\text{max}}_{P}ʻ(P\overline{R} _{\text{sc}}Q).\\ &\text{sc}(P,Q)ʻR=(CʻP-P\overline{R} _{\text{sc}}Q)\cup \overrightarrow{\text{max}}_{P}ʻ(P\overline{R} _{\text{sc}}Q)\end{align}\]

`max⃗_P'…` is `refs (maxP P) …`. -/
theorem pm234_181 :
    (po P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      scBar P R Q ∩ scPQ P Q R = refs (maxP P) (scBar P R Q) ∧
        scPQ P Q R = (fld P \ scBar P R Q) ∪ refs (maxP P) (scBar P R Q) := by
  rintro ⟨⟨hS, -⟩, hR⟩
  have e : scPQ P Q R = fld P \ P ʻʻ scBar P R Q := by
    rw [← compl_scPQ hS hR,
      Set.sdiff_sdiff_cancel_left fun x (hx : x ∈ scPQ P Q R) => (mem_scPQ.1 hx).1]
  have hmax : ∀ x, x ∈ refs (maxP P) (scBar P R Q) ↔ x ∈ scBar P R Q ∧ x ∉ P ʻʻ scBar P R Q := by
    intro x
    show maxP P x _ ↔ _
    rw [maxP_iff]
    exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, fun ⟨y, hy, hxy⟩ => h2 y hy hxy⟩,
      fun ⟨h1, h2⟩ => ⟨⟨h1, h1.2⟩, fun y hy hxy => h2 ⟨y, hy, hxy⟩⟩⟩
  rw [e]
  refine ⟨Set.ext fun x => ?_, Set.ext fun x => ?_⟩
  · rw [hmax]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h1.2, h2⟩⟩
  · rw [Set.mem_union, hmax]
    constructor
    · rintro ⟨hxP, hn⟩
      by_cases hx : x ∈ scBar P R Q
      · exact Or.inr ⟨hx, hn⟩
      · exact Or.inl ⟨hxP, hx⟩
    · rintro (⟨hxP, hx⟩ | ⟨hx, hn⟩)
      · exact ⟨hxP, fun h => hx (pm231_13.2 h)⟩
      · exact ⟨hx.2, hn⟩

/-- ✱234·182. \[\begin{align}\vdash :P\in \text{Ser}.Q_{*}\in \text{connex} .RʻʻCʻQ&\subset CʻP.\supset .\\ &\overrightarrow{\text{limax}} _{P}ʻ(P\overline{R} _{\text{sc}}Q)=\overrightarrow{\text{min}}_{P}ʻ\text{sc}(P,Q)ʻR\end{align}\]

`limax⃗_P'…`, `min⃗_P'…` are `refs (limaxP P) …`, `refs (minP P) …`. -/
theorem pm234_182 :
    (P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      refs (limaxP P) (scBar P R Q) = refs (minP P) (scPQ P Q R) := by
  rintro ⟨⟨hS, -⟩, hR⟩
  have hpo : po P ∈ Ser := by
    rw [po_eq_of_transR (Ser_transR hS)]
    exact hS
  obtain ⟨⟨hirr, htr⟩, hcon⟩ := Ser_parts hS
  have e : scPQ P Q R = fld P \ P ʻʻ scBar P R Q := by
    rw [← compl_scPQ hpo hR,
      Set.sdiff_sdiff_cancel_left fun x (hx : x ∈ scPQ P Q R) => (mem_scPQ.1 hx).1]
  ext m
  show limaxP P m _ ↔ minP P m _
  rw [limax_iff_Ser hS, minP_iff, e]
  constructor
  · rintro ⟨hmP, he⟩
    refine ⟨⟨⟨hmP, fun h => ?_⟩, hmP⟩, fun y ⟨hyP, hy⟩ hym => hy ?_⟩
    · rw [← he] at h
      exact hirr m h
    · rw [← he]
      exact hym
  · rintro ⟨⟨⟨hmP, hm⟩, -⟩, hmin⟩
    refine ⟨hmP, Set.ext fun u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
    · by_contra hn
      exact hmin u ⟨fld_of_left hu, hn⟩ hu
    · obtain ⟨s, hs, hus⟩ := hu
      rcases hcon u m (fld_of_left hus) hmP with (h | e') | h
      · exact h
      · subst e'
        exact absurd ⟨s, hs, hus⟩ hm
      · exact absurd ⟨s, hs, htr m u s h hus⟩ hm

/-- ✱234·183. \[\begin{align}&\vdash :\text{Hp}*234·18.\text{sc}(P,Q)ʻR=\Lambda .\supset .P\overline{R} _{\text{sc}}Q=CʻP.{\sim}\text{E}!Bʻ\breve{P}\\ &[*234·181·121]\end{align}\]

`∼E!B'P̆` is `¬EDesc Beg P˘`. -/
theorem pm234_183 :
    ((po P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P) ∧ scPQ P Q R = Λ →
      scBar P R Q = fld P ∧ ¬EDesc Beg P˘ := by
  rintro ⟨⟨⟨hS, -⟩, hR⟩, h0⟩
  have e := compl_scPQ (Q := Q) (R := R) hS hR
  rw [h0, Null_eq_empty, Set.sdiff_empty] at e
  refine ⟨Set.Subset.antisymm (fun x hx => hx.2) fun x hx => ?_, ?_⟩
  · rw [e] at hx
    exact pm231_13.2 hx
  · rintro ⟨b, hb⟩
    have : b ∈ scPQ P Q R := pm234_121 ((hb b).2 rfl)
    rw [h0] at this
    exact not_mem_null this

/-! The ultimate oscillation `os(P,Q)'R` in terms of `M = max⃗_P'(P R̄_sc Q)` and
`N = min⃗_P'(P̆ R̄_sc Q)` (✱234·2–·272). -/

private theorem max_unique_down {A : Set α} {m m' : α} (hS : po P ∈ Ser)
    (hAd : ∀ u w, u ∈ A → anc P w u → w ∈ A) (h1 : maxP P m A) (h2 : maxP P m' A) : m = m' := by
  rw [maxP_iff] at h1 h2
  have key : ∀ a b, maxP P a A → b ∈ A → po P a b → False := by
    intro a b ha hb hab
    rw [maxP_iff] at ha
    rw [po_iff_transGen] at hab
    obtain ⟨c, hac, hcb⟩ := Relation.TransGen.head'_iff.1 hab
    exact ha.2 c (hAd b c hb (anc_iff_reflTransGen.2 ⟨fld_of_right hac, hcb⟩)) hac
  rcases (poSer hS).2 m m' h1.1.2 h2.1.2 with h | h
  · rcases anc_iff_po.1 h with ⟨e, -⟩ | hp
    · exact e
    · exact (key m m' (maxP_iff.2 h1) h2.1.1 hp).elim
  · exact (key m' m (maxP_iff.2 h2) h1.1.1 h).elim

private theorem M_unique {m m' : α} (hS : po P ∈ Ser) (h1 : maxP P m (scBar P R Q))
    (h2 : maxP P m' (scBar P R Q)) : m = m' :=
  max_unique_down hS (fun _ _ hu h => scBar_down hu h) h1 h2

private theorem N_unique {n n' : α} (hS : po P ∈ Ser) (h1 : minP P n (scBar P˘ R Q))
    (h2 : minP P n' (scBar P˘ R Q)) : n = n' := by
  have hS' : po P˘ ∈ Ser := by
    rw [po_cnv_eq]
    exact Ser_cnv hS
  exact max_unique_down (P := P˘) hS' (fun _ _ hu h => scBar_down hu h) h1 h2

/-- Membership of `os(P,Q)'R` under the hypothesis of ✱234·2. -/
private theorem os_char (hS : po P ∈ Ser) (hR : R ʻʻ fld Q ⊆ fld P) (hc : anc Q ∈ connex)
    (x : α) :
    x ∈ osPQ P Q R ↔
      ((minP P x (scBar P˘ R Q) ∧ x ∉ scBar P R Q) ∨
          (maxP P x (scBar P R Q) ∧ x ∉ scBar P˘ R Q)) ∨
        (maxP P x (scBar P R Q) ∧ minP P x (scBar P˘ R Q)) := by
  have hS' : po P˘ ∈ Ser := by
    rw [po_cnv_eq]
    exact Ser_cnv hS
  have hR' : R ʻʻ fld Q ⊆ fld P˘ := by
    rw [fld_cnv]
    exact hR
  have hU := pm231_22 ⟨⟨connex_anc_of_po (Ser_connex hS), hc⟩, hR⟩
  have e1 := compl_scPQ (Q := Q) (R := R) hS hR
  have e2 := compl_scPQ (Q := Q) (R := R) hS' hR'
  rw [fld_cnv] at e2
  have k1 : x ∈ scPQ P Q R ↔ (x ∈ fld P ∧ x ∉ scBar P R Q) ∨ maxP P x (scBar P R Q) := by
    have : x ∈ scPQ P Q R ↔ x ∈ fld P ∧ x ∉ P ʻʻ scBar P R Q := by
      rw [← e1]
      exact ⟨fun h => ⟨h.1, fun h' => h'.2 h⟩, fun ⟨h1, h2⟩ => by_contra fun h => h2 ⟨h1, h⟩⟩
    rw [this, maxP_iff]
    constructor
    · rintro ⟨hxP, hn⟩
      by_cases hx : x ∈ scBar P R Q
      · exact Or.inr ⟨⟨hx, hxP⟩, fun y hy hxy => hn ⟨y, hy, hxy⟩⟩
      · exact Or.inl ⟨hxP, hx⟩
    · rintro (⟨hxP, hx⟩ | ⟨⟨hx, hxP⟩, hmax⟩)
      · exact ⟨hxP, fun h => hx (pm231_13.2 h)⟩
      · exact ⟨hxP, fun ⟨y, hy, hxy⟩ => hmax y hy hxy⟩
  have k2 : x ∈ scPQ P˘ Q R ↔ (x ∈ fld P ∧ x ∉ scBar P˘ R Q) ∨ minP P x (scBar P˘ R Q) := by
    have : x ∈ scPQ P˘ Q R ↔ x ∈ fld P ∧ x ∉ P˘ ʻʻ scBar P˘ R Q := by
      rw [← e2]
      exact ⟨fun h => ⟨by rw [← fld_cnv P]; exact h.1, fun h' => h'.2 h⟩,
        fun ⟨h1, h2⟩ => by_contra fun h => h2 ⟨h1, h⟩⟩
    rw [this]
    show _ ↔ _ ∨ maxP P˘ x _
    rw [maxP_iff, fld_cnv]
    constructor
    · rintro ⟨hxP, hn⟩
      by_cases hx : x ∈ scBar P˘ R Q
      · exact Or.inr ⟨⟨hx, hxP⟩, fun y hy hxy => hn ⟨y, hy, hxy⟩⟩
      · exact Or.inl ⟨hxP, hx⟩
    · rintro (⟨hxP, hx⟩ | ⟨⟨hx, hxP⟩, hmax⟩)
      · refine ⟨hxP, fun h => hx ?_⟩
        exact (pm231_13 (P := P˘)).2 h
      · exact ⟨hxP, fun ⟨y, hy, hxy⟩ => hmax y hy hxy⟩
  show x ∈ scPQ P Q R ∧ x ∈ scPQ P˘ Q R ↔ _
  rw [k1, k2]
  have hM : maxP P x (scBar P R Q) → x ∈ scBar P R Q := fun h => (maxP_iff.1 h).1.1
  have hN : minP P x (scBar P˘ R Q) → x ∈ scBar P˘ R Q := fun h => (minP_iff.1 h).1.1
  constructor
  · rintro ⟨⟨hxP, hxA⟩ | hm, ⟨-, hxB⟩ | hn⟩
    · rw [hU] at hxP
      rcases hxP with h | h
      · exact absurd h hxA
      · exact absurd h hxB
    · exact Or.inl (Or.inl ⟨hn, hxA⟩)
    · exact Or.inl (Or.inr ⟨hm, hxB⟩)
    · exact Or.inr ⟨hm, hn⟩
  · rintro ((⟨hn, hxA⟩ | ⟨hm, hxB⟩) | ⟨hm, hn⟩)
    · refine ⟨Or.inl ⟨?_, hxA⟩, Or.inr hn⟩
      rw [← fld_cnv P]
      exact (hN hn).2
    · exact ⟨Or.inr hm, Or.inl ⟨(hM hm).2, hxB⟩⟩
    · exact ⟨Or.inr hm, Or.inr hn⟩

/-- ✱234·2. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.RʻʻCʻQ\subset CʻP.Q_{*}\in \text{connex} .\supset .\\ \quad\quad\quad\text{os}(P,Q)ʻR=&\{\overrightarrow{\text{min}}_{P}ʻ(\breve{P} \overline{R} _{\text{sc}}Q)-P\overline{R} _{\text{sc}}Q\}\cup \{\overrightarrow{\text{max}}_{P}ʻ(P\overline{R} _{\text{sc}}Q)-\breve{P} \overline{R} _{\text{sc}}Q\}\cup \\ &\{\overrightarrow{\text{max}}_{P}ʻ(P\overline{R} _{\text{sc}}Q)\cap \overrightarrow{\text{min}}_{P}ʻ(\breve{P} \overline{R} _{\text{sc}}Q)\}\end{align}\]

The sums of three bracket to the left. -/
theorem pm234_2 :
    (po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ anc Q ∈ connex →
      osPQ P Q R =
        (refs (minP P) (scBar P˘ R Q) \ scBar P R Q ∪
            refs (maxP P) (scBar P R Q) \ scBar P˘ R Q) ∪
          (refs (maxP P) (scBar P R Q) ∩ refs (minP P) (scBar P˘ R Q)) := by
  rintro ⟨⟨hS, hR⟩, hc⟩
  ext x
  exact os_char hS hR hc x

/-- ✱234·201. \[\begin{align}&\vdash :\text{Hp}*234·2.\supset .\text{os}(P,Q)ʻR\subset \overrightarrow{\text{max}}_{P}ʻ(P\overline{R} _{\text{sc}}Q)\cup \overrightarrow{\text{min}}_{P}ʻ(\breve{P} \overline{R} _{\text{sc}}Q)\\ &[*234·2]\end{align}\] -/
theorem pm234_201 :
    (po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ anc Q ∈ connex →
      osPQ P Q R ⊆ refs (maxP P) (scBar P R Q) ∪ refs (minP P) (scBar P˘ R Q) := by
  rintro ⟨⟨hS, hR⟩, hc⟩ x hx
  rcases (os_char hS hR hc x).1 hx with (⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inl h

private theorem le_two {X : Set α} (h : ∀ u v w, u ∈ X → v ∈ X → w ∈ X → (u = v ∨ v = w) ∨ u = w) :
    X ∈ zero ∪ one ∪ two := by
  by_cases hX : X.Nonempty
  · obtain ⟨u, hu⟩ := hX
    by_cases h2 : ∃ v, v ∈ X ∧ v ≠ u
    · obtain ⟨v, hv, hvu⟩ := h2
      right
      refine ⟨u, v, hvu.symm, Set.ext fun z => ⟨fun hz => ?_, ?_⟩⟩
      · rcases h u v z hu hv hz with (e | e) | e
        · exact absurd e.symm hvu
        · exact Or.inr e.symm
        · exact Or.inl e.symm
      · rintro (rfl | rfl)
        · exact hu
        · exact hv
    · simp only [not_exists, not_and, not_not] at h2
      exact Or.inl (Or.inr (mem_one_iff.2 ⟨u, fun z => ⟨h2 z, fun e => e ▸ hu⟩⟩))
  · exact Or.inl (Or.inl (show X = Λ from eq_null_of fun x hx => hX ⟨x, hx⟩))

/-- ✱234·202. \[\begin{align}&\vdash :\text{Hp}*234·2.\supset .\text{os}(P,Q)ʻR\in 0\cup 1\cup 2\\ &[*234·201.*205·681.*60·391]\end{align}\] -/
theorem pm234_202 :
    (po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ anc Q ∈ connex → osPQ P Q R ∈ zero ∪ one ∪ two := by
  intro h
  have hS := h.1.1
  have hsub := pm234_201 h
  refine le_two fun u v w hu hv hw => ?_
  rcases hsub hu with hu' | hu' <;> rcases hsub hv with hv' | hv' <;>
    rcases hsub hw with hw' | hw'
  all_goals first
    | exact Or.inl (Or.inl (M_unique hS hu' hv'))
    | exact Or.inl (Or.inr (M_unique hS hv' hw'))
    | exact Or.inr (M_unique hS hu' hw')
    | exact Or.inl (Or.inl (N_unique hS hu' hv'))
    | exact Or.inl (Or.inr (N_unique hS hv' hw'))
    | exact Or.inr (N_unique hS hu' hw')

/-- ✱234·203. \[\begin{align}&\vdash :\text{Hp}*234·2.P\overline{R} _{\text{os}}Q\in 1.\supset .\\ &\text{os}(P,Q)ʻP\in 1.\text{os}(P,Q)ʻR = \iota ʻ\text{max}_{P}ʻ(P\overline{R} _{\text{sc}}Q)=\iota ʻ\text{min}_{P}ʻ(\breve{P} \overline{R} _{\text{sc}}Q)=P\overline{R} _{\text{os}}Q\\ &[*231·193·103.*205·68.*234·2]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `os(P,Q)'P ∈ 1` for
`os(P,Q)'R ∈ 1`. The chain of four is the conjunction of its three links. -/
theorem pm234_203 :
    ((po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ anc Q ∈ connex) ∧ osBar P R Q ∈ one →
      osPQ P Q R ∈ one ∧
        ((Desc (maxP P) (scBar P R Q) (fun m => osPQ P Q R = ι m) ∧
            Desc (maxP P) (scBar P R Q)
              (fun m => Desc (minP P) (scBar P˘ R Q) (fun n => ι m = ι n))) ∧
          Desc (minP P) (scBar P˘ R Q) (fun n => ι n = osBar P R Q)) := by
  rintro ⟨⟨⟨hS, hR⟩, hc⟩, h1⟩
  obtain ⟨x0, hx0⟩ := mem_one_iff.1 h1
  have hm := max_sc_of_os hS hx0
  have hS' : po P˘ ∈ Ser := by
    rw [po_cnv_eq]
    exact Ser_cnv hS
  have hx0' : ∀ z, z ∈ osBar P˘ R Q ↔ z = x0 := fun z => by rw [osBar_cnv]; exact hx0 z
  have hn : ∀ n, minP P n (scBar P˘ R Q) ↔ n = x0 := max_sc_of_os hS' hx0'
  have hx0os : x0 ∈ osBar P R Q := (hx0 x0).2 rfl
  have he : osPQ P Q R = ι x0 := by
    ext x
    rw [os_char hS hR hc, hm, hn]
    constructor
    · rintro ((⟨e, -⟩ | ⟨e, -⟩) | ⟨e, -⟩) <;> exact e
    · intro e
      exact Or.inr ⟨e, e⟩
  refine ⟨by rw [he]; exact mem_one_iff.2 ⟨x0, fun z => Iff.rfl⟩, ⟨(TheIs_iff_of_unique hm).2 he,
    (TheIs_iff_of_unique hm).2 ((TheIs_iff_of_unique hn).2 rfl)⟩,
    (TheIs_iff_of_unique hn).2 (Set.ext fun z => (hx0 z).symm)⟩

/-- ✱234·204. \(\vdash :P_{\text{po}}\in \text{Ser}.P\overline{R} _{\text{os}}Q{\sim}\in 0\cup 1.\supset .\text{os}(P,Q)ʻR=\Lambda \quad[*234·103]\) -/
theorem pm234_204 : po P ∈ Ser ∧ osBar P R Q ∉ zero ∪ one → osPQ P Q R = Λ := by
  rintro ⟨hS, hn⟩
  exact eq_null_of fun x hx => hn (pm234_103 ⟨hS, x, hx⟩)

private theorem osBar_null_disj (h0 : osBar P R Q = Λ) {x : α} (h1 : x ∈ scBar P R Q)
    (h2 : x ∈ scBar P˘ R Q) : False := by
  have : x ∈ osBar P R Q := ⟨h1, h2⟩
  rw [h0] at this
  exact not_mem_null this

/-- ✱234·21. \[\begin{align}\vdash :\text{Hp}*234·2.P\overline{R} _{\text{os}}Q = &\Lambda .\supset .\\ &\text{os}(P,Q)ʻR=\overrightarrow{\text{max}}_{P}ʻ(P\overline{R} _{\text{sc}}Q)\cup \overrightarrow{\text{min}}_{P}ʻ(\breve{P} \overline{R} _{\text{sc}}Q)\end{align}\] -/
theorem pm234_21 :
    ((po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ anc Q ∈ connex) ∧ osBar P R Q = Λ →
      osPQ P Q R = refs (maxP P) (scBar P R Q) ∪ refs (minP P) (scBar P˘ R Q) := by
  rintro ⟨⟨⟨hS, hR⟩, hc⟩, h0⟩
  ext x
  rw [os_char hS hR hc]
  constructor
  · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩)
    · exact Or.inr h
    · exact Or.inl h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inl (Or.inr ⟨h, fun h' => osBar_null_disj h0 (maxP_iff.1 h).1.1 h'⟩)
    · exact Or.inl (Or.inl ⟨h, fun h' => osBar_null_disj h0 h' (minP_iff.1 h).1.1⟩)

/-- ✱234·23. \[\begin{align}&\vdash \colon\ldotp \text{Hp}*234·2.P\overline{R} _{\text{os}}Q{\sim}\in 1.\text{os}(P,Q)ʻR\in 1.\supset :\\ P\overline{R} _{\text{os}}Q=\Lambda :&\text{os}(P,Q)ʻR=\iota ʻ\text{max}_{P}ʻ(P\overline{R} _{\text{sc}}Q).{\sim}\text{E}!\text{min}_{P}ʻ(\breve{P} \overline{R} _{\text{sc}}Q).\lor.\\ &\text{os}(P,Q)ʻR = \iota ʻ\text{min}_{P}ʻ(\breve{P} \overline{R} _{\text{sc}}Q).{\sim}\text{E}!\text{max}_{P}ʻ(P\overline{R} _{\text{sc}}Q)\end{align}\]

`P R̄_os Q = Λ : A .∨. B`: the colon makes a product of the first clause with the disjunction. -/
theorem pm234_23 :
    (((po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ anc Q ∈ connex) ∧ osBar P R Q ∉ one) ∧
        osPQ P Q R ∈ one →
      osBar P R Q = Λ ∧
        ((Desc (maxP P) (scBar P R Q) (fun m => osPQ P Q R = ι m) ∧
            ¬EDesc (minP P) (scBar P˘ R Q)) ∨
          (Desc (minP P) (scBar P˘ R Q) (fun n => osPQ P Q R = ι n) ∧
            ¬EDesc (maxP P) (scBar P R Q))) := by
  rintro ⟨⟨⟨⟨hS, hR⟩, hc⟩, hn1⟩, h1⟩
  obtain ⟨t, ht⟩ := mem_one_iff.1 h1
  have h0 : osBar P R Q = Λ := by
    rcases pm234_103 ⟨hS, t, (ht t).2 rfl⟩ with h | h
    · exact h
    · exact absurd h hn1
  have e := pm234_21 ⟨⟨⟨hS, hR⟩, hc⟩, h0⟩
  have hte : osPQ P Q R = ι t := Set.ext ht
  refine ⟨h0, ?_⟩
  have htT : t ∈ osPQ P Q R := (ht t).2 rfl
  rw [e] at htT
  rcases htT with hm | hn
  · left
    have hmu : ∀ m, maxP P m (scBar P R Q) ↔ m = t :=
      fun m => ⟨fun h => M_unique hS h hm, fun e => e ▸ hm⟩
    refine ⟨(TheIs_iff_of_unique hmu).2 hte, fun ⟨n, hn⟩ => ?_⟩
    have hnT : n ∈ osPQ P Q R := by rw [e]; exact Or.inr ((hn n).2 rfl)
    have hnt : n = t := (ht n).1 hnT
    subst hnt
    exact osBar_null_disj h0 (maxP_iff.1 hm).1.1 (minP_iff.1 ((hn n).2 rfl)).1.1
  · right
    have hnu : ∀ m, minP P m (scBar P˘ R Q) ↔ m = t :=
      fun m => ⟨fun h => N_unique hS h hn, fun e => e ▸ hn⟩
    refine ⟨(TheIs_iff_of_unique hnu).2 hte, fun ⟨m, hm⟩ => ?_⟩
    have hmT : m ∈ osPQ P Q R := by rw [e]; exact Or.inl ((hm m).2 rfl)
    have hmt : m = t := (ht m).1 hmT
    subst hmt
    exact osBar_null_disj h0 (maxP_iff.1 ((hm m).2 rfl)).1.1 (minP_iff.1 hn).1.1

/-- The partition of `C'P` by the two limiting sections, when the oscillation is null. -/
private theorem part_of_null (hS : po P ∈ Ser) (hR : R ʻʻ fld Q ⊆ fld P) (hc : anc Q ∈ connex)
    (h0 : osBar P R Q = Λ) (u : α) :
    u ∈ scBar P˘ R Q ↔ u ∈ fld P ∧ u ∉ scBar P R Q := by
  have hU := pm231_22 ⟨⟨connex_anc_of_po (Ser_connex hS), hc⟩, hR⟩
  constructor
  · intro hu
    exact ⟨by rw [hU]; exact Or.inr hu, fun h => osBar_null_disj h0 h hu⟩
  · rintro ⟨huP, huA⟩
    rw [hU] at huP
    exact huP.resolve_left huA

/-- For a section `A` without maximum whose complement `B` has a minimum `t`, `t` is the limit
of `A`. -/
private theorem limax_of_min_compl {A B : Set α} {t : α} (hS : P ∈ Ser) (hsect : A ∈ sect P)
    (hB : ∀ u, u ∈ B ↔ u ∈ fld P ∧ u ∉ A) (ht : minP P t B) (hnm : ¬∃ m, maxP P m A) (b : α) :
    limaxP P b A ↔ b = t := by
  obtain ⟨⟨hirr, -⟩, hcon⟩ := Ser_parts hS
  rw [minP_iff] at ht
  obtain ⟨⟨htB, htP⟩, hmin⟩ := ht
  have F : ∀ s u, s ∈ A → u ∈ B → P s u := by
    intro s u hs hu
    obtain ⟨huP, huA⟩ := (hB u).1 hu
    rcases hcon s u (hsect.1 hs) huP with (h | e) | h
    · exact h
    · exact absurd (e ▸ hs) huA
    · exact absurd (hsect.2 ⟨s, hs, h⟩) huA
  have hseq : seqP P t A := by
    rw [seqP_iff]
    refine ⟨⟨fun s hs => F s t hs.1 htB, htP⟩, fun z hz hzt => ?_⟩
    by_cases hzA : z ∈ A
    · exact hirr z (hz z ⟨hzA, fld_of_left hzt⟩)
    · exact hmin z ((hB z).2 ⟨fld_of_left hzt, hzA⟩) hzt
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact absurd ⟨b, h⟩ hnm
    · exact seqP_unique (Ser_connex hS) h hseq
  · intro e
    exact Or.inr ⟨e ▸ hseq, hnm⟩

/-- For a section `A` with maximum `t` whose complement `B` has no minimum, `t` is the lower limit
of `B`. -/
private theorem limin_of_max_compl {A B : Set α} {t : α} (hS : P ∈ Ser) (hsect : A ∈ sect P)
    (hB : ∀ u, u ∈ B ↔ u ∈ fld P ∧ u ∉ A) (ht : maxP P t A) (hnm : ¬∃ n, minP P n B) (b : α) :
    liminP P b B ↔ b = t := by
  rcases cut_limax hS hsect hB (Or.inl ht) with h | ⟨n, h, hP1⟩
  · exact h b
  · exfalso
    rcases (h n).2 rfl with hm | ⟨hp, -⟩
    · exact hnm ⟨n, hm⟩
    · rw [P1_iff_of_transR (Ser_transR hS) (Ser_rlJ hS)] at hP1
      have hnB : n ∈ B := (hB n).2 ⟨fld_of_right hP1.1, fun hnA => (maxP_iff.1 ht).2 n hnA hP1.1⟩
      rw [precP_iff] at hp
      exact (Ser_parts hS).1.1 n (hp.1.1 n ⟨hnB, fld_of_right hP1.1⟩)

private theorem Ser_po {P : α → α → Prop} (hS : P ∈ Ser) : po P ∈ Ser := by
  rw [po_eq_of_transR (Ser_transR hS)]
  exact hS

/-- `max_P'A P_1 min_P'B` for the two limiting sections when the oscillation is null. -/
private theorem P1_max_min (hS : po P ∈ Ser) (hR : R ʻʻ fld Q ⊆ fld P) (hc : anc Q ∈ connex)
    (h0 : osBar P R Q = Λ) {m n : α} (hm : maxP P m (scBar P R Q)) (hn : minP P n (scBar P˘ R Q)) :
    P1 P m n := by
  have hpart := part_of_null hS hR hc h0
  obtain ⟨hirr, hcon⟩ := poSer hS
  have hmA := (maxP_iff.1 hm).1.1
  have hnB := (minP_iff.1 hn).1.1
  have hmP := (maxP_iff.1 hm).1.2
  have hnP := (minP_iff.1 hn).1.2
  have hmn : m ≠ n := fun e => osBar_null_disj h0 hmA (e ▸ hnB)
  rw [P1_iff]
  refine ⟨m, n, hmn, Set.ext fun z => ⟨fun ⟨hmz, hzn⟩ => ?_, ?_⟩⟩
  · by_cases hzA : z ∈ scBar P R Q
    · left
      rcases anc_iff_po.1 hmz with ⟨e, -⟩ | hp
      · exact e.symm
      · exfalso
        rw [po_iff_transGen] at hp
        obtain ⟨c, hmc, hcz⟩ := Relation.TransGen.head'_iff.1 hp
        exact (maxP_iff.1 hm).2 c
          (scBar_down hzA (anc_iff_reflTransGen.2 ⟨fld_of_right hmc, hcz⟩)) hmc
    · right
      have hzB : z ∈ scBar P˘ R Q := (hpart z).2 ⟨anc_right hmz, hzA⟩
      rcases anc_iff_po.1 hzn with ⟨e, -⟩ | hp
      · exact e
      · exfalso
        rw [po_iff_transGen] at hp
        obtain ⟨c, hzc, hcn⟩ := Relation.TransGen.tail'_iff.1 hp
        exact (minP_iff.1 hn).2 c
          (scBar_cnv_up hzB (anc_iff_reflTransGen.2 ⟨anc_left hzn, hzc⟩)) hcn
  · rintro (rfl | rfl)
    · refine ⟨anc_rfl hmP, ?_⟩
      rcases hcon z n hmP hnP with h | h
      · exact h
      · exact absurd (scBar_cnv_up hnB (anc_of_po h)) (fun h' => osBar_null_disj h0 hmA h')
    · refine ⟨?_, anc_rfl hnP⟩
      rcases hcon m z hmP hnP with h | h
      · exact h
      · exact absurd (scBar_cnv_up hnB (anc_of_po h)) (fun h' => osBar_null_disj h0 hmA h')

/-- ✱234·24. \[\begin{align}&\vdash \colon\ldotp P \in \text{Ser}. Q_{*} \in \text{connex} . RʻʻCʻQ \subset CʻP . \supset :\\ &\text{os}(P,Q)ʻR \in 1 . \supset . \text{os}(P,Q)ʻR = \iota ʻ\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q) = \iota ʻ\text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q)\end{align}\] -/
theorem pm234_24 :
    (P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P →
      (osPQ P Q R ∈ one →
        Desc (limaxP P) (scBar P R Q) (fun l => osPQ P Q R = ι l) ∧
          Desc (limaxP P) (scBar P R Q)
            (fun l => Desc (liminP P) (scBar P˘ R Q) (fun m => ι l = ι m))) := by
  rintro ⟨⟨hS, hc⟩, hR⟩ h1
  have hpo := Ser_po hS
  obtain ⟨t, ht⟩ := mem_one_iff.1 h1
  have hte : osPQ P Q R = ι t := Set.ext ht
  suffices key : (∀ b, limaxP P b (scBar P R Q) ↔ b = t) ∧
      ∀ b, liminP P b (scBar P˘ R Q) ↔ b = t by
    exact ⟨(TheIs_iff_of_unique key.1).2 hte,
      (TheIs_iff_of_unique key.1).2 ((TheIs_iff_of_unique key.2).2 rfl)⟩
  rcases pm234_103 ⟨hpo, t, (ht t).2 rfl⟩ with h0 | h1'
  · have h0' : osBar P R Q = Λ := h0
    have hpart := part_of_null hpo hR hc h0'
    have htT : t ∈ osPQ P Q R := (ht t).2 rfl
    rw [pm234_21 ⟨⟨⟨hpo, hR⟩, hc⟩, h0'⟩] at htT
    · rcases htT with hm | hn
      · have hmu : ∀ m, maxP P m (scBar P R Q) ↔ m = t :=
          fun m => ⟨fun h => M_unique hpo h hm, fun e => e ▸ hm⟩
        have hnomin : ¬∃ n, minP P n (scBar P˘ R Q) := by
          rintro ⟨n, hn⟩
          have hP1 := P1_max_min hpo hR hc h0' hm hn
          have hnT : n ∈ osPQ P Q R := by
            rw [pm234_21 ⟨⟨⟨hpo, hR⟩, hc⟩, h0'⟩]
            exact Or.inr hn
          have := (ht n).1 hnT
          subst this
          exact osBar_null_disj h0' (maxP_iff.1 hm).1.1 (minP_iff.1 hn).1.1
        exact ⟨limax_of_max hmu, limin_of_max_compl hS pm231_13 hpart hm hnomin⟩
      · have hnu : ∀ m, minP P m (scBar P˘ R Q) ↔ m = t :=
          fun m => ⟨fun h => N_unique hpo h hn, fun e => e ▸ hn⟩
        have hnomax : ¬∃ m, maxP P m (scBar P R Q) := by
          rintro ⟨m, hm⟩
          have hmT : m ∈ osPQ P Q R := by
            rw [pm234_21 ⟨⟨⟨hpo, hR⟩, hc⟩, h0'⟩]
            exact Or.inl hm
          have := (ht m).1 hmT
          subst this
          exact osBar_null_disj h0' (maxP_iff.1 hm).1.1 (minP_iff.1 hn).1.1
        exact ⟨limax_of_min_compl hS pm231_13 hpart hn hnomax, limin_of_min hnu⟩
  · obtain ⟨-, ⟨⟨hd1, -⟩, -⟩⟩ := pm234_203 ⟨⟨⟨hpo, hR⟩, hc⟩, h1'⟩
    obtain ⟨x0, hx0⟩ := mem_one_iff.1 h1'
    have hm := max_sc_of_os hpo hx0
    have hS' : po P˘ ∈ Ser := by
      rw [po_cnv_eq]
      exact Ser_cnv hpo
    have hx0' : ∀ z, z ∈ osBar P˘ R Q ↔ z = x0 := fun z => by rw [osBar_cnv]; exact hx0 z
    have hn : ∀ n, minP P n (scBar P˘ R Q) ↔ n = x0 := max_sc_of_os hS' hx0'
    have hte' : osPQ P Q R = ι x0 := (TheIs_iff_of_unique hm).1 hd1
    have htx : t = x0 := by
      have : t ∈ ι x0 := hte' ▸ (ht t).2 rfl
      exact this
    subst htx
    exact ⟨limax_of_max hm, limin_of_min hn⟩

/-- ✱234·241. \(\vdash : \text{Hp} *234·2 . \text{os}(P,Q)ʻR \in 2. \supset . P\overline{R} _{\text{os}}Q = \Lambda\) -/
theorem pm234_241 :
    ((po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ anc Q ∈ connex) ∧ osPQ P Q R ∈ two →
      osBar P R Q = Λ := by
  rintro ⟨h, h2⟩
  obtain ⟨u, v, huv, he⟩ := h2
  have hu : u ∈ osPQ P Q R := by rw [he]; exact Or.inl rfl
  rcases pm234_103 ⟨h.1.1, u, hu⟩ with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨h1', -⟩ := pm234_203 ⟨h, h1⟩
    obtain ⟨t, ht⟩ := mem_one_iff.1 h1'
    have hv : v ∈ osPQ P Q R := by rw [he]; exact Or.inr rfl
    exact huv (((ht u).1 hu).trans ((ht v).1 hv).symm)

/-- ✱234·242. \[\begin{align}&\vdash : \text{Hp} *234·2. \text{os}(P,Q)ʻR \in 2. \supset .\\ &\text{os}(P,Q)ʻR = \iota ʻ\text{max}_{P}ʻ(P\overline{R} _{\text{sc}}Q)\cup \iota ʻ\text{min}_{P}ʻ(\breve{P} \overline{R} _{\text{sc}}Q) . \text{max}_{P}ʻ(P\overline{R} _{\text{sc}}Q)P_{1} \text{min}_{P}ʻ(\breve{P} \overline{R} _{\text{sc}}Q)\end{align}\] -/
theorem pm234_242 :
    ((po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ anc Q ∈ connex) ∧ osPQ P Q R ∈ two →
      Desc (maxP P) (scBar P R Q)
          (fun m => Desc (minP P) (scBar P˘ R Q) (fun n => osPQ P Q R = ι m ∪ ι n)) ∧
        Desc (maxP P) (scBar P R Q)
          (fun m => Desc (minP P) (scBar P˘ R Q) (fun n => P1 P m n)) := by
  rintro ⟨⟨⟨hS, hR⟩, hc⟩, h2⟩
  have h0 := pm234_241 ⟨⟨⟨hS, hR⟩, hc⟩, h2⟩
  have e := pm234_21 ⟨⟨⟨hS, hR⟩, hc⟩, h0⟩
  obtain ⟨u, v, huv, he⟩ := h2
  have hu : u ∈ osPQ P Q R := by rw [he]; exact Or.inl rfl
  have hv : v ∈ osPQ P Q R := by rw [he]; exact Or.inr rfl
  rw [e] at hu hv
  -- one of `u, v` is the maximum, the other the minimum
  obtain ⟨m, n, hm, hn, hmn⟩ : ∃ m n, maxP P m (scBar P R Q) ∧ minP P n (scBar P˘ R Q) ∧
      ((m = u ∧ n = v) ∨ (m = v ∧ n = u)) := by
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact absurd (M_unique hS hu hv) huv
    · exact ⟨u, v, hu, hv, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, u, hv, hu, Or.inr ⟨rfl, rfl⟩⟩
    · exact absurd (N_unique hS hu hv) huv
  have hmu : ∀ b, maxP P b (scBar P R Q) ↔ b = m :=
    fun b => ⟨fun h => M_unique hS h hm, fun e => e ▸ hm⟩
  have hnu : ∀ b, minP P b (scBar P˘ R Q) ↔ b = n :=
    fun b => ⟨fun h => N_unique hS h hn, fun e => e ▸ hn⟩
  refine ⟨(TheIs_iff_of_unique hmu).2 ((TheIs_iff_of_unique hnu).2 ?_),
    (TheIs_iff_of_unique hmu).2 ((TheIs_iff_of_unique hnu).2 (P1_max_min hS hR hc h0 hm hn))⟩
  rw [he]
  rcases hmn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Set.union_comm _ _

/-- ✱234·243. \[\begin{align}\vdash : \text{Hp} *234·24 . \exists ! &\text{os}(P,Q)ʻR. \supset .\\ &\text{E}! \text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q). \text{E}! \text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q)\end{align}\]

"Hp ✱234·24" is `(P ∈ Ser ∧ Q_* ∈ connex) ∧ R''C'Q ⊂ C'P`. -/
theorem pm234_243 :
    ((P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P) ∧ (osPQ P Q R).Nonempty →
      EDesc (limaxP P) (scBar P R Q) ∧ EDesc (liminP P) (scBar P˘ R Q) := by
  rintro ⟨⟨⟨hS, hc⟩, hR⟩, t, ht⟩
  have hpo := Ser_po hS
  rcases pm234_103 ⟨hpo, t, ht⟩ with h0 | h1
  · have h0' : osBar P R Q = Λ := h0
    have hpart := part_of_null hpo hR hc h0'
    rw [pm234_21 ⟨⟨⟨hpo, hR⟩, hc⟩, h0'⟩] at ht
    rcases ht with hm | hn
    · have hl : limaxP P t (scBar P R Q) := Or.inl hm
      refine ⟨⟨t, limax_val (Ser_connex hS) hl⟩, ?_⟩
      rcases cut_limax hS pm231_13 hpart hl with h | ⟨n, h, -⟩
      · exact ⟨t, h⟩
      · exact ⟨n, h⟩
    · have hnu : ∀ b, minP P b (scBar P˘ R Q) ↔ b = t :=
        fun b => ⟨fun h => N_unique hpo h hn, fun e => e ▸ hn⟩
      refine ⟨?_, ⟨t, limin_of_min hnu⟩⟩
      by_cases hmax : ∃ m, maxP P m (scBar P R Q)
      · obtain ⟨m, hm⟩ := hmax
        exact ⟨m, limax_val (Ser_connex hS) (Or.inl hm)⟩
      · exact ⟨t, limax_of_min_compl hS pm231_13 hpart hn hmax⟩
  · obtain ⟨x0, hx0⟩ := mem_one_iff.1 h1
    have hS' : po P˘ ∈ Ser := by
      rw [po_cnv_eq]
      exact Ser_cnv hpo
    have hx0' : ∀ z, z ∈ osBar P˘ R Q ↔ z = x0 := fun z => by rw [osBar_cnv]; exact hx0 z
    exact ⟨⟨x0, limax_of_max (max_sc_of_os hpo hx0)⟩, ⟨x0, limin_of_min (max_sc_of_os hS' hx0')⟩⟩

private theorem Ser_of_dense_po {P : α → α → Prop} (hS : po P ∈ Ser) (hd : rsq P = P) :
    P ∈ Ser := by
  have htr : P ∈ transR := fun x z h => by rw [hd] at h; exact h
  rw [← po_eq_of_transR htr]
  exact hS

/-- ✱234·244. \(\vdash : \text{Hp} *234·2 . P^{2} = P. \supset . \text{os}(P,Q)ʻR \in 0 \cup 1\) -/
theorem pm234_244 :
    ((po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ anc Q ∈ connex) ∧ rsq P = P →
      osPQ P Q R ∈ zero ∪ one := by
  rintro ⟨h, hd⟩
  rcases pm234_202 h with h01 | h2
  · exact h01
  · exfalso
    obtain ⟨m, -, n, -, hP1⟩ := (pm234_242 ⟨h, h2⟩).2
    exact P1_empty_of_dense (Ser_of_dense_po h.1.1 hd) hd m n hP1

/-- ✱234·25. \[\begin{align}\vdash : \text{Hp} *234·2. P^{2} &= P. \exists ! \text{os}(P,Q)ʻR . \supset .\\ &\text{os}(P,Q)ʻR = \iota ʻ\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q) = \iota ʻ\text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q) &[*234·244·24]\end{align}\] -/
theorem pm234_25 :
    (((po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ anc Q ∈ connex) ∧ rsq P = P) ∧
        (osPQ P Q R).Nonempty →
      Desc (limaxP P) (scBar P R Q) (fun l => osPQ P Q R = ι l) ∧
        Desc (limaxP P) (scBar P R Q)
          (fun l => Desc (liminP P) (scBar P˘ R Q) (fun m => ι l = ι m)) := by
  rintro ⟨⟨⟨⟨hS, hR⟩, hc⟩, hd⟩, hne⟩
  have hS' := Ser_of_dense_po hS hd
  rcases pm234_244 ⟨⟨⟨hS, hR⟩, hc⟩, hd⟩ with h0 | h1
  · exfalso
    obtain ⟨x, hx⟩ := hne
    rw [show osPQ P Q R = Λ from h0] at hx
    exact not_mem_null hx
  · exact pm234_24 ⟨⟨hS', hc⟩, hR⟩ h1

/-- ✱234·251. \[\begin{align}&\vdash :\text{Hp}*234·24.\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q)=\text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q).\supset .\\ &\text{os}(P,Q)ʻR=\iota ʻ\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q)=\iota ʻ\text{min}_{P}ʻ\text{sc}(P,Q)ʻR=\iota ʻ\text{max}_{P}ʻ\text{sc}(\breve{P} ,Q)ʻR\end{align}\] -/
theorem pm234_251 :
    ((P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P) ∧
        Desc (limaxP P) (scBar P R Q)
          (fun l => Desc (liminP P) (scBar P˘ R Q) (fun m => l = m)) →
      (Desc (limaxP P) (scBar P R Q) (fun l => osPQ P Q R = ι l) ∧
          Desc (limaxP P) (scBar P R Q)
            (fun l => Desc (minP P) (scPQ P Q R) (fun m => ι l = ι m))) ∧
        Desc (minP P) (scPQ P Q R)
          (fun m => Desc (maxP P) (scPQ P˘ Q R) (fun n => ι m = ι n)) := by
  rintro ⟨⟨⟨hS, hc⟩, hR⟩, l, hl, m, hm, rfl⟩
  have h182 := pm234_182 ⟨⟨hS, hc⟩, hR⟩
  have hR' : R ʻʻ fld Q ⊆ fld P˘ := by
    rw [fld_cnv]
    exact hR
  have h182' := pm234_182 (P := P˘) ⟨⟨Ser_cnv hS, hc⟩, hR'⟩
  have hmin : ∀ b, minP P b (scPQ P Q R) ↔ b = l := fun b => by
    have : b ∈ refs (minP P) (scPQ P Q R) ↔ b ∈ refs (limaxP P) (scBar P R Q) := by rw [h182]
    exact this.trans (hl b)
  have hmax : ∀ b, maxP P b (scPQ P˘ Q R) ↔ b = l := fun b => by
    have : b ∈ refs (minP P˘) (scPQ P˘ Q R) ↔ b ∈ refs (limaxP P˘) (scBar P˘ R Q) := by
      rw [h182']
    refine this.trans ?_
    show limaxP P˘ b _ ↔ _
    rw [← liminP_eq_limaxP_cnv]
    exact hm b
  obtain ⟨⟨hirr, -⟩, hcon⟩ := Ser_parts hS
  have hos : osPQ P Q R = ι l := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      have hl1 := (minP_iff.1 ((hmin l).2 rfl))
      have hl2 := (maxP_iff.1 ((hmax l).2 rfl))
      rcases hcon x l (mem_scPQ.1 h1).1 hl1.1.2 with (h | e) | h
      · exact absurd h (hl1.2 x h1)
      · exact e
      · exact absurd h (hl2.2 x h2)
    · intro e
      rw [mem_unitCls] at e
      subst e
      exact ⟨(minP_iff.1 ((hmin x).2 rfl)).1.1, (maxP_iff.1 ((hmax x).2 rfl)).1.1⟩
  exact ⟨⟨(TheIs_iff_of_unique hl).2 hos, (TheIs_iff_of_unique hl).2
    ((TheIs_iff_of_unique hmin).2 rfl)⟩, (TheIs_iff_of_unique hmin).2
    ((TheIs_iff_of_unique hmax).2 rfl)⟩

/-- ✱234·26. \[\begin{align}\vdash \colon\ldotp \text{Hp}*234·2.P^{2}&=P.\supset :\\ \exists !\text{os}(P,Q)ʻR.&\equiv .\text{os}(P,Q)ʻR=\iota ʻ\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q).\\ &\equiv .\text{os}(P,Q)ʻR=\iota ʻ\text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q).\\ &\equiv .\text{os}(P,Q)ʻR=\iota ʻ\text{min}_{P}ʻ\text{sc}(PQ)ʻR.\\ &\equiv .\text{os}(P,Q)ʻR=\iota ʻ\text{max}_{P}ʻ\text{sc}(\breve{P} Q)ʻR.\\ &\equiv .\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q)=\text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q)\\ &[*234·25·251·182.*51·161]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `sc(PQ)'R` and `sc(P̆Q)'R`
for `sc(P,Q)'R` and `sc(P̆,Q)'R`. The chain of six equivalences is the conjunction of its five
links. -/
theorem pm234_26 :
    ((po P ∈ Ser ∧ R ʻʻ fld Q ⊆ fld P) ∧ anc Q ∈ connex) ∧ rsq P = P →
      (((((osPQ P Q R).Nonempty ↔
              Desc (limaxP P) (scBar P R Q) (fun l => osPQ P Q R = ι l)) ∧
            (Desc (limaxP P) (scBar P R Q) (fun l => osPQ P Q R = ι l) ↔
              Desc (liminP P) (scBar P˘ R Q) (fun l => osPQ P Q R = ι l))) ∧
          (Desc (liminP P) (scBar P˘ R Q) (fun l => osPQ P Q R = ι l) ↔
            Desc (minP P) (scPQ P Q R) (fun m => osPQ P Q R = ι m))) ∧
        (Desc (minP P) (scPQ P Q R) (fun m => osPQ P Q R = ι m) ↔
          Desc (maxP P) (scPQ P˘ Q R) (fun m => osPQ P Q R = ι m))) ∧
      (Desc (maxP P) (scPQ P˘ Q R) (fun m => osPQ P Q R = ι m) ↔
        Desc (limaxP P) (scBar P R Q)
          (fun l => Desc (liminP P) (scBar P˘ R Q) (fun m => l = m))) := by
  rintro ⟨⟨⟨hS, hR⟩, hc⟩, hd⟩
  have hS' := Ser_of_dense_po hS hd
  -- every statement of the chain is equivalent to `∃!os(P,Q)'R`
  have ne_of : ∀ (φ : α → Prop), TheIs φ (fun l => osPQ P Q R = ι l) → (osPQ P Q R).Nonempty :=
    fun φ ⟨b, _, e⟩ => ⟨b, by rw [e]; rfl⟩
  have all : (osPQ P Q R).Nonempty →
      ((Desc (limaxP P) (scBar P R Q) (fun l => osPQ P Q R = ι l) ∧
          Desc (liminP P) (scBar P˘ R Q) (fun l => osPQ P Q R = ι l)) ∧
        (Desc (minP P) (scPQ P Q R) (fun m => osPQ P Q R = ι m) ∧
          Desc (maxP P) (scPQ P˘ Q R) (fun m => osPQ P Q R = ι m))) ∧
      Desc (limaxP P) (scBar P R Q)
        (fun l => Desc (liminP P) (scBar P˘ R Q) (fun m => l = m)) := by
    intro hne
    obtain ⟨h1, h2⟩ := pm234_25 ⟨⟨⟨⟨hS, hR⟩, hc⟩, hd⟩, hne⟩
    obtain ⟨l, hl, hos⟩ := h1
    have hl' : ∀ b, limaxP P b (scBar P R Q) ↔ b = l := hl
    obtain ⟨m, hm, hlm⟩ := (TheIs_iff_of_unique hl').1 h2
    have hlm' : l = m := unitCls_injective hlm
    subst hlm'
    have h5 : Desc (limaxP P) (scBar P R Q)
        (fun l => Desc (liminP P) (scBar P˘ R Q) (fun m => l = m)) :=
      (TheIs_iff_of_unique hl').2 ((TheIs_iff_of_unique hm).2 rfl)
    obtain ⟨⟨-, h3⟩, h4⟩ := pm234_251 ⟨⟨⟨hS', hc⟩, hR⟩, h5⟩
    obtain ⟨n, hn, hln⟩ := (TheIs_iff_of_unique hl').1 h3
    have hln' : l = n := unitCls_injective hln
    subst hln'
    obtain ⟨k, hk, hlk⟩ := (TheIs_iff_of_unique hn).1 h4
    have hlk' : l = k := unitCls_injective hlk
    subst hlk'
    exact ⟨⟨⟨(TheIs_iff_of_unique hl').2 hos, (TheIs_iff_of_unique hm).2 hos⟩,
      ⟨(TheIs_iff_of_unique hn).2 hos, (TheIs_iff_of_unique hk).2 hos⟩⟩, h5⟩
  have n5 : Desc (limaxP P) (scBar P R Q)
      (fun l => Desc (liminP P) (scBar P˘ R Q) (fun m => l = m)) → (osPQ P Q R).Nonempty :=
    fun h => ne_of _ (pm234_251 ⟨⟨⟨hS', hc⟩, hR⟩, h⟩).1.1
  exact ⟨⟨⟨⟨⟨fun h => (all h).1.1.1, ne_of _⟩, ⟨fun h => (all (ne_of _ h)).1.1.2,
    fun h => (all (ne_of _ h)).1.1.1⟩⟩, ⟨fun h => (all (ne_of _ h)).1.2.1,
    fun h => (all (ne_of _ h)).1.1.2⟩⟩, ⟨fun h => (all (ne_of _ h)).1.2.2,
    fun h => (all (ne_of _ h)).1.2.1⟩⟩, ⟨fun h => (all (ne_of _ h)).2,
    fun h => (all (n5 h)).1.2.2⟩⟩

/-- ✱234·27. \(\vdash :\text{Hp}*234·24.x\in \text{os}(P,Q)ʻR-\text{ᗡ}ʻP_{1}.\supset .x=\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q)\) -/
theorem pm234_27 {x : α} :
    ((P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P) ∧ x ∈ osPQ P Q R \ codom (P1 P) →
      Desc (limaxP P) (scBar P R Q) (fun l => x = l) := by
  rintro ⟨⟨⟨hS, hc⟩, hR⟩, hx, hx1⟩
  have hpo := Ser_po hS
  refine (TheIs_iff_of_unique (φ := fun l => limaxP P l (scBar P R Q)) ?_).2 rfl
  rcases pm234_103 ⟨hpo, x, hx⟩ with h0 | h1
  · have h0' : osBar P R Q = Λ := h0
    have hpart := part_of_null hpo hR hc h0'
    have hx' := hx
    rw [pm234_21 ⟨⟨⟨hpo, hR⟩, hc⟩, h0'⟩] at hx'
    rcases hx' with hm | hn
    · exact limax_of_max fun m => ⟨fun h => M_unique hpo h hm, fun e => e ▸ hm⟩
    · have hnomax : ¬∃ m, maxP P m (scBar P R Q) := fun ⟨m, hm⟩ =>
        hx1 ⟨m, P1_max_min hpo hR hc h0' hm hn⟩
      exact limax_of_min_compl hS pm231_13 hpart hn hnomax
  · obtain ⟨⟨t, ht⟩, ⟨⟨hd1, -⟩, -⟩⟩ := pm234_203 ⟨⟨⟨hpo, hR⟩, hc⟩, h1⟩
    obtain ⟨x0, hx0⟩ := mem_one_iff.1 h1
    have hm := max_sc_of_os hpo hx0
    have hte' : osPQ P Q R = ι x0 := (TheIs_iff_of_unique hm).1 hd1
    have hxx : x = x0 := by
      have : x ∈ ι x0 := hte' ▸ hx
      exact this
    subst hxx
    exact limax_of_max hm

/-- ✱234·271. \[\begin{align}&\vdash :\text{Hp}.234·24.x\in \text{os}(P,Q)ʻR-\text{D}ʻP_{1}.\supset .x=\text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q)\\ &\left[*234·27 \frac{\breve{P}}{P}\right]\end{align}\]

"Hp.234·24" (so printed) is the hypothesis of ✱234·24. -/
theorem pm234_271 {x : α} :
    ((P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P) ∧ x ∈ osPQ P Q R \ dom (P1 P) →
      Desc (liminP P) (scBar P˘ R Q) (fun l => x = l) := by
  rintro ⟨⟨⟨hS, hc⟩, hR⟩, hx, hx1⟩
  have hR' : R ʻʻ fld Q ⊆ fld P˘ := by
    rw [fld_cnv]
    exact hR
  have hx' : x ∈ osPQ P˘ Q R \ codom (P1 P˘) :=
    ⟨⟨hx.2, hx.1⟩, fun ⟨y, hy⟩ => hx1 ⟨y, P1_cnv.1 hy⟩⟩
  have h := pm234_27 (P := P˘) ⟨⟨⟨Ser_cnv hS, hc⟩, hR'⟩, hx'⟩
  rw [liminP_eq_limaxP_cnv]
  exact h

/-- ✱234·272. \[\begin{align}\vdash :\text{Hp}.*234·24.&x\in \text{os}(P,Q)ʻR-CʻP_{1}.\supset .\\ &x=\text{limax}_Pʻ(P\overline{R} _{\text{sc}}Q)=\text{limin}_Pʻ(\breve{P} \overline{R} _{\text{sc}}Q) \quad[*234·27·271]\end{align}\] -/
theorem pm234_272 {x : α} :
    ((P ∈ Ser ∧ anc Q ∈ connex) ∧ R ʻʻ fld Q ⊆ fld P) ∧ x ∈ osPQ P Q R \ fld (P1 P) →
      Desc (limaxP P) (scBar P R Q) (fun l => x = l) ∧
        Desc (limaxP P) (scBar P R Q)
          (fun l => Desc (liminP P) (scBar P˘ R Q) (fun m => l = m)) := by
  rintro ⟨h, hx, hx1⟩
  have h1 := pm234_27 ⟨h, hx, fun ⟨y, hy⟩ => hx1 ⟨y, Or.inr hy⟩⟩
  have h2 := pm234_271 ⟨h, hx, fun ⟨y, hy⟩ => hx1 ⟨y, Or.inl hy⟩⟩
  obtain ⟨l, hl, rfl⟩ := h1
  obtain ⟨m, hm, rfl⟩ := h2
  exact ⟨⟨x, hl, rfl⟩, (TheIs_iff_of_unique hl).2 ((TheIs_iff_of_unique hm).2 rfl)⟩

/-! ✱234·3–·462: the results above for `Q_* ⥏ α` (`anc Q ⥏ S`) in place of `Q`. -/

private theorem connQ' {S : Set β} (h : anc Q ⥏ S ∈ connex) : anc (anc Q ⥏ S) ∈ connex := by
  rw [anc_ancFres_eq]
  exact h

private theorem RQ' {S : Set β} (h : R ʻʻ (S ∩ fld Q) ⊆ fld P) : R ʻʻ fld (anc Q ⥏ S) ⊆ fld P :=
  fun _ ⟨y, hy, hvy⟩ => h ⟨y, fld_ancFres.1 hy, hvy⟩

private theorem cn_ancFres {S : Set β} {X : Set α} :
    cn (anc Q ⥏ S) R X ↔
      ∃ y, y ∈ S ∩ fld Q ∩ codom R ∧ R ʻʻ (S ∩ rels (anc Q) y) ⊆ X := by
  constructor
  · rintro ⟨y, ⟨hy, hyR⟩, h⟩
    obtain ⟨hyS, hyQ⟩ := fld_ancFres.1 hy
    refine ⟨y, ⟨⟨hyS, hyQ⟩, hyR⟩, fun v ⟨z, ⟨hzS, hyz⟩, hvz⟩ => h ?_⟩
    exact ⟨z, anc_ancFres.2 ⟨⟨hyS, hyz⟩, hzS⟩, hvz⟩
  · rintro ⟨y, ⟨⟨hyS, hyQ⟩, hyR⟩, h⟩
    refine ⟨y, ⟨fld_ancFres.2 ⟨hyS, hyQ⟩, hyR⟩, fun v ⟨z, hyz, hvz⟩ => h ?_⟩
    exact ⟨z, ⟨(anc_ancFres.1 hyz).2, (anc_ancFres.1 hyz).1.2⟩, hvz⟩

/-- ✱234·3. \[\begin{align}&\vdash \colon\ldotp x\in \text{sc}(P,Q_{*}\unicode{x0294f}\alpha )ʻR.\equiv :\\ &x\in CʻP:xP_{\text{po}}w.\supset _{w}.(\exists y).y\in \alpha \cap CʻQ\cap \text{ᗡ}ʻR.Rʻʻ(\alpha \cap \overrightarrow{Q}_{*}ʻy)\subset \overrightarrow{P}_{\text{po}}ʻw\\ &[*234·1]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `Q⃗_*'y` for `Q⃖_*'y` (as in
✱234·301 and ✱232·11). -/
theorem pm234_3 {S : Set β} {x : α} :
    x ∈ scPQ P (anc Q ⥏ S) R ↔
      x ∈ fld P ∧ ∀ w, po P x w →
        ∃ y, y ∈ S ∩ fld Q ∩ codom R ∧ R ʻʻ (S ∩ rels (anc Q) y) ⊆ refs (po P) w := by
  rw [mem_scPQ]
  exact and_congr Iff.rfl (forall_congr' fun w => imp_congr Iff.rfl cn_ancFres)

/-- ✱234·301. \[\begin{align}\vdash \colon\colon Q_{*}\unicode{x0294f}\alpha \in &\text{connex} .\supset \colon\ldotp x\in \text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR\cap \text{D}ʻP\cap \text{ᗡ}ʻP.\equiv :\\ &x\in \text{D}ʻP\cap \text{ᗡ}ʻP:x\in P(z-w).\supset _{z,w}.\\ &(\exists y).y\in \alpha \cap CʻQ\cap \text{ᗡ}ʻR.Rʻʻ(\alpha \cap \overleftarrow{Q}_{*}ʻy)\subset P(z-w)\\ [*234·12]\end{align}\] -/
theorem pm234_301 {S : Set β} {x : α} :
    anc Q ⥏ S ∈ connex →
      (x ∈ osPQ P (anc Q ⥏ S) R ∩ dom P ∩ codom P ↔
        x ∈ dom P ∩ codom P ∧ ∀ z w, x ∈ itvOO P z w →
          ∃ y, y ∈ S ∩ fld Q ∩ codom R ∧ R ʻʻ (S ∩ rels (anc Q) y) ⊆ itvOO P z w) := by
  intro hc
  rw [pm234_12 (connQ' hc)]
  exact and_congr Iff.rfl (forall_congr' fun z => forall_congr' fun w =>
    imp_congr Iff.rfl cn_ancFres)

/-- ✱234·31. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.Q_{*}\unicode{x0294f}\alpha \in \text{connex} .Rʻʻ(\alpha \cap CʻQ)\subset CʻP.\supset .\\ &CʻP-\text{sc}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=CʻP\cap pʻ\overrightarrow{P}_{\text{po}}ʻʻ\text{sc}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=Pʻʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha \\ &[*234·174]\end{align}\]

The chain of three is the conjunction of its two links. -/
theorem pm234_31 {S : Set β} :
    (po P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P →
      fld P \ scPQ P (anc Q ⥏ S) R = fld P ∩ prodCls (Rfwd (po P) ʻʻ scPQ P (anc Q ⥏ S) R) ∧
        fld P ∩ prodCls (Rfwd (po P) ʻʻ scPQ P (anc Q ⥏ S) R) = P ʻʻ scFun P R Q S :=
  fun ⟨⟨hS, hc⟩, hR⟩ => by
    have := pm234_174 ⟨⟨hS, connQ' hc⟩, RQ' hR⟩
    exact ⟨pm234_172 hS, this.1⟩

/-- ✱234·311. \[\begin{align}\vdash :\text{Hp}*234·31.\supset .CʻP=&\text{sc}(P,Q_{*}\unicode{x0294f}\alpha )ʻR\cup Pʻʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha .\\ &\text{sc}(P,Q_{*}\unicode{x0294f}\alpha )ʻR\cap Pʻʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha =\Lambda .\\ &\text{sc}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=CʻP-Pʻʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha\\ &[*234·18]\end{align}\] -/
theorem pm234_311 {S : Set β} :
    (po P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P →
      (fld P = scPQ P (anc Q ⥏ S) R ∪ P ʻʻ scFun P R Q S ∧
          scPQ P (anc Q ⥏ S) R ∩ P ʻʻ scFun P R Q S = Λ) ∧
        scPQ P (anc Q ⥏ S) R = fld P \ P ʻʻ scFun P R Q S :=
  fun ⟨⟨hS, hc⟩, hR⟩ => pm234_18 ⟨⟨hS, connQ' hc⟩, RQ' hR⟩

private theorem desc_lmxc {S : Set β} {ψ : α → Prop} :
    Desc (lmx P˘ R Q) S ψ ↔ Desc (liminP P) (scFun P˘ R Q S) ψ := by
  rw [desc_lmx, liminP_eq_limaxP_cnv]

private theorem desc_rlimc {a : β} {ψ : α → Prop} :
    Desc (rlim R P˘ Q) a ψ ↔ Desc (liminP P) (scFun P˘ R Q (refs Q a)) ψ := by
  rw [desc_rlim, liminP_eq_limaxP_cnv]

private theorem theIs_congr {φ ψ ψ' : α → Prop} (h : ∀ x, ψ x ↔ ψ' x) :
    TheIs φ ψ ↔ TheIs φ ψ' :=
  exists_congr fun b => and_congr Iff.rfl (h b)

private theorem vals_of {A B X : Set α}
    (h : Desc (limaxP P) A (fun l => X = ι l) ∧
      Desc (limaxP P) A (fun l => Desc (liminP P) B (fun m => ι l = ι m))) :
    ∃ l, ((∀ b, limaxP P b A ↔ b = l) ∧ ∀ b, liminP P b B ↔ b = l) ∧ X = ι l := by
  obtain ⟨⟨l, hl, hX⟩, h2⟩ := h
  obtain ⟨m, hm, e⟩ := (TheIs_iff_of_unique hl).1 h2
  have : l = m := unitCls_injective e
  subst this
  exact ⟨l, ⟨hl, hm⟩, hX⟩

/-- ✱234·312. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.Q_{*}&\unicode{x0294f}\alpha \in \text{connex} .Rʻʻ(\alpha \cap CʻQ)\subset CʻP.\supset :\\ &\text{E}!(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\equiv .\text{E}!\text{min}_{P}ʻ\text{sc}(P,Q_{*}\unicode{x0294f}\alpha )ʻR.\\ &\equiv .(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =\text{min}_{P}ʻ\text{sc}(P,Q_{*}\unicode{x0294f}\alpha )ʻR\\ &[*234·182]\end{align}\]

The chain of three is the conjunction of its two links. -/
theorem pm234_312 {S : Set β} :
    (P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P →
      (EDesc (lmx P R Q) S ↔ EDesc (minP P) (scPQ P (anc Q ⥏ S) R)) ∧
        (EDesc (minP P) (scPQ P (anc Q ⥏ S) R) ↔
          Desc (lmx P R Q) S (fun l => Desc (minP P) (scPQ P (anc Q ⥏ S) R) (fun m => l = m))) := by
  rintro ⟨⟨hS, hc⟩, hR⟩
  have h182 := pm234_182 ⟨⟨hS, connQ' hc⟩, RQ' hR⟩
  have key : ∀ b, lmx P R Q b S ↔ minP P b (scPQ P (anc Q ⥏ S) R) := fun b => by
    rw [lmx_apply]
    have : b ∈ refs (limaxP P) (scBar P R (anc Q ⥏ S)) ↔
        b ∈ refs (minP P) (scPQ P (anc Q ⥏ S) R) := by rw [h182]
    exact this
  have e : (fun b => lmx P R Q b S) = fun b => minP P b (scPQ P (anc Q ⥏ S) R) :=
    funext fun b => propext (key b)
  refine ⟨?_, ⟨fun ⟨m, hm⟩ => ?_, fun h => ?_⟩⟩
  · show EBang (fun b => lmx P R Q b S) ↔ EBang _
    rw [e]
  · exact (TheIs_iff_of_unique (fun b => (key b).trans (hm b))).2 ((TheIs_iff_of_unique hm).2 rfl)
  · obtain ⟨l, -, h'⟩ := h
    exact (TheIs_iff.1 h').1

/-- ✱234·32. \[\begin{align}&\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.Q_{*}\unicode{x0294f}\alpha \in \text{connex}.Rʻʻ(\alpha\cap CʻQ)\subset CʻP.\supset:(P\overline{R} Q)_{\text{os}}ʻ\alpha \in 1.\supset .\\ &\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=(P\overline{R} Q)_{\text{os}}ʻ\alpha =\iota ʻ\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha =\iota ʻ\text{min}_{P}ʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha\\ &[*234·203]\end{align}\]

The chain of four is the conjunction of its three links. -/
theorem pm234_32 {S : Set β} :
    (po P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P →
      (osFun P R Q S ∈ one →
        (osPQ P (anc Q ⥏ S) R = osFun P R Q S ∧
            Desc (maxP P) (scFun P R Q S) (fun m => osFun P R Q S = ι m)) ∧
          Desc (maxP P) (scFun P R Q S)
            (fun m => Desc (minP P) (scFun P˘ R Q S) (fun n => ι m = ι n))) := by
  rintro ⟨⟨hS, hc⟩, hR⟩ h1
  obtain ⟨-, ⟨⟨hd1, hd2⟩, hd3⟩⟩ :=
    pm234_203 (Q := anc Q ⥏ S) ⟨⟨⟨hS, RQ' hR⟩, connQ' hc⟩, h1⟩
  obtain ⟨m, hm, e1⟩ := hd1
  obtain ⟨n, hn, e3⟩ := hd3
  obtain ⟨n', hn', e2⟩ := (TheIs_iff_of_unique hm).1 hd2
  have : n' = n := ((hn n').1 ((hn' n').2 rfl))
  subst this
  have e : osPQ P (anc Q ⥏ S) R = osFun P R Q S := e1.trans (e2.trans e3)
  exact ⟨⟨e, (TheIs_iff_of_unique hm).2 (e2.trans e3).symm⟩, hd2⟩

/-- ✱234·321. \[\begin{align}&\vdash \colon\colon\text{Hp}*234·32.\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR\in 1.\supset \colon\ldotp (P\overline{R} Q)_{\text{os}}ʻ\alpha {\sim}\in 1.\supset :\\ (P\overline{R} Q)_{\text{os}}ʻ\alpha =&\Lambda :\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=\iota ʻ\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha .{\sim}\text{E}!\text{min}_{P}ʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha .\\ &\lor.\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=\iota ʻ\text{min}_{P}ʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha .{\sim}\text{E}!\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha\\ &[*234·23]\end{align}\] -/
theorem pm234_321 {S : Set β} :
    ((po P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧
        osPQ P (anc Q ⥏ S) R ∈ one →
      (osFun P R Q S ∉ one →
        osFun P R Q S = Λ ∧
          ((Desc (maxP P) (scFun P R Q S) (fun m => osPQ P (anc Q ⥏ S) R = ι m) ∧
              ¬EDesc (minP P) (scFun P˘ R Q S)) ∨
            (Desc (minP P) (scFun P˘ R Q S) (fun n => osPQ P (anc Q ⥏ S) R = ι n) ∧
              ¬EDesc (maxP P) (scFun P R Q S)))) :=
  fun ⟨⟨⟨hS, hc⟩, hR⟩, h1⟩ hn1 =>
    pm234_23 (Q := anc Q ⥏ S) ⟨⟨⟨⟨hS, RQ' hR⟩, connQ' hc⟩, hn1⟩, h1⟩

/-- ✱234·322. \[\begin{align}&\vdash :\text{Hp}.*234·312.\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR\in 1.\supset .\\ &\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=\iota ʻ(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =\iota ʻ(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha \quad[*234·24]\end{align}\]

"Hp.✱234·312" (so printed) is the hypothesis of ✱234·312. -/
theorem pm234_322 {S : Set β} :
    ((P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧
        osPQ P (anc Q ⥏ S) R ∈ one →
      Desc (lmx P R Q) S (fun l => osPQ P (anc Q ⥏ S) R = ι l) ∧
        Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => ι l = ι m)) := by
  rintro ⟨⟨⟨hS, hc⟩, hR⟩, h1⟩
  obtain ⟨l, ⟨h1', h2'⟩, hX⟩ := vals_of (pm234_24 (Q := anc Q ⥏ S) ⟨⟨hS, connQ' hc⟩, RQ' hR⟩ h1)
  exact ⟨(TheIs_iff_of_unique (lmx_val h1')).2 hX,
    (TheIs_iff_of_unique (lmx_val h1')).2 ((TheIs_iff_of_unique (lmxc_val h2')).2 rfl)⟩

/-- ✱234·329. \[\begin{align}&\vdash :\text{Hp}*234·32.\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR\in 2.\supset .\\ &\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=\iota ʻ\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}}ʻ\alpha \cup \iota ʻ\text{min}_{P}ʻ(\breve{P}\overline{R} Q)_{\text{sc}}ʻ\alpha .\\ &\{\text{max}_{P}ʻ(P\overline{R} Q)_{\text{sc}\}ʻ\alpha }P_{1}\{\text{min}_{P}ʻ(\breve{P} \overline{R} Q)_{\text{sc}}ʻ\alpha\}\\ &[*234·242]\end{align}\]

**Status.** proved (reading): transcription error: the e-text misplaces a brace in
`{max_P'(P R̄ Q)_sc}'α`. -/
theorem pm234_329 {S : Set β} :
    ((po P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧
        osPQ P (anc Q ⥏ S) R ∈ two →
      Desc (maxP P) (scFun P R Q S) (fun m => Desc (minP P) (scFun P˘ R Q S)
          (fun n => osPQ P (anc Q ⥏ S) R = ι m ∪ ι n)) ∧
        Desc (maxP P) (scFun P R Q S)
          (fun m => Desc (minP P) (scFun P˘ R Q S) (fun n => P1 P m n)) :=
  fun ⟨⟨⟨hS, hc⟩, hR⟩, h2⟩ => pm234_242 (Q := anc Q ⥏ S) ⟨⟨⟨hS, RQ' hR⟩, connQ' hc⟩, h2⟩

/-- ✱234·33. \[\begin{align}\vdash :\text{Hp}&*234·32.P^{2}=P.\exists !\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR.\supset .\\ &\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=\iota ʻ(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =\iota ʻ(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha \quad[*234·25]\end{align}\] -/
theorem pm234_33 {S : Set β} :
    (((po P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧ rsq P = P) ∧
        (osPQ P (anc Q ⥏ S) R).Nonempty →
      Desc (lmx P R Q) S (fun l => osPQ P (anc Q ⥏ S) R = ι l) ∧
        Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => ι l = ι m)) := by
  rintro ⟨⟨⟨⟨hS, hc⟩, hR⟩, hd⟩, hne⟩
  obtain ⟨l, ⟨h1', h2'⟩, hX⟩ :=
    vals_of (pm234_25 (Q := anc Q ⥏ S) ⟨⟨⟨⟨hS, RQ' hR⟩, connQ' hc⟩, hd⟩, hne⟩)
  exact ⟨(TheIs_iff_of_unique (lmx_val h1')).2 hX,
    (TheIs_iff_of_unique (lmx_val h1')).2 ((TheIs_iff_of_unique (lmxc_val h2')).2 rfl)⟩

/-- ✱234·331. \[\begin{align}&\vdash : \text{Hp}*234·312.(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha .\supset .\\ \text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR&=\iota ʻ(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =\iota ʻ(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha \\ &=\iota ʻ\text{min}_{P}ʻ\text{sc}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=\iota ʻ\text{max}_{P}ʻ\text{sc}(\breve{P} ,Q_{*}\unicode{x0294f}\alpha )ʻR\\ &[*234·251]\end{align}\]

The chain of five is the conjunction of its four links. -/
theorem pm234_331 {S : Set β} :
    ((P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧
        Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => l = m)) →
      ((Desc (lmx P R Q) S (fun l => osPQ P (anc Q ⥏ S) R = ι l) ∧
          Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => ι l = ι m))) ∧
          Desc (lmx P˘ R Q) S
            (fun l => Desc (minP P) (scPQ P (anc Q ⥏ S) R) (fun m => ι l = ι m))) ∧
        Desc (minP P) (scPQ P (anc Q ⥏ S) R)
          (fun m => Desc (maxP P) (scPQ P˘ (anc Q ⥏ S) R) (fun n => ι m = ι n)) := by
  rintro ⟨⟨⟨hS, hc⟩, hR⟩, l, hl, m, hm, rfl⟩
  have hl' : ∀ b, limaxP P b (scFun P R Q S) ↔ b = l := fun b => lmx_apply.symm.trans (hl b)
  have hm' : ∀ b, liminP P b (scFun P˘ R Q S) ↔ b = l := fun b => by
    rw [liminP_eq_limaxP_cnv, ← lmx_apply]
    exact hm b
  obtain ⟨⟨hd1, hd2⟩, hd3⟩ := pm234_251 (Q := anc Q ⥏ S) ⟨⟨⟨hS, connQ' hc⟩, RQ' hR⟩,
    (TheIs_iff_of_unique hl').2 ((TheIs_iff_of_unique hm').2 rfl)⟩
  have hX := (TheIs_iff_of_unique hl').1 hd1
  obtain ⟨n, hn, e⟩ := (TheIs_iff_of_unique hl').1 hd2
  have : l = n := unitCls_injective e
  subst this
  refine ⟨⟨⟨(TheIs_iff_of_unique hl).2 hX, (TheIs_iff_of_unique hl).2
    ((TheIs_iff_of_unique hm).2 rfl)⟩, (TheIs_iff_of_unique hm).2
    ((TheIs_iff_of_unique hn).2 rfl)⟩, hd3⟩

/-- ✱234·34. \[\begin{align}&\vdash \colon\ldotp \text{Hp}*234·32.P^{2}=P.\supset :\\ \exists !\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR.&\equiv .\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=\iota ʻ(P\overline{R} Q)_{\text{lmx}}ʻ\alpha .\\ &\equiv .\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR=\iota ʻ(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha .\\ &\equiv .(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha \\ &[*234·26]\end{align}\]

The chain of four equivalences is the conjunction of its three links. -/
theorem pm234_34 {S : Set β} :
    ((po P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧ rsq P = P →
      (((osPQ P (anc Q ⥏ S) R).Nonempty ↔
            Desc (lmx P R Q) S (fun l => osPQ P (anc Q ⥏ S) R = ι l)) ∧
          (Desc (lmx P R Q) S (fun l => osPQ P (anc Q ⥏ S) R = ι l) ↔
            Desc (lmx P˘ R Q) S (fun l => osPQ P (anc Q ⥏ S) R = ι l))) ∧
        (Desc (lmx P˘ R Q) S (fun l => osPQ P (anc Q ⥏ S) R = ι l) ↔
          Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => l = m))) := by
  rintro ⟨⟨⟨hS, hc⟩, hR⟩, hd⟩
  obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩ :=
    pm234_26 (Q := anc Q ⥏ S) ⟨⟨⟨hS, RQ' hR⟩, connQ' hc⟩, hd⟩
  have c5 : Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => l = m)) ↔
      Desc (limaxP P) (scFun P R Q S)
        (fun l => Desc (liminP P) (scFun P˘ R Q S) (fun m => l = m)) := by
    rw [desc_lmx]
    exact theIs_congr fun l => desc_lmxc
  have c2 : Desc (lmx P R Q) S (fun l => osPQ P (anc Q ⥏ S) R = ι l) ↔
      Desc (limaxP P) (scFun P R Q S) (fun l => osPQ P (anc Q ⥏ S) R = ι l) := desc_lmx
  have c3 : Desc (lmx P˘ R Q) S (fun l => osPQ P (anc Q ⥏ S) R = ι l) ↔
      Desc (liminP P) (scFun P˘ R Q S) (fun l => osPQ P (anc Q ⥏ S) R = ι l) := desc_lmxc
  exact ⟨⟨e1.trans c2.symm, c2.trans (e2.trans c3.symm)⟩,
    c3.trans ((e3.trans (e4.trans e5)).trans c5.symm)⟩

/-- ✱234·35. \[\begin{align}&\vdash :\text{Hp}*234·312.x\in \text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR-\text{ᗡ}ʻP_{1}.\supset .x=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha\\ &[*234·27]\end{align}\] -/
theorem pm234_35 {S : Set β} {x : α} :
    ((P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧
        x ∈ osPQ P (anc Q ⥏ S) R \ codom (P1 P) →
      Desc (lmx P R Q) S (fun l => x = l) := by
  rintro ⟨⟨⟨hS, hc⟩, hR⟩, hx⟩
  rw [desc_lmx]
  exact pm234_27 (Q := anc Q ⥏ S) ⟨⟨⟨hS, connQ' hc⟩, RQ' hR⟩, hx⟩

/-- ✱234·351. \[\begin{align}&\vdash :\text{Hp}*234·312.x\in \text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR-\text{D}ʻP_{1}.\supset.x=(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha \\ &\left[*234·35 \frac{\breve{P}}{P}\right]\end{align}\] -/
theorem pm234_351 {S : Set β} {x : α} :
    ((P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧
        x ∈ osPQ P (anc Q ⥏ S) R \ dom (P1 P) →
      Desc (lmx P˘ R Q) S (fun l => x = l) := by
  rintro ⟨⟨⟨hS, hc⟩, hR⟩, hx⟩
  rw [desc_lmxc]
  exact pm234_271 (Q := anc Q ⥏ S) ⟨⟨⟨hS, connQ' hc⟩, RQ' hR⟩, hx⟩

/-- ✱234·352. \[\begin{align}\vdash :\text{Hp}*234·312.x\in &\text{os}(P,Q_{*}\unicode{x0294f}\alpha )ʻR-CʻP_{1}.\supset .\\ &x=(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha \quad[*234·35·351]\end{align}\] -/
theorem pm234_352 {S : Set β} {x : α} :
    ((P ∈ Ser ∧ anc Q ⥏ S ∈ connex) ∧ R ʻʻ (S ∩ fld Q) ⊆ fld P) ∧
        x ∈ osPQ P (anc Q ⥏ S) R \ fld (P1 P) →
      Desc (lmx P R Q) S (fun l => x = l) ∧
        Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => l = m)) := by
  rintro ⟨h, hx, hx1⟩
  have h1 := pm234_35 ⟨h, hx, fun ⟨y, hy⟩ => hx1 ⟨y, Or.inr hy⟩⟩
  have h2 := pm234_351 ⟨h, hx, fun ⟨y, hy⟩ => hx1 ⟨y, Or.inl hy⟩⟩
  obtain ⟨l, hl, rfl⟩ := h1
  obtain ⟨m, hm, rfl⟩ := h2
  exact ⟨⟨x, hl, rfl⟩, (TheIs_iff_of_unique hl).2 ((TheIs_iff_of_unique hm).2 rfl)⟩

/-- ✱234·4. \[\begin{align}&\vdash \colon\ldotp x\in \text{sc}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}_{\text{po}}ʻa)ʻR.\equiv :\\ &x\in CʻP:xP_{\text{po}}w.\supset _{w}.(\exists y).y\in \overrightarrow{Q}_{\text{po}}ʻa\cap \text{ᗡ}ʻR.RʻʻQ(y\unicode{x27dd} a)\subset \overrightarrow{P}_{\text{po}}ʻw\\ &[*234·3.(*121·012)]\end{align}\]

`Q(y⟝a)` is `itvCO Q y a` (✱121·012). -/
theorem pm234_4 {a : β} {x : α} :
    x ∈ scPQ P (anc Q ⥏ refs (po Q) a) R ↔
      x ∈ fld P ∧ ∀ w, po P x w →
        ∃ y, y ∈ refs (po Q) a ∩ codom R ∧ R ʻʻ itvCO Q y a ⊆ refs (po P) w := by
  rw [pm234_3]
  refine and_congr Iff.rfl (forall_congr' fun w => imp_congr Iff.rfl (exists_congr fun y => ?_))
  have e : refs (po Q) a ∩ rels (anc Q) y = itvCO Q y a := Set.inter_comm _ _
  rw [e]
  exact and_congr ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨⟨h1, po_left h1⟩, h3⟩⟩ Iff.rfl

/-- ✱234·41. \[\begin{align}&\vdash \colon\colon Q\in \text{trans}.Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa\in \text{connex} .\supset \colon\ldotp \\ &x\in \text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR\cap \text{D}ʻP\cap \text{ᗡ}ʻP.\equiv :x\in \text{D}ʻP\cap \text{ᗡ}ʻP:\\ &x\in P(z-w).\supset _{z,w}.(\exists y).y\in \overrightarrow{Q}ʻa\cap \text{ᗡ}ʻR.RʻʻQ(y\unicode{x27dd} a)\subset P(z-w)\\ &[*234·301.(*121·012).*201·18]\end{align}\] -/
theorem pm234_41 {a : β} {x : α} :
    Q ∈ transR ∧ anc Q ⥏ refs Q a ∈ connex →
      (x ∈ osPQ P (anc Q ⥏ refs Q a) R ∩ dom P ∩ codom P ↔
        x ∈ dom P ∩ codom P ∧ ∀ z w, x ∈ itvOO P z w →
          ∃ y, y ∈ refs Q a ∩ codom R ∧ R ʻʻ itvCO Q y a ⊆ itvOO P z w) := by
  rintro ⟨htr, hc⟩
  rw [pm234_301 hc]
  have e : ∀ y, refs Q a ∩ rels (anc Q) y = itvCO Q y a := fun y => by
    show refs Q a ∩ rels (anc Q) y = rels (anc Q) y ∩ refs (po Q) a
    rw [po_eq_of_transR htr, Set.inter_comm]
  refine and_congr Iff.rfl (forall_congr' fun z => forall_congr' fun w =>
    imp_congr Iff.rfl (exists_congr fun y => ?_))
  rw [e]
  exact and_congr ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨⟨h1, fld_of_left h1⟩, h3⟩⟩
    Iff.rfl

private theorem RQa {a : β} (hR : R ʻʻ refs Q a ⊆ fld P) : R ʻʻ fld (anc Q ⥏ refs Q a) ⊆ fld P :=
  RQ' fun _ ⟨y, hy, hvy⟩ => hR ⟨y, hy.1, hvy⟩

/-- ✱234·42. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.Q\in &\text{trans}.Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa\in \text{connex} .Rʻʻ\overrightarrow{Q}ʻa\subset CʻP.\supset :\\ &\overrightarrow{R(PQ)}ʻa=\overrightarrow{\text{min}}_{P}ʻ\text{sc}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR \quad[*234·182]\end{align}\]

`R(PQ)⃗'a` is `refs (rlim R P Q) a`. -/
theorem pm234_42 {a : β} :
    ((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P →
      refs (rlim R P Q) a = refs (minP P) (scPQ P (anc Q ⥏ refs Q a) R) := by
  rintro ⟨⟨⟨hS, -⟩, hc⟩, hR⟩
  rw [← pm234_182 (Q := anc Q ⥏ refs Q a) ⟨⟨hS, connQ' hc⟩, RQa hR⟩]
  ext b
  exact rlim_apply

/-- ✱234·421. \[\begin{align}\vdash \colon\ldotp P_{\text{po}}\in &\text{Ser}.Q\in \text{trans}.Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa\in \text{connex} .Rʻʻ\overrightarrow{Q}ʻa\subset CʻP.\supset :\\ &\text{sc}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR=\Lambda .\supset .\overrightarrow{R(PQ)}ʻa=\overrightarrow{B}ʻ\breve{P} \quad[*234·183]\end{align}\] -/
theorem pm234_421 {a : β} :
    ((po P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P →
      (scPQ P (anc Q ⥏ refs Q a) R = Λ → refs (rlim R P Q) a = refs Beg P˘) := by
  rintro ⟨⟨⟨hS, -⟩, hc⟩, hR⟩ h0
  have h := (pm234_183 (Q := anc Q ⥏ refs Q a) ⟨⟨⟨hS, connQ' hc⟩, RQa hR⟩, h0⟩).1
  ext b
  show rlim R P Q b a ↔ Beg b P˘
  rw [rlim_apply]
  show limaxP P b (scBar P R (anc Q ⥏ refs Q a)) ↔ _
  rw [h, limax_fld_iff]

/-- ✱234·422. \[\begin{align}&\vdash :\text{Hp}*234·42.P\in \text{Ded}.\supset .R(PQ)ʻa=\text{limin}_Pʻ\text{sc}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR\\ &[*233·13.*234·42]\end{align}\] -/
theorem pm234_422 {a : β} :
    (((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        P ∈ Ded →
      Desc (rlim R P Q) a
        (fun r => Desc (liminP P) (scPQ P (anc Q ⥏ refs Q a) R) (fun m => r = m)) := by
  rintro ⟨h, hD⟩
  have e := pm234_42 h
  obtain ⟨l, hl⟩ := limax_exists' (Ser_connex h.1.1.1) hD (scFun P R Q (refs Q a))
  have hr : ∀ b, rlim R P Q b a ↔ b = l := rlim_val hl
  have hmin : ∀ b, minP P b (scPQ P (anc Q ⥏ refs Q a) R) ↔ b = l := fun b => by
    have : b ∈ refs (minP P) (scPQ P (anc Q ⥏ refs Q a) R) ↔ b ∈ refs (rlim R P Q) a := by
      rw [e]
    exact this.trans (hr b)
  exact eqDesc hr (limin_of_min hmin)

/-- ✱234·43. \[\begin{align}\vdash :\text{Hp}*234·42.&\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR\in 1.\supset .\\ &\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)=\iota ʻR(PQ)ʻa= \iota ʻR(\breve{P} Q)ʻa \quad[*234·322]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `os(P,Q_*⥏Q⃗'a)` for
`os(P,Q_*⥏Q⃗'a)'R`. The chain of three is the conjunction of its two links. -/
theorem pm234_43 {a : β} :
    ((((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        osPQ P (anc Q ⥏ refs Q a) R ∈ one) →
      Desc (rlim R P Q) a (fun r => osPQ P (anc Q ⥏ refs Q a) R = ι r) ∧
        Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => ι r = ι s)) := by
  rintro ⟨⟨⟨⟨hS, -⟩, hc⟩, hR⟩, h1⟩
  obtain ⟨l, ⟨h1', h2'⟩, hX⟩ :=
    vals_of (pm234_24 (Q := anc Q ⥏ refs Q a) ⟨⟨hS, connQ' hc⟩, RQa hR⟩ h1)
  exact ⟨(TheIs_iff_of_unique (rlim_val h1')).2 hX,
    (TheIs_iff_of_unique (rlim_val h1')).2 ((TheIs_iff_of_unique (rlimc_val h2')).2 rfl)⟩

/-- ✱234·439. \[\begin{align}\vdash :\text{Hp}&*234·421.\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR\in 2.\supset .\\ &\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR=\iota ʻR(PQ)ʻa\cup \iota ʻR(\breve{P} Q)ʻa.\\ &\{R(PQ)ʻa\}P_{1}\{R(\breve{P} Q)ʻa\} \quad[*234·329]\end{align}\] -/
theorem pm234_439 {a : β} :
    ((((po P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        osPQ P (anc Q ⥏ refs Q a) R ∈ two) →
      Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a
          (fun s => osPQ P (anc Q ⥏ refs Q a) R = ι r ∪ ι s)) ∧
        Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => P1 P r s)) := by
  rintro ⟨⟨⟨⟨hS, -⟩, hc⟩, hR⟩, h2⟩
  obtain ⟨hd1, hd2⟩ := pm234_242 (Q := anc Q ⥏ refs Q a) ⟨⟨⟨hS, RQa hR⟩, connQ' hc⟩, h2⟩
  obtain ⟨m, hm, n, hn, e⟩ := hd1
  have hm' : ∀ b, limaxP P b (scFun P R Q (refs Q a)) ↔ b = m := limax_of_max hm
  have hn' : ∀ b, liminP P b (scFun P˘ R Q (refs Q a)) ↔ b = n := limin_of_min hn
  obtain ⟨n', hn'', hP1⟩ := (TheIs_iff_of_unique hm).1 hd2
  have : n' = n := (hn n').1 ((hn'' n').2 rfl)
  subst this
  exact ⟨(TheIs_iff_of_unique (rlim_val hm')).2 ((TheIs_iff_of_unique (rlimc_val hn')).2 e),
    (TheIs_iff_of_unique (rlim_val hm')).2 ((TheIs_iff_of_unique (rlimc_val hn')).2 hP1)⟩

/-- ✱234·44. \[\begin{align}\vdash :\text{Hp}&*234·421.P^{2}=P.\exists !\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR.\supset .\\ &\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR=\iota ʻR(PQ)ʻa=\iota ʻR(\breve{P} Q)ʻa \quad[*234·33]\end{align}\] -/
theorem pm234_44 {a : β} :
    (((((po P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        rsq P = P) ∧ (osPQ P (anc Q ⥏ refs Q a) R).Nonempty) →
      Desc (rlim R P Q) a (fun r => osPQ P (anc Q ⥏ refs Q a) R = ι r) ∧
        Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => ι r = ι s)) := by
  rintro ⟨⟨⟨⟨⟨hS, -⟩, hc⟩, hR⟩, hd⟩, hne⟩
  obtain ⟨l, ⟨h1', h2'⟩, hX⟩ :=
    vals_of (pm234_25 (Q := anc Q ⥏ refs Q a) ⟨⟨⟨⟨hS, RQa hR⟩, connQ' hc⟩, hd⟩, hne⟩)
  exact ⟨(TheIs_iff_of_unique (rlim_val h1')).2 hX,
    (TheIs_iff_of_unique (rlim_val h1')).2 ((TheIs_iff_of_unique (rlimc_val h2')).2 rfl)⟩

/-- ✱234·441. \[\begin{align}\vdash :\text{Hp}*234·42.&R(PQ)ʻa=R(\breve{P} Q)ʻa.\supset .\\ &\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)=\iota ʻR(PQ)ʻa=\iota ʻR(\breve{P} Q)ʻa \quad[*234·331]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `os(P,Q_*⥏Q⃗'a)` for
`os(P,Q_*⥏Q⃗'a)'R`. -/
theorem pm234_441 {a : β} :
    ((((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s))) →
      Desc (rlim R P Q) a (fun r => osPQ P (anc Q ⥏ refs Q a) R = ι r) ∧
        Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => ι r = ι s)) := by
  rintro ⟨⟨⟨⟨hS, -⟩, hc⟩, hR⟩, r, hr, s, hs, rfl⟩
  have hr' : ∀ b, limaxP P b (scFun P R Q (refs Q a)) ↔ b = r :=
    fun b => rlim_apply.symm.trans (hr b)
  have hs' : ∀ b, liminP P b (scFun P˘ R Q (refs Q a)) ↔ b = r := fun b => by
    rw [liminP_eq_limaxP_cnv, ← rlim_apply]
    exact hs b
  obtain ⟨⟨hd1, -⟩, -⟩ := pm234_251 (Q := anc Q ⥏ refs Q a) ⟨⟨⟨hS, connQ' hc⟩, RQa hR⟩,
    eqDesc hr' hs'⟩
  exact ⟨(TheIs_iff_of_unique hr).2 ((TheIs_iff_of_unique hr').1 hd1),
    (TheIs_iff_of_unique hr).2 ((TheIs_iff_of_unique hs).2 rfl)⟩

/-- ✱234·45. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.Q\in \text{trans}.Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa\in \text{connex} .Rʻʻ\overrightarrow{Q}ʻa\subset CʻP.P^{2}=P.\supset :\\ \exists !\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR.&\equiv .\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR=\iota ʻR(PQ)ʻa.\\ &\equiv .\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR=\iota ʻR(\breve{P} Q)ʻa.\\ &\equiv .R(PQ)ʻa=R(\breve{P} Q)ʻa \quad[*234·34]\end{align}\]

The chain of four equivalences is the conjunction of its three links. -/
theorem pm234_45 {a : β} :
    ((((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        rsq P = P) →
      (((osPQ P (anc Q ⥏ refs Q a) R).Nonempty ↔
            Desc (rlim R P Q) a (fun r => osPQ P (anc Q ⥏ refs Q a) R = ι r)) ∧
          (Desc (rlim R P Q) a (fun r => osPQ P (anc Q ⥏ refs Q a) R = ι r) ↔
            Desc (rlim R P˘ Q) a (fun r => osPQ P (anc Q ⥏ refs Q a) R = ι r))) ∧
        (Desc (rlim R P˘ Q) a (fun r => osPQ P (anc Q ⥏ refs Q a) R = ι r) ↔
          Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s))) := by
  rintro ⟨⟨⟨⟨hS, -⟩, hc⟩, hR⟩, hd⟩
  have h := pm234_34 (S := refs Q a) ⟨⟨⟨Ser_po hS, hc⟩, fun v ⟨y, hy, hvy⟩ => hR ⟨y, hy.1, hvy⟩⟩,
    hd⟩
  simp only [desc_rlim_lmx]
  exact h

/-- ✱234·46. \[\begin{align}&\vdash :\text{Hp}*234·42.x\in \text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR-\text{ᗡ}ʻP_1.\supset .x=R(PQ)ʻa\\ &[*234·35]\end{align}\] -/
theorem pm234_46 {a : β} {x : α} :
    ((((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        x ∈ osPQ P (anc Q ⥏ refs Q a) R \ codom (P1 P)) →
      Desc (rlim R P Q) a (fun r => x = r) := by
  rintro ⟨⟨⟨⟨hS, -⟩, hc⟩, hR⟩, hx⟩
  rw [desc_rlim_lmx]
  exact pm234_35 ⟨⟨⟨hS, hc⟩, fun v ⟨y, hy, hvy⟩ => hR ⟨y, hy.1, hvy⟩⟩, hx⟩

/-- ✱234·461. \[\begin{align}&\vdash :\text{Hp}*234·42.x\in \text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR-\text{D}ʻP_1.\supset .x=R(\breve{P} Q)ʻa\\ &\left[*234·46 \frac{\breve{P}}{P}\right]\end{align}\] -/
theorem pm234_461 {a : β} {x : α} :
    ((((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        x ∈ osPQ P (anc Q ⥏ refs Q a) R \ dom (P1 P)) →
      Desc (rlim R P˘ Q) a (fun r => x = r) := by
  rintro ⟨⟨⟨⟨hS, -⟩, hc⟩, hR⟩, hx⟩
  rw [desc_rlim_lmx]
  exact pm234_351 ⟨⟨⟨hS, hc⟩, fun v ⟨y, hy, hvy⟩ => hR ⟨y, hy.1, hvy⟩⟩, hx⟩

/-- ✱234·462. \[\begin{align}\vdash :\text{Hp}*234·42.x\in &\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)ʻR-CʻP_1.\supset .\\ &x=R(PQ)ʻa=R(\breve{P} Q)ʻa \quad[*234·46·461]\end{align}\] -/
theorem pm234_462 {a : β} {x : α} :
    ((((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        x ∈ osPQ P (anc Q ⥏ refs Q a) R \ fld (P1 P)) →
      Desc (rlim R P Q) a (fun r => x = r) ∧
        Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) := by
  rintro ⟨⟨⟨⟨hS, -⟩, hc⟩, hR⟩, hx⟩
  have h := pm234_352 ⟨⟨⟨hS, hc⟩, fun v ⟨y, hy, hvy⟩ => hR ⟨y, hy.1, hvy⟩⟩, hx⟩
  simp only [desc_rlim_lmx]
  exact h

/-- ✱234·5. \(\vdash :a\in \text{ct}(PQ)ʻR.\equiv .Rʻa\in \text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}_{\text{po}}ʻa)ʻR-CʻP_1 \quad[(*234·03)]\) -/
theorem pm234_5 {a : β} :
    a ∈ ct P Q R ↔
      Desc R a (fun v => v ∈ osPQ P (anc Q ⥏ refs (po Q) a) R \ fld (P1 P)) :=
  Iff.rfl

private theorem itvCC_sub_iff {a y : β} {v : α} {X : Set α} (hRa : ∀ u, R u a ↔ u = v)
    (hvX : v ∈ X) : R ʻʻ itvCC Q y a ⊆ X ↔ R ʻʻ itvCO Q y a ⊆ X := by
  constructor
  · rintro h u ⟨t, ⟨hyt, hta⟩, hut⟩
    exact h ⟨t, ⟨hyt, anc_of_po hta⟩, hut⟩
  · rintro h u ⟨t, ⟨hyt, hta⟩, hut⟩
    rcases anc_iff_po.1 hta with ⟨e, -⟩ | hp
    · subst e
      rw [(hRa u).1 hut]
      exact hvX
    · exact h ⟨t, ⟨hyt, hp⟩, hut⟩

/-- ✱234·51. \[\begin{align}&\vdash \colon\colon Q\in \text{trans}.Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa\in \text{connex} .Rʻa\in \text{D}ʻP\cap \text{ᗡ}ʻP.\supset \colon\ldotp \\ &a\in \text{ct}(PQ)ʻR.\equiv :Rʻa{\sim}\in CʻP_1:Rʻa\in P(z-w).\supset _{z,w}.\\ &(\exists y).y\in \overrightarrow{Q}ʻa\cap \text{ᗡ}ʻR.RʻʻQ(y\vdash\dashv a)\subset P(z-w)\end{align}\]

`Q(y⊢⊣a)` is `itvCC Q y a`; `R'a ∈ P(z−w)` in the antecedent of `⊃_{z,w}` is the description
`Desc R a (fun v => v ∈ itvOO P z w)`. -/
theorem pm234_51 {a : β} :
    (Q ∈ transR ∧ anc Q ⥏ refs Q a ∈ connex) ∧ Desc R a (fun v => v ∈ dom P ∩ codom P) →
      (a ∈ ct P Q R ↔
        Desc R a (fun v => v ∉ fld (P1 P)) ∧
          ∀ z w, Desc R a (fun v => v ∈ itvOO P z w) →
            ∃ y, y ∈ refs Q a ∩ codom R ∧ R ʻʻ itvCC Q y a ⊆ itvOO P z w) := by
  rintro ⟨⟨htr, hc⟩, v, hv, hvD⟩
  have hRa : ∀ u, R u a ↔ u = v := hv
  have hpo : refs (po Q) a = refs Q a := by rw [po_eq_of_transR htr]
  have key := pm234_41 (P := P) (R := R) (x := v) ⟨htr, hc⟩
  show TheIs (fun u => R u a) (fun u => u ∈ osPQ P (anc Q ⥏ refs (po Q) a) R \ fld (P1 P)) ↔ _
  simp only [Desc, TheIs_iff_of_unique hRa]
  rw [hpo]
  constructor
  · rintro ⟨hos, hv1⟩
    refine ⟨hv1, fun z w hz => ?_⟩
    obtain ⟨y, hy, hsub⟩ := (key.1 ⟨⟨hos, hvD.1⟩, hvD.2⟩).2 z w hz
    exact ⟨y, hy, (itvCC_sub_iff hRa hz).2 hsub⟩
  · rintro ⟨hv1, h⟩
    refine ⟨(key.2 ⟨hvD, fun z w hz => ?_⟩).1.1, hv1⟩
    obtain ⟨y, hy, hsub⟩ := h z w hz
    exact ⟨y, hy, (itvCC_sub_iff hRa hz).1 hsub⟩

private theorem ct_vals {a : β} (hS : P ∈ Ser) (htr : Q ∈ transR)
    (hc : anc Q ⥏ refs Q a ∈ connex) (hR : R ʻʻ refs Q a ⊆ fld P) (ha : a ∈ ct P Q R) :
    ∃ v, ((∀ u, R u a ↔ u = v) ∧ ∀ b, rlim R P Q b a ↔ b = v) ∧ ∀ b, rlim R P˘ Q b a ↔ b = v := by
  obtain ⟨v, hv, hos, hv1⟩ := ha
  have hpo : refs (po Q) a = refs Q a := by rw [po_eq_of_transR htr]
  rw [hpo] at hos
  obtain ⟨⟨r, hr, e1⟩, h2⟩ := pm234_462 ⟨⟨⟨⟨hS, htr⟩, hc⟩, hR⟩, hos, hv1⟩
  subst e1
  obtain ⟨s, hs, e⟩ := (TheIs_iff_of_unique hr).1 h2
  subst e
  exact ⟨v, ⟨hv, hr⟩, hs⟩

/-- ✱234·52. \[\begin{align}\vdash \colon\ldotp P\in &\text{Ser}.Q\in \text{trans}.Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa\in \text{connex} .Rʻʻ\overrightarrow{Q}ʻa\subset CʻP.\supset :\\ &a\in \text{ct}(PQ)ʻR.\supset .R(PQ)ʻa=R(\breve{P} Q)ʻa=Rʻa \quad[*234·462·5]\end{align}\] -/
theorem pm234_52 {a : β} :
    ((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P →
      (a ∈ ct P Q R →
        Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ∧
          Desc (rlim R P˘ Q) a (fun s => Desc R a (fun v => s = v))) := by
  rintro ⟨⟨⟨hS, htr⟩, hc⟩, hR⟩ ha
  obtain ⟨v, ⟨hv, hr⟩, hs⟩ := ct_vals hS htr hc hR ha
  exact ⟨eqDesc hr hs, eqDesc hs hv⟩

/-- ✱234·521. \[\begin{align}&\vdash :\text{Hp}*234·52.a\in \text{ct}(PQ)ʻR.\supset .\text{os}(P,Q_{*}\unicode{x0294f}\overrightarrow{Q}ʻa)=\iota ʻRʻa\\ &[*234·441·52]\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `os(P,Q_*⥏Q⃗'a)` for
`os(P,Q_*⥏Q⃗'a)'R`. -/
theorem pm234_521 {a : β} :
    (((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        a ∈ ct P Q R →
      Desc R a (fun v => osPQ P (anc Q ⥏ refs Q a) R = ι v) := by
  rintro ⟨h, ha⟩
  obtain ⟨v, ⟨hv, hr⟩, hs⟩ := ct_vals h.1.1.1 h.1.1.2 h.1.2 h.2 ha
  obtain ⟨r, hr', hX⟩ := (pm234_441 ⟨h, eqDesc hr hs⟩).1
  have : r = v := (hr r).1 ((hr' r).2 rfl)
  subst this
  exact (TheIs_iff_of_unique hv).2 hX

/-- ✱234·522. \[\begin{align}\vdash \colon\ldotp \text{Hp}*234·52.P^{2}=&P.\supset :\\ &a\in \text{ct}(PQ)ʻR.\equiv .R(PQ)ʻa=R(\breve{P} Q)ʻa=Rʻa\end{align}\] -/
theorem pm234_522 {a : β} :
    (((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        rsq P = P →
      (a ∈ ct P Q R ↔
        Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ∧
          Desc (rlim R P˘ Q) a (fun s => Desc R a (fun v => s = v))) := by
  rintro ⟨h, hd⟩
  refine ⟨pm234_52 h, fun ⟨h1, h2⟩ => ?_⟩
  have hX0 := (pm234_45 ⟨h, hd⟩).2.2 h1
  obtain ⟨r, hr, s, hs, e0⟩ := h1
  subst e0
  obtain ⟨v, hv, e⟩ := (TheIs_iff_of_unique hs).1 h2
  subst e
  have hX := (TheIs_iff_of_unique hs).1 hX0
  have hpo : refs (po Q) a = refs Q a := by rw [po_eq_of_transR h.1.1.2]
  show TheIs (fun u => R u a) (fun u => u ∈ osPQ P (anc Q ⥏ refs (po Q) a) R \ fld (P1 P))
  rw [TheIs_iff_of_unique hv, hpo, hX]
  refine ⟨rfl, ?_⟩
  rintro ⟨y, hy | hy⟩
  · exact P1_empty_of_dense h.1.1.1 hd _ _ hy
  · exact P1_empty_of_dense h.1.1.1 hd _ _ hy

/-- ✱234·53. \[\begin{align}\vdash \colon\colon P_{\text{po}}&\in \text{connex} .Q\in \text{trans}.Rʻa=BʻP.\supset \colon\ldotp \\ a\in \text{ct}(PQ)ʻR.&\equiv :BʻP{\sim}\in \text{D}ʻP_{1}:w\in \text{ᗡ}ʻP.\supset _{w}.\\ &(\exists y).y\in \overrightarrow{Q}ʻa\cap \text{ᗡ}ʻR.RʻʻQ(y\vdash\dashv a)\subset \overrightarrow{P}_{\text{po}}ʻw\end{align}\]

`R'a = B'P` is `Desc R a (fun v => Desc Beg P (fun b => v = b))`; `B'P ∼∈ D'P_1` is
`Desc Beg P (fun b => b ∉ dom (P1 P))`. -/
theorem pm234_53 {a : β} :
    (po P ∈ connex ∧ Q ∈ transR) ∧ Desc R a (fun v => Desc Beg P (fun b => v = b)) →
      (a ∈ ct P Q R ↔
        Desc Beg P (fun b => b ∉ dom (P1 P)) ∧
          ∀ w, w ∈ codom P →
            ∃ y, y ∈ refs Q a ∩ codom R ∧ R ʻʻ itvCC Q y a ⊆ refs (po P) w) := by
  rintro ⟨⟨hc, htr⟩, v, hv, b, hb, rfl⟩
  have hvB : Beg v P := (hb v).2 rfl
  have hpo : refs (po Q) a = refs Q a := by rw [po_eq_of_transR htr]
  have hos := pm234_122 (P := P) (Q := anc Q ⥏ refs Q a) (R := R) (x := v)
    ⟨hc, (TheIs_iff_of_unique hb).2 rfl⟩
  have hcodom : v ∉ codom (P1 P) := by
    rintro ⟨u, hu⟩
    obtain ⟨u0, v0, h0, he⟩ := P1_iff.1 hu
    have hmem : ∀ z, z ∈ itvCC P u v → z = v := fun z hz => by
      rcases anc_iff_po.1 hz.2 with ⟨e, -⟩ | hp
      · exact e
      · rw [po_iff_transGen] at hp
        obtain ⟨c, -, hcv⟩ := Relation.TransGen.tail'_iff.1 hp
        exact absurd ⟨c, hcv⟩ hvB.2
    have h1 : u0 ∈ itvCC P u v := by rw [he]; exact Or.inl rfl
    have h2 : v0 ∈ itvCC P u v := by rw [he]; exact Or.inr rfl
    exact h0 ((hmem u0 h1).trans (hmem v0 h2).symm)
  have hw : ∀ w, w ∈ codom P → po P v w := by
    intro w ⟨u, huw⟩
    have hc' := hc
    rw [mem_connex, fld_po] at hc'
    obtain ⟨⟨y, hvy⟩, hvn⟩ := hvB
    rcases hc' v w ⟨fld_of_left hvy, fld_of_right huw⟩ with (h | e) | h
    · exact h
    · exact absurd (e ▸ ⟨u, huw⟩) hvn
    · rw [po_iff_transGen] at h
      obtain ⟨c, -, hcv⟩ := Relation.TransGen.tail'_iff.1 h
      exact absurd ⟨c, hcv⟩ hvn
  have hRa : ∀ u, R u a ↔ u = v := hv
  show TheIs (fun u => R u a) (fun u => u ∈ osPQ P (anc Q ⥏ refs (po Q) a) R \ fld (P1 P)) ↔ _
  have hdb : Desc Beg P (fun b => b ∉ dom (P1 P)) ↔ v ∉ dom (P1 P) := TheIs_iff_of_unique hb
  rw [TheIs_iff_of_unique hRa, hdb, hpo]
  have e3 : ∀ y, refs Q a ∩ rels (anc Q) y = itvCO Q y a := fun y => by
    show refs Q a ∩ rels (anc Q) y = rels (anc Q) y ∩ refs (po Q) a
    rw [po_eq_of_transR htr, Set.inter_comm]
  have hsc : v ∈ osPQ P (anc Q ⥏ refs Q a) R ↔ ∀ w, w ∈ codom P →
      ∃ y, y ∈ refs Q a ∩ codom R ∧ R ʻʻ itvCC Q y a ⊆ refs (po P) w := by
    rw [hos.1, hos.2]
    constructor
    · intro h w hw'
      obtain ⟨y, ⟨⟨hya, -⟩, hyR⟩, hsub⟩ := cn_ancFres.1 (h ⟨w, hw', rfl⟩)
      rw [e3] at hsub
      exact ⟨y, ⟨hya, hyR⟩, (itvCC_sub_iff hRa (hw w hw')).2 hsub⟩
    · rintro h C ⟨w, hw', rfl⟩
      obtain ⟨y, ⟨hya, hyR⟩, hsub⟩ := h w hw'
      refine cn_ancFres.2 ⟨y, ⟨⟨hya, fld_of_left hya⟩, hyR⟩, ?_⟩
      rw [e3]
      exact (itvCC_sub_iff hRa (hw w hw')).1 hsub
  constructor
  · rintro ⟨hos', hv1⟩
    exact ⟨fun h => hv1 (h.elim fun y hy => ⟨y, Or.inl hy⟩), hsc.1 hos'⟩
  · rintro ⟨hv1, h⟩
    refine ⟨hsc.2 h, ?_⟩
    rintro ⟨y, hy | hy⟩
    · exact hv1 ⟨y, hy⟩
    · exact hcodom ⟨y, hy⟩

/-- ✱234·54. \(\vdash :a\in \text{ct}(PQ)ʻR.\supset .a\in \text{ᗡ}ʻR\cap \breve{Q} _{\text{po}}ʻʻ\text{ᗡ}ʻR.Rʻa\in CʻP\)

`Q̆_po''ᗡ'R` is `po Q˘ ʻʻ codom R`. -/
theorem pm234_54 {a : β} :
    a ∈ ct P Q R → a ∈ codom R ∩ po Q˘ ʻʻ codom R ∧ Desc R a (fun v => v ∈ fld P) := by
  rintro ⟨v, hv, hos, -⟩
  have hva : R v a := (hv v).2 rfl
  have hvP : v ∈ fld P := (mem_scPQ.1 hos.1).1
  refine ⟨⟨⟨v, hva⟩, ?_⟩, ⟨v, hv, hvP⟩⟩
  obtain ⟨u, hu | hu⟩ := hvP
  · obtain ⟨y, ⟨hy, hyR⟩, -⟩ := (mem_scPQ.1 hos.1).2 u (po_of hu)
    exact ⟨y, hyR, po_cnv.2 (fld_ancFres.1 hy).1⟩
  · obtain ⟨y, ⟨hy, hyR⟩, -⟩ := (mem_scPQ_cnv.1 hos.2).2 u (po_of hu)
    exact ⟨y, hyR, po_cnv.2 (fld_ancFres.1 hy).1⟩

/-- ✱234·55. \(\vdash .{\sim}\{\text{min}(Q_{\text{po}})ʻ\text{ᗡ}ʻR\in \text{ct}(PQ)ʻR\} \quad[*234·54.\text{Transp}]\)

`min(Q_po)'ᗡ'R` is a description, `Desc (minP (po Q)) (codom R) ψ`. -/
theorem pm234_55 : ¬Desc (minP (po Q)) (codom R) (fun m => m ∈ ct P Q R) := by
  rintro ⟨m, hm, hct⟩
  obtain ⟨⟨-, y, hyR, hy⟩, -⟩ := pm234_54 hct
  exact (minP_iff.1 ((hm m).2 rfl)).2 y hyR (po_cnv.1 hy)

/-- ✱234·56. \[\begin{align}&\vdash :\text{Hp}*234·52.a\in \text{ct}(PQ)ʻR.\supset .\\ &(P\overline{R} Q)_{\text{os}}ʻ\overrightarrow{Q}ʻa\in 0\cup 1.\text{E}!R(PQ)ʻa.R(PQ)ʻa{\sim}\in CʻP_{1}.Rʻa=R(PQ)ʻa\end{align}\] -/
theorem pm234_56 {a : β} :
    (((P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refs Q a ∈ connex) ∧ R ʻʻ refs Q a ⊆ fld P) ∧
        a ∈ ct P Q R →
      ((osFun P R Q (refs Q a) ∈ zero ∪ one ∧ EDesc (rlim R P Q) a) ∧
          Desc (rlim R P Q) a (fun r => r ∉ fld (P1 P))) ∧
        Desc R a (fun v => Desc (rlim R P Q) a (fun r => v = r)) := by
  rintro ⟨h, ha⟩
  obtain ⟨v, ⟨hv, hr⟩, -⟩ := ct_vals h.1.1.1 h.1.1.2 h.1.2 h.2 ha
  obtain ⟨v', hv', hos, hv1⟩ := ha
  have : v' = v := (hv v').1 ((hv' v').2 rfl)
  subst this
  have hpo : refs (po Q) a = refs Q a := by rw [po_eq_of_transR h.1.1.2]
  rw [hpo] at hos
  exact ⟨⟨⟨pm234_103 ⟨Ser_po h.1.1.1, v', hos⟩, ⟨v', hr⟩⟩, (TheIs_iff_of_unique hr).2 hv1⟩,
    eqDesc hv hr⟩

/-- ✱234·561. \[\begin{align}\vdash :P,Q\in \text{Ser}.&a\in \text{ct}(PQ)ʻR.a=\text{lt}_{Q}ʻ(\alpha \cap \text{ᗡ}ʻR).Rʻʻ\overrightarrow{Q}ʻa\subset CʻP.\supset .\\ &(P\overline{R}Q)_{\text{lmx}}ʻ\alpha =Rʻa=(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha \quad[*233·515.*234·56]\end{align}\]

`P, Q ∈ Ser` is `P ∈ Ser ∧ Q ∈ Ser`; `a = lt_Q'(α ∩ ᗡ'R)` is
`Desc (ltP Q) (S ∩ codom R) (fun l => a = l)`. -/
theorem pm234_561 {S : Set β} {a : β} :
    ((((P ∈ Ser ∧ Q ∈ Ser) ∧ a ∈ ct P Q R) ∧ Desc (ltP Q) (S ∩ codom R) (fun l => a = l)) ∧
        R ʻʻ refs Q a ⊆ fld P) →
      Desc (lmx P R Q) S (fun l => Desc R a (fun v => l = v)) ∧
        Desc R a (fun v => Desc (lmx P˘ R Q) S (fun m => v = m)) := by
  rintro ⟨⟨⟨⟨hS, hQ⟩, ha⟩, hlt⟩, hR⟩
  have hc : anc Q ⥏ refs Q a ∈ connex := connex_ancFres_of (Ser_connex hQ)
  obtain ⟨v, ⟨hv, hr⟩, -⟩ := ct_vals hS (Ser_transR hQ) hc hR ha
  obtain ⟨⟨h01, hE⟩, hd⟩ := (pm234_56 ⟨⟨⟨⟨hS, Ser_transR hQ⟩, hc⟩, hR⟩, ha⟩).1
  have e := pm233_5 ⟨hQ, hlt⟩
  have hR' : R ʻʻ (fld Q ∩ S) ⊆ fld P := by
    rintro u ⟨y, ⟨hyQ, hyS⟩, huy⟩
    apply hR
    rw [e]
    exact ⟨y, ⟨y, ⟨hyS, u, huy⟩, anc_rfl hyQ⟩, huy⟩
  obtain ⟨⟨h1, h2⟩, -⟩ := pm233_515 ⟨⟨⟨⟨⟨⟨hS, hQ⟩, hlt⟩, hR'⟩, h01⟩, hE⟩, hd⟩
  obtain ⟨l, hl, m, hm, rfl⟩ := h1
  obtain ⟨r, hr', e'⟩ := (TheIs_iff_of_unique hm).1 h2
  have : r = v := (hr r).1 ((hr' r).2 rfl)
  subst this
  subst e'
  exact ⟨eqDesc hl hv, eqDesc hv hm⟩

/-- `R` with its arguments limited to those from `y₀` on; used for ✱234·562. -/
private abbrev tailR (R : α → β → Prop) (Q : β → β → Prop) (y₀ : β) : α → β → Prop :=
  fun u z => R u z ∧ anc Q y₀ z

/-- Of two terms of the field of a connected `Q`, one is reached from the other. -/
private theorem anc_or_of_connex (hc : Q ∈ connex) {y z : β} (hy : y ∈ fld Q)
    (hz : z ∈ fld Q) : anc Q y z ∨ Q z y := by
  rcases mem_connex.1 hc y z ⟨hy, hz⟩ with (h | rfl) | h
  · exact Or.inl (anc_of h)
  · exact Or.inl (anc_rfl hy)
  · exact Or.inr h

/-- If `a = lt_Q'γ` and `y₀ Q a`, some member of `γ` comes at or after `y₀`. -/
private theorem lt_cofinal (hQ : Q ∈ Ser) {G : Set β} {a y₀ : β} (ha : ltP Q a G)
    (hy : Q y₀ a) : ∃ g, (g ∈ G ∧ g ∈ fld Q) ∧ anc Q y₀ g := by
  have hn := (seqP_iff.1 ha.1).2 y₀
  by_contra hno
  refine hn (fun g hg => ?_) hy
  rcases anc_or_of_connex hQ.2 ⟨a, Or.inl hy⟩ hg.2 with h | h
  · exact absurd ⟨g, hg, h⟩ hno
  · exact h

/-- `lt_Q'γ = lt_Q'(γ ∩ Q⃖_*'y₀)` when `y₀ Q lt_Q'γ`. -/
private theorem ltP_tail (hQ : Q ∈ Ser) {G : Set β} {a y₀ : β} (ha : ltP Q a G) (hy : Q y₀ a)
    (x : β) : ltP Q x (G ∩ rels (anc Q) y₀) ↔ ltP Q x G := by
  obtain ⟨g, hg, hy₀g⟩ := lt_cofinal hQ ha hy
  have htr : Q ∈ transR := hQ.1.2
  have tr := mem_transR.1 htr
  have irr := mem_rl_J.1 hQ.1.1
  have hy₀ : y₀ ∈ fld Q := ⟨a, Or.inl hy⟩
  have early : ∀ y, y ∈ fld Q → ¬anc Q y₀ y → Q y y₀ := fun y hy hn =>
    (anc_or_of_connex hQ.2 hy₀ hy).resolve_left hn
  have aQ1 : ∀ {u w z}, anc Q u w → Q w z → Q u z := fun h hw => by
    rcases (anc_iff_of_transR htr).1 h with ⟨rfl, -⟩ | h
    · exact hw
    · exact tr _ _ _ ⟨h, hw⟩
  have aQ2 : ∀ {u w z}, Q z u → anc Q u w → Q z w := fun hz h => by
    rcases (anc_iff_of_transR htr).1 h with ⟨rfl, -⟩ | h
    · exact hz
    · exact tr _ _ _ ⟨hz, h⟩
  have ub : ∀ z, (∀ y, y ∈ (G ∩ rels (anc Q) y₀) ∩ fld Q → Q y z) ↔
      (∀ y, y ∈ G ∩ fld Q → Q y z) := fun z => by
    refine ⟨fun h y hy => ?_, fun h y hy => h y ⟨hy.1.1, hy.2⟩⟩
    by_cases hyt : anc Q y₀ y
    · exact h y ⟨⟨hy.1, hyt⟩, hy.2⟩
    · exact tr _ _ _ ⟨early y hy.2 hyt, aQ1 hy₀g (h g ⟨⟨hg.1, hy₀g⟩, hg.2⟩)⟩
  have mx : (∃ m, maxP Q m (G ∩ rels (anc Q) y₀)) ↔ ∃ m, maxP Q m G := by
    constructor
    · rintro ⟨m, hm⟩
      obtain ⟨⟨⟨hmG, hy₀m⟩, hmQ⟩, hmax⟩ := maxP_iff.1 hm
      refine ⟨m, maxP_iff.2 ⟨⟨hmG, hmQ⟩, fun y hyG hmy => ?_⟩⟩
      by_cases hyt : anc Q y₀ y
      · exact hmax y ⟨hyG, hyt⟩ hmy
      · have hyy₀ := early y ⟨m, Or.inr hmy⟩ hyt
        exact irr m (aQ2 (tr _ _ _ ⟨hmy, hyy₀⟩) hy₀m)
    · rintro ⟨m, hm⟩
      obtain ⟨⟨hmG, hmQ⟩, hmax⟩ := maxP_iff.1 hm
      rcases anc_or_of_connex hQ.2 hy₀ hmQ with h | h
      · exact ⟨m, maxP_iff.2 ⟨⟨⟨hmG, h⟩, hmQ⟩, fun y hy => hmax y hy.1⟩⟩
      · exact absurd (aQ2 h hy₀g) (hmax g hg.1)
  rw [ltP_iff, ltP_iff, mx]
  simp only [seqP_iff, ub]

/-- Limiting the arguments of `R` to those from `y₀` on does not change `(P R̄ Q)_sc'α`, when
every argument in `α` is followed by one from `y₀` on. -/
private theorem scFun_tailR {P' : α → α → Prop} {S : Set β} {y₀ : β}
    (H : ∀ y, y ∈ S ∩ fld Q ∩ codom R →
      ∃ g, g ∈ S ∩ fld Q ∩ codom R ∧ anc Q y₀ g ∧ anc Q y g) :
    scFun P' (tailR R Q y₀) Q S = scFun P' R Q S := by
  ext x
  rw [pm232_11, pm232_11]
  refine and_congr ⟨fun h y hy => ?_, fun h y hy => ?_⟩ Iff.rfl
  · obtain ⟨g, ⟨⟨hgS, hgQ⟩, u, hu⟩, hy₀g, hyg⟩ := H y hy
    obtain ⟨v, ⟨z, ⟨hzS, hgz⟩, hvz, -⟩, hxv⟩ := h g ⟨⟨hgS, hgQ⟩, u, hu, hy₀g⟩
    exact ⟨v, ⟨z, ⟨hzS, anc_trans' hyg hgz⟩, hvz⟩, hxv⟩
  · obtain ⟨⟨hyS, hyQ⟩, u, hu, hy₀y⟩ := hy
    obtain ⟨v, ⟨z, ⟨hzS, hyz⟩, hvz⟩, hxv⟩ := h y ⟨⟨hyS, hyQ⟩, u, hu⟩
    exact ⟨v, ⟨z, ⟨hzS, hyz⟩, hvz, anc_trans' hy₀y hyz⟩, hxv⟩

/-- Continuity from below at `a` survives limiting the arguments to those from `y₀` on. -/
private theorem ct_tailR {a y₀ : β} (hc : Q ∈ connex)
    (hy₀ : y₀ ∈ refs (po Q) a ∩ fld Q ∩ codom R) (ha : a ∈ ct P Q R) :
    a ∈ ct P Q (tailR R Q y₀) := by
  obtain ⟨⟨hy₀S, hy₀Q⟩, u₀, hu₀⟩ := hy₀
  have key : ∀ X : Set α,
      (∃ y, y ∈ refs (po Q) a ∩ fld Q ∩ codom R ∧
        R ʻʻ (refs (po Q) a ∩ rels (anc Q) y) ⊆ X) →
      ∃ y, y ∈ refs (po Q) a ∩ fld Q ∩ codom (tailR R Q y₀) ∧
        tailR R Q y₀ ʻʻ (refs (po Q) a ∩ rels (anc Q) y) ⊆ X := by
    rintro X ⟨y, ⟨⟨hyS, hyQ⟩, u, hu⟩, hsub⟩
    rcases anc_or_of_connex hc hy₀Q hyQ with h | h
    · exact ⟨y, ⟨⟨hyS, hyQ⟩, u, hu, h⟩, fun v ⟨z, hz, hvz, _⟩ => hsub ⟨z, hz, hvz⟩⟩
    · exact ⟨y₀, ⟨⟨hy₀S, hy₀Q⟩, u₀, hu₀, anc_rfl hy₀Q⟩, fun v ⟨z, ⟨hzS, hy₀z⟩, hvz, _⟩ =>
        hsub ⟨z, ⟨hzS, anc_trans' (anc_of h) hy₀z⟩, hvz⟩⟩
  have sc : ∀ (P' : α → α → Prop) x, x ∈ scPQ P' (anc Q ⥏ refs (po Q) a) R →
      x ∈ scPQ P' (anc Q ⥏ refs (po Q) a) (tailR R Q y₀) := fun P' x hx => by
    obtain ⟨hx1, hx2⟩ := (pm234_3 (P := P') (R := R)).1 hx
    exact (pm234_3 (P := P') (R := tailR R Q y₀)).2 ⟨hx1, fun w hw => key _ (hx2 w hw)⟩
  obtain ⟨v, hv, ⟨hos1, hos2⟩, hv1⟩ := ha
  have hy₀a : anc Q y₀ a := anc_of_po hy₀S
  show TheIs (fun u => tailR R Q y₀ u a)
    (fun u => u ∈ osPQ P (anc Q ⥏ refs (po Q) a) (tailR R Q y₀) \ fld (P1 P))
  exact ⟨v, fun u => ⟨fun h => (hv u).1 h.1, fun h => ⟨(hv u).2 h, hy₀a⟩⟩,
    ⟨sc P v hos1, sc P˘ v hos2⟩, hv1⟩

/-- Continuity from below at `a` puts in `C'P` the values for the arguments from some `y₀` on. -/
private theorem ct_fld {a : β} (ha : a ∈ ct P Q R) :
    ∃ y₀, y₀ ∈ refs (po Q) a ∩ fld Q ∩ codom R ∧
      R ʻʻ (refs (po Q) a ∩ rels (anc Q) y₀) ⊆ fld P := by
  obtain ⟨v, -, ⟨hos1, hos2⟩, -⟩ := ha
  obtain ⟨⟨w, hw | hw⟩, hall⟩ := (pm234_3 (P := P) (R := R)).1 hos1
  · obtain ⟨y, hy, hsub⟩ := hall w (po_of hw)
    exact ⟨y, hy, fun u hu => po_left (hsub hu)⟩
  · obtain ⟨-, hall2⟩ := (pm234_3 (P := P˘) (R := R)).1 hos2
    obtain ⟨y, hy, hsub⟩ := hall2 w (po_cnv.2 (po_of hw))
    exact ⟨y, hy, fun u hu => po_right (po_cnv.1 (hsub hu))⟩

/-- ✱234·562. \[\begin{align}\vdash :P,Q\in &\text{Ser}.\text{lt}_{Q}ʻ(\alpha \cap \text{ᗡ}ʻR)\in \text{ct}(PQ)ʻR.Rʻʻ(\alpha \cap CʻQ)\subset CʻP.\supset .\\ &(P\overline{R} Q)_{\text{lmx}}ʻ\alpha =(\breve{P} \overline{R} Q)_{\text{lmx}}ʻ\alpha =Rʻ\text{lt}_{Q}ʻ\alpha \quad[*233·516.*234·56]\end{align}\]

**Status.** proved (corrected): false as printed: the conclusion has `R'lt_Q'α`, while the
hypothesis has `lt_Q'(α ∩ ᗡ'R)` ∈ ct(PQ)'R (the reference ✱233·516 has the same defect).
Counterexample (series of rationals): `α = ẑ(−1 < z < 0) ∪ ẑ(1/2 < z < 1)`,
`ᗡ'R = ẑ(−1 < z ≤ 0) ∪ ι'1`, `R'z = 0` for `z ≤ 0` and `R'1 = 5`: then
`lt_Q'(α ∩ ᗡ'R) = 0 ∈ ct(PQ)'R` and `(P R̄ Q)_lmx'α = 0 ≠ R'lt_Q'α = 5`. The conclusion is read
with `R'lt_Q'(α ∩ ᗡ'R)`; no hypothesis is added. (PM's demonstration cites ✱234·56, whose
hypothesis also has `R''Q⃗'a ⊂ C'P`; it is not needed: continuity from below at `a` puts the
values for the arguments from some `y₀ Q a` on in `C'P`, and limiting `R` to those arguments
changes neither `(P R̄ Q)_sc'α`, `(P̆ R̄ Q)_sc'α`, `R'a` nor `lt_Q'(α ∩ ᗡ'R)`, so ✱234·561
applies to the limited function.) -/
theorem pm234_562 {S : Set β} :
    (((P ∈ Ser ∧ Q ∈ Ser) ∧ Desc (ltP Q) (S ∩ codom R) (fun a => a ∈ ct P Q R)) ∧
          R ʻʻ (S ∩ fld Q) ⊆ fld P) →
      Desc (lmx P R Q) S (fun l => Desc (lmx P˘ R Q) S (fun m => l = m)) ∧
        Desc (lmx P˘ R Q) S (fun m => Desc2 R (ltP Q) (S ∩ codom R) (fun v => m = v)) := by
  rintro ⟨⟨⟨hS, hQ⟩, a, ha, hct⟩, -⟩
  have hlta : ltP Q a (S ∩ codom R) := (ha a).2 rfl
  obtain ⟨y₀, hy₀, hfld⟩ := ct_fld hct
  have hpo : po Q = Q := po_eq_of_transR hQ.1.2
  have hy₀a : Q y₀ a := by
    have h := hy₀.1.1
    rw [hpo] at h
    exact h
  have h1 : a ∈ ct P Q (tailR R Q y₀) := ct_tailR hQ.2 hy₀ hct
  have hcod : S ∩ codom (tailR R Q y₀) = S ∩ codom R ∩ rels (anc Q) y₀ := by
    ext z
    constructor
    · rintro ⟨hz, u, hu, h⟩
      exact ⟨⟨hz, u, hu⟩, h⟩
    · rintro ⟨⟨hz, u, hu⟩, h⟩
      exact ⟨hz, u, hu, h⟩
  have h2 : Desc (ltP Q) (S ∩ codom (tailR R Q y₀)) (fun l => a = l) := by
    rw [hcod]
    exact ⟨a, fun x => (ltP_tail hQ hlta hy₀a x).trans (ha x), rfl⟩
  have h3 : tailR R Q y₀ ʻʻ refs Q a ⊆ fld P := by
    rintro u ⟨z, hz, huz, hy₀z⟩
    have hz' : z ∈ refs (po Q) a := by
      rw [hpo]
      exact hz
    exact hfld ⟨z, ⟨hz', hy₀z⟩, huz⟩
  have H : ∀ y, y ∈ S ∩ fld Q ∩ codom R →
      ∃ g, g ∈ S ∩ fld Q ∩ codom R ∧ anc Q y₀ g ∧ anc Q y g := by
    obtain ⟨g, ⟨⟨hgS, hgR⟩, hgQ⟩, hy₀g⟩ := lt_cofinal hQ hlta hy₀a
    rintro y ⟨⟨hyS, hyQ⟩, hyR⟩
    rcases anc_or_of_connex hQ.2 hyQ hgQ with h | h
    · exact ⟨g, ⟨⟨hgS, hgQ⟩, hgR⟩, hy₀g, h⟩
    · exact ⟨y, ⟨⟨hyS, hyQ⟩, hyR⟩, anc_trans' hy₀g (anc_of h), anc_rfl hyQ⟩
  have e1 : ∀ x, lmx P (tailR R Q y₀) Q x S ↔ lmx P R Q x S := fun x => by
    rw [lmx_apply, lmx_apply, scFun_tailR H]
  have e2 : ∀ x, lmx P˘ (tailR R Q y₀) Q x S ↔ lmx P˘ R Q x S := fun x => by
    rw [lmx_apply, lmx_apply, scFun_tailR H]
  have e3 : ∀ u, tailR R Q y₀ u a ↔ R u a := fun u =>
    ⟨fun h => h.1, fun h => ⟨h, anc_of hy₀a⟩⟩
  obtain ⟨⟨l, hl, v, hv, rfl⟩, h4⟩ := pm234_561 ⟨⟨⟨⟨hS, hQ⟩, h1⟩, h2⟩, h3⟩
  obtain ⟨m, hm, e⟩ := (TheIs_iff_of_unique hv).1 h4
  subst e
  have hl' := fun x => (e1 x).symm.trans (hl x)
  have hv' := fun x => (e3 x).symm.trans (hv x)
  have hm' := fun x => (e2 x).symm.trans (hm x)
  refine ⟨(TheIs_iff_of_unique hl').2 ((TheIs_iff_of_unique hm').2 rfl),
    (TheIs_iff_of_unique hm').2 ?_⟩
  rw [desc2_iff]
  exact (TheIs_iff_of_unique ha).2 ((TheIs_iff_of_unique hv').2 rfl)

/-- ✱234·6. \(\vdash :a\in \text{contin}(PQ)ʻR.\equiv .a\in \text{ct}(PQ)ʻR\cap \text{ct}(P\breve{Q} )ʻR \quad[(*234·04)]\) -/
theorem pm234_6 {a : β} : a ∈ contin P Q R ↔ a ∈ ct P Q R ∩ ct P Q˘ R := Iff.rfl

private theorem itvCC_cnv {y a : β} : itvCC Q˘ y a = itvCC Q a y := by
  ext z
  exact ⟨fun ⟨h1, h2⟩ => ⟨anc_cnv.1 h2, anc_cnv.1 h1⟩, fun ⟨h1, h2⟩ => ⟨anc_cnv.2 h2, anc_cnv.2 h1⟩⟩

private theorem transR_cnv {Q : β → β → Prop} (h : Q ∈ transR) : Q˘ ∈ transR :=
  mem_transR.2 fun x y z ⟨h1, h2⟩ => mem_transR.1 h z y x ⟨h2, h1⟩

private theorem contin_core {a : β} {v : α} (htr : Q ∈ transR) (hcon : Q ∈ connex)
    (hRa : ∀ u, R u a ↔ u = v) (hvD : v ∈ dom P ∩ codom P) :
    a ∈ contin P Q R ↔ v ∉ fld (P1 P) ∧ ∀ z w, v ∈ itvOO P z w →
      ∃ y y', (a ∈ itvOO Q y y' ∧ (y ∈ codom R ∧ y' ∈ codom R)) ∧
        R ʻʻ itvCC Q y y' ⊆ itvOO P z w := by
  have hd : Desc R a (fun u => u ∈ dom P ∩ codom P) := (TheIs_iff_of_unique hRa).2 hvD
  have h1 := pm234_51 (P := P) ⟨⟨htr, connex_ancFres_of hcon⟩, hd⟩
  have h2 := pm234_51 (P := P) (Q := Q˘) ⟨⟨transR_cnv htr, connex_ancFres_of (connex_cnv hcon)⟩, hd⟩
  rw [mem_connex] at hcon
  show a ∈ ct P Q R ∧ a ∈ ct P Q˘ R ↔ _
  rw [h1, h2]
  simp only [Desc, TheIs_iff_of_unique hRa]
  constructor
  · rintro ⟨⟨hv1, hA⟩, -, hB⟩
    refine ⟨hv1, fun z w hz => ?_⟩
    obtain ⟨y, ⟨hya, hyR⟩, hy⟩ := hA z w hz
    obtain ⟨y', ⟨hy'a, hy'R⟩, hy'⟩ := hB z w hz
    rw [itvCC_cnv] at hy'
    refine ⟨y, y', ⟨⟨po_of hya, po_of hy'a⟩, hyR, hy'R⟩, fun u ⟨t, ⟨hyt, hty'⟩, hut⟩ => ?_⟩
    have htQ : t ∈ fld Q := anc_right hyt
    have haQ : a ∈ fld Q := fld_of_right hya
    rcases hcon t a ⟨htQ, haQ⟩ with (h | e) | h
    · exact hy ⟨t, ⟨hyt, anc_of h⟩, hut⟩
    · exact hy ⟨t, ⟨hyt, by rw [e]; exact anc_rfl haQ⟩, hut⟩
    · exact hy' ⟨t, ⟨anc_of h, hty'⟩, hut⟩
  · rintro ⟨hv1, h⟩
    refine ⟨⟨hv1, fun z w hz => ?_⟩, hv1, fun z w hz => ?_⟩
    · obtain ⟨y, y', ⟨⟨hay, hay'⟩, hyR, -⟩, hsub⟩ := h z w hz
      rw [po_eq_of_transR htr] at hay
      exact ⟨y, ⟨hay, hyR⟩, fun u ⟨t, ⟨hyt, hta⟩, hut⟩ =>
        hsub ⟨t, ⟨hyt, anc_trans' hta (anc_of_po hay')⟩, hut⟩⟩
    · obtain ⟨y, y', ⟨⟨hay, hay'⟩, -, hy'R⟩, hsub⟩ := h z w hz
      rw [po_eq_of_transR htr] at hay'
      refine ⟨y', ⟨hay', hy'R⟩, ?_⟩
      rw [itvCC_cnv]
      exact fun u ⟨t, ⟨hat, hty'⟩, hut⟩ => hsub ⟨t, ⟨anc_trans' (anc_of_po hay) hat, hty'⟩, hut⟩

/-- ✱234·61. \[\begin{align}&\vdash \colon\colon P_{\text{po}}\in \text{Ser}.Q\in \text{trans}.Q_{*}\unicode{x0294f}\overleftrightarrow{Q}ʻa\in \text{connex} .Rʻa\in \text{D}ʻP\cap \text{ᗡ}ʻP.\supset \colon\ldotp \\ &a\in \text{contin}(PQ)ʻR.\equiv :Rʻa{\sim}\in CʻP_{1}:Rʻa\in P(z-w).\supset _{z,w}.\\ &(\exists y,y').a\in Q(y-y').y,y'\in \text{ᗡ}ʻR.RʻʻQ(y\vdash\dashv y')\subset P(z-w)\end{align}\]

`Q⃡'a` is `refsRels Q a`; `y, y' ∈ ᗡ'R` is `y ∈ codom R ∧ y' ∈ codom R`.

**Status.** proved (corrected): false as printed when `Q` is not connected: a term between `y`
and `y'` that is not comparable with `a` lies in `Q(y⊢⊣y')` but in neither `Q(y⊢⊣a)` nor
`Q(a⊢⊣y')`, which are all that continuity from below and from above control. Counterexample:
arguments `y, a, y', t` with `Q = y ↓ a ∪̇ a ↓ y' ∪̇ y ↓ y' ∪̇ y ↓ t ∪̇ t ↓ y'` (transitive;
`Q_* ⥏ Q⃡'a` is connected), `P` the series of rationals, `R'y = R'a = R'y' = 0`, `R't = 5`:
then `a ∈ contin(PQ)'R`, but `R''Q(y⊢⊣y') ∋ 5`, so the right side fails for `P(−1 − 1)`.
The hypothesis `Q ∈ connex` is added (it holds in ✱234·72·73, where `Q ∈ trans ∩ connex`). -/
theorem pm234_61 {a : β} :
    ((((po P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refsRels Q a ∈ connex) ∧ Q ∈ connex) ∧
        Desc R a (fun v => v ∈ dom P ∩ codom P)) →
      (a ∈ contin P Q R ↔
        Desc R a (fun v => v ∉ fld (P1 P)) ∧
          ∀ z w, Desc R a (fun v => v ∈ itvOO P z w) →
            ∃ y y', (a ∈ itvOO Q y y' ∧ (y ∈ codom R ∧ y' ∈ codom R)) ∧
              R ʻʻ itvCC Q y y' ⊆ itvOO P z w) := by
  rintro ⟨⟨⟨⟨-, htr⟩, -⟩, hcon⟩, v, hv, hvD⟩
  simp only [Desc, TheIs_iff_of_unique hv]
  exact contin_core htr hcon hv hvD

private theorem connex_ancFres_sub {S T : Set β} (h : anc Q ⥏ S ∈ connex) (hT : T ⊆ S) :
    anc Q ⥏ T ∈ connex := by
  rw [mem_connex] at h ⊢
  intro y z ⟨hy, hz⟩
  obtain ⟨hyT, hyQ⟩ := fld_ancFres.1 hy
  obtain ⟨hzT, hzQ⟩ := fld_ancFres.1 hz
  rcases h y z ⟨fld_ancFres.2 ⟨hT hyT, hyQ⟩, fld_ancFres.2 ⟨hT hzT, hzQ⟩⟩ with (h1 | h1) | h1
  · exact Or.inl (Or.inl ⟨⟨hyT, h1.1.2⟩, hzT⟩)
  · exact Or.inl (Or.inr h1)
  · exact Or.inr ⟨⟨hzT, h1.1.2⟩, hyT⟩

private theorem connex_ancFres_cnv {S : Set β} (h : anc Q ⥏ S ∈ connex) :
    anc Q˘ ⥏ S ∈ connex := by
  have e : anc Q˘ ⥏ S = (anc Q ⥏ S)˘ := by
    funext y z
    exact propext ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h3, anc_cnv.1 h2⟩, h1⟩,
      fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h3, anc_cnv.2 h2⟩, h1⟩⟩
  rw [e]
  exact connex_cnv h

/-- The four limits and the value at `a` coincide at a point of continuity. -/
private theorem contin_vals {a : β} (hS : P ∈ Ser) (htr : Q ∈ transR)
    (hc : anc Q ⥏ refsRels Q a ∈ connex) (hR : R ʻʻ refsRels Q a ⊆ fld P)
    (ha : a ∈ contin P Q R) :
    ∃ v, (∀ u, R u a ↔ u = v) ∧
      ((∀ b, rlim R P Q b a ↔ b = v) ∧ ∀ b, rlim R P˘ Q b a ↔ b = v) ∧
        ((∀ b, rlim R P Q˘ b a ↔ b = v) ∧ ∀ b, rlim R P˘ Q˘ b a ↔ b = v) := by
  have hsub1 : refs Q a ⊆ refsRels Q a := fun y h => Or.inl (Or.inl h)
  have hsub2 : rels Q a ⊆ refsRels Q a := fun y h => Or.inr h
  obtain ⟨v, ⟨hv, hr⟩, hs⟩ := ct_vals hS htr (connex_ancFres_sub hc hsub1)
    (fun u ⟨y, hy, huy⟩ => hR ⟨y, hsub1 hy, huy⟩) ha.1
  obtain ⟨v', ⟨hv', hr'⟩, hs'⟩ := ct_vals (Q := Q˘) hS (transR_cnv htr)
    (connex_ancFres_cnv (connex_ancFres_sub hc hsub2))
    (fun u ⟨y, hy, huy⟩ => hR ⟨y, hsub2 hy, huy⟩) ha.2
  have : v' = v := (hv v').1 ((hv' v').2 rfl)
  subst this
  exact ⟨v', hv, ⟨hr, hs⟩, ⟨hr', hs'⟩⟩

private theorem chain_of_vals {a : β} {v : α} (hv : ∀ u, R u a ↔ u = v)
    (h1 : ∀ b, rlim R P Q b a ↔ b = v) (h2 : ∀ b, rlim R P˘ Q b a ↔ b = v)
    (h3 : ∀ b, rlim R P Q˘ b a ↔ b = v) (h4 : ∀ b, rlim R P˘ Q˘ b a ↔ b = v) :
    ((Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ∧
        Desc (rlim R P˘ Q) a (fun s => Desc (rlim R P Q˘) a (fun t => s = t))) ∧
        Desc (rlim R P Q˘) a (fun t => Desc (rlim R P˘ Q˘) a (fun u => t = u))) ∧
      Desc (rlim R P˘ Q˘) a (fun u => Desc R a (fun w => u = w)) :=
  ⟨⟨⟨eqDesc h1 h2, eqDesc h2 h3⟩, eqDesc h3 h4⟩, eqDesc h4 hv⟩

private theorem vals_of_chain {a : β}
    (h : ((Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ∧
        Desc (rlim R P˘ Q) a (fun s => Desc (rlim R P Q˘) a (fun t => s = t))) ∧
        Desc (rlim R P Q˘) a (fun t => Desc (rlim R P˘ Q˘) a (fun u => t = u))) ∧
      Desc (rlim R P˘ Q˘) a (fun u => Desc R a (fun w => u = w))) :
    ∃ v, (∀ u, R u a ↔ u = v) ∧
      ((∀ b, rlim R P Q b a ↔ b = v) ∧ ∀ b, rlim R P˘ Q b a ↔ b = v) ∧
        ((∀ b, rlim R P Q˘ b a ↔ b = v) ∧ ∀ b, rlim R P˘ Q˘ b a ↔ b = v) := by
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := h
  obtain ⟨r, hr, s, hs, e1⟩ := c1
  subst e1
  obtain ⟨t, ht, e2⟩ := (TheIs_iff_of_unique hs).1 c2
  subst e2
  obtain ⟨u, hu, e3⟩ := (TheIs_iff_of_unique ht).1 c3
  subst e3
  obtain ⟨w, hw, e4⟩ := (TheIs_iff_of_unique hu).1 c4
  subst e4
  exact ⟨r, hw, ⟨hr, hs⟩, ⟨ht, hu⟩⟩

/-- ✱234·62. \[\begin{align}\vdash \colon\ldotp \text{Hp}*234·61.&P\in \text{trans}.Rʻʻ\overleftrightarrow{Q}ʻa\subset CʻP.\supset :a\in \text{contin}(PQ)ʻR.\supset .\\ &R(PQ)ʻa=R(\breve{P} Q)ʻa=R(P\breve{Q} )ʻa=R(\breve{P} \breve{Q} )ʻa=Rʻa\\ [*234·52·6]\end{align}\]

"Hp ✱234·61" is the hypothesis of ✱234·61 as printed (without `Q ∈ connex`, which is not needed
here). The chain of five is the conjunction of its four links. -/
theorem pm234_62 {a : β} :
    ((((((po P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refsRels Q a ∈ connex) ∧
            Desc R a (fun v => v ∈ dom P ∩ codom P)) ∧ P ∈ transR) ∧
          R ʻʻ refsRels Q a ⊆ fld P)) →
      (a ∈ contin P Q R →
        ((Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ∧
            Desc (rlim R P˘ Q) a (fun s => Desc (rlim R P Q˘) a (fun t => s = t))) ∧
            Desc (rlim R P Q˘) a (fun t => Desc (rlim R P˘ Q˘) a (fun u => t = u))) ∧
          Desc (rlim R P˘ Q˘) a (fun u => Desc R a (fun w => u = w))) := by
  rintro ⟨⟨⟨⟨⟨hpo, htr⟩, hc⟩, -⟩, hPt⟩, hR⟩ ha
  have hS : P ∈ Ser := by
    rw [← po_eq_of_transR hPt]
    exact hpo
  obtain ⟨v, hv, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := contin_vals hS htr hc hR ha
  exact chain_of_vals hv h1 h2 h3 h4

/-- ✱234·63. \[\begin{align}\vdash \colon\ldotp \text{Hp}*234·62.&P^{2}=P.\supset :a\in \text{contin}(PQ)ʻR.\equiv .\\ &R(PQ)ʻa = R(\breve{P} Q)ʻa = R(P\breve{Q} )ʻa = R(\breve{P} \breve{Q} )ʻa = Rʻa\\ [*234·522·6]\end{align}\]

"Hp ✱234·62" is written out; the chain of five is the conjunction of its four links. -/
theorem pm234_63 {a : β} :
    ((((((po P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refsRels Q a ∈ connex) ∧
            Desc R a (fun v => v ∈ dom P ∩ codom P)) ∧ P ∈ transR) ∧
          R ʻʻ refsRels Q a ⊆ fld P) ∧ rsq P = P) →
      (a ∈ contin P Q R ↔
        ((Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ∧
            Desc (rlim R P˘ Q) a (fun s => Desc (rlim R P Q˘) a (fun t => s = t))) ∧
            Desc (rlim R P Q˘) a (fun t => Desc (rlim R P˘ Q˘) a (fun u => t = u))) ∧
          Desc (rlim R P˘ Q˘) a (fun u => Desc R a (fun w => u = w))) := by
  rintro ⟨h, hd⟩
  refine ⟨pm234_62 h, fun hch => ?_⟩
  obtain ⟨⟨⟨⟨⟨hpo, htr⟩, hc⟩, -⟩, hPt⟩, hR⟩ := h
  have hS : P ∈ Ser := by
    rw [← po_eq_of_transR hPt]
    exact hpo
  obtain ⟨v, hv, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := vals_of_chain hch
  have hsub1 : refs Q a ⊆ refsRels Q a := fun y h => Or.inl (Or.inl h)
  have hsub2 : rels Q a ⊆ refsRels Q a := fun y h => Or.inr h
  refine ⟨(pm234_522 ⟨⟨⟨⟨hS, htr⟩, connex_ancFres_sub hc hsub1⟩,
      fun u ⟨y, hy, huy⟩ => hR ⟨y, hsub1 hy, huy⟩⟩, hd⟩).2 ⟨eqDesc h1 h2, eqDesc h2 hv⟩,
    (pm234_522 (Q := Q˘) ⟨⟨⟨⟨hS, transR_cnv htr⟩,
      connex_ancFres_cnv (connex_ancFres_sub hc hsub2)⟩,
      fun u ⟨y, hy, huy⟩ => hR ⟨y, hsub2 hy, huy⟩⟩, hd⟩).2 ⟨eqDesc h3 h4, eqDesc h4 hv⟩⟩

/-- ✱234·64. \[\begin{align}&\vdash \colon\colon\text{Hp}*234·62.Rʻa\in \text{D}ʻP\cap \text{ᗡ}ʻP.\supset \colon\ldotp a\in \text{contin}(P,Q)ʻR.\equiv :\\ Rʻa\in CʻP-&CʻP_{1}:Rʻa\in P(z-w).\supset _{z,w}.\\ &(\exists y,y').y,y'\in \text{ᗡ}ʻR.a\in Q(y-y').RʻʻQ(y\vdash\dashv y')\subset P(z-w)\\ &[*234·51·6]\end{align}\]

**Status.** proved (corrected): false as printed, for the reason given at ✱234·61 (the same
counterexample); `Q ∈ connex` is added. Also the e-text prints `contin(P,Q)'R` for
`contin(PQ)'R`. `R'a ∈ C'P − C'P_1` is `Desc R a (fun v => v ∈ fld P \ fld (P1 P))`. -/
theorem pm234_64 {a : β} :
    (((((((po P ∈ Ser ∧ Q ∈ transR) ∧ anc Q ⥏ refsRels Q a ∈ connex) ∧
            Desc R a (fun v => v ∈ dom P ∩ codom P)) ∧ P ∈ transR) ∧
          R ʻʻ refsRels Q a ⊆ fld P) ∧ Desc R a (fun v => v ∈ dom P ∩ codom P)) ∧
        Q ∈ connex) →
      (a ∈ contin P Q R ↔
        Desc R a (fun v => v ∈ fld P \ fld (P1 P)) ∧
          ∀ z w, Desc R a (fun v => v ∈ itvOO P z w) →
            ∃ y y', ((y ∈ codom R ∧ y' ∈ codom R) ∧ a ∈ itvOO Q y y') ∧
              R ʻʻ itvCC Q y y' ⊆ itvOO P z w) := by
  rintro ⟨⟨⟨⟨⟨⟨⟨-, htr⟩, -⟩, -⟩, -⟩, -⟩, v, hv, hvD⟩, hcon⟩
  simp only [Desc, TheIs_iff_of_unique hv]
  rw [contin_core htr hcon hv hvD]
  have hvP : v ∈ fld P := by
    obtain ⟨⟨u, hu⟩, -⟩ := hvD
    exact fld_of_left hu
  constructor
  · rintro ⟨hv1, h⟩
    refine ⟨⟨hvP, hv1⟩, fun z w hz => ?_⟩
    obtain ⟨y, y', ⟨h1, h2⟩, h3⟩ := h z w hz
    exact ⟨y, y', ⟨h2, h1⟩, h3⟩
  · rintro ⟨⟨-, hv1⟩, h⟩
    refine ⟨hv1, fun z w hz => ?_⟩
    obtain ⟨y, y', ⟨h1, h2⟩, h3⟩ := h z w hz
    exact ⟨y, y', ⟨h2, h1⟩, h3⟩

/-- ✱234·7. \[\begin{align}&\vdash :R\in P\,\overline{\text{contin}}\,Q.\equiv .\exists !CʻQ\cap \text{ᗡ}ʻR.CʻQ\cap \text{ᗡ}ʻR\subset \text{contin}(PQ)ʻR\\ &[(*234·04)]\end{align}\]

**Status.** proved (reading): the e-text cites `(*234·04)` for the Df `*234·05`. -/
theorem pm234_7 :
    R ∈ continBar P Q ↔ (fld Q ∩ codom R).Nonempty ∧ fld Q ∩ codom R ⊆ contin P Q R :=
  Iff.rfl

/-- ✱234·71. \(\vdash :R\in P\,\overline{\text{contin}}\,Q.\supset .R\upharpoonright CʻQ\in 1\rightarrow \text{Cls}.RʻʻCʻQ\subset CʻP\)

`R ∈ 1 → Cls` is `R ∈ arrow one Cls`. -/
theorem pm234_71 :
    R ∈ continBar P Q → R ↾ fld Q ∈ arrow one Cls ∧ R ʻʻ fld Q ⊆ fld P := by
  rintro ⟨-, h⟩
  have key : ∀ a, a ∈ fld Q → a ∈ codom R → ∃ v, (∀ u, R u a ↔ u = v) ∧ v ∈ fld P := by
    intro a haQ haR
    obtain ⟨v, hv, hos, -⟩ := (h ⟨haQ, haR⟩).1
    exact ⟨v, hv, (mem_scPQ.1 hos.1).1⟩
  refine ⟨mem_arrow_one_Cls.2 fun x y z ⟨⟨hx, hz⟩, hy, _⟩ => ?_, fun u ⟨a, haQ, hua⟩ => ?_⟩
  · obtain ⟨v, hv, -⟩ := key z hz ⟨x, hx⟩
    exact ((hv x).1 hx).trans ((hv y).1 hy).symm
  · obtain ⟨v, hv, hvP⟩ := key a haQ ⟨u, hua⟩
    rw [(hv u).1 hua]
    exact hvP

/-- ✱234·72. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.Q\in \text{trans}\cap \text{connex} .R\in P\,\overline{\text{contin}}\,Q.\supset :\\ &a\in CʻQ\cap \text{ᗡ}ʻR.\supset _{a}.R(PQ)ʻa=R(\breve{P} Q)ʻa=R(P\breve{Q})ʻa=R(\breve{P} \breve{Q} )ʻa=Rʻa\\ &[*234·62·7]\end{align}\]

`R(PQ̆)` is `rlim R P Q˘`; `⊃_a` is `∀ a`. -/
theorem pm234_72 :
    (P ∈ Ser ∧ Q ∈ transR ∩ connex) ∧ R ∈ continBar P Q →
      ∀ a, a ∈ fld Q ∩ codom R →
        ((Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ∧
            Desc (rlim R P˘ Q) a (fun s => Desc (rlim R P Q˘) a (fun t => s = t))) ∧
            Desc (rlim R P Q˘) a (fun t => Desc (rlim R P˘ Q˘) a (fun u => t = u))) ∧
          Desc (rlim R P˘ Q˘) a (fun u => Desc R a (fun w => u = w)) := by
  rintro ⟨⟨hS, htr, hcon⟩, hR⟩ a ha
  have hR' := (pm234_71 hR).2
  have hsub : refsRels Q a ⊆ fld Q := by
    rintro y ((h | ⟨-, h⟩) | h)
    · exact fld_of_left h
    · exact h
    · exact fld_of_right h
  obtain ⟨v, hv, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := contin_vals hS htr (connex_ancFres_of hcon)
    (fun u ⟨y, hy, huy⟩ => hR' ⟨y, hsub hy, huy⟩) (hR.2 ha)
  exact chain_of_vals hv h1 h2 h3 h4

private theorem limax_fld {P : α → α → Prop} {v : α} {A : Set α} (h : limaxP P v A) :
    v ∈ fld P := by
  rcases h with hm | ⟨hs, -⟩
  · exact (maxP_iff.1 hm).1.2
  · exact (seqP_iff.1 hs).1.2

/-- ✱234·73. \[\begin{align}\vdash \colon\colon P\in \text{Ser}.&P^{2}=P.Q\in \text{trans}\cap \text{connex} .\supset \colon\ldotp \\ &R\in P\,\overline{\text{contin}}\,Q.\equiv :\exists !CʻQ\cap \text{ᗡ}ʻR:a\in CʻQ\cap \text{ᗡ}ʻR.\supset _{a} .\\ &R(PQ)ʻa=R(\breve{P} Q)ʻa=R(P\breve{Q} )ʻa=R(\breve{P} \breve{Q} )ʻa=Rʻa\end{align}\] -/
theorem pm234_73 :
    (P ∈ Ser ∧ rsq P = P) ∧ Q ∈ transR ∩ connex →
      (R ∈ continBar P Q ↔
        (fld Q ∩ codom R).Nonempty ∧ ∀ a, a ∈ fld Q ∩ codom R →
          ((Desc (rlim R P Q) a (fun r => Desc (rlim R P˘ Q) a (fun s => r = s)) ∧
              Desc (rlim R P˘ Q) a (fun s => Desc (rlim R P Q˘) a (fun t => s = t))) ∧
              Desc (rlim R P Q˘) a (fun t => Desc (rlim R P˘ Q˘) a (fun u => t = u))) ∧
            Desc (rlim R P˘ Q˘) a (fun u => Desc R a (fun w => u = w))) := by
  rintro ⟨⟨hS, hd⟩, htr, hcon⟩
  refine ⟨fun h => ⟨h.1, pm234_72 ⟨⟨hS, htr, hcon⟩, h⟩⟩, fun ⟨hne, h⟩ => ⟨hne, fun a ha => ?_⟩⟩
  -- values lie in `C'P`, so `R''C'Q ⊂ C'P`
  have hR : R ʻʻ fld Q ⊆ fld P := by
    rintro u ⟨b, hbQ, hub⟩
    obtain ⟨v, hv, ⟨h1, -⟩, -⟩ := vals_of_chain (h b ⟨hbQ, u, hub⟩)
    rw [(hv u).1 hub]
    exact limax_fld (rlim_apply.1 ((h1 v).2 rfl))
  obtain ⟨v, hv, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := vals_of_chain (h a ha)
  have hc := connex_ancFres_of (S := refsRels Q a) hcon
  have hsub : refsRels Q a ⊆ fld Q := by
    rintro y ((h | ⟨-, h⟩) | h)
    · exact fld_of_left h
    · exact h
    · exact fld_of_right h
  have hsub1 : refs Q a ⊆ refsRels Q a := fun y h => Or.inl (Or.inl h)
  have hsub2 : rels Q a ⊆ refsRels Q a := fun y h => Or.inr h
  exact ⟨(pm234_522 ⟨⟨⟨⟨hS, htr⟩, connex_ancFres_sub hc hsub1⟩,
      fun u ⟨y, hy, huy⟩ => hR ⟨y, hsub (hsub1 hy), huy⟩⟩, hd⟩).2 ⟨eqDesc h1 h2, eqDesc h2 hv⟩,
    (pm234_522 (Q := Q˘) ⟨⟨⟨⟨hS, transR_cnv htr⟩,
      connex_ancFres_cnv (connex_ancFres_sub hc hsub2)⟩,
      fun u ⟨y, hy, huy⟩ => hR ⟨y, hsub (hsub2 hy), huy⟩⟩, hd⟩).2 ⟨eqDesc h3 h4, eqDesc h4 hv⟩⟩

end PrincipiaMathematica
