import PrincipiaMathematica.Defs.Part2

/-!
# Part II, Section C: One-many, many-one, and one-one relations

Volume 1. Numbers: ✱73, ✱74.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

/-! Helper lemmas for ✱73–✱74 (not PM propositions). -/

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

private theorem oo_iff' {R : α → β → Prop} :
    R ∈ arrow one one ↔ R ∈ arrow one Cls ∧ R ∈ arrow Cls one := by
  rw [mem_arrow_one_one, mem_arrow_one_Cls, mem_arrow_Cls_one]

private theorem oc_mono {R S : α → β → Prop} (h : R ∈ arrow one Cls)
    (hS : ∀ x y, S x y → R x y) : S ∈ arrow one Cls :=
  mem_arrow_one_Cls.2 fun x y z ⟨h1, h2⟩ => mem_arrow_one_Cls.1 h x y z ⟨hS _ _ h1, hS _ _ h2⟩

private theorem co_mono {R S : α → β → Prop} (h : R ∈ arrow Cls one)
    (hS : ∀ x y, S x y → R x y) : S ∈ arrow Cls one :=
  mem_arrow_Cls_one.2 fun x y z ⟨h1, h2⟩ => mem_arrow_Cls_one.1 h x y z ⟨hS _ _ h1, hS _ _ h2⟩

private theorem oo_mono {R S : α → β → Prop} (h : R ∈ arrow one one)
    (hS : ∀ x y, S x y → R x y) : S ∈ arrow one one :=
  oo_iff'.2 ⟨oc_mono (oo_iff'.1 h).1 hS, co_mono (oo_iff'.1 h).2 hS⟩

private theorem cnv_oc {R : α → β → Prop} : R˘ ∈ arrow one Cls ↔ R ∈ arrow Cls one := by
  rw [mem_arrow_one_Cls, mem_arrow_Cls_one]
  exact ⟨fun h x y z hh => h y z x hh, fun h x y z hh => h z x y hh⟩

private theorem cnv_co {R : α → β → Prop} : R˘ ∈ arrow Cls one ↔ R ∈ arrow one Cls := by
  rw [mem_arrow_one_Cls, mem_arrow_Cls_one]
  exact ⟨fun h x y z hh => h z x y hh, fun h x y z hh => h y z x hh⟩

private theorem cnv_oo {R : α → β → Prop} : R˘ ∈ arrow one one ↔ R ∈ arrow one one := by
  rw [oo_iff', oo_iff', cnv_oc, cnv_co, and_comm]

private theorem sm_of_mem {A : Set α} {B : Set β} {R : α → β → Prop} (h : R ∈ smbar A B) :
    sm A B := ⟨R, h⟩

private theorem mem_smbar {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ∈ smbar A B ↔ (R ∈ arrow one one ∧ A = dom R) ∧ B = codom R := Iff.rfl

private theorem dom_cres (R : α → β → Prop) (B : Set β) : dom (R ↾ B) = R ʻʻ B := by
  ext x; exact ⟨fun ⟨y, h, hy⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, h, hy⟩⟩

private theorem codom_cres (R : α → β → Prop) (B : Set β) : codom (R ↾ B) = codom R ∩ B := by
  ext y; exact ⟨fun ⟨x, h, hy⟩ => ⟨⟨x, h⟩, hy⟩, fun ⟨⟨x, h⟩, hy⟩ => ⟨x, h, hy⟩⟩

private theorem dom_dres (A : Set α) (R : α → β → Prop) : dom (A ◁ R) = dom R ∩ A := by
  ext x; exact ⟨fun ⟨y, hx, h⟩ => ⟨⟨y, h⟩, hx⟩, fun ⟨⟨y, h⟩, hx⟩ => ⟨y, hx, h⟩⟩

private theorem codom_dres (A : Set α) (R : α → β → Prop) : codom (A ◁ R) = R˘ ʻʻ A := by
  ext y; exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h⟩⟩

private theorem cnv_dres (A : Set α) (R : α → β → Prop) : (A ◁ R)˘ = R˘ ↾ A := by
  funext x y; exact propext and_comm

private theorem cnv_cres (R : α → β → Prop) (B : Set β) : (R ↾ B)˘ = B ◁ R˘ := by
  funext x y; exact propext and_comm

private theorem eq_inter_iff {A B : Set α} : A = B ∩ A ↔ A ⊆ B :=
  ⟨fun h x hx => (h ▸ hx : x ∈ B ∩ A).1, fun h => (Set.inter_eq_right.2 h).symm⟩

/-- General form of ✱73·142. -/
private theorem smbar_cres_iff {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ↾ B ∈ smbar A B ↔ (R ↾ B ∈ arrow one one ∧ B ⊆ codom R) ∧ A = R ʻʻ B := by
  rw [mem_smbar, dom_cres, codom_cres, eq_inter_iff]
  tauto

private theorem smbar_dres_iff {A : Set α} {B : Set β} {R : α → β → Prop} :
    A ◁ R ∈ smbar A B ↔ (A ◁ R ∈ arrow one one ∧ A ⊆ dom R) ∧ B = R˘ ʻʻ A := by
  rw [mem_smbar, dom_dres, codom_dres, eq_inter_iff]

/-- `R'y = R'z`, unfolded. -/
private theorem descEq_iff {R : α → β → Prop} {S : α → γ → Prop} {y : β} {z : γ} :
    Desc R y (fun b => Desc S z (fun c => b = c)) ↔
      ∃ b, (∀ x, R x y ↔ x = b) ∧ (∀ x, S x z ↔ x = b) := by
  constructor
  · rintro ⟨b, hb, c, hc, rfl⟩; exact ⟨b, hb, hc⟩
  · rintro ⟨b, hb, hc⟩; exact ⟨b, hb, b, hc, rfl⟩

private theorem descEq_graph (f : β → α) (y z : β) :
    Desc (graph f) y (fun b => Desc (graph f) z (fun c => b = c)) ↔ f y = f z :=
  (desc_graph f y _).trans (desc_graph f z _)

private theorem disj {A G : Set α} (h : A ∩ G = Λ) {x : α} (h1 : x ∈ A) (h2 : x ∈ G) : False := by
  have : x ∈ A ∩ G := ⟨h1, h2⟩
  rw [h, Null_eq_empty] at this
  exact this

private theorem disj_iff {A G : Set α} : A ∩ G = Λ ↔ ∀ x, x ∈ A → x ∈ G → False := by
  rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h x h1 h2 => h x ⟨h1, h2⟩, fun h x hx => h x hx.1 hx.2⟩

/-- For a many-one `T`, `T̆''T''β = β` when `β ⊂ ᗡ'T`. -/
private theorem img_cnv_img {T : α → β → Prop} {Y : Set β} (hT : T ∈ arrow Cls one)
    (hY : Y ⊆ codom T) : T˘ ʻʻ (T ʻʻ Y) = Y := by
  ext y
  constructor
  · rintro ⟨x, ⟨y', hy', hxy'⟩, hxy⟩
    exact (mem_arrow_Cls_one.1 hT x y' y ⟨hxy', hxy⟩) ▸ hy'
  · intro hy
    obtain ⟨x, hx⟩ := hY hy
    exact ⟨x, ⟨y, hy, hx⟩, hx⟩

private theorem img_img_cnv {T : α → β → Prop} {X : Set α} (hT : T ∈ arrow one Cls)
    (hX : X ⊆ dom T) : T ʻʻ (T˘ ʻʻ X) = X :=
  img_cnv_img (T := T˘) (cnv_co.2 hT) hX

private theorem relProd_assoc (R : α → β → Prop) (S : β → γ → Prop) (T : γ → δ → Prop) :
    R ⨾ S ⨾ T = R ⨾ (S ⨾ T) := by
  funext x w
  apply propext
  constructor
  · rintro ⟨z, ⟨y, h1, h2⟩, h3⟩; exact ⟨y, h1, z, h2, h3⟩
  · rintro ⟨y, h1, z, h2, h3⟩; exact ⟨z, ⟨y, h1, h2⟩, h3⟩

private theorem cancelR_imp {P P' : α → β → Prop} {Q : β → γ → Prop} {S : Set β}
    (hQ : ∀ y y' z, y ∈ S → y' ∈ S → Q y z → Q y' z → y = y')
    (hS : S ⊆ dom Q) (hP : codom P ⊆ S) (hP' : codom P' ⊆ S) (h : P ⨾ Q = P' ⨾ Q)
    (x : α) (y : β) (hxy : P x y) : P' x y := by
  have hy : y ∈ S := hP ⟨x, hxy⟩
  obtain ⟨z, hz⟩ := hS hy
  have h' : (P' ⨾ Q) x z := h ▸ ⟨y, hxy, hz⟩
  obtain ⟨y', h1, h2⟩ := h'
  rw [hQ y y' z hy (hP' ⟨x, h1⟩) hz h2]
  exact h1

private theorem cancelR {P P' : α → β → Prop} {Q : β → γ → Prop} {S : Set β}
    (hQ : ∀ y y' z, y ∈ S → y' ∈ S → Q y z → Q y' z → y = y')
    (hS : S ⊆ dom Q) (hP : codom P ⊆ S) (hP' : codom P' ⊆ S) (h : P ⨾ Q = P' ⨾ Q) : P = P' := by
  funext x y
  exact propext ⟨cancelR_imp hQ hS hP hP' h x y, cancelR_imp hQ hS hP' hP h.symm x y⟩

private theorem cancelL_imp {Q : γ → α → Prop} {P P' : α → β → Prop} {S : Set α}
    (hQ : ∀ w y y', y ∈ S → y' ∈ S → Q w y → Q w y' → y = y')
    (hS : S ⊆ codom Q) (hP : dom P ⊆ S) (hP' : dom P' ⊆ S) (h : Q ⨾ P = Q ⨾ P')
    (x : α) (y : β) (hxy : P x y) : P' x y := by
  have hx : x ∈ S := hP ⟨y, hxy⟩
  obtain ⟨w, hw⟩ := hS hx
  have h' : (Q ⨾ P') w y := h ▸ ⟨x, hw, hxy⟩
  obtain ⟨x', h1, h2⟩ := h'
  rw [hQ w x x' hx (hP' ⟨y, h2⟩) hw h1]
  exact h2

private theorem cancelL {Q : γ → α → Prop} {P P' : α → β → Prop} {S : Set α}
    (hQ : ∀ w y y', y ∈ S → y' ∈ S → Q w y → Q w y' → y = y')
    (hS : S ⊆ codom Q) (hP : dom P ⊆ S) (hP' : dom P' ⊆ S) (h : Q ⨾ P = Q ⨾ P') : P = P' := by
  funext x y
  exact propext ⟨cancelL_imp hQ hS hP hP' h x y, cancelL_imp hQ hS hP' hP h.symm x y⟩

/-!
## [✱73] Similarity of classes

*(Vol. 1, p. 476)*

> *Summary of* *73.
>
> Two classes \(\alpha\) and \(\beta\) are said to be *similar* when there is a one-one relation whose domain is \(\alpha\) and whose converse domain is \(\beta\). We express "\(\alpha\) is similar to \(\beta\)" by the notation "\(\alpha \mathop{\text{ sm }} \beta\)." When two classes are similar, they have the same cardinal number of terms: it is this fact which gives importance to the relation of similarity.
>
> We have \[ \alpha \mathop{\text{ sm }} \beta .\equiv. (\exists R) . R \in 1 \rightarrow 1 . \alpha = \text{D}ʻR . \beta = \text{ᗡ}ʻR\text{.} \]
>
> The relation of similarity is that of the domain of a \(1 \rightarrow 1\) to the converse domain, *i.e.* it is the relative product of \(\text{D} \upharpoonright (1 \rightarrow 1)\) and \((1 \rightarrow 1)\upharpoonleft \breve{\text{ᗡ}}\), or, what comes to the same thing, it is the relative product of \(\text{D} \upharpoonright 1 \rightarrow 1\) and \(\breve{\text{ᗡ}}\).
>
> Most of the properties of similarity result immediately from those of one-one relations and offer no difficulty of any kind.
>
> …

**Lean reading.** `α sm̄ β` is `smbar A B` and `α sm β` is `sm A B` (Defs/Part2); `R ∈ 1 → 1`, `1 → Cls`, `Cls → 1` are membership in `arrow one one`, `arrow one Cls`, `arrow Cls one`; `D'R`, `ᗡ'R` are `dom R`, `codom R`, and `α ↿ R`, `R ↾ β` are `A ◁ R`, `R ↾ B`. The two classes compared by `sm` may be of different types, except where PM's formula identifies them (`α ∪ γ`, `ᗡ'R ⊂ β ⊂ D'R`, `sm²`, …). `R'y = R'z` keeps both descriptions (`Desc R y (fun b => Desc R z (fun c => b = c))`) and `E!R'y` is `EDesc R y`; `ι`, `ῐ` are `iota`, `iota˘`, `x↓`, `↓x` are `coupleL x`, `coupleR x`, `R_∈`, `R'''κ` are `imgRel R`, `R ʻʻʻ K`. In ✱73·8–✱73·841 "Hp✱73·8" is written out. The Schröder–Bernstein theorem ✱73·88 is proved along PM's (Zermelo's) route ✱73·8–✱73·87; no cardinal theory of mathlib is used. Class variables `γ`, `δ` are named `G`, `H` (`C`, `D` are PM constants). Helper lemmas (private) precede the unit block.

**Status.** proved (all propositions; ✱73·01, ✱73·02 definition; ✱73·35, ✱73·52, ✱73·801 proved (reading), see their docstrings).
-/

/-- ✱73·01 (Df). \(\alpha\overline{\text{ sm }}\beta=1\rightarrow 1\cap \overleftarrow{\text{D}}ʻ\alpha\cap \overleftarrow{\text{ᗡ}}ʻ\beta \quad{\text{Df}}\) -/
theorem pm73_01 {A : Set α} {B : Set β} :
    smbar A B = arrow one one ∩ rels D A ∩ rels Dcnv B := rfl

/-- ✱73·02 (Df). \(\text{ sm }=\hat{\alpha}\hat{\beta}(\exists !\alpha\overline{\text{ sm }}\beta) \quad{\text{Df}}\) -/
theorem pm73_02 : (sm : Set α → Set β → Prop) = fun A B => (smbar A B).Nonempty := rfl

/-- ✱73·03. \(\vdash:R\in \alpha\overline{\text{ sm }}\beta.\equiv.R\in 1\rightarrow 1.\alpha=\text{D}ʻR.\beta=\text{ᗡ}ʻR \quad[\text{*33·6·61.(*73·01)}]\) -/
theorem pm73_03 {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ∈ smbar A B ↔ (R ∈ arrow one one ∧ A = dom R) ∧ B = codom R := Iff.rfl

/-- ✱73·04. \(\vdash:\alpha \text{ sm } \beta.\equiv.\exists !\alpha\overline{\text{ sm }}\beta \quad[\text{(*73·02)}]\) -/
theorem pm73_04 {A : Set α} {B : Set β} : sm A B ↔ (smbar A B).Nonempty := Iff.rfl

/-- ✱73·1. \(\vdash:\alpha \text{ sm } \beta.\equiv.(\exists R).R\in 1\rightarrow 1.\alpha=\text{D}ʻR.\beta=\text{ᗡ}ʻR \quad[\text{*73·03·04}]\) -/
theorem pm73_1 {A : Set α} {B : Set β} :
    sm A B ↔ ∃ R : α → β → Prop, (R ∈ arrow one one ∧ A = dom R) ∧ B = codom R := sm_iff

private theorem codom_eq_cnv_img_dom (R : α → β → Prop) : codom R = R˘ ʻʻ dom R := by
  ext y; exact ⟨fun ⟨x, h⟩ => ⟨x, ⟨y, h⟩, h⟩, fun ⟨x, _, h⟩ => ⟨x, h⟩⟩

private theorem dom_eq_img_codom (R : α → β → Prop) : dom R = R ʻʻ codom R := by
  ext x; exact ⟨fun ⟨y, h⟩ => ⟨y, ⟨x, h⟩, h⟩, fun ⟨y, _, h⟩ => ⟨y, h⟩⟩

/-- General form of ✱73·21, second half. -/
private theorem dres_mem_smbar {A : Set α} {R : α → β → Prop} (hR : R ∈ arrow one one)
    (hA : A ⊆ dom R) : A ◁ R ∈ smbar A (R˘ ʻʻ A) :=
  smbar_dres_iff.2 ⟨⟨oo_mono hR fun _ _ h => h.2, hA⟩, rfl⟩

/-- General form of ✱73·22, second half. -/
private theorem cres_mem_smbar {B : Set β} {R : α → β → Prop} (hR : R ∈ arrow one one)
    (hB : B ⊆ codom R) : R ↾ B ∈ smbar (R ʻʻ B) B :=
  smbar_cres_iff.2 ⟨⟨oo_mono hR fun _ _ h => h.1, hB⟩, rfl⟩

/-- ✱73·11. \(\vdash:\alpha \text{ sm } \beta.\equiv.(\exists R).R\in 1\rightarrow 1.\alpha\subset \text{D}ʻR.\beta=\breve{R}ʻʻ\alpha\) -/
theorem pm73_11 {A : Set α} {B : Set β} :
    sm A B ↔ ∃ R : α → β → Prop, (R ∈ arrow one one ∧ A ⊆ dom R) ∧ B = R˘ ʻʻ A := by
  constructor
  · rintro ⟨R, ⟨hR, rfl⟩, rfl⟩
    exact ⟨R, ⟨hR, le_rfl⟩, codom_eq_cnv_img_dom R⟩
  · rintro ⟨R, ⟨hR, hA⟩, rfl⟩
    exact sm_of_mem (dres_mem_smbar hR hA)

/-- ✱73·12. \[\begin{align}&\vdash:\alpha\text{ sm }\beta.\equiv.(\exists R).R\in 1\rightarrow 1.\beta\subset \text{ᗡ}ʻR.\alpha=Rʻʻ\beta\\ &\text{[Proof as in *73·11}]\end{align}\] -/
theorem pm73_12 {A : Set α} {B : Set β} :
    sm A B ↔ ∃ R : α → β → Prop, (R ∈ arrow one one ∧ B ⊆ codom R) ∧ A = R ʻʻ B := by
  constructor
  · rintro ⟨R, ⟨hR, rfl⟩, rfl⟩
    exact ⟨R, ⟨hR, le_rfl⟩, dom_eq_img_codom R⟩
  · rintro ⟨R, ⟨hR, hB⟩, rfl⟩
    exact sm_of_mem (cres_mem_smbar hR hB)

/-- General form of ✱73·23, second half. -/
private theorem cres_mem_smbar' {B : Set β} {R : α → β → Prop} (h1 : R ∈ arrow one Cls)
    (hB : B ⊆ codom R) (h2 : R ↾ B ∈ arrow Cls one) : R ↾ B ∈ smbar (R ʻʻ B) B :=
  smbar_cres_iff.2 ⟨⟨oo_iff'.2 ⟨oc_mono h1 fun _ _ h => h.1, h2⟩, hB⟩, rfl⟩

private theorem dres_mem_smbar' {A : Set α} {R : α → β → Prop} (h1 : R ∈ arrow Cls one)
    (hA : A ⊆ dom R) (h2 : A ◁ R ∈ arrow one Cls) : A ◁ R ∈ smbar A (R˘ ʻʻ A) :=
  smbar_dres_iff.2 ⟨⟨oo_iff'.2 ⟨h2, co_mono h1 fun _ _ h => h.2⟩, hA⟩, rfl⟩

/-- ✱73·13. \(\vdash:\alpha\text{ sm }\beta.\equiv.(\exists R).R\in 1\rightarrow \text{Cls}.R\upharpoonright \beta\in \text{Cls}\rightarrow 1.\beta\subset \text{ᗡ}ʻR.\alpha=Rʻʻ\beta\) -/
theorem pm73_13 {A : Set α} {B : Set β} :
    sm A B ↔ ∃ R : α → β → Prop,
      ((R ∈ arrow one Cls ∧ R ↾ B ∈ arrow Cls one) ∧ B ⊆ codom R) ∧ A = R ʻʻ B := by
  constructor
  · intro h
    obtain ⟨R, ⟨hR, hB⟩, rfl⟩ := pm73_12.1 h
    exact ⟨R, ⟨⟨(oo_iff'.1 hR).1, co_mono (oo_iff'.1 hR).2 fun _ _ h => h.1⟩, hB⟩, rfl⟩
  · rintro ⟨R, ⟨⟨h1, h2⟩, hB⟩, rfl⟩
    exact sm_of_mem (cres_mem_smbar' h1 hB h2)

/-- ✱73·131. \[\begin{align}&\vdash:\alpha\text{ sm }\beta.\equiv.(\exists R).R\in \text{Cls}\rightarrow 1.\alpha \upharpoonleft R\in 1\rightarrow \text{Cls}.\alpha\subset DʻR.\beta=\breve{R}ʻʻ\alpha\\ &[\text{Proof as in *73·13}]\end{align}\] -/
theorem pm73_131 {A : Set α} {B : Set β} :
    sm A B ↔ ∃ R : α → β → Prop,
      ((R ∈ arrow Cls one ∧ A ◁ R ∈ arrow one Cls) ∧ A ⊆ dom R) ∧ B = R˘ ʻʻ A := by
  constructor
  · intro h
    obtain ⟨R, ⟨hR, hA⟩, rfl⟩ := pm73_11.1 h
    exact ⟨R, ⟨⟨(oo_iff'.1 hR).2, oc_mono (oo_iff'.1 hR).1 fun _ _ h => h.2⟩, hA⟩, rfl⟩
  · rintro ⟨R, ⟨⟨h1, h2⟩, hA⟩, rfl⟩
    exact sm_of_mem (dres_mem_smbar' h1 hA h2)

/-- For a one-many `R` and `β ⊂ ᗡ'R`: `R ↾ β` is many-one iff `R'y = R'z` implies `y = z`
on `β`. -/
private theorem cres_co_iff {B : Set β} {R : α → β → Prop} (h1 : R ∈ arrow one Cls) :
    R ↾ B ∈ arrow Cls one ↔
      ∀ y z, (y ∈ B ∧ z ∈ B) ∧ Desc R y (fun b => Desc R z (fun c => b = c)) → y = z := by
  rw [mem_arrow_Cls_one]
  constructor
  · rintro h y z ⟨⟨hy, hz⟩, he⟩
    obtain ⟨b, hb, hc⟩ := descEq_iff.1 he
    exact h b y z ⟨⟨(hb b).2 rfl, hy⟩, ⟨(hc b).2 rfl, hz⟩⟩
  · rintro h x y z ⟨⟨hxy, hy⟩, ⟨hxz, hz⟩⟩
    refine h y z ⟨⟨hy, hz⟩, descEq_iff.2 ⟨x, fun w => ⟨fun hw => ?_, fun e => e ▸ hxy⟩,
      fun w => ⟨fun hw => ?_, fun e => e ▸ hxz⟩⟩⟩
    · exact mem_arrow_one_Cls.1 h1 w x y ⟨hw, hxy⟩
    · exact mem_arrow_one_Cls.1 h1 w x z ⟨hw, hxz⟩

/-- ✱73·14. \[\begin{align}&\vdash\colon\ldotp \alpha\text{ sm }\beta.\equiv:(\exists R):R\in 1\rightarrow \text{Cls}.\beta\subset \text{ᗡ}ʻR.\alpha=Rʻʻ\beta:\\ & y,z\in \beta.Rʻy=Rʻz.\supset_{y,z}.y=z\end{align}\] -/
theorem pm73_14 {A : Set α} {B : Set β} :
    sm A B ↔ ∃ R : α → β → Prop, ((R ∈ arrow one Cls ∧ B ⊆ codom R) ∧ A = R ʻʻ B) ∧
      ∀ y z, (y ∈ B ∧ z ∈ B) ∧ Desc R y (fun b => Desc R z (fun c => b = c)) → y = z := by
  rw [pm73_13]
  constructor
  · rintro ⟨R, ⟨⟨h1, h2⟩, hB⟩, hA⟩
    exact ⟨R, ⟨⟨h1, hB⟩, hA⟩, (cres_co_iff h1).1 h2⟩
  · rintro ⟨R, ⟨⟨h1, hB⟩, hA⟩, h⟩
    exact ⟨R, ⟨⟨h1, (cres_co_iff h1).2 h⟩, hB⟩, hA⟩

/-- ✱73·141. \[\begin{align}\vdash\colon\ldotp \alpha\text{ sm }\beta.\equiv:(\exists R):R\in \text{Cls}\rightarrow 1.\alpha\subset &\text{D}ʻR.\beta=\breve{R}ʻʻ\alpha:\\ & y,z\in \alpha.\breve{R}ʻy=\breve{R}ʻz.\supset_{y,z}.y=z\\ [\text{Proof as in *73·14}]\end{align}\] -/
theorem pm73_141 {A : Set α} {B : Set β} :
    sm A B ↔ ∃ R : α → β → Prop, ((R ∈ arrow Cls one ∧ A ⊆ dom R) ∧ B = R˘ ʻʻ A) ∧
      ∀ y z, (y ∈ A ∧ z ∈ A) ∧ Desc R˘ y (fun b => Desc R˘ z (fun c => b = c)) → y = z := by
  rw [pm73_131]
  constructor
  · rintro ⟨R, ⟨⟨h1, h2⟩, hA⟩, hB⟩
    refine ⟨R, ⟨⟨h1, hA⟩, hB⟩, (cres_co_iff (R := R˘) (cnv_oc.2 h1)).1 ?_⟩
    rw [← cnv_dres]; exact cnv_co.2 h2
  · rintro ⟨R, ⟨⟨h1, hA⟩, hB⟩, h⟩
    have h2 := (cres_co_iff (R := R˘) (B := A) (cnv_oc.2 h1)).2 h
    rw [← cnv_dres, cnv_co] at h2
    exact ⟨R, ⟨⟨h1, h2⟩, hA⟩, hB⟩

/-- ✱73·142. \(\vdash:R\upharpoonright \beta\in \alpha\overline{\text{ sm }}\beta.\equiv.R\upharpoonright \beta\in 1\rightarrow 1.\beta\subset \text{ᗡ}ʻR.\alpha=Rʻʻ\beta\) -/
theorem pm73_142 {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ↾ B ∈ smbar A B ↔ (R ↾ B ∈ arrow one one ∧ B ⊆ codom R) ∧ A = R ʻʻ B := smbar_cres_iff

/-- ✱73·15. \(\vdash:\alpha\text{ sm }\beta.\equiv.(\exists R).R\upharpoonright \beta\in 1\rightarrow 1.\beta\subset \text{ᗡ}ʻR.\alpha=Rʻʻ\beta\) -/
theorem pm73_15 {A : Set α} {B : Set β} :
    sm A B ↔ ∃ R : α → β → Prop, (R ↾ B ∈ arrow one one ∧ B ⊆ codom R) ∧ A = R ʻʻ B := by
  constructor
  · intro h
    obtain ⟨R, ⟨hR, hB⟩, hA⟩ := pm73_12.1 h
    exact ⟨R, ⟨oo_mono hR fun _ _ h => h.1, hB⟩, hA⟩
  · rintro ⟨R, h⟩
    exact sm_of_mem (pm73_142.2 h)

/-- ✱73·2. \(\vdash:R\in 1\rightarrow 1.\supset.\text{D}ʻR\text{ sm }\text{ᗡ}ʻR.\text{ᗡ}ʻR\text{ sm }\text{D}ʻR\) -/
theorem pm73_2 {R : α → β → Prop} :
    R ∈ arrow one one → sm (dom R) (codom R) ∧ sm (codom R) (dom R) := by
  intro hR
  exact ⟨⟨R, ⟨hR, rfl⟩, rfl⟩, ⟨R˘, ⟨cnv_oo.2 hR, rfl⟩, rfl⟩⟩

/-- ✱73·21. \(\vdash:R\in 1\rightarrow 1.\alpha\subset \text{D}ʻR.\supset.\alpha\text{ sm }\breve{R}ʻʻ\alpha.\alpha\upharpoonleft R\in \alpha\overline{\text{ sm }}(\breve{R}ʻʻ\alpha) \quad[\text{*73·11}]\) -/
theorem pm73_21 {A : Set α} {R : α → β → Prop} :
    R ∈ arrow one one ∧ A ⊆ dom R → sm A (R˘ ʻʻ A) ∧ A ◁ R ∈ smbar A (R˘ ʻʻ A) :=
  fun ⟨hR, hA⟩ => ⟨sm_of_mem (dres_mem_smbar hR hA), dres_mem_smbar hR hA⟩

/-- ✱73·22. \(\vdash:R\in 1\rightarrow 1.\beta\subset \text{ᗡ}ʻR.\supset.Rʻʻ\beta\text{ sm }\beta.R\upharpoonright \beta\in (Rʻʻ\beta)\overline{\text{ sm }}\beta \quad[\text{*73·12}]\) -/
theorem pm73_22 {B : Set β} {R : α → β → Prop} :
    R ∈ arrow one one ∧ B ⊆ codom R → sm (R ʻʻ B) B ∧ R ↾ B ∈ smbar (R ʻʻ B) B :=
  fun ⟨hR, hB⟩ => ⟨sm_of_mem (cres_mem_smbar hR hB), cres_mem_smbar hR hB⟩

/-- ✱73·23. \[\begin{align}\vdash:R\in 1\rightarrow \text{Cls}.\beta\subset \text{ᗡ}ʻR.&R\upharpoonright \beta\in \text{Cls}\rightarrow 1.\supset.\\ &Rʻʻ\beta\text{ sm }\beta.R\upharpoonright \beta\in (Rʻʻ\beta)\overline{\text{ sm }}\beta \quad[\text{*73·13}]\end{align}\] -/
theorem pm73_23 {B : Set β} {R : α → β → Prop} :
    (R ∈ arrow one Cls ∧ B ⊆ codom R) ∧ R ↾ B ∈ arrow Cls one →
      sm (R ʻʻ B) B ∧ R ↾ B ∈ smbar (R ʻʻ B) B :=
  fun ⟨⟨h1, hB⟩, h2⟩ => ⟨sm_of_mem (cres_mem_smbar' h1 hB h2), cres_mem_smbar' h1 hB h2⟩

/-- ✱73·231. \[\begin{align}\vdash:R\in \text{Cls}\rightarrow 1.\alpha\subset DʻR.&\alpha\upharpoonleft R\in 1\rightarrow \text{Cls}.\supset.\\ &\alpha\text{ sm }\breve{R}ʻʻ\alpha.\alpha\upharpoonleft R\in \alpha\overline{\text{ sm }}(\breve{R}ʻʻ\alpha) \quad[\text{*73·131}]\end{align}\] -/
theorem pm73_231 {A : Set α} {R : α → β → Prop} :
    (R ∈ arrow Cls one ∧ A ⊆ dom R) ∧ A ◁ R ∈ arrow one Cls →
      sm A (R˘ ʻʻ A) ∧ A ◁ R ∈ smbar A (R˘ ʻʻ A) :=
  fun ⟨⟨h1, hA⟩, h2⟩ => ⟨sm_of_mem (dres_mem_smbar' h1 hA h2), dres_mem_smbar' h1 hA h2⟩

/-- ✱73·24. \[\begin{align}\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\beta\subset \text{ᗡ}ʻR&:y,\,z\in \beta.Rʻy=Rʻz.\supset_{y,z}.y=z:\supset.\\ &Rʻʻ\beta\text{ sm }\beta.R\upharpoonright \beta\in (Rʻʻ\beta)\overline{\text{ sm }}\beta \quad[\text{*73·14·142}]\end{align}\] -/
theorem pm73_24 {B : Set β} {R : α → β → Prop} :
    (R ∈ arrow one Cls ∧ B ⊆ codom R) ∧
        (∀ y z, (y ∈ B ∧ z ∈ B) ∧ Desc R y (fun b => Desc R z (fun c => b = c)) → y = z) →
      sm (R ʻʻ B) B ∧ R ↾ B ∈ smbar (R ʻʻ B) B :=
  fun ⟨⟨h1, hB⟩, h⟩ => pm73_23 ⟨⟨h1, hB⟩, (cres_co_iff h1).2 h⟩

/-- ✱73·241. \[\begin{align}\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\alpha\subset \text{D}ʻR:&y,\,z\in \alpha.\breve{R}ʻy=\breve{R}ʻz.\supset_{y,z}.y=z:\supset.\\ &\alpha\text{ sm }\breve{R}ʻʻ\alpha.\alpha\upharpoonleft R\in \alpha\overline{\text{ sm }}\breve{R}ʻʻ\alpha \quad[\text{*73·141·03}]\end{align}\] -/
theorem pm73_241 {A : Set α} {R : α → β → Prop} :
    (R ∈ arrow Cls one ∧ A ⊆ dom R) ∧
        (∀ y z, (y ∈ A ∧ z ∈ A) ∧ Desc R˘ y (fun b => Desc R˘ z (fun c => b = c)) → y = z) →
      sm A (R˘ ʻʻ A) ∧ A ◁ R ∈ smbar A (R˘ ʻʻ A) := by
  rintro ⟨⟨h1, hA⟩, h⟩
  have h2 := (cres_co_iff (R := R˘) (B := A) (cnv_oc.2 h1)).2 h
  rw [← cnv_dres, cnv_co] at h2
  exact pm73_231 ⟨⟨h1, hA⟩, h2⟩

private theorem oc_of_EDesc {R : α → β → Prop} (h : ∀ y, EDesc R y) : R ∈ arrow one Cls :=
  mem_arrow_one_Cls.2 fun x y z ⟨hx, hy⟩ => by
    obtain ⟨b, hb⟩ := h z
    exact ((hb x).1 hx).trans ((hb y).1 hy).symm

private theorem codom_of_EDesc {R : α → β → Prop} (h : ∀ y, EDesc R y) (B : Set β) :
    B ⊆ codom R := fun y _ => by
  obtain ⟨b, hb⟩ := h y
  exact ⟨b, (hb b).2 rfl⟩

/-- ✱73·25. \(\vdash\colon\ldotp (y).\text{E}!Rʻy:y,z\in \beta.Rʻy=Rʻz.\supset_{y,z}.y=z:\supset.Rʻʻ\beta\text{ sm }\beta\) -/
theorem pm73_25 {B : Set β} {R : α → β → Prop} :
    (∀ y, EDesc R y) ∧
        (∀ y z, (y ∈ B ∧ z ∈ B) ∧ Desc R y (fun b => Desc R z (fun c => b = c)) → y = z) →
      sm (R ʻʻ B) B :=
  fun ⟨hE, h⟩ => (pm73_24 ⟨⟨oc_of_EDesc hE, codom_of_EDesc hE B⟩, h⟩).1

/-- ✱73·26. \(\vdash\colon\ldotp (y).\text{E}!Rʻy:R\in 1\rightarrow 1:\supset.Rʻʻ\beta \text{ sm }\beta.R\upharpoonright \beta\in (Rʻʻ\beta)\overline{\text{ sm }}\beta\) -/
theorem pm73_26 {B : Set β} {R : α → β → Prop} :
    (∀ y, EDesc R y) ∧ R ∈ arrow one one → sm (R ʻʻ B) B ∧ R ↾ B ∈ smbar (R ʻʻ B) B :=
  fun ⟨hE, hR⟩ => pm73_22 ⟨hR, codom_of_EDesc hE B⟩

private theorem cres_smbar_of_inj {B : Set β} {R : α → β → Prop} :
    (∀ y z, y ∈ B ∧ z ∈ B → (Desc R y (fun b => Desc R z (fun c => b = c)) ↔ y = z)) →
      sm (R ʻʻ B) B ∧ R ↾ B ∈ smbar (R ʻʻ B) B := by
  intro h
  have hE : ∀ y, y ∈ B → ∃ b, ∀ x, R x y ↔ x = b := fun y hy => by
    obtain ⟨b, hb, -⟩ := descEq_iff.1 ((h y y ⟨hy, hy⟩).2 rfl)
    exact ⟨b, hb⟩
  have hB : B ⊆ codom R := fun y hy => by
    obtain ⟨b, hb⟩ := hE y hy
    exact ⟨b, (hb b).2 rfl⟩
  have h1 : R ↾ B ∈ arrow one Cls := mem_arrow_one_Cls.2 fun x y z ⟨⟨hx, hz⟩, ⟨hy, _⟩⟩ => by
    obtain ⟨b, hb⟩ := hE z hz
    exact ((hb x).1 hx).trans ((hb y).1 hy).symm
  have h2 : R ↾ B ∈ arrow Cls one := mem_arrow_Cls_one.2 fun x y z ⟨⟨hxy, hy⟩, ⟨hxz, hz⟩⟩ => by
    obtain ⟨b, hb⟩ := hE y hy
    obtain ⟨c, hc⟩ := hE z hz
    have e1 := (hb x).1 hxy
    have e2 := (hc x).1 hxz
    refine (h y z ⟨hy, hz⟩).1 (descEq_iff.2 ⟨x, fun w => ?_, fun w => ?_⟩)
    · rw [hb w, e1]
    · rw [hc w, e2]
  have hm : R ↾ B ∈ smbar (R ʻʻ B) B := smbar_cres_iff.2 ⟨⟨oo_iff'.2 ⟨h1, h2⟩, hB⟩, rfl⟩
  exact ⟨sm_of_mem hm, hm⟩

/-- ✱73·27. \[\begin{align}&\vdash\colon\ldotp Rʻy=Rʻz.\equiv_{y,z}.y=z:\supset.Rʻʻ\beta\text{ sm }\beta.R\upharpoonright \beta\in (Rʻʻ\beta)\overline{\text{ sm }}\beta\\ &[\text{*73·26.*71·57}]\end{align}\] -/
theorem pm73_27 {B : Set β} {R : α → β → Prop} :
    (∀ y z, Desc R y (fun b => Desc R z (fun c => b = c)) ↔ y = z) →
      sm (R ʻʻ B) B ∧ R ↾ B ∈ smbar (R ʻʻ B) B :=
  fun h => cres_smbar_of_inj fun y z _ => h y z

/-- ✱73·28. \[\begin{align}\vdash\colon\colon y,\,z \in \beta.\supset_{y,z}:Rʻy=Rʻz.\equiv.y=&z\colon\ldotp \supset.\\ &Rʻʻ\beta \text{ sm }\beta.R\upharpoonright \beta\in (Rʻʻ\beta)\overline{\text{ sm }}\beta \end{align}\] -/
theorem pm73_28 {B : Set β} {R : α → β → Prop} :
    (∀ y z, y ∈ B ∧ z ∈ B → (Desc R y (fun b => Desc R z (fun c => b = c)) ↔ y = z)) →
      sm (R ʻʻ B) B ∧ R ↾ B ∈ smbar (R ʻʻ B) B := cres_smbar_of_inj

/-- ✱73·3. \(\vdash.\alpha\text{ sm }\alpha.I\upharpoonright \alpha\in \alpha\overline{\text{ sm }}\alpha\) -/
theorem pm73_3 {A : Set α} : sm A A ∧ I ↾ A ∈ smbar A A := by
  have hI : (I : α → α → Prop) ∈ arrow one one :=
    mem_arrow_one_one.2 ⟨fun x y z ⟨h1, h2⟩ => h1.trans h2.symm, fun x y z ⟨h1, h2⟩ => h1.symm.trans h2⟩
  have hA : A ⊆ codom I := fun y _ => ⟨y, rfl⟩
  have himg : I ʻʻ A = A := by
    ext x; exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have := pm73_22 ⟨hI, hA⟩
  rw [himg] at this
  exact this

/-- ✱73·301. \(\vdash:R\in \alpha\overline{\text{ sm }}\beta.\equiv.\breve{R}\in \beta\overline{\text{ sm }}\alpha\) -/
theorem pm73_301 {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ∈ smbar A B ↔ R˘ ∈ smbar B A := by
  rw [mem_smbar, mem_smbar, cnv_oo]
  show (R ∈ arrow one one ∧ A = dom R) ∧ B = codom R ↔
    (R ∈ arrow one one ∧ B = codom R) ∧ A = dom R
  tauto

/-- ✱73·31. \(\vdash:\alpha\text{ sm }\beta.\equiv.\beta\text{ sm }\alpha \quad[\text{*73·301·04.*31·52}]\) -/
theorem pm73_31 {A : Set α} {B : Set β} : sm A B ↔ sm B A :=
  ⟨fun ⟨R, h⟩ => ⟨R˘, pm73_301.1 h⟩, fun ⟨R, h⟩ => ⟨R˘, pm73_301.1 h⟩⟩

/-- ✱73·311. \(\vdash:R\in \alpha\overline{\text{ sm }}\beta.S\in \beta\overline{\text{ sm }}\gamma.\supset.R\mid S\in \alpha\overline{\text{ sm }}\gamma\) -/
theorem pm73_311 {A : Set α} {B : Set β} {G : Set γ} {R : α → β → Prop} {S : β → γ → Prop} :
    R ∈ smbar A B ∧ S ∈ smbar B G → R ⨾ S ∈ smbar A G := by
  rintro ⟨⟨⟨hR, rfl⟩, rfl⟩, ⟨⟨hS, hB⟩, rfl⟩⟩
  obtain ⟨hR1, hR2⟩ := mem_arrow_one_one.1 hR
  obtain ⟨hS1, hS2⟩ := mem_arrow_one_one.1 hS
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨u, h1, h2⟩, ⟨v, h3, h4⟩⟩
    exact hR1 x y u ⟨h1, (hS1 u v z ⟨h2, h4⟩) ▸ h3⟩
  · rintro x y z ⟨⟨u, h1, h2⟩, ⟨v, h3, h4⟩⟩
    exact hS2 u y z ⟨h2, (hR2 x v u ⟨h3, h1⟩) ▸ h4⟩
  · ext x
    constructor
    · rintro ⟨u, h⟩
      obtain ⟨w, hw⟩ : u ∈ dom S := hB ▸ ⟨x, h⟩
      exact ⟨w, u, h, hw⟩
    · rintro ⟨w, u, h, -⟩; exact ⟨u, h⟩
  · ext z
    constructor
    · rintro ⟨u, h⟩
      obtain ⟨x, hx⟩ : u ∈ codom R := hB.symm ▸ ⟨z, h⟩
      exact ⟨x, u, hx, h⟩
    · rintro ⟨x, u, -, h⟩; exact ⟨u, h⟩

/-- ✱73·32. \(\vdash:\alpha\text{ sm }\beta.\beta\text{ sm }\gamma.\supset.\alpha\text{ sm }\gamma \quad[\text{*73·311·04}]\) -/
theorem pm73_32 {A : Set α} {B : Set β} {G : Set γ} : sm A B ∧ sm B G → sm A G :=
  fun ⟨⟨R, hR⟩, ⟨S, hS⟩⟩ => ⟨R ⨾ S, pm73_311 ⟨hR, hS⟩⟩

/-- ✱73·33. \(\vdash.\text{Cnv}ʻ\text{ sm }=\text{ sm } \quad[\text{*73·31.*31·131}]\)

`Cnv'sm` is written `sm˘` (`desc_Cnv`, Basic §5). -/
theorem pm73_33 : (sm : Set α → Set β → Prop)˘ = sm := by
  funext B A
  exact propext pm73_31.symm

/-- ✱73·34. \(\vdash.\text{ sm }^{2}=\text{ sm }\)

`sm²` is `rsq sm`; `rsq` (✱34·02) is homogeneous, so `sm` is here the relation between classes of one type. -/
theorem pm73_34 : rsq (sm : Set α → Set α → Prop) = sm := by
  funext A G
  apply propext
  constructor
  · rintro ⟨B, h1, h2⟩; exact pm73_32 ⟨h1, h2⟩
  · intro h; exact ⟨A, pm73_3.1, h⟩

/-- ✱73·35. \(\vdash.\text{D}ʻ\text{ sm }=\text{ᗡ}ʻ\text{ sm }=\text{Cls}\)

**Status.** proved (reading): `sm` is typically ambiguous, and PM's proof (from ✱73·3, `α sm α`) takes it homogeneous; so `D'sm` and `ᗡ'sm` are taken for `sm` between classes of one type `α`, where both are `Cls`. For a heterogeneous `sm` (classes of `α` and of `β`) the domain is only the classes of `α` similar to some class of `β`, which in Lean need not be all of `Cls` (e.g. when `β` is empty). The chain `D'sm = ᗡ'sm = Cls` is the conjunction of its links. -/
theorem pm73_35 :
    dom (sm : Set α → Set α → Prop) = codom (sm : Set α → Set α → Prop) ∧
      codom (sm : Set α → Set α → Prop) = Cls := by
  have h1 : dom (sm : Set α → Set α → Prop) = Set.univ :=
    Set.eq_univ_of_forall fun A => ⟨A, pm73_3.1⟩
  have h2 : codom (sm : Set α → Set α → Prop) = Set.univ :=
    Set.eq_univ_of_forall fun A => ⟨A, pm73_3.1⟩
  rw [h1, h2, Cls_eq_univ]
  exact ⟨rfl, rfl⟩

/-- ✱73·36. \(\vdash\colon\ldotp \alpha\text{ sm }\beta.\supset:\exists !\alpha.\equiv.\exists !\beta\) -/
theorem pm73_36 {A : Set α} {B : Set β} : sm A B → (A.Nonempty ↔ B.Nonempty) := by
  rintro ⟨R, ⟨_, rfl⟩, rfl⟩
  exact ⟨fun ⟨x, y, h⟩ => ⟨y, x, h⟩, fun ⟨y, x, h⟩ => ⟨x, y, h⟩⟩

/-- ✱73·37. \(\vdash\colon\ldotp \alpha\text{ sm }\beta.\supset:\gamma\text{ sm }\alpha.\equiv.\gamma\text{ sm }\beta\) -/
theorem pm73_37 {A : Set α} {B : Set β} {G : Set γ} : sm A B → (sm G A ↔ sm G B) :=
  fun h => ⟨fun h' => pm73_32 ⟨h', h⟩, fun h' => pm73_32 ⟨h', pm73_31.1 h⟩⟩

/-- ✱73·4. \(\vdash.\text{Cnv}ʻʻ\lambda\text{ sm }\lambda.\text{Cnv}\upharpoonright \lambda\in (\text{Cnv}ʻʻ\lambda)\overline{\text{ sm }}\lambda \quad[\text{*73·26.*72·11.*31·13}]\) -/
theorem pm73_4 {L : Set (α → β → Prop)} :
    sm (Cnv ʻʻ L) L ∧ Cnv ↾ L ∈ smbar (Cnv ʻʻ L) L := by
  have hE : ∀ P : α → β → Prop, EDesc Cnv P := fun P => ⟨P˘, fun _ => Cnv_iff⟩
  have hR : (Cnv : (β → α → Prop) → (α → β → Prop) → Prop) ∈ arrow one one := by
    refine mem_arrow_one_one.2 ⟨fun x y z ⟨h1, h2⟩ => ?_, fun x y z ⟨h1, h2⟩ => ?_⟩
    · rw [Cnv_iff.1 h1, Cnv_iff.1 h2]
    · have e1 := Cnv_iff.1 h1
      have e2 := Cnv_iff.1 h2
      have : y˘ = z˘ := e1.symm.trans e2
      exact congrArg cnv this
  exact pm73_26 ⟨hE, hR⟩

/-- ✱73·41. \(\vdash.\iotaʻʻ\alpha\text{ sm }\alpha.\iota\upharpoonright \alpha\in (\iotaʻʻ\alpha)\overline{\text{ sm }}\alpha \quad[\text{*73·26.*72·18.*51·12}]\) -/
theorem pm73_41 {A : Set α} : sm (iota ʻʻ A) A ∧ iota ↾ A ∈ smbar (iota ʻʻ A) A :=
  pm73_27 fun y z => (descEq_graph unitCls y z).trans unitCls_injective.eq_iff

private theorem iota_oo : (iota : Set α → α → Prop) ∈ arrow one one :=
  mem_arrow_one_one.2 ⟨fun _ _ _ ⟨h1, h2⟩ => h1.trans h2.symm,
    fun _ _ _ ⟨h1, h2⟩ => unitCls_injective (h1.symm.trans h2)⟩

/-- ✱73·42. \(\vdash:\alpha\subset 1.\supset.\alpha\text{ sm }\breve{\iota}ʻʻ\alpha\) -/
theorem pm73_42 {A : Set (Set α)} : A ⊆ one → sm A (iota˘ ʻʻ A) := fun h =>
  (pm73_21 ⟨iota_oo, fun B hB => by obtain ⟨x, rfl⟩ := h hB; exact ⟨x, rfl⟩⟩).1

/-- ✱73·43. \(\vdash.\iotaʻx\text{ sm }\iotaʻy.x\downarrow y\in (\iotaʻx)\overline{\text{ sm }}(\iotaʻy) \quad[\text{*55·15.*72·182.*73·2}]\) -/
theorem pm73_43 {x : α} {y : β} : sm (ι x) (ι y) ∧ x ↓ y ∈ smbar (ι x) (ι y) := by
  have h : x ↓ y ∈ smbar (ι x) (ι y) := by
    refine ⟨⟨mem_arrow_one_one.2 ⟨fun a b c ⟨h1, h2⟩ => h1.1.trans h2.1.symm,
      fun a b c ⟨h1, h2⟩ => h1.2.trans h2.2.symm⟩, ?_⟩, ?_⟩
    · ext a; exact ⟨fun h => ⟨y, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
    · ext b; exact ⟨fun h => ⟨x, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  exact ⟨sm_of_mem h, h⟩

/-- ✱73·44. \(\vdash\colon\ldotp \alpha\in 1.\supset:\beta\text{ sm }\alpha.\equiv.\beta\in 1\) -/
theorem pm73_44 {A : Set α} {B : Set β} : A ∈ one → (sm B A ↔ B ∈ one) := by
  rintro ⟨a, rfl⟩
  constructor
  · rintro ⟨R, ⟨hR, rfl⟩, hA⟩
    obtain ⟨b, hb⟩ : a ∈ codom R := hA ▸ (rfl : a = a)
    refine mem_one_iff.2 ⟨b, fun z => ⟨fun ⟨w, hw⟩ => ?_, fun e => e ▸ ⟨a, hb⟩⟩⟩
    have hw' : w ∈ ι a := hA ▸ ⟨z, hw⟩
    rw [mem_unitCls] at hw'
    subst hw'
    exact mem_arrow_one_Cls.1 (oo_iff'.1 hR).1 z b w ⟨hw, hb⟩
  · rintro ⟨b, rfl⟩
    exact pm73_43.1

/-- ✱73·45. \(\vdash.1=\hat{\beta}(\beta\text{ sm }\iotaʻx)\) -/
theorem pm73_45 {x : α} : (one : Set (Set β)) = {B | sm B (ι x)} := by
  ext B
  exact (pm73_44 ⟨x, rfl⟩).symm

/-- ✱73·46. \(\vdash.\Lambda\text{ sm }\Lambda \quad[\text{*72·1.*33·29.*73·2}]\) -/
theorem pm73_46 : sm (Λ : Set α) (Λ : Set β) := by
  refine ⟨fun _ _ => False, ⟨mem_arrow_one_one.2 ⟨fun _ _ _ h => h.1.elim,
    fun _ _ _ h => h.1.elim⟩, ?_⟩, ?_⟩
  · ext x; simp [Null_eq_empty, dom]
  · ext x; simp [Null_eq_empty, codom]

/-- ✱73·47. \(\vdash:\beta\text{ sm }\Lambda.\equiv.\beta=\Lambda\) -/
theorem pm73_47 {B : Set β} : sm B (Λ : Set α) ↔ B = Λ := by
  constructor
  · rintro ⟨R, ⟨_, rfl⟩, h⟩
    rw [Null_eq_empty]
    refine Set.eq_empty_of_forall_notMem fun x ⟨y, hy⟩ => ?_
    have : y ∈ (Λ : Set α) := h ▸ ⟨x, hy⟩
    rw [Null_eq_empty] at this
    exact this
  · rintro rfl
    exact pm73_46

/-- ✱73·48. \(\vdash.0=\hat{\beta}(\beta\text{ sm }\Lambda) \quad[\text{*73·46.*51·11.(*54·01)}]\) -/
theorem pm73_48 : (zero : Set (Set β)) = {B | sm B (Λ : Set α)} := by
  ext B
  exact pm73_47.symm

/-- ✱73·5. \(\vdash:R\in 1\rightarrow 1.\equiv.R_{\in}\upharpoonright \text{Cl}ʻ\text{ᗡ}ʻR\unicode{x2abd}\text{ sm }\) -/
theorem pm73_5 {R : α → β → Prop} : R ∈ arrow one one ↔ imgRel R ↾ cl (codom R) ⪽ sm := by
  constructor
  · rintro hR A B ⟨hA, hB⟩
    have hA : A = R ʻʻ B := hA
    rw [hA]
    exact (pm73_22 ⟨hR, hB⟩).1
  · intro h
    have H : ∀ B, B ⊆ codom R → sm (R ʻʻ B) B := fun B hB => h _ _ ⟨rfl, hB⟩
    have h1 : R ∈ arrow one Cls := by
      refine mem_arrow_one_Cls.2 fun x y z ⟨hx, hy⟩ => ?_
      have hz : ι z ⊆ codom R := fun w hw => by rw [mem_unitCls.1 hw]; exact ⟨x, hx⟩
      have h1 := (pm73_44 ⟨z, rfl⟩).1 (H _ hz)
      obtain ⟨b, hb⟩ := mem_one_iff.1 h1
      have hxb := (hb x).1 ⟨z, rfl, hx⟩
      have hyb := (hb y).1 ⟨z, rfl, hy⟩
      exact hxb.trans hyb.symm
    refine oo_iff'.2 ⟨h1, mem_arrow_Cls_one.2 fun x y z ⟨hy, hz⟩ => ?_⟩
    have hsub : rels R x ⊆ codom R := fun w hw => ⟨x, hw⟩
    have himg : R ʻʻ rels R x = ι x := by
      ext u
      constructor
      · rintro ⟨w, hw, hu⟩; exact mem_arrow_one_Cls.1 h1 u x w ⟨hu, hw⟩
      · intro hu; rw [mem_unitCls.1 hu]; exact ⟨y, hy, hy⟩
    have h2 := H _ hsub
    rw [himg] at h2
    obtain ⟨b, hb⟩ := mem_one_iff.1 ((pm73_44 ⟨x, rfl⟩).1 (pm73_31.1 h2))
    exact ((hb y).1 hy).trans ((hb z).1 hz).symm

/-- ✱73·501. \(\vdash:R\in 1\rightarrow 1.\equiv.(\breve{R})_{\in}\upharpoonright \text{Cl}ʻ\text{D}ʻR\unicode{x2abd}\text{ sm }\) -/
theorem pm73_501 {R : α → β → Prop} : R ∈ arrow one one ↔ imgRel R˘ ↾ cl (dom R) ⪽ sm := by
  rw [← cnv_oo]
  exact pm73_5

/-- ✱73·51. \(\vdash:R\in 1\rightarrow \text{Cls}.\alpha\subset \text{D}ʻR.\supset.\overleftarrow{R}ʻʻ\alpha\text{ sm }\alpha\) -/
theorem pm73_51 {A : Set α} {R : α → β → Prop} :
    R ∈ arrow one Cls ∧ A ⊆ dom R → sm (Rbwd R ʻʻ A) A := by
  rintro ⟨hR, hA⟩
  refine pm73_25 ⟨fun y => EDesc_graph _ y, fun y z ⟨⟨hy, hz⟩, he⟩ => ?_⟩
  have e : rels R y = rels R z := (descEq_graph (rels R) y z).1 he
  obtain ⟨w, hw⟩ := hA hy
  have : w ∈ rels R z := e ▸ hw
  exact mem_arrow_one_Cls.1 hR y z w ⟨hw, this⟩

/-- ✱73·511. \[\begin{align}&\vdash:R\in \text{Cls}\rightarrow 1.\alpha\subset \text{ᗡ}ʻR.\supset.\overrightarrow{R}ʻʻ\alpha\text{ sm }\alpha\\ &\left[\text{*73·51} \frac{\breve{R}}{R}.\text{*71·211.*33·2.*32·241}\right]\end{align}\]

The erratum to ✱73·511 (Additional Errata to Vol. I, p. 485: `α` for `β`) is already incorporated in the e-text. -/
theorem pm73_511 {A : Set β} {R : α → β → Prop} :
    R ∈ arrow Cls one ∧ A ⊆ codom R → sm (Rfwd R ʻʻ A) A :=
  fun ⟨hR, hA⟩ => pm73_51 (R := R˘) ⟨cnv_oc.2 hR, hA⟩

private theorem graph_oc (f : β → α) : graph f ∈ arrow one Cls :=
  mem_arrow_one_Cls.2 fun _ _ _ ⟨h1, h2⟩ => h1.trans h2.symm

private theorem graph_codom (f : β → α) (B : Set β) : B ⊆ codom (graph f) :=
  fun y _ => ⟨f y, rfl⟩

/-- General form of ✱74·13. -/
private theorem imgRel_cnv_oo {R : α → β → Prop} (hR : R ∈ arrow one Cls) :
    imgRel R˘ ↾ cl (dom R) ∈ arrow one one := by
  refine mem_arrow_one_one.2 ⟨fun X Y Z ⟨h1, h2⟩ => h1.1.trans h2.1.symm,
    fun X Y Z ⟨⟨h1, hY⟩, ⟨h2, hZ⟩⟩ => ?_⟩
  have e : R˘ ʻʻ Y = R˘ ʻʻ Z := (h1 : X = R˘ ʻʻ Y).symm.trans h2
  rw [← img_img_cnv hR hY, ← img_img_cnv hR hZ, e]

/-- General form of ✱74·131. -/
private theorem imgRel_oo {R : α → β → Prop} (hR : R ∈ arrow Cls one) :
    imgRel R ↾ cl (codom R) ∈ arrow one one :=
  imgRel_cnv_oo (R := R˘) (cnv_oc.2 hR)

/-- ✱73·52. \(\vdash:R\in 1\rightarrow \text{Cls}.\alpha\subset \text{Cls}ʻ\text{D}ʻR.\supset.(\breve{R})_{\in}ʻʻ\alpha\text{ sm }\alpha\)

**Status.** proved (reading): transcription error: the e-text prints `Cls'D'R` (meaningless, since `Cls` is not a relation) for `Cl'D'R`, as the demonstration (`(R̆)_∈ ↾ Cl'D'R ∈ 1 → 1`), ✱73·521 and ✱73·53 show. -/
theorem pm73_52 {A : Set (Set α)} {R : α → β → Prop} :
    R ∈ arrow one Cls ∧ A ⊆ cl (dom R) → sm (imgRel R˘ ʻʻ A) A := by
  rintro ⟨hR, hA⟩
  have h := imgRel_cnv_oo hR
  exact (pm73_23 ⟨⟨graph_oc _, graph_codom _ _⟩,
    co_mono (oo_iff'.1 h).2 fun X Y hXY => ⟨hXY.1, hA hXY.2⟩⟩).1

/-- ✱73·521. \(\vdash:R\in \text{Cls}\rightarrow 1.\beta\subset \text{Cl}ʻ\text{ᗡ}ʻR.\supset.R_{\in}ʻʻ\beta\text{ sm }\beta \quad[\text{Proof as in *73·52}]\) -/
theorem pm73_521 {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow Cls one ∧ B ⊆ cl (codom R) → sm (imgRel R ʻʻ B) B :=
  fun ⟨hR, hB⟩ => pm73_52 (R := R˘) ⟨cnv_oc.2 hR, hB⟩

/-- ✱73·53. \(\vdash:R\in 1\rightarrow \text{Cls}.\alpha\subset \text{Cl}ʻ\text{D}ʻR.\supset.\breve{R}ʻʻʻ\alpha\text{ sm }\alpha \quad[\text{*73·52.(*37·04)}]\) -/
theorem pm73_53 {A : Set (Set α)} {R : α → β → Prop} :
    R ∈ arrow one Cls ∧ A ⊆ cl (dom R) → sm (R˘ ʻʻʻ A) A := pm73_52

/-- ✱73·531. \(\vdash:R\in \text{Cls}\rightarrow 1.\beta\subset \text{Cl}ʻ\text{ᗡ}ʻR.\supset.Rʻʻʻ\beta\text{ sm }\beta \quad[\text{*73·521.(*37·04)}]\) -/
theorem pm73_531 {B : Set (Set β)} {R : α → β → Prop} :
    R ∈ arrow Cls one ∧ B ⊆ cl (codom R) → sm (R ʻʻʻ B) B := pm73_521

/-- ✱73·61. \(\vdash.x\downarrow ʻʻ\alpha\text{ sm }\alpha.(x\downarrow )\upharpoonright \alpha\in (x\downarrow ʻʻ\alpha)\overline{\text{ sm }}\alpha \quad[\text{*73·27.*55·2}]\) -/
theorem pm73_61 {x : α} {A : Set β} :
    sm (coupleL x ʻʻ A) A ∧ coupleL x ↾ A ∈ smbar (coupleL x ʻʻ A) A := by
  refine pm73_27 fun y z => (descEq_graph (couple x) y z).trans ⟨fun e => ?_, fun e => e ▸ rfl⟩
  have : (x ↓ z) x y := e ▸ (⟨rfl, rfl⟩ : (x ↓ y) x y)
  exact this.2

/-- ✱73·611. \(\vdash.\downarrow xʻʻ\alpha\text{ sm }\alpha.(\downarrow x)\upharpoonright \alpha\in (\downarrow xʻʻ\alpha)\overline{\text{ sm }}\alpha \quad[\text{*73·27.*55·201}]\) -/
theorem pm73_611 {x : β} {A : Set α} :
    sm (coupleR x ʻʻ A) A ∧ coupleR x ↾ A ∈ smbar (coupleR x ʻʻ A) A := by
  refine pm73_27 fun y z =>
    (descEq_graph (fun w => w ↓ x) y z).trans ⟨fun e => ?_, fun e => e ▸ rfl⟩
  have : (z ↓ x) y x := (show (y ↓ x) = (z ↓ x) from e) ▸ (⟨rfl, rfl⟩ : (y ↓ x) y x)
  exact this.1

private theorem codom_couple (x : α) (y : β) : codom (x ↓ y) = ι y := by
  ext b; exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨x, rfl, h⟩⟩

private theorem dom_couple (x : α) (y : β) : dom (x ↓ y) = ι x := by
  ext a; exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨y, h, rfl⟩⟩

/-- ✱73·62. \(\vdash:\lambda\subset \text{D}ʻx\downarrow .\supset.\text{ᗡ}ʻʻ\lambda\text{ sm }\lambda.\text{ᗡ}\upharpoonright \lambda\in (\text{ᗡ}ʻʻ\lambda)\overline{\text{ sm }}\lambda \quad[\text{*73·23.*72·131·8}]\) -/
theorem pm73_62 {x : α} {L : Set (α → β → Prop)} :
    L ⊆ dom (coupleL x) → sm (Dcnv ʻʻ L) L ∧ Dcnv ↾ L ∈ smbar (Dcnv ʻʻ L) L := by
  intro hL
  refine pm73_28 fun P Q ⟨hP, hQ⟩ => (descEq_graph codom P Q).trans ⟨fun e => ?_, fun e => e ▸ rfl⟩
  obtain ⟨y, rfl⟩ := hL hP
  obtain ⟨z, rfl⟩ := hL hQ
  rw [codom_couple, codom_couple] at e
  rw [unitCls_injective e]

/-- ✱73·621. \(\vdash:\lambda\subset \text{D}ʻ\downarrow x.\supset.\text{D}ʻʻ\lambda\text{ sm }\lambda.\text{D}\upharpoonright \lambda\in (\text{D}ʻʻ\lambda)\overline{\text{ sm }}\lambda \quad[\text{*73·23.*72·13·81}]\) -/
theorem pm73_621 {x : β} {L : Set (α → β → Prop)} :
    L ⊆ dom (coupleR x) → sm (D ʻʻ L) L ∧ D ↾ L ∈ smbar (D ʻʻ L) L := by
  intro hL
  refine pm73_28 fun P Q ⟨hP, hQ⟩ => (descEq_graph dom P Q).trans ⟨fun e => ?_, fun e => e ▸ rfl⟩
  obtain ⟨y, rfl⟩ := hL hP
  obtain ⟨z, rfl⟩ := hL hQ
  rw [dom_couple, dom_couple] at e
  rw [unitCls_injective e]

/-- ✱73·63. \(\vdash:S\in \alpha\overline{\text{ sm }}\beta.T\upharpoonright \alpha,T\upharpoonright \beta\in 1\rightarrow 1.\alpha\cup \beta\subset \text{ᗡ}ʻT.\supset.T\mid S\mid \breve{T}\in (Tʻʻ\alpha)\overline{\text{ sm }}(Tʻʻ\beta)\) -/
theorem pm73_63 {A B : Set β} {S : β → β → Prop} {T : α → β → Prop} :
    (S ∈ smbar A B ∧ (T ↾ A ∈ arrow one one ∧ T ↾ B ∈ arrow one one)) ∧ A ∪ B ⊆ codom T →
      T ⨾ S ⨾ T˘ ∈ smbar (T ʻʻ A) (T ʻʻ B) := by
  rintro ⟨⟨⟨⟨hS, hA⟩, hB⟩, hTA, hTB⟩, hU⟩
  obtain ⟨S1, S2⟩ := mem_arrow_one_one.1 hS
  obtain ⟨A1, A2⟩ := mem_arrow_one_one.1 hTA
  obtain ⟨B1, B2⟩ := mem_arrow_one_one.1 hTB
  have hyA : ∀ y z, S y z → y ∈ A := fun y z h => hA ▸ ⟨z, h⟩
  have hzB : ∀ y z, S y z → z ∈ B := fun y z h => hB ▸ ⟨y, h⟩
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x x' w ⟨⟨z1, ⟨y1, h1, h2⟩, h3⟩, ⟨z2, ⟨y2, h4, h5⟩, h6⟩⟩
    have ez := B2 w z1 z2 ⟨⟨h3, hzB _ _ h2⟩, ⟨h6, hzB _ _ h5⟩⟩
    subst ez
    have ey := S1 y1 y2 z1 ⟨h2, h5⟩
    subst ey
    exact A1 x x' y1 ⟨⟨h1, hyA _ _ h2⟩, ⟨h4, hyA _ _ h2⟩⟩
  · rintro x w w' ⟨⟨z1, ⟨y1, h1, h2⟩, h3⟩, ⟨z2, ⟨y2, h4, h5⟩, h6⟩⟩
    have ey := A2 x y1 y2 ⟨⟨h1, hyA _ _ h2⟩, ⟨h4, hyA _ _ h5⟩⟩
    subst ey
    have ez := S2 y1 z1 z2 ⟨h2, h5⟩
    subst ez
    exact B1 w w' z1 ⟨⟨h3, hzB _ _ h2⟩, ⟨h6, hzB _ _ h2⟩⟩
  · ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hy' : y ∈ dom S := hA ▸ hy
      obtain ⟨z, hz⟩ := hy'
      obtain ⟨w, hw⟩ := hU (Or.inr (hzB _ _ hz))
      exact ⟨w, z, ⟨y, hxy, hz⟩, hw⟩
    · rintro ⟨w, z, ⟨y, h1, h2⟩, -⟩
      exact ⟨y, hyA _ _ h2, h1⟩
  · ext w
    constructor
    · rintro ⟨z, hz, hwz⟩
      have hz' : z ∈ codom S := hB ▸ hz
      obtain ⟨y, hy⟩ := hz'
      obtain ⟨x, hx⟩ := hU (Or.inl (hyA _ _ hy))
      exact ⟨x, z, ⟨y, hx, hy⟩, hwz⟩
    · rintro ⟨x, z, ⟨y, -, h2⟩, h3⟩
      exact ⟨z, hzB _ _ h2, h3⟩

private theorem rcup_smbar {A G : Set α} {B H : Set β} {R S : α → β → Prop} :
    ((R ∈ smbar A B ∧ S ∈ smbar G H) ∧ A ∩ G = Λ) ∧ B ∩ H = Λ →
      R ⊍ S ∈ smbar (A ∪ G) (B ∪ H) := by
  rintro ⟨⟨⟨⟨⟨hR, rfl⟩, rfl⟩, ⟨⟨hS, rfl⟩, rfl⟩⟩, hd1⟩, hd2⟩
  obtain ⟨R1, R2⟩ := mem_arrow_one_one.1 hR
  obtain ⟨S1, S2⟩ := mem_arrow_one_one.1 hS
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨h1 | h1, h2 | h2⟩
    · exact R1 x y z ⟨h1, h2⟩
    · exact (disj hd2 ⟨x, h1⟩ ⟨y, h2⟩).elim
    · exact (disj hd2 ⟨y, h2⟩ ⟨x, h1⟩).elim
    · exact S1 x y z ⟨h1, h2⟩
  · rintro x y z ⟨h1 | h1, h2 | h2⟩
    · exact R2 x y z ⟨h1, h2⟩
    · exact (disj hd1 ⟨y, h1⟩ ⟨z, h2⟩).elim
    · exact (disj hd1 ⟨z, h2⟩ ⟨y, h1⟩).elim
    · exact S2 x y z ⟨h1, h2⟩
  · ext x
    constructor
    · rintro (⟨y, h⟩ | ⟨y, h⟩)
      · exact ⟨y, Or.inl h⟩
      · exact ⟨y, Or.inr h⟩
    · rintro ⟨y, h | h⟩
      · exact Or.inl ⟨y, h⟩
      · exact Or.inr ⟨y, h⟩
  · ext y
    constructor
    · rintro (⟨x, h⟩ | ⟨x, h⟩)
      · exact ⟨x, Or.inl h⟩
      · exact ⟨x, Or.inr h⟩
    · rintro ⟨x, h | h⟩
      · exact Or.inl ⟨x, h⟩
      · exact Or.inr ⟨x, h⟩

/-- ✱73·69. \(\vdash:R\in \alpha\overline{\text{ sm }}\beta.\alpha\cap \gamma=\Lambda.\beta\cap \gamma=\Lambda.\supset.R\unicode{x228d}I\upharpoonright \gamma\in (\alpha\cup \gamma)\overline{\text{ sm }}(\beta\cup \gamma)\) -/
theorem pm73_69 {A B G : Set α} {R : α → α → Prop} :
    (R ∈ smbar A B ∧ A ∩ G = Λ) ∧ B ∩ G = Λ → R ⊍ I ↾ G ∈ smbar (A ∪ G) (B ∪ G) :=
  fun ⟨⟨hR, h1⟩, h2⟩ => rcup_smbar ⟨⟨⟨hR, pm73_3.2⟩, h1⟩, h2⟩

/-- ✱73·7. \(\vdash:\alpha\text{ sm }\beta.\alpha\cap \gamma=\Lambda.\beta\cap \gamma=\Lambda.\supset.(\alpha\cup \gamma)\text{ sm }(\beta\cup \gamma) \quad[\text{*73·69·04}]\) -/
theorem pm73_7 {A B G : Set α} :
    (sm A B ∧ A ∩ G = Λ) ∧ B ∩ G = Λ → sm (A ∪ G) (B ∪ G) :=
  fun ⟨⟨⟨_, hR⟩, h1⟩, h2⟩ => sm_of_mem (pm73_69 ⟨⟨hR, h1⟩, h2⟩)

/-- ✱73·701. \(\vdash:R\in \alpha\overline{\text{ sm }}\beta.S\in \gamma\overline{\text{ sm }}\delta.\alpha\cap \gamma=\Lambda.\beta\cap \delta=\Lambda.\supset.R\unicode{x228d}S\in (\alpha\cup \gamma)\overline{\text{ sm }}(\beta\cup \delta)\) -/
theorem pm73_701 {A G : Set α} {B H : Set β} {R S : α → β → Prop} :
    ((R ∈ smbar A B ∧ S ∈ smbar G H) ∧ A ∩ G = Λ) ∧ B ∩ H = Λ →
      R ⊍ S ∈ smbar (A ∪ G) (B ∪ H) := rcup_smbar

/-- ✱73·71. \(\vdash:\alpha\text{ sm }\beta.\gamma\text{ sm }\delta.\alpha\cap \gamma=\Lambda.\beta\cap \delta=\Lambda.\supset.(\alpha\cup \gamma)\text{ sm }(\beta\cup \delta) \quad[\text{*73·701·04}]\) -/
theorem pm73_71 {A G : Set α} {B H : Set β} :
    ((sm A B ∧ sm G H) ∧ A ∩ G = Λ) ∧ B ∩ H = Λ → sm (A ∪ G) (B ∪ H) :=
  fun ⟨⟨⟨⟨_, hR⟩, ⟨_, hS⟩⟩, h1⟩, h2⟩ => sm_of_mem (pm73_701 ⟨⟨⟨hR, hS⟩, h1⟩, h2⟩)

/-- ✱73·72. \(\vdash:\alpha\cup \iotaʻx \text{ sm }\beta\cup \iotaʻy.x{\sim}\in \alpha.y{\sim}\in \beta.\supset.\alpha\text{ sm }\beta\) -/
theorem pm73_72 {A : Set α} {B : Set β} {x : α} {y : β} :
    (sm (A ∪ ι x) (B ∪ ι y) ∧ x ∉ A) ∧ y ∉ B → sm A B := by
  rintro ⟨⟨⟨R, ⟨hR, hdom⟩, hcod⟩, hx⟩, hy⟩
  obtain ⟨R1, R2⟩ := mem_arrow_one_one.1 hR
  have hd : ∀ a, a ∈ A ∪ ι x → ∃ b, R a b := fun a ha => by rw [hdom] at ha; exact ha
  have hc : ∀ b, b ∈ B ∪ ι y → ∃ a, R a b := fun b hb => by rw [hcod] at hb; exact hb
  have hd' : ∀ a b, R a b → a ∈ A ∨ a = x := fun a b h => by
    have h' : a ∈ dom R := ⟨b, h⟩
    rw [← hdom] at h'; exact h'
  have hc' : ∀ a b, R a b → b ∈ B ∨ b = y := fun a b h => by
    have h' : b ∈ codom R := ⟨a, h⟩
    rw [← hcod] at h'; exact h'
  refine ⟨fun a b => (a ∈ A ∧ b ∈ B) ∧ (R a b ∨ (R a y ∧ R x b)),
    ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro a a' c ⟨⟨⟨ha, -⟩, h1 | ⟨h1, h1'⟩⟩, ⟨⟨ha', -⟩, h2 | ⟨h2, h2'⟩⟩⟩
    · exact R1 a a' c ⟨h1, h2⟩
    · exact (hx ((R1 a x c ⟨h1, h2'⟩) ▸ ha)).elim
    · exact (hx ((R1 a' x c ⟨h2, h1'⟩) ▸ ha')).elim
    · exact R1 a a' y ⟨h1, h2⟩
  · rintro a b c ⟨⟨⟨-, hb⟩, h1 | ⟨h1, h1'⟩⟩, ⟨⟨-, hc⟩, h2 | ⟨h2, h2'⟩⟩⟩
    · exact R2 a b c ⟨h1, h2⟩
    · exact (hy ((R2 a b y ⟨h1, h2⟩) ▸ hb)).elim
    · exact (hy ((R2 a c y ⟨h2, h1⟩) ▸ hc)).elim
    · exact R2 x b c ⟨h1', h2'⟩
  · ext a
    constructor
    · intro ha
      obtain ⟨b, hab⟩ := hd a (Or.inl ha)
      rcases hc' a b hab with hb | hb
      · exact ⟨b, ⟨ha, hb⟩, Or.inl hab⟩
      · rw [hb] at hab
        obtain ⟨c, hxc⟩ := hd x (Or.inr rfl)
        rcases hc' x c hxc with hc | hc
        · exact ⟨c, ⟨ha, hc⟩, Or.inr ⟨hab, hxc⟩⟩
        · rw [hc] at hxc
          exact (hx ((R1 a x y ⟨hab, hxc⟩) ▸ ha)).elim
    · rintro ⟨b, ⟨ha, -⟩, -⟩; exact ha
  · ext b
    constructor
    · intro hb
      obtain ⟨a, hab⟩ := hc b (Or.inl hb)
      rcases hd' a b hab with ha | ha
      · exact ⟨a, ⟨ha, hb⟩, Or.inl hab⟩
      · rw [ha] at hab
        obtain ⟨c, hcy⟩ := hc y (Or.inr rfl)
        rcases hd' c y hcy with hc | hc
        · exact ⟨c, ⟨hc, hb⟩, Or.inr ⟨hcy, hab⟩⟩
        · rw [hc] at hcy
          exact (hy ((R2 x b y ⟨hab, hcy⟩) ▸ hb)).elim
    · rintro ⟨a, ⟨-, hb⟩, -⟩; exact hb

/-- ✱73·8. \[\begin{align}\vdash:(\text{ᗡ}ʻR\subset \beta.\beta\subset \text{D}ʻR.\kappa = \hat{\alpha}(\alpha\subset \text{D}ʻR.\beta-\text{ᗡ}ʻR&\subset \alpha.\breve{R}ʻʻ\alpha\subset \alpha).\supset.\\ &\text{D}ʻR\in \kappa.pʻ\kappa \subset \text{D}ʻR\end{align}\]

"Hp✱73·8" in ✱73·801–✱73·841 is this hypothesis, written out. -/
theorem pm73_8 {R : α → α → Prop} {B : Set α} {K : Set (Set α)} :
    (codom R ⊆ B ∧ B ⊆ dom R) ∧ K = {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A} →
      dom R ∈ K ∧ prodCls K ⊆ dom R := by
  rintro ⟨⟨h1, h2⟩, rfl⟩
  have hD : dom R ∈ {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A} :=
    ⟨⟨le_rfl, fun x hx => h2 hx.1⟩, fun x ⟨y, _, hyx⟩ => h2 (h1 ⟨y, hyx⟩)⟩
  exact ⟨hD, fun x hx => hx _ hD⟩

/-- ✱73·801. \(\vdash: \text{Hp} *73·8 . \supset . \beta - \text{ᗡ}ʻR pʻ\kappa\)

**Status.** proved (reading): transcription error: the e-text drops the sign `⊂` of `β − ᗡ'R ⊂ p'κ`, as the demonstration and the use of ✱73·801 in ✱73·81 show. -/
theorem pm73_801 {R : α → α → Prop} {B : Set α} {K : Set (Set α)} :
    (codom R ⊆ B ∧ B ⊆ dom R) ∧ K = {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A} →
      B \ codom R ⊆ prodCls K := by
  rintro ⟨-, rfl⟩ x hx A hA
  exact hA.1.2 hx

/-- ✱73·802. \(\vdash: \text{Hp*73·8} .\supset .\breve{R}ʻʻpʻ\kappa \subset pʻ\kappa\) -/
theorem pm73_802 {R : α → α → Prop} {B : Set α} {K : Set (Set α)} :
    (codom R ⊆ B ∧ B ⊆ dom R) ∧ K = {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A} →
      R˘ ʻʻ prodCls K ⊆ prodCls K := by
  rintro ⟨-, rfl⟩ x ⟨y, hy, hyx⟩ A hA
  exact hA.2 ⟨y, hy A hA, hyx⟩

/-- ✱73·81. \(\vdash: \text{Hp*73·8} .\supset.pʻ\kappa\in \kappa\) -/
theorem pm73_81 {R : α → α → Prop} {B : Set α} {K : Set (Set α)} :
    (codom R ⊆ B ∧ B ⊆ dom R) ∧ K = {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A} →
      prodCls K ∈ K := by
  intro h
  have h8 := (pm73_8 h).2
  have h801 := pm73_801 h
  have h802 := pm73_802 h
  obtain ⟨-, rfl⟩ := h
  exact ⟨⟨h8, h801⟩, h802⟩

/-- ✱73·811. \(\vdash : \text{Hp*73·8} . \supset . \breve{R}ʻʻpʻ\kappa \subset pʻ\kappa - (\beta -\text{ᗡ}ʻR)\) -/
theorem pm73_811 {R : α → α → Prop} {B : Set α} {K : Set (Set α)} :
    (codom R ⊆ B ∧ B ⊆ dom R) ∧ K = {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A} →
      R˘ ʻʻ prodCls K ⊆ prodCls K \ (B \ codom R) := by
  intro h x hx
  obtain ⟨y, hy, hyx⟩ := hx
  exact ⟨pm73_802 h ⟨y, hy, hyx⟩, fun hB => hB.2 ⟨y, hyx⟩⟩

/-- ✱73·812. \(\vdash:\text{Hp}*73·8.x{\sim}\in (\beta-\text{ᗡ}ʻR)\cup \breve{R}ʻʻpʻ\kappa.\supset.\breve{R}ʻʻ(pʻ\kappa-\iotaʻx)\subset pʻ\kappa-\iotaʻx\) -/
theorem pm73_812 {R : α → α → Prop} {B : Set α} {K : Set (Set α)} {x : α} :
    ((codom R ⊆ B ∧ B ⊆ dom R) ∧ K = {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A}) ∧
        x ∉ (B \ codom R) ∪ R˘ ʻʻ prodCls K →
      R˘ ʻʻ (prodCls K \ ι x) ⊆ prodCls K \ ι x := by
  rintro ⟨h, hx⟩ z ⟨w, hw, hwz⟩
  have hz : z ∈ R˘ ʻʻ prodCls K := ⟨w, hw.1, hwz⟩
  refine ⟨pm73_802 h hz, fun e => hx (Or.inr ?_)⟩
  rw [mem_unitCls.1 e] at hz
  exact hz

/-- ✱73·82. \(\vdash:\text{Hp}*73·812.\supset.pʻ\kappa-\iotaʻx=pʻ\kappa.x{\sim}\in pʻ\kappa\) -/
theorem pm73_82 {R : α → α → Prop} {B : Set α} {K : Set (Set α)} {x : α} :
    ((codom R ⊆ B ∧ B ⊆ dom R) ∧ K = {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A}) ∧
        x ∉ (B \ codom R) ∪ R˘ ʻʻ prodCls K →
      prodCls K \ ι x = prodCls K ∧ x ∉ prodCls K := by
  intro hh
  have h812 := pm73_812 hh
  obtain ⟨h, hx⟩ := hh
  have h8 := (pm73_8 h).2
  have h801 := pm73_801 h
  obtain ⟨-, rfl⟩ := h
  have hmem : prodCls {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A} \ ι x ∈
      {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A} := by
    refine ⟨⟨fun z hz => h8 hz.1, fun z hz => ⟨h801 hz, fun e => ?_⟩⟩, h812⟩
    rw [mem_unitCls.1 e] at hz
    exact hx (Or.inl hz)
  have hsub : ∀ z, z ∈ prodCls _ → z ∈ _ := fun z hz => hz _ hmem
  exact ⟨Set.Subset.antisymm Set.sdiff_subset hsub, fun hxK => (hsub x hxK).2 rfl⟩

/-- ✱73·821. \(\vdash:\text{Hp}*73·8.x\in pʻ\kappa-(\beta-\text{ᗡ}ʻR).\supset.x\in \breve{R}ʻʻpʻ\kappa\) -/
theorem pm73_821 {R : α → α → Prop} {B : Set α} {K : Set (Set α)} {x : α} :
    ((codom R ⊆ B ∧ B ⊆ dom R) ∧ K = {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A}) ∧
        x ∈ prodCls K \ (B \ codom R) →
      x ∈ R˘ ʻʻ prodCls K := by
  rintro ⟨h, hx1, hx2⟩
  by_contra hc
  exact (pm73_82 (x := x) ⟨h, fun hu => hu.elim hx2 hc⟩).2 hx1

/-- ✱73·83. \(\vdash:\text{Hp}*73·8.\supset.pʻ\kappa-(\beta-\text{ᗡ}ʻR)=\breve{R}ʻʻpʻ\kappa.pʻ\kappa=(\beta-\text{ᗡ}ʻR)\cup \breve{R}ʻʻpʻ\kappa\) -/
theorem pm73_83 {R : α → α → Prop} {B : Set α} {K : Set (Set α)} :
    (codom R ⊆ B ∧ B ⊆ dom R) ∧ K = {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A} →
      prodCls K \ (B \ codom R) = R˘ ʻʻ prodCls K ∧
        prodCls K = (B \ codom R) ∪ R˘ ʻʻ prodCls K := by
  intro h
  refine ⟨Set.Subset.antisymm (fun x hx => pm73_821 ⟨h, hx⟩) (pm73_811 h), ?_⟩
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.union_subset (pm73_801 h) (pm73_802 h))
  by_cases hB : x ∈ B \ codom R
  · exact Or.inl hB
  · exact Or.inr (pm73_821 ⟨h, hx, hB⟩)

/-- ✱73·84. \(\vdash:\text{Hp*73·8}.\supset.\beta=pʻ\kappa\cup (\text{ᗡ}ʻR-\breve{R}ʻʻpʻ\kappa)\) -/
theorem pm73_84 {R : α → α → Prop} {B : Set α} {K : Set (Set α)} :
    (codom R ⊆ B ∧ B ⊆ dom R) ∧ K = {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A} →
      B = prodCls K ∪ (codom R \ R˘ ʻʻ prodCls K) := by
  intro h
  have h83 := (pm73_83 h).2
  have h1 := h.1.1
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.union_subset ?_ (fun x hx => h1 hx.1))
  · by_cases hc : x ∈ codom R
    · by_cases hp : x ∈ R˘ ʻʻ prodCls K
      · exact Or.inl (pm73_802 h hp)
      · exact Or.inr ⟨hc, hp⟩
    · exact Or.inl (pm73_801 h ⟨hx, hc⟩)
  · rw [h83]
    exact Set.union_subset Set.sdiff_subset fun x ⟨y, _, hyx⟩ => h1 ⟨y, hyx⟩

/-- ✱73·841. \(\vdash:\text{Hp*73·8}.R\in 1\rightarrow 1.\supset.\beta\text{ sm }\text{ᗡ}ʻR.\beta\text{ sm }\text{D}ʻR\) -/
theorem pm73_841 {R : α → α → Prop} {B : Set α} {K : Set (Set α)} :
    ((codom R ⊆ B ∧ B ⊆ dom R) ∧ K = {A | (A ⊆ dom R ∧ B \ codom R ⊆ A) ∧ R˘ ʻʻ A ⊆ A}) ∧
        R ∈ arrow one one →
      sm B (codom R) ∧ sm B (dom R) := by
  rintro ⟨h, hR⟩
  have hPD : (prodCls K) ⊆ dom R := (pm73_8 h).2
  have s1 : sm (prodCls K) (R˘ ʻʻ (prodCls K)) := (pm73_21 ⟨hR, hPD⟩).1
  have s2 : sm (codom R \ R˘ ʻʻ (prodCls K)) (codom R \ R˘ ʻʻ (prodCls K)) := pm73_3.1
  have d1 : (prodCls K) ∩ (codom R \ R˘ ʻʻ (prodCls K)) = Λ := by
    refine disj_iff.2 fun x hx hx' => ?_
    rw [(pm73_83 h).2] at hx
    rcases hx with hx | hx
    · exact hx.2 hx'.1
    · exact hx'.2 hx
  have d2 : R˘ ʻʻ (prodCls K) ∩ (codom R \ R˘ ʻʻ (prodCls K)) = Λ := disj_iff.2 fun x hx hx' => hx'.2 hx
  have s3 := pm73_71 ⟨⟨⟨s1, s2⟩, d1⟩, d2⟩
  rw [← pm73_84 h] at s3
  have e : R˘ ʻʻ (prodCls K) ∪ (codom R \ R˘ ʻʻ (prodCls K)) = codom R := by
    refine Set.Subset.antisymm (Set.union_subset (fun x ⟨y, _, hyx⟩ => ⟨y, hyx⟩)
      Set.sdiff_subset) (fun x hx => ?_)
    by_cases hp : x ∈ R˘ ʻʻ (prodCls K)
    · exact Or.inl hp
    · exact Or.inr ⟨hx, hp⟩
  rw [e] at s3
  exact ⟨s3, pm73_32 ⟨s3, (pm73_2 hR).2⟩⟩

/-- ✱73·85. \(\vdash:R\in 1\rightarrow 1.\text{ᗡ}ʻR\subset \beta.\beta\subset \text{D}ʻR.\supset.\beta\text{ sm }\text{ᗡ}ʻR.\beta\text{ sm }\text{D}ʻR \quad[\text{*73·841}]\) -/
theorem pm73_85 {R : α → α → Prop} {B : Set α} :
    (R ∈ arrow one one ∧ codom R ⊆ B) ∧ B ⊆ dom R → sm B (codom R) ∧ sm B (dom R) :=
  fun ⟨⟨hR, h1⟩, h2⟩ => pm73_841 ⟨⟨⟨h1, h2⟩, rfl⟩, hR⟩

/-- ✱73·86. \[\begin{align}\vdash:\text{ᗡ}ʻR\subset \text{D}ʻS.\text{ᗡ}ʻS&\subset \text{D}ʻR.\supset.\\ &\text{D}ʻ(R\mid S)=\text{D}ʻR.\text{ᗡ}ʻ(R\mid S)\subset \text{ᗡ}ʻS.\text{ᗡ}ʻS\subset \text{D}ʻ(R\mid S)\end{align}\] -/
theorem pm73_86 {R : α → β → Prop} {S : β → α → Prop} :
    codom R ⊆ dom S ∧ codom S ⊆ dom R →
      (dom (R ⨾ S) = dom R ∧ codom (R ⨾ S) ⊆ codom S) ∧ codom S ⊆ dom (R ⨾ S) := by
  rintro ⟨h1, h2⟩
  have e : dom (R ⨾ S) = dom R := by
    ext x
    constructor
    · rintro ⟨z, y, hxy, -⟩; exact ⟨y, hxy⟩
    · rintro ⟨y, hxy⟩
      obtain ⟨z, hz⟩ := h1 ⟨x, hxy⟩
      exact ⟨z, y, hxy, hz⟩
  refine ⟨⟨e, fun z ⟨x, y, _, hyz⟩ => ⟨y, hyz⟩⟩, ?_⟩
  rw [e]; exact h2

private theorem oo_comp {R : α → β → Prop} {S : β → γ → Prop} (hR : R ∈ arrow one one)
    (hS : S ∈ arrow one one) : R ⨾ S ∈ arrow one one := by
  obtain ⟨hR1, hR2⟩ := mem_arrow_one_one.1 hR
  obtain ⟨hS1, hS2⟩ := mem_arrow_one_one.1 hS
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro x y z ⟨⟨u, h1, h2⟩, ⟨v, h3, h4⟩⟩
    exact hR1 x y u ⟨h1, (hS1 u v z ⟨h2, h4⟩) ▸ h3⟩
  · rintro x y z ⟨⟨u, h1, h2⟩, ⟨v, h3, h4⟩⟩
    exact hS2 u y z ⟨h2, (hR2 x v u ⟨h3, h1⟩) ▸ h4⟩

/-- ✱73·87. \(\vdash:R,\,S\in 1\rightarrow 1.\text{ᗡ}ʻR\subset \text{D}ʻS.\text{ᗡ}ʻS\subset \text{D}ʻR.\supset.\text{D}ʻR\text{ sm }\text{D}ʻS\) -/
theorem pm73_87 {R : α → β → Prop} {S : β → α → Prop} :
    ((R ∈ arrow one one ∧ S ∈ arrow one one) ∧ codom R ⊆ dom S) ∧ codom S ⊆ dom R →
      sm (dom R) (dom S) := by
  rintro ⟨⟨⟨hR, hS⟩, h1⟩, h2⟩
  obtain ⟨⟨e, h3⟩, h4⟩ := pm73_86 ⟨h1, h2⟩
  have h5 := (pm73_85 ⟨⟨oo_comp hR hS, h3⟩, h4⟩).2
  rw [e] at h5
  exact pm73_31.1 (pm73_32 ⟨(pm73_2 hS).1, h5⟩)

/-- ✱73·88. \(\vdash:\alpha\text{ sm }\gamma.\beta\text{ sm }\delta.\gamma\subset \beta.\delta\subset \alpha.\supset.\alpha\text{ sm }\beta\) -/
theorem pm73_88 {A H : Set α} {B G : Set β} :
    ((sm A G ∧ sm B H) ∧ G ⊆ B) ∧ H ⊆ A → sm A B := by
  rintro ⟨⟨⟨⟨R, ⟨hR, rfl⟩, rfl⟩, ⟨S, ⟨hS, rfl⟩, rfl⟩⟩, h1⟩, h2⟩
  exact pm73_87 ⟨⟨⟨hR, hS⟩, h1⟩, h2⟩

/-!
## [✱74] On one-many and many-one relations with limited fields

*(Vol. 1, p. 490)*

> *Summary of* *74.
>
> The purpose of the present number is to collect together various propositions in which we have such hypotheses as \[ R \upharpoonright \lambda \in 1 \rightarrow \text{Cls}, \kappa \upharpoonleft R \in 1 \rightarrow \text{Cls}\text{, etc.} \] or in which such hypotheses are shown to be deducible from others. Hypotheses of this kind occur very frequently, and it is important to be able to deal with them easily. For the sake of completeness, we shall here repeat propositions previously proved on this subject.
>
> …

**Lean reading.** Hypotheses such as `R ↾ λ ∈ 1 → Cls`, `κ ↿ R ∈ Cls → 1` are memberships of restricted relations in `arrow`. The relations `R↾` and `↿R` (✱38 with `♀ = ↾, ↿`) are `opL cres R` and `opR dres R`, so `R↾''κ` is `opL cres R ʻʻ K` and `↿R''κ` is `opR dres R ʻʻ K`; `|Q`, `Q|` are `relProdR Q`, `relProdL Q`; `Q ‖ R` is `Q ∥ R`; `s'κ`, `ṡ'λ` are `sumCls K`, `sumRel L`; `∈ | D ↾ λ` is `memRel ⨾ D ↾ L` (✱35·25); `S̆'S'y` is `Desc2 S˘ S y`. Chains such as `α ↿ Q = Q ↾ β = α ↿ Q ↾ β` and `E!(P↾β)'y . ≡ . y ∈ β . E!P'y . ≡ . …` are conjunctions of their links. The e-text numbers ✱74·15 `*74.15.` (a full stop for the centred dot).

**Status.** proved (all propositions; ✱74·511 proved (corrected), with `pm74_511_printed_false`; ✱74·761 proved (reading); see their docstrings).
-/

/-- ✱74·1. \(\vdash\colon\colon R\upharpoonright \beta\in 1\rightarrow \text{Cls}.\supset\colon\ldotp R\upharpoonright \beta\in 1\rightarrow 1.\equiv:y,\,z\in \beta.Rʻy=Rʻz.\supset_{y,z}.y=z\) -/
theorem pm74_1 {B : Set β} {R : α → β → Prop} :
    R ↾ B ∈ arrow one Cls →
      (R ↾ B ∈ arrow one one ↔
        ∀ y z, (y ∈ B ∧ z ∈ B) ∧ Desc R y (fun b => Desc R z (fun c => b = c)) → y = z) := by
  intro h1
  constructor
  · rintro h y z ⟨⟨hy, hz⟩, he⟩
    obtain ⟨b, hb, hc⟩ := descEq_iff.1 he
    exact mem_arrow_Cls_one.1 (oo_iff'.1 h).2 b y z ⟨⟨(hb b).2 rfl, hy⟩, ⟨(hc b).2 rfl, hz⟩⟩
  · intro h
    refine oo_iff'.2 ⟨h1, mem_arrow_Cls_one.2 fun x y z ⟨⟨hxy, hy⟩, ⟨hxz, hz⟩⟩ => ?_⟩
    refine h y z ⟨⟨hy, hz⟩, descEq_iff.2 ⟨x, fun w => ⟨fun hw => ?_, fun e => e ▸ hxy⟩,
      fun w => ⟨fun hw => ?_, fun e => e ▸ hxz⟩⟩⟩
    · exact mem_arrow_one_Cls.1 h1 w x y ⟨⟨hw, hy⟩, ⟨hxy, hy⟩⟩
    · exact mem_arrow_one_Cls.1 h1 w x z ⟨⟨hw, hz⟩, ⟨hxz, hz⟩⟩

/-- ✱74·11. \(\vdash\colon\ldotp R\upharpoonright \beta\in 1\rightarrow \text{Cls}.\beta\subset \text{ᗡ}ʻR.\equiv:\text{E}‼Rʻʻ\beta \quad[\text{*71·571.(*37·05)}]\) -/
theorem pm74_11 {B : Set β} {R : α → β → Prop} :
    (R ↾ B ∈ arrow one Cls ∧ B ⊆ codom R) ↔ EE R B := by
  constructor
  · rintro ⟨h1, h2⟩ y hy
    obtain ⟨x, hx⟩ := h2 hy
    exact ⟨x, fun w => ⟨fun hw => mem_arrow_one_Cls.1 h1 w x y ⟨⟨hw, hy⟩, ⟨hx, hy⟩⟩,
      fun e => e ▸ hx⟩⟩
  · intro h
    refine ⟨mem_arrow_one_Cls.2 fun x y z ⟨⟨hx, hz⟩, ⟨hy, _⟩⟩ => ?_, fun y hy => ?_⟩
    · obtain ⟨b, hb⟩ := h z hz
      exact ((hb x).1 hx).trans ((hb y).1 hy).symm
    · obtain ⟨b, hb⟩ := h y hy
      exact ⟨b, (hb b).2 rfl⟩

/-- ✱74·12. \[\begin{align}\vdash\colon\colon R\upharpoonright \beta\in 1\rightarrow 1.\beta\subset \text{ᗡ}ʻR.\equiv\colon\ldotp y,z\in \beta.\supset_{y,z}:Rʻy=Rʻz.&\equiv.y=z\\ &[\text{*71·59}]\end{align}\] -/
theorem pm74_12 {B : Set β} {R : α → β → Prop} :
    (R ↾ B ∈ arrow one one ∧ B ⊆ codom R) ↔
      ∀ y z, y ∈ B ∧ z ∈ B → (Desc R y (fun b => Desc R z (fun c => b = c)) ↔ y = z) := by
  constructor
  · rintro ⟨h1, h2⟩ y z ⟨hy, hz⟩
    have hE := pm74_11.1 ⟨(oo_iff'.1 h1).1, h2⟩
    constructor
    · intro he
      exact (pm74_1 (oo_iff'.1 h1).1).1 h1 y z ⟨⟨hy, hz⟩, he⟩
    · rintro rfl
      obtain ⟨b, hb⟩ := hE y hy
      exact descEq_iff.2 ⟨b, hb, hb⟩
  · intro h
    exact (smbar_cres_iff.1 (pm73_28 h).2).1

/-- ✱74·13. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.(\breve{R})_{\in}\upharpoonright \text{Cl}ʻ\text{D}ʻR\in 1\rightarrow 1 \quad[\text{*72·45}]\) -/
theorem pm74_13 {R : α → β → Prop} :
    R ∈ arrow one Cls → imgRel R˘ ↾ cl (dom R) ∈ arrow one one := imgRel_cnv_oo

/-- ✱74·131. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.R_{\in}\upharpoonright Clʻ\text{ᗡ}ʻR\in 1\rightarrow 1 \quad[\text{*72·451}]\) -/
theorem pm74_131 {R : α → β → Prop} :
    R ∈ arrow Cls one → imgRel R ↾ cl (codom R) ∈ arrow one one := imgRel_oo

private theorem cres_eq_chain {A : Set α} {B : Set β} {R : α → β → Prop}
    (e : A ◁ R = R ↾ B) : R ↾ B = A ◁ R ↾ B := by
  rw [e]
  funext x y
  exact propext ⟨fun h => ⟨h, h.2⟩, fun h => h.1⟩

/-- ✱74·14. \(\vdash:R\in 1\rightarrow \text{Cls}.\beta=\breve{R}ʻʻ\alpha.\supset.\alpha\upharpoonleft R=R\upharpoonright \beta=\alpha\upharpoonleft R\upharpoonright \beta \quad[\text{*72·55}]\) -/
theorem pm74_14 {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ∈ arrow one Cls ∧ B = R˘ ʻʻ A → A ◁ R = R ↾ B ∧ R ↾ B = A ◁ R ↾ B := by
  rintro ⟨h, rfl⟩
  have e : A ◁ R = R ↾ R˘ ʻʻ A := by
    funext x y
    apply propext
    constructor
    · rintro ⟨hx, hxy⟩; exact ⟨hxy, x, hx, hxy⟩
    · rintro ⟨hxy, x', hx', hx'y⟩
      exact ⟨(mem_arrow_one_Cls.1 h x x' y ⟨hxy, hx'y⟩) ▸ hx', hxy⟩
  exact ⟨e, cres_eq_chain e⟩

/-- ✱74·141. \(\vdash:R\in \text{Cls}\rightarrow 1.\alpha=Rʻʻ\beta.\supset.\alpha\upharpoonleft R=R\upharpoonright \beta=\alpha\upharpoonleft R\upharpoonright \beta \quad[\text{*72·551}]\) -/
theorem pm74_141 {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ∈ arrow Cls one ∧ A = R ʻʻ B → A ◁ R = R ↾ B ∧ R ↾ B = A ◁ R ↾ B := by
  rintro ⟨h, rfl⟩
  have e : (R ʻʻ B) ◁ R = R ↾ B := by
    funext x y
    apply propext
    constructor
    · rintro ⟨⟨y', hy', hxy'⟩, hxy⟩
      exact ⟨hxy, (mem_arrow_Cls_one.1 h x y' y ⟨hxy', hxy⟩) ▸ hy'⟩
    · rintro ⟨hxy, hy⟩; exact ⟨⟨y, hy, hxy⟩, hxy⟩
  exact ⟨e, cres_eq_chain e⟩

/-- ✱74·15. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow \text{Cls}.\lambda=\breve{Q}ʻʻ\kappa.\supset.\kappa\cap \text{D}ʻQ=Qʻʻ\lambda \quad[\text{*72·57}]\)

The e-text numbers it `*74.15.` (a full stop for the centred dot). It is cited in ✱74·16 and
✱74·3. -/
theorem pm74_15 {K : Set α} {L : Set β} {Q : α → β → Prop} :
    Q ↾ L ∈ arrow one Cls ∧ L = Q˘ ʻʻ K → K ∩ dom Q = Q ʻʻ L := by
  rintro ⟨h, rfl⟩
  ext x
  constructor
  · rintro ⟨hx, y, hxy⟩; exact ⟨y, ⟨x, hx, hxy⟩, hxy⟩
  · rintro ⟨y, ⟨x', hx', hx'y⟩, hxy⟩
    have e := mem_arrow_one_Cls.1 h x x' y ⟨⟨hxy, x', hx', hx'y⟩, ⟨hx'y, x', hx', hx'y⟩⟩
    exact ⟨e ▸ hx', y, hxy⟩

/-- ✱74·151.\(\vdash:\kappa\upharpoonleft Q\in \text{Cls}\rightarrow 1.\kappa=Qʻʻ\lambda.\supset.\lambda\cap \text{ᗡ}ʻQ=\breve{Q}ʻʻ\kappa\) -/
theorem pm74_151 {K : Set α} {L : Set β} {Q : α → β → Prop} :
    K ◁ Q ∈ arrow Cls one ∧ K = Q ʻʻ L → L ∩ codom Q = Q˘ ʻʻ K := by
  rintro ⟨h, rfl⟩
  ext y
  constructor
  · rintro ⟨hy, x, hxy⟩; exact ⟨x, ⟨y, hy, hxy⟩, hxy⟩
  · rintro ⟨x, ⟨y', hy', hxy'⟩, hxy⟩
    have e := mem_arrow_Cls_one.1 h x y' y ⟨⟨⟨y', hy', hxy'⟩, hxy'⟩, ⟨⟨y', hy', hxy'⟩, hxy⟩⟩
    exact ⟨e ▸ hy', x, hxy⟩

/-- ✱74·16. \(\vdash:Q\upharpoonright \lambda\in 1\rightarrow \text{Cls}.\kappa\subset \text{D}ʻQ.\lambda=\breve{Q}ʻʻ\kappa.\supset.\kappa=Qʻʻ\lambda \quad[\text{*74·15.*22·621}]\) -/
theorem pm74_16 {K : Set α} {L : Set β} {Q : α → β → Prop} :
    (Q ↾ L ∈ arrow one Cls ∧ K ⊆ dom Q) ∧ L = Q˘ ʻʻ K → K = Q ʻʻ L := by
  rintro ⟨⟨h, hK⟩, rfl⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, hxy⟩ := hK hx
    exact ⟨y, ⟨x, hx, hxy⟩, hxy⟩
  · rintro ⟨y, ⟨x', hx', hx'y⟩, hxy⟩
    have e := mem_arrow_one_Cls.1 h x x' y ⟨⟨hxy, x', hx', hx'y⟩, ⟨hx'y, x', hx', hx'y⟩⟩
    exact e ▸ hx'

/-- ✱74·161. \(\vdash:\kappa\upharpoonleft Q\in \text{Cls}\rightarrow 1.\lambda\subset \text{ᗡ}ʻQ.\kappa=Qʻʻ\lambda.\supset.\lambda=\breve{Q}ʻʻ\kappa\) -/
theorem pm74_161 {K : Set α} {L : Set β} {Q : α → β → Prop} :
    (K ◁ Q ∈ arrow Cls one ∧ L ⊆ codom Q) ∧ K = Q ʻʻ L → L = Q˘ ʻʻ K := by
  rintro ⟨⟨h, hL⟩, hK⟩
  have h' : Q˘ ↾ K ∈ arrow one Cls := by rw [← cnv_dres]; exact cnv_oc.2 h
  exact pm74_16 (Q := Q˘) ⟨⟨h', hL⟩, hK⟩

/-- ✱74·17. \(\vdash:Q\upharpoonright \breve{Q}ʻʻ\kappa\in 1\rightarrow \text{Cls}.\kappa\subset \text{D}ʻQ.\supset.\kappa=Qʻʻ\breve{Q}ʻʻ\kappa \quad[\text{*74·16}]\) -/
theorem pm74_17 {K : Set α} {Q : α → β → Prop} :
    Q ↾ Q˘ ʻʻ K ∈ arrow one Cls ∧ K ⊆ dom Q → K = Q ʻʻ Q˘ ʻʻ K :=
  fun ⟨h, hK⟩ => pm74_16 ⟨⟨h, hK⟩, rfl⟩

/-- ✱74·171. \(\vdash:(Qʻʻ\lambda)\upharpoonleft Q\in \text{Cls}\rightarrow 1.\lambda\subset \text{ᗡ}ʻQ.\supset.\lambda=\breve{Q}ʻʻQʻʻ\lambda\) -/
theorem pm74_171 {L : Set β} {Q : α → β → Prop} :
    (Q ʻʻ L) ◁ Q ∈ arrow Cls one ∧ L ⊆ codom Q → L = Q˘ ʻʻ Q ʻʻ L :=
  fun ⟨h, hL⟩ => pm74_161 ⟨⟨h, hL⟩, rfl⟩

/-- ✱74·2. \(\vdash:\breve{Q}ʻʻ\alpha\subset \beta.\supset.\alpha\upharpoonleft Q=\alpha\upharpoonleft Q\upharpoonright \beta\) -/
theorem pm74_2 {A : Set α} {B : Set β} {Q : α → β → Prop} :
    Q˘ ʻʻ A ⊆ B → A ◁ Q = A ◁ Q ↾ B := by
  intro h
  funext x y
  exact propext ⟨fun hh => ⟨hh, h ⟨x, hh.1, hh.2⟩⟩, fun hh => hh.1⟩

/-- ✱74·201. \(\vdash:Qʻʻ\beta\subset \alpha.\supset.Q\upharpoonright \beta=\alpha\upharpoonleft Q\upharpoonright \beta \quad[\text{Similar proof}]\) -/
theorem pm74_201 {A : Set α} {B : Set β} {Q : α → β → Prop} :
    Q ʻʻ B ⊆ A → Q ↾ B = A ◁ Q ↾ B := by
  intro h
  funext x y
  exact propext ⟨fun hh => ⟨⟨h ⟨y, hh.2, hh.1⟩, hh.1⟩, hh.2⟩, fun hh => ⟨hh.1.2, hh.2⟩⟩

/-- ✱74·21. \(\vdash.\alpha\upharpoonleft Q=\alpha\upharpoonleft Q\upharpoonright \breve{Q}ʻʻ\alpha \quad[\text{*74·2}]\) -/
theorem pm74_21 {A : Set α} {Q : α → β → Prop} : A ◁ Q = A ◁ Q ↾ Q˘ ʻʻ A := pm74_2 le_rfl

/-- ✱74·211. \(\vdash.Q\upharpoonright \beta=(Qʻʻ\beta)\upharpoonleft Q\upharpoonright \beta \quad[\text{*74·201}]\) -/
theorem pm74_211 {B : Set β} {Q : α → β → Prop} : Q ↾ B = (Q ʻʻ B) ◁ Q ↾ B := pm74_201 le_rfl

/-- ✱74·22. \(\vdash:\text{D}ʻQ\subset \alpha.\supset.Q=\alpha\upharpoonleft Q \quad[\text{*35·451}]\) -/
theorem pm74_22 {A : Set α} {Q : α → β → Prop} : dom Q ⊆ A → Q = A ◁ Q := by
  intro h
  funext x y
  exact propext ⟨fun hh => ⟨h ⟨y, hh⟩, hh⟩, fun hh => hh.2⟩

/-- ✱74·221. \(\vdash:\text{ᗡ}ʻQ\subset \beta.\supset.Q=Q\upharpoonright \beta \quad[\text{*35·452}]\) -/
theorem pm74_221 {B : Set β} {Q : α → β → Prop} : codom Q ⊆ B → Q = Q ↾ B := by
  intro h
  funext x y
  exact propext ⟨fun hh => ⟨hh, h ⟨x, hh⟩⟩, fun hh => hh.1⟩

/-- ✱74·23. \(\vdash:\alpha=Qʻʻ\breve{Q}ʻʻ\alpha.\supset.\alpha\upharpoonleft Q=Q\upharpoonright \breve{Q}ʻʻ\alpha=\alpha\upharpoonleft Q\upharpoonright \breve{Q}ʻʻ\alpha \quad[\text{*74·21·211}]\) -/
theorem pm74_23 {A : Set α} {Q : α → β → Prop} :
    A = Q ʻʻ Q˘ ʻʻ A → A ◁ Q = Q ↾ Q˘ ʻʻ A ∧ Q ↾ Q˘ ʻʻ A = A ◁ Q ↾ Q˘ ʻʻ A := by
  intro h
  have e := pm74_211 (Q := Q) (B := Q˘ ʻʻ A)
  rw [← h] at e
  exact ⟨pm74_21.trans e.symm, e⟩

/-- ✱74·231. \(\vdash:\beta=\breve{Q}ʻʻQʻʻ\beta.\supset.Q\upharpoonright \beta=(Qʻʻ\beta)\upharpoonleft Q=(Qʻʻ\beta)\upharpoonleft Q\upharpoonright \beta \quad[\text{*74·21·211}]\) -/
theorem pm74_231 {B : Set β} {Q : α → β → Prop} :
    B = Q˘ ʻʻ Q ʻʻ B → Q ↾ B = (Q ʻʻ B) ◁ Q ∧ (Q ʻʻ B) ◁ Q = (Q ʻʻ B) ◁ Q ↾ B := by
  intro h
  have e := pm74_21 (Q := Q) (A := Q ʻʻ B)
  rw [← h] at e
  exact ⟨pm74_211.trans e.symm, e⟩

/-- ✱74·24. \(\vdash:\alpha=Qʻʻ\beta.\beta=\breve{Q}ʻʻ\alpha.\supset.\alpha\upharpoonleft Q=Q\upharpoonright \beta=\alpha\upharpoonleft Q\upharpoonright \beta \quad[\text{*74·23}]\) -/
theorem pm74_24 {A : Set α} {B : Set β} {Q : α → β → Prop} :
    A = Q ʻʻ B ∧ B = Q˘ ʻʻ A → A ◁ Q = Q ↾ B ∧ Q ↾ B = A ◁ Q ↾ B := by
  rintro ⟨hA, hB⟩
  have e1 := pm74_2 (Q := Q) (A := A) (B := B) (le_of_eq hB.symm)
  have e2 := pm74_201 (Q := Q) (A := A) (B := B) (le_of_eq hA.symm)
  exact ⟨e1.trans e2.symm, e2⟩

/-- ✱74·25. \[\begin{align}&\vdash:Q\upharpoonright \beta\in 1\rightarrow \text{Cls}.\alpha\subset \text{D}ʻQ.\beta=\breve{Q}ʻʻ\alpha.\supset.\alpha\upharpoonleft Q=Q\upharpoonright \beta=\alpha\upharpoonleft Q\upharpoonright \beta\\ &[\text{*74·16·24}]\end{align}\] -/
theorem pm74_25 {A : Set α} {B : Set β} {Q : α → β → Prop} :
    (Q ↾ B ∈ arrow one Cls ∧ A ⊆ dom Q) ∧ B = Q˘ ʻʻ A →
      A ◁ Q = Q ↾ B ∧ Q ↾ B = A ◁ Q ↾ B :=
  fun h => pm74_24 ⟨pm74_16 h, h.2⟩

/-- ✱74·251. \[\begin{align}&\vdash:\alpha\upharpoonleft Q\in \text{Cls}\rightarrow 1.\beta\subset \text{ᗡ}ʻQ.\alpha=Qʻʻ\beta.\supset.\alpha\upharpoonleft Q=Q\upharpoonright \beta=\alpha\upharpoonleft Q\upharpoonright \beta\\ &[\text{**74·161·24}]\end{align}\] -/
theorem pm74_251 {A : Set α} {B : Set β} {Q : α → β → Prop} :
    (A ◁ Q ∈ arrow Cls one ∧ B ⊆ codom Q) ∧ A = Q ʻʻ B →
      A ◁ Q = Q ↾ B ∧ Q ↾ B = A ◁ Q ↾ B :=
  fun h => pm74_24 ⟨h.2, pm74_161 h⟩

/-- ✱74·26. \(\vdash:Q\upharpoonright \beta\in 1\rightarrow 1.\alpha\subset \text{D}ʻQ.\beta=\breve{Q}ʻʻ\alpha.\equiv.\alpha\upharpoonleft Q\in 1\rightarrow 1.\beta\subset \text{ᗡ}ʻQ.\alpha=Qʻʻ\beta\) -/
theorem pm74_26 {A : Set α} {B : Set β} {Q : α → β → Prop} :
    (Q ↾ B ∈ arrow one one ∧ A ⊆ dom Q) ∧ B = Q˘ ʻʻ A ↔
      (A ◁ Q ∈ arrow one one ∧ B ⊆ codom Q) ∧ A = Q ʻʻ B := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hA := pm74_16 ⟨⟨(oo_iff'.1 h1).1, h2⟩, h3⟩
    have e := (pm74_24 ⟨hA, h3⟩).1
    refine ⟨⟨e ▸ h1, ?_⟩, hA⟩
    rw [h3]; exact fun y ⟨x, _, hxy⟩ => ⟨x, hxy⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hB := pm74_161 ⟨⟨(oo_iff'.1 h1).2, h2⟩, h3⟩
    have e := (pm74_24 ⟨h3, hB⟩).1
    refine ⟨⟨e.symm ▸ h1, ?_⟩, hB⟩
    rw [h3]; exact fun x ⟨y, _, hxy⟩ => ⟨y, hxy⟩

/-- ✱74·27. \(\vdash:Q\upharpoonright \beta\in 1\rightarrow 1.\beta=\breve{Q}ʻʻQʻʻ\beta.\equiv.(Qʻʻ\beta)\upharpoonleft Q\in 1\rightarrow 1.\beta\subset \text{ᗡ}ʻQ\) -/
theorem pm74_27 {B : Set β} {Q : α → β → Prop} :
    Q ↾ B ∈ arrow one one ∧ B = Q˘ ʻʻ Q ʻʻ B ↔ (Q ʻʻ B) ◁ Q ∈ arrow one one ∧ B ⊆ codom Q := by
  have hsub : Q ʻʻ B ⊆ dom Q := fun x ⟨y, _, hxy⟩ => ⟨y, hxy⟩
  constructor
  · rintro ⟨h1, h2⟩
    exact (pm74_26.1 ⟨⟨h1, hsub⟩, h2⟩).1
  · rintro ⟨h1, h2⟩
    obtain ⟨⟨h3, -⟩, h4⟩ := pm74_26.2 ⟨⟨h1, h2⟩, rfl⟩
    exact ⟨h3, h4⟩

/-- ✱74·271. \[\begin{align}&\vdash:\alpha\upharpoonleft Q\in 1\rightarrow 1.\alpha=Qʻʻ\breve{Q}ʻʻ\alpha.\equiv.Q\upharpoonright \breve{Q}ʻʻ\alpha\in 1\rightarrow 1.\alpha\subset \text{D}ʻQ\\ &\left[\text{*74·26}\, \frac{\breve{Q}ʻʻ\alpha}{\beta}\right]\end{align}\] -/
theorem pm74_271 {A : Set α} {Q : α → β → Prop} :
    A ◁ Q ∈ arrow one one ∧ A = Q ʻʻ Q˘ ʻʻ A ↔ Q ↾ Q˘ ʻʻ A ∈ arrow one one ∧ A ⊆ dom Q := by
  have hsub : Q˘ ʻʻ A ⊆ codom Q := fun y ⟨x, _, hxy⟩ => ⟨x, hxy⟩
  constructor
  · rintro ⟨h1, h2⟩
    exact (pm74_26.2 ⟨⟨h1, hsub⟩, h2⟩).1
  · rintro ⟨h1, h2⟩
    obtain ⟨⟨h3, -⟩, h4⟩ := pm74_26.1 ⟨⟨h1, h2⟩, rfl⟩
    exact ⟨h3, h4⟩

/-- ✱74·3. \(\vdash\colon\ldotp Q\upharpoonright \beta\in 1\rightarrow \text{Cls}:(\exists \alpha).\beta=\breve{Q}ʻʻ\alpha:\supset.\breve{Q}ʻʻQʻʻ\beta=\beta\) -/
theorem pm74_3 {B : Set β} {Q : α → β → Prop} :
    Q ↾ B ∈ arrow one Cls ∧ (∃ A : Set α, B = Q˘ ʻʻ A) → Q˘ ʻʻ Q ʻʻ B = B := by
  rintro ⟨h, A, rfl⟩
  ext y
  constructor
  · rintro ⟨x, ⟨y', ⟨x', hx', hx'y'⟩, hxy'⟩, hxy⟩
    have e := mem_arrow_one_Cls.1 h x x' y'
      ⟨⟨hxy', x', hx', hx'y'⟩, ⟨hx'y', x', hx', hx'y'⟩⟩
    exact ⟨x, e ▸ hx', hxy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, ⟨y, ⟨x, hx, hxy⟩, hxy⟩, hxy⟩

/-- ✱74·301. \(\vdash\colon\ldotp \alpha\upharpoonleft Q\in \text{Cls}\rightarrow 1:(\exists \beta).\alpha=Qʻʻ\beta:\supset.Qʻʻ\breve{Q}ʻʻ\alpha=\alpha \quad[\text{Similar proof}]\) -/
theorem pm74_301 {A : Set α} {Q : α → β → Prop} :
    A ◁ Q ∈ arrow Cls one ∧ (∃ B : Set β, A = Q ʻʻ B) → Q ʻʻ Q˘ ʻʻ A = A := by
  rintro ⟨h, B, hA⟩
  have h' : Q˘ ↾ A ∈ arrow one Cls := by rw [← cnv_dres]; exact cnv_oc.2 h
  exact pm74_3 (Q := Q˘) ⟨h', B, hA⟩

/-- ✱74·31. \[\begin{align}\vdash:Q\upharpoonright &\beta\in 1\rightarrow \text{Cls}.\beta\in \text{D}ʻ(\breve{Q})_{\in}.\supset.\\ &\beta=\breve{Q}ʻʻQʻʻ\beta.\beta\subset \text{ᗡ}ʻQ.Q\upharpoonright \beta=(Qʻʻ\beta)\upharpoonleft Q.(Qʻʻ\beta)\upharpoonleft Q\in 1\rightarrow \text{Cls}\end{align}\] -/
theorem pm74_31 {B : Set β} {Q : α → β → Prop} :
    Q ↾ B ∈ arrow one Cls ∧ B ∈ dom (imgRel Q˘) →
      ((B = Q˘ ʻʻ Q ʻʻ B ∧ B ⊆ codom Q) ∧ Q ↾ B = (Q ʻʻ B) ◁ Q) ∧
        (Q ʻʻ B) ◁ Q ∈ arrow one Cls := by
  rintro ⟨h, A, hA⟩
  have e1 : B = Q˘ ʻʻ Q ʻʻ B := (pm74_3 ⟨h, A, hA⟩).symm
  have e2 := (pm74_231 e1).1
  refine ⟨⟨⟨e1, ?_⟩, e2⟩, e2 ▸ h⟩
  rw [show B = Q˘ ʻʻ A from hA]
  exact fun y ⟨x, _, hxy⟩ => ⟨x, hxy⟩

/-- ✱74·311. \[\begin{align}&\vdash:\alpha\upharpoonleft Q\in \text{Cls}\rightarrow 1.\alpha\in \text{D}ʻQ_{\in}.\supset.\\ &\alpha=Qʻʻ\breve{Q}ʻʻ\alpha.\alpha\subset \text{D}ʻQ.\alpha\upharpoonleft Q=Q\upharpoonright \breve{Q}ʻʻ\alpha.Q\upharpoonright \breve{Q}ʻʻ\alpha\in \text{Cls}\rightarrow 1\\ &[\text{Similar proof}]\end{align}\] -/
theorem pm74_311 {A : Set α} {Q : α → β → Prop} :
    A ◁ Q ∈ arrow Cls one ∧ A ∈ dom (imgRel Q) →
      ((A = Q ʻʻ Q˘ ʻʻ A ∧ A ⊆ dom Q) ∧ A ◁ Q = Q ↾ Q˘ ʻʻ A) ∧
        Q ↾ Q˘ ʻʻ A ∈ arrow Cls one := by
  rintro ⟨h, B, hB⟩
  have e1 : A = Q ʻʻ Q˘ ʻʻ A := (pm74_301 ⟨h, B, hB⟩).symm
  have e2 := (pm74_23 e1).1
  refine ⟨⟨⟨e1, ?_⟩, e2⟩, e2 ▸ h⟩
  rw [show A = Q ʻʻ B from hB]
  exact fun x ⟨y, _, hxy⟩ => ⟨y, hxy⟩

/-- ✱74·32. \(\vdash:\kappa\subset \text{ᗡ}ʻR.R\upharpoonright \kappa\in \text{Cls}\rightarrow 1.\supset.\overrightarrow{R}\upharpoonright \kappa\in 1\rightarrow 1\) -/
theorem pm74_32 {K : Set β} {R : α → β → Prop} :
    K ⊆ codom R ∧ R ↾ K ∈ arrow Cls one → Rfwd R ↾ K ∈ arrow one one := by
  rintro ⟨hK, h⟩
  refine oo_iff'.2 ⟨oc_mono (graph_oc _) fun _ _ hh => hh.1,
    mem_arrow_Cls_one.2 fun X y z ⟨⟨h1, hy⟩, ⟨h2, hz⟩⟩ => ?_⟩
  obtain ⟨x, hxy⟩ := hK hy
  have hx : x ∈ refs R y := hxy
  have hx' : x ∈ refs R z := (show refs R y = refs R z from (h1 : X = _).symm.trans h2) ▸ hx
  exact mem_arrow_Cls_one.1 h x y z ⟨⟨hxy, hy⟩, ⟨hx', hz⟩⟩

/-- ✱74·4. \(\vdash:P\mid (Q\upharpoonright \lambda)=P\mid Q.\equiv.\breve{Q}ʻʻ\text{ᗡ}ʻP\subset \lambda\) -/
theorem pm74_4 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    P ⨾ (Q ↾ L) = P ⨾ Q ↔ Q˘ ʻʻ codom P ⊆ L := by
  constructor
  · rintro h z ⟨y, ⟨x, hxy⟩, hyz⟩
    have : (P ⨾ (Q ↾ L)) x z := h ▸ ⟨y, hxy, hyz⟩
    obtain ⟨_, _, _, hz⟩ := this
    exact hz
  · intro h
    funext x z
    apply propext
    constructor
    · rintro ⟨y, hxy, hyz, -⟩; exact ⟨y, hxy, hyz⟩
    · rintro ⟨y, hxy, hyz⟩; exact ⟨y, hxy, hyz, h ⟨y, ⟨x, hxy⟩, hyz⟩⟩

/-- ✱74·41. \(\vdash:\text{ᗡ}ʻP\cap \text{D}ʻQ\subset \kappa.\supset.P\mid \kappa\upharpoonleft Q=P\mid Q\) -/
theorem pm74_41 {P : α → β → Prop} {Q : β → γ → Prop} {K : Set β} :
    codom P ∩ dom Q ⊆ K → P ⨾ K ◁ Q = P ⨾ Q := by
  intro h
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, -, hyz⟩; exact ⟨y, hxy, hyz⟩
  · rintro ⟨y, hxy, hyz⟩; exact ⟨y, hxy, h ⟨⟨x, hxy⟩, ⟨z, hyz⟩⟩, hyz⟩

/-- ✱74·42. \(\vdash:\text{ᗡ}ʻP\subset Qʻʻ\lambda.\supset.\text{D}ʻ(P\mid Q\upharpoonright \lambda)=\text{D}ʻP \quad[\text{*37·321·401}]\) -/
theorem pm74_42 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    codom P ⊆ Q ʻʻ L → dom (P ⨾ Q ↾ L) = dom P := by
  intro h
  ext x
  constructor
  · rintro ⟨z, ⟨y, hxy, -⟩, -⟩; exact ⟨y, hxy⟩
  · rintro ⟨y, hxy⟩
    obtain ⟨z, hz, hyz⟩ := h ⟨x, hxy⟩
    exact ⟨z, ⟨y, hxy, hyz⟩, hz⟩

/-- ✱74·43. \(\vdash:Qʻʻ\lambda\subset \text{ᗡ}ʻP.\supset.\text{ᗡ}ʻ(P\mid Q\upharpoonright \lambda)=\text{ᗡ}ʻQ\cap \lambda \quad[\text{*37·322·401.*35·64}]\) -/
theorem pm74_43 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    Q ʻʻ L ⊆ codom P → codom (P ⨾ Q ↾ L) = codom Q ∩ L := by
  intro h
  ext z
  constructor
  · rintro ⟨x, ⟨y, -, hyz⟩, hz⟩; exact ⟨⟨y, hyz⟩, hz⟩
  · rintro ⟨⟨y, hyz⟩, hz⟩
    obtain ⟨x, hxy⟩ := h ⟨z, hz, hyz⟩
    exact ⟨x, ⟨y, hxy, hyz⟩, hz⟩

/-- ✱74·44. \[\begin{align}\vdash:\text{ᗡ}ʻP=Qʻʻ\lambda.\supset.\text{D}ʻ(P\mid Q\upharpoonright \lambda)=\text{D}ʻP.\text{ᗡ}ʻ&(P\mid Q\upharpoonright \lambda)=\text{ᗡ}ʻQ\cap \lambda\\ &[\text{*74·42·43}]\end{align}\] -/
theorem pm74_44 {P : α → β → Prop} {Q : β → γ → Prop} {L : Set γ} :
    codom P = Q ʻʻ L → dom (P ⨾ Q ↾ L) = dom P ∧ codom (P ⨾ Q ↾ L) = codom Q ∩ L :=
  fun h => ⟨pm74_42 (le_of_eq h), pm74_43 (le_of_eq h.symm)⟩

/-- ✱74·5. \(\vdash:\text{E}!(P\upharpoonright \beta)ʻy.\equiv.y\in \beta.\text{E}!Pʻy.\equiv.(P\upharpoonright \beta)ʻy=Pʻy\) -/
theorem pm74_5 {P : α → β → Prop} {B : Set β} {y : β} :
    (EDesc (P ↾ B) y ↔ y ∈ B ∧ EDesc P y) ∧
      (y ∈ B ∧ EDesc P y ↔ Desc (P ↾ B) y (fun b => Desc P y (fun c => b = c))) := by
  refine ⟨⟨fun ⟨b, hb⟩ => ?_, fun ⟨hy, b, hb⟩ => ?_⟩, ⟨fun ⟨hy, b, hb⟩ => ?_, fun h => ?_⟩⟩
  · have hy : y ∈ B := ((hb b).2 rfl).2
    exact ⟨hy, b, fun x => ⟨fun h => (hb x).1 ⟨h, hy⟩, fun e => ((hb x).2 e).1⟩⟩
  · exact ⟨b, fun x => ⟨fun h => (hb x).1 h.1, fun e => ⟨(hb x).2 e, hy⟩⟩⟩
  · exact descEq_iff.2 ⟨b, fun x => ⟨fun h => (hb x).1 h.1, fun e => ⟨(hb x).2 e, hy⟩⟩, hb⟩
  · obtain ⟨b, h1, h2⟩ := descEq_iff.1 h
    exact ⟨((h1 b).2 rfl).2, b, h2⟩

/-- ✱74·51. \(\vdash\colon\ldotp \overrightarrow{P}ʻy\subset \alpha.\supset:\text{E}!(\alpha\upharpoonleft P)ʻy.\equiv.\text{E}!Pʻy.\equiv.Pʻy=(\alpha\upharpoonleft P)ʻy\) -/
theorem pm74_51 {P : α → β → Prop} {A : Set α} {y : β} :
    refs P y ⊆ A →
      (EDesc (A ◁ P) y ↔ EDesc P y) ∧
        (EDesc P y ↔ Desc P y (fun b => Desc (A ◁ P) y (fun c => b = c))) := by
  intro h
  have hiff : ∀ x, (A ◁ P) x y ↔ P x y := fun x => ⟨fun hh => hh.2, fun hh => ⟨h hh, hh⟩⟩
  refine ⟨⟨fun ⟨b, hb⟩ => ⟨b, fun x => (hiff x).symm.trans (hb x)⟩,
    fun ⟨b, hb⟩ => ⟨b, fun x => (hiff x).trans (hb x)⟩⟩, ⟨fun ⟨b, hb⟩ => ?_, fun hh => ?_⟩⟩
  · exact descEq_iff.2 ⟨b, hb, fun x => (hiff x).trans (hb x)⟩
  · obtain ⟨b, h1, -⟩ := descEq_iff.1 hh
    exact ⟨b, h1⟩

/-- ✱74·511. \[\begin{align}&\vdash\colon\ldotp \overleftarrow{P}ʻx\subset \beta.\supset:\text{E}!(\breve{P}\upharpoonright \beta)ʻx.\equiv.\text{E}!\breve{P}ʻx.\equiv.\breve{P}ʻx=(\breve{P}\upharpoonright \beta)ʻx\\ &[\text{Proof as in *74·51}]\end{align}\]

**Status.** proved (corrected): as printed, with `P̆ ↾ β`, the proposition is false: `E!(P̆ ↾ β)'x`
requires `x ∈ β` (`P̆ ↾ β` restricts the relata of `P̆`, i.e. the referents of `P`), so it fails for
`P = x ↓ y`, `β = ι'y`, `x ≠ y` (`pm74_511_printed_false`; for heterogeneous `P` the printed
formula is not even well typed, since `P⃖'x ⊂ β` makes `β` a class of relata of `P`). PM intends
`(P ↾ β)˘` (`= β ↿ P̆`), the converse of `P ↾ β`, which is what ✱74·51 with `P̆` for `P` gives
("Proof as in ✱74·51", with `P̆⃗'x = P⃖'x` and `β ↿ P̆` for `α ↿ P`); the corrected form is proved.
Whether the misprint is PM's or the e-text's (a breve over the whole of `P ↾ β`) cannot be decided
from the e-text; the errata do not list it. -/
theorem pm74_511 {P : α → β → Prop} {B : Set β} {x : α} :
    rels P x ⊆ B →
      (EDesc (P ↾ B)˘ x ↔ EDesc P˘ x) ∧
        (EDesc P˘ x ↔ Desc P˘ x (fun b => Desc (P ↾ B)˘ x (fun c => b = c))) := by
  intro h
  rw [cnv_cres]
  exact pm74_51 (P := P˘) h

/-- The printed form of ✱74·511 (with `P̆ ↾ β`) is false: take `P = false ↓ true` on `Bool`,
`β = ι'true`, `x = false`; then `P⃖'x ⊂ β` and `E!P̆'x`, but not `E!(P̆ ↾ β)'x`. -/
theorem pm74_511_printed_false :
    ¬ ∀ (P : Bool → Bool → Prop) (B : Set Bool) (x : Bool),
      rels P x ⊆ B →
        (EDesc (P˘ ↾ B) x ↔ EDesc P˘ x) ∧
          (EDesc P˘ x ↔ Desc P˘ x (fun b => Desc (P˘ ↾ B) x (fun c => b = c))) := by
  intro h
  have hs : rels (fun a b : Bool => a = false ∧ b = true) false ⊆ {true} :=
    fun y hy => (hy : false = false ∧ y = true).2
  obtain ⟨b, hb⟩ := (h _ _ _ hs).1.2
    ⟨true, fun z => ⟨fun hz => (hz : false = false ∧ z = true).2, fun e => ⟨rfl, e⟩⟩⟩
  have hB : false ∈ ({true} : Set Bool) := ((hb b).2 rfl).2
  exact Bool.false_ne_true hB

/-- ✱74·52. \(\vdash:(Sʻʻ\beta)\upharpoonleft S\in 1\rightarrow \text{Cls}.\beta\subset \text{ᗡ}ʻS.y\in \beta.\supset.\{(Sʻʻ\beta)\upharpoonleft S\}ʻy=Sʻy.\text{E}!Sʻy\) -/
theorem pm74_52 {S : α → β → Prop} {B : Set β} {y : β} :
    ((S ʻʻ B) ◁ S ∈ arrow one Cls ∧ B ⊆ codom S) ∧ y ∈ B →
      Desc ((S ʻʻ B) ◁ S) y (fun b => Desc S y (fun c => b = c)) ∧ EDesc S y := by
  rintro ⟨⟨h1, h2⟩, hy⟩
  have hiff : ∀ x, ((S ʻʻ B) ◁ S) x y ↔ S x y :=
    fun x => ⟨fun hh => hh.2, fun hh => ⟨⟨y, hy, hh⟩, hh⟩⟩
  obtain ⟨b, hb⟩ := h2 hy
  have hu : ∀ x, S x y ↔ x = b := fun x =>
    ⟨fun hx => mem_arrow_one_Cls.1 h1 x b y ⟨(hiff x).2 hx, (hiff b).2 hb⟩, fun e => e ▸ hb⟩
  exact ⟨descEq_iff.2 ⟨b, fun x => (hiff x).trans (hu x), hu⟩, b, hu⟩

/-- ✱74·521. \[\begin{align}&\vdash:S\upharpoonright \breve{S}ʻʻ\beta\in \text{Cls}\rightarrow 1.\beta\subset \text{D}ʻS.y\in \beta.\supset.\{(\breve{S}ʻʻ\beta)\upharpoonleft \breve{S}\}ʻy=\breve{S}ʻy.\text{E}!\breve{S}ʻy\\ &\left[\text{*74·52}\, \frac{\breve{S}}{S}\right]\end{align}\] -/
theorem pm74_521 {S : α → β → Prop} {B : Set α} {y : α} :
    (S ↾ S˘ ʻʻ B ∈ arrow Cls one ∧ B ⊆ dom S) ∧ y ∈ B →
      Desc ((S˘ ʻʻ B) ◁ S˘) y (fun b => Desc S˘ y (fun c => b = c)) ∧ EDesc S˘ y := by
  rintro ⟨⟨h1, h2⟩, hy⟩
  have h1' : (S˘ ʻʻ B) ◁ S˘ ∈ arrow one Cls := by rw [← cnv_cres]; exact cnv_oc.2 h1
  exact pm74_52 (S := S˘) ⟨⟨h1', h2⟩, hy⟩

/-- ✱74·53. \(\vdash:(Sʻʻ\beta)\upharpoonleft S\in 1\rightarrow 1.\beta\subset \text{ᗡ}ʻS.y\in \beta.\supset.\breve{S}ʻSʻy=y\) -/
theorem pm74_53 {S : α → β → Prop} {B : Set β} {y : β} :
    ((S ʻʻ B) ◁ S ∈ arrow one one ∧ B ⊆ codom S) ∧ y ∈ B → Desc2 S˘ S y (fun b => b = y) := by
  rintro ⟨⟨h1, h2⟩, hy⟩
  obtain ⟨-, b, hb⟩ := pm74_52 ⟨⟨(oo_iff'.1 h1).1, h2⟩, hy⟩
  rw [desc2_iff]
  refine (TheIs_iff_of_unique hb).2 ((TheIs_iff_of_unique fun w => ?_).2 rfl)
  have hby : S b y := (hb b).2 rfl
  constructor
  · intro hw
    exact (mem_arrow_Cls_one.1 (oo_iff'.1 h1).2 b y w
      ⟨⟨⟨y, hy, hby⟩, hby⟩, ⟨⟨y, hy, hby⟩, hw⟩⟩).symm
  · rintro rfl; exact hby

/-- ✱74·531. \[\begin{align}&\vdash:S\upharpoonright \breve{S}ʻʻ\beta\in 1\rightarrow 1.\beta\subset \text{D}ʻS.y\in \beta.\supset.Sʻ\breve{S}ʻy=y\\ &\left[\text{*74·53}\, \frac{\breve{S}}{S}\right]\end{align}\] -/
theorem pm74_531 {S : α → β → Prop} {B : Set α} {y : α} :
    (S ↾ S˘ ʻʻ B ∈ arrow one one ∧ B ⊆ dom S) ∧ y ∈ B → Desc2 S S˘ y (fun b => b = y) := by
  rintro ⟨⟨h1, h2⟩, hy⟩
  have h1' : (S˘ ʻʻ B) ◁ S˘ ∈ arrow one one := by rw [← cnv_cres]; exact cnv_oo.2 h1
  exact pm74_53 (S := S˘) ⟨⟨h1', h2⟩, hy⟩

private theorem img3_cancel {T : α → β → Prop} {L : Set (Set β)} {K : Set (Set α)}
    (hT : T ∈ arrow one one) (hL : L ⊆ cl (codom T)) (h : K = imgRel T ʻʻ L) :
    L = imgRel T˘ ʻʻ K := by
  subst h
  have hT2 := (oo_iff'.1 hT).2
  ext Y
  constructor
  · intro hY
    exact ⟨T ʻʻ Y, ⟨Y, hY, rfl⟩, (img_cnv_img hT2 (hL hY)).symm⟩
  · rintro ⟨X, ⟨Y', hY', hX⟩, hY⟩
    have hX : X = T ʻʻ Y' := hX
    have hY : Y = T˘ ʻʻ X := hY
    rw [hY, hX, img_cnv_img hT2 (hL hY')]
    exact hY'

/-- ✱74·6. \(\vdash\colon\ldotp T\in 1\rightarrow 1.\lambda\subset \text{Cl}ʻ\text{ᗡ}ʻT.\kappa\subset \text{Cl}ʻ\text{D}ʻT.\supset:\kappa=T_{\in}ʻʻ\lambda.\equiv.\lambda=(\breve{T})_{\in}ʻʻ\kappa\) -/
theorem pm74_6 {T : α → β → Prop} {L : Set (Set β)} {K : Set (Set α)} :
    (T ∈ arrow one one ∧ L ⊆ cl (codom T)) ∧ K ⊆ cl (dom T) →
      (K = imgRel T ʻʻ L ↔ L = imgRel T˘ ʻʻ K) :=
  fun ⟨⟨hT, hL⟩, hK⟩ => ⟨img3_cancel hT hL, img3_cancel (T := T˘) (cnv_oo.2 hT) hK⟩

/-- ✱74·61. \(\vdash\colon\ldotp T\in 1\rightarrow 1.\supset:\lambda\subset \text{Cl}ʻ\text{ᗡ}ʻT.\kappa=Tʻʻʻ\lambda.\equiv.\kappa\subset \text{Cl}ʻ\text{D}ʻT.\lambda=\breve{T}ʻʻʻ\kappa\) -/
theorem pm74_61 {T : α → β → Prop} {L : Set (Set β)} {K : Set (Set α)} :
    T ∈ arrow one one →
      (L ⊆ cl (codom T) ∧ K = T ʻʻʻ L ↔ K ⊆ cl (dom T) ∧ L = T˘ ʻʻʻ K) := by
  intro hT
  constructor
  · rintro ⟨hL, hK⟩
    refine ⟨?_, img3_cancel hT hL hK⟩
    rw [hK]
    rintro X ⟨Y, -, hX⟩
    rw [show X = T ʻʻ Y from hX]
    exact fun x ⟨y, _, hxy⟩ => ⟨y, hxy⟩
  · rintro ⟨hK, hL⟩
    refine ⟨?_, img3_cancel (T := T˘) (cnv_oo.2 hT) hK hL⟩
    rw [hL]
    rintro Y ⟨X, -, hY⟩
    rw [show Y = T˘ ʻʻ X from hY]
    exact fun y ⟨x, _, hxy⟩ => ⟨x, hxy⟩

/-- ✱74·62. \(\vdash\colon\ldotp y,z\in \beta.y \neq z.\supset_{y,z}.\overrightarrow{S}ʻy\cap \overrightarrow{S}ʻz=\Lambda:\equiv.S\upharpoonright \beta\in \text{Cls}\rightarrow 1\) -/
theorem pm74_62 {S : α → β → Prop} {B : Set β} :
    (∀ y z, (y ∈ B ∧ z ∈ B) ∧ y ≠ z → refs S y ∩ refs S z = Λ) ↔ S ↾ B ∈ arrow Cls one := by
  rw [mem_arrow_Cls_one]
  constructor
  · rintro h x y z ⟨⟨hxy, hy⟩, ⟨hxz, hz⟩⟩
    by_contra hne
    exact disj (h y z ⟨⟨hy, hz⟩, hne⟩) hxy hxz
  · rintro h y z ⟨⟨hy, hz⟩, hne⟩
    exact disj_iff.2 fun x h1 h2 => hne (h x y z ⟨⟨h1, hy⟩, ⟨h2, hz⟩⟩)

private theorem refs_memRel_D (P : α → β → Prop) : refs (memRel ⨾ D) P = dom P := by
  ext x; exact ⟨fun ⟨_, hx, e⟩ => (e : _ = dom P) ▸ hx, fun hx => ⟨dom P, hx, rfl⟩⟩

private theorem refs_memRel_Dcnv (P : α → β → Prop) : refs (memRel ⨾ Dcnv) P = codom P := by
  ext x; exact ⟨fun ⟨_, hx, e⟩ => (e : _ = codom P) ▸ hx, fun hx => ⟨codom P, hx, rfl⟩⟩

/-- ✱74·63. \[\begin{align}&\vdash\colon\ldotp P,\,Q\in \lambda.P \neq Q.\supset_{P,Q}.\text{D}ʻP\cap \text{D}ʻQ=\Lambda:\equiv.\in \mid \text{D}\upharpoonright \lambda\in \text{Cls}\rightarrow 1\\ &[\text{*74·62.*72·27}]\end{align}\] -/
theorem pm74_63 {L : Set (α → β → Prop)} :
    (∀ P Q, (P ∈ L ∧ Q ∈ L) ∧ P ≠ Q → dom P ∩ dom Q = Λ) ↔
      memRel ⨾ D ↾ L ∈ arrow Cls one := by
  rw [← pm74_62]
  simp only [refs_memRel_D]

/-- ✱74·631. \[\begin{align}&\vdash\colon\ldotp P,\,Q\in \lambda.P \neq Q.\supset_{P,Q}.\text{ᗡ}ʻP\cap \text{ᗡ}ʻQ=\Lambda:\equiv.\in \mid \text{ᗡ}\upharpoonright \lambda\in \text{Cls}\rightarrow 1\\ &[\text{*74·62.*72·27}]\end{align}\] -/
theorem pm74_631 {L : Set (α → β → Prop)} :
    (∀ P Q, (P ∈ L ∧ Q ∈ L) ∧ P ≠ Q → codom P ∩ codom Q = Λ) ↔
      memRel ⨾ Dcnv ↾ L ∈ arrow Cls one := by
  rw [← pm74_62]
  simp only [refs_memRel_Dcnv]

/-- ✱74·632. \[\begin{align}&\vdash\colon\ldotp P,\,Q\in \lambda.P \neq Q.\supset_{P,Q}.CʻP\cap CʻQ=\Lambda:\equiv.F\upharpoonright \lambda\in \text{Cls}\rightarrow 1\\ &[\text{*74·62.*33·5}]\end{align}\] -/
theorem pm74_632 {L : Set (α → α → Prop)} :
    (∀ P Q, (P ∈ L ∧ Q ∈ L) ∧ P ≠ Q → fld P ∩ fld Q = Λ) ↔ F ↾ L ∈ arrow Cls one :=
  pm74_62

/-- ✱74·7. \(\vdash:Q\in 1\rightarrow \text{Cls}.P\mid Q=Pʻ\mid Q.\supset.P\upharpoonright \text{D}ʻQ=Pʻ\upharpoonright \text{D}ʻQ\) -/
theorem pm74_7 {P P' : α → β → Prop} {Q : β → γ → Prop} :
    Q ∈ arrow one Cls ∧ P ⨾ Q = P' ⨾ Q → P ↾ dom Q = P' ↾ dom Q := by
  rintro ⟨hQ, h⟩
  have e : ∀ X : α → β → Prop, (X ↾ dom Q) ⨾ Q = X ⨾ Q := fun X => by
    funext x z
    exact propext ⟨fun ⟨y, ⟨h1, _⟩, h2⟩ => ⟨y, h1, h2⟩, fun ⟨y, h1, h2⟩ => ⟨y, ⟨h1, z, h2⟩, h2⟩⟩
  refine cancelR (S := dom Q) (fun y y' z _ _ h1 h2 => mem_arrow_one_Cls.1 hQ y y' z ⟨h1, h2⟩)
    le_rfl (fun y ⟨_, h⟩ => h.2) (fun y ⟨_, h⟩ => h.2) ?_
  rw [e, e, h]

/-- ✱74·701. \(\vdash:Q\in \text{Cls}\rightarrow 1.Q\mid P=Q\mid P'.\supset.(\text{ᗡ}ʻQ)\upharpoonleft P=(\text{ᗡ}ʻQ)\upharpoonleft P'\) -/
theorem pm74_701 {P P' : α → β → Prop} {Q : γ → α → Prop} :
    Q ∈ arrow Cls one ∧ Q ⨾ P = Q ⨾ P' → codom Q ◁ P = codom Q ◁ P' := by
  rintro ⟨hQ, h⟩
  have e : ∀ X : α → β → Prop, Q ⨾ (codom Q ◁ X) = Q ⨾ X := fun X => by
    funext w y
    exact propext ⟨fun ⟨x, h1, _, h2⟩ => ⟨x, h1, h2⟩, fun ⟨x, h1, h2⟩ => ⟨x, h1, ⟨w, h1⟩, h2⟩⟩
  refine cancelL (S := codom Q) (fun w y y' _ _ h1 h2 => mem_arrow_Cls_one.1 hQ w y y' ⟨h1, h2⟩)
    le_rfl (fun x ⟨_, h⟩ => h.1) (fun x ⟨_, h⟩ => h.1) ?_
  rw [e, e, h]

/-- ✱74·71. \[\begin{align}&\vdash\colon\ldotp Q\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻP\subset \text{D}ʻQ.\text{ᗡ}ʻP'\subset \text{D}ʻQ.\supset:P\mid Q=P'\mid Q.\equiv.P=P'\\ &[\text{*74·7.*35·66.*34·28}]\end{align}\] -/
theorem pm74_71 {P P' : α → β → Prop} {Q : β → γ → Prop} :
    (Q ∈ arrow one Cls ∧ codom P ⊆ dom Q) ∧ codom P' ⊆ dom Q → (P ⨾ Q = P' ⨾ Q ↔ P = P') :=
  fun ⟨⟨hQ, h1⟩, h2⟩ => ⟨cancelR (S := dom Q)
    (fun y y' z _ _ h1 h2 => mem_arrow_one_Cls.1 hQ y y' z ⟨h1, h2⟩) le_rfl h1 h2,
    fun e => e ▸ rfl⟩

/-- ✱74·711. \(\vdash\colon\ldotp Q\in \text{Cls}\rightarrow 1.\text{D}ʻP\subset \text{ᗡ}ʻQ.\text{D}ʻP'\subset \text{ᗡ}ʻQ.\supset:Q\mid P=Q\mid P'.\equiv.P=P'\) -/
theorem pm74_711 {P P' : α → β → Prop} {Q : γ → α → Prop} :
    (Q ∈ arrow Cls one ∧ dom P ⊆ codom Q) ∧ dom P' ⊆ codom Q → (Q ⨾ P = Q ⨾ P' ↔ P = P') :=
  fun ⟨⟨hQ, h1⟩, h2⟩ => ⟨cancelL (S := codom Q)
    (fun w y y' _ _ h1 h2 => mem_arrow_Cls_one.1 hQ w y y' ⟨h1, h2⟩) le_rfl h1 h2,
    fun e => e ▸ rfl⟩

private theorem graph_cres_smbar {f : β → α} {B : Set β}
    (hinj : ∀ y z, y ∈ B → z ∈ B → f y = f z → y = z) :
    graph f ↾ B ∈ smbar (graph f ʻʻ B) B :=
  (pm73_23 ⟨⟨graph_oc f, graph_codom f B⟩, mem_arrow_Cls_one.2 fun x y z ⟨⟨h1, hy⟩, ⟨h2, hz⟩⟩ =>
    hinj y z hy hz ((h1 : x = f y).symm.trans h2)⟩).2

private theorem dom_sub_sumCls {L : Set (α → β → Prop)} {P : α → β → Prop} (hP : P ∈ L) :
    dom P ⊆ sumCls (D ʻʻ L) := fun _ hx => ⟨dom P, ⟨P, hP, rfl⟩, hx⟩

private theorem codom_sub_sumCls {L : Set (α → β → Prop)} {P : α → β → Prop} (hP : P ∈ L) :
    codom P ⊆ sumCls (Dcnv ʻʻ L) := fun _ hy => ⟨codom P, ⟨P, hP, rfl⟩, hy⟩

/-- ✱74·72. \(\vdash\colon\ldotp Q\in 1\rightarrow \text{Cls}:P\in \lambda.\supset_{P}.\text{ᗡ}ʻP\subset \text{D}ʻQ:\supset.(\mid Q)\upharpoonright \lambda\in (\mid Qʻʻ\lambda)\overline{\text{ sm }}\lambda\) -/
theorem pm74_72 {L : Set (α → β → Prop)} {Q : β → γ → Prop} :
    Q ∈ arrow one Cls ∧ (∀ P, P ∈ L → codom P ⊆ dom Q) →
      relProdR Q ↾ L ∈ smbar (relProdR Q ʻʻ L) L :=
  fun ⟨hQ, h⟩ => graph_cres_smbar (f := fun P : α → β → Prop => P ⨾ Q)
    fun P P' hP hP' e => (pm74_71 ⟨⟨hQ, h P hP⟩, h P' hP'⟩).1 e

/-- ✱74·721. \(\vdash\colon\ldotp Q\in \text{Cls}\rightarrow 1:P\in \lambda.\supset_{P}.\text{D}ʻP\subset \text{ᗡ}ʻQ:\supset.(Q\mid )\upharpoonright \lambda\in (Q\mid ʻʻ\lambda)\overline{\text{ sm }}\lambda\) -/
theorem pm74_721 {L : Set (β → γ → Prop)} {Q : α → β → Prop} :
    Q ∈ arrow Cls one ∧ (∀ P, P ∈ L → dom P ⊆ codom Q) →
      relProdL Q ↾ L ∈ smbar (relProdL Q ʻʻ L) L :=
  fun ⟨hQ, h⟩ => graph_cres_smbar (f := fun P : β → γ → Prop => Q ⨾ P)
    fun P P' hP hP' e => (pm74_711 ⟨⟨hQ, h P hP⟩, h P' hP'⟩).1 e

/-- ✱74·73. \[\begin{align}&\vdash:Q\in 1\rightarrow \text{Cls}.sʻ\text{ᗡ}ʻʻ\lambda\subset \text{D}ʻQ.\supset.(\mid Q)\upharpoonright \lambda\in (\mid Qʻʻ\lambda)\overline{\text{ sm }}\lambda\\ &[\text{*74·72.*40·43}]\end{align}\] -/
theorem pm74_73 {L : Set (α → β → Prop)} {Q : β → γ → Prop} :
    Q ∈ arrow one Cls ∧ sumCls (Dcnv ʻʻ L) ⊆ dom Q →
      relProdR Q ↾ L ∈ smbar (relProdR Q ʻʻ L) L :=
  fun ⟨hQ, h⟩ => pm74_72 ⟨hQ, fun _ hP => (codom_sub_sumCls hP).trans h⟩

/-- ✱74·731. \(\vdash:Q\in \text{Cls}\rightarrow 1.sʻ\text{D}ʻʻ\lambda\subset \text{ᗡ}ʻQ.\supset.(Q\mid )\upharpoonright \lambda\in (Q\mid ʻʻ\lambda)\overline{\text{ sm }}\lambda\) -/
theorem pm74_731 {L : Set (β → γ → Prop)} {Q : α → β → Prop} :
    Q ∈ arrow Cls one ∧ sumCls (D ʻʻ L) ⊆ codom Q →
      relProdL Q ↾ L ∈ smbar (relProdL Q ʻʻ L) L :=
  fun ⟨hQ, h⟩ => pm74_721 ⟨hQ, fun _ hP => (dom_sub_sumCls hP).trans h⟩

/-- ✱74·74. \[\begin{align}&\vdash:Q\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻ\dot{s}ʻ\lambda\subset \text{D}ʻQ.\supset.(\mid Q)\upharpoonright \lambda\in (\mid Qʻʻ\lambda)\overline{\text{ sm }}\lambda\\ &[\text{*74·73.*41·44}]\end{align}\] -/
theorem pm74_74 {L : Set (α → β → Prop)} {Q : β → γ → Prop} :
    Q ∈ arrow one Cls ∧ codom (sumRel L) ⊆ dom Q →
      relProdR Q ↾ L ∈ smbar (relProdR Q ʻʻ L) L :=
  fun ⟨hQ, h⟩ => pm74_72 ⟨hQ, fun P hP _ ⟨x, hxy⟩ => h ⟨x, P, hP, hxy⟩⟩

/-- ✱74·741. \(\vdash:Q\in \text{Cls}\rightarrow 1.\text{D}ʻ\dot{s}ʻ\lambda\subset \text{ᗡ}ʻQ.\supset.(Q\mid )\upharpoonright \lambda\in (Q\mid ʻʻ\lambda)\overline{\text{ sm }}\lambda\) -/
theorem pm74_741 {L : Set (β → γ → Prop)} {Q : α → β → Prop} :
    Q ∈ arrow Cls one ∧ dom (sumRel L) ⊆ codom Q →
      relProdL Q ↾ L ∈ smbar (relProdL Q ʻʻ L) L :=
  fun ⟨hQ, h⟩ => pm74_721 ⟨hQ, fun P hP _ ⟨y, hxy⟩ => h ⟨y, P, hP, hxy⟩⟩

/-- ✱74·75. \(\vdash:\alpha\upharpoonleft Q\in 1\rightarrow \text{Cls}.\alpha\subset \text{D}ʻQ.sʻ\text{ᗡ}ʻʻ\lambda\subset \alpha.\supset.(\mid Q)\upharpoonright \lambda\in (\mid Qʻʻ\lambda)\overline{\text{ sm }}\lambda\) -/
theorem pm74_75 {A : Set β} {L : Set (α → β → Prop)} {Q : β → γ → Prop} :
    (A ◁ Q ∈ arrow one Cls ∧ A ⊆ dom Q) ∧ sumCls (Dcnv ʻʻ L) ⊆ A →
      relProdR Q ↾ L ∈ smbar (relProdR Q ʻʻ L) L :=
  fun ⟨⟨hQ, hA⟩, h⟩ => graph_cres_smbar (f := fun P : α → β → Prop => P ⨾ Q)
    fun _ _ hP hP' e => cancelR (S := A)
      (fun y y' z hy hy' h1 h2 => mem_arrow_one_Cls.1 hQ y y' z ⟨⟨hy, h1⟩, ⟨hy', h2⟩⟩) hA
      ((codom_sub_sumCls hP).trans h) ((codom_sub_sumCls hP').trans h) e

/-- ✱74·751. \[\begin{align}&\vdash:Q\upharpoonright \alpha\in \text{Cls}\rightarrow 1.\alpha\subset \text{ᗡ}ʻQ.sʻ\text{D}ʻʻ\lambda\subset \alpha.\supset.(Q\mid )\upharpoonright \lambda\in (Q\mid ʻʻ\lambda)\overline{\text{ sm }}\lambda\\ &[\text{Proof as in *74·75, using *74·731, *43·48·49}]\end{align}\] -/
theorem pm74_751 {A : Set β} {L : Set (β → γ → Prop)} {Q : α → β → Prop} :
    (Q ↾ A ∈ arrow Cls one ∧ A ⊆ codom Q) ∧ sumCls (D ʻʻ L) ⊆ A →
      relProdL Q ↾ L ∈ smbar (relProdL Q ʻʻ L) L :=
  fun ⟨⟨hQ, hA⟩, h⟩ => graph_cres_smbar (f := fun P : β → γ → Prop => Q ⨾ P)
    fun _ _ hP hP' e => cancelL (S := A)
      (fun w y y' hy hy' h1 h2 => mem_arrow_Cls_one.1 hQ w y y' ⟨⟨h1, hy⟩, ⟨h2, hy'⟩⟩) hA
      ((dom_sub_sumCls hP).trans h) ((dom_sub_sumCls hP').trans h) e

private theorem cancel3 {Q : γ → α → Prop} {R : β → δ → Prop} {P P' : α → β → Prop}
    {X : Set α} {Y : Set β}
    (hQ : ∀ w y y', y ∈ X → y' ∈ X → Q w y → Q w y' → y = y') (hX : X ⊆ codom Q)
    (hR : ∀ y y' z, y ∈ Y → y' ∈ Y → R y z → R y' z → y = y') (hY : Y ⊆ dom R)
    (h1 : dom P ⊆ X) (h2 : codom P ⊆ Y) (h1' : dom P' ⊆ X) (h2' : codom P' ⊆ Y)
    (h : Q ⨾ P ⨾ R = Q ⨾ P' ⨾ R) : P = P' := by
  have e : Q ⨾ P = Q ⨾ P' := cancelR hR hY (fun z ⟨_, x, _, hxz⟩ => h2 ⟨x, hxz⟩)
    (fun z ⟨_, x, _, hxz⟩ => h2' ⟨x, hxz⟩) h
  exact cancelL hQ hX h1 h1' e

/-- ✱74·76. \[\begin{align}\vdash: Q \in \text{Cls} &\rightarrow 1.R\in 1 \rightarrow \text{Cls}. Q \mid P \mid R = Q \mid P'\mid R. \supset .\\ &(\text{ᗡ}ʻQ)\upharpoonleft P\upharpoonright \text{D}ʻR = (\text{ᗡ}ʻQ)\upharpoonleft P'\upharpoonright \text{D}ʻR \quad[\text{*74·7·701}]\end{align}\] -/
theorem pm74_76 {Q : γ → α → Prop} {R : β → δ → Prop} {P P' : α → β → Prop} :
    (Q ∈ arrow Cls one ∧ R ∈ arrow one Cls) ∧ Q ⨾ P ⨾ R = Q ⨾ P' ⨾ R →
      codom Q ◁ P ↾ dom R = codom Q ◁ P' ↾ dom R := by
  rintro ⟨⟨hQ, hR⟩, h⟩
  have e : ∀ X : α → β → Prop, Q ⨾ (codom Q ◁ X ↾ dom R) ⨾ R = Q ⨾ X ⨾ R := fun X => by
    funext w v
    apply propext
    constructor
    · rintro ⟨y, ⟨x, h1, ⟨_, h2⟩, _⟩, h3⟩; exact ⟨y, ⟨x, h1, h2⟩, h3⟩
    · rintro ⟨y, ⟨x, h1, h2⟩, h3⟩; exact ⟨y, ⟨x, h1, ⟨⟨w, h1⟩, h2⟩, ⟨v, h3⟩⟩, h3⟩
  refine cancel3 (X := codom Q) (Y := dom R)
    (fun w y y' _ _ h1 h2 => mem_arrow_Cls_one.1 hQ w y y' ⟨h1, h2⟩) le_rfl
    (fun y y' z _ _ h1 h2 => mem_arrow_one_Cls.1 hR y y' z ⟨h1, h2⟩) le_rfl
    (fun x ⟨_, hh⟩ => hh.1.1) (fun y ⟨_, hh⟩ => hh.2) (fun x ⟨_, hh⟩ => hh.1.1)
    (fun y ⟨_, hh⟩ => hh.2) ?_
  rw [e, e, h]

/-- ✱74·761. \[\begin{align}\vdash\colon\ldotp \text{Hp} *74·76.\text{D}ʻP \subset & \text{ᗡ}ʻQ.\text{ᗡ}ʻP \subset \text{D}ʻR. \text{D}ʻP' \subset \text{ᗡ}ʻQ.\text{ᗡ}ʻP'\subset \text{D}ʻR.\supset:\\ & Q\mid P\mid R = Q\mid P'\mid R.\equiv. P = P' [\text{*74·71·711}]\end{align}\]

**Status.** proved (reading): `Hp✱74·76` is read as the hypotheses `Q ∈ Cls → 1 . R ∈ 1 → Cls` of ✱74·76, without its third clause `Q|P|R = Q|P'|R`, which is one side of the `≡` asserted here (the cited ✱74·71·711 do not need it). The literal reading, with that clause assumed as well, follows at once from this one. -/
theorem pm74_761 {Q : γ → α → Prop} {R : β → δ → Prop} {P P' : α → β → Prop} :
    (((((Q ∈ arrow Cls one ∧ R ∈ arrow one Cls) ∧ dom P ⊆ codom Q) ∧ codom P ⊆ dom R) ∧
        dom P' ⊆ codom Q) ∧ codom P' ⊆ dom R) →
      (Q ⨾ P ⨾ R = Q ⨾ P' ⨾ R ↔ P = P') :=
  fun ⟨⟨⟨⟨⟨hQ, hR⟩, h1⟩, h2⟩, h1'⟩, h2'⟩ =>
    ⟨cancel3 (fun w y y' _ _ a b => mem_arrow_Cls_one.1 hQ w y y' ⟨a, b⟩) le_rfl
      (fun y y' z _ _ a b => mem_arrow_one_Cls.1 hR y y' z ⟨a, b⟩) le_rfl h1 h2 h1' h2',
      fun e => e ▸ rfl⟩

private theorem dpar_smbar {Q : γ → α → Prop} {R : β → δ → Prop} {L : Set (α → β → Prop)}
    (hinj : ∀ P P', P ∈ L → P' ∈ L → Q ⨾ P ⨾ R = Q ⨾ P' ⨾ R → P = P') :
    (Q ∥ R) ↾ L ∈ arrow one one ∧ (Q ∥ R) ↾ L ∈ smbar ((Q ∥ R) ʻʻ L) L := by
  have h1 : Q ∥ R ∈ arrow one Cls := mem_arrow_one_Cls.2 fun X Y P ⟨hX, hY⟩ =>
    ((dpar_iff _ _ _ _).1 hX).trans ((dpar_iff _ _ _ _).1 hY).symm
  have h2 : L ⊆ codom (Q ∥ R) := fun P _ => ⟨_, (dpar_iff _ _ _ _).2 rfl⟩
  have h3 : (Q ∥ R) ↾ L ∈ arrow Cls one := mem_arrow_Cls_one.2 fun X P P' ⟨⟨hP, hL⟩, ⟨hP', hL'⟩⟩ => by
    have e1 := (dpar_iff _ _ _ _).1 hP
    have e2 := (dpar_iff _ _ _ _).1 hP'
    rw [← relProd_assoc] at e1 e2
    exact hinj P P' hL hL' (e1.symm.trans e2)
  have hm := (pm73_23 ⟨⟨h1, h2⟩, h3⟩).2
  exact ⟨hm.1.1, hm⟩

/-- ✱74·77. \[\begin{align}\vdash: Q,\,R \in 1 \rightarrow \text{Cls}. sʻ\text{D}ʻʻ\lambda &\subset \text{D}ʻQ. sʻ\text{ᗡ}ʻʻ\lambda \subset \text{D}ʻR. \supset .\\ &(\breve{Q} \Arrowvert R)\upharpoonright \lambda\in 1 \rightarrow 1.(\breve{Q} \Arrowvert R)\upharpoonright \lambda \in \{(\breve{Q}\Arrowvert R)ʻʻ\lambda\} \overline{\text{ sm }} \lambda\end{align}\] -/
theorem pm74_77 {Q : α → γ → Prop} {R : β → δ → Prop} {L : Set (α → β → Prop)} :
    ((Q ∈ arrow one Cls ∧ R ∈ arrow one Cls) ∧ sumCls (D ʻʻ L) ⊆ dom Q) ∧
        sumCls (Dcnv ʻʻ L) ⊆ dom R →
      (Q˘ ∥ R) ↾ L ∈ arrow one one ∧ (Q˘ ∥ R) ↾ L ∈ smbar ((Q˘ ∥ R) ʻʻ L) L :=
  fun ⟨⟨⟨hQ, hR⟩, h1⟩, h2⟩ => dpar_smbar fun _ _ hP hP' e =>
    (pm74_761 (Q := Q˘) ⟨⟨⟨⟨⟨cnv_co.2 hQ, hR⟩, (dom_sub_sumCls hP).trans h1⟩,
      (codom_sub_sumCls hP).trans h2⟩, (dom_sub_sumCls hP').trans h1⟩,
      (codom_sub_sumCls hP').trans h2⟩).1 e

/-- ✱74·771. \[\begin{align}\vdash: Q,\,R \in \text{Cls} \rightarrow 1. sʻ&\text{D}ʻʻ\lambda \subset \text{ᗡ}ʻQ.sʻ\text{ᗡ}ʻʻ\lambda \subset \text{ᗡ}ʻR.\supset.\\ &(Q\Arrowvert \breve{R})\upharpoonright \lambda\in 1\rightarrow 1.(Q\Arrowvert \breve{R})\upharpoonright \lambda\in \{(Q\Arrowvert \breve{R})ʻʻ\lambda\}\overline{\text{ sm }}\lambda\\ \left[\text{*74·77}\, \frac{\breve{Q},\breve{R}}{Q,\,R}\right]\end{align}\] -/
theorem pm74_771 {Q : γ → α → Prop} {R : δ → β → Prop} {L : Set (α → β → Prop)} :
    ((Q ∈ arrow Cls one ∧ R ∈ arrow Cls one) ∧ sumCls (D ʻʻ L) ⊆ codom Q) ∧
        sumCls (Dcnv ʻʻ L) ⊆ codom R →
      (Q ∥ R˘) ↾ L ∈ arrow one one ∧ (Q ∥ R˘) ↾ L ∈ smbar ((Q ∥ R˘) ʻʻ L) L :=
  fun ⟨⟨⟨hQ, hR⟩, h1⟩, h2⟩ => dpar_smbar fun _ _ hP hP' e =>
    (pm74_761 (R := R˘) ⟨⟨⟨⟨⟨hQ, cnv_oc.2 hR⟩, (dom_sub_sumCls hP).trans h1⟩,
      (codom_sub_sumCls hP).trans h2⟩, (dom_sub_sumCls hP').trans h1⟩,
      (codom_sub_sumCls hP').trans h2⟩).1 e

/-- ✱74·772. \[\begin{align}&\vdash\colon\ldotp (x). \text{E}! Qʻx : (y). \text{E}! Rʻy : Q,\,R \in \text{Cls} \rightarrow 1:\supset.Q\Arrowvert \breve{R}\in 1\rightarrow 1\\ &[\text{*74·771. *33·431}]\end{align}\] -/
theorem pm74_772 {Q : γ → α → Prop} {R : δ → β → Prop} :
    ((∀ x, EDesc Q x) ∧ (∀ y, EDesc R y)) ∧ (Q ∈ arrow Cls one ∧ R ∈ arrow Cls one) →
      Q ∥ R˘ ∈ arrow one one := by
  rintro ⟨⟨hEQ, hER⟩, hQ, hR⟩
  have h := (pm74_771 (L := Set.univ) ⟨⟨⟨hQ, hR⟩, codom_of_EDesc hEQ _⟩,
    codom_of_EDesc hER _⟩).1
  exact oo_mono h fun _ _ hh => ⟨hh, trivial⟩

/-- ✱74·773. \[\begin{align}\vdash: Q\upharpoonright \alpha, R\upharpoonright \beta \in \text{Cls} \rightarrow & 1.\alpha \subset \text{ᗡ}ʻQ.\beta \subset \text{ᗡ}ʻR.sʻ\text{D}ʻʻ\lambda \subset \alpha.sʻ\text{ᗡ}ʻʻ\lambda \subset \beta.\supset.\\ &(Q\Arrowvert \breve{R})\upharpoonright \lambda \in 1 \rightarrow 1. (Q\Arrowvert \breve{R})\upharpoonright \lambda \in \{(Q\Arrowvert \breve{R})ʻʻ\lambda\} \overline{\text{ sm }} \lambda\end{align}\] -/
theorem pm74_773 {Q : γ → α → Prop} {R : δ → β → Prop} {A : Set α} {B : Set β}
    {L : Set (α → β → Prop)} :
    ((((Q ↾ A ∈ arrow Cls one ∧ R ↾ B ∈ arrow Cls one) ∧ A ⊆ codom Q) ∧ B ⊆ codom R) ∧
        sumCls (D ʻʻ L) ⊆ A) ∧ sumCls (Dcnv ʻʻ L) ⊆ B →
      (Q ∥ R˘) ↾ L ∈ arrow one one ∧ (Q ∥ R˘) ↾ L ∈ smbar ((Q ∥ R˘) ʻʻ L) L :=
  fun ⟨⟨⟨⟨⟨hQ, hR⟩, hA⟩, hB⟩, h1⟩, h2⟩ => dpar_smbar fun _ _ hP hP' e =>
    cancel3 (X := A) (Y := B)
      (fun w y y' hy hy' a b => mem_arrow_Cls_one.1 hQ w y y' ⟨⟨a, hy⟩, ⟨b, hy'⟩⟩) hA
      (fun y y' z hy hy' a b => mem_arrow_Cls_one.1 hR z y y' ⟨⟨a, hy⟩, ⟨b, hy'⟩⟩) hB
      ((dom_sub_sumCls hP).trans h1) ((codom_sub_sumCls hP).trans h2)
      ((dom_sub_sumCls hP').trans h1) ((codom_sub_sumCls hP').trans h2) e

/-- ✱74·774. \(\vdash\colon\ldotp R \in \text{Cls} \rightarrow 1 : (y). \text{E}! Rʻy : \supset . \mid \breve{R} \in 1 \rightarrow 1\) -/
theorem pm74_774 {R : γ → β → Prop} :
    R ∈ arrow Cls one ∧ (∀ y, EDesc R y) → relProdR (α := α) R˘ ∈ arrow one one := by
  rintro ⟨hR, hE⟩
  refine oo_iff'.2 ⟨graph_oc (fun P : α → β → Prop => P ⨾ R˘),
    mem_arrow_Cls_one.2 fun X P P' ⟨h1, h2⟩ => ?_⟩
  exact cancelR (S := Set.univ)
    (fun y y' z _ _ a b => mem_arrow_Cls_one.1 hR z y y' ⟨a, b⟩) (codom_of_EDesc hE _)
    (fun _ _ => trivial) (fun _ _ => trivial) ((h1 : X = P ⨾ R˘).symm.trans h2)

/-- ✱74·775. \[\begin{align}\vdash:Q\upharpoonright sʻ\text{D}ʻʻ&\lambda,R\upharpoonright sʻ\text{ᗡ}ʻʻ\lambda\in \text{Cls}\rightarrow 1.sʻ\text{D}ʻʻ\lambda\subset \text{ᗡ}ʻQ.sʻ\text{ᗡ}ʻʻ\lambda\subset \text{ᗡ}ʻR.\supset.\\ &(Q\Arrowvert \breve{R})\upharpoonright \lambda\in 1\rightarrow 1.(Q\Arrowvert \breve{R})\upharpoonright \lambda\in {(Q\Arrowvert \breve{R})ʻʻ\lambda}\overline{\text{ sm }}\lambda \quad[\text{*74·773}]\end{align}\] -/
theorem pm74_775 {Q : γ → α → Prop} {R : δ → β → Prop} {L : Set (α → β → Prop)} :
    ((Q ↾ sumCls (D ʻʻ L) ∈ arrow Cls one ∧ R ↾ sumCls (Dcnv ʻʻ L) ∈ arrow Cls one) ∧
        sumCls (D ʻʻ L) ⊆ codom Q) ∧ sumCls (Dcnv ʻʻ L) ⊆ codom R →
      (Q ∥ R˘) ↾ L ∈ arrow one one ∧ (Q ∥ R˘) ↾ L ∈ smbar ((Q ∥ R˘) ʻʻ L) L :=
  fun ⟨⟨⟨hQ, hR⟩, hA⟩, hB⟩ => pm74_773 ⟨⟨⟨⟨⟨hQ, hR⟩, hA⟩, hB⟩, le_rfl⟩, le_rfl⟩

/-- ✱74·8. \(\vdash:R\upharpoonright (\beta\cup \gamma)\in 1\rightarrow \text{Cls}.\equiv.R\upharpoonright \beta,R\upharpoonright \gamma\in 1\rightarrow \text{Cls}\) -/
theorem pm74_8 {R : α → β → Prop} {B G : Set β} :
    R ↾ (B ∪ G) ∈ arrow one Cls ↔ R ↾ B ∈ arrow one Cls ∧ R ↾ G ∈ arrow one Cls := by
  constructor
  · intro h
    exact ⟨oc_mono h fun _ _ hh => ⟨hh.1, Or.inl hh.2⟩, oc_mono h fun _ _ hh => ⟨hh.1, Or.inr hh.2⟩⟩
  · rintro ⟨h1, h2⟩
    refine mem_arrow_one_Cls.2 fun x y z ⟨⟨hx, hz⟩, ⟨hy, _⟩⟩ => ?_
    rcases hz with hz | hz
    · exact mem_arrow_one_Cls.1 h1 x y z ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩
    · exact mem_arrow_one_Cls.1 h2 x y z ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩

/-- ✱74·801. \(\vdash:(\beta\cup \gamma)\upharpoonleft R\in \text{Cls}\rightarrow 1.\equiv.\beta\upharpoonleft R,\gamma\upharpoonleft R\in \text{Cls}\rightarrow 1\) -/
theorem pm74_801 {R : α → β → Prop} {B G : Set α} :
    (B ∪ G) ◁ R ∈ arrow Cls one ↔ B ◁ R ∈ arrow Cls one ∧ G ◁ R ∈ arrow Cls one := by
  rw [← cnv_oc, ← cnv_oc (R := B ◁ R), ← cnv_oc (R := G ◁ R), cnv_dres, cnv_dres, cnv_dres]
  exact pm74_8

/-- ✱74·81. \(\vdash:R\upharpoonright sʻ\kappa\in 1\rightarrow \text{Cls}.\equiv.R\upharpoonright ʻʻ\kappa\subset 1\rightarrow \text{Cls}\) -/
theorem pm74_81 {R : α → β → Prop} {K : Set (Set β)} :
    R ↾ sumCls K ∈ arrow one Cls ↔ opL cres R ʻʻ K ⊆ arrow one Cls := by
  constructor
  · rintro h X ⟨B, hB, hX⟩
    rw [show X = R ↾ B from hX]
    exact oc_mono h fun _ _ hh => ⟨hh.1, B, hB, hh.2⟩
  · intro h
    refine mem_arrow_one_Cls.2 fun x y z ⟨⟨hx, B, hB, hz⟩, ⟨hy, _⟩⟩ => ?_
    exact mem_arrow_one_Cls.1 (h ⟨B, hB, rfl⟩) x y z ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩

/-- ✱74·811. \(\vdash:(sʻ\kappa)\upharpoonleft R\in \text{Cls}\rightarrow 1.\equiv.\upharpoonleft Rʻʻ\kappa\subset \text{Cls}\rightarrow 1\) -/
theorem pm74_811 {R : α → β → Prop} {K : Set (Set α)} :
    sumCls K ◁ R ∈ arrow Cls one ↔ opR dres R ʻʻ K ⊆ arrow Cls one := by
  constructor
  · rintro h X ⟨A, hA, hX⟩
    rw [show X = A ◁ R from hX]
    exact co_mono h fun _ _ hh => ⟨⟨A, hA, hh.1⟩, hh.2⟩
  · intro h
    refine mem_arrow_Cls_one.2 fun x y z ⟨⟨⟨A, hA, hx⟩, hy⟩, ⟨_, hz⟩⟩ => ?_
    exact mem_arrow_Cls_one.1 (h ⟨A, hA, rfl⟩) x y z ⟨⟨hx, hy⟩, ⟨hx, hz⟩⟩

/-- ✱74·82. \(\vdash:(\beta\cup \gamma)\upharpoonleft R\in 1\rightarrow \text{Cls}.\equiv.\beta\upharpoonleft R,\gamma\upharpoonleft R\in 1\rightarrow \text{Cls}.\breve{R}ʻʻ(\beta-\gamma)\cap \breve{R}ʻʻ\gamma=\Lambda\) -/
theorem pm74_82 {R : α → β → Prop} {B G : Set α} :
    (B ∪ G) ◁ R ∈ arrow one Cls ↔
      (B ◁ R ∈ arrow one Cls ∧ G ◁ R ∈ arrow one Cls) ∧ R˘ ʻʻ (B \ G) ∩ R˘ ʻʻ G = Λ := by
  constructor
  · intro h
    refine ⟨⟨oc_mono h fun _ _ hh => ⟨Or.inl hh.1, hh.2⟩,
      oc_mono h fun _ _ hh => ⟨Or.inr hh.1, hh.2⟩⟩, disj_iff.2 ?_⟩
    rintro z ⟨x, ⟨hxB, hxG⟩, hxz⟩ ⟨y, hyG, hyz⟩
    have e := mem_arrow_one_Cls.1 h x y z ⟨⟨Or.inl hxB, hxz⟩, ⟨Or.inr hyG, hyz⟩⟩
    exact hxG (e ▸ hyG)
  · rintro ⟨⟨h1, h2⟩, hd⟩
    have key : ∀ x y z, x ∈ B → y ∈ G → R x z → R y z → x = y := by
      intro x y z hx hy hxz hyz
      by_cases hxG : x ∈ G
      · exact mem_arrow_one_Cls.1 h2 x y z ⟨⟨hxG, hxz⟩, ⟨hy, hyz⟩⟩
      · exact (disj hd ⟨x, ⟨hx, hxG⟩, hxz⟩ ⟨y, hy, hyz⟩).elim
    refine mem_arrow_one_Cls.2 fun x y z ⟨⟨hx, hxz⟩, ⟨hy, hyz⟩⟩ => ?_
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact mem_arrow_one_Cls.1 h1 x y z ⟨⟨hx, hxz⟩, ⟨hy, hyz⟩⟩
    · exact key x y z hx hy hxz hyz
    · exact (key y x z hy hx hyz hxz).symm
    · exact mem_arrow_one_Cls.1 h2 x y z ⟨⟨hx, hxz⟩, ⟨hy, hyz⟩⟩

/-- ✱74·821. \[\begin{align}\vdash:R\upharpoonright (\beta\cup \gamma)\in \text{Cls}\rightarrow 1.&\equiv.\\ & R\upharpoonright \beta,R\upharpoonright \gamma\in \text{Cls}\rightarrow 1.Rʻʻ(\beta-\gamma)\cap Rʻʻ\gamma=\Lambda\end{align}\] -/
theorem pm74_821 {R : α → β → Prop} {B G : Set β} :
    R ↾ (B ∪ G) ∈ arrow Cls one ↔
      (R ↾ B ∈ arrow Cls one ∧ R ↾ G ∈ arrow Cls one) ∧ R ʻʻ (B \ G) ∩ R ʻʻ G = Λ := by
  rw [← cnv_oc, ← cnv_oc (R := R ↾ B), ← cnv_oc (R := R ↾ G), cnv_cres, cnv_cres, cnv_cres]
  exact pm74_82 (R := R˘)

/-- ✱74·822. \[\begin{align}&\vdash:(\beta\cup \gamma)\upharpoonleft R\in 1\rightarrow 1.\equiv.\beta\upharpoonleft R,\,\gamma\upharpoonleft R\in 1\rightarrow 1.\breve{R}ʻʻ(\beta-\gamma)\cap \breve{R}ʻʻ\gamma=\Lambda\\ &[\text{*74·82·801}]\end{align}\] -/
theorem pm74_822 {R : α → β → Prop} {B G : Set α} :
    (B ∪ G) ◁ R ∈ arrow one one ↔
      (B ◁ R ∈ arrow one one ∧ G ◁ R ∈ arrow one one) ∧ R˘ ʻʻ (B \ G) ∩ R˘ ʻʻ G = Λ := by
  rw [oo_iff', oo_iff', oo_iff', pm74_82, pm74_801]
  tauto

/-- ✱74·823. \[\begin{align}&\vdash:R\upharpoonright (\beta\cup \gamma)\in 1\rightarrow 1.\equiv.R\upharpoonright \beta,\,R\upharpoonright \gamma\in 1\rightarrow 1.Rʻʻ(\beta-\gamma)\cap Rʻʻ\gamma=\Lambda\\ &[\text{*74·8·821}]\end{align}\] -/
theorem pm74_823 {R : α → β → Prop} {B G : Set β} :
    R ↾ (B ∪ G) ∈ arrow one one ↔
      (R ↾ B ∈ arrow one one ∧ R ↾ G ∈ arrow one one) ∧ R ʻʻ (B \ G) ∩ R ʻʻ G = Λ := by
  rw [oo_iff', oo_iff', oo_iff', pm74_8, pm74_821]
  tauto

/-- ✱74·83. \[\begin{align}&\vdash\colon\ldotp \breve{R}ʻʻ\beta\cap \breve{R}ʻʻ\gamma=\Lambda.\supset:(\beta\cup \gamma)\upharpoonleft R\in 1\rightarrow \text{Cls}.\equiv.\beta\upharpoonleft R,\gamma\upharpoonleft R\in 1\rightarrow \text{Cls}\\ &[\text{*74·82}]\end{align}\] -/
theorem pm74_83 {R : α → β → Prop} {B G : Set α} :
    R˘ ʻʻ B ∩ R˘ ʻʻ G = Λ →
      ((B ∪ G) ◁ R ∈ arrow one Cls ↔ B ◁ R ∈ arrow one Cls ∧ G ◁ R ∈ arrow one Cls) := by
  intro h
  rw [pm74_82]
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, disj_iff.2 fun z ⟨x, hx, hxz⟩ hz => ?_⟩⟩
  exact disj h ⟨x, hx.1, hxz⟩ hz

/-- ✱74·831. \(\vdash\colon\ldotp Rʻʻ\beta\cap Rʻʻ\gamma=\Lambda.\supset:R\upharpoonright (\beta\cup \gamma)\in \text{Cls}\rightarrow 1.\equiv.R\upharpoonright \beta,R\upharpoonright \gamma\in \text{Cls}\rightarrow 1\) -/
theorem pm74_831 {R : α → β → Prop} {B G : Set β} :
    R ʻʻ B ∩ R ʻʻ G = Λ →
      (R ↾ (B ∪ G) ∈ arrow Cls one ↔ R ↾ B ∈ arrow Cls one ∧ R ↾ G ∈ arrow Cls one) := by
  intro h
  rw [pm74_821]
  refine ⟨fun hh => hh.1, fun hh => ⟨hh, disj_iff.2 fun z ⟨x, hx, hxz⟩ hz => ?_⟩⟩
  exact disj h ⟨x, hx.1, hxz⟩ hz

/-- ✱74·832. \[\begin{align}&\vdash\colon\ldotp \breve{R}ʻʻ\beta\cap \breve{R}ʻʻ\gamma=\Lambda.\supset:(\beta\cup \gamma)\upharpoonleft R\in 1\rightarrow 1.\equiv.\beta\upharpoonleft R,\gamma\upharpoonleft R\in 1\rightarrow 1\\ &[\text{*74·83·801}]\end{align}\] -/
theorem pm74_832 {R : α → β → Prop} {B G : Set α} :
    R˘ ʻʻ B ∩ R˘ ʻʻ G = Λ →
      ((B ∪ G) ◁ R ∈ arrow one one ↔ B ◁ R ∈ arrow one one ∧ G ◁ R ∈ arrow one one) := by
  intro h
  rw [oo_iff', oo_iff', oo_iff', pm74_83 h, pm74_801]
  tauto

/-- ✱74·833. \[\begin{align}&\vdash\colon\ldotp Rʻʻ\beta\cap Rʻʻ\gamma=\Lambda.\supset:R\upharpoonright (\beta\cup \gamma)\in 1\rightarrow 1.\equiv.R\upharpoonright \beta,R\upharpoonright \gamma\in 1\rightarrow 1\\ &[\text{*74·8·831}]\end{align}\] -/
theorem pm74_833 {R : α → β → Prop} {B G : Set β} :
    R ʻʻ B ∩ R ʻʻ G = Λ →
      (R ↾ (B ∪ G) ∈ arrow one one ↔ R ↾ B ∈ arrow one one ∧ R ↾ G ∈ arrow one one) := by
  intro h
  rw [oo_iff', oo_iff', oo_iff', pm74_8, pm74_831 h]
  tauto

/-- ✱74·84. \[\begin{align}\vdash\colon\ldotp (sʻ\kappa)\upharpoonleft R\in 1&\rightarrow \text{Cls}.\equiv:\\ &\upharpoonleft Rʻʻ\kappa\subset 1\rightarrow \text{Cls}:\beta,\gamma\in \kappa.\supset_{\beta,\gamma}.\breve{R}ʻʻ(\beta-\gamma)\cap \breve{R}ʻʻ\gamma=\Lambda\end{align}\] -/
theorem pm74_84 {R : α → β → Prop} {K : Set (Set α)} :
    sumCls K ◁ R ∈ arrow one Cls ↔
      opR dres R ʻʻ K ⊆ arrow one Cls ∧
        ∀ B G, B ∈ K ∧ G ∈ K → R˘ ʻʻ (B \ G) ∩ R˘ ʻʻ G = Λ := by
  constructor
  · intro h
    refine ⟨?_, fun B G ⟨hB, hG⟩ => disj_iff.2 ?_⟩
    · rintro X ⟨A, hA, hX⟩
      rw [show X = A ◁ R from hX]
      exact oc_mono h fun _ _ hh => ⟨⟨A, hA, hh.1⟩, hh.2⟩
    · rintro z ⟨x, ⟨hxB, hxG⟩, hxz⟩ ⟨y, hyG, hyz⟩
      have e := mem_arrow_one_Cls.1 h x y z ⟨⟨⟨B, hB, hxB⟩, hxz⟩, ⟨⟨G, hG, hyG⟩, hyz⟩⟩
      exact hxG (e ▸ hyG)
  · rintro ⟨h1, h2⟩
    refine mem_arrow_one_Cls.2 fun x y z ⟨⟨⟨B, hB, hx⟩, hxz⟩, ⟨⟨G, hG, hy⟩, hyz⟩⟩ => ?_
    by_cases hxG : x ∈ G
    · exact mem_arrow_one_Cls.1 (h1 ⟨G, hG, rfl⟩) x y z ⟨⟨hxG, hxz⟩, ⟨hy, hyz⟩⟩
    · exact (disj (h2 B G ⟨hB, hG⟩) ⟨x, ⟨hx, hxG⟩, hxz⟩ ⟨y, hy, hyz⟩).elim

/-- ✱74·841. \[\begin{align}\vdash\colon\ldotp R\upharpoonright sʻ\kappa\in \text{Cls}&\rightarrow 1.\equiv:\\ &R\upharpoonright ʻʻ\kappa\subset \text{Cls}\rightarrow 1:\beta,\gamma\in \kappa.\supset_{\beta,\gamma}.Rʻʻ(\beta-\gamma)\cap Rʻʻ\gamma=\Lambda\end{align}\] -/
theorem pm74_841 {R : α → β → Prop} {K : Set (Set β)} :
    R ↾ sumCls K ∈ arrow Cls one ↔
      opL cres R ʻʻ K ⊆ arrow Cls one ∧
        ∀ B G, B ∈ K ∧ G ∈ K → R ʻʻ (B \ G) ∩ R ʻʻ G = Λ := by
  constructor
  · intro h
    refine ⟨?_, fun B G ⟨hB, hG⟩ => disj_iff.2 ?_⟩
    · rintro X ⟨A, hA, hX⟩
      rw [show X = R ↾ A from hX]
      exact co_mono h fun _ _ hh => ⟨hh.1, A, hA, hh.2⟩
    · rintro x ⟨y, ⟨hyB, hyG⟩, hxy⟩ ⟨z, hzG, hxz⟩
      have e := mem_arrow_Cls_one.1 h x y z ⟨⟨hxy, B, hB, hyB⟩, ⟨hxz, G, hG, hzG⟩⟩
      exact hyG (e ▸ hzG)
  · rintro ⟨h1, h2⟩
    refine mem_arrow_Cls_one.2 fun x y z ⟨⟨hxy, B, hB, hy⟩, ⟨hxz, G, hG, hz⟩⟩ => ?_
    by_cases hyG : y ∈ G
    · exact mem_arrow_Cls_one.1 (h1 ⟨G, hG, rfl⟩) x y z ⟨⟨hxy, hyG⟩, ⟨hxz, hz⟩⟩
    · exact (disj (h2 B G ⟨hB, hG⟩) ⟨y, ⟨hy, hyG⟩, hxy⟩ ⟨z, hz, hxz⟩).elim

/-- ✱74·842. \[\begin{align}\vdash&\colon\ldotp (sʻ\kappa)\upharpoonleft R\in 1\rightarrow 1.\equiv:\\ &\upharpoonleft Rʻʻ\kappa\subset 1\rightarrow 1:\beta,\gamma\in \kappa.\supset_{\beta,\gamma}.\breve{R}ʻʻ(\beta-\gamma)\cap \breve{R}ʻʻ\gamma=\Lambda \quad[\text{*74·84·811}]\end{align}\] -/
theorem pm74_842 {R : α → β → Prop} {K : Set (Set α)} :
    sumCls K ◁ R ∈ arrow one one ↔
      opR dres R ʻʻ K ⊆ arrow one one ∧
        ∀ B G, B ∈ K ∧ G ∈ K → R˘ ʻʻ (B \ G) ∩ R˘ ʻʻ G = Λ := by
  rw [oo_iff', pm74_84, pm74_811]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun X hX => oo_iff'.2 ⟨h1 hX, h3 hX⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun X hX => (oo_iff'.1 (h1 hX)).1, h2⟩, fun X hX => (oo_iff'.1 (h1 hX)).2⟩

/-- ✱74·843. \[\begin{align}\vdash&\colon\ldotp R\upharpoonright sʻ\kappa\in 1\rightarrow 1.\equiv:\\ &R\upharpoonright ʻʻ\kappa\subset 1\rightarrow 1:\beta,\gamma\in \kappa.\supset_{\beta,\gamma}.Rʻʻ(\beta-\gamma)\cap Rʻʻ\gamma=\Lambda \quad[\text{*74·81·841}]\end{align}\] -/
theorem pm74_843 {R : α → β → Prop} {K : Set (Set β)} :
    R ↾ sumCls K ∈ arrow one one ↔
      opL cres R ʻʻ K ⊆ arrow one one ∧
        ∀ B G, B ∈ K ∧ G ∈ K → R ʻʻ (B \ G) ∩ R ʻʻ G = Λ := by
  rw [oo_iff', pm74_841, pm74_81]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun X hX => oo_iff'.2 ⟨h1 hX, h2 hX⟩, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun X hX => (oo_iff'.1 (h1 hX)).1, fun X hX => (oo_iff'.1 (h1 hX)).2, h2⟩

end PrincipiaMathematica
