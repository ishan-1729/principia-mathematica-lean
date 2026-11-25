import PrincipiaMathematica.Defs.Part5

/-!
# Part V, Section B: On sections, segments, stretches, and derivatives

Volume 2. Numbers: ✱213, ✱214, ✱215, ✱216, ✱217.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w

/-!
## [✱213] Sectional relations

*(Vol. 2, p. 668)*

> *Summary of* *213.
>
> …

**Lean reading.** `P_ς` is `Psec P` (Defs/Part5): `P⥏;{(ς'P_*)⥏(−ι'Λ)}`, the
sectional relations `P ⥏ α` of the non-null sections, ordered as the sections are by `ς'P_*`. The
series of non-null sections `(ς'P_*)⥏(−ι'Λ)` is written out as `segSer (anc P) ⥏ (ι Λ)ᶜ`; the
key facts are that `α (ς'P_*) β` holds for sections with `∃!β − α` (`mem_dom_imgRel_anc`), that
sections are nested when `P_po` is connected, and that `P⥏` is one-one on non-null sections when
`P_po` is serial. `B'R` is `Desc Beg R ψ`, `B⃗'R` is `refs Beg R`; `ι''B⃗'P` is `iota ʻʻ refs Beg P`;
`P⥏''κ` is `opL fres P ʻʻ κ`; `P⤉;Q` is `opL rsum P ⁏ Q`, `(C'P ∪)''κ` is `opL (· ∪ ·) (fld P) ʻʻ κ`;
`P ⤉ Q⥏γ` is `P ⤉ (Q ⥏ γ)`. Hypotheses are kept as printed (`P_po ∈ Ser`, `P_po ⊂̇ J`, …) as
left-nested conjunctions. ✱213·122–·124, ✱213·163 and ✱213·561 (`⥏` for `↾`) correct e-text
misprints. ✱213·172 is proved by carrying sections along a correlator of `P` with `Q` (no
seriality is needed). The relation-number propositions ✱213·17, ·171, ·57, ·58 use the relation
arithmetic of ✱150–✱181 (likeness through correlators, `x ⇷ P`, `P ⇸ x`, `x ⇷̇ P`, `P ⇸̇ x`,
`P + Q`, re-proved here): `ς'P_* = Λ ⇷ (ς'P_*)⥏(−ι'Λ)` (the null section begins `ς'P_*`), and the
four cases of ✱213·56 for `(P ⤉ Q)_ς`.

**Status.** proved; ✱213·01 definition; ✱213·122, ·123, ·124, ·163, ·561 proved (reading)
(transcription errors); ✱213·17 proved (reading) (`[Nonempty β]` for the type of the apparent `x`
of `1̇ +̇ μ`, Introduction, Ch. I).
-/

section B2Helpers

variable {α : Type u} {β : Type v}

private theorem b2_mem_iota {X Y : α} : X ∈ ι Y ↔ X = Y := Iff.rfl

private theorem b2_mem_iotaNull {A : Set α} : A ∈ ι (Λ : Set α) ↔ A = ∅ := by
  rw [b2_mem_iota, Null_eq_empty]

private theorem b2_not_mem_iotaNull {A : Set α} : A ∉ ι (Λ : Set α) ↔ A.Nonempty := by
  rw [b2_mem_iotaNull, Set.nonempty_iff_ne_empty]

private theorem b2_mem_diff_iotaNull {A : Set α} {K : Set (Set α)} :
    A ∈ K \ ι (Λ : Set α) ↔ A ∈ K ∧ A.Nonempty := by
  rw [Set.mem_sdiff, b2_not_mem_iotaNull]

private theorem b2_mem_one {A : Set α} : A ∈ (one : Set (Set α)) ↔ ∃ x, A = ι x := Iff.rfl

private theorem b2_mem_iota_img {A : Set α} {B : Set α} : A ∈ iota ʻʻ B ↔ ∃ b, b ∈ B ∧ A = ι b :=
  Iff.rfl

private theorem b2_eq_rNull {R : α → β → Prop} : R = rNull ↔ ∀ x y, ¬R x y := by
  constructor
  · rintro rfl x y h; exact h ⟨rfl, rfl⟩
  · intro h; funext x y; apply propext
    exact ⟨fun h' => absurd h' (h x y), fun h' => absurd ⟨rfl, rfl⟩ h'⟩

private theorem b2_rEx_iff_ne {R : α → β → Prop} : rEx R ↔ R ≠ rNull := by
  rw [Ne, b2_eq_rNull]; simp [rEx]

private theorem b2_Null_eq {A : Set α} : A = Λ ↔ A = ∅ := by rw [Null_eq_empty]

private theorem b2_refs_Beg {P : α → α → Prop} {x : α} :
    x ∈ refs Beg P ↔ x ∈ dom P ∧ x ∉ codom P := Iff.rfl

private theorem b2_fres_apply {P : α → α → Prop} {A : Set α} {x y : α} :
    (P ⥏ A) x y ↔ (x ∈ A ∧ P x y) ∧ y ∈ A := Iff.rfl

private theorem b2_mem_opL_fres_img {P : α → α → Prop} {K : Set (Set α)} {Q : α → α → Prop} :
    Q ∈ opL fres P ʻʻ K ↔ ∃ A, A ∈ K ∧ Q = P ⥏ A := Iff.rfl

/-! Transitive closure, ancestral, fields. -/

private theorem b2_po_of {P : α → α → Prop} {x y : α} (h : P x y) : po P x y :=
  po_iff_transGen.2 (Relation.TransGen.single h)

private theorem b2_po_trans {P : α → α → Prop} {x y z : α} (h1 : po P x y) (h2 : po P y z) : po P x z :=
  po_iff_transGen.2 ((po_iff_transGen.1 h1).trans (po_iff_transGen.1 h2))

private theorem b2_fld_of_po {P : α → α → Prop} {x y : α} (h : po P x y) : x ∈ fld P ∧ y ∈ fld P := by
  rw [po_iff_transGen] at h
  constructor
  · obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 h
    exact ⟨c, Or.inl hc⟩
  · obtain ⟨c, -, hc⟩ := Relation.TransGen.tail'_iff.1 h
    exact ⟨c, Or.inr hc⟩

private theorem b2_fld_of_anc {P : α → α → Prop} {x y : α} (h : anc P x y) : x ∈ fld P ∧ y ∈ fld P := by
  rcases anc_iff_po.1 h with ⟨rfl, hx⟩ | h
  · exact ⟨hx, hx⟩
  · exact b2_fld_of_po h

private theorem b2_anc_refl {P : α → α → Prop} {x : α} (hx : x ∈ fld P) : anc P x x :=
  anc_iff_po.2 (Or.inl ⟨rfl, hx⟩)

private theorem b2_anc_of_po {P : α → α → Prop} {x y : α} (h : po P x y) : anc P x y :=
  anc_iff_po.2 (Or.inr h)

private theorem b2_anc_trans {P : α → α → Prop} {x y z : α} (h1 : anc P x y) (h2 : anc P y z) :
    anc P x z := by
  rw [anc_iff_reflTransGen] at *
  exact ⟨h1.1, h1.2.trans h2.2⟩

private theorem b2_po_of_anc_po {P : α → α → Prop} {x y z : α} (h1 : anc P x y) (h2 : po P y z) :
    po P x z := by
  rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h
  · exact h2
  · exact b2_po_trans h h2

private theorem b2_po_of_po_anc {P : α → α → Prop} {x y z : α} (h1 : po P x y) (h2 : anc P y z) :
    po P x z := by
  rcases anc_iff_po.1 h2 with ⟨rfl, -⟩ | h
  · exact h1
  · exact b2_po_trans h1 h

private theorem b2_fld_po (P : α → α → Prop) : fld (po P) = fld P := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact (b2_fld_of_po h).1
    · exact (b2_fld_of_po h).2
  · rintro ⟨y, h | h⟩
    · exact ⟨y, Or.inl (b2_po_of h)⟩
    · exact ⟨y, Or.inr (b2_po_of h)⟩

private theorem b2_fld_anc (P : α → α → Prop) : fld (anc P) = fld P := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact (b2_fld_of_anc h).1
    · exact (b2_fld_of_anc h).2
  · intro hx; exact ⟨x, Or.inl (b2_anc_refl hx)⟩

/-- `P_po` from a step and an ancestral. -/
private theorem b2_po_of_P_anc {P : α → α → Prop} {x y z : α} (h1 : P x y) (h2 : anc P y z) :
    po P x z := b2_po_of_po_anc (b2_po_of h1) h2

/-- First step of a `P_po`-chain. -/
private theorem b2_po_head {P : α → α → Prop} {x z : α} (h : po P x z) :
    ∃ y, P x y ∧ anc P y z := by
  rw [po_iff_transGen] at h
  obtain ⟨y, hxy, hyz⟩ := Relation.TransGen.head'_iff.1 h
  exact ⟨y, hxy, anc_iff_reflTransGen.2 ⟨⟨x, Or.inr hxy⟩, hyz⟩⟩

/-- Last step of a `P_po`-chain. -/
private theorem b2_po_tail {P : α → α → Prop} {x z : α} (h : po P x z) :
    ∃ y, anc P x y ∧ P y z := by
  have hx := (b2_fld_of_po h).1
  rw [po_iff_transGen] at h
  obtain ⟨y, hxy, hyz⟩ := Relation.TransGen.tail'_iff.1 h
  exact ⟨y, anc_iff_reflTransGen.2 ⟨hx, hxy⟩, hyz⟩

/-! Sections. -/

private theorem b2_sect_sub {P : α → α → Prop} {A : Set α} (hA : A ∈ sect P) : A ⊆ fld P := hA.1

private theorem b2_sect_P {P : α → α → Prop} {A : Set α} (hA : A ∈ sect P) {x y : α} (h : P x y)
    (hy : y ∈ A) : x ∈ A := (mem_sect.1 hA).2 x y ⟨h, hy⟩

private theorem b2_sect_po {P : α → α → Prop} {A : Set α} (hA : A ∈ sect P) {x y : α} (h : po P x y)
    (hy : y ∈ A) : x ∈ A := by
  rw [po_iff_transGen] at h
  induction h using Relation.TransGen.head_induction_on with
  | single h => exact b2_sect_P hA h hy
  | head h _ ih => exact b2_sect_P hA h ih

private theorem b2_sect_anc {P : α → α → Prop} {A : Set α} (hA : A ∈ sect P) {x y : α} (h : anc P x y)
    (hy : y ∈ A) : x ∈ A := by
  rcases anc_iff_po.1 h with ⟨rfl, -⟩ | h
  · exact hy
  · exact b2_sect_po hA h hy

private theorem b2_fld_mem_sect (P : α → α → Prop) : fld P ∈ sect P :=
  ⟨fun _ h => h, fun x ⟨y, _, h⟩ => ⟨y, Or.inl h⟩⟩

private theorem b2_empty_mem_sect (P : α → α → Prop) : (∅ : Set α) ∈ sect P :=
  ⟨Set.empty_subset _, fun _ ⟨_, h, _⟩ => h⟩

private theorem b2_refs_anc_mem_sect (P : α → α → Prop) (x : α) : refs (anc P) x ∈ sect P := by
  refine ⟨fun z h => (b2_fld_of_anc h).1, ?_⟩
  rintro z ⟨y, hy, hzy⟩
  exact b2_anc_trans (b2_anc_of_po (b2_po_of hzy)) hy

private theorem b2_sect_ne_fld {P : α → α → Prop} {A : Set α} (hA : A ∈ sect P) :
    A ≠ fld P ↔ (fld P \ A).Nonempty := by
  constructor
  · intro h
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hn
    exact h (Set.Subset.antisymm hA.1 hn)
  · rintro ⟨z, hz, hzA⟩ rfl; exact hzA hz

/-- `α (ς'P_*) β . ≡ . α, β ∈ sect'P . ∃!β − α`. -/
private theorem b2_Plc_anc {P : α → α → Prop} {A B : Set α} (hA : A ∈ sect P) (hB : B ∈ sect P) :
    Plc (anc P) A B ↔ (B \ A).Nonempty := by
  show ((B ∈ cl (fld (anc P)˘) ∧ A ∈ cl (fld (anc P)˘)) ∧
    ((B \ A) \ (anc P)˘˘ ʻʻ (A \ B)).Nonempty) ↔ _
  rw [fld_cnv, b2_fld_anc]
  constructor
  · rintro ⟨-, z, ⟨hzB, hzA⟩, -⟩; exact ⟨z, hzB, hzA⟩
  · rintro ⟨z, hzB, hzA⟩
    refine ⟨⟨hB.1, hA.1⟩, z, ⟨hzB, hzA⟩, ?_⟩
    rintro ⟨y, ⟨hyA, -⟩, hzy⟩
    exact hzA (b2_sect_anc hA hzy hyA)

private theorem b2_segSer_anc {P : α → α → Prop} {A B : Set α} :
    segSer (anc P) A B ↔ (A ∈ sect P ∧ B ∈ sect P) ∧ (B \ A).Nonempty := by
  rw [segSer_apply, mem_dom_imgRel_anc, mem_dom_imgRel_anc]
  constructor
  · rintro ⟨⟨hA, h⟩, hB⟩; exact ⟨⟨hA, hB⟩, (b2_Plc_anc hA hB).1 h⟩
  · rintro ⟨⟨hA, hB⟩, h⟩; exact ⟨⟨hA, (b2_Plc_anc hA hB).2 h⟩, hB⟩

/-- The series of non-null sections `(ς'P_*) ⥏ (−ι'Λ)`. -/
private theorem b2_S0 {P : α → α → Prop} {A B : Set α} :
    (segSer (anc P) ⥏ (ι Λ)ᶜ) A B ↔
      ((A ∈ sect P ∧ A.Nonempty) ∧ (B ∈ sect P ∧ B.Nonempty)) ∧ (B \ A).Nonempty := by
  show ((A ∈ (ι Λ)ᶜ ∧ segSer (anc P) A B) ∧ B ∈ (ι Λ)ᶜ) ↔ _
  rw [Set.mem_compl_iff, Set.mem_compl_iff, b2_not_mem_iotaNull, b2_not_mem_iotaNull,
    b2_segSer_anc]
  tauto

private theorem b2_Psec {P Q R : α → α → Prop} :
    Psec P Q R ↔ ∃ A B, (((A ∈ sect P ∧ A.Nonempty) ∧ (B ∈ sect P ∧ B.Nonempty)) ∧
      (B \ A).Nonempty) ∧ Q = P ⥏ A ∧ R = P ⥏ B := by
  rw [Psec_apply]
  refine exists₂_congr fun A B => ?_
  rw [b2_S0]
  exact And.comm

private theorem b2_dom_semi_graph (f : β → α) (Q : β → β → Prop) :
    dom (graph f ⁏ Q) = graph f ʻʻ dom Q := by
  ext x
  constructor
  · rintro ⟨y, h⟩
    obtain ⟨z, w, ⟨rfl, -⟩, hzw⟩ := (semi_graph_apply _ _ _ _).1 h
    exact ⟨z, ⟨w, hzw⟩, rfl⟩
  · rintro ⟨z, ⟨w, hzw⟩, rfl⟩
    exact ⟨f w, (semi_graph_apply _ _ _ _).2 ⟨z, w, ⟨rfl, rfl⟩, hzw⟩⟩

private theorem b2_codom_semi_graph (f : β → α) (Q : β → β → Prop) :
    codom (graph f ⁏ Q) = graph f ʻʻ codom Q := by
  ext x
  constructor
  · rintro ⟨y, h⟩
    obtain ⟨z, w, ⟨-, rfl⟩, hzw⟩ := (semi_graph_apply _ _ _ _).1 h
    exact ⟨w, ⟨z, hzw⟩, rfl⟩
  · rintro ⟨w, ⟨z, hzw⟩, rfl⟩
    exact ⟨f z, (semi_graph_apply _ _ _ _).2 ⟨z, w, ⟨rfl, rfl⟩, hzw⟩⟩

/-! Descriptions with a unique value. -/

private theorem b2_desc_of_refs {R : α → β → Prop} {y : β} {b : α} (h : refs R y = {b})
    {ψ : α → Prop} : Desc R y ψ ↔ ψ b := by
  have hb : ∀ x, R x y ↔ x = b := fun x => by
    have := congrArg (x ∈ ·) h; simpa [refs] using this
  constructor
  · rintro ⟨c, hc, hψ⟩
    have : c = b := (hb c).1 ((hc c).2 rfl)
    exact this ▸ hψ
  · intro hψ; exact ⟨b, hb, hψ⟩

private theorem b2_EDesc_iff {R : α → β → Prop} {y : β} : EDesc R y ↔ ∃ b, refs R y = {b} := by
  constructor
  · rintro ⟨b, hb⟩; exact ⟨b, Set.ext fun x => hb x⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, fun x => by have := congrArg (x ∈ ·) hb; simpa [refs] using this⟩

end B2Helpers

section S213

variable {α : Type u}

/-- Serial `P_po` unfolded. -/
private theorem b2_serPo {P : α → α → Prop} (h : po P ∈ Ser) :
    (∀ x, ¬po P x x) ∧ (∀ x y, x ∈ fld P → y ∈ fld P → (po P x y ∨ x = y) ∨ po P y x) := by
  rw [mem_Ser, b2_fld_po] at h
  exact ⟨h.1.1, fun x y hx hy => h.2 x y ⟨hx, hy⟩⟩

private theorem b2_connPo {P : α → α → Prop} (h : po P ∈ connex) :
    ∀ x y, x ∈ fld P → y ∈ fld P → (po P x y ∨ x = y) ∨ po P y x := by
  rw [mem_connex, b2_fld_po] at h
  exact fun x y hx hy => h x y ⟨hx, hy⟩

private theorem b2_irr_of_J {P : α → α → Prop} (h : po P ⪽ J) : ∀ x, ¬po P x x :=
  fun x hx => h x x hx rfl

private theorem b2_irrP {P : α → α → Prop} (h : ∀ x, ¬po P x x) {x : α} : ¬P x x :=
  fun hx => h x (b2_po_of hx)

private theorem b2_J_of_ser {P : α → α → Prop} (h : po P ∈ Ser) : po P ⪽ J :=
  fun x y hxy e => (b2_serPo h).1 x (e ▸ hxy)

/-- Sections are nested when `P_po` is connected. -/
private theorem b2_nested {P : α → α → Prop} (hc : po P ∈ connex) {A B : Set α} (hA : A ∈ sect P)
    (hB : B ∈ sect P) : A ⊆ B ∨ B ⊆ A := by
  by_contra hn
  push Not at hn
  obtain ⟨⟨a, haA, haB⟩, ⟨b, hbB, hbA⟩⟩ :=
    And.intro (Set.not_subset.1 hn.1) (Set.not_subset.1 hn.2)
  rcases b2_connPo hc a b (hA.1 haA) (hB.1 hbB) with (h | rfl) | h
  · exact haB (b2_sect_po hB h hbB)
  · exact haB hbB
  · exact hbA (b2_sect_po hA h haA)

private theorem b2_ssub_of_diff {P : α → α → Prop} (hc : po P ∈ connex) {A B : Set α} (hA : A ∈ sect P)
    (hB : B ∈ sect P) (h : (B \ A).Nonempty) : A ⊆ B := by
  rcases b2_nested hc hA hB with h' | h'
  · exact h'
  · obtain ⟨z, hzB, hzA⟩ := h; exact absurd (h' hzB) hzA

/-- A proper non-null section from a pair `aPb`. -/
private theorem b2_proper {P : α → α → Prop} (hJ : ∀ x, ¬po P x x) {a b : α} (hab : P a b) :
    refs (anc P) a ∈ sect P ∧ (refs (anc P) a).Nonempty ∧ b ∈ fld P \ refs (anc P) a := by
  refine ⟨b2_refs_anc_mem_sect P a, ⟨a, b2_anc_refl ⟨b, Or.inl hab⟩⟩, ⟨a, Or.inr hab⟩, ?_⟩
  intro hba
  exact hJ b (b2_po_of_anc_po hba (b2_po_of hab))

/-- A non-null section which is not a unit class has a smaller non-null section. -/
private theorem b2_smaller {P : α → α → Prop} (h : po P ∈ Ser) {A : Set α} (hA : A ∈ sect P)
    (hne : A.Nonempty) (h1 : A ∉ (one : Set (Set α))) :
    ∃ C, (C ∈ sect P ∧ C.Nonempty) ∧ C ⊆ A ∧ (A \ C).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  have : ∃ y, y ∈ A ∧ y ≠ x := by
    by_contra hn; push Not at hn
    exact h1 ⟨x, Set.ext fun z => ⟨fun hz => hn z hz, fun hz => (b2_mem_iota.1 hz) ▸ hx⟩⟩
  obtain ⟨y, hy, hyx⟩ := this
  have key : ∀ x y, x ∈ A → y ∈ A → po P x y →
      ∃ C, (C ∈ sect P ∧ C.Nonempty) ∧ C ⊆ A ∧ (A \ C).Nonempty := by
    intro x y hx hy hxy
    refine ⟨refs (anc P) x, ⟨b2_refs_anc_mem_sect P x, x, b2_anc_refl (hA.1 hx)⟩,
      fun z hz => b2_sect_anc hA hz hx, y, hy, fun hyx => ?_⟩
    exact (b2_serPo h).1 y (b2_po_of_anc_po hyx hxy)
  rcases (b2_serPo h).2 x y (hA.1 hx) (hA.1 hy) with (h' | rfl) | h'
  · exact key x y hx hy h'
  · exact absurd rfl hyx
  · exact key y x hy hx h'

/-- The field of `P ⥏ α` is `α`, for a section not in `0 ∪ 1`. -/
private theorem b2_fld_fres {P : α → α → Prop} (h : po P ∈ Ser) {A : Set α} (hA : A ∈ sect P)
    (hne : A.Nonempty) (h1 : A ∉ (one : Set (Set α))) : fld (P ⥏ A) = A := by
  ext z
  constructor
  · rintro ⟨w, ⟨⟨hz, -⟩, -⟩ | ⟨-, hz⟩⟩ <;> exact hz
  · intro hz
    obtain ⟨x, hx⟩ := hne
    have : ∃ w, w ∈ A ∧ w ≠ z := by
      by_contra hn; push Not at hn
      exact h1 ⟨z, Set.ext fun v => ⟨fun hv => hn v hv, fun hv => (b2_mem_iota.1 hv) ▸ hz⟩⟩
    obtain ⟨w, hw, hwz⟩ := this
    rcases (b2_serPo h).2 z w (hA.1 hz) (hA.1 hw) with (h' | rfl) | h'
    · obtain ⟨v, hzv, hvw⟩ := b2_po_head h'
      exact ⟨v, Or.inl ⟨⟨hz, hzv⟩, b2_sect_anc hA hvw hw⟩⟩
    · exact absurd rfl hwz
    · obtain ⟨v, -, hvz⟩ := b2_po_tail h'
      exact ⟨v, Or.inr ⟨⟨b2_sect_P hA hvz hz, hvz⟩, hz⟩⟩

private theorem b2_fres_unit_null {P : α → α → Prop} (hJ : ∀ x, ¬po P x x) {A : Set α}
    (h1 : A ∈ (one : Set (Set α))) : P ⥏ A = rNull := by
  obtain ⟨x, rfl⟩ := h1
  rw [b2_eq_rNull]
  rintro y z ⟨⟨hy, hyz⟩, hz⟩
  rw [b2_mem_iota] at hy hz
  subst hy; subst hz
  exact b2_irrP hJ hyz

/-- Core of ✱213·15. -/
private theorem b2_fres_null_iff {P : α → α → Prop} (h : po P ∈ Ser) {A : Set α} (hA : A ∈ sect P)
    (hne : A.Nonempty) : P ⥏ A = rNull ↔ A ∈ (one : Set (Set α)) := by
  constructor
  · intro he
    by_contra h1
    obtain ⟨z, hz⟩ := hne
    have := (b2_fld_fres h hA ⟨z, hz⟩ h1).symm ▸ hz
    obtain ⟨w, hw | hw⟩ := this <;> rw [he] at hw <;> exact hw ⟨rfl, rfl⟩
  · exact b2_fres_unit_null (b2_serPo h).1

private theorem b2_unit_sect {P : α → α → Prop} (hJ : ∀ x, ¬po P x x) {x : α} :
    ι x ∈ sect P ↔ x ∈ refs Beg P := by
  rw [b2_refs_Beg]
  constructor
  · intro hs
    have hx : x ∈ fld P := hs.1 rfl
    have hc : x ∉ codom P := by
      rintro ⟨z, hz⟩
      have : z = x := b2_sect_P hs hz rfl
      subst this; exact b2_irrP hJ hz
    refine ⟨?_, hc⟩
    obtain ⟨y, hy | hy⟩ := hx
    · exact ⟨y, hy⟩
    · exact absurd ⟨y, hy⟩ hc
  · rintro ⟨⟨y, hy⟩, hc⟩
    refine ⟨fun z hz => (b2_mem_iota.1 hz) ▸ ⟨y, Or.inl hy⟩, ?_⟩
    rintro z ⟨w, hw, hzw⟩
    rw [b2_mem_iota] at hw; subst hw
    exact absurd ⟨z, hzw⟩ hc

/-- A beginning precedes every other term of the field. -/
private theorem b2_beg_anc {P : α → α → Prop} (h : po P ∈ Ser) {b c : α} (hb : b ∈ refs Beg P)
    (hc : c ∈ fld P) : anc P b c := by
  have hbf : b ∈ fld P := let ⟨y, hy⟩ := hb.1; ⟨y, Or.inl hy⟩
  rcases (b2_serPo h).2 b c hbf hc with (h' | rfl) | h'
  · exact b2_anc_of_po h'
  · exact b2_anc_refl hbf
  · obtain ⟨v, -, hv⟩ := b2_po_tail h'
    exact absurd ⟨v, hv⟩ hb.2

private theorem b2_beg_mem {P : α → α → Prop} (h : po P ∈ Ser) {b : α} (hb : b ∈ refs Beg P)
    {A : Set α} (hA : A ∈ sect P) (hne : A.Nonempty) : b ∈ A := by
  obtain ⟨c, hc⟩ := hne
  exact b2_sect_anc hA (b2_beg_anc h hb (hA.1 hc)) hc

private theorem b2_beg_unique {P : α → α → Prop} (h : po P ∈ Ser) {b c : α} (hb : b ∈ refs Beg P)
    (hc : c ∈ refs Beg P) : b = c := by
  have hcf : c ∈ fld P := let ⟨y, hy⟩ := hc.1; ⟨y, Or.inl hy⟩
  rcases anc_iff_po.1 (b2_beg_anc h hb hcf) with ⟨e, -⟩ | h'
  · exact e
  · obtain ⟨v, -, hv⟩ := b2_po_tail h'
    exact absurd ⟨v, hv⟩ hc.2

private theorem b2_refs_Beg_eq {P : α → α → Prop} (h : po P ∈ Ser) {b : α} (hb : b ∈ refs Beg P) :
    refs Beg P = {b} :=
  Set.ext fun c => ⟨fun hc => (b2_beg_unique h hb hc).symm, fun hc => hc ▸ hb⟩

/-- Core of ✱213·12: the domain of the series of non-null sections. -/
private theorem b2_dom_S0 (P : α → α → Prop) :
    dom (segSer (anc P) ⥏ (ι Λ)ᶜ) = (sect P \ ι Λ) \ ι (fld P) := by
  ext A
  rw [Set.mem_sdiff, b2_mem_diff_iotaNull, b2_mem_iota]
  constructor
  · rintro ⟨B, hAB⟩
    obtain ⟨⟨hA, hB⟩, z, hzB, hzA⟩ := b2_S0.1 hAB
    exact ⟨hA, fun e => hzA (e ▸ hB.1.1 hzB)⟩
  · rintro ⟨⟨hA, hne⟩, hne'⟩
    obtain ⟨x, hx⟩ := hne
    exact ⟨fld P, b2_S0.2 ⟨⟨⟨hA, x, hx⟩, b2_fld_mem_sect P, x, hA.1 hx⟩,
      (b2_sect_ne_fld hA).1 hne'⟩⟩

private theorem b2_mem_fld_S0 {P : α → α → Prop} {A : Set α} (h : A ∈ fld (segSer (anc P) ⥏ (ι Λ)ᶜ)) :
    A ∈ sect P ∧ A.Nonempty := by
  obtain ⟨B, hB | hB⟩ := h
  · exact (b2_S0.1 hB).1.1
  · exact (b2_S0.1 hB).1.2

private theorem b2_sect_one_eq {P : α → α → Prop} (hJ : ∀ x, ¬po P x x) :
    sect P ∩ one = iota ʻʻ refs Beg P := by
  ext A
  rw [b2_mem_iota_img]
  constructor
  · rintro ⟨hA, x, rfl⟩
    exact ⟨x, (b2_unit_sect hJ).1 hA, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(b2_unit_sect hJ).2 hx, x, rfl⟩

/-- A beginning's unit class is not the whole field. -/
private theorem b2_unit_ne_fld {P : α → α → Prop} (hJ : ∀ x, ¬po P x x) {x : α} (hx : x ∈ refs Beg P) :
    (fld P \ ι x).Nonempty := by
  obtain ⟨⟨y, hy⟩, -⟩ := hx
  refine ⟨y, ⟨x, Or.inr hy⟩, fun e => ?_⟩
  rw [b2_mem_iota] at e; subst e; exact b2_irrP hJ hy

private theorem b2_codom_S0 {P : α → α → Prop} (h : po P ∈ Ser) :
    codom (segSer (anc P) ⥏ (ι Λ)ᶜ) = (sect P \ ι Λ) \ iota ʻʻ refs Beg P := by
  ext B
  rw [Set.mem_sdiff, b2_mem_diff_iotaNull, b2_mem_iota_img]
  constructor
  · rintro ⟨A, hAB⟩
    obtain ⟨⟨hA, hB⟩, z, hzB, hzA⟩ := b2_S0.1 hAB
    refine ⟨hB, ?_⟩
    rintro ⟨b, hb, rfl⟩
    rw [b2_mem_iota] at hzB; subst hzB
    exact hzA (b2_beg_mem h hb hA.1 hA.2)
  · rintro ⟨⟨hB, hne⟩, hn⟩
    have h1 : B ∉ (one : Set (Set α)) := by
      rintro ⟨x, rfl⟩
      exact hn ⟨x, (b2_unit_sect (b2_serPo h).1).1 hB, rfl⟩
    obtain ⟨C, hC, -, hBC⟩ := b2_smaller h hB hne h1
    exact ⟨C, b2_S0.2 ⟨⟨hC, hB, hne⟩, hBC⟩⟩

private theorem b2_Beg_S0 {P : α → α → Prop} (h : po P ∈ Ser) :
    refs Beg (segSer (anc P) ⥏ (ι Λ)ᶜ) = sect P ∩ one := by
  have hJ := (b2_serPo h).1
  ext A
  rw [b2_refs_Beg, b2_dom_S0, b2_codom_S0 h]
  constructor
  · rintro ⟨⟨⟨hA, hne⟩, -⟩, hn⟩
    rw [b2_not_mem_iotaNull] at hne
    refine ⟨hA, ?_⟩
    by_contra h1
    refine hn ⟨⟨hA, b2_not_mem_iotaNull.2 hne⟩, ?_⟩
    rintro ⟨x, -, rfl⟩
    exact h1 ⟨x, rfl⟩
  · rintro ⟨hA, x, rfl⟩
    refine ⟨⟨⟨hA, b2_not_mem_iotaNull.2 ⟨x, rfl⟩⟩, fun e => ?_⟩, fun h' => h'.2 ?_⟩
    · obtain ⟨z, hz, hzx⟩ := b2_unit_ne_fld hJ ((b2_unit_sect hJ).1 hA)
      exact hzx ((b2_mem_iota.1 e) ▸ hz)
    · exact ⟨x, (b2_unit_sect hJ).1 hA, rfl⟩

/-- ✱213·01 (Df). \(P_{\varsigma }=P\unicode{x0294f}^{;}(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda ) \quad\text{Df}\) -/
theorem pm213_01 {P : α → α → Prop} : Psec P = opL fres P ⁏ (segSer (anc P) ⥏ (ι Λ)ᶜ) := rfl

/-- ✱213·1. \[\begin{align}\vdash :QP_{\varsigma }&R.\equiv .\\ &(\exists \alpha ,\beta ).\alpha ,\beta \in \text{sect}ʻP-\iota ʻ\Lambda .\exists !\beta -\alpha .Q=P\unicode{x0294f}\alpha .R=P\unicode{x0294f}\beta \\ &[*212·12·121.(*213·01)]\end{align}\] -/
theorem pm213_1 {P Q R : α → α → Prop} :
    Psec P Q R ↔ ∃ A B, (((A ∈ sect P \ ι Λ ∧ B ∈ sect P \ ι Λ) ∧ (B \ A).Nonempty) ∧
      Q = P ⥏ A) ∧ R = P ⥏ B := by
  rw [b2_Psec]
  refine exists₂_congr fun A B => ?_
  rw [b2_mem_diff_iotaNull, b2_mem_diff_iotaNull]
  tauto

/-- ✱213·11. \[\begin{align}\vdash \colon\ldotp &P_{\text{po}}\in \text{connex} .\supset :QP_{\varsigma }R.\equiv .\\ &(\exists \alpha ,\beta ).\alpha ,\beta \in \text{sect}ʻP-\iota ʻ\Lambda .\alpha \subset \beta .\alpha \neq \beta .Q=P\unicode{x0294f}\alpha .R=P\unicode{x0294f}\beta \\ &[*213·1.*211·6·17.*210·1]\end{align}\] -/
theorem pm213_11 {P Q R : α → α → Prop} (hc : po P ∈ connex) :
    Psec P Q R ↔ ∃ A B, (((((A ∈ sect P \ ι Λ ∧ B ∈ sect P \ ι Λ) ∧ A ⊆ B) ∧ A ≠ B) ∧
      Q = P ⥏ A) ∧ R = P ⥏ B) := by
  rw [b2_Psec]
  refine exists₂_congr fun A B => ?_
  rw [b2_mem_diff_iotaNull, b2_mem_diff_iotaNull]
  constructor
  · rintro ⟨⟨⟨hA, hB⟩, hd⟩, hQ, hR⟩
    have hsub := b2_ssub_of_diff hc hA.1 hB.1 hd
    refine ⟨⟨⟨⟨⟨hA, hB⟩, hsub⟩, ?_⟩, hQ⟩, hR⟩
    rintro rfl; obtain ⟨z, hz, hz'⟩ := hd; exact hz' hz
  · rintro ⟨⟨⟨⟨⟨hA, hB⟩, hsub⟩, hne⟩, hQ⟩, hR⟩
    refine ⟨⟨⟨hA, hB⟩, ?_⟩, hQ, hR⟩
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hn
    exact hne (Set.Subset.antisymm hsub hn)

/-- ✱213·12. \(\vdash .\text{D}ʻ(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda )=\text{sect}ʻP-\iota ʻ\Lambda -\iota ʻCʻP\) -/
theorem pm213_12 {P : α → α → Prop} :
    dom (segSer (anc P) ⥏ (ι Λ)ᶜ) = (sect P \ ι Λ) \ ι (fld P) := b2_dom_S0 P

/-- ✱213·121. \(\vdash :P_{\text{po}}\in \text{Ser}.\supset .\overrightarrow{B}ʻ(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda )=\text{sect}ʻP\cap 1=\iota ʻʻ\overrightarrow{B}ʻP\) -/
theorem pm213_121 {P : α → α → Prop} (h : po P ∈ Ser) :
    refs Beg (segSer (anc P) ⥏ (ι Λ)ᶜ) = sect P ∩ one ∧ sect P ∩ one = iota ʻʻ refs Beg P :=
  ⟨b2_Beg_S0 h, b2_sect_one_eq (b2_serPo h).1⟩

/-- ✱213·122. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.\exists !\overrightarrow{B}ʻP.\text{D}.Bʻ(\varsigma ʻP)\unicode{x0294f}(-\iota ʻ\Lambda )=\iota ʻBʻP\\ &[*213·121.*211·181]\end{align}\]

**Status.** proved (reading): transcription error of the e-text, which prints `ς'P` for `ς'P_*` and `D` for `⊃`; PM's proof cites ✱213·121 (about `ς'P_*`), and ✱213·132 has `ς'P_*`. -/
theorem pm213_122 {P : α → α → Prop} (h : po P ∈ Ser ∧ (refs Beg P).Nonempty) :
    Desc Beg (segSer (anc P) ⥏ (ι Λ)ᶜ) (fun X => Desc Beg P (fun b => X = ι b)) := by
  obtain ⟨h, b, hb⟩ := h
  have e1 := b2_refs_Beg_eq h hb
  have e2 : refs Beg (segSer (anc P) ⥏ (ι Λ)ᶜ) = {ι b} := by
    rw [pm213_121 h |>.1, pm213_121 h |>.2, e1]
    ext A; simp [b2_mem_iota_img]
  rw [b2_desc_of_refs e2, b2_desc_of_refs e1]

/-- ✱213·123. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.\overrightarrow{B}ʻP=\Lambda .\supset .\overrightarrow{B}ʻ(\varsigma ʻP)\unicode{x0294f}(-\iota ʻ\Lambda )=\Lambda \\ &[*213·121]\end{align}\]

**Status.** proved (reading): transcription error `ς'P` for `ς'P_*`, as in ✱213·122. -/
theorem pm213_123 {P : α → α → Prop} (h : po P ∈ Ser ∧ refs Beg P = Λ) :
    refs Beg (segSer (anc P) ⥏ (ι Λ)ᶜ) = Λ := by
  rw [pm213_121 h.1 |>.1, pm213_121 h.1 |>.2, h.2, Null_eq_empty, Null_eq_empty]
  ext A; simp [b2_mem_iota_img]

/-- ✱213·124. \[\begin{align}&\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.\supset :\text{E}!Bʻ(\varsigma ʻP)\unicode{x0294f}(-\iota ʻ\Lambda ).\equiv .\text{E}!BʻP\\ &[*213·122·123]\end{align}\]

**Status.** proved (reading): transcription error `ς'P` for `ς'P_*`, as in ✱213·122. -/
theorem pm213_124 {P : α → α → Prop} (h : po P ∈ Ser) :
    EDesc Beg (segSer (anc P) ⥏ (ι Λ)ᶜ) ↔ EDesc Beg P := by
  rw [b2_EDesc_iff, b2_EDesc_iff, pm213_121 h |>.1, pm213_121 h |>.2]
  constructor
  · rintro ⟨X, hX⟩
    have : X ∈ iota ʻʻ refs Beg P := hX ▸ rfl
    obtain ⟨b, hb, -⟩ := this
    exact ⟨b, b2_refs_Beg_eq h hb⟩
  · rintro ⟨b, hb⟩
    refine ⟨ι b, ?_⟩
    rw [hb]; ext A; simp [b2_mem_iota_img]

private theorem b2_rEx_of_mem_fld {P : α → α → Prop} {z : α} (hz : z ∈ fld P) : ∃ a b, P a b := by
  obtain ⟨w, hw | hw⟩ := hz
  · exact ⟨z, w, hw⟩
  · exact ⟨w, z, hw⟩

private theorem b2_two_sects {P : α → α → Prop} (hJ : ∀ x, ¬po P x x) {a b : α} (hab : P a b) :
    segSer (anc P) (refs (anc P) a) (fld P) ∧ (refs (anc P) a).Nonempty ∧
      (fld P).Nonempty ∧ refs (anc P) a ≠ fld P := by
  obtain ⟨hs, hne, hbf⟩ := b2_proper hJ hab
  exact ⟨b2_segSer_anc.2 ⟨⟨hs, b2_fld_mem_sect P⟩, b, hbf⟩, hne, ⟨b, hbf.1⟩,
    fun e => hbf.2 (e ▸ hbf.1)⟩

/-- ✱213·125. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\supset .Cʻ\varsigma ʻP_{*}-\iota ʻ\Lambda {\sim}\in 1\) -/
theorem pm213_125 {P : α → α → Prop} (hJ : po P ⪽ J) :
    fld (segSer (anc P)) \ ι Λ ∉ (one : Set (Set (Set α))) := by
  have hJ' := b2_irr_of_J hJ
  rintro ⟨X, hX⟩
  have hX' : X ∈ fld (segSer (anc P)) \ ι Λ := hX ▸ rfl
  obtain ⟨⟨Y, hY⟩, -⟩ := hX'
  have : ∃ z, z ∈ fld P := by
    rcases hY with hY | hY <;> obtain ⟨-, z, hzB, -⟩ := b2_segSer_anc.1 hY
    · exact ⟨z, (b2_segSer_anc.1 hY).1.2.1 hzB⟩
    · exact ⟨z, (b2_segSer_anc.1 hY).1.2.1 hzB⟩
  obtain ⟨z, hz⟩ := this
  obtain ⟨a, b, hab⟩ := b2_rEx_of_mem_fld hz
  obtain ⟨hs, hne, hfne, hneq⟩ := b2_two_sects hJ' hab
  have m1 : fld P ∈ fld (segSer (anc P)) \ ι Λ :=
    b2_mem_diff_iotaNull.2 ⟨⟨_, Or.inr hs⟩, hfne⟩
  have m2 : refs (anc P) a ∈ fld (segSer (anc P)) \ ι Λ :=
    b2_mem_diff_iotaNull.2 ⟨⟨_, Or.inl hs⟩, hne⟩
  rw [hX] at m1 m2
  exact hneq (b2_mem_iota.1 m2 ▸ (b2_mem_iota.1 m1).symm ▸ rfl)

/-- ✱213·126. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\dot{\exists} !P.\supset .\exists !\text{sect}ʻP-\iota ʻ\Lambda -\iota ʻCʻP\) -/
theorem pm213_126 {P : α → α → Prop} (h : po P ⪽ J ∧ rEx P) :
    ((sect P \ ι Λ) \ ι (fld P)).Nonempty := by
  obtain ⟨hJ, a, b, hab⟩ := h
  obtain ⟨hs, hne, -, hneq⟩ := b2_two_sects (b2_irr_of_J hJ) hab
  exact ⟨_, b2_mem_diff_iotaNull.2 ⟨(b2_segSer_anc.1 hs).1.1, hne⟩, hneq⟩

/-- ✱213·13. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\supset .Cʻ(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda )=\text{sect}ʻP-\iota ʻ\Lambda\) -/
theorem pm213_13 {P : α → α → Prop} (hJ : po P ⪽ J) :
    fld (segSer (anc P) ⥏ (ι Λ)ᶜ) = sect P \ ι Λ := by
  ext A
  rw [b2_mem_diff_iotaNull]
  refine ⟨b2_mem_fld_S0, fun ⟨hA, hne⟩ => ?_⟩
  by_cases hf : A = fld P
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨a, b, hab⟩ := b2_rEx_of_mem_fld (hA.1 hx)
    obtain ⟨hs, hne', hfne, -⟩ := b2_two_sects (b2_irr_of_J hJ) hab
    subst hf
    exact ⟨_, Or.inr (b2_S0.2 ⟨⟨⟨(b2_segSer_anc.1 hs).1.1, hne'⟩, hA, hfne⟩,
      (b2_segSer_anc.1 hs).2⟩)⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨fld P, Or.inl (b2_S0.2 ⟨⟨⟨hA, x, hx⟩, b2_fld_mem_sect P, x, hA.1 hx⟩,
      (b2_sect_ne_fld hA).1 hf⟩)⟩

/-- ✱213·131. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.\supset .\text{ᗡ}ʻ(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda )=\text{sect}ʻP-\iota ʻ\Lambda -\iota ʻʻ\overrightarrow{B}ʻP\\ &[*213·13·121]\end{align}\] -/
theorem pm213_131 {P : α → α → Prop} (h : po P ∈ Ser) :
    codom (segSer (anc P) ⥏ (ι Λ)ᶜ) = (sect P \ ι Λ) \ iota ʻʻ refs Beg P := b2_codom_S0 h

private theorem b2_iota_img_single (b : α) : iota ʻʻ ({b} : Set α) = ι (ι b) := by
  ext X
  rw [b2_mem_iota_img, b2_mem_iota]
  constructor
  · rintro ⟨c, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨b, rfl, rfl⟩

/-- ✱213·132. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.\exists !\overrightarrow{B}ʻP.\supset .\text{ᗡ}ʻ(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda )=\text{sect}ʻP-\iota ʻ\Lambda -\iota ʻ\iota ʻBʻP\\ &[*213·13·122]\end{align}\] -/
theorem pm213_132 {P : α → α → Prop} (h : po P ∈ Ser ∧ (refs Beg P).Nonempty) :
    Desc Beg P (fun b => codom (segSer (anc P) ⥏ (ι Λ)ᶜ) = (sect P \ ι Λ) \ ι (ι b)) := by
  obtain ⟨h, b, hb⟩ := h
  have e1 := b2_refs_Beg_eq h hb
  rw [b2_desc_of_refs e1, pm213_131 h, e1, b2_iota_img_single]

/-- ✱213·133. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.\overrightarrow{B}ʻP=\Lambda .\supset .\text{ᗡ}ʻ(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda )=\text{sect}ʻP-\iota ʻ\Lambda\\ &[*213·13·123]\end{align}\] -/
theorem pm213_133 {P : α → α → Prop} (h : po P ∈ Ser ∧ refs Beg P = Λ) :
    codom (segSer (anc P) ⥏ (ι Λ)ᶜ) = sect P \ ι Λ := by
  rw [pm213_131 h.1, h.2, Null_eq_empty]
  ext A; simp [b2_mem_iota_img]

/-- ✱213·134. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\dot{\exists} !P.\supset .Bʻ\text{Cnv}ʻ(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda )=CʻP \quad[*213·12·13]\) -/
theorem pm213_134 {P : α → α → Prop} (h : po P ⪽ J ∧ rEx P) :
    Desc Beg (segSer (anc P) ⥏ (ι Λ)ᶜ)˘ (fun X => X = fld P) := by
  obtain ⟨hJ, a, b, hab⟩ := h
  obtain ⟨hs, hne', hfne, -⟩ := b2_two_sects (b2_irr_of_J hJ) hab
  have e : refs Beg (segSer (anc P) ⥏ (ι Λ)ᶜ)˘ = {fld P} := by
    ext X
    show (X ∈ codom (segSer (anc P) ⥏ (ι Λ)ᶜ) ∧ X ∉ dom (segSer (anc P) ⥏ (ι Λ)ᶜ)) ↔ X = fld P
    rw [b2_dom_S0, Set.mem_sdiff, b2_mem_diff_iotaNull, b2_mem_iota]
    constructor
    · rintro ⟨⟨Y, hY⟩, hn⟩
      obtain ⟨⟨-, hX⟩, -⟩ := b2_S0.1 hY
      by_contra hf; exact hn ⟨hX, hf⟩
    · rintro rfl
      exact ⟨⟨_, b2_S0.2 ⟨⟨⟨(b2_segSer_anc.1 hs).1.1, hne'⟩, b2_fld_mem_sect P, hfne⟩,
        (b2_segSer_anc.1 hs).2⟩⟩, fun h' => h'.2 rfl⟩
  rw [b2_desc_of_refs e]

/-- ✱213·14. \[\begin{align}\vdash .&\text{D}ʻP_{\varsigma }=P\unicode{x0294f}ʻʻ\text{D}ʻ(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda ).\text{ᗡ}ʻP_{\varsigma }=P\unicode{x0294f}ʻʻ\text{ᗡ}ʻ(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda ).\\ &CʻP_{\varsigma }=P\unicode{x0294f}ʻʻCʻ(\varsigma ʻP_{*})\unicode{x0294f}(-\iota ʻ\Lambda )\\ &[*150·21·211·22]\end{align}\] -/
theorem pm213_14 {P : α → α → Prop} :
    (dom (Psec P) = opL fres P ʻʻ dom (segSer (anc P) ⥏ (ι Λ)ᶜ) ∧
      codom (Psec P) = opL fres P ʻʻ codom (segSer (anc P) ⥏ (ι Λ)ᶜ)) ∧
      fld (Psec P) = opL fres P ʻʻ fld (segSer (anc P) ⥏ (ι Λ)ᶜ) :=
  ⟨⟨b2_dom_semi_graph (fres P) _, b2_codom_semi_graph (fres P) _⟩, fld_semi_graph (fres P) _⟩

/-- ✱213·141. \[\begin{align}&\vdash .\text{D}ʻP_{\varsigma }=P\unicode{x0294f}ʻʻ(\text{sect}ʻP-\iota ʻ\Lambda -\iota ʻCʻP)\\ &[*213·12·14]\end{align}\] -/
theorem pm213_141 {P : α → α → Prop} :
    dom (Psec P) = opL fres P ʻʻ ((sect P \ ι Λ) \ ι (fld P)) := by
  rw [pm213_14.1.1, pm213_12]

/-- ✱213·142. \[\begin{align}&\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\supset .CʻP_{\varsigma }=P\unicode{x0294f}ʻʻ(\text{sect}ʻP-\iota ʻ\Lambda )\\ &[*213·13·14]\end{align}\] -/
theorem pm213_142 {P : α → α → Prop} (hJ : po P ⪽ J) :
    fld (Psec P) = opL fres P ʻʻ (sect P \ ι Λ) := by
  rw [pm213_14.2, pm213_13 hJ]

/-- ✱213·143. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.\supset .\text{ᗡ}ʻP_{\varsigma }=P\unicode{x0294f}ʻʻ(\text{sect}ʻP-\iota ʻ\Lambda -\iotaʻʻ\overrightarrow{B}ʻP)\\ &[*213·131·14]\end{align}\] -/
theorem pm213_143 {P : α → α → Prop} (h : po P ∈ Ser) :
    codom (Psec P) = opL fres P ʻʻ ((sect P \ ι Λ) \ iota ʻʻ refs Beg P) := by
  rw [pm213_14.1.2, pm213_131 h]

/-- ✱213·144. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.\exists !\overrightarrow{B}ʻP.\supset .\text{ᗡ}ʻP_{\varsigma }=P\unicode{x0294f}ʻʻ(\text{sect}ʻP-\iota ʻ\Lambda -\iota ʻ\iota ʻBʻP)\\ &[*213·132·14]\end{align}\] -/
theorem pm213_144 {P : α → α → Prop} (h : po P ∈ Ser ∧ (refs Beg P).Nonempty) :
    Desc Beg P (fun b => codom (Psec P) = opL fres P ʻʻ ((sect P \ ι Λ) \ ι (ι b))) := by
  obtain ⟨h, b, hb⟩ := h
  have e1 := b2_refs_Beg_eq h hb
  rw [b2_desc_of_refs e1, pm213_143 h, e1, b2_iota_img_single]

/-- ✱213·145. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.\overrightarrow{B}ʻP=\Lambda .\supset .\text{ᗡ}ʻP_{\varsigma }=P\unicode{x0294f}ʻʻ(\text{sect}ʻP-\iota ʻ\Lambda )\\ &[*213·143]\end{align}\] -/
theorem pm213_145 {P : α → α → Prop} (h : po P ∈ Ser ∧ refs Beg P = Λ) :
    codom (Psec P) = opL fres P ʻʻ (sect P \ ι Λ) := by
  rw [pm213_14.1.2, pm213_133 h]

private theorem b2_fres_empty (P : α → α → Prop) : P ⥏ (∅ : Set α) = rNull :=
  b2_eq_rNull.2 fun _ _ h => h.2

private theorem b2_empty_not_one : (∅ : Set α) ∉ (one : Set (Set α)) := by
  rintro ⟨x, hx⟩
  have : x ∈ (∅ : Set α) := hx ▸ rfl
  exact this

/-- ✱213·146. \(\vdash :P\,\unicode{x2abd}\, J.\supset .P\unicode{x0294f}ʻʻ\text{sect}ʻP=P\unicode{x0294f}ʻʻ(\text{sect}ʻP-1)\) -/
theorem pm213_146 {P : α → α → Prop} (hJ : P ⪽ J) :
    opL fres P ʻʻ sect P = opL fres P ʻʻ (sect P \ one) := by
  ext Q
  rw [b2_mem_opL_fres_img, b2_mem_opL_fres_img]
  constructor
  · rintro ⟨A, hA, rfl⟩
    by_cases h1 : A ∈ (one : Set (Set α))
    · obtain ⟨x, rfl⟩ := h1
      refine ⟨∅, ⟨b2_empty_mem_sect P, b2_empty_not_one⟩, ?_⟩
      rw [b2_fres_empty, b2_eq_rNull]
      rintro y z ⟨⟨hy, hyz⟩, hz⟩
      rw [b2_mem_iota] at hy hz; subst hy; subst hz
      exact hJ _ _ hyz rfl
    · exact ⟨A, ⟨hA, h1⟩, rfl⟩
  · rintro ⟨A, hA, rfl⟩; exact ⟨A, hA.1, rfl⟩

/-- ✱213·15. \(\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.\alpha \in \text{sect}ʻP-\iota ʻ\Lambda .\supset :P\unicode{x0294f}\alpha =\dot{\Lambda} .\equiv .\alpha \in 1\) -/
theorem pm213_15 {P : α → α → Prop} {A : Set α} (h : po P ∈ Ser ∧ A ∈ sect P \ ι Λ) :
    P ⥏ A = rNull ↔ A ∈ (one : Set (Set α)) := by
  obtain ⟨h, hA⟩ := h
  rw [b2_mem_diff_iotaNull] at hA
  exact b2_fres_null_iff h hA.1 hA.2

/-- `P ⥏` is one-one on non-null sections. -/
private theorem b2_fres_inj {P : α → α → Prop} (h : po P ∈ Ser) {A B : Set α} (hA : A ∈ sect P)
    (hAne : A.Nonempty) (hB : B ∈ sect P) (hBne : B.Nonempty) (e : P ⥏ A = P ⥏ B) : A = B := by
  by_cases h1 : A ∈ (one : Set (Set α))
  · have h2 : B ∈ (one : Set (Set α)) :=
      (b2_fres_null_iff h hB hBne).1 (e ▸ (b2_fres_null_iff h hA hAne).2 h1)
    obtain ⟨a, rfl⟩ := h1
    obtain ⟨b, rfl⟩ := h2
    have hJ := (b2_serPo h).1
    rw [b2_beg_unique h ((b2_unit_sect hJ).1 hA) ((b2_unit_sect hJ).1 hB)]
  · have h2 : B ∉ (one : Set (Set α)) := fun h2 =>
      h1 ((b2_fres_null_iff h hA hAne).1 (e ▸ (b2_fres_null_iff h hB hBne).2 h2))
    rw [← b2_fld_fres h hA hAne h1, ← b2_fld_fres h hB hBne h2, e]

/-- ✱213·151. \(\vdash :P_{\text{po}}\in \text{Ser}.\supset .(P\unicode{x0294f})\upharpoonright (\text{sect}ʻP-{℩}ʻ\Lambda )\in 1\rightarrow 1\) -/
theorem pm213_151 {P : α → α → Prop} (h : po P ∈ Ser) :
    opL fres P ↾ (sect P \ ι Λ) ∈ arrow one one := by
  rw [mem_arrow_one_one]
  constructor
  · rintro X Y A ⟨⟨hX, -⟩, ⟨hY, -⟩⟩
    exact hX.trans hY.symm
  · rintro X A B ⟨⟨hA, hA'⟩, ⟨hB, hB'⟩⟩
    rw [b2_mem_diff_iotaNull] at hA' hB'
    exact b2_fres_inj h hA'.1 hA'.2 hB'.1 hB'.2 (hA.symm.trans hB)

/-- ✱213·152. \(\vdash :P_{\text{po}}\in \text{Ser}.\supset .P_{\varsigma }\,\text{smor}\,(\varsigma ʻP_{*})\unicode{x0294f}(-{℩}ʻ\Lambda ) \quad[*213·151·13]\) -/
theorem pm213_152 {P : α → α → Prop} (h : po P ∈ Ser) :
    smor (Psec P) (segSer (anc P) ⥏ (ι Λ)ᶜ) := by
  refine ⟨opL fres P ↾ fld (segSer (anc P) ⥏ (ι Λ)ᶜ), ⟨?_, ?_⟩, ?_⟩
  · have h1 := pm213_151 h
    rw [mem_arrow_one_one] at h1 ⊢
    refine ⟨fun x y z hxyz => h1.1 x y z ⟨⟨hxyz.1.1, ?_⟩, ⟨hxyz.2.1, ?_⟩⟩,
      fun x y z hxyz => h1.2 x y z ⟨⟨hxyz.1.1, ?_⟩, ⟨hxyz.2.1, ?_⟩⟩⟩
    · exact b2_mem_diff_iotaNull.2 (b2_mem_fld_S0 hxyz.1.2)
    · exact b2_mem_diff_iotaNull.2 (b2_mem_fld_S0 hxyz.2.2)
    · exact b2_mem_diff_iotaNull.2 (b2_mem_fld_S0 hxyz.1.2)
    · exact b2_mem_diff_iotaNull.2 (b2_mem_fld_S0 hxyz.2.2)
  · ext A
    exact ⟨fun hA => ⟨P ⥏ A, rfl, hA⟩, fun ⟨_, _, hA⟩ => hA⟩
  · funext Q R
    apply propext
    rw [semi_apply, Psec_apply]
    constructor
    · rintro ⟨A, B, ⟨hQ, hR⟩, hAB⟩
      exact ⟨A, B, ⟨⟨hQ, ⟨B, Or.inl hAB⟩⟩, ⟨hR, ⟨A, Or.inr hAB⟩⟩⟩, hAB⟩
    · rintro ⟨A, B, ⟨⟨hQ, -⟩, ⟨hR, -⟩⟩, hAB⟩
      exact ⟨A, B, ⟨hQ, hR⟩, hAB⟩

private theorem b2_connex_of_ser {P : α → α → Prop} (h : po P ∈ Ser) : po P ∈ connex := by
  rw [mem_Ser] at h; exact mem_connex.2 h.2

private theorem b2_Psec_ser {P Q R : α → α → Prop} (h : po P ∈ Ser) :
    Psec P Q R ↔ ∃ A B, ((A ∈ sect P ∧ A.Nonempty) ∧ (B ∈ sect P ∧ B.Nonempty)) ∧
      (A ⊆ B ∧ (B \ A).Nonempty) ∧ Q = P ⥏ A ∧ R = P ⥏ B := by
  rw [b2_Psec]
  refine exists₂_congr fun A B => ?_
  constructor
  · rintro ⟨⟨⟨hA, hB⟩, hd⟩, hQ, hR⟩
    exact ⟨⟨hA, hB⟩, ⟨b2_ssub_of_diff (b2_connex_of_ser h) hA.1 hB.1 hd, hd⟩, hQ, hR⟩
  · rintro ⟨⟨hA, hB⟩, ⟨-, hd⟩, hQ, hR⟩
    exact ⟨⟨⟨hA, hB⟩, hd⟩, hQ, hR⟩

private theorem b2_mem_fld_Psec {P Q : α → α → Prop} (h : Q ∈ fld (Psec P)) :
    ∃ A, (A ∈ sect P ∧ A.Nonempty) ∧ Q = P ⥏ A := by
  obtain ⟨R, hR | hR⟩ := h
  · obtain ⟨A, B, ⟨⟨hA, -⟩, -⟩, hQ, -⟩ := b2_Psec.1 hR
    exact ⟨A, hA, hQ⟩
  · obtain ⟨A, B, ⟨⟨-, hB⟩, -⟩, -, hQ⟩ := b2_Psec.1 hR
    exact ⟨B, hB, hQ⟩

private theorem b2_diff_of_ne {A B : Set α} (hs : A ⊆ B) (e : A ≠ B) : (B \ A).Nonempty := by
  by_contra hn
  rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hn
  exact e (Set.Subset.antisymm hs hn)

/-- ✱213·153. \(\vdash :P_{\text{po}}\in \text{Ser}.\supset .P_{\varsigma }\in \text{Ser} \quad[*213·152.*212·3.*204·4·21]\) -/
theorem pm213_153 {P : α → α → Prop} (h : po P ∈ Ser) : Psec P ∈ Ser := by
  have hc := b2_connex_of_ser h
  rw [mem_Ser]
  refine ⟨⟨fun Q hQ => ?_, fun Q R S ⟨hQR, hRS⟩ => ?_⟩, fun Q R ⟨hQ, hR⟩ => ?_⟩
  · obtain ⟨A, B, ⟨hA, hB⟩, ⟨-, hd⟩, hQ1, hQ2⟩ := (b2_Psec_ser h).1 hQ
    have := b2_fres_inj h hA.1 hA.2 hB.1 hB.2 (hQ1.symm.trans hQ2)
    subst this
    obtain ⟨z, hz, hz'⟩ := hd; exact hz' hz
  · obtain ⟨A, B, ⟨hA, hB⟩, ⟨hAB, -⟩, hQ1, hR1⟩ := (b2_Psec_ser h).1 hQR
    obtain ⟨B', C, ⟨hB', hC⟩, ⟨-, hd⟩, hR2, hS⟩ := (b2_Psec_ser h).1 hRS
    have := b2_fres_inj h hB.1 hB.2 hB'.1 hB'.2 (hR1.symm.trans hR2)
    subst this
    obtain ⟨z, hz, hz'⟩ := hd
    exact b2_Psec.2 ⟨A, C, ⟨⟨hA, hC⟩, z, hz, fun hzA => hz' (hAB hzA)⟩, hQ1, hS⟩
  · obtain ⟨A, hA, rfl⟩ := b2_mem_fld_Psec hQ
    obtain ⟨B, hB, rfl⟩ := b2_mem_fld_Psec hR
    by_cases e : A = B
    · subst e; exact Or.inl (Or.inr rfl)
    rcases b2_nested hc hA.1 hB.1 with hs | hs
    · exact Or.inl (Or.inl (b2_Psec.2 ⟨A, B, ⟨⟨hA, hB⟩, b2_diff_of_ne hs e⟩, rfl, rfl⟩))
    · exact Or.inr (b2_Psec.2 ⟨B, A, ⟨⟨hB, hA⟩, b2_diff_of_ne hs (Ne.symm e)⟩, rfl, rfl⟩)

/-- ✱213·154. \(\vdash :P_{\text{po}}\in \text{Ser}.\supset .\overrightarrow{B}ʻP_{\varsigma }=P\unicode{x0294f}ʻʻ{℩}ʻʻ\overrightarrow{B}ʻP \quad[*213·151·121.*151·5]\) -/
theorem pm213_154 {P : α → α → Prop} (h : po P ∈ Ser) :
    refs Beg (Psec P) = opL fres P ʻʻ (iota ʻʻ refs Beg P) := by
  have hJ := (b2_serPo h).1
  ext Q
  rw [b2_refs_Beg, pm213_14.1.1, pm213_14.1.2, b2_mem_opL_fres_img, b2_mem_opL_fres_img,
    b2_mem_opL_fres_img, b2_dom_S0, b2_codom_S0 h]
  constructor
  · rintro ⟨⟨A, hA, rfl⟩, hn⟩
    rw [Set.mem_sdiff, b2_mem_diff_iotaNull] at hA
    have h1 : A ∈ (one : Set (Set α)) := by
      by_contra h1
      obtain ⟨C, hC, -, hd⟩ := b2_smaller h hA.1.1 hA.1.2 h1
      refine hn ⟨A, ?_, rfl⟩
      rw [← b2_codom_S0 h]
      exact ⟨C, b2_S0.2 ⟨⟨hC, hA.1⟩, hd⟩⟩
    obtain ⟨x, rfl⟩ := h1
    exact ⟨ι x, ⟨x, (b2_unit_sect hJ).1 hA.1.1, rfl⟩, rfl⟩
  · rintro ⟨A, ⟨b, hb, rfl⟩, rfl⟩
    have hs := (b2_unit_sect hJ).2 hb
    refine ⟨⟨ι b, ?_, rfl⟩, ?_⟩
    · refine ⟨b2_mem_diff_iotaNull.2 ⟨hs, b, rfl⟩, fun e => ?_⟩
      obtain ⟨z, hz, hzb⟩ := b2_unit_ne_fld hJ hb
      exact hzb ((b2_mem_iota.1 e) ▸ hz)
    · rintro ⟨B, hB, e⟩
      rw [Set.mem_sdiff, b2_mem_diff_iotaNull] at hB
      have := b2_fres_inj h hs ⟨b, rfl⟩ hB.1.1 hB.1.2 e
      exact hB.2 ⟨b, hb, this.symm⟩

private theorem b2_refs_Beg_Psec {P : α → α → Prop} (h : po P ∈ Ser) {b : α} (hb : b ∈ refs Beg P) :
    refs Beg (Psec P) = {rNull} := by
  rw [pm213_154 h, b2_refs_Beg_eq h hb, b2_iota_img_single]
  ext Q
  rw [b2_mem_opL_fres_img]
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [b2_mem_iota] at hA; subst hA
    exact b2_fres_unit_null (b2_serPo h).1 ⟨b, rfl⟩
  · intro hQ
    exact ⟨ι b, rfl, hQ.trans (b2_fres_unit_null (b2_serPo h).1 ⟨b, rfl⟩).symm⟩

/-- ✱213·155. \(\vdash :P_{\text{po}}\in \text{Ser}.\exists !\overrightarrow{B}ʻP.\supset .BʻP_{\varsigma }=\dot{\Lambda}\) -/
theorem pm213_155 {P : α → α → Prop} (h : po P ∈ Ser ∧ (refs Beg P).Nonempty) :
    Desc Beg (Psec P) (fun Q => Q = rNull) := by
  obtain ⟨h, b, hb⟩ := h
  rw [b2_desc_of_refs (b2_refs_Beg_Psec h hb)]

/-- ✱213·156. \(\vdash :P_{\text{po}}\in \text{Ser}.\overrightarrow{B}ʻP=\Lambda .\supset .\overrightarrow{B}ʻP_{\varsigma }=\Lambda \quad[*213·154]\) -/
theorem pm213_156 {P : α → α → Prop} (h : po P ∈ Ser ∧ refs Beg P = Λ) :
    refs Beg (Psec P) = Λ := by
  rw [pm213_154 h.1, h.2, Null_eq_empty, Null_eq_empty]
  ext Q; simp [b2_mem_opL_fres_img, b2_mem_iota_img]

/-- ✱213·157. \(\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.\supset :\text{E}!BʻP.\equiv .\text{E}!BʻP_{\varsigma } \quad[*213·155·156]\) -/
theorem pm213_157 {P : α → α → Prop} (h : po P ∈ Ser) :
    EDesc Beg P ↔ EDesc Beg (Psec P) := by
  rw [b2_EDesc_iff, b2_EDesc_iff]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨rNull, b2_refs_Beg_Psec h (hb.symm ▸ rfl : b ∈ refs Beg P)⟩
  · rintro ⟨Q, hQ⟩
    have : Q ∈ refs Beg (Psec P) := hQ ▸ rfl
    rw [pm213_154 h] at this
    obtain ⟨A, ⟨b, hb, -⟩, -⟩ := this
    exact ⟨b, b2_refs_Beg_eq h hb⟩

private theorem b2_fres_fld (P : α → α → Prop) : P ⥏ fld P = P := by
  funext x y; apply propext
  exact ⟨fun h => h.1.2, fun h => ⟨⟨⟨y, Or.inl h⟩, h⟩, ⟨x, Or.inr h⟩⟩⟩

private theorem b2_fld_fres_sub (P : α → α → Prop) (A : Set α) : fld (P ⥏ A) ⊆ A := by
  rintro z ⟨w, ⟨⟨hz, -⟩, -⟩ | ⟨-, hz⟩⟩ <;> exact hz

private theorem b2_fres_eq_self {P : α → α → Prop} {A : Set α} (hA : A ⊆ fld P) (e : P ⥏ A = P) :
    A = fld P := by
  refine Set.Subset.antisymm hA ?_
  have := b2_fld_fres_sub P A
  rw [e] at this; exact this

/-- ✱213·158. \(\vdash :P_{\text{po}}\in \text{Ser}.\dot{\exists} !P.\supset .Bʻ\breve{P} _{\varsigma }=P\) -/
theorem pm213_158 {P : α → α → Prop} (h : po P ∈ Ser ∧ rEx P) :
    Desc Beg (Psec P)˘ (fun Q => Q = P) := by
  obtain ⟨h, a, b, hab⟩ := h
  have hJ := (b2_serPo h).1
  obtain ⟨-, -, hfne, -⟩ := b2_two_sects hJ hab
  have e : refs Beg (Psec P)˘ = {P} := by
    ext X
    show (X ∈ codom (Psec P) ∧ X ∉ dom (Psec P)) ↔ X = P
    rw [pm213_141, pm213_143 h, b2_mem_opL_fres_img, b2_mem_opL_fres_img]
    constructor
    · rintro ⟨⟨B, hB, rfl⟩, hn⟩
      rw [Set.mem_sdiff, b2_mem_diff_iotaNull] at hB
      by_cases hf : B = fld P
      · subst hf; exact b2_fres_fld P
      · exact absurd ⟨B, ⟨b2_mem_diff_iotaNull.2 hB.1, hf⟩, rfl⟩ hn
    · intro hX; rw [hX]
      refine ⟨⟨fld P, ⟨b2_mem_diff_iotaNull.2 ⟨b2_fld_mem_sect P, hfne⟩, ?_⟩,
        (b2_fres_fld P).symm⟩, ?_⟩
      · rintro ⟨c, hc, e⟩
        obtain ⟨z, hz, hzc⟩ := b2_unit_ne_fld hJ hc
        exact hzc ((show fld P = ι c from e) ▸ hz)
      · rintro ⟨A, ⟨hA, hf⟩, e⟩
        rw [b2_mem_diff_iotaNull] at hA
        exact hf (b2_fres_eq_self hA.1.1 e.symm)
  rw [b2_desc_of_refs e]

/-- ✱213·16. \(\vdash .\text{D}ʻP_{\varsigma }=P\unicode{x0294f}ʻʻ(\text{sect}ʻP-{℩}ʻ\Lambda )-{℩}ʻP\) -/
theorem pm213_16 {P : α → α → Prop} :
    dom (Psec P) = opL fres P ʻʻ (sect P \ ι Λ) \ ι P := by
  rw [pm213_141]
  ext Q
  rw [Set.mem_sdiff, b2_mem_opL_fres_img, b2_mem_opL_fres_img, b2_mem_iota]
  constructor
  · rintro ⟨A, ⟨hA, hf⟩, rfl⟩
    refine ⟨⟨A, hA, rfl⟩, fun e => hf ?_⟩
    rw [b2_mem_diff_iotaNull] at hA
    exact b2_fres_eq_self hA.1.1 e
  · rintro ⟨⟨A, hA, rfl⟩, hn⟩
    refine ⟨A, ⟨hA, fun e => hn ?_⟩, rfl⟩
    rw [b2_mem_iota] at e; subst e; exact b2_fres_fld P

/-- ✱213·161. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\exists !\overrightarrow{B}ʻP.\supset .P\unicode{x0294f}ʻʻ\text{sect}ʻP=P\unicode{x0294f}ʻʻ(\text{sect}ʻP-\iota ʻ\Lambda )=CʻP_{\varsigma }\) -/
theorem pm213_161 {P : α → α → Prop} (h : po P ⪽ J ∧ (refs Beg P).Nonempty) :
    opL fres P ʻʻ sect P = opL fres P ʻʻ (sect P \ ι Λ) ∧
      opL fres P ʻʻ (sect P \ ι Λ) = fld (Psec P) := by
  obtain ⟨hJ, b, hb⟩ := h
  have hJ' := b2_irr_of_J hJ
  refine ⟨?_, (pm213_142 hJ).symm⟩
  ext Q
  rw [b2_mem_opL_fres_img, b2_mem_opL_fres_img]
  constructor
  · rintro ⟨A, hA, rfl⟩
    by_cases hne : A.Nonempty
    · exact ⟨A, b2_mem_diff_iotaNull.2 ⟨hA, hne⟩, rfl⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      subst hne
      refine ⟨ι b, b2_mem_diff_iotaNull.2 ⟨(b2_unit_sect hJ').2 hb, b, rfl⟩, ?_⟩
      rw [b2_fres_empty, b2_fres_unit_null hJ' ⟨b, rfl⟩]
  · rintro ⟨A, hA, rfl⟩; exact ⟨A, hA.1, rfl⟩

private theorem b2_fres_ne_null {P : α → α → Prop} (h : po P ∈ Ser) {A : Set α} (hA : A ∈ sect P) :
    P ⥏ A ≠ rNull ↔ A.Nonempty ∧ A ∉ (one : Set (Set α)) := by
  constructor
  · intro hn
    have hne : A.Nonempty := by
      by_contra h0; rw [Set.not_nonempty_iff_eq_empty] at h0; subst h0
      exact hn (b2_fres_empty P)
    exact ⟨hne, fun h1 => hn ((b2_fres_null_iff h hA hne).2 h1)⟩
  · rintro ⟨hne, h1⟩ e; exact h1 ((b2_fres_null_iff h hA hne).1 e)

/-- ✱213·162. \(\vdash :P_{\text{po}}\in \text{Ser}.\supset .\text{ᗡ}ʻP_{\varsigma }=P\unicode{x0294f}ʻʻ\text{sect}ʻP-\iota ʻ\dot{\Lambda}\) -/
theorem pm213_162 {P : α → α → Prop} (h : po P ∈ Ser) :
    codom (Psec P) = opL fres P ʻʻ sect P \ ι rNull := by
  have hJ := (b2_serPo h).1
  rw [pm213_143 h]
  ext Q
  rw [Set.mem_sdiff, b2_mem_opL_fres_img, b2_mem_opL_fres_img, b2_mem_iota]
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [Set.mem_sdiff, b2_mem_diff_iotaNull] at hA
    refine ⟨⟨A, hA.1.1, rfl⟩, (b2_fres_ne_null h hA.1.1).2 ⟨hA.1.2, ?_⟩⟩
    rintro ⟨x, rfl⟩
    exact hA.2 ⟨x, (b2_unit_sect hJ).1 hA.1.1, rfl⟩
  · rintro ⟨⟨A, hA, rfl⟩, hn⟩
    obtain ⟨hne, h1⟩ := (b2_fres_ne_null h hA).1 hn
    refine ⟨A, ⟨b2_mem_diff_iotaNull.2 ⟨hA, hne⟩, ?_⟩, rfl⟩
    rintro ⟨x, -, rfl⟩
    exact h1 ⟨x, rfl⟩

private theorem b2_fld_eq_codom {R : α → α → Prop} (h : refs Beg R = Λ) : fld R = codom R := by
  ext x
  refine ⟨fun hx => ?_, fun ⟨y, hy⟩ => ⟨y, Or.inr hy⟩⟩
  by_contra hc
  obtain ⟨y, hy | hy⟩ := hx
  · have : x ∈ refs Beg R := ⟨⟨y, hy⟩, hc⟩
    rw [h, Null_eq_empty] at this; exact this
  · exact hc ⟨y, hy⟩

/-- ✱213·163. \(\vdash :P_{\text{po}}\in \text{Ser}.\overrightarrow{B}ʻP=\Lambda .\supset .CʻP_{\varsigma }=P\unicode{x0294f}ʻʻ\text{sect}ʻP_\iota ʻ\dot{\Lambda} \)

**Status.** proved (reading): transcription error of the e-text, `sect'P_ι'Λ̇` for `sect'P − ι'Λ̇` (cf. ✱213·162, ✱213·164). -/
theorem pm213_163 {P : α → α → Prop} (h : po P ∈ Ser ∧ refs Beg P = Λ) :
    fld (Psec P) = opL fres P ʻʻ sect P \ ι rNull := by
  rw [b2_fld_eq_codom (pm213_156 h), pm213_162 h.1]

/-- ✱213·164. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.\overrightarrow{B}ʻP=\Lambda .\supset .\text{D}ʻP_{\varsigma }=P\unicode{x0294f}ʻʻ\text{sect}ʻP-\iota ʻ\dot{\Lambda} -\iota ʻP\\ &[*213·142·163·16]\end{align}\] -/
theorem pm213_164 {P : α → α → Prop} (h : po P ∈ Ser ∧ refs Beg P = Λ) :
    dom (Psec P) = (opL fres P ʻʻ sect P \ ι rNull) \ ι P := by
  obtain ⟨h, h0⟩ := h
  have hJ := (b2_serPo h).1
  rw [pm213_16]
  congr 1
  ext Q
  rw [Set.mem_sdiff, b2_mem_opL_fres_img, b2_mem_opL_fres_img, b2_mem_iota]
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [b2_mem_diff_iotaNull] at hA
    refine ⟨⟨A, hA.1, rfl⟩, (b2_fres_ne_null h hA.1).2 ⟨hA.2, ?_⟩⟩
    rintro ⟨x, rfl⟩
    have := (b2_unit_sect hJ).1 hA.1
    rw [h0, Null_eq_empty] at this; exact this
  · rintro ⟨⟨A, hA, rfl⟩, hn⟩
    exact ⟨A, b2_mem_diff_iotaNull.2 ⟨hA, ((b2_fres_ne_null h hA).1 hn).1⟩, rfl⟩

end S213

/-! ### Relation arithmetic helpers (from Part IV, ✱150–✱181; re-proved here)

Likeness through correlators, ordinal sums, `x ⇷ P`, `P ⇸ x`, `x ⇷̇ P`, `P ⇸̇ x`, `μ +̇ ν`,
`μ +̇ 1̇`, `1̇ +̇ μ`. -/

section B2RelHelpers

variable {α β γ δ : Type*}

private theorem b2r_img_empty (R : α → β → Prop) : R ʻʻ (∅ : Set β) = ∅ := by
  ext x; simp [img]

private theorem b2r_null_inter (A : Set α) : (Λ : Set α) ∩ A = ∅ := by
  rw [Null_eq_empty, Set.empty_inter]

private theorem b2r_not_mem_null (x : α) : x ∉ (Λ : Set α) := fun h => h rfl

private theorem b2r_inter_null_iff {G H : Set γ} : G ∩ H = Λ ↔ Disjoint G H := by
  rw [Null_eq_empty, Set.disjoint_iff_inter_eq_empty]

private theorem b2r_graph_relProd_graph (f : β → α) (g : γ → β) :
    graph f ⨾ graph g = graph (fun z => f (g z)) := by
  funext u z; apply propext
  constructor
  · rintro ⟨v, h1, h2⟩
    exact (h1 : u = f v).trans (congrArg f (h2 : v = g z))
  · intro h; exact ⟨g z, h, rfl⟩

/-- `x ∈ C'(S;Q)` when every member of `C'Q` has an `S`-referent. -/
private theorem b2r_mem_fld_semi {S : α → β → Prop} {Q : β → β → Prop}
    (hS : ∀ z, z ∈ fld Q → ∃ x, S x z) {x : α} :
    x ∈ fld (S ⁏ Q) ↔ ∃ z, z ∈ fld Q ∧ S x z := by
  constructor
  · rintro ⟨y, h | h⟩
    · obtain ⟨z, w, ⟨hxz, -⟩, hzw⟩ := (semi_apply S Q x y).1 h
      exact ⟨z, ⟨w, Or.inl hzw⟩, hxz⟩
    · obtain ⟨z, w, ⟨-, hxw⟩, hzw⟩ := (semi_apply S Q y x).1 h
      exact ⟨w, ⟨z, Or.inr hzw⟩, hxw⟩
  · rintro ⟨z, ⟨w, hzw | hwz⟩, hxz⟩
    · obtain ⟨y, hy⟩ := hS w ⟨z, Or.inr hzw⟩
      exact ⟨y, Or.inl ((semi_apply S Q x y).2 ⟨z, w, ⟨hxz, hy⟩, hzw⟩)⟩
    · obtain ⟨y, hy⟩ := hS w ⟨z, Or.inl hwz⟩
      exact ⟨y, Or.inr ((semi_apply S Q y x).2 ⟨w, z, ⟨hy, hxz⟩, hwz⟩)⟩

private theorem b2r_fld_semi_sub {S : α → β → Prop} {Q : β → β → Prop} {x : α}
    (h : x ∈ fld (S ⁏ Q)) : ∃ z, z ∈ fld Q ∧ S x z := by
  rcases h with ⟨y, h | h⟩
  · obtain ⟨z, w, ⟨hxz, -⟩, hzw⟩ := (semi_apply S Q x y).1 h
    exact ⟨z, ⟨w, Or.inl hzw⟩, hxz⟩
  · obtain ⟨z, w, ⟨-, hxw⟩, hzw⟩ := (semi_apply S Q y x).1 h
    exact ⟨w, ⟨z, Or.inr hzw⟩, hxw⟩

private theorem b2r_mem_fld_graph_semi {f : β → α} {Q : β → β → Prop} {u : α} :
    u ∈ fld (graph f ⁏ Q) ↔ ∃ z, z ∈ fld Q ∧ u = f z :=
  b2r_mem_fld_semi fun z _ => ⟨f z, rfl⟩

private theorem b2r_semi_congr {S T : α → β → Prop} {Q : β → β → Prop}
    (h : ∀ x z, z ∈ fld Q → (S x z ↔ T x z)) : S ⁏ Q = T ⁏ Q := by
  funext x y; apply propext
  rw [semi_apply, semi_apply]
  constructor
  · rintro ⟨z, w, ⟨h1, h2⟩, hq⟩
    exact ⟨z, w, ⟨(h x z ⟨w, Or.inl hq⟩).1 h1, (h y w ⟨z, Or.inr hq⟩).1 h2⟩, hq⟩
  · rintro ⟨z, w, ⟨h1, h2⟩, hq⟩
    exact ⟨z, w, ⟨(h x z ⟨w, Or.inl hq⟩).2 h1, (h y w ⟨z, Or.inr hq⟩).2 h2⟩, hq⟩

private theorem b2r_graph_semi_congr {f g : β → α} {Q : β → β → Prop}
    (h : ∀ z, z ∈ fld Q → f z = g z) : graph f ⁏ Q = graph g ⁏ Q :=
  b2r_semi_congr fun x z hz => by
    show x = f z ↔ x = g z
    rw [h z hz]

private theorem b2r_semi_rsum {S : α → β → Prop} {P Q : β → β → Prop}
    (hP : ∀ z, z ∈ fld P → ∃ x, S x z) (hQ : ∀ z, z ∈ fld Q → ∃ x, S x z) :
    S ⁏ (P ⤉ Q) = S ⁏ P ⤉ S ⁏ Q := by
  funext x y; apply propext
  rw [semi_apply, rsum_apply, semi_apply, semi_apply, b2r_mem_fld_semi hP, b2r_mem_fld_semi hQ]
  constructor
  · rintro ⟨z, w, ⟨h1, h2⟩, (hq | hq) | ⟨hz, hw⟩⟩
    · exact Or.inl (Or.inl ⟨z, w, ⟨h1, h2⟩, hq⟩)
    · exact Or.inl (Or.inr ⟨z, w, ⟨h1, h2⟩, hq⟩)
    · exact Or.inr ⟨⟨z, hz, h1⟩, ⟨w, hw, h2⟩⟩
  · rintro ((⟨z, w, ⟨h1, h2⟩, hq⟩ | ⟨z, w, ⟨h1, h2⟩, hq⟩) | ⟨⟨z, hz, h1⟩, ⟨w, hw, h2⟩⟩)
    · exact ⟨z, w, ⟨h1, h2⟩, Or.inl (Or.inl hq)⟩
    · exact ⟨z, w, ⟨h1, h2⟩, Or.inl (Or.inr hq)⟩
    · exact ⟨z, w, ⟨h1, h2⟩, Or.inr ⟨hz, hw⟩⟩

private theorem b2r_graph_semi_rsum (f : β → α) (P Q : β → β → Prop) :
    graph f ⁏ (P ⤉ Q) = graph f ⁏ P ⤉ graph f ⁏ Q :=
  b2r_semi_rsum (fun z _ => ⟨f z, rfl⟩) (fun z _ => ⟨f z, rfl⟩)

private theorem b2r_rsum_assoc (P Q R : α → α → Prop) : P ⤉ Q ⤉ R = P ⤉ (Q ⤉ R) := by
  funext x y; apply propext
  simp only [rsum_apply, fld_rsum, Set.mem_union]
  tauto

private theorem b2r_rsum_rNull (P : α → α → Prop) : P ⤉ rNull = P := by
  funext x y; apply propext
  simp only [rsum_apply]
  have h1 : ¬ (rNull : α → α → Prop) x y := rNull_apply x y
  have h2 : y ∉ fld (rNull : α → α → Prop) := by rintro ⟨z, h | h⟩ <;> exact rNull_apply _ _ h
  tauto

private theorem b2r_rNull_rsum (P : α → α → Prop) : rNull ⤉ P = P := by
  funext x y; apply propext
  simp only [rsum_apply]
  have h1 : ¬ (rNull : α → α → Prop) x y := rNull_apply x y
  have h2 : x ∉ fld (rNull : α → α → Prop) := by rintro ⟨z, h | h⟩ <;> exact rNull_apply _ _ h
  tauto

private theorem b2r_fld_rNull : fld (rNull : α → α → Prop) = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ ⟨_, h⟩ => h.elim (rNull_apply _ _) (rNull_apply _ _)

private theorem b2r_eq_rNull_of_fld {P : α → α → Prop} (h : fld P = ∅) : P = rNull := by
  funext x y; apply propext
  exact ⟨fun hxy => absurd (show x ∈ fld P from ⟨y, Or.inl hxy⟩) (h ▸ Set.notMem_empty x),
    fun hxy => absurd hxy (rNull_apply x y)⟩

private theorem b2r_rEx_iff_fld {P : α → α → Prop} : rEx P ↔ (fld P).Nonempty := by
  constructor
  · rintro ⟨x, y, h⟩; exact ⟨x, y, Or.inl h⟩
  · rintro ⟨x, y, h | h⟩
    · exact ⟨x, y, h⟩
    · exact ⟨y, x, h⟩

private theorem b2r_ne_rNull_iff {P : α → α → Prop} : P ≠ rNull ↔ rEx P := by
  constructor
  · intro h
    by_contra h'
    exact h (funext fun x => funext fun y => propext
      ⟨fun hxy => (h' ⟨x, y, hxy⟩).elim, fun hxy => absurd hxy (rNull_apply x y)⟩)
  · rintro ⟨x, y, hxy⟩ rfl; exact rNull_apply x y hxy

private theorem b2r_graph_semi_rNull (f : β → α) : graph f ⁏ (rNull : β → β → Prop) = rNull := by
  funext x y; apply propext
  rw [semi_apply]
  exact ⟨fun ⟨_, _, _, h⟩ => absurd h (rNull_apply _ _), fun h => absurd h (rNull_apply _ _)⟩

/-! #### Likeness through correlators -/

/-- `S;Q smor Q` when `S` is one-one on `C'Q` and every member of `C'Q` has a referent. -/
private theorem b2r_smor_semi_of {S : α → β → Prop} {Q : β → β → Prop}
    (h1 : ∀ x y z, z ∈ fld Q → S x z → S y z → x = y)
    (h2 : ∀ x z w, z ∈ fld Q → w ∈ fld Q → S x z → S x w → z = w)
    (hc : ∀ z, z ∈ fld Q → ∃ x, S x z) : smor (S ⁏ Q) Q := by
  refine ⟨S ↾ fld Q, ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨hx, hz⟩, ⟨hy, -⟩⟩; exact h1 x y z hz hx hy
  · rintro x z w ⟨⟨hz, hzQ⟩, ⟨hw, hwQ⟩⟩; exact h2 x z w hzQ hwQ hz hw
  · ext z
    exact ⟨fun hz => let ⟨x, hx⟩ := hc z hz; ⟨x, hx, hz⟩, fun ⟨_, _, hz⟩ => hz⟩
  · exact b2r_semi_congr (fun x z hz => ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩)

/-- The image of `Q` under a function injective on `C'Q` is like `Q` (cf. ✱151·61). -/
private theorem b2r_smor_graph {f : β → α} {Q : β → β → Prop}
    (hf : ∀ z w, z ∈ fld Q → w ∈ fld Q → f z = f w → z = w) : smor (graph f ⁏ Q) Q :=
  b2r_smor_semi_of (fun x y z _ hx hy => (hx : x = f z).trans (hy : y = f z).symm)
    (fun x z w hz hw hxz hxw => hf z w hz hw ((hxz : x = f z).symm.trans hxw))
    (fun z _ => ⟨f z, rfl⟩)

private theorem b2r_smor_graph_inj {f : β → α} (hf : Function.Injective f) (Q : β → β → Prop) :
    smor (graph f ⁏ Q) Q :=
  b2r_smor_graph fun _ _ _ _ h => hf h

/-- Likeness of ordinal sums with exclusive fields (✱160·48). -/
private theorem b2r_smor_rsum {R S : α → α → Prop} {P Q : β → β → Prop} (hR : smor R P)
    (hS : smor S Q) (hRS : Disjoint (fld R) (fld S)) (hPQ : Disjoint (fld P) (fld Q)) :
    smor (R ⤉ S) (P ⤉ Q) := by
  obtain ⟨T₁, ⟨hT₁, hc₁⟩, rfl⟩ := hR
  obtain ⟨T₂, ⟨hT₂, hc₂⟩, rfl⟩ := hS
  obtain ⟨a₁, b₁⟩ := mem_arrow_one_one.1 hT₁
  obtain ⟨a₂, b₂⟩ := mem_arrow_one_one.1 hT₂
  have e₁ : ∀ z, z ∈ fld P ↔ ∃ x, T₁ x z := fun z => by rw [hc₁]; rfl
  have e₂ : ∀ z, z ∈ fld Q ↔ ∃ x, T₂ x z := fun z => by rw [hc₂]; rfl
  have k₁ : T₁ ⁏ P = (T₁ ⊍ T₂) ⁏ P := b2r_semi_congr fun x z hz =>
    ⟨Or.inl, fun h => h.elim id fun h2 =>
      absurd ((e₂ z).2 ⟨x, h2⟩) (Set.disjoint_left.1 hPQ hz)⟩
  have k₂ : T₂ ⁏ Q = (T₁ ⊍ T₂) ⁏ Q := b2r_semi_congr fun x z hz =>
    ⟨Or.inr, fun h => h.elim (fun h1 =>
      absurd ((e₁ z).2 ⟨x, h1⟩) (Set.disjoint_right.1 hPQ hz)) id⟩
  have hP' : ∀ z, z ∈ fld P → ∃ x, (T₁ ⊍ T₂) x z := fun z hz =>
    let ⟨x, hx⟩ := (e₁ z).1 hz; ⟨x, Or.inl hx⟩
  have hQ' : ∀ z, z ∈ fld Q → ∃ x, (T₁ ⊍ T₂) x z := fun z hz =>
    let ⟨x, hx⟩ := (e₂ z).1 hz; ⟨x, Or.inr hx⟩
  have hd₁ : ∀ x z, T₁ x z → x ∈ fld (T₁ ⁏ P) := fun x z h =>
    (b2r_mem_fld_semi fun z hz => (e₁ z).1 hz).2 ⟨z, (e₁ z).2 ⟨x, h⟩, h⟩
  have hd₂ : ∀ x z, T₂ x z → x ∈ fld (T₂ ⁏ Q) := fun x z h =>
    (b2r_mem_fld_semi fun z hz => (e₂ z).1 hz).2 ⟨z, (e₂ z).2 ⟨x, h⟩, h⟩
  rw [k₁, k₂, ← b2r_semi_rsum hP' hQ']
  refine b2r_smor_semi_of ?_ ?_ ?_
  · rintro x y z - (hx | hx) (hy | hy)
    · exact a₁ x y z ⟨hx, hy⟩
    · exact absurd ((e₂ z).2 ⟨y, hy⟩) (Set.disjoint_left.1 hPQ ((e₁ z).2 ⟨x, hx⟩))
    · exact absurd ((e₂ z).2 ⟨x, hx⟩) (Set.disjoint_left.1 hPQ ((e₁ z).2 ⟨y, hy⟩))
    · exact a₂ x y z ⟨hx, hy⟩
  · rintro x z w - - (hz | hz) (hw | hw)
    · exact b₁ x z w ⟨hz, hw⟩
    · exact absurd (hd₂ x w hw) (Set.disjoint_left.1 hRS (hd₁ x z hz))
    · exact absurd (hd₂ x z hz) (Set.disjoint_left.1 hRS (hd₁ x w hw))
    · exact b₂ x z w ⟨hz, hw⟩
  · intro z hz
    rw [fld_rsum] at hz
    exact hz.elim (hP' z) (hQ' z)

/-- The fields of two like relations are similar; a correlator restricted. -/
private theorem b2r_smor_corr {R : α → α → Prop} {P : β → β → Prop} (h : smor R P) :
    ∃ T : α → β → Prop, ((∀ x y z, T x z → T y z → x = y) ∧ (∀ x z w, T x z → T x w → z = w)) ∧
      (∀ z, z ∈ fld P ↔ ∃ x, T x z) ∧ R = T ⁏ P := by
  obtain ⟨T, ⟨hT, hc⟩, rfl⟩ := h
  obtain ⟨a, b⟩ := mem_arrow_one_one.1 hT
  exact ⟨T, ⟨fun x y z h1 h2 => a x y z ⟨h1, h2⟩, fun x z w h1 h2 => b x z w ⟨h1, h2⟩⟩,
    fun z => by rw [hc]; rfl, rfl⟩

private theorem b2r_smor_rNull_iff' {P : α → α → Prop} : smor P (rNull : β → β → Prop) ↔ P = rNull := by
  constructor
  · intro h
    obtain ⟨e, -⟩ := smor_iff_exists_equiv.1 h
    apply b2r_eq_rNull_of_fld
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    obtain ⟨_, _, h⟩ := e ⟨x, hx⟩
    exact h.elim (rNull_apply _ _) (rNull_apply _ _)
  · rintro rfl
    refine ⟨rNull, ⟨mem_arrow_one_one.2 ⟨fun _ _ _ h => absurd h.1 (rNull_apply _ _),
      fun _ _ _ h => absurd h.1 (rNull_apply _ _)⟩, ?_⟩, ?_⟩
    · rw [b2r_fld_rNull]; ext z; simp only [Set.mem_empty_iff_false, false_iff]
      rintro ⟨_, h⟩; exact rNull_apply _ _ h
    · funext x y; apply propext; rw [semi_apply]
      exact ⟨fun h => absurd h (rNull_apply _ _), fun ⟨_, _, h, _⟩ => absurd h.1 (rNull_apply _ _)⟩

private theorem b2r_smor_preserves {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q)
    (hP : rEx P) : rEx Q := by
  obtain ⟨x, y, hxy⟩ := hP
  obtain ⟨e, he⟩ := smor_iff_exists_equiv.1 h
  exact ⟨e ⟨x, y, Or.inl hxy⟩, e ⟨y, x, Or.inr hxy⟩, (he _ _).1 hxy⟩


private theorem b2r_coupleR_iota (B : Set β) :
    (coupleR B ⨾ iota : (Set α → Set β → Prop) → α → Prop) = graph (fun x => ι x ↓ B) :=
  b2r_graph_relProd_graph (fun X => X ↓ B) (refs I)

private theorem b2r_coupleL_iota (A : Set α) :
    (coupleL A ⨾ iota : (Set α → Set β → Prop) → β → Prop) = graph (fun y => A ↓ ι y) :=
  b2r_graph_relProd_graph (fun Y => A ↓ Y) (refs I)

/-- `P + Q` as the sum of two images of `P` and `Q` (✱180·01). -/
private theorem b2r_rplus_eq (P : α → α → Prop) (Q : β → β → Prop) :
    P +ᵣ Q = graph (fun x => ι x ↓ (Λ ∩ fld Q)) ⁏ P ⤉ graph (fun y => (Λ ∩ fld P) ↓ ι y) ⁏ Q := by
  show (coupleR (Λ ∩ fld Q) ⁏ iota ⁏ P) ⤉ (coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q) = _
  rw [semi_semi, semi_semi, b2r_coupleR_iota, b2r_coupleL_iota]

private theorem b2r_smor_lft (P : α → α → Prop) (B : Set β) :
    smor (graph (fun x => ι x ↓ B) ⁏ P) P :=
  b2r_smor_graph_inj (fun _ _ h => unitCls_injective (couple_eq_couple_iff.1 h).1) P

private theorem b2r_smor_rgt (A : Set α) (Q : β → β → Prop) :
    smor (graph (fun y => A ↓ ι y) ⁏ Q) Q :=
  b2r_smor_graph_inj (fun _ _ h => unitCls_injective (couple_eq_couple_iff.1 h).2) Q

private theorem b2r_disj_lft_rgt (P : α → α → Prop) (Q : β → β → Prop) (A : Set α) (B : Set β) :
    Disjoint (fld (graph (fun x => ι x ↓ (Λ ∩ B)) ⁏ P)) (fld (graph (fun y => A ↓ ι y) ⁏ Q)) := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  obtain ⟨x, -, rfl⟩ := b2r_mem_fld_graph_semi.1 hu
  obtain ⟨y, -, h⟩ := b2r_mem_fld_graph_semi.1 hu'
  have := (couple_eq_couple_iff.1 h).2
  have hy : y ∈ Λ ∩ B := this ▸ (rfl : y = y)
  exact b2r_not_mem_null y hy.1

/-- `P + Q` is the sum of two exclusive relations like `P` and `Q`. -/
private theorem b2r_rplus_split (P : α → α → Prop) (Q : β → β → Prop) :
    ∃ L R, P +ᵣ Q = L ⤉ R ∧ (smor L P ∧ smor R Q) ∧ Disjoint (fld L) (fld R) :=
  ⟨_, _, b2r_rplus_eq P Q, ⟨b2r_smor_lft P _, b2r_smor_rgt _ Q⟩, b2r_disj_lft_rgt P Q _ _⟩

private theorem b2r_smor_rsum_rplus {R S : δ → δ → Prop} {P : α → α → Prop} {Q : β → β → Prop}
    (hR : smor R P) (hS : smor S Q) (h : Disjoint (fld R) (fld S)) : smor (R ⤉ S) (P +ᵣ Q) := by
  obtain ⟨L, R', e, ⟨hL, hR'⟩, hd⟩ := b2r_rplus_split P Q
  rw [e]
  exact b2r_smor_rsum (smor_trans hR (smor_symm hL)) (smor_trans hS (smor_symm hR')) h hd

/-- `R smor P . S smor Q . ⊃ . R + S smor P + Q` (✱180·15). -/
private theorem b2r_smor_rplus {R : γ → γ → Prop} {S : δ → δ → Prop} {P : α → α → Prop}
    {Q : β → β → Prop} (hR : smor R P) (hS : smor S Q) : smor (R +ᵣ S) (P +ᵣ Q) := by
  obtain ⟨L, R', e, ⟨hL, hR'⟩, hd⟩ := b2r_rplus_split R S
  rw [e]
  exact b2r_smor_rsum_rplus (smor_trans hL hR) (smor_trans hR' hS) hd

private theorem b2r_smor_rsum_iff {P Q : α → α → Prop} (hPQ : Disjoint (fld P) (fld Q))
    {Z : β → β → Prop} : smor Z (P ⤉ Q) ↔
      ∃ R S, ((smor R P ∧ smor S Q) ∧ Disjoint (fld R) (fld S)) ∧ Z = R ⤉ S := by
  constructor
  · intro h
    obtain ⟨T, ⟨a, b⟩, hc, rfl⟩ := b2r_smor_corr h
    have hP : ∀ z, z ∈ fld P → ∃ x, T x z := fun z hz =>
      (hc z).1 (by rw [fld_rsum]; exact Or.inl hz)
    have hQ : ∀ z, z ∈ fld Q → ∃ x, T x z := fun z hz =>
      (hc z).1 (by rw [fld_rsum]; exact Or.inr hz)
    refine ⟨T ⁏ P, T ⁏ Q, ⟨⟨b2r_smor_semi_of (fun x y z _ => a x y z)
      (fun x z w _ _ => b x z w) hP, b2r_smor_semi_of (fun x y z _ => a x y z)
      (fun x z w _ _ => b x z w) hQ⟩, ?_⟩, b2r_semi_rsum hP hQ⟩
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨z, hz, hxz⟩ := b2r_fld_semi_sub hx
    obtain ⟨w, hw, hxw⟩ := b2r_fld_semi_sub hx'
    rw [b x z w hxz hxw] at hz
    exact Set.disjoint_left.1 hPQ hz hw
  · rintro ⟨R, S, ⟨⟨hR, hS⟩, hd⟩, rfl⟩
    exact b2r_smor_rsum hR hS hd hPQ

private theorem b2r_smor_rplus_iff {P : α → α → Prop} {Q : β → β → Prop} {Z : γ → γ → Prop} :
    smor Z (P +ᵣ Q) ↔
      ∃ R S, ((smor R P ∧ smor S Q) ∧ Disjoint (fld R) (fld S)) ∧ Z = R ⤉ S := by
  obtain ⟨L, R', e, ⟨hL, hR'⟩, hd⟩ := b2r_rplus_split P Q
  constructor
  · intro h
    rw [e] at h
    obtain ⟨R, S, ⟨⟨hR, hS⟩, hRS⟩, rfl⟩ := (b2r_smor_rsum_iff hd).1 h
    exact ⟨R, S, ⟨⟨smor_trans hR hL, smor_trans hS hR'⟩, hRS⟩, rfl⟩
  · rintro ⟨R, S, ⟨⟨hR, hS⟩, hRS⟩, rfl⟩
    exact b2r_smor_rsum_rplus hR hS hRS

private theorem b2r_smor_rplus_rNull (P : α → α → Prop) : smor (P +ᵣ (rNull : β → β → Prop)) P := by
  rw [b2r_rplus_eq, b2r_graph_semi_rNull, b2r_rsum_rNull]; exact b2r_smor_lft P _

private theorem b2r_smor_rNull_rplus (P : α → α → Prop) : smor ((rNull : β → β → Prop) +ᵣ P) P := by
  rw [b2r_rplus_eq, b2r_graph_semi_rNull, b2r_rNull_rsum]; exact b2r_smor_rgt _ P

private theorem b2r_rsum_mono {P P' Q Q' : α → α → Prop} (h1 : P ⪽ P') (h2 : Q ⪽ Q') :
    P ⤉ Q ⪽ P' ⤉ Q' := by
  rintro x y ((h | h) | ⟨hx, hy⟩)
  · exact Or.inl (Or.inl (h1 _ _ h))
  · exact Or.inl (Or.inr (h2 _ _ h))
  · exact Or.inr ⟨fld_mono h1 hx, fld_mono h2 hy⟩

private theorem b2r_rplus_sub_rV (P : α → α → Prop) (Q : β → β → Prop) :
    P +ᵣ Q ⪽ (rV : α → α → Prop) +ᵣ (rV : β → β → Prop) := by
  rw [b2r_rplus_eq, b2r_rplus_eq, b2r_null_inter, b2r_null_inter, b2r_null_inter, b2r_null_inter]
  exact b2r_rsum_mono (semi_mono _ fun _ _ _ => ⟨rfl, rfl⟩) (semi_mono _ fun _ _ _ => ⟨rfl, rfl⟩)

private theorem b2r_rEx_rplus_left {P : α → α → Prop} (Q : β → β → Prop) (h : rEx P) :
    rEx (P +ᵣ Q) := by
  obtain ⟨L, R, e, ⟨hL, -⟩, -⟩ := b2r_rplus_split P Q
  obtain ⟨x, y, hxy⟩ := b2r_smor_preserves (smor_symm hL) h
  rw [e]; exact ⟨x, y, Or.inl (Or.inl hxy)⟩

private theorem b2r_rEx_rplus_right (P : α → α → Prop) {Q : β → β → Prop} (h : rEx Q) :
    rEx (P +ᵣ Q) := by
  obtain ⟨L, R, e, ⟨-, hR⟩, -⟩ := b2r_rplus_split P Q
  obtain ⟨x, y, hxy⟩ := b2r_smor_preserves (smor_symm hR) h
  rw [e]; exact ⟨x, y, Or.inl (Or.inr hxy)⟩

/-! #### `μ +̇ ν` -/

private theorem b2r_n₀r_nrAdd_n₀r (P : α → α → Prop) (Q : β → β → Prop) :
    (n₀r P ∔ n₀r Q : Set (γ → γ → Prop)) = nr γ (P +ᵣ Q) := by
  ext Z
  constructor
  · rintro ⟨P', Q', ⟨hP, hQ⟩, h⟩
    exact smor_trans h (b2r_smor_rplus (n₀r_eq_n₀r_iff.1 hP.symm) (n₀r_eq_n₀r_iff.1 hQ.symm))
  · intro h; exact ⟨P, Q, ⟨rfl, rfl⟩, h⟩

private theorem b2r_graph_semi_couple (f : β → α) (x y : β) : graph f ⁏ (x ↓ y) = f x ↓ f y := by
  funext u v; apply propext
  rw [semi_apply]
  constructor
  · rintro ⟨z, w, ⟨hu, hv⟩, hz, hw⟩
    exact ⟨(hu : u = f z).trans (congrArg f hz), (hv : v = f w).trans (congrArg f hw)⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨x, y, ⟨rfl, rfl⟩, rfl, rfl⟩

private theorem b2r_fld_couple {x y : α} : fld (x ↓ y) = {x, y} := by
  ext z
  constructor
  · rintro ⟨w, ⟨h, -⟩ | ⟨-, h⟩⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨y, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨x, Or.inr ⟨rfl, rfl⟩⟩

/-- `a ≠ b . x ≠ y . ⊃ . a ↓ b smor x ↓ y` (cf. ✱153·21). -/
private theorem b2r_smor_couple {a b : α} {x y : β} (hab : a ≠ b) (hxy : x ≠ y) :
    smor (a ↓ b) (x ↓ y) := by
  classical
  have e : graph (fun z => if z = x then a else b) ⁏ (x ↓ y) = a ↓ b := by
    rw [b2r_graph_semi_couple]; simp [hxy.symm]
  rw [← e]
  refine b2r_smor_graph fun z w hz hw h => ?_
  rw [b2r_fld_couple] at hz hw
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  · rfl
  · simp [hxy.symm] at h; exact absurd h hab
  · simp [hxy.symm] at h; exact absurd h.symm hab
  · rfl

private theorem b2r_mem_fld_addLast {P : α → α → Prop} {x z : α} :
    z ∈ fld (P ⇸ x) ↔ (z ∈ fld P ∨ z = x) ∧ rEx P := by
  constructor
  · rintro ⟨w, (h | ⟨h, -⟩) | (h | ⟨h, rfl⟩)⟩
    · exact ⟨Or.inl ⟨w, Or.inl h⟩, z, w, h⟩
    · exact ⟨Or.inl h, b2r_rEx_iff_fld.2 ⟨z, h⟩⟩
    · exact ⟨Or.inl ⟨w, Or.inr h⟩, w, z, h⟩
    · exact ⟨Or.inr rfl, b2r_rEx_iff_fld.2 ⟨w, h⟩⟩
  · rintro ⟨h | rfl, hP⟩
    · exact ⟨x, Or.inl (Or.inr ⟨h, rfl⟩)⟩
    · obtain ⟨u, hu⟩ := b2r_rEx_iff_fld.1 hP
      exact ⟨u, Or.inr (Or.inr ⟨hu, rfl⟩)⟩

private theorem b2r_mem_fld_addFirst {P : α → α → Prop} {x z : α} :
    z ∈ fld (x ⇷ P) ↔ (z ∈ fld P ∨ z = x) ∧ rEx P := by
  constructor
  · rintro ⟨w, (⟨h, hw⟩ | h) | (⟨-, h⟩ | h)⟩
    · exact ⟨Or.inr h, b2r_rEx_iff_fld.2 ⟨w, hw⟩⟩
    · exact ⟨Or.inl ⟨w, Or.inl h⟩, z, w, h⟩
    · exact ⟨Or.inl h, b2r_rEx_iff_fld.2 ⟨z, h⟩⟩
    · exact ⟨Or.inl ⟨w, Or.inr h⟩, w, z, h⟩
  · rintro ⟨h | rfl, hP⟩
    · exact ⟨x, Or.inr (Or.inl ⟨rfl, h⟩)⟩
    · obtain ⟨u, hu⟩ := b2r_rEx_iff_fld.1 hP
      exact ⟨u, Or.inl (Or.inl ⟨rfl, hu⟩)⟩

private theorem b2r_graph_semi_addLast (f : β → α) (P : β → β → Prop) (x : β) :
    graph f ⁏ (P ⇸ x) = graph f ⁏ P ⇸ f x := by
  funext u v; apply propext
  rw [semi_apply, addLast_apply, semi_apply, b2r_mem_fld_graph_semi]
  constructor
  · rintro ⟨z, w, ⟨hu, hv⟩, h | ⟨hz, rfl⟩⟩
    · exact Or.inl ⟨z, w, ⟨hu, hv⟩, h⟩
    · exact Or.inr ⟨⟨z, hz, hu⟩, hv⟩
  · rintro (⟨z, w, ⟨hu, hv⟩, h⟩ | ⟨⟨z, hz, hu⟩, hv⟩)
    · exact ⟨z, w, ⟨hu, hv⟩, Or.inl h⟩
    · exact ⟨z, x, ⟨hu, hv⟩, Or.inr ⟨hz, rfl⟩⟩

private theorem b2r_graph_semi_addFirst (f : β → α) (x : β) (P : β → β → Prop) :
    graph f ⁏ (x ⇷ P) = f x ⇷ graph f ⁏ P := by
  funext u v; apply propext
  rw [semi_apply, addFirst_apply, semi_apply, b2r_mem_fld_graph_semi]
  constructor
  · rintro ⟨z, w, ⟨hu, hv⟩, ⟨rfl, hw⟩ | h⟩
    · exact Or.inl ⟨hu, w, hw, hv⟩
    · exact Or.inr ⟨z, w, ⟨hu, hv⟩, h⟩
  · rintro (⟨hu, w, hw, hv⟩ | ⟨z, w, ⟨hu, hv⟩, h⟩)
    · exact ⟨x, w, ⟨hu, hv⟩, Or.inl ⟨rfl, hw⟩⟩
    · exact ⟨z, w, ⟨hu, hv⟩, Or.inr h⟩

private theorem b2r_addLast_rNull (x : α) : (rNull : α → α → Prop) ⇸ x = rNull := by
  funext u v; apply propext
  rw [addLast_apply, b2r_fld_rNull]
  exact ⟨fun h => h.elim id fun h => absurd h.1 (Set.notMem_empty u), fun h => Or.inl h⟩

private theorem b2r_fld_cnv' (P : α → α → Prop) : fld P˘ = fld P := by
  ext x; constructor <;> rintro ⟨y, h | h⟩ <;> exact ⟨y, by tauto⟩

private theorem b2r_addFirst_eq_cnv (x : α) (P : α → α → Prop) : x ⇷ P = (P˘ ⇸ x)˘ := by
  funext u v; apply propext
  show (x ⇷ P) u v ↔ (P˘ ⇸ x) v u
  rw [addFirst_apply, addLast_apply, b2r_fld_cnv']
  show _ ↔ P u v ∨ _
  tauto

private theorem b2r_smor_cnv {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q) : smor P˘ Q˘ := by
  obtain ⟨e, he⟩ := smor_iff_exists_equiv.1 h
  refine smor_iff_exists_equiv.2 ⟨(Set.equivOfEq (b2r_fld_cnv' P)).trans
    (e.trans (Set.equivOfEq (b2r_fld_cnv' Q).symm)), fun a b => ?_⟩
  exact he ⟨b, by rw [← b2r_fld_cnv']; exact b.2⟩ ⟨a, by rw [← b2r_fld_cnv']; exact a.2⟩

private theorem b2r_rEx_cnv {P : α → α → Prop} : rEx P˘ ↔ rEx P :=
  ⟨fun ⟨x, y, h⟩ => ⟨y, x, h⟩, fun ⟨x, y, h⟩ => ⟨y, x, h⟩⟩

/-- `A smor B . a ∼∈ C'A . b ∼∈ C'B . ⊃ . A ⇸ a smor B ⇸ b` (✱161·31). -/
private theorem b2r_smor_addLast {A : α → α → Prop} {B : β → β → Prop} {a : α} {b : β}
    (h : smor A B) (ha : a ∉ fld A) (hb : b ∉ fld B) : smor (A ⇸ a) (B ⇸ b) := by
  obtain ⟨T, ⟨t1, t2⟩, hc, rfl⟩ := b2r_smor_corr h
  have hcB : ∀ z, z ∈ fld B → ∃ x, T x z := fun z hz => (hc z).1 hz
  have hdom : ∀ x z, T x z → x ∈ fld (T ⁏ B) := fun x z hxz =>
    (b2r_mem_fld_semi hcB).2 ⟨z, (hc z).2 ⟨x, hxz⟩, hxz⟩
  let T' : α → β → Prop := fun u z => T u z ∨ (u = a ∧ z = b)
  have e : T ⁏ B ⇸ a = T' ⁏ (B ⇸ b) := by
    funext u v; apply propext
    rw [addLast_apply, semi_apply, semi_apply, b2r_mem_fld_semi hcB]
    constructor
    · rintro (⟨z, w, ⟨hu, hv⟩, hzw⟩ | ⟨⟨z, hz, hu⟩, rfl⟩)
      · exact ⟨z, w, ⟨Or.inl hu, Or.inl hv⟩, Or.inl hzw⟩
      · exact ⟨z, b, ⟨Or.inl hu, Or.inr ⟨rfl, rfl⟩⟩, Or.inr ⟨hz, rfl⟩⟩
    · rintro ⟨z, w, ⟨hu, hv⟩, hzw | ⟨hz, rfl⟩⟩
      · have hz : z ∈ fld B := ⟨w, Or.inl hzw⟩
        have hw : w ∈ fld B := ⟨z, Or.inr hzw⟩
        have hu' : T u z := hu.resolve_right fun ⟨_, e⟩ => hb (e ▸ hz)
        have hv' : T v w := hv.resolve_right fun ⟨_, e⟩ => hb (e ▸ hw)
        exact Or.inl ⟨z, w, ⟨hu', hv'⟩, hzw⟩
      · have hu' : T u z := hu.resolve_right fun ⟨_, e⟩ => hb (e ▸ hz)
        rcases hv with hv | ⟨rfl, -⟩
        · exact absurd ((hc w).2 ⟨v, hv⟩) hb
        · exact Or.inr ⟨⟨z, hz, hu'⟩, rfl⟩
  rw [e]
  refine b2r_smor_semi_of ?_ ?_ ?_
  · rintro x y z - (hx | ⟨hxa, hzb⟩) (hy | ⟨hya, hzb'⟩)
    · exact t1 x y z hx hy
    · exact absurd (hzb' ▸ (hc z).2 ⟨x, hx⟩) hb
    · exact absurd (hzb ▸ (hc z).2 ⟨y, hy⟩) hb
    · exact hxa.trans hya.symm
  · rintro x z w - - (hz | ⟨hxa, hzb⟩) (hw | ⟨hxa', hwb⟩)
    · exact t2 x z w hz hw
    · exact absurd (hxa' ▸ hdom x z hz) ha
    · exact absurd (hxa ▸ hdom x w hw) ha
    · exact hzb.trans hwb.symm
  · intro z hz
    obtain ⟨hz | rfl, -⟩ := b2r_mem_fld_addLast.1 hz
    · obtain ⟨x, hx⟩ := hcB z hz; exact ⟨x, Or.inl hx⟩
    · exact ⟨a, Or.inr ⟨rfl, rfl⟩⟩

private theorem b2r_smor_addFirst {A : α → α → Prop} {B : β → β → Prop} {a : α} {b : β}
    (h : smor A B) (ha : a ∉ fld A) (hb : b ∉ fld B) : smor (a ⇷ A) (b ⇷ B) := by
  rw [b2r_addFirst_eq_cnv, b2r_addFirst_eq_cnv]
  exact b2r_smor_cnv (b2r_smor_addLast (b2r_smor_cnv h) (by rwa [b2r_fld_cnv']) (by rwa [b2r_fld_cnv']))

/-- `A ⇸ a smor B ⇸ b . a ∼∈ C'A . b ∼∈ C'B . ⊃ . A smor B` (cf. ✱161·33). -/
private theorem b2r_smor_addLast_cancel {A : α → α → Prop} {B : β → β → Prop} {a : α} {b : β}
    (h : smor (A ⇸ a) (B ⇸ b)) (ha : a ∉ fld A) (hb : b ∉ fld B) : smor A B := by
  by_cases hA : rEx A
  swap
  · have hA0 : A = rNull := by by_contra h'; exact hA (b2r_ne_rNull_iff.1 h')
    subst hA0
    rw [b2r_addLast_rNull] at h
    have hB0 := b2r_smor_rNull_iff'.1 (smor_symm h)
    have : B = rNull := by
      funext u v; apply propext
      exact ⟨fun huv => by
        have : (B ⇸ b) u v := Or.inl huv
        rw [hB0] at this; exact absurd this (rNull_apply _ _), fun h => absurd h (rNull_apply _ _)⟩
    subst this; exact b2r_smor_rNull_iff'.2 rfl
  obtain ⟨T, ⟨t1, t2⟩, hc, hAT⟩ := b2r_smor_corr h
  have hBne : rEx B := by
    obtain ⟨u, v, huv⟩ := b2r_smor_preserves h (by obtain ⟨u, v, huv⟩ := hA; exact ⟨u, v, Or.inl huv⟩)
    rcases huv with huv | ⟨hu, -⟩
    · exact ⟨u, v, huv⟩
    · exact b2r_rEx_iff_fld.2 ⟨u, hu⟩
  have hbF : b ∈ fld (B ⇸ b) := b2r_mem_fld_addLast.2 ⟨Or.inr rfl, hBne⟩
  have hnoA : ∀ v, ¬ (A ⇸ a) a v := fun v hv =>
    hv.elim (fun h => ha ⟨v, Or.inl h⟩) (fun h => ha h.1)
  have hTab : T a b := by
    have haF : a ∈ fld (T ⁏ (B ⇸ b)) := by
      rw [← hAT]; exact b2r_mem_fld_addLast.2 ⟨Or.inr rfl, hA⟩
    obtain ⟨z, hz, haz⟩ := b2r_fld_semi_sub haF
    obtain ⟨hz' | rfl, -⟩ := b2r_mem_fld_addLast.1 hz
    · obtain ⟨y, hy⟩ := (hc b).1 hbF
      have : (T ⁏ (B ⇸ b)) a y := (semi_apply _ _ _ _).2 ⟨z, b, ⟨haz, hy⟩, Or.inr ⟨hz', rfl⟩⟩
      rw [← hAT] at this
      exact absurd this (hnoA y)
    · exact haz
  have e : A = T ⁏ B := by
    funext u v; apply propext
    constructor
    · intro huv
      have : (T ⁏ (B ⇸ b)) u v := by rw [← hAT]; exact Or.inl huv
      obtain ⟨z, w, ⟨hu, hv⟩, hzw | ⟨-, rfl⟩⟩ := (semi_apply _ _ _ _).1 this
      · exact (semi_apply _ _ _ _).2 ⟨z, w, ⟨hu, hv⟩, hzw⟩
      · have := t1 v a w hv hTab
        subst this
        exact absurd ⟨u, Or.inr huv⟩ ha
    · intro huv
      obtain ⟨z, w, ⟨hu, hv⟩, hzw⟩ := (semi_apply _ _ _ _).1 huv
      have : (T ⁏ (B ⇸ b)) u v := (semi_apply _ _ _ _).2 ⟨z, w, ⟨hu, hv⟩, Or.inl hzw⟩
      rw [← hAT] at this
      rcases this with h' | ⟨-, hva⟩
      · exact h'
      · rw [hva] at hv
        have := t2 a w b hv hTab
        subst this
        exact absurd ⟨z, Or.inr hzw⟩ hb
  rw [e]
  exact b2r_smor_semi_of (fun x y z _ => t1 x y z) (fun x z w _ _ => t2 x z w)
    (fun z hz => (hc z).1 (b2r_mem_fld_addLast.2 ⟨Or.inl hz, hBne⟩))

private theorem b2r_smor_addFirst_cancel {A : α → α → Prop} {B : β → β → Prop} {a : α} {b : β}
    (h : smor (a ⇷ A) (b ⇷ B)) (ha : a ∉ fld A) (hb : b ∉ fld B) : smor A B := by
  rw [b2r_addFirst_eq_cnv, b2r_addFirst_eq_cnv] at h
  have := b2r_smor_addLast_cancel (b2r_smor_cnv h) (by rwa [b2r_fld_cnv']) (by rwa [b2r_fld_cnv'])
  exact b2r_smor_cnv this


private theorem b2r_clsT_null (x : β) : clsT (Λ : Set β) x = ∅ := by rw [clsT_eq, Null_eq_empty]

private theorem b2r_addLastDot_eq (P : α → α → Prop) (x : β) :
    addLastDot P x = graph (fun y => ι y ↓ (∅ : Set β)) ⁏ P ⇸ ((∅ : Set α) ↓ ι x) := by
  show (coupleR (clsT Λ x) ⁏ iota ⁏ P) ⇸ ((Λ ∩ fld P) ↓ ι x) = _
  rw [semi_semi, b2r_coupleR_iota, b2r_clsT_null, b2r_null_inter]

private theorem b2r_addFirstDot_eq (x : β) (P : α → α → Prop) :
    addFirstDot x P = (ι x ↓ (∅ : Set α)) ⇷ graph (fun y => (∅ : Set β) ↓ ι y) ⁏ P := by
  show (ι x ↓ (Λ ∩ fld P)) ⇷ (coupleL (clsT Λ x) ⁏ iota ⁏ P) = _
  rw [semi_semi, b2r_coupleL_iota, b2r_clsT_null, b2r_null_inter]

private theorem b2r_inj_dotL : Function.Injective (fun y : α => ι y ↓ (∅ : Set β)) :=
  fun _ _ h => unitCls_injective (couple_eq_couple_iff.1 h).1

private theorem b2r_inj_dotR : Function.Injective (fun y : α => (∅ : Set β) ↓ ι y) :=
  fun _ _ h => unitCls_injective (couple_eq_couple_iff.1 h).2

private theorem b2r_unitCls_ne_empty (y : α) : ι y ≠ ∅ := fun h => (h ▸ (rfl : y = y) : y ∈ (∅ : Set α))

private theorem b2r_notin_dotL (P : α → α → Prop) (x : β) :
    ((∅ : Set α) ↓ ι x) ∉ fld (graph (fun y => ι y ↓ (∅ : Set β)) ⁏ P) := by
  intro h
  obtain ⟨y, -, e⟩ := b2r_mem_fld_graph_semi.1 h
  exact b2r_unitCls_ne_empty y (couple_eq_couple_iff.1 e).1.symm

private theorem b2r_notin_dotR (x : β) (P : α → α → Prop) :
    (ι x ↓ (∅ : Set α)) ∉ fld (graph (fun y => (∅ : Set β) ↓ ι y) ⁏ P) := by
  intro h
  obtain ⟨y, -, e⟩ := b2r_mem_fld_graph_semi.1 h
  exact b2r_unitCls_ne_empty y (couple_eq_couple_iff.1 e).2.symm

private theorem b2r_addLastDot_split (P : α → α → Prop) (x : β) :
    ∃ L e, addLastDot P x = L ⇸ e ∧ smor L P ∧ e ∉ fld L :=
  ⟨_, _, b2r_addLastDot_eq P x, b2r_smor_graph_inj b2r_inj_dotL P, b2r_notin_dotL P x⟩

private theorem b2r_addFirstDot_split (x : β) (P : α → α → Prop) :
    ∃ L e, addFirstDot x P = e ⇷ L ∧ smor L P ∧ e ∉ fld L :=
  ⟨_, _, b2r_addFirstDot_eq x P, b2r_smor_graph_inj b2r_inj_dotR P, b2r_notin_dotR x P⟩

private theorem b2r_smor_addLastDot {β' γ' : Type*} {P : α → α → Prop} {P' : γ' → γ' → Prop}
    (h : smor P P') (x : β) (x' : β') : smor (addLastDot P x) (addLastDot P' x') := by
  obtain ⟨L, e, h1, h2, h3⟩ := b2r_addLastDot_split P x
  obtain ⟨L', e', h1', h2', h3'⟩ := b2r_addLastDot_split P' x'
  rw [h1, h1']
  exact b2r_smor_addLast (smor_trans h2 (smor_trans h (smor_symm h2'))) h3 h3'

private theorem b2r_smor_addFirstDot {β' γ' : Type*} {P : α → α → Prop} {P' : γ' → γ' → Prop}
    (h : smor P P') (x : β) (x' : β') : smor (addFirstDot x P) (addFirstDot x' P') := by
  obtain ⟨L, e, h1, h2, h3⟩ := b2r_addFirstDot_split x P
  obtain ⟨L', e', h1', h2', h3'⟩ := b2r_addFirstDot_split x' P'
  rw [h1, h1']
  exact b2r_smor_addFirst (smor_trans h2 (smor_trans h (smor_symm h2'))) h3 h3'

/-- `Q smor P . y ∼∈ C'Q . ⊃ . Q ⇸ y smor P ⇸̇ x` (✱181·13). -/
private theorem b2r_smor_addLast_dot {Q : δ → δ → Prop} {P : α → α → Prop} {y : δ} (h : smor Q P)
    (hy : y ∉ fld Q) (x : β) : smor (Q ⇸ y) (addLastDot P x) := by
  obtain ⟨L, e, h1, h2, h3⟩ := b2r_addLastDot_split P x
  rw [h1]; exact b2r_smor_addLast (smor_trans h (smor_symm h2)) hy h3

private theorem b2r_smor_addFirst_dot {Q : δ → δ → Prop} {P : α → α → Prop} {y : δ} (h : smor Q P)
    (hy : y ∉ fld Q) (x : β) : smor (y ⇷ Q) (addFirstDot x P) := by
  obtain ⟨L, e, h1, h2, h3⟩ := b2r_addFirstDot_split x P
  rw [h1]; exact b2r_smor_addFirst (smor_trans h (smor_symm h2)) hy h3

private theorem b2r_rEx_addLast_iff {P : α → α → Prop} {x : α} : rEx (P ⇸ x) ↔ rEx P := by
  constructor
  · rintro ⟨u, v, h | ⟨hu, -⟩⟩
    · exact ⟨u, v, h⟩
    · exact b2r_rEx_iff_fld.2 ⟨u, hu⟩
  · rintro ⟨u, v, h⟩; exact ⟨u, v, Or.inl h⟩

private theorem b2r_rEx_addFirst_iff {P : α → α → Prop} {x : α} : rEx (x ⇷ P) ↔ rEx P := by
  constructor
  · rintro ⟨u, v, ⟨-, hv⟩ | h⟩
    · exact b2r_rEx_iff_fld.2 ⟨v, hv⟩
    · exact ⟨u, v, h⟩
  · rintro ⟨u, v, h⟩; exact ⟨u, v, Or.inr h⟩

private theorem b2r_rEx_addLastDot_iff {P : α → α → Prop} {x : β} : rEx (addLastDot P x) ↔ rEx P := by
  obtain ⟨L, e, h1, h2, -⟩ := b2r_addLastDot_split P x
  rw [h1, b2r_rEx_addLast_iff]
  exact ⟨b2r_smor_preserves h2, b2r_smor_preserves (smor_symm h2)⟩

private theorem b2r_rEx_addFirstDot_iff {P : α → α → Prop} {x : β} :
    rEx (addFirstDot x P) ↔ rEx P := by
  obtain ⟨L, e, h1, h2, -⟩ := b2r_addFirstDot_split x P
  rw [h1, b2r_rEx_addFirst_iff]
  exact ⟨b2r_smor_preserves h2, b2r_smor_preserves (smor_symm h2)⟩

private theorem b2r_addLast_mono {P P' : α → α → Prop} (h : P ⪽ P') (x : α) : P ⇸ x ⪽ P' ⇸ x := by
  rintro u v (huv | ⟨hu, hv⟩)
  · exact Or.inl (h _ _ huv)
  · exact Or.inr ⟨fld_mono h hu, hv⟩

private theorem b2r_addFirst_mono {P P' : α → α → Prop} (h : P ⪽ P') (x : α) : x ⇷ P ⪽ x ⇷ P' := by
  rintro u v (⟨hu, hv⟩ | huv)
  · exact Or.inl ⟨hu, fld_mono h hv⟩
  · exact Or.inr (h _ _ huv)

/-! #### `μ +̇ 1̇`, `1̇ +̇ μ` -/

/-- `N₀r'P +̇ 1̇ = Nr'(P ⇸̇ x)` (✱181·22). -/
private theorem b2r_nrAddOne_n₀r (P : α → α → Prop) (x : β) :
    (nrAddOne β (n₀r P) : Set (γ → γ → Prop)) = nr γ (addLastDot P x) := by
  ext Z
  constructor
  · rintro ⟨P', x', hP', hZ⟩
    exact smor_trans hZ (b2r_smor_addLastDot (n₀r_eq_n₀r_iff.1 hP') x' x)
  · intro h; exact ⟨P, x, rfl, h⟩

private theorem b2r_nrOneAdd_n₀r (P : α → α → Prop) (x : β) :
    (nrOneAdd β (n₀r P) : Set (γ → γ → Prop)) = nr γ (addFirstDot x P) := by
  ext Z
  constructor
  · rintro ⟨P', x', hP', hZ⟩
    exact smor_trans hZ (b2r_smor_addFirstDot (n₀r_eq_n₀r_iff.1 hP') x' x)
  · intro h; exact ⟨P, x, rfl, h⟩

/-- `(A ⇸ d) ⤉ T = A ⤉ (d ⇷ T)` for existent `A`, `T`. -/
private theorem b2_addLast_rsum {A T : α → α → Prop} (hA : rEx A) (hT : rEx T) (d : α) :
    (A ⇸ d) ⤉ T = A ⤉ (d ⇷ T) := by
  funext u v; apply propext
  simp only [rsum_apply, addLast_apply, addFirst_apply, b2r_mem_fld_addLast, b2r_mem_fld_addFirst,
    hA, hT, and_true]
  tauto

/-- `A ⇸ d ⇸ e = A ⤉ (d ↓ e)` for existent `A`. -/
private theorem b2_addLast_addLast {A : α → α → Prop} (hA : rEx A) (d e : α) :
    A ⇸ d ⇸ e = A ⤉ (d ↓ e) := by
  funext u v; apply propext
  have hf : ∀ z, z ∈ fld (d ↓ e) ↔ z = d ∨ z = e := fun z =>
    ⟨fun ⟨_, h⟩ => h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2),
      fun h => h.elim (fun h => ⟨e, Or.inl ⟨h, rfl⟩⟩) (fun h => ⟨d, Or.inr ⟨rfl, h⟩⟩)⟩
  simp only [rsum_apply, addLast_apply, b2r_mem_fld_addLast, couple_apply, hf, hA, and_true]
  tauto

private theorem b2_tg_smor {P : α → α → Prop} {Q : β → β → Prop} (f : fld Q ≃ fld P)
    (hf : ∀ a b : fld Q, Q a b ↔ P (f a) (f b)) {x y : β} (hxy : Relation.TransGen Q x y) :
    ∃ hx : x ∈ fld Q, ∃ hy : y ∈ fld Q, Relation.TransGen P (f ⟨x, hx⟩) (f ⟨y, hy⟩) := by
  induction hxy with
  | single h =>
    exact ⟨⟨_, Or.inl h⟩, ⟨_, Or.inr h⟩, Relation.TransGen.single ((hf ⟨_, _⟩ ⟨_, _⟩).1 h)⟩
  | tail _ h ih =>
    obtain ⟨hx, hb, ih⟩ := ih
    exact ⟨hx, ⟨_, Or.inr h⟩, ih.tail ((hf ⟨_, hb⟩ ⟨_, ⟨_, Or.inr h⟩⟩).1 h)⟩

/-- Likeness preserves `R_po ⊂̇ J`. -/
private theorem b2_poJ_of_smor {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q)
    (hJ : po P ⪽ J) : po Q ⪽ J := by
  obtain ⟨f, hf⟩ := smor_iff_exists_equiv.1 (smor_symm h)
  intro x y hxy hxy'
  have e : x = y := hxy'
  subst e
  obtain ⟨hx, hy, ht⟩ := b2_tg_smor f hf (po_iff_transGen.1 hxy)
  exact hJ _ _ (po_iff_transGen.2 ht) rfl

end B2RelHelpers

section S213b

variable {α : Type u}

/-- `ς'P_* = Λ ⇷ (ς'P_*)⥏(−ι'Λ)` when `P_po` is serial: the null section begins `ς'P_*`
(✱212·171·172). -/
private theorem b2_segSer_split {P : α → α → Prop} (h : po P ∈ Ser) :
    segSer (anc P) = (∅ : Set α) ⇷ (segSer (anc P) ⥏ (ι Λ)ᶜ) := by
  have hJ := (b2_serPo h).1
  funext A B; apply propext
  rw [addFirst_apply, b2_segSer_anc, b2_S0]
  constructor
  · rintro ⟨⟨hA, hB⟩, hd⟩
    have hBne : B.Nonempty := hd.mono Set.sdiff_subset
    by_cases hA0 : A.Nonempty
    · exact Or.inr ⟨⟨⟨hA, hA0⟩, hB, hBne⟩, hd⟩
    · refine Or.inl ⟨Set.not_nonempty_iff_eq_empty.1 hA0, ?_⟩
      by_cases hBf : B = fld P
      · have : B ∈ codom (segSer (anc P) ⥏ (ι Λ)ᶜ) := by
          rw [b2_codom_S0 h, Set.mem_sdiff, b2_mem_diff_iotaNull]
          refine ⟨⟨hB, hBne⟩, ?_⟩
          rintro ⟨c, hc, hcB⟩
          obtain ⟨z, hz, hzc⟩ := b2_unit_ne_fld hJ hc
          have hcB' : B = ι c := hcB
          exact hzc (by rw [← hcB', hBf]; exact hz)
        obtain ⟨C, hC⟩ := this
        exact ⟨C, Or.inr hC⟩
      · have : B ∈ dom (segSer (anc P) ⥏ (ι Λ)ᶜ) := by
          rw [b2_dom_S0, Set.mem_sdiff, b2_mem_diff_iotaNull, b2_mem_iota]
          exact ⟨⟨hB, hBne⟩, hBf⟩
        obtain ⟨C, hC⟩ := this
        exact ⟨C, Or.inl hC⟩
  · rintro (⟨e, hB⟩ | ⟨⟨hA, hB⟩, hd⟩)
    · obtain ⟨hBs, z, hz⟩ := b2_mem_fld_S0 hB
      rw [e]
      exact ⟨⟨b2_empty_mem_sect P, hBs⟩, z, hz, fun h => h⟩
    · exact ⟨⟨hA.1, hB.1⟩, hd⟩

/-- `(ς'P_*)⥏(ᗡ'ς'P_*) = (ς'P_*)⥏(−ι'Λ)`. -/
private theorem b2_segSer_codom_eq {P : α → α → Prop} :
    segSer (anc P) ⥏ codom (segSer (anc P)) = segSer (anc P) ⥏ (ι Λ)ᶜ := by
  have hc : ∀ A, A ∈ codom (segSer (anc P)) ↔ A ∈ sect P ∧ A.Nonempty := by
    intro A
    constructor
    · rintro ⟨C, hC⟩
      obtain ⟨⟨-, hA⟩, z, hz, -⟩ := b2_segSer_anc.1 hC
      exact ⟨hA, z, hz⟩
    · rintro ⟨hA, z, hz⟩
      exact ⟨∅, b2_segSer_anc.2 ⟨⟨b2_empty_mem_sect P, hA⟩, z, hz, fun h => h⟩⟩
  funext A B; apply propext
  rw [b2_S0, b2_fres_apply, hc, hc, b2_segSer_anc]
  constructor
  · rintro ⟨⟨hA, -, hd⟩, hB⟩; exact ⟨⟨hA, hB⟩, hd⟩
  · rintro ⟨⟨hA, hB⟩, hd⟩; exact ⟨⟨hA, ⟨hA.1, hB.1⟩, hd⟩, hB⟩

private theorem b2_null_not_fld_S0 {P : α → α → Prop} :
    (∅ : Set α) ∉ fld (segSer (anc P) ⥏ (ι Λ)ᶜ) := fun hm =>
  (b2_mem_fld_S0 hm).2.ne_empty rfl

/-- ✱213·17. \[\begin{align}\vdash :P_{\text{po}}\in \text{Ser}.\supset .\text{Nr}ʻ\varsigma ʻP_{*}=\dot{1} \dot{+} &\text{Nr}ʻP_{\varsigma }.\\ &\text{Nr}ʻ(\varsigma P_{*})\unicode{x0294f}(\text{ᗡ}ʻ\varsigma ʻP_{*})=\text{Nr}ʻP_{\varsigma }\end{align}\]

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): the
type `β` of the apparent `x` of ✱181·021 (`1̇ +̇ μ`) is `[Nonempty β]` (for an empty `β`, `1̇ +̇ μ = Λ`). -/
theorem pm213_17 (γ : Type v) (β : Type w) [Nonempty β] {P : α → α → Prop} (h : po P ∈ Ser) :
    nr γ (segSer (anc P)) = (nrOneAdd β (n₀r (Psec P)) : Set (γ → γ → Prop)) ∧
      nr γ (segSer (anc P) ⥏ codom (segSer (anc P))) = nr γ (Psec P) := by
  have h152 := smor_symm (pm213_152 h)
  refine ⟨?_, ?_⟩
  · obtain ⟨x⟩ := ‹Nonempty β›
    rw [b2r_nrOneAdd_n₀r (Psec P) x]
    apply nr_eq_nr_of_smor
    rw [b2_segSer_split h]
    exact b2r_smor_addFirst_dot h152 b2_null_not_fld_S0 x
  · rw [b2_segSer_codom_eq]
    exact nr_eq_nr_of_smor h152

/-- ✱213·171. \(\vdash \colon\ldotp P_{\text{po}},Q_{\text{po}}\in \text{Ser}.\supset :P_{\varsigma }\,\text{smor}\, Q_{\varsigma }. \equiv .\varsigma ʻP_{*} \,\text{smor}\, \varsigma ʻQ_{*}\) -/
theorem pm213_171 {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    (h : po P ∈ Ser ∧ po Q ∈ Ser) :
    smor (Psec P) (Psec Q) ↔ smor (segSer (anc P)) (segSer (anc Q)) := by
  obtain ⟨hP, hQ⟩ := h
  rw [b2_segSer_split hP, b2_segSer_split hQ]
  constructor
  · intro hPQ
    exact b2r_smor_addFirst (smor_trans (smor_symm (pm213_152 hP))
      (smor_trans hPQ (pm213_152 hQ))) b2_null_not_fld_S0 b2_null_not_fld_S0
  · intro H
    exact smor_trans (pm213_152 hP) (smor_trans
      (b2r_smor_addFirst_cancel H b2_null_not_fld_S0 b2_null_not_fld_S0) (smor_symm (pm213_152 hQ)))


section Transport

variable {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}

private theorem tS_fun (hS : S ∈ smorbar P Q) {a : α} {z z' : β} (h1 : S a z) (h2 : S a z') : z = z' :=
  (mem_arrow_one_one.1 hS.1.1).2 a z z' ⟨h1, h2⟩

private theorem tS_inj (hS : S ∈ smorbar P Q) {a a' : α} {z : β} (h1 : S a z) (h2 : S a' z) : a = a' :=
  (mem_arrow_one_one.1 hS.1.1).1 a a' z ⟨h1, h2⟩

private theorem tS_key (hS : S ∈ smorbar P Q) {a b : α} {z w : β} (ha : S a z) (hb : S b w) :
    P a b ↔ Q z w := by
  rw [hS.2, semi_apply]
  constructor
  · rintro ⟨z', w', ⟨ha', hb'⟩, h⟩
    rw [tS_fun hS ha ha', tS_fun hS hb hb']; exact h
  · intro h; exact ⟨z, w, ⟨ha, hb⟩, h⟩

private theorem tS_cod (hS : S ∈ smorbar P Q) {z : β} (hz : z ∈ fld Q) : ∃ a, S a z := by
  rw [hS.1.2] at hz; exact hz

private theorem tS_fldQ (hS : S ∈ smorbar P Q) {a : α} {z : β} (h : S a z) : z ∈ fld Q := by
  rw [hS.1.2]; exact ⟨a, h⟩

private theorem tS_fldP (hS : S ∈ smorbar P Q) {a : α} {z : β} (h : S a z) : a ∈ fld P := by
  obtain ⟨w, hw | hw⟩ := tS_fldQ hS h
  · obtain ⟨b, hb⟩ := tS_cod hS ⟨z, Or.inr hw⟩
    exact ⟨b, Or.inl ((tS_key hS h hb).2 hw)⟩
  · obtain ⟨b, hb⟩ := tS_cod hS ⟨z, Or.inl hw⟩
    exact ⟨b, Or.inr ((tS_key hS hb h).2 hw)⟩

private theorem tS_dom (hS : S ∈ smorbar P Q) {a : α} (ha : a ∈ fld P) : ∃ z, S a z := by
  rw [hS.2] at ha
  obtain ⟨b, hb | hb⟩ := ha
  · obtain ⟨z, w, ⟨haz, -⟩, -⟩ := (semi_apply _ _ _ _).1 hb; exact ⟨z, haz⟩
  · obtain ⟨z, w, ⟨-, haw⟩, -⟩ := (semi_apply _ _ _ _).1 hb; exact ⟨w, haw⟩

private theorem tS_mem_img (hS : S ∈ smorbar P Q) {a : α} {z : β} (h : S a z) {B : Set β} :
    a ∈ S ʻʻ B ↔ z ∈ B := by
  constructor
  · rintro ⟨z', hz', h'⟩; rw [tS_fun hS h h']; exact hz'
  · intro hz; exact ⟨z, hz, h⟩

private theorem tS_max (hS : S ∈ smorbar P Q) {a : α} {z : β} (h : S a z) {B : Set β} :
    maxP P a (S ʻʻ B) ↔ maxP Q z B := by
  rw [maxP_iff, maxP_iff, tS_mem_img hS h]
  constructor
  · rintro ⟨⟨hz, -⟩, hn⟩
    refine ⟨⟨hz, tS_fldQ hS h⟩, fun w hw hzw => ?_⟩
    obtain ⟨b, hb⟩ := tS_cod hS ⟨z, Or.inr hzw⟩
    exact hn b ⟨w, hw, hb⟩ ((tS_key hS h hb).2 hzw)
  · rintro ⟨⟨hz, -⟩, hn⟩
    refine ⟨⟨hz, tS_fldP hS h⟩, fun y ⟨w, hw, hyw⟩ hay => hn w hw ((tS_key hS h hyw).1 hay)⟩

private theorem tS_seq (hS : S ∈ smorbar P Q) {a : α} {z : β} (h : S a z) {B : Set β} :
    seqP P a (S ʻʻ B) ↔ seqP Q z B := by
  rw [seqP_iff, seqP_iff]
  have csP : ∀ c v, S c v → ((∀ y, y ∈ S ʻʻ B ∩ fld P → P y c) ↔ ∀ w, w ∈ B ∩ fld Q → Q w v) := by
    intro c v hcv
    constructor
    · rintro H w ⟨hw, hwf⟩
      obtain ⟨y, hy⟩ := tS_cod hS hwf
      exact (tS_key hS hy hcv).1 (H y ⟨⟨w, hw, hy⟩, tS_fldP hS hy⟩)
    · rintro H y ⟨⟨w, hw, hyw⟩, -⟩
      exact (tS_key hS hyw hcv).2 (H w ⟨hw, tS_fldQ hS hyw⟩)
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    refine ⟨⟨(csP a z h).1 h1, tS_fldQ hS h⟩, fun v hv hvz => ?_⟩
    obtain ⟨c, hc⟩ := tS_cod hS ⟨z, Or.inl hvz⟩
    exact h2 c ((csP c v hc).2 hv) ((tS_key hS hc h).2 hvz)
  · rintro ⟨⟨h1, -⟩, h2⟩
    refine ⟨⟨(csP a z h).2 h1, tS_fldP hS h⟩, fun c hc hca => ?_⟩
    obtain ⟨v, hv⟩ := tS_dom hS ⟨a, Or.inl hca⟩
    exact h2 v ((csP c v hv).1 hc) ((tS_key hS hv h).1 hca)

private theorem tS_sect (hS : S ∈ smorbar P Q) {B : Set β} (hB : B ∈ sect Q) : S ʻʻ B ∈ sect P := by
  refine ⟨fun a ⟨w, _, haw⟩ => tS_fldP hS haw, ?_⟩
  rintro c ⟨a, ⟨w, hw, haw⟩, hca⟩
  obtain ⟨v, hv⟩ := tS_dom hS ⟨a, Or.inl hca⟩
  exact ⟨v, b2_sect_P hB ((tS_key hS hv haw).1 hca) hw, hv⟩

end Transport

section Transport2

variable {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}

private theorem tS_cnv (hS : S ∈ smorbar P Q) : S ∈ smorbar P˘ Q˘ := by
  refine ⟨⟨hS.1.1, by rw [fld_cnv]; exact hS.1.2⟩, ?_⟩
  funext x y; apply propext
  show P y x ↔ (S ⁏ Q˘) x y
  rw [hS.2, semi_apply, semi_apply]
  constructor
  · rintro ⟨z, w, ⟨h1, h2⟩, h⟩; exact ⟨w, z, ⟨h2, h1⟩, h⟩
  · rintro ⟨z, w, ⟨h1, h2⟩, h⟩; exact ⟨w, z, ⟨h2, h1⟩, h⟩

private theorem tS_min (hS : S ∈ smorbar P Q) {a : α} {z : β} (h : S a z) {C : Set β} :
    minP P a (S ʻʻ C) ↔ minP Q z C := tS_max (tS_cnv hS) h

private theorem tS_exMax (hS : S ∈ smorbar P Q) {C : Set β} :
    (∃ m, maxP P m (S ʻʻ C)) ↔ ∃ w, maxP Q w C := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨w, hw⟩ := tS_dom hS (maxP_iff.1 hm).1.2
    exact ⟨w, (tS_max hS hw).1 hm⟩
  · rintro ⟨w, hw⟩
    obtain ⟨m, hm⟩ := tS_cod hS (maxP_iff.1 hw).1.2
    exact ⟨m, (tS_max hS hm).2 hw⟩

private theorem tS_lt (hS : S ∈ smorbar P Q) {a : α} {z : β} (h : S a z) {C : Set β} :
    ltP P a (S ʻʻ C) ↔ ltP Q z C := by
  rw [ltP_iff, ltP_iff, tS_seq hS h, tS_exMax hS]

private theorem tS_limax (hS : S ∈ smorbar P Q) {a : α} {z : β} (h : S a z) {C : Set β} :
    limaxP P a (S ʻʻ C) ↔ limaxP Q z C :=
  or_congr (tS_max hS h) (tS_lt hS h)

private theorem tS_back (hS : S ∈ smorbar P Q) {B : Set α} (hB : B ⊆ fld P) : S ʻʻ (S˘ ʻʻ B) = B := by
  ext x
  constructor
  · rintro ⟨z, ⟨b, hb, hbz⟩, hxz⟩
    rw [tS_inj hS hxz hbz]; exact hb
  · intro hx
    obtain ⟨z, hz⟩ := tS_dom hS (hB hx)
    exact ⟨z, ⟨x, hx, hz⟩, hz⟩

private theorem tS_deriv (hS : S ∈ smorbar P Q) {a : α} {z : β} (h : S a z) {A : Set α} :
    a ∈ derivCls P A ↔ z ∈ derivCls Q (S˘ ʻʻ A) := by
  constructor
  · rintro ⟨B, ⟨hBA, b, hb⟩, hlt⟩
    have hBf : B ⊆ fld P := fun x hx => (hBA hx).2
    rw [← tS_back hS hBf, tS_lt hS h] at hlt
    obtain ⟨w, hw⟩ := tS_dom hS (hBf hb)
    refine ⟨S˘ ʻʻ B, ⟨fun c ⟨b', hb', hc⟩ => ⟨⟨b', (hBA hb').1, hc⟩, tS_fldQ hS hc⟩,
      w, b, hb, hw⟩, hlt⟩
  · rintro ⟨C, ⟨hCA, c, hc⟩, hlt⟩
    rw [← tS_lt hS h] at hlt
    obtain ⟨b, hb⟩ := tS_cod hS (hCA hc).2
    refine ⟨S ʻʻ C, ⟨fun x ⟨c', hc', hxc'⟩ => ⟨?_, tS_fldP hS hxc'⟩, b, c, hc, hb⟩, hlt⟩
    obtain ⟨a', ha', ha'c'⟩ := (hCA hc').1
    rw [tS_inj hS hxc' ha'c']; exact ha'

end Transport2

private theorem b2_tS_fres {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    (hS : S ∈ smorbar P Q) (D : Set β) : P ⥏ (S ʻʻ D) = S ⁏ (Q ⥏ D) := by
  funext x y; apply propext
  rw [semi_apply]
  constructor
  · rintro ⟨⟨⟨z, hz, hxz⟩, hxy⟩, ⟨w, hw, hyw⟩⟩
    exact ⟨z, w, ⟨hxz, hyw⟩, ⟨hz, (tS_key hS hxz hyw).1 hxy⟩, hw⟩
  · rintro ⟨z, w, ⟨hxz, hyw⟩, ⟨hz, hzw⟩, hw⟩
    exact ⟨⟨⟨z, hz, hxz⟩, (tS_key hS hxz hyw).2 hzw⟩, ⟨w, hw, hyw⟩⟩

private theorem b2_semi_inj {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    (hS : S ∈ smorbar P Q) {R1 R2 : β → β → Prop} (h1 : fld R1 ⊆ fld Q) (h2 : fld R2 ⊆ fld Q)
    (e : S ⁏ R1 = S ⁏ R2) : R1 = R2 := by
  have key : ∀ R R' : β → β → Prop, fld R ⊆ fld Q → S ⁏ R = S ⁏ R' → R ⪽ R' := by
    intro R R' hR e' z w hzw
    obtain ⟨a, ha⟩ := tS_cod hS (hR ⟨w, Or.inl hzw⟩)
    obtain ⟨b, hb⟩ := tS_cod hS (hR ⟨z, Or.inr hzw⟩)
    have : (S ⁏ R) a b := (semi_apply _ _ _ _).2 ⟨z, w, ⟨ha, hb⟩, hzw⟩
    rw [e'] at this
    obtain ⟨z', w', ⟨ha', hb'⟩, h'⟩ := (semi_apply _ _ _ _).1 this
    rw [tS_fun hS ha ha', tS_fun hS hb hb']; exact h'
  funext z w; exact propext ⟨key R1 R2 h1 e z w, key R2 R1 h2 e.symm z w⟩

/-- Likeness of `P` with `Q` carries `P_ς` to `Q_ς` (the proof of ✱213·172; no seriality is used). -/
private theorem b2_Psec_smor {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    (h : smor P Q) : smor (Psec P) (Psec Q) := by
  obtain ⟨S, hS⟩ := h
  have hS' : S˘ ∈ smorbar Q P := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_arrow_one_one]
      exact ⟨fun x y z hh => tS_fun hS hh.1 hh.2, fun x y z hh => tS_inj hS hh.1 hh.2⟩
    · ext a
      exact ⟨fun ha => tS_dom hS ha, fun ⟨z, hz⟩ => tS_fldP hS hz⟩
    · funext z w; apply propext
      rw [semi_apply]
      constructor
      · intro hzw
        obtain ⟨a, ha⟩ := tS_cod hS ⟨w, Or.inl hzw⟩
        obtain ⟨b, hb⟩ := tS_cod hS ⟨z, Or.inr hzw⟩
        exact ⟨a, b, ⟨ha, hb⟩, (tS_key hS ha hb).2 hzw⟩
      · rintro ⟨a, b, ⟨ha, hb⟩, hab⟩
        exact (tS_key hS ha hb).1 hab
  have fldsub : ∀ R, R ∈ fld (Psec Q) → fld R ⊆ fld Q := by
    intro R hR
    obtain ⟨G, -, rfl⟩ := b2_mem_fld_Psec hR
    rintro z ⟨w, hw | hw⟩
    · exact ⟨w, Or.inl hw.1.2⟩
    · exact ⟨w, Or.inr hw.1.2⟩
  refine ⟨fun X R => X = S ⁏ R ∧ R ∈ fld (Psec Q), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_arrow_one_one]
    refine ⟨fun X Y R hh => hh.1.1.trans hh.2.1.symm, fun X R1 R2 hh => ?_⟩
    exact b2_semi_inj hS (fldsub R1 hh.1.2) (fldsub R2 hh.2.2) (hh.1.1.symm.trans hh.2.1)
  · ext R
    exact ⟨fun hR => ⟨S ⁏ R, rfl, hR⟩, fun ⟨_, _, hR⟩ => hR⟩
  · funext X Y; apply propext
    rw [b2_Psec, semi_apply]
    constructor
    · rintro ⟨A, B, ⟨⟨hA, hB⟩, b, hbB, hbA⟩, rfl, rfl⟩
      set G := S˘ ʻʻ A
      set H := S˘ ʻʻ B
      have eA := tS_back hS hA.1.1
      have eB := tS_back hS hB.1.1
      have hG : G ∈ sect Q ∧ G.Nonempty := ⟨tS_sect hS' hA.1, let ⟨a, ha⟩ := hA.2;
        let ⟨z, hz⟩ := tS_dom hS (hA.1.1 ha); ⟨z, a, ha, hz⟩⟩
      have hH : H ∈ sect Q ∧ H.Nonempty := ⟨tS_sect hS' hB.1, let ⟨a, ha⟩ := hB.2;
        let ⟨z, hz⟩ := tS_dom hS (hB.1.1 ha); ⟨z, a, ha, hz⟩⟩
      obtain ⟨w, hw⟩ := tS_dom hS (hB.1.1 hbB)
      have hQ : Psec Q (Q ⥏ G) (Q ⥏ H) := b2_Psec.2 ⟨G, H, ⟨⟨hG, hH⟩, w, ⟨b, hbB, hw⟩,
        fun ⟨a, ha, haw⟩ => hbA (tS_inj hS hw haw ▸ ha)⟩, rfl, rfl⟩
      refine ⟨Q ⥏ G, Q ⥏ H, ⟨⟨?_, ⟨_, Or.inl hQ⟩⟩, ⟨?_, ⟨_, Or.inr hQ⟩⟩⟩, hQ⟩
      · rw [← b2_tS_fres hS G, eA]
      · rw [← b2_tS_fres hS H, eB]
    · rintro ⟨R1, R2, ⟨⟨rfl, -⟩, ⟨rfl, -⟩⟩, hR⟩
      obtain ⟨G, H, ⟨⟨hG, hH⟩, w, hwH, hwG⟩, rfl, rfl⟩ := b2_Psec.1 hR
      obtain ⟨b, hb⟩ := tS_cod hS (hH.1.1 hwH)
      refine ⟨S ʻʻ G, S ʻʻ H, ⟨⟨⟨tS_sect hS hG.1, ?_⟩, ⟨tS_sect hS hH.1, ?_⟩⟩, b, ⟨w, hwH, hb⟩,
        fun ⟨z, hz, hbz⟩ => hwG (tS_fun hS hb hbz ▸ hz)⟩, b2_tS_fres hS G |>.symm,
        b2_tS_fres hS H |>.symm⟩
      · obtain ⟨z, hz⟩ := hG.2
        obtain ⟨a, ha⟩ := tS_cod hS (hG.1.1 hz)
        exact ⟨a, z, hz, ha⟩
      · obtain ⟨z, hz⟩ := hH.2
        obtain ⟨a, ha⟩ := tS_cod hS (hH.1.1 hz)
        exact ⟨a, z, hz, ha⟩

/-- ✱213·172. \(\vdash :P_{\text{po}},Q_{\text{po}}\in \text{Ser}.P \,\,\text{smor}\, \,Q.\supset .P_{\varsigma } \,\text{smor}\, Q_{\varsigma } \quad[*212·72.*213·171]\) -/
theorem pm213_172 {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    (h : (po P ∈ Ser ∧ po Q ∈ Ser) ∧ smor P Q) : smor (Psec P) (Psec Q) :=
  b2_Psec_smor h.2

/-- ✱213·18. \(\vdash :P\in \text{connex} .R\in \text{D}ʻP_{\varsigma }.\supset .\exists !CʻP\cap pʻ\overleftarrow{P}ʻʻCʻR\) -/
theorem pm213_18 {P R : α → α → Prop} (h : P ∈ connex ∧ R ∈ dom (Psec P)) :
    (fld P ∩ prodCls (Rbwd P ʻʻ fld R)).Nonempty := by
  obtain ⟨hc, hR⟩ := h
  rw [pm213_141, b2_mem_opL_fres_img] at hR
  obtain ⟨A, hA, rfl⟩ := hR
  rw [Set.mem_sdiff, b2_mem_diff_iotaNull, b2_mem_iota] at hA
  obtain ⟨z, hz, hzA⟩ := (b2_sect_ne_fld hA.1.1).1 hA.2
  refine ⟨z, hz, mem_prodCls_Rbwd.2 fun y hy => ?_⟩
  have hyA := b2_fld_fres_sub P A hy
  rcases mem_connex.1 hc y z ⟨hA.1.1.1 hyA, hz⟩ with (h1 | rfl) | h1
  · exact h1
  · exact absurd hyA hzA
  · exact absurd (b2_sect_P hA.1.1 h1 hyA) hzA

private theorem b2_fres_mono {P : α → α → Prop} {A B : Set α} (h : A ⊆ B) : P ⥏ A ⪽ P ⥏ B :=
  fun _ _ hxy => ⟨⟨h hxy.1.1, hxy.1.2⟩, h hxy.2⟩

private theorem b2_rsub_antisymm {R S : α → α → Prop} (h1 : R ⪽ S) (h2 : S ⪽ R) : R = S := by
  funext x y; exact propext ⟨h1 x y, h2 x y⟩

/-- The three conditions of ✱213·2 are each equivalent to `α ⊂ β . α ≠ β`. -/
private theorem b2_213_2 {P : α → α → Prop} (h : po P ∈ Ser) {A B : Set α} (hA : A ∈ sect P)
    (hAne : A.Nonempty) (hB : B ∈ sect P) (hBne : B.Nonempty) :
    ((B \ A).Nonempty ↔ A ⊆ B ∧ A ≠ B) ∧ (rEx (P ⥏ B ∸ P ⥏ A) ↔ A ⊆ B ∧ A ≠ B) ∧
      (P ⥏ A ⪽ P ⥏ B ∧ P ⥏ A ≠ P ⥏ B ↔ A ⊆ B ∧ A ≠ B) := by
  have hc := b2_connex_of_ser h
  have e1 : (B \ A).Nonempty ↔ A ⊆ B ∧ A ≠ B := by
    constructor
    · intro hd
      refine ⟨b2_ssub_of_diff hc hA hB hd, ?_⟩
      rintro rfl; obtain ⟨z, hz, hz'⟩ := hd; exact hz' hz
    · rintro ⟨hs, hne⟩; exact b2_diff_of_ne hs hne
  refine ⟨e1, ?_, ?_⟩
  · constructor
    · rintro ⟨x, y, ⟨⟨⟨hx, hPxy⟩, hy⟩, hn⟩⟩
      have hs : A ⊆ B := by
        rcases b2_nested hc hA hB with hs | hs
        · exact hs
        · exact absurd ⟨⟨hs hx, hPxy⟩, hs hy⟩ hn
      refine ⟨hs, ?_⟩
      rintro rfl; exact hn ⟨⟨hx, hPxy⟩, hy⟩
    · intro hAB
      obtain ⟨z, hzB, hzA⟩ := e1.2 hAB
      have h1 : B ∉ (one : Set (Set α)) := by
        rintro ⟨b, rfl⟩
        obtain ⟨a, ha⟩ := hAne
        have hab := hAB.1 ha
        rw [b2_mem_iota] at hzB hab; subst hzB; subst hab; exact hzA ha
      have hz := (b2_fld_fres h hB hBne h1).symm ▸ hzB
      obtain ⟨w, hw | hw⟩ := hz
      · exact ⟨z, w, hw, fun h' => hzA h'.1.1⟩
      · exact ⟨w, z, hw, fun h' => hzA h'.2⟩
  · constructor
    · rintro ⟨hs, hne⟩
      have hAB : A ≠ B := fun e => hne (e ▸ rfl)
      rcases b2_nested hc hA hB with hs' | hs'
      · exact ⟨hs', hAB⟩
      · exact absurd (b2_rsub_antisymm hs (b2_fres_mono hs')) hne
    · rintro ⟨hs, hne⟩
      exact ⟨b2_fres_mono hs, fun e => hne (b2_fres_inj h hA hAne hB hBne e)⟩

/-- ✱213·2. \[\begin{align}\vdash \colon\ldotp &P_{\text{po}}\in \text{Ser}.\alpha ,\beta \in \text{sect}ʻP-\iota ʻ\Lambda .Q = P\unicode{x0294f}\alpha .R = P\unicode{x0294f}\beta .\supset :\\ &\exists !\beta -\alpha . \equiv .\dot{\exists} !R\dot{-} Q. \equiv .Q\,\unicode{x2abd}\, R.Q \neq R. \equiv .\alpha \subset \beta .\alpha \neq \beta\end{align}\] -/
theorem pm213_2 {P Q R : α → α → Prop} {A B : Set α}
    (h : ((po P ∈ Ser ∧ (A ∈ sect P \ ι Λ ∧ B ∈ sect P \ ι Λ)) ∧ Q = P ⥏ A) ∧ R = P ⥏ B) :
    (((B \ A).Nonempty ↔ rEx (R ∸ Q)) ∧ (rEx (R ∸ Q) ↔ Q ⪽ R ∧ Q ≠ R)) ∧
      (Q ⪽ R ∧ Q ≠ R ↔ A ⊆ B ∧ A ≠ B) := by
  obtain ⟨⟨⟨h, hA, hB⟩, rfl⟩, rfl⟩ := h
  rw [b2_mem_diff_iotaNull] at hA hB
  obtain ⟨e1, e2, e3⟩ := b2_213_2 h hA.1 hA.2 hB.1 hB.2
  exact ⟨⟨e1.trans e2.symm, e2.trans e3.symm⟩, e3⟩

private theorem b2_Psec_iff_img {P Q R : α → α → Prop} (h : po P ∈ Ser) (K : Set (Set α))
    (hK : opL fres P ʻʻ K = opL fres P ʻʻ (sect P \ ι Λ)) :
    (Psec P Q R ↔ (Q ∈ opL fres P ʻʻ K ∧ R ∈ opL fres P ʻʻ K) ∧ rEx (R ∸ Q)) ∧
      ((Q ∈ opL fres P ʻʻ K ∧ R ∈ opL fres P ʻʻ K) ∧ rEx (R ∸ Q) ↔
        ((Q ∈ opL fres P ʻʻ K ∧ R ∈ opL fres P ʻʻ K) ∧ Q ⪽ R) ∧ Q ≠ R) := by
  rw [hK]
  constructor
  · rw [pm213_1]
    constructor
    · rintro ⟨A, B, ⟨⟨⟨hA, hB⟩, hd⟩, rfl⟩, rfl⟩
      refine ⟨⟨⟨A, hA, rfl⟩, ⟨B, hB, rfl⟩⟩, ?_⟩
      exact (pm213_2 ⟨⟨⟨h, hA, hB⟩, rfl⟩, rfl⟩).1.1.1 hd
    · rintro ⟨⟨⟨A, hA, rfl⟩, ⟨B, hB, rfl⟩⟩, hx⟩
      exact ⟨A, B, ⟨⟨⟨hA, hB⟩, (pm213_2 ⟨⟨⟨h, hA, hB⟩, rfl⟩, rfl⟩).1.1.2 hx⟩, rfl⟩, rfl⟩
  · constructor
    · rintro ⟨⟨⟨A, hA, rfl⟩, ⟨B, hB, rfl⟩⟩, hx⟩
      have := (pm213_2 ⟨⟨⟨h, hA, hB⟩, rfl⟩, rfl⟩).1.2.1 hx
      exact ⟨⟨⟨⟨A, hA, rfl⟩, ⟨B, hB, rfl⟩⟩, this.1⟩, this.2⟩
    · rintro ⟨⟨⟨⟨A, hA, rfl⟩, ⟨B, hB, rfl⟩⟩, hs⟩, hne⟩
      exact ⟨⟨⟨A, hA, rfl⟩, ⟨B, hB, rfl⟩⟩,
        (pm213_2 ⟨⟨⟨h, hA, hB⟩, rfl⟩, rfl⟩).1.2.2 ⟨hs, hne⟩⟩

/-- ✱213·21. \[\begin{align}\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.\supset :QP_{\varsigma }R.&\equiv .Q,R\in P\unicode{x0294f}ʻʻ(\text{sect}ʻP-{℩}ʻ\Lambda ).\dot{\exists} !R\dot{-} Q.\\ &\equiv .Q,R\in P\unicode{x0294f}ʻʻ(\text{sect}ʻP-{℩}ʻ\Lambda ).Q\,\unicode{x2abd}\, R.Q\neq R\end{align}\] -/
theorem pm213_21 {P Q R : α → α → Prop} (h : po P ∈ Ser) :
    (Psec P Q R ↔ (Q ∈ opL fres P ʻʻ (sect P \ ι Λ) ∧ R ∈ opL fres P ʻʻ (sect P \ ι Λ)) ∧
        rEx (R ∸ Q)) ∧
      ((Q ∈ opL fres P ʻʻ (sect P \ ι Λ) ∧ R ∈ opL fres P ʻʻ (sect P \ ι Λ)) ∧ rEx (R ∸ Q) ↔
        ((Q ∈ opL fres P ʻʻ (sect P \ ι Λ) ∧ R ∈ opL fres P ʻʻ (sect P \ ι Λ)) ∧ Q ⪽ R) ∧
          Q ≠ R) :=
  b2_Psec_iff_img h _ rfl

/-- ✱213·22. \[\begin{align}&\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.\exists !\overrightarrow{B}ʻP.\supset :\\ &QP_{\varsigma }R.\equiv .Q,R\in P\unicode{x0294f}ʻʻ\text{sect}ʻP.\dot{\exists} !R\dot{-} Q.\equiv .Q,R\in P\unicode{x0294f}ʻʻ\text{sect}ʻP.Q\,\unicode{x2abd}\, R.Q\neq R\\ &[*213·21·161]\end{align}\] -/
theorem pm213_22 {P Q R : α → α → Prop} (h : po P ∈ Ser ∧ (refs Beg P).Nonempty) :
    (Psec P Q R ↔ (Q ∈ opL fres P ʻʻ sect P ∧ R ∈ opL fres P ʻʻ sect P) ∧ rEx (R ∸ Q)) ∧
      ((Q ∈ opL fres P ʻʻ sect P ∧ R ∈ opL fres P ʻʻ sect P) ∧ rEx (R ∸ Q) ↔
        ((Q ∈ opL fres P ʻʻ sect P ∧ R ∈ opL fres P ʻʻ sect P) ∧ Q ⪽ R) ∧ Q ≠ R) :=
  b2_Psec_iff_img h.1 _ (pm213_161 ⟨b2_J_of_ser h.1, h.2⟩).1

/-- ✱213·23. \[\begin{align}&\vdash \colon\ldotp P_{\text{po}}\in \text{connex} .Q,R\in CʻP_{\varsigma }.\supset :Q\,\unicode{x2abd}\, R.\lor.R\,\unicode{x2abd}\, Q\\ &[*213·1.*211·6·17.*36·24]\end{align}\] -/
theorem pm213_23 {P Q R : α → α → Prop}
    (h : po P ∈ connex ∧ (Q ∈ fld (Psec P) ∧ R ∈ fld (Psec P))) : Q ⪽ R ∨ R ⪽ Q := by
  obtain ⟨hc, hQ, hR⟩ := h
  obtain ⟨A, hA, rfl⟩ := b2_mem_fld_Psec hQ
  obtain ⟨B, hB, rfl⟩ := b2_mem_fld_Psec hR
  rcases b2_nested hc hA.1 hB.1 with hs | hs
  · exact Or.inl (b2_fres_mono hs)
  · exact Or.inr (b2_fres_mono hs)

private theorem b2_fres_fres {P : α → α → Prop} {A B : Set α} (h : A ⊆ B) : (P ⥏ B) ⥏ A = P ⥏ A := by
  funext x y; apply propext
  constructor
  · rintro ⟨⟨hx, ⟨⟨-, hxy⟩, -⟩⟩, hy⟩; exact ⟨⟨hx, hxy⟩, hy⟩
  · rintro ⟨⟨hx, hxy⟩, hy⟩; exact ⟨⟨hx, ⟨⟨h hx, hxy⟩, h hy⟩⟩, hy⟩

/-- ✱213·24. \(\vdash :\beta \in \text{sect}ʻP.R=P\unicode{x0294f}\beta .\supset .\text{sect}ʻR=\text{sect}ʻP\cap \text{Cl}ʻCʻR\) -/
theorem pm213_24 {P R : α → α → Prop} {B : Set α} (h : B ∈ sect P ∧ R = P ⥏ B) :
    sect R = sect P ∩ cl (fld R) := by
  obtain ⟨hB, rfl⟩ := h
  ext A
  rw [Set.mem_inter_iff, mem_cl]
  constructor
  · intro hA
    refine ⟨⟨fun z hz => ?_, ?_⟩, hA.1⟩
    · obtain ⟨w, hw | hw⟩ := hA.1 hz
      · exact ⟨w, Or.inl hw.1.2⟩
      · exact ⟨w, Or.inr hw.1.2⟩
    · rintro z ⟨y, hy, hzy⟩
      have hyB : y ∈ B := b2_fld_fres_sub P B (hA.1 hy)
      exact b2_sect_P hA ⟨⟨b2_sect_P hB hzy hyB, hzy⟩, hyB⟩ hy
  · rintro ⟨hA, hsub⟩
    exact ⟨hsub, fun z ⟨y, hy, hzy⟩ => b2_sect_P hA hzy.1.2 hy⟩

private theorem b2_fres_sub {P : α → α → Prop} (A : Set α) : P ⥏ A ⪽ P := fun _ _ h => h.1.2

/-- ✱213·241. \(\vdash :R\in P\unicode{x0294f}ʻʻ\text{sect}ʻP.\supset .R_{\varsigma }\,\unicode{x2abd}\, P_{\varsigma }\unicode{x0294f}CʻR_{\varsigma }\) -/
theorem pm213_241 {P R : α → α → Prop} (h : R ∈ opL fres P ʻʻ sect P) :
    Psec R ⪽ Psec P ⥏ fld (Psec R) := by
  obtain ⟨B, hB, rfl⟩ := h
  intro Q Q' hQQ'
  refine ⟨⟨⟨Q', Or.inl hQQ'⟩, ?_⟩, ⟨Q, Or.inr hQQ'⟩⟩
  obtain ⟨A', B', ⟨⟨hA', hB'⟩, hd⟩, rfl, rfl⟩ := b2_Psec.1 hQQ'
  have e := pm213_24 ⟨hB, rfl⟩
  have hA'' := e ▸ hA'.1
  have hB'' := e ▸ hB'.1
  have sA : A' ⊆ B := fun z hz => b2_fld_fres_sub P B (hA''.2 hz)
  have sB : B' ⊆ B := fun z hz => b2_fld_fres_sub P B (hB''.2 hz)
  rw [b2_fres_fres sA, b2_fres_fres sB]
  exact b2_Psec.2 ⟨A', B', ⟨⟨⟨hA''.1, hA'.2⟩, ⟨hB''.1, hB'.2⟩⟩, hd⟩, rfl, rfl⟩

/-- ✱213·242. \(\vdash :P_{\text{po}}\in \text{Ser}.R\in P\unicode{x0294f}ʻʻ\text{sect}ʻP.\supset .R_{\varsigma }=P_{\varsigma }\unicode{x0294f}CʻR_{\varsigma }\) -/
theorem pm213_242 {P R : α → α → Prop} (h : po P ∈ Ser ∧ R ∈ opL fres P ʻʻ sect P) :
    Psec R = Psec P ⥏ fld (Psec R) := by
  obtain ⟨h, hR⟩ := h
  refine b2_rsub_antisymm (pm213_241 hR) ?_
  obtain ⟨B, hB, rfl⟩ := hR
  have e := pm213_24 ⟨hB, rfl⟩
  rintro Q Q' ⟨⟨hQ, hQQ'⟩, hQ'⟩
  obtain ⟨A', hA', rfl⟩ := b2_mem_fld_Psec hQ
  obtain ⟨B', hB', rfl⟩ := b2_mem_fld_Psec hQ'
  have hA'' := e ▸ hA'.1
  have hB'' := e ▸ hB'.1
  have sA : A' ⊆ B := fun z hz => b2_fld_fres_sub P B (hA''.2 hz)
  have sB : B' ⊆ B := fun z hz => b2_fld_fres_sub P B (hB''.2 hz)
  rw [b2_fres_fres sA, b2_fres_fres sB] at hQQ'
  obtain ⟨A, C, ⟨⟨hA, hC⟩, hd⟩, e1, e2⟩ := b2_Psec.1 hQQ'
  have := b2_fres_inj h hA''.1 hA'.2 hA.1 hA.2 e1
  subst this
  have := b2_fres_inj h hB''.1 hB'.2 hC.1 hC.2 e2
  subst this
  exact b2_Psec.2 ⟨A', B', ⟨⟨hA', hB'⟩, hd⟩, rfl, rfl⟩

/-- ✱213·243. \(\vdash . \overrightarrow{P}_{\varsigma }ʻP = \text{D}ʻP_{\varsigma }\) -/
theorem pm213_243 {P : α → α → Prop} : refs (Psec P) P = dom (Psec P) := by
  ext Q
  constructor
  · intro hQ; exact ⟨P, hQ⟩
  · intro hQ
    rw [pm213_141, b2_mem_opL_fres_img] at hQ
    obtain ⟨A, hA, rfl⟩ := hQ
    rw [Set.mem_sdiff, b2_mem_diff_iotaNull, b2_mem_iota] at hA
    obtain ⟨z, hz⟩ := hA.1.2
    show Psec P (P ⥏ A) P
    rw [← congrArg (Psec P (P ⥏ A)) (b2_fres_fld P)]
    exact b2_Psec.2 ⟨A, fld P, ⟨⟨hA.1, b2_fld_mem_sect P, z, hA.1.1.1 hz⟩,
      (b2_sect_ne_fld hA.1.1).1 hA.2⟩, rfl, rfl⟩

/-- ✱213·244. \(\vdash :R\in CʻP_{\varsigma }.Q\in \text{D}ʻR_{\varsigma }.\supset .QP_{\varsigma }R\) -/
theorem pm213_244 {P Q R : α → α → Prop} (h : R ∈ fld (Psec P) ∧ Q ∈ dom (Psec R)) :
    Psec P Q R := by
  obtain ⟨hR, hQ⟩ := h
  obtain ⟨B, hB, rfl⟩ := b2_mem_fld_Psec hR
  rw [← pm213_243] at hQ
  exact (pm213_241 ⟨B, hB.1, rfl⟩ _ _ hQ).1.2

private theorem b2_sect_of_sub {P : α → α → Prop} {A B : Set α} (hA : A ∈ sect P) (hB : B ∈ sect P)
    (hs : A ⊆ B) (h1 : B ∉ (one : Set (Set α))) (hne : B.Nonempty) (h : po P ∈ Ser) :
    A ∈ sect (P ⥏ B) := by
  rw [pm213_24 ⟨hB, rfl⟩, b2_fld_fres h hB hne h1]
  exact ⟨hA, hs⟩

/-- ✱213·245. \(\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.\supset :QP_{\varsigma }R.\equiv .R\in CʻP_{\varsigma }.Q\in \text{D}ʻR_{\varsigma }\) -/
theorem pm213_245 {P Q R : α → α → Prop} (h : po P ∈ Ser) :
    Psec P Q R ↔ R ∈ fld (Psec P) ∧ Q ∈ dom (Psec R) := by
  refine ⟨fun hQR => ⟨⟨Q, Or.inr hQR⟩, ?_⟩, pm213_244⟩
  obtain ⟨A, B, ⟨hA, hB⟩, ⟨hs, hd⟩, rfl, rfl⟩ := (b2_Psec_ser h).1 hQR
  have h1 : B ∉ (one : Set (Set α)) := by
    rintro ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := hA.2
    obtain ⟨z, hz, hz'⟩ := hd
    rw [b2_mem_iota] at hz; subst hz
    have := hs ha; rw [b2_mem_iota] at this; subst this; exact hz' ha
  refine ⟨P ⥏ B, ?_⟩
  have sA := b2_sect_of_sub hA.1 hB.1 hs h1 hB.2 h
  have sB := b2_sect_of_sub hB.1 hB.1 (le_refl B) h1 hB.2 h
  have e1 := b2_fres_fres (P := P) hs
  have e2 := b2_fres_fres (P := P) (le_refl B)
  have := b2_Psec.2 ⟨A, B, ⟨⟨⟨sA, hA.2⟩, ⟨sB, hB.2⟩⟩, hd⟩, rfl, rfl⟩
  rw [e1, e2] at this
  exact this

/-- ✱213·246. \(\vdash :P_{\text{po}}\in \text{Ser}.R\in CʻP_{\varsigma }.\supset .\overrightarrow{P}_{\varsigma }ʻR=\text{D}ʻR_{\varsigma } \quad[*213·245]\) -/
theorem pm213_246 {P R : α → α → Prop} (h : po P ∈ Ser ∧ R ∈ fld (Psec P)) :
    refs (Psec P) R = dom (Psec R) := by
  ext Q
  exact ⟨fun hQ => ((pm213_245 h.1).1 hQ).2, fun hQ => pm213_244 ⟨h.2, hQ⟩⟩

/-- ✱213·247. \[\begin{align}&\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.\supset :Q(P_{\varsigma }\unicode{x0294f}\text{D}ʻP_{\varsigma })R.\equiv .R\in \text{D}ʻP_{\varsigma }.Q\in \text{D}ʻR_{\varsigma }\\ &[*213·245]\end{align}\] -/
theorem pm213_247 {P Q R : α → α → Prop} (h : po P ∈ Ser) :
    (Psec P ⥏ dom (Psec P)) Q R ↔ R ∈ dom (Psec P) ∧ Q ∈ dom (Psec R) := by
  constructor
  · rintro ⟨⟨-, hQR⟩, hR⟩
    exact ⟨hR, ((pm213_245 h).1 hQR).2⟩
  · rintro ⟨hR, hQ⟩
    have := pm213_244 ⟨let ⟨S, hS⟩ := hR; ⟨S, Or.inl hS⟩, hQ⟩
    exact ⟨⟨⟨R, this⟩, this⟩, hR⟩

/-- ✱213·25. \(\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.Q,R\in CʻP_{\varsigma }.\supset :Q\in \text{D}ʻR_{\varsigma }.\lor.R\in \text{D}ʻQ_{\varsigma }.\lor.Q=R\) -/
theorem pm213_25 {P Q R : α → α → Prop}
    (h : po P ∈ Ser ∧ (Q ∈ fld (Psec P) ∧ R ∈ fld (Psec P))) :
    (Q ∈ dom (Psec R) ∨ R ∈ dom (Psec Q)) ∨ Q = R := by
  obtain ⟨h, hQ, hR⟩ := h
  have hs := pm213_153 h
  rw [mem_Ser] at hs
  rcases hs.2 Q R ⟨hQ, hR⟩ with (h1 | rfl) | h1
  · exact Or.inl (Or.inl ((pm213_245 h).1 h1).2)
  · exact Or.inr rfl
  · exact Or.inl (Or.inr ((pm213_245 h).1 h1).2)

private theorem b2_po_mono {R S : α → α → Prop} (h : R ⪽ S) {x y : α} (hxy : po R x y) : po S x y := by
  rw [po_iff_transGen] at hxy ⊢
  induction hxy with
  | single hab => exact Relation.TransGen.single (h _ _ hab)
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

private theorem b2_self_mem_fld_Psec {P Q : α → α → Prop} (h : po P ∈ Ser) (hQ : Q ∈ fld (Psec P))
    (hn : Q ≠ rNull) : Q ∈ fld (Psec Q) := by
  obtain ⟨A, hA, rfl⟩ := b2_mem_fld_Psec hQ
  obtain ⟨a, b, hab⟩ : rEx (P ⥏ A) := b2_rEx_iff_ne.2 hn
  have hJ : ∀ x, ¬po (P ⥏ A) x x := fun x hx => (b2_serPo h).1 x (b2_po_mono (b2_fres_sub A) hx)
  obtain ⟨hs, hne, hfne, -⟩ := b2_two_sects hJ hab
  refine ⟨(P ⥏ A) ⥏ refs (anc (P ⥏ A)) a, Or.inr ?_⟩
  have := b2_Psec.2 ⟨refs (anc (P ⥏ A)) a, fld (P ⥏ A),
    ⟨⟨⟨(b2_segSer_anc.1 hs).1.1, hne⟩, b2_fld_mem_sect _, hfne⟩, (b2_segSer_anc.1 hs).2⟩, rfl, rfl⟩
  rw [b2_fres_fld] at this
  exact this

/-- ✱213·251. \[\begin{align}\vdash \colon\ldotp P_{\text{po}}\in \text{Ser}.Q,R\in CʻP_{\varsigma }.{\sim}&(Q=\dot{\Lambda} .R=\dot{\Lambda} ).\supset :\\ &Q\in CʻR_{\varsigma }.\lor.R\in \text{D}ʻQ_{\varsigma }\end{align}\] -/
theorem pm213_251 {P Q R : α → α → Prop}
    (h : (po P ∈ Ser ∧ (Q ∈ fld (Psec P) ∧ R ∈ fld (Psec P))) ∧ ¬(Q = rNull ∧ R = rNull)) :
    Q ∈ fld (Psec R) ∨ R ∈ dom (Psec Q) := by
  obtain ⟨⟨h, hQ, hR⟩, hn⟩ := h
  rcases pm213_25 ⟨h, hQ, hR⟩ with (h1 | h1) | rfl
  · exact Or.inl (let ⟨S, hS⟩ := h1; ⟨S, Or.inl hS⟩)
  · exact Or.inr h1
  · have : Q ≠ rNull := fun e => hn ⟨e, e⟩
    exact Or.inl (b2_self_mem_fld_Psec h hQ this)

/-- ✱213·3. \(\vdash :P=\dot{\Lambda} .\supset .P_{\varsigma }=\dot{\Lambda}\) -/
theorem pm213_3 {P : α → α → Prop} (h : P = rNull) : Psec P = rNull := by
  subst h
  rw [b2_eq_rNull]
  intro Q R hQR
  obtain ⟨A, B, ⟨⟨-, hB⟩, z, hz, -⟩, -, -⟩ := b2_Psec.1 hQR
  obtain ⟨w, hw | hw⟩ := hB.1.1 hz <;> exact hw ⟨rfl, rfl⟩

/-- ✱213·301. \(\vdash :\exists !\text{sect}ʻP-\iota ʻ\Lambda -\iota ʻCʻP.\supset .\dot{\exists} !P_{\varsigma } \quad[*213·141]\) -/
theorem pm213_301 {P : α → α → Prop} (h : ((sect P \ ι Λ) \ ι (fld P)).Nonempty) :
    rEx (Psec P) := by
  obtain ⟨A, hA⟩ := h
  rw [Set.mem_sdiff, b2_mem_diff_iotaNull, b2_mem_iota] at hA
  obtain ⟨z, hz⟩ := hA.1.2
  exact ⟨P ⥏ A, P ⥏ fld P, b2_Psec.2 ⟨A, fld P, ⟨⟨hA.1, b2_fld_mem_sect P, z, hA.1.1.1 hz⟩,
    (b2_sect_ne_fld hA.1.1).1 hA.2⟩, rfl, rfl⟩⟩

/-- ✱213·302. \(\vdash \colon\ldotp P_{\text{po}}\,\unicode{x2abd}\, J.\supset :\dot{\exists} !P.\equiv .\dot{\exists} !P_{\varsigma }\) -/
theorem pm213_302 {P : α → α → Prop} (hJ : po P ⪽ J) : rEx P ↔ rEx (Psec P) := by
  constructor
  · intro hP; exact pm213_301 (pm213_126 ⟨hJ, hP⟩)
  · intro hS
    by_contra hP
    have : P = rNull := b2_eq_rNull.2 fun x y hxy => hP ⟨x, y, hxy⟩
    rw [pm213_3 this] at hS
    obtain ⟨_, _, h⟩ := hS; exact h ⟨rfl, rfl⟩

/-- ✱213·31. \(\vdash :x\neq y.\supset .(x\downarrow y)_{\varsigma }=\dot{\Lambda} \downarrow (x\downarrow y)\) -/
theorem pm213_31 {x y : α} (h : x ≠ y) : Psec (x ↓ y) = rNull ↓ (x ↓ y) := by
  have hfld : fld (x ↓ y) = {x, y} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, ⟨h1, -⟩ | ⟨-, h1⟩⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro (rfl | rfl)
      · exact ⟨y, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨x, Or.inr ⟨rfl, rfl⟩⟩
  funext Q R
  apply propext
  rw [b2_Psec, couple_apply]
  constructor
  · rintro ⟨A, B, ⟨⟨hA, hB⟩, z, hzB, hzA⟩, rfl, rfl⟩
    have hxA : x ∈ A := by
      obtain ⟨a, ha⟩ := hA.2
      have := hA.1.1 ha
      rw [hfld] at this
      rcases this with rfl | rfl
      · exact ha
      · exact b2_sect_P hA.1 (⟨rfl, rfl⟩ : (x ↓ a) x a) ha
    have hz : z = y := by
      have := hB.1.1 hzB
      rw [hfld] at this
      rcases this with rfl | rfl
      · exact absurd hxA hzA
      · rfl
    subst hz
    have hxB : x ∈ B := b2_sect_P hB.1 (⟨rfl, rfl⟩ : (x ↓ z) x z) hzB
    constructor
    · rw [b2_eq_rNull]
      rintro u v ⟨⟨-, huv⟩, hv⟩
      exact hzA (huv.2 ▸ hv)
    · funext u v; apply propext
      constructor
      · rintro ⟨⟨-, huv⟩, -⟩; exact huv
      · rintro ⟨rfl, rfl⟩; exact ⟨⟨hxB, rfl, rfl⟩, hzB⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨ι x, fld (x ↓ y), ⟨⟨⟨?_, x, rfl⟩, b2_fld_mem_sect _, x, ⟨y, Or.inl ⟨rfl, rfl⟩⟩⟩,
      y, ⟨x, Or.inr ⟨rfl, rfl⟩⟩, fun e => h (b2_mem_iota.1 e).symm⟩, ?_, ?_⟩
    · refine ⟨fun z hz => (b2_mem_iota.1 hz) ▸ ⟨y, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
      rintro u ⟨v, hv, huv⟩
      rw [b2_mem_iota] at hv; subst hv
      exact absurd huv.2 h
    · rw [eq_comm, b2_eq_rNull]
      rintro u v ⟨⟨-, huv⟩, hv⟩
      rw [b2_mem_iota] at hv
      exact h (huv.2.symm.trans hv).symm
    · exact (b2_fres_fld _).symm

/-- ✱213·32. \(\vdash :P\in 2_{r}.\supset .P_{\varsigma }=\dot{\Lambda} \downarrow P.P_{\varsigma }\in 2_{r} \quad[*213·31]\) -/
theorem pm213_32 {P : α → α → Prop} (h : P ∈ (two_r : Set (α → α → Prop))) :
    Psec P = rNull ↓ P ∧ Psec P ∈ (two_r : Set ((α → α → Prop) → (α → α → Prop) → Prop)) := by
  obtain ⟨x, y, hxy, rfl⟩ := h
  refine ⟨pm213_31 hxy, rNull, x ↓ y, fun e => ?_, pm213_31 hxy⟩
  have : (x ↓ y) x y := ⟨rfl, rfl⟩
  rw [← e] at this; exact this ⟨rfl, rfl⟩

private theorem b2_fld_fres_conn {P : α → α → Prop} (hc : po P ∈ connex) {A : Set α} (hA : A ∈ sect P)
    (h1 : A ∉ (one : Set (Set α))) (hne : A.Nonempty) : fld (P ⥏ A) = A := by
  ext z
  constructor
  · intro hz; exact b2_fld_fres_sub P A hz
  · intro hz
    have : ∃ w, w ∈ A ∧ w ≠ z := by
      by_contra hn; push Not at hn
      exact h1 ⟨z, Set.ext fun v => ⟨fun hv => hn v hv, fun hv => (b2_mem_iota.1 hv) ▸ hz⟩⟩
    obtain ⟨w, hw, hwz⟩ := this
    rcases b2_connPo hc z w (hA.1 hz) (hA.1 hw) with (h' | rfl) | h'
    · obtain ⟨v, hzv, hvw⟩ := b2_po_head h'
      exact ⟨v, Or.inl ⟨⟨hz, hzv⟩, b2_sect_anc hA hvw hw⟩⟩
    · exact absurd rfl hwz
    · obtain ⟨v, -, hvz⟩ := b2_po_tail h'
      exact ⟨v, Or.inr ⟨⟨b2_sect_P hA hvz hz, hvz⟩, hz⟩⟩

private theorem b2_ser_po {P : α → α → Prop} (h : P ∈ Ser) : po P ∈ Ser := by
  rw [po_eq_of_transR h.1.2]; exact h

private theorem b2_rsum_irr {P Q R : α → α → Prop} (hirr : ∀ x, ¬P x x) (e : P = Q ⤉ R) {z : α}
    (hQ : z ∈ fld Q) (hR : z ∈ fld R) : False := by
  have : P z z := by rw [e]; exact Or.inr ⟨hQ, hR⟩
  exact hirr z this

private theorem b2_fld_sub_of_rsub {Q P : α → α → Prop} (h : Q ⪽ P) : fld Q ⊆ fld P := by
  rintro z ⟨w, hw | hw⟩
  · exact ⟨w, Or.inl (h _ _ hw)⟩
  · exact ⟨w, Or.inr (h _ _ hw)⟩

/-- The "upper" part of the field beyond a section. -/
private theorem b2_upper_sect {P : α → α → Prop} {A : Set α} (hA : A ∈ sect P) :
    fld P \ A ∈ sect P˘ := by
  refine ⟨by rw [fld_cnv]; exact Set.sdiff_subset, ?_⟩
  rintro u ⟨v, ⟨hv, hvA⟩, hvu⟩
  refine ⟨⟨v, Or.inr hvu⟩, fun hu => hvA (b2_sect_P hA hvu hu)⟩

private theorem b2_fld_fres_cnv (P : α → α → Prop) (A : Set α) : fld (P˘ ⥏ A) = fld (P ⥏ A) := by
  ext z
  constructor
  · rintro ⟨w, ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩⟩
    · exact ⟨w, Or.inr ⟨⟨h3, h2⟩, h1⟩⟩
    · exact ⟨w, Or.inl ⟨⟨h3, h2⟩, h1⟩⟩
  · rintro ⟨w, ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩⟩
    · exact ⟨w, Or.inr ⟨⟨h3, h2⟩, h1⟩⟩
    · exact ⟨w, Or.inl ⟨⟨h3, h2⟩, h1⟩⟩

private theorem b2_cnv_ser {P : α → α → Prop} (h : P ∈ Ser) : P˘ ∈ Ser := by
  rw [mem_Ser] at h ⊢
  rw [fld_cnv]
  refine ⟨⟨fun x => h.1.1 x, fun x y z ⟨h1, h2⟩ => h.1.2 z y x ⟨h2, h1⟩⟩, fun x y hxy => ?_⟩
  rcases h.2 x y hxy with (h1 | h1) | h1
  · exact Or.inr h1
  · exact Or.inl (Or.inr h1)
  · exact Or.inl (Or.inl h1)

/-- ✱213·4. \[\begin{align}\vdash :P\in &\text{Ser}.\supset .\\ &P\unicode{x0294f}ʻʻ\text{sect}ʻP=\hat{Q} \{(\exists R).P=Q\unicode{x2909}R.\lor.(\exists x).P=Q\unicode{x21f8} x\}\end{align}\] -/
theorem pm213_4 {P : α → α → Prop} (h : P ∈ Ser) :
    opL fres P ʻʻ sect P = {Q | (∃ R, P = Q ⤉ R) ∨ ∃ x, P = Q ⇸ x} := by
  have hs := b2_ser_po h
  have hirr : ∀ x, ¬P x x := (mem_Ser.1 h).1.1
  have hconn := (mem_Ser.1 h).2
  ext Q
  rw [b2_mem_opL_fres_img, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨A, hA, rfl⟩
    by_cases h0 : A.Nonempty ∧ A ∉ (one : Set (Set α))
    · obtain ⟨hne, h1⟩ := h0
      have hfA := b2_fld_fres hs hA hne h1
      by_cases h2 : fld P \ A ∈ (one : Set (Set α))
      · obtain ⟨x, hx⟩ := h2
        have hxD : x ∈ fld P \ A := hx ▸ rfl
        refine Or.inr ⟨x, ?_⟩
        funext u v; apply propext
        rw [addLast_apply, hfA]
        constructor
        · intro huv
          by_cases hv : v ∈ A
          · exact Or.inl ⟨⟨b2_sect_P hA huv hv, huv⟩, hv⟩
          · have : v ∈ fld P \ A := ⟨⟨u, Or.inr huv⟩, hv⟩
            rw [hx, b2_mem_iota] at this
            refine Or.inr ⟨?_, this⟩
            by_contra hu
            have : u ∈ fld P \ A := ⟨⟨v, Or.inl huv⟩, hu⟩
            rw [hx, b2_mem_iota] at this
            subst this; exact hirr _ (‹v = u› ▸ huv)
        · rintro (h' | ⟨hu, rfl⟩)
          · exact h'.1.2
          · rcases hconn u v ⟨hA.1 hu, hxD.1⟩ with (h' | rfl) | h'
            · exact h'
            · exact absurd hu hxD.2
            · exact absurd (b2_sect_P hA h' hu) hxD.2
      · refine Or.inl ⟨P ⥏ (fld P \ A), ?_⟩
        have hfD : fld (P ⥏ (fld P \ A)) = fld P \ A := by
          by_cases hD : (fld P \ A).Nonempty
          · rw [← b2_fld_fres_cnv]
            exact b2_fld_fres (b2_ser_po (b2_cnv_ser h)) (b2_upper_sect hA) hD h2
          · rw [Set.not_nonempty_iff_eq_empty] at hD
            rw [hD]
            exact Set.subset_empty_iff.1 (b2_fld_fres_sub P ∅)
        funext u v; apply propext
        rw [rsum_apply, hfA, hfD]
        constructor
        · intro huv
          have hu : u ∈ fld P := ⟨v, Or.inl huv⟩
          have hv : v ∈ fld P := ⟨u, Or.inr huv⟩
          by_cases hvA : v ∈ A
          · exact Or.inl (Or.inl ⟨⟨b2_sect_P hA huv hvA, huv⟩, hvA⟩)
          · by_cases huA : u ∈ A
            · exact Or.inr ⟨huA, hv, hvA⟩
            · exact Or.inl (Or.inr ⟨⟨⟨hu, huA⟩, huv⟩, hv, hvA⟩)
        · rintro ((h' | h') | ⟨hu, hv⟩)
          · exact h'.1.2
          · exact h'.1.2
          · rcases hconn u v ⟨hA.1 hu, hv.1⟩ with (h' | rfl) | h'
            · exact h'
            · exact absurd hu hv.2
            · exact absurd (b2_sect_P hA h' hu) hv.2
    · have hnull : P ⥏ A = rNull := by
        by_cases hne : A.Nonempty
        · have h1 : A ∈ (one : Set (Set α)) := by by_contra h1; exact h0 ⟨hne, h1⟩
          exact b2_fres_unit_null (b2_serPo hs).1 h1
        · rw [Set.not_nonempty_iff_eq_empty] at hne; subst hne; exact b2_fres_empty P
      refine Or.inl ⟨P, ?_⟩
      rw [hnull]
      funext u v; apply propext
      rw [rsum_apply]
      constructor
      · intro huv; exact Or.inl (Or.inr huv)
      · rintro ((h' | h') | ⟨⟨w, hw | hw⟩, -⟩)
        · exact absurd h' (fun h'' => h'' ⟨rfl, rfl⟩)
        · exact h'
        · exact absurd hw (fun h'' => h'' ⟨rfl, rfl⟩)
        · exact absurd hw (fun h'' => h'' ⟨rfl, rfl⟩)
  · rintro (⟨R, e⟩ | ⟨x, e⟩)
    · have hQP : Q ⪽ P := fun u v h' => by rw [e]; exact Or.inl (Or.inl h')
      refine ⟨fld Q, ⟨b2_fld_sub_of_rsub hQP, ?_⟩, ?_⟩
      · rintro z ⟨y, hy, hzy⟩
        rw [e] at hzy
        rcases hzy with (h' | h') | ⟨hz, -⟩
        · exact ⟨y, Or.inl h'⟩
        · exact (b2_rsum_irr hirr e hy ⟨z, Or.inr h'⟩).elim
        · exact hz
      · funext u v; apply propext
        constructor
        · intro huv; exact ⟨⟨⟨v, Or.inl huv⟩, hQP _ _ huv⟩, ⟨u, Or.inr huv⟩⟩
        · rintro ⟨⟨hu, huv⟩, hv⟩
          rw [e] at huv
          rcases huv with (h' | h') | ⟨-, hv'⟩
          · exact h'
          · exact (b2_rsum_irr hirr e hu ⟨v, Or.inl h'⟩).elim
          · exact (b2_rsum_irr hirr e hv hv').elim
    · have hQP : Q ⪽ P := fun u v h' => by rw [e]; exact Or.inl h'
      refine ⟨fld Q, ⟨b2_fld_sub_of_rsub hQP, ?_⟩, ?_⟩
      · rintro z ⟨y, hy, hzy⟩
        rw [e, addLast_apply] at hzy
        rcases hzy with h' | ⟨hz, -⟩
        · exact ⟨y, Or.inl h'⟩
        · exact hz
      · funext u v; apply propext
        constructor
        · intro huv; exact ⟨⟨⟨v, Or.inl huv⟩, hQP _ _ huv⟩, ⟨u, Or.inr huv⟩⟩
        · rintro ⟨⟨hu, huv⟩, hv⟩
          rw [e, addLast_apply] at huv
          rcases huv with h' | ⟨-, rfl⟩
          · exact h'
          · have : P v v := by rw [e, addLast_apply]; exact Or.inr ⟨hv, rfl⟩
            exact (hirr v this).elim

/-- ✱213·41. \[\begin{align}\vdash :&P\in \text{Ser}.\exists !\overrightarrow{B}ʻP.\supset .\\ &CʻP_{\varsigma }=\hat{Q} \{(\exists R).P=Q\unicode{x2909}R.\lor.(\exists x).P=Q\unicode{x21f8} x\} \quad[*213·4·161]\end{align}\] -/
theorem pm213_41 {P : α → α → Prop} (h : P ∈ Ser ∧ (refs Beg P).Nonempty) :
    fld (Psec P) = {Q | (∃ R, P = Q ⤉ R) ∨ ∃ x, P = Q ⇸ x} := by
  have hs := b2_ser_po h.1
  rw [← pm213_4 h.1, (pm213_161 ⟨b2_J_of_ser hs, h.2⟩).1, (pm213_161 ⟨b2_J_of_ser hs, h.2⟩).2]

/-- ✱213·42. \[\begin{align}&\vdash :P\in \text{Ser}.\overrightarrow{B}ʻP=\Lambda .\supset .\\ &CʻP_{\varsigma }=\hat{Q} \{(\exists R).P=Q\unicode{x2909}R.\lor.(\exists x).P=Q\unicode{x21f8} x\}-\iota ʻ\dot{\Lambda} \quad[*213·4·163]\end{align}\] -/
theorem pm213_42 {P : α → α → Prop} (h : P ∈ Ser ∧ refs Beg P = Λ) :
    fld (Psec P) = {Q | (∃ R, P = Q ⤉ R) ∨ ∃ x, P = Q ⇸ x} \ ι rNull := by
  rw [← pm213_4 h.1, pm213_163 ⟨b2_ser_po h.1, h.2⟩]

/-! Sections of `P ⇸ x`. -/

private theorem b2_fld_addLast {P : α → α → Prop} {x z : α} :
    z ∈ fld (P ⇸ x) ↔ z ∈ fld P ∨ ((fld P).Nonempty ∧ z = x) := by
  constructor
  · rintro ⟨w, h | h⟩
    · rcases (addLast_apply _ _ _ _).1 h with h | ⟨hz, -⟩
      · exact Or.inl ⟨w, Or.inl h⟩
      · exact Or.inl hz
    · rcases (addLast_apply _ _ _ _).1 h with h | ⟨hw, rfl⟩
      · exact Or.inl ⟨w, Or.inr h⟩
      · exact Or.inr ⟨⟨w, hw⟩, rfl⟩
  · rintro (⟨w, h | h⟩ | ⟨⟨w, hw⟩, rfl⟩)
    · exact ⟨w, Or.inl (Or.inl h)⟩
    · exact ⟨w, Or.inr (Or.inl h)⟩
    · exact ⟨w, Or.inr (Or.inr ⟨hw, rfl⟩)⟩

private theorem b2_sect_addLast {P : α → α → Prop} {x : α} (hx : x ∉ fld P) {A : Set α} :
    A ∈ sect (P ⇸ x) ↔ A ∈ sect P ∨ ((fld P).Nonempty ∧ A = insert x (fld P)) := by
  constructor
  · intro hA
    by_cases hxA : x ∈ A
    · have hne : (fld P).Nonempty := by
        rcases b2_fld_addLast.1 (hA.1 hxA) with h | h
        · exact absurd h hx
        · exact h.1
      refine Or.inr ⟨hne, Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)⟩
      · rcases b2_fld_addLast.1 (hA.1 hz) with h | ⟨-, rfl⟩
        · exact Or.inr h
        · exact Or.inl rfl
      · rcases hz with rfl | hz
        · exact hxA
        · exact b2_sect_P hA (Or.inr ⟨hz, rfl⟩) hxA
    · refine Or.inl ⟨fun z hz => ?_, ?_⟩
      · rcases b2_fld_addLast.1 (hA.1 hz) with h | ⟨-, rfl⟩
        · exact h
        · exact absurd hz hxA
      · rintro z ⟨y, hy, hzy⟩
        exact b2_sect_P hA (Or.inl hzy) hy
  · rintro (hA | ⟨hne, rfl⟩)
    · refine ⟨fun z hz => b2_fld_addLast.2 (Or.inl (hA.1 hz)), ?_⟩
      rintro z ⟨y, hy, hzy⟩
      rcases (addLast_apply _ _ _ _).1 hzy with h | ⟨-, rfl⟩
      · exact b2_sect_P hA h hy
      · exact absurd (hA.1 hy) hx
    · refine ⟨fun z hz => ?_, ?_⟩
      · rcases hz with rfl | hz
        · exact b2_fld_addLast.2 (Or.inr ⟨hne, rfl⟩)
        · exact b2_fld_addLast.2 (Or.inl hz)
      · rintro z ⟨y, -, hzy⟩
        rcases (addLast_apply _ _ _ _).1 hzy with h | ⟨hz, -⟩
        · exact Or.inr ⟨y, Or.inl h⟩
        · exact Or.inr hz

private theorem b2_addLast_fres {P : α → α → Prop} {x : α} (hx : x ∉ fld P) {A : Set α}
    (hA : A ⊆ fld P) : (P ⇸ x) ⥏ A = P ⥏ A := by
  funext u v; apply propext
  constructor
  · rintro ⟨⟨hu, huv⟩, hv⟩
    rcases (addLast_apply _ _ _ _).1 huv with h | ⟨-, rfl⟩
    · exact ⟨⟨hu, h⟩, hv⟩
    · exact absurd (hA hv) hx
  · rintro ⟨⟨hu, huv⟩, hv⟩; exact ⟨⟨hu, Or.inl huv⟩, hv⟩

private theorem b2_fld_addLast_eq {P : α → α → Prop} {x : α} (hne : (fld P).Nonempty) :
    fld (P ⇸ x) = insert x (fld P) := by
  ext z
  rw [b2_fld_addLast]
  constructor
  · rintro (h | ⟨-, rfl⟩)
    · exact Or.inr h
    · exact Or.inl rfl
  · rintro (rfl | h)
    · exact Or.inr ⟨hne, rfl⟩
    · exact Or.inl h

/-- ✱213·5. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.x{\sim}\in CʻP.\supset .\text{D}ʻ(P\unicode{x21f8} x)_{\varsigma }=CʻP_{\varsigma }\) -/
theorem pm213_5 {P : α → α → Prop} {x : α} (h : po P ⪽ J ∧ x ∉ fld P) :
    dom (Psec (P ⇸ x)) = fld (Psec P) := by
  obtain ⟨hJ, hx⟩ := h
  rw [pm213_141, pm213_142 hJ]
  ext Q
  rw [b2_mem_opL_fres_img, b2_mem_opL_fres_img]
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [Set.mem_sdiff, b2_mem_diff_iotaNull, b2_mem_iota] at hA
    rcases (b2_sect_addLast hx).1 hA.1.1 with hA' | ⟨hne, rfl⟩
    · exact ⟨A, b2_mem_diff_iotaNull.2 ⟨hA', hA.1.2⟩, b2_addLast_fres hx hA'.1⟩
    · exact absurd (b2_fld_addLast_eq hne).symm hA.2
  · rintro ⟨A, hA, rfl⟩
    rw [b2_mem_diff_iotaNull] at hA
    refine ⟨A, ⟨b2_mem_diff_iotaNull.2 ⟨(b2_sect_addLast hx).2 (Or.inl hA.1), hA.2⟩, ?_⟩,
      (b2_addLast_fres hx hA.1.1).symm⟩
    intro e
    rw [b2_mem_iota] at e
    have hne : (fld P).Nonempty := let ⟨z, hz⟩ := hA.2; ⟨z, hA.1.1 hz⟩
    have : x ∈ fld (P ⇸ x) := b2_fld_addLast.2 (Or.inr ⟨hne, rfl⟩)
    rw [← e] at this
    exact hx (hA.1.1 this)

/-- ✱213·51. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.x{\sim}\in CʻP.\supset .(P\unicode{x21f8} x)_{\varsigma }=P_{\varsigma }\unicode{x21f8} (P\unicode{x21f8} x)\) -/
theorem pm213_51 {P : α → α → Prop} {x : α} (h : po P ⪽ J ∧ x ∉ fld P) :
    Psec (P ⇸ x) = Psec P ⇸ (P ⇸ x) := by
  obtain ⟨hJ, hx⟩ := h
  funext Q R; apply propext
  rw [addLast_apply, b2_Psec]
  constructor
  · rintro ⟨A, B, ⟨⟨hA, hB⟩, hd⟩, rfl, rfl⟩
    rcases (b2_sect_addLast hx).1 hA.1 with hA' | ⟨hne, rfl⟩
    · rw [b2_addLast_fres hx hA'.1]
      rcases (b2_sect_addLast hx).1 hB.1 with hB' | ⟨hne, rfl⟩
      · rw [b2_addLast_fres hx hB'.1]
        exact Or.inl (b2_Psec.2 ⟨A, B, ⟨⟨⟨hA', hA.2⟩, ⟨hB', hB.2⟩⟩, hd⟩, rfl, rfl⟩)
      · refine Or.inr ⟨?_, ?_⟩
        · rw [pm213_142 hJ]; exact ⟨A, b2_mem_diff_iotaNull.2 ⟨hA', hA.2⟩, rfl⟩
        · rw [← b2_fld_addLast_eq hne, b2_fres_fld]
    · obtain ⟨z, hz, hz'⟩ := hd
      have := (b2_sect_addLast hx).2 (Or.inr ⟨hne, rfl⟩)
      exact absurd (by rw [← b2_fld_addLast_eq hne]; exact hB.1.1 hz) hz'
  · rintro (hQR | ⟨hQ, rfl⟩)
    · obtain ⟨A, B, ⟨⟨hA, hB⟩, hd⟩, rfl, rfl⟩ := b2_Psec.1 hQR
      refine ⟨A, B, ⟨⟨⟨(b2_sect_addLast hx).2 (Or.inl hA.1), hA.2⟩,
        ⟨(b2_sect_addLast hx).2 (Or.inl hB.1), hB.2⟩⟩, hd⟩, ?_, ?_⟩
      · exact (b2_addLast_fres hx hA.1.1).symm
      · exact (b2_addLast_fres hx hB.1.1).symm
    · obtain ⟨A, hA, rfl⟩ := b2_mem_fld_Psec hQ
      have hne : (fld P).Nonempty := let ⟨z, hz⟩ := hA.2; ⟨z, hA.1.1 hz⟩
      refine ⟨A, insert x (fld P), ⟨⟨⟨(b2_sect_addLast hx).2 (Or.inl hA.1), hA.2⟩,
        ⟨(b2_sect_addLast hx).2 (Or.inr ⟨hne, rfl⟩), x, Or.inl rfl⟩⟩,
        x, Or.inl rfl, fun hxA => hx (hA.1.1 hxA)⟩, (b2_addLast_fres hx hA.1.1).symm, ?_⟩
      rw [← b2_fld_addLast_eq hne, b2_fres_fld]

/-! Sections of `P ⤉ Q` for disjoint fields. -/

private theorem b2_disj {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) {z : α} (hP : z ∈ fld P)
    (hQ : z ∈ fld Q) : False := by
  have : z ∈ fld P ∩ fld Q := ⟨hP, hQ⟩
  rw [hd, Null_eq_empty] at this; exact this

private theorem b2_sect_rsum {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) {A : Set α} :
    A ∈ sect (P ⤉ Q) ↔ A ∈ sect P ∨ ∃ G, (G ∈ sect Q ∧ G.Nonempty) ∧ A = fld P ∪ G := by
  constructor
  · intro hA
    by_cases hG : (A ∩ fld Q).Nonempty
    · right
      obtain ⟨y, hyA, hyQ⟩ := hG
      have hPA : fld P ⊆ A := fun z hz =>
        b2_sect_P hA ((rsum_apply _ _ _ _).2 (Or.inr ⟨hz, hyQ⟩)) hyA
      refine ⟨A ∩ fld Q, ⟨⟨Set.inter_subset_right, ?_⟩, y, hyA, hyQ⟩, ?_⟩
      · rintro z ⟨w, ⟨hwA, hwQ⟩, hzw⟩
        exact ⟨b2_sect_P hA ((rsum_apply _ _ _ _).2 (Or.inl (Or.inr hzw))) hwA, ⟨w, Or.inl hzw⟩⟩
      · ext z
        constructor
        · intro hz
          have := hA.1 hz
          rw [fld_rsum] at this
          rcases this with h | h
          · exact Or.inl h
          · exact Or.inr ⟨hz, h⟩
        · rintro (h | h)
          · exact hPA h
          · exact h.1
    · left
      rw [Set.not_nonempty_iff_eq_empty] at hG
      have hsub : A ⊆ fld P := by
        intro z hz
        have := hA.1 hz
        rw [fld_rsum] at this
        rcases this with h | h
        · exact h
        · have : z ∈ A ∩ fld Q := ⟨hz, h⟩
          rw [hG] at this; exact this.elim
      refine ⟨hsub, ?_⟩
      rintro z ⟨w, hw, hzw⟩
      exact b2_sect_P hA ((rsum_apply _ _ _ _).2 (Or.inl (Or.inl hzw))) hw
  · rintro (hA | ⟨G, ⟨hG, -⟩, rfl⟩)
    · refine ⟨fun z hz => by rw [fld_rsum]; exact Or.inl (hA.1 hz), ?_⟩
      rintro z ⟨y, hy, hzy⟩
      rcases (rsum_apply _ _ _ _).1 hzy with (h | h) | ⟨-, h⟩
      · exact b2_sect_P hA h hy
      · exact (b2_disj hd (hA.1 hy) ⟨z, Or.inr h⟩).elim
      · exact (b2_disj hd (hA.1 hy) h).elim
    · refine ⟨fun z hz => ?_, ?_⟩
      · rw [fld_rsum]
        rcases hz with h | h
        · exact Or.inl h
        · exact Or.inr (hG.1 h)
      · rintro z ⟨y, hy, hzy⟩
        rcases (rsum_apply _ _ _ _).1 hzy with (h | h) | ⟨h, -⟩
        · exact Or.inl ⟨y, Or.inl h⟩
        · rcases hy with hy | hy
          · exact (b2_disj hd hy ⟨z, Or.inr h⟩).elim
          · exact Or.inr (b2_sect_P hG h hy)
        · exact Or.inl h

private theorem b2_rsum_fres_P {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) {A : Set α}
    (hA : A ⊆ fld P) : (P ⤉ Q) ⥏ A = P ⥏ A := by
  funext u v; apply propext
  constructor
  · rintro ⟨⟨hu, huv⟩, hv⟩
    rcases (rsum_apply _ _ _ _).1 huv with (h | h) | ⟨-, h⟩
    · exact ⟨⟨hu, h⟩, hv⟩
    · exact (b2_disj hd (hA hv) ⟨u, Or.inr h⟩).elim
    · exact (b2_disj hd (hA hv) h).elim
  · rintro ⟨⟨hu, huv⟩, hv⟩
    exact ⟨⟨hu, (rsum_apply _ _ _ _).2 (Or.inl (Or.inl huv))⟩, hv⟩

private theorem b2_rsum_fres_union {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) {G : Set α}
    (hG : G ⊆ fld Q) (hf : fld (Q ⥏ G) = G) : (P ⤉ Q) ⥏ (fld P ∪ G) = P ⤉ Q ⥏ G := by
  funext u v; apply propext
  rw [rsum_apply, hf]
  constructor
  · rintro ⟨⟨hu, huv⟩, hv⟩
    rcases (rsum_apply _ _ _ _).1 huv with (h | h) | ⟨hu', hv'⟩
    · exact Or.inl (Or.inl h)
    · have hu' : u ∈ G := by
        rcases hu with hu | hu
        · exact (b2_disj hd hu ⟨v, Or.inl h⟩).elim
        · exact hu
      have hv' : v ∈ G := by
        rcases hv with hv | hv
        · exact (b2_disj hd hv ⟨u, Or.inr h⟩).elim
        · exact hv
      exact Or.inl (Or.inr ⟨⟨hu', h⟩, hv'⟩)
    · rcases hv with hv | hv
      · exact (b2_disj hd hv hv').elim
      · exact Or.inr ⟨hu', hv⟩
  · rintro ((h | ⟨⟨hu, h⟩, hv⟩) | ⟨hu, hv⟩)
    · exact ⟨⟨Or.inl ⟨v, Or.inl h⟩, (rsum_apply _ _ _ _).2 (Or.inl (Or.inl h))⟩,
        Or.inl ⟨u, Or.inr h⟩⟩
    · exact ⟨⟨Or.inr hu, (rsum_apply _ _ _ _).2 (Or.inl (Or.inr h))⟩, Or.inr hv⟩
    · exact ⟨⟨Or.inl hu, (rsum_apply _ _ _ _).2 (Or.inr ⟨hu, hG hv⟩)⟩, Or.inr hv⟩

private theorem b2_rsum_fres_unit {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) {b : α}
    (hb : b ∈ fld Q) (hbb : ¬Q b b) : (P ⤉ Q) ⥏ (fld P ∪ ι b) = P ⇸ b := by
  funext u v; apply propext
  rw [addLast_apply]
  constructor
  · rintro ⟨⟨hu, huv⟩, hv⟩
    rcases (rsum_apply _ _ _ _).1 huv with (h | h) | ⟨hu', hv'⟩
    · exact Or.inl h
    · have hu' : u = b := by
        rcases hu with hu | hu
        · exact (b2_disj hd hu ⟨v, Or.inl h⟩).elim
        · exact hu
      have hv' : v = b := by
        rcases hv with hv | hv
        · exact (b2_disj hd hv ⟨u, Or.inr h⟩).elim
        · exact hv
      subst hu'; subst hv'; exact (hbb h).elim
    · rcases hv with hv | hv
      · exact (b2_disj hd hv hv').elim
      · exact Or.inr ⟨hu', hv⟩
  · rintro (h | ⟨hu, rfl⟩)
    · exact ⟨⟨Or.inl ⟨v, Or.inl h⟩, (rsum_apply _ _ _ _).2 (Or.inl (Or.inl h))⟩,
        Or.inl ⟨u, Or.inr h⟩⟩
    · exact ⟨⟨Or.inl hu, (rsum_apply _ _ _ _).2 (Or.inr ⟨hu, hb⟩)⟩, Or.inr rfl⟩

private theorem b2_mem_opL_union {P : α → α → Prop} {K : Set (Set α)} {B : Set α} :
    B ∈ opL (· ∪ ·) (fld P) ʻʻ K ↔ ∃ G, G ∈ K ∧ B = fld P ∪ G := Iff.rfl

private theorem b2_union_inter {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) {G : Set α}
    (hG : G ⊆ fld Q) : (fld P ∪ G) ∩ fld Q = G := by
  ext z
  constructor
  · rintro ⟨hz | hz, hzQ⟩
    · exact (b2_disj hd hz hzQ).elim
    · exact hz
  · intro hz; exact ⟨Or.inr hz, hG hz⟩

/-- ✱213·52. \[\begin{align}&\vdash \colon\ldotp Q_{\text{po}}\in \text{connex} .CʻP\cap CʻQ=\Lambda .\supset :\\ &(\exists \beta ).\beta \cap CʻQ{\sim}\in 1.\beta \in (CʻP\cup )ʻʻ(\text{sect}ʻQ-\iota ʻ\Lambda ).S=(P\unicode{x2909}Q)\unicode{x0294f}\beta .\equiv .\\ &(\exists \gamma ).\gamma \in \text{sect}ʻQ-\iota ʻ\Lambda -1.S=P\unicode{x2909}Q\unicode{x0294f}\gamma\end{align}\] -/
theorem pm213_52 {P Q S : α → α → Prop} (h : po Q ∈ connex ∧ fld P ∩ fld Q = Λ) :
    (∃ B, (B ∩ fld Q ∉ (one : Set (Set α)) ∧ B ∈ opL (· ∪ ·) (fld P) ʻʻ (sect Q \ ι Λ)) ∧
        S = (P ⤉ Q) ⥏ B) ↔
      ∃ G, G ∈ (sect Q \ ι Λ) \ one ∧ S = P ⤉ Q ⥏ G := by
  obtain ⟨hc, hd⟩ := h
  constructor
  · rintro ⟨B, ⟨h1, G, hG, rfl⟩, rfl⟩
    rw [b2_mem_diff_iotaNull] at hG
    rw [b2_union_inter hd hG.1.1] at h1
    exact ⟨G, ⟨b2_mem_diff_iotaNull.2 hG, h1⟩,
      b2_rsum_fres_union hd hG.1.1 (b2_fld_fres_conn hc hG.1 h1 hG.2)⟩
  · rintro ⟨G, ⟨hG, h1⟩, rfl⟩
    rw [b2_mem_diff_iotaNull] at hG
    refine ⟨fld P ∪ G, ⟨?_, G, b2_mem_diff_iotaNull.2 hG, rfl⟩, ?_⟩
    · rw [b2_union_inter hd hG.1.1]; exact h1
    · exact (b2_rsum_fres_union hd hG.1.1 (b2_fld_fres_conn hc hG.1 h1 hG.2)).symm

private theorem b2_semi_graph_fld {γ δ : Type*} {f : δ → γ} {Q : δ → δ → Prop} {X : γ} :
    X ∈ fld (graph f ⁏ Q) ↔ ∃ Y, Y ∈ fld Q ∧ X = f Y := by
  rw [fld_semi_graph]; exact Iff.rfl

private theorem b2_diff_union {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) {A G : Set α}
    (hA : A ⊆ fld P) (hG : G ⊆ fld Q) (hne : G.Nonempty) : ((fld P ∪ G) \ A).Nonempty := by
  obtain ⟨z, hz⟩ := hne
  exact ⟨z, Or.inr hz, fun hzA => b2_disj hd (hA hzA) (hG hz)⟩

private theorem b2_no_unit {Q : α → α → Prop} (hJ : ∀ x, ¬po Q x x) (h0 : refs Beg Q = Λ) {G : Set α}
    (hG : G ∈ sect Q) : G ∉ (one : Set (Set α)) := by
  rintro ⟨b, rfl⟩
  have := (b2_unit_sect hJ).1 hG
  rw [h0, Null_eq_empty] at this; exact this

/-- ✱213·53. \[\begin{align}\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.Q_{\text{po}}\in \text{Ser}.\overrightarrow{B}ʻQ=\Lambda .CʻP\cap &CʻQ=\Lambda .\supset .\\ &(P\unicode{x2909}Q)_{\varsigma }=P_{\varsigma }\unicode{x2909}(P\unicode{x2909}^{;}Q_{\varsigma })\end{align}\] -/
theorem pm213_53 {P Q : α → α → Prop}
    (h : ((po P ⪽ J ∧ po Q ∈ Ser) ∧ refs Beg Q = Λ) ∧ fld P ∩ fld Q = Λ) :
    Psec (P ⤉ Q) = Psec P ⤉ (opL rsum P ⁏ Psec Q) := by
  obtain ⟨⟨⟨hJP, hQ⟩, h0⟩, hd⟩ := h
  have hJQ := (b2_serPo hQ).1
  have hcQ := b2_connex_of_ser hQ
  have rep : ∀ G, G ∈ sect Q → G.Nonempty → (P ⤉ Q) ⥏ (fld P ∪ G) = P ⤉ Q ⥏ G :=
    fun G hG hne => b2_rsum_fres_union hd hG.1 (b2_fld_fres_conn hcQ hG (b2_no_unit hJQ h0 hG) hne)
  funext X Y; apply propext
  rw [rsum_apply, b2_Psec]
  constructor
  · rintro ⟨A, B, ⟨⟨hA, hB⟩, hdiff⟩, rfl, rfl⟩
    rcases (b2_sect_rsum hd).1 hA.1 with hA' | ⟨G, hG, rfl⟩
    · rw [b2_rsum_fres_P hd hA'.1]
      rcases (b2_sect_rsum hd).1 hB.1 with hB' | ⟨H, hH, rfl⟩
      · rw [b2_rsum_fres_P hd hB'.1]
        exact Or.inl (Or.inl (b2_Psec.2 ⟨A, B, ⟨⟨⟨hA', hA.2⟩, ⟨hB', hB.2⟩⟩, hdiff⟩, rfl, rfl⟩))
      · rw [rep H hH.1 hH.2]
        refine Or.inr ⟨?_, ?_⟩
        · rw [pm213_142 hJP]; exact ⟨A, b2_mem_diff_iotaNull.2 ⟨hA', hA.2⟩, rfl⟩
        · refine (b2_semi_graph_fld (f := rsum P) (Q := Psec Q)).2 ⟨Q ⥏ H, ?_, rfl⟩
          rw [pm213_142 (b2_J_of_ser hQ)]
          exact ⟨H, b2_mem_diff_iotaNull.2 hH, rfl⟩
    · rcases (b2_sect_rsum hd).1 hB.1 with hB' | ⟨H, hH, rfl⟩
      · obtain ⟨z, hzB, hzA⟩ := hdiff
        exact absurd (Or.inl (hB'.1 hzB)) hzA
      · rw [rep G hG.1 hG.2, rep H hH.1 hH.2]
        refine Or.inl (Or.inr ((semi_graph_apply _ _ _ _).2 ⟨Q ⥏ G, Q ⥏ H, ⟨rfl, rfl⟩, ?_⟩))
        obtain ⟨z, hzB, hzA⟩ := hdiff
        have hzH : z ∈ H := by
          rcases hzB with h' | h'
          · exact absurd (Or.inl h') hzA
          · exact h'
        exact b2_Psec.2 ⟨G, H, ⟨⟨hG, hH⟩, z, hzH, fun h' => hzA (Or.inr h')⟩, rfl, rfl⟩
  · rintro ((hXY | hXY) | ⟨hX, hY⟩)
    · obtain ⟨A, B, ⟨⟨hA, hB⟩, hdiff⟩, rfl, rfl⟩ := b2_Psec.1 hXY
      exact ⟨A, B, ⟨⟨⟨(b2_sect_rsum hd).2 (Or.inl hA.1), hA.2⟩,
        ⟨(b2_sect_rsum hd).2 (Or.inl hB.1), hB.2⟩⟩, hdiff⟩,
        (b2_rsum_fres_P hd hA.1.1).symm, (b2_rsum_fres_P hd hB.1.1).symm⟩
    · obtain ⟨Q1, Q2, ⟨rfl, rfl⟩, hQ12⟩ := (semi_graph_apply _ _ _ _).1 hXY
      obtain ⟨G, H, ⟨⟨hG, hH⟩, z, hzH, hzG⟩, rfl, rfl⟩ := b2_Psec.1 hQ12
      refine ⟨fld P ∪ G, fld P ∪ H, ⟨⟨⟨(b2_sect_rsum hd).2 (Or.inr ⟨G, hG, rfl⟩),
        let ⟨w, hw⟩ := hG.2; ⟨w, Or.inr hw⟩⟩, ⟨(b2_sect_rsum hd).2 (Or.inr ⟨H, hH, rfl⟩),
        let ⟨w, hw⟩ := hH.2; ⟨w, Or.inr hw⟩⟩⟩, z, Or.inr hzH, ?_⟩,
        (rep G hG.1 hG.2).symm, (rep H hH.1 hH.2).symm⟩
      rintro (h' | h')
      · exact b2_disj hd h' (hH.1.1 hzH)
      · exact hzG h'
    · obtain ⟨A, hA, rfl⟩ := b2_mem_fld_Psec hX
      obtain ⟨Q', hQ', rfl⟩ := (b2_semi_graph_fld (f := rsum P) (Q := Psec Q)).1 hY
      obtain ⟨H, hH, rfl⟩ := b2_mem_fld_Psec hQ'
      exact ⟨A, fld P ∪ H, ⟨⟨⟨(b2_sect_rsum hd).2 (Or.inl hA.1), hA.2⟩,
        ⟨(b2_sect_rsum hd).2 (Or.inr ⟨H, hH, rfl⟩), let ⟨w, hw⟩ := hH.2; ⟨w, Or.inr hw⟩⟩⟩,
        b2_diff_union hd hA.1.1 hH.1.1 hH.2⟩,
        (b2_rsum_fres_P hd hA.1.1).symm, (rep H hH.1 hH.2).symm⟩

/-- ✱213·531. \[\begin{align}&\vdash \colon\colon Q_{\text{po}}\in \text{Ser}.\exists !\overrightarrow{B}ʻQ.CʻP\cap CʻQ=\Lambda .\supset \colon\ldotp \\ &(\exists \beta ).\beta \in (CʻP\cup )ʻʻ(\text{sect}ʻQ-\iota ʻ\Lambda ).S=(P\unicode{x2909}Q)\unicode{x0294f}\beta .\equiv :\\ &S=P\unicode{x21f8} BʻQ.\lor.(\exists \gamma ).\gamma \in \text{sect}ʻQ-\iota ʻ\Lambda -\iota ʻ\iota ʻBʻQ.S=P\unicode{x2909}Q\unicode{x0294f}\gamma\end{align}\] -/
theorem pm213_531 {P Q S : α → α → Prop}
    (h : (po Q ∈ Ser ∧ (refs Beg Q).Nonempty) ∧ fld P ∩ fld Q = Λ) :
    (∃ B, B ∈ opL (· ∪ ·) (fld P) ʻʻ (sect Q \ ι Λ) ∧ S = (P ⤉ Q) ⥏ B) ↔
      Desc Beg Q (fun b => S = P ⇸ b) ∨
        ∃ G, Desc Beg Q (fun b => G ∈ (sect Q \ ι Λ) \ ι (ι b)) ∧ S = P ⤉ Q ⥏ G := by
  obtain ⟨⟨hQ, b, hb⟩, hd⟩ := h
  have hJQ := (b2_serPo hQ).1
  have hcQ := b2_connex_of_ser hQ
  have e1 := b2_refs_Beg_eq hQ hb
  have hbf : b ∈ fld Q := let ⟨y, hy⟩ := hb.1; ⟨y, Or.inl hy⟩
  simp only [b2_desc_of_refs e1]
  constructor
  · rintro ⟨B, ⟨G, hG, rfl⟩, rfl⟩
    rw [b2_mem_diff_iotaNull] at hG
    by_cases h1 : G ∈ (one : Set (Set α))
    · obtain ⟨c, rfl⟩ := h1
      have := b2_beg_unique hQ hb ((b2_unit_sect hJQ).1 hG.1)
      subst this
      exact Or.inl (b2_rsum_fres_unit hd hbf (b2_irrP hJQ))
    · refine Or.inr ⟨G, ⟨b2_mem_diff_iotaNull.2 hG, fun e => h1 ⟨b, e⟩⟩, ?_⟩
      exact b2_rsum_fres_union hd hG.1.1 (b2_fld_fres_conn hcQ hG.1 h1 hG.2)
  · rintro (rfl | ⟨G, ⟨hG, hGb⟩, rfl⟩)
    · exact ⟨fld P ∪ ι b, ⟨ι b, b2_mem_diff_iotaNull.2 ⟨(b2_unit_sect hJQ).2 hb, b, rfl⟩, rfl⟩,
        (b2_rsum_fres_unit hd hbf (b2_irrP hJQ)).symm⟩
    · rw [b2_mem_diff_iotaNull] at hG
      have h1 : G ∉ (one : Set (Set α)) := by
        rintro ⟨c, rfl⟩
        have := b2_beg_unique hQ hb ((b2_unit_sect hJQ).1 hG.1)
        subst this; exact hGb rfl
      exact ⟨fld P ∪ G, ⟨G, b2_mem_diff_iotaNull.2 hG, rfl⟩,
        (b2_rsum_fres_union hd hG.1.1 (b2_fld_fres_conn hcQ hG.1 h1 hG.2)).symm⟩

/-- Classification of the non-null sections of `P ⤉ Q` (disjoint fields, `Q_po` serial,
`B'Q` exists). -/
private theorem b2_cls_rsum {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) (hQ : po Q ∈ Ser) {b : α}
    (hb : b ∈ refs Beg Q) {A : Set α} (hA : A ∈ sect (P ⤉ Q)) (hne : A.Nonempty) :
    (A ∈ sect P ∧ A.Nonempty) ∨ A = fld P ∪ ι b ∨
      ∃ G, ((G ∈ sect Q ∧ G.Nonempty) ∧ G ∉ (one : Set (Set α))) ∧ A = fld P ∪ G := by
  rcases (b2_sect_rsum hd).1 hA with hA' | ⟨G, hG, rfl⟩
  · exact Or.inl ⟨hA', hne⟩
  · by_cases h1 : G ∈ (one : Set (Set α))
    · obtain ⟨c, rfl⟩ := h1
      have := b2_beg_unique hQ hb ((b2_unit_sect (b2_serPo hQ).1).1 hG.1)
      subst this
      exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨G, ⟨hG, h1⟩, rfl⟩)

private theorem b2_mem_codom_Psec {Q R : α → α → Prop} (hQ : po Q ∈ Ser) :
    R ∈ codom (Psec Q) ↔ ∃ G, ((G ∈ sect Q ∧ G.Nonempty) ∧ G ∉ (one : Set (Set α))) ∧
      R = Q ⥏ G := by
  rw [pm213_162 hQ, Set.mem_sdiff, b2_mem_opL_fres_img, b2_mem_iota]
  constructor
  · rintro ⟨⟨G, hG, rfl⟩, hn⟩
    exact ⟨G, ⟨⟨hG, ((b2_fres_ne_null hQ hG).1 hn).1⟩, ((b2_fres_ne_null hQ hG).1 hn).2⟩, rfl⟩
  · rintro ⟨G, ⟨hG, h1⟩, rfl⟩
    exact ⟨⟨G, hG.1, rfl⟩, (b2_fres_ne_null hQ hG.1).2 ⟨hG.2, h1⟩⟩

private theorem b2_fld_codom_restr {R : α → α → Prop} (hR : R ∈ Ser) (h1 : codom R ∉ (one : Set (Set α))) :
    fld (R ⥏ codom R) = codom R := by
  ext X
  refine ⟨fun hX => b2_fld_fres_sub R _ hX, fun hX => ?_⟩
  have : ∃ Y, Y ∈ codom R ∧ Y ≠ X := by
    by_contra hn; push Not at hn
    exact h1 ⟨X, Set.ext fun Y => ⟨fun hY => hn Y hY, fun hY => (b2_mem_iota.1 hY) ▸ hX⟩⟩
  obtain ⟨Y, hY, hYX⟩ := this
  have hXf : X ∈ fld R := let ⟨Z, hZ⟩ := hX; ⟨Z, Or.inr hZ⟩
  have hYf : Y ∈ fld R := let ⟨Z, hZ⟩ := hY; ⟨Z, Or.inr hZ⟩
  rcases (mem_Ser.1 hR).2 X Y ⟨hXf, hYf⟩ with (h' | rfl) | h'
  · exact ⟨Y, Or.inl ⟨⟨hX, h'⟩, hY⟩⟩
  · exact absurd rfl hYX
  · exact ⟨Y, Or.inr ⟨⟨hY, h'⟩, hX⟩⟩

private theorem b2_fld_Psec_ne {P : α → α → Prop} (hJ : po P ⪽ J) (hP : rEx P) :
    (fld (Psec P)).Nonempty := by
  obtain ⟨X, Y, hXY⟩ := (pm213_302 hJ).1 hP
  exact ⟨X, Y, Or.inl hXY⟩

private theorem b2_beg_not_fldP {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) {b : α}
    (hb : b ∈ refs Beg Q) : b ∉ fld P := fun h =>
  b2_disj hd h (let ⟨y, hy⟩ := hb.1; ⟨y, Or.inl hy⟩)

/-- ✱213·54. \[\begin{align}\vdash :\dot{\exists} !P.P_{\text{po}}\,\unicode{x2abd}\, J.&Q_{\text{po}}\in \text{Ser}.\exists !\overrightarrow{B}ʻQ.CʻP\cap CʻQ=\Lambda .\text{ᗡ}ʻQ_{\varsigma }{\sim}\in 1.\supset .\\ &(P\unicode{x2909}Q)_{\varsigma }=P_{\varsigma }\unicode{x21f8} (P\unicode{x21f8} BʻQ)\unicode{x2909}\{P\unicode{x2909}^{;}(Q_{\varsigma }\unicode{x0294f}\text{ᗡ}ʻQ_{\varsigma })\}\end{align}\] -/
theorem pm213_54 {P Q : α → α → Prop}
    (h : ((((rEx P ∧ po P ⪽ J) ∧ po Q ∈ Ser) ∧ (refs Beg Q).Nonempty) ∧ fld P ∩ fld Q = Λ) ∧
      codom (Psec Q) ∉ (one : Set (Set (α → α → Prop)))) :
    Desc Beg Q (fun b => Psec (P ⤉ Q) =
      Psec P ⇸ (P ⇸ b) ⤉ (opL rsum P ⁏ (Psec Q ⥏ codom (Psec Q)))) := by
  obtain ⟨⟨⟨⟨⟨hPne, hJP⟩, hQ⟩, b, hb⟩, hd⟩, hc1⟩ := h
  have hJQ := (b2_serPo hQ).1
  have hcQ := b2_connex_of_ser hQ
  have hbf : b ∈ fld Q := let ⟨y, hy⟩ := hb.1; ⟨y, Or.inl hy⟩
  have hbP := b2_beg_not_fldP hd hb
  rw [b2_desc_of_refs (b2_refs_Beg_eq hQ hb)]
  have hfc := b2_fld_codom_restr (pm213_153 hQ) hc1
  have hsP := b2_fld_Psec_ne hJP hPne
  have repG : ∀ G, ((G ∈ sect Q ∧ G.Nonempty) ∧ G ∉ (one : Set (Set α))) →
      (P ⤉ Q) ⥏ (fld P ∪ G) = P ⤉ Q ⥏ G := fun G hG =>
    b2_rsum_fres_union hd hG.1.1.1 (b2_fld_fres_conn hcQ hG.1.1 hG.2 hG.1.2)
  have repb : (P ⤉ Q) ⥏ (fld P ∪ ι b) = P ⇸ b := b2_rsum_fres_unit hd hbf (b2_irrP hJQ)
  have hsb : fld P ∪ ι b ∈ sect (P ⤉ Q) :=
    (b2_sect_rsum hd).2 (Or.inr ⟨ι b, ⟨(b2_unit_sect hJQ).2 hb, b, rfl⟩, rfl⟩)
  have hsG : ∀ G, (G ∈ sect Q ∧ G.Nonempty) → fld P ∪ G ∈ sect (P ⤉ Q) ∧ (fld P ∪ G).Nonempty :=
    fun G hG => ⟨(b2_sect_rsum hd).2 (Or.inr ⟨G, hG, rfl⟩), let ⟨w, hw⟩ := hG.2; ⟨w, Or.inr hw⟩⟩
  have hsA : ∀ A, (A ∈ sect P ∧ A.Nonempty) → A ∈ sect (P ⤉ Q) ∧ A.Nonempty :=
    fun A hA => ⟨(b2_sect_rsum hd).2 (Or.inl hA.1), hA.2⟩
  have fT : ∀ G, ((G ∈ sect Q ∧ G.Nonempty) ∧ G ∉ (one : Set (Set α))) →
      P ⤉ Q ⥏ G ∈ fld (opL rsum P ⁏ (Psec Q ⥏ codom (Psec Q))) := fun G hG =>
    (b2_semi_graph_fld (f := rsum P) (Q := Psec Q ⥏ codom (Psec Q))).2
      ⟨Q ⥏ G, by rw [hfc]; exact (b2_mem_codom_Psec hQ).2 ⟨G, hG, rfl⟩, rfl⟩
  have fP : ∀ A, (A ∈ sect P ∧ A.Nonempty) → P ⥏ A ∈ fld (Psec P) := fun A hA => by
    rw [pm213_142 hJP]; exact ⟨A, b2_mem_diff_iotaNull.2 hA, rfl⟩
  have hbG : ∀ G, (G ∈ sect Q ∧ G.Nonempty) → b ∈ G := fun G hG => b2_beg_mem hQ hb hG.1 hG.2
  funext X Y; apply propext
  rw [rsum_apply, addLast_apply, b2_Psec]
  constructor
  · rintro ⟨A, B, ⟨⟨hA, hB⟩, hdiff⟩, rfl, rfl⟩
    rcases b2_cls_rsum hd hQ hb hA.1 hA.2 with hA' | rfl | ⟨G, hG, rfl⟩ <;>
      rcases b2_cls_rsum hd hQ hb hB.1 hB.2 with hB' | rfl | ⟨H, hH, rfl⟩
    · rw [b2_rsum_fres_P hd hA'.1.1, b2_rsum_fres_P hd hB'.1.1]
      exact Or.inl (Or.inl (Or.inl (b2_Psec.2 ⟨A, B, ⟨⟨hA', hB'⟩, hdiff⟩, rfl, rfl⟩)))
    · rw [b2_rsum_fres_P hd hA'.1.1, repb]
      exact Or.inl (Or.inl (Or.inr ⟨fP A hA', rfl⟩))
    · rw [b2_rsum_fres_P hd hA'.1.1, repG H hH]
      exact Or.inr ⟨b2_fld_addLast.2 (Or.inl (fP A hA')), fT H hH⟩
    · obtain ⟨z, hzB, hzA⟩ := hdiff; exact absurd (Or.inl (hB'.1.1 hzB)) hzA
    · obtain ⟨z, hzB, hzA⟩ := hdiff; exact absurd hzB hzA
    · rw [repb, repG H hH]
      exact Or.inr ⟨b2_fld_addLast.2 (Or.inr ⟨hsP, rfl⟩), fT H hH⟩
    · obtain ⟨z, hzB, hzA⟩ := hdiff; exact absurd (Or.inl (hB'.1.1 hzB)) hzA
    · obtain ⟨z, hzB, hzA⟩ := hdiff
      rcases hzB with h' | h'
      · exact absurd (Or.inl h') hzA
      · rw [b2_mem_iota] at h'; subst h'; exact absurd (Or.inr (hbG G hG.1)) hzA
    · rw [repG G hG, repG H hH]
      obtain ⟨z, hzB, hzA⟩ := hdiff
      have hzH : z ∈ H := by
        rcases hzB with h' | h'
        · exact absurd (Or.inl h') hzA
        · exact h'
      have m1 := (b2_mem_codom_Psec hQ).2 ⟨G, hG, rfl⟩
      have m2 := (b2_mem_codom_Psec hQ).2 ⟨H, hH, rfl⟩
      refine Or.inl (Or.inr ((semi_graph_apply _ _ _ _).2 ⟨Q ⥏ G, Q ⥏ H, ⟨rfl, rfl⟩, ?_⟩))
      exact ⟨⟨m1, b2_Psec.2 ⟨G, H, ⟨⟨hG.1, hH.1⟩, z, hzH, fun h' => hzA (Or.inr h')⟩, rfl, rfl⟩⟩, m2⟩
  · rintro (((hXY | ⟨hX, rfl⟩) | hXY) | ⟨hX, hY⟩)
    · obtain ⟨A, B, ⟨⟨hA, hB⟩, hdiff⟩, rfl, rfl⟩ := b2_Psec.1 hXY
      exact ⟨A, B, ⟨⟨hsA A hA, hsA B hB⟩, hdiff⟩,
        (b2_rsum_fres_P hd hA.1.1).symm, (b2_rsum_fres_P hd hB.1.1).symm⟩
    · obtain ⟨A, hA, rfl⟩ := b2_mem_fld_Psec hX
      exact ⟨A, fld P ∪ ι b, ⟨⟨hsA A hA, hsb, b, Or.inr rfl⟩,
        b, Or.inr rfl, fun h' => hbP (hA.1.1 h')⟩, (b2_rsum_fres_P hd hA.1.1).symm, repb.symm⟩
    · obtain ⟨Q1, Q2, ⟨rfl, rfl⟩, ⟨⟨hQ1, hQ12⟩, hQ2⟩⟩ := (semi_graph_apply _ _ _ _).1 hXY
      obtain ⟨G, H, ⟨⟨hG, hH⟩, z, hzH, hzG⟩, rfl, rfl⟩ := b2_Psec.1 hQ12
      have hG1 : G ∉ (one : Set (Set α)) := by
        obtain ⟨G', ⟨hG', h1'⟩, e3⟩ := (b2_mem_codom_Psec hQ).1 hQ1
        intro h1
        exact (b2_fres_ne_null hQ hG'.1).2 ⟨hG'.2, h1'⟩
          (e3.symm.trans ((b2_fres_null_iff hQ hG.1 hG.2).2 h1))
      have hH1 : H ∉ (one : Set (Set α)) := by
        obtain ⟨H', ⟨hH', h1'⟩, e3⟩ := (b2_mem_codom_Psec hQ).1 hQ2
        intro h1
        exact (b2_fres_ne_null hQ hH'.1).2 ⟨hH'.2, h1'⟩
          (e3.symm.trans ((b2_fres_null_iff hQ hH.1 hH.2).2 h1))
      refine ⟨fld P ∪ G, fld P ∪ H, ⟨⟨hsG G hG, hsG H hH⟩, z, Or.inr hzH, ?_⟩,
        (repG G ⟨hG, hG1⟩).symm, (repG H ⟨hH, hH1⟩).symm⟩
      rintro (h' | h')
      · exact b2_disj hd h' (hH.1.1 hzH)
      · exact hzG h'
    · obtain ⟨Q', hQ', rfl⟩ := (b2_semi_graph_fld (f := rsum P)
        (Q := Psec Q ⥏ codom (Psec Q))).1 hY
      obtain ⟨H, hH, rfl⟩ := (b2_mem_codom_Psec hQ).1 (b2_fld_fres_sub _ _ hQ')
      rcases b2_fld_addLast.1 hX with hX | ⟨-, rfl⟩
      · obtain ⟨A, hA, rfl⟩ := b2_mem_fld_Psec hX
        exact ⟨A, fld P ∪ H, ⟨⟨hsA A hA, hsG H hH.1⟩,
          b2_diff_union hd hA.1.1 hH.1.1.1 hH.1.2⟩,
          (b2_rsum_fres_P hd hA.1.1).symm, (repG H hH).symm⟩
      · have : ∃ z, z ∈ H ∧ z ≠ b := by
          by_contra hn; push Not at hn
          exact hH.2 ⟨b, Set.ext fun z => ⟨fun hz => hn z hz,
            fun hz => (b2_mem_iota.1 hz) ▸ hbG H hH.1⟩⟩
        obtain ⟨z, hzH, hzb⟩ := this
        refine ⟨fld P ∪ ι b, fld P ∪ H, ⟨⟨⟨hsb, b, Or.inr rfl⟩, hsG H hH.1⟩, z, Or.inr hzH, ?_⟩,
          repb.symm, (repG H hH).symm⟩
        rintro (h' | h')
        · exact b2_disj hd h' (hH.1.1.1 hzH)
        · exact hzb h'

/-- ✱213·541. \(\vdash :P_{\text{po}}\in \text{Ser}.\exists !\overrightarrow{B}ʻP.\text{ᗡ}ʻP_{\varsigma }\in 1.\supset .P\in 2_{r}\) -/
theorem pm213_541 {P : α → α → Prop}
    (h : (po P ∈ Ser ∧ (refs Beg P).Nonempty) ∧ codom (Psec P) ∈ (one : Set (Set (α → α → Prop)))) :
    P ∈ (two_r : Set (α → α → Prop)) := by
  obtain ⟨⟨h, b, hb⟩, X, hX⟩ := h
  have hJ := (b2_serPo h).1
  obtain ⟨⟨y, hby⟩, hbc⟩ := hb
  have hPnull : P ≠ rNull := fun e => by rw [e] at hby; exact hby ⟨rfl, rfl⟩
  have hPc : P ∈ codom (Psec P) := by
    rw [pm213_162 h]
    exact ⟨⟨fld P, b2_fld_mem_sect P, (b2_fres_fld P).symm⟩, hPnull⟩
  rw [hX] at hPc
  have key : ∀ z, z ∈ fld P → z ≠ b → ∀ w, w ∈ fld P → anc P w z := by
    intro z hz hzb w hw
    have hs := b2_refs_anc_mem_sect P z
    have hbz : anc P b z := b2_beg_anc h ⟨⟨y, hby⟩, hbc⟩ hz
    have h1 : refs (anc P) z ∉ (one : Set (Set α)) := by
      rintro ⟨c, hc⟩
      have m1 : b ∈ refs (anc P) z := hbz
      have m2 : z ∈ refs (anc P) z := b2_anc_refl hz
      rw [hc, b2_mem_iota] at m1 m2
      exact hzb (m2.trans m1.symm)
    have hne : (refs (anc P) z).Nonempty := ⟨z, b2_anc_refl hz⟩
    have hc : P ⥏ refs (anc P) z ∈ codom (Psec P) := by
      rw [pm213_162 h]
      exact ⟨⟨_, hs, rfl⟩, (b2_fres_ne_null h hs).2 ⟨hne, h1⟩⟩
    rw [hX, b2_mem_iota] at hc
    rw [b2_mem_iota] at hPc
    have e := b2_fres_eq_self hs.1 (hc.trans hPc.symm)
    have : w ∈ refs (anc P) z := e ▸ hw
    exact this
  have hyf : y ∈ fld P := ⟨b, Or.inr hby⟩
  have hyb : y ≠ b := fun e => b2_irrP hJ (e ▸ hby)
  refine ⟨b, y, hyb.symm, ?_⟩
  funext u v; apply propext
  rw [couple_apply]
  constructor
  · intro huv
    have hv : v ∈ fld P := ⟨u, Or.inr huv⟩
    have hu : u ∈ fld P := ⟨v, Or.inl huv⟩
    have hvb : v ≠ b := fun e => hbc ⟨u, e ▸ huv⟩
    have hvy : v = y := by
      by_contra hvy
      have a1 := key v hv hvb y hyf
      have a2 := key y hyf hyb v hv
      rcases anc_iff_po.1 a1 with ⟨e, -⟩ | p1
      · exact hvy e.symm
      · exact hJ y (b2_po_of_po_anc p1 a2)
    subst hvy
    refine ⟨?_, rfl⟩
    by_contra hub
    have a1 := key u hu hub v hv
    exact hJ u (b2_po_of_P_anc huv a1)
  · rintro ⟨rfl, rfl⟩; exact hby

private theorem b2_couple_ser {x y : α} (h : x ≠ y) : x ↓ y ∈ Ser := by
  rw [mem_Ser]
  refine ⟨⟨fun z hz => h (hz.1.symm.trans hz.2), fun a b c ⟨h1, h2⟩ => ?_⟩, fun a b ⟨ha, hb⟩ => ?_⟩
  · exact absurd (h2.1.symm.trans h1.2) h
  · have hf : ∀ z, z ∈ fld (x ↓ y) → z = x ∨ z = y := by
      rintro z ⟨w, ⟨h1, -⟩ | ⟨-, h1⟩⟩
      · exact Or.inl h1
      · exact Or.inr h1
    rcases hf a ha with rfl | rfl <;> rcases hf b hb with rfl | rfl
    · exact Or.inl (Or.inr rfl)
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl (Or.inr rfl)

private theorem b2_couple_beg {x y : α} (h : x ≠ y) : x ∈ refs Beg (x ↓ y) :=
  ⟨⟨y, rfl, rfl⟩, fun ⟨z, hz⟩ => h hz.2⟩

/-- ✱213·55. \[\begin{align}\vdash :\dot{\exists} !P.P_{\text{po}}\,\unicode{x2abd}\, J.Q\in 2_{r}.&CʻP\cap CʻQ=\Lambda .\supset .\\ &(P\unicode{x2909}Q)_{\varsigma }=P_{\varsigma }\unicode{x21f8} (P\unicode{x21f8} BʻQ)\unicode{x21f8} (P\unicode{x2909}Q)\end{align}\] -/
theorem pm213_55 {P Q : α → α → Prop}
    (h : ((rEx P ∧ po P ⪽ J) ∧ Q ∈ (two_r : Set (α → α → Prop))) ∧ fld P ∩ fld Q = Λ) :
    Desc Beg Q (fun b => Psec (P ⤉ Q) = Psec P ⇸ (P ⇸ b) ⇸ (P ⤉ Q)) := by
  obtain ⟨⟨⟨hPne, hJP⟩, x, y, hxy, rfl⟩, hd⟩ := h
  have hQs := b2_couple_ser hxy
  have hQ : po (x ↓ y) ∈ Ser := b2_ser_po hQs
  have hJQ := (b2_serPo hQ).1
  have hb := b2_couple_beg hxy
  have hbf : x ∈ fld (x ↓ y) := ⟨y, Or.inl ⟨rfl, rfl⟩⟩
  have hyf : y ∈ fld (x ↓ y) := ⟨x, Or.inr ⟨rfl, rfl⟩⟩
  have hbP := b2_beg_not_fldP hd hb
  rw [b2_desc_of_refs (b2_refs_Beg_eq hQ hb)]
  have hsP := b2_fld_Psec_ne hJP hPne
  have repb : (P ⤉ x ↓ y) ⥏ (fld P ∪ ι x) = P ⇸ x := b2_rsum_fres_unit hd hbf (b2_irrP hJQ)
  have repF : (P ⤉ x ↓ y) ⥏ (fld P ∪ fld (x ↓ y)) = P ⤉ x ↓ y := by
    rw [← fld_rsum, b2_fres_fld]
  have hsb : fld P ∪ ι x ∈ sect (P ⤉ x ↓ y) :=
    (b2_sect_rsum hd).2 (Or.inr ⟨ι x, ⟨(b2_unit_sect hJQ).2 hb, x, rfl⟩, rfl⟩)
  have hsF : fld P ∪ fld (x ↓ y) ∈ sect (P ⤉ x ↓ y) :=
    (b2_sect_rsum hd).2 (Or.inr ⟨fld (x ↓ y), ⟨b2_fld_mem_sect _, x, hbf⟩, rfl⟩)
  have hsA : ∀ A, (A ∈ sect P ∧ A.Nonempty) → A ∈ sect (P ⤉ x ↓ y) ∧ A.Nonempty :=
    fun A hA => ⟨(b2_sect_rsum hd).2 (Or.inl hA.1), hA.2⟩
  have fP : ∀ A, (A ∈ sect P ∧ A.Nonempty) → P ⥏ A ∈ fld (Psec P) := fun A hA => by
    rw [pm213_142 hJP]; exact ⟨A, b2_mem_diff_iotaNull.2 hA, rfl⟩
  have hG : ∀ G, ((G ∈ sect (x ↓ y) ∧ G.Nonempty) ∧ G ∉ (one : Set (Set α))) →
      G = fld (x ↓ y) := by
    rintro G ⟨⟨hG, hne⟩, h1⟩
    have hxG : x ∈ G := b2_beg_mem hQ hb hG hne
    refine Set.Subset.antisymm hG.1 ?_
    rintro z ⟨w, ⟨rfl, -⟩ | ⟨-, rfl⟩⟩
    · exact hxG
    · by_contra hyG
      refine h1 ⟨x, Set.ext fun v => ⟨fun hv => ?_, fun hv => (b2_mem_iota.1 hv) ▸ hxG⟩⟩
      obtain ⟨u, ⟨rfl, -⟩ | ⟨-, rfl⟩⟩ := hG.1 hv
      · rfl
      · exact absurd hv hyG
  funext X Y; apply propext
  rw [addLast_apply, addLast_apply, b2_Psec]
  constructor
  · rintro ⟨A, B, ⟨⟨hA, hB⟩, hdiff⟩, rfl, rfl⟩
    rcases b2_cls_rsum hd hQ hb hA.1 hA.2 with hA' | rfl | ⟨G, hG', rfl⟩ <;>
      rcases b2_cls_rsum hd hQ hb hB.1 hB.2 with hB' | rfl | ⟨H, hH', rfl⟩
    · rw [b2_rsum_fres_P hd hA'.1.1, b2_rsum_fres_P hd hB'.1.1]
      exact Or.inl (Or.inl (b2_Psec.2 ⟨A, B, ⟨⟨hA', hB'⟩, hdiff⟩, rfl, rfl⟩))
    · rw [b2_rsum_fres_P hd hA'.1.1, repb]
      exact Or.inl (Or.inr ⟨fP A hA', rfl⟩)
    · rw [b2_rsum_fres_P hd hA'.1.1, hG H hH', repF]
      exact Or.inr ⟨b2_fld_addLast.2 (Or.inl (fP A hA')), rfl⟩
    · obtain ⟨z, hzB, hzA⟩ := hdiff; exact absurd (Or.inl (hB'.1.1 hzB)) hzA
    · obtain ⟨z, hzB, hzA⟩ := hdiff; exact absurd hzB hzA
    · rw [repb, hG H hH', repF]
      exact Or.inr ⟨b2_fld_addLast.2 (Or.inr ⟨hsP, rfl⟩), rfl⟩
    · obtain ⟨z, hzB, hzA⟩ := hdiff; exact absurd (Or.inl (hB'.1.1 hzB)) hzA
    · obtain ⟨z, hzB, hzA⟩ := hdiff
      rcases hzB with h' | h'
      · exact absurd (Or.inl h') hzA
      · rw [b2_mem_iota] at h'; subst h'
        exact absurd (Or.inr (b2_beg_mem hQ hb hG'.1.1 hG'.1.2)) hzA
    · rw [hG G hG', hG H hH'] at hdiff
      obtain ⟨z, hzB, hzA⟩ := hdiff; exact absurd hzB hzA
  · rintro ((hXY | ⟨hX, rfl⟩) | ⟨hX, rfl⟩)
    · obtain ⟨A, B, ⟨⟨hA, hB⟩, hdiff⟩, rfl, rfl⟩ := b2_Psec.1 hXY
      exact ⟨A, B, ⟨⟨hsA A hA, hsA B hB⟩, hdiff⟩,
        (b2_rsum_fres_P hd hA.1.1).symm, (b2_rsum_fres_P hd hB.1.1).symm⟩
    · obtain ⟨A, hA, rfl⟩ := b2_mem_fld_Psec hX
      exact ⟨A, fld P ∪ ι x, ⟨⟨hsA A hA, hsb, x, Or.inr rfl⟩,
        x, Or.inr rfl, fun h' => hbP (hA.1.1 h')⟩, (b2_rsum_fres_P hd hA.1.1).symm, repb.symm⟩
    · rcases b2_fld_addLast.1 hX with hX | ⟨-, rfl⟩
      · obtain ⟨A, hA, rfl⟩ := b2_mem_fld_Psec hX
        exact ⟨A, fld P ∪ fld (x ↓ y), ⟨⟨hsA A hA, hsF, x, Or.inr hbf⟩,
          b2_diff_union hd hA.1.1 (le_refl _) ⟨x, hbf⟩⟩,
          (b2_rsum_fres_P hd hA.1.1).symm, repF.symm⟩
      · refine ⟨fld P ∪ ι x, fld P ∪ fld (x ↓ y), ⟨⟨⟨hsb, x, Or.inr rfl⟩, hsF, x, Or.inr hbf⟩,
          y, Or.inr hyf, ?_⟩, repb.symm, repF.symm⟩
        rintro (h' | h')
        · exact b2_disj hd h' hyf
        · exact hxy (b2_mem_iota.1 h').symm

/-- ✱213·56. \[\begin{align}\vdash \colon\ldotp &P_{\text{po}}\,\unicode{x2abd}\, J.Q_{\text{po}}\in \text{Ser}.CʻP\cap CʻQ=\Lambda .\supset :\\ &\overrightarrow{B}ʻQ=\Lambda .\supset .(P\unicode{x2909}Q)_{\varsigma }=P_{\varsigma }\unicode{x2909}(P\unicode{x2909}^{;}Q_{\varsigma }):\\ &\dot{\exists} !P.\exists !\overrightarrow{B}ʻQ.Q{\sim}\in 2_{r}.\supset .\\ &(P\unicode{x2909}Q)_{\varsigma }=P_{\varsigma }\unicode{x21f8} (P\unicode{x21f8} BʻQ)\unicode{x2909}\{P\unicode{x2909}^{;}(Q_{\varsigma }\unicode{x0294f}\text{ᗡ}ʻQ_{\varsigma })\}:\\ &\dot{\exists} !P.Q\in 2_{r}.\supset .(P\unicode{x2909}Q)_{\varsigma }=P_{\varsigma }\unicode{x21f8} (P\unicode{x21f8} BʻQ)\unicode{x21f8} (P\unicode{x2909}Q):\\ &P=\dot{\Lambda} .\supset .(P\unicode{x2909}Q)_{\varsigma }=Q_{\varsigma } \quad[*213·53·54·541·55.*160·22]\end{align}\] -/
theorem pm213_56 {P Q : α → α → Prop} (h : (po P ⪽ J ∧ po Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) :
    (((refs Beg Q = Λ → Psec (P ⤉ Q) = Psec P ⤉ (opL rsum P ⁏ Psec Q)) ∧
      ((rEx P ∧ (refs Beg Q).Nonempty) ∧ Q ∉ (two_r : Set (α → α → Prop)) →
        Desc Beg Q (fun b => Psec (P ⤉ Q) =
          Psec P ⇸ (P ⇸ b) ⤉ (opL rsum P ⁏ (Psec Q ⥏ codom (Psec Q)))))) ∧
      (rEx P ∧ Q ∈ (two_r : Set (α → α → Prop)) →
        Desc Beg Q (fun b => Psec (P ⤉ Q) = Psec P ⇸ (P ⇸ b) ⇸ (P ⤉ Q)))) ∧
      (P = rNull → Psec (P ⤉ Q) = Psec Q) := by
  obtain ⟨⟨hJP, hQ⟩, hd⟩ := h
  refine ⟨⟨⟨fun h0 => pm213_53 ⟨⟨⟨hJP, hQ⟩, h0⟩, hd⟩, fun ⟨⟨hP, hb⟩, h2⟩ => ?_⟩,
    fun ⟨hP, h2⟩ => pm213_55 ⟨⟨⟨hP, hJP⟩, h2⟩, hd⟩⟩, fun h0 => ?_⟩
  · refine pm213_54 ⟨⟨⟨⟨⟨hP, hJP⟩, hQ⟩, hb⟩, hd⟩, fun h1 => h2 (pm213_541 ⟨⟨hQ, hb⟩, h1⟩)⟩
  · subst h0
    congr 1
    funext u v; apply propext
    rw [rsum_apply]
    constructor
    · rintro ((h' | h') | ⟨⟨w, hw | hw⟩, -⟩)
      · exact absurd ⟨rfl, rfl⟩ h'
      · exact h'
      · exact absurd ⟨rfl, rfl⟩ hw
      · exact absurd ⟨rfl, rfl⟩ hw
    · intro h'; exact Or.inl (Or.inr h')

private theorem b2_rsum_restrict {P Q1 Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) (hs : fld Q1 ⊆ fld Q) :
    (P ⤉ Q1) ⥏ fld Q = Q1 := by
  funext u v; apply propext
  constructor
  · rintro ⟨⟨hu, huv⟩, hv⟩
    rcases (rsum_apply _ _ _ _).1 huv with (h | h) | ⟨h, -⟩
    · exact (b2_disj hd ⟨v, Or.inl h⟩ hu).elim
    · exact h
    · exact (b2_disj hd h hu).elim
  · intro huv
    exact ⟨⟨hs ⟨v, Or.inl huv⟩, (rsum_apply _ _ _ _).2 (Or.inl (Or.inr huv))⟩, hs ⟨u, Or.inr huv⟩⟩

/-- ✱213·561. \(\vdash :CʻP\cap CʻQ=\Lambda .\supset .(P\unicode{x2909})\unicode{x0294f}CʻQ_{\varsigma }\in 1\rightarrow 1\)

**Status.** proved (reading): the e-text prints `(P⤉)⥏C'Q_ς` (field limitation) for `(P⤉)↾C'Q_ς`
(converse-domain limitation, as in ✱213·151 and ✱217·24·25): PM's proof shows that `P⤉R = P⤉S`
implies `R = S` for `R, S ∈ C'Q_ς`, and ✱213·58 uses the proposition for `Nr'P⤉;Q_ς = Nr'Q_ς`,
which needs `(P⤉)↾C'Q_ς ∈ 1 → 1`. The stated form implies the printed one, since
`(P⤉)⥏C'Q_ς ⊂̇ (P⤉)↾C'Q_ς`. -/
theorem pm213_561 {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) :
    opL rsum P ↾ fld (Psec Q) ∈ arrow one one := by
  rw [mem_arrow_one_one]
  constructor
  · rintro X Y Z ⟨⟨hX, -⟩, ⟨hY, -⟩⟩
    exact hX.trans hY.symm
  · rintro X Q1 Q2 ⟨⟨h1, hQ1⟩, ⟨h2, hQ2⟩⟩
    obtain ⟨G, -, rfl⟩ := b2_mem_fld_Psec hQ1
    obtain ⟨H, -, rfl⟩ := b2_mem_fld_Psec hQ2
    have e : (P ⤉ Q ⥏ G) = (P ⤉ Q ⥏ H) := h1.symm.trans h2
    rw [← b2_rsum_restrict (P := P) hd (b2_fld_sub_of_rsub (b2_fres_sub G)),
      ← b2_rsum_restrict (P := P) hd (b2_fld_sub_of_rsub (b2_fres_sub (P := Q) H)), e]

/-- A series `R` with beginning `c` and `ᗡ'R ∼∈ 1` is `c ⇷ R⥏ᗡ'R` (cf. ✱204·46). -/
private theorem b2_ser_beg_split {R : α → α → Prop} (hR : R ∈ Ser) {c : α} (hc : c ∈ refs Beg R)
    (h1 : codom R ∉ (one : Set (Set α))) : R = c ⇷ (R ⥏ codom R) := by
  obtain ⟨-, hcon⟩ := mem_Ser.1 hR
  have hcf : c ∈ fld R := let ⟨y, hy⟩ := hc.1; ⟨y, Or.inl hy⟩
  funext u v; apply propext
  rw [addFirst_apply, b2_fld_codom_restr hR h1, b2_fres_apply]
  constructor
  · intro huv
    have hv : v ∈ codom R := ⟨u, huv⟩
    by_cases hu : u ∈ codom R
    · exact Or.inr ⟨⟨hu, huv⟩, hv⟩
    · refine Or.inl ⟨?_, hv⟩
      rcases hcon u c ⟨⟨v, Or.inl huv⟩, hcf⟩ with (h' | e) | h'
      · exact absurd ⟨u, h'⟩ hc.2
      · exact e
      · exact absurd ⟨c, h'⟩ hu
  · rintro (⟨e, ⟨w, hw⟩⟩ | ⟨⟨-, h'⟩, -⟩)
    · rw [e]
      have hvf : v ∈ fld R := ⟨w, Or.inr hw⟩
      rcases hcon c v ⟨hcf, hvf⟩ with (h' | e') | h'
      · exact h'
      · rw [← e'] at hw; exact absurd ⟨w, hw⟩ hc.2
      · exact absurd ⟨v, h'⟩ hc.2
    · exact h'

/-- ✱213·57. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\text{Nr}ʻQ=\text{Nr}ʻP\dot{+} \dot{1} .\supset .\text{Nr}ʻQ_{\varsigma }=\text{Nr}ʻP_{\varsigma }\dot{+} \dot{1}\) -/
theorem pm213_57 {β : Type v} (δ : Type w) {P : α → α → Prop} {Q : β → β → Prop}
    (h : po P ⪽ J ∧ nr β Q = (nrAddOne δ (n₀r P) : Set (β → β → Prop))) :
    nr (β → β → Prop) (Psec Q) =
      (nrAddOne δ (n₀r (Psec P)) : Set ((β → β → Prop) → (β → β → Prop) → Prop)) := by
  obtain ⟨hJ, hQ⟩ := h
  have hQm : Q ∈ (nrAddOne δ (n₀r P) : Set (β → β → Prop)) := hQ ▸ self_mem_nr Q
  obtain ⟨P', x, hP', hQx⟩ := hQm
  obtain ⟨L, e, hLe, hL, he⟩ := b2r_addLastDot_split P x
  have hQL : smor Q (L ⇸ e) := by
    rw [← hLe]; exact smor_trans hQx (b2r_smor_addLastDot (n₀r_eq_n₀r_iff.1 hP') x x)
  have hJL : po L ⪽ J := b2_poJ_of_smor (smor_symm hL) hJ
  have hnot : (L ⇸ e) ∉ fld (Psec L) := by
    intro hm
    by_cases hr : rEx L
    · obtain ⟨A, -, hA⟩ := b2_mem_fld_Psec hm
      obtain ⟨u, hu⟩ := b2r_rEx_iff_fld.1 hr
      have : (L ⇸ e) u e := Or.inr ⟨hu, rfl⟩
      rw [hA] at this
      exact he ⟨u, Or.inr this.1.2⟩
    · have e0 : L = rNull := b2_eq_rNull.2 fun a b hab => hr ⟨a, b, hab⟩
      rw [e0, pm213_3 rfl] at hm
      obtain ⟨_, hh | hh⟩ := hm <;> exact rNull_apply _ _ hh
  rw [b2r_nrAddOne_n₀r (Psec P) x]
  apply nr_eq_nr_of_smor
  refine smor_trans (b2_Psec_smor hQL) ?_
  rw [pm213_51 ⟨hJL, he⟩]
  exact b2r_smor_addLast_dot (b2_Psec_smor hL) hnot x

/-- ✱213·58. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.Q_{\text{po}}\in \text{Ser}.CʻP\cap CʻQ=\Lambda .\supset .\text{Nr}ʻ(P\unicode{x2909}Q)_{\varsigma }=\text{Nr}ʻP_{\varsigma }\dot{+} \text{Nr}ʻQ_{\varsigma }\) -/
theorem pm213_58 {P Q : α → α → Prop} (h : (po P ⪽ J ∧ po Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) :
    nr (α → α → Prop) (Psec (P ⤉ Q)) =
      (n₀r (Psec P) ∔ n₀r (Psec Q) : Set ((α → α → Prop) → (α → α → Prop) → Prop)) := by
  have h56 := pm213_56 h
  obtain ⟨⟨hJP, hQ⟩, hd⟩ := h
  rw [b2r_n₀r_nrAdd_n₀r]
  apply nr_eq_nr_of_smor
  suffices H : ∃ L R, Psec (P ⤉ Q) = L ⤉ R ∧ (smor L (Psec P) ∧ smor R (Psec Q)) ∧
      Disjoint (fld L) (fld R) by
    obtain ⟨L, R, e, ⟨hL, hR⟩, hLR⟩ := H
    rw [e]; exact b2r_smor_rsum_rplus hL hR hLR
  have hJQ := (b2_serPo hQ).1
  have hQJ : po Q ⪽ J := b2_J_of_ser hQ
  have fldPsecQ : ∀ T, T ∈ fld (Psec Q) → fld T ⊆ fld Q := by
    intro T hT
    obtain ⟨G, -, rfl⟩ := b2_mem_fld_Psec hT
    exact b2_fld_sub_of_rsub (b2_fres_sub G)
  have inj : ∀ T1 T2 : α → α → Prop, fld T1 ⊆ fld Q → fld T2 ⊆ fld Q → P ⤉ T1 = P ⤉ T2 →
      T1 = T2 := by
    intro T1 T2 h1 h2 e
    rw [← b2_rsum_restrict hd h1, ← b2_rsum_restrict hd h2, e]
  have neq : ∀ (A : Set α) (T : α → α → Prop), fld T ⊆ fld Q → rEx T → P ⥏ A ≠ P ⤉ T := by
    intro A T hT hr e
    obtain ⟨z, w, hzw⟩ := hr
    have : (P ⤉ T) z w := (rsum_apply _ _ _ _).2 (Or.inl (Or.inr hzw))
    rw [← e] at this
    exact b2_disj hd ⟨w, Or.inl this.1.2⟩ (hT ⟨w, Or.inl hzw⟩)
  have hcodQ : ∀ X, X ∈ codom (Psec Q) → rEx X ∧ fld X ⊆ fld Q := by
    intro X hX
    obtain ⟨G, ⟨hG, h1⟩, rfl⟩ := (b2_mem_codom_Psec hQ).1 hX
    exact ⟨b2_rEx_iff_ne.2 fun e => h1 ((b2_fres_null_iff hQ hG.1 hG.2).1 e),
      b2_fld_sub_of_rsub (b2_fres_sub G)⟩
  by_cases hP : rEx P
  swap
  · have e0 : P = rNull := b2_eq_rNull.2 fun x y hxy => hP ⟨x, y, hxy⟩
    refine ⟨rNull, Psec Q, ?_, ⟨?_, smor_refl _⟩, ?_⟩
    · rw [h56.2 e0, b2r_rNull_rsum]
    · rw [pm213_3 e0]; exact smor_refl _
    · rw [b2r_fld_rNull]; exact Set.empty_disjoint _
  have hPs : rEx (Psec P) := (pm213_302 hJP).1 hP
  by_cases hb : (refs Beg Q).Nonempty
  swap
  · have h0 : refs Beg Q = Λ := by
      rw [Null_eq_empty]; exact Set.not_nonempty_iff_eq_empty.1 hb
    refine ⟨Psec P, opL rsum P ⁏ Psec Q, h56.1.1.1 h0, ⟨smor_refl _, ?_⟩, ?_⟩
    · exact b2r_smor_graph fun z w hz hw e => inj z w (fldPsecQ z hz) (fldPsecQ w hw) e
    · refine Set.disjoint_left.2 fun X hX hX' => ?_
      obtain ⟨A, -, rfl⟩ := b2_mem_fld_Psec hX
      obtain ⟨T, hT, e⟩ := b2r_mem_fld_graph_semi.1 hX'
      obtain ⟨G, hG, rfl⟩ := b2_mem_fld_Psec hT
      have h1 : G ∉ (one : Set (Set α)) := by
        rintro ⟨c, rfl⟩
        have := (b2_unit_sect hJQ).1 hG.1
        rw [h0, Null_eq_empty] at this; exact this
      exact neq A _ (b2_fld_sub_of_rsub (b2_fres_sub G))
        (b2_rEx_iff_ne.2 fun e' => h1 ((b2_fres_null_iff hQ hG.1 hG.2).1 e')) e
  obtain ⟨b, hbQ⟩ := hb
  have hbP : b ∉ fld P := b2_beg_not_fldP hd hbQ
  have neqb : ∀ A : Set α, P ⥏ A ≠ P ⇸ b := by
    intro A e
    obtain ⟨u, hu⟩ := b2r_rEx_iff_fld.1 hP
    have : (P ⇸ b) u b := Or.inr ⟨hu, rfl⟩
    rw [← e] at this
    exact hbP ⟨u, Or.inr this.1.2⟩
  have hQne : rEx Q := let ⟨y, hy⟩ := hbQ.1; ⟨b, y, hy⟩
  by_cases h2 : Q ∈ (two_r : Set (α → α → Prop))
  · have hD := h56.1.2 ⟨hP, h2⟩
    rw [b2_desc_of_refs (b2_refs_Beg_eq hQ hbQ)] at hD
    have ne1 : P ⇸ b ≠ P ⤉ Q := by
      intro e
      obtain ⟨y, hy⟩ := hbQ.1
      have : (P ⤉ Q) b y := (rsum_apply _ _ _ _).2 (Or.inl (Or.inr hy))
      rw [← e] at this
      rcases this with h' | ⟨h', -⟩
      · exact hbP ⟨y, Or.inl h'⟩
      · exact hbP h'
    have hdis : Disjoint (fld (Psec P)) (fld ((P ⇸ b) ↓ (P ⤉ Q))) := by
      refine Set.disjoint_left.2 fun X hX hX' => ?_
      obtain ⟨A, -, rfl⟩ := b2_mem_fld_Psec hX
      rw [b2r_fld_couple, Set.mem_insert_iff, Set.mem_singleton_iff] at hX'
      rcases hX' with e | e
      · exact neqb A e
      · exact neq A Q subset_rfl hQne e
    obtain ⟨x, y, hxy, rfl⟩ := h2
    refine ⟨Psec P, (P ⇸ b) ↓ (P ⤉ (x ↓ y)), ?_, ⟨smor_refl _, ?_⟩, hdis⟩
    · rw [hD, b2_addLast_addLast hPs]
    · rw [pm213_31 hxy]
      refine b2r_smor_couple ne1 fun e => ?_
      have : (x ↓ y) x y := ⟨rfl, rfl⟩
      rw [← e] at this; exact rNull_apply _ _ this
  · have hc1 : codom (Psec Q) ∉ (one : Set (Set (α → α → Prop))) := fun h1 =>
      h2 (pm213_541 ⟨⟨hQ, b, hbQ⟩, h1⟩)
    have hC := h56.1.1.2 ⟨⟨hP, b, hbQ⟩, h2⟩
    rw [b2_desc_of_refs (b2_refs_Beg_eq hQ hbQ)] at hC
    have hQs : Psec Q ∈ Ser := pm213_153 hQ
    have hfS1 : fld (Psec Q ⥏ codom (Psec Q)) = codom (Psec Q) := b2_fld_codom_restr hQs hc1
    have hbeg : (rNull : α → α → Prop) ∈ refs Beg (Psec Q) := by
      rw [b2_refs_Beg_Psec hQ hbQ]; exact Set.mem_singleton _
    have hsplit := b2_ser_beg_split hQs hbeg hc1
    have hT : smor (opL rsum P ⁏ (Psec Q ⥏ codom (Psec Q))) (Psec Q ⥏ codom (Psec Q)) := by
      refine b2r_smor_graph fun z w hz hw e => ?_
      rw [hfS1] at hz hw
      exact inj z w (hcodQ z hz).2 (hcodQ w hw).2 e
    have hrS1 : rEx (Psec Q ⥏ codom (Psec Q)) := by
      obtain ⟨X, Y, hXY⟩ := (pm213_302 hQJ).1 hQne
      exact b2r_rEx_iff_fld.2 ⟨Y, by rw [hfS1]; exact ⟨X, hXY⟩⟩
    have hrT := b2r_smor_preserves (smor_symm hT) hrS1
    have hPb : (P ⇸ b) ∉ fld (opL rsum P ⁏ (Psec Q ⥏ codom (Psec Q))) := by
      intro hm
      obtain ⟨T, hT', e⟩ := b2r_mem_fld_graph_semi.1 hm
      rw [hfS1] at hT'
      obtain ⟨⟨u, w, huw⟩, hsub⟩ := hcodQ T hT'
      have : (P ⤉ T) u w := (rsum_apply _ _ _ _).2 (Or.inl (Or.inr huw))
      have hu : u ∈ fld P := by
        rw [← e] at this
        rcases this with h' | ⟨h', -⟩
        · exact ⟨w, Or.inl h'⟩
        · exact h'
      exact b2_disj hd hu (hsub ⟨w, Or.inl huw⟩)
    have hnS1 : (rNull : α → α → Prop) ∉ fld (Psec Q ⥏ codom (Psec Q)) := by
      rw [hfS1]; intro hm
      obtain ⟨⟨u, w, huw⟩, -⟩ := hcodQ _ hm
      exact rNull_apply _ _ huw
    refine ⟨Psec P, (P ⇸ b) ⇷ (opL rsum P ⁏ (Psec Q ⥏ codom (Psec Q))), ?_, ⟨smor_refl _, ?_⟩, ?_⟩
    · rw [hC, b2_addLast_rsum hPs hrT]
    · have := b2r_smor_addFirst hT hPb hnS1
      rwa [← hsplit] at this
    · refine Set.disjoint_left.2 fun X hX hX' => ?_
      obtain ⟨A, -, rfl⟩ := b2_mem_fld_Psec hX
      obtain ⟨hX' | e, -⟩ := b2r_mem_fld_addFirst.1 hX'
      · obtain ⟨T, hT', e⟩ := b2r_mem_fld_graph_semi.1 hX'
        rw [hfS1] at hT'
        exact neq A T (hcodQ T hT').2 (hcodQ T hT').1 e
      · exact neqb A e


/-!
## [✱214] Dedekindian relations

*(Vol. 2, p. 684)*

> *Summary of* *214.
>
> We call a relation "Dedekindian" when it is such that every class has either a maximum or a sequent with respect to it. As a rule, the hypothesis that a relation is Dedekindian is only important in the case of serial relations. Dedekindian series have considerable importance, especially in connection with limits.
>
> …

**Lean reading.** `Ded`, `semi Ded` are classes of relations (Defs/Part5). `ᗡ'max_P ∪ ᗡ'seq_P` is
`codom (maxP P) ∪ codom (seqP P)`, `max⃗_P'α` is `refs (maxP P) A`; descriptions `seq_P'α`,
`limax_P'α`, `B'P` are `Desc`. A Dedekindian relation is irreflexive (the unit class of a term
`x` with `xPx` has neither maximum nor sequent), so ✱214·51–·54 hold trivially. For series the
proofs go through Dedekind cuts: for a section `α`, `seq_P'α = min_P'(C'P − α)` (✱211·721); for
transitive `P` a class and the section it generates have the same maxima and sequents. ✱214·3·31
take `κ`, `Q` as real variables with PM's hypotheses; ✱214·32–·34 apply them. Likeness is used
through its correlator `S` (`P = S;Q`), transporting maxima and sequents. The e-text numbers
✱214·11 "✱21·411" (it stands between ✱214·101 and ✱214·12).

**Status.** proved (all propositions; ✱214·01·02 definition; ✱214·131, ·141, ·151 proved (reading),
e-text misprints).
-/

end S213b

section S214

variable {α : Type u}

private theorem b2_maxP_inter {P : α → α → Prop} {x : α} {A : Set α} :
    maxP P x A ↔ maxP P x (A ∩ fld P) := by
  rw [maxP_iff, maxP_iff]
  constructor
  · rintro ⟨⟨hx, hf⟩, h⟩; exact ⟨⟨⟨hx, hf⟩, hf⟩, fun y hy => h y hy.1⟩
  · rintro ⟨⟨⟨hx, -⟩, hf⟩, h⟩
    exact ⟨⟨hx, hf⟩, fun y hy hxy => h y ⟨hy, ⟨x, Or.inr hxy⟩⟩ hxy⟩

private theorem b2_seqP_inter {P : α → α → Prop} {x : α} {A : Set α} :
    seqP P x A ↔ seqP P x (A ∩ fld P) := by
  show minP P x _ ↔ minP P x _
  rw [Set.inter_assoc, Set.inter_self]

private theorem b2_mem_union_codom {P : α → α → Prop} {A : Set α} :
    A ∈ codom (maxP P) ∪ codom (seqP P) ↔ (∃ x, maxP P x A) ∨ ∃ x, seqP P x A := Iff.rfl

private theorem b2_dunion_inter {P : α → α → Prop} {A : Set α} :
    A ∈ codom (maxP P) ∪ codom (seqP P) ↔ A ∩ fld P ∈ codom (maxP P) ∪ codom (seqP P) := by
  simp only [b2_mem_union_codom, b2_maxP_inter (A := A), b2_seqP_inter (A := A),
    b2_maxP_inter (A := A ∩ fld P), b2_seqP_inter (A := A ∩ fld P), Set.inter_assoc,
    Set.inter_self]

/-- ✱214·01 (Df). \(\text{Ded} = \hat{P}\{(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}\} \quad\text{Df}\) -/
theorem pm214_01 : (Ded : Set (α → α → Prop)) =
    {P | ∀ A : Set α, A ∈ codom (maxP P) ∪ codom (seqP P)} := rfl

/-- ✱214·02 (Df). \(\text{semi Ded} = \hat{P} (\text{sect}ʻP-\iota ʻCʻP\subset \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}) \quad\text{Df}\) -/
theorem pm214_02 : (semiDed : Set (α → α → Prop)) =
    {P | sect P \ ι (fld P) ⊆ codom (maxP P) ∪ codom (seqP P)} := rfl

/-- ✱214·1. \(\vdash :P\in \text{Ded}. \equiv .(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P} \quad[(*214·01)]\) -/
theorem pm214_1 {P : α → α → Prop} :
    P ∈ Ded ↔ ∀ A : Set α, A ∈ codom (maxP P) ∪ codom (seqP P) := Iff.rfl

/-- ✱214·101. \[\begin{align}& \vdash :P\in \text{Ded}. \equiv .-\text{ᗡ}ʻ\text{max}_{P}\subset \text{ᗡ}ʻ\text{seq}_{P}. \equiv .-\text{ᗡ}ʻ\text{max}_{P}\subset \text{ᗡ}ʻ\text{lt}_P\\ &[*214·1.*24·312.*207·12]\end{align}\] -/
theorem pm214_101 {P : α → α → Prop} :
    (P ∈ Ded ↔ (codom (maxP P))ᶜ ⊆ codom (seqP P)) ∧
      ((codom (maxP P))ᶜ ⊆ codom (seqP P) ↔ (codom (maxP P))ᶜ ⊆ codom (ltP P)) := by
  constructor
  · constructor
    · intro h A hA
      rcases h A with h' | h'
      · exact absurd h' hA
      · exact h'
    · intro h A
      by_cases hA : A ∈ codom (maxP P)
      · exact Or.inl hA
      · exact Or.inr (h hA)
  · constructor
    · intro h A hA
      obtain ⟨x, hx⟩ := h hA
      exact ⟨x, hx, hA⟩
    · intro h A hA
      obtain ⟨x, hx, -⟩ := h hA
      exact ⟨x, hx⟩

/-- ✱214·11. \[\begin{align}& \vdash :P\in \text{Ded}. \equiv .(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{lt}_P. \equiv .(\alpha ).\alpha \in \text{ᗡ}ʻ\text{limax}_P\\ &[*214·1.*207·14·44]\end{align}\] -/
theorem pm214_11 {P : α → α → Prop} :
    (P ∈ Ded ↔ ∀ A : Set α, A ∈ codom (maxP P) ∪ codom (ltP P)) ∧
      ((∀ A : Set α, A ∈ codom (maxP P) ∪ codom (ltP P)) ↔ ∀ A : Set α, A ∈ codom (limaxP P)) := by
  have e1 : ∀ A : Set α, A ∈ codom (limaxP P) ↔ A ∈ codom (maxP P) ∪ codom (ltP P) := by
    intro A
    constructor
    · rintro ⟨x, hx | hx⟩
      · exact Or.inl ⟨x, hx⟩
      · exact Or.inr ⟨x, hx⟩
    · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
      · exact ⟨x, Or.inl hx⟩
      · exact ⟨x, Or.inr hx⟩
  have e2 : ∀ A : Set α,
      A ∈ codom (maxP P) ∪ codom (ltP P) ↔ A ∈ codom (maxP P) ∪ codom (seqP P) := by
    intro A
    constructor
    · rintro (h | ⟨x, hx, -⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, hx⟩
    · rintro (h | ⟨x, hx⟩)
      · exact Or.inl h
      · by_cases hA : A ∈ codom (maxP P)
        · exact Or.inl hA
        · exact Or.inr ⟨x, hx, hA⟩
  refine ⟨?_, ?_⟩
  · rw [pm214_1]
    exact forall_congr' fun A => (e2 A).symm
  · exact forall_congr' fun A => (e1 A).symm

/-- ✱214·12.\[\begin{align}& \vdash \colon\ldotp P\in \text{Ded}. \equiv :\alpha \subset CʻP.\supset _{\alpha }.\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}\\ &[*214·1.*205·151.*206·131]\end{align}\] -/
theorem pm214_12 {P : α → α → Prop} :
    P ∈ Ded ↔ ∀ A, A ⊆ fld P → A ∈ codom (maxP P) ∪ codom (seqP P) := by
  constructor
  · intro h A _; exact h A
  · intro h A
    rw [b2_dunion_inter]
    exact h _ Set.inter_subset_right

/-- For transitive `P`, a class and the section it generates have the same maxima and
sequents (✱211·272). -/
private theorem b2_trans_gen {P : α → α → Prop} (ht : P ∈ transR) (A : Set α) :
    (A ∩ fld P) ∪ P ʻʻ A ∈ sect P ∧
      (A ∈ codom (maxP P) ∪ codom (seqP P) ↔
        (A ∩ fld P) ∪ P ʻʻ A ∈ codom (maxP P) ∪ codom (seqP P)) := by
  have tr := mem_transR.1 ht
  set A' := (A ∩ fld P) ∪ P ʻʻ A with hA'
  have hsub : A' ⊆ fld P := by
    rintro z (h | ⟨y, -, hzy⟩)
    · exact h.2
    · exact ⟨y, Or.inl hzy⟩
  have hsect : A' ∈ sect P := by
    refine ⟨hsub, ?_⟩
    rintro z ⟨y, hy, hzy⟩
    rcases hy with ⟨hyA, -⟩ | ⟨w, hw, hyw⟩
    · exact Or.inr ⟨y, hyA, hzy⟩
    · exact Or.inr ⟨w, hw, tr z y w ⟨hzy, hyw⟩⟩
  refine ⟨hsect, ?_⟩
  have hA'f : A' ∩ fld P = A' := Set.inter_eq_left.2 hsub
  have csucc : ∀ z, (∀ y, y ∈ A ∩ fld P → P y z) ↔ (∀ y, y ∈ A' ∩ fld P → P y z) := by
    intro z
    constructor
    · rintro h y ⟨hy | ⟨w, hw, hyw⟩, -⟩
      · exact h y hy
      · exact tr y w z ⟨hyw, h w ⟨hw, ⟨y, Or.inr hyw⟩⟩⟩
    · intro h y hy; exact h y ⟨Or.inl hy, hy.2⟩
  have hseq : ∀ x, seqP P x A ↔ seqP P x A' := by
    intro x
    rw [seqP_iff, seqP_iff]
    simp only [csucc]
  have hmax : ∀ x, maxP P x A ↔ maxP P x A' := by
    intro x
    rw [maxP_iff, maxP_iff]
    constructor
    · rintro ⟨⟨hx, hf⟩, h⟩
      refine ⟨⟨Or.inl ⟨hx, hf⟩, hf⟩, ?_⟩
      rintro y (hy | ⟨w, hw, hyw⟩) hxy
      · exact h y hy.1 hxy
      · exact h w hw (tr x y w ⟨hxy, hyw⟩)
    · rintro ⟨⟨hx, hf⟩, h⟩
      rcases hx with hx | ⟨w, hw, hxw⟩
      · exact ⟨⟨hx.1, hf⟩, fun y hy hxy => h y (Or.inl ⟨hy, ⟨x, Or.inr hxy⟩⟩) hxy⟩
      · exact absurd hxw (h w (Or.inl ⟨hw, ⟨x, Or.inr hxw⟩⟩))
  simp only [b2_mem_union_codom, hseq, hmax]

/-- ✱214·13. \[\begin{align}& \vdash \colon\ldotp P\in \text{trans}.\supset :P\in \text{Ded}. \equiv .\text{sect}ʻP\subset \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}\\ &[*211·272.*214·1]\end{align}\] -/
theorem pm214_13 {P : α → α → Prop} (ht : P ∈ transR) :
    P ∈ Ded ↔ sect P ⊆ codom (maxP P) ∪ codom (seqP P) := by
  constructor
  · intro h A _; exact h A
  · intro h A
    exact (b2_trans_gen ht A).2.2 (h (b2_trans_gen ht A).1)

private theorem b2_noMax_fixed {P : α → α → Prop} {A : Set α} (hA : A = P ʻʻ A) :
    ¬∃ x, maxP P x A := by
  rintro ⟨x, hx⟩
  rw [maxP_iff] at hx
  have : x ∈ P ʻʻ A := hA ▸ hx.1.1
  obtain ⟨y, hy, hxy⟩ := this
  exact hx.2 y hy hxy

private theorem b2_fixed_of_noMax {P : α → α → Prop} {A : Set α} (hA : A ∈ sect P)
    (hn : ¬∃ x, maxP P x A) : A = P ʻʻ A := by
  refine Set.Subset.antisymm (fun x hx => ?_) hA.2
  by_contra hx'
  refine hn ⟨x, maxP_iff.2 ⟨⟨hx, hA.1 hx⟩, fun y hy hxy => hx' ⟨y, hy, hxy⟩⟩⟩

private theorem b2_img_sect {P : α → α → Prop} (ht : P ∈ transR) (B : Set α) : P ʻʻ B ∈ sect P := by
  refine ⟨fun z ⟨y, _, hzy⟩ => ⟨y, Or.inl hzy⟩, ?_⟩
  rintro z ⟨y, ⟨w, hw, hyw⟩, hzy⟩
  exact ⟨w, hw, mem_transR.1 ht z y w ⟨hzy, hyw⟩⟩

/-- ✱214·131. \(\vdash \colon\ldotp P\in \text{trans}.\supset :P\in \text{Ded}. \equiv .\text{D}(ʻP_{\in }\dot{\cap} I)\subset \text{ᗡ}ʻ\text{seq}_{P} \quad[*211·47.*214·1]\)

**Status.** proved (reading): the e-text prints `D(ʻP_∈ ∩̇ I)` for `D'(P_∈ ∩̇ I)`. -/
theorem pm214_131 {P : α → α → Prop} (ht : P ∈ transR) :
    P ∈ Ded ↔ dom (imgRel P ⩀ I) ⊆ codom (seqP P) := by
  constructor
  · intro h A hA
    rw [mem_dom_imgRel_rcap_I] at hA
    rcases h A with h' | h'
    · exact absurd h' (b2_noMax_fixed hA)
    · exact h'
  · intro h
    rw [pm214_13 ht]
    intro A hA
    by_cases hm : ∃ x, maxP P x A
    · exact Or.inl hm
    · exact Or.inr (h (mem_dom_imgRel_rcap_I.2 (b2_fixed_of_noMax hA hm)))

/-- ✱214·132. \[\begin{align}& \vdash \colon\ldotp P\in \text{trans}.\supset :P\in \text{Ded}. \equiv .\text{D}ʻP_{\in }\subset \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}\\ &[*214·131.*211·42]\end{align}\] -/
theorem pm214_132 {P : α → α → Prop} (ht : P ∈ transR) :
    P ∈ Ded ↔ dom (imgRel P) ⊆ codom (maxP P) ∪ codom (seqP P) := by
  constructor
  · intro h A _; exact h A
  · intro h
    rw [pm214_131 ht]
    intro A hA
    rw [mem_dom_imgRel_rcap_I] at hA
    rcases h ⟨A, hA⟩ with h' | h'
    · exact absurd h' (b2_noMax_fixed hA)
    · exact h'

/-- For a connected irreflexive `P` and a section `α`, `seq_P'α` is `min_P'(C'P − α)`
(✱211·721). -/
private theorem b2_seq_sect {P : α → α → Prop} (hirr : ∀ x, ¬P x x) (hc : P ∈ connex) {A : Set α}
    (hA : A ∈ sect P) {x : α} : seqP P x A ↔ minP P x (fld P \ A) := by
  have hAf : A ∩ fld P = A := Set.inter_eq_left.2 hA.1
  have sup : ∀ z, z ∈ fld P \ A → ∀ y, y ∈ A ∩ fld P → P y z := by
    rintro z ⟨hz, hzA⟩ y ⟨hy, hyf⟩
    rcases mem_connex.1 hc y z ⟨hyf, hz⟩ with (h | rfl) | h
    · exact h
    · exact absurd hy hzA
    · exact absurd (b2_sect_P hA h hy) hzA
  rw [seqP_iff, minP_iff]
  constructor
  · rintro ⟨⟨h1, hf⟩, h2⟩
    have hxA : x ∉ A := fun hxA => hirr x (h1 x ⟨hxA, hf⟩)
    exact ⟨⟨⟨hf, hxA⟩, hf⟩, fun y hy hyx => h2 y (sup y hy) hyx⟩
  · rintro ⟨⟨⟨hf, hxA⟩, -⟩, h2⟩
    refine ⟨⟨sup x ⟨hf, hxA⟩, hf⟩, fun z hz hzx => ?_⟩
    have hzf : z ∈ fld P := ⟨x, Or.inl hzx⟩
    by_cases hzA : z ∈ A
    · exact hirr z (hz z ⟨hzA, hzf⟩)
    · exact h2 z ⟨hzf, hzA⟩ hzx

private theorem b2_irr_of_ser {P : α → α → Prop} (h : P ∈ Ser) : ∀ x, ¬P x x := (mem_Ser.1 h).1.1

private theorem b2_trans_of_ser {P : α → α → Prop} (h : P ∈ Ser) : P ∈ transR := h.1.2

private theorem b2_conn_of_ser {P : α → α → Prop} (h : P ∈ Ser) : P ∈ connex := h.2

private theorem b2_cnv_cnv (P : α → α → Prop) : P˘˘ = P := rfl

private theorem b2_sect_cnv_iff {P : α → α → Prop} {B : Set α} (hB : B ⊆ fld P) :
    B ∈ sect P˘ ↔ fld P \ B ∈ sect P := by
  constructor
  · intro h
    have := b2_upper_sect h
    rw [fld_cnv] at this; exact this
  · intro h
    have := b2_upper_sect h
    rwa [Set.sdiff_sdiff_cancel_left hB] at this

/-- Dedekindian series via sections: every section has a maximum or its complement a
minimum. -/
private theorem b2_Ded_ser {P : α → α → Prop} (h : P ∈ Ser) :
    P ∈ Ded ↔ ∀ A, A ∈ sect P → (∃ x, maxP P x A) ∨ ∃ x, minP P x (fld P \ A) := by
  rw [pm214_13 h.1.2]
  refine forall₂_congr fun A hA => ?_
  rw [b2_mem_union_codom]
  simp only [b2_seq_sect (b2_irr_of_ser h) h.2 hA]

/-- ✱214·14. \(\vdash \colon\ldotp P\in \text{Ser}.\supset :P\in \text{Ded}. \equiv .\breve{P} \in \text{Ded} \quad[*206·57.*214·1]\) -/
theorem pm214_14 {P : α → α → Prop} (h : P ∈ Ser) : P ∈ Ded ↔ P˘ ∈ Ded := by
  have h' := b2_cnv_ser h
  rw [b2_Ded_ser h, b2_Ded_ser h', fld_cnv]
  constructor
  · intro H B hB
    have hBf : B ⊆ fld P := by have := hB.1; rwa [fld_cnv] at this
    rcases H _ ((b2_sect_cnv_iff hBf).1 hB) with h1 | h1
    · right; exact h1
    · left
      rw [Set.sdiff_sdiff_cancel_left hBf] at h1
      exact h1
  · intro H A hA
    have hc : fld P \ A ∈ sect P˘ := by
      rw [b2_sect_cnv_iff Set.sdiff_subset, Set.sdiff_sdiff_cancel_left hA.1]; exact hA
    rcases H _ hc with h1 | h1
    · right; exact h1
    · left
      rw [Set.sdiff_sdiff_cancel_left hA.1] at h1
      exact h1

private theorem b2_pred_cls {P : α → α → Prop} (h : P ∈ Ser) {A : Set α} (hA : A ∈ sect P) :
    prodCls (Rfwd P ʻʻ ((fld P \ A) ∩ fld P)) ∩ fld P = A := by
  ext x
  rw [Set.mem_inter_iff, mem_prodCls_Rfwd]
  constructor
  · rintro ⟨hx, hf⟩
    by_contra hxA
    exact b2_irr_of_ser h x (hx x ⟨⟨hf, hxA⟩, hf⟩)
  · intro hx
    refine ⟨fun y hy' => ?_, hA.1 hx⟩
    obtain ⟨⟨hy, hyA⟩, -⟩ := hy'
    rcases mem_connex.1 h.2 x y ⟨hA.1 hx, hy⟩ with (h1 | rfl) | h1
    · exact h1
    · exact absurd hx hyA
    · exact absurd (b2_sect_P hA h1 hx) hyA

/-- ✱214·141. \[\begin{align}& \vdash \colon\ldotp P\in \text{Ser}.\supset :P\in \text{Ded}. \equiv .(\alpha ).pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)\in \text{ᗡ}ʻ\text{max}_{P}\text{ᗡ}ʻ\text{seq}_{P}\\ &[*206·56.*214·1]\end{align}\]

**Status.** proved (reading): the e-text omits the `∪` of `ᗡ'max_P ∪ ᗡ'seq_P` (as in ✱214·1). -/
theorem pm214_141 {P : α → α → Prop} (h : P ∈ Ser) :
    P ∈ Ded ↔ ∀ A : Set α,
      prodCls (Rfwd P ʻʻ (A ∩ fld P)) ∈ codom (maxP P) ∪ codom (seqP P) := by
  constructor
  · intro H A; exact H _
  · intro H
    rw [pm214_13 h.1.2]
    intro A hA
    have := H (fld P \ A)
    rw [b2_dunion_inter, b2_pred_cls h hA] at this
    exact this

private theorem b2_seq_of_maxSeg {P : α → α → Prop} (h : P ∈ Ser) {B : Set α} {m : α}
    (hm : maxP P m (P ʻʻ B)) : ∃ x, seqP P x (P ʻʻ B) := by
  have tr := mem_transR.1 h.1.2
  have hirr := b2_irr_of_ser h
  rw [maxP_iff] at hm
  have : ∃ b, (b ∈ B ∧ b ∈ fld P) ∧ b ∉ P ʻʻ B := by
    obtain ⟨b', hb', hmb'⟩ := hm.1.1
    refine ⟨b', ⟨hb', ⟨m, Or.inr hmb'⟩⟩, fun hb'A => hm.2 b' hb'A hmb'⟩
  obtain ⟨b, ⟨hbB, hbf⟩, hbA⟩ := this
  refine ⟨b, seqP_iff.2 ⟨⟨fun y ⟨hy, hyf⟩ => ?_, hbf⟩, fun z hz hzb => ?_⟩⟩
  · obtain ⟨b'', hb'', hyb''⟩ := hy
    rcases mem_connex.1 h.2 y b ⟨hyf, hbf⟩ with (h1 | rfl) | h1
    · exact h1
    · exact absurd ⟨b'', hb'', hyb''⟩ hbA
    · exact absurd ⟨b'', hb'', tr b y b'' ⟨h1, hyb''⟩⟩ hbA
  · have hzA : z ∈ P ʻʻ B := ⟨b, hbB, hzb⟩
    exact hirr z (hz z ⟨hzA, ⟨b, Or.inl hzb⟩⟩)

/-- ✱214·15. \[\begin{align}& \vdash \colon\ldotp P\in \text{Ser}.\supset :P\in \text{Ded}. \equiv .\text{D}ʻP_{\in }\subset \text{ᗡ}ʻ\text{seq}_{P}\\ &[*206·36.*214·1.*211·11]\end{align}\] -/
theorem pm214_15 {P : α → α → Prop} (h : P ∈ Ser) :
    P ∈ Ded ↔ dom (imgRel P) ⊆ codom (seqP P) := by
  constructor
  · rintro H A ⟨B, rfl⟩
    rcases H (P ʻʻ B) with ⟨m, hm⟩ | h'
    · exact b2_seq_of_maxSeg h hm
    · exact h'
  · intro H
    rw [pm214_131 h.1.2]
    intro A hA
    exact H ⟨A, mem_dom_imgRel_rcap_I.1 hA⟩

/-- For a series, a section with sequent `x` is `P⃗'x`. -/
private theorem b2_sect_eq_refs {P : α → α → Prop} (h : P ∈ Ser) {A : Set α} (hA : A ∈ sect P) {x : α}
    (hx : seqP P x A) : A = refs P x := by
  have hAf : A ∩ fld P = A := Set.inter_eq_left.2 hA.1
  rw [b2_seq_sect (b2_irr_of_ser h) h.2 hA, minP_iff] at hx
  ext y
  constructor
  · intro hy
    rcases mem_connex.1 h.2 y x ⟨hA.1 hy, hx.1.2⟩ with (h1 | rfl) | h1
    · exact h1
    · exact absurd hy hx.1.1.2
    · exact absurd (b2_sect_P hA h1 hy) hx.1.1.2
  · intro hyx
    by_contra hyA
    exact hx.2 y ⟨⟨x, Or.inl hyx⟩, hyA⟩ hyx

private theorem b2_seq_refs {P : α → α → Prop} (h : P ∈ Ser) {x : α} (hx : x ∈ fld P) :
    seqP P x (refs P x) := by
  rw [seqP_iff]
  refine ⟨⟨fun y hy => hy.1, hx⟩, fun z hz hzx => ?_⟩
  exact b2_irr_of_ser h z (hz z ⟨hzx, ⟨x, Or.inl hzx⟩⟩)

private theorem b2_refs_mem_dom_img (P : α → α → Prop) (x : α) : refs P x ∈ dom (imgRel P) :=
  ⟨ι x, Set.ext fun y => ⟨fun hy => ⟨x, rfl, hy⟩, fun ⟨z, hz, hy⟩ => (b2_mem_iota.1 hz) ▸ hy⟩⟩

/-- ✱214·151. \(\vdash P\in \text{Ser}.\supset :P\in \text{Ded}. \equiv .\text{D}ʻP\in = \overrightarrow{P}ʻʻCʻP \quad[*211·38.*214·1]\)

**Status.** proved (reading): the e-text prints `D'P∈` for `D'P_∈`. -/
theorem pm214_151 {P : α → α → Prop} (h : P ∈ Ser) :
    P ∈ Ded ↔ dom (imgRel P) = Rfwd P ʻʻ fld P := by
  rw [pm214_15 h]
  constructor
  · intro H
    ext A
    constructor
    · intro hA
      obtain ⟨x, hx⟩ := H hA
      obtain ⟨B, rfl⟩ := hA
      refine ⟨x, (seqP_iff.1 hx).1.2, ?_⟩
      exact b2_sect_eq_refs h (b2_img_sect h.1.2 B) hx
    · rintro ⟨x, -, rfl⟩
      exact b2_refs_mem_dom_img P x
  · intro H A hA
    rw [H] at hA
    obtain ⟨x, hx, rfl⟩ := hA
    exact ⟨x, b2_seq_refs h hx⟩

private theorem b2_Ded_irr {P : α → α → Prop} (h : P ∈ Ded) : ∀ x, ¬P x x := by
  intro x hxx
  rcases h (ι x) with ⟨m, hm⟩ | ⟨s, hs⟩
  · rw [maxP_iff] at hm
    have : m = x := hm.1.1
    subst this
    exact hm.2 m rfl hxx
  · rw [seqP_iff] at hs
    have hxs : P x s := hs.1.1 x ⟨rfl, ⟨x, Or.inl hxx⟩⟩
    exact hs.2 x (fun y hy => (b2_mem_iota.1 hy.1) ▸ hxx) hxs

private theorem b2_ser_of_Ded {P : α → α → Prop} (h : P ∈ transR ∩ connex ∩ Ded) : P ∈ Ser :=
  ⟨⟨mem_rl_J.2 (b2_Ded_irr h.2), h.1.1⟩, h.1.2⟩

/-- ✱214·2. \(\vdash :P\in \text{trans}\cap \text{connex} \cap \text{Ded}.\supset .\text{D}ʻP_{\in }\subset \text{ᗡ}ʻ\text{seq}_{P} \quad[*211·371]\) -/
theorem pm214_2 {P : α → α → Prop} (h : P ∈ transR ∩ connex ∩ Ded) :
    dom (imgRel P) ⊆ codom (seqP P) :=
  (pm214_15 (b2_ser_of_Ded h)).1 h.2

/-- ✱214·21. \(\vdash :P\in \text{trans}\cap \text{connex} \cap \text{Ded}.\supset .\text{D}ʻP_{\in }=\overrightarrow{P}ʻʻCʻP \quad [*211·372]\) -/
theorem pm214_21 {P : α → α → Prop} (h : P ∈ transR ∩ connex ∩ Ded) :
    dom (imgRel P) = Rfwd P ʻʻ fld P :=
  (pm214_151 (b2_ser_of_Ded h)).1 h.2

/-- ✱214·22. \[\begin{align}& \vdash :P\in \text{trans}\cap \text{connex} \cap \text{Ded}.\supset .\text{D}ʻ(P_{\in }\dot{\cap} I)=\overrightarrow{P}ʻʻ\{CʻP-\text{ᗡ}ʻ(P\dot{-} P^{2})\}\\ &[*211·46]\end{align}\] -/
theorem pm214_22 {P : α → α → Prop} (h : P ∈ transR ∩ connex ∩ Ded) :
    dom (imgRel P ⩀ I) = Rfwd P ʻʻ (fld P \ codom (P ∸ rsq P)) := by
  have hs := b2_ser_of_Ded h
  have tr := mem_transR.1 h.1.1
  ext A
  rw [mem_dom_imgRel_rcap_I]
  constructor
  · intro hA
    have hAd : A ∈ dom (imgRel P) := ⟨A, hA⟩
    obtain ⟨x, hx⟩ := pm214_2 h hAd
    have e := b2_sect_eq_refs hs (b2_img_sect h.1.1 A |> fun hh => hA ▸ hh) hx
    refine ⟨x, ⟨(seqP_iff.1 hx).1.2, ?_⟩, e⟩
    rintro ⟨w, hwx, hn⟩
    have hwA : w ∈ A := e ▸ hwx
    rw [hA] at hwA
    obtain ⟨v, hvA, hwv⟩ := hwA
    exact hn ⟨v, hwv, (e ▸ hvA : v ∈ refs P x)⟩
  · rintro ⟨x, ⟨hx, hxn⟩, rfl⟩
    refine Set.Subset.antisymm (fun w hw => ?_) (fun w ⟨v, hv, hwv⟩ => tr w v x ⟨hwv, hv⟩)
    by_contra hw'
    refine hxn ⟨w, hw, fun ⟨v, hwv, hvx⟩ => hw' ⟨v, hvx, hwv⟩⟩

private theorem b2_maxP_unique {P : α → α → Prop} (hc : P ∈ connex) {A : Set α} {x y : α}
    (hx : maxP P x A) (hy : maxP P y A) : x = y := by
  rw [maxP_iff] at hx hy
  rcases mem_connex.1 hc x y ⟨hx.1.2, hy.1.2⟩ with (h | h) | h
  · exact absurd h (hx.2 y hy.1.1)
  · exact h
  · exact absurd h (hy.2 x hx.1.1)

private theorem b2_minP_unique {P : α → α → Prop} (hc : P ∈ connex) {A : Set α} {x y : α}
    (hx : minP P x A) (hy : minP P y A) : x = y := by
  rw [minP_iff] at hx hy
  rcases mem_connex.1 hc x y ⟨hx.1.2, hy.1.2⟩ with (h | h) | h
  · exact absurd h (hy.2 x hx.1.1)
  · exact h
  · exact absurd h (hx.2 y hy.1.1)

private theorem b2_seqP_unique {P : α → α → Prop} (hc : P ∈ connex) {A : Set α} {x y : α}
    (hx : seqP P x A) (hy : seqP P y A) : x = y := b2_minP_unique hc hx hy

private theorem b2_refs_single {β : Type v} {R : α → β → Prop} {y : β} {b : α} (hb : R b y)
    (hu : ∀ c, R c y → c = b) : refs R y = {b} :=
  Set.ext fun c => ⟨fun hc => hu c hc, fun hc => hc ▸ hb⟩

private theorem b2_max_union_seq {P : α → α → Prop} (h : P ∈ Ser) {A : Set α} {s : α}
    (hs : seqP P s A) : maxP P s (A ∪ ι s) := by
  rw [seqP_iff] at hs
  rw [maxP_iff]
  refine ⟨⟨Or.inr rfl, hs.1.2⟩, fun y hy hsy => ?_⟩
  rcases hy with hy | hy
  · exact b2_irr_of_ser h s (mem_transR.1 h.1.2 s y s ⟨hsy, hs.1.1 y ⟨hy, ⟨s, Or.inr hsy⟩⟩⟩)
  · rw [b2_mem_iota] at hy; subst hy; exact b2_irr_of_ser h y hsy

/-- ✱214·23. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} \cap \text{Ded}.{\sim}\text{E}!\text{max}_{P}ʻ\alpha .\supset .\\ &\text{seq}_{P}ʻ\alpha =\text{max}_{P}ʻ(\alpha \cup \iota ʻ\text{seq}_{P}ʻ\alpha ).\text{E}!\text{max}_{P}ʻ(\alpha \cup \iota ʻ\text{seq}_{P}ʻ\alpha )\end{align}\] -/
theorem pm214_23 {P : α → α → Prop} {A : Set α}
    (h : P ∈ transR ∩ connex ∩ Ded ∧ ¬EDesc (maxP P) A) :
    Desc (seqP P) A (fun s => Desc (seqP P) A (fun s' => Desc (maxP P) (A ∪ ι s')
        (fun m => s = m))) ∧
      Desc (seqP P) A (fun s' => EDesc (maxP P) (A ∪ ι s')) := by
  obtain ⟨h, hn⟩ := h
  have hs := b2_ser_of_Ded h
  have hm : ¬∃ x, maxP P x A := by
    rintro ⟨x, hx⟩
    exact hn ⟨x, fun y => ⟨fun hy => b2_maxP_unique h.1.2 hy hx, fun e => e ▸ hx⟩⟩
  obtain ⟨s, hsA⟩ : ∃ s, seqP P s A := by
    rcases h.2 A with h' | h'
    · exact absurd h' hm
    · exact h'
  have e1 : refs (seqP P) A = {s} := b2_refs_single hsA fun c hc => b2_seqP_unique h.1.2 hc hsA
  have hmax := b2_max_union_seq hs hsA
  have e2 : refs (maxP P) (A ∪ ι s) = {s} :=
    b2_refs_single hmax fun c hc => b2_maxP_unique h.1.2 hc hmax
  rw [b2_desc_of_refs e1, b2_desc_of_refs e1, b2_desc_of_refs e1, b2_desc_of_refs e2,
    b2_EDesc_iff]
  exact ⟨rfl, s, e2⟩

/-- ✱214·24. \[\begin{align}& \vdash :P\in \text{connex} \cap \text{Ded}.\alpha \in \text{sect}ʻP.\supset .\overrightarrow{\text{seq}} _{P}ʻ\alpha =\overrightarrow{\text{min}}_{P}ʻ(CʻP-\alpha )\\ &[*211·721]\end{align}\] -/
theorem pm214_24 {P : α → α → Prop} {A : Set α} (h : P ∈ connex ∩ Ded ∧ A ∈ sect P) :
    refs (seqP P) A = refs (minP P) (fld P \ A) := by
  ext x
  exact b2_seq_sect (b2_Ded_irr h.1.2) h.1.1 h.2

private theorem b2_cnv_connex {P : α → α → Prop} (h : P ∈ connex) : P˘ ∈ connex := by
  rw [mem_connex, fld_cnv]
  intro x y hxy
  rcases mem_connex.1 h x y hxy with (h1 | h1) | h1
  · exact Or.inr h1
  · exact Or.inl (Or.inr h1)
  · exact Or.inl (Or.inl h1)

/-- ✱214·241. \[\begin{align}& \vdash :P\in \text{connex} .\breve{P} \in \text{Ded}.\alpha \in \text{sect}ʻP.\supset .\overrightarrow{\text{max}}_{P}ʻ\alpha =\overrightarrow{\text{prec}} _{P}ʻ(CʻP-\alpha )\\ &\left[*214·24 \frac{\breve{P}}{P}. *211·7\right]\end{align}\] -/
theorem pm214_241 {P : α → α → Prop} {A : Set α}
    (h : (P ∈ connex ∧ P˘ ∈ Ded) ∧ A ∈ sect P) :
    refs (maxP P) A = refs (precP P) (fld P \ A) := by
  obtain ⟨⟨hc, hD⟩, hA⟩ := h
  have hc' := b2_cnv_connex hc
  have hirr : ∀ x, ¬P˘ x x := b2_Ded_irr hD
  have hs : fld P \ A ∈ sect P˘ := by
    rw [b2_sect_cnv_iff Set.sdiff_subset, Set.sdiff_sdiff_cancel_left hA.1]; exact hA
  ext x
  show maxP P x A ↔ precP P x (fld P \ A)
  rw [precP_eq_seqP_cnv, b2_seq_sect hirr hc' hs, fld_cnv, Set.sdiff_sdiff_cancel_left hA.1]
  rfl

/-- The series of a chain closed under sums is a Dedekindian series (✱214·3). -/
private theorem b2_chain_ser {κ : Set (Set α)} (hch : ∀ A B, A ∈ κ ∧ B ∈ κ → A ⊆ B ∨ B ⊆ A) :
    (fun A B => ((A ∈ κ ∧ B ∈ κ) ∧ A ⊆ B) ∧ A ≠ B : Set α → Set α → Prop) ∈ Ser := by
  rw [mem_Ser]
  refine ⟨⟨fun A hA => hA.2 rfl, fun A B C ⟨h1, h2⟩ => ?_⟩, fun A B ⟨hA, hB⟩ => ?_⟩
  · refine ⟨⟨⟨h1.1.1.1, h2.1.1.2⟩, h1.1.2.trans h2.1.2⟩, fun e => ?_⟩
    subst e
    exact h1.2 (Set.Subset.antisymm h1.1.2 h2.1.2)
  · have hκ : ∀ X, X ∈ fld (fun A B => ((A ∈ κ ∧ B ∈ κ) ∧ A ⊆ B) ∧ A ≠ B :
        Set α → Set α → Prop) → X ∈ κ := by
      rintro X ⟨Y, h | h⟩
      · exact h.1.1.1
      · exact h.1.1.2
    by_cases e : A = B
    · exact Or.inl (Or.inr e)
    rcases hch A B ⟨hκ A hA, hκ B hB⟩ with hs | hs
    · exact Or.inl (Or.inl ⟨⟨⟨hκ A hA, hκ B hB⟩, hs⟩, e⟩)
    · exact Or.inr ⟨⟨⟨hκ B hB, hκ A hA⟩, hs⟩, Ne.symm e⟩

private theorem b2_chain_fld {κ : Set (Set α)} (hch : ∀ A B, A ∈ κ ∧ B ∈ κ → A ⊆ B ∨ B ⊆ A)
    (h1 : κ ∉ (one : Set (Set (Set α)))) {u : Set α} (hu : u ∈ κ) :
    u ∈ fld (fun A B => ((A ∈ κ ∧ B ∈ κ) ∧ A ⊆ B) ∧ A ≠ B : Set α → Set α → Prop) := by
  have : ∃ W, W ∈ κ ∧ W ≠ u := by
    by_contra hn; push Not at hn
    exact h1 ⟨u, Set.ext fun W => ⟨fun hW => hn W hW, fun hW => (b2_mem_iota.1 hW) ▸ hu⟩⟩
  obtain ⟨W, hW, hWu⟩ := this
  rcases hch u W ⟨hu, hW⟩ with hs | hs
  · exact ⟨W, Or.inl ⟨⟨⟨hu, hW⟩, hs⟩, Ne.symm hWu⟩⟩
  · exact ⟨W, Or.inr ⟨⟨⟨hW, hu⟩, hs⟩, hWu⟩⟩

/-- ✱214·3. \[\begin{align}\vdash \colon\colon\alpha ,&\beta \in \kappa .\supset _{\alpha ,\beta }:\alpha \subset \beta .\lor.\beta \subset \alpha \colon\ldotp\\ &\kappa {\sim}\in 1.Q=\hat{\alpha} \hat{\beta} (\alpha ,\beta \in \kappa .\alpha \subset \beta .\alpha \neq \beta )\colon\ldotp \supset \colon\ldotp\\ &\lambda \subset \kappa .\supset _{\lambda }.sʻ\lambda \in \kappa :\supset .Q\in \text{Ser}\cap \text{Ded}\\ &[*210·12·253]\end{align}\] -/
theorem pm214_3 {κ : Set (Set α)} {Q : Set α → Set α → Prop}
    (h : (∀ A B, A ∈ κ ∧ B ∈ κ → A ⊆ B ∨ B ⊆ A) ∧
      (κ ∉ (one : Set (Set (Set α))) ∧ Q = fun A B => ((A ∈ κ ∧ B ∈ κ) ∧ A ⊆ B) ∧ A ≠ B)) :
    (∀ L, L ⊆ κ → sumCls L ∈ κ) → Q ∈ Ser ∩ Ded := by
  obtain ⟨hch, h1, rfl⟩ := h
  intro hsum
  refine ⟨b2_chain_ser hch, fun M => ?_⟩
  rw [b2_mem_union_codom]
  by_cases hm : ∃ x, maxP (fun A B => ((A ∈ κ ∧ B ∈ κ) ∧ A ⊆ B) ∧ A ≠ B) x M
  · exact Or.inl hm
  right
  set Qr : Set α → Set α → Prop := fun A B => ((A ∈ κ ∧ B ∈ κ) ∧ A ⊆ B) ∧ A ≠ B with hQr
  have hNκ : M ∩ fld Qr ⊆ κ := by
    rintro Y ⟨-, Z, hZ | hZ⟩
    · exact hZ.1.1.1
    · exact hZ.1.1.2
  set u := sumCls (M ∩ fld Qr)
  have huκ : u ∈ κ := hsum _ hNκ
  refine ⟨u, seqP_iff.2 ⟨⟨fun Y hY => ?_, b2_chain_fld hch h1 huκ⟩, fun Z hZ hZu => ?_⟩⟩
  · have hYu : Y ⊆ u := fun z hz => ⟨Y, hY, hz⟩
    refine ⟨⟨⟨hNκ hY, huκ⟩, hYu⟩, fun e => hm ⟨Y, maxP_iff.2 ⟨⟨hY.1, hY.2⟩, ?_⟩⟩⟩
    intro Z hZ hYZ
    have hZf : Z ∈ fld Qr := ⟨Y, Or.inr hYZ⟩
    have : Z ⊆ u := fun z hz => ⟨Z, ⟨hZ, hZf⟩, hz⟩
    rw [← e] at this
    exact hYZ.2 (Set.Subset.antisymm hYZ.1.2 this)
  · have huZ : u ⊆ Z := by
      rintro z ⟨Y, hY, hz⟩
      exact (hZ Y hY).1.2 hz
    exact hZu.2 (Set.Subset.antisymm hZu.1.2 huZ)

/-- ✱214·31. \[\begin{align}& \vdash \colon\ldotp \text{Hp}*214·3:\lambda \subset \kappa .\supset _{\lambda }.pʻ\lambda \cap sʻ\kappa \in \kappa :\supset .Q\in \text{Ser}\cap \text{Ded}\\ &[*210·12·254]\end{align}\] -/
theorem pm214_31 {κ : Set (Set α)} {Q : Set α → Set α → Prop}
    (h : ((∀ A B, A ∈ κ ∧ B ∈ κ → A ⊆ B ∨ B ⊆ A) ∧
      (κ ∉ (one : Set (Set (Set α))) ∧ Q = fun A B => ((A ∈ κ ∧ B ∈ κ) ∧ A ⊆ B) ∧ A ≠ B)) ∧
      ∀ L, L ⊆ κ → prodCls L ∩ sumCls κ ∈ κ) :
    Q ∈ Ser ∩ Ded := by
  obtain ⟨⟨hch, h1, rfl⟩, hprod⟩ := h
  refine ⟨b2_chain_ser hch, fun M => ?_⟩
  rw [b2_mem_union_codom]
  by_cases hm : ∃ x, maxP (fun A B => ((A ∈ κ ∧ B ∈ κ) ∧ A ⊆ B) ∧ A ≠ B) x M
  · exact Or.inl hm
  right
  set Qr : Set α → Set α → Prop := fun A B => ((A ∈ κ ∧ B ∈ κ) ∧ A ⊆ B) ∧ A ≠ B with hQr
  have hNκ : M ∩ fld Qr ⊆ κ := by
    rintro Y ⟨-, Z, hZ | hZ⟩
    · exact hZ.1.1.1
    · exact hZ.1.1.2
  set U : Set (Set α) := {Z | (∀ Y, Y ∈ M ∩ fld Qr → Qr Y Z) ∧ Z ∈ κ}
  set u := prodCls U ∩ sumCls κ
  have huκ : u ∈ κ := hprod U fun Z hZ => hZ.2
  have hYu : ∀ Y, Y ∈ M ∩ fld Qr → Y ⊆ u := by
    intro Y hY z hz
    exact ⟨fun Z hZ => (hZ.1 Y hY).1.2 hz, Y, hNκ hY, hz⟩
  refine ⟨u, seqP_iff.2 ⟨⟨fun Y hY => ?_, b2_chain_fld hch h1 huκ⟩, fun Z hZ hZu => ?_⟩⟩
  · refine ⟨⟨⟨hNκ hY, huκ⟩, hYu Y hY⟩, fun e => hm ⟨Y, maxP_iff.2 ⟨⟨hY.1, hY.2⟩, ?_⟩⟩⟩
    intro Z hZ hYZ
    have hZf : Z ∈ fld Qr := ⟨Y, Or.inr hYZ⟩
    have : Z ⊆ u := hYu Z ⟨hZ, hZf⟩
    rw [← e] at this
    exact hYZ.2 (Set.Subset.antisymm hYZ.1.2 this)
  · have huZ : u ⊆ Z := fun z hz => hz.1 Z ⟨hZ, hZu.1.1.1⟩
    exact hZu.2 (Set.Subset.antisymm hZu.1.2 huZ)

private theorem b2_Plc_nested {P : α → α → Prop} {A B : Set α} (hA : A ⊆ fld P) (hB : B ⊆ fld P)
    (hn : A ⊆ B ∨ B ⊆ A) : Plc P A B ↔ A ⊆ B ∧ A ≠ B := by
  show ((B ∈ cl (fld P˘) ∧ A ∈ cl (fld P˘)) ∧ ((B \ A) \ P˘˘ ʻʻ (A \ B)).Nonempty) ↔ _
  rw [fld_cnv]
  constructor
  · rintro ⟨-, z, ⟨hzB, hzA⟩, -⟩
    rcases hn with hs | hs
    · exact ⟨hs, fun e => hzA (e ▸ hzB)⟩
    · exact absurd (hs hzB) hzA
  · rintro ⟨hs, hne⟩
    obtain ⟨z, hzB, hzA⟩ := b2_diff_of_ne hs hne
    refine ⟨⟨hB, hA⟩, z, ⟨hzB, hzA⟩, ?_⟩
    rintro ⟨y, ⟨hyA, hyB⟩, -⟩
    exact hyB (hs hyA)

private theorem b2_conn_po {P : α → α → Prop} (hc : P ∈ connex) : po P ∈ connex := by
  rw [mem_connex, b2_fld_po]
  intro x y hxy
  rcases mem_connex.1 hc x y hxy with (h | h) | h
  · exact Or.inl (Or.inl (b2_po_of h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr (b2_po_of h)

private theorem b2_sect_sum {P : α → α → Prop} {L : Set (Set α)} (hL : L ⊆ sect P) :
    sumCls L ∈ sect P := by
  refine ⟨fun z ⟨A, hA, hz⟩ => (hL hA).1 hz, ?_⟩
  rintro z ⟨y, ⟨A, hA, hy⟩, hzy⟩
  exact ⟨A, hA, b2_sect_P (hL hA) hzy hy⟩

private theorem b2_two_ne {κ : Set (Set α)} {A B : Set α} (hA : A ∈ κ) (hB : B ∈ κ) (hne : A ≠ B) :
    κ ∉ (one : Set (Set (Set α))) := by
  rintro ⟨X, rfl⟩
  exact hne ((b2_mem_iota.1 hA).trans (b2_mem_iota.1 hB).symm)

/-- ✱214·32. \(\vdash :P\in \text{connex} .\dot{\exists} !P.\supset .\varsigma ʻP_{*}\in \text{Ser}\cap \text{Ded} \quad[*212·3·35]\) -/
theorem pm214_32 {P : α → α → Prop} (h : P ∈ connex ∧ rEx P) :
    segSer (anc P) ∈ Ser ∩ Ded := by
  obtain ⟨hc, a, b, hab⟩ := h
  have hcp := b2_conn_po hc
  refine pm214_3 (κ := sect P) ⟨fun A B ⟨hA, hB⟩ => b2_nested hcp hA hB,
    b2_two_ne (b2_empty_mem_sect P) (b2_fld_mem_sect P) (fun e => ?_), ?_⟩
    (fun L hL => b2_sect_sum hL)
  · have : a ∈ fld P := ⟨b, Or.inl hab⟩
    rw [← e] at this; exact this
  · funext A B; apply propext
    rw [b2_segSer_anc]
    constructor
    · rintro ⟨⟨hA, hB⟩, hd⟩
      exact ⟨⟨⟨hA, hB⟩, b2_ssub_of_diff hcp hA hB hd⟩, fun e => by
        subst e; obtain ⟨z, hz, hz'⟩ := hd; exact hz' hz⟩
    · rintro ⟨⟨⟨hA, hB⟩, hs⟩, hne⟩
      exact ⟨⟨hA, hB⟩, b2_diff_of_ne hs hne⟩

/-- ✱214·33. \(\vdash :P\in \text{trans}\cap \text{connex} .\dot{\exists} !P.\supset .\varsigma ʻP\in \text{Ser}\cap \text{Ded} \quad[*212·31·44]\) -/
theorem pm214_33 {P : α → α → Prop} (h : P ∈ transR ∩ connex ∧ rEx P) :
    segSer P ∈ Ser ∩ Ded := by
  obtain ⟨⟨ht, hc⟩, a, b, hab⟩ := h
  have hcp := b2_conn_po hc
  have hsect : ∀ A, A ∈ dom (imgRel P) → A ∈ sect P := by
    rintro A ⟨B, rfl⟩; exact b2_img_sect ht B
  have h0 : (∅ : Set α) ∈ dom (imgRel P) :=
    ⟨∅, Set.ext fun z => ⟨fun h => h.elim, fun ⟨_, h, _⟩ => h⟩⟩
  have h1 : P ʻʻ fld P ∈ dom (imgRel P) := ⟨fld P, rfl⟩
  have hne : (∅ : Set α) ≠ P ʻʻ fld P := by
    intro e
    have : a ∈ P ʻʻ fld P := ⟨b, ⟨a, Or.inr hab⟩, hab⟩
    rw [← e] at this; exact this
  refine pm214_3 (κ := dom (imgRel P))
    ⟨fun A B ⟨hA, hB⟩ => b2_nested hcp (hsect A hA) (hsect B hB), b2_two_ne h0 h1 hne, ?_⟩ ?_
  · funext A B; apply propext
    rw [segSer_apply]
    constructor
    · rintro ⟨⟨hA, hP⟩, hB⟩
      have := (b2_Plc_nested (hsect A hA).1 (hsect B hB).1
        (b2_nested hcp (hsect A hA) (hsect B hB))).1 hP
      exact ⟨⟨⟨hA, hB⟩, this.1⟩, this.2⟩
    · rintro ⟨⟨⟨hA, hB⟩, hs⟩, hne⟩
      exact ⟨⟨hA, (b2_Plc_nested (hsect A hA).1 (hsect B hB).1 (Or.inl hs)).2 ⟨hs, hne⟩⟩, hB⟩
  · intro L hL
    choose! f hf using fun A (hA : A ∈ L) => hL hA
    refine ⟨sumCls (f '' L), Set.ext fun z => ⟨?_, ?_⟩⟩
    · rintro ⟨A, hA, hz⟩
      rw [hf A hA] at hz
      obtain ⟨y, hy, hzy⟩ := hz
      exact ⟨y, ⟨f A, ⟨A, hA, rfl⟩, hy⟩, hzy⟩
    · rintro ⟨y, ⟨_, ⟨A, hA, rfl⟩, hy⟩, hzy⟩
      exact ⟨A, hA, by rw [hf A hA]; exact ⟨y, hy, hzy⟩⟩

/-- ✱214·34. \(\vdash :P\in \text{connex} .\dot{\exists} !\text{sgm}ʻP.\supset .\text{sgm}ʻP\in \text{Ser}\cap \text{Ded} \quad[*212·3·54]\) -/
theorem pm214_34 {P : α → α → Prop} (h : P ∈ connex ∧ rEx (sgm P)) : sgm P ∈ Ser ∩ Ded := by
  obtain ⟨hc, A0, B0, hAB0⟩ := h
  have hcp := b2_conn_po hc
  have hsect : ∀ A, A ∈ dom (imgRel P ⩀ I) → A ∈ sect P := by
    intro A hA
    rw [mem_dom_imgRel_rcap_I] at hA
    refine ⟨fun z hz => ?_, hA ▸ le_refl _⟩
    rw [hA] at hz
    obtain ⟨y, -, hzy⟩ := hz
    exact ⟨y, Or.inl hzy⟩
  obtain ⟨⟨hA0, hP0⟩, hB0⟩ := hAB0
  refine pm214_3 (κ := dom (imgRel P ⩀ I)) ⟨fun A B ⟨hA, hB⟩ =>
    b2_nested hcp (hsect A hA) (hsect B hB), b2_two_ne hA0 hB0 ?_, ?_⟩ ?_
  · intro e; subst e
    obtain ⟨-, z, ⟨hz, hz'⟩, -⟩ := hP0
    exact hz' hz
  · funext A B; apply propext
    show ((A ∈ _ ∧ Plc P A B) ∧ B ∈ _) ↔ _
    constructor
    · rintro ⟨⟨hA, hP⟩, hB⟩
      have := (b2_Plc_nested (hsect A hA).1 (hsect B hB).1
        (b2_nested hcp (hsect A hA) (hsect B hB))).1 hP
      exact ⟨⟨⟨hA, hB⟩, this.1⟩, this.2⟩
    · rintro ⟨⟨⟨hA, hB⟩, hs⟩, hne⟩
      exact ⟨⟨hA, (b2_Plc_nested (hsect A hA).1 (hsect B hB).1 (Or.inl hs)).2 ⟨hs, hne⟩⟩, hB⟩
  · intro L hL
    rw [mem_dom_imgRel_rcap_I]
    ext z
    constructor
    · rintro ⟨A, hA, hz⟩
      have e := mem_dom_imgRel_rcap_I.1 (hL hA)
      rw [e] at hz
      obtain ⟨y, hy, hzy⟩ := hz
      exact ⟨y, ⟨A, hA, hy⟩, hzy⟩
    · rintro ⟨y, ⟨A, hA, hy⟩, hzy⟩
      exact ⟨A, hA, b2_sect_P (hsect A (hL hA)) hzy hy⟩

/-- Under `P² = P` (and connexity) no class has both a maximum and a sequent (✱211·53). -/
private theorem b2_not_max_seq {P : α → α → Prop} (hd : rsq P = P) (hc : P ∈ connex) {A : Set α}
    {m s : α} (hm : maxP P m A) (hs : seqP P s A) : False := by
  have ht : ∀ x y z, P x y ∧ P y z → P x z := fun x y z hxyz => by
    rw [← hd]; exact ⟨y, hxyz.1, hxyz.2⟩
  rw [maxP_iff] at hm
  rw [seqP_iff] at hs
  have hms : P m s := hs.1.1 m ⟨hm.1.1, hm.1.2⟩
  rw [← hd] at hms
  obtain ⟨v, hmv, hvs⟩ := hms
  refine hs.2 v (fun y hy => ?_) hvs
  rcases mem_connex.1 hc y m ⟨hy.2, hm.1.2⟩ with (h1 | rfl) | h1
  · exact ht y m v ⟨h1, hmv⟩
  · exact hmv
  · exact absurd h1 (hm.2 y hy.1)

/-- ✱214·4. \[\begin{align}& \vdash \colon\ldotp P^{2}=P.P\in \text{connex} .\supset :P\in \text{Ded}.\equiv .\text{ᗡ}ʻ\text{max}_{P}=-\text{ᗡ}ʻ\text{seq}_{P}\\ &[*211·53]\end{align}\] -/
theorem pm214_4 {P : α → α → Prop} (h : rsq P = P ∧ P ∈ connex) :
    P ∈ Ded ↔ codom (maxP P) = (codom (seqP P))ᶜ := by
  constructor
  · intro hD
    ext A
    constructor
    · rintro ⟨m, hm⟩ ⟨s, hs⟩; exact b2_not_max_seq h.1 h.2 hm hs
    · intro hA
      rcases hD A with h' | h'
      · exact h'
      · exact absurd h' hA
  · intro e A
    by_cases hA : A ∈ codom (seqP P)
    · exact Or.inr hA
    · exact Or.inl (e ▸ hA)

/-- ✱214·41. \[\begin{align}& \vdash \colon\ldotp P\in \text{Ser}.\supset :P^{2}=P.P\in \text{Ded}.\equiv .\text{ᗡ}ʻ\text{max}_{P}=-\text{ᗡ}ʻ\text{seq}_{P}\\ &[*211·552]\end{align}\] -/
theorem pm214_41 {P : α → α → Prop} (h : P ∈ Ser) :
    rsq P = P ∧ P ∈ Ded ↔ codom (maxP P) = (codom (seqP P))ᶜ := by
  constructor
  · rintro ⟨hd, hD⟩; exact (pm214_4 ⟨hd, h.2⟩).1 hD
  · intro e
    have hD : P ∈ Ded := fun A => by
      by_cases hA : A ∈ codom (seqP P)
      · exact Or.inr hA
      · exact Or.inl (e ▸ hA)
    refine ⟨?_, hD⟩
    funext x y; apply propext
    constructor
    · rintro ⟨v, hxv, hvy⟩; exact mem_transR.1 h.1.2 x v y ⟨hxv, hvy⟩
    · intro hxy
      by_contra hn
      have hmax : maxP P x (ι x) := maxP_iff.2 ⟨⟨rfl, ⟨y, Or.inl hxy⟩⟩,
        fun z hz hxz => b2_irr_of_ser h x ((b2_mem_iota.1 hz) ▸ hxz)⟩
      have hseq : seqP P y (ι x) := seqP_iff.2 ⟨⟨fun w hw => (b2_mem_iota.1 hw.1) ▸ hxy,
        ⟨x, Or.inr hxy⟩⟩, fun z hz hzy => hn ⟨z, hz x ⟨rfl, ⟨y, Or.inl hxy⟩⟩, hzy⟩⟩
      have : ι x ∈ codom (maxP P) := ⟨x, hmax⟩
      rw [e] at this
      exact this ⟨y, hseq⟩

private theorem b2_refs_rcup {β : Type v} {R S : α → β → Prop} (y : β) : refs (R ⊍ S) y = refs R y ∪ refs S y := rfl

/-- The limits of a Dedekind cut. -/
private theorem b2_cut {P : α → α → Prop} (h : P ∈ Ser ∩ Ded) {A : Set α} (hA : A ∈ sect P) :
    ((∃ m, maxP P m A) → refs (limaxP P) A = refs (maxP P) A ∧
        ((¬∃ n, minP P n (fld P \ A)) → refs (liminP P) (fld P \ A) = refs (maxP P) A)) ∧
      ((¬∃ m, maxP P m A) → refs (limaxP P) A = refs (minP P) (fld P \ A) ∧
        refs (liminP P) (fld P \ A) = refs (minP P) (fld P \ A)) := by
  obtain ⟨hs, hD⟩ := h
  have hirr := b2_irr_of_ser hs
  have hseq : ∀ x, seqP P x A ↔ minP P x (fld P \ A) := fun x => b2_seq_sect hirr hs.2 hA
  have hprec : ∀ x, precP P x (fld P \ A) ↔ maxP P x A := fun x =>
    (Set.ext_iff.1 (pm214_241 ⟨⟨hs.2, (pm214_14 hs).1 hD⟩, hA⟩) x).symm
  constructor
  · intro hm
    constructor
    · ext x
      show maxP P x A ∨ (seqP P x A ∧ A ∈ (codom (maxP P))ᶜ) ↔ maxP P x A
      exact ⟨fun h' => h'.elim id fun h'' => absurd hm h''.2, Or.inl⟩
    · intro hn
      ext x
      show minP P x (fld P \ A) ∨ (precP P x (fld P \ A) ∧ fld P \ A ∈ (codom (minP P))ᶜ) ↔ _
      rw [hprec]
      exact ⟨fun h' => h'.elim (fun h'' => absurd ⟨x, h''⟩ hn) (fun h'' => h''.1),
        fun h' => Or.inr ⟨h', hn⟩⟩
  · intro hm
    constructor
    · ext x
      show maxP P x A ∨ (seqP P x A ∧ A ∈ (codom (maxP P))ᶜ) ↔ _
      rw [hseq]
      exact ⟨fun h' => h'.elim (fun h'' => absurd ⟨x, h''⟩ hm) (fun h'' => h''.1),
        fun h' => Or.inr ⟨h', hm⟩⟩
    · ext x
      show minP P x (fld P \ A) ∨ (precP P x (fld P \ A) ∧ fld P \ A ∈ (codom (minP P))ᶜ) ↔ _
      exact ⟨fun h' => h'.elim id fun h'' => absurd ((hprec x).1 h''.1) (fun h3 => hm ⟨x, h3⟩),
        Or.inl⟩

/-- ✱214·42. \(\vdash :P\in \text{Ser}\cap \text{Ded}.P^{2}=P.\alpha \in \text{sect}ʻP.\supset .\text{limax}_Pʻ\alpha =\text{limin}_Pʻ(CʻP-\alpha )\) -/
theorem pm214_42 {P : α → α → Prop} {A : Set α}
    (h : (P ∈ Ser ∩ Ded ∧ rsq P = P) ∧ A ∈ sect P) :
    Desc (limaxP P) A (fun l => Desc (liminP P) (fld P \ A) (fun l' => l = l')) := by
  obtain ⟨⟨hSD, hd⟩, hA⟩ := h
  have hc := hSD.1.2
  obtain ⟨h1, h2⟩ := b2_cut hSD hA
  by_cases hm : ∃ m, maxP P m A
  · obtain ⟨m, hmA⟩ := hm
    have hn : ¬∃ n, minP P n (fld P \ A) := by
      rintro ⟨n, hn⟩
      exact b2_not_max_seq hd hc hmA ((b2_seq_sect (b2_irr_of_ser hSD.1) hc hA).2 hn)
    have e := b2_refs_single hmA fun c hc' => b2_maxP_unique hc hc' hmA
    obtain ⟨e1, e2⟩ := h1 ⟨m, hmA⟩
    rw [b2_desc_of_refs (e1.trans e), b2_desc_of_refs ((e2 hn).trans e)]
  · obtain ⟨s, hsA⟩ : ∃ s, seqP P s A := by
      rcases hSD.2 A with h' | h'
      · exact absurd h' hm
      · exact h'
    have hmin := (b2_seq_sect (b2_irr_of_ser hSD.1) hc hA).1 hsA
    have e := b2_refs_single hmin fun c hc' => b2_minP_unique hc hc' hmin
    obtain ⟨e1, e2⟩ := h2 hm
    rw [b2_desc_of_refs (e1.trans e), b2_desc_of_refs (e2.trans e)]

/-- ✱214·43. \[\begin{align}\vdash \colon\ldotp P\in &\text{Ser}\cap \text{Ded}.\alpha \in \text{sect}ʻP.\supset :\\ &\text{limax}_Pʻ\alpha =\text{limin}_Pʻ(CʻP-\alpha ).\lor.\text{max}_{P}ʻ\alpha P_{1}\text{min}_{P}ʻ(CʻP-\alpha )\end{align}\] -/
theorem pm214_43 {P : α → α → Prop} {A : Set α} (h : P ∈ Ser ∩ Ded ∧ A ∈ sect P) :
    Desc (limaxP P) A (fun l => Desc (liminP P) (fld P \ A) (fun l' => l = l')) ∨
      Desc (maxP P) A (fun m => Desc (minP P) (fld P \ A) (fun n => P1 P m n)) := by
  obtain ⟨hSD, hA⟩ := h
  have hc := hSD.1.2
  have hs := hSD.1
  obtain ⟨h1, h2⟩ := b2_cut hSD hA
  by_cases hm : ∃ m, maxP P m A
  · obtain ⟨m, hmA⟩ := hm
    have e := b2_refs_single hmA fun c hc' => b2_maxP_unique hc hc' hmA
    obtain ⟨e1, e2⟩ := h1 ⟨m, hmA⟩
    by_cases hn : ∃ n, minP P n (fld P \ A)
    · obtain ⟨n, hnB⟩ := hn
      right
      have e' := b2_refs_single hnB fun c hc' => b2_minP_unique hc hc' hnB
      rw [b2_desc_of_refs e, b2_desc_of_refs e', P1_iff_of_transR hs.1.2 hs.1.1]
      rw [maxP_iff] at hmA
      rw [minP_iff] at hnB
      have hmn : P m n := by
        rcases mem_connex.1 hc m n ⟨hmA.1.2, hnB.1.2⟩ with (h' | rfl) | h'
        · exact h'
        · exact absurd hmA.1.1 hnB.1.1.2
        · exact absurd (b2_sect_P hA h' hmA.1.1) hnB.1.1.2
      refine ⟨hmn, fun ⟨z, hmz, hzn⟩ => ?_⟩
      by_cases hzA : z ∈ A
      · exact hmA.2 z hzA hmz
      · exact hnB.2 z ⟨⟨n, Or.inl hzn⟩, hzA⟩ hzn
    · left
      rw [b2_desc_of_refs (e1.trans e), b2_desc_of_refs ((e2 hn).trans e)]
  · left
    obtain ⟨s, hsA⟩ : ∃ s, seqP P s A := by
      rcases hSD.2 A with h' | h'
      · exact absurd h' hm
      · exact h'
    have hmin := (b2_seq_sect (b2_irr_of_ser hSD.1) hc hA).1 hsA
    have e := b2_refs_single hmin fun c hc' => b2_minP_unique hc hc' hmin
    obtain ⟨e1, e2⟩ := h2 hm
    rw [b2_desc_of_refs (e1.trans e), b2_desc_of_refs (e2.trans e)]

private theorem b2_seq_null {P : α → α → Prop} {x : α} : seqP P x Λ ↔ x ∈ refs Beg P := by
  rw [seqP_iff, b2_refs_Beg, Null_eq_empty]
  constructor
  · rintro ⟨⟨-, hx⟩, h⟩
    have hc : x ∉ codom P := fun ⟨z, hz⟩ => h z (fun y hy => hy.1.elim) hz
    refine ⟨?_, hc⟩
    obtain ⟨y, hy | hy⟩ := hx
    · exact ⟨y, hy⟩
    · exact absurd ⟨y, hy⟩ hc
  · rintro ⟨⟨y, hy⟩, hc⟩
    exact ⟨⟨fun z hz => hz.1.elim, ⟨y, Or.inl hy⟩⟩, fun z _ hz => hc ⟨z, hz⟩⟩

private theorem b2_max_fld {P : α → α → Prop} {x : α} : maxP P x (fld P) ↔ x ∈ refs Beg P˘ := by
  rw [maxP_iff, b2_refs_Beg]
  constructor
  · rintro ⟨⟨hx, -⟩, h⟩
    have hd : x ∉ dom P := fun ⟨y, hy⟩ => h y ⟨x, Or.inr hy⟩ hy
    refine ⟨?_, fun ⟨y, hy⟩ => hd ⟨y, hy⟩⟩
    obtain ⟨y, hy | hy⟩ := hx
    · exact absurd ⟨y, hy⟩ hd
    · exact ⟨y, hy⟩
  · rintro ⟨⟨y, hy⟩, hd⟩
    exact ⟨⟨⟨y, Or.inr hy⟩, ⟨y, Or.inr hy⟩⟩, fun z _ hz => hd ⟨z, hz⟩⟩

/-- ✱214·5. \(\vdash :P\in \text{Ded}.\supset .\exists !\overrightarrow{B}ʻP.\exists !\overrightarrow{B}ʻ\breve{P} .\overrightarrow{B}ʻP=\overrightarrow{\text{seq}} _{P}ʻ\Lambda .\overrightarrow{B}ʻ\breve{P} =\overrightarrow{\text{max}}_{P}ʻCʻP\) -/
theorem pm214_5 {P : α → α → Prop} (h : P ∈ Ded) :
    (((refs Beg P).Nonempty ∧ (refs Beg P˘).Nonempty) ∧ refs Beg P = refs (seqP P) Λ) ∧
      refs Beg P˘ = refs (maxP P) (fld P) := by
  have hirr := b2_Ded_irr h
  have e1 : refs Beg P = refs (seqP P) Λ := Set.ext fun x => b2_seq_null.symm
  have e2 : refs Beg P˘ = refs (maxP P) (fld P) := Set.ext fun x => b2_max_fld.symm
  refine ⟨⟨⟨?_, ?_⟩, e1⟩, e2⟩
  · rcases h Λ with ⟨m, hm⟩ | ⟨s, hs⟩
    · rw [maxP_iff, Null_eq_empty] at hm; exact hm.1.1.elim
    · exact ⟨s, b2_seq_null.1 hs⟩
  · rcases h (fld P) with ⟨m, hm⟩ | ⟨s, hs⟩
    · exact ⟨m, b2_max_fld.1 hm⟩
    · rw [seqP_iff] at hs
      exact (hirr s (hs.1.1 s ⟨hs.1.2, hs.1.2⟩)).elim

/-- ✱214·51. \(\vdash \colon\ldotp P\in \text{Ded}.\supset :{\sim}(xPx).\lor.x\in \text{D}ʻ(P\dot{-} P^{2})\) -/
theorem pm214_51 {P : α → α → Prop} {x : α} (h : P ∈ Ded) : ¬P x x ∨ x ∈ dom (P ∸ rsq P) :=
  Or.inl (b2_Ded_irr h x)

/-- ✱214·52. \(\vdash :P\in \text{Ded}.P\,\unicode{x2abd}\, P^{2}.\supset .P\,\unicode{x2abd}\, J \quad[*214·51]\) -/
theorem pm214_52 {P : α → α → Prop} (h : P ∈ Ded ∧ P ⪽ rsq P) : P ⪽ J :=
  fun x y hxy e => b2_Ded_irr h.1 x (e ▸ hxy)

private theorem b2_rcap_J_eq {P : α → α → Prop} (h : ∀ x, ¬P x x) : P ⩀ J = P := by
  funext x y; apply propext
  exact ⟨fun h' => h'.1, fun h' => ⟨h', fun e => h x (e ▸ h')⟩⟩

/-- ✱214·53. \(\vdash :P\in \text{Ded}.\supset .\text{D}ʻP=\text{D}ʻ(P\dot{\cap} J)\) -/
theorem pm214_53 {P : α → α → Prop} (h : P ∈ Ded) : dom P = dom (P ⩀ J) := by
  rw [b2_rcap_J_eq (b2_Ded_irr h)]

/-- ✱214·531. \(\vdash :P\in \text{Ded}.\supset .CʻP=Cʻ(P\dot{\cap} J)\) -/
theorem pm214_531 {P : α → α → Prop} (h : P ∈ Ded) : fld P = fld (P ⩀ J) := by
  rw [b2_rcap_J_eq (b2_Ded_irr h)]

/-- ✱214·532. \(\vdash :P\in \text{Ded}.\supset .\text{ᗡ}ʻP=\text{ᗡ}ʻ(P\dot{\cap} J)\) -/
theorem pm214_532 {P : α → α → Prop} (h : P ∈ Ded) : codom P = codom (P ⩀ J) := by
  rw [b2_rcap_J_eq (b2_Ded_irr h)]

/-- ✱214·54. \(\vdash :P\in \text{Ded}.\supset .P\dot{\cap} J\in \text{Ded}\) -/
theorem pm214_54 {P : α → α → Prop} (h : P ∈ Ded) : P ⩀ J ∈ Ded := by
  rw [b2_rcap_J_eq (b2_Ded_irr h)]; exact h

/-! Transport along an ordinal correlator `S ∈ P smor̄ Q`. -/

/-- ✱214·6. \(\vdash :P\in \text{Ded}.P\,\,\text{smor}\,\,Q.\supset .Q\in \text{Ded}\) -/
theorem pm214_6 {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} (h : P ∈ Ded ∧ smor P Q) :
    Q ∈ Ded := by
  obtain ⟨hD, S, hS⟩ := h
  intro B
  rcases hD (S ʻʻ B) with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hf : a ∈ fld P := (maxP_iff.1 ha).1.2
    obtain ⟨z, hz⟩ := tS_dom hS hf
    exact Or.inl ⟨z, (tS_max hS hz).1 ha⟩
  · have hf : a ∈ fld P := (seqP_iff.1 ha).1.2
    obtain ⟨z, hz⟩ := tS_dom hS hf
    exact Or.inr ⟨z, (tS_seq hS hz).1 ha⟩

/-- ✱214·7. \[\begin{align}& \vdash \colon\ldotp P \in \text{semi Ded}.\equiv :\alpha \in \text{sect}ʻP.\alpha \neq CʻP.\supset _{\alpha }.\exists !(\overrightarrow{\text{max}}_{P}ʻ\alpha \cup \overrightarrow{\text{seq}} _{P}ʻ\alpha )\\ &[(*214·02)]\end{align}\] -/
theorem pm214_7 {P : α → α → Prop} :
    P ∈ semiDed ↔ ∀ A, A ∈ sect P ∧ A ≠ fld P → (refs (maxP P) A ∪ refs (seqP P) A).Nonempty := by
  constructor
  · intro h A ⟨hA, hne⟩
    rcases h ⟨hA, hne⟩ with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨x, Or.inl hx⟩
    · exact ⟨x, Or.inr hx⟩
  · intro h A ⟨hA, hne⟩
    obtain ⟨x, hx | hx⟩ := h A ⟨hA, hne⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩

/-- ✱214·71. \(\vdash . \text{Ded} \subset \text{semi Ded} \quad[*214·1·7]\) -/
theorem pm214_71 : (Ded : Set (α → α → Prop)) ⊆ semiDed := fun _ h A _ => h A

/-- ✱214·72. \[\begin{align}& \vdash \colon\ldotp P \in \text{trans}.\supset :P \in \text{Ded}.\equiv .P \in \text{semi Ded}.\exists !\overrightarrow{B}ʻ\breve{P}\\ &[*214·7·13.*205·121]\end{align}\] -/
theorem pm214_72 {P : α → α → Prop} (ht : P ∈ transR) :
    P ∈ Ded ↔ P ∈ semiDed ∧ (refs Beg P˘).Nonempty := by
  constructor
  · intro h; exact ⟨pm214_71 h, (pm214_5 h).1.1.2⟩
  · rintro ⟨hs, x, hx⟩
    rw [pm214_13 ht]
    intro A hA
    by_cases hf : A = fld P
    · subst hf; exact Or.inl ⟨x, b2_max_fld.2 hx⟩
    · exact hs ⟨hA, hf⟩

/-- ✱214·73. \(\vdash . \text{semi Ded}-\iota ʻ\dot{\Lambda} \subset \text{ᗡ}ʻB \quad[*206·14.*211·44.*214·7]\) -/
theorem pm214_73 : (semiDed : Set (α → α → Prop)) \ ι rNull ⊆ codom Beg := by
  rintro P ⟨hP, hn⟩
  have hne : P ≠ rNull := hn
  obtain ⟨a, b, hab⟩ := b2_rEx_iff_ne.2 hne
  have h0 : (∅ : Set α) ∈ sect P \ ι (fld P) := by
    refine ⟨b2_empty_mem_sect P, fun e => ?_⟩
    have : a ∈ fld P := ⟨b, Or.inl hab⟩
    rw [← b2_mem_iota.1 e] at this; exact this
  rcases hP h0 with ⟨m, hm⟩ | ⟨s, hs⟩
  · rw [maxP_iff] at hm; exact hm.1.1.elim
  · rw [← Null_eq_empty] at hs
    exact ⟨s, b2_seq_null.1 hs⟩

/-- ✱214·74. \(\vdash :P\in \text{Ser}\cap \text{semi Ded}.\supset .P\unicode{x0294f}\overleftarrow{P}_{*}ʻx\in \text{semi Ded}\) -/
theorem pm214_74 {P : α → α → Prop} {x : α} (h : P ∈ Ser ∩ semiDed) :
    P ⥏ rels (anc P) x ∈ semiDed := by
  obtain ⟨hs, hD⟩ := h
  have hirr := b2_irr_of_ser hs
  have tr := mem_transR.1 hs.1.2
  have hc := hs.2
  set U := rels (anc P) x with hU
  have hUi : ∀ y, y ∈ U ↔ (x = y ∧ x ∈ fld P) ∨ P x y := fun y => anc_iff_of_transR hs.1.2
  set R := P ⥏ U
  have hRfld : fld R ⊆ U := b2_fld_fres_sub P U
  rintro C ⟨hC, hCne⟩
  have hCne' : C ≠ fld R := hCne
  obtain ⟨z, hzR, hzC⟩ := (b2_sect_ne_fld hC).1 hCne'
  have hzU := hRfld hzR
  have hxf : x ∈ fld P := ((hUi z).1 hzU).elim (fun h => h.2) (fun h => ⟨z, Or.inl h⟩)
  have hxU : x ∈ U := (hUi x).2 (Or.inl ⟨rfl, hxf⟩)
  by_cases hC0 : C.Nonempty
  · obtain ⟨c, hcC⟩ := hC0
    have hxC : x ∈ C := by
      have hcU := hRfld (hC.1 hcC)
      rcases (hUi c).1 hcU with ⟨rfl, -⟩ | hxc
      · exact hcC
      · exact b2_sect_P hC ⟨⟨hxU, hxc⟩, hcU⟩ hcC
    set C' := C ∪ refs P x
    have hC'sect : C' ∈ sect P := by
      refine ⟨fun w hw => hw.elim (fun hw => (b2_fld_fres_sub P U |> fun _ =>
        b2_fld_sub_of_rsub (b2_fres_sub U)) (hC.1 hw)) (fun hw => ⟨x, Or.inl hw⟩), ?_⟩
      rintro w ⟨c', hc', hwc'⟩
      rcases hc' with hc' | hc'
      · have hc'U := hRfld (hC.1 hc')
        by_cases hwU : w ∈ U
        · exact Or.inl (b2_sect_P hC ⟨⟨hwU, hwc'⟩, hc'U⟩ hc')
        · right
          rcases mem_connex.1 hc w x ⟨⟨c', Or.inl hwc'⟩, hxf⟩ with (h1 | rfl) | h1
          · exact h1
          · exact absurd hxU hwU
          · exact absurd ((hUi w).2 (Or.inr h1)) hwU
      · exact Or.inr (tr w c' x ⟨hwc', hc'⟩)
    have hzC' : z ∉ C' := by
      rintro (h' | h')
      · exact hzC h'
      · rcases (hUi z).1 hzU with ⟨rfl, -⟩ | hxz
        · exact hirr _ h'
        · exact hirr x (tr x z x ⟨hxz, h'⟩)
    have hzf : z ∈ fld P := b2_fld_sub_of_rsub (b2_fres_sub U) hzR
    rcases hD ⟨hC'sect, fun e => hzC' (e ▸ hzf)⟩ with ⟨m, hm⟩ | ⟨s, hs'⟩
    · rw [maxP_iff] at hm
      have hmC : m ∈ C := by
        rcases hm.1.1 with h' | h'
        · exact h'
        · exact absurd h' (hm.2 x (Or.inl hxC))
      refine Or.inl ⟨m, maxP_iff.2 ⟨⟨hmC, hC.1 hmC⟩, fun y hy hmy => hm.2 y (Or.inl hy) hmy.1.2⟩⟩
    · rw [seqP_iff] at hs'
      have hC'f : C' ∩ fld P = C' := Set.inter_eq_left.2 hC'sect.1
      have hxs : P x s := hs'.1.1 x ⟨Or.inl hxC, hxf⟩
      have hsU : s ∈ U := (hUi s).2 (Or.inr hxs)
      refine Or.inr ⟨s, seqP_iff.2 ⟨⟨fun y hy => ?_, ⟨x, Or.inr ⟨⟨hxU, hxs⟩, hsU⟩⟩⟩,
        fun v hv hvs => ?_⟩⟩
      · have hyU := hRfld (hC.1 hy.1)
        exact ⟨⟨hyU, hs'.1.1 y ⟨Or.inl hy.1, hC'sect.1 (Or.inl hy.1)⟩⟩, hsU⟩
      · refine hs'.2 v (fun y hy => ?_) hvs.1.2
        have hxv : P x v := (hv x ⟨hxC, hC.1 hxC⟩).1.2
        rcases hy.1 with hy' | hy'
        · exact (hv y ⟨hy', hC.1 hy'⟩).1.2
        · exact tr y x v ⟨hy', hxv⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hC0
    subst hC0
    right
    refine ⟨x, seqP_iff.2 ⟨⟨fun y hy => hy.1.elim, ?_⟩, fun v _ hvx => ?_⟩⟩
    · rcases (hUi z).1 hzU with ⟨rfl, -⟩ | hxz
      · exact hzR
      · exact ⟨z, Or.inl ⟨⟨hxU, hxz⟩, hzU⟩⟩
    · rcases (hUi v).1 hvx.1.1 with ⟨rfl, -⟩ | hxv
      · exact hirr _ hvx.1.2
      · exact hirr x (tr x v x ⟨hxv, hvx.1.2⟩)

/-- ✱214·75. \[\begin{align}& \vdash :P\in \text{semi Ded}.P\,\,\text{smor}\,\,Q.\supset .Q\in \text{semi Ded}\\ &[*205·8.*206·61.*212·7]\end{align}\] -/
theorem pm214_75 {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    (h : P ∈ semiDed ∧ smor P Q) : Q ∈ semiDed := by
  obtain ⟨hD, S, hS⟩ := h
  rintro B ⟨hB, hne⟩
  have hne' : S ʻʻ B ≠ fld P := by
    intro e
    have hne2 : B ≠ fld Q := hne
    obtain ⟨z, hz, hzB⟩ := (b2_sect_ne_fld hB).1 hne2
    obtain ⟨a, ha⟩ := tS_cod hS hz
    have : a ∈ S ʻʻ B := e ▸ tS_fldP hS ha
    exact hzB ((tS_mem_img hS ha).1 this)
  rcases hD ⟨tS_sect hS hB, hne'⟩ with ⟨a, ha⟩ | ⟨a, ha⟩
  · obtain ⟨z, hz⟩ := tS_dom hS (maxP_iff.1 ha).1.2
    exact Or.inl ⟨z, (tS_max hS hz).1 ha⟩
  · obtain ⟨z, hz⟩ := tS_dom hS (seqP_iff.1 ha).1.2
    exact Or.inr ⟨z, (tS_seq hS hz).1 ha⟩

/-!
## [✱215] Stretches

*(Vol. 2, p. 691)*

> *Summary of* *215.
>
> A *stretch* of a series is any piece taken out of it, and not having any gaps; that is, it is a class contained in the series, and containing all terms which come between any two of its terms. Thus it is defined as \[ \hat{\alpha} (\alpha \subset CʻP.Pʻʻ\alpha \cap \breve{P} ʻʻ\alpha \subset \alpha ). \]
>
> We denote the class of stretches by "\(\text{str}ʻP\)," where "\(\text{str}\)" stands for "stretch" or "Strecke." A stretch which has no predecessors is a section of \(P\); one which has no successors is a section of \(\breve{P}\). The properties of stretches are chiefly important in connection with compact series. In discrete series, stretches are the same as intervals.
>
> …

**Lean reading.** `str'P` is `str P`; intervals `P(x⊢⊣y)`, `P(x⟝y)`, `P(x⊣y)`, `P(x−y)` are `itvCC`,
`itvCO`, `itvOC`, `itvOO` (Defs/Part3); in ✱215·32 `P(min ⊢ seq)` is the interval `itvCO`.
`s'{(sect'P) ∩,, ''sect'P̆}` is `sumCls (graph (opImg (· ∩ ·) (sect P)) ʻʻ sect P˘)`. `P_1` is
`P1 P`. Descriptions (`max_P'α`, `limax_P'α`, `limin_P'β`, `ῐ'(α ∩ β)`) are `Desc`, the first
occurring having the larger scope; `E!` is `EDesc`. `0 ∪ 1` is `zero ∪ one`. The common core of
✱215·161–·166 is that, for connected `P`, a member of a section `α` either belongs to the upper
section `β` or precedes the members of `α ∩ β`.

**Status.** proved (all propositions; ✱215·01 definition; ✱215·165 proved (reading), converse
ancestrals).
-/

end S214

section S215

variable {α : Type u}

private theorem b2_refs_eq_of {β : Type*} {R : α → β → Prop} {y : β} {b : α}
    (h : ∀ x, R x y ↔ x = b) : refs R y = {b} := Set.ext fun x => h x

private theorem b2_mem_of_refs_eq {β : Type*} {R : α → β → Prop} {y : β} {b : α}
    (h : refs R y = {b}) : R b y := by
  have : b ∈ refs R y := by rw [h]; rfl
  exact this

/-- ✱215·01 (Df). \(\text{str}ʻP=\hat{\alpha} (\alpha \subset CʻP.Pʻʻ\alpha \cap \breve{P} ʻʻ\alpha \subset \alpha ) \quad\text{Df}\) -/
theorem pm215_01 {P : α → α → Prop} : str P = {A | A ⊆ fld P ∧ P ʻʻ A ∩ P˘ ʻʻ A ⊆ A} := rfl

/-- ✱215·1. \(\vdash :\alpha \in \text{str}ʻP.\equiv .\alpha \subset CʻP.Pʻʻ\alpha \cap \breve{P} ʻʻ\alpha \subset \alpha \quad[(*215·01)]\) -/
theorem pm215_1 {P : α → α → Prop} {A : Set α} :
    A ∈ str P ↔ A ⊆ fld P ∧ P ʻʻ A ∩ P˘ ʻʻ A ⊆ A := Iff.rfl

/-- ✱215·11. \(\vdash .\text{str}ʻP=\text{str}ʻ\breve{P} \quad[(*215·01).*33·22]\) -/
theorem pm215_11 {P : α → α → Prop} : str P = str P˘ := by
  ext A
  show (A ⊆ fld P ∧ P ʻʻ A ∩ P˘ ʻʻ A ⊆ A) ↔ (A ⊆ fld P˘ ∧ P˘ ʻʻ A ∩ P˘˘ ʻʻ A ⊆ A)
  rw [fld_cnv, b2_cnv_cnv, Set.inter_comm]

private theorem b2_sect_str {P : α → α → Prop} {A : Set α} (h : A ∈ sect P) : A ∈ str P :=
  ⟨h.1, fun _ hz => h.2 hz.1⟩

/-- ✱215·13. \(\vdash .\text{sect}ʻP\subset \text{str}ʻP.\text{sect}ʻ\breve{P} \subset \text{str}ʻP \quad[*215·1.*211·1]\) -/
theorem pm215_13 {P : α → α → Prop} : sect P ⊆ str P ∧ sect P˘ ⊆ str P := by
  refine ⟨fun A h => b2_sect_str h, fun A h => ?_⟩
  rw [pm215_11]; exact b2_sect_str h

private theorem b2_cnv_sect_mem {P : α → α → Prop} {B : Set α} (hB : B ∈ sect P˘) {x y : α}
    (h : P y x) (hy : y ∈ B) : x ∈ B := b2_sect_P hB h hy

/-- ✱215·14. \(\vdash :\alpha \in \text{sect}ʻP.\beta \in \text{sect}ʻ\breve{P} .\supset .\alpha \cap \beta \in \text{str}ʻP\) -/
theorem pm215_14 {P : α → α → Prop} {A B : Set α} (h : A ∈ sect P ∧ B ∈ sect P˘) :
    A ∩ B ∈ str P := by
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun z hz => hA.1 hz.1, ?_⟩
  rintro z ⟨⟨y, hy, hzy⟩, ⟨w, hw, hwz⟩⟩
  exact ⟨b2_sect_P hA hzy hy.1, b2_cnv_sect_mem hB hwz hw.2⟩

/-- ✱215·15. \[\begin{align}&\vdash :P\in \text{trans}.\alpha \in \text{str}ʻP.\supset .\alpha \cup Pʻʻ\alpha \in \text{sect}ʻP.\alpha \cup \breve{P} ʻʻ\alpha \in \text{sect}ʻ\breve{P} .\\ &\alpha =(\alpha \cup Pʻʻ\alpha )\cap (\alpha \cup \breve{P} ʻʻ\alpha )\end{align}\] -/
theorem pm215_15 {P : α → α → Prop} {A : Set α} (h : P ∈ transR ∧ A ∈ str P) :
    ((A ∪ P ʻʻ A ∈ sect P ∧ A ∪ P˘ ʻʻ A ∈ sect P˘) ∧ A = (A ∪ P ʻʻ A) ∩ (A ∪ P˘ ʻʻ A)) := by
  obtain ⟨ht, hA⟩ := h
  have tr := mem_transR.1 ht
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rintro z (hz | ⟨y, -, hzy⟩)
    · exact hA.1 hz
    · exact ⟨y, Or.inl hzy⟩
  · rintro z ⟨y, hy, hzy⟩
    rcases hy with hy | ⟨w, hw, hyw⟩
    · exact Or.inr ⟨y, hy, hzy⟩
    · exact Or.inr ⟨w, hw, tr z y w ⟨hzy, hyw⟩⟩
  · rw [fld_cnv]
    rintro z (hz | ⟨y, -, hzy⟩)
    · exact hA.1 hz
    · exact ⟨y, Or.inr hzy⟩
  · rintro z ⟨y, hy, hzy⟩
    rcases hy with hy | ⟨w, hw, hyw⟩
    · exact Or.inr ⟨y, hy, hzy⟩
    · exact Or.inr ⟨w, hw, tr w y z ⟨hyw, hzy⟩⟩
  · ext z
    constructor
    · intro hz; exact ⟨Or.inl hz, Or.inl hz⟩
    · rintro ⟨hz1 | hz1, hz2 | hz2⟩
      · exact hz1
      · exact hz1
      · exact hz2
      · exact hA.2 ⟨hz1, hz2⟩

/-- ✱215·16. \[\begin{align}\vdash :P\in \text{trans}.\supset .\text{str}ʻP=\hat{\gamma} \{(\exists \alpha ,\beta ).\alpha \in \text{sect}ʻP.\beta \in \text{sect}ʻ\breve{P} .\gamma &=\alpha \cap \beta\}\\ &=sʻ\{(\text{sect}ʻP)\cap_{,,} ʻʻ\text{sect}ʻ\breve{P}\}\\ [*215·14·15.*40·7]\end{align}\] -/
theorem pm215_16 {P : α → α → Prop} (ht : P ∈ transR) :
    str P = {G | ∃ A B, (A ∈ sect P ∧ B ∈ sect P˘) ∧ G = A ∩ B} ∧
      {G | ∃ A B, (A ∈ sect P ∧ B ∈ sect P˘) ∧ G = A ∩ B} =
        sumCls (graph (opImg (· ∩ ·) (sect P)) ʻʻ sect P˘) := by
  constructor
  · ext G
    constructor
    · intro hG
      obtain ⟨⟨h1, h2⟩, h3⟩ := pm215_15 ⟨ht, hG⟩
      exact ⟨_, _, ⟨h1, h2⟩, h3⟩
    · rintro ⟨A, B, h, rfl⟩; exact pm215_14 h
  · ext G
    constructor
    · rintro ⟨A, B, ⟨hA, hB⟩, rfl⟩
      exact ⟨_, ⟨B, hB, rfl⟩, ⟨A, hA, rfl⟩⟩
    · rintro ⟨K, ⟨B, hB, rfl⟩, ⟨A, hA, rfl⟩⟩
      exact ⟨A, B, ⟨hA, hB⟩, rfl⟩

/-- The common core of ✱215·161–·165: in a connected `P`, every member of a section `α`
precedes or belongs to `β`, if `α ∩ β` is not null. -/
private theorem b2_cut_pt {P : α → α → Prop} (hc : P ∈ connex) {A B : Set α} (hA : A ∈ sect P)
    (hB : B ∈ sect P˘) {c x : α} (hc' : c ∈ A ∩ B) (hx : x ∈ A) (hxB : x ∉ B) : P x c := by
  rcases mem_connex.1 hc x c ⟨hA.1 hx, hA.1 hc'.1⟩ with (h | rfl) | h
  · exact h
  · exact absurd hc'.2 hxB
  · exact absurd (b2_cnv_sect_mem hB h hc'.2) hxB

/-- ✱215·161. \[\begin{align}\vdash :P\in \text{connex} .&\alpha \in \text{sect}ʻP.\beta \in \text{sect}ʻ\breve{P} .\exists !\alpha \cap \beta .\supset .\\ &\alpha =Pʻʻ(\alpha \cap \beta )\cup (\alpha \cap \beta ).\beta =\breve{P} ʻʻ(\alpha \cap \beta )\cup (\alpha \cap \beta )\end{align}\] -/
theorem pm215_161 {P : α → α → Prop} {A B : Set α}
    (h : ((P ∈ connex ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ (A ∩ B).Nonempty) :
    A = P ʻʻ (A ∩ B) ∪ (A ∩ B) ∧ B = P˘ ʻʻ (A ∩ B) ∪ (A ∩ B) := by
  obtain ⟨⟨⟨hc, hA⟩, hB⟩, c, hcAB⟩ := h
  constructor
  · ext x
    constructor
    · intro hx
      by_cases hxB : x ∈ B
      · exact Or.inr ⟨hx, hxB⟩
      · exact Or.inl ⟨c, hcAB, b2_cut_pt hc hA hB hcAB hx hxB⟩
    · rintro (⟨y, hy, hxy⟩ | hx)
      · exact b2_sect_P hA hxy hy.1
      · exact hx.1
  · have hc' : P˘ ∈ connex := b2_cnv_connex hc
    ext x
    constructor
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inr ⟨hxA, hx⟩
      · have := b2_cut_pt (P := P˘) hc' hB (by rw [b2_cnv_cnv]; exact hA)
          ⟨hcAB.2, hcAB.1⟩ hx hxA
        exact Or.inl ⟨c, hcAB, this⟩
    · rintro (⟨y, hy, hxy⟩ | hx)
      · exact b2_sect_P hB hxy hy.2
      · exact hx.2

/-- ✱215·162. \[\begin{align}\vdash :P\in \text{trans}\cap \text{connex} .\alpha \in &\text{sect}ʻP.\beta \in \text{sect}ʻ\breve{P} .\exists !\alpha \cap \beta .\supset .\\ &Pʻʻ\alpha =Pʻʻ(\alpha \cap \beta ).\breve{P} ʻʻ\beta =\breve{P} ʻʻ(\alpha \cap \beta )\end{align}\] -/
theorem pm215_162 {P : α → α → Prop} {A B : Set α}
    (h : ((P ∈ transR ∩ connex ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ (A ∩ B).Nonempty) :
    P ʻʻ A = P ʻʻ (A ∩ B) ∧ P˘ ʻʻ B = P˘ ʻʻ (A ∩ B) := by
  obtain ⟨⟨⟨⟨ht, hc⟩, hA⟩, hB⟩, hne⟩ := h
  have tr := mem_transR.1 ht
  obtain ⟨e1, e2⟩ := pm215_161 ⟨⟨⟨hc, hA⟩, hB⟩, hne⟩
  constructor
  · ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      rw [e1] at hy
      rcases hy with ⟨w, hw, hyw⟩ | hy
      · exact ⟨w, hw, tr x y w ⟨hxy, hyw⟩⟩
      · exact ⟨y, hy, hxy⟩
    · rintro ⟨y, hy, hxy⟩; exact ⟨y, hy.1, hxy⟩
  · ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      rw [e2] at hy
      rcases hy with ⟨w, hw, hyw⟩ | hy
      · exact ⟨w, hw, tr w y x ⟨hyw, hxy⟩⟩
      · exact ⟨y, hy, hxy⟩
    · rintro ⟨y, hy, hxy⟩; exact ⟨y, hy.2, hxy⟩

/-- ✱215·163. \[\begin{align}\vdash :P\in \text{trans}\cap \text{connex} .\alpha \in \text{sect}ʻP.\beta \in &\text{sect}ʻ\breve{P} .\exists !\alpha \cap \beta .\supset .\\ &pʻ\overleftarrow{P}ʻʻ\alpha =pʻ\overleftarrow{P}ʻʻ(\alpha \cap \beta )\end{align}\] -/
theorem pm215_163 {P : α → α → Prop} {A B : Set α}
    (h : ((P ∈ transR ∩ connex ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ (A ∩ B).Nonempty) :
    prodCls (Rbwd P ʻʻ A) = prodCls (Rbwd P ʻʻ (A ∩ B)) := by
  obtain ⟨⟨⟨⟨ht, hc⟩, hA⟩, hB⟩, c, hcAB⟩ := h
  have tr := mem_transR.1 ht
  ext z
  rw [mem_prodCls_Rbwd, mem_prodCls_Rbwd]
  constructor
  · intro H y hy; exact H y hy.1
  · intro H y hy
    by_cases hyB : y ∈ B
    · exact H y ⟨hy, hyB⟩
    · exact tr y c z ⟨b2_cut_pt hc hA hB hcAB hy hyB, H c hcAB⟩

/-- Maxima and sequents of `α` are those of `α ∩ β` (✱215·164, first half). -/
private theorem b2_164 {P : α → α → Prop} {A B : Set α} (ht : P ∈ transR) (hc : P ∈ connex)
    (hA : A ∈ sect P) (hB : B ∈ sect P˘) (hne : (A ∩ B).Nonempty) :
    refs (maxP P) A = refs (maxP P) (A ∩ B) ∧ refs (seqP P) A = refs (seqP P) (A ∩ B) := by
  obtain ⟨c, hcAB⟩ := hne
  have tr := mem_transR.1 ht
  constructor
  · ext x
    show maxP P x A ↔ maxP P x (A ∩ B)
    rw [maxP_iff, maxP_iff]
    constructor
    · rintro ⟨⟨hx, hf⟩, hn⟩
      have hxB : x ∈ B := by
        by_contra hxB
        exact hn c hcAB.1 (b2_cut_pt hc hA hB hcAB hx hxB)
      exact ⟨⟨⟨hx, hxB⟩, hf⟩, fun y hy => hn y hy.1⟩
    · rintro ⟨⟨hx, hf⟩, hn⟩
      exact ⟨⟨hx.1, hf⟩, fun y hy hxy => hn y ⟨hy, b2_cnv_sect_mem hB hxy hx.2⟩ hxy⟩
  · ext x
    show seqP P x A ↔ seqP P x (A ∩ B)
    have hAf : A ∩ fld P = A := Set.inter_eq_left.2 hA.1
    have hABf : A ∩ B ∩ fld P = A ∩ B :=
      Set.inter_eq_left.2 (fun z hz => hA.1 hz.1)
    show minP P x (prodCls (Rbwd P ʻʻ (A ∩ fld P))) ↔ minP P x (prodCls (Rbwd P ʻʻ (A ∩ B ∩ fld P)))
    rw [hAf, hABf, pm215_163 ⟨⟨⟨⟨ht, hc⟩, hA⟩, hB⟩, c, hcAB⟩]

private theorem b2_trans_cnv {P : α → α → Prop} (ht : P ∈ transR) : P˘ ∈ transR := by
  rw [mem_transR] at ht ⊢
  intro x y z ⟨h1, h2⟩; exact ht z y x ⟨h2, h1⟩

/-- ✱215·164. \[\begin{align}\vdash :\text{Hp}*215·162.\supset .&\overrightarrow{\text{min}}_{P}ʻ\beta =\overrightarrow{\text{min}}_{P}ʻ(\alpha \cap \beta ).\overrightarrow{\text{max}}_{P}ʻ\alpha =\overrightarrow{\text{max}}_{P}ʻ(\alpha \cap \beta ).\\ &\overrightarrow{\text{seq}} _{P}ʻ\alpha =\overrightarrow{\text{seq}} _{P}ʻ(\alpha \cap \beta ).\overrightarrow{\text{prec}} _{P}ʻ\beta =\overrightarrow{\text{prec}} _{P}ʻ(\alpha \cap \beta ).\\ &\overrightarrow{\text{lt}} _{P}ʻ\alpha =\overrightarrow{\text{lt}} _{P}ʻ(\alpha \cap \beta ).\overrightarrow{\text{limax}} _{P}ʻ\alpha =\overrightarrow{\text{limax}} _{P}ʻ(\alpha \cap \beta )\end{align}\] -/
theorem pm215_164 {P : α → α → Prop} {A B : Set α}
    (h : ((P ∈ transR ∩ connex ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ (A ∩ B).Nonempty) :
    ((((refs (minP P) B = refs (minP P) (A ∩ B) ∧ refs (maxP P) A = refs (maxP P) (A ∩ B)) ∧
      refs (seqP P) A = refs (seqP P) (A ∩ B)) ∧ refs (precP P) B = refs (precP P) (A ∩ B)) ∧
      refs (ltP P) A = refs (ltP P) (A ∩ B)) ∧ refs (limaxP P) A = refs (limaxP P) (A ∩ B) := by
  obtain ⟨⟨⟨⟨ht, hc⟩, hA⟩, hB⟩, hne⟩ := h
  obtain ⟨e1, e2⟩ := b2_164 ht hc hA hB hne
  have hBA : (B ∩ A).Nonempty := by rw [Set.inter_comm]; exact hne
  obtain ⟨e3, e4⟩ := b2_164 (P := P˘) (b2_trans_cnv ht) (b2_cnv_connex hc) hB
    (by rw [b2_cnv_cnv]; exact hA) hBA
  rw [Set.inter_comm B A] at e3 e4
  have e5 : refs (ltP P) A = refs (ltP P) (A ∩ B) := by
    ext x
    show seqP P x A ∧ A ∈ (codom (maxP P))ᶜ ↔ seqP P x (A ∩ B) ∧ A ∩ B ∈ (codom (maxP P))ᶜ
    have : A ∈ codom (maxP P) ↔ A ∩ B ∈ codom (maxP P) :=
      ⟨fun ⟨m, hm⟩ => ⟨m, (Set.ext_iff.1 e1 m).1 hm⟩, fun ⟨m, hm⟩ => ⟨m, (Set.ext_iff.1 e1 m).2 hm⟩⟩
    rw [Set.mem_compl_iff, Set.mem_compl_iff, this]
    exact and_congr (Set.ext_iff.1 e2 x) Iff.rfl
  refine ⟨⟨⟨⟨⟨e3, e1⟩, e2⟩, ?_⟩, e5⟩, ?_⟩
  · rw [precP_eq_seqP_cnv]; exact e4
  · ext x
    show maxP P x A ∨ ltP P x A ↔ maxP P x (A ∩ B) ∨ ltP P x (A ∩ B)
    exact or_congr (Set.ext_iff.1 e1 x) (Set.ext_iff.1 e5 x)

private theorem b2_sect_po_cnv {P : α → α → Prop} {B : Set α} (hB : B ∈ sect P˘) {x y : α}
    (h : po P y x) (hy : y ∈ B) : x ∈ B := by
  rw [po_iff_transGen] at h
  induction h with
  | single h => exact b2_cnv_sect_mem hB h hy
  | tail _ h ih => exact b2_cnv_sect_mem hB h ih

/-- ✱215·165. \[\begin{align}&\vdash :P_{\text{po}}\in \text{connex} .\alpha \in \text{sect}ʻP.\beta \in \text{sect}ʻ\breve{P} .\exists !\alpha \cap \beta .\supset .\\ &\alpha =P_{*}ʻʻ(\alpha \cap \beta ).\beta =\breve{P} _{*}ʻʻ(\alpha \cap \beta ).Pʻʻ\alpha =P_{\text{po}}ʻʻ(\alpha \cap \beta ).\breve{P} ʻʻ\beta =\breve{P} _{\text{po}}ʻʻ(\alpha \cap \beta )\end{align}\]

**Status.** proved (reading): `P̆_*` is `Cnv'P_*` (✱90·02, `ancCnv P`), and `P̆_po` is read as the converse of `P_po` (`(po P)˘`, which equals `po P˘`). -/
theorem pm215_165 {P : α → α → Prop} {A B : Set α}
    (h : ((po P ∈ connex ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ (A ∩ B).Nonempty) :
    ((A = anc P ʻʻ (A ∩ B) ∧ B = ancCnv P ʻʻ (A ∩ B)) ∧ P ʻʻ A = po P ʻʻ (A ∩ B)) ∧
      P˘ ʻʻ B = (po P)˘ ʻʻ (A ∩ B) := by
  obtain ⟨⟨⟨hc, hA⟩, hB⟩, c, hcAB⟩ := h
  have key : ∀ x, x ∈ A → ∃ y, y ∈ A ∩ B ∧ anc P x y := by
    intro x hx
    rcases b2_connPo hc x c (hA.1 hx) (hA.1 hcAB.1) with (h | rfl) | h
    · exact ⟨c, hcAB, b2_anc_of_po h⟩
    · exact ⟨x, hcAB, b2_anc_refl (hA.1 hx)⟩
    · exact ⟨x, ⟨hx, b2_sect_po_cnv hB h hcAB.2⟩, b2_anc_refl (hA.1 hx)⟩
  have key' : ∀ x, x ∈ B → ∃ y, y ∈ A ∩ B ∧ anc P y x := by
    intro x hx
    have hxf : x ∈ fld P := by have := hB.1 hx; rwa [fld_cnv] at this
    have hcf : c ∈ fld P := hA.1 hcAB.1
    rcases b2_connPo hc x c hxf hcf with (h | rfl) | h
    · exact ⟨x, ⟨b2_sect_po hA h hcAB.1, hx⟩, b2_anc_refl hxf⟩
    · exact ⟨x, hcAB, b2_anc_refl hxf⟩
    · exact ⟨c, hcAB, b2_anc_of_po h⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · ext x
    exact ⟨fun hx => key x hx, fun ⟨y, hy, hxy⟩ => b2_sect_anc hA hxy hy.1⟩
  · ext x
    refine ⟨fun hx => key' x hx, fun ⟨y, hy, hyx⟩ => ?_⟩
    rcases anc_iff_po.1 hyx with ⟨rfl, -⟩ | h
    · exact hy.2
    · exact b2_sect_po_cnv hB h hy.2
  · ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨w, hw, hyw⟩ := key y hy
      exact ⟨w, hw, b2_po_of_P_anc hxy hyw⟩
    · rintro ⟨w, hw, hxw⟩
      obtain ⟨y, hxy, hyw⟩ := b2_po_head hxw
      exact ⟨y, b2_sect_anc hA hyw hw.1, hxy⟩
  · ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨w, hw, hwy⟩ := key' y hy
      exact ⟨w, hw, b2_po_of_anc_po hwy (b2_po_of hxy)⟩
    · rintro ⟨w, hw, hwx⟩
      obtain ⟨y, hwy, hyx⟩ := b2_po_tail hwx
      have : y ∈ B := by
        rcases anc_iff_po.1 hwy with ⟨rfl, -⟩ | h
        · exact hw.2
        · exact b2_sect_po_cnv hB h hw.2
      exact ⟨y, this, hyx⟩

/-- ✱215·166. \[\begin{align}\vdash :P_{\text{po}}\in \text{Ser}.\alpha \in \text{sect}ʻP.\beta \in &\text{sect}ʻ\breve{P} .\alpha \cap \beta \in 1.\supset .\\ &\alpha \cap \beta = \iota ʻ\text{max}_{P}ʻ\alpha = \iota ʻ\text{min}_{P}ʻ\beta\end{align}\] -/
theorem pm215_166 {P : α → α → Prop} {A B : Set α}
    (h : ((po P ∈ Ser ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ A ∩ B ∈ (one : Set (Set α))) :
    Desc (maxP P) A (fun m => A ∩ B = ι m) ∧
      Desc (maxP P) A (fun m => Desc (minP P) B (fun n => ι m = ι n)) := by
  obtain ⟨⟨⟨hs, hA⟩, hB⟩, c, hc⟩ := h
  have hJ := (b2_serPo hs).1
  have hcAB : c ∈ A ∩ B := hc ▸ rfl
  have hcf : c ∈ fld P := hA.1 hcAB.1
  have hmax : maxP P c A := by
    rw [maxP_iff]
    refine ⟨⟨hcAB.1, hcf⟩, fun y hy hcy => ?_⟩
    have : y ∈ A ∩ B := ⟨hy, b2_cnv_sect_mem hB hcy hcAB.2⟩
    rw [hc, b2_mem_iota] at this
    subst this; exact b2_irrP hJ hcy
  have hmin : minP P c B := by
    rw [minP_iff]
    refine ⟨⟨hcAB.2, hcf⟩, fun y hy hyc => ?_⟩
    have : y ∈ A ∩ B := ⟨b2_sect_P hA hyc hcAB.1, hy⟩
    rw [hc, b2_mem_iota] at this
    subst this; exact b2_irrP hJ hyc
  have u1 : refs (maxP P) A = {c} := by
    refine b2_refs_single hmax fun m hm => ?_
    rw [maxP_iff] at hm
    rcases (b2_serPo hs).2 m c hm.1.2 hcf with (h' | rfl) | h'
    · obtain ⟨v, hmv, hvc⟩ := b2_po_head h'
      exact absurd hmv (hm.2 v (b2_sect_anc hA hvc hcAB.1))
    · rfl
    · have : m ∈ A ∩ B := ⟨hm.1.1, b2_sect_po_cnv hB h' hcAB.2⟩
      rw [hc, b2_mem_iota] at this; exact this
  have u2 : refs (minP P) B = {c} := by
    refine b2_refs_single hmin fun m hm => ?_
    rw [minP_iff] at hm
    rcases (b2_serPo hs).2 m c hm.1.2 hcf with (h' | rfl) | h'
    · have : m ∈ A ∩ B := ⟨b2_sect_po hA h' hcAB.1, hm.1.1⟩
      rw [hc, b2_mem_iota] at this; exact this
    · rfl
    · obtain ⟨v, hcv, hvm⟩ := b2_po_tail h'
      have hv : v ∈ B := by
        rcases anc_iff_po.1 hcv with ⟨rfl, -⟩ | h''
        · exact hcAB.2
        · exact b2_sect_po_cnv hB h'' hcAB.2
      exact absurd hvm (hm.2 v hv)
  rw [b2_desc_of_refs u1, b2_desc_of_refs u1, b2_desc_of_refs u2]
  exact ⟨hc, rfl⟩

/-- ✱215·17. \(\vdash :P\in \text{trans}.\supset .\breve{P} ʻʻ\alpha \cap Pʻʻ\beta \in \text{str}ʻP\) -/
theorem pm215_17 {P : α → α → Prop} {A B : Set α} (ht : P ∈ transR) :
    P˘ ʻʻ A ∩ P ʻʻ B ∈ str P := by
  rw [Set.inter_comm]
  refine pm215_14 ⟨b2_img_sect ht B, ?_⟩
  exact b2_img_sect (b2_trans_cnv ht) A

private theorem b2_refs_anc_sect (P : α → α → Prop) (y : α) : refs (anc P) y ∈ sect P :=
  b2_refs_anc_mem_sect P y

private theorem b2_refs_po_sect (P : α → α → Prop) (y : α) : refs (po P) y ∈ sect P := by
  refine ⟨fun z h => (b2_fld_of_po h).1, ?_⟩
  rintro z ⟨w, hw, hzw⟩
  exact b2_po_trans (b2_po_of hzw) hw

private theorem b2_rels_anc_sect (P : α → α → Prop) (x : α) : rels (anc P) x ∈ sect P˘ := by
  refine ⟨fun z h => by rw [fld_cnv]; exact (b2_fld_of_anc h).2, ?_⟩
  rintro z ⟨w, hw, hwz⟩
  exact b2_anc_trans hw (b2_anc_of_po (b2_po_of hwz))

private theorem b2_rels_po_sect (P : α → α → Prop) (x : α) : rels (po P) x ∈ sect P˘ := by
  refine ⟨fun z h => by rw [fld_cnv]; exact (b2_fld_of_po h).2, ?_⟩
  rintro z ⟨w, hw, hwz⟩
  exact b2_po_trans hw (b2_po_of hwz)

/-- ✱215·18. \(\vdash .P(x\vdash\dashv y),P(x\unicode{x27dd} y),P(x\dashv y),P(x-y)\in \text{str}ʻP\) -/
theorem pm215_18 {P : α → α → Prop} {x y : α} :
    ((itvCC P x y ∈ str P ∧ itvCO P x y ∈ str P) ∧ itvOC P x y ∈ str P) ∧
      itvOO P x y ∈ str P := by
  have f : ∀ A B : Set α, A ∈ sect P˘ → B ∈ sect P → A ∩ B ∈ str P := fun A B hA hB => by
    rw [Set.inter_comm]; exact pm215_14 ⟨hB, hA⟩
  exact ⟨⟨⟨f _ _ (b2_rels_anc_sect P x) (b2_refs_anc_sect P y),
    f _ _ (b2_rels_anc_sect P x) (b2_refs_po_sect P y)⟩,
    f _ _ (b2_rels_po_sect P x) (b2_refs_anc_sect P y)⟩,
    f _ _ (b2_rels_po_sect P x) (b2_refs_po_sect P y)⟩

/-- ✱215·19. \(\vdash :P^{2}\,\unicode{x2abd}\, J.x\in CʻP.\supset .\iota ʻx\in \text{str}ʻP\) -/
theorem pm215_19 {P : α → α → Prop} {x : α} (h : rsq P ⪽ J ∧ x ∈ fld P) : ι x ∈ str P := by
  obtain ⟨hJ, hx⟩ := h
  refine ⟨fun z hz => (b2_mem_iota.1 hz) ▸ hx, ?_⟩
  rintro z ⟨⟨y, hy, hzy⟩, ⟨w, hw, hwz⟩⟩
  have e : w = y := (b2_mem_iota.1 hw).trans (b2_mem_iota.1 hy).symm
  rw [e] at hwz
  exact absurd rfl (hJ z z ⟨y, hzy, hwz⟩)

private theorem b2_str_P {P : α → α → Prop} {A : Set α} (hA : A ∈ str P) {z a b : α} (h1 : P z a)
    (ha : a ∈ A) (h2 : P b z) (hb : b ∈ A) : z ∈ A := hA.2 ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩

private theorem b2_215_2 {P : α → α → Prop} {A : Set α} {x : α} (hc : P ∈ connex) (hA : A ∈ str P)
    (hx : x ∈ A) : P ʻʻ A = A \ refs (maxP P) A ∪ refs P x := by
  ext z
  constructor
  · rintro ⟨a, ha, hza⟩
    by_cases hzA : z ∈ A
    · exact Or.inl ⟨hzA, fun hm => (maxP_iff.1 hm).2 a ha hza⟩
    · rcases mem_connex.1 hc z x ⟨⟨a, Or.inl hza⟩, hA.1 hx⟩ with (h | rfl) | h
      · exact Or.inr h
      · exact absurd hx hzA
      · exact absurd (b2_str_P hA hza ha h hx) hzA
  · rintro (⟨hzA, hn⟩ | hzx)
    · by_contra hz
      exact hn (maxP_iff.2 ⟨⟨hzA, hA.1 hzA⟩, fun y hy hzy => hz ⟨y, hy, hzy⟩⟩)
    · exact ⟨x, hx, hzx⟩

/-- ✱215·2. \[\begin{align}\vdash :P\in \text{connex} .\alpha \in \text{str}ʻP.x\in \alpha .\supset .&Pʻʻ\alpha = \alpha -\overrightarrow{\text{max}}_{P}ʻ\alpha \cup \overrightarrow{P}ʻx.\\ &\breve{P} ʻʻ\alpha = \alpha -\overrightarrow{\text{min}}_{P}ʻ\alpha \cup \overleftarrow{P}ʻx\end{align}\] -/
theorem pm215_2 {P : α → α → Prop} {A : Set α} {x : α}
    (h : (P ∈ connex ∧ A ∈ str P) ∧ x ∈ A) :
    P ʻʻ A = A \ refs (maxP P) A ∪ refs P x ∧ P˘ ʻʻ A = A \ refs (minP P) A ∪ rels P x := by
  obtain ⟨⟨hc, hA⟩, hx⟩ := h
  refine ⟨b2_215_2 hc hA hx, ?_⟩
  have hA' : A ∈ str P˘ := by rw [← pm215_11]; exact hA
  exact b2_215_2 (b2_cnv_connex hc) hA' hx

/-- ✱215·21. \(\vdash :P\in \text{connex} .\alpha ,\beta \in \text{str}ʻP.\exists !\alpha \cap \beta .\supset .\alpha \cap \beta \in \text{str}ʻP\) -/
theorem pm215_21 {P : α → α → Prop} {A B : Set α}
    (h : (P ∈ connex ∧ (A ∈ str P ∧ B ∈ str P)) ∧ (A ∩ B).Nonempty) : A ∩ B ∈ str P := by
  obtain ⟨⟨-, hA, hB⟩, -⟩ := h
  refine ⟨fun z hz => hA.1 hz.1, ?_⟩
  rintro z ⟨⟨y, hy, hzy⟩, ⟨w, hw, hwz⟩⟩
  exact ⟨b2_str_P hA hzy hy.1 hwz hw.1, b2_str_P hB hzy hy.2 hwz hw.2⟩

/-- ✱215·22. \(\vdash :\alpha ,\beta \in \text{str}ʻP.\supset .\alpha \cap \beta \in \text{str}ʻP\) -/
theorem pm215_22 {P : α → α → Prop} {A B : Set α} (h : A ∈ str P ∧ B ∈ str P) :
    A ∩ B ∈ str P := by
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun z hz => hA.1 hz.1, ?_⟩
  rintro z ⟨⟨y, hy, hzy⟩, ⟨w, hw, hwz⟩⟩
  exact ⟨b2_str_P hA hzy hy.1 hwz hw.1, b2_str_P hB hzy hy.2 hwz hw.2⟩

/-- ✱215·23. \(\vdash :P\in \text{connex} .\mu \subset \text{str}ʻP.\exists !pʻ\mu .\supset .sʻ\mu \in \text{str}ʻP\) -/
theorem pm215_23 {P : α → α → Prop} {M : Set (Set α)}
    (h : (P ∈ connex ∧ M ⊆ str P) ∧ (prodCls M).Nonempty) : sumCls M ∈ str P := by
  obtain ⟨⟨hc, hM⟩, x, hx⟩ := h
  refine ⟨fun z ⟨A, hA, hz⟩ => (hM hA).1 hz, ?_⟩
  rintro z ⟨⟨a, ⟨A1, hA1, ha⟩, hza⟩, ⟨b, ⟨A2, hA2, hb⟩, hbz⟩⟩
  have hxf : x ∈ fld P := (hM hA1).1 (hx A1 hA1)
  rcases mem_connex.1 hc z x ⟨⟨a, Or.inl hza⟩, hxf⟩ with (h1 | rfl) | h1
  · exact ⟨A2, hA2, b2_str_P (hM hA2) h1 (hx A2 hA2) hbz hb⟩
  · exact ⟨A1, hA1, hx A1 hA1⟩
  · exact ⟨A1, hA1, b2_str_P (hM hA1) hza ha h1 (hx A1 hA1)⟩

/-- ✱215·24. \(\vdash :\mu \subset \text{str}ʻP.\supset .CʻP\cap pʻ\mu \in \text{str}ʻP\) -/
theorem pm215_24 {P : α → α → Prop} {M : Set (Set α)} (h : M ⊆ str P) :
    fld P ∩ prodCls M ∈ str P := by
  refine ⟨fun z hz => hz.1, ?_⟩
  rintro z ⟨⟨a, ha, hza⟩, ⟨b, hb, hbz⟩⟩
  exact ⟨⟨a, Or.inl hza⟩, fun A hA => b2_str_P (h hA) hza (ha.2 A hA) hbz (hb.2 A hA)⟩

/-- ✱215·25. \(\vdash :\mu \subset \text{str}ʻP.\exists !\mu .\supset .pʻ\mu \in \text{str}ʻP\) -/
theorem pm215_25 {P : α → α → Prop} {M : Set (Set α)} (h : M ⊆ str P ∧ M.Nonempty) :
    prodCls M ∈ str P := by
  obtain ⟨h, A, hA⟩ := h
  have e : fld P ∩ prodCls M = prodCls M :=
    Set.inter_eq_right.2 fun z hz => (h hA).1 (hz A hA)
  rw [← e]; exact pm215_24 h

/-- ✱215·3. \[\begin{align}\vdash \colon\ldotp P\in &\text{connex} .\alpha ,\beta \in \text{str}ʻP-{℩}ʻ\Lambda .\alpha \cap \beta =\Lambda .\supset :\\ &\alpha \subset Pʻʻ\beta .\equiv .\alpha \subset pʻ\overrightarrow{P}ʻʻ\beta .\equiv .\beta \subset pʻ\overleftarrow{P}ʻʻ\alpha .\equiv .\beta \subset \breve{P} ʻʻ\alpha\end{align}\] -/
theorem pm215_3 {P : α → α → Prop} {A B : Set α}
    (h : (P ∈ connex ∧ (A ∈ str P \ ι Λ ∧ B ∈ str P \ ι Λ)) ∧ A ∩ B = Λ) :
    (((A ⊆ P ʻʻ B ↔ A ⊆ prodCls (Rfwd P ʻʻ B)) ∧
      (A ⊆ prodCls (Rfwd P ʻʻ B) ↔ B ⊆ prodCls (Rbwd P ʻʻ A))) ∧
      (B ⊆ prodCls (Rbwd P ʻʻ A) ↔ B ⊆ P˘ ʻʻ A)) := by
  obtain ⟨⟨hc, hA, hB⟩, hd⟩ := h
  rw [b2_mem_diff_iotaNull] at hA hB
  have hdis : ∀ z, z ∈ A → z ∈ B → False := fun z h1 h2 => by
    have : z ∈ A ∩ B := ⟨h1, h2⟩
    rw [hd, Null_eq_empty] at this; exact this
  refine ⟨⟨⟨fun H a ha => ?_, fun H a ha => ?_⟩, ⟨fun H b hb => ?_, fun H a ha => ?_⟩⟩,
    ⟨fun H b hb => ?_, fun H b hb => ?_⟩⟩
  · obtain ⟨b0, hb0, hab0⟩ := H ha
    rw [mem_prodCls_Rfwd]
    intro b hb
    rcases mem_connex.1 hc a b ⟨hA.1.1 ha, hB.1.1 hb⟩ with (h1 | rfl) | h1
    · exact h1
    · exact (hdis a ha hb).elim
    · exact (hdis a ha (b2_str_P hB.1 hab0 hb0 h1 hb)).elim
  · obtain ⟨b, hb⟩ := hB.2
    exact ⟨b, hb, mem_prodCls_Rfwd.1 (H ha) b hb⟩
  · rw [mem_prodCls_Rbwd]
    intro a ha
    exact mem_prodCls_Rfwd.1 (H ha) b hb
  · rw [mem_prodCls_Rfwd]
    intro b hb
    exact mem_prodCls_Rbwd.1 (H hb) a ha
  · obtain ⟨a, ha⟩ := hA.2
    exact ⟨a, ha, mem_prodCls_Rbwd.1 (H hb) a ha⟩
  · obtain ⟨a0, ha0, ha0b⟩ := H hb
    rw [mem_prodCls_Rbwd]
    intro a ha
    rcases mem_connex.1 hc a b ⟨hA.1.1 ha, hB.1.1 hb⟩ with (h1 | rfl) | h1
    · exact h1
    · exact (hdis a ha hb).elim
    · exact (hdis b (b2_str_P hA.1 h1 ha ha0b ha0) hb).elim

private theorem b2_mem_itvCC {P : α → α → Prop} (ht : P ∈ transR) {x y z : α} :
    z ∈ itvCC P x y ↔ ((x = z ∧ x ∈ fld P) ∨ P x z) ∧ ((z = y ∧ z ∈ fld P) ∨ P z y) :=
  and_congr (anc_iff_of_transR ht) (anc_iff_of_transR ht)

/-- ✱215·31. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .\alpha \in \text{str}ʻP.\text{E}!&\text{min}_{P}ʻ\alpha .\text{E}!\text{max}_{P}ʻ\alpha .\supset .\\ &\alpha = P(\text{min}_{P}ʻ\alpha \vdash\dashv \text{max}_{P}ʻ\alpha )\end{align}\] -/
theorem pm215_31 {P : α → α → Prop} {A : Set α}
    (h : ((P ∈ transR ∩ connex ∧ A ∈ str P) ∧ EDesc (minP P) A) ∧ EDesc (maxP P) A) :
    Desc (minP P) A (fun m => Desc (maxP P) A (fun M => A = itvCC P m M)) := by
  obtain ⟨⟨⟨⟨ht, hc⟩, hA⟩, ⟨m, hm⟩⟩, ⟨M, hM⟩⟩ := h
  have hm' : minP P m A := (hm m).2 rfl
  have hM' : maxP P M A := (hM M).2 rfl
  rw [b2_desc_of_refs (b2_refs_eq_of hm), b2_desc_of_refs (b2_refs_eq_of hM)]
  rw [minP_iff] at hm'
  rw [maxP_iff] at hM'
  ext z
  rw [b2_mem_itvCC ht]
  constructor
  · intro hz
    have hzf := hA.1 hz
    constructor
    · rcases mem_connex.1 hc m z ⟨hm'.1.2, hzf⟩ with (h1 | rfl) | h1
      · exact Or.inr h1
      · exact Or.inl ⟨rfl, hzf⟩
      · exact absurd h1 (hm'.2 z hz)
    · rcases mem_connex.1 hc z M ⟨hzf, hM'.1.2⟩ with (h1 | rfl) | h1
      · exact Or.inr h1
      · exact Or.inl ⟨rfl, hzf⟩
      · exact absurd h1 (hM'.2 z hz)
  · rintro ⟨⟨rfl, -⟩ | h1, ⟨rfl, -⟩ | h2⟩
    · exact hm'.1.1
    · exact hm'.1.1
    · exact hM'.1.1
    · exact b2_str_P hA h2 hM'.1.1 h1 hm'.1.1

private theorem b2_mem_itvCO {P : α → α → Prop} (ht : P ∈ transR) {x y z : α} :
    z ∈ itvCO P x y ↔ ((x = z ∧ x ∈ fld P) ∨ P x z) ∧ P z y := by
  show anc P x z ∧ po P z y ↔ _
  rw [anc_iff_of_transR ht, po_eq_of_transR ht]

private theorem b2_mem_itvOO {P : α → α → Prop} (ht : P ∈ transR) {x y z : α} :
    z ∈ itvOO P x y ↔ P x z ∧ P z y := by
  show po P x z ∧ po P z y ↔ _
  rw [po_eq_of_transR ht]

/-- In a connected relation, a term outside a stretch, preceded by a member, either follows
every member or precedes some member. -/
private theorem b2_str_above {P : α → α → Prop} (hc : P ∈ connex) {A : Set α} (hA : A ⊆ fld P) {z : α}
    (hz : z ∈ fld P) (hzA : z ∉ A) (hn : z ∉ P ʻʻ A) : ∀ y, y ∈ A ∩ fld P → P y z := by
  intro y hy
  rcases mem_connex.1 hc y z ⟨hy.2, hz⟩ with (h1 | rfl) | h1
  · exact h1
  · exact absurd hy.1 hzA
  · exact absurd ⟨y, hy.1, h1⟩ hn

/-- ✱215·32. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .\alpha \in \text{str}ʻP.\text{E}!&\text{min}_{P}ʻ\alpha .\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\\ &\alpha=P(\text{min}_{P}ʻ\alpha \vdash \text{seq}_{P}ʻ\alpha )\end{align}\] -/
theorem pm215_32 {P : α → α → Prop} {A : Set α}
    (h : ((P ∈ transR ∩ connex ∧ A ∈ str P) ∧ EDesc (minP P) A) ∧ EDesc (seqP P) A) :
    Desc (minP P) A (fun m => Desc (seqP P) A (fun s => A = itvCO P m s)) := by
  obtain ⟨⟨⟨⟨ht, hc⟩, hA⟩, ⟨m, hm⟩⟩, ⟨s, hs⟩⟩ := h
  have hm' : minP P m A := (hm m).2 rfl
  have hs' : seqP P s A := (hs s).2 rfl
  rw [b2_desc_of_refs (b2_refs_eq_of hm), b2_desc_of_refs (b2_refs_eq_of hs)]
  rw [minP_iff] at hm'
  rw [seqP_iff] at hs'
  ext z
  rw [b2_mem_itvCO ht]
  constructor
  · intro hz
    have hzf := hA.1 hz
    refine ⟨?_, hs'.1.1 z ⟨hz, hzf⟩⟩
    rcases mem_connex.1 hc m z ⟨hm'.1.2, hzf⟩ with (h1 | rfl) | h1
    · exact Or.inr h1
    · exact Or.inl ⟨rfl, hzf⟩
    · exact absurd h1 (hm'.2 z hz)
  · rintro ⟨⟨rfl, -⟩ | h1, h2⟩
    · exact hm'.1.1
    · by_contra hzA
      by_cases hn : z ∈ P ʻʻ A
      · exact hzA (hA.2 ⟨hn, ⟨m, hm'.1.1, h1⟩⟩)
      · exact hs'.2 z (b2_str_above hc hA.1 ⟨s, Or.inl h2⟩ hzA hn) h2

/-- ✱215·33. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .&\alpha \in \text{str}ʻP.\text{E}!\text{prec}_{P}ʻ\alpha .\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\\ &\alpha =P(\text{prec}_{P}ʻ\alpha -\text{seq}_{P}ʻ\alpha ) \quad[*206·22.*215·1]\end{align}\] -/
theorem pm215_33 {P : α → α → Prop} {A : Set α}
    (h : ((P ∈ transR ∩ connex ∧ A ∈ str P) ∧ EDesc (precP P) A) ∧ EDesc (seqP P) A) :
    Desc (precP P) A (fun p => Desc (seqP P) A (fun s => A = itvOO P p s)) := by
  obtain ⟨⟨⟨⟨ht, hc⟩, hA⟩, ⟨p, hp⟩⟩, ⟨s, hs⟩⟩ := h
  have hp' : precP P p A := (hp p).2 rfl
  have hs' : seqP P s A := (hs s).2 rfl
  rw [b2_desc_of_refs (b2_refs_eq_of hp), b2_desc_of_refs (b2_refs_eq_of hs)]
  rw [precP_iff] at hp'
  rw [seqP_iff] at hs'
  ext z
  rw [b2_mem_itvOO ht]
  constructor
  · intro hz
    have hzf := hA.1 hz
    exact ⟨hp'.1.1 z ⟨hz, hzf⟩, hs'.1.1 z ⟨hz, hzf⟩⟩
  · rintro ⟨h1, h2⟩
    by_contra hzA
    have hzf : z ∈ fld P := ⟨s, Or.inl h2⟩
    by_cases hn : z ∈ P ʻʻ A
    · by_cases hn' : z ∈ P˘ ʻʻ A
      · exact hzA (hA.2 ⟨hn, hn'⟩)
      · have hA' : A ⊆ fld P˘ := by rw [fld_cnv]; exact hA.1
        have := b2_str_above (P := P˘) (b2_cnv_connex hc) hA' (by rw [fld_cnv]; exact hzf) hzA hn'
        exact hp'.2 z (fun y hy => this y ⟨hy.1, by rw [fld_cnv]; exact hy.2⟩) h1
    · exact hs'.2 z (b2_str_above hc hA.1 hzf hzA hn) h2

/-- Disjoint non-null stretches of a connected relation: `P_cl` and `P_lc` both say that the
first wholly precedes the second. -/
private theorem b2_before {P : α → α → Prop} (hc : P ∈ connex) {A B : Set α} (hA : A ∈ str P)
    (hB : B ∈ str P) (hAne : A.Nonempty) (hBne : B.Nonempty) (hd : A ∩ B = Λ) :
    (Pcl P A B ↔ ∀ a b, a ∈ A → b ∈ B → P a b) ∧ (Plc P A B ↔ ∀ a b, a ∈ A → b ∈ B → P a b) := by
  have hdis : ∀ z, z ∈ A → z ∈ B → False := fun z h1 h2 => by
    have : z ∈ A ∩ B := ⟨h1, h2⟩
    rw [hd, Null_eq_empty] at this; exact this
  have e1 : A \ B = A := Set.ext fun z => ⟨fun h => h.1, fun h => ⟨h, hdis z h⟩⟩
  have e2 : B \ A = B := Set.ext fun z => ⟨fun h => h.1, fun h => ⟨h, fun h' => hdis z h' h⟩⟩
  have H3 := pm215_3 ⟨⟨hc, b2_mem_diff_iotaNull.2 ⟨hA, hAne⟩, b2_mem_diff_iotaNull.2 ⟨hB, hBne⟩⟩, hd⟩
  have all1 : B ⊆ P˘ ʻʻ A → ∀ a b, a ∈ A → b ∈ B → P a b := fun h a b ha hb =>
    mem_prodCls_Rbwd.1 ((H3.2.2 h) hb) a ha
  have all2 : A ⊆ P ʻʻ B → ∀ a b, a ∈ A → b ∈ B → P a b := fun h a b ha hb =>
    mem_prodCls_Rfwd.1 ((H3.1.1.1 h) ha) b hb
  constructor
  · show ((A ∈ cl (fld P) ∧ B ∈ cl (fld P)) ∧ ((A \ B) \ P˘ ʻʻ (B \ A)).Nonempty) ↔ _
    rw [e1, e2]
    constructor
    · rintro ⟨-, a0, ha0, hn⟩
      refine all1 fun b hb => ⟨a0, ha0, ?_⟩
      rcases mem_connex.1 hc a0 b ⟨hA.1 ha0, hB.1 hb⟩ with (h1 | rfl) | h1
      · exact h1
      · exact (hdis _ ha0 hb).elim
      · exact absurd ⟨b, hb, h1⟩ hn
    · intro H
      obtain ⟨a, ha⟩ := hAne
      refine ⟨⟨hA.1, hB.1⟩, a, ha, ?_⟩
      rintro ⟨b, hb, hba⟩
      exact hdis a ha (b2_str_P hB (H a b ha hb) hb hba hb)
  · show ((B ∈ cl (fld P˘) ∧ A ∈ cl (fld P˘)) ∧ ((B \ A) \ P˘˘ ʻʻ (A \ B)).Nonempty) ↔ _
    rw [e1, e2, fld_cnv]
    constructor
    · rintro ⟨-, b0, hb0, hn⟩
      refine all2 fun a ha => ⟨b0, hb0, ?_⟩
      rcases mem_connex.1 hc a b0 ⟨hA.1 ha, hB.1 hb0⟩ with (h1 | rfl) | h1
      · exact h1
      · exact (hdis _ ha hb0).elim
      · exact absurd ⟨a, ha, h1⟩ hn
    · intro H
      obtain ⟨b, hb⟩ := hBne
      refine ⟨⟨hB.1, hA.1⟩, b, hb, ?_⟩
      rintro ⟨a, ha, hba⟩
      exact hdis b (b2_str_P hA hba ha (H a b ha hb) ha) hb

private theorem b2_clExcl {P : α → α → Prop} {M : Set (Set α)} (hM : M ∈ clExcl (str P \ ι Λ))
    {X : Set α} (hX : X ∈ M) : X ∈ str P ∧ X.Nonempty :=
  b2_mem_diff_iotaNull.1 (hM.2 hX)

private theorem b2_clExcl_disj {P : α → α → Prop} {M : Set (Set α)} (hM : M ∈ clExcl (str P \ ι Λ))
    {X Y : Set α} (hX : X ∈ M) (hY : Y ∈ M) (hne : X ≠ Y) : X ∩ Y = Λ :=
  hM.1 X Y ⟨⟨hX, hY⟩, hne⟩

private theorem b2_Pcl_self {P : α → α → Prop} {X : Set α} : ¬Pcl P X X := by
  rintro ⟨-, z, ⟨hz, hz'⟩, -⟩; exact hz' hz

private theorem b2_Plc_self {P : α → α → Prop} {X : Set α} : ¬Plc P X X := by
  rintro ⟨-, z, ⟨hz, hz'⟩, -⟩; exact hz' hz

/-- ✱215·4. \(\vdash :P\in \text{connex} .\mu \in \text{Cl excl}ʻ(\text{str}ʻP-\iota ʻ\Lambda ).\supset .P_{\text{cl}}\unicode{x0294f}\mu =P_{\text{lc}}\unicode{x0294f}\mu \) -/
theorem pm215_4 {P : α → α → Prop} {M : Set (Set α)}
    (h : P ∈ connex ∧ M ∈ clExcl (str P \ ι Λ)) : Pcl P ⥏ M = Plc P ⥏ M := by
  obtain ⟨hc, hM⟩ := h
  funext X Y; apply propext
  show ((X ∈ M ∧ Pcl P X Y) ∧ Y ∈ M) ↔ ((X ∈ M ∧ Plc P X Y) ∧ Y ∈ M)
  constructor
  · rintro ⟨⟨hX, h1⟩, hY⟩
    by_cases e : X = Y
    · subst e; exact absurd h1 b2_Pcl_self
    obtain ⟨hXs, hXn⟩ := b2_clExcl hM hX
    obtain ⟨hYs, hYn⟩ := b2_clExcl hM hY
    have B := b2_before hc hXs hYs hXn hYn (b2_clExcl_disj hM hX hY e)
    exact ⟨⟨hX, B.2.2 (B.1.1 h1)⟩, hY⟩
  · rintro ⟨⟨hX, h1⟩, hY⟩
    by_cases e : X = Y
    · subst e; exact absurd h1 b2_Plc_self
    obtain ⟨hXs, hXn⟩ := b2_clExcl hM hX
    obtain ⟨hYs, hYn⟩ := b2_clExcl hM hY
    have B := b2_before hc hXs hYs hXn hYn (b2_clExcl_disj hM hX hY e)
    exact ⟨⟨hX, B.1.2 (B.2.1 h1)⟩, hY⟩

/-- For disjoint stretches, one precedes the other (connex), via a single pair. -/
private theorem b2_str_order {P : α → α → Prop} (hc : P ∈ connex) {X Y : Set α} (hX : X ∈ str P)
    (hY : Y ∈ str P) (hXn : X.Nonempty) (hYn : Y.Nonempty) (hd : X ∩ Y = Λ) :
    (∀ a b, a ∈ X → b ∈ Y → P a b) ∨ (∀ a b, a ∈ Y → b ∈ X → P a b) := by
  have hdis : ∀ z, z ∈ X → z ∈ Y → False := fun z h1 h2 => by
    have : z ∈ X ∩ Y := ⟨h1, h2⟩
    rw [hd, Null_eq_empty] at this; exact this
  have hd' : Y ∩ X = Λ := by rw [Set.inter_comm]; exact hd
  obtain ⟨a, ha⟩ := hXn
  obtain ⟨b, hb⟩ := hYn
  have H := pm215_3 ⟨⟨hc, b2_mem_diff_iotaNull.2 ⟨hX, a, ha⟩,
    b2_mem_diff_iotaNull.2 ⟨hY, b, hb⟩⟩, hd⟩
  have H' := pm215_3 ⟨⟨hc, b2_mem_diff_iotaNull.2 ⟨hY, b, hb⟩,
    b2_mem_diff_iotaNull.2 ⟨hX, a, ha⟩⟩, hd'⟩
  rcases mem_connex.1 hc a b ⟨hX.1 ha, hY.1 hb⟩ with (h1 | rfl) | h1
  · left
    have : X ⊆ P ʻʻ Y := by
      intro a' ha'
      rcases mem_connex.1 hc a' b ⟨hX.1 ha', hY.1 hb⟩ with (h2 | rfl) | h2
      · exact ⟨b, hb, h2⟩
      · exact (hdis _ ha' hb).elim
      · exact (hdis b (b2_str_P hX h2 ha' h1 ha) hb).elim
    exact fun a' b' ha' hb' => mem_prodCls_Rfwd.1 (H.1.1.1 this ha') b' hb'
  · exact (hdis _ ha hb).elim
  · right
    have : Y ⊆ P ʻʻ X := by
      intro b' hb'
      rcases mem_connex.1 hc b' a ⟨hY.1 hb', hX.1 ha⟩ with (h2 | rfl) | h2
      · exact ⟨a, ha, h2⟩
      · exact (hdis _ ha hb').elim
      · exact (hdis a ha (b2_str_P hY h2 hb' h1 hb)).elim
    exact fun a' b' ha' hb' => mem_prodCls_Rfwd.1 (H'.1.1.1 this ha') b' hb'

private theorem b2_Plc_M {P : α → α → Prop} {M : Set (Set α)} (hc : P ∈ connex)
    (hM : M ∈ clExcl (str P \ ι Λ)) {X Y : Set α} :
    (Plc P ⥏ M) X Y ↔ (X ∈ M ∧ Y ∈ M) ∧ X ≠ Y ∧ ∀ a b, a ∈ X → b ∈ Y → P a b := by
  show ((X ∈ M ∧ Plc P X Y) ∧ Y ∈ M) ↔ _
  constructor
  · rintro ⟨⟨hX, h1⟩, hY⟩
    have e : X ≠ Y := by rintro rfl; exact b2_Plc_self h1
    obtain ⟨hXs, hXn⟩ := b2_clExcl hM hX
    obtain ⟨hYs, hYn⟩ := b2_clExcl hM hY
    exact ⟨⟨hX, hY⟩, e, (b2_before hc hXs hYs hXn hYn (b2_clExcl_disj hM hX hY e)).2.1 h1⟩
  · rintro ⟨⟨hX, hY⟩, e, H⟩
    obtain ⟨hXs, hXn⟩ := b2_clExcl hM hX
    obtain ⟨hYs, hYn⟩ := b2_clExcl hM hY
    exact ⟨⟨hX, (b2_before hc hXs hYs hXn hYn (b2_clExcl_disj hM hX hY e)).2.2 H⟩, hY⟩

/-- ✱215·41. \(\vdash :P\in \text{trans} \cap \text{connex} .\mu \in \text{Cl excl}ʻ(\text{str}ʻP-\iota ʻ\Lambda ).\supset .P_{\text{lc}}\unicode{x0294f}\mu \in \text{Ser}\) -/
theorem pm215_41 {P : α → α → Prop} {M : Set (Set α)}
    (h : P ∈ transR ∩ connex ∧ M ∈ clExcl (str P \ ι Λ)) : Plc P ⥏ M ∈ Ser := by
  obtain ⟨⟨ht, hc⟩, hM⟩ := h
  have tr := mem_transR.1 ht
  rw [mem_Ser]
  refine ⟨⟨fun X hX => ?_, fun X Y Z ⟨h1, h2⟩ => ?_⟩, fun X Y ⟨hX, hY⟩ => ?_⟩
  · exact ((b2_Plc_M hc hM).1 hX).2.1 rfl
  · obtain ⟨⟨hX, hY⟩, eXY, H1⟩ := (b2_Plc_M hc hM).1 h1
    obtain ⟨⟨-, hZ⟩, eYZ, H2⟩ := (b2_Plc_M hc hM).1 h2
    obtain ⟨y, hy⟩ := (b2_clExcl hM hY).2
    obtain ⟨hXs, hXn⟩ := b2_clExcl hM hX
    have eXZ : X ≠ Z := by
      rintro rfl
      obtain ⟨a, ha⟩ := hXn
      have hd := b2_clExcl_disj hM hX hY eXY
      have : y ∈ X := b2_str_P hXs (H2 y a hy ha) ha (H1 a y ha hy) ha
      have : y ∈ X ∩ Y := ⟨this, hy⟩
      rw [hd, Null_eq_empty] at this; exact this
    exact (b2_Plc_M hc hM).2 ⟨⟨hX, hZ⟩, eXZ, fun a c ha hc' => tr a y c ⟨H1 a y ha hy, H2 y c hy hc'⟩⟩
  · have hXM : X ∈ M := by
      obtain ⟨W, hW | hW⟩ := hX
      · exact hW.1.1
      · exact hW.2
    have hYM : Y ∈ M := by
      obtain ⟨W, hW | hW⟩ := hY
      · exact hW.1.1
      · exact hW.2
    by_cases e : X = Y
    · exact Or.inl (Or.inr e)
    obtain ⟨hXs, hXn⟩ := b2_clExcl hM hXM
    obtain ⟨hYs, hYn⟩ := b2_clExcl hM hYM
    rcases b2_str_order hc hXs hYs hXn hYn (b2_clExcl_disj hM hXM hYM e) with H | H
    · exact Or.inl (Or.inl ((b2_Plc_M hc hM).2 ⟨⟨hXM, hYM⟩, e, H⟩))
    · exact Or.inr ((b2_Plc_M hc hM).2 ⟨⟨hYM, hXM⟩, Ne.symm e, H⟩)

/-- ✱215·42. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .\mu \in \text{Cl excl}ʻ(\text{str}ʻP-{℩}ʻ\Lambda ).\mu {\sim}\in 1.\supset .CʻP_{\text{lc}}\unicode{x0294f}\mu =\mu \\ &[*202·55.*215·41]\end{align}\] -/
theorem pm215_42 {P : α → α → Prop} {M : Set (Set α)}
    (h : (P ∈ transR ∩ connex ∧ M ∈ clExcl (str P \ ι Λ)) ∧ M ∉ (one : Set (Set (Set α)))) :
    fld (Plc P ⥏ M) = M := by
  obtain ⟨⟨⟨ht, hc⟩, hM⟩, h1⟩ := h
  ext X
  constructor
  · rintro ⟨W, hW | hW⟩
    · exact hW.1.1
    · exact hW.2
  · intro hX
    have : ∃ Y, Y ∈ M ∧ Y ≠ X := by
      by_contra hn; push Not at hn
      exact h1 ⟨X, Set.ext fun Y => ⟨fun hY => hn Y hY, fun hY => (b2_mem_iota.1 hY) ▸ hX⟩⟩
    obtain ⟨Y, hY, e⟩ := this
    obtain ⟨hXs, hXn⟩ := b2_clExcl hM hX
    obtain ⟨hYs, hYn⟩ := b2_clExcl hM hY
    rcases b2_str_order hc hXs hYs hXn hYn (b2_clExcl_disj hM hX hY (Ne.symm e)) with H | H
    · exact ⟨Y, Or.inl ((b2_Plc_M hc hM).2 ⟨⟨hX, hY⟩, Ne.symm e, H⟩)⟩
    · exact ⟨Y, Or.inr ((b2_Plc_M hc hM).2 ⟨⟨hY, hX⟩, e, H⟩)⟩

/-- `limin_P'β = limin_P'(α ∩ β)` under the hypothesis of ✱215·162. -/
private theorem b2_164_limin {P : α → α → Prop} {A B : Set α} (ht : P ∈ transR) (hc : P ∈ connex)
    (hA : A ∈ sect P) (hB : B ∈ sect P˘) (hne : (A ∩ B).Nonempty) :
    refs (liminP P) B = refs (liminP P) (A ∩ B) := by
  have hBA : (B ∩ A).Nonempty := by rw [Set.inter_comm]; exact hne
  have := (pm215_164 (P := P˘) ⟨⟨⟨⟨b2_trans_cnv ht, b2_cnv_connex hc⟩, hB⟩,
    by rw [b2_cnv_cnv]; exact hA⟩, hBA⟩).2
  rw [Set.inter_comm B A] at this
  rw [liminP_eq_limaxP_cnv]; exact this

private theorem b2_limax_164 {P : α → α → Prop} {A B : Set α} (ht : P ∈ transR) (hc : P ∈ connex)
    (hA : A ∈ sect P) (hB : B ∈ sect P˘) (hne : (A ∩ B).Nonempty) :
    refs (limaxP P) A = refs (limaxP P) (A ∩ B) :=
  (pm215_164 ⟨⟨⟨⟨ht, hc⟩, hA⟩, hB⟩, hne⟩).2

private theorem b2_desc_pair {β : Type v} {R S : α → β → Prop} {y y' : β} {ψ : α → α → Prop} :
    Desc R y (fun l => Desc S y' (fun l' => ψ l l')) ↔
      ∃ v u, (refs R y = {v} ∧ refs S y' = {u}) ∧ ψ v u := by
  constructor
  · rintro ⟨v, hv, u, hu, h⟩
    exact ⟨v, u, ⟨b2_refs_eq_of hv, b2_refs_eq_of hu⟩, h⟩
  · rintro ⟨v, u, ⟨hv, hu⟩, h⟩
    rw [b2_desc_of_refs hv, b2_desc_of_refs hu]; exact h

/-- ✱215·5. \[\begin{align}&\vdash \colon\ldotp P\in \text{trans}\cap \text{connex} .\alpha \in \text{sect}ʻP.\beta \in \text{sect}ʻ\breve{P} .\supset :\\ &\exists !\alpha \cap \beta .\text{limax}_Pʻ\alpha =\text{limin}_Pʻ\beta .\supset .\alpha \cap \beta \in 1 \quad[*207·71.*215·164]\end{align}\] -/
theorem pm215_5 {P : α → α → Prop} {A B : Set α}
    (h : (P ∈ transR ∩ connex ∧ A ∈ sect P) ∧ B ∈ sect P˘) :
    (A ∩ B).Nonempty ∧ Desc (limaxP P) A (fun l => Desc (liminP P) B (fun l' => l = l')) →
      A ∩ B ∈ (one : Set (Set α)) := by
  obtain ⟨⟨⟨ht, hc⟩, hA⟩, hB⟩ := h
  have tr := mem_transR.1 ht
  rintro ⟨hne, hD⟩
  obtain ⟨v, u, ⟨hv, hu⟩, rfl⟩ := b2_desc_pair.1 hD
  rw [b2_limax_164 ht hc hA hB hne] at hv
  rw [b2_164_limin ht hc hA hB hne] at hu
  have hvX : limaxP P v (A ∩ B) := b2_mem_of_refs_eq hv
  have huX : liminP P v (A ∩ B) := b2_mem_of_refs_eq hu
  obtain ⟨c, hc'⟩ := hne
  refine ⟨c, Set.ext fun d => ⟨fun hd => ?_, fun hd => (b2_mem_iota.1 hd) ▸ hc'⟩⟩
  rw [b2_mem_iota]
  by_contra hdc
  set X := A ∩ B
  have hXf : X ⊆ fld P := fun z hz => hA.1 hz.1
  -- WLOG `x P y` for two distinct members
  have main : ∀ x y, x ∈ X → y ∈ X → P x y → False := by
    intro x y hx hy hxy
    rcases hvX with hmax | ⟨hseq, hnm⟩ <;> rcases huX with hmin | ⟨hprec, hnn⟩
    · rw [maxP_iff] at hmax
      rw [minP_iff] at hmin
      rcases mem_connex.1 hc v x ⟨hmax.1.2, hXf hx⟩ with (h1 | rfl) | h1
      · exact hmax.2 x hx h1
      · exact hmax.2 y hy hxy
      · exact hmin.2 x hx h1
    · rw [maxP_iff] at hmax
      rw [precP_iff] at hprec
      exact hmax.2 x hx (hprec.1.1 x ⟨hx, hXf hx⟩)
    · rw [seqP_iff] at hseq
      rw [minP_iff] at hmin
      exact hmin.2 x hx (hseq.1.1 x ⟨hx, hXf hx⟩)
    · rw [seqP_iff] at hseq
      rw [precP_iff] at hprec
      have h1 := hprec.1.1 x ⟨hx, hXf hx⟩
      have h2 := hseq.1.1 y ⟨hy, hXf hy⟩
      exact hseq.2 v hseq.1.1 (tr v y v ⟨tr v x y ⟨h1, hxy⟩, h2⟩)
  rcases mem_connex.1 hc d c ⟨hXf hd, hXf hc'⟩ with (h1 | h1) | h1
  · exact main d c hd hc' h1
  · exact hdc h1
  · exact main c d hc' hd h1

/-- Unique maximum and minimum when `α ∩ β` is a unit class (from ✱215·166). -/
private theorem b2_166 {P : α → α → Prop} {A B : Set α} (hs : po P ∈ Ser) (hA : A ∈ sect P)
    (hB : B ∈ sect P˘) {c : α} (hc : A ∩ B = ι c) :
    refs (maxP P) A = {c} ∧ refs (minP P) B = {c} := by
  have hJ := (b2_serPo hs).1
  have hcAB : c ∈ A ∩ B := hc ▸ rfl
  have hcf : c ∈ fld P := hA.1 hcAB.1
  have hmax : maxP P c A := by
    rw [maxP_iff]
    refine ⟨⟨hcAB.1, hcf⟩, fun y hy hcy => ?_⟩
    have : y ∈ A ∩ B := ⟨hy, b2_cnv_sect_mem hB hcy hcAB.2⟩
    rw [hc, b2_mem_iota] at this
    subst this; exact b2_irrP hJ hcy
  have hmin : minP P c B := by
    rw [minP_iff]
    refine ⟨⟨hcAB.2, hcf⟩, fun y hy hyc => ?_⟩
    have : y ∈ A ∩ B := ⟨b2_sect_P hA hyc hcAB.1, hy⟩
    rw [hc, b2_mem_iota] at this
    subst this; exact b2_irrP hJ hyc
  constructor
  · refine b2_refs_single hmax fun m hm => ?_
    rw [maxP_iff] at hm
    rcases (b2_serPo hs).2 m c hm.1.2 hcf with (h' | rfl) | h'
    · obtain ⟨v, hmv, hvc⟩ := b2_po_head h'
      exact absurd hmv (hm.2 v (b2_sect_anc hA hvc hcAB.1))
    · rfl
    · have : m ∈ A ∩ B := ⟨hm.1.1, b2_sect_po_cnv hB h' hcAB.2⟩
      rw [hc, b2_mem_iota] at this; exact this
  · refine b2_refs_single hmin fun m hm => ?_
    rw [minP_iff] at hm
    rcases (b2_serPo hs).2 m c hm.1.2 hcf with (h' | rfl) | h'
    · have : m ∈ A ∩ B := ⟨b2_sect_po hA h' hcAB.1, hm.1.1⟩
      rw [hc, b2_mem_iota] at this; exact this
    · rfl
    · obtain ⟨v, hcv, hvm⟩ := b2_po_tail h'
      have hv : v ∈ B := by
        rcases anc_iff_po.1 hcv with ⟨rfl, -⟩ | h''
        · exact hcAB.2
        · exact b2_sect_po_cnv hB h'' hcAB.2
      exact absurd hvm (hm.2 v hv)

private theorem b2_limax_of_max {P : α → α → Prop} {A : Set α} {c : α} (h : refs (maxP P) A = {c}) :
    refs (limaxP P) A = {c} := by
  have hm : maxP P c A := b2_mem_of_refs_eq h
  ext x
  show maxP P x A ∨ (seqP P x A ∧ A ∈ (codom (maxP P))ᶜ) ↔ x = c
  constructor
  · rintro (h' | ⟨-, hn⟩)
    · exact (h ▸ h' : x ∈ ({c} : Set α))
    · exact absurd ⟨c, hm⟩ hn
  · rintro rfl; exact Or.inl hm

private theorem b2_limin_of_min {P : α → α → Prop} {B : Set α} {c : α} (h : refs (minP P) B = {c}) :
    refs (liminP P) B = {c} := by
  rw [liminP_eq_limaxP_cnv]; exact b2_limax_of_max (P := P˘) h

/-- ✱215·51. \[\begin{align}\vdash :P\in \text{Ser}.\alpha \in &\text{sect}ʻP.\beta \in \text{sect}ʻ\breve{P} .\alpha \cap \beta \in 1.\supset .\\ &\text{limax}_Pʻ\alpha =\text{limin}_Pʻ\beta =\breve{{℩}} ʻ(\alpha \cap \beta ) \quad[*207·72.*215·164]\end{align}\] -/
theorem pm215_51 {P : α → α → Prop} {A B : Set α}
    (h : ((P ∈ Ser ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ A ∩ B ∈ (one : Set (Set α))) :
    Desc (limaxP P) A (fun l => Desc (liminP P) B (fun l' => l = l')) ∧
      Desc (liminP P) B (fun l' => Desc iota˘ (A ∩ B) (fun c => l' = c)) := by
  obtain ⟨⟨⟨hs, hA⟩, hB⟩, c, hc⟩ := h
  obtain ⟨e1, e2⟩ := b2_166 (b2_ser_po hs) hA hB hc
  have l1 := b2_limax_of_max e1
  have l2 := b2_limin_of_min e2
  rw [b2_desc_of_refs l1, b2_desc_of_refs l2, b2_desc_of_refs l2, desc_iota_cnv, hc]
  refine ⟨rfl, c, fun x => Iff.rfl, rfl⟩

/-- ✱215·52. \[\begin{align}\vdash :\text{Hp}*215·5.\alpha \cap \beta {\sim}\in 0\cup 1.\text{E}!\text{limax}_Pʻ\alpha .\text{E}!&\text{limin}_Pʻ\beta .\supset .\\ &\text{limin}_Pʻ\beta P\text{limax}_Pʻ\alpha\end{align}\] -/
theorem pm215_52 {P : α → α → Prop} {A B : Set α}
    (h : ((((P ∈ transR ∩ connex ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧
      A ∩ B ∉ (zero : Set (Set α)) ∪ one) ∧ EDesc (limaxP P) A) ∧ EDesc (liminP P) B) :
    Desc (liminP P) B (fun l' => Desc (limaxP P) A (fun l => P l' l)) := by
  obtain ⟨h, hEu⟩ := h
  obtain ⟨h, hEv⟩ := h
  obtain ⟨⟨⟨⟨ht, hc⟩, hA⟩, hB⟩, h01⟩ := h
  have tr := mem_transR.1 ht
  have hne : (A ∩ B).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro e; exact h01 (Or.inl (by rw [e]; exact b2_mem_iotaNull.2 rfl))
  obtain ⟨v, hv⟩ := b2_EDesc_iff.1 hEv
  obtain ⟨u, hu⟩ := b2_EDesc_iff.1 hEu
  rw [b2_desc_of_refs hu, b2_desc_of_refs hv]
  rw [b2_limax_164 ht hc hA hB hne] at hv
  rw [b2_164_limin ht hc hA hB hne] at hu
  have hvX : limaxP P v (A ∩ B) := b2_mem_of_refs_eq hv
  have huX : liminP P u (A ∩ B) := b2_mem_of_refs_eq hu
  set X := A ∩ B
  have hXf : X ⊆ fld P := fun z hz => hA.1 hz.1
  obtain ⟨c, hcX⟩ := hne
  have : ∃ d, d ∈ X ∧ d ≠ c := by
    by_contra hn; push Not at hn
    exact h01 (Or.inr ⟨c, Set.ext fun z => ⟨fun hz => hn z hz,
      fun hz => (b2_mem_iota.1 hz) ▸ hcX⟩⟩)
  obtain ⟨d, hdX, hdc⟩ := this
  have pair : ∀ x y, x ∈ X → y ∈ X → P x y → P u v := by
    intro x y hx hy hxy
    have hu' : u = x ∨ P u x := by
      rcases huX with hmin | ⟨hprec, -⟩
      · rw [minP_iff] at hmin
        rcases mem_connex.1 hc u x ⟨hmin.1.2, hXf hx⟩ with (h1 | h1) | h1
        · exact Or.inr h1
        · exact Or.inl h1
        · exact absurd h1 (hmin.2 x hx)
      · exact Or.inr ((precP_iff.1 hprec).1.1 x ⟨hx, hXf hx⟩)
    have hv' : y = v ∨ P y v := by
      rcases hvX with hmax | ⟨hseq, -⟩
      · rw [maxP_iff] at hmax
        rcases mem_connex.1 hc y v ⟨hXf hy, hmax.1.2⟩ with (h1 | h1) | h1
        · exact Or.inr h1
        · exact Or.inl h1
        · exact absurd h1 (hmax.2 y hy)
      · exact Or.inr ((seqP_iff.1 hseq).1.1 y ⟨hy, hXf hy⟩)
    rcases hu' with rfl | h1 <;> rcases hv' with rfl | h2
    · exact hxy
    · exact tr u y v ⟨hxy, h2⟩
    · exact tr u x y ⟨h1, hxy⟩
    · exact tr u y v ⟨tr u x y ⟨h1, hxy⟩, h2⟩
  rcases mem_connex.1 hc c d ⟨hXf hcX, hXf hdX⟩ with (h1 | h1) | h1
  · exact pair c d hcX hdX h1
  · exact absurd h1.symm hdc
  · exact pair d c hdX hcX h1

/-- ✱215·53. \[\begin{align}\vdash :\text{Hp}*215·5.\alpha \cap \beta =\Lambda .\text{E}!\text{limax}_Pʻ\alpha .\text{E}!&\text{limin}_Pʻ\beta .\supset .\\ &\text{limax}_Pʻ\alpha P_{*}\text{limin}_Pʻ\beta\end{align}\] -/
theorem pm215_53 {P : α → α → Prop} {A B : Set α}
    (h : ((((P ∈ transR ∩ connex ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ A ∩ B = Λ) ∧
      EDesc (limaxP P) A) ∧ EDesc (liminP P) B) :
    Desc (limaxP P) A (fun l => Desc (liminP P) B (fun l' => anc P l l')) := by
  obtain ⟨h, hEu⟩ := h
  obtain ⟨h, hEv⟩ := h
  obtain ⟨⟨⟨⟨ht, hc⟩, hA⟩, hB⟩, hd⟩ := h
  have tr := mem_transR.1 ht
  obtain ⟨v, hv⟩ := b2_EDesc_iff.1 hEv
  obtain ⟨u, hu⟩ := b2_EDesc_iff.1 hEu
  rw [b2_desc_of_refs hv, b2_desc_of_refs hu, anc_iff_of_transR ht]
  have hvA : limaxP P v A := b2_mem_of_refs_eq hv
  have huB : liminP P u B := b2_mem_of_refs_eq hu
  have hBf : B ⊆ fld P := by have := hB.1; rwa [fld_cnv] at this
  have hdis : ∀ z, z ∈ A → z ∈ B → False := fun z h1 h2 => by
    have : z ∈ A ∩ B := ⟨h1, h2⟩
    rw [hd, Null_eq_empty] at this; exact this
  have ab : ∀ a b, a ∈ A → b ∈ B → P a b := by
    intro a b ha hb
    rcases mem_connex.1 hc a b ⟨hA.1 ha, hBf hb⟩ with (h1 | rfl) | h1
    · exact h1
    · exact (hdis _ ha hb).elim
    · exact (hdis b (b2_sect_P hA h1 ha) hb).elim
  have hvf : v ∈ fld P := by
    rcases hvA with h1 | ⟨h1, -⟩
    · exact (maxP_iff.1 h1).1.2
    · exact (seqP_iff.1 h1).1.2
  have huf : u ∈ fld P := by
    rcases huB with h1 | ⟨h1, -⟩
    · exact (minP_iff.1 h1).1.2
    · exact (precP_iff.1 h1).1.2
  have hn : ¬P u v := by
    intro huv
    rcases hvA with hmax | ⟨hseq, hnm⟩ <;> rcases huB with hmin | ⟨hprec, hnn⟩
    · exact hdis u (b2_sect_P hA huv (maxP_iff.1 hmax).1.1) (minP_iff.1 hmin).1.1
    · rw [maxP_iff] at hmax
      rw [precP_iff] at hprec
      exact hprec.2 v (fun b hb => ab v b hmax.1.1 hb.1) huv
    · rw [seqP_iff] at hseq
      rw [minP_iff] at hmin
      exact hseq.2 u (fun a ha => ab a u ha.1 hmin.1.1) huv
    · rw [seqP_iff] at hseq
      rw [precP_iff] at hprec
      by_cases huA : u ∈ A
      · have : ¬maxP P u A := fun hm => hnm ⟨u, hm⟩
        rw [maxP_iff] at this
        push Not at this
        obtain ⟨a', ha', hua'⟩ := this ⟨huA, huf⟩
        exact hprec.2 a' (fun b hb => ab a' b ha' hb.1) hua'
      · refine hseq.2 u (fun a ha => ?_) huv
        rcases mem_connex.1 hc a u ⟨ha.2, huf⟩ with (h1 | rfl) | h1
        · exact h1
        · exact absurd ha.1 huA
        · exact absurd (b2_sect_P hA h1 ha.1) huA
  rcases mem_connex.1 hc v u ⟨hvf, huf⟩ with (h1 | h1) | h1
  · exact Or.inr h1
  · exact Or.inl ⟨h1, hvf⟩
  · exact absurd h1 hn

private theorem b2_ser_tc {P : α → α → Prop} (h : P ∈ Ser) : P ∈ transR ∩ connex := ⟨h.1.2, h.2⟩

/-- ✱215·54. \[\begin{align}\vdash :P&\in \text{Ser}.\alpha \in \text{sect}ʻP.\beta \in \text{sect}ʻ\breve{P} .\alpha \cap \beta =\Lambda .\alpha \cup \beta =CʻP.\\ &\text{E}!\text{limax}_Pʻ\alpha .\text{E}!\text{limin}_Pʻ\beta .\supset :\text{limax}_Pʻ\alpha =\text{limin}_Pʻ\beta .\lor.\\ &\text{limax}_Pʻ\alpha P_{1}\text{limin}_Pʻ\beta\end{align}\] -/
theorem pm215_54 {P : α → α → Prop} {A B : Set α}
    (h : (((((P ∈ Ser ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ A ∩ B = Λ) ∧ A ∪ B = fld P) ∧
      EDesc (limaxP P) A) ∧ EDesc (liminP P) B) :
    Desc (limaxP P) A (fun l => Desc (liminP P) B (fun l' => l = l')) ∨
      Desc (limaxP P) A (fun l => Desc (liminP P) B (fun l' => P1 P l l')) := by
  obtain ⟨h, hEu⟩ := h
  obtain ⟨h, hEv⟩ := h
  obtain ⟨⟨⟨⟨hs, hA⟩, hB⟩, hd⟩, hU⟩ := h
  have tr := mem_transR.1 hs.1.2
  have hirr := b2_irr_of_ser hs
  have H := pm215_53 ⟨⟨⟨⟨⟨b2_ser_tc hs, hA⟩, hB⟩, hd⟩, hEv⟩, hEu⟩
  obtain ⟨v, u, ⟨hv, hu⟩, hvu⟩ := b2_desc_pair.1 H
  have hvA : limaxP P v A := b2_mem_of_refs_eq hv
  have huB : liminP P u B := b2_mem_of_refs_eq hu
  rw [anc_iff_of_transR hs.1.2] at hvu
  rcases hvu with ⟨rfl, -⟩ | hvu
  · left; exact b2_desc_pair.2 ⟨v, v, ⟨hv, hu⟩, rfl⟩
  · right
    refine b2_desc_pair.2 ⟨v, u, ⟨hv, hu⟩, (P1_iff_of_transR hs.1.2 hs.1.1).2 ⟨hvu, ?_⟩⟩
    rintro ⟨z, hvz, hzu⟩
    have hz : z ∈ A ∪ B := hU ▸ ⟨u, Or.inl hzu⟩
    rcases hz with hz | hz
    · rcases hvA with hmax | ⟨hseq, -⟩
      · exact (maxP_iff.1 hmax).2 z hz hvz
      · exact hirr v (tr v z v ⟨hvz, (seqP_iff.1 hseq).1.1 z ⟨hz, ⟨u, Or.inl hzu⟩⟩⟩)
    · rcases huB with hmin | ⟨hprec, -⟩
      · exact (minP_iff.1 hmin).2 z hz hzu
      · exact hirr u (tr u z u ⟨(precP_iff.1 hprec).1.1 z ⟨hz, ⟨v, Or.inr hvz⟩⟩, hzu⟩)

private theorem b2_EDesc_limax {P : α → α → Prop} (hc : P ∈ connex) {A : Set α} :
    EDesc (limaxP P) A ↔ (∃ m, maxP P m A) ∨ ∃ s, seqP P s A := by
  rw [b2_EDesc_iff]
  constructor
  · rintro ⟨v, hv⟩
    rcases b2_mem_of_refs_eq hv with h1 | ⟨h1, -⟩
    · exact Or.inl ⟨v, h1⟩
    · exact Or.inr ⟨v, h1⟩
  · rintro (⟨m, hm⟩ | ⟨s, hs⟩)
    · exact ⟨m, b2_limax_of_max (b2_refs_single hm fun c hc' => b2_maxP_unique hc hc' hm)⟩
    · by_cases hm : ∃ m, maxP P m A
      · obtain ⟨m, hm⟩ := hm
        exact ⟨m, b2_limax_of_max (b2_refs_single hm fun c hc' => b2_maxP_unique hc hc' hm)⟩
      · refine ⟨s, b2_refs_single (Or.inr ⟨hs, hm⟩) fun c hc' => ?_⟩
        rcases hc' with h1 | ⟨h1, -⟩
        · exact absurd ⟨c, h1⟩ hm
        · exact b2_seqP_unique hc h1 hs

private theorem b2_EDesc_limin {P : α → α → Prop} (hc : P ∈ connex) {B : Set α} :
    EDesc (liminP P) B ↔ (∃ m, minP P m B) ∨ ∃ s, precP P s B := by
  rw [liminP_eq_limaxP_cnv, b2_EDesc_limax (b2_cnv_connex hc), precP_eq_seqP_cnv]
  rfl

/-- ✱215·541. \[\begin{align}&\vdash \colon\colon P\in \text{Ser}.\alpha \in \text{sect}ʻP.\beta \in \text{sect}ʻ\breve{P} .\alpha \cup \beta =CʻP.\supset \colon\ldotp \\ &\alpha \cap \beta \in 0\cup 1.\supset :\text{E}!\text{limax}_Pʻ\alpha .\equiv .\text{E}!\text{limin}_Pʻ\beta \quad[*211·727.*215·51]\end{align}\] -/
theorem pm215_541 {P : α → α → Prop} {A B : Set α}
    (h : ((P ∈ Ser ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ A ∪ B = fld P) :
    A ∩ B ∈ (zero : Set (Set α)) ∪ one → (EDesc (limaxP P) A ↔ EDesc (liminP P) B) := by
  obtain ⟨⟨⟨hs, hA⟩, hB⟩, hU⟩ := h
  rintro (h0 | h1)
  · have hd : A ∩ B = ∅ := b2_mem_iotaNull.1 h0
    have hBf : B ⊆ fld P := by have := hB.1; rwa [fld_cnv] at this
    have eB : B = fld P \ A := by
      ext z
      constructor
      · intro hz; exact ⟨hBf hz, fun hzA => (hd ▸ (⟨hzA, hz⟩ : z ∈ A ∩ B) : z ∈ (∅ : Set α))⟩
      · rintro ⟨hz, hzA⟩
        rw [← hU] at hz
        exact hz.resolve_left hzA
    have eA : A = fld P \ B := by rw [eB, Set.sdiff_sdiff_cancel_left hA.1]
    have hirr := b2_irr_of_ser hs
    rw [b2_EDesc_limax hs.2, b2_EDesc_limin hs.2]
    have e1 : ∀ x, seqP P x A ↔ minP P x B := fun x => by rw [eB]; exact b2_seq_sect hirr hs.2 hA
    have e2 : ∀ x, precP P x B ↔ maxP P x A := fun x => by
      rw [precP_eq_seqP_cnv, b2_seq_sect (P := P˘) hirr (b2_cnv_connex hs.2) hB, fld_cnv, ← eA]
      rfl
    simp only [e1, e2]
    tauto
  · obtain ⟨c, hc⟩ := h1
    have H := pm215_51 ⟨⟨⟨hs, hA⟩, hB⟩, c, hc⟩
    obtain ⟨v, u, ⟨hv, hu⟩, -⟩ := b2_desc_pair.1 H.1
    exact ⟨fun _ => b2_EDesc_iff.2 ⟨u, hu⟩, fun _ => b2_EDesc_iff.2 ⟨v, hv⟩⟩

/-- ✱215·542. \[\begin{align}\vdash :\text{Hp}*215·541.\alpha \cap \beta =&\Lambda .\text{E}!\text{limax}_Pʻ\alpha .\text{limax}_Pʻ\alpha {\sim}\in \text{D}ʻP_{1}.\supset .\\ &\text{limax}_Pʻ\alpha =\text{limin}_Pʻ\beta \quad [*215·54.*211·727]\end{align}\] -/
theorem pm215_542 {P : α → α → Prop} {A B : Set α}
    (h : (((((P ∈ Ser ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ A ∪ B = fld P) ∧ A ∩ B = Λ) ∧
      EDesc (limaxP P) A) ∧ Desc (limaxP P) A (fun l => l ∉ dom (P1 P))) :
    Desc (limaxP P) A (fun l => Desc (liminP P) B (fun l' => l = l')) := by
  obtain ⟨h, hn⟩ := h
  obtain ⟨h, hEv⟩ := h
  obtain ⟨⟨⟨⟨hs, hA⟩, hB⟩, hU⟩, hd⟩ := h
  have hEu : EDesc (liminP P) B :=
    (pm215_541 ⟨⟨⟨hs, hA⟩, hB⟩, hU⟩ (Or.inl (by rw [hd]; exact b2_mem_iota.2 rfl))).1 hEv
  rcases pm215_54 ⟨⟨⟨⟨⟨⟨hs, hA⟩, hB⟩, hd⟩, hU⟩, hEv⟩, hEu⟩ with H | H
  · exact H
  · obtain ⟨v, u, ⟨hv, hu⟩, h1⟩ := b2_desc_pair.1 H
    rw [b2_desc_of_refs hv] at hn
    exact absurd ⟨u, h1⟩ hn

/-- ✱215·543. \[\begin{align}&\vdash :P\in \text{Ser}.\alpha \in \text{sect}ʻP.\beta \in \text{sect}ʻ\breve{P} .\alpha \cup \beta =CʻP.\alpha \cap \beta \in 0\cup 1.\\ &\text{E}!\text{limax}_Pʻ\alpha .\text{limax}_Pʻ\alpha {\sim}\in \text{D}ʻP_{1}.\supset .\text{limax}_Pʻ\alpha =\text{limin}_Pʻ\beta \quad[*215·542·51]\end{align}\] -/
theorem pm215_543 {P : α → α → Prop} {A B : Set α}
    (h : (((((P ∈ Ser ∧ A ∈ sect P) ∧ B ∈ sect P˘) ∧ A ∪ B = fld P) ∧
      A ∩ B ∈ (zero : Set (Set α)) ∪ one) ∧ EDesc (limaxP P) A) ∧
      Desc (limaxP P) A (fun l => l ∉ dom (P1 P))) :
    Desc (limaxP P) A (fun l => Desc (liminP P) B (fun l' => l = l')) := by
  obtain ⟨h, hn⟩ := h
  obtain ⟨h, hEv⟩ := h
  obtain ⟨⟨⟨⟨hs, hA⟩, hB⟩, hU⟩, h01⟩ := h
  rcases h01 with h0 | ⟨c, hc⟩
  · have hd : A ∩ B = Λ := by rw [b2_mem_iotaNull.1 h0, Null_eq_empty]
    exact pm215_542 ⟨⟨⟨⟨⟨⟨hs, hA⟩, hB⟩, hU⟩, hd⟩, hEv⟩, hn⟩
  · exact (pm215_51 ⟨⟨⟨hs, hA⟩, hB⟩, c, hc⟩).1

/-!
## [✱216] Derivatives

*(Vol. 2, p. 700)*

> *Summary of* *216.
>
> If \(\alpha\) is any class, and \(P\) is any series, the *derivative* (or *first derivative*) of \(\alpha\) with respect to \(P\) is the class of limits of existent sub-classes of \(\alpha \cap CʻP\), *i.e.* \(\text{lt}_{p}ʻʻ\text{Cl ex}ʻ(\alpha\cap CʻP)\). That is, a term \(x\) belongs to the derivative of \(\alpha\) if a set of terms exists which is contained both in \(\alpha\) and in \(CʻP\), and has \(x\) for its limit. The derivative of \(\alpha\) with respect to \(P\) will be denoted by \(\delta _{p}ʻ\alpha\).
>
> …

**Lean reading.** `δ_P'α` is `derivCls P A`, `dense'P`, `closed'P`, `perf'P`, `∇'P` are `dense P`, `closed P`,
`perf P`, `nabla P` (Defs/Part5; the e-text's subscript `p` is `P`). `Cl ex'` is `clEx`; `δ(ς'P)`
is `derivCls (segSer P)`. For series, `x ∈ δ_P'α` is characterized pointwise (✱216·13), and
`D'lt_P = C'P − ᗡ'(P −̇ P²)` (✱207·35) is reproved. Likeness `S ∈ P smor̄ Q` transports
maxima, minima, sequents, limits and derivatives (✱216·4–·412). ✱216·14, ·21, ·22 correct e-text
misprints. For ✱216·5–·56, the derivative in the series of segments `ς'P` of a series is
characterized pointwise (✱216·13 applied to `ς'P`, a Dedekindian series by ✱214·33): `Y ∈ δ(ς'P)'κ`
iff `Y` is a non-null segment and between any smaller segment and `Y` lies a member of `κ`.

**Status.** proved; ✱216·01–·05 definition; ✱216·14, ·21, ·22 proved (reading) (e-text misprints).
-/

end S215

section S216

variable {α : Type u}

/-- ✱216·01 (Df). \(\delta _{p}ʻ\alpha =\text{lt}_{p}ʻʻ\text{Cl ex}ʻ(\alpha \cap CʻP)\quad\text{Df}\) -/
theorem pm216_01 {P : α → α → Prop} {A : Set α} :
    derivCls P A = ltP P ʻʻ clEx (A ∩ fld P) := rfl

/-- ✱216·02 (Df). \(\text{dense}ʻP=\hat{\alpha} (\alpha -\overrightarrow{\text{min}}_{p}ʻ\alpha \subset \delta _{p}ʻ\alpha ) \quad\text{Df}\) -/
theorem pm216_02 {P : α → α → Prop} : dense P = {A | A \ refs (minP P) A ⊆ derivCls P A} := rfl

/-- ✱216·03 (Df). \(\text{closed}ʻP=\hat{\alpha} \{\text{Cl ex}ʻ(\alpha \cap CʻP)\subset \text{ᗡ}ʻ\text{limax}_{p}.\delta _{p}ʻ\alpha \subset \alpha\} \quad\text{Df}\) -/
theorem pm216_03 {P : α → α → Prop} :
    closed P = {A | clEx (A ∩ fld P) ⊆ codom (limaxP P) ∧ derivCls P A ⊆ A} := rfl

/-- ✱216·04 (Df). \(\text{perf}ʻP=\text{dense}ʻP\cap \text{closed}ʻP \quad\text{Df}\) -/
theorem pm216_04 {P : α → α → Prop} : perf P = dense P ∩ closed P := rfl

/-- ✱216·05 (Df). \(\nablaʻP=P\unicode{x0294f}\text{D}ʻ\text{lt}_{p} \quad\text{Df}\) -/
theorem pm216_05 {P : α → α → Prop} : nabla P = P ⥏ dom (ltP P) := rfl

/-- ✱216·1. \(\vdash :x\in \delta _{p}ʻ\alpha .\equiv .(\exists \beta ).\beta \subset \alpha \cap CʻP.\exists !\beta .x\text{lt}_{p}\beta \quad[(*216·01)]\) -/
theorem pm216_1 {P : α → α → Prop} {A : Set α} {x : α} :
    x ∈ derivCls P A ↔ ∃ B, (B ⊆ A ∩ fld P ∧ B.Nonempty) ∧ ltP P x B := Iff.rfl

private theorem b2_noMax_iff {P : α → α → Prop} {B : Set α} (hB : B ⊆ fld P) :
    (¬∃ m, maxP P m B) ↔ B ⊆ P ʻʻ B := by
  constructor
  · intro hn b hb
    by_contra hb'
    exact hn ⟨b, maxP_iff.2 ⟨⟨hb, hB hb⟩, fun y hy hby => hb' ⟨y, hy, hby⟩⟩⟩
  · rintro h ⟨m, hm⟩
    rw [maxP_iff] at hm
    obtain ⟨y, hy, hmy⟩ := h hm.1.1
    exact hm.2 y hy hmy

private theorem b2_sub_img_fld {P : α → α → Prop} {B : Set α} (h : B ⊆ P ʻʻ B) : B ⊆ fld P :=
  fun b hb => let ⟨y, _, hby⟩ := h hb; ⟨y, Or.inl hby⟩

/-- ✱216·101. \(\vdash :x\in \delta _{P}ʻ\alpha .\equiv .(\exists \beta ).\beta \subset \alpha .\exists !\beta .\beta \subset Pʻʻ\beta .x\text{seq}_{P}\beta\) -/
theorem pm216_101 {P : α → α → Prop} {A : Set α} {x : α} :
    x ∈ derivCls P A ↔ ∃ B, ((B ⊆ A ∧ B.Nonempty) ∧ B ⊆ P ʻʻ B) ∧ seqP P x B := by
  constructor
  · rintro ⟨B, ⟨hBA, hne⟩, hseq, hn⟩
    have hBf : B ⊆ fld P := fun b hb => (hBA hb).2
    exact ⟨B, ⟨⟨fun b hb => (hBA hb).1, hne⟩, (b2_noMax_iff hBf).1 (fun h => hn h)⟩, hseq⟩
  · rintro ⟨B, ⟨⟨hBA, hne⟩, hBP⟩, hseq⟩
    have hBf := b2_sub_img_fld hBP
    exact ⟨B, ⟨fun b hb => ⟨hBA hb, hBf hb⟩, hne⟩, hseq, fun h => (b2_noMax_iff hBf).2 hBP h⟩

/-- ✱216·11. \(\vdash .\delta _{P}ʻ\alpha \subset \breve{P} ʻʻ\alpha\) -/
theorem pm216_11 {P : α → α → Prop} {A : Set α} : derivCls P A ⊆ P˘ ʻʻ A := by
  rintro x ⟨B, ⟨hBA, b, hb⟩, hseq, -⟩
  exact ⟨b, (hBA hb).1, (seqP_iff.1 hseq).1.1 b ⟨hb, (hBA hb).2⟩⟩

/-- ✱216·111. \(\vdash .\delta _{P}ʻ\alpha \subset \text{ᗡ}ʻP \quad[*216·11.*37·16]\) -/
theorem pm216_111 {P : α → α → Prop} {A : Set α} : derivCls P A ⊆ codom P := by
  intro x hx
  obtain ⟨b, -, hbx⟩ := pm216_11 hx
  exact ⟨b, hbx⟩

/-- ✱216·12. \(\vdash .\delta _{P}ʻ\alpha =\delta _{P}ʻ(\alpha \cap CʻP) \quad[*22·5.(*216·01)]\) -/
theorem pm216_12 {P : α → α → Prop} {A : Set α} : derivCls P A = derivCls P (A ∩ fld P) := by
  show ltP P ʻʻ clEx (A ∩ fld P) = ltP P ʻʻ clEx (A ∩ fld P ∩ fld P)
  rw [Set.inter_assoc, Set.inter_self]

/-- ✱216·13. \(\vdash \colon\colon P\in \text{Ser}.\supset \colon\ldotp x\in \delta _{P}ʻ\alpha .\equiv :x\in \text{ᗡ}ʻP:yPx.\supset _{y}.\exists !\alpha \cap \overleftarrow{P}ʻy\cap \overrightarrow{P}ʻx\) -/
theorem pm216_13 {P : α → α → Prop} {A : Set α} {x : α} (h : P ∈ Ser) :
    x ∈ derivCls P A ↔ x ∈ codom P ∧ ∀ y, P y x → (A ∩ rels P y ∩ refs P x).Nonempty := by
  have tr := mem_transR.1 h.1.2
  have hirr := b2_irr_of_ser h
  constructor
  · rintro ⟨B, ⟨hBA, b, hb⟩, hseq, hn⟩
    rw [seqP_iff] at hseq
    refine ⟨⟨b, hseq.1.1 b ⟨hb, (hBA hb).2⟩⟩, fun y hyx => ?_⟩
    have : ¬∀ w, w ∈ B ∩ fld P → P w y := fun H => hseq.2 y H hyx
    push Not at this
    obtain ⟨w, ⟨hwB, hwf⟩, hwy⟩ := this
    have hyf : y ∈ fld P := ⟨x, Or.inl hyx⟩
    rcases mem_connex.1 h.2 w y ⟨hwf, hyf⟩ with (h1 | rfl) | h1
    · exact absurd h1 hwy
    · have : ¬maxP P w B := fun hm => hn ⟨w, hm⟩
      rw [maxP_iff] at this; push Not at this
      obtain ⟨w', hw'B, hww'⟩ := this ⟨hwB, hwf⟩
      exact ⟨w', ⟨(hBA hw'B).1, hww'⟩, hseq.1.1 w' ⟨hw'B, (hBA hw'B).2⟩⟩
    · exact ⟨w, ⟨(hBA hwB).1, h1⟩, hseq.1.1 w ⟨hwB, hwf⟩⟩
  · rintro ⟨⟨y0, hy0⟩, H⟩
    refine ⟨A ∩ refs P x ∩ fld P, ⟨fun z hz => ⟨hz.1.1, hz.2⟩, ?_⟩, ?_, ?_⟩
    · obtain ⟨w, ⟨hwA, -⟩, hwx⟩ := H y0 hy0
      exact ⟨w, ⟨hwA, hwx⟩, ⟨x, Or.inl hwx⟩⟩
    · rw [seqP_iff]
      refine ⟨⟨fun w hw => hw.1.1.2, ⟨y0, Or.inr hy0⟩⟩, fun z hz hzx => ?_⟩
      obtain ⟨w, ⟨hwA, hzw⟩, hwx⟩ := H z hzx
      have := hz w ⟨⟨⟨hwA, hwx⟩, ⟨x, Or.inl hwx⟩⟩, ⟨x, Or.inl hwx⟩⟩
      exact hirr z (tr z w z ⟨hzw, this⟩)
    · rintro ⟨m, hm⟩
      rw [maxP_iff] at hm
      obtain ⟨w, ⟨hwA, hmw⟩, hwx⟩ := H m hm.1.1.1.2
      exact hm.2 w ⟨⟨hwA, hwx⟩, ⟨x, Or.inl hwx⟩⟩ hmw

/-- ✱216·14. \(\vdash :P\in \text{Ser}.\supset .\delta _{^{2}}ʻ\alpha \subset \delta _{P}ʻ\alpha\)

**Status.** proved (reading): the e-text prints `δ_{^2}'α` for `δ_P²'α`, i.e. `δ_P'δ_P'α` (Defs/Part5, ✱216·01). -/
theorem pm216_14 {P : α → α → Prop} {A : Set α} (h : P ∈ Ser) :
    derivCls P (derivCls P A) ⊆ derivCls P A := by
  have tr := mem_transR.1 h.1.2
  intro x hx
  rw [pm216_13 h] at hx ⊢
  refine ⟨hx.1, fun y hyx => ?_⟩
  obtain ⟨z, ⟨hz, hyz⟩, hzx⟩ := hx.2 y hyx
  rw [pm216_13 h] at hz
  obtain ⟨w, ⟨hwA, hyw⟩, hwz⟩ := hz.2 y hyz
  exact ⟨w, ⟨hwA, hyw⟩, tr w z x ⟨hwz, hzx⟩⟩

/-- ✱216·15. \(\vdash :\alpha \subset \beta .\supset .\delta _{P}ʻ\alpha \subset \delta _{P}ʻ\beta \quad[*37·2.(*216·01)]\) -/
theorem pm216_15 {P : α → α → Prop} {A B : Set α} (h : A ⊆ B) :
    derivCls P A ⊆ derivCls P B := by
  rintro x ⟨C, ⟨hC, hne⟩, hlt⟩
  exact ⟨C, ⟨fun z hz => ⟨h (hC hz).1, (hC hz).2⟩, hne⟩, hlt⟩

/-- Removing the minimum of `α` from a class `β ⊂ α` without maximum keeps its limit
(✱216·16). -/
private theorem b2_lt_remove_min {P : α → α → Prop} (ht : P ∈ transR) (hc : P ∈ connex) {A B : Set α}
    (hBA : B ⊆ A ∩ fld P) (hne : B.Nonempty) {x : α} (hlt : ltP P x B) :
    (B \ refs (minP P) A).Nonempty ∧ ltP P x (B \ refs (minP P) A) := by
  have tr := mem_transR.1 ht
  obtain ⟨hseq, hn⟩ := hlt
  have hnoMax : B ⊆ P ʻʻ B := (b2_noMax_iff fun b hb => (hBA hb).2).1 (fun h => hn h)
  have notmin : ∀ b b', b ∈ B → P b b' → b' ∈ B → b' ∉ refs (minP P) A := by
    intro b b' hb hbb' hb' hm
    exact (minP_iff.1 hm).2 b (hBA hb).1 hbb'
  obtain ⟨b0, hb0⟩ := hne
  obtain ⟨b1, hb1, hb01⟩ := hnoMax hb0
  have hB'ne : (B \ refs (minP P) A).Nonempty := ⟨b1, hb1, notmin b0 b1 hb0 hb01 hb1⟩
  have cs : ∀ z, (∀ y, y ∈ B \ refs (minP P) A ∩ fld P → P y z) ↔ (∀ y, y ∈ B ∩ fld P → P y z) := by
    intro z
    constructor
    · intro H y ⟨hy, hyf⟩
      by_cases hym : y ∈ refs (minP P) A
      · obtain ⟨y', hy', hyy'⟩ := hnoMax hy
        exact tr y y' z ⟨hyy', H y' ⟨⟨hy', notmin y y' hy hyy' hy'⟩, (hBA hy').2⟩⟩
      · exact H y ⟨⟨hy, hym⟩, hyf⟩
    · intro H y ⟨hy, hyf⟩; exact H y ⟨hy.1, hyf⟩
  refine ⟨hB'ne, ?_, ?_⟩
  · rw [seqP_iff] at hseq ⊢
    simp only [cs]
    exact hseq
  · rintro ⟨m, hm⟩
    rw [maxP_iff] at hm
    obtain ⟨y, hy, hmy⟩ := hnoMax hm.1.1.1
    exact hm.2 y ⟨hy, notmin m y hm.1.1.1 hmy hy⟩ hmy

/-- ✱216·16. \(\vdash :P\in \text{trans}\cap \text{connex} .\supset .\delta _{P}ʻ\alpha =\delta _{P}ʻ(\alpha -\overrightarrow{\text{min}}_{P}ʻ\alpha )\) -/
theorem pm216_16 {P : α → α → Prop} {A : Set α} (h : P ∈ transR ∩ connex) :
    derivCls P A = derivCls P (A \ refs (minP P) A) := by
  refine Set.Subset.antisymm ?_ (pm216_15 Set.sdiff_subset)
  rintro x ⟨B, ⟨hBA, hne⟩, hlt⟩
  obtain ⟨hne', hlt'⟩ := b2_lt_remove_min h.1 h.2 hBA hne hlt
  exact ⟨B \ refs (minP P) A, ⟨fun z hz => ⟨⟨(hBA hz.1).1, hz.2⟩, (hBA hz.1).2⟩, hne'⟩, hlt'⟩

private theorem b2_lt_inter {P : α → α → Prop} {x : α} {B : Set α} : ltP P x B ↔ ltP P x (B ∩ fld P) := by
  rw [ltP_iff, ltP_iff, b2_seqP_inter]
  simp only [b2_maxP_inter (A := B), Set.inter_assoc, Set.inter_self]

/-- ✱216·2. \(\vdash .\delta_{P}ʻCʻP=\text{D}ʻ\text{lt}_P-\overrightarrow{B}ʻP\) -/
theorem pm216_2 {P : α → α → Prop} : derivCls P (fld P) = dom (ltP P) \ refs Beg P := by
  ext x
  constructor
  · rintro ⟨B, ⟨hB, b, hb⟩, hlt⟩
    refine ⟨⟨B, hlt⟩, fun hx => hx.2 ⟨b, ?_⟩⟩
    exact (seqP_iff.1 hlt.1).1.1 b ⟨hb, (hB hb).2⟩
  · rintro ⟨⟨B, hlt⟩, hx⟩
    rw [b2_lt_inter] at hlt
    refine ⟨B ∩ fld P, ⟨fun z hz => ⟨hz.2, hz.2⟩, ?_⟩, hlt⟩
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, ← Null_eq_empty] at hlt
    exact hx (b2_seq_null.1 hlt.1)

/-- Pointwise form of ✱207·35: for `P ⊂ J` connected, `D'lt_P = C'P − ᗡ'(P −̇ P²)`. -/
private theorem b2_dom_lt {P : α → α → Prop} (hirr : ∀ x, ¬P x x) (hc : P ∈ connex) :
    dom (ltP P) = fld P \ codom (P ∸ rsq P) := by
  ext x
  constructor
  · rintro ⟨B, hseq, hn⟩
    rw [seqP_iff] at hseq
    refine ⟨hseq.1.2, ?_⟩
    rintro ⟨y, hyx, hny⟩
    refine hseq.2 y (fun b hb => ?_) hyx
    have hyf : y ∈ fld P := ⟨x, Or.inl hyx⟩
    rcases mem_connex.1 hc b y ⟨hb.2, hyf⟩ with (h1 | rfl) | h1
    · exact h1
    · have : ¬maxP P b B := fun hm => hn ⟨b, hm⟩
      rw [maxP_iff] at this; push Not at this
      obtain ⟨b', hb', hbb'⟩ := this ⟨hb.1, hb.2⟩
      exact absurd ⟨b', hbb', hseq.1.1 b' ⟨hb', ⟨b, Or.inr hbb'⟩⟩⟩ hny
    · exact absurd ⟨b, h1, hseq.1.1 b hb⟩ hny
  · rintro ⟨hx, hn⟩
    refine ⟨refs P x, seqP_iff.2 ⟨⟨fun y hy => hy.1, hx⟩, fun z hz hzx => ?_⟩, ?_⟩
    · exact hirr z (hz z ⟨hzx, ⟨x, Or.inl hzx⟩⟩)
    · rintro ⟨m, hm⟩
      rw [maxP_iff] at hm
      by_cases hb : ∃ z, P m z ∧ P z x
      · obtain ⟨z, hmz, hzx⟩ := hb
        exact hm.2 z hzx hmz
      · exact hn ⟨m, hm.1.1, hb⟩

private theorem b2_fld_diff_Beg {P : α → α → Prop} : fld P \ refs Beg P = codom P := by
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    by_contra hc
    obtain ⟨y, hy | hy⟩ := hx
    · exact hn ⟨⟨y, hy⟩, hc⟩
    · exact hc ⟨y, hy⟩
  · rintro ⟨y, hy⟩; exact ⟨⟨y, Or.inr hy⟩, fun h => h.2 ⟨y, hy⟩⟩

private theorem b2_codom_sub (P : α → α → Prop) {S : α → α → Prop} (h : S ⪽ P) :
    codom S ⊆ codom P := fun x ⟨y, hy⟩ => ⟨y, h y x hy⟩

/-- ✱216·21. \[\begin{align}&\vdash :P\in \text{ᗡ}ʻʻʻJ\cap \text{connex} .\supset .\delta _{P}ʻCʻP=\text{ᗡ}ʻP-\text{ᗡ}ʻ(P\dot{-} P^{2})\\ &[*207·35.*216·2]\end{align}\]

**Status.** proved (reading): the e-text prints `ᗡ'''J` for `Rl'J` (the hypothesis of ✱207·35, which PM cites). -/
theorem pm216_21 {P : α → α → Prop} (h : P ∈ rl J ∩ connex) :
    derivCls P (fld P) = codom P \ codom (P ∸ rsq P) := by
  have hirr : ∀ x, ¬P x x := mem_rl_J.1 h.1
  rw [pm216_2, b2_dom_lt hirr h.2]
  have e := b2_fld_diff_Beg (P := P)
  ext x
  constructor
  · rintro ⟨⟨hx, hn⟩, hb⟩; exact ⟨(Set.ext_iff.1 e x).1 ⟨hx, hb⟩, hn⟩
  · rintro ⟨hx, hn⟩
    obtain ⟨h1, h2⟩ := (Set.ext_iff.1 e x).2 hx
    exact ⟨⟨h1, hn⟩, h2⟩

/-- ✱216·22. \(\vdash :P\in \text{ᗡ}ʻʻʻJ\cap \text{connex} .P\,\unicode{x2abd}\, P^{2}.\supset .\delta _{P}ʻCʻP=\text{ᗡ}ʻP \quad[*216·21]\)

**Status.** proved (reading): `ᗡ'''J` read as `Rl'J`, as in ✱216·21. -/
theorem pm216_22 {P : α → α → Prop} (h : P ∈ rl J ∩ connex ∧ P ⪽ rsq P) :
    derivCls P (fld P) = codom P := by
  rw [pm216_21 h.1]
  ext x
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
  rintro ⟨y, hyx, hn⟩
  exact hn (h.2 y x hyx)

/-- ✱216·23. \(\vdash :P\in \text{trans}.\supset .\delta _{P}ʻCʻP=\text{seq}_{P}ʻʻ\text{ᗡ}ʻ\text{sgm}ʻP=\text{lt}_Pʻʻ\text{ᗡ}ʻ\text{sgm}ʻP\) -/
theorem pm216_23 {P : α → α → Prop} (ht : P ∈ transR) :
    derivCls P (fld P) = seqP P ʻʻ codom (sgm P) ∧
      seqP P ʻʻ codom (sgm P) = ltP P ʻʻ codom (sgm P) := by
  have tr := mem_transR.1 ht
  have memK : ∀ A, A ∈ codom (sgm P) → A = P ʻʻ A ∧ A.Nonempty := by
    rintro A ⟨C, ⟨⟨hC, hP⟩, hA⟩⟩
    rw [mem_dom_imgRel_rcap_I] at hA
    obtain ⟨-, z, ⟨hz, -⟩, -⟩ := hP
    exact ⟨hA, z, hz⟩
  have e2 : seqP P ʻʻ codom (sgm P) = ltP P ʻʻ codom (sgm P) := by
    ext x
    constructor
    · rintro ⟨A, hA, hx⟩
      exact ⟨A, hA, hx, b2_noMax_fixed (memK A hA).1⟩
    · rintro ⟨A, hA, hx⟩; exact ⟨A, hA, hx.1⟩
  refine ⟨?_, e2⟩
  rw [e2]
  ext x
  constructor
  · rintro ⟨B, ⟨hBf, hne⟩, hlt⟩
    have hBf' : B ⊆ fld P := fun b hb => (hBf hb).2
    have hnoMax : B ⊆ P ʻʻ B := (b2_noMax_iff hBf').1 (fun h => hlt.2 h)
    have hfix : P ʻʻ B = P ʻʻ (P ʻʻ B) := by
      ext z
      constructor
      · rintro ⟨b, hb, hzb⟩; exact ⟨b, hnoMax hb, hzb⟩
      · rintro ⟨y, ⟨b, hb, hyb⟩, hzy⟩; exact ⟨b, hb, tr z y b ⟨hzy, hyb⟩⟩
    have hPBne : (P ʻʻ B).Nonempty := let ⟨b, hb⟩ := hne; ⟨b, hnoMax hb⟩
    refine ⟨P ʻʻ B, ⟨∅, ⟨⟨mem_dom_imgRel_rcap_I.2 ?_, ?_⟩, mem_dom_imgRel_rcap_I.2 hfix⟩⟩, ?_⟩
    · ext z; exact ⟨fun h => h.elim, fun ⟨_, h, _⟩ => h⟩
    · refine ⟨⟨fun z ⟨y, _, hzy⟩ => ⟨y, Or.inr hzy⟩, Set.empty_subset _⟩, ?_⟩
      obtain ⟨z, hz⟩ := hPBne
      exact ⟨z, ⟨hz, fun h => h⟩, fun ⟨_, h, _⟩ => h.1⟩
    · have cs : ∀ z, (∀ y, y ∈ B ∩ fld P → P y z) ↔ (∀ y, y ∈ P ʻʻ B ∩ fld P → P y z) := by
        intro z
        constructor
        · rintro H y ⟨⟨b, hb, hyb⟩, -⟩; exact tr y b z ⟨hyb, H b ⟨hb, hBf' hb⟩⟩
        · rintro H y ⟨hy, hyf⟩; exact H y ⟨hnoMax hy, hyf⟩
      refine ⟨?_, b2_noMax_fixed hfix⟩
      have := hlt.1
      rw [seqP_iff] at this ⊢
      simp only [← cs]
      exact this
  · rintro ⟨A, hA, hlt⟩
    obtain ⟨hfix, hne⟩ := memK A hA
    have hAf : A ⊆ fld P := fun z hz => by
      rw [hfix] at hz; obtain ⟨y, _, hzy⟩ := hz; exact ⟨y, Or.inl hzy⟩
    exact ⟨A, ⟨fun z hz => ⟨hAf hz, hAf hz⟩, hne⟩, hlt⟩

/-- ✱216·3. \(\vdash :\alpha \in \text{dense}ʻP.\equiv .\alpha -\overrightarrow{\text{min}}_{P}ʻ\alpha \subset \delta _{P}ʻ\alpha \quad[(*216·02)]\) -/
theorem pm216_3 {P : α → α → Prop} {A : Set α} :
    A ∈ dense P ↔ A \ refs (minP P) A ⊆ derivCls P A := Iff.rfl

private theorem b2_dense_sub {P : α → α → Prop} {A : Set α} (h : A ∈ dense P) : A ⊆ fld P := by
  intro x hx
  by_contra hxf
  have : x ∈ A \ refs (minP P) A := ⟨hx, fun hm => hxf (minP_iff.1 hm).1.2⟩
  obtain ⟨y, hy⟩ := pm216_111 (h this)
  exact hxf ⟨y, Or.inr hy⟩

private theorem b2_diff_min {P : α → α → Prop} {A : Set α} (hA : A ⊆ fld P) :
    A \ refs (minP P) A = A ∩ P˘ ʻʻ A := by
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    refine ⟨hx, ?_⟩
    by_contra h'
    exact hn (minP_iff.2 ⟨⟨hx, hA hx⟩, fun y hy hyx => h' ⟨y, hy, hyx⟩⟩)
  · rintro ⟨hx, y, hy, hyx⟩
    exact ⟨hx, fun hm => (minP_iff.1 hm).2 y hy hyx⟩

/-- ✱216·31. \(\vdash :\alpha \in \text{dense}ʻP.\equiv .\alpha \subset CʻP.\alpha \cap \breve{P} ʻʻ\alpha \subset \delta _{P}ʻ\alpha\) -/
theorem pm216_31 {P : α → α → Prop} {A : Set α} :
    A ∈ dense P ↔ A ⊆ fld P ∧ A ∩ P˘ ʻʻ A ⊆ derivCls P A := by
  constructor
  · intro h
    have hA := b2_dense_sub h
    exact ⟨hA, by rw [← b2_diff_min hA]; exact h⟩
  · rintro ⟨hA, h⟩
    show A \ refs (minP P) A ⊆ derivCls P A
    rw [b2_diff_min hA]; exact h

/-- ✱216·32. \[\begin{align}&\vdash :\alpha \in \text{closed}ʻP.\equiv .\text{Cl ex}ʻ(\alpha \cap CʻP)\subset \text{ᗡ}ʻ\text{limax}_P.\delta _{P}ʻ\alpha \subset \alpha \\ &[(*216·03)]\end{align}\] -/
theorem pm216_32 {P : α → α → Prop} {A : Set α} :
    A ∈ closed P ↔ clEx (A ∩ fld P) ⊆ codom (limaxP P) ∧ derivCls P A ⊆ A := Iff.rfl

/-- ✱216·33. \(\vdash \colon\ldotp \alpha \in \text{closed}ʻP.\equiv :\beta \subset \alpha .\exists !\beta .\beta \subset Pʻʻ\beta .\supset _{\beta }.\exists !\overrightarrow{\text{lt}} _{P}ʻ\beta .\overrightarrow{\text{lt}} _{P}ʻ\beta \subset \alpha\) -/
theorem pm216_33 {P : α → α → Prop} {A : Set α} :
    A ∈ closed P ↔ ∀ B, ((B ⊆ A ∧ B.Nonempty) ∧ B ⊆ P ʻʻ B) →
      (refs (ltP P) B).Nonempty ∧ refs (ltP P) B ⊆ A := by
  constructor
  · rintro ⟨h1, h2⟩ B ⟨⟨hBA, hne⟩, hBP⟩
    have hBf := b2_sub_img_fld hBP
    have hBc : B ∈ clEx (A ∩ fld P) := ⟨fun b hb => ⟨hBA hb, hBf hb⟩, hne⟩
    obtain ⟨v, hv | hv⟩ := h1 hBc
    · exact absurd ⟨v, hv⟩ ((b2_noMax_iff hBf).2 hBP)
    · refine ⟨⟨v, hv⟩, fun x hx => h2 ⟨B, hBc, hx⟩⟩
  · intro H
    constructor
    · rintro B ⟨hBA, hne⟩
      by_cases hm : ∃ m, maxP P m B
      · obtain ⟨m, hm⟩ := hm; exact ⟨m, Or.inl hm⟩
      · have hBf : B ⊆ fld P := fun b hb => (hBA hb).2
        obtain ⟨v, hv⟩ := (H B ⟨⟨fun b hb => (hBA hb).1, hne⟩, (b2_noMax_iff hBf).1 hm⟩).1
        exact ⟨v, Or.inr hv⟩
    · rintro x ⟨B, ⟨hBA, hne⟩, hlt⟩
      have hBf : B ⊆ fld P := fun b hb => (hBA hb).2
      exact (H B ⟨⟨fun b hb => (hBA hb).1, hne⟩, (b2_noMax_iff hBf).1 (fun h => hlt.2 h)⟩).2 hlt

private theorem b2_ltP_unique {P : α → α → Prop} (hc : P ∈ connex) {B : Set α} {x y : α}
    (hx : ltP P x B) (hy : ltP P y B) : x = y := b2_seqP_unique hc hx.1 hy.1

/-- ✱216·34. \[\begin{align}&\vdash \colon\colon P\in \text{connex} .\supset \colon\ldotp \alpha \in \text{closed}ʻP.\equiv :\\ &\beta \subset \alpha .\exists !\beta .\beta \subset Pʻʻ\beta .\supset _{\beta }.\text{lt}_Pʻ\beta \in \alpha \quad[*216·33.*71·332.*207·24]\end{align}\] -/
theorem pm216_34 {P : α → α → Prop} {A : Set α} (hc : P ∈ connex) :
    A ∈ closed P ↔ ∀ B, ((B ⊆ A ∧ B.Nonempty) ∧ B ⊆ P ʻʻ B) →
      Desc (ltP P) B (fun l => l ∈ A) := by
  rw [pm216_33]
  refine forall₂_congr fun B _ => ?_
  constructor
  · rintro ⟨⟨v, hv⟩, hsub⟩
    rw [b2_desc_of_refs (b2_refs_single (R := ltP P) (y := B) hv
      (fun c hc' => b2_ltP_unique hc hc' hv))]
    exact hsub hv
  · rintro ⟨v, hv, hvA⟩
    have e := b2_refs_eq_of hv
    refine ⟨⟨v, b2_mem_of_refs_eq (R := ltP P) (y := B) e⟩, ?_⟩
    rw [e]; rintro x rfl; exact hvA

/-- ✱216·35. \(\vdash :P\in \text{Ser}.\text{Cl ex}ʻ\alpha \subset \text{ᗡ}ʻ\text{limax}_P.\supset .\text{Cl ex}ʻ\delta _{P}ʻ\alpha \subset \text{ᗡ}ʻ\text{limax}_P\) -/
theorem pm216_35 {P : α → α → Prop} {A : Set α}
    (h : P ∈ Ser ∧ clEx A ⊆ codom (limaxP P)) : clEx (derivCls P A) ⊆ codom (limaxP P) := by
  obtain ⟨hs, hA⟩ := h
  have tr := mem_transR.1 hs.1.2
  have hirr := b2_irr_of_ser hs
  have hc := hs.2
  rintro D ⟨hD, d0, hd0⟩
  by_cases hm : ∃ m, maxP P m D
  · obtain ⟨m, hm⟩ := hm; exact ⟨m, Or.inl hm⟩
  have hDf : D ⊆ fld P := fun d hd => let ⟨y, hy⟩ := pm216_111 (hD hd); ⟨y, Or.inr hy⟩
  have hnoMax := (b2_noMax_iff hDf).1 hm
  set C := A ∩ P ʻʻ D
  have hCne : C.Nonempty := by
    obtain ⟨d1, hd1, hd01⟩ := hnoMax hd0
    have := (pm216_13 hs).1 (hD hd1)
    obtain ⟨a, ⟨haA, -⟩, had1⟩ := this.2 d0 hd01
    exact ⟨a, haA, d1, hd1, had1⟩
  obtain ⟨v, hv⟩ := hA ⟨Set.inter_subset_left, hCne⟩
  have hvf : v ∈ fld P := by
    rcases hv with h1 | ⟨h1, -⟩
    · exact (maxP_iff.1 h1).1.2
    · exact (seqP_iff.1 h1).1.2
  have hle : ∀ c, c ∈ C → c = v ∨ P c v := by
    intro c hc'
    have hcf : c ∈ fld P := let ⟨d, _, hcd⟩ := hc'.2; ⟨d, Or.inl hcd⟩
    rcases hv with h1 | ⟨h1, -⟩
    · rw [maxP_iff] at h1
      rcases mem_connex.1 hc c v ⟨hcf, hvf⟩ with (h2 | h2) | h2
      · exact Or.inr h2
      · exact Or.inl h2
      · exact absurd h2 (h1.2 c hc')
    · exact Or.inr ((seqP_iff.1 h1).1.1 c ⟨hc', hcf⟩)
  have hcs : ∀ d, d ∈ D → P d v := by
    intro d hd
    obtain ⟨d', hd', hdd'⟩ := hnoMax hd
    obtain ⟨a, ⟨haA, hda⟩, had'⟩ := ((pm216_13 hs).1 (hD hd')).2 d hdd'
    rcases hle a ⟨haA, d', hd', had'⟩ with rfl | h2
    · exact hda
    · exact tr d a v ⟨hda, h2⟩
  refine ⟨v, Or.inr ⟨seqP_iff.2 ⟨⟨fun d hd => hcs d hd.1, hvf⟩, fun z hz hzv => ?_⟩, hm⟩⟩
  rcases hv with h1 | ⟨h1, -⟩
  · rw [maxP_iff] at h1
    obtain ⟨d, hd, hvd⟩ := h1.1.1.2
    have := hz d ⟨hd, hDf hd⟩
    exact hirr v (tr v z v ⟨tr v d z ⟨hvd, this⟩, hzv⟩)
  · rw [seqP_iff] at h1
    refine h1.2 z (fun c hc' => ?_) hzv
    obtain ⟨d, hd, hcd⟩ := hc'.1.2
    exact tr c d z ⟨hcd, hz d ⟨hd, hDf hd⟩⟩

/-- ✱216·36. \(\vdash :\alpha \in \text{perf}ʻP.\equiv .\alpha \in \text{dense}ʻP\cap \text{closed}ʻP \quad[(*216·04)]\) -/
theorem pm216_36 {P : α → α → Prop} {A : Set α} : A ∈ perf P ↔ A ∈ dense P ∩ closed P :=
  Iff.rfl

private theorem b2_deriv_not_min {P : α → α → Prop} {A : Set α} {x : α} (hx : x ∈ derivCls P A) :
    x ∉ refs (minP P) A := by
  intro hm
  obtain ⟨b, hb, hbx⟩ := pm216_11 hx
  exact (minP_iff.1 hm).2 b hb hbx

/-- ✱216·37. \[\begin{align}&\vdash :\alpha \in \text{perf}ʻP.\equiv .\text{Cl ex}ʻ\alpha \subset \text{ᗡ}ʻ\text{limax}_P.\delta _{P}ʻ\alpha =\alpha -\overrightarrow{\text{min}}_{P}ʻ\alpha \\ &[*216·3·32·36]\end{align}\] -/
theorem pm216_37 {P : α → α → Prop} {A : Set α} :
    A ∈ perf P ↔ clEx A ⊆ codom (limaxP P) ∧ derivCls P A = A \ refs (minP P) A := by
  constructor
  · rintro ⟨hd, h1, h2⟩
    have hA := b2_dense_sub hd
    rw [Set.inter_eq_left.2 hA] at h1
    refine ⟨h1, Set.Subset.antisymm (fun x hx => ⟨h2 hx, b2_deriv_not_min hx⟩) hd⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun B (hB : B ∈ clEx (A ∩ fld P)) => h1 (⟨fun z hz => (hB.1 hz).1, hB.2⟩ : B ∈ clEx A), ?_⟩
    · show A \ refs (minP P) A ⊆ derivCls P A
      rw [h2]
    · rw [h2]; exact Set.sdiff_subset

/-- ✱216·371. \[\begin{align}&\vdash :\alpha \in \text{perf}ʻP.\equiv .\text{Cl ex}ʻ\alpha \subset \text{ᗡ}ʻ\text{limax}_P.\alpha \subset CʻP.\delta _{P}ʻ\alpha =\alpha \cap \breve{P} ʻʻ\alpha \\ &[*216·31·32·11·36]\end{align}\] -/
theorem pm216_371 {P : α → α → Prop} {A : Set α} :
    A ∈ perf P ↔ (clEx A ⊆ codom (limaxP P) ∧ A ⊆ fld P) ∧ derivCls P A = A ∩ P˘ ʻʻ A := by
  rw [pm216_37]
  constructor
  · rintro ⟨h1, h2⟩
    have hA : A ⊆ fld P := by
      have hd : A ∈ dense P := by show A \ refs (minP P) A ⊆ _; rw [h2]
      exact b2_dense_sub hd
    rw [← b2_diff_min hA]; exact ⟨⟨h1, hA⟩, h2⟩
  · rintro ⟨⟨h1, hA⟩, h2⟩
    rw [b2_diff_min hA]; exact ⟨h1, h2⟩

/-- ✱216·38. \(\vdash :P\in \text{trans}\cap \text{connex} .\alpha \in \text{dense}ʻP.\supset .\delta _{P}ʻ\alpha \in \text{dense}ʻP.\delta _{P}ʻ\alpha \subset \delta _{P}ʻ\delta _{P}ʻ\alpha\) -/
theorem pm216_38 {P : α → α → Prop} {A : Set α} (h : P ∈ transR ∩ connex ∧ A ∈ dense P) :
    derivCls P A ∈ dense P ∧ derivCls P A ⊆ derivCls P (derivCls P A) := by
  obtain ⟨⟨ht, hc⟩, hd⟩ := h
  have sub : derivCls P A ⊆ derivCls P (derivCls P A) := by
    rintro x ⟨B, ⟨hBA, hne⟩, hlt⟩
    obtain ⟨hne', hlt'⟩ := b2_lt_remove_min ht hc hBA hne hlt
    refine ⟨B \ refs (minP P) A, ⟨fun z hz => ⟨hd ⟨(hBA hz.1).1, hz.2⟩, (hBA hz.1).2⟩, hne'⟩, hlt'⟩
  exact ⟨fun x hx => sub hx.1, sub⟩

/-- ✱216·381. \[\begin{align}&\vdash :P\in \text{Ser}.\alpha \in \text{dense}ʻP.\supset .\delta _{P}ʻ\alpha =\delta _{P}ʻ\delta _{P}ʻ\alpha .\overrightarrow{\text{min}}_{P}ʻ\delta _{P}ʻ\alpha =\Lambda\\ &[*216·38·14·11]\end{align}\] -/
theorem pm216_381 {P : α → α → Prop} {A : Set α} (h : P ∈ Ser ∧ A ∈ dense P) :
    derivCls P A = derivCls P (derivCls P A) ∧ refs (minP P) (derivCls P A) = Λ := by
  obtain ⟨hs, hd⟩ := h
  have H := pm216_38 ⟨b2_ser_tc hs, hd⟩
  have e : derivCls P A = derivCls P (derivCls P A) :=
    Set.Subset.antisymm H.2 (pm216_14 hs)
  refine ⟨e, ?_⟩
  rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro x hx
  have : x ∈ derivCls P (derivCls P A) := e ▸ (minP_iff.1 hx).1.1
  exact b2_deriv_not_min this hx

/-- ✱216·382. \[\begin{align}&\vdash :P\in \text{Ser}.\alpha \in \text{dense}ʻP.\text{Cl ex}ʻ\alpha \subset \text{ᗡ}ʻ\text{limax}_P.\supset .\delta _{P}ʻ\alpha \in \text{perf}ʻP\\ &[*216·35·381·37]\end{align}\] -/
theorem pm216_382 {P : α → α → Prop} {A : Set α}
    (h : (P ∈ Ser ∧ A ∈ dense P) ∧ clEx A ⊆ codom (limaxP P)) : derivCls P A ∈ perf P := by
  obtain ⟨⟨hs, hd⟩, hcl⟩ := h
  obtain ⟨e, h0⟩ := pm216_381 ⟨hs, hd⟩
  rw [pm216_37]
  refine ⟨pm216_35 ⟨hs, hcl⟩, ?_⟩
  rw [← e, h0, Null_eq_empty, Set.sdiff_empty]

/-- ✱216·4. \(\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .\delta _{P}ʻ\alpha =Sʻʻ\delta _{Q}ʻ\breve{S} ʻʻ\alpha .\breve{S} ʻʻ\delta _{P}ʻ\alpha =\delta _{Q}ʻ\breve{S} ʻʻ\alpha\) -/
theorem pm216_4 {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    {A : Set α} (hS : S ∈ smorbar P Q) :
    derivCls P A = S ʻʻ derivCls Q (S˘ ʻʻ A) ∧ S˘ ʻʻ derivCls P A = derivCls Q (S˘ ʻʻ A) := by
  constructor
  · ext x
    constructor
    · intro hx
      have hxf : x ∈ fld P := let ⟨y, hy⟩ := pm216_111 hx; ⟨y, Or.inr hy⟩
      obtain ⟨z, hz⟩ := tS_dom hS hxf
      exact ⟨z, (tS_deriv hS hz).1 hx, hz⟩
    · rintro ⟨z, hz, hxz⟩; exact (tS_deriv hS hxz).2 hz
  · ext z
    constructor
    · rintro ⟨a, ha, haz⟩; exact (tS_deriv hS haz).1 ha
    · intro hz
      have hzf : z ∈ fld Q := let ⟨y, hy⟩ := pm216_111 hz; ⟨y, Or.inr hy⟩
      obtain ⟨a, ha⟩ := tS_cod hS hzf
      exact ⟨a, (tS_deriv hS ha).2 hz, ha⟩

/-- ✱216·401. \(\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .P\unicode{x0294f}\delta _{P}ʻ\alpha =S^{;}(Q\unicode{x0294f}\delta _{Q}ʻ\breve{S} ʻʻ\alpha )\) -/
theorem pm216_401 {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    {A : Set α} (hS : S ∈ smorbar P Q) :
    P ⥏ derivCls P A = S ⁏ (Q ⥏ derivCls Q (S˘ ʻʻ A)) := by
  rw [← b2_tS_fres hS, ← (pm216_4 hS).1]

/-- ✱216·41. \(\vdash \colon\ldotp S\in P\,\overline{\,\text{smor}\,}\,Q.\alpha \subset CʻP.\supset :\alpha \in \text{dense}ʻP.\equiv .\breve{S} ʻʻ\alpha \in \text{dense}ʻQ\) -/
theorem pm216_41 {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    {A : Set α} (h : S ∈ smorbar P Q ∧ A ⊆ fld P) : A ∈ dense P ↔ S˘ ʻʻ A ∈ dense Q := by
  obtain ⟨hS, hA⟩ := h
  have eA := tS_back hS hA
  constructor
  · rintro hd z ⟨⟨a, ha, haz⟩, hn⟩
    have : a ∉ refs (minP P) A := by
      intro hm
      have hm' : minP P a (S ʻʻ (S˘ ʻʻ A)) := by rw [eA]; exact hm
      exact hn ((tS_min hS haz).1 hm')
    exact (tS_deriv hS haz).1 (hd ⟨ha, this⟩)
  · rintro hd a ⟨ha, hn⟩
    obtain ⟨z, hz⟩ := tS_dom hS (hA ha)
    have : z ∉ refs (minP Q) (S˘ ʻʻ A) := by
      intro hm
      have := (tS_min hS hz).2 hm
      rw [eA] at this
      exact hn this
    exact (tS_deriv hS hz).2 (hd ⟨⟨a, ha, hz⟩, this⟩)

/-- ✱216·411. \(\vdash \colon\ldotp S\in P\,\overline{\,\text{smor}\,}\,Q.\alpha \subset CʻP.\supset :\alpha \in \text{closed}ʻP.\equiv .\breve{S} ʻʻ\alpha \in \text{closed}ʻQ\) -/
theorem pm216_411 {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    {A : Set α} (h : S ∈ smorbar P Q ∧ A ⊆ fld P) : A ∈ closed P ↔ S˘ ʻʻ A ∈ closed Q := by
  obtain ⟨hS, hA⟩ := h
  have eA := tS_back hS hA
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun C ⟨hC, c, hc⟩ => ?_, fun z hz => ?_⟩
    · have hBsub : S ʻʻ C ⊆ A ∩ fld P := by
        rintro x ⟨c', hc', hxc'⟩
        obtain ⟨a', ha', ha'c'⟩ := (hC hc').1
        rw [tS_inj hS hxc' ha'c']; exact ⟨ha', hA ha'⟩
      obtain ⟨b, hb⟩ := tS_cod hS (hC hc).2
      obtain ⟨v, hv⟩ := h1 ⟨hBsub, b, c, hc, hb⟩
      have hvf : v ∈ fld P := by
        rcases hv with h' | ⟨h', -⟩
        · exact (maxP_iff.1 h').1.2
        · exact (seqP_iff.1 h').1.2
      obtain ⟨w, hw⟩ := tS_dom hS hvf
      exact ⟨w, (tS_limax hS hw).1 hv⟩
    · have hzf : z ∈ fld Q := let ⟨y, hy⟩ := pm216_111 hz; ⟨y, Or.inr hy⟩
      obtain ⟨a, ha⟩ := tS_cod hS hzf
      exact ⟨a, h2 ((tS_deriv hS ha).2 hz), ha⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun B ⟨hB, b, hb⟩ => ?_, fun a ha => ?_⟩
    · have hBf : B ⊆ fld P := fun x hx => (hB hx).2
      obtain ⟨w0, hw0⟩ := tS_dom hS (hBf hb)
      have hmem : S˘ ʻʻ B ∈ clEx (S˘ ʻʻ A ∩ fld Q) := by
        refine ⟨?_, w0, b, hb, hw0⟩
        rintro c ⟨b', hb', hc⟩
        exact ⟨⟨b', (hB hb').1, hc⟩, tS_fldQ hS hc⟩
      obtain ⟨w, hw⟩ := h1 hmem
      have hwf : w ∈ fld Q := by
        rcases hw with h' | ⟨h', -⟩
        · exact (maxP_iff.1 h').1.2
        · exact (seqP_iff.1 h').1.2
      obtain ⟨v, hv⟩ := tS_cod hS hwf
      have := (tS_limax hS hv).2 hw
      rw [tS_back hS hBf] at this
      exact ⟨v, this⟩
    · have haf : a ∈ fld P := let ⟨y, hy⟩ := pm216_111 ha; ⟨y, Or.inr hy⟩
      obtain ⟨z, hz⟩ := tS_dom hS haf
      obtain ⟨a', ha', ha'z⟩ := h2 ((tS_deriv hS hz).1 ha)
      rw [tS_inj hS hz ha'z]; exact ha'

/-- ✱216·412. \[\begin{align}&\vdash \colon\ldotp S\in P\,\overline{\,\text{smor}\,}\,Q.\alpha \subset CʻP.\supset :\alpha \in \text{perf}ʻP.\equiv .\breve{S} ʻʻ\alpha \in \text{perf}ʻQ\\ &[*216·41·411·36]\end{align}\] -/
theorem pm216_412 {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    {A : Set α} (h : S ∈ smorbar P Q ∧ A ⊆ fld P) : A ∈ perf P ↔ S˘ ʻʻ A ∈ perf Q :=
  and_congr (pm216_41 h) (pm216_411 h)

private theorem b2_seg_sect {P : α → α → Prop} (h : P ∈ Ser) {G : Set α} (hG : G ∈ dom (imgRel P)) :
    G ∈ sect P := by
  obtain ⟨B, rfl⟩ := hG; exact b2_img_sect h.1.2 B

private theorem b2_segSer_ser {P : α → α → Prop} (h : P ∈ Ser) {X Y : Set α} :
    segSer P X Y ↔ (X ∈ dom (imgRel P) ∧ Y ∈ dom (imgRel P)) ∧ X ⊆ Y ∧ X ≠ Y := by
  rw [segSer_apply]
  have hcp := b2_conn_po h.2
  constructor
  · rintro ⟨⟨hX, hP⟩, hY⟩
    exact ⟨⟨hX, hY⟩, (b2_Plc_nested (b2_seg_sect h hX).1 (b2_seg_sect h hY).1
      (b2_nested hcp (b2_seg_sect h hX) (b2_seg_sect h hY))).1 hP⟩
  · rintro ⟨⟨hX, hY⟩, hs⟩
    exact ⟨⟨hX, (b2_Plc_nested (b2_seg_sect h hX).1 (b2_seg_sect h hY).1 (Or.inl hs.1)).2 hs⟩,
      hY⟩

private theorem b2_fld_segSer_ser {P : α → α → Prop} (h : P ∈ Ser) (hP : rEx P) :
    fld (segSer P) = dom (imgRel P) := by
  obtain ⟨a, b, hab⟩ := hP
  have h0 : (∅ : Set α) ∈ dom (imgRel P) := ⟨∅, Set.ext fun z => ⟨fun h => h.elim, fun ⟨_, h, _⟩ => h⟩⟩
  ext X
  constructor
  · rintro ⟨Y, hY | hY⟩
    · exact ((b2_segSer_ser h).1 hY).1.1
    · exact ((b2_segSer_ser h).1 hY).1.2
  · intro hX
    by_cases hXe : X = ∅
    · subst hXe
      refine ⟨P ʻʻ fld P, Or.inl ((b2_segSer_ser h).2 ⟨⟨h0, ⟨fld P, rfl⟩⟩, Set.empty_subset _, ?_⟩)⟩
      intro e
      have : a ∈ P ʻʻ fld P := ⟨b, ⟨a, Or.inr hab⟩, hab⟩
      rw [← e] at this; exact this
    · exact ⟨∅, Or.inr ((b2_segSer_ser h).2 ⟨⟨h0, hX⟩, Set.empty_subset _, Ne.symm hXe⟩)⟩

private theorem b2_refs_ssub {P : α → α → Prop} (h : P ∈ Ser) {x y : α} (hx : x ∈ fld P)
    (hy : y ∈ fld P) : (refs P x ⊆ refs P y ∧ refs P x ≠ refs P y) ↔ P x y := by
  have tr := mem_transR.1 h.1.2
  have hirr := b2_irr_of_ser h
  constructor
  · rintro ⟨hs, hne⟩
    rcases mem_connex.1 h.2 x y ⟨hx, hy⟩ with (h1 | rfl) | h1
    · exact h1
    · exact absurd rfl hne
    · exact absurd (hs h1) (hirr y)
  · intro hxy
    refine ⟨fun z hz => tr z x y ⟨hz, hxy⟩, fun e => ?_⟩
    have : x ∈ refs P y := hxy
    rw [← e] at this; exact hirr x this

private theorem b2_min_seg {P : α → α → Prop} (h : P ∈ Ser) {A : Set α} (hA : A ⊆ fld P) {x : α}
    (hx : x ∈ A) : minP (segSer P) (refs P x) (Rfwd P ʻʻ A) ↔ minP P x A := by
  have hxf := hA hx
  have hP : rEx P := let ⟨y, hy⟩ := hxf; hy.elim (fun h' => ⟨x, y, h'⟩) (fun h' => ⟨y, x, h'⟩)
  rw [minP_iff, minP_iff, b2_fld_segSer_ser h hP]
  constructor
  · rintro ⟨-, hn⟩
    exact ⟨⟨hx, hxf⟩, fun a ha hax => hn (refs P a) ⟨a, ha, rfl⟩ ((b2_segSer_ser h).2
      ⟨⟨b2_refs_mem_dom_img P a, b2_refs_mem_dom_img P x⟩,
        (b2_refs_ssub h (hA ha) hxf).2 hax⟩)⟩
  · rintro ⟨-, hn⟩
    refine ⟨⟨⟨x, hx, rfl⟩, b2_refs_mem_dom_img P x⟩, ?_⟩
    rintro Y ⟨a, ha, rfl⟩ hY
    exact hn a ha ((b2_refs_ssub h (hA ha) hxf).1 ((b2_segSer_ser h).1 hY).2)

/-! Derivatives in the series of segments `ς'P` of a series `P`: segments are nested sections,
`ς'P` is proper inclusion between them, and `ς'P` is a Dedekindian series (✱214·33). -/

private theorem b2_seg_empty (P : α → α → Prop) : (∅ : Set α) ∈ dom (imgRel P) :=
  ⟨∅, Set.ext fun _ => ⟨fun h => h.elim, fun ⟨_, h, _⟩ => h⟩⟩

/-- A segment not containing `y ∈ C'P` lies below `y`. -/
private theorem b2_seg_below {P : α → α → Prop} (h : P ∈ Ser) {G : Set α} (hG : G ∈ dom (imgRel P))
    {y : α} (hy : y ∈ fld P) (hyG : y ∉ G) : G ⊆ refs P y := by
  have hs := b2_seg_sect h hG
  intro z hz
  rcases mem_connex.1 h.2 z y ⟨hs.1 hz, hy⟩ with (h1 | e) | h1
  · exact h1
  · exact (hyG (e ▸ hz)).elim
  · exact absurd (b2_sect_P hs h1 hz) hyG

private theorem b2_refs_sub_seg {P : α → α → Prop} (h : P ∈ Ser) {G : Set α}
    (hG : G ∈ dom (imgRel P)) {y : α} (hy : y ∈ G) : refs P y ⊆ G :=
  fun _ hz => b2_sect_P (b2_seg_sect h hG) hz hy

private theorem b2_refs_ne {P : α → α → Prop} (h : P ∈ Ser) {G : Set α} {y : α} (hy : y ∈ G) :
    G ≠ refs P y := by
  intro e
  have : y ∈ refs P y := by rw [← e]; exact hy
  exact b2_irr_of_ser h y this

private theorem b2_codom_segSer {P : α → α → Prop} (h : P ∈ Ser) {Y : Set α} :
    Y ∈ codom (segSer P) ↔ Y ∈ dom (imgRel P) ∧ Y.Nonempty := by
  constructor
  · rintro ⟨Z, hZY⟩
    obtain ⟨⟨-, hY⟩, hs, hne⟩ := (b2_segSer_ser h).1 hZY
    obtain ⟨z, hz, -⟩ := b2_diff_of_ne hs hne
    exact ⟨hY, z, hz⟩
  · rintro ⟨hY, hne⟩
    exact ⟨∅, (b2_segSer_ser h).2 ⟨⟨b2_seg_empty P, hY⟩, Set.empty_subset _,
      Ne.symm hne.ne_empty⟩⟩

/-- `Y ∈ δ(ς'P)'κ` for a series `P`, pointwise (✱216·13 applied to `ς'P`). -/
private theorem b2_deriv_seg {P : α → α → Prop} (h : P ∈ Ser) (hP : rEx P) {K : Set (Set α)}
    {Y : Set α} : Y ∈ derivCls (segSer P) K ↔ (Y ∈ dom (imgRel P) ∧ Y.Nonempty) ∧
      ∀ Z, Z ∈ dom (imgRel P) → Z ⊆ Y → Z ≠ Y →
        ∃ W, W ∈ K ∧ W ∈ dom (imgRel P) ∧ (Z ⊆ W ∧ Z ≠ W) ∧ W ⊆ Y ∧ W ≠ Y := by
  have hs : segSer P ∈ Ser := (pm214_33 ⟨b2_ser_tc h, hP⟩).1
  rw [pm216_13 hs, b2_codom_segSer h]
  constructor
  · rintro ⟨hY, H⟩
    refine ⟨hY, fun Z hZ hZY hne => ?_⟩
    obtain ⟨W, ⟨hWK, hZW⟩, hWY⟩ := H Z ((b2_segSer_ser h).2 ⟨⟨hZ, hY.1⟩, hZY, hne⟩)
    obtain ⟨⟨-, hW⟩, hZW'⟩ := (b2_segSer_ser h).1 hZW
    exact ⟨W, hWK, hW, hZW', ((b2_segSer_ser h).1 hWY).2⟩
  · rintro ⟨hY, H⟩
    refine ⟨hY, fun Z hZY => ?_⟩
    obtain ⟨⟨hZ, -⟩, hZY', hne⟩ := (b2_segSer_ser h).1 hZY
    obtain ⟨W, hWK, hW, hZW, hWY⟩ := H Z hZ hZY' hne
    exact ⟨W, ⟨hWK, (b2_segSer_ser h).2 ⟨⟨hZ, hW⟩, hZW⟩⟩, (b2_segSer_ser h).2 ⟨⟨hW, hY.1⟩, hWY⟩⟩

/-- `P⃗'x ∈ δ(ς'P)'P⃗''α . ≡ . x ∈ δ_P'α` for `x ∈ C'P`. -/
private theorem b2_deriv_refs {P : α → α → Prop} (h : P ∈ Ser) (hP : rEx P) {A : Set α} {x : α}
    (hx : x ∈ fld P) : refs P x ∈ derivCls (segSer P) (Rfwd P ʻʻ A) ↔ x ∈ derivCls P A := by
  have tr := mem_transR.1 h.1.2
  rw [b2_deriv_seg h hP, pm216_13 h]
  constructor
  · rintro ⟨⟨-, y0, hy0⟩, H⟩
    refine ⟨⟨y0, hy0⟩, fun y hyx => ?_⟩
    have hyf : y ∈ fld P := ⟨x, Or.inl hyx⟩
    obtain ⟨W, ⟨a, haA, rfl⟩, -, hZW, hWY⟩ := H (refs P y) (b2_refs_mem_dom_img P y)
      ((b2_refs_ssub h hyf hx).2 hyx).1 ((b2_refs_ssub h hyf hx).2 hyx).2
    obtain ⟨z, hz, -⟩ := b2_diff_of_ne hZW.1 hZW.2
    have haf : a ∈ fld P := ⟨z, Or.inr hz⟩
    exact ⟨a, ⟨haA, (b2_refs_ssub h hyf haf).1 hZW⟩, (b2_refs_ssub h haf hx).1 hWY⟩
  · rintro ⟨⟨y0, hy0⟩, H⟩
    refine ⟨⟨b2_refs_mem_dom_img P x, y0, hy0⟩, fun Z hZ hZY hne => ?_⟩
    obtain ⟨y, hyx, hyZ⟩ := b2_diff_of_ne hZY hne
    obtain ⟨a, ⟨haA, hya⟩, hax⟩ := H y hyx
    have hyf : y ∈ fld P := ⟨x, Or.inl hyx⟩
    have haf : a ∈ fld P := ⟨x, Or.inl hax⟩
    exact ⟨refs P a, ⟨a, haA, rfl⟩, b2_refs_mem_dom_img P a,
      ⟨fun z hz => tr z y a ⟨b2_seg_below h hZ hyf hyZ hz, hya⟩,
        fun e => hyZ (by rw [e]; exact hya)⟩, (b2_refs_ssub h haf hx).2 hax⟩

/-- For a series, a non-null class without maximum has the limit `x` iff `P''β = P⃗'x`
(cf. ✱207·521). -/
private theorem b2_lt_img {P : α → α → Prop} (h : P ∈ Ser) {B : Set α} (hBf : B ⊆ fld P)
    (hne : B.Nonempty) (hBm : ¬∃ m, maxP P m B) {x : α} : ltP P x B ↔ P ʻʻ B = refs P x := by
  have tr := mem_transR.1 h.1.2
  have hirr := b2_irr_of_ser h
  have hnm := (b2_noMax_iff hBf).1 hBm
  rw [ltP_iff, seqP_iff]
  constructor
  · rintro ⟨⟨⟨hub, -⟩, hmin⟩, -⟩
    ext z
    constructor
    · rintro ⟨b, hb, hzb⟩; exact tr z b x ⟨hzb, hub b ⟨hb, hBf hb⟩⟩
    · intro hzx
      by_contra hz
      refine hmin z (fun b hb' => ?_) hzx
      obtain ⟨hb, hbf⟩ := hb'
      have hzf : z ∈ fld P := ⟨x, Or.inl hzx⟩
      rcases mem_connex.1 h.2 b z ⟨hbf, hzf⟩ with (h1 | e) | h1
      · exact h1
      · exact (hz (e ▸ hnm hb)).elim
      · exact absurd ⟨b, hb, h1⟩ hz
  · intro e
    obtain ⟨b0, hb0⟩ := hne
    obtain ⟨b1, hb1, hb01⟩ := hnm hb0
    have hb0x : P b0 x := by
      have : b0 ∈ P ʻʻ B := ⟨b1, hb1, hb01⟩
      rw [e] at this; exact this
    refine ⟨⟨⟨fun b hb' => ?_, ⟨b0, Or.inr hb0x⟩⟩, fun z hz hzx => ?_⟩, hBm⟩
    · obtain ⟨b', hb', hbb'⟩ := hnm hb'.1
      have : b ∈ P ʻʻ B := ⟨b', hb', hbb'⟩
      rw [e] at this; exact this
    · have : z ∈ P ʻʻ B := by rw [e]; exact hzx
      obtain ⟨b, hb, hzb⟩ := this
      exact hirr z (tr z b z ⟨hzb, hz b ⟨hb, hBf hb⟩⟩)

/-- Every class has a limit or maximum in `ς'P` (`ς'P` is Dedekindian, ✱214·33). -/
private theorem b2_seg_limax {P : α → α → Prop} (h : P ∈ Ser) (hP : rEx P) (K : Set (Set α)) :
    K ∈ codom (limaxP (segSer P)) := by
  have hD := (pm214_33 ⟨b2_ser_tc h, hP⟩).2
  rcases hD K with ⟨m, hm⟩ | ⟨s, hs⟩
  · exact ⟨m, Or.inl hm⟩
  · by_cases hm : ∃ m, maxP (segSer P) m K
    · obtain ⟨m, hm⟩ := hm; exact ⟨m, Or.inl hm⟩
    · exact ⟨s, Or.inr ⟨hs, hm⟩⟩

private theorem b2_codom_sgm {P : α → α → Prop} {Y : Set α} :
    Y ∈ codom (sgm P) ↔ Y = P ʻʻ Y ∧ Y.Nonempty := by
  constructor
  · rintro ⟨X, ⟨⟨-, hPl⟩, hY⟩⟩
    obtain ⟨-, z, ⟨hz, -⟩, -⟩ := hPl
    exact ⟨mem_dom_imgRel_rcap_I.1 hY, z, hz⟩
  · rintro ⟨hY, z, hz⟩
    have hYf : Y ⊆ fld P˘ := by
      rw [fld_cnv]
      intro w hw
      rw [hY] at hw
      obtain ⟨v, -, hwv⟩ := hw
      exact ⟨v, Or.inl hwv⟩
    exact ⟨∅, ⟨⟨mem_dom_imgRel_rcap_I.2 (Set.ext fun _ => ⟨fun h => h.elim,
      fun ⟨_, h, _⟩ => h⟩), ⟨hYf, Set.empty_subset _⟩, z, ⟨hz, fun h => h⟩,
      fun ⟨_, h, _⟩ => h.1⟩, mem_dom_imgRel_rcap_I.2 hY⟩⟩

/-- ✱216·5. \(\vdash :P\in \text{Ser}.\supset .\text{ᗡ}ʻ\varsigma ʻP-\overrightarrow{P}ʻʻCʻP\subset \delta (\varsigma ʻP)ʻ\overrightarrow{P}ʻʻCʻP\) -/
theorem pm216_5 {P : α → α → Prop} (h : P ∈ Ser) :
    codom (segSer P) \ Rfwd P ʻʻ fld P ⊆ derivCls (segSer P) (Rfwd P ʻʻ fld P) := by
  have tr := mem_transR.1 h.1.2
  rintro Y ⟨hYc, hYn⟩
  have hP : rEx P := by
    obtain ⟨Z, hZY⟩ := hYc
    obtain ⟨⟨-, hY⟩, hs, hne⟩ := (b2_segSer_ser h).1 hZY
    obtain ⟨y, hy, -⟩ := b2_diff_of_ne hs hne
    obtain ⟨B, rfl⟩ := hY
    obtain ⟨b, -, hyb⟩ := hy
    exact ⟨y, b, hyb⟩
  rw [b2_codom_segSer h] at hYc
  obtain ⟨hY, hne⟩ := hYc
  have hYs := b2_seg_sect h hY
  have hnm : ∀ y, y ∈ Y → ∃ y', y' ∈ Y ∧ P y y' := by
    intro y hy
    by_contra hn
    push Not at hn
    obtain ⟨C, hC⟩ := hY
    have hy' := hy
    rw [hC] at hy'
    obtain ⟨c, hc, hyc⟩ := hy'
    refine hYn ⟨c, ⟨y, Or.inr hyc⟩, ?_⟩
    ext z
    constructor
    · intro hz
      rcases mem_connex.1 h.2 z y ⟨hYs.1 hz, hYs.1 hy⟩ with (h1 | e) | h1
      · exact tr z y c ⟨h1, hyc⟩
      · rw [e]; exact hyc
      · exact absurd h1 (hn z hz)
    · intro hzc; rw [hC]; exact ⟨c, hc, hzc⟩
  rw [b2_deriv_seg h hP]
  refine ⟨⟨hY, hne⟩, fun Z hZ hZY hZne => ?_⟩
  obtain ⟨y, hyY, hyZ⟩ := b2_diff_of_ne hZY hZne
  obtain ⟨y', hy'Y, hyy'⟩ := hnm y hyY
  have hyf : y ∈ fld P := hYs.1 hyY
  have hy'f : y' ∈ fld P := hYs.1 hy'Y
  exact ⟨refs P y', ⟨y', hy'f, rfl⟩, b2_refs_mem_dom_img P y',
    ⟨fun z hz => tr z y y' ⟨b2_seg_below h hZ hyf hyZ hz, hyy'⟩,
      fun e => hyZ (by rw [e]; exact hyy')⟩, b2_refs_sub_seg h hY hy'Y, (b2_refs_ne h hy'Y).symm⟩

/-- ✱216·51. \[\begin{align}&\vdash :P\in \text{Ser} .\supset .\\ &\delta (\varsigma ʻP)ʻ\overrightarrow{P}ʻʻCʻP=\delta (\varsigma ʻP)ʻCʻ\varsigma ʻP=\text{D}ʻ\text{lt}(\varsigma ʻP)-\iota ʻ\Lambda =\text{ᗡ}ʻ\text{sgm}ʻP\end{align}\] -/
theorem pm216_51 {P : α → α → Prop} (h : P ∈ Ser) :
    (derivCls (segSer P) (Rfwd P ʻʻ fld P) = derivCls (segSer P) (fld (segSer P)) ∧
      derivCls (segSer P) (fld (segSer P)) = dom (ltP (segSer P)) \ ι Λ) ∧
      dom (ltP (segSer P)) \ ι Λ = codom (sgm P) := by
  have tr := mem_transR.1 h.1.2
  by_cases hP : rEx P
  · have ha : derivCls (segSer P) (Rfwd P ʻʻ fld P) = derivCls (segSer P) (fld (segSer P)) := by
      refine Set.Subset.antisymm (pm216_15 ?_) ?_
      · rintro _ ⟨x, -, rfl⟩
        rw [b2_fld_segSer_ser h hP]; exact b2_refs_mem_dom_img P x
      · intro Y hY
        rw [b2_deriv_seg h hP] at hY ⊢
        obtain ⟨⟨hYd, hne⟩, H⟩ := hY
        have hYs := b2_seg_sect h hYd
        refine ⟨⟨hYd, hne⟩, fun Z hZ hZY hZne => ?_⟩
        obtain ⟨W, -, hW, hZW, hWY⟩ := H Z hZ hZY hZne
        have hWs := b2_seg_sect h hW
        obtain ⟨w, hwW, hwZ⟩ := b2_diff_of_ne hZW.1 hZW.2
        obtain ⟨y, hyY, hyW⟩ := b2_diff_of_ne hWY.1 hWY.2
        have hwf := hWs.1 hwW
        have hyf := hYs.1 hyY
        have hwy : P w y := by
          rcases mem_connex.1 h.2 w y ⟨hwf, hyf⟩ with (h1 | e) | h1
          · exact h1
          · exact (hyW (e ▸ hwW)).elim
          · exact (hyW (b2_sect_P hWs h1 hwW)).elim
        exact ⟨refs P y, ⟨y, hyf, rfl⟩, b2_refs_mem_dom_img P y,
          ⟨fun z hz => tr z w y ⟨b2_seg_below h hZ hwf hwZ hz, hwy⟩,
            fun e => hwZ (by rw [e]; exact hwy)⟩, b2_refs_sub_seg h hYd hyY,
          (b2_refs_ne h hyY).symm⟩
    have hBeg : refs Beg (segSer P) = ι Λ := by
      obtain ⟨a, b, hab⟩ := hP
      ext X
      rw [b2_refs_Beg, b2_mem_iotaNull]
      constructor
      · rintro ⟨⟨Y, hXY⟩, hn⟩
        obtain ⟨⟨hX, -⟩, -⟩ := (b2_segSer_ser h).1 hXY
        by_contra hX0
        exact hn ((b2_codom_segSer h).2 ⟨hX, Set.nonempty_iff_ne_empty.2 hX0⟩)
      · rintro rfl
        refine ⟨⟨refs P b, (b2_segSer_ser h).2 ⟨⟨b2_seg_empty P, b2_refs_mem_dom_img P b⟩,
          Set.empty_subset _, fun e => ?_⟩⟩, fun hc => ?_⟩
        · have : a ∈ refs P b := hab
          rw [← e] at this; exact this
        · obtain ⟨-, z, hz⟩ := (b2_codom_segSer h).1 hc; exact hz
    have hb : derivCls (segSer P) (fld (segSer P)) = dom (ltP (segSer P)) \ ι Λ := by
      rw [pm216_2, hBeg]
    refine ⟨⟨ha, hb⟩, ?_⟩
    rw [← hb]
    ext Y
    rw [b2_deriv_seg h hP, b2_codom_sgm]
    constructor
    · rintro ⟨⟨hY, hne⟩, H⟩
      have hYs := b2_seg_sect h hY
      refine ⟨Set.Subset.antisymm (fun y hy => ?_) hYs.2, hne⟩
      obtain ⟨W, -, hW, hZW, hWY⟩ := H (refs P y) (b2_refs_mem_dom_img P y)
        (b2_refs_sub_seg h hY hy) (b2_refs_ne h hy).symm
      have hWs := b2_seg_sect h hW
      obtain ⟨w, hwW, hwZ⟩ := b2_diff_of_ne hZW.1 hZW.2
      obtain ⟨v, hvY, hvW⟩ := b2_diff_of_ne hWY.1 hWY.2
      rcases mem_connex.1 h.2 w y ⟨hWs.1 hwW, hYs.1 hy⟩ with (h1 | e) | h1
      · exact (hwZ h1).elim
      · have hyW : y ∈ W := e ▸ hwW
        rcases mem_connex.1 h.2 v y ⟨hYs.1 hvY, hYs.1 hy⟩ with (h2 | e2) | h2
        · exact (hvW (b2_sect_P hWs h2 hyW)).elim
        · exact (hvW (e2 ▸ hyW)).elim
        · exact ⟨v, hvY, h2⟩
      · exact ⟨w, hWY.1 hwW, h1⟩
    · rintro ⟨hfix, hne⟩
      have hY : Y ∈ dom (imgRel P) := ⟨Y, hfix⟩
      refine ⟨⟨hY, hne⟩, fun Z hZ hZY hZne => ?_⟩
      obtain ⟨y, hyY, hyZ⟩ := b2_diff_of_ne hZY hZne
      have hy' : y ∈ P ʻʻ Y := by rw [← hfix]; exact hyY
      obtain ⟨y', hy'Y, hyy'⟩ := hy'
      have hYs := b2_seg_sect h hY
      have hyf : y ∈ fld P := hYs.1 hyY
      refine ⟨refs P y', ?_, b2_refs_mem_dom_img P y',
        ⟨fun z hz => tr z y y' ⟨b2_seg_below h hZ hyf hyZ hz, hyy'⟩,
          fun e => hyZ (by rw [e]; exact hyy')⟩, b2_refs_sub_seg h hY hy'Y,
        (b2_refs_ne h hy'Y).symm⟩
      rw [b2_fld_segSer_ser h hP]; exact b2_refs_mem_dom_img P y'
  · have hn : ∀ X Y, ¬segSer P X Y := by
      intro X Y hXY
      obtain ⟨⟨-, hY⟩, hs, hne⟩ := (b2_segSer_ser h).1 hXY
      obtain ⟨y, hy, -⟩ := b2_diff_of_ne hs hne
      obtain ⟨B, rfl⟩ := hY
      obtain ⟨b, -, hyb⟩ := hy
      exact hP ⟨y, b, hyb⟩
    have e1 : ∀ K, derivCls (segSer P) K = ∅ := fun K =>
      Set.eq_empty_iff_forall_notMem.2 fun Y hY => by
        obtain ⟨X, hX⟩ := pm216_111 hY
        exact hn X Y hX
    have e2 : dom (ltP (segSer P)) \ ι Λ = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun Y hY => ?_
      obtain ⟨⟨K, hK⟩, -⟩ := hY
      obtain ⟨Z, hZ | hZ⟩ := (seqP_iff.1 hK.1).1.2
      · exact hn _ _ hZ
      · exact hn _ _ hZ
    have e3 : codom (sgm P) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun Y hY => ?_
      obtain ⟨hfix, z, hz⟩ := b2_codom_sgm.1 hY
      rw [hfix] at hz
      obtain ⟨w, -, hzw⟩ := hz
      exact hP ⟨z, w, hzw⟩
    rw [e1, e1, e2, e3]
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- ✱216·52. \(\vdash :P\in \text{Ser} .\dot{\exists} !P.\alpha \subset CʻP.\supset .\delta (\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha = Pʻʻʻ(\text{Cl ex}ʻ\alpha -\text{ᗡ}ʻ\text{max}_{P})\) -/
theorem pm216_52 {P : α → α → Prop} {A : Set α} (h : (P ∈ Ser ∧ rEx P) ∧ A ⊆ fld P) :
    derivCls (segSer P) (Rfwd P ʻʻ A) = P ʻʻʻ (clEx A \ codom (maxP P)) := by
  obtain ⟨⟨h, hP⟩, hA⟩ := h
  have tr := mem_transR.1 h.1.2
  ext Y
  rw [b2_deriv_seg h hP]
  constructor
  · rintro ⟨⟨hY, hne⟩, H⟩
    have key : ∀ y, y ∈ Y → ∃ x, (x ∈ A ∧ refs P x ⊆ Y ∧ refs P x ≠ Y) ∧ P y x := by
      intro y hy
      have hyf : y ∈ fld P := (b2_seg_sect h hY).1 hy
      obtain ⟨W, ⟨x, hxA, rfl⟩, -, hZW, hWY⟩ := H (refs P y) (b2_refs_mem_dom_img P y)
        (b2_refs_sub_seg h hY hy) (b2_refs_ne h hy).symm
      exact ⟨x, ⟨hxA, hWY⟩, (b2_refs_ssub h hyf (hA hxA)).1 hZW⟩
    refine ⟨{x | x ∈ A ∧ refs P x ⊆ Y ∧ refs P x ≠ Y}, ⟨⟨fun x hx => hx.1, ?_⟩, ?_⟩, ?_⟩
    · obtain ⟨y, hy⟩ := hne
      obtain ⟨x, hx, -⟩ := key y hy
      exact ⟨x, hx⟩
    · rintro ⟨m, hm⟩
      rw [maxP_iff] at hm
      obtain ⟨⟨hmB, hmf⟩, hn⟩ := hm
      obtain ⟨W, ⟨x, hxA, rfl⟩, -, hZW, hWY⟩ :=
        H (refs P m) (b2_refs_mem_dom_img P m) hmB.2.1 hmB.2.2
      exact hn x ⟨hxA, hWY⟩ ((b2_refs_ssub h hmf (hA hxA)).1 hZW)
    · show Y = P ʻʻ _
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, hyx⟩ := key y hy
        exact ⟨x, hx, hyx⟩
      · rintro ⟨x, hx, hyx⟩
        exact hx.2.1 hyx
  · rintro ⟨B, ⟨⟨hBA, b0, hb0⟩, hBm⟩, rfl⟩
    have hBf : B ⊆ fld P := fun b hb => hA (hBA hb)
    have hnm : B ⊆ P ʻʻ B := (b2_noMax_iff hBf).1 hBm
    refine ⟨⟨⟨B, rfl⟩, b0, hnm hb0⟩, fun Z hZ hZY hne => ?_⟩
    obtain ⟨y, ⟨b, hb, hyb⟩, hyZ⟩ := b2_diff_of_ne hZY hne
    obtain ⟨b', hb', hbb'⟩ := hnm hb
    refine ⟨refs P b, ⟨b, hBA hb, rfl⟩, b2_refs_mem_dom_img P b,
      ⟨fun z hz => tr z y b ⟨b2_seg_below h hZ ⟨b, Or.inl hyb⟩ hyZ hz, hyb⟩,
        fun e => hyZ (by rw [e]; exact hyb)⟩, fun z hz => ⟨b, hb, hz⟩, fun e => ?_⟩
    have : b ∈ P ʻʻ B := ⟨b', hb', hbb'⟩
    rw [← e] at this
    exact b2_irr_of_ser h b this

/-- ✱216·521. \(\vdash :P\in \text{Ser} .\alpha \subset CʻP.\supset .\overrightarrow{P}ʻʻ(\alpha -\overrightarrow{\text{min}}_{P}ʻ\alpha ) = \overrightarrow{P}ʻʻ\alpha -\overrightarrow{\text{min}}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha\) -/
theorem pm216_521 {P : α → α → Prop} {A : Set α} (h : P ∈ Ser ∧ A ⊆ fld P) :
    Rfwd P ʻʻ (A \ refs (minP P) A) = Rfwd P ʻʻ A \ refs (minP (segSer P)) (Rfwd P ʻʻ A) := by
  obtain ⟨h, hA⟩ := h
  ext X
  constructor
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, fun hm => hn ((b2_min_seg h hA hx).1 hm)⟩
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, fun hm => hn ((b2_min_seg h hA hx).2 hm)⟩, rfl⟩

/-- ✱216·53. \(\vdash \colon\ldotp P\in \text{Ser} .\dot{\exists} !P.\alpha \subset CʻP.\supset :\alpha \in \text{dense}ʻP.\equiv .\overrightarrow{P}ʻʻ\alpha \in \text{dense}ʻ\varsigma ʻP\) -/
theorem pm216_53 {P : α → α → Prop} {A : Set α} (h : (P ∈ Ser ∧ rEx P) ∧ A ⊆ fld P) :
    A ∈ dense P ↔ Rfwd P ʻʻ A ∈ dense (segSer P) := by
  obtain ⟨⟨hs, hP⟩, hA⟩ := h
  show A \ refs (minP P) A ⊆ derivCls P A ↔
    Rfwd P ʻʻ A \ refs (minP (segSer P)) (Rfwd P ʻʻ A) ⊆ derivCls (segSer P) (Rfwd P ʻʻ A)
  rw [← pm216_521 ⟨hs, hA⟩]
  constructor
  · rintro H _ ⟨x, hx, rfl⟩
    exact (b2_deriv_refs hs hP (hA hx.1)).2 (H hx)
  · intro H x hx
    exact (b2_deriv_refs hs hP (hA hx.1)).1 (H ⟨x, hx, rfl⟩)

/-- ✱216·54. \(\vdash \colon\ldotp P\in \text{Ser} .\dot{\exists} !P.\alpha \subset CʻP.\supset :\alpha \in \text{closed}ʻP.\equiv .\delta (\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha \subset \overrightarrow{P}ʻʻ\alpha\) -/
theorem pm216_54 {P : α → α → Prop} {A : Set α} (h : (P ∈ Ser ∧ rEx P) ∧ A ⊆ fld P) :
    A ∈ closed P ↔ derivCls (segSer P) (Rfwd P ʻʻ A) ⊆ Rfwd P ʻʻ A := by
  have h52 := pm216_52 h
  obtain ⟨⟨hs, hP⟩, hA⟩ := h
  rw [h52, pm216_34 hs.2]
  constructor
  · rintro H _ ⟨B, ⟨⟨hBA, hne⟩, hBm⟩, rfl⟩
    have hBf : B ⊆ fld P := fun b hb => hA (hBA hb)
    obtain ⟨l, hl, hlA⟩ := H B ⟨⟨hBA, hne⟩, (b2_noMax_iff hBf).1 hBm⟩
    exact ⟨l, hlA, (b2_lt_img hs hBf hne hBm).1 ((hl l).2 rfl)⟩
  · intro H B hB
    obtain ⟨⟨hBA, hne⟩, hBP⟩ := hB
    have hBf : B ⊆ fld P := fun b hb => hA (hBA hb)
    have hBm : ¬∃ m, maxP P m B := (b2_noMax_iff hBf).2 hBP
    obtain ⟨l, hlA, hl⟩ := H ⟨B, ⟨⟨hBA, hne⟩, hBm⟩, rfl⟩
    have hlt : ltP P l B := (b2_lt_img hs hBf hne hBm).2 hl
    exact ⟨l, fun x => ⟨fun hx => b2_ltP_unique hs.2 hx hlt, fun e => e ▸ hlt⟩, hlA⟩

/-- ✱216·55. \(\vdash \colon\ldotp P\in \text{Ser} .\dot{\exists} !P.\alpha \subset CʻP.\supset :\alpha \in \text{closed}ʻP.\equiv .\overrightarrow{P}ʻʻ\alpha \in \text{closed}ʻ\varsigma ʻP\) -/
theorem pm216_55 {P : α → α → Prop} {A : Set α} (h : (P ∈ Ser ∧ rEx P) ∧ A ⊆ fld P) :
    A ∈ closed P ↔ Rfwd P ʻʻ A ∈ closed (segSer P) := by
  have h54 := pm216_54 h
  obtain ⟨⟨hs, hP⟩, -⟩ := h
  rw [h54, pm216_32 (P := segSer P)]
  exact ⟨fun H => ⟨fun K _ => b2_seg_limax hs hP K, H⟩, fun H => H.2⟩

/-- ✱216·56. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser} .\dot{\exists} !P.\alpha &\subset CʻP.\supset :\alpha \in \text{perf}ʻP.\equiv .\overrightarrow{P}ʻʻ\alpha \in \text{perf}ʻ\varsigma ʻP.\\ &\equiv .\delta (\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha = \overrightarrow{P} ʻʻ\alpha - \overrightarrow{\text{min}}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha\\ &[*216·53·54·55·36·37.*212·44]\end{align}\] -/
theorem pm216_56 {P : α → α → Prop} {A : Set α} (h : (P ∈ Ser ∧ rEx P) ∧ A ⊆ fld P) :
    (A ∈ perf P ↔ Rfwd P ʻʻ A ∈ perf (segSer P)) ∧
      (Rfwd P ʻʻ A ∈ perf (segSer P) ↔
        derivCls (segSer P) (Rfwd P ʻʻ A) = Rfwd P ʻʻ A \ refs (minP (segSer P)) (Rfwd P ʻʻ A)) := by
  have h53 := pm216_53 h
  have h55 := pm216_55 h
  obtain ⟨⟨hs, hP⟩, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [pm216_36, pm216_36]
    exact and_congr h53 h55
  · rw [pm216_37]
    exact ⟨fun H => H.2, fun H => ⟨fun K _ => b2_seg_limax hs hP K, H⟩⟩


/-- ✱216·6. \(\vdash :x(\nabla ʻP)y.\equiv .x,y\in \text{D}ʻ\text{lt}_P.xPy \quad[(*216·05)]\) -/
theorem pm216_6 {P : α → α → Prop} {x y : α} :
    nabla P x y ↔ (x ∈ dom (ltP P) ∧ y ∈ dom (ltP P)) ∧ P x y := by
  show ((x ∈ dom (ltP P) ∧ P x y) ∧ y ∈ dom (ltP P)) ↔ _
  tauto

private theorem b2_beg_lt {P : α → α → Prop} {b : α} (hb : b ∈ refs Beg P) : ltP P b ∅ := by
  refine ⟨?_, fun ⟨m, hm⟩ => (maxP_iff.1 hm).1.1⟩
  rw [← Null_eq_empty]; exact b2_seq_null.2 hb

/-- ✱216·601. \(\vdash :x\in \text{D}ʻ\text{lt}_P\cap \text{ᗡ}ʻP.P\in \text{connex} .\text{E}!BʻP.\supset .(BʻP)(\nabla ʻP)x\) -/
theorem pm216_601 {P : α → α → Prop} {x : α}
    (h : (x ∈ dom (ltP P) ∩ codom P ∧ P ∈ connex) ∧ EDesc Beg P) :
    Desc Beg P (fun b => nabla P b x) := by
  obtain ⟨⟨⟨hxl, hxc⟩, hc⟩, hE⟩ := h
  obtain ⟨b, hb⟩ := b2_EDesc_iff.1 hE
  rw [b2_desc_of_refs hb]
  have hbB : b ∈ refs Beg P := b2_mem_of_refs_eq (R := Beg) (y := P) hb
  have hbf : b ∈ fld P := let ⟨y, hy⟩ := hbB.1; ⟨y, Or.inl hy⟩
  have hxf : x ∈ fld P := let ⟨y, hy⟩ := hxc; ⟨y, Or.inr hy⟩
  refine pm216_6.2 ⟨⟨⟨∅, b2_beg_lt hbB⟩, hxl⟩, ?_⟩
  rcases mem_connex.1 hc b x ⟨hbf, hxf⟩ with (h1 | rfl) | h1
  · exact h1
  · exact absurd hxc hbB.2
  · exact absurd ⟨x, h1⟩ hbB.2

/-- ✱216·602. \(\vdash :P\in \text{connex} .\text{E}!BʻP.\supset .\text{ᗡ}ʻ\nabla ʻP=\text{D}ʻ\text{lt}_P-\overrightarrow{B}ʻP=\delta _{P}ʻCʻP\) -/
theorem pm216_602 {P : α → α → Prop} (h : P ∈ connex ∧ EDesc Beg P) :
    codom (nabla P) = dom (ltP P) \ refs Beg P ∧ dom (ltP P) \ refs Beg P = derivCls P (fld P) := by
  refine ⟨?_, pm216_2.symm⟩
  ext y
  constructor
  · rintro ⟨x, hxy⟩
    obtain ⟨⟨-, hy⟩, hP⟩ := pm216_6.1 hxy
    exact ⟨hy, fun hb => hb.2 ⟨x, hP⟩⟩
  · rintro ⟨hy, hn⟩
    have hyf : y ∈ fld P := by obtain ⟨B, hB⟩ := hy; exact (seqP_iff.1 hB.1).1.2
    have hyc : y ∈ codom P := by
      by_contra hc'
      obtain ⟨z, hz | hz⟩ := hyf
      · exact hn ⟨⟨z, hz⟩, hc'⟩
      · exact hc' ⟨z, hz⟩
    have := pm216_601 ⟨⟨⟨hy, hyc⟩, h.1⟩, h.2⟩
    obtain ⟨b, -, hb⟩ := this
    exact ⟨b, hb⟩

/-- ✱216·603. \(\vdash :P\in \text{connex} .\dot{\exists} !\nabla ʻP.\supset .Cʻ\nabla ʻP=\text{D}ʻ\text{lt}_P\) -/
theorem pm216_603 {P : α → α → Prop} (h : P ∈ connex ∧ rEx (nabla P)) :
    fld (nabla P) = dom (ltP P) := by
  obtain ⟨hc, u, v, huv⟩ := h
  obtain ⟨⟨hu, hv⟩, hP⟩ := pm216_6.1 huv
  ext x
  constructor
  · rintro ⟨y, hy | hy⟩
    · exact (pm216_6.1 hy).1.1
    · exact (pm216_6.1 hy).1.2
  · intro hx
    have hxf : x ∈ fld P := by obtain ⟨B, hB⟩ := hx; exact (seqP_iff.1 hB.1).1.2
    rcases mem_connex.1 hc x u ⟨hxf, ⟨v, Or.inl hP⟩⟩ with (h1 | rfl) | h1
    · exact ⟨u, Or.inl (pm216_6.2 ⟨⟨hx, hu⟩, h1⟩)⟩
    · exact ⟨v, Or.inl huv⟩
    · exact ⟨u, Or.inr (pm216_6.2 ⟨⟨hu, hx⟩, h1⟩)⟩

private theorem b2_P1_eq {P : α → α → Prop} (h : P ∈ Ser) : P1 P = P ∸ rsq P := by
  funext x y; apply propext
  rw [P1_iff_of_transR h.1.2 h.1.1]; rfl

/-- ✱216·61. \(\vdash :P\in \text{Ser}.\text{E}!BʻP.\supset .\text{ᗡ}ʻ\nabla ʻP=\text{ᗡ}ʻP-\text{ᗡ}ʻP_{1} \quad[*216·602·21]\) -/
theorem pm216_61 {P : α → α → Prop} (h : P ∈ Ser ∧ EDesc Beg P) :
    codom (nabla P) = codom P \ codom (P1 P) := by
  rw [(pm216_602 ⟨h.1.2, h.2⟩).1, (pm216_602 ⟨h.1.2, h.2⟩).2, pm216_21 ⟨h.1.1.1, h.1.2⟩,
    b2_P1_eq h.1]

/-- ✱216·611. \(\vdash :P\in \text{Ser}.\dot{\exists} !\nabla ʻP.\supset .Cʻ\nabla ʻP=CʻP-\text{ᗡ}ʻP_{1}=\delta _{P}ʻCʻP\cup \overrightarrow{B}ʻP\) -/
theorem pm216_611 {P : α → α → Prop} (h : P ∈ Ser ∧ rEx (nabla P)) :
    fld (nabla P) = fld P \ codom (P1 P) ∧
      fld P \ codom (P1 P) = derivCls P (fld P) ∪ refs Beg P := by
  obtain ⟨hs, hn⟩ := h
  have hirr := b2_irr_of_ser hs
  rw [pm216_603 ⟨hs.2, hn⟩, b2_dom_lt hirr hs.2, b2_P1_eq hs, pm216_21 ⟨hs.1.1, hs.2⟩]
  refine ⟨rfl, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hn'⟩
    by_cases hb : x ∈ refs Beg P
    · exact Or.inr hb
    · exact Or.inl ⟨(Set.ext_iff.1 b2_fld_diff_Beg x).1 ⟨hx, hb⟩, hn'⟩
  · rintro (⟨hx, hn'⟩ | hb)
    · exact ⟨let ⟨y, hy⟩ := hx; ⟨y, Or.inr hy⟩, hn'⟩
    · refine ⟨let ⟨y, hy⟩ := hb.1; ⟨y, Or.inl hy⟩, fun ⟨y, hy⟩ => hb.2 ⟨y, hy.1⟩⟩

/-- ✱216·612. \(\vdash :P\in \text{Ser}.\supset .\text{ᗡ}ʻ\nabla ʻP\subset \text{ᗡ}ʻP-\text{ᗡ}ʻP_{1}\) -/
theorem pm216_612 {P : α → α → Prop} (h : P ∈ Ser) :
    codom (nabla P) ⊆ codom P \ codom (P1 P) := by
  rintro y ⟨x, hxy⟩
  obtain ⟨⟨-, hy⟩, hP⟩ := pm216_6.1 hxy
  have := (Set.ext_iff.1 (b2_dom_lt (b2_irr_of_ser h) h.2) y).1 hy
  rw [b2_P1_eq h]
  exact ⟨⟨x, hP⟩, this.2⟩

private theorem b2_sgm_codom_ne {P : α → α → Prop} (hs : P ∈ Ser) (hn : rEx (nabla P)) :
    (codom (sgm P)).Nonempty := by
  obtain ⟨u, v, huv⟩ := hn
  obtain ⟨⟨-, hv⟩, hP⟩ := pm216_6.1 huv
  have : v ∈ derivCls P (fld P) := by
    rw [pm216_2]
    exact ⟨hv, fun hb => hb.2 ⟨u, hP⟩⟩
  rw [(pm216_23 hs.1.2).1] at this
  obtain ⟨A, hA, -⟩ := this
  exact ⟨A, hA⟩

private theorem b2_sgm_empty {P : α → α → Prop} {A : Set α} (hA : A ∈ codom (sgm P)) :
    sgm P ∅ A := by
  obtain ⟨C, ⟨⟨hC, hP⟩, hA'⟩⟩ := hA
  obtain ⟨⟨hAf, -⟩, z, ⟨hz, -⟩, -⟩ := hP
  refine ⟨⟨mem_dom_imgRel_rcap_I.2 ?_, ⟨hAf, Set.empty_subset _⟩, z, ⟨hz, fun h => h⟩,
    fun ⟨_, h, _⟩ => h.1⟩, hA'⟩
  ext w; exact ⟨fun h => h.elim, fun ⟨_, h, _⟩ => h⟩

/-- ✱216·62. \(\vdash :P\in \text{Ser}.\dot{\exists} !\nabla ʻP.\supset .Cʻ\nabla ʻP=\text{seq}_{P}ʻʻCʻ\text{sgm}ʻP=\text{lt}_PʻʻCʻ\text{sgm}ʻP\) -/
theorem pm216_62 {P : α → α → Prop} (h : P ∈ Ser ∧ rEx (nabla P)) :
    fld (nabla P) = seqP P ʻʻ fld (sgm P) ∧ seqP P ʻʻ fld (sgm P) = ltP P ʻʻ fld (sgm P) := by
  obtain ⟨hs, hn⟩ := h
  obtain ⟨A0, hA0⟩ := b2_sgm_codom_ne hs hn
  have h0 : (∅ : Set α) ∈ fld (sgm P) := ⟨A0, Or.inl (b2_sgm_empty hA0)⟩
  have memK : ∀ A, A ∈ fld (sgm P) → A = P ʻʻ A := by
    rintro A ⟨C, hC | hC⟩
    · exact mem_dom_imgRel_rcap_I.1 hC.1.1
    · exact mem_dom_imgRel_rcap_I.1 hC.2
  have e2 : seqP P ʻʻ fld (sgm P) = ltP P ʻʻ fld (sgm P) := by
    ext x
    constructor
    · rintro ⟨A, hA, hx⟩; exact ⟨A, hA, hx, b2_noMax_fixed (memK A hA)⟩
    · rintro ⟨A, hA, hx⟩; exact ⟨A, hA, hx.1⟩
  refine ⟨?_, e2⟩
  rw [e2, pm216_603 ⟨hs.2, hn⟩]
  ext x
  constructor
  · rintro ⟨B, hB⟩
    by_cases hb : x ∈ refs Beg P
    · exact ⟨∅, h0, b2_beg_lt hb⟩
    · have : x ∈ derivCls P (fld P) := by rw [pm216_2]; exact ⟨⟨B, hB⟩, hb⟩
      rw [(pm216_23 hs.1.2).1, (pm216_23 hs.1.2).2] at this
      obtain ⟨A, hA, hx⟩ := this
      exact ⟨A, let ⟨C, hC⟩ := hA; ⟨C, Or.inr hC⟩, hx⟩
  · rintro ⟨A, -, hx⟩; exact ⟨A, hx⟩

/-- ✱216·621. \(\vdash :P\in \text{Ser}.\dot{\exists} !\nabla ʻP.\supset .\dot{\exists} !\text{sgm}ʻP.\exists !\text{ᗡ}ʻP-\text{ᗡ}ʻP_{1} \quad[*216·62·612]\) -/
theorem pm216_621 {P : α → α → Prop} (h : P ∈ Ser ∧ rEx (nabla P)) :
    rEx (sgm P) ∧ (codom P \ codom (P1 P)).Nonempty := by
  obtain ⟨hs, hn⟩ := h
  obtain ⟨A0, hA0⟩ := b2_sgm_codom_ne hs hn
  refine ⟨⟨∅, A0, b2_sgm_empty hA0⟩, ?_⟩
  obtain ⟨u, v, huv⟩ := hn
  exact ⟨v, pm216_612 hs ⟨u, huv⟩⟩

/-!
## [✱217] On segments of sums and converses

*(Vol. 2, p. 710)*

> *Summary of* *217.
>
> The purpose of the present number is to prove *217·43, which is required in the theory of real numbers (Part VI, Section A), where \(Q\) will be the series of positive ratios including zero, \(P\) will be the series of negative ratios in the order from zero to -\(\infty\) (both excluded), \(\alpha\) the real number zero, and \(Z\) and \(W\) two different series either of which may be taken as the series of negative and positive real numbers. In virtue of *217·43, these two series are ordinally similar.

**Lean reading.** `(C'P ∪)` and `(C'P −)` are the relations `opL (· ∪ ·) (fld P)`, `opL (· \ ·) (fld P)`
(✱38·01); `P_∈` is `imgRel P`, `(P̆)_∈ | (C'P −)` is `imgRel P˘ ⨾ opL (· \ ·) (fld P)`;
`R;S;T` is `R ⁏ S ⁏ T` (right associative); the printed `(D'P) ↓ α` is `dom P ↓ A` (read
`codom P ↓ A` in ✱217·43). Hypotheses are kept as
printed. ✱217·16 and ✱217·3 correct e-text misprints. ✱217·23, ·37 and ·41 are false in
degenerate cases (a null `P`, or `Q` with a single non-null segment) and are proved with the
minimal added hypotheses. ✱217·411, ·42, ·43 are proved pointwise: the segments of `P̆ ⤉ Q` are the
classes `P̆''(C'P − G)` (`G` a segment of `P`, in the reverse order) followed by the classes
`C'P ∪ H` (`H` a non-null segment of `Q`); they too fail in degenerate cases (too few segments), and
✱217·43 reads `ᗡ'P` for the `D'P` of its correlator.

**Status.** proved; ✱217·16, ·3 proved (reading) (e-text misprints); ✱217·23, ·37, ·41, ·411, ·42,
·43 proved (corrected).
-/

end S216

section S217

variable {α : Type u}

private theorem b2_rsum_img_iff {P Q : α → α → Prop} {A : Set α} {x : α} :
    x ∈ (P ⤉ Q) ʻʻ A ↔ ∃ a, a ∈ A ∧ ((P x a ∨ Q x a) ∨ x ∈ fld P ∧ a ∈ fld Q) := Iff.rfl

/-- ✱217·1. \(\vdash :\alpha \cap CʻQ=\Lambda .\supset .(P\unicode{x2909} Q)ʻʻ\alpha =Pʻʻ\alpha \quad[*160·1]\) -/
theorem pm217_1 {P Q : α → α → Prop} {A : Set α} (h : A ∩ fld Q = Λ) :
    (P ⤉ Q) ʻʻ A = P ʻʻ A := by
  have hdis : ∀ a, a ∈ A → a ∈ fld Q → False := fun a h1 h2 => by
    have : a ∈ A ∩ fld Q := ⟨h1, h2⟩
    rw [h, Null_eq_empty] at this; exact this
  ext x
  constructor
  · rintro ⟨a, ha, (h1 | h1) | ⟨-, h1⟩⟩
    · exact ⟨a, ha, h1⟩
    · exact (hdis a ha ⟨x, Or.inr h1⟩).elim
    · exact (hdis a ha h1).elim
  · rintro ⟨a, ha, h1⟩; exact ⟨a, ha, Or.inl (Or.inl h1)⟩

/-- ✱217·11. \(\vdash :\exists !\alpha \cap CʻQ.\supset .(P\unicode{x2909} Q)ʻʻ\alpha =CʻP\cup Qʻʻ\alpha \quad[*160·1]\) -/
theorem pm217_11 {P Q : α → α → Prop} {A : Set α} (h : (A ∩ fld Q).Nonempty) :
    (P ⤉ Q) ʻʻ A = fld P ∪ Q ʻʻ A := by
  obtain ⟨c, hcA, hcQ⟩ := h
  ext x
  constructor
  · rintro ⟨a, ha, (h1 | h1) | ⟨h1, -⟩⟩
    · exact Or.inl ⟨a, Or.inl h1⟩
    · exact Or.inr ⟨a, ha, h1⟩
    · exact Or.inl h1
  · rintro (h1 | ⟨a, ha, h1⟩)
    · exact ⟨c, hcA, Or.inr ⟨h1, hcQ⟩⟩
    · exact ⟨a, ha, Or.inl (Or.inr h1)⟩

/-- ✱217·12. \(\vdash .\text{D}ʻ(P\unicode{x2909} Q)_{\in }\subset \text{D}ʻP_{\in }\cup (CʻP\cup )ʻʻ\text{D}ʻQ_{\in } \quad[*217·1·11.*211·11]\) -/
theorem pm217_12 {P Q : α → α → Prop} :
    dom (imgRel (P ⤉ Q)) ⊆ dom (imgRel P) ∪ opL (· ∪ ·) (fld P) ʻʻ dom (imgRel Q) := by
  rintro X ⟨B, rfl⟩
  by_cases hB : (B ∩ fld Q).Nonempty
  · right; exact ⟨Q ʻʻ B, ⟨B, rfl⟩, pm217_11 hB⟩
  · left
    rw [Set.not_nonempty_iff_eq_empty, ← Null_eq_empty] at hB
    exact ⟨B, pm217_1 hB⟩

/-- ✱217·13. \(\vdash :CʻP\cap CʻQ=\Lambda .\supset .Pʻʻ\alpha =(P\unicode{x2909} Q)ʻʻ(\alpha -CʻQ) \quad[*217·1]\) -/
theorem pm217_13 {P Q : α → α → Prop} {A : Set α} (h : fld P ∩ fld Q = Λ) :
    P ʻʻ A = (P ⤉ Q) ʻʻ (A \ fld Q) := by
  rw [pm217_1 (by rw [Null_eq_empty]; ext z; simp)]
  ext x
  constructor
  · rintro ⟨a, ha, hxa⟩
    exact ⟨a, ⟨ha, fun haQ => b2_disj h ⟨x, Or.inr hxa⟩ haQ⟩, hxa⟩
  · rintro ⟨a, ha, hxa⟩; exact ⟨a, ha.1, hxa⟩

/-- ✱217·14. \(\vdash :\exists !Qʻʻ\alpha .\supset .CʻP\cup Qʻʻ\alpha =(P\unicode{x2909} Q)ʻʻ\alpha \quad[*217·11]\) -/
theorem pm217_14 {P Q : α → α → Prop} {A : Set α} (h : (Q ʻʻ A).Nonempty) :
    fld P ∪ Q ʻʻ A = (P ⤉ Q) ʻʻ A := by
  obtain ⟨x, a, ha, hxa⟩ := h
  rw [pm217_11 ⟨a, ha, ⟨x, Or.inr hxa⟩⟩]

/-- ✱217·15. \[\begin{align}&\vdash :CʻP\cap CʻQ=\Lambda .\supset .\text{D}ʻP_{\in }\cup (CʻP\cup )ʻʻ(\text{D}ʻQ_{\in }-{℩}ʻ\Lambda )\subset \text{D}ʻ(P\unicode{x2909} Q)_{\in }\\ &[*217·13·14]\end{align}\] -/
theorem pm217_15 {P Q : α → α → Prop} (h : fld P ∩ fld Q = Λ) :
    dom (imgRel P) ∪ opL (· ∪ ·) (fld P) ʻʻ (dom (imgRel Q) \ ι Λ) ⊆ dom (imgRel (P ⤉ Q)) := by
  rintro X (⟨B, rfl⟩ | ⟨G, ⟨⟨B, rfl⟩, hG⟩, rfl⟩)
  · exact ⟨B \ fld Q, pm217_13 h⟩
  · rw [b2_not_mem_iotaNull] at hG
    exact ⟨B, pm217_14 hG⟩

private theorem b2_last_dom {P : α → α → Prop} (h : ¬(refs Beg P˘).Nonempty) : fld P = dom P := by
  ext x
  refine ⟨fun hx => ?_, fun ⟨y, hy⟩ => ⟨y, Or.inl hy⟩⟩
  by_contra hd
  obtain ⟨y, hy | hy⟩ := hx
  · exact hd ⟨y, hy⟩
  · exact h ⟨x, ⟨y, hy⟩, fun ⟨z, hz⟩ => hd ⟨z, hz⟩⟩

private theorem b2_img_fld (P : α → α → Prop) : P ʻʻ fld P = dom P := by
  ext x
  exact ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, ⟨x, Or.inr hy⟩, hy⟩⟩

/-- ✱217·16. \(\vdash \colon\ldotp CʻP\cap CʻQ=\Lambda :{\sim}\exists !\overrightarrow{B}ʻ\breve{P} .\lor.\exists !\overrightarrow{B}ʻQ:\supset .CʻP_{\in }\text{D}ʻ(P\unicode{x2909} Q)_{\in }\)

**Status.** proved (reading): the e-text prints `C'P D'(P ⤉ Q)_∈` without the `∈` (`C'P ∈ D'(P ⤉ Q)_∈`). -/
theorem pm217_16 {P Q : α → α → Prop}
    (h : fld P ∩ fld Q = Λ ∧ (¬(refs Beg P˘).Nonempty ∨ (refs Beg Q).Nonempty)) :
    fld P ∈ dom (imgRel (P ⤉ Q)) := by
  obtain ⟨hd, h1 | ⟨b, hb⟩⟩ := h
  · refine ⟨fld P, ?_⟩
    show fld P = (P ⤉ Q) ʻʻ fld P
    rw [pm217_1 hd, b2_img_fld]
    exact b2_last_dom h1
  · refine ⟨ι b, ?_⟩
    show fld P = (P ⤉ Q) ʻʻ ι b
    have hbQ : b ∈ fld Q := let ⟨y, hy⟩ := hb.1; ⟨y, Or.inl hy⟩
    rw [pm217_11 (A := ι b) ⟨b, rfl, hbQ⟩]
    ext x
    refine ⟨Or.inl, ?_⟩
    rintro (h' | ⟨c, hc, hxc⟩)
    · exact h'
    · rw [b2_mem_iota] at hc; subst hc; exact absurd ⟨x, hxc⟩ hb.2

/-- ✱217·17. \[\begin{align}\vdash \colon\ldotp CʻP\cap &CʻQ=\Lambda :{\sim}\exists !\overrightarrow{B}ʻ\breve{P} .\lor.\exists !\overrightarrow{B}ʻQ:\supset .\\ &\text{D}ʻ(P\unicode{x2909} Q)_{\in }=\text{D}ʻP_{\in }\cup (CʻP\cup )ʻʻ\text{D}ʻQ_{\in } \quad[*217·12·15·16]\end{align}\] -/
theorem pm217_17 {P Q : α → α → Prop}
    (h : fld P ∩ fld Q = Λ ∧ (¬(refs Beg P˘).Nonempty ∨ (refs Beg Q).Nonempty)) :
    dom (imgRel (P ⤉ Q)) = dom (imgRel P) ∪ opL (· ∪ ·) (fld P) ʻʻ dom (imgRel Q) := by
  refine Set.Subset.antisymm pm217_12 ?_
  rintro X (hX | ⟨G, hG, rfl⟩)
  · exact pm217_15 h.1 (Or.inl hX)
  · by_cases hGe : G = ∅
    · subst hGe
      show fld P ∪ (∅ : Set α) ∈ dom (imgRel (P ⤉ Q))
      rw [Set.union_empty]; exact pm217_16 h
    · exact pm217_15 h.1 (Or.inr ⟨G, ⟨hG, by rw [b2_mem_iotaNull]; exact hGe⟩, rfl⟩)

/-- ✱217·18. \[\begin{align}\vdash \colon\ldotp CʻP\cap CʻQ=\Lambda :{\sim}&\exists !\overrightarrow{B}ʻ\breve{P} .\lor.{\sim}\exists !\overrightarrow{B}ʻQ:\supset .\\ &\text{D}ʻ(P\unicode{x2909} Q)_{\in }=\text{D}ʻP_{\in }\cup (CʻP\cup )ʻʻ(\text{D}ʻQ_{\in }-{℩}ʻ\Lambda )\end{align}\] -/
theorem pm217_18 {P Q : α → α → Prop}
    (h : fld P ∩ fld Q = Λ ∧ (¬(refs Beg P˘).Nonempty ∨ ¬(refs Beg Q).Nonempty)) :
    dom (imgRel (P ⤉ Q)) =
      dom (imgRel P) ∪ opL (· ∪ ·) (fld P) ʻʻ (dom (imgRel Q) \ ι Λ) := by
  obtain ⟨hd, h1⟩ := h
  refine Set.Subset.antisymm ?_ (pm217_15 hd)
  rintro X ⟨B, rfl⟩
  by_cases hB : (B ∩ fld Q).Nonempty
  · by_cases hQB : (Q ʻʻ B).Nonempty
    · exact Or.inr ⟨Q ʻʻ B, ⟨⟨B, rfl⟩, b2_not_mem_iotaNull.2 hQB⟩, pm217_11 hB⟩
    · left
      rw [pm217_11 hB, Set.not_nonempty_iff_eq_empty.1 hQB, Set.union_empty]
      rcases h1 with h1 | h1
      · exact ⟨fld P, by show fld P = P ʻʻ fld P; rw [b2_img_fld]; exact b2_last_dom h1⟩
      · exfalso
        obtain ⟨c, hcB, hcQ⟩ := hB
        refine h1 ⟨c, ?_, fun ⟨y, hy⟩ => hQB ⟨y, c, hcB, hy⟩⟩
        obtain ⟨y, hy | hy⟩ := hcQ
        · exact ⟨y, hy⟩
        · exact absurd ⟨y, c, hcB, hy⟩ (fun h' => hQB h')
  · left
    rw [Set.not_nonempty_iff_eq_empty, ← Null_eq_empty] at hB
    exact ⟨B, pm217_1 hB⟩

/-- ✱217·2. \(\vdash :CʻP\cap CʻQ=\Lambda .\supset .\text{D}ʻP_{\in }\cap (CʻP\cup )ʻʻ(\text{D}ʻQ_{\in }-{℩}ʻ\Lambda )=\Lambda\) -/
theorem pm217_2 {P Q : α → α → Prop} (h : fld P ∩ fld Q = Λ) :
    dom (imgRel P) ∩ opL (· ∪ ·) (fld P) ʻʻ (dom (imgRel Q) \ ι Λ) = Λ := by
  have e : (Λ : Set (Set α)) = ∅ := Null_eq_empty
  rw [e, Set.eq_empty_iff_forall_notMem]
  rintro X ⟨⟨B, hXB⟩, G, ⟨⟨C, rfl⟩, hG⟩, hX⟩
  rw [b2_not_mem_iotaNull] at hG
  obtain ⟨z, y, hy, hzy⟩ := hG
  have hz : z ∈ X := by rw [hX]; exact Or.inr ⟨y, hy, hzy⟩
  rw [hXB] at hz
  obtain ⟨w, -, hzw⟩ := hz
  exact b2_disj h ⟨w, Or.inl hzw⟩ ⟨y, Or.inl hzy⟩

/-- ✱217·21. \(\vdash :\exists !\overrightarrow{B}ʻ\breve{P} .\supset .\text{D}ʻP_{\in }\cap (CʻP\cup )ʻʻ\text{D}ʻQ_{\in }=\Lambda\) -/
theorem pm217_21 {P Q : α → α → Prop} (h : (refs Beg P˘).Nonempty) :
    dom (imgRel P) ∩ opL (· ∪ ·) (fld P) ʻʻ dom (imgRel Q) = Λ := by
  obtain ⟨e, ⟨y, hy⟩, hn⟩ := h
  have e0 : (Λ : Set (Set α)) = ∅ := Null_eq_empty
  rw [e0, Set.eq_empty_iff_forall_notMem]
  rintro X ⟨⟨B, hXB⟩, G, -, hX⟩
  have he : e ∈ X := by rw [hX]; exact Or.inl ⟨y, Or.inr hy⟩
  rw [hXB] at he
  obtain ⟨w, -, hew⟩ := he
  exact hn ⟨w, hew⟩

private theorem b2_segSer_tc {P : α → α → Prop} (h : P ∈ transR ∩ connex) {X Y : Set α} :
    segSer P X Y ↔ (X ∈ dom (imgRel P) ∧ Y ∈ dom (imgRel P)) ∧ X ⊆ Y ∧ X ≠ Y := by
  rw [segSer_apply]
  have hcp := b2_conn_po h.2
  have hs : ∀ G, G ∈ dom (imgRel P) → G ∈ sect P := by
    rintro G ⟨B, rfl⟩; exact b2_img_sect h.1 B
  constructor
  · rintro ⟨⟨hX, hP⟩, hY⟩
    exact ⟨⟨hX, hY⟩, (b2_Plc_nested (hs X hX).1 (hs Y hY).1
      (b2_nested hcp (hs X hX) (hs Y hY))).1 hP⟩
  · rintro ⟨⟨hX, hY⟩, hsub⟩
    exact ⟨⟨hX, (b2_Plc_nested (hs X hX).1 (hs Y hY).1 (Or.inl hsub.1)).2 hsub⟩, hY⟩

private theorem b2_fld_segSer_tc {P : α → α → Prop} (h : P ∈ transR ∩ connex) (hP : rEx P) :
    fld (segSer P) = dom (imgRel P) := by
  obtain ⟨a, b, hab⟩ := hP
  have h0 : (∅ : Set α) ∈ dom (imgRel P) :=
    ⟨∅, Set.ext fun z => ⟨fun h => h.elim, fun ⟨_, h, _⟩ => h⟩⟩
  ext X
  constructor
  · rintro ⟨Y, hY | hY⟩
    · exact ((b2_segSer_tc h).1 hY).1.1
    · exact ((b2_segSer_tc h).1 hY).1.2
  · intro hX
    by_cases hXe : X = ∅
    · subst hXe
      refine ⟨P ʻʻ fld P, Or.inl ((b2_segSer_tc h).2 ⟨⟨h0, ⟨fld P, rfl⟩⟩, Set.empty_subset _, ?_⟩)⟩
      intro e
      have : a ∈ P ʻʻ fld P := ⟨b, ⟨a, Or.inr hab⟩, hab⟩
      rw [← e] at this; exact this
    · exact ⟨∅, Or.inr ((b2_segSer_tc h).2 ⟨⟨h0, hX⟩, Set.empty_subset _, Ne.symm hXe⟩)⟩

private theorem b2_seg_sub {P : α → α → Prop} {G : Set α} (hG : G ∈ dom (imgRel P)) : G ⊆ fld P := by
  obtain ⟨B, rfl⟩ := hG; exact fun z ⟨y, _, hzy⟩ => ⟨y, Or.inl hzy⟩

/-- ✱217·22. \[\begin{align}\vdash :P,Q\in \text{trans}\cap \text{connex} .CʻP\cap CʻQ&=\Lambda .\exists !\overrightarrow{B}ʻ\breve{P} .\exists!\overrightarrow{B}ʻQ.\supset .\\ &\varsigma ʻ(P\unicode{x2909}Q)=\varsigma ʻP\unicode{x2909}(CʻP\cup )^;\varsigma ʻQ\end{align}\] -/
theorem pm217_22 {P Q : α → α → Prop}
    (h : (((P ∈ transR ∩ connex ∧ Q ∈ transR ∩ connex) ∧ fld P ∩ fld Q = Λ) ∧
      (refs Beg P˘).Nonempty) ∧ (refs Beg Q).Nonempty) :
    segSer (P ⤉ Q) = segSer P ⤉ (opL (· ∪ ·) (fld P) ⁏ segSer Q) := by
  obtain ⟨⟨⟨⟨hP, hQ⟩, hd⟩, ⟨e, ⟨y0, hy0⟩, he⟩⟩, ⟨b, hb⟩⟩ := h
  have hPne : rEx P := ⟨y0, e, hy0⟩
  have hQne : rEx Q := let ⟨y, hy⟩ := hb.1; ⟨b, y, hy⟩
  have hD := pm217_17 ⟨hd, Or.inr ⟨b, hb⟩⟩
  have hcpP := b2_conn_po hP.2
  have hcpQ := b2_conn_po hQ.2
  have sP : ∀ G, G ∈ dom (imgRel P) → G ∈ sect P := by
    rintro G ⟨B, rfl⟩; exact b2_img_sect hP.1 B
  have sQ : ∀ G, G ∈ dom (imgRel Q) → G ∈ sect Q := by
    rintro G ⟨B, rfl⟩; exact b2_img_sect hQ.1 B
  set D := dom (imgRel P) ∪ opL (· ∪ ·) (fld P) ʻʻ dom (imgRel Q)
  have subD : ∀ X, X ∈ D → X ⊆ fld (P ⤉ Q) := by
    rw [fld_rsum]
    rintro X (hX | ⟨G, hG, rfl⟩)
    · exact fun z hz => Or.inl (b2_seg_sub hX hz)
    · rintro z (hz | hz)
      · exact Or.inl hz
      · exact Or.inr (b2_seg_sub hG hz)
  have nestD : ∀ X Y, X ∈ D → Y ∈ D → X ⊆ Y ∨ Y ⊆ X := by
    rintro X Y (hX | ⟨G, hG, rfl⟩) (hY | ⟨H, hH, rfl⟩)
    · exact b2_nested hcpP (sP X hX) (sP Y hY)
    · exact Or.inl fun z hz => Or.inl (b2_seg_sub hX hz)
    · exact Or.inr fun z hz => Or.inl (b2_seg_sub hY hz)
    · rcases b2_nested hcpQ (sQ G hG) (sQ H hH) with hs | hs
      · exact Or.inl (Set.union_subset_union_right _ hs)
      · exact Or.inr (Set.union_subset_union_right _ hs)
  have lhs : ∀ X Y, segSer (P ⤉ Q) X Y ↔ (X ∈ D ∧ Y ∈ D) ∧ X ⊆ Y ∧ X ≠ Y := by
    intro X Y
    rw [segSer_apply, hD]
    constructor
    · rintro ⟨⟨hX, hPl⟩, hY⟩
      exact ⟨⟨hX, hY⟩, (b2_Plc_nested (subD X hX) (subD Y hY) (nestD X Y hX hY)).1 hPl⟩
    · rintro ⟨⟨hX, hY⟩, hs⟩
      exact ⟨⟨hX, (b2_Plc_nested (subD X hX) (subD Y hY) (Or.inl hs.1)).2 hs⟩, hY⟩
  have heP : e ∈ fld P := ⟨y0, Or.inr hy0⟩
  have heX : ∀ X, X ∈ dom (imgRel P) → e ∉ X := by
    rintro X ⟨B, rfl⟩ ⟨w, -, hew⟩; exact he ⟨w, hew⟩
  have disjPQ : ∀ z, z ∈ fld P → z ∈ fld Q → False := fun z h1 h2 => b2_disj hd h1 h2
  funext X Y; apply propext
  rw [lhs, rsum_apply, b2_segSer_tc hP, b2_fld_segSer_tc hP hPne, semi_apply]
  have fT : ∀ Z, Z ∈ fld (opL (· ∪ ·) (fld P) ⁏ segSer Q) ↔
      ∃ H, H ∈ dom (imgRel Q) ∧ Z = fld P ∪ H := by
    intro Z
    have := b2_semi_graph_fld (f := fun x2 : Set α => fld P ∪ x2) (Q := segSer Q) (X := Z)
    rw [b2_fld_segSer_tc hQ hQne] at this
    exact this
  rw [fT]
  constructor
  · rintro ⟨⟨hX, hY⟩, hs, hne⟩
    rcases hX with hX | ⟨G, hG, rfl⟩ <;> rcases hY with hY | ⟨H, hH, rfl⟩
    · exact Or.inl (Or.inl ⟨⟨hX, hY⟩, hs, hne⟩)
    · exact Or.inr ⟨hX, H, hH, rfl⟩
    · exact absurd (Set.Subset.antisymm hs (fun z hz => Or.inl (b2_seg_sub hY hz))) hne
    · refine Or.inl (Or.inr ⟨G, H, ⟨rfl, rfl⟩, (b2_segSer_tc hQ).2 ⟨⟨hG, hH⟩, ?_, ?_⟩⟩)
      · intro z hz
        rcases hs (Or.inr hz) with h1 | h1
        · exact (disjPQ z h1 (b2_seg_sub hG hz)).elim
        · exact h1
      · rintro rfl; exact hne rfl
  · rintro ((⟨⟨hX, hY⟩, hs, hne⟩ | ⟨G, H, ⟨rfl, rfl⟩, hGH⟩) | ⟨hX, H, hH, rfl⟩)
    · exact ⟨⟨Or.inl hX, Or.inl hY⟩, hs, hne⟩
    · obtain ⟨⟨hG, hH⟩, hs, hne⟩ := (b2_segSer_tc hQ).1 hGH
      refine ⟨⟨Or.inr ⟨G, hG, rfl⟩, Or.inr ⟨H, hH, rfl⟩⟩,
        Set.union_subset_union_right _ hs, fun e' => hne ?_⟩
      obtain ⟨z, hzH, hzG⟩ := b2_diff_of_ne hs hne
      have e2 : fld P ∪ H = fld P ∪ G := e'.symm
      have hz' : z ∈ fld P ∪ G := e2 ▸ (Or.inr hzH : z ∈ fld P ∪ H)
      exact absurd (hz'.resolve_left (fun h1 => disjPQ z h1 (b2_seg_sub hH hzH))) hzG
    · refine ⟨⟨Or.inl hX, Or.inr ⟨H, hH, rfl⟩⟩, fun z hz => Or.inl (b2_seg_sub hX hz), ?_⟩
      intro e'
      exact heX X hX (e' ▸ (Or.inl heP : e ∈ fld P ∪ H))

private theorem b2_fld_segSer_nn {Q : α → α → Prop} (h : Q ∈ transR ∩ connex)
    (h1 : dom (imgRel Q) \ ι Λ ∉ (one : Set (Set (Set α)))) :
    fld (segSer Q ⥏ (ι Λ)ᶜ) = dom (imgRel Q) \ ι Λ := by
  have hcp := b2_conn_po h.2
  have sQ : ∀ G, G ∈ dom (imgRel Q) → G ∈ sect Q := by
    rintro G ⟨B, rfl⟩; exact b2_img_sect h.1 B
  ext H
  constructor
  · rintro ⟨K, ⟨⟨hH, hHK⟩, -⟩ | ⟨⟨-, hKH⟩, hH⟩⟩
    · exact ⟨((b2_segSer_tc h).1 hHK).1.1, hH⟩
    · exact ⟨((b2_segSer_tc h).1 hKH).1.2, hH⟩
  · intro hH
    have : ∃ K, K ∈ dom (imgRel Q) \ ι Λ ∧ K ≠ H := by
      by_contra hn; push Not at hn
      exact h1 ⟨H, Set.ext fun K => ⟨fun hK => hn K hK, fun hK => (b2_mem_iota.1 hK) ▸ hH⟩⟩
    obtain ⟨K, hK, hKH⟩ := this
    rcases b2_nested hcp (sQ H hH.1) (sQ K hK.1) with hs | hs
    · exact ⟨K, Or.inl ⟨⟨hH.2, (b2_segSer_tc h).2 ⟨⟨hH.1, hK.1⟩, hs, Ne.symm hKH⟩⟩, hK.2⟩⟩
    · exact ⟨K, Or.inr ⟨⟨hK.2, (b2_segSer_tc h).2 ⟨⟨hK.1, hH.1⟩, hs, hKH⟩⟩, hH.2⟩⟩

/-- ✱217·23. \[\begin{align}\vdash \colon\ldotp P,Q\in \text{trans}\cap \text{connex} .&CʻP\cap CʻQ=\Lambda :{\sim}\exists !\overrightarrow{B}ʻ\breve{P} .\lor.{\sim}\exists !\overrightarrow{B}ʻQ:\supset .\\ &\varsigma ʻ(P\unicode{x2909}Q)=\varsigma ʻP\unicode{x2909}(CʻP\cup )^{;}(\varsigma ʻQ)\unicode{x0294f}(-{℩}ʻ\Lambda )\end{align}\]

**Status.** proved (corrected): false as printed in two degenerate cases, so the hypotheses `∃̇!P` and `D'Q_∈ − ι'Λ ∼∈ 1` are added. If `P = Λ̇` and `Q` has a non-null segment, `ς'(P ⤉ Q) = ς'Q` relates `Λ` to it, but the right side omits `Λ`; if `P` has no last term and `Q = x ↓ y` (one non-null segment `ι'x`), the pair `(P''β, C'P ∪ ι'x)` is lost, since `(ς'Q)⥏(−ι'Λ) = Λ̇`. -/
theorem pm217_23 {P Q : α → α → Prop}
    (h : ((P ∈ transR ∩ connex ∧ Q ∈ transR ∩ connex) ∧ fld P ∩ fld Q = Λ) ∧
      (¬(refs Beg P˘).Nonempty ∨ ¬(refs Beg Q).Nonempty))
    (hP : rEx P) (hQ1 : dom (imgRel Q) \ ι Λ ∉ (one : Set (Set (Set α)))) :
    segSer (P ⤉ Q) = segSer P ⤉ (opL (· ∪ ·) (fld P) ⁏ (segSer Q ⥏ (ι Λ)ᶜ)) := by
  obtain ⟨⟨⟨hPt, hQt⟩, hd⟩, hor⟩ := h
  have hD := pm217_18 ⟨hd, hor⟩
  have hcpP := b2_conn_po hPt.2
  have hcpQ := b2_conn_po hQt.2
  have sP : ∀ G, G ∈ dom (imgRel P) → G ∈ sect P := by
    rintro G ⟨B, rfl⟩; exact b2_img_sect hPt.1 B
  have sQ : ∀ G, G ∈ dom (imgRel Q) → G ∈ sect Q := by
    rintro G ⟨B, rfl⟩; exact b2_img_sect hQt.1 B
  have disjPQ : ∀ z, z ∈ fld P → z ∈ fld Q → False := fun z h1 h2 => b2_disj hd h1 h2
  set D := dom (imgRel P) ∪ opL (· ∪ ·) (fld P) ʻʻ (dom (imgRel Q) \ ι Λ)
  have subD : ∀ X, X ∈ D → X ⊆ fld (P ⤉ Q) := by
    rw [fld_rsum]
    rintro X (hX | ⟨G, hG, rfl⟩)
    · exact fun z hz => Or.inl (b2_seg_sub hX hz)
    · rintro z (hz | hz)
      · exact Or.inl hz
      · exact Or.inr (b2_seg_sub hG.1 hz)
  have nestD : ∀ X Y, X ∈ D → Y ∈ D → X ⊆ Y ∨ Y ⊆ X := by
    rintro X Y (hX | ⟨G, hG, rfl⟩) (hY | ⟨H, hH, rfl⟩)
    · exact b2_nested hcpP (sP X hX) (sP Y hY)
    · exact Or.inl fun z hz => Or.inl (b2_seg_sub hX hz)
    · exact Or.inr fun z hz => Or.inl (b2_seg_sub hY hz)
    · rcases b2_nested hcpQ (sQ G hG.1) (sQ H hH.1) with hs | hs
      · exact Or.inl (Set.union_subset_union_right _ hs)
      · exact Or.inr (Set.union_subset_union_right _ hs)
  have lhs : ∀ X Y, segSer (P ⤉ Q) X Y ↔ (X ∈ D ∧ Y ∈ D) ∧ X ⊆ Y ∧ X ≠ Y := by
    intro X Y
    rw [segSer_apply, hD]
    constructor
    · rintro ⟨⟨hX, hPl⟩, hY⟩
      exact ⟨⟨hX, hY⟩, (b2_Plc_nested (subD X hX) (subD Y hY) (nestD X Y hX hY)).1 hPl⟩
    · rintro ⟨⟨hX, hY⟩, hs⟩
      exact ⟨⟨hX, (b2_Plc_nested (subD X hX) (subD Y hY) (Or.inl hs.1)).2 hs⟩, hY⟩
  have fT : ∀ Z, Z ∈ fld (opL (· ∪ ·) (fld P) ⁏ (segSer Q ⥏ (ι Λ)ᶜ)) ↔
      ∃ H, H ∈ dom (imgRel Q) \ ι Λ ∧ Z = fld P ∪ H := by
    intro Z
    have := b2_semi_graph_fld (f := fun x2 : Set α => fld P ∪ x2) (Q := segSer Q ⥏ (ι Λ)ᶜ)
      (X := Z)
    rw [b2_fld_segSer_nn hQt hQ1] at this
    exact this
  funext X Y; apply propext
  rw [lhs, rsum_apply, b2_segSer_tc hPt, b2_fld_segSer_tc hPt hP, semi_apply, fT]
  constructor
  · rintro ⟨⟨hX, hY⟩, hs, hne⟩
    rcases hX with hX | ⟨G, hG, rfl⟩ <;> rcases hY with hY | ⟨H, hH, rfl⟩
    · exact Or.inl (Or.inl ⟨⟨hX, hY⟩, hs, hne⟩)
    · exact Or.inr ⟨hX, H, hH, rfl⟩
    · exact absurd (Set.Subset.antisymm hs (fun z hz => Or.inl (b2_seg_sub hY hz))) hne
    · refine Or.inl (Or.inr ⟨G, H, ⟨rfl, rfl⟩, ⟨⟨hG.2, (b2_segSer_tc hQt).2
        ⟨⟨hG.1, hH.1⟩, ?_, ?_⟩⟩, hH.2⟩⟩)
      · intro z hz
        rcases hs (Or.inr hz) with h1 | h1
        · exact (disjPQ z h1 (b2_seg_sub hG.1 hz)).elim
        · exact h1
      · rintro rfl; exact hne rfl
  · rintro ((⟨⟨hX, hY⟩, hs, hne⟩ | ⟨G, H, ⟨rfl, rfl⟩, ⟨⟨hG0, hGH⟩, hH0⟩⟩) | ⟨hX, H, hH, rfl⟩)
    · exact ⟨⟨Or.inl hX, Or.inl hY⟩, hs, hne⟩
    · obtain ⟨⟨hG, hH⟩, hs, hne⟩ := (b2_segSer_tc hQt).1 hGH
      refine ⟨⟨Or.inr ⟨G, ⟨hG, hG0⟩, rfl⟩, Or.inr ⟨H, ⟨hH, hH0⟩, rfl⟩⟩,
        Set.union_subset_union_right _ hs, fun e' => hne ?_⟩
      obtain ⟨z, hzH, hzG⟩ := b2_diff_of_ne hs hne
      have e2 : fld P ∪ H = fld P ∪ G := e'.symm
      have hz' : z ∈ fld P ∪ G := e2 ▸ (Or.inr hzH : z ∈ fld P ∪ H)
      exact absurd (hz'.resolve_left (fun h1 => disjPQ z h1 (b2_seg_sub hH hzH))) hzG
    · refine ⟨⟨Or.inl hX, Or.inr ⟨H, hH, rfl⟩⟩, fun z hz => Or.inl (b2_seg_sub hX hz), ?_⟩
      intro e'
      obtain ⟨z, hz⟩ := b2_not_mem_iotaNull.1 hH.2
      have : z ∈ X := by rw [e']; exact Or.inr hz
      exact disjPQ z (b2_seg_sub hX this) (b2_seg_sub hH.1 hz)

/-- ✱217·24. \(\vdash :\alpha \cap \beta =\Lambda .\supset .(\alpha \cup )\upharpoonright ʻ\text{Cl}ʻ\beta \in 1\rightarrow 1 \quad[*24·481]\) -/
theorem pm217_24 {A B : Set α} (h : A ∩ B = Λ) : opL (· ∪ ·) A ↾ cl B ∈ arrow one one := by
  rw [mem_arrow_one_one]
  constructor
  · rintro X Y G ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    exact h1.trans h2.symm
  rintro X G H ⟨⟨h1, hG⟩, ⟨h2, hH⟩⟩
  have e : A ∪ G = A ∪ H := h1.symm.trans h2
  have key : ∀ K : Set α, K ⊆ B → (A ∪ K) ∩ B = K := by
    intro K hK
    ext z
    constructor
    · rintro ⟨hz | hz, hzB⟩
      · have : z ∈ A ∩ B := ⟨hz, hzB⟩
        rw [h, Null_eq_empty] at this; exact this.elim
      · exact hz
    · intro hz; exact ⟨Or.inr hz, hK hz⟩
  rw [← key G hG, ← key H hH, e]

private theorem b2_fld_segSer_sub {Q : α → α → Prop} {G : Set α} (h : G ∈ fld (segSer Q)) :
    G ∈ cl (fld Q) := by
  obtain ⟨H, ⟨⟨⟨B, rfl⟩, -⟩, -⟩ | ⟨⟨-, -⟩, ⟨B, rfl⟩⟩⟩ := h <;>
    exact fun z ⟨y, _, hzy⟩ => ⟨y, Or.inl hzy⟩

/-- ✱217·25. \[\begin{align}&\vdash :CʻP\cap CʻQ=\Lambda .\supset .(CʻP\cup )\upharpoonright Cʻ\varsigma ʻQ\in \{(CʻP\cup )^{;}\varsigma ʻQ\}\overline{\,\text{smor}\,} (\varsigma ʻQ)\\ &[*217·24]\end{align}\] -/
theorem pm217_25 {P Q : α → α → Prop} (h : fld P ∩ fld Q = Λ) :
    opL (· ∪ ·) (fld P) ↾ fld (segSer Q) ∈
      smorbar (opL (· ∪ ·) (fld P) ⁏ segSer Q) (segSer Q) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 := pm217_24 h
    rw [mem_arrow_one_one] at h1 ⊢
    exact ⟨fun x y z hxyz => h1.1 x y z ⟨⟨hxyz.1.1, b2_fld_segSer_sub hxyz.1.2⟩,
      ⟨hxyz.2.1, b2_fld_segSer_sub hxyz.2.2⟩⟩,
      fun x y z hxyz => h1.2 x y z ⟨⟨hxyz.1.1, b2_fld_segSer_sub hxyz.1.2⟩,
      ⟨hxyz.2.1, b2_fld_segSer_sub hxyz.2.2⟩⟩⟩
  · ext G
    exact ⟨fun hG => ⟨fld P ∪ G, rfl, hG⟩, fun ⟨_, _, hG⟩ => hG⟩
  · funext X Y; apply propext
    rw [semi_apply, semi_apply]
    constructor
    · rintro ⟨G, H, ⟨hX, hY⟩, hGH⟩
      exact ⟨G, H, ⟨⟨hX, ⟨H, Or.inl hGH⟩⟩, ⟨hY, ⟨G, Or.inr hGH⟩⟩⟩, hGH⟩
    · rintro ⟨G, H, ⟨⟨hX, -⟩, ⟨hY, -⟩⟩, hGH⟩
      exact ⟨G, H, ⟨hX, hY⟩, hGH⟩

/-- ✱217·3. \[\begin{align}&\vdash :P\in \text{Ser}.\supset .\text{ᗡ}ʻP_{\in }=\overrightarrow{P}ʻʻCʻP\cup \text{D}ʻ(P_{\in }\dot{\cap} I)-\text{ᗡ}ʻ\text{seq}_{P}\\ &[*211·32·302·41]\end{align}\]

**Status.** proved (reading): the e-text prints `ᗡ'P_∈` (which is every class) for `D'P_∈`, the segments; PM's proof [✱211·32·302·41] and ✱217·31 concern segments. `P⃗''C'P ∪ D'(P_∈ ∩̇ I) − ᗡ'seq_P` is `P⃗''C'P ∪ (D'(P_∈ ∩̇ I) − ᗡ'seq_P)`. -/
theorem pm217_3 {P : α → α → Prop} (h : P ∈ Ser) :
    dom (imgRel P) = Rfwd P ʻʻ fld P ∪ dom (imgRel P ⩀ I) \ codom (seqP P) := by
  ext G
  constructor
  · intro hG
    have hs := b2_seg_sect h hG
    by_cases hq : ∃ x, seqP P x G
    · obtain ⟨x, hx⟩ := hq
      exact Or.inl ⟨x, (seqP_iff.1 hx).1.2, b2_sect_eq_refs h hs hx⟩
    · have hm : ¬∃ m, maxP P m G := by
        rintro ⟨m, hm⟩
        obtain ⟨B, rfl⟩ := hG
        exact hq (b2_seq_of_maxSeg h hm)
      exact Or.inr ⟨mem_dom_imgRel_rcap_I.2 (b2_fixed_of_noMax hs hm), hq⟩
  · rintro (⟨x, -, rfl⟩ | ⟨hG, -⟩)
    · exact b2_refs_mem_dom_img P x
    · exact ⟨G, mem_dom_imgRel_rcap_I.1 hG⟩

private theorem b2_cnv_ser' {P : α → α → Prop} (h : P ∈ Ser) : P˘ ∈ Ser := b2_cnv_ser h

/-- ✱217·301. \(\vdash :P\in \text{Ser}.\gamma \in \text{D}ʻ(P_{\in }\dot{\cap} I)-\text{ᗡ}ʻ\text{seq}_{P}.\supset .\gamma =CʻP-\breve{P} ʻʻ(CʻP-\gamma )\) -/
theorem pm217_301 {P : α → α → Prop} {G : Set α}
    (h : P ∈ Ser ∧ G ∈ dom (imgRel P ⩀ I) \ codom (seqP P)) :
    G = fld P \ P˘ ʻʻ (fld P \ G) := by
  obtain ⟨hs, hG, hq⟩ := h
  have hfix := mem_dom_imgRel_rcap_I.1 hG
  have hsect := b2_seg_sect hs ⟨G, hfix⟩
  have hu := b2_upper_sect hsect
  have hnmin : ¬∃ n, maxP P˘ n (fld P \ G) := by
    rintro ⟨n, hn⟩
    exact hq ⟨n, (b2_seq_sect (b2_irr_of_ser hs) hs.2 hsect).2 hn⟩
  have e := b2_fixed_of_noMax hu hnmin
  rw [← e, Set.sdiff_sdiff_cancel_left hsect.1]

/-- ✱217·31. \(\vdash :P\in \text{Ser}.\gamma \in \text{D}ʻP_{\in }.\supset .(\exists \beta ).\gamma =Pʻʻ(CʻP-\breve{P} ʻʻ\beta )\) -/
theorem pm217_31 {P : α → α → Prop} {G : Set α} (h : P ∈ Ser ∧ G ∈ dom (imgRel P)) :
    ∃ B, G = P ʻʻ (fld P \ P˘ ʻʻ B) := by
  obtain ⟨hs, hG⟩ := h
  have tr := mem_transR.1 hs.1.2
  have hirr := b2_irr_of_ser hs
  rw [pm217_3 hs] at hG
  rcases hG with ⟨x, hx, rfl⟩ | hG
  · refine ⟨rels (anc P) x, ?_⟩
    ext w
    constructor
    · intro hwx
      refine ⟨x, ⟨hx, ?_⟩, hwx⟩
      rintro ⟨b, hb, hbx⟩
      rcases (anc_iff_of_transR hs.1.2).1 hb with ⟨rfl, -⟩ | hxb
      · exact hirr _ hbx
      · exact hirr x (tr x b x ⟨hxb, hbx⟩)
    · rintro ⟨z, ⟨hz, hzn⟩, hwz⟩
      rcases mem_connex.1 hs.2 z x ⟨hz, hx⟩ with (h1 | rfl) | h1
      · exact tr w z x ⟨hwz, h1⟩
      · exact hwz
      · exact absurd ⟨x, (anc_iff_of_transR hs.1.2).2 (Or.inl ⟨rfl, hx⟩), h1⟩ hzn
  · refine ⟨fld P \ G, ?_⟩
    rw [← pm217_301 ⟨hs, hG⟩]
    exact mem_dom_imgRel_rcap_I.1 hG.1

private theorem b2_mem_opL_diff {P : α → α → Prop} {K : Set (Set α)} {Y : Set α} :
    Y ∈ opL (· \ ·) (fld P) ʻʻ K ↔ ∃ G, G ∈ K ∧ Y = fld P \ G := Iff.rfl

/-- ✱217·32. \(\vdash :P\in \text{Ser}.\supset .\text{D}ʻ(\breve{P} )_{\in }=(\breve{P} )_{\in }ʻʻ(CʻP-)ʻʻ\text{D}ʻP_{\in }\) -/
theorem pm217_32 {P : α → α → Prop} (h : P ∈ Ser) :
    dom (imgRel P˘) = imgRel P˘ ʻʻ (opL (· \ ·) (fld P) ʻʻ dom (imgRel P)) := by
  ext X
  constructor
  · intro hX
    obtain ⟨B, hB⟩ := pm217_31 ⟨b2_cnv_ser h, hX⟩
    rw [fld_cnv, b2_cnv_cnv] at hB
    exact ⟨_, ⟨P ʻʻ B, ⟨B, rfl⟩, rfl⟩, hB⟩
  · rintro ⟨Y, -, hXY⟩; exact ⟨Y, hXY⟩

/-- ✱217·33. \(\vdash .(\alpha -)\upharpoonright \text{Cl}ʻ\alpha \in 1\rightarrow 1\) -/
theorem pm217_33 {A : Set α} : opL (· \ ·) A ↾ cl A ∈ arrow one one := by
  rw [mem_arrow_one_one]
  constructor
  · rintro X Y G ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    exact h1.trans h2.symm
  · rintro X G H ⟨⟨h1, hG⟩, ⟨h2, hH⟩⟩
    have e : A \ G = A \ H := h1.symm.trans h2
    rw [← Set.sdiff_sdiff_cancel_left (mem_cl.1 hG), ← Set.sdiff_sdiff_cancel_left (mem_cl.1 hH), e]

/-- `P''α` for a section `α` of a series: `P⃗'max` if there is a maximum, `α` otherwise. -/
private theorem b2_img_sect_max {P : α → α → Prop} (h : P ∈ Ser) {A : Set α} (hA : A ∈ sect P) {m : α}
    (hm : maxP P m A) : P ʻʻ A = refs P m ∧ A = insert m (refs P m) := by
  have tr := mem_transR.1 h.1.2
  rw [maxP_iff] at hm
  have below : ∀ a, a ∈ A → a = m ∨ P a m := by
    intro a ha
    rcases mem_connex.1 h.2 a m ⟨hA.1 ha, hm.1.2⟩ with (h1 | h1) | h1
    · exact Or.inr h1
    · exact Or.inl h1
    · exact absurd h1 (hm.2 a ha)
  constructor
  · ext w
    constructor
    · rintro ⟨a, ha, hwa⟩
      rcases below a ha with rfl | h1
      · exact hwa
      · exact tr w a m ⟨hwa, h1⟩
    · intro hwm; exact ⟨m, hm.1.1, hwm⟩
  · ext a
    constructor
    · intro ha
      rcases below a ha with rfl | h1
      · exact Or.inl rfl
      · exact Or.inr h1
    · rintro (rfl | h1)
      · exact hm.1.1
      · exact b2_sect_P hA h1 hm.1.1

/-- ✱217·34. \(\vdash :P\in \text{Ser}.\supset .P_{\in }\upharpoonright (\text{sect}ʻP-\text{ᗡ}ʻ\text{lt}_P)\in 1\rightarrow 1\) -/
theorem pm217_34 {P : α → α → Prop} (h : P ∈ Ser) :
    imgRel P ↾ (sect P \ codom (ltP P)) ∈ arrow one one := by
  have hirr := b2_irr_of_ser h
  rw [mem_arrow_one_one]
  constructor
  · rintro X Y G ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    exact h1.trans h2.symm
  · rintro X A1 A2 ⟨⟨h1, hA1, hl1⟩, ⟨h2, hA2, hl2⟩⟩
    have e : P ʻʻ A1 = P ʻʻ A2 := h1.symm.trans h2
    have refsInj : ∀ m m', m ∈ fld P → m' ∈ fld P → refs P m = refs P m' → m = m' := by
      intro m m' hm hm' e'
      rcases mem_connex.1 h.2 m m' ⟨hm, hm'⟩ with (h3 | h3) | h3
      · have : m ∈ refs P m := e' ▸ h3
        exact absurd this (hirr m)
      · exact h3
      · have : m' ∈ refs P m' := e'.symm ▸ h3
        exact absurd this (hirr m')
    have noMaxCase : ∀ A B m, A ∈ sect P → B ∈ sect P → maxP P m A → (¬∃ m', maxP P m' B) →
        B ∉ codom (ltP P) → P ʻʻ A = P ʻʻ B → False := by
      intro A B m hA hB hm hn hl e'
      rw [(b2_img_sect_max h hA hm).1, ← b2_fixed_of_noMax hB hn] at e'
      have hmf := (maxP_iff.1 hm).1.2
      exact hl ⟨m, by rw [← e']; exact b2_seq_refs h hmf, fun hh => hn (e' ▸ hh)⟩
    by_cases hm1 : ∃ m, maxP P m A1 <;> by_cases hm2 : ∃ m, maxP P m A2
    · obtain ⟨m1, hm1⟩ := hm1
      obtain ⟨m2, hm2⟩ := hm2
      have f1 := b2_img_sect_max h hA1 hm1
      have f2 := b2_img_sect_max h hA2 hm2
      rw [f1.1, f2.1] at e
      have := refsInj m1 m2 (maxP_iff.1 hm1).1.2 (maxP_iff.1 hm2).1.2 e
      subst this
      rw [f1.2, f2.2]
    · obtain ⟨m1, hm1⟩ := hm1
      exact (noMaxCase A1 A2 m1 hA1 hA2 hm1 hm2 hl2 e).elim
    · obtain ⟨m2, hm2⟩ := hm2
      exact (noMaxCase A2 A1 m2 hA2 hA1 hm2 hm1 hl1 e.symm).elim
    · rw [← b2_fixed_of_noMax hA1 hm1, ← b2_fixed_of_noMax hA2 hm2] at e
      exact e

/-- The complement of a segment of a series is a section of `P̆` without a limit in `P̆`. -/
private theorem b2_compl_seg {P : α → α → Prop} (h : P ∈ Ser) {G : Set α} (hG : G ∈ dom (imgRel P)) :
    fld P \ G ∈ sect P˘ \ codom (ltP P˘) := by
  have hs := b2_seg_sect h hG
  refine ⟨b2_upper_sect hs, ?_⟩
  rintro ⟨x, hseq, hnm⟩
  rw [pm217_3 h] at hG
  rcases hG with ⟨y, hy, rfl⟩ | ⟨hfix, hq⟩
  · refine hnm ⟨y, ?_⟩
    show minP P y (fld P \ refs P y)
    rw [minP_iff]
    exact ⟨⟨⟨hy, b2_irr_of_ser h y⟩, hy⟩, fun z hz hzy => hz.2 hzy⟩
  · have hprec : precP P x (fld P \ G) := by rw [precP_eq_seqP_cnv]; exact hseq
    have : maxP P x (prodCls (Rfwd P ʻʻ ((fld P \ G) ∩ fld P))) := hprec
    rw [b2_maxP_inter, b2_pred_cls h hs] at this
    exact b2_noMax_fixed (mem_dom_imgRel_rcap_I.1 hfix) ⟨x, this⟩

private theorem b2_rel35 {P : α → α → Prop} {X G : Set α} :
    ((imgRel P˘ ⨾ opL (· \ ·) (fld P)) ↾ dom (imgRel P)) X G ↔
      X = P˘ ʻʻ (fld P \ G) ∧ G ∈ dom (imgRel P) := by
  constructor
  · rintro ⟨⟨Y, hXY, hY⟩, hG⟩
    rw [show Y = fld P \ G from hY] at hXY
    exact ⟨hXY, hG⟩
  · rintro ⟨hX, hG⟩; exact ⟨⟨fld P \ G, hX, rfl⟩, hG⟩

/-- ✱217·35. \(\vdash :P\in \text{Ser}.\supset .(\breve{P} )_{\in }\mid (CʻP-)\upharpoonright \text{D}ʻP_{\in }\in 1\rightarrow 1\) -/
theorem pm217_35 {P : α → α → Prop} (h : P ∈ Ser) :
    (imgRel P˘ ⨾ opL (· \ ·) (fld P)) ↾ dom (imgRel P) ∈ arrow one one := by
  have h34 := mem_arrow_one_one.1 (pm217_34 (b2_cnv_ser h))
  rw [mem_arrow_one_one]
  constructor
  · intro X Y G ⟨h1, h2⟩
    rw [b2_rel35] at h1 h2
    exact h1.1.trans h2.1.symm
  · intro X G H ⟨h1, h2⟩
    rw [b2_rel35] at h1 h2
    have := h34.2 X (fld P \ G) (fld P \ H)
      ⟨⟨h1.1, b2_compl_seg h h1.2⟩, ⟨h2.1, b2_compl_seg h h2.2⟩⟩
    rw [← Set.sdiff_sdiff_cancel_left (b2_seg_sect h h1.2).1,
      ← Set.sdiff_sdiff_cancel_left (b2_seg_sect h h2.2).1, this]

/-- ✱217·36. \(\vdash :P\in \text{Ser}.\supset .\varsigma ʻ\breve{P} =(\breve{P} )_{\in }^{;}(CʻP-)^{;}\text{Cnv}ʻ\varsigma ʻP\) -/
theorem pm217_36 {P : α → α → Prop} (h : P ∈ Ser) :
    segSer P˘ = imgRel P˘ ⁏ opL (· \ ·) (fld P) ⁏ (segSer P)˘ := by
  have h' := b2_cnv_ser h
  have inj := mem_arrow_one_one.1 (pm217_35 h)
  have hcp := b2_conn_po h.2
  funext X Y; apply propext
  rw [b2_segSer_ser h', semi_apply]
  constructor
  · rintro ⟨⟨hX, hY⟩, hs, hne⟩
    rw [pm217_32 h] at hX hY
    obtain ⟨U, ⟨G, hG, rfl⟩, hXU⟩ := hX
    obtain ⟨V, ⟨H, hH, rfl⟩, hYV⟩ := hY
    refine ⟨fld P \ G, fld P \ H, ⟨hXU, hYV⟩, (semi_apply _ _ _ _).2 ⟨G, H, ⟨rfl, rfl⟩, ?_⟩⟩
    show segSer P H G
    rw [b2_segSer_ser h]
    have hGH : G ≠ H := by rintro rfl; exact hne (hXU.trans hYV.symm)
    refine ⟨⟨hH, hG⟩, ?_, Ne.symm hGH⟩
    rcases b2_nested hcp (b2_seg_sect h hG) (b2_seg_sect h hH) with hs' | hs'
    · exfalso
      have : Y ⊆ X := by
        rw [hXU, hYV]
        exact fun z ⟨w, hw, hzw⟩ => ⟨w, ⟨hw.1, fun hwG => hw.2 (hs' hwG)⟩, hzw⟩
      exact hne (Set.Subset.antisymm hs this)
    · exact hs'
  · rintro ⟨U, V, ⟨hXU, hYV⟩, hUV⟩
    obtain ⟨G, H, ⟨rfl, rfl⟩, hHG⟩ := (semi_apply _ _ _ _).1 hUV
    have hHG' : segSer P H G := hHG
    rw [b2_segSer_ser h] at hHG'
    obtain ⟨⟨hH, hG⟩, hs, hne⟩ := hHG'
    refine ⟨⟨⟨_, hXU⟩, ⟨_, hYV⟩⟩, ?_, fun e => hne ?_⟩
    · rw [hXU, hYV]
      exact fun z ⟨w, hw, hzw⟩ => ⟨w, ⟨hw.1, fun hwH => hw.2 (hs hwH)⟩, hzw⟩
    · exact (inj.2 X G H ⟨b2_rel35.2 ⟨hXU, hG⟩, b2_rel35.2 ⟨e ▸ hYV, hH⟩⟩).symm

/-- ✱217·37. \[\begin{align}&\vdash :P\in \text{Ser}.\supset .(\breve{P} )_{\in }\mid (CʻP-)\upharpoonright \text{D}ʻP_{\in }\in (\varsigma ʻ\breve{P} )\overline{\,\text{smor}\,} (\text{Cnv}ʻ\varsigma ʻP)\\ &[*217·35·36]\end{align}\]

**Status.** proved (corrected): false for `P = Λ̇` (then `ς'P = Λ̇` has no field, while the correlator relates `Λ` to `Λ`); the hypothesis `∃̇!P` is added; `pm217_37_printed_false` proves the failure (for `P = Λ̇` on `Bool`). ✱217·38 holds in all cases. -/
theorem pm217_37 {P : α → α → Prop} (h : P ∈ Ser ∧ rEx P) :
    (imgRel P˘ ⨾ opL (· \ ·) (fld P)) ↾ dom (imgRel P) ∈ smorbar (segSer P˘) ((segSer P)˘) := by
  obtain ⟨h, hP⟩ := h
  refine ⟨⟨pm217_35 h, ?_⟩, ?_⟩
  · have : fld ((segSer P)˘) = fld (segSer P) := fld_cnv _
    rw [this, b2_fld_segSer_ser h hP]
    ext G
    exact ⟨fun hG => ⟨_, b2_rel35.2 ⟨rfl, hG⟩⟩, fun ⟨X, hX⟩ => (b2_rel35.1 hX).2⟩
  · rw [pm217_36 h]
    funext X Y; apply propext
    rw [semi_apply, semi_apply]
    constructor
    · rintro ⟨U, V, ⟨hXU, hYV⟩, hUV⟩
      obtain ⟨G, H, ⟨rfl, rfl⟩, hHG⟩ := (semi_apply _ _ _ _).1 hUV
      have hHG' : segSer P H G := hHG
      obtain ⟨⟨hH, hG⟩, -⟩ := (b2_segSer_ser h).1 hHG'
      exact ⟨G, H, ⟨b2_rel35.2 ⟨hXU, hG⟩, b2_rel35.2 ⟨hYV, hH⟩⟩, hHG⟩
    · rintro ⟨G, H, ⟨hX, hY⟩, hHG⟩
      obtain ⟨hX, -⟩ := b2_rel35.1 hX
      obtain ⟨hY, -⟩ := b2_rel35.1 hY
      exact ⟨fld P \ G, fld P \ H, ⟨hX, hY⟩, (semi_apply _ _ _ _).2 ⟨G, H, ⟨rfl, rfl⟩, hHG⟩⟩

private theorem b2_217_37_null_fails :
    ¬(((imgRel (rNull : Bool → Bool → Prop)˘ ⨾ opL (· \ ·) (fld (rNull : Bool → Bool → Prop))) ↾
      dom (imgRel (rNull : Bool → Bool → Prop))) ∈
        smorbar (segSer (rNull : Bool → Bool → Prop)˘) ((segSer (rNull : Bool → Bool → Prop))˘)) := by
  rintro ⟨⟨-, hc⟩, -⟩
  have h0 : (∅ : Set Bool) ∈ codom ((imgRel (rNull : Bool → Bool → Prop)˘ ⨾
      opL (· \ ·) (fld (rNull : Bool → Bool → Prop))) ↾ dom (imgRel (rNull : Bool → Bool → Prop))) :=
    ⟨_, b2_rel35.2 ⟨rfl, ⟨∅, Set.ext fun z => ⟨fun h => h.elim, fun ⟨_, h, _⟩ => h⟩⟩⟩⟩
  rw [← hc] at h0
  have hY0 : ∀ X Y, ¬segSer (rNull : Bool → Bool → Prop) X Y := by
    intro X Y h
    obtain ⟨-, z, ⟨hz, -⟩, -⟩ := h.1.2
    obtain ⟨B, hB⟩ := h.2
    have : z ∈ (rNull : Bool → Bool → Prop) ʻʻ B := (show Y = _ from hB) ▸ hz
    obtain ⟨w, -, hw⟩ := this; exact hw ⟨rfl, rfl⟩
  obtain ⟨Y, hY | hY⟩ := h0
  · exact hY0 _ _ hY
  · exact hY0 _ _ hY

/-- The printed ✱217·37 fails: `Λ̇` (on `Bool`) is a series, but its correlator relates `Λ` to `Λ`
while `ς'Λ̇` has no field. -/
theorem pm217_37_printed_false :
    ¬∀ P : Bool → Bool → Prop, P ∈ Ser →
      (imgRel P˘ ⨾ opL (· \ ·) (fld P)) ↾ dom (imgRel P) ∈ smorbar (segSer P˘) ((segSer P)˘) := by
  intro h
  have hn : ∀ x y : Bool, ¬(rNull : Bool → Bool → Prop) x y := b2_eq_rNull.1 rfl
  have hS : (rNull : Bool → Bool → Prop) ∈ Ser := by
    refine mem_Ser.2 ⟨⟨fun x => hn x x, fun x y z hxyz => (hn x y hxyz.1).elim⟩, ?_⟩
    rintro x y ⟨⟨w, hw | hw⟩, -⟩
    · exact (hn _ _ hw).elim
    · exact (hn _ _ hw).elim
  exact b2_217_37_null_fails (h _ hS)

/-- ✱217·38. \(\vdash :P\in \text{Ser}.\supset .(\varsigma ʻ\breve{P} )\,\text{smor}\,(\text{Cnv}ʻ\varsigma ʻP) \quad[*217·37]\) -/
theorem pm217_38 {P : α → α → Prop} (h : P ∈ Ser) : smor (segSer P˘) ((segSer P)˘) := by
  by_cases hP : rEx P
  · exact ⟨_, pm217_37 ⟨h, hP⟩⟩
  · have e : P = rNull := b2_eq_rNull.2 fun x y hxy => hP ⟨x, y, hxy⟩
    have n1 : segSer P˘ = rNull := by
      rw [b2_eq_rNull]
      intro X Y hXY
      obtain ⟨-, z, ⟨hz, -⟩, -⟩ := hXY.1.2
      obtain ⟨B, hB⟩ := hXY.2
      have : z ∈ P˘ ʻʻ B := hB ▸ hz
      obtain ⟨w, -, hw⟩ := this
      exact hP ⟨w, z, hw⟩
    have n2 : (segSer P)˘ = rNull := by
      rw [b2_eq_rNull]
      intro X Y hXY
      obtain ⟨-, z, ⟨hz, -⟩, -⟩ := hXY.1.2
      obtain ⟨B, hB⟩ := hXY.2
      have : z ∈ P ʻʻ B := hB ▸ hz
      obtain ⟨w, -, hw⟩ := this
      exact hP ⟨z, w, hw⟩
    rw [n1, n2]
    exact smor_refl _

/-- ✱217·4. \[\begin{align}\vdash :&P,Q\in \text{Ser}.CʻP\cap CʻQ=\Lambda .\text{E}!BʻP.\text{E}!BʻQ.\supset .\\ &\varsigma ʻ(\breve{P} \unicode{x2909} Q)=(\breve{P} )_{\in }^{;}(CʻP-)^{;}\text{Cnv}ʻ\varsigma ʻP\unicode{x2909} (CʻP\cup )^{;}\varsigma ʻQ \quad[*217·22·36]\end{align}\] -/
theorem pm217_4 {P Q : α → α → Prop}
    (h : (((P ∈ Ser ∧ Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) ∧ EDesc Beg P) ∧ EDesc Beg Q) :
    segSer (P˘ ⤉ Q) =
      imgRel P˘ ⁏ opL (· \ ·) (fld P) ⁏ (segSer P)˘ ⤉ opL (· ∪ ·) (fld P) ⁏ segSer Q := by
  obtain ⟨⟨⟨⟨hP, hQ⟩, hd⟩, hbP⟩, hbQ⟩ := h
  obtain ⟨b, hb⟩ := b2_EDesc_iff.1 hbP
  obtain ⟨c, hc⟩ := b2_EDesc_iff.1 hbQ
  have hP' := b2_cnv_ser hP
  have := pm217_22 (P := P˘) (Q := Q) ⟨⟨⟨⟨⟨hP'.1.2, hP'.2⟩, ⟨hQ.1.2, hQ.2⟩⟩, by rw [fld_cnv]; exact hd⟩,
    ⟨b, b2_mem_of_refs_eq (R := Beg) (y := P) hb⟩⟩, ⟨c, b2_mem_of_refs_eq (R := Beg) (y := Q) hc⟩⟩
  rw [this, pm217_36 hP, fld_cnv]

/-- ✱217·41. \[\begin{align}\vdash \colon\ldotp &P,Q\in \text{Ser}.CʻP\cap CʻQ=\Lambda :{\sim}\text{E}!BʻP.\lor.{\sim}\text{E}!BʻQ:\supset .\\ &\varsigma ʻ(\breve{P} \unicode{x2909} Q)=(\breve{P} )_{\in }^{;}(CʻP-)^{;}\text{Cnv}ʻ\varsigma ʻP\unicode{x2909} (CʻP\cup )^{;}(\varsigma ʻQ)\unicode{x0294f}(-{℩}ʻ\Lambda ) &[*217·23·36]\end{align}\]

**Status.** proved (corrected): ✱217·23 applied to `P̆`, so it needs the same added hypotheses `∃̇!P` and `D'Q_∈ − ι'Λ ∼∈ 1` (the printed form fails for `P = Λ̇` or for `P` without a beginning and `Q = x ↓ y`). -/
theorem pm217_41 {P Q : α → α → Prop}
    (h : ((P ∈ Ser ∧ Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) ∧ (¬EDesc Beg P ∨ ¬EDesc Beg Q))
    (hP : rEx P) (hQ1 : dom (imgRel Q) \ ι Λ ∉ (one : Set (Set (Set α)))) :
    segSer (P˘ ⤉ Q) = imgRel P˘ ⁏ opL (· \ ·) (fld P) ⁏ (segSer P)˘ ⤉
      opL (· ∪ ·) (fld P) ⁏ (segSer Q ⥏ (ι Λ)ᶜ) := by
  obtain ⟨⟨⟨hPs, hQs⟩, hd⟩, hor⟩ := h
  have hP' := b2_cnv_ser hPs
  have hor' : ¬(refs Beg P˘˘).Nonempty ∨ ¬(refs Beg Q).Nonempty := by
    rcases hor with h1 | h1
    · left; rintro ⟨b, hb⟩; exact h1 (b2_EDesc_iff.2 ⟨b, b2_refs_Beg_eq (b2_ser_po hPs) hb⟩)
    · right; rintro ⟨b, hb⟩; exact h1 (b2_EDesc_iff.2 ⟨b, b2_refs_Beg_eq (b2_ser_po hQs) hb⟩)
  have := pm217_23 (P := P˘) (Q := Q) ⟨⟨⟨⟨hP'.1.2, hP'.2⟩, ⟨hQs.1.2, hQs.2⟩⟩,
    by rw [fld_cnv]; exact hd⟩, hor'⟩ (let ⟨a, b, hab⟩ := hP; ⟨b, a, hab⟩) hQ1
  rw [this, pm217_36 hPs, fld_cnv]

/-! ### Segments of `P̆ ⤉ Q` (for ✱217·411·42·43)

`P̆''(C'P − G)` (the correlator of ✱217·37) carries the segments `G` of `P`, in the reverse order,
onto the segments of `P̆`; `C'P ∪ H` carries the non-null segments `H` of `Q` onto the remaining
segments of `P̆ ⤉ Q`, which all contain `C'P`. -/

/-- The series of segments of a sum is proper inclusion between its segments (✱217·18·23). -/
private theorem b2_segSer_rsum {P Q : α → α → Prop}
    (h : ((P ∈ transR ∩ connex ∧ Q ∈ transR ∩ connex) ∧ fld P ∩ fld Q = Λ) ∧
      (¬(refs Beg P˘).Nonempty ∨ ¬(refs Beg Q).Nonempty)) (X Y : Set α) :
    segSer (P ⤉ Q) X Y ↔
      ((X ∈ dom (imgRel P) ∪ opL (· ∪ ·) (fld P) ʻʻ (dom (imgRel Q) \ ι Λ)) ∧
        (Y ∈ dom (imgRel P) ∪ opL (· ∪ ·) (fld P) ʻʻ (dom (imgRel Q) \ ι Λ))) ∧ X ⊆ Y ∧ X ≠ Y := by
  obtain ⟨⟨⟨hPt, hQt⟩, hd⟩, hor⟩ := h
  have hD := pm217_18 ⟨hd, hor⟩
  have hcpP := b2_conn_po hPt.2
  have hcpQ := b2_conn_po hQt.2
  have sP : ∀ G, G ∈ dom (imgRel P) → G ∈ sect P := by
    rintro G ⟨B, rfl⟩; exact b2_img_sect hPt.1 B
  have sQ : ∀ G, G ∈ dom (imgRel Q) → G ∈ sect Q := by
    rintro G ⟨B, rfl⟩; exact b2_img_sect hQt.1 B
  have subD : ∀ X, X ∈ dom (imgRel P) ∪ opL (· ∪ ·) (fld P) ʻʻ (dom (imgRel Q) \ ι Λ) →
      X ⊆ fld (P ⤉ Q) := by
    rw [fld_rsum]
    rintro X (hX | ⟨G, hG, rfl⟩)
    · exact fun z hz => Or.inl (b2_seg_sub hX hz)
    · rintro z (hz | hz)
      · exact Or.inl hz
      · exact Or.inr (b2_seg_sub hG.1 hz)
  have nestD : ∀ X Y, X ∈ dom (imgRel P) ∪ opL (· ∪ ·) (fld P) ʻʻ (dom (imgRel Q) \ ι Λ) →
      Y ∈ dom (imgRel P) ∪ opL (· ∪ ·) (fld P) ʻʻ (dom (imgRel Q) \ ι Λ) → X ⊆ Y ∨ Y ⊆ X := by
    rintro X Y (hX | ⟨G, hG, rfl⟩) (hY | ⟨H, hH, rfl⟩)
    · exact b2_nested hcpP (sP X hX) (sP Y hY)
    · exact Or.inl fun z hz => Or.inl (b2_seg_sub hX hz)
    · exact Or.inr fun z hz => Or.inl (b2_seg_sub hY hz)
    · rcases b2_nested hcpQ (sQ G hG.1) (sQ H hH.1) with hs | hs
      · exact Or.inl (Set.union_subset_union_right _ hs)
      · exact Or.inr (Set.union_subset_union_right _ hs)
  rw [segSer_apply, hD]
  constructor
  · rintro ⟨⟨hX, hPl⟩, hY⟩
    exact ⟨⟨hX, hY⟩, (b2_Plc_nested (subD X hX) (subD Y hY) (nestD X Y hX hY)).1 hPl⟩
  · rintro ⟨⟨hX, hY⟩, hs⟩
    exact ⟨⟨hX, (b2_Plc_nested (subD X hX) (subD Y hY) (Or.inl hs.1)).2 hs⟩, hY⟩

/-- `(P̆)_∈;(C'P −);R` is `R` carried by `G ↦ P̆''(C'P − G)`. -/
private theorem b2_K_eq (P : α → α → Prop) (R : Set α → Set α → Prop) :
    imgRel P˘ ⁏ opL (· \ ·) (fld P) ⁏ R = graph (fun G => P˘ ʻʻ (fld P \ G)) ⁏ R := by
  rw [semi_semi]
  congr 1
  exact b2r_graph_relProd_graph _ _

private theorem b2_U_eq (P : α → α → Prop) :
    (opL (· ∪ ·) (fld P) : Set α → Set α → Prop) = graph (fun H => fld P ∪ H) := rfl

private theorem b2_f_sub (P : α → α → Prop) (G : Set α) : P˘ ʻʻ (fld P \ G) ⊆ fld P :=
  fun _ ⟨y, _, hy⟩ => ⟨y, Or.inr hy⟩

private theorem b2_f_mono (P : α → α → Prop) {G1 G2 : Set α} (h : G2 ⊆ G1) :
    P˘ ʻʻ (fld P \ G1) ⊆ P˘ ʻʻ (fld P \ G2) :=
  fun _ ⟨y, hy, hzy⟩ => ⟨y, ⟨hy.1, fun h' => hy.2 (h h')⟩, hzy⟩

private theorem b2_f_inj {P : α → α → Prop} (h : P ∈ Ser) {G1 G2 : Set α}
    (h1 : G1 ∈ dom (imgRel P)) (h2 : G2 ∈ dom (imgRel P))
    (e : P˘ ʻʻ (fld P \ G1) = P˘ ʻʻ (fld P \ G2)) : G1 = G2 :=
  (mem_arrow_one_one.1 (pm217_35 h)).2 _ G1 G2 ⟨b2_rel35.2 ⟨rfl, h1⟩, b2_rel35.2 ⟨e, h2⟩⟩

private theorem b2_f_ssub {P : α → α → Prop} (h : P ∈ Ser) {G1 G2 : Set α}
    (h1 : G1 ∈ dom (imgRel P)) (h2 : G2 ∈ dom (imgRel P)) :
    (P˘ ʻʻ (fld P \ G1) ⊆ P˘ ʻʻ (fld P \ G2) ∧ P˘ ʻʻ (fld P \ G1) ≠ P˘ ʻʻ (fld P \ G2)) ↔
      (G2 ⊆ G1 ∧ G2 ≠ G1) := by
  constructor
  · rintro ⟨hs, hne⟩
    have hn : G2 ≠ G1 := fun e => hne (by rw [e])
    rcases b2_nested (b2_conn_po h.2) (b2_seg_sect h h1) (b2_seg_sect h h2) with h' | h'
    · exact absurd (Set.Subset.antisymm hs (b2_f_mono P h')) hne
    · exact ⟨h', hn⟩
  · rintro ⟨hs, hne⟩
    exact ⟨b2_f_mono P hs, fun e => hne (b2_f_inj h h2 h1 e.symm)⟩

private theorem b2_f_dom (P : α → α → Prop) : P˘ ʻʻ (fld P \ dom P) = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ ⟨_, hy, hzy⟩ => hy.2 ⟨_, hzy⟩

private theorem b2_dom_seg (P : α → α → Prop) : dom P ∈ dom (imgRel P) :=
  ⟨fld P, (b2_img_fld P).symm⟩

private theorem b2_f_null {P : α → α → Prop} (h : P ∈ Ser) {G : Set α} (hG : G ∈ dom (imgRel P)) :
    P˘ ʻʻ (fld P \ G) = ∅ ↔ G = dom P := by
  constructor
  · intro e; exact b2_f_inj h hG (b2_dom_seg P) (e.trans (b2_f_dom P).symm)
  · rintro rfl; exact b2_f_dom P

private theorem b2_f_empty (P : α → α → Prop) : P˘ ʻʻ (fld P \ ∅) = codom P := by
  ext z
  exact ⟨fun ⟨y, _, hzy⟩ => ⟨y, hzy⟩, fun ⟨y, hy⟩ => ⟨y, ⟨⟨z, Or.inl hy⟩, fun h => h⟩, hy⟩⟩

private theorem b2_g_cap {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) {K : Set α}
    (hK : K ⊆ fld Q) : (fld P ∪ K) ∩ fld Q = K := by
  ext z
  exact ⟨fun ⟨hz, hzQ⟩ => hz.resolve_left fun hP => b2_disj hd hP hzQ,
    fun hz => ⟨Or.inr hz, hK hz⟩⟩

private theorem b2_g_inj {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) {H1 H2 : Set α}
    (h1 : H1 ⊆ fld Q) (h2 : H2 ⊆ fld Q) (e : fld P ∪ H1 = fld P ∪ H2) : H1 = H2 := by
  rw [← b2_g_cap hd h1, ← b2_g_cap hd h2, e]

private theorem b2_g_ssub {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) {H1 H2 : Set α}
    (h1 : H1 ⊆ fld Q) (h2 : H2 ⊆ fld Q) :
    (fld P ∪ H1 ⊆ fld P ∪ H2 ∧ fld P ∪ H1 ≠ fld P ∪ H2) ↔ (H1 ⊆ H2 ∧ H1 ≠ H2) := by
  constructor
  · rintro ⟨hs, hne⟩
    refine ⟨fun z hz => ?_, fun e => hne (by rw [e])⟩
    have h' : z ∈ (fld P ∪ H2) ∩ fld Q := ⟨hs (Or.inr hz), h1 hz⟩
    rwa [b2_g_cap hd h2] at h'
  · rintro ⟨hs, hne⟩
    exact ⟨Set.union_subset_union_right _ hs, fun e => hne (b2_g_inj hd h1 h2 e)⟩

private theorem b2_f_lt_g {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) (G : Set α) {H : Set α}
    (hH : H ⊆ fld Q) (hne : H.Nonempty) :
    (P˘ ʻʻ (fld P \ G) ⊆ fld P ∪ H ∧ P˘ ʻʻ (fld P \ G) ≠ fld P ∪ H) ∧
      ¬(fld P ∪ H ⊆ P˘ ʻʻ (fld P \ G)) := by
  obtain ⟨z, hz⟩ := hne
  have hn : z ∉ P˘ ʻʻ (fld P \ G) := fun h => b2_disj hd (b2_f_sub P G h) (hH hz)
  refine ⟨⟨fun w hw => Or.inl (b2_f_sub P G hw), fun e => hn ?_⟩, fun hs => hn (hs (Or.inr hz))⟩
  rw [e]; exact Or.inr hz

/-- The pairs of `ς'(P̆ ⤉ Q)` (cf. ✱217·41): two segments `P̆''(C'P − G)` of `P̆` (`G₂ ⊊ G₁`
segments of `P`), two classes `C'P ∪ H` (`H₁ ⊊ H₂` non-null segments of `Q`), or one of each. -/
private theorem b2_T_seg {P Q : α → α → Prop}
    (h : ((P ∈ Ser ∧ Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) ∧ (¬EDesc Beg P ∨ ¬EDesc Beg Q))
    (u v : Set α) :
    segSer (P˘ ⤉ Q) u v ↔
      ((∃ G1 G2, ((G1 ∈ dom (imgRel P) ∧ G2 ∈ dom (imgRel P)) ∧ G2 ⊆ G1 ∧ G2 ≠ G1) ∧
          u = P˘ ʻʻ (fld P \ G1) ∧ v = P˘ ʻʻ (fld P \ G2)) ∨
        (∃ H1 H2, ((H1 ∈ dom (imgRel Q) \ ι Λ ∧ H2 ∈ dom (imgRel Q) \ ι Λ) ∧ H1 ⊆ H2 ∧ H1 ≠ H2) ∧
          u = fld P ∪ H1 ∧ v = fld P ∪ H2)) ∨
      ((∃ G, G ∈ dom (imgRel P) ∧ u = P˘ ʻʻ (fld P \ G)) ∧
        (∃ H, H ∈ dom (imgRel Q) \ ι Λ ∧ v = fld P ∪ H)) := by
  obtain ⟨⟨⟨hPs, hQs⟩, hd⟩, hor⟩ := h
  have hP' := b2_cnv_ser hPs
  have hor' : ¬(refs Beg P˘˘).Nonempty ∨ ¬(refs Beg Q).Nonempty := by
    rcases hor with h1 | h1
    · left; rintro ⟨b, hb⟩; exact h1 (b2_EDesc_iff.2 ⟨b, b2_refs_Beg_eq (b2_ser_po hPs) hb⟩)
    · right; rintro ⟨b, hb⟩; exact h1 (b2_EDesc_iff.2 ⟨b, b2_refs_Beg_eq (b2_ser_po hQs) hb⟩)
  have hd' : fld P˘ ∩ fld Q = Λ := by rw [fld_cnv]; exact hd
  rw [b2_segSer_rsum ⟨⟨⟨⟨hP'.1.2, hP'.2⟩, ⟨hQs.1.2, hQs.2⟩⟩, hd'⟩, hor'⟩, fld_cnv, pm217_32 hPs]
  have hQsub : ∀ H, H ∈ dom (imgRel Q) \ ι Λ → H ⊆ fld Q ∧ H.Nonempty := fun H hH =>
    ⟨b2_seg_sub hH.1, b2_not_mem_iotaNull.1 hH.2⟩
  have mP : ∀ X, X ∈ imgRel P˘ ʻʻ (opL (· \ ·) (fld P) ʻʻ dom (imgRel P)) ↔
      ∃ G, G ∈ dom (imgRel P) ∧ X = P˘ ʻʻ (fld P \ G) := by
    intro X
    constructor
    · rintro ⟨U, ⟨G, hG, rfl⟩, rfl⟩; exact ⟨G, hG, rfl⟩
    · rintro ⟨G, hG, rfl⟩; exact ⟨_, ⟨G, hG, rfl⟩, rfl⟩
  simp only [Set.mem_union, mP]
  constructor
  · rintro ⟨⟨⟨G1, hG1, rfl⟩ | ⟨H1, hH1, rfl⟩, ⟨G2, hG2, rfl⟩ | ⟨H2, hH2, rfl⟩⟩, hs⟩
    · exact Or.inl (Or.inl ⟨G1, G2, ⟨⟨hG1, hG2⟩, (b2_f_ssub hPs hG1 hG2).1 hs⟩, rfl, rfl⟩)
    · exact Or.inr ⟨⟨G1, hG1, rfl⟩, H2, hH2, rfl⟩
    · exact absurd hs.1 (b2_f_lt_g hd G2 (hQsub H1 hH1).1 (hQsub H1 hH1).2).2
    · exact Or.inl (Or.inr ⟨H1, H2, ⟨⟨hH1, hH2⟩,
        (b2_g_ssub hd (hQsub H1 hH1).1 (hQsub H2 hH2).1).1 hs⟩, rfl, rfl⟩)
  · rintro ((⟨G1, G2, ⟨⟨hG1, hG2⟩, hs⟩, rfl, rfl⟩ | ⟨H1, H2, ⟨⟨hH1, hH2⟩, hs⟩, rfl, rfl⟩) |
      ⟨⟨G, hG, rfl⟩, H, hH, rfl⟩)
    · exact ⟨⟨Or.inl ⟨G1, hG1, rfl⟩, Or.inl ⟨G2, hG2, rfl⟩⟩, (b2_f_ssub hPs hG1 hG2).2 hs⟩
    · exact ⟨⟨Or.inr ⟨H1, hH1, rfl⟩, Or.inr ⟨H2, hH2, rfl⟩⟩,
        (b2_g_ssub hd (hQsub H1 hH1).1 (hQsub H2 hH2).1).2 hs⟩
    · exact ⟨⟨Or.inl ⟨G, hG, rfl⟩, Or.inr ⟨H, hH, rfl⟩⟩,
        (b2_f_lt_g hd G (hQsub H hH).1 (hQsub H hH).2).1⟩

/-- For a series `R`, `C'(R ⥏ E) = C'R ∩ E` as soon as `R ⥏ E` is not null. -/
private theorem b2_fld_fres_ser {β : Type*} {R : β → β → Prop} (hR : R ∈ Ser) {E : Set β}
    (hE : rEx (R ⥏ E)) : fld (R ⥏ E) = fld R ∩ E := by
  obtain ⟨-, hcon⟩ := mem_Ser.1 hR
  obtain ⟨a, b, hab⟩ := hE
  ext x
  constructor
  · rintro ⟨y, ⟨⟨hx, hxy⟩, -⟩ | ⟨⟨-, hyx⟩, hx⟩⟩
    · exact ⟨⟨y, Or.inl hxy⟩, hx⟩
    · exact ⟨⟨y, Or.inr hyx⟩, hx⟩
  · rintro ⟨hxf, hxE⟩
    have haf : a ∈ fld R := ⟨b, Or.inl hab.1.2⟩
    by_cases e : x = a
    · rw [e]; exact ⟨b, Or.inl hab⟩
    · rcases hcon x a ⟨hxf, haf⟩ with (h' | h') | h'
      · exact ⟨a, Or.inl ⟨⟨hxE, h'⟩, hab.1.1⟩⟩
      · exact absurd h' e
      · exact ⟨a, Or.inr ⟨⟨hab.1.1, h'⟩, hxE⟩⟩

private theorem b2_rEx_of_segfres {P : α → α → Prop} (h : P ∈ Ser) {E : Set (Set α)}
    (hE : rEx (segSer P ⥏ E)) : rEx P := by
  obtain ⟨G1, G2, hG⟩ := hE
  obtain ⟨⟨-, hG2⟩, hs, hne⟩ := (b2_segSer_ser h).1 hG.1.2
  obtain ⟨z, hz, -⟩ := b2_diff_of_ne hs hne
  obtain ⟨B, rfl⟩ := hG2
  obtain ⟨b, -, hzb⟩ := hz
  exact ⟨z, b, hzb⟩

private theorem b2_dom_rsum {R Q : α → α → Prop} (hQ : rEx Q) : dom (R ⤉ Q) = fld R ∪ dom Q := by
  obtain ⟨q, q', hqq⟩ := hQ
  ext x
  constructor
  · rintro ⟨y, (h' | h') | ⟨hx, -⟩⟩
    · exact Or.inl ⟨y, Or.inl h'⟩
    · exact Or.inr ⟨y, h'⟩
    · exact Or.inl hx
  · rintro (hx | ⟨y, hy⟩)
    · exact ⟨q, Or.inr ⟨hx, q', Or.inl hqq⟩⟩
    · exact ⟨y, Or.inl (Or.inr hy)⟩

private theorem b2_segSer_rNull_none {β : Type*} (X Y : Set β) :
    ¬segSer (rNull : β → β → Prop) X Y := by
  intro hXY
  obtain ⟨-, z, ⟨hz, -⟩, -⟩ := hXY.1.2
  obtain ⟨B, hB⟩ := hXY.2
  have : z ∈ (rNull : β → β → Prop) ʻʻ B := hB ▸ hz
  obtain ⟨w, -, hw⟩ := this
  exact rNull_apply _ _ hw

/-- The printed ✱217·411 fails: for `P = 0 ↓ 1` and `Q` the decreasing order of `2, 3, 4, …` (no
beginning), the pair `(ι'1, C'P ∪ Q''ι'2)` of `ς'(P̆ ⤉ Q)` is lost on the right, where
`(ς'P)⥏(−ι'D'P) = Λ̇`. -/
theorem pm217_411_printed_false :
    ¬∀ P Q : ℕ → ℕ → Prop,
      ((P ∈ Ser ∧ Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) ∧ (¬EDesc Beg P ∨ ¬EDesc Beg Q) →
        segSer (P˘ ⤉ Q) ⥏ (ι Λ)ᶜ =
          imgRel P˘ ⁏ opL (· \ ·) (fld P) ⁏ (segSer P ⥏ (ι (dom P))ᶜ)˘ ⤉
            opL (· ∪ ·) (fld P) ⁏ (segSer Q ⥏ (ι Λ)ᶜ) := by
  intro H
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ → Prop, ∀ x y, P x y ↔ x = 0 ∧ y = 1 := ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℕ → Prop, ∀ x y, Q x y ↔ y < x ∧ 2 ≤ y := ⟨_, fun _ _ => Iff.rfl⟩
  have fP : ∀ x, x ∈ fld P → x ≤ 1 := by
    rintro x ⟨w, h | h⟩ <;> rw [hP] at h <;> omega
  have fQ : ∀ x, x ∈ fld Q → 2 ≤ x := by
    rintro x ⟨w, h | h⟩ <;> rw [hQ] at h <;> omega
  have hPs : P ∈ Ser := by
    refine mem_Ser.2 ⟨⟨fun x h => ?_, fun x y z h => ?_⟩, fun x y h => ?_⟩
    · rw [hP] at h; omega
    · rw [hP, hP] at h; rw [hP]; omega
    · have := fP x h.1; have := fP y h.2
      rw [hP, hP]; omega
  have hQs : Q ∈ Ser := by
    refine mem_Ser.2 ⟨⟨fun x h => ?_, fun x y z h => ?_⟩, fun x y h => ?_⟩
    · rw [hQ] at h; omega
    · rw [hQ, hQ] at h; rw [hQ]; omega
    · have := fQ x h.1; have := fQ y h.2
      rw [hQ, hQ]; omega
  have hd : fld P ∩ fld Q = Λ := by
    rw [Null_eq_empty]
    refine Set.eq_empty_iff_forall_notMem.2 fun z ⟨h1, h2⟩ => ?_
    have := fP z h1; have := fQ z h2; omega
  have hor : ¬EDesc Beg P ∨ ¬EDesc Beg Q := by
    right; rintro ⟨b, hb⟩
    obtain ⟨⟨w, hw⟩, hn⟩ := (hb b).2 rfl
    rw [hQ] at hw
    exact hn ⟨b + 1, (hQ _ _).2 ⟨by omega, by omega⟩⟩
  have e := H P Q ⟨⟨⟨hPs, hQs⟩, hd⟩, hor⟩
  have hT : ∀ x y, (P˘ ⤉ Q) x y ↔ (P y x ∨ Q x y) ∨ (x ∈ fld P ∧ y ∈ fld Q) := by
    intro x y; rw [rsum_apply, fld_cnv]; exact Iff.rfl
  have h2Q : (2 : ℕ) ∈ fld Q := ⟨3, Or.inr ((hQ 3 2).2 ⟨by omega, le_rfl⟩)⟩
  have h0P : (0 : ℕ) ∈ fld P := ⟨1, Or.inl ((hP 0 1).2 ⟨rfl, rfl⟩)⟩
  have h1P : (1 : ℕ) ∈ fld P := ⟨0, Or.inr ((hP 0 1).2 ⟨rfl, rfl⟩)⟩
  have hu1 : (1 : ℕ) ∈ (P˘ ⤉ Q) ʻʻ {0} :=
    ⟨0, rfl, (hT 1 0).2 (Or.inl (Or.inl ((hP 0 1).2 ⟨rfl, rfl⟩)))⟩
  have hu : ∀ x, x ∈ (P˘ ⤉ Q) ʻʻ {0} → x = 1 := by
    rintro x ⟨y, hy, hxy⟩
    have hy0 : y = 0 := hy
    rw [hy0, hT] at hxy
    rcases hxy with (h | h) | ⟨-, h⟩
    · rw [hP] at h; omega
    · rw [hQ] at h; omega
    · have := fQ 0 h; omega
  have hv : ∀ x, x ∈ fld P → x ∈ (P˘ ⤉ Q) ʻʻ {2} := fun x hx =>
    ⟨2, rfl, (hT x 2).2 (Or.inr ⟨hx, h2Q⟩)⟩
  have hsub : (P˘ ⤉ Q) ʻʻ {0} ⊆ (P˘ ⤉ Q) ʻʻ {2} := fun x hx => by
    rw [hu x hx]; exact hv 1 h1P
  have hne : (P˘ ⤉ Q) ʻʻ {0} ≠ (P˘ ⤉ Q) ʻʻ {2} := fun e' => by
    have := hv 0 h0P
    rw [← e'] at this
    exact absurd (hu 0 this) (by omega)
  have himg : ∀ B : Set ℕ, (P˘ ⤉ Q) ʻʻ B ⊆ fld (P˘ ⤉ Q) := fun B z ⟨y, _, h⟩ => ⟨y, Or.inl h⟩
  have hL : (segSer (P˘ ⤉ Q) ⥏ (ι Λ)ᶜ) ((P˘ ⤉ Q) ʻʻ {0}) ((P˘ ⤉ Q) ʻʻ {2}) :=
    ⟨⟨b2_not_mem_iotaNull.2 ⟨1, hu1⟩, ⟨⟨_, rfl⟩,
      (b2_Plc_nested (himg _) (himg _) (Or.inl hsub)).2 ⟨hsub, hne⟩⟩, ⟨_, rfl⟩⟩,
      b2_not_mem_iotaNull.2 ⟨0, hv 0 h0P⟩⟩
  have nP : ∀ G1 G2 : Set ℕ, ¬(segSer P ⥏ (ι (dom P))ᶜ) G1 G2 := by
    rintro G1 G2 ⟨⟨-, hseg⟩, hG2⟩
    obtain ⟨⟨-, ⟨B, rfl⟩⟩, hs, hne'⟩ := (b2_segSer_ser hPs).1 hseg
    apply hG2
    obtain ⟨z, ⟨b, hb, hzb⟩, -⟩ := b2_diff_of_ne hs hne'
    rw [hP] at hzb
    show P ʻʻ B = dom P
    ext x
    constructor
    · rintro ⟨y, -, hxy⟩; exact ⟨y, hxy⟩
    · rintro ⟨y, hxy⟩
      rw [hP] at hxy
      exact ⟨b, hb, (hP _ _).2 ⟨hxy.1, hzb.2⟩⟩
  rw [e, rsum_apply] at hL
  rcases hL with (h1 | h1) | ⟨h1, -⟩
  · rw [b2_K_eq, semi_graph_apply] at h1
    obtain ⟨G1, G2, -, h'⟩ := h1
    exact nP _ _ h'
  · rw [semi_apply] at h1
    obtain ⟨H1, H2, ⟨hu', -⟩, -⟩ := h1
    have hu'' : (P˘ ⤉ Q) ʻʻ {0} = fld P ∪ H1 := hu'
    have : (0 : ℕ) ∈ (P˘ ⤉ Q) ʻʻ {0} := by rw [hu'']; exact Or.inl h0P
    exact absurd (hu 0 this) (by omega)
  · rw [b2_K_eq, b2_semi_graph_fld] at h1
    obtain ⟨G, ⟨G', hG' | hG'⟩, -⟩ := h1
    · exact nP _ _ hG'
    · exact nP _ _ hG'

/-- ✱217·411. \[\begin{align}\vdash :\text{Hp}&*217·41.\supset .{\varsigma ʻ(\breve{P} \unicode{x2909} Q)}\unicode{x0294f}(-{℩}ʻ\Lambda )=\\ &(\breve{P} )_{\in }^{;}(CʻP-)^{;}\text{Cnv}ʻ(\varsigma ʻP)\unicode{x0294f}(-{℩}ʻ\text{D}ʻP)\unicode{x2909} (CʻP\cup )^{;}(\varsigma ʻQ)\unicode{x0294f}(-{℩}ʻ\Lambda )\\ &[*217·41]\end{align}\]

**Status.** proved (corrected): false as printed in degenerate cases: as ✱217·41 when
`D'Q_∈ − ι'Λ ∈ 1` (and `∃̇!P`), and also when `P ∈ 2_r`, where `(ς'P)⥏(−ι'D'P) = Λ̇` and the pairs
`(ᗡ'P, C'P ∪ H)` of the left side are lost. The hypotheses `∃̇!(ς'P)⥏(−ι'D'P)` (`P` has at least
three terms) and `D'Q_∈ − ι'Λ ∼∈ 1` are added; `pm217_411_printed_false` proves the failure
(`P = 0 ↓ 1` and `Q` without beginning, on `ℕ`). -/
theorem pm217_411 {P Q : α → α → Prop}
    (h : ((P ∈ Ser ∧ Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) ∧ (¬EDesc Beg P ∨ ¬EDesc Beg Q))
    (hP : rEx (segSer P ⥏ (ι (dom P))ᶜ))
    (hQ1 : dom (imgRel Q) \ ι Λ ∉ (one : Set (Set (Set α)))) :
    segSer (P˘ ⤉ Q) ⥏ (ι Λ)ᶜ =
      imgRel P˘ ⁏ opL (· \ ·) (fld P) ⁏ (segSer P ⥏ (ι (dom P))ᶜ)˘ ⤉
        opL (· ∪ ·) (fld P) ⁏ (segSer Q ⥏ (ι Λ)ᶜ) := by
  have hT := b2_T_seg h
  obtain ⟨⟨⟨hPs, hQs⟩, hd⟩, -⟩ := h
  have hPne := b2_rEx_of_segfres hPs hP
  have hSP : segSer P ∈ Ser := (pm214_33 ⟨b2_ser_tc hPs, hPne⟩).1
  have hfP : fld (segSer P ⥏ (ι (dom P))ᶜ) = dom (imgRel P) ∩ (ι (dom P))ᶜ := by
    rw [b2_fld_fres_ser hSP hP, b2_fld_segSer_ser hPs hPne]
  have hfQ := b2_fld_segSer_nn (b2_ser_tc hQs) hQ1
  have hfPne : (fld P).Nonempty := b2r_rEx_iff_fld.1 hPne
  have gne : ∀ H : Set α, fld P ∪ H ∉ ι Λ := fun H =>
    b2_not_mem_iotaNull.2 (hfPne.mono Set.subset_union_left)
  rw [b2_K_eq, b2_U_eq]
  funext u v; apply propext
  rw [b2_fres_apply, hT, rsum_apply, semi_graph_apply, semi_graph_apply, b2_semi_graph_fld,
    b2_semi_graph_fld, fld_cnv, hfP, hfQ]
  constructor
  · rintro ⟨⟨hu, (⟨G1, G2, ⟨⟨hG1, hG2⟩, hs⟩, rfl, rfl⟩ | ⟨H1, H2, ⟨⟨hH1, hH2⟩, hs⟩, rfl, rfl⟩) |
      ⟨⟨G, hG, rfl⟩, H, hH, rfl⟩⟩, hv⟩
    · exact Or.inl (Or.inl ⟨G1, G2, ⟨rfl, rfl⟩,
        ⟨fun e => hv (b2_mem_iotaNull.2 ((b2_f_null hPs hG2).2 e)),
          (b2_segSer_ser hPs).2 ⟨⟨hG2, hG1⟩, hs⟩⟩,
        fun e => hu (b2_mem_iotaNull.2 ((b2_f_null hPs hG1).2 e))⟩)
    · exact Or.inl (Or.inr ⟨H1, H2, ⟨rfl, rfl⟩,
        ⟨hH1.2, (b2_segSer_ser hQs).2 ⟨⟨hH1.1, hH2.1⟩, hs⟩⟩, hH2.2⟩)
    · exact Or.inr ⟨⟨G, ⟨hG, fun e => hu (b2_mem_iotaNull.2 ((b2_f_null hPs hG).2 e))⟩, rfl⟩,
        H, hH, rfl⟩
  · rintro ((⟨G1, G2, ⟨rfl, rfl⟩, ⟨hG2, hseg⟩, hG1⟩ | ⟨H1, H2, ⟨rfl, rfl⟩, ⟨hH1, hseg⟩, hH2⟩) |
      ⟨⟨G, ⟨hG, hGn⟩, rfl⟩, H, hH, rfl⟩)
    · obtain ⟨⟨hG2', hG1'⟩, hs⟩ := (b2_segSer_ser hPs).1 hseg
      exact ⟨⟨fun e => hG1 ((b2_f_null hPs hG1').1 (b2_mem_iotaNull.1 e)),
        Or.inl (Or.inl ⟨G1, G2, ⟨⟨hG1', hG2'⟩, hs⟩, rfl, rfl⟩)⟩,
        fun e => hG2 ((b2_f_null hPs hG2').1 (b2_mem_iotaNull.1 e))⟩
    · obtain ⟨⟨hH1', hH2'⟩, hs⟩ := (b2_segSer_ser hQs).1 hseg
      exact ⟨⟨gne H1, Or.inl (Or.inr ⟨H1, H2, ⟨⟨⟨hH1', hH1⟩, ⟨hH2', hH2⟩⟩, hs⟩, rfl, rfl⟩)⟩,
        gne H2⟩
    · exact ⟨⟨fun e => hGn ((b2_f_null hPs hG).1 (b2_mem_iotaNull.1 e)),
        Or.inr ⟨⟨G, hG, rfl⟩, H, hH, rfl⟩⟩, gne H⟩

/-- The segments of `P` other than `Λ` and `D'P` for `P x y . ≡ . x < y ≤ 2` (on `ℕ`): only `ι'0`. -/
private theorem b2_seg_three {P : ℕ → ℕ → Prop} (hP : ∀ x y, P x y ↔ x < y ∧ y ≤ 2) {G : Set ℕ}
    (hG : G ∈ dom (imgRel P)) (hG' : G ∈ (ι Λ)ᶜ \ ι (dom P)) (x : ℕ) : x ∈ G ↔ x = 0 := by
  obtain ⟨B, rfl⟩ := hG
  obtain ⟨w, b, hb, hwb⟩ := b2_not_mem_iotaNull.1 hG'.1
  rw [hP] at hwb
  have h1 : (1 : ℕ) ∉ P ʻʻ B := by
    rintro ⟨c, hc, h1c⟩
    rw [hP] at h1c
    apply hG'.2
    show P ʻʻ B = dom P
    ext y
    constructor
    · rintro ⟨d, -, hyd⟩; exact ⟨d, hyd⟩
    · rintro ⟨d, hyd⟩
      rw [hP] at hyd
      exact ⟨c, hc, (hP _ _).2 ⟨by omega, h1c.2⟩⟩
  constructor
  · rintro ⟨c, hc, hxc⟩
    rw [hP] at hxc
    rcases Nat.lt_or_ge x 1 with h' | h'
    · omega
    · have : x = 1 := by omega
      subst this
      exact absurd ⟨c, hc, (hP _ _).2 hxc⟩ h1
  · rintro rfl
    exact ⟨b, hb, (hP _ _).2 ⟨by omega, hwb.2⟩⟩

/-- The printed ✱217·42 fails: for `P` the series `0, 1, 2` and `Q` the series `…, 5, 4, 3`
(decreasing, without beginning), the pair `(ι'2, ι'1 ∪ ι'2)` (`(P̆ ⤉ Q)''ι'1`, `(P̆ ⤉ Q)''ι'0`)
of the left side is lost on the right, where `(ς'P)⥏(−ι'Λ−ι'D'P) = Λ̇` (`ι'0` is the only segment
it keeps), so that `X̆ ⇸ ᗡ'P` is null and every left term of the `(C'P ∪)` part contains `C'P`.
Neither class is `D'(P ⤉ Q)` or `D'(P̆ ⤉ Q)` (both contain `0`), so the failure does not depend
on the e-text's `D'(P ⤉ Q)`. -/
theorem pm217_42_printed_false :
    ¬∀ P Q : ℕ → ℕ → Prop,
      ((P ∈ Ser ∧ Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) ∧ (¬EDesc Beg P ∨ ¬EDesc Beg Q) →
        segSer (P˘ ⤉ Q) ⥏ ((ι Λ)ᶜ \ ι (dom (P ⤉ Q))) =
          imgRel P˘ ⁏ opL (· \ ·) (fld P) ⁏ (segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P)))˘ ⇸ codom P ⤉
            opL (· ∪ ·) (fld P) ⁏ (segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q))) := by
  intro H
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ → Prop, ∀ x y, P x y ↔ x < y ∧ y ≤ 2 := ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℕ → Prop, ∀ x y, Q x y ↔ y < x ∧ 3 ≤ y := ⟨_, fun _ _ => Iff.rfl⟩
  have fP : ∀ x, x ∈ fld P → x ≤ 2 := by
    rintro x ⟨w, h | h⟩ <;> rw [hP] at h <;> omega
  have fQ : ∀ x, x ∈ fld Q → 3 ≤ x := by
    rintro x ⟨w, h | h⟩ <;> rw [hQ] at h <;> omega
  have hPs : P ∈ Ser := by
    refine mem_Ser.2 ⟨⟨fun x h => ?_, fun x y z h => ?_⟩, fun x y h => ?_⟩
    · rw [hP] at h; omega
    · rw [hP, hP] at h; rw [hP]; omega
    · have := fP x h.1; have := fP y h.2
      rw [hP, hP]; omega
  have hQs : Q ∈ Ser := by
    refine mem_Ser.2 ⟨⟨fun x h => ?_, fun x y z h => ?_⟩, fun x y h => ?_⟩
    · rw [hQ] at h; omega
    · rw [hQ, hQ] at h; rw [hQ]; omega
    · have := fQ x h.1; have := fQ y h.2
      rw [hQ, hQ]; omega
  have hd : fld P ∩ fld Q = Λ := by
    rw [Null_eq_empty]
    refine Set.eq_empty_iff_forall_notMem.2 fun z ⟨h1, h2⟩ => ?_
    have := fP z h1; have := fQ z h2; omega
  have hor : ¬EDesc Beg P ∨ ¬EDesc Beg Q := by
    right; rintro ⟨b, hb⟩
    obtain ⟨⟨w, hw⟩, hn⟩ := (hb b).2 rfl
    rw [hQ] at hw
    exact hn ⟨b + 1, (hQ _ _).2 ⟨by omega, by omega⟩⟩
  have e := H P Q ⟨⟨⟨hPs, hQs⟩, hd⟩, hor⟩
  have hT : ∀ x y, (P˘ ⤉ Q) x y ↔ (P y x ∨ Q x y) ∨ (x ∈ fld P ∧ y ∈ fld Q) := by
    intro x y; rw [rsum_apply, fld_cnv]; exact Iff.rfl
  have hu : ∀ x, x ∈ (P˘ ⤉ Q) ʻʻ {1} ↔ x = 2 := by
    intro x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hy1 : y = 1 := hy
      rw [hy1, hT] at hxy
      rcases hxy with (h | h) | ⟨-, h⟩
      · rw [hP] at h; omega
      · rw [hQ] at h; omega
      · have := fQ 1 h; omega
    · rintro rfl
      exact ⟨1, rfl, (hT 2 1).2 (Or.inl (Or.inl ((hP 1 2).2 ⟨by omega, le_rfl⟩)))⟩
  have hv : ∀ x, x ∈ (P˘ ⤉ Q) ʻʻ {0} ↔ 1 ≤ x ∧ x ≤ 2 := by
    intro x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hy0 : y = 0 := hy
      rw [hy0, hT] at hxy
      rcases hxy with (h | h) | ⟨-, h⟩
      · rw [hP] at h; omega
      · rw [hQ] at h; omega
      · have := fQ 0 h; omega
    · rintro ⟨h1, h2⟩
      exact ⟨0, rfl, (hT x 0).2 (Or.inl (Or.inl ((hP 0 x).2 ⟨by omega, h2⟩)))⟩
  have h0d : (0 : ℕ) ∈ dom (P ⤉ Q) :=
    ⟨1, (rsum_apply _ _ _ _).2 (Or.inl (Or.inl ((hP 0 1).2 ⟨by omega, by omega⟩)))⟩
  have memE : ∀ U : Set ℕ, (2 : ℕ) ∈ U → (0 : ℕ) ∉ U → U ∈ (ι Λ)ᶜ \ ι (dom (P ⤉ Q)) :=
    fun U h2 h0 => ⟨b2_not_mem_iotaNull.2 ⟨2, h2⟩, fun e' => h0 ((b2_mem_iota.1 e') ▸ h0d)⟩
  have himg : ∀ B : Set ℕ, (P˘ ⤉ Q) ʻʻ B ⊆ fld (P˘ ⤉ Q) := fun B z ⟨y, _, h⟩ => ⟨y, Or.inl h⟩
  have hsub : (P˘ ⤉ Q) ʻʻ {1} ⊆ (P˘ ⤉ Q) ʻʻ {0} := fun z hz =>
    (hv z).2 (by have := (hu z).1 hz; omega)
  have hne : (P˘ ⤉ Q) ʻʻ {1} ≠ (P˘ ⤉ Q) ʻʻ {0} := fun e' => by
    have h1 : (1 : ℕ) ∈ (P˘ ⤉ Q) ʻʻ {0} := (hv 1).2 ⟨le_rfl, by omega⟩
    rw [← e'] at h1
    have := (hu 1).1 h1; omega
  have h0L : (0 : ℕ) ∉ (P˘ ⤉ Q) ʻʻ {1} := fun h => by have := (hu 0).1 h; omega
  have hL : (segSer (P˘ ⤉ Q) ⥏ ((ι Λ)ᶜ \ ι (dom (P ⤉ Q))))
      ((P˘ ⤉ Q) ʻʻ {1}) ((P˘ ⤉ Q) ʻʻ {0}) :=
    ⟨⟨memE _ ((hu 2).2 rfl) h0L, ⟨⟨_, rfl⟩,
      (b2_Plc_nested (himg _) (himg _) (Or.inl hsub)).2 ⟨hsub, hne⟩⟩, ⟨_, rfl⟩⟩,
      memE _ ((hv 2).2 ⟨by omega, le_rfl⟩) (fun h => by have := (hv 0).1 h; omega)⟩
  have nP : ∀ G1 G2 : Set ℕ, ¬(segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P))) G1 G2 := by
    rintro G1 G2 ⟨⟨hG1, hseg⟩, hG2⟩
    obtain ⟨⟨h1, h2⟩, -, hne'⟩ := (b2_segSer_ser hPs).1 hseg
    exact hne' (Set.ext fun x => (b2_seg_three hP h1 hG1 x).trans (b2_seg_three hP h2 hG2 x).symm)
  have nR1 : ∀ U V : Set ℕ,
      ¬(imgRel P˘ ⁏ opL (· \ ·) (fld P) ⁏ (segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P)))˘) U V := by
    intro U V h'
    rw [b2_K_eq, semi_graph_apply] at h'
    obtain ⟨G1, G2, -, h''⟩ := h'
    exact nP _ _ h''
  have h0U : ∀ U V : Set ℕ,
      (opL (· ∪ ·) (fld P) ⁏ (segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q)))) U V → (0 : ℕ) ∈ U := by
    intro U V h'
    obtain ⟨H1, H2, ⟨hU, -⟩, -⟩ := (semi_apply _ _ _ _).1 h'
    have hU' : U = fld P ∪ H1 := hU
    rw [hU']
    exact Or.inl ⟨1, Or.inl ((hP 0 1).2 ⟨by omega, by omega⟩)⟩
  rw [e, rsum_apply, addLast_apply] at hL
  rcases hL with ((h1 | ⟨⟨V, h1 | h1⟩, -⟩) | h1) | ⟨h1, -⟩
  · exact nR1 _ _ h1
  · exact nR1 _ _ h1
  · exact nR1 _ _ h1
  · exact h0L (h0U _ _ h1)
  · obtain ⟨-, a, b, hab⟩ := b2r_mem_fld_addLast.1 h1
    exact nR1 _ _ hab

/-- ✱217·42. \[\begin{align}\vdash :\text{Hp}*217·41.&\supset .\{\varsigma ʻ(\breve{P} \unicode{x2909} Q)\}\unicode{x0294f}\{-{℩}ʻ\Lambda -{℩}ʻ\text{D}ʻ(P\unicode{x2909} Q)\}=\\ &(\breve{P} )_{\in }^{;}(CʻP-)^{;}\text{Cnv}ʻ(\varsigma ʻP)\unicode{x0294f}(-{℩}ʻ\Lambda -{℩}ʻ\text{D}ʻP)\unicode{x21f8}\text{ᗡ}ʻP\\ &\unicode{x2909} (CʻP\cup )^{;}(\varsigma ʻQ)\unicode{x0294f}(-{℩}ʻ\Lambda -{℩}ʻ\text{D}ʻQ) \quad[*217·411]\end{align}\]

**Status.** proved (corrected): false as printed in degenerate cases, where `X = (ς'P)⥏(−ι'Λ−ι'D'P)`
or `Y = (ς'Q)⥏(−ι'Λ−ι'D'Q)` (notation of ✱217·43) is null although `P` or `Q` has one segment
besides `Λ` and its domain: then `X̆ ⇸ ᗡ'P` or the `C'P ∪ H` part loses its pairs. The hypotheses
`∃̇!X . ∃̇!Y` are added; `pm217_42_printed_false` proves the failure (`P` the series `0, 1, 2` and
`Q` the series `…, 4, 3` without beginning, on `ℕ`; the example does not depend on reading
`D'(P ⤉ Q)` or `D'(P̆ ⤉ Q)`). (For `∃̇!Q`, `D'(P ⤉ Q) = D'(P̆ ⤉ Q) = C'P ∪ D'Q`, so the e-text's `D'(P ⤉ Q)`
agrees with the `D'(P̆ ⤉ Q)` of ✱217·43.) -/
theorem pm217_42 {P Q : α → α → Prop}
    (h : ((P ∈ Ser ∧ Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) ∧ (¬EDesc Beg P ∨ ¬EDesc Beg Q))
    (hX : rEx (segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P))))
    (hY : rEx (segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q)))) :
    segSer (P˘ ⤉ Q) ⥏ ((ι Λ)ᶜ \ ι (dom (P ⤉ Q))) =
      imgRel P˘ ⁏ opL (· \ ·) (fld P) ⁏ (segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P)))˘ ⇸ codom P ⤉
        opL (· ∪ ·) (fld P) ⁏ (segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q))) := by
  have hT := b2_T_seg h
  obtain ⟨⟨⟨hPs, hQs⟩, hd⟩, -⟩ := h
  have hPne := b2_rEx_of_segfres hPs hX
  have hQne := b2_rEx_of_segfres hQs hY
  have hfX : fld (segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P))) =
      dom (imgRel P) ∩ ((ι Λ)ᶜ \ ι (dom P)) := by
    rw [b2_fld_fres_ser (pm214_33 ⟨b2_ser_tc hPs, hPne⟩).1 hX, b2_fld_segSer_ser hPs hPne]
  have hfY : fld (segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q))) =
      dom (imgRel Q) ∩ ((ι Λ)ᶜ \ ι (dom Q)) := by
    rw [b2_fld_fres_ser (pm214_33 ⟨b2_ser_tc hQs, hQne⟩).1 hY, b2_fld_segSer_ser hQs hQne]
  have hR1 : rEx (graph (fun G => P˘ ʻʻ (fld P \ G)) ⁏ (segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P)))˘) := by
    obtain ⟨G1, G2, hG⟩ := hX
    exact ⟨_, _, (semi_graph_apply _ _ _ _).2 ⟨G2, G1, ⟨rfl, rfl⟩, hG⟩⟩
  have hdQ : (dom Q).Nonempty := let ⟨a, b, hab⟩ := hQne; ⟨a, b, hab⟩
  have hdQs : dom Q ⊆ fld Q := fun _ ⟨w, hw⟩ => ⟨w, Or.inl hw⟩
  have hdP : dom P ≠ ∅ := let ⟨a, b, hab⟩ := hPne; Set.nonempty_iff_ne_empty.1 ⟨a, b, hab⟩
  have hfPne : (fld P).Nonempty := b2r_rEx_iff_fld.1 hPne
  have hcod : codom P = P˘ ʻʻ (fld P \ ∅) := (b2_f_empty P).symm
  have memf : ∀ G, G ∈ dom (imgRel P) → G ≠ dom P →
      P˘ ʻʻ (fld P \ G) ∈ (ι Λ)ᶜ \ ι (fld P ∪ dom Q) := fun G hG hGd =>
    ⟨fun e => hGd ((b2_f_null hPs hG).1 (b2_mem_iotaNull.1 e)), (b2_f_lt_g hd G hdQs hdQ).1.2⟩
  have memg : ∀ H, H ∈ dom (imgRel Q) → H ≠ dom Q → fld P ∪ H ∈ (ι Λ)ᶜ \ ι (fld P ∪ dom Q) :=
    fun H hH hHd => ⟨b2_not_mem_iotaNull.2 (hfPne.mono Set.subset_union_left),
      fun e => hHd (b2_g_inj hd (b2_seg_sub hH) hdQs (b2_mem_iota.1 e))⟩
  rw [b2_K_eq, b2_U_eq, b2_dom_rsum hQne]
  funext u v; apply propext
  rw [b2_fres_apply, hT, rsum_apply, addLast_apply, semi_graph_apply, semi_graph_apply,
    b2r_mem_fld_addLast, b2_semi_graph_fld, b2_semi_graph_fld, fld_cnv, hfX, hfY]
  simp only [hR1, and_true]
  constructor
  · rintro ⟨⟨⟨hu0, hu1⟩, (⟨G1, G2, ⟨⟨hG1, hG2⟩, hs⟩, rfl, rfl⟩ |
      ⟨H1, H2, ⟨⟨hH1, hH2⟩, hs⟩, rfl, rfl⟩) | ⟨⟨G, hG, rfl⟩, H, hH, rfl⟩⟩, ⟨hv0, hv1⟩⟩
    · have nG1 : G1 ≠ dom P := fun e => hu0 (b2_mem_iotaNull.2 ((b2_f_null hPs hG1).2 e))
      have nG2 : G2 ≠ dom P := fun e => hv0 (b2_mem_iotaNull.2 ((b2_f_null hPs hG2).2 e))
      have eG1 : G1 ≠ ∅ := by
        rintro rfl; exact hs.2 (Set.subset_empty_iff.1 hs.1)
      by_cases hG2e : G2 = ∅
      · refine Or.inl (Or.inl (Or.inr ⟨⟨G1, ⟨hG1, fun e => eG1 (b2_mem_iotaNull.1 e), nG1⟩, rfl⟩,
          ?_⟩))
        rw [hG2e, b2_f_empty]
      · exact Or.inl (Or.inl (Or.inl ⟨G1, G2, ⟨rfl, rfl⟩,
          ⟨⟨fun e => hG2e (b2_mem_iotaNull.1 e), nG2⟩, (b2_segSer_ser hPs).2 ⟨⟨hG2, hG1⟩, hs⟩⟩,
          ⟨fun e => eG1 (b2_mem_iotaNull.1 e), nG1⟩⟩))
    · have nH1 : H1 ≠ dom Q := fun e => hu1 (b2_mem_iota.2 (by rw [e]))
      have nH2 : H2 ≠ dom Q := fun e => hv1 (b2_mem_iota.2 (by rw [e]))
      exact Or.inl (Or.inr ⟨H1, H2, ⟨rfl, rfl⟩,
        ⟨⟨hH1.2, nH1⟩, (b2_segSer_ser hQs).2 ⟨⟨hH1.1, hH2.1⟩, hs⟩⟩, ⟨hH2.2, nH2⟩⟩)
    · have nG : G ≠ dom P := fun e => hu0 (b2_mem_iotaNull.2 ((b2_f_null hPs hG).2 e))
      have nH : H ≠ dom Q := fun e => hv1 (b2_mem_iota.2 (by rw [e]))
      refine Or.inr ⟨?_, H, ⟨hH.1, hH.2, nH⟩, rfl⟩
      by_cases hGe : G = ∅
      · right; rw [hGe, b2_f_empty]
      · left; exact ⟨G, ⟨hG, fun e => hGe (b2_mem_iotaNull.1 e), nG⟩, rfl⟩
  · rintro (((⟨G1, G2, ⟨rfl, rfl⟩, ⟨⟨-, hG2d⟩, hseg⟩, ⟨-, hG1d⟩⟩ |
        ⟨⟨G, ⟨hG, hGn, hGd⟩, rfl⟩, rfl⟩) |
        ⟨H1, H2, ⟨rfl, rfl⟩, ⟨⟨hH1n, hH1d⟩, hseg⟩, ⟨hH2n, hH2d⟩⟩) |
      ⟨⟨G, ⟨hG, -, hGd⟩, rfl⟩ | rfl, ⟨H, ⟨hH, hHn, hHd⟩, rfl⟩⟩)
    · obtain ⟨⟨hG2', hG1'⟩, hs⟩ := (b2_segSer_ser hPs).1 hseg
      exact ⟨⟨memf G1 hG1' hG1d, Or.inl (Or.inl ⟨G1, G2, ⟨⟨hG1', hG2'⟩, hs⟩, rfl, rfl⟩)⟩,
        memf G2 hG2' hG2d⟩
    · refine ⟨⟨memf G hG hGd, Or.inl (Or.inl ⟨G, ∅, ⟨⟨hG, b2_seg_empty P⟩, Set.empty_subset _,
        fun e => hGn (b2_mem_iotaNull.2 e.symm)⟩, rfl, hcod⟩)⟩, ?_⟩
      rw [hcod]; exact memf ∅ (b2_seg_empty P) (Ne.symm hdP)
    · obtain ⟨⟨hH1', hH2'⟩, hs⟩ := (b2_segSer_ser hQs).1 hseg
      exact ⟨⟨memg H1 hH1' hH1d, Or.inl (Or.inr ⟨H1, H2, ⟨⟨⟨hH1', hH1n⟩, ⟨hH2', hH2n⟩⟩, hs⟩,
        rfl, rfl⟩)⟩, memg H2 hH2' hH2d⟩
    · exact ⟨⟨memf G hG hGd, Or.inr ⟨⟨G, hG, rfl⟩, H, ⟨hH, hHn⟩, rfl⟩⟩, memg H hH hHd⟩
    · refine ⟨⟨?_, Or.inr ⟨⟨∅, b2_seg_empty P, hcod⟩, H, ⟨hH, hHn⟩, rfl⟩⟩, memg H hH hHd⟩
      rw [hcod]; exact memf ∅ (b2_seg_empty P) (Ne.symm hdP)

/-- The printed ✱217·43 fails, and both corrections are needed.

(1) The printed correlator, with `(D'P) ↓ α`, fails even when `∃̇!X . ∃̇!Y` is added: for `P` the
series `0, 1, 2, 3`, `Q` the series `…, 6, 5, 4` (decreasing, without beginning) and `α = Λ`,
`X` and `Y` are not null, but `D'P = ι'0 ∪ ι'1 ∪ ι'2` is not a segment of `P̆ ⤉ Q` (a segment
containing `0` contains `C'P`), while the correlator relates it to `α ∈ C'W`, so that `D'P ∈ C'Z`.

(2) With the couple `(ᗡ'P) ↓ α`, the hypotheses `∃̇!X . ∃̇!Y` cannot be dropped: for `P = Q = Λ̇`,
`X = Y = Λ̇` and `W = Λ̇`, so `C'W = Λ`, but the correlator relates `ᗡ'P` to `α`, so `α ∈ ᗡ'S`. -/
theorem pm217_43_printed_false :
    (¬∀ (P Q : ℕ → ℕ → Prop) (X Y Z W : Set ℕ → Set ℕ → Prop) (A : Set ℕ),
      (((((((P ∈ Ser ∧ Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) ∧ (¬EDesc Beg P ∨ ¬EDesc Beg Q)) ∧
        X = segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P))) ∧ Y = segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q))) ∧
        Z = segSer (P˘ ⤉ Q) ⥏ ((ι Λ)ᶜ \ ι (dom (P˘ ⤉ Q)))) ∧ W = X˘ ⇸ A ⤉ Y) ∧
        A ∉ fld X ∪ fld Y → rEx X → rEx Y →
      (imgRel P˘ ⨾ opL (· \ ·) (fld P)) ↾ ((dom (imgRel P) \ ι Λ) \ ι (dom P)) ⊍ dom P ↓ A ⊍
        opL (· ∪ ·) (fld P) ↾ ((dom (imgRel Q) \ ι Λ) \ ι (dom Q)) ∈ smorbar Z W) ∧
    ¬∀ (P Q : ℕ → ℕ → Prop) (X Y Z W : Set ℕ → Set ℕ → Prop) (A : Set ℕ),
      (((((((P ∈ Ser ∧ Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) ∧ (¬EDesc Beg P ∨ ¬EDesc Beg Q)) ∧
        X = segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P))) ∧ Y = segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q))) ∧
        Z = segSer (P˘ ⤉ Q) ⥏ ((ι Λ)ᶜ \ ι (dom (P˘ ⤉ Q)))) ∧ W = X˘ ⇸ A ⤉ Y) ∧
        A ∉ fld X ∪ fld Y →
      (imgRel P˘ ⨾ opL (· \ ·) (fld P)) ↾ ((dom (imgRel P) \ ι Λ) \ ι (dom P)) ⊍ codom P ↓ A ⊍
        opL (· ∪ ·) (fld P) ↾ ((dom (imgRel Q) \ ι Λ) \ ι (dom Q)) ∈ smorbar Z W := by
  have nE : ∀ (R : Set ℕ → Set ℕ → Prop) (E : Set (Set ℕ)), E ⊆ (ι Λ)ᶜ →
      (∅ : Set ℕ) ∉ fld (R ⥏ E) := by
    rintro R E hE ⟨V, ⟨⟨h, -⟩, -⟩ | ⟨-, h⟩⟩ <;> exact hE h (b2_mem_iotaNull.2 rfl)
  refine ⟨fun H => ?_, fun H => ?_⟩
  · obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ → Prop, ∀ x y, P x y ↔ x < y ∧ y ≤ 3 :=
      ⟨_, fun _ _ => Iff.rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℕ → Prop, ∀ x y, Q x y ↔ y < x ∧ 4 ≤ y :=
      ⟨_, fun _ _ => Iff.rfl⟩
    have fP : ∀ x, x ∈ fld P → x ≤ 3 := by
      rintro x ⟨w, h | h⟩ <;> rw [hP] at h <;> omega
    have fQ : ∀ x, x ∈ fld Q → 4 ≤ x := by
      rintro x ⟨w, h | h⟩ <;> rw [hQ] at h <;> omega
    have hPs : P ∈ Ser := by
      refine mem_Ser.2 ⟨⟨fun x h => ?_, fun x y z h => ?_⟩, fun x y h => ?_⟩
      · rw [hP] at h; omega
      · rw [hP, hP] at h; rw [hP]; omega
      · have := fP x h.1; have := fP y h.2
        rw [hP, hP]; omega
    have hQs : Q ∈ Ser := by
      refine mem_Ser.2 ⟨⟨fun x h => ?_, fun x y z h => ?_⟩, fun x y h => ?_⟩
      · rw [hQ] at h; omega
      · rw [hQ, hQ] at h; rw [hQ]; omega
      · have := fQ x h.1; have := fQ y h.2
        rw [hQ, hQ]; omega
    have hd : fld P ∩ fld Q = Λ := by
      rw [Null_eq_empty]
      refine Set.eq_empty_iff_forall_notMem.2 fun z ⟨h1, h2⟩ => ?_
      have := fP z h1; have := fQ z h2; omega
    have hor : ¬EDesc Beg P ∨ ¬EDesc Beg Q := by
      right; rintro ⟨b, hb⟩
      obtain ⟨⟨w, hw⟩, hn⟩ := (hb b).2 rfl
      rw [hQ] at hw
      exact hn ⟨b + 1, (hQ _ _).2 ⟨by omega, by omega⟩⟩
    have hPimg : ∀ n x : ℕ, x ∈ P ʻʻ {n} ↔ x < n ∧ n ≤ 3 := by
      intro n x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hy' : y = n := hy
        rw [hy'] at hxy
        exact (hP x n).1 hxy
      · intro h; exact ⟨n, rfl, (hP x n).2 h⟩
    have hQimg : ∀ n x : ℕ, x ∈ Q ʻʻ {n} ↔ n < x ∧ 4 ≤ n := by
      intro n x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hy' : y = n := hy
        rw [hy'] at hxy
        exact (hQ x n).1 hxy
      · intro h; exact ⟨n, rfl, (hQ x n).2 h⟩
    have h2d : (2 : ℕ) ∈ dom P := ⟨3, (hP 2 3).2 ⟨by omega, le_rfl⟩⟩
    have h5d : (5 : ℕ) ∈ dom Q := ⟨4, (hQ 5 4).2 ⟨by omega, le_rfl⟩⟩
    have memP : ∀ U : Set ℕ, (0 : ℕ) ∈ U → (2 : ℕ) ∉ U → U ∈ (ι Λ)ᶜ \ ι (dom P) :=
      fun U h0 h2 => ⟨b2_not_mem_iotaNull.2 ⟨0, h0⟩, fun e' => h2 ((b2_mem_iota.1 e') ▸ h2d)⟩
    have memQ : ∀ U : Set ℕ, (7 : ℕ) ∈ U → (5 : ℕ) ∉ U → U ∈ (ι Λ)ᶜ \ ι (dom Q) :=
      fun U h7 h5 => ⟨b2_not_mem_iotaNull.2 ⟨7, h7⟩, fun e' => h5 ((b2_mem_iota.1 e') ▸ h5d)⟩
    have hXp : (segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P))) (P ʻʻ {1}) (P ʻʻ {2}) := by
      refine ⟨⟨memP _ ((hPimg 1 0).2 ⟨by omega, by omega⟩)
        (fun h => by have := (hPimg 1 2).1 h; omega),
        (b2_segSer_ser hPs).2 ⟨⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, fun z hz => ?_, fun e' => ?_⟩⟩,
        memP _ ((hPimg 2 0).2 ⟨by omega, by omega⟩) (fun h => by have := (hPimg 2 2).1 h; omega)⟩
      · have := (hPimg 1 z).1 hz; exact (hPimg 2 z).2 ⟨by omega, by omega⟩
      · have h1 : (1 : ℕ) ∈ P ʻʻ {2} := (hPimg 2 1).2 ⟨by omega, by omega⟩
        rw [← e'] at h1
        have := (hPimg 1 1).1 h1; omega
    have hYp : (segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q))) (Q ʻʻ {6}) (Q ʻʻ {5}) := by
      refine ⟨⟨memQ _ ((hQimg 6 7).2 ⟨by omega, by omega⟩)
        (fun h => by have := (hQimg 6 5).1 h; omega),
        (b2_segSer_ser hQs).2 ⟨⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, fun z hz => ?_, fun e' => ?_⟩⟩,
        memQ _ ((hQimg 5 7).2 ⟨by omega, by omega⟩) (fun h => by have := (hQimg 5 5).1 h; omega)⟩
      · have := (hQimg 6 z).1 hz; exact (hQimg 5 z).2 ⟨by omega, by omega⟩
      · have h6 : (6 : ℕ) ∈ Q ʻʻ {5} := (hQimg 5 6).2 ⟨by omega, by omega⟩
        rw [← e'] at h6
        have := (hQimg 6 6).1 h6; omega
    have r := H P Q _ _ _ _ ∅ ⟨⟨⟨⟨⟨⟨⟨⟨hPs, hQs⟩, hd⟩, hor⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩,
      fun h => h.elim (nE _ _ fun _ h' => h'.1) (nE _ _ fun _ h' => h'.1)⟩
      ⟨_, _, hXp⟩ ⟨_, _, hYp⟩
    obtain ⟨⟨-, hcod⟩, hsemi⟩ := r
    have hW : ((segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P)))˘ ⇸ ∅ ⤉ segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q)))
        (P ʻʻ {1}) ∅ :=
      (rsum_apply _ _ _ _).2 (Or.inl (Or.inl
        ((addLast_apply _ _ _ _).2 (Or.inr ⟨⟨_, Or.inr hXp⟩, rfl⟩))))
    have hc : P ʻʻ {1} ∈ fld ((segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P)))˘ ⇸ ∅ ⤉
        segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q))) := ⟨∅, Or.inl hW⟩
    rw [hcod] at hc
    obtain ⟨a, ha⟩ := hc
    have hZ := (semi_apply _ _ _ _).2 ⟨_, _, ⟨ha, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩, hW⟩
    rw [← hsemi] at hZ
    obtain ⟨B, hB⟩ := hZ.1.2.2
    have hB' : dom P = (P˘ ⤉ Q) ʻʻ B := hB
    have hT : ∀ x y, (P˘ ⤉ Q) x y ↔ (P y x ∨ Q x y) ∨ (x ∈ fld P ∧ y ∈ fld Q) := by
      intro x y; rw [rsum_apply, fld_cnv]; exact Iff.rfl
    have h0 : (0 : ℕ) ∈ dom P := ⟨1, (hP 0 1).2 ⟨by omega, by omega⟩⟩
    rw [hB'] at h0
    obtain ⟨y, hy, hy0⟩ := h0
    rw [hT] at hy0
    rcases hy0 with (h | h) | ⟨-, hyQ⟩
    · rw [hP] at h; omega
    · rw [hQ] at h; omega
    · have h3 : (3 : ℕ) ∈ (P˘ ⤉ Q) ʻʻ B :=
        ⟨y, hy, (hT 3 y).2 (Or.inr ⟨⟨2, Or.inr ((hP 2 3).2 ⟨by omega, le_rfl⟩)⟩, hyQ⟩)⟩
      rw [← hB'] at h3
      obtain ⟨w, hw⟩ := h3
      rw [hP] at hw; omega
  · have hN : ∀ x y, ¬(rNull : ℕ → ℕ → Prop) x y := fun x y => rNull_apply x y
    have hNs : (rNull : ℕ → ℕ → Prop) ∈ Ser := by
      refine mem_Ser.2 ⟨⟨fun x h => hN x x h, fun x y z h => (hN x y h.1).elim⟩, ?_⟩
      rintro x y ⟨⟨w, hw | hw⟩, -⟩ <;> exact (hN _ _ hw).elim
    have hfN : fld (rNull : ℕ → ℕ → Prop) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun _ ⟨_, h⟩ => h.elim (hN _ _) (hN _ _)
    have hnE : ¬EDesc Beg (rNull : ℕ → ℕ → Prop) := by
      rintro ⟨b, hb⟩
      obtain ⟨⟨w, hw⟩, -⟩ := (hb b).2 rfl
      exact hN _ _ hw
    have nX : ∀ (E : Set (Set ℕ)) (U V : Set ℕ), ¬(segSer (rNull : ℕ → ℕ → Prop) ⥏ E) U V :=
      fun E U V h => b2_segSer_rNull_none _ _ h.1.2
    have fX : ∀ (E : Set (Set ℕ)) (U : Set ℕ), U ∉ fld (segSer (rNull : ℕ → ℕ → Prop) ⥏ E) :=
      fun E U ⟨V, h⟩ => h.elim (nX E U V) (nX E V U)
    have r := H rNull rNull _ _ _ _ ∅ ⟨⟨⟨⟨⟨⟨⟨⟨hNs, hNs⟩, by rw [hfN, Set.inter_empty, Null_eq_empty]⟩,
      Or.inl hnE⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, fun h => h.elim (fX _ _) (fX _ _)⟩
    have hA : (∅ : Set ℕ) ∈ fld ((segSer (rNull : ℕ → ℕ → Prop) ⥏
        ((ι Λ)ᶜ \ ι (dom (rNull : ℕ → ℕ → Prop))))˘ ⇸ ∅ ⤉
        segSer (rNull : ℕ → ℕ → Prop) ⥏ ((ι Λ)ᶜ \ ι (dom (rNull : ℕ → ℕ → Prop)))) := by
      rw [r.1.2]
      exact ⟨codom (rNull : ℕ → ℕ → Prop), Or.inl (Or.inr ⟨rfl, rfl⟩)⟩
    obtain ⟨V, h | h⟩ := hA
    · rcases (rsum_apply _ _ _ _).1 h with ((h' | ⟨h', -⟩) | h') | ⟨h', -⟩
      · exact nX _ _ _ h'
      · exact fX _ _ (by rw [fld_cnv] at h'; exact h')
      · exact nX _ _ _ h'
      · obtain ⟨-, hr⟩ := b2r_mem_fld_addLast.1 h'
        obtain ⟨a, b, hab⟩ := hr
        exact nX _ _ _ hab
    · rcases (rsum_apply _ _ _ _).1 h with ((h' | ⟨h', -⟩) | h') | ⟨-, h'⟩
      · exact nX _ _ _ h'
      · exact fX _ _ (by rw [fld_cnv] at h'; exact h')
      · exact nX _ _ _ h'
      · exact fX _ _ h'

/-- ✱217·43. \[\begin{align}&\vdash \colon\ldotp P,Q\in \text{Ser}.CʻP\cap CʻQ=\Lambda :{\sim}\text{E}!BʻP.\lor.{\sim}\text{E}!BʻQ:\\ &X=(\varsigma ʻP)\unicode{x0294f}(-{℩}ʻ\Lambda -{℩}ʻ\text{D}ʻP).Y=(\varsigma ʻQ)\unicode{x0294f}(-{℩}ʻ\Lambda -{℩}ʻ\text{D}ʻQ).\\ &Z=\{\varsigma ʻ(\breve{P} \unicode{x2909} Q)\}\unicode{x0294f}\{-{℩}ʻ\Lambda -{℩}ʻ\text{D}ʻ(\breve{P} \unicode{x2909} Q)\}.\\ &W=\breve{X} \unicode{x21f8}\alpha \unicode{x2909} Y.\alpha {\sim}\in CʻX\cup CʻY.\supset .\\ &(\breve{P} )_{\in }\mid (CʻP-)\upharpoonright (\text{D}ʻP_{\in }-{℩}ʻ\Lambda -{℩}ʻ\text{D}ʻP)\unicode{x228d} (\text{D}ʻP)\downarrow \alpha \\ &\unicode{x228d} (CʻP\cup )\upharpoonright (\text{D}ʻQ_{\in }-{℩}ʻ\Lambda -{℩}ʻ\text{D}ʻQ)\in Z\,\overline{\text{smor}}\,\,W \quad[*217·37·25·42]\end{align}\]

**Status.** proved (corrected): (1) the couple `(D'P) ↓ α` of the correlator is read `(ᗡ'P) ↓ α`:
`α` stands in `W` for the term `ᗡ'P` (`= P̆''C'P`, the last segment of `P̆`) of ✱217·42, while
`D'P` is a segment of `P̆ ⤉ Q` only when `D'P = ᗡ'P` (`P` without beginning and end, as in Part VI,
Section A); (2) it inherits the degenerate failures of ✱217·42, so `∃̇!X . ∃̇!Y` are added.
`pm217_43_printed_false` proves that both are needed: the printed correlator fails even with
`∃̇!X . ∃̇!Y` (`P` the series `0, 1, 2, 3`, `Q` the series `…, 5, 4`, where `D'P ∉ C'Z`), and the
corrected one fails without them (`P = Q = Λ̇`, where `C'W = Λ` but `α ∈ ᗡ'S`). -/
theorem pm217_43 {P Q : α → α → Prop} {X Y Z W : Set α → Set α → Prop} {A : Set α}
    (h : (((((((P ∈ Ser ∧ Q ∈ Ser) ∧ fld P ∩ fld Q = Λ) ∧ (¬EDesc Beg P ∨ ¬EDesc Beg Q)) ∧
      X = segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P))) ∧ Y = segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q))) ∧
      Z = segSer (P˘ ⤉ Q) ⥏ ((ι Λ)ᶜ \ ι (dom (P˘ ⤉ Q)))) ∧ W = X˘ ⇸ A ⤉ Y) ∧
      A ∉ fld X ∪ fld Y)
    (hX : rEx X) (hY : rEx Y) :
    (imgRel P˘ ⨾ opL (· \ ·) (fld P)) ↾ ((dom (imgRel P) \ ι Λ) \ ι (dom P)) ⊍ codom P ↓ A ⊍
      opL (· ∪ ·) (fld P) ↾ ((dom (imgRel Q) \ ι Λ) \ ι (dom Q)) ∈ smorbar Z W := by
  classical
  obtain ⟨⟨⟨⟨⟨⟨hSd, hor⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hA⟩ := h
  have h42 := pm217_42 ⟨hSd, hor⟩ hX hY
  obtain ⟨⟨hPs, hQs⟩, hd⟩ := hSd
  have hPne := b2_rEx_of_segfres hPs hX
  have hQne := b2_rEx_of_segfres hQs hY
  have hDD : dom (P˘ ⤉ Q) = dom (P ⤉ Q) := by
    rw [b2_dom_rsum hQne, b2_dom_rsum hQne, fld_cnv]
  have hfX : fld (segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P))) = (dom (imgRel P) \ ι Λ) \ ι (dom P) := by
    rw [b2_fld_fres_ser (pm214_33 ⟨b2_ser_tc hPs, hPne⟩).1 hX, b2_fld_segSer_ser hPs hPne]
    ext G
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  have hfY : fld (segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q))) = (dom (imgRel Q) \ ι Λ) \ ι (dom Q) := by
    rw [b2_fld_fres_ser (pm214_33 ⟨b2_ser_tc hQs, hQne⟩).1 hY, b2_fld_segSer_ser hQs hQne]
    ext G
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  have hNsub : ∀ z, z ∈ (dom (imgRel P) \ ι Λ) \ ι (dom P) → z ⊆ fld P ∧ z.Nonempty :=
    fun z hz => ⟨b2_seg_sub hz.1.1, b2_not_mem_iotaNull.1 hz.1.2⟩
  have hMsub : ∀ z, z ∈ (dom (imgRel Q) \ ι Λ) \ ι (dom Q) → z ⊆ fld Q ∧ z.Nonempty :=
    fun z hz => ⟨b2_seg_sub hz.1.1, b2_not_mem_iotaNull.1 hz.1.2⟩
  have hAN : A ∉ (dom (imgRel P) \ ι Λ) \ ι (dom P) := fun h' => hA (Or.inl (by rw [hfX]; exact h'))
  have hAM : A ∉ (dom (imgRel Q) \ ι Λ) \ ι (dom Q) := fun h' => hA (Or.inr (by rw [hfY]; exact h'))
  have hfW : ∀ z, z ∈ fld ((segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P)))˘ ⇸ A ⤉
      segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q))) ↔
      (z ∈ (dom (imgRel P) \ ι Λ) \ ι (dom P) ∨ z = A) ∨
        z ∈ (dom (imgRel Q) \ ι Λ) \ ι (dom Q) := by
    intro z
    have hXc : rEx (segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P)))˘ := let ⟨a, b, hab⟩ := hX; ⟨b, a, hab⟩
    rw [fld_rsum, Set.mem_union, b2r_mem_fld_addLast, fld_cnv, hfX, hfY]
    simp only [hXc, and_true]
  obtain ⟨s, hs⟩ : ∃ s : Set α → Set α, ∀ z, s z =
      if z = A then codom P else if z ⊆ fld P then P˘ ʻʻ (fld P \ z) else fld P ∪ z :=
    ⟨_, fun _ => rfl⟩
  have sN : ∀ z, z ∈ (dom (imgRel P) \ ι Λ) \ ι (dom P) → s z = P˘ ʻʻ (fld P \ z) := by
    intro z hz
    rw [hs]
    split_ifs with h1 h2
    · exact (hAN (by rw [← h1]; exact hz)).elim
    · rfl
    · exact absurd (hNsub z hz).1 h2
  have sM : ∀ z, z ∈ (dom (imgRel Q) \ ι Λ) \ ι (dom Q) → s z = fld P ∪ z := by
    intro z hz
    rw [hs]
    split_ifs with h1 h2
    · exact (hAM (by rw [← h1]; exact hz)).elim
    · obtain ⟨w, hw⟩ := (hMsub z hz).2
      exact (b2_disj hd (h2 hw) ((hMsub z hz).1 hw)).elim
    · rfl
  have sA : s A = codom P := by
    rw [hs]
    split_ifs with h1 <;> first | rfl | exact absurd rfl h1
  have hKx : ∀ x z, (imgRel P˘ ⨾ opL (· \ ·) (fld P)) x z ↔ x = P˘ ʻʻ (fld P \ z) := fun x z =>
    ⟨fun ⟨U, h1, h2⟩ => (h1 : x = P˘ ʻʻ U).trans (congrArg (P˘ ʻʻ ·) (h2 : U = fld P \ z)),
      fun h' => ⟨_, h', rfl⟩⟩
  have hS : ∀ x z, ((imgRel P˘ ⨾ opL (· \ ·) (fld P)) ↾ ((dom (imgRel P) \ ι Λ) \ ι (dom P)) ⊍
      codom P ↓ A ⊍ opL (· ∪ ·) (fld P) ↾ ((dom (imgRel Q) \ ι Λ) \ ι (dom Q))) x z ↔
      x = s z ∧ ((z ∈ (dom (imgRel P) \ ι Λ) \ ι (dom P) ∨ z = A) ∨
        z ∈ (dom (imgRel Q) \ ι Λ) \ ι (dom Q)) := by
    intro x z
    constructor
    · rintro ((⟨h1, hz⟩ | ⟨rfl, rfl⟩) | ⟨rfl, hz⟩)
      · exact ⟨((hKx x z).1 h1).trans (sN z hz).symm, Or.inl (Or.inl hz)⟩
      · exact ⟨sA.symm, Or.inl (Or.inr rfl)⟩
      · exact ⟨(sM z hz).symm, Or.inr hz⟩
    · rintro ⟨rfl, (hz | hz) | hz⟩
      · exact Or.inl (Or.inl ⟨(hKx _ z).2 (sN z hz), hz⟩)
      · subst hz; exact Or.inl (Or.inr ⟨sA, rfl⟩)
      · exact Or.inr ⟨sM z hz, hz⟩
  have hcod : codom P = P˘ ʻʻ (fld P \ ∅) := (b2_f_empty P).symm
  have fe : ∀ G, G ∈ dom (imgRel P) → ∀ H, H ∈ (dom (imgRel Q) \ ι Λ) \ ι (dom Q) →
      P˘ ʻʻ (fld P \ G) ≠ fld P ∪ H := fun G _ H hH =>
    (b2_f_lt_g hd G (hMsub H hH).1 (hMsub H hH).2).1.2
  have s_inj : ∀ z z', ((z ∈ (dom (imgRel P) \ ι Λ) \ ι (dom P) ∨ z = A) ∨
      z ∈ (dom (imgRel Q) \ ι Λ) \ ι (dom Q)) →
      ((z' ∈ (dom (imgRel P) \ ι Λ) \ ι (dom P) ∨ z' = A) ∨
        z' ∈ (dom (imgRel Q) \ ι Λ) \ ι (dom Q)) → s z = s z' → z = z' := by
    rintro z z' ((hz | hz) | hz) ((hz' | hz') | hz') e
    · rw [sN z hz, sN z' hz'] at e; exact b2_f_inj hPs hz.1.1 hz'.1.1 e
    · rw [sN z hz, hz', sA, hcod] at e
      exact absurd (b2_f_inj hPs hz.1.1 (b2_seg_empty P) e) (hNsub z hz).2.ne_empty
    · rw [sN z hz, sM z' hz'] at e; exact absurd e (fe z hz.1.1 z' hz')
    · rw [hz, sA, sN z' hz', hcod] at e
      exact absurd (b2_f_inj hPs (b2_seg_empty P) hz'.1.1 e).symm (hNsub z' hz').2.ne_empty
    · rw [hz, hz']
    · rw [hz, sA, sM z' hz', hcod] at e; exact absurd e (fe ∅ (b2_seg_empty P) z' hz')
    · rw [sM z hz, sN z' hz'] at e; exact absurd e.symm (fe z' hz'.1.1 z hz)
    · rw [sM z hz, hz', sA, hcod] at e; exact absurd e.symm (fe ∅ (b2_seg_empty P) z hz)
    · rw [sM z hz, sM z' hz'] at e
      exact b2_g_inj hd (hMsub z hz).1 (hMsub z' hz').1 e
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_arrow_one_one]
    refine ⟨fun x y z ⟨h1, h2⟩ => ((hS x z).1 h1).1.trans ((hS y z).1 h2).1.symm,
      fun x z z' ⟨h1, h2⟩ => ?_⟩
    obtain ⟨e1, hz⟩ := (hS x z).1 h1
    obtain ⟨e2, hz'⟩ := (hS x z').1 h2
    exact s_inj z z' hz hz' (e1.symm.trans e2)
  · ext z
    rw [hfW]
    constructor
    · intro hz; exact ⟨s z, (hS _ z).2 ⟨rfl, hz⟩⟩
    · rintro ⟨x, hx⟩; exact ((hS x z).1 hx).2
  · rw [b2_K_eq, b2_U_eq] at h42
    rw [hDD, h42]
    symm
    have hsX : ∀ z, z ∈ fld (segSer P ⥏ ((ι Λ)ᶜ \ ι (dom P)))˘ → s z = P˘ ʻʻ (fld P \ z) :=
      fun z hz => sN z (by rw [fld_cnv, hfX] at hz; exact hz)
    have hsY : ∀ z, z ∈ fld (segSer Q ⥏ ((ι Λ)ᶜ \ ι (dom Q))) → s z = fld P ∪ z :=
      fun z hz => sM z (by rw [hfY] at hz; exact hz)
    rw [b2r_semi_congr (T := graph s) fun x z hz => (hS x z).trans
        ⟨fun h' => h'.1, fun h' => ⟨h', (hfW z).1 hz⟩⟩,
      b2r_graph_semi_rsum, b2r_graph_semi_addLast, sA, b2r_graph_semi_congr hsX,
      b2r_graph_semi_congr hsY]


end S217

end PrincipiaMathematica
