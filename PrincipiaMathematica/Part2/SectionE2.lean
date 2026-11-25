import PrincipiaMathematica.Defs.Part2

/-!
# Part II, Section E: Inductive relations

Volume 1. Numbers: ✱94, ✱95, ✱96, ✱97.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

open Relation

universe u v w u' v'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'} {ε : Type v'}

/-! ### Helper lemmas (not PM propositions)

`npow R n` is the `n`-fold relative power (`npow R 0` the identity of the whole type) and
`ipow R n` the member `(I ↾ C'R) | R^n` of `Potid'R`; `Pot'R` consists of the `npow R (n + 1)`
(`mem_pot_npow`) and `Potid'R` of the `ipow R n` (`mem_potid'`). The first group of lemmas
(`rp_assoc` … `anc_img_eq`) is shared with the helpers of `Part2/SectionE.lean`. -/

private theorem rp_assoc (R : α → β → Prop) (S : β → γ → Prop) (T : γ → δ → Prop) :
    R ⨾ S ⨾ T = R ⨾ (S ⨾ T) := by
  funext x w
  apply propext
  constructor
  · rintro ⟨z, ⟨y, h1, h2⟩, h3⟩
    exact ⟨y, h1, z, h2, h3⟩
  · rintro ⟨y, h1, z, h2, h3⟩
    exact ⟨z, ⟨y, h1, h2⟩, h3⟩

/-- `R^n`, exactly `n` steps; `npow R 0` is identity (on the whole type). -/
private def npow (R : α → α → Prop) : ℕ → α → α → Prop
  | 0 => fun x y => x = y
  | n + 1 => npow R n ⨾ R

private theorem npow_zero_apply {R : α → α → Prop} {x y : α} : npow R 0 x y ↔ x = y := Iff.rfl

private theorem npow_succ (R : α → α → Prop) (n : ℕ) : npow R (n + 1) = npow R n ⨾ R := rfl

private theorem comp_npow_zero (R : α → α → Prop) (Q : γ → α → Prop) : Q ⨾ npow R 0 = Q := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, h, rfl⟩
    exact h
  · intro h
    exact ⟨y, h, rfl⟩

private theorem npow_zero_comp (R : α → α → Prop) (Q : α → γ → Prop) : npow R 0 ⨾ Q = Q := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, rfl, h⟩
    exact h
  · intro h
    exact ⟨x, rfl, h⟩

private theorem npow_one (R : α → α → Prop) : npow R 1 = R := npow_zero_comp R R

private theorem npow_succ' (R : α → α → Prop) (n : ℕ) : npow R (n + 1) = R ⨾ npow R n := by
  induction n with
  | zero => rw [npow_one, comp_npow_zero]
  | succ n ih =>
    show npow R (n + 1) ⨾ R = R ⨾ (npow R n ⨾ R)
    rw [ih, rp_assoc]

private theorem npow_add (R : α → α → Prop) (m n : ℕ) : npow R (m + n) = npow R m ⨾ npow R n := by
  induction n with
  | zero => rw [comp_npow_zero]; rfl
  | succ n ih => rw [← Nat.add_assoc, npow_succ, ih, rp_assoc, ← npow_succ]

private theorem npow_comm (R : α → α → Prop) (m n : ℕ) :
    npow R m ⨾ npow R n = npow R n ⨾ npow R m := by
  rw [← npow_add, ← npow_add, Nat.add_comm]

private theorem npow_succ_iff {R : α → α → Prop} {n : ℕ} {x y : α} :
    npow R (n + 1) x y ↔ ∃ a, R x a ∧ npow R n a y := by
  rw [npow_succ']
  exact Iff.rfl

private theorem npow_mul (R : α → α → Prop) (m j : ℕ) : npow (npow R m) j = npow R (m * j) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [npow_succ, ih, Nat.mul_succ, npow_add]

private theorem rtg_iff_npow {R : α → α → Prop} {x y : α} :
    ReflTransGen R x y ↔ ∃ n, npow R n x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, _, hn, hbc⟩
  · rintro ⟨n, hn⟩
    induction n generalizing y with
    | zero => cases hn; exact ReflTransGen.refl
    | succ n ih =>
      obtain ⟨b, hb, hby⟩ := hn
      exact ReflTransGen.tail (ih hb) hby

private theorem tg_iff_npow {R : α → α → Prop} {x y : α} :
    TransGen R x y ↔ ∃ n, npow R (n + 1) x y := by
  constructor
  · intro h
    induction h with
    | single h => exact ⟨0, _, rfl, h⟩
    | tail _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, _, hn, hbc⟩
  · rintro ⟨n, b, hb, hby⟩
    exact TransGen.tail' (rtg_iff_npow.2 ⟨n, hb⟩) hby

private theorem fld_of_npow_succ {R : α → α → Prop} {n : ℕ} {x y : α} (h : npow R (n + 1) x y) :
    x ∈ fld R ∧ y ∈ fld R := by
  have h' := h
  obtain ⟨b, -, hby⟩ := h
  obtain ⟨a, hxa, -⟩ := npow_succ_iff.1 h'
  exact ⟨⟨a, Or.inl hxa⟩, ⟨b, Or.inr hby⟩⟩

private theorem anc_iff_npow {R : α → α → Prop} {x y : α} :
    anc R x y ↔ x ∈ fld R ∧ ∃ n, npow R n x y := by
  rw [anc_iff_reflTransGen, rtg_iff_npow]

private theorem po_iff_npow {R : α → α → Prop} {x y : α} :
    po R x y ↔ ∃ n, npow R (n + 1) x y := by
  rw [po_iff_transGen, tg_iff_npow]

/-- `R^n` with `R^0 = I ↾ C'R`: the members of `Potid'R`. -/
private def ipow (R : α → α → Prop) (n : ℕ) : α → α → Prop := (I ↾ fld R) ⨾ npow R n

private theorem ipow_apply {R : α → α → Prop} {n : ℕ} {x y : α} :
    ipow R n x y ↔ x ∈ fld R ∧ npow R n x y := by
  constructor
  · rintro ⟨a, ⟨rfl, ha⟩, h⟩
    exact ⟨ha, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨x, ⟨rfl, hx⟩, h⟩

private theorem ipow_zero_apply {R : α → α → Prop} {x y : α} :
    ipow R 0 x y ↔ x = y ∧ y ∈ fld R := by
  rw [ipow_apply, npow_zero_apply]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨h, rfl⟩

private theorem ipow_zero (R : α → α → Prop) : ipow R 0 = I ↾ fld R := comp_npow_zero R _

private theorem ipow_succ_eq (R : α → α → Prop) (n : ℕ) : ipow R (n + 1) = npow R (n + 1) := by
  funext x y
  apply propext
  rw [ipow_apply]
  exact ⟨fun h => h.2, fun h => ⟨(fld_of_npow_succ h).1, h⟩⟩

private theorem fld_of_ipow {R : α → α → Prop} {n : ℕ} {x y : α} (h : ipow R n x y) :
    x ∈ fld R ∧ y ∈ fld R := by
  cases n with
  | zero =>
    obtain ⟨rfl, h⟩ := ipow_zero_apply.1 h
    exact ⟨h, h⟩
  | succ n =>
    rw [ipow_succ_eq] at h
    exact fld_of_npow_succ h

private theorem ipow_add (R : α → α → Prop) (m n : ℕ) : ipow R (m + n) = ipow R m ⨾ npow R n := by
  rw [ipow, npow_add, ← rp_assoc]
  rfl

private theorem ipow_succ (R : α → α → Prop) (n : ℕ) : ipow R (n + 1) = ipow R n ⨾ R := by
  rw [ipow_add, npow_one]

private theorem ipow_one (R : α → α → Prop) : ipow R 1 = R := by
  rw [ipow_succ_eq, npow_one]

private theorem ipow_comp_idf (R : α → α → Prop) (n : ℕ) : ipow R n ⨾ (I ↾ fld R) = ipow R n := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a, h, rfl, -⟩
    exact h
  · intro h
    exact ⟨y, h, rfl, (fld_of_ipow h).2⟩

private theorem idf_comp_ipow (R : α → α → Prop) (n : ℕ) : (I ↾ fld R) ⨾ ipow R n = ipow R n := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a, ⟨rfl, -⟩, h⟩
    exact h
  · intro h
    exact ⟨x, ⟨rfl, (fld_of_ipow h).1⟩, h⟩

private theorem ipow_mul (R : α → α → Prop) (m n : ℕ) : ipow R m ⨾ ipow R n = ipow R (m + n) := by
  rw [ipow_add]
  conv_lhs => rw [show ipow R n = (I ↾ fld R) ⨾ npow R n from rfl, ← rp_assoc, ipow_comp_idf]

private theorem ipow_comm (R : α → α → Prop) (m n : ℕ) :
    ipow R m ⨾ ipow R n = ipow R n ⨾ ipow R m := by
  rw [ipow_mul, ipow_mul, Nat.add_comm]

private theorem ipow_succ' (R : α → α → Prop) (n : ℕ) : ipow R (n + 1) = R ⨾ ipow R n := by
  rw [show R ⨾ ipow R n = ipow R 1 ⨾ ipow R n by rw [ipow_one], ipow_mul, Nat.add_comm]

private theorem anc_iff_ipow {R : α → α → Prop} {x y : α} : anc R x y ↔ ∃ n, ipow R n x y := by
  rw [anc_iff_npow]
  constructor
  · rintro ⟨hx, n, h⟩
    exact ⟨n, ipow_apply.2 ⟨hx, h⟩⟩
  · rintro ⟨n, h⟩
    exact ⟨(ipow_apply.1 h).1, n, (ipow_apply.1 h).2⟩

private theorem po_iff_ipow {R : α → α → Prop} {x y : α} : po R x y ↔ ∃ n, ipow R (n + 1) x y := by
  rw [po_iff_npow]
  simp only [ipow_succ_eq]

private theorem anc_rtg_of_total {ε : Type*} {r : ε → ε → Prop} (h : ∀ a, ∃ b, r b a)
    {a b : ε} : anc r a b ↔ ReflTransGen r a b := by
  rw [anc_iff_reflTransGen]
  exact ⟨fun h' => h'.2, fun h' => ⟨(h a).elim fun c hc => ⟨c, Or.inr hc⟩, h'⟩⟩

private theorem Rts_iff (R : α → α → Prop) (P Q : γ → α → Prop) :
    Rts R P Q ↔ ∃ n, P = Q ⨾ npow R n := by
  rw [Rts, anc_rtg_of_total (fun X => ⟨X ⨾ R, rfl⟩)]
  constructor
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ⟨0, (comp_npow_zero R Q).symm⟩
    | head hac _ ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [relProdR_apply] at hac
      rw [hac, hn, rp_assoc, ← npow_succ]
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => rw [comp_npow_zero]
    | succ n ih =>
      refine ReflTransGen.head ?_ ih
      rw [relProdR_apply, npow_succ, rp_assoc]

private theorem Rst_iff (R : α → α → Prop) (P Q : α → γ → Prop) :
    Rst R P Q ↔ ∃ n, P = npow R n ⨾ Q := by
  rw [Rst, anc_rtg_of_total (fun X => ⟨R ⨾ X, rfl⟩)]
  constructor
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ⟨0, (npow_zero_comp R Q).symm⟩
    | head hac _ ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [relProdL_apply] at hac
      rw [hac, hn, ← rp_assoc, ← npow_succ']
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => rw [npow_zero_comp]
    | succ n ih =>
      refine ReflTransGen.head ?_ ih
      rw [relProdL_apply, npow_succ', rp_assoc]

private theorem mem_pot' {R P : α → α → Prop} : P ∈ pot R ↔ ∃ n, P = ipow R (n + 1) := by
  show Rts R P R ↔ _
  rw [Rts_iff]
  simp only [ipow_succ_eq, npow_succ']

private theorem mem_potid' {R P : α → α → Prop} : P ∈ potid R ↔ ∃ n, P = ipow R n := by
  show Rts R P (I ↾ fld R) ↔ _
  rw [Rts_iff]
  rfl

private theorem ipow_mem_potid (R : α → α → Prop) (n : ℕ) : ipow R n ∈ potid R :=
  mem_potid'.2 ⟨n, rfl⟩

private theorem ipow_succ_mem_pot (R : α → α → Prop) (n : ℕ) : ipow R (n + 1) ∈ pot R :=
  mem_pot'.2 ⟨n, rfl⟩

private theorem pot_sub_potid (R : α → α → Prop) : pot R ⊆ potid R := by
  intro P hP
  obtain ⟨n, rfl⟩ := mem_pot'.1 hP
  exact ipow_mem_potid R _

/-- one-many (`1 → Cls`) relations. -/
private theorem npow_oneMany {R : α → α → Prop} (hR : ∀ x y z, R x z ∧ R y z → x = y) (n : ℕ) :
    ∀ x y z, npow R n x z ∧ npow R n y z → x = y := by
  induction n with
  | zero => rintro x y z ⟨rfl, rfl⟩; rfl
  | succ n ih =>
    rintro x y z ⟨⟨a, hxa, haz⟩, ⟨b, hyb, hbz⟩⟩
    have hab : a = b := hR a b z ⟨haz, hbz⟩
    subst hab
    exact ih x y a ⟨hxa, hyb⟩

private theorem npow_manyOne {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z) (n : ℕ) :
    ∀ x y z, npow R n x y ∧ npow R n x z → y = z := by
  induction n with
  | zero => rintro x y z ⟨rfl, rfl⟩; rfl
  | succ n ih =>
    rintro x y z ⟨⟨a, hxa, hay⟩, ⟨b, hxb, hbz⟩⟩
    have hab : a = b := ih x a b ⟨hxa, hxb⟩
    subst hab
    exact hR a y z ⟨hay, hbz⟩


private theorem anc_fld_right {R : α → α → Prop} {x y : α} (h : anc R x y) : y ∈ fld R := by
  obtain ⟨hx, n, hn⟩ := anc_iff_npow.1 h
  cases n with
  | zero =>
    have e : x = y := hn
    exact e ▸ hx
  | succ n => exact (fld_of_npow_succ hn).2

private theorem anc_refl {R : α → α → Prop} {x : α} (h : x ∈ fld R) : anc R x x :=
  ⟨h, fun _ ⟨_, hM⟩ => hM⟩

private theorem R_sub_anc {R : α → α → Prop} {x y : α} (h : R x y) : anc R x y :=
  anc_iff_reflTransGen.2 ⟨⟨y, Or.inl h⟩, ReflTransGen.single h⟩

private theorem anc_trans {R : α → α → Prop} {x y z : α} (h1 : anc R x y) (h2 : anc R y z) :
    anc R x z := by
  rw [anc_iff_reflTransGen] at *
  exact ⟨h1.1, h1.2.trans h2.2⟩

private theorem anc_tail {R : α → α → Prop} {x y z : α} (h1 : anc R x y) (h2 : R y z) :
    anc R x z := anc_trans h1 (R_sub_anc h2)

private theorem anc_head {R : α → α → Prop} {x y z : α} (h1 : R x y) (h2 : anc R y z) :
    anc R x z := anc_trans (R_sub_anc h1) h2

private theorem fld_cnv (R : α → α → Prop) : fld R˘ = fld R := by
  ext z
  exact ⟨fun ⟨w, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, h.symm⟩⟩

private theorem img_comp (S : α → β → Prop) (T : β → γ → Prop) (A : Set γ) :
    S ʻʻ T ʻʻ A = (S ⨾ T) ʻʻ A := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    exact ⟨z, hz, y, hxy, hyz⟩
  · rintro ⟨z, hz, y, hxy, hyz⟩
    exact ⟨y, ⟨z, hz, hyz⟩, hxy⟩

private theorem img_rcup (S T : α → β → Prop) (A : Set β) : (S ⊍ T) ʻʻ A = S ʻʻ A ∪ T ʻʻ A := by
  ext x
  constructor
  · rintro ⟨y, hy, h | h⟩
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr ⟨y, hy, h⟩
  · rintro (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
    · exact ⟨y, hy, Or.inl h⟩
    · exact ⟨y, hy, Or.inr h⟩

private theorem img_idf (B A : Set α) : (I ↾ B) ʻʻ A = A ∩ B := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy, hyB⟩
    have e : x = y := hxy
    subst e
    exact ⟨hy, hyB⟩
  · rintro ⟨hx, hB⟩
    exact ⟨x, hx, rfl, hB⟩

private theorem po_eq_anc_comp (R : α → α → Prop) : po R = anc R ⨾ R := by
  funext x y
  apply propext
  rw [po_iff_npow]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨b, hb, hby⟩ := id hn
    exact ⟨b, anc_iff_npow.2 ⟨(fld_of_npow_succ hn).1, n, hb⟩, hby⟩
  · rintro ⟨b, hb, hby⟩
    obtain ⟨-, n, hn⟩ := anc_iff_npow.1 hb
    exact ⟨n, b, hn, hby⟩

private theorem po_eq_comp_anc (R : α → α → Prop) : po R = R ⨾ anc R := by
  funext x y
  apply propext
  rw [po_iff_npow]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨a, hxa, ha⟩ := npow_succ_iff.1 hn
    exact ⟨a, hxa, anc_iff_npow.2 ⟨⟨x, Or.inr hxa⟩, n, ha⟩⟩
  · rintro ⟨a, hxa, ha⟩
    obtain ⟨-, n, hn⟩ := anc_iff_npow.1 ha
    exact ⟨n, npow_succ_iff.2 ⟨a, hxa, hn⟩⟩

private theorem R_sub_po {R : α → α → Prop} {x y : α} (h : R x y) : po R x y :=
  po_iff_npow.2 ⟨0, x, rfl, h⟩

private theorem po_trans {R : α → α → Prop} {x y z : α} (h1 : po R x y) (h2 : po R y z) :
    po R x z := by
  rw [po_iff_transGen] at *
  exact h1.trans h2

private theorem po_sub_anc {R : α → α → Prop} {x y : α} (h : po R x y) : anc R x y := by
  rw [po_eq_anc_comp] at h
  obtain ⟨b, hb, hby⟩ := h
  exact anc_tail hb hby

private theorem po_eq_or_tail (R : α → α → Prop) : po R = R ⊍ po R ⨾ R := by
  funext x y
  apply propext
  constructor
  · intro h
    rw [po_eq_anc_comp] at h
    obtain ⟨b, hb, hby⟩ := h
    obtain ⟨hx, n, hn⟩ := anc_iff_npow.1 hb
    cases n with
    | zero =>
      have e : x = b := hn
      subst e
      exact Or.inl hby
    | succ n => exact Or.inr ⟨b, po_iff_npow.2 ⟨n, hn⟩, hby⟩
  · rintro (h | ⟨b, hb, hby⟩)
    · exact R_sub_po h
    · exact po_trans hb (R_sub_po hby)

private theorem po_eq_or_head (R : α → α → Prop) : po R = R ⊍ R ⨾ po R := by
  funext x y
  apply propext
  constructor
  · intro h
    rw [po_eq_comp_anc] at h
    obtain ⟨a, hxa, ha⟩ := h
    obtain ⟨hx, n, hn⟩ := anc_iff_npow.1 ha
    cases n with
    | zero =>
      have e : a = y := hn
      subst e
      exact Or.inl hxa
    | succ n => exact Or.inr ⟨a, hxa, po_iff_npow.2 ⟨n, hn⟩⟩
  · rintro (h | ⟨b, hxb, hb⟩)
    · exact R_sub_po h
    · exact po_trans (R_sub_po hxb) hb

private theorem anc_eq_idf_po (R : α → α → Prop) : anc R = I ↾ fld R ⊍ po R := by
  funext x y
  apply propext
  rw [anc_iff_po]
  constructor
  · rintro (⟨rfl, hx⟩ | h)
    · exact Or.inl ⟨rfl, hx⟩
    · exact Or.inr h
  · rintro (⟨h, hy⟩ | h)
    · have e : x = y := h
      subst e
      exact Or.inl ⟨rfl, hy⟩
    · exact Or.inr h

private theorem anc_img_eq (R : α → α → Prop) (A : Set α) :
    anc R ʻʻ A = (A ∩ fld R) ∪ po R ʻʻ A := by
  rw [anc_eq_idf_po, img_rcup, img_idf]



private theorem npow_mem_pot (R : α → α → Prop) (n : ℕ) : npow R (n + 1) ∈ pot R := by
  rw [← ipow_succ_eq]; exact ipow_succ_mem_pot R n

private theorem mem_pot_npow {R P : α → α → Prop} : P ∈ pot R ↔ ∃ n, P = npow R (n + 1) := by
  rw [mem_pot']; simp only [ipow_succ_eq]

private theorem mem_pot_union_I {R P : α → α → Prop} : P ∈ pot R ∪ ι I ↔ ∃ n, P = npow R n := by
  constructor
  · rintro (h | h)
    · obtain ⟨n, rfl⟩ := mem_pot_npow.1 h
      exact ⟨n + 1, rfl⟩
    · exact ⟨0, h⟩
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inr rfl
    | succ n => exact Or.inl (npow_mem_pot R n)

private theorem npow_shift (R : α → β → Prop) (S : β → α → Prop) (n : ℕ) :
    npow (R ⨾ S) n ⨾ R = R ⨾ npow (S ⨾ R) n := by
  induction n with
  | zero => rw [npow_zero_comp, comp_npow_zero]
  | succ n ih => simp only [npow_succ', rp_assoc, ih]

private theorem npow_comm_self (R : α → α → Prop) (n : ℕ) : npow R n ⨾ R = R ⨾ npow R n := by
  rw [← npow_succ, npow_succ']

private theorem pot_comm {R P : α → α → Prop} (h : P ∈ pot R) : P ⨾ R = R ⨾ P := by
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 h
  exact npow_comm_self R _

private theorem codom_comp_sub (A : α → β → Prop) (B : β → γ → Prop) : codom (A ⨾ B) ⊆ codom B :=
  fun _ ⟨_, _, _, hb⟩ => ⟨_, hb⟩

private theorem dom_comp_sub (A : α → β → Prop) (B : β → γ → Prop) : dom (A ⨾ B) ⊆ dom A :=
  fun _ ⟨_, _, ha, _⟩ => ⟨_, ha⟩

private theorem codom_comp (P : α → β → Prop) (S : β → γ → Prop) :
    codom (P ⨾ S) = S˘ ʻʻ codom P := by
  ext z
  constructor
  · rintro ⟨x, y, hxy, hyz⟩
    exact ⟨y, ⟨x, hxy⟩, hyz⟩
  · rintro ⟨y, ⟨x, hxy⟩, hyz⟩
    exact ⟨x, y, hxy, hyz⟩

private theorem dom_comp (P : α → β → Prop) (S : β → γ → Prop) :
    dom (P ⨾ S) = P ʻʻ dom S := by
  ext x
  constructor
  · rintro ⟨z, y, hxy, hyz⟩
    exact ⟨y, ⟨z, hyz⟩, hxy⟩
  · rintro ⟨y, ⟨z, hyz⟩, hxy⟩
    exact ⟨z, y, hxy, hyz⟩

private theorem mem_prodCls_Dcnv {L : Set (α → β → Prop)} {x : β} :
    x ∈ prodCls (Dcnv ʻʻ L) ↔ ∀ P, P ∈ L → x ∈ codom P := by
  constructor
  · intro h P hP
    exact h _ ⟨P, hP, rfl⟩
  · rintro h A ⟨P, hP, hA⟩
    have e : A = codom P := hA
    subst e
    exact h P hP

private theorem mem_prodCls_D {L : Set (α → β → Prop)} {x : α} :
    x ∈ prodCls (D ʻʻ L) ↔ ∀ P, P ∈ L → x ∈ dom P := by
  constructor
  · intro h P hP
    exact h _ ⟨P, hP, rfl⟩
  · rintro h A ⟨P, hP, hA⟩
    have e : A = dom P := hA
    subst e
    exact h P hP

private theorem oneMany_of_oneOne {R : α → β → Prop} (h : R ∈ arrow one one) :
    R ∈ arrow one Cls := mem_arrow_one_Cls.2 (mem_arrow_one_one.1 h).1

private theorem manyOne_of_oneOne {R : α → β → Prop} (h : R ∈ arrow one one) :
    R ∈ arrow Cls one := mem_arrow_Cls_one.2 (mem_arrow_one_one.1 h).2

private theorem comp_comp_cnv {R : α → β → Prop} {P : γ → α → Prop}
    (hR : ∀ x y z, R x z ∧ R y z → x = y) (h : codom P ⊆ dom R) : P ⨾ R ⨾ R˘ = P := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, ⟨a, hxa, haz⟩, hzy⟩
    have : a = y := hR a y z ⟨haz, hzy⟩
    exact this ▸ hxa
  · intro hxy
    obtain ⟨z, hz⟩ := h ⟨x, hxy⟩
    exact ⟨z, ⟨y, hxy, hz⟩, hz⟩

/-- A one-one relation correlates any part of its domain with its image. -/
private theorem sm_img_cnv {R : α → β → Prop} (hR : R ∈ arrow one one) {A : Set α}
    (hA : A ⊆ dom R) : sm A (R˘ ʻʻ A) := by
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
  refine ⟨A ◁ R, ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨-, hx⟩, ⟨-, hy⟩⟩
    exact h1 x y z ⟨hx, hy⟩
  · rintro x y z ⟨⟨-, hy⟩, ⟨-, hz⟩⟩
    exact h2 x y z ⟨hy, hz⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hA hx
      exact ⟨y, hx, hy⟩
    · rintro ⟨y, hx, -⟩
      exact hx
  · ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy⟩

private theorem codom_npow_succ_sub (X : α → α → Prop) (n : ℕ) : codom (npow X (n + 1)) ⊆ codom X :=
  codom_comp_sub _ _

private theorem dom_npow_succ_sub (X : α → α → Prop) (n : ℕ) : dom (npow X (n + 1)) ⊆ dom X := by
  rw [npow_succ']; exact dom_comp_sub _ _

private theorem codom_pot_sub {X P : α → α → Prop} (h : P ∈ pot X) : codom P ⊆ codom X := by
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 h
  exact codom_npow_succ_sub X n

private theorem dom_pot_sub {X P : α → α → Prop} (h : P ∈ pot X) : dom P ⊆ dom X := by
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 h
  exact dom_npow_succ_sub X n

/-- The common part of the converse domains of the powers is unchanged by one more step. -/
private theorem pdc_shift {X : α → α → Prop} {x : α} :
    (∀ P, P ∈ pot X → x ∈ codom P) ↔ (∀ P, P ∈ pot X → x ∈ codom (P ⨾ X)) := by
  constructor
  · intro h P hP
    exact h _ (relProd_mem_pot hP)
  · intro h P hP
    have := h P hP
    rw [pot_comm hP] at this
    exact codom_comp_sub _ _ this

private theorem comm_npow {A B : α → α → Prop} (h : A ⨾ B = B ⨾ A) (n : ℕ) :
    npow A n ⨾ B = B ⨾ npow A n := by
  induction n with
  | zero => rw [npow_zero_comp, comp_npow_zero]
  | succ n ih =>
    rw [npow_succ]
    calc npow A n ⨾ A ⨾ B = npow A n ⨾ (A ⨾ B) := rp_assoc _ _ _
      _ = npow A n ⨾ (B ⨾ A) := by rw [h]
      _ = npow A n ⨾ B ⨾ A := (rp_assoc _ _ _).symm
      _ = B ⨾ npow A n ⨾ A := by rw [ih]
      _ = B ⨾ (npow A n ⨾ A) := rp_assoc _ _ _

private theorem comm_npow_npow {A B : α → α → Prop} (h : A ⨾ B = B ⨾ A) (m n : ℕ) :
    npow A m ⨾ npow B n = npow B n ⨾ npow A m :=
  comm_npow (comm_npow h.symm n).symm m

private theorem npow_relProd_comm {A B : α → α → Prop} (h : A ⨾ B = B ⨾ A) (n : ℕ) :
    npow (A ⨾ B) n = npow A n ⨾ npow B n := by
  induction n with
  | zero => exact (npow_zero_comp _ _).symm
  | succ n ih =>
    rw [npow_succ, ih, npow_succ A, npow_succ B]
    simp only [rp_assoc]
    rw [← rp_assoc (npow B n) A B, comm_npow h.symm n, rp_assoc]

private theorem comm_po {M S : α → α → Prop} (h : ∀ n, M ⨾ npow S (n + 1) = npow S (n + 1) ⨾ M) :
    M ⨾ po S = po S ⨾ M := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, hyz⟩
    obtain ⟨n, hn⟩ := po_iff_npow.1 hyz
    have : (M ⨾ npow S (n + 1)) x z := ⟨y, hxy, hn⟩
    rw [h n] at this
    obtain ⟨w, hxw, hwz⟩ := this
    exact ⟨w, po_iff_npow.2 ⟨n, hxw⟩, hwz⟩
  · rintro ⟨y, hxy, hyz⟩
    obtain ⟨n, hn⟩ := po_iff_npow.1 hxy
    have : (npow S (n + 1) ⨾ M) x z := ⟨y, hn, hyz⟩
    rw [← h n] at this
    obtain ⟨w, hxw, hwz⟩ := this
    exact ⟨w, hxw, po_iff_npow.2 ⟨n, hwz⟩⟩


private theorem npow_sandwich_zero (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop) :
    npow P 0 ⨾ R ⨾ npow Q 0 = R := by
  rw [npow_zero_comp, comp_npow_zero]

private theorem npow_sandwich_succ (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop)
    (n : ℕ) : npow P (n + 1) ⨾ R ⨾ npow Q (n + 1) = P ⨾ (npow P n ⨾ R ⨾ npow Q n) ⨾ Q := by
  rw [npow_succ' P n, npow_succ Q n]
  simp only [rp_assoc]

/-- `(P∗Q)'R` consists of the relations `P^n | R | Q^n`. -/
private theorem eqf_mem {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    M ∈ refs (anc (P ∥ Q)) R ↔ ∃ n, M = npow P n ⨾ R ⨾ npow Q n := by
  show anc (P ∥ Q) M R ↔ _
  rw [anc_rtg_of_total (fun N => ⟨P ⨾ (N ⨾ Q), (dpar_iff _ _ _ _).2 rfl⟩)]
  constructor
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ⟨0, (npow_sandwich_zero P Q R).symm⟩
    | head hac _ ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [(dpar_iff _ _ _ _).1 hac, hn, npow_sandwich_succ]
      exact (rp_assoc _ _ _).symm
  · rintro ⟨n, rfl⟩
    induction n with
    | zero =>
      simp only [npow_sandwich_zero]
      exact ReflTransGen.refl
    | succ n ih =>
      refine ReflTransGen.head ((dpar_iff _ _ _ _).2 ?_) ih
      rw [npow_sandwich_succ]
      exact rp_assoc _ _ _

private theorem npow_mem_eqf (P : α → α → Prop) (Q : β → β → Prop) (R : α → β → Prop) (n : ℕ) :
    npow P n ⨾ R ⨾ npow Q n ∈ refs (anc (P ∥ Q)) R := eqf_mem.2 ⟨n, rfl⟩

private theorem npow_fwd {Q : α → α → Prop} (h : codom Q ⊆ dom Q) :
    ∀ n y, y ∈ dom Q → ∃ z, npow Q n y z := by
  intro n
  induction n with
  | zero => exact fun y _ => ⟨y, rfl⟩
  | succ n ih =>
    rintro y ⟨y1, hy1⟩
    obtain ⟨z, hz⟩ := ih y1 (h ⟨y, hy1⟩)
    exact ⟨z, npow_succ_iff.2 ⟨y1, hy1, hz⟩⟩

private theorem npow_bwd {P : α → α → Prop} (h : dom P ⊆ codom P) :
    ∀ n x, x ∈ codom P → ∃ w, npow P n w x := by
  intro n
  induction n with
  | zero => exact fun x _ => ⟨x, rfl⟩
  | succ n ih =>
    rintro x ⟨v, hv⟩
    obtain ⟨w, hw⟩ := ih v (h ⟨x, hv⟩)
    exact ⟨w, v, hw, hv⟩

private theorem ipow_of_npow_right {P : α → α → Prop} {n : ℕ} {w x : α} (h : npow P n w x)
    (hx : x ∈ fld P) : ipow P n w x := by
  cases n with
  | zero =>
    have e : w = x := h
    subst e
    exact ipow_apply.2 ⟨hx, rfl⟩
  | succ n => exact ipow_apply.2 ⟨(fld_of_npow_succ h).1, h⟩

private theorem dom_npow_comp_sub {P : α → α → Prop} {X : α → β → Prop} {B : Set α}
    (hX : dom X ⊆ B) (hP : dom P ⊆ B) (n : ℕ) : dom (npow P n ⨾ X) ⊆ B := by
  cases n with
  | zero => rw [npow_zero_comp]; exact hX
  | succ n => exact (dom_comp_sub _ _).trans ((dom_npow_succ_sub P n).trans hP)

private theorem codom_comp_npow_sub {Q : β → β → Prop} {X : α → β → Prop} {B : Set β}
    (hX : codom X ⊆ B) (hQ : codom Q ⊆ B) (n : ℕ) : codom (X ⨾ npow Q n) ⊆ B := by
  cases n with
  | zero => rw [comp_npow_zero]; exact hX
  | succ n => exact (codom_comp_sub _ _).trans ((codom_npow_succ_sub Q n).trans hQ)

private theorem comp_ipow_eq {Q : β → β → Prop} {X : α → β → Prop} (h : codom X ⊆ fld Q)
    (n : ℕ) : X ⨾ ipow Q n = X ⨾ npow Q n := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨y, hxy, (ipow_apply.1 hyz).2⟩
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨y, hxy, ipow_apply.2 ⟨h ⟨x, hxy⟩, hyz⟩⟩

private theorem ipow_comp_eq {P : α → α → Prop} {X : α → β → Prop} (h : dom X ⊆ fld P)
    (n : ℕ) : ipow P n ⨾ X = npow P n ⨾ X := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨y, (ipow_apply.1 hxy).2, hyz⟩
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨y, ipow_of_npow_right hxy (h ⟨z, hyz⟩), hyz⟩

private theorem dom_sub_fld (R : α → α → Prop) : dom R ⊆ fld R := fun _ ⟨y, h⟩ => ⟨y, Or.inl h⟩

private theorem codom_sub_fld (R : α → α → Prop) : codom R ⊆ fld R :=
  fun _ ⟨y, h⟩ => ⟨y, Or.inr h⟩

private theorem fld_sub_codom {R : α → α → Prop} (h : dom R ⊆ codom R) : fld R ⊆ codom R := by
  rintro x ⟨y, hxy | hyx⟩
  · exact h ⟨y, hxy⟩
  · exact ⟨y, hyx⟩

private theorem fld_sub_dom {R : α → α → Prop} (h : codom R ⊆ dom R) : fld R ⊆ dom R := by
  rintro x ⟨y, hxy | hyx⟩
  · exact ⟨y, hxy⟩
  · exact h ⟨y, hyx⟩

private theorem beg_dom {Q : α → α → Prop} {b : α} (h : Beg b Q) : b ∈ dom Q := h.1

private theorem beg_not_codom {Q : α → α → Prop} {b : α} (h : Beg b Q) : b ∉ codom Q := h.2

private theorem end_codom {P : α → α → Prop} {e : α} (h : Beg e P˘) : e ∈ codom P := by
  obtain ⟨⟨y, hy⟩, -⟩ := h
  exact ⟨y, hy⟩

private theorem end_not_dom {P : α → α → Prop} {e : α} (h : Beg e P˘) : e ∉ dom P := by
  obtain ⟨-, h2⟩ := h
  rintro ⟨y, hy⟩
  exact h2 ⟨y, hy⟩

/-- Under a one-many relation, the number of steps from a beginning is unique. -/
private theorem beg_npow_unique {Q : α → α → Prop} (hQ : ∀ x y z, Q x z ∧ Q y z → x = y) :
    ∀ n m b b' y, Beg b Q → Beg b' Q → npow Q n b y → npow Q m b' y → n = m := by
  intro n
  induction n with
  | zero =>
    intro m b b' y hb hb' h h'
    have e : b = y := h
    subst e
    cases m with
    | zero => rfl
    | succ m =>
      obtain ⟨c, -, hc⟩ := h'
      exact absurd ⟨c, hc⟩ (beg_not_codom hb)
  | succ n ih =>
    intro m b b' y hb hb' h h'
    cases m with
    | zero =>
      have e : b' = y := h'
      subst e
      obtain ⟨c, -, hc⟩ := h
      exact absurd ⟨c, hc⟩ (beg_not_codom hb')
    | succ m =>
      obtain ⟨c, hc, hcy⟩ := h
      obtain ⟨c', hc', hcy'⟩ := h'
      have e : c = c' := hQ c c' y ⟨hcy, hcy'⟩
      subst e
      rw [ih m b b' c hb hb' hc hc']

/-- Under a many-one relation, the number of steps to an end is unique. -/
private theorem end_npow_unique {P : α → α → Prop} (hP : ∀ x y z, P x y ∧ P x z → y = z) :
    ∀ n m x e e', Beg e P˘ → Beg e' P˘ → npow P n x e → npow P m x e' → n = m := by
  intro n
  induction n with
  | zero =>
    intro m x e e' he he' h h'
    have h0 : x = e := h
    subst h0
    cases m with
    | zero => rfl
    | succ m =>
      obtain ⟨a, hxa, -⟩ := npow_succ_iff.1 h'
      exact absurd ⟨a, hxa⟩ (end_not_dom he)
  | succ n ih =>
    intro m x e e' he he' h h'
    cases m with
    | zero =>
      have h0 : x = e' := h'
      subst h0
      obtain ⟨a, hxa, -⟩ := npow_succ_iff.1 h
      exact absurd ⟨a, hxa⟩ (end_not_dom he')
    | succ m =>
      obtain ⟨a, hxa, ha⟩ := npow_succ_iff.1 h
      obtain ⟨a', hxa', ha'⟩ := npow_succ_iff.1 h'
      have e0 : a = a' := hP x a a' ⟨hxa, hxa'⟩
      subst e0
      rw [ih m a e e' he he' ha ha']

/-- PM's ✱93·32 (for any member of `Potid'Q`): `min⃗_Q'ᗡ'T = T̆''B⃗'Q` when `Q ∈ 1 → Cls`. -/
private theorem minP_codom_ipow {Q : α → α → Prop} (hQ : ∀ x y z, Q x z ∧ Q y z → x = y)
    (n : ℕ) : refs (minP Q) (codom (ipow Q n)) = (ipow Q n)˘ ʻʻ refs Beg Q := by
  ext y
  constructor
  · rintro ⟨⟨⟨w, hwy⟩, hyf⟩, hmin⟩
    obtain ⟨hwf, hw⟩ := ipow_apply.1 hwy
    refine ⟨w, ?_, hwy⟩
    cases n with
    | zero =>
      have e : w = y := hw
      subst e
      refine ⟨?_, ?_⟩
      · rcases hwf with ⟨z, hz | hz⟩
        · exact ⟨z, hz⟩
        · exact absurd ⟨z, ⟨z, ipow_zero_apply.2 ⟨rfl, ⟨w, Or.inl hz⟩⟩⟩, hz⟩ hmin
      · rintro ⟨z, hz⟩
        exact hmin ⟨z, ⟨z, ipow_zero_apply.2 ⟨rfl, ⟨w, Or.inl hz⟩⟩⟩, hz⟩
    | succ n =>
      obtain ⟨a, hwa, -⟩ := npow_succ_iff.1 hw
      refine ⟨⟨a, hwa⟩, ?_⟩
      rintro ⟨v, hvw⟩
      obtain ⟨z, hwz, hzy⟩ := hw
      apply hmin
      refine ⟨z, ⟨v, ?_⟩, hzy⟩
      rw [ipow_succ_eq]
      exact npow_succ_iff.2 ⟨w, hvw, hwz⟩
  · rintro ⟨b, hb, hby⟩
    obtain ⟨-, hbn⟩ := ipow_apply.1 hby
    refine ⟨⟨⟨b, hby⟩, (fld_of_ipow hby).2⟩, ?_⟩
    rintro ⟨z, ⟨w, hwz⟩, hzy⟩
    obtain ⟨-, hwn⟩ := ipow_apply.1 hwz
    have h1 : npow Q (n + 1) w y := ⟨z, hwn, hzy⟩
    obtain ⟨c, hwc, hcy⟩ := npow_succ_iff.1 h1
    have : c = b := npow_oneMany hQ n c b y ⟨hcy, hbn⟩
    subst this
    exact beg_not_codom hb ⟨w, hwc⟩

private theorem mem_gen_iff {Q : α → α → Prop} {A : Set α} :
    A ∈ gen Q ↔ ∃ T, T ∈ potid Q ∧ A = refs (minP Q) (codom T) := by
  constructor
  · rintro ⟨B, ⟨T, hT, hB⟩, hA⟩
    have hB' : B = codom T := hB
    have hA' : A = refs (minP Q) B := hA
    subst hB'
    exact ⟨T, hT, hA'⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨codom T, ⟨T, hT, rfl⟩, rfl⟩

private theorem mem_gen_oneMany {Q : α → α → Prop} (hQ : ∀ x y z, Q x z ∧ Q y z → x = y)
    {A : Set α} : A ∈ gen Q ↔ ∃ n, A = (ipow Q n)˘ ʻʻ refs Beg Q := by
  rw [mem_gen_iff]
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨n, rfl⟩ := mem_potid'.1 hT
    exact ⟨n, minP_codom_ipow hQ n⟩
  · rintro ⟨n, rfl⟩
    exact ⟨ipow Q n, ipow_mem_potid Q n, (minP_codom_ipow hQ n).symm⟩

private theorem sumCls_gen_sub_fld (Q : α → α → Prop) : sumCls (gen Q) ⊆ fld Q := by
  rintro y ⟨A, hA, hy⟩
  obtain ⟨T, -, rfl⟩ := mem_gen_iff.1 hA
  exact hy.1.2

private theorem mem_sumCls_gen_oneMany {Q : α → α → Prop} (hQ : ∀ x y z, Q x z ∧ Q y z → x = y)
    {y : α} : y ∈ sumCls (gen Q) ↔ ∃ b n, Beg b Q ∧ npow Q n b y := by
  constructor
  · rintro ⟨A, hA, hy⟩
    obtain ⟨n, rfl⟩ := (mem_gen_oneMany hQ).1 hA
    obtain ⟨b, hb, hby⟩ := hy
    exact ⟨b, n, hb, (ipow_apply.1 hby).2⟩
  · rintro ⟨b, n, hb, hby⟩
    exact ⟨_, (mem_gen_oneMany hQ).2 ⟨n, rfl⟩, b, hb, ipow_apply.2 ⟨dom_sub_fld Q (beg_dom hb), hby⟩⟩

/-- Every member of the field is in some generation or in every converse domain of a power. -/
private theorem fld_sub_gen_pdc (P : α → α → Prop) :
    fld P ⊆ sumCls (gen P) ∪ prodCls (Dcnv ʻʻ pot P) := by
  intro x hx
  by_cases hg : x ∈ sumCls (gen P)
  · exact Or.inl hg
  · right
    have key : ∀ n, x ∈ codom (ipow P n) := by
      intro n
      induction n with
      | zero => exact ⟨x, ipow_zero_apply.2 ⟨rfl, hx⟩⟩
      | succ n ih =>
        by_contra hn
        apply hg
        refine ⟨_, mem_gen_iff.2 ⟨ipow P n, ipow_mem_potid P n, rfl⟩, ⟨ih, hx⟩, ?_⟩
        rintro ⟨z, hz, hzx⟩
        apply hn
        obtain ⟨w, hw⟩ := hz
        rw [ipow_succ]
        exact ⟨w, z, hw, hzx⟩
    rw [mem_prodCls_Dcnv]
    intro T hT
    obtain ⟨n, rfl⟩ := mem_pot'.1 hT
    exact key (n + 1)

private theorem sumCls_gen_empty {P : α → α → Prop} (h : dom P ⊆ codom P) :
    sumCls (gen P) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, hA, hx⟩
  obtain ⟨T, hT, rfl⟩ := mem_gen_iff.1 hA
  obtain ⟨n, rfl⟩ := mem_potid'.1 hT
  obtain ⟨⟨hxc, hxf⟩, hmin⟩ := hx
  obtain ⟨y, hyx⟩ := fld_sub_codom h hxf
  apply hmin
  refine ⟨y, ?_, hyx⟩
  cases n with
  | zero => exact ⟨y, ipow_zero_apply.2 ⟨rfl, ⟨x, Or.inl hyx⟩⟩⟩
  | succ n =>
    obtain ⟨w, hw⟩ := npow_bwd h (n + 1) y (h ⟨x, hyx⟩)
    rw [ipow_succ_eq]
    exact ⟨w, hw⟩

private theorem cnv_mem_one_one {R : α → β → Prop} (h : R ∈ arrow one one) : R˘ ∈ arrow one one := by
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 h
  exact mem_arrow_one_one.2 ⟨fun x y z hh => h2 z x y hh, fun x y z hh => h1 y z x hh⟩

private theorem relProd_mem_one_one {R : α → β → Prop} {S : β → γ → Prop} (hR : R ∈ arrow one one)
    (hS : S ∈ arrow one one) : R ⨾ S ∈ arrow one one := by
  obtain ⟨r1, r2⟩ := mem_arrow_one_one.1 hR
  obtain ⟨s1, s2⟩ := mem_arrow_one_one.1 hS
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro x y z ⟨⟨a, hxa, haz⟩, ⟨b, hyb, hbz⟩⟩
    have e : a = b := s1 a b z ⟨haz, hbz⟩
    subst e
    exact r1 x y a ⟨hxa, hyb⟩
  · rintro x y z ⟨⟨a, hxa, hay⟩, ⟨b, hxb, hbz⟩⟩
    have e : a = b := r2 x a b ⟨hxa, hxb⟩
    subst e
    exact s2 a y z ⟨hay, hbz⟩

private theorem npow_cnv_iff {P : α → α → Prop} {n : ℕ} {a b : α} :
    npow P˘ n a b ↔ npow P n b a := by
  induction n generalizing a b with
  | zero => exact eq_comm
  | succ n ih =>
    rw [npow_succ' P n]
    constructor
    · rintro ⟨c, hac, hcb⟩
      exact ⟨c, hcb, ih.1 hac⟩
    · rintro ⟨c, hbc, hca⟩
      exact ⟨c, ih.2 hca, hbc⟩

private theorem ipow_mem_one_Cls {P : α → α → Prop} (hP : ∀ x y z, P x z ∧ P y z → x = y)
    (n : ℕ) : ∀ x y z, ipow P n x z ∧ ipow P n y z → x = y := by
  intro x y z ⟨hx, hy⟩
  exact npow_oneMany hP n x y z ⟨(ipow_apply.1 hx).2, (ipow_apply.1 hy).2⟩

private theorem ipow_mem_Cls_one {P : α → α → Prop} (hP : ∀ x y z, P x y ∧ P x z → y = z)
    (n : ℕ) : ∀ x y z, ipow P n x y ∧ ipow P n x z → y = z := by
  intro x y z ⟨hy, hz⟩
  exact npow_manyOne hP n x y z ⟨(ipow_apply.1 hy).2, (ipow_apply.1 hz).2⟩

/-- `S̆ | S | Y = Y` for `S ∈ Potid'P`, `P ∈ Cls → 1`, `D'P ⊂ ᗡ'P`, `D'Y ⊂ C'P`. -/
private theorem cnv_potid_cancel {P : α → α → Prop} (hP : ∀ x y z, P x y ∧ P x z → y = z)
    (hd : dom P ⊆ codom P) {S : α → α → Prop} (hS : S ∈ potid P) {Y : α → β → Prop}
    (hY : dom Y ⊆ fld P) : S˘ ⨾ (S ⨾ Y) = Y := by
  obtain ⟨n, rfl⟩ := mem_potid'.1 hS
  funext x z
  apply propext
  constructor
  · rintro ⟨a, hax, b, hab, hbz⟩
    have e : x = b := ipow_mem_Cls_one hP n a x b ⟨hax, hab⟩
    subst e
    exact hbz
  · intro hxz
    have hx : x ∈ fld P := hY ⟨z, hxz⟩
    obtain ⟨a, ha⟩ := npow_bwd hd n x (fld_sub_codom hd hx)
    have ha' := ipow_of_npow_right ha hx
    exact ⟨a, ha', x, ha', hxz⟩

/-- `Y | T | T̆ = Y` for `T ∈ Potid'Q`, `Q ∈ 1 → Cls`, `ᗡ'Q ⊂ D'Q`, `ᗡ'Y ⊂ C'Q`. -/
private theorem potid_cnv_cancel {Q : β → β → Prop} (hQ : ∀ x y z, Q x z ∧ Q y z → x = y)
    (hc : codom Q ⊆ dom Q) {T : β → β → Prop} (hT : T ∈ potid Q) {Y : α → β → Prop}
    (hY : codom Y ⊆ fld Q) : Y ⨾ T ⨾ T˘ = Y := by
  obtain ⟨n, rfl⟩ := mem_potid'.1 hT
  funext x z
  apply propext
  constructor
  · rintro ⟨a, ⟨b, hxb, hba⟩, haz⟩
    have e : b = z := ipow_mem_one_Cls hQ n b z a ⟨hba, haz⟩
    subst e
    exact hxb
  · intro hxz
    have hz : z ∈ fld Q := hY ⟨x, hxz⟩
    obtain ⟨a, ha⟩ := npow_fwd hc n z (fld_sub_dom hc hz)
    have ha' : ipow Q n z a := ipow_apply.2 ⟨hz, ha⟩
    exact ⟨a, ⟨z, hxz, ha'⟩, ha'⟩


private theorem po_iff_anc_comp {R : α → α → Prop} {x y : α} :
    po R x y ↔ ∃ t, anc R x t ∧ R t y := by
  rw [po_eq_anc_comp]
  exact Iff.rfl

private theorem anc_left_fld {R : α → α → Prop} {x y : α} (h : anc R x y) : x ∈ fld R := h.1

private theorem po_left_dom {R : α → α → Prop} {x y : α} (h : po R x y) : x ∈ dom R := by
  rw [po_eq_comp_anc] at h
  obtain ⟨a, hxa, -⟩ := h
  exact ⟨a, hxa⟩

private theorem fld_po (R : α → α → Prop) : fld (po R) = fld R := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact dom_sub_fld R (po_left_dom h)
    · exact anc_fld_right (po_sub_anc h)
  · rintro ⟨y, h | h⟩
    · exact ⟨y, Or.inl (R_sub_po h)⟩
    · exact ⟨y, Or.inr (R_sub_po h)⟩

/-- Forward comparability under a many-one relation. -/
private theorem npow_manyOne_cmp {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z)
    {n m : ℕ} {x y z : α} (h1 : npow R n x y) (h2 : npow R m x z) :
    (∃ k, npow R k y z) ∨ (∃ k, npow R k z y) := by
  rcases le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [npow_add] at h2
    obtain ⟨t, hxt, htz⟩ := h2
    have : t = y := npow_manyOne hR n x t y ⟨hxt, h1⟩
    subst this
    exact Or.inl ⟨k, htz⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [npow_add] at h1
    obtain ⟨t, hxt, hty⟩ := h1
    have : t = z := npow_manyOne hR m x t z ⟨hxt, h2⟩
    subst this
    exact Or.inr ⟨k, hty⟩

/-- Backward comparability under a one-many relation. -/
private theorem npow_oneMany_cmp {R : α → α → Prop} (hR : ∀ x y z, R x z ∧ R y z → x = y)
    {n m : ℕ} {x y z : α} (h1 : npow R n x y) (h2 : npow R m z y) :
    (∃ k, npow R k x z) ∨ (∃ k, npow R k z x) := by
  rcases le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm, npow_add] at h2
    obtain ⟨t, hzt, hty⟩ := h2
    have : t = x := npow_oneMany hR n t x y ⟨hty, h1⟩
    subst this
    exact Or.inr ⟨k, hzt⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm, npow_add] at h1
    obtain ⟨t, hxt, hty⟩ := h1
    have : t = z := npow_oneMany hR m t z y ⟨hty, h2⟩
    subst this
    exact Or.inl ⟨k, hxt⟩

private theorem anc_of_npow {R : α → α → Prop} {n : ℕ} {x y : α} (hx : x ∈ fld R)
    (h : npow R n x y) : anc R x y := anc_iff_npow.2 ⟨hx, n, h⟩

private theorem po_of_npow_succ {R : α → α → Prop} {n : ℕ} {x y : α} (h : npow R (n + 1) x y) :
    po R x y := po_iff_npow.2 ⟨n, h⟩

private theorem npow_succ_of_po {R : α → α → Prop} {x y : α} (h : po R x y) :
    ∃ n, npow R (n + 1) x y := po_iff_npow.1 h

private theorem anc_manyOne_cmp {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z)
    {x y z : α} (h1 : anc R x y) (h2 : anc R x z) : anc R y z ∨ anc R z y := by
  obtain ⟨-, n, hn⟩ := anc_iff_npow.1 h1
  obtain ⟨-, m, hm⟩ := anc_iff_npow.1 h2
  rcases npow_manyOne_cmp hR hn hm with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact Or.inl (anc_of_npow (anc_fld_right h1) hk)
  · exact Or.inr (anc_of_npow (anc_fld_right h2) hk)

private theorem anc_oneMany_cmp {R : α → α → Prop} (hR : ∀ x y z, R x z ∧ R y z → x = y)
    {x y z : α} (h1 : anc R x y) (h2 : anc R z y) : anc R x z ∨ anc R z x := by
  obtain ⟨hx, n, hn⟩ := anc_iff_npow.1 h1
  obtain ⟨hz, m, hm⟩ := anc_iff_npow.1 h2
  rcases npow_oneMany_cmp hR hn hm with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact Or.inl (anc_of_npow hx hk)
  · exact Or.inr (anc_of_npow hz hk)

private theorem npow_mul_self {R : α → α → Prop} {p : ℕ} {z : α} (h : npow R p z z) :
    ∀ k, npow R (p * k) z z := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, npow_add]
    exact ⟨z, ih, h⟩

/-- PM's ✱96·34: under a many-one relation, whatever follows a cyclic term is cyclic. -/
private theorem po_cyc_succ {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z)
    {z w : α} (hz : po R z z) (hzw : po R z w) : po R w w := by
  obtain ⟨p, hp⟩ := npow_succ_of_po hz
  obtain ⟨n, hn⟩ := npow_succ_of_po hzw
  have hN := npow_mul_self hp (n + 1)
  have hle : n + 1 ≤ (p + 1) * (n + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos p)
  obtain ⟨M, hM⟩ := Nat.exists_eq_add_of_le hle
  rw [hM, npow_add] at hN
  obtain ⟨t, hzt, htz⟩ := hN
  have : t = w := npow_manyOne hR (n + 1) z t w ⟨hzt, hn⟩
  subst this
  have hk : npow R (M + (n + 1)) t t := by
    rw [npow_add]
    exact ⟨z, htz, hn⟩
  exact po_of_npow_succ (n := M + n) hk

private theorem anc_cyc {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z)
    {z w : α} (hz : po R z z) (hzw : anc R z w) : po R w w := by
  rcases anc_iff_po.1 hzw with ⟨rfl, -⟩ | h
  · exact hz
  · exact po_cyc_succ hR hz h

/-- The core of ✱96·403·41: a cyclic `y` and a later `z` with a common successor coincide. -/
private theorem cyc_common_succ {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z)
    {p b : ℕ} {y z w : α} (hy : npow R (p + 1) y y) (hb : npow R b y z) (hzw : R z w)
    (hyw : R y w) : z = y := by
  obtain ⟨w', hyw', hw'y⟩ := npow_succ_iff.1 hy
  have : w' = w := hR y w' w ⟨hyw', hyw⟩
  subst this
  have h1 : npow R (b + (1 + p)) y y := by
    rw [npow_add, npow_add]
    exact ⟨z, hb, w', ⟨z, rfl, hzw⟩, hw'y⟩
  have h2 : npow R ((p + 1) + b) y z := by
    rw [npow_add]
    exact ⟨y, hy, hb⟩
  rw [show b + (1 + p) = (p + 1) + b by omega] at h1
  exact npow_manyOne hR _ y z y ⟨h2, h1⟩

/-- Under a many-one relation, the successor of `y` (if `y R w`) is `w`. -/
private theorem desc_cnv_of {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z)
    {y w : α} (h : R y w) (ψ : α → Prop) : Desc R˘ y ψ ↔ ψ w :=
  TheIs_iff_of_unique fun u => ⟨fun hu => hR y u w ⟨hu, h⟩, fun e => e ▸ h⟩

private theorem desc_cnv_exists {R : α → α → Prop} {y : α} {ψ : α → Prop} (h : Desc R˘ y ψ) :
    ∃ w, R y w ∧ ψ w := by
  obtain ⟨w, hw, hψ⟩ := h
  exact ⟨w, (hw w).2 rfl, hψ⟩

private theorem maxP_apply' (R : α → α → Prop) (u : α) (A : Set α) :
    maxP R u A ↔ (u ∈ A ∧ u ∈ fld R) ∧ ¬ ∃ v, v ∈ A ∧ R u v := by
  show minP R˘ u A ↔ _
  rw [minP_apply, fld_cnv]
  exact Iff.rfl

private theorem mem_IR {R : α → α → Prop} {x z : α} : z ∈ IR R x ↔ anc R x z ∧ po R z z :=
  Iff.rfl

private theorem mem_JR {R : α → α → Prop} {x z : α} : z ∈ JR R x ↔ anc R x z ∧ ¬ po R z z := by
  show (anc R x z ∧ ¬ (anc R x z ∧ po R z z)) ↔ _
  tauto

private theorem rtg_mono {r p : α → α → Prop} {x y : α} (hxy : ReflTransGen r x y)
    (h : ∀ a b, r a b → p a b) : ReflTransGen p x y := by
  induction hxy with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)


/-!
## [✱94] On powers of relative products

*(Vol. 1, p. 617)*

> *Summary of* *94.
>
> In this number we shall be chiefly concerned with propositions connecting powers of \(R \mid S\) with powers of \(S \mid R\). If \(P\) is a power of \(R \mid S\), \(S \mid P \mid R\) will be a power of \(S\mid R\). If \(P\) is a power of \(R \mid S\), it is a product of the form \[ (R \mid S) \mid (R \mid S) \mid \ldots \mid (R \mid S). \]
>
> If we transfer the initial \(R\) to the end, we get a power of \(S \mid R\). Thus there is a power of \(S \mid R\), say \(T\), such that \[ P \mid R = R \mid T\text{.} \]
>
> If \(R \in 1 \rightarrow \text{Cls} . \text{ᗡ}ʻ(R \mid S) \subset\text{D}ʻR\), we find \[ R \mid (S \mid R) \mid (S \mid R) \mid \ldots \mid (S \mid R) \mid \breve{R} = (R \mid S) \mid (R \mid S) \ldots (R \mid S) \] by rearranging and observing that \(R \mid \breve{R} = I \upharpoonright \text{D}ʻR\). Thus \[ R \in 1 \rightarrow \text{Cls} . \text{ᗡ}ʻ(R \mid S) \subset \text{D}ʻR . P \in \text{Pot}ʻR \mid S .\supset. (\exists T) . T \in \text{Pot}ʻS \mid R . P = R \mid T \mid \breve{R}\text{.} \]
>
> Expressions of the form \(R \mid T \mid \breve{R}\) are constantly needed. They will be specially dealt with in *150, and will occur constantly in the sequel.
>
> …

**Lean reading.** `Pot'(R|S)` is `pot (R ⨾ S)` with `R : α → β → Prop` and
`S : β → α → Prop`, so that `R|S` and `S|R` are homogeneous on different types; `|R''κ` and
`R|''κ` are the images `relProdR R ʻʻ K` and `relProdL R ʻʻ K`, `S‖R` is `S ∥ R`, and `ι'I` is the
unit class of the identity `I`. `p'ᗡ''Pot'(R|S)` is `prodCls (Dcnv ʻʻ pot (R ⨾ S))` and `S̆'''κ` is
`S˘ ʻʻʻ K`; `R_po`, `R_*` are `po R`, `anc R`, and `sm` is `sm`. The four-term chain ✱94·4 is the
conjunction of its three links. The proofs write a power of `X` as an iterated relative product
(`npow X n`) and use `(R|S)^n | R = R | (S|R)^n`.

**Status.** proved (all propositions).
-/

/-- ✱94·12. \(\vdash:P\in \text{Pot}ʻ(R\mid S).\supset.(\exists T).T\in \text{Pot}ʻ(S\mid R).P\mid R=R\mid T\) -/
theorem pm94_12 {R : α → β → Prop} {S : β → α → Prop} {P : α → α → Prop} :
    P ∈ pot (R ⨾ S) → ∃ T, T ∈ pot (S ⨾ R) ∧ P ⨾ R = R ⨾ T := by
  intro h
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 h
  exact ⟨_, npow_mem_pot _ n, npow_shift R S (n + 1)⟩

/-- ✱94·13. \[\begin{align}&\vdash:T\in \text{Pot}ʻ(S\mid R).\supset.(\exists P).P\in \text{Pot}ʻ(R\mid S).P\mid R=R\mid T\\ &[\text{Proof as in *94·12}]\end{align}\] -/
theorem pm94_13 {R : α → β → Prop} {S : β → α → Prop} {T : β → β → Prop} :
    T ∈ pot (S ⨾ R) → ∃ P, P ∈ pot (R ⨾ S) ∧ P ⨾ R = R ⨾ T := by
  intro h
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 h
  exact ⟨_, npow_mem_pot _ n, npow_shift R S (n + 1)⟩

/-- ✱94·14. \(\vdash.\mid Rʻʻ\text{Pot}ʻ(R\mid S)=R\mid ʻʻ\text{Pot}ʻ(S\mid R)\) -/
theorem pm94_14 {R : α → β → Prop} {S : β → α → Prop} :
    relProdR R ʻʻ pot (R ⨾ S) = relProdL R ʻʻ pot (S ⨾ R) := by
  ext U
  constructor
  · rintro ⟨P, hP, hU⟩
    have hU' : U = P ⨾ R := hU
    obtain ⟨T, hT, e⟩ := pm94_12 hP
    exact ⟨T, hT, hU'.trans e⟩
  · rintro ⟨T, hT, hU⟩
    have hU' : U = R ⨾ T := hU
    obtain ⟨P, hP, e⟩ := pm94_13 hT
    exact ⟨P, hP, hU'.trans e.symm⟩

private theorem pm94_2_aux (R : α → β → Prop) (S : β → α → Prop) (n : ℕ) :
    S ⨾ npow (R ⨾ S) n ⨾ R = npow (S ⨾ R) (n + 1) := by
  rw [rp_assoc, npow_shift, ← rp_assoc, npow_succ']

/-- ✱94·2. \(\vdash:P\in \text{Pot}ʻ(R\mid S)\cup \iotaʻI.\supset.S\mid P\mid R\in \text{Pot}ʻ(S\mid R)\) -/
theorem pm94_2 {R : α → β → Prop} {S : β → α → Prop} {P : α → α → Prop} :
    P ∈ pot (R ⨾ S) ∪ ι I → S ⨾ P ⨾ R ∈ pot (S ⨾ R) := by
  intro h
  obtain ⟨n, rfl⟩ := mem_pot_union_I.1 h
  rw [pm94_2_aux]
  exact npow_mem_pot _ n

/-- ✱94·201. \(\vdash:T\in \text{Pot}ʻ(S\mid R).\supset.(\exists P).P\in \text{Pot}ʻ(R\mid S)\cup \iotaʻI.T=S\mid P\mid R\) -/
theorem pm94_201 {R : α → β → Prop} {S : β → α → Prop} {T : β → β → Prop} :
    T ∈ pot (S ⨾ R) → ∃ P, P ∈ pot (R ⨾ S) ∪ ι I ∧ T = S ⨾ P ⨾ R := by
  intro h
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 h
  exact ⟨npow (R ⨾ S) n, mem_pot_union_I.2 ⟨n, rfl⟩, (pm94_2_aux R S n).symm⟩

/-- ✱94·21. \(\vdash.\text{Pot}ʻ(S\mid R)=(S\Arrowvert R)ʻʻ\{\text{Pot}ʻ(R\mid S)\cup \iotaʻI\}\) -/
theorem pm94_21 {R : α → β → Prop} {S : β → α → Prop} :
    pot (S ⨾ R) = (S ∥ R) ʻʻ (pot (R ⨾ S) ∪ ι I) := by
  ext T
  constructor
  · intro h
    obtain ⟨P, hP, e⟩ := pm94_201 h
    exact ⟨P, hP, (dpar_iff _ _ _ _).2 (e.trans (rp_assoc _ _ _))⟩
  · rintro ⟨P, hP, hT⟩
    rw [(dpar_iff _ _ _ _).1 hT, ← rp_assoc]
    exact pm94_2 hP

/-- ✱94·22. \[\begin{align}\vdash\colon\ldotp \text{ᗡ}ʻR\subset \text{D}ʻS.\lor.\text{D}ʻS\subset \text{ᗡ}ʻR&:\supset.\\ &\text{Pot}ʻ(S\mid R)=(S\Arrowvert R)ʻʻ\text{Potid}ʻ(R\mid S)\end{align}\] -/
theorem pm94_22 {R : α → β → Prop} {S : β → α → Prop} :
    codom R ⊆ dom S ∨ dom S ⊆ codom R → pot (S ⨾ R) = (S ∥ R) ʻʻ potid (R ⨾ S) := by
  intro hyp
  have key : S ⨾ ((I ↾ fld (R ⨾ S)) ⨾ R) = S ⨾ R := by
    funext x z
    apply propext
    constructor
    · rintro ⟨y, hxy, a, ⟨hya, -⟩, haz⟩
      have e : y = a := hya
      subst e
      exact ⟨y, hxy, haz⟩
    · rintro ⟨y, hxy, hyz⟩
      refine ⟨y, hxy, y, ⟨rfl, ?_⟩, hyz⟩
      rcases hyp with h | h
      · obtain ⟨w, hw⟩ := h ⟨y, hyz⟩
        exact ⟨w, Or.inl ⟨z, hyz, hw⟩⟩
      · obtain ⟨v, hv⟩ := h ⟨y, hxy⟩
        exact ⟨v, Or.inr ⟨x, hv, hxy⟩⟩
  have hn : ∀ n, S ⨾ (ipow (R ⨾ S) n ⨾ R) = npow (S ⨾ R) (n + 1) := by
    intro n
    cases n with
    | zero => rw [ipow_zero, key, npow_one]
    | succ n => rw [ipow_succ_eq, ← rp_assoc, pm94_2_aux]
  ext T
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := mem_pot_npow.1 h
    exact ⟨ipow (R ⨾ S) n, ipow_mem_potid _ n, (dpar_iff _ _ _ _).2 (hn n).symm⟩
  · rintro ⟨P, hP, hT⟩
    obtain ⟨n, rfl⟩ := mem_potid'.1 hP
    rw [(dpar_iff _ _ _ _).1 hT, hn]
    exact npow_mem_pot _ n

/-- ✱94·3. \[\begin{align}\vdash\colon\ldotp R\in 1\rightarrow &\text{Cls}.\text{ᗡ}ʻ(R\mid S)\subset \text{D}ʻR.\supset:\\ & P\in \text{Pot}ʻ(R\mid S).\equiv.(\exists T).T\in \text{Pot}ʻ(S\mid R).P=R\mid T\mid \breve{R}\end{align}\] -/
theorem pm94_3 {R : α → β → Prop} {S : β → α → Prop} {P : α → α → Prop} :
    R ∈ arrow one Cls ∧ codom (R ⨾ S) ⊆ dom R →
      (P ∈ pot (R ⨾ S) ↔ ∃ T, T ∈ pot (S ⨾ R) ∧ P = R ⨾ T ⨾ R˘) := by
  rintro ⟨hR, hc⟩
  have hR' := mem_arrow_one_Cls.1 hR
  have hc' : ∀ n, codom (npow (R ⨾ S) (n + 1)) ⊆ dom R :=
    fun n => (codom_npow_succ_sub _ n).trans hc
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := mem_pot_npow.1 h
    refine ⟨_, npow_mem_pot (S ⨾ R) n, ?_⟩
    rw [← npow_shift]
    exact (comp_comp_cnv hR' (hc' n)).symm
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨n, rfl⟩ := mem_pot_npow.1 hT
    rw [← npow_shift, comp_comp_cnv hR' (hc' n)]
    exact npow_mem_pot _ n

/-- ✱94·31. \[\begin{align}&\vdash:R\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻ(R\mid S)\subset \text{D}ʻR.\supset.\text{Pot}ʻ(R\mid S)=(R\parallel\breve{R})ʻʻ\text{Pot}ʻ(S\mid R)\\ &[\text{*94·3}]\end{align}\] -/
theorem pm94_31 {R : α → β → Prop} {S : β → α → Prop} :
    R ∈ arrow one Cls ∧ codom (R ⨾ S) ⊆ dom R → pot (R ⨾ S) = (R ∥ R˘) ʻʻ pot (S ⨾ R) := by
  intro hyp
  ext P
  rw [pm94_3 hyp]
  constructor
  · rintro ⟨T, hT, e⟩
    exact ⟨T, hT, (dpar_iff _ _ _ _).2 (e.trans (rp_assoc _ _ _))⟩
  · rintro ⟨T, hT, hP⟩
    exact ⟨T, hT, ((dpar_iff _ _ _ _).1 hP).trans (rp_assoc _ _ _).symm⟩

/-- ✱94·4. \[\begin{align}\vdash.pʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S)&=pʻ\text{ᗡ}ʻʻ\mid Sʻʻ\mid Rʻʻ\text{Pot}ʻ(R\mid S)\\ &=pʻ\breve{S}ʻʻʻ\text{ᗡ}ʻʻ\mid Rʻʻ\text{Pot}ʻ(R\mid S)\\ & =pʻ\breve{S}ʻʻʻ\breve{R}ʻʻʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S)\end{align}\] -/
theorem pm94_4 {R : α → β → Prop} {S : β → α → Prop} :
    (prodCls (Dcnv ʻʻ pot (R ⨾ S)) = prodCls (Dcnv ʻʻ relProdR S ʻʻ relProdR R ʻʻ pot (R ⨾ S)) ∧
      prodCls (Dcnv ʻʻ relProdR S ʻʻ relProdR R ʻʻ pot (R ⨾ S)) =
        prodCls (S˘ ʻʻʻ Dcnv ʻʻ relProdR R ʻʻ pot (R ⨾ S))) ∧
      prodCls (S˘ ʻʻʻ Dcnv ʻʻ relProdR R ʻʻ pot (R ⨾ S)) =
        prodCls (S˘ ʻʻʻ R˘ ʻʻʻ Dcnv ʻʻ pot (R ⨾ S)) := by
  have h0 : ∀ x, x ∈ prodCls (Dcnv ʻʻ pot (R ⨾ S)) ↔
      ∀ P, P ∈ pot (R ⨾ S) → x ∈ codom (P ⨾ R ⨾ S) := by
    intro x
    rw [mem_prodCls_Dcnv, pdc_shift]
    simp only [rp_assoc]
  have h1 : ∀ x, x ∈ prodCls (Dcnv ʻʻ relProdR S ʻʻ relProdR R ʻʻ pot (R ⨾ S)) ↔
      ∀ P, P ∈ pot (R ⨾ S) → x ∈ codom (P ⨾ R ⨾ S) := by
    intro x
    rw [mem_prodCls_Dcnv]
    constructor
    · intro h P hP
      exact h _ ⟨P ⨾ R, ⟨P, hP, rfl⟩, rfl⟩
    · rintro h U ⟨V, ⟨P, hP, hV⟩, hU⟩
      have hU' : U = V ⨾ S := hU
      have hV' : V = P ⨾ R := hV
      subst hU' hV'
      exact h P hP
  have h2 : ∀ x, x ∈ prodCls (S˘ ʻʻʻ Dcnv ʻʻ relProdR R ʻʻ pot (R ⨾ S)) ↔
      ∀ P, P ∈ pot (R ⨾ S) → x ∈ codom (P ⨾ R ⨾ S) := by
    intro x
    constructor
    · intro h P hP
      rw [codom_comp]
      exact h _ ⟨_, ⟨P ⨾ R, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩
    · rintro h A ⟨B, ⟨V, ⟨P, hP, hV⟩, hB⟩, hA⟩
      have hA' : A = S˘ ʻʻ B := hA
      have hB' : B = codom V := hB
      have hV' : V = P ⨾ R := hV
      subst hA' hB' hV'
      rw [← codom_comp]
      exact h P hP
  have h3 : ∀ x, x ∈ prodCls (S˘ ʻʻʻ R˘ ʻʻʻ Dcnv ʻʻ pot (R ⨾ S)) ↔
      ∀ P, P ∈ pot (R ⨾ S) → x ∈ codom (P ⨾ R ⨾ S) := by
    intro x
    constructor
    · intro h P hP
      rw [codom_comp, codom_comp]
      exact h _ ⟨_, ⟨_, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩
    · rintro h A ⟨B, ⟨C, ⟨P, hP, hC⟩, hB⟩, hA⟩
      have hA' : A = S˘ ʻʻ B := hA
      have hB' : B = R˘ ʻʻ C := hB
      have hC' : C = codom P := hC
      subst hA' hB' hC'
      rw [← codom_comp, ← codom_comp]
      exact h P hP
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> ext x
  · rw [h0, h1]
  · rw [h1, h2]
  · rw [h2, h3]

/-- ✱94·401. \(\vdash.pʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S)=pʻ\text{ᗡ}ʻʻR\mid ʻʻS\mid ʻʻ\text{Pot}ʻ(R\mid S)\) -/
theorem pm94_401 {R : α → β → Prop} {S : β → α → Prop} :
    prodCls (Dcnv ʻʻ pot (R ⨾ S)) = prodCls (Dcnv ʻʻ relProdL R ʻʻ relProdL S ʻʻ pot (R ⨾ S)) := by
  ext x
  rw [mem_prodCls_Dcnv, mem_prodCls_Dcnv, pdc_shift]
  constructor
  · rintro h U ⟨V, ⟨P, hP, hV⟩, hU⟩
    have hU' : U = R ⨾ V := hU
    have hV' : V = S ⨾ P := hV
    subst hU' hV'
    have := h P hP
    rw [pot_comm hP] at this
    simpa only [rp_assoc] using this
  · intro h P hP
    have := h _ ⟨S ⨾ P, ⟨P, hP, rfl⟩, rfl⟩
    rw [pot_comm hP]
    simpa only [rp_assoc] using this

/-- ✱94·402. \(\vdash.pʻ\text{ᗡ}ʻʻR\mid ʻʻ\lambda\subset pʻ\text{ᗡ}ʻʻ\lambda\) -/
theorem pm94_402 {R : α → β → Prop} {L : Set (β → γ → Prop)} :
    prodCls (Dcnv ʻʻ relProdL R ʻʻ L) ⊆ prodCls (Dcnv ʻʻ L) := by
  intro x hx
  rw [mem_prodCls_Dcnv] at hx ⊢
  intro P hP
  exact codom_comp_sub R P (hx _ ⟨P, hP, rfl⟩)

private theorem mem_pdc_relProdR {R : α → β → Prop} {X : α → α → Prop} {b : β} :
    b ∈ prodCls (Dcnv ʻʻ relProdR R ʻʻ pot X) ↔ ∀ P, P ∈ pot X → b ∈ codom (P ⨾ R) := by
  rw [mem_prodCls_Dcnv]
  constructor
  · intro h P hP
    exact h _ ⟨P, hP, rfl⟩
  · rintro h U ⟨P, hP, hU⟩
    have hU' : U = P ⨾ R := hU
    subst hU'
    exact h P hP

private theorem mem_pdc_relProdL {R : α → β → Prop} {X : β → β → Prop} {b : β} :
    b ∈ prodCls (Dcnv ʻʻ relProdL R ʻʻ pot X) ↔ ∀ P, P ∈ pot X → b ∈ codom (R ⨾ P) := by
  rw [mem_prodCls_Dcnv]
  constructor
  · intro h P hP
    exact h _ ⟨P, hP, rfl⟩
  · rintro h U ⟨P, hP, hU⟩
    have hU' : U = R ⨾ P := hU
    subst hU'
    exact h P hP

/-- ✱94·41. \[\begin{align}\vdash:S\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻ(S\mid R)&\subset \text{D}ʻS.\supset.\\ & Sʻʻpʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S)=pʻ\text{ᗡ}ʻʻ\mid Rʻʻ\text{Pot}ʻ(R\mid S)\end{align}\] -/
theorem pm94_41 {R : α → β → Prop} {S : β → α → Prop} :
    S ∈ arrow one Cls ∧ codom (S ⨾ R) ⊆ dom S →
      S ʻʻ prodCls (Dcnv ʻʻ pot (R ⨾ S)) = prodCls (Dcnv ʻʻ relProdR R ʻʻ pot (R ⨾ S)) := by
  rintro ⟨hS, hc⟩
  have hS' := mem_arrow_one_Cls.1 hS
  ext b
  rw [mem_pdc_relProdR]
  constructor
  · rintro ⟨a, ha, hba⟩ P hP
    rw [mem_prodCls_Dcnv] at ha
    obtain ⟨z, w, hzw, c, hwc, hca⟩ := ha _ (relProd_mem_pot hP)
    have : c = b := hS' c b a ⟨hca, hba⟩
    subst this
    exact ⟨z, w, hzw, hwc⟩
  · intro h
    obtain ⟨z, w, hzw, hwb⟩ := h _ (self_mem_pot (R ⨾ S))
    obtain ⟨c, hzc, hcw⟩ := hzw
    obtain ⟨a, hba⟩ := hc ⟨c, w, hcw, hwb⟩
    refine ⟨a, ?_, hba⟩
    rw [mem_prodCls_Dcnv, pdc_shift]
    intro P hP
    obtain ⟨z', w', hzw', hwb'⟩ := h P hP
    exact ⟨z', w', hzw', b, hwb', hba⟩

/-- ✱94·42. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.\breve{R}ʻʻpʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S)=pʻ\text{ᗡ}ʻʻ\mid Rʻʻ\text{Pot}ʻ(R\mid S)\) -/
theorem pm94_42 {R : α → β → Prop} {S : β → α → Prop} :
    R ∈ arrow one Cls →
      R˘ ʻʻ prodCls (Dcnv ʻʻ pot (R ⨾ S)) = prodCls (Dcnv ʻʻ relProdR R ʻʻ pot (R ⨾ S)) := by
  intro hR
  have hR' := mem_arrow_one_Cls.1 hR
  ext b
  rw [mem_pdc_relProdR]
  constructor
  · rintro ⟨a, ha, hab⟩ P hP
    rw [mem_prodCls_Dcnv] at ha
    obtain ⟨z, hza⟩ := ha P hP
    exact ⟨z, a, hza, hab⟩
  · intro h
    obtain ⟨z, a, hza, hab⟩ := h _ (self_mem_pot (R ⨾ S))
    refine ⟨a, ?_, hab⟩
    rw [mem_prodCls_Dcnv]
    intro P hP
    obtain ⟨z', a', hza', hab'⟩ := h P hP
    have : a' = a := hR' a' a b ⟨hab', hab⟩
    subst this
    exact ⟨z', hza'⟩

/-- ✱94·43. \[\begin{align}\vdash:R,S\in 1\rightarrow &\text{Cls}.\text{ᗡ}ʻ(S\mid R)\subset \text{D}ʻS.\supset.\\ & Sʻʻpʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S)=\breve{R}ʻʻpʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S) \quad[\text{*94·41·42}]\end{align}\] -/
theorem pm94_43 {R : α → β → Prop} {S : β → α → Prop} :
    (R ∈ arrow one Cls ∧ S ∈ arrow one Cls) ∧ codom (S ⨾ R) ⊆ dom S →
      S ʻʻ prodCls (Dcnv ʻʻ pot (R ⨾ S)) = R˘ ʻʻ prodCls (Dcnv ʻʻ pot (R ⨾ S)) := by
  rintro ⟨⟨hR, hS⟩, hc⟩
  rw [pm94_41 ⟨hS, hc⟩, pm94_42 hR]

/-- ✱94·441. \[\begin{align}\vdash:S\in 1\rightarrow &\text{Cls}.\text{ᗡ}ʻ(S\mid R)\subset \text{D}ʻS.\supset.\\ & Sʻʻpʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S)=pʻ\text{ᗡ}ʻʻR\mid ʻʻ\text{Pot}ʻ(S\mid R) \quad[\text{*94·14·41}]\end{align}\] -/
theorem pm94_441 {R : α → β → Prop} {S : β → α → Prop} :
    S ∈ arrow one Cls ∧ codom (S ⨾ R) ⊆ dom S →
      S ʻʻ prodCls (Dcnv ʻʻ pot (R ⨾ S)) = prodCls (Dcnv ʻʻ relProdL R ʻʻ pot (S ⨾ R)) := by
  intro h
  rw [pm94_41 h, pm94_14]

/-- ✱94·442. \[\begin{align}&\vdash:R\in 1\rightarrow \text{Cls}.\supset.\breve{R}ʻʻpʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S)=pʻ\text{ᗡ}ʻʻR\mid ʻʻ\text{Pot}ʻ(S\mid R)\\ &[\text{*94·14·42}]\end{align}\] -/
theorem pm94_442 {R : α → β → Prop} {S : β → α → Prop} :
    R ∈ arrow one Cls →
      R˘ ʻʻ prodCls (Dcnv ʻʻ pot (R ⨾ S)) = prodCls (Dcnv ʻʻ relProdL R ʻʻ pot (S ⨾ R)) := by
  intro h
  rw [pm94_42 h, pm94_14]

/-- ✱94·5. \(\vdash.pʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(S\mid R)=pʻ\text{ᗡ}ʻʻR\mid ʻʻ\text{Pot}ʻ(S\mid R)\) -/
theorem pm94_5 {R : α → β → Prop} {S : β → α → Prop} :
    prodCls (Dcnv ʻʻ pot (S ⨾ R)) = prodCls (Dcnv ʻʻ relProdL R ʻʻ pot (S ⨾ R)) := by
  ext b
  rw [mem_pdc_relProdL, mem_prodCls_Dcnv]
  constructor
  · intro h T hT
    have := h _ (relProd_mem_pot hT)
    rw [pot_comm hT, rp_assoc] at this
    exact codom_comp_sub _ _ this
  · intro h T hT
    exact codom_comp_sub _ _ (h T hT)

/-- ✱94·51. \[\begin{align}&\vdash:R\in 1\rightarrow \text{Cls}.\supset .pʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(S\mid R)=\breve{R}ʻʻpʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S)\\ &[\text{*94·5·442}]\end{align}\] -/
theorem pm94_51 {R : α → β → Prop} {S : β → α → Prop} :
    R ∈ arrow one Cls → prodCls (Dcnv ʻʻ pot (S ⨾ R)) = R˘ ʻʻ prodCls (Dcnv ʻʻ pot (R ⨾ S)) := by
  intro h
  rw [pm94_5, pm94_442 h]

/-- ✱94·52. \[\begin{align}\vdash:S\in 1\rightarrow \text{Cls}.&\text{ᗡ}ʻ(S\mid R)\subset \text{D}ʻS.\supset .\\ & pʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(S\mid R)=Sʻʻpʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S) \quad[\text{*94·5·441}]\end{align}\] -/
theorem pm94_52 {R : α → β → Prop} {S : β → α → Prop} :
    S ∈ arrow one Cls ∧ codom (S ⨾ R) ⊆ dom S →
      prodCls (Dcnv ʻʻ pot (S ⨾ R)) = S ʻʻ prodCls (Dcnv ʻʻ pot (R ⨾ S)) := by
  intro h
  rw [pm94_5, pm94_441 h]

/-- ✱94·53. \[\begin{align}\vdash:R\in 1\rightarrow 1.\text{ᗡ}ʻ(R\mid S)\subset \text{D}ʻ&R.\supset .\\ & pʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S)\text{ sm } pʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(S\mid R)\end{align}\] -/
theorem pm94_53 {R : α → β → Prop} {S : β → α → Prop} :
    R ∈ arrow one one ∧ codom (R ⨾ S) ⊆ dom R →
      sm (prodCls (Dcnv ʻʻ pot (R ⨾ S))) (prodCls (Dcnv ʻʻ pot (S ⨾ R))) := by
  rintro ⟨hR, hc⟩
  rw [pm94_51 (oneMany_of_oneOne hR)]
  refine sm_img_cnv hR ?_
  intro x hx
  rw [mem_prodCls_Dcnv] at hx
  exact hc (hx _ (self_mem_pot _))

/-- ✱94·54. \[\begin{align}&\vdash:S\in 1\rightarrow 1.\text{ᗡ}ʻ(S\mid R)\subset \text{D}ʻS.\supset .pʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(R\mid S)\text{ sm } pʻ\text{ᗡ}ʻʻ\text{Pot}ʻ(S\mid R)\\ &\left[\text{*94·53}\, \frac{S,R}{R,S}\right]\\ &[\text{Or, *94·52.*93·261.*73·22}]\end{align}\] -/
theorem pm94_54 {R : α → β → Prop} {S : β → α → Prop} :
    S ∈ arrow one one ∧ codom (S ⨾ R) ⊆ dom S →
      sm (prodCls (Dcnv ʻʻ pot (R ⨾ S))) (prodCls (Dcnv ʻʻ pot (S ⨾ R))) :=
  fun h => sm_symm (pm94_53 h)

/-- ✱94·6. \(\vdash\colon\ldotp R\mid S=S\mid R.\supset :M\in \text{Pot}ʻR.N\in \text{Pot}ʻS.\supset .M\mid N=N\mid M\) -/
theorem pm94_6 {R S M N : α → α → Prop} :
    R ⨾ S = S ⨾ R → (M ∈ pot R ∧ N ∈ pot S → M ⨾ N = N ⨾ M) := by
  rintro h ⟨hM, hN⟩
  obtain ⟨m, rfl⟩ := mem_pot_npow.1 hM
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 hN
  exact comm_npow_npow h _ _

/-- ✱94·61. \[\begin{align}\vdash\colon\ldotp R\mid S=S\mid R.\supset :&M\in \text{Pot}ʻR.\supset .M\mid S_{\text{po}}=S_{\text{po}}\mid M:\\ & N\in \text{Pot}ʻS.\supset .N\mid R_{\text{po}}=R_{\text{po}}\mid N\end{align}\] -/
theorem pm94_61 {R S M N : α → α → Prop} :
    R ⨾ S = S ⨾ R →
      (M ∈ pot R → M ⨾ po S = po S ⨾ M) ∧ (N ∈ pot S → N ⨾ po R = po R ⨾ N) := by
  intro h
  refine ⟨fun hM => comm_po fun n => pm94_6 h ⟨hM, npow_mem_pot S n⟩,
    fun hN => comm_po fun n => pm94_6 h.symm ⟨hN, npow_mem_pot R n⟩⟩

/-- ✱94·62. \(\vdash:R\mid S=S\mid R.\supset .R_{\text{po}}\mid S_{\text{po}}=S_{\text{po}}\mid R_{\text{po}}\) -/
theorem pm94_62 {R S : α → α → Prop} :
    R ⨾ S = S ⨾ R → po R ⨾ po S = po S ⨾ po R := by
  intro h
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, hyz⟩
    obtain ⟨m, hm⟩ := po_iff_npow.1 hxy
    obtain ⟨n, hn⟩ := po_iff_npow.1 hyz
    have : (npow R (m + 1) ⨾ npow S (n + 1)) x z := ⟨y, hm, hn⟩
    rw [comm_npow_npow h] at this
    obtain ⟨w, hxw, hwz⟩ := this
    exact ⟨w, po_iff_npow.2 ⟨n, hxw⟩, po_iff_npow.2 ⟨m, hwz⟩⟩
  · rintro ⟨y, hxy, hyz⟩
    obtain ⟨n, hn⟩ := po_iff_npow.1 hxy
    obtain ⟨m, hm⟩ := po_iff_npow.1 hyz
    have : (npow S (n + 1) ⨾ npow R (m + 1)) x z := ⟨y, hn, hm⟩
    rw [← comm_npow_npow h] at this
    obtain ⟨w, hxw, hwz⟩ := this
    exact ⟨w, po_iff_npow.2 ⟨m, hxw⟩, po_iff_npow.2 ⟨n, hwz⟩⟩

/-- ✱94·63. \(\vdash : R\mid S = S\mid R. \supset .(R\mid S)_{\text{po}} \unicode{x2abd} R_{\text{po}}\mid S_{\text{po}}\) -/
theorem pm94_63 {R S : α → α → Prop} :
    R ⨾ S = S ⨾ R → po (R ⨾ S) ⪽ po R ⨾ po S := by
  intro h x y hxy
  obtain ⟨n, hn⟩ := po_iff_npow.1 hxy
  rw [npow_relProd_comm h] at hn
  obtain ⟨a, hxa, hay⟩ := hn
  exact ⟨a, po_iff_npow.2 ⟨n, hxa⟩, po_iff_npow.2 ⟨n, hay⟩⟩

/-- ✱94·64. \(\vdash: R\mid S = S\mid R.\supset.(R\mid S)_{\unicode{x2217}} \unicode{x2abd} R_{\unicode{x2217}}\mid S_{\unicode{x2217}}\) -/
theorem pm94_64 {R S : α → α → Prop} :
    R ⨾ S = S ⨾ R → anc (R ⨾ S) ⪽ anc R ⨾ anc S := by
  intro h x y hxy
  obtain ⟨hx, n, hn⟩ := anc_iff_npow.1 hxy
  cases n with
  | zero =>
    have e : x = y := hn
    subst e
    have hfR : x ∈ fld R ∧ x ∈ fld S := by
      obtain ⟨z, hz | hz⟩ := hx
      · have hz' : (S ⨾ R) x z := h ▸ hz
        obtain ⟨a, hxa, -⟩ := hz
        obtain ⟨b, hxb, -⟩ := hz'
        exact ⟨⟨a, Or.inl hxa⟩, ⟨b, Or.inl hxb⟩⟩
      · have hz' : (S ⨾ R) z x := h ▸ hz
        obtain ⟨a, -, hax⟩ := hz
        obtain ⟨b, -, hbx⟩ := hz'
        exact ⟨⟨b, Or.inr hbx⟩, ⟨a, Or.inr hax⟩⟩
    exact ⟨x, anc_refl hfR.1, anc_refl hfR.2⟩
  | succ n =>
    rw [npow_relProd_comm h] at hn
    obtain ⟨a, hxa, hay⟩ := hn
    exact ⟨a, anc_iff_npow.2 ⟨(fld_of_npow_succ hxa).1, n + 1, hxa⟩,
      anc_iff_npow.2 ⟨(fld_of_npow_succ hay).1, n + 1, hay⟩⟩

/-!
## [✱95] On the equi-factor relation

*(Vol. 1, p. 626)*

> *Summary of* *95.
>
> The purpose of this number may be explained as follows. Consider the series of relations \[ R, P \mid R \mid Q,\, P^{2} \mid R \mid Q^{2},\, P^{3} \mid R \mid Q^{3}, \ldots\text{;} \] it is required to find a means of defining this series without the use of numbers. If we used numbers, and had the definition given later (*301) of \(P^{\nu}\) where \(\nu\) is any finite integer, the general term of the series would be \(P^{\nu} \mid R \mid Q^{\nu}\). But we have not yet defined numbers, and we therefore desire some means, not involving numbers, of expressing what is intended when we say that, in a given term of the series, the same power of \(P\) and of \(Q\) is to be involved. This we do as follows. Using the definition of \(P\parallel Q\) in *43, we have \[ P \mid R \mid Q = (P \parallel Q)ʻR . P^{2} \mid R \mid Q^{2} = (P \parallel Q)^{2}ʻR . P^{3} \mid R \mid Q^{3} = (P \parallel Q)^{3}ʻR \ldots\text{.} \]
>
> …

**Lean reading.** `(P∗Q)` (Dft ✱95·01) is `eqf P Q`, and `(P∗Q)'R` is written
`refs (anc (P ∥ Q)) R` (`desc_eqf`); its members are the relations `P^n | R | Q^n`, with
`P : α → α → Prop`, `Q : β → β → Prop`, `R : α → β → Prop`. A hypothesis `Hp✱95·N` is written out
in full, flat products bracketed to the left, and `S, S' ∈ …` is a conjunction. `B⃗'Q` is
`refs Beg Q`, `B⃗'P̆` is `refs Beg P˘`, `P_st | Q_ts` is `Rst P ⨾ Rts Q`, and `ṡ'(P∗Q)'R` is
`sumRel (refs (anc (P ∥ Q)) R)`. The propositions ✱95·411–·45 need the hypothesis
`D'R ⊂ C'P . ᗡ'R ⊂ C'Q` of ✱95·22, which PM's proofs use but the enunciations omit; they are proved
with it added, and the printed forms are refuted in Lean. ✱95·46 reads `B⃗'Q` for the printed
`B⃗'Q̆`, ✱95·37 adds `∃̇!R`, and ✱95·62 has `s'gen'P̆` for `s'gen'P` (see the docstrings).

**Status.** proved (all propositions; ✱95·01 definition (Dft); ✱95·37, ✱95·411, ✱95·42,
✱95·43, ✱95·431, ✱95·44, ✱95·45, ✱95·62 proved (corrected); ✱95·46, ✱95·47, ✱95·471, ✱95·51,
✱95·511 proved (reading); see their docstrings).
-/

/-- ✱95·01. (\(P\unicode{x2217}Q)=\text{sg}ʻ\{(P\Arrowvert Q)_{\unicode{x2217}}\} \quad\text{Dft}\, [\text{*95}]\)

**Status.** definition: a temporary definition (Dft, used in ✱95 only). The definiendum
`(P∗Q)` is a constant and the definiens the descriptive function `sg'(P‖Q)_*` of a constant, so
the Df is stated with `Desc` (`eqf P Q = Rfwd (anc (P ∥ Q))`); in formulas `(P∗Q)'R` is
`refs (anc (P ∥ Q)) R` (`desc_eqf`). -/
theorem pm95_01 {P : α → α → Prop} {Q : β → β → Prop} :
    Desc sg (anc (P ∥ Q)) (fun X => eqf P Q = X) :=
  (desc_graph _ _ _).2 rfl

/-- ✱95·1. \(\vdash\colon\colon M\in (P\unicode{x2217}Q)ʻR.\equiv\colon\ldotp R\in \mu:N\in \mu.\supset_{N}.P\mid N\mid Q\in \mu:\supset_{\mu}.M\in \mu\) -/
theorem pm95_1 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    M ∈ refs (anc (P ∥ Q)) R ↔
      ∀ μ : Set (α → β → Prop), (R ∈ μ ∧ ∀ N, N ∈ μ → P ⨾ N ⨾ Q ∈ μ) → M ∈ μ := by
  constructor
  · intro h μ ⟨hR, hμ⟩
    obtain ⟨n, rfl⟩ := eqf_mem.1 h
    induction n with
    | zero => rw [npow_sandwich_zero]; exact hR
    | succ n ih =>
      rw [npow_sandwich_succ]
      exact hμ _ (ih (npow_mem_eqf P Q R n))
  · intro h
    refine h _ ⟨eqf_mem.2 ⟨0, (npow_sandwich_zero P Q R).symm⟩, ?_⟩
    intro N hN
    obtain ⟨n, rfl⟩ := eqf_mem.1 hN
    rw [← npow_sandwich_succ]
    exact npow_mem_eqf P Q R (n + 1)

/-- ✱95·11. \(\vdash\colon\ldotp \phi R:\phi N.\supset_{N}.\phi(P\mid N\mid Q):\supset:M\in (P\unicode{x2217}Q)ʻR.\supset_{M}.\phi M\) -/
theorem pm95_11 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {φ : (α → β → Prop) → Prop} :
    (φ R ∧ ∀ N, φ N → φ (P ⨾ N ⨾ Q)) → ∀ M, M ∈ refs (anc (P ∥ Q)) R → φ M := by
  intro h M hM
  exact pm95_1.1 hM {N | φ N} h

/-- ✱95·12. \(\vdash\colon\ldotp M\in (P\unicode{x2217}Q)ʻR.\supset_{M}.\phi(P\mid M\mid Q):\supset:N\in (P\unicode{x2217}Q)ʻR-\iotaʻR.\supset_{N}.\phi N\) -/
theorem pm95_12 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {φ : (α → β → Prop) → Prop} :
    (∀ M, M ∈ refs (anc (P ∥ Q)) R → φ (P ⨾ M ⨾ Q)) →
      ∀ N, N ∈ refs (anc (P ∥ Q)) R \ ι R → φ N := by
  rintro h N ⟨hN, hNR⟩
  obtain ⟨n, rfl⟩ := eqf_mem.1 hN
  cases n with
  | zero => exact absurd (npow_sandwich_zero P Q R) hNR
  | succ n =>
    rw [npow_sandwich_succ]
    exact h _ (npow_mem_eqf P Q R n)

/-- ✱95·13. \(\vdash.R\in (P\unicode{x2217}Q)ʻR \quad[\text{*95·1}]\) -/
theorem pm95_13 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} :
    R ∈ refs (anc (P ∥ Q)) R :=
  eqf_mem.2 ⟨0, (npow_sandwich_zero P Q R).symm⟩

/-- ✱95·131. \(\vdash.P\mid R\mid Q\in (P\unicode{x2217}Q)ʻR\) -/
theorem pm95_131 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} :
    P ⨾ R ⨾ Q ∈ refs (anc (P ∥ Q)) R := by
  have := npow_mem_eqf P Q R 1
  rwa [npow_sandwich_succ, npow_sandwich_zero] at this

/-- ✱95·132. \[\begin{align}&\vdash:M\in (P \unicode{x2217} Q)ʻR.\supset.P\mid M\mid Q\in (P \unicode{x2217} Q)ʻR\\ &\left[\text{*90·172}\, \frac{P\Arrowvert Q}{R} .\text{*43·102}\right]\end{align}\] -/
theorem pm95_132 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    M ∈ refs (anc (P ∥ Q)) R → P ⨾ M ⨾ Q ∈ refs (anc (P ∥ Q)) R := by
  intro h
  obtain ⟨n, rfl⟩ := eqf_mem.1 h
  rw [← npow_sandwich_succ]
  exact npow_mem_eqf P Q R (n + 1)

/-- ✱95·14. \(\vdash\colon\ldotp \phi R:N\in (P \unicode{x2217} Q)ʻR.\phi N.\supset_{N}.\phi(P\mid N\mid Q):\supset:M\in (P \unicode{x2217} Q)ʻR.\supset_{M}.\phi M\) -/
theorem pm95_14 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {φ : (α → β → Prop) → Prop} :
    (φ R ∧ ∀ N, N ∈ refs (anc (P ∥ Q)) R ∧ φ N → φ (P ⨾ N ⨾ Q)) →
      ∀ M, M ∈ refs (anc (P ∥ Q)) R → φ M := by
  rintro ⟨h0, h1⟩ M hM
  have := pm95_11 (φ := fun N => N ∈ refs (anc (P ∥ Q)) R ∧ φ N)
    ⟨⟨pm95_13, h0⟩, fun N hN => ⟨pm95_132 hN.1, h1 N hN⟩⟩ M hM
  exact this.2

/-- ✱95·21. \(\vdash:M\in (P \unicode{x2217} Q)ʻR.\supset.(\exists S,T).S\in \text{Pot}ʻP\cup \iotaʻI.T\in \text{Pot}ʻQ\cup \iotaʻI.M=S\mid R\mid T\) -/
theorem pm95_21 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    M ∈ refs (anc (P ∥ Q)) R →
      ∃ S T, (S ∈ pot P ∪ ι I ∧ T ∈ pot Q ∪ ι I) ∧ M = S ⨾ R ⨾ T := by
  intro h
  obtain ⟨n, rfl⟩ := eqf_mem.1 h
  exact ⟨_, _, ⟨mem_pot_union_I.2 ⟨n, rfl⟩, mem_pot_union_I.2 ⟨n, rfl⟩⟩, rfl⟩

/-- ✱95·211. \[\begin{align}\vdash:\text{ᗡ}ʻR\subset CʻQ.M &\in (P \unicode{x2217} Q)ʻR.\supset.\\ &(\exists S,T).S\in \text{Pot}ʻP\cup \iotaʻI.T\in \text{Potid}ʻQ.M=S\mid R\mid T\end{align}\] -/
theorem pm95_211 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    codom R ⊆ fld Q ∧ M ∈ refs (anc (P ∥ Q)) R →
      ∃ S T, (S ∈ pot P ∪ ι I ∧ T ∈ potid Q) ∧ M = S ⨾ R ⨾ T := by
  rintro ⟨hc, h⟩
  obtain ⟨n, rfl⟩ := eqf_mem.1 h
  refine ⟨_, ipow Q n, ⟨mem_pot_union_I.2 ⟨n, rfl⟩, ipow_mem_potid Q n⟩, ?_⟩
  rw [comp_ipow_eq ((codom_comp_sub _ _).trans hc)]

/-- ✱95·212. \[\begin{align}\vdash:\text{D}ʻR &\subset CʻP.M\in (P \unicode{x2217} Q)ʻR.\supset.\\ &(\exists S,T).S\in \text{Potid}ʻP.T\in \text{Pot}ʻQ\cup \iotaʻI.M=S\mid R\mid T\\ &[\text{Proof as in *95·211}]\end{align}\] -/
theorem pm95_212 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    dom R ⊆ fld P ∧ M ∈ refs (anc (P ∥ Q)) R →
      ∃ S T, (S ∈ potid P ∧ T ∈ pot Q ∪ ι I) ∧ M = S ⨾ R ⨾ T := by
  rintro ⟨hd, h⟩
  obtain ⟨n, rfl⟩ := eqf_mem.1 h
  refine ⟨ipow P n, _, ⟨ipow_mem_potid P n, mem_pot_union_I.2 ⟨n, rfl⟩⟩, ?_⟩
  rw [rp_assoc, rp_assoc, ipow_comp_eq ((dom_comp_sub _ _).trans hd)]

/-- ✱95·22. \[\begin{align}\vdash:\text{D}ʻR &\subset CʻP.\text{ᗡ}ʻR\subset CʻQ.M\in (P \unicode{x2217} Q)ʻR.\supset.\\ &(\exists S,T).S\in \text{Potid}ʻP.T\in \text{Potid}ʻQ.M=S\mid R\mid T\\ [\text{Proof as in *95·211}]\end{align}\] -/
theorem pm95_22 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    (dom R ⊆ fld P ∧ codom R ⊆ fld Q) ∧ M ∈ refs (anc (P ∥ Q)) R →
      ∃ S T, (S ∈ potid P ∧ T ∈ potid Q) ∧ M = S ⨾ R ⨾ T := by
  rintro ⟨⟨hd, hc⟩, h⟩
  obtain ⟨n, rfl⟩ := eqf_mem.1 h
  refine ⟨ipow P n, ipow Q n, ⟨ipow_mem_potid P n, ipow_mem_potid Q n⟩, ?_⟩
  rw [comp_ipow_eq ((codom_comp_sub _ _).trans hc), rp_assoc, rp_assoc,
    ipow_comp_eq ((dom_comp_sub _ _).trans hd)]

/-- ✱95·221. \(\vdash:T\in \text{Pot}ʻQ.\supset.(\exists S).S\in \text{Pot}ʻP.S\mid R\mid T\in (P \unicode{x2217} Q)ʻR\) -/
theorem pm95_221 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} {T : β → β → Prop} :
    T ∈ pot Q → ∃ S, S ∈ pot P ∧ S ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R := by
  intro h
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 h
  exact ⟨npow P (n + 1), npow_mem_pot P n, npow_mem_eqf P Q R (n + 1)⟩

/-- ✱95·222. \[\begin{align}&\vdash:S\in \text{Pot}ʻP.\supset.(\exists T).T\in \text{Pot}ʻQ.S\mid R\mid T\in (P \unicode{x2217} Q)ʻR\\ &[\text{Proof as in *95·221}]\end{align}\] -/
theorem pm95_222 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} {S : α → α → Prop} :
    S ∈ pot P → ∃ T, T ∈ pot Q ∧ S ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R := by
  intro h
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 h
  exact ⟨npow Q (n + 1), npow_mem_pot Q n, npow_mem_eqf P Q R (n + 1)⟩

/-- ✱95·23. \(\vdash:M\in (P \unicode{x2217} Q)ʻR.\supset.M(P_{\text{st}}\mid Q_{\text{ts}})R\) -/
theorem pm95_23 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    M ∈ refs (anc (P ∥ Q)) R → (Rst P ⨾ Rts Q) M R := by
  intro h
  obtain ⟨n, rfl⟩ := eqf_mem.1 h
  exact ⟨R ⨾ npow Q n, (Rst_iff _ _ _).2 ⟨n, rp_assoc _ _ _⟩, (Rts_iff _ _ _).2 ⟨n, rfl⟩⟩

/-- ✱95·24. \(\vdash:M\in (P \unicode{x2217} Q)ʻR.\supset.M(Q_{\text{ts}}\mid P_{\text{st}})R \quad[\text{Proof as in *95·23}]\) -/
theorem pm95_24 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    M ∈ refs (anc (P ∥ Q)) R → (Rts Q ⨾ Rst P) M R := by
  intro h
  obtain ⟨n, rfl⟩ := eqf_mem.1 h
  exact ⟨npow P n ⨾ R, (Rts_iff _ _ _).2 ⟨n, rfl⟩, (Rst_iff _ _ _).2 ⟨n, rfl⟩⟩

/-- ✱95·3. \(\vdash\colon\ldotp \dot{\exists}!R.\text{ᗡ}ʻQ\subset \text{D}ʻQ.\text{ᗡ}ʻR\subset \text{D}ʻQ.\supset:T\in \text{Potid}ʻQ.\supset.\dot{\exists}!R\mid T\) -/
theorem pm95_3 {Q : β → β → Prop} {R : α → β → Prop} {T : β → β → Prop} :
    (rEx R ∧ codom Q ⊆ dom Q) ∧ codom R ⊆ dom Q → (T ∈ potid Q → rEx (R ⨾ T)) := by
  rintro ⟨⟨⟨x, y, hxy⟩, hQ⟩, hR⟩ hT
  obtain ⟨n, rfl⟩ := mem_potid'.1 hT
  have hy : y ∈ dom Q := hR ⟨x, hxy⟩
  obtain ⟨z, hz⟩ := npow_fwd hQ n y hy
  exact ⟨x, z, y, hxy, ipow_apply.2 ⟨dom_sub_fld Q hy, hz⟩⟩

/-- ✱95·301. \[\begin{align}&\vdash\colon\ldotp \dot{\exists}!R.\text{D}ʻP\subset \text{ᗡ}ʻP.\text{D}ʻR\subset \text{ᗡ}ʻP.\supset:S\in \text{Potid}ʻP.\supset.\dot{\exists}!S\mid R\\ &[\text{Proof as in *95·3}]\end{align}\] -/
theorem pm95_301 {P : α → α → Prop} {R : α → β → Prop} {S : α → α → Prop} :
    (rEx R ∧ dom P ⊆ codom P) ∧ dom R ⊆ codom P → (S ∈ potid P → rEx (S ⨾ R)) := by
  rintro ⟨⟨⟨x, y, hxy⟩, hP⟩, hR⟩ hS
  obtain ⟨n, rfl⟩ := mem_potid'.1 hS
  have hx : x ∈ codom P := hR ⟨y, hxy⟩
  obtain ⟨w, hw⟩ := npow_bwd hP n x hx
  exact ⟨w, y, x, ipow_of_npow_right hw (codom_sub_fld P hx), hxy⟩

/-- ✱95·302. \(\vdash\colon\ldotp \text{ᗡ}ʻQ\subset \text{D}ʻQ.\text{ᗡ}ʻR\subset \text{D}ʻQ.\supset:T\in \text{Potid}ʻQ.\supset.\text{ᗡ}ʻ(R\mid T)\subset \text{D}ʻQ\) -/
theorem pm95_302 {Q : β → β → Prop} {R : α → β → Prop} {T : β → β → Prop} :
    codom Q ⊆ dom Q ∧ codom R ⊆ dom Q → (T ∈ potid Q → codom (R ⨾ T) ⊆ dom Q) := by
  rintro ⟨hQ, hR⟩ hT
  obtain ⟨n, rfl⟩ := mem_potid'.1 hT
  rw [comp_ipow_eq (hR.trans (dom_sub_fld Q))]
  exact codom_comp_npow_sub hR hQ n

/-- ✱95·303. \[\begin{align}&\vdash\colon\ldotp \text{D}ʻR\subset \text{ᗡ}ʻP.\text{D}ʻP\subset \text{ᗡ}ʻP.\supset:S\in \text{Potid}ʻP.\supset.\text{D}ʻ(S\mid R)\subset \text{ᗡ}ʻP\\ &[\text{Proof as in *95·302}]\end{align}\] -/
theorem pm95_303 {P : α → α → Prop} {R : α → β → Prop} {S : α → α → Prop} :
    dom R ⊆ codom P ∧ dom P ⊆ codom P → (S ∈ potid P → dom (S ⨾ R) ⊆ codom P) := by
  rintro ⟨hR, hP⟩ hS
  obtain ⟨n, rfl⟩ := mem_potid'.1 hS
  rw [ipow_comp_eq (hR.trans (codom_sub_fld P))]
  exact dom_npow_comp_sub hR hP n

/-- ✱95·304. \[\begin{align}&\vdash\colon\ldotp \text{ᗡ}ʻQ\subset \text{D}ʻQ.\text{ᗡ}ʻR\subset \text{D}ʻQ.\text{D}ʻP\subset \text{ᗡ}ʻP.\text{D}ʻR\subset \text{ᗡ}ʻP.\supset:\\ &S\in \text{Potid}ʻP.T\in \text{Potid}ʻQ.\supset.\text{D}ʻ(S\mid R\mid T)\subset \text{ᗡ}ʻP.\text{ᗡ}ʻ(S\mid R\mid T)\subset \text{D}ʻQ\\ &[\text{*95·302·303.*34·36}]\end{align}\] -/
theorem pm95_304 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {S : α → α → Prop} {T : β → β → Prop} :
    ((codom Q ⊆ dom Q ∧ codom R ⊆ dom Q) ∧ dom P ⊆ codom P) ∧ dom R ⊆ codom P →
      (S ∈ potid P ∧ T ∈ potid Q → dom (S ⨾ R ⨾ T) ⊆ codom P ∧ codom (S ⨾ R ⨾ T) ⊆ dom Q) := by
  rintro ⟨⟨⟨hQ, hRQ⟩, hP⟩, hRP⟩ ⟨hS, hT⟩
  refine ⟨(dom_comp_sub _ _).trans (pm95_303 ⟨hRP, hP⟩ hS), ?_⟩
  rw [rp_assoc]
  exact (codom_comp_sub _ _).trans (pm95_302 ⟨hQ, hRQ⟩ hT)

/-- ✱95·305. \[\begin{align}&\vdash\colon\ldotp \text{Hp}*95·304.\supset:M\in (P \unicode{x2217} Q)ʻR.\supset.\text{D}ʻM\subset \text{ᗡ}ʻP.\text{ᗡ}ʻM\subset \text{D}ʻQ\\ &[\text{*95·304·22}]\end{align}\] -/
theorem pm95_305 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    ((codom Q ⊆ dom Q ∧ codom R ⊆ dom Q) ∧ dom P ⊆ codom P) ∧ dom R ⊆ codom P →
      (M ∈ refs (anc (P ∥ Q)) R → dom M ⊆ codom P ∧ codom M ⊆ dom Q) := by
  intro hyp hM
  obtain ⟨⟨⟨-, hRQ⟩, -⟩, hRP⟩ := id hyp
  obtain ⟨S, T, ⟨hS, hT⟩, rfl⟩ :=
    pm95_22 ⟨⟨hRP.trans (codom_sub_fld P), hRQ.trans (dom_sub_fld Q)⟩, hM⟩
  exact pm95_304 hyp ⟨hS, hT⟩

/-- ✱95·31. \(\vdash\colon\ldotp \text{Hp*95·304}.\dot{\exists}!R.\supset:S\in \text{Potid}ʻP.T\in \text{Potid}ʻQ.\supset.\dot{\exists}!S\mid R\mid T\) -/
theorem pm95_31 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {S : α → α → Prop} {T : β → β → Prop} :
    (((codom Q ⊆ dom Q ∧ codom R ⊆ dom Q) ∧ dom P ⊆ codom P) ∧ dom R ⊆ codom P) ∧ rEx R →
      (S ∈ potid P ∧ T ∈ potid Q → rEx (S ⨾ R ⨾ T)) := by
  rintro ⟨⟨⟨⟨hQ, hRQ⟩, hP⟩, hRP⟩, ⟨x, y, hxy⟩⟩ ⟨hS, hT⟩
  obtain ⟨m, rfl⟩ := mem_potid'.1 hS
  obtain ⟨n, rfl⟩ := mem_potid'.1 hT
  have hx : x ∈ codom P := hRP ⟨y, hxy⟩
  have hy : y ∈ dom Q := hRQ ⟨x, hxy⟩
  obtain ⟨w, hw⟩ := npow_bwd hP m x hx
  obtain ⟨z, hz⟩ := npow_fwd hQ n y hy
  exact ⟨w, z, y, ⟨x, ipow_of_npow_right hw (codom_sub_fld P hx), hxy⟩,
    ipow_apply.2 ⟨dom_sub_fld Q hy, hz⟩⟩

/-- ✱95·32. \(\vdash\colon\ldotp \text{Hp*95·31}.\supset:M\in (P \unicode{x2217} Q)ʻR.\supset.\dot{\exists}!M \quad[\text{*95·31·22}]\) -/
theorem pm95_32 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    (((codom Q ⊆ dom Q ∧ codom R ⊆ dom Q) ∧ dom P ⊆ codom P) ∧ dom R ⊆ codom P) ∧ rEx R →
      (M ∈ refs (anc (P ∥ Q)) R → rEx M) := by
  intro hyp hM
  obtain ⟨⟨⟨⟨-, hRQ⟩, -⟩, hRP⟩, -⟩ := id hyp
  obtain ⟨S, T, ⟨hS, hT⟩, rfl⟩ :=
    pm95_22 ⟨⟨hRP.trans (codom_sub_fld P), hRQ.trans (dom_sub_fld Q)⟩, hM⟩
  exact pm95_31 hyp ⟨hS, hT⟩

/-- ✱95·33. \(\vdash:\text{ᗡ}ʻR\subset \overrightarrow{B}ʻQ.\supset.\text{ᗡ}ʻ(S\mid R\mid T)\subset \breve{T}ʻʻ\overrightarrow{B}ʻQ\) -/
theorem pm95_33 {Q : β → β → Prop} {R : α → β → Prop} {S : γ → α → Prop} {T : β → δ → Prop} :
    codom R ⊆ refs Beg Q → codom (S ⨾ R ⨾ T) ⊆ T˘ ʻʻ refs Beg Q := by
  rintro h z ⟨x, b, ⟨a, -, hab⟩, hbz⟩
  exact ⟨b, h ⟨a, hab⟩, hbz⟩

/-- ✱95·34. \[\begin{align}&\vdash:\text{ᗡ}ʻR\subset \overrightarrow{B}ʻQ.M\in (P \unicode{x2217} Q)ʻR.\supset.(\exists T).T\in \text{Potid}ʻQ.\text{ᗡ}ʻM\subset \breve{T}ʻʻ\overrightarrow{B}ʻQ\\ &[\text{*95·33·211}]\end{align}\] -/
theorem pm95_34 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    codom R ⊆ refs Beg Q ∧ M ∈ refs (anc (P ∥ Q)) R →
      ∃ T, T ∈ potid Q ∧ codom M ⊆ T˘ ʻʻ refs Beg Q := by
  rintro ⟨hc, hM⟩
  have hcf : codom R ⊆ fld Q := fun y hy => dom_sub_fld Q (beg_dom (hc hy))
  obtain ⟨S, T, ⟨-, hT⟩, rfl⟩ := pm95_211 ⟨hcf, hM⟩
  exact ⟨T, hT, pm95_33 hc⟩

/-- ✱95·35. \[\begin{align}&\vdash:Q\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻR\subset \overrightarrow{B}ʻQ.M\in (P \unicode{x2217} Q)ʻR.\supset.(\exists \alpha).\alpha\in \text{gen}ʻQ.\text{ᗡ}ʻM\subset \alpha\\ &[\text{*95·34.*93·32}]\end{align}\] -/
theorem pm95_35 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    (Q ∈ arrow one Cls ∧ codom R ⊆ refs Beg Q) ∧ M ∈ refs (anc (P ∥ Q)) R →
      ∃ A, A ∈ gen Q ∧ codom M ⊆ A := by
  rintro ⟨⟨hQ, hc⟩, hM⟩
  obtain ⟨T, hT, hsub⟩ := pm95_34 ⟨hc, hM⟩
  obtain ⟨n, rfl⟩ := mem_potid'.1 hT
  exact ⟨_, (mem_gen_oneMany (mem_arrow_one_Cls.1 hQ)).2 ⟨n, rfl⟩, hsub⟩

/-- ✱95·351. \[\begin{align}\vdash\colon\ldotp Q\in 1&\rightarrow \text{Cls}.\text{ᗡ}ʻR\subset \overrightarrow{B}ʻQ.\supset:\\ &T,\,T'\in \text{Potid}ʻQ.\exists !\text{ᗡ}ʻ(S\mid R\mid T)\cap \text{ᗡ}ʻ(S'\mid R\mid T').\supset.T=T'\end{align}\] -/
theorem pm95_351 {Q : β → β → Prop} {R : α → β → Prop} {S S' : γ → α → Prop}
    {T T' : β → β → Prop} :
    Q ∈ arrow one Cls ∧ codom R ⊆ refs Beg Q →
      ((T ∈ potid Q ∧ T' ∈ potid Q) ∧ (codom (S ⨾ R ⨾ T) ∩ codom (S' ⨾ R ⨾ T')).Nonempty →
        T = T') := by
  rintro ⟨hQ, hc⟩ ⟨⟨hT, hT'⟩, y, hy, hy'⟩
  obtain ⟨n, rfl⟩ := mem_potid'.1 hT
  obtain ⟨m, rfl⟩ := mem_potid'.1 hT'
  obtain ⟨b, hb, hby⟩ := pm95_33 hc hy
  obtain ⟨b', hb', hby'⟩ := pm95_33 hc hy'
  rw [beg_npow_unique (mem_arrow_one_Cls.1 hQ) n m b b' y hb hb' (ipow_apply.1 hby).2
    (ipow_apply.1 hby').2]

private theorem dom_comp_end_sub {P : α → α → Prop} {R : α → β → Prop} {S : γ → α → Prop}
    {T : β → δ → Prop} (h : dom R ⊆ refs Beg P˘) : dom (S ⨾ R ⨾ T) ⊆ S ʻʻ refs Beg P˘ := by
  rintro x ⟨z, b, ⟨a, hxa, hab⟩, -⟩
  exact ⟨a, h ⟨b, hab⟩, hxa⟩

/-- ✱95·352. \[\begin{align}\vdash\colon\ldotp P\in \text{Cls}&\rightarrow 1.\text{D}ʻR\subset \overrightarrow{B}ʻ\breve{P}.\supset:\\ &S,\,S'\in \text{Potid}ʻP.\exists !\text{D}ʻ(S\mid R\mid T)\cap \text{D}ʻ(S'\mid R\mid T').\supset.S=S'\\ &[\text{Proof as in *95·351}]\end{align}\] -/
theorem pm95_352 {P : α → α → Prop} {R : α → β → Prop} {S S' : α → α → Prop}
    {T T' : β → γ → Prop} :
    P ∈ arrow Cls one ∧ dom R ⊆ refs Beg P˘ →
      ((S ∈ potid P ∧ S' ∈ potid P) ∧ (dom (S ⨾ R ⨾ T) ∩ dom (S' ⨾ R ⨾ T')).Nonempty →
        S = S') := by
  rintro ⟨hP, hd⟩ ⟨⟨hS, hS'⟩, x, hx, hx'⟩
  obtain ⟨n, rfl⟩ := mem_potid'.1 hS
  obtain ⟨m, rfl⟩ := mem_potid'.1 hS'
  obtain ⟨e, he, hxe⟩ := dom_comp_end_sub hd hx
  obtain ⟨e', he', hxe'⟩ := dom_comp_end_sub hd hx'
  rw [end_npow_unique (mem_arrow_Cls_one.1 hP) n m x e e' he he' (ipow_apply.1 hxe).2
    (ipow_apply.1 hxe').2]

/-- ✱95·36. \[\begin{align}\vdash\colon\ldotp Q\in 1&\rightarrow \text{Cls}.\text{ᗡ}ʻR\subset \overrightarrow{B}ʻQ.\dot{\exists}!R.\text{D}ʻR\subset \text{ᗡ}ʻP.\\ &\text{D}ʻP\subset \text{ᗡ}ʻP.\text{ᗡ}ʻQ\subset \text{D}ʻQ.\supset:\\ &S,\,S'\in \text{Potid}ʻP.T,T'\in \text{Potid}ʻQ.S\mid R\mid T=S'\mid R\mid T'.\supset.T=T'\end{align}\] -/
theorem pm95_36 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {S S' : α → α → Prop} {T T' : β → β → Prop} :
    (((((Q ∈ arrow one Cls ∧ codom R ⊆ refs Beg Q) ∧ rEx R) ∧ dom R ⊆ codom P) ∧
      dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) →
      (((S ∈ potid P ∧ S' ∈ potid P) ∧ (T ∈ potid Q ∧ T' ∈ potid Q)) ∧
        S ⨾ R ⨾ T = S' ⨾ R ⨾ T' → T = T') := by
  rintro ⟨⟨⟨⟨⟨hQ, hc⟩, hR⟩, hdR⟩, hP⟩, hcQ⟩ ⟨⟨⟨hS, -⟩, ⟨hT, hT'⟩⟩, he⟩
  have hcd : codom R ⊆ dom Q := fun y hy => beg_dom (hc hy)
  obtain ⟨x, z, hxz⟩ := pm95_31 ⟨⟨⟨⟨hcQ, hcd⟩, hP⟩, hdR⟩, hR⟩ ⟨hS, hT⟩
  have hz' : z ∈ codom (S' ⨾ R ⨾ T') := by
    rw [← he]
    exact ⟨x, hxz⟩
  exact pm95_351 ⟨hQ, hc⟩ ⟨⟨hT, hT'⟩, z, ⟨x, hxz⟩, hz'⟩

/-- ✱95·361. \[\begin{align}\vdash\colon\ldotp P\in \text{Cls}\rightarrow 1.\text{D}ʻR&\subset \overrightarrow{B}ʻ\breve{P}.\dot{\exists}!R.\text{D}ʻP\subset \text{ᗡ}ʻP.\\ &\text{ᗡ}ʻR\subset \text{D}ʻQ.\text{ᗡ}ʻQ\subset \text{D}ʻQ.\supset:\\ &S,\,S'\in \text{Potid}ʻP.T,\,T'\in \text{Potid}ʻQ.S\mid R\mid T=S'\mid R\mid T'.\supset.S=S'\\ &[\text{Proof as in *95·36}]\end{align}\] -/
theorem pm95_361 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {S S' : α → α → Prop} {T T' : β → β → Prop} :
    (((((P ∈ arrow Cls one ∧ dom R ⊆ refs Beg P˘) ∧ rEx R) ∧ dom P ⊆ codom P) ∧
      codom R ⊆ dom Q) ∧ codom Q ⊆ dom Q) →
      (((S ∈ potid P ∧ S' ∈ potid P) ∧ (T ∈ potid Q ∧ T' ∈ potid Q)) ∧
        S ⨾ R ⨾ T = S' ⨾ R ⨾ T' → S = S') := by
  rintro ⟨⟨⟨⟨⟨hP, hd⟩, hR⟩, hPd⟩, hcd⟩, hcQ⟩ ⟨⟨⟨hS, hS'⟩, ⟨hT, -⟩⟩, he⟩
  have hdc : dom R ⊆ codom P := fun x hx => end_codom (hd hx)
  obtain ⟨x, z, hxz⟩ := pm95_31 ⟨⟨⟨⟨hcQ, hcd⟩, hPd⟩, hdc⟩, hR⟩ ⟨hS, hT⟩
  have hx' : x ∈ dom (S' ⨾ R ⨾ T') := by
    rw [← he]
    exact ⟨z, hxz⟩
  exact pm95_352 ⟨hP, hd⟩ ⟨⟨hS, hS'⟩, x, ⟨z, hxz⟩, hx'⟩

/-- ✱95·37. \[\begin{align}\vdash\colon\ldotp P\in \text{Cls}\rightarrow 1.Q\in 1\rightarrow \text{Cls}.\text{D}ʻR&\subset \overrightarrow{B}ʻ\breve{P}.\text{ᗡ}ʻR\subset \overrightarrow{B}ʻQ.\\ &\text{D}ʻP\subset \text{ᗡ}ʻP.\text{ᗡ}ʻQ\subset \text{D}ʻQ.\supset:\\ &S,\,S'\in \text{Potid}ʻP.T,T'\in \text{Potid}ʻQ.S\mid R\mid T=S'\mid R\mid T'.\supset.S=S'.T=T'\\ &[\text{*95·36·361}]\end{align}\]

**Status.** proved (corrected): the hypothesis `∃̇!R` is missing (it is in ✱95·36 and
✱95·361, from which PM derives ✱95·37). Without it the proposition is false: for `R = Λ̇`,
`S|R|T = Λ̇ = S'|R|T'` for all `S, S', T, T'`, while `Potid'P` may have two members
(`pm95_37_printed_false`: `P = Q` the transposition of `Bool`, `S = I ↾ C'P`, `S' = P`). The
corrected statement adds `∃̇!R` (`rEx R`) after `ᗡ'R ⊂ B⃗'Q`. -/
theorem pm95_37 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {S S' : α → α → Prop} {T T' : β → β → Prop} :
    ((((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom R ⊆ refs Beg P˘) ∧
      codom R ⊆ refs Beg Q) ∧ rEx R) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) →
      (((S ∈ potid P ∧ S' ∈ potid P) ∧ (T ∈ potid Q ∧ T' ∈ potid Q)) ∧
        S ⨾ R ⨾ T = S' ⨾ R ⨾ T' → S = S' ∧ T = T') := by
  rintro ⟨⟨⟨⟨⟨⟨hP, hQ⟩, hd⟩, hc⟩, hR⟩, hPd⟩, hQc⟩ h
  have hdc : dom R ⊆ codom P := fun x hx => end_codom (hd hx)
  have hcd : codom R ⊆ dom Q := fun y hy => beg_dom (hc hy)
  exact ⟨pm95_361 ⟨⟨⟨⟨⟨hP, hd⟩, hR⟩, hPd⟩, hcd⟩, hQc⟩ h,
    pm95_36 ⟨⟨⟨⟨⟨hQ, hc⟩, hR⟩, hdc⟩, hPd⟩, hQc⟩ h⟩

private def swapB : Bool → Bool → Prop := fun x y => y = !x

theorem pm95_37_printed_false :
    ¬ ∀ (P Q R S S' T T' : Bool → Bool → Prop),
      (((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom R ⊆ refs Beg P˘) ∧
        codom R ⊆ refs Beg Q) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) →
        (((S ∈ potid P ∧ S' ∈ potid P) ∧ (T ∈ potid Q ∧ T' ∈ potid Q)) ∧
          S ⨾ R ⨾ T = S' ⨾ R ⨾ T' → S = S' ∧ T = T') := by
  intro h
  have hP1 : swapB ∈ arrow Cls one :=
    mem_arrow_Cls_one.2 fun x y z ⟨hy, hz⟩ => (hy : y = !x).trans (hz : z = !x).symm
  have hP2 : swapB ∈ arrow one Cls := mem_arrow_one_Cls.2 fun x y z ⟨hx, hy⟩ => by
    have e : (!x) = !y := (hx : z = !x).symm.trans (hy : z = !y)
    cases x <;> cases y <;> first | rfl | exact absurd e (by decide)
  have hdc : dom swapB ⊆ codom swapB := fun x _ => ⟨!x, (by simp [swapB] : swapB (!x) x)⟩
  have hcd : codom swapB ⊆ dom swapB := fun x _ => ⟨!x, (rfl : (!x) = !x)⟩
  let E : Bool → Bool → Prop := fun _ _ => False
  have e1 : ipow swapB 0 ⨾ E ⨾ ipow swapB 0 = ipow swapB 1 ⨾ E ⨾ ipow swapB 0 := by
    funext x y
    apply propext
    constructor
    · rintro ⟨_, ⟨_, _, hE⟩, _⟩
      exact hE.elim
    · rintro ⟨_, ⟨_, _, hE⟩, _⟩
      exact hE.elim
  have key := (h swapB swapB E (ipow swapB 0) (ipow swapB 1) (ipow swapB 0) (ipow swapB 0)
    ⟨⟨⟨⟨⟨hP1, hP2⟩, fun _ ⟨_, hE⟩ => hE.elim⟩, fun _ ⟨_, hE⟩ => hE.elim⟩, hdc⟩, hcd⟩
    ⟨⟨⟨ipow_mem_potid _ 0, ipow_mem_potid _ 1⟩, ⟨ipow_mem_potid _ 0, ipow_mem_potid _ 0⟩⟩,
      e1⟩).1
  have h0 : ipow swapB 0 true true := ipow_zero_apply.2 ⟨rfl, ⟨false, Or.inl rfl⟩⟩
  rw [key, ipow_one] at h0
  have h1 : true = !true := h0
  exact absurd h1 (by decide)

/-- ✱95·38. \(\vdash\colon\ldotp \exists !\overrightarrow{B}ʻQ\cap \text{ᗡ}ʻR.\supset:T\in \text{Pot}ʻQ.\supset.R\mid T \neq R\) -/
theorem pm95_38 {Q : β → β → Prop} {R : α → β → Prop} {T : β → β → Prop} :
    (refs Beg Q ∩ codom R).Nonempty → (T ∈ pot Q → R ⨾ T ≠ R) := by
  rintro ⟨b, hb, hbR⟩ hT he
  have : b ∈ codom (R ⨾ T) := by
    rw [he]
    exact hbR
  exact beg_not_codom hb (codom_pot_sub hT (codom_comp_sub R T this))

/-- ✱95·381. \[\begin{align}&\vdash\colon\ldotp \exists !\overrightarrow{B}ʻ\breve{P}\cap \text{D}ʻR.\supset:S\in \text{Pot}ʻP.\supset.S\mid R \neq R\\ &[\text{Proof as in *95·38}]\end{align}\] -/
theorem pm95_381 {P : α → α → Prop} {R : α → β → Prop} {S : α → α → Prop} :
    (refs Beg P˘ ∩ dom R).Nonempty → (S ∈ pot P → S ⨾ R ≠ R) := by
  rintro ⟨e, he, heR⟩ hS hSR
  have : e ∈ dom (S ⨾ R) := by
    rw [hSR]
    exact heR
  exact end_not_dom he (dom_pot_sub hS (dom_comp_sub S R this))

/-- ✱95·382. \[\begin{align}\vdash\colon\ldotp \exists !\overrightarrow{B}ʻ\breve{P}&\cap \text{D}ʻR.\lor.\exists !\overrightarrow{B}ʻQ\cap \text{ᗡ}ʻR:\supset:\\ &S\in \text{Pot}ʻP.T\in \text{Pot}ʻQ.\supset.S\mid R\mid T \neq R\end{align}\] -/
theorem pm95_382 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {S : α → α → Prop} {T : β → β → Prop} :
    (refs Beg P˘ ∩ dom R).Nonempty ∨ (refs Beg Q ∩ codom R).Nonempty →
      (S ∈ pot P ∧ T ∈ pot Q → S ⨾ R ⨾ T ≠ R) := by
  rintro (⟨e, he, heR⟩ | ⟨b, hb, hbR⟩) ⟨hS, hT⟩ hSRT
  · have : e ∈ dom (S ⨾ R ⨾ T) := by
      rw [hSRT]
      exact heR
    exact end_not_dom he (dom_pot_sub hS (dom_comp_sub S R (dom_comp_sub _ T this)))
  · have : b ∈ codom (S ⨾ R ⨾ T) := by
      rw [hSRT]
      exact hbR
    exact beg_not_codom hb (codom_pot_sub hT (codom_comp_sub _ T this))

/-- ✱95·383. \[\begin{align}&\vdash\colon\ldotp \dot{\exists}!R:\text{D}ʻR\subset \overrightarrow{B}ʻ\breve{P}.\lor.\text{ᗡ}ʻR\subset \overrightarrow{B}ʻQ:\supset:\\ &S\in \text{Pot}ʻP.T\in \text{Pot}ʻQ.\supset.S\mid R\mid T \neq R \quad[\text{*95·382.*33·24.*22·621}]\end{align}\] -/
theorem pm95_383 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {S : α → α → Prop} {T : β → β → Prop} :
    rEx R ∧ (dom R ⊆ refs Beg P˘ ∨ codom R ⊆ refs Beg Q) →
      (S ∈ pot P ∧ T ∈ pot Q → S ⨾ R ⨾ T ≠ R) := by
  rintro ⟨⟨x, y, hxy⟩, h | h⟩
  · exact pm95_382 (Or.inl ⟨x, h ⟨y, hxy⟩, ⟨y, hxy⟩⟩)
  · exact pm95_382 (Or.inr ⟨y, h ⟨x, hxy⟩, ⟨x, hxy⟩⟩)

/-- ✱95·4. \[\begin{align}\vdash:M\in (P \unicode{x2217} Q)ʻR.S\in \text{Pot}ʻP.T\in \text{Pot}ʻQ.S\mid R\mid T\in &(P \unicode{x2217} Q)ʻR.\supset.\\ &S\mid M\mid T\in (P \unicode{x2217} Q)ʻR\end{align}\] -/
theorem pm95_4 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop}
    {S : α → α → Prop} {T : β → β → Prop} :
    ((M ∈ refs (anc (P ∥ Q)) R ∧ S ∈ pot P) ∧ T ∈ pot Q) ∧
      S ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R → S ⨾ M ⨾ T ∈ refs (anc (P ∥ Q)) R := by
  rintro ⟨⟨⟨hM, hS⟩, hT⟩, hSRT⟩
  obtain ⟨n, rfl⟩ := eqf_mem.1 hM
  obtain ⟨a, rfl⟩ := mem_pot_npow.1 hS
  obtain ⟨b, rfl⟩ := mem_pot_npow.1 hT
  obtain ⟨k, hk⟩ := eqf_mem.1 hSRT
  refine eqf_mem.2 ⟨n + k, ?_⟩
  have e1 : npow P (a + 1) ⨾ (npow P n ⨾ R ⨾ npow Q n) ⨾ npow Q (b + 1) =
      npow P n ⨾ (npow P (a + 1) ⨾ R ⨾ npow Q (b + 1)) ⨾ npow Q n := by
    simp only [rp_assoc]
    rw [← rp_assoc (npow P (a + 1)) (npow P n), npow_comm P (a + 1) n, rp_assoc,
      npow_comm Q n (b + 1)]
  rw [e1, hk, npow_add, npow_add, npow_comm Q n k]
  simp only [rp_assoc]

/-- ✱95·41. \[\begin{align}&\vdash\colon\ldotp P\in \text{Cls}\rightarrow 1.Q\in 1\rightarrow \text{Cls}.\text{D}ʻP\subset \text{ᗡ}ʻP.\text{ᗡ}ʻQ\subset \text{D}ʻQ.\supset:\\ & S,\,S'\in \text{Potid}ʻP.T,\,T'\in \text{Potid}ʻQ.\supset.\breve{S}\mid S\mid S'\mid N\mid T'\mid T\mid \breve{T} = S'\mid N\mid T'\\ &[\text{*92·15·151}]\end{align}\] -/
theorem pm95_41 {P : α → α → Prop} {Q : β → β → Prop} {S S' : α → α → Prop}
    {T T' : β → β → Prop} {N : α → β → Prop} :
    ((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q →
      ((S ∈ potid P ∧ S' ∈ potid P) ∧ (T ∈ potid Q ∧ T' ∈ potid Q) →
        S˘ ⨾ S ⨾ S' ⨾ N ⨾ T' ⨾ T ⨾ T˘ = S' ⨾ N ⨾ T') := by
  rintro ⟨⟨⟨hP, hQ⟩, hd⟩, hc⟩ ⟨⟨hS, hS'⟩, ⟨hT, hT'⟩⟩
  have hdom : dom (S' ⨾ N ⨾ T') ⊆ fld P := by
    obtain ⟨n, rfl⟩ := mem_potid'.1 hS'
    exact (dom_comp_sub _ _).trans ((dom_comp_sub _ _).trans fun x ⟨_, h⟩ => (fld_of_ipow h).1)
  have hcod : codom (S' ⨾ N ⨾ T') ⊆ fld Q := by
    obtain ⟨n, rfl⟩ := mem_potid'.1 hT'
    exact (codom_comp_sub _ _).trans fun y ⟨_, h⟩ => (fld_of_ipow h).2
  calc S˘ ⨾ S ⨾ S' ⨾ N ⨾ T' ⨾ T ⨾ T˘ = S˘ ⨾ (S ⨾ (S' ⨾ N ⨾ T')) ⨾ T ⨾ T˘ := by
        simp only [rp_assoc]
    _ = (S' ⨾ N ⨾ T') ⨾ T ⨾ T˘ := by
        rw [cnv_potid_cancel (mem_arrow_Cls_one.1 hP) hd hS hdom]
    _ = S' ⨾ N ⨾ T' := potid_cnv_cancel (mem_arrow_one_Cls.1 hQ) hc hT hcod

private theorem sandwich_dom_codom {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    (hd : dom R ⊆ fld P) (hc : codom R ⊆ fld Q) (n : ℕ) :
    dom (npow P n ⨾ R ⨾ npow Q n) ⊆ fld P ∧ codom (npow P n ⨾ R ⨾ npow Q n) ⊆ fld Q := by
  refine ⟨(dom_comp_sub _ _).trans (dom_npow_comp_sub hd (dom_sub_fld P) n), ?_⟩
  rw [rp_assoc]
  exact (codom_comp_sub _ _).trans (codom_comp_npow_sub hc (codom_sub_fld Q) n)

/-- ✱95·411. \[\begin{align}&\vdash\colon\ldotp \text{Hp*95·41}.\supset:\\ & S\in \text{Potid}ʻP.T\in \text{Potid}ʻQ.M\in (P \unicode{x2217} Q)ʻR.\supset.M = \breve{S}\mid S\mid M\mid T\mid \breve{T}\\ &[\text{*95·41·22}]\end{align}\]

**Status.** proved (corrected): with only Hp✱95·41 the proposition is false, since
nothing relates `R` to `C'P` and `C'Q`: for `M = R`, `S = I ↾ C'P`, `T = I ↾ C'Q` the right side
is `R` cut down to `C'P` and `C'Q` (`pm95_411_printed_false`: `P` the universal relation on
`Unit`, `Q` the successor relation on the numbers `≥ 1`, `R` relating `()` to `0` and to `1`).
PM's proof cites ✱95·22, whose hypothesis `D'R ⊂ C'P . ᗡ'R ⊂ C'Q` is added (as a conjunct after
Hp✱95·41). ✱95·42–·45, which depend on ✱95·411, carry the same added hypothesis; under
Hp✱95·46 it follows from `D'R ⊂ B⃗'P̆ . ᗡ'R ⊂ B⃗'Q`. -/
theorem pm95_411 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop}
    {S : α → α → Prop} {T : β → β → Prop} :
    (((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
      (dom R ⊆ fld P ∧ codom R ⊆ fld Q) →
      ((S ∈ potid P ∧ T ∈ potid Q) ∧ M ∈ refs (anc (P ∥ Q)) R → M = S˘ ⨾ S ⨾ M ⨾ T ⨾ T˘) := by
  rintro ⟨⟨⟨⟨hP, hQ⟩, hd⟩, hc⟩, hdR, hcR⟩ ⟨⟨hS, hT⟩, hM⟩
  obtain ⟨n, hn⟩ := eqf_mem.1 hM
  have hMd : dom M ⊆ fld P := by rw [hn]; exact (sandwich_dom_codom hdR hcR n).1
  have hMc : codom M ⊆ fld Q := by rw [hn]; exact (sandwich_dom_codom hdR hcR n).2
  rw [rp_assoc S˘ S M, cnv_potid_cancel (mem_arrow_Cls_one.1 hP) hd hS hMd,
    potid_cnv_cancel (mem_arrow_one_Cls.1 hQ) hc hT hMc]

/-- ✱95·42. \(\vdash\colon\ldotp \text{Hp*95·41}.\supset:M\in (P \unicode{x2217} Q)ʻR - \iotaʻR.\supset.\breve{P}\mid M\mid \breve{Q}\in (P \unicode{x2217} Q)ʻR\)

**Status.** proved (corrected): Hp✱95·41 is taken with the hypothesis
`D'R ⊂ C'P . ᗡ'R ⊂ C'Q` of ✱95·22 added (see ✱95·411). As printed it is false: in the
counterexample of ✱95·411, `M = P|R|Q` is a member of `(P∗Q)'R − ι'R`, but `P̆|M|Q̆` relates `()`
to `1` only and is not a member of `(P∗Q)'R` (`pm95_42_printed_false`). -/
theorem pm95_42 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop} :
    (((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
      (dom R ⊆ fld P ∧ codom R ⊆ fld Q) →
      (M ∈ refs (anc (P ∥ Q)) R \ ι R → P˘ ⨾ M ⨾ Q˘ ∈ refs (anc (P ∥ Q)) R) := by
  rintro ⟨⟨⟨⟨hP, hQ⟩, hd⟩, hc⟩, hdR, hcR⟩ ⟨hM, hMR⟩
  obtain ⟨k, rfl⟩ := eqf_mem.1 hM
  cases k with
  | zero => exact absurd (npow_sandwich_zero P Q R) hMR
  | succ j =>
    obtain ⟨hWd, hWc⟩ := sandwich_dom_codom hdR hcR j
    have hPp : P ∈ potid P := pot_sub_potid P (self_mem_pot P)
    have hQp : Q ∈ potid Q := pot_sub_potid Q (self_mem_pot Q)
    rw [npow_sandwich_succ, rp_assoc P, cnv_potid_cancel (mem_arrow_Cls_one.1 hP) hd hPp
      ((dom_comp_sub _ _).trans hWd), potid_cnv_cancel (mem_arrow_one_Cls.1 hQ) hc hQp hWc]
    exact npow_mem_eqf P Q R j

private theorem potid_comm_self {P S : α → α → Prop} (h : S ∈ potid P) : S ⨾ P = P ⨾ S := by
  obtain ⟨a, rfl⟩ := mem_potid'.1 h
  rw [← ipow_succ, ipow_succ']

private theorem potid_comm {P S S' : α → α → Prop} (h : S ∈ potid P) (h' : S' ∈ potid P) :
    S ⨾ S' = S' ⨾ S := by
  obtain ⟨a, rfl⟩ := mem_potid'.1 h
  obtain ⟨b, rfl⟩ := mem_potid'.1 h'
  exact ipow_comm P a b

private theorem comm_sandwich {S P : α → α → Prop} {Q T : β → β → Prop} (W : α → β → Prop)
    (h1 : S ⨾ P = P ⨾ S) (h2 : Q ⨾ T = T ⨾ Q) : S ⨾ (P ⨾ W ⨾ Q) ⨾ T = P ⨾ S ⨾ W ⨾ T ⨾ Q := by
  simp only [rp_assoc]
  rw [← rp_assoc S P, h1, rp_assoc, h2]

private theorem assoc_sandwich (S S' : α → α → Prop) (R : α → β → Prop) (T T' : β → β → Prop) :
    S ⨾ (S' ⨾ R ⨾ T') ⨾ T = S ⨾ S' ⨾ R ⨾ T' ⨾ T := by
  simp only [rp_assoc]

private theorem assoc_sandwich2 (P S S' : α → α → Prop) (R : α → β → Prop) (T T' Q : β → β → Prop) :
    P ⨾ S ⨾ (S' ⨾ R ⨾ T') ⨾ T ⨾ Q = P ⨾ (S ⨾ S') ⨾ R ⨾ (T' ⨾ T) ⨾ Q := by
  simp only [rp_assoc]

private theorem assoc_five (P S : α → α → Prop) (R : α → β → Prop) (T Q : β → β → Prop) :
    P ⨾ S ⨾ R ⨾ T ⨾ Q = (P ⨾ S) ⨾ R ⨾ (T ⨾ Q) := by
  simp only [rp_assoc]

private theorem assoc_seven (P S : α → α → Prop) (R : α → β → Prop) (T Q : β → β → Prop) :
    P˘ ⨾ (P ⨾ S ⨾ R ⨾ T ⨾ Q) ⨾ Q˘ = P˘ ⨾ P ⨾ S ⨾ R ⨾ T ⨾ Q ⨾ Q˘ := by
  simp only [rp_assoc]

private theorem comm_sandwich2 {S S' : α → α → Prop} {T T' : β → β → Prop} (R : α → β → Prop)
    (h1 : S' ⨾ S = S ⨾ S') (h2 : T ⨾ T' = T' ⨾ T) :
    S' ⨾ (S ⨾ R ⨾ T) ⨾ T' = S ⨾ S' ⨾ R ⨾ T' ⨾ T := by
  simp only [rp_assoc]
  rw [← rp_assoc S' S, h1, rp_assoc, h2]

/-- ✱95·43. \[\begin{align}\vdash\colon\ldotp \text{Hp*95·41}.\text{Hp*95·382}.&\supset:S\in \text{Potid}ʻP.T\in \text{Potid}ʻQ.\\ & P\mid S\mid R\mid T\mid Q\in (P \unicode{x2217} Q)ʻR.\supset.S\mid R\mid T\in (P \unicode{x2217} Q)ʻR\end{align}\]

**Status.** proved (corrected): Hp✱95·41 is taken with the hypothesis
`D'R ⊂ C'P . ᗡ'R ⊂ C'Q` of ✱95·22 added (see ✱95·411). As printed it is false: in the
counterexample of ✱95·411 (where `1 ∈ B⃗'Q ∩ ᗡ'R`, so Hp✱95·382 holds), with `S = I ↾ C'P`,
`T = I ↾ C'Q`, `P|S|R|T|Q = P|R|Q` is a member of `(P∗Q)'R` but `S|R|T`, which relates `()` to `1`
only, is not (`pm95_43_printed_false`). -/
theorem pm95_43 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {S : α → α → Prop} {T : β → β → Prop} :
    ((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
      (dom R ⊆ fld P ∧ codom R ⊆ fld Q)) ∧
      ((refs Beg P˘ ∩ dom R).Nonempty ∨ (refs Beg Q ∩ codom R).Nonempty) →
      ((S ∈ potid P ∧ T ∈ potid Q) ∧ P ⨾ S ⨾ R ⨾ T ⨾ Q ∈ refs (anc (P ∥ Q)) R →
        S ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R) := by
  rintro ⟨h41, h382⟩ ⟨⟨hS, hT⟩, hM⟩
  have hPS : P ⨾ S ∈ pot P := by
    obtain ⟨a, rfl⟩ := mem_potid'.1 hS
    rw [← ipow_succ']
    exact ipow_succ_mem_pot P a
  have hTQ : T ⨾ Q ∈ pot Q := by
    obtain ⟨b, rfl⟩ := mem_potid'.1 hT
    rw [← ipow_succ]
    exact ipow_succ_mem_pot Q b
  have hne : P ⨾ S ⨾ R ⨾ T ⨾ Q ≠ R := by
    rw [assoc_five]
    exact pm95_382 h382 ⟨hPS, hTQ⟩
  have h42 := pm95_42 h41 ⟨hM, hne⟩
  rw [assoc_seven, pm95_41 h41.1 ⟨⟨pot_sub_potid P (self_mem_pot P), hS⟩,
    ⟨pot_sub_potid Q (self_mem_pot Q), hT⟩⟩] at h42
  exact h42

/-- ✱95·431. \[\begin{align}\vdash:\text{Hp*95·43}.S\in &\text{Potid}ʻP.T\in \text{Potid}ʻQ.M\in (P \unicode{x2217} Q)ʻR.\\ & P\mid S\mid M\mid T\mid Q\in (P \unicode{x2217} Q)ʻR.\supset.S\mid M\mid T\in (P \unicode{x2217} Q)ʻR\end{align}\]

**Status.** proved (corrected): Hp✱95·43 is taken with the hypothesis
`D'R ⊂ C'P . ᗡ'R ⊂ C'Q` added to Hp✱95·41 (see ✱95·411, ✱95·43). As printed it is false: take
`M = R` in the counterexample of ✱95·43 (`pm95_431_printed_false`). -/
theorem pm95_431 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop}
    {S : α → α → Prop} {T : β → β → Prop} :
    ((((((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
      (dom R ⊆ fld P ∧ codom R ⊆ fld Q)) ∧
      ((refs Beg P˘ ∩ dom R).Nonempty ∨ (refs Beg Q ∩ codom R).Nonempty)) ∧ S ∈ potid P) ∧
      T ∈ potid Q) ∧ M ∈ refs (anc (P ∥ Q)) R) ∧ P ⨾ S ⨾ M ⨾ T ⨾ Q ∈ refs (anc (P ∥ Q)) R →
      S ⨾ M ⨾ T ∈ refs (anc (P ∥ Q)) R := by
  rintro ⟨⟨⟨⟨h43, hS⟩, hT⟩, hM⟩, hPM⟩
  obtain ⟨S', T', ⟨hS', hT'⟩, rfl⟩ := pm95_22 ⟨h43.1.2, hM⟩
  have hSS : S ⨾ S' ∈ potid P := by
    obtain ⟨a, rfl⟩ := mem_potid'.1 hS
    obtain ⟨b, rfl⟩ := mem_potid'.1 hS'
    rw [ipow_mul]
    exact ipow_mem_potid _ _
  have hTT : T' ⨾ T ∈ potid Q := by
    obtain ⟨a, rfl⟩ := mem_potid'.1 hT'
    obtain ⟨b, rfl⟩ := mem_potid'.1 hT
    rw [ipow_mul]
    exact ipow_mem_potid _ _
  rw [assoc_sandwich2] at hPM
  rw [assoc_sandwich, rp_assoc (S ⨾ S' ⨾ R) T' T]
  exact pm95_43 h43 ⟨⟨hSS, hTT⟩, hPM⟩

/-- ✱95·44. \[\begin{align}\vdash\colon\ldotp \text{Hp*95·43}.& S\in \text{Potid}ʻP.T\in \text{Potid}ʻQ.\supset:\\ & M\in (P \unicode{x2217} Q)ʻR.S\mid M\mid T\in (P \unicode{x2217} Q)ʻR.\supset.S\mid R\mid T\in (P \unicode{x2217} Q)ʻR\end{align}\]

**Status.** proved (corrected): Hp✱95·43 is taken with the hypothesis
`D'R ⊂ C'P . ᗡ'R ⊂ C'Q` added to Hp✱95·41 (see ✱95·411, ✱95·43). As printed it is false: take
`M = P|R|Q`, `S = I ↾ C'P`, `T = I ↾ C'Q` in the counterexample of ✱95·43; then `S|M|T = M`
(`pm95_44_printed_false`). -/
theorem pm95_44 {P : α → α → Prop} {Q : β → β → Prop} {R M : α → β → Prop}
    {S : α → α → Prop} {T : β → β → Prop} :
    ((((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
      (dom R ⊆ fld P ∧ codom R ⊆ fld Q)) ∧
      ((refs Beg P˘ ∩ dom R).Nonempty ∨ (refs Beg Q ∩ codom R).Nonempty)) ∧ S ∈ potid P) ∧
      T ∈ potid Q →
      (M ∈ refs (anc (P ∥ Q)) R ∧ S ⨾ M ⨾ T ∈ refs (anc (P ∥ Q)) R →
        S ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R) := by
  rintro ⟨⟨h43, hS⟩, hT⟩ ⟨hM, hSMT⟩
  have hSP : S ⨾ P = P ⨾ S := potid_comm_self hS
  have hQT : Q ⨾ T = T ⨾ Q := (potid_comm_self hT).symm
  obtain ⟨n, rfl⟩ := eqf_mem.1 hM
  induction n with
  | zero => rwa [npow_sandwich_zero] at hSMT
  | succ n ih =>
    refine ih (npow_mem_eqf P Q R n) ?_
    rw [npow_sandwich_succ, comm_sandwich _ hSP hQT] at hSMT
    exact pm95_431 ⟨⟨⟨⟨h43, hS⟩, hT⟩, npow_mem_eqf P Q R n⟩, hSMT⟩

/-- ✱95·45. \[\begin{align}&\vdash\colon\ldotp \text{Hp*95·43}.S,\,S'\in \text{Potid}ʻP.T,\,T'\in \text{Potid}ʻQ.\\ & S\mid S'\mid R\mid T'\mid T\in (P \unicode{x2217} Q)ʻR.\supset:S\mid R\mid T\in (P \unicode{x2217} Q)ʻR.\equiv.S'\mid R\mid T'\in (P \unicode{x2217} Q)ʻR\end{align}\]

**Status.** proved (corrected): Hp✱95·43 is taken with the hypothesis
`D'R ⊂ C'P . ᗡ'R ⊂ C'Q` added to Hp✱95·41 (see ✱95·411, ✱95·43). As printed it is false: take
`S = S' = I ↾ C'P`, `T = I ↾ C'Q`, `T' = Q` in the counterexample of ✱95·43; then
`S|S'|R|T'|T = R|Q` and `S'|R|T' = R|Q` are members of `(P∗Q)'R`, `S|R|T` is not
(`pm95_45_printed_false`). -/
theorem pm95_45 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {S S' : α → α → Prop} {T T' : β → β → Prop} :
    (((((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
      (dom R ⊆ fld P ∧ codom R ⊆ fld Q)) ∧
      ((refs Beg P˘ ∩ dom R).Nonempty ∨ (refs Beg Q ∩ codom R).Nonempty)) ∧
      (S ∈ potid P ∧ S' ∈ potid P)) ∧ (T ∈ potid Q ∧ T' ∈ potid Q)) ∧
      S ⨾ S' ⨾ R ⨾ T' ⨾ T ∈ refs (anc (P ∥ Q)) R →
      (S ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R ↔ S' ⨾ R ⨾ T' ∈ refs (anc (P ∥ Q)) R) := by
  rintro ⟨⟨⟨h43, hS, hS'⟩, hT, hT'⟩, h⟩
  constructor
  · intro hSRT
    refine pm95_44 ⟨⟨h43, hS'⟩, hT'⟩ ⟨hSRT, ?_⟩
    rw [comm_sandwich2 R (potid_comm hS' hS) (potid_comm hT hT')]
    exact h
  · intro hS'RT'
    refine pm95_44 ⟨⟨h43, hS⟩, hT⟩ ⟨hS'RT', ?_⟩
    rw [assoc_sandwich]
    exact h

/-! Counterexample for the printed forms of ✱95·411–·45: `P` the universal relation on `Unit`,
`Q` the successor relation on the numbers `≥ 1`, `R` relating `()` to `0` and to `1`; `0` lies
outside `C'Q`, so `D'R ⊂ C'P . ᗡ'R ⊂ C'Q` fails. -/

private def cxP : Unit → Unit → Prop := fun _ _ => True

private def cxQ : ℕ → ℕ → Prop := fun x y => 1 ≤ x ∧ y = x + 1

private def cxR : Unit → ℕ → Prop := fun _ y => y = 0 ∨ y = 1

private theorem cxP_npow (n : ℕ) (u v : Unit) : npow cxP n u v := by
  induction n generalizing v with
  | zero => exact Subsingleton.elim u v
  | succ n ih => exact ⟨(), ih (), trivial⟩

private theorem cxP_comp {γ : Type w} (n : ℕ) (Z : Unit → γ → Prop) : npow cxP n ⨾ Z = Z := by
  funext u y
  apply propext
  constructor
  · rintro ⟨v, -, h⟩
    rwa [Subsingleton.elim u v]
  · intro h
    exact ⟨u, cxP_npow n u u, h⟩

private theorem cxP_comp1 {γ : Type w} (Z : Unit → γ → Prop) : cxP ⨾ Z = Z := by
  have := cxP_comp 1 Z
  rwa [npow_one] at this

private theorem cxP_ipow_comp {γ : Type w} (Z : Unit → γ → Prop) : ipow cxP 0 ⨾ Z = Z := by
  rw [ipow_comp_eq (fun u _ => ⟨u, Or.inl trivial⟩) 0, cxP_comp]

private theorem cx_mem {Z : Unit → ℕ → Prop} :
    Z ∈ refs (anc (cxP ∥ cxQ)) cxR ↔ ∃ n, Z = cxR ⨾ npow cxQ n := by
  rw [eqf_mem]
  simp only [cxP_comp]

private theorem cxQ_npow {n x y : ℕ} (h : npow cxQ n x y) : y = x + n := by
  induction n generalizing y with
  | zero => exact (h : x = y).symm
  | succ n ih =>
    obtain ⟨c, hc, hcy⟩ := h
    have h1 := ih hc
    have h2 : y = c + 1 := hcy.2
    omega

private theorem cxQ_npow_succ_ge {n x y : ℕ} (h : npow cxQ (n + 1) x y) : 1 ≤ x := by
  obtain ⟨a, hxa, -⟩ := npow_succ_iff.1 h
  exact hxa.1

private theorem cx_zero_not_fld : (0 : ℕ) ∉ fld cxQ := by
  rintro ⟨y, h | h⟩
  · exact absurd h.1 (by omega)
  · have : (0 : ℕ) = y + 1 := h.2
    omega

private theorem cx_not_mem {Z : Unit → ℕ → Prop} (h1 : Z () 1) (h0 : ¬ Z () 0) :
    Z ∉ refs (anc (cxP ∥ cxQ)) cxR := by
  intro hZ
  obtain ⟨n, rfl⟩ := cx_mem.1 hZ
  cases n with
  | zero => exact h0 ⟨0, Or.inl rfl, rfl⟩
  | succ n =>
    obtain ⟨b, -, hb1⟩ := h1
    have e := cxQ_npow hb1
    have g := cxQ_npow_succ_ge hb1
    omega

private theorem cx_hp41 :
    ((cxP ∈ arrow Cls one ∧ cxQ ∈ arrow one Cls) ∧ dom cxP ⊆ codom cxP) ∧
      codom cxQ ⊆ dom cxQ := by
  refine ⟨⟨⟨mem_arrow_Cls_one.2 fun _ y z _ => Subsingleton.elim y z,
    mem_arrow_one_Cls.2 ?_⟩, fun x _ => ⟨x, trivial⟩⟩, ?_⟩
  · rintro x y z ⟨⟨-, hx⟩, ⟨-, hy⟩⟩
    omega
  · rintro y ⟨x, -, rfl⟩
    exact ⟨x + 1 + 1, by omega, rfl⟩

private theorem cx_beg1 : Beg 1 cxQ := by
  refine ⟨⟨2, le_refl 1, rfl⟩, ?_⟩
  rintro ⟨x, hx, h⟩
  omega

private theorem cx_hp382 :
    (refs Beg cxP˘ ∩ dom cxR).Nonempty ∨ (refs Beg cxQ ∩ codom cxR).Nonempty :=
  Or.inr ⟨1, cx_beg1, (), Or.inr rfl⟩

private theorem cxRQ_mem : cxR ⨾ cxQ ∈ refs (anc (cxP ∥ cxQ)) cxR :=
  cx_mem.2 ⟨1, by rw [npow_one]⟩

private theorem cxZ0_not_mem : cxR ⨾ ipow cxQ 0 ∉ refs (anc (cxP ∥ cxQ)) cxR := by
  refine cx_not_mem ⟨1, Or.inr rfl, ipow_zero_apply.2 ⟨rfl, ⟨2, Or.inl ⟨le_refl 1, rfl⟩⟩⟩⟩ ?_
  rintro ⟨b, -, hb⟩
  exact cx_zero_not_fld (fld_of_ipow hb).2

private theorem cxQ_ipow0 : ipow cxQ 0 ⨾ cxQ = cxQ := (ipow_succ cxQ 0).symm.trans (ipow_one cxQ)

private theorem cxQ_comp_ipow0 : cxQ ⨾ ipow cxQ 0 = cxQ := by
  rw [comp_ipow_eq (codom_sub_fld cxQ) 0, comp_npow_zero]

private theorem cx_PSRTQ : cxP ⨾ ipow cxP 0 ⨾ cxR ⨾ ipow cxQ 0 ⨾ cxQ = cxR ⨾ cxQ := by
  rw [rp_assoc (cxP ⨾ ipow cxP 0 ⨾ cxR) (ipow cxQ 0) cxQ, cxQ_ipow0, rp_assoc cxP,
    cxP_ipow_comp, cxP_comp1]

private theorem cx_SRT : ipow cxP 0 ⨾ cxR ⨾ ipow cxQ 0 = cxR ⨾ ipow cxQ 0 := by
  rw [cxP_ipow_comp]

theorem pm95_411_printed_false :
    ¬ ∀ (P : Unit → Unit → Prop) (Q : ℕ → ℕ → Prop) (R M : Unit → ℕ → Prop)
      (S : Unit → Unit → Prop) (T : ℕ → ℕ → Prop),
      (((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) →
        ((S ∈ potid P ∧ T ∈ potid Q) ∧ M ∈ refs (anc (P ∥ Q)) R →
          M = S˘ ⨾ S ⨾ M ⨾ T ⨾ T˘) := by
  intro h
  have e := h cxP cxQ cxR cxR (ipow cxP 0) (ipow cxQ 0) cx_hp41
    ⟨⟨ipow_mem_potid _ 0, ipow_mem_potid _ 0⟩, pm95_13⟩
  have h0 : cxR () 0 := Or.inl rfl
  rw [e] at h0
  obtain ⟨w, -, hw⟩ := h0
  exact cx_zero_not_fld (fld_of_ipow hw).1

theorem pm95_42_printed_false :
    ¬ ∀ (P : Unit → Unit → Prop) (Q : ℕ → ℕ → Prop) (R M : Unit → ℕ → Prop),
      (((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) →
        (M ∈ refs (anc (P ∥ Q)) R \ ι R → P˘ ⨾ M ⨾ Q˘ ∈ refs (anc (P ∥ Q)) R) := by
  intro h
  have hne : cxR ⨾ cxQ ∉ ι cxR := by
    intro e
    have e' : cxR ⨾ cxQ = cxR := e
    have h0 : cxR () 0 := Or.inl rfl
    rw [← e'] at h0
    obtain ⟨b, -, hb⟩ := h0
    have : (0 : ℕ) = b + 1 := hb.2
    omega
  refine cx_not_mem ?_ ?_ (h cxP cxQ cxR (cxR ⨾ cxQ) cx_hp41 ⟨cxRQ_mem, hne⟩)
  · exact ⟨2, ⟨(), trivial, 1, Or.inr rfl, le_refl 1, rfl⟩, le_refl 1, rfl⟩
  · rintro ⟨w, -, hw⟩
    exact absurd hw.1 (by omega)

theorem pm95_43_printed_false :
    ¬ ∀ (P : Unit → Unit → Prop) (Q : ℕ → ℕ → Prop) (R : Unit → ℕ → Prop)
      (S : Unit → Unit → Prop) (T : ℕ → ℕ → Prop),
      ((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
        ((refs Beg P˘ ∩ dom R).Nonempty ∨ (refs Beg Q ∩ codom R).Nonempty)) →
        ((S ∈ potid P ∧ T ∈ potid Q) ∧ P ⨾ S ⨾ R ⨾ T ⨾ Q ∈ refs (anc (P ∥ Q)) R →
          S ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R) := by
  intro h
  have := h cxP cxQ cxR (ipow cxP 0) (ipow cxQ 0) ⟨cx_hp41, cx_hp382⟩
    ⟨⟨ipow_mem_potid _ 0, ipow_mem_potid _ 0⟩, by rw [cx_PSRTQ]; exact cxRQ_mem⟩
  rw [cx_SRT] at this
  exact cxZ0_not_mem this

theorem pm95_431_printed_false :
    ¬ ∀ (P : Unit → Unit → Prop) (Q : ℕ → ℕ → Prop) (R M : Unit → ℕ → Prop)
      (S : Unit → Unit → Prop) (T : ℕ → ℕ → Prop),
      (((((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
        ((refs Beg P˘ ∩ dom R).Nonempty ∨ (refs Beg Q ∩ codom R).Nonempty)) ∧ S ∈ potid P) ∧
        T ∈ potid Q) ∧ M ∈ refs (anc (P ∥ Q)) R) ∧ P ⨾ S ⨾ M ⨾ T ⨾ Q ∈ refs (anc (P ∥ Q)) R →
        S ⨾ M ⨾ T ∈ refs (anc (P ∥ Q)) R := by
  intro h
  have := h cxP cxQ cxR cxR (ipow cxP 0) (ipow cxQ 0)
    ⟨⟨⟨⟨⟨cx_hp41, cx_hp382⟩, ipow_mem_potid _ 0⟩, ipow_mem_potid _ 0⟩, pm95_13⟩,
      by rw [cx_PSRTQ]; exact cxRQ_mem⟩
  rw [cx_SRT] at this
  exact cxZ0_not_mem this

theorem pm95_44_printed_false :
    ¬ ∀ (P : Unit → Unit → Prop) (Q : ℕ → ℕ → Prop) (R M : Unit → ℕ → Prop)
      (S : Unit → Unit → Prop) (T : ℕ → ℕ → Prop),
      ((((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
        ((refs Beg P˘ ∩ dom R).Nonempty ∨ (refs Beg Q ∩ codom R).Nonempty)) ∧ S ∈ potid P) ∧
        T ∈ potid Q) →
        (M ∈ refs (anc (P ∥ Q)) R ∧ S ⨾ M ⨾ T ∈ refs (anc (P ∥ Q)) R →
          S ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R) := by
  intro h
  have hSMT : ipow cxP 0 ⨾ (cxR ⨾ cxQ) ⨾ ipow cxQ 0 = cxR ⨾ cxQ := by
    rw [cxP_ipow_comp, rp_assoc, cxQ_comp_ipow0]
  have := h cxP cxQ cxR (cxR ⨾ cxQ) (ipow cxP 0) (ipow cxQ 0)
    ⟨⟨⟨cx_hp41, cx_hp382⟩, ipow_mem_potid _ 0⟩, ipow_mem_potid _ 0⟩
    ⟨cxRQ_mem, by rw [hSMT]; exact cxRQ_mem⟩
  rw [cx_SRT] at this
  exact cxZ0_not_mem this

theorem pm95_45_printed_false :
    ¬ ∀ (P : Unit → Unit → Prop) (Q : ℕ → ℕ → Prop) (R : Unit → ℕ → Prop)
      (S S' : Unit → Unit → Prop) (T T' : ℕ → ℕ → Prop),
      ((((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
        ((refs Beg P˘ ∩ dom R).Nonempty ∨ (refs Beg Q ∩ codom R).Nonempty)) ∧
        (S ∈ potid P ∧ S' ∈ potid P)) ∧ (T ∈ potid Q ∧ T' ∈ potid Q)) ∧
        S ⨾ S' ⨾ R ⨾ T' ⨾ T ∈ refs (anc (P ∥ Q)) R →
        (S ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R ↔ S' ⨾ R ⨾ T' ∈ refs (anc (P ∥ Q)) R) := by
  intro h
  have e1 : ipow cxP 0 ⨾ ipow cxP 0 ⨾ cxR ⨾ cxQ ⨾ ipow cxQ 0 = cxR ⨾ cxQ := by
    rw [rp_assoc (ipow cxP 0 ⨾ ipow cxP 0 ⨾ cxR) cxQ, cxQ_comp_ipow0, rp_assoc,
      cxP_ipow_comp, cxP_ipow_comp]
  have e2 : ipow cxP 0 ⨾ cxR ⨾ cxQ = cxR ⨾ cxQ := by rw [cxP_ipow_comp]
  have hQ : cxQ ∈ potid cxQ := pot_sub_potid cxQ (self_mem_pot cxQ)
  have := h cxP cxQ cxR (ipow cxP 0) (ipow cxP 0) (ipow cxQ 0) cxQ
    ⟨⟨⟨⟨cx_hp41, cx_hp382⟩, ⟨ipow_mem_potid _ 0, ipow_mem_potid _ 0⟩⟩,
      ⟨ipow_mem_potid _ 0, hQ⟩⟩, by rw [e1]; exact cxRQ_mem⟩
  rw [cx_SRT, e2] at this
  exact cxZ0_not_mem (this.2 cxRQ_mem)

/-- ✱95·46. \[\begin{align}\vdash\colon\ldotp \text{Hp}*95·41.\dot{\exists}!R.\text{D}ʻR\subset \overrightarrow{B}ʻ\breve{P}.\text{ᗡ}ʻ&R\subset \overrightarrow{B}ʻ\breve{Q}.\supset:\\ &T\in \text{Pot}ʻQ.\supset.R\mid T{\sim}\in (P \unicode{x2217} Q)ʻR\end{align}\]

**Status.** proved (reading): the e-text prints `ᗡ'R ⊂ B⃗'Q̆`, read `ᗡ'R ⊂ B⃗'Q`. As
printed the hypothesis is contradictory (Hp✱95·41 has `ᗡ'Q ⊂ D'Q`, so `B⃗'Q̆ = Λ`, while `∃̇!R`);
PM's proof uses ✱95·38, whose hypothesis `∃!B⃗'Q ∩ ᗡ'R` follows only with `B⃗'Q`, and ✱95·52
applies ✱95·511 under `ᗡ'R ⊂ B⃗'Q`. -/
theorem pm95_46 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} {T : β → β → Prop} :
    (((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
      rEx R) ∧ dom R ⊆ refs Beg P˘) ∧ codom R ⊆ refs Beg Q →
      (T ∈ pot Q → R ⨾ T ∉ refs (anc (P ∥ Q)) R) := by
  rintro ⟨⟨⟨⟨-, hc⟩, x, y, hxy⟩, hdR⟩, hcR⟩ hT hRT
  obtain ⟨k, hk⟩ := eqf_mem.1 hRT
  cases k with
  | zero =>
    rw [npow_sandwich_zero] at hk
    exact pm95_38 ⟨y, hcR ⟨x, hxy⟩, ⟨x, hxy⟩⟩ hT hk
  | succ j =>
    obtain ⟨m, rfl⟩ := mem_pot_npow.1 hT
    obtain ⟨z, hz⟩ := npow_fwd hc (m + 1) y (beg_dom (hcR ⟨x, hxy⟩))
    have h1 : (R ⨾ npow Q (m + 1)) x z := ⟨y, hxy, hz⟩
    rw [hk] at h1
    have hxP : x ∈ dom P :=
      dom_npow_succ_sub P j ((dom_comp_sub _ _) ((dom_comp_sub _ _) ⟨z, h1⟩))
    exact end_not_dom (hdR ⟨y, hxy⟩) hxP

/-- Under the hypothesis of ✱95·46, `S | R | T ∈ (P∗Q)'R` forces `S`, `T` to be the same power. -/
private theorem eqf_exponents {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    (hP : ∀ x y z, P x y ∧ P x z → y = z) (hQ : ∀ x y z, Q x z ∧ Q y z → x = y)
    (hd : dom P ⊆ codom P) (hc : codom Q ⊆ dom Q) (hR : rEx R) (hdR : dom R ⊆ refs Beg P˘)
    (hcR : codom R ⊆ refs Beg Q) {a b : ℕ}
    (h : ipow P a ⨾ R ⨾ ipow Q b ∈ refs (anc (P ∥ Q)) R) : a = b := by
  obtain ⟨x, y, hxy⟩ := hR
  have hx : x ∈ codom P := end_codom (hdR ⟨y, hxy⟩)
  have hy : y ∈ dom Q := beg_dom (hcR ⟨x, hxy⟩)
  obtain ⟨w, hw⟩ := npow_bwd hd a x hx
  obtain ⟨z, hz⟩ := npow_fwd hc b y hy
  have h1 : (ipow P a ⨾ R ⨾ ipow Q b) w z :=
    ⟨y, ⟨x, ipow_of_npow_right hw (codom_sub_fld P hx), hxy⟩, ipow_apply.2 ⟨dom_sub_fld Q hy, hz⟩⟩
  obtain ⟨k, hk⟩ := eqf_mem.1 h
  rw [hk] at h1
  obtain ⟨y', ⟨x', hwx', hx'y'⟩, hy'z⟩ := h1
  have e1 := end_npow_unique hP a k w x x' (hdR ⟨y, hxy⟩) (hdR ⟨y', hx'y'⟩) hw hwx'
  have e2 := beg_npow_unique hQ b k y y' z (hcR ⟨x, hxy⟩) (hcR ⟨x', hx'y'⟩) hz hy'z
  rw [e1, e2]

/-- ✱95·47. \[\begin{align}\vdash:\text{Hp*95·46}.S\in \text{Potid}ʻP.T,&T'\in \text{Potid}ʻQ.\\ & S\mid R\mid T,S\mid R\mid T'\in (P \unicode{x2217} Q)ʻR.\supset.T=T'\end{align}\]

**Status.** proved (reading): Hp✱95·46 is read as in ✱95·46 (`ᗡ'R ⊂ B⃗'Q` for the
printed `B⃗'Q̆`, which would make the hypothesis contradictory). -/
theorem pm95_47 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {S : α → α → Prop} {T T' : β → β → Prop} :
    ((((((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
      rEx R) ∧ dom R ⊆ refs Beg P˘) ∧ codom R ⊆ refs Beg Q) ∧ S ∈ potid P) ∧
      (T ∈ potid Q ∧ T' ∈ potid Q)) ∧
      (S ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R ∧ S ⨾ R ⨾ T' ∈ refs (anc (P ∥ Q)) R) → T = T' := by
  rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨hP, hQ⟩, hd⟩, hc⟩, hR⟩, hdR⟩, hcR⟩, hS⟩, hT, hT'⟩, h1, h2⟩
  obtain ⟨a, rfl⟩ := mem_potid'.1 hS
  obtain ⟨b, rfl⟩ := mem_potid'.1 hT
  obtain ⟨c, rfl⟩ := mem_potid'.1 hT'
  have e1 := eqf_exponents (mem_arrow_Cls_one.1 hP) (mem_arrow_one_Cls.1 hQ) hd hc hR hdR hcR h1
  have e2 := eqf_exponents (mem_arrow_Cls_one.1 hP) (mem_arrow_one_Cls.1 hQ) hd hc hR hdR hcR h2
  rw [← e1, ← e2]

/-- ✱95·471. \[\begin{align}\vdash:\text{Hp*95·46}.S,\,S'\in &\text{Potid}ʻP.T\in \text{Potid}ʻQ.\\ & S\mid R\mid T,S'\mid R\mid T\in (P \unicode{x2217} Q)ʻR.\supset.S=S'\\ [\text{Proof as in *95·47}]\end{align}\]

**Status.** proved (reading): Hp✱95·46 is read as in ✱95·46 (`ᗡ'R ⊂ B⃗'Q` for the
printed `B⃗'Q̆`, which would make the hypothesis contradictory). -/
theorem pm95_471 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop}
    {S S' : α → α → Prop} {T : β → β → Prop} :
    ((((((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
      rEx R) ∧ dom R ⊆ refs Beg P˘) ∧ codom R ⊆ refs Beg Q) ∧
      (S ∈ potid P ∧ S' ∈ potid P)) ∧ T ∈ potid Q) ∧
      (S ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R ∧ S' ⨾ R ⨾ T ∈ refs (anc (P ∥ Q)) R) → S = S' := by
  rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨hP, hQ⟩, hd⟩, hc⟩, hR⟩, hdR⟩, hcR⟩, hS, hS'⟩, hT⟩, h1, h2⟩
  obtain ⟨a, rfl⟩ := mem_potid'.1 hS
  obtain ⟨b, rfl⟩ := mem_potid'.1 hS'
  obtain ⟨c, rfl⟩ := mem_potid'.1 hT
  have e1 := eqf_exponents (mem_arrow_Cls_one.1 hP) (mem_arrow_one_Cls.1 hQ) hd hc hR hdR hcR h1
  have e2 := eqf_exponents (mem_arrow_Cls_one.1 hP) (mem_arrow_one_Cls.1 hQ) hd hc hR hdR hcR h2
  rw [e1, e2]

/-- ✱95·51. \(\vdash:\text{Hp*95·46}.M,\,M'\in (P \unicode{x2217} Q)ʻR.\exists !\text{ᗡ}ʻM\cap \text{ᗡ}ʻM'.\supset.M=M'\)

**Status.** proved (reading): Hp✱95·46 is read as in ✱95·46 (`ᗡ'R ⊂ B⃗'Q` for the
printed `B⃗'Q̆`, which would make the hypothesis contradictory). -/
theorem pm95_51 {P : α → α → Prop} {Q : β → β → Prop} {R M M' : α → β → Prop} :
    (((((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
      rEx R) ∧ dom R ⊆ refs Beg P˘) ∧ codom R ⊆ refs Beg Q) ∧
      (M ∈ refs (anc (P ∥ Q)) R ∧ M' ∈ refs (anc (P ∥ Q)) R)) ∧
      (codom M ∩ codom M').Nonempty → M = M' := by
  rintro ⟨⟨⟨⟨⟨⟨⟨⟨-, hQ⟩, -⟩, -⟩, -⟩, -⟩, hcR⟩, hM, hM'⟩, y, hy, hy'⟩
  obtain ⟨n, rfl⟩ := eqf_mem.1 hM
  obtain ⟨m, rfl⟩ := eqf_mem.1 hM'
  obtain ⟨w, b, ⟨a, -, hab⟩, hby⟩ := hy
  obtain ⟨w', b', ⟨a', -, hab'⟩, hby'⟩ := hy'
  rw [beg_npow_unique (mem_arrow_one_Cls.1 hQ) n m b b' y (hcR ⟨a, hab⟩) (hcR ⟨a', hab'⟩) hby hby']

/-- ✱95·511. \[\begin{align}&\vdash:\text{Hp*95·46}.M,\,M'\in (P \unicode{x2217} Q)ʻR.\exists !\text{D}ʻM\cap \text{D}ʻM'.\supset.M=M'\\ &[\text{Proof as in *95·51}]\end{align}\]

**Status.** proved (reading): Hp✱95·46 is read as in ✱95·46 (`ᗡ'R ⊂ B⃗'Q` for the
printed `B⃗'Q̆`, which would make the hypothesis contradictory). -/
theorem pm95_511 {P : α → α → Prop} {Q : β → β → Prop} {R M M' : α → β → Prop} :
    (((((((P ∈ arrow Cls one ∧ Q ∈ arrow one Cls) ∧ dom P ⊆ codom P) ∧ codom Q ⊆ dom Q) ∧
      rEx R) ∧ dom R ⊆ refs Beg P˘) ∧ codom R ⊆ refs Beg Q) ∧
      (M ∈ refs (anc (P ∥ Q)) R ∧ M' ∈ refs (anc (P ∥ Q)) R)) ∧
      (dom M ∩ dom M').Nonempty → M = M' := by
  rintro ⟨⟨⟨⟨⟨⟨⟨⟨hP, -⟩, -⟩, -⟩, -⟩, hdR⟩, -⟩, hM, hM'⟩, x, hx, hx'⟩
  obtain ⟨n, rfl⟩ := eqf_mem.1 hM
  obtain ⟨m, rfl⟩ := eqf_mem.1 hM'
  obtain ⟨z, b, ⟨a, hxa, hab⟩, -⟩ := hx
  obtain ⟨z', b', ⟨a', hxa', hab'⟩, -⟩ := hx'
  rw [end_npow_unique (mem_arrow_Cls_one.1 hP) n m x a a' (hdR ⟨b, hab⟩) (hdR ⟨b', hab'⟩) hxa hxa']

/-- ✱95·52. \[\begin{align}\vdash:P,\,Q,\,R\in 1\rightarrow 1.\text{D}ʻP\subset \text{ᗡ}ʻP.\text{ᗡ}ʻQ&\subset \text{D}ʻQ.\text{D}ʻR\subset \overrightarrow{B}ʻ\breve{P}.\text{ᗡ}ʻR\subset \overrightarrow{B}ʻQ.\supset.\\ &\dot{s}ʻ(P \unicode{x2217} Q)ʻR\in 1\rightarrow 1\end{align}\] -/
theorem pm95_52 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} :
    (((((P ∈ arrow one one ∧ Q ∈ arrow one one) ∧ R ∈ arrow one one) ∧ dom P ⊆ codom P) ∧
      codom Q ⊆ dom Q) ∧ dom R ⊆ refs Beg P˘) ∧ codom R ⊆ refs Beg Q →
      sumRel (refs (anc (P ∥ Q)) R) ∈ arrow one one := by
  rintro ⟨⟨⟨⟨⟨⟨hP, hQ⟩, hR⟩, -⟩, -⟩, hdR⟩, hcR⟩
  obtain ⟨p1, p2⟩ := mem_arrow_one_one.1 hP
  obtain ⟨q1, q2⟩ := mem_arrow_one_one.1 hQ
  obtain ⟨r1, r2⟩ := mem_arrow_one_one.1 hR
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro x x' y ⟨⟨M, hM, hxy⟩, ⟨M', hM', hx'y⟩⟩
    obtain ⟨n, rfl⟩ := eqf_mem.1 hM
    obtain ⟨m, rfl⟩ := eqf_mem.1 hM'
    obtain ⟨b, ⟨a, hxa, hab⟩, hby⟩ := hxy
    obtain ⟨b', ⟨a', hxa', hab'⟩, hby'⟩ := hx'y
    have hnm := beg_npow_unique q1 n m b b' y (hcR ⟨a, hab⟩) (hcR ⟨a', hab'⟩) hby hby'
    subst hnm
    have e1 : b = b' := npow_oneMany q1 n b b' y ⟨hby, hby'⟩
    subst e1
    have e2 : a = a' := r1 a a' b ⟨hab, hab'⟩
    subst e2
    exact npow_oneMany p1 n x x' a ⟨hxa, hxa'⟩
  · rintro x y y' ⟨⟨M, hM, hxy⟩, ⟨M', hM', hxy'⟩⟩
    obtain ⟨n, rfl⟩ := eqf_mem.1 hM
    obtain ⟨m, rfl⟩ := eqf_mem.1 hM'
    obtain ⟨b, ⟨a, hxa, hab⟩, hby⟩ := hxy
    obtain ⟨b', ⟨a', hxa', hab'⟩, hby'⟩ := hxy'
    have hnm := end_npow_unique p2 n m x a a' (hdR ⟨b, hab⟩) (hdR ⟨b', hab'⟩) hxa hxa'
    subst hnm
    have e1 : a = a' := npow_manyOne p2 n x a a' ⟨hxa, hxa'⟩
    subst e1
    have e2 : b = b' := r2 a b b' ⟨hab, hab'⟩
    subst e2
    exact npow_manyOne q2 n b y y' ⟨hby, hby'⟩

/-- ✱95·6. \[\begin{align}\vdash:\text{D}ʻR\subset \text{ᗡ}ʻP.\text{D}ʻP\subset \text{ᗡ}ʻP.\text{ᗡ}ʻR=&\overrightarrow{B}ʻQ.Q\in 1\rightarrow \text{Cls}.\supset.\\ &\text{ᗡ}ʻʻ(P \unicode{x2217} Q)ʻR=\text{gen}ʻQ\end{align}\] -/
theorem pm95_6 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} :
    ((dom R ⊆ codom P ∧ dom P ⊆ codom P) ∧ codom R = refs Beg Q) ∧ Q ∈ arrow one Cls →
      Dcnv ʻʻ refs (anc (P ∥ Q)) R = gen Q := by
  rintro ⟨⟨⟨hdR, hd⟩, hcR⟩, hQ⟩
  have key : ∀ n, codom (npow P n ⨾ R ⨾ npow Q n) = (ipow Q n)˘ ʻʻ refs Beg Q := by
    intro n
    ext y
    constructor
    · rintro ⟨w, b, ⟨a, -, hab⟩, hby⟩
      have hb : b ∈ refs Beg Q := by
        rw [← hcR]
        exact ⟨a, hab⟩
      exact ⟨b, hb, ipow_apply.2 ⟨dom_sub_fld Q (beg_dom hb), hby⟩⟩
    · rintro ⟨b, hb, hby⟩
      have hb' : b ∈ codom R := by
        rw [hcR]
        exact hb
      obtain ⟨a, hab⟩ := hb'
      obtain ⟨w, hw⟩ := npow_bwd hd n a (hdR ⟨b, hab⟩)
      exact ⟨w, b, ⟨a, hw, hab⟩, (ipow_apply.1 hby).2⟩
  ext A
  rw [mem_gen_oneMany (mem_arrow_one_Cls.1 hQ)]
  constructor
  · rintro ⟨M, hM, hA⟩
    have hA' : A = codom M := hA
    obtain ⟨n, rfl⟩ := eqf_mem.1 hM
    exact ⟨n, hA'.trans (key n)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, npow_mem_eqf P Q R n, (key n).symm⟩

/-- ✱95·601. \[\begin{align}\vdash:\text{ᗡ}ʻR\subset \text{D}ʻQ.\text{ᗡ}ʻQ\subset \text{D}ʻQ.\text{D}ʻR=\overrightarrow{B}ʻ\breve{P}.P\in &\text{Cls}\rightarrow 1.\supset.\\ &\text{D}ʻʻ(P \unicode{x2217} Q)ʻR=\text{gen}ʻ\breve{P}\\ &[\text{Proof as in *95·6}]\end{align}\] -/
theorem pm95_601 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} :
    ((codom R ⊆ dom Q ∧ codom Q ⊆ dom Q) ∧ dom R = refs Beg P˘) ∧ P ∈ arrow Cls one →
      D ʻʻ refs (anc (P ∥ Q)) R = gen P˘ := by
  rintro ⟨⟨⟨hcR, hc⟩, hdR⟩, hP⟩
  have hP' : ∀ x y z, P˘ x z ∧ P˘ y z → x = y :=
    fun x y z ⟨h1, h2⟩ => (mem_arrow_Cls_one.1 hP) z x y ⟨h1, h2⟩
  have key : ∀ n, dom (npow P n ⨾ R ⨾ npow Q n) = (ipow P˘ n)˘ ʻʻ refs Beg P˘ := by
    intro n
    ext x
    constructor
    · rintro ⟨z, b, ⟨a, hxa, hab⟩, -⟩
      have ha : a ∈ refs Beg P˘ := by
        rw [← hdR]
        exact ⟨b, hab⟩
      refine ⟨a, ha, ipow_apply.2 ⟨?_, npow_cnv_iff.2 hxa⟩⟩
      rw [fld_cnv]
      exact codom_sub_fld P (end_codom ha)
    · rintro ⟨a, ha, hax⟩
      obtain ⟨-, han⟩ := ipow_apply.1 hax
      have ha' : a ∈ dom R := by
        rw [hdR]
        exact ha
      obtain ⟨b, hab⟩ := ha'
      obtain ⟨z, hz⟩ := npow_fwd hc n b (hcR ⟨a, hab⟩)
      exact ⟨z, b, ⟨a, npow_cnv_iff.1 han, hab⟩, hz⟩
  ext A
  rw [mem_gen_oneMany hP']
  constructor
  · rintro ⟨M, hM, hA⟩
    have hA' : A = dom M := hA
    obtain ⟨n, rfl⟩ := eqf_mem.1 hM
    exact ⟨n, hA'.trans (key n)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, npow_mem_eqf P Q R n, (key n).symm⟩

private theorem dom_sumRel (L : Set (α → β → Prop)) : dom (sumRel L) = sumCls (D ʻʻ L) := by
  ext x
  constructor
  · rintro ⟨y, M, hM, hxy⟩
    exact ⟨dom M, ⟨M, hM, rfl⟩, y, hxy⟩
  · rintro ⟨A, ⟨M, hM, hA⟩, hx⟩
    have hA' : A = dom M := hA
    subst hA'
    obtain ⟨y, hxy⟩ := hx
    exact ⟨y, M, hM, hxy⟩

private theorem codom_sumRel (L : Set (α → β → Prop)) :
    codom (sumRel L) = sumCls (Dcnv ʻʻ L) := by
  ext y
  constructor
  · rintro ⟨x, M, hM, hxy⟩
    exact ⟨codom M, ⟨M, hM, rfl⟩, x, hxy⟩
  · rintro ⟨A, ⟨M, hM, hA⟩, hy⟩
    have hA' : A = codom M := hA
    subst hA'
    obtain ⟨x, hxy⟩ := hy
    exact ⟨x, M, hM, hxy⟩

/-- ✱95·61. \[\begin{align}&\vdash:P,Q,R\in 1\rightarrow 1.\text{D}ʻP\subset \text{ᗡ}ʻP.\text{ᗡ}ʻQ\subset \text{D}ʻQ.\text{D}ʻR=\overrightarrow{B}ʻ\breve{P}.\text{ᗡ}ʻR=\overrightarrow{B}ʻQ.\supset.\\ &\dot{s}ʻ(P \unicode{x2217} Q)ʻR\in 1\rightarrow 1.\text{D}ʻ\dot{s}ʻ(P \unicode{x2217} Q)ʻR=sʻ\text{gen}ʻ\breve{P}.\text{ᗡ}ʻ\dot{s}ʻ(P \unicode{x2217} Q)ʻR=sʻ\text{gen}ʻQ\\ &[\text{*95·52·6·601.*41·43·44}]\end{align}\] -/
theorem pm95_61 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} :
    ((((((P ∈ arrow one one ∧ Q ∈ arrow one one) ∧ R ∈ arrow one one) ∧ dom P ⊆ codom P) ∧
      codom Q ⊆ dom Q) ∧ dom R = refs Beg P˘) ∧ codom R = refs Beg Q) →
      (sumRel (refs (anc (P ∥ Q)) R) ∈ arrow one one ∧
        dom (sumRel (refs (anc (P ∥ Q)) R)) = sumCls (gen P˘)) ∧
        codom (sumRel (refs (anc (P ∥ Q)) R)) = sumCls (gen Q) := by
  rintro ⟨⟨⟨⟨⟨⟨hP, hQ⟩, hR⟩, hd⟩, hc⟩, hdR⟩, hcR⟩
  have hdR' : dom R ⊆ refs Beg P˘ := fun x hx => by rw [← hdR]; exact hx
  have hcR' : codom R ⊆ refs Beg Q := fun y hy => by rw [← hcR]; exact hy
  refine ⟨⟨pm95_52 ⟨⟨⟨⟨⟨⟨hP, hQ⟩, hR⟩, hd⟩, hc⟩, hdR'⟩, hcR'⟩, ?_⟩, ?_⟩
  · rw [dom_sumRel, pm95_601 ⟨⟨⟨fun y hy => beg_dom (hcR' hy), hc⟩, hdR⟩, manyOne_of_oneOne hP⟩]
  · rw [codom_sumRel, pm95_6 ⟨⟨⟨fun x hx => end_codom (hdR' hx), hd⟩, hcR⟩, oneMany_of_oneOne hQ⟩]

/-- ✱95·62. \(\vdash:\text{Hp*95·61}.\supset.sʻ\text{gen}ʻP \text{ sm } sʻ\text{gen}ʻQ \quad[\text{*95·61.*73·2}]\)

**Status.** proved (corrected): the e-text prints `s'gen'P sm s'gen'Q`. ✱95·61 gives the
domain `s'gen'P̆`, and ✱95·63 applies ✱95·62 with `P̆` for `P` to obtain `s'gen'P`, so the
conclusion is `s'gen'P̆ sm s'gen'Q`. As printed it is false: with `P` the predecessor relation
on ℕ, `Q` its converse and `R = 0 ↓ 0`, Hp✱95·61 holds, `s'gen'P = Λ` (as `D'P ⊂ ᗡ'P`) and
`0 ∈ s'gen'Q` (`pm95_62_printed_false`). -/
theorem pm95_62 {P : α → α → Prop} {Q : β → β → Prop} {R : α → β → Prop} :
    ((((((P ∈ arrow one one ∧ Q ∈ arrow one one) ∧ R ∈ arrow one one) ∧ dom P ⊆ codom P) ∧
      codom Q ⊆ dom Q) ∧ dom R = refs Beg P˘) ∧ codom R = refs Beg Q) →
      sm (sumCls (gen P˘)) (sumCls (gen Q)) := by
  intro h
  obtain ⟨⟨h1, h2⟩, h3⟩ := pm95_61 h
  exact sm_iff.2 ⟨_, ⟨h1, h2.symm⟩, h3.symm⟩

private def cxPred : ℕ → ℕ → Prop := fun x y => x = y + 1

private def cxSucc : ℕ → ℕ → Prop := fun x y => y = x + 1

private def cxZZ : ℕ → ℕ → Prop := fun x y => x = 0 ∧ y = 0

theorem pm95_62_printed_false :
    ¬ ∀ (P Q R : ℕ → ℕ → Prop),
      ((((((P ∈ arrow one one ∧ Q ∈ arrow one one) ∧ R ∈ arrow one one) ∧ dom P ⊆ codom P) ∧
        codom Q ⊆ dom Q) ∧ dom R = refs Beg P˘) ∧ codom R = refs Beg Q) →
        sm (sumCls (gen P)) (sumCls (gen Q)) := by
  intro h
  have hP : cxPred ∈ arrow one one := mem_arrow_one_one.2
    ⟨fun x y z ⟨hx, hy⟩ => (hx : x = z + 1).trans (hy : y = z + 1).symm,
      fun x y z ⟨hy, hz⟩ => by
        have h1 : x = y + 1 := hy
        have h2 : x = z + 1 := hz
        omega⟩
  have hQ : cxSucc ∈ arrow one one := mem_arrow_one_one.2
    ⟨fun x y z ⟨hx, hy⟩ => by
        have h1 : z = x + 1 := hx
        have h2 : z = y + 1 := hy
        omega,
      fun x y z ⟨hy, hz⟩ => (hy : y = x + 1).trans (hz : z = x + 1).symm⟩
  have hR : cxZZ ∈ arrow one one := mem_arrow_one_one.2
    ⟨fun x y z ⟨hx, hy⟩ => (hx : x = 0 ∧ z = 0).1.trans (hy : y = 0 ∧ z = 0).1.symm,
      fun x y z ⟨hy, hz⟩ => (hy : x = 0 ∧ y = 0).2.trans (hz : x = 0 ∧ z = 0).2.symm⟩
  have hd : dom cxPred ⊆ codom cxPred := fun x _ => ⟨x + 1, (rfl : x + 1 = x + 1)⟩
  have hc : codom cxSucc ⊆ dom cxSucc := fun y _ => ⟨y + 1, (rfl : y + 1 = y + 1)⟩
  have hdR : dom cxZZ = refs Beg cxPred˘ := by
    ext x
    constructor
    · rintro ⟨y, hx, -⟩
      subst hx
      refine ⟨⟨1, (rfl : (1 : ℕ) = 0 + 1)⟩, ?_⟩
      rintro ⟨y, hy⟩
      have : (0 : ℕ) = y + 1 := hy
      omega
    · rintro ⟨-, hnot⟩
      cases x with
      | zero => exact ⟨0, rfl, rfl⟩
      | succ k => exact absurd ⟨k, (rfl : k + 1 = k + 1)⟩ hnot
  have hcR : codom cxZZ = refs Beg cxSucc := by
    ext y
    constructor
    · rintro ⟨x, -, hy⟩
      subst hy
      refine ⟨⟨1, (rfl : (1 : ℕ) = 0 + 1)⟩, ?_⟩
      rintro ⟨x, hx⟩
      have : (0 : ℕ) = x + 1 := hx
      omega
    · rintro ⟨-, hnot⟩
      cases y with
      | zero => exact ⟨0, rfl, rfl⟩
      | succ k => exact absurd ⟨k, (rfl : k + 1 = k + 1)⟩ hnot
  have hsm := h cxPred cxSucc cxZZ ⟨⟨⟨⟨⟨⟨hP, hQ⟩, hR⟩, hd⟩, hc⟩, hdR⟩, hcR⟩
  rw [sumCls_gen_empty hd] at hsm
  have h0 : (0 : ℕ) ∈ sumCls (gen cxSucc) := by
    refine (mem_sumCls_gen_oneMany (mem_arrow_one_Cls.1 (oneMany_of_oneOne hQ))).2
      ⟨0, 0, ⟨⟨1, (rfl : (1 : ℕ) = 0 + 1)⟩, ?_⟩, rfl⟩
    rintro ⟨x, hx⟩
    have : (0 : ℕ) = x + 1 := hx
    omega
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hsm
  exact (e.symm ⟨0, h0⟩).2

/-- ✱95·63. \[\begin{align}\vdash:P,\,Q\in 1\rightarrow 1.\text{ᗡ}ʻP\subset \text{D}ʻP.\text{ᗡ}ʻQ\subset \text{D}ʻQ.&\overrightarrow{B}ʻP \text{ sm }\overrightarrow{B}ʻQ.\supset.\\ &sʻ\text{gen}ʻP \text{ sm } sʻ\text{gen}ʻQ\end{align}\] -/
theorem pm95_63 {P : α → α → Prop} {Q : β → β → Prop} :
    (((P ∈ arrow one one ∧ Q ∈ arrow one one) ∧ codom P ⊆ dom P) ∧ codom Q ⊆ dom Q) ∧
      sm (refs Beg P) (refs Beg Q) → sm (sumCls (gen P)) (sumCls (gen Q)) := by
  rintro ⟨⟨⟨⟨hP, hQ⟩, hcP⟩, hcQ⟩, hsm⟩
  obtain ⟨R, ⟨hR, hdR⟩, hcR⟩ := sm_iff.1 hsm
  exact pm95_62 (P := P˘) (Q := Q) (R := R)
    ⟨⟨⟨⟨⟨⟨cnv_mem_one_one hP, hQ⟩, hR⟩, hcP⟩, hcQ⟩, hdR.symm⟩, hcR.symm⟩

private theorem dom_eq_sumCls_gen {P : α → α → Prop} (hc : codom P ⊆ dom P)
    (hp : prodCls (Dcnv ʻʻ pot P) = Λ) : dom P = sumCls (gen P) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases fld_sub_gen_pdc P (dom_sub_fld P hx) with h | h
    · exact h
    · rw [hp, Null_eq_empty] at h
      exact h.elim
  · exact (sumCls_gen_sub_fld P).trans (fld_sub_dom hc)

/-- ✱95·64. \[\begin{align}\vdash:P,\,Q\in 1&\rightarrow 1.\text{ᗡ}ʻP\subset \text{D}ʻP.\text{ᗡ}ʻQ\subset \text{D}ʻQ.\overrightarrow{B}ʻP \text{ sm }\overrightarrow{B}ʻQ.\\ &pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP=\Lambda.pʻ\text{ᗡ}ʻʻ\text{Pot}ʻQ=\Lambda.\supset.\text{D}ʻP \text{ sm } \text{D}ʻQ\\ &[\text{*95·63.*93·274.*33·181}]\end{align}\] -/
theorem pm95_64 {P : α → α → Prop} {Q : β → β → Prop} :
    (((((P ∈ arrow one one ∧ Q ∈ arrow one one) ∧ codom P ⊆ dom P) ∧ codom Q ⊆ dom Q) ∧
      sm (refs Beg P) (refs Beg Q)) ∧ prodCls (Dcnv ʻʻ pot P) = Λ) ∧
      prodCls (Dcnv ʻʻ pot Q) = Λ → sm (dom P) (dom Q) := by
  rintro ⟨⟨h63, hpP⟩, hpQ⟩
  rw [dom_eq_sumCls_gen h63.1.1.2 hpP, dom_eq_sumCls_gen h63.1.2 hpQ]
  exact pm95_63 h63

private theorem fld_eq_sumCls_gen {P : α → α → Prop} (hP : ∀ x y z, P x z ∧ P y z → x = y)
    (h : fld P = ancCnv P ʻʻ refs Beg P) : fld P = sumCls (gen P) := by
  apply Set.Subset.antisymm _ (sumCls_gen_sub_fld P)
  intro y hy
  rw [h] at hy
  obtain ⟨b, hb, hby⟩ := hy
  have hby' : anc P b y := hby
  obtain ⟨-, n, hn⟩ := anc_iff_npow.1 hby'
  exact (mem_sumCls_gen_oneMany hP).2 ⟨b, n, hb, hn⟩

/-- ✱95·65. \[\begin{align}\vdash:&P,Q\in 1\rightarrow 1.\text{ᗡ}ʻP\subset \text{D}ʻP.\text{ᗡ}ʻQ\subset \text{D}ʻQ.\overrightarrow{B}ʻP \text{ sm }\overrightarrow{B}ʻQ.\\ &CʻP=\breve{P}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻP.CʻQ=\breve{Q}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻQ.\supset.CʻP \text{ sm } CʻQ\\ &[\text{*95·63.*93·36}]\end{align}\] -/
theorem pm95_65 {P : α → α → Prop} {Q : β → β → Prop} :
    (((((P ∈ arrow one one ∧ Q ∈ arrow one one) ∧ codom P ⊆ dom P) ∧ codom Q ⊆ dom Q) ∧
      sm (refs Beg P) (refs Beg Q)) ∧ fld P = ancCnv P ʻʻ refs Beg P) ∧
      fld Q = ancCnv Q ʻʻ refs Beg Q → sm (fld P) (fld Q) := by
  rintro ⟨⟨h63, hfP⟩, hfQ⟩
  rw [fld_eq_sumCls_gen (mem_arrow_one_Cls.1 (oneMany_of_oneOne h63.1.1.1.1)) hfP,
    fld_eq_sumCls_gen (mem_arrow_one_Cls.1 (oneMany_of_oneOne h63.1.1.1.2)) hfQ]
  exact pm95_63 h63

/-- ✱95·7. \(\vdash:R,\,S\in 1\rightarrow 1.\text{ᗡ}ʻR\subset \text{D}ʻS.\text{ᗡ}ʻS\subset \text{D}ʻR.\supset.\overrightarrow{B}ʻ(R\mid S)\text{ sm }\overrightarrow{B}ʻ(S\mid R)\) -/
theorem pm95_7 {R : α → β → Prop} {S : β → α → Prop} :
    ((R ∈ arrow one one ∧ S ∈ arrow one one) ∧ codom R ⊆ dom S) ∧ codom S ⊆ dom R →
      sm (refs Beg (R ⨾ S)) (refs Beg (S ⨾ R)) := by
  rintro ⟨⟨⟨hR, hS⟩, hRS⟩, hSR⟩
  obtain ⟨r1, r2⟩ := mem_arrow_one_one.1 hR
  obtain ⟨s1, s2⟩ := mem_arrow_one_one.1 hS
  refine sm_iff.2 ⟨fun x y => (x ∉ codom S ∧ R x y) ∨ (x ∈ codom S ∧ S y x ∧ y ∉ codom R),
    ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨(⟨-, hxz⟩ | ⟨-, hzx, hz⟩), (⟨-, hyz⟩ | ⟨-, hzy, hz'⟩)⟩
    · exact r1 x y z ⟨hxz, hyz⟩
    · exact absurd ⟨x, hxz⟩ hz'
    · exact absurd ⟨y, hyz⟩ hz
    · exact s2 z x y ⟨hzx, hzy⟩
  · rintro x y z ⟨(⟨hx, hxy⟩ | ⟨hx, hyx, -⟩), (⟨hx', hxz⟩ | ⟨hx', hzx, -⟩)⟩
    · exact r2 x y z ⟨hxy, hxz⟩
    · exact absurd hx' hx
    · exact absurd hx hx'
    · exact s1 y z x ⟨hyx, hzx⟩
  · ext x
    constructor
    · rintro ⟨⟨w, y, hxy, -⟩, hnot⟩
      by_cases hx : x ∈ codom S
      · obtain ⟨y', hy'x⟩ := id hx
        refine ⟨y', Or.inr ⟨hx, hy'x, ?_⟩⟩
        rintro ⟨u, huy'⟩
        exact hnot ⟨u, y', huy', hy'x⟩
      · exact ⟨y, Or.inl ⟨hx, hxy⟩⟩
    · rintro ⟨y, (⟨hx, hxy⟩ | ⟨hx, hyx, hy⟩)⟩
      · obtain ⟨w, hw⟩ := hRS ⟨x, hxy⟩
        refine ⟨⟨w, y, hxy, hw⟩, ?_⟩
        rintro ⟨u, v, -, hvx⟩
        exact hx ⟨v, hvx⟩
      · obtain ⟨y', hy'⟩ := hSR hx
        obtain ⟨w, hw⟩ := hRS ⟨x, hy'⟩
        refine ⟨⟨w, y', hy', hw⟩, ?_⟩
        rintro ⟨u, v, huv, hvx⟩
        have : v = y := s1 v y x ⟨hvx, hyx⟩
        subst this
        exact hy ⟨u, huv⟩
  · ext y
    constructor
    · rintro ⟨⟨w, x, hyx, -⟩, hnot⟩
      by_cases hy : y ∈ codom R
      · obtain ⟨x', hx'y⟩ := id hy
        refine ⟨x', Or.inl ⟨?_, hx'y⟩⟩
        rintro ⟨u, hux'⟩
        exact hnot ⟨u, x', hux', hx'y⟩
      · exact ⟨x, Or.inr ⟨⟨y, hyx⟩, hyx, hy⟩⟩
    · rintro ⟨x, (⟨hx, hxy⟩ | ⟨hx, hyx, hy⟩)⟩
      · obtain ⟨x', hyx'⟩ := hRS ⟨x, hxy⟩
        obtain ⟨w, hw⟩ := hSR ⟨y, hyx'⟩
        refine ⟨⟨w, x', hyx', hw⟩, ?_⟩
        rintro ⟨u, v, huv, hvy⟩
        have : v = x := r1 v x y ⟨hvy, hxy⟩
        subst this
        exact hx ⟨u, huv⟩
      · obtain ⟨w, hw⟩ := hSR hx
        refine ⟨⟨w, x, hyx, hw⟩, ?_⟩
        rintro ⟨u, v, -, hvy⟩
        exact hy ⟨v, hvy⟩

/-- ✱95·71. \(\vdash:R,\,S\in 1\rightarrow 1.\text{ᗡ}ʻR\subset \text{D}ʻS.\text{ᗡ}ʻS\subset \text{D}ʻR.\supset.sʻ\text{gen}ʻ(R\mid S)\text{ sm } sʻ\text{gen}ʻ(S\mid R)\) -/
theorem pm95_71 {R : α → β → Prop} {S : β → α → Prop} :
    ((R ∈ arrow one one ∧ S ∈ arrow one one) ∧ codom R ⊆ dom S) ∧ codom S ⊆ dom R →
      sm (sumCls (gen (R ⨾ S))) (sumCls (gen (S ⨾ R))) := by
  intro hyp
  obtain ⟨⟨⟨hR, hS⟩, hRS⟩, hSR⟩ := id hyp
  have c1 : codom (R ⨾ S) ⊆ dom (R ⨾ S) := by
    rintro z ⟨x, y, -, hyz⟩
    obtain ⟨y', hy'⟩ := hSR ⟨y, hyz⟩
    obtain ⟨w, hw⟩ := hRS ⟨z, hy'⟩
    exact ⟨w, y', hy', hw⟩
  have c2 : codom (S ⨾ R) ⊆ dom (S ⨾ R) := by
    rintro z ⟨x, y, -, hyz⟩
    obtain ⟨y', hy'⟩ := hRS ⟨y, hyz⟩
    obtain ⟨w, hw⟩ := hSR ⟨z, hy'⟩
    exact ⟨w, y', hy', hw⟩
  exact pm95_63 ⟨⟨⟨⟨relProd_mem_one_one hR hS, relProd_mem_one_one hS hR⟩, c1⟩, c2⟩, pm95_7 hyp⟩

/-!
## [✱96] On the posterity of a term

*(Vol. 1, p. 637)*

> *Summary of* *96.
>
> By the "posterity" of a term with respect to a relation \(R\) we mean the class \(\overleftarrow{R}_{\unicode{x2217}}ʻx\). In the present number, we shall be chiefly concerned with the relation (\(\overleftarrow{R}_{\unicode{x2217}}ʻx) \upharpoonleft R\), *i.e.* the relation \(R\) confined to the posterity of \(x\). We shall also be concerned with (\(\overleftarrow{R}_{\unicode{x2217}}ʻx) \upharpoonleft R_{\unicode{x2217}}\) and (\(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}\), which, as is proved in *96·13, are respectively \[ \{(\overleftarrow{R}_{\unicode{x2217}}ʻx) \upharpoonleft R\}_{\unicode{x2217}} ~\text{and}~ \{(\overleftarrow{R}_{\unicode{x2217}}ʻx) \upharpoonleft R\}_{\text{po}}. \]
>
> …

**Lean reading.** The posterity `R⃖_*'x` is `rels (anc R) x`, `R⃖_po'x` is `rels (po R) x`,
`I_R'x` and `J_R'x` are `IR R x` and `JR R x` (Dfts ✱96·01·02), and `α ↿ R` is `A ◁ R`. `R̆_po` is
read as the converse of `R_po`, `(po R)˘`, as ✱90·02 reads `R̆_*`. The descriptions `R̆'y`, `R'x`
and `max_R'J_R'x` stay descriptions (`Desc R˘ y ψ`, `Desc R x ψ`, `Desc (maxP R) (JR R x) ψ`),
`R̆'max_R'J_R'x` is `Desc2 R˘ (maxP R) (JR R x) ψ` (✱30·02), and `E!R̆'max_R'J_R'x` is
`EBang (fun u => Desc (maxP R) (JR R x) (fun m => R˘ u m))`. In ✱96·48 `∼(w = R̆'…)` keeps the
description inside the negation (PM's remark after ✱96·48), and `S⃗'w ∈ 1`, `S⃗'w ∈ 2` use `one`,
`two`.

**Status.** proved (all propositions; ✱96·01, ✱96·02 definition (Dft); ✱96·462, ✱96·47
proved (reading), see their docstrings).
-/

/-- ✱96·01. \(I_{R}ʻx=\overleftarrow{R}_{\unicode{x2217}}ʻx\cap \hat{z}(zR_{\text{po}}z) \quad\text{Dft}\, [\text{*96}]\)

**Status.** definition: a temporary definition (Dft, ✱96 only) of the descriptive
function `I_R'x`, whose value always exists; it is the function `IR R x`. -/
theorem pm96_01 {R : α → α → Prop} {x : α} : IR R x = rels (anc R) x ∩ {z | po R z z} := rfl

/-- ✱96·02. \(J_{R}ʻx=\overleftarrow{R}_{\unicode{x2217}}ʻx-I_{R}ʻx \quad\text{Dft}\, [\text{*96}]\)

**Status.** definition: a temporary definition (Dft, ✱96 only) of the descriptive
function `J_R'x`, whose value always exists; it is the function `JR R x`. -/
theorem pm96_02 {R : α → α → Prop} {x : α} : JR R x = rels (anc R) x \ IR R x := rfl

/-- ✱96·1. \(\vdash:z\in I_{R}ʻx.\equiv.xR_{\unicode{x2217}}z.zR_{\text{po}}z \quad[\text{*20·3.*32·181.(*96·01)}]\) -/
theorem pm96_1 {R : α → α → Prop} {x z : α} : z ∈ IR R x ↔ anc R x z ∧ po R z z := Iff.rfl

/-- ✱96·101. \(\vdash:z\in J_{R}ʻx.\equiv.xR_{\unicode{x2217}}z.{\sim}(zR_{\text{po}}z) \quad[\text{*96·1.*22·93.(*96·02)}]\) -/
theorem pm96_101 {R : α → α → Prop} {x z : α} : z ∈ JR R x ↔ anc R x z ∧ ¬ po R z z := mem_JR

/-- ✱96·102. \(\vdash.\overleftarrow{R}_{\unicode{x2217}}ʻx=J_{R}ʻx\cup I_{R}ʻx.J_{R}ʻx\cap I_{R}ʻx=\Lambda \quad[\text{*24·41·21.(*96·01·02)}]\) -/
theorem pm96_102 {R : α → α → Prop} {x : α} :
    rels (anc R) x = JR R x ∪ IR R x ∧ JR R x ∩ IR R x = Λ := by
  refine ⟨?_, ?_⟩
  · ext z
    constructor
    · intro hz
      by_cases h : po R z z
      · exact Or.inr ⟨hz, h⟩
      · exact Or.inl (mem_JR.2 ⟨hz, h⟩)
    · rintro (h | h)
      · exact h.1
      · exact h.1
  · rw [Null_eq_empty]
    exact Set.sdiff_inter_self

/-- ✱96·103. \(\vdash.(J_{R}ʻx)\upharpoonleft R_{\text{po}}\unicode{x2abd}J\) -/
theorem pm96_103 {R : α → α → Prop} {x : α} : JR R x ◁ po R ⪽ J := by
  rintro y z ⟨hy, hyz⟩ e
  have e' : y = z := e
  subst e'
  exact (mem_JR.1 hy).2 hyz

/-- ✱96·104. \(\vdash:I_{R}ʻx=\Lambda.\equiv.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}\unicode{x2abd}J.\equiv.J_{R}ʻx=\overleftarrow{R}_{\unicode{x2217}}ʻx\) -/
theorem pm96_104 {R : α → α → Prop} {x : α} :
    (IR R x = Λ ↔ rels (anc R) x ◁ po R ⪽ J) ∧ (rels (anc R) x ◁ po R ⪽ J ↔ JR R x = rels (anc R) x) := by
  have h1 : IR R x = Λ ↔ ∀ z, anc R x z → ¬ po R z z := by
    rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]
    exact ⟨fun h z hz hzz => h z ⟨hz, hzz⟩, fun h z hz => h z hz.1 hz.2⟩
  have h2 : rels (anc R) x ◁ po R ⪽ J ↔ ∀ z, anc R x z → ¬ po R z z := by
    constructor
    · intro h z hz hzz
      exact h z z ⟨hz, hzz⟩ rfl
    · intro h y z ⟨hy, hyz⟩ e
      have e' : y = z := e
      subst e'
      exact h y hy hyz
  have h3 : JR R x = rels (anc R) x ↔ ∀ z, anc R x z → ¬ po R z z := by
    constructor
    · intro h z hz
      have : z ∈ JR R x := by rw [h]; exact hz
      exact (mem_JR.1 this).2
    · intro h
      ext z
      exact ⟨fun hz => (mem_JR.1 hz).1, fun hz => mem_JR.2 ⟨hz, h z hz⟩⟩
  rw [h1, h2, h3]
  exact ⟨Iff.rfl, Iff.rfl⟩

private theorem po_dres_sub {R : α → α → Prop} {A : Set α} {x y : α} (h : po (A ◁ R) x y) :
    x ∈ A ∧ po R x y := by
  rw [po_iff_transGen] at h ⊢
  induction h with
  | single h => exact ⟨h.1, TransGen.single h.2⟩
  | tail _ hbc ih => exact ⟨ih.1, ih.2.tail hbc.2⟩

/-- ✱96·11. \(\vdash.(\alpha\upharpoonleft R)_{\text{po}}\unicode{x2abd}\alpha\upharpoonleft R_{\text{po}}\) -/
theorem pm96_11 {R : α → α → Prop} {A : Set α} : po (A ◁ R) ⪽ A ◁ po R :=
  fun _ _ h => po_dres_sub h

private theorem tg_dres_of {R : α → α → Prop} {A : Set α} (hA : R˘ ʻʻ A ⊆ A) {x y : α}
    (hx : x ∈ A) (h : TransGen R x y) : TransGen (A ◁ R) x y := by
  induction h using TransGen.head_induction_on with
  | single h => exact TransGen.single ⟨hx, h⟩
  | head hab _ ih => exact TransGen.head ⟨hx, hab⟩ (ih (hA ⟨_, hx, hab⟩))

/-- ✱96·111. \(\vdash:\breve{R}ʻʻ\alpha\subset \alpha.\supset.(\alpha\upharpoonleft R)_{\text{po}}=\alpha\upharpoonleft R_{\text{po}}\) -/
theorem pm96_111 {R : α → α → Prop} {A : Set α} : R˘ ʻʻ A ⊆ A → po (A ◁ R) = A ◁ po R := by
  intro hA
  funext x y
  apply propext
  constructor
  · exact po_dres_sub
  · rintro ⟨hx, h⟩
    rw [po_iff_transGen] at h ⊢
    exact tg_dres_of hA hx h

private theorem rtg_dres_of {R : α → α → Prop} {A : Set α} (hA : R˘ ʻʻ A ⊆ A) {x y : α}
    (hx : x ∈ A) (h : ReflTransGen R x y) : ReflTransGen (A ◁ R) x y := by
  rcases ReflTransGen.cases_head h with rfl | ⟨b, hxb, hby⟩
  · exact ReflTransGen.refl
  · exact (tg_dres_of hA hx (TransGen.head' hxb hby)).to_reflTransGen

/-- ✱96·112. \(\vdash:\alpha\subset \text{D}ʻR.\breve{R}ʻʻ\alpha\subset \alpha.\supset.(\alpha\upharpoonleft R)_{\unicode{x2217}}=\alpha\upharpoonleft R_{\unicode{x2217}}\) -/
theorem pm96_112 {R : α → α → Prop} {A : Set α} :
    A ⊆ dom R ∧ R˘ ʻʻ A ⊆ A → anc (A ◁ R) = A ◁ anc R := by
  rintro ⟨hd, hA⟩
  funext x y
  apply propext
  rw [anc_iff_reflTransGen]
  constructor
  · rintro ⟨hx, h⟩
    have hxA : x ∈ A := by
      obtain ⟨z, ⟨hxA, -⟩ | ⟨hzA, hzx⟩⟩ := hx
      · exact hxA
      · exact hA ⟨z, hzA, hzx⟩
    refine ⟨hxA, anc_iff_reflTransGen.2 ⟨dom_sub_fld R (hd hxA), ?_⟩⟩
    exact rtg_mono h (fun a b hab => hab.2)
  · rintro ⟨hx, h⟩
    obtain ⟨z, hz⟩ := hd hx
    exact ⟨⟨z, Or.inl ⟨hx, hz⟩⟩, rtg_dres_of hA hx (anc_iff_reflTransGen.1 h).2⟩

private theorem po_cres_sub {R : α → α → Prop} {A : Set α} {x y : α} (h : po (R ↾ A) x y) :
    po R x y ∧ y ∈ A := by
  rw [po_iff_transGen] at h ⊢
  induction h with
  | single h => exact ⟨TransGen.single h.1, h.2⟩
  | tail _ hbc ih => exact ⟨ih.1.tail hbc.1, hbc.2⟩

private theorem tg_cres_of {R : α → α → Prop} {A : Set α} (hA : R ʻʻ A ⊆ A) {x y : α}
    (hy : y ∈ A) (h : TransGen R x y) : TransGen (R ↾ A) x y := by
  induction h with
  | single h => exact TransGen.single ⟨h, hy⟩
  | tail _ hbc ih => exact TransGen.tail (ih (hA ⟨_, hy, hbc⟩)) ⟨hbc, hy⟩

/-- ✱96·121. \(\vdash:Rʻʻ\alpha\subset \alpha.\supset.(R\upharpoonright \alpha)_{\text{po}}=R_{\text{po}}\upharpoonright \alpha \quad[\text{Proof as in *96·111}]\) -/
theorem pm96_121 {R : α → α → Prop} {A : Set α} : R ʻʻ A ⊆ A → po (R ↾ A) = po R ↾ A := by
  intro hA
  funext x y
  apply propext
  constructor
  · exact po_cres_sub
  · rintro ⟨h, hy⟩
    rw [po_iff_transGen] at h ⊢
    exact tg_cres_of hA hy h

/-- ✱96·122. \(\vdash:\alpha\subset \text{ᗡ}ʻR.Rʻʻ\alpha\subset \alpha.\supset.(R\upharpoonright \alpha)_{\unicode{x2217}}=R_{\unicode{x2217}}\upharpoonright \alpha \quad[\text{Proof as in *96·112}]\) -/
theorem pm96_122 {R : α → α → Prop} {A : Set α} :
    A ⊆ codom R ∧ R ʻʻ A ⊆ A → anc (R ↾ A) = anc R ↾ A := by
  rintro ⟨hc, hA⟩
  funext x y
  apply propext
  rw [anc_iff_reflTransGen]
  constructor
  · rintro ⟨hx, h⟩
    have hyA : y ∈ A := by
      rcases ReflTransGen.cases_tail h with rfl | ⟨b, -, hby⟩
      · obtain ⟨z, ⟨hxz, hzA⟩ | ⟨hzx, hxA⟩⟩ := hx
        · exact hA ⟨z, hzA, hxz⟩
        · exact hxA
      · exact hby.2
    refine ⟨anc_iff_reflTransGen.2 ⟨?_, rtg_mono h (fun a b hab => hab.1)⟩, hyA⟩
    obtain ⟨z, h' | h'⟩ := hx
    · exact ⟨z, Or.inl h'.1⟩
    · exact ⟨z, Or.inr h'.1⟩
  · rintro ⟨h, hy⟩
    obtain ⟨hx, h⟩ := anc_iff_reflTransGen.1 h
    rcases ReflTransGen.cases_head h with rfl | ⟨b, hxb, hby⟩
    · obtain ⟨z, hz⟩ := hc hy
      exact ⟨⟨z, Or.inr ⟨hz, hy⟩⟩, ReflTransGen.refl⟩
    · have htg := tg_cres_of hA hy (TransGen.head' hxb hby)
      obtain ⟨c, hc'⟩ := TransGen.head'_iff.1 htg
      exact ⟨⟨c, Or.inl hc'.1⟩, htg.to_reflTransGen⟩

private theorem post_closed (R : α → α → Prop) (x : α) : R˘ ʻʻ rels (anc R) x ⊆ rels (anc R) x := by
  rintro z ⟨y, hy, hyz⟩
  exact anc_tail hy hyz

/-- ✱96·13. \(\vdash.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}=\{(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R\}_{\text{po}} \quad[\text{*96·111.*90·163}]\) -/
theorem pm96_13 {R : α → α → Prop} {x : α} :
    rels (anc R) x ◁ po R = po (rels (anc R) x ◁ R) :=
  (pm96_111 (post_closed R x)).symm

/-- ✱96·131. \(\vdash.x\in \text{D}ʻR.\supset.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\unicode{x2217}}=\{(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R\}_{\unicode{x2217}} \quad[\text{*96·112.*90·163}]\) -/
theorem pm96_131 {R : α → α → Prop} {x : α} :
    x ∈ dom R → rels (anc R) x ◁ anc R = anc (rels (anc R) x ◁ R) := by
  intro hx
  funext y z
  apply propext
  constructor
  · rintro ⟨hy, hyz⟩
    have hyz' := (anc_iff_reflTransGen.1 hyz).2
    refine anc_iff_reflTransGen.2 ⟨?_, rtg_dres_of (post_closed R x) hy hyz'⟩
    rcases anc_iff_po.1 hy with ⟨rfl, -⟩ | hpo
    · obtain ⟨w, hw⟩ := hx
      exact ⟨w, Or.inl ⟨hy, hw⟩⟩
    · obtain ⟨t, hxt, hty⟩ := po_iff_anc_comp.1 hpo
      exact ⟨t, Or.inr ⟨hxt, hty⟩⟩
  · intro h
    obtain ⟨hy, h⟩ := anc_iff_reflTransGen.1 h
    have hyA : y ∈ rels (anc R) x := by
      obtain ⟨w, ⟨hyA, -⟩ | ⟨hwA, hwy⟩⟩ := hy
      · exact hyA
      · exact anc_tail hwA hwy
    refine ⟨hyA, anc_iff_reflTransGen.2 ⟨anc_fld_right hyA, rtg_mono h (fun a b hab => hab.2)⟩⟩

/-- ✱96·14. \(\vdash:x\in CʻR.\supset.\overleftarrow{R}_{\unicode{x2217}}ʻx=\iotaʻx\cup \overleftarrow{R}_{\text{po}}ʻx \quad[\text{*91·54.*32·33}]\) -/
theorem pm96_14 {R : α → α → Prop} {x : α} :
    x ∈ fld R → rels (anc R) x = ι x ∪ rels (po R) x := by
  intro hx
  ext y
  constructor
  · intro h
    rcases anc_iff_po.1 h with ⟨rfl, -⟩ | h
    · exact Or.inl rfl
    · exact Or.inr h
  · rintro (h | h)
    · have e : y = x := h
      subst e
      exact anc_refl hx
    · exact po_sub_anc h

/-- ✱96·141. \(\vdash.Cʻ(\alpha\upharpoonleft R_{\unicode{x2217}})=\breve{R}_{\unicode{x2217}}ʻʻ\alpha\) -/
theorem pm96_141 {R : α → α → Prop} {A : Set α} : fld (A ◁ anc R) = ancCnv R ʻʻ A := by
  ext y
  constructor
  · rintro ⟨z, ⟨hy, hyz⟩ | ⟨hz, hzy⟩⟩
    · exact ⟨y, hy, anc_refl (anc_left_fld hyz)⟩
    · exact ⟨z, hz, hzy⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨z, Or.inr ⟨hz, hzy⟩⟩

/-- ✱96·142. \(\vdash.Cʻ(\alpha\upharpoonleft R_{\text{po}})=(\alpha\cap \text{D}ʻR)\cup \breve{R}_{\text{po}}ʻʻ\alpha \quad[\text{*35·61.*37·4.*91·504}]\) -/
theorem pm96_142 {R : α → α → Prop} {A : Set α} :
    fld (A ◁ po R) = (A ∩ dom R) ∪ (po R)˘ ʻʻ A := by
  ext y
  constructor
  · rintro ⟨z, ⟨hy, hyz⟩ | ⟨hz, hzy⟩⟩
    · exact Or.inl ⟨hy, po_left_dom hyz⟩
    · exact Or.inr ⟨z, hz, hzy⟩
  · rintro (⟨hy, w, hw⟩ | ⟨z, hz, hzy⟩)
    · exact ⟨w, Or.inl ⟨hy, R_sub_po hw⟩⟩
    · exact ⟨z, Or.inr ⟨hz, hzy⟩⟩

/-- ✱96·143. \(\vdash.Cʻ(\alpha\upharpoonleft R_{\text{po}})=\breve{R}_{\unicode{x2217}}ʻʻ(\alpha\cap \text{D}ʻR)\) -/
theorem pm96_143 {R : α → α → Prop} {A : Set α} :
    fld (A ◁ po R) = ancCnv R ʻʻ (A ∩ dom R) := by
  rw [pm96_142]
  ext y
  constructor
  · rintro (⟨hy, hyd⟩ | ⟨z, hz, hzy⟩)
    · exact ⟨y, ⟨hy, hyd⟩, anc_refl (dom_sub_fld R hyd)⟩
    · exact ⟨z, ⟨hz, po_left_dom hzy⟩, po_sub_anc hzy⟩
  · rintro ⟨z, ⟨hz, hzd⟩, hzy⟩
    rcases anc_iff_po.1 (show anc R z y from hzy) with ⟨rfl, -⟩ | h
    · exact Or.inl ⟨hz, hzd⟩
    · exact Or.inr ⟨z, hz, h⟩

/-- ✱96·144. \(\vdash:\alpha\cap \text{ᗡ}ʻR\subset \breve{R}_{\unicode{x2217}}ʻʻ(\alpha\cap \text{D}ʻR).\supset.Cʻ(\alpha\upharpoonleft R_{\text{po}})=\breve{R}_{\unicode{x2217}}ʻʻ\alpha\) -/
theorem pm96_144 {R : α → α → Prop} {A : Set α} :
    A ∩ codom R ⊆ ancCnv R ʻʻ (A ∩ dom R) → fld (A ◁ po R) = ancCnv R ʻʻ A := by
  intro h
  rw [pm96_143]
  apply Set.Subset.antisymm
  · rintro y ⟨z, ⟨hz, -⟩, hzy⟩
    exact ⟨z, hz, hzy⟩
  · rintro y ⟨z, hz, hzy⟩
    have hzy' : anc R z y := hzy
    by_cases hzd : z ∈ dom R
    · exact ⟨z, ⟨hz, hzd⟩, hzy⟩
    · rcases anc_iff_po.1 hzy' with ⟨rfl, -⟩ | hpo
      · have hzf := anc_left_fld hzy'
        have hzc : z ∈ codom R := by
          obtain ⟨w, hw | hw⟩ := hzf
          · exact absurd ⟨w, hw⟩ hzd
          · exact ⟨w, hw⟩
        exact h ⟨hz, hzc⟩
      · exact absurd (po_left_dom hpo) hzd

/-- ✱96·15. \(\vdash:\text{D}ʻ\{(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R\}=\overleftarrow{R}_{\unicode{x2217}}ʻx\cap \text{D}ʻR.\text{ᗡ}ʻ{(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R}=\overleftarrow{R}_{\text{po}}ʻx\) -/
theorem pm96_15 {R : α → α → Prop} {x : α} :
    dom (rels (anc R) x ◁ R) = rels (anc R) x ∩ dom R ∧
      codom (rels (anc R) x ◁ R) = rels (po R) x := by
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, hy, hyz⟩
      exact ⟨hy, z, hyz⟩
    · rintro ⟨hy, z, hyz⟩
      exact ⟨z, hy, hyz⟩
  · ext z
    constructor
    · rintro ⟨y, hy, hyz⟩
      exact po_iff_anc_comp.2 ⟨y, hy, hyz⟩
    · intro h
      obtain ⟨y, hy, hyz⟩ := po_iff_anc_comp.1 h
      exact ⟨y, hy, hyz⟩

/-- ✱96·151. \(\vdash:x\in \text{D}ʻR.\supset.Cʻ\{(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R\}=\overleftarrow{R}_{\unicode{x2217}}ʻx\) -/
theorem pm96_151 {R : α → α → Prop} {x : α} :
    x ∈ dom R → fld (rels (anc R) x ◁ R) = rels (anc R) x := by
  intro hx
  ext y
  constructor
  · rintro ⟨z, ⟨hy, -⟩ | ⟨hz, hzy⟩⟩
    · exact hy
    · exact anc_tail hz hzy
  · intro hy
    rcases anc_iff_po.1 hy with ⟨rfl, -⟩ | hpo
    · obtain ⟨w, hw⟩ := hx
      exact ⟨w, Or.inl ⟨hy, hw⟩⟩
    · obtain ⟨t, hxt, hty⟩ := po_iff_anc_comp.1 hpo
      exact ⟨t, Or.inr ⟨hxt, hty⟩⟩

/-- ✱96·152. \(\vdash.\breve{R}_{\unicode{x2217}}ʻʻ\overleftarrow{R}_{\unicode{x2217}}ʻx=\overleftarrow{R}_{\unicode{x2217}}ʻx \quad[\text{*90·17}]\) -/
theorem pm96_152 {R : α → α → Prop} {x : α} :
    ancCnv R ʻʻ rels (anc R) x = rels (anc R) x := by
  ext z
  constructor
  · rintro ⟨y, hy, hyz⟩
    exact anc_trans hy hyz
  · intro hz
    exact ⟨z, hz, anc_refl (anc_fld_right hz)⟩

/-- ✱96·153. \(\vdash.\breve{R}_{\unicode{x2217}}ʻʻ\overleftarrow{R}_{\text{po}}ʻx=\breve{R}_{\text{po}}ʻʻ\overleftarrow{R}_{\unicode{x2217}}ʻx=\overleftarrow{R}_{\text{po}}ʻx \quad[\text{*91·574}]\) -/
theorem pm96_153 {R : α → α → Prop} {x : α} :
    ancCnv R ʻʻ rels (po R) x = (po R)˘ ʻʻ rels (anc R) x ∧
      (po R)˘ ʻʻ rels (anc R) x = rels (po R) x := by
  have h1 : ancCnv R ʻʻ rels (po R) x = rels (po R) x := by
    ext z
    constructor
    · rintro ⟨y, hy, hyz⟩
      have hyz' : anc R y z := hyz
      rcases anc_iff_po.1 hyz' with ⟨rfl, -⟩ | h
      · exact hy
      · exact po_trans hy h
    · intro hz
      exact ⟨z, hz, anc_refl (anc_fld_right (po_sub_anc hz))⟩
  have h2 : (po R)˘ ʻʻ rels (anc R) x = rels (po R) x := by
    ext z
    constructor
    · rintro ⟨y, hy, hyz⟩
      have hyz' : po R y z := hyz
      rcases anc_iff_po.1 hy with ⟨rfl, -⟩ | h
      · exact hyz'
      · exact po_trans h hyz'
    · intro hz
      have hz' : po R x z := hz
      exact ⟨x, anc_refl (dom_sub_fld R (po_left_dom hz')), hz'⟩
  rw [h1, h2]
  exact ⟨rfl, rfl⟩

/-- ✱96·154. \(\vdash.Cʻ\{(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\unicode{x2217}}\}=\overleftarrow{R}_{\unicode{x2217}}ʻx \quad[\text{*96·141·152}]\) -/
theorem pm96_154 {R : α → α → Prop} {x : α} :
    fld (rels (anc R) x ◁ anc R) = rels (anc R) x := by
  rw [pm96_141, pm96_152]

/-- ✱96·155. \(\vdash.\text{D}ʻ\{(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}\}=\overleftarrow{R}_{\unicode{x2217}}ʻx\cap \text{D}ʻR.\text{ᗡ}ʻ\{(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}\}=\overleftarrow{R}_{\text{po}}ʻx\) -/
theorem pm96_155 {R : α → α → Prop} {x : α} :
    dom (rels (anc R) x ◁ po R) = rels (anc R) x ∩ dom R ∧
      codom (rels (anc R) x ◁ po R) = rels (po R) x := by
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, hy, hyz⟩
      exact ⟨hy, po_left_dom hyz⟩
    · rintro ⟨hy, z, hyz⟩
      exact ⟨z, hy, R_sub_po hyz⟩
  · rw [← (pm96_153 (R := R) (x := x)).2]
    ext z
    exact ⟨fun ⟨y, hy, hyz⟩ => ⟨y, hy, hyz⟩, fun ⟨y, hy, hyz⟩ => ⟨y, hy, hyz⟩⟩

/-- ✱96·156. \(\vdash.Cʻ\{(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}\}=(\iotaʻx\cap \text{D}ʻR)\cup \overleftarrow{R}_{\text{po}}ʻx\) -/
theorem pm96_156 {R : α → α → Prop} {x : α} :
    fld (rels (anc R) x ◁ po R) = (ι x ∩ dom R) ∪ rels (po R) x := by
  rw [pm96_142, (pm96_153 (R := R) (x := x)).2]
  ext y
  constructor
  · rintro (⟨hy, hyd⟩ | h)
    · rcases anc_iff_po.1 hy with ⟨rfl, -⟩ | h
      · exact Or.inl ⟨rfl, hyd⟩
      · exact Or.inr h
    · exact Or.inr h
  · rintro (⟨hy, hyd⟩ | h)
    · have e : y = x := hy
      subst e
      exact Or.inl ⟨anc_refl (dom_sub_fld R hyd), hyd⟩
    · exact Or.inr h

/-- ✱96·157. \(\vdash:x\in \text{D}ʻR.\supset.Cʻ\{(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}\}=\overleftarrow{R}_{\unicode{x2217}}ʻx \quad[\text{*96·156·14}]\) -/
theorem pm96_157 {R : α → α → Prop} {x : α} :
    x ∈ dom R → fld (rels (anc R) x ◁ po R) = rels (anc R) x := by
  intro hx
  rw [pm96_156, pm96_14 (dom_sub_fld R hx)]
  ext y
  constructor
  · rintro (⟨hy, -⟩ | h)
    · exact Or.inl hy
    · exact Or.inr h
  · rintro (hy | h)
    · have e : y = x := hy
      subst e
      exact Or.inl ⟨rfl, hx⟩
    · exact Or.inr h

/-- ✱96·158. \(\vdash:x{\sim}\in \text{D}ʻR.\supset.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}=\dot{\Lambda}\) -/
theorem pm96_158 {R : α → α → Prop} {x : α} :
    x ∉ dom R → rels (anc R) x ◁ po R = rNull := by
  intro hx
  funext y z
  apply propext
  refine ⟨?_, fun h => absurd h (rNull_apply y z)⟩
  rintro ⟨hy, hyz⟩
  rcases anc_iff_po.1 hy with ⟨rfl, -⟩ | h
  · exact absurd (po_left_dom hyz) hx
  · exact absurd (po_left_dom h) hx

/-- ✱96·159. \(\vdash:\dot{\exists}!(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}.\supset.Cʻ\{(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}\}=\overleftarrow{R}_{\unicode{x2217}}ʻx \quad[\text{*96·157·158}]\) -/
theorem pm96_159 {R : α → α → Prop} {x : α} :
    rEx (rels (anc R) x ◁ po R) → fld (rels (anc R) x ◁ po R) = rels (anc R) x := by
  intro h
  by_cases hx : x ∈ dom R
  · exact pm96_157 hx
  · rw [pm96_158 hx] at h
    obtain ⟨a, b, hab⟩ := h
    exact absurd hab (rNull_apply a b)

/-- ✱96·16. \(\vdash.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R=R \unicode{x0294f} \overleftarrow{R}_{\unicode{x2217}}ʻx\) -/
theorem pm96_16 {R : α → α → Prop} {x : α} :
    rels (anc R) x ◁ R = R ⥏ rels (anc R) x := by
  funext y z
  apply propext
  constructor
  · rintro ⟨hy, hyz⟩
    exact ⟨⟨hy, hyz⟩, anc_tail hy hyz⟩
  · rintro ⟨⟨hy, hyz⟩, -⟩
    exact ⟨hy, hyz⟩

/-- ✱96·2. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R=R\upharpoonright \overleftarrow{R}_{\text{po}}ʻx\) -/
theorem pm96_2 {R : α → α → Prop} {x : α} :
    R ∈ arrow one Cls → rels (anc R) x ◁ R = R ↾ rels (po R) x := by
  intro hR
  have hR' := mem_arrow_one_Cls.1 hR
  funext y z
  apply propext
  constructor
  · rintro ⟨hy, hyz⟩
    exact ⟨hyz, po_iff_anc_comp.2 ⟨y, hy, hyz⟩⟩
  · rintro ⟨hyz, hz⟩
    obtain ⟨t, hxt, htz⟩ := po_iff_anc_comp.1 hz
    have : t = y := hR' t y z ⟨htz, hyz⟩
    subst this
    exact ⟨hxt, hyz⟩

/-- ✱96·21. \(\vdash:R\in 1\rightarrow \text{Cls}.xBR.\supset.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R=R\upharpoonright \overleftarrow{R}_{\unicode{x2217}}ʻx\) -/
theorem pm96_21 {R : α → α → Prop} {x : α} :
    R ∈ arrow one Cls ∧ Beg x R → rels (anc R) x ◁ R = R ↾ rels (anc R) x := by
  rintro ⟨hR, hx⟩
  rw [pm96_2 hR]
  funext y z
  apply propext
  constructor
  · rintro ⟨hyz, hz⟩
    exact ⟨hyz, po_sub_anc hz⟩
  · rintro ⟨hyz, hz⟩
    refine ⟨hyz, ?_⟩
    rcases anc_iff_po.1 hz with ⟨rfl, -⟩ | h
    · exact absurd ⟨y, hyz⟩ (beg_not_codom hx)
    · exact h

private theorem npow_oneMany_fixed {R : α → α → Prop} (hR : ∀ x y z, R x z ∧ R y z → x = y)
    {y : α} (hy : R y y) : ∀ n x, npow R n x y → x = y := by
  intro n
  induction n with
  | zero => exact fun x h => h
  | succ n ih =>
    intro x h
    obtain ⟨w, hxw, hwy⟩ := h
    have : w = y := hR w y y ⟨hwy, hy⟩
    subst this
    exact ih x hxw

/-- ✱96·22. \(\vdash:R\in 1\rightarrow \text{Cls}.{\sim}(xRx).\supset.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R\unicode{x2abd}J\) -/
theorem pm96_22 {R : α → α → Prop} {x : α} :
    R ∈ arrow one Cls ∧ ¬ R x x → rels (anc R) x ◁ R ⪽ J := by
  rintro ⟨hR, hxx⟩ y z ⟨hy, hyz⟩ e
  have e' : y = z := e
  subst e'
  obtain ⟨-, n, hn⟩ := anc_iff_npow.1 hy
  have : x = y := npow_oneMany_fixed (mem_arrow_one_Cls.1 hR) hyz n x hn
  subst this
  exact hxx hyz

private theorem IR_empty_of_beg {R : α → α → Prop} {x : α} (hR : ∀ x y z, R x z ∧ R y z → x = y)
    (hx : Beg x R) : IR R x = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hz, hzz⟩
  obtain ⟨-, n, hn⟩ := anc_iff_npow.1 hz
  obtain ⟨p, hp⟩ := npow_succ_of_po hzz
  have hN := npow_mul_self hp (n + 1)
  have hle : n + 1 ≤ (p + 1) * (n + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos p)
  obtain ⟨M, hM⟩ := Nat.exists_eq_add_of_le hle
  rw [hM, show n + 1 + M = (M + 1) + n by omega, npow_add] at hN
  obtain ⟨t, hzt, htz⟩ := hN
  have : t = x := npow_oneMany hR n t x z ⟨htz, hn⟩
  subst this
  obtain ⟨u, -, hut⟩ := hzt
  exact beg_not_codom hx ⟨u, hut⟩

/-- ✱96·23. \(\vdash:R\in 1\rightarrow \text{Cls}.xBR.\supset.I_{R}ʻx=\Lambda.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}\unicode{x2abd}J\) -/
theorem pm96_23 {R : α → α → Prop} {x : α} :
    R ∈ arrow one Cls ∧ Beg x R → IR R x = Λ ∧ rels (anc R) x ◁ po R ⪽ J := by
  rintro ⟨hR, hx⟩
  have hI := IR_empty_of_beg (mem_arrow_one_Cls.1 hR) hx
  rw [Null_eq_empty]
  refine ⟨hI, ?_⟩
  rintro y z ⟨hy, hyz⟩ e
  have e' : y = z := e
  subst e'
  have : y ∈ IR R x := ⟨hy, hyz⟩
  rw [hI] at this
  exact this

/-- ✱96·24. \(\vdash:R\in 1\rightarrow \text{Cls}.CʻR=\breve{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR.\supset.R_{\text{po}}\unicode{x2abd}J\) -/
theorem pm96_24 {R : α → α → Prop} :
    R ∈ arrow one Cls ∧ fld R = ancCnv R ʻʻ refs Beg R → po R ⪽ J := by
  rintro ⟨hR, hf⟩ y z hyz e
  have e' : y = z := e
  subst e'
  have hy : y ∈ fld R := dom_sub_fld R (po_left_dom hyz)
  rw [hf] at hy
  obtain ⟨b, hb, hby⟩ := hy
  have hI := IR_empty_of_beg (mem_arrow_one_Cls.1 hR) hb
  have : y ∈ IR R b := ⟨hby, hyz⟩
  rw [hI] at this
  exact this

/-- ✱96·25. \(\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.xBR.xR_{\unicode{x2217}}y:yR_{\unicode{x2217}}z.\lor.zR_{\unicode{x2217}}y:\supset.xR_{\unicode{x2217}}z\) -/
theorem pm96_25 {R : α → α → Prop} {x y z : α} :
    ((R ∈ arrow one Cls ∧ Beg x R) ∧ anc R x y) ∧ (anc R y z ∨ anc R z y) → anc R x z := by
  rintro ⟨⟨⟨hR, hx⟩, hxy⟩, hyz | hzy⟩
  · exact anc_trans hxy hyz
  · rcases anc_oneMany_cmp (mem_arrow_one_Cls.1 hR) hxy hzy with h | h
    · exact h
    · rcases anc_iff_po.1 h with ⟨rfl, -⟩ | hpo
      · exact anc_refl (anc_left_fld hxy)
      · obtain ⟨t, -, htx⟩ := po_iff_anc_comp.1 hpo
        exact absurd ⟨t, htx⟩ (beg_not_codom hx)

/-- ✱96·3. \(\vdash:xR_{\unicode{x2217}}y.\supset.\overleftarrow{R}_{\unicode{x2217}}ʻy\subset \overleftarrow{R}_{\unicode{x2217}}ʻx \quad[\text{*90·17}]\) -/
theorem pm96_3 {R : α → α → Prop} {x y : α} :
    anc R x y → rels (anc R) y ⊆ rels (anc R) x :=
  fun h _ hz => anc_trans h hz

/-- ✱96·301. \(\vdash:xR_{\unicode{x2217}}y.\supset.\overrightarrow{R}_{\unicode{x2217}}ʻx\subset \overrightarrow{R}_{\unicode{x2217}}ʻy \quad[\text{*90·17}]\) -/
theorem pm96_301 {R : α → α → Prop} {x y : α} :
    anc R x y → refs (anc R) x ⊆ refs (anc R) y :=
  fun h _ hz => anc_trans hz h

/-- ✱96·302. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.xR_{\unicode{x2217}}y.xR_{\unicode{x2217}}z.\supset:yR_{\unicode{x2217}}z.\lor.zR_{\unicode{x2217}}y \quad[\text{*92·311}]\) -/
theorem pm96_302 {R : α → α → Prop} {x y z : α} :
    (R ∈ arrow Cls one ∧ anc R x y) ∧ anc R x z → anc R y z ∨ anc R z y := by
  rintro ⟨⟨hR, hxy⟩, hxz⟩
  exact anc_manyOne_cmp (mem_arrow_Cls_one.1 hR) hxy hxz

/-- ✱96·303. \[\begin{align}&\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.xR_{\unicode{x2217}}y.xR_{\unicode{x2217}}z.y \neq z.\supset:yR_{\text{po}}z.\lor.zR_{\text{po}}y\\ &[\text{*96·302.*91·542}]\end{align}\] -/
theorem pm96_303 {R : α → α → Prop} {x y z : α} :
    ((R ∈ arrow Cls one ∧ anc R x y) ∧ anc R x z) ∧ y ≠ z → po R y z ∨ po R z y := by
  rintro ⟨h, hne⟩
  rcases pm96_302 h with h1 | h1
  · rcases anc_iff_po.1 h1 with ⟨e, -⟩ | h2
    · exact absurd e hne
    · exact Or.inl h2
  · rcases anc_iff_po.1 h1 with ⟨e, -⟩ | h2
    · exact absurd e.symm hne
    · exact Or.inr h2

/-- ✱96·311. \(\vdash:R\in 1\rightarrow \text{Cls}.xR_{\unicode{x2217}}y.\supset.\overrightarrow{R}_{\unicode{x2217}}ʻy\subset \overrightarrow{R}_{\unicode{x2217}}ʻx\cup \overleftarrow{R}_{\unicode{x2217}}ʻx \quad[\text{*92·31}]\) -/
theorem pm96_311 {R : α → α → Prop} {x y : α} :
    R ∈ arrow one Cls ∧ anc R x y → refs (anc R) y ⊆ refs (anc R) x ∪ rels (anc R) x := by
  rintro ⟨hR, hxy⟩ z hz
  rcases anc_oneMany_cmp (mem_arrow_one_Cls.1 hR) hz hxy with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- ✱96·32. \(\vdash:R\in 1\rightarrow 1.xR_{\unicode{x2217}}y.\supset.\overrightarrow{R}_{\unicode{x2217}}ʻx\cup \overleftarrow{R}_{\unicode{x2217}}ʻx=\overrightarrow{R}_{\unicode{x2217}}ʻy\cup \overleftarrow{R}_{\unicode{x2217}}ʻy\) -/
theorem pm96_32 {R : α → α → Prop} {x y : α} :
    R ∈ arrow one one ∧ anc R x y →
      refs (anc R) x ∪ rels (anc R) x = refs (anc R) y ∪ rels (anc R) y := by
  rintro ⟨hR, hxy⟩
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
  ext z
  constructor
  · rintro (hz | hz)
    · exact Or.inl (anc_trans hz hxy)
    · rcases anc_manyOne_cmp h2 hxy hz with h | h
      · exact Or.inr h
      · exact Or.inl h
  · rintro (hz | hz)
    · rcases anc_oneMany_cmp h1 hz hxy with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact Or.inr (anc_trans hxy hz)

private theorem npow_manyOne_fixed {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z)
    {x : α} (hx : R x x) : ∀ n y, npow R n x y → y = x := by
  intro n
  induction n with
  | zero => exact fun y h => h.symm
  | succ n ih =>
    intro y h
    obtain ⟨a, hxa, hay⟩ := npow_succ_iff.1 h
    have : a = x := hR x a x ⟨hxa, hx⟩
    subst this
    exact ih y hay

/-- ✱96·33. \(\vdash:R\in \text{Cls}\rightarrow 1.xRx.\supset.\overleftarrow{R}_{\unicode{x2217}}ʻx=\iotaʻx\) -/
theorem pm96_33 {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one ∧ R x x → rels (anc R) x = ι x := by
  rintro ⟨hR, hxx⟩
  ext y
  constructor
  · intro hy
    obtain ⟨-, n, hn⟩ := anc_iff_npow.1 hy
    exact npow_manyOne_fixed (mem_arrow_Cls_one.1 hR) hxx n y hn
  · intro hy
    have e : y = x := hy
    subst e
    exact anc_refl ⟨y, Or.inl hxx⟩

/-- ✱96·331. \(\vdash:R\in \text{Cls}\rightarrow 1.xRy.yRx.\supset.\overleftarrow{R}_{\unicode{x2217}}ʻx=\iotaʻx\cup \iotaʻy\) -/
theorem pm96_331 {R : α → α → Prop} {x y : α} :
    (R ∈ arrow Cls one ∧ R x y) ∧ R y x → rels (anc R) x = ι x ∪ ι y := by
  rintro ⟨⟨hR, hxy⟩, hyx⟩
  have hR' := mem_arrow_Cls_one.1 hR
  ext z
  constructor
  · intro hz
    obtain ⟨-, n, hn⟩ := anc_iff_npow.1 hz
    induction n generalizing z with
    | zero =>
      have e : x = z := hn
      exact Or.inl e.symm
    | succ n ih =>
      obtain ⟨c, hc, hcz⟩ := hn
      rcases ih c (anc_iff_npow.2 ⟨⟨y, Or.inl hxy⟩, n, hc⟩) hc with e | e
      · have e' : c = x := e
        subst e'
        exact Or.inr (hR' c z y ⟨hcz, hxy⟩)
      · have e' : c = y := e
        subst e'
        exact Or.inl (hR' c z x ⟨hcz, hyx⟩)
  · rintro (h | h)
    · have e : z = x := h
      subst e
      exact anc_refl ⟨y, Or.inl hxy⟩
    · have e : z = y := h
      subst e
      exact R_sub_anc hxy

/-- ✱96·34. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\breve{R}_{\text{po}}ʻʻ\hat{z}(zR_{\text{po}}z)\subset \hat{z}(zR_{\text{po}}z)\) -/
theorem pm96_34 {R : α → α → Prop} :
    R ∈ arrow Cls one → (po R)˘ ʻʻ {z | po R z z} ⊆ {z | po R z z} := by
  rintro hR w ⟨z, hz, hzw⟩
  exact po_cyc_succ (mem_arrow_Cls_one.1 hR) hz hzw

/-- ✱96·341. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\breve{R}_{\text{po}}ʻʻI_{R}ʻx\subset I_{R}ʻx\) -/
theorem pm96_341 {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one → (po R)˘ ʻʻ IR R x ⊆ IR R x := by
  rintro hR w ⟨z, ⟨hxz, hz⟩, hzw⟩
  exact ⟨anc_trans hxz (po_sub_anc hzw), po_cyc_succ (mem_arrow_Cls_one.1 hR) hz hzw⟩

/-- ✱96·342. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\breve{R}_{\unicode{x2217}}ʻʻI_{R}ʻx\subset I_{R}ʻx \quad[\text{*96·341.*91·71}]\) -/
theorem pm96_342 {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one → ancCnv R ʻʻ IR R x ⊆ IR R x := by
  rintro hR w ⟨z, ⟨hxz, hz⟩, hzw⟩
  exact ⟨anc_trans hxz hzw, anc_cyc (mem_arrow_Cls_one.1 hR) hz hzw⟩

/-- ✱96·35. \[\begin{align}&\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:{\sim}(wR_{\text{po}}w).zR_{\text{po}}w.\supset.{\sim}(zR_{\text{po}}z)\\ &[\text{*96·34.Transp}]\end{align}\] -/
theorem pm96_35 {R : α → α → Prop} {z w : α} :
    R ∈ arrow Cls one → (¬ po R w w ∧ po R z w → ¬ po R z z) := by
  rintro hR ⟨hw, hzw⟩ hz
  exact hw (po_cyc_succ (mem_arrow_Cls_one.1 hR) hz hzw)

/-- ✱96·351. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.R_{\text{po}}ʻʻJ_{R}ʻx\cap \overleftarrow{R}_{\unicode{x2217}}ʻx\subset J_{R}ʻx\) -/
theorem pm96_351 {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one → po R ʻʻ JR R x ∩ rels (anc R) x ⊆ JR R x := by
  rintro hR y ⟨⟨w, hw, hyw⟩, hy⟩
  exact mem_JR.2 ⟨hy, fun hyy => (mem_JR.1 hw).2 (po_cyc_succ (mem_arrow_Cls_one.1 hR) hyy hyw)⟩

/-- ✱96·352. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.R_{\unicode{x2217}}ʻʻJ_{R}ʻx\cap \overleftarrow{R}_{\unicode{x2217}}ʻx\subset J_{R}ʻx \quad[\text{*91·543.*96·351}]\) -/
theorem pm96_352 {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one → anc R ʻʻ JR R x ∩ rels (anc R) x ⊆ JR R x := by
  rintro hR y ⟨⟨w, hw, hyw⟩, hy⟩
  exact mem_JR.2 ⟨hy, fun hyy => (mem_JR.1 hw).2 (anc_cyc (mem_arrow_Cls_one.1 hR) hyy hyw)⟩

private theorem pot_manyOne {R T : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z)
    (hT : T ∈ pot R) : ∀ x y z, T x y ∧ T x z → y = z := by
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 hT
  exact npow_manyOne hR _

/-- ✱96·4. \(\vdash:R\in \text{Cls}\rightarrow 1.S,\,T\in \text{Pot}ʻR.ySy.yTz.\supset.zSz\) -/
theorem pm96_4 {R S T : α → α → Prop} {y z : α} :
    ((R ∈ arrow Cls one ∧ (S ∈ pot R ∧ T ∈ pot R)) ∧ S y y) ∧ T y z → S z z := by
  rintro ⟨⟨⟨hR, hS, hT⟩, hyy⟩, hyz⟩
  have hc : S ⨾ T = T ⨾ S := pm94_6 (R := R) (S := R) rfl ⟨hS, hT⟩
  have h1 : (S ⨾ T) y z := ⟨y, hyy, hyz⟩
  rw [hc] at h1
  obtain ⟨w, hyw, hwz⟩ := h1
  have : w = z := pot_manyOne (mem_arrow_Cls_one.1 hR) hT y w z ⟨hyw, hyz⟩
  subst this
  exact hwz

/-- ✱96·401. \(\vdash:R\in \text{Cls}\rightarrow 1.S,\,T\in \text{Pot}ʻR.ySy.yTz.yRw.zRw.\supset.wSw.wTw\) -/
theorem pm96_401 {R S T : α → α → Prop} {y z w : α} :
    ((((R ∈ arrow Cls one ∧ (S ∈ pot R ∧ T ∈ pot R)) ∧ S y y) ∧ T y z) ∧ R y w) ∧ R z w →
      S w w ∧ T w w := by
  rintro ⟨⟨⟨⟨⟨hR, hS, hT⟩, hyy⟩, hyz⟩, hyw⟩, hzw⟩
  refine ⟨pm96_4 ⟨⟨⟨hR, hS, self_mem_pot R⟩, hyy⟩, hyw⟩, ?_⟩
  have h1 : (T ⨾ R) y w := ⟨z, hyz, hzw⟩
  rw [pot_comm hT] at h1
  obtain ⟨w', hyw', hw'w⟩ := h1
  have : w' = w := mem_arrow_Cls_one.1 hR y w' w ⟨hyw', hyw⟩
  subst this
  exact hw'w

/-- ✱96·402. \(\vdash:R\in \text{Cls}\rightarrow 1.T\in \text{Pot}ʻR.yRy.yTz.yRw.zRw.\supset.y=w.y=z\) -/
theorem pm96_402 {R T : α → α → Prop} {y z w : α} :
    ((((R ∈ arrow Cls one ∧ T ∈ pot R) ∧ R y y) ∧ T y z) ∧ R y w) ∧ R z w → y = w ∧ y = z := by
  rintro ⟨⟨⟨⟨⟨hR, hT⟩, hyy⟩, hyz⟩, hyw⟩, -⟩
  have hR' := mem_arrow_Cls_one.1 hR
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 hT
  exact ⟨hR' y y w ⟨hyy, hyw⟩, (npow_manyOne_fixed hR' hyy _ z hyz).symm⟩

/-- ✱96·403. \[\begin{align}\vdash:R\in \text{Cls}\rightarrow 1.S,\,T\in \text{Pot}ʻR.yS\mid Ry.yTz.yRw.&zRw.\supset.\\ &wSy.wSz.y=z\end{align}\] -/
theorem pm96_403 {R S T : α → α → Prop} {y z w : α} :
    ((((R ∈ arrow Cls one ∧ (S ∈ pot R ∧ T ∈ pot R)) ∧ (S ⨾ R) y y) ∧ T y z) ∧ R y w) ∧
      R z w → (S w y ∧ S w z) ∧ y = z := by
  rintro ⟨⟨⟨⟨⟨hR, hS, hT⟩, hyy⟩, hyz⟩, hyw⟩, hzw⟩
  have hR' := mem_arrow_Cls_one.1 hR
  have hwy : S w y := by
    have h1 := hyy
    rw [pot_comm hS] at h1
    obtain ⟨w', hyw', hw'y⟩ := h1
    have : w' = w := hR' y w' w ⟨hyw', hyw⟩
    subst this
    exact hw'y
  obtain ⟨a, rfl⟩ := mem_pot_npow.1 hS
  obtain ⟨b, rfl⟩ := mem_pot_npow.1 hT
  have e : z = y := cyc_common_succ hR' (p := a + 1) hyy hyz hzw hyw
  subst e
  exact ⟨⟨hwy, hwy⟩, rfl⟩

/-- ✱96·41. \(\vdash:R\in \text{Cls}\rightarrow 1.S,\,T\in \text{Pot}ʻR.ySy.yTz.yRw.zRw.\supset.y=z\) -/
theorem pm96_41 {R S T : α → α → Prop} {y z w : α} :
    ((((R ∈ arrow Cls one ∧ (S ∈ pot R ∧ T ∈ pot R)) ∧ S y y) ∧ T y z) ∧ R y w) ∧ R z w →
      y = z := by
  rintro ⟨⟨⟨⟨⟨hR, hS, hT⟩, hyy⟩, hyz⟩, hyw⟩, hzw⟩
  obtain ⟨a, rfl⟩ := mem_pot_npow.1 hS
  obtain ⟨b, rfl⟩ := mem_pot_npow.1 hT
  exact (cyc_common_succ (mem_arrow_Cls_one.1 hR) hyy hyz hzw hyw).symm

/-- ✱96·42. \(\vdash:R\in \text{Cls}\rightarrow 1.yRw.zRw.yR_{\text{po}}z.\supset.zR_{\text{po}}z\) -/
theorem pm96_42 {R : α → α → Prop} {y z w : α} :
    ((R ∈ arrow Cls one ∧ R y w) ∧ R z w) ∧ po R y z → po R z z := by
  rintro ⟨⟨⟨hR, hyw⟩, hzw⟩, hyz⟩
  obtain ⟨n, hn⟩ := npow_succ_of_po hyz
  obtain ⟨a, hya, haz⟩ := npow_succ_iff.1 hn
  have : a = w := mem_arrow_Cls_one.1 hR y a w ⟨hya, hyw⟩
  subst this
  exact po_of_npow_succ (npow_succ_iff.2 ⟨a, hzw, haz⟩)

/-- ✱96·421. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.y,\,z\in \overleftarrow{R}_{\unicode{x2217}}ʻx.yRw.zRw.y \neq z.\supset:yR_{\text{po}}y.\lor.zR_{\text{po}}z\) -/
theorem pm96_421 {R : α → α → Prop} {x y z w : α} :
    (((R ∈ arrow Cls one ∧ (y ∈ rels (anc R) x ∧ z ∈ rels (anc R) x)) ∧ R y w) ∧ R z w) ∧
      y ≠ z → po R y y ∨ po R z z := by
  rintro ⟨⟨⟨⟨hR, hy, hz⟩, hyw⟩, hzw⟩, hne⟩
  rcases anc_manyOne_cmp (mem_arrow_Cls_one.1 hR) hy hz with h | h
  · rcases anc_iff_po.1 h with ⟨e, -⟩ | h'
    · exact absurd e hne
    · exact Or.inr (pm96_42 ⟨⟨⟨hR, hyw⟩, hzw⟩, h'⟩)
  · rcases anc_iff_po.1 h with ⟨e, -⟩ | h'
    · exact absurd e.symm hne
    · exact Or.inl (pm96_42 ⟨⟨⟨hR, hzw⟩, hyw⟩, h'⟩)

/-- ✱96·431. \(\vdash:R\in \text{Cls}\rightarrow 1.y\in J_{R}ʻx.z\in I_{R}ʻx.\supset.yR_{\text{po}}z\) -/
theorem pm96_431 {R : α → α → Prop} {x y z : α} :
    (R ∈ arrow Cls one ∧ y ∈ JR R x) ∧ z ∈ IR R x → po R y z := by
  rintro ⟨⟨hR, hy⟩, hz⟩
  obtain ⟨hy, hyn⟩ := mem_JR.1 hy
  rcases anc_manyOne_cmp (mem_arrow_Cls_one.1 hR) hy hz.1 with h | h
  · rcases anc_iff_po.1 h with ⟨rfl, -⟩ | h'
    · exact absurd hz.2 hyn
    · exact h'
  · exact absurd (anc_cyc (mem_arrow_Cls_one.1 hR) hz.2 h) hyn

/-- ✱96·432. \(\vdash:R\in \text{Cls}\rightarrow 1.y,z\in I_{R}ʻx.yRw.zRw.\supset.y=z\) -/
theorem pm96_432 {R : α → α → Prop} {x y z w : α} :
    ((R ∈ arrow Cls one ∧ (y ∈ IR R x ∧ z ∈ IR R x)) ∧ R y w) ∧ R z w → y = z := by
  rintro ⟨⟨⟨hR, hy, hz⟩, hyw⟩, hzw⟩
  have hR' := mem_arrow_Cls_one.1 hR
  rcases anc_manyOne_cmp hR' hy.1 hz.1 with h | h
  · obtain ⟨-, n, hn⟩ := anc_iff_npow.1 h
    obtain ⟨p, hp⟩ := npow_succ_of_po hy.2
    exact (cyc_common_succ hR' hp hn hzw hyw).symm
  · obtain ⟨-, n, hn⟩ := anc_iff_npow.1 h
    obtain ⟨p, hp⟩ := npow_succ_of_po hz.2
    exact cyc_common_succ hR' hp hn hyw hzw

/-- ✱96·44. \[\begin{align}&\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.y,z\in \overleftarrow{R}_{\unicode{x2217}}ʻx.yRw.zRw.y \neq z.\supset:y\in I_{R}ʻx.\lor.z\in I_{R}ʻx\\ &[\text{*96·421·1}]\end{align}\] -/
theorem pm96_44 {R : α → α → Prop} {x y z w : α} :
    (((R ∈ arrow Cls one ∧ (y ∈ rels (anc R) x ∧ z ∈ rels (anc R) x)) ∧ R y w) ∧ R z w) ∧
      y ≠ z → y ∈ IR R x ∨ z ∈ IR R x := by
  intro h
  obtain ⟨⟨⟨⟨-, hy, hz⟩, -⟩, -⟩, -⟩ := id h
  rcases pm96_421 h with h' | h'
  · exact Or.inl ⟨hy, h'⟩
  · exact Or.inr ⟨hz, h'⟩

/-- ✱96·441. \[\begin{align}\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.y,z\in &\overleftarrow{R}_{\unicode{x2217}}ʻx.yRw.zRw.y \neq z.\supset:\\ &w\in I_{R}ʻx:y\in J_{R}ʻx.z\in I_{R}ʻx.\lor.y\in I_{R}ʻx.z\in J_{R}ʻx\end{align}\] -/
theorem pm96_441 {R : α → α → Prop} {x y z w : α} :
    (((R ∈ arrow Cls one ∧ (y ∈ rels (anc R) x ∧ z ∈ rels (anc R) x)) ∧ R y w) ∧ R z w) ∧
      y ≠ z →
      w ∈ IR R x ∧ ((y ∈ JR R x ∧ z ∈ IR R x) ∨ (y ∈ IR R x ∧ z ∈ JR R x)) := by
  intro h
  obtain ⟨⟨⟨⟨hR, hy, hz⟩, hyw⟩, hzw⟩, hne⟩ := id h
  rcases pm96_44 h with hyI | hzI
  · refine ⟨pm96_342 hR ⟨y, hyI, R_sub_anc hyw⟩, Or.inr ⟨hyI, mem_JR.2 ⟨hz, fun hzz => ?_⟩⟩⟩
    exact hne (pm96_432 ⟨⟨⟨hR, hyI, ⟨hz, hzz⟩⟩, hyw⟩, hzw⟩)
  · refine ⟨pm96_342 hR ⟨z, hzI, R_sub_anc hzw⟩, Or.inl ⟨mem_JR.2 ⟨hy, fun hyy => ?_⟩, hzI⟩⟩
    exact hne (pm96_432 ⟨⟨⟨hR, ⟨hy, hyy⟩, hzI⟩, hyw⟩, hzw⟩)

/-- ✱96·442. \(\vdash:R\in \text{Cls}\rightarrow 1.y,\,z\in J_{R}ʻx.yRw.zRw.\supset.y=z \quad[\text{*96·44.Transp}]\) -/
theorem pm96_442 {R : α → α → Prop} {x y z w : α} :
    ((R ∈ arrow Cls one ∧ (y ∈ JR R x ∧ z ∈ JR R x)) ∧ R y w) ∧ R z w → y = z := by
  rintro ⟨⟨⟨hR, hy, hz⟩, hyw⟩, hzw⟩
  by_contra hne
  rcases pm96_44 ⟨⟨⟨⟨hR, (mem_JR.1 hy).1, (mem_JR.1 hz).1⟩, hyw⟩, hzw⟩, hne⟩ with h | h
  · exact (mem_JR.1 hy).2 h.2
  · exact (mem_JR.1 hz).2 h.2

/-- ✱96·45. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.(J_{R}ʻx)\upharpoonleft R,(I_{R}ʻx)\upharpoonleft R\in 1\rightarrow 1 \quad[\text{*96·442·432}]\) -/
theorem pm96_45 {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one → JR R x ◁ R ∈ arrow one one ∧ IR R x ◁ R ∈ arrow one one := by
  intro hR
  have hR' := mem_arrow_Cls_one.1 hR
  refine ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, mem_arrow_one_one.2 ⟨?_, ?_⟩⟩
  · rintro y z w ⟨⟨hy, hyw⟩, ⟨hz, hzw⟩⟩
    exact pm96_442 ⟨⟨⟨hR, hy, hz⟩, hyw⟩, hzw⟩
  · rintro y z w ⟨⟨-, hyz⟩, ⟨-, hyw⟩⟩
    exact hR' y z w ⟨hyz, hyw⟩
  · rintro y z w ⟨⟨hy, hyw⟩, ⟨hz, hzw⟩⟩
    exact pm96_432 ⟨⟨⟨hR, hy, hz⟩, hyw⟩, hzw⟩
  · rintro y z w ⟨⟨-, hyz⟩, ⟨-, hyw⟩⟩
    exact hR' y z w ⟨hyz, hyw⟩

/-- ✱96·451. \[\begin{align}&\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1:J_{R}ʻx=\Lambda.\lor.I_{R}ʻx=\Lambda:\supset.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R\in 1\rightarrow 1\\ &[\text{*96·45·102}]\end{align}\] -/
theorem pm96_451 {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one ∧ (JR R x = Λ ∨ IR R x = Λ) → rels (anc R) x ◁ R ∈ arrow one one := by
  rintro ⟨hR, hJI⟩
  rw [Null_eq_empty] at hJI
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro y z w ⟨⟨hy, hyw⟩, ⟨hz, hzw⟩⟩
    by_contra hne
    obtain ⟨-, h⟩ := pm96_441 ⟨⟨⟨⟨hR, hy, hz⟩, hyw⟩, hzw⟩, hne⟩
    rcases hJI with hJ | hI
    · rcases h with ⟨h1, -⟩ | ⟨-, h1⟩
      · rw [hJ] at h1
        exact h1
      · rw [hJ] at h1
        exact h1
    · rcases h with ⟨-, h1⟩ | ⟨h1, -⟩
      · rw [hI] at h1
        exact h1
      · rw [hI] at h1
        exact h1
  · rintro y z w ⟨⟨-, hyz⟩, ⟨-, hyw⟩⟩
    exact mem_arrow_Cls_one.1 hR y z w ⟨hyz, hyw⟩

/-- ✱96·452. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:\exists !J_{R}ʻx.\equiv.x\in J_{R}ʻx\) -/
theorem pm96_452 {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one → ((JR R x).Nonempty ↔ x ∈ JR R x) := by
  intro hR
  refine ⟨?_, fun h => ⟨x, h⟩⟩
  rintro ⟨y, hy⟩
  obtain ⟨hxy, hyn⟩ := mem_JR.1 hy
  exact mem_JR.2 ⟨anc_refl (anc_left_fld hxy),
    fun hxx => hyn (anc_cyc (mem_arrow_Cls_one.1 hR) hxx hxy)⟩

/-- ✱96·453. \(\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1:xR_{\text{po}}x.\lor.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R_{\text{po}}\unicode{x2abd}J:\supset.(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R\in 1\rightarrow 1\) -/
theorem pm96_453 {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one ∧ (po R x x ∨ rels (anc R) x ◁ po R ⪽ J) →
      rels (anc R) x ◁ R ∈ arrow one one := by
  rintro ⟨hR, h | h⟩
  · refine pm96_451 ⟨hR, Or.inl ?_⟩
    rw [Null_eq_empty]
    ext y
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hy
    obtain ⟨hxy, hyn⟩ := mem_JR.1 hy
    exact hyn (anc_cyc (mem_arrow_Cls_one.1 hR) h hxy)
  · exact pm96_451 ⟨hR, Or.inr ((pm96_104 (R := R) (x := x)).1.2 h)⟩

/-- ✱96·46. \(\vdash:R\in \text{Cls}\rightarrow 1.y,y'\in J_{R}ʻx.\breve{R}ʻy,\breve{R}ʻy'\in I_{R}ʻx.\supset.y=y'\) -/
theorem pm96_46 {R : α → α → Prop} {x y y' : α} :
    ((R ∈ arrow Cls one ∧ (y ∈ JR R x ∧ y' ∈ JR R x)) ∧ Desc R˘ y (fun u => u ∈ IR R x)) ∧
      Desc R˘ y' (fun u => u ∈ IR R x) → y = y' := by
  rintro ⟨⟨⟨hR, hy, hy'⟩, hd⟩, hd'⟩
  have hR' := mem_arrow_Cls_one.1 hR
  obtain ⟨w, hyw, hwI⟩ := desc_cnv_exists hd
  obtain ⟨w', hyw', hw'I⟩ := desc_cnv_exists hd'
  obtain ⟨hy, hyn⟩ := mem_JR.1 hy
  obtain ⟨hy', hyn'⟩ := mem_JR.1 hy'
  rcases anc_manyOne_cmp hR' hy hy' with h | h
  · rcases anc_iff_po.1 h with ⟨e, -⟩ | h'
    · exact e
    · obtain ⟨n, hn⟩ := npow_succ_of_po h'
      obtain ⟨a, hya, han⟩ := npow_succ_iff.1 hn
      have : a = w := hR' y a w ⟨hya, hyw⟩
      subst this
      exact absurd (anc_cyc hR' hwI.2 (anc_of_npow ⟨y, Or.inr hya⟩ han)) hyn'
  · rcases anc_iff_po.1 h with ⟨e, -⟩ | h'
    · exact e.symm
    · obtain ⟨n, hn⟩ := npow_succ_of_po h'
      obtain ⟨a, hya, han⟩ := npow_succ_iff.1 hn
      have : a = w' := hR' y' a w' ⟨hya, hyw'⟩
      subst this
      exact absurd (anc_cyc hR' hw'I.2 (anc_of_npow ⟨y', Or.inr hya⟩ han)) hyn

/-- The last term of `J_R'x` is the term of `J_R'x` whose successor lies in `I_R'x`. -/
private theorem maxJ_unique {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z)
    {x y w : α} (hy : y ∈ JR R x) (hyw : R y w) (hwI : w ∈ IR R x) :
    ∀ u, maxP R u (JR R x) ↔ u = y := by
  intro u
  rw [maxP_apply']
  obtain ⟨hy, hyn⟩ := mem_JR.1 hy
  constructor
  · rintro ⟨⟨hu, -⟩, hmax⟩
    obtain ⟨hu, hun⟩ := mem_JR.1 hu
    rcases anc_manyOne_cmp hR hu hy with h | h
    · rcases anc_iff_po.1 h with ⟨e, -⟩ | h'
      · exact e
      · obtain ⟨n, hn⟩ := npow_succ_of_po h'
        obtain ⟨a, hua, han⟩ := npow_succ_iff.1 hn
        refine absurd ⟨a, mem_JR.2 ⟨anc_tail hu hua, fun haa => hyn ?_⟩, hua⟩ hmax
        exact anc_cyc hR haa (anc_of_npow ⟨u, Or.inr hua⟩ han)
    · rcases anc_iff_po.1 h with ⟨e, -⟩ | h'
      · exact e.symm
      · obtain ⟨n, hn⟩ := npow_succ_of_po h'
        obtain ⟨a, hya, han⟩ := npow_succ_iff.1 hn
        have : a = w := hR y a w ⟨hya, hyw⟩
        subst this
        exact absurd (anc_cyc hR hwI.2 (anc_of_npow ⟨y, Or.inr hya⟩ han)) hun
  · rintro rfl
    refine ⟨⟨mem_JR.2 ⟨hy, hyn⟩, ⟨w, Or.inl hyw⟩⟩, ?_⟩
    rintro ⟨v, hv, huv⟩
    have : v = w := hR u v w ⟨huv, hyw⟩
    subst this
    exact (mem_JR.1 hv).2 hwI.2

/-- ✱96·461. \(\vdash:R\in \text{Cls}\rightarrow 1.y\in J_{R}ʻx.\breve{R}ʻy\in I_{R}ʻx.\supset.y=\text{max}_{R}ʻJ_{R}ʻx\) -/
theorem pm96_461 {R : α → α → Prop} {x y : α} :
    (R ∈ arrow Cls one ∧ y ∈ JR R x) ∧ Desc R˘ y (fun u => u ∈ IR R x) →
      Desc (maxP R) (JR R x) (fun u => y = u) := by
  rintro ⟨⟨hR, hy⟩, hd⟩
  obtain ⟨w, hyw, hwI⟩ := desc_cnv_exists hd
  exact (TheIs_iff_of_unique (maxJ_unique (mem_arrow_Cls_one.1 hR) hy hyw hwI)).2 rfl

private theorem IR_closed {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z) {x z w : α}
    (hz : z ∈ IR R x) (hzw : R z w) : w ∈ IR R x :=
  ⟨anc_tail hz.1 hzw, anc_cyc hR hz.2 (R_sub_anc hzw)⟩

/-- Under `Cls → 1`: if `y ∈ J`, `z ∈ I` and `yRw . zRw`, then `max_R'J = y`, `R̆'max_R'J = w`,
`{(I_R'x) ↿ R}'R̆'max_R'J = z`, in the forms used below. -/
private theorem maxJ_facts {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z)
    {x y z w : α} (hy : y ∈ JR R x) (hz : z ∈ IR R x) (hyw : R y w) (hzw : R z w)
    (ψ : α → Prop) :
    (Desc (maxP R) (JR R x) ψ ↔ ψ y) ∧ (Desc2 R˘ (maxP R) (JR R x) ψ ↔ ψ w) ∧
      (TheIs (fun u => Desc2 R˘ (maxP R) (JR R x) (fun v => (IR R x ◁ R) u v)) ψ ↔ ψ z) := by
  have hwI : w ∈ IR R x := IR_closed hR hz hzw
  have hmax := maxJ_unique hR hy hyw hwI
  have h1 : ∀ φ : α → Prop, Desc (maxP R) (JR R x) φ ↔ φ y :=
    fun φ => TheIs_iff_of_unique hmax
  have h2 : ∀ φ : α → Prop, Desc2 R˘ (maxP R) (JR R x) φ ↔ φ w := by
    intro φ
    rw [desc2_iff, h1]
    exact desc_cnv_of hR hyw φ
  refine ⟨h1 ψ, h2 ψ, TheIs_iff_of_unique fun u => ?_⟩
  rw [h2]
  constructor
  · rintro ⟨hu, huw⟩
    exact pm96_432 (x := x) ⟨⟨⟨mem_arrow_Cls_one.2 hR, hu, hz⟩, huw⟩, hzw⟩
  · rintro rfl
    exact ⟨hz, hzw⟩

/-- ✱96·462. \[\begin{align}\vdash:R &\in \text{Cls}\rightarrow 1.y\in J_{R}ʻx.z\in I_{R}ʻx.yRw.zRw.\supset.\\ & y=\text{max}_{R}ʻJ_{R}ʻx.w=\breve{R}ʻ\text{max}_{R}ʻJ_{R}ʻx.z=\{(I_{R}ʻx)\upharpoonleft R\}ʻ\breve{R}ʻ\text{max}_{R}ʻJ_{R}ʻx\end{align}\]

**Status.** proved (reading): `z = {(I_R'x) ↿ R}'R̆'max_R'J_R'x` contains three
descriptive functions; it is read by iterating ✱30·02 (`A'B'C'y = A'(B'C'y)`, the outer
description with the larger scope): `TheIs (fun u => Desc2 R˘ (maxP R) (JR R x)
(fun v => (IR R x ◁ R) u v)) (fun u => z = u)`. -/
theorem pm96_462 {R : α → α → Prop} {x y z w : α} :
    (((R ∈ arrow Cls one ∧ y ∈ JR R x) ∧ z ∈ IR R x) ∧ R y w) ∧ R z w →
      (Desc (maxP R) (JR R x) (fun u => y = u) ∧
        Desc2 R˘ (maxP R) (JR R x) (fun u => w = u)) ∧
        TheIs (fun u => Desc2 R˘ (maxP R) (JR R x) (fun v => (IR R x ◁ R) u v)) (fun u => z = u) := by
  rintro ⟨⟨⟨⟨hR, hy⟩, hz⟩, hyw⟩, hzw⟩
  have hR' := mem_arrow_Cls_one.1 hR
  exact ⟨⟨(maxJ_facts hR' hy hz hyw hzw _).1.2 rfl, (maxJ_facts hR' hy hz hyw hzw _).2.1.2 rfl⟩,
    (maxJ_facts hR' hy hz hyw hzw _).2.2.2 rfl⟩

/-- ✱96·47. \[\begin{align}\vdash\colon\ldotp R\in \text{Cls}\rightarrow &1.y,z\in \overleftarrow{R}_{\unicode{x2217}}ʻx.yRw.zRw.y \neq z.\supset:w=\breve{R}ʻ\text{max}_{R}ʻJ_{R}ʻx:\\ &y = \text{max}_{R}ʻJ_{R}ʻx.z=\{(I_{R}ʻx)\upharpoonleft R\}ʻ\breve{R}ʻ\text{max}_{R}ʻJ_{R}ʻx.\lor.\\ &z = \text{max}_{R}ʻJ_{R}ʻx.y=\{(I_{R}ʻx)\upharpoonleft R\}ʻ\breve{R}ʻ\text{max}_{R}ʻJ_{R}ʻx\\ \quad[\text{*96·441·462}]\end{align}\]

**Status.** proved (reading): the triple descriptions `{(I_R'x) ↿ R}'R̆'max_R'J_R'x` are
read by iterating ✱30·02, as in ✱96·462. -/
theorem pm96_47 {R : α → α → Prop} {x y z w : α} :
    (((R ∈ arrow Cls one ∧ (y ∈ rels (anc R) x ∧ z ∈ rels (anc R) x)) ∧ R y w) ∧ R z w) ∧
      y ≠ z →
      Desc2 R˘ (maxP R) (JR R x) (fun u => w = u) ∧
        ((Desc (maxP R) (JR R x) (fun u => y = u) ∧
          TheIs (fun u => Desc2 R˘ (maxP R) (JR R x) (fun v => (IR R x ◁ R) u v))
            (fun u => z = u)) ∨
        (Desc (maxP R) (JR R x) (fun u => z = u) ∧
          TheIs (fun u => Desc2 R˘ (maxP R) (JR R x) (fun v => (IR R x ◁ R) u v))
            (fun u => y = u))) := by
  intro h
  obtain ⟨⟨⟨⟨hR, -, -⟩, hyw⟩, hzw⟩, -⟩ := id h
  have hR' := mem_arrow_Cls_one.1 hR
  rcases (pm96_441 h).2 with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · have F := maxJ_facts hR' hy hz hyw hzw
    exact ⟨(F _).2.1.2 rfl, Or.inl ⟨(F _).1.2 rfl, (F _).2.2.2 rfl⟩⟩
  · have F := maxJ_facts hR' hz hy hzw hyw
    exact ⟨(F _).2.1.2 rfl, Or.inr ⟨(F _).1.2 rfl, (F _).2.2.2 rfl⟩⟩

/-- Under `Cls → 1`, a member of `I_R'x` has an immediate predecessor in `I_R'x`. -/
private theorem IR_pred {R : α → α → Prop} {x w : α} (hw : w ∈ IR R x) :
    ∃ u, u ∈ IR R x ∧ R u w := by
  obtain ⟨p, hp⟩ := npow_succ_of_po hw.2
  obtain ⟨u, hwu, huw⟩ := hp
  refine ⟨u, ⟨anc_trans hw.1 (anc_of_npow (anc_fld_right hw.1) hwu), ?_⟩, huw⟩
  exact po_of_npow_succ (npow_succ_iff.2 ⟨w, huw, hwu⟩)

/-- ✱96·472. \(\vdash:R\in \text{Cls}\rightarrow 1.\exists !J_{R}ʻx.\exists !I_{R}ʻx.\supset.(\exists y).y\in J_{R}ʻx.\breve{R}ʻy\in I_{R}ʻx\) -/
theorem pm96_472 {R : α → α → Prop} {x : α} :
    (R ∈ arrow Cls one ∧ (JR R x).Nonempty) ∧ (IR R x).Nonempty →
      ∃ y, y ∈ JR R x ∧ Desc R˘ y (fun u => u ∈ IR R x) := by
  rintro ⟨⟨hR, hJ⟩, z, hz⟩
  have hR' := mem_arrow_Cls_one.1 hR
  have hx := (pm96_452 hR).1 hJ
  obtain ⟨-, n, hn⟩ := anc_iff_npow.1 hz.1
  have key : ∀ n y, y ∈ JR R x → npow R n y z → ∃ y', y' ∈ JR R x ∧ ∃ w, R y' w ∧ w ∈ IR R x := by
    intro n
    induction n with
    | zero =>
      intro y hy h
      have e : y = z := h
      subst e
      exact absurd hz.2 (mem_JR.1 hy).2
    | succ n ih =>
      intro y hy h
      obtain ⟨a, hya, han⟩ := npow_succ_iff.1 h
      have ha : anc R x a := anc_tail (mem_JR.1 hy).1 hya
      by_cases haa : po R a a
      · exact ⟨y, hy, a, hya, ha, haa⟩
      · exact ih a (mem_JR.2 ⟨ha, haa⟩) han
  obtain ⟨y, hy, w, hyw, hwI⟩ := key n x hx hn
  exact ⟨y, hy, (desc_cnv_of hR' hyw _).2 hwI⟩

/-- ✱96·473. \[\begin{align}&\vdash:R\in \text{Cls}\rightarrow 1.\exists !J_{R}ʻx.\exists !I_{R}ʻx.\supset.\text{E}!\text{max}_{R}ʻJ_{R}ʻx.\text{E}!\breve{R}ʻ\text{max}_{R}ʻJ_{R}ʻx\\ &[\text{*96·461·472}]\end{align}\] -/
theorem pm96_473 {R : α → α → Prop} {x : α} :
    (R ∈ arrow Cls one ∧ (JR R x).Nonempty) ∧ (IR R x).Nonempty →
      EDesc (maxP R) (JR R x) ∧ EBang (fun u => Desc (maxP R) (JR R x) (fun m => R˘ u m)) := by
  intro h
  have hR' := mem_arrow_Cls_one.1 h.1.1
  obtain ⟨y, hy, hd⟩ := pm96_472 h
  obtain ⟨w, hyw, hwI⟩ := desc_cnv_exists hd
  have hmax := maxJ_unique hR' hy hyw hwI
  exact ⟨⟨y, hmax⟩, ⟨w, fun u => (TheIs_iff_of_unique (ψ := fun m => R˘ u m) hmax).trans
    ⟨fun hu => hR' y u w ⟨hu, hyw⟩, fun e => e ▸ hyw⟩⟩⟩

/-- ✱96·474. \[\begin{align}\vdash:&R\in \text{Cls}\rightarrow 1.w=\breve{R}ʻ\text{max}_{R}ʻJ_{R}ʻx.\supset.\\ &\text{E}!\{(I_{R}ʻx)\upharpoonleft R\}ʻw.\text{E}!\text{max}_{R}ʻJ_{R}ʻx.\{(J_{R}ʻx)\upharpoonleft R\}ʻw=\text{max}_{R}ʻJ_{R}ʻx\end{align}\] -/
theorem pm96_474 {R : α → α → Prop} {x w : α} :
    R ∈ arrow Cls one ∧ Desc2 R˘ (maxP R) (JR R x) (fun u => w = u) →
      (EDesc (IR R x ◁ R) w ∧ EDesc (maxP R) (JR R x)) ∧
        Desc (JR R x ◁ R) w (fun u => Desc (maxP R) (JR R x) (fun m => u = m)) := by
  rintro ⟨hR, hd⟩
  have hR' := mem_arrow_Cls_one.1 hR
  rw [desc2_iff] at hd
  obtain ⟨m, hm, hmw⟩ := hd
  obtain ⟨w, hmw', hww⟩ := desc_cnv_exists hmw
  subst hww
  have hmJ : m ∈ JR R x := ((maxP_apply' R m _).1 ((hm m).2 rfl)).1.1
  have hmax := (maxP_apply' R m _).1 ((hm m).2 rfl)
  have hwI : w ∈ IR R x := by
    refine ⟨anc_tail (mem_JR.1 hmJ).1 hmw', ?_⟩
    by_contra hn
    exact hmax.2 ⟨w, mem_JR.2 ⟨anc_tail (mem_JR.1 hmJ).1 hmw', hn⟩, hmw'⟩
  obtain ⟨u, huI, huw⟩ := IR_pred hwI
  refine ⟨⟨⟨u, fun v => ⟨fun ⟨hv, hvw⟩ => pm96_432 ⟨⟨⟨hR, hv, huI⟩, hvw⟩, huw⟩,
    fun e => e ▸ ⟨huI, huw⟩⟩⟩, ⟨m, hm⟩⟩, ?_⟩
  refine (TheIs_iff_of_unique (b := m) fun v => ⟨fun ⟨hv, hvw⟩ =>
    pm96_442 ⟨⟨⟨hR, hv, hmJ⟩, hvw⟩, hmw'⟩, fun e => e ▸ ⟨hmJ, hmw'⟩⟩).2 ?_
  exact (TheIs_iff_of_unique hm).2 rfl

/-- ✱96·475. \[\begin{align}&\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1.\supset:\text{E}!\breve{R}ʻ\text{max}_{R}ʻJ_{R}ʻx.\equiv.\exists !J_{R}ʻx.\exists !I_{R}ʻx\\ &[\text{*96·473·474}]\end{align}\] -/
theorem pm96_475 {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one →
      (EBang (fun u => Desc (maxP R) (JR R x) (fun m => R˘ u m)) ↔
        (JR R x).Nonempty ∧ (IR R x).Nonempty) := by
  intro hR
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨m, hm, hmw⟩ := (hw w).2 rfl
    have hmax := (maxP_apply' R m _).1 ((hm m).2 rfl)
    have hmJ := hmax.1.1
    refine ⟨⟨m, hmJ⟩, w, anc_tail (mem_JR.1 hmJ).1 hmw, ?_⟩
    by_contra hn
    exact hmax.2 ⟨w, mem_JR.2 ⟨anc_tail (mem_JR.1 hmJ).1 hmw, hn⟩, hmw⟩
  · rintro ⟨hJ, hI⟩
    exact (pm96_473 ⟨⟨hR, hJ⟩, hI⟩).2

/-- ✱96·48. \[\begin{align}\vdash\colon\ldotp R &\in \text{Cls}\rightarrow 1.S=(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R.w\in \overleftarrow{R}_{\text{po}}ʻx.\supset:\\ &{\sim}(w=\breve{R}ʻ\text{max}_{R}ʻJ_{R}ʻx).\equiv.\overrightarrow{S}ʻw\in 1:w=\breve{R}ʻ\text{max}_{R}ʻJ_{R}ʻx.\equiv.\overrightarrow{S}ʻw\in 2\end{align}\] -/
theorem pm96_48 {R S : α → α → Prop} {x w : α} :
    (R ∈ arrow Cls one ∧ S = rels (anc R) x ◁ R) ∧ w ∈ rels (po R) x →
      (¬ Desc2 R˘ (maxP R) (JR R x) (fun u => w = u) ↔ refs S w ∈ one) ∧
        (Desc2 R˘ (maxP R) (JR R x) (fun u => w = u) ↔ refs S w ∈ two) := by
  rintro ⟨⟨hR, rfl⟩, hw⟩
  have hR' := mem_arrow_Cls_one.1 hR
  have hex : ∀ A : Set α, A ∈ one → A ∉ two := by
    rintro A ⟨a, rfl⟩ ⟨b, c, hbc, hA⟩
    have hb : b ∈ ι a := by rw [hA]; exact Or.inl rfl
    have hc : c ∈ ι a := by rw [hA]; exact Or.inr rfl
    exact hbc ((hb : b = a).trans (hc : c = a).symm)
  have ha : Desc2 R˘ (maxP R) (JR R x) (fun u => w = u) → refs (rels (anc R) x ◁ R) w ∈ two := by
    intro hd
    obtain ⟨⟨u, hu⟩, ⟨m, hm⟩⟩ := (pm96_474 ⟨hR, hd⟩).1
    rw [desc2_iff] at hd
    obtain ⟨m', hm', hmw⟩ := hd
    obtain ⟨w, hmw', hww⟩ := desc_cnv_exists hmw
    subst hww
    have hmax := (maxP_apply' R m' _).1 ((hm' m').2 rfl)
    have hmJ := hmax.1.1
    obtain ⟨huI, huw⟩ := (hu u).2 rfl
    refine ⟨m', u, fun e => ?_, ?_⟩
    · subst e
      exact (mem_JR.1 hmJ).2 huI.2
    · ext v
      constructor
      · rintro ⟨hv, hvw⟩
        by_cases hvv : po R v v
        · exact Or.inr ((hu v).1 ⟨⟨hv, hvv⟩, hvw⟩)
        · exact Or.inl (pm96_442 ⟨⟨⟨hR, mem_JR.2 ⟨hv, hvv⟩, hmJ⟩, hvw⟩, hmw'⟩)
      · rintro (e | e)
        · have e' : v = m' := e
          subst e'
          exact ⟨(mem_JR.1 hmJ).1, hmw'⟩
        · have e' : v = u := e
          subst e'
          exact ⟨huI.1, huw⟩
  have hb : ¬ Desc2 R˘ (maxP R) (JR R x) (fun u => w = u) → refs (rels (anc R) x ◁ R) w ∈ one := by
    intro hnd
    obtain ⟨t, hxt, htw⟩ := po_iff_anc_comp.1 hw
    refine mem_one_iff.2 ⟨t, fun v => ⟨?_, fun e => e ▸ ⟨hxt, htw⟩⟩⟩
    rintro ⟨hv, hvw⟩
    by_contra hne
    exact hnd (pm96_47 ⟨⟨⟨⟨hR, hv, hxt⟩, hvw⟩, htw⟩, hne⟩).1
  refine ⟨⟨hb, fun h1 hd => hex _ h1 (ha hd)⟩, ⟨ha, fun h2 => ?_⟩⟩
  by_contra hnd
  exact hex _ (hb hnd) h2

/-- ✱96·49. \[\begin{align}\vdash\colon\colon R\in \text{Cls}\rightarrow 1.x\in \text{D}ʻ&R.\supset\colon\ldotp \\ &(\overleftarrow{R}_{\unicode{x2217}}ʻx)\upharpoonleft R\in 1\rightarrow 1.\equiv:I_{R}ʻx=\Lambda.\lor.J_{R}ʻx=\Lambda\end{align}\] -/
theorem pm96_49 {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one ∧ x ∈ dom R →
      (rels (anc R) x ◁ R ∈ arrow one one ↔ IR R x = Λ ∨ JR R x = Λ) := by
  rintro ⟨hR, -⟩
  constructor
  · intro h
    rw [Null_eq_empty]
    by_contra hne
    rw [not_or] at hne
    obtain ⟨y, hy, hd⟩ := pm96_472 ⟨⟨hR, Set.nonempty_iff_ne_empty.2 hne.2⟩, Set.nonempty_iff_ne_empty.2 hne.1⟩
    obtain ⟨w, hyw, hwI⟩ := desc_cnv_exists hd
    obtain ⟨u, huI, huw⟩ := IR_pred hwI
    have e : y = u := (mem_arrow_one_one.1 h).1 y u w ⟨⟨(mem_JR.1 hy).1, hyw⟩, ⟨huI.1, huw⟩⟩
    subst e
    exact (mem_JR.1 hy).2 huI.2
  · rintro (h | h)
    · exact pm96_451 ⟨hR, Or.inr h⟩
    · exact pm96_451 ⟨hR, Or.inl h⟩

/-- ✱96·491. \(\vdash\colon\ldotp R\in 1\rightarrow 1.\supset:I_{R}ʻx=\Lambda.\lor.J_{R}ʻx=\Lambda\) -/
theorem pm96_491 {R : α → α → Prop} {x : α} :
    R ∈ arrow one one → IR R x = Λ ∨ JR R x = Λ := by
  intro hR
  rw [Null_eq_empty]
  by_contra hne
  rw [not_or] at hne
  obtain ⟨y, hy, hd⟩ := pm96_472 ⟨⟨manyOne_of_oneOne hR, Set.nonempty_iff_ne_empty.2 hne.2⟩,
    Set.nonempty_iff_ne_empty.2 hne.1⟩
  obtain ⟨w, hyw, hwI⟩ := desc_cnv_exists hd
  obtain ⟨u, huI, huw⟩ := IR_pred hwI
  have e : y = u := (mem_arrow_one_one.1 hR).1 y u w ⟨hyw, huw⟩
  subst e
  exact (mem_JR.1 hy).2 huI.2

/-- ✱96·492. \[\begin{align}\vdash\colon\ldotp R\in 1\rightarrow 1.x\in \text{D}ʻR.&\supset:\\ &{\sim}(xR_{\text{po}}x).\equiv.I_{R}ʻx=\Lambda:xR_{\text{po}}x.\equiv.J_{R}ʻx=\Lambda\end{align}\] -/
theorem pm96_492 {R : α → α → Prop} {x : α} :
    R ∈ arrow one one ∧ x ∈ dom R →
      (¬ po R x x ↔ IR R x = Λ) ∧ (po R x x ↔ JR R x = Λ) := by
  rintro ⟨hR, hx⟩
  have hR' := mem_arrow_Cls_one.1 (manyOne_of_oneOne hR)
  have hxp : anc R x x := anc_refl (dom_sub_fld R hx)
  have hJ : po R x x → JR R x = ∅ := by
    intro hxx
    ext y
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hy
    exact (mem_JR.1 hy).2 (anc_cyc hR' hxx (mem_JR.1 hy).1)
  rw [Null_eq_empty]
  refine ⟨⟨fun hn => ?_, fun hI hxx => ?_⟩, ⟨hJ, fun hJ' => ?_⟩⟩
  · have hxJ : x ∈ JR R x := mem_JR.2 ⟨hxp, hn⟩
    rcases pm96_491 (x := x) hR with h | h
    · rwa [Null_eq_empty] at h
    · rw [Null_eq_empty] at h
      rw [h] at hxJ
      exact hxJ.elim
  · have : x ∈ IR R x := ⟨hxp, hxx⟩
    rw [hI] at this
    exact this
  · by_contra hn
    have hxJ : x ∈ JR R x := mem_JR.2 ⟨hxp, hn⟩
    rw [hJ'] at hxJ
    exact hxJ

/-- ✱96·5. \(\vdash:R\in 1\rightarrow 1.x\in \text{D}ʻR.\supset.\overrightarrow{R}_{\text{po}}ʻ\breve{R}ʻx=\overrightarrow{R}_{\unicode{x2217}}ʻx=\overrightarrow{R}_{\text{po}}ʻx\cup \iotaʻx\) -/
theorem pm96_5 {R : α → α → Prop} {x : α} :
    R ∈ arrow one one ∧ x ∈ dom R →
      Desc R˘ x (fun v => refs (po R) v = refs (anc R) x) ∧
        refs (anc R) x = refs (po R) x ∪ ι x := by
  rintro ⟨hR, v, hxv⟩
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
  refine ⟨(desc_cnv_of h2 hxv _).2 ?_, ?_⟩
  · ext u
    constructor
    · intro hu
      obtain ⟨t, hut, htv⟩ := po_iff_anc_comp.1 hu
      have : t = x := h1 t x v ⟨htv, hxv⟩
      subst this
      exact hut
    · intro hu
      exact po_iff_anc_comp.2 ⟨x, hu, hxv⟩
  · ext u
    constructor
    · intro hu
      rcases anc_iff_po.1 hu with ⟨rfl, -⟩ | h
      · exact Or.inr rfl
      · exact Or.inl h
    · rintro (h | h)
      · exact po_sub_anc h
      · have e : u = x := h
        subst e
        exact anc_refl ⟨v, Or.inl hxv⟩

/-- ✱96·501. \(\vdash:R\in 1\rightarrow 1.x\in \text{ᗡ}ʻR.\supset.\overleftarrow{R}_{\text{po}}ʻRʻx=\overleftarrow{R}_{\unicode{x2217}}ʻx=\overleftarrow{R}_{\text{po}}ʻx\cup \iotaʻx\) -/
theorem pm96_501 {R : α → α → Prop} {x : α} :
    R ∈ arrow one one ∧ x ∈ codom R →
      Desc R x (fun v => rels (po R) v = rels (anc R) x) ∧
        rels (anc R) x = rels (po R) x ∪ ι x := by
  rintro ⟨hR, v, hvx⟩
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
  refine ⟨(TheIs_iff_of_unique fun u => ⟨fun hu => h1 u v x ⟨hu, hvx⟩, fun e => e ▸ hvx⟩).2 ?_, ?_⟩
  · ext u
    constructor
    · intro hu
      have hu' : po R v u := hu
      rw [po_eq_comp_anc] at hu'
      obtain ⟨t, hvt, htu⟩ := hu'
      have : t = x := h2 v t x ⟨hvt, hvx⟩
      subst this
      exact htu
    · intro hu
      have : po R v u := by
        rw [po_eq_comp_anc]
        exact ⟨x, hvx, hu⟩
      exact this
  · ext u
    constructor
    · intro hu
      rcases anc_iff_po.1 hu with ⟨rfl, -⟩ | h
      · exact Or.inr rfl
      · exact Or.inl h
    · rintro (h | h)
      · exact po_sub_anc h
      · have e : u = x := h
        subst e
        exact anc_refl ⟨v, Or.inr hvx⟩

/-- ✱96·502. \(\vdash:R\in 1\rightarrow \text{Cls}.xRy.\supset.\overrightarrow{R}_{\unicode{x2217}}ʻy=\overrightarrow{R}_{\unicode{x2217}}ʻx\cup \iotaʻy\) -/
theorem pm96_502 {R : α → α → Prop} {x y : α} :
    R ∈ arrow one Cls ∧ R x y → refs (anc R) y = refs (anc R) x ∪ ι y := by
  rintro ⟨hR, hxy⟩
  ext u
  constructor
  · intro hu
    rcases anc_iff_po.1 hu with ⟨rfl, -⟩ | h
    · exact Or.inr rfl
    · obtain ⟨t, hut, hty⟩ := po_iff_anc_comp.1 h
      have : t = x := mem_arrow_one_Cls.1 hR t x y ⟨hty, hxy⟩
      subst this
      exact Or.inl hut
  · rintro (h | h)
    · exact anc_tail h hxy
    · have e : u = y := h
      subst e
      exact anc_refl ⟨x, Or.inr hxy⟩

/-- ✱96·51. \(\vdash:R\in 1\rightarrow 1.\alpha\subset \breve{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR.\alpha\subset \breve{R}_{\text{po}}ʻʻ\alpha.\supset.\alpha=\Lambda\) -/
theorem pm96_51 {R : α → α → Prop} {A : Set α} :
    (R ∈ arrow one one ∧ A ⊆ ancCnv R ʻʻ refs Beg R) ∧ A ⊆ (po R)˘ ʻʻ A → A = Λ := by
  rintro ⟨⟨hR, hA⟩, hA'⟩
  have hR' := (mem_arrow_one_one.1 hR).1
  have key : ∀ n y b, Beg b R → npow R n b y → y ∉ A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y b hb hby hy
      obtain ⟨y', hy', hy'y⟩ := hA' hy
      obtain ⟨b', hb', hb'y'⟩ := hA hy'
      have hb'y'' : anc R b' y' := hb'y'
      obtain ⟨-, m, hm⟩ := anc_iff_npow.1 hb'y''
      obtain ⟨k, hk⟩ := npow_succ_of_po (show po R y' y from hy'y)
      have hmk : npow R (m + (k + 1)) b' y := by
        rw [npow_add]
        exact ⟨y', hm, hk⟩
      have e := beg_npow_unique hR' n (m + (k + 1)) b b' y hb hb' hby hmk
      exact ih m (by omega) y' b' hb' hm hy'
  rw [Null_eq_empty]
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  obtain ⟨b, hb, hby⟩ := hA hy
  obtain ⟨-, n, hn⟩ := anc_iff_npow.1 (show anc R b y from hby)
  exact key n y b hb hn hy

/-- ✱96·52. \(\vdash:R\in 1\rightarrow 1.\alpha\subset \breve{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR.\exists !\alpha.\supset.\exists !\overrightarrow{\text{min}}(R_{\text{po}})ʻ\alpha\) -/
theorem pm96_52 {R : α → α → Prop} {A : Set α} :
    (R ∈ arrow one one ∧ A ⊆ ancCnv R ʻʻ refs Beg R) ∧ A.Nonempty →
      (refs (minP (po R)) A).Nonempty := by
  rintro ⟨⟨hR, hA⟩, hne⟩
  by_contra hmin
  have hsub : A ⊆ (po R)˘ ʻʻ A := by
    intro y hy
    by_contra hy'
    apply hmin
    refine ⟨y, ⟨hy, ?_⟩, ?_⟩
    · obtain ⟨b, -, hby⟩ := hA hy
      rw [fld_po]
      exact anc_fld_right (show anc R b y from hby)
    · rintro ⟨v, hv, hvy⟩
      exact hy' ⟨v, hv, hvy⟩
  have := pm96_51 ⟨⟨hR, hA⟩, hsub⟩
  rw [Null_eq_empty] at this
  rw [this] at hne
  exact Set.not_nonempty_empty hne

/-!
## [✱97] Analysis of the field of a relation into families

*(Vol. 1, p. 654)*

> *Summary of* *97.
>
> In this number, we consider not only the posterity of a term, but the ancestry and posterity together, *i.e.* \(\overrightarrow{R}_{\unicode{x2217}}ʻx \cup\overleftarrow{R}_{\unicode{x2217}}ʻx\). We put \[ \overleftrightarrow{R}ʻx = \overrightarrow{R}ʻx \cup (\iotaʻx \cap CʻR) \cup \overleftarrow{R}ʻx \quad \text{Df}\text{.} \]
>
> Thus the whole family of a term, *i.e.* its ancestry and posterity together, is \(\overleftrightarrow{R}_{\unicode{x2217}}ʻx\). The most important case here is when \(R \in 1 \rightarrow 1\); in this case families are mutually exclusive, *i.e.* we have \[ \vdash: R \in 1 \rightarrow 1 .\supset. \overleftrightarrow{R}_{\unicode{x2217}}ʻʻCʻR \in \text{Cls} ~ \text{ex}^{2} ~ \text{excl}\text{.} \]
>
> In case \(R \in 1 \rightarrow 1\) and \(y\) belongs to a family which has a beginning, *i.e.* in case \(\exists!\overleftrightarrow{R}_{\unicode{x2217}}ʻy \cap \overrightarrow{B}ʻR\), the whole family of \(y\) consists of the posterity of the beginning, *i.e.* we have \[ \vdash: R \in 1 \rightarrow 1 . xBR . x R_{\unicode{x2217}} y .\supset. \overleftrightarrow{R}_{\unicode{x2217}}ʻy = \overleftarrow{R}_{\unicode{x2217}}ʻx\text{,} \] whence
>
> …

**Lean reading.** `R⃡'x` is `refsRels R x` and the relation `R⃡` is `Rboth R`; the family
`R⃡_*'x` is `refsRels (anc R) x` and `R⃡_*''C'R` is `Rboth (anc R) ʻʻ fld R`. `R⃖_*` as a relation is
`Rbwd (anc R)` (so `R⃖_*''B⃗'R` is `Rbwd (anc R) ʻʻ refs Beg R`), `Cnv'R⃖_*` is `(Rbwd (anc R))˘`,
`∈_Δ'κ` is `sel memRel K`, `(R̆_*)_Δ'α` is `sel (ancCnv R) A`, `S̆'x ∈ B⃗'R̆` is
`Desc S˘ x (fun u => u ∈ refs Beg R˘)`, and `0 ∪ 1` is `zero ∪ one`. Chains are conjunctions of
their links. ✱97·402 (which needs `x ∈ D'R`) and ✱97·41 (printed with `x ∈ −B⃗'R`) are proved
corrected, with Lean counterexamples to the printed forms; ✱97·47 has a stray `|` in the e-text.

**Status.** proved (all propositions; ✱97·01 definition; ✱97·402, ✱97·41 proved (corrected);
✱97·47 proved (reading); see their docstrings).
-/

/-- ✱97·01 (Df). \(\overleftrightarrow{R}ʻx=\overrightarrow{R}ʻx\cup(\iotaʻx\cap CʻR)\cup\overleftarrow{R}ʻx \quad\text{Df}\) -/
theorem pm97_01 {R : α → α → Prop} {x : α} :
    refsRels R x = refs R x ∪ (ι x ∩ fld R) ∪ rels R x := rfl

/-- ✱97·1. \(\vdash\colon\ldotp y\in \overleftrightarrow{R}ʻx.\equiv:yRx.\lor.y=x.x\in CʻR.\lor.xRy\) -/
theorem pm97_1 {R : α → α → Prop} {x y : α} :
    y ∈ refsRels R x ↔ (R y x ∨ (y = x ∧ x ∈ fld R)) ∨ R x y := by
  constructor
  · rintro ((h | ⟨h1, h2⟩) | h)
    · exact Or.inl (Or.inl h)
    · have e : y = x := h1
      subst e
      exact Or.inl (Or.inr ⟨rfl, h2⟩)
    · exact Or.inr h
  · rintro ((h | ⟨rfl, h2⟩) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨rfl, h2⟩)
    · exact Or.inr h

/-- ✱97·101. \(\vdash:y\in \overleftrightarrow{R}ʻx.\equiv.x\in \overleftrightarrow{R}ʻy\) -/
theorem pm97_101 {R : α → α → Prop} {x y : α} : y ∈ refsRels R x ↔ x ∈ refsRels R y := by
  rw [pm97_1, pm97_1]
  constructor
  · rintro ((h | ⟨rfl, h⟩) | h)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inl (Or.inl h)
  · rintro ((h | ⟨rfl, h⟩) | h)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inl (Or.inl h)

private theorem refsRels_sub_fld (R : α → α → Prop) (x : α) : refsRels R x ⊆ fld R := by
  intro y hy
  rcases pm97_1.1 hy with (h | ⟨rfl, h⟩) | h
  · exact ⟨x, Or.inl h⟩
  · exact h
  · exact ⟨x, Or.inr h⟩

private theorem self_mem_refsRels {R : α → α → Prop} {x : α} (h : x ∈ fld R) :
    x ∈ refsRels R x := pm97_1.2 (Or.inl (Or.inr ⟨rfl, h⟩))

/-- ✱97·11. \(\vdash.sʻ\overleftrightarrow{R}ʻʻCʻR=CʻR\) -/
theorem pm97_11 {R : α → α → Prop} : sumCls (Rboth R ʻʻ fld R) = fld R := by
  ext y
  constructor
  · rintro ⟨A, ⟨x, -, hA⟩, hy⟩
    have hA' : A = refsRels R x := hA
    subst hA'
    exact refsRels_sub_fld R x hy
  · intro hy
    exact ⟨refsRels R y, ⟨y, hy, rfl⟩, self_mem_refsRels hy⟩

/-- ✱97·111. \(\vdash:x\in CʻR.\equiv.x\in \overleftrightarrow{R}ʻx.\equiv.\exists !\overleftrightarrow{R}ʻx\) -/
theorem pm97_111 {R : α → α → Prop} {x : α} :
    (x ∈ fld R ↔ x ∈ refsRels R x) ∧ (x ∈ refsRels R x ↔ (refsRels R x).Nonempty) := by
  refine ⟨⟨self_mem_refsRels, fun h => refsRels_sub_fld R x h⟩, ⟨fun h => ⟨x, h⟩, ?_⟩⟩
  rintro ⟨y, hy⟩
  rcases pm97_1.1 hy with (h | ⟨rfl, h⟩) | h
  · exact self_mem_refsRels ⟨y, Or.inr h⟩
  · exact self_mem_refsRels h
  · exact self_mem_refsRels ⟨y, Or.inl h⟩

private theorem fld_anc (R : α → α → Prop) : fld (anc R) = fld R := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact anc_left_fld h
    · exact anc_fld_right h
  · intro h
    exact ⟨x, Or.inl (anc_refl h)⟩

/-- ✱97·12. \(\vdash.\Lambda{\sim}\in \overleftrightarrow{R}_{\unicode{x2217}}ʻʻCʻR\) -/
theorem pm97_12 {R : α → α → Prop} : Λ ∉ Rboth (anc R) ʻʻ fld R := by
  rintro ⟨x, hx, hA⟩
  have hA' : Λ = refsRels (anc R) x := hA
  have : x ∈ refsRels (anc R) x := self_mem_refsRels (by rw [fld_anc]; exact hx)
  rw [← hA', Null_eq_empty] at this
  exact this

/-- ✱97·13. \(\vdash.\overleftrightarrow{R}_{\unicode{x2217}}ʻx = \overrightarrow{R}_{\unicode{x2217}}ʻx \cup \overleftarrow{R}_{\unicode{x2217}}ʻx\) -/
theorem pm97_13 {R : α → α → Prop} {x : α} :
    refsRels (anc R) x = refs (anc R) x ∪ rels (anc R) x := by
  ext y
  rw [pm97_1]
  constructor
  · rintro ((h | ⟨rfl, h⟩) | h)
    · exact Or.inl h
    · rw [fld_anc] at h
      exact Or.inl (anc_refl h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

private theorem mem_fam {R : α → α → Prop} {x y : α} :
    y ∈ refsRels (anc R) x ↔ anc R y x ∨ anc R x y := by
  rw [pm97_13]
  exact Iff.rfl

/-- ✱97·14. \(\vdash:R\in 1\rightarrow 1.xR_{\unicode{x2217}}y.\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻx=\overleftrightarrow{R}_{\unicode{x2217}}ʻy \quad[\text{*96·32.*97·13}]\) -/
theorem pm97_14 {R : α → α → Prop} {x y : α} :
    R ∈ arrow one one ∧ anc R x y → refsRels (anc R) x = refsRels (anc R) y := by
  intro h
  rw [pm97_13, pm97_13]
  exact pm96_32 h

/-- ✱97·15. \(\vdash:R\in 1\rightarrow 1.x\in \overleftrightarrow{R}_{\unicode{x2217}}ʻy.\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻx=\overleftrightarrow{R}_{\unicode{x2217}}ʻy\) -/
theorem pm97_15 {R : α → α → Prop} {x y : α} :
    R ∈ arrow one one ∧ x ∈ refsRels (anc R) y → refsRels (anc R) x = refsRels (anc R) y := by
  rintro ⟨hR, h⟩
  rcases mem_fam.1 h with h' | h'
  · exact pm97_14 ⟨hR, h'⟩
  · exact (pm97_14 ⟨hR, h'⟩).symm

/-- ✱97·16. \(\vdash:R\in 1\rightarrow 1.\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻʻCʻR\in \text{Cls}^{2}\,\text{excl}\) -/
theorem pm97_16 {R : α → α → Prop} :
    R ∈ arrow one one → Rboth (anc R) ʻʻ fld R ∈ Cls2excl := by
  rintro hR A B ⟨⟨⟨x, -, hA⟩, ⟨y, -, hB⟩⟩, hne⟩
  have hA' : A = refsRels (anc R) x := hA
  have hB' : B = refsRels (anc R) y := hB
  subst hA' hB'
  rw [Null_eq_empty]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hzx hzy
  exact hne ((pm97_15 ⟨hR, hzx⟩).symm.trans (pm97_15 ⟨hR, hzy⟩))

private theorem fam_canon {R : α → α → Prop} {x : α} :
    refsRels (anc R) x = (refs (po R) x ∪ (ι x ∩ fld R)) ∪ rels (po R) x := by
  ext y
  rw [mem_fam]
  constructor
  · rintro (h | h)
    · rcases anc_iff_po.1 h with ⟨rfl, hf⟩ | h'
      · exact Or.inl (Or.inr ⟨rfl, hf⟩)
      · exact Or.inl (Or.inl h')
    · rcases anc_iff_po.1 h with ⟨rfl, hf⟩ | h'
      · exact Or.inl (Or.inr ⟨rfl, hf⟩)
      · exact Or.inr h'
  · rintro ((h | ⟨h1, h2⟩) | h)
    · exact Or.inl (po_sub_anc h)
    · have e : y = x := h1
      subst e
      exact Or.inl (anc_refl h2)
    · exact Or.inr (po_sub_anc h)

/-- ✱97·17. \(\vdash.\overleftrightarrow{R}_{\unicode{x2217}}ʻx=\overleftrightarrow{R}_{\text{po}}ʻx=\overrightarrow{R}_{\unicode{x2217}}ʻx\cup \overleftarrow{R}_{\text{po}}ʻx=\overrightarrow{R}_{\text{po}}ʻx\cup \overleftarrow{R}_{\unicode{x2217}}ʻx\) -/
theorem pm97_17 {R : α → α → Prop} {x : α} :
    (refsRels (anc R) x = refsRels (po R) x ∧
      refsRels (po R) x = refs (anc R) x ∪ rels (po R) x) ∧
      refs (anc R) x ∪ rels (po R) x = refs (po R) x ∪ rels (anc R) x := by
  have h1 : refsRels (po R) x = refsRels (anc R) x := by
    rw [fam_canon, refsRels, fld_po]
  have h2 : refs (anc R) x ∪ rels (po R) x = refsRels (anc R) x := by
    rw [fam_canon]
    ext y
    constructor
    · rintro (h | h)
      · rcases anc_iff_po.1 h with ⟨rfl, hf⟩ | h'
        · exact Or.inl (Or.inr ⟨rfl, hf⟩)
        · exact Or.inl (Or.inl h')
      · exact Or.inr h
    · rintro ((h | ⟨h1, hf2⟩) | h)
      · exact Or.inl (po_sub_anc h)
      · have e : y = x := h1
        subst e
        exact Or.inl (anc_refl hf2)
      · exact Or.inr h
  have h3 : refs (po R) x ∪ rels (anc R) x = refsRels (anc R) x := by
    rw [fam_canon]
    ext y
    constructor
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · rcases anc_iff_po.1 h with ⟨rfl, hf⟩ | h'
        · exact Or.inl (Or.inr ⟨rfl, hf⟩)
        · exact Or.inr h'
    · rintro ((h | ⟨h1, hf2⟩) | h)
      · exact Or.inl h
      · have e : y = x := h1
        subst e
        exact Or.inr (anc_refl hf2)
      · exact Or.inr (po_sub_anc h)
  rw [h1, h2, h3]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- ✱97·18. \(\vdash.Cʻ(R\unicode{x0294f}\overleftrightarrow{R}ʻx)=\overleftrightarrow{R}ʻx\) -/
theorem pm97_18 {R : α → α → Prop} {x : α} : fld (R ⥏ refsRels R x) = refsRels R x := by
  ext y
  constructor
  · rintro ⟨z, ⟨⟨hy, -⟩, -⟩ | ⟨⟨-, -⟩, hy⟩⟩
    · exact hy
    · exact hy
  · intro hy
    rcases pm97_1.1 hy with (h | ⟨rfl, h⟩) | h
    · exact ⟨x, Or.inl ⟨⟨hy, h⟩, self_mem_refsRels ⟨y, Or.inr h⟩⟩⟩
    · obtain ⟨z, hz | hz⟩ := h
      · exact ⟨z, Or.inl ⟨⟨hy, hz⟩, pm97_1.2 (Or.inr hz)⟩⟩
      · exact ⟨z, Or.inr ⟨⟨pm97_1.2 (Or.inl (Or.inl hz)), hz⟩, hy⟩⟩
    · exact ⟨x, Or.inr ⟨⟨self_mem_refsRels ⟨y, Or.inl h⟩, h⟩, hy⟩⟩

/-- ✱97·2. \(\vdash:xBR.\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻx=\overleftarrow{R}_{\unicode{x2217}}ʻx\) -/
theorem pm97_2 {R : α → α → Prop} {x : α} :
    Beg x R → refsRels (anc R) x = rels (anc R) x := by
  intro hx
  rw [pm97_13]
  ext y
  constructor
  · rintro (h | h)
    · rcases anc_iff_po.1 h with ⟨rfl, hf⟩ | h'
      · exact anc_refl hf
      · obtain ⟨t, -, htx⟩ := po_iff_anc_comp.1 h'
        exact absurd ⟨t, htx⟩ (beg_not_codom hx)
    · exact h
  · exact Or.inr

/-- ✱97·21. \(\vdash:R\in 1\rightarrow 1.\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻʻsʻ\text{gen}ʻR=\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR\) -/
theorem pm97_21 {R : α → α → Prop} :
    R ∈ arrow one one → Rboth (anc R) ʻʻ sumCls (gen R) = Rbwd (anc R) ʻʻ refs Beg R := by
  intro hR
  have hR1 := (mem_arrow_one_one.1 hR).1
  ext A
  constructor
  · rintro ⟨y, hy, hA⟩
    have hA' : A = refsRels (anc R) y := hA
    subst hA'
    obtain ⟨b, n, hb, hby⟩ := (mem_sumCls_gen_oneMany hR1).1 hy
    have hby' : anc R b y := anc_of_npow (dom_sub_fld R (beg_dom hb)) hby
    refine ⟨b, hb, ?_⟩
    show refsRels (anc R) y = rels (anc R) b
    rw [← pm97_14 ⟨hR, hby'⟩, pm97_2 hb]
  · rintro ⟨b, hb, hA⟩
    have hA' : A = rels (anc R) b := hA
    subst hA'
    refine ⟨b, (mem_sumCls_gen_oneMany hR1).2 ⟨b, 0, hb, rfl⟩, ?_⟩
    show rels (anc R) b = refsRels (anc R) b
    rw [pm97_2 hb]

private theorem img_union' (P : β → α → Prop) (A B : Set α) : P ʻʻ (A ∪ B) = P ʻʻ A ∪ P ʻʻ B := by
  ext z
  constructor
  · rintro ⟨y, hy | hy, h⟩
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr ⟨y, hy, h⟩
  · rintro (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
    · exact ⟨y, Or.inl hy, h⟩
    · exact ⟨y, Or.inr hy, h⟩

private theorem pdc_sub_fld (R : α → α → Prop) : prodCls (Dcnv ʻʻ pot R) ⊆ fld R := by
  intro x hx
  rw [mem_prodCls_Dcnv] at hx
  exact codom_sub_fld R (hx R (self_mem_pot R))

/-- ✱97·22. \[\begin{align}&\vdash:R\in 1\rightarrow 1.\supset.\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR\cup \overleftrightarrow{R}_{\unicode{x2217}}ʻʻpʻ\text{ᗡ}ʻʻPotʻR=\overleftrightarrow{R}_{\unicode{x2217}}ʻʻCʻR\\ &[\text{*97·21.*93·37}]\end{align}\] -/
theorem pm97_22 {R : α → α → Prop} :
    R ∈ arrow one one →
      Rbwd (anc R) ʻʻ refs Beg R ∪ Rboth (anc R) ʻʻ prodCls (Dcnv ʻʻ pot R) =
        Rboth (anc R) ʻʻ fld R := by
  intro hR
  have hf : fld R = sumCls (gen R) ∪ prodCls (Dcnv ʻʻ pot R) :=
    Set.Subset.antisymm (fld_sub_gen_pdc R)
      (Set.union_subset (sumCls_gen_sub_fld R) (pdc_sub_fld R))
  rw [hf, img_union', pm97_21 hR]

private theorem zero_union_one_iff {K : Set (Set α)} :
    K ∈ zero ∪ one ↔ ∀ A B, A ∈ K → B ∈ K → A = B := by
  constructor
  · rintro (h | ⟨a, rfl⟩)
    · have h' : K = Λ := h
      rw [h', Null_eq_empty]
      intro A B hA
      exact hA.elim
    · intro A B hA hB
      exact (hA : A = a).trans (hB : B = a).symm
  · intro h
    by_cases hK : K.Nonempty
    · obtain ⟨a, ha⟩ := hK
      exact Or.inr ⟨a, Set.ext fun B => ⟨fun hB => h B a hB ha, fun e => e ▸ ha⟩⟩
    · left
      show K = Λ
      rw [Null_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.1 hK

private theorem fam_conn_iff (P : α → α → Prop) :
    (∀ x y, x ∈ fld P ∧ y ∈ fld P → refsRels P x = refsRels P y) ↔
      ∀ x y, x ∈ fld P ∧ y ∈ fld P → (x = y ∨ P x y) ∨ P y x := by
  constructor
  · rintro h x y ⟨hx, hy⟩
    have : x ∈ refsRels P y := by rw [← h x y ⟨hx, hy⟩]; exact self_mem_refsRels hx
    rcases pm97_1.1 this with (h1 | ⟨rfl, -⟩) | h1
    · exact Or.inl (Or.inr h1)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr h1
  · intro h
    have key : ∀ x, x ∈ fld P → refsRels P x = fld P := by
      intro x hx
      apply Set.Subset.antisymm (refsRels_sub_fld P x)
      intro z hz
      rcases h z x ⟨hz, hx⟩ with (rfl | h1) | h1
      · exact self_mem_refsRels hz
      · exact pm97_1.2 (Or.inl (Or.inl h1))
      · exact pm97_1.2 (Or.inr h1)
    rintro x y ⟨hx, hy⟩
    rw [key x hx, key y hy]

private theorem zero_one_fam (P : α → α → Prop) :
    Rboth P ʻʻ fld P ∈ zero ∪ one ↔
      ∀ x y, x ∈ fld P ∧ y ∈ fld P → refsRels P x = refsRels P y := by
  rw [zero_union_one_iff]
  constructor
  · rintro h x y ⟨hx, hy⟩
    exact h _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  · rintro h A B ⟨x, hx, hA⟩ ⟨y, hy, hB⟩
    have hA' : A = refsRels P x := hA
    have hB' : B = refsRels P y := hB
    rw [hA', hB']
    exact h x y ⟨hx, hy⟩

/-- ✱97·23. \(\vdash\colon\colon \overleftrightarrow{R}ʻʻCʻR\in 0\cup 1.\equiv\colon\ldotp x,\,y\in CʻR.\supset_{x,y}:x=y.\lor.xRy.\lor.yRx\) -/
theorem pm97_23 {R : α → α → Prop} :
    Rboth R ʻʻ fld R ∈ zero ∪ one ↔
      ∀ x y, x ∈ fld R ∧ y ∈ fld R → (x = y ∨ R x y) ∨ R y x := by
  rw [zero_one_fam, fam_conn_iff]

/-- ✱97·231. \(\vdash\colon\ldotp \overleftrightarrow{R}ʻʻCʻR\in 0\cup 1.\equiv:x\in CʻR.\supset_{x}.CʻR=\overrightarrow{R}ʻx\cup \iotaʻx\cup \overleftarrow{R}ʻx\) -/
theorem pm97_231 {R : α → α → Prop} :
    Rboth R ʻʻ fld R ∈ zero ∪ one ↔ ∀ x, x ∈ fld R → fld R = refs R x ∪ ι x ∪ rels R x := by
  rw [pm97_23]
  constructor
  · intro h x hx
    apply Set.Subset.antisymm
    · intro z hz
      rcases h z x ⟨hz, hx⟩ with (rfl | h1) | h1
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h1
    · rintro z ((h1 | h1) | h1)
      · exact ⟨x, Or.inl h1⟩
      · have e : z = x := h1
        subst e
        exact hx
      · exact ⟨x, Or.inr h1⟩
  · rintro h x y ⟨hx, hy⟩
    have : x ∈ refs R y ∪ ι y ∪ rels R y := by rw [← h y hy]; exact hx
    rcases this with (h1 | h1) | h1
    · exact Or.inl (Or.inr h1)
    · exact Or.inl (Or.inl h1)
    · exact Or.inr h1

/-- ✱97·24. \(\vdash\colon\ldotp \overleftrightarrow{R}_{\unicode{x2217}}ʻʻCʻR\in 0\cup 1.\equiv:x\in CʻR.\supset_{x}.CʻR=\overrightarrow{R}_{\unicode{x2217}}ʻx\cup \overleftarrow{R}_{\unicode{x2217}}ʻx\) -/
theorem pm97_24 {R : α → α → Prop} :
    Rboth (anc R) ʻʻ fld R ∈ zero ∪ one ↔
      ∀ x, x ∈ fld R → fld R = refs (anc R) x ∪ rels (anc R) x := by
  have h := pm97_231 (R := anc R)
  rw [fld_anc] at h
  rw [h]
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  have e : refs (anc R) x ∪ ι x ∪ rels (anc R) x = refs (anc R) x ∪ rels (anc R) x := by
    ext z
    constructor
    · rintro ((h1 | h1) | h1)
      · exact Or.inl h1
      · have e : z = x := h1
        subst e
        exact Or.inl (anc_refl hx)
      · exact Or.inr h1
    · rintro (h1 | h1)
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h1
  rw [e]

/-- ✱97·241. \(\vdash\colon\colon \overleftrightarrow{R}_{\unicode{x2217}}ʻʻCʻR\in 0\cup 1.\equiv\colon\ldotp x,y\in CʻR.\supset_{x,y}:xR_{\unicode{x2217}}y.\lor.yR_{\unicode{x2217}}x\) -/
theorem pm97_241 {R : α → α → Prop} :
    Rboth (anc R) ʻʻ fld R ∈ zero ∪ one ↔
      ∀ x y, x ∈ fld R ∧ y ∈ fld R → anc R x y ∨ anc R y x := by
  have h := pm97_23 (R := anc R)
  rw [fld_anc] at h
  rw [h]
  refine forall_congr' fun x => forall_congr' fun y => imp_congr_right fun hxy => ?_
  constructor
  · rintro ((rfl | h1) | h1)
    · exact Or.inl (anc_refl hxy.1)
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (h1 | h1)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h1

/-- ✱97·242. \[\begin{align}\vdash\colon\colon \overleftrightarrow{R}_{\unicode{x2217}}ʻʻCʻR\in 0\cup 1.&\equiv\colon\ldotp x,\,y\in CʻR.\supset_{x,y}:x=y.\lor.xR_{\text{po}}y.\lor.yR_{\text{po}}x\colon\ldotp \\ &\equiv\colon\ldotp \overleftrightarrow{R}_{\text{po}}ʻʻCʻR\in 0\cup 1\\ [\text{*91·542.*97·23.*91·504}]\end{align}\] -/
theorem pm97_242 {R : α → α → Prop} :
    (Rboth (anc R) ʻʻ fld R ∈ zero ∪ one ↔
      ∀ x y, x ∈ fld R ∧ y ∈ fld R → (x = y ∨ po R x y) ∨ po R y x) ∧
      ((∀ x y, x ∈ fld R ∧ y ∈ fld R → (x = y ∨ po R x y) ∨ po R y x) ↔
        Rboth (po R) ʻʻ fld R ∈ zero ∪ one) := by
  refine ⟨?_, ?_⟩
  · rw [pm97_241]
    refine forall_congr' fun x => forall_congr' fun y => imp_congr_right fun hxy => ?_
    constructor
    · rintro (h1 | h1)
      · rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h2
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr h2)
      · rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h2
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr h2
    · rintro ((rfl | h1) | h1)
      · exact Or.inl (anc_refl hxy.1)
      · exact Or.inl (po_sub_anc h1)
      · exact Or.inr (po_sub_anc h1)
  · have h := pm97_23 (R := po R)
    rw [fld_po] at h
    exact h.symm

private theorem post_beg_inj {R : α → α → Prop} {x y : α} (_hx : Beg x R) (hy : Beg y R)
    (h : rels (anc R) x = rels (anc R) y) : x = y := by
  have hyy : y ∈ rels (anc R) y := anc_refl (dom_sub_fld R (beg_dom hy))
  rw [← h] at hyy
  rcases anc_iff_po.1 hyy with ⟨e, -⟩ | h'
  · exact e
  · obtain ⟨t, -, hty⟩ := po_iff_anc_comp.1 h'
    exact absurd ⟨t, hty⟩ (beg_not_codom hy)

/-- ✱97·3. \(\vdash.\overleftarrow{R}_{\unicode{x2217}}\upharpoonright \overrightarrow{B}ʻR\in 1\rightarrow 1\) -/
theorem pm97_3 {R : α → α → Prop} : Rbwd (anc R) ↾ refs Beg R ∈ arrow one one := by
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro A A' x ⟨⟨hA, -⟩, ⟨hA', -⟩⟩
    exact (hA : A = rels (anc R) x).trans (hA' : A' = rels (anc R) x).symm
  · rintro A x y ⟨⟨hx, hxB⟩, ⟨hy, hyB⟩⟩
    exact post_beg_inj hxB hyB ((hx : A = rels (anc R) x).symm.trans hy)

/-- ✱97·301. \(\vdash.I\upharpoonright \overrightarrow{B}ʻR\in (\breve{R}_{\unicode{x2217}})_{\Delta}ʻ\overrightarrow{B}ʻR\) -/
theorem pm97_301 {R : α → α → Prop} : I ↾ refs Beg R ∈ sel (ancCnv R) (refs Beg R) := by
  refine mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨hxz, -⟩, ⟨hyz, -⟩⟩
    exact (hxz : x = z).trans (hyz : y = z).symm
  · rintro x y ⟨hxy, hy⟩
    have e : x = y := hxy
    subst e
    exact anc_refl (dom_sub_fld R (beg_dom hy))
  · ext y
    constructor
    · rintro ⟨x, -, hy⟩
      exact hy
    · intro hy
      exact ⟨y, rfl, hy⟩

/-- ✱97·31. \(\vdash.(\overrightarrow{B}ʻR)\upharpoonleft \text{Cnv}ʻ\overleftarrow{R}_{\unicode{x2217}}\in {\in}_{\Delta}ʻ\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR.\text{D}ʻ\{(\overrightarrow{B}ʻR)\upharpoonleft \text{Cnv}ʻ\overleftarrow{R}_{\unicode{x2217}}\}=\overrightarrow{B}ʻR\) -/
theorem pm97_31 {R : α → α → Prop} :
    refs Beg R ◁ (Rbwd (anc R))˘ ∈ sel memRel (Rbwd (anc R) ʻʻ refs Beg R) ∧
      dom (refs Beg R ◁ (Rbwd (anc R))˘) = refs Beg R := by
  refine ⟨mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y A ⟨⟨hx, hxA⟩, ⟨hy, hyA⟩⟩
    exact post_beg_inj hx hy ((hxA : A = rels (anc R) x).symm.trans hyA)
  · rintro x A ⟨hx, hxA⟩
    have e : A = rels (anc R) x := hxA
    subst e
    exact anc_refl (dom_sub_fld R (beg_dom hx))
  · ext A
    constructor
    · rintro ⟨x, hx, hxA⟩
      exact ⟨x, hx, hxA⟩
    · rintro ⟨x, hx, hxA⟩
      exact ⟨x, hx, hxA⟩
  · ext x
    constructor
    · rintro ⟨A, hx, -⟩
      exact hx
    · intro hx
      exact ⟨rels (anc R) x, hx, rfl⟩

/-- ✱97·32. \(\vdash.\overrightarrow{B}ʻR\in \text{D}ʻʻ{\in}_{\Delta}ʻ\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR \quad[\text{*97·31}]\) -/
theorem pm97_32 {R : α → α → Prop} :
    refs Beg R ∈ D ʻʻ sel memRel (Rbwd (anc R) ʻʻ refs Beg R) :=
  ⟨_, pm97_31.1, pm97_31.2.symm⟩

private theorem fam_img_sub {R : α → α → Prop} (hR : R ∈ arrow one one) {A B : Set α}
    (h : A ⊆ sumCls (Rboth (anc R) ʻʻ B)) : Rboth (anc R) ʻʻ A ⊆ Rboth (anc R) ʻʻ B := by
  rintro K ⟨x, hx, hK⟩
  have hK' : K = refsRels (anc R) x := hK
  subst hK'
  obtain ⟨C, ⟨y, hy, hC⟩, hxC⟩ := h hx
  have hC' : C = refsRels (anc R) y := hC
  subst hC'
  exact ⟨y, hy, pm97_15 ⟨hR, hxC⟩⟩

/-- ✱97·33. \(\vdash:R\in 1\rightarrow 1.\alpha\subset sʻ\overleftrightarrow{R}_{\unicode{x2217}}ʻʻ\beta.\beta\subset sʻ\overleftrightarrow{R}_{\unicode{x2217}}ʻʻ\alpha.\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻʻ\alpha=\overleftrightarrow{R}_{\unicode{x2217}}ʻʻ\beta\) -/
theorem pm97_33 {R : α → α → Prop} {A B : Set α} :
    (R ∈ arrow one one ∧ A ⊆ sumCls (Rboth (anc R) ʻʻ B)) ∧ B ⊆ sumCls (Rboth (anc R) ʻʻ A) →
      Rboth (anc R) ʻʻ A = Rboth (anc R) ʻʻ B := by
  rintro ⟨⟨hR, hA⟩, hB⟩
  exact Set.Subset.antisymm (fam_img_sub hR hA) (fam_img_sub hR hB)

/-- ✱97·34. \(\vdash:R\in 1\rightarrow 1.\beta\in \text{D}ʻʻ{\in}_{\Delta}ʻ\overleftrightarrow{R}_{\unicode{x2217}}ʻʻ\alpha.\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻʻ\alpha=\overleftrightarrow{R}_{\unicode{x2217}}ʻʻ\beta\) -/
theorem pm97_34 {R : α → α → Prop} {A B : Set α} :
    R ∈ arrow one one ∧ B ∈ D ʻʻ sel memRel (Rboth (anc R) ʻʻ A) →
      Rboth (anc R) ʻʻ A = Rboth (anc R) ʻʻ B := by
  rintro ⟨hR, M, hM, hB⟩
  have hB' : B = dom M := hB
  subst hB'
  obtain ⟨⟨-, hMe⟩, hcod⟩ := mem_sel_iff.1 hM
  refine pm97_33 ⟨⟨hR, ?_⟩, ?_⟩
  · intro x hx
    have hK : refsRels (anc R) x ∈ codom M := by rw [hcod]; exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hK
    exact ⟨refsRels (anc R) y, ⟨y, ⟨_, hy⟩, rfl⟩, pm97_101.1 (hMe y _ hy)⟩
  · rintro y ⟨K, hyK⟩
    have hK : K ∈ codom M := ⟨y, hyK⟩
    rw [hcod] at hK
    exact ⟨K, hK, hMe y K hyK⟩

private theorem Rbwd_eq_Rboth_beg (R : α → α → Prop) :
    Rbwd (anc R) ʻʻ refs Beg R = Rboth (anc R) ʻʻ refs Beg R := by
  ext K
  constructor
  · rintro ⟨b, hb, hK⟩
    have hK' : K = rels (anc R) b := hK
    exact ⟨b, hb, hK'.trans (pm97_2 hb).symm⟩
  · rintro ⟨b, hb, hK⟩
    have hK' : K = refsRels (anc R) b := hK
    exact ⟨b, hb, hK'.trans (pm97_2 hb)⟩

/-- ✱97·341. \[\begin{align}&\vdash:R \in 1\rightarrow 1.\beta\in \text{D}ʻʻ{\in}_{\Delta}ʻ\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR.\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻʻ\beta=\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR\\ &\left[\text{*97·34}\, \frac{\overrightarrow{B}ʻR}{\alpha} .\text{*97·2}\right]\end{align}\] -/
theorem pm97_341 {R : α → α → Prop} {B : Set α} :
    R ∈ arrow one one ∧ B ∈ D ʻʻ sel memRel (Rbwd (anc R) ʻʻ refs Beg R) →
      Rboth (anc R) ʻʻ B = Rbwd (anc R) ʻʻ refs Beg R := by
  rintro ⟨hR, hB⟩
  rw [Rbwd_eq_Rboth_beg] at hB ⊢
  exact (pm97_34 ⟨hR, hB⟩).symm

/-- ✱97·35. \[\begin{align}\vdash:R &\in \text{Cls}\rightarrow 1.T\in PotidʻR.\overrightarrow{B}ʻR\subset \text{D}ʻT.\supset.\\ &\text{Cnv}ʻ{(\overleftarrow{R}_{\unicode{x2217}}\upharpoonright \overrightarrow{B}ʻR)\mid T}\in {\in}_{\Delta}ʻ\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR.\text{ᗡ}ʻ\{(\overleftarrow{R}_{\unicode{x2217}}\upharpoonright \overrightarrow{B}ʻR)\mid T\}=\breve{T}ʻʻ\overrightarrow{B}ʻR\end{align}\] -/
theorem pm97_35 {R T : α → α → Prop} :
    (R ∈ arrow Cls one ∧ T ∈ potid R) ∧ refs Beg R ⊆ dom T →
      ((Rbwd (anc R) ↾ refs Beg R) ⨾ T)˘ ∈ sel memRel (Rbwd (anc R) ʻʻ refs Beg R) ∧
        codom ((Rbwd (anc R) ↾ refs Beg R) ⨾ T) = T˘ ʻʻ refs Beg R := by
  rintro ⟨⟨hR, hT⟩, hBT⟩
  obtain ⟨n, rfl⟩ := mem_potid'.1 hT
  have hTm := ipow_mem_Cls_one (mem_arrow_Cls_one.1 hR) n
  refine ⟨mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro y y' A ⟨⟨x, ⟨hxA, hxB⟩, hxy⟩, ⟨x', ⟨hx'A, hx'B⟩, hx'y'⟩⟩
    have e : x = x' := post_beg_inj hxB hx'B ((hxA : A = _).symm.trans hx'A)
    subst e
    exact hTm x y y' ⟨hxy, hx'y'⟩
  · rintro y A ⟨x, ⟨hxA, -⟩, hxy⟩
    have e : A = rels (anc R) x := hxA
    subst e
    obtain ⟨hx, hn⟩ := ipow_apply.1 hxy
    exact anc_of_npow hx hn
  · ext A
    constructor
    · rintro ⟨y, x, ⟨hxA, hxB⟩, -⟩
      exact ⟨x, hxB, hxA⟩
    · rintro ⟨x, hxB, hxA⟩
      obtain ⟨y, hxy⟩ := hBT hxB
      exact ⟨y, x, ⟨hxA, hxB⟩, hxy⟩
  · ext y
    constructor
    · rintro ⟨A, x, ⟨-, hxB⟩, hxy⟩
      exact ⟨x, hxB, hxy⟩
    · rintro ⟨x, hxB, hxy⟩
      exact ⟨rels (anc R) x, x, ⟨rfl, hxB⟩, hxy⟩

/-- ✱97·36. \[\begin{align}&\vdash:R\in \text{Cls}\rightarrow 1.T\in \text{Potid}ʻR.\overrightarrow{B}ʻR\subset \text{D}ʻT.\supset.\breve{T}ʻʻ\overrightarrow{B}ʻR\in \text{D}ʻʻ{\in}_{\Delta}ʻ\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR\\ &[\text{*97·35}]\end{align}\] -/
theorem pm97_36 {R T : α → α → Prop} :
    (R ∈ arrow Cls one ∧ T ∈ potid R) ∧ refs Beg R ⊆ dom T →
      T˘ ʻʻ refs Beg R ∈ D ʻʻ sel memRel (Rbwd (anc R) ʻʻ refs Beg R) := by
  intro h
  obtain ⟨h1, h2⟩ := pm97_35 h
  exact ⟨_, h1, h2.symm⟩

private theorem gen_mem_D {R : α → α → Prop} (hR : R ∈ arrow one one) {n : ℕ}
    (hB : refs Beg R ⊆ dom (ipow R n)) :
    (ipow R n)˘ ʻʻ refs Beg R ∈ D ʻʻ sel memRel (Rbwd (anc R) ʻʻ refs Beg R) :=
  pm97_36 ⟨⟨manyOne_of_oneOne hR, ipow_mem_potid R n⟩, hB⟩

/-- ✱97·37. \(\vdash:R\in 1\rightarrow 1.\text{ᗡ}ʻR\subset \text{D}ʻR.\supset.\text{gen}ʻR\subset \text{D}ʻʻ{\in}_{\Delta}ʻ\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR\) -/
theorem pm97_37 {R : α → α → Prop} :
    R ∈ arrow one one ∧ codom R ⊆ dom R →
      gen R ⊆ D ʻʻ sel memRel (Rbwd (anc R) ʻʻ refs Beg R) := by
  rintro ⟨hR, hc⟩ A hA
  obtain ⟨n, rfl⟩ := (mem_gen_oneMany (mem_arrow_one_one.1 hR).1).1 hA
  refine gen_mem_D hR fun b hb => ?_
  obtain ⟨z, hz⟩ := npow_fwd hc n b (beg_dom hb)
  exact ⟨z, ipow_apply.2 ⟨dom_sub_fld R (beg_dom hb), hz⟩⟩

/-- A column `R⃖_*'b` of a beginning is the domain of a selector from a class `K` of generations
which all meet the column and cover it. -/
private theorem col_sel {R : α → α → Prop} (hR : R ∈ arrow one one) {b : α} (hb : Beg b R)
    {K : Set (Set α)} (hK : K ⊆ gen R) (hmeet : ∀ A, A ∈ K → (A ∩ rels (anc R) b).Nonempty)
    (hcov : ∀ y, anc R b y → ∃ A, A ∈ K ∧ y ∈ A) :
    rels (anc R) b ∈ D ʻʻ sel memRel K := by
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
  refine ⟨fun y A => A ∈ K ∧ y ∈ A ∧ anc R b y,
    mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro y y' A ⟨⟨hA, hyA, hby⟩, ⟨-, hy'A, hby'⟩⟩
    obtain ⟨n, rfl⟩ := (mem_gen_oneMany h1).1 (hK hA)
    obtain ⟨b1, hb1, hb1y⟩ := hyA
    obtain ⟨b2, hb2, hb2y'⟩ := hy'A
    obtain ⟨-, m, hm⟩ := anc_iff_npow.1 hby
    obtain ⟨-, m', hm'⟩ := anc_iff_npow.1 hby'
    have e1 := beg_npow_unique h1 n m b1 b y hb1 hb (ipow_apply.1 hb1y).2 hm
    have e2 := beg_npow_unique h1 n m' b2 b y' hb2 hb (ipow_apply.1 hb2y').2 hm'
    subst e1 e2
    exact npow_manyOne h2 n b y y' ⟨hm, hm'⟩
  · rintro y A ⟨-, hyA, -⟩
    exact hyA
  · ext A
    constructor
    · rintro ⟨y, hA, -⟩
      exact hA
    · intro hA
      obtain ⟨y, hyA, hby⟩ := hmeet A hA
      exact ⟨y, hA, hyA, hby⟩
  · ext y
    constructor
    · intro hy
      obtain ⟨A, hA, hyA⟩ := hcov y hy
      exact ⟨A, hA, hyA, hy⟩
    · rintro ⟨A, -, -, hy⟩
      exact hy

/-- ✱97·38. \(\vdash:R\in 1\rightarrow 1.\text{ᗡ}ʻR\subset \text{D}ʻR.\supset.\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR\subset \text{D}ʻʻ{\in}_{\Delta}ʻ\text{gen}ʻR\) -/
theorem pm97_38 {R : α → α → Prop} :
    R ∈ arrow one one ∧ codom R ⊆ dom R →
      Rbwd (anc R) ʻʻ refs Beg R ⊆ D ʻʻ sel memRel (gen R) := by
  rintro ⟨hR, hc⟩ C ⟨b, hb, hC⟩
  have hC' : C = rels (anc R) b := hC
  subst hC'
  have h1 := (mem_arrow_one_one.1 hR).1
  have hbf : b ∈ fld R := dom_sub_fld R (beg_dom hb)
  refine col_sel hR hb subset_rfl ?_ ?_
  · intro A hA
    obtain ⟨n, rfl⟩ := (mem_gen_oneMany h1).1 hA
    obtain ⟨z, hz⟩ := npow_fwd hc n b (beg_dom hb)
    exact ⟨z, ⟨b, hb, ipow_apply.2 ⟨hbf, hz⟩⟩, anc_of_npow hbf hz⟩
  · intro y hy
    obtain ⟨-, m, hm⟩ := anc_iff_npow.1 hy
    exact ⟨_, (mem_gen_oneMany h1).2 ⟨m, rfl⟩, b, hb, ipow_apply.2 ⟨hbf, hm⟩⟩

/-- ✱97·4. \(\vdash:S\in \text{Pot}ʻR.\supset.\breve{S}ʻʻ\overrightarrow{B}ʻ\breve{R}=\Lambda\) -/
theorem pm97_4 {R S : α → α → Prop} : S ∈ pot R → S˘ ʻʻ refs Beg R˘ = Λ := by
  intro hS
  rw [Null_eq_empty]
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨e, he, hey⟩
  exact end_not_dom he (dom_pot_sub hS ⟨y, hey⟩)

/-- ✱97·401. \(\vdash\colon\ldotp x\in \text{D}ʻR:S\in \text{Pot}ʻR.xSy.\supset_{S,y}.y\in \text{D}ʻR:\supset:S\in \text{Pot}ʻR.\supset_{S}.x\in \text{D}ʻS\) -/
theorem pm97_401 {R : α → α → Prop} {x : α} :
    x ∈ dom R ∧ (∀ S y, S ∈ pot R ∧ S x y → y ∈ dom R) → ∀ S, S ∈ pot R → x ∈ dom S := by
  rintro ⟨hx, h⟩ S hS
  obtain ⟨n, rfl⟩ := mem_pot_npow.1 hS
  induction n with
  | zero => rw [npow_one]; exact hx
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih (npow_mem_pot R n)
    obtain ⟨z, hz⟩ := h _ y ⟨npow_mem_pot R n, hy⟩
    exact ⟨z, y, hy, hz⟩

/-- ✱97·402. \[\begin{align}\vdash\colon\ldotp R\in \text{Cls}\rightarrow 1:(\exists S).S\in \text{Pot}ʻR.x{\sim}\in &\text{D}ʻS:\supset.\\ &(\exists S).S\in \text{Pot}ʻR.\breve{S}ʻx\in \overrightarrow{B}ʻ\breve{R}\end{align}\]

**Status.** proved (corrected): false as printed when `x ∼∈ D'R`: then `x ∼∈ D'S` for
every `S ∈ Pot'R`, so the hypothesis holds, while `S̆'x` never exists
(`pm97_402_printed_false`: `R = Λ̇` on `Unit`). PM's proof (by ✱97·401 and Transp) tacitly
assumes `x ∈ D'R`, which is added; it holds in the only use, ✱97·41, where `x ∈ B⃗'R`. -/
theorem pm97_402 {R : α → α → Prop} {x : α} :
    (R ∈ arrow Cls one ∧ x ∈ dom R) ∧ (∃ S, S ∈ pot R ∧ x ∉ dom S) →
      ∃ S, S ∈ pot R ∧ Desc S˘ x (fun u => u ∈ refs Beg R˘) := by
  rintro ⟨⟨hR, hx⟩, S0, hS0, hxS0⟩
  by_contra hne
  apply hxS0
  refine pm97_401 ⟨hx, fun S y ⟨hS, hxy⟩ => ?_⟩ S0 hS0
  by_contra hy
  apply hne
  refine ⟨S, hS, (desc_cnv_of (pot_manyOne (mem_arrow_Cls_one.1 hR) hS) hxy _).2 ?_⟩
  refine ⟨codom_pot_sub hS ⟨x, hxy⟩, ?_⟩
  rintro ⟨w, hw⟩
  exact hy ⟨w, hw⟩

theorem pm97_402_printed_false :
    ¬ ∀ (R : Unit → Unit → Prop) (x : Unit),
      R ∈ arrow Cls one ∧ (∃ S, S ∈ pot R ∧ x ∉ dom S) →
        ∃ S, S ∈ pot R ∧ Desc S˘ x (fun u => u ∈ refs Beg R˘) := by
  intro h
  have hR : (fun _ _ => False : Unit → Unit → Prop) ∈ arrow Cls one :=
    mem_arrow_Cls_one.2 fun _ _ _ ⟨h1, _⟩ => h1.elim
  obtain ⟨S, hS, hd⟩ := h (fun _ _ => False) () ⟨hR, ⟨_, self_mem_pot _, fun ⟨_, h1⟩ => h1⟩⟩
  obtain ⟨w, hw, -⟩ := desc_cnv_exists hd
  obtain ⟨_, h1⟩ := dom_pot_sub hS ⟨w, hw⟩
  exact h1

/-- ✱97·403. \[\begin{align}\vdash:R\in \text{Cls}\rightarrow 1.x\in \overrightarrow{B}ʻR.T\in \text{Pot}ʻR.&\overrightarrow{B}ʻ\breve{R} = \breve{T}ʻʻ\overrightarrow{B}ʻR.\supset.\\ &(\exists S).S\in \text{Pot}ʻR.x{\sim}\in \text{D}ʻS\end{align}\] -/
theorem pm97_403 {R T : α → α → Prop} {x : α} :
    ((R ∈ arrow Cls one ∧ x ∈ refs Beg R) ∧ T ∈ pot R) ∧ refs Beg R˘ = T˘ ʻʻ refs Beg R →
      ∃ S, S ∈ pot R ∧ x ∉ dom S := by
  rintro ⟨⟨⟨hR, hx⟩, hT⟩, hE⟩
  by_cases hxT : x ∈ dom T
  · obtain ⟨y, hxy⟩ := hxT
    have hy : y ∈ refs Beg R˘ := by rw [hE]; exact ⟨x, hx, hxy⟩
    refine ⟨T ⨾ R, relProd_mem_pot hT, ?_⟩
    rintro ⟨z, y', hxy', hy'z⟩
    have : y' = y := pot_manyOne (mem_arrow_Cls_one.1 hR) hT x y' y ⟨hxy', hxy⟩
    subst this
    exact end_not_dom hy ⟨z, hy'z⟩
  · exact ⟨T, hT, hxT⟩

/-- ✱97·41. \[\begin{align}\vdash:R\in \text{Cls}\rightarrow 1.x\in {\sim}\overrightarrow{B}ʻR.T\in \text{Pot}ʻR.&\overrightarrow{B}ʻ\breve{R} = \breve{T}ʻʻ\overrightarrow{B}ʻR.\supset.\\ &(\exists S).S\in \text{Pot}ʻR.\breve{S}ʻx\in \overrightarrow{B}ʻ\breve{R}\\ &[\text{*97·402·403}]\end{align}\]

**Status.** proved (corrected): the e-text prints `x ∈ −B⃗'R`, which makes the
proposition false (`pm97_41_printed_false`: `R = T = Λ̇` on `Unit`, where `B⃗'R̆ = Λ = T̆''B⃗'R` and
`x ∈ −B⃗'R`, but no `S̆'x` exists). The proof cites ✱97·402·403, and ✱97·403 has `x ∈ B⃗'R`, as has
✱97·43, which uses ✱97·41; the statement is proved with `x ∈ B⃗'R`. -/
theorem pm97_41 {R T : α → α → Prop} {x : α} :
    ((R ∈ arrow Cls one ∧ x ∈ refs Beg R) ∧ T ∈ pot R) ∧ refs Beg R˘ = T˘ ʻʻ refs Beg R →
      ∃ S, S ∈ pot R ∧ Desc S˘ x (fun u => u ∈ refs Beg R˘) := by
  intro h
  exact pm97_402 ⟨⟨h.1.1.1, beg_dom h.1.1.2⟩, pm97_403 h⟩

theorem pm97_41_printed_false :
    ¬ ∀ (R T : Unit → Unit → Prop) (x : Unit),
      ((R ∈ arrow Cls one ∧ x ∈ (refs Beg R)ᶜ) ∧ T ∈ pot R) ∧ refs Beg R˘ = T˘ ʻʻ refs Beg R →
        ∃ S, S ∈ pot R ∧ Desc S˘ x (fun u => u ∈ refs Beg R˘) := by
  intro h
  let E : Unit → Unit → Prop := fun _ _ => False
  have hR : E ∈ arrow Cls one := mem_arrow_Cls_one.2 fun _ _ _ ⟨h1, _⟩ => h1.elim
  have hx : () ∈ (refs Beg E)ᶜ := fun ⟨⟨_, h1⟩, _⟩ => h1
  have hE : refs Beg E˘ = E˘ ʻʻ refs Beg E := by
    ext y
    constructor
    · rintro ⟨⟨_, h1⟩, _⟩
      exact h1.elim
    · rintro ⟨_, _, h1⟩
      exact h1.elim
  obtain ⟨S, hS, hd⟩ := h E E () ⟨⟨⟨hR, hx⟩, self_mem_pot E⟩, hE⟩
  obtain ⟨w, hw, -⟩ := desc_cnv_exists hd
  obtain ⟨_, h1⟩ := dom_pot_sub hS ⟨w, hw⟩
  exact h1

/-- ✱97·42. \(\vdash:R\in 1\rightarrow 1.x\in \overrightarrow{B}ʻR.S,T\in \text{Pot}ʻR.\overrightarrow{B}ʻ\breve{R} = \breve{T}ʻʻ\overrightarrow{B}ʻR.\breve{S}ʻx\in \overrightarrow{B}ʻ\breve{R}.\supset.S = T\) -/
theorem pm97_42 {R S T : α → α → Prop} {x : α} :
    (((R ∈ arrow one one ∧ x ∈ refs Beg R) ∧ (S ∈ pot R ∧ T ∈ pot R)) ∧
      refs Beg R˘ = T˘ ʻʻ refs Beg R) ∧ Desc S˘ x (fun u => u ∈ refs Beg R˘) → S = T := by
  rintro ⟨⟨⟨⟨hR, hx⟩, hS, hT⟩, hE⟩, hd⟩
  obtain ⟨y, hxy, hy⟩ := desc_cnv_exists hd
  rw [hE] at hy
  obtain ⟨b, hb, hby⟩ := hy
  obtain ⟨a, rfl⟩ := mem_pot_npow.1 hS
  obtain ⟨c, rfl⟩ := mem_pot_npow.1 hT
  rw [beg_npow_unique (mem_arrow_one_one.1 hR).1 (a + 1) (c + 1) x b y hx hb hxy hby]

/-- ✱97·43. \(\vdash:R\in 1\rightarrow 1.T\in \text{Pot}ʻR.\overrightarrow{B}ʻ\breve{R} = \breve{T}ʻʻ\overrightarrow{B}ʻR.\supset.\overrightarrow{B}ʻR\subset \text{D}ʻT\) -/
theorem pm97_43 {R T : α → α → Prop} :
    (R ∈ arrow one one ∧ T ∈ pot R) ∧ refs Beg R˘ = T˘ ʻʻ refs Beg R → refs Beg R ⊆ dom T := by
  rintro ⟨⟨hR, hT⟩, hE⟩ x hx
  obtain ⟨S, hS, hd⟩ := pm97_41 ⟨⟨⟨manyOne_of_oneOne hR, hx⟩, hT⟩, hE⟩
  have e : S = T := pm97_42 ⟨⟨⟨⟨hR, hx⟩, hS, hT⟩, hE⟩, hd⟩
  subst e
  obtain ⟨y, hxy, -⟩ := desc_cnv_exists hd
  exact ⟨y, hxy⟩

/-- ✱97·44. \(\vdash:R\in 1\rightarrow 1.S,\,T\in \text{Pot}ʻR.\overrightarrow{B}ʻ\breve{R}=\breve{T}ʻʻ\overrightarrow{B}ʻR.\exists !\breve{S}ʻʻ\overrightarrow{B}ʻR.\supset.\overrightarrow{B}ʻR\subset \text{D}ʻS\) -/
theorem pm97_44 {R S T : α → α → Prop} :
    ((R ∈ arrow one one ∧ (S ∈ pot R ∧ T ∈ pot R)) ∧ refs Beg R˘ = T˘ ʻʻ refs Beg R) ∧
      (S˘ ʻʻ refs Beg R).Nonempty → refs Beg R ⊆ dom S := by
  rintro ⟨⟨⟨hR, hS, hT⟩, hE⟩, y0, b0, hb0, hb0y0⟩
  have hBT := pm97_43 ⟨⟨hR, hT⟩, hE⟩
  obtain ⟨a, rfl⟩ := mem_pot_npow.1 hS
  obtain ⟨c, rfl⟩ := mem_pot_npow.1 hT
  rcases le_or_gt a c with hac | hac
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hac
    intro x hx
    obtain ⟨z, hz⟩ := hBT hx
    rw [show a + k + 1 = (a + 1) + k by omega, npow_add] at hz
    obtain ⟨w, hw, -⟩ := hz
    exact ⟨w, hw⟩
  · exfalso
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hac
    have hb0y0' : npow R ((c + 1) + (k + 1)) b0 y0 := by
      rw [show (c + 1) + (k + 1) = a + 1 by omega]
      exact hb0y0
    rw [npow_add] at hb0y0'
    obtain ⟨z, hz, hzy⟩ := hb0y0'
    have hzE : z ∈ refs Beg R˘ := by rw [hE]; exact ⟨b0, hb0, hz⟩
    obtain ⟨u, hzu, -⟩ := npow_succ_iff.1 hzy
    exact end_not_dom hzE ⟨u, hzu⟩

/-- When `B⃗'R̆ ∈ gen'R` or `B⃗'R̆ = Λ`, every beginning of a one-one `R` lies in the domain of
any power whose generation is not null (cf. ✱97·43·44). -/
private theorem beg_sub_dom_npow {R : α → α → Prop} (hR : R ∈ arrow one one)
    (hE : refs Beg R˘ ∈ gen R ∨ refs Beg R˘ = Λ) (k : ℕ)
    (hne : ((npow R (k + 1))˘ ʻʻ refs Beg R).Nonempty) : refs Beg R ⊆ dom (npow R (k + 1)) := by
  have h1 := (mem_arrow_one_one.1 hR).1
  rcases hE with hE | hE
  · obtain ⟨c, hc⟩ := (mem_gen_oneMany h1).1 hE
    obtain ⟨y0, b0, hb0, hb0y0⟩ := hne
    cases c with
    | zero =>
      exfalso
      have : b0 ∈ refs Beg R˘ := by
        rw [hc]
        exact ⟨b0, hb0, ipow_zero_apply.2 ⟨rfl, dom_sub_fld R (beg_dom hb0)⟩⟩
      exact end_not_dom this (beg_dom hb0)
    | succ c =>
      rw [ipow_succ_eq] at hc
      have hkc : k ≤ c := by
        by_contra hkc
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt (not_le.1 hkc)
        have h' : npow R ((c + 1) + (j + 1)) b0 y0 := by
          rw [show (c + 1) + (j + 1) = k + 1 by omega]
          exact hb0y0
        rw [npow_add] at h'
        obtain ⟨z, hz, hzy⟩ := h'
        have hzE : z ∈ refs Beg R˘ := by rw [hc]; exact ⟨b0, hb0, hz⟩
        obtain ⟨u, hzu, -⟩ := npow_succ_iff.1 hzy
        exact end_not_dom hzE ⟨u, hzu⟩
      intro b hb
      have key : ∀ j, j ≤ c + 1 → ∃ e, npow R j b e := by
        intro j
        induction j with
        | zero => exact fun _ => ⟨b, rfl⟩
        | succ j ih =>
          intro hj
          obtain ⟨e, he⟩ := ih (by omega)
          by_cases hed : e ∈ dom R
          · obtain ⟨f, hf⟩ := hed
            exact ⟨f, e, he, hf⟩
          · exfalso
            cases j with
            | zero =>
              have e0 : b = e := he
              subst e0
              exact hed (beg_dom hb)
            | succ j =>
              have he' := he
              obtain ⟨g, -, hge⟩ := he
              have hE' : e ∈ refs Beg R˘ := ⟨⟨g, hge⟩, fun ⟨w, hw⟩ => hed ⟨w, hw⟩⟩
              rw [hc] at hE'
              obtain ⟨b', hb', hb'e⟩ := hE'
              have := beg_npow_unique h1 (c + 1) (j + 1) b' b e hb' hb hb'e he'
              omega
      obtain ⟨e, he⟩ := key (c + 1) le_rfl
      obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hkc
      rw [show k + l + 1 = (k + 1) + l by omega, npow_add] at he
      obtain ⟨w, hw, -⟩ := he
      exact ⟨w, hw⟩
  · have hc : codom R ⊆ dom R := by
      intro y hy
      by_contra hyd
      have : y ∈ refs Beg R˘ := ⟨hy, fun ⟨w, hw⟩ => hyd ⟨w, hw⟩⟩
      rw [hE, Null_eq_empty] at this
      exact this
    intro b hb
    obtain ⟨z, hz⟩ := npow_fwd hc (k + 1) b (beg_dom hb)
    exact ⟨z, hz⟩

private theorem beg_sub_dom_ipow {R : α → α → Prop} (hR : R ∈ arrow one one)
    (hE : refs Beg R˘ ∈ gen R ∨ refs Beg R˘ = Λ) (n : ℕ)
    (hne : ((ipow R n)˘ ʻʻ refs Beg R).Nonempty) : refs Beg R ⊆ dom (ipow R n) := by
  cases n with
  | zero =>
    intro b hb
    exact ⟨b, ipow_zero_apply.2 ⟨rfl, dom_sub_fld R (beg_dom hb)⟩⟩
  | succ k =>
    rw [ipow_succ_eq] at hne ⊢
    exact beg_sub_dom_npow hR hE k hne

private theorem gen_sub_D_of {R : α → α → Prop} (hR : R ∈ arrow one one)
    (hE : refs Beg R˘ ∈ gen R ∨ refs Beg R˘ = Λ) :
    gen R \ ι Λ ⊆ D ʻʻ sel memRel (Rbwd (anc R) ʻʻ refs Beg R) := by
  rintro A ⟨hA, hAn⟩
  obtain ⟨n, rfl⟩ := (mem_gen_oneMany (mem_arrow_one_one.1 hR).1).1 hA
  refine gen_mem_D hR (beg_sub_dom_ipow hR hE n ?_)
  by_contra hne
  apply hAn
  show _ = Λ
  rw [Null_eq_empty]
  exact Set.not_nonempty_iff_eq_empty.1 hne

private theorem col_sub_D_of {R : α → α → Prop} (hR : R ∈ arrow one one)
    (hE : refs Beg R˘ ∈ gen R ∨ refs Beg R˘ = Λ) :
    Rbwd (anc R) ʻʻ refs Beg R ⊆ D ʻʻ sel memRel (gen R \ ι Λ) := by
  rintro C ⟨b, hb, hC⟩
  have hC' : C = rels (anc R) b := hC
  subst hC'
  have h1 := (mem_arrow_one_one.1 hR).1
  have hbf : b ∈ fld R := dom_sub_fld R (beg_dom hb)
  refine col_sel hR hb (fun A hA => hA.1) ?_ ?_
  · rintro A ⟨hA, hAn⟩
    obtain ⟨n, rfl⟩ := (mem_gen_oneMany h1).1 hA
    have hne : ((ipow R n)˘ ʻʻ refs Beg R).Nonempty := by
      by_contra hne
      apply hAn
      show _ = Λ
      rw [Null_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.1 hne
    obtain ⟨z, hz⟩ := beg_sub_dom_ipow hR hE n hne hb
    exact ⟨z, ⟨b, hb, hz⟩, anc_of_npow hbf (ipow_apply.1 hz).2⟩
  · intro y hy
    obtain ⟨-, m, hm⟩ := anc_iff_npow.1 hy
    have hyA : y ∈ (ipow R m)˘ ʻʻ refs Beg R := ⟨b, hb, ipow_apply.2 ⟨hbf, hm⟩⟩
    refine ⟨_, ⟨(mem_gen_oneMany h1).2 ⟨m, rfl⟩, fun hn => ?_⟩, hyA⟩
    have hn' : (ipow R m)˘ ʻʻ refs Beg R = Λ := hn
    rw [hn', Null_eq_empty] at hyA
    exact hyA

/-- ✱97·45. \(\vdash:R\in 1\rightarrow 1.\overrightarrow{B}ʻ\breve{R}\in \text{gen}ʻR.\supset.\text{gen}ʻR-\iotaʻ\Lambda\subset \text{D}ʻʻ{\in}_{\Delta}ʻ\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR\) -/
theorem pm97_45 {R : α → α → Prop} :
    R ∈ arrow one one ∧ refs Beg R˘ ∈ gen R →
      gen R \ ι Λ ⊆ D ʻʻ sel memRel (Rbwd (anc R) ʻʻ refs Beg R) :=
  fun ⟨hR, hE⟩ => gen_sub_D_of hR (Or.inl hE)

/-- ✱97·46. \(\vdash:R\in 1\rightarrow 1.\overrightarrow{B}ʻ\breve{R}\in \text{gen}ʻR.\supset.\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR\subset \text{D}ʻʻ{\in}_{\Delta}ʻ(\text{gen}ʻR-\iotaʻ\Lambda)\) -/
theorem pm97_46 {R : α → α → Prop} :
    R ∈ arrow one one ∧ refs Beg R˘ ∈ gen R →
      Rbwd (anc R) ʻʻ refs Beg R ⊆ D ʻʻ sel memRel (gen R \ ι Λ) :=
  fun ⟨hR, hE⟩ => col_sub_D_of hR (Or.inl hE)

/-- ✱97·47. \[\begin{align}\vdash:R &\in 1\rightarrow 1.\overrightarrow{B}ʻ\breve{R}\in \text{gen}ʻR\cup \iotaʻ\Lambda.\supset.\\ &\mid \text{gen}ʻR-\iotaʻ\Lambda\subset \text{D}ʻʻ{\in}_{\Delta}ʻ\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR.\overleftarrow{R}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻR\subset \text{D}ʻʻ{\in}_{\Delta}ʻ(\text{gen}ʻR-\iotaʻ\Lambda) \end{align}\]

**Status.** proved (reading): transcription error: the e-text prints a stray `|` before
`gen'R − ι'Λ` (`|gen'R − ι'Λ ⊂ D''∈_Δ'…`), which has no meaning here; the demonstration has
`gen'R − ι'Λ ⊂ D''∈_Δ'R⃖_*''B⃗'R`. -/
theorem pm97_47 {R : α → α → Prop} :
    R ∈ arrow one one ∧ refs Beg R˘ ∈ gen R ∪ ι Λ →
      gen R \ ι Λ ⊆ D ʻʻ sel memRel (Rbwd (anc R) ʻʻ refs Beg R) ∧
        Rbwd (anc R) ʻʻ refs Beg R ⊆ D ʻʻ sel memRel (gen R \ ι Λ) := by
  rintro ⟨hR, hE⟩
  have hE' : refs Beg R˘ ∈ gen R ∨ refs Beg R˘ = Λ := hE
  exact ⟨gen_sub_D_of hR hE', col_sub_D_of hR hE'⟩

private theorem cyc_back {R : α → α → Prop} (hR : ∀ x y z, R x y ∧ R x z → y = z) {x y : α}
    (hx : po R x x) (hxy : po R x y) : po R y x := by
  obtain ⟨p, hp⟩ := npow_succ_of_po hx
  obtain ⟨n, hn⟩ := npow_succ_of_po hxy
  have hN := npow_mul_self hp (n + 2)
  have hle : n + 2 ≤ (p + 1) * (n + 2) := Nat.le_mul_of_pos_left _ (Nat.succ_pos p)
  obtain ⟨M, hM⟩ := Nat.exists_eq_add_of_le hle
  rw [hM, show n + 2 + M = (n + 1) + (M + 1) by omega, npow_add] at hN
  obtain ⟨t, hxt, htx⟩ := hN
  have : t = y := npow_manyOne hR (n + 1) x t y ⟨hxt, hn⟩
  subst this
  exact po_of_npow_succ htx

/-- ✱97·5. \(\vdash:R\in \text{Cls}\rightarrow 1.xR_{\text{po}}x.xR_{\text{po}}y.\supset.yR_{\text{po}}x\) -/
theorem pm97_5 {R : α → α → Prop} {x y : α} :
    (R ∈ arrow Cls one ∧ po R x x) ∧ po R x y → po R y x := by
  rintro ⟨⟨hR, hx⟩, hxy⟩
  exact cyc_back (mem_arrow_Cls_one.1 hR) hx hxy

private theorem po_cnv_iff {R : α → α → Prop} {x y : α} : po R˘ x y ↔ po R y x := by
  rw [po_iff_transGen, po_iff_transGen]
  exact Relation.transGen_swap

/-- ✱97·501. \(\vdash:R\in 1\rightarrow \text{Cls}.xR_{\text{po}}x.yR_{\text{po}}x.\supset.xR_{\text{po}}y \quad[\text{Proof as in *97·5}]\) -/
theorem pm97_501 {R : α → α → Prop} {x y : α} :
    (R ∈ arrow one Cls ∧ po R x x) ∧ po R y x → po R x y := by
  rintro ⟨⟨hR, hx⟩, hyx⟩
  have hR' : ∀ a b c, R˘ a b ∧ R˘ a c → b = c :=
    fun a b c ⟨h1, h2⟩ => mem_arrow_one_Cls.1 hR b c a ⟨h1, h2⟩
  exact po_cnv_iff.1 (cyc_back hR' (po_cnv_iff.2 hx) (po_cnv_iff.2 hyx))

private theorem cyc_sym {R : α → α → Prop} (hR : R ∈ arrow one one) {x : α} (hx : po R x x)
    (y : α) : anc R y x ↔ anc R x y := by
  constructor
  · intro h
    rcases anc_iff_po.1 h with ⟨rfl, -⟩ | h'
    · exact po_sub_anc hx
    · exact po_sub_anc (pm97_501 ⟨⟨mem_arrow_one_Cls.2 (mem_arrow_one_one.1 hR).1, hx⟩, h'⟩)
  · intro h
    rcases anc_iff_po.1 h with ⟨rfl, -⟩ | h'
    · exact po_sub_anc hx
    · exact po_sub_anc (pm97_5 ⟨⟨mem_arrow_Cls_one.2 (mem_arrow_one_one.1 hR).2, hx⟩, h'⟩)

/-- ✱97·51. \[\begin{align}&\vdash:R\in 1\rightarrow 1.xR_{\text{po}}x.\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻx=\overrightarrow{R}_{\unicode{x2217}}ʻx=\overleftarrow{R}_{\unicode{x2217}}ʻx=\overleftarrow{R}_{\unicode{x2217}}ʻx\cap \overrightarrow{R}_{\unicode{x2217}}ʻx\\ &[\text{*97·5·501·17}]\end{align}\] -/
theorem pm97_51 {R : α → α → Prop} {x : α} :
    R ∈ arrow one one ∧ po R x x →
      (refsRels (anc R) x = refs (anc R) x ∧ refs (anc R) x = rels (anc R) x) ∧
        rels (anc R) x = rels (anc R) x ∩ refs (anc R) x := by
  rintro ⟨hR, hx⟩
  have h1 : refs (anc R) x = rels (anc R) x := Set.ext (cyc_sym hR hx)
  refine ⟨⟨?_, h1⟩, ?_⟩
  · rw [pm97_13, h1, Set.union_self]
  · rw [h1, Set.inter_self]

/-- ✱97·52. \(\vdash:R\in 1\rightarrow 1.xR_{\text{po}}x.xR_{\text{po}}y.\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻx=\overleftarrow{R}_{\unicode{x2217}}ʻx\cap \overrightarrow{R}_{\unicode{x2217}}ʻy \quad[\text{*97·5·501·51·14}]\) -/
theorem pm97_52 {R : α → α → Prop} {x y : α} :
    (R ∈ arrow one one ∧ po R x x) ∧ po R x y →
      refsRels (anc R) x = rels (anc R) x ∩ refs (anc R) y := by
  rintro ⟨⟨hR, hx⟩, hxy⟩
  rw [(pm97_51 ⟨hR, hx⟩).1.1, (pm97_51 ⟨hR, hx⟩).1.2]
  ext z
  constructor
  · intro hz
    exact ⟨hz, anc_trans ((cyc_sym hR hx z).2 hz) (po_sub_anc hxy)⟩
  · exact fun h => h.1

/-- ✱97·53. \(\vdash:R\in 1\rightarrow 1.P\in \text{Pot}ʻR.xPx.y\in \overleftrightarrow{R}_{\unicode{x2217}}ʻx.\supset.yPy \quad[\text{*92·132·133}]\) -/
theorem pm97_53 {R P : α → α → Prop} {x y : α} :
    ((R ∈ arrow one one ∧ P ∈ pot R) ∧ P x x) ∧ y ∈ refsRels (anc R) x → P y y := by
  rintro ⟨⟨⟨hR, hP⟩, hxx⟩, hy⟩
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
  obtain ⟨a, rfl⟩ := mem_pot_npow.1 hP
  rcases mem_fam.1 hy with h | h
  · obtain ⟨-, n, hn⟩ := anc_iff_npow.1 h
    have h3 : (npow R n ⨾ npow R (a + 1)) y x := ⟨x, hn, hxx⟩
    rw [npow_comm] at h3
    obtain ⟨w, hyw, hwx⟩ := h3
    have : w = y := npow_oneMany h1 n w y x ⟨hwx, hn⟩
    subst this
    exact hyw
  · obtain ⟨-, n, hn⟩ := anc_iff_npow.1 h
    have h3 : (npow R (a + 1) ⨾ npow R n) x y := ⟨x, hxx, hn⟩
    rw [npow_comm] at h3
    obtain ⟨w, hxw, hwy⟩ := h3
    have : w = y := npow_manyOne h2 n x w y ⟨hxw, hn⟩
    subst this
    exact hwy

/-- ✱97·54. \[\begin{align}&\vdash:R\in 1\rightarrow 1.xR_{\text{po}}x.\supset.(\exists P).P\in \text{Pot}ʻR.P\upharpoonright \overleftrightarrow{R}_{\unicode{x2217}}ʻx=I\upharpoonright \overleftrightarrow{R}_{\unicode{x2217}}ʻx\\ &[\text{*97·53}]\end{align}\] -/
theorem pm97_54 {R : α → α → Prop} {x : α} :
    R ∈ arrow one one ∧ po R x x →
      ∃ P, P ∈ pot R ∧ P ↾ refsRels (anc R) x = I ↾ refsRels (anc R) x := by
  rintro ⟨hR, hx⟩
  obtain ⟨p, hp⟩ := npow_succ_of_po hx
  refine ⟨npow R (p + 1), npow_mem_pot R p, ?_⟩
  funext a b
  apply propext
  constructor
  · rintro ⟨hab, hb⟩
    have hbb := pm97_53 ⟨⟨⟨hR, npow_mem_pot R p⟩, hp⟩, hb⟩
    exact ⟨npow_oneMany (mem_arrow_one_one.1 hR).1 (p + 1) a b b ⟨hab, hbb⟩, hb⟩
  · rintro ⟨hab, hb⟩
    have e : a = b := hab
    subst e
    exact ⟨pm97_53 ⟨⟨⟨hR, npow_mem_pot R p⟩, hp⟩, hb⟩, hb⟩

/-- ✱97·55. \(\vdash\colon\colon R\in 1\rightarrow 1.\supset\colon\ldotp y\in \overleftrightarrow{R}_{\unicode{x2217}}ʻx.\supset_{y}.yR_{\text{po}}y:\lor:y\in \overleftrightarrow{R}_{\unicode{x2217}}ʻx.\supset_{y}.{\sim}(yR_{\text{po}}y)\) -/
theorem pm97_55 {R : α → α → Prop} {x : α} :
    R ∈ arrow one one →
      (∀ y, y ∈ refsRels (anc R) x → po R y y) ∨ (∀ y, y ∈ refsRels (anc R) x → ¬ po R y y) := by
  intro hR
  by_cases hx : po R x x
  · left
    intro y hy
    obtain ⟨p, hp⟩ := npow_succ_of_po hx
    exact po_of_npow_succ (pm97_53 ⟨⟨⟨hR, npow_mem_pot R p⟩, hp⟩, hy⟩)
  · right
    intro y hy hyy
    obtain ⟨p, hp⟩ := npow_succ_of_po hyy
    exact hx (po_of_npow_succ (pm97_53 ⟨⟨⟨hR, npow_mem_pot R p⟩, hp⟩, pm97_101.1 hy⟩))

/-- ✱97·56. \[\begin{align}&\vdash\colon\ldotp R\in 1\rightarrow 1.x\in \overrightarrow{B}ʻR.\supset:y\in \overleftrightarrow{R}_{\unicode{x2217}}ʻx.\supset_{y}.{\sim}(yR_{\text{po}}y)\\ &[\text{*96·23·1.*97·55}]\end{align}\] -/
theorem pm97_56 {R : α → α → Prop} {x : α} :
    R ∈ arrow one one ∧ x ∈ refs Beg R → ∀ y, y ∈ refsRels (anc R) x → ¬ po R y y := by
  rintro ⟨hR, hx⟩ y hy hyy
  rw [pm97_2 hx] at hy
  have hI := IR_empty_of_beg (mem_arrow_one_one.1 hR).1 hx
  have : y ∈ IR R x := ⟨hy, hyy⟩
  rw [hI] at this
  exact this

/-- ✱97·57. \[\begin{align}&\vdash\colon\ldotp R\in 1\rightarrow 1.x\in sʻ\text{gen}ʻR.\supset:y\in \overleftrightarrow{R}_{\unicode{x2217}}ʻx.\supset_{y}.{\sim}(yR_{\text{po}}y)\\ &[\text{*97·21·56}]\end{align}\] -/
theorem pm97_57 {R : α → α → Prop} {x : α} :
    R ∈ arrow one one ∧ x ∈ sumCls (gen R) → ∀ y, y ∈ refsRels (anc R) x → ¬ po R y y := by
  rintro ⟨hR, hx⟩ y hy
  obtain ⟨b, n, hb, hbx⟩ := (mem_sumCls_gen_oneMany (mem_arrow_one_one.1 hR).1).1 hx
  have hbx' : anc R b x := anc_of_npow (dom_sub_fld R (beg_dom hb)) hbx
  rw [← pm97_14 ⟨hR, hbx'⟩] at hy
  exact pm97_56 ⟨hR, hb⟩ y hy

/-- ✱97·58. \[\begin{align}\vdash\colon\ldotp R\in 1\rightarrow \text{Cls}.\supset:x\in sʻ\text{gen}ʻR.&\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻx\subset sʻ\text{gen}ʻR:\\ & x\in pʻ\text{ᗡ}ʻʻ\text{Pot}ʻR.\supset.\overleftrightarrow{R}_{\unicode{x2217}}ʻx\subset pʻ\text{ᗡ}ʻʻ\text{Pot}ʻR\end{align}\] -/
theorem pm97_58 {R : α → α → Prop} {x : α} :
    R ∈ arrow one Cls →
      (x ∈ sumCls (gen R) → refsRels (anc R) x ⊆ sumCls (gen R)) ∧
        (x ∈ prodCls (Dcnv ʻʻ pot R) → refsRels (anc R) x ⊆ prodCls (Dcnv ʻʻ pot R)) := by
  intro hR
  have hR' := mem_arrow_one_Cls.1 hR
  refine ⟨fun hx y hy => ?_, fun hx y hy => ?_⟩
  · obtain ⟨b, n, hb, hbx⟩ := (mem_sumCls_gen_oneMany hR').1 hx
    rcases mem_fam.1 hy with h | h
    · obtain ⟨-, m, hm⟩ := anc_iff_npow.1 h
      rcases npow_oneMany_cmp hR' hbx hm with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact (mem_sumCls_gen_oneMany hR').2 ⟨b, k, hb, hk⟩
      · cases k with
        | zero =>
          have e : y = b := hk
          subst e
          exact (mem_sumCls_gen_oneMany hR').2 ⟨y, 0, hb, rfl⟩
        | succ k =>
          obtain ⟨c, -, hcb⟩ := hk
          exact absurd ⟨c, hcb⟩ (beg_not_codom hb)
    · obtain ⟨-, m, hm⟩ := anc_iff_npow.1 h
      have : npow R (n + m) b y := by rw [npow_add]; exact ⟨x, hbx, hm⟩
      exact (mem_sumCls_gen_oneMany hR').2 ⟨b, n + m, hb, this⟩
  · rw [mem_prodCls_Dcnv] at hx ⊢
    intro S hS
    obtain ⟨k, rfl⟩ := mem_pot_npow.1 hS
    rcases mem_fam.1 hy with h | h
    · obtain ⟨-, m, hm⟩ := anc_iff_npow.1 h
      obtain ⟨z, hz⟩ := hx _ (npow_mem_pot R (k + m))
      rw [show k + m + 1 = (k + 1) + m by omega, npow_add] at hz
      obtain ⟨w, hzw, hwx⟩ := hz
      have : w = y := npow_oneMany hR' m w y x ⟨hwx, hm⟩
      subst this
      exact ⟨z, hzw⟩
    · obtain ⟨-, m, hm⟩ := anc_iff_npow.1 h
      obtain ⟨z, hz⟩ := hx _ (npow_mem_pot R k)
      have : npow R (m + (k + 1)) z y := by
        rw [show m + (k + 1) = (k + 1) + m by omega, npow_add]
        exact ⟨x, hz, hm⟩
      rw [npow_add] at this
      obtain ⟨w, -, hwy⟩ := this
      exact ⟨w, hwy⟩

end PrincipiaMathematica
