import PrincipiaMathematica.Defs.Part2

/-!
# Part II, Section E: Inductive relations

Volume 1. Numbers: ✱90, ✱91, ✱92, ✱93.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

open Relation

universe u v w u'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

/-! ### Helper lemmas for Section E (not PM propositions) -/

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

private theorem I_comp (X : α → γ → Prop) : I ⨾ X = X := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, h, hz⟩
    have e : x = z := h
    exact e ▸ hz
  · intro h
    exact ⟨x, rfl, h⟩

private theorem comp_I (X : γ → α → Prop) : X ⨾ I = X := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, hz, h⟩
    have e : z = y := h
    exact e ▸ hz
  · intro h
    exact ⟨y, h, rfl⟩

private theorem comp_idf_of_codom {Q : γ → α → Prop} {B : Set α} (h : codom Q ⊆ B) :
    Q ⨾ (I ↾ B) = Q := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, hz, h', -⟩
    have e : z = y := h'
    exact e ▸ hz
  · intro hxy
    exact ⟨y, hxy, rfl, h ⟨x, hxy⟩⟩

private theorem npow_comp_idf (R : α → α → Prop) (n : ℕ) : npow R n ⨾ (I ↾ fld R) = ipow R n := by
  cases n with
  | zero => rw [npow_zero_comp, ipow_zero]
  | succ n =>
    rw [ipow_succ_eq]
    exact comp_idf_of_codom fun y ⟨x, h⟩ => (fld_of_npow_succ h).2

private theorem Rts_refl (R : α → α → Prop) (Q : γ → α → Prop) : Rts R Q Q :=
  (Rts_iff R Q Q).2 ⟨0, (comp_npow_zero R Q).symm⟩

private theorem Rst_refl (R : α → α → Prop) (Q : α → γ → Prop) : Rst R Q Q :=
  (Rst_iff R Q Q).2 ⟨0, (npow_zero_comp R Q).symm⟩

private theorem Rts_step {R : α → α → Prop} {S Q : γ → α → Prop} (h : Rts R S Q) :
    Rts R (S ⨾ R) Q := by
  obtain ⟨n, rfl⟩ := (Rts_iff R S Q).1 h
  exact (Rts_iff R _ Q).2 ⟨n + 1, by rw [npow_succ, rp_assoc]⟩

private theorem Rst_step {R : α → α → Prop} {S Q : α → γ → Prop} (h : Rst R S Q) :
    Rst R (R ⨾ S) Q := by
  obtain ⟨n, rfl⟩ := (Rst_iff R S Q).1 h
  exact (Rst_iff R _ Q).2 ⟨n + 1, by rw [npow_succ', rp_assoc]⟩

private theorem Rts_cases {R : α → α → Prop} {P Q : γ → α → Prop} :
    Rts R P Q ↔ P = Q ∨ Rts R P (Q ⨾ R) := by
  rw [Rts_iff, Rts_iff]
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl (comp_npow_zero R Q)
    | succ n => exact Or.inr ⟨n, by rw [npow_succ', rp_assoc]⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨0, (comp_npow_zero R P).symm⟩
    · exact ⟨n + 1, by rw [npow_succ', rp_assoc]⟩

private theorem Rst_cases {R : α → α → Prop} {P Q : α → γ → Prop} :
    Rst R P Q ↔ P = Q ∨ Rst R P (R ⨾ Q) := by
  rw [Rst_iff, Rst_iff]
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl (npow_zero_comp R Q)
    | succ n => exact Or.inr ⟨n, by rw [npow_succ, rp_assoc]⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨0, (npow_zero_comp R P).symm⟩
    · exact ⟨n + 1, by rw [npow_succ, rp_assoc]⟩

private theorem fld_iff_of_npow {R : α → α → Prop} {n : ℕ} {x y : α} (h : npow R n x y) :
    x ∈ fld R ↔ y ∈ fld R := by
  cases n with
  | zero =>
    have e : x = y := h
    rw [e]
  | succ n => exact ⟨fun _ => (fld_of_npow_succ h).2, fun _ => (fld_of_npow_succ h).1⟩

private theorem cnv_npow (R : α → α → Prop) (n : ℕ) : (npow R n)˘ = npow R˘ n := by
  induction n with
  | zero =>
    funext x y
    exact propext ⟨fun h => h.symm, fun h => h.symm⟩
  | succ n ih =>
    rw [npow_succ', show npow R˘ (n + 1) = npow R˘ n ⨾ R˘ from rfl, ← ih]
    funext x y
    apply propext
    constructor
    · rintro ⟨z, h1, h2⟩
      exact ⟨z, h2, h1⟩
    · rintro ⟨z, h1, h2⟩
      exact ⟨z, h2, h1⟩

private theorem cnv_ipow (R : α → α → Prop) (n : ℕ) : (ipow R n)˘ = ipow R˘ n := by
  funext x y
  apply propext
  show ipow R n y x ↔ ipow R˘ n x y
  rw [ipow_apply, ipow_apply, fld_cnv, ← cnv_npow]
  exact ⟨fun ⟨h1, h2⟩ => ⟨(fld_iff_of_npow h2).1 h1, h2⟩,
    fun ⟨h1, h2⟩ => ⟨(fld_iff_of_npow h2).2 h1, h2⟩⟩

private theorem mem_of_npow {R : α → α → Prop} {M : Set α} (hM : R ʻʻ M ⊆ M) {n : ℕ} :
    ∀ {x y : α}, npow R n x y → y ∈ M → x ∈ M := by
  induction n with
  | zero =>
    intro x y h hy
    have e : x = y := h
    exact e ▸ hy
  | succ n ih =>
    rintro x y ⟨b, hb, hby⟩ hy
    exact ih hb (hM ⟨y, hy, hby⟩)

private theorem anc_comp_po (R : α → α → Prop) : anc R ⨾ po R = po R := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a, ha, hay⟩
    rcases anc_iff_po.1 ha with ⟨rfl, -⟩ | h
    · exact hay
    · exact po_trans h hay
  · intro h
    obtain ⟨n, hn⟩ := po_iff_npow.1 h
    exact ⟨x, anc_refl (fld_of_npow_succ hn).1, h⟩

private theorem po_comp_anc (R : α → α → Prop) : po R ⨾ anc R = po R := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a, hxa, ha⟩
    rcases anc_iff_po.1 ha with ⟨rfl, -⟩ | h
    · exact hxa
    · exact po_trans hxa h
  · intro h
    obtain ⟨n, hn⟩ := po_iff_npow.1 h
    exact ⟨y, h, anc_refl (fld_of_npow_succ hn).2⟩

private theorem cnv_comp (X : α → β → Prop) (Y : β → γ → Prop) : (X ⨾ Y)˘ = Y˘ ⨾ X˘ := by
  funext x y
  apply propext
  exact ⟨fun ⟨z, h1, h2⟩ => ⟨z, h2, h1⟩, fun ⟨z, h1, h2⟩ => ⟨z, h2, h1⟩⟩

private theorem comp_cres (X : α → β → Prop) (Y : β → γ → Prop) (B : Set γ) :
    X ⨾ (Y ↾ B) = X ⨾ Y ↾ B := by
  funext x y
  apply propext
  exact ⟨fun ⟨z, h1, h2, h3⟩ => ⟨⟨z, h1, h2⟩, h3⟩, fun ⟨⟨z, h1, h2⟩, h3⟩ => ⟨z, h1, h2, h3⟩⟩

private theorem dres_comp (A : Set α) (X : α → β → Prop) (Y : β → γ → Prop) :
    A ◁ X ⨾ Y = A ◁ (X ⨾ Y) := by
  funext x y
  apply propext
  exact ⟨fun ⟨z, ⟨h1, h2⟩, h3⟩ => ⟨h1, z, h2, h3⟩, fun ⟨h1, z, h2, h3⟩ => ⟨z, ⟨h1, h2⟩, h3⟩⟩

private theorem cres_eq_self {X : α → β → Prop} {B : Set β} (h : codom X ⊆ B) : X ↾ B = X := by
  funext x y
  apply propext
  exact ⟨fun h' => h'.1, fun h' => ⟨h', h ⟨x, h'⟩⟩⟩

private theorem dres_eq_self {X : α → β → Prop} {A : Set α} (h : dom X ⊆ A) : A ◁ X = X := by
  funext x y
  apply propext
  exact ⟨fun h' => h'.2, fun h' => ⟨h ⟨y, h'⟩, h'⟩⟩

private theorem comp_comp_cnv {Q : β → γ → Prop} (hQ : ∀ x y z, Q x z ∧ Q y z → x = y)
    (T : α → β → Prop) : T ⨾ Q ⨾ Q˘ = T ↾ dom Q := by
  funext x y
  apply propext
  constructor
  · rintro ⟨b, ⟨a, hxa, hab⟩, hyb⟩
    have e : a = y := hQ a y b ⟨hab, hyb⟩
    subst e
    exact ⟨hxa, b, hyb⟩
  · rintro ⟨hxy, b, hyb⟩
    exact ⟨b, ⟨y, hxy, hyb⟩, hyb⟩

private theorem cnv_comp_comp {Q : β → α → Prop} (hQ : ∀ x y z, Q x y ∧ Q x z → y = z)
    (T : α → γ → Prop) : Q˘ ⨾ Q ⨾ T = codom Q ◁ T := by
  funext x y
  apply propext
  constructor
  · rintro ⟨b, ⟨a, hax, hab⟩, hby⟩
    have e : x = b := hQ a x b ⟨hax, hab⟩
    subst e
    exact ⟨⟨a, hax⟩, hby⟩
  · rintro ⟨⟨a, hax⟩, hxy⟩
    exact ⟨x, ⟨a, hax, hax⟩, hxy⟩

private theorem ipow_oneMany {R : α → α → Prop} (hR : R ∈ arrow one Cls) (n : ℕ) :
    ipow R n ∈ arrow one Cls := by
  rw [mem_arrow_one_Cls] at *
  rintro x y z ⟨hx, hy⟩
  rw [ipow_apply] at hx hy
  exact npow_oneMany hR n x y z ⟨hx.2, hy.2⟩

private theorem ipow_manyOne {R : α → α → Prop} (hR : R ∈ arrow Cls one) (n : ℕ) :
    ipow R n ∈ arrow Cls one := by
  rw [mem_arrow_Cls_one] at *
  rintro x y z ⟨hy, hz⟩
  rw [ipow_apply] at hy hz
  exact npow_manyOne hR n x y z ⟨hy.2, hz.2⟩

private theorem dom_npow_succ {R : α → α → Prop} (h : codom R ⊆ dom R) (n : ℕ) :
    dom (npow R (n + 1)) = dom R := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, hxa, -⟩ := npow_succ_iff.1 hy
    exact ⟨a, hxa⟩
  · intro hx
    induction n with
    | zero =>
      rw [npow_one]
      exact hx
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨b, -, hby⟩ := id hy
      obtain ⟨z, hz⟩ := h ⟨b, hby⟩
      exact ⟨z, y, hy, hz⟩

private theorem fld_sub_dom {R : α → α → Prop} (h : codom R ⊆ dom R) : fld R ⊆ dom R := by
  rintro x ⟨y, h' | h'⟩
  · exact ⟨y, h'⟩
  · exact h ⟨y, h'⟩

private theorem dom_ipow {R : α → α → Prop} (h : codom R ⊆ dom R) (n : ℕ) :
    dom (ipow R n) = dom R := by
  cases n with
  | zero =>
    rw [ipow_zero]
    ext x
    constructor
    · rintro ⟨y, hxy, hy⟩
      have e : x = y := hxy
      subst e
      exact fld_sub_dom h hy
    · intro hx
      exact ⟨x, rfl, ⟨_, Or.inl hx.choose_spec⟩⟩
  | succ n => rw [ipow_succ_eq, dom_npow_succ h]

private theorem mem_minImg (P : α → α → Prop) (K : Set (α → α → Prop)) (A : Set α) :
    A ∈ Rfwd (minP P) ʻʻ Dcnv ʻʻ K ↔ ∃ T, T ∈ K ∧ A = refs (minP P) (codom T) := by
  constructor
  · rintro ⟨B, ⟨T, hT, hB⟩, hA⟩
    have hB' : B = codom T := hB
    have hA' : A = refs (minP P) B := hA
    subst hB'
    exact ⟨T, hT, hA'⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨codom T, ⟨T, hT, rfl⟩, rfl⟩

private theorem mem_gen' {P : α → α → Prop} {A : Set α} :
    A ∈ gen P ↔ ∃ n, A = refs (minP P) (codom (ipow P n)) := by
  rw [gen, mem_minImg]
  constructor
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨n, rfl⟩ := mem_potid'.1 hT
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, ipow_mem_potid P n, rfl⟩

private theorem mem_prodCls_Dcnv (K : Set (α → α → Prop)) (x : α) :
    x ∈ prodCls (Dcnv ʻʻ K) ↔ ∀ T, T ∈ K → x ∈ codom T := by
  constructor
  · intro h T hT
    exact h _ ⟨T, hT, rfl⟩
  · rintro h B ⟨T, hT, hB⟩
    have hB' : B = codom T := hB
    rw [hB']
    exact h T hT

private theorem mem_p_pot {P : α → α → Prop} {x : α} :
    x ∈ prodCls (Dcnv ʻʻ pot P) ↔ ∀ n, x ∈ codom (ipow P (n + 1)) := by
  rw [mem_prodCls_Dcnv]
  constructor
  · intro h n
    exact h _ (ipow_succ_mem_pot P n)
  · intro h T hT
    obtain ⟨n, rfl⟩ := mem_pot'.1 hT
    exact h n

private theorem img_cnv_codom (P : α → α → Prop) (T : β → α → Prop) :
    P˘ ʻʻ codom T = codom (T ⨾ P) := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, hxy⟩, hyz⟩
    exact ⟨x, y, hxy, hyz⟩
  · rintro ⟨x, y, hxy, hyz⟩
    exact ⟨y, ⟨x, hxy⟩, hyz⟩

private theorem codom_ipow_succ (P : α → α → Prop) (n : ℕ) :
    codom (ipow P (n + 1)) = P˘ ʻʻ codom (ipow P n) := by
  rw [img_cnv_codom, ipow_succ]

private theorem codom_ipow_succ_sub (P : α → α → Prop) (n : ℕ) :
    codom (ipow P (n + 1)) ⊆ codom (ipow P n) := by
  rintro z ⟨x, h⟩
  rw [ipow_succ'] at h
  obtain ⟨a, -, ha⟩ := h
  exact ⟨a, ha⟩

private theorem codom_ipow_mono (P : α → α → Prop) {n m : ℕ} (h : n ≤ m) :
    codom (ipow P m) ⊆ codom (ipow P n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact fun _ h => h
  | succ k ih => exact (codom_ipow_succ_sub P (n + k)).trans (ih (Nat.le_add_right n k))

private theorem codom_ipow_sub_fld (P : α → α → Prop) (n : ℕ) : codom (ipow P n) ⊆ fld P :=
  fun _ ⟨_, h⟩ => (fld_of_ipow h).2

private theorem refs_minP_codom {P : α → α → Prop} {T : α → α → Prop} (h : codom T ⊆ fld P) :
    refs (minP P) (codom T) = codom T \ codom (T ⨾ P) := by
  ext x
  show (x ∈ codom T ∧ x ∈ fld P) ∧ x ∉ P˘ ʻʻ codom T ↔ _
  rw [img_cnv_codom]
  exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h h1⟩, h2⟩⟩

private theorem mem_refs_minP_ipow {P : α → α → Prop} {n : ℕ} {x : α} :
    x ∈ refs (minP P) (codom (ipow P n)) ↔
      x ∈ codom (ipow P n) ∧ x ∉ codom (ipow P (n + 1)) := by
  rw [refs_minP_codom (codom_ipow_sub_fld P n), ← ipow_succ]
  exact Iff.rfl

private theorem eq_Null {A : Set α} (h : ∀ x, x ∉ A) : A = Λ := by
  rw [Null_eq_empty]
  exact Set.eq_empty_iff_forall_notMem.2 h

private theorem cycle_pred {P : α → α → Prop} {m : ℕ} {x : α} (hx : npow P (m + 1) x x) :
    ∀ k, ∃ w, npow P k w x ∧ npow P (m + 1) w w := by
  intro k
  induction k with
  | zero => exact ⟨x, rfl, hx⟩
  | succ k ih =>
    obtain ⟨w, hwx, hw⟩ := ih
    obtain ⟨b, hb, hbw⟩ := id hw
    refine ⟨b, npow_succ_iff.2 ⟨w, hbw, hwx⟩, ?_⟩
    rw [npow_succ']
    exact ⟨w, hbw, hb⟩

/-!
## [✱90] On the ancestral relation

*(Vol. 1, p. 576)*

> *Summary of* *90.
>
> If \(R\) is any relation, "\(x R_{\unicode{x2217}} y\)" is to mean "\(x\) is an ancestor of \(y\) with respect to \(R\)," where a term counts as its own ancestor provided it belongs to the field of \(R\). The definition of \(R_{\unicode{x2217}}\) is as follows:
>
> 90·01. \(R_{\unicode{x2217}} = \hat{x}\hat{y}\{x \in CʻR:\breve{R}ʻʻ\mu \subset \mu . x \in \mu .\supset_{\mu}. y \in \mu\} \quad \text{Df}\)
>
> That is, \(x R_{\unicode{x2217}} y\) is to hold when \(x\) belongs to the field of \(R\), and \(y\) belongs to every hereditary class to which \(x\) belongs; a hereditary class being a class \(\mu\) such that \(\breve{R}ʻʻ\mu \subset \mu\), *i.e.* such that all successors of \(\mu\)'s are \(\mu\)'s.
>
> *90·02. \(\breve{R}_{\unicode{x2217}} = \text{Cnv}ʻR_{\unicode{x2217}} \quad \text{Df}\)
>
> This definition serves merely to decide the ambiguity between \((\breve{R})_{\unicode{x2217}}\) and \(\text{Cnv}ʻR_{\unicode{x2217}}\), either of which might be meant of \(\breve{R}_{\unicode{x2217}}\). It will be shown, however, that the two are equal (*90·132).
>
> The most important propositions of this number are the following:
>
> …

**Lean reading.** `R_*` is `anc R` (homogeneous `R : α → α → Prop`), defined exactly
as ✱90·01 (`x ∈ C'R` and `y` in every hereditary class `μ` containing `x`, hereditary meaning
`R̆''μ ⊂ μ`); `R̆_*` is `ancCnv R`, the converse of `R_*` (✱90·02), and ✱90·132 proves it equal to
`anc R˘`. The classes `μ` of the formal implications `⊃_μ` are `M : Set α`; the hypotheses of
`⊃_μ` and `⊃_{z,w}` are products and stay conjunctions. `R⃖_*'x` is `rels (anc R) x`, `R̆_*''α`
is `ancCnv R ʻʻ A`, `R_*²` is `rsq (anc R)`, and PM's chains of `=` are conjunctions of their
links. The proofs use that `anc R` is the reflexive-transitive closure restricted to `C'R`
(`anc_iff_reflTransGen`) and the exact powers `R^n` of a private helper.

**Status.** proved (all propositions; ✱90·01, ✱90·02 definition).
-/

/-- ✱90·01 (Df). \(R_{\unicode{x2217}} = \hat{x}\hat{y}\{x\in CʻR:\breve{R}ʻʻ\mu\subset \mu.x\in \mu.\supset_{\mu}.y\in \mu\} \quad\text{Df}\) -/
theorem pm90_01 (R : α → α → Prop) :
    anc R = fun x y => x ∈ fld R ∧ ∀ M : Set α, R˘ ʻʻ M ⊆ M ∧ x ∈ M → y ∈ M := rfl

/-- ✱90·02 (Df). \(\breve{R}_{\unicode{x2217}} = \text{Cnv}ʻR_{\unicode{x2217}} \quad\text{Df}\) -/
theorem pm90_02 (R : α → α → Prop) : Desc Cnv (anc R) (fun Q => ancCnv R = Q) :=
  (desc_Cnv _ _).2 rfl

/-- ✱90·1. \(\vdash\colon\ldotp xR_{\unicode{x2217}}y. \equiv :x\in CʻR:\breve{R}ʻʻ\mu\subset \mu.x\in \mu.\supset_{\mu}.y\in \mu \quad[\text{*21·3.(*90·01)}]\) -/
theorem pm90_1 {R : α → α → Prop} {x y : α} :
    anc R x y ↔ x ∈ fld R ∧ ∀ M : Set α, R˘ ʻʻ M ⊆ M ∧ x ∈ M → y ∈ M := Iff.rfl

/-- ✱90·101. \(\vdash:\breve{R}ʻʻ\mu\subset \mu. \equiv .Rʻʻ-\mu\subset -\mu\) -/
theorem pm90_101 {R : α → α → Prop} {M : Set α} : R˘ ʻʻ M ⊆ M ↔ R ʻʻ Mᶜ ⊆ Mᶜ := by
  constructor
  · rintro h x ⟨y, hy, hxy⟩ hx
    exact hy (h ⟨x, hx, hxy⟩)
  · rintro h x ⟨y, hy, hyx⟩
    by_contra hx
    exact h ⟨x, hx, hyx⟩ hy

/-- ✱90·102. \(\vdash\colon\ldotp \breve{R}ʻʻ\mu\subset \mu.x\in \mu.\supset_{\mu}.y\in \mu: \equiv :Rʻʻ\mu\subset \mu.y\in \mu.\supset_{\mu}.x\in \mu\) -/
theorem pm90_102 {R : α → α → Prop} {x y : α} :
    (∀ M : Set α, R˘ ʻʻ M ⊆ M ∧ x ∈ M → y ∈ M) ↔ (∀ M : Set α, R ʻʻ M ⊆ M ∧ y ∈ M → x ∈ M) := by
  constructor
  · rintro h M ⟨hM, hy⟩
    by_contra hx
    exact h Mᶜ ⟨(pm90_101 (R := R˘)).1 hM, hx⟩ hy
  · rintro h M ⟨hM, hx⟩
    by_contra hy
    exact h Mᶜ ⟨pm90_101.1 hM, hy⟩ hx

/-- ✱90·11. \(\vdash\colon\ldotp xR_{\unicode{x2217}}y. \equiv :x\in CʻR:Rʻʻ\mu\subset \mu.y\in \mu.\supset_{\mu}.x\in \mu \quad[\text{*90·1·102}]\) -/
theorem pm90_11 {R : α → α → Prop} {x y : α} :
    anc R x y ↔ x ∈ fld R ∧ ∀ M : Set α, R ʻʻ M ⊆ M ∧ y ∈ M → x ∈ M :=
  and_congr_right fun _ => pm90_102

/-- ✱90·111. \[\begin{align}&\vdash\colon\colon xR_{\unicode{x2217}}y. \equiv \colon\ldotp x\in CʻR\colon\ldotp z\in \mu.zRw.\supset_{z,w}.w\in \mu:x\in \mu:\supset_{\mu}.y\in \mu\\ &[\text{*90·1.*37·171}]\end{align}\] -/
theorem pm90_111 {R : α → α → Prop} {x y : α} :
    anc R x y ↔
      x ∈ fld R ∧ ∀ M : Set α, (∀ z w, z ∈ M ∧ R z w → w ∈ M) ∧ x ∈ M → y ∈ M := by
  have key : ∀ M : Set α, R˘ ʻʻ M ⊆ M ↔ ∀ z w, z ∈ M ∧ R z w → w ∈ M := fun M =>
    ⟨fun h z w ⟨hz, hzw⟩ => h ⟨z, hz, hzw⟩, fun h w ⟨z, hz, hzw⟩ => h z w ⟨hz, hzw⟩⟩
  show (x ∈ fld R ∧ ∀ M : Set α, R˘ ʻʻ M ⊆ M ∧ x ∈ M → y ∈ M) ↔ _
  simp only [key]

/-- ✱90·112. \(\vdash\colon\ldotp xR_{\unicode{x2217}}y:\phi z.zRw.\supset_{z,w}.\phi w:\phi x:\supset.\phi y\) -/
theorem pm90_112 {R : α → α → Prop} {φ : α → Prop} {x y : α} :
    (anc R x y ∧ (∀ z w, φ z ∧ R z w → φ w)) ∧ φ x → φ y := by
  rintro ⟨⟨⟨-, h⟩, hφ⟩, hx⟩
  exact h {z | φ z} ⟨fun w ⟨z, hz, hzw⟩ => hφ z w ⟨hz, hzw⟩, hx⟩

/-- ✱90·12. \(\vdash:x\in CʻR.\equiv.xR_{\unicode{x2217}}x\) -/
theorem pm90_12 {R : α → α → Prop} {x : α} : x ∈ fld R ↔ anc R x x :=
  ⟨anc_refl, fun h => h.1⟩

/-- ✱90·13. \(\vdash:xR_{\unicode{x2217}}y.\supset.x,y\in CʻR.xR_{\unicode{x2217}}x.yR_{\unicode{x2217}}y\) -/
theorem pm90_13 {R : α → α → Prop} {x y : α} :
    anc R x y → (Mem2 x y (fld R) ∧ anc R x x) ∧ anc R y y := fun h =>
  ⟨⟨⟨h.1, anc_fld_right h⟩, anc_refl h.1⟩, anc_refl (anc_fld_right h)⟩

/-- ✱90·131. \(\vdash\colon\ldotp xR_{\unicode{x2217}}y.\equiv:y\in CʻR:Rʻʻ\mu\subset \mu.y\in \mu.\supset_{\mu}.x\in \mu\) -/
theorem pm90_131 {R : α → α → Prop} {x y : α} :
    anc R x y ↔ y ∈ fld R ∧ ∀ M : Set α, R ʻʻ M ⊆ M ∧ y ∈ M → x ∈ M := by
  constructor
  · intro h
    exact ⟨anc_fld_right h, (pm90_11.1 h).2⟩
  · rintro ⟨hy, h⟩
    refine h {z | anc R z y} ⟨?_, anc_refl hy⟩
    rintro z ⟨w, hw, hzw⟩
    exact anc_head hzw hw

/-- ✱90·132. \(\vdash.(\breve{R})_{\unicode{x2217}}=\breve{R}_{\unicode{x2217}}\) -/
theorem pm90_132 {R : α → α → Prop} : anc R˘ = ancCnv R := by
  funext x y
  exact propext ancCnv_iff.symm

/-- ✱90·14. \(\vdash.\text{D}ʻR_\unicode{x2217} = \text{ᗡ}ʻR_\unicode{x2217} = CʻR_\unicode{x2217} = CʻR\) -/
theorem pm90_14 {R : α → α → Prop} :
    (dom (anc R) = codom (anc R) ∧ codom (anc R) = fld (anc R)) ∧ fld (anc R) = fld R := by
  have h1 : dom (anc R) = fld R := by
    ext x
    exact ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨x, anc_refl h⟩⟩
  have h2 : codom (anc R) = fld R := by
    ext x
    exact ⟨fun ⟨_, h⟩ => anc_fld_right h, fun h => ⟨x, anc_refl h⟩⟩
  have h3 : fld (anc R) = fld R := by
    ext x
    constructor
    · rintro ⟨y, h | h⟩
      · exact h.1
      · exact anc_fld_right h
    · intro h
      exact ⟨x, Or.inl (anc_refl h)⟩
  exact ⟨⟨h1.trans h2.symm, h2.trans h3.symm⟩, h3⟩

/-- ✱90·141. \(\vdash:\dot{\exists}!R_\unicode{x2217}. \equiv .\dot{\exists}!R \quad[\text{*90·14.*33·24}]\) -/
theorem pm90_141 {R : α → α → Prop} : rEx (anc R) ↔ rEx R := by
  constructor
  · rintro ⟨x, y, h⟩
    obtain ⟨z, hz | hz⟩ := h.1
    · exact ⟨x, z, hz⟩
    · exact ⟨z, x, hz⟩
  · rintro ⟨x, y, h⟩
    exact ⟨x, y, R_sub_anc h⟩

/-- ✱90·15. \(\vdash.I\upharpoonright CʻR\unicode{x2abd}R_\unicode{x2217}\) -/
theorem pm90_15 {R : α → α → Prop} : I ↾ fld R ⪽ anc R := by
  rintro x y ⟨h, hy⟩
  have e : x = y := h
  subst e
  exact anc_refl hy

/-- ✱90·151. \(\vdash.R\unicode{x2abd}R_\unicode{x2217}\) -/
theorem pm90_151 {R : α → α → Prop} : R ⪽ anc R := fun _ _ h => R_sub_anc h

/-- ✱90·16. \(\vdash.R_\unicode{x2217}\mid R\unicode{x2abd}R_\unicode{x2217}\) -/
theorem pm90_16 {R : α → α → Prop} : anc R ⨾ R ⪽ anc R := by
  rintro x z ⟨y, hxy, hyz⟩
  exact anc_tail hxy hyz

/-- ✱90·161. \(\vdash :S\unicode{x2abd} R_{\unicode{x2217}}\ldotp \supset \ldotp S\mid R\unicode{x2abd} R_{\unicode{x2217}}\) -/
theorem pm90_161 {R S : α → α → Prop} : S ⪽ anc R → S ⨾ R ⪽ anc R := by
  rintro h x z ⟨y, hxy, hyz⟩
  exact anc_tail (h x y hxy) hyz

/-- ✱90·162. \(\vdash \ldotp R^{2}\unicode{x2abd} R_{\unicode{x2217}} \quad [\text{*90·151·161}]\) -/
theorem pm90_162 {R : α → α → Prop} : rsq R ⪽ anc R := pm90_161 pm90_151

/-- ✱90·163. \(\vdash \ldotp \breve{R}ʻʻ\overleftarrow{R}_{\unicode{x2217}}ʻx\subset \overleftarrow{R}_{\unicode{x2217}}ʻx \quad[\text{*37·301.·32·19.*90·16}]\) -/
theorem pm90_163 {R : α → α → Prop} {x : α} : R˘ ʻʻ rels (anc R) x ⊆ rels (anc R) x := by
  rintro z ⟨y, hy, hyz⟩
  exact anc_tail hy hyz

/-- ✱90·164. \(\vdash \ldotp \breve{R}ʻʻ\breve{R}_{\unicode{x2217}}ʻʻ\alpha \subset \breve{R}_{\unicode{x2217}}ʻʻ\alpha \quad[\text{*37·33·201.*90·16}]\) -/
theorem pm90_164 {R : α → α → Prop} {A : Set α} : R˘ ʻʻ ancCnv R ʻʻ A ⊆ ancCnv R ʻʻ A := by
  rintro z ⟨y, ⟨a, ha, hay⟩, hyz⟩
  exact ⟨a, ha, anc_tail hay hyz⟩

/-- ✱90·17. \(\vdash \ldotp R_{\unicode{x2217}}^{2}=R_{\unicode{x2217}}\) -/
theorem pm90_17 {R : α → α → Prop} : rsq (anc R) = anc R := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, h1, h2⟩
    exact anc_trans h1 h2
  · intro h
    exact ⟨z, h, anc_refl (anc_fld_right h)⟩

/-- ✱90·171. \(\vdash \ldotp \breve{R}_{\unicode{x2217}}ʻʻ\breve{R}_{\unicode{x2217} }ʻʻ\alpha =\breve{R}_{\unicode{x2217}}ʻʻ\alpha \quad[\text{*90·17.*37·33}]\) -/
theorem pm90_171 {R : α → α → Prop} {A : Set α} :
    ancCnv R ʻʻ ancCnv R ʻʻ A = ancCnv R ʻʻ A := by
  ext z
  constructor
  · rintro ⟨y, ⟨a, ha, hay⟩, hyz⟩
    exact ⟨a, ha, anc_trans hay hyz⟩
  · rintro ⟨a, ha, haz⟩
    exact ⟨z, ⟨a, ha, haz⟩, anc_refl (anc_fld_right haz)⟩

/-- ✱90·172. \(\vdash \ldotp R\mid R_{\unicode{x2217}}\unicode{x2abd} R_{\unicode{x2217}}\) -/
theorem pm90_172 {R : α → α → Prop} : R ⨾ anc R ⪽ anc R := by
  rintro x z ⟨y, hxy, hyz⟩
  exact anc_head hxy hyz

/-- ✱90·18. \(\vdash :P\unicode{x2abd} Q\ldotp \supset \ldotp P_{\unicode{x2217} }\unicode{x2abd} Q_{\unicode{x2217}}\) -/
theorem pm90_18 {P Q : α → α → Prop} : P ⪽ Q → anc P ⪽ anc Q := by
  intro hPQ x y h
  rw [anc_iff_reflTransGen] at *
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz | hz⟩ := h1
    · exact ⟨z, Or.inl (hPQ _ _ hz)⟩
    · exact ⟨z, Or.inr (hPQ _ _ hz)⟩
  · induction h2 with
    | refl => exact ReflTransGen.refl
    | tail _ hbc ih => exact ReflTransGen.tail ih (hPQ _ _ hbc)

/-- ✱90·21. \(\vdash:\alpha\subset CʻR . \equiv .\alpha\subset \breve{R}_\unicode{x2217}ʻʻ\alpha. \equiv .\alpha\subset R_\unicode{x2217}ʻʻ\alpha\) -/
theorem pm90_21 {R : α → α → Prop} {A : Set α} :
    (A ⊆ fld R ↔ A ⊆ ancCnv R ʻʻ A) ∧ (A ⊆ ancCnv R ʻʻ A ↔ A ⊆ anc R ʻʻ A) := by
  have h1 : A ⊆ fld R ↔ A ⊆ ancCnv R ʻʻ A := by
    constructor
    · intro h x hx
      exact ⟨x, hx, anc_refl (h hx)⟩
    · intro h x hx
      obtain ⟨y, -, hyx⟩ := h hx
      exact anc_fld_right hyx
  have h2 : A ⊆ fld R ↔ A ⊆ anc R ʻʻ A := by
    constructor
    · intro h x hx
      exact ⟨x, hx, anc_refl (h hx)⟩
    · intro h x hx
      obtain ⟨y, -, hxy⟩ := h hx
      exact hxy.1
  exact ⟨h1, h1.symm.trans h2⟩

/-- ✱90·22. \(\vdash:\breve{R}ʻʻ\alpha\subset \alpha. \equiv .\breve{R}_\unicode{x2217}ʻʻ\alpha\subset \alpha\) -/
theorem pm90_22 {R : α → α → Prop} {A : Set α} : R˘ ʻʻ A ⊆ A ↔ ancCnv R ʻʻ A ⊆ A := by
  constructor
  · rintro h x ⟨y, hy, hyx⟩
    exact hyx.2 A ⟨h, hy⟩
  · rintro h x ⟨y, hy, hyx⟩
    exact h ⟨y, hy, R_sub_anc hyx⟩

/-- ✱90·23. \(\vdash:\alpha\subset CʻR.\breve{R}ʻʻ\alpha\subset \alpha. \equiv .\alpha = \breve{R}_\unicode{x2217}ʻʻ\alpha \quad[\text{*90·21·22}]\) -/
theorem pm90_23 {R : α → α → Prop} {A : Set α} :
    A ⊆ fld R ∧ R˘ ʻʻ A ⊆ A ↔ A = ancCnv R ʻʻ A := by
  constructor
  · rintro ⟨h1, h2⟩
    exact Set.Subset.antisymm (pm90_21.1.1 h1) (pm90_22.1 h2)
  · intro e
    exact ⟨pm90_21.1.2 fun x hx => (Set.ext_iff.1 e x).1 hx,
      pm90_22.2 fun x hx => (Set.ext_iff.1 e x).2 hx⟩

/-- ✱90·24. \(\vdash:\breve{R}ʻʻ\mu\subset \mu.\alpha\subset \mu.\supset.\breve{R}_\unicode{x2217}ʻʻ\alpha\subset \mu\) -/
theorem pm90_24 {R : α → α → Prop} {A M : Set α} :
    R˘ ʻʻ M ⊆ M ∧ A ⊆ M → ancCnv R ʻʻ A ⊆ M := by
  rintro ⟨hM, hA⟩ x ⟨y, hy, hyx⟩
  exact hyx.2 M ⟨hM, hA hy⟩

/-- ✱90·25. \(\vdash:\alpha\subset CʻR.\breve{R}_\unicode{x2217}ʻʻ\alpha\subset \mu.\supset.\alpha\subset \mu\) -/
theorem pm90_25 {R : α → α → Prop} {A M : Set α} :
    A ⊆ fld R ∧ ancCnv R ʻʻ A ⊆ M → A ⊆ M := by
  rintro ⟨h1, h2⟩ x hx
  exact h2 ⟨x, hx, anc_refl (h1 hx)⟩

/-- ✱90·26. \(\vdash\colon\ldotp \alpha\subset CʻR.\breve{R}ʻʻ\mu\subset \mu.\supset:\alpha\subset \mu. \equiv .\breve{R}_\unicode{x2217}ʻʻ\alpha\subset \mu\) -/
theorem pm90_26 {R : α → α → Prop} {A M : Set α} :
    A ⊆ fld R ∧ R˘ ʻʻ M ⊆ M → (A ⊆ M ↔ ancCnv R ʻʻ A ⊆ M) := by
  rintro ⟨h1, h2⟩
  exact ⟨fun hA => pm90_24 ⟨h2, hA⟩, fun h => pm90_25 ⟨h1, h⟩⟩

/-- ✱90·27. \(\vdash\colon\ldotp \alpha\subset CʻR.\supset:\alpha\cup \breve{R}ʻʻ\mu\subset \mu. \equiv .\breve{R}_\unicode{x2217}ʻʻ\alpha\cup \breve{R}ʻʻ\mu\subset \mu\) -/
theorem pm90_27 {R : α → α → Prop} {A M : Set α} :
    A ⊆ fld R → (A ∪ R˘ ʻʻ M ⊆ M ↔ ancCnv R ʻʻ A ∪ R˘ ʻʻ M ⊆ M) := by
  intro h
  rw [Set.union_subset_iff, Set.union_subset_iff]
  constructor
  · rintro ⟨hA, hM⟩
    exact ⟨pm90_24 ⟨hM, hA⟩, hM⟩
  · rintro ⟨hA, hM⟩
    exact ⟨pm90_25 ⟨h, hA⟩, hM⟩

/-- ✱90·31. \(\vdash.R_\unicode{x2217} = I\upharpoonright CʻR\unicode{x228d}R_\unicode{x2217}\mid R\) -/
theorem pm90_31 {R : α → α → Prop} : anc R = I ↾ fld R ⊍ anc R ⨾ R := by
  funext x y
  apply propext
  constructor
  · intro h
    obtain ⟨hx, n, hn⟩ := anc_iff_npow.1 h
    cases n with
    | zero =>
      have e : x = y := hn
      subst e
      exact Or.inl ⟨rfl, hx⟩
    | succ n =>
      obtain ⟨b, hb, hby⟩ := hn
      exact Or.inr ⟨b, anc_iff_npow.2 ⟨hx, n, hb⟩, hby⟩
  · rintro (⟨h, hy⟩ | h)
    · have e : x = y := h
      subst e
      exact anc_refl hy
    · exact pm90_16 x y h

/-- ✱90·311. \(\vdash.R_\unicode{x2217} = I\upharpoonright CʻR\unicode{x228d}R\mid R_\unicode{x2217}\) -/
theorem pm90_311 {R : α → α → Prop} : anc R = I ↾ fld R ⊍ R ⨾ anc R := by
  funext x y
  apply propext
  constructor
  · intro h
    obtain ⟨hx, n, hn⟩ := anc_iff_npow.1 h
    cases n with
    | zero =>
      have e : x = y := hn
      subst e
      exact Or.inl ⟨rfl, hx⟩
    | succ n =>
      obtain ⟨a, hxa, ha⟩ := npow_succ_iff.1 hn
      exact Or.inr ⟨a, hxa, anc_iff_npow.2 ⟨⟨x, Or.inr hxa⟩, n, ha⟩⟩
  · rintro (⟨h, hy⟩ | h)
    · have e : x = y := h
      subst e
      exact anc_refl hy
    · exact pm90_172 x y h

/-- ✱90·32. \(\vdash.R\mid R_{\unicode{x2217}}=R\unicode{x228d}R\mid R_{\unicode{x2217}}\mid R=R_{\unicode{x2217}}\mid R\) -/
theorem pm90_32 {R : α → α → Prop} :
    R ⨾ anc R = R ⊍ R ⨾ anc R ⨾ R ∧ R ⊍ R ⨾ anc R ⨾ R = anc R ⨾ R := by
  rw [← po_eq_comp_anc, ← po_eq_anc_comp]
  exact ⟨po_eq_or_tail R, (po_eq_or_tail R).symm⟩

/-- ✱90·33. \(\vdash.R_{\unicode{x2217}}ʻʻ\alpha=(\alpha\cap CʻR)\cup R_{\unicode{x2217}}ʻʻRʻʻ\alpha=(\alpha\cap CʻR)\cup RʻʻR_{\unicode{x2217}}ʻʻ\alpha\) -/
theorem pm90_33 {R : α → α → Prop} {A : Set α} :
    anc R ʻʻ A = (A ∩ fld R) ∪ anc R ʻʻ R ʻʻ A ∧
      (A ∩ fld R) ∪ anc R ʻʻ R ʻʻ A = (A ∩ fld R) ∪ R ʻʻ anc R ʻʻ A := by
  rw [img_comp, img_comp, ← po_eq_anc_comp, ← po_eq_comp_anc]
  exact ⟨anc_img_eq R A, rfl⟩

/-- ✱90·331. \[\begin{align}&\vdash.\breve{R}_{\unicode{x2217}}ʻʻ\alpha=(\alpha\cap CʻR)\cup \breve{R}_{\unicode{x2217}}ʻʻ\breve{R}ʻʻ\alpha=(\alpha\cap CʻR)\cup \breve{R}ʻʻ\breve{R}_{\unicode{x2217}}ʻʻ\alpha\\ &[\text{Proof as in *90·33}]\end{align}\] -/
theorem pm90_331 {R : α → α → Prop} {A : Set α} :
    ancCnv R ʻʻ A = (A ∩ fld R) ∪ ancCnv R ʻʻ R˘ ʻʻ A ∧
      (A ∩ fld R) ∪ ancCnv R ʻʻ R˘ ʻʻ A = (A ∩ fld R) ∪ R˘ ʻʻ ancCnv R ʻʻ A := by
  rw [← pm90_132, ← fld_cnv R]
  exact pm90_33

/-- ✱90·34. \[\begin{align}&\vdash:\alpha\subset CʻR.\supset.R_{\unicode{x2217}}ʻʻ\alpha=\alpha\cup R_{\unicode{x2217}}ʻʻRʻʻ\alpha=\alpha\cup RʻʻR_{\unicode{x2217}}ʻʻ\alpha\\ &[\text{*90·33.*22·621}]\end{align}\] -/
theorem pm90_34 {R : α → α → Prop} {A : Set α} :
    A ⊆ fld R →
      anc R ʻʻ A = A ∪ anc R ʻʻ R ʻʻ A ∧ A ∪ anc R ʻʻ R ʻʻ A = A ∪ R ʻʻ anc R ʻʻ A := by
  intro h
  have := pm90_33 (R := R) (A := A)
  rwa [Set.inter_eq_left.2 h] at this

/-- ✱90·341. \[\begin{align}&\vdash:\alpha\subset CʻR.\supset.\breve{R}_{\unicode{x2217}}ʻʻ\alpha=\alpha\cup \breve{R}_{\unicode{x2217}}ʻʻ\breve{R}ʻʻ\alpha=\alpha\cup \breve{R}ʻʻ\breve{R}_{\unicode{x2217}}ʻʻ\alpha\\ &[\text{*90·331.*22·621}]\end{align}\] -/
theorem pm90_341 {R : α → α → Prop} {A : Set α} :
    A ⊆ fld R →
      ancCnv R ʻʻ A = A ∪ ancCnv R ʻʻ R˘ ʻʻ A ∧
        A ∪ ancCnv R ʻʻ R˘ ʻʻ A = A ∪ R˘ ʻʻ ancCnv R ʻʻ A := by
  intro h
  have := pm90_331 (R := R) (A := A)
  rwa [Set.inter_eq_left.2 h] at this

/-- ✱90·35. \(\vdash\colon\ldotp xR\mid R_{\unicode{x2217}}z.\supset:\breve{R}ʻʻ\mu\subset \mu.\overleftarrow{R}ʻx\subset \mu.\supset_{\mu}.z\in \mu\) -/
theorem pm90_35 {R : α → α → Prop} {x z : α} :
    (R ⨾ anc R) x z → ∀ M : Set α, R˘ ʻʻ M ⊆ M ∧ rels R x ⊆ M → z ∈ M := by
  rintro ⟨y, hxy, hyz⟩ M ⟨hM, hx⟩
  exact hyz.2 M ⟨hM, hx hxy⟩

/-- ✱90·351. \(\vdash\colon\ldotp \breve{R}ʻʻ\mu\subset \mu.\overleftarrow{R}ʻx\subset \mu.\supset_{\mu}.z\in \mu:\supset.xR\mid R_{\unicode{x2217}}z\) -/
theorem pm90_351 {R : α → α → Prop} {x z : α} :
    (∀ M : Set α, R˘ ʻʻ M ⊆ M ∧ rels R x ⊆ M → z ∈ M) → (R ⨾ anc R) x z := by
  intro h
  refine h {w | (R ⨾ anc R) x w} ⟨?_, ?_⟩
  · rintro v ⟨w, ⟨y, hxy, hyw⟩, hwv⟩
    exact ⟨y, hxy, anc_tail hyw hwv⟩
  · intro y hxy
    exact ⟨y, hxy, anc_refl ⟨x, Or.inr hxy⟩⟩

/-- ✱90·36. \(\vdash\colon\ldotp xR\mid R_{\unicode{x2217}}z.\equiv:\breve{R}ʻʻ\mu\subset \mu.\overleftarrow{R}ʻx\subset \mu.\supset_{\mu}.z\in \mu \quad[\text{*90·35·351}]\) -/
theorem pm90_36 {R : α → α → Prop} {x z : α} :
    (R ⨾ anc R) x z ↔ ∀ M : Set α, R˘ ʻʻ M ⊆ M ∧ rels R x ⊆ M → z ∈ M :=
  ⟨pm90_35, pm90_351⟩

/-- ✱90·4. \(\vdash.(R_{\unicode{x2217}})_{\unicode{x2217}}=R_{\unicode{x2217}}\) -/
theorem pm90_4 {R : α → α → Prop} : anc (anc R) = anc R := by
  funext x y
  apply propext
  constructor
  · intro h
    rw [anc_iff_reflTransGen] at h
    obtain ⟨hx, h⟩ := h
    have hx' : x ∈ fld R := by
      obtain ⟨z, hz | hz⟩ := hx
      · exact hz.1
      · exact anc_fld_right hz
    induction h with
    | refl => exact anc_refl hx'
    | tail _ hbc ih => exact anc_trans ih hbc
  · intro h
    exact R_sub_anc h

/-- ✱90·41. \(\vdash.CʻP_{\unicode{x2217}}\unicode{x0294f}\alpha=\alpha\cap CʻP\) -/
theorem pm90_41 {P : α → α → Prop} {A : Set α} : fld (anc P ⥏ A) = A ∩ fld P := by
  ext x
  constructor
  · rintro ⟨y, ⟨⟨hx, h⟩, -⟩ | ⟨⟨-, h⟩, hx⟩⟩
    · exact ⟨hx, h.1⟩
    · exact ⟨hx, anc_fld_right h⟩
  · rintro ⟨hA, hx⟩
    exact ⟨x, Or.inl ⟨⟨hA, anc_refl hx⟩, hA⟩⟩

/-- ✱90·42. \(\vdash.(Q_{\unicode{x2217}}\unicode{x0294f}\alpha)_{\unicode{x2217}}=Q_{\unicode{x2217}}\unicode{x0294f}\alpha\) -/
theorem pm90_42 {Q : α → α → Prop} {A : Set α} : anc (anc Q ⥏ A) = anc Q ⥏ A := by
  funext x y
  apply propext
  constructor
  · intro h
    rw [anc_iff_reflTransGen] at h
    obtain ⟨hx, h⟩ := h
    rw [pm90_41] at hx
    induction h with
    | refl => exact ⟨⟨hx.1, anc_refl hx.2⟩, hx.1⟩
    | tail _ hbc ih => exact ⟨⟨ih.1.1, anc_trans ih.1.2 hbc.1.2⟩, hbc.2⟩
  · intro h
    exact R_sub_anc h

/-!
## [✱91] On powers of a relation

*(Vol. 1, p. 585)*

> *Summary of* *91.
>
> In the present number, we consider the class of relations \[ R, R^{2}, R^{3}, \ldots \]
>
> …

**Lean reading.** `R_st` and `R_ts` are `Rst R` and `Rts R`, the ancestrals of `R|`
(`relProdL R`) and `|R` (`relProdR R`); the relations they relate have a free type
(`α → γ → Prop`, resp. `γ → α → Prop`), as PM's are typically ambiguous. `Pot'R` and `Potid'R`
are the value functions `pot R`, `potid R` (✱91·03·04), `R⃗_ts'Q` is `refs (Rts R) Q`, `Q|''κ` is
`relProdL Q ʻʻ K`, `|Q''κ` is `relProdR Q ʻʻ K`, `ι'Q` is `ι Q`. `R_po` is `po R`, and ✱91·05
keeps the description `Pot'R` (`Desc Pot R`). `R̆_po` is the converse `(po R)˘` (as `R̆_*` by
✱90·02; ✱91·53 proves it equal to `po R˘`). `P, Q ∈ κ` is `Mem2 P Q K`; chains of `=` and `⊂` are
conjunctions of links, nested to the left. The proofs use a private description of `Pot'R` and
`Potid'R` as the exact powers `R^{n+1}` and `R^n` (with `R^0 = I ↾ C'R`).

**Status.** proved (all propositions; ✱91·01–✱91·05 definition).
-/

/-- ✱91·01 (Df). \(R_{\text{st}}=(R\mid)_{\unicode{x2217}} \quad\text{Df}\) -/
theorem pm91_01 (R : α → α → Prop) :
    (Rst R : (α → γ → Prop) → (α → γ → Prop) → Prop) = anc (relProdL R) := rfl

/-- ✱91·02 (Df). \(R_{\text{ts}}=(\mid R)_{\unicode{x2217}} \quad\text{Df}\) -/
theorem pm91_02 (R : α → α → Prop) :
    (Rts R : (γ → α → Prop) → (γ → α → Prop) → Prop) = anc (relProdR R) := rfl

/-- ✱91·03 (Df). \(\text{Pot}ʻR=\overrightarrow{R}_{\text{ts}}ʻR \quad\text{Df}\) -/
theorem pm91_03 (R : α → α → Prop) : pot R = refs (Rts R) R := rfl

/-- ✱91·04 (Df). \(\text{Potid}ʻR=\overrightarrow{R}_{\text{ts}}ʻ(I\upharpoonright CʻR) \quad\text{Df}\) -/
theorem pm91_04 (R : α → α → Prop) : potid R = refs (Rts R) (I ↾ fld R) := rfl

/-- ✱91·05 (Df). \(R_{\text{po}}=\dot{s}ʻ\text{Pot}ʻR \quad\text{Df}\) -/
theorem pm91_05 (R : α → α → Prop) : Desc Pot R (fun L => po R = sumRel L) :=
  (desc_graph _ _ _).2 rfl

/-- ✱91·1. \(\vdash\colon\colon PR_{\text{st}}Q.\equiv\colon\ldotp S\in \mu.\supset_{S}.R\mid S\in \mu:Q\in \mu:\supset_{\mu}.P\in \mu\) -/
theorem pm91_1 {R : α → α → Prop} {P Q : α → γ → Prop} :
    Rst R P Q ↔ ∀ M : Set (α → γ → Prop), (∀ S, S ∈ M → R ⨾ S ∈ M) ∧ Q ∈ M → P ∈ M := by
  constructor
  · intro h M ⟨hM, hQ⟩
    obtain ⟨n, rfl⟩ := (Rst_iff R P Q).1 h
    clear h
    induction n with
    | zero => rw [npow_zero_comp]; exact hQ
    | succ n ih => rw [npow_succ', rp_assoc]; exact hM _ ih
  · intro h
    exact h {S | Rst R S Q} ⟨fun S hS => Rst_step hS, Rst_refl R Q⟩

/-- ✱91·11. \(\vdash\colon\colon PR_{\text{ts}}Q.\equiv\colon\ldotp S\in \mu.\supset_{S}.S\mid R\in \mu:Q\in \mu:\supset_{\mu}.P\in \mu\) -/
theorem pm91_11 {R : α → α → Prop} {P Q : γ → α → Prop} :
    Rts R P Q ↔ ∀ M : Set (γ → α → Prop), (∀ S, S ∈ M → S ⨾ R ∈ M) ∧ Q ∈ M → P ∈ M := by
  constructor
  · intro h M ⟨hM, hQ⟩
    obtain ⟨n, rfl⟩ := (Rts_iff R P Q).1 h
    clear h
    induction n with
    | zero => rw [comp_npow_zero]; exact hQ
    | succ n ih => rw [npow_succ, ← rp_assoc]; exact hM _ ih
  · intro h
    exact h {S | Rts R S Q} ⟨fun S hS => Rts_step hS, Rts_refl R Q⟩

/-- ✱91·12. \(\vdash:P\in \text{Pot}ʻR.\equiv.PR_{\text{ts}}R \quad[\text{*32·18.(*91·03)}]\) -/
theorem pm91_12 {R P : α → α → Prop} : P ∈ pot R ↔ Rts R P R := Iff.rfl

/-- ✱91·13. \[\begin{align}&\vdash\colon\colon P\in \text{Pot}ʻR.\equiv\colon\ldotp S\in \mu.\supset_{S}.S\mid R\in \mu:R\in \mu:\supset_{\mu}.P\in \mu\\ &[\text{*91·11·12}]\end{align}\] -/
theorem pm91_13 {R P : α → α → Prop} :
    P ∈ pot R ↔ ∀ M : Set (α → α → Prop), (∀ S, S ∈ M → S ⨾ R ∈ M) ∧ R ∈ M → P ∈ M :=
  pm91_11

/-- ✱91·14. \(\vdash:P\in \text{Potid}ʻR.\equiv.PR_{\text{ts}}(I\upharpoonright CʻR) \quad[\text{*32·18.(*91·04)}]\) -/
theorem pm91_14 {R P : α → α → Prop} : P ∈ potid R ↔ Rts R P (I ↾ fld R) := Iff.rfl

/-- ✱91·15. \[\begin{align}&\vdash\colon\colon P\in \text{Potid}ʻR.\equiv\colon\ldotp S\in \mu.\supset_{S}.S\mid R\in \mu:I\upharpoonright CʻR\in \mu:\supset_{\mu}.P\in \mu\\ &[\text{*91·11·14}]\end{align}\] -/
theorem pm91_15 {R P : α → α → Prop} :
    P ∈ potid R ↔
      ∀ M : Set (α → α → Prop), (∀ S, S ∈ M → S ⨾ R ∈ M) ∧ I ↾ fld R ∈ M → P ∈ M :=
  pm91_11

/-- ✱91·16. \[\begin{align}&\vdash\colon\colon xR_{\text{po}}y.\equiv\colon\ldotp (\exists P)\colon\ldotp S\in \mu.\supset_{S}.S\mid R\in \mu:R\in \mu:\supset_{\mu}.P\in \mu\colon\ldotp xPy\\ &[\text{*41·11.(*91·05).*91·13}]\end{align}\] -/
theorem pm91_16 {R : α → α → Prop} {x y : α} :
    po R x y ↔ ∃ P : α → α → Prop,
      (∀ M : Set (α → α → Prop), (∀ S, S ∈ M → S ⨾ R ∈ M) ∧ R ∈ M → P ∈ M) ∧ P x y :=
  exists_congr fun _ => and_congr_left' pm91_13

/-- ✱91·17. \[\begin{align}&\vdash\colon\ldotp P\in \text{Potid}ʻR:\phi S.\supset_{S}.\phi(S\mid R):\phi(I\upharpoonright CʻR):\supset.\phi P\\ &\left[\text{*91·15} \frac{\hat{S}(\phi S)}{\mu}\right]\end{align}\] -/
theorem pm91_17 {R P : α → α → Prop} {φ : (α → α → Prop) → Prop} :
    (P ∈ potid R ∧ (∀ S, φ S → φ (S ⨾ R))) ∧ φ (I ↾ fld R) → φ P :=
  fun ⟨⟨hP, h⟩, h0⟩ => pm91_15.1 hP {S | φ S} ⟨h, h0⟩

/-- ✱91·171. \[\begin{align}&\vdash\colon\ldotp P\in \text{Pot}ʻR:\phi S.\supset_{S}.\phi(S\mid R):\phi R:\supset.\phi P\\ &\left[*91·13 \frac{\hat{S}(\phi S)}{\mu}\right]\end{align}\] -/
theorem pm91_171 {R P : α → α → Prop} {φ : (α → α → Prop) → Prop} :
    (P ∈ pot R ∧ (∀ S, φ S → φ (S ⨾ R))) ∧ φ R → φ P :=
  fun ⟨⟨hP, h⟩, h0⟩ => pm91_13.1 hP {S | φ S} ⟨h, h0⟩

/-- ✱91·2. \(\vdash:QR_{\text{ts}}P.\supset.(Q\mid R)R_{\text{ts}}P\) -/
theorem pm91_2 {R : α → α → Prop} {Q P : γ → α → Prop} : Rts R Q P → Rts R (Q ⨾ R) P :=
  Rts_step

/-- ✱91·201. \(\vdash:QR_{\text{st}}P.\supset.(R\mid Q)R_{\text{st}}P \quad[\text{Proof as in *91·2}]\) -/
theorem pm91_201 {R : α → α → Prop} {Q P : α → γ → Prop} : Rst R Q P → Rst R (R ⨾ Q) P :=
  Rst_step

/-- ✱91·204. \(\vdash:P\{R_{\text{ts}}\mid (\mid R)\}Q.\equiv.PR_{\text{ts}}(Q\mid R)\) -/
theorem pm91_204 {R : α → α → Prop} {P Q : γ → α → Prop} :
    (Rts R ⨾ relProdR R) P Q ↔ Rts R P (Q ⨾ R) := by
  constructor
  · rintro ⟨X, h, hX⟩
    rw [relProdR_apply] at hX
    subst hX
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

/-- ✱91·205. \(\vdash:P\{R_{\text{st}}\mid (R\mid )\}Q.\equiv.PR_{\text{st}}(R\mid Q)\) -/
theorem pm91_205 {R : α → α → Prop} {P Q : α → γ → Prop} :
    (Rst R ⨾ relProdL R) P Q ↔ Rst R P (R ⨾ Q) := by
  constructor
  · rintro ⟨X, h, hX⟩
    rw [relProdL_apply] at hX
    subst hX
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

/-- ✱91·21. \(\vdash.R_{\text{ts}}=I\unicode{x228d}R_{\text{ts}}\mid (\mid R)\) -/
theorem pm91_21 {R : α → α → Prop} :
    (Rts R : (γ → α → Prop) → (γ → α → Prop) → Prop) = I ⊍ Rts R ⨾ relProdR R := by
  funext P Q
  exact propext (Rts_cases.trans (or_congr Iff.rfl pm91_204.symm))

/-- ✱91·211. \(\vdash \ldotp R_{\text{st}}=I\unicode{x228d} R_{\text{st}}\mid (R\mid)\) -/
theorem pm91_211 {R : α → α → Prop} :
    (Rst R : (α → γ → Prop) → (α → γ → Prop) → Prop) = I ⊍ Rst R ⨾ relProdL R := by
  funext P Q
  exact propext (Rst_cases.trans (or_congr Iff.rfl pm91_205.symm))

/-- ✱91·212. \(\vdash \colon\ldotp PR_{\text{ts}}Q\ldotp \equiv :P=Q\ldotp \lor \ldotp PR_{\text{ts}}(Q\mid R)\) -/
theorem pm91_212 {R : α → α → Prop} {P Q : γ → α → Prop} :
    Rts R P Q ↔ P = Q ∨ Rts R P (Q ⨾ R) := Rts_cases

/-- ✱91·213. \(\vdash \colon\ldotp PR_{\text{st}}Q\ldotp \equiv :P=Q\ldotp \lor \ldotp PR_{\text{st}}(R\mid Q)\) -/
theorem pm91_213 {R : α → α → Prop} {P Q : α → γ → Prop} :
    Rst R P Q ↔ P = Q ∨ Rst R P (R ⨾ Q) := Rst_cases

/-- ✱91·22. \(\vdash \ldotp \overrightarrow{R}_{\text{ts}}ʻQ=\iota ʻQ\cup \overrightarrow{R}_{\text{ts}}ʻ(Q\mid R)\quad[\text{*91·212.*32·18.*51·15}]\) -/
theorem pm91_22 {R : α → α → Prop} {Q : γ → α → Prop} :
    refs (Rts R) Q = ι Q ∪ refs (Rts R) (Q ⨾ R) := by
  ext P
  exact Rts_cases

/-- ✱91·221. \(\vdash \ldotp \overrightarrow{R}_{\text{st}}ʻQ=\iota ʻQ\cup \overrightarrow{R}_{\text{st}}ʻ(R\mid Q)\) -/
theorem pm91_221 {R : α → α → Prop} {Q : α → γ → Prop} :
    refs (Rst R) Q = ι Q ∪ refs (Rst R) (R ⨾ Q) := by
  ext P
  exact Rst_cases

/-- ✱91·23. \(\vdash \ldotp \text{Potid}ʻR=\iota ʻ(I\upharpoonright CʻR)\cup \text{Pot}ʻR\) -/
theorem pm91_23 {R : α → α → Prop} : potid R = ι (I ↾ fld R) ∪ pot R := by
  ext P
  show P ∈ potid R ↔ P = I ↾ fld R ∨ P ∈ pot R
  rw [mem_potid', mem_pot', ← ipow_zero]
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨n, rfl⟩
  · rintro (h | ⟨n, h⟩)
    · exact ⟨0, h⟩
    · exact ⟨n + 1, h⟩

/-- ✱91·231. \(\vdash \ldotp \overrightarrow{R}_{\text{ts}}ʻI=\iota ʻI\cup \text{Pot}ʻR \quad[\text{*91·22.(*91·03).*50·4}]\) -/
theorem pm91_231 {R : α → α → Prop} : refs (Rts R) I = ι I ∪ pot R := by
  ext P
  show Rts R P I ↔ P = I ∨ P ∈ pot R
  rw [Rts_iff, mem_pot']
  simp only [I_comp]
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨n, by rw [ipow_succ_eq]⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨n + 1, by rw [ipow_succ_eq]⟩

/-- ✱91·24. \(\vdash \ldotp \text{Pot}ʻR=\mid Rʻʻ\text{Potid}ʻR\) -/
theorem pm91_24 {R : α → α → Prop} : pot R = relProdR R ʻʻ potid R := by
  ext P
  show P ∈ pot R ↔ ∃ Y, Y ∈ potid R ∧ P = Y ⨾ R
  rw [mem_pot']
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨ipow R n, ipow_mem_potid R n, ipow_succ R n⟩
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨n, rfl⟩ := mem_potid'.1 hY
    exact ⟨n, (ipow_succ R n).symm⟩

/-- ✱91·241. \(\vdash :TR_{\text{ts}}P\ldotp \supset \ldotp (Q\mid T)R_{\text{ts}}(Q\mid P)\) -/
theorem pm91_241 {R : α → α → Prop} {T P : γ → α → Prop} {Q : δ → γ → Prop} :
    Rts R T P → Rts R (Q ⨾ T) (Q ⨾ P) := by
  intro h
  obtain ⟨n, rfl⟩ := (Rts_iff R T P).1 h
  exact (Rts_iff R _ _).2 ⟨n, (rp_assoc _ _ _).symm⟩

/-- ✱91·242. \(\vdash:SR_{\text{ts}}(Q\mid P).\supset.S\in Q\mid ʻʻ\overrightarrow{R}_{\text{ts}}ʻP\) -/
theorem pm91_242 {R : α → α → Prop} {S : δ → α → Prop} {Q : δ → γ → Prop} {P : γ → α → Prop} :
    Rts R S (Q ⨾ P) → S ∈ relProdL Q ʻʻ refs (Rts R) P := by
  intro h
  obtain ⟨n, rfl⟩ := (Rts_iff R S _).1 h
  exact ⟨P ⨾ npow R n, (Rts_iff R _ P).2 ⟨n, rfl⟩, rp_assoc _ _ _⟩

/-- ✱91·25. \(\vdash.\overrightarrow{R}_{\text{ts}}ʻ(Q\mid P)=Q\mid ʻʻ\overrightarrow{R}_{\text{ts}}ʻP\) -/
theorem pm91_25 {R : α → α → Prop} {Q : δ → γ → Prop} {P : γ → α → Prop} :
    refs (Rts R) (Q ⨾ P) = relProdL Q ʻʻ refs (Rts R) P := by
  ext S
  constructor
  · exact pm91_242
  · rintro ⟨X, hX, hS⟩
    rw [relProdL_apply] at hS
    subst hS
    exact pm91_241 hX

/-- ✱91·251. \(\vdash.\overrightarrow{R}_{\text{st}}ʻ(Q\mid P)=\mid Pʻʻ\overrightarrow{R}_{\text{st}}ʻQ \quad[\text{Proof as in *91·25}]\) -/
theorem pm91_251 {R : α → α → Prop} {Q : α → γ → Prop} {P : γ → δ → Prop} :
    refs (Rst R) (Q ⨾ P) = relProdR P ʻʻ refs (Rst R) Q := by
  ext S
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := (Rst_iff R S _).1 h
    exact ⟨npow R n ⨾ Q, (Rst_iff R _ Q).2 ⟨n, rfl⟩, (rp_assoc _ _ _).symm⟩
  · rintro ⟨X, hX, hS⟩
    rw [relProdR_apply] at hS
    subst hS
    obtain ⟨n, rfl⟩ := (Rst_iff R X Q).1 hX
    exact (Rst_iff R _ _).2 ⟨n, rp_assoc _ _ _⟩

/-- ✱91·26. \(\vdash.\overrightarrow{R}_{\text{ts}}ʻQ=Q\mid ʻʻ\overrightarrow{R}_{\text{ts}}ʻI \quad\left[\text{*91·25}\, \frac{I}{P}\right]\) -/
theorem pm91_26 {R : α → α → Prop} {Q : γ → α → Prop} :
    refs (Rts R) Q = relProdL Q ʻʻ refs (Rts R) I := by
  have h := pm91_25 (R := R) (Q := Q) (P := I)
  rwa [comp_I] at h

/-- ✱91·261. \(\vdash.\overrightarrow{R}_{\text{st}}ʻQ=\mid Qʻʻ\overrightarrow{R}_{\text{st}}ʻI \quad\left[\text{*91·251}\, \frac{I,\,Q}{Q,\,P}\right]\) -/
theorem pm91_261 {R : α → α → Prop} {Q : α → γ → Prop} :
    refs (Rst R) Q = relProdR Q ʻʻ refs (Rst R) I := by
  have h := pm91_251 (R := R) (Q := I) (P := Q)
  rwa [I_comp] at h

/-- ✱91·262. \[\begin{align}&\vdash:\text{ᗡ}ʻQ\subset CʻR.\supset.\overrightarrow{R}_{\text{ts}}ʻQ=Q\mid ʻʻ\text{Potid}ʻR\\ &\left[\text{*91·25}\, \frac{I\upharpoonright CʻR}{P} .\text{*50·62.(*91·04)}\right]\end{align}\] -/
theorem pm91_262 {R : α → α → Prop} {Q : γ → α → Prop} :
    codom Q ⊆ fld R → refs (Rts R) Q = relProdL Q ʻʻ potid R := by
  intro h
  have h' := pm91_25 (R := R) (Q := Q) (P := I ↾ fld R)
  rwa [comp_idf_of_codom h] at h'

/-- ✱91·263. \(\vdash.\overrightarrow{R}_{\text{ts}}ʻ(Q\mid R)=Q\mid ʻʻ\text{Pot}ʻR \quad\left[\text{*91·25}\, \frac{R}{P}.\,\text{(*91·03)}\right]\) -/
theorem pm91_263 {R : α → α → Prop} {Q : γ → α → Prop} :
    refs (Rts R) (Q ⨾ R) = relProdL Q ʻʻ pot R := pm91_25

/-- ✱91·264. \(\vdash.\text{Pot}ʻR=\iotaʻR\cup R\mid ʻʻ\text{Pot}ʻR \quad\left[\text{*91·22·263}\, \frac{R}{Q}\right]\) -/
theorem pm91_264 {R : α → α → Prop} : pot R = ι R ∪ relProdL R ʻʻ pot R := by
  show refs (Rts R) R = _
  rw [pm91_22, pm91_263]

/-- ✱91·27. \(\vdash:P\in \text{Potid}ʻR.\supset.CʻP\subset CʻR\) -/
theorem pm91_27 {R P : α → α → Prop} : P ∈ potid R → fld P ⊆ fld R := by
  intro hP x hx
  obtain ⟨n, rfl⟩ := mem_potid'.1 hP
  obtain ⟨y, h | h⟩ := hx
  · exact (fld_of_ipow h).1
  · exact (fld_of_ipow h).2

/-- ✱91·271. \(\vdash:P\in \text{Pot}ʻR.\supset.\text{D}ʻP\subset \text{D}ʻR.\text{ᗡ}ʻP\subset \text{ᗡ}ʻR\) -/
theorem pm91_271 {R P : α → α → Prop} : P ∈ pot R → dom P ⊆ dom R ∧ codom P ⊆ codom R := by
  intro hP
  obtain ⟨n, rfl⟩ := mem_pot'.1 hP
  rw [ipow_succ_eq]
  refine ⟨?_, ?_⟩
  · rintro x ⟨y, h⟩
    obtain ⟨a, hxa, -⟩ := npow_succ_iff.1 h
    exact ⟨a, hxa⟩
  · rintro y ⟨x, b, -, hby⟩
    exact ⟨b, hby⟩

/-- ✱91·28. \(\vdash:P\in \text{Potid}ʻR.\supset.P\mid R\in \text{Pot}ʻR \quad[\text{*91·24}]\) -/
theorem pm91_28 {R P : α → α → Prop} : P ∈ potid R → P ⨾ R ∈ pot R := by
  intro hP
  obtain ⟨n, rfl⟩ := mem_potid'.1 hP
  exact mem_pot'.2 ⟨n, (ipow_succ R n).symm⟩

/-- ✱91·281. \(\vdash:\text{Pot}ʻR\subset \text{Potid}ʻR.\mid Rʻʻ\text{Potid}ʻR\subset \text{Potid}ʻR \quad[\text{*91·23·24}]\) -/
theorem pm91_281 {R : α → α → Prop} :
    pot R ⊆ potid R ∧ relProdR R ʻʻ potid R ⊆ potid R := by
  refine ⟨pot_sub_potid R, ?_⟩
  rintro X ⟨Y, hY, hX⟩
  rw [relProdR_apply] at hX
  subst hX
  exact pot_sub_potid R (pm91_28 hY)

/-- ✱91·282. \(\vdash:P\in \text{Pot}ʻR.\supset.P\mid R\in \text{Pot}ʻR \quad[\text{*91·28·281}]\) -/
theorem pm91_282 {R P : α → α → Prop} : P ∈ pot R → P ⨾ R ∈ pot R :=
  fun h => pm91_28 (pot_sub_potid R h)

/-- ✱91·283. \(\vdash:\mid Rʻʻ\text{Pot}ʻR\subset \text{Pot}ʻR \quad[\text{*91·282}]\) -/
theorem pm91_283 {R : α → α → Prop} : relProdR R ʻʻ pot R ⊆ pot R := by
  rintro X ⟨Y, hY, hX⟩
  rw [relProdR_apply] at hX
  subst hX
  exact pm91_282 hY

/-- ✱91·3. \(\vdash:P\in \text{Potid}ʻR.\supset.R\mid P=P\mid R\) -/
theorem pm91_3 {R P : α → α → Prop} : P ∈ potid R → R ⨾ P = P ⨾ R := by
  intro hP
  obtain ⟨n, rfl⟩ := mem_potid'.1 hP
  rw [← ipow_succ', ipow_succ]

/-- ✱91·301. \(\vdash:P\in \overrightarrow{R}_{\text{st}}ʻ(I\upharpoonright CʻR).\supset.R\mid P=P\mid R \quad[\text{Proof as in *91·3}]\) -/
theorem pm91_301 {R P : α → α → Prop} : P ∈ refs (Rst R) (I ↾ fld R) → R ⨾ P = P ⨾ R := by
  intro hP
  obtain ⟨n, rfl⟩ := (Rst_iff R P _).1 hP
  rw [npow_comp_idf, ← ipow_succ', ipow_succ]

/-- ✱91·302. \(\vdash.\mid Rʻʻ\text{Potid}ʻR=R\mid ʻʻ\text{Potid}ʻR\) -/
theorem pm91_302 {R : α → α → Prop} : relProdR R ʻʻ potid R = relProdL R ʻʻ potid R := by
  ext X
  constructor
  · rintro ⟨Y, hY, hX⟩
    exact ⟨Y, hY, hX.trans (pm91_3 hY).symm⟩
  · rintro ⟨Y, hY, hX⟩
    exact ⟨Y, hY, hX.trans (pm91_3 hY)⟩

/-- ✱91·303. \(\vdash.\mid Rʻʻ\overrightarrow{R}_{\text{st}}ʻ(I\upharpoonright CʻR)=R\mid ʻʻ\overrightarrow{R}_{\text{st}}ʻ(I\upharpoonright CʻR) \quad[\text{Proof as in *91·302}]\) -/
theorem pm91_303 {R : α → α → Prop} :
    relProdR R ʻʻ refs (Rst R) (I ↾ fld R) = relProdL R ʻʻ refs (Rst R) (I ↾ fld R) := by
  ext X
  constructor
  · rintro ⟨Y, hY, hX⟩
    exact ⟨Y, hY, hX.trans (pm91_301 hY).symm⟩
  · rintro ⟨Y, hY, hX⟩
    exact ⟨Y, hY, hX.trans (pm91_301 hY)⟩

/-- ✱91·304. \(\vdash.\mid Rʻʻ\text{Pot}ʻR=R\mid ʻʻ\text{Pot}ʻR \quad[\text{Proof as in *91·302}]\) -/
theorem pm91_304 {R : α → α → Prop} : relProdR R ʻʻ pot R = relProdL R ʻʻ pot R := by
  ext X
  constructor
  · rintro ⟨Y, hY, hX⟩
    exact ⟨Y, hY, hX.trans (pm91_3 (pot_sub_potid R hY)).symm⟩
  · rintro ⟨Y, hY, hX⟩
    exact ⟨Y, hY, hX.trans (pm91_3 (pot_sub_potid R hY))⟩

/-- ✱91·31. \(\vdash.\text{Pot}ʻR=R\mid ʻʻ\text{Potid}ʻR \quad[\text{*91·24·301}]\) -/
theorem pm91_31 {R : α → α → Prop} : pot R = relProdL R ʻʻ potid R := by
  rw [pm91_24, pm91_302]

/-- ✱91·33. \(\vdash.\text{Potid}ʻR=\overrightarrow{R}_{\text{st}}ʻ(I\upharpoonright CʻR)\) -/
theorem pm91_33 {R : α → α → Prop} : potid R = refs (Rst R) (I ↾ fld R) := by
  ext P
  show P ∈ potid R ↔ Rst R P (I ↾ fld R)
  rw [mem_potid', Rst_iff]
  simp only [npow_comp_idf]

/-- ✱91·331. \(\vdash.\text{Pot}ʻR=\overrightarrow{R}_{\text{st}}ʻR\) -/
theorem pm91_331 {R : α → α → Prop} : pot R = refs (Rst R) R := by
  ext P
  show P ∈ pot R ↔ Rst R P R
  rw [mem_pot', Rst_iff]
  simp only [ipow_succ_eq, npow_succ]

/-- ✱91·34. \(\vdash:P,\,Q\in \text{Potid}ʻR.\supset.P\mid Q=Q\mid P\) -/
theorem pm91_34 {R P Q : α → α → Prop} : Mem2 P Q (potid R) → P ⨾ Q = Q ⨾ P := by
  rintro ⟨hP, hQ⟩
  obtain ⟨m, rfl⟩ := mem_potid'.1 hP
  obtain ⟨n, rfl⟩ := mem_potid'.1 hQ
  exact ipow_comm R m n

/-- ✱91·341. \(\vdash:P,\,Q\in \text{Potid}ʻR.\supset.P\mid Q\in \text{Potid}ʻR\) -/
theorem pm91_341 {R P Q : α → α → Prop} : Mem2 P Q (potid R) → P ⨾ Q ∈ potid R := by
  rintro ⟨hP, hQ⟩
  obtain ⟨m, rfl⟩ := mem_potid'.1 hP
  obtain ⟨n, rfl⟩ := mem_potid'.1 hQ
  rw [ipow_mul]
  exact ipow_mem_potid R _

/-- ✱91·342. \(\vdash:P\in \text{Potid}ʻR.Q\in \text{Pot}ʻR.\supset.P\mid Q\in \text{Pot}ʻR\) -/
theorem pm91_342 {R P Q : α → α → Prop} : P ∈ potid R ∧ Q ∈ pot R → P ⨾ Q ∈ pot R := by
  rintro ⟨hP, hQ⟩
  obtain ⟨m, rfl⟩ := mem_potid'.1 hP
  obtain ⟨n, rfl⟩ := mem_pot'.1 hQ
  rw [ipow_mul, ← Nat.add_assoc]
  exact ipow_succ_mem_pot R _

/-- ✱91·343. \(\vdash:P,\,Q\in \text{Pot}ʻR.\supset.P\mid Q\in \text{Pot}ʻR \quad[\text{*91·342·23}]\) -/
theorem pm91_343 {R P Q : α → α → Prop} : Mem2 P Q (pot R) → P ⨾ Q ∈ pot R :=
  fun ⟨hP, hQ⟩ => pm91_342 ⟨pot_sub_potid R hP, hQ⟩

/-- ✱91·35. \(\vdash.I\upharpoonright CʻR\in \text{Potid}ʻR \quad[\text{*91·23}]\) -/
theorem pm91_35 {R : α → α → Prop} : I ↾ fld R ∈ potid R := by
  rw [← ipow_zero]
  exact ipow_mem_potid R 0

/-- ✱91·351. \(\vdash.R\in \text{Pot}ʻR \quad[\text{*91·264}]\) -/
theorem pm91_351 {R : α → α → Prop} : R ∈ pot R := self_mem_pot R

/-- ✱91·352. \(\vdash.R^{2}\in \text{Pot}ʻR \quad[\text{*91·282·351}]\) -/
theorem pm91_352 {R : α → α → Prop} : rsq R ∈ pot R := relProd_mem_pot (self_mem_pot R)

/-- ✱91·36. \(\vdash:P\in \text{Pot}ʻR.\supset.P\mid R,R\mid P\in \text{Pot}ʻR \quad[\text{*91·343·351}]\) -/
theorem pm91_36 {R P : α → α → Prop} : P ∈ pot R → Mem2 (P ⨾ R) (R ⨾ P) (pot R) :=
  fun h => ⟨pm91_343 ⟨h, self_mem_pot R⟩, pm91_343 ⟨self_mem_pot R, h⟩⟩

/-- ✱91·37. \(\vdash\colon\ldotp \text{Potid}ʻR\subset \mu.\equiv:I\upharpoonright CʻR\in \mu:S\in \text{Potid}ʻR.S\in \mu.\supset_{S}.S\mid R\in \mu\) -/
theorem pm91_37 {R : α → α → Prop} {M : Set (α → α → Prop)} :
    potid R ⊆ M ↔ I ↾ fld R ∈ M ∧ ∀ S, S ∈ potid R ∧ S ∈ M → S ⨾ R ∈ M := by
  constructor
  · intro h
    exact ⟨h pm91_35, fun S ⟨hS, _⟩ => h (pot_sub_potid R (pm91_28 hS))⟩
  · rintro ⟨h0, h⟩ P hP
    obtain ⟨n, rfl⟩ := mem_potid'.1 hP
    induction n with
    | zero => rw [ipow_zero]; exact h0
    | succ n ih =>
      rw [ipow_succ]
      exact h _ ⟨ipow_mem_potid R n, ih (ipow_mem_potid R n)⟩

/-- ✱91·371. \[\begin{align}\vdash\colon\ldotp P\in \text{Potid}ʻ&R.\supset_{P}.\phi P:\equiv:\\ &\phi(I\upharpoonright CʻR):S\in \text{Potid}ʻR.\phi S.\supset_{S}.\phi(S\mid R) \quad[\text{*91·37}]\end{align}\] -/
theorem pm91_371 {R : α → α → Prop} {φ : (α → α → Prop) → Prop} :
    (∀ P, P ∈ potid R → φ P) ↔ φ (I ↾ fld R) ∧ ∀ S, S ∈ potid R ∧ φ S → φ (S ⨾ R) :=
  pm91_37 (M := {S | φ S})

/-- ✱91·372. \[\begin{align}&\vdash\colon\ldotp \text{Pot}ʻR\subset \mu.\equiv:R\in \mu:S\in \text{Pot}ʻR.S\in \mu.\supset_{S}.S\mid R\in \mu\\ &[\text{Proof as in *91·37}]\end{align}\] -/
theorem pm91_372 {R : α → α → Prop} {M : Set (α → α → Prop)} :
    pot R ⊆ M ↔ R ∈ M ∧ ∀ S, S ∈ pot R ∧ S ∈ M → S ⨾ R ∈ M := by
  constructor
  · intro h
    exact ⟨h pm91_351, fun S ⟨hS, _⟩ => h (pm91_282 hS)⟩
  · rintro ⟨h0, h⟩ P hP
    obtain ⟨n, rfl⟩ := mem_pot'.1 hP
    induction n with
    | zero => rw [ipow_one]; exact h0
    | succ n ih =>
      rw [ipow_succ]
      exact h _ ⟨ipow_succ_mem_pot R n, ih (ipow_succ_mem_pot R n)⟩

/-- ✱91·373. \[\begin{align}&\vdash\colon\ldotp P\in \text{Pot}ʻR.\supset_{P}.\phi P:\equiv:\phi R:S\in \text{Pot}ʻR.\phi S.\supset_{S}.\phi(S\mid R)\\ &[\text{*91·372}]\end{align}\] -/
theorem pm91_373 {R : α → α → Prop} {φ : (α → α → Prop) → Prop} :
    (∀ P, P ∈ pot R → φ P) ↔ φ R ∧ ∀ S, S ∈ pot R ∧ φ S → φ (S ⨾ R) :=
  pm91_372 (M := {S | φ S})

/-- ✱91·41. \(\vdash.\overrightarrow{R}_{\text{ts}}ʻ(P\mid R)=P\mid ʻʻ\text{Pot}ʻR \quad\left[\text{*91·25}\, \frac{P,\,R}{Q,\,P}.\text{(*91·03)}\right]\) -/
theorem pm91_41 {R : α → α → Prop} {P : γ → α → Prop} :
    refs (Rts R) (P ⨾ R) = relProdL P ʻʻ pot R := pm91_25

/-- ✱91·411. \(\vdash.\overrightarrow{R}_{\text{st}}ʻ(R\mid P)=\mid Pʻʻ\text{Pot}ʻR \quad\left[\text{*91·251}\, \frac{R}{Q}.\text{*91·331}\right]\) -/
theorem pm91_411 {R : α → α → Prop} {P : α → γ → Prop} :
    refs (Rst R) (R ⨾ P) = relProdR P ʻʻ pot R := by
  rw [pm91_251, ← pm91_331]

/-- ✱91·42. \(\vdash.\overrightarrow{R}_{\text{ts}}ʻP=\iotaʻP\cup P\mid ʻʻ\text{Pot}ʻR \quad[\text{*91·22·41}]\) -/
theorem pm91_42 {R : α → α → Prop} {P : γ → α → Prop} :
    refs (Rts R) P = ι P ∪ relProdL P ʻʻ pot R := by
  rw [pm91_22, pm91_41]

/-- ✱91·421. \(\vdash.\overrightarrow{R}_{\text{st}}ʻP=\iotaʻP\cup \mid Pʻʻ\text{Pot}ʻR \quad[\text{*91·221·411}]\) -/
theorem pm91_421 {R : α → α → Prop} {P : α → γ → Prop} :
    refs (Rst R) P = ι P ∪ relProdR P ʻʻ pot R := by
  rw [pm91_221, pm91_411]

/-- ✱91·43. \(\vdash:P\in \text{Pot}ʻR.QR_{\text{ts}}P.\supset.Q\in \text{Pot}ʻR\) -/
theorem pm91_43 {R P Q : α → α → Prop} : P ∈ pot R ∧ Rts R Q P → Q ∈ pot R := by
  rintro ⟨hP, hQ⟩
  obtain ⟨n, rfl⟩ := mem_pot'.1 hP
  obtain ⟨k, rfl⟩ := (Rts_iff R Q _).1 hQ
  rw [← ipow_add, Nat.add_right_comm]
  exact ipow_succ_mem_pot R _

/-- ✱91·431. \(\vdash:P\in \text{Potid}ʻR.QR_{\text{ts}}P.\supset.Q\in \text{Potid}ʻR \quad[\text{Proof as in *91·43}]\) -/
theorem pm91_431 {R P Q : α → α → Prop} : P ∈ potid R ∧ Rts R Q P → Q ∈ potid R := by
  rintro ⟨hP, hQ⟩
  obtain ⟨n, rfl⟩ := mem_potid'.1 hP
  obtain ⟨k, rfl⟩ := (Rts_iff R Q _).1 hQ
  rw [← ipow_add]
  exact ipow_mem_potid R _

/-- ✱91·44. \(\vdash\colon\ldotp P,\,Q\in \text{Potid}ʻR.\supset:QR_{\text{ts}}P.\lor .PR_{\text{ts}}Q\) -/
theorem pm91_44 {R P Q : α → α → Prop} : Mem2 P Q (potid R) → Rts R Q P ∨ Rts R P Q := by
  rintro ⟨hP, hQ⟩
  obtain ⟨m, rfl⟩ := mem_potid'.1 hP
  obtain ⟨n, rfl⟩ := mem_potid'.1 hQ
  rcases Nat.le_total m n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact Or.inl ((Rts_iff R _ _).2 ⟨k, ipow_add R m k⟩)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact Or.inr ((Rts_iff R _ _).2 ⟨k, ipow_add R n k⟩)

/-- ✱91·45. \(\vdash\colon\ldotp P,\,Q\in \text{Potid}ʻR.\supset:(\exists T):T\in \text{Potid}ʻR:Q=P\mid T.\lor .P=Q\mid T\) -/
theorem pm91_45 {R P Q : α → α → Prop} :
    Mem2 P Q (potid R) → ∃ T, T ∈ potid R ∧ (Q = P ⨾ T ∨ P = Q ⨾ T) := by
  rintro ⟨hP, hQ⟩
  obtain ⟨m, rfl⟩ := mem_potid'.1 hP
  obtain ⟨n, rfl⟩ := mem_potid'.1 hQ
  rcases Nat.le_total m n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨ipow R k, ipow_mem_potid R k, Or.inl (ipow_mul R m k).symm⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨ipow R k, ipow_mem_potid R k, Or.inr (ipow_mul R n k).symm⟩

/-- ✱91·46. \[\begin{align}&\vdash\colon\ldotp P,\,Q\in \text{Potid}ʻR.\supset:(\exists T):T\in \text{Potid}ʻR:Q=T\mid P.\lor .P=T\mid Q\\ &[\text{*91·45·34}]\end{align}\] -/
theorem pm91_46 {R P Q : α → α → Prop} :
    Mem2 P Q (potid R) → ∃ T, T ∈ potid R ∧ (Q = T ⨾ P ∨ P = T ⨾ Q) := by
  intro h
  obtain ⟨T, hT, h'⟩ := pm91_45 h
  refine ⟨T, hT, ?_⟩
  rw [pm91_34 ⟨hT, h.1⟩, pm91_34 ⟨hT, h.2⟩]
  exact h'

/-- ✱91·502. \(\vdash.R\unicode{x2abd}R_{\text{po}} \quad[\text{*91·351.(*91·05).*41·13}]\) -/
theorem pm91_502 {R : α → α → Prop} : R ⪽ po R := fun _ _ h => R_sub_po h

/-- ✱91·503. \(\vdash.R^{2}\unicode{x2abd}R_{\text{po}} \quad[\text{*91·352.(*91·05).*41·13}]\) -/
theorem pm91_503 {R : α → α → Prop} : rsq R ⪽ po R := by
  rintro x z ⟨y, h1, h2⟩
  exact po_trans (R_sub_po h1) (R_sub_po h2)

/-- ✱91·504. \(\vdash.\text{D}ʻR_{\text{po}}=\text{D}ʻR.\text{ᗡ}ʻR_{\text{po}}=\text{ᗡ}ʻR.CʻR_{\text{po}}=CʻR\) -/
theorem pm91_504 {R : α → α → Prop} :
    (dom (po R) = dom R ∧ codom (po R) = codom R) ∧ fld (po R) = fld R := by
  have hd : ∀ {x y}, po R x y → x ∈ dom R := by
    intro x y h
    rw [po_eq_comp_anc] at h
    obtain ⟨a, hxa, -⟩ := h
    exact ⟨a, hxa⟩
  have hc : ∀ {x y}, po R x y → y ∈ codom R := by
    intro x y h
    rw [po_eq_anc_comp] at h
    obtain ⟨b, -, hby⟩ := h
    exact ⟨b, hby⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext x
    exact ⟨fun ⟨_, h⟩ => hd h, fun ⟨y, h⟩ => ⟨y, R_sub_po h⟩⟩
  · ext y
    exact ⟨fun ⟨_, h⟩ => hc h, fun ⟨x, h⟩ => ⟨x, R_sub_po h⟩⟩
  · ext x
    constructor
    · rintro ⟨y, h | h⟩
      · obtain ⟨z, hz⟩ := hd h
        exact ⟨z, Or.inl hz⟩
      · obtain ⟨z, hz⟩ := hc h
        exact ⟨z, Or.inr hz⟩
    · rintro ⟨y, h | h⟩
      · exact ⟨y, Or.inl (R_sub_po h)⟩
      · exact ⟨y, Or.inr (R_sub_po h)⟩

/-- ✱91·51. \(\vdash.R_{\text{po}}\mid R=R\mid R_{\text{po}}\) -/
theorem pm91_51 {R : α → α → Prop} : po R ⨾ R = R ⨾ po R := by
  calc po R ⨾ R = R ⨾ anc R ⨾ R := by rw [← po_eq_comp_anc]
    _ = R ⨾ (anc R ⨾ R) := rp_assoc _ _ _
    _ = R ⨾ po R := by rw [← po_eq_anc_comp]

/-- ✱91·511. \(\vdash.R_{\text{po}}\mid R\unicode{x2abd}R_{\text{po}} \quad[\text{*43·421.*91·283.*41·161}]\) -/
theorem pm91_511 {R : α → α → Prop} : po R ⨾ R ⪽ po R := by
  rintro x z ⟨y, h1, h2⟩
  exact po_trans h1 (R_sub_po h2)

/-- ✱91·512. \(\vdash.R_{\text{po}}\unicode{x2abd}R_{\unicode{x2217}}\mid R\) -/
theorem pm91_512 {R : α → α → Prop} : po R ⪽ anc R ⨾ R := by
  rw [← po_eq_anc_comp]
  exact fun _ _ h => h

/-- ✱91·513. \(\vdash.R_{\unicode{x2217}}\unicode{x2abd}\dot{s}ʻ\text{Potid}ʻR\) -/
theorem pm91_513 {R : α → α → Prop} : anc R ⪽ sumRel (potid R) := by
  intro x y h
  obtain ⟨n, hn⟩ := anc_iff_ipow.1 h
  exact ⟨ipow R n, ipow_mem_potid R n, hn⟩

/-- ✱91·514. \(\vdash.R_{\unicode{x2217}}\mid R\unicode{x2abd}R_{\text{po}}\) -/
theorem pm91_514 {R : α → α → Prop} : anc R ⨾ R ⪽ po R := by
  rw [← po_eq_anc_comp]
  exact fun _ _ h => h

/-- ✱91·52. \(\vdash.R_{\text{po}}=R_{\unicode{x2217}}\mid R=R\mid R_{\unicode{x2217}} \quad[\text{*91·512·514.*90·32}]\) -/
theorem pm91_52 {R : α → α → Prop} : po R = anc R ⨾ R ∧ anc R ⨾ R = R ⨾ anc R :=
  ⟨po_eq_anc_comp R, (po_eq_anc_comp R).symm.trans (po_eq_comp_anc R)⟩

/-- ✱91·521. \(\vdash : P \in \text{Potid}ʻR. \equiv . \breve{P} \in \text{Potid}ʻ\breve{R}\) -/
theorem pm91_521 {R P : α → α → Prop} : P ∈ potid R ↔ P˘ ∈ potid R˘ := by
  rw [mem_potid', mem_potid']
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, cnv_ipow R n⟩
  · rintro ⟨n, h⟩
    have h' := congrArg cnv h
    rw [cnv_ipow] at h'
    exact ⟨n, h'⟩

/-- ✱91·522. \(\vdash: P \in \text{Pot}ʻR .\equiv. \breve{P} \in \text{Pot}ʻ\breve{R} \quad[\text{Proof as in *91·521}]\) -/
theorem pm91_522 {R P : α → α → Prop} : P ∈ pot R ↔ P˘ ∈ pot R˘ := by
  rw [mem_pot', mem_pot']
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, cnv_ipow R _⟩
  · rintro ⟨n, h⟩
    have h' := congrArg cnv h
    rw [cnv_ipow] at h'
    exact ⟨n, h'⟩

/-- ✱91·53. \(\vdash. \breve{R}_{\text{po}} = (\breve{R})_{\text{po}}\) -/
theorem pm91_53 {R : α → α → Prop} : (po R)˘ = po R˘ := by
  funext x y
  apply propext
  show po R y x ↔ po R˘ x y
  rw [po_iff_npow, po_iff_npow]
  exact exists_congr fun n => by rw [← cnv_npow]; exact Iff.rfl

/-- ✱91·54. \(\vdash . R_{\unicode{x2217}} = I \upharpoonright CʻR \unicode{x228d} R_{\text{po}} \quad[\text{*90·31.*91·52}]\) -/
theorem pm91_54 {R : α → α → Prop} : anc R = I ↾ fld R ⊍ po R := anc_eq_idf_po R

/-- ✱91·541. \(\vdash . R_{\unicode{x2217}}\dot{\cap}J=R_{\text{po}}\dot{\cap}J \quad[\text{*25·401.(*50·02).*35·441. *91·54}]\) -/
theorem pm91_541 {R : α → α → Prop} : anc R ⩀ J = po R ⩀ J := by
  funext x y
  apply propext
  show anc R x y ∧ x ≠ y ↔ po R x y ∧ x ≠ y
  rw [anc_iff_po]
  constructor
  · rintro ⟨⟨rfl, -⟩ | h, hne⟩
    · exact absurd rfl hne
    · exact ⟨h, hne⟩
  · rintro ⟨h, hne⟩
    exact ⟨Or.inr h, hne⟩

/-- ✱91·542. \(\vdash : xR_{\unicode{x2217}}y.x \neq y.\equiv. xR_{\text{po}}y.x \neq y \quad[\text{*91·541 .*50·11}]\) -/
theorem pm91_542 {R : α → α → Prop} {x y : α} : anc R x y ∧ x ≠ y ↔ po R x y ∧ x ≠ y := by
  have h := congrFun (congrFun (pm91_541 (R := R)) x) y
  exact Eq.to_iff h

/-- ✱91·543. \(\vdash . R_{\unicode{x2217}}ʻʻ\beta = (\beta \cap CʻR) \cup R_{\text{po}}ʻʻ\beta\) -/
theorem pm91_543 {R : α → α → Prop} {B : Set α} : anc R ʻʻ B = (B ∩ fld R) ∪ po R ʻʻ B :=
  anc_img_eq R B

/-- ✱91·544. \(\vdash . \breve{R}_{\unicode{x2217}}ʻʻ\beta = (\beta \cap CʻR) \cup \breve{R}_{\text{po}}ʻʻ\beta\) -/
theorem pm91_544 {R : α → α → Prop} {B : Set α} :
    ancCnv R ʻʻ B = (B ∩ fld R) ∪ (po R)˘ ʻʻ B := by
  rw [← pm90_132, pm91_53, ← fld_cnv R]
  exact anc_img_eq R˘ B

/-- ✱91·545. \(\vdash : \beta \subset CʻR.\supset. R_{\unicode{x2217}}ʻʻ\beta = \beta \cup R_{\text{po}}ʻʻ\beta \quad[\text{*91·543.*22·621}]\) -/
theorem pm91_545 {R : α → α → Prop} {B : Set α} :
    B ⊆ fld R → anc R ʻʻ B = B ∪ po R ʻʻ B := by
  intro h
  rw [pm91_543, Set.inter_eq_left.2 h]

/-- ✱91·546. \(\vdash : \beta \subset CʻR. \supset . \breve{R}_{\unicode{x2217}}ʻʻ\beta = \beta \cup \breve{R}_{\text{po}}ʻʻ\beta\) -/
theorem pm91_546 {R : α → α → Prop} {B : Set α} :
    B ⊆ fld R → ancCnv R ʻʻ B = B ∪ (po R)˘ ʻʻ B := by
  intro h
  rw [pm91_544, Set.inter_eq_left.2 h]

/-- ✱91·55. \(\vdash.R_{\unicode{x2217}}=\dot{s}ʻ\text{Potid}ʻR\) -/
theorem pm91_55 {R : α → α → Prop} : anc R = sumRel (potid R) := by
  funext x y
  apply propext
  constructor
  · exact pm91_513 x y
  · rintro ⟨P, hP, h⟩
    obtain ⟨n, rfl⟩ := mem_potid'.1 hP
    exact anc_iff_ipow.2 ⟨n, h⟩

/-- ✱91·56. \(\vdash.R_{\text{po}}^{2}\unicode{x2abd}R_{\text{po}}\) -/
theorem pm91_56 {R : α → α → Prop} : rsq (po R) ⪽ po R := by
  rintro x z ⟨y, h1, h2⟩
  exact po_trans h1 h2

/-- ✱91·561. \(\vdash\colon\ldotp S\unicode{x2abd}R_{\text{po}}.T\unicode{x2abd}R_{\text{po}}.\supset.S\mid T\unicode{x2abd}R_{\text{po}} \quad[\text{*34·34.*91·56}]\) -/
theorem pm91_561 {R S T : α → α → Prop} : S ⪽ po R ∧ T ⪽ po R → S ⨾ T ⪽ po R := by
  rintro ⟨hS, hT⟩ x z ⟨y, h1, h2⟩
  exact po_trans (hS _ _ h1) (hT _ _ h2)

/-- ✱91·562. \(\vdash:S\unicode{x2abd}R_{\text{po}}.\supset.S\mid R\unicode{x2abd}R_{\text{po}}.R\mid S\unicode{x2abd}R_{\text{po}} \quad[\text{*91·561·502}]\) -/
theorem pm91_562 {R S : α → α → Prop} : S ⪽ po R → S ⨾ R ⪽ po R ∧ R ⨾ S ⪽ po R := fun h =>
  ⟨pm91_561 ⟨h, pm91_502⟩, pm91_561 ⟨pm91_502, h⟩⟩

/-- ✱91·57. \(\vdash.R_{\text{po}}=R\unicode{x228d}R_{\text{po}}\mid R=R\unicode{x228d}R\mid R_{\text{po}} \quad[\text{*90·32.*91·52}]\) -/
theorem pm91_57 {R : α → α → Prop} : po R = R ⊍ po R ⨾ R ∧ R ⊍ po R ⨾ R = R ⊍ R ⨾ po R :=
  ⟨po_eq_or_tail R, by rw [pm91_51]⟩

/-- ✱91·571. \(\vdash.R_{\text{po}}\mid R=R\mid R_{\text{po}} \quad[\text{*91·52}]\) -/
theorem pm91_571 {R : α → α → Prop} : po R ⨾ R = R ⨾ po R := pm91_51

/-- ✱91·572. \(\vdash.R_{\text{po}}\dot{-}(R_{\text{po}}\mid R)\unicode{x2abd}R \quad[\text{*91·57.*22·9·43}]\) -/
theorem pm91_572 {R : α → α → Prop} : po R ∸ (po R ⨾ R) ⪽ R := by
  rintro x y ⟨h, hn⟩
  rw [po_eq_or_tail] at h
  rcases h with h | h
  · exact h
  · exact absurd h hn

/-- ✱91·573. \(\vdash.R_{\text{po}}\dot{-}(R\mid R_{\text{po}})\unicode{x2abd}R \quad[\text{*91·571·572}]\) -/
theorem pm91_573 {R : α → α → Prop} : po R ∸ (R ⨾ po R) ⪽ R := by
  rw [← pm91_51]
  exact pm91_572

/-- ✱91·574. \(\vdash.R_{\unicode{x2217}}\mid R_{\text{po}}=R_{\text{po}}\mid R_{\unicode{x2217}}=R_{\text{po}}=R\mid R_{\unicode{x2217}}=R_{\unicode{x2217}}\mid R\) -/
theorem pm91_574 {R : α → α → Prop} :
    ((anc R ⨾ po R = po R ⨾ anc R ∧ po R ⨾ anc R = po R) ∧ po R = R ⨾ anc R) ∧
      R ⨾ anc R = anc R ⨾ R := by
  rw [anc_comp_po, po_comp_anc, ← po_eq_comp_anc, ← po_eq_anc_comp]
  exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩

/-- ✱91·575. \(\vdash.R_{\text{po}}^{2}=R\mid R_{\text{po}}=R_{\text{po}}\mid R=R^{2}\mid R_{\unicode{x2217}}=R_{\unicode{x2217}}\mid R^{2}=R\mid R_{\unicode{x2217}}\mid R\) -/
theorem pm91_575 {R : α → α → Prop} :
    (((rsq (po R) = R ⨾ po R ∧ R ⨾ po R = po R ⨾ R) ∧ po R ⨾ R = rsq R ⨾ anc R) ∧
      rsq R ⨾ anc R = anc R ⨾ rsq R) ∧ anc R ⨾ rsq R = R ⨾ anc R ⨾ R := by
  have h1 : rsq (po R) = R ⨾ po R := by
    show po R ⨾ po R = R ⨾ po R
    conv_lhs => rw [po_eq_comp_anc R]
    rw [rp_assoc, ← po_eq_comp_anc R, anc_comp_po]
  have h2 : rsq R ⨾ anc R = R ⨾ po R := by
    show R ⨾ R ⨾ anc R = R ⨾ po R
    rw [rp_assoc, ← po_eq_comp_anc]
  have h3 : anc R ⨾ rsq R = po R ⨾ R := by
    show anc R ⨾ (R ⨾ R) = po R ⨾ R
    rw [← rp_assoc, ← po_eq_anc_comp]
  have h4 : R ⨾ anc R ⨾ R = po R ⨾ R := by
    rw [← po_eq_comp_anc]
  rw [h1, h2, h3, h4, pm91_51]
  exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- ✱91·58. \(\vdash:P\in \text{Potid}ʻR.\supset.P\unicode{x2abd}R_{\unicode{x2217}} \quad[\text{*91·55.*41·13}]\) -/
theorem pm91_58 {R P : α → α → Prop} : P ∈ potid R → P ⪽ anc R := by
  intro hP x y h
  obtain ⟨n, rfl⟩ := mem_potid'.1 hP
  exact anc_iff_ipow.2 ⟨n, h⟩

/-- ✱91·581. \(\vdash:P\in \text{Pot}ʻR.\supset.P\unicode{x2abd}R_{\text{po}} \quad[\text{*41·13.(*91·05)}]\) -/
theorem pm91_581 {R P : α → α → Prop} : P ∈ pot R → P ⪽ po R := by
  intro hP x y h
  obtain ⟨n, rfl⟩ := mem_pot'.1 hP
  exact po_iff_ipow.2 ⟨n, h⟩

/-- ✱91·59. \(\vdash:R\unicode{x2abd}S.\supset.R_{\text{po}}\unicode{x2abd}S_{\text{po}}\) -/
theorem pm91_59 {R S : α → α → Prop} : R ⪽ S → po R ⪽ po S := by
  intro hRS x y h
  rw [po_iff_transGen] at *
  induction h with
  | single h => exact TransGen.single (hRS _ _ h)
  | tail _ hbc ih => exact TransGen.tail ih (hRS _ _ hbc)

/-- ✱91·6. \(\vdash:Q\in \text{Pot}ʻR.\supset.\text{Pot}ʻQ\subset \text{Pot}ʻR.Q_{\text{po}}\unicode{x2abd}R_{\text{po}}\) -/
theorem pm91_6 {R Q : α → α → Prop} : Q ∈ pot R → pot Q ⊆ pot R ∧ po Q ⪽ po R := by
  intro hQ
  obtain ⟨k, rfl⟩ := mem_pot'.1 hQ
  have key : ∀ j, ipow (ipow R (k + 1)) (j + 1) = ipow R ((k * (j + 1) + j) + 1) := by
    intro j
    rw [ipow_succ_eq, ipow_succ_eq, ipow_succ_eq, npow_mul]
    congr 1
    rw [Nat.succ_mul, Nat.add_assoc]
  refine ⟨?_, ?_⟩
  · intro P hP
    obtain ⟨j, rfl⟩ := mem_pot'.1 hP
    rw [key]
    exact ipow_succ_mem_pot R _
  · intro x y h
    obtain ⟨j, hj⟩ := po_iff_ipow.1 h
    rw [key] at hj
    exact po_iff_ipow.2 ⟨_, hj⟩

/-- ✱91·601. \(\vdash.(R_{\text{po}})_{\text{po}}=R_{\text{po}}\) -/
theorem pm91_601 {R : α → α → Prop} : po (po R) = po R := by
  funext x y
  apply propext
  constructor
  · intro h
    rw [po_iff_transGen] at h
    induction h with
    | single h => exact h
    | tail _ hbc ih => exact po_trans ih hbc
  · intro h
    exact R_sub_po h

/-- ✱91·602. \(\vdash.(R_{\text{po}})_{\unicode{x2217}}=R_{\unicode{x2217}}\) -/
theorem pm91_602 {R : α → α → Prop} : anc (po R) = anc R := by
  funext x y
  apply propext
  rw [anc_iff_reflTransGen (R := po R), pm91_504.2]
  constructor
  · rintro ⟨hx, h⟩
    induction h with
    | refl => exact anc_refl hx
    | tail _ hbc ih => exact anc_trans ih (po_sub_anc hbc)
  · intro h
    rcases anc_iff_po.1 h with ⟨rfl, hx⟩ | h
    · exact ⟨hx, ReflTransGen.refl⟩
    · obtain ⟨n, hn⟩ := po_iff_npow.1 h
      exact ⟨(fld_of_npow_succ hn).1, ReflTransGen.single h⟩

/-- ✱91·603. \(\vdash.(R_{\unicode{x2217}})_{\text{po}}=R_{\unicode{x2217}}\) -/
theorem pm91_603 {R : α → α → Prop} : po (anc R) = anc R := by
  funext x y
  apply propext
  constructor
  · intro h
    rw [po_iff_transGen] at h
    induction h with
    | single h => exact h
    | tail _ hbc ih => exact anc_trans ih hbc
  · intro h
    exact R_sub_po h

/-- ✱91·62. \(\vdash\colon\ldotp xR_{\text{po}}y.\equiv:\breve{R}ʻʻ\mu\subset \mu.\overleftarrow{R}ʻx\subset \mu.\supset_{\mu}.y\in \mu \quad[\text{*91·52.*90·36}]\) -/
theorem pm91_62 {R : α → α → Prop} {x y : α} :
    po R x y ↔ ∀ M : Set α, R˘ ʻʻ M ⊆ M ∧ rels R x ⊆ M → y ∈ M := by
  rw [po_eq_comp_anc]
  exact pm90_36

/-- ✱91·7. \(\vdash.R_{\text{po}}ʻʻ\text{ᗡ}ʻR=\text{D}ʻR.\breve{R}_{\text{po}}ʻʻ\text{D}ʻR=\text{ᗡ}ʻR \quad[\text{*91·504.*37·25}]\) -/
theorem pm91_7 {R : α → α → Prop} : po R ʻʻ codom R = dom R ∧ (po R)˘ ʻʻ dom R = codom R := by
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, -, h⟩
      exact pm91_504.1.1 ▸ (⟨y, h⟩ : x ∈ dom (po R))
    · rintro ⟨y, h⟩
      exact ⟨y, ⟨x, h⟩, R_sub_po h⟩
  · ext y
    constructor
    · rintro ⟨x, -, h⟩
      exact pm91_504.1.2 ▸ (⟨x, h⟩ : y ∈ codom (po R))
    · rintro ⟨x, h⟩
      exact ⟨x, ⟨y, h⟩, R_sub_po h⟩

/-- ✱91·71. \(\vdash:Rʻʻ\mu\subset \mu.\equiv.R_{\text{po}}ʻʻ\mu\subset \mu.\equiv.R_{\unicode{x2217}}ʻʻ\mu\subset \mu\) -/
theorem pm91_71 {R : α → α → Prop} {M : Set α} :
    (R ʻʻ M ⊆ M ↔ po R ʻʻ M ⊆ M) ∧ (po R ʻʻ M ⊆ M ↔ anc R ʻʻ M ⊆ M) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro h x ⟨y, hy, hxy⟩
    obtain ⟨n, hn⟩ := po_iff_npow.1 hxy
    exact mem_of_npow h hn hy
  · rintro h x ⟨y, hy, hxy⟩
    exact h ⟨y, hy, R_sub_po hxy⟩
  · rw [anc_img_eq, Set.union_subset_iff]
    exact ⟨fun h => ⟨Set.inter_subset_left, h⟩, fun h => h.2⟩

/-- ✱91·711. \(\vdash:Rʻʻ\mu\subset \mu.\supset.R_{\text{po}}ʻʻ\mu=Rʻʻ\mu\) -/
theorem pm91_711 {R : α → α → Prop} {M : Set α} : R ʻʻ M ⊆ M → po R ʻʻ M = R ʻʻ M := by
  intro hM
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [po_eq_comp_anc] at hxy
    obtain ⟨a, hxa, ha⟩ := hxy
    obtain ⟨-, n, hn⟩ := anc_iff_npow.1 ha
    exact ⟨a, mem_of_npow hM hn hy, hxa⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, R_sub_po hxy⟩

/-- ✱91·72. \(\vdash.Rʻʻ(\alpha\cup R_{\text{po}}ʻʻ\alpha)=R_{\text{po}}ʻʻ\alpha\) -/
theorem pm91_72 {R : α → α → Prop} {A : Set α} : R ʻʻ (A ∪ po R ʻʻ A) = po R ʻʻ A := by
  ext x
  constructor
  · rintro ⟨z, hz | ⟨a, ha, hza⟩, hxz⟩
    · exact ⟨z, hz, R_sub_po hxz⟩
    · exact ⟨a, ha, po_trans (R_sub_po hxz) hza⟩
  · rintro ⟨y, hy, hxy⟩
    rw [po_eq_or_head] at hxy
    rcases hxy with h | ⟨z, hxz, hzy⟩
    · exact ⟨y, Or.inl hy, h⟩
    · exact ⟨z, Or.inr ⟨y, hy, hzy⟩, hxz⟩

/-- ✱91·721. \(\vdash.\breve{R}ʻʻ(\alpha\cup \breve{R}_{\text{po}}ʻʻ\alpha)=\breve{R}_{\text{po}}ʻʻ\alpha \quad\left[\text{*91·72}\, \frac{\breve{R}}{R}.\text{*91·53}\right]\) -/
theorem pm91_721 {R : α → α → Prop} {A : Set α} :
    R˘ ʻʻ (A ∪ (po R)˘ ʻʻ A) = (po R)˘ ʻʻ A := by
  rw [pm91_53]
  exact pm91_72

/-- ✱91·73. \(\vdash\colon\ldotp P,\,Q\in \text{Potid}ʻR.P \neq Q.\supset:(\exists T):T\in \text{Pot}ʻR:Q=P\mid T.\lor.P=Q\mid T\) -/
theorem pm91_73 {R P Q : α → α → Prop} :
    Mem2 P Q (potid R) ∧ P ≠ Q → ∃ T, T ∈ pot R ∧ (Q = P ⨾ T ∨ P = Q ⨾ T) := by
  rintro ⟨⟨hP, hQ⟩, hne⟩
  obtain ⟨m, rfl⟩ := mem_potid'.1 hP
  obtain ⟨n, rfl⟩ := mem_potid'.1 hQ
  rcases Nat.lt_or_ge m n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    exact ⟨ipow R (k + 1), ipow_succ_mem_pot R k, Or.inl (by rw [ipow_mul, Nat.add_assoc])⟩
  · rcases Nat.eq_or_lt_of_le h with h | h
    · exact absurd (by rw [h]) hne
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
      exact ⟨ipow R (k + 1), ipow_succ_mem_pot R k, Or.inr (by rw [ipow_mul, Nat.add_assoc])⟩

/-- ✱91·731. \[\begin{align}&\vdash\colon\ldotp P,\,Q\in \text{Potid}ʻR.P \neq Q.\supset:(\exists T):T\in \text{Pot}ʻR:Q=T\mid P.\lor.P=T\mid Q\\ &[\text{*91·73·34}]\end{align}\] -/
theorem pm91_731 {R P Q : α → α → Prop} :
    Mem2 P Q (potid R) ∧ P ≠ Q → ∃ T, T ∈ pot R ∧ (Q = T ⨾ P ∨ P = T ⨾ Q) := by
  intro h
  obtain ⟨T, hT, h'⟩ := pm91_73 h
  refine ⟨T, hT, ?_⟩
  rw [pm91_34 ⟨pot_sub_potid R hT, h.1.1⟩, pm91_34 ⟨pot_sub_potid R hT, h.1.2⟩]
  exact h'

/-- ✱91·732. \[\begin{align}\vdash\colon\ldotp P,Q\in \text{Potid}ʻR.&P \neq Q.\supset:\\ &(\exists S):S\in \text{Potid}ʻR:Q = S\mid R\mid P.\lor.P = S\mid R\mid Q\end{align}\] -/
theorem pm91_732 {R P Q : α → α → Prop} :
    Mem2 P Q (potid R) ∧ P ≠ Q → ∃ S, S ∈ potid R ∧ (Q = S ⨾ R ⨾ P ∨ P = S ⨾ R ⨾ Q) := by
  rintro ⟨⟨hP, hQ⟩, hne⟩
  obtain ⟨m, rfl⟩ := mem_potid'.1 hP
  obtain ⟨n, rfl⟩ := mem_potid'.1 hQ
  rcases Nat.lt_or_ge m n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    refine ⟨ipow R k, ipow_mem_potid R k, Or.inl ?_⟩
    rw [← ipow_succ, ipow_mul]
    congr 1
    omega
  · rcases Nat.eq_or_lt_of_le h with h | h
    · exact absurd (by rw [h]) hne
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
      refine ⟨ipow R k, ipow_mem_potid R k, Or.inr ?_⟩
      rw [← ipow_succ, ipow_mul]
      congr 1
      omega

/-- ✱91·74. \(\vdash.\breve{R}ʻʻ\overleftarrow{R}_{\unicode{x2217}}ʻx = \overleftarrow{R}_{\text{po}}ʻx.Rʻʻ\overrightarrow{R}_{\unicode{x2217}}ʻx = \overrightarrow{R}_{\text{po}}ʻx \quad[\text{*91·52.*37·302}]\) -/
theorem pm91_74 {R : α → α → Prop} {x : α} :
    R˘ ʻʻ rels (anc R) x = rels (po R) x ∧ R ʻʻ refs (anc R) x = refs (po R) x := by
  refine ⟨?_, ?_⟩
  · ext z
    rw [po_eq_anc_comp]
    exact ⟨fun ⟨y, hy, hyz⟩ => ⟨y, hy, hyz⟩, fun ⟨y, hy, hyz⟩ => ⟨y, hy, hyz⟩⟩
  · ext z
    rw [po_eq_comp_anc]
    exact ⟨fun ⟨y, hy, hzy⟩ => ⟨y, hzy, hy⟩, fun ⟨y, hzy, hy⟩ => ⟨y, hy, hzy⟩⟩

/-- ✱91·75. \(\vdash.R_{\unicode{x2217}}\unicode{x228d}\breve{R}_{\unicode{x2217}} = R_{\unicode{x2217}}\unicode{x228d}\breve{R}_{\text{po}} = R_{\text{po}}\unicode{x228d}\breve{R}_{\unicode{x2217}} = R_{\text{po}}\unicode{x228d}I\upharpoonright CʻR\unicode{x228d}\breve{R}_{\text{po}}\) -/
theorem pm91_75 {R : α → α → Prop} :
    (anc R ⊍ ancCnv R = anc R ⊍ (po R)˘ ∧ anc R ⊍ (po R)˘ = po R ⊍ ancCnv R) ∧
      po R ⊍ ancCnv R = po R ⊍ I ↾ fld R ⊍ (po R)˘ := by
  have K : ∀ X : α → α → Prop,
      (∀ x y, X x y ↔ (x = y ∧ x ∈ fld R) ∨ po R x y ∨ po R y x) →
        X = fun x y => (x = y ∧ x ∈ fld R) ∨ po R x y ∨ po R y x :=
    fun X h => funext fun x => funext fun y => propext (h x y)
  have e1 := K (anc R ⊍ ancCnv R) (by
    intro x y
    show anc R x y ∨ anc R y x ↔ _
    rw [anc_iff_po, anc_iff_po]
    constructor
    · rintro ((⟨rfl, h⟩ | h) | (⟨rfl, h⟩ | h))
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr (Or.inr h)
    · rintro (⟨rfl, h⟩ | h | h)
      · exact Or.inl (Or.inl ⟨rfl, h⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h))
  have e2 := K (anc R ⊍ (po R)˘) (by
    intro x y
    show anc R x y ∨ po R y x ↔ _
    rw [anc_iff_po]
    tauto)
  have e3 := K (po R ⊍ ancCnv R) (by
    intro x y
    show po R x y ∨ anc R y x ↔ _
    rw [anc_iff_po]
    constructor
    · rintro (h | ⟨rfl, h⟩ | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr (Or.inr h)
    · rintro (⟨rfl, h⟩ | h | h)
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inr h))
  have e4 := K (po R ⊍ I ↾ fld R ⊍ (po R)˘) (by
    intro x y
    show (po R x y ∨ (x = y ∧ y ∈ fld R)) ∨ po R y x ↔ _
    constructor
    · rintro ((h | ⟨rfl, h⟩) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr (Or.inr h)
    · rintro (⟨rfl, h⟩ | h | h)
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h)
  rw [e1, e2, e3, e4]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

/-!
## [✱92] Powers of one-many and many-one relations

*(Vol. 1, p. 601)*

> *Summary of* *92.
>
> If \(R \in \text{Cls} \rightarrow 1\), it follows that, starting from a given term \(x\), there is only one series of terms \(x_{1}, x_{2}, x_{3}, \ldots\) such that \[ x R x_{1} . x_{1} R x_{2} . x_{2} R x_{3} . \ldots \text{.} \]
>
> Thus for example the relation of son to father is a \(\text{Cls}\rightarrow 1\); and starting from a given man, the series of ancestors in the direct male line (which is the above series \(x_{1}\), \(x_{2}\), \(x_{3}\),...) is unique and determinate. A result of this property of many-one relations is that if, starting from a term \(y\), we go backwards a certain number of steps to a term \(x\), and then forward a greater number of steps to a term \(z\), we must pass through \(y\) in going from \(x\) to \(z\); while if the number of steps from \(x\) to \(z\) is less than that from \(x\) to \(y\), \(z\) must lie on the road from \(x\) to \(y\). These facts are expressed by the proposition: \[ R \in \text{Cls} \rightarrow 1 .\supset. \breve{R}_{\unicode{x2217}} \mid R_{\unicode{x2217}} \unicode{x2abd} R_{\unicode{x2217}} \unicode{x228d} \breve{R}_{\unicode{x2217}}\text{.} \]
>
> …

**Lean reading.** `1 → Cls`, `Cls → 1`, `1 → 1` are `arrow one Cls`, `arrow Cls one`,
`arrow one one` (✱70·01; `mem_arrow_one_Cls` etc. give the usual characterizations), and
`Potid'R ⊂ 1 → Cls` is `potid R ⊆ arrow one Cls`. `R_*`, `R̆_*`, `R_po`, `Pot'R`, `Potid'R` are
read as in ✱90–✱91; `T ↾ D'Q` is `T ↾ dom Q`, `(ᗡ'Q) ↿ T` is `codom Q ◁ T`, `Cnv'(T ↾ D'P)` is
`(T ↾ dom P)˘`. Hypotheses that are products (`R ∈ 1 → Cls . ᗡ'R ⊂ D'R . Q, T ∈ Potid'R`) are
conjunctions bracketed to the left, and `P, Q ∈ Potid'R` is `Mem2 P Q (potid R)`. The e-text's
✱92·191 has the hypothesis `P|Q ∈ Potid'R` where PM means `P, Q ∈ Potid'R` (see its docstring).

**Status.** proved (all propositions; ✱92·191 proved (reading), see its docstring).
-/

/-- ✱92·1. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.\text{Potid}ʻR\subset 1\rightarrow \text{Cls}\) -/
theorem pm92_1 {R : α → α → Prop} : R ∈ arrow one Cls → potid R ⊆ arrow one Cls := by
  intro hR P hP
  obtain ⟨n, rfl⟩ := mem_potid'.1 hP
  exact ipow_oneMany hR n

/-- ✱92·101. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\text{Potid}ʻR\subset \text{Cls}\rightarrow 1 \quad[\text{Proof as in *92·1}]\) -/
theorem pm92_101 {R : α → α → Prop} : R ∈ arrow Cls one → potid R ⊆ arrow Cls one := by
  intro hR P hP
  obtain ⟨n, rfl⟩ := mem_potid'.1 hP
  exact ipow_manyOne hR n

/-- ✱92·102. \(\vdash:R\in 1\rightarrow 1.\supset.\text{Potid}ʻR\subset 1\rightarrow 1 \quad[\text{Proof as in *92·1}]\) -/
theorem pm92_102 {R : α → α → Prop} : R ∈ arrow one one → potid R ⊆ arrow one one := by
  intro hR P hP
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
  exact mem_arrow_one_one.2 ⟨mem_arrow_one_Cls.1 (pm92_1 (mem_arrow_one_Cls.2 h1) hP),
    mem_arrow_Cls_one.1 (pm92_101 (mem_arrow_Cls_one.2 h2) hP)⟩

/-- ✱92·11. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.R_{\text{po}}\mid \breve{R}\unicode{x2abd}R_{\unicode{x2217}}.R_{\text{po}}\mid \breve{R} = R_{\unicode{x2217}}\upharpoonright \text{D}ʻR\) -/
theorem pm92_11 {R : α → α → Prop} :
    R ∈ arrow one Cls → po R ⨾ R˘ ⪽ anc R ∧ po R ⨾ R˘ = anc R ↾ dom R := by
  intro hR
  rw [mem_arrow_one_Cls] at hR
  have e : po R ⨾ R˘ = anc R ↾ dom R := by
    rw [po_eq_anc_comp, comp_comp_cnv hR]
  exact ⟨fun x y h => (e ▸ h : (anc R ↾ dom R) x y).1, e⟩

/-- ✱92·111. \[\begin{align}&\vdash:R\in \text{Cls}\rightarrow 1.\supset.\breve{R}\mid R_{\text{po}}\unicode{x2abd}R_{\unicode{x2217}}.\breve{R}\mid R_{\text{po}} = (\text{ᗡ}ʻR)\upharpoonleft R_{\unicode{x2217}}\\ &[\text{Proof as in *92·11}]\end{align}\] -/
theorem pm92_111 {R : α → α → Prop} :
    R ∈ arrow Cls one → R˘ ⨾ po R ⪽ anc R ∧ R˘ ⨾ po R = codom R ◁ anc R := by
  intro hR
  rw [mem_arrow_Cls_one] at hR
  have e : R˘ ⨾ po R = codom R ◁ anc R := by
    rw [po_eq_comp_anc, ← rp_assoc, cnv_comp_comp hR]
  exact ⟨fun x y h => (e ▸ h : (codom R ◁ anc R) x y).2, e⟩

/-- ✱92·112. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.R\mid R_{\text{po}}\mid \breve{R} = R_{\text{po}}\upharpoonright \text{D}ʻR \quad[\text{*92·11.*91·52}]\) -/
theorem pm92_112 {R : α → α → Prop} : R ∈ arrow one Cls → R ⨾ po R ⨾ R˘ = po R ↾ dom R := by
  intro hR
  rw [rp_assoc, (pm92_11 hR).2, comp_cres, ← po_eq_comp_anc]

/-- ✱92·113. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\breve{R}\mid R_{\text{po}}\mid R = (\text{ᗡ}ʻR)\upharpoonleft R_{\text{po}} \quad[\text{*92·111.*91·52}]\) -/
theorem pm92_113 {R : α → α → Prop} : R ∈ arrow Cls one → R˘ ⨾ po R ⨾ R = codom R ◁ po R := by
  intro hR
  rw [(pm92_111 hR).2, dres_comp, ← po_eq_anc_comp]

/-- ✱92·12. \(\vdash:R\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻR\subset \text{D}ʻR.\supset.R_{\text{po}}\mid \breve{R} = R_{\unicode{x2217}} \quad[\text{*92·11.*35·66}]\) -/
theorem pm92_12 {R : α → α → Prop} :
    R ∈ arrow one Cls ∧ codom R ⊆ dom R → po R ⨾ R˘ = anc R := by
  rintro ⟨hR, h⟩
  rw [(pm92_11 hR).2]
  exact cres_eq_self fun y ⟨x, hxy⟩ => fld_sub_dom h (anc_fld_right hxy)

/-- ✱92·121. \(\vdash:R\in \text{Cls}\rightarrow 1.\text{D}ʻR\subset \text{ᗡ}ʻR.\supset.\breve{R}\mid R_{\text{po}} = R_{\unicode{x2217}} \quad[\text{*92·111.*35·63}]\) -/
theorem pm92_121 {R : α → α → Prop} :
    R ∈ arrow Cls one ∧ dom R ⊆ codom R → R˘ ⨾ po R = anc R := by
  rintro ⟨hR, h⟩
  rw [(pm92_111 hR).2]
  refine dres_eq_self fun x ⟨y, hxy⟩ => ?_
  have hx : x ∈ fld R˘ := (fld_cnv R).symm ▸ hxy.1
  exact fld_sub_dom (R := R˘) h hx

/-- ✱92·13. \(\vdash:R\in 1\rightarrow \text{Cls}.Q,\,T\in \text{Potid}ʻR.\supset.T\mid Q\mid \breve{Q} = T\upharpoonright \text{D}ʻQ\) -/
theorem pm92_13 {R Q T : α → α → Prop} :
    R ∈ arrow one Cls ∧ Mem2 Q T (potid R) → T ⨾ Q ⨾ Q˘ = T ↾ dom Q := by
  rintro ⟨hR, hQ, -⟩
  exact comp_comp_cnv (mem_arrow_one_Cls.1 (pm92_1 hR hQ)) T

/-- ✱92·131. \(\vdash:R\in \text{Cls}\rightarrow 1.Q,\,T\in \text{Potid}ʻR.\supset.\breve{Q}\mid Q\mid T= (\text{ᗡ}ʻQ)\upharpoonleft T\) -/
theorem pm92_131 {R Q T : α → α → Prop} :
    R ∈ arrow Cls one ∧ Mem2 Q T (potid R) → Q˘ ⨾ Q ⨾ T = codom Q ◁ T := by
  rintro ⟨hR, hQ, -⟩
  exact cnv_comp_comp (mem_arrow_Cls_one.1 (pm92_101 hR hQ)) T

/-- ✱92·132. \(\vdash:R\in 1\rightarrow \text{Cls}.Q,\,T\in \text{Potid}ʻR.\supset.Q\mid T\mid \breve{Q}\unicode{x2abd}T \quad[\text{*92·13.*91·34}]\) -/
theorem pm92_132 {R Q T : α → α → Prop} :
    R ∈ arrow one Cls ∧ Mem2 Q T (potid R) → Q ⨾ T ⨾ Q˘ ⪽ T := by
  intro h
  rw [pm91_34 h.2, pm92_13 h]
  exact fun _ _ h' => h'.1

/-- ✱92·133. \(\vdash:R\in \text{Cls}\rightarrow 1.Q,\,T\in \text{Potid}ʻR.\supset.\breve{Q}\mid T\mid Q\unicode{x2abd}T\) -/
theorem pm92_133 {R Q T : α → α → Prop} :
    R ∈ arrow Cls one ∧ Mem2 Q T (potid R) → Q˘ ⨾ T ⨾ Q ⪽ T := by
  intro h
  rw [rp_assoc, ← pm91_34 h.2, ← rp_assoc, pm92_131 h]
  exact fun _ _ h' => h'.2

/-- ✱92·14. \(\vdash:\text{ᗡ}ʻR\subset \text{D}ʻR.Q\in \text{Pot}ʻR.\supset.\text{D}ʻQ=\text{D}ʻR\) -/
theorem pm92_14 {R Q : α → α → Prop} : codom R ⊆ dom R ∧ Q ∈ pot R → dom Q = dom R := by
  rintro ⟨h, hQ⟩
  obtain ⟨n, rfl⟩ := mem_pot'.1 hQ
  exact dom_ipow h _

/-- ✱92·141. \(\vdash:\text{D}ʻR\subset \text{ᗡ}ʻR.Q\in \text{Pot}ʻR.\supset.\text{ᗡ}ʻQ=\text{ᗡ}ʻR\) -/
theorem pm92_141 {R Q : α → α → Prop} : dom R ⊆ codom R ∧ Q ∈ pot R → codom Q = codom R :=
  fun ⟨h, hQ⟩ => pm92_14 (R := R˘) (Q := Q˘) ⟨h, pm91_522.1 hQ⟩

/-- ✱92·142. \(\vdash:\text{ᗡ}ʻR\subset \text{D}ʻR.Q\in \text{Potid}ʻR.\supset.\text{D}ʻQ=\text{D}ʻR\) -/
theorem pm92_142 {R Q : α → α → Prop} : codom R ⊆ dom R ∧ Q ∈ potid R → dom Q = dom R := by
  rintro ⟨h, hQ⟩
  obtain ⟨n, rfl⟩ := mem_potid'.1 hQ
  exact dom_ipow h _

/-- ✱92·143. \(\vdash:\text{D}ʻR\subset \text{ᗡ}ʻR.Q\in \text{Potid}ʻR.\supset.\text{ᗡ}ʻQ=\text{ᗡ}ʻR\) -/
theorem pm92_143 {R Q : α → α → Prop} : dom R ⊆ codom R ∧ Q ∈ potid R → codom Q = codom R :=
  fun ⟨h, hQ⟩ => pm92_142 (R := R˘) (Q := Q˘) ⟨h, pm91_521.1 hQ⟩

/-- ✱92·144. \(\vdash:R\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻR\subset \text{D}ʻR.Q\in \text{Potid}ʻR.\supset.\text{ᗡ}ʻQ\subset \text{D}ʻR.\text{ᗡ}ʻQ\subset \text{D}ʻQ\) -/
theorem pm92_144 {R Q : α → α → Prop} :
    (R ∈ arrow one Cls ∧ codom R ⊆ dom R) ∧ Q ∈ potid R → codom Q ⊆ dom R ∧ codom Q ⊆ dom Q := by
  rintro ⟨⟨-, h⟩, hQ⟩
  have h1 : codom Q ⊆ dom R := fun y ⟨x, hxy⟩ => fld_sub_dom h (pm91_27 hQ ⟨x, Or.inr hxy⟩)
  exact ⟨h1, (pm92_142 ⟨h, hQ⟩).symm ▸ h1⟩

/-- ✱92·145. \(\vdash:R\in \text{Cls}\rightarrow 1.\text{D}ʻR\subset \text{ᗡ}ʻR.Q\in \text{Potid}ʻR.\supset.\text{D}ʻQ\subset \text{ᗡ}ʻR.\text{D}ʻQ\subset \text{ᗡ}ʻQ\) -/
theorem pm92_145 {R Q : α → α → Prop} :
    (R ∈ arrow Cls one ∧ dom R ⊆ codom R) ∧ Q ∈ potid R → dom Q ⊆ codom R ∧ dom Q ⊆ codom Q := by
  rintro ⟨⟨-, h⟩, hQ⟩
  have h1 : dom Q ⊆ codom R := by
    rintro x ⟨y, hxy⟩
    have hx : x ∈ fld R˘ := (fld_cnv R).symm ▸ pm91_27 hQ ⟨y, Or.inl hxy⟩
    exact fld_sub_dom (R := R˘) h hx
  exact ⟨h1, (pm92_143 ⟨h, hQ⟩).symm ▸ h1⟩

/-- ✱92·146. \(\vdash:R\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻR\subset \text{D}ʻR.Q,\,T\in \text{Potid}ʻR.\supset.T\upharpoonright \text{D}ʻQ=T\) -/
theorem pm92_146 {R Q T : α → α → Prop} :
    (R ∈ arrow one Cls ∧ codom R ⊆ dom R) ∧ Mem2 Q T (potid R) → T ↾ dom Q = T := by
  rintro ⟨hR, hQ, hT⟩
  rw [pm92_142 ⟨hR.2, hQ⟩]
  exact cres_eq_self (pm92_144 ⟨hR, hT⟩).1

/-- ✱92·147. \(\vdash:R\in \text{Cls}\rightarrow 1.\text{D}ʻR\subset \text{ᗡ}ʻR.Q,\,T\in \text{Potid}ʻR.\supset.(\text{ᗡ}ʻQ)\upharpoonleft T=T\) -/
theorem pm92_147 {R Q T : α → α → Prop} :
    (R ∈ arrow Cls one ∧ dom R ⊆ codom R) ∧ Mem2 Q T (potid R) → codom Q ◁ T = T := by
  rintro ⟨hR, hQ, hT⟩
  rw [pm92_143 ⟨hR.2, hQ⟩]
  exact dres_eq_self (pm92_145 ⟨hR, hT⟩).1

/-- ✱92·15. \[\begin{align}&\vdash:R\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻR\subset \text{D}ʻR.Q,\,T\in \text{Potid}ʻR.\supset.T\mid Q\mid \breve{Q}=T\\ &[\text{*92·13·146}]\end{align}\] -/
theorem pm92_15 {R Q T : α → α → Prop} :
    (R ∈ arrow one Cls ∧ codom R ⊆ dom R) ∧ Mem2 Q T (potid R) → T ⨾ Q ⨾ Q˘ = T := by
  intro h
  rw [pm92_13 ⟨h.1.1, h.2⟩, pm92_146 h]

/-- ✱92·151. \(\vdash:R\in \text{Cls}\rightarrow 1.\text{D}ʻR\subset \text{ᗡ}ʻR.Q,T\in \text{Potid}ʻR.\supset.\breve{Q}\mid Q\mid T=T\) -/
theorem pm92_151 {R Q T : α → α → Prop} :
    (R ∈ arrow Cls one ∧ dom R ⊆ codom R) ∧ Mem2 Q T (potid R) → Q˘ ⨾ Q ⨾ T = T := by
  intro h
  rw [pm92_131 ⟨h.1.1, h.2⟩, pm92_147 h]

/-- ✱92·152. \[\begin{align}&\vdash:R\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻR\subset \text{D}ʻR.Q,\,T\in \text{Potid}ʻR.\supset.Q\mid T\mid \breve{Q}=T\\ &[\text{*92·15.*91·34}]\end{align}\] -/
theorem pm92_152 {R Q T : α → α → Prop} :
    (R ∈ arrow one Cls ∧ codom R ⊆ dom R) ∧ Mem2 Q T (potid R) → Q ⨾ T ⨾ Q˘ = T := by
  intro h
  rw [pm91_34 h.2, pm92_15 h]

/-- ✱92·153. \(\vdash:R\in \text{Cls}\rightarrow 1.\text{D}ʻR\subset \text{ᗡ}ʻR.Q,\,T\in \text{Potid}ʻR.\supset.\breve{Q}\mid T\mid Q=T\) -/
theorem pm92_153 {R Q T : α → α → Prop} :
    (R ∈ arrow Cls one ∧ dom R ⊆ codom R) ∧ Mem2 Q T (potid R) → Q˘ ⨾ T ⨾ Q = T := by
  intro h
  rw [rp_assoc, ← pm91_34 h.2, ← rp_assoc, pm92_151 h]

/-- ✱92·16. \[\begin{align}\vdash\colon\ldotp R\in &1\rightarrow \text{Cls}.P,\,Q\in \text{Potid}ʻR.\supset:\\ &(\exists T):T\in \text{Potid}ʻR:P\mid \breve{Q}=T\upharpoonright \text{D}ʻQ.\lor.P\mid \breve{Q}=\text{Cnv}ʻ(T\upharpoonright \text{D}ʻP)\end{align}\] -/
theorem pm92_16 {R P Q : α → α → Prop} :
    R ∈ arrow one Cls ∧ Mem2 P Q (potid R) →
      ∃ T, T ∈ potid R ∧ (P ⨾ Q˘ = T ↾ dom Q ∨ P ⨾ Q˘ = (T ↾ dom P)˘) := by
  rintro ⟨hR, hP, hQ⟩
  obtain ⟨T, hT, h | h⟩ := pm91_46 ⟨hP, hQ⟩
  · subst h
    refine ⟨T, hT, Or.inr ?_⟩
    rw [← pm92_13 ⟨hR, hP, hT⟩]
    simp only [cnv_comp, cnv_cnv, rp_assoc]
  · subst h
    exact ⟨T, hT, Or.inl (pm92_13 ⟨hR, hQ, hT⟩)⟩

/-- ✱92·161. \[\begin{align}\vdash\colon\ldotp &R\in \text{Cls}\rightarrow 1.P,\,Q\in \text{Potid}ʻR.\supset:\\ &(\exists T):T\in \text{Potid}ʻR:\breve{Q}\mid P=(\text{ᗡ}ʻQ)\upharpoonleft T.\lor.\breve{Q}\mid P=\text{Cnv}ʻ\{(\text{ᗡ}ʻP)\upharpoonleft T\}\end{align}\] -/
theorem pm92_161 {R P Q : α → α → Prop} :
    R ∈ arrow Cls one ∧ Mem2 P Q (potid R) →
      ∃ T, T ∈ potid R ∧ (Q˘ ⨾ P = codom Q ◁ T ∨ Q˘ ⨾ P = (codom P ◁ T)˘) := by
  rintro ⟨hR, hP, hQ⟩
  obtain ⟨T, hT, h | h⟩ := pm91_45 ⟨hP, hQ⟩
  · subst h
    refine ⟨T, hT, Or.inr ?_⟩
    rw [← pm92_131 ⟨hR, hP, hT⟩]
    simp only [cnv_comp, cnv_cnv, rp_assoc]
  · subst h
    refine ⟨T, hT, Or.inl ?_⟩
    rw [← rp_assoc, pm92_131 ⟨hR, hQ, hT⟩]

/-- ✱92·17. \(\vdash:R\in 1\rightarrow \text{Cls}.P,\,Q\in \text{Potid}ʻR.\supset.(\exists T).T\in \text{Potid}ʻR.P\mid \breve{Q}\unicode{x2abd}T\unicode{x228d}\breve{T}\) -/
theorem pm92_17 {R P Q : α → α → Prop} :
    R ∈ arrow one Cls ∧ Mem2 P Q (potid R) → ∃ T, T ∈ potid R ∧ P ⨾ Q˘ ⪽ T ⊍ T˘ := by
  intro h
  obtain ⟨T, hT, e | e⟩ := pm92_16 h
  · refine ⟨T, hT, ?_⟩
    rw [e]
    exact fun _ _ h' => Or.inl h'.1
  · refine ⟨T, hT, ?_⟩
    rw [e]
    exact fun _ _ h' => Or.inr h'.1

/-- ✱92·171. \(\vdash:R\in \text{Cls}\rightarrow 1.P,Q\in \text{Potid}ʻR.\supset.(\exists T).T\in \text{Potid}ʻR.\breve{Q}\mid P\unicode{x2abd}T\unicode{x228d}\breve{T}\) -/
theorem pm92_171 {R P Q : α → α → Prop} :
    R ∈ arrow Cls one ∧ Mem2 P Q (potid R) → ∃ T, T ∈ potid R ∧ Q˘ ⨾ P ⪽ T ⊍ T˘ := by
  intro h
  obtain ⟨T, hT, e | e⟩ := pm92_161 h
  · refine ⟨T, hT, ?_⟩
    rw [e]
    exact fun _ _ h' => Or.inl h'.2
  · refine ⟨T, hT, ?_⟩
    rw [e]
    exact fun _ _ h' => Or.inr h'.2

/-- ✱92·18. \[\begin{align}\vdash:R\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻR\subset \text{D}ʻR.P,Q\in \text{Potid}ʻ&R.\supset.\\ &P\mid \breve{Q}\in \text{Potid}ʻR\cup \text{Potid}ʻ\breve{R}\end{align}\] -/
theorem pm92_18 {R P Q : α → α → Prop} :
    (R ∈ arrow one Cls ∧ codom R ⊆ dom R) ∧ Mem2 P Q (potid R) →
      P ⨾ Q˘ ∈ potid R ∪ potid R˘ := by
  rintro ⟨hR, hP, hQ⟩
  obtain ⟨T, hT, e | e⟩ := pm92_16 ⟨hR.1, hP, hQ⟩
  · rw [e, pm92_146 ⟨hR, hQ, hT⟩]
    exact Or.inl hT
  · rw [e, pm92_146 ⟨hR, hP, hT⟩]
    exact Or.inr (pm91_521.1 hT)

/-- ✱92·181. \[\begin{align}\vdash:R\in \text{Cls}\rightarrow 1.\text{D}ʻR\subset \text{ᗡ}ʻR.P,Q\in \text{Potid}ʻ&R.\supset.\\ &\breve{Q}\mid P\in \text{Potid}ʻR\cup \text{Potid}ʻ\breve{R}\end{align}\] -/
theorem pm92_181 {R P Q : α → α → Prop} :
    (R ∈ arrow Cls one ∧ dom R ⊆ codom R) ∧ Mem2 P Q (potid R) →
      Q˘ ⨾ P ∈ potid R ∪ potid R˘ := by
  rintro ⟨hR, hP, hQ⟩
  obtain ⟨T, hT, e | e⟩ := pm92_161 ⟨hR.1, hP, hQ⟩
  · rw [e, pm92_147 ⟨hR, hQ, hT⟩]
    exact Or.inl hT
  · rw [e, pm92_147 ⟨hR, hP, hT⟩]
    exact Or.inr (pm91_521.1 hT)

/-- ✱92·19. \[\begin{align}\vdash:R\in 1\rightarrow \text{Cls}.\text{ᗡ}ʻR\subset \text{D}ʻR.P,&Q\in \text{Potid}ʻR.\supset:\\ &P\mid \breve{Q}\in \text{Potid}ʻR.\lor.Q\mid \breve{P}\in \text{Potid}ʻR\end{align}\] -/
theorem pm92_19 {R P Q : α → α → Prop} :
    (R ∈ arrow one Cls ∧ codom R ⊆ dom R) ∧ Mem2 P Q (potid R) →
      P ⨾ Q˘ ∈ potid R ∨ Q ⨾ P˘ ∈ potid R := by
  intro h
  rcases pm92_18 h with h' | h'
  · exact Or.inl h'
  · refine Or.inr ?_
    have := pm91_521.1 h'
    rwa [cnv_comp, cnv_cnv] at this

/-- ✱92·191. \[\begin{align}\vdash:R\in \text{Cls}\rightarrow 1.\text{D}ʻR\subset \text{ᗡ}ʻR.P\mid Q &\in \text{Potid}ʻR.\supset:\\ &\breve{P}\mid Q\in \text{Potid}ʻR.\lor.\breve{Q}\mid P\in \text{Potid}ʻR\end{align}\]

**Status.** proved (reading): the e-text prints the hypothesis `P|Q ∈ Potid'R`; PM means
`P, Q ∈ Potid'R`, as in its companion ✱92·19, of which ✱92·191 is the converse form (✱92·181,
from which it follows as ✱92·19 follows from ✱92·18, has `P, Q ∈ Potid'R`). As printed it is
false: with `R = Λ̇` (whose only power is `Λ̇ = I ↾ C'R`) and `P = Q = x ↓ y`, `x ≠ y`, we have
`P|Q = Λ̇ ∈ Potid'R` but `P̆|Q = Q̆|P = y ↓ y ≠ Λ̇` (`pm92_191_printed_false`). -/
theorem pm92_191 {R P Q : α → α → Prop} :
    (R ∈ arrow Cls one ∧ dom R ⊆ codom R) ∧ Mem2 P Q (potid R) →
      P˘ ⨾ Q ∈ potid R ∨ Q˘ ⨾ P ∈ potid R := by
  intro h
  rcases pm92_181 h with h' | h'
  · exact Or.inr h'
  · refine Or.inl ?_
    have := pm91_521.1 h'
    rwa [cnv_comp, cnv_cnv] at this

/-- The printed form of ✱92·191 (hypothesis `P|Q ∈ Potid'R`) is false: take `R = Λ̇` and
`P = Q = x ↓ y` with `x ≠ y`. -/
theorem pm92_191_printed_false :
    ¬ ∀ R P Q : Bool → Bool → Prop,
      (R ∈ arrow Cls one ∧ dom R ⊆ codom R) ∧ P ⨾ Q ∈ potid R →
        P˘ ⨾ Q ∈ potid R ∨ Q˘ ⨾ P ∈ potid R := by
  intro h
  let R : Bool → Bool → Prop := fun _ _ => False
  let P : Bool → Bool → Prop := false ↓ true
  have hempty : ∀ X, X ∈ potid R → ∀ a b, ¬ X a b := by
    intro X hX a b hab
    obtain ⟨⟨c, hc | hc⟩, -⟩ := pm91_58 hX a b hab <;> exact hc
  have hPP : P ⨾ P = I ↾ fld R := by
    funext a b
    apply propext
    constructor
    · rintro ⟨c, ⟨-, rfl⟩, h1, -⟩
      exact absurd h1 Bool.noConfusion
    · rintro ⟨-, c, hc | hc⟩ <;> exact hc.elim
  have hR : R ∈ arrow Cls one := mem_arrow_Cls_one.2 fun _ _ _ h => h.1.elim
  have h1 := h R P P ⟨⟨hR, fun _ ⟨_, h⟩ => h.elim⟩, hPP ▸ pm91_35⟩
  have hw : (P˘ ⨾ P) true true := ⟨false, ⟨rfl, rfl⟩, rfl, rfl⟩
  rcases h1 with h1 | h1 <;> exact hempty _ h1 true true hw

/-- ✱92·3. \(\vdash:R\in 1\rightarrow \text{Cls}.P,\,Q\in \text{Potid}ʻR.\supset.P\mid \breve{Q}\unicode{x2abd}R_{\unicode{x2217}}\unicode{x228d}\breve{R}_{\unicode{x2217}}\) -/
theorem pm92_3 {R P Q : α → α → Prop} :
    R ∈ arrow one Cls ∧ Mem2 P Q (potid R) → P ⨾ Q˘ ⪽ anc R ⊍ ancCnv R := by
  intro h x y hxy
  obtain ⟨T, hT, hsub⟩ := pm92_17 h
  rcases hsub x y hxy with h' | h'
  · exact Or.inl (pm91_58 hT x y h')
  · exact Or.inr (pm91_58 hT y x h')

/-- ✱92·301. \(\vdash:R\in \text{Cls}\rightarrow 1.P,\,Q\in \text{Potid}ʻR.\supset.\breve{P}\mid Q\unicode{x2abd}R_{\unicode{x2217}}\unicode{x228d}\breve{R}_{\unicode{x2217}}\) -/
theorem pm92_301 {R P Q : α → α → Prop} :
    R ∈ arrow Cls one ∧ Mem2 P Q (potid R) → P˘ ⨾ Q ⪽ anc R ⊍ ancCnv R := by
  rintro ⟨hR, hP, hQ⟩ x y hxy
  obtain ⟨T, hT, hsub⟩ := pm92_171 ⟨hR, hQ, hP⟩
  rcases hsub x y hxy with h' | h'
  · exact Or.inl (pm91_58 hT x y h')
  · exact Or.inr (pm91_58 hT y x h')

/-- ✱92·31. \(\vdash:R\in 1\rightarrow \text{Cls}.\supset.R_{\unicode{x2217}}\mid \breve{R}_{\unicode{x2217}}=R_{\unicode{x2217}}\unicode{x228d}\breve{R}_{\unicode{x2217}}\) -/
theorem pm92_31 {R : α → α → Prop} :
    R ∈ arrow one Cls → anc R ⨾ ancCnv R = anc R ⊍ ancCnv R := by
  intro hR
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, hzy⟩
    obtain ⟨m, hm⟩ := anc_iff_ipow.1 hxy
    obtain ⟨n, hn⟩ := anc_iff_ipow.1 hzy
    exact pm92_3 ⟨hR, ipow_mem_potid R m, ipow_mem_potid R n⟩ x z ⟨y, hm, hn⟩
  · rintro (h | h)
    · exact ⟨z, h, anc_refl (anc_fld_right h)⟩
    · exact ⟨x, anc_refl (anc_fld_right h), h⟩

/-- ✱92·311. \(\vdash:R\in \text{Cls}\rightarrow 1.\supset.\breve{R}_{\unicode{x2217}}\mid R_{\unicode{x2217}}=R_{\unicode{x2217}}\unicode{x228d}\breve{R}_{\unicode{x2217}}\) -/
theorem pm92_311 {R : α → α → Prop} :
    R ∈ arrow Cls one → ancCnv R ⨾ anc R = anc R ⊍ ancCnv R := by
  intro hR
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hyx, hyz⟩
    obtain ⟨m, hm⟩ := anc_iff_ipow.1 hyx
    obtain ⟨n, hn⟩ := anc_iff_ipow.1 hyz
    exact pm92_301 ⟨hR, ipow_mem_potid R m, ipow_mem_potid R n⟩ x z ⟨y, hm, hn⟩
  · rintro (h | h)
    · exact ⟨x, anc_refl h.1, h⟩
    · exact ⟨z, h, anc_refl h.1⟩

/-- ✱92·312. \(\vdash:R\in 1\rightarrow 1.\supset.R_{\unicode{x2217}}\mid \breve{R}_{\unicode{x2217}}=\breve{R}_{\unicode{x2217}}\mid R_{\unicode{x2217}}=R_{\unicode{x2217}}\unicode{x228d}\breve{R}_{\unicode{x2217}} \quad[\text{*92·31·311}]\) -/
theorem pm92_312 {R : α → α → Prop} :
    R ∈ arrow one one →
      anc R ⨾ ancCnv R = ancCnv R ⨾ anc R ∧ ancCnv R ⨾ anc R = anc R ⊍ ancCnv R := by
  intro hR
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
  have e1 := pm92_31 (mem_arrow_one_Cls.2 h1)
  have e2 := pm92_311 (mem_arrow_Cls_one.2 h2)
  exact ⟨e1.trans e2.symm, e2⟩

/-- ✱92·32. \(\vdash:R\in 1\rightarrow 1.\supset.(R_{\unicode{x2217}}\unicode{x228d}\breve{R}_{\unicode{x2217}})\mid (R\unicode{x228d}\breve{R})\unicode{x2abd}R_{\unicode{x2217}}\unicode{x228d}\breve{R}_{\unicode{x2217}}\) -/
theorem pm92_32 {R : α → α → Prop} :
    R ∈ arrow one one → (anc R ⊍ ancCnv R) ⨾ (R ⊍ R˘) ⪽ anc R ⊍ ancCnv R := by
  intro hR
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
  have e1 := pm92_31 (mem_arrow_one_Cls.2 h1)
  have e2 := pm92_311 (mem_arrow_Cls_one.2 h2)
  rintro x z ⟨a, hxa | hax, haz | hza⟩
  · exact Or.inl (anc_tail hxa haz)
  · rw [← e1]
    exact ⟨a, hxa, R_sub_anc hza⟩
  · rw [← e2]
    exact ⟨a, hax, R_sub_anc haz⟩
  · exact Or.inr (anc_head hza hax)

/-- ✱92·33. \(\vdash:R\in 1\rightarrow 1.\supset.(R\unicode{x228d}\breve{R})_{\unicode{x2217}}=R_{\unicode{x2217}}\unicode{x228d}\breve{R}_{\unicode{x2217}}\) -/
theorem pm92_33 {R : α → α → Prop} :
    R ∈ arrow one one → anc (R ⊍ R˘) = anc R ⊍ ancCnv R := by
  intro hR
  have hfld : fld (R ⊍ R˘) = fld R := by
    ext x
    constructor
    · rintro ⟨y, (h | h) | (h | h)⟩
      · exact ⟨y, Or.inl h⟩
      · exact ⟨y, Or.inr h⟩
      · exact ⟨y, Or.inr h⟩
      · exact ⟨y, Or.inl h⟩
    · rintro ⟨y, h | h⟩
      · exact ⟨y, Or.inl (Or.inl h)⟩
      · exact ⟨y, Or.inl (Or.inr h)⟩
  have hsymm : (R ⊍ R˘)˘ = R ⊍ R˘ := by
    funext a b
    exact propext Or.comm
  funext x y
  apply propext
  constructor
  · intro h
    rw [anc_iff_reflTransGen, hfld] at h
    obtain ⟨hx, h⟩ := h
    induction h with
    | refl => exact Or.inl (anc_refl hx)
    | tail _ hbc ih => exact pm92_32 hR _ _ ⟨_, ih, hbc⟩
  · rintro (h | h)
    · exact pm90_18 (fun a b h' => Or.inl h') x y h
    · have h' : anc (R ⊍ R˘) y x := pm90_18 (fun a b h' => Or.inl h') y x h
      have h'' : ancCnv (R ⊍ R˘) x y := h'
      rw [ancCnv_iff, hsymm] at h''
      exact h''

/-- ✱92·34. \(\vdash:R\in 1\rightarrow 1.\supset.(R\unicode{x228d}\breve{R})_{\text{po}}=R_{\unicode{x2217}}\unicode{x228d}\breve{R}_{\unicode{x2217}}\) -/
theorem pm92_34 {R : α → α → Prop} :
    R ∈ arrow one one → po (R ⊍ R˘) = anc R ⊍ ancCnv R := by
  intro hR
  rw [← pm92_33 hR]
  funext x y
  apply propext
  constructor
  · exact po_sub_anc
  · intro h
    rcases anc_iff_po.1 h with ⟨rfl, w, hw | hw⟩ | h
    · exact po_trans (R_sub_po hw) (R_sub_po (Or.comm.1 hw))
    · exact po_trans (R_sub_po (Or.comm.1 hw)) (R_sub_po hw)
    · exact h

/-!
## [✱93] Inductive analysis of the field of a relation

*(Vol. 1, p. 607)*

> *Summary of* *93.
>
> For this number, we introduce three new notations, of which the first two will be used constantly, especially in the theory of series, while the third will be seldom used except in the present section. The two which are constantly used are \[ xBP, ~ \text{meaning} ~ x \in \text{D}ʻP - \text{ᗡ}ʻP \] \[ \text{and} \quad x \mathop{\text{min}_{P}} \alpha, ~ \text{meaning} ~ x \in \alpha \cap CʻP-\breve{P}ʻʻ\alpha\text{,} \] *i.e.* \(x\) is a member of \(\alpha\) and of \(CʻP\), and no member of \(\alpha\) precedes \(x\) in \(CʻP\).
>
> …

**Lean reading.** `B` is `Beg` (`x B P ↔ x ∈ D'P − ᗡ'P`), `min_P` is `minP P` and
`max_P` is `maxP P = minP P˘`; their descriptive functions `B'P`, `min_P'α` may fail to exist, so
`x = B'P` is `Desc Beg P (fun b => x = b)` and `ῐ'α` is `Desc iota˘ A`, while the plurals `B⃗'P`,
`min⃗_P'α`, `max⃗_P'α` are the classes `refs Beg P`, `refs (minP P) A`, `refs (maxP P) A`
(✱93·101·111·116, which compute these values from the definitions as ✱32·13 does, keep the
description `Desc (Rfwd …)`). `gen'P` is `gen P` (✱93·03), `ᗡ''Pot'P` is `Dcnv ʻʻ pot P`, `p'`
and `s'` are `prodCls`, `sumCls`, `∃!α` is `A.Nonempty`, `Cls² excl` and `Cls ex² excl` are
`Cls2excl`, `ClsEx2excl`, `|S''κ` is `relProdR S ʻʻ K` and `T|''κ` is `relProdL T ʻʻ K`. The
e-text numbers ✱93·12 and ✱93·2 "✱92·12" and "✱92·2" (their anchors are `*93·12`, `*93·2`).
✱93·132 needs the hypothesis `ᗡ'T ⊂ C'P` (see its docstring). ✱93·31
prints `min⃗_P'(T|P)` for `min⃗_P'ᗡ'(T|P)` (as its demonstration has it).

**Status.** proved (all propositions; ✱93·01–✱93·03 definition; ✱93·132 proved (corrected), ✱93·31
and ✱93·4 proved (reading), see their docstrings).
-/

/-- ✱93·01 (Df). \(B=\hat{x}\hat{P}(x\in \text{D}ʻP-\text{ᗡ}ʻP) \quad\text{Df}\) -/
theorem pm93_01 : (Beg : α → (α → α → Prop) → Prop) = fun x P => x ∈ dom P \ codom P := rfl

/-- ✱93·02 (Df). \(\text{min}_{P}=\text{min}(P)=\hat{x}\hat{\alpha}(x\in \alpha\cap CʻP-\breve{P}ʻʻ\alpha) \quad\text{Df}\) -/
theorem pm93_02 (P : α → α → Prop) : minP P = fun x A => x ∈ (A ∩ fld P) \ P˘ ʻʻ A := rfl

/-- ✱93·021 (Df). \(\text{max}_{P}=\text{max}(P)=\text{min}(\breve{P}) \quad\text{Df}\) -/
theorem pm93_021 (P : α → α → Prop) : maxP P = minP P˘ := rfl

/-- ✱93·03 (Df). \(\text{gen}ʻP=\overrightarrow{\text{min}}_{P}ʻʻ\text{ᗡ}ʻʻ\text{Potid}ʻP \quad\text{Df}\) -/
theorem pm93_03 (P : α → α → Prop) : gen P = Rfwd (minP P) ʻʻ Dcnv ʻʻ potid P := rfl

/-- ✱93·1. \(\vdash:xBP.\equiv.x\in \text{D}ʻP-\text{ᗡ}ʻP \quad[\text{*21·3.(*93·01)}]\) -/
theorem pm93_1 {x : α} {P : α → α → Prop} : Beg x P ↔ x ∈ dom P \ codom P := Iff.rfl

/-- ✱93·101. \(\vdash.\overrightarrow{B}ʻP=\text{D}ʻP-\text{ᗡ}ʻP \quad[\text{*93·1.*32·18}]\) -/
theorem pm93_101 {P : α → α → Prop} : Desc (Rfwd Beg) P (fun A => A = dom P \ codom P) :=
  (desc_graph (refs Beg) P _).2 rfl

/-- ✱93·102. \[\begin{align}&\vdash:x=BʻP.\equiv.x=\breve{\iota}ʻ(\text{D}ʻP-\text{ᗡ}ʻP).\equiv.\text{D}ʻP-\text{ᗡ}ʻP\in 1.x\in \text{D}ʻP-\text{ᗡ}ʻP\\ &[\text{*93·101.*53·4}]\end{align}\] -/
theorem pm93_102 {x : α} {P : α → α → Prop} :
    (Desc Beg P (fun b => x = b) ↔ Desc iota˘ (dom P \ codom P) (fun b => x = b)) ∧
      (Desc iota˘ (dom P \ codom P) (fun b => x = b) ↔
        dom P \ codom P ∈ one ∧ x ∈ dom P \ codom P) := by
  refine ⟨(desc_iota_cnv _ _).symm, ?_⟩
  rw [desc_iota_cnv]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨mem_one_iff.2 ⟨x, hb⟩, (hb x).2 rfl⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨b, hb⟩ := mem_one_iff.1 h1
    exact ⟨b, hb, (hb x).1 h2⟩

/-- ✱93·103. \(\vdash.\overrightarrow{B}ʻP=CʻP-\text{ᗡ}ʻP\) -/
theorem pm93_103 {P : α → α → Prop} : refs Beg P = fld P \ codom P := by
  ext x
  constructor
  · rintro ⟨⟨y, h⟩, h'⟩
    exact ⟨⟨y, Or.inl h⟩, h'⟩
  · rintro ⟨⟨y, h | h⟩, h'⟩
    · exact ⟨⟨y, h⟩, h'⟩
    · exact absurd ⟨y, h⟩ h'

/-- ✱93·104. \(\vdash:xBR.\supset.\overrightarrow{R}_{\unicode{x2217}}ʻx=\iotaʻx.\overrightarrow{R}_{\text{po}}ʻx=\Lambda\) -/
theorem pm93_104 {x : α} {R : α → α → Prop} :
    Beg x R → refs (anc R) x = ι x ∧ refs (po R) x = Λ := by
  rintro ⟨⟨z, hxz⟩, hx⟩
  have hpo : ∀ y, ¬ po R y x := by
    intro y h
    rw [po_eq_anc_comp] at h
    obtain ⟨b, -, hb⟩ := h
    exact hx ⟨b, hb⟩
  refine ⟨?_, eq_Null hpo⟩
  ext y
  constructor
  · intro h
    rcases anc_iff_po.1 h with ⟨rfl, -⟩ | h
    · rfl
    · exact absurd h (hpo y)
  · rintro rfl
    exact anc_refl ⟨z, Or.inl hxz⟩

/-- ✱93·11. \(\vdash:x\, \text{min}_{P}\,\alpha.\equiv.x\in \alpha\cap CʻP-\breve{P}ʻʻ\alpha \quad[\text{(*93·02)}]\) -/
theorem pm93_11 {x : α} {P : α → α → Prop} {A : Set α} :
    minP P x A ↔ x ∈ (A ∩ fld P) \ P˘ ʻʻ A := Iff.rfl

/-- ✱93·111. \(\vdash.\overrightarrow{\text{min}}_{P}ʻ\alpha=\alpha\cap CʻP-\breve{P}ʻʻ\alpha \quad[\text{*93·11.*32·18}]\) -/
theorem pm93_111 {P : α → α → Prop} {A : Set α} :
    Desc (Rfwd (minP P)) A (fun B => B = (A ∩ fld P) \ P˘ ʻʻ A) :=
  (desc_graph (refs (minP P)) A _).2 rfl

/-- ✱93·112. \(\vdash.\overrightarrow{B}ʻP=\overrightarrow{\text{min}}_{P}ʻ\text{D}ʻP=\overrightarrow{\text{min}}_{P}ʻCʻP\) -/
theorem pm93_112 {P : α → α → Prop} :
    refs Beg P = refs (minP P) (dom P) ∧ refs (minP P) (dom P) = refs (minP P) (fld P) := by
  have h1 : P˘ ʻʻ dom P = codom P := by
    ext z
    exact ⟨fun ⟨y, _, h⟩ => ⟨y, h⟩, fun ⟨y, h⟩ => ⟨y, ⟨z, h⟩, h⟩⟩
  have h2 : P˘ ʻʻ fld P = codom P := by
    ext z
    exact ⟨fun ⟨y, _, h⟩ => ⟨y, h⟩, fun ⟨y, h⟩ => ⟨y, ⟨z, Or.inl h⟩, h⟩⟩
  have e1 : refs (minP P) (dom P) = refs Beg P := by
    ext x
    show (x ∈ dom P ∧ x ∈ fld P) ∧ x ∉ P˘ ʻʻ dom P ↔ x ∈ dom P ∧ x ∉ codom P
    rw [h1]
    exact ⟨fun ⟨⟨h, _⟩, h'⟩ => ⟨h, h'⟩, fun ⟨⟨y, h⟩, h'⟩ => ⟨⟨⟨y, h⟩, ⟨y, Or.inl h⟩⟩, h'⟩⟩
  have e2 : refs (minP P) (fld P) = refs Beg P := by
    ext x
    show (x ∈ fld P ∧ x ∈ fld P) ∧ x ∉ P˘ ʻʻ fld P ↔ x ∈ refs Beg P
    rw [h2, pm93_103]
    exact ⟨fun ⟨⟨h, _⟩, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨⟨h, h⟩, h'⟩⟩
  rw [e1, e2]
  exact ⟨rfl, rfl⟩

/-- ✱93·113. \(\vdash.\overrightarrow{\text{min}}_{P}ʻ\alpha\subset \alpha\cap CʻP \quad[\text{*93·111}]\) -/
theorem pm93_113 {P : α → α → Prop} {A : Set α} : refs (minP P) A ⊆ A ∩ fld P :=
  fun _ h => h.1

/-- ✱93·114. \(\vdash.\text{max}_{P}=\text{min}(\breve{P}) \quad[\text{(*93·021)}]\) -/
theorem pm93_114 {P : α → α → Prop} : maxP P = minP P˘ := rfl

/-- ✱93·115. \(\vdash:x\, \text{max}_{P}\,\alpha.\equiv.x\in \alpha\cap CʻP-Pʻʻ\alpha \quad[\text{*93·11·114}]\) -/
theorem pm93_115 {x : α} {P : α → α → Prop} {A : Set α} :
    maxP P x A ↔ x ∈ (A ∩ fld P) \ P ʻʻ A := by
  show x ∈ (A ∩ fld P˘) \ P˘˘ ʻʻ A ↔ _
  rw [fld_cnv]
  exact Iff.rfl

/-- ✱93·116. \(\vdash.\overrightarrow{\text{max}}_{P}ʻ\alpha=\alpha\cap CʻP-Pʻʻ\alpha \quad[\text{*93·115.*32·18}]\) -/
theorem pm93_116 {P : α → α → Prop} {A : Set α} :
    Desc (Rfwd (maxP P)) A (fun B => B = (A ∩ fld P) \ P ʻʻ A) :=
  (desc_graph (refs (maxP P)) A _).2 (Set.ext fun _ => pm93_115)

/-- ✱93·117. \(\vdash.\overrightarrow{B}ʻ\breve{P}=\overrightarrow{\text{max}}_{P}ʻ\text{ᗡ}ʻP=\overrightarrow{\text{max}}_{P}ʻCʻP \quad[\text{*93·112·114}]\) -/
theorem pm93_117 {P : α → α → Prop} :
    refs Beg P˘ = refs (maxP P) (codom P) ∧ refs (maxP P) (codom P) = refs (maxP P) (fld P) := by
  have h := pm93_112 (P := P˘)
  rw [fld_cnv] at h
  exact h

/-- ✱93·118. \(\vdash.\overrightarrow{\text{max}}_{P}ʻ\alpha\subset \alpha\cap CʻP \quad[\text{*93·116}]\) -/
theorem pm93_118 {P : α → α → Prop} {A : Set α} : refs (maxP P) A ⊆ A ∩ fld P := by
  intro x h
  have h' := h.1
  rw [fld_cnv] at h'
  exact h'

/-- ✱93·12. \(\vdash.\overrightarrow{B}ʻ\breve{P}=\text{ᗡ}ʻP-\text{D}ʻP=CʻP-\text{D}ʻP \quad[\text{*93·101·103.*33·2·21·22}]\) -/
theorem pm93_12 {P : α → α → Prop} :
    refs Beg P˘ = codom P \ dom P ∧ codom P \ dom P = fld P \ dom P := by
  refine ⟨rfl, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨y, h⟩, h'⟩
    exact ⟨⟨y, Or.inr h⟩, h'⟩
  · rintro ⟨⟨y, h | h⟩, h'⟩
    · exact absurd ⟨y, h⟩ h'
    · exact ⟨⟨y, h⟩, h'⟩

/-- ✱93·13.\(\vdash.\overrightarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻ(I\upharpoonright CʻP)=\overrightarrow{B}ʻP \quad[\text{*50·5·52.*93·112}]\) -/
theorem pm93_13 {P : α → α → Prop} : refs (minP P) (codom (I ↾ fld P)) = refs Beg P := by
  have e : codom (I ↾ fld P) = fld P := by
    ext x
    constructor
    · rintro ⟨y, -, h⟩
      exact h
    · intro h
      exact ⟨x, rfl, h⟩
  rw [e, pm93_112.1, pm93_112.2]

/-- ✱93·131. \(\vdash.\overrightarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻP=\text{ᗡ}ʻP-\text{ᗡ}ʻP^{2}\) -/
theorem pm93_131 {P : α → α → Prop} : refs (minP P) (codom P) = codom P \ codom (rsq P) :=
  refs_minP_codom fun _ ⟨x, h⟩ => ⟨x, Or.inr h⟩

/-- ✱93·132. \(\vdash.\overrightarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻT=\text{ᗡ}ʻT-\text{ᗡ}ʻ(T\mid P)\)

**Status.** proved (corrected): as printed (for any `T`) the equation is false, since
`min⃗_P'ᗡ'T = ᗡ'T ∩ C'P − P̆''ᗡ'T` (✱93·111) and PM's demonstration drops the factor `∩ C'P`; e.g.
for `P = Λ̇` and `T = V̇` (on a one-element type) the left side is `Λ` and the right side is `V`
(`pm93_132_printed_false`). It holds under the hypothesis `ᗡ'T ⊂ C'P`, which is satisfied in
every use PM makes of it (✱93·21, where `T ∈ Potid'P`, by ✱91·27); that is the statement proved. -/
theorem pm93_132 {P T : α → α → Prop} :
    codom T ⊆ fld P → refs (minP P) (codom T) = codom T \ codom (T ⨾ P) :=
  refs_minP_codom

/-- The printed form of ✱93·132 (without `ᗡ'T ⊂ C'P`) is false: take `P = Λ̇`, `T = V̇` in a
one-element type. -/
theorem pm93_132_printed_false :
    ¬ ∀ P T : Unit → Unit → Prop, refs (minP P) (codom T) = codom T \ codom (T ⨾ P) := by
  intro h
  have e := Set.ext_iff.1 (h (fun _ _ => False) (fun _ _ => True)) ()
  have hr : () ∈ codom (fun _ _ => True : Unit → Unit → Prop) \
      codom ((fun _ _ => True : Unit → Unit → Prop) ⨾ fun _ _ => False) :=
    ⟨⟨(), trivial⟩, fun ⟨_, _, _, h⟩ => h⟩
  obtain ⟨⟨-, _, h | h⟩, -⟩ := e.2 hr <;> exact h

/-- ✱93·2. \[\begin{align}&\vdash:\alpha\in \text{gen}ʻP.\equiv.(\exists T).T\in \text{Potid}ʻP.\alpha=\overrightarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻT\\ &[\text{*37·67.(*93·03)}]\end{align}\] -/
theorem pm93_2 {P : α → α → Prop} {A : Set α} :
    A ∈ gen P ↔ ∃ T, T ∈ potid P ∧ A = refs (minP P) (codom T) := by
  rw [gen]
  exact mem_minImg P (potid P) A

/-- ✱93·21.\[\begin{align}&\vdash:\alpha\in \text{gen}ʻP.\equiv.(\exists T).T\in \text{Potid}ʻP.\alpha=\text{ᗡ}ʻT-\text{ᗡ}ʻ(T\mid P)\\ &[\text{*93·2·132}]\end{align}\] -/
theorem pm93_21 {P : α → α → Prop} {A : Set α} :
    A ∈ gen P ↔ ∃ T, T ∈ potid P ∧ A = codom T \ codom (T ⨾ P) := by
  rw [gen, mem_minImg]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT, refs_minP_codom fun y ⟨x, h⟩ => pm91_27 hT ⟨x, Or.inr h⟩⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT, (refs_minP_codom fun y ⟨x, h⟩ => pm91_27 hT ⟨x, Or.inr h⟩).symm⟩

/-- ✱93·22. \(\vdash.\overrightarrow{B}ʻP\in \text{gen}ʻP \quad[\text{*93·2·13.*91·35}]\) -/
theorem pm93_22 {P : α → α → Prop} : refs Beg P ∈ gen P := by
  rw [gen, mem_minImg]
  exact ⟨I ↾ fld P, pm91_35, pm93_13.symm⟩

/-- ✱93·221. \(\vdash.\text{ᗡ}ʻP-\text{ᗡ}ʻP^{2}\in \text{gen}ʻP \quad[\text{*93·2·131.*91·351·23}]\) -/
theorem pm93_221 {P : α → α → Prop} : codom P \ codom (rsq P) ∈ gen P := by
  rw [gen, mem_minImg]
  exact ⟨P, pot_sub_potid P pm91_351, pm93_131.symm⟩

/-- ✱93·23. \(\vdash.\text{gen}ʻP=\iotaʻ\overrightarrow{B}ʻP\cup \overrightarrow{\text{min}}_{P}ʻʻ\text{ᗡ}ʻʻ\text{Pot}ʻP\) -/
theorem pm93_23 {P : α → α → Prop} :
    gen P = ι (refs Beg P) ∪ Rfwd (minP P) ʻʻ Dcnv ʻʻ pot P := by
  ext A
  show A ∈ gen P ↔ A = refs Beg P ∨ A ∈ Rfwd (minP P) ʻʻ Dcnv ʻʻ pot P
  rw [gen, mem_minImg, mem_minImg, pm91_23]
  constructor
  · rintro ⟨T, hT | hT, rfl⟩
    · have e : T = I ↾ fld P := hT
      subst e
      exact Or.inl pm93_13
    · exact Or.inr ⟨T, hT, rfl⟩
  · rintro (rfl | ⟨T, hT, rfl⟩)
    · exact ⟨I ↾ fld P, Or.inl rfl, pm93_13.symm⟩
    · exact ⟨T, Or.inr hT, rfl⟩

/-- ✱93·231. \(\vdash\colon\ldotp S,\,T\in \text{Potid}ʻP.S \neq T.\supset:\text{ᗡ}ʻS\subset \breve{P}ʻʻ\text{ᗡ}ʻT.\lor.\text{ᗡ}ʻT\subset \breve{P}ʻʻ\text{ᗡ}ʻS\) -/
theorem pm93_231 {P S T : α → α → Prop} :
    Mem2 S T (potid P) ∧ S ≠ T → codom S ⊆ P˘ ʻʻ codom T ∨ codom T ⊆ P˘ ʻʻ codom S := by
  rintro ⟨⟨hS, hT⟩, hne⟩
  obtain ⟨m, rfl⟩ := mem_potid'.1 hS
  obtain ⟨n, rfl⟩ := mem_potid'.1 hT
  rcases Nat.lt_or_ge m n with h | h
  · refine Or.inr ?_
    rw [← codom_ipow_succ]
    exact codom_ipow_mono P h
  · rcases Nat.eq_or_lt_of_le h with h | h
    · exact absurd (by rw [h]) hne
    · refine Or.inl ?_
      rw [← codom_ipow_succ]
      exact codom_ipow_mono P h

/-- ✱93·24. \(\vdash:S,\,T\in \text{Potid}ʻP.S \neq T.\supset.\overrightarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻS\cap \overrightarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻT=\Lambda\) -/
theorem pm93_24 {P S T : α → α → Prop} :
    Mem2 S T (potid P) ∧ S ≠ T → refs (minP P) (codom S) ∩ refs (minP P) (codom T) = Λ := by
  intro h
  refine eq_Null fun x ⟨hxS, hxT⟩ => ?_
  rcases pm93_231 h with h' | h'
  · exact hxT.2 (h' hxS.1.1)
  · exact hxS.2 (h' hxT.1.1)

/-- ✱93·25. \(\vdash.\text{gen}ʻP\in \text{Cls}^{2}\,\text{excl}\) -/
theorem pm93_25 {P : α → α → Prop} : gen P ∈ Cls2excl := by
  rintro A B ⟨⟨hA, hB⟩, hne⟩
  rw [gen, mem_minImg] at hA hB
  obtain ⟨S, hS, rfl⟩ := hA
  obtain ⟨T, hT, rfl⟩ := hB
  refine pm93_24 ⟨⟨hS, hT⟩, ?_⟩
  rintro rfl
  exact hne rfl

/-- ✱93·26. \(\vdash:S,\,T\in \text{Potid}ʻP.T\in \mid Sʻʻ\text{Pot}ʻP.\supset.\overrightarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻS\cap \overrightarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻT=\Lambda\) -/
theorem pm93_26 {P S T : α → α → Prop} :
    Mem2 S T (potid P) ∧ T ∈ relProdR S ʻʻ pot P →
      refs (minP P) (codom S) ∩ refs (minP P) (codom T) = Λ := by
  rintro ⟨⟨hS, -⟩, ⟨Q, hQ, hT⟩⟩
  rw [relProdR_apply] at hT
  subst hT
  obtain ⟨m, rfl⟩ := mem_potid'.1 hS
  obtain ⟨k, rfl⟩ := mem_pot'.1 hQ
  have hsub : codom (ipow P (k + 1) ⨾ ipow P m) ⊆ P˘ ʻʻ codom (ipow P m) := by
    rw [ipow_mul, ← codom_ipow_succ]
    exact codom_ipow_mono P (by omega)
  refine eq_Null fun x ⟨hxS, hxT⟩ => ?_
  exact hxS.2 (hsub hxT.1.1)

/-- ✱93·261. \(\vdash.pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP=pʻ\text{ᗡ}ʻʻ\text{Potid}ʻP.pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP\subset \text{ᗡ}ʻP\) -/
theorem pm93_261 {P : α → α → Prop} :
    prodCls (Dcnv ʻʻ pot P) = prodCls (Dcnv ʻʻ potid P) ∧ prodCls (Dcnv ʻʻ pot P) ⊆ codom P := by
  refine ⟨?_, ?_⟩
  · ext x
    rw [mem_p_pot, mem_prodCls_Dcnv]
    constructor
    · intro h T hT
      obtain ⟨n, rfl⟩ := mem_potid'.1 hT
      cases n with
      | zero => exact codom_ipow_succ_sub P 0 (h 0)
      | succ n => exact h n
    · intro h n
      exact h _ (ipow_mem_potid P _)
  · intro x hx
    have h := mem_p_pot.1 hx 0
    rwa [ipow_one] at h

/-- ✱93·27. \(\vdash\colon\ldotp x\in CʻP.\supset:x{\sim}\in sʻ\text{gen}ʻP.\equiv.x\in pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP\) -/
theorem pm93_27 {P : α → α → Prop} {x : α} :
    x ∈ fld P → (x ∉ sumCls (gen P) ↔ x ∈ prodCls (Dcnv ʻʻ pot P)) := by
  intro hx
  have hs : x ∈ sumCls (gen P) ↔ ∃ n, x ∈ refs (minP P) (codom (ipow P n)) := by
    constructor
    · rintro ⟨A, hA, hxA⟩
      obtain ⟨n, rfl⟩ := mem_gen'.1 hA
      exact ⟨n, hxA⟩
    · rintro ⟨n, hn⟩
      exact ⟨_, mem_gen'.2 ⟨n, rfl⟩, hn⟩
  rw [hs, mem_p_pot]
  simp only [mem_refs_minP_ipow, not_exists, not_and, not_not]
  constructor
  · intro h n
    induction n with
    | zero =>
      apply h 0
      rw [ipow_zero]
      exact ⟨x, rfl, hx⟩
    | succ n ih => exact h (n + 1) ih
  · intro h n _
    exact h n

/-- ✱93·271. \(\vdash.CʻP-sʻ\text{gen}ʻP=pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP\) -/
theorem pm93_271 {P : α → α → Prop} : fld P \ sumCls (gen P) = prodCls (Dcnv ʻʻ pot P) := by
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact (pm93_27 hx).1 h
  · intro h
    have hx : x ∈ fld P := by
      obtain ⟨y, hy⟩ := pm93_261.2 h
      exact ⟨y, Or.inr hy⟩
    exact ⟨hx, (pm93_27 hx).2 h⟩

/-- ✱93·272. \(\vdash.sʻ\text{gen}ʻP\subset CʻP\) -/
theorem pm93_272 {P : α → α → Prop} : sumCls (gen P) ⊆ fld P := by
  rintro x ⟨A, hA, hxA⟩
  obtain ⟨n, rfl⟩ := mem_gen'.1 hA
  exact hxA.1.2

/-- ✱93·273. \(\vdash.CʻP-pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP=sʻ\text{gen}ʻP \quad[\text{*93·271·272.*24·492}]\) -/
theorem pm93_273 {P : α → α → Prop} : fld P \ prodCls (Dcnv ʻʻ pot P) = sumCls (gen P) := by
  rw [← pm93_271]
  ext x
  constructor
  · rintro ⟨hx, h⟩
    by_contra h'
    exact h ⟨hx, h'⟩
  · intro h
    exact ⟨pm93_272 h, fun h' => h'.2 h⟩

/-- ✱93·274. \(\vdash.CʻP=sʻ\text{gen}ʻP\cup pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP \quad[\text{*24·411.*93·271·272}]\) -/
theorem pm93_274 {P : α → α → Prop} : fld P = sumCls (gen P) ∪ prodCls (Dcnv ʻʻ pot P) := by
  rw [← pm93_271]
  ext x
  constructor
  · intro hx
    by_cases h : x ∈ sumCls (gen P)
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  · rintro (h | h)
    · exact pm93_272 h
    · exact h.1

/-- ✱93·275. \(\vdash.sʻ\text{gen}ʻP\cap pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP=\Lambda \quad[\text{*93·271.*24·21}]\) -/
theorem pm93_275 {P : α → α → Prop} : sumCls (gen P) ∩ prodCls (Dcnv ʻʻ pot P) = Λ := by
  rw [← pm93_271]
  exact eq_Null fun x ⟨h1, h2⟩ => h2.2 h1

/-- ✱93·3. \(\vdash:P\in 1\rightarrow \text{Cls}.T\in \text{Potid}ʻP.\supset.\overrightarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻT=\breve{T}ʻʻ\overrightarrow{B}ʻP\) -/
theorem pm93_3 {P T : α → α → Prop} :
    P ∈ arrow one Cls ∧ T ∈ potid P → refs (minP P) (codom T) = T˘ ʻʻ refs Beg P := by
  rintro ⟨hP, hT⟩
  obtain ⟨n, rfl⟩ := mem_potid'.1 hT
  have hone := mem_arrow_one_Cls.1 (ipow_oneMany hP n)
  ext x
  rw [mem_refs_minP_ipow]
  constructor
  · rintro ⟨⟨b, hb⟩, hx⟩
    have hbc : b ∉ codom P := by
      rintro ⟨a, hab⟩
      exact hx ⟨a, by rw [ipow_succ']; exact ⟨b, hab, hb⟩⟩
    have hbd : b ∈ dom P := by
      obtain ⟨c, hc | hc⟩ := (fld_of_ipow hb).1
      · exact ⟨c, hc⟩
      · exact absurd ⟨c, hc⟩ hbc
    exact ⟨b, ⟨hbd, hbc⟩, hb⟩
  · rintro ⟨b, ⟨-, hbc⟩, hb⟩
    refine ⟨⟨b, hb⟩, ?_⟩
    rintro ⟨a, ha⟩
    rw [ipow_succ'] at ha
    obtain ⟨c, hac, hc⟩ := ha
    have e : c = b := hone c b x ⟨hc, hb⟩
    subst e
    exact hbc ⟨a, hac⟩

/-- ✱93·31. \(\vdash:P\in 1\rightarrow \text{Cls}.\supset.\breve{P}ʻʻ\overrightarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻT=\overrightarrow{\text{min}}_{P}ʻ(T\mid P)\)

**Status.** proved (reading): the right side is printed `min⃗_P'(T|P)`, which is meaningless
(`min_P` relates terms to classes, and `T|P` is a relation); PM's demonstration ends with
`min⃗_P'ᗡ'(T|P)`, and that is what is used in ✱93·33 and ✱93·4, so the right side is read
`min⃗_P'ᗡ'(T|P)`. -/
theorem pm93_31{P T : α → α → Prop} :
    P ∈ arrow one Cls → P˘ ʻʻ refs (minP P) (codom T) = refs (minP P) (codom (T ⨾ P)) := by
  intro hP
  rw [mem_arrow_one_Cls] at hP
  ext z
  constructor
  · rintro ⟨y, ⟨⟨hyT, -⟩, hy⟩, hyz⟩
    refine ⟨⟨?_, ⟨y, Or.inr hyz⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := hyT
      exact ⟨x, y, hx, hyz⟩
    · rintro ⟨w, hw, hwz⟩
      have e : w = y := hP w y z ⟨hwz, hyz⟩
      subst e
      exact hy ((img_cnv_codom P T).symm ▸ hw)
  · rintro ⟨⟨⟨x, y, hxy, hyz⟩, -⟩, hz⟩
    refine ⟨y, ⟨⟨⟨x, hxy⟩, ⟨z, Or.inl hyz⟩⟩, ?_⟩, hyz⟩
    intro hy
    exact hz ⟨y, (img_cnv_codom P T) ▸ hy, hyz⟩

/-- ✱93·32. \[\begin{align}&\vdash\vdash\colon\ldotp P\in 1\rightarrow \text{Cls}.\supset:\alpha\in \text{gen}ʻP.\equiv.(\exists T).T\in \text{Potid}ʻP.\alpha=\breve{T}ʻʻ\overrightarrow{B}ʻP\\ &[\text{*93·2·3}]\end{align}\] -/
theorem pm93_32 {P : α → α → Prop} {A : Set α} :
    P ∈ arrow one Cls → (A ∈ gen P ↔ ∃ T, T ∈ potid P ∧ A = T˘ ʻʻ refs Beg P) := by
  intro hP
  rw [gen, mem_minImg]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT, pm93_3 ⟨hP, hT⟩⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, hT, (pm93_3 ⟨hP, hT⟩).symm⟩

/-- ✱93·33. \[\begin{align}&\vdash\vdash:P\in 1\rightarrow \text{Cls}.\alpha\in \text{gen}ʻP.\supset.\breve{P}ʻʻ\alpha\in \text{gen}ʻP\\ &[\text{*93·2·31.*91·28·281}]\end{align}\] -/
theorem pm93_33 {P : α → α → Prop} {A : Set α} :
    P ∈ arrow one Cls ∧ A ∈ gen P → P˘ ʻʻ A ∈ gen P := by
  rintro ⟨hP, hA⟩
  rw [gen, mem_minImg] at hA ⊢
  obtain ⟨T, hT, rfl⟩ := hA
  exact ⟨T ⨾ P, pot_sub_potid P (pm91_28 hT), pm93_31 hP⟩

/-- ✱93·34. \(\vdash:P\in 1\rightarrow \text{Cls}.\supset.\breve{P}ʻʻ\overrightarrow{B}ʻP\in \text{gen}ʻP \quad[\text{*93·22·33}]\) -/
theorem pm93_34 {P : α → α → Prop} : P ∈ arrow one Cls → P˘ ʻʻ refs Beg P ∈ gen P :=
  fun hP => pm93_33 ⟨hP, pm93_22⟩

/-- ✱93·35. \(\vdash:P\in 1\rightarrow \text{Cls}.\alpha\in \text{gen}ʻP.T\in \text{Potid}ʻP.\supset.\breve{T}ʻʻ\alpha\in \text{gen}ʻP\) -/
theorem pm93_35 {P T : α → α → Prop} {A : Set α} :
    (P ∈ arrow one Cls ∧ A ∈ gen P) ∧ T ∈ potid P → T˘ ʻʻ A ∈ gen P := by
  rintro ⟨⟨hP, hA⟩, hT⟩
  obtain ⟨U, hU, rfl⟩ := (pm93_32 hP).1 hA
  refine (pm93_32 hP).2 ⟨U ⨾ T, pm91_341 ⟨hU, hT⟩, ?_⟩
  rw [img_comp, cnv_comp]

/-- ✱93·36. \(\vdash:P\in 1\rightarrow \text{Cls}.\supset.sʻ\text{gen}ʻP=\breve{P}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻP\) -/
theorem pm93_36 {P : α → α → Prop} :
    P ∈ arrow one Cls → sumCls (gen P) = ancCnv P ʻʻ refs Beg P := by
  intro hP
  ext x
  constructor
  · rintro ⟨A, hA, hxA⟩
    obtain ⟨T, hT, rfl⟩ := (pm93_32 hP).1 hA
    obtain ⟨b, hb, hbx⟩ := hxA
    exact ⟨b, hb, pm91_58 hT b x hbx⟩
  · rintro ⟨b, hb, hbx⟩
    obtain ⟨n, hn⟩ := anc_iff_ipow.1 (show anc P b x from hbx)
    exact ⟨_, (pm93_32 hP).2 ⟨ipow P n, ipow_mem_potid P n, rfl⟩, b, hb, hn⟩

/-- ✱93·37. \(\vdash:P\in 1\rightarrow \text{Cls}.\supset.CʻP=\breve{P}_{\unicode{x2217}}ʻʻ\overrightarrow{B}ʻP\cup pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP \quad[\text{*93·274·36}]\) -/
theorem pm93_37 {P : α → α → Prop} :
    P ∈ arrow one Cls → fld P = ancCnv P ʻʻ refs Beg P ∪ prodCls (Dcnv ʻʻ pot P) := by
  intro hP
  rw [← pm93_36 hP]
  exact pm93_274

/-- ✱93·38. \(\vdash\colon\ldotp P\in 1\rightarrow \text{Cls}.\supset:x\in pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP.\equiv.\overrightarrow{P}_{\unicode{x2217}}ʻx\subset \text{ᗡ}ʻP.x\in CʻP\) -/
theorem pm93_38 {P : α → α → Prop} {x : α} :
    P ∈ arrow one Cls → (x ∈ prodCls (Dcnv ʻʻ pot P) ↔ refs (anc P) x ⊆ codom P ∧ x ∈ fld P) := by
  intro hP
  rw [mem_p_pot]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro y hy
      obtain ⟨k, hk⟩ := anc_iff_ipow.1 (show anc P y x from hy)
      obtain ⟨a, ha⟩ := h k
      rw [ipow_succ'] at ha
      obtain ⟨c, hac, hc⟩ := ha
      have e : c = y := mem_arrow_one_Cls.1 (ipow_oneMany hP k) c y x ⟨hc, hk⟩
      subst e
      exact ⟨a, hac⟩
    · obtain ⟨a, ha⟩ := h 0
      rw [ipow_one] at ha
      exact ⟨a, Or.inr ha⟩
  · rintro ⟨h, hx⟩ n
    induction n with
    | zero =>
      obtain ⟨a, ha⟩ := h (show anc P x x from anc_refl hx)
      exact ⟨a, by rw [ipow_one]; exact ha⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨a, ha⟩ := h (show anc P y x from anc_iff_ipow.2 ⟨n + 1, hy⟩)
      exact ⟨a, by rw [ipow_succ']; exact ⟨y, ha, hy⟩⟩

/-- ✱93·381. \(\vdash\colon\ldotp P \in \text{Cls} \rightarrow 1.\supset:x \in pʻ\text{ᗡ}ʻʻ\text{Pot}ʻ\breve{P}.\equiv.\overleftarrow{P}_{\unicode{x2217}}ʻx\subset \text{D}ʻP. x\in CʻP\) -/
theorem pm93_381 {P : α → α → Prop} {x : α} :
    P ∈ arrow Cls one →
      (x ∈ prodCls (Dcnv ʻʻ pot P˘) ↔ rels (anc P) x ⊆ dom P ∧ x ∈ fld P) := by
  intro hP
  have hP' : P˘ ∈ arrow one Cls :=
    mem_arrow_one_Cls.2 fun a b c h => mem_arrow_Cls_one.1 hP c a b ⟨h.1, h.2⟩
  have h := pm93_38 (P := P˘) (x := x) hP'
  rw [pm90_132, fld_cnv] at h
  exact h

/-- ✱93·382. \[\begin{align}\vdash\colon\ldotp &P \in 1 \rightarrow 1.\supset : x \in pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP \cap pʻ\text{ᗡ}ʻʻ\text{Pot}ʻ\breve{P}. \equiv .\\ &\overrightarrow{P}_{\unicode{x2217}}ʻx \cup \overleftarrow{P}_{\unicode{x2217}}ʻx \subset \text{D}ʻP \cap \text{ᗡ}ʻP. x \in CʻP \quad[\text{*93·38·381·261. *90·31·311}]\end{align}\] -/
theorem pm93_382 {P : α → α → Prop} {x : α} :
    P ∈ arrow one one →
      (x ∈ prodCls (Dcnv ʻʻ pot P) ∩ prodCls (Dcnv ʻʻ pot P˘) ↔
        refs (anc P) x ∪ rels (anc P) x ⊆ dom P ∩ codom P ∧ x ∈ fld P) := by
  intro hP
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hP
  rw [Set.mem_inter_iff, pm93_38 (mem_arrow_one_Cls.2 h1), pm93_381 (mem_arrow_Cls_one.2 h2)]
  constructor
  · rintro ⟨⟨hc, hx⟩, ⟨hd, -⟩⟩
    refine ⟨?_, hx⟩
    rintro y (hy | hy)
    · refine ⟨?_, hc hy⟩
      rcases anc_iff_po.1 (show anc P y x from hy) with ⟨rfl, -⟩ | h
      · exact hd (anc_refl hx)
      · rw [po_eq_comp_anc] at h
        obtain ⟨a, hya, -⟩ := h
        exact ⟨a, hya⟩
    · refine ⟨hd hy, ?_⟩
      rcases anc_iff_po.1 (show anc P x y from hy) with ⟨rfl, -⟩ | h
      · exact hc (anc_refl hx)
      · rw [po_eq_anc_comp] at h
        obtain ⟨b, -, hby⟩ := h
        exact ⟨b, hby⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨fun y hy => (h (Or.inl hy)).2, hx⟩, ⟨fun y hy => (h (Or.inr hy)).1, hx⟩⟩

/-- ✱93·4. \(\vdash: P \in 1 \rightarrow \text{Cls}.\text{ᗡ}ʻP \subset \text{D}ʻP. \exists !\overrightarrow{B}ʻP. T \in \text{Potid}ʻP.\supset.\exists !\overrightarrow{\text{min}}_{p}ʻ\text{ᗡ}ʻT\)

**Status.** proved (reading): transcription error of the e-text, which prints `min_p` (lower-case
`p`) in the consequent; PM's `min_P` is meant, as the hypotheses (all about `P`) and the use in
✱93·41 show. -/
theorem pm93_4 {P T : α → α → Prop} :
    ((P ∈ arrow one Cls ∧ codom P ⊆ dom P) ∧ (refs Beg P).Nonempty) ∧ T ∈ potid P →
      (refs (minP P) (codom T)).Nonempty := by
  rintro ⟨⟨⟨hP, hcd⟩, ⟨b, hb⟩⟩, hT⟩
  rw [pm93_3 ⟨hP, hT⟩]
  obtain ⟨n, rfl⟩ := mem_potid'.1 hT
  have hbd : b ∈ dom (ipow P n) := (dom_ipow hcd n).symm ▸ hb.1
  obtain ⟨z, hz⟩ := hbd
  exact ⟨z, b, hb, hz⟩

/-- ✱93·41. \[\begin{align}&\vdash : P \in 1 \rightarrow \text{Cls}.\text{ᗡ}ʻP \subset \text{D}ʻP. \exists ! \overrightarrow{B}ʻP . \supset . \text{gen}ʻP \in \text{Cls ex}^{2}\, \text{excl}\\ &[\text{*93·2·4·25 .*84·13 .*24·63}]\end{align}\] -/
theorem pm93_41 {P : α → α → Prop} :
    (P ∈ arrow one Cls ∧ codom P ⊆ dom P) ∧ (refs Beg P).Nonempty → gen P ∈ ClsEx2excl := by
  intro h
  refine ⟨pm93_25, ?_⟩
  intro hΛ
  have hΛ' : (Λ : Set α) ∈ gen P := hΛ
  rw [gen, mem_minImg] at hΛ'
  obtain ⟨T, hT, e⟩ := hΛ'
  obtain ⟨x, hx⟩ := pm93_4 ⟨h, hT⟩
  rw [← e, Null_eq_empty] at hx
  exact hx

/-- ✱93·412. \(\vdash . \breve{P}ʻʻpʻ\text{ᗡ}ʻʻ\text{Pot}ʻP \subset pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP\) -/
theorem pm93_412 {P : α → α → Prop} :
    P˘ ʻʻ prodCls (Dcnv ʻʻ pot P) ⊆ prodCls (Dcnv ʻʻ pot P) := by
  rintro z ⟨y, hy, hyz⟩
  rw [mem_p_pot] at hy ⊢
  intro n
  cases n with
  | zero => exact ⟨y, by rw [ipow_one]; exact hyz⟩
  | succ n =>
    rw [codom_ipow_succ]
    exact ⟨y, hy n, hyz⟩

/-- ✱93·42. \(\vdash : P \in 1 \rightarrow \text{Cls} . \supset . \breve{P}ʻʻpʻ\text{ᗡ}ʻʻ\text{Pot}ʻP = pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP\) -/
theorem pm93_42 {P : α → α → Prop} :
    P ∈ arrow one Cls → P˘ ʻʻ prodCls (Dcnv ʻʻ pot P) = prodCls (Dcnv ʻʻ pot P) := by
  intro hP
  refine Set.Subset.antisymm pm93_412 ?_
  intro x hx
  have hx' := mem_p_pot.1 hx
  obtain ⟨y, hy⟩ := hx' 0
  rw [ipow_one] at hy
  refine ⟨y, mem_p_pot.2 fun n => ?_, hy⟩
  obtain ⟨w, hw⟩ := hx' (n + 1)
  rw [ipow_succ] at hw
  obtain ⟨v, hwv, hvx⟩ := hw
  have e : v = y := mem_arrow_one_Cls.1 hP v y x ⟨hvx, hy⟩
  subst e
  exact ⟨w, hwv⟩

/-- ✱93·431. \(\vdash . pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP = pʻ\text{ᗡ}ʻʻ \mid Pʻʻ\text{Pot}ʻP\) -/
theorem pm93_431 {P : α → α → Prop} :
    prodCls (Dcnv ʻʻ pot P) = prodCls (Dcnv ʻʻ relProdR P ʻʻ pot P) := by
  ext x
  rw [mem_p_pot, mem_prodCls_Dcnv]
  constructor
  · rintro h T ⟨Q, hQ, hT⟩
    rw [relProdR_apply] at hT
    subst hT
    obtain ⟨n, hn⟩ := mem_pot'.1 (pm91_282 hQ)
    rw [hn]
    exact h n
  · intro h n
    have h' : x ∈ codom (ipow P (n + 2)) := by
      refine h _ ⟨ipow P (n + 1), ipow_succ_mem_pot P n, ?_⟩
      rw [relProdR_apply, ← ipow_succ]
    exact codom_ipow_succ_sub P _ h'

/-- ✱93·5. \(\vdash:T\in \text{Potid}ʻP.\supset.\overrightarrow{P}_{\text{ts}}ʻT=\overrightarrow{P}_{\text{st}}ʻT=T\mid ʻʻ\text{Potid}ʻP=\mid Tʻʻ\text{Potid}ʻP\) -/
theorem pm93_5 {P T : α → α → Prop} :
    T ∈ potid P →
      (refs (Rts P) T = refs (Rst P) T ∧ refs (Rst P) T = relProdL T ʻʻ potid P) ∧
        relProdL T ʻʻ potid P = relProdR T ʻʻ potid P := by
  intro hT
  obtain ⟨m, rfl⟩ := mem_potid'.1 hT
  have hS : ∀ X : α → α → Prop, (∃ k, X = ipow P (m + k)) ↔ (∃ k, X = ipow P (k + m)) := by
    intro X
    simp only [Nat.add_comm m]
  have e1 : refs (Rts P) (ipow P m) = {X | ∃ k, X = ipow P (m + k)} := by
    ext X
    show Rts P X (ipow P m) ↔ ∃ k, X = ipow P (m + k)
    rw [Rts_iff]
    simp only [ipow_add]
  have e2 : refs (Rst P) (ipow P m) = {X | ∃ k, X = ipow P (m + k)} := by
    ext X
    show Rst P X (ipow P m) ↔ ∃ k, X = ipow P (m + k)
    rw [Rst_iff, hS]
    have key : ∀ n, npow P n ⨾ ipow P m = ipow P (n + m) := by
      intro n
      cases n with
      | zero => rw [npow_zero_comp, Nat.zero_add]
      | succ n => rw [← ipow_succ_eq, ipow_mul]
    simp only [key]
  have e3 : relProdL (ipow P m) ʻʻ potid P = {X | ∃ k, X = ipow P (m + k)} := by
    ext X
    constructor
    · rintro ⟨Y, hY, hX⟩
      rw [relProdL_apply] at hX
      obtain ⟨k, rfl⟩ := mem_potid'.1 hY
      exact ⟨k, hX.trans (ipow_mul P m k)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨ipow P k, ipow_mem_potid P k, (ipow_mul P m k).symm⟩
  have e4 : relProdR (ipow P m) ʻʻ potid P = {X | ∃ k, X = ipow P (m + k)} := by
    ext X
    show (∃ Y, Y ∈ potid P ∧ relProdR (ipow P m) X Y) ↔ ∃ k, X = ipow P (m + k)
    rw [hS]
    constructor
    · rintro ⟨Y, hY, hX⟩
      rw [relProdR_apply] at hX
      obtain ⟨k, rfl⟩ := mem_potid'.1 hY
      exact ⟨k, hX.trans (ipow_mul P k m)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨ipow P k, ipow_mem_potid P k, (ipow_mul P k m).symm⟩
  rw [e1, e2, e3, e4]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- ✱93·51. \(\vdash:T\in \text{Pot}ʻP.\supset.\text{Pot}ʻT\subset \overrightarrow{P}_{\text{ts}}ʻT\subset \text{Pot}ʻP\) -/
theorem pm93_51 {P T : α → α → Prop} :
    T ∈ pot P → pot T ⊆ refs (Rts P) T ∧ refs (Rts P) T ⊆ pot P := by
  intro hT
  refine ⟨?_, fun Q hQ => pm91_43 ⟨hT, hQ⟩⟩
  obtain ⟨k, rfl⟩ := mem_pot'.1 hT
  intro X hX
  obtain ⟨j, rfl⟩ := (Rts_iff _ X _).1 (show Rts (ipow P (k + 1)) X (ipow P (k + 1)) from hX)
  refine (Rts_iff P _ _).2 ⟨(k + 1) * j, ?_⟩
  conv_lhs => rw [show npow (ipow P (k + 1)) j = npow (npow P (k + 1)) j by rw [ipow_succ_eq]]
  rw [npow_mul]

/-- ✱93·52. \(\vdash:T\in \text{Pot}ʻP.\supset.pʻ\text{ᗡ}ʻʻ\text{Pot}ʻT=pʻ\text{ᗡ}ʻʻ\overrightarrow{P}_{\text{ts}}ʻT=pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP\) -/
theorem pm93_52 {P T : α → α → Prop} :
    T ∈ pot P →
      prodCls (Dcnv ʻʻ pot T) = prodCls (Dcnv ʻʻ refs (Rts P) T) ∧
        prodCls (Dcnv ʻʻ refs (Rts P) T) = prodCls (Dcnv ʻʻ pot P) := by
  intro hT
  obtain ⟨k, rfl⟩ := mem_pot'.1 hT
  have hΦ : ∀ x : α, x ∈ prodCls (Dcnv ʻʻ pot P) ↔ ∀ n, x ∈ codom (ipow P (n + 1)) :=
    fun x => mem_p_pot
  have hR : ∀ x : α, x ∈ prodCls (Dcnv ʻʻ refs (Rts P) (ipow P (k + 1))) ↔
      ∀ n, x ∈ codom (ipow P (n + 1)) := by
    intro x
    rw [mem_prodCls_Dcnv]
    constructor
    · intro h n
      have h' := h _ ((Rts_iff P _ _).2 ⟨n, rfl⟩)
      rw [← ipow_add] at h'
      exact codom_ipow_mono P (by omega) h'
    · intro h X hX
      obtain ⟨n, rfl⟩ := (Rts_iff P X _).1 hX
      rw [← ipow_add, Nat.add_right_comm]
      exact h _
  have hT' : ∀ x : α, x ∈ prodCls (Dcnv ʻʻ pot (ipow P (k + 1))) ↔
      ∀ n, x ∈ codom (ipow P (n + 1)) := by
    intro x
    have key : ∀ j, ipow (ipow P (k + 1)) (j + 1) = ipow P ((k * (j + 1) + j) + 1) := by
      intro j
      rw [ipow_succ_eq, ipow_succ_eq, ipow_succ_eq, npow_mul]
      congr 1
      rw [Nat.succ_mul, Nat.add_assoc]
    rw [mem_p_pot]
    simp only [key]
    constructor
    · intro h n
      exact codom_ipow_mono P (by
        have : n ≤ k * (n + 1) + n := Nat.le_add_left n _
        omega) (h n)
    · intro h j
      exact h _
  refine ⟨Set.ext fun x => (hT' x).trans (hR x).symm, Set.ext fun x => (hR x).trans (hΦ x).symm⟩

/-- ✱93·53. \(\vdash:S,\,T\in \text{Pot}ʻP.xSx.\supset.(\exists y).y(S\mid T)x\) -/
theorem pm93_53 {P S T : α → α → Prop} {x : α} :
    Mem2 S T (pot P) ∧ S x x → ∃ y, (S ⨾ T) y x := by
  rintro ⟨⟨hS, hT⟩, hx⟩
  obtain ⟨m, rfl⟩ := mem_pot'.1 hS
  obtain ⟨n, rfl⟩ := mem_pot'.1 hT
  rw [ipow_succ_eq] at hx ⊢
  obtain ⟨w, hwx, hw⟩ := cycle_pred hx (n + 1)
  exact ⟨w, w, hw, by rw [ipow_succ_eq]; exact hwx⟩

/-- ✱93·54. \(\vdash:S\in \text{Pot}ʻP.xSx.\supset.x\in pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP\) -/
theorem pm93_54 {P S : α → α → Prop} {x : α} :
    S ∈ pot P ∧ S x x → x ∈ prodCls (Dcnv ʻʻ pot P) := by
  rintro ⟨hS, hx⟩
  obtain ⟨m, rfl⟩ := mem_pot'.1 hS
  rw [ipow_succ_eq] at hx
  rw [mem_p_pot]
  intro n
  obtain ⟨w, hwx, -⟩ := cycle_pred hx (n + 1)
  exact ⟨w, by rw [ipow_succ_eq]; exact hwx⟩

/-- ✱93·55. \(\vdash.Cʻ(P_{\text{po}}\dot{\cap}I)\subset pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP\) -/
theorem pm93_55 {P : α → α → Prop} : fld (po P ⩀ I) ⊆ prodCls (Dcnv ʻʻ pot P) := by
  rintro x ⟨y, ⟨h, e⟩ | ⟨h, e⟩⟩
  · have e' : x = y := e
    subst e'
    obtain ⟨m, hm⟩ := po_iff_ipow.1 h
    exact pm93_54 ⟨ipow_succ_mem_pot P m, hm⟩
  · have e' : y = x := e
    subst e'
    obtain ⟨m, hm⟩ := po_iff_ipow.1 h
    exact pm93_54 ⟨ipow_succ_mem_pot P m, hm⟩

/-- ✱93·56. \(\vdash:\dot{\exists}!(P_{\text{po}}\dot{\cap}I).\supset.\exists !pʻ\text{ᗡ}ʻʻ\text{Pot}ʻP\) -/
theorem pm93_56 {P : α → α → Prop} : rEx (po P ⩀ I) → (prodCls (Dcnv ʻʻ pot P)).Nonempty := by
  rintro ⟨x, y, h⟩
  exact ⟨x, pm93_55 ⟨y, Or.inl h⟩⟩

end PrincipiaMathematica
