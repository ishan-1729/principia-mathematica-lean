import PrincipiaMathematica.Defs.Part3

/-!
# Part III, Section C: Finite and infinite

Volume 2. Numbers: ✱122, ✱123, ✱124, ✱125, ✱126.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

/-! ## Auxiliary lemmas

Private lemmas used in the proofs below: progressions are the successor relations of injective
sequences `ℕ → α`, `ℵ₀` is the class of countably infinite classes, the inductive cardinals are
the classes `cardN β k` of `k`-membered classes, and comparisons of homogeneous cardinals are
embeddings. -/

section Aux

open Function

variable {α : Type*} {β : Type*} {γ : Type*}

/-! ### Progressions as injective sequences -/

/-- The successor relation of a sequence `f`: `f n` to `f (n + 1)`. -/
private def SeqRel (f : ℕ → α) : α → α → Prop := fun x y => ∃ n, x = f n ∧ y = f (n + 1)

private theorem seqRel_apply (f : ℕ → α) (n : ℕ) : SeqRel f (f n) (f (n + 1)) := ⟨n, rfl, rfl⟩

private theorem seqRel_iff {f : ℕ → α} (hf : Injective f) {m n : ℕ} :
    SeqRel f (f m) (f n) ↔ n = m + 1 := by
  constructor
  · rintro ⟨k, hk, hn⟩
    rw [hf hn, hf hk]
  · rintro rfl
    exact seqRel_apply f m

private theorem dom_seqRel (f : ℕ → α) : dom (SeqRel f) = Set.range f := by
  ext x
  constructor
  · rintro ⟨y, n, rfl, -⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, seqRel_apply f n⟩

private theorem codom_seqRel (f : ℕ → α) :
    codom (SeqRel f) = Set.range (fun n => f (n + 1)) := by
  ext y
  constructor
  · rintro ⟨x, n, -, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, seqRel_apply f n⟩

private theorem fld_seqRel (f : ℕ → α) : fld (SeqRel f) = Set.range f := by
  ext x
  constructor
  · rintro ⟨y, ⟨n, rfl, -⟩ | ⟨n, -, rfl⟩⟩
    · exact ⟨n, rfl⟩
    · exact ⟨n + 1, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, Or.inl (seqRel_apply f n)⟩

private theorem rtg_seqRel {f : ℕ → α} (hf : Injective f) {m : ℕ} {y : α} :
    Relation.ReflTransGen (SeqRel f) (f m) y ↔ ∃ n, m ≤ n ∧ y = f n := by
  constructor
  · intro hr
    induction hr with
    | refl => exact ⟨m, le_rfl, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨n, hn, rfl⟩ := ih
      obtain ⟨k, hk, rfl⟩ := hbc
      rw [hf hk] at hn
      exact ⟨k + 1, by omega, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    induction n, hn using Nat.le_induction with
    | base => exact Relation.ReflTransGen.refl
    | succ k _ ih => exact ih.tail (seqRel_apply f k)

private theorem anc_seqRel {f : ℕ → α} (hf : Injective f) {x y : α} :
    anc (SeqRel f) x y ↔ ∃ m n, m ≤ n ∧ x = f m ∧ y = f n := by
  rw [anc_iff_reflTransGen, fld_seqRel]
  constructor
  · rintro ⟨⟨m, rfl⟩, h⟩
    obtain ⟨n, hn, rfl⟩ := (rtg_seqRel hf).1 h
    exact ⟨m, n, hn, rfl, rfl⟩
  · rintro ⟨m, n, hmn, rfl, rfl⟩
    exact ⟨⟨m, rfl⟩, (rtg_seqRel hf).2 ⟨n, hmn, rfl⟩⟩

private theorem anc_seqRel' {f : ℕ → α} (hf : Injective f) {m n : ℕ} :
    anc (SeqRel f) (f m) (f n) ↔ m ≤ n := by
  rw [anc_seqRel hf]
  constructor
  · rintro ⟨a, b, h, ha, hb⟩
    rw [hf ha, hf hb]
    exact h
  · intro h
    exact ⟨m, n, h, rfl, rfl⟩

private theorem po_seqRel {f : ℕ → α} (hf : Injective f) {x y : α} :
    po (SeqRel f) x y ↔ ∃ m n, m < n ∧ x = f m ∧ y = f n := by
  rw [po_iff_transGen, Relation.TransGen.head'_iff]
  constructor
  · rintro ⟨z, ⟨m, rfl, rfl⟩, h⟩
    obtain ⟨n, hn, rfl⟩ := (rtg_seqRel hf).1 h
    exact ⟨m, n, by omega, rfl, rfl⟩
  · rintro ⟨m, n, hmn, rfl, rfl⟩
    exact ⟨f (m + 1), seqRel_apply f m, (rtg_seqRel hf).2 ⟨n, hmn, rfl⟩⟩

private theorem po_seqRel' {f : ℕ → α} (hf : Injective f) {m n : ℕ} :
    po (SeqRel f) (f m) (f n) ↔ m < n := by
  rw [po_seqRel hf]
  constructor
  · rintro ⟨a, b, h, ha, hb⟩
    rw [hf ha, hf hb]
    exact h
  · intro h
    exact ⟨m, n, h, rfl, rfl⟩

private theorem beg_seqRel {f : ℕ → α} (hf : Injective f) {x : α} :
    Beg x (SeqRel f) ↔ x = f 0 := by
  rw [Beg_apply, dom_seqRel, codom_seqRel]
  constructor
  · rintro ⟨⟨n, rfl⟩, h⟩
    cases n with
    | zero => rfl
    | succ k => exact absurd ⟨k, rfl⟩ h
  · rintro rfl
    refine ⟨⟨0, rfl⟩, ?_⟩
    rintro ⟨k, hk⟩
    exact absurd (hf hk) (by omega)

private theorem desc_beg_seqRel {f : ℕ → α} (hf : Injective f) (ψ : α → Prop) :
    Desc Beg (SeqRel f) ψ ↔ ψ (f 0) :=
  TheIs_iff_of_unique (fun _ => beg_seqRel hf)

private theorem seqRel_oneone {f : ℕ → α} (hf : Injective f) : SeqRel f ∈ arrow one one := by
  rw [mem_arrow_one_one]
  refine ⟨?_, ?_⟩
  · rintro x y z ⟨⟨m, rfl, hz⟩, ⟨n, rfl, hz'⟩⟩
    have := hf (hz.symm.trans hz')
    rw [show m = n by omega]
  · rintro x y z ⟨⟨m, rfl, rfl⟩, ⟨n, hmn, rfl⟩⟩
    rw [hf hmn]

private theorem seqRel_mem_prog {f : ℕ → α} (hf : Injective f) : SeqRel f ∈ Prog := by
  refine ⟨seqRel_oneone hf, ?_⟩
  show Desc Beg (SeqRel f) (fun b => dom (SeqRel f) = rels (anc (SeqRel f)) b)
  rw [desc_beg_seqRel hf, dom_seqRel]
  ext y
  show y ∈ Set.range f ↔ anc (SeqRel f) (f 0) y
  rw [anc_seqRel hf]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨0, n, Nat.zero_le _, rfl, rfl⟩
  · rintro ⟨m, n, -, -, rfl⟩
    exact ⟨n, rfl⟩

private theorem exists_seq_of_prog {R : α → α → Prop} (h : R ∈ Prog) :
    ∃ f : ℕ → α, Injective f ∧ R = SeqRel f := by
  classical
  obtain ⟨h11, b, hb, hdom⟩ := h
  obtain ⟨hinj, hfun⟩ := mem_arrow_one_one.1 h11
  have hbB : Beg b R := (hb b).2 rfl
  have hex : ∀ x, ∃ y, x ∈ dom R → R x y := by
    intro x
    by_cases hx : x ∈ dom R
    · obtain ⟨y, hy⟩ := hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨x, fun h => absurd h hx⟩
  choose g hg using hex
  let f : ℕ → α := fun n => g^[n] b
  have hfs : ∀ n, f (n + 1) = g (f n) := fun n => Function.iterate_succ_apply' g n b
  have hanc : ∀ n, anc R b (f n) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨y, hy⟩ := hbB.1
      exact anc_iff_reflTransGen.2 ⟨⟨y, Or.inl hy⟩, Relation.ReflTransGen.refl⟩
    | succ n ih =>
      have hd : f n ∈ dom R := by rw [hdom]; exact ih
      have hr := hg _ hd
      rw [← hfs] at hr
      obtain ⟨hfl, hrt⟩ := anc_iff_reflTransGen.1 ih
      exact anc_iff_reflTransGen.2 ⟨hfl, hrt.tail hr⟩
  have hstep : ∀ n, R (f n) (f (n + 1)) := by
    intro n
    rw [hfs]
    exact hg _ (by rw [hdom]; exact hanc n)
  have hne : ∀ m k, f m ≠ f (m + k + 1) := by
    intro m
    induction m with
    | zero =>
      intro k h
      apply hbB.2
      refine ⟨f k, ?_⟩
      have h' : b = f (k + 1) := by rw [show k + 1 = 0 + k + 1 by omega]; exact h
      rw [h']
      exact hstep k
    | succ m ih =>
      intro k h
      apply ih k
      apply hinj _ _ (f (m + 1))
      refine ⟨hstep m, ?_⟩
      rw [h, show m + 1 + k + 1 = m + k + 1 + 1 by omega]
      exact hstep _
  have hfinj : Injective f := by
    intro m n h
    rcases lt_trichotomy m n with hlt | heq | hgt
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      exact absurd h (hne m k)
    · exact heq
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
      exact absurd h.symm (hne n k)
  refine ⟨f, hfinj, ?_⟩
  have hrange : ∀ x, Relation.ReflTransGen R b x → ∃ n, x = f n := by
    intro x hx
    induction hx with
    | refl => exact ⟨0, rfl⟩
    | tail _ hcd ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, hfun _ _ _ ⟨hcd, hstep n⟩⟩
  funext x y
  apply propext
  constructor
  · intro hxy
    have hx : x ∈ rels (anc R) b := by rw [← hdom]; exact ⟨y, hxy⟩
    obtain ⟨n, rfl⟩ := hrange x (anc_iff_reflTransGen.1 hx).2
    exact ⟨n, rfl, hfun _ _ _ ⟨hxy, hstep n⟩⟩
  · rintro ⟨n, rfl, rfl⟩
    exact hstep n

private theorem prog_iff_seq {R : α → α → Prop} :
    R ∈ Prog ↔ ∃ f : ℕ → α, Injective f ∧ R = SeqRel f :=
  ⟨exists_seq_of_prog, fun ⟨_, hf, e⟩ => e ▸ seqRel_mem_prog hf⟩

/-- `α ∈ ℵ₀` iff `α` is the range of an injective sequence. -/
private theorem mem_aleph0_iff {A : Set α} :
    A ∈ aleph0 ↔ ∃ f : ℕ → α, Injective f ∧ A = Set.range f := by
  constructor
  · rintro ⟨R, hR, hA⟩
    obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 hR
    exact ⟨f, hf, by rw [← dom_seqRel f]; exact hA⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨SeqRel f, seqRel_mem_prog hf, (dom_seqRel f).symm⟩

private theorem mem_aleph0_iff_equiv {A : Set α} : A ∈ aleph0 ↔ Nonempty (ℕ ≃ A) := by
  rw [mem_aleph0_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨Equiv.ofInjective f hf⟩
  · rintro ⟨e⟩
    refine ⟨fun n => (e n : α), Subtype.val_injective.comp e.injective, ?_⟩
    ext x
    exact ⟨fun hx => ⟨e.symm ⟨x, hx⟩, by simp⟩, fun ⟨n, hn⟩ => hn ▸ (e n).2⟩

private theorem aleph0_of_sm {A : Set α} {B : Set β} (hA : A ∈ aleph0) (h : sm A B) :
    B ∈ aleph0 := by
  obtain ⟨e⟩ := mem_aleph0_iff_equiv.1 hA
  obtain ⟨e'⟩ := sm_iff_nonempty_equiv.1 h
  exact mem_aleph0_iff_equiv.2 ⟨e.trans e'⟩

private theorem sm_of_aleph0 {A : Set α} {B : Set β} (hA : A ∈ aleph0) (hB : B ∈ aleph0) :
    sm A B := by
  obtain ⟨e⟩ := mem_aleph0_iff_equiv.1 hA
  obtain ⟨e'⟩ := mem_aleph0_iff_equiv.1 hB
  exact sm_iff_nonempty_equiv.2 ⟨e.symm.trans e'⟩

private theorem aleph0_nonempty_iff : (aleph0 : Set (Set α)).Nonempty ↔ Infinite α := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨f, hf, -⟩ := mem_aleph0_iff.1 hA
    exact Infinite.of_injective f hf
  · intro h
    exact ⟨_, mem_aleph0_iff.2 ⟨Infinite.natEmbedding α, (Infinite.natEmbedding α).injective, rfl⟩⟩

private theorem infinite_of_aleph0 {A : Set α} (hA : A ∈ aleph0) : A.Infinite := by
  obtain ⟨f, hf, rfl⟩ := mem_aleph0_iff.1 hA
  exact Set.infinite_range_of_injective hf

private theorem infinite_of_prog {R : α → α → Prop} (h : R ∈ Prog) : Infinite α := by
  obtain ⟨f, hf, -⟩ := prog_iff_seq.1 h
  exact Infinite.of_injective f hf

/-! ### Finite cardinals -/

/-- The class of the `k`-membered classes of `β`-things. -/
private def cardN (β : Type*) (k : ℕ) : Set (Set β) := {ξ | ξ.Finite ∧ ξ.ncard = k}

private theorem sm_iff_of_finite {A : Set α} {B : Set β} (hA : A.Finite) :
    sm A B ↔ B.Finite ∧ A.ncard = B.ncard := by
  rw [sm_iff_nonempty_equiv]
  have : Finite A := hA.to_subtype
  constructor
  · rintro ⟨e⟩
    have hB : Finite B := Finite.of_equiv _ e
    exact ⟨Set.toFinite B, by rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_congr e]⟩
  · rintro ⟨hB, h⟩
    have : Finite B := hB.to_subtype
    exact Finite.card_eq.1 (by rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, h])

private theorem nc_eq_cardN {A : Set β} (hA : A.Finite) : nc γ A = cardN γ A.ncard := by
  ext ξ
  rw [mem_nc]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (sm_iff_of_finite hA).1 (sm_symm h)
    exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact sm_symm ((sm_iff_of_finite hA).2 ⟨h1, h2.symm⟩)

private theorem n₀c_eq_cardN {A : Set α} (hA : A.Finite) : n₀c A = cardN α A.ncard := by
  rw [n₀c_eq_nc, nc_eq_cardN hA]

private theorem cardN_nonempty_of_infinite [Infinite β] (k : ℕ) : (cardN β k).Nonempty := by
  obtain ⟨t, -, ht, hk⟩ := (Set.infinite_univ (α := β)).exists_subset_ncard_eq k
  exact ⟨t, ht, hk⟩

private theorem cardN_eq_n₀c {B : Set β} (hB : B ∈ cardN β k) : cardN β k = n₀c B := by
  rw [n₀c_eq_cardN hB.1, hB.2]

private theorem cardN_inj {m n : ℕ} (hm : (cardN β m).Nonempty) (h : cardN β m = cardN β n) :
    m = n := by
  obtain ⟨A, hA, rfl⟩ := hm
  have : A ∈ cardN β n := h ▸ (⟨hA, rfl⟩ : A ∈ cardN β A.ncard)
  exact this.2

private theorem cardN_mono_nonempty {m n : ℕ} (hmn : m ≤ n) (h : (cardN β n).Nonempty) :
    (cardN β m).Nonempty := by
  obtain ⟨A, hA, rfl⟩ := h
  obtain ⟨t, hts, hk⟩ := Set.exists_subset_card_eq (s := A) hmn
  exact ⟨t, hA.subset hts, hk⟩

private theorem zero_eq_cardN : (zero : Set (Set β)) = cardN β 0 := by
  rw [zero_eq_n₀c_empty, n₀c_eq_cardN Set.finite_empty, Set.ncard_empty]

private theorem one_eq_cardN : (one : Set (Set β)) = cardN β 1 := by
  ext B
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Set.finite_singleton x, Set.ncard_singleton x⟩
  · rintro ⟨-, h⟩
    obtain ⟨a, rfl⟩ := Set.ncard_eq_one.1 h
    exact ⟨a, rfl⟩

private theorem two_eq_cardN : (two : Set (Set β)) = cardN β 2 := by
  ext B
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    rw [unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]
    exact ⟨Set.toFinite _, Set.ncard_pair hxy⟩
  · rintro ⟨-, h⟩
    obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.1 h
    exact ⟨x, y, hxy, by rw [unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union]⟩

private theorem cardN_ne_n₀c_of_infinite {k : ℕ} {A : Set β} (hA : A.Infinite) :
    cardN β k ≠ n₀c A := by
  intro h
  have : A ∈ cardN β k := h ▸ self_mem_n₀c A
  exact hA this.1

private theorem empty_mem_NCinduct [Finite β] : (∅ : Set (Set β)) ∈ NCinduct := by
  have h := cardAdd_one_mem_NCinduct (n₀c_mem_NCinduct (Set.finite_univ (α := β)))
  rwa [n₀c_univ_cardAdd_one] at h

private theorem mem_NCinduct_iff_cardN {μ : Set (Set β)} : μ ∈ NCinduct ↔ ∃ k, μ = cardN β k := by
  constructor
  · intro h
    rcases NCinduct_cases h with ⟨A, hA, rfl⟩ | ⟨hfin, rfl⟩
    · exact ⟨A.ncard, n₀c_eq_cardN hA⟩
    · refine ⟨Nat.card β + 1, ?_⟩
      ext ξ
      simp only [Set.mem_empty_iff_false, false_iff]
      rintro ⟨-, hk⟩
      have := Set.ncard_le_ncard (Set.subset_univ ξ) Set.finite_univ
      rw [Set.ncard_univ] at this
      omega
  · rintro ⟨k, rfl⟩
    by_cases hk : (cardN β k).Nonempty
    · obtain ⟨A, hA⟩ := hk
      rw [cardN_eq_n₀c hA]
      exact n₀c_mem_NCinduct hA.1
    · have hfin : Finite β := by
        by_contra hinf
        have : Infinite β := not_finite_iff_infinite.1 hinf
        exact hk (cardN_nonempty_of_infinite k)
      rw [Set.not_nonempty_iff_eq_empty.1 hk]
      exact empty_mem_NCinduct

private theorem cardN_mem_NCinduct (k : ℕ) : cardN β k ∈ NCinduct :=
  mem_NCinduct_iff_cardN.2 ⟨k, rfl⟩

private theorem clsSum_finite {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    (A +ₐ B).Finite := by
  have : Finite A := hA.to_subtype
  have : Finite B := hB.to_subtype
  have := Fintype.ofFinite A
  have := Fintype.ofFinite B
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ (clsSumEquiv A B).symm)

private theorem ncard_clsSum {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    (A +ₐ B).ncard = A.ncard + B.ncard := by
  have : Finite A := hA.to_subtype
  have : Finite B := hB.to_subtype
  have := Fintype.ofFinite A
  have := Fintype.ofFinite B
  rw [← Nat.card_coe_set_eq, Nat.card_congr (clsSumEquiv A B), Nat.card_sum, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq]

private theorem cardAdd_cardN_of_nonempty {m n : ℕ} (hm : (cardN α m).Nonempty)
    (hn : (cardN β n).Nonempty) : (cardN α m +ᶜ cardN β n : Set (Set γ)) = cardN γ (m + n) := by
  obtain ⟨A, hA, rfl⟩ := hm
  obtain ⟨B, hB, rfl⟩ := hn
  rw [← n₀c_eq_cardN hA, ← n₀c_eq_cardN hB, n₀c_cardAdd_n₀c, nc_eq_cardN (clsSum_finite hA hB),
    ncard_clsSum hA hB]

private theorem cardAdd_eq_empty_of_empty_left {μ : Set (Set α)} (hm : ¬ μ.Nonempty)
    (ν : Set (Set β)) : (μ +ᶜ ν : Set (Set γ)) = ∅ :=
  cardAdd_eq_empty_of_left (fun A hA => hm (by rw [hA]; exact n₀c_nonempty A)) _

private theorem cardAdd_eq_empty_of_empty_right (μ : Set (Set α)) {ν : Set (Set β)}
    (hn : ¬ ν.Nonempty) : (μ +ᶜ ν : Set (Set γ)) = ∅ :=
  cardAdd_eq_empty_of_right _ (fun B hB => hn (by rw [hB]; exact n₀c_nonempty B))

/-! ### Comparison of cardinals -/

private theorem cl_inter_nc_nonempty_iff {A : Set α} {B : Set β} :
    (cl A ∩ nc α B).Nonempty ↔ Nonempty (B ↪ A) := by
  constructor
  · rintro ⟨C, hCA, hC⟩
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hC
    exact ⟨⟨fun b => ⟨(e.symm b : α), hCA (e.symm b).2⟩, fun b b' h => by
      simp only [Subtype.mk.injEq] at h
      exact e.symm.injective (Subtype.ext h)⟩⟩
  · rintro ⟨g⟩
    refine ⟨Set.range (fun b => (g b : α)), ?_, ?_⟩
    · rintro x ⟨b, rfl⟩
      exact (g b).2
    · exact sm_iff_nonempty_equiv.2
        ⟨(Equiv.ofInjective (fun b => (g b : α)) (Subtype.val_injective.comp g.injective)).symm⟩

private theorem cardGt_n₀c_iff {A : Set α} {B : Set β} :
    n₀c A >ᶜ n₀c B ↔ Nonempty (B ↪ A) ∧ ¬ Nonempty (A ↪ B) := by
  constructor
  · rintro ⟨A', B', ⟨⟨hA, hB⟩, h1⟩, h2⟩
    obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 hA)
    obtain ⟨eB⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 hB)
    obtain ⟨g⟩ := cl_inter_nc_nonempty_iff.1 h1
    refine ⟨⟨eB.toEmbedding.trans (g.trans eA.symm.toEmbedding)⟩, ?_⟩
    rintro ⟨g'⟩
    exact h2 (cl_inter_nc_nonempty_iff.2 ⟨eA.symm.toEmbedding.trans (g'.trans eB.toEmbedding)⟩)
  · rintro ⟨h1, h2⟩
    exact ⟨A, B, ⟨⟨rfl, rfl⟩, cl_inter_nc_nonempty_iff.2 h1⟩,
      fun h => h2 (cl_inter_nc_nonempty_iff.1 h)⟩

private theorem n₀c_eq_sm_img_iff {A : Set α} {B : Set β} : n₀c A = sm ʻʻ n₀c B ↔ sm A B := by
  rw [sm_img_n₀c, n₀c_eq_nc, nc_eq_nc_iff ⟨A, self_mem_nc A⟩]

private theorem cardGe_n₀c_iff {A : Set α} {B : Set β} :
    n₀c A ≥ᶜ n₀c B ↔ Nonempty (B ↪ A) := by
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact (cardGt_n₀c_iff.1 h).1
    · obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_sm_img_iff.1 h)
      exact ⟨e.symm.toEmbedding⟩
  · rintro ⟨g⟩
    by_cases h : Nonempty (A ↪ B)
    · obtain ⟨g'⟩ := h
      obtain ⟨k, hk⟩ := Function.Embedding.schroeder_bernstein g.injective g'.injective
      refine Or.inr ⟨⟨⟨A, rfl⟩, ⟨B, rfl⟩⟩, n₀c_eq_sm_img_iff.2 ?_⟩
      exact sm_iff_nonempty_equiv.2 ⟨(Equiv.ofBijective k hk).symm⟩
    · exact Or.inl (cardGt_n₀c_iff.2 ⟨⟨g⟩, h⟩)

private theorem mem_N₀C_of_cardGt {μ : Set (Set α)} {ν : Set (Set β)} (h : μ >ᶜ ν) :
    ∃ (A : Set α) (B : Set β), μ = n₀c A ∧ ν = n₀c B := by
  obtain ⟨A, B, ⟨⟨hA, hB⟩, -⟩, -⟩ := h
  exact ⟨A, B, hA, hB⟩

private theorem mem_N₀C_of_cardGe {μ : Set (Set α)} {ν : Set (Set β)} (h : μ ≥ᶜ ν) :
    ∃ (A : Set α) (B : Set β), μ = n₀c A ∧ ν = n₀c B := by
  rcases h with h | ⟨⟨⟨A, hA⟩, ⟨B, hB⟩⟩, -⟩
  · exact mem_N₀C_of_cardGt h
  · exact ⟨A, B, hA, hB⟩

private theorem embedding_iff_ncard_le {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    Nonempty (A ↪ B) ↔ A.ncard ≤ B.ncard := by
  have : Finite A := hA.to_subtype
  have : Finite B := hB.to_subtype
  constructor
  · rintro ⟨g⟩
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Finite.card_le_of_embedding g
  · intro h
    have := Fintype.ofFinite A
    have := Fintype.ofFinite B
    apply Function.Embedding.nonempty_of_card_le
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      Nat.card_coe_set_eq]
    exact h


/-! ### Ancestral: general facts -/

private theorem fld_of_anc_left {R : α → α → Prop} {x y : α} (h : anc R x y) : x ∈ fld R :=
  (anc_iff_reflTransGen.1 h).1

private theorem fld_of_anc_right {R : α → α → Prop} {x y : α} (h : anc R x y) : y ∈ fld R := by
  obtain ⟨hx, h⟩ := anc_iff_reflTransGen.1 h
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with rfl | h'
  · exact hx
  · obtain ⟨b, -, hby⟩ := Relation.TransGen.tail'_iff.1 h'
    exact ⟨b, Or.inr hby⟩

private theorem anc_trans {R : α → α → Prop} {x y z : α} (h1 : anc R x y) (h2 : anc R y z) :
    anc R x z := by
  obtain ⟨hx, h1⟩ := anc_iff_reflTransGen.1 h1
  exact anc_iff_reflTransGen.2 ⟨hx, h1.trans (anc_iff_reflTransGen.1 h2).2⟩

private theorem anc_refl {R : α → α → Prop} {x : α} (h : x ∈ fld R) : anc R x x :=
  anc_iff_reflTransGen.2 ⟨h, Relation.ReflTransGen.refl⟩

private theorem anc_of_rel {R : α → α → Prop} {x y : α} (h : R x y) : anc R x y :=
  anc_iff_reflTransGen.2 ⟨⟨y, Or.inl h⟩, Relation.ReflTransGen.single h⟩

private theorem anc_tail {R : α → α → Prop} {x y z : α} (h1 : anc R x y) (h2 : R y z) :
    anc R x z :=
  anc_trans h1 (anc_of_rel h2)

/-- For a many-one relation, the posterity of a term is linearly ordered. -/
private theorem rtg_linear_fwd {P : α → α → Prop} (hfun : ∀ x y z, P x y ∧ P x z → y = z)
    {y a b : α} (ha : Relation.ReflTransGen P y a) (hb : Relation.ReflTransGen P y b) :
    Relation.ReflTransGen P a b ∨ Relation.ReflTransGen P b a := by
  induction hb with
  | refl => exact Or.inr ha
  | tail _ hcb ih =>
    rcases ih with h | h
    · exact Or.inl (h.tail hcb)
    · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨d, hcd, hda⟩
      · exact Or.inl (Relation.ReflTransGen.single hcb)
      · rw [hfun _ _ _ ⟨hcd, hcb⟩] at hda
        exact Or.inr hda

/-- For a one-many relation, the ancestors of a term form a chain. -/
private theorem rtg_linear_bwd {P : α → α → Prop} (hinj : ∀ x y z, P x z ∧ P y z → x = y)
    {x a b : α} (ha : Relation.ReflTransGen P a x) (hb : Relation.ReflTransGen P b x) :
    Relation.ReflTransGen P a b ∨ Relation.ReflTransGen P b a := by
  have ha' : Relation.ReflTransGen P˘ x a := Relation.reflTransGen_swap.2 ha
  have hb' : Relation.ReflTransGen P˘ x b := Relation.reflTransGen_swap.2 hb
  rcases rtg_linear_fwd (P := P˘) (fun x y z h => hinj y z x ⟨h.1, h.2⟩) ha' hb' with h | h
  · exact Or.inr (Relation.reflTransGen_swap.1 h)
  · exact Or.inl (Relation.reflTransGen_swap.1 h)

/-- The posterity of `x` with respect to a many-one `P` whose posterity of `x` lies in `D'P` is
the range of a sequence of successive `P`-steps starting at `x`. -/
private theorem post_seq {P : α → α → Prop} (hfun : ∀ x y z, P x y ∧ P x z → y = z) {x : α}
    (hx : x ∈ dom P) (hdom : rels (anc P) x ⊆ dom P) :
    ∃ f : ℕ → α, f 0 = x ∧ (∀ n, P (f n) (f (n + 1))) ∧ rels (anc P) x = Set.range f := by
  have hex : ∀ y, ∃ z, y ∈ dom P → P y z := by
    intro y
    by_cases hy : y ∈ dom P
    · obtain ⟨z, hz⟩ := hy
      exact ⟨z, fun _ => hz⟩
    · exact ⟨y, fun h => absurd h hy⟩
  choose g hg using hex
  let f : ℕ → α := fun n => g^[n] x
  have hfs : ∀ n, f (n + 1) = g (f n) := fun n => Function.iterate_succ_apply' g n x
  have hfld : x ∈ fld P := let ⟨y, hy⟩ := hx; ⟨y, Or.inl hy⟩
  have hanc : ∀ n, anc P x (f n) := by
    intro n
    induction n with
    | zero => exact anc_refl hfld
    | succ n ih =>
      rw [hfs]
      exact anc_tail ih (hg _ (hdom ih))
  have hstep : ∀ n, P (f n) (f (n + 1)) := fun n => by rw [hfs]; exact hg _ (hdom (hanc n))
  refine ⟨f, rfl, hstep, ?_⟩
  ext y
  constructor
  · intro hy
    have hr := (anc_iff_reflTransGen.1 hy).2
    induction hr with
    | refl => exact ⟨0, rfl⟩
    | tail hbc hcd ih =>
      obtain ⟨n, hn⟩ := ih (anc_iff_reflTransGen.2 ⟨hfld, hbc⟩)
      exact ⟨n + 1, hfun _ _ _ ⟨hn ▸ hstep n, hcd⟩⟩
  · rintro ⟨n, rfl⟩
    exact hanc n

/-- Steps of a sequence give the proper ancestral. -/
private theorem po_of_steps {P : α → α → Prop} {f : ℕ → α} (hstep : ∀ n, P (f n) (f (n + 1)))
    {m n : ℕ} (h : m < n) : po P (f m) (f n) := by
  rw [po_iff_transGen]
  induction n, h using Nat.le_induction with
  | base => exact Relation.TransGen.single (hstep m)
  | succ k _ ih => exact ih.tail (hstep k)

/-- A many-one relation whose domain is the range of a sequence of its steps is the successor
relation of that sequence. -/
private theorem eq_seqRel_of_steps {P : α → α → Prop} (hfun : ∀ x y z, P x y ∧ P x z → y = z)
    {f : ℕ → α} (hstep : ∀ n, P (f n) (f (n + 1))) (hdom : dom P ⊆ Set.range f) :
    P = SeqRel f := by
  funext x y
  apply propext
  constructor
  · intro hxy
    obtain ⟨n, rfl⟩ := hdom ⟨y, hxy⟩
    exact ⟨n, rfl, hfun _ _ _ ⟨hxy, hstep n⟩⟩
  · rintro ⟨n, rfl, rfl⟩
    exact hstep n

/-! ### Powers of a progression -/

/-- The `d`-th power of the successor relation of `f`. -/
private def SeqStep (f : ℕ → α) (d : ℕ) : α → α → Prop := fun x y => ∃ n, x = f n ∧ y = f (n + d)

private theorem seqStep_one (f : ℕ → α) : SeqStep f 1 = SeqRel f := rfl

private theorem dom_seqStep (f : ℕ → α) (d : ℕ) : dom (SeqStep f d) = Set.range f := by
  ext x
  constructor
  · rintro ⟨y, n, rfl, -⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, n, rfl, rfl⟩

private theorem codom_seqStep (f : ℕ → α) (d : ℕ) :
    codom (SeqStep f d) = Set.range (fun n => f (n + d)) := by
  ext y
  constructor
  · rintro ⟨x, n, -, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, n, rfl, rfl⟩

private theorem fld_seqStep (f : ℕ → α) (d : ℕ) : fld (SeqStep f d) = Set.range f := by
  ext x
  constructor
  · rintro ⟨y, ⟨n, rfl, -⟩ | ⟨n, -, rfl⟩⟩
    · exact ⟨n, rfl⟩
    · exact ⟨n + d, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, Or.inl ⟨n, rfl, rfl⟩⟩

private theorem seqStep_comp {f : ℕ → α} (hf : Injective f) (d : ℕ) :
    SeqStep f d ⨾ SeqRel f = SeqStep f (d + 1) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, ⟨n, rfl, rfl⟩, ⟨m, hm, rfl⟩⟩
    rw [← hf hm]
    exact ⟨n, rfl, by rw [Nat.add_assoc]⟩
  · rintro ⟨n, rfl, rfl⟩
    exact ⟨f (n + d), ⟨n, rfl, rfl⟩, ⟨n + d, rfl, by rw [Nat.add_assoc]⟩⟩

private theorem pot_seqRel {f : ℕ → α} (hf : Injective f) {P : α → α → Prop}
    (h : P ∈ pot (SeqRel f)) : ∃ d, 1 ≤ d ∧ P = SeqStep f d := by
  have key : ∀ S, Relation.ReflTransGen (relProdR (SeqRel f)) S (SeqRel f) →
      ∃ d, 1 ≤ d ∧ S = SeqStep f d := by
    intro S hS
    induction hS using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨1, le_rfl, rfl⟩
    | head hac _ ih =>
      obtain ⟨d, hd, hS⟩ := ih
      rw [relProdR_apply, hS] at hac
      exact ⟨d + 1, by omega, by rw [hac, seqStep_comp hf]⟩
  exact key P (mem_pot_iff.1 h).2

private theorem rtg_seqStep {f : ℕ → α} (hf : Injective f) {d : ℕ} {m : ℕ} {y : α} :
    Relation.ReflTransGen (SeqStep f d) (f m) y ↔ ∃ q, y = f (m + q * d) := by
  constructor
  · intro hr
    induction hr with
    | refl => exact ⟨0, by simp⟩
    | tail _ hbc ih =>
      obtain ⟨q, rfl⟩ := ih
      obtain ⟨k, hk, rfl⟩ := hbc
      rw [← hf hk]
      exact ⟨q + 1, by rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]⟩
  · rintro ⟨q, rfl⟩
    induction q with
    | zero => simpa using Relation.ReflTransGen.refl
    | succ q ih =>
      refine ih.tail ⟨m + q * d, rfl, ?_⟩
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]

private theorem anc_seqStep {f : ℕ → α} (hf : Injective f) {d : ℕ} {m : ℕ} {y : α} :
    anc (SeqStep f d) (f m) y ↔ ∃ q, y = f (m + q * d) := by
  rw [anc_iff_reflTransGen, fld_seqStep, rtg_seqStep hf]
  exact and_iff_right ⟨m, rfl⟩

private theorem seqStep_oneone {f : ℕ → α} (hf : Injective f) (d : ℕ) :
    SeqStep f d ∈ arrow one one := by
  rw [mem_arrow_one_one]
  refine ⟨?_, ?_⟩
  · rintro x y z ⟨⟨m, rfl, hz⟩, ⟨n, rfl, hz'⟩⟩
    have := hf (hz.symm.trans hz')
    rw [show m = n by omega]
  · rintro x y z ⟨⟨m, rfl, rfl⟩, ⟨n, hmn, rfl⟩⟩
    rw [hf hmn]

private theorem beg_seqStep {f : ℕ → α} (hf : Injective f) {d : ℕ} {x : α} :
    Beg x (SeqStep f d) ↔ ∃ i, i < d ∧ x = f i := by
  rw [Beg_apply, dom_seqStep, codom_seqStep]
  constructor
  · rintro ⟨⟨n, rfl⟩, h⟩
    refine ⟨n, ?_, rfl⟩
    by_contra hn
    exact h ⟨n - d, by simp only; congr 1; omega⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, rfl⟩, ?_⟩
    rintro ⟨k, hk⟩
    have := hf hk
    omega

/-! ### Generations -/

/-- `I ↾ C'P`, `P`, `P²`, …: the members of `Potid'P`. -/
private def pw (P : α → α → Prop) : ℕ → α → α → Prop
  | 0 => I ↾ fld P
  | n + 1 => pw P n ⨾ P

private theorem mem_potid_iff {P Q : α → α → Prop} : Q ∈ potid P ↔ ∃ n, Q = pw P n := by
  show anc (relProdR P) Q (I ↾ fld P) ↔ _
  rw [anc_iff_reflTransGen]
  constructor
  · rintro ⟨-, h⟩
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | head hac _ ih =>
      obtain ⟨n, hn⟩ := ih
      rw [relProdR_apply, hn] at hac
      exact ⟨n + 1, hac⟩
  · rintro ⟨n, rfl⟩
    refine ⟨⟨pw P n ⨾ P, Or.inr rfl⟩, ?_⟩
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih => exact Relation.ReflTransGen.head (rfl : relProdR P (pw P n ⨾ P) (pw P n)) ih

private theorem codom_pw_zero (P : α → α → Prop) : codom (pw P 0) = fld P := by
  ext y
  constructor
  · rintro ⟨x, rfl, hy⟩
    exact hy
  · intro hy
    exact ⟨y, rfl, hy⟩

private theorem codom_pw_succ (P : α → α → Prop) (n : ℕ) (y : α) :
    y ∈ codom (pw P (n + 1)) ↔ ∃ z, z ∈ codom (pw P n) ∧ P z y := by
  constructor
  · rintro ⟨x, z, hxz, hzy⟩
    exact ⟨z, ⟨x, hxz⟩, hzy⟩
  · rintro ⟨z, ⟨x, hxz⟩, hzy⟩
    exact ⟨x, z, hxz, hzy⟩

/-- `x ∈ s'gen'P` iff `x` is a descendant of a beginning of `P`, for a one-many `P`. -/
private theorem mem_sumCls_gen_iff {P : α → α → Prop} (hinj : ∀ x y z, P x z ∧ P y z → x = y)
    {x : α} : x ∈ sumCls (gen P) ↔ ∃ y, Beg y P ∧ anc P y x := by
  have hgen : x ∈ sumCls (gen P) ↔ ∃ n, minP P x (codom (pw P n)) := by
    constructor
    · rintro ⟨G, ⟨C, ⟨Q, hQ, hC⟩, hG⟩, hx⟩
      obtain ⟨n, rfl⟩ := mem_potid_iff.1 hQ
      have hG' : G = refs (minP P) C := hG
      have hC' : C = codom (pw P n) := hC
      rw [hG', hC'] at hx
      exact ⟨n, hx⟩
    · rintro ⟨n, hn⟩
      exact ⟨_, ⟨codom (pw P n), ⟨pw P n, mem_potid_iff.2 ⟨n, rfl⟩, rfl⟩, rfl⟩, hn⟩
  rw [hgen]
  clear hgen
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing x with
    | zero =>
      rw [minP_apply, codom_pw_zero] at hn
      obtain ⟨⟨-, hx⟩, hno⟩ := hn
      have hxc : x ∉ codom P := fun ⟨y, hy⟩ => hno ⟨y, ⟨x, Or.inl hy⟩, hy⟩
      have hxd : x ∈ dom P := by
        obtain ⟨y, hy | hy⟩ := hx
        · exact ⟨y, hy⟩
        · exact absurd ⟨y, hy⟩ hxc
      exact ⟨x, ⟨hxd, hxc⟩, anc_refl hx⟩
    | succ n ih =>
      rw [minP_apply] at hn
      obtain ⟨⟨hx1, -⟩, hno⟩ := hn
      obtain ⟨z, hz, hzx⟩ := (codom_pw_succ P n x).1 hx1
      have hzmin : minP P z (codom (pw P n)) := by
        refine ⟨⟨hz, ⟨x, Or.inl hzx⟩⟩, ?_⟩
        rintro ⟨w, hw, hwz⟩
        exact hno ⟨z, (codom_pw_succ P n z).2 ⟨w, hw, hwz⟩, hzx⟩
      obtain ⟨y, hy, hyz⟩ := ih hzmin
      exact ⟨y, hy, anc_tail hyz hzx⟩
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨hyf, hr⟩ := anc_iff_reflTransGen.1 hyx
    induction hr with
    | refl =>
      refine ⟨0, ?_⟩
      rw [minP_apply, codom_pw_zero]
      exact ⟨⟨hyf, hyf⟩, fun ⟨w, _, hw⟩ => hy.2 ⟨w, hw⟩⟩
    | tail hbc hcx ih =>
      obtain ⟨n, hn⟩ := ih (anc_iff_reflTransGen.2 ⟨hyf, hbc⟩)
      refine ⟨n + 1, ?_⟩
      rw [minP_apply] at hn ⊢
      refine ⟨⟨(codom_pw_succ P n _).2 ⟨_, hn.1.1, hcx⟩, ⟨_, Or.inr hcx⟩⟩, ?_⟩
      rintro ⟨w, hw, hwx⟩
      rw [hinj _ _ _ ⟨hwx, hcx⟩] at hw
      obtain ⟨v, hv, hvc⟩ := (codom_pw_succ P n _).1 hw
      exact hn.2 ⟨v, hv, hvc⟩

/-! ### Intervals of a progression -/

private theorem finite_Icc_nat (m n : ℕ) : {i | m ≤ i ∧ i ≤ n}.Finite :=
  (Set.finite_le_nat n).subset fun i hi => (show m ≤ i ∧ i ≤ n from hi).2

private theorem ncard_Icc_nat (m n : ℕ) : {i | m ≤ i ∧ i ≤ n}.ncard = n + 1 - m := by
  induction n with
  | zero =>
    by_cases hm : m = 0
    · subst hm
      have : {i : ℕ | 0 ≤ i ∧ i ≤ 0} = {0} := by
        ext i; simp
      rw [this, Set.ncard_singleton]
    · have : {i : ℕ | m ≤ i ∧ i ≤ 0} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun i hi => by obtain ⟨h1, h2⟩ := hi; omega
      rw [this, Set.ncard_empty]
      omega
  | succ n ih =>
    by_cases hm : m ≤ n + 1
    · have : {i : ℕ | m ≤ i ∧ i ≤ n + 1} = insert (n + 1) {i | m ≤ i ∧ i ≤ n} := by
        ext i
        rw [Set.mem_insert_iff]
        show (m ≤ i ∧ i ≤ n + 1) ↔ i = n + 1 ∨ (m ≤ i ∧ i ≤ n)
        constructor
        · intro h; omega
        · intro h; omega
      have hnot : n + 1 ∉ {i : ℕ | m ≤ i ∧ i ≤ n} := fun h => by
        have := (show m ≤ n + 1 ∧ n + 1 ≤ n from h).2
        omega
      rw [this, Set.ncard_insert_of_notMem hnot (finite_Icc_nat m n), ih]
      omega
    · have : {i : ℕ | m ≤ i ∧ i ≤ n + 1} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun i hi => by obtain ⟨h1, h2⟩ := hi; omega
      rw [this, Set.ncard_empty]
      omega

private theorem itvCC_seqRel {f : ℕ → α} (hf : Injective f) (m n : ℕ) :
    itvCC (SeqRel f) (f m) (f n) = f '' {i | m ≤ i ∧ i ≤ n} := by
  ext z
  show anc (SeqRel f) (f m) z ∧ anc (SeqRel f) z (f n) ↔ _
  rw [anc_seqRel hf, anc_seqRel hf]
  constructor
  · rintro ⟨⟨a, b, hab, ha, rfl⟩, ⟨c, e, hce, hc, he⟩⟩
    rw [← hf ha] at hab
    rw [← hf hc, ← hf he] at hce
    exact ⟨b, ⟨hab, hce⟩, rfl⟩
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨m, i, h1, rfl, rfl⟩, ⟨i, n, h2, rfl, rfl⟩⟩

private theorem itvCC_eq_empty_left {R : α → α → Prop} {x y : α} (hx : x ∉ fld R) :
    itvCC R x y = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hz => hx (fld_of_anc_left hz.1)

private theorem itvCC_eq_empty_right {R : α → α → Prop} {x y : α} (hy : y ∉ fld R) :
    itvCC R x y = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hz => hy (fld_of_anc_right hz.2)

private theorem itvCC_seqRel_finite {f : ℕ → α} (hf : Injective f) (x y : α) :
    (itvCC (SeqRel f) x y).Finite := by
  by_cases hx : x ∈ Set.range f
  · by_cases hy : y ∈ Set.range f
    · obtain ⟨m, rfl⟩ := hx
      obtain ⟨n, rfl⟩ := hy
      rw [itvCC_seqRel hf]
      exact (finite_Icc_nat m n).image f
    · rw [itvCC_eq_empty_right (by rwa [fld_seqRel])]
      exact Set.finite_empty
  · rw [itvCC_eq_empty_left (by rwa [fld_seqRel])]
    exact Set.finite_empty

/-- The number of terms of `R(x ⊢⊣ y)` in a progression. -/
private theorem ncard_itvCC_seqRel {f : ℕ → α} (hf : Injective f) {x y : α} {k : ℕ} :
    (itvCC (SeqRel f) x y).ncard = k + 1 ↔ ∃ m, x = f m ∧ y = f (m + k) := by
  constructor
  · intro h
    by_cases hx : x ∈ Set.range f
    · by_cases hy : y ∈ Set.range f
      · obtain ⟨m, rfl⟩ := hx
        obtain ⟨n, rfl⟩ := hy
        rw [itvCC_seqRel hf, Set.ncard_image_of_injective _ hf, ncard_Icc_nat] at h
        exact ⟨m, rfl, by congr 1; omega⟩
      · rw [itvCC_eq_empty_right (by rwa [fld_seqRel]), Set.ncard_empty] at h
        omega
    · rw [itvCC_eq_empty_left (by rwa [fld_seqRel]), Set.ncard_empty] at h
      omega
  · rintro ⟨m, rfl, rfl⟩
    rw [itvCC_seqRel hf, Set.ncard_image_of_injective _ hf, ncard_Icc_nat]
    omega

/-! ### `ν +_c 1`, `ν −_c 1`, `P_ν` and `ν_P` -/

private theorem finite_of_clsSum_finite_left {A : Set α} {B : Set β} (h : (A +ₐ B).Finite) :
    A.Finite := by
  have : Finite ↥(A +ₐ B) := h.to_subtype
  have : Finite (A ⊕ B) := Finite.of_equiv _ (clsSumEquiv A B)
  exact Set.finite_coe_iff.1 (Finite.of_injective (Sum.inl : A → A ⊕ B) Sum.inl_injective)

private theorem cardN_one_nonempty {X : Type*} (b : X) : (cardN X 1).Nonempty :=
  ⟨{b}, Set.finite_singleton b, Set.ncard_singleton b⟩

/-- `N₀c'σ = μ +_c 1` for a finite `σ` (the `1` in the type of `μ`). -/
private theorem n₀c_eq_cardAdd_one_iff {X : Type*} {S : Set α} (hS : S.Finite)
    {μ : Set (Set X)} :
    n₀c S = (μ +ᶜ (one : Set (Set X)) : Set (Set α)) ↔
      ∃ j, (μ = cardN X j ∧ (cardN X j).Nonempty) ∧ Nonempty X ∧ S.ncard = j + 1 := by
  constructor
  · intro h
    have hS' : S ∈ (μ +ᶜ (one : Set (Set X)) : Set (Set α)) := h ▸ self_mem_n₀c S
    obtain ⟨A, B, ⟨hμ, h1⟩, hsm⟩ := hS'
    have hB : B ∈ (one : Set (Set X)) := h1 ▸ self_mem_n₀c B
    obtain ⟨b, rfl⟩ := hB
    obtain ⟨hfin, hcard⟩ := (sm_iff_of_finite hS).1 hsm
    have hA : A.Finite := finite_of_clsSum_finite_left hfin
    rw [unitCls_eq_singleton, ncard_clsSum hA (Set.finite_singleton b), Set.ncard_singleton]
      at hcard
    exact ⟨A.ncard, ⟨by rw [hμ, n₀c_eq_cardN hA], ⟨A, hA, rfl⟩⟩, ⟨b⟩, hcard⟩
  · rintro ⟨j, ⟨rfl, hj⟩, ⟨b⟩, hcard⟩
    rw [one_eq_cardN, cardAdd_cardN_of_nonempty hj (cardN_one_nonempty b), n₀c_eq_cardN hS, hcard]

/-- `x P_μ y` in a progression. -/
private theorem pnu_seqRel {X : Type*} {f : ℕ → α} (hf : Injective f) {μ : Set (Set X)}
    {x y : α} :
    Pnu (SeqRel f) μ x y ↔
      ∃ j, (μ = cardN X j ∧ (cardN X j).Nonempty) ∧ Nonempty X ∧ ∃ m, x = f m ∧ y = f (m + j) := by
  show n₀c (itvCC (SeqRel f) x y) = _ ↔ _
  rw [n₀c_eq_cardAdd_one_iff (itvCC_seqRel_finite hf x y)]
  simp only [ncard_itvCC_seqRel hf]

private theorem nonempty_of_cardN_succ {X : Type*} {k : ℕ} (h : (cardN X (k + 1)).Nonempty) :
    Nonempty X := by
  obtain ⟨A, -, hk⟩ := h
  obtain ⟨a, -⟩ := Set.nonempty_of_ncard_ne_zero (s := A) (by omega)
  exact ⟨a⟩

private theorem cardN_succ_eq {X : Type*} {k : ℕ} {ξ : Set X} (hξ : ξ ∈ cardN X k) (b : X) :
    (n₀c ξ +ᶜ (one : Set (Set X)) : Set (Set X)) = cardN X (k + 1) := by
  rw [← cardN_eq_n₀c hξ, one_eq_cardN, cardAdd_cardN_of_nonempty ⟨ξ, hξ⟩ (cardN_one_nonempty b)]

private theorem cardSub_one_cardN {X : Type*} {k : ℕ} (h : (cardN X (k + 1)).Nonempty) :
    (cardN X (k + 1) -ᶜ (one : Set (Set X)) : Set (Set X)) = cardN X k := by
  obtain ⟨b⟩ := nonempty_of_cardN_succ h
  ext ξ
  constructor
  · rintro ⟨he, -⟩
    obtain ⟨C, hC⟩ := h
    rw [cardN_eq_n₀c hC] at he
    obtain ⟨j, ⟨hj, -⟩, -, hc⟩ := (n₀c_eq_cardAdd_one_iff hC.1).1 he.symm
    have hξ : ξ ∈ cardN X j := hj ▸ self_mem_n₀c ξ
    rw [hC.2] at hc
    rw [show k = j by omega]
    exact hξ
  · intro hξ
    have := cardN_succ_eq hξ b
    exact ⟨this, this ▸ h⟩

private theorem EDesc_iff_desc_true {R : α → β → Prop} {y : β} :
    EDesc R y ↔ Desc R y (fun _ => True) := by
  rw [Desc, TheIs_iff]
  exact (and_iff_left (fun _ _ => trivial)).symm

/-- `ψ(ν_R)` for a progression `R` and an existent `ν = k + 1`. -/
private theorem desc_nuP_seqRel {X : Type*} {f : ℕ → α} (hf : Injective f) {k : ℕ}
    (hk : (cardN X (k + 1)).Nonempty) (ψ : α → Prop) :
    Desc (nuP (cardN X (k + 1))) (SeqRel f) ψ ↔ ψ (f k) := by
  rw [desc_nuP, desc2_iff, desc_beg_seqRel hf, cardSub_one_cardN hk]
  apply TheIs_iff_of_unique
  intro y
  show Pnu (SeqRel f) (cardN X k) (f 0) y ↔ y = f k
  rw [pnu_seqRel hf]
  constructor
  · rintro ⟨j, ⟨hj, -⟩, -, m, hm, rfl⟩
    rw [← hf hm, Nat.zero_add, ← cardN_inj (cardN_mono_nonempty (Nat.le_succ k) hk) hj]
  · rintro rfl
    exact ⟨k, ⟨rfl, cardN_mono_nonempty (Nat.le_succ k) hk⟩, nonempty_of_cardN_succ hk, 0, rfl,
      by rw [Nat.zero_add]⟩

/-- If `ν_R` exists for a progression `R`, then `ν` is an existent inductive cardinal other
than `0`. -/
private theorem cardN_of_EDesc_nuP {X : Type*} {f : ℕ → α} (hf : Injective f) {ν : Set (Set X)}
    (h : EDesc (nuP ν) (SeqRel f)) : ∃ k, ν = cardN X (k + 1) ∧ (cardN X (k + 1)).Nonempty := by
  rw [EDesc_iff_desc_true, desc_nuP, desc2_iff, desc_beg_seqRel hf] at h
  obtain ⟨y, hy, -⟩ := h
  have hy' : Pnu (SeqRel f) (ν -ᶜ (one : Set (Set X))) (f 0) y := (hy y).2 rfl
  obtain ⟨j, ⟨hj, ⟨ξ, hξ⟩⟩, ⟨b⟩, -⟩ := (pnu_seqRel hf).1 hy'
  have hξ' : ξ ∈ (ν -ᶜ (one : Set (Set X)) : Set (Set X)) := hj ▸ hξ
  obtain ⟨he, hne⟩ := hξ'
  rw [cardN_succ_eq hξ b] at he hne
  exact ⟨j, he.symm, hne⟩

private theorem desc_nuP_one_seqRel {W : Type*} [Nonempty W] {f : ℕ → α} (hf : Injective f)
    (ψ : α → Prop) : Desc (nuP (one : Set (Set W))) (SeqRel f) ψ ↔ ψ (f 0) := by
  obtain ⟨b⟩ := ‹Nonempty W›
  rw [one_eq_cardN]
  exact desc_nuP_seqRel hf (k := 0) (cardN_one_nonempty b) ψ

/-- Members of `NC induct − ι'0`. -/
private theorem mem_NCinduct_ne_zero {X : Type*} {ν : Set (Set X)} :
    ν ∈ NCinduct \ ι zero ↔ ∃ k, ν = cardN X (k + 1) := by
  rw [Set.mem_sdiff, mem_NCinduct_iff_cardN]
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    cases k with
    | zero => exact absurd (zero_eq_cardN).symm hk
    | succ k => exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    refine ⟨⟨k + 1, rfl⟩, fun h => ?_⟩
    have h' : cardN X (k + 1) = cardN X 0 := (mem_unitCls.1 h).trans zero_eq_cardN
    have h0 : ∅ ∈ cardN X 0 := ⟨Set.finite_empty, Set.ncard_empty X⟩
    rw [← h'] at h0
    exact absurd h0.2 (by rw [Set.ncard_empty]; omega)


/-! ### Further helpers -/

private theorem desc_iff_of_unique {R : α → β → Prop} {y : β} {b : α} (h : ∀ x, R x y ↔ x = b)
    (ψ : α → Prop) : Desc R y ψ ↔ ψ b :=
  TheIs_iff_of_unique h

private theorem seqRel_mem {f : ℕ → α} {x y : α} (h : SeqRel f x y) :
    x ∈ Set.range f ∧ y ∈ Set.range (fun n => f (n + 1)) :=
  let ⟨n, hx, hy⟩ := h
  ⟨⟨n, hx.symm⟩, ⟨n, hy.symm⟩⟩

private theorem range_succ_sub (f : ℕ → α) : Set.range (fun n => f (n + 1)) ⊆ Set.range f := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n + 1, rfl⟩

private theorem post_zero_seqRel {f : ℕ → α} (hf : Injective f) :
    rels (anc (SeqRel f)) (f 0) = Set.range f := by
  ext y
  show anc (SeqRel f) (f 0) y ↔ _
  rw [anc_seqRel hf]
  constructor
  · rintro ⟨-, n, -, -, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨0, n, Nat.zero_le n, rfl, rfl⟩

private theorem popost_zero_seqRel {f : ℕ → α} (hf : Injective f) :
    rels (po (SeqRel f)) (f 0) = Set.range (fun n => f (n + 1)) := by
  ext y
  show po (SeqRel f) (f 0) y ↔ _
  rw [po_seqRel hf]
  constructor
  · rintro ⟨m, n, hmn, hm, rfl⟩
    rw [← hf hm] at hmn
    exact ⟨n - 1, by show f (n - 1 + 1) = f n; rw [Nat.sub_add_cancel hmn]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨0, n + 1, by omega, rfl, rfl⟩

private theorem anc_seqRel_mem {f : ℕ → α} (hf : Injective f) {x y : α}
    (h : anc (SeqRel f) x y) : x ∈ Set.range f ∧ y ∈ Set.range f := by
  obtain ⟨m, n, -, rfl, rfl⟩ := (anc_seqRel hf).1 h
  exact ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩

private theorem po_seqRel_mem {f : ℕ → α} (hf : Injective f) {x y : α}
    (h : po (SeqRel f) x y) : x ∈ Set.range f ∧ y ∈ Set.range (fun n => f (n + 1)) := by
  obtain ⟨m, n, hmn, rfl, rfl⟩ := (po_seqRel hf).1 h
  exact ⟨⟨m, rfl⟩, ⟨n - 1, by show f (n - 1 + 1) = f n; rw [Nat.sub_add_cancel (by omega)]⟩⟩

private theorem fld_po_seqRel {f : ℕ → α} (hf : Injective f) :
    fld (po (SeqRel f)) = Set.range f := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact (po_seqRel_mem hf h).1
    · exact range_succ_sub f (po_seqRel_mem hf h).2
  · rintro ⟨n, rfl⟩
    exact ⟨f (n + 1), Or.inl ((po_seqRel' hf).2 (Nat.lt_succ_self n))⟩

private theorem fld_cnv (R : α → α → Prop) : fld R˘ = fld R := by
  ext z
  exact ⟨fun ⟨w, h⟩ => ⟨w, h.symm⟩, fun ⟨w, h⟩ => ⟨w, h.symm⟩⟩

private theorem pnu_seqRel_of_nonempty {X : Type*} {f : ℕ → α} (hf : Injective f) {j : ℕ}
    (hj : (cardN X j).Nonempty) [Nonempty X] {x y : α} :
    Pnu (SeqRel f) (cardN X j) x y ↔ ∃ m, x = f m ∧ y = f (m + j) := by
  rw [pnu_seqRel hf]
  constructor
  · rintro ⟨i, ⟨hi, -⟩, -, h⟩
    rwa [← cardN_inj hj hi] at h
  · intro h
    exact ⟨j, ⟨rfl, hj⟩, inferInstance, h⟩

private theorem pnu_seqRel_of_empty {X : Type*} {f : ℕ → α} (hf : Injective f) {j : ℕ}
    (hj : ¬ (cardN X j).Nonempty) {x y : α} : ¬ Pnu (SeqRel f) (cardN X j) x y := by
  rw [pnu_seqRel hf]
  rintro ⟨i, ⟨hi, hine⟩, -⟩
  exact hj (hi ▸ hine)

private theorem beg_pnu_seqRel {X : Type*} {f : ℕ → α} (hf : Injective f) {k : ℕ}
    (hk : (cardN X (k + 1)).Nonempty) {x : α} :
    Beg x (Pnu (SeqRel f) (cardN X (k + 1))) ↔ ∃ m, m ≤ k ∧ x = f m := by
  have := nonempty_of_cardN_succ hk
  rw [Beg_apply]
  constructor
  · rintro ⟨⟨y, hxy⟩, hno⟩
    obtain ⟨m, rfl, rfl⟩ := (pnu_seqRel_of_nonempty hf hk).1 hxy
    refine ⟨m, ?_, rfl⟩
    by_contra hm
    exact hno ⟨f (m - (k + 1)), (pnu_seqRel_of_nonempty hf hk).2
      ⟨m - (k + 1), rfl, by congr 1; omega⟩⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨⟨_, (pnu_seqRel_of_nonempty hf hk).2 ⟨m, rfl, rfl⟩⟩, ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl, hn⟩ := (pnu_seqRel_of_nonempty hf hk).1 hy
    have := hf hn
    omega

private theorem cardGt_cardN_iff {X : Type*} {S : Set α} (hS : S.Finite) {j : ℕ} :
    n₀c S >ᶜ cardN X j ↔ (cardN X j).Nonempty ∧ j < S.ncard := by
  by_cases hj : (cardN X j).Nonempty
  · obtain ⟨B, hB⟩ := hj
    rw [cardN_eq_n₀c hB, cardGt_n₀c_iff, embedding_iff_ncard_le hB.1 hS,
      embedding_iff_ncard_le hS hB.1, hB.2]
    exact ⟨fun h => ⟨⟨B, self_mem_n₀c B⟩, by omega⟩, fun h => ⟨by omega, by omega⟩⟩
  · refine ⟨fun h => ?_, fun h => absurd h.1 hj⟩
    obtain ⟨A, B, -, hB⟩ := mem_N₀C_of_cardGt h
    exact absurd (hB ▸ n₀c_nonempty B) hj

private theorem cardGe_cardN_iff {X : Type*} {S : Set α} (hS : S.Finite) {j : ℕ} :
    cardN X j ≥ᶜ n₀c S ↔ (cardN X j).Nonempty ∧ S.ncard ≤ j := by
  by_cases hj : (cardN X j).Nonempty
  · obtain ⟨B, hB⟩ := hj
    rw [cardN_eq_n₀c hB, cardGe_n₀c_iff, embedding_iff_ncard_le hS hB.1, hB.2]
    exact ⟨fun h => ⟨⟨B, self_mem_n₀c B⟩, h⟩, fun h => h.2⟩
  · refine ⟨fun h => ?_, fun h => absurd h.1 hj⟩
    obtain ⟨A, B, hA, -⟩ := mem_N₀C_of_cardGe h
    exact absurd (hA ▸ n₀c_nonempty A) hj

private theorem aleph0_of_infinite_sub_range {f : ℕ → α} {A : Set α} (hA : A ⊆ Set.range f)
    (hinf : A.Infinite) : A ∈ aleph0 := by
  have hc : A.Countable := (Set.countable_range f).mono hA
  have : Countable A := hc.to_subtype
  have : Infinite A := Set.infinite_coe_iff.2 hinf
  obtain ⟨_⟩ : Nonempty (Denumerable A) := nonempty_denumerable_iff.2 ⟨inferInstance, inferInstance⟩
  exact mem_aleph0_iff_equiv.2 ⟨(Denumerable.eqv A).symm⟩

/-- A bounded nonempty set of naturals has a greatest member. -/
private theorem exists_max_nat {p : ℕ → Prop} (N : ℕ) (hb : ∀ n, p n → n ≤ N) (hne : ∃ n, p n) :
    ∃ M, p M ∧ ∀ n, p n → n ≤ M := by
  classical
  have hex : ∃ d, p (N - d) := by
    obtain ⟨n, hn⟩ := hne
    exact ⟨N - n, by rw [Nat.sub_sub_self (hb n hn)]; exact hn⟩
  refine ⟨N - Nat.find hex, Nat.find_spec hex, fun n hn => ?_⟩
  have h1 := hb n hn
  have h2 : Nat.find hex ≤ N - n := Nat.find_min' hex (by rw [Nat.sub_sub_self h1]; exact hn)
  omega

/-- The increasing enumeration of a class contained in a progression and having no last term. -/
private theorem enum_of_sub_po {f : ℕ → α} (hf : Injective f) {A : Set α}
    (hA : A ⊆ po (SeqRel f) ʻʻ A) (hne : A.Nonempty) :
    ∃ idx : ℕ → ℕ, StrictMono idx ∧ (∀ q, f (idx q) ∈ A) ∧ (∀ n, f n ∈ A → ∃ q, idx q = n) ∧
      (∀ q k, f k ∈ A → idx q < k → idx (q + 1) ≤ k) ∧ (∀ k, f k ∈ A → idx 0 ≤ k) := by
  classical
  have hsub : ∀ z ∈ A, ∃ n, z = f n := fun z hz => by
    obtain ⟨y, -, hzy⟩ := hA hz
    obtain ⟨m, n, -, rfl, -⟩ := (po_seqRel hf).1 hzy
    exact ⟨m, rfl⟩
  have hnext : ∀ m, f m ∈ A → ∃ k, m < k ∧ f k ∈ A := fun m hm => by
    obtain ⟨y, hy, hmy⟩ := hA hm
    obtain ⟨a, n, han, ha, rfl⟩ := (po_seqRel hf).1 hmy
    rw [← hf ha] at han
    exact ⟨n, han, hy⟩
  have h0 : ∃ k, f k ∈ A := let ⟨x, hx⟩ := hne; let ⟨n, e⟩ := hsub x hx; ⟨n, e ▸ hx⟩
  have hunb : ∀ m, ∃ k, m < k ∧ f k ∈ A := by
    intro m
    induction m with
    | zero =>
      obtain ⟨k, hk⟩ := h0
      obtain ⟨k', hk', hk'A⟩ := hnext k hk
      exact ⟨k', by omega, hk'A⟩
    | succ m ih =>
      obtain ⟨k, hk, hkA⟩ := ih
      obtain ⟨k', hk', hk'A⟩ := hnext k hkA
      exact ⟨k', by omega, hk'A⟩
  let nx : ℕ → ℕ := fun m => Nat.find (hunb m)
  have hnx : ∀ m, m < nx m ∧ f (nx m) ∈ A := fun m => Nat.find_spec (hunb m)
  have hnxmin : ∀ m k, m < k → f k ∈ A → nx m ≤ k := fun m k h1 h2 => Nat.find_min' (hunb m) ⟨h1, h2⟩
  let idx : ℕ → ℕ := fun q => nx^[q] (Nat.find h0)
  have hidx0 : idx 0 = Nat.find h0 := rfl
  have hidxs : ∀ q, idx (q + 1) = nx (idx q) := fun q => Function.iterate_succ_apply' nx q _
  have hmem : ∀ q, f (idx q) ∈ A := by
    intro q
    cases q with
    | zero => exact Nat.find_spec h0
    | succ q => rw [hidxs]; exact (hnx _).2
  have hmono : StrictMono idx := strictMono_nat_of_lt_succ fun q => by rw [hidxs]; exact (hnx _).1
  have hgap : ∀ q k, f k ∈ A → idx q < k → idx (q + 1) ≤ k := fun q k hk hlt => by
    rw [hidxs]; exact hnxmin _ _ hlt hk
  have hfirst : ∀ k, f k ∈ A → idx 0 ≤ k := fun k hk => Nat.find_min' h0 hk
  have hall : ∀ q n, f n ∈ A → n ≤ idx q → ∃ p, idx p = n := by
    intro q
    induction q with
    | zero => exact fun n hn hle => ⟨0, le_antisymm (hfirst n hn) hle⟩
    | succ q ih =>
      intro n hn hle
      by_cases h : n ≤ idx q
      · exact ih n hn h
      · exact ⟨q + 1, le_antisymm (hgap q n hn (by omega)) hle⟩
  exact ⟨idx, hmono, hmem, fun n hn => hall n n hn (hmono.id_le n), hgap, hfirst⟩

/-- The generating relation `Q = P −̇ P²` of ✱122·44, `P = R_po ⥏ α`, is the successor relation of
the increasing enumeration of `α`. -/
private theorem pm122_44_core {f : ℕ → α} (hf : Injective f) {A : Set α}
    (hA : A ⊆ po (SeqRel f) ʻʻ A) (hne : A.Nonempty) :
    ∃ g : ℕ → α, Injective g ∧
      (po (SeqRel f) ⥏ A) ∸ rsq (po (SeqRel f) ⥏ A) = SeqRel g ∧ Set.range g = A ∧
      (∀ m n, m < n → po (SeqRel f) (g m) (g n)) ∧ (∀ x, x ∈ A → ¬ po (SeqRel f) x (g 0)) := by
  obtain ⟨idx, hmono, hmem, hall, hgap, hfirst⟩ := enum_of_sub_po hf hA hne
  have hsub : ∀ z ∈ A, ∃ n, z = f n := fun z hz => by
    obtain ⟨y, -, hzy⟩ := hA hz
    obtain ⟨m, n, -, rfl, -⟩ := (po_seqRel hf).1 hzy
    exact ⟨m, rfl⟩
  refine ⟨fun q => f (idx q), hf.comp hmono.injective, ?_, ?_, ?_, ?_⟩
  · funext x y
    apply propext
    constructor
    · rintro ⟨⟨⟨hxA, hxy⟩, hyA⟩, hno⟩
      obtain ⟨m, n, hmn, rfl, rfl⟩ := (po_seqRel hf).1 hxy
      obtain ⟨q, rfl⟩ := hall m hxA
      refine ⟨q, rfl, ?_⟩
      have h1 := hgap q n hyA hmn
      rcases Nat.lt_or_ge (idx (q + 1)) n with h2 | h2
      · exact absurd ⟨f (idx (q + 1)), ⟨⟨hxA, (po_seqRel' hf).2 (hmono (Nat.lt_succ_self q))⟩,
          hmem _⟩, ⟨⟨hmem _, (po_seqRel' hf).2 h2⟩, hyA⟩⟩ hno
      · show f n = f (idx (q + 1))
        rw [le_antisymm h2 h1]
    · rintro ⟨q, rfl, rfl⟩
      refine ⟨⟨⟨hmem q, (po_seqRel' hf).2 (hmono (Nat.lt_succ_self q))⟩, hmem (q + 1)⟩, ?_⟩
      rintro ⟨z, ⟨⟨-, hxz⟩, hzA⟩, ⟨⟨-, hzy⟩, -⟩⟩
      obtain ⟨a, k, hak, ha, rfl⟩ := (po_seqRel hf).1 hxz
      obtain ⟨b, c, hbc, hb, hc⟩ := (po_seqRel hf).1 hzy
      rw [← hf ha] at hak
      rw [← hf hb] at hbc
      rw [← hf hc] at hbc
      have := hgap q k hzA hak
      omega
  · ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact hmem q
    · intro hx
      obtain ⟨n, rfl⟩ := hsub x hx
      obtain ⟨q, rfl⟩ := hall n hx
      exact ⟨q, rfl⟩
  · intro m n hmn
    exact (po_seqRel' hf).2 (hmono hmn)
  · intro x hx hpo
    obtain ⟨m, n, hmn, rfl, hn⟩ := (po_seqRel hf).1 hpo
    rw [← hf hn] at hmn
    have := hfirst m hx
    omega

private theorem anc_mono {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) {x y : α}
    (hxy : anc R x y) : anc S x y := by
  obtain ⟨hx, hr⟩ := anc_iff_reflTransGen.1 hxy
  have hr' : Relation.ReflTransGen S x y := by
    clear hxy
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail (h _ _ hbc)
  refine anc_iff_reflTransGen.2 ⟨?_, hr'⟩
  obtain ⟨z, hz | hz⟩ := hx
  exacts [⟨z, Or.inl (h _ _ hz)⟩, ⟨z, Or.inr (h _ _ hz)⟩]

/-- Successor relation of a posterity: shared step of ✱122·51·52. -/
private theorem prog_of_post_seq {P : α → α → Prop} (hfun : ∀ x y z, P x y ∧ P x z → y = z)
    {x : α} {f : ℕ → α} (hf : Injective f) (hstep : ∀ n, P (f n) (f (n + 1)))
    (hrange : rels (anc P) x = Set.range f) : rels (anc P) x ◁ P ∈ Prog := by
  have : rels (anc P) x ◁ P = SeqRel f := by
    funext u v
    apply propext
    constructor
    · rintro ⟨hu, huv⟩
      rw [hrange] at hu
      obtain ⟨n, rfl⟩ := hu
      exact ⟨n, rfl, hfun _ _ _ ⟨huv, hstep n⟩⟩
    · rintro ⟨n, rfl, rfl⟩
      refine ⟨?_, hstep n⟩
      rw [hrange]
      exact ⟨n, rfl⟩
  rw [this]
  exact seqRel_mem_prog hf


/-! ### `ℵ₀` as the countably infinite classes -/

private theorem mem_aleph0_iff_ci {A : Set α} : A ∈ aleph0 ↔ A.Countable ∧ A.Infinite := by
  constructor
  · intro h
    obtain ⟨f, hf, rfl⟩ := mem_aleph0_iff.1 h
    exact ⟨Set.countable_range f, Set.infinite_range_of_injective hf⟩
  · rintro ⟨hc, hi⟩
    have : Countable A := hc.to_subtype
    have : Infinite A := Set.infinite_coe_iff.2 hi
    obtain ⟨_⟩ : Nonempty (Denumerable A) :=
      nonempty_denumerable_iff.2 ⟨inferInstance, inferInstance⟩
    exact mem_aleph0_iff_equiv.2 ⟨(Denumerable.eqv A).symm⟩

private theorem aleph0_eq_nc {A : Set α} (hA : A ∈ aleph0) : (aleph0 : Set (Set γ)) = nc γ A := by
  ext B
  rw [mem_nc]
  exact ⟨fun hB => sm_of_aleph0 hB hA, fun h => aleph0_of_sm hA (sm_symm h)⟩

private theorem aleph0_eq_n₀c {A : Set α} (hA : A ∈ aleph0) : (aleph0 : Set (Set α)) = n₀c A := by
  rw [n₀c_eq_nc]
  exact aleph0_eq_nc hA

private theorem exists_mem_aleph0 [Infinite α] : ∃ A : Set α, A ∈ aleph0 :=
  aleph0_nonempty_iff.2 inferInstance

private theorem fres_univ (P : α → α → Prop) : P ⥏ Set.univ = P := by
  funext x y
  apply propext
  exact ⟨fun h => h.1.2, fun h => ⟨⟨Set.mem_univ x, h⟩, Set.mem_univ y⟩⟩

private theorem typ2_eq_univ (x : α) : typ2 x = Set.univ := typ_eq_univ _

private theorem typ3_eq_univ (x : α) : typ3 x = Set.univ := typ_eq_univ _

private theorem clsT2_eq (A : Set (Set α)) (x : α) : clsT2 A x = A := by
  rw [clsT2, typ_eq_univ, Set.inter_univ]

/-! ### Countable and infinite class-sums and class-products -/

private theorem countable_infinite_clsSum {A : Set α} {B : Set β} (hA : A ∈ aleph0)
    (hB : B.Countable) : (A +ₐ B) ∈ aleph0 := by
  obtain ⟨hAc, hAi⟩ := mem_aleph0_iff_ci.1 hA
  have : Countable A := hAc.to_subtype
  have : Countable B := hB.to_subtype
  have : Infinite A := Set.infinite_coe_iff.2 hAi
  have hc : Countable (A ⊕ B) := inferInstance
  have hi : Infinite (A ⊕ B) := Infinite.of_injective Sum.inl Sum.inl_injective
  refine mem_aleph0_iff_ci.2 ⟨Set.countable_coe_iff.1 (Countable.of_equiv _ (clsSumEquiv A B).symm),
    Set.infinite_coe_iff.1 (Infinite.of_injective _ (clsSumEquiv A B).symm.injective)⟩

private theorem mem_clsTimes {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ∈ B ×ₐ A ↔ ∃ x y, (x ∈ A ∧ y ∈ B) ∧ R = x ↓ y := by
  constructor
  · rintro ⟨S, ⟨y, hy, hS⟩, hR⟩
    have hS' : S = opImg couple A y := hS
    rw [hS'] at hR
    obtain ⟨x, hx, hRx⟩ := hR
    exact ⟨x, y, ⟨hx, hy⟩, hRx⟩
  · rintro ⟨x, y, hxy, rfl⟩
    exact couple_mem_clsTimes.2 hxy

/-- `β × α` is equivalent to the product type (cf. ✱113·101). -/
private noncomputable def clsTimesEquiv (B : Set β) (A : Set α) : ↥(B ×ₐ A) ≃ A × B :=
  (Equiv.ofBijective (fun p : A × B => (⟨(p.1 : α) ↓ (p.2 : β),
      couple_mem_clsTimes.2 ⟨p.1.2, p.2.2⟩⟩ : ↥(B ×ₐ A)))
    ⟨fun p q h => by
      have h' := congrArg Subtype.val h
      obtain ⟨h1, h2⟩ := couple_eq_couple_iff.1 h'
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2),
    fun ⟨R, hR⟩ => by
      obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := mem_clsTimes.1 hR
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩⟩).symm

private theorem sm_clsTimes {A : Set α} {B : Set β} {A' : Set γ} {B' : Set δ} (hA : sm A A')
    (hB : sm B B') : sm (A ×ₐ B) (A' ×ₐ B') := by
  obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 hA
  obtain ⟨eB⟩ := sm_iff_nonempty_equiv.1 hB
  exact sm_iff_nonempty_equiv.2
    ⟨(clsTimesEquiv A B).trans ((eB.prodCongr eA).trans (clsTimesEquiv A' B').symm)⟩

private theorem n₀c_cardMul_n₀c (A : Set α) (B : Set β) :
    (n₀c A ×ᶜ n₀c B : Set (Set γ)) = nc γ (A ×ₐ B) := by
  ext ξ
  constructor
  · rintro ⟨A', B', ⟨hA, hB⟩, h⟩
    have hA' : sm A A' := mem_n₀c.1 (hA ▸ self_mem_n₀c A)
    have hB' : sm B B' := mem_n₀c.1 (hB ▸ self_mem_n₀c B)
    exact sm_trans h (sm_clsTimes (sm_symm hA') (sm_symm hB'))
  · intro h
    exact ⟨A, B, ⟨rfl, rfl⟩, h⟩

private theorem cardMul_eq_empty_of_left {μ : Set (Set α)} (hm : ¬ μ.Nonempty) (ν : Set (Set β)) :
    (μ ×ᶜ ν : Set (Set γ)) = ∅ := by
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨hA, -⟩, -⟩
  exact hm (hA ▸ n₀c_nonempty A)

private theorem cardMul_eq_empty_of_right (μ : Set (Set α)) {ν : Set (Set β)} (hn : ¬ ν.Nonempty) :
    (μ ×ᶜ ν : Set (Set γ)) = ∅ := by
  ext ξ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨-, hB⟩, -⟩
  exact hn (hB ▸ n₀c_nonempty B)

/-! ### The successor relation `N` of ✱123·02 -/

private theorem cardN_add_one {X : Type*} (k : ℕ) :
    (cardN X k +ᶜ (one : Set (Set X)) : Set (Set X)) = cardN X (k + 1) := by
  by_cases h : (cardN X (k + 1)).Nonempty
  · obtain ⟨b⟩ := nonempty_of_cardN_succ h
    rw [one_eq_cardN, cardAdd_cardN_of_nonempty (cardN_mono_nonempty (Nat.le_succ k) h)
      (cardN_one_nonempty b)]
  · rw [Set.not_nonempty_iff_eq_empty.1 h]
    by_cases hk : (cardN X k).Nonempty
    · by_cases hX : Nonempty X
      · obtain ⟨b⟩ := hX
        rw [one_eq_cardN, cardAdd_cardN_of_nonempty hk (cardN_one_nonempty b)]
        exact Set.not_nonempty_iff_eq_empty.1 h
      · refine cardAdd_eq_empty_of_empty_right _ ?_
        rintro ⟨B, y, rfl⟩
        exact hX ⟨y⟩
    · exact cardAdd_eq_empty_of_empty_left hk _

private theorem nsucc_eq_seqRel {X : Type*} :
    (Nsucc : Set (Set X) → Set (Set X) → Prop) = SeqRel (cardN X) := by
  funext μ ν
  apply propext
  show μ ∈ NCinduct ∧ ν = (μ +ᶜ (one : Set (Set X)) : Set (Set X)) ∩ typ₀ μ ↔ _
  rw [typ₀_eq_univ, Set.inter_univ, mem_NCinduct_iff_cardN]
  constructor
  · rintro ⟨⟨k, rfl⟩, rfl⟩
    exact ⟨k, rfl, cardN_add_one k⟩
  · rintro ⟨k, rfl, rfl⟩
    exact ⟨⟨k, rfl⟩, (cardN_add_one k).symm⟩

private theorem cardN_injective {X : Type*} [Infinite X] : Injective (cardN X) :=
  fun m _ h => cardN_inj (cardN_nonempty_of_infinite m) h

private theorem NCinduct_eq_range {X : Type*} :
    (NCinduct : Set (Set (Set X))) = Set.range (cardN X) := by
  ext μ
  rw [mem_NCinduct_iff_cardN]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

private theorem NCinduct_mem_aleph0 {X : Type*} [Infinite X] :
    (NCinduct : Set (Set (Set X))) ∈ aleph0 := by
  rw [NCinduct_eq_range]
  exact mem_aleph0_iff.2 ⟨_, cardN_injective, rfl⟩

/-- The members of a homogeneous cardinal of a finite class. -/
private theorem n₀c_finite_ne_aleph0 {A B : Set α} (hA : A.Finite) (hB : B ∈ aleph0) :
    n₀c A ≠ n₀c B := by
  intro h
  have : B ∈ n₀c A := h ▸ self_mem_n₀c B
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (mem_n₀c.1 this)
  have : Finite A := hA.to_subtype
  exact (infinite_of_aleph0 hB) (Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm))

/-- `ℵ₀` is not an inductive cardinal. -/
private theorem aleph0_not_mem_NCinduct (hne : (aleph0 : Set (Set α)).Nonempty) :
    (aleph0 : Set (Set α)) ∉ NCinduct := by
  obtain ⟨B, hB⟩ := hne
  rw [aleph0_eq_n₀c hB]
  intro h
  rcases NCinduct_cases h with ⟨A, hA, he⟩ | ⟨hfin, -⟩
  · exact n₀c_finite_ne_aleph0 hA hB he.symm
  · obtain ⟨f, hf, -⟩ := mem_aleph0_iff.1 hB
    exact (not_finite_iff_infinite.2 (Infinite.of_injective f hf)) hfin

/-- `ℵ₀ > ν` for an existent inductive `ν`. -/
private theorem aleph0_cardGt_cardN {X : Type*} {B : Set α} (hB : B ∈ aleph0) {k : ℕ}
    (hk : (cardN X k).Nonempty) : n₀c B >ᶜ cardN X k := by
  obtain ⟨C, hC⟩ := hk
  rw [cardN_eq_n₀c hC, cardGt_n₀c_iff]
  have : Finite C := hC.1.to_subtype
  have : Infinite B := Set.infinite_coe_iff.2 (infinite_of_aleph0 hB)
  have hno : ¬ Nonempty (B ↪ C) := fun ⟨e⟩ =>
    not_finite_iff_infinite.2 (Infinite.of_injective e e.injective) ‹Finite C›
  exact ⟨(Function.Embedding.total C B).resolve_right hno, hno⟩

private theorem rtg_seqRel_of_le (f : ℕ → α) {m n : ℕ} (h : m ≤ n) :
    Relation.ReflTransGen (SeqRel f) (f m) (f n) := by
  induction n, h using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ k _ ih => exact ih.tail (seqRel_apply f k)

private theorem nsucc_iff {X : Type*} {μ ν : Set (Set X)} :
    Nsucc μ ν ↔ μ ∈ NCinduct ∧ ν = (μ +ᶜ (one : Set (Set X)) : Set (Set X)) := by
  show μ ∈ NCinduct ∧ ν = (μ +ᶜ (one : Set (Set X)) : Set (Set X)) ∩ typ₀ μ ↔ _
  rw [typ₀_eq_univ, Set.inter_univ]

private theorem aleph0_of_clsSum_left {A : Set α} {B : Set β} (h : (A +ₐ B) ∈ aleph0)
    (hB : B.Finite) : A ∈ aleph0 := by
  obtain ⟨hc, hi⟩ := mem_aleph0_iff_ci.1 h
  have : Countable ↥(A +ₐ B) := hc.to_subtype
  have : Countable (A ⊕ B) := Countable.of_equiv _ (clsSumEquiv A B)
  refine mem_aleph0_iff_ci.2 ⟨Set.countable_coe_iff.1
    (Function.Injective.countable (f := (Sum.inl : A → A ⊕ B)) Sum.inl_injective), fun hA => hi ?_⟩
  have : Finite A := hA.to_subtype
  have : Finite B := hB.to_subtype
  have := Fintype.ofFinite A
  have := Fintype.ofFinite B
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ (clsSumEquiv A B).symm)

private theorem countable_infinite_clsTimes {A : Set α} {B : Set β} (hA : A ∈ aleph0)
    (hB : B.Countable) (hBne : B.Nonempty) : (B ×ₐ A) ∈ aleph0 := by
  obtain ⟨hAc, hAi⟩ := mem_aleph0_iff_ci.1 hA
  have : Countable A := hAc.to_subtype
  have : Countable B := hB.to_subtype
  have : Infinite A := Set.infinite_coe_iff.2 hAi
  obtain ⟨b, hb⟩ := hBne
  have hi : Infinite (A × B) :=
    Infinite.of_injective (fun a => (a, (⟨b, hb⟩ : B))) (fun a a' h => congrArg Prod.fst h)
  refine mem_aleph0_iff_ci.2 ⟨Set.countable_coe_iff.1
    (Countable.of_equiv _ (clsTimesEquiv B A).symm),
    Set.infinite_coe_iff.1 (Infinite.of_injective _ (clsTimesEquiv B A).symm.injective)⟩

/-- `ℵ₀ −_c N₀c'β = ℵ₀` for a finite `β`. -/
private theorem cardSub_aleph0 {W X : Type*} (hW : (aleph0 : Set (Set W)).Nonempty) {B : Set X}
    (hB : B.Finite) : ((aleph0 : Set (Set W)) -ᶜ n₀c B : Set (Set γ)) = aleph0 := by
  obtain ⟨A, hA⟩ := hW
  ext ξ
  show (n₀c ξ +ᶜ n₀c B : Set (Set W)) = aleph0 ∧ (n₀c ξ +ᶜ n₀c B : Set (Set W)).Nonempty ↔
    ξ ∈ aleph0
  rw [n₀c_cardAdd_n₀c, aleph0_eq_nc (γ := W) hA]
  constructor
  · rintro ⟨he, hne⟩
    rw [nc_eq_nc_iff hne] at he
    exact aleph0_of_clsSum_left (aleph0_of_sm hA (sm_symm he)) hB
  · intro hξ
    have hs : (ξ +ₐ B) ∈ aleph0 := countable_infinite_clsSum hξ hB.countable
    have : nc W (ξ +ₐ B) = nc W A := nc_eq_nc_of_sm (sm_of_aleph0 hs hA)
    refine ⟨this, ?_⟩
    rw [this]
    exact ⟨A, self_mem_nc A⟩

/-- Conjugating a progression by a one-one relation. -/
private theorem conj_seqRel {f : ℕ → α} (hf : Injective f) {S : β → α → Prop}
    (h11 : S ∈ arrow one one) (hcd : codom S = Set.range f) :
    ∃ g : ℕ → β, Injective g ∧ S ⨾ SeqRel f ⨾ S˘ = SeqRel g ∧ dom S = Set.range g ∧
      ∀ u, S u (f 0) ↔ u = g 0 := by
  obtain ⟨hinj, hfun⟩ := mem_arrow_one_one.1 h11
  have hex : ∀ n, ∃ u, S u (f n) := fun n => by
    have : f n ∈ codom S := by rw [hcd]; exact ⟨n, rfl⟩
    exact this
  choose g hg using hex
  have huniq : ∀ n u, S u (f n) ↔ u = g n := fun n u =>
    ⟨fun h => hinj _ _ _ ⟨h, hg n⟩, fun h => h ▸ hg n⟩
  refine ⟨g, fun m n h => hf (hfun (g m) (f m) (f n) ⟨hg m, by rw [h]; exact hg n⟩), ?_, ?_,
    huniq 0⟩
  · funext u v
    apply propext
    constructor
    · rintro ⟨y, ⟨x, hux, n, rfl, rfl⟩, hvy⟩
      exact ⟨n, (huniq n u).1 hux, (huniq (n + 1) v).1 hvy⟩
    · rintro ⟨n, rfl, rfl⟩
      exact ⟨f (n + 1), ⟨f n, hg n, seqRel_apply f n⟩, hg (n + 1)⟩
  · ext u
    constructor
    · rintro ⟨x, hux⟩
      have : x ∈ codom S := ⟨u, hux⟩
      rw [hcd] at this
      obtain ⟨n, rfl⟩ := this
      exact ⟨n, ((huniq n u).1 hux).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨f n, hg n⟩

private theorem infinite_set_of_infinite [Infinite α] : Infinite (Set α) :=
  Infinite.of_injective (fun a : α => ({a} : Set α)) (fun _ _ h => Set.singleton_injective h)


/-! ### Exponentiation: `α exp β` is the class of the functions from `β` to `α` -/

private theorem mem_opImg_couple {A : Set α} {y : β} {R : α → β → Prop} :
    R ∈ opImg couple A y ↔ ∃ x, x ∈ A ∧ R = x ↓ y := Iff.rfl

/-- The class of couples `h'y ↓ y` of a function `h : β → α`. -/
private def expFun (A : Set α) (B : Set β) (h : B → A) : Set (α → β → Prop) :=
  {R | ∃ y : B, R = (h y : α) ↓ (y : β)}

private theorem expFun_mem {A : Set α} {B : Set β} (h : B → A) : expFun A B h ∈ clsExp A B := by
  refine ⟨fun R C => C ∈ coupleImg A ʻʻ B ∧ R ∈ C ∧ R ∈ expFun A B h, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [mem_arrow_one_Cls]
    rintro R R' C ⟨⟨⟨y₀, -, hC⟩, hRC, ⟨y, rfl⟩⟩, ⟨-, hR'C, ⟨y', rfl⟩⟩⟩
    have hC' : C = opImg couple A y₀ := hC
    rw [hC'] at hRC hR'C
    obtain ⟨x, -, hx⟩ := hRC
    obtain ⟨x', -, hx'⟩ := hR'C
    obtain ⟨-, e1⟩ := couple_eq_couple_iff.1 hx
    obtain ⟨-, e2⟩ := couple_eq_couple_iff.1 hx'
    have : y = y' := Subtype.ext (e1.trans e2.symm)
    rw [this]
  · rintro R C ⟨-, hRC, -⟩
    exact hRC
  · show coupleImg A ʻʻ B = codom _
    ext C
    constructor
    · intro hC
      have hCκ := hC
      obtain ⟨y₀, hy₀, hC'⟩ := hC
      have hC'' : C = opImg couple A y₀ := hC'
      refine ⟨(h ⟨y₀, hy₀⟩ : α) ↓ y₀, hCκ, ?_, ⟨y₀, hy₀⟩, rfl⟩
      rw [hC'']
      exact ⟨_, (h ⟨y₀, hy₀⟩).2, rfl⟩
    · rintro ⟨R, hC, -⟩
      exact hC
  · show expFun A B h = dom _
    ext R
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨opImg couple A y, ⟨y, y.2, rfl⟩, ⟨_, (h y).2, rfl⟩, ⟨y, rfl⟩⟩
    · rintro ⟨C, -, -, hR⟩
      exact hR

private theorem exists_expFun {A : Set α} {B : Set β} {ξ : Set (α → β → Prop)}
    (hξ : ξ ∈ clsExp A B) : ∃ h : B → A, ξ = expFun A B h := by
  obtain ⟨M, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := hξ
  have h3' : coupleImg A ʻʻ B = codom M := h3
  have hone := mem_arrow_one_Cls.1 h1
  have hex : ∀ y : B, ∃ x : A, M ((x : α) ↓ (y : β)) (opImg couple A y) := by
    intro y
    have hC : opImg couple A (y : β) ∈ codom M := by rw [← h3']; exact ⟨y, y.2, rfl⟩
    obtain ⟨R, hR⟩ := hC
    obtain ⟨x, hx, rfl⟩ := mem_opImg_couple.1 (h2 _ _ hR)
    exact ⟨⟨x, hx⟩, hR⟩
  choose h hh using hex
  refine ⟨h, Set.ext fun R => ⟨?_, ?_⟩⟩
  · rintro ⟨C, hRC⟩
    have hC : C ∈ codom M := ⟨R, hRC⟩
    rw [← h3'] at hC
    obtain ⟨y, hy, hCy⟩ := hC
    have hCy' : C = opImg couple A y := hCy
    subst hCy'
    exact ⟨⟨y, hy⟩, hone _ _ _ ⟨hRC, hh ⟨y, hy⟩⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, hh y⟩

private theorem expFun_injective {A : Set α} {B : Set β} : Injective (expFun A B) := by
  intro h h' e
  funext y
  have hy : (h y : α) ↓ (y : β) ∈ expFun A B h' := by rw [← e]; exact ⟨y, rfl⟩
  obtain ⟨y', hy'⟩ := hy
  obtain ⟨e1, e2⟩ := couple_eq_couple_iff.1 hy'
  have : y = y' := Subtype.ext e2
  subst this
  exact Subtype.ext e1

/-- `α exp β` is equivalent to the type of functions from `β` to `α` (cf. ✱116·15). -/
private noncomputable def clsExpEquiv (A : Set α) (B : Set β) : ↥(clsExp A B) ≃ (B → A) :=
  (Set.equivOfEq (show clsExp A B = Set.range (expFun A B) from Set.ext fun _ =>
    ⟨fun hξ => let ⟨h, e⟩ := exists_expFun hξ; ⟨h, e.symm⟩,
      fun ⟨h, e⟩ => e ▸ expFun_mem h⟩)).trans (Equiv.ofInjective _ expFun_injective).symm

private theorem sm_clsExp {A : Set α} {B : Set β} {A' : Set γ} {B' : Set δ} (hA : sm A A')
    (hB : sm B B') : sm (clsExp A B) (clsExp A' B') := by
  obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 hA
  obtain ⟨eB⟩ := sm_iff_nonempty_equiv.1 hB
  exact sm_iff_nonempty_equiv.2
    ⟨(clsExpEquiv A B).trans ((Equiv.arrowCongr eB eA).trans (clsExpEquiv A' B').symm)⟩

private theorem n₀c_cardExp_n₀c (A : Set α) (B : Set β) :
    (n₀c A ^ᶜ n₀c B : Set (Set γ)) = nc γ (clsExp A B) := by
  ext ξ
  constructor
  · rintro ⟨A', B', ⟨hA, hB⟩, h⟩
    have hA' : sm A A' := mem_n₀c.1 (hA ▸ self_mem_n₀c A)
    have hB' : sm B B' := mem_n₀c.1 (hB ▸ self_mem_n₀c B)
    exact sm_trans h (sm_clsExp (sm_symm hA') (sm_symm hB'))
  · intro h
    exact ⟨A, B, ⟨rfl, rfl⟩, h⟩

private theorem clsExp_mem_aleph0 {A : Set α} {B : Set β} (hA : A ∈ aleph0) (hB : B.Finite)
    (hBne : B.Nonempty) : clsExp A B ∈ aleph0 := by
  obtain ⟨hAc, hAi⟩ := mem_aleph0_iff_ci.1 hA
  have : Countable A := hAc.to_subtype
  have : Infinite A := Set.infinite_coe_iff.2 hAi
  have : Finite B := hB.to_subtype
  obtain ⟨b, hb⟩ := hBne
  have hi : Infinite (B → A) :=
    Infinite.of_injective (fun a : A => fun _ : B => a) (fun a a' h => congrFun h ⟨b, hb⟩)
  exact mem_aleph0_iff_ci.2 ⟨Set.countable_coe_iff.1 (Countable.of_equiv _ (clsExpEquiv A B).symm),
    Set.infinite_coe_iff.1 (Infinite.of_injective _ (clsExpEquiv A B).symm.injective)⟩

/-! ### The diagonal enumeration of `ℕ × ℕ` (✱123·5) -/

private def tri : ℕ → ℕ
  | 0 => 0
  | s + 1 => tri s + s + 1

/-- The successor of a pair in PM's enumeration: `(i, j + 1) ↦ (i + 1, j)`, `(i, 0) ↦ (0, i + 1)`. -/
private def dnext : ℕ × ℕ → ℕ × ℕ
  | (i, 0) => (0, i + 1)
  | (i, j + 1) => (i + 1, j)

private def dpos : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 => dnext (dpos n)

private def didx (p : ℕ × ℕ) : ℕ := tri (p.1 + p.2) + p.1

private theorem didx_dnext (p : ℕ × ℕ) : didx (dnext p) = didx p + 1 := by
  obtain ⟨i, j⟩ := p
  cases j with
  | zero =>
    show tri (0 + (i + 1)) + 0 = tri (i + 0) + i + 1
    rw [Nat.zero_add, Nat.add_zero, Nat.add_zero]
    rfl
  | succ j =>
    show tri (i + 1 + j) + (i + 1) = tri (i + (j + 1)) + i + 1
    rw [show i + 1 + j = i + (j + 1) by omega]
    omega

private theorem didx_dpos (n : ℕ) : didx (dpos n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => show didx (dnext (dpos n)) = n + 1; rw [didx_dnext, ih]

private theorem dpos_injective : Injective dpos := fun m n h => by
  rw [← didx_dpos m, ← didx_dpos n, h]

private theorem dpos_surjective : Function.Surjective dpos := by
  have key : ∀ s i, i ≤ s → ∃ n, dpos n = (i, s - i) := by
    intro s
    induction s with
    | zero => intro i hi; exact ⟨0, by rw [show i = 0 by omega]; rfl⟩
    | succ s ih =>
      intro i
      induction i with
      | zero =>
        intro _
        obtain ⟨n, hn⟩ := ih s le_rfl
        refine ⟨n + 1, ?_⟩
        show dnext (dpos n) = (0, s + 1 - 0)
        rw [hn, Nat.sub_self]
        rfl
      | succ i ihi =>
        intro hi
        obtain ⟨n, hn⟩ := ihi (by omega)
        refine ⟨n + 1, ?_⟩
        show dnext (dpos n) = (i + 1, s + 1 - (i + 1))
        rw [hn, show s + 1 - i = (s - i) + 1 by omega]
        show (i + 1, s - i) = (i + 1, s + 1 - (i + 1))
        rw [show s + 1 - (i + 1) = s - i by omega]
  rintro ⟨i, j⟩
  obtain ⟨n, hn⟩ := key (i + j) i (by omega)
  exact ⟨n, by rw [hn, show i + j - i = j by omega]⟩

private theorem dnext_injective : Injective dnext := fun p q h => by
  obtain ⟨m, rfl⟩ := dpos_surjective p
  obtain ⟨n, rfl⟩ := dpos_surjective q
  have : m + 1 = n + 1 := by
    have h1 := didx_dpos (m + 1)
    have h2 := didx_dpos (n + 1)
    show m + 1 = n + 1
    rw [← h1, ← h2]
    exact congrArg didx h
  rw [show m = n by omega]

/-- `ψ(ν_R)` for a progression `R`, any `ν`. -/
private theorem desc_nuP_seqRel_iff {X : Type*} {f : ℕ → α} (hf : Injective f) {μ : Set (Set X)}
    (ψ : α → Prop) :
    Desc (nuP μ) (SeqRel f) ψ ↔ ∃ k, (μ = cardN X (k + 1) ∧ (cardN X (k + 1)).Nonempty) ∧ ψ (f k) := by
  constructor
  · intro h
    have hE : EDesc (nuP μ) (SeqRel f) := (TheIs_iff.1 h).1
    obtain ⟨k, rfl, hk⟩ := cardN_of_EDesc_nuP hf hE
    exact ⟨k, ⟨rfl, hk⟩, (desc_nuP_seqRel hf hk ψ).1 h⟩
  · rintro ⟨k, ⟨rfl, hk⟩, hψ⟩
    exact (desc_nuP_seqRel hf hk ψ).2 hψ

/-- The relation of ✱123·5. -/
private def rel1235 (M N W₁ W₂ : Type*) (P : α → α → Prop) (Q : β → β → Prop) :
    (α → β → Prop) → (α → β → Prop) → Prop :=
  fun X Y => ∃ (μ : Set (Set M)) (ν : Set (Set N)),
    (Desc (nuP μ) P (fun a => Desc (nuP ν) Q (fun b => X = a ↓ b)) ∧
      Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) P
        (fun a => Desc (nuP (ν -ᶜ (one : Set (Set N)) : Set (Set N))) Q (fun b => Y = a ↓ b))) ∨
    (Desc (nuP μ) P (fun a => Desc (nuP (one : Set (Set W₁))) Q (fun b => X = a ↓ b)) ∧
      Desc (nuP (one : Set (Set W₂))) P
        (fun a => Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) Q (fun b => Y = a ↓ b)))

private theorem rel1235_fwd {M N W₁ W₂ : Type*} {f : ℕ → α} (hf : Injective f) {g : ℕ → β}
    (hg : Injective g) {X Y : α → β → Prop} (h : rel1235 M N W₁ W₂ (SeqRel f) (SeqRel g) X Y) :
    ∃ p : ℕ × ℕ, X = f p.1 ↓ g p.2 ∧ Y = f (dnext p).1 ↓ g (dnext p).2 := by
  obtain ⟨μ, ν, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · obtain ⟨i, ⟨rfl, hi⟩, h1'⟩ := (desc_nuP_seqRel_iff hf _).1 h1
    obtain ⟨j, ⟨rfl, hj⟩, rfl⟩ := (desc_nuP_seqRel_iff hg _).1 h1'
    rw [cardN_add_one, cardSub_one_cardN hj] at h2
    obtain ⟨k, ⟨hk, hkne⟩, h2'⟩ := (desc_nuP_seqRel_iff hf _).1 h2
    obtain ⟨l, ⟨hl, hlne⟩, rfl⟩ := (desc_nuP_seqRel_iff hg _).1 h2'
    have e1 : k + 1 = i + 1 + 1 := cardN_inj hkne hk.symm
    have e2 : l + 1 = j := cardN_inj hlne hl.symm
    subst e2
    refine ⟨(i, l + 1), rfl, ?_⟩
    rw [show k = i + 1 by omega]
    rfl
  · obtain ⟨i, ⟨rfl, hi⟩, h1'⟩ := (desc_nuP_seqRel_iff hf _).1 h1
    obtain ⟨j, ⟨hj, hjne⟩, rfl⟩ := (desc_nuP_seqRel_iff hg _).1 h1'
    rw [one_eq_cardN] at hj
    have ej : j = 0 := by have := cardN_inj hjne hj.symm; omega
    subst ej
    obtain ⟨k, ⟨hk, hkne⟩, h2'⟩ := (desc_nuP_seqRel_iff hf _).1 h2
    rw [one_eq_cardN] at hk
    have ek : k = 0 := by have := cardN_inj hkne hk.symm; omega
    subst ek
    rw [cardN_add_one] at h2'
    obtain ⟨l, ⟨hl, hlne⟩, rfl⟩ := (desc_nuP_seqRel_iff hg _).1 h2'
    have el : l + 1 = i + 1 + 1 := cardN_inj hlne hl.symm
    refine ⟨(i, 0), rfl, ?_⟩
    rw [show l = i + 1 by omega]
    rfl

private theorem rel1235_bwd {M N W₁ W₂ : Type*} [Infinite M] [Infinite N] [Nonempty W₁]
    [Nonempty W₂] {f : ℕ → α} (hf : Injective f) {g : ℕ → β} (hg : Injective g) (p : ℕ × ℕ) :
    rel1235 M N W₁ W₂ (SeqRel f) (SeqRel g) (f p.1 ↓ g p.2) (f (dnext p).1 ↓ g (dnext p).2) := by
  obtain ⟨i, j⟩ := p
  cases j with
  | zero =>
    refine ⟨cardN M (i + 1), cardN N 1, Or.inr ⟨?_, ?_⟩⟩
    · rw [desc_nuP_seqRel hf (cardN_nonempty_of_infinite _), desc_nuP_one_seqRel hg]
    · rw [desc_nuP_one_seqRel hf, cardN_add_one, desc_nuP_seqRel hg (cardN_nonempty_of_infinite _)]
      rfl
  | succ j =>
    refine ⟨cardN M (i + 1), cardN N (j + 1 + 1), Or.inl ⟨?_, ?_⟩⟩
    · rw [desc_nuP_seqRel hf (cardN_nonempty_of_infinite _),
        desc_nuP_seqRel hg (cardN_nonempty_of_infinite _)]
    · rw [cardN_add_one, cardSub_one_cardN (cardN_nonempty_of_infinite _),
        desc_nuP_seqRel hf (cardN_nonempty_of_infinite _),
        desc_nuP_seqRel hg (cardN_nonempty_of_infinite _)]
      rfl

/-- Under the conventions, the relation of ✱123·5 is a progression enumerating the couples. -/
private theorem rel1235_eq {M N W₁ W₂ : Type*} [Infinite M] [Infinite N] [Nonempty W₁]
    [Nonempty W₂] {f : ℕ → α} (hf : Injective f) {g : ℕ → β} (hg : Injective g) :
    rel1235 M N W₁ W₂ (SeqRel f) (SeqRel g) =
      SeqRel (fun n => f (dpos n).1 ↓ g (dpos n).2) := by
  have hE : Injective (fun p : ℕ × ℕ => f p.1 ↓ g p.2) := fun p q h => by
    obtain ⟨h1, h2⟩ := couple_eq_couple_iff.1 h
    exact Prod.ext (hf h1) (hg h2)
  funext X Y
  apply propext
  constructor
  · intro h
    obtain ⟨p, rfl, rfl⟩ := rel1235_fwd hf hg h
    obtain ⟨n, rfl⟩ := dpos_surjective p
    exact ⟨n, rfl, rfl⟩
  · rintro ⟨n, rfl, rfl⟩
    exact rel1235_bwd hf hg (dpos n)


/-! ### Reflexive classes are the infinite classes -/

private theorem exists_aleph0_sub {ρ : Set α} (hρ : ρ.Infinite) : ∃ C, C ∈ aleph0 ∧ C ⊆ ρ := by
  let e := hρ.natEmbedding
  refine ⟨Set.range (fun n => (e n : α)), mem_aleph0_iff.2 ⟨_, ?_, rfl⟩, ?_⟩
  · exact Subtype.val_injective.comp e.injective
  · rintro _ ⟨n, rfl⟩
    exact (e n).2

/-- An infinite class is similar to itself less one term, by a one-one relation with a
beginning: the construction behind ✱124·1·17. -/
private theorem exists_shift {ρ : Set α} (hρ : ρ.Infinite) {x : α} (hx : x ∈ ρ) :
    ∃ R : α → α → Prop, R ∈ arrow one one ∧ dom R = ρ ∧ codom R = ρ \ ι x := by
  classical
  have hρ' : (ρ \ ι x).Infinite := hρ.sdiff (Set.finite_singleton x)
  let e := hρ'.natEmbedding
  obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → α, f 0 = x ∧ ∀ m, f (m + 1) = e m :=
    ⟨fun n => Nat.casesOn n x (fun m => (e m : α)), rfl, fun m => rfl⟩
  have hfρ : ∀ n, f n ∈ ρ := fun n => by
    cases n with
    | zero => rw [hf0]; exact hx
    | succ m => rw [hfs]; exact (e m).2.1
  have hfinj : Function.Injective f := by
    intro a b h
    cases a with
    | zero =>
      cases b with
      | zero => rfl
      | succ b =>
        rw [hf0, hfs] at h
        exact absurd (mem_unitCls.2 h.symm) (e b).2.2
    | succ a =>
      cases b with
      | zero =>
        rw [hf0, hfs] at h
        exact absurd (mem_unitCls.2 h) (e a).2.2
      | succ b =>
        rw [hfs, hfs] at h
        have : e a = e b := Subtype.ext h
        rw [e.injective this]
  let R : α → α → Prop := fun u v => (∃ n, u = f n ∧ v = f (n + 1)) ∨
    ((u ∈ ρ ∧ u ∉ Set.range f) ∧ v = u)
  refine ⟨R, mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · intro u u' v ⟨h1, h2⟩
    rcases h1 with ⟨n, hu, hv⟩ | ⟨⟨-, hur⟩, hvu⟩ <;>
      rcases h2 with ⟨n', hu', hv'⟩ | ⟨⟨-, hur'⟩, hvu'⟩
    · rw [hu, hu', show n = n' by have := hfinj (hv.symm.trans hv'); omega]
    · exact absurd ⟨n + 1, hv.symm.trans hvu'⟩ hur'
    · exact absurd ⟨n' + 1, hv'.symm.trans hvu⟩ hur
    · rw [← hvu, hvu']
  · intro u v v' ⟨h1, h2⟩
    rcases h1 with ⟨n, hu, hv⟩ | ⟨⟨-, hur⟩, hvu⟩ <;>
      rcases h2 with ⟨n', hu', hv'⟩ | ⟨⟨-, hur'⟩, hvu'⟩
    · rw [hv, hv', hfinj (hu.symm.trans hu')]
    · exact absurd ⟨n, hu.symm⟩ hur'
    · exact absurd ⟨n', hu'.symm⟩ hur
    · rw [hvu, hvu']
  · ext u
    constructor
    · rintro ⟨v, ⟨n, rfl, -⟩ | ⟨⟨hu, -⟩, -⟩⟩
      · exact hfρ n
      · exact hu
    · intro hu
      by_cases hr : u ∈ Set.range f
      · obtain ⟨n, rfl⟩ := hr
        exact ⟨_, Or.inl ⟨n, rfl, rfl⟩⟩
      · exact ⟨u, Or.inr ⟨⟨hu, hr⟩, rfl⟩⟩
  · ext v
    constructor
    · rintro ⟨u, ⟨n, rfl, rfl⟩ | ⟨⟨hu, hr⟩, rfl⟩⟩
      · exact ⟨hfρ _, fun h => Nat.succ_ne_zero n (hfinj ((mem_unitCls.1 h).trans hf0.symm))⟩
      · exact ⟨hu, fun h => hr ⟨0, hf0.trans (mem_unitCls.1 h).symm⟩⟩
    · rintro ⟨hv, hvx⟩
      by_cases hr : v ∈ Set.range f
      · obtain ⟨n, rfl⟩ := hr
        cases n with
        | zero => exact absurd (mem_unitCls.2 hf0) hvx
        | succ m => exact ⟨f m, Or.inl ⟨m, rfl, rfl⟩⟩
      · exact ⟨v, Or.inr ⟨⟨hv, hr⟩, rfl⟩⟩

private theorem post_injective {P : α → α → Prop} (hinj : ∀ x y z, P x z ∧ P y z → x = y)
    {f : ℕ → α} (hstep : ∀ n, P (f n) (f (n + 1))) (h0 : ¬ po P (f 0) (f 0)) : Injective f := by
  have hne : ∀ m k, f m ≠ f (m + k + 1) := by
    intro m
    induction m with
    | zero =>
      intro k he
      have hpo := po_of_steps hstep (show 0 < 0 + k + 1 by omega)
      rw [← he] at hpo
      exact h0 hpo
    | succ m ih =>
      intro k he
      apply ih k
      apply hinj _ _ (f (m + 1))
      refine ⟨hstep m, ?_⟩
      rw [he, show m + 1 + k + 1 = m + k + 1 + 1 by omega]
      exact hstep _
  intro m n h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact absurd h (hne m k)
  · exact heq
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    exact absurd h.symm (hne n k)

private theorem clsRefl_iff {ρ : Set α} : ρ ∈ ClsRefl ↔ ρ.Infinite := by
  constructor
  · rintro ⟨R, ⟨⟨h11, hcd⟩, b, hb⟩, rfl⟩
    have hb' : Beg b R := hb
    have hpost : rels (anc R) b ⊆ dom R := fun y hy => by
      obtain ⟨z, hz | hz⟩ := fld_of_anc_right (show anc R b y from hy)
      · exact ⟨z, hz⟩
      · exact hcd ⟨z, hz⟩
    have hpo : ¬ po R b b := fun hpo => by
      rw [po_iff_transGen] at hpo
      obtain ⟨c, -, hcb⟩ := Relation.TransGen.tail'_iff.1 hpo
      exact hb'.2 ⟨c, hcb⟩
    obtain ⟨hinj, hfun⟩ := mem_arrow_one_one.1 h11
    obtain ⟨f, h0, hstep, hrange⟩ := post_seq hfun hb'.1 hpost
    have hf := post_injective hinj hstep (by rw [h0]; exact hpo)
    have hinf : (Set.range f).Infinite := Set.infinite_range_of_injective hf
    rw [← hrange] at hinf
    exact hinf.mono hpost
  · intro hρ
    obtain ⟨x, hx⟩ := hρ.nonempty
    obtain ⟨R, h11, hdom, hcod⟩ := exists_shift hρ hx
    refine ⟨R, ⟨⟨h11, ?_⟩, x, ?_⟩, hdom.symm⟩
    · rw [hdom, hcod]
      exact fun y hy => hy.1
    · show x ∈ dom R ∧ x ∉ codom R
      rw [hdom, hcod]
      exact ⟨hx, fun h => h.2 rfl⟩

private theorem mem_NCrefl_iff {μ : Set (Set α)} : μ ∈ NCrefl ↔ ∃ ρ : Set α, ρ.Infinite ∧ μ = n₀c ρ := by
  constructor
  · rintro ⟨ρ, hρ, hμ⟩
    exact ⟨ρ, clsRefl_iff.1 hρ, hμ⟩
  · rintro ⟨ρ, hρ, hμ⟩
    exact ⟨ρ, clsRefl_iff.2 hρ, hμ⟩

/-- An infinite class absorbs a countable one. -/
private theorem equiv_sum_countable {ρ : Set α} (hρ : ρ.Infinite) (B : Type*) [Countable B] :
    Nonempty (ρ ⊕ B ≃ ρ) := by
  classical
  obtain ⟨C, hC, hCρ⟩ := exists_aleph0_sub hρ
  obtain ⟨eC⟩ := mem_aleph0_iff_equiv.1 hC
  have hCB : Nonempty (C ⊕ B ≃ C) := by
    have : Countable C := (mem_aleph0_iff_ci.1 hC).1.to_subtype
    have : Infinite C := Set.infinite_coe_iff.2 (infinite_of_aleph0 hC)
    have : Infinite (C ⊕ B) := Infinite.of_injective Sum.inl Sum.inl_injective
    obtain ⟨_⟩ : Nonempty (Denumerable (C ⊕ B)) :=
      nonempty_denumerable_iff.2 ⟨inferInstance, inferInstance⟩
    exact ⟨(Denumerable.eqv (C ⊕ B)).trans eC⟩
  obtain ⟨e⟩ := hCB
  let d := Equiv.Set.sumDiffSubset hCρ
  exact ⟨(d.symm.sumCongr (Equiv.refl B)).trans ((Equiv.sumAssoc _ _ _).trans
    (((Equiv.refl _).sumCongr (Equiv.sumComm _ _)).trans ((Equiv.sumAssoc _ _ _).symm.trans
      ((e.sumCongr (Equiv.refl _)).trans d))))⟩

private theorem sm_clsSum_right_absorb {ρ : Set α} (hρ : ρ.Infinite) {B : Set β} (hB : B.Countable) :
    sm (ρ +ₐ B) ρ := by
  have : Countable B := hB.to_subtype
  obtain ⟨e⟩ := equiv_sum_countable hρ B
  exact sm_iff_nonempty_equiv.2 ⟨(clsSumEquiv ρ B).trans e⟩

private theorem sm_clsSum_left_absorb {ρ : Set α} (hρ : ρ.Infinite) {B : Set β} (hB : B.Countable) :
    sm (B +ₐ ρ) ρ := by
  have : Countable B := hB.to_subtype
  obtain ⟨e⟩ := equiv_sum_countable hρ B
  exact sm_iff_nonempty_equiv.2 ⟨(clsSumEquiv B ρ).trans ((Equiv.sumComm _ _).trans e)⟩

private theorem sm_diff_finite {ρ σ : Set α} (hρ : ρ.Infinite) (hσ : σ.Finite) : sm (ρ \ σ) ρ := by
  classical
  have hd : (ρ \ σ).Infinite := hρ.sdiff hσ
  have hsub : ρ ∩ σ ⊆ ρ := Set.inter_subset_left
  have hfin : (ρ ∩ σ).Finite := hσ.subset Set.inter_subset_right
  have : Countable ↥(ρ ∩ σ) := hfin.countable.to_subtype
  obtain ⟨e⟩ := equiv_sum_countable hd ↥(ρ ∩ σ)
  have hρeq : ρ \ (ρ ∩ σ) = ρ \ σ := by
    ext y; simp only [Set.mem_sdiff, Set.mem_inter_iff, not_and]; tauto
  let d := Equiv.Set.sumDiffSubset hsub
  refine sm_iff_nonempty_equiv.2 ⟨(e.symm.trans (Equiv.sumComm _ _)).trans ?_⟩
  exact ((Equiv.refl _).sumCongr (Set.equivOfEq hρeq.symm)).trans d

private theorem sel_nonempty_of {K : Set (Set α)} (hK : ∀ A, A ∈ K → A.Nonempty) :
    (sel memRel K).Nonempty := by
  classical
  refine ⟨fun x A => A ∈ K ∧ ∃ h : A ∈ K, x = (hK A h).some, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rw [mem_arrow_one_Cls]
    rintro x y A ⟨⟨-, h, rfl⟩, ⟨-, h', rfl⟩⟩
    rfl
  · rintro x A ⟨-, h, rfl⟩
    exact (hK A h).some_mem
  · show K = codom _
    ext A
    exact ⟨fun h => ⟨_, h, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩


private theorem infinite_cardGt_cardN {X : Type*} {ρ : Set α} (hρ : ρ.Infinite) {k : ℕ}
    (hk : (cardN X k).Nonempty) : n₀c ρ >ᶜ cardN X k := by
  obtain ⟨C, hC⟩ := hk
  rw [cardN_eq_n₀c hC, cardGt_n₀c_iff]
  have : Finite C := hC.1.to_subtype
  have : Infinite ρ := Set.infinite_coe_iff.2 hρ
  have hno : ¬ Nonempty (ρ ↪ C) := fun ⟨e⟩ =>
    not_finite_iff_infinite.2 (Infinite.of_injective e e.injective) ‹Finite C›
  exact ⟨(Function.Embedding.total C ρ).resolve_right hno, hno⟩

private theorem nc_univ_eq_empty {T : Type*} : nc T (Set.univ : Set (Set (Set T))) = ∅ := by
  ext B
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hB
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (mem_nc.1 hB)
  apply Function.cantor_injective (fun s : Set T => ((e.symm ⟨{s}, trivial⟩ : B) : T))
  intro s t hst
  have h1 := e.symm.injective (Subtype.ext hst)
  exact Set.singleton_injective (congrArg Subtype.val h1)

private theorem infinite_cl {ρ : Set α} (hρ : ρ.Infinite) : (cl ρ).Infinite := by
  have : Infinite ρ := Set.infinite_coe_iff.2 hρ
  refine Set.infinite_of_injective_forall_mem (f := fun x : ρ => ({(x : α)} : Set α))
    (fun a b h => Subtype.ext (Set.singleton_injective h)) ?_
  intro x y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact x.2

private theorem finite_cl {ρ : Set α} (hρ : ρ.Finite) : (cl ρ).Finite := hρ.finite_subsets

private theorem sumCls_infinite_of_infinite {K : Set (Set α)} (hK : K.Infinite) :
    (sumCls K).Infinite := fun h => hK ((finite_cl h).subset fun A hA _ hx => ⟨A, hA, hx⟩)

/-- In a type adequate for `μ^ν`, `Nc'(α exp β)` exists for every existent `α`. -/
private theorem AdeqExp_nc_nonempty {W : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (h : AdeqExp W μ ν) (A : Set α) (B : Set β) (hA : A.Nonempty) :
    (nc W (clsExp A B)).Nonempty := by
  classical
  unfold AdeqExp at h
  rw [n₀c_cardExp_n₀c, nc_nonempty_iff] at h
  obtain ⟨g, hg⟩ := h
  obtain ⟨a₀, ha₀⟩ := hA
  let E : (B → A) → (typ₁ ν → typ₁ μ) := fun k y =>
    ⟨if hy : (y : β) ∈ B then (k ⟨y, hy⟩ : α) else a₀, by rw [typ₁, typ₀_eq_univ]; trivial⟩
  have hE : Function.Injective E := by
    intro k k' hk
    funext y
    have := congrArg (fun F => (F ⟨y, by rw [typ₁, typ₀_eq_univ]; trivial⟩ : α)) hk
    simp only [E, dite_eq_left y.2] at this
    exact Subtype.ext this
  refine nc_nonempty_iff.2 ⟨fun ξ => g ((clsExpEquiv _ _).symm (E (clsExpEquiv A B ξ))), ?_⟩
  exact hg.comp ((clsExpEquiv _ _).symm.injective.comp (hE.comp (clsExpEquiv A B).injective))

/-- The new terms of a class in a progression of classes. -/
private theorem sumCls_finite {K : Set (Set α)} (hK : K.Finite) :
    (∀ A, A ∈ K → A.Finite) → (sumCls K).Finite := by
  induction K, hK using Set.Finite.induction_on with
  | empty =>
    intro _
    refine Set.finite_empty.subset ?_
    rintro x ⟨A, hA, -⟩
    exact absurd hA (Set.mem_empty_iff_false A).1
  | insert _ _ ih =>
    intro h
    refine ((h _ (Set.mem_insert _ _)).union (ih fun A hA => h A (Set.mem_insert_of_mem _ hA))).subset ?_
    rintro x ⟨A, hA | hA, hx⟩
    · exact Or.inl (hA ▸ hx)
    · exact Or.inr ⟨A, hA, hx⟩

private def newPart (R : Set α → Set α → Prop) (G : Set α) : Set α := G \ sumCls (refs (po R) G)

private theorem newPart_disjoint {f : ℕ → Set α} (hf : Injective f) {m n : ℕ} (h : m < n) :
    newPart (SeqRel f) (f m) ∩ newPart (SeqRel f) (f n) = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hm hn
  exact hn.2 ⟨f m, (po_seqRel' hf).2 h, hm.1⟩

private theorem infinite_fun_two {Y : Type*} [Infinite Y] {T : Set γ} (hT : T ∈ cardN γ 2) :
    Infinite (Y → T) := by
  classical
  obtain ⟨x, y, hxy, hT'⟩ := Set.ncard_eq_two.1 hT.2
  have hx : x ∈ T := by rw [hT']; exact Or.inl rfl
  have hy : y ∈ T := by rw [hT']; exact Or.inr rfl
  refine Infinite.of_injective (fun a : Y => fun b => if b = a then (⟨y, hy⟩ : T) else ⟨x, hx⟩) ?_
  intro a a' h
  have h' := congrFun h a
  dsimp only at h'
  by_contra hne
  rw [ite_eq_left (rfl : a = a), ite_eq_right hne] at h'
  exact hxy (congrArg Subtype.val h').symm


/-! ### Finite cardinal arithmetic (✱125–✱126) -/

private theorem mem_NCind_iff {μ : Set (Set α)} : μ ∈ NCind ↔ ∃ M : Set α, M.Finite ∧ μ = n₀c M := by
  constructor
  · rintro ⟨hi, hΛ⟩
    rcases NCinduct_cases hi with ⟨M, hM, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨M, hM, rfl⟩
    · exact absurd (by rw [Null_eq_empty]; rfl) hΛ
  · rintro ⟨M, hM, rfl⟩
    refine ⟨n₀c_mem_NCinduct hM, fun h => n₀c_ne_empty M ?_⟩
    rw [mem_unitCls.1 h, Null_eq_empty]

private theorem finite_clsTimes {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    (B ×ₐ A).Finite := by
  have : Finite A := hA.to_subtype
  have : Finite B := hB.to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ (clsTimesEquiv B A).symm)

private theorem ncard_clsTimes {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    (B ×ₐ A).ncard = A.ncard * B.ncard := by
  have : Finite A := hA.to_subtype
  have : Finite B := hB.to_subtype
  rw [← Nat.card_coe_set_eq, Nat.card_congr (clsTimesEquiv B A), Nat.card_prod, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq]

private theorem finite_clsExp {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    (clsExp A B).Finite := by
  have : Finite A := hA.to_subtype
  have : Finite B := hB.to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ (clsExpEquiv A B).symm)

private theorem ncard_clsExp {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    (clsExp A B).ncard = A.ncard ^ B.ncard := by
  have : Finite A := hA.to_subtype
  have : Finite B := hB.to_subtype
  rw [← Nat.card_coe_set_eq, Nat.card_congr (clsExpEquiv A B), Nat.card_fun, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq]

private theorem n₀c_add_finite {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    (n₀c A +ᶜ n₀c B : Set (Set γ)) = cardN γ (A.ncard + B.ncard) := by
  rw [n₀c_cardAdd_n₀c, nc_eq_cardN (clsSum_finite hA hB), ncard_clsSum hA hB]

private theorem n₀c_mul_finite {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    (n₀c A ×ᶜ n₀c B : Set (Set γ)) = cardN γ (A.ncard * B.ncard) := by
  rw [n₀c_cardMul_n₀c, nc_eq_cardN (finite_clsTimes hB hA), ncard_clsTimes hB hA, Nat.mul_comm]

private theorem n₀c_exp_finite {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    (n₀c A ^ᶜ n₀c B : Set (Set γ)) = cardN γ (A.ncard ^ B.ncard) := by
  rw [n₀c_cardExp_n₀c, nc_eq_cardN (finite_clsExp hA hB), ncard_clsExp hA hB]

private theorem cardN_cardGt_iff {X Y : Type*} {a b : ℕ} :
    cardN X a >ᶜ cardN Y b ↔ ((cardN X a).Nonempty ∧ (cardN Y b).Nonempty) ∧ b < a := by
  by_cases ha : (cardN X a).Nonempty
  · obtain ⟨S, hS⟩ := ha
    rw [cardN_eq_n₀c hS, cardGt_cardN_iff hS.1, hS.2]
    exact ⟨fun h => ⟨⟨⟨S, self_mem_n₀c S⟩, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  · refine ⟨fun h => ?_, fun h => absurd h.1.1 ha⟩
    obtain ⟨A, B, hA, -⟩ := mem_N₀C_of_cardGt h
    exact absurd (hA ▸ n₀c_nonempty A) ha

private theorem n₀c_finite_cardGt_iff {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) :
    n₀c A >ᶜ n₀c B ↔ B.ncard < A.ncard := by
  rw [n₀c_eq_cardN hA, n₀c_eq_cardN hB, cardN_cardGt_iff]
  exact ⟨fun h => h.2, fun h => ⟨⟨⟨A, hA, rfl⟩, ⟨B, hB, rfl⟩⟩, h⟩⟩

private theorem n₀c_finite_eq_iff {A B : Set α} (hA : A.Finite) (hB : B.Finite) :
    n₀c A = n₀c B ↔ A.ncard = B.ncard := by
  rw [n₀c_eq_cardN hA, n₀c_eq_cardN hB]
  exact ⟨cardN_inj ⟨A, hA, rfl⟩, fun h => by rw [h]⟩

private theorem n₀c_eq_zero_iff {A : Set α} : n₀c A = zero ↔ A = ∅ := by
  rw [zero_eq_n₀c_empty, n₀c_eq_n₀c_iff, sm_iff_nonempty_equiv]
  constructor
  · rintro ⟨e⟩
    exact Set.eq_empty_iff_forall_notMem.2 fun a ha => (e ⟨a, ha⟩).2
  · rintro rfl
    exact ⟨Equiv.refl _⟩

private theorem n₀c_eq_one_iff {A : Set α} : n₀c A = one ↔ ∃ a, A = {a} := by
  constructor
  · intro h
    have : A ∈ (one : Set (Set α)) := h ▸ self_mem_n₀c A
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    rw [one_eq_n₀c_singleton a]

/-- `Nc'(α + β)` in an adequate type exists, for any `α`, `β` of the types of the arguments. -/
private theorem AdeqMul_nc_nonempty {W : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (h : AdeqMul W μ ν) (A : Set α) (B : Set β) : (nc W (A ×ₐ B)).Nonempty := by
  unfold AdeqMul at h
  rw [n₀c_cardMul_n₀c, nc_nonempty_iff] at h
  obtain ⟨g, hg⟩ := h
  let E : B × A → typ₁ ν × typ₁ μ := fun p =>
    (⟨p.1, by rw [typ₁, typ₀_eq_univ]; trivial⟩, ⟨p.2, by rw [typ₁, typ₀_eq_univ]; trivial⟩)
  have hE : Function.Injective E := fun p q h => by
    simp only [E, Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  refine nc_nonempty_iff.2 ⟨fun ξ => g ((clsTimesEquiv _ _).symm (E (clsTimesEquiv A B ξ))), ?_⟩
  exact hg.comp ((clsTimesEquiv _ _).symm.injective.comp (hE.comp (clsTimesEquiv A B).injective))

private theorem AdeqExp_nc_nonempty' {W : Type*} {μ : Set (Set α)} {ν : Set (Set β)}
    (h : AdeqExp W μ ν) (A : Set α) (B : Set β) (hAB : A.Nonempty ∨ B.Nonempty) :
    (nc W (clsExp A B)).Nonempty := by
  rcases hAB with hA | ⟨b, hb⟩
  · exact AdeqExp_nc_nonempty h A B hA
  · by_cases hA : A.Nonempty
    · exact AdeqExp_nc_nonempty h A B hA
    · have hE : IsEmpty ↥(clsExp A B) := ⟨fun ξ => by
        have k := clsExpEquiv A B ξ ⟨b, hb⟩
        exact hA ⟨k.1, k.2⟩⟩
      exact ⟨∅, sm_iff_nonempty_equiv.2 ⟨Equiv.equivOfIsEmpty _ _⟩⟩

/-- `ι'x ↓ Λ`-style count: the class of `Λ` and the unit classes of members of `C` has one more
member than `C`. -/
private theorem sm_clsSum_unit_insert {X W : Type*} (C : Set X) (w : W) :
    sm (C +ₐ ι w) (insert (∅ : Set X) ((fun c => ({c} : Set X)) '' C)) := by
  classical
  refine sm_iff_nonempty_equiv.2 ⟨(clsSumEquiv C (ι w)).trans (Equiv.ofBijective
    (Sum.elim (fun c => (⟨{(c : X)}, Set.mem_insert_of_mem _ ⟨c, c.2, rfl⟩⟩ :
        ↥(insert (∅ : Set X) ((fun c => ({c} : Set X)) '' C))))
      (fun _ => ⟨∅, Set.mem_insert _ _⟩)) ⟨?_, ?_⟩)⟩
  · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
    · exact congrArg Sum.inl (Subtype.ext (Set.singleton_injective h))
    · exact absurd h (Set.singleton_ne_empty _)
    · exact absurd h.symm (Set.singleton_ne_empty _)
    · exact congrArg Sum.inr (Subtype.ext ((mem_unitCls.1 a.2).trans (mem_unitCls.1 b.2).symm))
  · rintro ⟨s, hs | ⟨c, hc, rfl⟩⟩
    · exact ⟨Sum.inr ⟨w, rfl⟩, Subtype.ext hs.symm⟩
    · exact ⟨Sum.inl ⟨c, hc⟩, rfl⟩

private theorem n₀c_not_mem_zero_iff {C : Set α} : n₀c C ∉ ι zero ↔ C.Nonempty := by
  rw [mem_unitCls, n₀c_eq_zero_iff, Set.nonempty_iff_ne_empty]

private theorem n₀c_not_mem_one_iff {C : Set α} :
    n₀c C ∉ ι one ↔ C.ncard ≠ 1 := by
  rw [mem_unitCls, n₀c_eq_one_iff, Ne, Set.ncard_eq_one]

private theorem finite_of_clsSum_finite_right {A : Set α} {B : Set β} (h : (A +ₐ B).Finite) :
    B.Finite := by
  have : Finite ↥(A +ₐ B) := h.to_subtype
  have : Finite (A ⊕ B) := Finite.of_equiv _ (clsSumEquiv A B)
  exact Set.finite_coe_iff.1 (Finite.of_injective (Sum.inr : B → A ⊕ B) Sum.inr_injective)

private theorem finite_of_clsTimes_finite {A : Set α} {B : Set β} (h : (B ×ₐ A).Finite)
    (hA : A.Nonempty) (hB : B.Nonempty) : A.Finite ∧ B.Finite := by
  have : Finite ↥(B ×ₐ A) := h.to_subtype
  have : Finite (A × B) := Finite.of_equiv _ (clsTimesEquiv B A)
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨Set.finite_coe_iff.1 (Finite.of_injective (fun x : A => (x, (⟨b, hb⟩ : B)))
      (fun x y h => congrArg Prod.fst h)),
    Set.finite_coe_iff.1 (Finite.of_injective (fun y : B => ((⟨a, ha⟩ : A), y))
      (fun x y h => congrArg Prod.snd h))⟩

/-- A member of a nonempty homogeneous cardinal sum, product or power: the arguments are
homogeneous cardinals. -/
private theorem exists_of_cardAdd_nonempty {μ : Set (Set α)} {ν : Set (Set β)}
    (h : (μ +ᶜ ν : Set (Set γ)).Nonempty) : ∃ (A : Set α) (B : Set β), μ = n₀c A ∧ ν = n₀c B := by
  obtain ⟨ξ, A, B, ⟨hA, hB⟩, -⟩ := h
  exact ⟨A, B, hA, hB⟩

private theorem exists_of_cardMul_nonempty {μ : Set (Set α)} {ν : Set (Set β)}
    (h : (μ ×ᶜ ν : Set (Set γ)).Nonempty) : ∃ (A : Set α) (B : Set β), μ = n₀c A ∧ ν = n₀c B := by
  obtain ⟨ξ, A, B, ⟨hA, hB⟩, -⟩ := h
  exact ⟨A, B, hA, hB⟩

private theorem exists_of_cardExp_nonempty {μ : Set (Set α)} {ν : Set (Set β)}
    (h : (μ ^ᶜ ν : Set (Set γ)).Nonempty) : ∃ (A : Set α) (B : Set β), μ = n₀c A ∧ ν = n₀c B := by
  obtain ⟨ξ, A, B, ⟨hA, hB⟩, -⟩ := h
  exact ⟨A, B, hA, hB⟩

/-- A nonempty homogeneous cardinal `nc γ S` that is in `NC ind` comes from a finite `S`. -/
private theorem finite_of_nc_mem_NCind {S : Set α} (h : (nc γ S) ∈ NCind) : S.Finite := by
  obtain ⟨F, hF, he⟩ := mem_NCind_iff.1 h
  have hF' : F ∈ nc γ S := he ▸ self_mem_n₀c F
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hF'
  have : Finite F := hF.to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ e)

private theorem nc_mem_NCind {S : Set α} (hS : S.Finite) (hne : (nc γ S).Nonempty) :
    nc γ S ∈ NCind := by
  obtain ⟨F, hF⟩ := hne
  rw [nc_eq_n₀c_of_mem hF]
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hF
  have : Finite S := hS.to_subtype
  exact mem_NCind_iff.2 ⟨F, Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm), rfl⟩

end Aux

/-!
## [✱122] Progressions

*(Vol. 2, p. 253)*

> *Summary of* *122.
>
> By a "progression" we mean a series which is like the series of the inductive cardinals in order of magnitude (assuming that all inductive cardinals exist), *i.e.* a series whose terms can be called \[ 1_{R}, 2_{R}, 3_{R}, ... \nu _{R}, ..., \] where every term of the series is correlated with some inductive cardinal, and every inductive cardinal is correlated with some term of the series. Such series belong to the relation-number (cf. *152 and *263) which Cantor calls \(\omega\). Their generating relation may be taken to be the transitive relation of earlier and later, or the one-one relation of immediate predecessor to immediate successor. We shall reserve the notation \(\omega\) for the *transitive* generating relations of progressions; for the present, we are concerned with the one-one relations which generate progressions. The class of these relations we shall call "\(\text{Prog}\)."
>
> …

**Lean reading.** `Prog` (✱122·01) is the class of one-one relations `R` with
`D'R = R⃖_*'B'R`, the description `B'R` (`Desc Beg R`) having that equation as scope. `R⃖_*'x`,
`R⃗_*'x`, `R⃖_po'x` are `rels (anc R) x`, `refs (anc R) x`, `rels (po R) x`; `R̆_po` is `(po R)˘`;
`min(R_po)`, `max(R_po)` are `minP (po R)`, `maxP (po R)`; `R_ν` is `Pnu R ν` and `ν_R` is
`Desc (nuP ν) R` (✱121); chains of equations are conjunctions of their links, each link with its own
descriptions. The proofs identify a progression with the successor relation of an injective sequence
`ℕ → α` (private lemma `prog_iff_seq`). Convention Infin T is applied where `ν_R` must exist
(`InfinAx X` for the type of `ν`, which nothing determines, ✱122·3·33·34·341); ✱122·31·32 hold in
every type and get no such hypothesis, and where `B⃗'R_ν ∈ ν` ties `ν` to the type of `R`
(✱122·35·381) it is not needed. The constant `1` of `1_R` has its own type, with `[Nonempty W]`.

**Status.** proved (all propositions; ✱122·01 definition; ✱122·3·33·34·341·35·381 proved (reading),
✱122·42 proved (corrected), see their docstrings)
-/

/-- ✱122·01 (Df). \(\text{Prog} = (1\rightarrow 1)\cap \hat{R} (\text{D}ʻR = \overleftarrow{R}_{*}ʻBʻR) \quad\text{Df}\) -/
theorem pm122_01 {α : Type*} :
    (Prog : Set (α → α → Prop)) =
      arrow one one ∩ {R | Desc Beg R (fun b => dom R = rels (anc R) b)} := rfl

/-- ✱122·1. \(\vdash :R\in \text{Prog}.\equiv .R\in 1\rightarrow 1.\text{D}ʻR = \overleftarrow{R}_{*}ʻBʻR \quad[(*122·01)]\) -/
theorem pm122_1 {α : Type*} {R : α → α → Prop} :
    R ∈ Prog ↔ R ∈ arrow one one ∧ Desc Beg R (fun b => dom R = rels (anc R) b) := Iff.rfl

/-- ✱122·11. \(\vdash \colon\ldotp R\in \text{Prog}.\equiv :R\in 1\rightarrow 1.\text{E}!BʻR:x\in \text{D}ʻR.\equiv _{x}.x\in \overleftarrow{R}_{*}ʻBʻR\) -/
theorem pm122_11 {α : Type*} {R : α → α → Prop} :
    R ∈ Prog ↔ (R ∈ arrow one one ∧ EDesc Beg R) ∧
      ∀ x, x ∈ dom R ↔ Desc Beg R (fun b => x ∈ rels (anc R) b) := by
  constructor
  · rintro ⟨h11, b, hb, hdom⟩
    refine ⟨⟨h11, b, hb⟩, fun x => ?_⟩
    rw [desc_iff_of_unique hb, hdom]
  · rintro ⟨⟨h11, b, hb⟩, h⟩
    exact ⟨h11, b, hb, Set.ext fun x => (h x).trans (desc_iff_of_unique hb _)⟩

/-- ✱122·12. \[\begin{align}\vdash \colon\colon R\in \text{Prog}.&\equiv \colon\ldotp R\in 1\rightarrow 1.\text{E}!BʻR\colon\ldotp x\in \text{D}ʻR.\equiv _{x}:\\ &BʻR\in \alpha .\breve{R} ʻʻ\alpha \subset \alpha .\supset _{\alpha }.x\in \alpha \quad[*122·11.*90·1]\end{align}\] -/
theorem pm122_12 {α : Type*} {R : α → α → Prop} :
    R ∈ Prog ↔ (R ∈ arrow one one ∧ EDesc Beg R) ∧
      ∀ x, x ∈ dom R ↔
        ∀ A : Set α, Desc Beg R (fun b => b ∈ A) ∧ R˘ ʻʻ A ⊆ A → x ∈ A := by
  rw [pm122_11]
  refine and_congr_right fun hE => forall_congr' fun x => iff_congr Iff.rfl ?_
  obtain ⟨-, b, hb⟩ := hE
  have hfld : b ∈ fld R := by
    obtain ⟨y, hy⟩ := ((hb b).2 rfl).1
    exact ⟨y, Or.inl hy⟩
  rw [desc_iff_of_unique hb]
  show anc R b x ↔ _
  constructor
  · rintro ⟨-, hM⟩ A ⟨hbA, hA⟩
    exact hM A ⟨hA, (desc_iff_of_unique hb _).1 hbA⟩
  · intro hx
    exact ⟨hfld, fun M ⟨hM, hbM⟩ => hx M ⟨(desc_iff_of_unique hb _).2 hbM, hM⟩⟩

/-- ✱122·14. \(\vdash :R\in \text{Prog}.\supset .\overleftarrow{R}_{\text{po}}ʻBʻR=\text{ᗡ}ʻR\) -/
theorem pm122_14 {α : Type*} {R : α → α → Prop} :
    R ∈ Prog → Desc Beg R (fun b => rels (po R) b = codom R) := by
  intro h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [desc_beg_seqRel hf, codom_seqRel, popost_zero_seqRel hf]

/-- ✱122·141. \(\vdash :R\in \text{Prog}.\supset .\text{ᗡ}ʻR\subset \text{D}ʻR.CʻR=\text{D}ʻR\) -/
theorem pm122_141 {α : Type*} {R : α → α → Prop} :
    R ∈ Prog → codom R ⊆ dom R ∧ fld R = dom R := by
  intro h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [codom_seqRel, dom_seqRel, fld_seqRel]
  exact ⟨range_succ_sub f, rfl⟩

/-- ✱122·142. \(\vdash :R\in \text{Prog}.P\in \text{Pot}ʻR.\supset .\text{D}ʻP=\text{D}ʻR \quad[*122·141.*92·14]\) -/
theorem pm122_142 {α : Type*} {R P : α → α → Prop} :
    R ∈ Prog ∧ P ∈ pot R → dom P = dom R := by
  rintro ⟨h, hP⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨d, -, rfl⟩ := pot_seqRel hf hP
  rw [dom_seqStep, dom_seqRel]

/-- ✱122·143. \(\vdash :R\in \text{Prog}.P\in \text{Pot}ʻR.\supset .\text{ᗡ}ʻP\subset \text{D}ʻP \quad[*122·142·141.*91·271]\) -/
theorem pm122_143 {α : Type*} {R P : α → α → Prop} :
    R ∈ Prog ∧ P ∈ pot R → codom P ⊆ dom P := by
  rintro ⟨h, hP⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨d, -, rfl⟩ := pot_seqRel hf hP
  rw [codom_seqStep, dom_seqStep]
  rintro _ ⟨n, rfl⟩
  exact ⟨n + d, rfl⟩

/-- ✱122·15. \(\vdash :R\in \text{Prog}.\supset .R=(\overleftarrow{R}_{*}ʻBʻR)\upharpoonleft R=R\upharpoonright (\overleftarrow{R}_{\text{po}}ʻBʻR)=R\upharpoonright (\overleftarrow{R}_{*}ʻBʻR)\)

The chain `R = X = Y = Z` is the conjunction of its links (✱13·03); in each link the
descriptions `B'R` have the smallest scope, the first occurrence the larger one (✱14·113). -/
theorem pm122_15 {α : Type*} {R : α → α → Prop} :
    R ∈ Prog →
      (Desc Beg R (fun b => R = rels (anc R) b ◁ R) ∧
        Desc Beg R (fun b => Desc Beg R (fun c => rels (anc R) b ◁ R = R ↾ rels (po R) c))) ∧
      Desc Beg R (fun b => Desc Beg R (fun c => R ↾ rels (po R) b = R ↾ rels (anc R) c)) := by
  intro h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  simp only [desc_beg_seqRel hf, post_zero_seqRel hf, popost_zero_seqRel hf]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> funext x y <;> apply propext
  · exact ⟨fun h => ⟨(seqRel_mem h).1, h⟩, fun h => h.2⟩
  · exact ⟨fun h => ⟨h.2, (seqRel_mem h.2).2⟩, fun h => ⟨(seqRel_mem h.1).1, h.1⟩⟩
  · exact ⟨fun h => ⟨h.1, range_succ_sub f (seqRel_mem h.1).2⟩,
      fun h => ⟨h.1, (seqRel_mem h.1).2⟩⟩

/-- ✱122·151. \[\begin{align}&\vdash :R\in \text{Prog}.\supset .R_{*}=(\overleftarrow{R}_{*}ʻBʻR)\upharpoonleft R_{*}=R_{*}\upharpoonright (\overleftarrow{R}_{*}ʻBʻR)\\ &[35·63·66.*90·14.*122·141·1]\end{align}\] -/
theorem pm122_151 {α : Type*} {R : α → α → Prop} :
    R ∈ Prog →
      Desc Beg R (fun b => anc R = rels (anc R) b ◁ anc R) ∧
        Desc Beg R (fun b => Desc Beg R (fun c => rels (anc R) b ◁ anc R = anc R ↾ rels (anc R) c)) := by
  intro h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  simp only [desc_beg_seqRel hf, post_zero_seqRel hf]
  refine ⟨?_, ?_⟩ <;> funext x y <;> apply propext
  · exact ⟨fun h => ⟨(anc_seqRel_mem hf h).1, h⟩, fun h => h.2⟩
  · exact ⟨fun h => ⟨h.2, (anc_seqRel_mem hf h.2).2⟩, fun h => ⟨(anc_seqRel_mem hf h.1).1, h.1⟩⟩

/-- ✱122·152. \[\begin{align}\vdash :R\in \text{Prog}.\supset .R_{\text{po}}=(\overleftarrow{R}_{*}ʻBʻR)\upharpoonleft R_{\text{po}}&=R_{\text{po}}\upharpoonright (\overleftarrow{R}_{\text{po}}ʻBʻR)\\ &=R_{\text{po}}\upharpoonright (\overleftarrow{R}_{*}ʻBʻR)\\ [*35·63·66.*91·504.*121·1·14]\end{align}\] -/
theorem pm122_152 {α : Type*} {R : α → α → Prop} :
    R ∈ Prog →
      (Desc Beg R (fun b => po R = rels (anc R) b ◁ po R) ∧
        Desc Beg R (fun b => Desc Beg R (fun c => rels (anc R) b ◁ po R = po R ↾ rels (po R) c))) ∧
      Desc Beg R (fun b => Desc Beg R (fun c => po R ↾ rels (po R) b = po R ↾ rels (anc R) c)) := by
  intro h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  simp only [desc_beg_seqRel hf, post_zero_seqRel hf, popost_zero_seqRel hf]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> funext x y <;> apply propext
  · exact ⟨fun h => ⟨(po_seqRel_mem hf h).1, h⟩, fun h => h.2⟩
  · exact ⟨fun h => ⟨h.2, (po_seqRel_mem hf h.2).2⟩, fun h => ⟨(po_seqRel_mem hf h.1).1, h.1⟩⟩
  · exact ⟨fun h => ⟨h.1, range_succ_sub f (po_seqRel_mem hf h.1).2⟩,
      fun h => ⟨h.1, (po_seqRel_mem hf h.1).2⟩⟩

/-- ✱122·16. \(\vdash :R\in \text{Prog}.\supset .R_{\text{po}}\,\unicode{x2abd}\, J \quad[*96·23.*122·152]\) -/
theorem pm122_16 {α : Type*} {R : α → α → Prop} : R ∈ Prog → po R ⪽ J := by
  intro h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  intro x y hxy
  obtain ⟨m, n, hmn, rfl, rfl⟩ := (po_seqRel hf).1 hxy
  exact (J_apply _ _).2 fun e => by have := hf e; omega

/-- ✱122·17. \(\vdash :R\in \text{Prog}.\equiv .R\in \text{Cls}\rightarrow 1.R_{\text{po}}\,\unicode{x2abd}\, J.\text{D}ʻR=\overleftarrow{R}_{*}ʻBʻR\) -/
theorem pm122_17 {α : Type*} {R : α → α → Prop} :
    R ∈ Prog ↔ (R ∈ arrow Cls one ∧ po R ⪽ J) ∧ Desc Beg R (fun b => dom R = rels (anc R) b) := by
  constructor
  · intro h
    exact ⟨⟨mem_arrow_Cls_one.2 (mem_arrow_one_one.1 h.1).2, pm122_16 h⟩, h.2⟩
  · rintro ⟨⟨hfun, hpo⟩, b, hb, hdom⟩
    rw [mem_arrow_Cls_one] at hfun
    have hbB : Beg b R := (hb b).2 rfl
    obtain ⟨f, -, hstep, hrange⟩ := post_seq hfun hbB.1 (fun z hz => by rw [hdom]; exact hz)
    have hinj : Function.Injective f := by
      intro m n hmn
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact (J_apply _ _).1 (hpo _ _ (po_of_steps hstep hlt)) hmn
      · exact (J_apply _ _).1 (hpo _ _ (po_of_steps hstep hlt)) hmn.symm
    have : R = SeqRel f := eq_seqRel_of_steps hfun hstep
      (fun z hz => by rw [hdom, hrange] at hz; exact hz)
    rw [this]
    exact seqRel_mem_prog hinj

/-- ✱122·2. \(\vdash \colon\ldotp R\in \text{Prog}.x,y\in CʻR.\supset :xR_{*}y.\lor.yR_{*}x \quad[*96·302.*122·1·141]\) -/
theorem pm122_2 {α : Type*} {R : α → α → Prop} {x y : α} :
    R ∈ Prog ∧ Mem2 x y (fld R) → anc R x y ∨ anc R y x := by
  rintro ⟨h, hx, hy⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [fld_seqRel] at hx hy
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  rw [anc_seqRel' hf, anc_seqRel' hf]
  omega

/-- ✱122·21. \[\begin{align}\vdash \colon\ldotp R\in \text{Prog}.x,y\in CʻR.\supset :xR_{\text{po}}y.&\lor.x=y.\lor.yR_{\text{po}}x\\ &[*96·303.*122·1·141]\end{align}\] -/
theorem pm122_21 {α : Type*} {R : α → α → Prop} {x y : α} :
    R ∈ Prog ∧ Mem2 x y (fld R) → (po R x y ∨ x = y) ∨ po R y x := by
  rintro ⟨h, hx, hy⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [fld_seqRel] at hx hy
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  rw [po_seqRel' hf, po_seqRel' hf]
  rcases lt_trichotomy m n with h | rfl | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr h

/-- ✱122·22. \(\vdash :R\in \text{Prog}.\alpha \subset \text{D}ʻR.x,y\in \alpha -\breve{R} _{\text{po}}ʻʻ\alpha .\supset .x=y\) -/
theorem pm122_22 {α : Type*} {R : α → α → Prop} {A : Set α} {x y : α} :
    (R ∈ Prog ∧ A ⊆ dom R) ∧ Mem2 x y (A \ (po R)˘ ʻʻ A) → x = y := by
  rintro ⟨⟨h, hA⟩, ⟨hxA, hx⟩, ⟨hyA, hy⟩⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [dom_seqRel] at hA
  obtain ⟨m, rfl⟩ := hA hxA
  obtain ⟨n, rfl⟩ := hA hyA
  rcases lt_trichotomy m n with hlt | rfl | hlt
  · exact absurd ⟨f m, hxA, (po_seqRel' hf).2 hlt⟩ hy
  · rfl
  · exact absurd ⟨f n, hyA, (po_seqRel' hf).2 hlt⟩ hx

/-- ✱122·23. \[\begin{align}\vdash :R\in \text{Prog}.\alpha \subset \text{D}ʻR.&\exists !\alpha .\supset .\\ &\text{E}!\text{min}(R_{\text{po}})ʻ\alpha .\alpha -\breve{R} _{\text{po}}ʻʻ\alpha =\iota ʻ\text{min}(R_{\text{po}})ʻ\alpha\end{align}\] -/
theorem pm122_23 {α : Type*} {R : α → α → Prop} {A : Set α} :
    (R ∈ Prog ∧ A ⊆ dom R) ∧ A.Nonempty →
      EDesc (minP (po R)) A ∧ Desc (minP (po R)) A (fun m => A \ (po R)˘ ʻʻ A = ι m) := by
  classical
  rintro ⟨⟨h, hA⟩, x₀, hx₀⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [dom_seqRel] at hA
  have hex : ∃ n, f n ∈ A := let ⟨n, e⟩ := hA hx₀; ⟨n, e ▸ hx₀⟩
  have hNA : f (Nat.find hex) ∈ A := Nat.find_spec hex
  have hmin : ∀ x, minP (po (SeqRel f)) x A ↔ x = f (Nat.find hex) := by
    intro x
    rw [minP_apply, fld_po_seqRel hf]
    constructor
    · rintro ⟨⟨hx, -⟩, hno⟩
      obtain ⟨n, rfl⟩ := hA hx
      have h1 : Nat.find hex ≤ n := Nat.find_min' hex hx
      rcases Nat.lt_or_ge (Nat.find hex) n with hlt | hge
      · exact absurd ⟨f (Nat.find hex), hNA, (po_seqRel' hf).2 hlt⟩ hno
      · rw [show n = Nat.find hex by omega]
    · rintro rfl
      refine ⟨⟨hNA, ⟨_, rfl⟩⟩, ?_⟩
      rintro ⟨y, hy, hyN⟩
      obtain ⟨m, n, hmn, rfl, hn⟩ := (po_seqRel hf).1 hyN
      rw [← hf hn] at hmn
      exact absurd (Nat.find_min' hex hy) (by omega)
  have hset : A \ (po (SeqRel f))˘ ʻʻ A = ι (f (Nat.find hex)) := by
    ext x
    rw [mem_unitCls, ← hmin, minP_apply, fld_po_seqRel hf]
    constructor
    · rintro ⟨hx, hno⟩
      exact ⟨⟨hx, hA hx⟩, fun ⟨y, hy, hyx⟩ => hno ⟨y, hy, hyx⟩⟩
    · rintro ⟨⟨hx, -⟩, hno⟩
      exact ⟨hx, fun ⟨y, hy, hyx⟩ => hno ⟨y, hy, hyx⟩⟩
  exact ⟨⟨_, hmin⟩, _, hmin, hset⟩

/-- ✱122·231. \(\vdash :R\in \text{Prog}.\alpha \subset \breve{R} _{\text{po}}ʻʻ\alpha .\supset .\alpha =\Lambda\) -/
theorem pm122_231 {α : Type*} {R : α → α → Prop} {A : Set α} :
    R ∈ Prog ∧ A ⊆ (po R)˘ ʻʻ A → A = Λ := by
  classical
  rintro ⟨h, hA⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [Null_eq_empty]
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hA' : ∀ z ∈ A, ∃ n, z = f n := fun z hz => by
    obtain ⟨a, -, ha⟩ := hA hz
    obtain ⟨m, n, -, -, rfl⟩ := (po_seqRel hf).1 ha
    exact ⟨n, rfl⟩
  have hex : ∃ n, f n ∈ A := let ⟨n, e⟩ := hA' x hx; ⟨n, e ▸ hx⟩
  obtain ⟨a, haA, ha⟩ := hA (Nat.find_spec hex)
  obtain ⟨m, n, hmn, rfl, hn⟩ := (po_seqRel hf).1 ha
  rw [← hf hn] at hmn
  exact absurd (Nat.find_min' hex haA) (by omega)

/-- ✱122·24. \(\vdash :R\in \text{Prog}.P\in PotʻR.\supset .\text{D}ʻP=\breve{P} _{*}ʻʻ\overrightarrow{B}ʻP=sʻ\text{gen}ʻP\)

`P̆_*` is `Cnv'P_*` (✱90·02), so `P̆_*''B⃗'P` is `ancCnv P ʻʻ refs Beg P`, the posterity of
the beginnings of `P`; `s'gen'P` is `sumCls (gen P)`. The chain is the conjunction of its links. -/
theorem pm122_24 {α : Type*} {R P : α → α → Prop} :
    R ∈ Prog ∧ P ∈ pot R →
      dom P = ancCnv P ʻʻ refs Beg P ∧ ancCnv P ʻʻ refs Beg P = sumCls (gen P) := by
  rintro ⟨h, hP⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨d, hd, rfl⟩ := pot_seqRel hf hP
  refine ⟨?_, ?_⟩
  · ext x
    rw [dom_seqStep]
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨f (n % d), (beg_seqStep hf).2 ⟨n % d, Nat.mod_lt _ hd, rfl⟩, ?_⟩
      show anc (SeqStep f d) (f (n % d)) (f n)
      rw [anc_seqStep hf]
      exact ⟨n / d, by rw [Nat.mod_add_div' n d]⟩
    · rintro ⟨y, -, hyx⟩
      have := fld_of_anc_right (show anc (SeqStep f d) y x from hyx)
      rwa [fld_seqStep] at this
  · ext x
    rw [mem_sumCls_gen_iff (mem_arrow_one_one.1 (seqStep_oneone hf d)).1]
    exact ⟨fun ⟨y, hy, hyx⟩ => ⟨y, hy, hyx⟩, fun ⟨y, hy, hyx⟩ => ⟨y, hy, hyx⟩⟩

/-- ✱122·25. \[\begin{align}\vdash :R\in \text{Prog}.P\in \text{Pot}ʻR.x\in &\text{D}ʻR.\supset .\\ &(\overleftarrow{P}_{*}ʻx)\upharpoonleft P\in \text{Prog}.x=Bʻ\{(\overleftarrow{P}_{*}ʻx)\upharpoonleft P\}\end{align}\] -/
theorem pm122_25 {α : Type*} {R P : α → α → Prop} {x : α} :
    (R ∈ Prog ∧ P ∈ pot R) ∧ x ∈ dom R →
      rels (anc P) x ◁ P ∈ Prog ∧ Desc Beg (rels (anc P) x ◁ P) (fun b => x = b) := by
  rintro ⟨⟨h, hP⟩, hx⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨d, hd, rfl⟩ := pot_seqRel hf hP
  rw [dom_seqRel] at hx
  obtain ⟨m, rfl⟩ := hx
  let g : ℕ → α := fun q => f (m + q * d)
  have hg : Function.Injective g := by
    intro p q hpq
    have h1 : m + p * d = m + q * d := hf hpq
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h1)
  have heq : rels (anc (SeqStep f d)) (f m) ◁ SeqStep f d = SeqRel g := by
    funext u v
    apply propext
    show anc (SeqStep f d) (f m) u ∧ SeqStep f d u v ↔ _
    rw [anc_seqStep hf]
    have hq : ∀ q, m + (q + 1) * d = m + q * d + d := fun q => by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    constructor
    · rintro ⟨⟨q, rfl⟩, k, hk, rfl⟩
      rw [← hf hk]
      refine ⟨q, rfl, ?_⟩
      show f (m + q * d + d) = f (m + (q + 1) * d)
      rw [hq]
    · rintro ⟨q, rfl, rfl⟩
      refine ⟨⟨q, rfl⟩, m + q * d, rfl, ?_⟩
      show f (m + (q + 1) * d) = f (m + q * d + d)
      rw [hq]
  rw [heq]
  refine ⟨seqRel_mem_prog hg, (desc_beg_seqRel hg _).2 ?_⟩
  show f m = f (m + 0 * d)
  rw [Nat.zero_mul, Nat.add_zero]

/-- ✱122·26. \(\vdash :R\in \text{Prog}.\alpha \subset R_{\text{po}}ʻʻ\alpha .\exists !\alpha .\supset .\text{D}ʻR=R_{\text{po}}ʻʻ\alpha\) -/
theorem pm122_26 {α : Type*} {R : α → α → Prop} {A : Set α} :
    (R ∈ Prog ∧ A ⊆ po R ʻʻ A) ∧ A.Nonempty → dom R = po R ʻʻ A := by
  rintro ⟨⟨h, hA⟩, hne⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨idx, hmono, hmem, -, -, -⟩ := enum_of_sub_po hf hA hne
  rw [dom_seqRel]
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨f (idx (n + 1)), hmem _, (po_seqRel' hf).2
      (lt_of_lt_of_le (Nat.lt_succ_self n) (hmono.id_le _))⟩
  · rintro ⟨y, -, hxy⟩
    exact (po_seqRel_mem hf hxy).1

/-- ✱122·27. \[\begin{align}\vdash :R\in \text{Prog}.\exists !\text{D}ʻR-R_{\text{po}}ʻʻ\alpha .&\exists !\alpha \cap \text{D}ʻR.\supset .\\ &\text{E}!\text{max}(R_{\text{po}})ʻ\alpha .\exists !\alpha \cap \text{D}ʻR-R_{\text{po}}ʻʻ\alpha \end{align}\]

`max(R_po)'α` is `max_P'α` with `P = R_po` (✱93·021), i.e. `Desc (maxP (po R)) A`; the
product `α ∩ D'R − R_po''α` is `(A ∩ dom R) \ po R ʻʻ A`. -/
theorem pm122_27 {α : Type*} {R : α → α → Prop} {A : Set α} :
    (R ∈ Prog ∧ (dom R \ po R ʻʻ A).Nonempty) ∧ (A ∩ dom R).Nonempty →
      EDesc (maxP (po R)) A ∧ ((A ∩ dom R) \ po R ʻʻ A).Nonempty := by
  rintro ⟨⟨h, ⟨z, hzd, hz⟩⟩, ⟨a, haA, had⟩⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [dom_seqRel] at hzd had
  obtain ⟨N, rfl⟩ := hzd
  obtain ⟨k, rfl⟩ := had
  have hb : ∀ n, f n ∈ A → n ≤ N := fun n hn => by
    by_contra hlt
    exact hz ⟨f n, hn, (po_seqRel' hf).2 (by omega)⟩
  obtain ⟨M, hM, hMmax⟩ := exists_max_nat N hb ⟨k, haA⟩
  have hmax : ∀ x, maxP (po (SeqRel f)) x A ↔ x = f M := by
    intro x
    show minP (po (SeqRel f))˘ x A ↔ _
    rw [minP_apply, fld_cnv, fld_po_seqRel hf]
    constructor
    · rintro ⟨⟨hx, n, rfl⟩, hno⟩
      have h1 := hMmax n hx
      rcases Nat.lt_or_ge n M with hlt | hge
      · exact absurd ⟨f M, hM, (po_seqRel' hf).2 hlt⟩ hno
      · rw [show n = M by omega]
    · rintro rfl
      refine ⟨⟨hM, M, rfl⟩, ?_⟩
      rintro ⟨y, hy, hMy⟩
      obtain ⟨m, n, hmn, hm, rfl⟩ := (po_seqRel hf).1 hMy
      rw [← hf hm] at hmn
      have := hMmax n hy
      omega
  refine ⟨⟨f M, hmax⟩, f M, ⟨hM, _, seqRel_apply f M⟩, ?_⟩
  rintro ⟨y, hy, hMy⟩
  exact ((hmax (f M)).2 rfl).2 ⟨y, hy, hMy⟩

/-- ✱122·28. \(\vdash :R\in \text{Prog}.\alpha \subset \overrightarrow{R}_{*}ʻx.\exists !\alpha .\supset .\text{E}!\text{max}(R_{\text{po}})ʻ\alpha .\exists !\alpha \cap \text{D}ʻR-R_{\text{po}}ʻʻ\alpha\) -/
theorem pm122_28 {α : Type*} {R : α → α → Prop} {A : Set α} {x : α} :
    (R ∈ Prog ∧ A ⊆ refs (anc R) x) ∧ A.Nonempty →
      EDesc (maxP (po R)) A ∧ ((A ∩ dom R) \ po R ʻʻ A).Nonempty := by
  rintro ⟨⟨h, hA⟩, ⟨a, ha⟩⟩
  have hR := h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  have hax : anc (SeqRel f) a x := hA ha
  obtain ⟨-, N, -, -, rfl⟩ := (anc_seqRel hf).1 hax
  refine pm122_27 ⟨⟨hR, f N, ⟨_, seqRel_apply f N⟩, ?_⟩, a, ha, ?_⟩
  · rintro ⟨y, hy, hNy⟩
    obtain ⟨p, q, hpq, hp, hq⟩ := (anc_seqRel hf).1 (show anc (SeqRel f) y (f N) from hA hy)
    rw [hp] at hNy
    rw [← hf hq] at hpq
    have := (po_seqRel' hf).1 hNy
    omega
  · rw [dom_seqRel]
    exact (anc_seqRel_mem hf hax).1

/-- ✱122·3. \[\begin{align}&\vdash :R\in \text{Prog}.\supset .\text{D}ʻR=\hat{x} \{(\exists \nu ).\nu \in \text{NC induct}.(BʻR)R_{v}x\}\\ &[*121·52.*122·1·16]\end{align}\]

`(B'R) R_ν x` is `Desc Beg R (fun b => Pnu R ν b x)`; the type of the apparent variable `ν`
(and of `NC induct`) is determined by nothing (✱121·02), so it is a type parameter `X`.

**Status.** proved (reading): convention Infin T (Prefatory Statement, VI): `R ∈ Prog` implies that some type has all inductive cardinals, so `NC induct` is taken at a type `X` with `InfinAx X`; in a finite `X` the inclusion `D'R ⊂ …` fails. -/
theorem pm122_3 {α X : Type*} (hX : InfinAx X) {R : α → α → Prop} :
    R ∈ Prog →
      dom R = {x | ∃ ν : Set (Set X), ν ∈ NCinduct ∧ Desc Beg R (fun b => Pnu R ν b x)} := by
  intro h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  have : Infinite X := infinAx_iff_infinite.1 hX
  rw [dom_seqRel]
  ext x
  show x ∈ Set.range f ↔ ∃ ν : Set (Set X), ν ∈ NCinduct ∧
    Desc Beg (SeqRel f) (fun b => Pnu (SeqRel f) ν b x)
  simp only [desc_beg_seqRel hf, pnu_seqRel hf]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨cardN X n, cardN_mem_NCinduct n, n, ⟨rfl, cardN_nonempty_of_infinite n⟩,
      inferInstance, 0, rfl, by rw [Nat.zero_add]⟩
  · rintro ⟨ν, -, j, -, -, m, -, rfl⟩
    exact ⟨m + j, rfl⟩

/-- ✱122·31. \(\vdash :R\in \text{Prog}.\nu \in \text{NC induct}-\iota ʻ0.\supset .\text{ᗡ}ʻR_{\nu }=\hat{y} \{\text{Nc}ʻR(BʻR\vdash\dashv y)>\nu\}\)

`Nc'R(B'R ⊢⊣ y) > ν` is a side of `>`, hence `N₀c'…` (✱117·03); `B'R` has the scope of the
inequality. The type of `ν` is free. Convention Infin T would take `NC induct` in a type with
all inductive cardinals; the proposition holds in every type, so no hypothesis is added. -/
theorem pm122_31 {α X : Type*} {R : α → α → Prop} {ν : Set (Set X)} :
    R ∈ Prog ∧ ν ∈ NCinduct \ ι zero →
      codom (Pnu R ν) = {y | Desc Beg R (fun b => n₀c (itvCC R b y) >ᶜ ν)} := by
  rintro ⟨h, hν⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨k, rfl⟩ := mem_NCinduct_ne_zero.1 hν
  ext y
  show (∃ x, Pnu (SeqRel f) (cardN X (k + 1)) x y) ↔
    Desc Beg (SeqRel f) (fun b => n₀c (itvCC (SeqRel f) b y) >ᶜ cardN X (k + 1))
  rw [desc_beg_seqRel hf, cardGt_cardN_iff (itvCC_seqRel_finite hf _ _)]
  by_cases hne : (cardN X (k + 1)).Nonempty
  · have := nonempty_of_cardN_succ hne
    simp only [pnu_seqRel_of_nonempty hf hne]
    constructor
    · rintro ⟨x, m, rfl, rfl⟩
      have h1 : (itvCC (SeqRel f) (f 0) (f (m + (k + 1)))).ncard = m + (k + 1) + 1 :=
        (ncard_itvCC_seqRel hf).2 ⟨0, rfl, by rw [Nat.zero_add]⟩
      exact ⟨hne, by omega⟩
    · rintro ⟨-, hlt⟩
      obtain ⟨c, hc⟩ : ∃ c, (itvCC (SeqRel f) (f 0) y).ncard = c + 1 :=
        ⟨_, (Nat.sub_add_cancel (by omega : 1 ≤ (itvCC (SeqRel f) (f 0) y).ncard)).symm⟩
      obtain ⟨m, hm, rfl⟩ := (ncard_itvCC_seqRel hf).1 hc
      have hm0 : m = 0 := (hf hm).symm
      subst hm0
      exact ⟨f (c - (k + 1)), c - (k + 1), rfl, by congr 1; omega⟩
  · exact ⟨fun ⟨_, hp⟩ => absurd hp (pnu_seqRel_of_empty hf hne), fun h => absurd h.1 hne⟩

/-- ✱122·32. \[\begin{align}\vdash :R\in \text{Prog}.\nu \in &\text{NC induct}-\iota ʻ0.\supset .\\ &\overrightarrow{B}ʻR_{\nu }=\text{D}ʻR\cap \hat{x} \{\text{Nc}ʻR(BʻR\vdash\dashv x)\leq \nu\}\end{align}\]

`B⃗'R_ν` is `refs Beg (Pnu R ν)`; `Nc'R(B'R ⊢⊣ x) ≤ ν` is `N₀c'… ≤ ν` (note to ✱117·06).
As in ✱122·31, no Infin T hypothesis is needed. -/
theorem pm122_32 {α X : Type*} {R : α → α → Prop} {ν : Set (Set X)} :
    R ∈ Prog ∧ ν ∈ NCinduct \ ι zero →
      refs Beg (Pnu R ν) = dom R ∩ {x | Desc Beg R (fun b => n₀c (itvCC R b x) ≤ᶜ ν)} := by
  rintro ⟨h, hν⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨k, rfl⟩ := mem_NCinduct_ne_zero.1 hν
  ext x
  show Beg x (Pnu (SeqRel f) (cardN X (k + 1))) ↔ x ∈ dom (SeqRel f) ∧
    Desc Beg (SeqRel f) (fun b => cardN X (k + 1) ≥ᶜ n₀c (itvCC (SeqRel f) b x))
  rw [desc_beg_seqRel hf, cardGe_cardN_iff (itvCC_seqRel_finite hf _ _), dom_seqRel]
  by_cases hne : (cardN X (k + 1)).Nonempty
  · rw [beg_pnu_seqRel hf hne]
    constructor
    · rintro ⟨m, hm, rfl⟩
      have h1 : (itvCC (SeqRel f) (f 0) (f m)).ncard = m + 1 :=
        (ncard_itvCC_seqRel hf).2 ⟨0, rfl, by rw [Nat.zero_add]⟩
      exact ⟨⟨m, rfl⟩, hne, by omega⟩
    · rintro ⟨⟨m, rfl⟩, -, hle⟩
      have h1 : (itvCC (SeqRel f) (f 0) (f m)).ncard = m + 1 :=
        (ncard_itvCC_seqRel hf).2 ⟨0, rfl, by rw [Nat.zero_add]⟩
      exact ⟨m, by omega, rfl⟩
  · refine ⟨fun hb => ?_, fun h => absurd h.2.1 hne⟩
    obtain ⟨y, hy⟩ := hb.1
    exact absurd hy (pnu_seqRel_of_empty hf hne)

/-- ✱122·33. \(\vdash :R\in \text{Prog}.\nu \in \text{NC induct}-\iota ʻ0.\supset .\text{E}!\nu _{R}\)

**Status.** proved (reading): convention Infin T (Prefatory Statement, VI; PM's own example of the convention): the type `X` of `ν`, which nothing determines, has all inductive cardinals (`InfinAx X`); in a finite `X` the inductive cardinal `Λ` has no `Λ_R`. -/
theorem pm122_33 {α X : Type*} (hX : InfinAx X) {R : α → α → Prop} {ν : Set (Set X)} :
    R ∈ Prog ∧ ν ∈ NCinduct \ ι zero → EDesc (nuP ν) R := by
  rintro ⟨h, hν⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨k, rfl⟩ := mem_NCinduct_ne_zero.1 hν
  have : Infinite X := infinAx_iff_infinite.1 hX
  rw [EDesc_iff_desc_true, desc_nuP_seqRel hf (cardN_nonempty_of_infinite _)]
  trivial

/-- ✱122·34. \(\vdash \colon\ldotp R\in \text{Prog}.\supset :\nu \in \text{NC induct}-\iota ʻ0.\equiv .\text{E}!\nu _{R} \quad[*122·33.*121·635]\)

**Status.** proved (reading): convention Infin T, as in ✱122·33 (`InfinAx X` for the type `X` of `ν`); it is needed for `⊃` only. -/
theorem pm122_34 {α X : Type*} (hX : InfinAx X) {R : α → α → Prop} {ν : Set (Set X)} :
    R ∈ Prog → (ν ∈ NCinduct \ ι zero ↔ EDesc (nuP ν) R) := by
  intro h
  refine ⟨fun hν => pm122_33 hX ⟨h, hν⟩, fun hE => ?_⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨k, rfl, -⟩ := cardN_of_EDesc_nuP hf hE
  exact mem_NCinduct_ne_zero.2 ⟨k, rfl⟩

/-- ✱122·341. \(\vdash :R\in \text{Prog}.\supset .\text{D}ʻR=\hat{x} \{(\exists \nu ).\nu \in \text{NC induct}-\iota ʻ0.x=\nu _{R}\}\)

**Status.** proved (reading): convention Infin T, as in ✱122·33 (`InfinAx X` for the type `X` of the apparent variable `ν`). -/
theorem pm122_341 {α X : Type*} (hX : InfinAx X) {R : α → α → Prop} :
    R ∈ Prog →
      dom R = {x | ∃ ν : Set (Set X), ν ∈ NCinduct \ ι zero ∧ Desc (nuP ν) R (fun y => x = y)} := by
  intro h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  have : Infinite X := infinAx_iff_infinite.1 hX
  rw [dom_seqRel]
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨cardN X (n + 1), mem_NCinduct_ne_zero.2 ⟨n, rfl⟩,
      (desc_nuP_seqRel hf (cardN_nonempty_of_infinite _) _).2 rfl⟩
  · rintro ⟨ν, hν, hd⟩
    obtain ⟨k, rfl⟩ := mem_NCinduct_ne_zero.1 hν
    rw [desc_nuP_seqRel hf (cardN_nonempty_of_infinite _)] at hd
    exact ⟨k, hd.symm⟩

/-- ✱122·35. \(\vdash :R\in \text{Prog}.\nu \in \text{NC induct}-\iota ʻ0.\supset .\overrightarrow{B}ʻR_{\nu }=R(1_{R}\vdash\dashv \nu _{R}).\overrightarrow{B}ʻR_{\nu }\in \nu\)

`B⃗'R_ν ∈ ν` forces `ν` into the type of the classes of terms of `R` (`ν : Set (Set α)`), and
then `NC induct` has every inductive cardinal (`R ∈ Prog`), so Infin T adds nothing. In
`R(1_R ⊢⊣ ν_R)` the description `1_R` occurs first and has the larger scope; the `1` is a
constant whose type `W` nothing determines.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): `[Nonempty W]` for the type of the `1` of `1_R` (in an empty type `1 = Λ` and `1_R` does not exist). -/
theorem pm122_35 {α W : Type*} [Nonempty W] {R : α → α → Prop} {ν : Set (Set α)} :
    R ∈ Prog ∧ ν ∈ NCinduct \ ι zero →
      Desc (nuP (one : Set (Set W))) R
          (fun a => Desc (nuP ν) R (fun c => refs Beg (Pnu R ν) = itvCC R a c)) ∧
        refs Beg (Pnu R ν) ∈ ν := by
  rintro ⟨h, hν⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨k, rfl⟩ := mem_NCinduct_ne_zero.1 hν
  have : Infinite α := Infinite.of_injective f hf
  have hne := cardN_nonempty_of_infinite (β := α) (k + 1)
  have hbeg : refs Beg (Pnu (SeqRel f) (cardN α (k + 1))) = itvCC (SeqRel f) (f 0) (f k) := by
    ext x
    show Beg x (Pnu (SeqRel f) (cardN α (k + 1))) ↔ _
    rw [beg_pnu_seqRel hf hne, itvCC_seqRel hf]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, ⟨Nat.zero_le m, hm⟩, rfl⟩
    · rintro ⟨m, ⟨-, hm⟩, rfl⟩
      exact ⟨m, hm, rfl⟩
  rw [desc_nuP_one_seqRel hf, desc_nuP_seqRel hf hne, hbeg]
  exact ⟨rfl, itvCC_seqRel_finite hf _ _, (ncard_itvCC_seqRel hf).2 ⟨0, rfl, by rw [Nat.zero_add]⟩⟩

/-- ✱122·36. \(\vdash :\exists !\text{Prog}\cap t^{11}ʻx.\supset .\text{Infin ax}(x)\)

`t¹¹'x` is `typ11 x`, the type of the relations between terms of the type of `x`. -/
theorem pm122_36 {α : Type*} {x : α} : (Prog ∩ typ11 x).Nonempty → InfinAxAt x := by
  rintro ⟨R, hR, -⟩
  rw [infinAxAt_iff, infinAx_iff_infinite]
  exact infinite_of_prog hR

/-- ✱122·37. \(\vdash :R\in \text{Prog}.\supset .\text{D}ʻR{\sim}\in \text{Cls induct}.\text{N}_{0}\text{c}ʻ\text{D}ʻR{\sim}\in \text{NC induct}\) -/
theorem pm122_37 {α : Type*} {R : α → α → Prop} :
    R ∈ Prog → dom R ∉ ClsInduct ∧ n₀c (dom R) ∉ NCinduct := by
  intro h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  have hinf : (dom (SeqRel f)).Infinite := by
    rw [dom_seqRel]; exact Set.infinite_range_of_injective hf
  refine ⟨fun h => hinf (mem_ClsInduct.1 h), fun h => ?_⟩
  rcases NCinduct_cases h with ⟨A, hA, he⟩ | ⟨hfin, -⟩
  · obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 he)
    have : Finite A := hA.to_subtype
    exact hinf (Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm))
  · exact (not_finite_iff_infinite.2 (Infinite.of_injective f hf)) hfin

/-- ✱122·38. \(\vdash :R\in \text{Prog}.\supset .\overrightarrow{R}_{*}ʻx\in \text{Cls induct} \quad[*121·7.*90·13.*120·212]\) -/
theorem pm122_38 {α : Type*} {R : α → α → Prop} {x : α} :
    R ∈ Prog → refs (anc R) x ∈ ClsInduct := by
  intro h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [mem_ClsInduct]
  by_cases hx : x ∈ Set.range f
  · obtain ⟨n, rfl⟩ := hx
    refine ((finite_Icc_nat 0 n).image f).subset ?_
    intro z hz
    obtain ⟨a, b, hab, rfl, hb⟩ := (anc_seqRel hf).1 (show anc (SeqRel f) z (f n) from hz)
    rw [← hf hb] at hab
    exact ⟨a, ⟨Nat.zero_le a, hab⟩, rfl⟩
  · refine Set.finite_empty.subset fun z hz => hx ?_
    exact (anc_seqRel_mem hf (show anc (SeqRel f) z x from hz)).2

/-- ✱122·381. \[\begin{align}&\vdash :R\in \text{Prog}.\nu \in \text{NC induct}-\iota ʻ0.\supset .\overrightarrow{R}_{*}ʻ\nu _{R}=R(1_{R}\vdash\dashv \nu _{R}).\overrightarrow{R}_{*}ʻ\nu _{R}\in \nu \\ &[*121·7.*122·35]\end{align}\]

As in ✱122·35, `R⃗_*'ν_R ∈ ν` puts `ν` in the type of the classes of terms of `R`, and the
`1` of `1_R` has its own type `W`. In `R⃗_*'ν_R = R(1_R ⊢⊣ ν_R)` the descriptions are taken in
the order of occurrence, the first with the largest scope.

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): `[Nonempty W]` for the type of the `1` of `1_R`. -/
theorem pm122_381 {α W : Type*} [Nonempty W] {R : α → α → Prop} {ν : Set (Set α)} :
    R ∈ Prog ∧ ν ∈ NCinduct \ ι zero →
      Desc (nuP ν) R (fun c => Desc (nuP (one : Set (Set W))) R
          (fun a => Desc (nuP ν) R (fun c' => refs (anc R) c = itvCC R a c'))) ∧
        Desc (nuP ν) R (fun c => refs (anc R) c ∈ ν) := by
  rintro ⟨h, hν⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨k, rfl⟩ := mem_NCinduct_ne_zero.1 hν
  have : Infinite α := Infinite.of_injective f hf
  have hne := cardN_nonempty_of_infinite (β := α) (k + 1)
  have hanc : refs (anc (SeqRel f)) (f k) = itvCC (SeqRel f) (f 0) (f k) := by
    rw [itvCC_seqRel hf]
    ext z
    show anc (SeqRel f) z (f k) ↔ _
    rw [anc_seqRel hf]
    constructor
    · rintro ⟨a, b, hab, rfl, hb⟩
      rw [← hf hb] at hab
      exact ⟨a, ⟨Nat.zero_le a, hab⟩, rfl⟩
    · rintro ⟨a, ⟨-, ha⟩, rfl⟩
      exact ⟨a, k, ha, rfl, rfl⟩
  simp only [desc_nuP_one_seqRel hf, desc_nuP_seqRel hf hne]
  rw [hanc]
  exact ⟨rfl, itvCC_seqRel_finite hf _ _, (ncard_itvCC_seqRel hf).2 ⟨0, rfl, by rw [Nat.zero_add]⟩⟩

/-- ✱122·42. \(\vdash :R\in \text{Prog}.\alpha \subset R(BʻR\vdash\dashv y).y\in \alpha .\supset .y= \text{max}_{R}ʻ\alpha\)

The e-text prints `max_R'α`; with `max_R` the proposition is false (`pm122_42_printed_false`),
and PM's demonstration (`y ∼∈ R_po''α`, ✱93·115 applied to `R_po`) proves `y = max(R_po)'α`,
as in ✱122·27·28. `α ⊂ R(B'R ⊢⊣ y)` is `Desc Beg R (fun b => A ⊆ itvCC R b y)`.

**Status.** proved (corrected): `max_R'α` replaced by `max(R_po)'α`. With `max_R` it is false: in the progression `n ↦ n + 1` on `ℕ`, `α = {0, 2} ⊂ R(0 ⊢⊣ 2)` has the two `R`-maxima `0` and `2`, so `max_R'α` does not exist. -/
theorem pm122_42 {α : Type*} {R : α → α → Prop} {A : Set α} {y : α} :
    (R ∈ Prog ∧ Desc Beg R (fun b => A ⊆ itvCC R b y)) ∧ y ∈ A →
      Desc (maxP (po R)) A (fun m => y = m) := by
  rintro ⟨⟨h, hA⟩, hy⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [desc_beg_seqRel hf] at hA
  obtain ⟨n, rfl⟩ : y ∈ Set.range f := (anc_seqRel_mem hf (hA hy).1).2
  have hle : ∀ z ∈ A, ∃ i, i ≤ n ∧ z = f i := fun z hz => by
    rw [itvCC_seqRel hf] at hA
    obtain ⟨i, ⟨-, hi⟩, rfl⟩ := hA hz
    exact ⟨i, hi, rfl⟩
  refine desc_iff_of_unique (b := f n) (fun x => ?_) _ |>.2 rfl
  show minP (po (SeqRel f))˘ x A ↔ _
  rw [minP_apply, fld_cnv, fld_po_seqRel hf]
  constructor
  · rintro ⟨⟨hx, -⟩, hno⟩
    obtain ⟨i, hi, rfl⟩ := hle x hx
    rcases Nat.lt_or_ge i n with hlt | hge
    · exact absurd ⟨f n, hy, (po_seqRel' hf).2 hlt⟩ hno
    · rw [show i = n by omega]
  · rintro rfl
    refine ⟨⟨hy, n, rfl⟩, ?_⟩
    rintro ⟨z, hz, hnz⟩
    obtain ⟨i, hi, rfl⟩ := hle z hz
    have := (po_seqRel' hf).1 hnz
    omega

/-- The printed form of ✱122·42 (with `max_R`) is false. -/
theorem pm122_42_printed_false :
    ¬ ∀ (R : ℕ → ℕ → Prop) (A : Set ℕ) (y : ℕ),
      (R ∈ Prog ∧ Desc Beg R (fun b => A ⊆ itvCC R b y)) ∧ y ∈ A →
        Desc (maxP R) A (fun m => y = m) := by
  intro H
  have hf : Function.Injective (id : ℕ → ℕ) := Function.injective_id
  have hI : itvCC (SeqRel id) 0 2 = id '' {i | 0 ≤ i ∧ i ≤ 2} := itvCC_seqRel hf 0 2
  have hsub : ({0, 2} : Set ℕ) ⊆ itvCC (SeqRel id) 0 2 := by
    rw [hI]
    rintro z (rfl | rfl)
    · exact ⟨0, ⟨le_rfl, by omega⟩, rfl⟩
    · exact ⟨2, ⟨by omega, le_rfl⟩, rfl⟩
  have hD := H (SeqRel id) {0, 2} 2
    ⟨⟨seqRel_mem_prog hf, (desc_beg_seqRel hf (fun b => ({0, 2} : Set ℕ) ⊆ itvCC (SeqRel id) b 2)).2 hsub⟩,
      Or.inr rfl⟩
  obtain ⟨b, hb, -⟩ := hD
  have hmax : ∀ c : ℕ, c ∈ ({0, 2} : Set ℕ) → maxP (SeqRel id) c {0, 2} := by
    intro c hc
    show minP (SeqRel id)˘ c {0, 2}
    rw [minP_apply]
    refine ⟨⟨hc, c + 1, Or.inr ⟨c, rfl, rfl⟩⟩, ?_⟩
    rintro ⟨z, hz, n, hn, rfl⟩
    have hn' : c = n := hn
    subst hn'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, id] at hz hc
    omega
  have h0 := (hb 0).1 (hmax 0 (Or.inl rfl))
  have h2 := (hb 2).1 (hmax 2 (Or.inr rfl))
  omega

/-- ✱122·43. \[\begin{align}&\vdash :R\in \text{Prog}.\alpha \subset \text{D}ʻR.\exists !\alpha -R_{\text{po}}ʻʻ\alpha .\supset .\alpha \in \text{Cls induct}\\ &[*122·41.*121·45.*120·481]\end{align}\] -/
theorem pm122_43 {α : Type*} {R : α → α → Prop} {A : Set α} :
    (R ∈ Prog ∧ A ⊆ dom R) ∧ (A \ po R ʻʻ A).Nonempty → A ∈ ClsInduct := by
  rintro ⟨⟨h, hA⟩, ⟨a, haA, ha⟩⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [dom_seqRel] at hA
  rw [mem_ClsInduct]
  obtain ⟨N, rfl⟩ := hA haA
  refine ((finite_Icc_nat 0 N).image f).subset fun z hz => ?_
  obtain ⟨i, rfl⟩ := hA hz
  refine ⟨i, ⟨Nat.zero_le i, ?_⟩, rfl⟩
  by_contra hi
  exact ha ⟨f i, hz, (po_seqRel' hf).2 (by omega)⟩

/-- ✱122·44. \[\begin{align}\vdash :R\in \text{Prog} .\alpha \subset R_{\text{po}}ʻʻ\alpha .\exists !\alpha .P=R_{\text{po}}\unicode{x0294f}\alpha .Q&=P\dot{-} P^{2}.\supset .\\ &Q\in 1\rightarrow 1.Q\,\unicode{x2abd}\, R_{\text{po}}\end{align}\]

`P = R_po ⥏ α . Q = P −̇ P²` are hypotheses (the products bracket to the left); `P²` is
`rsq P`, `P −̇ P²` is `P ∸ rsq P`. -/
theorem pm122_44 {α : Type*} {R P Q : α → α → Prop} {A : Set α} :
    (((R ∈ Prog ∧ A ⊆ po R ʻʻ A) ∧ A.Nonempty) ∧ P = po R ⥏ A) ∧ Q = P ∸ rsq P →
      Q ∈ arrow one one ∧ Q ⪽ po R := by
  rintro ⟨⟨⟨⟨h, hA⟩, hne⟩, rfl⟩, rfl⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨g, hg, hQ, -, hpo, -⟩ := pm122_44_core hf hA hne
  rw [hQ]
  refine ⟨seqRel_oneone hg, ?_⟩
  rintro x y ⟨n, rfl, rfl⟩
  exact hpo n (n + 1) (Nat.lt_succ_self n)

/-- ✱122·441. \(\vdash :\text{Hp}*122·44.\supset .\text{D}ʻQ=\alpha\) -/
theorem pm122_441 {α : Type*} {R P Q : α → α → Prop} {A : Set α} :
    (((R ∈ Prog ∧ A ⊆ po R ʻʻ A) ∧ A.Nonempty) ∧ P = po R ⥏ A) ∧ Q = P ∸ rsq P →
      dom Q = A := by
  rintro ⟨⟨⟨⟨h, hA⟩, hne⟩, rfl⟩, rfl⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨g, -, hQ, hrange, -, -⟩ := pm122_44_core hf hA hne
  rw [hQ, dom_seqRel, hrange]

/-- ✱122·443. \(\vdash :\text{Hp}*122·44.\supset .\text{min}(R_{\text{po}})ʻ\alpha =BʻQ.\text{ᗡ}ʻQ=\alpha \cap \breve{R} _{\text{po}}ʻʻ\alpha \)

`min(R_po)'α = B'Q`: the description occurring first has the larger scope. -/
theorem pm122_443 {α : Type*} {R P Q : α → α → Prop} {A : Set α} :
    (((R ∈ Prog ∧ A ⊆ po R ʻʻ A) ∧ A.Nonempty) ∧ P = po R ⥏ A) ∧ Q = P ∸ rsq P →
      Desc (minP (po R)) A (fun m => Desc Beg Q (fun b => m = b)) ∧
        codom Q = A ∩ (po R)˘ ʻʻ A := by
  rintro ⟨⟨⟨⟨h, hA⟩, hne⟩, rfl⟩, rfl⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨g, hg, hQ, hrange, hpo, hfirst⟩ := pm122_44_core hf hA hne
  rw [hQ]
  have hmemA : ∀ q, g q ∈ A := fun q => by rw [← hrange]; exact ⟨q, rfl⟩
  have hg0 : g 0 ∈ A := hmemA 0
  have hmin : ∀ x, minP (po (SeqRel f)) x A ↔ x = g 0 := by
    intro x
    rw [minP_apply, fld_po_seqRel hf]
    constructor
    · rintro ⟨⟨hx, -⟩, hno⟩
      rw [← hrange] at hx
      obtain ⟨q, rfl⟩ := hx
      cases q with
      | zero => rfl
      | succ q => exact absurd ⟨g q, hmemA q, hpo q (q + 1) (Nat.lt_succ_self q)⟩ hno
    · rintro rfl
      refine ⟨⟨hg0, (po_seqRel_mem hf (hpo 0 1 Nat.one_pos)).1⟩, ?_⟩
      rintro ⟨y, hy, hy0⟩
      exact hfirst y hy hy0
  refine ⟨(desc_iff_of_unique hmin _).2 ((desc_beg_seqRel hg _).2 rfl), ?_⟩
  rw [codom_seqRel]
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨hmemA (q + 1), g q, hmemA q, hpo q (q + 1) (Nat.lt_succ_self q)⟩
  · rintro ⟨hy, a, ha, hay⟩
    rw [← hrange] at hy
    obtain ⟨q, rfl⟩ := hy
    cases q with
    | zero => exact absurd hay (hfirst a ha)
    | succ q => exact ⟨q, rfl⟩

/-- ✱122·444. \(\vdash :\text{Hp}*122·44.\supset .\text{D}ʻQ=\overleftarrow{Q}_{*}ʻBʻQ\) -/
theorem pm122_444 {α : Type*} {R P Q : α → α → Prop} {A : Set α} :
    (((R ∈ Prog ∧ A ⊆ po R ʻʻ A) ∧ A.Nonempty) ∧ P = po R ⥏ A) ∧ Q = P ∸ rsq P →
      Desc Beg Q (fun b => dom Q = rels (anc Q) b) := by
  rintro ⟨⟨⟨⟨h, hA⟩, hne⟩, rfl⟩, rfl⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨g, hg, hQ, -, -, -⟩ := pm122_44_core hf hA hne
  rw [hQ]
  exact (seqRel_mem_prog hg).2

/-- ✱122·45. \[\begin{align}&\vdash :R\in \text{Prog}.\alpha \subset R_{\text{po}}ʻʻ\alpha .\exists !\alpha .P = R_{\text{po}}\unicode{x0294f}\alpha .Q = P\dot{-} P^{2}.\supset .\\ &Q\in \text{Prog}.\text{D}ʻQ = \alpha \quad[*122·44·444·441]\end{align}\] -/
theorem pm122_45 {α : Type*} {R P Q : α → α → Prop} {A : Set α} :
    (((R ∈ Prog ∧ A ⊆ po R ʻʻ A) ∧ A.Nonempty) ∧ P = po R ⥏ A) ∧ Q = P ∸ rsq P →
      Q ∈ Prog ∧ dom Q = A := by
  rintro ⟨⟨⟨⟨h, hA⟩, hne⟩, rfl⟩, rfl⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨g, hg, hQ, hrange, -, -⟩ := pm122_44_core hf hA hne
  rw [hQ, dom_seqRel, hrange]
  exact ⟨seqRel_mem_prog hg, rfl⟩

/-- ✱122·46. \[\begin{align}&\vdash :R\in \text{Prog}.\alpha \subset \text{D}ʻR.\supset :\alpha \in \text{Cls induct} \cup \text{D}ʻʻ\text{Prog}\\ &[*122·43·45.*120·212]\end{align}\]

`D''Prog` is printed (it is `ℵ₀`, ✱123·01). -/
theorem pm122_46 {α : Type*} {R : α → α → Prop} {A : Set α} :
    R ∈ Prog ∧ A ⊆ dom R → A ∈ ClsInduct ∪ D ʻʻ Prog := by
  rintro ⟨h, hA⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [dom_seqRel] at hA
  by_cases hfin : A.Finite
  · exact Or.inl (mem_ClsInduct.2 hfin)
  · exact Or.inr (aleph0_of_infinite_sub_range hA hfin)

/-- ✱122·47. \(\vdash \colon\ldotp R\in \text{Prog}.\alpha \subset \text{D}ʻR.\supset :\alpha \in \text{Cls induct} - \iota ʻ\Lambda .\equiv .\exists !\alpha -R_{\text{po}}ʻʻ\alpha \) -/
theorem pm122_47 {α : Type*} {R : α → α → Prop} {A : Set α} :
    R ∈ Prog ∧ A ⊆ dom R → (A ∈ ClsInduct \ ι Λ ↔ (A \ po R ʻʻ A).Nonempty) := by
  rintro ⟨h, hA⟩
  constructor
  · rintro ⟨hind, hΛ⟩
    obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
    rw [dom_seqRel] at hA
    have hfin := mem_ClsInduct.1 hind
    have hne : A.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro e
      exact hΛ (by rw [mem_unitCls, e, Null_eq_empty])
    obtain ⟨a, ha⟩ := hne
    obtain ⟨k, rfl⟩ := hA ha
    obtain ⟨M, hM, hMmax⟩ :=
      Set.Finite.exists_maximal (hfin.preimage (fun a _ b _ h => hf h)) ⟨k, ha⟩
    refine ⟨f M, hM, ?_⟩
    rintro ⟨y, hy, hMy⟩
    obtain ⟨m, n, hmn, hm, rfl⟩ := (po_seqRel hf).1 hMy
    rw [← hf hm] at hmn
    have := hMmax (show n ∈ f ⁻¹' A from hy) (le_of_lt hmn)
    omega
  · intro hne
    refine ⟨pm122_43 ⟨⟨h, hA⟩, hne⟩, fun hΛ => ?_⟩
    obtain ⟨a, ha, -⟩ := hne
    rw [mem_unitCls, Null_eq_empty] at hΛ
    rw [hΛ] at ha
    exact ha

/-- ✱122·48. \(\vdash :R\in \text{Prog}.\alpha \subset \text{D}ʻR.\alpha \in \text{Cls induct}.\supset .\text{D}ʻR-\alpha {\sim}\in \text{Cls induct}\) -/
theorem pm122_48 {α : Type*} {R : α → α → Prop} {A : Set α} :
    (R ∈ Prog ∧ A ⊆ dom R) ∧ A ∈ ClsInduct → dom R \ A ∉ ClsInduct := by
  rintro ⟨⟨h, hA⟩, hind⟩ hd
  apply (pm122_37 h).1
  rw [mem_ClsInduct] at hind hd ⊢
  rw [← Set.sdiff_union_of_subset hA]
  exact hd.union hind

/-- ✱122·49. \[\begin{align}&\vdash :R\in \text{Prog}.\alpha \subset \text{D}ʻR.\alpha \in \text{Cls induct}.\supset .\text{D}ʻR-\alpha \in \text{D}ʻʻ\text{Prog}\\ &[*122·46·48]\end{align}\] -/
theorem pm122_49 {α : Type*} {R : α → α → Prop} {A : Set α} :
    (R ∈ Prog ∧ A ⊆ dom R) ∧ A ∈ ClsInduct → dom R \ A ∈ D ʻʻ Prog := by
  rintro ⟨⟨h, hA⟩, hind⟩
  have h48 := pm122_48 ⟨⟨h, hA⟩, hind⟩
  rcases pm122_46 ⟨h, Set.sdiff_subset⟩ with h1 | h1
  · exact absurd h1 h48
  · exact h1

/-- ✱122·51. \(\vdash :P\in \text{Cls}\rightarrow 1.I_{P}ʻx=\Lambda .x\in \text{D}ʻP.\overleftarrow{P}_{*}ʻx\subset \text{D}ʻP.\supset .(\overleftarrow{P}_{*}ʻx)\upharpoonleft P\in \text{Prog}\)

`I_P'x` is `IR P x` (Dft ✱96·01), the cyclic part of the posterity of `x`. -/
theorem pm122_51 {α : Type*} {P : α → α → Prop} {x : α} :
    ((P ∈ arrow Cls one ∧ IR P x = Λ) ∧ x ∈ dom P) ∧ rels (anc P) x ⊆ dom P →
      rels (anc P) x ◁ P ∈ Prog := by
  rintro ⟨⟨⟨hfun, hIR⟩, hx⟩, hdom⟩
  rw [mem_arrow_Cls_one] at hfun
  obtain ⟨f, -, hstep, hrange⟩ := post_seq hfun hx hdom
  have key : ∀ a b, a < b → f a ≠ f b := fun a b hab he => by
    have hpo := po_of_steps hstep hab
    rw [← he] at hpo
    have hmem : f a ∈ IR P x := ⟨by rw [hrange]; exact ⟨a, rfl⟩, hpo⟩
    rw [hIR, Null_eq_empty] at hmem
    exact hmem
  have hinj : Function.Injective f := by
    intro m n hmn
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key m n h hmn
    · exact key n m h hmn.symm
  exact prog_of_post_seq hfun hinj hstep hrange

/-- ✱122·52. \(\vdash :P\in 1\rightarrow 1.x\in \text{D}ʻP.{\sim}(xP_{\text{po}}x).\overleftarrow{P}_{*}ʻx\subset \text{D}ʻP.\supset .(\overleftarrow{P}_{*}ʻx)\upharpoonleft P\in \text{Prog}\) -/
theorem pm122_52 {α : Type*} {P : α → α → Prop} {x : α} :
    ((P ∈ arrow one one ∧ x ∈ dom P) ∧ ¬ po P x x) ∧ rels (anc P) x ⊆ dom P →
      rels (anc P) x ◁ P ∈ Prog := by
  rintro ⟨⟨⟨h11, hx⟩, hxx⟩, hdom⟩
  obtain ⟨hinj, hfun⟩ := mem_arrow_one_one.1 h11
  obtain ⟨f, h0, hstep, hrange⟩ := post_seq hfun hx hdom
  have hne : ∀ m k, f m ≠ f (m + k + 1) := by
    intro m
    induction m with
    | zero =>
      intro k he
      have hpo := po_of_steps hstep (show 0 < 0 + k + 1 by omega)
      rw [← he, h0] at hpo
      exact hxx hpo
    | succ m ih =>
      intro k he
      apply ih k
      apply hinj _ _ (f (m + 1))
      refine ⟨hstep m, ?_⟩
      rw [he, show m + 1 + k + 1 = m + k + 1 + 1 by omega]
      exact hstep _
  have hfinj : Function.Injective f := by
    intro m n h
    rcases lt_trichotomy m n with hlt | heq | hgt
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      exact absurd h (hne m k)
    · exact heq
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
      exact absurd h.symm (hne n k)
  exact prog_of_post_seq hfun hfinj hstep hrange

/-- ✱122·53. \(\vdash :P\in 1\rightarrow 1.x\in sʻ \text{gen}ʻP.\overleftarrow{P}_{*}ʻx\subset \text{D}ʻP.\supset .(\overleftrightarrow{P}_{*}ʻx)\upharpoonleft P\in \text{Prog}\)

`P⃡_*'x`, the family of `x`, is `refsRels (anc P) x` (✱97·01); `s'gen'P` is `sumCls (gen P)`. -/
theorem pm122_53 {α : Type*} {P : α → α → Prop} {x : α} :
    (P ∈ arrow one one ∧ x ∈ sumCls (gen P)) ∧ rels (anc P) x ⊆ dom P →
      refsRels (anc P) x ◁ P ∈ Prog := by
  rintro ⟨⟨h11, hx⟩, hdom⟩
  obtain ⟨hinj, hfun⟩ := mem_arrow_one_one.1 h11
  obtain ⟨y, hy, hyx⟩ := (mem_sumCls_gen_iff hinj).1 hx
  have hxf : x ∈ fld P := fld_of_anc_right hyx
  have hfam : refsRels (anc P) x = rels (anc P) y := by
    ext w
    constructor
    · rintro ((hw | ⟨rfl, -⟩) | hw)
      · obtain ⟨hwf, hwx⟩ := anc_iff_reflTransGen.1 (show anc P w x from hw)
        rcases rtg_linear_bwd hinj (anc_iff_reflTransGen.1 hyx).2 hwx with h | h
        · exact anc_iff_reflTransGen.2 ⟨hy.1.elim (fun z hz => ⟨z, Or.inl hz⟩), h⟩
        · rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, -, hcy⟩
          · exact anc_refl hwf
          · exact absurd ⟨c, hcy⟩ hy.2
      · exact hyx
      · exact anc_trans hyx hw
    · intro hw
      have hw' : anc P y w := hw
      have hwf := fld_of_anc_right hw'
      rcases rtg_linear_fwd hfun (anc_iff_reflTransGen.1 hw').2 (anc_iff_reflTransGen.1 hyx).2
        with h | h
      · exact Or.inl (Or.inl (anc_iff_reflTransGen.2 ⟨hwf, h⟩))
      · exact Or.inr (anc_iff_reflTransGen.2 ⟨hxf, h⟩)
  rw [hfam]
  refine pm122_52 ⟨⟨⟨h11, hy.1⟩, fun hpo => ?_⟩, fun w hw => ?_⟩
  · rw [po_iff_transGen] at hpo
    obtain ⟨c, -, hcy⟩ := Relation.TransGen.tail'_iff.1 hpo
    exact hy.2 ⟨c, hcy⟩
  · have hw' : anc P y w := hw
    rcases rtg_linear_fwd hfun (anc_iff_reflTransGen.1 hw').2 (anc_iff_reflTransGen.1 hyx).2
      with h | h
    · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hwc, -⟩
      · exact hdom (anc_refl hxf)
      · exact ⟨c, hwc⟩
    · exact hdom (anc_iff_reflTransGen.2 ⟨hxf, h⟩)

/-- ✱122·54. \(\vdash :P\in 1\rightarrow 1.x\in sʻ \text{gen}ʻP-sʻ \text{gen}ʻ\breve{P} .\supset .(\overleftrightarrow{P}_{*}ʻx)\upharpoonleft P\in \text{Prog}\) -/
theorem pm122_54 {α : Type*} {P : α → α → Prop} {x : α} :
    P ∈ arrow one one ∧ x ∈ sumCls (gen P) \ sumCls (gen P˘) → refsRels (anc P) x ◁ P ∈ Prog := by
  rintro ⟨h11, hx, hnx⟩
  obtain ⟨hinj, hfun⟩ := mem_arrow_one_one.1 h11
  refine pm122_53 ⟨⟨h11, hx⟩, fun w hw => ?_⟩
  by_contra hwd
  apply hnx
  rw [mem_sumCls_gen_iff (P := P˘) (fun a b c h => hfun c a b ⟨h.1, h.2⟩)]
  have hw' : anc P x w := hw
  have hwf := fld_of_anc_right hw'
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨v, hv | hv⟩ := hwf
    · exact absurd ⟨v, hv⟩ hwd
    · exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact hwd ⟨v, hv⟩
  · exact ancCnv_iff.1 hw'

/-- ✱122·55. \(\vdash \colon\ldotp P\in 1\rightarrow 1.\supset :x\in sʻ \text{gen}ʻP-sʻ \text{gen}ʻ\breve{P} .\equiv .(\overleftrightarrow{P}_{*}ʻx)\upharpoonleft P\in \text{Prog}\) -/
theorem pm122_55 {α : Type*} {P : α → α → Prop} {x : α} :
    P ∈ arrow one one →
      (x ∈ sumCls (gen P) \ sumCls (gen P˘) ↔ refsRels (anc P) x ◁ P ∈ Prog) := by
  intro h11
  refine ⟨fun hx => pm122_54 ⟨h11, hx⟩, fun hQ => ?_⟩
  obtain ⟨hinj, hfun⟩ := mem_arrow_one_one.1 h11
  obtain ⟨g, hg, hQg⟩ := prog_iff_seq.1 hQ
  have hdomQ : ∀ u, u ∈ dom (refsRels (anc P) x ◁ P) ↔ u ∈ refsRels (anc P) x ∧ u ∈ dom P :=
    fun u => ⟨fun ⟨v, hu, huv⟩ => ⟨hu, v, huv⟩, fun ⟨hu, v, huv⟩ => ⟨v, hu, huv⟩⟩
  have hcd := (pm122_141 hQ).1
  have hpred : ∀ z v, P z v → v ∈ refsRels (anc P) x → z ∈ refsRels (anc P) x := by
    intro z v hzv hv
    have hzf : z ∈ fld P := ⟨v, Or.inl hzv⟩
    rcases hv with (hv | ⟨hvx, -⟩) | hv
    · exact Or.inl (Or.inl (anc_trans (anc_of_rel hzv) hv))
    · have hvx' : v = x := hvx
      subst hvx'
      exact Or.inl (Or.inl (anc_of_rel hzv))
    · obtain ⟨hxf, hr⟩ := anc_iff_reflTransGen.1 (show anc P x v from hv)
      rcases Relation.ReflTransGen.cases_tail hr with rfl | ⟨c, hxc, hcv⟩
      · exact Or.inl (Or.inl (anc_of_rel hzv))
      · rw [hinj _ _ _ ⟨hzv, hcv⟩]
        exact Or.inr (anc_iff_reflTransGen.2 ⟨hxf, hxc⟩)
  have hg0 : g 0 ∈ dom (refsRels (anc P) x ◁ P) := by rw [hQg, dom_seqRel]; exact ⟨0, rfl⟩
  have hxF : x ∈ fld P := by
    rcases ((hdomQ _).1 hg0).1 with (hw | ⟨hx0, ⟨y, hw | hw⟩⟩) | hw
    · exact fld_of_anc_right hw
    · rw [← (show g 0 = x from hx0)]; exact fld_of_anc_left hw
    · rw [← (show g 0 = x from hx0)]; exact fld_of_anc_right hw
    · exact fld_of_anc_left hw
  have hxFm : x ∈ refsRels (anc P) x := Or.inl (Or.inl (anc_refl hxF))
  have hxdom : x ∈ dom (refsRels (anc P) x ◁ P) := by
    by_cases hxd : x ∈ dom P
    · exact (hdomQ x).2 ⟨hxFm, hxd⟩
    · obtain ⟨z, hz | hz⟩ := hxF
      · exact absurd ⟨z, hz⟩ hxd
      · exact hcd ⟨z, hpred z x hz hxFm, hz⟩
  refine ⟨?_, ?_⟩
  · rw [mem_sumCls_gen_iff hinj]
    refine ⟨g 0, ⟨((hdomQ _).1 hg0).2, ?_⟩, ?_⟩
    · rintro ⟨z, hz⟩
      have hc : g 0 ∈ codom (refsRels (anc P) x ◁ P) := ⟨z, hpred z (g 0) hz ((hdomQ _).1 hg0).1, hz⟩
      rw [hQg, codom_seqRel] at hc
      obtain ⟨n, hn⟩ := hc
      exact absurd (hg hn) (by omega)
    · rw [hQg, dom_seqRel] at hxdom
      obtain ⟨n, rfl⟩ := hxdom
      have h1 : anc (SeqRel g) (g 0) (g n) := (anc_seqRel' hg).2 (Nat.zero_le n)
      rw [← hQg] at h1
      exact anc_mono (fun a b h => h.2) h1
  · intro hx'
    rw [mem_sumCls_gen_iff (P := P˘) (fun a b c h => hfun c a b ⟨h.1, h.2⟩)] at hx'
    obtain ⟨e, ⟨⟨v, hv⟩, he2⟩, hex⟩ := hx'
    have hxe : anc P x e := ancCnv_iff.2 hex
    have heF : e ∈ refsRels (anc P) x := Or.inr hxe
    obtain ⟨w, -, hew⟩ := hcd ⟨v, hpred v e hv heF, hv⟩
    exact he2 ⟨w, hew⟩

/-!
## [✱123] \(\aleph _{0}\)

*(Vol. 2, p. 268)*

> *Summary of* *123.
>
> In this number we are concerned with the arithmetical properties of \(\aleph _{0}\), the smallest of Cantor's transfinite cardinals. Cantor defines \(\aleph _{0}\) as the cardinal number of any class which can be put into one-one relation with the inductive cardinals. This definition assumes that \(\nu \neq \nu +_{c}1\), when \(\nu\) is an inductive cardinal; in other words, it assumes the axiom of infinity; for without this, the inductive cardinals would form a finite series, with a last term, namely \(\Lambda\). For this reason among others, we do not make similarity with the inductive cardinals our *definition*. We define \(\aleph _{0}\) as the class of those classes which can be arranged in progressions, *i.e.* as \(\text{D}ʻʻ\text{Prog}\). We then have to prove that \(\aleph _{0}\) so defined is a cardinal, and that if it is not null, it is the number of the inductive numbers.
>
> For convenience we put for the moment \(N\) for the relation of \(\mu\) to \(\mu +_{c}1\) when \(\mu\) is an inductive cardinal. We then easily prove
>
> *123·21·23. \(\vdash .N\in \text{Cls}\rightarrow 1.\text{D}ʻN=\text{NC induct}.BʻN=0.\overleftarrow{N}_{*}ʻ0=\text{NC induct}\)
>
> …

**Lean reading.** `ℵ₀` is `aleph0 = D''Prog` (✱123·01) and `N` the Dft `Nsucc` (✱123·02). In
the proofs `ℵ₀` is the class of countably infinite classes, the inductive cardinals of a type are the
classes `cardN β k` of its `k`-membered classes, and `N` is the successor relation of the sequence
`0, 1, 2, …` of a type. `ℵ₀(x)` is `clsT2 aleph0 x`, `NC induct ∩ t³'x` is `NCinduct ∩ typ3 x`.
An `ℵ₀` subjected to `+_c`, `−_c`, `×_c`, `^` (an arithmetical component) has its own type `W`
with the IIT hypothesis `∃!ℵ₀` in `W` (PM's test (iii), `∃!N₀c't₁'ℵ₀`, is met in every type, and the
propositions then fail: `pm123_4_aux_IIT`); an `ℵ₀` that is a side of `>`, `≥` is in the type of
the hypothesis `∃!ℵ₀` (worked example ✱123·43 of `Defs/Part3`). `NC induct` whose type nothing
determines is taken under Infin T (`InfinAx X`), also when the hypothesis implying it comes from IIT
(✱123·41·411·422·53). In ✱123·501·51 PM's `D'P × D'Q` is corrected to `D'Q × D'P` (the order of
✱113·02). `NC` in ✱123·36 has the converse-domain type of PM's demonstration.

**Status.** proved (all propositions; ✱123·01 definition, ✱123·02 definition (Dft);
✱123·13·3·31·36·39·4·41·411·42·421·422·43·44·45·502·503·504·52·53 proved (reading),
✱123·501·51 proved (corrected), see their docstrings)
-/

/-- ✱123·01 (Df). \(\aleph _{0}=\text{D}ʻʻ\text{Prog} \quad\text{Df}\) -/
theorem pm123_01 {α : Type*} : (aleph0 : Set (Set α)) = D ʻʻ Prog := rfl

/-- ✱123·02. \(N=\hat{\mu} \hat{\nu} \{\mu \in \text{NC induct}.\nu =(\mu +_{c}1)\cap t_{0}ʻ\mu\} \quad\text{Dft} [*123—4]\)

(Printed in the e-text as a proposition.) A temporary definition (Dft) for ✱123–✱124: `N` is
`Nsucc`, the relation of an inductive cardinal to its successor in the same type.

**Status.** definition: a Dft, as in `Defs/Part3`. -/
theorem pm123_02 {α : Type*} :
    (Nsucc : Set (Set α) → Set (Set α) → Prop) =
      fun μ ν => μ ∈ NCinduct ∧ ν = (μ +ᶜ (one : Set (Set α)) : Set (Set α)) ∩ typ₀ μ := rfl

/-- ✱123·1. \(\vdash :\alpha \in \aleph _{0}.\equiv .(\exists R).R\in \text{Prog}.\alpha =\text{D}ʻR \quad[*37·1.(*123·01)]\) -/
theorem pm123_1 {α : Type*} {A : Set α} : A ∈ aleph0 ↔ ∃ R, R ∈ Prog ∧ A = dom R := Iff.rfl

/-- ✱123·101. \(\vdash :R\in \text{Prog}.\supset .\text{D}ʻR\in \aleph _{0} \quad[*123·1]\) -/
theorem pm123_101 {α : Type*} {R : α → α → Prop} : R ∈ Prog → dom R ∈ aleph0 :=
  fun h => ⟨R, h, rfl⟩

/-- ✱123·11. \(\vdash :R\in 1\rightarrow 1.\text{D}ʻR=\overleftarrow{R}_{*}ʻBʻR.\supset .\text{D}ʻR\in \aleph _{0} \quad[*123·101.*122·1]\) -/
theorem pm123_11 {α : Type*} {R : α → α → Prop} :
    R ∈ arrow one one ∧ Desc Beg R (fun b => dom R = rels (anc R) b) → dom R ∈ aleph0 :=
  fun h => pm123_101 h

/-- ✱123·12. \[\begin{align}\vdash :\alpha \in \aleph _{0}.\supset .(\exists R).\text{D}ʻR=\alpha .R\in 1\rightarrow 1.\text{ᗡ}ʻR&\subset \text{D}ʻR.\overrightarrow{B}ʻR\in 1\\ &[*123·1.*122·141·11]\end{align}\]

`B⃗'R ∈ 1`: `R` has exactly one beginning. The products bracket to the left. -/
theorem pm123_12 {α : Type*} {A : Set α} :
    A ∈ aleph0 → ∃ R : α → α → Prop,
      ((dom R = A ∧ R ∈ arrow one one) ∧ codom R ⊆ dom R) ∧ refs Beg R ∈ one := by
  rintro ⟨R, hR, rfl⟩
  refine ⟨R, ⟨⟨rfl, hR.1⟩, (pm122_141 hR).1⟩, ?_⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 hR
  exact ⟨f 0, Set.ext fun x => beg_seqRel hf⟩

/-- ✱123·13. \(\vdash :\alpha \in \aleph _{0}.\supset .\text{Nc}ʻ\alpha =\text{Nc}ʻ\alpha +_{c}1\)

The argument `Nc'α` of `+_c` is `N₀c'α` (✱110·03); the equation is in a type `γ` that nothing
else determines; the `1` is in the type of the other argument (encoding decision 10 of
`Defs/Part3`).

**Status.** proved (reading): normal adjustment (✱110·03): the argument `Nc'α` of `+_c` is read `N₀c'α`. -/
theorem pm123_13 {α γ : Type*} {A : Set α} :
    A ∈ aleph0 → nc γ A = (n₀c A +ᶜ (one : Set (Set α)) : Set (Set γ)) := by
  intro hA
  obtain ⟨f, -, rfl⟩ := mem_aleph0_iff.1 hA
  rw [one_eq_n₀c_singleton (f 0), n₀c_cardAdd_n₀c]
  exact nc_eq_nc_of_sm (sm_of_aleph0 hA (countable_infinite_clsSum hA (Set.countable_singleton _)))

/-- ✱123·14. \(\vdash :\alpha \in \aleph _{0}.\nu \in \text{NC induct}.\supset .\exists !\nu \cap \text{Cl}ʻ\alpha \quad[*122·35]\)

`ν ∩ Cl'α` puts `ν` (and `NC induct`) in the type of the classes of terms of `α`. -/
theorem pm123_14 {α : Type*} {A : Set α} {ν : Set (Set α)} :
    A ∈ aleph0 ∧ ν ∈ NCinduct → (ν ∩ cl A).Nonempty := by
  rintro ⟨hA, hν⟩
  obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hν
  obtain ⟨t, hts, htf, htk⟩ := (infinite_of_aleph0 hA).exists_subset_ncard_eq k
  exact ⟨t, ⟨htf, htk⟩, hts⟩

/-- ✱123·15. \(\vdash :\alpha \in \aleph _{0}.\supset .\alpha {\sim}\in \text{Cls induct} \quad[*122·37]\) -/
theorem pm123_15 {α : Type*} {A : Set α} : A ∈ aleph0 → A ∉ ClsInduct :=
  fun hA h => infinite_of_aleph0 hA (mem_ClsInduct.1 h)

/-- ✱123·16. \(\vdash :\alpha \in \aleph _{0}.\supset .\text{Cl}ʻ\alpha \subset \text{Cls induct}\cup \aleph _{0} \quad[*122·46]\) -/
theorem pm123_16 {α : Type*} {A : Set α} : A ∈ aleph0 → cl A ⊆ ClsInduct ∪ aleph0 := by
  intro hA B hB
  by_cases hfin : B.Finite
  · exact Or.inl (mem_ClsInduct.2 hfin)
  · exact Or.inr (mem_aleph0_iff_ci.2 ⟨(mem_aleph0_iff_ci.1 hA).1.mono hB, hfin⟩)

/-- ✱123·17. \(\vdash :\alpha \in \aleph _{0}.\beta \in \text{Cls induct}.\supset .\alpha -\beta \in \aleph _{0}\) -/
theorem pm123_17 {α : Type*} {A B : Set α} : A ∈ aleph0 ∧ B ∈ ClsInduct → A \ B ∈ aleph0 := by
  rintro ⟨hA, hB⟩
  obtain ⟨hc, hi⟩ := mem_aleph0_iff_ci.1 hA
  exact mem_aleph0_iff_ci.2 ⟨hc.mono (fun x hx => hx.1), hi.sdiff (mem_ClsInduct.1 hB)⟩

/-- ✱123·18. \(\vdash :\exists !\aleph _{0}(x).\supset .\text{Infin ax}(x) \quad[*122·36]\)

`ℵ₀(x)` is `ℵ₀ ∩ t't'x` (✱65·02), `clsT2 aleph0 x`. -/
theorem pm123_18 {α : Type*} {x : α} : (clsT2 aleph0 x).Nonempty → InfinAxAt x := by
  intro h
  rw [clsT2_eq] at h
  rw [infinAxAt_iff, infinAx_iff_infinite]
  exact aleph0_nonempty_iff.1 h

/-- ✱123·19. \(\vdash :R\in \text{Prog}.\exists !\alpha .\alpha \subset R_{\text{po}}ʻʻ\alpha .\supset .\alpha \in \aleph _{0} \quad[*122·45]\) -/
theorem pm123_19 {α : Type*} {R : α → α → Prop} {A : Set α} :
    (R ∈ Prog ∧ A.Nonempty) ∧ A ⊆ po R ʻʻ A → A ∈ aleph0 := by
  rintro ⟨⟨h, hne⟩, hA⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  obtain ⟨g, hg, -, hrange, -, -⟩ := pm122_44_core hf hA hne
  exact mem_aleph0_iff.2 ⟨g, hg, hrange.symm⟩

/-- ✱123·191. \[\begin{align}&\vdash :R\in 1\rightarrow 1.x\in \text{D}ʻR.{\sim}(xR_{\text{po}}x).&\overleftarrow{R}_{*}ʻx\subset \text{D}ʻR.\supset .\overleftarrow{R}_{*}ʻx\in \aleph _{0}\\ &[*122·52]\end{align}\] -/
theorem pm123_191 {α : Type*} {R : α → α → Prop} {x : α} :
    ((R ∈ arrow one one ∧ x ∈ dom R) ∧ ¬ po R x x) ∧ rels (anc R) x ⊆ dom R →
      rels (anc R) x ∈ aleph0 := by
  intro h
  refine ⟨_, pm122_52 h, ?_⟩
  show rels (anc R) x = dom (rels (anc R) x ◁ R)
  ext y
  exact ⟨fun hy => let ⟨z, hz⟩ := h.2 hy; ⟨z, hy, hz⟩, fun ⟨_, hy, _⟩ => hy⟩

/-- ✱123·192. \(\vdash :R\in 1\rightarrow 1.\text{ᗡ}ʻR\subset \text{D}ʻR.\supset .\overleftarrow{R}_{*}ʻʻ\overrightarrow{B}ʻR\subset \aleph _{0}\)

`R⃖_*` is the relation `Rbwd (anc R)` (✱32·02), so `R⃖_*''B⃗'R` is `Rbwd (anc R) ʻʻ refs Beg R`,
the class of the posterities of the beginnings of `R`. -/
theorem pm123_192 {α : Type*} {R : α → α → Prop} :
    R ∈ arrow one one ∧ codom R ⊆ dom R → Rbwd (anc R) ʻʻ refs Beg R ⊆ aleph0 := by
  rintro ⟨h11, hcd⟩ X ⟨x, hx, hX⟩
  have hX' : X = rels (anc R) x := hX
  rw [hX']
  refine pm123_191 ⟨⟨⟨h11, hx.1⟩, fun hpo => ?_⟩, fun y hy => ?_⟩
  · rw [po_iff_transGen] at hpo
    obtain ⟨c, -, hcx⟩ := Relation.TransGen.tail'_iff.1 hpo
    exact hx.2 ⟨c, hcx⟩
  · obtain ⟨z, hz | hz⟩ := fld_of_anc_right (show anc R x y from hy)
    · exact ⟨z, hz⟩
    · exact hcd ⟨z, hz⟩

/-- ✱123·2. \(\vdash :\mu N\nu .\equiv .\mu \in \text{NC induct}.\nu =(\mu +_{c}1)\cap t_{0}ʻ\mu \quad[(*123·02)]\) -/
theorem pm123_2 {α : Type*} {μ ν : Set (Set α)} :
    Nsucc μ ν ↔ μ ∈ NCinduct ∧ ν = (μ +ᶜ (one : Set (Set α)) : Set (Set α)) ∩ typ₀ μ := Iff.rfl

/-- ✱123·21. \(\vdash .N\in \text{Cls}\rightarrow 1.\text{D}ʻN=\text{NC induct}.\text{ᗡ}ʻN=\text{NC induct}-\iota ʻ0.BʻN=0\)

`N` is taken at an arbitrary type of the cardinals; the proposition holds in every type
(in a finite type `Λ` is an inductive cardinal other than `0`, and `Λ = μ +_c 1` for the
greatest existent `μ`). -/
theorem pm123_21 {α : Type*} :
    (((Nsucc : Set (Set α) → Set (Set α) → Prop) ∈ arrow Cls one ∧
        dom (Nsucc : Set (Set α) → Set (Set α) → Prop) = NCinduct) ∧
      codom (Nsucc : Set (Set α) → Set (Set α) → Prop) = NCinduct \ ι zero) ∧
      Desc Beg (Nsucc : Set (Set α) → Set (Set α) → Prop) (fun b => b = zero) := by
  have hfun : (Nsucc : Set (Set α) → Set (Set α) → Prop) ∈ arrow Cls one :=
    mem_arrow_Cls_one.2 fun μ ν ν' ⟨h1, h2⟩ => (nsucc_iff.1 h1).2.trans (nsucc_iff.1 h2).2.symm
  have hdom : dom (Nsucc : Set (Set α) → Set (Set α) → Prop) = NCinduct := by
    ext μ
    exact ⟨fun ⟨_, h⟩ => (nsucc_iff.1 h).1, fun h => ⟨_, nsucc_iff.2 ⟨h, rfl⟩⟩⟩
  have hcod : codom (Nsucc : Set (Set α) → Set (Set α) → Prop) = NCinduct \ ι zero := by
    rw [nsucc_eq_seqRel, codom_seqRel, NCinduct_eq_range, zero_eq_cardN]
    ext μ
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨⟨k + 1, rfl⟩, fun h => ?_⟩
      have h' : cardN α (k + 1) = cardN α 0 := h
      have h0 : (∅ : Set α) ∈ cardN α 0 := ⟨Set.finite_empty, Set.ncard_empty α⟩
      rw [← h'] at h0
      exact absurd h0.2 (by rw [Set.ncard_empty]; omega)
    · rintro ⟨⟨k, rfl⟩, hk⟩
      cases k with
      | zero => exact absurd rfl hk
      | succ k => exact ⟨k, rfl⟩
  have hbeg : ∀ b, Beg b (Nsucc : Set (Set α) → Set (Set α) → Prop) ↔ b = zero := by
    intro b
    rw [Beg_apply, hdom, hcod]
    constructor
    · rintro ⟨hb, hno⟩
      by_contra hne
      exact hno ⟨hb, hne⟩
    · rintro rfl
      exact ⟨zero_mem_NCinduct, fun h => h.2 rfl⟩
  exact ⟨⟨⟨hfun, hdom⟩, hcod⟩, desc_iff_of_unique hbeg _ |>.2 rfl⟩

/-- ✱123·22. \(\vdash .\breve{N} =(+_{c}1)\upharpoonright \text{NC induct} \quad[*123·2]\)

`(+_c 1)` is the relation `plusC1` (✱120·01). -/
theorem pm123_22 {α : Type*} :
    (Nsucc : Set (Set α) → Set (Set α) → Prop)˘ = plusC1 ↾ NCinduct := by
  funext ν μ
  apply propext
  show Nsucc μ ν ↔ plusC1 ν μ ∧ μ ∈ NCinduct
  rw [nsucc_iff, plusC1_iff]
  exact and_comm

/-- ✱123·23. \(\vdash .\overleftarrow{N}_{*}ʻ0=\text{NC induct}=\text{D}ʻN\) -/
theorem pm123_23 {α : Type*} :
    rels (anc (Nsucc : Set (Set α) → Set (Set α) → Prop)) zero = NCinduct ∧
      NCinduct = dom (Nsucc : Set (Set α) → Set (Set α) → Prop) := by
  refine ⟨?_, pm123_21.1.1.2.symm⟩
  rw [nsucc_eq_seqRel, NCinduct_eq_range, zero_eq_cardN]
  ext μ
  constructor
  · intro h
    have := fld_of_anc_right (show anc (SeqRel (cardN α)) (cardN α 0) μ from h)
    rwa [fld_seqRel] at this
  · rintro ⟨k, rfl⟩
    exact anc_iff_reflTransGen.2 ⟨⟨_, Or.inl (seqRel_apply _ 0)⟩,
      rtg_seqRel_of_le _ (Nat.zero_le k)⟩

/-- ✱123·24. \(\vdash :\text{Infin ax}(x).\supset .N\unicode{x0294f}t^{3}ʻx\in 1\rightarrow 1\)

`N ⥏ t³'x` is `Nsucc ⥏ typ3 x` (the cardinals of classes of terms of the type of `x`). -/
theorem pm123_24 {X : Type*} {x : X} : InfinAxAt x → Nsucc ⥏ typ3 x ∈ arrow one one := by
  intro hx
  have : Infinite X := infinAx_iff_infinite.1 ((infinAxAt_iff x).1 hx)
  rw [typ3_eq_univ, fres_univ, nsucc_eq_seqRel]
  exact seqRel_oneone cardN_injective

/-- ✱123·25. \(\vdash :\text{Infin ax}(x).\supset .N\unicode{x0294f}t^{3}ʻx\in \text{Prog} \quad[*123·21·23·24.*122·1]\) -/
theorem pm123_25 {X : Type*} {x : X} : InfinAxAt x → Nsucc ⥏ typ3 x ∈ Prog := by
  intro hx
  have : Infinite X := infinAx_iff_infinite.1 ((infinAxAt_iff x).1 hx)
  rw [typ3_eq_univ, fres_univ, nsucc_eq_seqRel]
  exact seqRel_mem_prog cardN_injective

/-- ✱123·26. \(\vdash :\text{Infin ax}(x).\supset .\text{NC induct}\cap t^{3}ʻx\in \aleph _{0} \quad[*123·25·21·101]\) -/
theorem pm123_26 {X : Type*} {x : X} : InfinAxAt x → NCinduct ∩ typ3 x ∈ aleph0 := by
  intro hx
  have : Infinite X := infinAx_iff_infinite.1 ((infinAxAt_iff x).1 hx)
  rw [typ3_eq_univ, Set.inter_univ]
  exact NCinduct_mem_aleph0

/-- ✱123·27. \(\vdash :\exists !\aleph _{0}(x).\supset .\text{NC induct}\cap t^{3}ʻx\in \aleph _{0} \quad[*123·26·18]\) -/
theorem pm123_27 {X : Type*} {x : X} :
    (clsT2 (aleph0 : Set (Set X)) x).Nonempty → NCinduct ∩ typ3 x ∈ aleph0 :=
  fun h => pm123_26 (pm123_18 h)

/-- ✱123·3. \[\begin{align}\vdash :R\in \text{Prog}.&S=\hat{x} \hat{\nu} \{\nu \in \text{NC induct}.x=(\nu +_{c}1)_{R}\}.\supset .\\ &S\in 1\rightarrow 1.\text{D}ʻS=\text{D}ʻR.\text{ᗡ}ʻS=\text{NC induct}\end{align}\]

`S : α → Set (Set X) → Prop`; `x = (ν +_c 1)_R` is `Desc (nuP (ν +_c 1)) R (fun y => x = y)`,
with `ν +_c 1` (and its `1`) in the type of `ν`, as in the relation `+_c 1` of ✱120·01. The
type `X` of `ν` is tied by `ᗡ'S = NC induct` to that occurrence of `NC induct`.

**Status.** proved (reading): convention Infin T (Prefatory Statement, VI): `NC induct`, whose type `X` is tied by significance to the relata of `S`, is taken in a type with all inductive cardinals (`InfinAx X`); otherwise `ᗡ'S = NC induct` fails. -/
theorem pm123_3 {α X : Type*} (hX : InfinAx X) {R : α → α → Prop} {S : α → Set (Set X) → Prop} :
    R ∈ Prog ∧ S = (fun x ν => ν ∈ NCinduct ∧
        Desc (nuP (ν +ᶜ (one : Set (Set X)) : Set (Set X))) R (fun y => x = y)) →
      (S ∈ arrow one one ∧ dom S = dom R) ∧ codom S = NCinduct := by
  rintro ⟨h, rfl⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  have : Infinite X := infinAx_iff_infinite.1 hX
  have hS : ∀ x (ν : Set (Set X)), (ν ∈ NCinduct ∧
      Desc (nuP (ν +ᶜ (one : Set (Set X)) : Set (Set X))) (SeqRel f) (fun y => x = y)) ↔
      ∃ k, ν = cardN X k ∧ x = f k := by
    intro x ν
    rw [mem_NCinduct_iff_cardN]
    constructor
    · rintro ⟨⟨k, rfl⟩, hd⟩
      rw [cardN_add_one, desc_nuP_seqRel hf (cardN_nonempty_of_infinite _)] at hd
      exact ⟨k, rfl, hd⟩
    · rintro ⟨k, rfl, rfl⟩
      refine ⟨⟨k, rfl⟩, ?_⟩
      rw [cardN_add_one, desc_nuP_seqRel hf (cardN_nonempty_of_infinite _)]
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y ν ⟨h1, h2⟩
    obtain ⟨k, rfl, rfl⟩ := (hS _ _).1 h1
    obtain ⟨k', hk', rfl⟩ := (hS _ _).1 h2
    rw [cardN_injective hk']
  · rintro x ν ν' ⟨h1, h2⟩
    obtain ⟨k, rfl, rfl⟩ := (hS _ _).1 h1
    obtain ⟨k', rfl, hk'⟩ := (hS _ _).1 h2
    rw [hf hk']
  · rw [dom_seqRel]
    ext x
    constructor
    · rintro ⟨ν, hν⟩
      obtain ⟨k, -, rfl⟩ := (hS _ _).1 hν
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨cardN X k, (hS _ _).2 ⟨k, rfl, rfl⟩⟩
  · ext ν
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨k, rfl, -⟩ := (hS _ _).1 hx
      exact cardN_mem_NCinduct k
    · intro hν
      obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hν
      exact ⟨f k, (hS _ _).2 ⟨k, rfl, rfl⟩⟩

/-- ✱123·31. \(\vdash :\alpha \in \aleph _{0}.\supset .\alpha \text{ sm }\text{NC induct} \quad[*123·3]\)

**Status.** proved (reading): convention Infin T (Prefatory Statement, VI): `α ∈ ℵ₀` implies that some type has all inductive cardinals, so `NC induct` is taken at a type `X` with `InfinAx X`. -/
theorem pm123_31 {α X : Type*} (hX : InfinAx X) {A : Set α} :
    A ∈ aleph0 → sm A (NCinduct : Set (Set (Set X))) := by
  intro hA
  have : Infinite X := infinAx_iff_infinite.1 hX
  exact sm_of_aleph0 hA NCinduct_mem_aleph0

/-- ✱123·311. \(\vdash :\alpha ,\beta \in \aleph _{0}.\supset .\alpha \text{ sm }\beta \quad[*123·31.*73·31·32]\)

`α, β ∈ ℵ₀` with `α`, `β` of possibly different types (PM's note) is the conjunction. -/
theorem pm123_311 {α β : Type*} {A : Set α} {B : Set β} : A ∈ aleph0 ∧ B ∈ aleph0 → sm A B :=
  fun ⟨hA, hB⟩ => sm_of_aleph0 hA hB

/-- ✱123·312. \[\begin{align}\vdash :R\in &\text{Prog}.S\in 1\rightarrow 1.\text{ᗡ}ʻS=\text{D}ʻR.\supset .\\ &S\mid R\mid \breve{S} \in 1\rightarrow 1.\text{D}ʻS=\text{D}ʻ(S\mid R\mid \breve{S} ).SʻBʻR=Bʻ(S\mid R\mid \breve{S} )\end{align}\]

`S : β → α → Prop`; `S | R | S̆` is `S ⨾ R ⨾ S˘` (`(S ⨾ R) ⨾ S˘`). In `S'B'R = B'(S|R|S̆)` the
double description `S'B'R` (✱30·02) occurs first and has the larger scope. -/
theorem pm123_312 {α β : Type*} {R : α → α → Prop} {S : β → α → Prop} :
    (R ∈ Prog ∧ S ∈ arrow one one) ∧ codom S = dom R →
      ((S ⨾ R ⨾ S˘ ∈ arrow one one ∧ dom S = dom (S ⨾ R ⨾ S˘)) ∧
        Desc2 S Beg R (fun u => Desc Beg (S ⨾ R ⨾ S˘) (fun v => u = v))) := by
  rintro ⟨⟨h, h11⟩, hcd⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [dom_seqRel] at hcd
  obtain ⟨g, hg, hconj, hdom, h0⟩ := conj_seqRel hf h11 hcd
  rw [hconj, dom_seqRel, hdom, desc2_iff, desc_beg_seqRel hf]
  refine ⟨⟨seqRel_oneone hg, rfl⟩, (desc_iff_of_unique h0 _).2 ?_⟩
  exact (desc_beg_seqRel hg _).2 rfl

/-- ✱123·313. \(\vdash :R\in \text{Prog}.S\in 1\rightarrow 1.\text{ᗡ}ʻS=\text{D}ʻR.P= S\mid R\mid \breve{S} .\supset .\text{D}ʻP=\overleftarrow{P}_{*}ʻBʻP\) -/
theorem pm123_313 {α β : Type*} {R : α → α → Prop} {S : β → α → Prop} {P : β → β → Prop} :
    ((R ∈ Prog ∧ S ∈ arrow one one) ∧ codom S = dom R) ∧ P = S ⨾ R ⨾ S˘ →
      Desc Beg P (fun b => dom P = rels (anc P) b) := by
  rintro ⟨⟨⟨h, h11⟩, hcd⟩, rfl⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [dom_seqRel] at hcd
  obtain ⟨g, hg, hconj, -, -⟩ := conj_seqRel hf h11 hcd
  rw [hconj]
  exact (seqRel_mem_prog hg).2

/-- ✱123·32. \[\begin{align}&\vdash :R\in \text{Prog}.S\in 1\rightarrow 1.\text{ᗡ}ʻS=\text{D}ʻR.\supset .\\ &S\mid R\mid \breve{S} \in \text{Prog}.\text{D}ʻS=\text{D}ʻS\mid R\mid \breve{S} .SʻBʻR=Bʻ(S\mid R\mid \breve{S} ) \quad[*123·312·313]\end{align}\]

`D'S = D'S|R|S̆` is `dom S = dom (S ⨾ R ⨾ S˘)` (`D'` applies to the whole relative product). -/
theorem pm123_32 {α β : Type*} {R : α → α → Prop} {S : β → α → Prop} :
    (R ∈ Prog ∧ S ∈ arrow one one) ∧ codom S = dom R →
      ((S ⨾ R ⨾ S˘ ∈ Prog ∧ dom S = dom (S ⨾ R ⨾ S˘)) ∧
        Desc2 S Beg R (fun u => Desc Beg (S ⨾ R ⨾ S˘) (fun v => u = v))) := by
  intro h
  obtain ⟨⟨h1, h2⟩, h3⟩ := pm123_312 h
  exact ⟨⟨⟨h1, pm123_313 ⟨h, rfl⟩⟩, h2⟩, h3⟩

/-- ✱123·321. \(\vdash :\alpha \in \aleph _{0}.\alpha \text{ sm }\beta .\supset .\beta \in \aleph _{0} \quad[*123·32]\) -/
theorem pm123_321 {α β : Type*} {A : Set α} {B : Set β} : A ∈ aleph0 ∧ sm A B → B ∈ aleph0 :=
  fun ⟨hA, h⟩ => aleph0_of_sm hA h

/-- ✱123·322. \(\vdash :\alpha \in \aleph _{0}.\supset .\aleph _{0}=\text{Nc}ʻ\alpha\)

The type `γ` of the equation is free (an equational occurrence of `Nc'α`). -/
theorem pm123_322 {α γ : Type*} {A : Set α} : A ∈ aleph0 → (aleph0 : Set (Set γ)) = nc γ A :=
  aleph0_eq_nc

/-- ✱123·323. \(\vdash :R\in \text{Prog}.\supset .\aleph _{0}=\text{Nc}ʻ\text{D}ʻR \quad[*123·322]\) -/
theorem pm123_323 {α γ : Type*} {R : α → α → Prop} :
    R ∈ Prog → (aleph0 : Set (Set γ)) = nc γ (dom R) :=
  fun h => aleph0_eq_nc (pm123_101 h)

/-- ✱123·33. \(\vdash \colon\ldotp \text{Infin ax}(x).\supset :\alpha \in \aleph _{0}.\equiv .\alpha \text{ sm }(\text{NC induct}\cap t^{3}ʻx) \quad[*123·26·321·31]\)

`NC induct ∩ t³'x` has its type indicated expressly (the cardinals of classes of terms of the
type of `x`), so Infin T does not apply; `α` is of any type. -/
theorem pm123_33 {α X : Type*} {x : X} {A : Set α} :
    InfinAxAt x → (A ∈ aleph0 ↔ sm A (NCinduct ∩ typ3 x)) := by
  intro hx
  have : Infinite X := infinAx_iff_infinite.1 ((infinAxAt_iff x).1 hx)
  rw [typ3_eq_univ, Set.inter_univ]
  exact ⟨fun hA => sm_of_aleph0 hA NCinduct_mem_aleph0,
    fun h => aleph0_of_sm NCinduct_mem_aleph0 (sm_symm h)⟩

/-- ✱123·34. \(\vdash :\text{Infin ax}(x).\supset .\aleph _{0}=\text{Nc}ʻ(\text{NC induct}\cap t^{3}ʻx) \quad[*123·33]\) -/
theorem pm123_34 {X γ : Type*} {x : X} :
    InfinAxAt x → (aleph0 : Set (Set γ)) = nc γ (NCinduct ∩ typ3 x) :=
  fun hx => aleph0_eq_nc (pm123_26 hx)

/-- ✱123·35. \(\vdash :\exists !\aleph _{0}(x).\supset .\aleph _{0}(x)=\text{Nc}ʻ(\text{NC induct}\cap t^{3}ʻx) \quad[*123·34·18]\)

`ℵ₀(x)` is `clsT2 aleph0 x`, and the equation is in its type. -/
theorem pm123_35 {X : Type*} {x : X} :
    (clsT2 (aleph0 : Set (Set X)) x).Nonempty →
      clsT2 (aleph0 : Set (Set X)) x = nc X (NCinduct ∩ typ3 x) := by
  intro h
  rw [clsT2_eq]
  exact pm123_34 (pm123_18 h)

/-- ✱123·36. \(\vdash .\aleph _{0}\in \text{NC} \quad[*123·35.*102·74]\)

`NC` is `NC β` with the type `β` of the converse domain of `Nc` explicit (`Defs/Part3`,
decision 3). PM's demonstration (✱123·35, ✱102·74) takes it as the type of
`NC induct ∩ t³'x`, i.e. classes of classes of the type of the members of the members of
`ℵ₀`: `Set (Set α)`.

**Status.** proved (reading): the converse-domain type of `NC`, which PM leaves undetermined, is the one of PM's demonstration (classes of classes of `α`-things); in some types the statement fails (e.g. in a finite one when `ℵ₀ ≠ Λ`). -/
theorem pm123_36 {α : Type*} : (aleph0 : Set (Set α)) ∈ NC (Set (Set α)) := by
  by_cases h : (aleph0 : Set (Set α)).Nonempty
  · have : Infinite α := aleph0_nonempty_iff.1 h
    exact ⟨NCinduct, aleph0_eq_nc NCinduct_mem_aleph0⟩
  · refine ⟨Set.univ, ?_⟩
    rw [Set.not_nonempty_iff_eq_empty.1 h]
    ext B
    simp only [Set.mem_empty_iff_false, false_iff]
    intro hB
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (mem_nc.1 hB)
    apply Function.cantor_injective (fun s : Set α => ((e.symm ⟨{s}, trivial⟩ : B) : α))
    intro s t hst
    have h1 := e.symm.injective (Subtype.ext hst)
    exact Set.singleton_injective (congrArg Subtype.val h1)

/-- ✱123·361. \(\vdash :\exists !\aleph _{0}.\supset .\aleph _{0}{\sim}\in \text{NC induct} \quad[*123·15·322.*120·211]\) -/
theorem pm123_361 {α : Type*} :
    (aleph0 : Set (Set α)).Nonempty → (aleph0 : Set (Set α)) ∉ NCinduct :=
  aleph0_not_mem_NCinduct

/-- ✱123·37. \(\vdash :\text{Infin ax}(x).\supset .\exists !\aleph _{0}(t^{2}ʻx).\aleph _{0}(t^{2}x)\in \text{N}_{0}\text{C}\)

`ℵ₀(t²'x)` is `clsT2 aleph0 (typ2 x)`: classes of classes of classes of terms of the type of
`x`. -/
theorem pm123_37 {X : Type*} {x : X} :
    InfinAxAt x → (clsT2 aleph0 (typ2 x)).Nonempty ∧ clsT2 aleph0 (typ2 x) ∈ N₀C := by
  intro hx
  have : Infinite X := infinAx_iff_infinite.1 ((infinAxAt_iff x).1 hx)
  have : Infinite (Set X) := infinite_set_of_infinite
  have : Infinite (Set (Set X)) := infinite_set_of_infinite
  rw [clsT2_eq]
  obtain ⟨A, hA⟩ := exists_mem_aleph0 (α := Set (Set X))
  exact ⟨⟨A, hA⟩, A, aleph0_eq_n₀c hA⟩

/-- ✱123·39. \(\vdash .(\aleph _{0})_{\eta }=(\aleph _{0}+_{c}1)_{\eta }\)

`σ_η` is `σ ∩ t'η` (✱65·01, `clsT σ η`). The `ℵ₀` subjected to `+_c` is an arithmetical
component in a type `W`; the `1` is in the type of the other argument.

**Status.** proved (reading): convention IIT (Prefatory Statement, II (iii), IV): the actual type `W` of the `ℵ₀` subjected to `+_c` is taken adequate, i.e. with `∃!ℵ₀` (PM's test (iii), `∃!N₀c't₁'ℵ₀`, is met in every type, and in a finite `W` the right side is `Λ`; see `pm123_4_aux_IIT`). -/
theorem pm123_39 {G W : Type*} {η : Set G} :
    (aleph0 : Set (Set W)).Nonempty →
      clsT (aleph0 : Set (Set G)) η =
        clsT ((aleph0 : Set (Set W)) +ᶜ (one : Set (Set W)) : Set (Set G)) η := by
  intro h
  obtain ⟨A, hA⟩ := h
  rw [clsT_eq, clsT_eq, aleph0_eq_n₀c hA, aleph0_eq_nc (γ := G) hA]
  exact pm123_13 hA

/-- ✱123·4. \(\vdash .\aleph _{0}=\aleph _{0}+_{c}1 \quad[*123·39]\)

**Status.** proved (reading): convention IIT, as in ✱123·39: the `ℵ₀` subjected to `+_c` is taken in a type `W` with `∃!ℵ₀`; without it the proposition fails (`pm123_4_aux_IIT`). -/
theorem pm123_4 {γ W : Type*} :
    (aleph0 : Set (Set W)).Nonempty →
      (aleph0 : Set (Set γ)) = ((aleph0 : Set (Set W)) +ᶜ (one : Set (Set W)) : Set (Set γ)) := by
  intro h
  obtain ⟨A, hA⟩ := h
  rw [aleph0_eq_n₀c hA, aleph0_eq_nc (γ := γ) hA]
  exact pm123_13 hA

/-- Without the IIT hypothesis ✱123·4 fails: with the inner `ℵ₀` in a finite type it is `Λ`, and
`ℵ₀ +_c 1 = Λ`, while `ℵ₀` of `ℕ` is not `Λ`. -/
theorem pm123_4_aux_IIT :
    (aleph0 : Set (Set ℕ)) ≠ ((aleph0 : Set (Set Unit)) +ᶜ (one : Set (Set Unit)) : Set (Set ℕ)) := by
  have h0 : ¬ (aleph0 : Set (Set Unit)).Nonempty := fun h =>
    not_finite_iff_infinite.2 (aleph0_nonempty_iff.1 h) inferInstance
  rw [cardAdd_eq_empty_of_empty_left h0]
  exact (aleph0_nonempty_iff.2 inferInstance).ne_empty

/-- ✱123·401. \(\vdash :\exists !\aleph _{0}.\supset .\aleph _{0}=\aleph _{0}-_{c}1\)

The hypothesis `∃!ℵ₀` is in a type `α`, and the `ℵ₀` subjected to `−_c` is taken in it (as in
the worked example ✱123·43 of `Defs/Part3`); the `1` is in the same type, and the equation
in a free type `γ`. -/
theorem pm123_401 {α γ : Type*} :
    (aleph0 : Set (Set α)).Nonempty →
      (aleph0 : Set (Set γ)) = ((aleph0 : Set (Set α)) -ᶜ (one : Set (Set α)) : Set (Set γ)) := by
  intro h
  have : Infinite α := aleph0_nonempty_iff.1 h
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  rw [one_eq_n₀c_singleton a, cardSub_aleph0 h (Set.finite_singleton a)]

/-- ✱123·41. \(\vdash :\nu \in \text{NC induct}.\supset .\aleph _{0}=\aleph _{0}+_{c}\nu \quad[*123·4.*120·11]\)

**Status.** proved (reading): conventions IIT and Infin T (Prefatory Statement, IV, VI): the `ℵ₀` subjected to `+_c` is in a type `W` with `∃!ℵ₀` (as in ✱123·4); the hypothesis then implies a type with all inductive cardinals, and `NC induct` (the type `X` of `ν`) is taken in such a type, `InfinAx X` (for `ν = Λ` in a finite type the proposition fails). -/
theorem pm123_41 {X W γ : Type*} (hX : InfinAx X) {ν : Set (Set X)} :
    (aleph0 : Set (Set W)).Nonempty → ν ∈ NCinduct →
      (aleph0 : Set (Set γ)) = ((aleph0 : Set (Set W)) +ᶜ ν : Set (Set γ)) := by
  intro h hν
  have : Infinite X := infinAx_iff_infinite.1 hX
  obtain ⟨A, hA⟩ := h
  obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hν
  obtain ⟨B, hB⟩ := cardN_nonempty_of_infinite (β := X) k
  rw [cardN_eq_n₀c hB, aleph0_eq_n₀c hA, n₀c_cardAdd_n₀c]
  exact aleph0_eq_nc (countable_infinite_clsSum hA hB.1.countable)

/-- ✱123·411. \(\vdash :\nu \in \text{NC induct}.\supset .\aleph _{0}=\aleph _{0}-_{c}\nu \quad[*123·401.*120·11]\)

**Status.** proved (reading): conventions IIT and Infin T, as in ✱123·41. -/
theorem pm123_411 {X W γ : Type*} (hX : InfinAx X) {ν : Set (Set X)} :
    (aleph0 : Set (Set W)).Nonempty → ν ∈ NCinduct →
      (aleph0 : Set (Set γ)) = ((aleph0 : Set (Set W)) -ᶜ ν : Set (Set γ)) := by
  intro h hν
  have : Infinite X := infinAx_iff_infinite.1 hX
  obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hν
  obtain ⟨B, hB⟩ := cardN_nonempty_of_infinite (β := X) k
  rw [cardN_eq_n₀c hB, cardSub_aleph0 h hB.1]

/-- ✱123·42. \(\vdash :P\in \text{Prog}.Q=P^{2}.\supset .\overleftarrow{Q}_{*}ʻ1_{P},\overleftarrow{Q}_{*}ʻ2_{P}\in \aleph _{0}.\overleftarrow{Q}_{*}ʻ1_{P}\cap \overleftarrow{Q}_{*}ʻ2_{P}=\Lambda\)

`1_P`, `2_P` are `Desc (nuP 1) P`, `Desc (nuP 2) P`, the constants `1`, `2` in types `W₁`,
`W₂` that nothing determines. `Q⃖_*'1_P, Q⃖_*'2_P ∈ ℵ₀` is the conjunction of the two
memberships (✱20·04), each with its own description.

**Status.** proved (reading): the constants `1`, `2` are taken in types in which they exist (`[Nonempty W₁]`, `∃!2` in `W₂`; stable truth-value, Prefatory Statement, I): otherwise `1_P`, `2_P` do not exist. -/
theorem pm123_42 {α W₁ W₂ : Type*} [Nonempty W₁] (h2 : (two : Set (Set W₂)).Nonempty)
    {P Q : α → α → Prop} :
    P ∈ Prog ∧ Q = rsq P →
      (Desc (nuP (one : Set (Set W₁))) P (fun a => rels (anc Q) a ∈ aleph0) ∧
        Desc (nuP (two : Set (Set W₂))) P (fun c => rels (anc Q) c ∈ aleph0)) ∧
      Desc (nuP (one : Set (Set W₁))) P
        (fun a => Desc (nuP (two : Set (Set W₂))) P (fun c => rels (anc Q) a ∩ rels (anc Q) c = Λ)) := by
  rintro ⟨h, rfl⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  have hsq : rsq (SeqRel f) = SeqStep f 2 := by
    show SeqStep f 1 ⨾ SeqRel f = SeqStep f 2
    rw [seqStep_comp hf]
  rw [two_eq_cardN] at h2 ⊢
  rw [hsq]
  simp only [desc_nuP_one_seqRel hf, desc_nuP_seqRel (k := 1) hf h2]
  have hpost : ∀ i, rels (anc (SeqStep f 2)) (f i) = Set.range (fun q => f (i + q * 2)) := by
    intro i
    ext y
    show anc (SeqStep f 2) (f i) y ↔ _
    rw [anc_seqStep hf]
    exact ⟨fun ⟨q, hq⟩ => ⟨q, hq.symm⟩, fun ⟨q, hq⟩ => ⟨q, hq.symm⟩⟩
  have hinj : ∀ i, Function.Injective (fun q => f (i + q * 2)) := fun i p q hpq => by
    have := hf hpq
    omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hpost]; exact mem_aleph0_iff.2 ⟨_, hinj 0, rfl⟩
  · rw [hpost]; exact mem_aleph0_iff.2 ⟨_, hinj 1, rfl⟩
  · rw [hpost, hpost, Null_eq_empty]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨p, rfl⟩, ⟨q, hq⟩⟩
    have := hf hq
    omega

/-- ✱123·421. \(\vdash .\aleph _{0}=\aleph _{0}+_{c}\aleph _{0}=2\times _{c}\aleph _{0}\)

The chain is the conjunction of its links, in one type `γ`; each `ℵ₀` subjected to an
arithmetical operation, and the `2`, has its own type (`W₁`, …, `W₄`).

**Status.** proved (reading): convention IIT (Prefatory Statement, II, IV): the arithmetical components are taken in adequate types (`∃!2` in `W₃`; `∃!ℵ₀` for the `ℵ₀`s, as in ✱123·4). -/
theorem pm123_421 {γ W₁ W₂ W₃ W₄ : Type*} (h1 : (aleph0 : Set (Set W₁)).Nonempty)
    (h2 : (aleph0 : Set (Set W₂)).Nonempty) (h3 : (two : Set (Set W₃)).Nonempty)
    (h4 : (aleph0 : Set (Set W₄)).Nonempty) :
    (aleph0 : Set (Set γ)) = ((aleph0 : Set (Set W₁)) +ᶜ (aleph0 : Set (Set W₂)) : Set (Set γ)) ∧
      ((aleph0 : Set (Set W₁)) +ᶜ (aleph0 : Set (Set W₂)) : Set (Set γ)) =
        ((two : Set (Set W₃)) ×ᶜ (aleph0 : Set (Set W₄)) : Set (Set γ)) := by
  obtain ⟨A₁, hA₁⟩ := h1
  obtain ⟨A₂, hA₂⟩ := h2
  obtain ⟨A₄, hA₄⟩ := h4
  rw [two_eq_cardN] at h3
  obtain ⟨T, hT⟩ := h3
  have hsum : ((aleph0 : Set (Set W₁)) +ᶜ (aleph0 : Set (Set W₂)) : Set (Set γ)) = aleph0 := by
    rw [aleph0_eq_n₀c hA₁, aleph0_eq_n₀c hA₂, n₀c_cardAdd_n₀c]
    exact (aleph0_eq_nc (countable_infinite_clsSum hA₁ (mem_aleph0_iff_ci.1 hA₂).1)).symm
  refine ⟨hsum.symm, ?_⟩
  rw [hsum, two_eq_cardN, cardN_eq_n₀c hT, aleph0_eq_n₀c hA₄, n₀c_cardMul_n₀c]
  refine aleph0_eq_nc (countable_infinite_clsTimes hA₄ hT.1.countable ?_)
  exact Set.nonempty_of_ncard_ne_zero (by rw [hT.2]; omega)

/-- ✱123·422. \(\vdash :\nu \in \text{NC induct}-\iota ʻ0.\supset .\nu \times _{c}\aleph _{0}=\aleph _{0}\)

**Status.** proved (reading): conventions IIT and Infin T, as in ✱123·41 (`∃!ℵ₀` for the `ℵ₀` in `W`, `InfinAx X` for the type of `ν`). -/
theorem pm123_422 {X W γ : Type*} (hX : InfinAx X) {ν : Set (Set X)} :
    (aleph0 : Set (Set W)).Nonempty → ν ∈ NCinduct \ ι zero →
      (ν ×ᶜ (aleph0 : Set (Set W)) : Set (Set γ)) = aleph0 := by
  intro h hν
  have : Infinite X := infinAx_iff_infinite.1 hX
  obtain ⟨A, hA⟩ := h
  obtain ⟨k, rfl⟩ := mem_NCinduct_ne_zero.1 hν
  obtain ⟨B, hB⟩ := cardN_nonempty_of_infinite (β := X) (k + 1)
  rw [cardN_eq_n₀c hB, aleph0_eq_n₀c hA, n₀c_cardMul_n₀c]
  refine (aleph0_eq_nc (countable_infinite_clsTimes hA hB.1.countable ?_)).symm
  exact Set.nonempty_of_ncard_ne_zero (by rw [hB.2]; omega)

/-- ✱123·43. \(\vdash \colon\ldotp \exists !\aleph _{0}.\supset :\nu \in \text{NC induct}.\supset _{\nu }.\aleph _{0}>\nu\)

The worked example of convention Infin T in `Defs/Part3`: `ℵ₀` is in a type `α`, with the
hypothesis `∃!ℵ₀` as printed; `NC induct` (the type of the apparent variable `ν`) is taken
at a type `X` with `InfinAx X`.

**Status.** proved (reading): convention Infin T (Prefatory Statement, VI); in a finite `X`, `Λ` is an inductive cardinal and `ℵ₀ > Λ` is false. -/
theorem pm123_43 {α X : Type*} :
    InfinAx X → (aleph0 : Set (Set α)).Nonempty →
      ∀ ν : Set (Set X), ν ∈ NCinduct → (aleph0 : Set (Set α)) >ᶜ ν := by
  intro hX h ν hν
  have : Infinite X := infinAx_iff_infinite.1 hX
  obtain ⟨B, hB⟩ := h
  obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hν
  rw [aleph0_eq_n₀c hB]
  exact aleph0_cardGt_cardN hB (cardN_nonempty_of_infinite k)

/-- ✱123·44. \(\vdash \colon\ldotp \exists !\aleph _{0}.\supset :\nu \in \text{NC induct} \cup \iota ʻ\aleph _{0}.\equiv .\aleph _{0}\geq \nu \)

`ν` is a real variable of a type `X`; the `ℵ₀` of `ι'ℵ₀` is in that type, the other `ℵ₀`s in
the type `α` of the hypothesis (as in ✱123·43).

**Status.** proved (reading): convention Infin T (Prefatory Statement, VI): `NC induct`, in the type `X` of `ν`, is taken with `InfinAx X` (in a finite `X`, `Λ ∈ NC induct` but not `ℵ₀ ≥ Λ`). -/
theorem pm123_44 {α X : Type*} (hX : InfinAx X) {ν : Set (Set X)} :
    (aleph0 : Set (Set α)).Nonempty →
      (ν ∈ NCinduct ∪ ι (aleph0 : Set (Set X)) ↔ (aleph0 : Set (Set α)) ≥ᶜ ν) := by
  intro h
  have : Infinite X := infinAx_iff_infinite.1 hX
  obtain ⟨B, hB⟩ := h
  have hBi : Infinite B := Set.infinite_coe_iff.2 (infinite_of_aleph0 hB)
  rw [aleph0_eq_n₀c hB]
  constructor
  · rintro (hν | hν)
    · obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hν
      exact Or.inl (aleph0_cardGt_cardN hB (cardN_nonempty_of_infinite k))
    · obtain ⟨D, hD⟩ := exists_mem_aleph0 (α := X)
      rw [mem_unitCls.1 hν, aleph0_eq_n₀c hD, cardGe_n₀c_iff]
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (sm_of_aleph0 hD hB)
      exact ⟨e.toEmbedding⟩
  · intro hge
    obtain ⟨-, C, -, rfl⟩ := mem_N₀C_of_cardGe hge
    obtain ⟨e⟩ := cardGe_n₀c_iff.1 hge
    have hC : C.Countable := by
      have : Countable B := (mem_aleph0_iff_ci.1 hB).1.to_subtype
      exact Set.countable_coe_iff.1 (Function.Injective.countable e.injective)
    by_cases hfin : C.Finite
    · exact Or.inl (n₀c_mem_NCinduct hfin)
    · exact Or.inr (mem_unitCls.2 (aleph0_eq_n₀c (mem_aleph0_iff_ci.2 ⟨hC, hfin⟩)).symm)

/-- ✱123·45. \(\vdash \colon\ldotp \exists !\aleph _{0}.\supset :\nu \in \text{NC induct} .\equiv .\aleph _{0}>\nu .\equiv .\nu <\aleph _{0} \quad[*123·43·44]\)

**Status.** proved (reading): convention Infin T, as in ✱123·44. -/
theorem pm123_45 {α X : Type*} (hX : InfinAx X) {ν : Set (Set X)} :
    (aleph0 : Set (Set α)).Nonempty →
      (ν ∈ NCinduct ↔ (aleph0 : Set (Set α)) >ᶜ ν) ∧
        ((aleph0 : Set (Set α)) >ᶜ ν ↔ ν <ᶜ (aleph0 : Set (Set α))) := by
  intro h
  refine ⟨⟨fun hν => pm123_43 hX h ν hν, fun hgt => ?_⟩, Iff.rfl⟩
  obtain ⟨B, hB⟩ := h
  obtain ⟨-, C, -, rfl⟩ := mem_N₀C_of_cardGt hgt
  rw [aleph0_eq_n₀c hB, cardGt_n₀c_iff] at hgt
  obtain ⟨⟨e⟩, hno⟩ := hgt
  have hC : C.Countable := by
    have : Countable B := (mem_aleph0_iff_ci.1 hB).1.to_subtype
    exact Set.countable_coe_iff.1 (Function.Injective.countable e.injective)
  by_cases hfin : C.Finite
  · exact n₀c_mem_NCinduct hfin
  · obtain ⟨e'⟩ := sm_iff_nonempty_equiv.1 (sm_of_aleph0 hB (mem_aleph0_iff_ci.2 ⟨hC, hfin⟩))
    exact absurd ⟨e'.toEmbedding⟩ hno

/-- ✱123·46. \(\vdash :\alpha \in \text{Cls induct} .\beta \in \aleph _{0}.\supset .\alpha \cup \beta \in \aleph _{0}\) -/
theorem pm123_46 {α : Type*} {A B : Set α} : A ∈ ClsInduct ∧ B ∈ aleph0 → A ∪ B ∈ aleph0 := by
  rintro ⟨hA, hB⟩
  obtain ⟨hc, hi⟩ := mem_aleph0_iff_ci.1 hB
  exact mem_aleph0_iff_ci.2 ⟨(mem_ClsInduct.1 hA).countable.union hc,
    hi.mono Set.subset_union_right⟩

/-- ✱123·47. \[\begin{align}\vdash \colon\ldotp \exists !\aleph _{0}.\supset :\alpha \in \text{Cls induct} \cup \aleph _{0}.&\equiv .(\exists \gamma ).\gamma \in \aleph _{0}.\alpha \subset \gamma .\\ &\equiv .\text{Nc}ʻ\alpha \leq \aleph _{0}\end{align}\]

The hypothesis `∃!ℵ₀`, the attributive occurrences `α ∈ ℵ₀`, `γ ∈ ℵ₀` and the side of `≤` are
in the type of `α` (as in ✱123·43); `Nc'α ≤ ℵ₀` is `N₀c'α ≤ ℵ₀` (note to ✱117·06). -/
theorem pm123_47 {α : Type*} {A : Set α} :
    (aleph0 : Set (Set α)).Nonempty →
      (A ∈ ClsInduct ∪ aleph0 ↔ ∃ G, G ∈ aleph0 ∧ A ⊆ G) ∧
        ((∃ G, G ∈ aleph0 ∧ A ⊆ G) ↔ n₀c A ≤ᶜ (aleph0 : Set (Set α))) := by
  intro h
  obtain ⟨B, hB⟩ := h
  have hBc : Countable B := (mem_aleph0_iff_ci.1 hB).1.to_subtype
  have hBi : Infinite B := Set.infinite_coe_iff.2 (infinite_of_aleph0 hB)
  have hcount : (∃ G, G ∈ aleph0 ∧ A ⊆ G) ↔ A.Countable := by
    constructor
    · rintro ⟨G, hG, hAG⟩
      exact (mem_aleph0_iff_ci.1 hG).1.mono hAG
    · intro hA
      by_cases hfin : A.Finite
      · exact ⟨A ∪ B, pm123_46 ⟨mem_ClsInduct.2 hfin, hB⟩, Set.subset_union_left⟩
      · exact ⟨A, mem_aleph0_iff_ci.2 ⟨hA, hfin⟩, subset_rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hcount]
    constructor
    · rintro (hA | hA)
      · exact (mem_ClsInduct.1 hA).countable
      · exact (mem_aleph0_iff_ci.1 hA).1
    · intro hA
      by_cases hfin : A.Finite
      · exact Or.inl (mem_ClsInduct.2 hfin)
      · exact Or.inr (mem_aleph0_iff_ci.2 ⟨hA, hfin⟩)
  · rw [hcount]
    show A.Countable ↔ (aleph0 : Set (Set α)) ≥ᶜ n₀c A
    rw [aleph0_eq_n₀c hB, cardGe_n₀c_iff]
    constructor
    · intro hA
      have : Countable A := hA.to_subtype
      by_cases hfin : A.Finite
      · have : Finite A := hfin.to_subtype
        refine (Function.Embedding.total A B).resolve_right fun ⟨e⟩ => ?_
        exact not_finite_iff_infinite.2 (Infinite.of_injective e e.injective) ‹Finite A›
      · obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (sm_of_aleph0 (mem_aleph0_iff_ci.2 ⟨hA, hfin⟩) hB)
        exact ⟨e.toEmbedding⟩
    · rintro ⟨e⟩
      exact Set.countable_coe_iff.1 (Function.Injective.countable e.injective)

/-- ✱123·5. \[\begin{align}\vdash :P,Q\in \text{Prog}.\\ R=\hat{X} \hat{Y} [(\exists \mu ,\nu ):&X=\mu _{P}\downarrow \nu _{Q}.Y=(\mu +_{c}1)_{P}\downarrow (\nu -_{c}1)_{Q}.\lor.\\ &X=\mu _{P}\downarrow 1_{Q}.Y=1_{P}\downarrow (\mu +_{c}1)_{Q}].\supset .R\in 1\rightarrow 1\end{align}\]

`P : α → α → Prop`, `Q : β → β → Prop`; `X`, `Y` are couples `α → β → Prop`. The apparent
variables `μ`, `ν` have types `M`, `N` that nothing determines; `μ +_c 1`, `ν −_c 1` are in the
types of `μ`, `ν` (as the relation `+_c 1` of ✱120·01), and the two `1`s of `1_Q`, `1_P` have
their own types `W₁`, `W₂`. In `X = μ_P ↓ ν_Q` the description occurring first has the larger
scope. The proposition holds for every determination of these types. -/
theorem pm123_5 {α β M N W₁ W₂ : Type*} {P : α → α → Prop} {Q : β → β → Prop}
    {R : (α → β → Prop) → (α → β → Prop) → Prop} :
    (P ∈ Prog ∧ Q ∈ Prog) ∧
      R = (fun X Y => ∃ (μ : Set (Set M)) (ν : Set (Set N)),
        (Desc (nuP μ) P (fun a => Desc (nuP ν) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) P
            (fun a => Desc (nuP (ν -ᶜ (one : Set (Set N)) : Set (Set N))) Q (fun b => Y = a ↓ b))) ∨
        (Desc (nuP μ) P (fun a => Desc (nuP (one : Set (Set W₁))) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (one : Set (Set W₂))) P
            (fun a => Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) Q (fun b => Y = a ↓ b)))) →
      R ∈ arrow one one := by
  rintro ⟨⟨hP, hQ⟩, hR⟩
  replace hR : R = rel1235 M N W₁ W₂ P Q := hR
  subst hR
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 hP
  obtain ⟨g, hg, rfl⟩ := prog_iff_seq.1 hQ
  have hE : ∀ p q : ℕ × ℕ, f p.1 ↓ g p.2 = f q.1 ↓ g q.2 → p = q := fun p q h => by
    obtain ⟨h1, h2⟩ := couple_eq_couple_iff.1 h
    exact Prod.ext (hf h1) (hg h2)
  rw [mem_arrow_one_one]
  refine ⟨?_, ?_⟩
  · rintro X X' Y ⟨h1, h2⟩
    obtain ⟨p, rfl, rfl⟩ := rel1235_fwd hf hg h1
    obtain ⟨q, rfl, hq⟩ := rel1235_fwd hf hg h2
    rw [dnext_injective (hE _ _ hq)]
  · rintro X Y Y' ⟨h1, h2⟩
    obtain ⟨p, rfl, rfl⟩ := rel1235_fwd hf hg h1
    obtain ⟨q, hq, rfl⟩ := rel1235_fwd hf hg h2
    rw [hE _ _ hq]

/-- ✱123·501. \(\vdash :\text{Hp}*123·5.\supset .\text{D}ʻR=\text{D}ʻP\times \text{D}ʻQ\)

Under the hypothesis of ✱123·5, with the types of `μ`, `ν` taken with all inductive cardinals
(Infin T, as PM's demonstration requires through ✱122·34) and the `1`s existent.
`D'Q × D'P` is `dom Q ×ₐ dom P`, the couples `x ↓ y` with `x ∈ D'P`, `y ∈ D'Q` (✱113·101).

**Status.** proved (corrected): the e-text has `D'P × D'Q`, which by ✱113·02·101 (`β × α` is the class of the couples `x ↓ y` with `x ∈ α`, `y ∈ β`) is the class of couples with referents in `D'Q`; the couples `μ_P ↓ ν_Q` are in `D'Q × D'P` (for `P`, `Q` of different types `D'P × D'Q` is not significant; for `n ↦ n + 1` on `ℕ` and on `{n ≥ 5}` it differs, `pm123_501_printed_false`). Also conventions Infin T (`InfinAx M`, `InfinAx N`) and existence of the `1`s (`[Nonempty W₁]`, `[Nonempty W₂]`, PM assumes every type has a member). -/
theorem pm123_501 {α β M N W₁ W₂ : Type*} (hM : InfinAx M) (hN : InfinAx N) [Nonempty W₁]
    [Nonempty W₂] {P : α → α → Prop} {Q : β → β → Prop}
    {R : (α → β → Prop) → (α → β → Prop) → Prop} :
    (P ∈ Prog ∧ Q ∈ Prog) ∧
      R = (fun X Y => ∃ (μ : Set (Set M)) (ν : Set (Set N)),
        (Desc (nuP μ) P (fun a => Desc (nuP ν) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) P
            (fun a => Desc (nuP (ν -ᶜ (one : Set (Set N)) : Set (Set N))) Q (fun b => Y = a ↓ b))) ∨
        (Desc (nuP μ) P (fun a => Desc (nuP (one : Set (Set W₁))) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (one : Set (Set W₂))) P
            (fun a => Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) Q (fun b => Y = a ↓ b)))) →
      dom R = dom Q ×ₐ dom P := by
  rintro ⟨⟨hP, hQ⟩, hR⟩
  replace hR : R = rel1235 M N W₁ W₂ P Q := hR
  subst hR
  have : Infinite M := infinAx_iff_infinite.1 hM
  have : Infinite N := infinAx_iff_infinite.1 hN
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 hP
  obtain ⟨g, hg, rfl⟩ := prog_iff_seq.1 hQ
  rw [rel1235_eq hf hg, dom_seqRel, dom_seqRel, dom_seqRel]
  ext X
  rw [mem_clsTimes]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨_, _, ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩
  · rintro ⟨x, y, ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩, rfl⟩
    obtain ⟨n, hn⟩ := dpos_surjective (i, j)
    exact ⟨n, by show f (dpos n).1 ↓ g (dpos n).2 = f i ↓ g j; rw [hn]⟩

/-- The printed form of ✱123·501 (with `D'P × D'Q`) is false (both progressions on `ℕ`). -/
theorem pm123_501_printed_false :
    ¬ ∀ (P Q : ℕ → ℕ → Prop) (R : (ℕ → ℕ → Prop) → (ℕ → ℕ → Prop) → Prop),
      (P ∈ Prog ∧ Q ∈ Prog) ∧
        R = (fun X Y => ∃ (μ : Set (Set ℕ)) (ν : Set (Set ℕ)),
          (Desc (nuP μ) P (fun a => Desc (nuP ν) Q (fun b => X = a ↓ b)) ∧
            Desc (nuP (μ +ᶜ (one : Set (Set ℕ)) : Set (Set ℕ))) P
              (fun a => Desc (nuP (ν -ᶜ (one : Set (Set ℕ)) : Set (Set ℕ))) Q
                (fun b => Y = a ↓ b))) ∨
          (Desc (nuP μ) P (fun a => Desc (nuP (one : Set (Set ℕ))) Q (fun b => X = a ↓ b)) ∧
            Desc (nuP (one : Set (Set ℕ))) P
              (fun a => Desc (nuP (μ +ᶜ (one : Set (Set ℕ)) : Set (Set ℕ))) Q
                (fun b => Y = a ↓ b)))) →
        dom R = dom P ×ₐ dom Q := by
  intro H
  have hf : Function.Injective (id : ℕ → ℕ) := Function.injective_id
  have hg : Function.Injective (fun n : ℕ => n + 5) := fun a b h => by simpa using h
  have hinf : InfinAx ℕ := infinAx_iff_infinite.2 inferInstance
  have h := H (SeqRel id) (SeqRel (fun n => n + 5)) _ ⟨⟨seqRel_mem_prog hf, seqRel_mem_prog hg⟩, rfl⟩
  have h' := pm123_501 (W₁ := ℕ) (W₂ := ℕ) hinf hinf
    ⟨⟨seqRel_mem_prog hf, seqRel_mem_prog hg⟩, rfl⟩
  rw [h'] at h
  have hmem : (0 : ℕ) ↓ (5 : ℕ) ∈ dom (SeqRel (fun n : ℕ => n + 5)) ×ₐ dom (SeqRel (id : ℕ → ℕ)) :=
    couple_mem_clsTimes.2 ⟨by rw [dom_seqRel]; exact ⟨0, rfl⟩, by rw [dom_seqRel]; exact ⟨0, rfl⟩⟩
  rw [h, couple_mem_clsTimes, dom_seqRel, dom_seqRel] at hmem
  obtain ⟨n, hn⟩ := hmem.1
  have : n + 5 = 0 := hn
  omega

/-- ✱123·502. \(\vdash :\text{Hp}*123·5.\supset .\text{ᗡ}ʻR\subset \text{D}ʻR.\overleftarrow{R}_{*}ʻ(1_{P}\downarrow 1_{Q})\subset \text{D}ʻR\)

`R⃖_*'(1_P ↓ 1_Q)`: the descriptions `1_P`, `1_Q` (constants `1` in types `W₃`, `W₄`) have the
scope of the inclusion, `1_P` the larger.

**Status.** proved (reading): under the hypothesis of ✱123·5 with conventions Infin T (`InfinAx M`, `InfinAx N`) and existent `1`s (`[Nonempty W₁]` … `[Nonempty W₄]`), as in ✱123·501. -/
theorem pm123_502 {α β M N W₁ W₂ W₃ W₄ : Type*} (hM : InfinAx M) (hN : InfinAx N) [Nonempty W₁]
    [Nonempty W₂] [Nonempty W₃] [Nonempty W₄] {P : α → α → Prop} {Q : β → β → Prop}
    {R : (α → β → Prop) → (α → β → Prop) → Prop} :
    (P ∈ Prog ∧ Q ∈ Prog) ∧
      R = (fun X Y => ∃ (μ : Set (Set M)) (ν : Set (Set N)),
        (Desc (nuP μ) P (fun a => Desc (nuP ν) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) P
            (fun a => Desc (nuP (ν -ᶜ (one : Set (Set N)) : Set (Set N))) Q (fun b => Y = a ↓ b))) ∨
        (Desc (nuP μ) P (fun a => Desc (nuP (one : Set (Set W₁))) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (one : Set (Set W₂))) P
            (fun a => Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) Q (fun b => Y = a ↓ b)))) →
      codom R ⊆ dom R ∧
        Desc (nuP (one : Set (Set W₃))) P
          (fun a => Desc (nuP (one : Set (Set W₄))) Q (fun b => rels (anc R) (a ↓ b) ⊆ dom R)) := by
  rintro ⟨⟨hP, hQ⟩, hR⟩
  replace hR : R = rel1235 M N W₁ W₂ P Q := hR
  subst hR
  have : Infinite M := infinAx_iff_infinite.1 hM
  have : Infinite N := infinAx_iff_infinite.1 hN
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 hP
  obtain ⟨g, hg, rfl⟩ := prog_iff_seq.1 hQ
  rw [rel1235_eq hf hg, desc_nuP_one_seqRel hf, desc_nuP_one_seqRel hg]
  refine ⟨(pm122_141 (seqRel_mem_prog ?_)).1, ?_⟩
  · intro m n h
    have h' := couple_eq_couple_iff.1 h
    exact dpos_injective (Prod.ext (hf h'.1) (hg h'.2))
  · intro y hy
    have := fld_of_anc_right (show anc _ _ y from hy)
    rw [fld_seqRel] at this
    rw [dom_seqRel]
    exact this

/-- ✱123·503. \(\vdash : \text{Hp} *123·5 . \supset . \text{D}ʻR \subset \overleftarrow{R}_{*}ʻ(1_{P} \downarrow 1_{Q})\)

**Status.** proved (reading): under the hypothesis of ✱123·5 with conventions Infin T and existent `1`s, as in ✱123·502. -/
theorem pm123_503 {α β M N W₁ W₂ W₃ W₄ : Type*} (hM : InfinAx M) (hN : InfinAx N) [Nonempty W₁]
    [Nonempty W₂] [Nonempty W₃] [Nonempty W₄] {P : α → α → Prop} {Q : β → β → Prop}
    {R : (α → β → Prop) → (α → β → Prop) → Prop} :
    (P ∈ Prog ∧ Q ∈ Prog) ∧
      R = (fun X Y => ∃ (μ : Set (Set M)) (ν : Set (Set N)),
        (Desc (nuP μ) P (fun a => Desc (nuP ν) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) P
            (fun a => Desc (nuP (ν -ᶜ (one : Set (Set N)) : Set (Set N))) Q (fun b => Y = a ↓ b))) ∨
        (Desc (nuP μ) P (fun a => Desc (nuP (one : Set (Set W₁))) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (one : Set (Set W₂))) P
            (fun a => Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) Q (fun b => Y = a ↓ b)))) →
      Desc (nuP (one : Set (Set W₃))) P
        (fun a => Desc (nuP (one : Set (Set W₄))) Q (fun b => dom R ⊆ rels (anc R) (a ↓ b))) := by
  rintro ⟨⟨hP, hQ⟩, hR⟩
  replace hR : R = rel1235 M N W₁ W₂ P Q := hR
  subst hR
  have : Infinite M := infinAx_iff_infinite.1 hM
  have : Infinite N := infinAx_iff_infinite.1 hN
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 hP
  obtain ⟨g, hg, rfl⟩ := prog_iff_seq.1 hQ
  rw [rel1235_eq hf hg, desc_nuP_one_seqRel hf, desc_nuP_one_seqRel hg]
  intro X hX
  rw [dom_seqRel] at hX
  obtain ⟨n, rfl⟩ := hX
  exact anc_iff_reflTransGen.2 ⟨⟨_, Or.inl (seqRel_apply _ 0)⟩, rtg_seqRel_of_le _ (Nat.zero_le n)⟩

/-- ✱123·504. \(\vdash : \text{Hp} *123·5 . \supset . BʻR = 1_{P} \downarrow 1_{Q} \quad[*123·34 . *120·414]\)

`B'R = 1_P ↓ 1_Q`: the description `B'R` occurs first and has the largest scope.

**Status.** proved (reading): under the hypothesis of ✱123·5 with conventions Infin T and existent `1`s, as in ✱123·502. -/
theorem pm123_504 {α β M N W₁ W₂ W₃ W₄ : Type*} (hM : InfinAx M) (hN : InfinAx N) [Nonempty W₁]
    [Nonempty W₂] [Nonempty W₃] [Nonempty W₄] {P : α → α → Prop} {Q : β → β → Prop}
    {R : (α → β → Prop) → (α → β → Prop) → Prop} :
    (P ∈ Prog ∧ Q ∈ Prog) ∧
      R = (fun X Y => ∃ (μ : Set (Set M)) (ν : Set (Set N)),
        (Desc (nuP μ) P (fun a => Desc (nuP ν) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) P
            (fun a => Desc (nuP (ν -ᶜ (one : Set (Set N)) : Set (Set N))) Q (fun b => Y = a ↓ b))) ∨
        (Desc (nuP μ) P (fun a => Desc (nuP (one : Set (Set W₁))) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (one : Set (Set W₂))) P
            (fun a => Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) Q (fun b => Y = a ↓ b)))) →
      Desc Beg R (fun c => Desc (nuP (one : Set (Set W₃))) P
        (fun a => Desc (nuP (one : Set (Set W₄))) Q (fun b => c = a ↓ b))) := by
  rintro ⟨⟨hP, hQ⟩, hR⟩
  replace hR : R = rel1235 M N W₁ W₂ P Q := hR
  subst hR
  have : Infinite M := infinAx_iff_infinite.1 hM
  have : Infinite N := infinAx_iff_infinite.1 hN
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 hP
  obtain ⟨g, hg, rfl⟩ := prog_iff_seq.1 hQ
  have hinj : Function.Injective (fun n => f (dpos n).1 ↓ g (dpos n).2) := by
    intro m n h
    have h' := couple_eq_couple_iff.1 h
    exact dpos_injective (Prod.ext (hf h'.1) (hg h'.2))
  rw [rel1235_eq hf hg, desc_beg_seqRel hinj, desc_nuP_one_seqRel hf, desc_nuP_one_seqRel hg]
  rfl

/-- ✱123·51. \[\begin{align}\vdash : \text{Hp} *123·5 . \supset . R \in \text{Prog} . \text{D}ʻR = &\text{D}ʻP \times \text{D}ʻQ\\ &[*123·5·501·502·503·504]\end{align}\]

**Status.** proved (corrected): `D'P × D'Q` replaced by `D'Q × D'P`, as in ✱123·501 (with the conventions of ✱123·501). -/
theorem pm123_51 {α β M N W₁ W₂ : Type*} (hM : InfinAx M) (hN : InfinAx N) [Nonempty W₁]
    [Nonempty W₂] {P : α → α → Prop} {Q : β → β → Prop}
    {R : (α → β → Prop) → (α → β → Prop) → Prop} :
    (P ∈ Prog ∧ Q ∈ Prog) ∧
      R = (fun X Y => ∃ (μ : Set (Set M)) (ν : Set (Set N)),
        (Desc (nuP μ) P (fun a => Desc (nuP ν) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) P
            (fun a => Desc (nuP (ν -ᶜ (one : Set (Set N)) : Set (Set N))) Q (fun b => Y = a ↓ b))) ∨
        (Desc (nuP μ) P (fun a => Desc (nuP (one : Set (Set W₁))) Q (fun b => X = a ↓ b)) ∧
          Desc (nuP (one : Set (Set W₂))) P
            (fun a => Desc (nuP (μ +ᶜ (one : Set (Set M)) : Set (Set M))) Q (fun b => Y = a ↓ b)))) →
      R ∈ Prog ∧ dom R = dom Q ×ₐ dom P := by
  intro h
  refine ⟨?_, pm123_501 hM hN h⟩
  obtain ⟨⟨hP, hQ⟩, hR⟩ := h
  replace hR : R = rel1235 M N W₁ W₂ P Q := hR
  subst hR
  have : Infinite M := infinAx_iff_infinite.1 hM
  have : Infinite N := infinAx_iff_infinite.1 hN
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 hP
  obtain ⟨g, hg, rfl⟩ := prog_iff_seq.1 hQ
  rw [rel1235_eq hf hg]
  refine seqRel_mem_prog fun m n h => ?_
  have h' := couple_eq_couple_iff.1 h
  exact dpos_injective (Prod.ext (hf h'.1) (hg h'.2))

/-- ✱123·52. \(\vdash . \aleph _{0} = \aleph _{0} \times _{c} \aleph _{0} = \aleph _{0}^{2} \quad[*123·51 . *116·34 . *113·25·204]\)

The chain is the conjunction of its links, in one type `γ`; the arithmetical components
(`ℵ₀`, `ℵ₀`, `ℵ₀`, `2`) have their own types `W₁` … `W₄`.

**Status.** proved (reading): convention IIT (Prefatory Statement, II, IV): adequate types for the arithmetical components (`∃!ℵ₀` for each `ℵ₀`, as in ✱123·4; `∃!2`). -/
theorem pm123_52 {γ W₁ W₂ W₃ W₄ : Type*} (h1 : (aleph0 : Set (Set W₁)).Nonempty)
    (h2 : (aleph0 : Set (Set W₂)).Nonempty) (h3 : (aleph0 : Set (Set W₃)).Nonempty)
    (h4 : (two : Set (Set W₄)).Nonempty) :
    (aleph0 : Set (Set γ)) = ((aleph0 : Set (Set W₁)) ×ᶜ (aleph0 : Set (Set W₂)) : Set (Set γ)) ∧
      ((aleph0 : Set (Set W₁)) ×ᶜ (aleph0 : Set (Set W₂)) : Set (Set γ)) =
        ((aleph0 : Set (Set W₃)) ^ᶜ (two : Set (Set W₄)) : Set (Set γ)) := by
  obtain ⟨A₁, hA₁⟩ := h1
  obtain ⟨A₂, hA₂⟩ := h2
  obtain ⟨A₃, hA₃⟩ := h3
  rw [two_eq_cardN] at h4
  obtain ⟨T, hT⟩ := h4
  have hTne : T.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hT.2]; omega)
  have hmul : ((aleph0 : Set (Set W₁)) ×ᶜ (aleph0 : Set (Set W₂)) : Set (Set γ)) = aleph0 := by
    rw [aleph0_eq_n₀c hA₁, aleph0_eq_n₀c hA₂, n₀c_cardMul_n₀c]
    exact (aleph0_eq_nc (countable_infinite_clsTimes hA₂ (mem_aleph0_iff_ci.1 hA₁).1
      (infinite_of_aleph0 hA₁).nonempty)).symm
  refine ⟨hmul.symm, ?_⟩
  rw [hmul, two_eq_cardN, cardN_eq_n₀c hT, aleph0_eq_n₀c hA₃, n₀c_cardExp_n₀c]
  exact aleph0_eq_nc (clsExp_mem_aleph0 hA₃ hT.1 hTne)

/-- ✱123·53. \(\vdash : \nu \in \text{NC induct} - \iota ʻO . \supset . \aleph _{0}^\nu = \aleph _{0} \quad[*123·52 . *116·52]\)

(The e-text prints `ι'O` for `ι'0`.)

**Status.** proved (reading): conventions IIT and Infin T, as in ✱123·41 (`∃!ℵ₀` for the base, `InfinAx X` for the type of `ν`). -/
theorem pm123_53 {X W γ : Type*} (hX : InfinAx X) {ν : Set (Set X)} :
    (aleph0 : Set (Set W)).Nonempty → ν ∈ NCinduct \ ι zero →
      ((aleph0 : Set (Set W)) ^ᶜ ν : Set (Set γ)) = aleph0 := by
  intro h hν
  have : Infinite X := infinAx_iff_infinite.1 hX
  obtain ⟨A, hA⟩ := h
  obtain ⟨k, rfl⟩ := mem_NCinduct_ne_zero.1 hν
  obtain ⟨B, hB⟩ := cardN_nonempty_of_infinite (β := X) (k + 1)
  rw [cardN_eq_n₀c hB, aleph0_eq_n₀c hA, n₀c_cardExp_n₀c]
  exact (aleph0_eq_nc (clsExp_mem_aleph0 hA hB.1
    (Set.nonempty_of_ncard_ne_zero (by rw [hB.2]; omega)))).symm

/-- ✱123·7. \(\vdash : \text{Infin ax} (x) . \text{Mult ax} . \supset . \exists ! \aleph _{0} (tʻx)\)

`ℵ₀(t'x)` is `clsT2 aleph0 (typ x)` (classes of classes of terms of the type of `x`); `Mult ax`
is taken at the type of PM's `NC induct(t'x)` (classes of classes of classes of terms of
that type, ✱88·32), `MultAx (Set X)`. (It is a theorem of Lean, but stays a hypothesis.) -/
theorem pm123_7 {X : Type*} {x : X} :
    InfinAxAt x ∧ MultAx (Set X) → (clsT2 aleph0 (typ x)).Nonempty := by
  rintro ⟨hx, -⟩
  have : Infinite X := infinAx_iff_infinite.1 ((infinAxAt_iff x).1 hx)
  have : Infinite (Set X) := infinite_set_of_infinite
  rw [clsT2_eq]
  exact aleph0_nonempty_iff.2 inferInstance

/-!
## [✱124] Reflexive classes and cardinals

*(Vol. 2, p. 278)*

> *Summary of* *124.
>
> In this number, we have to take up the second definition of infinity mentioned in the introduction to this Section. A class which is infinite according to this definition we propose to call a reflexive class, because a class which is of this kind is capable of *reflexion* into a part of itself. A class is called *reflexive* when there is a one-one relation which correlates the class with a proper part of itself. (A *proper part* is a part not the whole.) A reflexive cardinal is the homogeneous cardinal of a reflexive class.
>
> …

**Lean reading.** `Cls refl`, `NC refl`, `NC mult` are `ClsRefl`, `NCrefl`, `NCmult β`
(✱124·01–·03; `Nc'ρ ∈ NC refl` is `N₀c'ρ ∈ NC refl` by ✱124·021). In Lean the reflexive classes are
the infinite classes (private lemma `clsRefl_iff`, via the shift of an injective sequence); the
multiplicative axiom is a theorem of Lean, but `ℵ₀ ∈ NC mult` stays a hypothesis exactly where PM
has it, at the type of PM's demonstration (the classes of classes it is applied to). `∩Cl'ρ` is the
relation `opR (· ∩ ·) (cl ρ)` (✱38). An `ℵ₀` in arithmetical position has its own type with
`∃!ℵ₀` (IIT, as in ✱123), `NC induct` in a type left free gets `InfinAx` (Infin T), and the formal
numbers of ✱124·57 get adequate types (`AdeqExp`).

**Status.** proved (all propositions; ✱124·01·02·021·03 definition;
✱124·151·23·231·232·24·252·253·26·28·3·31·33·41·535·57 proved (reading), see their docstrings)
-/

/-- ✱124·01 (Df). \(\text{Cls refl} = \hat{\rho} \{(\exists R) . R \in 1 \rightarrow 1 . \text{ᗡ}ʻR \subset \text{D}ʻR . \exists ! \overrightarrow{B}ʻR . \rho = \text{D}ʻR\} \quad\text{Df}\) -/
theorem pm124_01 {α : Type*} :
    (ClsRefl : Set (Set α)) = {ρ | ∃ R : α → α → Prop,
      ((R ∈ arrow one one ∧ codom R ⊆ dom R) ∧ (refs Beg R).Nonempty) ∧ ρ = dom R} := rfl

/-- ✱124·02 (Df). \(\text{NC refl} = \text{N}_{0}\text{c}ʻʻ\text{Cls refl} \quad\text{Df}\) -/
theorem pm124_02 {α : Type*} : (NCrefl : Set (Set (Set α))) = N₀c ʻʻ ClsRefl := rfl

/-- ✱124·021 (Df). \(\text{Nc}ʻ\rho \in \text{NC refl} . = . \text{N}_{0}\text{c}ʻ\rho \in \text{NC refl} \quad\text{Df}\)

**Status.** definition: a rule of translation (normal adjustment): `Nc'ρ ∈ NC refl` is written `N₀c'ρ ∈ NC refl`, so the target is the identity of the two readings. -/
theorem pm124_021 {α : Type*} {ρ : Set α} : n₀c ρ ∈ NCrefl ↔ n₀c ρ ∈ NCrefl := Iff.rfl

/-- ✱124·03 (Df). \(\text{NC mult} = \text{NC} \cap \hat{\alpha} \{\kappa \in \alpha \cap \text{Cls ex}^{2}\,\text{excl}. \supset _{\kappa } . \exists ! {\in}_{\Delta}ʻ\kappa \} \quad\text{Df}\)

The converse-domain type `β` of `NC` is explicit (`Defs/Part3`, decision 3). -/
theorem pm124_03 {α β : Type*} :
    (NCmult β : Set (Set (Set (Set α)))) =
      NC β ∩ {μ | ∀ K, K ∈ μ ∩ ClsEx2excl → (sel memRel K).Nonempty} := rfl

/-- ✱124·1. \[\begin{align}&\vdash : \rho \in \text{Cls refl} . \equiv . (\exists R). R \in 1 \rightarrow 1 . \text{ᗡ}ʻR \subset \text{D}ʻR . \exists ! \overrightarrow{B}ʻR . \rho = \text{D}ʻR\\ &[(*124·01)]\end{align}\] -/
theorem pm124_1 {α : Type*} {ρ : Set α} :
    ρ ∈ ClsRefl ↔ ∃ R : α → α → Prop,
      ((R ∈ arrow one one ∧ codom R ⊆ dom R) ∧ (refs Beg R).Nonempty) ∧ ρ = dom R := Iff.rfl

/-- ✱124·11. \(\vdash : R \in 1 \rightarrow 1 . \text{ᗡ}ʻR \subset \text{D}ʻR . \exists ! \overrightarrow{B}ʻR . \supset . \text{D}ʻR \in \text{Cls refl} \quad[*124·1]\) -/
theorem pm124_11 {α : Type*} {R : α → α → Prop} :
    (R ∈ arrow one one ∧ codom R ⊆ dom R) ∧ (refs Beg R).Nonempty → dom R ∈ ClsRefl :=
  fun h => ⟨R, h, rfl⟩

/-- ✱124·12. \(\vdash . \aleph _{0} \subset \text{Cls refl} \quad[*123·12 . *124·1]\) -/
theorem pm124_12 {α : Type*} : (aleph0 : Set (Set α)) ⊆ ClsRefl :=
  fun _ hA => clsRefl_iff.2 (infinite_of_aleph0 hA)

/-- ✱124·13. \(\vdash : \rho \in \text{Cls refl} . \supset . \exists ! \aleph _{0} \cap \text{Cl}ʻ\rho \quad[*124·1 . *123·192]\) -/
theorem pm124_13 {α : Type*} {ρ : Set α} : ρ ∈ ClsRefl → (aleph0 ∩ cl ρ).Nonempty := by
  intro h
  obtain ⟨C, hC, hCρ⟩ := exists_aleph0_sub (clsRefl_iff.1 h)
  exact ⟨C, hC, hCρ⟩

/-- ✱124·14. \(\vdash :\rho \in \text{Cls refl} .\supset .\rho \cup \sigma \in \text{Cls refl}\) -/
theorem pm124_14 {α : Type*} {ρ σ : Set α} : ρ ∈ ClsRefl → ρ ∪ σ ∈ ClsRefl :=
  fun h => clsRefl_iff.2 ((clsRefl_iff.1 h).mono Set.subset_union_left)

/-- ✱124·141. \(\vdash :\exists ! Cl ʻ\rho \cap \text{Cls refl} .\supset .\rho \in \text{Cls refl}\) -/
theorem pm124_141 {α : Type*} {ρ : Set α} : (cl ρ ∩ ClsRefl).Nonempty → ρ ∈ ClsRefl :=
  fun ⟨_, hμρ, hμ⟩ => clsRefl_iff.2 ((clsRefl_iff.1 hμ).mono hμρ)

/-- ✱124·15. \(\vdash :\rho \in \text{Cls refl} .\equiv .\exists !\aleph _{0}\cap \text{Cl} ʻ\rho \) -/
theorem pm124_15 {α : Type*} {ρ : Set α} : ρ ∈ ClsRefl ↔ (aleph0 ∩ cl ρ).Nonempty :=
  ⟨pm124_13, fun ⟨_, hC, hCρ⟩ => clsRefl_iff.2 ((infinite_of_aleph0 hC).mono hCρ)⟩

/-- ✱124·151. \(\vdash :\rho \in \text{Cls refl} .\equiv .\text{Nc}ʻ\rho \geq \aleph _{0} \quad[*124·15.*117·22]\)

`Nc'ρ ≥ ℵ₀` is `N₀c'ρ ≥ ℵ₀` (note to ✱117·06); the `ℵ₀`, a side of `≥`, is in a type `W`.

**Status.** proved (reading): convention IIT (Prefatory Statement, II (iii), IV): the `ℵ₀` in arithmetical position is taken in a type `W` with `∃!ℵ₀` (as in ✱123·4); in a finite `W` the right side is false. -/
theorem pm124_151 {α W : Type*} (hW : (aleph0 : Set (Set W)).Nonempty) {ρ : Set α} :
    ρ ∈ ClsRefl ↔ n₀c ρ ≥ᶜ (aleph0 : Set (Set W)) := by
  obtain ⟨A, hA⟩ := hW
  rw [aleph0_eq_n₀c hA, cardGe_n₀c_iff, clsRefl_iff]
  obtain ⟨eA⟩ := mem_aleph0_iff_equiv.1 hA
  constructor
  · intro h
    exact ⟨eA.symm.toEmbedding.trans h.natEmbedding⟩
  · rintro ⟨e⟩
    have : Infinite A := Set.infinite_coe_iff.2 (infinite_of_aleph0 hA)
    exact Set.infinite_coe_iff.1 (Infinite.of_injective e e.injective)

/-- ✱124·16. \[\begin{align}\vdash :\rho \in \text{Cls refl} .&\equiv .(\exists \sigma ).\sigma \subset \rho .\exists !\rho -\sigma .\rho \text{ sm } \sigma.\\ &\equiv .\exists ! \text{Nc} ʻ\rho \cap \text{Cl} ʻ\rho -\iota ʻ\rho \end{align}\]

`Nc'ρ ∩ Cl'ρ − ι'ρ` is `(nc α ρ ∩ cl ρ) \ ι ρ` (`∩ Cl'ρ` puts `Nc'ρ` in the type of `ρ`).
The chain is the conjunction of its links. -/
theorem pm124_16 {α : Type*} {ρ : Set α} :
    (ρ ∈ ClsRefl ↔ ∃ σ, (σ ⊆ ρ ∧ (ρ \ σ).Nonempty) ∧ sm ρ σ) ∧
      ((∃ σ, (σ ⊆ ρ ∧ (ρ \ σ).Nonempty) ∧ sm ρ σ) ↔ ((nc α ρ ∩ cl ρ) \ ι ρ).Nonempty) := by
  refine ⟨⟨fun h => ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have hρ := clsRefl_iff.1 h
    obtain ⟨x, hx⟩ := hρ.nonempty
    obtain ⟨R, h11, hdom, hcod⟩ := exists_shift hρ hx
    exact ⟨ρ \ ι x, ⟨fun y hy => hy.1, x, hx, fun h => h.2 rfl⟩, R, ⟨h11, hdom.symm⟩, hcod.symm⟩
  · rintro ⟨σ, ⟨hσ, y, hyρ, hyσ⟩, hsm⟩
    refine clsRefl_iff.2 fun hfin => hyσ ?_
    obtain ⟨hσf, hcard⟩ := (sm_iff_of_finite hfin).1 hsm
    rw [Set.eq_of_subset_of_ncard_le hσ (le_of_eq hcard) hfin]
    exact hyρ
  · rintro ⟨σ, ⟨hσ, y, hyρ, hyσ⟩, hsm⟩
    exact ⟨σ, ⟨sm_symm hsm, hσ⟩, fun h => hyσ (by rw [mem_unitCls.1 h]; exact hyρ)⟩
  · rintro ⟨σ, ⟨hsm, hσ⟩, hne⟩
    refine ⟨σ, ⟨hσ, ?_⟩, sm_symm hsm⟩
    by_contra h
    apply hne
    show σ = ρ
    exact Set.Subset.antisymm hσ fun y hy => by
      by_contra hyσ
      exact h ⟨y, hy, hyσ⟩

/-- ✱124·17. \(\vdash :\rho \in \text{Cls refl} .\equiv .(\exists x).x\in \rho .\rho -\iota ʻx \text{ sm } \rho\) -/
theorem pm124_17 {α : Type*} {ρ : Set α} : ρ ∈ ClsRefl ↔ ∃ x, x ∈ ρ ∧ sm (ρ \ ι x) ρ := by
  constructor
  · intro h
    have hρ := clsRefl_iff.1 h
    obtain ⟨x, hx⟩ := hρ.nonempty
    exact ⟨x, hx, sm_diff_finite hρ (Set.finite_singleton x)⟩
  · rintro ⟨x, hx, hsm⟩
    exact pm124_16.1.2 ⟨ρ \ ι x, ⟨fun y hy => hy.1, x, hx, fun h => h.2 rfl⟩, sm_symm hsm⟩

/-- ✱124·18. \(\vdash :\rho \in \text{Cls refl}.\rho \text{ sm }\sigma .\supset .\sigma \in \text{Cls refl} \quad[*124·151.*100·321]\)

`ρ` and `σ` may be of different types. -/
theorem pm124_18 {α β : Type*} {ρ : Set α} {σ : Set β} : ρ ∈ ClsRefl ∧ sm ρ σ → σ ∈ ClsRefl := by
  rintro ⟨h, hsm⟩
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hsm
  have : Infinite ρ := Set.infinite_coe_iff.2 (clsRefl_iff.1 h)
  exact clsRefl_iff.2 (Set.infinite_coe_iff.1 (Infinite.of_injective e e.injective))

/-- ✱124·181. \(\vdash :\rho \in \text{Cls refl}.\supset .\rho -\iota ʻx\in \text{Cls refl}.\rho -\iota ʻx\text{ sm }\rho \) -/
theorem pm124_181 {α : Type*} {ρ : Set α} {x : α} :
    ρ ∈ ClsRefl → ρ \ ι x ∈ ClsRefl ∧ sm (ρ \ ι x) ρ := by
  intro h
  have hρ := clsRefl_iff.1 h
  exact ⟨clsRefl_iff.2 (hρ.sdiff (Set.finite_singleton x)), sm_diff_finite hρ (Set.finite_singleton x)⟩

/-- ✱124·182. \[\begin{align}&\vdash :\rho \in \text{Cls refl}.\sigma \in \text{Cls induct}.\supset .\rho -\sigma \in \text{Cls refl}.\rho -\sigma \text{ sm }\rho \\ &[*124·181.*120·26]\end{align}\] -/
theorem pm124_182 {α : Type*} {ρ σ : Set α} :
    ρ ∈ ClsRefl ∧ σ ∈ ClsInduct → ρ \ σ ∈ ClsRefl ∧ sm (ρ \ σ) ρ := by
  rintro ⟨h, hσ⟩
  have hρ := clsRefl_iff.1 h
  have hσ' := mem_ClsInduct.1 hσ
  exact ⟨clsRefl_iff.2 (hρ.sdiff hσ'), sm_diff_finite hρ hσ'⟩

/-- ✱124·2. \(\vdash :\mu \in \text{NC refl}.\equiv .(\exists \rho ).\rho \in \text{Cls refl}.\mu =\text{N}_{0}\text{c}ʻ\rho \quad[(*124·02)]\) -/
theorem pm124_2 {α : Type*} {μ : Set (Set α)} :
    μ ∈ NCrefl ↔ ∃ ρ, ρ ∈ ClsRefl ∧ μ = n₀c ρ := Iff.rfl

/-- ✱124·21. \[\begin{align}&\vdash :\mu \in \text{NC refl}.\equiv .\\ &(\exists R).R\in 1\rightarrow 1.\text{ᗡ}ʻR\subset \text{D}ʻR.\exists !.\overrightarrow{B}ʻR.\mu =\text{N}_{0}\text{c}ʻ\text{D}ʻR \quad[*124·2·1]\end{align}\] -/
theorem pm124_21 {α : Type*} {μ : Set (Set α)} :
    μ ∈ NCrefl ↔ ∃ R : α → α → Prop,
      ((R ∈ arrow one one ∧ codom R ⊆ dom R) ∧ (refs Beg R).Nonempty) ∧ μ = n₀c (dom R) := by
  constructor
  · rintro ⟨ρ, ⟨R, hR, rfl⟩, rfl⟩
    exact ⟨R, hR, rfl⟩
  · rintro ⟨R, hR, rfl⟩
    exact ⟨dom R, ⟨R, hR, rfl⟩, rfl⟩

/-- ✱124·23. \(\vdash :\mu \in \text{NC refl}.\equiv .\mu \geq \aleph _{0}\)

**Status.** proved (reading): convention IIT, as in ✱124·151 (`∃!ℵ₀` in the type `W` of the `ℵ₀` that is a side of `≥`). -/
theorem pm124_23 {α W : Type*} (hW : (aleph0 : Set (Set W)).Nonempty) {μ : Set (Set α)} :
    μ ∈ NCrefl ↔ μ ≥ᶜ (aleph0 : Set (Set W)) := by
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact (pm124_151 hW).1 hρ
  · intro hge
    obtain ⟨A, -, rfl, -⟩ := mem_N₀C_of_cardGe hge
    exact ⟨A, (pm124_151 hW).2 hge, rfl⟩

/-- ✱124·231. \(\vdash :\exists !\text{NC refl}.\equiv .\exists !\text{Cls refl}.\equiv .\exists !\aleph _{0} \quad[*124·2·12·13]\)

The three constants are taken in corresponding types (`NC refl = N₀c''Cls refl`,
`ℵ₀ ⊂ Cls refl`, ✱124·02·12): cardinals of classes of `α`-things, classes of `α`-things.

**Status.** proved (reading): the typically ambiguous constants `NC refl`, `Cls refl`, `ℵ₀` are taken in the corresponding types that PM's definitions relate (with unrelated types the equivalences fail, e.g. a finite and an infinite type). -/
theorem pm124_231 {α : Type*} :
    ((NCrefl : Set (Set (Set α))).Nonempty ↔ (ClsRefl : Set (Set α)).Nonempty) ∧
      ((ClsRefl : Set (Set α)).Nonempty ↔ (aleph0 : Set (Set α)).Nonempty) := by
  refine ⟨⟨fun ⟨_, ρ, hρ, _⟩ => ⟨ρ, hρ⟩, fun ⟨ρ, hρ⟩ => ⟨_, ρ, hρ, rfl⟩⟩,
    ⟨fun ⟨ρ, hρ⟩ => ?_, fun ⟨A, hA⟩ => ⟨A, pm124_12 hA⟩⟩⟩
  obtain ⟨C, hC, -⟩ := exists_aleph0_sub (clsRefl_iff.1 hρ)
  exact ⟨C, hC⟩

/-- ✱124·232. \(\vdash :\exists !\text{NC refl}.\supset .\text{Infin ax} \quad[*124·231.*123·18]\)

**Status.** proved (reading): `NC refl` and `Infin ax` are taken in corresponding types, as in ✱124·231 (`Infin ax` for the classes whose cardinals are in `NC refl`). -/
theorem pm124_232 {α : Type*} : (NCrefl : Set (Set (Set α))).Nonempty → InfinAx α := by
  rintro ⟨_, ρ, hρ, -⟩
  rw [infinAx_iff_infinite]
  have : Infinite ρ := Set.infinite_coe_iff.2 (clsRefl_iff.1 hρ)
  exact Infinite.of_injective (Subtype.val : ρ → α) Subtype.val_injective

/-- ✱124·24. \(\vdash \colon\ldotp \mu \in \text{NC refl}.\equiv :\mu \in \text{N}_{0}\text{C}:(\exists \nu ).\mu =\aleph _{0}+_{c}\nu .\nu \in \text{NC}\)

The `ℵ₀` of `ℵ₀ +_c ν` is an arithmetical component in a type `W`; the apparent variable `ν`
and its `NC` are taken in the type of `μ` (the converse domain of `Nc` in the same type).

**Status.** proved (reading): convention IIT for the `ℵ₀` (`∃!ℵ₀` in `W`, as in ✱123·4); the type of the apparent variable `ν`, which PM leaves undetermined, is that of `μ`, and `NC` is taken with converse domain of that type (in too small a type for `ν` the equivalence fails). -/
theorem pm124_24 {α W : Type*} (hW : (aleph0 : Set (Set W)).Nonempty) {μ : Set (Set α)} :
    μ ∈ NCrefl ↔ μ ∈ N₀C ∧
      ∃ ν : Set (Set α), μ = ((aleph0 : Set (Set W)) +ᶜ ν : Set (Set α)) ∧ ν ∈ NC α := by
  obtain ⟨A, hA⟩ := hW
  rw [aleph0_eq_n₀c hA]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    refine ⟨⟨ρ, rfl⟩, n₀c ρ, ?_, ρ, n₀c_eq_nc ρ⟩
    rw [n₀c_cardAdd_n₀c, n₀c_eq_nc]
    exact nc_eq_nc_of_sm (sm_symm (sm_clsSum_left_absorb (clsRefl_iff.1 hρ)
      (mem_aleph0_iff_ci.1 hA).1))
  · rintro ⟨⟨C, rfl⟩, ν, hν, -⟩
    have hC : C ∈ (n₀c A +ᶜ ν : Set (Set α)) := hν ▸ self_mem_n₀c C
    obtain ⟨A', B', ⟨hAA', -⟩, hsm⟩ := hC
    have hA' : A' ∈ aleph0 := aleph0_of_sm hA (n₀c_eq_n₀c_iff.1 hAA')
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hsm
    have : Infinite A' := Set.infinite_coe_iff.2 (infinite_of_aleph0 hA')
    have : Infinite C := Infinite.of_injective (e.symm ∘ (clsSumEquiv A' B').symm ∘ Sum.inl)
      (e.symm.injective.comp ((clsSumEquiv A' B').symm.injective.comp Sum.inl_injective))
    exact ⟨C, clsRefl_iff.2 (Set.infinite_coe_iff.1 this), rfl⟩

/-- ✱124·25. \[\begin{align}&\vdash :\mu \in \text{NC refl}.\equiv .\mu \in \text{N}_{0}\text{C}.\mu =\mu +_{c}1.\equiv .\exists !\mu .\mu =\mu +_{c}1 \\ &[*124·17·2]\end{align}\]

`μ = μ +_c 1` is an equation in the type of `μ`; the `1` is in the type of the other argument.
The chain is the conjunction of its links. -/
theorem pm124_25 {α : Type*} {μ : Set (Set α)} :
    (μ ∈ NCrefl ↔ μ ∈ N₀C ∧ μ = (μ +ᶜ (one : Set (Set α)) : Set (Set α))) ∧
      ((μ ∈ N₀C ∧ μ = (μ +ᶜ (one : Set (Set α)) : Set (Set α))) ↔
        μ.Nonempty ∧ μ = (μ +ᶜ (one : Set (Set α)) : Set (Set α))) := by
  refine ⟨⟨?_, ?_⟩, ⟨fun ⟨⟨A, hA⟩, h⟩ => ⟨by rw [hA]; exact n₀c_nonempty A, h⟩,
    fun ⟨hne, h⟩ => ⟨?_, h⟩⟩⟩
  · rintro ⟨ρ, hρ, rfl⟩
    have hρ' := clsRefl_iff.1 hρ
    obtain ⟨a, -⟩ := hρ'.nonempty
    refine ⟨⟨ρ, rfl⟩, ?_⟩
    rw [one_eq_n₀c_singleton a, n₀c_cardAdd_n₀c, n₀c_eq_nc]
    exact nc_eq_nc_of_sm (sm_symm (sm_clsSum_right_absorb hρ' (Set.countable_singleton a)))
  · rintro ⟨⟨C, rfl⟩, h⟩
    refine ⟨C, clsRefl_iff.2 fun hfin => ?_, rfl⟩
    obtain ⟨j, ⟨hj, hjne⟩, -, hc⟩ := (n₀c_eq_cardAdd_one_iff hfin).1 h
    rw [n₀c_eq_cardN hfin] at hj
    have := cardN_inj ⟨C, hfin, rfl⟩ hj
    omega
  · obtain ⟨ξ, hξ⟩ := hne
    rw [h] at hξ
    obtain ⟨A, -, ⟨hA, -⟩, -⟩ := hξ
    exact ⟨A, hA⟩

/-- ✱124·251. \(\vdash :\mu \in \text{NC refl}.\supset .\mu =\mu +_{c}1 \quad[*124·25]\) -/
theorem pm124_251 {α : Type*} {μ : Set (Set α)} :
    μ ∈ NCrefl → μ = (μ +ᶜ (one : Set (Set α)) : Set (Set α)) :=
  fun h => (pm124_25.1.1 h).2

/-- ✱124·252. \(\vdash :\mu \in \text{NC refl}.\nu \in \text{NC induct}.\supset .\mu =\mu +_{c}\nu\)

The equation is in the type of `μ`; `ν` is a real variable of a type `X`.

**Status.** proved (reading): convention Infin T (Prefatory Statement, VI): `μ ∈ NC refl` implies a type with all inductive cardinals, so `NC induct` (the type of `ν`) is taken with `InfinAx X` (for `ν = Λ` in a finite type the proposition fails). -/
theorem pm124_252 {α X : Type*} (hX : InfinAx X) {μ : Set (Set α)} {ν : Set (Set X)} :
    μ ∈ NCrefl ∧ ν ∈ NCinduct → μ = (μ +ᶜ ν : Set (Set α)) := by
  rintro ⟨⟨ρ, hρ, rfl⟩, hν⟩
  have : Infinite X := infinAx_iff_infinite.1 hX
  obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hν
  obtain ⟨B, hB⟩ := cardN_nonempty_of_infinite (β := X) k
  rw [cardN_eq_n₀c hB, n₀c_cardAdd_n₀c, n₀c_eq_nc]
  exact nc_eq_nc_of_sm (sm_symm (sm_clsSum_right_absorb (clsRefl_iff.1 hρ) hB.1.countable))

/-- ✱124·253. \(\vdash :\mu \in \text{NC refl}.\supset .\mu =\mu +_{c}\aleph _{0}\)

**Status.** proved (reading): convention IIT, as in ✱124·151 (`∃!ℵ₀` in the type `W` of the `ℵ₀` subjected to `+_c`). -/
theorem pm124_253 {α W : Type*} (hW : (aleph0 : Set (Set W)).Nonempty) {μ : Set (Set α)} :
    μ ∈ NCrefl → μ = (μ +ᶜ (aleph0 : Set (Set W)) : Set (Set α)) := by
  rintro ⟨ρ, hρ, rfl⟩
  obtain ⟨A, hA⟩ := hW
  rw [aleph0_eq_n₀c hA, n₀c_cardAdd_n₀c, n₀c_eq_nc]
  exact nc_eq_nc_of_sm (sm_symm (sm_clsSum_right_absorb (clsRefl_iff.1 hρ)
    (mem_aleph0_iff_ci.1 hA).1))

/-- ✱124·26. \(\vdash \colon\ldotp \mu \in \text{NC refl}.\supset :\nu \in \text{NC induct}.\supset _{\nu }.\mu >\nu\)

**Status.** proved (reading): convention Infin T, as in ✱124·252 (`InfinAx X` for the type of the apparent variable `ν`). -/
theorem pm124_26 {α X : Type*} (hX : InfinAx X) {μ : Set (Set α)} :
    μ ∈ NCrefl → ∀ ν : Set (Set X), ν ∈ NCinduct → μ >ᶜ ν := by
  rintro ⟨ρ, hρ, rfl⟩ ν hν
  have : Infinite X := infinAx_iff_infinite.1 hX
  obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hν
  exact infinite_cardGt_cardN (clsRefl_iff.1 hρ) (cardN_nonempty_of_infinite k)

/-- ✱124·27. \(\vdash .\text{NC refl}\cap \text{NC induct}=\Lambda \quad[*124·26.*117·42]\) -/
theorem pm124_27 {α : Type*} : (NCrefl : Set (Set (Set α))) ∩ NCinduct = Λ := by
  rw [Null_eq_empty]
  ext μ
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨ρ, hρ, rfl⟩ h
  rcases NCinduct_cases h with ⟨A, hA, he⟩ | ⟨-, he⟩
  · obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 he)
    have : Finite A := hA.to_subtype
    exact clsRefl_iff.1 hρ (Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm))
  · exact n₀c_ne_empty ρ he

/-- ✱124·271. \(\vdash .\text{Cls refl} \cap \text{Cls induct}=\Lambda\) -/
theorem pm124_271 {α : Type*} : (ClsRefl : Set (Set α)) ∩ ClsInduct = Λ := by
  rw [Null_eq_empty]
  ext ρ
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun h hi => clsRefl_iff.1 h (mem_ClsInduct.1 hi)

/-- ✱124·28. \(\vdash :\rho \in \text{Cls refl}.\equiv .\text{N}_{0}\text{c}ʻ\rho \in \text{NC refl}.\equiv .\text{Nc}ʻ\rho \in \text{NC refl}\)

**Status.** proved (reading): by the Df ✱124·021 `Nc'ρ ∈ NC refl` is read `N₀c'ρ ∈ NC refl`, so the second equivalence is the identity of the two readings. -/
theorem pm124_28 {α : Type*} {ρ : Set α} :
    (ρ ∈ ClsRefl ↔ n₀c ρ ∈ NCrefl) ∧ (n₀c ρ ∈ NCrefl ↔ n₀c ρ ∈ NCrefl) := by
  refine ⟨⟨fun h => ⟨ρ, h, rfl⟩, ?_⟩, Iff.rfl⟩
  rintro ⟨σ, hσ, he⟩
  exact pm124_18 ⟨hσ, sm_symm (n₀c_eq_n₀c_iff.1 he)⟩

/-- ✱124·29. \(\vdash .sʻ\text{NC refl}=\text{Cls refl}\) -/
theorem pm124_29 {α : Type*} : sumCls (NCrefl : Set (Set (Set α))) = ClsRefl := by
  ext ρ
  constructor
  · rintro ⟨μ, ⟨σ, hσ, rfl⟩, hρ⟩
    exact pm124_18 ⟨hσ, sm_symm (mem_n₀c.1 hρ)⟩
  · intro h
    exact ⟨n₀c ρ, ⟨ρ, h, rfl⟩, self_mem_n₀c ρ⟩

/-- ✱124·3. \[\begin{align}\vdash \colon\colon \exists !\aleph _0.\supset \colon\ldotp \mu <\aleph _0.\lor.\mu \geq \aleph _0:\equiv .\mu \in &\text{NC induct}\cup \text{NC refl}\\ &[*123·45.*124·23]\end{align}\]

The hypothesis `∃!ℵ₀` and the `ℵ₀`s of the inequalities are in a type `α` (as in ✱123·43);
`μ` is a real variable of a type `β`, and `NC induct ∪ NC refl` is in its type.

**Status.** proved (reading): convention Infin T (Prefatory Statement, VI): `NC induct`, in the type `β` of `μ`, is taken with `InfinAx β` (in a finite type `Λ ∈ NC induct` is neither `< ℵ₀` nor `≥ ℵ₀`). -/
theorem pm124_3 {α β : Type*} (hβ : InfinAx β) {μ : Set (Set β)} :
    (aleph0 : Set (Set α)).Nonempty →
      (μ <ᶜ (aleph0 : Set (Set α)) ∨ μ ≥ᶜ (aleph0 : Set (Set α)) ↔ μ ∈ NCinduct ∪ NCrefl) := by
  intro h
  constructor
  · rintro (hlt | hge)
    · exact Or.inl ((pm123_45 hβ h).1.2 hlt)
    · exact Or.inr ((pm124_23 h).2 hge)
  · rintro (hi | hr)
    · exact Or.inl ((pm123_45 hβ h).1.1 hi)
    · exact Or.inr ((pm124_23 h).1 hr)

/-- ✱124·31. \(\vdash :\exists !\aleph _{0}.\supset .\text{spec}ʻ\aleph _{0}=\text{NC induct}\cup \text{NC refl} \quad[*124·3.*120·431]\)

**Status.** proved (reading): convention Infin T, as in ✱124·3. -/
theorem pm124_31 {α β : Type*} (hβ : InfinAx β) :
    (aleph0 : Set (Set α)).Nonempty →
      (spec (aleph0 : Set (Set α)) : Set (Set (Set β))) = NCinduct ∪ NCrefl := by
  intro h
  ext μ
  exact pm124_3 hβ h

/-- ✱124·33. \[\begin{align}\vdash \colon\ldotp \exists !\aleph _{0}.\supset :&\mu \in \text{NC}-\text{NC induct}-\text{NC refl}.\equiv .\\ &\mu \in \text{NC}.{\sim}(\mu <\aleph _{0}).{\sim}(\mu \geq \aleph _{0}) \quad[*124·3.\text{Transp}]\end{align}\]

The two occurrences of `NC` are in one type (converse domain `δ`).

**Status.** proved (reading): convention Infin T, as in ✱124·3. -/
theorem pm124_33 {α β δ : Type*} (hβ : InfinAx β) {μ : Set (Set β)} :
    (aleph0 : Set (Set α)).Nonempty →
      (μ ∈ (NC δ \ NCinduct) \ NCrefl ↔
        (μ ∈ NC δ ∧ ¬ μ <ᶜ (aleph0 : Set (Set α))) ∧ ¬ μ ≥ᶜ (aleph0 : Set (Set α))) := by
  intro h
  have h3 := pm124_3 (μ := μ) hβ h
  constructor
  · rintro ⟨⟨hNC, hi⟩, hr⟩
    exact ⟨⟨hNC, fun hlt => (h3.1 (Or.inl hlt)).elim hi hr⟩, fun hge => (h3.1 (Or.inr hge)).elim hi hr⟩
  · rintro ⟨⟨hNC, hlt⟩, hge⟩
    exact ⟨⟨hNC, fun hi => (h3.2 (Or.inl hi)).elim hlt hge⟩, fun hr => (h3.2 (Or.inr hr)).elim hlt hge⟩

/-- ✱124·34. \[\begin{align}\vdash \colon\colon \exists !\aleph _{0}.\supset \colon\ldotp \alpha {\sim}\in &(\text{Cls induct} \cup \text{Cls refl}).\equiv :\\ &{\sim}(\exists \gamma ):\gamma \in \aleph _{0}:\alpha \subset \gamma .\lor.\gamma \subset \alpha\end{align}\]

The hypothesis `∃!ℵ₀` and `γ ∈ ℵ₀` are in the type of `α` (`α ⊂ γ` identifies the types).
In Lean every class is inductive or reflexive, and both sides are false. -/
theorem pm124_34 {β : Type*} {A : Set β} :
    (aleph0 : Set (Set β)).Nonempty →
      (A ∉ ClsInduct ∪ ClsRefl ↔ ¬ ∃ G, G ∈ aleph0 ∧ (A ⊆ G ∨ G ⊆ A)) := by
  rintro ⟨B, hB⟩
  constructor
  · intro h
    exfalso
    apply h
    by_cases hf : A.Finite
    · exact Or.inl (mem_ClsInduct.2 hf)
    · exact Or.inr (clsRefl_iff.2 hf)
  · intro h
    exfalso
    apply h
    by_cases hf : A.Finite
    · exact ⟨A ∪ B, pm123_46 ⟨mem_ClsInduct.2 hf, hB⟩, Or.inl Set.subset_union_left⟩
    · obtain ⟨C, hC, hCA⟩ := exists_aleph0_sub hf
      exact ⟨C, hC, Or.inr hCA⟩

/-- ✱124·4. \[\begin{align}&\vdash \colon\ldotp \mu \in \text{NC mult}.\equiv :\mu \in \text{NC}:\kappa \in \mu \cap \text{Cls ex}^{2}\, \text{excl}.\supset _{\kappa }.\exists !{\in}_{\Delta}ʻ\kappa\\ &[(*124·03)]\end{align}\] -/
theorem pm124_4 {α β : Type*} {μ : Set (Set (Set α))} :
    μ ∈ NCmult β ↔ μ ∈ NC β ∧ ∀ K, K ∈ μ ∩ ClsEx2excl → (sel memRel K).Nonempty := Iff.rfl

/-- ✱124·41. \(\vdash .\text{NC induct}\subset \text{NC mult}\quad[*120·62 . *124·4]\)

`NC induct` is that of the cardinals of classes of classes of `α`-things (members of
`NC mult`); `NC` in `NC mult` is taken with the converse domain of PM's ✱123·36 (two types above
the members of the classes counted).

**Status.** proved (reading): the converse-domain type of `NC` in `NC mult`, which PM leaves undetermined, is taken as in ✱123·36 (in a type of too few classes, `Λ` and the large inductive cardinals are not in `NC`). -/
theorem pm124_41 {α : Type*} :
    (NCinduct : Set (Set (Set (Set α)))) ⊆ NCmult (Set (Set (Set α))) := by
  intro μ hμ
  refine ⟨?_, fun K hK => sel_nonempty_of fun A hA => ?_⟩
  · rcases NCinduct_cases hμ with ⟨C, -, rfl⟩ | ⟨-, rfl⟩
    · refine ⟨(fun c : Set α => ({{c}} : Set (Set (Set α)))) '' C, ?_⟩
      rw [n₀c_eq_nc]
      apply nc_eq_nc_of_sm
      exact sm_iff_nonempty_equiv.2 ⟨Equiv.Set.image _ C
        (fun a b h => Set.singleton_injective (Set.singleton_injective h))⟩
    · exact ⟨Set.univ, nc_univ_eq_empty.symm⟩
  · obtain ⟨-, -, hΛ⟩ := hK
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact hΛ (show memRel Λ K by rw [Null_eq_empty]; exact hA)

/-- ✱124·51. \[\begin{align}\vdash :\rho {\sim}\in &\text{Cls induct}.Q=(\cap \text{Cl}ʻ\rho )\mid N\mid \text{Cnv}ʻ(\cap \text{Cl}ʻ\rho ).\supset .\\ &Q\in \text{Prog}.\text{D}ʻQ\subset \text{Cl}ʻ\text{Cl}ʻ\rho .\text{D}ʻQ=(\cap \text{Cl}ʻ\rho )ʻʻ\text{NC induct}\end{align}\]

`∩Cl'ρ` is the relation `opR (· ∩ ·) (cl ρ)` of `μ ∩ Cl'ρ` to `μ` (✱38·02 with `♀ = ∩`), and
`Cnv'(∩Cl'ρ)` its converse; `N` is `Nsucc` (Dft ✱123·02) on the cardinals of classes of
`α`-things. -/
theorem pm124_51 {α : Type*} {ρ : Set α} {Q : Set (Set α) → Set (Set α) → Prop} :
    ρ ∉ ClsInduct ∧ Q = opR (fun μ C : Set (Set α) => μ ∩ C) (cl ρ) ⨾ Nsucc ⨾
        (opR (fun μ C : Set (Set α) => μ ∩ C) (cl ρ))˘ →
      (Q ∈ Prog ∧ dom Q ⊆ cl (cl ρ)) ∧
        dom Q = opR (fun μ C : Set (Set α) => μ ∩ C) (cl ρ) ʻʻ NCinduct := by
  rintro ⟨hρ, rfl⟩
  rw [mem_ClsInduct] at hρ
  have hρ' : ρ.Infinite := hρ
  have : Infinite ρ := Set.infinite_coe_iff.2 hρ'
  have : Infinite α := Infinite.of_injective (Subtype.val : ρ → α) Subtype.val_injective
  obtain ⟨h, hh⟩ : ∃ h : ℕ → Set (Set α), ∀ k, h k = cardN α k ∩ cl ρ := ⟨_, fun _ => rfl⟩
  have hne : ∀ k, (h k).Nonempty := fun k => by
    obtain ⟨t, hts, htf, htk⟩ := hρ'.exists_subset_ncard_eq k
    exact ⟨t, by rw [hh]; exact ⟨⟨htf, htk⟩, hts⟩⟩
  have hinj : Function.Injective h := fun m n hmn => by
    obtain ⟨t, ht⟩ := hne m
    have ht' : t ∈ h n := by rw [← hmn]; exact ht
    rw [hh] at ht ht'
    exact ht.1.2.symm.trans ht'.1.2
  have hQ : opR (fun μ C : Set (Set α) => μ ∩ C) (cl ρ) ⨾ Nsucc ⨾
      (opR (fun μ C : Set (Set α) => μ ∩ C) (cl ρ))˘ = SeqRel h := by
    rw [nsucc_eq_seqRel]
    funext X Y
    apply propext
    constructor
    · rintro ⟨ν, ⟨μ, hXμ, k, rfl, rfl⟩, hνY⟩
      exact ⟨k, by rw [hh]; exact hXμ, by rw [hh]; exact hνY⟩
    · rintro ⟨k, rfl, rfl⟩
      exact ⟨cardN α (k + 1), ⟨cardN α k, hh k, k, rfl, rfl⟩, hh (k + 1)⟩
  rw [hQ, dom_seqRel]
  refine ⟨⟨seqRel_mem_prog hinj, ?_⟩, ?_⟩
  · rintro _ ⟨k, rfl⟩ t ht
    rw [hh] at ht
    exact ht.2
  · ext X
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨cardN α k, cardN_mem_NCinduct k, hh k⟩
    · rintro ⟨μ, hμ, hX⟩
      obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hμ
      exact ⟨k, (hh k).trans hX.symm⟩

/-- ✱124·511. \[\begin{align}\vdash :\rho {\sim}\in &\text{Cls induct}.\supset .\\ &\text{Cl}ʻ\text{Cl}ʻ\rho \in \text{Cls refl}.(\cap \text{Cl}ʻ\rho )ʻʻ\text{NC induct}\in \aleph _{0}\cap \text{Cls}^{2} \text{excl}\\ &[*124·51·15. *120·491.*100·43]\end{align}\]

`ℵ₀ ∩ Cls² excl` at the type of classes of classes of `α`-things. -/
theorem pm124_511 {α : Type*} {ρ : Set α} :
    ρ ∉ ClsInduct →
      cl (cl ρ) ∈ ClsRefl ∧
        opR (fun μ C : Set (Set α) => μ ∩ C) (cl ρ) ʻʻ NCinduct ∈ aleph0 ∩ Cls2excl := by
  intro hρ
  obtain ⟨⟨hQ, hsub⟩, hdom⟩ := pm124_51 (Q := _) ⟨hρ, rfl⟩
  have hD := pm123_101 hQ
  rw [hdom] at hD hsub
  refine ⟨clsRefl_iff.2 ((infinite_of_aleph0 hD).mono hsub), hD, ?_⟩
  rintro A B ⟨⟨⟨μ, hμ, rfl⟩, ⟨ν, hν, rfl⟩⟩, hne⟩
  obtain ⟨m, rfl⟩ := mem_NCinduct_iff_cardN.1 hμ
  obtain ⟨n, rfl⟩ := mem_NCinduct_iff_cardN.1 hν
  rw [Null_eq_empty]
  refine Set.eq_empty_iff_forall_notMem.2 fun t ht => hne ?_
  obtain ⟨⟨ht1, -⟩, ⟨ht2, -⟩⟩ := ht
  show cardN α m ∩ cl ρ = cardN α n ∩ cl ρ
  rw [show m = n from ht1.2.symm.trans ht2.2]

/-- ✱124·512. \[\begin{align}\vdash :P\in {\in}_{\Delta}ʻ(\cap \text{Cl}ʻ\rho )ʻʻ&\text{NC induct}.\supset .\\ &\text{D}ʻP\in \aleph _{0}\cap \text{Cl}ʻ\text{Cl}ʻ\rho .\text{D}ʻP\subset \text{Cls induct}\end{align}\]

`P` is a selector (✱80) from the class of classes `(∩Cl'ρ)''NC induct`. -/
theorem pm124_512 {α : Type*} {ρ : Set α} {P : Set α → Set (Set α) → Prop} :
    P ∈ sel memRel (opR (fun μ C : Set (Set α) => μ ∩ C) (cl ρ) ʻʻ NCinduct) →
      dom P ∈ aleph0 ∩ cl (cl ρ) ∧ dom P ⊆ ClsInduct := by
  classical
  rintro ⟨⟨h1, h2⟩, h3⟩
  have hcod : opR (fun μ C : Set (Set α) => μ ∩ C) (cl ρ) ʻʻ NCinduct = codom P := h3
  have hone := mem_arrow_one_Cls.1 h1
  have hmem : ∀ D C, P D C → ∃ k, C = cardN α k ∩ cl ρ := fun D C hDC => by
    have : C ∈ codom P := ⟨D, hDC⟩
    rw [← hcod] at this
    obtain ⟨μ, hμ, hC⟩ := this
    obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hμ
    exact ⟨k, hC⟩
  have hex : ∀ k, ∃ D, P D (cardN α k ∩ cl ρ) := fun k => by
    have : cardN α k ∩ cl ρ ∈ codom P := by rw [← hcod]; exact ⟨_, cardN_mem_NCinduct k, rfl⟩
    exact this
  choose D hD using hex
  have hDk : ∀ k, D k ∈ cardN α k ∩ cl ρ := fun k => h2 _ _ (hD k)
  have hDinj : Function.Injective D := fun m n hmn => by
    have := (hDk m).1.2
    rw [hmn, (hDk n).1.2] at this
    exact this.symm
  have hdom : dom P = Set.range D := by
    ext E
    constructor
    · rintro ⟨C, hEC⟩
      obtain ⟨k, rfl⟩ := hmem E C hEC
      exact ⟨k, hone _ _ _ ⟨hD k, hEC⟩⟩
    · rintro ⟨k, rfl⟩
      exact ⟨_, hD k⟩
  rw [hdom]
  refine ⟨⟨mem_aleph0_iff.2 ⟨D, hDinj, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨k, rfl⟩
    exact (hDk k).2
  · rintro _ ⟨k, rfl⟩
    exact mem_ClsInduct.2 (hDk k).1.1

/-- ✱124·513. \(\vdash :\exists !{\in}_{\Delta}ʻ(\cap \text{Cl}ʻ\rho )ʻʻ\text{NC induct}.\supset .\text{Cl}ʻ\rho \in \text{Cls refl} \quad[*124·512·15]\) -/
theorem pm124_513 {α : Type*} {ρ : Set α} :
    (sel memRel (opR (fun μ C : Set (Set α) => μ ∩ C) (cl ρ) ʻʻ NCinduct)).Nonempty →
      cl ρ ∈ ClsRefl := by
  rintro ⟨P, hP⟩
  obtain ⟨⟨hD, hsub⟩, -⟩ := pm124_512 hP
  exact clsRefl_iff.2 ((infinite_of_aleph0 hD).mono hsub)

/-- ✱124·514. \[\begin{align}\vdash \colon\ldotp \aleph _{0}\in \text{NC mult}.\supset :\rho {\sim}\in &\text{Cls induct}.\supset .\text{Cl}ʻ\rho \in \text{Cls refl}\\ &[*124·511·513·4]\end{align}\]

`ℵ₀ ∈ NC mult` is taken at the type of PM's demonstration (`(∩Cl'ρ)''NC induct ∈ ℵ₀`, classes
of classes of classes of `α`-things), with `NC`'s converse-domain type `β` free. -/
theorem pm124_514 {α β : Type*} {ρ : Set α} :
    (aleph0 : Set (Set (Set (Set α)))) ∈ NCmult β → (ρ ∉ ClsInduct → cl ρ ∈ ClsRefl) := by
  intro _ hρ
  exact clsRefl_iff.2 (infinite_cl (fun h => hρ (mem_ClsInduct.2 h)))

/-- ✱124·52. \[\begin{align}&\vdash \colon\ldotp R\in \text{Prog}.\sigma = \hat{\beta} \{(\exists \gamma ).\gamma \in \text{D}ʻR.\beta = \gamma -sʻ\overrightarrow{R}_{\text{po}}ʻ\gamma .\exists !\beta \}.\supset :\\ &\sigma \in \text{Cls ex}^{2} \text{excl}:\gamma ,\delta \in \text{D}ʻR.\gamma \neq \delta .\supset .(\gamma -sʻ\overrightarrow{R}_{\text{po}}ʻ\gamma )\cap (\delta -sʻ\overrightarrow{R}_{\text{po}}ʻ\delta ) = \Lambda \end{align}\]

`R` is a progression of classes (`R : Set α → Set α → Prop`); `γ − s'R⃗_po'γ` is
`G \ sumCls (refs (po R) G)` (the terms of `γ` not in any earlier member of `D'R`). In the
second conjunct `γ`, `δ` are real variables (`G`, `D`). -/
theorem pm124_52 {α : Type*} {R : Set α → Set α → Prop} {σ : Set (Set α)} {G D : Set α} :
    R ∈ Prog ∧ σ = {B | ∃ G', (G' ∈ dom R ∧ B = G' \ sumCls (refs (po R) G')) ∧ B.Nonempty} →
      σ ∈ ClsEx2excl ∧ (Mem2 G D (dom R) ∧ G ≠ D →
        (G \ sumCls (refs (po R) G)) ∩ (D \ sumCls (refs (po R) D)) = Λ) := by
  rintro ⟨h, rfl⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  have key : ∀ G D : Set α, Mem2 G D (dom (SeqRel f)) ∧ G ≠ D →
      (G \ sumCls (refs (po (SeqRel f)) G)) ∩ (D \ sumCls (refs (po (SeqRel f)) D)) = Λ := by
    rintro G D ⟨⟨hG, hD⟩, hne⟩
    rw [dom_seqRel] at hG hD
    obtain ⟨m, rfl⟩ := hG
    obtain ⟨n, rfl⟩ := hD
    rw [Null_eq_empty]
    rcases lt_trichotomy m n with hlt | rfl | hlt
    · exact newPart_disjoint hf hlt
    · exact absurd rfl hne
    · rw [Set.inter_comm]; exact newPart_disjoint hf hlt
  refine ⟨⟨?_, ?_⟩, key G D⟩
  · rintro A B ⟨⟨⟨G', ⟨hG', rfl⟩, hA⟩, ⟨D', ⟨hD', rfl⟩, hB⟩⟩, hne⟩
    exact key G' D' ⟨⟨hG', hD'⟩, fun e => hne (by rw [e])⟩
  · rintro ⟨G', -, hne⟩
    rw [Null_eq_empty] at hne
    exact Set.not_nonempty_empty hne

/-- ✱124·521. \(\vdash :\text{Hp}*124·52.\pi =\hat{\gamma}\{\gamma \in \text{D}ʻR.\exists !\gamma -sʻ\overrightarrow{R}_{\text{po}}ʻ\gamma \}.\supset .\sigma \text{ sm }\pi\) -/
theorem pm124_521 {α : Type*} {R : Set α → Set α → Prop} {σ π : Set (Set α)} :
    (R ∈ Prog ∧ σ = {B | ∃ G', (G' ∈ dom R ∧ B = G' \ sumCls (refs (po R) G')) ∧ B.Nonempty}) ∧
      π = {G | G ∈ dom R ∧ (G \ sumCls (refs (po R) G)).Nonempty} → sm σ π := by
  rintro ⟨⟨h, rfl⟩, rfl⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  refine sm_symm (sm_iff_nonempty_equiv.2 ⟨Equiv.ofBijective
    (fun G => ⟨newPart (SeqRel f) G.1, G.1, ⟨G.2.1, rfl⟩, G.2.2⟩) ⟨?_, ?_⟩⟩)
  · rintro ⟨G, hG, hGn⟩ ⟨G', hG', hG'n⟩ he
    have he' : newPart (SeqRel f) G = newPart (SeqRel f) G' := congrArg Subtype.val he
    apply Subtype.ext
    show G = G'
    rw [dom_seqRel] at hG hG'
    obtain ⟨m, rfl⟩ := hG
    obtain ⟨n, rfl⟩ := hG'
    rcases lt_trichotomy m n with hlt | rfl | hlt
    · have := newPart_disjoint hf hlt
      rw [he', Set.inter_self] at this
      exact absurd this (hG'n.ne_empty)
    · rfl
    · have := newPart_disjoint hf hlt
      rw [← he', Set.inter_self] at this
      exact absurd this (hGn.ne_empty)
  · rintro ⟨B, G, ⟨hG, rfl⟩, hne⟩
    exact ⟨⟨G, hG, hne⟩, rfl⟩

/-- ✱124·53. \(\vdash :R\in \text{Prog}.\supset .sʻ\text{D}ʻR{\sim}\in \text{Cls induct} \quad[*120·75.*122·37]\) -/
theorem pm124_53 {α : Type*} {R : Set α → Set α → Prop} : R ∈ Prog → sumCls (dom R) ∉ ClsInduct := by
  intro h hfin
  have hinf : (dom R).Infinite := fun hd => (pm122_37 h).1 (mem_ClsInduct.2 hd)
  exact sumCls_infinite_of_infinite hinf (mem_ClsInduct.1 hfin)

/-- ✱124·532. \[\begin{align}&\vdash :R\in \text{Prog}.\text{D}ʻR\subset \text{Cls induct}.\supset .\exists !sʻ\text{D}ʻR-sʻ\overrightarrow{R}_{*}ʻ\gamma \\ &[*124·53·531.*120·481.\text{Transp}]\end{align}\]

`γ` is a real variable (`G`). -/
theorem pm124_532 {α : Type*} {R : Set α → Set α → Prop} {G : Set α} :
    R ∈ Prog ∧ dom R ⊆ ClsInduct → (sumCls (dom R) \ sumCls (refs (anc R) G)).Nonempty := by
  rintro ⟨h, hsub⟩
  have hinf : (sumCls (dom R)).Infinite := fun hfin => pm124_53 h (mem_ClsInduct.2 hfin)
  have hfin : (sumCls (refs (anc R) G)).Finite := by
    refine sumCls_finite (mem_ClsInduct.1 (pm122_38 h)) fun A hA => ?_
    have hA' : A ∈ fld R := fld_of_anc_left (show anc R A G from hA)
    rw [(pm122_141 h).2] at hA'
    exact mem_ClsInduct.1 (hsub hA')
  exact (hinf.sdiff hfin).nonempty

/-- ✱124·533. \[\begin{align}\vdash :R\in \text{Prog}.\text{D}ʻR\subset \text{Cls induct}.\gamma \in &\text{D}ʻR.\supset .\\ &(\exists \beta ).\gamma R_{\text{po}}\beta .\exists !\beta -sʻ\overrightarrow{R}_{\text{po}}ʻ\beta\end{align}\] -/
theorem pm124_533 {α : Type*} {R : Set α → Set α → Prop} {G : Set α} :
    (R ∈ Prog ∧ dom R ⊆ ClsInduct) ∧ G ∈ dom R →
      ∃ B, po R G B ∧ (B \ sumCls (refs (po R) B)).Nonempty := by
  classical
  rintro ⟨⟨h, hsub⟩, hG⟩
  obtain ⟨x, ⟨B', hB', hxB'⟩, hx⟩ := pm124_532 (G := G) ⟨h, hsub⟩
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  rw [dom_seqRel] at hG hB'
  obtain ⟨m, rfl⟩ := hG
  have hex : ∃ n, x ∈ f n := let ⟨n, e⟩ := hB'; ⟨n, e ▸ hxB'⟩
  have hNm : m < Nat.find hex := by
    by_contra hle
    exact hx ⟨f (Nat.find hex), (anc_seqRel' hf).2 (by omega), Nat.find_spec hex⟩
  refine ⟨f (Nat.find hex), (po_seqRel' hf).2 hNm, x, Nat.find_spec hex, ?_⟩
  rintro ⟨A, hA, hxA⟩
  obtain ⟨a, b, hab, rfl, hb⟩ := (po_seqRel hf).1 hA
  rw [← hf hb] at hab
  exact Nat.find_min hex hab hxA

/-- ✱124·534. \[\begin{align}\vdash :R\in \text{Prog}.\text{D}ʻR\subset &\text{Cls induct}.\\ &\pi =\hat{\gamma}\{\gamma \in \text{D}ʻR.\exists !\gamma -sʻ\overrightarrow{R}_{\text{po}}ʻ\gamma\}.\supset .\pi \in \aleph _{0}\end{align}\] -/
theorem pm124_534 {α : Type*} {R : Set α → Set α → Prop} {π : Set (Set α)} :
    (R ∈ Prog ∧ dom R ⊆ ClsInduct) ∧
      π = {G | G ∈ dom R ∧ (G \ sumCls (refs (po R) G)).Nonempty} → π ∈ aleph0 := by
  rintro ⟨⟨h, hsub⟩, rfl⟩
  have hR := h
  obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 h
  refine aleph0_of_infinite_sub_range (f := f) (fun G hG => by rw [← dom_seqRel]; exact hG.1) ?_
  intro hfin
  have hfin' := hfin.preimage (fun a _ b _ h => hf h)
  obtain ⟨B, hB, hBn⟩ := pm124_533 ⟨⟨hR, hsub⟩, (⟨_, seqRel_apply f 0⟩ : f 0 ∈ dom (SeqRel f))⟩
  obtain ⟨-, k, -, -, rfl⟩ := (po_seqRel hf).1 hB
  obtain ⟨M, hM, hMmax⟩ := Set.Finite.exists_maximal hfin' ⟨k, ⟨_, seqRel_apply f k⟩, hBn⟩
  obtain ⟨B', hB', hB'n⟩ := pm124_533 ⟨⟨hR, hsub⟩, (⟨_, seqRel_apply f M⟩ : f M ∈ dom (SeqRel f))⟩
  obtain ⟨a, n, han, ha, rfl⟩ := (po_seqRel hf).1 hB'
  rw [← hf ha] at han
  have := hMmax (show n ∈ f ⁻¹' _ from ⟨⟨_, seqRel_apply f n⟩, hB'n⟩) (le_of_lt han)
  omega

/-- ✱124·535. \[\begin{align}\vdash :R\in \text{Prog}.&\text{D}ʻR\subset \text{Cls induct}.\\ &\sigma =\hat{\beta}\{(\exists y).\gamma \in \text{D}ʻR.\beta =\gamma -sʻ\overrightarrow{R}_{\text{po}}ʻ\gamma .\exists !\beta\}.\supset .\sigma \in \aleph _{0}\\ &[*124·534·521.*123·321]\end{align}\]

The e-text prints `(∃y)` for `(∃γ)` in the definition of `σ` (as ✱124·52·536 show).

**Status.** proved (reading): transcription error of the e-text: the apparent variable of `σ`'s definition is `γ`, not `y`. -/
theorem pm124_535 {α : Type*} {R : Set α → Set α → Prop} {σ : Set (Set α)} :
    (R ∈ Prog ∧ dom R ⊆ ClsInduct) ∧
      σ = {B | ∃ G', (G' ∈ dom R ∧ B = G' \ sumCls (refs (po R) G')) ∧ B.Nonempty} →
      σ ∈ aleph0 := by
  rintro ⟨hR, rfl⟩
  exact aleph0_of_sm (pm124_534 ⟨hR, rfl⟩) (sm_symm (pm124_521 ⟨⟨hR.1, rfl⟩, rfl⟩))

/-- ✱124·536. \[\begin{align}\vdash :R\in \text{Prog}.\text{D}ʻR\subset &\text{Cls induct}.\\ &\sigma =\hat{\beta} \{(\exists \gamma ).\gamma \in \text{D}ʻR.\beta =\gamma -sʻ\overrightarrow{R}_{\text{po}}ʻ\gamma .\exists !\beta \}.\\ &S\in {\in}_{\Delta}ʻ\sigma .\supset .\text{D}ʻS\in \aleph _{0}.\text{D}ʻS\subset sʻ\text{D}ʻR\end{align}\] -/
theorem pm124_536 {α : Type*} {R : Set α → Set α → Prop} {σ : Set (Set α)} {S : α → Set α → Prop} :
    ((R ∈ Prog ∧ dom R ⊆ ClsInduct) ∧
      σ = {B | ∃ G', (G' ∈ dom R ∧ B = G' \ sumCls (refs (po R) G')) ∧ B.Nonempty}) ∧
      S ∈ sel memRel σ → dom S ∈ aleph0 ∧ dom S ⊆ sumCls (dom R) := by
  classical
  rintro ⟨⟨hR, rfl⟩, ⟨h1, h2⟩, h3⟩
  have hσ := pm124_535 (σ := _) ⟨hR, rfl⟩
  have hexcl := (pm124_52 (G := ∅) (D := ∅) ⟨hR.1, rfl⟩).1.1
  have hcod : {B | ∃ G', (G' ∈ dom R ∧ B = G' \ sumCls (refs (po R) G')) ∧ B.Nonempty} =
    codom S := h3
  have hone := mem_arrow_one_Cls.1 h1
  have hex : ∀ B : ↥{B | ∃ G', (G' ∈ dom R ∧ B = G' \ sumCls (refs (po R) G')) ∧ B.Nonempty},
      ∃ x, S x B := fun B => by
    have : (B : Set α) ∈ codom S := by rw [← hcod]; exact B.2
    exact this
  choose g hg using hex
  have hdom : dom S = Set.range g := by
    ext x
    constructor
    · rintro ⟨B, hxB⟩
      have hB : B ∈ codom S := ⟨x, hxB⟩
      rw [← hcod] at hB
      exact ⟨⟨B, hB⟩, hone _ _ _ ⟨hg ⟨B, hB⟩, hxB⟩⟩
    · rintro ⟨B, rfl⟩
      exact ⟨_, hg B⟩
  have hginj : Function.Injective g := by
    intro B B' he
    by_contra hne
    have hx1 : g B ∈ (B : Set α) := h2 _ _ (hg B)
    have hx2 : g B ∈ (B' : Set α) := by rw [he]; exact h2 _ _ (hg B')
    have := hexcl B B' ⟨⟨B.2, B'.2⟩, fun e => hne (Subtype.ext e)⟩
    rw [Null_eq_empty] at this
    exact (Set.eq_empty_iff_forall_notMem.1 this) _ ⟨hx1, hx2⟩
  rw [hdom]
  refine ⟨aleph0_of_sm hσ (sm_iff_nonempty_equiv.2 ⟨Equiv.ofInjective g hginj⟩), ?_⟩
  rintro _ ⟨B, rfl⟩
  obtain ⟨G', ⟨hG', hB⟩, -⟩ := B.2
  have hx : g B ∈ (B : Set α) := h2 _ _ (hg B)
  rw [hB] at hx
  exact ⟨G', hG', hx.1⟩

/-- ✱124·54. \(\vdash :\aleph _{0}\in \text{NC mult}.R\in \text{Prog}.\text{D}ʻR\subset \text{Cls induct}.\supset .\exists !\aleph _0\cap \text{Cl}ʻsʻ\text{D}ʻR\)

`ℵ₀ ∈ NC mult` is at the type of PM's demonstration (the class `σ` of classes of ✱124·536:
`ℵ₀` of classes of classes of `α`-things); the conclusion's `ℵ₀` is in the type of `s'D'R`. -/
theorem pm124_54 {α β : Type*} {R : Set α → Set α → Prop} :
    ((aleph0 : Set (Set (Set α))) ∈ NCmult β ∧ R ∈ Prog) ∧ dom R ⊆ ClsInduct →
      (aleph0 ∩ cl (sumCls (dom R))).Nonempty := by
  rintro ⟨⟨-, h⟩, -⟩
  have hinf : (sumCls (dom R)).Infinite := fun hfin => pm124_53 h (mem_ClsInduct.2 hfin)
  obtain ⟨C, hC, hCs⟩ := exists_aleph0_sub hinf
  exact ⟨C, hC, hCs⟩

/-- ✱124·541. \[\begin{align}\vdash :\aleph _{0}\in \text{NC mult}.P\in {\in}_{\Delta}ʻ(\cap \text{Cl}ʻ\rho )ʻʻ&\text{NC induct}.\supset .\\ &\exists !\aleph _{0}\cap \text{Cl}ʻsʻ\text{D}ʻP.sʻ\text{D}ʻP\subset \rho\end{align}\]

`ℵ₀ ∈ NC mult` as in ✱124·54. -/
theorem pm124_541 {α β : Type*} {ρ : Set α} {P : Set α → Set (Set α) → Prop} :
    (aleph0 : Set (Set (Set α))) ∈ NCmult β ∧
        P ∈ sel memRel (opR (fun μ C : Set (Set α) => μ ∩ C) (cl ρ) ʻʻ NCinduct) →
      (aleph0 ∩ cl (sumCls (dom P))).Nonempty ∧ sumCls (dom P) ⊆ ρ := by
  rintro ⟨-, hP⟩
  obtain ⟨⟨hD, hsub⟩, -⟩ := pm124_512 hP
  have hinf : (sumCls (dom P)).Infinite := sumCls_infinite_of_infinite (infinite_of_aleph0 hD)
  obtain ⟨C, hC, hCs⟩ := exists_aleph0_sub hinf
  refine ⟨⟨C, hC, hCs⟩, ?_⟩
  rintro x ⟨A, hA, hxA⟩
  exact hsub hA hxA

/-- ✱124·55. \(\vdash :\aleph _{0}\in \text{NC mult}.\rho {\sim}\in \text{Cls induct}.\supset .\exists !\aleph _{0}\cap \text{Cl}ʻ\rho\)

`ℵ₀ ∈ NC mult` is at the type of PM's demonstration (`(∩Cl'ρ)''NC induct ∈ ℵ₀`), as in
✱124·514. -/
theorem pm124_55 {α β : Type*} {ρ : Set α} :
    (aleph0 : Set (Set (Set (Set α)))) ∈ NCmult β ∧ ρ ∉ ClsInduct → (aleph0 ∩ cl ρ).Nonempty := by
  rintro ⟨-, hρ⟩
  obtain ⟨C, hC, hCs⟩ := exists_aleph0_sub (fun h => hρ (mem_ClsInduct.2 h))
  exact ⟨C, hC, hCs⟩

/-- ✱124·56. \(\vdash :\aleph _{0}\in \text{NC mult}.\supset .-\text{Cls induct}=\text{Cls refl}.\text{N}_{0}\text{C}-\text{NC induct}=\text{NC refl}\)

`−Cls induct` is the complement `ClsInductᶜ`; the types are those of ✱124·55. -/
theorem pm124_56 {α β : Type*} :
    (aleph0 : Set (Set (Set (Set α)))) ∈ NCmult β →
      (ClsInduct : Set (Set α))ᶜ = ClsRefl ∧ (N₀C : Set (Set (Set α))) \ NCinduct = NCrefl := by
  intro _
  refine ⟨?_, ?_⟩
  · ext ρ
    rw [Set.mem_compl_iff, mem_ClsInduct, clsRefl_iff]
    rfl
  · ext μ
    constructor
    · rintro ⟨⟨ρ, rfl⟩, hi⟩
      exact ⟨ρ, clsRefl_iff.2 fun hfin => hi (n₀c_mem_NCinduct hfin), rfl⟩
    · rintro ⟨ρ, hρ, rfl⟩
      refine ⟨⟨ρ, rfl⟩, fun hi => ?_⟩
      have : n₀c ρ ∈ (NCrefl : Set (Set (Set α))) ∩ NCinduct := ⟨⟨ρ, hρ, rfl⟩, hi⟩
      rw [pm124_27, Null_eq_empty] at this
      exact this

/-- ✱124·57. \(\vdash :\mu \in \text{N}_{0}\text{C}-\text{NC induct}.\supset .2^{2^\mu }\in \text{NC refl} \quad[*124·511.*116·72]\)

`μ` is a real variable (type `α`); the `2`s are constants in types `V₁`, `V₂`; the inner
`2^μ`, an arithmetical component, has its own type `W`; `2^{2^μ} ∈ NC refl` is in a type `γ`.

**Status.** proved (reading): convention IIT (Prefatory Statement, II, IV) for the arithmetical components: the `2`s exist in their types and the actual type `W` of `2^μ` is adequate (`AdeqExp`); the logical occurrence `2^{2^μ}` is taken in a type `γ` adequate for it (`AdeqExp`), i.e. where the form has its stable truth-value (Prefatory Statement, I–II): in a type too small for `2^{2^μ}` it is `Λ ∉ NC refl`. -/
theorem pm124_57 {α V₁ V₂ W γ : Type*} (h1 : (two : Set (Set V₁)).Nonempty)
    (h2 : (two : Set (Set V₂)).Nonempty) {μ : Set (Set α)} (hW : AdeqExp W (two : Set (Set V₁)) μ)
    (hγ : AdeqExp γ (two : Set (Set V₂)) ((two : Set (Set V₁)) ^ᶜ μ : Set (Set W))) :
    μ ∈ N₀C \ NCinduct →
      ((two : Set (Set V₂)) ^ᶜ ((two : Set (Set V₁)) ^ᶜ μ : Set (Set W)) : Set (Set γ)) ∈ NCrefl := by
  rintro ⟨⟨A, rfl⟩, hi⟩
  have hA : A.Infinite := fun hfin => hi (n₀c_mem_NCinduct hfin)
  rw [two_eq_cardN] at h1 h2
  obtain ⟨T₁, hT₁⟩ := h1
  obtain ⟨T₂, hT₂⟩ := h2
  have hT₁ne : T₁.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hT₁.2]; omega)
  have hT₂ne : T₂.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hT₂.2]; omega)
  obtain ⟨Y, hY⟩ := AdeqExp_nc_nonempty hW T₁ A hT₁ne
  have hinner : ((two : Set (Set V₁)) ^ᶜ n₀c A : Set (Set W)) = n₀c Y := by
    rw [two_eq_cardN, cardN_eq_n₀c hT₁, n₀c_cardExp_n₀c, nc_eq_n₀c_of_mem hY]
  rw [hinner] at hγ ⊢
  obtain ⟨Z, hZ⟩ := AdeqExp_nc_nonempty hγ T₂ Y hT₂ne
  rw [two_eq_cardN, cardN_eq_n₀c hT₂, n₀c_cardExp_n₀c, nc_eq_n₀c_of_mem hZ]
  refine ⟨Z, clsRefl_iff.2 ?_, rfl⟩
  obtain ⟨eZ⟩ := sm_iff_nonempty_equiv.1 hZ
  obtain ⟨eY⟩ := sm_iff_nonempty_equiv.1 hY
  have : Infinite A := Set.infinite_coe_iff.2 hA
  have hAT : Infinite (A → T₁) := infinite_fun_two hT₁
  have hYi : Infinite Y := Infinite.of_injective (fun k => eY.symm ((clsExpEquiv T₁ A).symm k))
    (eY.symm.injective.comp (clsExpEquiv T₁ A).symm.injective)
  have hYT : Infinite (Y → T₂) := infinite_fun_two hT₂
  have hZi : Infinite Z := Infinite.of_injective (fun k => eZ.symm ((clsExpEquiv T₂ Y).symm k))
    (eZ.symm.injective.comp (clsExpEquiv T₂ Y).symm.injective)
  exact Set.infinite_coe_iff.1 hZi

/-- ✱124·58. \(\vdash \colon\ldotp 2^\mu \in \text{NC refl}.\supset _{\mu }.\mu \in \text{NC refl}:\supset .\text{N}_{0}\text{C}-\text{NC induct}=\text{NC refl}\)

`μ` is an apparent variable of a type `α`; the `2` is in a type `V`, `2^μ` (with `NC refl`) in a
type `γ`; the conclusion is in the type of `μ`. In Lean the conclusion holds outright. -/
theorem pm124_58 {α V γ : Type*} :
    (∀ μ : Set (Set α), ((two : Set (Set V)) ^ᶜ μ : Set (Set γ)) ∈ NCrefl → μ ∈ NCrefl) →
      (N₀C : Set (Set (Set α))) \ NCinduct = NCrefl := by
  intro _
  ext μ
  constructor
  · rintro ⟨⟨ρ, rfl⟩, hi⟩
    exact ⟨ρ, clsRefl_iff.2 fun hfin => hi (n₀c_mem_NCinduct hfin), rfl⟩
  · rintro ⟨ρ, hρ, rfl⟩
    refine ⟨⟨ρ, rfl⟩, fun hi => ?_⟩
    have : n₀c ρ ∈ (NCrefl : Set (Set (Set α))) ∩ NCinduct := ⟨⟨ρ, hρ, rfl⟩, hi⟩
    rw [pm124_27, Null_eq_empty] at this
    exact this

/-- ✱124·6. \(\vdash :\rho {\sim}\in \text{Cls induct}.\equiv .\text{Cl}ʻ\text{Cl}ʻ\rho \in \text{Cls refl}\) -/
theorem pm124_6 {α : Type*} {ρ : Set α} : ρ ∉ ClsInduct ↔ cl (cl ρ) ∈ ClsRefl := by
  rw [mem_ClsInduct, clsRefl_iff]
  constructor
  · intro h
    exact infinite_cl (infinite_cl h)
  · intro h hfin
    exact h (finite_cl (finite_cl hfin))

/-- ✱124·61. \(\vdash \colon\ldotp \aleph _{0}\in \text{NC mult}.\supset :\rho \in \text{Cls refl}.\equiv .\text{Cl}ʻ\rho \in \text{Cls refl}.\equiv .\text{Cl}ʻ\text{Cl}ʻ\rho \in \text{Cls refl}\)

`ℵ₀ ∈ NC mult` as in ✱124·56. -/
theorem pm124_61 {α β : Type*} {ρ : Set α} :
    (aleph0 : Set (Set (Set (Set α)))) ∈ NCmult β →
      ((ρ ∈ ClsRefl ↔ cl ρ ∈ ClsRefl) ∧ (cl ρ ∈ ClsRefl ↔ cl (cl ρ) ∈ ClsRefl)) := by
  intro _
  simp only [clsRefl_iff]
  have key : ∀ {T : Type _} {σ : Set T}, σ.Infinite ↔ (cl σ).Infinite := fun {T σ} =>
    ⟨infinite_cl, fun h hfin => h (finite_cl hfin)⟩
  exact ⟨key, key⟩

/-!
## [✱125] The axiom of infinity

*(Vol. 2, p. 289)*

> *Summary of* *125.
>
> The present number is merely concerned to give a few equivalent forms of the axiom of infinity, and of the kindred assumption of the existence of \(\aleph _{0}\).
>
> In virtue of *125·24·25 below, if the axiom of infinity holds in any one type, then it holds in any other type which can be derived from this one, or from any type from which this one can be derived. Hence if we assume, as it seems natural to do, that all extensional types are derived from a first type, namely that of individuals, then the axiom of infinity in any such type is equivalent to the assumption that the number of individuals is not inductive.
>
> …

**Lean reading.** `Infin ax` is `InfinAx α`, `Infin ax(x)` is `InfinAxAt x` (✱120·03·04); without
typical determination the symbols are in the lowest types, with the same relative types (Summary of
✱125): `Infin ax` and `NC induct`, `Cls induct`, `N₀C`, `V` in one type. `t'x`, `t²'x`, `t³'x` are
`typ x`, `typ2 x`, `typ3 x`; `ℵ₀(x)` is `clsT2 aleph0 x`; `D⃖'α`, `ᗡ⃖'α` are `rels D A`,
`rels Dcnv A`. The open chains "etc." of ✱125·24·25 are stated by their first links (each further
link is the theorem at a higher type).

**Status.** proved (all propositions; ✱125·15·24·25·34·35 proved (reading), see their docstrings)
-/

/-- ✱125·1. \(\vdash \colon\ldotp \text{Infin ax}.\equiv :\alpha \in \text{NC induct}.\supset _{\alpha } .\exists !\alpha \quad[*120·3]\)

`Infin ax` and `NC induct` are in one type (the types of the cardinals `α` of the enunciation). -/
theorem pm125_1 {α : Type*} : InfinAx α ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → μ.Nonempty := Iff.rfl

/-- ✱125·11. \(\vdash \colon\ldotp \text{Infin ax}.\equiv :\alpha \in \text{NC induct}.\supset _{\alpha }.\alpha \neq \alpha +_{c}1 \quad[*120·33]\)

`α +_c 1` (with its `1`) is in the type of `α`, as the relation `+_c 1` of ✱120·01. -/
theorem pm125_11 {α : Type*} :
    InfinAx α ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → μ ≠ (μ +ᶜ (one : Set (Set α)) : Set (Set α)) := by
  rw [infinAx_iff_infinite]
  constructor
  · intro h μ hμ
    obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hμ
    rw [cardN_add_one]
    intro e
    have := cardN_inj (cardN_nonempty_of_infinite k) e
    omega
  · intro h
    by_contra hinf
    have : Finite α := not_infinite_iff_finite.1 hinf
    exact h ∅ empty_mem_NCinduct (cardAdd_eq_empty_of_empty_left Set.not_nonempty_empty _).symm

/-- ✱125·12. \(\vdash \colon\ldotp \text{Infin ax}.\equiv :\alpha \in \text{NC induct}.\supset _{\alpha }.\exists !\alpha +_{c}1\) -/
theorem pm125_12 {α : Type*} :
    InfinAx α ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → (μ +ᶜ (one : Set (Set α)) : Set (Set α)).Nonempty := by
  rw [infinAx_iff_infinite]
  constructor
  · intro h μ hμ
    obtain ⟨k, rfl⟩ := mem_NCinduct_iff_cardN.1 hμ
    rw [cardN_add_one]
    exact cardN_nonempty_of_infinite _
  · intro h
    by_contra hinf
    have : Finite α := not_infinite_iff_finite.1 hinf
    have := h ∅ empty_mem_NCinduct
    rw [cardAdd_eq_empty_of_empty_left Set.not_nonempty_empty] at this
    exact Set.not_nonempty_empty this

/-- ✱125·13. \(\vdash :\text{Infin ax}.\equiv .\Lambda {\sim}\in \text{NC induct} \quad[*125·1. *24·63]\)

`Λ` is the null class of the type of the inductive cardinals (worked example of `Defs/Part3`). -/
theorem pm125_13 {α : Type*} : InfinAx α ↔ (Λ : Set (Set α)) ∉ NCinduct := by
  rw [Null_eq_empty]
  constructor
  · intro h hΛ
    exact Set.not_nonempty_empty (h _ hΛ)
  · intro h μ hμ
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact h hμ

/-- ✱125·14. \(\vdash :\text{Infin ax}.\equiv .(+_{c}1)\upharpoonright \text{NC induct}\in 1\rightarrow 1\)

`(+_c 1)` is the relation `plusC1` (✱120·01), restricted to `NC induct`. -/
theorem pm125_14 {α : Type*} :
    InfinAx α ↔ plusC1 ↾ (NCinduct : Set (Set (Set α))) ∈ arrow one one := by
  rw [infinAx_iff_infinite, mem_arrow_one_one]
  constructor
  · intro h
    refine ⟨fun x y z ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ => hx.trans hy.symm, ?_⟩
    rintro x y z ⟨⟨hy, hyi⟩, ⟨hz, hzi⟩⟩
    obtain ⟨a, rfl⟩ := mem_NCinduct_iff_cardN.1 hyi
    obtain ⟨b, rfl⟩ := mem_NCinduct_iff_cardN.1 hzi
    have hy' : x = cardN α (a + 1) := hy.trans (cardN_add_one a)
    have hz' : x = cardN α (b + 1) := hz.trans (cardN_add_one b)
    have := cardN_inj (cardN_nonempty_of_infinite (a + 1)) (hy'.symm.trans hz')
    rw [show a = b by omega]
  · rintro ⟨-, hfun⟩
    by_contra hinf
    have : Finite α := not_infinite_iff_finite.1 hinf
    have hle : ∀ (A : Set α), A.ncard ≤ Nat.card α := fun A => by
      have := Set.ncard_le_ncard (Set.subset_univ A) Set.finite_univ
      rwa [Set.ncard_univ] at this
    have hemp : ∀ k, Nat.card α < k → cardN α k = ∅ := fun k hk => by
      ext A
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, hA⟩
      have := hle A
      omega
    have hne : (cardN α (Nat.card α)).Nonempty :=
      ⟨Set.univ, Set.finite_univ, Set.ncard_univ α⟩
    have hR1 : (plusC1 ↾ (NCinduct : Set (Set (Set α)))) (cardN α (Nat.card α + 1))
        (cardN α (Nat.card α)) :=
      ⟨plusC1_iff.2 (cardN_add_one _).symm, cardN_mem_NCinduct _⟩
    have hR2 : (plusC1 ↾ (NCinduct : Set (Set (Set α)))) (cardN α (Nat.card α + 1))
        (cardN α (Nat.card α + 1)) :=
      ⟨plusC1_iff.2 ((hemp _ (by omega)).trans ((hemp (Nat.card α + 1 + 1) (by omega)).symm.trans
        (cardN_add_one _).symm)), cardN_mem_NCinduct _⟩
    have e := hfun _ _ _ ⟨hR1, hR2⟩
    rw [e, hemp _ (by omega)] at hne
    exact Set.not_nonempty_empty hne

/-- ✱125·15. \(\vdash \colon\ldotp \text{Infin ax}.\equiv :\rho \in \text{Cls induct}.\supset _{p}.\exists !-\rho\)

(The e-text prints `⊃_p` for `⊃_ρ`.) `ρ ∈ Cls induct` puts `Cls induct` in the type of the
classes `ρ`, whose cardinals are those of `Infin ax`.

**Status.** proved (reading): transcription error of the e-text (`⊃_p` for `⊃_ρ`). -/
theorem pm125_15 {α : Type*} : InfinAx α ↔ ∀ ρ : Set α, ρ ∈ ClsInduct → (ρᶜ).Nonempty := by
  rw [infinAx_iff_infinite]
  constructor
  · intro h ρ hρ
    rw [Set.nonempty_compl]
    intro e
    rw [e, mem_ClsInduct] at hρ
    exact Set.infinite_univ hρ
  · intro h
    by_contra hinf
    have : Finite α := not_infinite_iff_finite.1 hinf
    have := h Set.univ (mem_ClsInduct.2 Set.finite_univ)
    rw [Set.compl_univ] at this
    exact Set.not_nonempty_empty this

/-- ✱125·16. \[\begin{align}\vdash : \text{Infin ax} . \equiv . \exists ! \text{Cls} - \text{Cls induct}. \equiv . &\exists ! \text{N}_{0}\text{C} - \text{NC induct}. \equiv .\\ &\text{V} {\sim} \in \text{Cls induct}\end{align}\]

The chain is the conjunction of its links; `Cls`, `Cls induct`, `N₀C`, `NC induct`, `V` are in
the types of `Infin ax`. -/
theorem pm125_16 {α : Type*} :
    ((InfinAx α ↔ (Cls \ ClsInduct : Set (Set α)).Nonempty) ∧
        ((Cls \ ClsInduct : Set (Set α)).Nonempty ↔ ((N₀C : Set (Set (Set α))) \ NCinduct).Nonempty)) ∧
      (((N₀C : Set (Set (Set α))) \ NCinduct).Nonempty ↔ (V : Set α) ∉ ClsInduct) := by
  have h1 : InfinAx α ↔ (Cls \ ClsInduct : Set (Set α)).Nonempty := by
    rw [infinAx_iff_infinite, Cls_eq_univ]
    constructor
    · intro h
      exact ⟨Set.univ, Set.mem_univ _, fun hi => Set.infinite_univ (mem_ClsInduct.1 hi)⟩
    · rintro ⟨A, -, hA⟩
      by_contra hinf
      have : Finite α := not_infinite_iff_finite.1 hinf
      exact hA (mem_ClsInduct.2 (Set.toFinite A))
  have h2 : InfinAx α ↔ ((N₀C : Set (Set (Set α))) \ NCinduct).Nonempty := by
    rw [infinAx_iff_infinite]
    constructor
    · intro h
      refine ⟨n₀c Set.univ, ⟨Set.univ, rfl⟩, fun hi => ?_⟩
      rcases NCinduct_cases hi with ⟨A, hA, he⟩ | ⟨hfin, -⟩
      · obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 he)
        have : Finite A := hA.to_subtype
        exact Set.infinite_univ (Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm))
      · exact not_finite_iff_infinite.2 h hfin
    · rintro ⟨μ, ⟨A, rfl⟩, hi⟩
      by_contra hinf
      have : Finite α := not_infinite_iff_finite.1 hinf
      exact hi (n₀c_mem_NCinduct (Set.toFinite A))
  have h3 : InfinAx α ↔ (V : Set α) ∉ ClsInduct := by
    rw [infinAx_iff_infinite, V_eq_univ, mem_ClsInduct, Set.finite_univ_iff, not_finite_iff_infinite]
  exact ⟨⟨h1, h1.symm.trans h2⟩, h2.symm.trans h3⟩

/-- ✱125·2. \(\vdash \colon\ldotp \text{Infin ax} (x). \equiv : \alpha \in \text{NC induct}. \supset _{\alpha } . \exists ! \alpha (x) \quad[*120·301]\) -/
theorem pm125_2 {α : Type*} {x : α} :
    InfinAxAt x ↔ ∀ μ : Set (Set α), μ ∈ NCinduct → (clsT2 μ x).Nonempty := Iff.rfl

/-- ✱125·21. \(\vdash :\text{Infin ax}(x).\equiv .tʻx{\sim}\in \text{Cls induct}\) -/
theorem pm125_21 {α : Type*} {x : α} : InfinAxAt x ↔ typ x ∉ ClsInduct := by
  rw [infinAxAt_iff, infinAx_iff_infinite, typ_eq_univ, mem_ClsInduct, Set.finite_univ_iff,
    not_finite_iff_infinite]

/-- ✱125·22. \(\vdash :\text{Infin ax}(x).\equiv .t^{3}ʻx\in \text{Cls refl} \quad[*125·21.*63·66.*124·6]\)

`t³'x` is `typ3 x`, the class of all classes of classes of terms of the type of `x`. -/
theorem pm125_22 {α : Type*} {x : α} : InfinAxAt x ↔ typ3 x ∈ ClsRefl := by
  rw [infinAxAt_iff, infinAx_iff_infinite, typ3_eq_univ, clsRefl_iff, Set.infinite_univ_iff]
  constructor
  · intro h
    have : Infinite (Set α) := infinite_set_of_infinite
    exact infinite_set_of_infinite
  · intro h
    by_contra hinf
    have : Finite α := not_infinite_iff_finite.1 hinf
    exact not_finite_iff_infinite.2 h inferInstance

/-- ✱125·23. \(\vdash :\text{Infin ax}(x).\equiv .\exists !\aleph _{0}(t^{2}ʻx) \quad[*125·22.*124·15]\)

`ℵ₀(t²'x)` is `clsT2 aleph0 (typ2 x)` (as in ✱123·37). -/
theorem pm125_23 {α : Type*} {x : α} : InfinAxAt x ↔ (clsT2 aleph0 (typ2 x)).Nonempty := by
  rw [clsT2_eq, aleph0_nonempty_iff, pm125_22, typ3_eq_univ, clsRefl_iff, Set.infinite_univ_iff]

/-- ✱125·24. \(\vdash :\text{Infin ax}(x).\equiv .\text{Infin ax}(tʻx).\equiv .\text{Infin ax}(t^{2}ʻx).\equiv .\text{etc}.\)

The chain `Infin ax(x) ≡ Infin ax(t'x) ≡ Infin ax(t²'x) ≡ etc.` is the conjunction of its
links; "etc." is the same equivalence one type higher, i.e. the proposition itself at `t'x`,
`t²'x`, … (it is proved for every type).

**Status.** proved (reading): the indefinite chain ("etc.") is stated by its first two links; each further link is this theorem at a higher type. -/
theorem pm125_24 {α : Type*} {x : α} :
    (InfinAxAt x ↔ InfinAxAt (typ x)) ∧ (InfinAxAt (typ x) ↔ InfinAxAt (typ2 x)) := by
  have key : ∀ {T : Type _} (y : T), InfinAxAt y ↔ InfinAxAt (typ y) := fun {T} y => by
    rw [infinAxAt_iff, infinAxAt_iff, infinAx_iff_infinite, infinAx_iff_infinite]
    constructor
    · intro h
      exact infinite_set_of_infinite
    · intro h
      by_contra hinf
      have : Finite T := not_infinite_iff_finite.1 hinf
      exact not_finite_iff_infinite.2 h inferInstance
  exact ⟨key x, key (typ x)⟩

/-- ✱125·25. \[\begin{align}\vdash :\text{Infin ax}(\alpha ).\equiv .\text{Infin ax}(t_{00}ʻ\alpha ).\equiv .&\text{Infin ax}(t_{0}^{1}ʻ\alpha ).\equiv .\\ &\text{Infin ax}(t^{11}ʻ\alpha ).\equiv .\text{etc}.\\ [*116·91·92.*120·56·52.*125·21]\end{align}\]

`Infin ax(α)` with `α` a class is `InfinAxAt A`; `t₀₀'α`, `t₀¹'α`, `t¹¹'α` are `typ₀₀ A`,
`typ₀1 A`, `typ11 A` (✱64). The chain is the conjunction of its links.

**Status.** proved (reading): the indefinite chain ("etc.") is stated by its first three links, as in ✱125·24. -/
theorem pm125_25 {α : Type*} {A : Set α} :
    ((InfinAxAt A ↔ InfinAxAt (typ₀₀ A)) ∧ (InfinAxAt (typ₀₀ A) ↔ InfinAxAt (typ₀1 A))) ∧
      (InfinAxAt (typ₀1 A) ↔ InfinAxAt (typ11 A)) := by
  have hS : ∀ {T : Type _}, Infinite (Set T) ↔ Infinite T := fun {T} => by
    constructor
    · intro h
      by_contra hinf
      have : Finite T := not_infinite_iff_finite.1 hinf
      exact not_finite_iff_infinite.2 h inferInstance
    · intro h
      exact infinite_set_of_infinite
  have h0 : InfinAxAt A ↔ Infinite α := by
    rw [infinAxAt_iff, infinAx_iff_infinite, hS]
  have h1 : InfinAxAt (typ₀₀ A) ↔ Infinite α := by
    rw [infinAxAt_iff, infinAx_iff_infinite, hS]
    constructor
    · intro h
      by_contra hinf
      have : Finite α := not_infinite_iff_finite.1 hinf
      exact not_finite_iff_infinite.2 h inferInstance
    · intro h
      exact Infinite.of_injective (fun a : α => fun x y : α => x = a)
        (fun a b e => cast (congrFun (congrFun e a) a) rfl)
  have h2 : InfinAxAt (typ₀1 A) ↔ Infinite α := by
    rw [infinAxAt_iff, infinAx_iff_infinite, hS]
    constructor
    · intro h
      by_contra hinf
      have : Finite α := not_infinite_iff_finite.1 hinf
      exact not_finite_iff_infinite.2 h inferInstance
    · intro h
      exact Infinite.of_injective (fun a : α => fun (x : α) (_ : Set α) => x = a)
        (fun a b e => cast (congrFun (congrFun e a) ∅) rfl)
  have h3 : InfinAxAt (typ11 A) ↔ Infinite α := by
    rw [infinAxAt_iff, infinAx_iff_infinite, hS]
    constructor
    · intro h
      by_contra hinf
      have : Finite α := not_infinite_iff_finite.1 hinf
      exact not_finite_iff_infinite.2 h inferInstance
    · intro h
      exact Infinite.of_injective (fun a : α => fun (X _ : Set α) => X = {a})
        (fun a b e => Set.singleton_injective (cast (congrFun (congrFun e {a}) ∅) rfl))
  exact ⟨⟨h0.trans h1.symm, h1.trans h2.symm⟩, h2.trans h3.symm⟩

/-- ✱125·3. \(\vdash :\exists !\aleph _{0}.\equiv .\exists !(1\rightarrow 1)\cap \hat{R} (\exists !\overrightarrow{B}ʻR.{\sim}\exists !\overrightarrow{B}ʻ\breve{R} )\)

`ℵ₀` and the relations `R` are in the lowest types (the Summary of ✱125): `R : α → α → Prop`. -/
theorem pm125_3 {α : Type*} :
    (aleph0 : Set (Set α)).Nonempty ↔
      (arrow one one ∩ {R : α → α → Prop | (refs Beg R).Nonempty ∧ ¬ (refs Beg R˘).Nonempty}).Nonempty := by
  constructor
  · rintro ⟨A, R, hR, -⟩
    refine ⟨R, hR.1, ?_⟩
    obtain ⟨f, hf, rfl⟩ := prog_iff_seq.1 hR
    refine ⟨⟨f 0, (beg_seqRel hf).2 rfl⟩, ?_⟩
    rintro ⟨y, ⟨v, n, -, rfl⟩, hy2⟩
    exact hy2 ⟨_, seqRel_apply f (n + 1)⟩
  · rintro ⟨R, h11, ⟨b, hb⟩, hno⟩
    have hcd : codom R ⊆ dom R := fun y hy => by
      by_contra hyd
      exact hno ⟨y, hy, hyd⟩
    exact ⟨_, pm123_192 ⟨h11, hcd⟩ ⟨b, hb, rfl⟩⟩

/-- ✱125·31. \(\vdash :\exists !\aleph _{0}(x).\equiv .tʻx\in \text{Cls refl} \quad[*124·15]\) -/
theorem pm125_31 {α : Type*} {x : α} : (clsT2 aleph0 x).Nonempty ↔ typ x ∈ ClsRefl := by
  rw [clsT2_eq, aleph0_nonempty_iff, typ_eq_univ, clsRefl_iff, Set.infinite_univ_iff]

/-- ✱125·32. \(\vdash :\exists !\aleph _{0}(x).\equiv \exists !(1\rightarrow 1)\cap \overleftarrow{\text{D}}ʻtʻx-\overleftarrow{\text{ᗡ}}ʻtʻx\)

`D⃖'t'x` is `rels D (typ x)` (the relations whose domain is `t'x`), `ᗡ⃖'t'x` is
`rels Dcnv (typ x)`; `(1 → 1) ∩ D⃖'t'x − ᗡ⃖'t'x` brackets to the left. -/
theorem pm125_32 {α : Type*} {x : α} :
    (clsT2 aleph0 x).Nonempty ↔
      ((arrow one one ∩ rels D (typ x)) \ rels Dcnv (typ x) : Set (α → α → Prop)).Nonempty := by
  rw [pm125_31, typ_eq_univ, clsRefl_iff]
  constructor
  · intro h
    obtain ⟨R, h11, hdom, hcod⟩ := exists_shift h (Set.mem_univ x)
    refine ⟨R, ⟨h11, hdom.symm⟩, fun hc => ?_⟩
    have hc' : Set.univ = codom R := hc
    have : x ∈ codom R := hc' ▸ Set.mem_univ x
    rw [hcod] at this
    exact this.2 rfl
  · rintro ⟨R, ⟨h11, hdom⟩, hcod⟩
    have hdom' : Set.univ = dom R := hdom
    refine clsRefl_iff.1 (pm124_16.1.2 ⟨codom R, ⟨Set.subset_univ _, ?_⟩, R, ⟨h11, hdom'⟩, rfl⟩)
    by_contra hne
    apply hcod
    show Set.univ = codom R
    exact (Set.eq_univ_of_forall fun y => by
      by_contra hy
      exact hne ⟨y, Set.mem_univ y, hy⟩).symm

/-- ✱125·33. \(\vdash \colon\ldotp \exists !\aleph _{0}(x).\equiv :\alpha \subset tʻx.\exists !\alpha .\supset _{\alpha }.\exists !(1\rightarrow 1)\cap \overleftarrow{\text{D}}ʻ\alpha -\overleftarrow{\text{ᗡ}}ʻ\alpha\) -/
theorem pm125_33 {α : Type*} {x : α} :
    (clsT2 aleph0 x).Nonempty ↔ ∀ A : Set α, A ⊆ typ x ∧ A.Nonempty →
      ((arrow one one ∩ rels D A) \ rels Dcnv A : Set (α → α → Prop)).Nonempty := by
  constructor
  · intro h A ⟨_, y, hy⟩
    by_cases hz : ∃ z, z ∉ A
    · classical
      obtain ⟨z, hz⟩ := hz
      let R : α → α → Prop := fun u v => (u ∈ A ∧ u ≠ y ∧ v = u) ∨ (u = y ∧ v = z)
      refine ⟨R, ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · intro u u' v ⟨h1, h2⟩
        rcases h1 with ⟨hu, huy, hvu⟩ | ⟨huy, hvz⟩ <;>
          rcases h2 with ⟨hu', hu'y, hvu'⟩ | ⟨hu'y, hvz'⟩
        · exact hvu.symm.trans hvu'
        · exact absurd (by rw [← hvz', hvu]; exact hu) hz
        · exact absurd (by rw [← hvz, hvu']; exact hu') hz
        · exact huy.trans hu'y.symm
      · intro u v v' ⟨h1, h2⟩
        rcases h1 with ⟨hu, huy, hvu⟩ | ⟨huy, hvz⟩ <;>
          rcases h2 with ⟨hu', hu'y, hv'u⟩ | ⟨hu'y, hv'z⟩
        · exact hvu.trans hv'u.symm
        · exact absurd hu'y huy
        · exact absurd huy hu'y
        · exact hvz.trans hv'z.symm
      · show A = dom R
        ext u
        constructor
        · intro hu
          by_cases huy : u = y
          · exact ⟨z, Or.inr ⟨huy, rfl⟩⟩
          · exact ⟨u, Or.inl ⟨hu, huy, rfl⟩⟩
        · rintro ⟨v, ⟨hu, -, -⟩ | ⟨rfl, -⟩⟩
          · exact hu
          · exact hy
      · intro hc
        have hc' : A = codom R := hc
        apply hz
        rw [hc']
        exact ⟨y, Or.inr ⟨rfl, rfl⟩⟩
    · push Not at hz
      have hA : A = Set.univ := Set.eq_univ_of_forall hz
      subst hA
      rw [pm125_31, typ_eq_univ, clsRefl_iff] at h
      obtain ⟨R, h11, hdom, hcod⟩ := exists_shift h hy
      refine ⟨R, ⟨h11, hdom.symm⟩, fun hc => ?_⟩
      have hc' : Set.univ = codom R := hc
      have : y ∈ codom R := hc' ▸ Set.mem_univ y
      rw [hcod] at this
      exact this.2 rfl
  · intro h
    rw [pm125_32]
    exact h (typ x) ⟨subset_rfl, x, by rw [typ_eq_univ]; trivial⟩

/-- ✱125·34. \(\vdash :\exists !\aleph _{0}(x).\equiv .\iota ʻtʻx{\sim}\in \text{NC}\)

`ι't'x ∈ NC` is `ι (typ x) ∈ NC β` with the converse-domain type of `NC` that of `t'x`, as in
PM's demonstration (`Nc't'x = ι't'x`, ✱100·13·41·45).

**Status.** proved (reading): the converse-domain type of `NC`, which PM leaves undetermined, is the type of `t'x`, as PM's demonstration uses (`Nc't'x = ι't'x`); in a type with fewer classes the equivalence fails. -/
theorem pm125_34 {α : Type*} {x : α} : (clsT2 aleph0 x).Nonempty ↔ ι (typ x) ∉ NC α := by
  rw [pm125_31, typ_eq_univ, clsRefl_iff]
  constructor
  · intro h hNC
    obtain ⟨B, hB⟩ := mem_NC.1 hNC
    have huniv : (Set.univ : Set α) ∈ nc α B := by rw [← hB]; exact mem_unitCls.2 rfl
    have hsm : sm (Set.univ \ ι x) (Set.univ : Set α) := sm_diff_finite h (Set.finite_singleton x)
    have hmem : Set.univ \ ι x ∈ nc α B := sm_trans hsm huniv
    rw [← hB, mem_unitCls] at hmem
    have : x ∈ Set.univ \ ι x := by rw [hmem]; trivial
    exact this.2 rfl
  · intro h hfin
    apply h
    refine ⟨Set.univ, Set.ext fun C => ⟨fun hC => ?_, fun hC => ?_⟩⟩
    · rw [mem_unitCls.1 hC]
      exact sm_refl _
    · have hC : sm C (Set.univ : Set α) := hC
      obtain ⟨-, hc⟩ := (sm_iff_of_finite hfin).1 (sm_symm hC)
      exact mem_unitCls.2 (Set.eq_of_subset_of_ncard_le (Set.subset_univ C) (le_of_eq hc) hfin)

/-- ✱125·35. \(\vdash \colon\ldotp \aleph _{0}\text{NC mult}.\supset :\exists !\aleph _{0}(x).\equiv .\text{Infin ax}(x)\)

(The e-text omits the `∈` of `ℵ₀ ∈ NC mult`.) `ℵ₀ ∈ NC mult` is at the type of ✱124·56.

**Status.** proved (reading): transcription error of the e-text (`ℵ₀ NC mult` for `ℵ₀ ∈ NC mult`). -/
theorem pm125_35 {α β : Type*} {x : α} :
    (aleph0 : Set (Set (Set (Set α)))) ∈ NCmult β →
      ((clsT2 (aleph0 : Set (Set α)) x).Nonempty ↔ InfinAxAt x) := by
  intro _
  rw [clsT2_eq, aleph0_nonempty_iff, infinAxAt_iff, infinAx_iff_infinite]

/-- ✱125·36. \(\vdash :\text{Infin ax}(\text{Cls}).\equiv .\exists !\aleph _{0}(\text{Cls})\)

`Cls` (✱20·03) is the class of all classes of `α`-things, a term of the type `Set (Set α)`;
`ℵ₀(Cls)` is `clsT2 aleph0 Cls`. -/
theorem pm125_36 {α : Type*} :
    InfinAxAt (Cls : Set (Set α)) ↔ (clsT2 aleph0 (Cls : Set (Set α))).Nonempty := by
  rw [clsT2_eq, aleph0_nonempty_iff, infinAxAt_iff, infinAx_iff_infinite]

/-!
## [✱126] On typically indefinite inductive cardinals

*(Vol. 2, p. 293)*

> *Recapitulation of Conventions and Summary of* *126.
>
> We have now arrived at the stage where we can adopt the standpoint of ordinary arithmetic, and can for the future in arithmetical operations with cardinals ignore differences of type. In order to understand how this is so, it will be necessary briefly to recall the line of thought of some of the previous numbers and the conventions upon which the symbolism is based.
>
> The symbolism of *102, though perfectly precise as to the typical relations of the various symbols, is in fact too complex for use, except in cases of absolute necessity. It is better to use the typically ambiguous symbols \(\text{Nc}\) and \(\text{sm}\), combined with some simple rules of interpretation of the symbolism, so as to secure that the various occurrences of the same symbols are in their proper relationships of type. This is the course followed in *100, *101, and in every number from *110 onwards.
>
> The important symbols which involve an explicit or implicit use of \(\text{Nc}\) or \(\text{ sm }\) are called 'formal numbers,' and it is only necessary to make the rules of interpretation apply to them.
>
> …

**Lean reading.** `NC ind` is `NCind = NC induct − ι'Λ` (✱126·01). The Rule of Indefinite Numbers
(Prefatory Statement, VII) is the hypothesis that a symbol for an inductive number (`1`, `2`,
`α +_c β`, `α ×_c β`, `α^β`, `α +_c 1`) is not `Λ` in its type; with `NC ind` convention AT is
applied: an equation between pure arithmetical formal numbers is in a type adequate for both sides
(`AdeqAdd`, `AdeqMul`, `AdeqExp`), and a formal number that is a side of `>` has its own adequate type
(IIT). `μ, ν ∈ NC ind` with an equation `μ = ν` makes `μ`, `ν` of one type. `μ_λ` is `clsT μ L`.

**Status.** proved (all propositions; ✱126·01 definition;
✱126·1·12·121·13·14·141·15·151·23·31·32·4·41·42·43·5·51·52·53 proved (reading), see their
docstrings)
-/

/-- ✱126·01 (Df). \(\text{NC ind}=\text{Nc induct}-\iota ʻ\Lambda \quad\text{Df}\)

(The e-text prints `Nc induct` for `NC induct`.)

**Status.** definition: transcription error of the e-text (`Nc induct` for `NC induct`), as `Defs/Part3` notes. -/
theorem pm126_01 {α : Type*} : (NCind : Set (Set (Set α))) = NCinduct \ ι Λ := rfl

/-- ✱126·011. \(\vdash :\nu \in \text{NC ind}.\equiv .\nu \in \text{NC induct}-\iota ʻ\Lambda \quad[(*126·01)]\) -/
theorem pm126_011 {α : Type*} {ν : Set (Set α)} : ν ∈ NCind ↔ ν ∈ NCinduct \ ι Λ := Iff.rfl

/-- ✱126·1. \(\vdash :\nu \in \text{NC ind}.\equiv .(\exists \alpha ).\alpha \in \text{Cls induct}.\nu =\text{Nc}ʻ\alpha .\exists !\nu\)

`Nc'α` is taken as the homogeneous cardinal of `α` (`α` in the type of the members of `ν`), as
the Prefatory Statement (VII) says `μ ∈ NC ind` may be replaced by `μ = Nc'α . α ∈ Cls induct`
with `Nc'α` a homogeneous or ascending cardinal.

**Status.** proved (reading): the type of the apparent variable `α`, which PM leaves undetermined, is that of the members of `ν` (homogeneous cardinal, Prefatory Statement VII). -/
theorem pm126_1 {α : Type*} {ν : Set (Set α)} :
    ν ∈ NCind ↔ ∃ A : Set α, (A ∈ ClsInduct ∧ ν = nc α A) ∧ ν.Nonempty := by
  rw [mem_NCind_iff]
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact ⟨M, ⟨mem_ClsInduct.2 hM, n₀c_eq_nc M⟩, n₀c_nonempty M⟩
  · rintro ⟨A, ⟨hA, rfl⟩, -⟩
    exact ⟨A, mem_ClsInduct.1 hA, (n₀c_eq_nc A).symm⟩

/-- ✱126·101. \[\begin{align}&\vdash \colon\ldotp \mu ,\nu \in \text{NC ind}.\exists !\mu _{\lambda }.\supset :\mu _{\lambda }=\nu _{\lambda }.\equiv .\mu _{\lambda }=\nu .\equiv .\mu =\nu \\ &[*126·1.*103·16]\end{align}\]

`μ_λ` is `μ ∩ t'λ` (✱65·01, `clsT μ L`), which makes `μ` and `ν` of the type of `λ`; so
`μ, ν ∈ NC ind` is `Mem2 μ ν NCind`. -/
theorem pm126_101 {α : Type*} {μ ν : Set (Set α)} {L : Set α} :
    Mem2 μ ν NCind ∧ (clsT μ L).Nonempty →
      ((clsT μ L = clsT ν L ↔ clsT μ L = ν) ∧ (clsT μ L = ν ↔ μ = ν)) := by
  intro _
  rw [clsT_eq, clsT_eq]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- ✱126·11. \(\vdash .0\in \text{NC ind} \quad[*120·12.*101·12]\) -/
theorem pm126_11 {α : Type*} : (zero : Set (Set α)) ∈ NCind := by
  rw [zero_eq_n₀c_empty]
  exact mem_NCind_iff.2 ⟨∅, Set.finite_empty, rfl⟩

/-- ✱126·12. \(\vdash :\nu \in \text{NC ind}.\supset .(\nu +_{c}1)\cap tʻ\nu \in \text{NC ind}\)

`(ν +_c 1) ∩ t'ν`: `t'ν` is the type of `ν`, so `ν +_c 1` is a cardinal of classes of the
type of `ν`'s members' classes (`Set (Set (Set X))`); the `1` is in the type of `ν`.

**Status.** proved (reading): Rule of Indefinite Numbers (✱126): the `1` is taken in a type in which it is not `Λ` (`[Nonempty X]`; for `ν = 0` in an empty type the proposition fails). -/
theorem pm126_12 {X : Type*} [Nonempty X] {ν : Set (Set X)} :
    ν ∈ NCind → ((ν +ᶜ (one : Set (Set X)) : Set (Set (Set X))) ∩ typ ν) ∈ NCind := by
  intro hν
  obtain ⟨A, hA, rfl⟩ := mem_NCind_iff.1 hν
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have key : nc (Set X) (A +ₐ ({x₀} : Set X)) = n₀c (insert ∅ ((fun c => ({c} : Set X)) '' A)) := by
    rw [n₀c_eq_nc]
    exact nc_eq_nc_of_sm (sm_clsSum_unit_insert A x₀)
  rw [typ_eq_univ, Set.inter_univ, one_eq_n₀c_singleton x₀, n₀c_cardAdd_n₀c, key]
  exact mem_NCind_iff.2 ⟨_, (hA.image _).insert ∅, rfl⟩

/-- ✱126·121. \(\vdash .1,2,3, ... \in \text{NC ind} \quad[*126·11·12]\)

`1, 2, 3, … ∈ NC ind` is schematic: `1` and `2`, and every particular inductive number `n`
(the cardinal of an `n`-membered class), each in a type in which it exists.

**Status.** proved (reading): Rule of Indefinite Numbers (✱126): each number is taken in a type in which it is not `Λ` (`[Nonempty W₁]`, `∃!2` in `W₂`, an `n`-membered class for `n`); the open list "3, …" is rendered by the clause for every `n`. -/
theorem pm126_121 {W₁ W₂ W₃ : Type*} [Nonempty W₁] (h2 : (two : Set (Set W₂)).Nonempty) :
    ((one : Set (Set W₁)) ∈ NCind ∧ (two : Set (Set W₂)) ∈ NCind) ∧
      ∀ (n : ℕ) (A : Set W₃), A.Finite ∧ A.ncard = n → n₀c A ∈ NCind := by
  obtain ⟨w⟩ := ‹Nonempty W₁›
  refine ⟨⟨?_, ?_⟩, fun n A ⟨hA, _⟩ => mem_NCind_iff.2 ⟨A, hA, rfl⟩⟩
  · rw [one_eq_n₀c_singleton w]
    exact mem_NCind_iff.2 ⟨_, Set.finite_singleton w, rfl⟩
  · rw [two_eq_cardN] at h2 ⊢
    obtain ⟨T, hT⟩ := h2
    rw [cardN_eq_n₀c hT]
    exact mem_NCind_iff.2 ⟨T, hT.1, rfl⟩

/-- ✱126·13. \[\begin{align}&\vdash :\alpha ,\beta \in \text{NC ind}.\equiv .\alpha +_{c}\beta \in \text{NC ind}\\ &[*120·71.*126·1.*110·3.*103·13]\end{align}\]

`α`, `β` are real variables of types `A₁`, `A₂`; `α +_c β` is in a type `γ`.

**Status.** proved (reading): Rule of Indefinite Numbers (✱126, applied to `α +_c β`): the sum is taken in a type in which it is not `Λ`. -/
theorem pm126_13 {A₁ A₂ γ : Type*} {α : Set (Set A₁)} {β : Set (Set A₂)}
    (h : (α +ᶜ β : Set (Set γ)).Nonempty) :
    α ∈ NCind ∧ β ∈ NCind ↔ (α +ᶜ β : Set (Set γ)) ∈ NCind := by
  obtain ⟨A, B, rfl, rfl⟩ := exists_of_cardAdd_nonempty h
  rw [n₀c_cardAdd_n₀c] at h ⊢
  constructor
  · rintro ⟨hA, hB⟩
    obtain ⟨M, hM, he⟩ := mem_NCind_iff.1 hA
    obtain ⟨N, hN, he'⟩ := mem_NCind_iff.1 hB
    have hAM : A.Finite := by
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 he)
      have : Finite M := hM.to_subtype
      exact Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)
    have hBN : B.Finite := by
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 he')
      have : Finite N := hN.to_subtype
      exact Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)
    exact nc_mem_NCind (clsSum_finite hAM hBN) h
  · intro hs
    have hf := finite_of_nc_mem_NCind hs
    exact ⟨mem_NCind_iff.2 ⟨A, finite_of_clsSum_finite_left hf, rfl⟩,
      mem_NCind_iff.2 ⟨B, finite_of_clsSum_finite_right hf, rfl⟩⟩

/-- ✱126·14. \[\begin{align}&\vdash :\alpha ,\beta \in \text{NC ind}.\supset .\alpha \times _{c}\beta \in \text{NC ind}\\ &[*120·72.*126·1.*113·25.*103·13]\end{align}\]

**Status.** proved (reading): Rule of Indefinite Numbers, as in ✱126·13 (the product is taken in a type in which it is not `Λ`). -/
theorem pm126_14 {A₁ A₂ γ : Type*} {α : Set (Set A₁)} {β : Set (Set A₂)}
    (h : (α ×ᶜ β : Set (Set γ)).Nonempty) :
    α ∈ NCind ∧ β ∈ NCind → (α ×ᶜ β : Set (Set γ)) ∈ NCind := by
  rintro ⟨hA, hB⟩
  obtain ⟨M, hM, rfl⟩ := mem_NCind_iff.1 hA
  obtain ⟨N, hN, rfl⟩ := mem_NCind_iff.1 hB
  rw [n₀c_cardMul_n₀c] at h ⊢
  exact nc_mem_NCind (finite_clsTimes hN hM) h

/-- ✱126·141. \[\begin{align}&\vdash :\alpha ,\beta \in \text{NC ind}-\iota ʻ0.\equiv .\alpha \times _{c}\beta \in \text{NC ind}-\iota ʻ0\\ &[*120·721.*113·114]\end{align}\]

**Status.** proved (reading): Rule of Indefinite Numbers, as in ✱126·13. -/
theorem pm126_141 {A₁ A₂ γ : Type*} {α : Set (Set A₁)} {β : Set (Set A₂)}
    (h : (α ×ᶜ β : Set (Set γ)).Nonempty) :
    α ∈ NCind \ ι zero ∧ β ∈ NCind \ ι zero ↔ (α ×ᶜ β : Set (Set γ)) ∈ NCind \ ι zero := by
  obtain ⟨A, B, rfl, rfl⟩ := exists_of_cardMul_nonempty h
  constructor
  · rintro ⟨⟨hA, hA0⟩, ⟨hB, hB0⟩⟩
    refine ⟨pm126_14 h ⟨hA, hB⟩, ?_⟩
    rw [n₀c_cardMul_n₀c] at h ⊢
    rw [n₀c_not_mem_zero_iff] at hA0 hB0
    obtain ⟨S, hS⟩ := h
    rw [nc_eq_n₀c_of_mem hS, n₀c_not_mem_zero_iff]
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hS
    obtain ⟨a, ha⟩ := hA0
    obtain ⟨b, hb⟩ := hB0
    exact ⟨_, (e.symm ((clsTimesEquiv A B).symm (⟨b, hb⟩, ⟨a, ha⟩))).2⟩
  · rintro ⟨hs, hs0⟩
    rw [n₀c_cardMul_n₀c] at h hs hs0
    obtain ⟨S, hS⟩ := h
    rw [nc_eq_n₀c_of_mem hS, n₀c_not_mem_zero_iff] at hs0
    obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hS
    obtain ⟨s, hs'⟩ := hs0
    obtain ⟨b, a⟩ := clsTimesEquiv A B (e ⟨s, hs'⟩)
    obtain ⟨hBf, hAf⟩ := finite_of_clsTimes_finite (finite_of_nc_mem_NCind hs)
      ⟨b.1, b.2⟩ ⟨a.1, a.2⟩
    refine ⟨⟨mem_NCind_iff.2 ⟨A, hAf, rfl⟩, n₀c_not_mem_zero_iff.2 ⟨a.1, a.2⟩⟩,
      ⟨mem_NCind_iff.2 ⟨B, hBf, rfl⟩, n₀c_not_mem_zero_iff.2 ⟨b.1, b.2⟩⟩⟩

/-- ✱126·15. \(\vdash :\alpha ,\beta \in \text{NC ind}.\supset .\alpha ^\beta \in \text{NC ind} \quad[*120·73.*116·25.*103·13]\)

**Status.** proved (reading): Rule of Indefinite Numbers, as in ✱126·13 (the power is taken in a type in which it is not `Λ`). -/
theorem pm126_15 {A₁ A₂ γ : Type*} {α : Set (Set A₁)} {β : Set (Set A₂)}
    (h : (α ^ᶜ β : Set (Set γ)).Nonempty) :
    α ∈ NCind ∧ β ∈ NCind → (α ^ᶜ β : Set (Set γ)) ∈ NCind := by
  rintro ⟨hA, hB⟩
  obtain ⟨M, hM, rfl⟩ := mem_NCind_iff.1 hA
  obtain ⟨N, hN, rfl⟩ := mem_NCind_iff.1 hB
  rw [n₀c_cardExp_n₀c] at h ⊢
  exact nc_mem_NCind (finite_clsExp hM hN) h

/-- ✱126·151. \[\begin{align}&\vdash :\alpha ,\beta \in \text{NC ind}-\iota ʻ0.\alpha \neq 1.\equiv .\alpha ^\beta \in \text{NC ind}-\iota ʻ0-\iota ʻ1\\ &[*120·731.*116·35.*117·592]\end{align}\]

The `1` of `α ≠ 1` is in the type of `α`, the `0`s and `1` of the right side in the types of
the classes they are compared with.

**Status.** proved (reading): Rule of Indefinite Numbers, as in ✱126·13. -/
theorem pm126_151 {A₁ A₂ γ : Type*} {α : Set (Set A₁)} {β : Set (Set A₂)}
    (h : (α ^ᶜ β : Set (Set γ)).Nonempty) :
    (α ∈ NCind \ ι zero ∧ β ∈ NCind \ ι zero) ∧ α ≠ one ↔
      (α ^ᶜ β : Set (Set γ)) ∈ (NCind \ ι zero) \ ι one := by
  obtain ⟨A, B, rfl, rfl⟩ := exists_of_cardExp_nonempty h
  rw [n₀c_cardExp_n₀c] at h ⊢
  obtain ⟨S, hS⟩ := h
  have hSA : nc γ (clsExp A B) = n₀c S := nc_eq_n₀c_of_mem hS
  rw [hSA]
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hS
  constructor
  · rintro ⟨⟨⟨hA, hA0⟩, ⟨hB, hB0⟩⟩, hA1⟩
    rw [n₀c_not_mem_zero_iff] at hA0 hB0
    obtain ⟨M, hM, hAM⟩ := mem_NCind_iff.1 hA
    obtain ⟨N, hN, hBN⟩ := mem_NCind_iff.1 hB
    have hAf : A.Finite := by
      obtain ⟨e'⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 hAM)
      have : Finite M := hM.to_subtype
      exact Set.finite_coe_iff.1 (Finite.of_equiv _ e'.symm)
    have hBf : B.Finite := by
      obtain ⟨e'⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 hBN)
      have : Finite N := hN.to_subtype
      exact Set.finite_coe_iff.1 (Finite.of_equiv _ e'.symm)
    have hSf : S.Finite := by
      have : Finite ↥(clsExp A B) := (finite_clsExp hAf hBf).to_subtype
      exact Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)
    have hcard : S.ncard = A.ncard ^ B.ncard := by
      rw [← ncard_clsExp hAf hBf]
      exact ((sm_iff_of_finite hSf).1 hS).2
    have hA1' : A.ncard ≠ 1 := by
      intro h1
      exact hA1 (by rw [n₀c_eq_one_iff]; exact Set.ncard_eq_one.1 h1)
    have hA2 : 2 ≤ A.ncard := by
      have := (Set.ncard_pos hAf).2 hA0
      omega
    have hB1 : 1 ≤ B.ncard := (Set.ncard_pos hBf).2 hB0
    refine ⟨⟨mem_NCind_iff.2 ⟨S, hSf, rfl⟩, ?_⟩, n₀c_not_mem_one_iff.2 ?_⟩
    · rw [n₀c_not_mem_zero_iff]
      exact Set.nonempty_of_ncard_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
    · rw [hcard]
      have : 2 ^ B.ncard ≤ A.ncard ^ B.ncard := Nat.pow_le_pow_left hA2 _
      have : 2 ≤ 2 ^ B.ncard := Nat.le_self_pow (by omega) 2
      omega
  · rintro ⟨⟨hSi, hS0⟩, hS1⟩
    have hSf : S.Finite := (mem_NCind_iff.1 hSi).elim fun F ⟨hF, he⟩ => by
      obtain ⟨e'⟩ := sm_iff_nonempty_equiv.1 (n₀c_eq_n₀c_iff.1 he)
      have : Finite F := hF.to_subtype
      exact Set.finite_coe_iff.1 (Finite.of_equiv _ e'.symm)
    rw [n₀c_not_mem_zero_iff] at hS0
    rw [n₀c_not_mem_one_iff] at hS1
    have : Finite S := hSf.to_subtype
    have hfin : Finite (B → A) := Finite.of_equiv _ (e.trans (clsExpEquiv A B))
    have hcardS : Nat.card (B → A) = S.ncard := by
      rw [← Nat.card_coe_set_eq, Nat.card_congr (e.trans (clsExpEquiv A B))]
    have hB0 : B.Nonempty := by
      by_contra hB
      rw [Set.not_nonempty_iff_eq_empty] at hB
      subst hB
      have : Nat.card ((∅ : Set A₂) → A) = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun f g => funext fun x => False.elim ((Set.mem_empty_iff_false _).1 x.2)⟩,
          ⟨fun x => False.elim ((Set.mem_empty_iff_false _).1 x.2)⟩⟩
      omega
    obtain ⟨b, hb⟩ := hB0
    have hA0 : A.Nonempty := by
      obtain ⟨s, hs⟩ := hS0
      exact ⟨((e.trans (clsExpEquiv A B)) ⟨s, hs⟩ ⟨b, hb⟩ : A₁),
        ((e.trans (clsExpEquiv A B)) ⟨s, hs⟩ ⟨b, hb⟩).2⟩
    have hAf : A.Finite := Set.finite_coe_iff.1 (Finite.of_injective (fun a : A => fun _ : B => a)
      (fun a a' h => congrFun h ⟨b, hb⟩))
    have hA1 : A.ncard ≠ 1 := by
      intro h1
      obtain ⟨a, rfl⟩ := Set.ncard_eq_one.1 h1
      have : Nat.card (B → ({a} : Set A₁)) = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun f g => funext fun x => Subtype.ext ((f x).2.trans (g x).2.symm)⟩,
          ⟨fun _ => ⟨a, rfl⟩⟩⟩
      omega
    have hBf : B.Finite := by
      by_contra hBi
      have : Infinite B := Set.infinite_coe_iff.2 hBi
      obtain ⟨T, hTA, hT⟩ := Set.exists_subset_card_eq (s := A) (n := 2) (by
        have := (Set.ncard_pos hAf).2 hA0
        omega)
      have hTc : T ∈ cardN A₁ 2 := ⟨hAf.subset hTA, hT⟩
      have : Infinite (B → T) := infinite_fun_two hTc
      exact not_finite_iff_infinite.2 (Infinite.of_injective
        (fun k : B → T => fun y => (⟨(k y : A₁), hTA (k y).2⟩ : A))
        (fun k k' h => funext fun y => Subtype.ext (by
          have := congrArg Subtype.val (congrFun h y)
          exact this))) hfin
    refine ⟨⟨⟨mem_NCind_iff.2 ⟨A, hAf, rfl⟩, n₀c_not_mem_zero_iff.2 hA0⟩,
      ⟨mem_NCind_iff.2 ⟨B, hBf, rfl⟩, n₀c_not_mem_zero_iff.2 ⟨b, hb⟩⟩⟩, fun h1 => hA1 ?_⟩
    obtain ⟨a, ha⟩ := n₀c_eq_one_iff.1 h1
    rw [ha, Set.ncard_singleton]

/-- ✱126·23. \(\vdash :\mu \in \text{NC}.\exists !\mu \cap tʻ\alpha .\supset .\exists !2^\mu \cap tʻtʻ\alpha .\exists !(\mu +_{c}1)\cap tʻtʻ\alpha\)

`μ ∩ t'α` puts `μ` in the type of `α`'s classes; `2^μ ∩ t't'α` and `(μ +_c 1) ∩ t't'α` are one
type higher. `NC`'s converse-domain type `β` is free; the `2` and `1` are constants in types
`V`, `W`.

**Status.** proved (reading): Rule of Indefinite Numbers (✱126): the constants `2`, `1` are taken in types in which they are not `Λ`. -/
theorem pm126_23 {X β V W : Type*} [Nonempty W] (h2 : (two : Set (Set V)).Nonempty) {A : Set X}
    {μ : Set (Set X)} :
    μ ∈ NC β ∧ (μ ∩ typ A).Nonempty →
      (((two : Set (Set V)) ^ᶜ μ : Set (Set (Set X))) ∩ typ (typ A)).Nonempty ∧
        ((μ +ᶜ (one : Set (Set W)) : Set (Set (Set X))) ∩ typ (typ A)).Nonempty := by
  classical
  rintro ⟨hNC, C, hC, -⟩
  obtain ⟨B, rfl⟩ := mem_NC.1 hNC
  rw [nc_eq_n₀c_of_mem hC]
  simp only [typ_eq_univ, Set.inter_univ]
  obtain ⟨w⟩ := ‹Nonempty W›
  refine ⟨?_, ?_⟩
  · rw [two_eq_cardN] at h2 ⊢
    obtain ⟨T, hT⟩ := h2
    obtain ⟨x, y, hxy, hT'⟩ := Set.ncard_eq_two.1 hT.2
    have hx : x ∈ T := by rw [hT']; exact Or.inl rfl
    have hy : y ∈ T := by rw [hT']; exact Or.inr rfl
    rw [cardN_eq_n₀c hT, n₀c_cardExp_n₀c]
    refine ⟨cl C, sm_iff_nonempty_equiv.2 ⟨(Equiv.Set.powerset C).trans ?_⟩⟩
    refine (Equiv.ofBijective (fun (D : Set C) (c : C) =>
      if c ∈ D then (⟨y, hy⟩ : T) else ⟨x, hx⟩) ⟨?_, ?_⟩).trans (clsExpEquiv T C).symm
    · intro D D' h
      ext c
      have := congrFun h c
      dsimp only at this
      by_cases h1 : c ∈ D <;> by_cases h2 : c ∈ D'
      · exact ⟨fun _ => h2, fun _ => h1⟩
      · rw [ite_eq_left h1, ite_eq_right h2] at this
        exact absurd (congrArg Subtype.val this).symm hxy
      · rw [ite_eq_right h1, ite_eq_left h2] at this
        exact absurd (congrArg Subtype.val this) hxy
      · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    · intro k
      refine ⟨{c | (k c : V) = y}, funext fun c => ?_⟩
      dsimp only
      by_cases hc : (k c : V) = y
      · rw [ite_eq_left (show c ∈ {c | (k c : V) = y} from hc)]
        exact Subtype.ext hc.symm
      · rw [ite_eq_right (show c ∉ {c | (k c : V) = y} from hc)]
        apply Subtype.ext
        have hk : (k c : V) ∈ ({x, y} : Set V) := by rw [← hT']; exact (k c).2
        rcases hk with hk | hk
        · exact hk.symm
        · exact absurd hk hc
  · rw [one_eq_n₀c_singleton w, n₀c_cardAdd_n₀c]
    exact ⟨_, sm_symm (sm_clsSum_unit_insert C w)⟩

/-- ✱126·31. \(\vdash :\alpha +_{c}1\in \text{NC ind}.\equiv .\alpha \in \text{NC ind} \quad[*126·12·13·121.*120·452]\)

The `1` is in the type of `α`; the sum is in a type `γ` that the convention leaves free (PM:
"the specification of the type of `α +_c 1` is omitted in accordance with the convention").

**Status.** proved (reading): Rule of Indefinite Numbers (✱126): `α +_c 1` is taken in a type in which it is not `Λ`. -/
theorem pm126_31 {A₁ γ : Type*} {α : Set (Set A₁)}
    (h : (α +ᶜ (one : Set (Set A₁)) : Set (Set γ)).Nonempty) :
    (α +ᶜ (one : Set (Set A₁)) : Set (Set γ)) ∈ NCind ↔ α ∈ NCind := by
  rw [← pm126_13 h]
  obtain ⟨-, B, -, hB⟩ := exists_of_cardAdd_nonempty h
  have hone : (one : Set (Set A₁)) ∈ NCind := by
    rw [hB]
    have : B ∈ (one : Set (Set A₁)) := hB ▸ self_mem_n₀c B
    obtain ⟨a, rfl⟩ := this
    exact mem_NCind_iff.2 ⟨_, Set.finite_singleton a, rfl⟩
  exact ⟨fun h => h.1, fun h => ⟨h, hone⟩⟩

/-- ✱126·32. \(\vdash :\alpha \in \text{NC}-\iota ʻ0-\iota ʻ\Lambda .\nu \in \text{NC ind}.\supset .\alpha +_{c}\nu >\nu \quad[*120·428.*110·3]\)

`α` (a cardinal of a type `A₁`, with `NC`'s converse-domain type `β` free) and `ν` are real
variables; `α +_c ν`, a side of `>`, has its own type `W`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type `W` of `α +_c ν`, a side of `>`, is adequate (`AdeqAdd`). -/
theorem pm126_32 {A₁ A₂ β W : Type*} {α : Set (Set A₁)} {ν : Set (Set A₂)} (hW : AdeqAdd W α ν) :
    α ∈ (NC β \ ι zero) \ ι Λ ∧ ν ∈ NCind → (α +ᶜ ν : Set (Set W)) >ᶜ ν := by
  rintro ⟨⟨⟨hNC, h0⟩, hΛ⟩, hν⟩
  obtain ⟨B, rfl⟩ := mem_NC.1 hNC
  have hne : (nc A₁ B).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro e
    exact hΛ (by rw [mem_unitCls, e, Null_eq_empty])
  obtain ⟨C, hC⟩ := hne
  rw [nc_eq_n₀c_of_mem hC] at h0 hW ⊢
  have hC0 : C.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro e
    exact h0 (by rw [mem_unitCls, n₀c_eq_zero_iff]; exact e)
  obtain ⟨D, hD, rfl⟩ := mem_NCind_iff.1 hν
  obtain ⟨E, hE⟩ := hW.nc_nonempty C D
  rw [n₀c_cardAdd_n₀c, nc_eq_n₀c_of_mem hE, cardGt_n₀c_iff]
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 hE
  refine ⟨⟨⟨fun d => e.symm ((clsSumEquiv C D).symm (Sum.inr d)),
    e.symm.injective.comp ((clsSumEquiv C D).symm.injective.comp Sum.inr_injective)⟩⟩, ?_⟩
  rintro ⟨g⟩
  have : Finite D := hD.to_subtype
  have : Finite E := Finite.of_injective g g.injective
  have : Finite (C ⊕ D) := Finite.of_equiv _ (e.trans (clsSumEquiv C D))
  have : Finite C := Finite.of_injective (Sum.inl : C → C ⊕ D) Sum.inl_injective
  have h1 : Nat.card E ≤ Nat.card D := Finite.card_le_of_embedding g
  have h2 : Nat.card E = Nat.card C + Nat.card D := by
    have := Fintype.ofFinite C
    have := Fintype.ofFinite D
    rw [Nat.card_congr (e.trans (clsSumEquiv C D)), Nat.card_sum]
  have h3 : 0 < Nat.card C := by
    obtain ⟨c, hc⟩ := hC0
    exact Nat.card_pos_iff.2 ⟨⟨⟨c, hc⟩⟩, inferInstance⟩
  omega

/-- ✱126·33. \(\vdash \colon\ldotp \alpha \in \text{NC ind}.\beta \in \text{NC}-\iota ʻ\Lambda .\supset :\alpha \beta \quad[*120·441]\)

The e-text has `α < β . ∨ . α = β . ∨ . α > β` (the formula above lost it in extraction); the
sum of three brackets to the left, and `α = β` makes `α`, `β` of one type.

**Status.** proved: PM's enunciation as printed in the e-text (`α < β ∨ α = β ∨ α > β`, checked against the source HTML); only the extracted formula above is defective. -/
theorem pm126_33 {A δ : Type*} {α β : Set (Set A)} :
    α ∈ NCind ∧ β ∈ NC δ \ ι Λ → (α <ᶜ β ∨ α = β) ∨ α >ᶜ β := by
  rintro ⟨hα, hNC, hΛ⟩
  obtain ⟨B, rfl⟩ := mem_NC.1 hNC
  obtain ⟨M, -, rfl⟩ := mem_NCind_iff.1 hα
  have hne : (nc A B).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro e
    exact hΛ (by rw [mem_unitCls, e, Null_eq_empty])
  obtain ⟨C, hC⟩ := hne
  rw [nc_eq_n₀c_of_mem hC]
  by_cases h1 : Nonempty (M ↪ C)
  · by_cases h2 : Nonempty (C ↪ M)
    · obtain ⟨g⟩ := h1
      obtain ⟨g'⟩ := h2
      obtain ⟨k, hk⟩ := Function.Embedding.schroeder_bernstein g.injective g'.injective
      exact Or.inl (Or.inr (n₀c_eq_n₀c_iff.2 (sm_iff_nonempty_equiv.2 ⟨Equiv.ofBijective k hk⟩)))
    · exact Or.inl (Or.inl (cardGt_n₀c_iff.2 ⟨h1, h2⟩))
  · exact Or.inr (cardGt_n₀c_iff.2 ⟨(Function.Embedding.total M C).resolve_left h1, h1⟩)

/-- ✱126·4. \[\begin{align}&\vdash \colon\ldotp \mu ,\nu ,\varpi \in \text{NC ind}.\supset :\mu +_{c}\varpi =\nu +_{c}\varpi .\equiv .\mu =\nu \\ &[*126·13.*120·41]\end{align}\]

`μ = ν` makes `μ`, `ν` of one type; `ϖ` is of a type `B`. The equation of the sums is
arithmetical (AT): in a type `γ` adequate for both sides.

**Status.** proved (reading): convention AT (Prefatory Statement, VI; used with `NC ind`, ✱126): the equation `μ +_c ϖ = ν +_c ϖ` is taken in a type adequate for both sides. -/
theorem pm126_4 {A B γ : Type*} {μ ν : Set (Set A)} {ϖ : Set (Set B)} (h1 : AdeqAdd γ μ ϖ)
    (h2 : AdeqAdd γ ν ϖ) :
    (μ ∈ NCind ∧ ν ∈ NCind) ∧ ϖ ∈ NCind →
      ((μ +ᶜ ϖ : Set (Set γ)) = (ν +ᶜ ϖ : Set (Set γ)) ↔ μ = ν) := by
  rintro ⟨⟨hμ, hν⟩, hϖ⟩
  obtain ⟨M, hM, rfl⟩ := mem_NCind_iff.1 hμ
  obtain ⟨N, hN, rfl⟩ := mem_NCind_iff.1 hν
  obtain ⟨P, hP, rfl⟩ := mem_NCind_iff.1 hϖ
  have hne := h1.nc_nonempty M P
  rw [← n₀c_cardAdd_n₀c, n₀c_add_finite hM hP] at hne
  rw [n₀c_add_finite hM hP, n₀c_add_finite hN hP, n₀c_finite_eq_iff hM hN]
  constructor
  · intro e
    have := cardN_inj hne e
    omega
  · intro e
    rw [e]

/-- ✱126·41. \[\begin{align}&\vdash \colon\ldotp \mu ,\nu ,\varpi \in \text{NC ind}.\varpi \neq 0.\supset :\mu \times _{c}\varpi =\nu \times _{c}\varpi .\equiv .\mu =\nu \\ &[*120·51.*126·14]\end{align}\]

**Status.** proved (reading): convention AT, as in ✱126·4. -/
theorem pm126_41 {A B γ : Type*} {μ ν : Set (Set A)} {ϖ : Set (Set B)} (h1 : AdeqMul γ μ ϖ)
    (h2 : AdeqMul γ ν ϖ) :
    ((μ ∈ NCind ∧ ν ∈ NCind) ∧ ϖ ∈ NCind) ∧ ϖ ≠ zero →
      ((μ ×ᶜ ϖ : Set (Set γ)) = (ν ×ᶜ ϖ : Set (Set γ)) ↔ μ = ν) := by
  rintro ⟨⟨⟨hμ, hν⟩, hϖ⟩, h0⟩
  obtain ⟨M, hM, rfl⟩ := mem_NCind_iff.1 hμ
  obtain ⟨N, hN, rfl⟩ := mem_NCind_iff.1 hν
  obtain ⟨P, hP, rfl⟩ := mem_NCind_iff.1 hϖ
  have hP0 : P.ncard ≠ 0 := fun h => h0 (n₀c_eq_zero_iff.2 ((Set.ncard_eq_zero hP).1 h))
  have hne := AdeqMul_nc_nonempty h1 M P
  rw [← n₀c_cardMul_n₀c, n₀c_mul_finite hM hP] at hne
  rw [n₀c_mul_finite hM hP, n₀c_mul_finite hN hP, n₀c_finite_eq_iff hM hN]
  constructor
  · intro e
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hP0) (cardN_inj hne e)
  · intro e
    rw [e]

/-- ✱126·42. \[\begin{align}&\vdash \colon\ldotp \mu \nu ,\varpi \in \text{NC ind}.\varpi \neq 0.\supset :\mu ^{\varpi }=\nu ^{\varpi }.\equiv .\mu =\nu \\ &[*120·55.*126·15]\end{align}\]

(The e-text omits the comma of `μ, ν, ϖ ∈ NC ind`.)

**Status.** proved (reading): convention AT, as in ✱126·4; transcription error of the e-text (`μ ν, ϖ` for `μ, ν, ϖ`). -/
theorem pm126_42 {A B γ : Type*} {μ ν : Set (Set A)} {ϖ : Set (Set B)} (h1 : AdeqExp γ μ ϖ)
    (h2 : AdeqExp γ ν ϖ) :
    ((μ ∈ NCind ∧ ν ∈ NCind) ∧ ϖ ∈ NCind) ∧ ϖ ≠ zero →
      ((μ ^ᶜ ϖ : Set (Set γ)) = (ν ^ᶜ ϖ : Set (Set γ)) ↔ μ = ν) := by
  rintro ⟨⟨⟨hμ, hν⟩, hϖ⟩, h0⟩
  obtain ⟨M, hM, rfl⟩ := mem_NCind_iff.1 hμ
  obtain ⟨N, hN, rfl⟩ := mem_NCind_iff.1 hν
  obtain ⟨P, hP, rfl⟩ := mem_NCind_iff.1 hϖ
  have hP0 : P.ncard ≠ 0 := fun h => h0 (n₀c_eq_zero_iff.2 ((Set.ncard_eq_zero hP).1 h))
  have hPne : P.Nonempty := Set.nonempty_of_ncard_ne_zero hP0
  have hne := AdeqExp_nc_nonempty' h1 M P (Or.inr hPne)
  rw [← n₀c_cardExp_n₀c, n₀c_exp_finite hM hP] at hne
  rw [n₀c_exp_finite hM hP, n₀c_exp_finite hN hP, n₀c_finite_eq_iff hM hN]
  constructor
  · intro e
    exact Nat.pow_left_injective hP0 (cardN_inj hne e)
  · intro e
    rw [e]

/-- ✱126·43. \[\begin{align}&\vdash \colon\ldotp \mu ,\nu ,\varpi \in \text{NC ind}.\varpi \neq 0.\omega \neq 1·\supset :\varpi ^\mu =\varpi ^\nu .\equiv .\mu =\nu \\ &[*120·53.*126·15]\end{align}\]

(The e-text prints `ω ≠ 1·` for `ϖ ≠ 1 .`.) The `0`, `1` are in the type of `ϖ`.

**Status.** proved (reading): convention AT, as in ✱126·4; transcription error of the e-text (`ω ≠ 1·` for `ϖ ≠ 1 .`). -/
theorem pm126_43 {A B γ : Type*} {μ ν : Set (Set A)} {ϖ : Set (Set B)} (h1 : AdeqExp γ ϖ μ)
    (h2 : AdeqExp γ ϖ ν) :
    (((μ ∈ NCind ∧ ν ∈ NCind) ∧ ϖ ∈ NCind) ∧ ϖ ≠ zero) ∧ ϖ ≠ one →
      ((ϖ ^ᶜ μ : Set (Set γ)) = (ϖ ^ᶜ ν : Set (Set γ)) ↔ μ = ν) := by
  rintro ⟨⟨⟨⟨hμ, hν⟩, hϖ⟩, h0⟩, h1'⟩
  obtain ⟨M, hM, rfl⟩ := mem_NCind_iff.1 hμ
  obtain ⟨N, hN, rfl⟩ := mem_NCind_iff.1 hν
  obtain ⟨P, hP, rfl⟩ := mem_NCind_iff.1 hϖ
  have hP0 : P.ncard ≠ 0 := fun h => h0 (n₀c_eq_zero_iff.2 ((Set.ncard_eq_zero hP).1 h))
  have hP1 : P.ncard ≠ 1 := fun h => h1' (n₀c_eq_one_iff.2 (Set.ncard_eq_one.1 h))
  have hPne : P.Nonempty := Set.nonempty_of_ncard_ne_zero hP0
  have hne := AdeqExp_nc_nonempty' h1 P M (Or.inl hPne)
  rw [← n₀c_cardExp_n₀c, n₀c_exp_finite hP hM] at hne
  rw [n₀c_exp_finite hP hM, n₀c_exp_finite hP hN, n₀c_finite_eq_iff hM hN]
  constructor
  · intro e
    exact Nat.pow_right_injective (by omega) (cardN_inj hne e)
  · intro e
    rw [e]

/-- ✱126·5. \(\vdash \colon\ldotp \mu ,\nu ,\varpi \in \text{NC ind}.\supset :\mu +_{c}\varpi >\nu +_{c}\varpi .\equiv .\mu >\nu\)

The sides of `>` are formal numbers in arithmetical position, each in its own type
(`W₁`, `W₂`); `μ`, `ν`, `ϖ` are real variables of types `A₁`, `A₂`, `B`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the sums, sides of `>`, are adequate (`AdeqAdd`). -/
theorem pm126_5 {A₁ A₂ B W₁ W₂ : Type*} {μ : Set (Set A₁)} {ν : Set (Set A₂)} {ϖ : Set (Set B)}
    (h1 : AdeqAdd W₁ μ ϖ) (h2 : AdeqAdd W₂ ν ϖ) :
    (μ ∈ NCind ∧ ν ∈ NCind) ∧ ϖ ∈ NCind →
      ((μ +ᶜ ϖ : Set (Set W₁)) >ᶜ (ν +ᶜ ϖ : Set (Set W₂)) ↔ μ >ᶜ ν) := by
  rintro ⟨⟨hμ, hν⟩, hϖ⟩
  obtain ⟨M, hM, rfl⟩ := mem_NCind_iff.1 hμ
  obtain ⟨N, hN, rfl⟩ := mem_NCind_iff.1 hν
  obtain ⟨P, hP, rfl⟩ := mem_NCind_iff.1 hϖ
  have hne1 := h1.nc_nonempty M P
  have hne2 := h2.nc_nonempty N P
  rw [← n₀c_cardAdd_n₀c, n₀c_add_finite hM hP] at hne1
  rw [← n₀c_cardAdd_n₀c, n₀c_add_finite hN hP] at hne2
  rw [n₀c_add_finite hM hP, n₀c_add_finite hN hP, cardN_cardGt_iff, n₀c_finite_cardGt_iff hM hN]
  constructor
  · intro h
    omega
  · intro h
    exact ⟨⟨hne1, hne2⟩, by omega⟩

/-- ✱126·51. \[\begin{align}&\vdash \colon\ldotp \mu ,\nu ,\varpi \in \text{NC ind}.\varpi \neq 0.\supset :\mu \times _{c}\varpi >\nu \times _{c}\varpi .\equiv .\mu >\nu \\ &[*117·571.*126·41]\end{align}\]

**Status.** proved (reading): convention IIT, as in ✱126·5 (`AdeqMul`). -/
theorem pm126_51 {A₁ A₂ B W₁ W₂ : Type*} {μ : Set (Set A₁)} {ν : Set (Set A₂)} {ϖ : Set (Set B)}
    (h1 : AdeqMul W₁ μ ϖ) (h2 : AdeqMul W₂ ν ϖ) :
    ((μ ∈ NCind ∧ ν ∈ NCind) ∧ ϖ ∈ NCind) ∧ ϖ ≠ zero →
      ((μ ×ᶜ ϖ : Set (Set W₁)) >ᶜ (ν ×ᶜ ϖ : Set (Set W₂)) ↔ μ >ᶜ ν) := by
  rintro ⟨⟨⟨hμ, hν⟩, hϖ⟩, h0⟩
  obtain ⟨M, hM, rfl⟩ := mem_NCind_iff.1 hμ
  obtain ⟨N, hN, rfl⟩ := mem_NCind_iff.1 hν
  obtain ⟨P, hP, rfl⟩ := mem_NCind_iff.1 hϖ
  have hP0 : P.ncard ≠ 0 := fun h => h0 (n₀c_eq_zero_iff.2 ((Set.ncard_eq_zero hP).1 h))
  have hne1 := AdeqMul_nc_nonempty h1 M P
  have hne2 := AdeqMul_nc_nonempty h2 N P
  rw [← n₀c_cardMul_n₀c, n₀c_mul_finite hM hP] at hne1
  rw [← n₀c_cardMul_n₀c, n₀c_mul_finite hN hP] at hne2
  rw [n₀c_mul_finite hM hP, n₀c_mul_finite hN hP, cardN_cardGt_iff, n₀c_finite_cardGt_iff hM hN]
  constructor
  · intro h
    exact (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hP0)).1 h.2
  · intro h
    exact ⟨⟨hne1, hne2⟩, (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hP0)).2 h⟩

/-- ✱126·52. \[\begin{align}&\vdash \colon\ldotp \mu ,\nu ,\varpi \in \text{NC ind}.\varpi \neq 0.\supset :\mu ^{\varpi }>\nu ^{\varpi }.\equiv .\mu >\nu \\ &[*117·581.*126·42]\end{align}\]

**Status.** proved (reading): convention IIT, as in ✱126·5 (`AdeqExp`). -/
theorem pm126_52 {A₁ A₂ B W₁ W₂ : Type*} {μ : Set (Set A₁)} {ν : Set (Set A₂)} {ϖ : Set (Set B)}
    (h1 : AdeqExp W₁ μ ϖ) (h2 : AdeqExp W₂ ν ϖ) :
    ((μ ∈ NCind ∧ ν ∈ NCind) ∧ ϖ ∈ NCind) ∧ ϖ ≠ zero →
      ((μ ^ᶜ ϖ : Set (Set W₁)) >ᶜ (ν ^ᶜ ϖ : Set (Set W₂)) ↔ μ >ᶜ ν) := by
  rintro ⟨⟨⟨hμ, hν⟩, hϖ⟩, h0⟩
  obtain ⟨M, hM, rfl⟩ := mem_NCind_iff.1 hμ
  obtain ⟨N, hN, rfl⟩ := mem_NCind_iff.1 hν
  obtain ⟨P, hP, rfl⟩ := mem_NCind_iff.1 hϖ
  have hP0 : P.ncard ≠ 0 := fun h => h0 (n₀c_eq_zero_iff.2 ((Set.ncard_eq_zero hP).1 h))
  have hPne : P.Nonempty := Set.nonempty_of_ncard_ne_zero hP0
  have hne1 := AdeqExp_nc_nonempty' h1 M P (Or.inr hPne)
  have hne2 := AdeqExp_nc_nonempty' h2 N P (Or.inr hPne)
  rw [← n₀c_cardExp_n₀c, n₀c_exp_finite hM hP] at hne1
  rw [← n₀c_cardExp_n₀c, n₀c_exp_finite hN hP] at hne2
  rw [n₀c_exp_finite hM hP, n₀c_exp_finite hN hP, cardN_cardGt_iff, n₀c_finite_cardGt_iff hM hN]
  constructor
  · intro h
    exact (Nat.pow_lt_pow_iff_left hP0).1 h.2
  · intro h
    exact ⟨⟨hne1, hne2⟩, (Nat.pow_lt_pow_iff_left hP0).2 h⟩

/-- ✱126·53. \[\begin{align}&\vdash \colon\ldotp \mu ,\nu ,\varpi \in \text{NC ind}.\varpi \neq 0.\varpi \neq 1.\supset :\varpi ^\mu >\varpi ^\nu .\equiv .\mu >\nu \\ &[*117·591.*126·43]\end{align}\]

**Status.** proved (reading): convention IIT, as in ✱126·5 (`AdeqExp`). -/
theorem pm126_53 {A₁ A₂ B W₁ W₂ : Type*} {μ : Set (Set A₁)} {ν : Set (Set A₂)} {ϖ : Set (Set B)}
    (h1 : AdeqExp W₁ ϖ μ) (h2 : AdeqExp W₂ ϖ ν) :
    (((μ ∈ NCind ∧ ν ∈ NCind) ∧ ϖ ∈ NCind) ∧ ϖ ≠ zero) ∧ ϖ ≠ one →
      ((ϖ ^ᶜ μ : Set (Set W₁)) >ᶜ (ϖ ^ᶜ ν : Set (Set W₂)) ↔ μ >ᶜ ν) := by
  rintro ⟨⟨⟨⟨hμ, hν⟩, hϖ⟩, h0⟩, h1'⟩
  obtain ⟨M, hM, rfl⟩ := mem_NCind_iff.1 hμ
  obtain ⟨N, hN, rfl⟩ := mem_NCind_iff.1 hν
  obtain ⟨P, hP, rfl⟩ := mem_NCind_iff.1 hϖ
  have hP0 : P.ncard ≠ 0 := fun h => h0 (n₀c_eq_zero_iff.2 ((Set.ncard_eq_zero hP).1 h))
  have hP1 : P.ncard ≠ 1 := fun h => h1' (n₀c_eq_one_iff.2 (Set.ncard_eq_one.1 h))
  have hPne : P.Nonempty := Set.nonempty_of_ncard_ne_zero hP0
  have hne1 := AdeqExp_nc_nonempty' h1 P M (Or.inl hPne)
  have hne2 := AdeqExp_nc_nonempty' h2 P N (Or.inl hPne)
  rw [← n₀c_cardExp_n₀c, n₀c_exp_finite hP hM] at hne1
  rw [← n₀c_cardExp_n₀c, n₀c_exp_finite hP hN] at hne2
  rw [n₀c_exp_finite hP hM, n₀c_exp_finite hP hN, cardN_cardGt_iff, n₀c_finite_cardGt_iff hM hN]
  constructor
  · intro h
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 h.2
  · intro h
    exact ⟨⟨hne1, hne2⟩, (Nat.pow_lt_pow_iff_right (by omega)).2 h⟩

end PrincipiaMathematica
