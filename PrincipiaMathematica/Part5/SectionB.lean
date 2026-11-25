import PrincipiaMathematica.Defs.Part5

/-!
# Part V, Section B: On sections, segments, stretches, and derivatives

Volume 2. Numbers: ✱210, ✱211, ✱212.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v

/-! ### Helper lemmas (not PM propositions) -/

section Helpers

variable {α : Type u} {β : Type v}

private theorem eqΛ {A : Set α} : A = Λ ↔ ∀ x, x ∉ A := by
  rw [Null_eq_empty]; exact Set.eq_empty_iff_forall_notMem

private theorem desc_of {R : α → β → Prop} {y : β} {b : α} (h : ∀ x, R x y ↔ x = b)
    {ψ : α → Prop} (hb : ψ b) : Desc R y ψ := (TheIs_iff_of_unique h).2 hb

private theorem desc_iff_of {R : α → β → Prop} {y : β} {b : α} (h : ∀ x, R x y ↔ x = b)
    {ψ : α → Prop} : Desc R y ψ ↔ ψ b := TheIs_iff_of_unique h

private theorem edesc_of {R : α → β → Prop} {y : β} {b : α} (h : ∀ x, R x y ↔ x = b) :
    EDesc R y := ⟨b, h⟩

/-- A description whose object is unique: two descriptions with the same unique object. -/
private theorem desc2_of {R S : α → β → Prop} {y z : β} {b : α} (h1 : ∀ x, R x y ↔ x = b)
    (h2 : ∀ x, S x z ↔ x = b) : Desc R y (fun A => Desc S z (fun B => A = B)) :=
  desc_of h1 (desc_of h2 rfl)

private theorem Plc_iff {P : α → α → Prop} {A B : Set α} :
    Plc P A B ↔ (A ⊆ fld P ∧ B ⊆ fld P) ∧ ((B \ A) \ P ʻʻ (A \ B)).Nonempty := by
  show (B ∈ cl (fld P˘) ∧ A ∈ cl (fld P˘)) ∧ ((B \ A) \ P˘˘ ʻʻ (A \ B)).Nonempty ↔ _
  rw [fld_cnv]
  exact and_congr And.comm Iff.rfl

private theorem tl_iff_of {P : α → α → Prop} {x : α} {L : Set α} (h : ¬∃ y, minP P y L) :
    tlP P x L ↔ precP P x L := ⟨fun h' => h'.1, fun h' => ⟨h', h⟩⟩

private theorem lt_iff_of {P : α → α → Prop} {x : α} {L : Set α} (h : ¬∃ y, maxP P y L) :
    ltP P x L ↔ seqP P x L := ⟨fun h' => h'.1, fun h' => ⟨h', h⟩⟩

end Helpers

/-! ### Helper lemmas for ✱210: the series of a nest of classes by inclusion -/

section H210

variable {α : Type u} {K : Set (Set α)}

/-- PM's hypothesis ✱210·1: of any two members of `κ`, one is contained in the other. -/
private def Nest (K : Set (Set α)) : Prop := ∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C

/-- PM's `Q` of ✱210·11: proper inclusion between members of `κ`. -/
private def incl (K : Set (Set α)) : Set α → Set α → Prop :=
  fun A B => ((A ∈ K ∧ B ∈ K) ∧ A ⊆ B) ∧ A ≠ B

private theorem ssub_iff (hn : Nest K) {A B : Set α} (hA : A ∈ K) (hB : B ∈ K) :
    A ⊆ B ∧ A ≠ B ↔ (B \ A).Nonempty := by
  constructor
  · rintro ⟨h1, h2⟩
    by_contra h
    apply h2
    refine Set.Subset.antisymm h1 fun x hx => ?_
    by_contra hxA
    exact h ⟨x, hx, hxA⟩
  · rintro ⟨x, hxB, hxA⟩
    rcases hn A B ⟨hA, hB⟩ with h | h
    · exact ⟨h, fun e => hxA (e ▸ hxB)⟩
    · exact absurd (h hxB) hxA

private theorem incl_iff (hn : Nest K) {A B : Set α} :
    incl K A B ↔ (A ∈ K ∧ B ∈ K) ∧ (B \ A).Nonempty := by
  constructor
  · rintro ⟨⟨hAB, h1⟩, h2⟩
    exact ⟨hAB, (ssub_iff hn hAB.1 hAB.2).1 ⟨h1, h2⟩⟩
  · rintro ⟨hAB, h⟩
    obtain ⟨h1, h2⟩ := (ssub_iff hn hAB.1 hAB.2).2 h
    exact ⟨⟨hAB, h1⟩, h2⟩

private theorem not_incl (hn : Nest K) {A B : Set α} (hA : A ∈ K) (hB : B ∈ K) :
    ¬ incl K A B ↔ B ⊆ A := by
  rw [incl_iff hn]
  constructor
  · intro h x hx
    by_contra hxA
    exact h ⟨⟨hA, hB⟩, x, hx, hxA⟩
  · rintro h ⟨-, x, hxB, hxA⟩
    exact hxA (h hxB)

private theorem fld_incl_sub {A : Set α} (h : A ∈ fld (incl K)) : A ∈ K := by
  obtain ⟨B, h | h⟩ := h
  · exact h.1.1.1
  · exact h.1.1.2

private theorem fld_incl (hn : Nest K) (h1 : K ∉ one) : fld (incl K) = K := by
  ext A
  refine ⟨fld_incl_sub, fun hA => ?_⟩
  by_contra hf
  apply h1
  refine mem_one_iff.2 ⟨A, fun B => ⟨fun hB => ?_, fun e => e ▸ hA⟩⟩
  by_contra hne
  rcases hn A B ⟨hA, hB⟩ with h | h
  · exact hf ⟨B, Or.inl ⟨⟨⟨hA, hB⟩, h⟩, Ne.symm hne⟩⟩
  · exact hf ⟨B, Or.inr ⟨⟨⟨hB, hA⟩, h⟩, hne⟩⟩

private theorem incl_ser (hn : Nest K) : incl K ∈ Ser := by
  refine mem_Ser.2 ⟨⟨fun A h => h.2 rfl, fun A B C ⟨h1, h2⟩ =>
    ⟨⟨⟨h1.1.1.1, h2.1.1.2⟩, h1.1.2.trans h2.1.2⟩, ?_⟩⟩, ?_⟩
  · intro e
    subst e
    exact h1.2 (Set.Subset.antisymm h1.1.2 h2.1.2)
  · rintro A B ⟨hA, hB⟩
    have hA' := fld_incl_sub hA
    have hB' := fld_incl_sub hB
    by_cases e : A = B
    · exact Or.inl (Or.inr e)
    rcases hn A B ⟨hA', hB'⟩ with h | h
    · exact Or.inl (Or.inl ⟨⟨⟨hA', hB'⟩, h⟩, e⟩)
    · exact Or.inr ⟨⟨⟨hB', hA'⟩, h⟩, Ne.symm e⟩

private theorem min_incl_mp (hn : Nest K) {L : Set (Set α)} (hL : L ⊆ K) {A : Set α}
    (h : minP (incl K) A L) : A ∈ L ∧ A = prodCls L := by
  obtain ⟨⟨hAL, hAf⟩, h⟩ := minP_iff.1 h
  have hAK := fld_incl_sub hAf
  refine ⟨hAL, Set.Subset.antisymm (fun x hx B hB => ?_) (fun x hx => hx A hAL)⟩
  exact (not_incl hn (hL hB) hAK).1 (h B hB) hx

private theorem min_incl (hn : Nest K) (h1 : K ∉ one) {L : Set (Set α)} (hL : L ⊆ K)
    {A : Set α} : minP (incl K) A L ↔ A ∈ L ∧ A = prodCls L := by
  refine ⟨min_incl_mp hn hL, ?_⟩
  rintro ⟨hAL, rfl⟩
  refine minP_iff.2 ⟨⟨hAL, by rw [fld_incl hn h1]; exact hL hAL⟩, fun B hB => ?_⟩
  exact (not_incl hn (hL hB) (hL hAL)).2 (fun x hx => hx B hB)

private theorem max_incl_mp (hn : Nest K) {L : Set (Set α)} (hL : L ⊆ K) {A : Set α}
    (h : maxP (incl K) A L) : A ∈ L ∧ A = sumCls L := by
  obtain ⟨⟨hAL, hAf⟩, h⟩ := maxP_iff.1 h
  have hAK := fld_incl_sub hAf
  refine ⟨hAL, Set.Subset.antisymm (fun x hx => ⟨A, hAL, hx⟩) (fun x hx => ?_)⟩
  obtain ⟨B, hB, hx⟩ := hx
  exact (not_incl hn hAK (hL hB)).1 (h B hB) hx

private theorem max_incl (hn : Nest K) (h1 : K ∉ one) {L : Set (Set α)} (hL : L ⊆ K)
    {A : Set α} : maxP (incl K) A L ↔ A ∈ L ∧ A = sumCls L := by
  refine ⟨max_incl_mp hn hL, ?_⟩
  rintro ⟨hAL, rfl⟩
  refine maxP_iff.2 ⟨⟨hAL, by rw [fld_incl hn h1]; exact hL hAL⟩, fun B hB => ?_⟩
  exact (not_incl hn (hL hAL) (hL hB)).2 (fun x hx => ⟨B, hB, hx⟩)

private theorem min_incl_inter {L : Set (Set α)} {A : Set α} :
    minP (incl K) A L ↔ minP (incl K) A (L ∩ K) := by
  rw [minP_iff, minP_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨h1, fld_incl_sub h2⟩, h2⟩, fun y hy => h3 y hy.1⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1.1, h2⟩, fun y hy hyA => h3 y ⟨hy, hyA.1.1.1⟩ hyA⟩

private theorem max_incl_inter {L : Set (Set α)} {A : Set α} :
    maxP (incl K) A L ↔ maxP (incl K) A (L ∩ K) := by
  rw [maxP_iff, maxP_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨h1, fld_incl_sub h2⟩, h2⟩, fun y hy => h3 y hy.1⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1.1, h2⟩, fun y hy hyA => h3 y ⟨hy, hyA.1.1.2⟩ hyA⟩

private theorem inter_fld_incl {L : Set (Set α)} :
    (L ∩ K) ∩ fld (incl K) = L ∩ fld (incl K) := by
  ext B
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fld_incl_sub h.2⟩, h.2⟩⟩

private theorem seq_incl_inter {L : Set (Set α)} {A : Set α} :
    seqP (incl K) A L ↔ seqP (incl K) A (L ∩ K) := by
  unfold seqP
  rw [inter_fld_incl]

private theorem prec_incl_inter {L : Set (Set α)} {A : Set α} :
    precP (incl K) A L ↔ precP (incl K) A (L ∩ K) := by
  unfold precP
  rw [inter_fld_incl]

private theorem prec_incl (hn : Nest K) (h1 : K ∉ one) {L : Set (Set α)} (hL : L ⊆ K)
    (hp : prodCls L ∉ L) {A : Set α} :
    precP (incl K) A L ↔ A ∈ K ∩ cl (prodCls L) ∧ A = sumCls (K ∩ cl (prodCls L)) := by
  have hLf : L ∩ fld (incl K) = L := by
    rw [fld_incl hn h1]; exact Set.inter_eq_left.2 hL
  have hU : prodCls (Rfwd (incl K) ʻʻ (L ∩ fld (incl K))) ∩ K = K ∩ cl (prodCls L) := by
    rw [hLf]
    ext C
    rw [Set.mem_inter_iff, mem_prodCls_Rfwd]
    constructor
    · rintro ⟨h, hC⟩
      exact ⟨hC, fun x hx B hB => (h B hB).1.2 hx⟩
    · rintro ⟨hC, hCp⟩
      refine ⟨fun B hB => ⟨⟨⟨hC, hL hB⟩, fun x hx => hCp hx B hB⟩, fun e => hp ?_⟩, hC⟩
      have : prodCls L = B := Set.Subset.antisymm (fun x hx => hx B hB) (e ▸ hCp)
      exact this ▸ hB
  show maxP (incl K) A _ ↔ _
  rw [max_incl_inter, hU, max_incl hn h1 Set.inter_subset_left]

private theorem up_sub {L : Set (Set α)} : {C | C ∈ K ∧ sumCls L ⊆ C} ⊆ K := fun _ hC => hC.1

private theorem seq_incl (hn : Nest K) (h1 : K ∉ one) {L : Set (Set α)} (hL : L ⊆ K)
    (hs : sumCls L ∉ L) {A : Set α} :
    seqP (incl K) A L ↔ A ∈ {C | C ∈ K ∧ sumCls L ⊆ C} ∧
      A = prodCls {C | C ∈ K ∧ sumCls L ⊆ C} := by
  have hLf : L ∩ fld (incl K) = L := by
    rw [fld_incl hn h1]; exact Set.inter_eq_left.2 hL
  have hU : prodCls (Rbwd (incl K) ʻʻ (L ∩ fld (incl K))) ∩ K =
      {C | C ∈ K ∧ sumCls L ⊆ C} := by
    rw [hLf]
    ext C
    rw [Set.mem_inter_iff, mem_prodCls_Rbwd]
    constructor
    · rintro ⟨h, hC⟩
      refine ⟨hC, fun x hx => ?_⟩
      obtain ⟨B, hB, hx⟩ := hx
      exact (h B hB).1.2 hx
    · rintro ⟨hC, hCs⟩
      refine ⟨fun B hB => ⟨⟨⟨hL hB, hC⟩, fun x hx => hCs ⟨B, hB, hx⟩⟩, fun e => hs ?_⟩, hC⟩
      have : sumCls L = B := Set.Subset.antisymm (e ▸ hCs) (fun x hx => ⟨B, hB, hx⟩)
      exact this ▸ hB
  show minP (incl K) A _ ↔ _
  rw [min_incl_inter, hU, min_incl hn h1 up_sub]


private theorem dom_incl (hn : Nest K) : dom (incl K) = K \ ι (sumCls K) := by
  ext A
  constructor
  · rintro ⟨B, h⟩
    obtain ⟨⟨hA, hB⟩, x, hxB, hxA⟩ := (incl_iff hn).1 h
    refine ⟨hA, fun e => hxA ?_⟩
    have e' : A = sumCls K := e
    rw [e']
    exact ⟨B, hB, hxB⟩
  · rintro ⟨hA, hne⟩
    have : ¬ sumCls K ⊆ A := fun hs => hne (Set.Subset.antisymm (fun x hx => ⟨A, hA, hx⟩) hs)
    obtain ⟨x, hx, hxA⟩ := Set.not_subset.1 this
    obtain ⟨B, hB, hxB⟩ := hx
    exact ⟨B, (incl_iff hn).2 ⟨⟨hA, hB⟩, x, hxB, hxA⟩⟩

private theorem codom_incl (hn : Nest K) : codom (incl K) = K \ ι (prodCls K) := by
  ext B
  constructor
  · rintro ⟨A, h⟩
    obtain ⟨⟨hA, hB⟩, x, hxB, hxA⟩ := (incl_iff hn).1 h
    refine ⟨hB, fun e => hxA ?_⟩
    have e' : B = prodCls K := e
    rw [e'] at hxB
    exact hxB A hA
  · rintro ⟨hB, hne⟩
    have : ¬ B ⊆ prodCls K := fun hs => hne (Set.Subset.antisymm hs (fun x hx => hx B hB))
    obtain ⟨x, hxB, hx⟩ := Set.not_subset.1 this
    have : ∃ A, A ∈ K ∧ x ∉ A := by
      by_contra hc
      push Not at hc
      exact hx hc
    obtain ⟨A, hA, hxA⟩ := this
    exact ⟨A, (incl_iff hn).2 ⟨⟨hA, hB⟩, x, hxB, hxA⟩⟩

private theorem min_eq_of (hn : Nest K) (h1 : K ∉ one) {L : Set (Set α)} (hL : L ⊆ K)
    (hp : prodCls L ∈ L) (A : Set α) : minP (incl K) A L ↔ A = prodCls L := by
  rw [min_incl hn h1 hL]
  exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hp, h⟩⟩

private theorem max_eq_of (hn : Nest K) (h1 : K ∉ one) {L : Set (Set α)} (hL : L ⊆ K)
    (hs : sumCls L ∈ L) (A : Set α) : maxP (incl K) A L ↔ A = sumCls L := by
  rw [max_incl hn h1 hL]
  exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hs, h⟩⟩

private theorem nomin_of (hn : Nest K) {L : Set (Set α)} (hL : L ⊆ K) (hp : prodCls L ∉ L) :
    ¬∃ y, minP (incl K) y L := by
  rintro ⟨y, hy⟩
  obtain ⟨hyL, rfl⟩ := min_incl_mp hn hL hy
  exact hp hyL

private theorem nomax_of (hn : Nest K) {L : Set (Set α)} (hL : L ⊆ K) (hs : sumCls L ∉ L) :
    ¬∃ y, maxP (incl K) y L := by
  rintro ⟨y, hy⟩
  obtain ⟨hyL, rfl⟩ := max_incl_mp hn hL hy
  exact hs hyL

/-- `prec_Q'λ = s'(κ ∩ Cl'p'λ)` when this sum is a member of `κ` and `p'λ ∉ λ`. -/
private theorem prec_eq_of (hn : Nest K) (h1 : K ∉ one) {L : Set (Set α)} (hL : L ⊆ K)
    (hp : prodCls L ∉ L) (hs : sumCls (K ∩ cl (prodCls L)) ∈ K) (A : Set α) :
    precP (incl K) A L ↔ A = sumCls (K ∩ cl (prodCls L)) := by
  rw [prec_incl hn h1 hL hp]
  have hm : sumCls (K ∩ cl (prodCls L)) ∈ K ∩ cl (prodCls L) := by
    refine ⟨hs, fun x hx => ?_⟩
    obtain ⟨C, hC, hx⟩ := hx
    exact hC.2 hx
  exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hm, h⟩⟩

/-- `seq_Q'λ = p'α̂(α ∈ κ . s'λ ⊂ α)` when this product is a member of `κ` and `s'λ ∉ λ`. -/
private theorem seq_eq_of (hn : Nest K) (h1 : K ∉ one) {L : Set (Set α)} (hL : L ⊆ K)
    (hs : sumCls L ∉ L) (hp : prodCls {C | C ∈ K ∧ sumCls L ⊆ C} ∈ K) (A : Set α) :
    seqP (incl K) A L ↔ A = prodCls {C | C ∈ K ∧ sumCls L ⊆ C} := by
  rw [seq_incl hn h1 hL hs]
  have hm : prodCls {C | C ∈ K ∧ sumCls L ⊆ C} ∈ {C | C ∈ K ∧ sumCls L ⊆ C} :=
    ⟨hp, fun x hx C hC => hC.2 hx⟩
  exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hm, h⟩⟩

private theorem sum_cl_prod {L : Set (Set α)} (hp : prodCls L ∈ K) :
    sumCls (K ∩ cl (prodCls L)) = prodCls L := by
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ⟨_, ⟨hp, mem_cl.2 subset_rfl⟩, hx⟩)
  obtain ⟨C, hC, hx⟩ := hx
  exact hC.2 hx

private theorem prod_up_sum {L : Set (Set α)} (hs : sumCls L ∈ K) :
    prodCls {C | C ∈ K ∧ sumCls L ⊆ C} = sumCls L :=
  Set.Subset.antisymm (fun _ hx => hx _ ⟨hs, subset_rfl⟩) (fun _ hx _ hC => hC.2 hx)

private theorem limax_of {P : α → α → Prop} {L : Set α}
    (h : L ∈ codom (maxP P) ∪ codom (seqP P)) : L ∈ codom (limaxP P) := by
  rcases h with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact ⟨x, Or.inl hx⟩
  · by_cases hm : ∃ y, maxP P y L
    · obtain ⟨y, hy⟩ := hm
      exact ⟨y, Or.inl hy⟩
    · exact ⟨x, Or.inr ⟨hx, hm⟩⟩

private theorem limin_of {P : α → α → Prop} {L : Set α}
    (h : L ∈ codom (minP P) ∪ codom (precP P)) : L ∈ codom (liminP P) := by
  rcases h with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact ⟨x, Or.inl hx⟩
  · by_cases hm : ∃ y, minP P y L
    · obtain ⟨y, hy⟩ := hm
      exact ⟨y, Or.inl hy⟩
    · exact ⟨x, Or.inr ⟨hx, hm⟩⟩

/-- From existence for the sub-classes of `κ` to existence for all classes (✱205·15, ✱206·131). -/
private theorem all_of_sub
    (h : ∀ L, L ⊆ K → (refs (maxP (incl K)) L ∪ refs (seqP (incl K)) L).Nonempty ∧
      (refs (minP (incl K)) L ∪ refs (precP (incl K)) L).Nonempty) (L : Set (Set α)) :
    L ∈ (codom (maxP (incl K)) ∪ codom (seqP (incl K))) ∩
      (codom (minP (incl K)) ∪ codom (precP (incl K))) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h (L ∩ K) Set.inter_subset_right
  constructor
  · rcases hx with hx | hx
    · exact Or.inl ⟨x, max_incl_inter.2 hx⟩
    · exact Or.inr ⟨x, seq_incl_inter.2 hx⟩
  · rcases hy with hy | hy
    · exact Or.inl ⟨y, min_incl_inter.2 hy⟩
    · exact Or.inr ⟨y, prec_incl_inter.2 hy⟩

/-- The case `p'λ ∩ s'κ ∈ κ` (✱210·252). -/
private theorem limin_prodsum (hn : Nest K) (h1 : K ∉ one) {L : Set (Set α)} (hL : L ⊆ K)
    (hK : prodCls L ∩ sumCls K ∈ K) :
    prodCls L ∩ sumCls K ∈ refs (minP (incl K)) L ∪ refs (precP (incl K)) L ∧
      ∀ A, liminP (incl K) A L ↔ A = prodCls L ∩ sumCls K := by
  by_cases hpL : prodCls L ∈ L
  · have e : prodCls L ∩ sumCls K = prodCls L :=
      Set.inter_eq_left.2 (fun x hx => ⟨_, hL hpL, hx⟩)
    rw [e]
    have hmin := min_eq_of hn h1 hL hpL
    refine ⟨Or.inl ((hmin _).2 rfl), fun A => ⟨fun h => ?_, fun h => Or.inl ((hmin A).2 h)⟩⟩
    rcases h with h | h
    · exact (hmin A).1 h
    · exact absurd ⟨_, (hmin _).2 rfl⟩ h.2
  · have hs : sumCls (K ∩ cl (prodCls L)) = prodCls L ∩ sumCls K := by
      refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ⟨_, ⟨hK, Set.inter_subset_left⟩, hx⟩)
      obtain ⟨C, hC, hx⟩ := hx
      exact ⟨hC.2 hx, C, hC.1, hx⟩
    have hprec := prec_eq_of hn h1 hL hpL (hs ▸ hK)
    rw [hs] at hprec
    have hnm := nomin_of hn hL hpL
    refine ⟨Or.inr ((hprec _).2 rfl), fun A => ⟨fun h => ?_, fun h => Or.inr ⟨(hprec A).2 h, hnm⟩⟩⟩
    rcases h with h | h
    · exact absurd ⟨A, h⟩ hnm
    · exact (hprec A).1 h.1

/-- The case `s'κ ∩ p'α̂(α ∈ κ . s'λ ⊂ α) ∈ κ` (✱210·262). -/
private theorem seq_prodsum (hn : Nest K) (h1 : K ∉ one) {L : Set (Set α)} (hL : L ⊆ K)
    (hsL : sumCls L ∉ L) (hK : sumCls K ∩ prodCls {C | C ∈ K ∧ sumCls L ⊆ C} ∈ K) (A : Set α) :
    seqP (incl K) A L ↔ A = sumCls K ∩ prodCls {C | C ∈ K ∧ sumCls L ⊆ C} := by
  have hne : ({C | C ∈ K ∧ sumCls L ⊆ C} : Set (Set α)).Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty] at h0
    rw [h0] at hK
    have : sumCls K ∩ prodCls (∅ : Set (Set α)) = sumCls K :=
      Set.inter_eq_left.2 (fun _ _ C hC => absurd hC (Set.notMem_empty C))
    rw [this] at hK
    have hmem : sumCls K ∈ ({C | C ∈ K ∧ sumCls L ⊆ C} : Set (Set α)) := by
      refine ⟨hK, fun x hx => ?_⟩
      obtain ⟨D, hD, hx⟩ := hx
      exact ⟨D, hL hD, hx⟩
    rw [h0] at hmem
    exact Set.notMem_empty _ hmem
  obtain ⟨C₀, hC₀⟩ := hne
  have e : sumCls K ∩ prodCls {C | C ∈ K ∧ sumCls L ⊆ C} = prodCls {C | C ∈ K ∧ sumCls L ⊆ C} :=
    Set.inter_eq_right.2 (fun x hx => ⟨C₀, hC₀.1, hx C₀ hC₀⟩)
  rw [e] at hK ⊢
  exact seq_eq_of hn h1 hL hsL hK A

end H210

/-!
## [✱210] On series of classes generated by the relation of inclusion

*(Vol. 2, p. 615)*

> *Summary of* *210.
>
> In the theory of series it frequently happens that we have to deal with a class of classes such that, of any two, one is contained in the other. *I.e.* if \(\kappa\) is the class of classes, we have \[ \alpha ,\beta \in \kappa .\supset _{\alpha ,\beta }:\alpha \subset \beta .\lor.\beta \subset \alpha . \]
>
> Instances of this are afforded by the various classes of sections, to be considered in *211. When \(\kappa\) fulfils the above condition, the classes composing \(\kappa\) can be arranged in a series by the relation of inclusion (combined with inequality), *i.e.* by the relation \[ \hat{\alpha} \hat{\beta} (\alpha ,\beta \in \kappa .\alpha \subset \beta .\alpha \neq \beta ), \] or, what comes to the same, \[ \hat{\alpha} \hat{\beta} (\alpha ,\beta \in \kappa .\exists !\beta -\alpha ). \] If \(P\) is any relation such that \(\kappa \subset \text{Cl}ʻCʻP\), the above relation of inclusion is equal to \[ P_{\text{lc}}\unicode{x0294f}\kappa . \] (For the definition of \(P_{\text{lc}}\), see *170.) Thus under the above circumstances, \(P_{\text{lc}}\unicode{x0294f}\kappa\) is a series, whatever \(P\) may be.
>
> …

**Lean reading.** `κ` is a class of classes `K : Set (Set α)` and `Q : Set α → Set α → Prop`.
PM's abbreviated hypotheses are written out in every statement: Hp ✱210·1 (`κ` is nested,
`∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C`), Hp ✱210·11 (`Q = fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧
C ≠ D`), Hp ✱210·12 (their product), Hp ✱210·2 (adds `K ∉ one`), and Hp ✱210·251·252 (add
`∀ M, M ⊆ K → sumCls M ∈ K`, resp. `∀ M, M ⊆ K → prodCls M ∩ sumCls K ∈ K`). `min_Q'λ = …`,
`prec_Q'λ`, `limin_Q'λ`, `B'Q` are descriptions (`Desc`), `min⃗_Q'λ` is `refs (minP Q) L`,
`Cl'p'λ` is `cl (prodCls L)`, `s''Cl'κ` is `sRel ʻʻ cl K` and `p''Cl'κ` is `graph prodCls ʻʻ cl K`.
The proofs characterize, through the private `incl K` (PM's `Q`), the minima, maxima, sequents and
precedents of sub-classes of `κ` by `p'λ`, `s'λ`, `s'(κ ∩ Cl'p'λ)` and `p'α̂(α ∈ κ . s'λ ⊂ α)`.

**Status.** proved (all propositions; ✱210·17, ✱210·232, ✱210·233, ✱210·251, ✱210·252,
✱210·261, ✱210·29, ✱210·291 proved (reading): misprints of the e-text, see their docstrings)
-/

/-- ✱210·1. \(\vdash \colon\colon\alpha ,\beta \in \kappa .\supset _{\alpha ,\beta }:\alpha \subset \beta .\lor.\beta \subset \alpha \colon\ldotp \supset \colon\ldotp \alpha ,\beta \in \kappa .\supset :\alpha \subset \beta .\alpha \neq \beta .\equiv .\exists !\beta -\alpha\) -/
theorem pm210_1 {α : Type u} {K : Set (Set α)} {A B : Set α} :
    (∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) → (A ∈ K ∧ B ∈ K → (A ⊆ B ∧ A ≠ B ↔ (B \ A).Nonempty)) :=
  fun hn ⟨hA, hB⟩ => ssub_iff hn hA hB

/-- ✱210·11. \(\vdash :Q=\hat{\alpha} \hat{\beta} (\alpha ,\beta \in \kappa .\alpha \subset \beta .\alpha \neq \beta ).\supset .Q\in \text{trans}\cap \text{Rl}ʻJ\) -/
theorem pm210_11 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} : Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D) → Q ∈ transR ∩ rl J := by
  intro hQ
  obtain rfl : Q = incl K := hQ
  refine ⟨mem_transR.2 fun A B C ⟨h1, h2⟩ => ⟨⟨⟨h1.1.1.1, h2.1.1.2⟩, h1.1.2.trans h2.1.2⟩, ?_⟩,
    mem_rl_J.2 fun A h => h.2 rfl⟩
  intro e
  subst e
  exact h1.2 (Set.Subset.antisymm h1.1.2 h2.1.2)

/-- ✱210·12. \(\vdash :\text{Hp}*210·1·11.\supset .Q\in \text{Ser}\) -/
theorem pm210_12 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} : ((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) → Q ∈ Ser := by
  rintro ⟨hn, hQ⟩
  obtain rfl : Q = incl K := hQ
  exact incl_ser hn

/-- ✱210·121. \(\vdash : \text{Hp} *210·12 . \supset . \text{D}ʻQ = \kappa - \iota ʻsʻ\kappa . \text{ᗡ}ʻQ = \kappa - \iota ʻpʻ\kappa\) -/
theorem pm210_121 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) → dom Q = K \ ι (sumCls K) ∧ codom Q = K \ ι (prodCls K) := by
  rintro ⟨hn, hQ⟩
  obtain rfl : Q = incl K := hQ
  exact ⟨dom_incl hn, codom_incl hn⟩

/-- ✱210·122. \(\vdash : \text{Hp} *210·12 . \kappa {\sim} \in 1 . \supset . CʻQ = \kappa\) -/
theorem pm210_122 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} : ((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one → fld Q = K := by
  rintro ⟨⟨hn, hQ⟩, h1⟩
  obtain rfl : Q = incl K := hQ
  exact fld_incl hn h1

/-- ✱210·123. \(\vdash : \text{Hp} *210·12 . \kappa \in 0 \cup 1 . \supset . Q = \dot{\Lambda}\) -/
theorem pm210_123 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} : ((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∈ zero ∪ one → Q = rNull := by
  rintro ⟨⟨hn, hQ⟩, h0⟩
  obtain rfl : Q = incl K := hQ
  funext A B
  apply propext
  refine ⟨fun h => ?_, fun h => (rNull_apply _ _ h).elim⟩
  exfalso
  obtain ⟨⟨⟨hA, hB⟩, -⟩, hne⟩ := h
  rcases h0 with h0 | h0
  · have e : K = Λ := h0
    rw [e, Null_eq_empty] at hA
    exact Set.notMem_empty _ hA
  · obtain ⟨b, hb⟩ := mem_one_iff.1 h0
    exact hne (((hb A).1 hA).trans ((hb B).1 hB).symm)

/-- ✱210·124. \(\vdash \colon\ldotp \text{Hp} *210·12 . \supset : \alpha Q\beta . \equiv . \alpha , \beta \in \kappa . \exists ! \beta - \alpha \quad[*210·1]\) -/
theorem pm210_124 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {A B : Set α} :
    ((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) → (Q A B ↔ (A ∈ K ∧ B ∈ K) ∧ (B \ A).Nonempty) := by
  rintro ⟨hn, hQ⟩
  obtain rfl : Q = incl K := hQ
  exact incl_iff hn

/-- ✱210·13. \(\vdash : \text{Hp} *210·12 . \kappa \subset \text{Cl}ʻCʻP . \supset . Q = P_{\text{lc}} \unicode{x0294f} \kappa\) -/
theorem pm210_13 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {P : α → α → Prop} : ((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ⊆ cl (fld P) → Q = Plc P ⥏ K := by
  rintro ⟨⟨hn, hQ⟩, hK⟩
  obtain rfl : Q = incl K := hQ
  funext A B
  apply propext
  show incl K A B ↔ (A ∈ K ∧ Plc P A B) ∧ B ∈ K
  rw [incl_iff hn, Plc_iff]
  constructor
  · rintro ⟨⟨hA, hB⟩, x, hxB, hxA⟩
    refine ⟨⟨hA, ⟨hK hA, hK hB⟩, x, ⟨hxB, hxA⟩, ?_⟩, hB⟩
    rintro ⟨y, ⟨hyA, hyB⟩, -⟩
    rcases hn A B ⟨hA, hB⟩ with h | h
    · exact hyB (h hyA)
    · exact hxA (h hxB)
  · rintro ⟨⟨hA, -, x, ⟨hxB, hxA⟩, -⟩, hB⟩
    exact ⟨⟨hA, hB⟩, x, hxB, hxA⟩

/-- ✱210·14. \[\begin{align}&\vdash :\text{Hp}*210·1.\kappa \subset \text{Cl}ʻCʻP.\supset .P_{\text{lc}}\unicode{x0294f}\kappa \in \text{Ser}\\ &[*210·12·13]\end{align}\] -/
theorem pm210_14 {α : Type u} {K : Set (Set α)} {P : α → α → Prop} :
    (∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ K ⊆ cl (fld P) → Plc P ⥏ K ∈ Ser := by
  rintro ⟨hn, hK⟩
  rw [← pm210_13 ⟨⟨hn, rfl⟩, hK⟩]
  exact incl_ser hn

/-- ✱210·15. \[\begin{align}&\vdash \colon\ldotp \text{Hp}*210·12.\alpha ,\beta \in \kappa .\supset :{\sim}(\alpha Q\beta ).\equiv .\beta \subset \alpha \\ &[*210·124.*24·55]\end{align}\] -/
theorem pm210_15 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {A B : Set α} :
    ((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ (A ∈ K ∧ B ∈ K) → (¬ Q A B ↔ B ⊆ A) := by
  rintro ⟨⟨hn, hQ⟩, hA, hB⟩
  obtain rfl : Q = incl K := hQ
  exact not_incl hn hA hB

/-- ✱210·16. \[\begin{align}&\vdash \colon\colon\text{Hp}*210·1.\supset \colon\ldotp \\ &\alpha \in \kappa .\lambda \subset \kappa .\supset :\alpha \subset pʻ\lambda .\lor.pʻ\lambda \subset \alpha :\alpha \subset sʻ\lambda .\lor.sʻ\lambda \subset \alpha\end{align}\] -/
theorem pm210_16 {α : Type u} {K L : Set (Set α)} {A : Set α} :
    (∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) → (A ∈ K ∧ L ⊆ K →
      (A ⊆ prodCls L ∨ prodCls L ⊆ A) ∧ (A ⊆ sumCls L ∨ sumCls L ⊆ A)) := by
  rintro hn ⟨hA, hL⟩
  constructor
  · by_cases h : ∀ B, B ∈ L → A ⊆ B
    · exact Or.inl fun x hx B hB => h B hB hx
    · push Not at h
      obtain ⟨B, hB, hAB⟩ := h
      rcases hn A B ⟨hA, hL hB⟩ with h' | h'
      · exact absurd h' hAB
      · exact Or.inr fun x hx => h' (hx B hB)
  · by_cases h : ∀ B, B ∈ L → B ⊆ A
    · refine Or.inr fun x hx => ?_
      obtain ⟨B, hB, hx⟩ := hx
      exact h B hB hx
    · push Not at h
      obtain ⟨B, hB, hAB⟩ := h
      rcases hn A B ⟨hA, hL hB⟩ with h' | h'
      · exact Or.inl fun x hx => ⟨B, hB, h' hx⟩
      · exact absurd h' hAB

/-- ✱210·17. \[\begin{align}\vdash :\text{Hp}*210·12.&\lambda \subset \kappa .\supset .\\ &\kappa -\breve{Q} ʻʻ\lambda =\kappa \cap \text{Cl}ʻpʻ\lambda .\kappa -Qʻʻ\lambda =\kappa \cap \hat{\gamma} (sʻ\lambda \subset y)\end{align}\]

**Status.** proved (reading): the e-text prints `γ̂(s'λ ⊂ y)` for `γ̂(s'λ ⊂ γ)` (line (3) of the demonstration); the class is read `{G | s'λ ⊆ G}`. -/
theorem pm210_17 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    ((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ L ⊆ K →
      K \ Q˘ ʻʻ L = K ∩ cl (prodCls L) ∧ K \ Q ʻʻ L = K ∩ {G | sumCls L ⊆ G} := by
  rintro ⟨⟨hn, hQ⟩, hL⟩
  obtain rfl : Q = incl K := hQ
  constructor
  · ext A
    constructor
    · rintro ⟨hA, hn'⟩
      refine ⟨hA, fun x hx B hB => ?_⟩
      have : ¬ incl K B A := fun h => hn' ⟨B, hB, h⟩
      exact (not_incl hn (hL hB) hA).1 this hx
    · rintro ⟨hA, hp⟩
      refine ⟨hA, ?_⟩
      rintro ⟨B, hB, h⟩
      exact (not_incl hn (hL hB) hA).2 (fun x hx => hp hx B hB) h
  · ext A
    constructor
    · rintro ⟨hA, hn'⟩
      refine ⟨hA, fun x hx => ?_⟩
      obtain ⟨B, hB, hx⟩ := hx
      have : ¬ incl K A B := fun h => hn' ⟨B, hB, h⟩
      exact (not_incl hn hA (hL hB)).1 this hx
    · rintro ⟨hA, hs⟩
      refine ⟨hA, ?_⟩
      rintro ⟨B, hB, h⟩
      exact (not_incl hn hA (hL hB)).2 (fun x hx => hs ⟨B, hB, hx⟩) h

/-- ✱210·2. \(\vdash :\text{Hp}*210·12.\kappa {\sim}\in 1.\supset .\overrightarrow{\text{min}}_{Q}ʻ\lambda =\lambda \cap \kappa \cap \iota ʻpʻ(\lambda \cap \kappa )\) -/
theorem pm210_2 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) → refs (minP Q) L = L ∩ K ∩ ι (prodCls (L ∩ K)) := by
  rintro ⟨⟨hn, hQ⟩, h1⟩
  obtain rfl : Q = incl K := hQ
  ext A
  show minP (incl K) A L ↔ _
  rw [min_incl_inter, min_incl hn h1 Set.inter_subset_right]
  exact Iff.rfl

/-- ✱210·201. \[\begin{align}&\vdash : \text{Hp} *210·2 . \lambda \subset \kappa . \supset . \overrightarrow{\text{min}}_{Q}ʻ\lambda = \lambda \cap \iota ʻp ʻ\lambda \\ &[*210·2 . *22·621]\end{align}\] -/
theorem pm210_201 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K → refs (minP Q) L = L ∩ ι (prodCls L) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩
  obtain rfl : Q = incl K := hQ
  ext A
  show minP (incl K) A L ↔ _
  rw [min_incl hn h1 hL]
  exact Iff.rfl

/-- ✱210·202. \[\begin{align}&\vdash : \text{Hp} *210·2 . \supset . \overrightarrow{\text{max}}_{Q}ʻ\lambda = \lambda \cap \kappa \cap {℩}ʻsʻ(\lambda \cap \kappa )\\ &[\text{Proof as in *210·2}]\end{align}\] -/
theorem pm210_202 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) → refs (maxP Q) L = L ∩ K ∩ ι (sumCls (L ∩ K)) := by
  rintro ⟨⟨hn, hQ⟩, h1⟩
  obtain rfl : Q = incl K := hQ
  ext A
  show maxP (incl K) A L ↔ _
  rw [max_incl_inter, max_incl hn h1 Set.inter_subset_right]
  exact Iff.rfl

/-- ✱210·203. \[\begin{align}&\vdash : \text{Hp} *210·2 . \lambda \subset \kappa . \supset . \overrightarrow{\text{max}}_{Q}ʻ\lambda = \lambda \cap {℩}ʻsʻ\lambda \\ &[*210·202 . *22·621]\end{align}\] -/
theorem pm210_203 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K → refs (maxP Q) L = L ∩ ι (sumCls L) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩
  obtain rfl : Q = incl K := hQ
  ext A
  show maxP (incl K) A L ↔ _
  rw [max_incl hn h1 hL]
  exact Iff.rfl

/-- ✱210·21. \[\begin{align}&\vdash : \text{Hp} *210·2 . \lambda \subset \kappa . pʻ\lambda \in \lambda . \supset . \text{min}_{Q}ʻ\lambda = pʻ\lambda\\ &[*210·201 . *51·31]\end{align}\] -/
theorem pm210_21 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K) ∧ prodCls L ∈ L → Desc (minP Q) L (fun A => A = prodCls L) := by
  rintro ⟨⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩, hp⟩
  obtain rfl : Q = incl K := hQ
  exact desc_of (min_eq_of hn h1 hL hp) rfl

/-- ✱210·211. \[\begin{align}&\vdash : \text{Hp} *210·2 . \lambda \subset \kappa . sʻ\lambda \in \lambda . \supset . \text{max}_{Q}ʻ\lambda = sʻ\lambda\\ &[*210·203 . *51·31]\end{align}\] -/
theorem pm210_211 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K) ∧ sumCls L ∈ L → Desc (maxP Q) L (fun A => A = sumCls L) := by
  rintro ⟨⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩, hs⟩
  obtain rfl : Q = incl K := hQ
  exact desc_of (max_eq_of hn h1 hL hs) rfl

/-- ✱210·22. \[\begin{align}&\vdash : \text{Hp} *210·12 . \lambda \subset \kappa . pʻ\lambda {\sim} \in \lambda . \supset . {\sim} \exists ! \overrightarrow{\text{min}}_{Q}ʻ\lambda \\ &[*210·201·123 . *51·211]\end{align}\] -/
theorem pm210_22 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ L ⊆ K) ∧ prodCls L ∉ L → ¬ (refs (minP Q) L).Nonempty := by
  rintro ⟨⟨⟨hn, hQ⟩, hL⟩, hp⟩ ⟨A, hA⟩
  obtain rfl : Q = incl K := hQ
  exact nomin_of hn hL hp ⟨A, hA⟩

/-- ✱210·221. \[\begin{align}&\vdash : \text{Hp} *210·12 . \lambda \subset \kappa . sʻ\lambda {\sim} \in \lambda . \supset . {\sim} \exists ! \overrightarrow{\text{max}}_{Q}ʻ\lambda \\ &[*210·203·123 . *51·211]\end{align}\] -/
theorem pm210_221 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ L ⊆ K) ∧ sumCls L ∉ L → ¬ (refs (maxP Q) L).Nonempty := by
  rintro ⟨⟨⟨hn, hQ⟩, hL⟩, hs⟩ ⟨A, hA⟩
  obtain rfl : Q = incl K := hQ
  exact nomax_of hn hL hs ⟨A, hA⟩

/-- ✱210·222. \[\begin{align}&\vdash \colon\ldotp \text{Hp} *210·2 . \lambda \subset \kappa . \supset : pʻ\lambda \in \lambda . \equiv . \text{E}! \text{min}_{Q}ʻ\lambda \\ &[*210·21·22]\end{align}\] -/
theorem pm210_222 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K → (prodCls L ∈ L ↔ EDesc (minP Q) L) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩
  obtain rfl : Q = incl K := hQ
  refine ⟨fun hp => edesc_of (min_eq_of hn h1 hL hp), fun ⟨b, hb⟩ => ?_⟩
  obtain ⟨hbL, rfl⟩ := min_incl_mp hn hL ((hb b).2 rfl)
  exact hbL

/-- ✱210·223. \[\begin{align}&\vdash \colon\ldotp \text{Hp} *210·2 . \lambda \subset \kappa . \supset : sʻ\lambda \in \lambda . \equiv . \text{E}! \text{max}_{Q}ʻ\lambda\\ &[*210·211·221]\end{align}\] -/
theorem pm210_223 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K → (sumCls L ∈ L ↔ EDesc (maxP Q) L) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩
  obtain rfl : Q = incl K := hQ
  refine ⟨fun hs => edesc_of (max_eq_of hn h1 hL hs), fun ⟨b, hb⟩ => ?_⟩
  obtain ⟨hbL, rfl⟩ := max_incl_mp hn hL ((hb b).2 rfl)
  exact hbL

/-- ✱210·23. \(\vdash : \text{Hp} *210·2 . \lambda \subset \kappa . pʻ\lambda \in \kappa - \lambda . \supset . pʻ\lambda = \text{prec}_{Q}ʻ\lambda = \text{tl}_{Q}ʻ\lambda\) -/
theorem pm210_23 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K) ∧ prodCls L ∈ K \ L →
      Desc (precP Q) L (fun A => prodCls L = A) ∧
        Desc (precP Q) L (fun A => Desc (tlP Q) L (fun B => A = B)) := by
  rintro ⟨⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩, hp⟩
  obtain rfl : Q = incl K := hQ
  have hprec := prec_eq_of hn h1 hL hp.2 (by rw [sum_cl_prod hp.1]; exact hp.1)
  rw [sum_cl_prod hp.1] at hprec
  have htl : ∀ A, tlP (incl K) A L ↔ A = prodCls L :=
    fun A => (tl_iff_of (nomin_of hn hL hp.2)).trans (hprec A)
  exact ⟨desc_of hprec rfl, desc2_of hprec htl⟩

/-- ✱210·231. \[\begin{align}&\vdash :\text{Hp}*210·2.\lambda \subset \kappa .sʻ\lambda \in \kappa -\lambda .\supset .sʻ\lambda =\text{seq}_{Q}ʻ\lambda =\text{lt}_{Q}ʻ\lambda \\ &[\text{Proof as in *210·23}]\end{align}\] -/
theorem pm210_231 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K) ∧ sumCls L ∈ K \ L →
      Desc (seqP Q) L (fun A => sumCls L = A) ∧
        Desc (seqP Q) L (fun A => Desc (ltP Q) L (fun B => A = B)) := by
  rintro ⟨⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩, hs⟩
  obtain rfl : Q = incl K := hQ
  have hseq := seq_eq_of hn h1 hL hs.2 (by rw [prod_up_sum hs.1]; exact hs.1)
  rw [prod_up_sum hs.1] at hseq
  have hlt : ∀ A, ltP (incl K) A L ↔ A = sumCls L :=
    fun A => (lt_iff_of (nomax_of hn hL hs.2)).trans (hseq A)
  exact ⟨desc_of hseq rfl, desc2_of hseq hlt⟩

/-- ✱210·232. \(\vdash :\text{Hp}*210·2.\lambda \subset \kappa .pʻ\lambda \in \kappa .\supset .pʻ\lambda =\text{limin}_Pʻ\lambda \quad[*210·21·23]\)

**Status.** proved (reading): `limin_P` is a misprint for `limin_Q` (`P` does not occur in the hypothesis; the Summary of ✱210 and the demonstration from ✱210·21·23 concern `Q`). -/
theorem pm210_232 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K) ∧ prodCls L ∈ K → Desc (liminP Q) L (fun A => prodCls L = A) := by
  rintro ⟨⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩, hp⟩
  obtain rfl : Q = incl K := hQ
  refine desc_of (fun A => ?_) rfl
  by_cases hpL : prodCls L ∈ L
  · have hmin := min_eq_of hn h1 hL hpL
    refine ⟨fun h => ?_, fun h => Or.inl ((hmin A).2 h)⟩
    rcases h with h | h
    · exact (hmin A).1 h
    · exact absurd ⟨_, (hmin _).2 rfl⟩ h.2
  · have hprec := prec_eq_of hn h1 hL hpL (by rw [sum_cl_prod hp]; exact hp)
    rw [sum_cl_prod hp] at hprec
    have hnm := nomin_of hn hL hpL
    refine ⟨fun h => ?_, fun h => Or.inr ⟨(hprec A).2 h, hnm⟩⟩
    rcases h with h | h
    · exact absurd ⟨A, h⟩ hnm
    · exact (hprec A).1 h.1

/-- ✱210·233. \(\vdash :\text{Hp}*210·2.\lambda \subset \kappa .sʻ\lambda \in \kappa .\supset .sʻ\lambda =\text{limax}_Pʻ\lambda \quad[*210·211·231]\)

**Status.** proved (reading): `limax_P` is a misprint for `limax_Q` (`P` does not occur in the hypothesis; the demonstration is from ✱210·211·231, which concern `Q`). -/
theorem pm210_233 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K) ∧ sumCls L ∈ K → Desc (limaxP Q) L (fun A => sumCls L = A) := by
  rintro ⟨⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩, hs⟩
  obtain rfl : Q = incl K := hQ
  refine desc_of (fun A => ?_) rfl
  by_cases hsL : sumCls L ∈ L
  · have hmax := max_eq_of hn h1 hL hsL
    refine ⟨fun h => ?_, fun h => Or.inl ((hmax A).2 h)⟩
    rcases h with h | h
    · exact (hmax A).1 h
    · exact absurd ⟨_, (hmax _).2 rfl⟩ h.2
  · have hseq := seq_eq_of hn h1 hL hsL (by rw [prod_up_sum hs]; exact hs)
    rw [prod_up_sum hs] at hseq
    have hnm := nomax_of hn hL hsL
    refine ⟨fun h => ?_, fun h => Or.inr ⟨(hseq A).2 h, hnm⟩⟩
    rcases h with h | h
    · exact absurd ⟨A, h⟩ hnm
    · exact (hseq A).1 h.1

/-- ✱210·24. \[\begin{align}&\vdash :\text{Hp}*210·2.\supset .\kappa \cap {℩}ʻpʻ\kappa =\overrightarrow{B}ʻQ.\kappa \cap {℩}ʻsʻ\kappa =\overrightarrow{B}ʻ\breve{Q} \\ &[*205·12·121.*210·201·203·122]\end{align}\] -/
theorem pm210_24 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) → K ∩ ι (prodCls K) = refs Beg Q ∧ K ∩ ι (sumCls K) = refs Beg Q˘ := by
  rintro ⟨⟨hn, hQ⟩, h1⟩
  obtain rfl : Q = incl K := hQ
  have hsing : ∀ A, A ∈ K → A = prodCls K → A = sumCls K → False := by
    intro A hA hp hs
    apply h1
    refine mem_one_iff.2 ⟨A, fun C => ⟨fun hC => ?_, fun e => e ▸ hA⟩⟩
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [hs]; exact ⟨C, hC, hx⟩
    · rw [hp] at hx; exact hx C hC
  constructor
  · ext A
    show A ∈ K ∩ ι (prodCls K) ↔ A ∈ dom (incl K) \ codom (incl K)
    rw [dom_incl hn, codom_incl hn]
    constructor
    · rintro ⟨hA, hAp⟩
      exact ⟨⟨hA, fun hAs => hsing A hA hAp hAs⟩, fun h => h.2 hAp⟩
    · rintro ⟨⟨hA, -⟩, h⟩
      refine ⟨hA, ?_⟩
      by_contra hc
      exact h ⟨hA, hc⟩
  · ext A
    show A ∈ K ∩ ι (sumCls K) ↔ A ∈ codom (incl K) \ dom (incl K)
    rw [dom_incl hn, codom_incl hn]
    constructor
    · rintro ⟨hA, hAs⟩
      exact ⟨⟨hA, fun hAp => hsing A hA hAp hAs⟩, fun h => h.2 hAs⟩
    · rintro ⟨⟨hA, -⟩, h⟩
      refine ⟨hA, ?_⟩
      by_contra hc
      exact h ⟨hA, hc⟩

/-- ✱210·241. \(\vdash :\text{Hp}*210·2.pʻ\kappa \in \kappa .\supset .pʻ\kappa =BʻQ \quad[*210·24]\) -/
theorem pm210_241 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} : (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ prodCls K ∈ K → Desc Beg Q (fun b => prodCls K = b) := by
  rintro ⟨h, hp⟩
  have e := (pm210_24 h).1
  refine desc_of (fun b => ?_) rfl
  have := Set.ext_iff.1 e b
  exact this.symm.trans ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hp, h⟩⟩

/-- ✱210·242. \(\vdash :\text{Hp}*210·2.sʻ\kappa \in \kappa .\supset .sʻ\kappa =Bʻ\breve{Q} \quad [*210·24]\) -/
theorem pm210_242 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} : (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ sumCls K ∈ K → Desc Beg Q˘ (fun b => sumCls K = b) := by
  rintro ⟨h, hs⟩
  have e := (pm210_24 h).2
  refine desc_of (fun b => ?_) rfl
  have := Set.ext_iff.1 e b
  exact this.symm.trans ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hs, h⟩⟩

/-- ✱210·25. \[\begin{align}\vdash \colon\ldotp \text{Hp}*210·2:\lambda \subset \kappa .\supset _{\lambda }.pʻ\lambda \in &\kappa :\supset :\\ &\lambda \subset \kappa .\supset .pʻ\lambda \in (\overrightarrow{\text{min}}_{Q}ʻ\lambda \cup \overrightarrow{\text{prec}} _{Q}ʻ\lambda )\end{align}\] -/
theorem pm210_25 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → prodCls M ∈ K) →
      (L ⊆ K → prodCls L ∈ refs (minP Q) L ∪ refs (precP Q) L) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hp⟩ hL
  obtain rfl : Q = incl K := hQ
  by_cases hpL : prodCls L ∈ L
  · exact Or.inl ((min_eq_of hn h1 hL hpL _).2 rfl)
  · have h2 := prec_eq_of hn h1 hL hpL (by rw [sum_cl_prod (hp L hL)]; exact hp L hL)
    rw [sum_cl_prod (hp L hL)] at h2
    exact Or.inr ((h2 _).2 rfl)

/-- ✱210·251. \[\begin{align}\vdash \colon\ldotp \text{Hp}*210·2:\lambda \subset \kappa .\supset _{\lambda }.sʻ\lambda \in &\kappa :\supset :\\ &\lambda \supset \kappa .\supset .sʻ\lambda \in (\overrightarrow{\text{max}}_{Q}ʻ\lambda \cup \overrightarrow{\text{seq}} _{Q}ʻ\lambda )\\ [\text{Proof as in *210·25}]\end{align}\]

**Status.** proved (reading): `λ ⊃ κ` in the consequent is a misprint for `λ ⊂ κ` (as in ✱210·25, whose proof this one copies). -/
theorem pm210_251 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → sumCls M ∈ K) →
      (L ⊆ K → sumCls L ∈ refs (maxP Q) L ∪ refs (seqP Q) L) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hs⟩ hL
  obtain rfl : Q = incl K := hQ
  by_cases hsL : sumCls L ∈ L
  · exact Or.inl ((max_eq_of hn h1 hL hsL _).2 rfl)
  · have h2 := seq_eq_of hn h1 hL hsL (by rw [prod_up_sum (hs L hL)]; exact hs L hL)
    rw [prod_up_sum (hs L hL)] at h2
    exact Or.inr ((h2 _).2 rfl)

/-- ✱210·252. \[\begin{align}\vdash \colon\ldotp &\text{Hp}*210·2:\lambda \subset \kappa .\supset _{\lambda }.pʻ\lambda \cap sʻ\kappa \in \kappa :\supset :\\ &\lambda \subset \kappa .\supset .pʻ\lambda \cap sʻ\kappa \in (\overrightarrow{\text{min}}_{Q}ʻ\lambda \cup \overrightarrow{\text{prec}} _{Q}ʻ\lambda ).pʻ\lambda \cap sʻ\kappa =\text{limin}_Pʻ\lambda\end{align}\]

**Status.** proved (reading): `limin_P` is a misprint for `limin_Q` (as in ✱210·232; `P` does not occur in the hypothesis). -/
theorem pm210_252 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → prodCls M ∩ sumCls K ∈ K) →
      (L ⊆ K → prodCls L ∩ sumCls K ∈ refs (minP Q) L ∪ refs (precP Q) L ∧
        Desc (liminP Q) L (fun A => prodCls L ∩ sumCls K = A)) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hK⟩ hL
  obtain rfl : Q = incl K := hQ
  obtain ⟨h, h'⟩ := limin_prodsum hn h1 hL (hK L hL)
  exact ⟨h, desc_of h' rfl⟩

/-- ✱210·253. \[\begin{align}&\vdash :\text{Hp}*210·252.\supset .(\lambda ).\lambda \in \text{ᗡ}ʻ\text{min}_{Q}\cup \text{ᗡ}ʻ\text{prec}_{Q}\\ &[*210·252.*205·15.*206·131]\end{align}\] -/
theorem pm210_253 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → prodCls M ∩ sumCls K ∈ K) →
      ∀ L, L ∈ codom (minP Q) ∪ codom (precP Q) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hK⟩ L
  obtain rfl : Q = incl K := hQ
  rcases (limin_prodsum hn h1 Set.inter_subset_right (hK _ Set.inter_subset_right)).1 with h | h
  · exact Or.inl ⟨_, min_incl_inter.2 h⟩
  · exact Or.inr ⟨_, prec_incl_inter.2 h⟩

/-- ✱210·254. \[\begin{align}&\vdash :\text{Hp}*210·251.\supset .(\lambda ).\lambda \in \text{ᗡ}ʻ\text{max}_{Q}\cup \text{ᗡ}ʻ\text{seq}_{Q}\\ &[\text{Proof as in *210·253}]\end{align}\] -/
theorem pm210_254 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → sumCls M ∈ K) → ∀ L, L ∈ codom (maxP Q) ∪ codom (seqP Q) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hs⟩ L
  obtain rfl : Q = incl K := hQ
  rcases pm210_251 (L := L ∩ K) ⟨⟨⟨hn, rfl⟩, h1⟩, hs⟩ Set.inter_subset_right with h' | h'
  · exact Or.inl ⟨_, max_incl_inter.2 h'⟩
  · exact Or.inr ⟨_, seq_incl_inter.2 h'⟩

/-- ✱210·26. \[\begin{align}\vdash :\text{Hp}*210·2.\lambda \subset \kappa .pʻ\lambda {\sim}\in \lambda .&sʻ(\kappa \cap \text{Cl}ʻpʻ\lambda )\in \kappa .\supset .\\ &sʻ(\kappa \cap \text{Cl}ʻpʻ\lambda )=\text{prec}_{Q}ʻ\lambda \end{align}\] -/
theorem pm210_26 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    (((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K) ∧ prodCls L ∉ L) ∧ sumCls (K ∩ cl (prodCls L)) ∈ K →
      Desc (precP Q) L (fun A => sumCls (K ∩ cl (prodCls L)) = A) := by
  rintro ⟨⟨⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩, hp⟩, hs⟩
  obtain rfl : Q = incl K := hQ
  exact desc_of (prec_eq_of hn h1 hL hp hs) rfl

/-- ✱210·261. \[\begin{align}\vdash :\text{Hp}*210·2.&\lambda \subset k.sʻ\lambda {\sim}\in \lambda .pʻ\hat{\alpha} (\alpha \in \kappa .sʻ\lambda \subset \alpha )\in \kappa .\supset .\\ &pʻ\hat{\alpha} (\alpha \in \kappa .sʻ\lambda \subset \alpha )=\text{seq}_{Q}ʻ\lambda \quad[\text{Proof as in *210·26}]\end{align}\]

**Status.** proved (reading): the e-text prints `λ ⊂ k` for `λ ⊂ κ`. -/
theorem pm210_261 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    (((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K) ∧ sumCls L ∉ L) ∧ prodCls {C | C ∈ K ∧ sumCls L ⊆ C} ∈ K →
      Desc (seqP Q) L (fun A => prodCls {C | C ∈ K ∧ sumCls L ⊆ C} = A) := by
  rintro ⟨⟨⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩, hs⟩, hp⟩
  obtain rfl : Q = incl K := hQ
  exact desc_of (seq_eq_of hn h1 hL hs hp) rfl

/-- ✱210·262. \[\begin{align}\vdash :\text{Hp}*210·2.\lambda \subset \kappa .sʻ\lambda {\sim}\in \lambda .&sʻ\kappa \cap pʻ\hat{\alpha} (\alpha \in \kappa .sʻ\lambda \subset \alpha )\in \kappa .\supset .\\ &sʻ\kappa \cap pʻ\hat{\alpha} (\alpha \in \kappa .sʻ\lambda \subset \alpha )=\text{seq}_{Q}ʻ\lambda \end{align}\] -/
theorem pm210_262 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} {L : Set (Set α)} :
    (((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ L ⊆ K) ∧ sumCls L ∉ L) ∧ sumCls K ∩ prodCls {C | C ∈ K ∧ sumCls L ⊆ C} ∈ K →
      Desc (seqP Q) L (fun A => sumCls K ∩ prodCls {C | C ∈ K ∧ sumCls L ⊆ C} = A) := by
  rintro ⟨⟨⟨⟨⟨hn, hQ⟩, h1⟩, hL⟩, hs⟩, hp⟩
  obtain rfl : Q = incl K := hQ
  exact desc_of (seq_prodsum hn h1 hL hs hp) rfl

/-- ✱210·27. \[\begin{align}\vdash \colon\ldotp \text{Hp}*210·2:&\lambda \subset \kappa .\supset _{\lambda }.sʻ\lambda \in \kappa :\supset :\\ &\lambda \subset \kappa .\supset _{\lambda }.\exists !(\overrightarrow{\text{max}} _{Q}ʻ\lambda \cup \overrightarrow{\text{seq}} _{Q}ʻ\lambda ).\exists !(\overrightarrow{\text{min}} _{Q}ʻ\lambda \cup \overrightarrow{\text{prec}} _{Q}ʻ\lambda )\end{align}\] -/
theorem pm210_27 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → sumCls M ∈ K) →
      ∀ L, L ⊆ K → (refs (maxP Q) L ∪ refs (seqP Q) L).Nonempty ∧
        (refs (minP Q) L ∪ refs (precP Q) L).Nonempty := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hs⟩ L hL
  obtain rfl : Q = incl K := hQ
  refine ⟨⟨_, pm210_251 ⟨⟨⟨hn, rfl⟩, h1⟩, hs⟩ hL⟩, ?_⟩
  by_cases hpL : prodCls L ∈ L
  · exact ⟨_, Or.inl ((min_eq_of hn h1 hL hpL _).2 rfl)⟩
  · exact ⟨_, Or.inr ((prec_eq_of hn h1 hL hpL (hs _ Set.inter_subset_left) _).2 rfl)⟩

/-- ✱210·271. \[\begin{align}\vdash \colon\ldotp \text{Hp}*210·2:&\lambda \subset \kappa .\supset _{\lambda }.pʻ\lambda \in \kappa :\supset :\\ &\lambda \subset \kappa .\supset _{\lambda }.\exists !(\overrightarrow{\text{max}} _{Q}ʻ\lambda \cup \overrightarrow{\text{seq}} _{Q}ʻ\lambda ).\exists !(\overrightarrow{\text{min}} _{Q}ʻ\lambda \cup \overrightarrow{\text{prec}} _{Q}ʻ\lambda )\\ &[\text{Proof as in *210·27}]\end{align}\] -/
theorem pm210_271 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → prodCls M ∈ K) →
      ∀ L, L ⊆ K → (refs (maxP Q) L ∪ refs (seqP Q) L).Nonempty ∧
        (refs (minP Q) L ∪ refs (precP Q) L).Nonempty := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hp⟩ L hL
  obtain rfl : Q = incl K := hQ
  refine ⟨?_, ⟨_, pm210_25 ⟨⟨⟨hn, rfl⟩, h1⟩, hp⟩ hL⟩⟩
  by_cases hsL : sumCls L ∈ L
  · exact ⟨_, Or.inl ((max_eq_of hn h1 hL hsL _).2 rfl)⟩
  · exact ⟨_, Or.inr ((seq_eq_of hn h1 hL hsL (hp _ up_sub) _).2 rfl)⟩

/-- ✱210·272. \[\begin{align}\vdash \colon\ldotp \text{Hp}*210·2:&\lambda \subset \kappa .\supset _{\lambda }.pʻ\lambda \cap sʻ\kappa \in \kappa :\supset :\\ &\lambda \subset \kappa .\supset _{\lambda }.\exists !(\overrightarrow{\text{max}} _{Q}ʻ\lambda \cup \overrightarrow{\text{seq}} _{Q}ʻ\lambda ).\exists !(\overrightarrow{\text{min}} _{Q}ʻ\lambda \cup \overrightarrow{\text{prec}} _{Q}ʻ\lambda )\\ &[\text{Proof as in *210·27, using *210·262}]\end{align}\] -/
theorem pm210_272 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → prodCls M ∩ sumCls K ∈ K) →
      ∀ L, L ⊆ K → (refs (maxP Q) L ∪ refs (seqP Q) L).Nonempty ∧
        (refs (minP Q) L ∪ refs (precP Q) L).Nonempty := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hK⟩ L hL
  obtain rfl : Q = incl K := hQ
  refine ⟨?_, ⟨_, (limin_prodsum hn h1 hL (hK L hL)).1⟩⟩
  by_cases hsL : sumCls L ∈ L
  · exact ⟨_, Or.inl ((max_eq_of hn h1 hL hsL _).2 rfl)⟩
  · have h' := hK {C | C ∈ K ∧ sumCls L ⊆ C} up_sub
    rw [Set.inter_comm] at h'
    exact ⟨_, Or.inr ((seq_prodsum hn h1 hL hsL h' _).2 rfl)⟩

/-- ✱210·28. \[\begin{align}\vdash :\text{Hp}*210·2.sʻʻ&\text{Cl}ʻ\kappa \subset \kappa .\supset .\\ &(\lambda ).\lambda \in (\text{ᗡ}ʻ\text{max}_{Q}\cup \text{ᗡ}ʻ\text{seq}_{Q})\cap (\text{ᗡ}ʻ\text{min}_{Q}\cup \text{ᗡ}ʻ\text{prec}_{Q})\end{align}\] -/
theorem pm210_28 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ sRel ʻʻ cl K ⊆ K →
      ∀ L, L ∈ (codom (maxP Q) ∪ codom (seqP Q)) ∩ (codom (minP Q) ∪ codom (precP Q)) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hs⟩
  obtain rfl : Q = incl K := hQ
  exact all_of_sub (pm210_27 ⟨⟨⟨hn, rfl⟩, h1⟩, fun M hM => hs ⟨M, hM, rfl⟩⟩)

/-- ✱210·281. \[\begin{align}\vdash :\text{Hp}*210·2.pʻʻ&\text{Cl}ʻ\kappa \subset \kappa .\supset .\\ &(\lambda ).\lambda \in (\text{ᗡ}ʻ\text{max}_{Q}\cup \text{ᗡ}ʻ\text{seq}_{Q})\cap (\text{ᗡ}ʻ\text{min}_{Q}\cup \text{ᗡ}ʻ\text{prec}_{Q})\end{align}\] -/
theorem pm210_281 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    (((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ graph prodCls ʻʻ cl K ⊆ K →
      ∀ L, L ∈ (codom (maxP Q) ∪ codom (seqP Q)) ∩ (codom (minP Q) ∪ codom (precP Q)) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hp⟩
  obtain rfl : Q = incl K := hQ
  exact all_of_sub (pm210_271 ⟨⟨⟨hn, rfl⟩, h1⟩, fun M hM => hp ⟨M, hM, rfl⟩⟩)

/-- ✱210·282. \[\begin{align}\vdash \colon\ldotp \text{Hp}*210·2:\lambda &\subset \kappa .\supset _{\lambda }.pʻ\lambda \cap sʻ\kappa \in \kappa :\supset .\\ &(\lambda ).\lambda \in (\text{ᗡ}ʻ\text{max}_{Q}\cup \text{ᗡ}ʻ\text{seq}_{Q})\cap (\text{ᗡ}ʻ\text{min}_{Q}\cup \text{ᗡ}ʻ\text{prec}_{Q})\end{align}\] -/
theorem pm210_282 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → prodCls M ∩ sumCls K ∈ K) →
      ∀ L, L ∈ (codom (maxP Q) ∪ codom (seqP Q)) ∩ (codom (minP Q) ∪ codom (precP Q)) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hK⟩
  obtain rfl : Q = incl K := hQ
  exact all_of_sub (pm210_272 ⟨⟨⟨hn, rfl⟩, h1⟩, hK⟩)

/-- ✱210·29. \(\vdash :\text{Hp}*210·251.\supset .(\lambda ).\lambda \in \text{ᗡ}ʻ\text{limax}_P\cap \text{ᗡ}ʻ\text{limin}_P \quad[*210·28.*207·44]\)

**Status.** proved (reading): `limax_P`, `limin_P` are misprints for `limax_Q`, `limin_Q` (`P` does not occur in the hypothesis; the demonstration is from ✱210·28 and ✱207·44, which concern `Q`). -/
theorem pm210_29 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → sumCls M ∈ K) →
      ∀ L, L ∈ codom (limaxP Q) ∩ codom (liminP Q) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hs⟩ L
  obtain rfl : Q = incl K := hQ
  obtain ⟨h, h'⟩ := all_of_sub (pm210_27 ⟨⟨⟨hn, rfl⟩, h1⟩, hs⟩) L
  exact ⟨limax_of h, limin_of h'⟩

/-- ✱210·291. \[\begin{align}\vdash :\text{Hp}*210·252.\supset .(\lambda ).\lambda \in \text{ᗡ}ʻ\text{limax}_P\cap \text{ᗡ}ʻ\text{limin}_P\\ &[*210·282.*207·44]\end{align}\]

**Status.** proved (reading): `limax_P`, `limin_P` are misprints for `limax_Q`, `limin_Q`, as in ✱210·29. -/
theorem pm210_291 {α : Type u} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → prodCls M ∩ sumCls K ∈ K) →
      ∀ L, L ∈ codom (limaxP Q) ∩ codom (liminP Q) := by
  rintro ⟨⟨⟨hn, hQ⟩, h1⟩, hK⟩ L
  obtain rfl : Q = incl K := hQ
  obtain ⟨h, h'⟩ := all_of_sub (pm210_272 ⟨⟨⟨hn, rfl⟩, h1⟩, hK⟩) L
  exact ⟨limax_of h, limin_of h'⟩

/-! ### Helper lemmas for ✱211 -/

section H211

variable {α : Type u} {P : α → α → Prop}

private theorem fld_l {x y : α} (h : P x y) : x ∈ fld P := ⟨y, Or.inl h⟩

private theorem fld_r {x y : α} (h : P x y) : y ∈ fld P := ⟨x, Or.inr h⟩

private theorem po_of {x y : α} (h : P x y) : po P x y :=
  po_iff_transGen.2 (Relation.TransGen.single h)

private theorem anc_of {x y : α} (h : P x y) : anc P x y := anc_iff_po.2 (Or.inr (po_of h))

private theorem fld_eq_dom_union_codom (R : α → α → Prop) : fld R = dom R ∪ codom R := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact Or.inl ⟨y, h⟩
    · exact Or.inr ⟨y, h⟩
  · rintro (⟨y, h⟩ | ⟨y, h⟩)
    · exact ⟨y, Or.inl h⟩
    · exact ⟨y, Or.inr h⟩

private theorem sect_closed {A : Set α} (h : A ∈ sect P) {x y : α} (hxy : P x y) (hy : y ∈ A) :
    x ∈ A := h.2 ⟨y, hy, hxy⟩

private theorem sect_closed_rtg {A : Set α} (h : A ∈ sect P) {x y : α}
    (hxy : Relation.ReflTransGen P x y) (hy : y ∈ A) : x ∈ A := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact hy
  | head hab _ ih => exact sect_closed h hab ih

private theorem sect_closed_po {A : Set α} (h : A ∈ sect P) {x y : α} (hxy : po P x y)
    (hy : y ∈ A) : x ∈ A :=
  sect_closed_rtg h (po_iff_transGen.1 hxy).to_reflTransGen hy

private theorem sect_closed_anc {A : Set α} (h : A ∈ sect P) {x y : α} (hxy : anc P x y)
    (hy : y ∈ A) : x ∈ A :=
  sect_closed_rtg h (anc_iff_reflTransGen.1 hxy).2 hy

private theorem sect_iff_anc {A : Set α} : A ∈ sect P ↔ A = anc P ʻʻ A := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, anc_iff_po.2 (Or.inl ⟨rfl, h.1 hx⟩)⟩
    · rintro ⟨y, hy, hxy⟩
      exact sect_closed_anc h hxy hy
  · intro h
    exact mem_dom_imgRel_anc.1 ⟨A, h⟩

private theorem fld_po : fld (po P) = fld P := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.1 (po_iff_transGen.1 h)
      exact ⟨b, Or.inl hb⟩
    · obtain ⟨b, -, hb⟩ := Relation.TransGen.tail'_iff.1 (po_iff_transGen.1 h)
      exact ⟨b, Or.inr hb⟩
  · rintro ⟨y, h | h⟩
    · exact ⟨y, Or.inl (po_of h)⟩
    · exact ⟨y, Or.inr (po_of h)⟩

private theorem fld_anc : fld (anc P) = fld P := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact (anc_iff_reflTransGen.1 h).1
    · rcases anc_iff_po.1 h with ⟨rfl, hy⟩ | h
      · exact hy
      · rw [← fld_po]
        exact ⟨y, Or.inr h⟩
  · intro hx
    exact ⟨x, Or.inl (anc_iff_po.2 (Or.inl ⟨rfl, hx⟩))⟩

private theorem sect_po : sect (po P) = sect P := by
  ext A
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fld_po ▸ h1, fun x ⟨y, hy, hxy⟩ => h2 ⟨y, hy, po_of hxy⟩⟩
  · intro h
    exact ⟨fld_po.symm ▸ h.1, fun x ⟨y, hy, hxy⟩ => sect_closed_po h hxy hy⟩

private theorem sect_anc : sect (anc P) = sect P := by
  ext A
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fld_anc ▸ h1, fun x ⟨y, hy, hxy⟩ => h2 ⟨y, hy, anc_of hxy⟩⟩
  · intro h
    exact ⟨fld_anc.symm ▸ h.1, fun x ⟨y, hy, hxy⟩ => sect_closed_anc h hxy hy⟩

private theorem img_po_of_sect {A : Set α} (h : A ∈ sect P) : P ʻʻ A = po P ʻʻ A := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, po_of hxy⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨b, hxb, hby⟩ := Relation.TransGen.head'_iff.1 (po_iff_transGen.1 hxy)
    exact ⟨b, sect_closed_rtg h hby hy, hxb⟩

private theorem sect_of_seg (ht : P ∈ transR) {A : Set α} (h : A ∈ dom (imgRel P)) :
    A ∈ sect P := by
  obtain ⟨C, rfl⟩ := h
  refine ⟨fun x ⟨c, _, hxc⟩ => fld_l hxc, ?_⟩
  rintro x ⟨y, ⟨c, hc, hyc⟩, hxy⟩
  exact ⟨c, hc, mem_transR.1 ht x y c ⟨hxy, hyc⟩⟩

private theorem follow_of_sect (hc : P ∈ connex) {A : Set α} (hA : A ∈ sect P) {y : α}
    (hy : y ∈ fld P) (hyA : y ∉ A) {z : α} (hz : z ∈ A) : P z y := by
  rcases mem_connex.1 hc z y ⟨hA.1 hz, hy⟩ with (h | rfl) | h
  · exact h
  · exact absurd hz hyA
  · exact absurd (sect_closed hA h hz) hyA

private theorem seq_not_mem {A : Set α} {s : α} (hs : seqP P s A) (hA : A ⊆ fld P) : s ∉ A := by
  intro h
  obtain ⟨⟨h1, -⟩, h3⟩ := seqP_iff.1 hs
  exact h3 s h1 (h1 s ⟨h, hA h⟩)

private theorem pred_seq_mem (hc : P ∈ connex) {A : Set α} (hA : A ∈ sect P) {s : α}
    (hs : seqP P s A) {y : α} (hy : P y s) : y ∈ A := by
  by_contra hyA
  obtain ⟨-, h3⟩ := seqP_iff.1 hs
  exact h3 y (fun z hz => follow_of_sect hc hA (fld_l hy) hyA hz.1) hy

private theorem seq_unique (hc : P ∈ connex) {A : Set α} {s t : α} (hs : seqP P s A)
    (ht : seqP P t A) : s = t := by
  obtain ⟨⟨hs1, hs2⟩, hs3⟩ := seqP_iff.1 hs
  obtain ⟨⟨ht1, ht2⟩, ht3⟩ := seqP_iff.1 ht
  rcases mem_connex.1 hc s t ⟨hs2, ht2⟩ with (h | h) | h
  · exact absurd h (ht3 s hs1)
  · exact h
  · exact absurd h (hs3 t ht1)

private theorem max_unique (hc : P ∈ connex) {A : Set α} {m n : α} (hm : maxP P m A)
    (hn : maxP P n A) : m = n := by
  obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
  obtain ⟨⟨hnA, hnf⟩, hn'⟩ := maxP_iff.1 hn
  rcases mem_connex.1 hc m n ⟨hmf, hnf⟩ with (h | h) | h
  · exact absurd h (hm' n hnA)
  · exact h
  · exact absurd h (hn' m hmA)

private theorem min_unique (hc : P ∈ connex) {A : Set α} {m n : α} (hm : minP P m A)
    (hn : minP P n A) : m = n := by
  obtain ⟨⟨hmA, hmf⟩, hm'⟩ := minP_iff.1 hm
  obtain ⟨⟨hnA, hnf⟩, hn'⟩ := minP_iff.1 hn
  rcases mem_connex.1 hc m n ⟨hmf, hnf⟩ with (h | h) | h
  · exact absurd h (hn' m hmA)
  · exact h
  · exact absurd h (hm' n hnA)

private theorem uniq_of {β : Type v} {R : α → β → Prop} {y : β} {a : α}
    (hu : ∀ b, R b y → b = a) (ha : R a y) : ∀ x, R x y ↔ x = a :=
  fun x => ⟨hu x, fun e => e ▸ ha⟩

private theorem edesc_iff_ex {β : Type v} {R : α → β → Prop} {y : β}
    (hu : ∀ a b, R a y → R b y → a = b) : EDesc R y ↔ ∃ a, R a y :=
  ⟨fun ⟨b, hb⟩ => ⟨b, (hb b).2 rfl⟩,
    fun ⟨a, ha⟩ => ⟨a, uniq_of (fun b hb => hu b a hb ha) ha⟩⟩

private theorem exists_of_edesc {β : Type v} {R : α → β → Prop} {y : β} (h : EDesc R y) :
    ∃ a, R a y := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, (hb b).2 rfl⟩

/-- A section which is a segment and has a maximum has a sequent, which immediately follows the
maximum (cf. ✱211·314, ✱206·52). -/
private theorem seq_of_max_sect (hc : P ∈ connex) {A C : Set α} (hA : A ∈ sect P)
    (hAC : A = P ʻʻ C) {m : α} (hm : maxP P m A) : ∃ b, P m b ∧ seqP P b A := by
  obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
  have hm2 : m ∈ P ʻʻ C := hAC ▸ hmA
  obtain ⟨b, hbC, hmb⟩ := hm2
  have hbA : b ∉ A := fun h => hm' b h hmb
  have hbf : b ∈ fld P := fld_r hmb
  refine ⟨b, hmb, seqP_iff.2 ⟨⟨fun y hy => follow_of_sect hc hA hbf hbA hy.1, hbf⟩,
    fun z hz hzb => ?_⟩⟩
  have hzA : z ∈ A := by rw [hAC]; exact ⟨b, hbC, hzb⟩
  exact hm' z hzA (hz m ⟨hmA, hmf⟩)

/-- `α = P''(α ∪ seq⃗_P'α)` for a section with a sequent. -/
private theorem eq_img_seq (hc : P ∈ connex) {A : Set α} (hA : A ∈ sect P) {s : α}
    (hs : seqP P s A) : A = P ʻʻ (A ∪ refs (seqP P) A) := by
  ext x
  constructor
  · intro hx
    exact ⟨s, Or.inr hs, (seqP_iff.1 hs).1.1 x ⟨hx, hA.1 hx⟩⟩
  · rintro ⟨y, hy | hy, hxy⟩
    · exact sect_closed hA hxy hy
    · exact pred_seq_mem hc hA hy hxy

private theorem refs_seq_eq (hc : P ∈ connex) {A : Set α} (hA : A ∈ sect P) {s : α}
    (hs : seqP P s A) : refs P s = A := by
  ext x
  exact ⟨fun h => pred_seq_mem hc hA hs h, fun h => (seqP_iff.1 hs).1.1 x ⟨h, hA.1 h⟩⟩

/-- A section without a maximum is the class of the predecessors of its members (✱211·2). -/
private theorem eq_img_of_nomax {A : Set α} (hA : A ∈ sect P) (h : ¬∃ m, maxP P m A) :
    A = P ʻʻ A := by
  refine Set.Subset.antisymm (fun x hx => ?_) hA.2
  by_contra hx'
  exact h ⟨x, maxP_iff.2 ⟨⟨hx, hA.1 hx⟩, fun y hy hxy => hx' ⟨y, hy, hxy⟩⟩⟩

private theorem seg_of_sect (hc : P ∈ connex) {A : Set α} (hA : A ∈ sect P)
    (h : A ∈ codom (seqP P) ∪ (codom (maxP P))ᶜ) : A ∈ dom (imgRel P) := by
  rcases h with ⟨s, hs⟩ | h
  · exact ⟨_, eq_img_seq hc hA hs⟩
  · exact ⟨A, eq_img_of_nomax hA h⟩

/-- For a series, `x = seq_P'P⃗'x` (`x ∈ C'P`). -/
private theorem seq_refs (hS : P ∈ Ser) {x : α} (hx : x ∈ fld P) :
    ∀ s, seqP P s (refs P x) ↔ s = x := by
  obtain ⟨⟨hJ, -⟩, hc⟩ := hS
  have hseq : seqP P x (refs P x) :=
    seqP_iff.2 ⟨⟨fun y hy => hy.1, hx⟩, fun z hz hzx => mem_rl_J.1 hJ z (hz z ⟨hzx, fld_l hzx⟩)⟩
  exact uniq_of (fun s hs => seq_unique hc hs hseq) hseq

private theorem refs_mem_sect (ht : P ∈ transR) (x : α) : refs P x ∈ sect P :=
  ⟨fun _ h => fld_l h, fun y ⟨z, hz, hyz⟩ => mem_transR.1 ht y z x ⟨hyz, hz⟩⟩

private theorem not_one {A : Set α} (h : A ∉ one) {x : α} (hx : x ∈ A) : ∃ y, y ∈ A ∧ y ≠ x := by
  by_contra hc
  push Not at hc
  exact h (mem_one_iff.2 ⟨x, fun z => ⟨fun hz => hc z hz, fun e => e ▸ hx⟩⟩)

/-- For connected `P`, `C'(P ⥏ α) = α` when `α ⊂ C'P` is not a unit class. -/
private theorem fld_fres (hc : P ∈ connex) {A : Set α} (hA : A ⊆ fld P) (h1 : A ∉ one) :
    fld (P ⥏ A) = A := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact h.1.1
    · exact h.2
  · intro hx
    obtain ⟨y, hy, hyx⟩ := not_one h1 hx
    rcases mem_connex.1 hc x y ⟨hA hx, hA hy⟩ with (h | h) | h
    · exact ⟨y, Or.inl ⟨⟨hx, h⟩, hy⟩⟩
    · exact absurd h.symm hyx
    · exact ⟨y, Or.inr ⟨⟨hy, h⟩, hx⟩⟩

private theorem fld_fres_sub (A : Set α) : fld (P ⥏ A) ⊆ A := by
  rintro x ⟨y, h | h⟩
  · exact h.1.1
  · exact h.2

/-- `x P_1 y` for transitive `P` contained in diversity, in terms of `P` (cf. ✱201·63). -/
private theorem P1cnv_iff (hS : P ∈ Ser) {x z : α} :
    P1 P˘ z x ↔ P x z ∧ ¬∃ w, P x w ∧ P w z := by
  have ht : P˘ ∈ transR := mem_transR.2 fun a b c ⟨h1, h2⟩ => mem_transR.1 hS.1.2 c b a ⟨h2, h1⟩
  have hJ : P˘ ∈ rl J := mem_rl_J.2 fun a h => mem_rl_J.1 hS.1.1 a h
  rw [P1_iff_of_transR ht hJ]
  exact and_congr Iff.rfl ⟨fun h ⟨w, h1, h2⟩ => h ⟨w, h2, h1⟩, fun h ⟨w, h1, h2⟩ => h ⟨w, h2, h1⟩⟩

private theorem P1_iff' (hS : P ∈ Ser) {x z : α} :
    P1 P x z ↔ P x z ∧ ¬∃ w, P x w ∧ P w z :=
  P1_iff_of_transR hS.1.2 hS.1.1

/-- In a series, a term has at most one immediate successor. -/
private theorem succ_unique (hS : P ∈ Ser) {x z z' : α} (h : P x z ∧ ¬∃ w, P x w ∧ P w z)
    (h' : P x z' ∧ ¬∃ w, P x w ∧ P w z') : z = z' := by
  rcases mem_connex.1 hS.2 z z' ⟨fld_r h.1, fld_r h'.1⟩ with (e | e) | e
  · exact absurd ⟨z, h.1, e⟩ h'.2
  · exact e
  · exact absurd ⟨z', h'.1, e⟩ h.2

end H211

/-!
## [✱211] On sections and segments

*(Vol. 2, p. 624)*

> *Summary of* *211.
>
> The theory of the modes of separation of a series into two classes, one of which wholly precedes the other, and which together make up the whole series, is of fundamental importance. When one out of a pair of such classes is given, the other is the rest of the series; we may therefore, for most purposes, confine our attention to that one of the two classes which comes first in the serial order. Any class which can be the first of such a pair we shall call a *section* of our series. If \(P\) is the series, we shall denote the class of its sections by "\(\text{sect}ʻP\)." If \(\alpha\) is a section of \(P\), we shall call \(CʻP - \alpha\) (which is the second class of our pair) the *complement* of \(\alpha\). The class of complements of sections is \[ (CʻP -)ʻʻ\text{sect}ʻP, \] which is identical with \(\text{sect}ʻ\breve{P}\) (*211·75).
>
> …

**Lean reading.** `sect'P` is `sect P`, the segments `D'P_∈` are `dom (imgRel P)`, the segments
without maximum `D'(P_∈ ∩̇ I)` are `dom (imgRel P ⩀ I)`; `P⥏` is the relation `opL fres P` (so
`Q ∈ D'P⥏` is `Q ∈ dom (opL fres P)`), `(C'P −)` and `(C'P ∪)` are `opL (· \ ·) (fld P)` and
`opL (· ∪ ·) (fld P)`, `P̆_1` is `P1 P˘`, `B'P̆` is the description `Desc Beg P˘`, `E!seq_P'α` is
`EDesc (seqP P) A` and `∃!max⃗_P'α` is `(refs (maxP P) A).Nonempty`. In ✱211·67–·692 the
conclusions "Hp ✱210·12", "Hp ✱210·251", "Hp ✱210·252" are written out with `κ`, `Q` as in ✱210.
No hypothesis is added; the proofs are direct (connexity makes maxima, minima and sequents unique).

**Status.** proved (all propositions; ✱211·2, ✱211·282, ✱211·756 proved (reading): misprints of
the e-text; ✱211·73 proved (corrected): false as printed, counterexample `pm211_73_printed_false`;
see their docstrings)
-/

/-- ✱211·01 (Df). \(\text{sect}ʻP=\hat{\alpha} (\alpha \subset CʻP.Pʻʻ\alpha \subset \alpha ) \quad\text{Df}\) -/
theorem pm211_01 {α : Type u} {P : α → α → Prop} : sect P = {A | A ⊆ fld P ∧ P ʻʻ A ⊆ A} := rfl

/-- ✱211·1. \(\vdash :\alpha \in \text{sect}ʻP.\equiv .\alpha \subset CʻP.Pʻʻ\alpha \subset \alpha \quad[(*211·01)]\) -/
theorem pm211_1 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∈ sect P ↔ A ⊆ fld P ∧ P ʻʻ A ⊆ A := Iff.rfl

/-- ✱211·11. \(\vdash :\alpha \in \text{D}ʻP_{\in }.\equiv .(\exists \beta ).\alpha =Pʻʻ\beta \quad[*37·101]\) -/
theorem pm211_11 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∈ dom (imgRel P) ↔ ∃ B, A = P ʻʻ B := Iff.rfl

/-- ✱211·12. \(\vdash :\alpha \in \text{D}ʻ(P_{\in }\dot{\cap} I).\equiv .\alpha =Pʻʻ\alpha\) -/
theorem pm211_12 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∈ dom (imgRel P ⩀ I) ↔ A = P ʻʻ A := mem_dom_imgRel_rcap_I

/-- ✱211·13. \(\vdash :\alpha \in \text{sect}ʻP.\equiv .\alpha =P_{*}ʻʻ\alpha .\equiv .\alpha \in \text{D}ʻ{(P_{*})_{\in }\dot{\cap} I}.\equiv .\alpha \in \text{D}ʻ(P_{*})_{\in }\) -/
theorem pm211_13 {α : Type u} {P : α → α → Prop} {A : Set α} :
    ((A ∈ sect P ↔ A = anc P ʻʻ A) ∧ (A = anc P ʻʻ A ↔ A ∈ dom (imgRel (anc P) ⩀ I))) ∧
      (A ∈ dom (imgRel (anc P) ⩀ I) ↔ A ∈ dom (imgRel (anc P))) := by
  refine ⟨⟨sect_iff_anc, mem_dom_imgRel_rcap_I.symm⟩, ⟨fun ⟨B, h, _⟩ => ⟨B, h⟩, fun h => ?_⟩⟩
  exact mem_dom_imgRel_rcap_I.2 (sect_iff_anc.1 (mem_dom_imgRel_anc.1 h))

/-- ✱211·131. \(\vdash :\alpha \in \text{sect}ʻP.\supset .Pʻʻ\alpha =P_{\text{po}}ʻʻ\alpha\) -/
theorem pm211_131 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∈ sect P → P ʻʻ A = po P ʻʻ A := img_po_of_sect

/-- ✱211·132. \[\begin{align}\vdash :\alpha \in \text{sect}ʻP.\supset .&\text{D}ʻ(P\unicode{x0294f}\alpha )=\text{D}ʻ(P_{\text{po}}\unicode{x0294f}\alpha ).\text{ᗡ}ʻ(P\unicode{x0294f}\alpha )=\text{ᗡ}ʻ(P_{\text{po}}\unicode{x0294f}\alpha ).\\ &Cʻ(P\unicode{x0294f}\alpha )=Cʻ(P_{\text{po}}\unicode{x0294f}\alpha )\end{align}\] -/
theorem pm211_132 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∈ sect P → (dom (P ⥏ A) = dom (po P ⥏ A) ∧ codom (P ⥏ A) = codom (po P ⥏ A)) ∧
      fld (P ⥏ A) = fld (po P ⥏ A) := by
  intro h
  have hd : dom (P ⥏ A) = dom (po P ⥏ A) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hx, hxy⟩, hy⟩
      exact ⟨y, ⟨hx, po_of hxy⟩, hy⟩
    · rintro ⟨y, ⟨hx, hxy⟩, hy⟩
      obtain ⟨b, hxb, hby⟩ := Relation.TransGen.head'_iff.1 (po_iff_transGen.1 hxy)
      exact ⟨b, ⟨hx, hxb⟩, sect_closed_rtg h hby hy⟩
  have hcd : codom (P ⥏ A) = codom (po P ⥏ A) := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxy⟩, hy⟩
      exact ⟨x, ⟨hx, po_of hxy⟩, hy⟩
    · rintro ⟨x, ⟨hx, hxy⟩, hy⟩
      obtain ⟨b, -, hby⟩ := Relation.TransGen.tail'_iff.1 (po_iff_transGen.1 hxy)
      exact ⟨b, ⟨sect_closed h hby hy, hby⟩, hy⟩
  refine ⟨⟨hd, hcd⟩, ?_⟩
  rw [fld_eq_dom_union_codom, fld_eq_dom_union_codom, hd, hcd]

/-- ✱211·133. \(\vdash :P_{\text{po}}\in \text{connex} .\alpha \in \text{sect}ʻP-1.\supset .Cʻ(P\unicode{x0294f}\alpha )=\alpha \) -/
theorem pm211_133 {α : Type u} {P : α → α → Prop} {A : Set α} :
    po P ∈ connex ∧ A ∈ sect P \ one → fld (P ⥏ A) = A := by
  rintro ⟨hc, hA, h1⟩
  rw [(pm211_132 hA).2]
  exact fld_fres hc (by rw [fld_po]; exact hA.1) h1

/-- ✱211·14. \(\vdash .\text{D}ʻ(P_{\in }\dot{\cap} I)\subset \text{D}ʻP_{\in }.\text{D}ʻ(P_{\in }\dot{\cap} I)\subset \text{sect}ʻP\) -/
theorem pm211_14 {α : Type u} {P : α → α → Prop} :
    dom (imgRel P ⩀ I) ⊆ dom (imgRel P) ∧ dom (imgRel P ⩀ I) ⊆ sect P := by
  refine ⟨fun A ⟨B, h, _⟩ => ⟨B, h⟩, fun A hA => ?_⟩
  have h : A = P ʻʻ A := mem_dom_imgRel_rcap_I.1 hA
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [h] at hx
    obtain ⟨y, -, hxy⟩ := hx
    exact fld_l hxy
  · rw [h]; exact hx

/-- ✱211·15. \(\vdash :P\in \text{trans}.\supset .\text{D}ʻP_{\in }\subset \text{sect}ʻP\) -/
theorem pm211_15 {α : Type u} {P : α → α → Prop} : P ∈ transR → dom (imgRel P) ⊆ sect P :=
  fun ht _ h => sect_of_seg ht h

/-- ✱211·16. \(\vdash .P_{\text{po}}ʻʻ\alpha \in \text{sect}ʻP\) -/
theorem pm211_16 {α : Type u} {P : α → α → Prop} {A : Set α} : po P ʻʻ A ∈ sect P := by
  refine ⟨fun x ⟨y, _, hxy⟩ => ?_, ?_⟩
  · rw [← fld_po]; exact fld_l hxy
  · rintro x ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    exact ⟨z, hz, po_iff_transGen.2 (Relation.TransGen.head hxy (po_iff_transGen.1 hyz))⟩

/-- ✱211·17. \[\begin{align}&\vdash .\text{sect}ʻP=\text{sect}ʻP_{\text{po}}=\text{sect}ʻP_{*} &[*211·13.*90·4.*91·602]\end{align}\] -/
theorem pm211_17 {α : Type u} {P : α → α → Prop} :
    sect P = sect (po P) ∧ sect (po P) = sect (anc P) :=
  ⟨sect_po.symm, sect_po.trans sect_anc.symm⟩

/-- ✱211·18. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\supset .\text{sect}ʻP\cap 1=\iotaʻʻ\overrightarrow{B}ʻP\) -/
theorem pm211_18 {α : Type u} {P : α → α → Prop} :
    po P ⪽ J → sect P ∩ one = iota ʻʻ refs Beg P := by
  intro hJ
  have irr : ∀ x, ¬ P x x := fun x h => hJ x x (po_of h) rfl
  ext A
  constructor
  · rintro ⟨hA, h1⟩
    obtain ⟨b, hb⟩ := mem_one_iff.1 h1
    have hbA : b ∈ A := (hb b).2 rfl
    obtain ⟨y, hy⟩ := hA.1 hbA
    refine ⟨b, ⟨?_, ?_⟩, Set.ext fun z => hb z⟩
    · rcases hy with hy | hy
      · exact ⟨y, hy⟩
      · exact absurd ((hb y).1 (sect_closed hA hy hbA) ▸ hy) (irr b)
    · rintro ⟨y, hyb⟩
      exact irr b ((hb y).1 (sect_closed hA hyb hbA) ▸ hyb)
  · rintro ⟨b, ⟨⟨y, hby⟩, hnb⟩, rfl⟩
    refine ⟨⟨fun z hz => ?_, fun z ⟨w, hw, hzw⟩ => ?_⟩, mem_one_iff.2 ⟨b, fun z => Iff.rfl⟩⟩
    · have hz' : z = b := hz
      rw [hz']; exact fld_l hby
    · have hw' : w = b := hw
      rw [hw'] at hzw
      exact absurd ⟨z, hzw⟩ hnb

/-- ✱211·181. \(\vdash :P_{\text{po}}\in \text{Ser}.\exists !\overrightarrow{B}ʻP.\supset .\text{sect}ʻP\cap 1=\iota ʻ\iota ʻBʻP\) -/
theorem pm211_181 {α : Type u} {P : α → α → Prop} :
    po P ∈ Ser ∧ (refs Beg P).Nonempty → Desc Beg P (fun b => sect P ∩ one = ι (ι b)) := by
  rintro ⟨hS, b, hb⟩
  have hJ : po P ⪽ J := fun x y h e => mem_rl_J.1 hS.1.1 x (e ▸ h)
  have hu : ∀ c, Beg c P → c = b := by
    intro c hc
    have hcf : c ∈ fld (po P) := by
      obtain ⟨y, hy⟩ := hc.1
      rw [fld_po]; exact fld_l hy
    have hbf : b ∈ fld (po P) := by
      obtain ⟨y, hy⟩ := hb.1
      rw [fld_po]; exact fld_l hy
    rcases mem_connex.1 hS.2 c b ⟨hcf, hbf⟩ with (h | h) | h
    · obtain ⟨d, -, hd⟩ := Relation.TransGen.tail'_iff.1 (po_iff_transGen.1 h)
      exact absurd ⟨d, hd⟩ hb.2
    · exact h
    · obtain ⟨d, -, hd⟩ := Relation.TransGen.tail'_iff.1 (po_iff_transGen.1 h)
      exact absurd ⟨d, hd⟩ hc.2
  refine desc_of (uniq_of hu hb) ?_
  rw [pm211_18 hJ]
  ext A
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [hu c hc]
    rfl
  · intro hA
    exact ⟨b, hb, hA⟩

/-- ✱211·182. \(\vdash :P_{\text{po}}\in \text{Ser}.\overrightarrow{B}ʻP=\Lambda .\supset .\text{sect}ʻP\cap 1=\Lambda \quad[*211·18]\) -/
theorem pm211_182 {α : Type u} {P : α → α → Prop} :
    po P ∈ Ser ∧ refs Beg P = Λ → sect P ∩ one = Λ := by
  rintro ⟨hS, h0⟩
  have hJ : po P ⪽ J := fun x y h e => mem_rl_J.1 hS.1.1 x (e ▸ h)
  rw [pm211_18 hJ, eqΛ]
  rintro A ⟨b, hb, -⟩
  exact eqΛ.1 h0 b hb

/-- ✱211·2. \(\vdash :\alpha \in \text{sect}ʻP.\supset .\alpha =\alpha \cap CʻP=a\cup Pʻʻ\alpha =(\alpha \cap CʻP)\cup Pʻʻ\alpha =Pʻʻ\alpha \cup \overrightarrow{\text{max}}_{P}ʻ\alpha\)

**Status.** proved (reading): the e-text prints `a ∪ P''α` for `α ∪ P''α` in the second link of the chain. -/
theorem pm211_2 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∈ sect P → ((A = A ∩ fld P ∧ A ∩ fld P = A ∪ P ʻʻ A) ∧
      A ∪ P ʻʻ A = (A ∩ fld P) ∪ P ʻʻ A) ∧ (A ∩ fld P) ∪ P ʻʻ A = P ʻʻ A ∪ refs (maxP P) A := by
  intro h
  have e1 : A ∩ fld P = A := Set.inter_eq_left.2 h.1
  have e2 : A ∪ P ʻʻ A = A := Set.union_eq_left.2 h.2
  refine ⟨⟨⟨e1.symm, by rw [e1, e2]⟩, by rw [e1]⟩, ?_⟩
  rw [e1, e2]
  ext x
  constructor
  · intro hx
    by_cases hp : ∃ y, y ∈ A ∧ P x y
    · exact Or.inl hp
    · exact Or.inr (maxP_iff.2 ⟨⟨hx, h.1 hx⟩, fun y hy hxy => hp ⟨y, hy, hxy⟩⟩)
  · rintro (hx | hx)
    · exact h.2 hx
    · exact (maxP_iff.1 hx).1.1

/-- ✱211·21. \(\vdash \colon\ldotp \alpha \in \text{sect}ʻP.\supset :{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .\equiv .\alpha \in \text{D}ʻ(P_{\in }\dot{\cap} I)\) -/
theorem pm211_21 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∈ sect P → (¬ (refs (maxP P) A).Nonempty ↔ A ∈ dom (imgRel P ⩀ I)) := by
  intro h
  rw [mem_dom_imgRel_rcap_I]
  constructor
  · intro hn
    exact eq_img_of_nomax h (fun ⟨m, hm⟩ => hn ⟨m, hm⟩)
  · rintro e ⟨m, hm⟩
    obtain ⟨⟨hmA, -⟩, hm'⟩ := maxP_iff.1 hm
    have : m ∈ P ʻʻ A := e ▸ hmA
    obtain ⟨y, hy, hmy⟩ := this
    exact hm' y hy hmy

/-- ✱211·22. \(\vdash :P\in \text{connex} .\alpha \in \text{sect}ʻP.\supset .\alpha \cup \overrightarrow{\text{seq}} _{P}ʻ\alpha \in \text{sect}ʻP\) -/
theorem pm211_22 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P → A ∪ refs (seqP P) A ∈ sect P := by
  rintro ⟨hc, hA⟩
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases hx with hx | hx
    · exact hA.1 hx
    · exact (seqP_iff.1 hx).1.2
  · rintro x ⟨y, hy | hy, hxy⟩
    · exact Or.inl (sect_closed hA hxy hy)
    · exact Or.inl (pred_seq_mem hc hA hy hxy)

/-- ✱211·23. \(\vdash :P\in \text{connex} .\alpha \in \text{sect}ʻP.\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\alpha =Pʻʻ(\alpha \cup \overrightarrow{\text{seq}} _{P}ʻ\alpha )=\overrightarrow{P}ʻ\text{seq}_{P}ʻ\alpha\) -/
theorem pm211_23 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ connex ∧ A ∈ sect P) ∧ EDesc (seqP P) A →
      A = P ʻʻ (A ∪ refs (seqP P) A) ∧
        Desc (seqP P) A (fun s => P ʻʻ (A ∪ refs (seqP P) A) = refs P s) := by
  rintro ⟨⟨hc, hA⟩, hE⟩
  obtain ⟨s, hs⟩ := exists_of_edesc hE
  have e := eq_img_seq hc hA hs
  refine ⟨e, desc_of (uniq_of (fun t ht => seq_unique hc ht hs) hs) ?_⟩
  rw [← e, refs_seq_eq hc hA hs]

/-- ✱211·24. \(\vdash :P\in \text{connex} .\alpha \in \text{sect}ʻP\cap (\text{ᗡ}ʻ\text{seq}_{P}\cup -\text{ᗡ}ʻ\text{max}_{P}).\supset .\alpha \in \text{D}ʻP_{\in }\) -/
theorem pm211_24 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P ∩ (codom (seqP P) ∪ (codom (maxP P))ᶜ) → A ∈ dom (imgRel P) := by
  rintro ⟨hc, hA, h⟩
  exact seg_of_sect hc hA h

/-- ✱211·26. \(\vdash .CʻP\in \text{sect}ʻP.sʻ\text{sect}ʻP=CʻP\) -/
theorem pm211_26 {α : Type u} {P : α → α → Prop} : fld P ∈ sect P ∧ sumCls (sect P) = fld P := by
  have h : fld P ∈ sect P := ⟨subset_rfl, fun x ⟨y, _, hxy⟩ => fld_l hxy⟩
  refine ⟨h, Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ⟨_, h, hx⟩)⟩
  obtain ⟨B, hB, hx⟩ := hx
  exact hB.1 hx

/-- ✱211·27. \(\vdash :P\in \text{trans}.\supset .(\alpha \cap CʻP)\cup Pʻʻ\alpha \in \text{sect}ʻP\) -/
theorem pm211_27 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → (A ∩ fld P) ∪ P ʻʻ A ∈ sect P := by
  intro ht
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases hx with hx | ⟨y, -, hxy⟩
    · exact hx.2
    · exact fld_l hxy
  · rintro x ⟨y, hy, hxy⟩
    rcases hy with hy | ⟨z, hz, hyz⟩
    · exact Or.inr ⟨y, hy.1, hxy⟩
    · exact Or.inr ⟨z, hz, mem_transR.1 ht x y z ⟨hxy, hyz⟩⟩

/-- ✱211·271. \(\vdash :P\in \text{trans}.\supset .(\exists \beta ).\beta \in \text{sect}ʻP.\overrightarrow{\text{max}}_{P}ʻ\alpha =\overrightarrow{\text{max}}_{P}ʻ\beta .\overrightarrow{\text{seq}} _{P}ʻ\alpha =\overrightarrow{\text{seq}} _{P}ʻ\beta\) -/
theorem pm211_271 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → ∃ B, (B ∈ sect P ∧ refs (maxP P) A = refs (maxP P) B) ∧
      refs (seqP P) A = refs (seqP P) B := by
  intro ht
  have tr := mem_transR.1 ht
  refine ⟨(A ∩ fld P) ∪ P ʻʻ A, ⟨pm211_27 ht, ?_⟩, ?_⟩
  · ext x
    show maxP P x A ↔ maxP P x _
    rw [maxP_iff, maxP_iff]
    constructor
    · rintro ⟨⟨hxA, hxf⟩, h⟩
      refine ⟨⟨Or.inl ⟨hxA, hxf⟩, hxf⟩, fun y hy hxy => ?_⟩
      rcases hy with hy | ⟨z, hz, hyz⟩
      · exact h y hy.1 hxy
      · exact h z hz (tr x y z ⟨hxy, hyz⟩)
    · rintro ⟨⟨hxB, hxf⟩, h⟩
      rcases hxB with hxA | ⟨z, hz, hxz⟩
      · exact ⟨⟨hxA.1, hxf⟩, fun y hy hxy => h y (Or.inl ⟨hy, fld_r hxy⟩) hxy⟩
      · exact absurd hxz (h z (Or.inl ⟨hz, fld_r hxz⟩))
  · have key : ∀ z, (∀ y, y ∈ A ∩ fld P → P y z) ↔
        (∀ y, y ∈ ((A ∩ fld P) ∪ P ʻʻ A) ∩ fld P → P y z) := by
      intro z
      constructor
      · intro h y hy
        rcases hy.1 with hy' | ⟨w, hw, hyw⟩
        · exact h y hy'
        · exact tr y w z ⟨hyw, h w ⟨hw, fld_r hyw⟩⟩
      · intro h y hy
        exact h y ⟨Or.inl hy, hy.2⟩
    ext x
    show seqP P x A ↔ seqP P x _
    rw [seqP_iff, seqP_iff, key]
    exact and_congr Iff.rfl (forall_congr' fun z => imp_congr (key z) Iff.rfl)

/-- ✱211·272. \[\begin{align}\vdash \colon\ldotp P\in &\text{trans}.\supset :\\ &(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}.\equiv .\text{sect}ʻP\subset \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}\end{align}\] -/
theorem pm211_272 {α : Type u} {P : α → α → Prop} :
    P ∈ transR → ((∀ A, A ∈ codom (maxP P) ∪ codom (seqP P)) ↔
      sect P ⊆ codom (maxP P) ∪ codom (seqP P)) := by
  intro ht
  refine ⟨fun h A _ => h A, fun h A => ?_⟩
  obtain ⟨B, ⟨hB, e1⟩, e2⟩ := pm211_271 (A := A) ht
  rcases h hB with ⟨x, hx⟩ | ⟨x, hx⟩
  · have : x ∈ refs (maxP P) A := e1 ▸ hx
    exact Or.inl ⟨x, this⟩
  · have : x ∈ refs (seqP P) A := e2 ▸ hx
    exact Or.inr ⟨x, this⟩

/-- ✱211·28. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.\alpha \subset CʻP.\alpha {\sim}\in 1.&(CʻP-\alpha ){\sim}\in 1.\supset :\\ &\alpha \in \text{sect}ʻP.\equiv .P =P \unicode{x0294f}\alpha \unicode{x2909}P \unicode{x0294f}(CʻP-\alpha )\end{align}\] -/
theorem pm211_28 {α : Type u} {P : α → α → Prop} {A : Set α} :
    ((P ∈ Ser ∧ A ⊆ fld P) ∧ A ∉ one) ∧ fld P \ A ∉ one →
      (A ∈ sect P ↔ P = P ⥏ A ⤉ P ⥏ (fld P \ A)) := by
  rintro ⟨⟨⟨hS, hAf⟩, h1⟩, h2⟩
  have hc := hS.2
  have e1 : fld (P ⥏ A) = A := fld_fres hc hAf h1
  have e2 : fld (P ⥏ (fld P \ A)) = fld P \ A := fld_fres hc (fun _ hx => hx.1) h2
  constructor
  · intro hA
    funext x y
    apply propext
    rw [rsum_apply, e1, e2]
    constructor
    · intro hxy
      by_cases hx : x ∈ A
      · by_cases hy : y ∈ A
        · exact Or.inl (Or.inl ⟨⟨hx, hxy⟩, hy⟩)
        · exact Or.inr ⟨hx, fld_r hxy, hy⟩
      · by_cases hy : y ∈ A
        · exact absurd (sect_closed hA hxy hy) hx
        · exact Or.inl (Or.inr ⟨⟨⟨fld_l hxy, hx⟩, hxy⟩, fld_r hxy, hy⟩)
    · rintro ((h | h) | ⟨hx, hyf, hy⟩)
      · exact h.1.2
      · exact h.1.2
      · exact follow_of_sect hc hA hyf hy hx
  · intro e
    refine ⟨hAf, ?_⟩
    rintro x ⟨y, hy, hxy⟩
    have h' := Eq.mp (congrFun (congrFun e x) y) hxy
    rw [rsum_apply] at h'
    rcases h' with (h | h) | ⟨hx, -⟩
    · exact h.1.1
    · exact absurd hy h.2.2
    · exact fld_fres_sub A hx

/-- ✱211·281. \(\vdash :P\in \text{Ser}.CʻQ\cap CʻR=\Lambda .P=Q\unicode{x2909}R.\supset .CʻQ\in \text{sect}ʻP\) -/
theorem pm211_281 {α : Type u} {P Q R : α → α → Prop} :
    (P ∈ Ser ∧ fld Q ∩ fld R = Λ) ∧ P = Q ⤉ R → fld Q ∈ sect P := by
  rintro ⟨⟨-, hd⟩, rfl⟩
  refine ⟨fun x hx => by rw [fld_rsum]; exact Or.inl hx, ?_⟩
  rintro x ⟨y, hy, hxy⟩
  rcases hxy with (h | h) | ⟨hx, hyR⟩
  · exact fld_l h
  · exact absurd ⟨hy, fld_r h⟩ (eqΛ.1 hd y)
  · exact hx

/-- ✱211·282. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.Q\in &\text{D}ʻP\unicode{x0294f}.CʻP-CʻQ{\sim}\in I.\supset :\\ &CʻQ\in \text{sect}ʻP.\equiv .(\exists R).CʻQ\cap CʻR=\Lambda .P=Q\unicode{x2909}R\\ &[*211·28·281.*200·12]\end{align}\]

**Status.** proved (reading): the e-text prints `C'P − C'Q ∼∈ I` (`I` the identity relation, which a class cannot belong to) for `C'P − C'Q ∼∈ 1`, the hypothesis of ✱211·28 that the proof (from ✱211·28·281) requires. -/
theorem pm211_282 {α : Type u} {P Q : α → α → Prop} :
    (P ∈ Ser ∧ Q ∈ dom (opL fres P)) ∧ fld P \ fld Q ∉ one →
      (fld Q ∈ sect P ↔ ∃ R, fld Q ∩ fld R = Λ ∧ P = Q ⤉ R) := by
  rintro ⟨⟨hS, S, hQ⟩, h2⟩
  have hQ' : Q = P ⥏ S := hQ
  constructor
  · intro hsect
    have eQ : Q = P ⥏ fld Q := by
      funext x y
      apply propext
      constructor
      · intro h
        have h' : (P ⥏ S) x y := hQ' ▸ h
        exact ⟨⟨fld_l h, h'.1.2⟩, fld_r h⟩
      · intro h
        have hx : x ∈ S := fld_fres_sub S (hQ' ▸ h.1.1)
        have hy : y ∈ S := fld_fres_sub S (hQ' ▸ h.2)
        rw [hQ']
        exact ⟨⟨hx, h.1.2⟩, hy⟩
    have h1 : fld Q ∉ one := by
      intro h1
      obtain ⟨b, hb⟩ := mem_one_iff.1 h1
      obtain ⟨y, hy | hy⟩ := (hb b).2 rfl
      · have e := (hb y).1 (fld_r hy)
        rw [e, hQ'] at hy
        exact mem_rl_J.1 hS.1.1 b hy.1.2
      · have e := (hb y).1 (fld_l hy)
        rw [e, hQ'] at hy
        exact mem_rl_J.1 hS.1.1 b hy.1.2
    have hsub : fld Q ⊆ fld P := hsect.1
    have e := (pm211_28 ⟨⟨⟨hS, hsub⟩, h1⟩, h2⟩).1 hsect
    refine ⟨P ⥏ (fld P \ fld Q), ?_, ?_⟩
    · rw [eqΛ]
      rintro x ⟨hx, hx'⟩
      exact (fld_fres_sub _ hx').2 hx
    · rw [← eQ] at e
      exact e
  · rintro ⟨R, hd, e⟩
    exact pm211_281 ⟨⟨hS, hd⟩, e⟩

/-- ✱211·283. \(\vdash :P\,\unicode{x2abd}\, J.P=Q\unicode{x2909}R.\supset .CʻQ\cap CʻR=\Lambda\) -/
theorem pm211_283 {α : Type u} {P Q R : α → α → Prop} :
    P ⪽ J ∧ P = Q ⤉ R → fld Q ∩ fld R = Λ := by
  rintro ⟨hJ, rfl⟩
  rw [eqΛ]
  rintro x ⟨hQ, hR⟩
  exact hJ x x (Or.inr ⟨hQ, hR⟩) rfl

/-- ✱211·3. \(\vdash .\overrightarrow{P}ʻʻCʻP\subset \text{D}ʻP_{\in } \quad[*53·301.*211·11]\) -/
theorem pm211_3 {α : Type u} {P : α → α → Prop} : Rfwd P ʻʻ fld P ⊆ dom (imgRel P) := by
  rintro B ⟨x, -, rfl⟩
  refine ⟨ι x, ?_⟩
  ext y
  exact ⟨fun h => ⟨x, rfl, h⟩, fun ⟨z, hz, h⟩ => (show z = x from hz) ▸ h⟩

/-- ✱211·301. \(\vdash .\text{D}ʻP\in \text{D}ʻP_{\in } \quad[*37·25.*211·11]\) -/
theorem pm211_301 {α : Type u} {P : α → α → Prop} : dom P ∈ dom (imgRel P) := by
  refine ⟨Set.univ, ?_⟩
  ext x
  exact ⟨fun ⟨y, h⟩ => ⟨y, trivial, h⟩, fun ⟨y, _, h⟩ => ⟨y, h⟩⟩

/-- ✱211·302. \(\vdash :P\in \text{Ser}.\supset .\overrightarrow{P}ʻʻCʻP=\text{sect}ʻP\cap \text{ᗡ}ʻ\text{seq}_{P}\) -/
theorem pm211_302 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → Rfwd P ʻʻ fld P = sect P ∩ codom (seqP P) := by
  intro hS
  ext B
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨refs_mem_sect hS.1.2 x, x, (seq_refs hS hx x).2 rfl⟩
  · rintro ⟨hB, s, hs⟩
    exact ⟨s, (seqP_iff.1 hs).1.2, (refs_seq_eq hS.2 hB hs).symm⟩

/-- ✱211·31. \[\begin{align}&\vdash \colon\ldotp P\in \text{trans}\cap \text{connex} .\alpha \in \text{D}ʻP_{\in }.\supset :\text{E}!\text{seq}_{P}ʻ\alpha .\lor.{\sim}\text{E}!\text{max}_{P}ʻ\alpha \\ &[*206·52.*211·11]\end{align}\] -/
theorem pm211_31 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR ∩ connex ∧ A ∈ dom (imgRel P) → EDesc (seqP P) A ∨ ¬ EDesc (maxP P) A := by
  rintro ⟨⟨ht, hc⟩, C, hAC⟩
  by_cases hm : EDesc (maxP P) A
  · obtain ⟨m, hm⟩ := exists_of_edesc hm
    obtain ⟨b, -, hb⟩ := seq_of_max_sect hc (sect_of_seg ht ⟨C, hAC⟩) hAC hm
    exact Or.inl ⟨b, uniq_of (fun t ht => seq_unique hc ht hb) hb⟩
  · exact Or.inr hm

/-- ✱211·311. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .\alpha \in \text{D}ʻP_{\in }.\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\alpha =\overrightarrow{P}ʻ\text{seq}_{P}ʻ\alpha \\ &[*206·31.*211·11]\end{align}\] -/
theorem pm211_311 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ transR ∩ connex ∧ A ∈ dom (imgRel P)) ∧ EDesc (seqP P) A →
      Desc (seqP P) A (fun s => A = refs P s) := by
  rintro ⟨⟨⟨ht, hc⟩, hA⟩, hE⟩
  obtain ⟨s, hs⟩ := exists_of_edesc hE
  exact desc_of (uniq_of (fun t ht => seq_unique hc ht hs) hs)
    (refs_seq_eq hc (sect_of_seg ht hA) hs).symm

/-- ✱211·312. \(\vdash :P\in \text{trans}\cap \text{connex} .\alpha \in \text{D}ʻP_{\in }.\supset .\alpha =Pʻʻ(\alpha \cup \overrightarrow{\text{seq}} _{P}ʻ\alpha )\) -/
theorem pm211_312 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR ∩ connex ∧ A ∈ dom (imgRel P) → A = P ʻʻ (A ∪ refs (seqP P) A) := by
  rintro ⟨⟨ht, hc⟩, C, hAC⟩
  have hA := sect_of_seg ht ⟨C, hAC⟩
  ext x
  constructor
  · intro hx
    by_cases hp : ∃ y, y ∈ A ∧ P x y
    · obtain ⟨y, hy, hxy⟩ := hp
      exact ⟨y, Or.inl hy, hxy⟩
    · have hm : maxP P x A := maxP_iff.2 ⟨⟨hx, hA.1 hx⟩, fun y hy hxy => hp ⟨y, hy, hxy⟩⟩
      obtain ⟨b, hxb, hb⟩ := seq_of_max_sect hc hA hAC hm
      exact ⟨b, Or.inr hb, hxb⟩
  · rintro ⟨y, hy | hy, hxy⟩
    · exact sect_closed hA hxy hy
    · exact pred_seq_mem hc hA hy hxy

/-- ✱211·313. \(\vdash :\alpha \in \text{sect}ʻP\cap \text{D}ʻP_{\in }.\supset .(\exists \beta ).\beta \in \text{sect}ʻP.\alpha =Pʻʻ\beta\) -/
theorem pm211_313 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∈ sect P ∩ dom (imgRel P) → ∃ B, B ∈ sect P ∧ A = P ʻʻ B := by
  rintro ⟨hA, C, hAC⟩
  refine ⟨A ∪ (C ∩ fld P), ⟨fun x hx => ?_, ?_⟩, ?_⟩
  · rcases hx with hx | hx
    · exact hA.1 hx
    · exact hx.2
  · rintro x ⟨y, hy, hxy⟩
    rcases hy with hy | hy
    · exact Or.inl (sect_closed hA hxy hy)
    · exact Or.inl (by rw [hAC]; exact ⟨y, hy.1, hxy⟩)
  · ext x
    constructor
    · intro hx
      have hx' : x ∈ P ʻʻ C := hAC ▸ hx
      obtain ⟨c, hc, hxc⟩ := hx'
      exact ⟨c, Or.inr ⟨hc, fld_r hxc⟩, hxc⟩
    · rintro ⟨y, hy | hy, hxy⟩
      · exact sect_closed hA hxy hy
      · rw [hAC]; exact ⟨y, hy.1, hxy⟩

/-- ✱211·314. \(\vdash :P\in \text{Rl}ʻJ\cap \text{connex} .\alpha \in \text{sect}ʻP\cap \text{D}ʻP_{\in }.\text{E}!\text{max}_{P}ʻ\alpha .\supset .\text{E}!\text{seq}_{P}ʻ\alpha\) -/
theorem pm211_314 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ rl J ∩ connex ∧ A ∈ sect P ∩ dom (imgRel P)) ∧ EDesc (maxP P) A → EDesc (seqP P) A := by
  rintro ⟨⟨⟨-, hc⟩, hA, C, hAC⟩, hE⟩
  obtain ⟨m, hm⟩ := exists_of_edesc hE
  obtain ⟨b, -, hb⟩ := seq_of_max_sect hc hA hAC hm
  exact ⟨b, uniq_of (fun t ht => seq_unique hc ht hb) hb⟩

/-- ✱211·315. \[\begin{align}\vdash \colon\ldotp P\in \text{Rl}ʻJ\cap \text{connex} .\alpha \in &\text{sect}ʻP.\supset :\\ &\alpha \in \text{D}ʻP_{\in }.\equiv .\alpha \in \text{ᗡ}ʻ\text{seq}_{P}\cup -\text{ᗡ}ʻ\text{max}_{P}\end{align}\] -/
theorem pm211_315 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ rl J ∩ connex ∧ A ∈ sect P →
      (A ∈ dom (imgRel P) ↔ A ∈ codom (seqP P) ∪ (codom (maxP P))ᶜ) := by
  rintro ⟨⟨-, hc⟩, hA⟩
  refine ⟨fun ⟨C, hAC⟩ => ?_, seg_of_sect hc hA⟩
  by_cases hm : ∃ m, maxP P m A
  · obtain ⟨m, hm⟩ := hm
    obtain ⟨b, -, hb⟩ := seq_of_max_sect hc hA hAC hm
    exact Or.inl ⟨b, hb⟩
  · exact Or.inr hm

/-- ✱211·316. \[\begin{align}&\vdash :P\in \text{Rl}ʻJ\cap \text{connex} .\supset .\text{sect}ʻP-\text{D}ʻP_{\in }=\text{sect}ʻP\cap \text{ᗡ}ʻ\text{max}_{P}-\text{ᗡ}ʻ\text{seq}_{P}\\ &[*211·315.\text{Transp}]\end{align}\] -/
theorem pm211_316 {α : Type u} {P : α → α → Prop} :
    P ∈ rl J ∩ connex → sect P \ dom (imgRel P) = (sect P ∩ codom (maxP P)) \ codom (seqP P) := by
  intro h
  ext A
  constructor
  · rintro ⟨hA, hD⟩
    rw [pm211_315 ⟨h, hA⟩] at hD
    exact ⟨⟨hA, by by_contra hc; exact hD (Or.inr hc)⟩, fun hs => hD (Or.inl hs)⟩
  · rintro ⟨⟨hA, hm⟩, hs⟩
    refine ⟨hA, fun hD => ?_⟩
    rcases (pm211_315 ⟨h, hA⟩).1 hD with h' | h'
    · exact hs h'
    · exact h' hm

/-- ✱211·317. \(\vdash :P\in \text{trans}.\supset .\text{D}ʻP_{\in }=P_{\in }ʻʻ\text{sect}ʻP\) -/
theorem pm211_317 {α : Type u} {P : α → α → Prop} :
    P ∈ transR → dom (imgRel P) = imgRel P ʻʻ sect P := by
  intro ht
  ext A
  constructor
  · intro hA
    obtain ⟨B, hB, e⟩ := pm211_313 ⟨sect_of_seg ht hA, hA⟩
    exact ⟨B, hB, e⟩
  · rintro ⟨B, -, e⟩
    exact ⟨B, e⟩

/-- ✱211·32. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .\supset .\text{D}ʻP_{\in }=\text{sect}ʻP\cap (\text{ᗡ}ʻ\text{seq}_{P}\cup -\text{ᗡ}ʻ\text{max}_{P})\\ &[*211·24·15·31]\end{align}\] -/
theorem pm211_32 {α : Type u} {P : α → α → Prop} :
    P ∈ transR ∩ connex → dom (imgRel P) = sect P ∩ (codom (seqP P) ∪ (codom (maxP P))ᶜ) := by
  rintro ⟨ht, hc⟩
  ext A
  constructor
  · rintro ⟨C, hAC⟩
    have hA := sect_of_seg ht ⟨C, hAC⟩
    refine ⟨hA, ?_⟩
    by_cases hm : ∃ m, maxP P m A
    · obtain ⟨m, hm⟩ := hm
      obtain ⟨b, -, hb⟩ := seq_of_max_sect hc hA hAC hm
      exact Or.inl ⟨b, hb⟩
    · exact Or.inr hm
  · rintro ⟨hA, h⟩
    exact seg_of_sect hc hA h

/-- ✱211·321. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .\supset .\text{sect}ʻP-\text{D}ʻP_{\in }=\text{sect}ʻP\cap \text{ᗡ}ʻ\text{max}_{P}-\text{ᗡ}ʻ\text{seq}_{P}\\ &[*211·32]\end{align}\] -/
theorem pm211_321 {α : Type u} {P : α → α → Prop} :
    P ∈ transR ∩ connex → sect P \ dom (imgRel P) = (sect P ∩ codom (maxP P)) \ codom (seqP P) := by
  intro h
  rw [pm211_32 h]
  ext A
  constructor
  · rintro ⟨hA, hD⟩
    exact ⟨⟨hA, by by_contra hc; exact hD ⟨hA, Or.inr hc⟩⟩, fun hs => hD ⟨hA, Or.inl hs⟩⟩
  · rintro ⟨⟨hA, hm⟩, hs⟩
    refine ⟨hA, fun ⟨_, h'⟩ => ?_⟩
    rcases h' with h' | h'
    · exact hs h'
    · exact h' hm

/-- ✱211·33. \[\begin{align}\vdash \colon\ldotp P\in &\text{Ser}.\alpha \in \text{sect}ʻP.\supset :\\ &\alpha {\sim}\in \text{D}ʻP_{\in }.\supset .\text{E}!\text{seq}_{P}ʻPʻʻ\alpha .{\sim}\text{E}!\text{seq}_{P}ʻ\overrightarrow{\text{seq}} _{P}ʻPʻʻ\alpha\end{align}\] -/
theorem pm211_33 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser ∧ A ∈ sect P →
      (A ∉ dom (imgRel P) → EDesc (seqP P) (P ʻʻ A) ∧
        ¬ EDesc (seqP P) (refs (seqP P) (P ʻʻ A))) := by
  rintro ⟨hS, hA⟩ hD
  have hc := hS.2
  have tr := mem_transR.1 hS.1.2
  have hm : ∃ m, maxP P m A := by
    by_contra hm
    exact hD (seg_of_sect hc hA (Or.inr hm))
  obtain ⟨m, hm⟩ := hm
  obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
  have hle : ∀ y, y ∈ A → P y m ∨ y = m := by
    intro y hy
    rcases mem_connex.1 hc y m ⟨hA.1 hy, hmf⟩ with (h | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hm' y hy)
  have e : P ʻʻ A = refs P m := by
    ext y
    constructor
    · rintro ⟨z, hz, hyz⟩
      rcases hle z hz with h | rfl
      · exact tr y z m ⟨hyz, h⟩
      · exact hyz
    · intro h
      exact ⟨m, hmA, h⟩
  rw [e]
  have hseq := seq_refs hS hmf
  refine ⟨⟨m, hseq⟩, ?_⟩
  have e2 : refs (seqP P) (refs P m) = ι m := Set.ext hseq
  rw [e2]
  rintro hE
  obtain ⟨s, hs⟩ := exists_of_edesc hE
  apply hD
  refine seg_of_sect hc hA (Or.inl ⟨s, seqP_iff.2 ⟨⟨fun y hy => ?_, (seqP_iff.1 hs).1.2⟩,
    fun z hz hzs => ?_⟩⟩)
  · have hms : P m s := (seqP_iff.1 hs).1.1 m ⟨rfl, hmf⟩
    rcases hle y hy.1 with h | rfl
    · exact tr y m s ⟨h, hms⟩
    · exact hms
  · exact (seqP_iff.1 hs).2 z (fun y hy => by
      have hy' : y = m := hy.1
      rw [hy']; exact hz m ⟨hmA, hmf⟩) hzs

/-- ✱211·34. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.\supset :\alpha \in &\text{sect}ʻP-\text{D}ʻP_{\in }.\equiv .\\ &\alpha =Pʻʻ\alpha \cup \iota ʻ\text{seq}_{P}ʻPʻʻ\alpha .{\sim}\text{E}!\text{seq}_{P}ʻ\overrightarrow{\text{seq}} _{P}ʻPʻʻ\alpha\end{align}\] -/
theorem pm211_34 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser → (A ∈ sect P \ dom (imgRel P) ↔
      Desc (seqP P) (P ʻʻ A) (fun s => A = P ʻʻ A ∪ ι s) ∧
        ¬ EDesc (seqP P) (refs (seqP P) (P ʻʻ A))) := by
  intro hS
  have hc := hS.2
  have tr := mem_transR.1 hS.1.2
  have irr := mem_rl_J.1 hS.1.1
  constructor
  · rintro ⟨hA, hD⟩
    obtain ⟨hE, hnE⟩ := pm211_33 ⟨hS, hA⟩ hD
    refine ⟨?_, hnE⟩
    obtain ⟨s, hs⟩ := exists_of_edesc hE
    refine desc_of (uniq_of (fun t ht => seq_unique hc ht hs) hs) ?_
    have hm : ∃ m, maxP P m A := by
      by_contra hm
      exact hD (seg_of_sect hc hA (Or.inr hm))
    obtain ⟨m, hm⟩ := hm
    obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
    have hsm : s = m := by
      have hseq := seq_refs hS hmf
      have e : P ʻʻ A = refs P m := by
        ext y
        constructor
        · rintro ⟨z, hz, hyz⟩
          rcases mem_connex.1 hc z m ⟨hA.1 hz, hmf⟩ with (h | rfl) | h
          · exact tr y z m ⟨hyz, h⟩
          · exact hyz
          · exact absurd h (hm' z hz)
        · intro h
          exact ⟨m, hmA, h⟩
      rw [e] at hs
      exact (hseq s).1 hs
    subst hsm
    ext y
    constructor
    · intro hy
      by_cases e : y = s
      · exact Or.inr e
      · rcases mem_connex.1 hc y s ⟨hA.1 hy, hmf⟩ with (h | h) | h
        · exact Or.inl ⟨s, hmA, h⟩
        · exact absurd h e
        · exact absurd h (hm' y hy)
    · rintro (hy | hy)
      · exact hA.2 hy
      · have hy' : y = s := hy
        rw [hy']; exact hmA
  · rintro ⟨hd, hnE⟩
    obtain ⟨s, hs1, hs2⟩ := hd
    have hs : seqP P s (P ʻʻ A) := (hs1 s).2 rfl
    have hsf : s ∈ fld P := (seqP_iff.1 hs).1.2
    have hsect : A ∈ sect P := by
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [hs2] at hx
        rcases hx with ⟨y, -, hxy⟩ | hx
        · exact fld_l hxy
        · have hx' : x = s := hx
          rw [hx']; exact hsf
      · rw [hs2]; exact Or.inl hx
    refine ⟨hsect, fun hD => hnE ?_⟩
    have hsA : s ∈ A := by rw [hs2]; exact Or.inr rfl
    have hfol : ∀ y, y ∈ P ʻʻ A → P y s := fun y hy => (seqP_iff.1 hs).1.1 y ⟨hy, by
      obtain ⟨z, -, hyz⟩ := hy; exact fld_l hyz⟩
    have hmax : maxP P s A := by
      refine maxP_iff.2 ⟨⟨hsA, hsf⟩, fun y hy hsy => ?_⟩
      rw [hs2] at hy
      rcases hy with hy | hy
      · exact irr s (tr s y s ⟨hsy, hfol y hy⟩)
      · have hy' : y = s := hy
        rw [hy'] at hsy
        exact irr s hsy
    obtain ⟨C, hAC⟩ := hD
    obtain ⟨t, -, ht⟩ := seq_of_max_sect hc hsect hAC hmax
    have e2 : refs (seqP P) (P ʻʻ A) = ι s := Set.ext fun x => hs1 x
    rw [e2]
    have hts : seqP P t (ι s) := by
      refine seqP_iff.2 ⟨⟨fun y hy => ?_, (seqP_iff.1 ht).1.2⟩, fun z hz hzt => ?_⟩
      · have hy' : y = s := hy.1
        rw [hy']; exact (seqP_iff.1 ht).1.1 s ⟨hsA, hsf⟩
      · refine (seqP_iff.1 ht).2 z (fun y hy => ?_) hzt
        have hzs : P s z := hz s ⟨rfl, hsf⟩
        rw [hs2] at hy
        rcases hy.1 with hy' | hy'
        · exact tr y s z ⟨hfol y hy', hzs⟩
        · have hy'' : y = s := hy'
          rw [hy'']; exact hzs
    exact ⟨t, uniq_of (fun u hu => seq_unique hc hu hts) hts⟩

/-- ✱211·35. \[\begin{align}&\vdash \colon\ldotp P \in \text{Ser} . \supset : \alpha \in \text{sect}ʻP - \text{D}ʻP_{\in } . \equiv .\\ &(\exists x) . x \in CʻP . \alpha = \overrightarrow{P}ʻx \cup {℩}ʻx . {\sim} \text{E}! \breve{P} _{1}ʻx\end{align}\] -/
theorem pm211_35 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser → (A ∈ sect P \ dom (imgRel P) ↔
      ∃ x, (x ∈ fld P ∧ A = refs P x ∪ ι x) ∧ ¬ EDesc (P1 P˘) x) := by
  intro hS
  have hc := hS.2
  have tr := mem_transR.1 hS.1.2
  have irr := mem_rl_J.1 hS.1.1
  constructor
  · rintro ⟨hA, hD⟩
    have hm : ∃ m, maxP P m A := by
      by_contra hm
      exact hD (seg_of_sect hc hA (Or.inr hm))
    obtain ⟨m, hm⟩ := hm
    obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
    refine ⟨m, ⟨hmf, ?_⟩, fun hE => ?_⟩
    · ext y
      constructor
      · intro hy
        rcases mem_connex.1 hc y m ⟨hA.1 hy, hmf⟩ with (h | h) | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h (hm' y hy)
      · rintro (hy | hy)
        · exact sect_closed hA hy hmA
        · have hy' : y = m := hy
          rw [hy']; exact hmA
    · obtain ⟨z, hz⟩ := exists_of_edesc hE
      rw [P1cnv_iff hS] at hz
      apply hD
      refine seg_of_sect hc hA (Or.inl ⟨z, seqP_iff.2 ⟨⟨fun y hy => ?_, fld_r hz.1⟩,
        fun w hw hwz => hz.2 ⟨w, hw m ⟨hmA, hmf⟩, hwz⟩⟩⟩)
      rcases mem_connex.1 hc y m ⟨hy.2, hmf⟩ with (h | rfl) | h
      · exact tr y m z ⟨h, hz.1⟩
      · exact hz.1
      · exact absurd h (hm' y hy.1)
  · rintro ⟨x, ⟨hxf, e⟩, hnE⟩
    have hsect : A ∈ sect P := by
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · rw [e] at hy
        rcases hy with hy | hy
        · exact fld_l hy
        · have hy' : y = x := hy
          rw [hy']; exact hxf
      · obtain ⟨z, hz, hyz⟩ := hy
        rw [e] at hz ⊢
        rcases hz with hz | hz
        · exact Or.inl (tr y z x ⟨hyz, hz⟩)
        · have hz' : z = x := hz
          rw [hz'] at hyz
          exact Or.inl hyz
    refine ⟨hsect, fun hD => hnE ?_⟩
    have hxA : x ∈ A := by rw [e]; exact Or.inr rfl
    have hmax : maxP P x A := by
      refine maxP_iff.2 ⟨⟨hxA, hxf⟩, fun y hy hxy => ?_⟩
      rw [e] at hy
      rcases hy with hy | hy
      · exact irr x (tr x y x ⟨hxy, hy⟩)
      · have hy' : y = x := hy
        rw [hy'] at hxy
        exact irr x hxy
    obtain ⟨C, hAC⟩ := hD
    obtain ⟨s, hxs, hs⟩ := seq_of_max_sect hc hsect hAC hmax
    have hsucc : P x s ∧ ¬∃ w, P x w ∧ P w s := by
      refine ⟨hxs, fun ⟨w, hxw, hws⟩ => (seqP_iff.1 hs).2 w (fun y hy => ?_) hws⟩
      have hy' := hy.1
      rw [e] at hy'
      rcases hy' with hy' | hy'
      · exact tr y x w ⟨hy', hxw⟩
      · have hy'' : y = x := hy'
        rw [hy'']; exact hxw
    refine ⟨s, uniq_of (fun z hz => ?_) ((P1cnv_iff hS).2 hsucc)⟩
    exact succ_unique hS ((P1cnv_iff hS).1 hz) hsucc

/-- ✱211·351. \(\vdash : P \in \text{Ser} . \supset . \text{sect}ʻP - \text{D}ʻP_{\in } = \overrightarrow{P}_{*}ʻʻ(CʻP - \text{D}ʻP_{1})\) -/
theorem pm211_351 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → sect P \ dom (imgRel P) = Rfwd (anc P) ʻʻ (fld P \ dom (P1 P)) := by
  intro hS
  have hrefs : ∀ x, x ∈ fld P → refs (anc P) x = refs P x ∪ ι x := by
    intro x hx
    ext y
    show anc P y x ↔ _
    rw [anc_iff_of_transR hS.1.2]
    constructor
    · rintro (⟨rfl, -⟩ | h)
      · exact Or.inr rfl
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · have h' : y = x := h
        exact Or.inl ⟨h', h' ▸ hx⟩
  have hsucc : ∀ x, ¬ EDesc (P1 P˘) x ↔ x ∉ dom (P1 P) := by
    intro x
    rw [edesc_iff_ex (fun a b ha hb => succ_unique hS ((P1cnv_iff hS).1 ha) ((P1cnv_iff hS).1 hb))]
    constructor
    · rintro h ⟨z, hz⟩
      exact h ⟨z, (P1cnv_iff hS).2 ((P1_iff' hS).1 hz)⟩
    · rintro h ⟨z, hz⟩
      exact h ⟨z, (P1_iff' hS).2 ((P1cnv_iff hS).1 hz)⟩
  ext A
  rw [pm211_35 hS]
  constructor
  · rintro ⟨x, ⟨hx, e⟩, hn⟩
    exact ⟨x, ⟨hx, (hsucc x).1 hn⟩, show A = refs (anc P) x by rw [hrefs x hx]; exact e⟩
  · rintro ⟨x, ⟨hx, hn⟩, e⟩
    have e' : A = refs (anc P) x := e
    exact ⟨x, ⟨hx, by rw [← hrefs x hx]; exact e'⟩, (hsucc x).2 hn⟩

/-- ✱211·36. \(\vdash \colon\ldotp P \in \text{Ser} . \text{D}ʻP_{1} = \text{D}ʻP . \supset : \alpha \in \text{sect}ʻP - \text{D}ʻP_{\in } . \equiv . \alpha = CʻP . \text{E}! Bʻ\breve{P}\) -/
theorem pm211_36 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser ∧ dom (P1 P) = dom P →
      (A ∈ sect P \ dom (imgRel P) ↔ A = fld P ∧ EDesc Beg P˘) := by
  rintro ⟨hS, hd⟩
  have hc := hS.2
  rw [pm211_351 hS, hd]
  have hlast : ∀ x, x ∈ fld P \ dom P → ∀ y, Beg y P˘ ↔ y = x := by
    rintro x ⟨hxf, hxd⟩ y
    constructor
    · rintro ⟨hy1, hy2⟩
      have hyf : y ∈ fld P := by obtain ⟨w, hw⟩ := hy1; exact fld_r (show P w y from hw)
      rcases mem_connex.1 hc y x ⟨hyf, hxf⟩ with (h | h) | h
      · exact absurd ⟨x, h⟩ hy2
      · exact h
      · exact absurd ⟨y, h⟩ hxd
    · rintro rfl
      refine ⟨?_, hxd⟩
      obtain ⟨w, hw | hw⟩ := hxf
      · exact absurd ⟨w, hw⟩ hxd
      · exact ⟨w, hw⟩
  have hfld : ∀ x, x ∈ fld P \ dom P → refs (anc P) x = fld P := by
    rintro x ⟨hxf, hxd⟩
    ext y
    show anc P y x ↔ _
    rw [anc_iff_of_transR hS.1.2]
    constructor
    · rintro (⟨-, hy⟩ | h)
      · exact hy
      · exact fld_l h
    · intro hy
      rcases mem_connex.1 hc y x ⟨hy, hxf⟩ with (h | h) | h
      · exact Or.inr h
      · exact Or.inl ⟨h, hy⟩
      · exact absurd ⟨y, h⟩ hxd
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hfld x hx, ⟨x, hlast x hx⟩⟩
  · rintro ⟨rfl, b, hb⟩
    have hbB := (hb b).2 rfl
    have hbx : b ∈ fld P \ dom P := by
      obtain ⟨⟨w, hw⟩, hb2⟩ := hbB
      exact ⟨fld_r hw, hb2⟩
    exact ⟨b, hbx, (hfld b hbx).symm⟩

/-- ✱211·361. \(\vdash :P\in \text{Ser}.\text{D}ʻP_{1}=CʻP.\supset .\text{sect}ʻP=\text{D}ʻP_{\in }\) -/
theorem pm211_361 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser ∧ dom (P1 P) = fld P → sect P = dom (imgRel P) := by
  rintro ⟨hS, hd⟩
  refine Set.Subset.antisymm (fun A hA => ?_) (pm211_15 hS.1.2)
  by_contra hD
  have h : A ∈ Rfwd (anc P) ʻʻ (fld P \ dom (P1 P)) := by
    rw [← pm211_351 hS]; exact ⟨hA, hD⟩
  obtain ⟨x, ⟨hx, hxd⟩, -⟩ := h
  rw [hd] at hxd
  exact hxd hx

/-- ✱211·371. \[\begin{align}&\vdash \colon\ldotp P\in \text{trans}\cap \text{connex} :(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}:\supset .\text{D}ʻP_{\in }\subset \text{ᗡ}ʻ\text{seq}_{P}\\ &[*211·32]\end{align}\] -/
theorem pm211_371 {α : Type u} {P : α → α → Prop} :
    P ∈ transR ∩ connex ∧ (∀ A, A ∈ codom (maxP P) ∪ codom (seqP P)) →
      dom (imgRel P) ⊆ codom (seqP P) := by
  rintro ⟨h, hD⟩ A hA
  rw [pm211_32 h] at hA
  rcases hA.2 with hs | hm
  · exact hs
  · rcases hD A with h' | h'
    · exact absurd h' hm
    · exact h'

/-- ✱211·372. \(\vdash \colon\ldotp P\in \text{trans}\cap \text{connex} :(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}:\supset .\text{D}ʻP_{\in }=\overrightarrow{P}ʻʻCʻP\) -/
theorem pm211_372 {α : Type u} {P : α → α → Prop} :
    P ∈ transR ∩ connex ∧ (∀ A, A ∈ codom (maxP P) ∪ codom (seqP P)) →
      dom (imgRel P) = Rfwd P ʻʻ fld P := by
  rintro ⟨⟨ht, hc⟩, hD⟩
  refine Set.Subset.antisymm (fun A hA => ?_) pm211_3
  obtain ⟨s, hs⟩ := pm211_371 ⟨⟨ht, hc⟩, hD⟩ hA
  exact ⟨s, (seqP_iff.1 hs).1.2, (refs_seq_eq hc (sect_of_seg ht hA) hs).symm⟩

/-- ✱211·38. \(\vdash \colon\ldotp P\in \text{Ser}.\supset :(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}.\equiv .\text{D}ʻP_{\in }=\overrightarrow{P}ʻʻCʻP\) -/
theorem pm211_38 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → ((∀ A, A ∈ codom (maxP P) ∪ codom (seqP P)) ↔ dom (imgRel P) = Rfwd P ʻʻ fld P) := by
  intro hS
  have tr := mem_transR.1 hS.1.2
  have irr := mem_rl_J.1 hS.1.1
  refine ⟨fun h => pm211_372 ⟨⟨hS.1.2, hS.2⟩, h⟩, fun e A => ?_⟩
  by_cases hm : ∃ m, maxP P m A
  · exact Or.inl hm
  · have hseg : P ʻʻ A ∈ dom (imgRel P) := ⟨A, rfl⟩
    rw [e] at hseg
    obtain ⟨x, hx, ex⟩ := hseg
    have ex' : P ʻʻ A = refs P x := ex
    refine Or.inr ⟨x, seqP_iff.2 ⟨⟨fun y hy => ?_, hx⟩, fun w hw hwx => ?_⟩⟩
    · have : y ∈ P ʻʻ A := by
        by_contra hy'
        exact hm ⟨y, maxP_iff.2 ⟨hy, fun z hz hyz => hy' ⟨z, hz, hyz⟩⟩⟩
      rw [ex'] at this
      exact this
    · have hw' : w ∈ P ʻʻ A := by rw [ex']; exact hwx
      obtain ⟨z, hz, hwz⟩ := hw'
      exact irr w (tr w z w ⟨hwz, hw z ⟨hz, fld_r hwz⟩⟩)

/-- ✱211·4. \(\vdash .\text{D}ʻ(P_{\in }\dot{\cap} I)\subset -\text{ᗡ}ʻ\text{max}_{P}\) -/
theorem pm211_4 {α : Type u} {P : α → α → Prop} : dom (imgRel P ⩀ I) ⊆ (codom (maxP P))ᶜ := by
  rintro A hA ⟨m, hm⟩
  have e : A = P ʻʻ A := mem_dom_imgRel_rcap_I.1 hA
  obtain ⟨⟨hmA, -⟩, hm'⟩ := maxP_iff.1 hm
  have : m ∈ P ʻʻ A := e ▸ hmA
  obtain ⟨y, hy, hmy⟩ := this
  exact hm' y hy hmy

/-- ✱211·41. \(\vdash .\text{D}ʻ(P_{\in }\dot{\cap} I)=\text{sect}ʻP-\text{ᗡ}ʻ\text{max}_{P}\) -/
theorem pm211_41 {α : Type u} {P : α → α → Prop} :
    dom (imgRel P ⩀ I) = sect P \ codom (maxP P) := by
  ext A
  constructor
  · intro hA
    exact ⟨pm211_14.2 hA, pm211_4 hA⟩
  · rintro ⟨hA, hm⟩
    exact mem_dom_imgRel_rcap_I.2 (eq_img_of_nomax hA hm)

/-- ✱211·411. \(\vdash :P\in \text{trans}.\alpha =Pʻʻ\beta .\alpha \subset Pʻʻ\alpha .\supset .\alpha =Pʻʻ\alpha\) -/
theorem pm211_411 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    (P ∈ transR ∧ A = P ʻʻ B) ∧ A ⊆ P ʻʻ A → A = P ʻʻ A := by
  rintro ⟨⟨ht, e⟩, h⟩
  refine Set.Subset.antisymm h ?_
  have hs : A ∈ sect P := sect_of_seg ht ⟨B, e⟩
  exact hs.2

/-- ✱211·42. \(\vdash :P\in \text{trans}.\supset .\text{D}ʻ(P_{\in }\dot{\cap} I)=\text{D}ʻP_{\in }-\text{ᗡ}ʻ\text{max}_{P}\) -/
theorem pm211_42 {α : Type u} {P : α → α → Prop} :
    P ∈ transR → dom (imgRel P ⩀ I) = dom (imgRel P) \ codom (maxP P) := by
  intro ht
  rw [pm211_41]
  ext A
  constructor
  · rintro ⟨hA, hm⟩
    exact ⟨⟨A, eq_img_of_nomax hA hm⟩, hm⟩
  · rintro ⟨hA, hm⟩
    exact ⟨sect_of_seg ht hA, hm⟩

/-- ✱211·43. \(\vdash :P\in \text{trans}\cap \text{connex} .\supset .\text{D}ʻP_{\in }-\text{ᗡ}ʻ\text{seq}_{P}\subset \text{D}ʻ(P_{\in }\dot{\cap} I)\) -/
theorem pm211_43 {α : Type u} {P : α → α → Prop} :
    P ∈ transR ∩ connex → dom (imgRel P) \ codom (seqP P) ⊆ dom (imgRel P ⩀ I) := by
  rintro ⟨ht, hc⟩ A ⟨⟨C, hAC⟩, hs⟩
  have hA := sect_of_seg ht ⟨C, hAC⟩
  refine mem_dom_imgRel_rcap_I.2 (eq_img_of_nomax hA ?_)
  rintro ⟨m, hm⟩
  obtain ⟨b, -, hb⟩ := seq_of_max_sect hc hA hAC hm
  exact hs ⟨b, hb⟩

/-- ✱211·431. \[\begin{align}\vdash :P\in \text{trans}\cap &\text{connex} .\supset .\\ &\text{D}ʻP_{\in }-\text{D}ʻ(P_{\in }\dot{\cap} I)=\text{sect}ʻP\cap \text{ᗡ}ʻ\text{max}_{P}\cap \text{ᗡ}ʻ\text{seq}_{P}\\ [*211·32·41]\end{align}\] -/
theorem pm211_431 {α : Type u} {P : α → α → Prop} :
    P ∈ transR ∩ connex →
      dom (imgRel P) \ dom (imgRel P ⩀ I) = sect P ∩ codom (maxP P) ∩ codom (seqP P) := by
  rintro ⟨ht, hc⟩
  ext A
  constructor
  · rintro ⟨⟨C, hAC⟩, hI⟩
    have hA := sect_of_seg ht ⟨C, hAC⟩
    have hm : ∃ m, maxP P m A := by
      by_contra hm
      exact hI (mem_dom_imgRel_rcap_I.2 (eq_img_of_nomax hA hm))
    obtain ⟨m, hm⟩ := hm
    obtain ⟨b, -, hb⟩ := seq_of_max_sect hc hA hAC hm
    exact ⟨⟨hA, m, hm⟩, b, hb⟩
  · rintro ⟨⟨hA, hm⟩, hs⟩
    exact ⟨seg_of_sect hc hA (Or.inl hs), fun hI => pm211_4 hI hm⟩

/-- ✱211·44. \[\begin{align}&\vdash .\Lambda \in \text{D}ʻ(P_{\in }\dot{\cap} I).\Lambda \in \text{D}ʻP_{\in }.\Lambda \in \text{sect}ʻP\\ &[*37·29.*211·12·14]\end{align}\] -/
theorem pm211_44 {α : Type u} {P : α → α → Prop} :
    ((Λ : Set α) ∈ dom (imgRel P ⩀ I) ∧ (Λ : Set α) ∈ dom (imgRel P)) ∧ (Λ : Set α) ∈ sect P := by
  have e : (Λ : Set α) = P ʻʻ Λ := by
    rw [Null_eq_empty]
    ext x
    exact ⟨fun h => absurd h (Set.notMem_empty x), fun ⟨y, hy, _⟩ => absurd hy (Set.notMem_empty y)⟩
  have h1 : (Λ : Set α) ∈ dom (imgRel P ⩀ I) := mem_dom_imgRel_rcap_I.2 e
  exact ⟨⟨h1, pm211_14.1 h1⟩, pm211_14.2 h1⟩

/-- ✱211·45. \(\vdash :P\in \text{trans}.x{\sim}\in \text{ᗡ}ʻ(P\dot{-} P^{2}).\supset .\overrightarrow{P}ʻx\in \text{D}ʻ(P_{\in}\dot{\cap} I)\) -/
theorem pm211_45 {α : Type u} {P : α → α → Prop} {x : α} :
    P ∈ transR ∧ x ∉ codom (P ∸ rsq P) → refs P x ∈ dom (imgRel P ⩀ I) := by
  rintro ⟨ht, hx⟩
  refine mem_dom_imgRel_rcap_I.2 (Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_))
  · by_contra h
    apply hx
    refine ⟨y, hy, fun ⟨z, hyz, hzx⟩ => h ⟨z, hzx, hyz⟩⟩
  · obtain ⟨z, hz, hyz⟩ := hy
    exact mem_transR.1 ht y z x ⟨hyz, hz⟩

/-- ✱211·451. \(\vdash :\overrightarrow{P}ʻx\in \text{D}ʻ(P_{\in }\dot{\cap} I).\supset .x{\sim}\in \text{ᗡ}ʻ(P\dot{-} P^{2})\) -/
theorem pm211_451 {α : Type u} {P : α → α → Prop} {x : α} :
    refs P x ∈ dom (imgRel P ⩀ I) → x ∉ codom (P ∸ rsq P) := by
  intro h
  have e : refs P x = P ʻʻ refs P x := mem_dom_imgRel_rcap_I.1 h
  rintro ⟨y, hyx, hn⟩
  have : y ∈ P ʻʻ refs P x := e ▸ hyx
  obtain ⟨z, hz, hyz⟩ := this
  exact hn ⟨z, hyz, hz⟩

/-- ✱211·452. \[\begin{align}&\vdash \colon\ldotp P\in \text{trans}.\supset :\overrightarrow{P}ʻx\in \text{D}ʻ(P_{\in }\dot{\cap} I).\equiv .x{\sim}\in \text{ᗡ}ʻ(P\dot{-} P^{2})\\ &[*211*·45·451]\end{align}\] -/
theorem pm211_452 {α : Type u} {P : α → α → Prop} {x : α} :
    P ∈ transR → (refs P x ∈ dom (imgRel P ⩀ I) ↔ x ∉ codom (P ∸ rsq P)) :=
  fun ht => ⟨pm211_451, fun h => pm211_45 ⟨ht, h⟩⟩

/-- ✱211·46. \[\begin{align}\vdash \colon\ldotp P\in \text{trans}\cap \text{connex} :(\alpha ).\alpha \in &\text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}:\supset .\\ &\text{D}ʻ(P_{\in }\dot{\cap} I)=\overrightarrow{P}ʻʻ\{CʻP-\text{ᗡ}ʻ(P\dot{-} P^{2})\}\end{align}\] -/
theorem pm211_46 {α : Type u} {P : α → α → Prop} :
    P ∈ transR ∩ connex ∧ (∀ A, A ∈ codom (maxP P) ∪ codom (seqP P)) →
      dom (imgRel P ⩀ I) = Rfwd P ʻʻ (fld P \ codom (P ∸ rsq P)) := by
  rintro ⟨⟨ht, hc⟩, hD⟩
  ext A
  constructor
  · intro hA
    have h2 : A ∈ Rfwd P ʻʻ fld P := by
      rw [← pm211_372 ⟨⟨ht, hc⟩, hD⟩]; exact pm211_14.1 hA
    obtain ⟨x, hx, e⟩ := h2
    have e' : A = refs P x := e
    refine ⟨x, ⟨hx, pm211_451 (e' ▸ hA)⟩, e⟩
  · rintro ⟨x, ⟨-, hx⟩, e⟩
    have e' : A = refs P x := e
    rw [e']
    exact pm211_45 ⟨ht, hx⟩

/-- ✱211·47. \(\vdash \colon\ldotp P\in \text{trans}.\supset :(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}.\equiv .\text{D}ʻ(P_{\in }\dot{\cap} I)\subset \text{ᗡ}ʻ\text{seq}_{P}\) -/
theorem pm211_47 {α : Type u} {P : α → α → Prop} :
    P ∈ transR → ((∀ A, A ∈ codom (maxP P) ∪ codom (seqP P)) ↔
      dom (imgRel P ⩀ I) ⊆ codom (seqP P)) := by
  intro ht
  constructor
  · intro h A hA
    rcases h A with h' | h'
    · exact absurd h' (pm211_4 hA)
    · exact h'
  · intro h
    refine (pm211_272 ht).2 fun A hA => ?_
    by_cases hm : ∃ m, maxP P m A
    · exact Or.inl hm
    · exact Or.inr (h (mem_dom_imgRel_rcap_I.2 (eq_img_of_nomax hA hm)))

/-- ✱211·5. \(\vdash :P^{2}=P.\alpha =Pʻʻ\beta .\supset .\alpha =Pʻʻ\alpha\) -/
theorem pm211_5 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    rsq P = P ∧ A = P ʻʻ B → A = P ʻʻ A := by
  rintro ⟨e, rfl⟩
  ext x
  constructor
  · rintro ⟨b, hb, hxb⟩
    have h : rsq P x b := by rw [e]; exact hxb
    obtain ⟨z, hxz, hzb⟩ := h
    exact ⟨z, ⟨b, hb, hzb⟩, hxz⟩
  · rintro ⟨z, ⟨b, hb, hzb⟩, hxz⟩
    have h : rsq P x b := ⟨z, hxz, hzb⟩
    rw [e] at h
    exact ⟨b, hb, h⟩

/-- ✱211·51. \(\vdash :P^{2}=P.\supset .\text{D}ʻP_{\in }=\text{D}ʻ(P_{\in }\dot{\cap} I) \quad[*211·5·11·12]\) -/
theorem pm211_51 {α : Type u} {P : α → α → Prop} :
    rsq P = P → dom (imgRel P) = dom (imgRel P ⩀ I) := by
  intro e
  refine Set.Subset.antisymm (fun A ⟨B, hAB⟩ => mem_dom_imgRel_rcap_I.2 (pm211_5 ⟨e, hAB⟩))
    pm211_14.1

/-- ✱211·52. \(\vdash \colon\ldotp P^{2}=P.P\in \text{connex} .\supset :\text{E}!\text{max}_{P}ʻ\alpha .\supset .{\sim}\text{E}!\text{seq}_{P}ʻ\alpha\) -/
theorem pm211_52 {α : Type u} {P : α → α → Prop} {A : Set α} :
    rsq P = P ∧ P ∈ connex → (EDesc (maxP P) A → ¬ EDesc (seqP P) A) := by
  rintro ⟨e, hc⟩ hM hS
  obtain ⟨m, hm⟩ := exists_of_edesc hM
  obtain ⟨s, hs⟩ := exists_of_edesc hS
  obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
  obtain ⟨⟨hs1, hs2⟩, hs3⟩ := seqP_iff.1 hs
  have hms : rsq P m s := by rw [e]; exact hs1 m ⟨hmA, hmf⟩
  obtain ⟨z, hmz, hzs⟩ := hms
  refine hs3 z (fun y hy => ?_) hzs
  rcases mem_connex.1 hc y z ⟨hy.2, fld_r hmz⟩ with (h | h) | h
  · exact h
  · rw [h] at hy
    exact absurd hmz (hm' z hy.1)
  · have : rsq P m y := ⟨z, hmz, h⟩
    rw [e] at this
    exact absurd this (hm' y hy.1)

/-- ✱211·53. \[\begin{align}\vdash \colon\colon P^{2}=P.P\in \text{connex} .\supset \colon\ldotp \text{E}!\text{max}_{P}ʻ\alpha .&\lor.\text{E}!\text{seq}_{P}ʻ\alpha :\equiv :\\ &\text{E}!\text{max}_{P}ʻ\alpha .\equiv .{\sim}\text{E}!\text{seq}_{P}ʻ\alpha\end{align}\] -/
theorem pm211_53 {α : Type u} {P : α → α → Prop} {A : Set α} :
    rsq P = P ∧ P ∈ connex →
      ((EDesc (maxP P) A ∨ EDesc (seqP P) A) ↔ (EDesc (maxP P) A ↔ ¬ EDesc (seqP P) A)) := by
  intro h
  have h' := pm211_52 (A := A) h
  tauto

/-- ✱211·54. \(\vdash \colon\ldotp P\,\unicode{x2abd}\, J:\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .\supset _{\alpha }.{\sim}\exists !\overrightarrow{\text{seq}} _{P}ʻ\alpha :\supset .P\,\unicode{x2abd}\, P^{2}\) -/
theorem pm211_54 {α : Type u} {P : α → α → Prop} :
    P ⪽ J ∧ (∀ A, (refs (maxP P) A).Nonempty → ¬ (refs (seqP P) A).Nonempty) → P ⪽ rsq P := by
  rintro ⟨hJ, h⟩ x y hxy
  have hm : (refs (maxP P) (ι x)).Nonempty := by
    refine ⟨x, maxP_iff.2 ⟨⟨rfl, fld_l hxy⟩, fun z hz hxz => ?_⟩⟩
    have hz' : z = x := hz
    rw [hz'] at hxz
    exact hJ x x hxz rfl
  by_contra hn
  refine h _ hm ⟨y, seqP_iff.2 ⟨⟨fun z hz => ?_, fld_r hxy⟩, fun w hw hwy => hn ⟨w, ?_, hwy⟩⟩⟩
  · have hz' : z = x := hz.1
    rw [hz']; exact hxy
  · exact hw x ⟨rfl, fld_l hxy⟩

/-- ✱211·541.\(\vdash \colon\ldotp P\in \text{Rl}ʻJ\cap \text{trans}:\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .\supset _{\alpha }.{\sim}\exists !\overrightarrow{\text{seq}} _{P}ʻ\alpha :\supset .P=P^{2}\) -/
theorem pm211_541 {α : Type u} {P : α → α → Prop} :
    P ∈ rl J ∩ transR ∧ (∀ A, (refs (maxP P) A).Nonempty → ¬ (refs (seqP P) A).Nonempty) →
      P = rsq P := by
  rintro ⟨⟨hJ, ht⟩, h⟩
  funext x y
  apply propext
  constructor
  · intro hxy
    have hm : (refs (maxP P) (ι x)).Nonempty := by
      refine ⟨x, maxP_iff.2 ⟨⟨rfl, fld_l hxy⟩, fun z hz hxz => ?_⟩⟩
      have hz' : z = x := hz
      rw [hz'] at hxz
      exact mem_rl_J.1 hJ x hxz
    by_contra hn
    refine h _ hm ⟨y, seqP_iff.2 ⟨⟨fun z hz => ?_, fld_r hxy⟩, fun w hw hwy => hn ⟨w, ?_, hwy⟩⟩⟩
    · have hz' : z = x := hz.1
      rw [hz']; exact hxy
    · exact hw x ⟨rfl, fld_l hxy⟩
  · rintro ⟨z, hxz, hzy⟩
    exact mem_transR.1 ht x z y ⟨hxz, hzy⟩

/-- ✱211·55. \[\begin{align}&\vdash \colon\colon P\in \text{Ser}.\supset \colon\ldotp \exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .\supset _{\alpha }.{\sim}\exists !\overrightarrow{\text{seq}} _{P}ʻ\alpha :\equiv .P=P^{2}\\ &[*211·52·541]\end{align}\] -/
theorem pm211_55 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → ((∀ A, (refs (maxP P) A).Nonempty → ¬ (refs (seqP P) A).Nonempty) ↔ P = rsq P) := by
  intro hS
  refine ⟨fun h => pm211_541 ⟨⟨hS.1.1, hS.1.2⟩, h⟩, fun e A ⟨m, hm⟩ ⟨s, hs⟩ => ?_⟩
  refine pm211_52 ⟨e.symm, hS.2⟩ ⟨m, uniq_of (fun n hn => max_unique hS.2 hn hm) hm⟩
    ⟨s, uniq_of (fun t ht => seq_unique hS.2 ht hs) hs⟩

/-- ✱211·551. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.\supset :\text{ᗡ}ʻ\text{max}_{P}\cap \text{ᗡ}ʻ\text{seq}_{P}=\Lambda .\equiv .P=P^{2}\\ &[*211·55.*33·41]\end{align}\] -/
theorem pm211_551 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → (codom (maxP P) ∩ codom (seqP P) = Λ ↔ P = rsq P) := by
  intro hS
  rw [← pm211_55 hS, eqΛ]
  constructor
  · intro h A hm hs
    exact h A ⟨hm, hs⟩
  · rintro h A ⟨hm, hs⟩
    exact h A hm hs

/-- ✱211·552. \[\begin{align}\vdash \colon\colon P\in \text{Ser}.\supset \colon\ldotp \text{E}!\text{max}_{P}ʻ\alpha .&\equiv _{\alpha }.{\sim}\text{E}!\text{seq}_{P}ʻ\alpha :\equiv :\\ &P=P^{2}:(\alpha ):\text{E}!\text{max}_{P}ʻ\alpha .\lor.\text{E}!\text{seq}_{P}ʻ\alpha \\ &[*211·55]\end{align}\] -/
theorem pm211_552 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → ((∀ A, EDesc (maxP P) A ↔ ¬ EDesc (seqP P) A) ↔
      P = rsq P ∧ ∀ A, EDesc (maxP P) A ∨ EDesc (seqP P) A) := by
  intro hS
  have hM : ∀ A, EDesc (maxP P) A ↔ ∃ m, maxP P m A :=
    fun A => edesc_iff_ex (fun a b ha hb => max_unique hS.2 ha hb)
  have hQ : ∀ A, EDesc (seqP P) A ↔ ∃ s, seqP P s A :=
    fun A => edesc_iff_ex (fun a b ha hb => seq_unique hS.2 ha hb)
  rw [← pm211_55 hS]
  constructor
  · intro h
    refine ⟨fun A hm hs => ?_, fun A => ?_⟩
    · exact ((h A).1 ((hM A).2 hm)) ((hQ A).2 hs)
    · by_cases hm : EDesc (maxP P) A
      · exact Or.inl hm
      · exact Or.inr (by by_contra hs; exact hm ((h A).2 hs))
  · rintro ⟨h1, h2⟩ A
    constructor
    · intro hm hs
      exact h1 A ((hM A).1 hm) ((hQ A).1 hs)
    · intro hs
      rcases h2 A with h | h
      · exact h
      · exact absurd h hs

/-- ✱211·553. \[\begin{align}\vdash \colon\colon P\in \text{Ser}.\supset \colon\ldotp \text{ᗡ}ʻ\text{max}_{P}=-&\text{ᗡ}ʻ\text{seq}_{P}.\equiv :\\ &P=P^{2}:(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}\\ [*211·552.*71·163]\end{align}\] -/
theorem pm211_553 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → (codom (maxP P) = (codom (seqP P))ᶜ ↔
      P = rsq P ∧ ∀ A, A ∈ codom (maxP P) ∪ codom (seqP P)) := by
  intro hS
  rw [← pm211_55 hS]
  constructor
  · intro e
    refine ⟨fun A hm hs => ?_, fun A => ?_⟩
    · have : A ∈ (codom (seqP P))ᶜ := e ▸ hm
      exact this hs
    · by_cases hm : A ∈ codom (maxP P)
      · exact Or.inl hm
      · refine Or.inr ?_
        by_contra hs
        exact hm (e ▸ hs)
  · rintro ⟨h1, h2⟩
    ext A
    constructor
    · intro hm hs
      exact h1 A hm hs
    · intro hs
      rcases h2 A with h | h
      · exact h
      · exact absurd h hs

/-- ✱211·56. \(\vdash \colon\ldotp P\in \text{connex} .\alpha ,\beta \in \text{sect}ʻP.\supset :\alpha \subset \beta .\lor.\beta \subset Pʻʻ\alpha\) -/
theorem pm211_56 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    P ∈ connex ∧ (A ∈ sect P ∧ B ∈ sect P) → A ⊆ B ∨ B ⊆ P ʻʻ A := by
  rintro ⟨hc, hA, hB⟩
  by_cases h : A ⊆ B
  · exact Or.inl h
  · obtain ⟨x, hxA, hxB⟩ := Set.not_subset.1 h
    exact Or.inr fun y hy => ⟨x, hxA, follow_of_sect hc hB (hA.1 hxA) hxB hy⟩

/-- ✱211·561. \[\begin{align}&\vdash \colon\ldotp P_{\text{po}}\in \text{connex} .\alpha ,\beta \in \text{sect}ʻP.\supset :\alpha \subset \beta .\lor.\beta \subset Pʻʻ\alpha \\ &[*211·56·17·131]\end{align}\] -/
theorem pm211_561 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    po P ∈ connex ∧ (A ∈ sect P ∧ B ∈ sect P) → A ⊆ B ∨ B ⊆ P ʻʻ A := by
  rintro ⟨hc, hA, hB⟩
  rw [img_po_of_sect hA]
  rw [← sect_po] at hA hB
  exact pm211_56 ⟨hc, hA, hB⟩

/-- ✱211·562. \(\vdash \colon\ldotp P_{\text{po}}\in \text{connex} .\alpha ,\beta \in \text{sect}ʻP.\supset :\alpha \subset \beta .\lor.\beta \subset \alpha \quad[*211·561·1]\) -/
theorem pm211_562 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    po P ∈ connex ∧ (A ∈ sect P ∧ B ∈ sect P) → A ⊆ B ∨ B ⊆ A := by
  rintro ⟨hc, hA, hB⟩
  rcases pm211_561 ⟨hc, hA, hB⟩ with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hA.2)

/-- ✱211·6. \(\vdash \colon\ldotp P\in \text{connex} .\alpha ,\beta \in \text{sect}ʻP.\supset :\alpha \subset \beta .\lor.\beta \subset \alpha \quad[*211·56·1]\) -/
theorem pm211_6 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    P ∈ connex ∧ (A ∈ sect P ∧ B ∈ sect P) → A ⊆ B ∨ B ⊆ A := by
  rintro ⟨hc, hA, hB⟩
  rcases pm211_56 ⟨hc, hA, hB⟩ with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hA.2)

/-- ✱211·61. \[\begin{align}&\vdash \colon\ldotp P\in \text{trans}\cap \text{connex} .\alpha ,\beta \in \text{D}ʻP_{\in }.\supset :\alpha \subset \beta .\lor.\beta \subset \alpha \\ &[*211·15·6]\end{align}\] -/
theorem pm211_61 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    P ∈ transR ∩ connex ∧ (A ∈ dom (imgRel P) ∧ B ∈ dom (imgRel P)) → A ⊆ B ∨ B ⊆ A := by
  rintro ⟨⟨ht, hc⟩, hA, hB⟩
  exact pm211_6 ⟨hc, sect_of_seg ht hA, sect_of_seg ht hB⟩

/-- ✱211·62. \(\vdash \colon\ldotp P\in \text{connex} .\alpha ,\beta \in \text{D}ʻ(P_{\in }\dot{\cap} I).\supset :\alpha \subset \beta .\lor.\beta \subset \alpha \quad[*211·14·6]\) -/
theorem pm211_62 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    P ∈ connex ∧ (A ∈ dom (imgRel P ⩀ I) ∧ B ∈ dom (imgRel P ⩀ I)) → A ⊆ B ∨ B ⊆ A := by
  rintro ⟨hc, hA, hB⟩
  exact pm211_6 ⟨hc, pm211_14.2 hA, pm211_14.2 hB⟩

/-- ✱211·63. \(\vdash :\lambda \subset \text{sect}ʻP.\supset .sʻ\lambda \in \text{sect}ʻP\) -/
theorem pm211_63 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    L ⊆ sect P → sumCls L ∈ sect P := by
  intro hL
  refine ⟨fun x ⟨A, hA, hx⟩ => (hL hA).1 hx, ?_⟩
  rintro x ⟨y, ⟨A, hA, hy⟩, hxy⟩
  exact ⟨A, hA, sect_closed (hL hA) hxy hy⟩

/-- ✱211·631. \(\vdash :\lambda \subset \text{sect}ʻP.\supset .pʻ\lambda \cap CʻP\in \text{sect}ʻP\) -/
theorem pm211_631 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    L ⊆ sect P → prodCls L ∩ fld P ∈ sect P := by
  intro hL
  refine ⟨fun x hx => hx.2, ?_⟩
  rintro x ⟨y, ⟨hy, -⟩, hxy⟩
  exact ⟨fun A hA => sect_closed (hL hA) hxy (hy A hA), fld_l hxy⟩

/-- ✱211·632. \(\vdash :\lambda \subset \text{sect}ʻP.\exists !\lambda .\supset .pʻ\lambda \in \text{sect}ʻP\) -/
theorem pm211_632 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    L ⊆ sect P ∧ L.Nonempty → prodCls L ∈ sect P := by
  rintro ⟨hL, A, hA⟩
  refine ⟨fun x hx => (hL hA).1 (hx A hA), ?_⟩
  rintro x ⟨y, hy, hxy⟩
  exact fun B hB => sect_closed (hL hB) hxy (hy B hB)

/-- ✱211·633. \(\vdash :\lambda \subset \text{sect}ʻP.\supset .pʻ\lambda \cap sʻ\text{sect}ʻP\in \text{sect}ʻP \quad[*211·631·26]\) -/
theorem pm211_633 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    L ⊆ sect P → prodCls L ∩ sumCls (sect P) ∈ sect P := by
  intro hL
  rw [pm211_26.2]
  exact pm211_631 hL

/-- ✱211·64. \(\vdash :\lambda \subset \text{D}ʻP_{\in }.\supset .sʻ\lambda \in \text{D}ʻP_{\in }\) -/
theorem pm211_64 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    L ⊆ dom (imgRel P) → sumCls L ∈ dom (imgRel P) := by
  intro hL
  refine ⟨{y | ∃ C, P ʻʻ C ∈ L ∧ y ∈ C}, ?_⟩
  ext x
  constructor
  · rintro ⟨A, hA, hx⟩
    obtain ⟨C, hAC⟩ := hL hA
    have hx' : x ∈ P ʻʻ C := hAC ▸ hx
    obtain ⟨y, hy, hxy⟩ := hx'
    exact ⟨y, ⟨C, hAC ▸ hA, hy⟩, hxy⟩
  · rintro ⟨y, ⟨C, hC, hy⟩, hxy⟩
    exact ⟨_, hC, y, hy, hxy⟩

/-- ✱211·65. \(\vdash :\lambda \subset \text{D}ʻ(P_{\in }\dot{\cap} I).\supset .sʻ\lambda \in \text{D}ʻ(P_{\in }\dot{\cap} I)\) -/
theorem pm211_65 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    L ⊆ dom (imgRel P ⩀ I) → sumCls L ∈ dom (imgRel P ⩀ I) := by
  intro hL
  refine mem_dom_imgRel_rcap_I.2 (Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_))
  · obtain ⟨A, hA, hx⟩ := hx
    have e : A = P ʻʻ A := mem_dom_imgRel_rcap_I.1 (hL hA)
    have hx' : x ∈ P ʻʻ A := e ▸ hx
    obtain ⟨y, hy, hxy⟩ := hx'
    exact ⟨y, ⟨A, hA, hy⟩, hxy⟩
  · obtain ⟨y, ⟨A, hA, hy⟩, hxy⟩ := hx
    have e : A = P ʻʻ A := mem_dom_imgRel_rcap_I.1 (hL hA)
    exact ⟨A, hA, by rw [e]; exact ⟨y, hy, hxy⟩⟩

/-- ✱211·66. \(\vdash :\dot{\exists} !P.\supset .\text{sect}ʻP,\text{D}ʻP_{\in }{\sim}\in 1\) -/
theorem pm211_66 {α : Type u} {P : α → α → Prop} :
    rEx P → sect P ∉ one ∧ dom (imgRel P) ∉ one := by
  rintro ⟨x, y, hxy⟩
  have h0 := pm211_44 (P := P)
  constructor
  · intro h1
    obtain ⟨b, hb⟩ := mem_one_iff.1 h1
    have e1 := (hb _ ).1 h0.2
    have e2 := (hb _).1 pm211_26.1
    have : x ∈ (Λ : Set α) := by rw [e1, ← e2]; exact fld_l hxy
    rw [Null_eq_empty] at this
    exact Set.notMem_empty x this
  · intro h1
    obtain ⟨b, hb⟩ := mem_one_iff.1 h1
    have e1 := (hb _ ).1 h0.1.2
    have e2 := (hb _).1 (pm211_301 (P := P))
    have : x ∈ (Λ : Set α) := by rw [e1, ← e2]; exact ⟨y, hxy⟩
    rw [Null_eq_empty] at this
    exact Set.notMem_empty x this

/-- ✱211·661. \(\vdash :P\in \text{trans}.\exists !\text{Cl ex}ʻCʻP-\text{ᗡ}ʻ\text{max}_{P}.\supset .\text{D}ʻ(P_{\in }\dot{\cap} I){\sim}\in 1\) -/
theorem pm211_661 {α : Type u} {P : α → α → Prop} :
    P ∈ transR ∧ (clEx (fld P) \ codom (maxP P)).Nonempty → dom (imgRel P ⩀ I) ∉ one := by
  rintro ⟨ht, G, ⟨hGf, x, hxG⟩, hGm⟩
  have hGA : G ⊆ P ʻʻ G := by
    intro z hz
    by_contra hz'
    exact hGm ⟨z, maxP_iff.2 ⟨⟨hz, hGf hz⟩, fun y hy hzy => hz' ⟨y, hy, hzy⟩⟩⟩
  have hA : P ʻʻ G ∈ dom (imgRel P ⩀ I) := by
    refine mem_dom_imgRel_rcap_I.2 (pm211_411 ⟨⟨ht, rfl⟩, fun z hz => ?_⟩)
    obtain ⟨y, hy, hzy⟩ := hz
    exact ⟨y, hGA hy, hzy⟩
  intro h1
  obtain ⟨b, hb⟩ := mem_one_iff.1 h1
  have e1 := (hb _).1 pm211_44.1.1
  have e2 := (hb _).1 hA
  have : x ∈ (Λ : Set α) := by rw [e1, ← e2]; exact hGA hxG
  rw [Null_eq_empty] at this
  exact Set.notMem_empty x this

/-- ✱211·67. \[\begin{align}&\vdash :P\in \text{connex} .\kappa =\text{sect}ʻP.Q=P_{\text{lc}}\unicode{x0294f}\kappa .\supset .\text{Hp}*210·12\\ &[*211·6.*210·13]\end{align}\] -/
theorem pm211_67 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    (P ∈ connex ∧ K = sect P) ∧ Q = Plc P ⥏ K → ((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) := by
  rintro ⟨⟨hc, rfl⟩, rfl⟩
  have hn : ∀ C D, C ∈ sect P ∧ D ∈ sect P → C ⊆ D ∨ D ⊆ C := fun C D h => pm211_6 ⟨hc, h⟩
  exact ⟨hn, (pm210_13 ⟨⟨hn, rfl⟩, fun A hA => hA.1⟩).symm⟩

/-- ✱211·671. \[\begin{align}\vdash : P \in \text{connex} . \kappa = &\text{sect}ʻP . Q = P_{\text{lc}} \unicode{x0294f} \kappa . \dot{\exists} ! P . \supset .\\ &\text{Hp} *210·251 . \text{Hp} *210·252 \quad[*211·67·66·63·633]\end{align}\] -/
theorem pm211_671 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((P ∈ connex ∧ K = sect P) ∧ Q = Plc P ⥏ K) ∧ rEx P → ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → sumCls M ∈ K) ∧ ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → prodCls M ∩ sumCls K ∈ K) := by
  rintro ⟨h, hP⟩
  have h12 := pm211_67 h
  obtain ⟨⟨-, rfl⟩, -⟩ := h
  have h1 : sect P ∉ one := (pm211_66 hP).1
  exact ⟨⟨⟨h12, h1⟩, fun M hM => pm211_63 hM⟩, ⟨⟨h12, h1⟩, fun M hM => pm211_633 hM⟩⟩

/-- ✱211·68. \[\begin{align}&\vdash : P \in \text{trans} \cap \text{connex} . \kappa = \text{D}ʻP_{\in } . Q = P_{\text{lc}} \unicode{x0294f} \kappa . \supset . \text{Hp} *210·12\\ &[*211·61 . *210·13]\end{align}\] -/
theorem pm211_68 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    (P ∈ transR ∩ connex ∧ K = dom (imgRel P)) ∧ Q = Plc P ⥏ K → ((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) := by
  rintro ⟨⟨hP, rfl⟩, rfl⟩
  have hn : ∀ C D, C ∈ dom (imgRel P) ∧ D ∈ dom (imgRel P) → C ⊆ D ∨ D ⊆ C :=
    fun C D h => pm211_61 ⟨hP, h⟩
  exact ⟨hn, (pm210_13 ⟨⟨hn, rfl⟩, fun A hA => (sect_of_seg hP.1 hA).1⟩).symm⟩

/-- ✱211·681. \[\begin{align}&\vdash : P \in \text{trans} \cap \text{connex} . \kappa = \text{D}ʻP_{\in } . Q = P_{\text{lc}} \unicode{x0294f} \kappa . \dot{\exists} ! P . \supset . \text{Hp} *210·251\\ &[*211·68·66·64]\end{align}\] -/
theorem pm211_681 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((P ∈ transR ∩ connex ∧ K = dom (imgRel P)) ∧ Q = Plc P ⥏ K) ∧ rEx P → ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → sumCls M ∈ K) := by
  rintro ⟨h, hP⟩
  have h12 := pm211_68 h
  obtain ⟨⟨-, rfl⟩, -⟩ := h
  exact ⟨⟨h12, (pm211_66 hP).2⟩, fun M hM => pm211_64 hM⟩

/-- ✱211·69. \[\begin{align}&\vdash : P \in \text{connex} . \kappa = \text{D}ʻ(P_{\in } \dot{\cap} I) . Q = P_{\text{lc}} \unicode{x0294f} \kappa . \supset . \text{Hp} *210·12\\ &[*211·62 . *210·13]\end{align}\] -/
theorem pm211_69 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    (P ∈ connex ∧ K = dom (imgRel P ⩀ I)) ∧ Q = Plc P ⥏ K → ((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) := by
  rintro ⟨⟨hc, rfl⟩, rfl⟩
  have hn : ∀ C D, C ∈ dom (imgRel P ⩀ I) ∧ D ∈ dom (imgRel P ⩀ I) → C ⊆ D ∨ D ⊆ C :=
    fun C D h => pm211_62 ⟨hc, h⟩
  exact ⟨hn, (pm210_13 ⟨⟨hn, rfl⟩, fun A hA => (pm211_14.2 hA).1⟩).symm⟩

/-- ✱211·691. \[\begin{align}\vdash : P \in \text{connex} . \kappa = \text{D}ʻ(P_{\in } \dot{\cap} I) . Q = P_{\text{lc}} &\unicode{x0294f} \kappa . \text{D}ʻ(P_{\in } \dot{\cap} I) {\sim} \in 1 . \supset .\\ &\text{Hp} *210·251 \quad[*211·69·65]\end{align}\] -/
theorem pm211_691 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((P ∈ connex ∧ K = dom (imgRel P ⩀ I)) ∧ Q = Plc P ⥏ K) ∧ dom (imgRel P ⩀ I) ∉ one →
      ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → sumCls M ∈ K) := by
  rintro ⟨h, h1⟩
  have h12 := pm211_69 h
  obtain ⟨⟨-, rfl⟩, -⟩ := h
  exact ⟨⟨h12, h1⟩, fun M hM => pm211_65 hM⟩

/-- ✱211·692. \[\begin{align}\vdash : P \in &\text{trans} \cap \text{connex} . \kappa = \text{D}ʻ(P_{\in } \dot{\cap} I) . Q = P_{\text{lc}} \unicode{x0294f} \kappa .\\ &\exists ! \text{Cl ex}ʻCʻP - \text{ᗡ}ʻ\text{max}_{P} . \supset . \text{Hp} *210·251 \quad[*211·691·661]\end{align}\] -/
theorem pm211_692 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} {Q : Set α → Set α → Prop} :
    ((P ∈ transR ∩ connex ∧ K = dom (imgRel P ⩀ I)) ∧ Q = Plc P ⥏ K) ∧
      (clEx (fld P) \ codom (maxP P)).Nonempty → ((((∀ C D, C ∈ K ∧ D ∈ K → C ⊆ D ∨ D ⊆ C) ∧ Q = (fun C D => ((C ∈ K ∧ D ∈ K) ∧ C ⊆ D) ∧ C ≠ D)) ∧ K ∉ one) ∧ ∀ M, M ⊆ K → sumCls M ∈ K) := by
  rintro ⟨⟨⟨⟨ht, hc⟩, hK⟩, hQ⟩, hE⟩
  exact pm211_691 ⟨⟨⟨hc, hK⟩, hQ⟩, pm211_661 ⟨ht, hE⟩⟩

/-! ### Helper lemmas for ✱211·7–·9: complements of sections -/

section H211b

variable {α : Type u} {P : α → α → Prop}

private theorem compl_compl' {F A : Set α} (hA : A ⊆ F) : F \ (F \ A) = A := by
  ext x
  constructor
  · rintro ⟨hx, hx'⟩
    by_contra h
    exact hx' ⟨hx, h⟩
  · intro hx
    exact ⟨hA hx, fun h => h.2 hx⟩

private theorem cnv_trans (h : P ∈ transR) : P˘ ∈ transR :=
  mem_transR.2 fun a b c ⟨h1, h2⟩ => mem_transR.1 h c b a ⟨h2, h1⟩

private theorem cnv_connex (h : P ∈ connex) : P˘ ∈ connex := by
  refine mem_connex.2 fun x y hxy => ?_
  rcases mem_connex.1 h x y (by simpa only [fld_cnv] using hxy) with
    (h1 | h1) | h1
  · exact Or.inr h1
  · exact Or.inl (Or.inr h1)
  · exact Or.inl (Or.inl h1)

private theorem cnv_rlJ (h : P ∈ rl J) : P˘ ∈ rl J := mem_rl_J.2 fun a h' => mem_rl_J.1 h a h'

private theorem cnv_ser (h : P ∈ Ser) : P˘ ∈ Ser :=
  ⟨⟨cnv_rlJ h.1.1, cnv_trans h.1.2⟩, cnv_connex h.2⟩

private theorem eq_refs_of_min (hc : P ∈ connex) {A : Set α} (hA : A ∈ sect P) {n : α}
    (hn : minP P n (fld P \ A)) : A = refs P n := by
  obtain ⟨⟨⟨hnf, hnA⟩, -⟩, hn'⟩ := minP_iff.1 hn
  ext x
  constructor
  · intro hx
    exact follow_of_sect hc hA hnf hnA hx
  · intro hxn
    by_contra hxA
    exact hn' x ⟨fld_l hxn, hxA⟩ hxn

private theorem seq_min (hc : P ∈ connex) {A : Set α} (hA : A ∈ sect P) {s : α}
    (hs : seqP P s A) : minP P s (fld P \ A) := by
  have hsf := (seqP_iff.1 hs).1.2
  exact minP_iff.2 ⟨⟨⟨hsf, seq_not_mem hs hA.1⟩, hsf⟩,
    fun y hy hys => hy.2 (pred_seq_mem hc hA hs hys)⟩

private theorem prec_max (hc : P ∈ connex) {A : Set α} (hA : A ∈ sect P) {p : α}
    (hp : precP P p (fld P \ A)) : maxP P p A := by
  obtain ⟨⟨h1, hpf⟩, h3⟩ := precP_iff.1 hp
  have hpA : p ∈ A := by
    by_contra hpA
    exact h3 p h1 (h1 p ⟨⟨hpf, hpA⟩, hpf⟩)
  refine maxP_iff.2 ⟨⟨hpA, hpf⟩, fun y hy hpy => h3 y (fun z hz => ?_) hpy⟩
  exact follow_of_sect hc hA hz.1.1 hz.1.2 hy

private theorem max_prec_of_seq (hc : P ∈ connex) {A : Set α} (hA : A ∈ sect P) {s m : α}
    (hs : seqP P s A) (hm : maxP P m A) : precP P m (fld P \ A) := by
  obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
  refine precP_iff.2 ⟨⟨fun y hy => follow_of_sect hc hA hy.1.1 hy.1.2 hmA, hmf⟩,
    fun z hz hmz => ?_⟩
  have hzA : z ∉ A := fun h => hm' z h hmz
  have hzf : z ∈ fld P := fld_r hmz
  have hsβ : s ∈ fld P \ A := ⟨(seqP_iff.1 hs).1.2, seq_not_mem hs hA.1⟩
  exact (seqP_iff.1 hs).2 z (fun y hy => follow_of_sect hc hA hzf hzA hy.1) (hz s ⟨hsβ, hsβ.1⟩)

private theorem max_prec_of_J (hc : P ∈ connex) (hJ : P ∈ rl J) {A : Set α} (hA : A ∈ sect P)
    {m : α} (hm : maxP P m A) : precP P m (fld P \ A) := by
  obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
  refine precP_iff.2 ⟨⟨fun y hy => follow_of_sect hc hA hy.1.1 hy.1.2 hmA, hmf⟩,
    fun z hz hmz => ?_⟩
  have hzA : z ∉ A := fun h => hm' z h hmz
  exact mem_rl_J.1 hJ z (hz z ⟨⟨fld_r hmz, hzA⟩, fld_r hmz⟩)

private theorem min_seq_of_J (hc : P ∈ connex) (hJ : P ∈ rl J) {A : Set α} (hA : A ∈ sect P)
    {n : α} (hn : minP P n (fld P \ A)) : seqP P n A := by
  obtain ⟨⟨⟨hnf, hnA⟩, -⟩, hn'⟩ := minP_iff.1 hn
  refine seqP_iff.2 ⟨⟨fun y hy => follow_of_sect hc hA hnf hnA hy.1, hnf⟩, fun z hz hzn => ?_⟩
  by_cases hzA : z ∈ A
  · exact mem_rl_J.1 hJ z (hz z ⟨hzA, hA.1 hzA⟩)
  · exact hn' z ⟨fld_l hzn, hzA⟩ hzn

/-- The form of ✱211·726 used throughout: for `P ∈ connex ∩ Rl'J` and a section `α`,
`max⃗_P'α = prec⃗_P'(C'P − α)` and `seq⃗_P'α = min⃗_P'(C'P − α)`. -/
private theorem compl_eqs (hc : P ∈ connex) (hJ : P ∈ rl J) {A : Set α} (hA : A ∈ sect P) :
    refs (maxP P) A = refs (precP P) (fld P \ A) ∧
      refs (seqP P) A = refs (minP P) (fld P \ A) :=
  ⟨Set.Subset.antisymm (fun _ hm => max_prec_of_J hc hJ hA hm) (fun _ hp => prec_max hc hA hp),
    Set.Subset.antisymm (fun _ hs => seq_min hc hA hs) (fun _ hn => min_seq_of_J hc hJ hA hn)⟩

private theorem prec_unique (hc : P ∈ connex) {B : Set α} {p q : α} (hp : precP P p B)
    (hq : precP P q B) : p = q := by
  obtain ⟨⟨hp1, hpf⟩, hp3⟩ := precP_iff.1 hp
  obtain ⟨⟨hq1, hqf⟩, hq3⟩ := precP_iff.1 hq
  rcases mem_connex.1 hc p q ⟨hpf, hqf⟩ with (h | h) | h
  · exact absurd h (hp3 q hq1)
  · exact h
  · exact absurd h (hq3 p hp1)

private theorem compl_eq_img_of_nomin {A : Set α} (hA : A ∈ sect P)
    (hn : ¬∃ n, minP P n (fld P \ A)) : fld P \ A = P˘ ʻʻ (fld P \ A) := by
  ext z
  constructor
  · intro hz
    by_contra hz'
    exact hn ⟨z, minP_iff.2 ⟨⟨hz, hz.1⟩, fun y hy hyz => hz' ⟨y, hy, hyz⟩⟩⟩
  · rintro ⟨y, ⟨hyf, hyA⟩, hzy⟩
    have hyz : P y z := hzy
    exact ⟨fld_r hyz, fun hzA => hyA (sect_closed hA hyz hzA)⟩

private theorem edesc_iff_refs {γ : Type v} {R : α → γ → Prop} {y : γ} :
    EDesc R y ↔ ∃ b, refs R y = ι b :=
  ⟨fun ⟨b, h⟩ => ⟨b, Set.ext h⟩, fun ⟨b, h⟩ => ⟨b, fun x => Set.ext_iff.1 h x⟩⟩

private theorem limax_refs_max {A : Set α} (hm : ∃ m, maxP P m A) :
    refs (limaxP P) A = refs (maxP P) A := by
  ext x
  show limaxP P x A ↔ maxP P x A
  rw [limaxP_iff]
  exact ⟨fun h => h.elim id (fun h => absurd hm h.2), Or.inl⟩

private theorem limax_refs_nomax {A : Set α} (hm : ¬∃ m, maxP P m A) :
    refs (limaxP P) A = refs (seqP P) A := by
  ext x
  show limaxP P x A ↔ seqP P x A
  rw [limaxP_iff]
  exact ⟨fun h => h.elim (fun h => absurd ⟨x, h⟩ hm) (fun h => h.1), fun h => Or.inr ⟨h, hm⟩⟩

private theorem limin_refs_min {B : Set α} (hn : ∃ n, minP P n B) :
    refs (liminP P) B = refs (minP P) B := by
  ext x
  show liminP P x B ↔ minP P x B
  rw [liminP_iff]
  exact ⟨fun h => h.elim id (fun h => absurd hn h.2), Or.inl⟩

private theorem limin_refs_nomin {B : Set α} (hn : ¬∃ n, minP P n B) :
    refs (liminP P) B = refs (precP P) B := by
  ext x
  show liminP P x B ↔ precP P x B
  rw [liminP_iff]
  exact ⟨fun h => h.elim (fun h => absurd ⟨x, h⟩ hn) (fun h => h.1), fun h => Or.inr ⟨h, hn⟩⟩

private theorem limax_limin_eq (hc : P ∈ connex) (hJ : P ∈ rl J) {A : Set α} (hA : A ∈ sect P)
    (h : (¬∃ m, maxP P m A) ∨ ¬∃ n, minP P n (fld P \ A)) :
    refs (limaxP P) A = refs (liminP P) (fld P \ A) := by
  obtain ⟨e1, e2⟩ := compl_eqs hc hJ hA
  by_cases hm : ∃ m, maxP P m A
  · have hn : ¬∃ n, minP P n (fld P \ A) := h.resolve_left (not_not.2 hm)
    rw [limax_refs_max hm, limin_refs_nomin hn, e1]
  · rw [limax_refs_nomax hm, e2]
    by_cases hn : ∃ n, minP P n (fld P \ A)
    · rw [limin_refs_min hn]
    · rw [limin_refs_nomin hn, ← e1]
      have h1 : refs (minP P) (fld P \ A) = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun x hx => hn ⟨x, hx⟩
      have h2 : refs (maxP P) A = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => hm ⟨x, hx⟩
      rw [h1, h2]

private theorem sect_addLast {Q : α → α → Prop} {x : α} : fld Q ∈ sect (Q ⇸ x) := by
  refine ⟨fun y hy => ⟨x, Or.inl (Or.inr ⟨hy, rfl⟩)⟩, ?_⟩
  rintro y ⟨z, -, h | ⟨hy, -⟩⟩
  · exact fld_l h
  · exact hy

private theorem fres_fld_eq {Q : α → α → Prop} {S : Set α} (hQ : Q = P ⥏ S) :
    Q = P ⥏ fld Q := by
  funext x y
  apply propext
  constructor
  · intro h
    have h' : (P ⥏ S) x y := hQ ▸ h
    exact ⟨⟨fld_l h, h'.1.2⟩, fld_r h⟩
  · intro h
    have hx : x ∈ S := fld_fres_sub S (hQ ▸ h.1.1)
    have hy : y ∈ S := fld_fres_sub S (hQ ▸ h.2)
    rw [hQ]
    exact ⟨⟨hx, h.1.2⟩, hy⟩

private theorem fld_not_one_of_irr {Q : α → α → Prop} {S : Set α} (irr : ∀ x, ¬ P x x)
    (hQ : Q = P ⥏ S) : fld Q ∉ one := by
  intro h1
  obtain ⟨b, hb⟩ := mem_one_iff.1 h1
  obtain ⟨y, hy | hy⟩ := (hb b).2 rfl
  · have e := (hb y).1 (fld_r hy)
    rw [e, hQ] at hy
    exact irr b hy.1.2
  · have e := (hb y).1 (fld_l hy)
    rw [e, hQ] at hy
    exact irr b hy.1.2

end H211b

/-- ✱211·7. \(\vdash : \alpha \in \text{sect}ʻP . \supset . CʻP - \alpha \in \text{sect}ʻ\breve{P}\) -/
theorem pm211_7 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∈ sect P → fld P \ A ∈ sect P˘ := by
  intro h
  refine ⟨fun x hx => by rw [fld_cnv]; exact hx.1, ?_⟩
  rintro x ⟨y, ⟨hyf, hyA⟩, hxy⟩
  have hxy' : P y x := hxy
  exact ⟨fld_r hxy', fun hxA => hyA (sect_closed h hxy' hxA)⟩

/-- ✱211·701. \(\vdash : \alpha \in \text{sect}ʻP . \text{E}! \text{max}_{P}ʻ\alpha . \supset . pʻ\overleftarrow{P}ʻʻ\alpha \subset \overleftarrow{P}ʻ\text{max}_{P}ʻ\alpha \subset CʻP - \alpha\) -/
theorem pm211_701 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∈ sect P ∧ EDesc (maxP P) A →
      Desc (maxP P) A (fun m => prodCls (Rbwd P ʻʻ A) ⊆ rels P m ∧ rels P m ⊆ fld P \ A) := by
  rintro ⟨hA, hE⟩
  obtain ⟨m, hm⟩ := hE
  have hm0 := (hm m).2 rfl
  obtain ⟨⟨hmA, -⟩, hm'⟩ := maxP_iff.1 hm0
  refine ⟨m, hm, fun z hz => ?_, fun z hz => ⟨fld_r (show P m z from hz), fun hzA => hm' z hzA hz⟩⟩
  exact (mem_prodCls_Rbwd.1 hz) m hmA

/-- ✱211·702. \(\vdash : P \in \text{connex} . \alpha \in \text{sect}ʻP . \supset . CʻP - \alpha \subset pʻ\overleftarrow{P}ʻʻ\alpha \quad[*202·501 . *211·1]\) -/
theorem pm211_702 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P → fld P \ A ⊆ prodCls (Rbwd P ʻʻ A) := by
  rintro ⟨hc, hA⟩ z ⟨hzf, hzA⟩
  exact mem_prodCls_Rbwd.2 fun y hy => follow_of_sect hc hA hzf hzA hy

/-- ✱211·703. \[\begin{align}&\vdash : P \in \text{connex} . \alpha \in \text{sect}ʻP - {℩}ʻCʻP . \supset . \exists ! pʻ\overleftarrow{P}ʻʻ\alpha \\ &[*211·702·1 . *24·58]\end{align}\] -/
theorem pm211_703 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P \ ι (fld P) → (prodCls (Rbwd P ʻʻ A)).Nonempty := by
  rintro ⟨hc, hA, hne⟩
  have : ¬ fld P ⊆ A := fun h => hne (Set.Subset.antisymm hA.1 h)
  obtain ⟨z, hzf, hzA⟩ := Set.not_subset.1 this
  exact ⟨z, pm211_702 ⟨hc, hA⟩ ⟨hzf, hzA⟩⟩

/-- ✱211·71. \[\begin{align}\vdash : P \in \text{connex} . \alpha \in \text{sect}ʻP . \text{E}! &\text{max}_{P}ʻ\alpha . \supset .\\ &pʻ\overleftarrow{P}ʻʻ\alpha = \overleftarrow{P}ʻ\text{max}_{P}ʻ\alpha = CʻP - \alpha\end{align}\] -/
theorem pm211_71 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ connex ∧ A ∈ sect P) ∧ EDesc (maxP P) A →
      Desc (maxP P) A (fun m => prodCls (Rbwd P ʻʻ A) = rels P m ∧ rels P m = fld P \ A) := by
  rintro ⟨⟨hc, hA⟩, hE⟩
  obtain ⟨m, hm⟩ := hE
  have hm0 := (hm m).2 rfl
  obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm0
  have e2 : rels P m = fld P \ A := by
    ext z
    constructor
    · intro hz
      exact ⟨fld_r (show P m z from hz), fun hzA => hm' z hzA hz⟩
    · rintro ⟨hzf, hzA⟩
      exact follow_of_sect hc hA hzf hzA hmA
  refine ⟨m, hm, Set.Subset.antisymm (fun z hz => (mem_prodCls_Rbwd.1 hz) m hmA) ?_, e2⟩
  rw [e2]
  exact pm211_702 ⟨hc, hA⟩

/-- ✱211·711. \[\begin{align}\vdash : P &\in \text{connex} . P^{2} \,\unicode{x2abd}\, J . \alpha \in \text{sect}ʻP . \supset .\\ &\alpha = CʻP - pʻ\overleftarrow{P}ʻʻ\alpha . CʻP \cap pʻ\overleftarrow{P}ʻʻ\alpha = CʻP - \alpha \quad[*202·503 . *211·2]\end{align}\] -/
theorem pm211_711 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ connex ∧ rsq P ⪽ J) ∧ A ∈ sect P →
      A = fld P \ prodCls (Rbwd P ʻʻ A) ∧ fld P ∩ prodCls (Rbwd P ʻʻ A) = fld P \ A := by
  rintro ⟨⟨hc, hJ⟩, hA⟩
  have irr : ∀ x, ¬ P x x := fun x h => hJ x x ⟨x, h, h⟩ rfl
  have hdis : ∀ z, z ∈ A → z ∉ prodCls (Rbwd P ʻʻ A) :=
    fun z hz h => irr z ((mem_prodCls_Rbwd.1 h) z hz)
  constructor
  · ext z
    constructor
    · intro hz
      exact ⟨hA.1 hz, hdis z hz⟩
    · rintro ⟨hzf, hzp⟩
      by_contra hzA
      exact hzp (pm211_702 ⟨hc, hA⟩ ⟨hzf, hzA⟩)
  · ext z
    constructor
    · rintro ⟨hzf, hzp⟩
      exact ⟨hzf, fun hzA => hdis z hzA hzp⟩
    · rintro ⟨hzf, hzA⟩
      exact ⟨hzf, pm211_702 ⟨hc, hA⟩ ⟨hzf, hzA⟩⟩

/-- ✱211·712. \(\vdash : P \in \text{connex} . \alpha \in \text{sect}ʻP . \text{E}! \text{min}_{P}ʻ(CʻP - \alpha ) . \supset . \alpha = \overrightarrow{P}ʻ\text{min}_{P}ʻ(CʻP - \alpha )\) -/
theorem pm211_712 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ connex ∧ A ∈ sect P) ∧ EDesc (minP P) (fld P \ A) →
      Desc (minP P) (fld P \ A) (fun m => A = refs P m) := by
  rintro ⟨⟨hc, hA⟩, hE⟩
  obtain ⟨m, hm⟩ := hE
  have hm0 := (hm m).2 rfl
  exact ⟨m, hm, (eq_refs_of_min hc hA hm0)⟩

/-- ✱211·713. \(\vdash : P \in \text{connex} . \alpha \in \text{sect}ʻP - \text{D}ʻP_{\in } . \supset . \text{E}! \text{max}_{P}ʻ\alpha . {\sim} \text{E}! \text{min}_{P}ʻ(CʻP - \alpha )\) -/
theorem pm211_713 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P \ dom (imgRel P) →
      EDesc (maxP P) A ∧ ¬ EDesc (minP P) (fld P \ A) := by
  rintro ⟨hc, hA, hD⟩
  have hm : ∃ m, maxP P m A := by
    by_contra hm
    exact hD (seg_of_sect hc hA (Or.inr hm))
  refine ⟨(edesc_iff_ex (fun a b ha hb => max_unique hc ha hb)).2 hm, fun hE => hD ?_⟩
  obtain ⟨n, hn⟩ := exists_of_edesc hE
  rw [eq_refs_of_min hc hA hn]
  exact pm211_3 ⟨n, (minP_iff.1 hn).1.2, rfl⟩

/-- ✱211·714. \(\vdash :P\in \text{connex} .\alpha \in \text{sect}ʻP.\supset .\overrightarrow{\text{seq}} _{P}ʻ\alpha \subset \overrightarrow{\text{min}}_{P}ʻ(CʻP-\alpha )\) -/
theorem pm211_714 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P → refs (seqP P) A ⊆ refs (minP P) (fld P \ A) :=
  fun ⟨hc, hA⟩ _ hs => seq_min hc hA hs

/-- ✱211·715. \(\vdash :P\in \text{connex} \cap \text{Rl}ʻJ.\alpha \in \text{sect}ʻP.\supset .\overrightarrow{\text{seq}} _{P}ʻ\alpha =\overrightarrow{\text{min}}_{P}ʻ(CʻP-\alpha )\) -/
theorem pm211_715 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∩ rl J ∧ A ∈ sect P → refs (seqP P) A = refs (minP P) (fld P \ A) := by
  rintro ⟨⟨hc, hJ⟩, hA⟩
  exact (compl_eqs hc hJ hA).2

/-- ✱211·72. \[\begin{align}\vdash :&P\in \text{connex} .\alpha \in \text{sect}ʻP-\text{D}ʻP_{\in }.\supset .\\ &CʻP-\alpha =\breve{P} ʻʻ(CʻP-\alpha ).CʻP-\alpha \in \text{D}ʻ\{(\breve{P} )_{\in }\dot{\cap} I\} \quad[*211·21·7·713]\end{align}\] -/
theorem pm211_72 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P \ dom (imgRel P) →
      fld P \ A = P˘ ʻʻ (fld P \ A) ∧ fld P \ A ∈ dom (imgRel P˘ ⩀ I) := by
  rintro ⟨hc, hA, hD⟩
  have hn : ¬∃ n, minP P n (fld P \ A) := by
    rintro ⟨n, hn⟩
    apply hD
    rw [eq_refs_of_min hc hA hn]
    exact pm211_3 ⟨n, (minP_iff.1 hn).1.2, rfl⟩
  have e := compl_eq_img_of_nomin hA hn
  exact ⟨e, mem_dom_imgRel_rcap_I.2 e⟩

/-- ✱211·721. \[\begin{align}\vdash :P\in \text{connex} .\alpha \in \text{sect}ʻP\cap (\text{ᗡ}ʻ\text{max}_{P}&\cup \text{ᗡ}ʻ\text{seq}_{P}).\supset .\\ &\overrightarrow{\text{seq}} _{P}ʻ\alpha =\overrightarrow{\text{min}}_{P}ʻ(CʻP-\alpha )\end{align}\] -/
theorem pm211_721 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P ∩ (codom (maxP P) ∪ codom (seqP P)) →
      refs (seqP P) A = refs (minP P) (fld P \ A) := by
  rintro ⟨hc, hA, h⟩
  refine Set.Subset.antisymm (fun s hs => seq_min hc hA hs) (fun n hn => ?_)
  rcases h with ⟨x, hx⟩ | ⟨s, hs⟩
  · obtain ⟨⟨hxA, hxf⟩, hx'⟩ := maxP_iff.1 hx
    obtain ⟨⟨⟨hnf, hnA⟩, -⟩, hn'⟩ := minP_iff.1 hn
    show seqP P n A
    refine seqP_iff.2 ⟨⟨fun y hy => follow_of_sect hc hA hnf hnA hy.1, hnf⟩, fun z hz hzn => ?_⟩
    have hxz : P x z := hz x ⟨hxA, hxf⟩
    have hzA : z ∉ A := fun h => hx' z h hxz
    exact hn' z ⟨fld_l hzn, hzA⟩ hzn
  · have e := min_unique hc hn (seq_min hc hA hs)
    show seqP P n A
    rw [e]
    exact hs

/-- ✱211·722. \[\begin{align}\vdash :P\in \text{connex} .\alpha \in \text{sect}ʻP.\text{E}!\text{max}_{P}ʻ\alpha .\text{E}!&\text{seq}_{P}ʻ\alpha .\supset .\\ &\text{max}_{P}ʻ\alpha =\text{prec}_{P}ʻ(CʻP-\alpha )\end{align}\] -/
theorem pm211_722 {α : Type u} {P : α → α → Prop} {A : Set α} :
    ((P ∈ connex ∧ A ∈ sect P) ∧ EDesc (maxP P) A) ∧ EDesc (seqP P) A →
      Desc (maxP P) A (fun m => Desc (precP P) (fld P \ A) (fun p => m = p)) := by
  rintro ⟨⟨⟨hc, hA⟩, hM⟩, hS⟩
  obtain ⟨m, hm⟩ := exists_of_edesc hM
  obtain ⟨s, hs⟩ := exists_of_edesc hS
  have hp := max_prec_of_seq hc hA hs hm
  exact desc_of (uniq_of (fun n hn => max_unique hc hn hm) hm)
    (desc_of (uniq_of (fun q hq => prec_unique hc hq hp) hp) rfl)

/-- ✱211·723. \(\vdash :P\in \text{connex} .\alpha \in \text{sect}ʻP.\supset .\overrightarrow{\text{prec}} _{P}ʻ(CʻP-\alpha )\subset \overrightarrow{\text{max}}_{P}ʻ\alpha\) -/
theorem pm211_723 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P → refs (precP P) (fld P \ A) ⊆ refs (maxP P) A :=
  fun ⟨hc, hA⟩ _ hp => prec_max hc hA hp

/-- ✱211·724. \[\begin{align}\vdash :P\in \text{connex} .\alpha \in \text{sect}ʻP\cap (\text{ᗡ}ʻ\text{seq}_{P}\cup -\text{ᗡ}ʻ&\text{max}_{P}).\supset .\\ &\overrightarrow{\text{max}}_{P}ʻ\alpha =\overrightarrow{\text{prec}} _{P}ʻ(CʻP-\alpha )\end{align}\] -/
theorem pm211_724 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P ∩ (codom (seqP P) ∪ (codom (maxP P))ᶜ) →
      refs (maxP P) A = refs (precP P) (fld P \ A) := by
  rintro ⟨hc, hA, h⟩
  refine Set.Subset.antisymm (fun m hm => ?_) (fun p hp => prec_max hc hA hp)
  rcases h with ⟨s, hs⟩ | h
  · exact max_prec_of_seq hc hA hs hm
  · exact absurd ⟨m, hm⟩ h

/-- ✱211·725. \[\begin{align}&\vdash :P\in \text{connex} .\alpha \in \text{sect}ʻP\cap \text{ᗡ}ʻ\text{seq}_{P}.\supset .\\ &\overrightarrow{\text{max}}_{P}ʻ\alpha =\overrightarrow{\text{prec}} _{P}ʻ(CʻP-\alpha ).\overrightarrow{\text{seq}} _{P}ʻ\alpha =\overrightarrow{\text{min}}_{P}ʻ(CʻP-\alpha ) \quad[*211·721·724]\end{align}\] -/
theorem pm211_725 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P ∩ codom (seqP P) →
      refs (maxP P) A = refs (precP P) (fld P \ A) ∧
        refs (seqP P) A = refs (minP P) (fld P \ A) := by
  rintro ⟨hc, hA, hs⟩
  exact ⟨pm211_724 ⟨hc, hA, Or.inl hs⟩, pm211_721 ⟨hc, hA, Or.inr hs⟩⟩

/-- ✱211·726. \[\begin{align}\vdash :P\in \text{connex} \cap \text{Rl}ʻ&J.\alpha \in \text{sect}ʻP.\supset .\\ &\overrightarrow{\text{max}}_{P}ʻ\alpha = \overrightarrow{\text{prec}} _{P}ʻ(CʻP-\alpha ).\overrightarrow{\text{seq}} _{P}ʻ\alpha = \overrightarrow{\text{min}}_{P}ʻ(CʻP-\alpha )\end{align}\] -/
theorem pm211_726 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∩ rl J ∧ A ∈ sect P →
      refs (maxP P) A = refs (precP P) (fld P \ A) ∧
        refs (seqP P) A = refs (minP P) (fld P \ A) := by
  rintro ⟨⟨hc, hJ⟩, hA⟩
  exact compl_eqs hc hJ hA

/-- ✱211·727. \[\begin{align}\vdash \colon\ldotp &P\in \text{connex} \cap \text{Rl}ʻJ.\alpha \in \text{sect}ʻP.\supset :\\ &\text{E}!\text{limax}_Pʻ\alpha . \equiv .\text{E}!\text{limin}_Pʻ(CʻP-\alpha ) \quad[*211·726.*207·44]\end{align}\] -/
theorem pm211_727 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∩ rl J ∧ A ∈ sect P →
      (EDesc (limaxP P) A ↔ EDesc (liminP P) (fld P \ A)) := by
  rintro ⟨⟨hc, hJ⟩, hA⟩
  obtain ⟨e1, e2⟩ := compl_eqs hc hJ hA
  rw [edesc_iff_refs, edesc_iff_refs]
  by_cases hm : ∃ m, maxP P m A
  · by_cases hn : ∃ n, minP P n (fld P \ A)
    · rw [limax_refs_max hm, limin_refs_min hn]
      obtain ⟨m, hm'⟩ := hm
      obtain ⟨n, hn'⟩ := hn
      exact ⟨fun _ => ⟨n, Set.ext (uniq_of (fun b hb => min_unique hc hb hn') hn')⟩,
        fun _ => ⟨m, Set.ext (uniq_of (fun b hb => max_unique hc hb hm') hm')⟩⟩
    · rw [limax_refs_max hm, limin_refs_nomin hn, e1]
  · by_cases hn : ∃ n, minP P n (fld P \ A)
    · rw [limax_refs_nomax hm, limin_refs_min hn, e2]
    · have h1 : refs (minP P) (fld P \ A) = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun x hx => hn ⟨x, hx⟩
      have h2 : refs (maxP P) A = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => hm ⟨x, hx⟩
      rw [limax_refs_nomax hm, limin_refs_nomin hn, e2, ← e1, h1, h2]

/-- ✱211·728. \[\begin{align}\vdash \colon\ldotp P\in \text{connex} &\cap \text{Rl}ʻJ.\alpha \in \text{sect}ʻP:{\sim}\text{E}!\text{max}_{P}ʻ\alpha .\lor.\\ &{\sim}\text{E}!\text{min}_{P}ʻ(CʻP-\alpha ):\supset .\overrightarrow{\text{limax}} _{P}ʻ\alpha = \overrightarrow{\text{limin}} _{P}ʻ(CʻP-\alpha )\end{align}\] -/
theorem pm211_728 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ connex ∩ rl J ∧ A ∈ sect P) ∧ (¬ EDesc (maxP P) A ∨ ¬ EDesc (minP P) (fld P \ A)) →
      refs (limaxP P) A = refs (liminP P) (fld P \ A) := by
  rintro ⟨⟨⟨hc, hJ⟩, hA⟩, h⟩
  rw [edesc_iff_ex (fun a b ha hb => max_unique hc ha hb),
    edesc_iff_ex (fun a b ha hb => min_unique hc ha hb)] at h
  exact limax_limin_eq hc hJ hA h

/-- ✱211·729. \[\begin{align}\vdash :P\in \text{connex} \cap \text{Rl}ʻJ.&\alpha \in \text{sect}ʻP-(\text{ᗡ}ʻ\text{max}_{P}\cap \text{ᗡ}ʻ\text{seq}_{P}).\supset .\\ &\overrightarrow{\text{limax}} _{P}ʻ\alpha = \overrightarrow{\text{limin}} _{P}ʻ(CʻP-\alpha ) \quad[*211·728·726]\end{align}\] -/
theorem pm211_729 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∩ rl J ∧ A ∈ sect P \ (codom (maxP P) ∩ codom (seqP P)) →
      refs (limaxP P) A = refs (liminP P) (fld P \ A) := by
  rintro ⟨⟨hc, hJ⟩, hA, h⟩
  refine limax_limin_eq hc hJ hA ?_
  by_cases hm : ∃ m, maxP P m A
  · refine Or.inr fun ⟨n, hn⟩ => h ⟨hm, ?_⟩
    have : n ∈ refs (seqP P) A := by rw [(compl_eqs hc hJ hA).2]; exact hn
    exact ⟨n, this⟩
  · exact Or.inl hm

/-- ✱211·73. \[\begin{align}\vdash :P\in \text{connex} .&\alpha \in \text{sect}ʻP-\text{D}ʻ(P_{\in }\dot{\cap} I).\supset .\\ &CʻP-\alpha \in \text{D}ʻ\{(\breve{P} )_{\in }\dot{\cap} I\}-\text{ᗡ}ʻ\text{prec}_{P}\cup \{\text{sect}ʻP-\text{D}ʻ(\breve{P} )_{\in }\}\end{align}\]

**Status.** proved (corrected): as printed, with the hypothesis `α ∈ sect'P − D'(P_∈ ∩̇ I)` (a section with a maximum) and `sect'P` in the second alternative, the proposition is false: for the two-term series `P = false ↓ true` on `Bool` and `α = ι'false`, `C'P − α = ι'true` is in neither alternative (`pm211_73_printed_false`). PM's demonstration starts from `α ∈ sect'P − ᗡ'max_P`, i.e. a section without a maximum (`= D'(P_∈ ∩̇ I)`, ✱211·41), and its last step yields `sect'P̆ − D'(P̆)_∈`; with this hypothesis and `sect'P̆` the proposition holds and is proved. -/
theorem pm211_73 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∈ sect P \ codom (maxP P) →
      fld P \ A ∈ (dom (imgRel P˘ ⩀ I) \ codom (precP P)) ∪ (sect P˘ \ dom (imgRel P˘)) := by
  rintro ⟨hc, hA, hm⟩
  by_cases hn : ∃ n, minP P n (fld P \ A)
  · refine Or.inr ⟨pm211_7 hA, ?_⟩
    rintro ⟨C, hC⟩
    obtain ⟨n, hn⟩ := hn
    obtain ⟨⟨hnβ, -⟩, hn'⟩ := minP_iff.1 hn
    have : n ∈ P˘ ʻʻ C := by rw [← hC]; exact hnβ
    obtain ⟨g, hgC, hgn⟩ := this
    have hgn' : P g n := hgn
    have hgA : g ∈ A := by
      by_contra hgA
      exact hn' g ⟨fld_l hgn', hgA⟩ hgn'
    have hz : ∃ z, z ∈ A ∧ P g z := by
      by_contra hz
      push Not at hz
      exact hm ⟨g, maxP_iff.2 ⟨⟨hgA, fld_l hgn'⟩, hz⟩⟩
    obtain ⟨z, hzA, hgz⟩ := hz
    have : z ∈ fld P \ A := by rw [hC]; exact ⟨g, hgC, hgz⟩
    exact this.2 hzA
  · refine Or.inl ⟨mem_dom_imgRel_rcap_I.2 (compl_eq_img_of_nomin hA hn), ?_⟩
    rintro ⟨p, hp⟩
    exact hm ⟨p, prec_max hc hA hp⟩

/-- The printed form of ✱211·73 is false (see its status). -/
theorem pm211_73_printed_false :
    ¬ ∀ (P : Bool → Bool → Prop) (A : Set Bool), P ∈ connex ∧ A ∈ sect P \ dom (imgRel P ⩀ I) →
      fld P \ A ∈ (dom (imgRel P˘ ⩀ I) \ codom (precP P)) ∪ (sect P \ dom (imgRel P˘)) := by
  intro h
  obtain ⟨R, hR⟩ : ∃ R : Bool → Bool → Prop, ∀ x y, R x y ↔ x = false ∧ y = true :=
    ⟨_, fun _ _ => Iff.rfl⟩
  have hf : false ∈ fld R := ⟨true, Or.inl ((hR _ _).2 ⟨rfl, rfl⟩)⟩
  have ht : true ∈ fld R := ⟨false, Or.inr ((hR _ _).2 ⟨rfl, rfl⟩)⟩
  have hc : R ∈ connex := by
    refine mem_connex.2 fun x y _ => ?_
    cases x <;> cases y <;> simp [hR]
  have hA : ({false} : Set Bool) ∈ sect R := by
    refine ⟨fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hf, ?_⟩
    rintro x ⟨y, hy, hxy⟩
    rw [Set.mem_singleton_iff.1 hy] at hxy
    exact absurd ((hR _ _).1 hxy).2 Bool.false_ne_true
  have hD : ({false} : Set Bool) ∉ dom (imgRel R ⩀ I) := by
    intro hD
    have e := mem_dom_imgRel_rcap_I.1 hD
    have : false ∈ R ʻʻ ({false} : Set Bool) := by rw [← e]; exact Set.mem_singleton _
    obtain ⟨y, hy, hxy⟩ := this
    rw [Set.mem_singleton_iff.1 hy] at hxy
    exact absurd ((hR _ _).1 hxy).2 Bool.false_ne_true
  have htβ : true ∈ fld R \ ({false} : Set Bool) := ⟨ht, by simp⟩
  rcases h R {false} ⟨hc, hA, hD⟩ with ⟨h1, -⟩ | ⟨h2, -⟩
  · have e := mem_dom_imgRel_rcap_I.1 h1
    have : true ∈ R˘ ʻʻ (fld R \ ({false} : Set Bool)) := by rw [← e]; exact htβ
    obtain ⟨y, hy, hty⟩ := this
    have hty' : R y true := hty
    rw [((hR _ _).1 hty').1] at hy
    exact hy.2 (Set.mem_singleton _)
  · have := sect_closed h2 ((hR false true).2 ⟨rfl, rfl⟩) htβ
    exact this.2 (Set.mem_singleton _)

/-- ✱211·74. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .\alpha \in \text{D}ʻP_{\in }-&\text{D}ʻ(P_{\in }\dot{\cap} I).\supset .\\ &CʻP-\alpha \in \text{D}ʻ(\breve{P} )_{\in }-\text{D}ʻ\{(\breve{P} )_{\in }\dot{\cap} I\}\end{align}\] -/
theorem pm211_74 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR ∩ connex ∧ A ∈ dom (imgRel P) \ dom (imgRel P ⩀ I) →
      fld P \ A ∈ dom (imgRel P˘) \ dom (imgRel P˘ ⩀ I) := by
  rintro ⟨⟨ht, hc⟩, hA⟩
  have hA' : A ∈ sect P ∩ codom (maxP P) ∩ codom (seqP P) := by
    rw [← pm211_431 ⟨ht, hc⟩]; exact hA
  obtain ⟨⟨hAs, m, hm⟩, s, hs⟩ := hA'
  obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
  constructor
  · refine ⟨ι m, ?_⟩
    ext z
    constructor
    · rintro ⟨hzf, hzA⟩
      exact ⟨m, rfl, follow_of_sect hc hAs hzf hzA hmA⟩
    · rintro ⟨y, hy, hyz⟩
      have hy' : y = m := hy
      have hmz : P m z := hy' ▸ hyz
      exact ⟨fld_r hmz, fun hzA => hm' z hzA hmz⟩
  · intro hI
    have e := mem_dom_imgRel_rcap_I.1 hI
    have hsβ : s ∈ fld P \ A := ⟨(seqP_iff.1 hs).1.2, seq_not_mem hs hAs.1⟩
    have : s ∈ P˘ ʻʻ (fld P \ A) := e ▸ hsβ
    obtain ⟨y, ⟨hyf, hyA⟩, hys⟩ := this
    exact (seqP_iff.1 hs).2 y (fun z hz => follow_of_sect hc hAs hyf hyA hz.1) hys

/-- ✱211·75. \(\vdash \colon\ldotp \alpha \subset CʻP.Q=\breve{P} .\supset :\alpha \in \text{sect}ʻP.\equiv .CʻP-\alpha \in \text{sect}ʻQ \quad[*211·7]\) -/
theorem pm211_75 {α : Type u} {P Q : α → α → Prop} {A : Set α} :
    A ⊆ fld P ∧ Q = P˘ → (A ∈ sect P ↔ fld P \ A ∈ sect Q) := by
  rintro ⟨hA, rfl⟩
  refine ⟨pm211_7, fun h => ?_⟩
  have h2 := pm211_7 h
  rw [fld_cnv, compl_compl' hA] at h2
  exact h2

/-- ✱211·751. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.\alpha &\subset CʻP.Q=\breve{P} .\supset :\\ &\alpha \in \text{D}ʻP_{\in }.\equiv .CʻP-\alpha \in \text{sect}ʻQ\cap (\text{ᗡ}ʻ\text{max}_{Q}\cup -\text{ᗡ}ʻ\text{seq}_{Q})\end{align}\] -/
theorem pm211_751 {α : Type u} {P Q : α → α → Prop} {A : Set α} :
    (P ∈ Ser ∧ A ⊆ fld P) ∧ Q = P˘ →
      (A ∈ dom (imgRel P) ↔ fld P \ A ∈ sect Q ∩ (codom (maxP Q) ∪ (codom (seqP Q))ᶜ)) := by
  rintro ⟨⟨hS, hAf⟩, rfl⟩
  have hc := hS.2
  have hJ := hS.1.1
  rw [← precP_eq_seqP_cnv]
  show _ ↔ fld P \ A ∈ sect P˘ ∩ (codom (minP P) ∪ (codom (precP P))ᶜ)
  rw [pm211_32 ⟨hS.1.2, hc⟩]
  constructor
  · rintro ⟨hA, h⟩
    obtain ⟨e1, e2⟩ := compl_eqs hc hJ hA
    refine ⟨pm211_7 hA, ?_⟩
    rcases h with ⟨s, hs⟩ | h
    · have hs' : s ∈ refs (minP P) (fld P \ A) := by rw [← e2]; exact hs
      exact Or.inl ⟨s, hs'⟩
    · refine Or.inr fun hp => ?_
      obtain ⟨p, hp⟩ := hp
      have hp' : p ∈ refs (maxP P) A := by rw [e1]; exact hp
      exact h ⟨p, hp'⟩
  · rintro ⟨hβ, h⟩
    have hA : A ∈ sect P := (pm211_75 ⟨hAf, rfl⟩).2 hβ
    obtain ⟨e1, e2⟩ := compl_eqs hc hJ hA
    refine ⟨hA, ?_⟩
    rcases h with ⟨n, hn⟩ | h
    · have hn' : n ∈ refs (seqP P) A := by rw [e2]; exact hn
      exact Or.inl ⟨n, hn'⟩
    · refine Or.inr fun hm => ?_
      obtain ⟨m, hm⟩ := hm
      have hm' : m ∈ refs (precP P) (fld P \ A) := by rw [← e1]; exact hm
      exact h ⟨m, hm'⟩

/-- ✱211·752. \[\begin{align}\vdash \colon\ldotp P\in \text{connex} .\alpha \subset &CʻP.Q=\breve{P} .\supset :\\ &\alpha \in \text{D}ʻ(P_{\in }\dot{\cap} I).\supset .CʻP-\alpha \in \text{sect}ʻQ-\text{ᗡ}ʻ\text{seq}_{Q}\end{align}\] -/
theorem pm211_752 {α : Type u} {P Q : α → α → Prop} {A : Set α} :
    (P ∈ connex ∧ A ⊆ fld P) ∧ Q = P˘ →
      (A ∈ dom (imgRel P ⩀ I) → fld P \ A ∈ sect Q \ codom (seqP Q)) := by
  rintro ⟨⟨hc, -⟩, rfl⟩ hI
  have hA := pm211_14.2 hI
  refine ⟨pm211_7 hA, ?_⟩
  rw [← precP_eq_seqP_cnv]
  rintro ⟨p, hp⟩
  exact pm211_4 hI ⟨p, prec_max hc hA hp⟩

/-- ✱211·753. \[\begin{align}\vdash \colon\ldotp P&\in \text{Rl}ʻJ\cap \text{connex} .\alpha \subset CʻP.Q=\breve{P} .\supset :\\ &\alpha \in \text{D}ʻ(P_{\in }\dot{\cap} I).\equiv .CʻP-\alpha \in \text{sect}ʻQ- \text{ᗡ}ʻ\text{seq}_{Q} \quad[*211·41·7·726]\end{align}\] -/
theorem pm211_753 {α : Type u} {P Q : α → α → Prop} {A : Set α} :
    (P ∈ rl J ∩ connex ∧ A ⊆ fld P) ∧ Q = P˘ →
      (A ∈ dom (imgRel P ⩀ I) ↔ fld P \ A ∈ sect Q \ codom (seqP Q)) := by
  rintro ⟨⟨⟨hJ, hc⟩, hAf⟩, rfl⟩
  refine ⟨pm211_752 ⟨⟨hc, hAf⟩, rfl⟩, fun ⟨hβ, hn⟩ => ?_⟩
  have hA : A ∈ sect P := (pm211_75 ⟨hAf, rfl⟩).2 hβ
  rw [← precP_eq_seqP_cnv] at hn
  rw [pm211_41]
  refine ⟨hA, fun ⟨m, hm⟩ => hn ⟨m, ?_⟩⟩
  show m ∈ refs (precP P) (fld P \ A)
  rw [← (compl_eqs hc hJ hA).1]
  exact hm

/-- ✱211·754. \[\begin{align}\vdash \colon\ldotp P \in\text{Rl}ʻJ\cap &\text{connex} .\alpha \subset CʻP.Q=\breve{P} .\supset :\\ &\alpha \in \text{sect}ʻP-\text{D}ʻP_{\in }.\equiv .CʻP-\alpha \in \text{D}ʻ(Q_{\in }\dot{\cap} I)\cap \text{ᗡ}ʻ\text{seq}_{Q}\end{align}\] -/
theorem pm211_754 {α : Type u} {P Q : α → α → Prop} {A : Set α} :
    (P ∈ rl J ∩ connex ∧ A ⊆ fld P) ∧ Q = P˘ →
      (A ∈ sect P \ dom (imgRel P) ↔ fld P \ A ∈ dom (imgRel Q ⩀ I) ∩ codom (seqP Q)) := by
  rintro ⟨⟨⟨hJ, hc⟩, hAf⟩, rfl⟩
  rw [pm211_316 ⟨hJ, hc⟩, pm211_41, ← precP_eq_seqP_cnv]
  show _ ↔ fld P \ A ∈ (sect P˘ \ codom (minP P)) ∩ codom (precP P)
  constructor
  · rintro ⟨⟨hA, m, hm⟩, hs⟩
    obtain ⟨e1, e2⟩ := compl_eqs hc hJ hA
    refine ⟨⟨pm211_7 hA, fun ⟨n, hn⟩ => hs ⟨n, ?_⟩⟩, m, ?_⟩
    · show n ∈ refs (seqP P) A
      rw [e2]; exact hn
    · show m ∈ refs (precP P) (fld P \ A)
      rw [← e1]; exact hm
  · rintro ⟨⟨hβ, hn⟩, p, hp⟩
    have hA : A ∈ sect P := (pm211_75 ⟨hAf, rfl⟩).2 hβ
    obtain ⟨e1, e2⟩ := compl_eqs hc hJ hA
    refine ⟨⟨hA, p, ?_⟩, fun ⟨s, hs⟩ => hn ⟨s, ?_⟩⟩
    · show p ∈ refs (maxP P) A
      rw [e1]; exact hp
    · show s ∈ refs (minP P) (fld P \ A)
      rw [← e2]; exact hs

/-- ✱211·755. \[\begin{align}&\vdash \colon\ldotp P\in \text{trans}\cap \text{connex} .\alpha \subset CʻP.Q=\breve{P} .\supset :\\ &\alpha \in \text{D}ʻP_{\in }-\text{D}ʻ(P_{\in }\dot{\cap} I).\equiv .CʻP-\alpha \in \text{D}ʻQ_{\in }-\text{D}ʻ(Q_{\in }\dot{\cap} I) \quad[*211·74]\end{align}\] -/
theorem pm211_755 {α : Type u} {P Q : α → α → Prop} {A : Set α} :
    (P ∈ transR ∩ connex ∧ A ⊆ fld P) ∧ Q = P˘ →
      (A ∈ dom (imgRel P) \ dom (imgRel P ⩀ I) ↔
        fld P \ A ∈ dom (imgRel Q) \ dom (imgRel Q ⩀ I)) := by
  rintro ⟨⟨⟨ht, hc⟩, hAf⟩, rfl⟩
  refine ⟨fun h => pm211_74 ⟨⟨ht, hc⟩, h⟩, fun h => ?_⟩
  have h2 := pm211_74 ⟨⟨cnv_trans ht, cnv_connex hc⟩, h⟩
  rw [fld_cnv, compl_compl' hAf] at h2
  exact h2

/-- ✱211·756. \[\begin{align}&\vdash \colon\ldotp P\in \text{ᗡ}ʻʻʻJ\cap \text{connex} .\alpha \subset CʻP.Q=\breve{P} .\supset :\\ &\alpha \in \text{sect}ʻP-\text{D}ʻ(P_{\in }\dot{\cap} I).\equiv .CʻP-\alpha \in \text{sect}ʻQ\cap \text{ᗡ}ʻ\text{seq}_{Q} \quad[*211·41·7·726]\end{align}\]

**Status.** proved (reading): the e-text prints `P ∈ ᗡ'''J ∩ connex` for `P ∈ Rl'J ∩ connex` (the hypothesis of ✱211·753·754, and of ✱211·726, which the proof cites). -/
theorem pm211_756 {α : Type u} {P Q : α → α → Prop} {A : Set α} :
    (P ∈ rl J ∩ connex ∧ A ⊆ fld P) ∧ Q = P˘ →
      (A ∈ sect P \ dom (imgRel P ⩀ I) ↔ fld P \ A ∈ sect Q ∩ codom (seqP Q)) := by
  rintro ⟨⟨⟨hJ, hc⟩, hAf⟩, rfl⟩
  rw [pm211_41, ← precP_eq_seqP_cnv]
  constructor
  · rintro ⟨hA, hm⟩
    have hm' : ∃ m, maxP P m A := by
      by_contra h
      exact hm ⟨hA, h⟩
    obtain ⟨m, hm'⟩ := hm'
    refine ⟨pm211_7 hA, m, ?_⟩
    show m ∈ refs (precP P) (fld P \ A)
    rw [← (compl_eqs hc hJ hA).1]; exact hm'
  · rintro ⟨hβ, p, hp⟩
    have hA : A ∈ sect P := (pm211_75 ⟨hAf, rfl⟩).2 hβ
    refine ⟨hA, fun ⟨_, h⟩ => h ⟨p, ?_⟩⟩
    show p ∈ refs (maxP P) A
    rw [(compl_eqs hc hJ hA).1]; exact hp

/-- ✱211·757. \[\begin{align}\vdash \colon\ldotp P&\in \text{Ser}.\alpha \subset CʻP.\supset :\\ &\alpha \in \text{sect}ʻP- \text{D}ʻ(P_{\in }\dot{\cap} I).\equiv .CʻP-\alpha \in \overleftarrow{P}ʻʻCʻP \quad[*211·756·302]\end{align}\] -/
theorem pm211_757 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser ∧ A ⊆ fld P → (A ∈ sect P \ dom (imgRel P ⩀ I) ↔ fld P \ A ∈ Rbwd P ʻʻ fld P) := by
  rintro ⟨hS, hAf⟩
  rw [pm211_756 ⟨⟨⟨hS.1.1, hS.2⟩, hAf⟩, rfl⟩, ← pm211_302 (cnv_ser hS), fld_cnv]
  exact Iff.rfl

/-- ✱211·76. \(\vdash :P\in \text{Ser}.\supset .\text{D}ʻP_{\in }=(CʻP-)ʻʻ(\text{sect}ʻ\breve{P} -\text{ᗡ}ʻ\text{tl}_P)\) -/
theorem pm211_76 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → dom (imgRel P) = opL (· \ ·) (fld P) ʻʻ (sect P˘ \ codom (tlP P)) := by
  intro hS
  have htl : ∀ B, B ∈ codom (tlP P) ↔ (∃ p, precP P p B) ∧ ¬∃ n, minP P n B :=
    fun B => ⟨fun ⟨p, hp, hn⟩ => ⟨⟨p, hp⟩, hn⟩, fun ⟨⟨p, hp⟩, hn⟩ => ⟨p, hp, hn⟩⟩
  ext A
  constructor
  · intro hA
    have hAf : A ⊆ fld P := (sect_of_seg hS.1.2 hA).1
    have h := (pm211_751 ⟨⟨hS, hAf⟩, rfl⟩).1 hA
    rw [← precP_eq_seqP_cnv] at h
    refine ⟨fld P \ A, ⟨h.1, fun ht => ?_⟩, (compl_compl' hAf).symm⟩
    rw [htl] at ht
    rcases h.2 with hn | hp
    · exact ht.2 hn
    · exact hp ht.1
  · rintro ⟨B, ⟨hB, ht⟩, e⟩
    have e' : A = fld P \ B := e
    have hBf : B ⊆ fld P := by rw [← fld_cnv P]; exact hB.1
    have hAf : A ⊆ fld P := by rw [e']; exact fun x hx => hx.1
    have hBA : fld P \ A = B := by rw [e']; exact compl_compl' hBf
    rw [pm211_751 ⟨⟨hS, hAf⟩, rfl⟩, hBA, ← precP_eq_seqP_cnv]
    refine ⟨hB, ?_⟩
    rw [htl] at ht
    by_cases hn : ∃ n, minP P n B
    · exact Or.inl hn
    · exact Or.inr fun hp => ht ⟨hp, hn⟩

/-- ✱211·761. \[\begin{align}&\vdash :P\in \text{Ser}.\supset .\text{sect}ʻP\cap \text{ᗡ}ʻ\text{lt}_P=(CʻP-)ʻʻ\{\text{sect}ʻ\breve{P} -\text{D}ʻ(\breve{P} )_{\in }\}\\ &[\text{Proof as in *211·76}]\end{align}\] -/
theorem pm211_761 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → sect P ∩ codom (ltP P) = opL (· \ ·) (fld P) ʻʻ (sect P˘ \ dom (imgRel P˘)) := by
  intro hS
  have hS' := cnv_ser hS
  have key : ∀ B, B ⊆ fld P → (B ∈ sect P˘ \ dom (imgRel P˘) ↔
      fld P \ B ∈ dom (imgRel P ⩀ I) ∩ codom (seqP P)) := by
    intro B hB
    have := pm211_754 (A := B) ⟨⟨⟨hS'.1.1, hS'.2⟩, by rw [fld_cnv]; exact hB⟩, rfl⟩
    rw [fld_cnv] at this
    exact this
  ext A
  constructor
  · rintro ⟨hA, x, hs, hm⟩
    have hβ : fld P \ A ⊆ fld P := fun x hx => hx.1
    refine ⟨fld P \ A, (key _ hβ).2 ?_, (compl_compl' hA.1).symm⟩
    rw [compl_compl' hA.1, pm211_41]
    exact ⟨⟨hA, hm⟩, x, hs⟩
  · rintro ⟨B, hB, e⟩
    have e' : A = fld P \ B := e
    have hBf : B ⊆ fld P := by rw [← fld_cnv P]; exact hB.1.1
    have h := (key B hBf).1 hB
    rw [← e', pm211_41] at h
    obtain ⟨⟨hA, hm⟩, x, hx⟩ := h
    exact ⟨hA, x, hx, hm⟩

/-- ✱211·762. \(\vdash :P\in \text{Ser}.\supset .\text{D}ʻ(P_{\in }\dot{\cap} I)=(CʻP-)ʻʻ(\text{sect}ʻ\breve{P} -\overleftarrow{P}ʻʻCʻP)\) -/
theorem pm211_762 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → dom (imgRel P ⩀ I) = opL (· \ ·) (fld P) ʻʻ (sect P˘ \ Rbwd P ʻʻ fld P) := by
  intro hS
  ext A
  constructor
  · intro hI
    have hA := pm211_14.2 hI
    refine ⟨fld P \ A, ⟨pm211_7 hA, fun h => ?_⟩, (compl_compl' hA.1).symm⟩
    exact ((pm211_757 ⟨hS, hA.1⟩).2 h).2 hI
  · rintro ⟨B, ⟨hB, hn⟩, e⟩
    have e' : A = fld P \ B := e
    have hBf : B ⊆ fld P := by rw [← fld_cnv P]; exact hB.1
    have hAf : A ⊆ fld P := by rw [e']; exact fun x hx => hx.1
    have hBA : fld P \ A = B := by rw [e']; exact compl_compl' hBf
    have hA : A ∈ sect P := (pm211_75 ⟨hAf, rfl⟩).2 (by rw [hBA]; exact hB)
    by_contra hI
    have h := (pm211_757 ⟨hS, hAf⟩).1 ⟨hA, hI⟩
    rw [hBA] at h
    exact hn h

/-- ✱211·8. \[\begin{align}&\vdash :P_{\text{po}}\in \text{Ser}.\alpha \in \text{sect}ʻP.\supset .\\ &\overrightarrow{\text{max}}_{P}ʻ\alpha =\overrightarrow{\text{max}}(P_{\text{po}})ʻ\alpha .\overrightarrow{\text{min}}_{P}ʻ(CʻP-\alpha )=\overrightarrow{\text{min}}(P_{\text{po}})ʻ(CʻP-\alpha )=\overrightarrow{\text{seq}} (P_{\text{po}})ʻ\alpha\end{align}\] -/
theorem pm211_8 {α : Type u} {P : α → α → Prop} {A : Set α} :
    po P ∈ Ser ∧ A ∈ sect P →
      (refs (maxP P) A = refs (maxP (po P)) A ∧
        refs (minP P) (fld P \ A) = refs (minP (po P)) (fld P \ A)) ∧
      refs (minP (po P)) (fld P \ A) = refs (seqP (po P)) A := by
  rintro ⟨hS, hA⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext x
    show maxP P x A ↔ maxP (po P) x A
    rw [maxP_iff, maxP_iff, fld_po]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨hx, fun y hy hxy => ?_⟩
      obtain ⟨b, hxb, hby⟩ := Relation.TransGen.head'_iff.1 (po_iff_transGen.1 hxy)
      exact h b (sect_closed_rtg hA hby hy) hxb
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun y hy hxy => h y hy (po_of hxy)⟩
  · ext x
    show minP P x (fld P \ A) ↔ minP (po P) x (fld P \ A)
    rw [minP_iff, minP_iff, fld_po]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨hx, fun y hy hyx => ?_⟩
      obtain ⟨b, hyb, hbx⟩ := Relation.TransGen.tail'_iff.1 (po_iff_transGen.1 hyx)
      refine h b ⟨fld_l hbx, fun hbA => hy.2 (sect_closed_rtg hA hyb hbA)⟩ hbx
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun y hy hyx => h y hy (po_of hyx)⟩
  · have hA' : A ∈ sect (po P) := by rw [sect_po]; exact hA
    have := (compl_eqs hS.2 hS.1.1 hA').2
    rw [fld_po] at this
    exact this.symm

/-- ✱211·81. \[\begin{align}\vdash :P\in \text{Ser}.\alpha \in \text{sect}ʻP.\alpha &{\sim}\in 1.CʻP-\alpha \in 1.\supset .\\ &CʻP-\alpha =\iota ʻBʻ\breve{P} .P=P\unicode{x0294f}\alpha \unicode{x21f8} Bʻ\breve{P} .\alpha =\text{D}ʻP\end{align}\] -/
theorem pm211_81 {α : Type u} {P : α → α → Prop} {A : Set α} :
    ((P ∈ Ser ∧ A ∈ sect P) ∧ A ∉ one) ∧ fld P \ A ∈ one →
      (Desc Beg P˘ (fun b => fld P \ A = ι b) ∧ Desc Beg P˘ (fun b => P = P ⥏ A ⇸ b)) ∧
        A = dom P := by
  rintro ⟨⟨⟨hS, hA⟩, h1⟩, h2⟩
  have hc := hS.2
  have irr := mem_rl_J.1 hS.1.1
  obtain ⟨b, hb⟩ := mem_one_iff.1 h2
  have hbβ : b ∈ fld P \ A := (hb b).2 rfl
  have hAne : ∃ a, a ∈ A := by
    by_contra hA0
    push Not at hA0
    obtain ⟨y, hy | hy⟩ := hbβ.1
    · have := (hb y).1 ⟨fld_r hy, hA0 y⟩
      rw [this] at hy; exact irr b hy
    · have := (hb y).1 ⟨fld_l hy, hA0 y⟩
      rw [this] at hy; exact irr b hy
  obtain ⟨a, ha⟩ := hAne
  have hab : P a b := follow_of_sect hc hA hbβ.1 hbβ.2 ha
  have hbd : b ∉ dom P := by
    rintro ⟨y, hby⟩
    by_cases hyA : y ∈ A
    · exact hbβ.2 (sect_closed hA hby hyA)
    · have := (hb y).1 ⟨fld_r hby, hyA⟩
      rw [this] at hby; exact irr b hby
  have hBeg : ∀ c, Beg c P˘ ↔ c = b := by
    intro c
    constructor
    · rintro ⟨⟨y, hyc⟩, hcd⟩
      have hyc' : P y c := hyc
      have hcf : c ∈ fld P := fld_r hyc'
      by_cases hcA : c ∈ A
      · exact absurd ⟨b, follow_of_sect hc hA hbβ.1 hbβ.2 hcA⟩ hcd
      · exact (hb c).1 ⟨hcf, hcA⟩
    · rintro rfl
      exact ⟨⟨a, hab⟩, hbd⟩
  have hdom : A = dom P := by
    ext x
    constructor
    · intro hx
      exact ⟨b, follow_of_sect hc hA hbβ.1 hbβ.2 hx⟩
    · rintro ⟨y, hxy⟩
      by_contra hxA
      have := (hb x).1 ⟨fld_l hxy, hxA⟩
      rw [this] at hxy
      exact hbd ⟨y, hxy⟩
  have hfA := fld_fres hc hA.1 h1
  refine ⟨⟨desc_of hBeg (Set.ext hb), desc_of hBeg ?_⟩, hdom⟩
  funext x y
  apply propext
  rw [addLast_apply, hfA]
  constructor
  · intro hxy
    have hxA : x ∈ A := by rw [hdom]; exact ⟨y, hxy⟩
    by_cases hyA : y ∈ A
    · exact Or.inl ⟨⟨hxA, hxy⟩, hyA⟩
    · exact Or.inr ⟨hxA, (hb y).1 ⟨fld_r hxy, hyA⟩⟩
  · rintro (h | ⟨hx, rfl⟩)
    · exact h.1.2
    · exact follow_of_sect hc hA hbβ.1 hbβ.2 hx

/-- ✱211·811. \(\vdash :P\in \text{Ser}-\iota ʻ\dot{\Lambda} .P=Q\unicode{x21f8} x.\supset .CʻQ\in \text{sect}ʻP.x=Bʻ\breve{P} .CʻQ=\text{D}ʻP\) -/
theorem pm211_811 {α : Type u} {P Q : α → α → Prop} {x : α} :
    P ∈ Ser \ ι rNull ∧ P = Q ⇸ x →
      (fld Q ∈ sect P ∧ Desc Beg P˘ (fun b => x = b)) ∧ fld Q = dom P := by
  rintro ⟨⟨hS, hN⟩, rfl⟩
  have irr := mem_rl_J.1 hS.1.1
  have hxQ : x ∉ fld Q := fun h => irr x (Or.inr ⟨h, rfl⟩)
  have hQne : ∃ y, y ∈ fld Q := by
    by_contra h0
    push Not at h0
    apply hN
    funext y z
    apply propext
    refine ⟨fun h => ?_, fun h => (rNull_apply _ _ h).elim⟩
    rcases h with h | ⟨hy, -⟩
    · exact absurd (fld_l h) (h0 y)
    · exact absurd hy (h0 y)
  obtain ⟨y₀, hy₀⟩ := hQne
  have hdom : fld Q = dom (Q ⇸ x) := by
    ext y
    constructor
    · intro hy
      exact ⟨x, Or.inr ⟨hy, rfl⟩⟩
    · rintro ⟨z, h | ⟨hy, -⟩⟩
      · exact fld_l h
      · exact hy
  have hBeg : ∀ c, Beg c (Q ⇸ x)˘ ↔ c = x := by
    intro c
    constructor
    · intro hc
      obtain ⟨⟨y, hyc⟩, hcd⟩ := hc
      rcases (show (Q ⇸ x) y c from hyc) with h | ⟨-, h⟩
      · have : c ∈ dom (Q ⇸ x) := by rw [← hdom]; exact fld_r h
        exact absurd this hcd
      · exact h
    · intro hc
      rw [hc]
      refine ⟨⟨y₀, Or.inr ⟨hy₀, rfl⟩⟩, fun hd => hxQ ?_⟩
      rw [hdom]; exact hd
  exact ⟨⟨sect_addLast, desc_of hBeg rfl⟩, hdom⟩

/-- ✱211·812. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}-\iota ʻ\dot{\Lambda} .Q\in \text{D}ʻP\unicode{x0294f}.\supset :\\ &CʻQ\in \text{sect}ʻP.CʻP-CʻQ\in 1.\equiv .(\exists x).P=Q\unicode{x21f8} x.\equiv .P=Q\unicode{x21f8} Bʻ\breve{P}\end{align}\] -/
theorem pm211_812 {α : Type u} {P Q : α → α → Prop} :
    P ∈ Ser \ ι rNull ∧ Q ∈ dom (opL fres P) →
      ((fld Q ∈ sect P ∧ fld P \ fld Q ∈ one) ↔ ∃ x, P = Q ⇸ x) ∧
        ((∃ x, P = Q ⇸ x) ↔ Desc Beg P˘ (fun b => P = Q ⇸ b)) := by
  rintro ⟨⟨hS, hN⟩, S, hQ⟩
  have hQ' : Q = P ⥏ S := hQ
  have eQ := fres_fld_eq hQ'
  constructor
  · constructor
    · rintro ⟨hsect, h2⟩
      have h1 := fld_not_one_of_irr (mem_rl_J.1 hS.1.1) hQ'
      obtain ⟨⟨-, ⟨b, -, hb⟩⟩, -⟩ := pm211_81 ⟨⟨⟨hS, hsect⟩, h1⟩, h2⟩
      rw [← eQ] at hb
      exact ⟨b, hb⟩
    · rintro ⟨x, e⟩
      obtain ⟨⟨hsect, b, hb, hxb⟩, hd⟩ := pm211_811 ⟨⟨hS, hN⟩, e⟩
      refine ⟨hsect, mem_one_iff.2 ⟨x, fun z => ⟨fun ⟨hzf, hzQ⟩ => ?_, ?_⟩⟩⟩
      · rw [hd] at hzQ
        rw [hxb, ← hb z]
        obtain ⟨w, hw | hw⟩ := hzf
        · exact absurd ⟨w, hw⟩ hzQ
        · exact ⟨⟨w, hw⟩, hzQ⟩
      · intro hz
        rw [hz]
        have hbB := (hb b).2 rfl
        rw [← hxb] at hbB
        obtain ⟨⟨w, hw⟩, hd'⟩ := hbB
        refine ⟨fld_r (show P w x from hw), fun hx => hd' ?_⟩
        rw [hd] at hx
        exact hx
  · constructor
    · rintro ⟨x, e⟩
      obtain ⟨⟨-, b, hb, hxb⟩, -⟩ := pm211_811 ⟨⟨hS, hN⟩, e⟩
      exact ⟨b, hb, hxb ▸ e⟩
    · rintro ⟨b, -, e⟩
      exact ⟨b, e⟩

/-- ✱211·82. \[\begin{align}\vdash \colon\colon P\in \text{Ser}.&Q\in \text{D}ʻP\unicode{x0294f}.\supset \colon\ldotp \\ CʻQ\in \text{sect}ʻP.&\equiv :(\exists R).P=Q\unicode{x2909}R.\lor.(\exists x).P=Q\unicode{x21f8} x:\\ &\equiv :(\exists R).P=Q\unicode{x2909}R.\lor.P=Q\unicode{x21f8} Bʻ\breve{P} \\ &[*211·282·283·812.*160·22.*161·2]\end{align}\] -/
theorem pm211_82 {α : Type u} {P Q : α → α → Prop} :
    P ∈ Ser ∧ Q ∈ dom (opL fres P) →
      (fld Q ∈ sect P ↔ (∃ R, P = Q ⤉ R) ∨ ∃ x, P = Q ⇸ x) ∧
        (((∃ R, P = Q ⤉ R) ∨ ∃ x, P = Q ⇸ x) ↔
          (∃ R, P = Q ⤉ R) ∨ Desc Beg P˘ (fun b => P = Q ⇸ b)) := by
  rintro ⟨hS, S, hQ⟩
  have hQ' : Q = P ⥏ S := hQ
  have hJ : P ⪽ J := fun x y h e => mem_rl_J.1 hS.1.1 x (e ▸ h)
  have hnull : P = rNull → P = Q ⤉ rNull := by
    intro e
    have eQ : Q = rNull := by
      rw [hQ', e]
      funext x y
      apply propext
      exact ⟨fun h => h.1.2, fun h => (rNull_apply _ _ h).elim⟩
    rw [e, eQ]
    funext x y
    apply propext
    refine ⟨fun h => (rNull_apply _ _ h).elim, fun h => ?_⟩
    rcases h with (h | h) | ⟨-, ⟨z, h | h⟩⟩
    · exact h
    · exact h
    · exact (rNull_apply _ _ h).elim
    · exact (rNull_apply _ _ h).elim
  constructor
  · constructor
    · intro hsect
      by_cases h2 : fld P \ fld Q ∈ one
      · by_cases hN : P = rNull
        · exact Or.inl ⟨rNull, hnull hN⟩
        · exact Or.inr ((pm211_812 ⟨⟨hS, hN⟩, S, hQ⟩).1.1 ⟨hsect, h2⟩)
      · obtain ⟨R, -, e⟩ := (pm211_282 ⟨⟨hS, S, hQ⟩, h2⟩).1 hsect
        exact Or.inl ⟨R, e⟩
    · rintro (⟨R, e⟩ | ⟨x, rfl⟩)
      · exact pm211_281 ⟨⟨hS, pm211_283 ⟨hJ, e⟩⟩, e⟩
      · exact sect_addLast
  · constructor
    · rintro (h | ⟨x, e⟩)
      · exact Or.inl h
      · by_cases hN : P = rNull
        · exact Or.inl ⟨rNull, hnull hN⟩
        · exact Or.inr ((pm211_812 ⟨⟨hS, hN⟩, S, hQ⟩).2.1 ⟨x, e⟩)
    · rintro (h | ⟨b, -, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨b, e⟩

/-- ✱211·83. \(\vdash :\dot{\exists} !P.x{\sim}\in CʻP.\supset .\text{sect}ʻ(P\unicode{x21f8} x)=\text{sect}ʻP\cup \iota ʻ(CʻP\cup \iota ʻx)\) -/
theorem pm211_83 {α : Type u} {P : α → α → Prop} {x : α} :
    rEx P ∧ x ∉ fld P → sect (P ⇸ x) = sect P ∪ ι (fld P ∪ ι x) := by
  rintro ⟨⟨a, b, hab⟩, hx⟩
  have hfld : fld (P ⇸ x) = fld P ∪ ι x := by
    ext y
    constructor
    · rintro ⟨z, h | h⟩
      · rcases h with h | ⟨hy, -⟩
        · exact Or.inl (fld_l h)
        · exact Or.inl hy
      · rcases h with h | ⟨-, rfl⟩
        · exact Or.inl (fld_r h)
        · exact Or.inr rfl
    · rintro (hy | hy)
      · exact ⟨x, Or.inl (Or.inr ⟨hy, rfl⟩)⟩
      · have hy' : y = x := hy
        rw [hy']
        exact ⟨a, Or.inr (Or.inr ⟨fld_l hab, rfl⟩)⟩
  ext A
  constructor
  · rintro ⟨hAf, hcl⟩
    rw [hfld] at hAf
    by_cases hxA : x ∈ A
    · refine Or.inr (Set.Subset.antisymm hAf fun y hy => ?_)
      rcases hy with hy | hy
      · exact hcl ⟨x, hxA, Or.inr ⟨hy, rfl⟩⟩
      · have hy' : y = x := hy
        rw [hy']; exact hxA
    · refine Or.inl ⟨fun y hy => ?_, fun y ⟨z, hz, hyz⟩ => hcl ⟨z, hz, Or.inl hyz⟩⟩
      rcases hAf hy with h | h
      · exact h
      · have h' : y = x := h
        exact absurd (h' ▸ hy) hxA
  · rintro (hA | hA)
    · refine ⟨fun y hy => by rw [hfld]; exact Or.inl (hA.1 hy), ?_⟩
      rintro y ⟨z, hz, h | ⟨-, rfl⟩⟩
      · exact sect_closed hA h hz
      · exact absurd (hA.1 hz) hx
    · have hA' : A = fld P ∪ ι x := hA
      rw [hA']
      refine ⟨fun y hy => by rw [hfld]; exact hy, ?_⟩
      rintro y ⟨z, -, h | ⟨hy, -⟩⟩
      · exact Or.inl (fld_l h)
      · exact Or.inl hy

/-- ✱211·84. \[\begin{align}\vdash :CʻP\cap CʻQ=\Lambda .\supset .\text{sect}ʻ(P\unicode{x2909}Q)&=\text{sect}ʻP\cup (CʻP\cup )ʻʻ\text{sect}ʻQ\\ &=\text{sect}ʻP\cup (CʻP\cup )ʻʻ(\text{sect}ʻQ-\iota ʻ\Lambda )\end{align} \] -/
theorem pm211_84 {α : Type u} {P Q : α → α → Prop} :
    fld P ∩ fld Q = Λ →
      sect (P ⤉ Q) = sect P ∪ opL (· ∪ ·) (fld P) ʻʻ sect Q ∧
        sect P ∪ opL (· ∪ ·) (fld P) ʻʻ sect Q =
          sect P ∪ opL (· ∪ ·) (fld P) ʻʻ (sect Q \ ι Λ) := by
  intro hd
  have hd' : ∀ z, z ∈ fld P → z ∈ fld Q → False := fun z h1 h2 => eqΛ.1 hd z ⟨h1, h2⟩
  constructor
  · ext A
    constructor
    · rintro ⟨hAf, hcl⟩
      rw [fld_rsum] at hAf
      by_cases hne : ∃ z, z ∈ A ∧ z ∈ fld Q
      · obtain ⟨z, hzA, hzQ⟩ := hne
        have hPA : fld P ⊆ A := fun y hy => hcl ⟨z, hzA, Or.inr ⟨hy, hzQ⟩⟩
        refine Or.inr ⟨A ∩ fld Q, ⟨fun y hy => hy.2, ?_⟩, ?_⟩
        · rintro y ⟨w, hw, hyw⟩
          exact ⟨hcl ⟨w, hw.1, Or.inl (Or.inr hyw)⟩, fld_l hyw⟩
        · show A = fld P ∪ (A ∩ fld Q)
          ext y
          constructor
          · intro hy
            rcases hAf hy with h | h
            · exact Or.inl h
            · exact Or.inr ⟨hy, h⟩
          · rintro (h | h)
            · exact hPA h
            · exact h.1
      · push Not at hne
        refine Or.inl ⟨fun y hy => ?_, fun y ⟨w, hw, hyw⟩ => hcl ⟨w, hw, Or.inl (Or.inl hyw)⟩⟩
        rcases hAf hy with h | h
        · exact h
        · exact absurd h (hne y hy)
    · rintro (hA | ⟨G, hG, rfl⟩)
      · refine ⟨fun y hy => by rw [fld_rsum]; exact Or.inl (hA.1 hy), ?_⟩
        rintro y ⟨w, hw, (h | h) | ⟨-, h⟩⟩
        · exact sect_closed hA h hw
        · exact (hd' w (hA.1 hw) (fld_r h)).elim
        · exact (hd' w (hA.1 hw) h).elim
      · refine ⟨fun y hy => ?_, ?_⟩
        · rw [fld_rsum]
          rcases hy with h | h
          · exact Or.inl h
          · exact Or.inr (hG.1 h)
        · rintro y ⟨w, hw, (h | h) | ⟨hy, -⟩⟩
          · exact Or.inl (fld_l h)
          · rcases hw with hw | hw
            · exact (hd' w hw (fld_r h)).elim
            · exact Or.inr (sect_closed hG h hw)
          · exact Or.inl hy
  · ext A
    constructor
    · rintro (h | ⟨G, hG, rfl⟩)
      · exact Or.inl h
      · by_cases hG0 : G = Λ
        · refine Or.inl ?_
          show fld P ∪ G ∈ sect P
          rw [hG0, Null_eq_empty, Set.union_empty]
          exact pm211_26.1
        · exact Or.inr ⟨G, ⟨hG, hG0⟩, rfl⟩
    · rintro (h | ⟨G, hG, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨G, hG.1, rfl⟩

/-- ✱211·841. \[\begin{align}&\vdash :CʻP\cap CʻQ=\Lambda .\supset .\\ &\text{sect}ʻ(P\unicode{x2909}Q)-\iota ʻ\Lambda =(\text{sect}ʻP-\iota ʻ\Lambda )\cup (CʻP\cup )ʻʻ(\text{sect}ʻQ-\iota ʻ\Lambda ) \quad[*211·84]\end{align}\] -/
theorem pm211_841 {α : Type u} {P Q : α → α → Prop} :
    fld P ∩ fld Q = Λ →
      sect (P ⤉ Q) \ ι Λ = (sect P \ ι Λ) ∪ opL (· ∪ ·) (fld P) ʻʻ (sect Q \ ι Λ) := by
  intro hd
  obtain ⟨e1, e2⟩ := pm211_84 hd
  rw [e1, e2]
  ext A
  constructor
  · rintro ⟨h | h, hA⟩
    · exact Or.inl ⟨h, hA⟩
    · exact Or.inr h
  · rintro (⟨h, hA⟩ | ⟨G, ⟨hG, hG0⟩, rfl⟩)
    · exact ⟨Or.inl h, hA⟩
    · refine ⟨Or.inr ⟨G, ⟨hG, hG0⟩, rfl⟩, fun h0 => hG0 ?_⟩
      have h0' : fld P ∪ G = Λ := h0
      show G = Λ
      rw [eqΛ] at h0' ⊢
      exact fun z hz => h0' z (Or.inr hz)

/-- ✱211·9. \(\vdash .\text{sect}ʻ(x\downarrow y)=\iota ʻ\Lambda \cup \iota ʻ\iota ʻx\cup \iota ʻ(\iota ʻx\cup \iota ʻy)\) -/
theorem pm211_9 {α : Type u} {x y : α} :
    sect (x ↓ y) = ι Λ ∪ ι (ι x) ∪ ι (ι x ∪ ι y) := by
  have hfld : fld (x ↓ y) = ι x ∪ ι y := by
    ext z
    constructor
    · rintro ⟨w, ⟨rfl, -⟩ | ⟨-, rfl⟩⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · have h' : z = x := h
        exact ⟨y, Or.inl ⟨h', rfl⟩⟩
      · have h' : z = y := h
        exact ⟨x, Or.inr ⟨rfl, h'⟩⟩
  ext A
  constructor
  · rintro ⟨hAf, hcl⟩
    rw [hfld] at hAf
    have hyx : y ∈ A → x ∈ A := fun hy => hcl ⟨y, hy, rfl, rfl⟩
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ A
      · refine Or.inr (Set.Subset.antisymm hAf ?_)
        rintro z (h | h)
        · have h' : z = x := h
          rw [h']; exact hx
        · have h' : z = y := h
          rw [h']; exact hy
      · refine Or.inl (Or.inr (Set.Subset.antisymm (fun z hz => ?_) ?_))
        · rcases hAf hz with h | h
          · exact h
          · have h' : z = y := h
            exact absurd (h' ▸ hz) hy
        · intro z hz
          have h' : z = x := hz
          rw [h']; exact hx
    · refine Or.inl (Or.inl ?_)
      show A = Λ
      rw [eqΛ]
      intro z hz
      rcases hAf hz with h | h
      · have h' : z = x := h
        exact hx (h' ▸ hz)
      · have h' : z = y := h
        exact hx (hyx (h' ▸ hz))
  · rintro ((h | h) | h)
    · have h' : A = Λ := h
      rw [h', Null_eq_empty]
      exact ⟨fun z hz => absurd hz (Set.notMem_empty z), fun z ⟨w, hw, _⟩ => absurd hw (Set.notMem_empty w)⟩
    · have h' : A = ι x := h
      rw [h']
      refine ⟨fun z hz => by rw [hfld]; exact Or.inl hz, ?_⟩
      rintro z ⟨w, hw, hzw, -⟩
      exact hzw
    · have h' : A = ι x ∪ ι y := h
      rw [h']
      refine ⟨fun z hz => by rw [hfld]; exact hz, ?_⟩
      rintro z ⟨w, -, hzw, -⟩
      exact Or.inl hzw

/-! ### Helper lemmas for ✱212 -/

section H212

variable {α : Type u} {P : α → α → Prop}

private theorem desc_symm {β : Type v} {R : Set α → β → Prop} {y : β} {c : Set α}
    (h : Desc R y (fun A => A = c)) : Desc R y (fun A => c = A) := by
  obtain ⟨b, h1, h2⟩ := h
  exact ⟨b, h1, h2.symm⟩

private theorem seg_sub_fld {A : Set α} (h : A ∈ dom (imgRel P)) : A ⊆ fld P := by
  obtain ⟨B, rfl⟩ := h
  rintro x ⟨y, -, hxy⟩
  exact fld_l hxy

private theorem seg_sub_dom {A : Set α} (h : A ∈ dom (imgRel P)) : A ⊆ dom P := by
  obtain ⟨B, rfl⟩ := h
  rintro x ⟨y, -, hxy⟩
  exact ⟨y, hxy⟩

private theorem null_mem_D : (Λ : Set α) ∈ dom (imgRel P) := pm211_44.1.2

private theorem null_mem_DI : (Λ : Set α) ∈ dom (imgRel P ⩀ I) := pm211_44.1.1

private theorem Plc_closed {A B : Set α} (hA : P ʻʻ A ⊆ A) :
    Plc P A B ↔ (A ⊆ fld P ∧ B ⊆ fld P) ∧ (B \ A).Nonempty := by
  rw [Plc_iff]
  refine and_congr Iff.rfl ⟨fun ⟨x, hx, _⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx, ?_⟩⟩
  rintro ⟨y, hy, hxy⟩
  exact hx.2 (hA ⟨y, hy.1, hxy⟩)

private theorem Plc_irr {A : Set α} : ¬ Plc P A A := by
  rw [Plc_iff]
  rintro ⟨-, x, ⟨hx, hx'⟩, -⟩
  exact hx' hx

private theorem fld_irr_not_one {β : Type v} {R : β → β → Prop} (irr : ∀ x, ¬ R x x) :
    fld R ∉ one := by
  intro h1
  obtain ⟨b, hb⟩ := mem_one_iff.1 h1
  obtain ⟨y, hy | hy⟩ := (hb b).2 rfl
  · have e := (hb y).1 (fld_r hy)
    rw [e] at hy
    exact irr b hy
  · have e := (hb y).1 (fld_l hy)
    rw [e] at hy
    exact irr b hy

private theorem DI_anc : dom (imgRel (anc P) ⩀ I) = sect P := by
  ext A
  rw [mem_dom_imgRel_rcap_I]
  exact sect_iff_anc.symm

private theorem D_anc : dom (imgRel (anc P)) = sect P := by
  ext A
  exact mem_dom_imgRel_anc

private theorem segSer_anc_iff {A B : Set α} :
    segSer (anc P) A B ↔ (A ∈ sect P ∧ B ∈ sect P) ∧ (B \ A).Nonempty := by
  rw [segSer_apply, D_anc]
  constructor
  · rintro ⟨⟨hA, h⟩, hB⟩
    have hA' : A ∈ sect (anc P) := by rw [sect_anc]; exact hA
    rw [Plc_closed hA'.2] at h
    exact ⟨⟨hA, hB⟩, h.2⟩
  · rintro ⟨⟨hA, hB⟩, h⟩
    have hA' : A ∈ sect (anc P) := by rw [sect_anc]; exact hA
    refine ⟨⟨hA, (Plc_closed hA'.2).2 ⟨⟨?_, ?_⟩, h⟩⟩, hB⟩
    · rw [fld_anc]; exact hA.1
    · rw [fld_anc]; exact hB.1

private theorem segSer_anc_eq : segSer (anc P) = Plc P ⥏ sect P := by
  funext A B
  apply propext
  rw [segSer_anc_iff]
  show _ ↔ (A ∈ sect P ∧ Plc P A B) ∧ B ∈ sect P
  constructor
  · rintro ⟨⟨hA, hB⟩, h⟩
    exact ⟨⟨hA, (Plc_closed hA.2).2 ⟨⟨hA.1, hB.1⟩, h⟩⟩, hB⟩
  · rintro ⟨⟨hA, h⟩, hB⟩
    exact ⟨⟨hA, hB⟩, ((Plc_closed hA.2).1 h).2⟩

private theorem H12_sect (hc : P ∈ connex) :
    (∀ C D, C ∈ sect P ∧ D ∈ sect P → C ⊆ D ∨ D ⊆ C) ∧
      segSer (anc P) = (fun C D => ((C ∈ sect P ∧ D ∈ sect P) ∧ C ⊆ D) ∧ C ≠ D) := by
  rw [segSer_anc_eq]
  exact pm211_67 ⟨⟨hc, rfl⟩, rfl⟩

private theorem H12_seg (h : P ∈ transR ∩ connex) :
    (∀ C D, C ∈ dom (imgRel P) ∧ D ∈ dom (imgRel P) → C ⊆ D ∨ D ⊆ C) ∧
      segSer P = (fun C D => ((C ∈ dom (imgRel P) ∧ D ∈ dom (imgRel P)) ∧ C ⊆ D) ∧ C ≠ D) :=
  pm211_68 ⟨⟨h, rfl⟩, rfl⟩

private theorem H12_sgm (hc : P ∈ connex) :
    (∀ C D, C ∈ dom (imgRel P ⩀ I) ∧ D ∈ dom (imgRel P ⩀ I) → C ⊆ D ∨ D ⊆ C) ∧
      sgm P = (fun C D => ((C ∈ dom (imgRel P ⩀ I) ∧ D ∈ dom (imgRel P ⩀ I)) ∧ C ⊆ D) ∧ C ≠ D) :=
  pm211_69 ⟨⟨hc, rfl⟩, rfl⟩

/-- `prec_Q'λ = p'λ ∩ s'κ` when `p'λ ∩ s'κ ∈ κ` and `p'λ ∉ λ` (cf. ✱210·252). -/
private theorem prec_prodsum {K : Set (Set α)} (hn : Nest K) (h1 : K ∉ one) {L : Set (Set α)}
    (hL : L ⊆ K) (hpL : prodCls L ∉ L) (hK : prodCls L ∩ sumCls K ∈ K) (A : Set α) :
    precP (incl K) A L ↔ A = prodCls L ∩ sumCls K := by
  have hs : sumCls (K ∩ cl (prodCls L)) = prodCls L ∩ sumCls K := by
    refine Set.Subset.antisymm (fun x hx => ?_)
      (fun x hx => ⟨_, ⟨hK, Set.inter_subset_left⟩, hx⟩)
    obtain ⟨C, hC, hx⟩ := hx
    exact ⟨hC.2 hx, C, hC.1, hx⟩
  have h := prec_eq_of hn h1 hL hpL (hs ▸ hK) A
  rw [hs] at h
  exact h

private theorem prec_tl_chain {K : Set (Set α)} (hn : Nest K) {L : Set (Set α)} (hL : L ⊆ K)
    (hp : prodCls L ∉ L) {σ : Set α} (hprec : ∀ A, precP (incl K) A L ↔ A = σ) :
    Desc (precP (incl K)) L (fun A => σ = A) ∧
      Desc (precP (incl K)) L (fun A => Desc (tlP (incl K)) L (fun B => A = B)) :=
  ⟨desc_of hprec rfl, desc2_of hprec (fun A => (tl_iff_of (nomin_of hn hL hp)).trans (hprec A))⟩

private theorem pm212_2_aux : sgm P ⪽ segSer P :=
  fun _ _ h => ⟨⟨pm211_14.1 h.1.1, h.1.2⟩, pm211_14.1 h.2⟩

private theorem rEx_of_fld {β : Type v} {R : β → β → Prop} {x : β} (h : x ∈ fld R) : rEx R := by
  obtain ⟨y, h | h⟩ := h
  · exact ⟨x, y, h⟩
  · exact ⟨y, x, h⟩

end H212

/-!
## [✱212] The series of segments

*(Vol. 2, p. 651)*

> *Summary of* *212.
>
> The series of segments or sections of a series may be ordered by the relation of inclusion, after the manner considered in *210. Since, as was shown in *211, sections and segments have the properties assigned to \(\kappa\) in the hypothesis of *210, the resulting series are such that every class has either a maximum or a sequent, and either a minimum or a precedent; *i.e.* the series of segments or sections are Dedekindian. Most of the properties of the series of sections and of the series of segments which have no maximum, only require that the original relation should be connected. The properties of the series of segments in general \((\text{D}ʻP_{\in })\) require also that the original relation should be transitive.
>
> We denote the series of segments by \(\varsigma ʻP\), putting \[ \varsigma ʻP=P_{\text{lc}}\unicode{x0294f}\text{D}ʻP_{\in } \quad\text{Df}. \]
>
> We then have, in virtue of *210·13 and *211·61,
>
> *212·23. \(\vdash :P\in \text{trans}\cap \text{connex} .\supset .\varsigma ʻP=\hat{\alpha} \hat{\beta} \{\alpha ,\beta \in \text{D}ʻP_{\in }.\alpha \subset \beta .\alpha \neq \beta\}\)
>
> …

**Lean reading.** `ς'P` is `segSer P`, `sgm'P` is `sgm P`, the series of sections `ς'P_*` is
`segSer (anc P)` (`= P_lc ⥏ sect'P`, ✱212·121), `Cnv'ς'P` is `(segSer P)˘`, `P⃗;P` is
`Rfwd P ⁏ P`, `S_∈` is `imgRel S`; `max(ς'P)'λ`, `seq(ς'P)'λ`, `B'ς'P`, … are descriptions
(`Desc (maxP (segSer P)) L ψ`, …) and their arrows are `refs`. The limit theorems for `ς'P_*`,
`ς'P` and `sgm'P` (✱212·32–·55) are obtained from ✱210 with `κ = sect'P`, `D'P_∈`,
`D'(P_∈ ∩̇ I)` (the hypotheses of ✱210·12 being ✱211·67·68·69); ✱212·6–·667 compare `P` with the
rational segments `P⃗''C'P`, and ✱212·7–·72 transport sections and segments along a correlator.

**Status.** proved (all propositions; ✱212·122, ✱212·32, ✱212·54, ✱212·712 proved (reading):
misprints of the e-text, see their docstrings)
-/

/-- ✱212·01 (Df). \(\varsigma ʻP=P_{\text{lc}}\unicode{x0294f}\text{D}ʻP_{\in } \quad\text{Df}\) -/
theorem pm212_01 {α : Type u} {P : α → α → Prop} : segSer P = Plc P ⥏ dom (imgRel P) := rfl

/-- ✱212·02 (Df). \(\text{sgm}ʻP=P_{\text{lc}}\unicode{x0294f}\text{D}ʻ(P_{\in }\dot{\cap} I) \quad\text{Df}\) -/
theorem pm212_02 {α : Type u} {P : α → α → Prop} : sgm P = Plc P ⥏ dom (imgRel P ⩀ I) := rfl

/-- ✱212·1. \[\begin{align}&\vdash :\alpha (\varsigma ʻP)\beta .\equiv .\alpha ,\beta \in \text{D}ʻP_{\in }.\exists !\beta -\alpha -Pʻʻ(\alpha -\beta )\\ &[*170·102.*37·15]\end{align}\] -/
theorem pm212_1 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    segSer P A B ↔ (A ∈ dom (imgRel P) ∧ B ∈ dom (imgRel P)) ∧
      ((B \ A) \ P ʻʻ (A \ B)).Nonempty := by
  rw [segSer_apply, Plc_iff]
  constructor
  · rintro ⟨⟨hA, -, h⟩, hB⟩
    exact ⟨⟨hA, hB⟩, h⟩
  · rintro ⟨⟨hA, hB⟩, h⟩
    exact ⟨⟨hA, ⟨seg_sub_fld hA, seg_sub_fld hB⟩, h⟩, hB⟩

/-- ✱212·11. \(\vdash :\alpha (\text{sgm}ʻP)\beta .\equiv .\alpha ,\beta \in \text{D}ʻ(P_{\in }\dot{\cap} I).\exists !\beta -\alpha\) -/
theorem pm212_11 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    sgm P A B ↔ (A ∈ dom (imgRel P ⩀ I) ∧ B ∈ dom (imgRel P ⩀ I)) ∧ (B \ A).Nonempty := by
  show (A ∈ dom (imgRel P ⩀ I) ∧ Plc P A B) ∧ B ∈ dom (imgRel P ⩀ I) ↔ _
  constructor
  · rintro ⟨⟨hA, h⟩, hB⟩
    exact ⟨⟨hA, hB⟩, ((Plc_closed (pm211_14.2 hA).2).1 h).2⟩
  · rintro ⟨⟨hA, hB⟩, h⟩
    exact ⟨⟨hA, (Plc_closed (pm211_14.2 hA).2).2
      ⟨⟨(pm211_14.2 hA).1, (pm211_14.2 hB).1⟩, h⟩⟩, hB⟩

/-- ✱212·12. \(\vdash :\alpha (\text{sgm}ʻP_{*})\beta .\equiv .\alpha ,\beta \in \text{sect}ʻP.\exists !\beta -\alpha \quad[*211·13.*212·11]\) -/
theorem pm212_12 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    sgm (anc P) A B ↔ (A ∈ sect P ∧ B ∈ sect P) ∧ (B \ A).Nonempty := by
  rw [pm212_11, DI_anc]

/-- ✱212·121. \(\vdash .\text{sgm}ʻP_{*}=\varsigma ʻP_{*}=P_{\text{lc}}\unicode{x0294f}\text{sect}ʻP\) -/
theorem pm212_121 {α : Type u} {P : α → α → Prop} :
    sgm (anc P) = segSer (anc P) ∧ segSer (anc P) = Plc P ⥏ sect P := by
  refine ⟨?_, segSer_anc_eq⟩
  funext A B
  apply propext
  rw [pm212_12, segSer_anc_iff]

/-- ✱212·122. \(\vdash .\varsigma ʻP,\text{sgm}ʻP\in \text{ᗡ}ʻʻʻJ \quad[*170·17]\)

**Status.** proved (reading): the e-text prints `ς'P, sgm'P ∈ ᗡ'''J` for `ς'P, sgm'P ∈ Rl'J`; the demonstration cites ✱170·17 (`P_lc ⊂̇ J`), so the relations are contained in diversity. -/
theorem pm212_122 {α : Type u} {P : α → α → Prop} : segSer P ∈ rl J ∧ sgm P ∈ rl J :=
  ⟨mem_rl_J.2 fun _ h => Plc_irr h.1.2, mem_rl_J.2 fun _ h => Plc_irr h.1.2⟩

/-- ✱212·123. \(\vdash .Cʻ\varsigma ʻP,Cʻ\text{sgm}ʻP{\sim}\in 1 \quad[*200·12.*212·122]\) -/
theorem pm212_123 {α : Type u} {P : α → α → Prop} : fld (segSer P) ∉ one ∧ fld (sgm P) ∉ one :=
  ⟨fld_irr_not_one (mem_rl_J.1 pm212_122.1), fld_irr_not_one (mem_rl_J.1 pm212_122.2)⟩

/-- ✱212·13. \(\vdash :\Lambda (\varsigma ʻP)\beta .\equiv .\beta \in \text{D}ʻP_{\in }-\iota ʻ\Lambda \quad[*170·6]\) -/
theorem pm212_13 {α : Type u} {P : α → α → Prop} {B : Set α} :
    segSer P Λ B ↔ B ∈ dom (imgRel P) \ ι Λ := by
  rw [pm212_1]
  constructor
  · rintro ⟨⟨-, hB⟩, x, ⟨hxB, -⟩, -⟩
    refine ⟨hB, fun e => ?_⟩
    have e' : B = Λ := e
    rw [e', Null_eq_empty] at hxB
    exact Set.notMem_empty x hxB
  · rintro ⟨hB, hne⟩
    refine ⟨⟨null_mem_D, hB⟩, ?_⟩
    have : B ≠ Λ := hne
    rw [Ne, eqΛ] at this
    push Not at this
    obtain ⟨x, hx⟩ := this
    refine ⟨x, ⟨hx, by rw [Null_eq_empty]; exact Set.notMem_empty x⟩, ?_⟩
    rintro ⟨y, ⟨hy, -⟩, -⟩
    rw [Null_eq_empty] at hy
    exact Set.notMem_empty y hy

/-- ✱212·131. \(\vdash :\alpha (\varsigma ʻP)(\text{D}ʻP).\equiv .\alpha \in \text{D}ʻP_{\in }-\iota ʻ\text{D}ʻP\) -/
theorem pm212_131 {α : Type u} {P : α → α → Prop} {A : Set α} :
    segSer P A (dom P) ↔ A ∈ dom (imgRel P) \ ι (dom P) := by
  rw [pm212_1]
  constructor
  · rintro ⟨⟨hA, -⟩, x, ⟨hx, hxA⟩, -⟩
    refine ⟨hA, fun e => hxA ?_⟩
    have e' : A = dom P := e
    rw [e']; exact hx
  · rintro ⟨hA, hne⟩
    have hsub := seg_sub_dom hA
    have : ¬ dom P ⊆ A := fun h => hne (Set.Subset.antisymm hsub h)
    obtain ⟨x, hx, hxA⟩ := Set.not_subset.1 this
    refine ⟨⟨hA, pm211_301⟩, x, ⟨hx, hxA⟩, ?_⟩
    rintro ⟨y, ⟨hyA, hyD⟩, -⟩
    exact hyD (hsub hyA)

/-- ✱212·132. \(\vdash .\text{D}ʻ\varsigma ʻP=\text{D}ʻP_{\in }-\iota ʻ\text{D}ʻP.\text{ᗡ}ʻ\varsigma ʻP= \text{D}ʻP_{\in }-\iota ʻ\Lambda\) -/
theorem pm212_132 {α : Type u} {P : α → α → Prop} :
    dom (segSer P) = dom (imgRel P) \ ι (dom P) ∧ codom (segSer P) = dom (imgRel P) \ ι Λ := by
  constructor
  · ext A
    constructor
    · rintro ⟨B, h⟩
      obtain ⟨⟨hA, hB⟩, x, ⟨hxB, hxA⟩, -⟩ := pm212_1.1 h
      refine ⟨hA, fun e => hxA ?_⟩
      have e' : A = dom P := e
      rw [e']; exact seg_sub_dom hB hxB
    · intro h
      exact ⟨dom P, pm212_131.2 h⟩
  · ext B
    constructor
    · rintro ⟨A, h⟩
      obtain ⟨⟨-, hB⟩, x, ⟨hxB, -⟩, -⟩ := pm212_1.1 h
      refine ⟨hB, fun e => ?_⟩
      have e' : B = Λ := e
      rw [e', Null_eq_empty] at hxB
      exact Set.notMem_empty x hxB
    · intro h
      exact ⟨Λ, pm212_13.2 h⟩

/-- ✱212·133. \(\vdash :\dot{\exists} !P.\supset .Cʻ\varsigma ʻP=\text{D}ʻP_{\in }.Bʻ\varsigma ʻP=\Lambda .Bʻ\text{Cnv}ʻ\varsigma ʻP= \text{D}ʻP\) -/
theorem pm212_133 {α : Type u} {P : α → α → Prop} :
    rEx P → (fld (segSer P) = dom (imgRel P) ∧ Desc Beg (segSer P) (fun b => b = Λ)) ∧
      Desc Beg (segSer P)˘ (fun b => b = dom P) := by
  rintro ⟨a, b, hab⟩
  have hne : dom P ≠ Λ := by
    intro e
    have : a ∈ dom P := ⟨b, hab⟩
    rw [e, Null_eq_empty] at this
    exact Set.notMem_empty a this
  obtain ⟨hd, hcd⟩ := pm212_132 (P := P)
  have hfld : fld (segSer P) = dom (imgRel P) := by
    rw [fld_eq_dom_union_codom, hd, hcd]
    ext A
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      by_cases e : A = Λ
      · refine Or.inl ⟨h, fun e' => hne ?_⟩
        have e'' : A = dom P := e'
        rw [← e'', e]
      · exact Or.inr ⟨h, e⟩
  refine ⟨⟨hfld, desc_of (fun c => ?_) rfl⟩, desc_of (fun c => ?_) rfl⟩
  · show c ∈ dom (segSer P) \ codom (segSer P) ↔ c = Λ
    rw [hd, hcd]
    constructor
    · rintro ⟨⟨hc, -⟩, h⟩
      by_contra hc'
      exact h ⟨hc, hc'⟩
    · rintro rfl
      exact ⟨⟨null_mem_D, fun e => hne (show Λ = dom P from e).symm⟩, fun h => h.2 rfl⟩
  · show c ∈ codom (segSer P) \ dom (segSer P) ↔ c = dom P
    rw [hd, hcd]
    constructor
    · rintro ⟨⟨hc, -⟩, h⟩
      by_contra hc'
      exact h ⟨hc, hc'⟩
    · rintro rfl
      exact ⟨⟨pm211_301, hne⟩, fun h => h.2 rfl⟩

/-- ✱212·134. \(\vdash :P=\dot{\Lambda} .\supset .\varsigma ʻP=\dot{\Lambda} \quad[*170·35]\) -/
theorem pm212_134 {α : Type u} {P : α → α → Prop} : P = rNull → segSer P = rNull := by
  rintro rfl
  funext A B
  apply propext
  refine ⟨fun h => ?_, fun h => (rNull_apply _ _ h).elim⟩
  obtain ⟨⟨-, hB⟩, x, ⟨hxB, -⟩, -⟩ := pm212_1.1 h
  obtain ⟨y, hy | hy⟩ := seg_sub_fld hB hxB
  · exact (rNull_apply _ _ hy).elim
  · exact (rNull_apply _ _ hy).elim

/-- ✱212·14. \(\vdash :\dot{\exists} !P.\equiv .\dot{\exists} !\varsigma ʻP\) -/
theorem pm212_14 {α : Type u} {P : α → α → Prop} : rEx P ↔ rEx (segSer P) := by
  constructor
  · intro h
    exact rEx_of_fld (x := Λ) (by rw [(pm212_133 h).1.1]; exact null_mem_D)
  · rintro ⟨A, B, h⟩
    obtain ⟨⟨-, hB⟩, x, ⟨hxB, -⟩, -⟩ := pm212_1.1 h
    exact rEx_of_fld (seg_sub_fld hB hxB)

/-- ✱212·141. \(\vdash :\alpha \in Cʻ\varsigma ʻP.\equiv .\alpha \in \text{D}ʻP_{\in }.\dot{\exists} !P\) -/
theorem pm212_141 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∈ fld (segSer P) ↔ A ∈ dom (imgRel P) ∧ rEx P := by
  constructor
  · intro h
    have hP := pm212_14.2 (rEx_of_fld h)
    rw [(pm212_133 hP).1.1] at h
    exact ⟨h, hP⟩
  · rintro ⟨h, hP⟩
    rw [(pm212_133 hP).1.1]
    exact h

/-- ✱212·142. \(\vdash :\dot{\exists} !\varsigma ʻP.\equiv .\text{D}ʻP_{\in }{\sim}\in 1\) -/
theorem pm212_142 {α : Type u} {P : α → α → Prop} : rEx (segSer P) ↔ dom (imgRel P) ∉ one := by
  rw [← pm212_14]
  refine ⟨fun h => (pm211_66 h).2, fun h => ?_⟩
  by_contra hP
  apply h
  refine mem_one_iff.2 ⟨Λ, fun A => ⟨fun hA => ?_, fun e => e ▸ null_mem_D⟩⟩
  rw [eqΛ]
  intro x hx
  exact hP (rEx_of_fld (seg_sub_fld hA hx))

/-- ✱212·15. \(\vdash :\Lambda (\text{sgm}ʻP)\beta .\equiv .\beta \in \text{D}ʻ(P_{\in }\dot{\cap} I)-\iota ʻ\Lambda \quad[\text{Proof as in *212·13}]\) -/
theorem pm212_15 {α : Type u} {P : α → α → Prop} {B : Set α} :
    sgm P Λ B ↔ B ∈ dom (imgRel P ⩀ I) \ ι Λ := by
  rw [pm212_11]
  constructor
  · rintro ⟨⟨-, hB⟩, x, hxB, -⟩
    refine ⟨hB, fun e => ?_⟩
    have e' : B = Λ := e
    rw [e', Null_eq_empty] at hxB
    exact Set.notMem_empty x hxB
  · rintro ⟨hB, hne⟩
    refine ⟨⟨null_mem_DI, hB⟩, ?_⟩
    have : B ≠ Λ := hne
    rw [Ne, eqΛ] at this
    push Not at this
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx, by rw [Null_eq_empty]; exact Set.notMem_empty x⟩

/-- ✱212·151. \(\vdash :P=\dot{\Lambda} .\supset .\text{sgm}ʻP=\dot{\Lambda} \quad[*170·35]\) -/
theorem pm212_151 {α : Type u} {P : α → α → Prop} : P = rNull → sgm P = rNull := by
  intro h
  funext A B
  apply propext
  refine ⟨fun h' => ?_, fun h' => (rNull_apply _ _ h').elim⟩
  rw [← pm212_134 h]
  exact pm212_2_aux A B h'

/-- ✱212·152. \(\vdash .\text{ᗡ}ʻ\text{sgm}ʻP=\text{D}ʻ(P_{\in }\dot{\cap} I)-\iota ʻ\Lambda \quad[\text{Proof as in *212·132}]\) -/
theorem pm212_152 {α : Type u} {P : α → α → Prop} :
    codom (sgm P) = dom (imgRel P ⩀ I) \ ι Λ := by
  ext B
  constructor
  · rintro ⟨A, h⟩
    obtain ⟨⟨-, hB⟩, x, hxB, -⟩ := pm212_11.1 h
    refine ⟨hB, fun e => ?_⟩
    have e' : B = Λ := e
    rw [e', Null_eq_empty] at hxB
    exact Set.notMem_empty x hxB
  · intro h
    exact ⟨Λ, pm212_15.2 h⟩

/-- ✱212·153. \(\vdash :\dot{\exists} !\text{sgm}ʻP.\equiv .\exists !\text{D}ʻ(P_{\in }\dot{\cap} I)-\iota ʻ\Lambda .\equiv .\text{D}ʻ(P_{\in }\dot{\cap} I){\sim}\in 1\) -/
theorem pm212_153 {α : Type u} {P : α → α → Prop} :
    (rEx (sgm P) ↔ (dom (imgRel P ⩀ I) \ ι Λ).Nonempty) ∧
      ((dom (imgRel P ⩀ I) \ ι Λ).Nonempty ↔ dom (imgRel P ⩀ I) ∉ one) := by
  constructor
  · constructor
    · rintro ⟨A, B, h⟩
      exact ⟨B, by rw [← pm212_152]; exact ⟨A, h⟩⟩
    · rintro ⟨B, hB⟩
      exact ⟨Λ, B, pm212_15.2 hB⟩
  · constructor
    · rintro ⟨B, hB, hne⟩ h1
      obtain ⟨b, hb⟩ := mem_one_iff.1 h1
      exact hne (((hb B).1 hB).trans ((hb Λ).1 null_mem_DI).symm)
    · intro h1
      obtain ⟨B, hB, hne⟩ := not_one h1 null_mem_DI
      exact ⟨B, hB, hne⟩

/-- ✱212·154. \(\vdash :\dot{\exists} !\text{sgm}ʻP.\supset .Cʻ\text{sgm}ʻP=\text{D}ʻ(P_{\in }\dot{\cap} I)\) -/
theorem pm212_154 {α : Type u} {P : α → α → Prop} :
    rEx (sgm P) → fld (sgm P) = dom (imgRel P ⩀ I) := by
  intro h
  obtain ⟨B₀, hB₀⟩ := pm212_153.1.1 h
  ext A
  constructor
  · rintro ⟨B, h' | h'⟩
    · exact h'.1.1
    · exact h'.2
  · intro hA
    by_cases e : A = Λ
    · rw [e]
      exact ⟨B₀, Or.inl (pm212_15.2 hB₀)⟩
    · exact ⟨Λ, Or.inr (pm212_15.2 ⟨hA, e⟩)⟩

/-- ✱212·155. \(\vdash :\dot{\exists} !\text{sgm}ʻP.\supset .\Lambda =Bʻ\text{sgm}ʻP \quad[*212·152·154.*93·103]\) -/
theorem pm212_155 {α : Type u} {P : α → α → Prop} :
    rEx (sgm P) → Desc Beg (sgm P) (fun b => Λ = b) := by
  intro h
  obtain ⟨B₀, hB₀⟩ := pm212_153.1.1 h
  refine desc_of (fun c => ⟨fun hc => ?_, ?_⟩) rfl
  · obtain ⟨⟨B, hB⟩, hc2⟩ := hc
    have hcf : c ∈ fld (sgm P) := ⟨B, Or.inl hB⟩
    rw [pm212_154 h] at hcf
    by_contra hc
    exact hc2 (by rw [pm212_152]; exact ⟨hcf, hc⟩)
  · rintro rfl
    refine ⟨⟨B₀, pm212_15.2 hB₀⟩, fun hc => ?_⟩
    rw [pm212_152] at hc
    exact hc.2 rfl

/-- ✱212·156. \[\begin{align}\vdash :\alpha \in Cʻ\text{sgm}ʻP.&\equiv .\alpha \in \text{D}ʻ(P_{\in }\dot{\cap} I).\dot{\exists} !\text{sgm}ʻP.\\ &\equiv .\alpha \in \text{D}ʻ(P_{\in }\dot{\cap} I).\text{D}ʻ(P_{\in }\dot{\cap} I){\sim}\in 1\end{align}\] -/
theorem pm212_156 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (A ∈ fld (sgm P) ↔ A ∈ dom (imgRel P ⩀ I) ∧ rEx (sgm P)) ∧
      (A ∈ dom (imgRel P ⩀ I) ∧ rEx (sgm P) ↔ A ∈ dom (imgRel P ⩀ I) ∧
        dom (imgRel P ⩀ I) ∉ one) := by
  constructor
  · constructor
    · intro h
      have hs := rEx_of_fld h
      rw [pm212_154 hs] at h
      exact ⟨h, hs⟩
    · rintro ⟨h, hs⟩
      rw [pm212_154 hs]
      exact h
  · rw [pm212_153.1, pm212_153.2]

/-- ✱212·16. \(\vdash :\text{ᗡ}ʻP\subset \text{D}ʻP.\supset .\text{D}ʻP\in \text{D}ʻ(P_{\in }\dot{\cap} I)\) -/
theorem pm212_16 {α : Type u} {P : α → α → Prop} :
    codom P ⊆ dom P → dom P ∈ dom (imgRel P ⩀ I) := by
  intro h
  refine mem_dom_imgRel_rcap_I.2 (Set.Subset.antisymm (fun x ⟨y, hxy⟩ => ?_)
    (fun x ⟨y, _, hxy⟩ => ⟨y, hxy⟩))
  exact ⟨y, h ⟨x, hxy⟩, hxy⟩

/-- ✱212·161. \(\vdash :\text{ᗡ}ʻP\subset \text{D}ʻP.\dot{\exists} !P.\supset .\dot{\exists} !\text{sgm}ʻP\) -/
theorem pm212_161 {α : Type u} {P : α → α → Prop} :
    codom P ⊆ dom P ∧ rEx P → rEx (sgm P) := by
  rintro ⟨h, a, b, hab⟩
  refine ⟨Λ, dom P, pm212_15.2 ⟨pm212_16 h, fun e => ?_⟩⟩
  have e' : dom P = Λ := e
  have : a ∈ dom P := ⟨b, hab⟩
  rw [e', Null_eq_empty] at this
  exact Set.notMem_empty a this

/-- ✱212·162. \[\begin{align}\vdash :\text{ᗡ}ʻP\subset \text{D}ʻ&P.\dot{\exists} !P.\supset .\\ &\text{D}ʻP=Bʻ\text{Cnv}ʻ\text{sgm}ʻP.\text{D}ʻ\text{sgm}ʻP=\text{D}ʻ(P_{\in }\dot{\cap} I)-\iota ʻ\text{D}ʻP\end{align}\] -/
theorem pm212_162 {α : Type u} {P : α → α → Prop} :
    codom P ⊆ dom P ∧ rEx P → Desc Beg (sgm P)˘ (fun b => dom P = b) ∧
      dom (sgm P) = dom (imgRel P ⩀ I) \ ι (dom P) := by
  intro h
  have hD := pm212_16 h.1
  have hne : dom P ∉ ι Λ := by
    intro e
    obtain ⟨a, b, hab⟩ := h.2
    have e' : dom P = Λ := e
    have : a ∈ dom P := ⟨b, hab⟩
    rw [e', Null_eq_empty] at this
    exact Set.notMem_empty a this
  have hsub : ∀ A, A ∈ dom (imgRel P ⩀ I) → A ⊆ dom P := fun A hA => seg_sub_dom (pm211_14.1 hA)
  have hdom : dom (sgm P) = dom (imgRel P ⩀ I) \ ι (dom P) := by
    ext A
    constructor
    · rintro ⟨B, hAB⟩
      obtain ⟨⟨hA, hB⟩, x, hxB, hxA⟩ := pm212_11.1 hAB
      refine ⟨hA, fun e => hxA ?_⟩
      have e' : A = dom P := e
      rw [e']; exact hsub B hB hxB
    · rintro ⟨hA, hAne⟩
      have : ¬ dom P ⊆ A := fun h' => hAne (Set.Subset.antisymm (hsub A hA) h')
      obtain ⟨x, hx, hxA⟩ := Set.not_subset.1 this
      exact ⟨dom P, pm212_11.2 ⟨⟨hA, hD⟩, x, hx, hxA⟩⟩
  refine ⟨desc_of (fun c => ?_) rfl, hdom⟩
  show c ∈ codom (sgm P) \ dom (sgm P) ↔ c = dom P
  rw [hdom, pm212_152]
  constructor
  · rintro ⟨⟨hc, -⟩, h'⟩
    by_contra hc'
    exact h' ⟨hc, hc'⟩
  · rintro rfl
    exact ⟨⟨hD, hne⟩, fun h' => h'.2 rfl⟩

/-- ✱212·17. \(\vdash :\dot{\exists} !\varsigma ʻP_{*}.\equiv .\exists !\text{sect}ʻP-\iota ʻ\Lambda .\equiv .\text{sect}ʻP{\sim}\in 1.\equiv .\dot{\exists} !P\) -/
theorem pm212_17 {α : Type u} {P : α → α → Prop} :
    ((rEx (segSer (anc P)) ↔ (sect P \ ι Λ).Nonempty) ∧
      ((sect P \ ι Λ).Nonempty ↔ sect P ∉ one)) ∧ (sect P ∉ one ↔ rEx P) := by
  have hΛ : (Λ : Set α) ∈ sect P := pm211_44.2
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨?_, fun h => (pm211_66 h).1⟩⟩
  · rintro ⟨A, B, h⟩
    obtain ⟨⟨-, hB⟩, x, hxB, -⟩ := segSer_anc_iff.1 h
    refine ⟨B, hB, fun e => ?_⟩
    have e' : B = Λ := e
    rw [e', Null_eq_empty] at hxB
    exact Set.notMem_empty x hxB
  · rintro ⟨B, hB, hne⟩
    have : B ≠ Λ := hne
    rw [Ne, eqΛ] at this
    push Not at this
    obtain ⟨x, hx⟩ := this
    exact ⟨Λ, B, segSer_anc_iff.2 ⟨⟨hΛ, hB⟩, x, hx, by rw [Null_eq_empty]; exact Set.notMem_empty x⟩⟩
  · rintro ⟨B, hB, hne⟩ h1
    obtain ⟨b, hb⟩ := mem_one_iff.1 h1
    exact hne (((hb B).1 hB).trans ((hb Λ).1 hΛ).symm)
  · intro h1
    obtain ⟨B, hB, hne⟩ := not_one h1 hΛ
    exact ⟨B, hB, hne⟩
  · intro h1
    by_contra hP
    apply h1
    refine mem_one_iff.2 ⟨Λ, fun A => ⟨fun hA => ?_, fun e => e ▸ hΛ⟩⟩
    rw [eqΛ]
    intro x hx
    exact hP (rEx_of_fld (hA.1 hx))

/-- ✱212·171. \[\begin{align}&\vdash .\text{D}ʻ\varsigma ʻP_{*}=\text{sect}ʻP-\iota ʻCʻP.\text{ᗡ}ʻ\varsigma ʻP_{*}=\text{sect}ʻP-\iota ʻ\Lambda \\ &[*212·132.*211·13.*90·14]\end{align}\] -/
theorem pm212_171 {α : Type u} {P : α → α → Prop} :
    dom (segSer (anc P)) = sect P \ ι (fld P) ∧ codom (segSer (anc P)) = sect P \ ι Λ := by
  constructor
  · ext A
    constructor
    · rintro ⟨B, h⟩
      obtain ⟨⟨hA, hB⟩, x, hxB, hxA⟩ := segSer_anc_iff.1 h
      refine ⟨hA, fun e => hxA ?_⟩
      have e' : A = fld P := e
      rw [e']; exact hB.1 hxB
    · rintro ⟨hA, hne⟩
      have : ¬ fld P ⊆ A := fun h => hne (Set.Subset.antisymm hA.1 h)
      obtain ⟨x, hx, hxA⟩ := Set.not_subset.1 this
      exact ⟨fld P, segSer_anc_iff.2 ⟨⟨hA, pm211_26.1⟩, x, hx, hxA⟩⟩
  · ext B
    constructor
    · rintro ⟨A, h⟩
      obtain ⟨⟨-, hB⟩, x, hxB, -⟩ := segSer_anc_iff.1 h
      refine ⟨hB, fun e => ?_⟩
      have e' : B = Λ := e
      rw [e', Null_eq_empty] at hxB
      exact Set.notMem_empty x hxB
    · rintro ⟨hB, hne⟩
      have : B ≠ Λ := hne
      rw [Ne, eqΛ] at this
      push Not at this
      obtain ⟨x, hx⟩ := this
      exact ⟨Λ, segSer_anc_iff.2 ⟨⟨pm211_44.2, hB⟩, x, hx,
        by rw [Null_eq_empty]; exact Set.notMem_empty x⟩⟩

/-- ✱212·172. \[\begin{align}&\vdash :\dot{\exists} !P.\supset .Cʻ\varsigma ʻP_{*}=\text{sect}ʻP.Bʻ\varsigma ʻP_{*}=\Lambda .Bʻ\text{Cnv}ʻ\varsigma ʻP_{*}=CʻP\\ &[*212·133.*211·13.*90·141]\end{align}\] -/
theorem pm212_172 {α : Type u} {P : α → α → Prop} :
    rEx P → (fld (segSer (anc P)) = sect P ∧ Desc Beg (segSer (anc P)) (fun b => b = Λ)) ∧
      Desc Beg (segSer (anc P))˘ (fun b => b = fld P) := by
  rintro ⟨a, b, hab⟩
  have hne : fld P ≠ Λ := by
    intro e
    have : a ∈ fld P := fld_l hab
    rw [e, Null_eq_empty] at this
    exact Set.notMem_empty a this
  obtain ⟨hd, hcd⟩ := pm212_171 (P := P)
  have hfld : fld (segSer (anc P)) = sect P := by
    rw [fld_eq_dom_union_codom, hd, hcd]
    ext A
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      by_cases e : A = Λ
      · refine Or.inl ⟨h, fun e' => hne ?_⟩
        have e'' : A = fld P := e'
        rw [← e'', e]
      · exact Or.inr ⟨h, e⟩
  refine ⟨⟨hfld, desc_of (fun c => ?_) rfl⟩, desc_of (fun c => ?_) rfl⟩
  · show c ∈ dom (segSer (anc P)) \ codom (segSer (anc P)) ↔ c = Λ
    rw [hd, hcd]
    constructor
    · rintro ⟨⟨hc, -⟩, h⟩
      by_contra hc'
      exact h ⟨hc, hc'⟩
    · rintro rfl
      exact ⟨⟨pm211_44.2, fun e => hne (show Λ = fld P from e).symm⟩, fun h => h.2 rfl⟩
  · show c ∈ codom (segSer (anc P)) \ dom (segSer (anc P)) ↔ c = fld P
    rw [hd, hcd]
    constructor
    · rintro ⟨⟨hc, -⟩, h⟩
      by_contra hc'
      exact h ⟨hc, hc'⟩
    · rintro rfl
      exact ⟨⟨pm211_26.1, hne⟩, fun h => h.2 rfl⟩

/-- ✱212·173. \[\begin{align}&\vdash :\alpha \in Cʻ\varsigma ʻP_{*}.\equiv .\alpha \in \text{sect}ʻP.\dot{\exists} !P.\equiv .\alpha \in \text{sect}ʻP.\text{sect}ʻP{\sim}\in 1\\ &[*212·141·142·14.*211·13]\end{align}\] -/
theorem pm212_173 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (A ∈ fld (segSer (anc P)) ↔ A ∈ sect P ∧ rEx P) ∧
      (A ∈ sect P ∧ rEx P ↔ A ∈ sect P ∧ sect P ∉ one) := by
  constructor
  · constructor
    · intro h
      have hP : rEx P := pm212_17.2.1 (pm212_17.1.2.1 (pm212_17.1.1.1 (rEx_of_fld h)))
      rw [(pm212_172 hP).1.1] at h
      exact ⟨h, hP⟩
    · rintro ⟨h, hP⟩
      rw [(pm212_172 hP).1.1]
      exact h
  · rw [pm212_17.2]

/-- ✱212·18. \(\vdash.\varsigmaʻ\breve{P}_{*}=(CʻP-)^{;}\text{Cnv}ʻ\varsigma ʻP_{*}\) -/
theorem pm212_18 {α : Type u} {P : α → α → Prop} :
    segSer (anc P˘) = opL (· \ ·) (fld P) ⁏ (segSer (anc P))˘ := by
  funext A B
  apply propext
  rw [semi_apply, segSer_anc_iff]
  constructor
  · rintro ⟨⟨hA, hB⟩, x, hxB, hxA⟩
    have hAf : A ⊆ fld P := by rw [← fld_cnv P]; exact hA.1
    have hBf : B ⊆ fld P := by rw [← fld_cnv P]; exact hB.1
    have hA' : fld P \ A ∈ sect P := by
      have := pm211_7 hA
      rw [fld_cnv] at this
      exact this
    have hB' : fld P \ B ∈ sect P := by
      have := pm211_7 hB
      rw [fld_cnv] at this
      exact this
    refine ⟨fld P \ A, fld P \ B, ⟨(compl_compl' hAf).symm, (compl_compl' hBf).symm⟩, ?_⟩
    exact segSer_anc_iff.2 ⟨⟨hB', hA'⟩, x, ⟨hBf hxB, hxA⟩, fun h => h.2 hxB⟩
  · rintro ⟨z, w, ⟨hA, hB⟩, h⟩
    obtain ⟨⟨hw, hz⟩, x, ⟨hxz, hxw⟩⟩ := segSer_anc_iff.1 (show segSer (anc P) w z from h)
    have hA' : A = fld P \ z := hA
    have hB' : B = fld P \ w := hB
    rw [hA', hB']
    refine ⟨⟨pm211_7 hz, pm211_7 hw⟩, x, ⟨hz.1 hxz, hxw⟩, fun h' => h'.2 hxz⟩

/-- ✱212·181. \(\vdash .(\varsigma ʻ\breve{P} _{*})\,\text{smor}\,(\text{Cnv}ʻ\varsigma ʻP_{*}) \quad[*212·18]\) -/
theorem pm212_181 {α : Type u} {P : α → α → Prop} :
    smor (segSer (anc P˘)) (segSer (anc P))˘ := by
  let Q := (segSer (anc P))˘
  have hfQ : ∀ z, z ∈ fld Q → z ⊆ fld P := by
    rintro z ⟨w, h | h⟩
    · exact ((segSer_anc_iff.1 (show segSer (anc P) w z from h)).1.2).1
    · exact ((segSer_anc_iff.1 (show segSer (anc P) z w from h)).1.1).1
  refine ⟨opL (· \ ·) (fld P) ↾ fld Q, ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨hx, -⟩, ⟨hy, -⟩⟩
    exact (show x = fld P \ z from hx).trans (show y = fld P \ z from hy).symm
  · rintro x y z ⟨⟨hy, hyQ⟩, ⟨hz, hzQ⟩⟩
    have hy' : x = fld P \ y := hy
    have hz' : x = fld P \ z := hz
    rw [← compl_compl' (hfQ y hyQ), ← compl_compl' (hfQ z hzQ), ← hy', ← hz']
  · ext z
    exact ⟨fun h => ⟨fld P \ z, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  · rw [pm212_18]
    funext A B
    apply propext
    rw [semi_apply, semi_apply]
    constructor
    · rintro ⟨z, w, ⟨hA, hB⟩, h⟩
      exact ⟨z, w, ⟨⟨hA, w, Or.inl h⟩, ⟨hB, z, Or.inr h⟩⟩, h⟩
    · rintro ⟨z, w, ⟨hA, hB⟩, h⟩
      exact ⟨z, w, ⟨hA.1, hB.1⟩, h⟩

/-- ✱212·2. \(\vdash .\text{sgm}ʻP\,\unicode{x2abd}\, \varsigma ʻP.\text{sgm}ʻP\,\unicode{x2abd}\, \varsigma ʻP_{*} \quad[*211·14.*212·1·11·12]\) -/
theorem pm212_2 {α : Type u} {P : α → α → Prop} : sgm P ⪽ segSer P ∧ sgm P ⪽ segSer (anc P) := by
  constructor
  · exact pm212_2_aux
  · intro A B h
    obtain ⟨⟨hA, hB⟩, hne⟩ := pm212_11.1 h
    exact segSer_anc_iff.2 ⟨⟨pm211_14.2 hA, pm211_14.2 hB⟩, hne⟩

/-- ✱212·21. \(\vdash :P\in \text{trans}.\supset .\varsigma ʻP\,\unicode{x2abd}\, \varsigma ʻP_{*} \quad[*211·15.*212·12]\) -/
theorem pm212_21 {α : Type u} {P : α → α → Prop} : P ∈ transR → segSer P ⪽ segSer (anc P) := by
  intro ht A B h
  obtain ⟨⟨hA, h'⟩, hB⟩ := h
  have hA' := sect_of_seg ht hA
  exact segSer_anc_iff.2 ⟨⟨hA', sect_of_seg ht hB⟩, ((Plc_closed hA'.2).1 h').2⟩

/-- ✱212·22. \[\begin{align}&\vdash :P\in \text{connex} .\supset .\text{sgm}ʻP=\hat{\alpha} \hat{\beta} \{\alpha ,\beta \in \text{D}ʻ(P_{\in }\dot{\cap} I).\alpha \subset \beta .\alpha \neq \beta\}\\ &[*211·62.*210·1.*212·11]\end{align}\] -/
theorem pm212_22 {α : Type u} {P : α → α → Prop} :
    P ∈ connex → sgm P = fun A B =>
      ((A ∈ dom (imgRel P ⩀ I) ∧ B ∈ dom (imgRel P ⩀ I)) ∧ A ⊆ B) ∧ A ≠ B :=
  fun hc => (H12_sgm hc).2

/-- ✱212·23. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .\supset .\varsigma ʻP=\hat{\alpha} \hat{\beta} \{\alpha ,\beta \in \text{D}ʻP_{\in }.\alpha \subset \beta .\alpha \neq \beta\}\\ &[*210·13.*211·61.(*212·01)]\end{align}\] -/
theorem pm212_23 {α : Type u} {P : α → α → Prop} :
    P ∈ transR ∩ connex → segSer P = fun A B =>
      ((A ∈ dom (imgRel P) ∧ B ∈ dom (imgRel P)) ∧ A ⊆ B) ∧ A ≠ B :=
  fun h => (H12_seg h).2

/-- ✱212·24. \[\begin{align}&\vdash : P_{*} \in \text{connex} . \supset . \varsigma ʻP_{*} = \hat{\alpha}\hat{\beta} \{\alpha , \beta \in \text{sect}ʻP . \alpha \subset \beta . \alpha \neq \beta\}\\ &[*212·121·22 . *211·13]\end{align}\] -/
theorem pm212_24 {α : Type u} {P : α → α → Prop} :
    anc P ∈ connex → segSer (anc P) = fun A B => ((A ∈ sect P ∧ B ∈ sect P) ∧ A ⊆ B) ∧ A ≠ B := by
  intro hc
  have hn : ∀ C D, C ∈ sect P ∧ D ∈ sect P → C ⊆ D ∨ D ⊆ C := by
    rintro C D ⟨hC, hD⟩
    rw [← sect_anc] at hC hD
    exact pm211_6 ⟨hc, hC, hD⟩
  funext A B
  apply propext
  rw [segSer_anc_iff]
  constructor
  · rintro ⟨⟨hA, hB⟩, h⟩
    exact ⟨⟨⟨hA, hB⟩, ((ssub_iff hn hA hB).2 h).1⟩, ((ssub_iff hn hA hB).2 h).2⟩
  · rintro ⟨⟨⟨hA, hB⟩, h1⟩, h2⟩
    exact ⟨⟨hA, hB⟩, (ssub_iff hn hA hB).1 ⟨h1, h2⟩⟩

/-- ✱212·25. \(\vdash : P \in \text{Ser} . \supset . \overrightarrow{P}^{;}P = (\varsigma ʻP) \unicode{x0294f} \overrightarrow{P}ʻʻCʻP\) -/
theorem pm212_25 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → Rfwd P ⁏ P = segSer P ⥏ Rfwd P ʻʻ fld P := by
  intro hS
  have tr := mem_transR.1 hS.1.2
  have irr := mem_rl_J.1 hS.1.1
  rw [pm212_23 ⟨hS.1.2, hS.2⟩, show Rfwd P = graph (refs P) from rfl]
  funext U V
  apply propext
  rw [semi_graph_apply]
  constructor
  · rintro ⟨x, y, ⟨rfl, rfl⟩, hxy⟩
    refine ⟨⟨⟨x, fld_l hxy, rfl⟩, ⟨⟨pm211_3 ⟨x, fld_l hxy, rfl⟩, pm211_3 ⟨y, fld_r hxy, rfl⟩⟩,
      fun z hz => tr z x y ⟨hz, hxy⟩⟩, fun e => ?_⟩, ⟨y, fld_r hxy, rfl⟩⟩
    have : x ∈ refs P x := by rw [e]; exact hxy
    exact irr x this
  · rintro ⟨⟨⟨x, hx, rfl⟩, ⟨-, hsub⟩, hne⟩, ⟨y, hy, rfl⟩⟩
    refine ⟨x, y, ⟨rfl, rfl⟩, ?_⟩
    rcases mem_connex.1 hS.2 x y ⟨hx, hy⟩ with (h | rfl) | h
    · exact h
    · exact absurd rfl hne
    · exact absurd (Set.Subset.antisymm hsub fun z hz => tr z y x ⟨hz, h⟩) hne

/-- ✱212·3. \[\begin{align}&\vdash : P \in \text{connex} . \supset . \text{sgm}ʻP, \varsigma ʻP_{*} \in \text{Ser}\\ &[*211·67 . *210·14 . *212·121]\end{align}\] -/
theorem pm212_3 {α : Type u} {P : α → α → Prop} :
    P ∈ connex → sgm P ∈ Ser ∧ segSer (anc P) ∈ Ser :=
  fun hc => ⟨pm210_12 (H12_sgm hc), pm210_12 (H12_sect hc)⟩

/-- ✱212·31. \[\begin{align}&\vdash : P \in \text{trans} \cap \text{connex} . \supset . \varsigma ʻP \in \text{Ser}\\ &[*211·68 . *210·14 . (*212·01)]\end{align}\] -/
theorem pm212_31 {α : Type u} {P : α → α → Prop} : P ∈ transR ∩ connex → segSer P ∈ Ser :=
  fun h => pm210_12 (H12_seg h)

/-! ### Helper lemmas for ✱212·32–·55 -/

section H212b

variable {α : Type u} {P : α → α → Prop}

private theorem H2_sect (hc : P ∈ connex) (hP : rEx P) :
    ((∀ C D, C ∈ sect P ∧ D ∈ sect P → C ⊆ D ∨ D ⊆ C) ∧
      segSer (anc P) = (fun C D => ((C ∈ sect P ∧ D ∈ sect P) ∧ C ⊆ D) ∧ C ≠ D)) ∧
      sect P ∉ one :=
  ⟨H12_sect hc, (pm211_66 hP).1⟩

private theorem H2_seg (h : P ∈ transR ∩ connex) (hP : rEx P) :
    ((∀ C D, C ∈ dom (imgRel P) ∧ D ∈ dom (imgRel P) → C ⊆ D ∨ D ⊆ C) ∧
      segSer P = (fun C D => ((C ∈ dom (imgRel P) ∧ D ∈ dom (imgRel P)) ∧ C ⊆ D) ∧ C ≠ D)) ∧
      dom (imgRel P) ∉ one :=
  ⟨H12_seg h, (pm211_66 hP).2⟩

private theorem H2_sgm (hc : P ∈ connex) (hs : rEx (sgm P)) :
    ((∀ C D, C ∈ dom (imgRel P ⩀ I) ∧ D ∈ dom (imgRel P ⩀ I) → C ⊆ D ∨ D ⊆ C) ∧
      sgm P = (fun C D => ((C ∈ dom (imgRel P ⩀ I) ∧ D ∈ dom (imgRel P ⩀ I)) ∧ C ⊆ D) ∧ C ≠ D)) ∧
      dom (imgRel P ⩀ I) ∉ one :=
  ⟨H12_sgm hc, pm212_153.2.1 (pm212_153.1.1 hs)⟩

private theorem fld_sgm_sub {β : Type v} {X : β → β → Prop} {L : Set β} (h : L ∈ fld (sgm X)) :
    L ∈ dom (imgRel X ⩀ I) := by
  obtain ⟨M, h | h⟩ := h
  · exact h.1.1
  · exact h.2

private theorem rEx_of_sgm_fld {β : Type v} {X : β → β → Prop} {L : Set β}
    (h : L ∈ fld (sgm X)) : rEx X := by
  obtain ⟨M, h | h⟩ := h
  · obtain ⟨⟨-, hM⟩, x, hx, -⟩ := pm212_11.1 h
    exact rEx_of_fld ((pm211_14.2 hM).1 hx)
  · obtain ⟨⟨-, hL⟩, x, hx, -⟩ := pm212_11.1 h
    exact rEx_of_fld ((pm211_14.2 hL).1 hx)

end H212b

/-- ✱212·32. \[\begin{align}&\vdash : P \in \text{connex} . \dot{\exists} ! P . \lambda \in \text{sect}ʻP . sʻ\lambda \in \lambda . \supset . sʻ\lambda = \text{max}(\varsigma ʻP_{*})ʻ\lambda \\ &[*210·211.*211·67.*212·17]\end{align}\]

**Status.** proved (reading): the e-text prints `λ ∈ sect'P` for `λ ⊂ sect'P` (as in ✱212·321·322; `s'λ` and `max(ς'P_*)'λ` require `λ` to be a class of sections). -/
theorem pm212_32 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ connex ∧ rEx P) ∧ L ⊆ sect P) ∧ sumCls L ∈ L →
      Desc (maxP (segSer (anc P))) L (fun A => sumCls L = A) := by
  rintro ⟨⟨⟨hc, hP⟩, hL⟩, hs⟩
  exact desc_symm (pm210_211 ⟨⟨H2_sect hc hP, hL⟩, hs⟩)

/-- ✱212·321. \[\begin{align}\vdash : P \in \text{connex} . \dot{\exists} ! P . \lambda \subset \text{sect}ʻP . sʻ\lambda {\sim} \in \lambda . \supset . sʻ\lambda &= \text{seq}(\varsigma ʻP_{*})ʻ\lambda \\ &= \text{lt}(\varsigma ʻP_{*})ʻ\lambda \\ [*210·231 . *211·67 . *212·17 . *211·63]\end{align}\] -/
theorem pm212_321 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ connex ∧ rEx P) ∧ L ⊆ sect P) ∧ sumCls L ∉ L →
      Desc (seqP (segSer (anc P))) L (fun A => sumCls L = A) ∧
        Desc (seqP (segSer (anc P))) L (fun A => Desc (ltP (segSer (anc P))) L (fun B => A = B)) := by
  rintro ⟨⟨⟨hc, hP⟩, hL⟩, hs⟩
  exact pm210_231 ⟨⟨H2_sect hc hP, hL⟩, ⟨pm211_63 hL, hs⟩⟩

/-- ✱212·322. \[\begin{align}&\vdash : P \in \text{connex} . \dot{\exists} ! P . \lambda \subset \text{sect}ʻP . \supset . sʻ\lambda = \text{limax}(\varsigma ʻP_{*})ʻ\lambda \\ &[*212·32·321.*207·46]\end{align}\] -/
theorem pm212_322 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    (P ∈ connex ∧ rEx P) ∧ L ⊆ sect P →
      Desc (limaxP (segSer (anc P))) L (fun A => sumCls L = A) := by
  rintro ⟨⟨hc, hP⟩, hL⟩
  exact pm210_233 ⟨⟨H2_sect hc hP, hL⟩, pm211_63 hL⟩

/-- ✱212·33. \[\begin{align}\vdash : P \in \text{connex} . \dot{\exists} ! P . \lambda \subset \text{sect}ʻP . &pʻ\lambda \cap CʻP \in \lambda . \supset .\\ pʻ\lambda \cap CʻP = \text{min}(\varsigma ʻP_{*})ʻ\lambda\end{align}\] -/
theorem pm212_33 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ connex ∧ rEx P) ∧ L ⊆ sect P) ∧ prodCls L ∩ fld P ∈ L →
      Desc (minP (segSer (anc P))) L (fun A => prodCls L ∩ fld P = A) := by
  rintro ⟨⟨⟨hc, hP⟩, hL⟩, hp⟩
  have e : prodCls L ∩ fld P = prodCls L :=
    Set.inter_eq_left.2 fun x hx => (hL hp).1 (hx _ hp)
  rw [e] at hp ⊢
  exact desc_symm (pm210_21 ⟨⟨H2_sect hc hP, hL⟩, hp⟩)

/-- ✱212·331. \[\begin{align}\vdash :P\in \text{connex} .\dot{\exists} !P.\lambda \subset \text{sect}ʻP.&pʻ\lambda \cap CʻP{\sim}\in \lambda .\supset .\\ &pʻ\lambda \cap CʻP = \text{prec} (\varsigma ʻP_{*})ʻ\lambda = \text{tl}(\varsigma ʻP_{*})ʻ\lambda\end{align}\] -/
theorem pm212_331 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ connex ∧ rEx P) ∧ L ⊆ sect P) ∧ prodCls L ∩ fld P ∉ L →
      Desc (precP (segSer (anc P))) L (fun A => prodCls L ∩ fld P = A) ∧
        Desc (precP (segSer (anc P))) L (fun A => Desc (tlP (segSer (anc P))) L (fun B => A = B)) := by
  rintro ⟨⟨⟨hc, hP⟩, hL⟩, hp⟩
  obtain ⟨hn, hQ⟩ := H12_sect hc
  rw [show segSer (anc P) = incl (sect P) from hQ]
  have h1 := (pm211_66 hP).1
  have hpL : prodCls L ∉ L := by
    intro h
    apply hp
    have e : prodCls L ∩ fld P = prodCls L :=
      Set.inter_eq_left.2 fun x (hx : x ∈ prodCls L) => (hL h).1 (hx _ h)
    rw [e]
    exact h
  have hprec := prec_prodsum hn h1 hL hpL (pm211_633 hL)
  rw [pm211_26.2] at hprec
  exact prec_tl_chain hn hL hpL hprec

/-- ✱212·34. \[\begin{align}&\vdash :P\in \text{connex} .\dot{\exists} !P.\lambda \subset \text{sect}ʻP.\supset .pʻ\lambda \cap CʻP = \text{limin}(\varsigma ʻP_{*})ʻ\lambda \\ &[*212·33·331.*207·46]\end{align}\] -/
theorem pm212_34 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    (P ∈ connex ∧ rEx P) ∧ L ⊆ sect P →
      Desc (liminP (segSer (anc P))) L (fun A => prodCls L ∩ fld P = A) := by
  rintro ⟨⟨hc, hP⟩, hL⟩
  have h := (pm210_252 ⟨H2_sect hc hP, fun M hM => pm211_633 hM⟩ hL).2
  rw [pm211_26.2] at h
  exact h

/-- ✱212·35. \[\begin{align}&\vdash :P\in \text{connex} .\dot{\exists} !P.\supset .\\ &(\lambda ).\lambda \in \{\text{ᗡ}ʻ\text{max}(\varsigma ʻP_{*})\cup \text{ᗡ}ʻ\text{seq}(\varsigma ʻP_{*})\}\cap \{\text{ᗡ}ʻ\text{min}(\varsigma ʻP_{*})\cup \text{ᗡ}ʻ\text{prec}(\varsigma ʻP_{*})\}\\ &[*210·28.*211·671.*212·121]\end{align}\] -/
theorem pm212_35 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ∧ rEx P → ∀ L, L ∈ (codom (maxP (segSer (anc P))) ∪ codom (seqP (segSer (anc P)))) ∩
      (codom (minP (segSer (anc P))) ∪ codom (precP (segSer (anc P)))) := by
  rintro ⟨hc, hP⟩
  exact pm210_282 ⟨H2_sect hc hP, fun M hM => pm211_633 hM⟩

/-- ✱212·36. \(\vdash \colon\ldotp P\in \text{connex} .\supset :\lambda \in Cʻ\text{sgm}ʻ\varsigma ʻP_{*}.\supset .\text{E}!\text{seq}(\varsigma ʻP_{*})ʻ\lambda\) -/
theorem pm212_36 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    P ∈ connex → (L ∈ fld (sgm (segSer (anc P))) → EDesc (seqP (segSer (anc P))) L) := by
  intro hc hL
  have hS := (pm212_3 hc).2
  have hP : rEx P := pm212_17.2.1 (pm212_17.1.2.1 (pm212_17.1.1.1 (rEx_of_sgm_fld hL)))
  have hDI := fld_sgm_sub hL
  rcases (pm212_35 ⟨hc, hP⟩ L).1 with h | h
  · exact absurd h (pm211_4 hDI)
  · exact (edesc_iff_ex fun a b ha hb => seq_unique hS.2 ha hb).2 h

/-- ✱212·4. \[\begin{align}&\vdash :P\in \text{trans} \cap \text{connex} .\dot{\exists} !P.\lambda \subset \text{D}ʻP_{\in }.sʻ\lambda \in \lambda .\supset .sʻ\lambda = \text{max}(\varsigma ʻP)ʻ\lambda\\ &[*211·68·66.*210·211]\end{align}\] -/
theorem pm212_4 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ transR ∩ connex ∧ rEx P) ∧ L ⊆ dom (imgRel P)) ∧ sumCls L ∈ L →
      Desc (maxP (segSer P)) L (fun A => sumCls L = A) := by
  rintro ⟨⟨⟨h, hP⟩, hL⟩, hs⟩
  exact desc_symm (pm210_211 ⟨⟨H2_seg h hP, hL⟩, hs⟩)

/-- ✱212·401. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .\dot{\exists} !P.\lambda \subset \text{D}ʻ&P_{\in }.sʻ\lambda {\sim}\in \lambda .\supset .\\ &sʻ\lambda = \text{seq}(\varsigma ʻP)ʻ\lambda = \text{lt}(\varsigma ʻP)ʻ\lambda \\ [*211·68·66·64.*210·231]\end{align}\] -/
theorem pm212_401 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ transR ∩ connex ∧ rEx P) ∧ L ⊆ dom (imgRel P)) ∧ sumCls L ∉ L →
      Desc (seqP (segSer P)) L (fun A => sumCls L = A) ∧
        Desc (seqP (segSer P)) L (fun A => Desc (ltP (segSer P)) L (fun B => A = B)) := by
  rintro ⟨⟨⟨h, hP⟩, hL⟩, hs⟩
  exact pm210_231 ⟨⟨H2_seg h hP, hL⟩, ⟨pm211_64 hL, hs⟩⟩

/-- ✱212·402. \[\begin{align}&\vdash :P\in \text{trans} \cap \text{connex} .\dot{\exists} !P.\lambda \subset \text{D}ʻP_{\in }.\supset .sʻ\lambda = \text{limax}(\varsigma ʻP)ʻ\lambda \\ &[*212·4·401.*207·46]\end{align}\] -/
theorem pm212_402 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    (P ∈ transR ∩ connex ∧ rEx P) ∧ L ⊆ dom (imgRel P) →
      Desc (limaxP (segSer P)) L (fun A => sumCls L = A) := by
  rintro ⟨⟨h, hP⟩, hL⟩
  exact pm210_233 ⟨⟨H2_seg h hP, hL⟩, pm211_64 hL⟩

/-- ✱212·41. \[\begin{align}&\vdash :P\in \text{trans} \cap \text{connex} .\dot{\exists} !P.\lambda \subset \text{D}ʻP_{\in }.pʻ\lambda \in \lambda .\supset .pʻ\lambda = \text{min}(\varsigma ʻP)ʻ\lambda \\ &[*211·68·66.*210·21]\end{align}\] -/
theorem pm212_41 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ transR ∩ connex ∧ rEx P) ∧ L ⊆ dom (imgRel P)) ∧ prodCls L ∈ L →
      Desc (minP (segSer P)) L (fun A => prodCls L = A) := by
  rintro ⟨⟨⟨h, hP⟩, hL⟩, hp⟩
  exact desc_symm (pm210_21 ⟨⟨H2_seg h hP, hL⟩, hp⟩)

/-- ✱212·411. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .\dot{\exists} !P.\lambda \subset \text{D}ʻ&P_{\in }.pʻ\lambda \in \text{D}ʻP_{\in }-\lambda .\supset .\\ &pʻ\lambda = \text{prec}(\varsigma ʻP)ʻ\lambda = \text{tl}(\varsigma ʻP)ʻ\lambda \\ [*211·68·66.*210·23]\end{align}\] -/
theorem pm212_411 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ transR ∩ connex ∧ rEx P) ∧ L ⊆ dom (imgRel P)) ∧ prodCls L ∈ dom (imgRel P) \ L →
      Desc (precP (segSer P)) L (fun A => prodCls L = A) ∧
        Desc (precP (segSer P)) L (fun A => Desc (tlP (segSer P)) L (fun B => A = B)) := by
  rintro ⟨⟨⟨h, hP⟩, hL⟩, hp⟩
  exact pm210_23 ⟨⟨H2_seg h hP, hL⟩, hp⟩

/-- ✱212·42. \[\begin{align}&\vdash :P\in \text{trans} \cap \text{connex} .\dot{\exists} !P.\lambda \subset \text{D}ʻP_{\in }.pʻ\lambda {\sim}\in \lambda .\supset .\\ &sʻ(\text{D}ʻP_{\in }\cap \text{Cl}ʻpʻ\lambda ) = \text{prec}(\varsigma ʻP)ʻ\lambda = \text{tl}(\varsigma ʻP)ʻ\lambda \\ &[*210·26·22.*211·68·66·64]\end{align}\] -/
theorem pm212_42 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ transR ∩ connex ∧ rEx P) ∧ L ⊆ dom (imgRel P)) ∧ prodCls L ∉ L →
      Desc (precP (segSer P)) L (fun A => sumCls (dom (imgRel P) ∩ cl (prodCls L)) = A) ∧
        Desc (precP (segSer P)) L (fun A => Desc (tlP (segSer P)) L (fun B => A = B)) := by
  rintro ⟨⟨⟨h, hP⟩, hL⟩, hp⟩
  obtain ⟨hn, hQ⟩ := H12_seg h
  rw [show segSer P = incl (dom (imgRel P)) from hQ]
  have h1 := (pm211_66 hP).2
  exact prec_tl_chain hn hL hp (prec_eq_of hn h1 hL hp (pm211_64 fun A hA => hA.1))

/-- ✱212·421. \[\begin{align}\vdash : P \in \text{trans} \cap \text{connex} . \dot{\exists} ! P . \lambda \subset \text{D}ʻ&P_{\in } . pʻ\lambda {\sim} \in \text{D}ʻP_{\in } . \supset .\\ &sʻ(\text{D}ʻP_{\in } \cap \text{Cl}ʻpʻ\lambda ) = Pʻʻpʻ\lambda\end{align}\] -/
theorem pm212_421 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ transR ∩ connex ∧ rEx P) ∧ L ⊆ dom (imgRel P)) ∧ prodCls L ∉ dom (imgRel P) →
      sumCls (dom (imgRel P) ∩ cl (prodCls L)) = P ʻʻ prodCls L := by
  rintro ⟨⟨⟨⟨ht, hc⟩, -⟩, hL⟩, hp⟩
  have hsect : ∀ B, B ∈ L → B ∈ sect P := fun B hB => sect_of_seg ht (hL hB)
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨G, ⟨hG, hGp⟩, hxG⟩ := hx
    have hGs := sect_of_seg ht hG
    rw [pm211_312 ⟨⟨ht, hc⟩, hG⟩] at hxG
    obtain ⟨y, hy, hxy⟩ := hxG
    refine ⟨y, ?_, hxy⟩
    rcases hy with hy | hy
    · exact hGp hy
    · intro B hB
      have hGB : G ⊆ B := fun z hz => hGp hz B hB
      have hne : ¬ B ⊆ G := by
        intro hBG
        apply hp
        have e : prodCls L = G :=
          Set.Subset.antisymm (fun z hz => hBG (hz B hB)) (fun z hz => hGp hz)
        rw [e]
        exact hG
      obtain ⟨z, hzB, hzG⟩ := Set.not_subset.1 hne
      have hzf : z ∈ fld P := (hsect B hB).1 hzB
      have hyf : y ∈ fld P := (seqP_iff.1 hy).1.2
      rcases mem_connex.1 hc y z ⟨hyf, hzf⟩ with (h | h) | h
      · exact sect_closed (hsect B hB) h hzB
      · rw [h]; exact hzB
      · exact absurd h ((seqP_iff.1 hy).2 z
          (fun w hw => follow_of_sect hc hGs hzf hzG hw.1))
  · have hsub : P ʻʻ prodCls L ⊆ prodCls L := by
      rintro y ⟨z, hz, hyz⟩ B hB
      exact sect_closed (hsect B hB) hyz (hz B hB)
    exact ⟨P ʻʻ prodCls L, ⟨⟨prodCls L, rfl⟩, hsub⟩, hx⟩

/-- ✱212·43. \[\begin{align}\vdash : P \in \text{trans} \cap &\text{connex} . \dot{\exists} ! P . \lambda \subset \text{D}ʻP_{\in } . pʻ\lambda {\sim} \in \text{D}ʻP_{\in } . \supset .\\ &Pʻʻpʻ\lambda = \text{prec}(\varsigma ʻP)ʻ\lambda = \text{tl}(\varsigma ʻP)ʻ\lambda \quad[*212·42·421]\end{align}\] -/
theorem pm212_43 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ transR ∩ connex ∧ rEx P) ∧ L ⊆ dom (imgRel P)) ∧ prodCls L ∉ dom (imgRel P) →
      Desc (precP (segSer P)) L (fun A => P ʻʻ prodCls L = A) ∧
        Desc (precP (segSer P)) L (fun A => Desc (tlP (segSer P)) L (fun B => A = B)) := by
  intro h
  have hpL : prodCls L ∉ L := fun h' => h.2 (h.1.2 h')
  have h2 := pm212_42 ⟨h.1, hpL⟩
  rw [pm212_421 h] at h2
  exact h2

/-- ✱212·431. \[\begin{align}\vdash : P \in \text{trans} \cap \text{connex} . \dot{\exists} ! P . \lambda &\subset \text{D}ʻP_{\in } . \supset .\\ &sʻ(\text{D}ʻP_{\in } \cap \text{Cl}ʻpʻ\lambda ) = \text{limin}(\varsigma ʻP)ʻ\lambda\end{align}\] -/
theorem pm212_431 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    (P ∈ transR ∩ connex ∧ rEx P) ∧ L ⊆ dom (imgRel P) →
      Desc (liminP (segSer P)) L (fun A => sumCls (dom (imgRel P) ∩ cl (prodCls L)) = A) := by
  rintro ⟨⟨h, hP⟩, hL⟩
  obtain ⟨hn, hQ⟩ := H12_seg h
  rw [show segSer P = incl (dom (imgRel P)) from hQ]
  have h1 := (pm211_66 hP).2
  refine desc_of (fun A => ?_) rfl
  by_cases hpL : prodCls L ∈ L
  · rw [sum_cl_prod (hL hpL)]
    have hmin := min_eq_of hn h1 hL hpL
    refine ⟨fun h' => ?_, fun h' => Or.inl ((hmin A).2 h')⟩
    rcases h' with h' | h'
    · exact (hmin A).1 h'
    · exact absurd ⟨_, (hmin _).2 rfl⟩ h'.2
  · have hprec := prec_eq_of hn h1 hL hpL (pm211_64 fun A hA => hA.1)
    have hnm := nomin_of hn hL hpL
    refine ⟨fun h' => ?_, fun h' => Or.inr ⟨(hprec A).2 h', hnm⟩⟩
    rcases h' with h' | h'
    · exact absurd ⟨A, h'⟩ hnm
    · exact (hprec A).1 h'.1

/-- ✱212·44. \[\begin{align}\vdash : &P \in \text{trans} \cap \text{connex} . \dot{\exists} ! P . \supset .\\ &(\lambda ) . \lambda \in \{\text{ᗡ}ʻ\text{max}(\varsigma ʻP) \cup \text{ᗡ}ʻ\text{seq}(\varsigma ʻP)\} \cap \{\text{ᗡ}ʻ\text{min}(\varsigma ʻP) \cup \text{ᗡ}ʻ\text{prec}(\varsigma ʻP)\}\\ &[*211·681.*210·28]\end{align}\] -/
theorem pm212_44 {α : Type u} {P : α → α → Prop} :
    P ∈ transR ∩ connex ∧ rEx P → ∀ L, L ∈ (codom (maxP (segSer P)) ∪ codom (seqP (segSer P))) ∩
      (codom (minP (segSer P)) ∪ codom (precP (segSer P))) := by
  rintro ⟨h, hP⟩
  refine pm210_28 ⟨H2_seg h hP, fun A ⟨M, hM, e⟩ => ?_⟩
  rw [show A = sumCls M from e]
  exact pm211_64 hM

/-- ✱212·45. \(\vdash \colon\ldotp P\in \text{trans}\cap \text{connex} .\supset :\lambda \in Cʻ\text{sgm}ʻ\varsigma ʻP.\supset .\text{E}!\text{seq}(\varsigma ʻP)ʻ\lambda \) -/
theorem pm212_45 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    P ∈ transR ∩ connex → (L ∈ fld (sgm (segSer P)) → EDesc (seqP (segSer P)) L) := by
  intro h hL
  have hS := pm212_31 h
  have hP : rEx P := pm212_14.2 (rEx_of_sgm_fld hL)
  rcases (pm212_44 ⟨h, hP⟩ L).1 with h' | h'
  · exact absurd h' (pm211_4 (fld_sgm_sub hL))
  · exact (edesc_iff_ex fun a b ha hb => seq_unique hS.2 ha hb).2 h'

/-- ✱212·5. \[\begin{align}\vdash :P\in \text{connex} .\dot{\exists} !\text{sgm}ʻP.\lambda \subset \text{D}ʻ(P_{\in }\dot{\cap} I).&sʻ\lambda \in \lambda .\supset .\\ &sʻ\lambda =\text{max}(\text{sgm}ʻP)ʻ\lambda\end{align}\] -/
theorem pm212_5 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ connex ∧ rEx (sgm P)) ∧ L ⊆ dom (imgRel P ⩀ I)) ∧ sumCls L ∈ L →
      Desc (maxP (sgm P)) L (fun A => sumCls L = A) := by
  rintro ⟨⟨⟨hc, hs⟩, hL⟩, hsL⟩
  exact desc_symm (pm210_211 ⟨⟨H2_sgm hc hs, hL⟩, hsL⟩)

/-- ✱212·501. \[\begin{align}\vdash :P\in \text{connex} .\dot{\exists} !\text{sgm}ʻP.\lambda &\subset \text{D}ʻ(P_{\in }\dot{\cap} I).sʻ\lambda {\sim}\in \lambda .\supset .\\ &sʻ\lambda =\text{seq}(\text{sgm}ʻP)ʻ\lambda =\text{lt}(\text{sgm}ʻP)ʻ\lambda\end{align}\] -/
theorem pm212_501 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ connex ∧ rEx (sgm P)) ∧ L ⊆ dom (imgRel P ⩀ I)) ∧ sumCls L ∉ L →
      Desc (seqP (sgm P)) L (fun A => sumCls L = A) ∧
        Desc (seqP (sgm P)) L (fun A => Desc (ltP (sgm P)) L (fun B => A = B)) := by
  rintro ⟨⟨⟨hc, hs⟩, hL⟩, hsL⟩
  exact pm210_231 ⟨⟨H2_sgm hc hs, hL⟩, ⟨pm211_65 hL, hsL⟩⟩

/-- ✱212·502. \[\begin{align}&\vdash :P\in \text{connex} .\dot{\exists} !\text{sgm}ʻP.\lambda \subset \text{D}ʻ(P_{\in }\dot{\cap} I).\supset .sʻ\lambda =\text{limax}(\text{sgm}ʻP)ʻ\lambda\\ &[*212·5·501]\end{align}\] -/
theorem pm212_502 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    (P ∈ connex ∧ rEx (sgm P)) ∧ L ⊆ dom (imgRel P ⩀ I) →
      Desc (limaxP (sgm P)) L (fun A => sumCls L = A) := by
  rintro ⟨⟨hc, hs⟩, hL⟩
  exact pm210_233 ⟨⟨H2_sgm hc hs, hL⟩, pm211_65 hL⟩

/-- ✱212·51. \[\begin{align}\vdash :P\in \text{connex} .\dot{\exists} !\text{sgm}ʻP.\lambda \subset \text{D}ʻ(P_{\in }\dot{\cap} I).&pʻ\lambda \in \lambda .\supset .\\ &pʻ\lambda =\text{min}(\text{sgm}ʻP)ʻ\lambda \end{align}\] -/
theorem pm212_51 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ connex ∧ rEx (sgm P)) ∧ L ⊆ dom (imgRel P ⩀ I)) ∧ prodCls L ∈ L →
      Desc (minP (sgm P)) L (fun A => prodCls L = A) := by
  rintro ⟨⟨⟨hc, hs⟩, hL⟩, hp⟩
  exact desc_symm (pm210_21 ⟨⟨H2_sgm hc hs, hL⟩, hp⟩)

/-- ✱212·511. \[\begin{align}\vdash :P\in \text{connex} .\dot{\exists} !\text{sgm}ʻP.\lambda &\subset \text{D}ʻ(P_{\in }\dot{\cap} I).pʻ\lambda \in \text{D}ʻ(P_{\in }\dot{\cap} I)-\lambda .\supset .\\ &pʻ\lambda =\text{prec}(\text{sgm}ʻP)ʻ\lambda =\text{tl}(\text{sgm}ʻP)ʻ\lambda\end{align}\] -/
theorem pm212_511 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ connex ∧ rEx (sgm P)) ∧ L ⊆ dom (imgRel P ⩀ I)) ∧ prodCls L ∈ dom (imgRel P ⩀ I) \ L →
      Desc (precP (sgm P)) L (fun A => prodCls L = A) ∧
        Desc (precP (sgm P)) L (fun A => Desc (tlP (sgm P)) L (fun B => A = B)) := by
  rintro ⟨⟨⟨hc, hs⟩, hL⟩, hp⟩
  exact pm210_23 ⟨⟨H2_sgm hc hs, hL⟩, hp⟩

/-- ✱212·52. \[\begin{align}\vdash :P\in &\text{connex} .\dot{\exists} !\text{sgm}ʻP.\lambda \subset \text{D}ʻ(P_{\in }\dot{\cap} I).pʻ\lambda {\sim}\in \lambda .\supset .\\ &sʻ\{\text{D}ʻ(P_{\in }\dot{\cap} I)\cap \text{Cl}ʻpʻ\lambda \}=\text{prec}(\text{sgm}ʻP)ʻ\lambda =\text{tl}(\text{sgm}ʻP)ʻ\lambda\end{align}\] -/
theorem pm212_52 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    ((P ∈ connex ∧ rEx (sgm P)) ∧ L ⊆ dom (imgRel P ⩀ I)) ∧ prodCls L ∉ L →
      Desc (precP (sgm P)) L (fun A => sumCls (dom (imgRel P ⩀ I) ∩ cl (prodCls L)) = A) ∧
        Desc (precP (sgm P)) L (fun A => Desc (tlP (sgm P)) L (fun B => A = B)) := by
  rintro ⟨⟨⟨hc, hs⟩, hL⟩, hp⟩
  obtain ⟨⟨hn, hQ⟩, h1⟩ := H2_sgm hc hs
  rw [show sgm P = incl (dom (imgRel P ⩀ I)) from hQ]
  exact prec_tl_chain hn hL hp (prec_eq_of hn h1 hL hp (pm211_65 fun A hA => hA.1))

/-- ✱212·53. \[\begin{align}\vdash :P\in &\text{connex} .\dot{\exists} !\text{sgm}ʻP.\lambda \subset \text{D}ʻ(P_{\in }\dot{\cap} I).\supset .\\ &sʻ\{\text{D}ʻ(P_{\in }\dot{\cap} I)\cap \text{Cl}ʻpʻ\lambda\}=\text{limin}(\text{sgm}ʻP)ʻ\lambda \quad[*212·51·52]\end{align}\] -/
theorem pm212_53 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    (P ∈ connex ∧ rEx (sgm P)) ∧ L ⊆ dom (imgRel P ⩀ I) →
      Desc (liminP (sgm P)) L (fun A => sumCls (dom (imgRel P ⩀ I) ∩ cl (prodCls L)) = A) := by
  rintro ⟨⟨hc, hs⟩, hL⟩
  obtain ⟨⟨hn, hQ⟩, h1⟩ := H2_sgm hc hs
  rw [show sgm P = incl (dom (imgRel P ⩀ I)) from hQ]
  refine desc_of (fun A => ?_) rfl
  by_cases hpL : prodCls L ∈ L
  · rw [sum_cl_prod (hL hpL)]
    have hmin := min_eq_of hn h1 hL hpL
    refine ⟨fun h' => ?_, fun h' => Or.inl ((hmin A).2 h')⟩
    rcases h' with h' | h'
    · exact (hmin A).1 h'
    · exact absurd ⟨_, (hmin _).2 rfl⟩ h'.2
  · have hprec := prec_eq_of hn h1 hL hpL (pm211_65 fun A hA => hA.1)
    have hnm := nomin_of hn hL hpL
    refine ⟨fun h' => ?_, fun h' => Or.inr ⟨(hprec A).2 h', hnm⟩⟩
    rcases h' with h' | h'
    · exact absurd ⟨A, h'⟩ hnm
    · exact (hprec A).1 h'.1

/-- ✱212·54. \[\begin{align}&\vdash :P\in \text{connex} .\dot{\exists} !\text{sgm}ʻP.\supset .\\ &(\lambda ).\lambda \in \{\text{ᗡ}ʻ\text{max}(\text{sgm}ʻP)\cup \text{ᗡ}ʻ\text{seq}(\text{sgm}ʻP)\}\cap \{\text{ᗡ}ʻ\text{min}(\text{sgm}ʻP)\cap\text{ᗡ}ʻ\text{prec}(\text{sgm}ʻP)\}\end{align}\]

**Status.** proved (reading): the e-text prints `{ᗡ'min(sgm'P) ∩ ᗡ'prec(sgm'P)}` for `{ᗡ'min(sgm'P) ∪ ᗡ'prec(sgm'P)}` (as in ✱212·35·44 and ✱210·28, from which it follows; with `∩` it would fail for `λ = ι'Λ`, which has the minimum `Λ = B'sgm'P` and no precedent). -/
theorem pm212_54 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ∧ rEx (sgm P) → ∀ L, L ∈ (codom (maxP (sgm P)) ∪ codom (seqP (sgm P))) ∩
      (codom (minP (sgm P)) ∪ codom (precP (sgm P))) := by
  rintro ⟨hc, hs⟩
  refine pm210_28 ⟨H2_sgm hc hs, fun A ⟨M, hM, e⟩ => ?_⟩
  rw [show A = sumCls M from e]
  exact pm211_65 hM

/-- ✱212·55. \(\vdash \colon\ldotp P\in \text{connex} .\supset :\lambda \in Cʻ\text{sgm}ʻ\text{sgm}ʻP.\supset .\text{E}!\text{seq}(\text{sgm}ʻP)ʻ\lambda\) -/
theorem pm212_55 {α : Type u} {P : α → α → Prop} {L : Set (Set α)} :
    P ∈ connex → (L ∈ fld (sgm (sgm P)) → EDesc (seqP (sgm P)) L) := by
  intro hc hL
  have hS := (pm212_3 hc).1
  have hs : rEx (sgm P) := rEx_of_sgm_fld hL
  rcases (pm212_54 ⟨hc, hs⟩ L).1 with h' | h'
  · exact absurd h' (pm211_4 (fld_sgm_sub hL))
  · exact (edesc_iff_ex fun a b ha hb => seq_unique hS.2 ha hb).2 h'

/-! ### Helper lemmas for ✱212·6–·667: the segments `P⃗'x` in `ς'P` -/

section H212c

variable {α : Type u} {P : α → α → Prop}

private theorem refs_inj (hS : P ∈ Ser) {x y : α} (hx : x ∈ fld P) (hy : y ∈ fld P)
    (e : refs P x = refs P y) : x = y := by
  have irr := mem_rl_J.1 hS.1.1
  rcases mem_connex.1 hS.2 x y ⟨hx, hy⟩ with (h | h) | h
  · have : x ∈ refs P x := by rw [e]; exact h
    exact absurd this (irr x)
  · exact h
  · have : y ∈ refs P y := by rw [← e]; exact h
    exact absurd this (irr y)

private theorem refs_seg (x : α) : refs P x ∈ dom (imgRel P) := by
  refine ⟨ι x, ?_⟩
  ext y
  exact ⟨fun h => ⟨x, rfl, h⟩, fun ⟨z, hz, h⟩ => (show z = x from hz) ▸ h⟩

private theorem S_refs (hS : P ∈ Ser) {x y : α} (hx : x ∈ fld P) (hy : y ∈ fld P) :
    segSer P (refs P x) (refs P y) ↔ P x y := by
  have tr := mem_transR.1 hS.1.2
  rw [pm212_23 ⟨hS.1.2, hS.2⟩]
  constructor
  · rintro ⟨⟨-, hsub⟩, hne⟩
    rcases mem_connex.1 hS.2 x y ⟨hx, hy⟩ with (h | rfl) | h
    · exact h
    · exact absurd rfl hne
    · exact absurd (Set.Subset.antisymm hsub fun z hz => tr z y x ⟨hz, h⟩) hne
  · intro h
    refine ⟨⟨⟨refs_seg x, refs_seg y⟩, fun z hz => tr z x y ⟨hz, h⟩⟩, fun e => ?_⟩
    have : x ∈ refs P x := by rw [e]; exact h
    exact mem_rl_J.1 hS.1.1 x this

private theorem T_refs (hS : P ∈ Ser) {x y : α} (hx : x ∈ fld P) (hy : y ∈ fld P) :
    (Rfwd P ⁏ P) (refs P x) (refs P y) ↔ P x y := by
  rw [pm212_25 hS]
  constructor
  · rintro ⟨⟨-, h⟩, -⟩
    exact (S_refs hS hx hy).1 h
  · intro h
    exact ⟨⟨⟨x, hx, rfl⟩, (S_refs hS hx hy).2 h⟩, ⟨y, hy, rfl⟩⟩

private theorem T_apply (_hS : P ∈ Ser) {U V : Set α} :
    (Rfwd P ⁏ P) U V ↔ ∃ x y, (U = refs P x ∧ V = refs P y) ∧ P x y :=
  semi_graph_apply (refs P) P U V

private theorem fld_T (_hS : P ∈ Ser) : fld (Rfwd P ⁏ P) = Rfwd P ʻʻ fld P :=
  fld_semi_graph (refs P) P

private theorem fld_S (hP : rEx P) : fld (segSer P) = dom (imgRel P) := (pm212_133 hP).1.1

private theorem img_refs_inj (hS : P ∈ Ser) {X Y : Set α} (hX : X ⊆ fld P) (hY : Y ⊆ fld P)
    (e : Rfwd P ʻʻ X = Rfwd P ʻʻ Y) : X = Y := by
  ext x
  constructor
  · intro hx
    have : refs P x ∈ Rfwd P ʻʻ Y := by rw [← e]; exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := this
    rw [refs_inj hS (hX hx) (hY hy) hxy]; exact hy
  · intro hx
    have : refs P x ∈ Rfwd P ʻʻ X := by rw [e]; exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := this
    rw [refs_inj hS (hY hx) (hX hy) hxy]; exact hy

private theorem img_sub_fld (A : Set α) : P ʻʻ A ⊆ fld P := fun _ ⟨_, _, h⟩ => fld_l h

private theorem refs_sub_fld (x : α) : refs P x ⊆ fld P := fun _ h => fld_l h

/-- For a series, `x = limax_P'α . ≡ . x ∈ C'P . P⃗'x = P''α` (cf. ✱207·51). -/
private theorem limax_char (hS : P ∈ Ser) {A : Set α} (x : α) :
    limaxP P x A ↔ x ∈ fld P ∧ P ʻʻ A = refs P x := by
  have tr := mem_transR.1 hS.1.2
  have irr := mem_rl_J.1 hS.1.1
  have hc := hS.2
  rw [limaxP_iff]
  constructor
  · rintro (h | h)
    · obtain ⟨⟨hxA, hxf⟩, hx'⟩ := maxP_iff.1 h
      refine ⟨hxf, Set.Subset.antisymm (fun y ⟨w, hw, hyw⟩ => ?_) (fun y hy => ⟨x, hxA, hy⟩)⟩
      rcases mem_connex.1 hc w x ⟨fld_r hyw, hxf⟩ with (h' | rfl) | h'
      · exact tr y w x ⟨hyw, h'⟩
      · exact hyw
      · exact absurd h' (hx' w hw)
    · obtain ⟨hs, hnm⟩ := h
      obtain ⟨⟨hs1, hxf⟩, hs3⟩ := seqP_iff.1 hs
      refine ⟨hxf, Set.Subset.antisymm (fun y ⟨w, hw, hyw⟩ => tr y w x ⟨hyw, hs1 w ⟨hw, fld_r hyw⟩⟩)
        (fun y hy => ?_)⟩
      by_contra hyA
      refine hs3 y (fun w hw => ?_) hy
      rcases mem_connex.1 hc w y ⟨hw.2, fld_l hy⟩ with (h' | rfl) | h'
      · exact h'
      · exact absurd (show w ∈ P ʻʻ A from by
          by_contra hw'
          exact hnm ⟨w, maxP_iff.2 ⟨hw, fun z hz hwz => hw' ⟨z, hz, hwz⟩⟩⟩) hyA
      · exact absurd ⟨w, hw.1, h'⟩ hyA
  · rintro ⟨hxf, e⟩
    by_cases hxA : x ∈ A
    · refine Or.inl (maxP_iff.2 ⟨⟨hxA, hxf⟩, fun y hy hxy => irr x ?_⟩)
      have : x ∈ P ʻʻ A := ⟨y, hy, hxy⟩
      rw [e] at this
      exact this
    · have hfol : ∀ w, w ∈ A ∩ fld P → P w x := by
        intro w hw
        rcases mem_connex.1 hc w x ⟨hw.2, hxf⟩ with (h' | rfl) | h'
        · exact h'
        · exact absurd hw.1 hxA
        · have : x ∈ P ʻʻ A := ⟨w, hw.1, h'⟩
          rw [e] at this
          exact absurd this (irr x)
      refine Or.inr ⟨seqP_iff.2 ⟨⟨hfol, hxf⟩, fun z hz hzx => ?_⟩, ?_⟩
      · have : z ∈ P ʻʻ A := by rw [e]; exact hzx
        obtain ⟨w, hw, hzw⟩ := this
        exact irr z (tr z w z ⟨hzw, hz w ⟨hw, fld_r hzw⟩⟩)
      · rintro ⟨m, hm⟩
        obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
        have := hfol m ⟨hmA, hmf⟩
        have hmx : P ʻʻ A = refs P m := by
          refine Set.Subset.antisymm (fun y ⟨w, hw, hyw⟩ => ?_) (fun y hy => ⟨m, hmA, hy⟩)
          rcases mem_connex.1 hc w m ⟨fld_r hyw, hmf⟩ with (h' | rfl) | h'
          · exact tr y w m ⟨hyw, h'⟩
          · exact hyw
          · exact absurd h' (hm' w hw)
        exact hxA (refs_inj hS hmf hxf (hmx.symm.trans e) ▸ hmA)

private theorem limax_unique (hS : P ∈ Ser) {A : Set α} {x y : α} (hx : limaxP P x A)
    (hy : limaxP P y A) : x = y := by
  obtain ⟨hxf, ex⟩ := (limax_char hS x).1 hx
  obtain ⟨hyf, ey⟩ := (limax_char hS y).1 hy
  exact refs_inj hS hxf hyf (ex.symm.trans ey)

/-- `max⃗(ς'P)'P⃗''α = P⃗''max⃗_P'α` (✱212·6, pointwise). -/
private theorem maxS_iff (hS : P ∈ Ser) {A : Set α} (hA : A ⊆ fld P) (U : Set α) :
    maxP (segSer P) U (Rfwd P ʻʻ A) ↔ ∃ x, maxP P x A ∧ U = refs P x := by
  rw [maxP_iff]
  constructor
  · rintro ⟨⟨⟨x, hxA, rfl⟩, -⟩, h⟩
    refine ⟨x, maxP_iff.2 ⟨⟨hxA, hA hxA⟩, fun y hy hxy => h _ ⟨y, hy, rfl⟩ ?_⟩, rfl⟩
    exact (S_refs hS (hA hxA) (hA hy)).2 hxy
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨⟨hxA, hxf⟩, hx'⟩ := maxP_iff.1 hx
    have hP : rEx P := rEx_of_fld hxf
    refine ⟨⟨⟨x, hxA, rfl⟩, by rw [fld_S hP]; exact refs_seg x⟩, ?_⟩
    rintro V ⟨y, hy, rfl⟩ h
    exact hx' y hy ((S_refs hS hxf (hA hy)).1 h)

private theorem lim_S (hS : P ∈ Ser) (hP : rEx P) (A : Set α) :
    ∀ B, limaxP (segSer P) B (Rfwd P ʻʻ A) ↔ B = P ʻʻ A := by
  have hsum : sumCls (Rfwd P ʻʻ A) = P ʻʻ A := by
    ext x
    constructor
    · rintro ⟨U, ⟨y, hy, rfl⟩, hx⟩
      exact ⟨y, hy, hx⟩
    · rintro ⟨y, hy, hx⟩
      exact ⟨refs P y, ⟨y, hy, rfl⟩, hx⟩
  obtain ⟨b, hb, e⟩ := pm212_402 ⟨⟨⟨hS.1.2, hS.2⟩, hP⟩, fun U (hU : U ∈ Rfwd P ʻʻ A) => by
    obtain ⟨y, -, hU⟩ := hU
    rw [show U = refs P y from hU]
    exact refs_seg y⟩
  rw [hsum] at e
  rw [← e] at hb
  exact hb

/-- `lt(ς'P)'P⃗''α = P''α` exactly when `α` has no maximum (✱212·63). -/
private theorem lt_S (hS : P ∈ Ser) (hP : rEx P) {A : Set α} (hA : A ⊆ fld P) (B : Set α) :
    ltP (segSer P) B (Rfwd P ʻʻ A) ↔ B = P ʻʻ A ∧ ¬∃ m, maxP P m A := by
  have hnm : (¬∃ m, maxP P m A) ↔ ¬∃ U, maxP (segSer P) U (Rfwd P ʻʻ A) := by
    constructor
    · rintro h ⟨U, hU⟩
      obtain ⟨x, hx, -⟩ := (maxS_iff hS hA U).1 hU
      exact h ⟨x, hx⟩
    · rintro h ⟨m, hm⟩
      exact h ⟨refs P m, (maxS_iff hS hA _).2 ⟨m, hm, rfl⟩⟩
  rw [hnm, ← lim_S hS hP A B, limaxP_iff]
  constructor
  · intro h
    exact ⟨Or.inr h, h.2⟩
  · rintro ⟨h | h, h'⟩
    · exact absurd ⟨B, h⟩ h'
    · exact h

private theorem lt_char (hS : P ∈ Ser) {A : Set α} (x : α) :
    ltP P x A ↔ (x ∈ fld P ∧ P ʻʻ A = refs P x) ∧ ¬∃ m, maxP P m A := by
  rw [← limax_char hS x, limaxP_iff]
  constructor
  · intro h
    exact ⟨Or.inr h, h.2⟩
  · rintro ⟨h | h, h'⟩
    · exact absurd ⟨x, h⟩ h'
    · exact h

private theorem lt_inter {β : Type v} {X : β → β → Prop} {K : Set β} {U : β} :
    ltP X U K ↔ ltP X U (K ∩ fld X) := by
  have hm : ∀ y, maxP X y K ↔ maxP X y (K ∩ fld X) := by
    intro y
    rw [maxP_iff, maxP_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨h1, h2⟩, h2⟩, fun z hz => h3 z hz.1⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1.1, h2⟩, fun z hz hyz => h3 z ⟨hz, fld_r hyz⟩ hyz⟩
  have hs : seqP X U K ↔ seqP X U (K ∩ fld X) := by
    unfold seqP
    rw [Set.inter_assoc, Set.inter_self]
  rw [ltP_iff, ltP_iff, hs]
  exact and_congr Iff.rfl (not_congr (exists_congr hm))

private theorem seq_congr {A B : Set α} {x : α}
    (h : ∀ z, (∀ y, y ∈ A ∩ fld P → P y z) ↔ (∀ y, y ∈ B ∩ fld P → P y z)) :
    seqP P x A ↔ seqP P x B := by
  rw [seqP_iff, seqP_iff, h]
  exact and_congr Iff.rfl (forall_congr' fun z => imp_congr (h z) Iff.rfl)

/-- For a series and `α ⊂ C'P` with a sequent `s`, `P⃗'s` is the sequent of `P⃗''α` in `ς'P`. -/
private theorem seqS_of (hS : P ∈ Ser) {A : Set α} (hA : A ⊆ fld P) {s : α} (hs : seqP P s A) :
    ∀ B, seqP (segSer P) B (Rfwd P ʻʻ A) ↔ B = refs P s := by
  have tr := mem_transR.1 hS.1.2
  have hc := hS.2
  obtain ⟨⟨hs1, hsf⟩, hs3⟩ := seqP_iff.1 hs
  have hP : rEx P := rEx_of_fld hsf
  have hSS := pm212_31 ⟨hS.1.2, hS.2⟩
  have hseq : seqP (segSer P) (refs P s) (Rfwd P ʻʻ A) := by
    refine seqP_iff.2 ⟨⟨fun V hV => ?_, by rw [fld_S hP]; exact refs_seg s⟩, fun W hW hWs => ?_⟩
    · obtain ⟨⟨y, hy, rfl⟩, -⟩ := hV
      exact (S_refs hS (hA hy) hsf).2 (hs1 y ⟨hy, hA hy⟩)
    · rw [pm212_23 ⟨hS.1.2, hS.2⟩] at hWs
      obtain ⟨⟨⟨hWD, -⟩, hWsub⟩, hWne⟩ := hWs
      have hWs' : W ∈ sect P := sect_of_seg hS.1.2 hWD
      have : ¬ refs P s ⊆ W := fun h => hWne (Set.Subset.antisymm hWsub h)
      obtain ⟨z, hzs, hzW⟩ := Set.not_subset.1 this
      have hzs' : P z s := hzs
      have hnf : ¬ ∀ y, y ∈ A ∩ fld P → P y z := fun h => hs3 z h hzs'
      push Not at hnf
      obtain ⟨y, hy, hyz⟩ := hnf
      have hW' := hW (refs P y) ⟨⟨y, hy.1, rfl⟩, by rw [fld_S hP]; exact refs_seg y⟩
      rw [pm212_23 ⟨hS.1.2, hS.2⟩] at hW'
      obtain ⟨⟨-, hyW⟩, hyne⟩ := hW'
      rcases mem_connex.1 hc y z ⟨hy.2, fld_l hzs'⟩ with (h | rfl) | h
      · exact hyz h
      · have : ¬ W ⊆ refs P y := fun h => hyne (Set.Subset.antisymm hyW h)
        obtain ⟨w, hwW, hwy⟩ := Set.not_subset.1 this
        rcases mem_connex.1 hc w y ⟨hWs'.1 hwW, hy.2⟩ with (h' | rfl) | h'
        · exact hwy h'
        · exact hzW hwW
        · exact hzW (sect_closed hWs' h' hwW)
      · exact hzW (hyW h)
  exact uniq_of (fun B hB => seq_unique hSS.2 hB hseq) hseq

/-- The sequent in `ς'P` of `P⃗''α` corresponds to a sequent of `α`, if it is some `P⃗'w`. -/
private theorem seq_of_S (hS : P ∈ Ser) {A : Set α} (hA : A ⊆ fld P) {w : α} (hw : w ∈ fld P)
    (h : seqP (segSer P) (refs P w) (Rfwd P ʻʻ A)) : seqP P w A := by
  have hP : rEx P := rEx_of_fld hw
  obtain ⟨⟨h1, -⟩, h3⟩ := seqP_iff.1 h
  refine seqP_iff.2 ⟨⟨fun y hy => ?_, hw⟩, fun z hz hzw => ?_⟩
  · exact (S_refs hS hy.2 hw).1 (h1 _ ⟨⟨y, hy.1, rfl⟩, by rw [fld_S hP]; exact refs_seg y⟩)
  · refine h3 (refs P z) (fun V hV => ?_) ((S_refs hS (fld_l hzw) hw).2 hzw)
    obtain ⟨⟨y, hy, rfl⟩, -⟩ := hV
    exact (S_refs hS (hA hy) (fld_l hzw)).2 (hz y ⟨hy, hA hy⟩)

private theorem segSer_rNull (hP : ¬ rEx P) : segSer P = rNull := by
  apply pm212_134
  funext x y
  apply propext
  exact ⟨fun h => absurd ⟨x, y, h⟩ hP, fun h => (rNull_apply _ _ h).elim⟩

private theorem not_max_S_of (hS : P ∈ Ser) {K : Set (Set α)} (hK : K ⊆ dom (imgRel P))
    (h : ¬∃ U, maxP (segSer P) U K) : ¬∃ m, maxP P m (sumCls K) := by
  have hc := hS.2
  rintro ⟨x, hx⟩
  obtain ⟨⟨⟨B, hB, hxB⟩, hxf⟩, hx'⟩ := maxP_iff.1 hx
  have hP : rEx P := rEx_of_fld hxf
  apply h
  refine ⟨B, maxP_iff.2 ⟨⟨hB, by rw [fld_S hP]; exact hK hB⟩, fun C hC hBC => ?_⟩⟩
  rw [pm212_23 ⟨hS.1.2, hS.2⟩] at hBC
  obtain ⟨⟨-, hsub⟩, hne⟩ := hBC
  have hCs : C ∈ sect P := sect_of_seg hS.1.2 (hK hC)
  have hBs : B ∈ sect P := sect_of_seg hS.1.2 (hK hB)
  have : ¬ C ⊆ B := fun h' => hne (Set.Subset.antisymm hsub h')
  obtain ⟨w, hwC, hwB⟩ := Set.not_subset.1 this
  rcases mem_connex.1 hc x w ⟨hxf, hCs.1 hwC⟩ with (h' | rfl) | h'
  · exact hx' w ⟨C, hC, hwC⟩ h'
  · exact hwB hxB
  · exact hwB (sect_closed hBs h' hxB)

private theorem fres_ser {X : α → α → Prop} {B : Set α} (h : X ∈ Ser) : X ⥏ B ∈ Ser := by
  obtain ⟨⟨hJ, ht⟩, hc⟩ := h
  have hf : ∀ x, x ∈ fld (X ⥏ B) → x ∈ B ∧ x ∈ fld X := by
    rintro x ⟨w, h | h⟩
    · exact ⟨h.1.1, fld_l h.1.2⟩
    · exact ⟨h.2, fld_r h.1.2⟩
  refine ⟨⟨mem_rl_J.2 fun x hx => mem_rl_J.1 hJ x hx.1.2,
    mem_transR.2 fun x y z ⟨h1, h2⟩ => ⟨⟨h1.1.1, mem_transR.1 ht x y z ⟨h1.1.2, h2.1.2⟩⟩, h2.2⟩⟩,
    mem_connex.2 fun x y ⟨hx, hy⟩ => ?_⟩
  obtain ⟨hxB, hxf⟩ := hf x hx
  obtain ⟨hyB, hyf⟩ := hf y hy
  rcases mem_connex.1 hc x y ⟨hxf, hyf⟩ with (h | h) | h
  · exact Or.inl (Or.inl ⟨⟨hxB, h⟩, hyB⟩)
  · exact Or.inl (Or.inr h)
  · exact Or.inr ⟨⟨hyB, h⟩, hxB⟩

private theorem not_fld_rNull {β : Type v} {x : β} : x ∉ fld (rNull : β → β → Prop) := by
  rintro ⟨w, h | h⟩ <;> exact rNull_apply _ _ h

private theorem no_limax_rNull {β : Type v} {C : β} {K : Set β} :
    ¬ limaxP (rNull : β → β → Prop) C K := by
  rintro (h | h)
  · exact not_fld_rNull (maxP_iff.1 h).1.2
  · exact not_fld_rNull (seqP_iff.1 h.1).1.2

end H212c

/-- ✱212·6. \[\begin{align}\vdash :P\in \text{Ser}.\alpha \subset Cʻ&P.\supset .\\ &\overrightarrow{\text{max}}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha =\overrightarrow{\text{max}}(\overrightarrow{P}^{;}P)ʻ\overrightarrow{P}ʻʻ\alpha =\overrightarrow{P}ʻʻ\overrightarrow{\text{max}}_{P}ʻ\alpha\end{align}\] -/
theorem pm212_6 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser ∧ A ⊆ fld P →
      refs (maxP (segSer P)) (Rfwd P ʻʻ A) = refs (maxP (Rfwd P ⁏ P)) (Rfwd P ʻʻ A) ∧
        refs (maxP (Rfwd P ⁏ P)) (Rfwd P ʻʻ A) = Rfwd P ʻʻ refs (maxP P) A := by
  rintro ⟨hS, hA⟩
  have hT : ∀ U, maxP (Rfwd P ⁏ P) U (Rfwd P ʻʻ A) ↔ ∃ x, maxP P x A ∧ U = refs P x := by
    intro U
    rw [maxP_iff]
    constructor
    · rintro ⟨⟨⟨x, hxA, rfl⟩, -⟩, h⟩
      refine ⟨x, maxP_iff.2 ⟨⟨hxA, hA hxA⟩, fun y hy hxy => h _ ⟨y, hy, rfl⟩ ?_⟩, rfl⟩
      exact (T_refs hS (hA hxA) (hA hy)).2 hxy
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨⟨hxA, hxf⟩, hx'⟩ := maxP_iff.1 hx
      refine ⟨⟨⟨x, hxA, rfl⟩, by rw [fld_T hS]; exact ⟨x, hxf, rfl⟩⟩, ?_⟩
      rintro V ⟨y, hy, rfl⟩ h
      exact hx' y hy ((T_refs hS hxf (hA hy)).1 h)
  constructor
  · ext U
    exact (maxS_iff hS hA U).trans (hT U).symm
  · ext U
    exact (hT U).trans ⟨fun ⟨x, hx, e⟩ => ⟨x, hx, e⟩, fun ⟨x, hx, e⟩ => ⟨x, hx, e⟩⟩

/-- ✱212·601. \[\begin{align}\vdash \colon\ldotp P\in &\text{Ser}.\alpha \subset CʻP.\supset :\\ &\text{E}!\text{max}_{P}ʻ\alpha .\equiv .\text{E}!\text{max}(\overrightarrow{P}^{;}P)ʻ\overrightarrow{P}ʻʻ\alpha .\equiv .\text{E}!\text{max}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha \\ [*212·6]\end{align}\] -/
theorem pm212_601 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser ∧ A ⊆ fld P →
      (EDesc (maxP P) A ↔ EDesc (maxP (Rfwd P ⁏ P)) (Rfwd P ʻʻ A)) ∧
        (EDesc (maxP (Rfwd P ⁏ P)) (Rfwd P ʻʻ A) ↔ EDesc (maxP (segSer P)) (Rfwd P ʻʻ A)) := by
  intro h
  obtain ⟨e1, e2⟩ := pm212_6 h
  have hc := h.1.2
  constructor
  · rw [edesc_iff_refs, edesc_iff_refs, e2]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨refs P m, ?_⟩
      rw [hm]
      ext U
      exact ⟨fun ⟨y, hy, hU⟩ => (show y = m from hy) ▸ hU, fun hU => ⟨m, rfl, hU⟩⟩
    · rintro ⟨B, hB⟩
      have : B ∈ Rfwd P ʻʻ refs (maxP P) A := by rw [hB]; exact (show B = B from rfl)
      obtain ⟨m, hm, -⟩ := this
      exact ⟨m, Set.ext (uniq_of (fun n hn => max_unique hc hn hm) hm)⟩
  · rw [edesc_iff_refs, edesc_iff_refs, e1]

/-- ✱212·602. \(\vdash \colon\ldotp P\in \text{Ser}.\dot{\exists} !P.\alpha \subset CʻP.\supset :\text{E}!\text{max}_{P}ʻ\alpha .\equiv .Pʻʻ\alpha \in \overrightarrow{P}ʻʻ\alpha\) -/
theorem pm212_602 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ Ser ∧ rEx P) ∧ A ⊆ fld P → (EDesc (maxP P) A ↔ P ʻʻ A ∈ Rfwd P ʻʻ A) := by
  rintro ⟨⟨hS, -⟩, hA⟩
  have irr := mem_rl_J.1 hS.1.1
  rw [edesc_iff_ex fun a b ha hb => max_unique hS.2 ha hb]
  constructor
  · rintro ⟨m, hm⟩
    have hm' := (limax_char hS m).1 (Or.inl hm)
    exact ⟨m, (maxP_iff.1 hm).1.1, hm'.2⟩
  · rintro ⟨x, hxA, e⟩
    have e' : P ʻʻ A = refs P x := e
    refine ⟨x, maxP_iff.2 ⟨⟨hxA, hA hxA⟩, fun y hy hxy => irr x ?_⟩⟩
    have : x ∈ P ʻʻ A := ⟨y, hy, hxy⟩
    rw [e'] at this
    exact this

/-- ✱212·61. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .\dot{\exists} !P.\supset .\text{limax}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha =Pʻʻ\alpha\\ &[*212·402.*40·5]\end{align}\] -/
theorem pm212_61 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR ∩ connex ∧ rEx P →
      Desc (limaxP (segSer P)) (Rfwd P ʻʻ A) (fun B => B = P ʻʻ A) := by
  rintro ⟨h, hP⟩
  have hsum : sumCls (Rfwd P ʻʻ A) = P ʻʻ A := by
    ext x
    constructor
    · rintro ⟨U, ⟨y, hy, rfl⟩, hx⟩
      exact ⟨y, hy, hx⟩
    · rintro ⟨y, hy, hx⟩
      exact ⟨refs P y, ⟨y, hy, rfl⟩, hx⟩
  obtain ⟨b, hb, e⟩ := pm212_402 ⟨⟨h, hP⟩, fun U (hU : U ∈ Rfwd P ʻʻ A) => by
    obtain ⟨y, -, hU⟩ := hU
    rw [show U = refs P y from hU]
    exact refs_seg y⟩
  rw [hsum] at e
  exact ⟨b, hb, e.symm⟩

/-- ✱212·62. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.\dot{\exists} !&P.\supset :\\ &\text{E}!\text{limax}_Pʻ\alpha .\equiv .\text{E}!\text{limax}(\overrightarrow{P}^{;}P)ʻ\overrightarrow{P}ʻʻ\alpha .\\ &\equiv .\text{limax}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha =\overrightarrow{P}ʻ\text{limax}_Pʻ\alpha .\\ &\equiv .\text{limax}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha \in \overrightarrow{P}ʻʻCʻP\end{align}\] -/
theorem pm212_62 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser ∧ rEx P →
      ((EDesc (limaxP P) A ↔ EDesc (limaxP (Rfwd P ⁏ P)) (Rfwd P ʻʻ A)) ∧
        (EDesc (limaxP (Rfwd P ⁏ P)) (Rfwd P ʻʻ A) ↔
          Desc (limaxP (segSer P)) (Rfwd P ʻʻ A)
            (fun B => Desc (limaxP P) A (fun x => B = refs P x)))) ∧
      (Desc (limaxP (segSer P)) (Rfwd P ʻʻ A) (fun B => Desc (limaxP P) A (fun x => B = refs P x)) ↔
        Desc (limaxP (segSer P)) (Rfwd P ʻʻ A) (fun B => B ∈ Rfwd P ʻʻ fld P)) := by
  rintro ⟨hS, hP⟩
  have hTS : (Rfwd P ⁏ P) ∈ Ser := by
    rw [pm212_25 hS]
    exact fres_ser (pm212_31 ⟨hS.1.2, hS.2⟩)
  let E := ∃ x, x ∈ fld P ∧ P ʻʻ A = refs P x
  have h1 : EDesc (limaxP P) A ↔ E := by
    rw [edesc_iff_ex fun a b ha hb => limax_unique hS ha hb]
    exact exists_congr fun x => limax_char hS x
  have hLT : ∀ U, limaxP (Rfwd P ⁏ P) U (Rfwd P ʻʻ A) ↔
      ∃ x, x ∈ fld P ∧ U = refs P x ∧ P ʻʻ A = refs P x := by
    intro U
    rw [limax_char hTS U, fld_T hS]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, e⟩
      refine ⟨x, hx, rfl, img_refs_inj hS (img_sub_fld A) (refs_sub_fld x) ?_⟩
      have e1 : (Rfwd P ⁏ P) ʻʻ (Rfwd P ʻʻ A) = Rfwd P ʻʻ (P ʻʻ A) := by
        ext V
        constructor
        · rintro ⟨W, ⟨a, ha, rfl⟩, hVW⟩
          obtain ⟨z, y, ⟨rfl, hy⟩, hzy⟩ := (T_apply hS).1 hVW
          have : z ∈ refs P a := by rw [hy]; exact hzy
          exact ⟨z, ⟨a, ha, this⟩, rfl⟩
        · rintro ⟨z, ⟨a, ha, hza⟩, rfl⟩
          exact ⟨refs P a, ⟨a, ha, rfl⟩, (T_apply hS).2 ⟨z, a, ⟨rfl, rfl⟩, hza⟩⟩
      have e2 : refs (Rfwd P ⁏ P) (refs P x) = Rfwd P ʻʻ refs P x := by
        ext V
        constructor
        · intro hV
          obtain ⟨z, y, ⟨rfl, hy⟩, hzy⟩ := (T_apply hS).1 hV
          have hy' := refs_inj hS hx (fld_r hzy) hy
          exact ⟨z, by rw [hy']; exact hzy, rfl⟩
        · rintro ⟨z, hzx, rfl⟩
          exact (T_apply hS).2 ⟨z, x, ⟨rfl, rfl⟩, hzx⟩
      rw [← e1, ← e2]
      exact e
    · rintro ⟨x, hx, rfl, e⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      ext V
      constructor
      · rintro ⟨W, ⟨a, ha, rfl⟩, hVW⟩
        obtain ⟨z, y, ⟨rfl, hy⟩, hzy⟩ := (T_apply hS).1 hVW
        have hza' : z ∈ refs P a := by rw [hy]; exact hzy
        have hza : z ∈ P ʻʻ A := ⟨a, ha, hza'⟩
        rw [e] at hza
        exact (T_apply hS).2 ⟨z, x, ⟨rfl, rfl⟩, hza⟩
      · intro hV
        obtain ⟨z, y, ⟨rfl, hy⟩, hzy⟩ := (T_apply hS).1 hV
        have hy' := refs_inj hS hx (fld_r hzy) hy
        rw [← hy'] at hzy
        have : z ∈ P ʻʻ A := by rw [e]; exact hzy
        obtain ⟨a, ha, hza⟩ := this
        exact ⟨refs P a, ⟨a, ha, rfl⟩, (T_apply hS).2 ⟨z, a, ⟨rfl, rfl⟩, hza⟩⟩
  have h2 : EDesc (limaxP (Rfwd P ⁏ P)) (Rfwd P ʻʻ A) ↔ E := by
    constructor
    · intro h
      obtain ⟨U, hU⟩ := exists_of_edesc h
      obtain ⟨x, hx, -, e⟩ := (hLT U).1 hU
      exact ⟨x, hx, e⟩
    · rintro ⟨x, hx, e⟩
      refine ⟨refs P x, fun U => ⟨fun hU => ?_, fun hU => (hLT U).2 ⟨x, hx, hU, e⟩⟩⟩
      obtain ⟨y, -, rfl, e'⟩ := (hLT U).1 hU
      exact e'.symm.trans e
  have hlimS := lim_S hS hP A
  have h3 : Desc (limaxP (segSer P)) (Rfwd P ʻʻ A)
      (fun B => Desc (limaxP P) A (fun x => B = refs P x)) ↔ E := by
    rw [desc_iff_of hlimS]
    constructor
    · rintro ⟨x, hx, e⟩
      exact ⟨x, ((limax_char hS x).1 ((hx x).2 rfl)).1, e⟩
    · rintro ⟨x, hxf, e⟩
      have hx : limaxP P x A := (limax_char hS x).2 ⟨hxf, e⟩
      exact desc_of (uniq_of (fun y hy => limax_unique hS hy hx) hx) e
  have h4 : Desc (limaxP (segSer P)) (Rfwd P ʻʻ A) (fun B => B ∈ Rfwd P ʻʻ fld P) ↔ E := by
    rw [desc_iff_of hlimS]
    exact ⟨fun ⟨x, hx, e⟩ => ⟨x, hx, e⟩, fun ⟨x, hx, e⟩ => ⟨x, hx, e⟩⟩
  rw [h1, h2, h3, h4]
  exact ⟨⟨Iff.rfl, Iff.rfl⟩, Iff.rfl⟩

/-- ✱212·621. \(\vdash \colon\ldotp P\in \text{Ser}.\beta \subset CʻP.\supset :\text{limax}_Pʻ\alpha \in \beta .\equiv .\text{limax}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha \in \overrightarrow{P}ʻʻ\beta\) -/
theorem pm212_621 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    P ∈ Ser ∧ B ⊆ fld P → (Desc (limaxP P) A (fun x => x ∈ B) ↔
      Desc (limaxP (segSer P)) (Rfwd P ʻʻ A) (fun C => C ∈ Rfwd P ʻʻ B)) := by
  rintro ⟨hS, hB⟩
  by_cases hP : rEx P
  · rw [desc_iff_of (lim_S hS hP A)]
    constructor
    · rintro ⟨x, hx, hxB⟩
      have := (limax_char hS x).1 ((hx x).2 rfl)
      exact ⟨x, hxB, this.2⟩
    · rintro ⟨x, hxB, e⟩
      have hx : limaxP P x A := (limax_char hS x).2 ⟨hB hxB, e⟩
      exact desc_of (uniq_of (fun y hy => limax_unique hS hy hx) hx) hxB
  · rw [segSer_rNull hP]
    constructor
    · rintro ⟨x, hx, -⟩
      exact absurd (rEx_of_fld ((limax_char hS x).1 ((hx x).2 rfl)).1) hP
    · rintro ⟨C, hC, -⟩
      exact absurd ((hC C).2 rfl) no_limax_rNull

/-- ✱212·63. \[\begin{align}&\vdash :P\in \text{Ser}.\dot{\exists} !P.\alpha \subset CʻP.{\sim}\text{E}!\text{max}_{P}ʻ\alpha .\supset .\text{lt}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha =Pʻʻ\alpha \\ &[*212·61·601.*207·43]\end{align}\] -/
theorem pm212_63 {α : Type u} {P : α → α → Prop} {A : Set α} :
    ((P ∈ Ser ∧ rEx P) ∧ A ⊆ fld P) ∧ ¬ EDesc (maxP P) A →
      Desc (ltP (segSer P)) (Rfwd P ʻʻ A) (fun B => B = P ʻʻ A) := by
  rintro ⟨⟨⟨hS, hP⟩, hA⟩, hM⟩
  rw [edesc_iff_ex fun a b ha hb => max_unique hS.2 ha hb] at hM
  exact desc_of (fun B => (lt_S hS hP hA B).trans ⟨fun h => h.1, fun h => ⟨h, hM⟩⟩) rfl

/-- ✱212·631. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.\dot{\exists} !P.\alpha \subset CʻP.\supset :\text{E}!\text{lt}_Pʻ\alpha .&\equiv .\text{lt}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha =\overrightarrow{P}ʻ\text{lt}_Pʻ\alpha .\\ &\equiv .\text{lt}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha \in \overrightarrow{P}ʻʻCʻP\end{align}\] -/
theorem pm212_631 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ Ser ∧ rEx P) ∧ A ⊆ fld P →
      (EDesc (ltP P) A ↔ Desc (ltP (segSer P)) (Rfwd P ʻʻ A)
          (fun B => Desc (ltP P) A (fun x => B = refs P x))) ∧
        (Desc (ltP (segSer P)) (Rfwd P ʻʻ A) (fun B => Desc (ltP P) A (fun x => B = refs P x)) ↔
          Desc (ltP (segSer P)) (Rfwd P ʻʻ A) (fun B => B ∈ Rfwd P ʻʻ fld P)) := by
  rintro ⟨⟨hS, hP⟩, hA⟩
  have huP : ∀ a b, ltP P a A → ltP P b A → a = b := fun a b ha hb => limax_unique hS (Or.inr ha) (Or.inr hb)
  by_cases hm : ∃ m, maxP P m A
  · have hnS : ∀ B, ¬ ltP (segSer P) B (Rfwd P ʻʻ A) := fun B h => ((lt_S hS hP hA B).1 h).2 hm
    have hnP : ∀ x, ¬ ltP P x A := fun x h => h.2 hm
    refine ⟨⟨fun h => by obtain ⟨x, hx⟩ := exists_of_edesc h; exact absurd hx (hnP x),
      fun ⟨b, hb, _⟩ => absurd ((hb b).2 rfl) (hnS b)⟩,
      ⟨fun ⟨b, hb, _⟩ => absurd ((hb b).2 rfl) (hnS b), fun ⟨b, hb, _⟩ => absurd ((hb b).2 rfl) (hnS b)⟩⟩
  · have hS' : ∀ B, ltP (segSer P) B (Rfwd P ʻʻ A) ↔ B = P ʻʻ A :=
      fun B => (lt_S hS hP hA B).trans ⟨fun h => h.1, fun h => ⟨h, hm⟩⟩
    have hP' : ∀ x, ltP P x A ↔ x ∈ fld P ∧ P ʻʻ A = refs P x :=
      fun x => (lt_char hS x).trans ⟨fun h => h.1, fun h => ⟨h, hm⟩⟩
    rw [desc_iff_of hS', desc_iff_of hS', edesc_iff_ex huP]
    constructor
    · constructor
      · rintro ⟨x, hx⟩
        exact desc_of (uniq_of (fun y hy => huP y x hy hx) hx) ((hP' x).1 hx).2
      · rintro ⟨x, hx, -⟩
        exact ⟨x, (hx x).2 rfl⟩
    · constructor
      · rintro ⟨x, hx, e⟩
        exact ⟨x, ((hP' x).1 ((hx x).2 rfl)).1, e⟩
      · rintro ⟨x, hxf, e⟩
        have hx : ltP P x A := (hP' x).2 ⟨hxf, e⟩
        exact desc_of (uniq_of (fun y hy => huP y x hy hx) hx) e

/-- ✱212·632. \(\vdash :P\in \text{Ser}.\dot{\exists} !P.\alpha \subset CʻP.Pʻʻ\alpha {\sim}\in \overrightarrow{P}ʻʻCʻP.\supset .Pʻʻ\alpha =\text{lt}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha\) -/
theorem pm212_632 {α : Type u} {P : α → α → Prop} {A : Set α} :
    ((P ∈ Ser ∧ rEx P) ∧ A ⊆ fld P) ∧ P ʻʻ A ∉ Rfwd P ʻʻ fld P →
      Desc (ltP (segSer P)) (Rfwd P ʻʻ A) (fun B => P ʻʻ A = B) := by
  rintro ⟨h, hn⟩
  have hM : ¬ EDesc (maxP P) A := by
    intro hE
    obtain ⟨x, hx, e⟩ := (pm212_602 h).1 hE
    exact hn ⟨x, h.2 hx, e⟩
  exact desc_symm (pm212_63 ⟨h, hM⟩)

/-- ✱212·633. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.\dot{\exists} !P.x\in CʻP.\beta \subset &CʻP.\supset :\\ &x=\text{lt}_Pʻ\beta .\equiv .\overrightarrow{P}ʻx=\text{lt}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\beta\end{align}\] -/
theorem pm212_633 {α : Type u} {P : α → α → Prop} {x : α} {B : Set α} :
    ((P ∈ Ser ∧ rEx P) ∧ x ∈ fld P) ∧ B ⊆ fld P →
      (Desc (ltP P) B (fun y => x = y) ↔ Desc (ltP (segSer P)) (Rfwd P ʻʻ B) (fun C => refs P x = C)) := by
  rintro ⟨⟨⟨hS, hP⟩, hx⟩, hB⟩
  constructor
  · rintro ⟨y, hy, ey⟩
    have hx' : ltP P x B := by rw [ey]; exact (hy y).2 rfl
    obtain ⟨⟨-, e⟩, hm⟩ := (lt_char hS x).1 hx'
    exact desc_of (fun C => (lt_S hS hP hB C).trans ⟨fun h => h.1, fun h => ⟨h, hm⟩⟩) e.symm
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨e, hm⟩ := (lt_S hS hP hB (refs P x)).1 ((hC _).2 rfl)
    have hlt : ltP P x B := (lt_char hS x).2 ⟨⟨hx, e.symm⟩, hm⟩
    exact desc_of (uniq_of (fun y hy => limax_unique hS (Or.inr hy) (Or.inr hlt)) hlt) rfl

/-- ✱212·65. \(\vdash \colon\ldotp P\in \text{Ser}.\alpha \subset CʻP.\supset :\text{E}!\text{seq}_{P}ʻ\alpha .\equiv .\overrightarrow{P}ʻ\text{seq}_{P}ʻ\alpha =\text{seq}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha\) -/
theorem pm212_65 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser ∧ A ⊆ fld P → (EDesc (seqP P) A ↔
      Desc (seqP P) A (fun s => Desc (seqP (segSer P)) (Rfwd P ʻʻ A) (fun B => refs P s = B))) := by
  rintro ⟨hS, hA⟩
  constructor
  · intro hE
    obtain ⟨s, hs⟩ := exists_of_edesc hE
    exact desc_of (uniq_of (fun t ht => seq_unique hS.2 ht hs) hs) (desc_of (seqS_of hS hA hs) rfl)
  · rintro ⟨s, hs, -⟩
    exact ⟨s, hs⟩

/-- ✱212·651. \[\begin{align}\vdash \colon\ldotp &P\in \text{Ser}.\alpha \subset CʻP.\supset :\\ &\text{E}!\text{seq}_{P}ʻ\alpha .\equiv .\text{seq}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha \in \overrightarrow{P} ʻʻCʻP .\equiv .\text{E}!\text{seq}(\overrightarrow{P}^{;}P)ʻ\overrightarrow{P}ʻʻ\alpha\end{align}\] -/
theorem pm212_651 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser ∧ A ⊆ fld P →
      (EDesc (seqP P) A ↔ Desc (seqP (segSer P)) (Rfwd P ʻʻ A) (fun B => B ∈ Rfwd P ʻʻ fld P)) ∧
        (Desc (seqP (segSer P)) (Rfwd P ʻʻ A) (fun B => B ∈ Rfwd P ʻʻ fld P) ↔
          EDesc (seqP (Rfwd P ⁏ P)) (Rfwd P ʻʻ A)) := by
  rintro ⟨hS, hA⟩
  have hu : ∀ a b, seqP P a A → seqP P b A → a = b := fun a b ha hb => seq_unique hS.2 ha hb
  have h1 : EDesc (seqP P) A ↔
      Desc (seqP (segSer P)) (Rfwd P ʻʻ A) (fun B => B ∈ Rfwd P ʻʻ fld P) := by
    rw [edesc_iff_ex hu]
    constructor
    · rintro ⟨s, hs⟩
      exact desc_of (seqS_of hS hA hs) ⟨s, (seqP_iff.1 hs).1.2, rfl⟩
    · rintro ⟨B, hB, ⟨w, hw, rfl⟩⟩
      exact ⟨w, seq_of_S hS hA hw ((hB _).2 rfl)⟩
  have hT : ∀ U, seqP (Rfwd P ⁏ P) U (Rfwd P ʻʻ A) ↔ ∃ w, seqP P w A ∧ U = refs P w := by
    intro U
    have hM : Rfwd P ʻʻ A ∩ fld (Rfwd P ⁏ P) = Rfwd P ʻʻ A := by
      rw [fld_T hS]
      exact Set.inter_eq_left.2 fun V ⟨y, hy, hV⟩ => ⟨y, hA hy, hV⟩
    rw [seqP_iff, hM, fld_T hS]
    constructor
    · rintro ⟨⟨h1, ⟨w, hw, rfl⟩⟩, h3⟩
      refine ⟨w, seqP_iff.2 ⟨⟨fun y hy => ?_, hw⟩, fun z hz hzw => ?_⟩, rfl⟩
      · exact (T_refs hS hy.2 hw).1 (h1 _ ⟨y, hy.1, rfl⟩)
      · refine h3 (refs P z) (fun V hV => ?_) ((T_refs hS (fld_l hzw) hw).2 hzw)
        obtain ⟨y, hy, rfl⟩ := hV
        exact (T_refs hS (hA hy) (fld_l hzw)).2 (hz y ⟨hy, hA hy⟩)
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨⟨hw1, hwf⟩, hw3⟩ := seqP_iff.1 hw
      refine ⟨⟨fun V hV => ?_, ⟨w, hwf, rfl⟩⟩, fun W hW hWw => ?_⟩
      · obtain ⟨y, hy, rfl⟩ := hV
        exact (T_refs hS (hA hy) hwf).2 (hw1 y ⟨hy, hA hy⟩)
      · obtain ⟨z, y, ⟨rfl, hy⟩, hzy⟩ := (T_apply hS).1 hWw
        have hy' := refs_inj hS hwf (fld_r hzy) hy
        rw [← hy'] at hzy
        refine hw3 z (fun a ha => ?_) hzy
        exact (T_refs hS ha.2 (fld_l hzy)).1 (hW _ ⟨a, ha.1, rfl⟩)
  refine ⟨h1, ?_⟩
  rw [← h1, edesc_iff_ex hu]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨refs P s, uniq_of (fun U hU => ?_) ((hT _).2 ⟨s, hs, rfl⟩)⟩
    obtain ⟨w, hw, rfl⟩ := (hT U).1 hU
    rw [hu w s hw hs]
  · intro h
    obtain ⟨U, hU⟩ := exists_of_edesc h
    obtain ⟨w, hw, -⟩ := (hT U).1 hU
    exact ⟨w, hw⟩

/-- ✱212·652. \[\begin{align}\vdash : P \in \text{Ser} . \alpha \subset CʻP . \text{E}! \text{max}_{P}ʻ\alpha . \text{E}! &\text{seq}(\varsigma ʻP )ʻ\overrightarrow{P} ʻʻ\alpha . \supset .\\ &\text{seq}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha = \alpha \cup Pʻʻ\alpha\end{align}\] -/
theorem pm212_652 {α : Type u} {P : α → α → Prop} {A : Set α} :
    ((P ∈ Ser ∧ A ⊆ fld P) ∧ EDesc (maxP P) A) ∧ EDesc (seqP (segSer P)) (Rfwd P ʻʻ A) →
      Desc (seqP (segSer P)) (Rfwd P ʻʻ A) (fun B => B = A ∪ P ʻʻ A) := by
  rintro ⟨⟨⟨hS, hA⟩, hM⟩, hE⟩
  obtain ⟨m, hm⟩ := exists_of_edesc hM
  obtain ⟨B, hB⟩ := hE
  have hBs := (hB B).2 rfl
  refine ⟨B, hB, ?_⟩
  have tr := mem_transR.1 hS.1.2
  have hc := hS.2
  obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
  have hP : rEx P := rEx_of_fld hmf
  have hle : ∀ y, y ∈ A → P y m ∨ y = m := by
    intro y hy
    rcases mem_connex.1 hc y m ⟨hA hy, hmf⟩ with (h | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hm' y hy)
  have eA : A ∪ P ʻʻ A = refs P m ∪ ι m := by
    ext y
    constructor
    · rintro (hy | ⟨w, hw, hyw⟩)
      · rcases hle y hy with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rcases hle w hw with h | rfl
        · exact Or.inl (tr y w m ⟨hyw, h⟩)
        · exact Or.inl hyw
    · rintro (hy | hy)
      · exact Or.inr ⟨m, hmA, hy⟩
      · have hy' : y = m := hy
        rw [hy']; exact Or.inl hmA
  rw [eA]
  obtain ⟨⟨hfol, hBf⟩, hmin⟩ := seqP_iff.1 hBs
  rw [fld_S hP] at hBf
  have hBsect := sect_of_seg hS.1.2 hBf
  have hmB := hfol (refs P m) ⟨⟨m, hmA, rfl⟩, by rw [fld_S hP]; exact refs_seg m⟩
  rw [pm212_23 ⟨hS.1.2, hS.2⟩] at hmB
  obtain ⟨⟨-, hsub⟩, hne⟩ := hmB
  have hmB' : m ∈ B := by
    have : ¬ B ⊆ refs P m := fun h => hne (Set.Subset.antisymm hsub h)
    obtain ⟨z, hzB, hzm⟩ := Set.not_subset.1 this
    rcases mem_connex.1 hc z m ⟨hBsect.1 hzB, hmf⟩ with (h | rfl) | h
    · exact absurd h hzm
    · exact hzB
    · exact sect_closed hBsect h hzB
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · by_contra hz'
    have hmz : P m z := by
      rcases mem_connex.1 hc z m ⟨hBsect.1 hz, hmf⟩ with (h | h) | h
      · exact absurd (Or.inl h) hz'
      · exact absurd (Or.inr h) hz'
      · exact h
    refine hmin (refs P z) (fun V hV => ?_) ?_
    · obtain ⟨⟨y, hy, rfl⟩, -⟩ := hV
      have hyz : P y z := by
        rcases hle y hy with h | rfl
        · exact tr y m z ⟨h, hmz⟩
        · exact hmz
      exact (S_refs hS (hA hy) (fld_r hmz)).2 hyz
    · rw [pm212_23 ⟨hS.1.2, hS.2⟩]
      refine ⟨⟨⟨refs_seg z, hBf⟩, fun y hy => sect_closed hBsect hy hz⟩, fun e => ?_⟩
      have : z ∈ refs P z := by rw [e]; exact hz
      exact mem_rl_J.1 hS.1.1 z this
  · rcases hz with hz | hz
    · exact hsub hz
    · have hz' : z = m := hz
      rw [hz']; exact hmB'

/-- ✱212·653. \(\vdash \colon\ldotp P \in \text{Ser} . \text{E}! \text{max}_{P}ʻ\alpha . \alpha \subset CʻP . \supset : \text{E}! \text{seq}_{P}ʻ\alpha . \equiv . \text{E}! \text{seq}(\varsigma ʻP) ʻ\overrightarrow{P}ʻʻ\alpha\) -/
theorem pm212_653 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ Ser ∧ EDesc (maxP P) A) ∧ A ⊆ fld P →
      (EDesc (seqP P) A ↔ EDesc (seqP (segSer P)) (Rfwd P ʻʻ A)) := by
  rintro ⟨⟨hS, hM⟩, hA⟩
  constructor
  · intro hE
    obtain ⟨s, -, ⟨B, hB, -⟩⟩ := (pm212_65 ⟨hS, hA⟩).1 hE
    exact ⟨B, hB⟩
  · intro hE
    obtain ⟨B, hB, e⟩ := pm212_652 ⟨⟨⟨hS, hA⟩, hM⟩, hE⟩
    have hBs := (hB B).2 rfl
    obtain ⟨m, hm⟩ := exists_of_edesc hM
    obtain ⟨⟨hmA, hmf⟩, hm'⟩ := maxP_iff.1 hm
    have hP : rEx P := rEx_of_fld hmf
    have hBD : B ∈ dom (imgRel P) := by
      have := (seqP_iff.1 hBs).1.2
      rwa [fld_S hP] at this
    rw [e] at hBD
    have hsect := sect_of_seg hS.1.2 hBD
    have hmax : maxP P m (A ∪ P ʻʻ A) := by
      refine maxP_iff.2 ⟨⟨Or.inl hmA, hmf⟩, fun y hy hmy => ?_⟩
      rcases hy with hy | ⟨w, hw, hyw⟩
      · exact hm' y hy hmy
      · rcases mem_connex.1 hS.2 w m ⟨fld_r hyw, hmf⟩ with (h | rfl) | h
        · exact mem_rl_J.1 hS.1.1 m (mem_transR.1 hS.1.2 m y m ⟨hmy,
            mem_transR.1 hS.1.2 y w m ⟨hyw, h⟩⟩)
        · exact mem_rl_J.1 hS.1.1 w (mem_transR.1 hS.1.2 w y w ⟨hmy, hyw⟩)
        · exact hm' w hw h
    obtain ⟨C, hC⟩ := hBD
    obtain ⟨b, -, hb⟩ := seq_of_max_sect hS.2 hsect hC hmax
    have hbA : seqP P b A := by
      refine (seq_congr fun z => ⟨fun h y hy => ?_, fun h y hy => h y ⟨Or.inl hy.1, hy.2⟩⟩).2 hb
      rcases hy.1 with hy' | ⟨w, hw, hyw⟩
      · exact h y ⟨hy', hy.2⟩
      · exact mem_transR.1 hS.1.2 y w z ⟨hyw, h w ⟨hw, fld_r hyw⟩⟩
    exact ⟨b, uniq_of (fun t ht => seq_unique hS.2 ht hbA) hbA⟩

/-- ✱212·66. \(\vdash : P \in \text{trans} \cap \text{connex} . \kappa \subset \text{D}ʻP_{\in } . {\sim} \text{E}! \text{max}(\varsigma ʻP )ʻ\kappa . \supset . {\sim} \text{E}! \text{max}_{P}ʻsʻ\kappa\) -/
theorem pm212_66 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} :
    (P ∈ transR ∩ connex ∧ K ⊆ dom (imgRel P)) ∧ ¬ EDesc (maxP (segSer P)) K →
      ¬ EDesc (maxP P) (sumCls K) := by
  rintro ⟨⟨⟨ht, hc⟩, hK⟩, hM⟩ hE
  obtain ⟨x, hx⟩ := exists_of_edesc hE
  have hP : rEx P := rEx_of_fld (maxP_iff.1 hx).1.2
  have hSS := pm212_31 ⟨ht, hc⟩
  rw [edesc_iff_ex fun a b ha hb => max_unique hSS.2 ha hb] at hM
  obtain ⟨⟨⟨B, hB, hxB⟩, hxf⟩, hx'⟩ := maxP_iff.1 hx
  apply hM
  refine ⟨B, maxP_iff.2 ⟨⟨hB, by rw [fld_S hP]; exact hK hB⟩, fun C hC hBC => ?_⟩⟩
  rw [pm212_23 ⟨ht, hc⟩] at hBC
  obtain ⟨⟨-, hsub⟩, hne⟩ := hBC
  have hCs : C ∈ sect P := sect_of_seg ht (hK hC)
  have hBs : B ∈ sect P := sect_of_seg ht (hK hB)
  have : ¬ C ⊆ B := fun h' => hne (Set.Subset.antisymm hsub h')
  obtain ⟨w, hwC, hwB⟩ := Set.not_subset.1 this
  rcases mem_connex.1 hc x w ⟨hxf, hCs.1 hwC⟩ with (h' | rfl) | h'
  · exact hx' w ⟨C, hC, hwC⟩ h'
  · exact hwB hxB
  · exact hwB (sect_closed hBs h' hxB)

/-- ✱212·661. \(\vdash : P \in \text{Ser}.\kappa \subset \text{D}ʻP_{\in } . \text{E}! \text{lt}(\varsigma ʻP)ʻ\kappa .\supset .\text{lt}(\varsigma ʻP)ʻ\kappa = \text{lt}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻsʻ\kappa = sʻ\kappa\) -/
theorem pm212_661 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} :
    (P ∈ Ser ∧ K ⊆ dom (imgRel P)) ∧ EDesc (ltP (segSer P)) K →
      Desc (ltP (segSer P)) K (fun A => Desc (ltP (segSer P)) (Rfwd P ʻʻ sumCls K)
          (fun B => A = B)) ∧
        Desc (ltP (segSer P)) (Rfwd P ʻʻ sumCls K) (fun B => B = sumCls K) := by
  rintro ⟨⟨hS, hK⟩, hE⟩
  obtain ⟨U, hU⟩ := exists_of_edesc hE
  have hP : rEx P := pm212_14.2 (rEx_of_fld (seqP_iff.1 hU.1).1.2)
  have h1 : ∀ A, ltP (segSer P) A K ↔ A = sumCls K := by
    intro A
    obtain ⟨b, hb, e⟩ := pm212_402 ⟨⟨⟨hS.1.2, hS.2⟩, hP⟩, hK⟩
    have hnm : ¬∃ V, maxP (segSer P) V K := hU.2
    rw [ltP_iff]
    constructor
    · rintro ⟨hs, -⟩
      rw [e]; exact (hb A).1 (Or.inr ⟨hs, hnm⟩)
    · intro hA
      rw [e] at hA
      rcases (hb A).2 hA with h | h
      · exact absurd ⟨A, h⟩ hnm
      · exact h
  have hsK : sumCls K ∈ dom (imgRel P) := pm211_64 hK
  have hsf : sumCls K ⊆ fld P := seg_sub_fld hsK
  have hM' : ¬ EDesc (maxP (segSer P)) K := fun hM => by
    obtain ⟨V, hV⟩ := exists_of_edesc hM
    exact hU.2 ⟨V, hV⟩
  have hnm : ¬∃ m, maxP P m (sumCls K) := by
    have := pm212_66 ⟨⟨⟨hS.1.2, hS.2⟩, hK⟩, hM'⟩
    rwa [edesc_iff_ex fun a b ha hb => max_unique hS.2 ha hb] at this
  have heq : P ʻʻ sumCls K = sumCls K :=
    (eq_img_of_nomax (sect_of_seg hS.1.2 hsK) hnm).symm
  have h2 : ∀ B, ltP (segSer P) B (Rfwd P ʻʻ sumCls K) ↔ B = sumCls K := by
    intro B
    rw [lt_S hS hP hsf B, heq]
    exact ⟨fun h => h.1, fun h => ⟨h, hnm⟩⟩
  exact ⟨desc_of h1 (desc_of h2 rfl), desc_of h2 rfl⟩

/-- ✱212·662. \[\begin{align}\vdash : P \in \text{Ser}. \kappa \subset \text{D}ʻP_{\in } . \text{E}! &\text{lt}(\varsigma ʻP)ʻ\kappa .\supset .\\ &(\exists \lambda ).\lambda \subset \overrightarrow{P}ʻʻCʻP.\text{lt}(\varsigma ʻP)ʻ\kappa = \text{lt}(\varsigma ʻP)ʻ\lambda \\ [*212·661]\end{align}\] -/
theorem pm212_662 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} :
    (P ∈ Ser ∧ K ⊆ dom (imgRel P)) ∧ EDesc (ltP (segSer P)) K →
      ∃ L, L ⊆ Rfwd P ʻʻ fld P ∧ Desc (ltP (segSer P)) K (fun A => Desc (ltP (segSer P)) L
        (fun B => A = B)) := by
  intro h
  have hsf : sumCls K ⊆ fld P := seg_sub_fld (pm211_64 h.1.2)
  exact ⟨Rfwd P ʻʻ sumCls K, fun V ⟨y, hy, hV⟩ => ⟨y, hsf hy, hV⟩, (pm212_661 h).1⟩

/-- ✱212·663. \[\begin{align}\vdash : P \in \text{Ser}. x \in CʻP.\overrightarrow{P}ʻx \in \text{D}ʻ&\text{lt}(\varsigma ʻP).\supset .\\ &\overrightarrow{P}ʻx = \text{lt}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\overrightarrow{P}ʻx.x = \text{lt}_Pʻ\overrightarrow{P}ʻx\end{align}\] -/
theorem pm212_663 {α : Type u} {P : α → α → Prop} {x : α} :
    (P ∈ Ser ∧ x ∈ fld P) ∧ refs P x ∈ dom (ltP (segSer P)) →
      Desc (ltP (segSer P)) (Rfwd P ʻʻ refs P x) (fun B => refs P x = B) ∧
        Desc (ltP P) (refs P x) (fun y => x = y) := by
  rintro ⟨⟨hS, hx⟩, K, hK⟩
  have hP : rEx P := rEx_of_fld hx
  have hSS := pm212_31 ⟨hS.1.2, hS.2⟩
  rw [lt_inter, fld_S hP] at hK
  have hK'D : K ∩ dom (imgRel P) ⊆ dom (imgRel P) := fun A hA => hA.2
  have hE : EDesc (ltP (segSer P)) (K ∩ dom (imgRel P)) :=
    ⟨refs P x, uniq_of (fun B hB => seq_unique hSS.2 hB.1 hK.1) hK⟩
  obtain ⟨b, hb, e⟩ := pm212_402 ⟨⟨⟨hS.1.2, hS.2⟩, hP⟩, hK'D⟩
  have e1 : refs P x = sumCls (K ∩ dom (imgRel P)) := ((hb _).1 (Or.inr hK)).trans e.symm
  have hM' : ¬ EDesc (maxP (segSer P)) (K ∩ dom (imgRel P)) := fun hM => by
    obtain ⟨V, hV⟩ := exists_of_edesc hM
    exact hK.2 ⟨V, hV⟩
  have hnm0 := pm212_66 ⟨⟨⟨hS.1.2, hS.2⟩, hK'D⟩, hM'⟩
  rw [edesc_iff_ex fun a b ha hb => max_unique hS.2 ha hb] at hnm0
  have h2 := (pm212_661 ⟨⟨hS, hK'D⟩, hE⟩).2
  rw [← e1] at h2 hnm0
  refine ⟨desc_symm h2, ?_⟩
  have hlt : ltP P x (refs P x) := ⟨(seq_refs hS hx x).2 rfl, hnm0⟩
  exact desc_of (uniq_of (fun y hy => limax_unique hS (Or.inr hy) (Or.inr hlt)) hlt) rfl

/-- ✱212·664. \(\vdash \colon\ldotp P \in \text{Ser}.x \in CʻP.\supset :x \in \text{D}ʻ\text{lt}_P . \equiv .\overrightarrow{P}ʻx \in \text{D}ʻ\text{lt}(\varsigma ʻP)\) -/
theorem pm212_664 {α : Type u} {P : α → α → Prop} {x : α} :
    P ∈ Ser ∧ x ∈ fld P → (x ∈ dom (ltP P) ↔ refs P x ∈ dom (ltP (segSer P))) := by
  rintro ⟨hS, hx⟩
  have hP : rEx P := rEx_of_fld hx
  constructor
  · rintro ⟨A, hA⟩
    rw [lt_inter] at hA
    obtain ⟨⟨-, e⟩, hm⟩ := (lt_char hS x).1 hA
    exact ⟨_, (lt_S hS hP (Set.inter_subset_right : A ∩ fld P ⊆ fld P) (refs P x)).2 ⟨e.symm, hm⟩⟩
  · intro h
    obtain ⟨y, hy, e⟩ := (pm212_663 ⟨⟨hS, hx⟩, h⟩).2
    have h1 : ltP P y (refs P x) := (hy y).2 rfl
    rw [← e] at h1
    exact ⟨refs P x, h1⟩

/-- ✱212·665. \(\vdash : P \in \text{Ser}. \dot{\exists} ! P . \alpha \in \text{D}ʻ(P_{\in } \dot{\cap} I) .\supset . \text{lt}(\varsigma ʻP)ʻ\overrightarrow{P}ʻʻ\alpha = \alpha\) -/
theorem pm212_665 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ Ser ∧ rEx P) ∧ A ∈ dom (imgRel P ⩀ I) →
      Desc (ltP (segSer P)) (Rfwd P ʻʻ A) (fun B => B = A) := by
  rintro ⟨⟨hS, hP⟩, hA⟩
  have e : A = P ʻʻ A := mem_dom_imgRel_rcap_I.1 hA
  have hnm : ¬∃ m, maxP P m A := fun ⟨m, hm⟩ => pm211_4 hA ⟨m, hm⟩
  refine desc_of (fun B => ?_) rfl
  rw [lt_S hS hP (pm211_14.2 hA).1 B, ← e]
  exact ⟨fun h => h.1, fun h => ⟨h, hnm⟩⟩

/-- ✱212·666. \(\vdash : P \in \text{Ser}. \dot{\exists} ! P .\supset . \text{D}ʻ\text{lt}(\varsigma ʻP) = \text{D}ʻ(P_{\in } \dot{\cap} I)\) -/
theorem pm212_666 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser ∧ rEx P → dom (ltP (segSer P)) = dom (imgRel P ⩀ I) := by
  rintro ⟨hS, hP⟩
  ext A
  constructor
  · rintro ⟨K, hK⟩
    have hSS := pm212_31 ⟨hS.1.2, hS.2⟩
    rw [lt_inter, fld_S hP] at hK
    have hK'D : K ∩ dom (imgRel P) ⊆ dom (imgRel P) := fun B hB => hB.2
    obtain ⟨b, hb, e⟩ := pm212_402 ⟨⟨⟨hS.1.2, hS.2⟩, hP⟩, hK'D⟩
    have hA : A = sumCls (K ∩ dom (imgRel P)) := ((hb A).1 (Or.inr hK)).trans e.symm
    have hM' : ¬ EDesc (maxP (segSer P)) (K ∩ dom (imgRel P)) := fun hM => by
      obtain ⟨V, hV⟩ := exists_of_edesc hM
      exact hK.2 ⟨V, hV⟩
    have hnm := pm212_66 ⟨⟨⟨hS.1.2, hS.2⟩, hK'D⟩, hM'⟩
    rw [edesc_iff_ex fun a b ha hb => max_unique hS.2 ha hb] at hnm
    rw [pm211_42 hS.1.2, hA]
    exact ⟨pm211_64 hK'D, fun ⟨m, hm⟩ => hnm ⟨m, hm⟩⟩
  · intro hA
    obtain ⟨b, hb, e⟩ := pm212_665 ⟨⟨hS, hP⟩, hA⟩
    have h1 : ltP (segSer P) b (Rfwd P ʻʻ A) := (hb b).2 rfl
    rw [e] at h1
    exact ⟨_, h1⟩

/-- ✱212·667. \(\vdash : P \in \text{Ser}.\supset . \text{D}ʻ\text{lt}(\varsigma ʻP) - \iota ʻ\Lambda = \text{ᗡ}ʻ\text{sgm}ʻP \quad[*212·152·151·666]\) -/
theorem pm212_667 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → dom (ltP (segSer P)) \ ι Λ = codom (sgm P) := by
  intro hS
  by_cases hP : rEx P
  · rw [pm212_666 ⟨hS, hP⟩, pm212_152]
  · have h0 : P = rNull := by
      funext x y
      apply propext
      exact ⟨fun h => absurd ⟨x, y, h⟩ hP, fun h => (rNull_apply _ _ h).elim⟩
    rw [segSer_rNull hP, pm212_151 h0]
    ext A
    constructor
    · rintro ⟨⟨K, hK⟩, -⟩
      exact absurd (seqP_iff.1 hK.1).1.2 not_fld_rNull
    · rintro ⟨B, hB⟩
      exact (rNull_apply _ _ hB).elim

/-! ### Helper lemmas for ✱212·7–·72: a correlator carries sections and segments -/

section H212d

variable {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}

private theorem cor_data (hS : S ∈ smorbar P Q) :
    ((∀ x y z, S x z ∧ S y z → x = y) ∧ (∀ x y z, S x y ∧ S x z → y = z)) ∧
      fld Q = codom S ∧ ∀ x y, P x y ↔ ∃ z w, (S x z ∧ S y w) ∧ Q z w := by
  obtain ⟨⟨h11, hcod⟩, hP⟩ := hS
  refine ⟨mem_arrow_one_one.1 h11, hcod, fun x y => ?_⟩
  rw [hP]
  exact semi_apply S Q x y

private theorem cor_zfld (hS : S ∈ smorbar P Q) {x : α} {z : β} (h : S x z) : z ∈ fld Q := by
  rw [(cor_data hS).2.1]
  exact ⟨x, h⟩

private theorem cor_xfld (hS : S ∈ smorbar P Q) {x : α} {z : β} (h : S x z) : x ∈ fld P := by
  obtain ⟨-, hcod, hPi⟩ := cor_data hS
  obtain ⟨w, hzw | hwz⟩ := cor_zfld hS h
  · have : w ∈ codom S := by rw [← hcod]; exact fld_r hzw
    obtain ⟨y, hy⟩ := this
    exact fld_l ((hPi x y).2 ⟨z, w, ⟨h, hy⟩, hzw⟩)
  · have : w ∈ codom S := by rw [← hcod]; exact fld_l hwz
    obtain ⟨y, hy⟩ := this
    exact fld_r ((hPi y x).2 ⟨w, z, ⟨hy, h⟩, hwz⟩)

private theorem cor_img_img (hS : S ∈ smorbar P Q) (B : Set β) :
    P ʻʻ (S ʻʻ B) = S ʻʻ (Q ʻʻ B) := by
  obtain ⟨⟨-, h2⟩, hcod, hPi⟩ := cor_data hS
  ext x
  constructor
  · rintro ⟨y, ⟨w', hw', hyw'⟩, hxy⟩
    obtain ⟨z, w, ⟨hxz, hyw⟩, hzw⟩ := (hPi x y).1 hxy
    have e := h2 y w w' ⟨hyw, hyw'⟩
    exact ⟨z, ⟨w, e ▸ hw', hzw⟩, hxz⟩
  · rintro ⟨z, ⟨w, hw, hzw⟩, hxz⟩
    have : w ∈ codom S := by rw [← hcod]; exact fld_r hzw
    obtain ⟨y, hyw⟩ := this
    exact ⟨y, ⟨w, hw, hyw⟩, (hPi x y).2 ⟨z, w, ⟨hxz, hyw⟩, hzw⟩⟩

private theorem cor_img_diff (hS : S ∈ smorbar P Q) (B C : Set β) :
    S ʻʻ (B \ C) = S ʻʻ B \ S ʻʻ C := by
  obtain ⟨⟨-, h2⟩, -, -⟩ := cor_data hS
  ext x
  constructor
  · rintro ⟨z, ⟨hzB, hzC⟩, hxz⟩
    refine ⟨⟨z, hzB, hxz⟩, ?_⟩
    rintro ⟨w, hwC, hxw⟩
    exact hzC (h2 x w z ⟨hxw, hxz⟩ ▸ hwC)
  · rintro ⟨⟨z, hzB, hxz⟩, hn⟩
    exact ⟨z, ⟨hzB, fun hzC => hn ⟨z, hzC, hxz⟩⟩, hxz⟩

private theorem cor_inj (hS : S ∈ smorbar P Q) {B C : Set β} (hB : B ⊆ fld Q) (hC : C ⊆ fld Q)
    (e : S ʻʻ B = S ʻʻ C) : B = C := by
  obtain ⟨⟨-, h2⟩, hcod, -⟩ := cor_data hS
  have key : ∀ B C : Set β, B ⊆ fld Q → S ʻʻ B = S ʻʻ C → B ⊆ C := by
    intro B C hB e z hz
    have : z ∈ codom S := by rw [← hcod]; exact hB hz
    obtain ⟨x, hxz⟩ := this
    have : x ∈ S ʻʻ C := by rw [← e]; exact ⟨z, hz, hxz⟩
    obtain ⟨w, hw, hxw⟩ := this
    exact h2 x w z ⟨hxw, hxz⟩ ▸ hw
  exact Set.Subset.antisymm (key B C hB e) (key C B hC e.symm)

private theorem cor_ne (hS : S ∈ smorbar P Q) {B : Set β} (hB : B ⊆ fld Q) :
    B.Nonempty ↔ (S ʻʻ B).Nonempty := by
  obtain ⟨-, hcod, -⟩ := cor_data hS
  constructor
  · rintro ⟨z, hz⟩
    have : z ∈ codom S := by rw [← hcod]; exact hB hz
    obtain ⟨x, hxz⟩ := this
    exact ⟨x, z, hz, hxz⟩
  · rintro ⟨x, z, hz, -⟩
    exact ⟨z, hz⟩

private theorem cor_pre (hS : S ∈ smorbar P Q) {A : Set α} (hA : A ⊆ fld P) :
    {z | ∃ x, x ∈ A ∧ S x z} ⊆ fld Q ∧ S ʻʻ {z | ∃ x, x ∈ A ∧ S x z} = A := by
  obtain ⟨⟨h1, -⟩, -, hPi⟩ := cor_data hS
  refine ⟨fun z ⟨x, _, hxz⟩ => cor_zfld hS hxz, ?_⟩
  ext x
  constructor
  · rintro ⟨z, ⟨y, hy, hyz⟩, hxz⟩
    exact h1 x y z ⟨hxz, hyz⟩ ▸ hy
  · intro hx
    obtain ⟨w, hxw | hwx⟩ := hA hx
    · obtain ⟨z, -, ⟨hxz, -⟩, -⟩ := (hPi x w).1 hxw
      exact ⟨z, ⟨x, hx, hxz⟩, hxz⟩
    · obtain ⟨-, z, ⟨-, hxz⟩, -⟩ := (hPi w x).1 hwx
      exact ⟨z, ⟨x, hx, hxz⟩, hxz⟩

private theorem cor_img_sub (hS : S ∈ smorbar P Q) (B : Set β) : S ʻʻ B ⊆ fld P :=
  fun _ ⟨_, _, hxz⟩ => cor_xfld hS hxz

private theorem cor_sect (hS : S ∈ smorbar P Q) {A : Set α} :
    A ∈ sect P ↔ ∃ B, B ∈ sect Q ∧ A = S ʻʻ B := by
  obtain ⟨-, hcod, hPi⟩ := cor_data hS
  constructor
  · intro hA
    obtain ⟨hsub, e⟩ := cor_pre hS hA.1
    refine ⟨_, ⟨hsub, ?_⟩, e.symm⟩
    rintro z ⟨w, ⟨x', hx', hx'w⟩, hzw⟩
    have : z ∈ codom S := by rw [← hcod]; exact fld_l hzw
    obtain ⟨x, hxz⟩ := this
    exact ⟨x, sect_closed hA ((hPi x x').2 ⟨z, w, ⟨hxz, hx'w⟩, hzw⟩) hx', hxz⟩
  · rintro ⟨B, hB, rfl⟩
    refine ⟨cor_img_sub hS B, ?_⟩
    rw [cor_img_img hS]
    rintro x ⟨z, hz, hxz⟩
    exact ⟨z, hB.2 hz, hxz⟩

private theorem cor_D (hS : S ∈ smorbar P Q) {A : Set α} :
    A ∈ dom (imgRel P) ↔ ∃ B, B ∈ dom (imgRel Q) ∧ A = S ʻʻ B := by
  constructor
  · rintro ⟨C, rfl⟩
    have hC : P ʻʻ C = P ʻʻ (C ∩ fld P) := by
      ext x
      exact ⟨fun ⟨y, hy, hxy⟩ => ⟨y, ⟨hy, fld_r hxy⟩, hxy⟩, fun ⟨y, hy, hxy⟩ => ⟨y, hy.1, hxy⟩⟩
    obtain ⟨-, e⟩ := cor_pre hS (Set.inter_subset_right : C ∩ fld P ⊆ fld P)
    refine ⟨Q ʻʻ {z | ∃ x, x ∈ C ∩ fld P ∧ S x z}, ⟨_, rfl⟩, ?_⟩
    rw [hC, ← cor_img_img hS, e]
  · rintro ⟨B, ⟨C, rfl⟩, rfl⟩
    exact ⟨S ʻʻ C, (cor_img_img hS C).symm⟩

private theorem cor_DI (hS : S ∈ smorbar P Q) {A : Set α} :
    A ∈ dom (imgRel P ⩀ I) ↔ ∃ B, B ∈ dom (imgRel Q ⩀ I) ∧ A = S ʻʻ B := by
  rw [mem_dom_imgRel_rcap_I]
  constructor
  · intro hA
    have hAf : A ⊆ fld P := by
      rw [hA]; exact img_sub_fld A
    obtain ⟨hsub, e⟩ := cor_pre hS hAf
    refine ⟨_, mem_dom_imgRel_rcap_I.2 (cor_inj hS hsub (img_sub_fld _) ?_), e.symm⟩
    rw [← cor_img_img hS, e]
    exact hA
  · rintro ⟨B, hB, rfl⟩
    rw [cor_img_img hS, ← mem_dom_imgRel_rcap_I.1 hB]

private theorem cor_smorbar (hS : S ∈ smorbar P Q) {X : Set α → Set α → Prop}
    {Y : Set β → Set β → Prop} (hY : ∀ B, B ∈ fld Y → B ⊆ fld Q)
    (hXY : ∀ A C, X A C ↔ ∃ B D, (A = S ʻʻ B ∧ C = S ʻʻ D) ∧ Y B D) :
    imgRel S ↾ fld Y ∈ smorbar X Y := by
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro A A' B ⟨⟨hA, -⟩, ⟨hA', -⟩⟩
    exact (show A = S ʻʻ B from hA).trans (show A' = S ʻʻ B from hA').symm
  · rintro A B B' ⟨⟨hB, hBY⟩, ⟨hB', hB'Y⟩⟩
    exact cor_inj hS (hY B hBY) (hY B' hB'Y)
      ((show A = S ʻʻ B from hB).symm.trans (show A = S ʻʻ B' from hB'))
  · ext B
    exact ⟨fun h => ⟨S ʻʻ B, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  · funext A C
    apply propext
    rw [semi_apply, hXY]
    constructor
    · rintro ⟨B, D, ⟨e1, e2⟩, h⟩
      exact ⟨B, D, ⟨⟨e1, D, Or.inl h⟩, ⟨e2, B, Or.inr h⟩⟩, h⟩
    · rintro ⟨B, D, ⟨⟨e1, -⟩, ⟨e2, -⟩⟩, h⟩
      exact ⟨B, D, ⟨e1, e2⟩, h⟩

private theorem cor_fld {X : Set α → Set α → Prop} {Y : Set β → Set β → Prop}
    (hXY : ∀ A C, X A C ↔ ∃ B D, (A = S ʻʻ B ∧ C = S ʻʻ D) ∧ Y B D) :
    fld X = imgRel S ʻʻ fld Y := by
  ext A
  constructor
  · rintro ⟨C, h | h⟩
    · obtain ⟨B, D, ⟨e1, -⟩, h'⟩ := (hXY A C).1 h
      exact ⟨B, ⟨D, Or.inl h'⟩, e1⟩
    · obtain ⟨B, D, ⟨-, e2⟩, h'⟩ := (hXY C A).1 h
      exact ⟨D, ⟨B, Or.inr h'⟩, e2⟩
  · rintro ⟨B, ⟨D, h | h⟩, e⟩
    · exact ⟨S ʻʻ D, Or.inl ((hXY A _).2 ⟨B, D, ⟨e, rfl⟩, h⟩)⟩
    · exact ⟨S ʻʻ D, Or.inr ((hXY _ A).2 ⟨D, B, ⟨rfl, e⟩, h⟩)⟩

private theorem cor_XY_sect (hS : S ∈ smorbar P Q) :
    ∀ A C, segSer (anc P) A C ↔
      ∃ B D, (A = S ʻʻ B ∧ C = S ʻʻ D) ∧ segSer (anc Q) B D := by
  intro A C
  rw [segSer_anc_iff]
  constructor
  · rintro ⟨⟨hA, hC⟩, hne⟩
    obtain ⟨B, hB, rfl⟩ := (cor_sect hS).1 hA
    obtain ⟨D, hD, rfl⟩ := (cor_sect hS).1 hC
    refine ⟨B, D, ⟨rfl, rfl⟩, segSer_anc_iff.2 ⟨⟨hB, hD⟩, ?_⟩⟩
    rw [← cor_img_diff hS] at hne
    exact (cor_ne hS fun z (hz : z ∈ D \ B) => hD.1 hz.1).2 hne
  · rintro ⟨B, D, ⟨rfl, rfl⟩, h⟩
    obtain ⟨⟨hB, hD⟩, hne⟩ := segSer_anc_iff.1 h
    refine ⟨⟨(cor_sect hS).2 ⟨B, hB, rfl⟩, (cor_sect hS).2 ⟨D, hD, rfl⟩⟩, ?_⟩
    rw [← cor_img_diff hS]
    exact (cor_ne hS fun z (hz : z ∈ D \ B) => hD.1 hz.1).1 hne

private theorem cor_XY_seg (hS : S ∈ smorbar P Q) :
    ∀ A C, segSer P A C ↔ ∃ B D, (A = S ʻʻ B ∧ C = S ʻʻ D) ∧ segSer Q B D := by
  intro A C
  have key : ∀ B D : Set β, D ⊆ fld Q →
      (((S ʻʻ D \ S ʻʻ B) \ P ʻʻ (S ʻʻ B \ S ʻʻ D)).Nonempty ↔
        ((D \ B) \ Q ʻʻ (B \ D)).Nonempty) := by
    intro B D hD
    rw [← cor_img_diff hS, ← cor_img_diff hS, cor_img_img hS, ← cor_img_diff hS]
    exact (cor_ne hS fun z (hz : z ∈ (D \ B) \ Q ʻʻ (B \ D)) => hD hz.1.1).symm
  rw [pm212_1]
  constructor
  · rintro ⟨⟨hA, hC⟩, hne⟩
    obtain ⟨B, hB, rfl⟩ := (cor_D hS).1 hA
    obtain ⟨D, hD, rfl⟩ := (cor_D hS).1 hC
    exact ⟨B, D, ⟨rfl, rfl⟩, pm212_1.2 ⟨⟨hB, hD⟩, (key B D (seg_sub_fld hD)).1 hne⟩⟩
  · rintro ⟨B, D, ⟨rfl, rfl⟩, h⟩
    obtain ⟨⟨hB, hD⟩, hne⟩ := pm212_1.1 h
    exact ⟨⟨(cor_D hS).2 ⟨B, hB, rfl⟩, (cor_D hS).2 ⟨D, hD, rfl⟩⟩,
      (key B D (seg_sub_fld hD)).2 hne⟩

private theorem cor_XY_sgm (hS : S ∈ smorbar P Q) :
    ∀ A C, sgm P A C ↔ ∃ B D, (A = S ʻʻ B ∧ C = S ʻʻ D) ∧ sgm Q B D := by
  intro A C
  rw [pm212_11]
  constructor
  · rintro ⟨⟨hA, hC⟩, hne⟩
    obtain ⟨B, hB, rfl⟩ := (cor_DI hS).1 hA
    obtain ⟨D, hD, rfl⟩ := (cor_DI hS).1 hC
    refine ⟨B, D, ⟨rfl, rfl⟩, pm212_11.2 ⟨⟨hB, hD⟩, ?_⟩⟩
    rw [← cor_img_diff hS] at hne
    exact (cor_ne hS fun z (hz : z ∈ D \ B) => (pm211_14.2 hD).1 hz.1).2 hne
  · rintro ⟨B, D, ⟨rfl, rfl⟩, h⟩
    obtain ⟨⟨hB, hD⟩, hne⟩ := pm212_11.1 h
    refine ⟨⟨(cor_DI hS).2 ⟨B, hB, rfl⟩, (cor_DI hS).2 ⟨D, hD, rfl⟩⟩, ?_⟩
    rw [← cor_img_diff hS]
    exact (cor_ne hS fun z (hz : z ∈ D \ B) => (pm211_14.2 hD).1 hz.1).1 hne

end H212d

/-- ✱212·7. \(\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .\text{sect}ʻP = S_{\in }ʻʻ\text{sect}ʻQ.Cʻ\varsigma ʻP_{*} = S_{\in }ʻʻCʻ\varsigma ʻQ_{*}\) -/
theorem pm212_7 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {S : α → β → Prop} :
    S ∈ smorbar P Q → sect P = imgRel S ʻʻ sect Q ∧
      fld (segSer (anc P)) = imgRel S ʻʻ fld (segSer (anc Q)) := by
  intro hS
  refine ⟨?_, cor_fld (cor_XY_sect hS)⟩
  ext A
  rw [cor_sect hS]
  exact ⟨fun ⟨B, hB, e⟩ => ⟨B, hB, e⟩, fun ⟨B, hB, e⟩ => ⟨B, hB, e⟩⟩

/-- ✱212·701. \[\begin{align}&\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .\text{D}ʻP_{\in } = S_{\in }ʻʻ\text{D}ʻQ_{\in }.Cʻ\varsigma ʻP = S_{\in }ʻʻCʻ\varsigma ʻQ\\ &[\text{Proof as in *212·7}]\end{align}\] -/
theorem pm212_701 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {S : α → β → Prop} :
    S ∈ smorbar P Q → dom (imgRel P) = imgRel S ʻʻ dom (imgRel Q) ∧
      fld (segSer P) = imgRel S ʻʻ fld (segSer Q) := by
  intro hS
  refine ⟨?_, cor_fld (cor_XY_seg hS)⟩
  ext A
  rw [cor_D hS]
  exact ⟨fun ⟨B, hB, e⟩ => ⟨B, hB, e⟩, fun ⟨B, hB, e⟩ => ⟨B, hB, e⟩⟩

/-- ✱212·702. \[\begin{align}\vdash :S\in P\overline{\,\text{smor}\,} &Q.\supset .\\ &\text{D}ʻ(P_{\in }\dot{\cap} I) = S_{\in }ʻʻ\text{D}ʻ(Q_{\in }\dot{\cap} I).Cʻ\text{sgm}ʻP = S_{\in }ʻʻCʻ\text{sgm}ʻQ\\ &[\text{Proof as in *212·7}]\end{align}\] -/
theorem pm212_702 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {S : α → β → Prop} :
    S ∈ smorbar P Q → dom (imgRel P ⩀ I) = imgRel S ʻʻ dom (imgRel Q ⩀ I) ∧
      fld (sgm P) = imgRel S ʻʻ fld (sgm Q) := by
  intro hS
  refine ⟨?_, cor_fld (cor_XY_sgm hS)⟩
  ext A
  rw [cor_DI hS]
  exact ⟨fun ⟨B, hB, e⟩ => ⟨B, hB, e⟩, fun ⟨B, hB, e⟩ => ⟨B, hB, e⟩⟩

/-- ✱212·71. \(\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .S_{\in }\upharpoonright Cʻ\varsigma ʻQ_{*}\in (\varsigma ʻP_{*})\overline{\,\text{smor}\,} (\varsigma ʻQ_{*})\) -/
theorem pm212_71 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {S : α → β → Prop} :
    S ∈ smorbar P Q →
      imgRel S ↾ fld (segSer (anc Q)) ∈ smorbar (segSer (anc P)) (segSer (anc Q)) := by
  intro hS
  refine cor_smorbar hS (fun B hB => ?_) (cor_XY_sect hS)
  obtain ⟨D, h | h⟩ := hB
  · exact (segSer_anc_iff.1 h).1.1.1
  · exact (segSer_anc_iff.1 h).1.2.1

/-- ✱212·711. \[\begin{align}&\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .S_{\in }\upharpoonright Cʻ\varsigma ʻQ\in (\varsigma ʻP)\overline{\,\text{smor}\,} (\varsigma ʻQ)\\ &[\text{Proof as in *212·71}]\end{align}\] -/
theorem pm212_711 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {S : α → β → Prop} :
    S ∈ smorbar P Q → imgRel S ↾ fld (segSer Q) ∈ smorbar (segSer P) (segSer Q) := by
  intro hS
  refine cor_smorbar hS (fun B hB => ?_) (cor_XY_seg hS)
  obtain ⟨D, h | h⟩ := hB
  · exact seg_sub_fld h.1.1
  · exact seg_sub_fld h.2

/-- ✱212·712. \[\begin{align}&\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .S_{\in }\upharpoonright Cʻ\text{sgm}ʻP\in (\text{sgm}ʻP)\overline{\,\text{smor}\,} (\text{sgm}ʻQ)\\ &[\text{Proof as in *212·7}]\end{align}\]

**Status.** proved (reading): the e-text prints `S_∈ ↾ C'sgm'P` for `S_∈ ↾ C'sgm'Q`: the converse domain of `S_∈` consists of classes of the field of `Q`, so only the restriction to `C'sgm'Q` is significant (and is the one of ✱212·71·711). -/
theorem pm212_712 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {S : α → β → Prop} :
    S ∈ smorbar P Q → imgRel S ↾ fld (sgm Q) ∈ smorbar (sgm P) (sgm Q) := by
  intro hS
  refine cor_smorbar hS (fun B hB => ?_) (cor_XY_sgm hS)
  obtain ⟨D, h | h⟩ := hB
  · exact (pm211_14.2 h.1.1).1
  · exact (pm211_14.2 h.2).1

/-- ✱212·72. \[\begin{align}&\vdash :P \,\,\text{smor}\, \,Q.\supset .\varsigma ʻP_{*}\,\text{smor}\, \varsigma ʻQ_{*}.\varsigma ʻP \,\,\text{smor}\, \varsigma ʻQ.\text{sgm}ʻP \,\,\text{smor}\, \text{sgm}ʻ Q\\ &[*212·71·711·712]\end{align}\] -/
theorem pm212_72 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} :
    smor P Q → (smor (segSer (anc P)) (segSer (anc Q)) ∧ smor (segSer P) (segSer Q)) ∧
      smor (sgm P) (sgm Q) := by
  rintro ⟨S, hS⟩
  exact ⟨⟨⟨_, pm212_71 hS⟩, ⟨_, pm212_711 hS⟩⟩, ⟨_, pm212_712 hS⟩⟩

end PrincipiaMathematica
