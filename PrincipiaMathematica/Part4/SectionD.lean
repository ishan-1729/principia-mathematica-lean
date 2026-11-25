import PrincipiaMathematica.Defs.Part4

/-!
# Part IV, Section D: Arithmetic of relation-numbers

Volume 2. Numbers: ✱180, ✱181, ✱182, ✱183, ✱184, ✱185, ✱186.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w

/-! ### Helper lemmas for ✱180–✱186 (not propositions of PM) -/

private theorem semi_iff' {α β : Type*} (S : α → β → Prop) (Q : β → β → Prop) (x y : α) :
    (S ⁏ Q) x y ↔ ∃ z w, S x z ∧ S y w ∧ Q z w := by
  rw [semi_apply]; simp only [and_assoc]

/-- Unfold the relations and classes of Part IV to first-order logic. -/
local macro "dsimp'" : tactic => `(tactic| simp only [semi_iff', rcup, rcap, rdiff, rneg, cres,
  dres, bres, fres, couple_apply, cross, mem_unitCls, refs, rels, img, dom, codom, fld,
  Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff, RSub,
  relProd, sumRel, sumCls, Null_eq_empty, Set.mem_empty_iff_false, mem_rl, rNull, rV,
  Set.subset_def, rel_eq_iff, Set.ext_iff, Set.Nonempty, D, Dcnv, C, F, graph, eq_iff_iff, ne_eq,
  I, not_exists, mem_arrow_Cls_one, mem_arrow_one_Cls, mem_arrow_one_one, cnv, exists_imp,
  and_imp, rEx, Desc, TheIs, EDesc, EBang, daggerRel, daggerOp, opL, opR, opSemi, coupleR,
  coupleL, iota, Rfwd, imgRel, cl, Set.mem_univ, true_and, and_true, rsum, addLast, addFirst]
  at *)

section HelpersD

variable {α β γ δ : Type*}

private theorem img_empty (R : α → β → Prop) : R ʻʻ (∅ : Set β) = ∅ := by
  ext x; simp [img]

private theorem null_inter (A : Set α) : (Λ : Set α) ∩ A = ∅ := by
  rw [Null_eq_empty, Set.empty_inter]

private theorem not_mem_null (x : α) : x ∉ (Λ : Set α) := fun h => h rfl

private theorem inter_null_iff {G H : Set γ} : G ∩ H = Λ ↔ Disjoint G H := by
  rw [Null_eq_empty, Set.disjoint_iff_inter_eq_empty]

private theorem graph_relProd_graph (f : β → α) (g : γ → β) :
    graph f ⨾ graph g = graph (fun z => f (g z)) := by
  funext u z; apply propext
  constructor
  · rintro ⟨v, h1, h2⟩
    exact (h1 : u = f v).trans (congrArg f (h2 : v = g z))
  · intro h; exact ⟨g z, h, rfl⟩

/-- `x ∈ C'(S;Q)` when every member of `C'Q` has an `S`-referent. -/
private theorem mem_fld_semi {S : α → β → Prop} {Q : β → β → Prop}
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

private theorem fld_semi_sub {S : α → β → Prop} {Q : β → β → Prop} {x : α}
    (h : x ∈ fld (S ⁏ Q)) : ∃ z, z ∈ fld Q ∧ S x z := by
  rcases h with ⟨y, h | h⟩
  · obtain ⟨z, w, ⟨hxz, -⟩, hzw⟩ := (semi_apply S Q x y).1 h
    exact ⟨z, ⟨w, Or.inl hzw⟩, hxz⟩
  · obtain ⟨z, w, ⟨-, hxw⟩, hzw⟩ := (semi_apply S Q y x).1 h
    exact ⟨w, ⟨z, Or.inr hzw⟩, hxw⟩

private theorem mem_fld_graph_semi {f : β → α} {Q : β → β → Prop} {u : α} :
    u ∈ fld (graph f ⁏ Q) ↔ ∃ z, z ∈ fld Q ∧ u = f z :=
  mem_fld_semi fun z _ => ⟨f z, rfl⟩

private theorem semi_congr {S T : α → β → Prop} {Q : β → β → Prop}
    (h : ∀ x z, z ∈ fld Q → (S x z ↔ T x z)) : S ⁏ Q = T ⁏ Q := by
  funext x y; apply propext
  rw [semi_apply, semi_apply]
  constructor
  · rintro ⟨z, w, ⟨h1, h2⟩, hq⟩
    exact ⟨z, w, ⟨(h x z ⟨w, Or.inl hq⟩).1 h1, (h y w ⟨z, Or.inr hq⟩).1 h2⟩, hq⟩
  · rintro ⟨z, w, ⟨h1, h2⟩, hq⟩
    exact ⟨z, w, ⟨(h x z ⟨w, Or.inl hq⟩).2 h1, (h y w ⟨z, Or.inr hq⟩).2 h2⟩, hq⟩

private theorem graph_semi_congr {f g : β → α} {Q : β → β → Prop}
    (h : ∀ z, z ∈ fld Q → f z = g z) : graph f ⁏ Q = graph g ⁏ Q :=
  semi_congr fun x z hz => by
    show x = f z ↔ x = g z
    rw [h z hz]

private theorem semi_rsum {S : α → β → Prop} {P Q : β → β → Prop}
    (hP : ∀ z, z ∈ fld P → ∃ x, S x z) (hQ : ∀ z, z ∈ fld Q → ∃ x, S x z) :
    S ⁏ (P ⤉ Q) = S ⁏ P ⤉ S ⁏ Q := by
  funext x y; apply propext
  rw [semi_apply, rsum_apply, semi_apply, semi_apply, mem_fld_semi hP, mem_fld_semi hQ]
  constructor
  · rintro ⟨z, w, ⟨h1, h2⟩, (hq | hq) | ⟨hz, hw⟩⟩
    · exact Or.inl (Or.inl ⟨z, w, ⟨h1, h2⟩, hq⟩)
    · exact Or.inl (Or.inr ⟨z, w, ⟨h1, h2⟩, hq⟩)
    · exact Or.inr ⟨⟨z, hz, h1⟩, ⟨w, hw, h2⟩⟩
  · rintro ((⟨z, w, ⟨h1, h2⟩, hq⟩ | ⟨z, w, ⟨h1, h2⟩, hq⟩) | ⟨⟨z, hz, h1⟩, ⟨w, hw, h2⟩⟩)
    · exact ⟨z, w, ⟨h1, h2⟩, Or.inl (Or.inl hq)⟩
    · exact ⟨z, w, ⟨h1, h2⟩, Or.inl (Or.inr hq)⟩
    · exact ⟨z, w, ⟨h1, h2⟩, Or.inr ⟨hz, hw⟩⟩

private theorem graph_semi_rsum (f : β → α) (P Q : β → β → Prop) :
    graph f ⁏ (P ⤉ Q) = graph f ⁏ P ⤉ graph f ⁏ Q :=
  semi_rsum (fun z _ => ⟨f z, rfl⟩) (fun z _ => ⟨f z, rfl⟩)

private theorem rsum_assoc (P Q R : α → α → Prop) : P ⤉ Q ⤉ R = P ⤉ (Q ⤉ R) := by
  funext x y; apply propext
  simp only [rsum_apply, fld_rsum, Set.mem_union]
  tauto

private theorem rsum_rNull (P : α → α → Prop) : P ⤉ rNull = P := by
  funext x y; apply propext
  simp only [rsum_apply]
  have h1 : ¬ (rNull : α → α → Prop) x y := rNull_apply x y
  have h2 : y ∉ fld (rNull : α → α → Prop) := by rintro ⟨z, h | h⟩ <;> exact rNull_apply _ _ h
  tauto

private theorem rNull_rsum (P : α → α → Prop) : rNull ⤉ P = P := by
  funext x y; apply propext
  simp only [rsum_apply]
  have h1 : ¬ (rNull : α → α → Prop) x y := rNull_apply x y
  have h2 : x ∉ fld (rNull : α → α → Prop) := by rintro ⟨z, h | h⟩ <;> exact rNull_apply _ _ h
  tauto

private theorem fld_rNull : fld (rNull : α → α → Prop) = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ ⟨_, h⟩ => h.elim (rNull_apply _ _) (rNull_apply _ _)

private theorem eq_rNull_of_fld {P : α → α → Prop} (h : fld P = ∅) : P = rNull := by
  funext x y; apply propext
  exact ⟨fun hxy => absurd (show x ∈ fld P from ⟨y, Or.inl hxy⟩) (h ▸ Set.notMem_empty x),
    fun hxy => absurd hxy (rNull_apply x y)⟩

private theorem rEx_iff_fld {P : α → α → Prop} : rEx P ↔ (fld P).Nonempty := by
  constructor
  · rintro ⟨x, y, h⟩; exact ⟨x, y, Or.inl h⟩
  · rintro ⟨x, y, h | h⟩
    · exact ⟨x, y, h⟩
    · exact ⟨y, x, h⟩

private theorem ne_rNull_iff {P : α → α → Prop} : P ≠ rNull ↔ rEx P := by
  constructor
  · intro h
    by_contra h'
    exact h (funext fun x => funext fun y => propext
      ⟨fun hxy => (h' ⟨x, y, hxy⟩).elim, fun hxy => absurd hxy (rNull_apply x y)⟩)
  · rintro ⟨x, y, hxy⟩ rfl; exact rNull_apply x y hxy

private theorem graph_semi_rNull (f : β → α) : graph f ⁏ (rNull : β → β → Prop) = rNull := by
  funext x y; apply propext
  rw [semi_apply]
  exact ⟨fun ⟨_, _, _, h⟩ => absurd h (rNull_apply _ _), fun h => absurd h (rNull_apply _ _)⟩

/-! #### Likeness through correlators -/

/-- `S;Q smor Q` when `S` is one-one on `C'Q` and every member of `C'Q` has a referent. -/
private theorem smor_semi_of {S : α → β → Prop} {Q : β → β → Prop}
    (h1 : ∀ x y z, z ∈ fld Q → S x z → S y z → x = y)
    (h2 : ∀ x z w, z ∈ fld Q → w ∈ fld Q → S x z → S x w → z = w)
    (hc : ∀ z, z ∈ fld Q → ∃ x, S x z) : smor (S ⁏ Q) Q := by
  refine ⟨S ↾ fld Q, ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨hx, hz⟩, ⟨hy, -⟩⟩; exact h1 x y z hz hx hy
  · rintro x z w ⟨⟨hz, hzQ⟩, ⟨hw, hwQ⟩⟩; exact h2 x z w hzQ hwQ hz hw
  · ext z
    exact ⟨fun hz => let ⟨x, hx⟩ := hc z hz; ⟨x, hx, hz⟩, fun ⟨_, _, hz⟩ => hz⟩
  · exact semi_congr (fun x z hz => ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩)

/-- The image of `Q` under a function injective on `C'Q` is like `Q` (cf. ✱151·61). -/
private theorem smor_graph {f : β → α} {Q : β → β → Prop}
    (hf : ∀ z w, z ∈ fld Q → w ∈ fld Q → f z = f w → z = w) : smor (graph f ⁏ Q) Q :=
  smor_semi_of (fun x y z _ hx hy => (hx : x = f z).trans (hy : y = f z).symm)
    (fun x z w hz hw hxz hxw => hf z w hz hw ((hxz : x = f z).symm.trans hxw))
    (fun z _ => ⟨f z, rfl⟩)

private theorem smor_graph_inj {f : β → α} (hf : Function.Injective f) (Q : β → β → Prop) :
    smor (graph f ⁏ Q) Q :=
  smor_graph fun _ _ _ _ h => hf h

/-- Likeness of ordinal sums with exclusive fields (✱160·48). -/
private theorem smor_rsum {R S : α → α → Prop} {P Q : β → β → Prop} (hR : smor R P)
    (hS : smor S Q) (hRS : Disjoint (fld R) (fld S)) (hPQ : Disjoint (fld P) (fld Q)) :
    smor (R ⤉ S) (P ⤉ Q) := by
  obtain ⟨T₁, ⟨hT₁, hc₁⟩, rfl⟩ := hR
  obtain ⟨T₂, ⟨hT₂, hc₂⟩, rfl⟩ := hS
  obtain ⟨a₁, b₁⟩ := mem_arrow_one_one.1 hT₁
  obtain ⟨a₂, b₂⟩ := mem_arrow_one_one.1 hT₂
  have e₁ : ∀ z, z ∈ fld P ↔ ∃ x, T₁ x z := fun z => by rw [hc₁]; rfl
  have e₂ : ∀ z, z ∈ fld Q ↔ ∃ x, T₂ x z := fun z => by rw [hc₂]; rfl
  have k₁ : T₁ ⁏ P = (T₁ ⊍ T₂) ⁏ P := semi_congr fun x z hz =>
    ⟨Or.inl, fun h => h.elim id fun h2 =>
      absurd ((e₂ z).2 ⟨x, h2⟩) (Set.disjoint_left.1 hPQ hz)⟩
  have k₂ : T₂ ⁏ Q = (T₁ ⊍ T₂) ⁏ Q := semi_congr fun x z hz =>
    ⟨Or.inr, fun h => h.elim (fun h1 =>
      absurd ((e₁ z).2 ⟨x, h1⟩) (Set.disjoint_right.1 hPQ hz)) id⟩
  have hP' : ∀ z, z ∈ fld P → ∃ x, (T₁ ⊍ T₂) x z := fun z hz =>
    let ⟨x, hx⟩ := (e₁ z).1 hz; ⟨x, Or.inl hx⟩
  have hQ' : ∀ z, z ∈ fld Q → ∃ x, (T₁ ⊍ T₂) x z := fun z hz =>
    let ⟨x, hx⟩ := (e₂ z).1 hz; ⟨x, Or.inr hx⟩
  have hd₁ : ∀ x z, T₁ x z → x ∈ fld (T₁ ⁏ P) := fun x z h =>
    (mem_fld_semi fun z hz => (e₁ z).1 hz).2 ⟨z, (e₁ z).2 ⟨x, h⟩, h⟩
  have hd₂ : ∀ x z, T₂ x z → x ∈ fld (T₂ ⁏ Q) := fun x z h =>
    (mem_fld_semi fun z hz => (e₂ z).1 hz).2 ⟨z, (e₂ z).2 ⟨x, h⟩, h⟩
  rw [k₁, k₂, ← semi_rsum hP' hQ']
  refine smor_semi_of ?_ ?_ ?_
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
private theorem smor_corr {R : α → α → Prop} {P : β → β → Prop} (h : smor R P) :
    ∃ T : α → β → Prop, ((∀ x y z, T x z → T y z → x = y) ∧ (∀ x z w, T x z → T x w → z = w)) ∧
      (∀ z, z ∈ fld P ↔ ∃ x, T x z) ∧ R = T ⁏ P := by
  obtain ⟨T, ⟨hT, hc⟩, rfl⟩ := h
  obtain ⟨a, b⟩ := mem_arrow_one_one.1 hT
  exact ⟨T, ⟨fun x y z h1 h2 => a x y z ⟨h1, h2⟩, fun x z w h1 h2 => b x z w ⟨h1, h2⟩⟩,
    fun z => by rw [hc]; rfl, rfl⟩

private theorem smor_rNull_iff' {P : α → α → Prop} : smor P (rNull : β → β → Prop) ↔ P = rNull := by
  constructor
  · intro h
    obtain ⟨e, -⟩ := smor_iff_exists_equiv.1 h
    apply eq_rNull_of_fld
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    obtain ⟨_, _, h⟩ := e ⟨x, hx⟩
    exact h.elim (rNull_apply _ _) (rNull_apply _ _)
  · rintro rfl
    refine ⟨rNull, ⟨mem_arrow_one_one.2 ⟨fun _ _ _ h => absurd h.1 (rNull_apply _ _),
      fun _ _ _ h => absurd h.1 (rNull_apply _ _)⟩, ?_⟩, ?_⟩
    · rw [fld_rNull]; ext z; simp only [Set.mem_empty_iff_false, false_iff]
      rintro ⟨_, h⟩; exact rNull_apply _ _ h
    · funext x y; apply propext; rw [semi_apply]
      exact ⟨fun h => absurd h (rNull_apply _ _), fun ⟨_, _, h, _⟩ => absurd h.1 (rNull_apply _ _)⟩

private theorem smor_preserves {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q)
    (hP : rEx P) : rEx Q := by
  obtain ⟨x, y, hxy⟩ := hP
  obtain ⟨e, he⟩ := smor_iff_exists_equiv.1 h
  exact ⟨e ⟨x, y, Or.inl hxy⟩, e ⟨y, x, Or.inr hxy⟩, (he _ _).1 hxy⟩

/-! #### Relation-numbers -/

private theorem nr_eq_n₀r_of_mem {P : β → β → Prop} {X : γ → γ → Prop} (h : X ∈ nr γ P) :
    nr γ P = n₀r X := by
  rw [n₀r_eq_nr]; exact (nr_eq_nr_of_smor h).symm

/-- A member of `NR` is `Λ` or a homogeneous relation-number. -/
private theorem NR_cases {μ : Set (α → α → Prop)} (h : μ ∈ NR β) :
    μ = ∅ ∨ ∃ P, μ = n₀r P := by
  obtain ⟨P', rfl⟩ := h
  rcases Set.eq_empty_or_nonempty (nr α P') with h0 | ⟨X, hX⟩
  · exact Or.inl h0
  · exact Or.inr ⟨X, nr_eq_n₀r_of_mem hX⟩

private theorem n₀r_ne_empty (P : α → α → Prop) : n₀r P ≠ ∅ := (n₀r_nonempty P).ne_empty

private theorem n₀r_mem_NR (P : α → α → Prop) : n₀r P ∈ NR α := ⟨P, n₀r_eq_nr P⟩

private theorem smor_img_n₀r (P : α → α → Prop) :
    (smor ʻʻ n₀r P : Set (γ → γ → Prop)) = nr γ P := by
  ext R
  constructor
  · rintro ⟨P', hP', hR⟩; exact smor_trans hR (mem_n₀r.1 hP')
  · intro h; exact ⟨P, self_mem_n₀r P, h⟩

private theorem smor_img_empty : (smor ʻʻ (∅ : Set (α → α → Prop)) : Set (γ → γ → Prop)) = ∅ := by
  ext R; simp [img]

private theorem mem_nr_of_smor {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop}
    (hR : smor R P) (h : smor P Q) : R ∈ nr γ Q := smor_trans hR h

private theorem zero_r_eq_nr : (zero_r : Set (γ → γ → Prop)) = nr γ (rNull : β → β → Prop) := by
  ext R; exact (smor_rNull_iff').symm

private theorem zero_r_eq_n₀r : (zero_r : Set (α → α → Prop)) = n₀r rNull := by
  rw [n₀r_eq_nr]; exact zero_r_eq_nr

private theorem nr_eq_zero_r_iff {P : β → β → Prop} :
    nr γ P = (zero_r : Set (γ → γ → Prop)) ↔ P = rNull := by
  constructor
  · intro h
    have : (rNull : γ → γ → Prop) ∈ nr γ P := by rw [h]; rfl
    exact smor_rNull_iff'.1 (smor_symm this)
  · rintro rfl; exact zero_r_eq_nr.symm

private theorem eq_of_n₀r_eq {μ : Set (α → α → Prop)} {P : α → α → Prop} (h : μ = n₀r P) :
    P ∈ μ := h ▸ self_mem_n₀r P

/-- `C''Nr'Q = Nc'C'Q` (✱152·7), in any type. -/
private theorem C_img_nr {Q : β → β → Prop} : C ʻʻ nr γ Q = nc γ (fld Q) := by
  ext X
  constructor
  · rintro ⟨R, hR, rfl⟩
    exact sm_fld_of_smor hR
  · intro h
    obtain ⟨S, ⟨hS, hdom⟩, hcod⟩ := sm_iff.1 h
    obtain ⟨a, b⟩ := mem_arrow_one_one.1 hS
    refine ⟨S ⁏ Q, ⟨S, ⟨hS, hcod⟩, rfl⟩, ?_⟩
    show X = fld (S ⁏ Q)
    rw [hdom]
    ext x
    rw [mem_fld_semi (fun z hz => by rw [hcod] at hz; exact hz)]
    constructor
    · rintro ⟨z, hz⟩; exact ⟨z, by rw [hcod]; exact ⟨x, hz⟩, hz⟩
    · rintro ⟨z, -, hz⟩; exact ⟨z, hz⟩

end HelpersD

variable {α β γ δ : Type*}

section Helpers180

private theorem coupleR_iota (B : Set β) :
    (coupleR B ⨾ iota : (Set α → Set β → Prop) → α → Prop) = graph (fun x => ι x ↓ B) :=
  graph_relProd_graph (fun X => X ↓ B) (refs I)

private theorem coupleL_iota (A : Set α) :
    (coupleL A ⨾ iota : (Set α → Set β → Prop) → β → Prop) = graph (fun y => A ↓ ι y) :=
  graph_relProd_graph (fun Y => A ↓ Y) (refs I)

/-- `P + Q` as the sum of two images of `P` and `Q` (✱180·01). -/
private theorem rplus_eq (P : α → α → Prop) (Q : β → β → Prop) :
    P +ᵣ Q = graph (fun x => ι x ↓ (Λ ∩ fld Q)) ⁏ P ⤉ graph (fun y => (Λ ∩ fld P) ↓ ι y) ⁏ Q := by
  show (coupleR (Λ ∩ fld Q) ⁏ iota ⁏ P) ⤉ (coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q) = _
  rw [semi_semi, semi_semi, coupleR_iota, coupleL_iota]

private theorem smor_lft (P : α → α → Prop) (B : Set β) :
    smor (graph (fun x => ι x ↓ B) ⁏ P) P :=
  smor_graph_inj (fun x y h => unitCls_injective (couple_eq_couple_iff.1 h).1) P

private theorem smor_rgt (A : Set α) (Q : β → β → Prop) :
    smor (graph (fun y => A ↓ ι y) ⁏ Q) Q :=
  smor_graph_inj (fun x y h => unitCls_injective (couple_eq_couple_iff.1 h).2) Q

private theorem disj_lft_rgt (P : α → α → Prop) (Q : β → β → Prop) (A : Set α) (B : Set β) :
    Disjoint (fld (graph (fun x => ι x ↓ (Λ ∩ B)) ⁏ P)) (fld (graph (fun y => A ↓ ι y) ⁏ Q)) := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  obtain ⟨x, -, rfl⟩ := mem_fld_graph_semi.1 hu
  obtain ⟨y, -, h⟩ := mem_fld_graph_semi.1 hu'
  have := (couple_eq_couple_iff.1 h).2
  have hy : y ∈ Λ ∩ B := this ▸ (rfl : y = y)
  exact not_mem_null y hy.1

/-- `P + Q` is the sum of two exclusive relations like `P` and `Q`. -/
private theorem rplus_split (P : α → α → Prop) (Q : β → β → Prop) :
    ∃ L R, P +ᵣ Q = L ⤉ R ∧ (smor L P ∧ smor R Q) ∧ Disjoint (fld L) (fld R) :=
  ⟨_, _, rplus_eq P Q, ⟨smor_lft P _, smor_rgt _ Q⟩, disj_lft_rgt P Q _ _⟩

private theorem smor_rsum_rplus {R S : δ → δ → Prop} {P : α → α → Prop} {Q : β → β → Prop}
    (hR : smor R P) (hS : smor S Q) (h : Disjoint (fld R) (fld S)) : smor (R ⤉ S) (P +ᵣ Q) := by
  obtain ⟨L, R', e, ⟨hL, hR'⟩, hd⟩ := rplus_split P Q
  rw [e]
  exact smor_rsum (smor_trans hR (smor_symm hL)) (smor_trans hS (smor_symm hR')) h hd

/-- `R smor P . S smor Q . ⊃ . R + S smor P + Q` (✱180·15). -/
private theorem smor_rplus {R : γ → γ → Prop} {S : δ → δ → Prop} {P : α → α → Prop}
    {Q : β → β → Prop} (hR : smor R P) (hS : smor S Q) : smor (R +ᵣ S) (P +ᵣ Q) := by
  obtain ⟨L, R', e, ⟨hL, hR'⟩, hd⟩ := rplus_split R S
  rw [e]
  exact smor_rsum_rplus (smor_trans hL hR) (smor_trans hR' hS) hd

private theorem smor_rsum_iff {P Q : α → α → Prop} (hPQ : Disjoint (fld P) (fld Q))
    {Z : β → β → Prop} : smor Z (P ⤉ Q) ↔
      ∃ R S, ((smor R P ∧ smor S Q) ∧ Disjoint (fld R) (fld S)) ∧ Z = R ⤉ S := by
  constructor
  · intro h
    obtain ⟨T, ⟨a, b⟩, hc, rfl⟩ := smor_corr h
    have hP : ∀ z, z ∈ fld P → ∃ x, T x z := fun z hz =>
      (hc z).1 (by rw [fld_rsum]; exact Or.inl hz)
    have hQ : ∀ z, z ∈ fld Q → ∃ x, T x z := fun z hz =>
      (hc z).1 (by rw [fld_rsum]; exact Or.inr hz)
    refine ⟨T ⁏ P, T ⁏ Q, ⟨⟨smor_semi_of (fun x y z _ => a x y z)
      (fun x z w _ _ => b x z w) hP, smor_semi_of (fun x y z _ => a x y z)
      (fun x z w _ _ => b x z w) hQ⟩, ?_⟩, semi_rsum hP hQ⟩
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨z, hz, hxz⟩ := fld_semi_sub hx
    obtain ⟨w, hw, hxw⟩ := fld_semi_sub hx'
    rw [b x z w hxz hxw] at hz
    exact Set.disjoint_left.1 hPQ hz hw
  · rintro ⟨R, S, ⟨⟨hR, hS⟩, hd⟩, rfl⟩
    exact smor_rsum hR hS hd hPQ

private theorem smor_rplus_iff {P : α → α → Prop} {Q : β → β → Prop} {Z : γ → γ → Prop} :
    smor Z (P +ᵣ Q) ↔
      ∃ R S, ((smor R P ∧ smor S Q) ∧ Disjoint (fld R) (fld S)) ∧ Z = R ⤉ S := by
  obtain ⟨L, R', e, ⟨hL, hR'⟩, hd⟩ := rplus_split P Q
  constructor
  · intro h
    rw [e] at h
    obtain ⟨R, S, ⟨⟨hR, hS⟩, hRS⟩, rfl⟩ := (smor_rsum_iff hd).1 h
    exact ⟨R, S, ⟨⟨smor_trans hR hL, smor_trans hS hR'⟩, hRS⟩, rfl⟩
  · rintro ⟨R, S, ⟨⟨hR, hS⟩, hRS⟩, rfl⟩
    exact smor_rsum_rplus hR hS hRS

private theorem smor_rplus_rNull (P : α → α → Prop) : smor (P +ᵣ (rNull : β → β → Prop)) P := by
  rw [rplus_eq, graph_semi_rNull, rsum_rNull]; exact smor_lft P _

private theorem smor_rNull_rplus (P : α → α → Prop) : smor ((rNull : β → β → Prop) +ᵣ P) P := by
  rw [rplus_eq, graph_semi_rNull, rNull_rsum]; exact smor_rgt _ P

private theorem rsum_mono {P P' Q Q' : α → α → Prop} (h1 : P ⪽ P') (h2 : Q ⪽ Q') :
    P ⤉ Q ⪽ P' ⤉ Q' := by
  rintro x y ((h | h) | ⟨hx, hy⟩)
  · exact Or.inl (Or.inl (h1 _ _ h))
  · exact Or.inl (Or.inr (h2 _ _ h))
  · exact Or.inr ⟨fld_mono h1 hx, fld_mono h2 hy⟩

private theorem rplus_sub_rV (P : α → α → Prop) (Q : β → β → Prop) :
    P +ᵣ Q ⪽ (rV : α → α → Prop) +ᵣ (rV : β → β → Prop) := by
  rw [rplus_eq, rplus_eq, null_inter, null_inter, null_inter, null_inter]
  exact rsum_mono (semi_mono _ fun _ _ _ => ⟨rfl, rfl⟩) (semi_mono _ fun _ _ _ => ⟨rfl, rfl⟩)

private theorem rEx_rplus_left {P : α → α → Prop} (Q : β → β → Prop) (h : rEx P) :
    rEx (P +ᵣ Q) := by
  obtain ⟨L, R, e, ⟨hL, -⟩, -⟩ := rplus_split P Q
  obtain ⟨x, y, hxy⟩ := smor_preserves (smor_symm hL) h
  rw [e]; exact ⟨x, y, Or.inl (Or.inl hxy)⟩

private theorem rEx_rplus_right (P : α → α → Prop) {Q : β → β → Prop} (h : rEx Q) :
    rEx (P +ᵣ Q) := by
  obtain ⟨L, R, e, ⟨-, hR⟩, -⟩ := rplus_split P Q
  obtain ⟨x, y, hxy⟩ := smor_preserves (smor_symm hR) h
  rw [e]; exact ⟨x, y, Or.inl (Or.inr hxy)⟩

/-! #### `μ +̇ ν` -/

private theorem n₀r_nrAdd_n₀r (P : α → α → Prop) (Q : β → β → Prop) :
    (n₀r P ∔ n₀r Q : Set (γ → γ → Prop)) = nr γ (P +ᵣ Q) := by
  ext Z
  constructor
  · rintro ⟨P', Q', ⟨hP, hQ⟩, h⟩
    exact smor_trans h (smor_rplus (n₀r_eq_n₀r_iff.1 hP.symm) (n₀r_eq_n₀r_iff.1 hQ.symm))
  · intro h; exact ⟨P, Q, ⟨rfl, rfl⟩, h⟩

private theorem nrAdd_of {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} {P : α → α → Prop}
    {Q : β → β → Prop} (hμ : μ = n₀r P) (hν : ν = n₀r Q) :
    (μ ∔ ν : Set (γ → γ → Prop)) = nr γ (P +ᵣ Q) := by
  subst hμ hν; exact n₀r_nrAdd_n₀r P Q

private theorem nrAdd_eq_empty_of_left {μ : Set (α → α → Prop)} (h : ∀ P, μ ≠ n₀r P)
    (ν : Set (β → β → Prop)) : (μ ∔ ν : Set (γ → γ → Prop)) = ∅ := by
  ext Z; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨P, Q, ⟨hP, -⟩, -⟩; exact h P hP

private theorem nrAdd_eq_empty_of_right (μ : Set (α → α → Prop)) {ν : Set (β → β → Prop)}
    (h : ∀ Q, ν ≠ n₀r Q) : (μ ∔ ν : Set (γ → γ → Prop)) = ∅ := by
  ext Z; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨P, Q, ⟨-, hQ⟩, -⟩; exact h Q hQ

private theorem empty_nrAdd (ν : Set (β → β → Prop)) :
    ((∅ : Set (α → α → Prop)) ∔ ν : Set (γ → γ → Prop)) = ∅ :=
  nrAdd_eq_empty_of_left (fun P h => n₀r_ne_empty P h.symm) ν

private theorem nrAdd_empty (μ : Set (α → α → Prop)) :
    (μ ∔ (∅ : Set (β → β → Prop)) : Set (γ → γ → Prop)) = ∅ :=
  nrAdd_eq_empty_of_right μ (fun P h => n₀r_ne_empty P h.symm)

/-- In a type adequate for `μ +̇ ν`, `Nr'(P + Q)` exists for all `P`, `Q`. -/
private theorem AdeqNrAdd.nr_nonempty {W : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    (h : AdeqNrAdd W μ ν) (P : α → α → Prop) (Q : β → β → Prop) : (nr W (P +ᵣ Q)).Nonempty := by
  have h' : (nr W ((rV : α → α → Prop) +ᵣ (rV : β → β → Prop))).Nonempty := by
    have := h; unfold AdeqNrAdd at this; rwa [n₀r_nrAdd_n₀r] at this
  exact nr_nonempty_of_rsub h' (rplus_sub_rV P Q)

/-- With `W` adequate, `N₀r'P +̇ N₀r'Q` in `W` is a homogeneous relation-number. -/
private theorem AdeqNrAdd.eq_n₀r {W : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    (h : AdeqNrAdd W μ ν) (P : α → α → Prop) (Q : β → β → Prop) :
    ∃ X : W → W → Prop, smor X (P +ᵣ Q) ∧ (n₀r P ∔ n₀r Q : Set (W → W → Prop)) = n₀r X := by
  obtain ⟨X, hX⟩ := h.nr_nonempty P Q
  exact ⟨X, hX, (n₀r_nrAdd_n₀r P Q).trans (nr_eq_n₀r_of_mem hX)⟩

/-- An existent relation-number in `γ` is the relation-number of a relation on `Set γ`. -/
private theorem n₀r_mem_NR_set (Z : γ → γ → Prop) : n₀r Z ∈ NR (Set γ) :=
  ⟨graph (fun x => ι x) ⁏ Z, by
    rw [n₀r_eq_nr]
    exact nr_eq_nr_of_smor (smor_symm (smor_graph_inj (fun x y h => unitCls_injective h) Z))⟩

private theorem empty_mem_NR_set : (∅ : Set (γ → γ → Prop)) ∈ NR (Set γ) := by
  refine ⟨rV, (Set.eq_empty_iff_forall_notMem.2 fun R hR => ?_).symm⟩
  obtain ⟨f, hf⟩ := nr_nonempty_iff.1 ⟨R, hR⟩
  have hmem : ∀ A : Set γ, A ∈ fld (rV : Set γ → Set γ → Prop) := fun A => ⟨A, Or.inl ⟨rfl, rfl⟩⟩
  exact Function.cantor_injective (fun A => f ⟨A, hmem A⟩)
    (fun A B e => congrArg Subtype.val (hf e))

private theorem graph_semi_couple (f : β → α) (x y : β) : graph f ⁏ (x ↓ y) = f x ↓ f y := by
  funext u v; apply propext
  rw [semi_apply]
  constructor
  · rintro ⟨z, w, ⟨hu, hv⟩, hz, hw⟩
    exact ⟨(hu : u = f z).trans (congrArg f hz), (hv : v = f w).trans (congrArg f hw)⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨x, y, ⟨rfl, rfl⟩, rfl, rfl⟩

private theorem fld_couple {x y : α} : fld (x ↓ y) = {x, y} := by
  ext z
  constructor
  · rintro ⟨w, ⟨h, -⟩ | ⟨-, h⟩⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨y, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨x, Or.inr ⟨rfl, rfl⟩⟩

/-- `a ≠ b . x ≠ y . ⊃ . a ↓ b smor x ↓ y` (cf. ✱153·21). -/
private theorem smor_couple {a b : α} {x y : β} (hab : a ≠ b) (hxy : x ≠ y) :
    smor (a ↓ b) (x ↓ y) := by
  classical
  have e : graph (fun z => if z = x then a else b) ⁏ (x ↓ y) = a ↓ b := by
    rw [graph_semi_couple]; simp [hxy.symm]
  rw [← e]
  refine smor_graph fun z w hz hw h => ?_
  rw [fld_couple] at hz hw
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  · rfl
  · simp [hxy.symm] at h; exact absurd h hab
  · simp [hxy.symm] at h; exact absurd h.symm hab
  · rfl

private theorem smor_couple_inv {R : α → α → Prop} {x y : β} (hxy : x ≠ y) (h : smor R (x ↓ y)) :
    ∃ a b, a ≠ b ∧ R = a ↓ b := by
  obtain ⟨T, ⟨ha, hb⟩, hc, rfl⟩ := smor_corr h
  obtain ⟨a, hax⟩ := (hc x).1 ⟨y, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨b, hby⟩ := (hc y).1 ⟨x, Or.inr ⟨rfl, rfl⟩⟩
  refine ⟨a, b, fun e => hxy (hb a x y hax (e ▸ hby)), ?_⟩
  funext u v; apply propext
  rw [semi_apply]
  constructor
  · rintro ⟨z, w, ⟨hu, hv⟩, rfl, rfl⟩
    exact ⟨ha u a z hu hax, ha v b w hv hby⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨x, y, ⟨hax, hby⟩, rfl, rfl⟩

private theorem two_r_eq_nr {x y : β} (hxy : x ≠ y) :
    (two_r : Set (γ → γ → Prop)) = nr γ (x ↓ y) := by
  ext R
  constructor
  · rintro ⟨a, b, hab, rfl⟩; exact smor_couple hab hxy
  · intro h; exact smor_couple_inv hxy h

private theorem two_r_eq_n₀r {x y : α} (hxy : x ≠ y) :
    (two_r : Set (α → α → Prop)) = n₀r (x ↓ y) := by
  rw [n₀r_eq_nr]; exact two_r_eq_nr hxy

/-- `ν ∈ NR . ⊃ : ν = Λ . ∨ . (∃Q) . ν = N₀r'Q`, with emptiness of `μ +̇ ν`. -/
private theorem nrAdd_cases_NR {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    (hμ : μ = ∅ ∨ ∃ P, μ = n₀r P) (hν : ν = ∅ ∨ ∃ Q, ν = n₀r Q) :
    (∃ P Q, μ = n₀r P ∧ ν = n₀r Q) ∨ (μ = ∅ ∨ ν = ∅) := by
  rcases hμ with h | ⟨P, hP⟩
  · exact Or.inr (Or.inl h)
  rcases hν with h | ⟨Q, hQ⟩
  · exact Or.inr (Or.inr h)
  exact Or.inl ⟨P, Q, hP, hQ⟩

end Helpers180

/-- The printed form of ✱180·212 fails: `Z = x ↓ y ∪̇ y ↓ x` satisfies the right-hand side with
`μ = Nr'(x ↓ y)` (so `μ +̇ 0_r = 2_r`), `ν = 0_r`, `R = x ↓ y`, but `Z ∼∈ 2_r`. -/
theorem pm180_212_printed_false : ¬ ∀ (μ ν : Set (Bool → Bool → Prop)) (Z : Bool → Bool → Prop),
    (μ ∈ NR Bool ∧ ν ∈ NR Bool) → (Z ∈ (μ ∔ ν : Set (Bool → Bool → Prop)) ↔
      ∃ R : Bool → Bool → Prop, (R ∈ smor ʻʻ μ ∧ R ⪽ Z) ∧ Z ⥏ (fld R)ᶜ ∈ smor ʻʻ ν) := by
  intro h
  let Z : Bool → Bool → Prop := true ↓ false ⊍ false ↓ true
  have hμ : nr Bool (true ↓ false) ∈ NR Bool := nr_mem_NR _
  have hν : (zero_r : Set (Bool → Bool → Prop)) ∈ NR Bool := ⟨rNull, zero_r_eq_nr⟩
  have key := (h (nr Bool (true ↓ false)) zero_r Z ⟨hμ, hν⟩).2 ⟨true ↓ false, ⟨⟨true ↓ false,
    self_mem_nr _, smor_refl _⟩, fun _ _ hxy => Or.inl hxy⟩, rNull, rfl, ?_⟩
  · obtain ⟨P, Q, ⟨hP, hQ⟩, hZ⟩ := key
    have hQ0 : Q = rNull := by
      have : Q ∈ (zero_r : Set (Bool → Bool → Prop)) := hQ ▸ self_mem_n₀r Q
      exact this
    subst hQ0
    have hP' : smor P (true ↓ false) := (eq_of_n₀r_eq hP : P ∈ nr Bool (true ↓ false))
    have hZ' : smor Z (true ↓ false) :=
      smor_trans hZ (smor_trans (smor_rplus_rNull P) hP')
    obtain ⟨e, he⟩ := smor_iff_exists_equiv.1 hZ'
    have ht : true ∈ fld Z := ⟨false, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
    have hf : false ∈ fld Z := ⟨true, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩
    have h1 := (he ⟨true, ht⟩ ⟨false, hf⟩).1 (Or.inl ⟨rfl, rfl⟩)
    have h2 := (he ⟨false, hf⟩ ⟨true, ht⟩).1 (Or.inr ⟨rfl, rfl⟩)
    have := h1.2.symm.trans h2.1
    exact Bool.noConfusion this
  · show smor (Z ⥏ (fld (true ↓ false))ᶜ) rNull
    rw [smor_rNull_iff']
    funext a b; apply propext
    rw [fld_couple]
    constructor
    · rintro ⟨⟨ha, -⟩, -⟩
      exact absurd (by cases a <;> simp) ha
    · intro hab; exact absurd hab (rNull_apply _ _)

/-!
## [✱180] The sum of two relation-numbers

*(Vol. 2, p. 477)*

> *Summary of* *180.
>
> …

**Lean reading.** `P + Q` is `P +ᵣ Q` (`rplus`, a relation between classes `Set α → Set β → Prop` for `P` on
`α`, `Q` on `β`); `↓(Λ ∩ C'Q);ι;P` is `coupleR (Λ ∩ fld Q) ⁏ iota ⁏ P`, `(Λ ∩ C'P)↓;ι;Q` is
`coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q`. `μ +̇ ν` is `μ ∔ ν` with its actual type `γ` implicit (fixed by
an ascription); an argument `Nr'P` of `+̇` is `n₀r P` (normal adjustment, ✱180·03·031).
`μ, ν ∈ NR` is `μ ∈ NR β₁ ∧ ν ∈ NR β₂` with independent types; the ambiguous `NR` of a conclusion
is taken in the type PM's proof puts it in (as for `NC` in ✱110). The inner sums of ✱180·54–·56,
`0_r`, `2_r` and `C''Nr'P` in arithmetical positions have their own types (IIT), with adequacy
hypotheses (none for `0_r`). `C''μ` is `C ʻʻ μ`, `Nc'C'P` in an arithmetical position is
`n₀c (fld P)`.

**Status.** proved (all propositions; ✱180·01·02·03·031·531·561 definition; ✱180·151·21·22·3·4·42·54·541·55·551·56·642·7 proved (reading), ✱180·212 proved (corrected), see their docstrings)
-/

/-- ✱180·01 (Df). \(P + Q = {\downarrow (\Lambda \cap CʻQ)^{;}{℩}^{;}P} \unicode{x2909} \{(\Lambda \cap CʻP) \downarrow ^{;}\iota ^{;}Q\} \quad\text{Df}\) -/
theorem pm180_01 {P : α → α → Prop} {Q : β → β → Prop} :
    P +ᵣ Q = (coupleR (Λ ∩ fld Q) ⁏ iota ⁏ P) ⤉ (coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q) := rfl

/-- ✱180·02 (Df). \(\mu \dot{+} \nu = \hat{R} \{(\exists P,Q) . \mu = \text{N}_0\text{r}ʻP . \nu = \text{N}_0\text{r}ʻQ . R\,\text{smor}\,(P + Q)\} \quad\text{Df}\) -/
theorem pm180_02 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} : (μ ∔ ν : Set (γ → γ → Prop)) =
    {R | ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (P +ᵣ Q)} :=
  rfl

/-- ✱180·03 (Df). \(\text{Nr}ʻP \dot{+} \nu = \text{N}_0\text{r}ʻP \dot{+} \nu \quad\text{Df}\)

A rule of translation (normal adjustment): an argument `Nr'P` of `+̇` is written `n₀r P`; the
target is the identity of the two readings. -/
theorem pm180_03 {P : α → α → Prop} {ν : Set (β → β → Prop)} :
    (n₀r P ∔ ν : Set (γ → γ → Prop)) = n₀r P ∔ ν := rfl

/-- ✱180·031 (Df). \(\mu \dot{+} \text{Nr}ʻQ = \mu \dot{+} \text{N}_0\text{r}ʻQ \quad\text{Df}\)

A rule of translation (normal adjustment), as ✱180·03. -/
theorem pm180_031 {μ : Set (α → α → Prop)} {Q : β → β → Prop} :
    (μ ∔ n₀r Q : Set (γ → γ → Prop)) = μ ∔ n₀r Q := rfl

/-- ✱180·1. \(\vdash . P + Q = {\downarrow (\Lambda \cap CʻQ)^{;}{℩}^{;}P} \unicode{x2909} \{(\Lambda \cap CʻP) \downarrow ^{;}{℩}^{;}Q\} \quad[(*180·01)]\) -/
theorem pm180_1 {P : α → α → Prop} {Q : β → β → Prop} :
    P +ᵣ Q = (coupleR (Λ ∩ fld Q) ⁏ iota ⁏ P) ⤉ (coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q) := rfl

/-- ✱180·101. \[\begin{align}\vdash . Cʻ \downarrow &(\Lambda \cap CʻQ)^{;}{℩}^{;}P = \downarrow (\Lambda \cap CʻQ)ʻʻ{℩}ʻʻCʻP.\\ &Cʻ(\Lambda \cap CʻP) \downarrow ^{;}\iota {℩}^{;}Q = (\Lambda \cap CʻP) \downarrow ʻʻ{℩}ʻʻCʻQ \quad[*150·22]\end{align}\]

(The e-text's `ι℩;Q` in the second formula is `ι;Q`.) -/
theorem pm180_101 {P : α → α → Prop} {Q : β → β → Prop} :
    fld (coupleR (Λ ∩ fld Q) ⁏ iota ⁏ P) = coupleR (Λ ∩ fld Q) ʻʻ iota ʻʻ fld P ∧
      fld (coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q) = coupleL (Λ ∩ fld P) ʻʻ iota ʻʻ fld Q := by
  constructor
  · rw [show coupleR (Λ ∩ fld Q) = graph (fun x : Set α => x ↓ (Λ ∩ fld Q)) from rfl,
      fld_semi_graph, show (iota : Set α → α → Prop) = graph (refs I) from rfl, fld_semi_graph]
  · rw [show coupleL (Λ ∩ fld P) = graph (fun y : Set β => (Λ ∩ fld P) ↓ y) from rfl,
      fld_semi_graph, show (iota : Set β → β → Prop) = graph (refs I) from rfl, fld_semi_graph]

/-- ✱180·11. \(\vdash . Cʻ \downarrow (\Lambda \cap CʻQ)^{;}{℩}^{;}P \cap Cʻ(\Lambda \cap CʻP) \downarrow ^{;}{℩}^{;}Q = \Lambda \quad[*180·101 . *110·11]\) -/
theorem pm180_11 {P : α → α → Prop} {Q : β → β → Prop} :
    fld (coupleR (Λ ∩ fld Q) ⁏ iota ⁏ P) ∩ fld (coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q) = Λ := by
  rw [semi_semi, semi_semi, coupleR_iota, coupleL_iota, inter_null_iff]
  exact disj_lft_rgt P Q _ _

/-- ✱180·111. \(\vdash . Cʻ(P + Q) = CʻP + CʻQ\) -/
theorem pm180_111 {P : α → α → Prop} {Q : β → β → Prop} : fld (P +ᵣ Q) = fld P +ₐ fld Q :=
  fld_rplus P Q

/-- ✱180·12. \(\vdash . \downarrow (\Lambda \cap CʻP)^{;}{℩}^{;}P \,\text{smor} P . (\Lambda \cap CʻP) \downarrow ^{;}{℩}^{;}Q \,\text{smor}\, Q \quad[*151·61·64·65]\) -/
theorem pm180_12 {P : α → α → Prop} {Q : β → β → Prop} :
    smor (coupleR (Λ ∩ fld P) ⁏ iota ⁏ P) P ∧ smor (coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q) Q := by
  rw [semi_semi, semi_semi, coupleR_iota, coupleL_iota]
  exact ⟨smor_lft P _, smor_rgt _ Q⟩

/-- ✱180·13. \(\vdash : R \,\text{smor}\, P . S \,\text{smor}\, Q . CʻR \cap CʻS = \Lambda . \supset . R \unicode{x2909} S \,\text{smor}\, P + Q\) -/
theorem pm180_13 {R S : δ → δ → Prop} {P : α → α → Prop} {Q : β → β → Prop} :
    (smor R P ∧ smor S Q) ∧ fld R ∩ fld S = Λ → smor (R ⤉ S) (P +ᵣ Q) := by
  rintro ⟨⟨hR, hS⟩, h⟩
  exact smor_rsum_rplus hR hS (inter_null_iff.1 h)

/-- ✱180·14. \(\vdash : CʻP \cap CʻQ = \Lambda . \supset . P \unicode{x2909} Q \,\text{smor}\, P + Q \quad[*180·13 . *151·13]\) -/
theorem pm180_14 {P Q : α → α → Prop} : fld P ∩ fld Q = Λ → smor (P ⤉ Q) (P +ᵣ Q) := fun h =>
  pm180_13 ⟨⟨smor_refl P, smor_refl Q⟩, h⟩

/-- ✱180·15. \(\vdash : R \,\text{smor}\, P . S \,\text{smor}\, Q . \supset . R + S \,\text{smor}\, P + Q\) -/
theorem pm180_15 {R : γ → γ → Prop} {S : δ → δ → Prop} {P : α → α → Prop} {Q : β → β → Prop} :
    smor R P ∧ smor S Q → smor (R +ᵣ S) (P +ᵣ Q) := fun ⟨hR, hS⟩ => smor_rplus hR hS

/-- ✱180·151. \[\begin{align}\vdash \colon\ldotp &CʻP\cap C\supset Q=\Lambda .\supset :Z\,\text{smor}\,(P\unicode{x2909}Q).\equiv .\\ &(\exists R,S).R\,\,\text{smor}\,\,P.S\,\text{smor}\,Q.CʻR\cap CʻS=\Lambda .Z=R\unicode{x2909}S\end{align}\]

**Status.** proved (reading): transcription error: the e-text prints `C'P ∩ C⊃Q` for
`C'P ∩ C'Q` (as in the Dem., which uses ✱160·48 with `C'P ∩ C'Q = Λ`). -/
theorem pm180_151 {P Q : α → α → Prop} {Z : β → β → Prop} : fld P ∩ fld Q = Λ →
    (smor Z (P ⤉ Q) ↔
      ∃ R S, ((smor R P ∧ smor S Q) ∧ fld R ∩ fld S = Λ) ∧ Z = R ⤉ S) := by
  intro h
  rw [smor_rsum_iff (inter_null_iff.1 h)]
  simp only [inter_null_iff]

/-- ✱180·152. \[\begin{align}\vdash :Z\,\text{smor}\,&(P+Q).\equiv .\\ &(\exists R,S).R\,\,\text{smor}\,\,P.S\,\text{smor}\,Q.CʻR\cap CʻS=\Lambda .Z=R\unicode{x2909}S\\ &[*180·151·11·12]\end{align}\] -/
theorem pm180_152 {P : α → α → Prop} {Q : β → β → Prop} {Z : γ → γ → Prop} :
    smor Z (P +ᵣ Q) ↔
      ∃ R S, ((smor R P ∧ smor S Q) ∧ fld R ∩ fld S = Λ) ∧ Z = R ⤉ S := by
  rw [smor_rplus_iff]; simp only [inter_null_iff]

/-- ✱180·16. \[\begin{align}\vdash .\text{Nr}ʻ&(P+Q)=\\ &\hat{Z} \{(\exists R,S).R\in \text{Nr}ʻP.S\in \text{Nr}ʻQ.CʻR\cap CʻS=\Lambda .Z=R\unicode{x2909}S\}\\ &[*180·152.*152·11]\end{align}\]

`Nr'(P + Q)`, `Nr'P`, `Nr'Q` are in one type `γ` (that of `Z`). -/
theorem pm180_16 {P : α → α → Prop} {Q : β → β → Prop} :
    nr γ (P +ᵣ Q) =
      {Z | ∃ R S, ((R ∈ nr γ P ∧ S ∈ nr γ Q) ∧ fld R ∩ fld S = Λ) ∧ Z = R ⤉ S} := by
  ext Z; exact pm180_152

/-- ✱180·2. \[\begin{align}&\vdash :Z\in \mu \dot{+} \nu .\equiv .(\exists P,Q).\mu =\text{N}_{0}\text{r}ʻP.\nu =\text{N}_{0}\text{r}ʻQ.Z\,\text{smor}\,(P+Q)\\ &[(*180·02)]\end{align}\] -/
theorem pm180_2 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} {Z : γ → γ → Prop} :
    Z ∈ (μ ∔ ν : Set (γ → γ → Prop)) ↔
      ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor Z (P +ᵣ Q) :=
  Iff.rfl

/-- ✱180·201. \[\begin{align}&\vdash \colon\ldotp Z\in \mu \dot{+} \nu .\equiv :\mu ,\nu \in \text{N}_{0}\text{R}:(\exists P,Q).P\in \mu .Q\in \nu .Z\,\text{smor}\,(P+Q)\\ &[*155·27.*180·2]\end{align}\] -/
theorem pm180_201 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} {Z : γ → γ → Prop} :
    Z ∈ (μ ∔ ν : Set (γ → γ → Prop)) ↔
      (μ ∈ N₀R ∧ ν ∈ N₀R) ∧ ∃ P Q, (P ∈ μ ∧ Q ∈ ν) ∧ smor Z (P +ᵣ Q) := by
  constructor
  · rintro ⟨P, Q, ⟨rfl, rfl⟩, h⟩
    exact ⟨⟨⟨P, rfl⟩, ⟨Q, rfl⟩⟩, P, Q, ⟨self_mem_n₀r P, self_mem_n₀r Q⟩, h⟩
  · rintro ⟨⟨⟨P', rfl⟩, ⟨Q', rfl⟩⟩, P, Q, ⟨hP, hQ⟩, h⟩
    exact ⟨P, Q, ⟨n₀r_eq_n₀r_iff.2 (smor_symm (mem_n₀r.1 hP)),
      n₀r_eq_n₀r_iff.2 (smor_symm (mem_n₀r.1 hQ))⟩, h⟩

/-- ✱180·202. \[\begin{align}\vdash \colon\ldotp Z\in &\mu \dot{+} \nu .\equiv :\\ &\exists !\mu .\exists !\nu :(\exists P,Q).\mu =\text{Nr}ʻP.\nu =\text{Nr}ʻQ.Z\,\text{smor}\,(P+Q)\end{align}\]

`μ = Nr'P` is in the type of the members of `μ` (meaning). -/
theorem pm180_202 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} {Z : γ → γ → Prop} :
    Z ∈ (μ ∔ ν : Set (γ → γ → Prop)) ↔ (μ.Nonempty ∧ ν.Nonempty) ∧
      ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = nr α P ∧ ν = nr β Q) ∧ smor Z (P +ᵣ Q) := by
  constructor
  · rintro ⟨P, Q, ⟨rfl, rfl⟩, h⟩
    exact ⟨⟨n₀r_nonempty P, n₀r_nonempty Q⟩, P, Q, ⟨n₀r_eq_nr P, n₀r_eq_nr Q⟩, h⟩
  · rintro ⟨-, P, Q, ⟨hP, hQ⟩, h⟩
    exact ⟨P, Q, ⟨hP.trans (n₀r_eq_nr P).symm, hQ.trans (n₀r_eq_nr Q).symm⟩, h⟩

/-- ✱180·21. \(\vdash \colon\ldotp \mu ,\nu \in \text{NR}.\supset :Z\in \mu \dot{+} \nu .\equiv .(\exists P,Q).P\in \mu .Q\in \nu .Z\,\text{smor}\,(P\dot{+}Q)\)

`μ, ν ∈ NR` is `μ ∈ NR β₁ ∧ ν ∈ NR β₂` with independent types (Prefatory Statement, V).

**Status.** proved (reading): transcription error: the e-text prints `P +̇ Q` for the relation
`P + Q` (`+̇` is significant only between relation-numbers; ✱180·2). -/
theorem pm180_21 {β₁ β₂ : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    {Z : γ → γ → Prop} : μ ∈ NR β₁ ∧ ν ∈ NR β₂ →
      (Z ∈ (μ ∔ ν : Set (γ → γ → Prop)) ↔ ∃ P Q, (P ∈ μ ∧ Q ∈ ν) ∧ smor Z (P +ᵣ Q)) := by
  rintro ⟨hμ, hν⟩
  rcases NR_cases hμ with rfl | ⟨P', rfl⟩
  · rw [empty_nrAdd]; simp
  rcases NR_cases hν with rfl | ⟨Q', rfl⟩
  · rw [nrAdd_empty]; simp
  rw [pm180_201]
  exact ⟨fun h => h.2, fun h => ⟨⟨⟨P', rfl⟩, ⟨Q', rfl⟩⟩, h⟩⟩

/-- ✱180·211. \[\begin{align}\vdash \colon\ldotp &\mu , \nu \in \text{NR} . \supset : Z \in \mu \dot{+} \nu . \equiv .\\ &(\exists R, S) . R \in \,\text{smor}\,ʻʻ\mu . S \in \,\text{smor}\,ʻʻ\nu . CʻR \cap CʻS = \Lambda . Z = R \unicode{x2909} S\end{align}\]

`smor''μ` is the ascribed `smor ʻʻ μ` in the type of `Z`. -/
theorem pm180_211 {β₁ β₂ : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    {Z : γ → γ → Prop} : μ ∈ NR β₁ ∧ ν ∈ NR β₂ →
      (Z ∈ (μ ∔ ν : Set (γ → γ → Prop)) ↔ ∃ R S : γ → γ → Prop,
        ((R ∈ smor ʻʻ μ ∧ S ∈ smor ʻʻ ν) ∧ fld R ∩ fld S = Λ) ∧ Z = R ⤉ S) := by
  intro h
  rw [pm180_21 h]
  constructor
  · rintro ⟨P, Q, ⟨hP, hQ⟩, hZ⟩
    obtain ⟨R, S, ⟨⟨hR, hS⟩, hRS⟩, rfl⟩ := pm180_152.1 hZ
    exact ⟨R, S, ⟨⟨⟨P, hP, hR⟩, ⟨Q, hQ, hS⟩⟩, hRS⟩, rfl⟩
  · rintro ⟨R, S, ⟨⟨⟨P, hP, hR⟩, ⟨Q, hQ, hS⟩⟩, hRS⟩, rfl⟩
    exact ⟨P, Q, ⟨hP, hQ⟩, pm180_13 ⟨⟨hR, hS⟩, hRS⟩⟩

/-- ✱180·212. \[\begin{align}\vdash \colon\ldotp &\mu , \nu \in \text{NR} . \supset : Z \in \mu \dot{+} \nu . \equiv .\\ &(\exists R) . R \in \,\text{smor}\,ʻʻ\mu . R \,\unicode{x2abd}\, Z . Z \unicode{x0294f} (- CʻR) \in \,\text{smor}\,ʻʻ\nu\end{align}\]

**Status.** proved (corrected): as printed (with `R ⊂̇ Z`) the right-hand side does not make `Z`
the sum `R ⤉ (Z ⥏ −C'R)`: `Z` may contain further pairs (from the part `Z ⥏ −C'R` back to `C'R`,
or within `C'R`); e.g. `Z = x ↓ y ∪̇ y ↓ x`, `μ = Nr'(x ↓ y)`, `ν = 0_r`, `R = x ↓ y`
(`pm180_212_printed_false`). Corrected (the analogue of ✱110·212 `γ ⊂ ξ . ξ − γ ∈ sm''ν`, i.e.
`ξ = γ ∪ (ξ − γ)`): `R ⊂̇ Z` is replaced by `Z = R ⤉ (Z ⥏ −C'R)`. -/
theorem pm180_212 {β₁ β₂ : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    {Z : γ → γ → Prop} : μ ∈ NR β₁ ∧ ν ∈ NR β₂ →
      (Z ∈ (μ ∔ ν : Set (γ → γ → Prop)) ↔ ∃ R : γ → γ → Prop,
        (R ∈ smor ʻʻ μ ∧ Z = R ⤉ Z ⥏ (fld R)ᶜ) ∧ Z ⥏ (fld R)ᶜ ∈ smor ʻʻ ν) := by
  intro h
  rw [pm180_211 h]
  have key : ∀ R S : γ → γ → Prop, Disjoint (fld R) (fld S) → (R ⤉ S) ⥏ (fld R)ᶜ = S := by
    intro R S hd
    funext x y; apply propext
    constructor
    · rintro ⟨⟨hx, ((hr | hs) | ⟨hx', -⟩)⟩, -⟩
      · exact absurd ⟨y, Or.inl hr⟩ hx
      · exact hs
      · exact absurd hx' hx
    · intro hs
      exact ⟨⟨Set.disjoint_right.1 hd ⟨y, Or.inl hs⟩, Or.inl (Or.inr hs)⟩,
        Set.disjoint_right.1 hd ⟨x, Or.inr hs⟩⟩
  constructor
  · rintro ⟨R, S, ⟨⟨hR, hS⟩, hRS⟩, rfl⟩
    refine ⟨R, ⟨hR, ?_⟩, ?_⟩ <;> rw [key R S (inter_null_iff.1 hRS)]
    exact hS
  · rintro ⟨R, ⟨hR, hZ⟩, hS⟩
    refine ⟨R, Z ⥏ (fld R)ᶜ, ⟨⟨hR, hS⟩, ?_⟩, hZ⟩
    rw [inter_null_iff]
    exact Set.disjoint_left.2 fun x hx ⟨y, h⟩ => h.elim (fun h => h.1.1 hx) (fun h => h.2 hx)

/-- ✱180·22. \(\vdash . \text{N}_{0}\text{r}ʻP \dot{+} \text{N}_{0}\text{r}ʻQ = \text{Nr}ʻ(P \dot{+} Q)\)

**Status.** proved (reading): transcription error: the e-text prints `Nr'(P +̇ Q)` for
`Nr'(P + Q)`. The sides are in one type `γ`. -/
theorem pm180_22 {P : α → α → Prop} {Q : β → β → Prop} :
    (n₀r P ∔ n₀r Q : Set (γ → γ → Prop)) = nr γ (P +ᵣ Q) := n₀r_nrAdd_n₀r P Q

/-- ✱180·24. \[\begin{align}&\vdash : R \,\text{smor}\, P . S \,\text{smor}\, Q . \supset . \text{N}_{0}\text{r}ʻR \dot{+} \text{N}_{0}\text{r}ʻS = \text{N}_{0}\text{r}ʻP \dot{+} \text{N}_{0}\text{r}ʻQ\\ &[*180·15·22]\end{align}\] -/
theorem pm180_24 {R : γ → γ → Prop} {S : δ → δ → Prop} {P : α → α → Prop} {Q : β → β → Prop}
    {ε : Type*} : smor R P ∧ smor S Q →
      (n₀r R ∔ n₀r S : Set (ε → ε → Prop)) = n₀r P ∔ n₀r Q := by
  rintro ⟨hR, hS⟩
  rw [n₀r_nrAdd_n₀r, n₀r_nrAdd_n₀r]
  exact nr_eq_nr_of_smor (smor_rplus hR hS)

/-- ✱180·3. \[\begin{align}\vdash . \text{Nr}ʻP \dot{+} &\text{Nr}ʻQ = \text{N}_{0}\text{r}ʻP \dot{+} \text{Nr}ʻQ = \text{Nr}ʻP \dot{+} \text{N}_{0}\text{r}ʻQ\\ &= \text{N}_{0}\text{r}ʻP \dot{+} \text{N}_{0}\text{r}ʻQ = \text{Nr}ʻ(P \dot{+} Q) \quad[*180·22 . (*180·03·031)]\end{align}\]

(Normal adjustment.) The arguments `Nr'P`, `Nr'Q` of `+̇` are `n₀r P`, `n₀r Q` by ✱180·03·031,
so the first three equations are identities of readings; all sides are in one type `γ`.

**Status.** proved (reading): by the Dfs ✱180·03·031 the arguments Nr'P, Nr'Q of +̇ are read
N₀r'P, N₀r'Q; transcription error: the e-text prints `Nr'(P +̇ Q)` for `Nr'(P + Q)` -/
theorem pm180_3 {P : α → α → Prop} {Q : β → β → Prop} :
    (((n₀r P ∔ n₀r Q : Set (γ → γ → Prop)) = n₀r P ∔ n₀r Q ∧
      (n₀r P ∔ n₀r Q : Set (γ → γ → Prop)) = n₀r P ∔ n₀r Q) ∧
      (n₀r P ∔ n₀r Q : Set (γ → γ → Prop)) = n₀r P ∔ n₀r Q) ∧
      (n₀r P ∔ n₀r Q : Set (γ → γ → Prop)) = nr γ (P +ᵣ Q) :=
  ⟨⟨⟨rfl, rfl⟩, rfl⟩, n₀r_nrAdd_n₀r P Q⟩

/-- ✱180·31. \(\vdash : P \,\,\text{smor}\, R . Q \,\text{smor}\, S . \supset . \text{Nr}ʻP \dot{+} \text{Nr}ʻQ = \text{Nr}ʻR \dot{+} \text{Nr}ʻS\) -/
theorem pm180_31 {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop} {S : δ → δ → Prop}
    {ε : Type*} : smor P R ∧ smor Q S → (n₀r P ∔ n₀r Q : Set (ε → ε → Prop)) = n₀r R ∔ n₀r S :=
  pm180_24

/-- ✱180·32. \(\vdash : CʻP \cap CʻQ = \Lambda . \supset . \text{Nr}ʻP \dot{+} \text{Nr}ʻQ = \text{Nr}ʻ(P \unicode{x2909} Q) \quad[*180·14·3]\) -/
theorem pm180_32 {P Q : α → α → Prop} : fld P ∩ fld Q = Λ →
    (n₀r P ∔ n₀r Q : Set (γ → γ → Prop)) = nr γ (P ⤉ Q) := fun h => by
  rw [n₀r_nrAdd_n₀r]; exact nr_eq_nr_of_smor (smor_symm (pm180_14 h))

/-- ✱180·4. \(\vdash : \exists ! \mu \dot{+} \nu . \supset . \mu , \nu \in \text{NR} - {℩}ʻ\Lambda . \mu , \nu \in \text{N}_{0}\text{R}\)

**Status.** proved (reading): the ambiguous `NR` of the conclusion is taken, as in ✱155·27 (cf.
✱110·4), with the relations whose numbers are in question in the types of the members of `μ` and
`ν` (`NR^α(α)`). -/
theorem pm180_4 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    (μ ∔ ν : Set (γ → γ → Prop)).Nonempty →
      (μ ∈ NR α \ ι Λ ∧ ν ∈ NR β \ ι Λ) ∧ (μ ∈ N₀R ∧ ν ∈ N₀R) := by
  rintro ⟨Z, P, Q, ⟨rfl, rfl⟩, -⟩
  refine ⟨⟨⟨n₀r_mem_NR P, ?_⟩, ⟨n₀r_mem_NR Q, ?_⟩⟩, ⟨P, rfl⟩, ⟨Q, rfl⟩⟩
  · rw [mem_unitCls, Null_eq_empty]; exact n₀r_ne_empty P
  · rw [mem_unitCls, Null_eq_empty]; exact n₀r_ne_empty Q

/-- ✱180·42. \(\vdash . \mu \dot{+} \nu \in \text{NR}\)

**Status.** proved (reading): the ambiguous `NR` is taken as `NR^{t'Z}(Z)` for the relations `Z`
of the sum (`NR (Set γ)`), as ✱110·42 (where `Λ ∈ NR` by ✱154·242); in some other determinations
of `NR` the proposition fails (e.g. `NR` of the relations of an empty type contains only `0_r`). -/
theorem pm180_42 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    (μ ∔ ν : Set (γ → γ → Prop)) ∈ NR (Set γ) := by
  rcases Set.eq_empty_or_nonempty (μ ∔ ν : Set (γ → γ → Prop)) with h | ⟨Z, hZ⟩
  · rw [h]; exact empty_mem_NR_set
  · obtain ⟨P, Q, ⟨rfl, rfl⟩, h⟩ := hZ
    rw [n₀r_nrAdd_n₀r, nr_eq_n₀r_of_mem h]
    exact n₀r_mem_NR_set Z

/-- ✱180·43. \(\vdash : \mu \dot{+} \nu = \text{N}_{0}\text{r}ʻZ . \equiv . Z \in \mu \dot{+} \nu\) -/
theorem pm180_43 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} {Z : γ → γ → Prop} :
    (μ ∔ ν : Set (γ → γ → Prop)) = n₀r Z ↔ Z ∈ (μ ∔ ν : Set (γ → γ → Prop)) := by
  constructor
  · intro h; rw [h]; exact self_mem_n₀r Z
  · intro hZ
    obtain ⟨P, Q, ⟨rfl, rfl⟩, h⟩ := hZ
    rw [n₀r_nrAdd_n₀r]; exact nr_eq_n₀r_of_mem h


/-- ✱180·53. \(\vdash . (P + Q) + R \,\text{smor}\, P + (Q + R)\) -/
theorem pm180_53 {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop} :
    smor (P +ᵣ Q +ᵣ R) (P +ᵣ (Q +ᵣ R)) := by
  obtain ⟨L₁, R₁, e₁, ⟨hL₁, hR₁⟩, hd₁⟩ := rplus_split P Q
  obtain ⟨L₂, R₂, e₂, ⟨hL₂, hR₂⟩, hd₂⟩ := rplus_split (P +ᵣ Q) R
  obtain ⟨L₃, R₃, e₃, ⟨hL₃, hR₃⟩, hd₃⟩ := rplus_split Q R
  obtain ⟨L₄, R₄, e₄, ⟨hL₄, hR₄⟩, hd₄⟩ := rplus_split P (Q +ᵣ R)
  rw [e₁] at hL₂
  obtain ⟨A, B, ⟨⟨hA, hB⟩, hAB⟩, rfl⟩ := (smor_rsum_iff hd₁).1 hL₂
  rw [e₃] at hR₄
  obtain ⟨B', C', ⟨⟨hB', hC'⟩, hBC'⟩, rfl⟩ := (smor_rsum_iff hd₃).1 hR₄
  rw [e₂, e₄, rsum_assoc]
  rw [fld_rsum] at hd₂
  refine smor_rsum (smor_trans (smor_trans hA hL₁) (smor_symm hL₄))
    (smor_rsum (smor_trans (smor_trans hB hR₁) (smor_symm (smor_trans hB' hL₃)))
      (smor_trans hR₂ (smor_symm (smor_trans hC' hR₃))) (hd₂.mono_left Set.subset_union_right)
      hBC') ?_ hd₄
  rw [fld_rsum]
  exact Set.disjoint_union_right.2 ⟨hAB, hd₂.mono_left Set.subset_union_left⟩

/-- ✱180·531 (Df). \(P + Q + R = (P + Q) + R \quad\text{Df}\) -/
theorem pm180_531 {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop} :
    P +ᵣ Q +ᵣ R = (P +ᵣ Q) +ᵣ R := rfl

/-- ✱180·54. \(\vdash . (\text{Nr}ʻP \dot{+} \text{Nr}ʻQ) \dot{+} \text{Nr}ʻR = \text{Nr}ʻ(P + Q + R)\)

The inner sum is an arithmetical component (IIT): its type `W` is a parameter with the
hypothesis that it is adequate. The arguments `Nr'P`, … of `+̇` are `n₀r P`, … (✱180·03·031).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component Nr'P +̇ Nr'Q is adequate -/
theorem pm180_54 {W : Type*} {P : α → α → Prop} {Q : β → β → Prop} {R : δ → δ → Prop}
    (h : AdeqNrAdd W (n₀r P) (n₀r Q)) :
    ((n₀r P ∔ n₀r Q : Set (W → W → Prop)) ∔ n₀r R : Set (γ → γ → Prop)) = nr γ (P +ᵣ Q +ᵣ R) := by
  obtain ⟨X, hX, e⟩ := h.eq_n₀r P Q
  rw [e, n₀r_nrAdd_n₀r]
  exact nr_eq_nr_of_smor (smor_rplus hX (smor_refl R))

/-- ✱180·541. \(\vdash . \text{Nr}ʻP \dot{+} (\text{Nr}ʻQ \dot{+} \text{Nr}ʻR) = \text{Nr}ʻ(P + Q + R)\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component Nr'Q +̇ Nr'R is adequate -/
theorem pm180_541 {W : Type*} {P : α → α → Prop} {Q : β → β → Prop} {R : δ → δ → Prop}
    (h : AdeqNrAdd W (n₀r Q) (n₀r R)) :
    (n₀r P ∔ (n₀r Q ∔ n₀r R : Set (W → W → Prop)) : Set (γ → γ → Prop)) = nr γ (P +ᵣ Q +ᵣ R) := by
  obtain ⟨X, hX, e⟩ := h.eq_n₀r Q R
  rw [e, n₀r_nrAdd_n₀r]
  exact nr_eq_nr_of_smor (smor_trans (smor_rplus (smor_refl P) hX) (smor_symm pm180_53))

/-- ✱180·55. \(\vdash . (\text{Nr}ʻP \dot{+} \text{Nr}ʻQ) \dot{+} \text{Nr}ʻR = \text{Nr}ʻP \dot{+} (\text{Nr}ʻQ \dot{+} \text{Nr}ʻR)\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components are adequate -/
theorem pm180_55 {W₁ W₂ : Type*} {P : α → α → Prop} {Q : β → β → Prop} {R : δ → δ → Prop}
    (h₁ : AdeqNrAdd W₁ (n₀r P) (n₀r Q)) (h₂ : AdeqNrAdd W₂ (n₀r Q) (n₀r R)) :
    ((n₀r P ∔ n₀r Q : Set (W₁ → W₁ → Prop)) ∔ n₀r R : Set (γ → γ → Prop)) =
      n₀r P ∔ (n₀r Q ∔ n₀r R : Set (W₂ → W₂ → Prop)) :=
  (pm180_54 h₁).trans (pm180_541 h₂).symm

/-- ✱180·551. \(\vdash .(\text{N}_{0}\text{r}ʻP\dot{+} \text{N}_{0}\text{r}ʻQ)\dot{+} \text{N}_{0}\text{r}ʻR = \text{N}_{0}\text{r}ʻP\dot{+} (\text{N}_{0}\text{r}ʻQ\dot{+} \text{N}_{0}\text{r}ʻR)\)

(After normal adjustment this is the statement of ✱180·55.)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components are adequate -/
theorem pm180_551 {W₁ W₂ : Type*} {P : α → α → Prop} {Q : β → β → Prop} {R : δ → δ → Prop}
    (h₁ : AdeqNrAdd W₁ (n₀r P) (n₀r Q)) (h₂ : AdeqNrAdd W₂ (n₀r Q) (n₀r R)) :
    ((n₀r P ∔ n₀r Q : Set (W₁ → W₁ → Prop)) ∔ n₀r R : Set (γ → γ → Prop)) =
      n₀r P ∔ (n₀r Q ∔ n₀r R : Set (W₂ → W₂ → Prop)) :=
  pm180_55 h₁ h₂

/-- ✱180·56. \(\vdash .(\mu \dot{+} \nu )\dot{+} \omega = \mu \dot{+} (\nu \dot{+} \omega )\)

(The e-text's `ω` is PM's `ϖ`.) The real variables `μ`, `ν`, `ϖ` have independent types; the
inner sums are arithmetical components, each with its own adequate type.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components μ +̇ ν and ν +̇ ϖ are adequate -/
theorem pm180_56 {α₁ α₂ α₃ W₁ W₂ : Type*} {μ : Set (α₁ → α₁ → Prop)} {ν : Set (α₂ → α₂ → Prop)}
    {ϖ : Set (α₃ → α₃ → Prop)} (h₁ : AdeqNrAdd W₁ μ ν) (h₂ : AdeqNrAdd W₂ ν ϖ) :
    ((μ ∔ ν : Set (W₁ → W₁ → Prop)) ∔ ϖ : Set (γ → γ → Prop)) =
      μ ∔ (ν ∔ ϖ : Set (W₂ → W₂ → Prop)) := by
  by_cases hμ : ∃ P, μ = n₀r P
  · by_cases hν : ∃ Q, ν = n₀r Q
    · by_cases hϖ : ∃ R, ϖ = n₀r R
      · obtain ⟨P, rfl⟩ := hμ; obtain ⟨Q, rfl⟩ := hν; obtain ⟨R, rfl⟩ := hϖ
        exact pm180_55 h₁ h₂
      · push Not at hϖ
        rw [nrAdd_eq_empty_of_right _ hϖ, nrAdd_eq_empty_of_right (ν := ϖ) _ hϖ, nrAdd_empty]
    · push Not at hν
      rw [nrAdd_eq_empty_of_right (ν := ν) _ hν, nrAdd_eq_empty_of_left (μ := ν) hν,
        empty_nrAdd, nrAdd_empty]
  · push Not at hμ
    rw [nrAdd_eq_empty_of_left (μ := μ) hμ, nrAdd_eq_empty_of_left (μ := μ) hμ, empty_nrAdd]

/-- ✱180·561 (Df). \(\mu \dot{+} \nu \dot{+} \omega = (\mu \dot{+} \nu ])\dot{+} \omega \quad\text{Df}\)

(The e-text has a stray `]`: PM has `(μ +̇ ν) +̇ ω`.) Realized by `infixl`; the inner sum is an
arithmetical component, so its type is a separate parameter `W` (IIT). -/
theorem pm180_561 {W : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    {ϖ : Set (δ → δ → Prop)} : ((μ ∔ ν : Set (W → W → Prop)) ∔ ϖ : Set (γ → γ → Prop)) =
      ((μ ∔ ν : Set (W → W → Prop)) ∔ ϖ : Set (γ → γ → Prop)) := rfl

/-- ✱180·6. \(\vdash :\mu \in \text{NR}.\supset .\mu \dot{+} 0_{r} = \,\text{smor}\,ʻʻ\mu = 0_{r}\dot{+} \mu\)

`0_r` is an arithmetical argument with its own type `W` (IIT; `0_r` exists in every type, so no
hypothesis is needed); `smor''μ` is in the type `γ` of the sums. -/
theorem pm180_6 {β' W : Type*} {μ : Set (α → α → Prop)} :
    μ ∈ NR β' → (μ ∔ (zero_r : Set (W → W → Prop)) : Set (γ → γ → Prop)) = smor ʻʻ μ ∧
      smor ʻʻ μ = ((zero_r : Set (W → W → Prop)) ∔ μ : Set (γ → γ → Prop)) := by
  intro h
  rcases NR_cases h with rfl | ⟨P, rfl⟩
  · rw [empty_nrAdd, nrAdd_empty, smor_img_empty]; exact ⟨rfl, rfl⟩
  · rw [nrAdd_of rfl zero_r_eq_n₀r, nrAdd_of zero_r_eq_n₀r rfl, smor_img_n₀r]
    exact ⟨nr_eq_nr_of_smor (smor_rplus_rNull P), (nr_eq_nr_of_smor (smor_rNull_rplus P)).symm⟩

/-- ✱180·61. \(\vdash .\text{Nr}ʻP\dot{+} 0_{r} = \text{Nr}ʻP = 0_{r}\dot{+} \text{Nr}ʻP\) -/
theorem pm180_61 {W : Type*} {P : α → α → Prop} :
    (n₀r P ∔ (zero_r : Set (W → W → Prop)) : Set (γ → γ → Prop)) = nr γ P ∧
      nr γ P = ((zero_r : Set (W → W → Prop)) ∔ n₀r P : Set (γ → γ → Prop)) := by
  have := pm180_6 (β' := α) (W := W) (γ := γ) (n₀r_mem_NR P)
  rw [smor_img_n₀r] at this
  exact this

/-- ✱180·62. \(\vdash :\mu \dot{+} \nu = 0_{r}. \equiv .\mu = 0_{r}.\nu = 0_{r}\) -/
theorem pm180_62 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    (μ ∔ ν : Set (γ → γ → Prop)) = zero_r ↔ μ = zero_r ∧ ν = zero_r := by
  constructor
  · intro h
    have hz : (rNull : γ → γ → Prop) ∈ (μ ∔ ν : Set (γ → γ → Prop)) := by rw [h]; rfl
    obtain ⟨P, Q, ⟨rfl, rfl⟩, -⟩ := hz
    rw [n₀r_nrAdd_n₀r, nr_eq_zero_r_iff] at h
    have hP : P = rNull := by
      by_contra hP
      exact ne_rNull_iff.2 (rEx_rplus_left Q (ne_rNull_iff.1 hP)) h
    have hQ : Q = rNull := by
      by_contra hQ
      exact ne_rNull_iff.2 (rEx_rplus_right P (ne_rNull_iff.1 hQ)) h
    subst hP hQ
    exact ⟨zero_r_eq_n₀r.symm, zero_r_eq_n₀r.symm⟩
  · rintro ⟨rfl, rfl⟩
    rw [nrAdd_of zero_r_eq_n₀r zero_r_eq_n₀r]
    exact nr_eq_zero_r_iff.2 (by rw [rplus_eq, graph_semi_rNull, graph_semi_rNull, rsum_rNull])

/-- ✱180·64. \(\vdash .0_{r}\dot{+} 0_{r} = 0_{r}\)

Each `0_r` has its own type (IIT; no hypothesis is needed for `0_r`). -/
theorem pm180_64 {W₁ W₂ : Type*} :
    ((zero_r : Set (W₁ → W₁ → Prop)) ∔ (zero_r : Set (W₂ → W₂ → Prop)) : Set (γ → γ → Prop)) =
      zero_r :=
  pm180_62.2 ⟨rfl, rfl⟩

/-- ✱180·642. \(\vdash .2_{r}\dot{+} 0_{r} = 0_{r}\dot{+} 2_{r} = 2_{r}\)

Each `2_r`, `0_r` in an arithmetical position has its own type (IIT); a `2_r` there is adequate
in its type when it exists there.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the types of the
arithmetical components 2_r are adequate (2_r exists in them) -/
theorem pm180_642 {W₁ W₂ W₃ W₄ : Type*} (h₁ : (two_r : Set (W₁ → W₁ → Prop)).Nonempty)
    (h₄ : (two_r : Set (W₄ → W₄ → Prop)).Nonempty) :
    ((two_r : Set (W₁ → W₁ → Prop)) ∔ (zero_r : Set (W₂ → W₂ → Prop)) : Set (γ → γ → Prop)) =
        (zero_r : Set (W₃ → W₃ → Prop)) ∔ (two_r : Set (W₄ → W₄ → Prop)) ∧
      ((zero_r : Set (W₃ → W₃ → Prop)) ∔ (two_r : Set (W₄ → W₄ → Prop)) :
        Set (γ → γ → Prop)) = two_r := by
  obtain ⟨_, x, y, hxy, -⟩ := h₁
  obtain ⟨_, x', y', hxy', -⟩ := h₄
  rw [nrAdd_of (two_r_eq_n₀r hxy) zero_r_eq_n₀r, nrAdd_of zero_r_eq_n₀r (two_r_eq_n₀r hxy'),
    two_r_eq_nr hxy]
  have e₁ := nr_eq_nr_of_smor (γ := γ) (smor_rplus_rNull (β := W₂) (x ↓ y))
  have e₂ := nr_eq_nr_of_smor (γ := γ) (smor_rNull_rplus (β := W₃) (x' ↓ y'))
  have e₃ := nr_eq_nr_of_smor (γ := γ) (smor_couple hxy hxy')
  exact ⟨e₁.trans (e₃.trans e₂.symm), e₂.trans e₃.symm⟩

/-- ✱180·7. \(\vdash .CʻʻN_{r}ʻ(P+Q) = CʻʻN_{r}ʻP+_{c}Cʻʻ\text{Nr}ʻQ = \text{Nc}ʻCʻP+_{c}\text{Nc}ʻCʻQ\)

`C''Nr'P` and `C''Nr'Q` are arithmetical components (IIT), each in its own adequate type; `Nc'C'P`,
`Nc'C'Q` as arguments of `+_c` are `n₀c (fld P)`, `n₀c (fld Q)` (✱110·03·04); the equation is in
one type `γ`, that of `Nr'(P + Q)`. (The e-text prints `N_r` for `Nr`.)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components C''Nr'P, C''Nr'Q are adequate -/
theorem pm180_7 {W₁ W₂ : Type*} {P : α → α → Prop} {Q : β → β → Prop} (h₁ : AdeqNr W₁ P)
    (h₂ : AdeqNr W₂ Q) :
    C ʻʻ nr γ (P +ᵣ Q) = (C ʻʻ nr W₁ P +ᶜ C ʻʻ nr W₂ Q : Set (Set γ)) ∧
      (C ʻʻ nr W₁ P +ᶜ C ʻʻ nr W₂ Q : Set (Set γ)) = n₀c (fld P) +ᶜ n₀c (fld Q) := by
  obtain ⟨X₁, hX₁⟩ := h₁.nr_nonempty P
  obtain ⟨X₂, hX₂⟩ := h₂.nr_nonempty Q
  rw [C_img_nr, C_img_nr, C_img_nr, nc_eq_n₀c_of_mem (sm_fld_of_smor hX₁),
    nc_eq_n₀c_of_mem (sm_fld_of_smor hX₂), n₀c_cardAdd_n₀c, n₀c_cardAdd_n₀c, fld_rplus]
  have e := nc_eq_nc_of_sm (γ := γ) (sm_clsSum (sm_fld_of_smor hX₁) (sm_fld_of_smor hX₂))
  exact ⟨e.symm, e⟩

/-- ✱180·71. \(\vdash :\mu ,\nu \in \text{NR}.\supset .Cʻʻ(\mu \dot{+} \nu ) = Cʻʻ\mu +_{c}Cʻʻ\nu\)

`μ, ν ∈ NR` have independent types; `C''μ`, `C''ν` are in the types of the members of `μ`, `ν`. -/
theorem pm180_71 {β₁ β₂ : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    μ ∈ NR β₁ ∧ ν ∈ NR β₂ →
      C ʻʻ (μ ∔ ν : Set (γ → γ → Prop)) = (C ʻʻ μ +ᶜ C ʻʻ ν : Set (Set γ)) := by
  rintro ⟨hμ, hν⟩
  rcases NR_cases hμ with rfl | ⟨P, rfl⟩
  · rw [empty_nrAdd, img_empty, img_empty]
    exact (cardAdd_eq_empty_of_left (fun A h => n₀c_ne_empty A h.symm) _).symm
  rcases NR_cases hν with rfl | ⟨Q, rfl⟩
  · rw [nrAdd_empty, img_empty, img_empty]
    exact (cardAdd_eq_empty_of_right _ (fun A h => n₀c_ne_empty A h.symm)).symm
  rw [n₀r_nrAdd_n₀r, C_img_nr, n₀r_eq_nr P, n₀r_eq_nr Q, C_img_nr, C_img_nr,
    ← n₀c_eq_nc (fld P), ← n₀c_eq_nc (fld Q), n₀c_cardAdd_n₀c, fld_rplus]

section Helpers181

private theorem mem_fld_addLast {P : α → α → Prop} {x z : α} :
    z ∈ fld (P ⇸ x) ↔ (z ∈ fld P ∨ z = x) ∧ rEx P := by
  constructor
  · rintro ⟨w, (h | ⟨h, -⟩) | (h | ⟨h, rfl⟩)⟩
    · exact ⟨Or.inl ⟨w, Or.inl h⟩, z, w, h⟩
    · exact ⟨Or.inl h, rEx_iff_fld.2 ⟨z, h⟩⟩
    · exact ⟨Or.inl ⟨w, Or.inr h⟩, w, z, h⟩
    · exact ⟨Or.inr rfl, rEx_iff_fld.2 ⟨w, h⟩⟩
  · rintro ⟨h | rfl, hP⟩
    · exact ⟨x, Or.inl (Or.inr ⟨h, rfl⟩)⟩
    · obtain ⟨u, hu⟩ := rEx_iff_fld.1 hP
      exact ⟨u, Or.inr (Or.inr ⟨hu, rfl⟩)⟩

private theorem mem_fld_addFirst {P : α → α → Prop} {x z : α} :
    z ∈ fld (x ⇷ P) ↔ (z ∈ fld P ∨ z = x) ∧ rEx P := by
  constructor
  · rintro ⟨w, (⟨h, hw⟩ | h) | (⟨-, h⟩ | h)⟩
    · exact ⟨Or.inr h, rEx_iff_fld.2 ⟨w, hw⟩⟩
    · exact ⟨Or.inl ⟨w, Or.inl h⟩, z, w, h⟩
    · exact ⟨Or.inl h, rEx_iff_fld.2 ⟨z, h⟩⟩
    · exact ⟨Or.inl ⟨w, Or.inr h⟩, w, z, h⟩
  · rintro ⟨h | rfl, hP⟩
    · exact ⟨x, Or.inr (Or.inl ⟨rfl, h⟩)⟩
    · obtain ⟨u, hu⟩ := rEx_iff_fld.1 hP
      exact ⟨u, Or.inl (Or.inl ⟨rfl, hu⟩)⟩

private theorem graph_semi_addLast (f : β → α) (P : β → β → Prop) (x : β) :
    graph f ⁏ (P ⇸ x) = graph f ⁏ P ⇸ f x := by
  funext u v; apply propext
  rw [semi_apply, addLast_apply, semi_apply, mem_fld_graph_semi]
  constructor
  · rintro ⟨z, w, ⟨hu, hv⟩, h | ⟨hz, rfl⟩⟩
    · exact Or.inl ⟨z, w, ⟨hu, hv⟩, h⟩
    · exact Or.inr ⟨⟨z, hz, hu⟩, hv⟩
  · rintro (⟨z, w, ⟨hu, hv⟩, h⟩ | ⟨⟨z, hz, hu⟩, hv⟩)
    · exact ⟨z, w, ⟨hu, hv⟩, Or.inl h⟩
    · exact ⟨z, x, ⟨hu, hv⟩, Or.inr ⟨hz, rfl⟩⟩

private theorem graph_semi_addFirst (f : β → α) (x : β) (P : β → β → Prop) :
    graph f ⁏ (x ⇷ P) = f x ⇷ graph f ⁏ P := by
  funext u v; apply propext
  rw [semi_apply, addFirst_apply, semi_apply, mem_fld_graph_semi]
  constructor
  · rintro ⟨z, w, ⟨hu, hv⟩, ⟨rfl, hw⟩ | h⟩
    · exact Or.inl ⟨hu, w, hw, hv⟩
    · exact Or.inr ⟨z, w, ⟨hu, hv⟩, h⟩
  · rintro (⟨hu, w, hw, hv⟩ | ⟨z, w, ⟨hu, hv⟩, h⟩)
    · exact ⟨x, w, ⟨hu, hv⟩, Or.inl ⟨rfl, hw⟩⟩
    · exact ⟨z, w, ⟨hu, hv⟩, Or.inr h⟩

private theorem addLast_rNull (x : α) : (rNull : α → α → Prop) ⇸ x = rNull := by
  funext u v; apply propext
  rw [addLast_apply, fld_rNull]
  exact ⟨fun h => h.elim id fun h => absurd h.1 (Set.notMem_empty u), fun h => Or.inl h⟩

private theorem fld_cnv' (P : α → α → Prop) : fld P˘ = fld P := by
  ext x; constructor <;> rintro ⟨y, h | h⟩ <;> exact ⟨y, by tauto⟩

private theorem addFirst_eq_cnv (x : α) (P : α → α → Prop) : x ⇷ P = (P˘ ⇸ x)˘ := by
  funext u v; apply propext
  show (x ⇷ P) u v ↔ (P˘ ⇸ x) v u
  rw [addFirst_apply, addLast_apply, fld_cnv']
  show _ ↔ P u v ∨ _
  tauto

private theorem smor_cnv {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q) : smor P˘ Q˘ := by
  obtain ⟨e, he⟩ := smor_iff_exists_equiv.1 h
  refine smor_iff_exists_equiv.2 ⟨(Set.equivOfEq (fld_cnv' P)).trans
    (e.trans (Set.equivOfEq (fld_cnv' Q).symm)), fun a b => ?_⟩
  exact he ⟨b, by rw [← fld_cnv']; exact b.2⟩ ⟨a, by rw [← fld_cnv']; exact a.2⟩

private theorem rEx_cnv {P : α → α → Prop} : rEx P˘ ↔ rEx P :=
  ⟨fun ⟨x, y, h⟩ => ⟨y, x, h⟩, fun ⟨x, y, h⟩ => ⟨y, x, h⟩⟩

/-- `A smor B . a ∼∈ C'A . b ∼∈ C'B . ⊃ . A ⇸ a smor B ⇸ b` (✱161·31). -/
private theorem smor_addLast {A : α → α → Prop} {B : β → β → Prop} {a : α} {b : β}
    (h : smor A B) (ha : a ∉ fld A) (hb : b ∉ fld B) : smor (A ⇸ a) (B ⇸ b) := by
  obtain ⟨T, ⟨t1, t2⟩, hc, rfl⟩ := smor_corr h
  have hcB : ∀ z, z ∈ fld B → ∃ x, T x z := fun z hz => (hc z).1 hz
  have hdom : ∀ x z, T x z → x ∈ fld (T ⁏ B) := fun x z hxz =>
    (mem_fld_semi hcB).2 ⟨z, (hc z).2 ⟨x, hxz⟩, hxz⟩
  let T' : α → β → Prop := fun u z => T u z ∨ (u = a ∧ z = b)
  have e : T ⁏ B ⇸ a = T' ⁏ (B ⇸ b) := by
    funext u v; apply propext
    rw [addLast_apply, semi_apply, semi_apply, mem_fld_semi hcB]
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
  refine smor_semi_of ?_ ?_ ?_
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
    obtain ⟨hz | rfl, -⟩ := mem_fld_addLast.1 hz
    · obtain ⟨x, hx⟩ := hcB z hz; exact ⟨x, Or.inl hx⟩
    · exact ⟨a, Or.inr ⟨rfl, rfl⟩⟩

private theorem smor_addFirst {A : α → α → Prop} {B : β → β → Prop} {a : α} {b : β}
    (h : smor A B) (ha : a ∉ fld A) (hb : b ∉ fld B) : smor (a ⇷ A) (b ⇷ B) := by
  rw [addFirst_eq_cnv, addFirst_eq_cnv]
  exact smor_cnv (smor_addLast (smor_cnv h) (by rwa [fld_cnv']) (by rwa [fld_cnv']))

/-- `A ⇸ a smor B ⇸ b . a ∼∈ C'A . b ∼∈ C'B . ⊃ . A smor B` (cf. ✱161·33). -/
private theorem smor_addLast_cancel {A : α → α → Prop} {B : β → β → Prop} {a : α} {b : β}
    (h : smor (A ⇸ a) (B ⇸ b)) (ha : a ∉ fld A) (hb : b ∉ fld B) : smor A B := by
  by_cases hA : rEx A
  swap
  · have hA0 : A = rNull := by by_contra h'; exact hA (ne_rNull_iff.1 h')
    subst hA0
    rw [addLast_rNull] at h
    have hB0 := smor_rNull_iff'.1 (smor_symm h)
    have : B = rNull := by
      funext u v; apply propext
      exact ⟨fun huv => by
        have : (B ⇸ b) u v := Or.inl huv
        rw [hB0] at this; exact absurd this (rNull_apply _ _), fun h => absurd h (rNull_apply _ _)⟩
    subst this; exact smor_rNull_iff'.2 rfl
  obtain ⟨T, ⟨t1, t2⟩, hc, hAT⟩ := smor_corr h
  have hBne : rEx B := by
    obtain ⟨u, v, huv⟩ := smor_preserves h (by obtain ⟨u, v, huv⟩ := hA; exact ⟨u, v, Or.inl huv⟩)
    rcases huv with huv | ⟨hu, -⟩
    · exact ⟨u, v, huv⟩
    · exact rEx_iff_fld.2 ⟨u, hu⟩
  have hbF : b ∈ fld (B ⇸ b) := mem_fld_addLast.2 ⟨Or.inr rfl, hBne⟩
  have hnoA : ∀ v, ¬ (A ⇸ a) a v := fun v hv =>
    hv.elim (fun h => ha ⟨v, Or.inl h⟩) (fun h => ha h.1)
  have hTab : T a b := by
    have haF : a ∈ fld (T ⁏ (B ⇸ b)) := by
      rw [← hAT]; exact mem_fld_addLast.2 ⟨Or.inr rfl, hA⟩
    obtain ⟨z, hz, haz⟩ := fld_semi_sub haF
    obtain ⟨hz' | rfl, -⟩ := mem_fld_addLast.1 hz
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
  exact smor_semi_of (fun x y z _ => t1 x y z) (fun x z w _ _ => t2 x z w)
    (fun z hz => (hc z).1 (mem_fld_addLast.2 ⟨Or.inl hz, hBne⟩))

private theorem smor_addFirst_cancel {A : α → α → Prop} {B : β → β → Prop} {a : α} {b : β}
    (h : smor (a ⇷ A) (b ⇷ B)) (ha : a ∉ fld A) (hb : b ∉ fld B) : smor A B := by
  rw [addFirst_eq_cnv, addFirst_eq_cnv] at h
  have := smor_addLast_cancel (smor_cnv h) (by rwa [fld_cnv']) (by rwa [fld_cnv'])
  exact smor_cnv this

end Helpers181
section Helpers181b

private theorem clsT_null (x : β) : clsT (Λ : Set β) x = ∅ := by rw [clsT_eq, Null_eq_empty]

private theorem addLastDot_eq (P : α → α → Prop) (x : β) :
    addLastDot P x = graph (fun y => ι y ↓ (∅ : Set β)) ⁏ P ⇸ ((∅ : Set α) ↓ ι x) := by
  show (coupleR (clsT Λ x) ⁏ iota ⁏ P) ⇸ ((Λ ∩ fld P) ↓ ι x) = _
  rw [semi_semi, coupleR_iota, clsT_null, null_inter]

private theorem addFirstDot_eq (x : β) (P : α → α → Prop) :
    addFirstDot x P = (ι x ↓ (∅ : Set α)) ⇷ graph (fun y => (∅ : Set β) ↓ ι y) ⁏ P := by
  show (ι x ↓ (Λ ∩ fld P)) ⇷ (coupleL (clsT Λ x) ⁏ iota ⁏ P) = _
  rw [semi_semi, coupleL_iota, clsT_null, null_inter]

private theorem inj_dotL : Function.Injective (fun y : α => ι y ↓ (∅ : Set β)) :=
  fun _ _ h => unitCls_injective (couple_eq_couple_iff.1 h).1

private theorem inj_dotR : Function.Injective (fun y : α => (∅ : Set β) ↓ ι y) :=
  fun _ _ h => unitCls_injective (couple_eq_couple_iff.1 h).2

private theorem unitCls_ne_empty (y : α) : ι y ≠ ∅ := fun h => (h ▸ (rfl : y = y) : y ∈ (∅ : Set α))

private theorem notin_dotL (P : α → α → Prop) (x : β) :
    ((∅ : Set α) ↓ ι x) ∉ fld (graph (fun y => ι y ↓ (∅ : Set β)) ⁏ P) := by
  intro h
  obtain ⟨y, -, e⟩ := mem_fld_graph_semi.1 h
  exact unitCls_ne_empty y (couple_eq_couple_iff.1 e).1.symm

private theorem notin_dotR (x : β) (P : α → α → Prop) :
    (ι x ↓ (∅ : Set α)) ∉ fld (graph (fun y => (∅ : Set β) ↓ ι y) ⁏ P) := by
  intro h
  obtain ⟨y, -, e⟩ := mem_fld_graph_semi.1 h
  exact unitCls_ne_empty y (couple_eq_couple_iff.1 e).2.symm

private theorem addLastDot_split (P : α → α → Prop) (x : β) :
    ∃ L e, addLastDot P x = L ⇸ e ∧ smor L P ∧ e ∉ fld L :=
  ⟨_, _, addLastDot_eq P x, smor_graph_inj inj_dotL P, notin_dotL P x⟩

private theorem addFirstDot_split (x : β) (P : α → α → Prop) :
    ∃ L e, addFirstDot x P = e ⇷ L ∧ smor L P ∧ e ∉ fld L :=
  ⟨_, _, addFirstDot_eq x P, smor_graph_inj inj_dotR P, notin_dotR x P⟩

private theorem smor_addLastDot {β' γ' : Type*} {P : α → α → Prop} {P' : γ' → γ' → Prop}
    (h : smor P P') (x : β) (x' : β') : smor (addLastDot P x) (addLastDot P' x') := by
  obtain ⟨L, e, h1, h2, h3⟩ := addLastDot_split P x
  obtain ⟨L', e', h1', h2', h3'⟩ := addLastDot_split P' x'
  rw [h1, h1']
  exact smor_addLast (smor_trans h2 (smor_trans h (smor_symm h2'))) h3 h3'

private theorem smor_addFirstDot {β' γ' : Type*} {P : α → α → Prop} {P' : γ' → γ' → Prop}
    (h : smor P P') (x : β) (x' : β') : smor (addFirstDot x P) (addFirstDot x' P') := by
  obtain ⟨L, e, h1, h2, h3⟩ := addFirstDot_split x P
  obtain ⟨L', e', h1', h2', h3'⟩ := addFirstDot_split x' P'
  rw [h1, h1']
  exact smor_addFirst (smor_trans h2 (smor_trans h (smor_symm h2'))) h3 h3'

/-- `Q smor P . y ∼∈ C'Q . ⊃ . Q ⇸ y smor P ⇸̇ x` (✱181·13). -/
private theorem smor_addLast_dot {Q : δ → δ → Prop} {P : α → α → Prop} {y : δ} (h : smor Q P)
    (hy : y ∉ fld Q) (x : β) : smor (Q ⇸ y) (addLastDot P x) := by
  obtain ⟨L, e, h1, h2, h3⟩ := addLastDot_split P x
  rw [h1]; exact smor_addLast (smor_trans h (smor_symm h2)) hy h3

private theorem smor_addFirst_dot {Q : δ → δ → Prop} {P : α → α → Prop} {y : δ} (h : smor Q P)
    (hy : y ∉ fld Q) (x : β) : smor (y ⇷ Q) (addFirstDot x P) := by
  obtain ⟨L, e, h1, h2, h3⟩ := addFirstDot_split x P
  rw [h1]; exact smor_addFirst (smor_trans h (smor_symm h2)) hy h3

private theorem rEx_addLast_iff {P : α → α → Prop} {x : α} : rEx (P ⇸ x) ↔ rEx P := by
  constructor
  · rintro ⟨u, v, h | ⟨hu, -⟩⟩
    · exact ⟨u, v, h⟩
    · exact rEx_iff_fld.2 ⟨u, hu⟩
  · rintro ⟨u, v, h⟩; exact ⟨u, v, Or.inl h⟩

private theorem rEx_addFirst_iff {P : α → α → Prop} {x : α} : rEx (x ⇷ P) ↔ rEx P := by
  constructor
  · rintro ⟨u, v, ⟨-, hv⟩ | h⟩
    · exact rEx_iff_fld.2 ⟨v, hv⟩
    · exact ⟨u, v, h⟩
  · rintro ⟨u, v, h⟩; exact ⟨u, v, Or.inr h⟩

private theorem rEx_addLastDot_iff {P : α → α → Prop} {x : β} : rEx (addLastDot P x) ↔ rEx P := by
  obtain ⟨L, e, h1, h2, -⟩ := addLastDot_split P x
  rw [h1, rEx_addLast_iff]
  exact ⟨smor_preserves h2, smor_preserves (smor_symm h2)⟩

private theorem rEx_addFirstDot_iff {P : α → α → Prop} {x : β} :
    rEx (addFirstDot x P) ↔ rEx P := by
  obtain ⟨L, e, h1, h2, -⟩ := addFirstDot_split x P
  rw [h1, rEx_addFirst_iff]
  exact ⟨smor_preserves h2, smor_preserves (smor_symm h2)⟩

private theorem addLast_mono {P P' : α → α → Prop} (h : P ⪽ P') (x : α) : P ⇸ x ⪽ P' ⇸ x := by
  rintro u v (huv | ⟨hu, hv⟩)
  · exact Or.inl (h _ _ huv)
  · exact Or.inr ⟨fld_mono h hu, hv⟩

private theorem addFirst_mono {P P' : α → α → Prop} (h : P ⪽ P') (x : α) : x ⇷ P ⪽ x ⇷ P' := by
  rintro u v (⟨hu, hv⟩ | huv)
  · exact Or.inl ⟨hu, fld_mono h hv⟩
  · exact Or.inr (h _ _ huv)

/-! #### `μ +̇ 1̇`, `1̇ +̇ μ` -/

/-- `N₀r'P +̇ 1̇ = Nr'(P ⇸̇ x)` (✱181·22). -/
private theorem nrAddOne_n₀r (P : α → α → Prop) (x : β) :
    (nrAddOne β (n₀r P) : Set (γ → γ → Prop)) = nr γ (addLastDot P x) := by
  ext Z
  constructor
  · rintro ⟨P', x', hP', hZ⟩
    exact smor_trans hZ (smor_addLastDot (n₀r_eq_n₀r_iff.1 hP') x' x)
  · intro h; exact ⟨P, x, rfl, h⟩

private theorem nrOneAdd_n₀r (P : α → α → Prop) (x : β) :
    (nrOneAdd β (n₀r P) : Set (γ → γ → Prop)) = nr γ (addFirstDot x P) := by
  ext Z
  constructor
  · rintro ⟨P', x', hP', hZ⟩
    exact smor_trans hZ (smor_addFirstDot (n₀r_eq_n₀r_iff.1 hP') x' x)
  · intro h; exact ⟨P, x, rfl, h⟩

private theorem nrAddOne_empty_of {μ : Set (α → α → Prop)} (h : ∀ P, μ ≠ n₀r P) :
    (nrAddOne β μ : Set (γ → γ → Prop)) = ∅ := by
  ext Z; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨P, x, hP, -⟩; exact h P hP.symm

private theorem nrOneAdd_empty_of {μ : Set (α → α → Prop)} (h : ∀ P, μ ≠ n₀r P) :
    (nrOneAdd β μ : Set (γ → γ → Prop)) = ∅ := by
  ext Z; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨P, x, hP, -⟩; exact h P hP.symm

private theorem nrAddOne_isEmpty [IsEmpty β] (μ : Set (α → α → Prop)) :
    (nrAddOne β μ : Set (γ → γ → Prop)) = ∅ := by
  ext Z; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨P, x, -, -⟩; exact isEmptyElim x

private theorem nrOneAdd_isEmpty [IsEmpty β] (μ : Set (α → α → Prop)) :
    (nrOneAdd β μ : Set (γ → γ → Prop)) = ∅ := by
  ext Z; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨P, x, -, -⟩; exact isEmptyElim x

private theorem addLastDot_sub_rV (P : α → α → Prop) (x : β) :
    addLastDot P x ⪽ addLastDot (rV : α → α → Prop) x := by
  rw [addLastDot_eq, addLastDot_eq]
  exact addLast_mono (semi_mono _ fun _ _ _ => ⟨rfl, rfl⟩) _

private theorem addFirstDot_sub_rV (x : β) (P : α → α → Prop) :
    addFirstDot x P ⪽ addFirstDot x (rV : α → α → Prop) := by
  rw [addFirstDot_eq, addFirstDot_eq]
  exact addFirst_mono (semi_mono _ fun _ _ _ => ⟨rfl, rfl⟩) _

private theorem AdeqNrAddOne.nonempty {W : Type*} {μ : Set (α → α → Prop)}
    (h : AdeqNrAddOne W β μ) : Nonempty β := by
  obtain ⟨_, _, x, -, -⟩ := h; exact ⟨x⟩

private theorem AdeqNrOneAdd.nonempty {W : Type*} {μ : Set (α → α → Prop)}
    (h : AdeqNrOneAdd W β μ) : Nonempty β := by
  obtain ⟨_, _, x, -, -⟩ := h; exact ⟨x⟩

private theorem AdeqNrAddOne.nr_nonempty {W : Type*} {μ : Set (α → α → Prop)}
    (h : AdeqNrAddOne W β μ) (P : α → α → Prop) (x : β) : (nr W (addLastDot P x)).Nonempty := by
  obtain ⟨R, P', x', hP', hR⟩ := h
  have hR' : R ∈ nr W (addLastDot (rV : α → α → Prop) x) :=
    smor_trans hR (smor_addLastDot (n₀r_eq_n₀r_iff.1 hP') x' x)
  exact nr_nonempty_of_rsub ⟨R, hR'⟩ (addLastDot_sub_rV P x)

private theorem AdeqNrOneAdd.nr_nonempty {W : Type*} {μ : Set (α → α → Prop)}
    (h : AdeqNrOneAdd W β μ) (P : α → α → Prop) (x : β) : (nr W (addFirstDot x P)).Nonempty := by
  obtain ⟨R, P', x', hP', hR⟩ := h
  have hR' : R ∈ nr W (addFirstDot x (rV : α → α → Prop)) :=
    smor_trans hR (smor_addFirstDot (n₀r_eq_n₀r_iff.1 hP') x' x)
  exact nr_nonempty_of_rsub ⟨R, hR'⟩ (addFirstDot_sub_rV x P)

private theorem AdeqNrAddOne.eq_n₀r {W : Type*} {μ : Set (α → α → Prop)}
    (h : AdeqNrAddOne W β μ) (P : α → α → Prop) (x : β) :
    ∃ X : W → W → Prop, smor X (addLastDot P x) ∧ (nrAddOne β (n₀r P) : Set (W → W → Prop)) = n₀r X := by
  obtain ⟨X, hX⟩ := h.nr_nonempty P x
  exact ⟨X, hX, (nrAddOne_n₀r P x).trans (nr_eq_n₀r_of_mem hX)⟩

private theorem AdeqNrOneAdd.eq_n₀r {W : Type*} {μ : Set (α → α → Prop)}
    (h : AdeqNrOneAdd W β μ) (P : α → α → Prop) (x : β) :
    ∃ X : W → W → Prop, smor X (addFirstDot x P) ∧ (nrOneAdd β (n₀r P) : Set (W → W → Prop)) = n₀r X := by
  obtain ⟨X, hX⟩ := h.nr_nonempty P x
  exact ⟨X, hX, (nrOneAdd_n₀r P x).trans (nr_eq_n₀r_of_mem hX)⟩

/-! #### Ordinal sums with one or two added terms -/

private theorem rsum_addLast' {P Q : α → α → Prop} (hQ : rEx Q) (z : α) :
    P ⤉ Q ⇸ z = P ⤉ (Q ⇸ z) := by
  funext u v; apply propext
  have hPQ : rEx (P ⤉ Q) := by obtain ⟨a, b, h⟩ := hQ; exact ⟨a, b, Or.inl (Or.inr h)⟩
  simp only [rsum_apply, addLast_apply, fld_rsum, Set.mem_union, mem_fld_addLast, hQ, and_true]
  tauto

private theorem addLast_addLast' {P : α → α → Prop} (hP : rEx P) (x y : α) :
    P ⇸ x ⇸ y = P ⤉ x ↓ y := by
  funext u v; apply propext
  simp only [rsum_apply, addLast_apply, mem_fld_addLast, hP, and_true, couple_apply, fld_couple,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem addFirst_rsum' {P Q : α → α → Prop} (hP : rEx P) (z : α) :
    z ⇷ (P ⤉ Q) = (z ⇷ P) ⤉ Q := by
  funext u v; apply propext
  simp only [rsum_apply, addFirst_apply, fld_rsum, Set.mem_union, mem_fld_addFirst, hP, and_true]
  tauto

private theorem addFirst_addFirst' {P : α → α → Prop} (hP : rEx P) (x y : α) :
    x ⇷ y ⇷ P = (x ↓ y) ⤉ P := by
  funext u v; apply propext
  simp only [rsum_apply, addFirst_apply, mem_fld_addFirst, hP, and_true, couple_apply, fld_couple,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem addLast_rsum_eq {A B : α → α → Prop} (hA : rEx A) (hB : rEx B) (a : α) :
    A ⇸ a ⤉ B = A ⤉ (a ⇷ B) := by
  funext u v; apply propext
  simp only [rsum_apply, addLast_apply, addFirst_apply, mem_fld_addLast, mem_fld_addFirst, hA, hB,
    and_true]
  tauto

private theorem addLast_rsum_addFirst {A B : α → α → Prop} (hA : rEx A) (hB : rEx B) (a b : α) :
    A ⇸ a ⤉ (b ⇷ B) = A ⤉ a ↓ b ⤉ B := by
  funext u v; apply propext
  simp only [rsum_apply, addLast_apply, addFirst_apply, mem_fld_addLast, mem_fld_addFirst, hA, hB,
    and_true, fld_rsum, Set.mem_union, couple_apply, fld_couple, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  tauto

private theorem disj_graph {f : β → α} (hf : Function.Injective f) {A B : β → β → Prop}
    (h : Disjoint (fld A) (fld B)) : Disjoint (fld (graph f ⁏ A)) (fld (graph f ⁏ B)) := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  obtain ⟨z, hz, rfl⟩ := mem_fld_graph_semi.1 hu
  obtain ⟨w, hw, e⟩ := mem_fld_graph_semi.1 hu'
  rw [hf e] at hz
  exact Set.disjoint_left.1 h hz hw

private theorem notin_graph {f : β → α} (hf : Function.Injective f) {A : β → β → Prop} {z : β}
    (h : z ∉ fld A) : f z ∉ fld (graph f ⁏ A) := by
  intro h'
  obtain ⟨w, hw, e⟩ := mem_fld_graph_semi.1 h'
  exact h (hf e ▸ hw)

private theorem rEx_graph {f : β → α} {A : β → β → Prop} : rEx (graph f ⁏ A) ↔ rEx A := by
  constructor
  · rintro ⟨u, v, h⟩
    obtain ⟨z, w, -, hzw⟩ := (semi_apply _ _ _ _).1 h
    exact ⟨z, w, hzw⟩
  · rintro ⟨z, w, h⟩; exact ⟨f z, f w, (semi_apply _ _ _ _).2 ⟨z, w, ⟨rfl, rfl⟩, h⟩⟩

private theorem disj_addLast {A B : α → α → Prop} {b : α} (h : Disjoint (fld A) (fld B))
    (hb : b ∉ fld A) : Disjoint (fld A) (fld (B ⇸ b)) := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  obtain ⟨h' | rfl, -⟩ := mem_fld_addLast.1 hu'
  · exact Set.disjoint_left.1 h hu h'
  · exact hb hu

private theorem disj_addFirst {A B : α → α → Prop} {a : α} (h : Disjoint (fld A) (fld B))
    (ha : a ∉ fld B) : Disjoint (fld (a ⇷ A)) (fld B) := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  obtain ⟨h' | rfl, -⟩ := mem_fld_addFirst.1 hu
  · exact Set.disjoint_left.1 h h' hu'
  · exact ha hu'

/-- The image of a sum under `y ↦ ι'y ↓ Λ` splits. -/
private theorem dotL_rplus_split (P : α → α → Prop) (Q : β → β → Prop) (W : Type*) :
    ∃ A B, graph (fun y => ι y ↓ (∅ : Set W)) ⁏ (P +ᵣ Q) = A ⤉ B ∧ (smor A P ∧ smor B Q) ∧
      Disjoint (fld A) (fld B) := by
  obtain ⟨L, R, e, ⟨hL, hR⟩, hd⟩ := rplus_split P Q
  refine ⟨_, _, by rw [e, graph_semi_rsum], ⟨smor_trans (smor_graph_inj inj_dotL L) hL,
    smor_trans (smor_graph_inj inj_dotL R) hR⟩, disj_graph inj_dotL hd⟩

private theorem dotR_rplus_split (P : α → α → Prop) (Q : β → β → Prop) (W : Type*) :
    ∃ A B, graph (fun y => (∅ : Set W) ↓ ι y) ⁏ (P +ᵣ Q) = A ⤉ B ∧ (smor A P ∧ smor B Q) ∧
      Disjoint (fld A) (fld B) := by
  obtain ⟨L, R, e, ⟨hL, hR⟩, hd⟩ := rplus_split P Q
  refine ⟨_, _, by rw [e, graph_semi_rsum], ⟨smor_trans (smor_graph_inj inj_dotR L) hL,
    smor_trans (smor_graph_inj inj_dotR R) hR⟩, disj_graph inj_dotR hd⟩


private theorem rplus_eq' (P : α → α → Prop) (Q : β → β → Prop) :
    P +ᵣ Q = graph (fun x => ι x ↓ (∅ : Set β)) ⁏ P ⤉ graph (fun y => (∅ : Set α) ↓ ι y) ⁏ Q := by
  rw [rplus_eq, null_inter, null_inter]

private theorem dL_ne_dR (u : α) (v : β) : (ι u ↓ (∅ : Set β)) ≠ ((∅ : Set α) ↓ ι v) :=
  fun h => unitCls_ne_empty u (couple_eq_couple_iff.1 h).1

private theorem disj_dL_dR (A : α → α → Prop) (B : β → β → Prop) :
    Disjoint (fld (graph (fun x => ι x ↓ (∅ : Set β)) ⁏ A))
      (fld (graph (fun y => (∅ : Set α) ↓ ι y) ⁏ B)) := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  obtain ⟨x, -, rfl⟩ := mem_fld_graph_semi.1 hu
  obtain ⟨y, -, h⟩ := mem_fld_graph_semi.1 hu'
  exact dL_ne_dR x y h

private theorem dL_notin_dR {A : β → β → Prop} (u : α) :
    (ι u ↓ (∅ : Set β)) ∉ fld (graph (fun y => (∅ : Set α) ↓ ι y) ⁏ A) := by
  intro h
  obtain ⟨y, -, e⟩ := mem_fld_graph_semi.1 h
  exact dL_ne_dR u y e

private theorem dR_notin_dL {A : α → α → Prop} (v : β) :
    ((∅ : Set α) ↓ ι v) ∉ fld (graph (fun x => ι x ↓ (∅ : Set β)) ⁏ A) := by
  intro h
  obtain ⟨x, -, e⟩ := mem_fld_graph_semi.1 h
  exact dL_ne_dR x v e.symm

private theorem smor_rsum3 {A B C : α → α → Prop} {A' B' C' : β → β → Prop}
    (hA : smor A A') (hB : smor B B') (hC : smor C C')
    (d1 : Disjoint (fld A) (fld B)) (d2 : Disjoint (fld A ∪ fld B) (fld C))
    (d1' : Disjoint (fld A') (fld B')) (d2' : Disjoint (fld A' ∪ fld B') (fld C')) :
    smor (A ⤉ B ⤉ C) (A' ⤉ B' ⤉ C') :=
  smor_rsum (smor_rsum hA hB d1 d1') hC (by rwa [fld_rsum]) (by rwa [fld_rsum])

private theorem disj_addFirst_right {A B : α → α → Prop} {a : α} (h : Disjoint (fld A) (fld B))
    (ha : a ∉ fld A) : Disjoint (fld A) (fld (a ⇷ B)) := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  obtain ⟨h' | rfl, -⟩ := mem_fld_addFirst.1 hu'
  · exact Set.disjoint_left.1 h hu h'
  · exact ha hu

private theorem disj_couple {A : α → α → Prop} {a b : α} (ha : a ∉ fld A) (hb : b ∉ fld A) :
    Disjoint (fld A) (fld (a ↓ b)) := by
  rw [fld_couple]
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  rcases hu' with rfl | rfl
  · exact ha hu
  · exact hb hu

/-- `(P + Q) ⇸̇ x smor P + (Q ⇸̇ x')` when `∃̇!Q` (cf. ✱181·54). -/
private theorem smor_addLastDot_rplus {ε ε' : Type*} {P : α → α → Prop} {Q : β → β → Prop}
    (hQ : rEx Q) (x : ε) (x' : ε') : smor (addLastDot (P +ᵣ Q) x) (P +ᵣ addLastDot Q x') := by
  obtain ⟨A, B, hAB, ⟨hA, hB⟩, hd⟩ := dotL_rplus_split P Q ε
  have hn := notin_dotL (P +ᵣ Q) x
  rw [hAB, fld_rsum] at hn
  rw [addLastDot_eq, hAB, rsum_addLast' (smor_preserves (smor_symm hB) hQ)]
  obtain ⟨L, R, e', ⟨hL, hR⟩, hd'⟩ := rplus_split P (addLastDot Q x')
  obtain ⟨L₂, e₂, h₂, hL₂, hn₂⟩ := addLastDot_split Q x'
  rw [e']
  rw [h₂] at hR
  exact smor_rsum (smor_trans hA (smor_symm hL))
    (smor_trans (smor_addLast (smor_trans hB (smor_symm hL₂)) (fun h => hn (Or.inr h)) hn₂)
      (smor_symm hR))
    (disj_addLast hd fun h => hn (Or.inl h)) hd'

/-- `x ⇷̇ (P + Q) smor (x' ⇷̇ P) + Q` when `∃̇!P` (cf. ✱181·55). -/
private theorem smor_addFirstDot_rplus {ε ε' : Type*} {P : α → α → Prop} {Q : β → β → Prop}
    (hP : rEx P) (x : ε) (x' : ε') : smor (addFirstDot x (P +ᵣ Q)) (addFirstDot x' P +ᵣ Q) := by
  obtain ⟨A, B, hAB, ⟨hA, hB⟩, hd⟩ := dotR_rplus_split P Q ε
  have hn := notin_dotR x (P +ᵣ Q)
  rw [hAB, fld_rsum] at hn
  rw [addFirstDot_eq, hAB, addFirst_rsum' (smor_preserves (smor_symm hA) hP)]
  obtain ⟨L, R, e', ⟨hL, hR⟩, hd'⟩ := rplus_split (addFirstDot x' P) Q
  obtain ⟨L₂, e₂, h₂, hL₂, hn₂⟩ := addFirstDot_split x' P
  rw [e']
  rw [h₂] at hL
  exact smor_rsum (smor_trans (smor_addFirst (smor_trans hA (smor_symm hL₂))
      (fun h => hn (Or.inl h)) hn₂) (smor_symm hL)) (smor_trans hB (smor_symm hR))
    (disj_addFirst hd fun h => hn (Or.inr h)) hd'

/-- `∃̇!P . a ≠ b . ⊃ . (P ⇸̇ x) ⇸̇ y smor P + (a ↓ b)` (✱181·53). -/
private theorem smor_dot_dot {ε ε' W : Type*} {P : α → α → Prop} (hP : rEx P) (x : ε) (y : ε')
    {a b : W} (hab : a ≠ b) : smor (addLastDot (addLastDot P x) y) (P +ᵣ (a ↓ b)) := by
  have hn₂ := notin_dotL (addLastDot P x) y
  have hn₁ := notin_dotL P x
  rw [addLastDot_eq P x, graph_semi_addLast] at hn₂
  rw [addLastDot_eq (addLastDot P x) y, addLastDot_eq P x, graph_semi_addLast]
  have hL : rEx (graph (fun y => ι y ↓ (∅ : Set ε')) ⁏ graph (fun y => ι y ↓ (∅ : Set ε)) ⁏ P) :=
    rEx_graph.2 (rEx_graph.2 hP)
  rw [addLast_addLast' hL, rplus_eq']
  have hne : (ι ((∅ : Set α) ↓ ι x) ↓ (∅ : Set ε')) ≠
      ((∅ : Set (Set α → Set ε → Prop)) ↓ ι y) :=
    fun h => hn₂ (by rw [mem_fld_addLast]; exact ⟨Or.inr h.symm, hL⟩)
  refine smor_rsum (smor_trans (smor_trans (smor_graph_inj inj_dotL _)
    (smor_graph_inj inj_dotL _)) (smor_symm (smor_graph_inj inj_dotL _))) ?_ ?_
    (disj_dL_dR _ _)
  · rw [graph_semi_couple]
    exact smor_couple hne (fun h => hab (inj_dotR h))
  · refine disj_couple (notin_graph inj_dotL hn₁) ?_
    intro h
    exact hn₂ (by rw [mem_fld_addLast]; exact ⟨Or.inl h, hL⟩)

/-- `∃̇!P . a ≠ b . ⊃ . y ⇷̇ (x ⇷̇ P) smor (a ↓ b) + P` (cf. ✱181·57). -/
private theorem smor_first_first {ε ε' W : Type*} {P : α → α → Prop} (hP : rEx P) (x : ε)
    (y : ε') {a b : W} (hab : a ≠ b) :
    smor (addFirstDot y (addFirstDot x P)) ((a ↓ b) +ᵣ P) := by
  have hn₂ := notin_dotR y (addFirstDot x P)
  have hn₁ := notin_dotR x P
  rw [addFirstDot_eq x P, graph_semi_addFirst] at hn₂
  rw [addFirstDot_eq y (addFirstDot x P), addFirstDot_eq x P, graph_semi_addFirst]
  have hL : rEx (graph (fun y => (∅ : Set ε') ↓ ι y) ⁏ graph (fun y => (∅ : Set ε) ↓ ι y) ⁏ P) :=
    rEx_graph.2 (rEx_graph.2 hP)
  rw [addFirst_addFirst' hL, rplus_eq']
  have hne : (ι y ↓ (∅ : Set (Set ε → Set α → Prop))) ≠
      ((∅ : Set ε') ↓ ι (ι x ↓ (∅ : Set α))) :=
    fun h => hn₂ (by rw [mem_fld_addFirst]; exact ⟨Or.inr h, hL⟩)
  refine smor_rsum ?_ (smor_trans (smor_trans (smor_graph_inj inj_dotR _)
    (smor_graph_inj inj_dotR _)) (smor_symm (smor_graph_inj inj_dotR _))) ?_ (disj_dL_dR _ _)
  · rw [graph_semi_couple]
    exact smor_couple hne (fun h => hab (inj_dotL h))
  · refine Disjoint.symm (disj_couple ?_ (notin_graph inj_dotR hn₁))
    intro h
    exact hn₂ (by rw [mem_fld_addFirst]; exact ⟨Or.inl h, hL⟩)

/-- `(P ⇸̇ x) + Q smor P + (x' ⇷̇ Q)` when `∃̇!P . ∃̇!Q` (cf. ✱181·58). -/
private theorem smor_dot_rplus_dot {ε ε' : Type*} {P : α → α → Prop} {Q : β → β → Prop}
    (hP : rEx P) (hQ : rEx Q) (x : ε) (x' : ε') :
    smor (addLastDot P x +ᵣ Q) (P +ᵣ addFirstDot x' Q) := by
  rw [rplus_eq', rplus_eq', addLastDot_eq, addFirstDot_eq, graph_semi_addLast, graph_semi_addFirst]
  rw [addLast_rsum_eq (rEx_graph.2 (rEx_graph.2 hP)) (rEx_graph.2 hQ)]
  refine smor_rsum (smor_trans (smor_graph_inj inj_dotL _) (smor_trans (smor_graph_inj inj_dotL _)
    (smor_symm (smor_graph_inj inj_dotL _)))) (smor_addFirst (smor_trans
      (smor_graph_inj inj_dotR _) (smor_symm (smor_trans (smor_graph_inj inj_dotR _)
        (smor_graph_inj inj_dotR _)))) (dL_notin_dR _) (notin_graph inj_dotR (notin_dotR x' Q)))
    ?_ ?_
  · exact disj_addFirst_right (disj_dL_dR _ _) (notin_graph inj_dotL (notin_dotL P x))
  · exact disj_addFirst_right (disj_dL_dR _ _) (dR_notin_dL _)

/-- `(P ⇸̇ x) + (y ⇷̇ Q) smor P + (a ↓ b) + Q` when `∃̇!P . ∃̇!Q . a ≠ b` (cf. ✱181·59). -/
private theorem smor_dot_rplus_dot2 {ε ε' W : Type*} {P : α → α → Prop} {Q : β → β → Prop}
    (hP : rEx P) (hQ : rEx Q) (x : ε) (y : ε') {a b : W} (hab : a ≠ b) :
    smor (addLastDot P x +ᵣ addFirstDot y Q) (P +ᵣ (a ↓ b) +ᵣ Q) := by
  rw [rplus_eq' (addLastDot P x), addLastDot_eq, addFirstDot_eq, graph_semi_addLast,
    graph_semi_addFirst]
  rw [addLast_rsum_addFirst (rEx_graph.2 (rEx_graph.2 hP)) (rEx_graph.2 (rEx_graph.2 hQ))]
  rw [rplus_eq' (P +ᵣ (a ↓ b)), rplus_eq' P (a ↓ b), graph_semi_rsum, graph_semi_couple,
    graph_semi_couple]
  refine smor_rsum3 (smor_trans (smor_graph_inj inj_dotL _) (smor_trans (smor_graph_inj inj_dotL _)
      (smor_symm (smor_trans (smor_graph_inj inj_dotL _) (smor_graph_inj inj_dotL _)))))
    (smor_couple (dL_ne_dR _ _) (fun h => hab (inj_dotR (inj_dotL h))))
    (smor_trans (smor_graph_inj inj_dotR _) (smor_trans (smor_graph_inj inj_dotR _)
      (smor_symm (smor_graph_inj inj_dotR _)))) ?_ ?_ ?_ ?_
  · exact disj_couple (notin_graph inj_dotL (notin_dotL P x)) (dR_notin_dL _)
  · rw [fld_couple]
    refine Set.disjoint_left.2 fun u hu hu' => ?_
    rcases hu with hu | (rfl | rfl)
    · exact Set.disjoint_left.1 (disj_dL_dR _ _) hu hu'
    · exact dL_notin_dR _ hu'
    · exact notin_graph inj_dotR (notin_dotR y Q) hu'
  · exact disj_couple (notin_graph inj_dotL (dR_notin_dL _)) (notin_graph inj_dotL (dR_notin_dL _))
  · rw [fld_couple]
    refine Set.disjoint_left.2 fun u hu hu' => ?_
    rcases hu with hu | (rfl | rfl)
    · exact Set.disjoint_left.1 (disj_dL_dR _ _) hu hu'
    · exact dL_notin_dR _ hu'
    · exact dL_notin_dR _ hu'

end Helpers181b

section Helpers181d

private theorem sm_union_clsSum {ε ε' : Type*} {A B : Set γ} {A' : Set ε} {B' : Set ε'}
    (hd : Disjoint A B) (hA : sm A A') (hB : sm B B') : sm (A ∪ B) (A' +ₐ B') := by
  classical
  obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 hA
  obtain ⟨eB⟩ := sm_iff_nonempty_equiv.1 hB
  exact sm_iff_nonempty_equiv.2
    ⟨(Equiv.Set.union hd).trans ((eA.sumCongr eB).trans (clsSumEquiv A' B').symm)⟩

private theorem sm_singleton {a : γ} {b : δ} : sm ({a} : Set γ) ({b} : Set δ) :=
  sm_iff_nonempty_equiv.2 ⟨Equiv.ofUnique _ _⟩

private theorem fld_addLast_eq {P : α → α → Prop} (hP : rEx P) (x : α) :
    fld (P ⇸ x) = fld P ∪ {x} := by
  ext z; rw [mem_fld_addLast]
  simp only [hP, and_true, Set.mem_union, Set.mem_singleton_iff]

private theorem fld_addFirst_eq {P : α → α → Prop} (hP : rEx P) (x : α) :
    fld (x ⇷ P) = {x} ∪ fld P := by
  ext z; rw [mem_fld_addFirst]
  simp only [hP, and_true, Set.mem_union, Set.mem_singleton_iff]
  tauto

private theorem fld_addLastDot_sm {P : α → α → Prop} (hP : rEx P) (x : β) :
    sm (fld (addLastDot P x)) (fld P +ₐ ({x} : Set β)) := by
  obtain ⟨L, e, h1, h2, h3⟩ := addLastDot_split P x
  rw [h1, fld_addLast_eq (smor_preserves (smor_symm h2) hP)]
  exact sm_union_clsSum (Set.disjoint_singleton_right.2 h3) (sm_fld_of_smor h2) sm_singleton

private theorem fld_addFirstDot_sm {P : α → α → Prop} (hP : rEx P) (x : β) :
    sm (fld (addFirstDot x P)) (fld P +ₐ ({x} : Set β)) := by
  obtain ⟨L, e, h1, h2, h3⟩ := addFirstDot_split x P
  rw [h1, fld_addFirst_eq (smor_preserves (smor_symm h2) hP)]
  refine sm_trans (sm_union_clsSum (Set.disjoint_singleton_left.2 h3) (sm_singleton (b := x))
    (sm_fld_of_smor h2)) ?_
  exact sm_iff_nonempty_equiv.2 ⟨(clsSumEquiv _ _).trans ((Equiv.sumComm _ _).trans
    (clsSumEquiv _ _).symm)⟩

private theorem addFirst_rNull (x : α) : x ⇷ (rNull : α → α → Prop) = rNull := by
  funext u v; apply propext
  rw [addFirst_apply, fld_rNull]
  exact ⟨fun h => h.elim (fun h => absurd h.2 (Set.notMem_empty v)) id, fun h => Or.inr h⟩

private theorem C_img_nr_addLastDot {W : Type*} [Nonempty W] {P : α → α → Prop} (hP : rEx P)
    (x : β) : C ʻʻ nr γ (addLastDot P x) = (n₀c (fld P) +ᶜ (one : Set (Set W)) : Set (Set γ)) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨L, e, h1, h2, h3⟩ := addLastDot_split P x
  rw [C_img_nr, one_eq_n₀c_singleton w, n₀c_cardAdd_n₀c, h1,
    fld_addLast_eq (smor_preserves (smor_symm h2) hP)]
  exact nc_eq_nc_of_sm (sm_union_clsSum (Set.disjoint_singleton_right.2 h3) (sm_fld_of_smor h2)
    sm_singleton)

private theorem C_img_nr_addFirstDot {W : Type*} [Nonempty W] {P : α → α → Prop} (hP : rEx P)
    (x : β) : C ʻʻ nr γ (addFirstDot x P) = ((one : Set (Set W)) +ᶜ n₀c (fld P) : Set (Set γ)) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨L, e, h1, h2, h3⟩ := addFirstDot_split x P
  rw [C_img_nr, one_eq_n₀c_singleton w, n₀c_cardAdd_n₀c, h1,
    fld_addFirst_eq (smor_preserves (smor_symm h2) hP)]
  exact nc_eq_nc_of_sm (sm_union_clsSum (Set.disjoint_singleton_left.2 h3) sm_singleton
    (sm_fld_of_smor h2))

private theorem nrAddOne_cases {μ : Set (α → α → Prop)} :
    (∃ P, μ = n₀r P) ∨ ∀ (β' γ' : Type*), (nrAddOne β' μ : Set (γ' → γ' → Prop)) = ∅ ∧
      (nrOneAdd β' μ : Set (γ' → γ' → Prop)) = ∅ := by
  by_cases h : ∃ P, μ = n₀r P
  · exact Or.inl h
  · push Not at h; exact Or.inr fun _ _ => ⟨nrAddOne_empty_of h, nrOneAdd_empty_of h⟩

end Helpers181d

/-!
## [✱181] On the addition of unity to a relation-number

*(Vol. 2, p. 482)*

> *Summary of* *181.
>
> The relation-number \(\dot{1}\) has, according to our definitions, no meaning in isolation, because our definitions are framed with a view to series, and a series cannot consist of one term. But we can *add* one term to a series; hence \(\dot{1}\) is required as an addendum. In order to get our definitions in the most manageable form, we first construct a relation, which we call \(P\dot{\unicode{x21f8}}x\), which is such that, whenever \(P\) exists, \(P\dot{\unicode{x21f8}}x\) has one more term in its field than \(P\); the relation-number of this relation is then defined as \(\text{Nr}ʻP\dot{+} \dot{1}\). We add also a definition \[ \dot{1} \dot{+} \dot{1} =2_r \quad\text{Df} \] which is purely formal, and serves to minimize exceptions to the associative law of addition.
>
> …

**Lean reading.** `P ⇸̇ x` is `addLastDot P x`, `x ⇷̇ P` is `addFirstDot x P` (relations between classes, for
`P` on `α` and `x : β`; `Λ_x` is `clsT Λ x`); `μ +̇ 1̇` is `nrAddOne β μ`, `1̇ +̇ μ` is `nrOneAdd β μ`,
where `β` is the type of the apparent `x` of ✱181·02·021, a parameter of its own; the actual type
`γ` is implicit. `1̇ +̇ 1̇` is `two_r` (✱181·04), `μ +̇ 1̇ +̇ 1̇` is `μ ∔ two_r`, `1̇ +̇ 1̇ +̇ μ` is
`two_r ∔ μ` (✱181·561·571). An argument `Nr'P` is `n₀r P` (✱181·03·031). An inner sum, a `+̇ 1̇`
or `2_r` in an arithmetical position has its own type with an adequacy hypothesis (IIT); the
cardinal `1` of ✱181·6–·62 likewise (`[Nonempty W]`). Where a `μ +̇ 1̇` with an empty type of its
apparent `x` would make the proposition false, that type is assumed `[Nonempty β]` (Basic §3).

**Status.** proved (all propositions; ✱181·01·011·02·021·03·031·04·561·571 definition; ✱181·3·32·33·4·42·43·54·55·56·57·58·59·6·61·62 proved (reading), see their docstrings)
-/

/-- ✱181·01 (Df). \(P \dot{\unicode{x21f8}} x = \downarrow \Lambda _{x}^{;}{℩}^{;}P \unicode{x21f8} (\Lambda \cap CʻP) \downarrow {℩}ʻx \quad\text{Df}\) -/
theorem pm181_01 {P : α → α → Prop} {x : β} :
    addLastDot P x = (coupleR (clsT Λ x) ⁏ iota ⁏ P) ⇸ ((Λ ∩ fld P) ↓ ι x) := rfl

/-- ✱181·011 (Df). \(x \dot{\unicode{x21f7}} P = ({℩}ʻx) \downarrow (\Lambda \cap CʻP) \unicode{x21f7} \Lambda _{x} \downarrow ^{;}{℩}^{;}P \quad\text{Df}\) -/
theorem pm181_011 {x : β} {P : α → α → Prop} :
    addFirstDot x P = (ι x ↓ (Λ ∩ fld P)) ⇷ (coupleL (clsT Λ x) ⁏ iota ⁏ P) := rfl

/-- ✱181·02 (Df). \(\mu \dot{+} \dot{1} = \hat{R} \{(\exists P, x) . \text{N}_{0}\text{r}ʻP = \mu . R \,\text{smor}\, (P \dot{\unicode{x21f8}} x)\} \quad\text{Df}\) -/
theorem pm181_02 {μ : Set (α → α → Prop)} : (nrAddOne β μ : Set (γ → γ → Prop)) =
    {R | ∃ (P : α → α → Prop) (x : β), n₀r P = μ ∧ smor R (addLastDot P x)} := rfl

/-- ✱181·021 (Df). \(\dot{1} \dot{+} \mu = \hat{R} \{(\exists P, x) . \text{N}_{0}\text{r}ʻP = \mu . R \,\text{smor}\, (x \dot{\unicode{x21f7}} P)\} \quad\text{Df}\) -/
theorem pm181_021 {μ : Set (α → α → Prop)} : (nrOneAdd β μ : Set (γ → γ → Prop)) =
    {R | ∃ (P : α → α → Prop) (x : β), n₀r P = μ ∧ smor R (addFirstDot x P)} := rfl

/-- ✱181·03 (Df). \(\text{Nr}ʻP \dot{+} \dot{1} = \text{N}_{0}\text{r}ʻP \dot{+} \dot{1} \quad\text{Df}\)

A rule of translation (normal adjustment), as ✱180·03. -/
theorem pm181_03 {P : α → α → Prop} :
    (nrAddOne β (n₀r P) : Set (γ → γ → Prop)) = nrAddOne β (n₀r P) := rfl

/-- ✱181·031 (Df). \(\dot{1} \dot{+} \text{Nr}ʻP = \dot{1} \dot{+} \text{N}_{0}\text{r}ʻP \quad\text{Df}\)

A rule of translation (normal adjustment), as ✱180·03. -/
theorem pm181_031 {P : α → α → Prop} :
    (nrOneAdd β (n₀r P) : Set (γ → γ → Prop)) = nrOneAdd β (n₀r P) := rfl

/-- ✱181·04 (Df). \(\dot{1} \dot{+} \dot{1} = 2_{r} \quad\text{Df}\)

"Purely formal" (PM): a rule of translation, the symbol `1̇ +̇ 1̇` is written `two_r` (✱56·02). -/
theorem pm181_04 : (two_r : Set (α → α → Prop)) = {R | ∃ x y, x ≠ y ∧ R = x ↓ y} := rfl

/-- ✱181·1. \[\begin{align}\vdash \colon\ldotp &R(P \dot{\unicode{x21f8}} x)S . \equiv : (\exists y, z) . yPz . R = ({℩}ʻy) \downarrow \Lambda _{x} . S = ({℩}ʻz) \downarrow \Lambda _{x} . \lor .\\ &(\exists y) . y \in CʻP . R = ({℩}ʻy) \downarrow \Lambda _{x} . S = (\Lambda \cap CʻP) \downarrow {℩}ʻx \quad[(*181·01)]\end{align}\] -/
theorem pm181_1 {P : α → α → Prop} {x : β} {R S : Set α → Set β → Prop} :
    addLastDot P x R S ↔ (∃ y z, (P y z ∧ R = ι y ↓ clsT Λ x) ∧ S = ι z ↓ clsT Λ x) ∨
      ∃ y, (y ∈ fld P ∧ R = ι y ↓ clsT Λ x) ∧ S = (Λ ∩ fld P) ↓ ι x := by
  show ((coupleR (clsT Λ x) ⁏ iota ⁏ P) ⇸ ((Λ ∩ fld P) ↓ ι x)) R S ↔ _
  rw [semi_semi, coupleR_iota, addLast_apply, semi_graph_apply, mem_fld_graph_semi]
  constructor
  · rintro (⟨y, z, ⟨hR, hS⟩, h⟩ | ⟨⟨y, hy, hR⟩, hS⟩)
    · exact Or.inl ⟨y, z, ⟨h, hR⟩, hS⟩
    · exact Or.inr ⟨y, ⟨hy, hR⟩, hS⟩
  · rintro (⟨y, z, ⟨h, hR⟩, hS⟩ | ⟨y, ⟨hy, hR⟩, hS⟩)
    · exact Or.inl ⟨y, z, ⟨hR, hS⟩, h⟩
    · exact Or.inr ⟨⟨y, hy, hR⟩, hS⟩

/-- ✱181·11. \(\vdash . (\Lambda \cap CʻP) \downarrow {℩}ʻx {\sim} \in Cʻ \downarrow \Lambda _{x}^{;}{℩}^{;}P\) -/
theorem pm181_11 {P : α → α → Prop} {x : β} :
    (Λ ∩ fld P) ↓ ι x ∉ fld (coupleR (clsT Λ x) ⁏ iota ⁏ P) := by
  rw [semi_semi, coupleR_iota, clsT_null, null_inter]
  exact notin_dotL P x

/-- ✱181·12. \(\vdash . \downarrow \Lambda _{x}^{;}{℩}^{;}P \,\,\text{smor}\, P \quad[*151·61·65]\) -/
theorem pm181_12 {P : α → α → Prop} {x : β} : smor (coupleR (clsT Λ x) ⁏ iota ⁏ P) P := by
  rw [semi_semi, coupleR_iota]
  exact smor_graph_inj (fun _ _ h => unitCls_injective (couple_eq_couple_iff.1 h).1) P

/-- ✱181·13. \(\vdash : Q \,\text{smor}\, P . y {\sim} \in CʻQ . \supset . Q \unicode{x21f8} y \,\text{smor}\, P \dot{\unicode{x21f8}} x\) -/
theorem pm181_13 {Q : δ → δ → Prop} {P : α → α → Prop} {y : δ} {x : β} :
    smor Q P ∧ y ∉ fld Q → smor (Q ⇸ y) (addLastDot P x) := fun ⟨h, hy⟩ =>
  smor_addLast_dot h hy x

/-- ✱181·2. \(\vdash :Z\in \mu \dot{+} \dot{1} .\equiv .(\exists P,x).\mu =\text{N}_{0}\text{r}ʻP.Z\,\text{smor}\,(P\dot{\unicode{x21f8}} x) \quad[(*181·02)]\) -/
theorem pm181_2 {μ : Set (α → α → Prop)} {Z : γ → γ → Prop} :
    Z ∈ (nrAddOne β μ : Set (γ → γ → Prop)) ↔
      ∃ (P : α → α → Prop) (x : β), μ = n₀r P ∧ smor Z (addLastDot P x) :=
  ⟨fun ⟨P, x, h1, h2⟩ => ⟨P, x, h1.symm, h2⟩, fun ⟨P, x, h1, h2⟩ => ⟨P, x, h1.symm, h2⟩⟩

/-- ✱181·21. \[\begin{align}&\vdash \colon\ldotp \mu \in \text{NR}.\supset :Z\in \mu \dot{+} \dot{1} .\equiv .(\exists P,x).P\in \mu .Z\,\text{smor}\,(P\dot{\unicode{x21f8}} x)\\ &[*181·2 .*155·26]\end{align}\]

`μ ∈ NR` with the type of its `NR` free. -/
theorem pm181_21 {β' : Type*} {μ : Set (α → α → Prop)} {Z : γ → γ → Prop} :
    μ ∈ NR β' → (Z ∈ (nrAddOne β μ : Set (γ → γ → Prop)) ↔
      ∃ (P : α → α → Prop) (x : β), P ∈ μ ∧ smor Z (addLastDot P x)) := by
  intro hμ
  rw [pm181_2]
  constructor
  · rintro ⟨P, x, rfl, h⟩; exact ⟨P, x, self_mem_n₀r P, h⟩
  · rintro ⟨P, x, hP, h⟩
    rcases NR_cases hμ with rfl | ⟨P', rfl⟩
    · exact absurd hP (Set.notMem_empty P)
    · exact ⟨P, x, n₀r_eq_n₀r_iff.2 (smor_symm (mem_n₀r.1 hP)), h⟩

/-- ✱181·24. \(\vdash :P\,\,\text{smor}\,\,Q.\supset .\text{N}_{0}\text{r}ʻP\dot{+} \dot{1} =\text{N}_{0}\text{r}ʻQ\dot{+} 1 \quad[*181·22·12·11.*161·31]\)

(The e-text's `N₀r'Q +̇ 1` is `N₀r'Q +̇ 1̇`.) -/
theorem pm181_24 {P : α → α → Prop} {Q : δ → δ → Prop} : smor P Q →
    (nrAddOne β (n₀r P) : Set (γ → γ → Prop)) = nrAddOne β (n₀r Q) := by
  intro h
  rcases isEmpty_or_nonempty β with hβ | hβ
  · rw [nrAddOne_isEmpty, nrAddOne_isEmpty]
  · obtain ⟨x⟩ := hβ
    rw [nrAddOne_n₀r P x, nrAddOne_n₀r Q x]
    exact nr_eq_nr_of_smor (smor_addLastDot h x x)

/-- ✱181·3. \(\vdash .\text{Nr}ʻP\dot{+} \dot{1} =\text{N}_{0}\text{r}ʻP\dot{+} \dot{1} =\text{Nr}ʻ(P\dot{\unicode{x21f8}} x) \quad[*181·22.(*181·03)]\)

The `x` of `P ⇸̇ x` is of the type `β` of the apparent `x` of ✱181·02 (so that type is not empty);
by ✱181·03 the first equation is the identity of the two readings.

**Status.** proved (reading): by the Df ✱181·03 the argument Nr'P of +̇ 1̇ is read N₀r'P; the type
of the apparent `x` of ✱181·02 is taken to be that of the real `x` -/
theorem pm181_3 {P : α → α → Prop} {x : β} :
    (nrAddOne β (n₀r P) : Set (γ → γ → Prop)) = nrAddOne β (n₀r P) ∧
      (nrAddOne β (n₀r P) : Set (γ → γ → Prop)) = nr γ (addLastDot P x) :=
  ⟨rfl, nrAddOne_n₀r P x⟩

/-- ✱181·31. \(\vdash :P\,\,\text{smor}\,\,Q.\supset .\text{Nr}ʻP\dot{+} \dot{1} =\text{Nr}ʻQ\dot{+} \dot{1} \quad[*181·3·24]\) -/
theorem pm181_31 {P : α → α → Prop} {Q : δ → δ → Prop} : smor P Q →
    (nrAddOne β (n₀r P) : Set (γ → γ → Prop)) = nrAddOne β (n₀r Q) := pm181_24

/-- ✱181·32. \(\vdash :x{\sim}\in CʻP.\supset .\text{Nr}ʻP\dot{+} \dot{1} =\text{Nr}ʻ(P\unicode{x21f8} x) \quad[*181·3·13]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I): the type
`β` of the apparent `x` of ✱181·02 is `[Nonempty β]` (for an empty `β`, `μ +̇ 1̇ = Λ`) -/
theorem pm181_32 [Nonempty β] {P : α → α → Prop} {x : α} :
    x ∉ fld P → (nrAddOne β (n₀r P) : Set (γ → γ → Prop)) = nr γ (P ⇸ x) := by
  intro hx
  obtain ⟨b⟩ := ‹Nonempty β›
  rw [nrAddOne_n₀r P b]
  exact nr_eq_nr_of_smor (smor_symm (smor_addLast_dot (smor_refl P) hx b))

/-- ✱181·33. \[\begin{align}&\vdash \colon\ldotp \mu ,\nu \in \text{NR}.\exists !\mu \dot{+} \dot{1} .\supset :\mu =\nu .\equiv .\mu \dot{+} \dot{1} =\nu \dot{+} \dot{1} .\equiv .\dot{1} \dot{+} \mu =\dot{1} \dot{+} \nu \\ &[*161·33.*181·3·11·12]\end{align}\]

`μ, ν ∈ NR` have independent `NR` types; `μ +̇ 1̇`, `ν +̇ 1̇`, `1̇ +̇ μ`, `1̇ +̇ ν` are in one type `γ`, that
of the hypothesis `∃!μ +̇ 1̇` (convention AT); likewise the apparent `x` of all four is taken in one
type `β`, that of the hypothesis.

**Status.** proved (reading): convention AT (Prefatory Statement, VI): the equations (and the
apparent `x` of the four `+̇ 1̇`, `1̇ +̇`) are taken in the types in which `∃!μ +̇ 1̇` is asserted -/
theorem pm181_33 {β₁ β₂ : Type*} {μ ν : Set (α → α → Prop)} :
    (μ ∈ NR β₁ ∧ ν ∈ NR β₂) ∧ (nrAddOne β μ : Set (γ → γ → Prop)).Nonempty →
      (μ = ν ↔ (nrAddOne β μ : Set (γ → γ → Prop)) = nrAddOne β ν) ∧
        ((nrAddOne β μ : Set (γ → γ → Prop)) = nrAddOne β ν ↔
          (nrOneAdd β μ : Set (γ → γ → Prop)) = nrOneAdd β ν) := by
  rintro ⟨⟨-, hν⟩, ⟨Z, P, x, hP, hZ⟩⟩
  subst hP
  -- `1̇ +̇ μ` exists in `γ` as well
  have hfirst : (nr γ (addFirstDot x P)).Nonempty := by
    by_cases hP : rEx P
    · obtain ⟨f, hf⟩ := nr_nonempty_iff.1 (⟨Z, hZ⟩ : (nr γ (addLastDot P x)).Nonempty)
      obtain ⟨e⟩ := sm_iff_nonempty_equiv.1
        (sm_trans (fld_addFirstDot_sm hP x) (sm_symm (fld_addLastDot_sm hP x)))
      exact nr_nonempty_iff.2 ⟨fun u => f (e u), hf.comp e.injective⟩
    · have : P = rNull := by by_contra h; exact hP (ne_rNull_iff.1 h)
      subst this
      exact ⟨rNull, by rw [addFirstDot_eq, graph_semi_rNull, addFirst_rNull]
                       exact smor_rNull_iff'.2 rfl⟩
  have key1 : ∀ Q : α → α → Prop, (nr γ (addLastDot P x) = nr γ (addLastDot Q x) ↔ smor P Q) :=
    fun Q => by
      rw [nr_eq_nr_iff ⟨Z, hZ⟩]
      constructor
      · intro h
        obtain ⟨L, e, h1, h2, h3⟩ := addLastDot_split P x
        obtain ⟨L', e', h1', h2', h3'⟩ := addLastDot_split Q x
        rw [h1, h1'] at h
        exact smor_trans (smor_symm h2) (smor_trans (smor_addLast_cancel h h3 h3') h2')
      · intro h; exact smor_addLastDot h x x
  have key2 : ∀ Q : α → α → Prop, (nr γ (addFirstDot x P) = nr γ (addFirstDot x Q) ↔ smor P Q) :=
    fun Q => by
      rw [nr_eq_nr_iff hfirst]
      constructor
      · intro h
        obtain ⟨L, e, h1, h2, h3⟩ := addFirstDot_split x P
        obtain ⟨L', e', h1', h2', h3'⟩ := addFirstDot_split x Q
        rw [h1, h1'] at h
        exact smor_trans (smor_symm h2) (smor_trans (smor_addFirst_cancel h h3 h3') h2')
      · intro h; exact smor_addFirstDot h x x
  rcases NR_cases hν with rfl | ⟨Q, rfl⟩
  · have e1 : (nrAddOne β (∅ : Set (α → α → Prop)) : Set (γ → γ → Prop)) = ∅ :=
      nrAddOne_empty_of fun P h => n₀r_ne_empty P h.symm
    have e2 : (nrOneAdd β (∅ : Set (α → α → Prop)) : Set (γ → γ → Prop)) = ∅ :=
      nrOneAdd_empty_of fun P h => n₀r_ne_empty P h.symm
    rw [e1, e2, nrAddOne_n₀r P x, nrOneAdd_n₀r P x]
    refine ⟨⟨fun h => absurd h (n₀r_ne_empty P), fun h => absurd h ?_⟩,
      ⟨fun h => absurd h ?_, fun h => absurd h ?_⟩⟩
    · exact Set.nonempty_iff_ne_empty.1 ⟨Z, hZ⟩
    · exact Set.nonempty_iff_ne_empty.1 ⟨Z, hZ⟩
    · exact Set.nonempty_iff_ne_empty.1 hfirst
  · rw [nrAddOne_n₀r P x, nrAddOne_n₀r Q x, nrOneAdd_n₀r P x, nrOneAdd_n₀r Q x, key1, key2,
      n₀r_eq_n₀r_iff]
    exact ⟨Iff.rfl, Iff.rfl⟩

/-- ✱181·4. \(\vdash :\exists !\mu \dot{+} \dot{1} .\supset .\mu \in \text{NR}-\iota ʻ\Lambda .\mu \in \text{N}_{0}\text{R} \quad[*181·2.*155·22]\)

**Status.** proved (reading): the ambiguous `NR` of the conclusion is taken in the type of the
members of `μ` (as ✱180·4) -/
theorem pm181_4 {μ : Set (α → α → Prop)} :
    (nrAddOne β μ : Set (γ → γ → Prop)).Nonempty → μ ∈ NR α \ ι Λ ∧ μ ∈ N₀R := by
  rintro ⟨Z, P, x, rfl, -⟩
  refine ⟨⟨n₀r_mem_NR P, ?_⟩, ⟨P, rfl⟩⟩
  rw [mem_unitCls, Null_eq_empty]; exact n₀r_ne_empty P

/-- ✱181·42. \(\vdash .\mu \dot{+} \dot{1} \in \text{NR}\)

**Status.** proved (reading): the ambiguous `NR` is taken as `NR^{t'Z}(Z)` (`NR (Set γ)`), as in
✱180·42 -/
theorem pm181_42 {μ : Set (α → α → Prop)} :
    (nrAddOne β μ : Set (γ → γ → Prop)) ∈ NR (Set γ) := by
  rcases Set.eq_empty_or_nonempty (nrAddOne β μ : Set (γ → γ → Prop)) with h | ⟨Z, P, x, hP, hZ⟩
  · rw [h]; exact empty_mem_NR_set
  · subst hP
    rw [nrAddOne_n₀r P x, nr_eq_n₀r_of_mem hZ]
    exact n₀r_mem_NR_set Z

/-- ✱181·43. \(\vdash :\mu \dot{+} 1=\text{N}_{0}\text{r}ʻZ.\equiv .Z\in \mu \dot{+} 1 \quad[*155·26.*181·42]\)

**Status.** proved (reading): transcription error: the e-text prints `μ +̇ 1` for `μ +̇ 1̇` -/
theorem pm181_43 {μ : Set (α → α → Prop)} {Z : γ → γ → Prop} :
    (nrAddOne β μ : Set (γ → γ → Prop)) = n₀r Z ↔ Z ∈ (nrAddOne β μ : Set (γ → γ → Prop)) := by
  constructor
  · intro h; rw [h]; exact self_mem_n₀r Z
  · rintro ⟨P, x, rfl, hZ⟩
    rw [nrAddOne_n₀r P x]; exact nr_eq_n₀r_of_mem hZ

/-- ✱181·53. \(\vdash :\dot{\exists} !P.x\neq y.\supset .(P\dot{\unicode{x21f8}} x)\dot{\unicode{x21f8}} y\,\text{smor}\,P+(x\downarrow y)\) -/
theorem pm181_53 {P : α → α → Prop} {x y : β} :
    rEx P ∧ x ≠ y → smor (addLastDot (addLastDot P x) y) (P +ᵣ (x ↓ y)) := fun ⟨hP, hxy⟩ =>
  smor_dot_dot hP x y hxy

/-- ✱181·54. \(\vdash :\nu \neq 0_{r}.\supset .(\mu \dot{+} \nu )\dot{+} \dot{1} =\mu \dot{+} (\nu \dot{+} \dot{1} )\)

The inner sum `μ +̇ ν` and the `ν +̇ 1̇` are arithmetical components, each in its own adequate type
(IIT); each `+̇ 1̇` has its own type of the apparent `x` (`β₁` outer, `β₂` inner).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components μ +̇ ν and ν +̇ 1̇ are adequate; PM assumes every type has a member
(Introduction, Ch. I): the type of the apparent `x` of the outer `+̇ 1̇` is `[Nonempty β₁]` -/
theorem pm181_54 {β₁ β₂ W₁ W₂ : Type*} [Nonempty β₁] {μ : Set (α → α → Prop)}
    {ν : Set (δ → δ → Prop)} (h₁ : AdeqNrAdd W₁ μ ν) (h₂ : AdeqNrAddOne W₂ β₂ ν) :
    ν ≠ zero_r → (nrAddOne β₁ (μ ∔ ν : Set (W₁ → W₁ → Prop)) : Set (γ → γ → Prop)) =
      μ ∔ (nrAddOne β₂ ν : Set (W₂ → W₂ → Prop)) := by
  intro hν0
  obtain ⟨b⟩ := h₂.nonempty
  obtain ⟨b₁⟩ := ‹Nonempty β₁›
  by_cases hμ : ∃ P, μ = n₀r P
  · obtain ⟨P, rfl⟩ := hμ
    by_cases hν : ∃ Q, ν = n₀r Q
    · obtain ⟨Q, rfl⟩ := hν
      have hQ : rEx Q := ne_rNull_iff.1 fun e => hν0 (by rw [e]; exact zero_r_eq_n₀r.symm)
      obtain ⟨X, hX, eX⟩ := h₁.eq_n₀r P Q
      obtain ⟨Y, hY, eY⟩ := h₂.eq_n₀r Q b
      rw [eX, eY, nrAddOne_n₀r X b₁, n₀r_nrAdd_n₀r]
      apply nr_eq_nr_of_smor
      exact smor_trans (smor_addLastDot hX b₁ b₁) (smor_trans (smor_addLastDot_rplus hQ b₁ b)
        (smor_rplus (smor_refl P) (smor_symm hY)))
    · push Not at hν
      rw [nrAdd_eq_empty_of_right _ hν, nrAddOne_empty_of (fun P h' => n₀r_ne_empty P h'.symm),
        nrAddOne_empty_of hν, nrAdd_empty]
  · push Not at hμ
    rw [nrAdd_eq_empty_of_left hμ, nrAddOne_empty_of (fun P h' => n₀r_ne_empty P h'.symm),
      nrAdd_eq_empty_of_left hμ]

/-- ✱181·55. \(\vdash :\mu \neq 0_{r}.\supset .\dot{1} \dot{+} (\mu \dot{+} \nu )=(\dot{1} \dot{+} \mu )\dot{+} \nu \quad[\text{Proof as in *181·54}]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components μ +̇ ν and 1̇ +̇ μ are adequate -/
theorem pm181_55 {W₁ W₂ : Type*} {μ : Set (α → α → Prop)} {ν : Set (δ → δ → Prop)}
    (h₁ : AdeqNrAdd W₁ μ ν) (h₂ : AdeqNrOneAdd W₂ β μ) :
    μ ≠ zero_r → (nrOneAdd β (μ ∔ ν : Set (W₁ → W₁ → Prop)) : Set (γ → γ → Prop)) =
      (nrOneAdd β μ : Set (W₂ → W₂ → Prop)) ∔ ν := by
  intro hμ0
  obtain ⟨b⟩ := h₂.nonempty
  by_cases hμ : ∃ P, μ = n₀r P
  · obtain ⟨P, rfl⟩ := hμ
    have hP : rEx P := ne_rNull_iff.1 fun e => hμ0 (by rw [e]; exact zero_r_eq_n₀r.symm)
    by_cases hν : ∃ Q, ν = n₀r Q
    · obtain ⟨Q, rfl⟩ := hν
      obtain ⟨X, hX, eX⟩ := h₁.eq_n₀r P Q
      obtain ⟨Y, hY, eY⟩ := h₂.eq_n₀r P b
      rw [eX, eY, nrOneAdd_n₀r X b, n₀r_nrAdd_n₀r]
      apply nr_eq_nr_of_smor
      exact smor_trans (smor_addFirstDot hX b b) (smor_trans (smor_addFirstDot_rplus hP b b)
        (smor_rplus (smor_symm hY) (smor_refl Q)))
    · push Not at hν
      rw [nrAdd_eq_empty_of_right _ hν, nrAdd_eq_empty_of_right _ hν,
        nrOneAdd_empty_of (fun P h' => n₀r_ne_empty P h'.symm)]
  · push Not at hμ
    rw [nrAdd_eq_empty_of_left hμ, nrOneAdd_empty_of hμ, empty_nrAdd,
      nrOneAdd_empty_of (fun P h' => n₀r_ne_empty P h'.symm)]

/-- ✱181·56. \(\vdash :\mu \neq 0_{r}.\supset .(\mu \dot{+} \dot{1} )\dot{+} \dot{1} =\mu \dot{+} (\dot{1} \dot{+} \dot{1} )=\mu \dot{+} 2_{r}\)

The inner `μ +̇ 1̇` and the `2_r` are arithmetical components with their own adequate types (IIT);
each `+̇ 1̇` has its own type of the apparent `x`, and the second link is the identity of the
readings of `μ +̇ (1̇ +̇ 1̇)` and `μ +̇ 2_r` (✱181·04).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the arithmetical
components μ +̇ 1̇ and 2_r are in adequate types; PM assumes every type has a member (Introduction,
Ch. I): the type of the apparent `x` of the outer `+̇ 1̇` is `[Nonempty β₂]` -/
theorem pm181_56 {β₁ β₂ W₁ W₂ : Type*} [Nonempty β₂] {μ : Set (α → α → Prop)}
    (h₁ : AdeqNrAddOne W₁ β₁ μ) (h₂ : (two_r : Set (W₂ → W₂ → Prop)).Nonempty) :
    μ ≠ zero_r → (nrAddOne β₂ (nrAddOne β₁ μ : Set (W₁ → W₁ → Prop)) : Set (γ → γ → Prop)) =
        μ ∔ (two_r : Set (W₂ → W₂ → Prop)) ∧
      (μ ∔ (two_r : Set (W₂ → W₂ → Prop)) : Set (γ → γ → Prop)) = μ ∔ (two_r : Set (W₂ → W₂ → Prop)) := by
  intro hμ0
  refine ⟨?_, rfl⟩
  obtain ⟨b₁⟩ := h₁.nonempty
  obtain ⟨b₂⟩ := ‹Nonempty β₂›
  obtain ⟨_, a, a', haa', -⟩ := h₂
  by_cases hμ : ∃ P, μ = n₀r P
  · obtain ⟨P, rfl⟩ := hμ
    have hP : rEx P := ne_rNull_iff.1 fun e => hμ0 (by rw [e]; exact zero_r_eq_n₀r.symm)
    obtain ⟨X, hX, eX⟩ := h₁.eq_n₀r P b₁
    rw [eX, nrAddOne_n₀r X b₂, nrAdd_of rfl (two_r_eq_n₀r haa')]
    exact nr_eq_nr_of_smor (smor_trans (smor_addLastDot hX b₂ b₂) (smor_dot_dot hP b₁ b₂ haa'))
  · push Not at hμ
    rw [nrAddOne_empty_of hμ, nrAddOne_empty_of (fun P h' => n₀r_ne_empty P h'.symm),
      nrAdd_eq_empty_of_left hμ]

/-- ✱181·57. \[\begin{align}&\vdash :\mu \neq 0_{r}.\supset .\dot{1} \dot{+} (\dot{1} \dot{+} \mu )=(\dot{1} \dot{+} \dot{1} )\dot{+} \mu =2_{r}\dot{+} \mu \\ &[\text{Proof as in *181·56}]\end{align}\]

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the arithmetical
components 1̇ +̇ μ and 2_r are in adequate types; PM assumes every type has a member (Introduction,
Ch. I): the type of the apparent `x` of the outer `1̇ +̇` is `[Nonempty β₂]` -/
theorem pm181_57 {β₁ β₂ W₁ W₂ : Type*} [Nonempty β₂] {μ : Set (α → α → Prop)}
    (h₁ : AdeqNrOneAdd W₁ β₁ μ) (h₂ : (two_r : Set (W₂ → W₂ → Prop)).Nonempty) :
    μ ≠ zero_r → (nrOneAdd β₂ (nrOneAdd β₁ μ : Set (W₁ → W₁ → Prop)) : Set (γ → γ → Prop)) =
        (two_r : Set (W₂ → W₂ → Prop)) ∔ μ ∧
      ((two_r : Set (W₂ → W₂ → Prop)) ∔ μ : Set (γ → γ → Prop)) = (two_r : Set (W₂ → W₂ → Prop)) ∔ μ := by
  intro hμ0
  refine ⟨?_, rfl⟩
  obtain ⟨b₁⟩ := h₁.nonempty
  obtain ⟨b₂⟩ := ‹Nonempty β₂›
  obtain ⟨_, a, a', haa', -⟩ := h₂
  by_cases hμ : ∃ P, μ = n₀r P
  · obtain ⟨P, rfl⟩ := hμ
    have hP : rEx P := ne_rNull_iff.1 fun e => hμ0 (by rw [e]; exact zero_r_eq_n₀r.symm)
    obtain ⟨X, hX, eX⟩ := h₁.eq_n₀r P b₁
    rw [eX, nrOneAdd_n₀r X b₂, nrAdd_of (two_r_eq_n₀r haa') rfl]
    exact nr_eq_nr_of_smor (smor_trans (smor_addFirstDot hX b₂ b₂) (smor_first_first hP b₁ b₂ haa'))
  · push Not at hμ
    rw [nrOneAdd_empty_of hμ, nrOneAdd_empty_of (fun P h' => n₀r_ne_empty P h'.symm),
      nrAdd_eq_empty_of_right _ hμ]

/-- ✱181·561 (Df). \(\mu \dot{+} \dot{1} \dot{+} \dot{1} =\mu \dot{+} (\dot{1} \dot{+} \dot{1} ) \quad\text{Df}\) -/
theorem pm181_561 {W : Type*} {μ : Set (α → α → Prop)} :
    (μ ∔ (two_r : Set (W → W → Prop)) : Set (γ → γ → Prop)) = μ ∔ (two_r : Set (W → W → Prop)) :=
  rfl

/-- ✱181·571 (Df). \(\dot{1} \dot{+} \dot{1} \dot{+} \mu =(\dot{1} \dot{+} \dot{1} )\dot{+} \mu \quad\text{Df}\) -/
theorem pm181_571 {W : Type*} {μ : Set (α → α → Prop)} :
    ((two_r : Set (W → W → Prop)) ∔ μ : Set (γ → γ → Prop)) = (two_r : Set (W → W → Prop)) ∔ μ :=
  rfl

/-- ✱181·58. \(\vdash :\mu \neq 0_{r}.\nu \neq 0_{r}.\supset .(\mu \dot{+} \dot{1} )\dot{+} \nu =\mu \dot{+} (\dot{1} \dot{+} \nu ) \quad[*161·232]\)

Each `+̇ 1̇` has its own type of the apparent `x` (`β₁`, `β₂`).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components μ +̇ 1̇ and 1̇ +̇ ν are adequate -/
theorem pm181_58 {β₁ β₂ W₁ W₂ : Type*} {μ : Set (α → α → Prop)} {ν : Set (δ → δ → Prop)}
    (h₁ : AdeqNrAddOne W₁ β₁ μ) (h₂ : AdeqNrOneAdd W₂ β₂ ν) :
    μ ≠ zero_r ∧ ν ≠ zero_r → ((nrAddOne β₁ μ : Set (W₁ → W₁ → Prop)) ∔ ν : Set (γ → γ → Prop)) =
      μ ∔ (nrOneAdd β₂ ν : Set (W₂ → W₂ → Prop)) := by
  rintro ⟨hμ0, hν0⟩
  obtain ⟨b⟩ := h₁.nonempty
  obtain ⟨b₂⟩ := h₂.nonempty
  by_cases hμ : ∃ P, μ = n₀r P
  · obtain ⟨P, rfl⟩ := hμ
    have hP : rEx P := ne_rNull_iff.1 fun e => hμ0 (by rw [e]; exact zero_r_eq_n₀r.symm)
    by_cases hν : ∃ Q, ν = n₀r Q
    · obtain ⟨Q, rfl⟩ := hν
      have hQ : rEx Q := ne_rNull_iff.1 fun e => hν0 (by rw [e]; exact zero_r_eq_n₀r.symm)
      obtain ⟨X, hX, eX⟩ := h₁.eq_n₀r P b
      obtain ⟨Y, hY, eY⟩ := h₂.eq_n₀r Q b₂
      rw [eX, eY, n₀r_nrAdd_n₀r, n₀r_nrAdd_n₀r]
      exact nr_eq_nr_of_smor (smor_trans (smor_rplus hX (smor_refl Q)) (smor_trans
        (smor_dot_rplus_dot hP hQ b b₂) (smor_rplus (smor_refl P) (smor_symm hY))))
    · push Not at hν
      rw [nrAdd_eq_empty_of_right _ hν, nrOneAdd_empty_of hν, nrAdd_empty]
  · push Not at hμ
    rw [nrAddOne_empty_of hμ, empty_nrAdd, nrAdd_eq_empty_of_left hμ]

/-- ✱181·59. \(\vdash :\mu \neq 0_{r}.\nu \neq 0_{r}.\supset .(\mu \dot{+} \dot{1} )\dot{+} (\dot{1} \dot{+} \nu )=\mu \dot{+} 2_{r}\dot{+} \nu \quad[*161·25]\)

The right-hand side is `(μ +̇ 2_r) +̇ ν` (✱180·561, ✱181·561); each inner sum and `2_r` has its own
adequate type, and each `+̇ 1̇` its own type of the apparent `x`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components are adequate -/
theorem pm181_59 {β₁ β₂ W₁ W₂ W₃ W₄ : Type*} {μ : Set (α → α → Prop)} {ν : Set (δ → δ → Prop)}
    (h₁ : AdeqNrAddOne W₁ β₁ μ) (h₂ : AdeqNrOneAdd W₂ β₂ ν)
    (h₃ : (two_r : Set (W₃ → W₃ → Prop)).Nonempty)
    (h₄ : AdeqNrAdd W₄ μ (two_r : Set (W₃ → W₃ → Prop))) :
    μ ≠ zero_r ∧ ν ≠ zero_r →
      ((nrAddOne β₁ μ : Set (W₁ → W₁ → Prop)) ∔ (nrOneAdd β₂ ν : Set (W₂ → W₂ → Prop)) :
        Set (γ → γ → Prop)) = ((μ ∔ (two_r : Set (W₃ → W₃ → Prop)) : Set (W₄ → W₄ → Prop)) ∔ ν) := by
  rintro ⟨hμ0, hν0⟩
  obtain ⟨b₁⟩ := h₁.nonempty
  obtain ⟨b₂⟩ := h₂.nonempty
  obtain ⟨_, a, a', haa', -⟩ := h₃
  by_cases hμ : ∃ P, μ = n₀r P
  · obtain ⟨P, rfl⟩ := hμ
    have hP : rEx P := ne_rNull_iff.1 fun e => hμ0 (by rw [e]; exact zero_r_eq_n₀r.symm)
    by_cases hν : ∃ Q, ν = n₀r Q
    · obtain ⟨Q, rfl⟩ := hν
      have hQ : rEx Q := ne_rNull_iff.1 fun e => hν0 (by rw [e]; exact zero_r_eq_n₀r.symm)
      obtain ⟨X, hX, eX⟩ := h₁.eq_n₀r P b₁
      obtain ⟨Y, hY, eY⟩ := h₂.eq_n₀r Q b₂
      rw [two_r_eq_n₀r haa'] at h₄ ⊢
      obtain ⟨Z, hZ, eZ⟩ := h₄.eq_n₀r P (a ↓ a')
      rw [eX, eY, eZ, n₀r_nrAdd_n₀r, n₀r_nrAdd_n₀r]
      exact nr_eq_nr_of_smor (smor_trans (smor_rplus hX hY) (smor_trans
        (smor_dot_rplus_dot2 hP hQ b₁ b₂ haa') (smor_rplus (smor_symm hZ) (smor_refl Q))))
    · push Not at hν
      rw [nrOneAdd_empty_of hν, nrAdd_empty, nrAdd_eq_empty_of_right _ hν]
  · push Not at hμ
    rw [nrAddOne_empty_of hμ, empty_nrAdd, nrAdd_eq_empty_of_left hμ, empty_nrAdd]

/-- ✱181·6. \(\vdash :\dot{\exists} !P.\supset .Cʻʻ\text{Nr}ʻ(P\dot{\unicode{x21f8}} x)= \text{Nc}ʻCʻP+_{c}1\)

`Nc'C'P` (an argument of `+_c`) is `n₀c (fld P)` (✱110·03); the cardinal `1` has its own type
`W`, adequate (`[Nonempty W]`, IIT); the equation is in the type of `Nr'(P ⇸̇ x)`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the type of the
arithmetical component 1 is adequate -/
theorem pm181_6 {W : Type*} [Nonempty W] {P : α → α → Prop} {x : β} :
    rEx P → C ʻʻ nr γ (addLastDot P x) = (n₀c (fld P) +ᶜ (one : Set (Set W)) : Set (Set γ)) :=
  fun hP => C_img_nr_addLastDot hP x

/-- ✱181·61. \[\begin{align}&\vdash :\dot{\exists} !P.\supset .Cʻʻ\text{Nr}ʻ(x\dot{\unicode{x21f7}} P)=1+_{c}\text{Nc}ʻCʻP= \text{Nc}ʻCʻP+_{c}1\\ &[\text{Proof as in *181·6}]\end{align}\]

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the types of the
arithmetical components 1 are adequate -/
theorem pm181_61 {W₁ W₂ : Type*} [Nonempty W₁] [Nonempty W₂] {P : α → α → Prop} {x : β} :
    rEx P → C ʻʻ nr γ (addFirstDot x P) = ((one : Set (Set W₁)) +ᶜ n₀c (fld P) : Set (Set γ)) ∧
      ((one : Set (Set W₁)) +ᶜ n₀c (fld P) : Set (Set γ)) = n₀c (fld P) +ᶜ (one : Set (Set W₂)) := by
  intro hP
  refine ⟨C_img_nr_addFirstDot hP x, ?_⟩
  obtain ⟨w₁⟩ := ‹Nonempty W₁›
  obtain ⟨w₂⟩ := ‹Nonempty W₂›
  rw [one_eq_n₀c_singleton w₁, one_eq_n₀c_singleton w₂, n₀c_cardAdd_n₀c, n₀c_cardAdd_n₀c]
  apply nc_eq_nc_of_sm
  obtain ⟨e⟩ := sm_iff_nonempty_equiv.1 (sm_singleton (a := w₁) (b := w₂))
  exact sm_iff_nonempty_equiv.2 ⟨(clsSumEquiv _ _).trans ((Equiv.sumComm _ _).trans
    (((Equiv.refl _).sumCongr e).trans (clsSumEquiv _ _).symm))⟩

/-- ✱181·62. \(\vdash :\mu \in \text{NR}-\iota ʻ0_{r}.\supset .Cʻʻ(\mu \dot{+} \dot{1} )=Cʻʻ(\dot{1} \dot{+} \mu )=Cʻ\mu +_{c}1\)

**Status.** proved (reading): transcription error: the e-text prints `C'μ +_c 1` for
`C''μ +_c 1`; convention IIT for the cardinal `1` (`[Nonempty W]`); PM assumes every type has a
member (Introduction, Ch. I): the type of the apparent `x` of `μ +̇ 1̇` is `[Nonempty β]` -/
theorem pm181_62 {β' W : Type*} [Nonempty β] [Nonempty W] {μ : Set (α → α → Prop)} :
    μ ∈ NR β' \ ι zero_r → C ʻʻ (nrAddOne β μ : Set (γ → γ → Prop)) =
        C ʻʻ (nrOneAdd β μ : Set (γ → γ → Prop)) ∧
      C ʻʻ (nrOneAdd β μ : Set (γ → γ → Prop)) = (C ʻʻ μ +ᶜ (one : Set (Set W)) : Set (Set γ)) := by
  rintro ⟨hμ, hμ0⟩
  obtain ⟨b⟩ := ‹Nonempty β›
  rcases NR_cases hμ with rfl | ⟨P, rfl⟩
  · rw [nrAddOne_empty_of (fun P h' => n₀r_ne_empty P h'.symm),
      nrOneAdd_empty_of (fun P h' => n₀r_ne_empty P h'.symm)]
    simp only [img_empty, true_and]
    exact (cardAdd_eq_empty_of_left (fun A h => n₀c_ne_empty A h.symm) _).symm
  · have hP : rEx P := ne_rNull_iff.1 fun e => hμ0 (by rw [e, ← zero_r_eq_n₀r]; rfl)
    rw [nrAddOne_n₀r P b, nrOneAdd_n₀r P b, C_img_nr_addLastDot (W := W) hP,
      C_img_nr_addFirstDot (W := W) hP, n₀r_eq_nr, C_img_nr, ← n₀c_eq_nc]
    obtain ⟨w⟩ := ‹Nonempty W›
    rw [one_eq_n₀c_singleton w, n₀c_cardAdd_n₀c, n₀c_cardAdd_n₀c]
    have e : nc γ (fld P +ₐ ({w} : Set W)) = nc γ (({w} : Set W) +ₐ fld P) :=
      nc_eq_nc_of_sm (sm_iff_nonempty_equiv.2 ⟨(clsSumEquiv _ _).trans ((Equiv.sumComm _ _).trans
        (clsSumEquiv _ _).symm)⟩)
    exact ⟨e, e.symm⟩


section Helpers182

private theorem graph_id_semi (P : α → α → Prop) : graph (fun x : α => x) ⁏ P = P := by
  funext x y; apply propext
  rw [semi_graph_apply]
  exact ⟨fun ⟨z, w, ⟨hx, hy⟩, h⟩ => hx ▸ hy ▸ h, fun h => ⟨x, y, ⟨rfl, rfl⟩, h⟩⟩

private theorem dpar_eq_graph (R : α → β → Prop) (S : γ → δ → Prop) :
    R ∥ S = graph (fun Q => R ⨾ (Q ⨾ S)) := by
  funext P Q; apply propext; exact dpar_iff R S P Q

private theorem daggerRel_eq_graph (S : α → β → Prop) :
    daggerRel S = graph (fun Q => S ⁏ Q) := rfl

private theorem sep_apply {Q : α → α → Prop} {S T : α → (α → α → Prop) → Prop} :
    opSemi couple Q Q S T ↔ ∃ x y, (S = x ↓ Q ∧ T = y ↓ Q) ∧ Q x y :=
  opSemi_couple_apply Q Q S T

private theorem mem_fld_sep {Q : α → α → Prop} {S : α → (α → α → Prop) → Prop} :
    S ∈ fld (opSemi couple Q Q) ↔ ∃ x, x ∈ fld Q ∧ S = x ↓ Q := by
  rw [fld_opSemi_couple]; rfl

private theorem sepRel_eq (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    sepRel P = graph (fun Q => opSemi couple Q Q) ⁏ P := rfl

private theorem sepRel_apply' {P : (α → α → Prop) → (α → α → Prop) → Prop} {X Y} :
    sepRel P X Y ↔ ∃ Q R, (X = opSemi couple Q Q ∧ Y = opSemi couple R R) ∧ P Q R :=
  semi_graph_apply _ _ _ _

private theorem mem_fld_sepRel {P : (α → α → Prop) → (α → α → Prop) → Prop} {Y} :
    Y ∈ fld (sepRel P) ↔ ∃ Q, Q ∈ fld P ∧ Y = opSemi couple Q Q :=
  mem_fld_graph_semi

private theorem couple_eq_iff {x x' : α} {y y' : β} : x ↓ y = x' ↓ y' ↔ x = x' ∧ y = y' :=
  couple_eq_couple_iff

private theorem sep_inj {Q R : α → α → Prop} (h : opSemi couple Q Q = opSemi couple R R) :
    Q = R := by
  by_cases hQ : rEx Q
  · obtain ⟨x, y, hxy⟩ := hQ
    have : opSemi couple R R (x ↓ Q) (y ↓ Q) := by rw [← h]; exact sep_apply.2 ⟨x, y, ⟨rfl, rfl⟩, hxy⟩
    obtain ⟨u, v, ⟨h1, -⟩, -⟩ := sep_apply.1 this
    exact (couple_eq_iff.1 h1).2
  by_cases hR : rEx R
  · obtain ⟨x, y, hxy⟩ := hR
    have : opSemi couple Q Q (x ↓ R) (y ↓ R) := by rw [h]; exact sep_apply.2 ⟨x, y, ⟨rfl, rfl⟩, hxy⟩
    obtain ⟨u, v, ⟨h1, -⟩, -⟩ := sep_apply.1 this
    exact (couple_eq_iff.1 h1).2.symm
  have h1 : Q = rNull := by by_contra h'; exact hQ (ne_rNull_iff.1 h')
  have h2 : R = rNull := by by_contra h'; exact hR (ne_rNull_iff.1 h')
  rw [h1, h2]

private theorem fld_relSigma' {P : (α → α → Prop) → (α → α → Prop) → Prop} {x : α} :
    x ∈ fld (relSigma P) ↔ ∃ Q, Q ∈ fld P ∧ x ∈ fld Q := by
  constructor
  · rintro ⟨y, h | h⟩ <;> rcases (relSigma_apply P _ _).1 h with ⟨Q, hQ, hq⟩ | ⟨Q, R, ⟨h1, h2⟩, hQR⟩
    · exact ⟨Q, hQ, y, Or.inl hq⟩
    · exact ⟨Q, ⟨R, Or.inl hQR⟩, h1⟩
    · exact ⟨Q, hQ, y, Or.inr hq⟩
    · exact ⟨R, ⟨Q, Or.inr hQR⟩, h2⟩
  · rintro ⟨Q, hQ, y, h | h⟩
    · exact ⟨y, Or.inl ((relSigma_apply P _ _).2 (Or.inl ⟨Q, hQ, h⟩))⟩
    · exact ⟨y, Or.inr ((relSigma_apply P _ _).2 (Or.inl ⟨Q, hQ, h⟩))⟩

private theorem mem_fld_sigma_sep {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {S : α → (α → α → Prop) → Prop} :
    S ∈ fld (relSigma (sepRel P)) ↔ ∃ Q x, (Q ∈ fld P ∧ x ∈ fld Q) ∧ S = x ↓ Q := by
  rw [fld_relSigma']
  constructor
  · rintro ⟨Y, hY, hS⟩
    obtain ⟨Q, hQ, rfl⟩ := mem_fld_sepRel.1 hY
    obtain ⟨x, hx, rfl⟩ := mem_fld_sep.1 hS
    exact ⟨Q, x, ⟨hQ, hx⟩, rfl⟩
  · rintro ⟨Q, x, ⟨hQ, hx⟩, rfl⟩
    exact ⟨_, mem_fld_sepRel.2 ⟨Q, hQ, rfl⟩, mem_fld_sep.2 ⟨x, hx, rfl⟩⟩

/-! #### Selections and `Π'P` -/

private theorem mem_selF {L : Set (α → α → Prop)} {M : α → (α → α → Prop) → Prop} :
    M ∈ sel F L ↔ ((∀ x y Q, M x Q → M y Q → x = y) ∧ (∀ x Q, M x Q → x ∈ fld Q)) ∧
      ∀ Q, Q ∈ L ↔ ∃ x, M x Q := by
  rw [mem_sel_iff, mem_arrow_one_Cls]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨fun x y Q hx hy => h1 x y Q ⟨hx, hy⟩, fun x Q h => h2 x Q h⟩,
      fun Q => by rw [← h3]; rfl⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨fun x y Q h => h1 x y Q h.1 h.2, fun x Q h => h2 x Q h⟩,
      Set.ext fun Q => (h3 Q).symm⟩

private theorem desc_of_mem {M : α → β → Prop} {y : β} {x : α} (hx : M x y)
    (hu : ∀ u, M u y → u = x) {ψ : α → Prop} : Desc M y ψ ↔ ψ x :=
  TheIs_iff_of_unique fun u => ⟨hu u, fun e => e ▸ hx⟩

private theorem relPi_iff {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M N : α → (α → α → Prop) → Prop} :
    relPi P M N ↔ (M ∈ sel F (fld P) ∧ N ∈ sel F (fld P)) ∧
      ∃ Q, (∃ x y, (M x Q ∧ N y Q) ∧ Q x y) ∧
        ∀ R, P R Q ∧ R ≠ Q → ∀ x y, M x R → N y R → x = y := by
  constructor
  · rintro ⟨⟨hM, hN⟩, Q, ⟨b, hb, c, hc, hq⟩, h2⟩
    refine ⟨⟨hM, hN⟩, Q, ⟨b, c, ⟨(hb b).2 rfl, (hc c).2 rfl⟩, hq⟩, fun R hR x y hx hy => ?_⟩
    obtain ⟨b', hb', c', hc', e⟩ := h2 R hR
    rw [(hb' x).1 hx, (hc' y).1 hy]; exact e
  · rintro ⟨⟨hM, hN⟩, Q, ⟨x, y, ⟨hx, hy⟩, hq⟩, h2⟩
    have hM' := mem_selF.1 hM
    have hN' := mem_selF.1 hN
    refine ⟨⟨hM, hN⟩, Q, ?_, fun R hR => ?_⟩
    · exact (desc_of_mem hx fun u hu => hM'.1.1 u x Q hu hx).2
        ((desc_of_mem hy fun u hu => hN'.1.1 u y Q hu hy).2 hq)
    · have hRf : R ∈ fld P := ⟨Q, Or.inl hR.1⟩
      obtain ⟨x', hx'⟩ := (hM'.2 R).1 hRf
      obtain ⟨y', hy'⟩ := (hN'.2 R).1 hRf
      exact (desc_of_mem hx' fun u hu => hM'.1.1 u x' R hu hx').2
        ((desc_of_mem hy' fun u hu => hN'.1.1 u y' R hu hy').2 (h2 R hR x' y' hx' hy'))

private theorem mem_fld_relPi {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M : α → (α → α → Prop) → Prop} (h : M ∈ fld (relPi P)) : M ∈ sel F (fld P) := by
  rcases h with ⟨N, h | h⟩
  · exact h.1.1
  · exact h.1.2

private theorem relPi_congr {P P' : (α → α → Prop) → (α → α → Prop) → Prop}
    (hf : fld P = fld P') (h : ∀ R Q, R ≠ Q → (P R Q ↔ P' R Q)) : relPi P = relPi P' := by
  funext M N; apply propext
  simp only [relPi_iff, hf]
  constructor
  · rintro ⟨hs, Q, h1, h2⟩
    exact ⟨hs, Q, h1, fun R hR => h2 R ⟨(h R Q hR.2).2 hR.1, hR.2⟩⟩
  · rintro ⟨hs, Q, h1, h2⟩
    exact ⟨hs, Q, h1, fun R hR => h2 R ⟨(h R Q hR.2).1 hR.1, hR.2⟩⟩

private theorem sel_single {Q : α → α → Prop} {M : α → (α → α → Prop) → Prop} :
    M ∈ sel F ({Q} : Set (α → α → Prop)) ↔ ∃ x, x ∈ fld Q ∧ M = x ↓ Q := by
  rw [mem_selF]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨x, hx⟩ := (h3 Q).1 rfl
    refine ⟨x, h2 x Q hx, ?_⟩
    funext u R; apply propext
    constructor
    · intro hu
      have hR : R = Q := (h3 R).2 ⟨u, hu⟩
      subst hR
      exact ⟨h1 u x R hu hx, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨fun u v R hu hv => hu.1.trans hv.1.symm, fun u R h => ?_⟩, fun R => ?_⟩
    · rw [h.1, h.2]; exact hx
    · exact ⟨fun h => ⟨x, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩

private theorem fld_couple_self (Q : α) : fld (Q ↓ Q) = {Q} := by
  rw [fld_couple, Set.pair_eq_singleton]

/-- `Π'(Q ↓ Q) = ↓Q;Q` (✱172·2). -/
private theorem relPi_couple_self (Q : α → α → Prop) : relPi (Q ↓ Q) = opSemi couple Q Q := by
  funext M N; apply propext
  rw [relPi_iff, sep_apply, fld_couple_self, sel_single, sel_single]
  constructor
  · rintro ⟨⟨⟨x, -, rfl⟩, ⟨y, -, rfl⟩⟩, Q', ⟨x', y', ⟨⟨hx, hQ⟩, ⟨hy, -⟩⟩, hq⟩, -⟩
    subst hx hy hQ
    exact ⟨x', y', ⟨rfl, rfl⟩, hq⟩
  · rintro ⟨x, y, ⟨rfl, rfl⟩, hq⟩
    refine ⟨⟨⟨x, ⟨y, Or.inl hq⟩, rfl⟩, ⟨y, ⟨x, Or.inr hq⟩, rfl⟩⟩, Q,
      ⟨x, y, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, hq⟩, ?_⟩
    rintro R ⟨⟨hR, -⟩, hne⟩
    exact absurd hR hne

end Helpers182

section Helpers182b

/-- From a selection `M` from `C'P` to the corresponding selection from `C'↓̆.,;P`. -/
private def liftSel (M : α → (α → α → Prop) → Prop) :
    (α → (α → α → Prop) → Prop) →
      ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) → Prop :=
  fun c Y => ∃ Q x, (Y = opSemi couple Q Q ∧ c = x ↓ Q) ∧ M x Q

private theorem g_lift (M : α → (α → α → Prop) → Prop) : sumRel (dom (liftSel M)) = M := by
  funext x Q; apply propext
  constructor
  · rintro ⟨c, ⟨Y, Q', x', ⟨-, rfl⟩, hM⟩, hc⟩
    obtain ⟨rfl, rfl⟩ := hc
    exact hM
  · intro h
    exact ⟨x ↓ Q, ⟨_, Q, x, ⟨rfl, rfl⟩, h⟩, rfl, rfl⟩

private theorem lift_sel {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M : α → (α → α → Prop) → Prop} (hM : M ∈ sel F (fld P)) :
    liftSel M ∈ sel F (fld (sepRel P)) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_selF.1 hM
  refine mem_selF.2 ⟨⟨?_, ?_⟩, ?_⟩
  · rintro c d Y ⟨Q, x, ⟨rfl, rfl⟩, hx⟩ ⟨Q', y, ⟨e, rfl⟩, hy⟩
    have := sep_inj e; subst this
    rw [h1 x y Q hx hy]
  · rintro c Y ⟨Q, x, ⟨rfl, rfl⟩, hx⟩
    exact mem_fld_sep.2 ⟨x, h2 x Q hx, rfl⟩
  · intro Y
    rw [mem_fld_sepRel]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      obtain ⟨x, hx⟩ := (h3 Q).1 hQ
      exact ⟨x ↓ Q, Q, x, ⟨rfl, rfl⟩, hx⟩
    · rintro ⟨c, Q, x, ⟨rfl, rfl⟩, hx⟩; exact ⟨Q, (h3 Q).2 ⟨x, hx⟩, rfl⟩

private theorem g_eq {P : (α → α → Prop) → (α → α → Prop) → Prop} {M'}
    (hM' : M' ∈ sel F (fld (sepRel P))) {x : α} {Q : α → α → Prop} :
    sumRel (dom M') x Q ↔ M' (x ↓ Q) (opSemi couple Q Q) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_selF.1 hM'
  constructor
  · rintro ⟨c, ⟨Y, hcY⟩, hc⟩
    obtain ⟨R, -, rfl⟩ := mem_fld_sepRel.1 ((h3 Y).2 ⟨c, hcY⟩)
    obtain ⟨u, -, rfl⟩ := mem_fld_sep.1 (h2 c _ hcY)
    obtain ⟨rfl, rfl⟩ := hc
    exact hcY
  · intro h; exact ⟨x ↓ Q, ⟨_, h⟩, rfl, rfl⟩

private theorem lift_g {P : (α → α → Prop) → (α → α → Prop) → Prop} {M'}
    (hM' : M' ∈ sel F (fld (sepRel P))) : liftSel (sumRel (dom M')) = M' := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_selF.1 hM'
  funext c Y; apply propext
  constructor
  · rintro ⟨Q, x, ⟨rfl, rfl⟩, h⟩; exact (g_eq hM').1 h
  · intro h
    obtain ⟨Q, -, rfl⟩ := mem_fld_sepRel.1 ((h3 Y).2 ⟨c, h⟩)
    obtain ⟨x, -, rfl⟩ := mem_fld_sep.1 (h2 c _ h)
    exact ⟨Q, x, ⟨rfl, rfl⟩, (g_eq hM').2 h⟩

private theorem g_sel {P : (α → α → Prop) → (α → α → Prop) → Prop} {M'}
    (hM' : M' ∈ sel F (fld (sepRel P))) : sumRel (dom M') ∈ sel F (fld P) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_selF.1 hM'
  refine mem_selF.2 ⟨⟨fun x y Q hx hy => ?_, fun x Q hx => ?_⟩, fun Q => ?_⟩
  · exact (couple_eq_iff.1 (h1 _ _ _ ((g_eq hM').1 hx) ((g_eq hM').1 hy))).1
  · obtain ⟨u, hu, e⟩ := mem_fld_sep.1 (h2 _ _ ((g_eq hM').1 hx))
    rw [(couple_eq_iff.1 e).1]; exact hu
  · constructor
    · intro hQ
      obtain ⟨c, hc⟩ := (h3 _).1 (mem_fld_sepRel.2 ⟨Q, hQ, rfl⟩)
      obtain ⟨x, -, rfl⟩ := mem_fld_sep.1 (h2 _ _ hc)
      exact ⟨x, (g_eq hM').2 hc⟩
    · rintro ⟨x, hx⟩
      obtain ⟨R, hR, e⟩ := mem_fld_sepRel.1 ((h3 _).2 ⟨_, (g_eq hM').1 hx⟩)
      rw [sep_inj e]; exact hR

private theorem relPi_lift {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M N : α → (α → α → Prop) → Prop} (hM : M ∈ sel F (fld P)) (hN : N ∈ sel F (fld P)) :
    relPi P M N ↔ relPi (sepRel P) (liftSel M) (liftSel N) := by
  rw [relPi_iff, relPi_iff]
  simp only [hM, hN, lift_sel hM, lift_sel hN, true_and]
  constructor
  · rintro ⟨Q, ⟨x, y, ⟨hx, hy⟩, hq⟩, h2⟩
    refine ⟨opSemi couple Q Q, ⟨x ↓ Q, y ↓ Q, ⟨⟨Q, x, ⟨rfl, rfl⟩, hx⟩, ⟨Q, y, ⟨rfl, rfl⟩, hy⟩⟩,
      sep_apply.2 ⟨x, y, ⟨rfl, rfl⟩, hq⟩⟩, ?_⟩
    rintro R' ⟨hR', hne⟩ c d ⟨R, u, ⟨rfl, rfl⟩, hu⟩ ⟨R₂, v, ⟨e, rfl⟩, hv⟩
    have := sep_inj e; subst this
    obtain ⟨R₃, Q₃, ⟨e1, e2⟩, hPR⟩ := sepRel_apply'.1 hR'
    have h1 := sep_inj e1; have h2' := sep_inj e2; subst h1 h2'
    rw [h2 R ⟨hPR, fun e => hne (by rw [e])⟩ u v hu hv]
  · rintro ⟨Y, ⟨c, d, ⟨⟨Q, x, ⟨rfl, rfl⟩, hx⟩, ⟨Q', y, ⟨e, rfl⟩, hy⟩⟩, hcd⟩, h2⟩
    have := sep_inj e; subst this
    obtain ⟨u, v, ⟨e1, e2⟩, huv⟩ := sep_apply.1 hcd
    have ex := (couple_eq_iff.1 e1).1
    have ey := (couple_eq_iff.1 e2).1
    refine ⟨Q, ⟨x, y, ⟨hx, hy⟩, by rw [ex, ey]; exact huv⟩, fun R hR a b ha hb => ?_⟩
    have := h2 (opSemi couple R R) ⟨sepRel_apply'.2 ⟨R, Q, ⟨rfl, rfl⟩, hR.1⟩,
      fun e => hR.2 (sep_inj e)⟩ (a ↓ R) (b ↓ R) ⟨R, a, ⟨rfl, rfl⟩, ha⟩ ⟨R, b, ⟨rfl, rfl⟩, hb⟩
    exact (couple_eq_iff.1 this).1

/-- `Π'P = ṡ;D;Π'↓̆.,;P` (✱182·42). -/
private theorem relPi_eq_sdot (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    relPi P = graph (fun M' => sumRel (dom M')) ⁏ relPi (sepRel P) := by
  funext M N; apply propext
  rw [semi_graph_apply]
  constructor
  · intro h
    obtain ⟨⟨hM, hN⟩, -⟩ := relPi_iff.1 h
    exact ⟨liftSel M, liftSel N, ⟨(g_lift M).symm, (g_lift N).symm⟩, (relPi_lift hM hN).1 h⟩
  · rintro ⟨M', N', ⟨rfl, rfl⟩, h⟩
    obtain ⟨⟨hM', hN'⟩, -⟩ := relPi_iff.1 h
    exact (relPi_lift (g_sel hM') (g_sel hN')).2 (by rw [lift_g hM', lift_g hN']; exact h)

private theorem sDot_D (α' β' : Type*) :
    (sDotRel ⨾ D : (α → α' → Prop) → ((α → α' → Prop) → β' → Prop) → Prop) =
      graph (fun M' => sumRel (dom M')) :=
  graph_relProd_graph _ _

/-- A correlator `graph f ↾ C'Q` with `f` injective on `C'Q`. -/
private theorem graph_cres_smorbar {f : β → α} {Q : β → β → Prop}
    (hf : ∀ z w, z ∈ fld Q → w ∈ fld Q → f z = f w → z = w) :
    graph f ↾ fld Q ∈ smorbar (graph f ⁏ Q) Q := by
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨hx, -⟩, ⟨hy, -⟩⟩; exact (hx : x = f z).trans (hy : y = f z).symm
  · rintro x y z ⟨⟨hy, hyQ⟩, ⟨hz, hzQ⟩⟩; exact hf y z hyQ hzQ ((hy : x = f y).symm.trans hz)
  · ext z; exact ⟨fun h => ⟨f z, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  · exact semi_congr fun x z hz => ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩

/-- `Σ'(T†;Q) = T;Σ'Q` when every member of the fields of the members of `C'Q` has a
`T`-referent (✱162·35). -/
private theorem relSigma_dagger {T : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    (hc : ∀ S, S ∈ fld Q → ∀ z, z ∈ fld S → ∃ x, T x z) :
    relSigma (daggerRel T ⁏ Q) = T ⁏ relSigma Q := by
  funext u v; apply propext
  rw [relSigma_apply, semi_apply]
  have hfT : ∀ S, S ∈ fld Q → ∀ x, x ∈ fld (T ⁏ S) ↔ ∃ z, z ∈ fld S ∧ T x z :=
    fun S hS x => mem_fld_semi (hc S hS)
  constructor
  · rintro (⟨X, hX, hXuv⟩ | ⟨X, Y, ⟨hu, hv⟩, hXY⟩)
    · obtain ⟨S, hS, rfl⟩ := mem_fld_graph_semi.1 hX
      obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := (semi_apply _ _ _ _).1 hXuv
      exact ⟨a, b, ⟨ha, hb⟩, (relSigma_apply Q a b).2 (Or.inl ⟨S, hS, hab⟩)⟩
    · obtain ⟨S, S', ⟨rfl, rfl⟩, hSS'⟩ := (semi_graph_apply _ _ _ _).1 hXY
      obtain ⟨a, ha, hua⟩ := (hfT S ⟨S', Or.inl hSS'⟩ u).1 hu
      obtain ⟨b, hb, hvb⟩ := (hfT S' ⟨S, Or.inr hSS'⟩ v).1 hv
      exact ⟨a, b, ⟨hua, hvb⟩, (relSigma_apply Q a b).2 (Or.inr ⟨S, S', ⟨ha, hb⟩, hSS'⟩)⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, hab⟩
    rcases (relSigma_apply Q a b).1 hab with ⟨S, hS, hS'⟩ | ⟨S, S', ⟨h1, h2⟩, hSS'⟩
    · exact Or.inl ⟨T ⁏ S, mem_fld_graph_semi.2 ⟨S, hS, rfl⟩,
        (semi_apply _ _ _ _).2 ⟨a, b, ⟨ha, hb⟩, hS'⟩⟩
    · exact Or.inr ⟨T ⁏ S, T ⁏ S', ⟨(hfT S ⟨S', Or.inl hSS'⟩ u).2 ⟨a, h1, ha⟩,
        (hfT S' ⟨S, Or.inr hSS'⟩ v).2 ⟨b, h2, hb⟩⟩,
        (semi_graph_apply _ _ _ _).2 ⟨S, S', ⟨rfl, rfl⟩, hSS'⟩⟩

/-- Double likeness gives likeness of the sums (✱164·151). -/
private theorem smor_relSigma_of_smorsmor {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} (h : smorsmor P Q) :
    smor (relSigma P) (relSigma Q) := by
  obtain ⟨T, ⟨hT, hcod⟩, hP⟩ := h
  obtain ⟨a, b⟩ := mem_arrow_one_one.1 hT
  have hc : ∀ z, z ∈ fld (relSigma Q) → ∃ x, T x z := fun z hz => by
    have : z ∈ codom T := by rw [← (hcod : fld (relSigma Q) = codom T)]; exact hz
    exact this
  have hP' : P = daggerRel T ⁏ Q := hP
  rw [hP', relSigma_dagger fun S hS z hz => hc z (fld_relSigma'.2 ⟨S, hS, hz⟩)]
  exact smor_semi_of (fun x y z _ hx hy => a x y z ⟨hx, hy⟩)
    (fun x z w _ _ hz hw => b x z w ⟨hz, hw⟩) hc

/-! #### Double correlators and `↓̆.,` (✱182·3–·34) -/

private theorem dpar_couple {T : α → β → Prop} {y : β} {x : α} {S : β → β → Prop}
    (hx : T x y) (hu : ∀ u, T u y → u = x) :
    T ⨾ ((y ↓ S) ⨾ (daggerRel T)˘) = x ↓ (T ⁏ S) := by
  funext u W; apply propext
  constructor
  · rintro ⟨v, huv, R, ⟨rfl, rfl⟩, hW⟩
    exact ⟨hu u huv, hW⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨y, hx, S, ⟨rfl, rfl⟩, rfl⟩

private theorem pm182_aux_31 {T : α → β → Prop} {S : β → β → Prop} (h : EE T (fld S)) :
    opSemi couple (T ⁏ S) (T ⁏ S) = (T ∥ (daggerRel T)˘) ⁏ opSemi couple S S := by
  rw [dpar_eq_graph]
  show graph (fun x => x ↓ (T ⁏ S)) ⁏ (T ⁏ S) = graph _ ⁏ (graph (fun y => y ↓ S) ⁏ S)
  conv_rhs => rw [semi_semi, graph_relProd_graph]
  funext X Y; apply propext
  rw [semi_graph_apply, semi_graph_apply]
  constructor
  · rintro ⟨x, x', ⟨rfl, rfl⟩, hxx'⟩
    obtain ⟨y, y', ⟨hy, hy'⟩, hS⟩ := (semi_apply _ _ _ _).1 hxx'
    obtain ⟨b, hb⟩ := h y ⟨y', Or.inl hS⟩
    obtain ⟨b', hb'⟩ := h y' ⟨y, Or.inr hS⟩
    refine ⟨y, y', ⟨?_, ?_⟩, hS⟩
    · rw [dpar_couple hy fun u hu => ((hb u).1 hu).trans ((hb x).1 hy).symm]
    · rw [dpar_couple hy' fun u hu => ((hb' u).1 hu).trans ((hb' x').1 hy').symm]
  · rintro ⟨y, y', ⟨rfl, rfl⟩, hS⟩
    obtain ⟨b, hb⟩ := h y ⟨y', Or.inl hS⟩
    obtain ⟨b', hb'⟩ := h y' ⟨y, Or.inr hS⟩
    rw [dpar_couple ((hb b).2 rfl) fun u hu => (hb u).1 hu,
      dpar_couple ((hb' b').2 rfl) fun u hu => (hb' u).1 hu]
    exact ⟨b, b', ⟨rfl, rfl⟩, (semi_apply _ _ _ _).2 ⟨y, y', ⟨(hb b).2 rfl, (hb' b').2 rfl⟩, hS⟩⟩

private theorem pm182_aux_32 {T : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    (h : EE T (fld (relSigma Q))) :
    sepRel (daggerRel T ⁏ Q) = daggerRel (T ∥ (daggerRel T)˘) ⁏ sepRel Q := by
  rw [sepRel_eq, sepRel_eq, daggerRel_eq_graph, daggerRel_eq_graph, semi_semi, semi_semi,
    graph_relProd_graph, graph_relProd_graph]
  refine graph_semi_congr fun S hS => ?_
  exact pm182_aux_31 fun y hy => h y (fld_relSigma'.2 ⟨S, hS, hy⟩)

/-- The data of a double correlator restricted to `C'Σ'Q`. -/
private theorem smorsmorbar_data {T : α → β → Prop} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} (h : T ↾ fld (relSigma Q) ∈ smorsmorbar P Q) :
    (∀ x x' y, y ∈ fld (relSigma Q) → T x y → T x' y → x = x') ∧
    (∀ x y y', y ∈ fld (relSigma Q) → y' ∈ fld (relSigma Q) → T x y → T x y' → y = y') ∧
    (∀ y, y ∈ fld (relSigma Q) → ∃ x, T x y) ∧ P = daggerRel (T ↾ fld (relSigma Q)) ⁏ Q := by
  obtain ⟨⟨hT, hcod⟩, hP⟩ := h
  obtain ⟨a, b⟩ := mem_arrow_one_one.1 hT
  refine ⟨fun x x' y hy h1 h2 => a x x' y ⟨⟨h1, hy⟩, ⟨h2, hy⟩⟩,
    fun x y y' hy hy' h1 h2 => b x y y' ⟨⟨h1, hy⟩, ⟨h2, hy'⟩⟩, fun y hy => ?_, hP⟩
  have : y ∈ codom (T ↾ fld (relSigma Q)) := by
    rw [← (hcod : fld (relSigma Q) = codom _)]; exact hy
  obtain ⟨x, hx, -⟩ := this
  exact ⟨x, hx⟩

private theorem EE_of_data {T : α → β → Prop} {B : Set β}
    (h1 : ∀ x x' y, y ∈ B → T x y → T x' y → x = x') (h3 : ∀ y, y ∈ B → ∃ x, T x y)
    {A : Set β} (hA : A ⊆ B) : EE T A := fun y hy => by
  obtain ⟨x, hx⟩ := h3 y (hA hy)
  exact ⟨x, fun u => ⟨fun hu => h1 u x y (hA hy) hu hx, fun e => e ▸ hx⟩⟩

private theorem fld_sub_sigma {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : β → β → Prop}
    (hS : S ∈ fld Q) : fld S ⊆ fld (relSigma Q) := fun _ hy => fld_relSigma'.2 ⟨S, hS, hy⟩

private theorem fld_sep_sub {Q : (β → β → Prop) → (β → β → Prop) → Prop} {S : β → β → Prop}
    (hS : S ∈ fld Q) : fld (opSemi couple S S) ⊆ fld (relSigma (sepRel Q)) := fun Y hY => by
  obtain ⟨y, hy, rfl⟩ := mem_fld_sep.1 hY
  exact mem_fld_sigma_sep.2 ⟨S, y, ⟨hS, hy⟩, rfl⟩

end Helpers182b

section Helpers182c

private theorem dom_couple (x : α) (y : β) : dom (x ↓ y) = ι x := by
  ext u; exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨y, h, rfl⟩⟩

private theorem codom_couple (x : α) (y : β) : codom (x ↓ y) = ι y := by
  ext u; exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨x, rfl, h⟩⟩

private theorem D_sep (Q : α → α → Prop) : D ⁏ opSemi couple Q Q = iota ⁏ Q := by
  show graph dom ⁏ (graph (fun x => x ↓ Q) ⁏ Q) = graph (fun x => ι x) ⁏ Q
  rw [semi_semi, graph_relProd_graph]
  exact graph_semi_congr fun x _ => dom_couple x Q

private theorem iota_cnv_iota : (iota˘ ⨾ iota : α → α → Prop) = graph (fun y => y) := by
  funext x y; apply propext
  constructor
  · rintro ⟨A, hA, hA'⟩
    exact unitCls_injective ((hA : A = ι x).symm.trans (hA' : A = ι y))
  · rintro rfl; exact ⟨ι x, rfl, rfl⟩

private theorem iota_D_sep (Q : α → α → Prop) : iota˘ ⁏ D ⁏ opSemi couple Q Q = Q := by
  rw [D_sep, semi_semi, iota_cnv_iota, graph_id_semi]

private theorem downCls_F_eq (Q : α → α → Prop) : F ↧ Q = fld (opSemi couple Q Q) := by
  rw [fld_opSemi_couple]; rfl

private theorem downCls_F_inj {Q R : α → α → Prop} (h : F ↧ Q = F ↧ R) : Q = R := by
  rw [downCls_F_eq, downCls_F_eq] at h
  by_cases hQ : rEx Q
  · obtain ⟨x, y, hxy⟩ := hQ
    have : x ↓ Q ∈ fld (opSemi couple R R) := by
      rw [← h]; exact mem_fld_sep.2 ⟨x, ⟨y, Or.inl hxy⟩, rfl⟩
    obtain ⟨u, -, e⟩ := mem_fld_sep.1 this
    exact (couple_eq_iff.1 e).2
  by_cases hR : rEx R
  · obtain ⟨x, y, hxy⟩ := hR
    have : x ↓ R ∈ fld (opSemi couple Q Q) := by
      rw [h]; exact mem_fld_sep.2 ⟨x, ⟨y, Or.inl hxy⟩, rfl⟩
    obtain ⟨u, -, e⟩ := mem_fld_sep.1 this
    exact (couple_eq_iff.1 e).2.symm
  have h1 : Q = rNull := by by_contra h'; exact hQ (ne_rNull_iff.1 h')
  have h2 : R = rNull := by by_contra h'; exact hR (ne_rNull_iff.1 h')
  rw [h1, h2]

private theorem relPi_union_I (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    relPi (P ⊍ I ↾ fld P) = relPi P := by
  refine relPi_congr ?_ fun R Q hRQ => ⟨fun h => h.elim id fun h => absurd h.1 hRQ, Or.inl⟩
  ext Q
  constructor
  · rintro ⟨R, (h | ⟨rfl, h⟩) | (h | ⟨rfl, h⟩)⟩
    · exact ⟨R, Or.inl h⟩
    · exact h
    · exact ⟨R, Or.inr h⟩
    · exact h
  · rintro ⟨R, h | h⟩
    · exact ⟨R, Or.inl (Or.inl h)⟩
    · exact ⟨R, Or.inr (Or.inl h)⟩

private theorem sel_eq_of_dom {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : P ∈ Rel2excl)
    {M N : α → (α → α → Prop) → Prop} (hM : M ∈ sel F (fld P)) (hN : N ∈ sel F (fld P))
    (h : dom M = dom N) : M = N := by
  obtain ⟨⟨m1, m2⟩, m3⟩ := mem_selF.1 hM
  obtain ⟨⟨n1, n2⟩, n3⟩ := mem_selF.1 hN
  have key : ∀ {M N : α → (α → α → Prop) → Prop}, (∀ x Q, M x Q → x ∈ fld Q) →
      (∀ Q, Q ∈ fld P ↔ ∃ x, M x Q) → (∀ x Q, N x Q → x ∈ fld Q) →
      (∀ Q, Q ∈ fld P ↔ ∃ x, N x Q) → dom M = dom N → ∀ x Q, M x Q → N x Q := by
    intro M N m2 m3 n2 n3 h x Q hx
    have : x ∈ dom N := h ▸ ⟨Q, hx⟩
    obtain ⟨R, hR⟩ := this
    by_cases e : Q = R
    · rw [e]; exact hR
    · have := (mem_Rel2excl.1 hP) Q R ⟨⟨(m3 Q).2 ⟨x, hx⟩, (n3 R).2 ⟨x, hR⟩⟩, e⟩
      rw [inter_null_iff] at this
      exact absurd (n2 x R hR) (Set.disjoint_left.1 this (m2 x Q hx))
  funext x Q; apply propext
  exact ⟨key m2 m3 n2 n3 h x Q, key n2 n3 m2 m3 h.symm x Q⟩

/-- `P ∈ Rel² excl . ⊃ . Prod'P smor Π'P` (✱173·16). -/
private theorem smor_prodR_relPi {P : (α → α → Prop) → (α → α → Prop) → Prop}
    (hP : P ∈ Rel2excl) : smor (prodR P) (relPi P) :=
  smor_graph fun M N hM hN h => sel_eq_of_dom hP (mem_fld_relPi hM) (mem_fld_relPi hN) h

private theorem sm_of_inj_img {A : Set α} {S : Set δ} (f : α → δ)
    (hf : ∀ x y, x ∈ A → y ∈ A → f x = f y → x = y) (hS : ∀ z, z ∈ S ↔ ∃ x, x ∈ A ∧ z = f x) :
    sm S A := by
  refine sm_iff_nonempty_equiv.2 ⟨(Equiv.ofBijective (fun a : A => (⟨f a, (hS _).2 ⟨a, a.2, rfl⟩⟩ : S))
    ⟨fun a b h => Subtype.ext (hf a b a.2 b.2 (congrArg Subtype.val h)), fun s => ?_⟩).symm⟩
  obtain ⟨x, hx, e⟩ := (hS s).1 s.2
  exact ⟨⟨x, hx⟩, Subtype.ext e.symm⟩

private theorem couple_C (y : α) (Q : α → α → Prop) :
    (y ↓ Q) ⨾ C˘ = y ↓ fld Q := by
  funext u A; apply propext
  constructor
  · rintro ⟨R, ⟨rfl, rfl⟩, hA⟩; exact ⟨rfl, hA⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨Q, ⟨rfl, rfl⟩, rfl⟩

end Helpers182c

/-!
## [✱182] *182 on separated relations

*(Vol. 2, p. 487)*

> *Summary of* *182.
>
> …

**Lean reading.** `♀̆` is `opDiag f` for a double function `f : α → α → γ` (`graph` of `x ↦ x♀x`), so `♀̆'x` is
`f x x` (✱182·021 keeps the description); `↓̆`, `|̆`, `↑̆`, `↓̆,,`, `↓̆.,` are `opDiag couple`,
`opDiag relProd`, `opDiag cross`, `opDiag (opImg couple)`, `opDiag (opSemi couple)`, and the
separated relation `↓̆.,;P` is `sepRel P` (`↓̆.,'Q = ↓Q;Q` is `opSemi couple Q Q`). `F↧Q` is
`F ↧ Q` and the relation `F↧` is `opL downCls F`; `∈↧` is `opL downCls memRel`; `ṡ` is `sDotRel`;
`|C̆` is `relProdR C˘`; `T ‖ Cnv'T†` is `T ∥ (daggerRel T)˘`; `E!!T''C'S` is `EE T (fld S)`.
`P smor̄smor̄ Q`, `smor smor` are `smorsmorbar`, `smorsmor`; `κ sm̄sm̄ λ` is `smsmbar`. Values of
descriptive functions that always exist are written directly (Basic §5).

**Status.** proved (all propositions; ✱182·01 definition; ✱182·33 proved (reading), see its docstring)
-/

/-- ✱182·01 (Df). \(\breve{\unicode{x2640}}=\hat{y} \hat{x} (y=x\unicode{x2640}x) \quad\text{Df}\) -/
theorem pm182_01 {f : α → α → γ} : opDiag f = fun y x => y = f x x := rfl

/-- ✱182·02. \(\vdash :y\breve{\unicode{x2640}}x.\equiv .y=x\unicode{x2640}x \quad[(*182·01)]\) -/
theorem pm182_02 {f : α → α → γ} {y : γ} {x : α} : opDiag f y x ↔ y = f x x := Iff.rfl

/-- ✱182·021. \(\vdash .\breve{\unicode{x2640}}ʻx=x\unicode{x2640}x \quad[*182·02.*30·3]\) -/
theorem pm182_021 {f : α → α → γ} {x : α} : Desc (opDiag f) x (fun y => y = f x x) :=
  (desc_graph _ _ _).2 rfl

/-- ✱182·022. \(\vdash .\text{E}!\breve{\unicode{x2640}}ʻx \quad[*182·021.*14·21]\) -/
theorem pm182_022 {f : α → α → γ} {x : α} : EDesc (opDiag f) x := EDesc_graph _ _

/-- ✱182·023. \(\vdash :\breve{\unicode{x2640}}\in 1\rightarrow \text{Cls}:(\alpha ).\alpha \subset \text{ᗡ}ʻ\breve{\unicode{x2640}} \quad[*182·022.*71·166.*33·431]\) -/
theorem pm182_023 {f : α → α → γ} : opDiag f ∈ arrow one Cls ∧ ∀ A : Set α, A ⊆ codom (opDiag f) :=
  ⟨mem_arrow_one_Cls.2 fun x y z h => (h.1 : x = f z z).trans (h.2 : y = f z z).symm,
    fun _ x _ => ⟨f x x, rfl⟩⟩

/-- ✱182·03. \(\vdash .\breve{\mid}ʻR=R^{2} \quad[*182·021.(*34·02)]\) -/
theorem pm182_03 {R : α → α → Prop} :
    Desc (opDiag (relProd : (α → α → Prop) → (α → α → Prop) → α → α → Prop)) R
      (fun S => S = rsq R) := (desc_graph _ _ _).2 rfl

/-- ✱182·031. \(\vdash .\breve{\uparrow}ʻ\alpha =\alpha \uparrow \alpha \quad[*182·021]\) -/
theorem pm182_031 {A : Set α} :
    Desc (opDiag (cross : Set α → Set α → α → α → Prop)) A (fun X => X = cross A A) :=
  (desc_graph _ _ _).2 rfl

/-- ✱182·032. \(\vdash .\breve{{\downarrow}}ʻx=x\downarrow x \quad[*182·021]\) -/
theorem pm182_032 {x : α} :
    Desc (opDiag (couple : α → α → α → α → Prop)) x (fun X => X = x ↓ x) :=
  (desc_graph _ _ _).2 rfl

/-- ✱182·033. \(\vdash .\dot{2} -2_{r}=\text{D}ʻ\breve{{\downarrow}}=1_{s} \quad[*56·13.*182·032.*153·3]\)

`2̇` is `twoDot` (✱56·01); `D'↓̆` is `dom (opDiag couple)`. -/
theorem pm182_033 :
    (twoDot \ two_r : Set (α → α → Prop)) = dom (opDiag (couple : α → α → α → α → Prop)) ∧
      dom (opDiag (couple : α → α → α → α → Prop)) = one_s := by
  refine ⟨?_, Set.ext fun R => ⟨fun ⟨x, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, h⟩⟩⟩
  ext R
  constructor
  · rintro ⟨⟨x, y, rfl⟩, h2⟩
    by_cases hxy : x = y
    · subst hxy; exact ⟨x, rfl⟩
    · exact absurd ⟨x, y, hxy, rfl⟩ h2
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x, x, rfl⟩, ?_⟩
    rintro ⟨a, b, hab, e⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e
    exact hab rfl

/-- ✱182·04. \(\vdash .\breve{\downarrow_{,,}}ʻ\alpha =\downarrow \alpha ʻʻ\alpha \quad[*182·021.*38·2]\) -/
theorem pm182_04 {A : Set α} :
    Desc (opDiag (opImg (couple : α → Set α → α → Set α → Prop))) A
      (fun K => K = coupleR A ʻʻ A) := (desc_graph _ _ _).2 rfl

/-- ✱182·05. \(\vdash .\breve{\downarrow}_{.,}ʻQ=\downarrow Q^{;}Q=Q\downarrow_{.,} Q \quad[*182·021.*150·6]\) -/
theorem pm182_05 {Q : α → α → Prop} :
    Desc (opDiag (opSemi couple)) Q (fun X => X = coupleR Q ⁏ Q) ∧
      coupleR Q ⁏ Q = opSemi couple Q Q := ⟨(desc_graph _ _ _).2 rfl, rfl⟩

/-- ✱182·1. \[\begin{align}&\vdash .\breve{\downarrow}_{.,}^{;}P=\hat{X} \hat{Y} \{(\exists Q,R).QPR.X=Q\downarrow_{.,} Q.Y=R\downarrow_{.,} R\}\\ &[*182·023·05.*150·4]\end{align}\] -/
theorem pm182_1 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    sepRel P = fun X Y => ∃ Q R, (P Q R ∧ X = opSemi couple Q Q) ∧ Y = opSemi couple R R := by
  funext X Y; apply propext
  rw [sepRel_apply']
  exact ⟨fun ⟨Q, R, ⟨h1, h2⟩, h⟩ => ⟨Q, R, ⟨h, h1⟩, h2⟩, fun ⟨Q, R, ⟨h, h1⟩, h2⟩ => ⟨Q, R, ⟨h1, h2⟩, h⟩⟩

/-- ✱182·11. \(\vdash .Cʻ\breve{\downarrow}_{.,}^{;}P=\breve{\downarrow}_{.,}ʻʻCʻP \quad[*150·22]\) -/
theorem pm182_11 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    fld (sepRel P) = opDiag (opSemi couple) ʻʻ fld P := fld_semi_graph _ _

/-- ✱182·12. \(\vdash .Cʻ\breve{\downarrow}_{.,}ʻQ=\downarrow QʻʻCʻQ=F\unicode{x21A7}Q \quad[*182·05.*150·22.*33·5.(*85·5)]\) -/
theorem pm182_12 {Q : α → α → Prop} :
    fld (opSemi couple Q Q) = coupleR Q ʻʻ fld Q ∧ coupleR Q ʻʻ fld Q = F ↧ Q :=
  ⟨fld_semi_graph _ _, rfl⟩

/-- ✱182·13. \(\vdash .CʻʻCʻ\breve{\downarrow}_{.,}^{;}P=F\unicode{x21A7}ʻʻCʻP \quad[*182·11·12]\) -/
theorem pm182_13 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    C ʻʻ fld (sepRel P) = opL downCls F ʻʻ fld P := by
  ext A
  constructor
  · rintro ⟨X, hX, hA⟩
    obtain ⟨Q, hQ, rfl⟩ := mem_fld_sepRel.1 hX
    exact ⟨Q, hQ, (hA : A = fld _).trans (downCls_F_eq Q).symm⟩
  · rintro ⟨Q, hQ, hA⟩
    exact ⟨_, mem_fld_sepRel.2 ⟨Q, hQ, rfl⟩, (hA : A = F ↧ Q).trans (downCls_F_eq Q)⟩

/-- ✱182·14. \(\vdash .F\unicode{x21A7}\in 1\rightarrow 1\) -/
theorem pm182_14 :
    (opL downCls F : Set (α → (α → α → Prop) → Prop) → (α → α → Prop) → Prop) ∈ arrow one one :=
  mem_arrow_one_one.2 ⟨fun _ _ _ h => (h.1 : _ = _).trans (h.2 : _ = _).symm,
    fun _ _ _ h => downCls_F_inj ((h.1 : _ = _).symm.trans (h.2 : _ = _))⟩

/-- ✱182·15. \(\vdash :\exists !F\unicode{x21A7}Q\cap F\unicode{x21A7}R.\supset .Q=R\) -/
theorem pm182_15 {Q R : α → α → Prop} : (F ↧ Q ∩ F ↧ R).Nonempty → Q = R := by
  rintro ⟨c, ⟨x, -, hx⟩, ⟨y, -, hy⟩⟩
  exact (couple_eq_iff.1 ((hx : c = x ↓ Q).symm.trans hy)).2

/-- ✱182·16. \(\vdash .\breve{\downarrow}_{.,}^{;}P\in \text{Rel}^{2}\text{excl} \quad[*182·12·15]\) -/
theorem pm182_16 {P : (α → α → Prop) → (α → α → Prop) → Prop} : sepRel P ∈ Rel2excl := by
  rintro X Y ⟨⟨hX, hY⟩, hne⟩
  obtain ⟨Q, -, rfl⟩ := mem_fld_sepRel.1 hX
  obtain ⟨R, -, rfl⟩ := mem_fld_sepRel.1 hY
  rw [inter_null_iff]
  refine Set.disjoint_left.2 fun c hc hc' => hne ?_
  obtain ⟨x, -, rfl⟩ := mem_fld_sep.1 hc
  obtain ⟨y, -, e⟩ := mem_fld_sep.1 hc'
  rw [(couple_eq_iff.1 e).2]

/-- ✱182·161. \(\vdash :\breve{\downarrow}_{.,}ʻQ=\breve{\downarrow}_{.,}ʻR.\equiv .Q=R\) -/
theorem pm182_161 {Q R : α → α → Prop} : opSemi couple Q Q = opSemi couple R R ↔ Q = R :=
  ⟨sep_inj, fun h => h ▸ rfl⟩

/-- ✱182·162. \(\vdash .\breve{\downarrow}_{.,}\in 1\rightarrow 1.\breve{\downarrow}_{.,}^{;}P\,\,\text{smor}\,\,P \quad[*182·161.*71·57.*151·243]\) -/
theorem pm182_162 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    (opDiag (opSemi couple) : ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) →
      (α → α → Prop) → Prop) ∈ arrow one one ∧ smor (sepRel P) P :=
  ⟨mem_arrow_one_one.2 ⟨fun _ _ _ h => (h.1 : _ = _).trans (h.2 : _ = _).symm,
    fun _ _ _ h => sep_inj ((h.1 : _ = _).symm.trans (h.2 : _ = _))⟩,
    smor_graph_inj (fun _ _ h => sep_inj h) P⟩

/-- ✱182·17. \(\vdash .Cʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}P=\hat{S} \{(\exists Q,x).Q\in CʻP.x\in CʻQ.S=x\downarrow Q\}\) -/
theorem pm182_17 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    fld (relSigma (sepRel P)) = {S | ∃ Q x, (Q ∈ fld P ∧ x ∈ fld Q) ∧ S = x ↓ Q} :=
  Set.ext fun _ => mem_fld_sigma_sep

/-- ✱182·18. \(\vdash .\dot{s} ʻCʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}P = F\upharpoonright CʻP\) -/
theorem pm182_18 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    sumRel (fld (relSigma (sepRel P))) = F ↾ fld P := by
  funext x Q; apply propext
  constructor
  · rintro ⟨S, hS, hxQ⟩
    obtain ⟨R, y, ⟨hR, hy⟩, rfl⟩ := mem_fld_sigma_sep.1 hS
    obtain ⟨rfl, rfl⟩ := hxQ
    exact ⟨hy, hR⟩
  · rintro ⟨hx, hQ⟩
    exact ⟨x ↓ Q, mem_fld_sigma_sep.2 ⟨Q, x, ⟨hQ, hx⟩, rfl⟩, rfl, rfl⟩

/-- ✱182·19. \(\vdash . sʻ\text{D}ʻʻCʻ\Sigma ʻ \breve{\downarrow}_{.,}^{;}P = Cʻ\Sigma ʻP . sʻ\text{ᗡ}ʻʻCʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}P = CʻP - {℩}ʻ\dot{\Lambda}\) -/
theorem pm182_19 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    sumCls (D ʻʻ fld (relSigma (sepRel P))) = fld (relSigma P) ∧
      sumCls (Dcnv ʻʻ fld (relSigma (sepRel P))) = fld P \ ι rNull := by
  constructor
  · ext x
    rw [fld_relSigma']
    constructor
    · rintro ⟨A, ⟨S, hS, hA⟩, hx⟩
      obtain ⟨Q, y, ⟨hQ, hy⟩, rfl⟩ := mem_fld_sigma_sep.1 hS
      rw [(hA : A = dom _), dom_couple] at hx
      exact ⟨Q, hQ, (hx : x = y) ▸ hy⟩
    · rintro ⟨Q, hQ, hx⟩
      exact ⟨_, ⟨x ↓ Q, mem_fld_sigma_sep.2 ⟨Q, x, ⟨hQ, hx⟩, rfl⟩, rfl⟩, ⟨Q, rfl, rfl⟩⟩
  · ext Q
    constructor
    · rintro ⟨A, ⟨S, hS, hA⟩, hQ⟩
      obtain ⟨R, y, ⟨hR, hy⟩, rfl⟩ := mem_fld_sigma_sep.1 hS
      rw [(hA : A = codom _), codom_couple] at hQ
      rw [(hQ : Q = R)]
      refine ⟨hR, fun h => ?_⟩
      rw [mem_unitCls] at h
      rw [h] at hy
      exact absurd hy (by rw [fld_rNull]; exact Set.notMem_empty y)
    · rintro ⟨hQ, hne⟩
      obtain ⟨x, hx⟩ := rEx_iff_fld.1 (ne_rNull_iff.1 hne)
      exact ⟨_, ⟨x ↓ Q, mem_fld_sigma_sep.2 ⟨Q, x, ⟨hQ, hx⟩, rfl⟩, rfl⟩, ⟨x, rfl, rfl⟩⟩

/-- ✱182·2. \(\vdash .\breve{\downarrow}_{.,}ʻQ=\Pi ʻ(Q\downarrow Q)=\Pi ʻ\breve{{\downarrow}}ʻQ \quad[*182·05·032 . *172·2]\)

`↓̆.,'Q` is written `opSemi couple Q Q`; the description `↓̆'Q` of the second equation is kept. -/
theorem pm182_2 {Q : α → α → Prop} :
    opSemi couple Q Q = relPi (Q ↓ Q) ∧ Desc (opDiag couple) Q (fun X => relPi (Q ↓ Q) = relPi X) :=
  ⟨(relPi_couple_self Q).symm, (desc_graph _ _ _).2 rfl⟩

/-- ✱182·21. \(\vdash .\breve{\downarrow}_{.,}^{;}P=\Pi ^{;}\breve{{\downarrow}}^{;}P \quad[*182·2]\) -/
theorem pm182_21 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    sepRel P = RelPi ⁏ opDiag couple ⁏ P := by
  rw [semi_semi, show (RelPi ⨾ opDiag couple : _ → (α → α → Prop) → Prop) =
    graph (fun Q => relPi (Q ↓ Q)) from graph_relProd_graph _ _, sepRel_eq]
  exact graph_semi_congr fun Q _ => (relPi_couple_self Q).symm

/-- ✱182·22. \(\vdash .\text{D}^{;}\breve{\downarrow}_{.,}ʻQ=\text{Prod}ʻ\breve{{\downarrow}}ʻQ={℩}^{;}Q \quad[*182·2 *173·1·22]\)

`Prod'↓̆'Q` is written `prodR (Q ↓ Q)`. -/
theorem pm182_22 {Q : α → α → Prop} :
    D ⁏ opSemi couple Q Q = prodR (Q ↓ Q) ∧ prodR (Q ↓ Q) = iota ⁏ Q := by
  have e : prodR (Q ↓ Q) = D ⁏ opSemi couple Q Q := by
    show D ⁏ relPi (Q ↓ Q) = _; rw [relPi_couple_self]
  exact ⟨e.symm, e.trans (D_sep Q)⟩

/-- ✱182·23. \(\vdash .\breve{{℩}} ^{;}\text{D}^{;}\breve{\downarrow}_{.,}ʻQ=Q \quad[*182·22. *151·252]\) -/
theorem pm182_23 {Q : α → α → Prop} : iota˘ ⁏ D ⁏ opSemi couple Q Q = Q := iota_D_sep Q

/-- ✱182·24. \(\vdash .\breve{{℩}} \dagger ^{;}\text{D}\dagger ^{;}\breve{\downarrow}_{.,}^{;}P=P \quad[*182·23]\) -/
theorem pm182_24 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    daggerRel iota˘ ⁏ daggerRel D ⁏ sepRel P = P := by
  rw [daggerRel_eq_graph, daggerRel_eq_graph, sepRel_eq, semi_semi, semi_semi, graph_relProd_graph,
    graph_relProd_graph]
  refine (graph_semi_congr (g := fun Q => Q) fun Q _ => ?_).trans (graph_id_semi P)
  exact iota_D_sep Q

/-- ✱182·25. \(\vdash .\breve{{℩}} ^{;}\text{D}^{;}\Sigma ʻ\breve{\downarrow}_{.,}^{;}P=\Sigma ʻP.Cʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}P\subset \text{ᗡ}ʻ(\breve{{℩}} \mid \text{D})\) -/
theorem pm182_25 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    iota˘ ⁏ D ⁏ relSigma (sepRel P) = relSigma P ∧
      fld (relSigma (sepRel P)) ⊆ codom (iota˘ ⨾ D) := by
  constructor
  · have e1 : relSigma (daggerRel D ⁏ sepRel P) = D ⁏ relSigma (sepRel P) :=
      relSigma_dagger fun _ _ z _ => ⟨dom z, rfl⟩
    have e2 : relSigma (daggerRel iota˘ ⁏ daggerRel D ⁏ sepRel P) =
        iota˘ ⁏ relSigma (daggerRel D ⁏ sepRel P) := by
      refine relSigma_dagger fun S hS z hz => ?_
      obtain ⟨X, hX, rfl⟩ := mem_fld_graph_semi.1 hS
      obtain ⟨Q, -, rfl⟩ := mem_fld_sepRel.1 hX
      rw [show daggerOp D (opSemi couple Q Q) = iota ⁏ Q from D_sep Q] at hz
      obtain ⟨x, -, hzx⟩ := (mem_fld_graph_semi (f := fun x : α => ι x)).1 hz
      exact ⟨x, hzx⟩
    rw [← e1, ← e2, pm182_24]
  · intro S hS
    obtain ⟨Q, x, -, rfl⟩ := mem_fld_sigma_sep.1 hS
    exact ⟨x, ι x, rfl, (dom_couple x Q).symm⟩

/-- ✱182·26. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\breve{\iota} \mid \text{D}\upharpoonright Cʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}P\in P\,\overline{\,\text{smor}\,} \,\overline{\,\text{smor}\,}\, \breve{\downarrow}_{.,}^{;}P\) -/
theorem pm182_26 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl → (iota˘ ⨾ D) ↾ fld (relSigma (sepRel P)) ∈ smorsmorbar P (sepRel P) := by
  intro hP
  have hT : ∀ x S, ((iota˘ ⨾ D) ↾ fld (relSigma (sepRel P))) x S ↔
      dom S = ι x ∧ S ∈ fld (relSigma (sepRel P)) := fun x S =>
    ⟨fun ⟨⟨A, hA, hA'⟩, h⟩ => ⟨(hA' : A = dom S).symm.trans hA, h⟩,
      fun ⟨h, h'⟩ => ⟨⟨ι x, rfl, h.symm⟩, h'⟩⟩
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y S ⟨hx, hy⟩
    exact unitCls_injective (((hT x S).1 hx).1.symm.trans ((hT y S).1 hy).1)
  · rintro x S S' ⟨hS, hS'⟩
    obtain ⟨h1, h2⟩ := (hT x S).1 hS
    obtain ⟨h1', h2'⟩ := (hT x S').1 hS'
    obtain ⟨Q, u, ⟨hQ, hu⟩, rfl⟩ := mem_fld_sigma_sep.1 h2
    obtain ⟨Q', u', ⟨hQ', hu'⟩, rfl⟩ := mem_fld_sigma_sep.1 h2'
    rw [dom_couple] at h1 h1'
    have e1 := unitCls_injective h1; have e2 := unitCls_injective h1'
    subst e1 e2
    by_contra hne
    have := (mem_Rel2excl.1 hP) Q Q' ⟨⟨hQ, hQ'⟩, fun e => hne (by rw [e])⟩
    rw [inter_null_iff] at this
    exact Set.disjoint_left.1 this hu hu'
  · show fld (relSigma (sepRel P)) = codom _
    ext S
    constructor
    · intro hS
      obtain ⟨Q, x, -, rfl⟩ := mem_fld_sigma_sep.1 hS
      exact ⟨x, (hT x _).2 ⟨dom_couple x Q, hS⟩⟩
    · rintro ⟨x, -, h⟩; exact h
  · show P = daggerRel _ ⁏ sepRel P
    rw [daggerRel_eq_graph, sepRel_eq, semi_semi, graph_relProd_graph]
    refine (graph_id_semi P).symm.trans (graph_semi_congr fun Q hQ => ?_)
    funext u v; apply propext
    show Q u v ↔ (_ ⁏ opSemi couple Q Q) u v
    rw [semi_apply]
    constructor
    · intro huv
      exact ⟨u ↓ Q, v ↓ Q, ⟨(hT u _).2 ⟨dom_couple u Q, mem_fld_sigma_sep.2 ⟨Q, u, ⟨hQ, ⟨v, Or.inl huv⟩⟩,
        rfl⟩⟩, (hT v _).2 ⟨dom_couple v Q, mem_fld_sigma_sep.2 ⟨Q, v, ⟨hQ, ⟨u, Or.inr huv⟩⟩, rfl⟩⟩⟩,
        sep_apply.2 ⟨u, v, ⟨rfl, rfl⟩, huv⟩⟩
    · rintro ⟨S, S', ⟨hS, hS'⟩, h⟩
      obtain ⟨x, y, ⟨rfl, rfl⟩, hxy⟩ := sep_apply.1 h
      have e1 := ((hT u _).1 hS).1; have e2 := ((hT v _).1 hS').1
      rw [dom_couple] at e1 e2
      rw [← unitCls_injective e1, ← unitCls_injective e2]; exact hxy

/-- ✱182·27. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .P \,\,\text{smor}\, \,\text{smor}\, \breve{\downarrow}_{.,}^{;}P \quad[*182·26]\) -/
theorem pm182_27 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl → smorsmor P (sepRel P) := fun h => ⟨_, pm182_26 h⟩

/-- ✱182·3. \(\vdash :T\upharpoonright Cʻ\Sigma ʻQ\in P\,\overline{\,\text{smor}\,} \,\overline{\,\text{smor}\,}\, Q.\supset .(T\parallel \text{Cnv}ʻT\dagger )\upharpoonright Cʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}Q\in 1\rightarrow 1\) -/
theorem pm182_3 {T : α → β → Prop} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    T ↾ fld (relSigma Q) ∈ smorsmorbar P Q →
      (T ∥ (daggerRel T)˘) ↾ fld (relSigma (sepRel Q)) ∈ arrow one one := by
  intro h
  obtain ⟨h1, h2, h3, -⟩ := smorsmorbar_data h
  rw [dpar_eq_graph]
  have hf : ∀ y S, S ∈ fld Q → y ∈ fld S → ∃ x, T x y ∧
      T ⨾ ((y ↓ S) ⨾ (daggerRel T)˘) = x ↓ (T ⁏ S) := fun y S hS hy => by
    obtain ⟨x, hx⟩ := h3 y (fld_sub_sigma hS hy)
    exact ⟨x, hx, dpar_couple hx fun u hu => h1 u x y (fld_sub_sigma hS hy) hu hx⟩
  refine mem_arrow_one_one.2 ⟨fun X X' Y ⟨hX, hX'⟩ => (hX.1 : X = _).trans (hX'.1 : X' = _).symm, ?_⟩
  rintro X Y Y' ⟨⟨hY, hYB⟩, ⟨hY', hYB'⟩⟩
  obtain ⟨S, y, ⟨hS, hy⟩, rfl⟩ := mem_fld_sigma_sep.1 hYB
  obtain ⟨S', y', ⟨hS', hy'⟩, rfl⟩ := mem_fld_sigma_sep.1 hYB'
  obtain ⟨x, hx, ex⟩ := hf y S hS hy
  obtain ⟨x', hx', ex'⟩ := hf y' S' hS' hy'
  have e := (hY : X = _).symm.trans (hY' : X = _)
  simp only [] at e
  rw [ex, ex', couple_eq_iff] at e
  obtain ⟨rfl, eS⟩ := e
  have hyy' := h2 x y y' (fld_sub_sigma hS hy) (fld_sub_sigma hS' hy') hx hx'
  subst hyy'
  suffices S = S' by rw [this]
  funext u v; apply propext
  have key : ∀ {S S'}, S ∈ fld Q → S' ∈ fld Q → T ⁏ S = T ⁏ S' → ∀ u v, S u v → S' u v := by
    intro S S' hS hS' eS u v huv
    obtain ⟨a, ha⟩ := h3 u (fld_sub_sigma hS ⟨v, Or.inl huv⟩)
    obtain ⟨b, hb⟩ := h3 v (fld_sub_sigma hS ⟨u, Or.inr huv⟩)
    have : (T ⁏ S') a b := by rw [← eS]; exact (semi_apply _ _ _ _).2 ⟨u, v, ⟨ha, hb⟩, huv⟩
    obtain ⟨u', v', ⟨ha', hb'⟩, huv'⟩ := (semi_apply _ _ _ _).1 this
    rw [h2 a u u' (fld_sub_sigma hS ⟨v, Or.inl huv⟩) (fld_sub_sigma hS' ⟨v', Or.inl huv'⟩) ha ha',
      h2 b v v' (fld_sub_sigma hS ⟨u, Or.inr huv⟩) (fld_sub_sigma hS' ⟨u', Or.inr huv'⟩) hb hb']
    exact huv'
  exact ⟨key hS hS' eS u v, key hS' hS eS.symm u v⟩

/-- ✱182·31. \(\vdash :\text{E}!!TʻʻCʻS.\supset .\breve{\downarrow}_{.,}ʻT^{;}S=(T\parallel \text{Cnv}ʻT\dagger )^{;}\breve{\downarrow}_{.,}ʻS\) -/
theorem pm182_31 {T : α → β → Prop} {S : β → β → Prop} :
    EE T (fld S) → opSemi couple (T ⁏ S) (T ⁏ S) = (T ∥ (daggerRel T)˘) ⁏ opSemi couple S S :=
  pm182_aux_31

/-- ✱182·32. \(\vdash :\text{E}!!TʻʻCʻ\Sigma ʻQ.\supset .\breve{\downarrow}_{.,}^{;}T\dagger ^{;}Q=(T\parallel \text{Cnv}ʻT\dagger )\dagger ^{;}\breve{\downarrow}_{.,}^{;}Q\) -/
theorem pm182_32 {T : α → β → Prop} {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    EE T (fld (relSigma Q)) →
      sepRel (daggerRel T ⁏ Q) = daggerRel (T ∥ (daggerRel T)˘) ⁏ sepRel Q :=
  pm182_aux_32

/-- ✱182·33. \[\begin{align}\vdash :T\upharpoonright Cʻ\Sigma ʻP\in P&\,\overline{\,\text{smor}\,} \,\overline{\,\text{smor}\,}\, Q.\supset .\\ &(T\parallel \text{Cnv}ʻT\dagger )\upharpoonright Cʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}Q\in (\breve{\downarrow}_{.,}^{;}P)\overline{\,\text{smor}\,} \overline{\,\text{smor}\,} (\breve{\downarrow}_{.,}^{;}Q)\end{align}\]

**Status.** proved (reading): the e-text prints the hypothesis `T ↾ C'Σ'P ∈ P smor̄smor̄ Q`; the
correlator `T` relates the fields of the members of `C'P` to those of `C'Q`, so only
`T ↾ C'Σ'Q` is significant (as in ✱182·3, and the Dem., which uses ✱164·18 and ✱182·3) -/
theorem pm182_33 {T : α → β → Prop} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    T ↾ fld (relSigma Q) ∈ smorsmorbar P Q →
      (T ∥ (daggerRel T)˘) ↾ fld (relSigma (sepRel Q)) ∈
        smorsmorbar (sepRel P) (sepRel Q) := by
  intro h
  obtain ⟨h1, h2, h3, hP⟩ := smorsmorbar_data h
  refine ⟨⟨pm182_3 h, ?_⟩, ?_⟩
  · show fld (relSigma (sepRel Q)) = codom _
    ext Y
    exact ⟨fun hY => ⟨_, (dpar_iff _ _ _ _).2 rfl, hY⟩, fun ⟨_, _, hY⟩ => hY⟩
  · show sepRel P = daggerRel _ ⁏ sepRel Q
    rw [hP, sepRel_eq, sepRel_eq, daggerRel_eq_graph, daggerRel_eq_graph, semi_semi, semi_semi,
      graph_relProd_graph, graph_relProd_graph]
    refine graph_semi_congr fun S hS => ?_
    have hEE : EE T (fld S) := EE_of_data h1 h3 (fld_sub_sigma hS)
    show opSemi couple ((T ↾ fld (relSigma Q)) ⁏ S) ((T ↾ fld (relSigma Q)) ⁏ S) =
      ((T ∥ (daggerRel T)˘) ↾ fld (relSigma (sepRel Q))) ⁏ opSemi couple S S
    have e1 : (T ↾ fld (relSigma Q)) ⁏ S = T ⁏ S :=
      semi_congr fun x z hz => ⟨fun h => h.1, fun h => ⟨h, fld_sub_sigma hS hz⟩⟩
    have e2 : ((T ∥ (daggerRel T)˘) ↾ fld (relSigma (sepRel Q))) ⁏ opSemi couple S S =
        (T ∥ (daggerRel T)˘) ⁏ opSemi couple S S :=
      semi_congr fun X Y hY => ⟨fun h => h.1, fun h => ⟨h, fld_sep_sub hS hY⟩⟩
    rw [e1, e2, pm182_aux_31 hEE]

/-- ✱182·34. \(\vdash :P\,\text{smor}\,\text{smor}Q.\supset .\breve{\downarrow}_{.,}^{;}P\,\text{smor}\,\text{smor}\breve{\downarrow}_{.,}^{;}Q \quad[*182·33]\) -/
theorem pm182_34 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor P Q → smorsmor (sepRel P) (sepRel Q) := by
  rintro ⟨T, hT⟩
  have e : T ↾ fld (relSigma Q) = T := by
    funext x y; apply propext
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    have hc : fld (relSigma Q) = codom T := hT.1.2
    rw [hc]; exact ⟨x, h⟩
  rw [← e] at hT
  exact ⟨_, pm182_33 hT⟩

/-- ✱182·411. \(\vdash .\dot{s} ʻCʻ\breve{{\downarrow}}^{;}P=I\upharpoonright CʻP\) -/
theorem pm182_411 {P : α → α → Prop} :
    sumRel (fld (opDiag (couple : α → α → α → α → Prop) ⁏ P)) = I ↾ fld P := by
  funext x y; apply propext
  constructor
  · rintro ⟨S, hS, hxy⟩
    obtain ⟨z, hz, rfl⟩ := mem_fld_graph_semi.1 hS
    obtain ⟨rfl, rfl⟩ := hxy
    exact ⟨rfl, hz⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨x ↓ x, mem_fld_graph_semi.2 ⟨x, hx, rfl⟩, rfl, rfl⟩

/-- ✱182·412. \(\vdash .F^{;}\breve{{\downarrow}}^{;}P=P\) -/
theorem pm182_412 {P : α → α → Prop} : F ⁏ opDiag (couple : α → α → α → α → Prop) ⁏ P = P := by
  rw [semi_semi]
  have : (F ⨾ opDiag (couple : α → α → α → α → Prop)) = graph (fun x : α => x) := by
    funext x z; apply propext
    constructor
    · rintro ⟨S, hS, rfl⟩
      obtain ⟨w, ⟨h, -⟩ | ⟨-, h⟩⟩ := hS <;> exact h
    · rintro rfl; exact ⟨x ↓ x, ⟨x, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩
  rw [this, graph_id_semi]

/-- ✱182·413. \(\vdash .\Sigma ʻ\breve{{\downarrow}}^{;}P=P\unicode{x228d} I\upharpoonright CʻP \quad[*182·411·412.*162·1]\) -/
theorem pm182_413 {P : α → α → Prop} :
    relSigma (opDiag (couple : α → α → α → α → Prop) ⁏ P) = P ⊍ I ↾ fld P := by
  show sumRel (fld _) ⊍ F ⁏ _ = _
  rw [pm182_411, pm182_412]
  funext x y; apply propext; exact or_comm

/-- ✱182·414. \(\vdash .\breve{{\downarrow}}^{;}P\in \text{Rel}^{2}\text{excl}\) -/
theorem pm182_414 {P : α → α → Prop} :
    opDiag (couple : α → α → α → α → Prop) ⁏ P ∈ Rel2excl := by
  rintro X Y ⟨⟨hX, hY⟩, hne⟩
  obtain ⟨x, -, rfl⟩ := mem_fld_graph_semi.1 hX
  obtain ⟨y, -, rfl⟩ := mem_fld_graph_semi.1 hY
  rw [inter_null_iff, fld_couple_self, fld_couple_self, Set.disjoint_singleton]
  exact fun e => hne (by rw [e])

/-- ✱182·415. \(\vdash :Q\in Cʻ\breve{{\downarrow}}^{;}P.\supset .CʻQ\in 1\) -/
theorem pm182_415 {P : α → α → Prop} {Q : α → α → Prop} :
    Q ∈ fld (opDiag (couple : α → α → α → α → Prop) ⁏ P) → fld Q ∈ one := by
  intro h
  obtain ⟨x, -, rfl⟩ := mem_fld_graph_semi.1 h
  rw [fld_couple_self]; exact ⟨x, rfl⟩

/-- ✱182·42. \(\vdash .\Pi ʻP=\dot{s} ^{;}\text{Prod}ʻ\breve{\downarrow}_{.,}^{;}P=\dot{s} ^{;}\text{D}^{;}\Pi ʻ\breve{\downarrow}_{.,}^{;}P=\Pi ʻ\Sigma ʻ\breve{{\downarrow}}^{;}P\) -/
theorem pm182_42 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    (relPi P = sDotRel ⁏ prodR (sepRel P) ∧
      sDotRel ⁏ prodR (sepRel P) = sDotRel ⁏ D ⁏ relPi (sepRel P)) ∧
      sDotRel ⁏ D ⁏ relPi (sepRel P) = relPi (relSigma (opDiag couple ⁏ P)) := by
  have e : sDotRel ⁏ D ⁏ relPi (sepRel P) = relPi P := by
    rw [semi_semi, sDot_D, ← relPi_eq_sdot]
  refine ⟨⟨e.symm, rfl⟩, e.trans ?_⟩
  rw [pm182_413, relPi_union_I]

/-- ✱182·43. \(\vdash .\dot{s} \upharpoonright (Cʻ\text{Prod}ʻ\breve{\downarrow}_{.,}^{;}P)\in (\Pi ʻP)\overline{\,\text{smor}\,} (\text{Prod}ʻ\breve{\downarrow}_{.,}^{;}P)\) -/
theorem pm182_43 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    sDotRel ↾ fld (prodR (sepRel P)) ∈ smorbar (relPi P) (prodR (sepRel P)) := by
  have e : relPi P = graph sumRel ⁏ prodR (sepRel P) := pm182_42.1.1
  rw [e]
  refine graph_cres_smorbar fun A B hA hB h => ?_
  obtain ⟨M', hM', rfl⟩ := mem_fld_graph_semi.1 hA
  obtain ⟨N', hN', rfl⟩ := mem_fld_graph_semi.1 hB
  rw [← lift_g (mem_fld_relPi hM'), ← lift_g (mem_fld_relPi hN')]
  exact congrArg (fun X => dom (liftSel X)) h

/-- ✱182·431. \[\begin{align}&\vdash .\dot{s} \mid \text{D} \upharpoonright (Cʻ\Pi ʻ\breve{\downarrow}_{.,}^{;}P) \in (\Pi ʻP) \overline{\,\text{smor}\,} (\Pi ʻ\breve{\downarrow}_{.,}^{;}P)\\ &[*174·221. *182·414·415·21·42]\end{align}\] -/
theorem pm182_431 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    (sDotRel ⨾ D) ↾ fld (relPi (sepRel P)) ∈ smorbar (relPi P) (relPi (sepRel P)) := by
  rw [sDot_D, relPi_eq_sdot P]
  refine graph_cres_smorbar fun M N hM hN h => ?_
  rw [← lift_g (mem_fld_relPi hM), ← lift_g (mem_fld_relPi hN)]
  exact congrArg liftSel h

/-- ✱182·44. \(\vdash . \text{Nr}ʻ\Pi ʻP = \text{Nr}ʻ\text{Prod}ʻ\breve{\downarrow}_{.,}^{;}P = \text{Nr}ʻ\Pi ʻ\breve{\downarrow}_{.,}^{;}P \quad[*182·43·431 . *152·321]\) -/
theorem pm182_44 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    nr γ (relPi P) = nr γ (prodR (sepRel P)) ∧
      nr γ (prodR (sepRel P)) = nr γ (relPi (sepRel P)) := by
  have h1 : smor (relPi P) (prodR (sepRel P)) := ⟨_, pm182_43⟩
  have h2 : smor (relPi P) (relPi (sepRel P)) := ⟨_, pm182_431⟩
  exact ⟨nr_eq_nr_of_smor h1, nr_eq_nr_of_smor (smor_trans (smor_symm h1) h2)⟩

/-- ✱182·45. \(\vdash : P \in \text{Rel}^{2}\text{excl} . \supset . \text{Nr}ʻ\text{Prod}ʻP = \text{Nr}ʻ\text{Prod}ʻ\breve{\downarrow}_{.,}^{;}P \quad[*182·44 . *173·16]\) -/
theorem pm182_45 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl → nr γ (prodR P) = nr γ (prodR (sepRel P)) := fun hP =>
  (nr_eq_nr_of_smor (smor_prodR_relPi hP)).trans pm182_44.1

/-- ✱182·5. \(\vdash . \in \unicode{x21A7} \alpha = \breve{\downarrow_{,,}} ʻ\alpha \quad[*182·04 . *85·601]\) -/
theorem pm182_5 {A : Set α} :
    Desc (opDiag (opImg (couple : α → Set α → α → Set α → Prop))) A (fun K => memRel ↧ A = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱182·51. \(\vdash . \in \unicode{x21A7}ʻʻ\kappa = \breve{\downarrow_{,,}} ʻʻ\kappa \quad[*182·5]\) -/
theorem pm182_51 {K : Set (Set α)} :
    opL downCls memRel ʻʻ K = opDiag (opImg (couple : α → Set α → α → Set α → Prop)) ʻʻ K := rfl

/-- ✱182·52. \(\vdash . \Sigma ʻ\kappa = sʻ\breve{\downarrow_{,,}}ʻʻ\kappa . \Sigma \text{Nc}ʻ\kappa = \text{Nc}ʻsʻ\breve{\downarrow_{,,}}ʻʻ\kappa \quad[*182·51 . *112·1·101]\) -/
theorem pm182_52 {K : Set (Set α)} :
    clsSigma K = sumCls (opDiag (opImg (couple : α → Set α → α → Set α → Prop)) ʻʻ K) ∧
      sigmaNc γ K = nc γ (sumCls (opDiag (opImg (couple : α → Set α → α → Set α → Prop)) ʻʻ K)) :=
  ⟨rfl, rfl⟩

/-- ✱182·53. \[\begin{align}\vdash : C \upharpoonright CʻP \in 1 &\rightarrow 1 . \supset .\\ &(\mid \breve{C} ) \upharpoonright (Cʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}P) \in (\breve{\downarrow_{,,}}ʻʻCʻʻCʻP) \,\overline{\text{ sm }}\, \,\overline{\text{ sm }}\, (CʻʻCʻ\breve{\downarrow}_{.,}^{;}P)\end{align}\] -/
theorem pm182_53 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    C ↾ fld P ∈ arrow one one → relProdR C˘ ↾ fld (relSigma (sepRel P)) ∈
      smsmbar (opDiag (opImg (couple : α → Set α → α → Set α → Prop)) ʻʻ C ʻʻ fld P)
        (C ʻʻ fld (sepRel P)) := by
  intro hC
  obtain ⟨-, c2⟩ := mem_arrow_one_one.1 hC
  have hT : ∀ X Y, (relProdR C˘ ↾ fld (relSigma (sepRel P))) X Y ↔
      X = Y ⨾ C˘ ∧ Y ∈ fld (relSigma (sepRel P)) := fun _ _ => Iff.rfl
  refine ⟨⟨mem_arrow_one_one.2 ⟨fun X X' Y h => ((hT X Y).1 h.1).1.trans ((hT X' Y).1 h.2).1.symm,
    ?_⟩, ?_⟩, ?_⟩
  · rintro X Y Y' ⟨hY, hY'⟩
    obtain ⟨e1, hB⟩ := (hT X Y).1 hY
    obtain ⟨e2, hB'⟩ := (hT X Y').1 hY'
    obtain ⟨Q, y, ⟨hQ, -⟩, rfl⟩ := mem_fld_sigma_sep.1 hB
    obtain ⟨Q', y', ⟨hQ', -⟩, rfl⟩ := mem_fld_sigma_sep.1 hB'
    rw [couple_C] at e1 e2
    obtain ⟨rfl, ef⟩ := couple_eq_iff.1 (e1.symm.trans e2)
    rw [c2 (fld Q) Q Q' ⟨⟨rfl, hQ⟩, ⟨ef, hQ'⟩⟩]
  · show sumCls (C ʻʻ fld (sepRel P)) = codom _
    ext Y
    constructor
    · rintro ⟨A, ⟨X, hX, hA⟩, hY⟩
      rw [(hA : A = fld X)] at hY
      exact ⟨_, rfl, fld_relSigma'.2 ⟨X, hX, hY⟩⟩
    · rintro ⟨_, -, hY⟩
      obtain ⟨X, hX, hY'⟩ := fld_relSigma'.1 hY
      exact ⟨fld X, ⟨X, hX, rfl⟩, hY'⟩
  · show _ = imgRel _ ʻʻ C ʻʻ fld (sepRel P)
    ext K
    constructor
    · rintro ⟨A, ⟨Q, hQ, hA⟩, hK⟩
      refine ⟨fld (opSemi couple Q Q), ⟨_, mem_fld_sepRel.2 ⟨Q, hQ, rfl⟩, rfl⟩, ?_⟩
      rw [(hK : K = _), (hA : A = fld Q)]
      show _ = _ ʻʻ _
      ext X
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y ↓ Q, mem_fld_sep.2 ⟨y, hy, rfl⟩, by rw [hT, couple_C]; exact ⟨rfl,
          mem_fld_sigma_sep.2 ⟨Q, y, ⟨hQ, hy⟩, rfl⟩⟩⟩
      · rintro ⟨Y, hY, hXY⟩
        obtain ⟨y, hy, rfl⟩ := mem_fld_sep.1 hY
        rw [hT, couple_C] at hXY
        exact ⟨y, hy, hXY.1⟩
    · rintro ⟨B, ⟨X, hX, hB⟩, hK⟩
      obtain ⟨Q, hQ, rfl⟩ := mem_fld_sepRel.1 hX
      refine ⟨fld Q, ⟨Q, hQ, rfl⟩, ?_⟩
      rw [(hK : K = _), (hB : B = _)]
      show _ ʻʻ _ = _
      ext X
      constructor
      · rintro ⟨Y, hY, hXY⟩
        obtain ⟨y, hy, rfl⟩ := mem_fld_sep.1 hY
        rw [hT, couple_C] at hXY
        exact ⟨y, hy, hXY.1⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y ↓ Q, mem_fld_sep.2 ⟨y, hy, rfl⟩, by rw [hT, couple_C]; exact ⟨rfl,
          mem_fld_sigma_sep.2 ⟨Q, y, ⟨hQ, hy⟩, rfl⟩⟩⟩

/-- ✱182·54. \[\begin{align}&\vdash : C \upharpoonright CʻP \in 1 \rightarrow 1 . \supset . \text{Nc}ʻCʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}P = \Sigma \text{Nc}ʻCʻʻCʻP\\ &[*182·52·53 . *111·44]\end{align}\] -/
theorem pm182_54 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    C ↾ fld P ∈ arrow one one →
      nc γ (fld (relSigma (sepRel P))) = sigmaNc γ (C ʻʻ fld P) := by
  intro hC
  obtain ⟨-, c2⟩ := mem_arrow_one_one.1 hC
  refine nc_eq_nc_of_sm (sm_symm (sm_of_inj_img (fun Y => Y ⨾ C˘) ?_ ?_))
  · intro Y Y' hY hY' e
    obtain ⟨Q, y, ⟨hQ, -⟩, rfl⟩ := mem_fld_sigma_sep.1 hY
    obtain ⟨Q', y', ⟨hQ', -⟩, rfl⟩ := mem_fld_sigma_sep.1 hY'
    simp only [couple_C] at e
    obtain ⟨rfl, ef⟩ := couple_eq_iff.1 e
    rw [c2 (fld Q) Q Q' ⟨⟨rfl, hQ⟩, ⟨ef, hQ'⟩⟩]
  · intro Z
    constructor
    · rintro ⟨K, ⟨A, ⟨Q, hQ, hA⟩, hK⟩, hZ⟩
      rw [(hK : K = _), (hA : A = fld Q)] at hZ
      obtain ⟨y, hy, rfl⟩ := hZ
      exact ⟨y ↓ Q, mem_fld_sigma_sep.2 ⟨Q, y, ⟨hQ, hy⟩, rfl⟩, (couple_C y Q).symm⟩
    · rintro ⟨Y, hY, rfl⟩
      obtain ⟨Q, y, ⟨hQ, hy⟩, rfl⟩ := mem_fld_sigma_sep.1 hY
      rw [couple_C]
      exact ⟨_, ⟨fld Q, ⟨Q, hQ, rfl⟩, rfl⟩, y, hy, rfl⟩


section Helpers183

private theorem smor_sep (Q : α → α → Prop) : smor (opSemi couple Q Q) Q :=
  smor_graph_inj (fun x y h => (couple_eq_iff.1 h).1) Q

private theorem rEx_relSigma {X : (α → α → Prop) → (α → α → Prop) → Prop} :
    rEx (relSigma X) ↔ ∃ Q, Q ∈ fld X ∧ rEx Q := by
  rw [rEx_iff_fld]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨Q, hQ, hx⟩ := fld_relSigma'.1 hx
    exact ⟨Q, hQ, rEx_iff_fld.2 ⟨x, hx⟩⟩
  · rintro ⟨Q, hQ, hQ'⟩
    obtain ⟨x, hx⟩ := rEx_iff_fld.1 hQ'
    exact ⟨x, fld_relSigma'.2 ⟨Q, hQ, hx⟩⟩

private theorem relSigma_eq_rNull_iff {X : (α → α → Prop) → (α → α → Prop) → Prop} :
    relSigma X = rNull ↔ ∀ Q, Q ∈ fld X → Q = rNull := by
  constructor
  · intro h Q hQ
    by_contra hne
    exact ne_rNull_iff.2 (rEx_relSigma.2 ⟨Q, hQ, ne_rNull_iff.1 hne⟩) h
  · intro h
    by_contra hne
    obtain ⟨Q, hQ, hQ'⟩ := rEx_relSigma.1 (ne_rNull_iff.1 hne)
    exact ne_rNull_iff.2 hQ' (h Q hQ)

private theorem relSigma_sep_eq_rNull_iff {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    relSigma (sepRel P) = rNull ↔ relSigma P = rNull := by
  rw [relSigma_eq_rNull_iff, relSigma_eq_rNull_iff]
  constructor
  · intro h Q hQ
    have := h _ (mem_fld_sepRel.2 ⟨Q, hQ, rfl⟩)
    have h2 : smor (opSemi couple Q Q)
        (rNull : (α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) :=
      smor_rNull_iff'.2 this
    exact smor_rNull_iff'.1 (smor_trans (smor_symm (smor_sep Q)) h2)
  · intro h Y hY
    obtain ⟨Q, hQ, rfl⟩ := mem_fld_sepRel.1 hY
    rw [h Q hQ]
    exact smor_rNull_iff'.1 (smor_sep _)

private theorem rel2excl_eq {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : P ∈ Rel2excl)
    {Q R : α → α → Prop} (hQ : Q ∈ fld P) (hR : R ∈ fld P) {x : α} (hxQ : x ∈ fld Q)
    (hxR : x ∈ fld R) : Q = R := by
  by_contra hne
  have := (mem_Rel2excl.1 hP) Q R ⟨⟨hQ, hR⟩, hne⟩
  rw [inter_null_iff] at this
  exact Set.disjoint_left.1 this hxQ hxR

/-- `Mult ax . ⊃ :` exclusive relations of relations with a correlator contained in `smor` are
doubly like (✱164·46; here `Classical.choice` does the work of `Mult ax`). -/
private theorem smorsmor_of_corr {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} (hP : P ∈ Rel2excl) (hQ : Q ∈ Rel2excl)
    {S : (α → α → Prop) → (β → β → Prop) → Prop} (hS : S ∈ smorbar P Q) (hSs : S ⪽ smor) :
    smorsmor P Q := by
  classical
  obtain ⟨⟨hS1, hcod⟩, hPS⟩ := hS
  obtain ⟨s1, s2⟩ := mem_arrow_one_one.1 hS1
  have hcodQ : ∀ Y, Y ∈ fld Q ↔ ∃ X, S X Y := fun Y => by rw [hcod]; rfl
  have hfP : ∀ X Y, S X Y → X ∈ fld P := fun X Y h => by
    rw [hPS]; exact (mem_fld_semi fun z hz => (hcodQ z).1 hz).2 ⟨Y, (hcodQ Y).2 ⟨X, h⟩, h⟩
  let c : (α → α → Prop) → (β → β → Prop) → α → β → Prop :=
    fun X Y => if h : smor X Y then Classical.choose h else rNull
  have hc : ∀ X Y, S X Y → c X Y ∈ smorbar X Y := fun X Y h => by
    show (if h' : smor X Y then Classical.choose h' else rNull) ∈ smorbar X Y
    rw [dite_eq_left_of_eq_true (eq_true (hSs X Y h))]; exact Classical.choose_spec (hSs X Y h)
  have hc' : ∀ X Y, S X Y → ((∀ x x' y, c X Y x y → c X Y x' y → x = x') ∧
      (∀ x y y', c X Y x y → c X Y x y' → y = y')) ∧ (∀ y, y ∈ fld Y ↔ ∃ x, c X Y x y) ∧
      X = c X Y ⁏ Y := fun X Y h => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc X Y h
    obtain ⟨a, b⟩ := mem_arrow_one_one.1 h1
    exact ⟨⟨fun x x' y hx hx' => a x x' y ⟨hx, hx'⟩, fun x y y' hy hy' => b x y y' ⟨hy, hy'⟩⟩,
      fun y => by rw [h2]; rfl, h3⟩
  have hx_fld : ∀ X Y x y, S X Y → c X Y x y → x ∈ fld X := fun X Y x y h hxy => by
    obtain ⟨-, h2, h3⟩ := hc' X Y h
    rw [h3]; exact (mem_fld_semi fun z hz => (h2 z).1 hz).2 ⟨y, (h2 y).2 ⟨x, hxy⟩, hxy⟩
  let U : α → β → Prop := fun x y => ∃ X Y, S X Y ∧ c X Y x y
  have hU : ∀ X Y, S X Y → U ⁏ Y = X := fun X Y h => by
    obtain ⟨-, h2, h3⟩ := hc' X Y h
    rw [h3]
    refine (semi_congr fun x z hz => ⟨?_, fun h' => ⟨X, Y, h, h'⟩⟩).trans rfl
    rintro ⟨X', Y', h', hz'⟩
    have hY : Y' = Y := rel2excl_eq hQ ((hcodQ Y').2 ⟨X', h'⟩) ((hcodQ Y).2 ⟨X, h⟩)
      ((hc' X' Y' h').2.1 z |>.2 ⟨x, hz'⟩) hz
    subst hY
    rw [s1 X' X Y' ⟨h', h⟩] at hz'
    exact hz'
  refine ⟨U, ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x x' y ⟨⟨X, Y, h, hxy⟩, ⟨X', Y', h', hxy'⟩⟩
    have hY : Y = Y' := rel2excl_eq hQ ((hcodQ Y).2 ⟨X, h⟩) ((hcodQ Y').2 ⟨X', h'⟩)
      ((hc' X Y h).2.1 y |>.2 ⟨x, hxy⟩) ((hc' X' Y' h').2.1 y |>.2 ⟨x', hxy'⟩)
    subst hY
    rw [s1 X X' Y ⟨h, h'⟩] at hxy
    exact (hc' X' Y h').1.1 x x' y hxy hxy'
  · rintro x y y' ⟨⟨X, Y, h, hxy⟩, ⟨X', Y', h', hxy'⟩⟩
    have hX : X = X' := rel2excl_eq hP (hfP X Y h) (hfP X' Y' h') (hx_fld X Y x y h hxy)
      (hx_fld X' Y' x y' h' hxy')
    subst hX
    rw [s2 X Y Y' ⟨h, h'⟩] at hxy
    exact (hc' X Y' h').1.2 x y y' hxy hxy'
  · show fld (relSigma Q) = codom U
    ext y
    rw [fld_relSigma']
    constructor
    · rintro ⟨Y, hY, hy⟩
      obtain ⟨X, h⟩ := (hcodQ Y).1 hY
      obtain ⟨x, hx⟩ := ((hc' X Y h).2.1 y).1 hy
      exact ⟨x, X, Y, h, hx⟩
    · rintro ⟨x, X, Y, h, hx⟩
      exact ⟨Y, (hcodQ Y).2 ⟨X, h⟩, ((hc' X Y h).2.1 y).2 ⟨x, hx⟩⟩
  · show P = daggerRel U ⁏ Q
    rw [hPS, daggerRel_eq_graph]
    refine semi_congr fun X Y hY => ⟨fun h => (hU X Y h).symm, fun h => ?_⟩
    obtain ⟨X₀, h₀⟩ := (hcodQ Y).1 hY
    have : X = X₀ := (h : X = U ⁏ Y).trans (hU X₀ Y h₀)
    rw [this]; exact h₀

end Helpers183

section Helpers183b

private theorem relSigma_couple (Q R : α → α → Prop) : relSigma (Q ↓ R) = Q ⤉ R := by
  funext x y; apply propext
  rw [relSigma_apply, rsum_apply]
  constructor
  · rintro (⟨S, hS, h⟩ | ⟨S, S', ⟨hx, hy⟩, ⟨rfl, rfl⟩⟩)
    · rw [fld_couple] at hS
      rcases hS with rfl | rfl
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨hx, hy⟩
  · rintro ((h | h) | ⟨hx, hy⟩)
    · exact Or.inl ⟨Q, by rw [fld_couple]; exact Or.inl rfl, h⟩
    · exact Or.inl ⟨R, by rw [fld_couple]; exact Or.inr rfl, h⟩
    · exact Or.inr ⟨Q, R, ⟨hx, hy⟩, rfl, rfl⟩

private theorem relSigma_rNull :
    relSigma (rNull : (α → α → Prop) → (α → α → Prop) → Prop) = rNull := by
  rw [relSigma_eq_rNull_iff, fld_rNull]; intro Q hQ; exact absurd hQ (Set.notMem_empty Q)

private theorem relSigma_rsum (A B : (α → α → Prop) → (α → α → Prop) → Prop) :
    relSigma (A ⤉ B) = relSigma A ⤉ relSigma B := by
  funext x y; apply propext
  rw [rsum_apply, relSigma_apply, relSigma_apply, relSigma_apply, fld_relSigma', fld_relSigma']
  constructor
  · rintro (⟨Z, hZ, h⟩ | ⟨Z, W, ⟨hx, hy⟩, (hZW | hZW) | ⟨hZ, hW⟩⟩)
    · rw [fld_rsum] at hZ
      rcases hZ with hZ | hZ
      · exact Or.inl (Or.inl (Or.inl ⟨Z, hZ, h⟩))
      · exact Or.inl (Or.inr (Or.inl ⟨Z, hZ, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨Z, W, ⟨hx, hy⟩, hZW⟩))
    · exact Or.inl (Or.inr (Or.inr ⟨Z, W, ⟨hx, hy⟩, hZW⟩))
    · exact Or.inr ⟨⟨Z, hZ, hx⟩, ⟨W, hW, hy⟩⟩
  · rintro (((⟨Z, hZ, h⟩ | ⟨Z, W, ⟨hx, hy⟩, hZW⟩) | (⟨Z, hZ, h⟩ | ⟨Z, W, ⟨hx, hy⟩, hZW⟩)) |
      ⟨⟨Z, hZ, hx⟩, ⟨W, hW, hy⟩⟩)
    · exact Or.inl ⟨Z, by rw [fld_rsum]; exact Or.inl hZ, h⟩
    · exact Or.inr ⟨Z, W, ⟨hx, hy⟩, Or.inl (Or.inl hZW)⟩
    · exact Or.inl ⟨Z, by rw [fld_rsum]; exact Or.inr hZ, h⟩
    · exact Or.inr ⟨Z, W, ⟨hx, hy⟩, Or.inl (Or.inr hZW)⟩
    · exact Or.inr ⟨Z, W, ⟨hx, hy⟩, Or.inr ⟨hZ, hW⟩⟩

private theorem relSigma_addLast {A : (α → α → Prop) → (α → α → Prop) → Prop} (hA : rEx A)
    (Y : α → α → Prop) : relSigma (A ⇸ Y) = relSigma A ⤉ Y := by
  funext x y; apply propext
  rw [rsum_apply, relSigma_apply, relSigma_apply, fld_relSigma']
  constructor
  · rintro (⟨Z, hZ, h⟩ | ⟨Z, W, ⟨hx, hy⟩, (hZW | ⟨hZ, rfl⟩)⟩)
    · obtain ⟨hZ | rfl, -⟩ := mem_fld_addLast.1 hZ
      · exact Or.inl (Or.inl (Or.inl ⟨Z, hZ, h⟩))
      · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl (Or.inr ⟨Z, W, ⟨hx, hy⟩, hZW⟩))
    · exact Or.inr ⟨⟨Z, hZ, hx⟩, hy⟩
  · rintro (((⟨Z, hZ, h⟩ | ⟨Z, W, ⟨hx, hy⟩, hZW⟩) | h) | ⟨⟨Z, hZ, hx⟩, hy⟩)
    · exact Or.inl ⟨Z, mem_fld_addLast.2 ⟨Or.inl hZ, hA⟩, h⟩
    · exact Or.inr ⟨Z, W, ⟨hx, hy⟩, Or.inl hZW⟩
    · exact Or.inl ⟨Y, mem_fld_addLast.2 ⟨Or.inr rfl, hA⟩, h⟩
    · exact Or.inr ⟨Z, Y, ⟨hx, hy⟩, Or.inr ⟨hZ, rfl⟩⟩

private theorem relSigma_addFirst {A : (α → α → Prop) → (α → α → Prop) → Prop} (hA : rEx A)
    (Y : α → α → Prop) : relSigma (Y ⇷ A) = Y ⤉ relSigma A := by
  funext x y; apply propext
  rw [rsum_apply, relSigma_apply, relSigma_apply, fld_relSigma']
  constructor
  · rintro (⟨Z, hZ, h⟩ | ⟨Z, W, ⟨hx, hy⟩, (⟨rfl, hW⟩ | hZW)⟩)
    · obtain ⟨hZ | rfl, -⟩ := mem_fld_addFirst.1 hZ
      · exact Or.inl (Or.inr (Or.inl ⟨Z, hZ, h⟩))
      · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨hx, ⟨W, hW, hy⟩⟩
    · exact Or.inl (Or.inr (Or.inr ⟨Z, W, ⟨hx, hy⟩, hZW⟩))
  · rintro ((h | (⟨Z, hZ, h⟩ | ⟨Z, W, ⟨hx, hy⟩, hZW⟩)) | ⟨hx, ⟨W, hW, hy⟩⟩)
    · exact Or.inl ⟨Y, mem_fld_addFirst.2 ⟨Or.inr rfl, hA⟩, h⟩
    · exact Or.inl ⟨Z, mem_fld_addFirst.2 ⟨Or.inl hZ, hA⟩, h⟩
    · exact Or.inr ⟨Z, W, ⟨hx, hy⟩, Or.inr hZW⟩
    · exact Or.inr ⟨Y, W, ⟨hx, hy⟩, Or.inl ⟨rfl, hW⟩⟩

/-- `Σ'Σ;P = Σ'Σ'P` (✱162·34). -/
private theorem relSigma_RelSigma
    (X : ((α → α → Prop) → (α → α → Prop) → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) →
      Prop) : relSigma (RelSigma ⁏ X) = relSigma (relSigma X) := by
  funext u v; apply propext
  rw [relSigma_apply, relSigma_apply]
  constructor
  · rintro (⟨W, hW, h⟩ | ⟨W, W', ⟨hu, hv⟩, hWW'⟩)
    · obtain ⟨A, hA, rfl⟩ := mem_fld_graph_semi.1 hW
      rcases (relSigma_apply A u v).1 h with ⟨Q, hQ, hq⟩ | ⟨Q, R, ⟨h1, h2⟩, hQR⟩
      · exact Or.inl ⟨Q, fld_relSigma'.2 ⟨A, hA, hQ⟩, hq⟩
      · exact Or.inr ⟨Q, R, ⟨h1, h2⟩, (relSigma_apply X Q R).2 (Or.inl ⟨A, hA, hQR⟩)⟩
    · obtain ⟨A, B, ⟨rfl, rfl⟩, hAB⟩ := (semi_graph_apply _ _ _ _).1 hWW'
      obtain ⟨Q, hQ, hu'⟩ := fld_relSigma'.1 hu
      obtain ⟨R, hR, hv'⟩ := fld_relSigma'.1 hv
      exact Or.inr ⟨Q, R, ⟨hu', hv'⟩, (relSigma_apply X Q R).2 (Or.inr ⟨A, B, ⟨hQ, hR⟩, hAB⟩)⟩
  · rintro (⟨Q, hQ, hq⟩ | ⟨Q, R, ⟨h1, h2⟩, hQR⟩)
    · obtain ⟨A, hA, hQ'⟩ := fld_relSigma'.1 hQ
      exact Or.inl ⟨relSigma A, mem_fld_graph_semi.2 ⟨A, hA, rfl⟩,
        (relSigma_apply A u v).2 (Or.inl ⟨Q, hQ', hq⟩)⟩
    · rcases (relSigma_apply X Q R).1 hQR with ⟨A, hA, hA'⟩ | ⟨A, B, ⟨hQ, hR⟩, hAB⟩
      · exact Or.inl ⟨relSigma A, mem_fld_graph_semi.2 ⟨A, hA, rfl⟩,
          (relSigma_apply A u v).2 (Or.inr ⟨Q, R, ⟨h1, h2⟩, hA'⟩)⟩
      · exact Or.inr ⟨relSigma A, relSigma B, ⟨fld_relSigma'.2 ⟨Q, hQ, h1⟩,
          fld_relSigma'.2 ⟨R, hR, h2⟩⟩, (semi_graph_apply _ _ _ _).2 ⟨A, B, ⟨rfl, rfl⟩, hAB⟩⟩

private theorem fld_coupleSemi_mem {P : α → α → Prop} {Q : β → β → Prop}
    {X : (α → β → Prop) → (α → β → Prop) → Prop} :
    X ∈ fld (coupleSemi P ⁏ Q) ↔ ∃ z, z ∈ fld Q ∧ X = opSemi couple P z := by
  rw [fld_coupleSemi_semi]; rfl

private theorem coupleSemi_rel2excl (P : α → α → Prop) (Q : β → β → Prop) :
    coupleSemi P ⁏ Q ∈ Rel2excl := by
  rintro X Y ⟨⟨hX, hY⟩, hne⟩
  obtain ⟨z, -, rfl⟩ := fld_coupleSemi_mem.1 hX
  obtain ⟨w, -, rfl⟩ := fld_coupleSemi_mem.1 hY
  rw [inter_null_iff]
  refine Set.disjoint_left.2 fun c hc hc' => hne ?_
  rw [fld_opSemi_couple] at hc hc'
  obtain ⟨x, -, rfl⟩ := hc
  obtain ⟨y, -, e⟩ := hc'
  rw [(couple_eq_iff.1 e).2]

private theorem smor_opSemi (P : α → α → Prop) (z : β) : smor (opSemi couple P z) P :=
  smor_graph_inj (fun x y h => (couple_eq_iff.1 h).1) P

private theorem smor_coupleSemi {P : α → α → Prop} (hP : rEx P) (Q : β → β → Prop) :
    smor (coupleSemi P ⁏ Q) Q := by
  refine smor_graph_inj (fun z w h => ?_) Q
  obtain ⟨x, y, hxy⟩ := hP
  have : opSemi couple P w (x ↓ z) (y ↓ z) := by
    rw [← h]; exact (opSemi_couple_apply P z _ _).2 ⟨x, y, ⟨rfl, rfl⟩, hxy⟩
  obtain ⟨u, v, ⟨e, -⟩, -⟩ := (opSemi_couple_apply P w _ _).1 this
  exact (couple_eq_iff.1 e).2

end Helpers183b

/-!
## [✱183] The sum of the relation-numbers of a field

*(Vol. 2, p. 496)*

> *Summary of* *183.
>
> In this number we have to define and consider the sum of the relation-numbers of the members of \(CʻP\), where \(P\) is a relation of relations. Since relational sums are not commutative, we cannot define the sum of the relation-numbers of members of a class of relations \(\lambda\): it is necessary that \(\lambda\) should be given as the field of a relation \(P\), where \(P\) determines the order in which the summation is to be effected.
>
> In order to avoid repetition, we replace \(P\) by \(\breve{\downarrow}_{.,}^{;}P\), so that if \(Q\) is a member of \(CʻP\), \(Q\) is replaced by \(\breve{\downarrow}_{.,}ʻQ\), *i.e.* by \(\downarrow Q^{;}Q\). This relation is like \(Q\), and its field has no members in common with the field of \(\downarrow R^{;}R\), unless \(Q=R\). Hence we are led to the following definition:
>
> *183·01. \(\Sigma \text{Nr}ʻP=\text{Nr}ʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}P \quad\text{Df}\)
>
> This definition is analogous to *112·01, as appears from *182·52, and the propositions of the present number are analogous to some of the propositions of *112.
>
> We have not merely
>
> …

**Lean reading.** `ΣNr'P` is `sigmaNr γ P` (`= nr γ (relSigma (sepRel P))`, the type `γ` explicit); `Σ;P` is
`RelSigma ⁏ P`, `↓̆.,†;P` is `daggerRel (opDiag (opSemi couple)) ⁏ P`, `P↓.,;Q` is
`coupleSemi P ⁏ Q`, `Q × P` is `Q ×ᵣ P`. `P smor̄ Q ∩ Rl'smor` is `smorbar P Q ∩ rl smor`;
`C'P, C'Q ∈ Cl'Nr'S` is `fld P ∈ cl (nr α S) ∧ fld Q ∈ cl (nr α S)`. `Mult ax` is a hypothesis
where PM has it, at the type of the correlators it is used to select (the correlators of the
members of the two fields; it is not used in the Lean proofs, `Classical.choice` doing its work,
Basic §4). In ✱183·32·33·331 the `ΣNr` in arithmetical positions have their own adequate types
(IIT).

**Status.** proved (all propositions; ✱183·01 definition; ✱183·32·33·331·42·43 proved (reading), see their docstrings)
-/

/-- ✱183·01 (Df). \(\Sigma \text{Nr}ʻP=\text{Nr}ʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}P \quad\text{Df}\) -/
theorem pm183_01 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    sigmaNr γ P = nr γ (relSigma (opDiag (opSemi couple) ⁏ P)) := rfl

/-- ✱183·1. \(\vdash .\Sigma \text{Nr}ʻP=\text{Nr}ʻ\Sigma ʻ\breve{\downarrow}_{.,}^{;}P \quad[(*183·01)]\) -/
theorem pm183_1 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    sigmaNr γ P = nr γ (relSigma (opDiag (opSemi couple) ⁏ P)) := rfl

/-- ✱183·11. \(\vdash :P \,\,\text{smor}\, \,\text{smor}\, Q.\supset .\Sigma \text{Nr}ʻP=\Sigma \text{Nr}ʻQ\) -/
theorem pm183_11 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor P Q → sigmaNr γ P = sigmaNr γ Q := fun h =>
  nr_eq_nr_of_smor (smor_relSigma_of_smorsmor (pm182_34 h))

/-- ✱183·12. \(\vdash :P \,\,\text{smor}\, \,\text{smor}\,\breve{\downarrow}_{.,}^{;}Q.\supset .\text{Nr}ʻ\Sigma ʻP=\Sigma \text{Nr}ʻQ \quad[*164·151.*183·1]\) -/
theorem pm183_12 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor P (sepRel Q) → nr γ (relSigma P) = sigmaNr γ Q := fun h =>
  nr_eq_nr_of_smor (smor_relSigma_of_smorsmor h)

/-- ✱183·13. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\text{Nr}ʻ\Sigma ʻP=\Sigma \text{Nr}ʻP \quad[*182·27.*183·12]\) -/
theorem pm183_13 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl → nr γ (relSigma P) = sigmaNr γ P := fun h => pm183_12 (pm182_27 h)

/-- ✱183·14. \(\vdash .\Sigma \text{Nr}ʻP=\Sigma \text{Nr}ʻ\breve{\downarrow}_{.,}^{;}P\) -/
theorem pm183_14 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    sigmaNr γ P = sigmaNr γ (sepRel P) := pm183_13 pm182_16

/-- ✱183·15. \(\vdash :\breve{\downarrow}_{.,}^{;}P\,\text{smor}\, \,\text{smor}\,\breve{\downarrow}_{.,}^{;}Q.\supset .\Sigma \text{Nr}ʻP=\Sigma \text{Nr}ʻQ \quad[*183·11·14]\) -/
theorem pm183_15 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor (sepRel P) (sepRel Q) → sigmaNr γ P = sigmaNr γ Q := fun h => by
  rw [pm183_14 (P := P), pm183_14 (P := Q)]; exact pm183_11 h

/-- ✱183·2. \(\vdash :\Sigma \text{Nr}ʻP=0_{r}.\equiv .\Sigma ʻP=\dot{\Lambda}\) -/
theorem pm183_2 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    sigmaNr γ P = zero_r ↔ relSigma P = rNull := by
  rw [sigmaNr, nr_eq_zero_r_iff, relSigma_sep_eq_rNull_iff]

/-- ✱183·22. \(\vdash \colon\ldotp \text{Mult ax} . \supset : \exists ! (\breve{\downarrow}_{.,}^{;}P) \overline{\,\text{smor}\,} (\breve{\downarrow}_{.,}^{;}Q) \cap \text{Rl}ʻ\,\text{smor}\, . \supset . \Sigma \text{Nr}ʻP = \Sigma \text{Nr}ʻQ\)

`Mult ax` at the type of the correlators of members of `C'↓̆.,;P` with members of `C'↓̆.,;Q`. -/
theorem pm183_22 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop}
    (_hm : MultAx ((α → (α → α → Prop) → Prop) → (β → (β → β → Prop) → Prop) → Prop)) :
    (smorbar (sepRel P) (sepRel Q) ∩ rl smor).Nonempty → sigmaNr γ P = sigmaNr γ Q := by
  rintro ⟨S, hS, hSs⟩
  exact pm183_15 (smorsmor_of_corr pm182_16 pm182_16 hS hSs)

/-- ✱183·23. \(\vdash \colon\ldotp \text{Mult ax} . \supset : P, Q \in \text{Rel}^{2}\text{excl} . \exists ! P \overline{\,\text{smor}\,} Q \cap \text{Rl}ʻ\,\text{smor}\, . \supset . \Sigma \text{Nr}ʻP = \Sigma \text{Nr}ʻQ \quad[*164·46 . *183·13]\)

`Mult ax` at the type of the correlators of members of `C'P` with members of `C'Q`. -/
theorem pm183_23 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} (_hm : MultAx (α → β → Prop)) :
    (P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ (smorbar P Q ∩ rl smor).Nonempty →
      sigmaNr γ P = sigmaNr γ Q := by
  rintro ⟨⟨hP, hQ⟩, S, hS, hSs⟩
  exact pm183_11 (smorsmor_of_corr hP hQ hS hSs)

/-- ✱183·231. \(\vdash : P \in \text{Nr}ʻR . CʻP \subset \text{Nr}ʻS . \equiv . \breve{\downarrow}_{.,}^{;}P \in \text{Nr}ʻR . Cʻ\breve{\downarrow}_{.,}^{;}P \subset \text{Nr}ʻS\)

`Nr'R`, `Nr'S` are in the types required by the memberships (typical ambiguity). -/
theorem pm183_231 {ζ ξ : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {R : ζ → ζ → Prop} {S : ξ → ξ → Prop} :
    P ∈ nr (α → α → Prop) R ∧ fld P ⊆ nr α S ↔
      sepRel P ∈ nr ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) R ∧
        fld (sepRel P) ⊆ nr (α → (α → α → Prop) → Prop) S := by
  have h1 : smor (sepRel P) P := pm182_162.2
  refine and_congr ⟨fun h => smor_trans h1 h, fun h => smor_trans (smor_symm h1) h⟩ ⟨?_, ?_⟩
  · intro h Y hY
    obtain ⟨Q, hQ, rfl⟩ := mem_fld_sepRel.1 hY
    exact smor_trans (smor_sep Q) (h hQ)
  · intro h Q hQ
    exact smor_trans (smor_symm (smor_sep Q)) (h (mem_fld_sepRel.2 ⟨Q, hQ, rfl⟩))

/-- ✱183·24. \(\vdash \colon\ldotp \text{Mult ax} . \supset : P, Q \in \text{Nr}ʻR . CʻP, CʻQ \in \text{Cl}ʻ\text{Nr}ʻS . \supset . \Sigma \text{Nr}ʻP = \Sigma \text{Nr}ʻQ\)

`Mult ax` at the type of the correlators of members of `C'↓̆.,;P` with members of `C'↓̆.,;Q`. -/
theorem pm183_24 {ζ ξ : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop}
    {R : ζ → ζ → Prop} {S : ξ → ξ → Prop}
    (_hm : MultAx ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop)) :
    (P ∈ nr (α → α → Prop) R ∧ Q ∈ nr (α → α → Prop) R) ∧
      (fld P ∈ cl (nr α S) ∧ fld Q ∈ cl (nr α S)) → sigmaNr γ P = sigmaNr γ Q := by
  rintro ⟨⟨hP, hQ⟩, hPS, hQS⟩
  obtain ⟨hP', hPS'⟩ := pm183_231.1 ⟨hP, hPS⟩
  obtain ⟨hQ', hQS'⟩ := pm183_231.1 ⟨hQ, hQS⟩
  obtain ⟨T, hT⟩ := smor_trans hP' (smor_symm hQ')
  refine pm183_15 (smorsmor_of_corr pm182_16 pm182_16 hT fun X Y hXY => ?_)
  obtain ⟨⟨hT1, hc⟩, hTe⟩ := hT
  have hY : Y ∈ fld (sepRel Q) := by rw [hc]; exact ⟨X, hXY⟩
  have hX : X ∈ fld (sepRel P) := by
    rw [hTe]; exact (mem_fld_semi fun z hz => by rw [hc] at hz; exact hz).2 ⟨Y, hY, hXY⟩
  exact smor_trans (hPS' hX) (smor_symm (hQS' hY))

/-- ✱183·25. \(\vdash . \Sigma \text{Nr}ʻP \downarrow_{.,} ^{;}Q = \text{Nr}ʻ(Q \times P)\) -/
theorem pm183_25 {P : α → α → Prop} {Q : β → β → Prop} :
    sigmaNr γ (coupleSemi P ⁏ Q) = nr γ (Q ×ᵣ P) :=
  (pm183_13 (coupleSemi_rel2excl P Q)).symm

/-- ✱183·26. \(\vdash \colon\ldotp \text{Mult ax} . \supset : P \in \text{Nr}ʻR . CʻP \subset \text{Nr}ʻS . \supset . \Sigma \text{Nr}ʻP = \text{Nr}ʻ(R \times S)\)

`Mult ax` at the type of the correlators of members of `C'↓̆.,;P` with members of
`C'↓̆.,;(S↓.,;R)`. -/
theorem pm183_26 {ζ ξ : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {R : ζ → ζ → Prop} {S : ξ → ξ → Prop}
    (_hm : MultAx ((α → (α → α → Prop) → Prop) →
      ((ξ → ζ → Prop) → ((ξ → ζ → Prop) → (ξ → ζ → Prop) → Prop) → Prop) → Prop)) :
    P ∈ nr (α → α → Prop) R ∧ fld P ⊆ nr α S → sigmaNr γ P = nr γ (R ×ᵣ S) := by
  rintro ⟨hP, hPS⟩
  by_cases hS : rEx S
  · obtain ⟨hP', hPS'⟩ := pm183_231.1 ⟨hP, hPS⟩
    have hX : coupleSemi S ⁏ R ∈ nr _ R := smor_coupleSemi hS R
    have hXS : fld (coupleSemi S ⁏ R) ⊆ nr (ξ → ζ → Prop) S := fun X hX' => by
      obtain ⟨z, -, rfl⟩ := fld_coupleSemi_mem.1 hX'
      exact smor_opSemi S z
    obtain ⟨hX', hXS'⟩ := pm183_231.1 ⟨hX, hXS⟩
    obtain ⟨T, hT⟩ := smor_trans hP' (smor_symm hX')
    rw [← pm183_25]
    refine pm183_15 (smorsmor_of_corr pm182_16 pm182_16 hT fun A B hAB => ?_)
    obtain ⟨⟨hT1, hc⟩, hTe⟩ := hT
    have hB : B ∈ fld (sepRel (coupleSemi S ⁏ R)) := by rw [hc]; exact ⟨A, hAB⟩
    have hA : A ∈ fld (sepRel P) := by
      rw [hTe]; exact (mem_fld_semi fun z hz => by rw [hc] at hz; exact hz).2 ⟨B, hB, hAB⟩
    exact smor_trans (hPS' hA) (smor_symm (hXS' hB))
  · have hS0 : S = rNull := by by_contra h; exact hS (ne_rNull_iff.1 h)
    subst hS0
    have e1 : sigmaNr γ P = zero_r := pm183_2.2 (relSigma_eq_rNull_iff.2 fun Q hQ =>
      smor_rNull_iff'.1 (hPS hQ))
    have e2 : R ×ᵣ (rNull : ξ → ξ → Prop) = rNull := by
      show relSigma _ = _
      refine relSigma_eq_rNull_iff.2 fun X hX => ?_
      obtain ⟨z, -, rfl⟩ := fld_coupleSemi_mem.1 hX
      exact smor_rNull_iff'.1 (smor_opSemi rNull z)
    rw [e1, e2, ← zero_r_eq_nr]

/-- ✱183·3. \(\vdash .\Sigma \text{Nr}ʻ\dot{\Lambda} =0_{r} \quad[*183·2.*162·4]\) -/
theorem pm183_3 : sigmaNr γ (rNull : (α → α → Prop) → (α → α → Prop) → Prop) = zero_r :=
  pm183_2.2 relSigma_rNull

/-- ✱183·301. \(\vdash .\Sigma \text{Nr}ʻ(\dot{\Lambda} \downarrow \dot{\Lambda} )=0_{r} \quad[*183·2.*162·41]\) -/
theorem pm183_301 :
    sigmaNr γ ((rNull : α → α → Prop) ↓ (rNull : α → α → Prop)) = zero_r :=
  pm183_2.2 (by rw [relSigma_couple, rsum_rNull])

/-- ✱183·302. \(\vdash .\Sigma \text{Nr}ʻ(P\downarrow P)=\text{Nr}ʻ(CʻP\uparrow CʻP)\) -/
theorem pm183_302 {P : α → α → Prop} : sigmaNr γ (P ↓ P) = nr γ (cross (fld P) (fld P)) := by
  have hex : P ↓ P ∈ Rel2excl := by
    rintro X Y ⟨⟨hX, hY⟩, hne⟩
    rw [fld_couple_self] at hX hY
    exact absurd (hX.trans hY.symm) hne
  rw [← pm183_13 hex, relSigma_couple]
  congr 1
  funext x y; apply propext
  rw [rsum_apply]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨⟨y, Or.inl h⟩, ⟨x, Or.inr h⟩⟩
    · exact ⟨⟨y, Or.inl h⟩, ⟨x, Or.inr h⟩⟩
    · exact h
  · intro h; exact Or.inr h

/-- ✱183·31. \(\vdash :P\neq Q.\supset .\Sigma \text{Nr}ʻ(P\downarrow Q)=\text{Nr}ʻP\dot{+} \text{Nr}ʻQ\) -/
theorem pm183_31 {P Q : α → α → Prop} :
    P ≠ Q → sigmaNr γ (P ↓ Q) = (n₀r P ∔ n₀r Q : Set (γ → γ → Prop)) := by
  intro hPQ
  rw [sigmaNr, sepRel_eq, graph_semi_couple, relSigma_couple, ← pm180_32]
  · exact pm180_31 ⟨smor_sep P, smor_sep Q⟩
  · rw [inter_null_iff]
    refine Set.disjoint_left.2 fun c hc hc' => hPQ ?_
    obtain ⟨x, -, rfl⟩ := mem_fld_sep.1 hc
    obtain ⟨y, -, e⟩ := mem_fld_sep.1 hc'
    exact (couple_eq_iff.1 e).2

/-- ✱183·32. \(\vdash :CʻP\cap CʻQ=\Lambda .\supset .\Sigma \text{Nr}ʻ(P\unicode{x2909}Q)=\Sigma \text{Nr}ʻP\dot{+} \Sigma \text{Nr}ʻQ\)

The `ΣNr'P`, `ΣNr'Q` in arithmetical positions have their own types, adequate (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components ΣNr'P, ΣNr'Q are adequate -/
theorem pm183_32 {W₁ W₂ : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop}
    (h₁ : AdeqSigmaNr W₁ P) (h₂ : AdeqSigmaNr W₂ Q) :
    fld P ∩ fld Q = Λ → sigmaNr γ (P ⤉ Q) =
      (sigmaNr W₁ P ∔ sigmaNr W₂ Q : Set (γ → γ → Prop)) := by
  intro hPQ
  obtain ⟨X₁, hX₁⟩ := h₁.sigmaNr_nonempty P
  obtain ⟨X₂, hX₂⟩ := h₂.sigmaNr_nonempty Q
  rw [sigmaNr, sepRel_eq, graph_semi_rsum, relSigma_rsum, ← sepRel_eq, ← sepRel_eq,
    show sigmaNr W₁ P = n₀r X₁ from nr_eq_n₀r_of_mem hX₁,
    show sigmaNr W₂ Q = n₀r X₂ from nr_eq_n₀r_of_mem hX₂, ← pm180_32]
  · exact (pm180_31 ⟨(hX₁ : smor X₁ _), (hX₂ : smor X₂ _)⟩).symm
  · rw [inter_null_iff] at hPQ ⊢
    refine Set.disjoint_left.2 fun c hc hc' => ?_
    obtain ⟨R, x, ⟨hR, -⟩, rfl⟩ := mem_fld_sigma_sep.1 hc
    obtain ⟨R', y, ⟨hR', -⟩, e⟩ := mem_fld_sigma_sep.1 hc'
    rw [(couple_eq_iff.1 e).2] at hR
    exact Set.disjoint_left.1 hPQ hR hR'

/-- ✱183·33. \(\vdash :\dot{\exists} !P.Z{\sim}\in CʻP.\supset .\Sigma \text{Nr}ʻ(P\unicode{x21f8} Z)=\Sigma \text{Nr}ʻP\dot{+} \text{Nr}ʻZ\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component ΣNr'P is adequate -/
theorem pm183_33 {W : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    (h : AdeqSigmaNr W P) :
    rEx P ∧ Z ∉ fld P → sigmaNr γ (P ⇸ Z) = (sigmaNr W P ∔ n₀r Z : Set (γ → γ → Prop)) := by
  rintro ⟨hP, hZ⟩
  obtain ⟨X, hX⟩ := h.sigmaNr_nonempty P
  rw [sigmaNr, sepRel_eq, graph_semi_addLast, relSigma_addLast (rEx_graph.2 hP), ← sepRel_eq,
    show sigmaNr W P = n₀r X from nr_eq_n₀r_of_mem hX, ← pm180_32]
  · exact pm180_31 ⟨smor_symm (hX : smor X _), smor_sep Z⟩
  · rw [inter_null_iff]
    refine Set.disjoint_left.2 fun c hc hc' => ?_
    obtain ⟨R, x, ⟨hR, -⟩, rfl⟩ := mem_fld_sigma_sep.1 hc
    obtain ⟨y, -, e⟩ := mem_fld_sep.1 hc'
    exact hZ ((couple_eq_iff.1 e).2 ▸ hR)

/-- ✱183·331. \[\begin{align}&\vdash :\dot{\exists} !P.Z{\sim}\in CʻP.\supset .\Sigma \text{Nr}ʻ(Z\unicode{x21f7}P) = \text{Nr}ʻZ\dot{+} \Sigma \text{Nr}ʻP\\ &[\text{Proof as in *183·33}]\end{align}\]

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component ΣNr'P is adequate -/
theorem pm183_331 {W : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    (h : AdeqSigmaNr W P) :
    rEx P ∧ Z ∉ fld P → sigmaNr γ (Z ⇷ P) = (n₀r Z ∔ sigmaNr W P : Set (γ → γ → Prop)) := by
  rintro ⟨hP, hZ⟩
  obtain ⟨X, hX⟩ := h.sigmaNr_nonempty P
  rw [sigmaNr, sepRel_eq, graph_semi_addFirst, relSigma_addFirst (rEx_graph.2 hP), ← sepRel_eq,
    show sigmaNr W P = n₀r X from nr_eq_n₀r_of_mem hX, ← pm180_32]
  · exact pm180_31 ⟨smor_sep Z, smor_symm (hX : smor X _)⟩
  · rw [inter_null_iff]
    refine Set.disjoint_left.2 fun c hc' hc => ?_
    obtain ⟨R, x, ⟨hR, -⟩, rfl⟩ := mem_fld_sigma_sep.1 hc
    obtain ⟨y, -, e⟩ := mem_fld_sep.1 hc'
    exact hZ ((couple_eq_iff.1 e).2 ▸ hR)

/-- ✱183·42. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\breve{\downarrow_{,,}}\dagger^{{} ;}P\in \text{Rel}^{3}\text{arithm}\)

**Status.** proved (reading): transcription error: the e-text prints `↓̆,,†;P` (two commas) for
`↓̆.,†;P`, as the Dem. (✱182·162, ✱162·35) and the Summary (✱183·43) show -/
theorem pm183_42
    {P : ((α → α → Prop) → (α → α → Prop) → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) →
      Prop} :
    P ∈ Rel2excl → daggerRel (opDiag (opSemi couple)) ⁏ P ∈ Rel3arithm := by
  intro hP
  refine ⟨?_, ?_⟩
  · rintro A B ⟨⟨hA, hB⟩, hne⟩
    obtain ⟨X, hX, rfl⟩ := mem_fld_graph_semi.1 hA
    obtain ⟨Y, hY, rfl⟩ := mem_fld_graph_semi.1 hB
    have hXY : X ≠ Y := fun e => hne (by rw [e])
    have hd := (mem_Rel2excl.1 hP) X Y ⟨⟨hX, hY⟩, hXY⟩
    rw [inter_null_iff] at hd ⊢
    refine Set.disjoint_left.2 fun c hc hc' => ?_
    obtain ⟨Q, hQ, rfl⟩ := mem_fld_sepRel.1 hc
    obtain ⟨R, hR, e⟩ := mem_fld_sepRel.1 hc'
    rw [← sep_inj e] at hR
    exact Set.disjoint_left.1 hd hQ hR
  · rw [relSigma_dagger (T := opDiag (opSemi couple)) fun _ _ z _ => ⟨_, rfl⟩]
    exact pm182_16

/-- ✱183·43. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\Sigma \text{Nr}ʻ\Sigma ^{;}\breve{\downarrow_{,,}}\dagger^{{} ;}P = \Sigma \text{Nr}ʻ\Sigma ʻP\)

**Status.** proved (reading): transcription error: the e-text prints `↓̆,,†;P` (two commas) for
`↓̆.,†;P`, as the Dem. and the Summary show -/
theorem pm183_43
    {P : ((α → α → Prop) → (α → α → Prop) → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) →
      Prop} :
    P ∈ Rel2excl → sigmaNr γ (RelSigma ⁏ daggerRel (opDiag (opSemi couple)) ⁏ P) =
      sigmaNr γ (relSigma P) := by
  intro hP
  obtain ⟨h1, h2⟩ := pm183_42 hP
  have hexcl : RelSigma ⁏ daggerRel (opDiag (opSemi couple)) ⁏ P ∈ Rel2excl := by
    rintro A B ⟨⟨hA, hB⟩, hne⟩
    obtain ⟨X, hX, rfl⟩ := mem_fld_graph_semi.1 hA
    obtain ⟨Y, hY, rfl⟩ := mem_fld_graph_semi.1 hB
    have hXY : X ≠ Y := fun e => hne (by rw [e])
    rw [inter_null_iff]
    refine Set.disjoint_left.2 fun c hc hc' => ?_
    obtain ⟨Q, hQ, hc1⟩ := fld_relSigma'.1 hc
    obtain ⟨R, hR, hc2⟩ := fld_relSigma'.1 hc'
    have hQR : Q ≠ R := by
      intro e; subst e
      have := (mem_Rel2excl.1 h1) X Y ⟨⟨hX, hY⟩, hXY⟩
      rw [inter_null_iff] at this
      exact Set.disjoint_left.1 this hQ hR
    have := (mem_Rel2excl.1 h2) Q R ⟨⟨fld_relSigma'.2 ⟨X, hX, hQ⟩, fld_relSigma'.2 ⟨Y, hY, hR⟩⟩, hQR⟩
    rw [inter_null_iff] at this
    exact Set.disjoint_left.1 this hc1 hc2
  rw [← pm183_13 hexcl, relSigma_RelSigma, relSigma_dagger (T := opDiag (opSemi couple)) fun _ _ z _ => ⟨_, rfl⟩]
  rfl

/-- ✱183·5. \(\vdash :C\upharpoonright CʻP\in 1\rightarrow 1.\supset .Cʻʻ\Sigma \text{Nr}ʻP = \Sigma \text{Nc}ʻCʻʻCʻP\) -/
theorem pm183_5 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    C ↾ fld P ∈ arrow one one → C ʻʻ sigmaNr γ P = sigmaNc γ (C ʻʻ fld P) := fun h => by
  rw [sigmaNr, C_img_nr]; exact pm182_54 h


section Helpers184

private theorem rtimes_lex (Q : β → β → Prop) (P : α → α → Prop) (u v : α → β → Prop) :
    (Q ×ᵣ P) u v ↔ ∃ x z y w, (u = x ↓ z ∧ v = y ↓ w) ∧
      ((z = w ∧ z ∈ fld Q ∧ P x y) ∨ (Q z w ∧ x ∈ fld P ∧ y ∈ fld P)) := by
  rw [rtimes_apply]
  constructor
  · rintro (⟨z, hz, x, y, ⟨rfl, rfl⟩, h⟩ | ⟨z, w, hzw, x, y, ⟨hx, hy⟩, rfl, rfl⟩)
    · exact ⟨x, z, y, z, ⟨rfl, rfl⟩, Or.inl ⟨rfl, hz, h⟩⟩
    · exact ⟨x, z, y, w, ⟨rfl, rfl⟩, Or.inr ⟨hzw, hx, hy⟩⟩
  · rintro ⟨x, z, y, w, ⟨rfl, rfl⟩, ⟨rfl, hz, h⟩ | ⟨hzw, hx, hy⟩⟩
    · exact Or.inl ⟨z, hz, x, y, ⟨rfl, rfl⟩, h⟩
    · exact Or.inr ⟨z, w, hzw, x, y, ⟨hx, hy⟩, rfl, rfl⟩

private theorem mem_fld_rtimes {Q : β → β → Prop} {P : α → α → Prop} {u : α → β → Prop} :
    u ∈ fld (Q ×ᵣ P) ↔ ∃ x z, (x ∈ fld P ∧ z ∈ fld Q) ∧ u = x ↓ z := by
  show u ∈ fld (relSigma _) ↔ _
  rw [fld_relSigma']
  constructor
  · rintro ⟨X, hX, hu⟩
    obtain ⟨z, hz, rfl⟩ := fld_coupleSemi_mem.1 hX
    rw [fld_opSemi_couple] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨x, z, ⟨hx, hz⟩, rfl⟩
  · rintro ⟨x, z, ⟨hx, hz⟩, rfl⟩
    exact ⟨_, fld_coupleSemi_mem.2 ⟨z, hz, rfl⟩, by rw [fld_opSemi_couple]; exact ⟨x, hx, rfl⟩⟩

private theorem rEx_rtimes {Q : β → β → Prop} {P : α → α → Prop} :
    rEx (Q ×ᵣ P) ↔ rEx Q ∧ rEx P := by
  constructor
  · rintro ⟨u, v, h⟩
    obtain ⟨x, z, y, w, -, ⟨-, hz, hxy⟩ | ⟨hzw, hx, -⟩⟩ := (rtimes_lex Q P u v).1 h
    · exact ⟨rEx_iff_fld.2 ⟨z, hz⟩, x, y, hxy⟩
    · exact ⟨⟨z, w, hzw⟩, rEx_iff_fld.2 ⟨x, hx⟩⟩
  · rintro ⟨⟨z, w, hzw⟩, ⟨x, y, hxy⟩⟩
    exact ⟨x ↓ z, x ↓ w, (rtimes_lex Q P _ _).2
      ⟨x, z, x, w, ⟨rfl, rfl⟩, Or.inr ⟨hzw, ⟨y, Or.inl hxy⟩, ⟨y, Or.inl hxy⟩⟩⟩⟩

private theorem rtimes_mono {Q Q' : β → β → Prop} {P P' : α → α → Prop} (hQ : Q ⪽ Q')
    (hP : P ⪽ P') : Q ×ᵣ P ⪽ Q' ×ᵣ P' := by
  intro u v h
  obtain ⟨x, z, y, w, e, ⟨hzw, hz, hxy⟩ | ⟨hzw, hx, hy⟩⟩ := (rtimes_lex Q P u v).1 h
  · exact (rtimes_lex Q' P' u v).2 ⟨x, z, y, w, e, Or.inl ⟨hzw, fld_mono hQ hz, hP _ _ hxy⟩⟩
  · exact (rtimes_lex Q' P' u v).2 ⟨x, z, y, w, e, Or.inr ⟨hQ _ _ hzw, fld_mono hP hx,
      fld_mono hP hy⟩⟩

/-- `Q smor Q' . P smor P' . ⊃ . Q × P smor Q' × P'` (✱166·23). -/
private theorem smor_rtimes {Q : β → β → Prop} {Q' : δ → δ → Prop} {P : α → α → Prop}
    {P' : γ → γ → Prop} (hQ : smor Q Q') (hP : smor P P') : smor (Q ×ᵣ P) (Q' ×ᵣ P') := by
  obtain ⟨T₁, ⟨a₁, b₁⟩, hc₁, rfl⟩ := smor_corr hQ
  obtain ⟨T₂, ⟨a₂, b₂⟩, hc₂, rfl⟩ := smor_corr hP
  have f₁ : ∀ z, z ∈ fld (T₁ ⁏ Q') ↔ ∃ z', z' ∈ fld Q' ∧ T₁ z z' :=
    fun z => mem_fld_semi fun z' hz' => (hc₁ z').1 hz'
  have f₂ : ∀ x, x ∈ fld (T₂ ⁏ P') ↔ ∃ x', x' ∈ fld P' ∧ T₂ x x' :=
    fun x => mem_fld_semi fun x' hx' => (hc₂ x').1 hx'
  let U : (α → β → Prop) → (γ → δ → Prop) → Prop :=
    fun u a => ∃ x z x' z', (u = x ↓ z ∧ a = x' ↓ z') ∧ T₂ x x' ∧ T₁ z z'
  have e : (T₁ ⁏ Q') ×ᵣ (T₂ ⁏ P') = U ⁏ (Q' ×ᵣ P') := by
    funext u v; apply propext
    rw [rtimes_lex, semi_apply]
    constructor
    · rintro ⟨x, z, y, w, ⟨rfl, rfl⟩, ⟨rfl, hz, hxy⟩ | ⟨hzw, hx, hy⟩⟩
      · obtain ⟨z', hz', hzz'⟩ := (f₁ z).1 hz
        obtain ⟨x', y', ⟨hx, hy⟩, hxy'⟩ := (semi_apply _ _ _ _).1 hxy
        exact ⟨x' ↓ z', y' ↓ z', ⟨⟨x, z, x', z', ⟨rfl, rfl⟩, hx, hzz'⟩,
          ⟨y, z, y', z', ⟨rfl, rfl⟩, hy, hzz'⟩⟩,
          (rtimes_lex _ _ _ _).2 ⟨x', z', y', z', ⟨rfl, rfl⟩, Or.inl ⟨rfl, hz', hxy'⟩⟩⟩
      · obtain ⟨z', w', ⟨hz, hw⟩, hzw'⟩ := (semi_apply _ _ _ _).1 hzw
        obtain ⟨x', hx', hxx'⟩ := (f₂ x).1 hx
        obtain ⟨y', hy', hyy'⟩ := (f₂ y).1 hy
        exact ⟨x' ↓ z', y' ↓ w', ⟨⟨x, z, x', z', ⟨rfl, rfl⟩, hxx', hz⟩,
          ⟨y, w, y', w', ⟨rfl, rfl⟩, hyy', hw⟩⟩,
          (rtimes_lex _ _ _ _).2 ⟨x', z', y', w', ⟨rfl, rfl⟩, Or.inr ⟨hzw', hx', hy'⟩⟩⟩
    · rintro ⟨a, b, ⟨⟨x, z, x', z', ⟨rfl, rfl⟩, hx, hz⟩, ⟨y, w, y', w', ⟨rfl, rfl⟩, hy, hw⟩⟩, h⟩
      obtain ⟨x₀, z₀, y₀, w₀, ⟨e1, e2⟩, h'⟩ := (rtimes_lex _ _ _ _).1 h
      obtain ⟨ex, ez⟩ := couple_eq_iff.1 e1
      obtain ⟨ey, ew⟩ := couple_eq_iff.1 e2
      subst ex ez ey ew
      rcases h' with ⟨hzw, hz', hxy'⟩ | ⟨hzw', hx', hy'⟩
      · subst hzw
        have : z = w := a₁ z w z' hz hw
        subst this
        exact ⟨x, z, y, z, ⟨rfl, rfl⟩, Or.inl ⟨rfl, (f₁ z).2 ⟨z', hz', hz⟩,
          (semi_apply _ _ _ _).2 ⟨x', y', ⟨hx, hy⟩, hxy'⟩⟩⟩
      · exact ⟨x, z, y, w, ⟨rfl, rfl⟩, Or.inr ⟨(semi_apply _ _ _ _).2 ⟨z', w', ⟨hz, hw⟩, hzw'⟩,
          (f₂ x).2 ⟨x', hx', hx⟩, (f₂ y).2 ⟨y', hy', hy⟩⟩⟩
  rw [e]
  refine smor_semi_of ?_ ?_ ?_
  · rintro u v a - ⟨x, z, x', z', ⟨rfl, rfl⟩, hx, hz⟩ ⟨y, w, y', w', ⟨rfl, e'⟩, hy, hw⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e'
    rw [a₂ x y x' hx hy, a₁ z w z' hz hw]
  · rintro u a b - - ⟨x, z, x', z', ⟨rfl, rfl⟩, hx, hz⟩ ⟨y, w, y', w', ⟨e', rfl⟩, hy, hw⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e'
    rw [b₂ x x' y' hx hy, b₁ z z' w' hz hw]
  · intro a ha
    obtain ⟨x', z', ⟨hx', hz'⟩, rfl⟩ := mem_fld_rtimes.1 ha
    obtain ⟨x, hx⟩ := (hc₂ x').1 hx'
    obtain ⟨z, hz⟩ := (hc₁ z').1 hz'
    exact ⟨x ↓ z, x, z, x', z', ⟨rfl, rfl⟩, hx, hz⟩

private theorem rtimes_rsum (P Q : α → α → Prop) (R : β → β → Prop) :
    (P ⤉ Q) ×ᵣ R = P ×ᵣ R ⤉ Q ×ᵣ R := by
  show relSigma (coupleSemi R ⁏ (P ⤉ Q)) = relSigma _ ⤉ relSigma _
  rw [show coupleSemi R = graph (opSemi couple R) from rfl, graph_semi_rsum, relSigma_rsum]

private theorem rtimes_addLast {Q : α → α → Prop} (hQ : rEx Q) (y : α) (P : β → β → Prop) :
    (Q ⇸ y) ×ᵣ P = Q ×ᵣ P ⤉ opSemi couple P y := by
  show relSigma (coupleSemi P ⁏ (Q ⇸ y)) = relSigma _ ⤉ _
  rw [show coupleSemi P = graph (opSemi couple P) from rfl, graph_semi_addLast,
    relSigma_addLast (rEx_graph.2 hQ)]

private theorem rtimes_addFirst {Q : α → α → Prop} (hQ : rEx Q) (y : α) (P : β → β → Prop) :
    (y ⇷ Q) ×ᵣ P = opSemi couple P y ⤉ Q ×ᵣ P := by
  show relSigma (coupleSemi P ⁏ (y ⇷ Q)) = _ ⤉ relSigma _
  rw [show coupleSemi P = graph (opSemi couple P) from rfl, graph_semi_addFirst,
    relSigma_addFirst (rEx_graph.2 hQ)]

private theorem rtimes_couple (a b : α) (P : β → β → Prop) :
    (a ↓ b) ×ᵣ P = opSemi couple P a ⤉ opSemi couple P b := by
  show relSigma (coupleSemi P ⁏ (a ↓ b)) = _
  rw [show coupleSemi P = graph (opSemi couple P) from rfl, graph_semi_couple, relSigma_couple]

private theorem disj_rtimes {Q Q' : α → α → Prop} (h : Disjoint (fld Q) (fld Q'))
    (P : β → β → Prop) : Disjoint (fld (Q ×ᵣ P)) (fld (Q' ×ᵣ P)) := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  obtain ⟨x, z, ⟨-, hz⟩, rfl⟩ := mem_fld_rtimes.1 hu
  obtain ⟨x', z', ⟨-, hz'⟩, e⟩ := mem_fld_rtimes.1 hu'
  rw [(couple_eq_iff.1 e).2] at hz
  exact Set.disjoint_left.1 h hz hz'

private theorem disj_rtimes_opSemi {Q : α → α → Prop} {y : α} (hy : y ∉ fld Q)
    (P : β → β → Prop) : Disjoint (fld (Q ×ᵣ P)) (fld (opSemi couple P y)) := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  obtain ⟨x, z, ⟨-, hz⟩, rfl⟩ := mem_fld_rtimes.1 hu
  rw [fld_opSemi_couple] at hu'
  obtain ⟨x', -, e⟩ := hu'
  rw [(couple_eq_iff.1 e).2] at hz
  exact hy hz

private theorem disj_opSemi {a b : α} (hab : a ≠ b) (P : β → β → Prop) :
    Disjoint (fld (opSemi couple P a)) (fld (opSemi couple P b)) := by
  refine Set.disjoint_left.2 fun u hu hu' => ?_
  rw [fld_opSemi_couple] at hu hu'
  obtain ⟨x, -, rfl⟩ := hu
  obtain ⟨x', -, e⟩ := hu'
  exact hab (couple_eq_iff.1 e).2

/-- `Σ'P × R = Σ'(×R);P` (✱166·44). -/
private theorem rtimes_relSigma (P : (α → α → Prop) → (α → α → Prop) → Prop) (R : β → β → Prop) :
    relSigma P ×ᵣ R = relSigma (opR rtimes R ⁏ P) := by
  have e1 : (opR rtimes R : _ → (α → α → Prop) → Prop) = RelSigma ⨾ daggerRel (coupleSemi R) :=
    (graph_relProd_graph _ _).symm
  rw [e1, ← semi_semi, relSigma_RelSigma,
    relSigma_dagger (T := coupleSemi R) fun _ _ z _ => ⟨_, rfl⟩]
  rfl

/-- `P ∈ Rel² excl . ⊃ . (×R);P ∈ Rel² excl` (✱166·3). -/
private theorem rtimes_rel2excl {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : P ∈ Rel2excl)
    (R : β → β → Prop) : opR rtimes R ⁏ P ∈ Rel2excl := by
  rintro A B ⟨⟨hA, hB⟩, hne⟩
  obtain ⟨X, hX, rfl⟩ := mem_fld_graph_semi.1 hA
  obtain ⟨Y, hY, rfl⟩ := mem_fld_graph_semi.1 hB
  have hXY : X ≠ Y := fun e => hne (by rw [e])
  have := (mem_Rel2excl.1 hP) X Y ⟨⟨hX, hY⟩, hXY⟩
  rw [inter_null_iff] at this ⊢
  exact disj_rtimes this R

/-! #### The associative law `(P × Q) × R smor P × (Q × R)` (✱166·42) -/

private def assocN {α β γ : Type*} (P : α → α → Prop) (Q : β → β → Prop) (R : γ → γ → Prop)
    (r : γ) (x : β) (p : α) (r' : γ) (x' : β) (p' : α) : Prop :=
  (p = p' ∧ p ∈ fld P ∧ ((x = x' ∧ x ∈ fld Q ∧ R r r') ∨ (Q x x' ∧ r ∈ fld R ∧ r' ∈ fld R))) ∨
    (P p p' ∧ (x ∈ fld Q ∧ x' ∈ fld Q) ∧ (r ∈ fld R ∧ r' ∈ fld R))

private theorem assoc_left {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop}
    {u v : γ → (β → α → Prop) → Prop} :
    (P ×ᵣ Q ×ᵣ R) u v ↔ ∃ r x p r' x' p', (u = r ↓ (x ↓ p) ∧ v = r' ↓ (x' ↓ p')) ∧
      assocN P Q R r x p r' x' p' := by
  rw [rtimes_lex]
  constructor
  · rintro ⟨r, c, r', c', ⟨rfl, rfl⟩, ⟨rfl, hc, hR⟩ | ⟨hcc', hr, hr'⟩⟩
    · obtain ⟨x, p, ⟨hx, hp⟩, rfl⟩ := mem_fld_rtimes.1 hc
      exact ⟨r, x, p, r', x, p, ⟨rfl, rfl⟩, Or.inl ⟨rfl, hp, Or.inl ⟨rfl, hx, hR⟩⟩⟩
    · obtain ⟨x, p, x', p', ⟨rfl, rfl⟩, ⟨rfl, hp, hxx'⟩ | ⟨hpp', hx, hx'⟩⟩ :=
        (rtimes_lex _ _ _ _).1 hcc'
      · exact ⟨r, x, p, r', x', p, ⟨rfl, rfl⟩, Or.inl ⟨rfl, hp, Or.inr ⟨hxx', hr, hr'⟩⟩⟩
      · exact ⟨r, x, p, r', x', p', ⟨rfl, rfl⟩, Or.inr ⟨hpp', ⟨hx, hx'⟩, ⟨hr, hr'⟩⟩⟩
  · rintro ⟨r, x, p, r', x', p', ⟨rfl, rfl⟩, ⟨rfl, hp, ⟨rfl, hx, hR⟩ | ⟨hxx', hr, hr'⟩⟩ |
      ⟨hpp', ⟨hx, hx'⟩, ⟨hr, hr'⟩⟩⟩
    · exact ⟨r, x ↓ p, r', x ↓ p, ⟨rfl, rfl⟩, Or.inl ⟨rfl, mem_fld_rtimes.2 ⟨x, p, ⟨hx, hp⟩, rfl⟩,
        hR⟩⟩
    · exact ⟨r, x ↓ p, r', x' ↓ p, ⟨rfl, rfl⟩, Or.inr ⟨(rtimes_lex _ _ _ _).2
        ⟨x, p, x', p, ⟨rfl, rfl⟩, Or.inl ⟨rfl, hp, hxx'⟩⟩, hr, hr'⟩⟩
    · exact ⟨r, x ↓ p, r', x' ↓ p', ⟨rfl, rfl⟩, Or.inr ⟨(rtimes_lex _ _ _ _).2
        ⟨x, p, x', p', ⟨rfl, rfl⟩, Or.inr ⟨hpp', hx, hx'⟩⟩, hr, hr'⟩⟩

private theorem assoc_right {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop}
    {a b : (γ → β → Prop) → α → Prop} :
    (P ×ᵣ (Q ×ᵣ R)) a b ↔ ∃ r x p r' x' p', (a = (r ↓ x) ↓ p ∧ b = (r' ↓ x') ↓ p') ∧
      assocN P Q R r x p r' x' p' := by
  rw [rtimes_lex]
  constructor
  · rintro ⟨d, p, d', p', ⟨rfl, rfl⟩, ⟨rfl, hp, hdd'⟩ | ⟨hpp', hd, hd'⟩⟩
    · obtain ⟨r, x, r', x', ⟨rfl, rfl⟩, ⟨rfl, hx, hR⟩ | ⟨hxx', hr, hr'⟩⟩ :=
        (rtimes_lex _ _ _ _).1 hdd'
      · exact ⟨r, x, p, r', x, p, ⟨rfl, rfl⟩, Or.inl ⟨rfl, hp, Or.inl ⟨rfl, hx, hR⟩⟩⟩
      · exact ⟨r, x, p, r', x', p, ⟨rfl, rfl⟩, Or.inl ⟨rfl, hp, Or.inr ⟨hxx', hr, hr'⟩⟩⟩
    · obtain ⟨r, x, ⟨hr, hx⟩, rfl⟩ := mem_fld_rtimes.1 hd
      obtain ⟨r', x', ⟨hr', hx'⟩, rfl⟩ := mem_fld_rtimes.1 hd'
      exact ⟨r, x, p, r', x', p', ⟨rfl, rfl⟩, Or.inr ⟨hpp', ⟨hx, hx'⟩, ⟨hr, hr'⟩⟩⟩
  · rintro ⟨r, x, p, r', x', p', ⟨rfl, rfl⟩, ⟨rfl, hp, ⟨rfl, hx, hR⟩ | ⟨hxx', hr, hr'⟩⟩ |
      ⟨hpp', ⟨hx, hx'⟩, ⟨hr, hr'⟩⟩⟩
    · exact ⟨r ↓ x, p, r' ↓ x, p, ⟨rfl, rfl⟩, Or.inl ⟨rfl, hp, (rtimes_lex _ _ _ _).2
        ⟨r, x, r', x, ⟨rfl, rfl⟩, Or.inl ⟨rfl, hx, hR⟩⟩⟩⟩
    · exact ⟨r ↓ x, p, r' ↓ x', p, ⟨rfl, rfl⟩, Or.inl ⟨rfl, hp, (rtimes_lex _ _ _ _).2
        ⟨r, x, r', x', ⟨rfl, rfl⟩, Or.inr ⟨hxx', hr, hr'⟩⟩⟩⟩
    · exact ⟨r ↓ x, p, r' ↓ x', p', ⟨rfl, rfl⟩, Or.inr ⟨hpp',
        mem_fld_rtimes.2 ⟨r, x, ⟨hr, hx⟩, rfl⟩, mem_fld_rtimes.2 ⟨r', x', ⟨hr', hx'⟩, rfl⟩⟩⟩

private theorem smor_rtimes_assoc (P : α → α → Prop) (Q : β → β → Prop) (R : γ → γ → Prop) :
    smor (P ×ᵣ Q ×ᵣ R) (P ×ᵣ (Q ×ᵣ R)) := by
  let U : (γ → (β → α → Prop) → Prop) → ((γ → β → Prop) → α → Prop) → Prop :=
    fun u a => ∃ r x p, u = r ↓ (x ↓ p) ∧ a = (r ↓ x) ↓ p
  have e : P ×ᵣ Q ×ᵣ R = U ⁏ (P ×ᵣ (Q ×ᵣ R)) := by
    funext u v; apply propext
    rw [assoc_left, semi_apply]
    constructor
    · rintro ⟨r, x, p, r', x', p', ⟨rfl, rfl⟩, h⟩
      exact ⟨(r ↓ x) ↓ p, (r' ↓ x') ↓ p', ⟨⟨r, x, p, rfl, rfl⟩, ⟨r', x', p', rfl, rfl⟩⟩,
        assoc_right.2 ⟨r, x, p, r', x', p', ⟨rfl, rfl⟩, h⟩⟩
    · rintro ⟨a, b, ⟨⟨r, x, p, rfl, rfl⟩, ⟨r', x', p', rfl, rfl⟩⟩, h⟩
      obtain ⟨r₀, x₀, p₀, r₀', x₀', p₀', ⟨e1, e2⟩, h'⟩ := assoc_right.1 h
      obtain ⟨e1a, rfl⟩ := couple_eq_iff.1 e1
      obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e1a
      obtain ⟨e2a, rfl⟩ := couple_eq_iff.1 e2
      obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e2a
      exact ⟨r, x, p, r', x', p', ⟨rfl, rfl⟩, h'⟩
  rw [e]
  refine smor_semi_of ?_ ?_ ?_
  · rintro u v a - ⟨r, x, p, rfl, rfl⟩ ⟨r', x', p', rfl, e'⟩
    obtain ⟨e1, rfl⟩ := couple_eq_iff.1 e'
    obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e1
    rfl
  · rintro u a b - - ⟨r, x, p, rfl, rfl⟩ ⟨r', x', p', e', rfl⟩
    obtain ⟨rfl, e1⟩ := couple_eq_iff.1 e'
    obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e1
    rfl
  · intro a ha
    obtain ⟨d, p, ⟨hd, -⟩, rfl⟩ := mem_fld_rtimes.1 ha
    obtain ⟨r, x, -, rfl⟩ := mem_fld_rtimes.1 hd
    exact ⟨r ↓ (x ↓ p), r, x, p, rfl, rfl⟩

/-! #### `μ ×̇ ν` -/

private theorem n₀r_nrMul_n₀r (P : α → α → Prop) (Q : β → β → Prop) :
    (n₀r P ⨰ n₀r Q : Set (γ → γ → Prop)) = nr γ (P ×ᵣ Q) := by
  ext Z
  constructor
  · rintro ⟨P', Q', ⟨hP, hQ⟩, h⟩
    exact smor_trans h (smor_rtimes (n₀r_eq_n₀r_iff.1 hP.symm) (n₀r_eq_n₀r_iff.1 hQ.symm))
  · intro h; exact ⟨P, Q, ⟨rfl, rfl⟩, h⟩

private theorem nrMul_of {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} {P : α → α → Prop}
    {Q : β → β → Prop} (hμ : μ = n₀r P) (hν : ν = n₀r Q) :
    (μ ⨰ ν : Set (γ → γ → Prop)) = nr γ (P ×ᵣ Q) := by
  subst hμ hν; exact n₀r_nrMul_n₀r P Q

private theorem nrMul_eq_empty_of_left {μ : Set (α → α → Prop)} (h : ∀ P, μ ≠ n₀r P)
    (ν : Set (β → β → Prop)) : (μ ⨰ ν : Set (γ → γ → Prop)) = ∅ := by
  ext Z; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨P, Q, ⟨hP, -⟩, -⟩; exact h P hP

private theorem nrMul_eq_empty_of_right (μ : Set (α → α → Prop)) {ν : Set (β → β → Prop)}
    (h : ∀ Q, ν ≠ n₀r Q) : (μ ⨰ ν : Set (γ → γ → Prop)) = ∅ := by
  ext Z; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨P, Q, ⟨-, hQ⟩, -⟩; exact h Q hQ

private theorem empty_nrMul (ν : Set (β → β → Prop)) :
    ((∅ : Set (α → α → Prop)) ⨰ ν : Set (γ → γ → Prop)) = ∅ :=
  nrMul_eq_empty_of_left (fun P h => n₀r_ne_empty P h.symm) ν

private theorem nrMul_empty (μ : Set (α → α → Prop)) :
    (μ ⨰ (∅ : Set (β → β → Prop)) : Set (γ → γ → Prop)) = ∅ :=
  nrMul_eq_empty_of_right μ (fun P h => n₀r_ne_empty P h.symm)

private theorem rtimes_sub_rV (P : α → α → Prop) (Q : β → β → Prop) :
    P ×ᵣ Q ⪽ (rV : α → α → Prop) ×ᵣ (rV : β → β → Prop) :=
  rtimes_mono (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ => ⟨rfl, rfl⟩)

private theorem AdeqNrMul.eq_n₀r {W : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    (h : AdeqNrMul W μ ν) (P : α → α → Prop) (Q : β → β → Prop) :
    ∃ X : W → W → Prop, smor X (P ×ᵣ Q) ∧ (n₀r P ⨰ n₀r Q : Set (W → W → Prop)) = n₀r X := by
  have h' : (nr W ((rV : α → α → Prop) ×ᵣ (rV : β → β → Prop))).Nonempty := by
    have := h; unfold AdeqNrMul at this; rwa [n₀r_nrMul_n₀r] at this
  obtain ⟨X, hX⟩ := nr_nonempty_of_rsub h' (rtimes_sub_rV P Q)
  exact ⟨X, hX, (n₀r_nrMul_n₀r P Q).trans (nr_eq_n₀r_of_mem hX)⟩

/-! #### Cardinal products -/

private noncomputable def clsTimesEquiv (B : Set β) (A : Set α) : ↥(B ×ₐ A) ≃ A × B :=
  (Equiv.ofBijective (fun p : A × B => (⟨(p.1 : α) ↓ (p.2 : β),
    couple_mem_clsTimes.2 ⟨p.1.2, p.2.2⟩⟩ : ↥(B ×ₐ A)))
    ⟨fun p q h => by
      have := couple_eq_iff.1 (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2),
    fun ⟨u, hu⟩ => by
      obtain ⟨S, ⟨y, hy, hS⟩, hu'⟩ := hu
      rw [hS] at hu'
      obtain ⟨x, hx, rfl⟩ := hu'
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩⟩).symm

private theorem sm_clsTimes {A : Set α} {B : Set β} {A' : Set γ} {B' : Set δ} (hA : sm A A')
    (hB : sm B B') : sm (B ×ₐ A) (B' ×ₐ A') := by
  obtain ⟨eA⟩ := sm_iff_nonempty_equiv.1 hA
  obtain ⟨eB⟩ := sm_iff_nonempty_equiv.1 hB
  exact sm_iff_nonempty_equiv.2 ⟨(clsTimesEquiv B A).trans ((eA.prodCongr eB).trans
    (clsTimesEquiv B' A').symm)⟩

private theorem n₀c_cardMul_n₀c (A : Set α) (B : Set β) :
    (n₀c A ×ᶜ n₀c B : Set (Set γ)) = nc γ (A ×ₐ B) := by
  ext ξ
  constructor
  · rintro ⟨A', B', ⟨hA, hB⟩, h⟩
    have hA' : sm A A' := mem_n₀c.1 (hA ▸ self_mem_n₀c A)
    have hB' : sm B B' := mem_n₀c.1 (hB ▸ self_mem_n₀c B)
    exact sm_trans h (sm_clsTimes (sm_symm hB') (sm_symm hA'))
  · intro h
    exact ⟨A, B, ⟨rfl, rfl⟩, h⟩

private theorem fld_rtimes_eq (Q : β → β → Prop) (P : α → α → Prop) :
    fld (Q ×ᵣ P) = fld Q ×ₐ fld P := by
  ext u
  rw [mem_fld_rtimes]
  constructor
  · rintro ⟨x, z, ⟨hx, hz⟩, rfl⟩; exact couple_mem_clsTimes.2 ⟨hx, hz⟩
  · intro hu
    obtain ⟨S, ⟨z, hz, hS⟩, hu'⟩ := hu
    rw [hS] at hu'
    obtain ⟨x, hx, rfl⟩ := hu'
    exact ⟨x, z, ⟨hx, hz⟩, rfl⟩

end Helpers184

/-!
## [✱184] The product of two relation-numbers

*(Vol. 2, p. 501)*

> *Summary of* *184.
>
> The propositions of this number are for the most part analogous to those of the propositions of *113 which are concerned with \(\mu \times _{c} \nu\). Those of *113 which are concerned with \(\alpha \times \beta\) have their analogues in *166. We put
>
> *184·01. \(\mu \dot{\times} \nu =\hat{R} \{(\exists P,Q).\mu =\text{N}_{0}\text{r}ʻP.\nu =\text{N}_{0}\text{r}ʻQ.R\,\text{smor}\,(P\times Q)\} \quad\text{Df}\)
>
> *184·02. \(\text{Nr}ʻP\dot{\times} \nu =\text{N}_{0}\text{r}ʻP\dot{\times} \nu \quad\text{Df}\)
>
> *184·03. \(\mu \dot{\times} \text{Nr}ʻQ=\mu \dot{\times} \text{N}_{0}\text{r}ʻQ \quad\text{Df}\)
>
> We prove that \(\mu \dot{\times} \nu\) is only zero when one of its factors is zero (*184·16); we prove the associative law (*184·31), and the distributive law in the forms
>
> *184·33. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\Sigma \text{Nr}ʻP\dot{\times} \text{Nr}ʻR=\Sigma \text{Nr}ʻ(\times R)^{;}P\)
>
> *184·35. \(\vdash .(\nu \dot{+} \varpi )\dot{\times} \mu =(\nu \dot{\times} \mu )\dot{+} (\varpi \dot{\times} \mu )\)
>
> …

**Lean reading.** `μ ×̇ ν` is `μ ⨰ ν` with its actual type implicit, `P × Q` is `P ×ᵣ Q` (the couples `x ↓ z`
with `x ∈ C'Q`, `z ∈ C'P`, ordered first by `P`), `(×R);P` is `opR rtimes R ⁏ P`; an argument
`Nr'P` of `×̇` is `n₀r P` (✱184·02·03). The inner products and sums of ✱184·3–·35, `2_r`, `ΣNr'P`,
`ν +̇ 1̇` and `1̇ +̇ ν` in arithmetical positions have their own adequate types (IIT); `μ, ν ∈ NR`
have independent types, and the `NR` of a conclusion is in the type of the members (✱184·16) or
`NR (Set γ)` (✱184·15), as in ✱180. `C''μ ×_c C''ν` is `C ʻʻ μ ×ᶜ C ʻʻ ν`. `Mult ax` is a
hypothesis where PM has it, at the type of the correlators it selects (✱183·26).

**Status.** proved (all propositions; ✱184·01·02·03·32 definition; ✱184·13·15·16·3·31·33·34·35·4·41·42 proved (reading), see their docstrings)
-/

/-- ✱184·01 (Df). \(\mu \dot{\times} \nu =\hat{R} \{(\exists P,Q).\mu =\text{N}_{0}\text{r}ʻP.\nu =\text{N}_{0}\text{r}ʻQ.R\,\text{smor}\,(P\times Q)\} \quad\text{Df}\) -/
theorem pm184_01 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} : (μ ⨰ ν : Set (γ → γ → Prop)) =
    {R | ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (P ×ᵣ Q)} :=
  rfl

/-- ✱184·02 (Df). \(\text{Nr}ʻP\dot{\times} \nu =\text{N}_{0}\text{r}ʻP\dot{\times} \nu \quad\text{Df}\)

A rule of translation (normal adjustment), as ✱180·03. -/
theorem pm184_02 {P : α → α → Prop} {ν : Set (β → β → Prop)} :
    (n₀r P ⨰ ν : Set (γ → γ → Prop)) = n₀r P ⨰ ν := rfl

/-- ✱184·03 (Df). \(\mu \dot{\times} \text{Nr}ʻQ=\mu \dot{\times} \text{N}_{0}\text{r}ʻQ \quad\text{Df}\)

A rule of translation (normal adjustment), as ✱180·03. -/
theorem pm184_03 {μ : Set (α → α → Prop)} {Q : β → β → Prop} :
    (μ ⨰ n₀r Q : Set (γ → γ → Prop)) = μ ⨰ n₀r Q := rfl

/-- ✱184·1. \[\begin{align}&\vdash :R\in \mu \dot{\times} \nu .\equiv .(\exists P,Q).\mu =\text{N}_{0}\text{r}ʻP.\nu =\text{N}_{0}\text{r}ʻQ.R\,\text{smor}\,(P\times Q)\\ &[(*184·01)]\end{align}\] -/
theorem pm184_1 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} {R : γ → γ → Prop} :
    R ∈ (μ ⨰ ν : Set (γ → γ → Prop)) ↔
      ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (P ×ᵣ Q) :=
  Iff.rfl

/-- ✱184·11. \(\vdash :\exists !\mu \dot{\times} \nu .\supset .\mu ,\nu \in \text{N}_{0}\text{R}.\exists !\mu .\exists !\nu\) -/
theorem pm184_11 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    (μ ⨰ ν : Set (γ → γ → Prop)).Nonempty → ((μ ∈ N₀R ∧ ν ∈ N₀R) ∧ μ.Nonempty) ∧ ν.Nonempty := by
  rintro ⟨R, P, Q, ⟨rfl, rfl⟩, -⟩
  exact ⟨⟨⟨⟨P, rfl⟩, ⟨Q, rfl⟩⟩, n₀r_nonempty P⟩, n₀r_nonempty Q⟩

/-- ✱184·111. \(\vdash :{\sim}(\mu ,\nu \in \text{N}_{0}\text{R}).\supset .\mu \dot{\times} \nu =\Lambda\) -/
theorem pm184_111 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    ¬(μ ∈ N₀R ∧ ν ∈ N₀R) → (μ ⨰ ν : Set (γ → γ → Prop)) = Λ := by
  intro h
  rw [Null_eq_empty]
  by_contra hne
  exact h (pm184_11 (Set.nonempty_iff_ne_empty.2 hne)).1.1

/-- ✱184·12. \(\vdash \colon\ldotp \mu ,\nu \in \text{NR}.\supset :R\in \mu \dot{\times} \nu .\equiv .(\exists P,Q).P\in \mu .Q\in \nu .R\,\text{smor}\,(P\times Q)\) -/
theorem pm184_12 {β₁ β₂ : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    {R : γ → γ → Prop} : μ ∈ NR β₁ ∧ ν ∈ NR β₂ →
      (R ∈ (μ ⨰ ν : Set (γ → γ → Prop)) ↔ ∃ P Q, (P ∈ μ ∧ Q ∈ ν) ∧ smor R (P ×ᵣ Q)) := by
  rintro ⟨hμ, hν⟩
  rcases NR_cases hμ with rfl | ⟨P', rfl⟩
  · rw [empty_nrMul]; simp
  rcases NR_cases hν with rfl | ⟨Q', rfl⟩
  · rw [nrMul_empty]; simp
  constructor
  · rintro ⟨P, Q, ⟨hP, hQ⟩, h⟩
    exact ⟨P, Q, ⟨hP ▸ self_mem_n₀r P, hQ ▸ self_mem_n₀r Q⟩, h⟩
  · rintro ⟨P, Q, ⟨hP, hQ⟩, h⟩
    exact ⟨P, Q, ⟨n₀r_eq_n₀r_iff.2 (smor_symm (mem_n₀r.1 hP)),
      n₀r_eq_n₀r_iff.2 (smor_symm (mem_n₀r.1 hQ))⟩, h⟩

/-- ✱184·13. \[\begin{align}\vdash .\text{Nr}ʻP\dot{\times} \text{Nr}ʻQ=\text{N}_{0}\text{r}ʻP\dot{\times} \text{Nr}ʻQ&=\text{Nr}ʻP\dot{\times} \text{N}_{0}\text{r}ʻQ\\ &=\text{N}_{0}\text{r}ʻP\dot{\times} \text{N}_{0}\text{r}ʻQ=\text{Nr}ʻ(P\times Q)\end{align}\]

**Status.** proved (reading): by the Dfs ✱184·02·03 the arguments Nr'P, Nr'Q of ×̇ are read
N₀r'P, N₀r'Q, so the first three equations are identities of readings; all sides in one type -/
theorem pm184_13 {P : α → α → Prop} {Q : β → β → Prop} :
    (((n₀r P ⨰ n₀r Q : Set (γ → γ → Prop)) = n₀r P ⨰ n₀r Q ∧
      (n₀r P ⨰ n₀r Q : Set (γ → γ → Prop)) = n₀r P ⨰ n₀r Q) ∧
      (n₀r P ⨰ n₀r Q : Set (γ → γ → Prop)) = n₀r P ⨰ n₀r Q) ∧
      (n₀r P ⨰ n₀r Q : Set (γ → γ → Prop)) = nr γ (P ×ᵣ Q) :=
  ⟨⟨⟨rfl, rfl⟩, rfl⟩, n₀r_nrMul_n₀r P Q⟩

/-- ✱184·14. \(\vdash :P\,\,\text{smor}\,\,R.Q\,\text{smor}\,S.\supset .\text{Nr}ʻP\dot{\times} \text{Nr}ʻQ=\text{Nr}ʻR\dot{\times} \text{Nr}ʻS\) -/
theorem pm184_14 {P : α → α → Prop} {Q : β → β → Prop} {R : γ → γ → Prop} {S : δ → δ → Prop}
    {ε : Type*} : smor P R ∧ smor Q S → (n₀r P ⨰ n₀r Q : Set (ε → ε → Prop)) = n₀r R ⨰ n₀r S := by
  rintro ⟨h1, h2⟩
  rw [n₀r_nrMul_n₀r, n₀r_nrMul_n₀r]
  exact nr_eq_nr_of_smor (smor_rtimes h1 h2)

/-- ✱184·15. \(\vdash .\mu \dot{\times} \nu \in \text{NR}\)

**Status.** proved (reading): the ambiguous `NR` is taken as `NR (Set γ)`, as in ✱180·42 -/
theorem pm184_15 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    (μ ⨰ ν : Set (γ → γ → Prop)) ∈ NR (Set γ) := by
  rcases Set.eq_empty_or_nonempty (μ ⨰ ν : Set (γ → γ → Prop)) with h | ⟨Z, P, Q, ⟨rfl, rfl⟩, h⟩
  · rw [h]; exact empty_mem_NR_set
  · rw [n₀r_nrMul_n₀r, nr_eq_n₀r_of_mem h]; exact n₀r_mem_NR_set Z

/-- ✱184·16. \(\vdash \colon\ldotp \mu \dot{\times} \nu =0_{r}.\equiv :\mu ,\nu \in \text{NR}-\iota ʻ\Lambda :\mu =0_{r}.\lor.\nu =0_{r}\)

**Status.** proved (reading): the ambiguous `NR` is taken in the types of the members of `μ` and
`ν` (as ✱180·4) -/
theorem pm184_16 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    (μ ⨰ ν : Set (γ → γ → Prop)) = zero_r ↔
      (μ ∈ NR α \ ι Λ ∧ ν ∈ NR β \ ι Λ) ∧ (μ = zero_r ∨ ν = zero_r) := by
  constructor
  · intro h
    have hz : (rNull : γ → γ → Prop) ∈ (μ ⨰ ν : Set (γ → γ → Prop)) := by rw [h]; rfl
    obtain ⟨P, Q, ⟨rfl, rfl⟩, -⟩ := hz
    rw [n₀r_nrMul_n₀r, nr_eq_zero_r_iff] at h
    refine ⟨⟨⟨n₀r_mem_NR P, ?_⟩, ⟨n₀r_mem_NR Q, ?_⟩⟩, ?_⟩
    · rw [mem_unitCls, Null_eq_empty]; exact n₀r_ne_empty P
    · rw [mem_unitCls, Null_eq_empty]; exact n₀r_ne_empty Q
    · by_contra hc
      push Not at hc
      have hP : rEx P := ne_rNull_iff.1 fun e => hc.1 (by rw [e]; exact zero_r_eq_n₀r.symm)
      have hQ : rEx Q := ne_rNull_iff.1 fun e => hc.2 (by rw [e]; exact zero_r_eq_n₀r.symm)
      exact ne_rNull_iff.2 (rEx_rtimes.2 ⟨hP, hQ⟩) h
  · rintro ⟨⟨⟨hμ, hμ0⟩, ⟨hν, hν0⟩⟩, h⟩
    rcases NR_cases hμ with rfl | ⟨P, rfl⟩
    · exact absurd (by rw [mem_unitCls, Null_eq_empty]) hμ0
    rcases NR_cases hν with rfl | ⟨Q, rfl⟩
    · exact absurd (by rw [mem_unitCls, Null_eq_empty]) hν0
    rw [n₀r_nrMul_n₀r, nr_eq_zero_r_iff]
    rcases h with h | h
    · rw [zero_r_eq_n₀r, n₀r_eq_n₀r_iff, smor_rNull_iff'] at h
      subst h
      by_contra hne
      exact (rEx_rtimes.1 (ne_rNull_iff.1 hne)).1 |> fun ⟨x, y, h⟩ => rNull_apply x y h
    · rw [zero_r_eq_n₀r, n₀r_eq_n₀r_iff, smor_rNull_iff'] at h
      subst h
      by_contra hne
      exact (rEx_rtimes.1 (ne_rNull_iff.1 hne)).2 |> fun ⟨x, y, h⟩ => rNull_apply x y h

/-- ✱184·2. \[\begin{align}&\vdash \colon\ldotp \text{Mult ax}.\supset :P\in \text{Nr}ʻR.CʻP\subset \text{Nr}ʻS.\supset .\Sigma \text{Nr}ʻP =\text{Nr}ʻR\dot{\times} \text{Nr}ʻS\\ &[*183·26.*184·13]\end{align}\]

`Mult ax` as in ✱183·26. -/
theorem pm184_2 {ζ ξ : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {R : ζ → ζ → Prop} {S : ξ → ξ → Prop}
    (hm : MultAx ((α → (α → α → Prop) → Prop) →
      ((ξ → ζ → Prop) → ((ξ → ζ → Prop) → (ξ → ζ → Prop) → Prop) → Prop) → Prop)) :
    P ∈ nr (α → α → Prop) R ∧ fld P ⊆ nr α S →
      sigmaNr γ P = (n₀r R ⨰ n₀r S : Set (γ → γ → Prop)) := fun h => by
  rw [pm183_26 hm h, n₀r_nrMul_n₀r]

/-- ✱184·21. \(\vdash \colon\ldotp \text{Mult ax}.\supset :\mu ,\nu \in \text{NR}.\nu \neq \Lambda .P \in \mu .CʻP\subset \nu .\supset .\Sigma \text{Nr}ʻP =\mu \dot{\times} \nu\)

`μ, ν ∈ NR` have independent `NR` types; `Mult ax` as in ✱183·26 (with `R` the relation `P`). -/
theorem pm184_21 {β₁ β₂ : Type*} {μ : Set ((α → α → Prop) → (α → α → Prop) → Prop)}
    {ν : Set (α → α → Prop)} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    (hm : MultAx ((α → (α → α → Prop) → Prop) →
      ((α → (α → α → Prop) → Prop) → ((α → (α → α → Prop) → Prop) →
        (α → (α → α → Prop) → Prop) → Prop) → Prop) → Prop)) :
    (((μ ∈ NR β₁ ∧ ν ∈ NR β₂) ∧ ν ≠ Λ) ∧ P ∈ μ) ∧ fld P ⊆ ν →
      sigmaNr γ P = (μ ⨰ ν : Set (γ → γ → Prop)) := by
  rintro ⟨⟨⟨⟨hμ, hν⟩, hν0⟩, hP⟩, hPν⟩
  rcases NR_cases hμ with rfl | ⟨P', rfl⟩
  · exact absurd hP (Set.notMem_empty P)
  rcases NR_cases hν with rfl | ⟨S, rfl⟩
  · exact absurd Null_eq_empty.symm hν0
  have e : n₀r P' = n₀r P := n₀r_eq_n₀r_iff.2 (smor_symm (mem_n₀r.1 hP))
  rw [e]
  refine pm184_2 hm ⟨smor_refl P, fun Q hQ => ?_⟩
  have := hPν hQ
  rw [n₀r_eq_nr] at this
  exact this

/-- ✱184·3. \(\vdash .(\text{Nr}ʻP\dot{\times} \text{Nr}ʻQ)\dot{\times} \text{Nr}ʻR=\text{Nr}ʻP\dot{\times} (\text{Nr}ʻQ\dot{\times} \text{Nr}ʻR)=\text{Nr}ʻ(P\times Q\times R)\)

The inner products are arithmetical components with their own adequate types (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components Nr'P ×̇ Nr'Q and Nr'Q ×̇ Nr'R are adequate -/
theorem pm184_3 {W₁ W₂ : Type*} {P : α → α → Prop} {Q : β → β → Prop} {R : δ → δ → Prop}
    (h₁ : AdeqNrMul W₁ (n₀r P) (n₀r Q)) (h₂ : AdeqNrMul W₂ (n₀r Q) (n₀r R)) :
    ((n₀r P ⨰ n₀r Q : Set (W₁ → W₁ → Prop)) ⨰ n₀r R : Set (γ → γ → Prop)) =
        n₀r P ⨰ (n₀r Q ⨰ n₀r R : Set (W₂ → W₂ → Prop)) ∧
      (n₀r P ⨰ (n₀r Q ⨰ n₀r R : Set (W₂ → W₂ → Prop)) : Set (γ → γ → Prop)) =
        nr γ (P ×ᵣ Q ×ᵣ R) := by
  obtain ⟨X₁, hX₁, e₁⟩ := h₁.eq_n₀r P Q
  obtain ⟨X₂, hX₂, e₂⟩ := h₂.eq_n₀r Q R
  rw [e₁, e₂, n₀r_nrMul_n₀r, n₀r_nrMul_n₀r]
  have a1 := nr_eq_nr_of_smor (γ := γ) (smor_rtimes hX₁ (smor_refl R))
  have a2 := nr_eq_nr_of_smor (γ := γ) (smor_rtimes (smor_refl P) hX₂)
  have a3 := nr_eq_nr_of_smor (γ := γ) (smor_rtimes_assoc P Q R)
  exact ⟨a1.trans (a3.trans a2.symm), a2.trans a3.symm⟩

/-- ✱184·31. \(\vdash .(\mu \dot{\times} \nu )\dot{\times} \varpi =\mu \dot{\times} (\nu \dot{\times} \varpi )\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components μ ×̇ ν and ν ×̇ ϖ are adequate -/
theorem pm184_31 {α₁ α₂ α₃ W₁ W₂ : Type*} {μ : Set (α₁ → α₁ → Prop)} {ν : Set (α₂ → α₂ → Prop)}
    {ϖ : Set (α₃ → α₃ → Prop)} (h₁ : AdeqNrMul W₁ μ ν) (h₂ : AdeqNrMul W₂ ν ϖ) :
    ((μ ⨰ ν : Set (W₁ → W₁ → Prop)) ⨰ ϖ : Set (γ → γ → Prop)) =
      μ ⨰ (ν ⨰ ϖ : Set (W₂ → W₂ → Prop)) := by
  by_cases hμ : ∃ P, μ = n₀r P
  · by_cases hν : ∃ Q, ν = n₀r Q
    · by_cases hϖ : ∃ R, ϖ = n₀r R
      · obtain ⟨P, rfl⟩ := hμ; obtain ⟨Q, rfl⟩ := hν; obtain ⟨R, rfl⟩ := hϖ
        exact (pm184_3 h₁ h₂).1
      · push Not at hϖ
        rw [nrMul_eq_empty_of_right _ hϖ, nrMul_eq_empty_of_right (ν := ϖ) _ hϖ, nrMul_empty]
    · push Not at hν
      rw [nrMul_eq_empty_of_right (ν := ν) _ hν, nrMul_eq_empty_of_left (μ := ν) hν,
        empty_nrMul, nrMul_empty]
  · push Not at hμ
    rw [nrMul_eq_empty_of_left (μ := μ) hμ, nrMul_eq_empty_of_left (μ := μ) hμ, empty_nrMul]

/-- ✱184·32 (Df). \(\mu \dot{\times} \nu \dot{\times} \varpi =(\mu \dot{\times} \nu )\dot{\times} \varpi \quad\text{Df}\) -/
theorem pm184_32 {W : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    {ϖ : Set (δ → δ → Prop)} : ((μ ⨰ ν : Set (W → W → Prop)) ⨰ ϖ : Set (γ → γ → Prop)) =
      ((μ ⨰ ν : Set (W → W → Prop)) ⨰ ϖ : Set (γ → γ → Prop)) := rfl

/-- ✱184·33. \(\vdash :P\in \text{Rel}^{2}\text{excl}.\supset .\Sigma \text{Nr}ʻP\dot{\times} \text{Nr}ʻR=\Sigma \text{Nr}ʻ(\times R)^{;}P\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component ΣNr'P is adequate -/
theorem pm184_33 {W : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {R : β → β → Prop}
    (h : AdeqSigmaNr W P) : P ∈ Rel2excl →
      (sigmaNr W P ⨰ n₀r R : Set (γ → γ → Prop)) = sigmaNr γ (opR rtimes R ⁏ P) := by
  intro hP
  obtain ⟨X, hX⟩ := h.sigmaNr_nonempty P
  have hX' : smor X (relSigma P) := by
    have := pm183_13 (γ := W) hP
    rw [← this] at hX; exact hX
  rw [show sigmaNr W P = n₀r X from nr_eq_n₀r_of_mem hX, n₀r_nrMul_n₀r,
    ← pm183_13 (rtimes_rel2excl hP R), ← rtimes_relSigma]
  exact nr_eq_nr_of_smor (smor_rtimes hX' (smor_refl R))

/-- ✱184·34. \(\vdash .(\text{Nr}ʻP\dot{+} \text{Nr}ʻQ)\dot{\times} \text{Nr}ʻR=(\text{Nr}ʻP\dot{\times} \text{Nr}ʻR)\dot{+} (\text{Nr}ʻQ\dot{\times} \text{Nr}ʻR)\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components Nr'P +̇ Nr'Q, Nr'P ×̇ Nr'R, Nr'Q ×̇ Nr'R are adequate -/
theorem pm184_34 {W W₁ W₂ : Type*} {P : α → α → Prop} {Q : β → β → Prop} {R : δ → δ → Prop}
    (h : AdeqNrAdd W (n₀r P) (n₀r Q)) (h₁ : AdeqNrMul W₁ (n₀r P) (n₀r R))
    (h₂ : AdeqNrMul W₂ (n₀r Q) (n₀r R)) :
    ((n₀r P ∔ n₀r Q : Set (W → W → Prop)) ⨰ n₀r R : Set (γ → γ → Prop)) =
      ((n₀r P ⨰ n₀r R : Set (W₁ → W₁ → Prop)) ∔ (n₀r Q ⨰ n₀r R : Set (W₂ → W₂ → Prop)) :
        Set (γ → γ → Prop)) := by
  obtain ⟨X, hX, e⟩ := h.eq_n₀r P Q
  obtain ⟨Y₁, hY₁, e₁⟩ := h₁.eq_n₀r P R
  obtain ⟨Y₂, hY₂, e₂⟩ := h₂.eq_n₀r Q R
  rw [e, e₁, e₂, n₀r_nrMul_n₀r, n₀r_nrAdd_n₀r]
  obtain ⟨L, R', eLR, ⟨hL, hR'⟩, hd⟩ := rplus_split P Q
  apply nr_eq_nr_of_smor
  refine smor_trans (smor_rtimes hX (smor_refl R)) ?_
  rw [eLR, rtimes_rsum]
  exact smor_rsum_rplus (smor_trans (smor_rtimes hL (smor_refl R)) (smor_symm hY₁))
    (smor_trans (smor_rtimes hR' (smor_refl R)) (smor_symm hY₂)) (disj_rtimes hd R)

/-- ✱184·35. \(\vdash .(\nu \dot{+} \varpi )\dot{\times} \mu =(\nu \dot{\times} \mu )\dot{+} (\varpi \dot{\times} \mu ) \quad[*184·34]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components ν +̇ ϖ, ν ×̇ μ, ϖ ×̇ μ are adequate -/
theorem pm184_35 {α₁ α₂ α₃ W W₁ W₂ : Type*} {μ : Set (α₁ → α₁ → Prop)} {ν : Set (α₂ → α₂ → Prop)}
    {ϖ : Set (α₃ → α₃ → Prop)} (h : AdeqNrAdd W ν ϖ) (h₁ : AdeqNrMul W₁ ν μ)
    (h₂ : AdeqNrMul W₂ ϖ μ) :
    ((ν ∔ ϖ : Set (W → W → Prop)) ⨰ μ : Set (γ → γ → Prop)) =
      ((ν ⨰ μ : Set (W₁ → W₁ → Prop)) ∔ (ϖ ⨰ μ : Set (W₂ → W₂ → Prop)) : Set (γ → γ → Prop)) := by
  by_cases hν : ∃ Q, ν = n₀r Q
  · by_cases hϖ : ∃ R, ϖ = n₀r R
    · by_cases hμ : ∃ P, μ = n₀r P
      · obtain ⟨P, rfl⟩ := hμ; obtain ⟨Q, rfl⟩ := hν; obtain ⟨R, rfl⟩ := hϖ
        exact pm184_34 h h₁ h₂
      · push Not at hμ
        rw [nrMul_eq_empty_of_right _ hμ, nrMul_eq_empty_of_right (ν := μ) _ hμ, empty_nrAdd]
    · push Not at hϖ
      rw [nrAdd_eq_empty_of_right (ν := ϖ) _ hϖ, nrMul_eq_empty_of_left (μ := ϖ) hϖ,
        empty_nrMul, nrAdd_empty]
  · push Not at hν
    rw [nrAdd_eq_empty_of_left (μ := ν) hν, nrMul_eq_empty_of_left (μ := ν) hν, empty_nrMul,
      empty_nrAdd]

/-- ✱184·4. \(\vdash .2_{r}\dot{\times} \mu =\mu \dot{+} \mu \)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the type of the
arithmetical component 2_r is adequate (2_r exists in it) -/
theorem pm184_4 {W : Type*} {μ : Set (α → α → Prop)} (h : (two_r : Set (W → W → Prop)).Nonempty) :
    ((two_r : Set (W → W → Prop)) ⨰ μ : Set (γ → γ → Prop)) = (μ ∔ μ : Set (γ → γ → Prop)) := by
  obtain ⟨_, a, b, hab, -⟩ := h
  by_cases hμ : ∃ P, μ = n₀r P
  · obtain ⟨P, rfl⟩ := hμ
    rw [nrMul_of (two_r_eq_n₀r hab) rfl, n₀r_nrAdd_n₀r, rtimes_couple]
    exact nr_eq_nr_of_smor (smor_rsum_rplus (smor_opSemi P a) (smor_opSemi P b)
      (disj_opSemi hab P))
  · push Not at hμ
    rw [nrMul_eq_empty_of_right _ hμ, nrAdd_eq_empty_of_left hμ]

/-- ✱184·41. \(\vdash :\nu \neq 0_{r}.\supset .(\nu \dot{+} \dot{1} )\dot{\times} \mu = (\nu \dot{\times} \mu) \dot{+} \mu\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components ν +̇ 1̇ and ν ×̇ μ are adequate -/
theorem pm184_41 {W W₁ : Type*} {μ : Set (α → α → Prop)} {ν : Set (δ → δ → Prop)}
    (h : AdeqNrAddOne W β ν) (h₁ : AdeqNrMul W₁ ν μ) :
    ν ≠ zero_r → ((nrAddOne β ν : Set (W → W → Prop)) ⨰ μ : Set (γ → γ → Prop)) =
      ((ν ⨰ μ : Set (W₁ → W₁ → Prop)) ∔ μ : Set (γ → γ → Prop)) := by
  intro hν0
  obtain ⟨b⟩ := h.nonempty
  by_cases hν : ∃ Q, ν = n₀r Q
  · obtain ⟨Q, rfl⟩ := hν
    have hQ : rEx Q := ne_rNull_iff.1 fun e => hν0 (by rw [e]; exact zero_r_eq_n₀r.symm)
    by_cases hμ : ∃ P, μ = n₀r P
    · obtain ⟨P, rfl⟩ := hμ
      obtain ⟨X, hX, eX⟩ := h.eq_n₀r Q b
      obtain ⟨Y, hY, eY⟩ := h₁.eq_n₀r Q P
      rw [eX, eY, n₀r_nrMul_n₀r, n₀r_nrAdd_n₀r]
      obtain ⟨L, e, hLe, hL, he⟩ := addLastDot_split Q b
      rw [hLe] at hX
      apply nr_eq_nr_of_smor
      refine smor_trans (smor_rtimes hX (smor_refl P)) ?_
      rw [rtimes_addLast (smor_preserves (smor_symm hL) hQ)]
      exact smor_rsum_rplus (smor_trans (smor_rtimes hL (smor_refl P)) (smor_symm hY))
        (smor_opSemi P e) (disj_rtimes_opSemi he P)
    · push Not at hμ
      rw [nrMul_eq_empty_of_right _ hμ, nrAdd_eq_empty_of_right _ hμ]
  · push Not at hν
    rw [nrAddOne_empty_of hν, empty_nrMul, nrMul_eq_empty_of_left hν, empty_nrAdd]

/-- ✱184·42. \(\vdash :\nu \neq 0_{r}.\supset .(\dot{1} \dot{+} \nu )\dot{\times} \mu = \mu \dot{+} (\nu \dot{\times} \mu ) \quad[\text{Proof as in *184·41}]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components 1̇ +̇ ν and ν ×̇ μ are adequate -/
theorem pm184_42 {W W₁ : Type*} {μ : Set (α → α → Prop)} {ν : Set (δ → δ → Prop)}
    (h : AdeqNrOneAdd W β ν) (h₁ : AdeqNrMul W₁ ν μ) :
    ν ≠ zero_r → ((nrOneAdd β ν : Set (W → W → Prop)) ⨰ μ : Set (γ → γ → Prop)) =
      (μ ∔ (ν ⨰ μ : Set (W₁ → W₁ → Prop)) : Set (γ → γ → Prop)) := by
  intro hν0
  obtain ⟨b⟩ := h.nonempty
  by_cases hν : ∃ Q, ν = n₀r Q
  · obtain ⟨Q, rfl⟩ := hν
    have hQ : rEx Q := ne_rNull_iff.1 fun e => hν0 (by rw [e]; exact zero_r_eq_n₀r.symm)
    by_cases hμ : ∃ P, μ = n₀r P
    · obtain ⟨P, rfl⟩ := hμ
      obtain ⟨X, hX, eX⟩ := h.eq_n₀r Q b
      obtain ⟨Y, hY, eY⟩ := h₁.eq_n₀r Q P
      rw [eX, eY, n₀r_nrMul_n₀r, n₀r_nrAdd_n₀r]
      obtain ⟨L, e, hLe, hL, he⟩ := addFirstDot_split b Q
      rw [hLe] at hX
      apply nr_eq_nr_of_smor
      refine smor_trans (smor_rtimes hX (smor_refl P)) ?_
      rw [rtimes_addFirst (smor_preserves (smor_symm hL) hQ)]
      exact smor_rsum_rplus (smor_opSemi P e)
        (smor_trans (smor_rtimes hL (smor_refl P)) (smor_symm hY))
        (disj_rtimes_opSemi he P).symm
    · push Not at hμ
      rw [nrMul_eq_empty_of_right _ hμ, nrAdd_eq_empty_of_left hμ]
  · push Not at hν
    rw [nrOneAdd_empty_of hν, empty_nrMul, nrMul_eq_empty_of_left hν, nrAdd_empty]

private theorem empty_cardMul {ε ε' : Type*} (ν' : Set (Set ε')) :
    ((∅ : Set (Set ε)) ×ᶜ ν' : Set (Set γ)) = ∅ := by
  ext X; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨hA, -⟩, -⟩; exact n₀c_ne_empty A hA.symm

private theorem cardMul_empty {ε ε' : Type*} (μ' : Set (Set ε)) :
    (μ' ×ᶜ (∅ : Set (Set ε')) : Set (Set γ)) = ∅ := by
  ext X; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, B, ⟨-, hB⟩, -⟩; exact n₀c_ne_empty B hB.symm

/-- ✱184·5. \(\vdash :\mu ,\nu \in \text{NR}.\supset .Cʻʻ(\mu \dot{\times} \nu ) = Cʻʻ\mu \times _{c}Cʻʻ\nu \) -/
theorem pm184_5 {β₁ β₂ : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    μ ∈ NR β₁ ∧ ν ∈ NR β₂ →
      C ʻʻ (μ ⨰ ν : Set (γ → γ → Prop)) = (C ʻʻ μ ×ᶜ C ʻʻ ν : Set (Set γ)) := by
  rintro ⟨hμ, hν⟩
  rcases NR_cases hμ with rfl | ⟨P, rfl⟩
  · rw [empty_nrMul, img_empty, img_empty, empty_cardMul]
  rcases NR_cases hν with rfl | ⟨Q, rfl⟩
  · rw [nrMul_empty, img_empty, img_empty, cardMul_empty]
  rw [n₀r_nrMul_n₀r, C_img_nr, n₀r_eq_nr P, n₀r_eq_nr Q, C_img_nr, C_img_nr,
    ← n₀c_eq_nc (fld P), ← n₀c_eq_nc (fld Q), n₀c_cardMul_n₀c, fld_rtimes_eq]


section Helpers185

/-- Transport of selections along a double correlator (cf. ✱172·42·44). -/
private theorem smor_relPi_of {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} {T : α → β → Prop}
    (t1 : ∀ x x' y, T x y → T x' y → x = x') (t2 : ∀ x y y', T x y → T x y' → y = y')
    (tc : ∀ Y, Y ∈ fld Q → ∀ y, y ∈ fld Y → ∃ x, T x y) (hP : P = daggerRel T ⁏ Q) :
    smor (relPi P) (relPi Q) := by
  -- `Y ↦ T;Y` is one-one on `C'Q`
  have fT : ∀ Y, Y ∈ fld Q → ∀ x, x ∈ fld (T ⁏ Y) ↔ ∃ y, y ∈ fld Y ∧ T x y :=
    fun Y hY x => mem_fld_semi (tc Y hY)
  have ginj : ∀ Y Y', Y ∈ fld Q → Y' ∈ fld Q → T ⁏ Y = T ⁏ Y' → Y = Y' := by
    have key : ∀ {Y Y'}, Y ∈ fld Q → Y' ∈ fld Q → T ⁏ Y = T ⁏ Y' → ∀ u v, Y u v → Y' u v := by
      intro Y Y' hY hY' e u v huv
      obtain ⟨a, ha⟩ := tc Y hY u ⟨v, Or.inl huv⟩
      obtain ⟨b, hb⟩ := tc Y hY v ⟨u, Or.inr huv⟩
      have : (T ⁏ Y') a b := by rw [← e]; exact (semi_apply _ _ _ _).2 ⟨u, v, ⟨ha, hb⟩, huv⟩
      obtain ⟨u', v', ⟨ha', hb'⟩, huv'⟩ := (semi_apply _ _ _ _).1 this
      rw [t2 a u u' ha ha', t2 b v v' hb hb']; exact huv'
    intro Y Y' hY hY' e
    funext u v; apply propext
    exact ⟨key hY hY' e u v, key hY' hY e.symm u v⟩
  have hfP : ∀ X, X ∈ fld P ↔ ∃ Y, Y ∈ fld Q ∧ X = T ⁏ Y := fun X => by
    rw [hP, daggerRel_eq_graph]; exact mem_fld_graph_semi
  let pull : (β → (β → β → Prop) → Prop) → α → (α → α → Prop) → Prop :=
    fun N x X => ∃ y Y, (T x y ∧ X = T ⁏ Y) ∧ N y Y
  have pull_sel : ∀ N, N ∈ sel F (fld Q) → pull N ∈ sel F (fld P) := by
    intro N hN
    obtain ⟨⟨n1, n2⟩, n3⟩ := mem_selF.1 hN
    refine mem_selF.2 ⟨⟨?_, ?_⟩, fun X => ?_⟩
    · rintro x x' X ⟨y, Y, ⟨hx, rfl⟩, hy⟩ ⟨y', Y', ⟨hx', e⟩, hy'⟩
      have hYY : Y' = Y := ginj Y' Y ((n3 Y').2 ⟨y', hy'⟩) ((n3 Y).2 ⟨y, hy⟩) e.symm
      subst hYY
      rw [n1 y y' Y' hy hy'] at hx
      exact t1 x x' y' hx hx'
    · rintro x X ⟨y, Y, ⟨hx, rfl⟩, hy⟩
      exact (fT Y ((n3 Y).2 ⟨y, hy⟩) x).2 ⟨y, n2 y Y hy, hx⟩
    · rw [hfP]
      constructor
      · rintro ⟨Y, hY, rfl⟩
        obtain ⟨y, hy⟩ := (n3 Y).1 hY
        obtain ⟨x, hx⟩ := tc Y hY y (n2 y Y hy)
        exact ⟨x, y, Y, ⟨hx, rfl⟩, hy⟩
      · rintro ⟨x, y, Y, ⟨-, rfl⟩, hy⟩; exact ⟨Y, (n3 Y).2 ⟨y, hy⟩, rfl⟩
  have pull_inj : ∀ N N', N ∈ sel F (fld Q) → N' ∈ sel F (fld Q) → pull N = pull N' → N = N' := by
    have key : ∀ {N N'}, N ∈ sel F (fld Q) → N' ∈ sel F (fld Q) → pull N = pull N' →
        ∀ y Y, N y Y → N' y Y := by
      intro N N' hN hN' e y Y h
      obtain ⟨⟨n1, n2⟩, n3⟩ := mem_selF.1 hN
      obtain ⟨⟨n1', n2'⟩, n3'⟩ := mem_selF.1 hN'
      have hY := (n3 Y).2 ⟨y, h⟩
      obtain ⟨x, hx⟩ := tc Y hY y (n2 y Y h)
      have : pull N' x (T ⁏ Y) := by rw [← e]; exact ⟨y, Y, ⟨hx, rfl⟩, h⟩
      obtain ⟨y', Y', ⟨hx', e'⟩, h'⟩ := this
      have hYY := ginj Y Y' hY ((n3' Y').2 ⟨y', h'⟩) e'
      subst hYY
      rw [t2 x y y' hx hx']; exact h'
    intro N N' hN hN' e
    funext y Y; apply propext
    exact ⟨key hN hN' e y Y, key hN' hN e.symm y Y⟩
  have pull_surj : ∀ M, M ∈ sel F (fld P) → ∃ N, N ∈ sel F (fld Q) ∧ M = pull N := by
    intro M hM
    obtain ⟨⟨m1, m2⟩, m3⟩ := mem_selF.1 hM
    let N : β → (β → β → Prop) → Prop := fun y Y => Y ∈ fld Q ∧ ∃ x, T x y ∧ M x (T ⁏ Y)
    have hN : N ∈ sel F (fld Q) := by
      refine mem_selF.2 ⟨⟨?_, ?_⟩, fun Y => ⟨fun hY => ?_, fun ⟨y, hY, _⟩ => hY⟩⟩
      · rintro y y' Y ⟨-, x, hx, hM⟩ ⟨-, x', hx', hM'⟩
        rw [m1 x x' _ hM hM'] at hx
        exact t2 x' y y' hx hx'
      · rintro y Y ⟨hY, x, hx, hM⟩
        obtain ⟨y₀, hy₀, hx₀⟩ := (fT Y hY x).1 (m2 x _ hM)
        rw [t2 x y y₀ hx hx₀]; exact hy₀
      · obtain ⟨x, hx⟩ := (m3 _).1 ((hfP _).2 ⟨Y, hY, rfl⟩)
        obtain ⟨y, hy, hxy⟩ := (fT Y hY x).1 (m2 x _ hx)
        exact ⟨y, hY, x, hxy, hx⟩
    refine ⟨N, hN, ?_⟩
    funext x X; apply propext
    constructor
    · intro h
      obtain ⟨Y, hY, rfl⟩ := (hfP X).1 ((m3 X).2 ⟨x, h⟩)
      obtain ⟨y, -, hxy⟩ := (fT Y hY x).1 (m2 x _ h)
      exact ⟨y, Y, ⟨hxy, rfl⟩, hY, x, hxy, h⟩
    · rintro ⟨y, Y, ⟨hxy, rfl⟩, -, x', hx', h⟩
      rw [t1 x x' y hxy hx']; exact h
  have pull_relPi : ∀ N N', N ∈ sel F (fld Q) → N' ∈ sel F (fld Q) →
      (relPi P (pull N) (pull N') ↔ relPi Q N N') := by
    intro N N' hN hN'
    obtain ⟨⟨n1, n2⟩, n3⟩ := mem_selF.1 hN
    obtain ⟨⟨n1', n2'⟩, n3'⟩ := mem_selF.1 hN'
    rw [relPi_iff, relPi_iff]
    simp only [pull_sel N hN, pull_sel N' hN', hN, hN', true_and]
    have hPapp : ∀ R X, P R X ↔ ∃ Y₁ Y₂, (R = T ⁏ Y₁ ∧ X = T ⁏ Y₂) ∧ Q Y₁ Y₂ := fun R X => by
      rw [hP, daggerRel_eq_graph, semi_graph_apply]
    constructor
    · rintro ⟨X, ⟨x, x', ⟨⟨y, Y, ⟨hx, rfl⟩, hy⟩, ⟨y', Y', ⟨hx', e⟩, hy'⟩⟩, hxx'⟩, h2⟩
      have hY := (n3 Y).2 ⟨y, hy⟩
      have hYY := ginj Y Y' hY ((n3' Y').2 ⟨y', hy'⟩) e
      subst hYY
      obtain ⟨u, u', ⟨hu, hu'⟩, huu'⟩ := (semi_apply _ _ _ _).1 hxx'
      have e1 := t2 x y u hx hu
      have e2 := t2 x' y' u' hx' hu'
      subst e1 e2
      refine ⟨Y, ⟨y, y', ⟨hy, hy'⟩, huu'⟩, fun R hR a b ha hb => ?_⟩
      have hRf := (n3 R).2 ⟨a, ha⟩
      obtain ⟨c, hc⟩ := tc R hRf a (n2 a R ha)
      obtain ⟨d, hd⟩ := tc R hRf b (n2' b R hb)
      have := h2 (T ⁏ R) ⟨(hPapp _ _).2 ⟨R, Y, ⟨rfl, rfl⟩, hR.1⟩, fun e => hR.2
        (ginj R Y hRf hY e)⟩ c d ⟨a, R, ⟨hc, rfl⟩, ha⟩ ⟨b, R, ⟨hd, rfl⟩, hb⟩
      subst this
      exact t2 c a b hc hd
    · rintro ⟨Y, ⟨y, y', ⟨hy, hy'⟩, hyy'⟩, h2⟩
      have hY := (n3 Y).2 ⟨y, hy⟩
      obtain ⟨x, hx⟩ := tc Y hY y (n2 y Y hy)
      obtain ⟨x', hx'⟩ := tc Y hY y' (n2' y' Y hy')
      refine ⟨T ⁏ Y, ⟨x, x', ⟨⟨y, Y, ⟨hx, rfl⟩, hy⟩, ⟨y', Y, ⟨hx', rfl⟩, hy'⟩⟩,
        (semi_apply _ _ _ _).2 ⟨y, y', ⟨hx, hx'⟩, hyy'⟩⟩, ?_⟩
      rintro R ⟨hR, hne⟩ u v ⟨a, R₁, ⟨hu, rfl⟩, ha⟩ ⟨b, R₂, ⟨hv, e⟩, hb⟩
      have hR₁ := (n3 R₁).2 ⟨a, ha⟩
      have hRR := ginj R₁ R₂ hR₁ ((n3' R₂).2 ⟨b, hb⟩) e
      subst hRR
      obtain ⟨Y₁, Y₂, ⟨e1, e2⟩, hQ⟩ := (hPapp _ _).1 hR
      have h₁ : R₁ = Y₁ := ginj R₁ Y₁ hR₁ ⟨Y₂, Or.inl hQ⟩ e1
      have h₂ : Y = Y₂ := ginj Y Y₂ hY ⟨Y₁, Or.inr hQ⟩ e2
      subst h₁ h₂
      have := h2 R₁ ⟨hQ, fun e => hne (by rw [e])⟩ a b ha hb
      subst this
      exact t1 u v a hu hv
  -- conclusion
  have e : relPi P = graph pull ⁏ relPi Q := by
    funext M M'; apply propext
    rw [semi_graph_apply]
    constructor
    · intro h
      obtain ⟨⟨hM, hM'⟩, -⟩ := relPi_iff.1 h
      obtain ⟨N, hN, rfl⟩ := pull_surj M hM
      obtain ⟨N', hN', rfl⟩ := pull_surj M' hM'
      exact ⟨N, N', ⟨rfl, rfl⟩, (pull_relPi N N' hN hN').1 h⟩
    · rintro ⟨N, N', ⟨rfl, rfl⟩, h⟩
      obtain ⟨⟨hN, hN'⟩, -⟩ := relPi_iff.1 h
      exact (pull_relPi N N' hN hN').2 h
  rw [e]
  exact smor_graph fun N N' hN hN' h => pull_inj N N' (mem_fld_relPi hN) (mem_fld_relPi hN') h

/-- `P smor smor Q . ⊃ . Π'P smor Π'Q` (✱172·44). -/
private theorem smor_relPi_of_smorsmor {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} (h : smorsmor P Q) :
    smor (relPi P) (relPi Q) := by
  obtain ⟨T, ⟨hT, hcod⟩, hP⟩ := h
  obtain ⟨a, b⟩ := mem_arrow_one_one.1 hT
  have hc : ∀ z, z ∈ fld (relSigma Q) → ∃ x, T x z := fun z hz => by
    have : z ∈ codom T := by rw [← (hcod : fld (relSigma Q) = codom T)]; exact hz
    exact this
  exact smor_relPi_of (fun x x' y h1 h2 => a x x' y ⟨h1, h2⟩) (fun x y y' h1 h2 => b x y y' ⟨h1, h2⟩)
    (fun Y hY y hy => hc y (fld_relSigma'.2 ⟨Y, hY, hy⟩)) hP

end Helpers185

section Helpers185b

private theorem relPi_rNull :
    relPi (rNull : (α → α → Prop) → (α → α → Prop) → Prop) = rNull := by
  funext M N; apply propext
  refine ⟨fun h => ?_, fun h => absurd h (rNull_apply _ _)⟩
  obtain ⟨-, Q, ⟨x, -, ⟨hx, -⟩, -⟩, -⟩ := relPi_iff.1 h
  obtain ⟨⟨-, -⟩, h3⟩ := mem_selF.1 (relPi_iff.1 h).1.1
  have := (h3 Q).2 ⟨x, hx⟩
  rw [fld_rNull] at this; exact absurd this (Set.notMem_empty Q)

private theorem sel_empty_of_rNull_mem {L : Set (α → α → Prop)} (h : rNull ∈ L)
    {M : α → (α → α → Prop) → Prop} : M ∉ sel F L := by
  intro hM
  obtain ⟨⟨-, m2⟩, m3⟩ := mem_selF.1 hM
  obtain ⟨x, hx⟩ := (m3 _).1 h
  have := m2 x _ hx
  rw [fld_rNull] at this; exact absurd this (Set.notMem_empty x)

/-- `Λ̇ ∈ C'P . ⊃ . Π'P = Λ̇` (✱172·14). -/
private theorem relPi_eq_rNull_of_mem {P : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : rNull ∈ fld P) : relPi P = rNull := by
  funext M N; apply propext
  refine ⟨fun h' => absurd (relPi_iff.1 h').1.1 (sel_empty_of_rNull_mem h),
    fun h' => absurd h' (rNull_apply _ _)⟩

/-- Every selection is in the field of `Π'P` when `∃̇!P` (cf. ✱172·16). -/
private theorem sel_mem_fld_relPi {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : rEx P)
    {M : α → (α → α → Prop) → Prop} (hM : M ∈ sel F (fld P)) : M ∈ fld (relPi P) := by
  classical
  obtain ⟨⟨m1, m2⟩, m3⟩ := mem_selF.1 hM
  obtain ⟨Q, R, hQR⟩ := hP
  have hQ : Q ∈ fld P := ⟨R, Or.inl hQR⟩
  obtain ⟨m, hm⟩ := (m3 Q).1 hQ
  obtain ⟨m', hmm'⟩ := m2 m Q hm
  let M₂ : α → (α → α → Prop) → Prop := fun x X => (X ≠ Q ∧ M x X) ∨ (X = Q ∧ x = m')
  have hm' : m' ∈ fld Q := by rcases hmm' with h | h; exacts [⟨m, Or.inr h⟩, ⟨m, Or.inl h⟩]
  have hM₂ : M₂ ∈ sel F (fld P) := by
    refine mem_selF.2 ⟨⟨?_, ?_⟩, fun X => ⟨fun hX => ?_, ?_⟩⟩
    · rintro x y X (⟨hX, hx⟩ | ⟨hX, rfl⟩) (⟨hX', hy⟩ | ⟨hX', rfl⟩)
      · exact m1 x y X hx hy
      · exact absurd hX' hX
      · exact absurd hX hX'
      · rfl
    · rintro x X (⟨-, hx⟩ | ⟨rfl, rfl⟩)
      · exact m2 x X hx
      · exact hm'
    · by_cases e : X = Q
      · exact ⟨m', Or.inr ⟨e, rfl⟩⟩
      · obtain ⟨x, hx⟩ := (m3 X).1 hX; exact ⟨x, Or.inl ⟨e, hx⟩⟩
    · rintro ⟨x, ⟨-, hx⟩ | ⟨rfl, -⟩⟩
      · exact (m3 X).2 ⟨x, hx⟩
      · exact hQ
  have agree : ∀ R, R ≠ Q → ∀ u v, M u R → M₂ v R → u = v := by
    rintro R hR u v hu (⟨-, hv⟩ | ⟨e, -⟩)
    · exact m1 u v R hu hv
    · exact absurd e hR
  rcases hmm' with h | h
  · exact ⟨M₂, Or.inl (relPi_iff.2 ⟨⟨hM, hM₂⟩, Q, ⟨m, m', ⟨hm, Or.inr ⟨rfl, rfl⟩⟩, h⟩,
      fun R hR u v hu hv => agree R hR.2 u v hu hv⟩)⟩
  · exact ⟨M₂, Or.inr (relPi_iff.2 ⟨⟨hM₂, hM⟩, Q, ⟨m', m, ⟨Or.inr ⟨rfl, rfl⟩, hm⟩, h⟩,
      fun R hR u v hu hv => (agree R hR.2 v u hv hu).symm⟩)⟩

private theorem fld_relPi_eq {P : (α → α → Prop) → (α → α → Prop) → Prop} (hP : rEx P) :
    fld (relPi P) = sel F (fld P) :=
  Set.ext fun _ => ⟨mem_fld_relPi, sel_mem_fld_relPi hP⟩

/-! #### `Π'(P ⤉ Q) smor Π'P × Π'Q` (✱172·35) -/

private theorem sel_union {L₁ L₂ : Set (α → α → Prop)} (hd : Disjoint L₁ L₂)
    {M₁ M₂ : α → (α → α → Prop) → Prop} (h1 : M₁ ∈ sel F L₁) (h2 : M₂ ∈ sel F L₂) :
    M₁ ⊍ M₂ ∈ sel F (L₁ ∪ L₂) := by
  obtain ⟨⟨a1, b1⟩, c1⟩ := mem_selF.1 h1
  obtain ⟨⟨a2, b2⟩, c2⟩ := mem_selF.1 h2
  refine mem_selF.2 ⟨⟨?_, ?_⟩, fun X => ?_⟩
  · rintro x y X (hx | hx) (hy | hy)
    · exact a1 x y X hx hy
    · exact absurd ((c2 X).2 ⟨y, hy⟩) (Set.disjoint_left.1 hd ((c1 X).2 ⟨x, hx⟩))
    · exact absurd ((c2 X).2 ⟨x, hx⟩) (Set.disjoint_left.1 hd ((c1 X).2 ⟨y, hy⟩))
    · exact a2 x y X hx hy
  · rintro x X (h | h)
    · exact b1 x X h
    · exact b2 x X h
  · rw [Set.mem_union, c1, c2]
    constructor
    · rintro (⟨x, h⟩ | ⟨x, h⟩)
      · exact ⟨x, Or.inl h⟩
      · exact ⟨x, Or.inr h⟩
    · rintro ⟨x, h | h⟩
      · exact Or.inl ⟨x, h⟩
      · exact Or.inr ⟨x, h⟩

private theorem sel_res {L₁ L₂ : Set (α → α → Prop)} {M : α → (α → α → Prop) → Prop}
    (h : M ∈ sel F (L₁ ∪ L₂)) : (fun x X => M x X ∧ X ∈ L₁) ∈ sel F L₁ := by
  obtain ⟨⟨a, b⟩, c⟩ := mem_selF.1 h
  refine mem_selF.2 ⟨⟨fun x y X hx hy => a x y X hx.1 hy.1, fun x X hx => b x X hx.1⟩,
    fun X => ⟨fun hX => ?_, fun ⟨x, _, hX⟩ => hX⟩⟩
  obtain ⟨x, hx⟩ := (c X).1 (Or.inl hX)
  exact ⟨x, hx, hX⟩

private theorem sel_res' {L₁ L₂ : Set (α → α → Prop)} {M : α → (α → α → Prop) → Prop}
    (h : M ∈ sel F (L₁ ∪ L₂)) : (fun x X => M x X ∧ X ∈ L₂) ∈ sel F L₂ := by
  rw [Set.union_comm] at h; exact sel_res h

private theorem sel_split {L₁ L₂ : Set (α → α → Prop)} {M : α → (α → α → Prop) → Prop}
    (h : M ∈ sel F (L₁ ∪ L₂)) : M = (fun x X => M x X ∧ X ∈ L₁) ⊍ (fun x X => M x X ∧ X ∈ L₂) := by
  obtain ⟨-, c⟩ := mem_selF.1 h
  funext x X; apply propext
  constructor
  · intro hx
    rcases (c X).2 ⟨x, hx⟩ with h1 | h2
    · exact Or.inl ⟨hx, h1⟩
    · exact Or.inr ⟨hx, h2⟩
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx

private theorem sel_union_res {L₁ L₂ : Set (α → α → Prop)} (hd : Disjoint L₁ L₂)
    {M₁ M₂ : α → (α → α → Prop) → Prop} (h1 : M₁ ∈ sel F L₁) (h2 : M₂ ∈ sel F L₂) :
    (fun x X => (M₁ ⊍ M₂) x X ∧ X ∈ L₁) = M₁ ∧ (fun x X => (M₁ ⊍ M₂) x X ∧ X ∈ L₂) = M₂ := by
  obtain ⟨-, c1⟩ := mem_selF.1 h1
  obtain ⟨-, c2⟩ := mem_selF.1 h2
  constructor
  · funext x X; apply propext
    constructor
    · rintro ⟨hx | hx, hX⟩
      · exact hx
      · exact absurd ((c2 X).2 ⟨x, hx⟩) (Set.disjoint_left.1 hd hX)
    · intro hx; exact ⟨Or.inl hx, (c1 X).2 ⟨x, hx⟩⟩
  · funext x X; apply propext
    constructor
    · rintro ⟨hx | hx, hX⟩
      · exact absurd ((c1 X).2 ⟨x, hx⟩) (Set.disjoint_right.1 hd hX)
      · exact hx
    · intro hx; exact ⟨Or.inr hx, (c2 X).2 ⟨x, hx⟩⟩

private theorem relPi_rsum_smor {A B : (α → α → Prop) → (α → α → Prop) → Prop} (hA : rEx A)
    (hB : rEx B) (hd : Disjoint (fld A) (fld B)) : smor (relPi (A ⤉ B)) (relPi A ×ᵣ relPi B) := by
  let g : ((α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) →
      α → (α → α → Prop) → Prop :=
    fun c x X => ∃ N₂ N₁, c = N₂ ↓ N₁ ∧ (N₁ x X ∨ N₂ x X)
  have hg : ∀ N₂ N₁, g (N₂ ↓ N₁) = N₁ ⊍ N₂ := by
    intro N₂ N₁
    funext x X; apply propext
    constructor
    · rintro ⟨N₂', N₁', e, h⟩
      obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e
      exact h
    · intro h; exact ⟨N₂, N₁, rfl, h⟩
  have hfAB : fld (A ⤉ B) = fld A ∪ fld B := fld_rsum A B
  have e : relPi (A ⤉ B) = graph g ⁏ (relPi A ×ᵣ relPi B) := by
    funext M N; apply propext
    rw [semi_graph_apply]
    constructor
    · intro h
      obtain ⟨⟨hM, hN⟩, Q, ⟨u, v, ⟨hu, hv⟩, huv⟩, h2⟩ := relPi_iff.1 h
      rw [hfAB] at hM hN
      refine ⟨(fun x X => M x X ∧ X ∈ fld B) ↓ (fun x X => M x X ∧ X ∈ fld A),
        (fun x X => N x X ∧ X ∈ fld B) ↓ (fun x X => N x X ∧ X ∈ fld A),
        ⟨(sel_split hM).trans (hg _ _).symm, (sel_split hN).trans (hg _ _).symm⟩, ?_⟩
      obtain ⟨-, cM⟩ := mem_selF.1 hM
      have hQ : Q ∈ fld A ∪ fld B := (cM Q).2 ⟨u, hu⟩
      rw [rtimes_lex]
      refine ⟨_, _, _, _, ⟨rfl, rfl⟩, ?_⟩
      rcases hQ with hQA | hQB
      · refine Or.inr ⟨relPi_iff.2 ⟨⟨sel_res hM, sel_res hN⟩, Q, ⟨u, v, ⟨⟨hu, hQA⟩, ⟨hv, hQA⟩⟩, huv⟩,
          fun R hR a b ha hb => h2 R ⟨Or.inl (Or.inl hR.1), hR.2⟩ a b ha.1 hb.1⟩,
          sel_mem_fld_relPi hB (sel_res' hM), sel_mem_fld_relPi hB (sel_res' hN)⟩
      · refine Or.inl ⟨?_, sel_mem_fld_relPi hA (sel_res hM), relPi_iff.2 ⟨⟨sel_res' hM, sel_res' hN⟩,
          Q, ⟨u, v, ⟨⟨hu, hQB⟩, ⟨hv, hQB⟩⟩, huv⟩,
          fun R hR a b ha hb => h2 R ⟨Or.inl (Or.inr hR.1), hR.2⟩ a b ha.1 hb.1⟩⟩
        obtain ⟨⟨mM, -⟩, -⟩ := mem_selF.1 hM
        obtain ⟨⟨mN, -⟩, cN⟩ := mem_selF.1 hN
        funext x X; apply propext
        constructor
        · rintro ⟨hx, hX⟩
          obtain ⟨y, hy⟩ := (cN X).1 (Or.inl hX)
          have := h2 X ⟨Or.inr ⟨hX, hQB⟩, fun e => Set.disjoint_left.1 hd (e ▸ hX) hQB⟩ x y hx hy
          subst this; exact ⟨hy, hX⟩
        · rintro ⟨hx, hX⟩
          obtain ⟨y, hy⟩ := (cM X).1 (Or.inl hX)
          have := h2 X ⟨Or.inr ⟨hX, hQB⟩, fun e => Set.disjoint_left.1 hd (e ▸ hX) hQB⟩ y x hy hx
          subst this; exact ⟨hy, hX⟩
    · rintro ⟨c, d, ⟨rfl, rfl⟩, h⟩
      obtain ⟨x, z, y, w, ⟨rfl, rfl⟩, hlex⟩ := (rtimes_lex _ _ _ _).1 h
      clear h
      rw [hg, hg]
      rcases hlex with ⟨rfl, hz, hxy⟩ | ⟨hzw, hx, hy⟩
      · have hzs := mem_fld_relPi hz
        obtain ⟨⟨hx, hy⟩, Q, ⟨u, v, ⟨hu, hv⟩, huv⟩, h2⟩ := relPi_iff.1 hxy
        obtain ⟨⟨z1, -⟩, zc⟩ := mem_selF.1 hzs
        obtain ⟨-, xc⟩ := mem_selF.1 hx
        have hQB : Q ∈ fld B := (xc Q).2 ⟨u, hu⟩
        have hQA : Q ∉ fld A := Set.disjoint_right.1 hd hQB
        refine relPi_iff.2 ⟨⟨by rw [hfAB]; exact sel_union hd hzs hx,
          by rw [hfAB]; exact sel_union hd hzs hy⟩, Q, ⟨u, v, ⟨Or.inr hu, Or.inr hv⟩, huv⟩, ?_⟩
        rintro R ⟨hRQ, hne⟩ a b ha hb
        rcases hRQ with (hR | hR) | ⟨hR, -⟩
        · exact absurd ⟨R, Or.inr hR⟩ hQA
        · have hRB : R ∈ fld B := ⟨Q, Or.inl hR⟩
          have hRA : R ∉ fld A := Set.disjoint_right.1 hd hRB
          rcases ha with ha | ha
          · exact absurd ((zc R).2 ⟨a, ha⟩) hRA
          rcases hb with hb | hb
          · exact absurd ((zc R).2 ⟨b, hb⟩) hRA
          exact h2 R ⟨hR, hne⟩ a b ha hb
        · have hRB : R ∉ fld B := Set.disjoint_left.1 hd hR
          rcases ha with ha | ha
          swap; · exact absurd (((mem_selF.1 hx).2 R).2 ⟨a, ha⟩) hRB
          rcases hb with hb | hb
          swap; · exact absurd (((mem_selF.1 hy).2 R).2 ⟨b, hb⟩) hRB
          exact z1 a b R ha hb
      · have hzs := mem_fld_relPi hx
        have hys := mem_fld_relPi hy
        obtain ⟨⟨hz, hw⟩, Q, ⟨u, v, ⟨hu, hv⟩, huv⟩, h2⟩ := relPi_iff.1 hzw
        obtain ⟨-, zc⟩ := mem_selF.1 hz
        obtain ⟨⟨w1, -⟩, wc⟩ := mem_selF.1 hw
        obtain ⟨⟨x1, -⟩, xc⟩ := mem_selF.1 hzs
        obtain ⟨⟨y1, -⟩, yc⟩ := mem_selF.1 hys
        have hQA : Q ∈ fld A := (zc Q).2 ⟨u, hu⟩
        have hQB : Q ∉ fld B := Set.disjoint_left.1 hd hQA
        refine relPi_iff.2 ⟨⟨by rw [hfAB]; exact sel_union hd hz hzs,
          by rw [hfAB]; exact sel_union hd hw hys⟩, Q, ⟨u, v, ⟨Or.inl hu, Or.inl hv⟩, huv⟩, ?_⟩
        rintro R ⟨hRQ, hne⟩ a b ha hb
        rcases hRQ with (hR | hR) | ⟨-, hQ⟩
        · have hRA : R ∈ fld A := ⟨Q, Or.inl hR⟩
          have hRB : R ∉ fld B := Set.disjoint_left.1 hd hRA
          rcases ha with ha | ha
          swap; · exact absurd ((xc R).2 ⟨a, ha⟩) hRB
          rcases hb with hb | hb
          swap; · exact absurd ((yc R).2 ⟨b, hb⟩) hRB
          exact h2 R ⟨hR, hne⟩ a b ha hb
        · exact absurd ⟨R, Or.inr hR⟩ hQB
        · exact absurd hQ hQB
  rw [e]
  refine smor_graph fun c d hc hd' h => ?_
  obtain ⟨x, z, ⟨hx, hz⟩, rfl⟩ := mem_fld_rtimes.1 hc
  obtain ⟨y, w, ⟨hy, hw⟩, rfl⟩ := mem_fld_rtimes.1 hd'
  rw [hg, hg] at h
  have r1 := sel_union_res hd (mem_fld_relPi hz) (mem_fld_relPi hx)
  have r2 := sel_union_res hd (mem_fld_relPi hw) (mem_fld_relPi hy)
  rw [h] at r1
  rw [← r1.1.symm.trans r2.1, ← r1.2.symm.trans r2.2]

end Helpers185b

section Helpers185c

private theorem relPi_congr_I {P P' : (α → α → Prop) → (α → α → Prop) → Prop}
    (hf : fld P = fld P') (h : ∀ R Q, R ≠ Q → (P R Q ↔ P' R Q)) : smor (relPi P) (relPi P') := by
  rw [relPi_congr hf h]; exact smor_refl _

/-- `P ≠ Q . ⊃ . Π'(P ↓ Q) smor P × Q` (✱172·23). -/
private theorem relPi_couple_smor {P Q : α → α → Prop} (hPQ : P ≠ Q) :
    smor (relPi (P ↓ Q)) (P ×ᵣ Q) := by
  have hd : Disjoint (fld (P ↓ P)) (fld (Q ↓ Q)) := by
    rw [fld_couple_self, fld_couple_self, Set.disjoint_singleton]; exact hPQ
  have e : relPi (P ↓ Q) = relPi ((P ↓ P) ⤉ (Q ↓ Q)) := by
    refine relPi_congr ?_ fun R S hRS => ?_
    · rw [fld_rsum, fld_couple, fld_couple_self, fld_couple_self]; rfl
    · rw [rsum_apply, fld_couple_self, fld_couple_self]
      simp only [couple_apply, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl, rfl⟩; exact Or.inr ⟨rfl, rfl⟩
      · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
        · exact absurd rfl hRS
        · exact absurd rfl hRS
        · exact ⟨rfl, rfl⟩
  rw [e]
  refine smor_trans (relPi_rsum_smor ⟨P, P, rfl, rfl⟩ ⟨Q, Q, rfl, rfl⟩ hd) ?_
  rw [relPi_couple_self, relPi_couple_self]
  exact smor_rtimes (smor_sep P) (smor_sep Q)

/-- `Z ∼∈ C'P . ⊃ . Π'(P ⇸ Z) smor Π'P × Z` (✱172·32). -/
private theorem relPi_addLast_smor {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    (hZ : Z ∉ fld P) : smor (relPi (P ⇸ Z)) (relPi P ×ᵣ Z) := by
  by_cases hP : rEx P
  · have e : relPi (P ⇸ Z) = relPi (P ⤉ (Z ↓ Z)) := by
      refine relPi_congr ?_ fun R S hRS => ?_
      · rw [fld_rsum, fld_couple_self, fld_addLast_eq hP]
      · rw [rsum_apply, addLast_apply, fld_couple_self]
        simp only [couple_apply, Set.mem_singleton_iff]
        constructor
        · rintro (h | ⟨h, rfl⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr ⟨h, rfl⟩
        · rintro ((h | ⟨rfl, rfl⟩) | ⟨h, rfl⟩)
          · exact Or.inl h
          · exact absurd rfl hRS
          · exact Or.inr ⟨h, rfl⟩
    rw [e]
    have hd : Disjoint (fld P) (fld (Z ↓ Z)) := by
      rw [fld_couple_self, Set.disjoint_singleton_right]; exact hZ
    refine smor_trans (relPi_rsum_smor hP ⟨Z, Z, rfl, rfl⟩ hd) ?_
    rw [relPi_couple_self]
    exact smor_rtimes (smor_refl _) (smor_sep Z)
  · have hP0 : P = rNull := by by_contra h; exact hP (ne_rNull_iff.1 h)
    subst hP0
    rw [addLast_rNull, relPi_rNull]
    have : (rNull : (α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) ×ᵣ Z =
        rNull := by
      by_contra h
      obtain ⟨⟨_, _, h'⟩, -⟩ := rEx_rtimes.1 (ne_rNull_iff.1 h)
      exact rNull_apply _ _ h'
    rw [this]; exact smor_rNull_iff'.2 rfl

/-- `Z ∼∈ C'P . ⊃ . Π'(Z ⇷ P) smor Z × Π'P` (✱172·321). -/
private theorem relPi_addFirst_smor {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    (hZ : Z ∉ fld P) : smor (relPi (Z ⇷ P)) (Z ×ᵣ relPi P) := by
  by_cases hP : rEx P
  · have e : relPi (Z ⇷ P) = relPi ((Z ↓ Z) ⤉ P) := by
      refine relPi_congr ?_ fun R S hRS => ?_
      · rw [fld_rsum, fld_couple_self, fld_addFirst_eq hP]
      · rw [rsum_apply, addFirst_apply, fld_couple_self]
        simp only [couple_apply, Set.mem_singleton_iff]
        constructor
        · rintro (⟨rfl, h⟩ | h)
          · exact Or.inr ⟨rfl, h⟩
          · exact Or.inl (Or.inr h)
        · rintro ((⟨rfl, rfl⟩ | h) | ⟨rfl, h⟩)
          · exact absurd rfl hRS
          · exact Or.inr h
          · exact Or.inl ⟨rfl, h⟩
    rw [e]
    have hd : Disjoint (fld (Z ↓ Z)) (fld P) := by
      rw [fld_couple_self, Set.disjoint_singleton_left]; exact hZ
    refine smor_trans (relPi_rsum_smor ⟨Z, Z, rfl, rfl⟩ hP hd) ?_
    rw [relPi_couple_self]
    exact smor_rtimes (smor_sep Z) (smor_refl _)
  · have hP0 : P = rNull := by by_contra h; exact hP (ne_rNull_iff.1 h)
    subst hP0
    rw [addFirst_rNull, relPi_rNull]
    have : Z ×ᵣ (rNull : (α → (α → α → Prop) → Prop) → (α → (α → α → Prop) → Prop) → Prop) =
        rNull := by
      by_contra h
      obtain ⟨-, ⟨_, _, h'⟩⟩ := rEx_rtimes.1 (ne_rNull_iff.1 h)
      exact rNull_apply _ _ h'
    rw [this]; exact smor_rNull_iff'.2 rfl

/-! #### `P exp Q` -/

private theorem rexp_eq (P : α → α → Prop) (Q : β → β → Prop) :
    rexp P Q = prodR (coupleSemi P ⁏ Q) := rfl

private theorem smor_rexp_relPi (P : α → α → Prop) (Q : β → β → Prop) :
    smor (rexp P Q) (relPi (coupleSemi P ⁏ Q)) :=
  smor_prodR_relPi (coupleSemi_rel2excl P Q)

private theorem opSemi_inj {P : α → α → Prop} (hP : rEx P) :
    Function.Injective (opSemi couple P : β → _) := by
  intro z w h
  obtain ⟨x, y, hxy⟩ := hP
  have : opSemi couple P w (x ↓ z) (y ↓ z) := by
    rw [← h]; exact (opSemi_couple_apply P z _ _).2 ⟨x, y, ⟨rfl, rfl⟩, hxy⟩
  obtain ⟨u, v, ⟨e, -⟩, -⟩ := (opSemi_couple_apply P w _ _).1 this
  exact (couple_eq_iff.1 e).2

private theorem opSemi_rNull (z : β) : opSemi couple (rNull : α → α → Prop) z = rNull :=
  graph_semi_rNull _

private theorem rexp_rNull_left {Q : β → β → Prop} (hQ : rEx Q) :
    rexp (rNull : α → α → Prop) Q = rNull := by
  show D ⁏ relPi _ = rNull
  obtain ⟨z, w, hzw⟩ := hQ
  rw [relPi_eq_rNull_of_mem (by rw [fld_coupleSemi_mem]; exact ⟨z, ⟨w, Or.inl hzw⟩,
    (opSemi_rNull z).symm⟩)]
  exact graph_semi_rNull _

private theorem rexp_rNull_right (P : α → α → Prop) :
    rexp P (rNull : β → β → Prop) = rNull := by
  show D ⁏ relPi (coupleSemi P ⁏ rNull) = rNull
  rw [show coupleSemi P = graph (opSemi couple P) from rfl, graph_semi_rNull, relPi_rNull]
  exact graph_semi_rNull _

/-- `P smor P' . Q smor Q' . ⊃ . P exp Q smor P' exp Q'` (✱176·22). -/
private theorem smor_rexp {P : α → α → Prop} {P' : γ → γ → Prop} {Q : β → β → Prop}
    {Q' : δ → δ → Prop} (hP : smor P P') (hQ : smor Q Q') : smor (rexp P Q) (rexp P' Q') := by
  refine smor_trans (smor_rexp_relPi P Q) (smor_trans ?_ (smor_symm (smor_rexp_relPi P' Q')))
  obtain ⟨T₁, ⟨a₁, b₁⟩, hc₁, rfl⟩ := smor_corr hQ
  obtain ⟨T₂, ⟨a₂, b₂⟩, hc₂, rfl⟩ := smor_corr hP
  let U : (α → β → Prop) → (γ → δ → Prop) → Prop :=
    fun u a => ∃ x z x' z', (u = x ↓ z ∧ a = x' ↓ z') ∧ T₂ x x' ∧ T₁ z z'
  refine smor_relPi_of (T := U) ?_ ?_ ?_ ?_
  · rintro u v a ⟨x, z, x', z', ⟨rfl, rfl⟩, hx, hz⟩ ⟨y, w, y', w', ⟨rfl, e'⟩, hy, hw⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e'
    rw [a₂ x y x' hx hy, a₁ z w z' hz hw]
  · rintro u a b ⟨x, z, x', z', ⟨rfl, rfl⟩, hx, hz⟩ ⟨y, w, y', w', ⟨e', rfl⟩, hy, hw⟩
    obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e'
    rw [b₂ x x' y' hx hy, b₁ z z' w' hz hw]
  · intro Y hY y hy
    obtain ⟨z', hz', rfl⟩ := fld_coupleSemi_mem.1 hY
    rw [fld_opSemi_couple] at hy
    obtain ⟨x', hx', rfl⟩ := hy
    obtain ⟨x, hx⟩ := (hc₂ x').1 hx'
    obtain ⟨z, hz⟩ := (hc₁ z').1 hz'
    exact ⟨x ↓ z, x, z, x', z', ⟨rfl, rfl⟩, hx, hz⟩
  · rw [daggerRel_eq_graph]
    show graph (opSemi couple (T₂ ⁏ P')) ⁏ (T₁ ⁏ Q') = graph _ ⁏ (graph (opSemi couple P') ⁏ Q')
    rw [semi_semi, semi_semi, graph_relProd_graph]
    refine semi_congr fun X z' hz' => ?_
    obtain ⟨z, hz⟩ := (hc₁ z').1 hz'
    have hzu : ∀ w, T₁ w z' → w = z := fun w hw => a₁ w z z' hw hz
    constructor
    · rintro ⟨w, rfl, hw⟩
      rw [hzu w hw]
      show opSemi couple (T₂ ⁏ P') z = U ⁏ opSemi couple P' z'
      funext u v; apply propext
      rw [opSemi_couple_apply, semi_apply]
      constructor
      · rintro ⟨x, y, ⟨rfl, rfl⟩, hxy⟩
        obtain ⟨x', y', ⟨hx, hy⟩, hxy'⟩ := (semi_apply _ _ _ _).1 hxy
        exact ⟨x' ↓ z', y' ↓ z', ⟨⟨x, z, x', z', ⟨rfl, rfl⟩, hx, hz⟩, ⟨y, z, y', z', ⟨rfl, rfl⟩, hy, hz⟩⟩,
          (opSemi_couple_apply _ _ _ _).2 ⟨x', y', ⟨rfl, rfl⟩, hxy'⟩⟩
      · rintro ⟨a, b, ⟨⟨x, w, x', w', ⟨rfl, rfl⟩, hx, hw⟩, ⟨y, w₂, y', w₂', ⟨rfl, rfl⟩, hy, hw₂⟩⟩, hab⟩
        obtain ⟨x₀, y₀, ⟨e1, e2⟩, hxy⟩ := (opSemi_couple_apply _ _ _ _).1 hab
        obtain ⟨ex, ew⟩ := couple_eq_iff.1 e1
        obtain ⟨ey, ew₂⟩ := couple_eq_iff.1 e2
        subst ex ey
        rw [ew] at hw; rw [ew₂] at hw₂
        rw [hzu w hw, hzu w₂ hw₂]
        exact ⟨x, y, ⟨rfl, rfl⟩, (semi_apply _ _ _ _).2 ⟨x', y', ⟨hx, hy⟩, hxy⟩⟩
    · intro hX
      refine ⟨z, ?_, hz⟩
      have hX' : X = U ⁏ opSemi couple P' z' := hX
      rw [hX']
      funext u v; apply propext
      rw [opSemi_couple_apply, semi_apply]
      constructor
      · rintro ⟨a, b, ⟨⟨x, w, x', w', ⟨rfl, rfl⟩, hx, hw⟩, ⟨y, w₂, y', w₂', ⟨rfl, rfl⟩, hy, hw₂⟩⟩, hab⟩
        obtain ⟨x₀, y₀, ⟨e1, e2⟩, hxy⟩ := (opSemi_couple_apply _ _ _ _).1 hab
        obtain ⟨ex, ew⟩ := couple_eq_iff.1 e1
        obtain ⟨ey, ew₂⟩ := couple_eq_iff.1 e2
        subst ex ey
        rw [ew] at hw; rw [ew₂] at hw₂
        rw [hzu w hw, hzu w₂ hw₂]
        exact ⟨x, y, ⟨rfl, rfl⟩, (semi_apply _ _ _ _).2 ⟨x', y', ⟨hx, hy⟩, hxy⟩⟩
      · rintro ⟨x, y, ⟨rfl, rfl⟩, hxy⟩
        obtain ⟨x', y', ⟨hx, hy⟩, hxy'⟩ := (semi_apply _ _ _ _).1 hxy
        exact ⟨x' ↓ z', y' ↓ z', ⟨⟨x, z, x', z', ⟨rfl, rfl⟩, hx, hz⟩, ⟨y, z, y', z', ⟨rfl, rfl⟩, hy, hz⟩⟩,
          (opSemi_couple_apply _ _ _ _).2 ⟨x', y', ⟨rfl, rfl⟩, hxy'⟩⟩

/-- `P^Q smor P exp Q` (✱176·181). -/
private theorem smor_rpow_rexp (P : α → α → Prop) (Q : β → β → Prop) : smor (rpow P Q) (rexp P Q) := by
  refine smor_graph fun A B hA hB h => ?_
  have couples : ∀ A, A ∈ fld (rexp P Q) → ∀ c, c ∈ A → ∃ x z, c = x ↓ z := by
    intro A hA c hc
    obtain ⟨M, hM, rfl⟩ := mem_fld_graph_semi.1 hA
    obtain ⟨Y, hcY⟩ := hc
    obtain ⟨⟨-, m2⟩, m3⟩ := mem_selF.1 (mem_fld_relPi hM)
    obtain ⟨z, -, rfl⟩ := fld_coupleSemi_mem.1 ((m3 Y).2 ⟨c, hcY⟩)
    have := m2 c _ hcY
    rw [fld_opSemi_couple] at this
    obtain ⟨x, -, rfl⟩ := this
    exact ⟨x, z, rfl⟩
  have key : ∀ A B, A ∈ fld (rexp P Q) → B ∈ fld (rexp P Q) → sumRel A = sumRel B →
      ∀ c, c ∈ A → c ∈ B := by
    intro A B hA hB h c hc
    obtain ⟨x, z, rfl⟩ := couples A hA c hc
    have : sumRel B x z := by rw [← h]; exact ⟨_, hc, rfl, rfl⟩
    obtain ⟨c', hc', hxz⟩ := this
    obtain ⟨x', z', rfl⟩ := couples B hB c' hc'
    obtain ⟨rfl, rfl⟩ := hxz
    exact hc'
  exact Set.ext fun c => ⟨key A B hA hB h c, key B A hB hA h.symm c⟩

end Helpers185c

section Helpers185d

private theorem piNr_eq_n₀r {W : Type*} {P' : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : AdeqPiNr W P') (P : (α → α → Prop) → (α → α → Prop) → Prop) :
    ∃ X : W → W → Prop, smor X (relPi P) ∧ piNr W P = n₀r X := by
  obtain ⟨X, hX⟩ := h.piNr_nonempty P
  exact ⟨X, hX, nr_eq_n₀r_of_mem hX⟩

private theorem rtimes_rNull_left (Z : β → β → Prop) :
    (rNull : α → α → Prop) ×ᵣ Z = rNull := by
  by_contra h
  obtain ⟨⟨_, _, h'⟩, -⟩ := rEx_rtimes.1 (ne_rNull_iff.1 h)
  exact rNull_apply _ _ h'

private theorem rtimes_rNull_right (Z : β → β → Prop) :
    Z ×ᵣ (rNull : α → α → Prop) = rNull := by
  by_contra h
  obtain ⟨-, ⟨_, _, h'⟩⟩ := rEx_rtimes.1 (ne_rNull_iff.1 h)
  exact rNull_apply _ _ h'

/-- An existent selection from `C'P` exists when no member of `C'P` is `Λ̇` (`Mult ax`, here
`Classical.choice`). -/
private theorem exists_sel {P : (α → α → Prop) → (α → α → Prop) → Prop}
    (h : rNull ∉ fld P) : ∃ M, M ∈ sel F (fld P) := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · refine ⟨fun _ _ => False, mem_selF.2 ⟨⟨fun _ _ _ h _ => h.elim, fun _ _ h => h.elim⟩,
      fun Q => ⟨fun hQ => ?_, fun ⟨_, h'⟩ => h'.elim⟩⟩⟩
    have : Q = rNull := funext fun x => isEmptyElim x
    exact absurd (this ▸ hQ) h
  refine ⟨fun x Q => Q ∈ fld P ∧ x = Classical.epsilon (· ∈ fld Q), mem_selF.2 ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rintro x y Q ⟨-, rfl⟩ ⟨-, rfl⟩; rfl
  · rintro x Q ⟨hQ, rfl⟩
    have hne : Q ≠ rNull := fun e => h (e ▸ hQ)
    obtain ⟨u, hu⟩ := rEx_iff_fld.1 (ne_rNull_iff.1 hne)
    exact Classical.epsilon_spec ⟨u, hu⟩
  · intro Q
    exact ⟨fun hQ => ⟨_, hQ, rfl⟩, fun ⟨x, hQ, _⟩ => hQ⟩

private theorem sm_empty_empty : sm (∅ : Set γ) (∅ : Set δ) := by
  refine sm_iff.2 ⟨rNull, ⟨mem_arrow_one_one.2 ⟨fun _ _ _ h => absurd h.1 (rNull_apply _ _),
    fun _ _ _ h => absurd h.1 (rNull_apply _ _)⟩, ?_⟩, ?_⟩ <;>
  · ext x; simp only [Set.mem_empty_iff_false, false_iff]; rintro ⟨_, h⟩; exact rNull_apply _ _ h

end Helpers185d

/-!
## [✱185] The product of the relation-numbers of a field

*(Vol. 2, p. 505)*

> *Summary of* *185.
>
> The subject of this number is analogous to part of the subject of *114. The propositions concerned are immediate consequences of previously proved properties of \(\Pi ʻP\), and offer no difficulty of any kind.

**Lean reading.** `ΠNr'P` is `piNr γ P` (`= nr γ (relPi P)`); `Π;P` is `RelPi ⁏ P`, `S exp R` is `rexp S R`,
`0 ∪ 1` is `zero ∪ one`, `J` is diversity. `Mult ax` is a hypothesis where PM has it, at the type
of the correlators (✱185·27·28·29) or of the members chosen (✱185·25); it is not used in the Lean
proofs (`Classical.choice`). The `ΠNr` and `Nr` of arithmetical components have their own
adequate types (IIT). ✱185·4·41 are false as printed when `Λ̇ ∈ C'P` (then `Π'Λ̇ = Λ̇` is in
`C'Π;P` but `Λ̇` contributes nothing to `Σ'P`).

**Status.** proved (all propositions except ✱185·4·41; ✱185·01 definition; ✱185·31·32·321 proved (reading); ✱185·4·41 stated (open here), with the counterexamples to the printed forms proved), see their docstrings
-/

/-- ✱185·01 (Df). \(\Pi \text{Nr}ʻP=\text{Nr}ʻ\Pi ʻP \quad\text{Df}\) -/
theorem pm185_01 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    piNr γ P = nr γ (relPi P) := rfl

/-- ✱185·1. \(\vdash .\Pi \text{Nr}ʻP=\text{Nr}ʻ\Pi ʻP \quad[(*185·01)]\) -/
theorem pm185_1 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    piNr γ P = nr γ (relPi P) := rfl

/-- ✱185·11. \(\vdash :P \,\,\text{smor}\, \,\text{smor}\, Q.\supset .\Pi \text{Nr}ʻP=\Pi \text{Nr}ʻQ \quad[*172·44]\) -/
theorem pm185_11 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} :
    smorsmor P Q → piNr γ P = piNr γ Q := fun h =>
  nr_eq_nr_of_smor (smor_relPi_of_smorsmor h)

/-- ✱185·12. \(\vdash .\Pi \text{Nr}ʻP=\text{Nr}ʻ\text{Prod}ʻ\breve{\downarrow}_{.,}^{;}P=\text{Nr}ʻ\Pi ʻ\breve{\downarrow}_{.,}^{;}P \quad[*182·44]\) -/
theorem pm185_12 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    piNr γ P = nr γ (prodR (sepRel P)) ∧ nr γ (prodR (sepRel P)) = nr γ (relPi (sepRel P)) :=
  pm182_44

/-- ✱185·2. \(\vdash .\Pi \text{Nr}ʻ\dot{\Lambda} =0_{r} \quad[*172·13]\) -/
theorem pm185_2 : piNr γ (rNull : (α → α → Prop) → (α → α → Prop) → Prop) = zero_r := by
  rw [piNr, relPi_rNull, ← zero_r_eq_nr]

/-- ✱185·21. \(\vdash .\Pi \text{Nr}ʻ(P\downarrow P)=\text{Nr}ʻP \quad[*172·2.*165·251]\) -/
theorem pm185_21 {P : α → α → Prop} : piNr γ (P ↓ P) = nr γ P := by
  rw [piNr, relPi_couple_self]; exact nr_eq_nr_of_smor (smor_sep P)

/-- ✱185·22. \(\vdash .\Pi \text{Nr}ʻ(\dot{\Lambda} \downarrow \dot{\Lambda} )=0_{r} \quad[*185·21]\) -/
theorem pm185_22 : piNr γ ((rNull : α → α → Prop) ↓ (rNull : α → α → Prop)) = zero_r := by
  rw [pm185_21, ← zero_r_eq_nr]

/-- ✱185·23. \(\vdash :\dot{\Lambda} \in CʻP.\supset .\Pi \text{Nr}ʻP=0_{r} \quad [*172·14]\) -/
theorem pm185_23 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    rNull ∈ fld P → piNr γ P = zero_r := fun h => by
  rw [piNr, relPi_eq_rNull_of_mem h, ← zero_r_eq_nr]

/-- ✱185·25. \(\vdash \colon\colon\text{Mult ax}.\supset \colon\ldotp \Pi \text{Nr}ʻP=0_{r}.\equiv :\dot{\Lambda} \in CʻP.\lor.P=\dot{\Lambda} \quad[*172·182]\)

`Mult ax` at the type of the members of the fields of the members of `C'P`. -/
theorem pm185_25 {P : (α → α → Prop) → (α → α → Prop) → Prop} (_hm : MultAx α) :
    piNr γ P = zero_r ↔ rNull ∈ fld P ∨ P = rNull := by
  constructor
  · intro h
    rw [piNr, nr_eq_zero_r_iff] at h
    by_contra hc
    push Not at hc
    obtain ⟨M, hM⟩ := exists_sel hc.1
    obtain ⟨N, hN⟩ := sel_mem_fld_relPi (ne_rNull_iff.1 hc.2) hM
    rw [h] at hN
    exact hN.elim (rNull_apply _ _) (rNull_apply _ _)
  · rintro (h | rfl)
    · exact pm185_23 h
    · exact pm185_2

/-- ✱185·27. \[\begin{align}\vdash \colon\ldotp \text{Mult ax}.\supset :P,Q\in &\text{Rel}^{2}\text{excl}.\exists !P\,\overline{\,\text{smor}\,}\,Q\cap \text{Rl}ʻ\,\text{smor}\,.\supset .\\ &\Pi \text{Nr}ʻP=\Pi \text{Nr}ʻQ \quad[*172·45]\end{align}\]

`Mult ax` at the type of the correlators of members of `C'P` with members of `C'Q`. -/
theorem pm185_27 {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : (β → β → Prop) → (β → β → Prop) → Prop} (_hm : MultAx (α → β → Prop)) :
    (P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ (smorbar P Q ∩ rl smor).Nonempty →
      piNr γ P = piNr γ Q := by
  rintro ⟨⟨hP, hQ⟩, S, hS, hSs⟩
  exact pm185_11 (smorsmor_of_corr hP hQ hS hSs)

/-- ✱185·28. \[\begin{align}\vdash \colon\ldotp \text{Mult ax}.\supset :P,Q\in &\text{Rel}^{2}\text{excl}.P,Q\in \text{Nr}ʻR.CʻP,CʻQ\in \text{Cl}ʻ\text{Nr}ʻS.\supset .\\ &\Pi \text{Nr}ʻP=\Pi \text{Nr}ʻQ \quad[*164·48.*185·11]\end{align}\]

`Mult ax` at the type of the correlators of members of `C'P` with members of `C'Q`. -/
theorem pm185_28 {ζ ξ : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop}
    {R : ζ → ζ → Prop} {S : ξ → ξ → Prop} (_hm : MultAx (α → α → Prop)) :
    ((P ∈ Rel2excl ∧ Q ∈ Rel2excl) ∧ (P ∈ nr (α → α → Prop) R ∧ Q ∈ nr (α → α → Prop) R)) ∧
      (fld P ∈ cl (nr α S) ∧ fld Q ∈ cl (nr α S)) → piNr γ P = piNr γ Q := by
  rintro ⟨⟨⟨hP, hQ⟩, ⟨hPR, hQR⟩⟩, hPS, hQS⟩
  obtain ⟨T, hT⟩ := smor_trans hPR (smor_symm hQR)
  refine pm185_11 (smorsmor_of_corr hP hQ hT fun X Y hXY => ?_)
  obtain ⟨⟨-, hc⟩, hTe⟩ := hT
  have hY : Y ∈ fld Q := by rw [hc]; exact ⟨X, hXY⟩
  have hX : X ∈ fld P := by
    rw [hTe]; exact (mem_fld_semi fun z hz => by rw [hc] at hz; exact hz).2 ⟨Y, hY, hXY⟩
  exact smor_trans (hPS hX) (smor_symm (hQS hY))

/-- ✱185·29. \[\begin{align}\vdash \colon\ldotp \text{Mult ax}.\supset :P\in &\text{Rel}^{2}\text{excl}.P\in \text{Nr}ʻR.CʻP\subset \text{Nr}ʻS.\supset .\\ &\Pi \text{Nr}ʻP=\text{Nr}ʻ(S\,\text{exp}\,\,R) \quad[*176·24]\end{align}\]

`Mult ax` at the type `α → (ξ → ζ → Prop) → Prop` of the correlators of the fields of members
of `C'P` (on `α`) with the fields of members of `C'S↓.,;R` (couples `x ↓ z : ξ → ζ → Prop`). -/
theorem pm185_29 {ζ ξ : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {R : ζ → ζ → Prop} {S : ξ → ξ → Prop} (_hm : MultAx (α → (ξ → ζ → Prop) → Prop)) :
    (P ∈ Rel2excl ∧ P ∈ nr (α → α → Prop) R) ∧ fld P ⊆ nr α S →
      piNr γ P = nr γ (rexp S R) := by
  rintro ⟨⟨hP, hPR⟩, hPS⟩
  by_cases hS : rEx S
  · have hX : smor (coupleSemi S ⁏ R) R := smor_coupleSemi hS R
    obtain ⟨T, hT⟩ := smor_trans hPR (smor_symm hX)
    have hss : smorsmor P (coupleSemi S ⁏ R) := by
      refine smorsmor_of_corr hP (coupleSemi_rel2excl S R) hT fun A B hAB => ?_
      obtain ⟨⟨-, hc⟩, hTe⟩ := hT
      have hB : B ∈ fld (coupleSemi S ⁏ R) := by rw [hc]; exact ⟨A, hAB⟩
      have hA : A ∈ fld P := by
        rw [hTe]; exact (mem_fld_semi fun z hz => by rw [hc] at hz; exact hz).2 ⟨B, hB, hAB⟩
      obtain ⟨z, -, rfl⟩ := fld_coupleSemi_mem.1 hB
      exact smor_trans (hPS hA) (smor_symm (smor_opSemi S z))
    rw [piNr]
    exact nr_eq_nr_of_smor (smor_trans (smor_relPi_of_smorsmor hss)
      (smor_symm (smor_rexp_relPi S R)))
  · have hS0 : S = rNull := by by_contra h; exact hS (ne_rNull_iff.1 h)
    subst hS0
    by_cases hR : rEx R
    · rw [rexp_rNull_left hR, ← zero_r_eq_nr]
      obtain ⟨Q, hQ⟩ := rEx_iff_fld.1 (smor_preserves (smor_symm hPR) hR)
      have := smor_rNull_iff'.1 (hPS hQ)
      subst this
      exact pm185_23 hQ
    · have hR0 : R = rNull := by by_contra h; exact hR (ne_rNull_iff.1 h)
      subst hR0
      have hP0 : P = rNull := smor_rNull_iff'.1 hPR
      subst hP0
      rw [rexp_rNull_right, pm185_2, ← zero_r_eq_nr]

/-- ✱185·31. \[\begin{align}&\vdash :\dot{\exists} !P.\dot{\exists} !Q.CʻP\cap CʻQ=\Lambda .\supset .\Pi \text{Nr}ʻ(P\unicode{x2909}Q)=\Pi \text{Nr}ʻP\dot{\times} \Pi \text{Nr}ʻQ\\ &[*172·35]\end{align}\]

`ΠNr'P`, `ΠNr'Q` are arithmetical components with their own adequate types (IIT).

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components ΠNr'P, ΠNr'Q are adequate -/
theorem pm185_31 {W₁ W₂ : Type*} {P Q : (α → α → Prop) → (α → α → Prop) → Prop}
    (h₁ : AdeqPiNr W₁ P) (h₂ : AdeqPiNr W₂ Q) :
    (rEx P ∧ rEx Q) ∧ fld P ∩ fld Q = Λ →
      piNr γ (P ⤉ Q) = (piNr W₁ P ⨰ piNr W₂ Q : Set (γ → γ → Prop)) := by
  rintro ⟨⟨hP, hQ⟩, hPQ⟩
  obtain ⟨X₁, hX₁, e₁⟩ := piNr_eq_n₀r h₁ P
  obtain ⟨X₂, hX₂, e₂⟩ := piNr_eq_n₀r h₂ Q
  rw [e₁, e₂, n₀r_nrMul_n₀r, piNr]
  exact nr_eq_nr_of_smor (smor_trans (relPi_rsum_smor hP hQ (inter_null_iff.1 hPQ))
    (smor_rtimes (smor_symm hX₁) (smor_symm hX₂)))

/-- ✱185·32. \(\vdash :Z{\sim}\in CʻP.\supset .\Pi \text{Nr}ʻ(P\unicode{x21f8} Z)=\Pi \text{Nr}ʻP\dot{\times} \text{Nr}ʻZ \quad[*172·32]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component ΠNr'P is adequate -/
theorem pm185_32 {W : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    (h : AdeqPiNr W P) : Z ∉ fld P →
      piNr γ (P ⇸ Z) = (piNr W P ⨰ n₀r Z : Set (γ → γ → Prop)) := by
  intro hZ
  obtain ⟨X, hX, e⟩ := piNr_eq_n₀r h P
  rw [e, n₀r_nrMul_n₀r, piNr]
  exact nr_eq_nr_of_smor (smor_trans (relPi_addLast_smor hZ) (smor_rtimes (smor_symm hX)
    (smor_refl Z)))

/-- ✱185·321. \(\vdash :Z{\sim}\in CʻP.\supset .\Pi \text{Nr}ʻ(Z\unicode{x21f7}P)=\text{Nr}ʻZ\dot{\times} \Pi \text{Nr}ʻP \quad[*172·321]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual type of the
arithmetical component ΠNr'P is adequate -/
theorem pm185_321 {W : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop} {Z : α → α → Prop}
    (h : AdeqPiNr W P) : Z ∉ fld P →
      piNr γ (Z ⇷ P) = (n₀r Z ⨰ piNr W P : Set (γ → γ → Prop)) := by
  intro hZ
  obtain ⟨X, hX, e⟩ := piNr_eq_n₀r h P
  rw [e, n₀r_nrMul_n₀r, piNr]
  exact nr_eq_nr_of_smor (smor_trans (relPi_addFirst_smor hZ) (smor_rtimes (smor_refl Z)
    (smor_symm hX)))

/-- ✱185·35. \(\vdash :P\neq Q.\supset .\Pi \text{Nr}ʻ(P\downarrow Q)=\text{Nr}ʻP\dot{\times} \text{Nr}ʻQ \quad [*172·23]\) -/
theorem pm185_35 {P Q : α → α → Prop} :
    P ≠ Q → piNr γ (P ↓ Q) = (n₀r P ⨰ n₀r Q : Set (γ → γ → Prop)) := fun h => by
  rw [n₀r_nrMul_n₀r, piNr]; exact nr_eq_nr_of_smor (relPi_couple_smor h)

/-- The relation of relations of relations `(Q₀ ↓ Q₀) ↓ Λ̇` (`Q₀ = x ↓ y`, `x ≠ y`) refutes the
printed ✱185·4·41: `Λ̇ = Π'Λ̇` is in `C'Π;P`, so `ΠNr'Π;P = 0_r`, while `Σ'P = Q₀ ↓ Q₀` and
`ΠNr'Σ'P = Nr'Q₀`. -/
private theorem pm185_aux_counter :
    let Q₀ : Bool → Bool → Prop := true ↓ false
    let P : ((Bool → Bool → Prop) → (Bool → Bool → Prop) → Prop) →
        ((Bool → Bool → Prop) → (Bool → Bool → Prop) → Prop) → Prop := (Q₀ ↓ Q₀) ↓ rNull
    (P ∈ Rel2excl ∧ P ⪽ J ∧ ∀ Q, P Q Q → fld Q ∈ (zero ∪ one : Set (Set (Bool → Bool → Prop)))) ∧
      piNr Bool (RelPi ⁏ P) ≠ piNr Bool (relSigma P) := by
  intro Q₀ P
  have hne : (Q₀ ↓ Q₀ : (Bool → Bool → Prop) → (Bool → Bool → Prop) → Prop) ≠ rNull := fun e =>
    rNull_apply Q₀ Q₀ (e ▸ (⟨rfl, rfl⟩ : (Q₀ ↓ Q₀) Q₀ Q₀))
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rintro X Y ⟨⟨hX, hY⟩, hXY⟩
    rw [fld_couple] at hX hY
    rw [inter_null_iff]
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact absurd rfl hXY
    · rw [fld_rNull]; exact Set.disjoint_empty _
    · rw [fld_rNull]; exact Set.empty_disjoint _
    · exact absurd rfl hXY
  · rintro R S ⟨rfl, rfl⟩; exact hne
  · rintro Q ⟨h1, h2⟩; exact absurd (h1.symm.trans h2) hne
  · intro e
    have h1 : piNr Bool (RelPi ⁏ P) = zero_r := by
      rw [piNr, show RelPi ⁏ P = relPi (Q₀ ↓ Q₀) ↓ relPi rNull from graph_semi_couple _ _ _,
        relPi_eq_rNull_of_mem (by rw [fld_couple, relPi_rNull]; exact Or.inr rfl), ← zero_r_eq_nr]
    have h2 : Q₀ ∈ piNr Bool (relSigma P) := by
      rw [piNr, show relSigma P = (Q₀ ↓ Q₀) ⤉ rNull from relSigma_couple _ _, rsum_rNull,
        relPi_couple_self]
      exact smor_symm (smor_sep Q₀)
    rw [← e, h1] at h2
    exact rNull_apply true false ((h2 : Q₀ = rNull) ▸ (⟨rfl, rfl⟩ : Q₀ true false))

/-- The printed form of ✱185·4 is false (`pm185_aux_counter`). -/
theorem pm185_4_printed_false : ¬ ∀ P : ((Bool → Bool → Prop) → (Bool → Bool → Prop) → Prop) →
    ((Bool → Bool → Prop) → (Bool → Bool → Prop) → Prop) → Prop,
    P ∈ Rel2excl ∧ (∀ Q, P Q Q → fld Q ∈ (zero ∪ one : Set (Set (Bool → Bool → Prop)))) →
      piNr Bool (RelPi ⁏ P) = piNr Bool (relSigma P) := fun h =>
  pm185_aux_counter.2 (h _ ⟨pm185_aux_counter.1.1, pm185_aux_counter.1.2.2⟩)

/-- The printed form of ✱185·41 is false (`pm185_aux_counter`). -/
theorem pm185_41_printed_false : ¬ ∀ P : ((Bool → Bool → Prop) → (Bool → Bool → Prop) → Prop) →
    ((Bool → Bool → Prop) → (Bool → Bool → Prop) → Prop) → Prop,
    P ∈ Rel2excl ∧ P ⪽ J → piNr Bool (RelPi ⁏ P) = piNr Bool (relSigma P) := fun h =>
  pm185_aux_counter.2 (h _ ⟨pm185_aux_counter.1.1, pm185_aux_counter.1.2.1⟩)

/-- ✱185·4. \[\begin{align}&\vdash \colon\ldotp P\in \text{Rel}^{2}\text{excl}:QPQ.\supset _{Q}.CʻQ\in 0\cup 1:\supset .\Pi \text{Nr}ʻ\Pi ^{;}P=\Pi \text{Nr}ʻ\Sigma ʻP\\ &[*174·241]\end{align}\]

**Status.** stated (open here): PM's statement is false when `Λ̇ ∈ C'P` (`Π'Λ̇ = Λ̇ ∈ C'Π;P` gives
`ΠNr'Π;P = 0_r`, while `Λ̇` contributes nothing to `Σ'P`; `pm185_4_printed_false`); the
corrected statement, with the further hypothesis `Λ̇ ∼∈ C'P`, is stated; its proof (the
associative law of `Π`, ✱174·241) is not given here -/
def pm185_4 : Prop :=
  ∀ {α : Type u} {γ : Type w}
    {P : ((α → α → Prop) → (α → α → Prop) → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) → Prop},
    ((P ∈ Rel2excl ∧ rNull ∉ fld P) ∧ ∀ Q, P Q Q → fld Q ∈ (zero ∪ one : Set (Set (α → α → Prop)))) →
      piNr γ (RelPi ⁏ P) = piNr γ (relSigma P)

/-- ✱185·41. \(\vdash :P\in \text{Rel}^{2}\text{excl}.P\,\unicode{x2abd}\, J.\supset .\Pi \text{Nr}ʻ\Pi ^{;}P=\Pi \text{Nr}ʻ\Sigma ʻP \quad[*174·25]\)

**Status.** stated (open here): false as printed when `Λ̇ ∈ C'P` (`pm185_41_printed_false`); the
corrected statement (with `Λ̇ ∼∈ C'P`) is stated, its proof (✱174·25) is not given here -/
def pm185_41 : Prop :=
  ∀ {α : Type u} {γ : Type w}
    {P : ((α → α → Prop) → (α → α → Prop) → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) → Prop},
    (P ∈ Rel2excl ∧ rNull ∉ fld P) ∧ P ⪽ J → piNr γ (RelPi ⁏ P) = piNr γ (relSigma P)

/-- ✱185·5. \(\vdash : P \in \text{Rel}^{2}\text{excl} . \dot{\exists} ! P . \supset . Cʻʻ\Pi \text{Nr}ʻP = \Pi \text{Nc}ʻCʻʻCʻP\) -/
theorem pm185_5 {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ∧ rEx P → C ʻʻ piNr γ P = piNc γ (C ʻʻ fld P) := by
  rintro ⟨hP, hPe⟩
  rw [piNr, C_img_nr, piNc]
  apply nc_eq_nc_of_sm
  by_cases h0 : rNull ∈ fld P
  · rw [relPi_eq_rNull_of_mem h0, fld_rNull]
    have : sel memRel (C ʻʻ fld P) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun M hM => ?_
      obtain ⟨⟨-, hM2⟩, hM3⟩ := hM
      have hA : (∅ : Set α) ∈ C ʻʻ fld P := ⟨rNull, h0, fld_rNull.symm⟩
      rw [(hM3 : C ʻʻ fld P = codom M)] at hA
      obtain ⟨x, hx⟩ := hA
      exact absurd (hM2 x _ hx) (Set.notMem_empty x)
    rw [this]; exact sm_empty_empty
  · rw [fld_relPi_eq hPe]
    have hfinj : ∀ Q R, Q ∈ fld P → R ∈ fld P → fld Q = fld R → Q = R := by
      intro Q R hQ hR e
      by_contra hne
      have hQne : Q ≠ rNull := fun e' => h0 (e' ▸ hQ)
      obtain ⟨x, hx⟩ := rEx_iff_fld.1 (ne_rNull_iff.1 hQne)
      exact hne (rel2excl_eq hP hQ hR hx (e ▸ hx))
    refine sm_symm (sm_of_inj_img (fun M x A => ∃ Q, (Q ∈ fld P ∧ A = fld Q) ∧ M x Q) ?_ ?_)
    · intro M N hM hN e
      funext x Q; apply propext
      have key : ∀ {M N : α → (α → α → Prop) → Prop}, M ∈ sel F (fld P) →
          (fun x A => ∃ Q, (Q ∈ fld P ∧ A = fld Q) ∧ M x Q) =
            (fun x A => ∃ Q, (Q ∈ fld P ∧ A = fld Q) ∧ N x Q) → M x Q → N x Q := by
        intro M N hM e hx
        have hQ := (mem_selF.1 hM).2 Q |>.2 ⟨x, hx⟩
        have : ∃ Q', (Q' ∈ fld P ∧ fld Q = fld Q') ∧ N x Q' := by
          rw [← congrFun (congrFun e x) (fld Q)]; exact ⟨Q, ⟨hQ, rfl⟩, hx⟩
        obtain ⟨Q', ⟨hQ', ef⟩, hN⟩ := this
        rw [hfinj Q Q' hQ hQ' ef]; exact hN
      exact ⟨key hM e, key hN e.symm⟩
    · intro N
      constructor
      · intro hN
        obtain ⟨⟨hN1, hN2⟩, hN3⟩ := hN
        refine ⟨fun x Q => Q ∈ fld P ∧ N x (fld Q), mem_selF.2 ⟨⟨?_, ?_⟩, fun Q => ?_⟩, ?_⟩
        · rintro x y Q ⟨-, hx⟩ ⟨-, hy⟩
          exact (mem_arrow_one_Cls.1 hN1) x y _ ⟨hx, hy⟩
        · rintro x Q ⟨-, hx⟩; exact hN2 x _ hx
        · constructor
          · intro hQ
            have : fld Q ∈ codom N := by rw [← (hN3 : C ʻʻ fld P = codom N)]; exact ⟨Q, hQ, rfl⟩
            obtain ⟨x, hx⟩ := this
            exact ⟨x, hQ, hx⟩
          · rintro ⟨x, hQ, -⟩; exact hQ
        · funext x A; apply propext
          constructor
          · intro hx
            have : A ∈ codom N := ⟨x, hx⟩
            rw [← (hN3 : C ʻʻ fld P = codom N)] at this
            obtain ⟨Q, hQ, rfl⟩ := this
            exact ⟨Q, ⟨hQ, rfl⟩, hQ, hx⟩
          · rintro ⟨Q, ⟨hQ, rfl⟩, -, hx⟩; exact hx
      · rintro ⟨M, hM, rfl⟩
        obtain ⟨⟨m1, m2⟩, m3⟩ := mem_selF.1 hM
        refine ⟨⟨mem_arrow_one_Cls.2 ?_, ?_⟩, ?_⟩
        · rintro x y A ⟨⟨Q, ⟨hQ, rfl⟩, hx⟩, ⟨Q', ⟨hQ', e⟩, hy⟩⟩
          rw [hfinj Q Q' hQ hQ' e] at hx
          exact m1 x y Q' hx hy
        · rintro x A ⟨Q, ⟨-, rfl⟩, hx⟩; exact m2 x Q hx
        · ext A
          constructor
          · rintro ⟨Q, hQ, rfl⟩
            obtain ⟨x, hx⟩ := (m3 Q).1 hQ
            exact ⟨x, Q, ⟨hQ, rfl⟩, hx⟩
          · rintro ⟨x, Q, ⟨hQ, rfl⟩, -⟩; exact ⟨Q, hQ, rfl⟩


section Helpers186

private theorem n₀r_nrExp_n₀r (P : α → α → Prop) (Q : β → β → Prop) :
    (nrExp (n₀r P) (n₀r Q) : Set (γ → γ → Prop)) = nr γ (rexp P Q) := by
  ext Z
  constructor
  · rintro ⟨P', Q', ⟨hP, hQ⟩, h⟩
    exact smor_trans h (smor_rexp (n₀r_eq_n₀r_iff.1 hP.symm) (n₀r_eq_n₀r_iff.1 hQ.symm))
  · intro h; exact ⟨P, Q, ⟨rfl, rfl⟩, h⟩

private theorem nrExp_of {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} {P : α → α → Prop}
    {Q : β → β → Prop} (hμ : μ = n₀r P) (hν : ν = n₀r Q) :
    (nrExp μ ν : Set (γ → γ → Prop)) = nr γ (rexp P Q) := by
  subst hμ hν; exact n₀r_nrExp_n₀r P Q

private theorem nrExp_eq_empty_of_left {μ : Set (α → α → Prop)} (h : ∀ P, μ ≠ n₀r P)
    (ν : Set (β → β → Prop)) : (nrExp μ ν : Set (γ → γ → Prop)) = ∅ := by
  ext Z; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨P, Q, ⟨hP, -⟩, -⟩; exact h P hP

private theorem nrExp_eq_empty_of_right (μ : Set (α → α → Prop)) {ν : Set (β → β → Prop)}
    (h : ∀ Q, ν ≠ n₀r Q) : (nrExp μ ν : Set (γ → γ → Prop)) = ∅ := by
  ext Z; simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨P, Q, ⟨-, hQ⟩, -⟩; exact h Q hQ

private theorem rexp_eq_rNull_iff {P : α → α → Prop} {Q : β → β → Prop} :
    rexp P Q = rNull ↔ P = rNull ∨ Q = rNull := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hP := ne_rNull_iff.1 hc.1
    have hQ := ne_rNull_iff.1 hc.2
    have hX : rEx (coupleSemi P ⁏ Q) := rEx_graph.2 hQ
    have hn : rNull ∉ fld (coupleSemi P ⁏ Q) := by
      intro h'
      obtain ⟨z, -, e⟩ := fld_coupleSemi_mem.1 h'
      have : rEx (opSemi couple P z) := rEx_graph.2 hP
      exact ne_rNull_iff.2 this e.symm
    obtain ⟨M, hM⟩ := exists_sel hn
    have := smor_preserves (smor_symm (smor_rexp_relPi P Q))
      (rEx_iff_fld.2 ⟨M, sel_mem_fld_relPi hX hM⟩)
    rw [h] at this
    obtain ⟨_, _, h'⟩ := this; exact rNull_apply _ _ h'
  · rintro (rfl | rfl)
    · by_cases hQ : rEx Q
      · exact rexp_rNull_left hQ
      · have : Q = rNull := by by_contra h; exact hQ (ne_rNull_iff.1 h)
        subst this; exact rexp_rNull_right _
    · exact rexp_rNull_right _

/-- The members of `C'(P exp Q)` (for `∃̇!P . ∃̇!Q`): classes of couples taking one `x ∈ C'P` for
each `z ∈ C'Q` (cf. ✱176·14). -/
private theorem mem_fld_rexp {P : α → α → Prop} {Q : β → β → Prop} (hP : rEx P) (hQ : rEx Q)
    {A : Set (α → β → Prop)} : A ∈ fld (rexp P Q) ↔
      (∀ c, c ∈ A → ∃ x z, (x ∈ fld P ∧ z ∈ fld Q) ∧ c = x ↓ z) ∧
        ∀ z, z ∈ fld Q → ∃ x, x ↓ z ∈ A ∧ ∀ y, y ↓ z ∈ A → y = x := by
  have hX : rEx (coupleSemi P ⁏ Q) := rEx_graph.2 hQ
  have hfX : fld (relPi (coupleSemi P ⁏ Q)) = sel F (fld (coupleSemi P ⁏ Q)) := fld_relPi_eq hX
  have hfA : A ∈ fld (rexp P Q) ↔ ∃ M, M ∈ sel F (fld (coupleSemi P ⁏ Q)) ∧ A = dom M := by
    show A ∈ fld (graph dom ⁏ relPi _) ↔ _
    rw [mem_fld_graph_semi, hfX]
  rw [hfA]
  constructor
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨⟨m1, m2⟩, m3⟩ := mem_selF.1 hM
    refine ⟨fun c ⟨Y, hcY⟩ => ?_, fun z hz => ?_⟩
    · obtain ⟨z, hz, rfl⟩ := fld_coupleSemi_mem.1 ((m3 Y).2 ⟨c, hcY⟩)
      have := m2 c _ hcY
      rw [fld_opSemi_couple] at this
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨x, z, ⟨hx, hz⟩, rfl⟩
    · obtain ⟨c, hc⟩ := (m3 _).1 (fld_coupleSemi_mem.2 ⟨z, hz, rfl⟩)
      have := m2 c _ hc
      rw [fld_opSemi_couple] at this
      obtain ⟨x, -, rfl⟩ := this
      refine ⟨x, ⟨_, hc⟩, fun y ⟨Y, hyY⟩ => ?_⟩
      obtain ⟨w, -, rfl⟩ := fld_coupleSemi_mem.1 ((m3 Y).2 ⟨_, hyY⟩)
      have := m2 _ _ hyY
      rw [fld_opSemi_couple] at this
      obtain ⟨y', -, e⟩ := this
      obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e
      exact (couple_eq_iff.1 (m1 _ _ _ hyY hc)).1
  · rintro ⟨h1, h2⟩
    refine ⟨fun c Y => c ∈ A ∧ ∃ x z, c = x ↓ z ∧ Y = opSemi couple P z,
      mem_selF.2 ⟨⟨?_, ?_⟩, fun Y => ?_⟩, ?_⟩
    · rintro c d Y ⟨hc, x, z, rfl, rfl⟩ ⟨hd, y, w, rfl, e⟩
      have := opSemi_inj hP e; subst this
      have hz : z ∈ fld Q := by
        obtain ⟨_, _, ⟨-, hz⟩, e'⟩ := h1 _ hc
        rw [(couple_eq_iff.1 e').2]; exact hz
      obtain ⟨u, -, hu⟩ := h2 z hz
      rw [hu x hc, hu y hd]
    · rintro c Y ⟨hc, x, z, rfl, rfl⟩
      obtain ⟨_, _, ⟨hx, -⟩, e⟩ := h1 _ hc
      obtain ⟨rfl, rfl⟩ := couple_eq_iff.1 e
      rw [fld_opSemi_couple]; exact ⟨x, hx, rfl⟩
    · rw [fld_coupleSemi_mem]
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨x, hx, -⟩ := h2 z hz
        exact ⟨x ↓ z, hx, x, z, rfl, rfl⟩
      · rintro ⟨c, hc, x, z, rfl, rfl⟩
        obtain ⟨_, _, ⟨-, hz⟩, e⟩ := h1 _ hc
        exact ⟨z, (couple_eq_iff.1 e).2 ▸ hz, rfl⟩
    · ext c
      exact ⟨fun hc => by
        obtain ⟨x, z, -, rfl⟩ := h1 c hc
        exact ⟨_, hc, x, z, rfl, rfl⟩, fun ⟨_, hc, _⟩ => hc⟩

/-- In a type adequate for `μ exp_r ν`, `Nr'(P exp Q)` exists for all `P`, `Q`. -/
private theorem AdeqNrExp.nr_nonempty {W : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    (h : AdeqNrExp W μ ν) (P : α → α → Prop) (Q : β → β → Prop) :
    (nr W (rexp P Q)).Nonempty := by
  classical
  by_cases hP : rEx P
  swap
  · have : P = rNull := by by_contra h'; exact hP (ne_rNull_iff.1 h')
    rw [rexp_eq_rNull_iff.2 (Or.inl this)]; exact ⟨rNull, smor_rNull_iff'.2 rfl⟩
  by_cases hQ : rEx Q
  swap
  · have : Q = rNull := by by_contra h'; exact hQ (ne_rNull_iff.1 h')
    rw [rexp_eq_rNull_iff.2 (Or.inr this)]; exact ⟨rNull, smor_rNull_iff'.2 rfl⟩
  have h' : (nr W (rexp (rV : α → α → Prop) (rV : β → β → Prop))).Nonempty := by
    have := h; unfold AdeqNrExp at this; rwa [n₀r_nrExp_n₀r] at this
  obtain ⟨f, hf⟩ := nr_nonempty_iff.1 h'
  obtain ⟨d, -⟩ := rEx_iff_fld.1 hP
  have hrα : rEx (rV : α → α → Prop) := ⟨d, d, rfl, rfl⟩
  obtain ⟨b, -⟩ := rEx_iff_fld.1 hQ
  have hrβ : rEx (rV : β → β → Prop) := ⟨b, b, rfl, rfl⟩
  have hfV : ∀ {u : α}, u ∈ fld (rV : α → α → Prop) := fun {u} => ⟨u, Or.inl ⟨rfl, rfl⟩⟩
  have hfW : ∀ {u : β}, u ∈ fld (rV : β → β → Prop) := fun {u} => ⟨u, Or.inl ⟨rfl, rfl⟩⟩
  let ext : Set (α → β → Prop) → Set (α → β → Prop) :=
    fun A => A ∪ {c | ∃ z, z ∉ fld Q ∧ c = d ↓ z}
  have hext : ∀ A, A ∈ fld (rexp P Q) → ext A ∈ fld (rexp (rV : α → α → Prop) rV) := by
    intro A hA
    obtain ⟨h1, h2⟩ := (mem_fld_rexp hP hQ).1 hA
    refine (mem_fld_rexp hrα hrβ).2 ⟨fun c hc => ?_, fun z _ => ?_⟩
    · rcases hc with hc | ⟨z, -, rfl⟩
      · obtain ⟨x, z, -, rfl⟩ := h1 c hc; exact ⟨x, z, ⟨hfV, hfW⟩, rfl⟩
      · exact ⟨d, z, ⟨hfV, hfW⟩, rfl⟩
    · by_cases hz : z ∈ fld Q
      · obtain ⟨x, hx, hu⟩ := h2 z hz
        refine ⟨x, Or.inl hx, fun y hy => ?_⟩
        rcases hy with hy | ⟨w, hw, e⟩
        · exact hu y hy
        · exact absurd ((couple_eq_iff.1 e).2 ▸ hz) hw
      · refine ⟨d, Or.inr ⟨z, hz, rfl⟩, fun y hy => ?_⟩
        rcases hy with hy | ⟨w, -, e⟩
        · obtain ⟨_, _, ⟨-, hz'⟩, e'⟩ := h1 _ hy
          exact absurd ((couple_eq_iff.1 e').2 ▸ hz') hz
        · exact (couple_eq_iff.1 e).1
  have hinj : ∀ A B, A ∈ fld (rexp P Q) → B ∈ fld (rexp P Q) → ext A = ext B → A = B := by
    have key : ∀ A B, A ∈ fld (rexp P Q) → ext A = ext B → ∀ c, c ∈ A → c ∈ B := by
      intro A B hA e c hc
      have : c ∈ ext B := e ▸ Or.inl hc
      rcases this with h | ⟨z, hz, rfl⟩
      · exact h
      · obtain ⟨_, _, ⟨-, hz'⟩, e'⟩ := ((mem_fld_rexp hP hQ).1 hA).1 _ hc
        exact absurd ((couple_eq_iff.1 e').2 ▸ hz') hz
    intro A B hA hB e
    exact Set.ext fun c => ⟨key A B hA e c, key B A hB e.symm c⟩
  exact nr_nonempty_iff.2 ⟨fun A => f ⟨ext A, hext A A.2⟩, fun A B e =>
    Subtype.ext (hinj A B A.2 B.2 (congrArg Subtype.val (hf e)))⟩

private theorem AdeqNrExp.eq_n₀r {W : Type*} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)}
    (h : AdeqNrExp W μ ν) (P : α → α → Prop) (Q : β → β → Prop) :
    ∃ X : W → W → Prop, smor X (rexp P Q) ∧ (nrExp (n₀r P) (n₀r Q) : Set (W → W → Prop)) = n₀r X := by
  obtain ⟨X, hX⟩ := h.nr_nonempty P Q
  exact ⟨X, hX, (n₀r_nrExp_n₀r P Q).trans (nr_eq_n₀r_of_mem hX)⟩

/-- `∃̇!P . ∃̇!Q . ∃̇!R . C'Q ∩ C'R = Λ . ⊃ . P exp (Q ⤉ R) smor (P exp Q) × (P exp R)` (✱176·42). -/
private theorem smor_rexp_rsum {P : α → α → Prop} {Q R : β → β → Prop} (hP : rEx P) (hQ : rEx Q)
    (hR : rEx R) (hd : Disjoint (fld Q) (fld R)) :
    smor (rexp P (Q ⤉ R)) (rexp P Q ×ᵣ rexp P R) := by
  refine smor_trans (smor_rexp_relPi P (Q ⤉ R)) ?_
  rw [show coupleSemi P = graph (opSemi couple P) from rfl, graph_semi_rsum]
  refine smor_trans (relPi_rsum_smor (rEx_graph.2 hQ) (rEx_graph.2 hR)
    (disj_graph (opSemi_inj hP) hd)) ?_
  exact smor_rtimes (smor_symm (smor_rexp_relPi P Q)) (smor_symm (smor_rexp_relPi P R))

/-- `∃̇!P . a ≠ b . ⊃ . P exp (a ↓ b) smor P × P` (cf. ✱186·21). -/
private theorem smor_rexp_couple {P : α → α → Prop} (hP : rEx P) {a b : β} (hab : a ≠ b) :
    smor (rexp P (a ↓ b)) (P ×ᵣ P) := by
  refine smor_trans (smor_rexp_relPi P (a ↓ b)) ?_
  rw [show coupleSemi P = graph (opSemi couple P) from rfl, graph_semi_couple]
  exact smor_trans (relPi_couple_smor fun e => hab (opSemi_inj hP e))
    (smor_rtimes (smor_opSemi P a) (smor_opSemi P b))

/-- `∃̇!P . z ∼∈ C'Q . ⊃ . P exp (Q ⇸ z) smor (P exp Q) × P` (cf. ✱186·22). -/
private theorem smor_rexp_addLast {P : α → α → Prop} (hP : rEx P) {Q : β → β → Prop} {z : β}
    (hz : z ∉ fld Q) : smor (rexp P (Q ⇸ z)) (rexp P Q ×ᵣ P) := by
  refine smor_trans (smor_rexp_relPi P (Q ⇸ z)) ?_
  rw [show coupleSemi P = graph (opSemi couple P) from rfl, graph_semi_addLast]
  exact smor_trans (relPi_addLast_smor (notin_graph (opSemi_inj hP) hz))
    (smor_rtimes (smor_symm (smor_rexp_relPi P Q)) (smor_opSemi P z))

/-- `∃̇!P . z ∼∈ C'Q . ⊃ . P exp (z ⇷ Q) smor P × (P exp Q)` (cf. ✱186·23). -/
private theorem smor_rexp_addFirst {P : α → α → Prop} (hP : rEx P) {Q : β → β → Prop} {z : β}
    (hz : z ∉ fld Q) : smor (rexp P (z ⇷ Q)) (P ×ᵣ rexp P Q) := by
  refine smor_trans (smor_rexp_relPi P (z ⇷ Q)) ?_
  rw [show coupleSemi P = graph (opSemi couple P) from rfl, graph_semi_addFirst]
  exact smor_trans (relPi_addFirst_smor (notin_graph (opSemi_inj hP) hz))
    (smor_rtimes (smor_opSemi P z) (smor_symm (smor_rexp_relPi P Q)))

end Helpers186

private theorem fld_rexp_subsingleton {P : (Bool → Bool → Prop)} :
    ∀ A B, A ∈ fld (rexp (P ↓ P) (true ↓ false)) → B ∈ fld (rexp (P ↓ P) (true ↓ false)) → A = B := by
  intro A B hA hB
  have hP : rEx (P ↓ P) := ⟨P, P, rfl, rfl⟩
  have hQ : rEx (true ↓ false) := ⟨true, false, rfl, rfl⟩
  obtain ⟨a1, a2⟩ := (mem_fld_rexp hP hQ).1 hA
  obtain ⟨b1, b2⟩ := (mem_fld_rexp hP hQ).1 hB
  have key : ∀ {A B : Set ((Bool → Bool → Prop) → Bool → Prop)},
      (∀ c, c ∈ A → ∃ x z, (x ∈ fld (P ↓ P) ∧ z ∈ fld (true ↓ false)) ∧ c = x ↓ z) →
      (∀ c, c ∈ B → ∃ x z, (x ∈ fld (P ↓ P) ∧ z ∈ fld (true ↓ false)) ∧ c = x ↓ z) →
      (∀ z, z ∈ fld (true ↓ false) → ∃ x, x ↓ z ∈ B ∧ ∀ y, y ↓ z ∈ B → y = x) →
      ∀ c, c ∈ A → c ∈ B := by
    intro A B a1 b1 b2 c hc
    obtain ⟨x, z, ⟨hx, hz⟩, rfl⟩ := a1 c hc
    obtain ⟨x', hx', -⟩ := b2 z hz
    have h1 : x = P := by rw [fld_couple_self] at hx; exact hx
    rw [h1]
    obtain ⟨y, w, ⟨hy, -⟩, e⟩ := b1 _ hx'
    have h2 : y = P := by rw [fld_couple_self] at hy; exact hy
    rw [(couple_eq_iff.1 e).1, h2] at hx'
    exact hx'
  exact Set.ext fun c => ⟨key a1 b1 b2 c, key b1 a1 a2 c⟩

/-- The printed forms of ✱186·3·31 fail: with `S = x ↓ y` (`x ≠ y`) and `P = S ↓ S`,
`ΠNr'P = Nr'S` has members with two terms in their field, while every member of
`(Nr'P) exp_r (Nr'S) = Nr'(P exp S)` has at most one. -/
theorem pm186_3_printed_false : ¬ ∀ (P R : (Bool → Bool → Prop) → (Bool → Bool → Prop) → Prop)
    (S : Bool → Bool → Prop), (P ∈ Rel2excl ∧ P ∈ nr (Bool → Bool → Prop) R) ∧
      fld P ⊆ nr Bool S → piNr Bool P = nrExp (n₀r P) (n₀r S) := by
  intro h
  let S : Bool → Bool → Prop := true ↓ false
  have hex : S ↓ S ∈ Rel2excl := by
    rintro X Y ⟨⟨hX, hY⟩, hne⟩
    rw [fld_couple_self] at hX hY
    exact absurd (hX.trans hY.symm) hne
  have e := h (S ↓ S) (S ↓ S) S ⟨⟨hex, smor_refl _⟩, fun Q hQ => by
    rw [fld_couple_self] at hQ; rw [hQ]; exact smor_refl _⟩
  rw [pm185_21, n₀r_nrExp_n₀r] at e
  have hS : S ∈ nr Bool S := smor_refl S
  rw [e] at hS
  obtain ⟨eq, -⟩ := smor_iff_exists_equiv.1 hS
  have ht : true ∈ fld S := ⟨false, Or.inl ⟨rfl, rfl⟩⟩
  have hf : false ∈ fld S := ⟨true, Or.inr ⟨rfl, rfl⟩⟩
  have := fld_rexp_subsingleton _ _ (eq ⟨true, ht⟩).2 (eq ⟨false, hf⟩).2
  have := eq.injective (Subtype.ext this)
  exact Bool.noConfusion (congrArg Subtype.val this)

/-!
## [✱186] Powers of relation-numbers

*(Vol. 2, p. 507)*

> *Summary of* *186.
>
> For "\(\mu\) to the \(\nu\)th power," where ordinal powers are concerned, we use the notation "\(\mu \,\text{exp}\,\,_{r}\nu\)." We cannot use "\(\mu ^\nu\)" or "\(\mu \,\text{exp}\,\,\nu\)" because these have been already used for cardinals and classes (*116). We therefore put a suffix \(r\) to "\(\,\text{exp}\,\)" to show that it is *relational* powers that we are dealing with. We put \[ \mu \,\text{exp}\,\,_{r}\nu =\hat{R} \{(\exists P,Q).\mu =\text{N}_{0}\text{r}ʻP.\nu =\text{N}_{0}\text{r}ʻQ.R\,\text{smor}\,(P\,\text{exp}\,\,Q)\} \quad\text{Df}. \]
>
> The following are the principal propositions of this number:
>
> *186·2. \(\vdash :\mu \in \text{N}_{0}\text{R}.\supset .0_{r}\,\text{exp}\,\,_{r}\mu =0_{r}.\mu \,\text{exp}\,\,_{r}0_{r}=0_{r}\)
>
> We do not have \(\mu \,\text{exp}\,\,_{r}0_{r}=1\), because there is no ordinal 1.
>
> *186·21. \(\vdash .\mu \,\text{exp}\,\,_{r}2_{r}=\mu \dot{\times} \mu\)
>
> *186·22. \(\vdash .\alpha \,\text{exp}\,\,_{r}(\beta \dot{+} \dot{1} )=(\alpha \,\text{exp}\,\,_{r}\beta )\dot{\times} \alpha\)
>
> *186·23. \(\vdash .\alpha \,\text{exp}\,\,_{r}(\dot{1} \dot{+} \beta )=\alpha \dot{\times} (\alpha \,\text{exp}\,\,_{r}\beta )\)
>
> …

**Lean reading.** `μ exp_r ν` is `nrExp μ ν` with its actual type implicit, `P exp Q` is `rexp P Q`, `P^Q`
is `rpow P Q`, `P_df` is `Pdf P`; arguments `Nr'P` are `n₀r P` (✱186·02·03). The `0_r`, `2_r`,
`ν +̇ ϖ`, `ν +̇ 1̇`, `ϖ ×̇ ν`, `μ exp_r ν` in arithmetical positions have their own adequate types
(IIT). The real variables `α`, `β` of ✱186·22·23 (relation-numbers) are written `μ`, `ν`. `Mult ax`
as in ✱185·29. In ✱186·3·31 PM's base and exponent are interchanged: `ΠNr'P` is the `Nr'R`-th
power of `Nr'S` (✱185·29), not the converse.

**Status.** proved (all propositions except ✱186·15·4·5; ✱186·01·02·03 definition; ✱186·11·111·13·14·2·21·22·23 proved (reading); ✱186·3·31 proved (corrected); ✱186·15·4·5 stated (open here)), see their docstrings
-/

/-- ✱186·01 (Df). \(\mu \,\text{exp}\,\,_{r}\nu =\hat{R} \{(\exists P,Q).\mu =\text{N}_{0}\text{r}ʻP.\nu =\text{N}_{0}\text{r}ʻQ.R\,\text{smor}\,(P\,\text{exp}\,\,Q)\} \quad\text{Df}\) -/
theorem pm186_01 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    (nrExp μ ν : Set (γ → γ → Prop)) =
      {R | ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (rexp P Q)} :=
  rfl

/-- ✱186·02 (Df). \((\text{Nr}ʻP)\,\text{exp}\,\,_{r}\nu =(\text{N}_{0}\text{r}ʻP)\,\text{exp}\,\,_{r}\nu \quad\text{Df}\)

A rule of translation (normal adjustment), as ✱180·03. -/
theorem pm186_02 {P : α → α → Prop} {ν : Set (β → β → Prop)} :
    (nrExp (n₀r P) ν : Set (γ → γ → Prop)) = nrExp (n₀r P) ν := rfl

/-- ✱186·03 (Df). \(\mu \,\text{exp}\,\,_{r}(\text{Nr}ʻQ)=\mu \,\text{exp}\,\,_{r}(\text{N}_{0}\text{r}ʻQ) \quad\text{Df}\)

A rule of translation (normal adjustment), as ✱180·03. -/
theorem pm186_03 {μ : Set (α → α → Prop)} {Q : β → β → Prop} :
    (nrExp μ (n₀r Q) : Set (γ → γ → Prop)) = nrExp μ (n₀r Q) := rfl

/-- ✱186·1. \[\begin{align}&\vdash :R\in \mu \,\text{exp}\,\,_{r}\nu .\equiv .(\exists P,Q).\mu =\text{N}_{0}\text{r}ʻP.\nu =\text{N}_{0}\text{r}ʻQ.R\,\text{smor}\,(P\,\text{exp}\,\,Q)\\ &[(*186·01)]\end{align}\] -/
theorem pm186_1 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} {R : γ → γ → Prop} :
    R ∈ (nrExp μ ν : Set (γ → γ → Prop)) ↔
      ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (rexp P Q) :=
  Iff.rfl

/-- ✱186·11. \(\vdash .\exists !\mu \,\text{exp}\,\,_{r}\nu .\supset .\mu ,\nu \in \text{N}_{0}\text{R}.\mu ,\nu \in \text{NR}-\iota ʻ\Lambda\)

**Status.** proved (reading): the e-text's `⊢ .` is `⊢ :`; the ambiguous `NR` is taken in the
types of the members of `μ` and `ν` (as ✱180·4) -/
theorem pm186_11 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    (nrExp μ ν : Set (γ → γ → Prop)).Nonempty →
      (μ ∈ N₀R ∧ ν ∈ N₀R) ∧ (μ ∈ NR α \ ι Λ ∧ ν ∈ NR β \ ι Λ) := by
  rintro ⟨R, P, Q, ⟨rfl, rfl⟩, -⟩
  refine ⟨⟨⟨P, rfl⟩, ⟨Q, rfl⟩⟩, ⟨n₀r_mem_NR P, ?_⟩, ⟨n₀r_mem_NR Q, ?_⟩⟩
  · rw [mem_unitCls, Null_eq_empty]; exact n₀r_ne_empty P
  · rw [mem_unitCls, Null_eq_empty]; exact n₀r_ne_empty Q

/-- ✱186·111. \(\vdash :{\sim}(\mu \nu \in \text{N}_{0}\text{R}).\supset .\mu \,\text{exp}\,\,_{r}\nu =\Lambda\)

**Status.** proved (reading): transcription error: the e-text prints `μν ∈ N₀R` for
`μ, ν ∈ N₀R` -/
theorem pm186_111 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} :
    ¬(μ ∈ N₀R ∧ ν ∈ N₀R) → (nrExp μ ν : Set (γ → γ → Prop)) = Λ := by
  intro h
  rw [Null_eq_empty]
  by_contra hne
  exact h (pm186_11 (Set.nonempty_iff_ne_empty.2 hne)).1

/-- ✱186·12. \[\begin{align}&\vdash :R\in \mu \,\text{exp}\,\,_{r}\nu .\equiv .(\exists P,Q).\mu =\text{N}_{0}\text{r}ʻP.\nu =\text{N}_{0}\text{r}ʻQ.R\,\,\text{smor}\,\,P^{Q}\\ &[*176·181.*186·1]\end{align}\] -/
theorem pm186_12 {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)} {R : γ → γ → Prop} :
    R ∈ (nrExp μ ν : Set (γ → γ → Prop)) ↔
      ∃ (P : α → α → Prop) (Q : β → β → Prop), (μ = n₀r P ∧ ν = n₀r Q) ∧ smor R (rpow P Q) := by
  constructor
  · rintro ⟨P, Q, h, hR⟩; exact ⟨P, Q, h, smor_trans hR (smor_symm (smor_rpow_rexp P Q))⟩
  · rintro ⟨P, Q, h, hR⟩; exact ⟨P, Q, h, smor_trans hR (smor_rpow_rexp P Q)⟩

/-- ✱186·13. \[\begin{align}\vdash .(\text{Nr}ʻP)\,\text{exp}\,\,_{r}(\text{Nr}ʻQ)&=(\text{N}_{0}\text{r}ʻP)\,\text{exp}\,\,_{r}(\text{Nr}ʻQ)=(\text{Nr}ʻP)\,\text{exp}\,\,_{r}(\text{N}_{0}\text{r}ʻQ)\\ &=(\text{N}_{0}\text{r}ʻP)\,\text{exp}\,\,_{r}(\text{N}_{0}\text{r}ʻQ)=\text{Nr}ʻ(P\,\text{exp}\,\,Q)=\text{Nr}ʻ(P^{Q})\\ [\text{Proof as in *180·3}]\end{align}\]

**Status.** proved (reading): by the Dfs ✱186·02·03 the arguments Nr'P, Nr'Q of exp_r are read
N₀r'P, N₀r'Q, so the first three equations are identities of readings; all sides in one type -/
theorem pm186_13 {P : α → α → Prop} {Q : β → β → Prop} :
    ((((nrExp (n₀r P) (n₀r Q) : Set (γ → γ → Prop)) = nrExp (n₀r P) (n₀r Q) ∧
      (nrExp (n₀r P) (n₀r Q) : Set (γ → γ → Prop)) = nrExp (n₀r P) (n₀r Q)) ∧
      (nrExp (n₀r P) (n₀r Q) : Set (γ → γ → Prop)) = nrExp (n₀r P) (n₀r Q)) ∧
      (nrExp (n₀r P) (n₀r Q) : Set (γ → γ → Prop)) = nr γ (rexp P Q)) ∧
      nr γ (rexp P Q) = nr γ (rpow P Q) :=
  ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, n₀r_nrExp_n₀r P Q⟩, nr_eq_nr_of_smor (smor_symm (smor_rpow_rexp P Q))⟩

/-- ✱186·14. \(\vdash :\nu \neq 0_{r}.\varpi \neq 0_{r}.\supset .\mu \,\text{exp}\,\,_{r}(\nu \dot{+} \varpi )=(\mu \,\text{exp}\,\,_{r}\nu )\dot{\times} (\mu \,\text{exp}\,\,_{r}\varpi )\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components ν +̇ ϖ, μ exp_r ν, μ exp_r ϖ are adequate -/
theorem pm186_14 {α₁ α₂ α₃ W W₁ W₂ : Type*} {μ : Set (α₁ → α₁ → Prop)} {ν : Set (α₂ → α₂ → Prop)}
    {ϖ : Set (α₃ → α₃ → Prop)}
    (h : AdeqNrAdd W ν ϖ) (h₁ : AdeqNrExp W₁ μ ν) (h₂ : AdeqNrExp W₂ μ ϖ) :
    ν ≠ zero_r ∧ ϖ ≠ zero_r → (nrExp μ (ν ∔ ϖ : Set (W → W → Prop)) : Set (γ → γ → Prop)) =
      ((nrExp μ ν : Set (W₁ → W₁ → Prop)) ⨰ (nrExp μ ϖ : Set (W₂ → W₂ → Prop))) := by
  rintro ⟨hν0, hϖ0⟩
  by_cases hμ : ∃ P, μ = n₀r P
  swap
  · push Not at hμ
    rw [nrExp_eq_empty_of_left hμ, nrExp_eq_empty_of_left hμ, empty_nrMul]
  by_cases hν : ∃ Q, ν = n₀r Q
  swap
  · push Not at hν
    rw [nrAdd_eq_empty_of_left hν, nrExp_eq_empty_of_right _ (fun Q h => n₀r_ne_empty Q h.symm),
      nrExp_eq_empty_of_right _ hν, empty_nrMul]
  by_cases hϖ : ∃ R, ϖ = n₀r R
  swap
  · push Not at hϖ
    rw [nrAdd_eq_empty_of_right _ hϖ, nrExp_eq_empty_of_right _ (fun Q h => n₀r_ne_empty Q h.symm),
      nrExp_eq_empty_of_right (ν := ϖ) _ hϖ, nrMul_empty]
  obtain ⟨P, rfl⟩ := hμ; obtain ⟨Q, rfl⟩ := hν; obtain ⟨R, rfl⟩ := hϖ
  have hQ : rEx Q := ne_rNull_iff.1 fun e => hν0 (by rw [e]; exact zero_r_eq_n₀r.symm)
  have hR : rEx R := ne_rNull_iff.1 fun e => hϖ0 (by rw [e]; exact zero_r_eq_n₀r.symm)
  obtain ⟨X, hX, eX⟩ := h.eq_n₀r Q R
  obtain ⟨Y₁, hY₁, e₁⟩ := h₁.eq_n₀r P Q
  obtain ⟨Y₂, hY₂, e₂⟩ := h₂.eq_n₀r P R
  rw [eX, e₁, e₂, n₀r_nrExp_n₀r, n₀r_nrMul_n₀r]
  apply nr_eq_nr_of_smor
  by_cases hP : rEx P
  · obtain ⟨L, R', eLR, ⟨hL, hR'⟩, hd⟩ := rplus_split Q R
    refine smor_trans (smor_rexp (smor_refl P) hX) ?_
    rw [eLR]
    exact smor_trans (smor_rexp_rsum hP (smor_preserves (smor_symm hL) hQ)
      (smor_preserves (smor_symm hR') hR) hd) (smor_rtimes (smor_trans (smor_rexp (smor_refl P) hL)
        (smor_symm hY₁)) (smor_trans (smor_rexp (smor_refl P) hR') (smor_symm hY₂)))
  · have hP0 : P = rNull := by by_contra h'; exact hP (ne_rNull_iff.1 h')
    subst hP0
    rw [rexp_eq_rNull_iff.2 (Or.inl rfl)] at hY₁ ⊢
    rw [smor_rNull_iff'.1 hY₁, rtimes_rNull_left]
    exact smor_rNull_iff'.2 rfl

/-- ✱186·15. \(\vdash :\varpi \subset \text{Rl}ʻJ.\supset .\mu \,\text{exp}\,\,_{r}(\varpi \dot{\times} \nu )=(\mu \,\text{exp}\,\,_{r}\nu )\,\text{exp}\,\,_{r}\varpi )\)

The inner product and exponential are arithmetical components with their own adequate types
(IIT); `ϖ ⊂ Rl'J` is `ϖ ⊆ rl J`.

**Status.** stated (open here): the second formal law of exponentiation (✱176·57,
`R ⊂̇ J . ⊃ . (P exp Q) exp R smor P exp (R × Q)`) is not proved here -/
def pm186_15 : Prop :=
  ∀ {α₁ α₂ α₃ W W₁ γ : Type u} {μ : Set (α₁ → α₁ → Prop)} {ν : Set (α₂ → α₂ → Prop)}
    {ϖ : Set (α₃ → α₃ → Prop)}, AdeqNrMul W ϖ ν → AdeqNrExp W₁ μ ν →
    ϖ ⊆ rl J → (nrExp μ (ϖ ⨰ ν : Set (W → W → Prop)) : Set (γ → γ → Prop)) =
      nrExp (nrExp μ ν : Set (W₁ → W₁ → Prop)) ϖ

/-- ✱186·2. \(\vdash :\mu \in \text{N}_{0}\text{R}\supset .0_{r}\,\text{exp}\,\,_{r}\mu =0_{r}.\mu \,\text{exp}\,\,_{r}0_{r}=0_{r} \quad[*176·151]\)

Each `0_r` has its own type (IIT; no hypothesis is needed for `0_r`).

**Status.** proved (reading): the e-text's `μ ∈ N₀R ⊃ .` is `μ ∈ N₀R . ⊃ .` -/
theorem pm186_2 {W₁ W₂ : Type*} {μ : Set (α → α → Prop)} :
    μ ∈ N₀R → (nrExp (zero_r : Set (W₁ → W₁ → Prop)) μ : Set (γ → γ → Prop)) = zero_r ∧
      (nrExp μ (zero_r : Set (W₂ → W₂ → Prop)) : Set (γ → γ → Prop)) = zero_r := by
  rintro ⟨P, rfl⟩
  rw [nrExp_of zero_r_eq_n₀r rfl, nrExp_of rfl zero_r_eq_n₀r, rexp_eq_rNull_iff.2 (Or.inl rfl),
    rexp_eq_rNull_iff.2 (Or.inr rfl)]
  exact ⟨zero_r_eq_nr.symm, zero_r_eq_nr.symm⟩

/-- ✱186·21. \(\vdash .\mu \,\text{exp}\,\,_{r}2_{r}=\mu \dot{\times} \mu\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the type of the
arithmetical component 2_r is adequate (2_r exists in it) -/
theorem pm186_21 {W : Type*} {μ : Set (α → α → Prop)} (h : (two_r : Set (W → W → Prop)).Nonempty) :
    (nrExp μ (two_r : Set (W → W → Prop)) : Set (γ → γ → Prop)) = (μ ⨰ μ : Set (γ → γ → Prop)) := by
  obtain ⟨_, a, b, hab, -⟩ := h
  by_cases hμ : ∃ P, μ = n₀r P
  · obtain ⟨P, rfl⟩ := hμ
    rw [nrExp_of rfl (two_r_eq_n₀r hab), n₀r_nrMul_n₀r]
    by_cases hP : rEx P
    · exact nr_eq_nr_of_smor (smor_rexp_couple hP hab)
    · have hP0 : P = rNull := by by_contra h'; exact hP (ne_rNull_iff.1 h')
      subst hP0
      rw [rexp_eq_rNull_iff.2 (Or.inl rfl), rtimes_rNull_left]
      exact (zero_r_eq_nr (γ := γ)).symm.trans zero_r_eq_nr
  · push Not at hμ
    rw [nrExp_eq_empty_of_left hμ, nrMul_eq_empty_of_left hμ]

/-- ✱186·22. \(\vdash .\alpha \,\text{exp}\,\,_{r}(\beta \dot{+} \dot{1} )=(\alpha \,\text{exp}\,\,_{r}\beta )\dot{\times} \alpha\)

PM's `α`, `β` are relation-numbers, here `μ`, `ν`.

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components β +̇ 1̇ and α exp_r β are adequate -/
theorem pm186_22 {W W₁ : Type*} {μ : Set (α → α → Prop)} {ν : Set (δ → δ → Prop)}
    (h : AdeqNrAddOne W β ν) (h₁ : AdeqNrExp W₁ μ ν) :
    (nrExp μ (nrAddOne β ν : Set (W → W → Prop)) : Set (γ → γ → Prop)) =
      ((nrExp μ ν : Set (W₁ → W₁ → Prop)) ⨰ μ : Set (γ → γ → Prop)) := by
  obtain ⟨b⟩ := h.nonempty
  by_cases hμ : ∃ P, μ = n₀r P
  swap
  · push Not at hμ
    rw [nrExp_eq_empty_of_left hμ, nrMul_eq_empty_of_right _ hμ]
  by_cases hν : ∃ Q, ν = n₀r Q
  swap
  · push Not at hν
    rw [nrAddOne_empty_of hν, nrExp_eq_empty_of_right _ (fun Q h => n₀r_ne_empty Q h.symm),
      nrExp_eq_empty_of_right _ hν, empty_nrMul]
  obtain ⟨P, rfl⟩ := hμ; obtain ⟨Q, rfl⟩ := hν
  obtain ⟨X, hX, eX⟩ := h.eq_n₀r Q b
  obtain ⟨Y, hY, eY⟩ := h₁.eq_n₀r P Q
  rw [eX, eY, n₀r_nrExp_n₀r, n₀r_nrMul_n₀r]
  apply nr_eq_nr_of_smor
  obtain ⟨L, e, hLe, hL, he⟩ := addLastDot_split Q b
  rw [hLe] at hX
  refine smor_trans (smor_rexp (smor_refl P) hX) ?_
  by_cases hP : rEx P
  · by_cases hQ : rEx Q
    · exact smor_trans (smor_rexp_addLast hP he) (smor_rtimes (smor_trans
        (smor_rexp (smor_refl P) hL) (smor_symm hY)) (smor_refl P))
    · have hQ0 : Q = rNull := by by_contra h'; exact hQ (ne_rNull_iff.1 h')
      subst hQ0
      have hL0 : L = rNull := smor_rNull_iff'.1 hL
      subst hL0
      rw [addLast_rNull, rexp_eq_rNull_iff.2 (Or.inr rfl)] at *
      have hY0 : Y = rNull := smor_rNull_iff'.1 hY
      subst hY0
      rw [rtimes_rNull_left]; exact smor_rNull_iff'.2 rfl
  · have hP0 : P = rNull := by by_contra h'; exact hP (ne_rNull_iff.1 h')
    subst hP0
    rw [rexp_eq_rNull_iff.2 (Or.inl rfl), rtimes_rNull_right]
    exact smor_rNull_iff'.2 rfl

/-- ✱186·23. \(\vdash .\alpha \,\text{exp}\,\,_{r}(\dot{1} \dot{+} \beta )=\alpha \dot{\times} (\alpha \,\text{exp}\,\,_{r}\beta ) \quad[\text{Proof as in *186·22}]\)

**Status.** proved (reading): convention IIT (Prefatory Statement, IV): the actual types of the
arithmetical components 1̇ +̇ β and α exp_r β are adequate -/
theorem pm186_23 {W W₁ : Type*} {μ : Set (α → α → Prop)} {ν : Set (δ → δ → Prop)}
    (h : AdeqNrOneAdd W β ν) (h₁ : AdeqNrExp W₁ μ ν) :
    (nrExp μ (nrOneAdd β ν : Set (W → W → Prop)) : Set (γ → γ → Prop)) =
      (μ ⨰ (nrExp μ ν : Set (W₁ → W₁ → Prop)) : Set (γ → γ → Prop)) := by
  obtain ⟨b⟩ := h.nonempty
  by_cases hμ : ∃ P, μ = n₀r P
  swap
  · push Not at hμ
    rw [nrExp_eq_empty_of_left hμ, nrMul_eq_empty_of_left hμ]
  by_cases hν : ∃ Q, ν = n₀r Q
  swap
  · push Not at hν
    rw [nrOneAdd_empty_of hν, nrExp_eq_empty_of_right _ (fun Q h => n₀r_ne_empty Q h.symm),
      nrExp_eq_empty_of_right _ hν, nrMul_empty]
  obtain ⟨P, rfl⟩ := hμ; obtain ⟨Q, rfl⟩ := hν
  obtain ⟨X, hX, eX⟩ := h.eq_n₀r Q b
  obtain ⟨Y, hY, eY⟩ := h₁.eq_n₀r P Q
  rw [eX, eY, n₀r_nrExp_n₀r, n₀r_nrMul_n₀r]
  apply nr_eq_nr_of_smor
  obtain ⟨L, e, hLe, hL, he⟩ := addFirstDot_split b Q
  rw [hLe] at hX
  refine smor_trans (smor_rexp (smor_refl P) hX) ?_
  by_cases hP : rEx P
  · by_cases hQ : rEx Q
    · exact smor_trans (smor_rexp_addFirst hP he) (smor_rtimes (smor_refl P)
        (smor_trans (smor_rexp (smor_refl P) hL) (smor_symm hY)))
    · have hQ0 : Q = rNull := by by_contra h'; exact hQ (ne_rNull_iff.1 h')
      subst hQ0
      have hL0 : L = rNull := smor_rNull_iff'.1 hL
      subst hL0
      rw [addFirst_rNull, rexp_eq_rNull_iff.2 (Or.inr rfl)] at *
      have hY0 : Y = rNull := smor_rNull_iff'.1 hY
      subst hY0
      rw [rtimes_rNull_right]; exact smor_rNull_iff'.2 rfl
  · have hP0 : P = rNull := by by_contra h'; exact hP (ne_rNull_iff.1 h')
    subst hP0
    rw [rexp_eq_rNull_iff.2 (Or.inl rfl), rtimes_rNull_left]
    exact smor_rNull_iff'.2 rfl

/-- ✱186·3. \[\begin{align}\vdash \colon\ldotp \text{Mult ax}.\supset :P\in &\text{Rel}^{2}\text{excl}\cap \text{Nr}ʻR.CʻP\subset \text{Nr}ʻS.\supset .\\ &\Pi \text{Nr}ʻP=(\text{Nr}ʻP)\,\text{exp}\,\,_{r}(\text{Nr}ʻS) \quad[*185·29]\end{align}\]

`Mult ax` as in ✱185·29.

**Status.** proved (corrected): as printed, `ΠNr'P = (Nr'P) exp_r (Nr'S)` interchanges base and
exponent: by ✱185·29 (the reference) `ΠNr'P = Nr'(S exp R)`, i.e. `(Nr'S) exp_r (Nr'P)` (`P` is
like `R`); e.g. `S = x ↓ y`, `P = R = S ↓ S` gives `ΠNr'P = Nr'S` with two terms in the fields
of its members and `(Nr'P) exp_r (Nr'S)` with at most one (`pm186_3_printed_false`). Corrected:
`ΠNr'P = (Nr'S) exp_r (Nr'P)`. -/
theorem pm186_3 {ζ ξ : Type*} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {R : ζ → ζ → Prop} {S : ξ → ξ → Prop} (hm : MultAx (α → (ξ → ζ → Prop) → Prop)) :
    P ∈ Rel2excl ∩ nr (α → α → Prop) R ∧ fld P ⊆ nr α S →
      piNr γ P = (nrExp (n₀r S) (n₀r P) : Set (γ → γ → Prop)) := by
  rintro ⟨⟨hP, hPR⟩, hPS⟩
  rw [pm185_29 hm ⟨⟨hP, hPR⟩, hPS⟩, n₀r_nrExp_n₀r]
  exact nr_eq_nr_of_smor (smor_rexp (smor_refl S) (smor_symm hPR))

/-- ✱186·31. \[\begin{align}\vdash \colon\ldotp \text{Mult ax}.\supset :\mu ,\nu \in \text{NR}-\iota ʻ\Lambda .P\in &\text{Rel}^{2}\text{excl}\cap \mu .CʻP\subset \nu .\supset .\\ &\Pi \text{Nr}ʻP=\mu \,\text{exp}\,\,_{r}\nu \quad[*186·3]\end{align}\]

`μ, ν ∈ NR` have independent `NR` types; `Mult ax` as in ✱185·29.

**Status.** proved (corrected): as ✱186·3, PM interchanges base and exponent: `P ∈ μ`,
`C'P ⊂ ν` give `ΠNr'P = ν exp_r μ` (✱185·29); with `μ = Nr'(S ↓ S)`, `ν = Nr'S`, `S = x ↓ y`,
`μ exp_r ν` differs (`pm186_3_printed_false`). Corrected: `ΠNr'P = ν exp_r μ`. -/
theorem pm186_31 {β₁ β₂ : Type*} {μ : Set ((α → α → Prop) → (α → α → Prop) → Prop)}
    {ν : Set (α → α → Prop)} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    (hm : MultAx (α → (α → (α → α → Prop) → Prop) → Prop)) :
    ((μ ∈ NR β₁ \ ι Λ ∧ ν ∈ NR β₂ \ ι Λ) ∧ P ∈ Rel2excl ∩ μ) ∧ fld P ⊆ ν →
      piNr γ P = (nrExp ν μ : Set (γ → γ → Prop)) := by
  rintro ⟨⟨⟨⟨hμ, -⟩, ⟨hν, hν0⟩⟩, hP, hPμ⟩, hPν⟩
  rcases NR_cases hμ with rfl | ⟨P', rfl⟩
  · exact absurd hPμ (Set.notMem_empty P)
  rcases NR_cases hν with rfl | ⟨S, rfl⟩
  · exact absurd (by rw [mem_unitCls, Null_eq_empty]) hν0
  have e : n₀r P' = n₀r P := n₀r_eq_n₀r_iff.2 (smor_symm (mem_n₀r.1 hPμ))
  rw [e]
  refine pm186_3 (R := P) hm ⟨⟨hP, smor_refl P⟩, fun Q hQ => ?_⟩
  have := hPν hQ
  rw [n₀r_eq_nr] at this; exact this

/-- ✱186·4. \(\vdash .\text{Nr}ʻP_{\text{df}}=2_{r}\,\text{exp}\,\,_{r}(\text{Nr}ʻP) \quad[*177·13]\)

The `2_r` has its own type, adequate (IIT).

**Status.** stated (open here): the likeness `P_df smor (x ↓ y)^P` (✱177·13), on which the
proposition rests, is not proved here -/
def pm186_4 : Prop :=
  ∀ {α W γ : Type u} {P : α → α → Prop}, (two_r : Set (W → W → Prop)).Nonempty →
    nr γ (Pdf P) = (nrExp (two_r : Set (W → W → Prop)) (n₀r P) : Set (γ → γ → Prop))

/-- ✱186·5. \(\vdash :\mu ,\nu \in \text{N}_{0}\text{R}.\nu \neq 0_{r}.\supset .Cʻʻ(\mu \,\text{exp}\,\,_{r}\nu )=(Cʻʻ\mu )^{Cʻʻ\nu }\)

`(C''μ)^{C''ν}` is `C ʻʻ μ ^ᶜ C ʻʻ ν` (✱116·02).

**Status.** stated (open here): the identification of `C'(P exp Q)` with `(C'P) exp (C'Q)`
(✱176·14) and its cardinal (✱116·222), on which the proposition rests, are not proved here -/
def pm186_5 : Prop :=
  ∀ {α β γ : Type u} {μ : Set (α → α → Prop)} {ν : Set (β → β → Prop)},
    (μ ∈ N₀R ∧ ν ∈ N₀R) ∧ ν ≠ zero_r →
      C ʻʻ (nrExp μ ν : Set (γ → γ → Prop)) = (C ʻʻ μ ^ᶜ C ʻʻ ν : Set (Set γ))


end PrincipiaMathematica
