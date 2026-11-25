import PrincipiaMathematica.Defs.Part5

/-!
# Part V, Section A: General theory of series

Volume 2. Numbers: ✱206, ✱207, ✱208.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable {P : α → α → Prop} {A B G : Set α} {K : Set (Set α)} {x y a : α}

/-! ### Auxiliary lemmas for ✱206–✱208 (not PM propositions) -/

section Aux

private theorem a2_fl {R : α → α → Prop} {x y : α} (h : R x y) : x ∈ fld R := ⟨y, Or.inl h⟩

private theorem a2_fr {R : α → α → Prop} {x y : α} (h : R x y) : y ∈ fld R := ⟨x, Or.inr h⟩

private theorem a2_desc_iff {R : α → β → Prop} {y : β} {ψ : α → Prop} :
    Desc R y ψ ↔ EDesc R y ∧ ∀ x, R x y → ψ x := TheIs_iff

private theorem a2_desc_intro {R : α → β → Prop} {y : β} {ψ : α → Prop} {b : α} (hb : R b y)
    (hu : ∀ c, R c y → c = b) (h : ψ b) : Desc R y ψ :=
  ⟨b, fun c => ⟨hu c, fun e => e ▸ hb⟩, h⟩

private theorem a2_EDesc_uniq {R : α → β → Prop} {y : β} (h : EDesc R y) {a b : α}
    (ha : R a y) (hb : R b y) : a = b := by
  obtain ⟨c, hc⟩ := h
  exact ((hc a).1 ha).trans ((hc b).1 hb).symm

private theorem a2_EDesc_of {R : α → β → Prop} {y : β} {a : α} (ha : R a y)
    (hu : ∀ b, R b y → b = a) : EDesc R y := ⟨a, fun b => ⟨hu b, fun h => h ▸ ha⟩⟩

private theorem a2_EDesc_exists {R : α → β → Prop} {y : β} (h : EDesc R y) : ∃ a, R a y := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, (hc c).2 rfl⟩

private theorem a2_desc_of_unique {R : α → β → Prop} {y : β} {ψ : α → Prop} {a : α} (ha : R a y)
    (hu : ∀ b, R b y → b = a) : Desc R y ψ ↔ ψ a :=
  TheIs_iff_of_unique (fun b => ⟨hu b, fun h => h ▸ ha⟩)

private theorem a2_refs_congr_EDesc {R : α → β → Prop} {S : α → γ → Prop} {y : β} {z : γ}
    (h : refs R y = refs S z) : EDesc R y ↔ EDesc S z := by
  have e : (fun x => R x y) = fun x => S x z :=
    funext fun x => propext (show R x y ↔ S x z from Set.ext_iff.1 h x)
  show EBang _ ↔ EBang _
  rw [e]

private theorem a2_refs_congr_desc {R : α → β → Prop} {S : α → γ → Prop} {y : β} {z : γ}
    {ψ : α → Prop}
    (h : refs R y = refs S z) : Desc R y ψ ↔ Desc S z ψ := by
  have e : (fun x => R x y) = fun x => S x z :=
    funext fun x => propext (show R x y ↔ S x z from Set.ext_iff.1 h x)
  show TheIs _ ψ ↔ TheIs _ ψ
  rw [e]

private theorem a2_eq_Null_iff {X : Set α} : X = Λ ↔ ∀ x, x ∉ X := by
  rw [Null_eq_empty, Set.eq_empty_iff_forall_notMem]

private theorem a2_mem_zero_union_one {X : Set α} :
    X ∈ (zero ∪ one : Set (Set α)) ↔ ∀ a b, a ∈ X → b ∈ X → a = b := by
  constructor
  · rintro (h | h) a b ha hb
    · have e : X = Λ := h
      exact absurd ha (a2_eq_Null_iff.1 e a)
    · obtain ⟨c, hc⟩ := mem_one_iff.1 h
      exact ((hc a).1 ha).trans ((hc b).1 hb).symm
  · intro h
    by_cases hX : X.Nonempty
    · obtain ⟨c, hc⟩ := hX
      exact Or.inr (mem_one_iff.2 ⟨c, fun z => ⟨fun hz => h z c hz hc, fun e => e ▸ hc⟩⟩)
    · left
      show X = Λ
      exact a2_eq_Null_iff.2 fun z hz => hX ⟨z, hz⟩

private theorem a2_asymm (hJ : rsq P ⪽ J) {x y : α} (h1 : P x y) (h2 : P y x) : False :=
  hJ x x ⟨y, h1, h2⟩ rfl

private theorem a2_rsqJ_of_Ser (h : P ∈ Ser) : rsq P ⪽ J := by
  intro x y hxy hxy'
  obtain ⟨z, hxz, hzy⟩ := hxy
  have e : x = y := hxy'
  subst e
  exact mem_rl_J.1 h.1.1 x (mem_transR.1 h.1.2 x z x ⟨hxz, hzy⟩)

private theorem a2_seq_uniq (hc : P ∈ connex) {x x' : α} (hx : seqP P x A) (hx' : seqP P x' A) :
    x = x' := by
  rw [seqP_iff] at hx hx'
  rcases mem_connex.1 hc x x' ⟨hx.1.2, hx'.1.2⟩ with (h | h) | h
  · exact absurd h (hx'.2 x hx.1.1)
  · exact h
  · exact absurd h (hx.2 x' hx'.1.1)

private theorem a2_max_uniq (hc : P ∈ connex) {a b : α} (h1 : maxP P a A) (h2 : maxP P b A) :
    a = b := by
  rw [maxP_iff] at h1 h2
  rcases mem_connex.1 hc a b ⟨h1.1.2, h2.1.2⟩ with (h | h) | h
  · exact absurd h (h1.2 b h2.1.1)
  · exact h
  · exact absurd h (h2.2 a h1.1.1)

private theorem a2_min_uniq (hc : P ∈ connex) {a b : α} (h1 : minP P a A) (h2 : minP P b A) :
    a = b := by
  rw [minP_iff] at h1 h2
  rcases mem_connex.1 hc a b ⟨h1.1.2, h2.1.2⟩ with (h | h) | h
  · exact absurd h (h2.2 a h1.1.1)
  · exact h
  · exact absurd h (h1.2 b h2.1.1)

/-- `seq⃗_P'α` depends only on `p'P⃖''(α ∩ C'P)`. -/
private theorem a2_seq_congr_pi
    (h : prodCls (Rbwd P ʻʻ (A ∩ fld P)) = prodCls (Rbwd P ʻʻ (B ∩ fld P))) :
    refs (seqP P) A = refs (seqP P) B := by
  ext x
  show minP P x (prodCls (Rbwd P ʻʻ (A ∩ fld P))) ↔ minP P x (prodCls (Rbwd P ʻʻ (B ∩ fld P)))
  rw [h]

private theorem a2_pi_ext
    (h : ∀ z, (∀ y, y ∈ A ∩ fld P → P y z) ↔ (∀ y, y ∈ B ∩ fld P → P y z)) :
    prodCls (Rbwd P ʻʻ (A ∩ fld P)) = prodCls (Rbwd P ʻʻ (B ∩ fld P)) :=
  Set.ext fun z => by rw [mem_prodCls_Rbwd, mem_prodCls_Rbwd]; exact h z

/-- For connected `P`, the predecessors of a sequent are members or predecessors of members. -/
private theorem a2_seq_pred_sub (hc : P ∈ connex) {s : α} (hs : seqP P s A) :
    refs P s ⊆ (A ∩ fld P) ∪ P ʻʻ A := by
  intro y hys
  have hys' : P y s := hys
  have hs' := (seqP_iff.1 hs)
  by_contra hn
  apply hs'.2 y _ hys'
  intro z hz
  rcases mem_connex.1 hc y z ⟨a2_fl hys', hz.2⟩ with (h | h) | h
  · exact absurd (Or.inr ⟨z, hz.1, h⟩) hn
  · exact absurd (Or.inl (by rw [h]; exact hz)) hn
  · exact h

/-- `α ∩ C'P ∪ P''α = max⃗_P'α ∪ P''α` (no hypothesis). -/
private theorem a2_inter_fld_union_img : (A ∩ fld P) ∪ P ʻʻ A = refs (maxP P) A ∪ P ʻʻ A := by
  ext x
  constructor
  · rintro (hx | hx)
    · by_cases h : ∃ y, y ∈ A ∧ P x y
      · exact Or.inr h
      · push Not at h
        exact Or.inl (maxP_iff.2 ⟨hx, h⟩)
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact Or.inl (maxP_iff.1 hx).1
    · exact Or.inr hx

/-- `∼(∃x).x max_P α . ≡ . α ∩ C'P ⊂ P''α` (cf. ✱205·123). -/
private theorem a2_noMax_iff_sub : (¬∃ m, maxP P m A) ↔ A ∩ fld P ⊆ P ʻʻ A := by
  constructor
  · intro h y hy
    by_contra hn
    exact h ⟨y, maxP_iff.2 ⟨hy, fun z hz hyz => hn ⟨z, hz, hyz⟩⟩⟩
  · rintro h ⟨m, hm⟩
    obtain ⟨w, hw, hmw⟩ := h (maxP_iff.1 hm).1
    exact (maxP_iff.1 hm).2 w hw hmw

private theorem a2_noMax_of (hc : P ∈ connex) (h : ¬EDesc (maxP P) A) : ¬∃ m, maxP P m A :=
  fun ⟨_, hm⟩ => h (a2_EDesc_of hm fun _ hb => a2_max_uniq hc hb hm)

private theorem a2_maxP_inter {m : α} : maxP P m (A ∩ fld P) ↔ maxP P m A := by
  rw [maxP_iff, maxP_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, -⟩, h3⟩
    exact ⟨⟨h1, h2⟩, fun z hz hyz => h3 z ⟨hz, a2_fr hyz⟩ hyz⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨h1, h2⟩, h2⟩, fun z hz => h3 z hz.1⟩

private theorem a2_connex_cnv (hc : P ∈ connex) : P˘ ∈ connex := by
  rw [mem_connex] at hc ⊢
  intro x y hxy
  rw [fld_cnv] at hxy
  rcases hc y x ⟨hxy.2, hxy.1⟩ with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h.symm)
  · exact Or.inr h

private theorem a2_img_inter_fld : P ʻʻ (A ∩ fld P) = P ʻʻ A := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy.1, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, ⟨hy, a2_fr hxy⟩, hxy⟩

/-- For transitive `P`, `P_*''α = (α ∩ C'P) ∪ P''α`. -/
private theorem a2_anc_img_eq (ht : P ∈ transR) : anc P ʻʻ A = (A ∩ fld P) ∪ P ʻʻ A := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (anc_iff_of_transR ht).1 hxy with ⟨e, hx⟩ | h
    · rw [e]
      exact Or.inl ⟨hy, by rw [← e]; exact hx⟩
    · exact Or.inr ⟨y, hy, h⟩
  · rintro (⟨hx, hxf⟩ | ⟨y, hy, hxy⟩)
    · exact ⟨x, hx, (anc_iff_of_transR ht).2 (Or.inl ⟨rfl, hxf⟩)⟩
    · exact ⟨y, hy, (anc_iff_of_transR ht).2 (Or.inr hxy)⟩

/-- A one-many relation: `ψ(S'x) . ≡ . (∃y) . ySx . ψy`. -/
private theorem a2_desc_oneMany {S : α → β → Prop} (hom : ∀ x y z, S x z ∧ S y z → x = y)
    {x : β} {ψ : α → Prop} : Desc S x ψ ↔ ∃ y, S y x ∧ ψ y := by
  constructor
  · rintro ⟨b, hb, hψ⟩
    exact ⟨b, (hb b).2 rfl, hψ⟩
  · rintro ⟨y, hy, hψ⟩
    exact ⟨y, fun v => ⟨fun hv => hom v y x ⟨hv, hy⟩, fun e => e ▸ hy⟩, hψ⟩

/-- No term is both the precedent and the sequent of `γ` when `P ∈ trans ∨ P² ⊂̇ J`
(the core of ✱206·731·732). -/
private theorem a2_prec_seq_false (hor : P ∈ transR ∨ rsq P ⪽ J) (hp : precP P x G)
    (hs : seqP P x G) : False := by
  by_cases hne : (G ∩ fld P).Nonempty
  · obtain ⟨g, hg⟩ := hne
    have h1 := (precP_iff.1 hp).1.1 g hg
    have h2 := (seqP_iff.1 hs).1.1 g hg
    rcases hor with ht | hJ
    · have hxx : P x x := mem_transR.1 ht x g x ⟨h1, h2⟩
      have hs' := seqP_iff.1 hs
      exact hs'.2 x hs'.1.1 hxx
    · exact hJ x x ⟨g, h1, h2⟩ rfl
  · have hG : ∀ y, y ∈ G ∩ fld P → False := fun y hy => hne ⟨y, hy⟩
    obtain ⟨w, hw | hw⟩ := (precP_iff.1 hp).1.2
    · exact (precP_iff.1 hp).2 w (fun y hy => (hG y hy).elim) hw
    · exact (seqP_iff.1 hs).2 w (fun y hy => (hG y hy).elim) hw

/-! #### Ordinal correlators (`S ∈ P smor̄ Q`) -/

private theorem a2_smor_facts {Q : β → β → Prop} {S : α → β → Prop} (hS : S ∈ smorbar P Q) :
    ((∀ x y z, S x z ∧ S y z → x = y) ∧ (∀ x y z, S x y ∧ S x z → y = z)) ∧
    (∀ x y, P x y ↔ ∃ z w, (S x z ∧ S y w) ∧ Q z w) ∧
    (∀ x, x ∈ fld P ↔ ∃ z, S x z) ∧ (∀ z, z ∈ fld Q ↔ ∃ x, S x z) := by
  obtain ⟨⟨h1, hcod⟩, hP⟩ := hS
  have hP' : ∀ x y, P x y ↔ ∃ z w, (S x z ∧ S y w) ∧ Q z w := fun x y => by
    rw [hP]
    exact semi_apply S Q x y
  have hQ : ∀ z, z ∈ fld Q ↔ ∃ x, S x z := fun z => Set.ext_iff.1 hcod z
  refine ⟨mem_arrow_one_one.1 h1, hP', fun x => ⟨?_, ?_⟩, hQ⟩
  · rintro ⟨y, h | h⟩
    · obtain ⟨z, w, ⟨hxz, -⟩, -⟩ := (hP' x y).1 h
      exact ⟨z, hxz⟩
    · obtain ⟨z, w, ⟨-, hxw⟩, -⟩ := (hP' y x).1 h
      exact ⟨w, hxw⟩
  · rintro ⟨z, hxz⟩
    obtain ⟨w, hw | hw⟩ := (hQ z).2 ⟨x, hxz⟩
    · obtain ⟨y, hyw⟩ := (hQ w).1 ⟨z, Or.inr hw⟩
      exact ⟨y, Or.inl ((hP' x y).2 ⟨z, w, ⟨hxz, hyw⟩, hw⟩)⟩
    · obtain ⟨y, hyw⟩ := (hQ w).1 ⟨z, Or.inl hw⟩
      exact ⟨y, Or.inr ((hP' y x).2 ⟨w, z, ⟨hyw, hxz⟩, hw⟩)⟩

private theorem a2_smor_seq {Q : β → β → Prop} {S : α → β → Prop} (hS : S ∈ smorbar P Q)
    {x : α} {z : β} (hxz : S x z) : seqP P x A ↔ seqP Q z (S˘ ʻʻ A) := by
  obtain ⟨⟨_, hmo⟩, hP, hfP, hfQ⟩ := a2_smor_facts hS
  have pi : ∀ u v, S u v →
      ((∀ a, a ∈ A ∩ fld P → P a u) ↔ (∀ w, w ∈ S˘ ʻʻ A ∩ fld Q → Q w v)) := by
    intro u v huv
    constructor
    · rintro h w ⟨⟨a, ha, haw⟩, -⟩
      have hPa := h a ⟨ha, (hfP a).2 ⟨w, haw⟩⟩
      obtain ⟨w', v', ⟨haw', huv'⟩, hq⟩ := (hP a u).1 hPa
      rw [hmo a w' w ⟨haw', haw⟩, hmo u v' v ⟨huv', huv⟩] at hq
      exact hq
    · rintro h a ⟨ha, haf⟩
      obtain ⟨w, haw⟩ := (hfP a).1 haf
      exact (hP a u).2 ⟨w, v, ⟨haw, huv⟩, h w ⟨⟨a, ha, haw⟩, (hfQ w).2 ⟨a, haw⟩⟩⟩
  rw [seqP_iff, seqP_iff]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    refine ⟨⟨(pi x z hxz).1 h1, (hfQ z).2 ⟨x, hxz⟩⟩, fun v hv hvz => ?_⟩
    obtain ⟨u, huv⟩ := (hfQ v).1 (a2_fl hvz)
    exact h2 u ((pi u v huv).2 hv) ((hP u x).2 ⟨v, z, ⟨huv, hxz⟩, hvz⟩)
  · rintro ⟨⟨h1, -⟩, h2⟩
    refine ⟨⟨(pi x z hxz).2 h1, (hfP x).2 ⟨z, hxz⟩⟩, fun u hu hux => ?_⟩
    obtain ⟨v, z', ⟨huv, hxz'⟩, hq⟩ := (hP u x).1 hux
    rw [hmo x z' z ⟨hxz', hxz⟩] at hq
    exact h2 v ((pi u v huv).1 hu) hq

private theorem a2_smor_max {Q : β → β → Prop} {S : α → β → Prop} (hS : S ∈ smorbar P Q)
    {x : α} {z : β} (hxz : S x z) : maxP P x A ↔ maxP Q z (S˘ ʻʻ A) := by
  obtain ⟨⟨hom, hmo⟩, hP, hfP, hfQ⟩ := a2_smor_facts hS
  rw [maxP_iff, maxP_iff]
  constructor
  · rintro ⟨⟨hxA, -⟩, hn⟩
    refine ⟨⟨⟨x, hxA, hxz⟩, (hfQ z).2 ⟨x, hxz⟩⟩, ?_⟩
    rintro w ⟨a, ha, haw⟩ hzw
    exact hn a ha ((hP x a).2 ⟨z, w, ⟨hxz, haw⟩, hzw⟩)
  · rintro ⟨⟨⟨a, ha, haz⟩, -⟩, hn⟩
    have e : a = x := hom a x z ⟨haz, hxz⟩
    rw [e] at ha
    refine ⟨⟨ha, (hfP x).2 ⟨z, hxz⟩⟩, fun y hy hxy => ?_⟩
    obtain ⟨z', w, ⟨hxz', hyw⟩, hq⟩ := (hP x y).1 hxy
    rw [hmo x z' z ⟨hxz', hxz⟩] at hq
    exact hn w ⟨y, hy, hyw⟩ hq

private theorem a2_smor_max_ex {Q : β → β → Prop} {S : α → β → Prop} (hS : S ∈ smorbar P Q) :
    (∃ m, maxP P m A) ↔ ∃ m, maxP Q m (S˘ ʻʻ A) := by
  obtain ⟨-, -, hfP, hfQ⟩ := a2_smor_facts hS
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨z, hmz⟩ := (hfP m).1 (maxP_iff.1 hm).1.2
    exact ⟨z, (a2_smor_max hS hmz).1 hm⟩
  · rintro ⟨z, hz⟩
    obtain ⟨m, hmz⟩ := (hfQ z).1 (maxP_iff.1 hz).1.2
    exact ⟨m, (a2_smor_max hS hmz).2 hz⟩

private theorem a2_smor_lt {Q : β → β → Prop} {S : α → β → Prop} (hS : S ∈ smorbar P Q)
    {x : α} {z : β} (hxz : S x z) : ltP P x A ↔ ltP Q z (S˘ ʻʻ A) := by
  show seqP P x A ∧ ¬(∃ m, maxP P m A) ↔ seqP Q z (S˘ ʻʻ A) ∧ ¬∃ m, maxP Q m (S˘ ʻʻ A)
  rw [a2_smor_seq hS hxz, a2_smor_max_ex hS]

private theorem a2_smor_refs {Q : β → β → Prop} {S : α → β → Prop} {R : α → Set α → Prop}
    {R' : β → Set β → Prop} (hS : S ∈ smorbar P Q) (hR : ∀ x, R x A → x ∈ fld P)
    (htr : ∀ x z, S x z → (R x A ↔ R' z (S˘ ʻʻ A))) :
    refs R A = S ʻʻ refs R' (S˘ ʻʻ A) := by
  obtain ⟨-, -, hfP, -⟩ := a2_smor_facts hS
  ext x
  constructor
  · intro hx
    obtain ⟨z, hxz⟩ := (hfP x).1 (hR x hx)
    exact ⟨z, (htr x z hxz).1 hx, hxz⟩
  · rintro ⟨z, hz, hxz⟩
    exact (htr x z hxz).2 hz

private theorem a2_img_mem_one_iff {Q : β → β → Prop} {S : α → β → Prop} (hS : S ∈ smorbar P Q)
    {X : Set β} (hX : X ⊆ fld Q) : S ʻʻ X ∈ one ↔ X ∈ one := by
  obtain ⟨⟨hom, hmo⟩, -, -, hfQ⟩ := a2_smor_facts hS
  rw [mem_one_iff, mem_one_iff]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz, hxz⟩ := (hx x).2 rfl
    refine ⟨z, fun w => ⟨fun hw => ?_, fun e => e ▸ hz⟩⟩
    obtain ⟨u, huw⟩ := (hfQ w).1 (hX hw)
    have e : u = x := (hx u).1 ⟨w, hw, huw⟩
    rw [e] at huw
    exact hmo x w z ⟨huw, hxz⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, hxz⟩ := (hfQ z).1 (hX ((hz z).2 rfl))
    refine ⟨x, fun u => ⟨?_, fun e => ⟨z, (hz z).2 rfl, e ▸ hxz⟩⟩⟩
    rintro ⟨w, hw, huw⟩
    have e : w = z := (hz w).1 hw
    rw [e] at huw
    exact hom u x z ⟨huw, hxz⟩

private theorem a2_smor_EDesc {Q : β → β → Prop} {S : α → β → Prop} {R : α → Set α → Prop}
    {R' : β → Set β → Prop} (hS : S ∈ smorbar P Q) (hR : ∀ x, R x A → x ∈ fld P)
    (hR' : ∀ z, R' z (S˘ ʻʻ A) → z ∈ fld Q) (htr : ∀ x z, S x z → (R x A ↔ R' z (S˘ ʻʻ A))) :
    EDesc R A ↔ EDesc R' (S˘ ʻʻ A) := by
  rw [← refs_mem_one_iff, ← refs_mem_one_iff, a2_smor_refs hS hR htr]
  exact a2_img_mem_one_iff hS hR'

private theorem a2_smor_desc {Q : β → β → Prop} {S : α → β → Prop} {R : α → Set α → Prop}
    {R' : β → Set β → Prop} (hS : S ∈ smorbar P Q) (hR : ∀ x, R x A → x ∈ fld P)
    (hR' : ∀ z, R' z (S˘ ʻʻ A) → z ∈ fld Q) (htr : ∀ x z, S x z → (R x A ↔ R' z (S˘ ʻʻ A)))
    (hE : EDesc R A) : Desc R A (fun s => Desc2 S R' (S˘ ʻʻ A) (fun t => s = t)) := by
  obtain ⟨⟨hom, hmo⟩, -, hfP, hfQ⟩ := a2_smor_facts hS
  obtain ⟨s, hs1⟩ := a2_EDesc_exists hE
  have hu : ∀ b, R b A → b = s := fun b hb => a2_EDesc_uniq hE hb hs1
  obtain ⟨t, hst⟩ := (hfP s).1 (hR s hs1)
  have ht : R' t (S˘ ʻʻ A) := (htr s t hst).1 hs1
  have htu : ∀ b, R' b (S˘ ʻʻ A) → b = t := by
    intro b hb
    obtain ⟨u, hub⟩ := (hfQ b).1 (hR' b hb)
    have e : u = s := hu u ((htr u b hub).2 hb)
    rw [e] at hub
    exact hmo s b t ⟨hub, hst⟩
  refine a2_desc_intro hs1 hu ?_
  rw [desc2_iff]
  exact a2_desc_intro ht htu (a2_desc_intro hst (fun b hb => hom b s t ⟨hb, hst⟩) rfl)

end Aux

/-!
## [✱206] Sequent points

*(Vol. 2, p. 577)*

> *Summary of* *206.
>
> A "sequent" of a class \(\alpha\) is a minimum of the terms that come after the whole of \(\alpha \cap CʻP\); that is, we put \[ \overrightarrow{\text{seq}} _{P}ʻ\alpha =\overrightarrow{\text{min}}_{P}ʻpʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP). \] Thus the sequents of \(\alpha\) are its immediate successors. If \(\alpha\) has a maximum, the sequents are the immediate successors of the maximum; but if \(\alpha\) has no maximum, there will be no one term of \(\alpha\) which is immediately succeeded by a sequent of \(\alpha\); in this case, if \(\alpha\) has a single sequent, the sequent is the "upper limit" of \(\alpha\). Whenever \(P\) is connected, and therefore whenever \(P\) is serial, every class has one sequent or none with respect to \(P\), by *205·3.
>
> It will be seen that the sequents of \(\alpha\) are the same as the sequents of \(\alpha \cap CʻP\), and therefore that \(\overrightarrow{\text{seq}}_{P}ʻ\alpha\) depends only upon \(\alpha\cap CʻP\): if \(\alpha\) has terms not belonging to \(CʻP\), they are irrelevant.
>
> …

**Lean reading.** `x seq_P α` is `seqP P x A`, `seq⃗_P'α` is `refs (seqP P) A`, and a
description `ψ(seq_P'α)` is `Desc (seqP P) A ψ` (`E!seq_P'α` is `EDesc (seqP P) A`); likewise
`prec_P` (`precP P`), `min_P`, `max_P` (`minP P`, `maxP P`). `p'P⃖''(α ∩ C'P)` (the terms
following the whole of `α ∩ C'P`) is `prodCls (Rbwd P ʻʻ (A ∩ fld P))`, `p'P⃗''…` is
`prodCls (Rfwd P ʻʻ …)`; `P⃗'x`, `P⃖'x` are `refs P x`, `rels P x`; `P''α` is `P ʻʻ A`;
`ι'x` (printed `℩'x`) is `ι x`; `B⃗'P` is `refs Beg P`; `0 ∪ 1` is `zero ∪ one` and `1 → Cls`
is `arrow one Cls`; `P −̇ P²` is `P ∸ rsq P`; `P_1` is `P1 P` (Defs/Part5, encoding decision 3)
and `P̆_1'x` is `Desc (P1 P)˘ x ψ`; `trans` is `transR`; `S'x` with `S` one-one is `Desc S x ψ`
and `S'seq_Q'…` is `Desc2`. PM's `∃!` of a class is `Set.Nonempty`. Products in hypotheses
bracket to the left, chains of `=` are conjunctions of their links, and of two descriptions the
first has the larger scope. The proofs work directly from `seqP_iff`, `maxP_iff`, `mem_connex`,
`mem_transR`; the transfer by a correlator (✱206·6–·63) goes pointwise through the one-one `S`.
✱206·6 is false as printed when `α ∩ C'P = Λ` (then the left side is `V` and the right side
`C'P`); the corrected form intersects the left side with `C'P`.

**Status.** proved (all propositions; ✱206·6 proved (corrected), see its docstring).
-/

/-- ✱206·01 (Df). \(\text{seq}_{P}=\hat{x} \hat{\alpha} \{x\text{min}_{P}pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\} \quad\text{Df}\) -/
theorem pm206_01 : seqP P = fun x A => minP P x (prodCls (Rbwd P ʻʻ (A ∩ fld P))) := rfl

/-- ✱206·02 (Df). \(\text{prec}_{P}=\hat{x} \hat{\alpha} \{x\text{max}_{P}pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)\} \quad\text{Df}\) -/
theorem pm206_02 : precP P = fun x A => maxP P x (prodCls (Rfwd P ʻʻ (A ∩ fld P))) := rfl

/-- ✱206·1. \(\vdash :x\text{seq}_{P}\alpha .\equiv .x\text{min}_{P}pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP) \quad[(*206·01)]\) -/
theorem pm206_1 : seqP P x A ↔ minP P x (prodCls (Rbwd P ʻʻ (A ∩ fld P))) := Iff.rfl

/-- ✱206·101. \(\vdash .\text{prec}_{P}=\text{seq}(\breve{P} ) \quad[*32·241.*33·22.*205·102]\) -/
theorem pm206_101 : precP P = seqP P˘ := precP_eq_seqP_cnv P

/-- ✱206·11. \[\begin{align}&\vdash :x\text{seq}_{P}\alpha .\equiv .x\in pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\cap CʻP-\breve{P} ʻʻpʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\\ &[*206·1.*205·1]\end{align}\] -/
theorem pm206_11 : seqP P x A ↔
    x ∈ (prodCls (Rbwd P ʻʻ (A ∩ fld P)) ∩ fld P) \ P˘ ʻʻ prodCls (Rbwd P ʻʻ (A ∩ fld P)) :=
  Iff.rfl

/-- ✱206·12. \[\begin{align}\vdash \colon\colon &x\text{seq}_{P}\alpha .\equiv \colon\ldotp y\in \alpha \cap CʻP.\supset _{y}.yPx:x\in CʻP\colon\ldotp \\ &y\in \alpha \cap CʻP.\supset _{y}.yPz:\supset _{z}.{\sim}(zPx) \quad[*206·11.*40·53.*37·105]\end{align}\] -/
theorem pm206_12 : seqP P x A ↔ ((∀ y, y ∈ A ∩ fld P → P y x) ∧ x ∈ fld P) ∧
    ∀ z, (∀ y, y ∈ A ∩ fld P → P y z) → ¬P z x := seqP_iff

/-- ✱206·13. \(\vdash .\overrightarrow{\text{seq}} _{P}ʻ\alpha =\overrightarrow{\text{min}}_{P}pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP) \quad[*206·1]\) -/
theorem pm206_13 :
    refs (seqP P) A = refs (minP P) (prodCls (Rbwd P ʻʻ (A ∩ fld P))) := rfl

/-- ✱206·131. \(\vdash .\overrightarrow{\text{seq}} _{P}ʻ\alpha =\overrightarrow{\text{seq}} _{P}ʻ(\alpha \cap CʻP) \quad[*206·13.*22·43·621]\) -/
theorem pm206_131 : refs (seqP P) A = refs (seqP P) (A ∩ fld P) := by
  apply a2_seq_congr_pi
  rw [Set.inter_assoc, Set.inter_self]

/-- ✱206·132. \(\vdash . \overrightarrow{\text{seq}} _{P}ʻ\alpha = pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP) \cap CʻP - \breve{P} ʻʻpʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP) \quad[*206·11]\) -/
theorem pm206_132 : refs (seqP P) A =
    (prodCls (Rbwd P ʻʻ (A ∩ fld P)) ∩ fld P) \ P˘ ʻʻ prodCls (Rbwd P ʻʻ (A ∩ fld P)) := rfl

/-- ✱206·133. \(\vdash : x \text{seq}_{P}\alpha . \supset . {\sim} (xPx) \quad[*205·194 . *206·13]\) -/
theorem pm206_133 : seqP P x A → ¬P x x := by
  intro hs hxx
  have hs' := seqP_iff.1 hs
  exact hs'.2 x hs'.1.1 hxx

/-- ✱206·134. \(\vdash . \overrightarrow{\text{seq}} _{P}ʻ\alpha = CʻP \cap \hat{x} \{\alpha \cap CʻP \subset \overrightarrow{P}ʻx . \overrightarrow{P}ʻx \subset - pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\}\) -/
theorem pm206_134 : refs (seqP P) A = fld P ∩
    {x | A ∩ fld P ⊆ refs P x ∧ refs P x ⊆ (prodCls (Rbwd P ʻʻ (A ∩ fld P)))ᶜ} := by
  ext x
  show seqP P x A ↔ x ∈ fld P ∧
    (A ∩ fld P ⊆ refs P x ∧ refs P x ⊆ (prodCls (Rbwd P ʻʻ (A ∩ fld P)))ᶜ)
  rw [seqP_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h2, fun y hy => h1 y hy, fun z hzx hzπ => h3 z (mem_prodCls_Rbwd.1 hzπ) hzx⟩
  · rintro ⟨h2, h1, h3⟩
    exact ⟨⟨fun y hy => h1 hy, h2⟩, fun z hz hzx => h3 hzx (mem_prodCls_Rbwd.2 hz)⟩

/-- ✱206·14. \(\vdash : \alpha \cap CʻP = \Lambda . \supset . \overrightarrow{\text{seq}} _{P}ʻ\alpha = \overrightarrow{B}ʻP\) -/
theorem pm206_14 : A ∩ fld P = Λ → refs (seqP P) A = refs Beg P := by
  intro h
  have hA : ∀ y, y ∉ A ∩ fld P := a2_eq_Null_iff.1 h
  ext x
  show seqP P x A ↔ x ∈ dom P \ codom P
  rw [seqP_iff]
  constructor
  · rintro ⟨⟨-, hx⟩, hmin⟩
    have hnc : x ∉ codom P := fun ⟨y, hyx⟩ => hmin y (fun w hw => absurd hw (hA w)) hyx
    obtain ⟨y, hy | hy⟩ := hx
    · exact ⟨⟨y, hy⟩, hnc⟩
    · exact absurd ⟨y, hy⟩ hnc
  · rintro ⟨⟨y, hxy⟩, hnc⟩
    exact ⟨⟨fun w hw => absurd hw (hA w), ⟨y, Or.inl hxy⟩⟩, fun z _ hzx => hnc ⟨z, hzx⟩⟩

/-- ✱206·141. \(\vdash : \exists ! \alpha \cap CʻP . \supset . \overrightarrow{\text{seq}} _{P}ʻ\alpha = pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP) - \breve{P} ʻʻpʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\) -/
theorem pm206_141 : (A ∩ fld P).Nonempty → refs (seqP P) A =
    prodCls (Rbwd P ʻʻ (A ∩ fld P)) \ P˘ ʻʻ prodCls (Rbwd P ʻʻ (A ∩ fld P)) := by
  rintro ⟨a, ha⟩
  ext x
  show x ∈ (prodCls (Rbwd P ʻʻ (A ∩ fld P)) ∩ fld P) \ P˘ ʻʻ prodCls (Rbwd P ʻʻ (A ∩ fld P)) ↔ _
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, a2_fr (mem_prodCls_Rbwd.1 h1 a ha)⟩, h2⟩

/-- ✱206·142. \(\vdash : \exists ! \alpha \cap CʻP . \supset . \overrightarrow{\text{seq}} _{P}ʻ\alpha \subset \breve{P} ʻʻ\alpha \quad[*40·61 . *206·141]\) -/
theorem pm206_142 : (A ∩ fld P).Nonempty → refs (seqP P) A ⊆ P˘ ʻʻ A := by
  rintro ⟨a, ha⟩ x hx
  have hx' : seqP P x A := hx
  exact ⟨a, ha.1, (seqP_iff.1 hx').1.1 a ha⟩

/-- ✱206·143. \[\begin{align}&\vdash : \alpha \subset CʻP . \supset . \overrightarrow{\text{seq}} _{P}ʻ\alpha = pʻ\overleftarrow{P}ʻʻ\alpha \cap CʻP - \breve{P} ʻʻpʻ\overleftarrow{P}ʻʻ\alpha \\ &[*206·132 . *22·621]\end{align}\] -/
theorem pm206_143 : A ⊆ fld P → refs (seqP P) A =
    (prodCls (Rbwd P ʻʻ A) ∩ fld P) \ P˘ ʻʻ prodCls (Rbwd P ʻʻ A) := by
  intro h
  have e : A ∩ fld P = A := Set.inter_eq_left.2 h
  rw [pm206_132, e]

/-- ✱206·144. \(\vdash : \exists ! \overrightarrow{\text{seq}} _{P}ʻ\alpha . \supset . \exists ! pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP) \quad[*206·132]\) -/
theorem pm206_144 :
    (refs (seqP P) A).Nonempty → (prodCls (Rbwd P ʻʻ (A ∩ fld P))).Nonempty := by
  rintro ⟨x, hx⟩
  exact ⟨x, hx.1.1⟩

/-- ✱206·15. \[\begin{align}&\vdash : \alpha \subset CʻP . \exists ! \alpha . \supset . \overrightarrow{\text{seq}} _{P}ʻ\alpha = pʻ\overleftarrow{P}ʻʻ\alpha - \breve{P} ʻʻpʻ\overleftarrow{P}ʻʻ\alpha\\ &[*206·141 . *22·621]\end{align}\] -/
theorem pm206_15 : A ⊆ fld P ∧ A.Nonempty →
    refs (seqP P) A = prodCls (Rbwd P ʻʻ A) \ P˘ ʻʻ prodCls (Rbwd P ʻʻ A) := by
  rintro ⟨h1, h2⟩
  have e : A ∩ fld P = A := Set.inter_eq_left.2 h1
  have h := pm206_141 (P := P) (A := A) (by rw [e]; exact h2)
  rw [h, e]

/-- ✱206·16. \(\vdash : P \in \text{connex} . \supset . \overrightarrow{\text{seq}} _{P}ʻ\alpha \in 0 \cup 1 \quad[*205·3 . *206·13]\) -/
theorem pm206_16 : P ∈ connex → refs (seqP P) A ∈ zero ∪ one :=
  fun hc => a2_mem_zero_union_one.2 fun _ _ ha hb => a2_seq_uniq hc ha hb

/-- ✱206·161. \(\vdash : P \in \text{connex} . \supset . \text{seq}_{P} \in 1 \rightarrow \text{Cls} \quad[*206·16 . *71·12]\) -/
theorem pm206_161 : P ∈ connex → seqP P ∈ arrow one Cls :=
  fun hc => mem_arrow_one_Cls.2 fun _ _ _ h => a2_seq_uniq hc h.1 h.2

/-- ✱206·17. \[\begin{align}\vdash \colon\ldotp x \text{seq}_{P}\alpha .\equiv :y\in \alpha \cap CʻP.\supset _{y}.&yPx:x\in CʻP:\\ &yPx.\supset _{y}.(\exists z).z\in \alpha \cap CʻP.{\sim}(zPy)\end{align}\] -/
theorem pm206_17 : seqP P x A ↔ ((∀ y, y ∈ A ∩ fld P → P y x) ∧ x ∈ fld P) ∧
    ∀ y, P y x → ∃ z, z ∈ A ∩ fld P ∧ ¬P z y := by
  rw [seqP_iff]
  refine and_congr Iff.rfl ⟨fun h y hyx => ?_, fun h z hz hzx => ?_⟩
  · by_contra hn
    push Not at hn
    exact h y hn hyx
  · obtain ⟨w, hw, hn⟩ := h z hzx
    exact hn (hz w hw)

/-- ✱206·171. \[\begin{align}\vdash :P\in &\text{connex} .P^{2}\,\unicode{x2abd}\, J.\supset .\\ &\overrightarrow{\text{seq}} _{P}ʻ\alpha =CʻP\cap \hat{x} \{\alpha \cap CʻP\subset \overrightarrow{P}ʻx.\overrightarrow{P}ʻx\subset (\alpha \cap CʻP)\cup Pʻʻ\alpha\}\end{align}\] -/
theorem pm206_171 : P ∈ connex ∧ rsq P ⪽ J → refs (seqP P) A =
    fld P ∩ {x | A ∩ fld P ⊆ refs P x ∧ refs P x ⊆ (A ∩ fld P) ∪ P ʻʻ A} := by
  rintro ⟨hc, hJ⟩
  ext x
  show seqP P x A ↔ x ∈ fld P ∧ (A ∩ fld P ⊆ refs P x ∧ refs P x ⊆ (A ∩ fld P) ∪ P ʻʻ A)
  constructor
  · intro hs
    have hs' := seqP_iff.1 hs
    exact ⟨hs'.1.2, fun y hy => hs'.1.1 y hy, a2_seq_pred_sub hc hs⟩
  · rintro ⟨hx, h1, h2⟩
    rw [seqP_iff]
    refine ⟨⟨fun y hy => h1 hy, hx⟩, fun z hz hzx => ?_⟩
    rcases h2 hzx with hz' | ⟨w, hw, hzw⟩
    · exact a2_asymm hJ (hz z hz') (hz z hz')
    · exact a2_asymm hJ hzw (hz w ⟨hw, a2_fr hzw⟩)

/-- ✱206·172. \[\begin{align}\vdash :P\in &\text{connex} .P^{2}\,\unicode{x2abd}\, J.Pʻʻ\alpha \subset \alpha .\supset .\\ &\overrightarrow{\text{seq}} _{P}ʻ\alpha =CʻP\cap \hat{x} (\alpha \cap CʻP=\overrightarrow{P}ʻx) \quad[*206·171.*22·62]\end{align}\] -/
theorem pm206_172 : (P ∈ connex ∧ rsq P ⪽ J) ∧ P ʻʻ A ⊆ A →
    refs (seqP P) A = fld P ∩ {x | A ∩ fld P = refs P x} := by
  rintro ⟨h, hA⟩
  rw [pm206_171 h]
  have e : (A ∩ fld P) ∪ P ʻʻ A = A ∩ fld P := by
    apply Set.union_eq_left.2
    rintro z ⟨w, hw, hzw⟩
    exact ⟨hA ⟨w, hw, hzw⟩, a2_fl hzw⟩
  ext x
  show x ∈ fld P ∧ (A ∩ fld P ⊆ refs P x ∧ refs P x ⊆ (A ∩ fld P) ∪ P ʻʻ A) ↔
    x ∈ fld P ∧ A ∩ fld P = refs P x
  rw [e, Set.Subset.antisymm_iff]

/-- ✱206·173. \[\begin{align}\vdash :P\in &\text{connex} .P^{2}\,\unicode{x2abd}\, J.\alpha \cap CʻP\subset Pʻʻ\alpha .\supset .\\ &\overrightarrow{\text{seq}} _{P}ʻ\alpha =CʻP\cap \hat{x} \{\alpha \cap CʻP\subset \overrightarrow{P}ʻx.\overrightarrow{P}ʻx\subset Pʻʻ\alpha\} &[*206·171.*22·62]\end{align}\] -/
theorem pm206_173 : (P ∈ connex ∧ rsq P ⪽ J) ∧ A ∩ fld P ⊆ P ʻʻ A →
    refs (seqP P) A = fld P ∩ {x | A ∩ fld P ⊆ refs P x ∧ refs P x ⊆ P ʻʻ A} := by
  rintro ⟨h, hA⟩
  rw [pm206_171 h, Set.union_eq_right.2 hA]

/-- ✱206·174. \(\vdash :P\in \text{Ser}.\alpha \cap CʻP\subset Pʻʻ\alpha .\supset .\overrightarrow{\text{seq}} _{P}ʻ\alpha =CʻP\cap \hat{x} (\overrightarrow{P}ʻx=Pʻʻ\alpha )\) -/
theorem pm206_174 : P ∈ Ser ∧ A ∩ fld P ⊆ P ʻʻ A →
    refs (seqP P) A = fld P ∩ {x | refs P x = P ʻʻ A} := by
  rintro ⟨hS, hA⟩
  rw [pm206_173 ⟨⟨hS.2, a2_rsqJ_of_Ser hS⟩, hA⟩]
  ext x
  show x ∈ fld P ∧ (A ∩ fld P ⊆ refs P x ∧ refs P x ⊆ P ʻʻ A) ↔ x ∈ fld P ∧ refs P x = P ʻʻ A
  constructor
  · rintro ⟨hx, h1, h2⟩
    refine ⟨hx, Set.Subset.antisymm h2 ?_⟩
    rintro z ⟨w, hw, hzw⟩
    exact mem_transR.1 hS.1.2 z w x ⟨hzw, h1 ⟨hw, a2_fr hzw⟩⟩
  · rintro ⟨hx, he⟩
    exact ⟨hx, fun z hz => by rw [he]; exact hA hz, he.subset⟩

/-- ✱206·18. \(\vdash .\overrightarrow{\text{seq}} _{P}ʻ\alpha \subset CʻP \quad[*206·132]\) -/
theorem pm206_18 : refs (seqP P) A ⊆ fld P := fun _ hx => hx.1.2

/-- ✱206·181. \(\vdash :\exists !\alpha \cap CʻP.\supset .\overrightarrow{\text{seq}} _{P}ʻ\alpha \subset \text{ᗡ}ʻP \quad[*206·142.*37·16]\) -/
theorem pm206_181 : (A ∩ fld P).Nonempty → refs (seqP P) A ⊆ codom P := by
  rintro ⟨a, ha⟩ x hx
  have hx' : seqP P x A := hx
  exact ⟨a, (seqP_iff.1 hx').1.1 a ha⟩

/-- ✱206·2. \(\vdash .\overrightarrow{\text{seq}} _{P}ʻ\alpha \subset -\alpha\) -/
theorem pm206_2 : refs (seqP P) A ⊆ Aᶜ := by
  intro x hx hxA
  have hx' := seqP_iff.1 (show seqP P x A from hx)
  exact hx'.2 x hx'.1.1 (hx'.1.1 x ⟨hxA, hx'.1.2⟩)

/-- ✱206·21. \(\vdash :P^{2}\,\unicode{x2abd}\, J.\supset .\overrightarrow{\text{seq}} _{P}ʻ\alpha \subset -Pʻʻ\alpha \quad[*200·53.*206·132]\) -/
theorem pm206_21 : rsq P ⪽ J → refs (seqP P) A ⊆ (P ʻʻ A)ᶜ := by
  rintro hJ x hx ⟨w, hw, hxw⟩
  have hx' := seqP_iff.1 (show seqP P x A from hx)
  exact a2_asymm hJ hxw (hx'.1.1 w ⟨hw, a2_fr hxw⟩)

/-- ✱206·211. \(\vdash :\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\alpha \cap CʻP\subset \overrightarrow{P}ʻ\text{seq}_{P}ʻ\alpha\) -/
theorem pm206_211 : EDesc (seqP P) A → Desc (seqP P) A (fun s => A ∩ fld P ⊆ refs P s) :=
  fun h => a2_desc_iff.2 ⟨h, fun _ hs y hy => (seqP_iff.1 hs).1.1 y hy⟩

/-- ✱206·212. \(\vdash :P\in \text{trans}.\text{E}!\text{seq}_{P}ʻ\alpha .\supset .Pʻʻ\alpha \subset \overrightarrow{P}ʻ\text{seq}_{P}ʻ\alpha\) -/
theorem pm206_212 : P ∈ transR ∧ EDesc (seqP P) A →
    Desc (seqP P) A (fun s => P ʻʻ A ⊆ refs P s) := by
  rintro ⟨ht, h⟩
  refine a2_desc_iff.2 ⟨h, fun s hs => ?_⟩
  rintro z ⟨w, hw, hzw⟩
  exact mem_transR.1 ht z w s ⟨hzw, (seqP_iff.1 hs).1.1 w ⟨hw, a2_fr hzw⟩⟩

/-- ✱206·213. \(\vdash :P\in \text{connex} .\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\overrightarrow{P}ʻ\text{seq}_{P}ʻ\alpha \subset (\alpha \cap CʻP)\cup Pʻʻ\alpha\) -/
theorem pm206_213 : P ∈ connex ∧ EDesc (seqP P) A →
    Desc (seqP P) A (fun s => refs P s ⊆ (A ∩ fld P) ∪ P ʻʻ A) := by
  rintro ⟨hc, h⟩
  exact a2_desc_iff.2 ⟨h, fun s hs => a2_seq_pred_sub hc hs⟩

/-- ✱206·22. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .&\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\\ &\overrightarrow{P}ʻ\text{seq}_{P}ʻ\alpha =(\alpha \cap CʻP)\cup Pʻʻ\alpha =\overrightarrow{\text{max}}_{P}ʻ\alpha \cup Pʻʻ\alpha \\ &[*206·211·212·213.*205·131]\end{align}\] -/
theorem pm206_22 : P ∈ transR ∩ connex ∧ EDesc (seqP P) A →
    Desc (seqP P) A (fun s => refs P s = (A ∩ fld P) ∪ P ʻʻ A) ∧
      (A ∩ fld P) ∪ P ʻʻ A = refs (maxP P) A ∪ P ʻʻ A := by
  rintro ⟨⟨ht, hc⟩, h⟩
  refine ⟨a2_desc_iff.2 ⟨h, fun s hs => Set.Subset.antisymm (a2_seq_pred_sub hc hs) ?_⟩,
    a2_inter_fld_union_img⟩
  rintro z (hz | ⟨w, hw, hzw⟩)
  · exact (seqP_iff.1 hs).1.1 z hz
  · exact mem_transR.1 ht z w s ⟨hzw, (seqP_iff.1 hs).1.1 w ⟨hw, a2_fr hzw⟩⟩

/-- ✱206·23. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .&\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\\ &\iota ʻ\text{seq}_{P}ʻ\alpha \cup \overleftarrow{P}ʻ\text{seq}_{P}ʻ\alpha =pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\cap CʻP\end{align}\] -/
theorem pm206_23 : P ∈ transR ∩ connex ∧ EDesc (seqP P) A →
    Desc (seqP P) A (fun s => ι s ∪ rels P s = prodCls (Rbwd P ʻʻ (A ∩ fld P)) ∩ fld P) := by
  rintro ⟨⟨ht, hc⟩, h⟩
  refine a2_desc_iff.2 ⟨h, fun s hs => ?_⟩
  have hs' := seqP_iff.1 hs
  ext z
  constructor
  · rintro (hz | hsz)
    · have e : z = s := hz
      rw [e]
      exact ⟨mem_prodCls_Rbwd.2 hs'.1.1, hs'.1.2⟩
    · have hsz' : P s z := hsz
      exact ⟨mem_prodCls_Rbwd.2 fun y hy => mem_transR.1 ht y s z ⟨hs'.1.1 y hy, hsz'⟩,
        a2_fr hsz'⟩
  · rintro ⟨hz, hzf⟩
    rcases mem_connex.1 hc z s ⟨hzf, hs'.1.2⟩ with (h1 | h1) | h1
    · exact absurd h1 (hs'.2 z (mem_prodCls_Rbwd.1 hz))
    · exact Or.inl h1
    · exact Or.inr h1

/-- ✱206·24. \(\vdash : P \in \text{trans} . \beta \subset Pʻʻ\alpha . \supset . \overrightarrow{\text{seq}} _{P}ʻ(\alpha \cup \beta ) = \overrightarrow{\text{seq}} _{P}ʻ\alpha\) -/
theorem pm206_24 : P ∈ transR ∧ B ⊆ P ʻʻ A → refs (seqP P) (A ∪ B) = refs (seqP P) A := by
  rintro ⟨ht, hB⟩
  apply a2_seq_congr_pi
  apply a2_pi_ext
  intro z
  constructor
  · intro h y hy
    exact h y ⟨Or.inl hy.1, hy.2⟩
  · rintro h y ⟨hy | hy, hyf⟩
    · exact h y ⟨hy, hyf⟩
    · obtain ⟨w, hw, hyw⟩ := hB hy
      exact mem_transR.1 ht y w z ⟨hyw, h w ⟨hw, a2_fr hyw⟩⟩

/-- ✱206·25. \(\vdash : P \in \text{trans} . \supset . \overrightarrow{\text{seq}} _{P}ʻ(\alpha \cup Pʻʻ\alpha ) = \overrightarrow{\text{seq}} _{P}ʻ\alpha \quad[*206·24]\) -/
theorem pm206_25 : P ∈ transR → refs (seqP P) (A ∪ P ʻʻ A) = refs (seqP P) A :=
  fun ht => pm206_24 ⟨ht, fun _ h => h⟩

/-- ✱206·26. \[\begin{align}\vdash : P \in \text{trans} \cap \text{connex} . \exists ! \alpha \cap &CʻP . \text{E}! \text{seq}_{P}ʻ\alpha . \supset .\\ &pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP) = {℩}ʻ\text{seq}_{P}ʻ\alpha \cup \overleftarrow{P}ʻ\text{seq}_{P}ʻ\alpha\end{align}\] -/
theorem pm206_26 : (P ∈ transR ∩ connex ∧ (A ∩ fld P).Nonempty) ∧ EDesc (seqP P) A →
    Desc (seqP P) A (fun s => prodCls (Rbwd P ʻʻ (A ∩ fld P)) = ι s ∪ rels P s) := by
  rintro ⟨⟨h1, ⟨a, ha⟩⟩, h⟩
  have h23 := pm206_23 ⟨h1, h⟩
  refine a2_desc_iff.2 ⟨h, fun s hs => ?_⟩
  rw [(a2_desc_iff.1 h23).2 s hs]
  exact (Set.inter_eq_left.2 fun z hz => a2_fr (mem_prodCls_Rbwd.1 hz a ha)).symm

/-- ✱206·27. \[\begin{align}\vdash : P \in \text{trans} \cap \text{connex} . \text{E}! \text{seq}_{P}ʻ&\alpha . \text{E}! \text{max}_{P}ʻ\alpha . \supset .\\ &\overrightarrow{P}ʻ\text{seq}_{P}ʻ\alpha = \overrightarrow{P}ʻ\text{max}_{P}ʻ\alpha \cup {℩}ʻ\text{max}_{P}ʻ\alpha.\\ &\overleftarrow{P}ʻ\text{max}_{P}ʻ\alpha = \overleftarrow{P}ʻ\text{seq}_{P}ʻ\alpha \cup {℩}ʻ\text{seq}_{P}ʻ\alpha\end{align}\] -/
theorem pm206_27 : (P ∈ transR ∩ connex ∧ EDesc (seqP P) A) ∧ EDesc (maxP P) A →
    Desc (seqP P) A (fun s => Desc (maxP P) A (fun m => refs P s = refs P m ∪ ι m)) ∧
      Desc (maxP P) A (fun m => Desc (seqP P) A (fun s => rels P m = rels P s ∪ ι s)) := by
  rintro ⟨⟨⟨ht, hc⟩, hs⟩, hm⟩
  have tr := mem_transR.1 ht
  obtain ⟨s, hs1⟩ := a2_EDesc_exists hs
  obtain ⟨m, hm1⟩ := a2_EDesc_exists hm
  have hsu : ∀ b, seqP P b A → b = s := fun b hb => a2_EDesc_uniq hs hb hs1
  have hmu : ∀ b, maxP P b A → b = m := fun b hb => a2_EDesc_uniq hm hb hm1
  have hs' := seqP_iff.1 hs1
  have hm' := maxP_iff.1 hm1
  have hms : P m s := hs'.1.1 m hm'.1
  refine ⟨a2_desc_intro hs1 hsu (a2_desc_intro hm1 hmu ?_),
    a2_desc_intro hm1 hmu (a2_desc_intro hs1 hsu ?_)⟩
  · ext z
    constructor
    · intro hz
      rcases a2_seq_pred_sub hc hs1 hz with hz' | ⟨w, hw, hzw⟩
      · rcases mem_connex.1 hc z m ⟨hz'.2, hm'.1.2⟩ with (h | h) | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h (hm'.2 z hz'.1)
      · rcases mem_connex.1 hc w m ⟨a2_fr hzw, hm'.1.2⟩ with (h | h) | h
        · exact Or.inl (tr z w m ⟨hzw, h⟩)
        · have hzm : P z m := by rw [← h]; exact hzw
          exact Or.inl hzm
        · exact absurd h (hm'.2 w hw)
    · rintro (hz | hz)
      · exact tr z m s ⟨hz, hms⟩
      · have e : z = m := hz
        show P z s
        rw [e]
        exact hms
  · ext z
    constructor
    · intro hz
      have hmz : P m z := hz
      rcases mem_connex.1 hc z s ⟨a2_fr hmz, hs'.1.2⟩ with (h | h) | h
      · exfalso
        apply hs'.2 z _ h
        intro y hy
        rcases mem_connex.1 hc y m ⟨hy.2, hm'.1.2⟩ with (h' | h') | h'
        · exact tr y m z ⟨h', hmz⟩
        · rw [h']
          exact hmz
        · exact absurd h' (hm'.2 y hy.1)
      · exact Or.inr h
      · exact Or.inl h
    · rintro (hz | hz)
      · exact tr m s z ⟨hms, hz⟩
      · have e : z = s := hz
        show P m z
        rw [e]
        exact hms

/-- ✱206·28. \[\begin{align}\vdash \colon\ldotp P \in \text{Ser} . &\supset :\\ &x \in CʻP - \alpha . \overrightarrow{P}ʻx = Pʻʻ\alpha . \equiv . x = \text{seq}_{P}ʻ\alpha . {\sim} \text{E}! \text{max}_{P}ʻ\alpha \end{align}\] -/
theorem pm206_28 : P ∈ Ser → (x ∈ fld P \ A ∧ refs P x = P ʻʻ A ↔
    Desc (seqP P) A (fun s => x = s) ∧ ¬EDesc (maxP P) A) := by
  intro hS
  have irr := mem_rl_J.1 hS.1.1
  have tr := mem_transR.1 hS.1.2
  constructor
  · rintro ⟨⟨hx, hxA⟩, he⟩
    have hfol : ∀ y, y ∈ A ∩ fld P → P y x := by
      intro y hy
      rcases mem_connex.1 hS.2 y x ⟨hy.2, hx⟩ with (h | h) | h
      · exact h
      · exact absurd (by rw [← h]; exact hy.1) hxA
      · have hxi : x ∈ P ʻʻ A := ⟨y, hy.1, h⟩
        rw [← he] at hxi
        exact absurd hxi (irr x)
    have hseq : seqP P x A := by
      rw [seqP_iff]
      refine ⟨⟨hfol, hx⟩, fun z hz hzx => ?_⟩
      have hzi : z ∈ refs P x := hzx
      rw [he] at hzi
      obtain ⟨w, hw, hzw⟩ := hzi
      exact irr z (tr z w z ⟨hzw, hz w ⟨hw, a2_fr hzw⟩⟩)
    refine ⟨a2_desc_intro hseq (fun b hb => a2_seq_uniq hS.2 hb hseq) rfl, fun hm => ?_⟩
    obtain ⟨m, hm1⟩ := a2_EDesc_exists hm
    have hm' := maxP_iff.1 hm1
    have hmi : m ∈ refs P x := hfol m hm'.1
    rw [he] at hmi
    obtain ⟨w, hw, hmw⟩ := hmi
    exact hm'.2 w hw hmw
  · rintro ⟨hd, hnm⟩
    obtain ⟨b, hb, hxb⟩ := hd
    have hs1 : seqP P b A := (hb b).2 rfl
    rw [← hxb] at hs1
    have hE : EDesc (seqP P) A := a2_EDesc_of hs1 fun c hc => a2_seq_uniq hS.2 hc hs1
    have h22 := (a2_desc_iff.1 (pm206_22 ⟨⟨hS.1.2, hS.2⟩, hE⟩).1).2 x hs1
    have hsub := a2_noMax_iff_sub.1 (a2_noMax_of hS.2 hnm)
    refine ⟨⟨(seqP_iff.1 hs1).1.2, pm206_2 hs1⟩, ?_⟩
    rw [h22]
    exact Set.union_eq_right.2 hsub

/-- ✱206·3. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .\alpha \subset CʻP.Pʻʻ\alpha \subset &\alpha .\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\\ &\overrightarrow{P}ʻ\text{seq}_{P}ʻ\alpha = \alpha \quad[*206·22]\end{align}\] -/
theorem pm206_3 : ((P ∈ transR ∩ connex ∧ A ⊆ fld P) ∧ P ʻʻ A ⊆ A) ∧ EDesc (seqP P) A →
    Desc (seqP P) A (fun s => refs P s = A) := by
  rintro ⟨⟨⟨h1, hA⟩, hPA⟩, h⟩
  have h22 := (pm206_22 ⟨h1, h⟩).1
  refine a2_desc_iff.2 ⟨h, fun s hs => ?_⟩
  rw [(a2_desc_iff.1 h22).2 s hs, Set.inter_eq_left.2 hA, Set.union_eq_left.2 hPA]

/-- ✱206·31. \[\begin{align}&\vdash :P\in \text{trans} \cap \text{connex} .\text{E}!\text{seq}_{P}ʻPʻʻ\alpha .\supset .\overrightarrow{P}ʻ\text{seq}_{P}ʻPʻʻ\alpha = Pʻʻ\alpha\\ &[*206·3.*201·5]\end{align}\] -/
theorem pm206_31 : P ∈ transR ∩ connex ∧ EDesc (seqP P) (P ʻʻ A) →
    Desc (seqP P) (P ʻʻ A) (fun s => refs P s = P ʻʻ A) := by
  rintro ⟨h1, h⟩
  refine pm206_3 ⟨⟨⟨h1, fun z ⟨_, _, hzw⟩ => a2_fl hzw⟩, ?_⟩, h⟩
  rintro z ⟨w, ⟨v, hv, hwv⟩, hzw⟩
  exact ⟨v, hv, mem_transR.1 h1.1 z w v ⟨hzw, hwv⟩⟩

/-- ✱206·32. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .\text{E}!\text{max}_{P}ʻ\alpha .\text{E}!\text{seq}_{P}ʻ&Pʻʻ\alpha .\supset .\\ &\text{max}_{P}ʻ\alpha = \text{seq}_{P}ʻPʻʻ\alpha\end{align}\] -/
theorem pm206_32 : (P ∈ transR ∩ connex ∧ EDesc (maxP P) A) ∧ EDesc (seqP P) (P ʻʻ A) →
    Desc (maxP P) A (fun m => Desc (seqP P) (P ʻʻ A) (fun s => m = s)) := by
  rintro ⟨⟨⟨ht, hc⟩, hm⟩, hs⟩
  obtain ⟨m, hm1⟩ := a2_EDesc_exists hm
  obtain ⟨s, hs1⟩ := a2_EDesc_exists hs
  refine a2_desc_intro hm1 (fun b hb => a2_EDesc_uniq hm hb hm1)
    (a2_desc_intro hs1 (fun b hb => a2_EDesc_uniq hs hb hs1) ?_)
  have hps : refs P s = P ʻʻ A := (a2_desc_iff.1 (pm206_31 ⟨⟨ht, hc⟩, hs⟩)).2 s hs1
  have hm' := maxP_iff.1 hm1
  have hs' := seqP_iff.1 hs1
  rcases mem_connex.1 hc m s ⟨hm'.1.2, hs'.1.2⟩ with (h | h) | h
  · exfalso
    have hmi : m ∈ refs P s := h
    rw [hps] at hmi
    obtain ⟨w, hw, hmw⟩ := hmi
    exact hm'.2 w hw hmw
  · exact h
  · exfalso
    have hsi : s ∈ P ʻʻ A := ⟨m, hm'.1.1, h⟩
    rw [← hps] at hsi
    exact pm206_133 hs1 hsi

/-- ✱206·33. \(\vdash :P\in \text{trans} \cap \text{connex} .{\sim}\text{E}!\text{max}_{P}ʻ\alpha .\supset .\overrightarrow{\text{seq}} _{P}ʻPʻʻ\alpha = \overrightarrow{\text{seq}} _{P}ʻ\alpha\) -/
theorem pm206_33 : P ∈ transR ∩ connex ∧ ¬EDesc (maxP P) A →
    refs (seqP P) (P ʻʻ A) = refs (seqP P) A := by
  rintro ⟨⟨ht, hc⟩, hn⟩
  have hsub := a2_noMax_iff_sub.1 (a2_noMax_of hc hn)
  apply a2_seq_congr_pi
  apply a2_pi_ext
  intro z
  constructor
  · intro h y hy
    exact h y ⟨hsub hy, hy.2⟩
  · rintro h y ⟨⟨w, hw, hyw⟩, -⟩
    exact mem_transR.1 ht y w z ⟨hyw, h w ⟨hw, a2_fr hyw⟩⟩

/-- ✱206·331. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .{\sim}\text{E}!\text{max}_{P}ʻ\alpha .\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\text{seq}_{P}ʻPʻʻ\alpha =\text{seq}_{P}ʻ\alpha \\ &[*206·33]\end{align}\] -/
theorem pm206_331 : (P ∈ transR ∩ connex ∧ ¬EDesc (maxP P) A) ∧ EDesc (seqP P) A →
    Desc (seqP P) (P ʻʻ A) (fun s => Desc (seqP P) A (fun t => s = t)) := by
  rintro ⟨h, hs⟩
  rw [a2_refs_congr_desc (pm206_33 h)]
  obtain ⟨s, hs1⟩ := a2_EDesc_exists hs
  have hu : ∀ b, seqP P b A → b = s := fun b hb => a2_EDesc_uniq hs hb hs1
  exact a2_desc_intro hs1 hu (a2_desc_intro hs1 hu rfl)

/-- ✱206·34. \(\vdash :P\in \text{Ser}.\supset .\overrightarrow{\text{max}}_{P}ʻ\alpha \subset \overrightarrow{\text{seq}} _{P}ʻPʻʻ\alpha\) -/
theorem pm206_34 : P ∈ Ser → refs (maxP P) A ⊆ refs (seqP P) (P ʻʻ A) := by
  intro hS m hm
  have hm' := maxP_iff.1 hm
  have tr := mem_transR.1 hS.1.2
  have irr := mem_rl_J.1 hS.1.1
  show seqP P m (P ʻʻ A)
  rw [seqP_iff]
  refine ⟨⟨?_, hm'.1.2⟩, ?_⟩
  · rintro w ⟨⟨a, ha, hwa⟩, -⟩
    rcases mem_connex.1 hS.2 a m ⟨a2_fr hwa, hm'.1.2⟩ with (h | h) | h
    · exact tr w a m ⟨hwa, h⟩
    · rw [← h]
      exact hwa
    · exact absurd h (hm'.2 a ha)
  · intro z hz hzm
    exact irr z (hz z ⟨⟨m, hm'.1.1, hzm⟩, a2_fl hzm⟩)

/-- ✱206·35. \(\vdash :P\in \text{Ser}.\text{E}!\text{max}_{P}ʻ\alpha .\supset .\text{max}_{P}ʻ\alpha =\text{seq}_{P}ʻPʻʻ\alpha .\text{E}!\text{seq}_{P}ʻPʻʻ\alpha\) -/
theorem pm206_35 : P ∈ Ser ∧ EDesc (maxP P) A →
    Desc (maxP P) A (fun m => Desc (seqP P) (P ʻʻ A) (fun s => m = s)) ∧
      EDesc (seqP P) (P ʻʻ A) := by
  rintro ⟨hS, hm⟩
  obtain ⟨m, hm1⟩ := a2_EDesc_exists hm
  have h1 : seqP P m (P ʻʻ A) := pm206_34 hS hm1
  have hu : ∀ b, seqP P b (P ʻʻ A) → b = m := fun b hb => a2_seq_uniq hS.2 hb h1
  exact ⟨a2_desc_intro hm1 (fun b hb => a2_EDesc_uniq hm hb hm1) (a2_desc_intro h1 hu rfl),
    a2_EDesc_of h1 hu⟩

/-- ✱206·36. \(\vdash \colon\colon P\in \text{Ser}.\supset \colon\ldotp \text{E}!\text{seq}_{P}ʻPʻʻ\alpha .\equiv :\text{E}!\text{max}_{P}ʻ\alpha .\lor.\text{E}!\text{seq}_{P}ʻ\alpha\) -/
theorem pm206_36 : P ∈ Ser →
    (EDesc (seqP P) (P ʻʻ A) ↔ EDesc (maxP P) A ∨ EDesc (seqP P) A) := by
  intro hS
  by_cases hm : EDesc (maxP P) A
  · exact ⟨fun _ => Or.inl hm, fun _ => (pm206_35 ⟨hS, hm⟩).2⟩
  · rw [a2_refs_congr_EDesc (pm206_33 ⟨⟨hS.1.2, hS.2⟩, hm⟩)]
    exact ⟨Or.inr, fun h => h.resolve_left hm⟩

/-- ✱206·37. \(\vdash :P\in \text{Ser}.\supset .\overrightarrow{\text{seq}} _{P}ʻPʻʻ\alpha =\overrightarrow{\text{min}}_{P}ʻ(\overrightarrow{\text{max}}_{P}ʻ\alpha \cup \overrightarrow{\text{seq}} _{P}ʻ\alpha )\) -/
theorem pm206_37 : P ∈ Ser →
    refs (seqP P) (P ʻʻ A) = refs (minP P) (refs (maxP P) A ∪ refs (seqP P) A) := by
  intro hS
  have irr := mem_rl_J.1 hS.1.1
  have tr := mem_transR.1 hS.1.2
  by_cases hm : ∃ m, maxP P m A
  · obtain ⟨m, hm1⟩ := hm
    have h1 : seqP P m (P ʻʻ A) := pm206_34 hS hm1
    have hmA := (maxP_iff.1 hm1).1
    ext x
    show seqP P x (P ʻʻ A) ↔ minP P x (refs (maxP P) A ∪ refs (seqP P) A)
    rw [minP_iff]
    constructor
    · intro hx
      have e : x = m := a2_seq_uniq hS.2 hx h1
      rw [e]
      refine ⟨⟨Or.inl hm1, hmA.2⟩, ?_⟩
      rintro y (hy | hy) hym
      · have e' : y = m := a2_max_uniq hS.2 hy hm1
        rw [e'] at hym
        exact irr m hym
      · exact irr m (tr m y m ⟨(seqP_iff.1 hy).1.1 m hmA, hym⟩)
    · rintro ⟨⟨hx | hx, -⟩, hn⟩
      · have e : x = m := a2_max_uniq hS.2 hx hm1
        rw [e]
        exact h1
      · exact absurd ((seqP_iff.1 hx).1.1 m hmA) (hn m (Or.inl hm1))
  · rw [pm206_33 ⟨⟨hS.1.2, hS.2⟩, fun h => hm (a2_EDesc_exists h)⟩]
    ext x
    show seqP P x A ↔ minP P x (refs (maxP P) A ∪ refs (seqP P) A)
    rw [minP_iff]
    constructor
    · intro hx
      refine ⟨⟨Or.inr hx, (seqP_iff.1 hx).1.2⟩, ?_⟩
      rintro y (hy | hy) hyx
      · exact hm ⟨y, hy⟩
      · have e : y = x := a2_seq_uniq hS.2 hy hx
        rw [e] at hyx
        exact irr x hyx
    · rintro ⟨⟨hx | hx, -⟩, -⟩
      · exact absurd ⟨x, hx⟩ hm
      · exact hx

/-- ✱206·38. \(\vdash :P\in \text{Ser}.\supset .\overrightarrow{\text{max}}_{P}ʻ\alpha =\alpha \cap \overrightarrow{\text{seq}} _{P}ʻPʻʻ\alpha\) -/
theorem pm206_38 : P ∈ Ser → refs (maxP P) A = A ∩ refs (seqP P) (P ʻʻ A) := by
  intro hS
  ext x
  constructor
  · intro hx
    exact ⟨(maxP_iff.1 hx).1.1, pm206_34 hS hx⟩
  · rintro ⟨hxA, hx⟩
    have hx' : seqP P x (P ʻʻ A) := hx
    exact maxP_iff.2 ⟨⟨hxA, (seqP_iff.1 hx').1.2⟩, fun y hy hxy => pm206_2 hx ⟨y, hy, hxy⟩⟩

/-- ✱206·4. \(\vdash :P\,\unicode{x2abd}\, J.x\in CʻP.\supset .x\text{seq}_{P}\overrightarrow{P}ʻx\) -/
theorem pm206_4 : P ⪽ J ∧ x ∈ fld P → seqP P x (refs P x) := by
  rintro ⟨hJ, hx⟩
  rw [seqP_iff]
  exact ⟨⟨fun y hy => hy.1, hx⟩, fun z hz hzx => hJ z z (hz z ⟨hzx, a2_fl hzx⟩) rfl⟩

/-- ✱206·401. \(\vdash :P\in \text{connex} \cap \text{Rl}ʻJ.x\in CʻP.\supset .x=\text{seq}_{P}ʻ\overrightarrow{P}ʻx \quad[*206·4·161]\) -/
theorem pm206_401 : P ∈ connex ∩ rl J ∧ x ∈ fld P →
    Desc (seqP P) (refs P x) (fun s => x = s) := by
  rintro ⟨⟨hc, hJ⟩, hx⟩
  have h1 := pm206_4 ⟨hJ, hx⟩
  exact a2_desc_intro h1 (fun b hb => a2_seq_uniq hc hb h1) rfl

/-- ✱206·41. \(\vdash .\overrightarrow{\text{min}}_{P}ʻ\overleftarrow{P}ʻx=\overleftarrow{P\dot{-} P^{2}}ʻx \quad[*205·25]\) -/
theorem pm206_41 : refs (minP P) (rels P x) = rels (P ∸ rsq P) x := by
  ext y
  show minP P y (rels P x) ↔ P x y ∧ ¬rsq P x y
  rw [minP_iff]
  constructor
  · rintro ⟨⟨hxy, -⟩, hn⟩
    exact ⟨hxy, fun ⟨z, hxz, hzy⟩ => hn z hxz hzy⟩
  · rintro ⟨hxy, hn⟩
    exact ⟨⟨hxy, a2_fr hxy⟩, fun z hxz hzy => hn ⟨z, hxz, hzy⟩⟩

/-- ✱206·42. \(\vdash :x\in CʻP.\supset .\overrightarrow{\text{seq}} _{P}ʻ{℩}ʻx=\overleftarrow{P\dot{-} P^{2}}ʻx=\overrightarrow{\text{min}}_{P}ʻ\overleftarrow{P}ʻx\) -/
theorem pm206_42 : x ∈ fld P → refs (seqP P) (ι x) = rels (P ∸ rsq P) x ∧
    rels (P ∸ rsq P) x = refs (minP P) (rels P x) := by
  intro hx
  refine ⟨?_, pm206_41.symm⟩
  rw [← pm206_41]
  have e : prodCls (Rbwd P ʻʻ (ι x ∩ fld P)) = rels P x := by
    ext z
    rw [mem_prodCls_Rbwd]
    constructor
    · intro h
      exact h x ⟨rfl, hx⟩
    · rintro h y ⟨hy, -⟩
      have e' : y = x := hy
      rw [e']
      exact h
  ext y
  show minP P y (prodCls (Rbwd P ʻʻ (ι x ∩ fld P))) ↔ minP P y (rels P x)
  rw [e]

/-- ✱206·43. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{Rl}ʻJ.x\in CʻP.\supset .\overrightarrow{\text{seq}} _{P}ʻ{℩}ʻx=\overleftarrow{P}_{1}ʻx\\ &[*206·42.*201·63]\end{align}\] -/
theorem pm206_43 : P ∈ transR ∩ rl J ∧ x ∈ fld P → refs (seqP P) (ι x) = rels (P1 P) x := by
  rintro ⟨⟨ht, hJ⟩, hx⟩
  rw [(pm206_42 hx).1]
  ext y
  show P x y ∧ ¬rsq P x y ↔ P1 P x y
  rw [P1_iff_of_transR ht hJ]
  rfl

/-- ✱206·44. \[\begin{align}\vdash \colon\ldotp P\in &\text{trans}\cap \text{Rl}ʻJ.x\in CʻP.\supset :\\ &\text{E}!\text{seq}_{P}ʻ{℩}ʻx.\equiv .\text{E}!\breve{P} _{1}ʻx:\text{E}!\text{seq}_{P}ʻ{℩}ʻx.\supset .\text{seq}_{P}ʻ{℩}ʻx=\breve{P} _{1}ʻx\\ [*206·43]\end{align}\] -/
theorem pm206_44 : P ∈ transR ∩ rl J ∧ x ∈ fld P →
    (EDesc (seqP P) (ι x) ↔ EDesc (P1 P)˘ x) ∧
      (EDesc (seqP P) (ι x) → Desc (seqP P) (ι x) (fun s => Desc (P1 P)˘ x (fun t => s = t))) := by
  intro h
  have e : refs (seqP P) (ι x) = refs (P1 P)˘ x := pm206_43 h
  refine ⟨a2_refs_congr_EDesc e, fun hs => ?_⟩
  obtain ⟨s, hs1⟩ := a2_EDesc_exists hs
  have hu : ∀ b, seqP P b (ι x) → b = s := fun b hb => a2_EDesc_uniq hs hb hs1
  have hs2 : (P1 P)˘ s x := by
    have hm : s ∈ refs (seqP P) (ι x) := hs1
    rw [e] at hm
    exact hm
  refine a2_desc_intro hs1 hu (a2_desc_intro hs2 (fun b hb => ?_) rfl)
  have hm : b ∈ refs (P1 P)˘ x := hb
  rw [← e] at hm
  exact hu b hm

/-- ✱206·45. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.x\in CʻP.\supset :\text{E}!\text{seq}_{P}ʻ{℩}ʻx.\equiv .x\in \text{D}ʻP_{1}\\ &[*206·44.*204·7.*71·165]\end{align}\] -/
theorem pm206_45 : P ∈ Ser ∧ x ∈ fld P → (EDesc (seqP P) (ι x) ↔ x ∈ dom (P1 P)) := by
  rintro ⟨hS, hx⟩
  rw [(pm206_44 ⟨⟨hS.1.2, hS.1.1⟩, hx⟩).1]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := a2_EDesc_exists h
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    refine a2_EDesc_of (show (P1 P)˘ y x from hy) fun b hb => ?_
    have hb' : P1 P x b := hb
    rw [P1_iff_of_transR hS.1.2 hS.1.1] at hy hb'
    rcases mem_connex.1 hS.2 b y ⟨a2_fr hb'.1, a2_fr hy.1⟩ with (h | h) | h
    · exact absurd ⟨b, hb'.1, h⟩ hy.2
    · exact h
    · exact absurd ⟨y, hy.1, h⟩ hb'.2

/-- ✱206·451. \(\vdash :P\in \text{Ser}.\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\overrightarrow{\text{max}}_{P}ʻ\alpha =\overrightarrow{P}_{1}ʻ\text{seq}_{P}ʻ\alpha\) -/
theorem pm206_451 : P ∈ Ser ∧ EDesc (seqP P) A →
    Desc (seqP P) A (fun s => refs (maxP P) A = refs (P1 P) s) := by
  rintro ⟨hS, hs⟩
  have tr := mem_transR.1 hS.1.2
  have h22 := pm206_22 ⟨⟨hS.1.2, hS.2⟩, hs⟩
  refine a2_desc_iff.2 ⟨hs, fun s hs1 => ?_⟩
  have hps : refs P s = (A ∩ fld P) ∪ P ʻʻ A := (a2_desc_iff.1 h22.1).2 s hs1
  have hs' := seqP_iff.1 hs1
  ext t
  show maxP P t A ↔ P1 P t s
  rw [P1_iff_of_transR hS.1.2 hS.1.1, maxP_iff]
  constructor
  · rintro ⟨ht, hn⟩
    refine ⟨hs'.1.1 t ht, fun ⟨z, htz, hzs⟩ => ?_⟩
    have hz : z ∈ refs P s := hzs
    rw [hps] at hz
    rcases hz with hz | ⟨w, hw, hzw⟩
    · exact hn z hz.1 htz
    · exact hn w hw (tr t z w ⟨htz, hzw⟩)
  · rintro ⟨hts, hn⟩
    have ht : t ∈ refs P s := hts
    rw [hps] at ht
    rcases ht with ht | ⟨w, hw, htw⟩
    · exact ⟨ht, fun y hy hty => hn ⟨y, hty, hs'.1.1 y ⟨hy, a2_fr hty⟩⟩⟩
    · exact absurd ⟨w, htw, hs'.1.1 w ⟨hw, a2_fr htw⟩⟩ hn

/-- ✱206·46. \(\vdash : P \in \text{trans} \cap \text{connex} . \text{E}! \text{max}_{P}ʻ\alpha . \supset . \overrightarrow{\text{seq}} _{P}ʻ\alpha = \overrightarrow{\text{seq}} _{P}ʻ\overrightarrow{\text{max}}_{P}ʻ\alpha\) -/
theorem pm206_46 : P ∈ transR ∩ connex ∧ EDesc (maxP P) A →
    refs (seqP P) A = refs (seqP P) (refs (maxP P) A) := by
  rintro ⟨⟨ht, hc⟩, hm⟩
  obtain ⟨m, hm1⟩ := a2_EDesc_exists hm
  have hm' := maxP_iff.1 hm1
  apply a2_seq_congr_pi
  apply a2_pi_ext
  intro z
  constructor
  · rintro h y ⟨hy, -⟩
    exact h y (maxP_iff.1 hy).1
  · intro h y hy
    have hmz : P m z := h m ⟨hm1, hm'.1.2⟩
    rcases mem_connex.1 hc y m ⟨hy.2, hm'.1.2⟩ with (h1 | h1) | h1
    · exact mem_transR.1 ht y m z ⟨h1, hmz⟩
    · rw [h1]
      exact hmz
    · exact absurd h1 (hm'.2 y hy.1)

/-- ✱206·47. \(\vdash : P \in \text{trans} . \text{E}! \text{seq}_{P}ʻ\alpha . \supset . \text{seq}_{P}ʻ\alpha = \text{max}_{P}ʻ(\alpha \cup \overrightarrow{\text{seq}} _{P}ʻ\alpha )\) -/
theorem pm206_47 : P ∈ transR ∧ EDesc (seqP P) A →
    Desc (seqP P) A (fun s => Desc (maxP P) (A ∪ refs (seqP P) A) (fun m => s = m)) := by
  rintro ⟨ht, hs⟩
  obtain ⟨s, hs1⟩ := a2_EDesc_exists hs
  have hu : ∀ b, seqP P b A → b = s := fun b hb => a2_EDesc_uniq hs hb hs1
  have hs' := seqP_iff.1 hs1
  have hmax : maxP P s (A ∪ refs (seqP P) A) := by
    rw [maxP_iff]
    refine ⟨⟨Or.inr hs1, hs'.1.2⟩, ?_⟩
    rintro y (hy | hy) hsy
    · exact pm206_133 hs1 (mem_transR.1 ht s y s ⟨hsy, hs'.1.1 y ⟨hy, a2_fr hsy⟩⟩)
    · have e : y = s := hu y hy
      rw [e] at hsy
      exact pm206_133 hs1 hsy
  refine a2_desc_intro hs1 hu (a2_desc_intro hmax (fun b hb => ?_) rfl)
  rw [maxP_iff] at hb
  rcases hb.1.1 with hbA | hbs
  · exact absurd (hs'.1.1 b ⟨hbA, hb.1.2⟩) (hb.2 s (Or.inr hs1))
  · exact hu b hbs

/-- ✱206·48. \(\vdash : P \in \text{trans} \cap \text{connex} . \text{E}! \text{seq}_{P}ʻ\alpha . \supset . \overrightarrow{\text{seq}} _{P}ʻ\overrightarrow{\text{seq}} _{P}ʻ\alpha = \overrightarrow{\text{seq}} _{P}ʻ(\alpha \cup \overrightarrow{\text{seq}} _{P}ʻ\alpha )\) -/
theorem pm206_48 : P ∈ transR ∩ connex ∧ EDesc (seqP P) A →
    refs (seqP P) (refs (seqP P) A) = refs (seqP P) (A ∪ refs (seqP P) A) := by
  rintro ⟨⟨ht, -⟩, hs⟩
  obtain ⟨s, hs1⟩ := a2_EDesc_exists hs
  have hu : ∀ b, seqP P b A → b = s := fun b hb => a2_EDesc_uniq hs hb hs1
  have hs' := seqP_iff.1 hs1
  apply a2_seq_congr_pi
  apply a2_pi_ext
  intro z
  constructor
  · rintro h y ⟨hyA | hys, hyf⟩
    · exact mem_transR.1 ht y s z ⟨hs'.1.1 y ⟨hyA, hyf⟩, h s ⟨hs1, hs'.1.2⟩⟩
    · exact h y ⟨hys, hyf⟩
  · intro h y hy
    exact h y ⟨Or.inr hy.1, hy.2⟩

/-- ✱206·5. \[\begin{align}\vdash : P \in \text{trans} \cap \text{connex} . \text{E}! \text{max}_{P}ʻ\alpha . \text{E}! &\text{seq}_{P}ʻ\alpha . \supset .\\ &\text{max}_Pʻ\alpha (P \dot{-} P^{2}) \text{seq}_{P}ʻ\alpha\end{align}\] -/
theorem pm206_5 : (P ∈ transR ∩ connex ∧ EDesc (maxP P) A) ∧ EDesc (seqP P) A →
    Desc (maxP P) A (fun m => Desc (seqP P) A (fun s => (P ∸ rsq P) m s)) := by
  rintro ⟨⟨⟨ht, hc⟩, hm⟩, hs⟩
  obtain ⟨m, hm1⟩ := a2_EDesc_exists hm
  obtain ⟨s, hs1⟩ := a2_EDesc_exists hs
  refine a2_desc_intro hm1 (fun b hb => a2_EDesc_uniq hm hb hm1)
    (a2_desc_intro hs1 (fun b hb => a2_EDesc_uniq hs hb hs1) ?_)
  have hm' := maxP_iff.1 hm1
  have hs' := seqP_iff.1 hs1
  have hps : refs P s = (A ∩ fld P) ∪ P ʻʻ A :=
    (a2_desc_iff.1 (pm206_22 ⟨⟨ht, hc⟩, hs⟩).1).2 s hs1
  show P m s ∧ ¬rsq P m s
  refine ⟨hs'.1.1 m hm'.1, ?_⟩
  rintro ⟨z, hmz, hzs⟩
  have hz : z ∈ refs P s := hzs
  rw [hps] at hz
  rcases hz with hz | ⟨w, hw, hzw⟩
  · exact hm'.2 z hz.1 hmz
  · exact hm'.2 w hw (mem_transR.1 ht m z w ⟨hmz, hzw⟩)

/-- ✱206·51. \(\vdash : \exists ! \overrightarrow{\text{max}}_{P}ʻ\overrightarrow{P}ʻx . \supset . x \text{seq}_{P} \overrightarrow{P}ʻx\) -/
theorem pm206_51 : (refs (maxP P) (refs P x)).Nonempty → seqP P x (refs P x) := by
  rintro ⟨m, hm⟩
  have hm' := maxP_iff.1 hm
  have hmx : P m x := hm'.1.1
  rw [seqP_iff]
  exact ⟨⟨fun y hy => hy.1, a2_fr hmx⟩,
    fun z hz hzx => hm'.2 z hzx (hz m ⟨hmx, a2_fl hmx⟩)⟩

/-- ✱206·52. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .\text{E}!\text{max}_{P}ʻ&Pʻʻ\alpha .\supset .\\ &\text{E}!\text{seq}_{P}ʻPʻʻ\alpha .\text{seq}_{P}ʻPʻʻ\alpha =\text{max}_{P}ʻ\alpha\end{align}\] -/
theorem pm206_52 : P ∈ transR ∩ connex ∧ EDesc (maxP P) (P ʻʻ A) →
    EDesc (seqP P) (P ʻʻ A) ∧
      Desc (seqP P) (P ʻʻ A) (fun s => Desc (maxP P) A (fun m => s = m)) := by
  rintro ⟨⟨ht, hc⟩, hm⟩
  have tr := mem_transR.1 ht
  obtain ⟨m', hm1⟩ := a2_EDesc_exists hm
  have hm' := maxP_iff.1 hm1
  obtain ⟨a, ha, hm'a⟩ := hm'.1.1
  have hamax : maxP P a A :=
    maxP_iff.2 ⟨⟨ha, a2_fr hm'a⟩, fun y hy hay => hm'.2 a ⟨y, hy, hay⟩ hm'a⟩
  have haseq : seqP P a (P ʻʻ A) := by
    rw [seqP_iff]
    refine ⟨⟨?_, a2_fr hm'a⟩, ?_⟩
    · rintro w ⟨⟨b, hb, hwb⟩, -⟩
      rcases mem_connex.1 hc b a ⟨a2_fr hwb, a2_fr hm'a⟩ with (h | h) | h
      · exact tr w b a ⟨hwb, h⟩
      · rw [← h]
        exact hwb
      · exact absurd h ((maxP_iff.1 hamax).2 b hb)
    · intro z hz hza
      exact hm'.2 z ⟨a, ha, hza⟩ (hz m' hm'.1)
  have hu : ∀ b, seqP P b (P ʻʻ A) → b = a := fun b hb => a2_seq_uniq hc hb haseq
  exact ⟨a2_EDesc_of haseq hu,
    a2_desc_intro haseq hu (a2_desc_intro hamax (fun b hb => a2_max_uniq hc hb hamax) rfl)⟩

/-- ✱206·53. \(\vdash :P\in \text{Ser}.\supset .\overrightarrow{\text{seq}} _{P}ʻpʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)=\overrightarrow{\text{min}}_{P}ʻ\alpha\) -/
theorem pm206_53 : P ∈ Ser →
    refs (seqP P) (prodCls (Rfwd P ʻʻ (A ∩ fld P))) = refs (minP P) A := by
  intro hS
  have irr := mem_rl_J.1 hS.1.1
  have tr := mem_transR.1 hS.1.2
  have yπ : ∀ y, y ∈ A ∩ fld P → ∀ w, w ∈ prodCls (Rfwd P ʻʻ (A ∩ fld P)) ∩ fld P → P w y :=
    fun y hy w hw => mem_prodCls_Rfwd.1 hw.1 y hy
  ext x
  show seqP P x (prodCls (Rfwd P ʻʻ (A ∩ fld P))) ↔ minP P x A
  rw [seqP_iff, minP_iff]
  constructor
  · rintro ⟨⟨h1, hx⟩, h2⟩
    have hxA : x ∈ A := by
      by_contra hxA
      have hxβ : x ∈ prodCls (Rfwd P ʻʻ (A ∩ fld P)) := by
        rw [mem_prodCls_Rfwd]
        intro y hy
        rcases mem_connex.1 hS.2 x y ⟨hx, hy.2⟩ with (h | h) | h
        · exact h
        · exact absurd (by rw [h]; exact hy.1) hxA
        · exact absurd h (h2 y (yπ y hy))
      exact irr x (h1 x ⟨hxβ, hx⟩)
    exact ⟨⟨hxA, hx⟩, fun y hy hyx => h2 y (yπ y ⟨hy, a2_fl hyx⟩) hyx⟩
  · rintro ⟨⟨hxA, hx⟩, hmin⟩
    refine ⟨⟨fun w hw => yπ x ⟨hxA, hx⟩ w hw, hx⟩, fun z hz hzx => ?_⟩
    have hzβ : z ∈ prodCls (Rfwd P ʻʻ (A ∩ fld P)) := by
      rw [mem_prodCls_Rfwd]
      intro y hy
      rcases mem_connex.1 hS.2 z y ⟨a2_fl hzx, hy.2⟩ with (h | h) | h
      · exact h
      · exact absurd (by rw [← h]; exact hzx) (hmin y hy.1)
      · exact absurd (tr y z x ⟨h, hzx⟩) (hmin y hy.1)
    exact irr z (hz z ⟨hzβ, a2_fl hzx⟩)

/-- ✱206·531. \[\begin{align}\vdash :P&\in \text{Ser}.\supset .\\ &CʻP\cap \hat{x} \{pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)=\overrightarrow{P}ʻx\}=\overrightarrow{\text{seq}} _{P}ʻpʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)=\overrightarrow{\text{min}}_{P}ʻ\alpha \end{align}\] -/
theorem pm206_531 : P ∈ Ser →
    fld P ∩ {x | prodCls (Rfwd P ʻʻ (A ∩ fld P)) = refs P x} =
        refs (seqP P) (prodCls (Rfwd P ʻʻ (A ∩ fld P))) ∧
      refs (seqP P) (prodCls (Rfwd P ʻʻ (A ∩ fld P))) = refs (minP P) A := by
  intro hS
  have irr := mem_rl_J.1 hS.1.1
  have tr := mem_transR.1 hS.1.2
  refine ⟨?_, pm206_53 hS⟩
  rw [pm206_53 hS]
  ext x
  show x ∈ fld P ∧ prodCls (Rfwd P ʻʻ (A ∩ fld P)) = refs P x ↔ minP P x A
  rw [minP_iff]
  constructor
  · rintro ⟨hx, he⟩
    have hxβ : x ∉ prodCls (Rfwd P ʻʻ (A ∩ fld P)) := by
      intro h
      rw [he] at h
      exact irr x h
    rw [mem_prodCls_Rfwd] at hxβ
    push Not at hxβ
    obtain ⟨y, hy, hn⟩ := hxβ
    have hxA : x ∈ A := by
      rcases mem_connex.1 hS.2 x y ⟨hx, hy.2⟩ with (h | h) | h
      · exact absurd h hn
      · rw [h]
        exact hy.1
      · have hyb : y ∈ refs P x := h
        rw [← he, mem_prodCls_Rfwd] at hyb
        exact absurd (hyb y hy) (irr y)
    refine ⟨⟨hxA, hx⟩, fun z hz hzx => ?_⟩
    have hzb : z ∈ refs P x := hzx
    rw [← he, mem_prodCls_Rfwd] at hzb
    exact irr z (hzb z ⟨hz, a2_fl hzx⟩)
  · rintro ⟨⟨hxA, hx⟩, hmin⟩
    refine ⟨hx, Set.ext fun w => ⟨fun hw => mem_prodCls_Rfwd.1 hw x ⟨hxA, hx⟩, fun hwx => ?_⟩⟩
    have hwx' : P w x := hwx
    rw [mem_prodCls_Rfwd]
    intro y hy
    rcases mem_connex.1 hS.2 w y ⟨a2_fl hwx', hy.2⟩ with (h | h) | h
    · exact h
    · exact absurd (by rw [← h]; exact hwx') (hmin y hy.1)
    · exact absurd (tr y w x ⟨h, hwx'⟩) (hmin y hy.1)

/-- ✱206·54. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.\supset :&\text{E}!\text{seq}_{P}ʻpʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP).\equiv .\text{E}!\text{min}_{P}ʻ\alpha :\\ &\text{E}!\text{max}_{P}ʻpʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP).\equiv .\text{E}!\text{prec}_{P}ʻ\alpha\end{align}\] -/
theorem pm206_54 : P ∈ Ser →
    (EDesc (seqP P) (prodCls (Rfwd P ʻʻ (A ∩ fld P))) ↔ EDesc (minP P) A) ∧
      (EDesc (maxP P) (prodCls (Rfwd P ʻʻ (A ∩ fld P))) ↔ EDesc (precP P) A) :=
  fun hS => ⟨a2_refs_congr_EDesc (pm206_53 hS), Iff.rfl⟩

/-- ✱206·55. \[\begin{align}\vdash \colon\ldotp &P\in \text{Ser}.\supset :(\alpha ).\alpha \in \text{ᗡ}ʻ\text{min}_{P}\cup \text{ᗡ}ʻ\text{prec}_{P}.\equiv .\\ &(\alpha ).pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)\in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P} \quad[*206·54·161.*205·32]\end{align}\] -/
theorem pm206_55 : P ∈ Ser →
    ((∀ A : Set α, A ∈ codom (minP P) ∪ codom (precP P)) ↔
      ∀ A : Set α, prodCls (Rfwd P ʻʻ (A ∩ fld P)) ∈ codom (maxP P) ∪ codom (seqP P)) := by
  intro hS
  refine forall_congr' fun A => ?_
  have h1 : A ∈ codom (minP P) ↔ prodCls (Rfwd P ʻʻ (A ∩ fld P)) ∈ codom (seqP P) := by
    show (∃ x, x ∈ refs (minP P) A) ↔ ∃ x, x ∈ refs (seqP P) (prodCls (Rfwd P ʻʻ (A ∩ fld P)))
    rw [pm206_53 hS]
  show A ∈ codom (minP P) ∨ A ∈ codom (precP P) ↔
    prodCls (Rfwd P ʻʻ (A ∩ fld P)) ∈ codom (maxP P) ∨
      prodCls (Rfwd P ʻʻ (A ∩ fld P)) ∈ codom (seqP P)
  rw [h1]
  exact or_comm

/-- ✱206·551. \[\begin{align}\vdash :P\in \text{Ser}.\supset .&\overrightarrow{\text{seq}} _{P}ʻ\alpha = \overrightarrow{\text{seq}} _{P}ʻpʻ\overrightarrow{P}ʻʻpʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP).\\ &\overrightarrow{\text{max}}_{P}ʻ\alpha = \overrightarrow{\text{max}}_{P}ʻpʻ\overrightarrow{P}ʻʻpʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\end{align}\] -/
theorem pm206_551 : P ∈ Ser →
    refs (seqP P) A = refs (seqP P) (prodCls (Rfwd P ʻʻ prodCls (Rbwd P ʻʻ (A ∩ fld P)))) ∧
      refs (maxP P) A = refs (maxP P) (prodCls (Rfwd P ʻʻ prodCls (Rbwd P ʻʻ (A ∩ fld P)))) := by
  intro hS
  have irr := mem_rl_J.1 hS.1.1
  have tr := mem_transR.1 hS.1.2
  have memπ : ∀ z, z ∈ prodCls (Rbwd P ʻʻ (A ∩ fld P)) ↔ ∀ y, y ∈ A ∩ fld P → P y z :=
    fun z => mem_prodCls_Rbwd
  have memδ : ∀ x, x ∈ prodCls (Rfwd P ʻʻ prodCls (Rbwd P ʻʻ (A ∩ fld P))) ↔
      ∀ y, y ∈ prodCls (Rbwd P ʻʻ (A ∩ fld P)) → P x y := fun x => mem_prodCls_Rfwd
  have Aδ : ∀ a, a ∈ A ∩ fld P → a ∈ prodCls (Rfwd P ʻʻ prodCls (Rbwd P ʻʻ (A ∩ fld P))) :=
    fun a ha => (memδ a).2 fun y hy => (memπ y).1 hy a ha
  constructor
  · apply a2_seq_congr_pi
    apply a2_pi_ext
    intro z
    constructor
    · intro h x hx
      exact (memδ x).1 hx.1 z ((memπ z).2 h)
    · intro h a ha
      exact h a ⟨Aδ a ha, ha.2⟩
  · ext x
    show maxP P x A ↔ maxP P x (prodCls (Rfwd P ʻʻ prodCls (Rbwd P ʻʻ (A ∩ fld P))))
    rw [maxP_iff, maxP_iff]
    constructor
    · rintro ⟨⟨hxA, hx⟩, hn⟩
      refine ⟨⟨Aδ x ⟨hxA, hx⟩, hx⟩, fun y hy hxy => ?_⟩
      have hyπ : y ∈ prodCls (Rbwd P ʻʻ (A ∩ fld P)) := by
        rw [memπ]
        intro a ha
        rcases mem_connex.1 hS.2 a x ⟨ha.2, hx⟩ with (h | h) | h
        · exact tr a x y ⟨h, hxy⟩
        · rw [h]
          exact hxy
        · exact absurd h (hn a ha.1)
      exact irr y ((memδ y).1 hy y hyπ)
    · rintro ⟨⟨hxδ, hx⟩, hn⟩
      have hxA : x ∈ A := by
        by_contra hxA
        have hxπ : x ∉ prodCls (Rbwd P ʻʻ (A ∩ fld P)) := fun h => irr x ((memδ x).1 hxδ x h)
        rw [memπ] at hxπ
        push Not at hxπ
        obtain ⟨a, ha, hax⟩ := hxπ
        rcases mem_connex.1 hS.2 x a ⟨hx, ha.2⟩ with (h | h) | h
        · exact hn a (Aδ a ha) h
        · exact hxA (by rw [h]; exact ha.1)
        · exact hax h
      exact ⟨⟨hxA, hx⟩, fun y hy hxy => hn y (Aδ y ⟨hy, a2_fr hxy⟩) hxy⟩

private theorem pm206_56_aux (hS : P ∈ Ser) :
    refs (maxP P) A =
        refs (maxP P) (prodCls (Rfwd P ʻʻ (prodCls (Rbwd P ʻʻ (A ∩ fld P)) ∩ fld P))) ∧
      refs (seqP P) A =
        refs (seqP P) (prodCls (Rfwd P ʻʻ (prodCls (Rbwd P ʻʻ (A ∩ fld P)) ∩ fld P))) := by
  by_cases hne : (A ∩ fld P).Nonempty
  · obtain ⟨a, ha⟩ := hne
    have e : prodCls (Rbwd P ʻʻ (A ∩ fld P)) ∩ fld P = prodCls (Rbwd P ʻʻ (A ∩ fld P)) :=
      Set.inter_eq_left.2 fun z hz => a2_fr (mem_prodCls_Rbwd.1 hz a ha)
    rw [e]
    exact ⟨(pm206_551 hS).2, (pm206_551 hS).1⟩
  · have hA : A ∩ fld P = Λ := a2_eq_Null_iff.2 fun y hy => hne ⟨y, hy⟩
    have hD : prodCls (Rfwd P ʻʻ (prodCls (Rbwd P ʻʻ (A ∩ fld P)) ∩ fld P)) ∩ fld P = Λ := by
      rw [a2_eq_Null_iff]
      rintro x ⟨hx, hxf⟩
      apply mem_rl_J.1 hS.1.1 x
      apply mem_prodCls_Rfwd.1 hx x
      refine ⟨mem_prodCls_Rbwd.2 fun y hy => absurd hy (a2_eq_Null_iff.1 hA y), hxf⟩
    have h0 : ∀ C : Set α, C ∩ fld P = Λ → refs (maxP P) C = Λ := by
      intro C hC
      rw [a2_eq_Null_iff]
      intro x hx
      exact a2_eq_Null_iff.1 hC x (maxP_iff.1 hx).1
    exact ⟨by rw [h0 A hA, h0 _ hD], by rw [pm206_14 hA, pm206_14 hD]⟩

/-- ✱206·56. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.\supset :(\alpha ).pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)\in &\text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}. \equiv .\\ &(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}\end{align}\] -/
theorem pm206_56 : P ∈ Ser →
    ((∀ A : Set α, prodCls (Rfwd P ʻʻ (A ∩ fld P)) ∈ codom (maxP P) ∪ codom (seqP P)) ↔
      ∀ A : Set α, A ∈ codom (maxP P) ∪ codom (seqP P)) := by
  intro hS
  constructor
  · intro h A
    have hB := h (prodCls (Rbwd P ʻʻ (A ∩ fld P)))
    obtain ⟨e1, e2⟩ := pm206_56_aux (A := A) hS
    show (∃ x, x ∈ refs (maxP P) A) ∨ ∃ x, x ∈ refs (seqP P) A
    rw [e1, e2]
    exact hB
  · intro h A
    exact h _

/-- ✱206·57. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.\supset :&(\alpha ).\alpha \in \text{ᗡ}ʻ\text{min}_{P}\cup \text{ᗡ}ʻ\text{prec}_{P}. \equiv .\\ &(\alpha ).\alpha \in \text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P} \quad[*206·55·56]\end{align}\] -/
theorem pm206_57 : P ∈ Ser →
    ((∀ A : Set α, A ∈ codom (minP P) ∪ codom (precP P)) ↔
      ∀ A : Set α, A ∈ codom (maxP P) ∪ codom (seqP P)) :=
  fun hS => (pm206_55 hS).trans (pm206_56 hS)

/-- ✱206·6. \(\vdash :S\in P \overline{\,\text{smor}\,} Q.\supset .pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP) = Sʻʻpʻ\overleftarrow{Q}ʻʻ\breve{S} ʻʻ\alpha\)

**Status.** proved (corrected): false as printed when `α ∩ C'P = Λ` and `C'P` is not
the whole type: then `p'P⃖''(α ∩ C'P) = p'Λ = V` (✱40), while `S''p'Q⃖''S̆''α ⊂ D'S = C'P`
(`pm206_6_printed_false`: `P = Q = S = Λ̇` on `Unit`, `α = Λ`). PM's demonstration uses ✱72·341
(`p'S'''κ = S''p'κ`), which needs `∃!κ`. Proved with the left side intersected with `C'P`,
which leaves it unchanged whenever `∃!α ∩ C'P`, and suffices for ✱206·61. -/
theorem pm206_6 {Q : β → β → Prop} {S : α → β → Prop} : S ∈ smorbar P Q →
    prodCls (Rbwd P ʻʻ (A ∩ fld P)) ∩ fld P = S ʻʻ prodCls (Rbwd Q ʻʻ (S˘ ʻʻ A)) := by
  intro hS
  obtain ⟨⟨_, hmo⟩, hP, hfP, _⟩ := a2_smor_facts hS
  ext x
  constructor
  · rintro ⟨hπ, hx⟩
    obtain ⟨z, hxz⟩ := (hfP x).1 hx
    refine ⟨z, mem_prodCls_Rbwd.2 ?_, hxz⟩
    rintro w ⟨a, ha, haw⟩
    have hPa := mem_prodCls_Rbwd.1 hπ a ⟨ha, (hfP a).2 ⟨w, haw⟩⟩
    obtain ⟨w', z', ⟨haw', hxz'⟩, hq⟩ := (hP a x).1 hPa
    rw [hmo a w' w ⟨haw', haw⟩, hmo x z' z ⟨hxz', hxz⟩] at hq
    exact hq
  · rintro ⟨z, hz, hxz⟩
    refine ⟨mem_prodCls_Rbwd.2 ?_, (hfP x).2 ⟨z, hxz⟩⟩
    rintro a ⟨ha, haf⟩
    obtain ⟨w, haw⟩ := (hfP a).1 haf
    exact (hP a x).2 ⟨w, z, ⟨haw, hxz⟩, mem_prodCls_Rbwd.1 hz w ⟨a, ha, haw⟩⟩

/-- The printed form of ✱206·6 is false: the null relation on `Unit` correlates with itself, and
for `α = Λ` the left side is `V` while the right side is `Λ`. -/
theorem pm206_6_printed_false : ¬∀ (P Q S : Unit → Unit → Prop) (A : Set Unit),
    S ∈ smorbar P Q → prodCls (Rbwd P ʻʻ (A ∩ fld P)) = S ʻʻ prodCls (Rbwd Q ʻʻ (S˘ ʻʻ A)) := by
  intro h
  let N : Unit → Unit → Prop := fun _ _ => False
  have hS : N ∈ smorbar N N := by
    refine ⟨⟨mem_arrow_one_one.2 ⟨fun _ _ _ h => False.elim h.1, fun _ _ _ h => False.elim h.1⟩,
      ?_⟩, ?_⟩
    · ext x
      constructor
      · rintro ⟨_, h | h⟩ <;> exact False.elim h
      · rintro ⟨_, h⟩
        exact False.elim h
    · funext x y
      apply propext
      rw [semi_apply]
      constructor
      · intro h
        exact False.elim h
      · rintro ⟨_, _, ⟨h, _⟩, _⟩
        exact False.elim h
  have e := h N N N ∅ hS
  have hmem : () ∈ prodCls (Rbwd N ʻʻ ((∅ : Set Unit) ∩ fld N)) :=
    mem_prodCls_Rbwd.2 fun y hy => absurd hy.1 (Set.notMem_empty y)
  obtain ⟨_, _, h'⟩ := (Set.ext_iff.1 e ()).1 hmem
  exact h'

/-- ✱206·61. \(\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .\overrightarrow{\text{seq}} _{P}ʻ\alpha =Sʻʻ\overrightarrow{\text{seq}} _{Q}ʻ\breve{S} ʻʻ\alpha\) -/
theorem pm206_61 {Q : β → β → Prop} {S : α → β → Prop} : S ∈ smorbar P Q →
    refs (seqP P) A = S ʻʻ refs (seqP Q) (S˘ ʻʻ A) :=
  fun hS => a2_smor_refs hS (fun _ hx => (seqP_iff.1 hx).1.2) fun _ _ h => a2_smor_seq hS h

/-- ✱206·62. \[\begin{align}&\vdash \colon\ldotp S\in P\,\overline{\,\text{smor}\,}\,Q.\supset :\text{E}!\text{seq}_{P}ʻ\alpha .\equiv .\text{E}!\text{seq}_{Q}ʻ\breve{S} ʻʻ\alpha \\ &[*206·61.*73·22·44.*53·3]\end{align}\] -/
theorem pm206_62 {Q : β → β → Prop} {S : α → β → Prop} : S ∈ smorbar P Q →
    (EDesc (seqP P) A ↔ EDesc (seqP Q) (S˘ ʻʻ A)) :=
  fun hS => a2_smor_EDesc hS (fun _ hx => (seqP_iff.1 hx).1.2) (fun _ hz => (seqP_iff.1 hz).1.2)
    fun _ _ h => a2_smor_seq hS h

/-- ✱206·63. \[\begin{align}&\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\text{E}!\text{seq}_{P}ʻ\alpha .\supset .\text{seq}_{P}ʻ\alpha =Sʻ\text{seq}_{Q}ʻ\breve{S} ʻʻ\alpha \\ &[*206·61·62.*53·31]\end{align}\] -/
theorem pm206_63 {Q : β → β → Prop} {S : α → β → Prop} : S ∈ smorbar P Q ∧ EDesc (seqP P) A →
    Desc (seqP P) A (fun s => Desc2 S (seqP Q) (S˘ ʻʻ A) (fun t => s = t)) :=
  fun ⟨hS, hE⟩ => a2_smor_desc hS (fun _ hx => (seqP_iff.1 hx).1.2)
    (fun _ hz => (seqP_iff.1 hz).1.2) (fun _ _ h => a2_smor_seq hS h) hE

private theorem pm206_7_aux (ht : P ∈ transR) (hy : ¬P y y) (hm : y ∉ refs (maxP P) B) :
    prodCls (Rbwd P ʻʻ (B ∩ fld P)) = prodCls (Rbwd P ʻʻ ((B \ ι y) ∩ fld P)) := by
  apply a2_pi_ext
  intro z
  constructor
  · intro h w hw
    exact h w ⟨hw.1.1, hw.2⟩
  · intro h b hb
    by_cases hby : b = y
    · rw [hby] at hb ⊢
      obtain ⟨x, hxB, hyx⟩ : ∃ x, x ∈ B ∧ P y x := by
        by_contra hn
        push Not at hn
        exact hm (maxP_iff.2 ⟨hb, hn⟩)
      have hxy : x ≠ y := fun e => hy (by rw [e] at hyx; exact hyx)
      exact mem_transR.1 ht y x z ⟨hyx, h x ⟨⟨hxB, hxy⟩, a2_fr hyx⟩⟩
    · exact h b ⟨⟨hb.1, hby⟩, hb.2⟩

/-- ✱206·7. \[\begin{align}\vdash :P\in \text{trans}.\beta \subset CʻP.{\sim}(yPy).y{\sim}\in &\overrightarrow{\text{max}}_{P}ʻ\beta .\supset .\\ &pʻ\overleftarrow{P}ʻʻ\beta =pʻ\overleftarrow{P}ʻʻ(\beta -{℩}ʻy)\end{align}\] -/
theorem pm206_7 : ((P ∈ transR ∧ B ⊆ fld P) ∧ ¬P y y) ∧ y ∉ refs (maxP P) B →
    prodCls (Rbwd P ʻʻ B) = prodCls (Rbwd P ʻʻ (B \ ι y)) := by
  rintro ⟨⟨⟨ht, hB⟩, hy⟩, hm⟩
  have e1 : B ∩ fld P = B := Set.inter_eq_left.2 hB
  have e2 : (B \ ι y) ∩ fld P = B \ ι y := Set.inter_eq_left.2 fun _ hx => hB hx.1
  have h := pm206_7_aux ht hy hm
  rwa [e1, e2] at h

/-- ✱206·71. \(\vdash :P\in \text{trans}.\beta \subset CʻP.{\sim}(yPy).y{\sim}\in \overrightarrow{\text{max}}_{P}ʻ\beta .\supset .\overrightarrow{\text{seq}} _{P}ʻ\beta =\overrightarrow{\text{seq}} _{P}ʻ(\beta -{℩}ʻy)\) -/
theorem pm206_71 : ((P ∈ transR ∧ B ⊆ fld P) ∧ ¬P y y) ∧ y ∉ refs (maxP P) B →
    refs (seqP P) B = refs (seqP P) (B \ ι y) :=
  fun ⟨⟨⟨ht, _⟩, hy⟩, hm⟩ => a2_seq_congr_pi (pm206_7_aux ht hy hm)

/-- ✱206·72. \(\vdash :P\in \text{trans}.{\sim}(yPy).y{\sim}\in \overrightarrow{\text{max}}_{P}ʻ\beta .\supset .\overrightarrow{\text{seq}} _{P}ʻ\beta =\overrightarrow{\text{seq}} _{P}ʻ(\beta -{℩}ʻy)\) -/
theorem pm206_72 : (P ∈ transR ∧ ¬P y y) ∧ y ∉ refs (maxP P) B →
    refs (seqP P) B = refs (seqP P) (B \ ι y) :=
  fun ⟨⟨ht, hy⟩, hm⟩ => a2_seq_congr_pi (pm206_7_aux ht hy hm)

/-- ✱206·73. \(\vdash :\exists !\gamma \cap CʻP.\text{E}!\text{prec}_{P}ʻ\gamma .\text{E}!\text{seq}_{P}ʻ\gamma .\supset .\text{prec}_{P}ʻ\gamma P^{2}\text{seq}_{P}ʻ\gamma\) -/
theorem pm206_73 : ((G ∩ fld P).Nonempty ∧ EDesc (precP P) G) ∧ EDesc (seqP P) G →
    Desc (precP P) G (fun p => Desc (seqP P) G (fun s => rsq P p s)) := by
  rintro ⟨⟨⟨g, hg⟩, hp⟩, hs⟩
  obtain ⟨p, hp1⟩ := a2_EDesc_exists hp
  obtain ⟨s, hs1⟩ := a2_EDesc_exists hs
  refine a2_desc_intro hp1 (fun b hb => a2_EDesc_uniq hp hb hp1)
    (a2_desc_intro hs1 (fun b hb => a2_EDesc_uniq hs hb hs1) ?_)
  exact ⟨g, (precP_iff.1 hp1).1.1 g hg, (seqP_iff.1 hs1).1.1 g hg⟩

/-- ✱206·731. \(\vdash \colon\ldotp \exists !\gamma \cap CʻP:P\in \text{trans}.\lor.P^{2}\,\unicode{x2abd}\, J:\supset .{\sim}(\text{prec}_{P}ʻ\gamma =\text{seq}_{P}ʻ\gamma )\) -/
theorem pm206_731 : (G ∩ fld P).Nonempty ∧ (P ∈ transR ∨ rsq P ⪽ J) →
    ¬Desc (precP P) G (fun p => Desc (seqP P) G (fun s => p = s)) := by
  rintro ⟨-, hor⟩ ⟨p, hpu, s, hsu, hps⟩
  have hp1 : precP P p G := (hpu p).2 rfl
  have hs1 : seqP P s G := (hsu s).2 rfl
  rw [← hps] at hs1
  exact a2_prec_seq_false hor hp1 hs1

/-- ✱206·732. \(\vdash \colon\ldotp P\in \text{trans}.\lor.P^{2}\,\unicode{x2abd}\, J:\supset .{\sim}(\text{prec}_{P}ʻ\gamma =\text{seq}_{P}ʻ\gamma )\) -/
theorem pm206_732 : (P ∈ transR ∨ rsq P ⪽ J) →
    ¬Desc (precP P) G (fun p => Desc (seqP P) G (fun s => p = s)) := by
  rintro hor ⟨p, hpu, s, hsu, hps⟩
  have hp1 : precP P p G := (hpu p).2 rfl
  have hs1 : seqP P s G := (hsu s).2 rfl
  rw [← hps] at hs1
  exact a2_prec_seq_false hor hp1 hs1

/-!
## [✱207] Limits

*(Vol. 2, p. 594)*

> *Summary of* *207.
>
> A term \(x\) is said to be the "upper limit" of \(\alpha\) in \(P\) if \(\alpha\) has no maximum and \(x\) is the sequent of \(\alpha\). In this case, \(x\) immediately follows the class \(\alpha\), though there is no one member of \(\alpha\) which \(x\) immediately follows. Sequents which are limits have special importance, and it is convenient to have a special notation for them. We write "\(\text{lt}_Pʻ\alpha\)" for the upper limit of \(\alpha\); or, if it is more convenient, "\(\text{lt}(P)ʻ\alpha\)". (This is more convenient when \(P\) is replaced by an expression consisting of several letters, or by a letter with a suffix.) The *lower* limit of \(\alpha\) will be the immediate predecessor of \(\alpha\) when \(\alpha\) has no minimum; this we denote by \(\text{tl}_Pʻ\alpha\).
>
> The following propositions on limits for the most part follow immediately from the propositions of *206 on sequents.
>
> …

**Lean reading.** `x lt_P α` is `ltP P x A` (`= seqP P ↾ (codom (maxP P))ᶜ`, ✱207·01),
`x limax_P α` is `limaxP P x A`; `lt⃗_P'α`, `limax⃗_P'α` are `refs (ltP P) A`,
`refs (limaxP P) A`, and the descriptions `lt_P'α`, `limax_P'α`, `max_P'α`, `min_P'α`,
`limin_P'α` are `Desc` (`E!` is `EDesc`); `ᗡ'lt_P` is `codom (ltP P)`, `D'lt_P` is
`dom (ltP P)`, `lt_P''κ` is `ltP P ʻʻ K`, `S̆'''κ` is `S˘ ʻʻʻ K`, `s'κ` is `sumCls K`,
`P_*''α` is `anc P ʻʻ A` and `P⃗_*'a` is `refs (anc P) a`; `α ∩ C'P ∼∈ 1` is
`A ∩ fld P ∉ one`; `ᗡ'(P −̇ P²)` is `codom (P ∸ rsq P)`; `limax_P, limin_P ∈ 1 → Cls` is the
conjunction; `Rl'J` is `rl J`. The notation of ✱206 is kept. The facts about `tl_P`, `limin_P`
come from `tl_P = lt(P̆)` and `limin_P = limax(P̆)` (Defs/Part5). Two e-text misprints are read as
PM intends: ✱207·35 prints `R1'J` for `Rl'J`, and ✱207·482 prints `α` for the term `a` in
`a = limax_P'α` and `α ⊂ P⃗_*'a` (as its demonstration shows).

**Status.** proved (all propositions; ✱207·35 and ✱207·482 proved (reading), see their docstrings).
-/

/-- ✱207·01 (Df). \(\text{lt}_P=\text{lt}(P)=\text{seq}_{P}\upharpoonright (-\text{ᗡ}ʻ\text{max}_{P}) \quad\text{Df}\) -/
theorem pm207_01 : ltP P = seqP P ↾ (codom (maxP P))ᶜ := rfl

/-- ✱207·02 (Df). \(\text{tl}_P=tl(P)=\text{prec}_{P}\upharpoonright (-\text{ᗡ}ʻ\text{min}_{P}) \quad\text{Df}\) -/
theorem pm207_02 : tlP P = precP P ↾ (codom (minP P))ᶜ := rfl

/-- ✱207·03 (Df). \(\text{limax}_P=\text{max}_{P}\unicode{x228d} \text{lt}_P \quad\text{Df}\) -/
theorem pm207_03 : limaxP P = maxP P ⊍ ltP P := rfl

/-- ✱207·04 (Df). \(\text{limin}_P=\text{min}_{P}\unicode{x228d} \text{tl}_P \quad\text{Df}\) -/
theorem pm207_04 : liminP P = minP P ⊍ tlP P := rfl

/-- ✱207·1. \(\vdash :x\,\text{lt}_P\,\alpha .\equiv .x\text{seq}_{P}\alpha .{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha \quad[(*207·01)]\) -/
theorem pm207_1 : ltP P x A ↔ seqP P x A ∧ ¬(refs (maxP P) A).Nonempty := Iff.rfl

/-- ✱207·101. \(\vdash .\text{tl}_P=\text{lt}(\breve{P} ) \quad[*205·102.*206·101.(*207·02)]\) -/
theorem pm207_101 : tlP P = ltP P˘ := tlP_eq_ltP_cnv P

/-- ✱207·11. \(\vdash :\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .\supset .\overrightarrow{\text{lt}} _{P}ʻ\alpha =\Lambda \quad[*207·1]\) -/
theorem pm207_11 : (refs (maxP P) A).Nonempty → refs (ltP P) A = Λ := by
  intro h
  rw [a2_eq_Null_iff]
  intro x hx
  exact hx.2 h

/-- ✱207·12. \(\vdash :\overrightarrow{\text{max}}_{P}ʻ\alpha =\Lambda .\supset .\overrightarrow{\text{lt}} _{P}ʻ\alpha =\overrightarrow{\text{seq}} _{P}ʻ\alpha \quad[*207·1]\) -/
theorem pm207_12 : refs (maxP P) A = Λ → refs (ltP P) A = refs (seqP P) A := by
  intro h
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun ⟨m, hm⟩ => a2_eq_Null_iff.1 h m hm⟩⟩

private theorem a2_lt_eq_seq (h : ¬∃ m, maxP P m A) : refs (ltP P) A = refs (seqP P) A :=
  pm207_12 (a2_eq_Null_iff.2 fun m hm => h ⟨m, hm⟩)

private theorem a2_lt_congr (h1 : refs (seqP P) A = refs (seqP P) B)
    (h2 : (∃ m, maxP P m A) ↔ ∃ m, maxP P m B) : refs (ltP P) A = refs (ltP P) B := by
  ext x
  show seqP P x A ∧ ¬(∃ m, maxP P m A) ↔ seqP P x B ∧ ¬∃ m, maxP P m B
  rw [show seqP P x A ↔ seqP P x B from Set.ext_iff.1 h1 x, h2]

private theorem a2_lt_of_empty (h : A ∩ fld P = Λ) : refs (ltP P) A = refs Beg P := by
  rw [← pm206_14 h]
  exact a2_lt_eq_seq fun ⟨m, hm⟩ => a2_eq_Null_iff.1 h m (maxP_iff.1 hm).1

/-- ✱207·121. \(\vdash :\alpha \cap CʻP\subset Pʻʻ\alpha .\supset .\overrightarrow{\text{lt}} _{P}ʻ\alpha =\overrightarrow{\text{seq}} _{P}ʻ\alpha \quad[*207·12.*205·123]\) -/
theorem pm207_121 : A ∩ fld P ⊆ P ʻʻ A → refs (ltP P) A = refs (seqP P) A :=
  fun h => a2_lt_eq_seq (a2_noMax_iff_sub.2 h)

/-- ✱207·13. \(\vdash :\exists !\overrightarrow{\text{lt}} _{P}ʻ\alpha .\equiv .{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .\exists !\overrightarrow{\text{seq}} _{P}ʻ\alpha \quad[*207·1]\) -/
theorem pm207_13 :
    (refs (ltP P) A).Nonempty ↔ ¬(refs (maxP P) A).Nonempty ∧ (refs (seqP P) A).Nonempty := by
  constructor
  · rintro ⟨x, hx1, hx2⟩
    exact ⟨hx2, x, hx1⟩
  · rintro ⟨h1, x, hx⟩
    exact ⟨x, hx, h1⟩

/-- ✱207·14. \[\begin{align}&\vdash \colon\ldotp \exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .\lor.\exists !\overrightarrow{\text{seq}} _{P}ʻ\alpha :\equiv :\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .\lor.\exists !\overrightarrow{\text{lt}} _{P}ʻ\alpha \\ &[*207·13.*5·63]\end{align}\] -/
theorem pm207_14 : (refs (maxP P) A).Nonempty ∨ (refs (seqP P) A).Nonempty ↔
    (refs (maxP P) A).Nonempty ∨ (refs (ltP P) A).Nonempty := by
  rw [pm207_13]
  tauto

/-- ✱207·15. \[\begin{align}&\vdash :x\,\text{lt}_P\,\alpha .\equiv .x\in CʻP.\alpha \cap CʻP\subset Pʻʻ\alpha \cap \overrightarrow{P}ʻx.\overrightarrow{P}ʻx\subset -pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\\ &[*207·1.*205·123.*206·134]\end{align}\] -/
theorem pm207_15 : ltP P x A ↔ (x ∈ fld P ∧ A ∩ fld P ⊆ P ʻʻ A ∩ refs P x) ∧
    refs P x ⊆ (prodCls (Rbwd P ʻʻ (A ∩ fld P)))ᶜ := by
  have h134 : seqP P x A ↔ x ∈ fld P ∧
      (A ∩ fld P ⊆ refs P x ∧ refs P x ⊆ (prodCls (Rbwd P ʻʻ (A ∩ fld P)))ᶜ) :=
    Set.ext_iff.1 pm206_134 x
  rw [ltP_iff, h134, a2_noMax_iff_sub, Set.subset_inter_iff]
  tauto

/-- ✱207·16. \(\vdash .\overrightarrow{\text{lt}} _{P}ʻ\alpha =\overrightarrow{\text{lt}} _{P}ʻ(\alpha \cap CʻP) \quad[*207·15.*37·265]\) -/
theorem pm207_16 : refs (ltP P) A = refs (ltP P) (A ∩ fld P) :=
  a2_lt_congr pm206_131 (exists_congr fun _ => a2_maxP_inter.symm)

/-- ✱207·17. \(\vdash .\overrightarrow{\text{lt}} _{P}ʻ\Lambda =\overrightarrow{B}ʻP \quad[*207·12.*205·161.*206·14]\) -/
theorem pm207_17 : refs (ltP P) Λ = refs Beg P :=
  a2_lt_of_empty (a2_eq_Null_iff.2 fun x hx => a2_eq_Null_iff.1 rfl x hx.1)

/-- ✱207·18. \(\vdash :\text{ᗡ}ʻP\subset \text{D}ʻ\text{lt}_P.\equiv .CʻP=\text{D}ʻ\text{lt}_P\) -/
theorem pm207_18 : codom P ⊆ dom (ltP P) ↔ fld P = dom (ltP P) := by
  have hdom : dom (ltP P) ⊆ fld P := fun x ⟨_, hB⟩ => (seqP_iff.1 hB.1).1.2
  constructor
  · intro h
    refine Set.Subset.antisymm (fun x hx => ?_) hdom
    by_cases hc : x ∈ codom P
    · exact h hc
    · refine ⟨Λ, ?_⟩
      have hb : x ∈ refs Beg P := by
        obtain ⟨y, hy | hy⟩ := hx
        · exact ⟨⟨y, hy⟩, hc⟩
        · exact absurd ⟨y, hy⟩ hc
      rw [← pm207_17] at hb
      exact hb
  · intro h x hx
    rw [← h]
    obtain ⟨y, hy⟩ := hx
    exact a2_fr hy

/-- ✱207·2. \[\begin{align}&\vdash :P\in \text{connex} .x\,\text{lt}_P\,\alpha .\supset .\alpha \cap CʻP\subset \overrightarrow{P}ʻx.\overrightarrow{P}ʻx\subset Pʻʻ\alpha \\ &[*207·15.*202·503]\end{align}\] -/
theorem pm207_2 : P ∈ connex ∧ ltP P x A → A ∩ fld P ⊆ refs P x ∧ refs P x ⊆ P ʻʻ A := by
  rintro ⟨hc, hs, hn⟩
  have hsub := a2_noMax_iff_sub.1 hn
  refine ⟨fun y hy => (seqP_iff.1 hs).1.1 y hy, fun z hz => ?_⟩
  rcases a2_seq_pred_sub hc hs hz with h | h
  · exact hsub h
  · exact h

/-- ✱207·21. \(\vdash :P^{2}\,\unicode{x2abd}\, J.x\in CʻP.\alpha \cap CʻP\subset \overrightarrow{P}ʻx.\overrightarrow{P}ʻx\subset Pʻʻ\alpha .\supset .x\,\text{lt}_P\,\alpha \) -/
theorem pm207_21 : ((rsq P ⪽ J ∧ x ∈ fld P) ∧ A ∩ fld P ⊆ refs P x) ∧ refs P x ⊆ P ʻʻ A →
    ltP P x A := by
  rintro ⟨⟨⟨hJ, hx⟩, h1⟩, h2⟩
  refine ⟨?_, ?_⟩
  · rw [seqP_iff]
    refine ⟨⟨fun y hy => h1 hy, hx⟩, fun z hz hzx => ?_⟩
    obtain ⟨w, hw, hzw⟩ := h2 hzx
    exact a2_asymm hJ hzw (hz w ⟨hw, a2_fr hzw⟩)
  · rintro ⟨m, hm⟩
    have hm' := maxP_iff.1 hm
    obtain ⟨w, hw, hmw⟩ := h2 (h1 hm'.1)
    exact hm'.2 w hw hmw

/-- ✱207·22. \[\begin{align}&\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.\supset .\overrightarrow{\text{lt}} _{P}ʻ\alpha =CʻP\cap \hat{x} (\alpha \cap CʻP\subset \overrightarrow{P}ʻx.\overrightarrow{P}ʻx\subset Pʻʻ\alpha )\\ &[*207·2·21]\end{align}\] -/
theorem pm207_22 : P ∈ connex ∧ rsq P ⪽ J →
    refs (ltP P) A = fld P ∩ {x | A ∩ fld P ⊆ refs P x ∧ refs P x ⊆ P ʻʻ A} := by
  rintro ⟨hc, hJ⟩
  ext x
  constructor
  · intro hx
    exact ⟨(seqP_iff.1 hx.1).1.2, pm207_2 ⟨hc, hx⟩⟩
  · rintro ⟨hx, h1, h2⟩
    exact pm207_21 ⟨⟨⟨hJ, hx⟩, h1⟩, h2⟩

/-- ✱207·23. \(\vdash :P\in \text{Ser}.\supset .\overrightarrow{\text{lt}} _{P}ʻ\alpha =CʻP\cap \hat{x} (\overrightarrow{P}ʻx=Pʻʻ\alpha .\alpha \cap CʻP\subset Pʻʻ\alpha )\) -/
theorem pm207_23 : P ∈ Ser →
    refs (ltP P) A = fld P ∩ {x | refs P x = P ʻʻ A ∧ A ∩ fld P ⊆ P ʻʻ A} := by
  intro hS
  rw [pm207_22 ⟨hS.2, a2_rsqJ_of_Ser hS⟩]
  ext x
  show x ∈ fld P ∧ (A ∩ fld P ⊆ refs P x ∧ refs P x ⊆ P ʻʻ A) ↔
    x ∈ fld P ∧ (refs P x = P ʻʻ A ∧ A ∩ fld P ⊆ P ʻʻ A)
  constructor
  · rintro ⟨hx, h1, h2⟩
    refine ⟨hx, Set.Subset.antisymm h2 ?_, fun y hy => h2 (h1 hy)⟩
    rintro z ⟨w, hw, hzw⟩
    exact mem_transR.1 hS.1.2 z w x ⟨hzw, h1 ⟨hw, a2_fr hzw⟩⟩
  · rintro ⟨hx, he, h3⟩
    exact ⟨hx, fun y hy => by rw [he]; exact h3 hy, he.subset⟩

/-- ✱207·231. \(\vdash :P\in \text{Ser}.\exists !\overrightarrow{\text{lt}} _{P}ʻ\alpha .\supset .\overrightarrow{\text{lt}} _{P}ʻ\alpha =CʻP\cap \hat{x} (\overrightarrow{P}ʻx=Pʻʻ\alpha ) \quad[*207·23]\) -/
theorem pm207_231 : P ∈ Ser ∧ (refs (ltP P) A).Nonempty →
    refs (ltP P) A = fld P ∩ {x | refs P x = P ʻʻ A} := by
  rintro ⟨hS, ⟨l, hl⟩⟩
  have hsub : A ∩ fld P ⊆ P ʻʻ A := a2_noMax_iff_sub.1 hl.2
  rw [pm207_23 hS]
  ext x
  exact and_congr Iff.rfl (and_iff_left hsub)

/-- ✱207·232. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.\supset :x=\text{lt}_Pʻ\alpha .\equiv .x\in CʻP-\alpha .\overrightarrow{P}ʻx=Pʻʻ\alpha \\ &[*206·28.*207·1]\end{align}\] -/
theorem pm207_232 : P ∈ Ser →
    (Desc (ltP P) A (fun l => x = l) ↔ x ∈ fld P \ A ∧ refs P x = P ʻʻ A) := by
  intro hS
  rw [pm206_28 hS]
  by_cases hm : EDesc (maxP P) A
  · have e : refs (ltP P) A = Λ := pm207_11 (a2_EDesc_exists hm)
    constructor
    · intro h
      obtain ⟨l, hl⟩ := a2_EDesc_exists (a2_desc_iff.1 h).1
      exact absurd hl (a2_eq_Null_iff.1 e l)
    · rintro ⟨-, h⟩
      exact absurd hm h
  · rw [a2_refs_congr_desc (a2_lt_eq_seq (a2_noMax_of hS.2 hm))]
    exact ⟨fun h => ⟨h, hm⟩, fun h => h.1⟩

/-- ✱207·24. \(\vdash :P\in \text{connex} .\supset .\overrightarrow{\text{lt}} _{P}ʻ\alpha \in 0\cup 1.\text{lt}_P\in 1\rightarrow \text{Cls}\) -/
theorem pm207_24 : P ∈ connex → refs (ltP P) A ∈ zero ∪ one ∧ ltP P ∈ arrow one Cls :=
  fun hc => ⟨a2_mem_zero_union_one.2 fun _ _ ha hb => a2_seq_uniq hc ha.1 hb.1,
    mem_arrow_one_Cls.2 fun _ _ _ h => a2_seq_uniq hc h.1.1 h.2.1⟩

/-- ✱207·25. \(\vdash :P\in \text{trans}.\beta \subset Pʻʻ\alpha .\supset .\overrightarrow{\text{lt}} _{P}ʻ(\alpha \cup \beta )=\overrightarrow{\text{lt}} _{P}ʻ\alpha\) -/
theorem pm207_25 : P ∈ transR ∧ B ⊆ P ʻʻ A → refs (ltP P) (A ∪ B) = refs (ltP P) A := by
  rintro ⟨ht, hB⟩
  refine a2_lt_congr (pm206_24 ⟨ht, hB⟩) (exists_congr fun m => ?_)
  rw [maxP_iff, maxP_iff]
  constructor
  · rintro ⟨⟨hm | hm, hmf⟩, hn⟩
    · exact ⟨⟨hm, hmf⟩, fun y hy => hn y (Or.inl hy)⟩
    · obtain ⟨w, hw, hmw⟩ := hB hm
      exact absurd hmw (hn w (Or.inl hw))
  · rintro ⟨⟨hm, hmf⟩, hn⟩
    refine ⟨⟨Or.inl hm, hmf⟩, ?_⟩
    rintro y (hy | hy) hmy
    · exact hn y hy hmy
    · obtain ⟨w, hw, hyw⟩ := hB hy
      exact hn w hw (mem_transR.1 ht m y w ⟨hmy, hyw⟩)

/-- ✱207·251. \(\vdash :P\in \text{trans}.y\in Pʻʻ(\beta -{℩}ʻy).\supset .\overrightarrow{\text{lt}} _{P}ʻ\beta =\overrightarrow{\text{lt}} _{P}ʻ(\beta -{℩}ʻy)\) -/
theorem pm207_251 : P ∈ transR ∧ y ∈ P ʻʻ (B \ ι y) →
    refs (ltP P) B = refs (ltP P) (B \ ι y) := by
  rintro ⟨ht, hy⟩
  have h := pm207_25 (A := B \ ι y) (B := B ∩ ι y) ⟨ht, ?_⟩
  · rwa [Set.sdiff_union_inter] at h
  · rintro z ⟨-, hz⟩
    have e : z = y := hz
    rw [e]
    exact hy

private theorem a2_max_remove (ht : P ∈ transR) (hy : ¬P y y) (hm : y ∉ refs (maxP P) B)
    (m : α) : maxP P m B ↔ maxP P m (B \ ι y) := by
  rw [maxP_iff, maxP_iff]
  constructor
  · rintro ⟨⟨hmB, hmf⟩, hn⟩
    have hmy : m ≠ y := fun e => hm (by rw [← e]; exact maxP_iff.2 ⟨⟨hmB, hmf⟩, hn⟩)
    exact ⟨⟨⟨hmB, hmy⟩, hmf⟩, fun z hz => hn z hz.1⟩
  · rintro ⟨⟨⟨hmB, -⟩, hmf⟩, hn⟩
    refine ⟨⟨hmB, hmf⟩, fun z hz hmz => ?_⟩
    by_cases hzy : z = y
    · rw [hzy] at hmz hz
      obtain ⟨v, hvB, hyv⟩ : ∃ v, v ∈ B ∧ P y v := by
        by_contra hn'
        push Not at hn'
        exact hm (maxP_iff.2 ⟨⟨hz, a2_fr hmz⟩, hn'⟩)
      have hvy : v ≠ y := fun e => hy (by rw [e] at hyv; exact hyv)
      exact hn v ⟨hvB, hvy⟩ (mem_transR.1 ht m y v ⟨hmz, hyv⟩)
    · exact hn z ⟨hz, hzy⟩ hmz

private theorem a2_lt_remove (ht : P ∈ transR) (hy : ¬P y y) (hm : y ∉ refs (maxP P) B) :
    refs (ltP P) B = refs (ltP P) (B \ ι y) :=
  a2_lt_congr (pm206_72 ⟨⟨ht, hy⟩, hm⟩) (exists_congr (a2_max_remove ht hy hm))

/-- ✱207·26. \[\begin{align}&\vdash :P\in \text{trans}.{\sim}(yPy).\exists !\overrightarrow{\text{lt}} _{P}ʻ\beta .\supset .\overrightarrow{\text{lt}} _{P}ʻ\beta =\overrightarrow{\text{lt}} _{P}ʻ(\beta -\iota ʻy)\\ &[*207·13·12.*206·72]\end{align}\] -/
theorem pm207_26 : (P ∈ transR ∧ ¬P y y) ∧ (refs (ltP P) B).Nonempty →
    refs (ltP P) B = refs (ltP P) (B \ ι y) := by
  rintro ⟨⟨ht, hy⟩, ⟨l, hl⟩⟩
  exact a2_lt_remove ht hy fun h => hl.2 ⟨y, h⟩

/-- ✱207·261. \[\begin{align}&\vdash :P\in \text{trans}.y\in \overrightarrow{\text{min}}_{P}ʻ\beta .\exists !\overrightarrow{\text{lt}} _{P}ʻ\beta .\supset .\overrightarrow{\text{lt}} _{P}ʻ\beta =\overrightarrow{\text{lt}} _{P}ʻ(\beta -\iota ʻy)\\ &[*207·26.*205·194]\end{align}\] -/
theorem pm207_261 : (P ∈ transR ∧ y ∈ refs (minP P) B) ∧ (refs (ltP P) B).Nonempty →
    refs (ltP P) B = refs (ltP P) (B \ ι y) := by
  rintro ⟨⟨ht, hy⟩, hl⟩
  have hy' := minP_iff.1 hy
  exact pm207_26 ⟨⟨ht, hy'.2 y hy'.1.1⟩, hl⟩

private theorem a2_refs_min_eq (hc : P ∈ connex) (hy : minP P y B) : refs (minP P) B = ι y :=
  Set.ext fun z => ⟨fun hz => a2_min_uniq hc hz hy, fun hz => by
    have e : z = y := hz
    rw [e]
    exact hy⟩

private theorem a2_diff_min_eq (hmin : ¬∃ y, minP P y B) : B \ refs (minP P) B = B :=
  Set.ext fun z => ⟨fun h => h.1, fun h => ⟨h, fun hz => hmin ⟨z, hz⟩⟩⟩

/-- ✱207·262. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .\exists !\overrightarrow{\text{lt}} _{P}ʻ\beta .\supset .\overrightarrow{\text{lt}} _{P}ʻ\beta =\overrightarrow{\text{lt}} _{P}ʻ(\beta -\overrightarrow{\text{min}}_{P}ʻ\beta )\\ &[*207·261.*205·3]\end{align}\] -/
theorem pm207_262 : P ∈ transR ∩ connex ∧ (refs (ltP P) B).Nonempty →
    refs (ltP P) B = refs (ltP P) (B \ refs (minP P) B) := by
  rintro ⟨⟨ht, hc⟩, hl⟩
  by_cases hmin : ∃ y, minP P y B
  · obtain ⟨y, hy⟩ := hmin
    rw [a2_refs_min_eq hc hy]
    exact pm207_261 ⟨⟨ht, hy⟩, hl⟩
  · rw [a2_diff_min_eq hmin]

/-- ✱207·263. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .\supset .\overrightarrow{\text{lt}} _{P}ʻ\beta \subset \overrightarrow{\text{lt}} _{P}ʻ(\beta -\overrightarrow{\text{min}}_{P}ʻ\beta )\\ &[*207·262.*24·12]\end{align}\] -/
theorem pm207_263 : P ∈ transR ∩ connex →
    refs (ltP P) B ⊆ refs (ltP P) (B \ refs (minP P) B) := by
  intro h x hx
  rw [← pm207_262 ⟨h, ⟨x, hx⟩⟩]
  exact hx

/-- ✱207·27. \(\vdash :P\in \text{trans}\cap \text{connex} .\beta \cap CʻP{\sim}\in 1.\supset .\overrightarrow{\text{lt}} _{P}ʻ\beta =\overrightarrow{\text{lt}} _{P}ʻ(\beta -\overrightarrow{\text{min}}_{P}ʻ\beta )\) -/
theorem pm207_27 : P ∈ transR ∩ connex ∧ B ∩ fld P ∉ one →
    refs (ltP P) B = refs (ltP P) (B \ refs (minP P) B) := by
  rintro ⟨⟨ht, hc⟩, h1⟩
  by_cases hmin : ∃ y, minP P y B
  · obtain ⟨y, hy⟩ := hmin
    rw [a2_refs_min_eq hc hy]
    have hy' := minP_iff.1 hy
    have hyy : ¬P y y := hy'.2 y hy'.1.1
    obtain ⟨z, hz, hzy⟩ : ∃ z, z ∈ B ∩ fld P ∧ z ≠ y := by
      by_contra hn
      push Not at hn
      exact h1 (mem_one_iff.2 ⟨y, fun z => ⟨fun hz => hn z hz, fun e => by rw [e]; exact hy'.1⟩⟩)
    have hyz : P y z := by
      rcases mem_connex.1 hc y z ⟨hy'.1.2, hz.2⟩ with (h | h) | h
      · exact h
      · exact absurd h.symm hzy
      · exact absurd h (hy'.2 z hz.1)
    exact a2_lt_remove ht hyy fun hm => (maxP_iff.1 hm).2 z hz.1 hyz
  · rw [a2_diff_min_eq hmin]

/-- ✱207·28. \(\vdash :P\in \text{trans}.\supset .\overrightarrow{\text{lt}} _{P}ʻ(\alpha \cup Pʻʻ\alpha )=\overrightarrow{\text{lt}} _{P}ʻ\alpha \quad[*207·25]\) -/
theorem pm207_28 : P ∈ transR → refs (ltP P) (A ∪ P ʻʻ A) = refs (ltP P) A :=
  fun ht => pm207_25 ⟨ht, fun _ h => h⟩

/-- ✱207·281. \[\begin{align}&\vdash :P\in \text{trans}.{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .\supset .\overrightarrow{\text{lt}} _{P}ʻPʻʻ\alpha =\overrightarrow{\text{lt}} _{P}ʻ\alpha \\ &[*207·28·16.*205·123]\end{align}\] -/
theorem pm207_281 : P ∈ transR ∧ ¬(refs (maxP P) A).Nonempty →
    refs (ltP P) (P ʻʻ A) = refs (ltP P) A := by
  rintro ⟨ht, hn⟩
  have hsub := a2_noMax_iff_sub.1 hn
  have e : P ʻʻ A ∩ fld P = (A ∪ P ʻʻ A) ∩ fld P := by
    ext z
    constructor
    · rintro ⟨hz, hzf⟩
      exact ⟨Or.inr hz, hzf⟩
    · rintro ⟨hz | hz, hzf⟩
      · exact ⟨hsub ⟨hz, hzf⟩, hzf⟩
      · exact ⟨hz, hzf⟩
  calc refs (ltP P) (P ʻʻ A) = refs (ltP P) (P ʻʻ A ∩ fld P) := pm207_16
    _ = refs (ltP P) ((A ∪ P ʻʻ A) ∩ fld P) := by rw [e]
    _ = refs (ltP P) (A ∪ P ʻʻ A) := pm207_16.symm
    _ = refs (ltP P) A := pm207_28 ht

/-- ✱207·282. \[\begin{align}&\vdash :P\in \text{trans}.{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻ\beta .Pʻʻ\alpha =Pʻʻ\beta .\supset .\overrightarrow{\text{lt}} _{P}ʻ\alpha =\overrightarrow{\text{lt}} _{P}ʻ\beta \\ &[*207·281]\end{align}\] -/
theorem pm207_282 : ((P ∈ transR ∧ ¬(refs (maxP P) A).Nonempty) ∧
    ¬(refs (maxP P) B).Nonempty) ∧ P ʻʻ A = P ʻʻ B → refs (ltP P) A = refs (ltP P) B := by
  rintro ⟨⟨⟨ht, hA⟩, hB⟩, he⟩
  rw [← pm207_281 ⟨ht, hA⟩, ← pm207_281 ⟨ht, hB⟩, he]

/-- ✱207·29. \(\vdash :P\in \text{trans}.\supset .\overrightarrow{\text{lt}} _{P}ʻ\alpha =\overrightarrow{\text{lt}} _{P}ʻP_{*}ʻʻ\alpha\) -/
theorem pm207_29 : P ∈ transR → refs (ltP P) A = refs (ltP P) (anc P ʻʻ A) := by
  intro ht
  rw [a2_anc_img_eq ht, ← a2_img_inter_fld (A := A), pm207_28 ht]
  exact pm207_16

/-- ✱207·291. \(\vdash :P\in \text{trans}\cap \text{connex} .\text{E}!\text{lt}_Pʻ\alpha .\supset .\overrightarrow{P}ʻ\text{lt}_Pʻ\alpha =P_{*}ʻʻ\alpha\) -/
theorem pm207_291 : P ∈ transR ∩ connex ∧ EDesc (ltP P) A →
    Desc (ltP P) A (fun l => refs P l = anc P ʻʻ A) := by
  rintro ⟨h, hl⟩
  obtain ⟨l, hl1⟩ := a2_EDesc_exists hl
  refine a2_desc_intro hl1 (fun b hb => a2_EDesc_uniq hl hb hl1) ?_
  have hs : EDesc (seqP P) A := a2_EDesc_of hl1.1 fun b hb => a2_seq_uniq h.2 hb hl1.1
  rw [(a2_desc_iff.1 (pm206_22 ⟨h, hs⟩).1).2 l hl1.1, a2_anc_img_eq h.1]

/-- ✱207·3. \(\vdash :\alpha \cap CʻP=\Lambda .\supset .\overrightarrow{\text{lt}} _{P}ʻ\alpha =\overrightarrow{B}ʻP\) -/
theorem pm207_3 : A ∩ fld P = Λ → refs (ltP P) A = refs Beg P := a2_lt_of_empty

/-- ✱207·31. \(\vdash :P\,\unicode{x2abd}\, J.x\in CʻP-\text{ᗡ}ʻ(P\dot{-} P^{2}).\supset .x\text{lt}_P\overrightarrow{P}ʻx\) -/
theorem pm207_31 : P ⪽ J ∧ x ∈ fld P \ codom (P ∸ rsq P) → ltP P x (refs P x) := by
  rintro ⟨hJ, hx, hn⟩
  refine ⟨pm206_4 ⟨hJ, hx⟩, ?_⟩
  rintro ⟨m, hm⟩
  have hm' := maxP_iff.1 hm
  apply hn
  refine ⟨m, (show P m x ∧ ¬rsq P m x from ⟨hm'.1.1, ?_⟩)⟩
  rintro ⟨z, hmz, hzx⟩
  exact hm'.2 z hzx hmz

/-- ✱207·32. \[\begin{align}&\vdash :P\in \text{Rl}ʻJ\cap \text{connex} .x\in CʻP-\text{ᗡ}ʻ(P\dot{-} P^{2}).\supset .x=\text{lt}_Pʻ\overrightarrow{P}ʻx\\ &[*207·31·24]\end{align}\] -/
theorem pm207_32 : P ∈ rl J ∩ connex ∧ x ∈ fld P \ codom (P ∸ rsq P) →
    Desc (ltP P) (refs P x) (fun l => x = l) := by
  rintro ⟨⟨hJ, hc⟩, hx⟩
  have h1 := pm207_31 ⟨hJ, hx⟩
  exact a2_desc_intro h1 (fun b hb => a2_seq_uniq hc hb.1 h1.1) rfl

/-- ✱207·33. \(\vdash :x\in \text{ᗡ}ʻ(P\dot{-} P^{2}).\supset .\overrightarrow{\text{lt}} _{P}ʻ\overrightarrow{P}ʻx=\Lambda \quad[*205·252.*207·11]\) -/
theorem pm207_33 : x ∈ codom (P ∸ rsq P) → refs (ltP P) (refs P x) = Λ := by
  rintro ⟨y, hyx⟩
  have hyx' : P y x ∧ ¬rsq P y x := hyx
  apply pm207_11
  refine ⟨y, maxP_iff.2 ⟨⟨hyx'.1, a2_fl hyx'.1⟩, fun z hz hyz => hyx'.2 ⟨z, hyz, hz⟩⟩⟩

/-- ✱207·34. \(\vdash :P\in \text{connex} .x\,\text{lt}_P\,\alpha .\supset .x\text{lt}_P\overrightarrow{P}ʻx.x{\sim}\in \text{ᗡ}ʻ(P\dot{-} P^{2})\) -/
theorem pm207_34 : P ∈ connex ∧ ltP P x A → ltP P x (refs P x) ∧ x ∉ codom (P ∸ rsq P) := by
  rintro ⟨hc, hl⟩
  obtain ⟨h1, h2⟩ := pm207_2 ⟨hc, hl⟩
  have hs := seqP_iff.1 hl.1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [seqP_iff]
    refine ⟨⟨fun y hy => hy.1, hs.1.2⟩, fun z hz hzx => ?_⟩
    exact hs.2 z (fun a ha => hz a ⟨h1 ha, ha.2⟩) hzx
  · rintro ⟨m, hm⟩
    have hm' := maxP_iff.1 hm
    obtain ⟨w, hw, hmw⟩ := h2 hm'.1.1
    exact hm'.2 w (h1 ⟨hw, a2_fr hmw⟩) hmw
  · rintro ⟨y, hyx⟩
    have hyx' : P y x ∧ ¬rsq P y x := hyx
    obtain ⟨w, hw, hyw⟩ := h2 hyx'.1
    exact hyx'.2 ⟨w, hyw, h1 ⟨hw, a2_fr hyw⟩⟩

/-- ✱207·35. \(\vdash :P\in R1ʻJ\cap \text{connex} .\supset .\text{D}ʻ\text{lt}_P=CʻP-\text{ᗡ}ʻ(P\dot{-} P^{2})\)

**Status.** proved (reading): transcription error of the e-text, which prints `R1ʻJ` for
`Rlʻ J` (as in ✱207·32 and ✱207·36 and the demonstration, which cites ✱207·32). -/
theorem pm207_35 : P ∈ rl J ∩ connex → dom (ltP P) = fld P \ codom (P ∸ rsq P) := by
  rintro ⟨hJ, hc⟩
  ext x
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨(seqP_iff.1 hA.1).1.2, (pm207_34 ⟨hc, hA⟩).2⟩
  · intro hx
    exact ⟨refs P x, pm207_31 ⟨hJ, hx⟩⟩

/-- ✱207·36. \[\begin{align}\vdash :P\in \text{Rl}ʻJ\cap &\text{connex} .\supset .\\ &\text{D}ʻ\text{lt}_P=\text{lt}_Pʻʻ\overrightarrow{P}ʻʻ{CʻP-\text{ᗡ}ʻ(P\dot{-} P^{2})}=\text{lt}_Pʻʻ\overrightarrow{P}ʻʻCʻP\end{align}\] -/
theorem pm207_36 : P ∈ rl J ∩ connex →
    dom (ltP P) = ltP P ʻʻ (Rfwd P ʻʻ (fld P \ codom (P ∸ rsq P))) ∧
      ltP P ʻʻ (Rfwd P ʻʻ (fld P \ codom (P ∸ rsq P))) = ltP P ʻʻ (Rfwd P ʻʻ fld P) := by
  rintro ⟨hJ, hc⟩
  have h3 : ltP P ʻʻ (Rfwd P ʻʻ fld P) ⊆ dom (ltP P) := fun x ⟨B, _, hB⟩ => ⟨B, hB⟩
  have h1 : dom (ltP P) ⊆ ltP P ʻʻ (Rfwd P ʻʻ (fld P \ codom (P ∸ rsq P))) := by
    rintro x ⟨A, hA⟩
    have hx := pm207_34 ⟨hc, hA⟩
    exact ⟨refs P x, ⟨x, ⟨(seqP_iff.1 hA.1).1.2, hx.2⟩, rfl⟩, hx.1⟩
  have h2 : ltP P ʻʻ (Rfwd P ʻʻ (fld P \ codom (P ∸ rsq P))) ⊆ ltP P ʻʻ (Rfwd P ʻʻ fld P) := by
    rintro x ⟨B, ⟨y, hy, hBy⟩, hB⟩
    exact ⟨B, ⟨y, hy.1, hBy⟩, hB⟩
  exact ⟨Set.Subset.antisymm h1 (h2.trans h3), Set.Subset.antisymm h2 (h3.trans h1)⟩

/-- ✱207·4. \[\begin{align}\vdash \colon\ldotp x \text{limax}_P \alpha .&\equiv :x \text{max}_{P} \alpha .\lor.x \text{lt}_P \alpha :\\ &\equiv :x \text{max}_{P} \alpha .\lor.{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .x \text{seq}_{P} \alpha \quad[(*207·03)]\end{align}\] -/
theorem pm207_4 : (limaxP P x A ↔ maxP P x A ∨ ltP P x A) ∧
    (maxP P x A ∨ ltP P x A ↔ maxP P x A ∨ ¬(refs (maxP P) A).Nonempty ∧ seqP P x A) :=
  ⟨Iff.rfl, or_congr Iff.rfl and_comm⟩

/-- ✱207·401. \(\vdash .\text{limin}_P=\text{limax}(\breve{P} ) \quad[(*207·04)]\) -/
theorem pm207_401 : liminP P = limaxP P˘ := liminP_eq_limaxP_cnv P

private theorem a2_limax_uniq (hc : P ∈ connex) {a b : α} (ha : limaxP P a A)
    (hb : limaxP P b A) : a = b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact a2_max_uniq hc ha hb
  · exact absurd ⟨a, ha⟩ hb.2
  · exact absurd ⟨b, hb⟩ ha.2
  · exact a2_seq_uniq hc ha.1 hb.1

/-- ✱207·41. \[\begin{align}&\vdash :P\in \text{connex} .\supset .\text{limax}_P,\text{limin}_P\in 1\rightarrow \text{Cls}\\ &[*71·24.*205·31.*207·24.(*207·03·04)]\end{align}\] -/
theorem pm207_41 : P ∈ connex → limaxP P ∈ arrow one Cls ∧ liminP P ∈ arrow one Cls := by
  intro hc
  refine ⟨mem_arrow_one_Cls.2 fun _ _ _ h => a2_limax_uniq hc h.1 h.2, ?_⟩
  rw [liminP_eq_limaxP_cnv]
  exact mem_arrow_one_Cls.2 fun _ _ _ h => a2_limax_uniq (a2_connex_cnv hc) h.1 h.2

/-- ✱207·42. \(\vdash :\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha .\supset .\overrightarrow{\text{limax}} _{P}ʻ\alpha =\overrightarrow{\text{max}}_{P}ʻ\alpha \quad[*207·4]\) -/
theorem pm207_42 : (refs (maxP P) A).Nonempty → refs (limaxP P) A = refs (maxP P) A := by
  intro hne
  ext x
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd hne h.2
  · exact Or.inl

/-- ✱207·43. \(\vdash :\overrightarrow{\text{max}}_{P}ʻ\alpha =\Lambda .\supset .\overrightarrow{\text{limax}} _{P}ʻ\alpha =\overrightarrow{\text{seq}} _{P}ʻ\alpha =\overrightarrow{\text{lt}} _{P}ʻ\alpha \quad[*207·4]\) -/
theorem pm207_43 : refs (maxP P) A = Λ →
    refs (limaxP P) A = refs (seqP P) A ∧ refs (seqP P) A = refs (ltP P) A := by
  intro h
  have h' : ¬∃ m, maxP P m A := fun ⟨m, hm⟩ => a2_eq_Null_iff.1 h m hm
  have e := pm207_12 h
  refine ⟨?_, e.symm⟩
  rw [← e]
  ext x
  constructor
  · rintro (hx | hx)
    · exact absurd ⟨x, hx⟩ h'
    · exact hx
  · exact Or.inr

/-- ✱207·44. \[\begin{align}&\vdash .\text{ᗡ}ʻ\text{limax}_P=\text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{lt}_P=\text{ᗡ}ʻ\text{max}_{P}\cup \text{ᗡ}ʻ\text{seq}_{P}\\ &[*207·14.(*207·03)]\end{align}\] -/
theorem pm207_44 : codom (limaxP P) = codom (maxP P) ∪ codom (ltP P) ∧
    codom (maxP P) ∪ codom (ltP P) = codom (maxP P) ∪ codom (seqP P) := by
  constructor
  · ext A
    constructor
    · rintro ⟨x, hx | hx⟩
      · exact Or.inl ⟨x, hx⟩
      · exact Or.inr ⟨x, hx⟩
    · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
      · exact ⟨x, Or.inl hx⟩
      · exact ⟨x, Or.inr hx⟩
  · ext A
    exact (pm207_14 (P := P) (A := A)).symm

/-- ✱207·45. \(\vdash .\overrightarrow{\text{limax}} _{P}ʻ\alpha =\overrightarrow{\text{max}}_{P}ʻ\alpha \cup \overrightarrow{\text{lt}} _{P}ʻ\alpha \quad[(*207·03)]\) -/
theorem pm207_45 : refs (limaxP P) A = refs (maxP P) A ∪ refs (ltP P) A :=
  Set.ext fun _ => Iff.rfl

/-- ✱207·46. \(\vdash \colon\ldotp x=\text{limax}_Pʻ\alpha .\equiv :x=\text{max}_{P}ʻ\alpha .\lor.x=\text{lt}_Pʻ\alpha\) -/
theorem pm207_46 : Desc (limaxP P) A (fun l => x = l) ↔
    Desc (maxP P) A (fun m => x = m) ∨ Desc (ltP P) A (fun l => x = l) := by
  by_cases hm : (refs (maxP P) A).Nonempty
  · rw [a2_refs_congr_desc (pm207_42 hm)]
    have hn : ¬Desc (ltP P) A (fun l => x = l) := fun h => by
      obtain ⟨l, hl⟩ := a2_EDesc_exists (a2_desc_iff.1 h).1
      exact hl.2 hm
    exact ⟨Or.inl, fun h => h.resolve_right hn⟩
  · have e : refs (limaxP P) A = refs (ltP P) A := by
      ext y
      constructor
      · rintro (h | h)
        · exact absurd ⟨y, h⟩ hm
        · exact h
      · exact Or.inr
    rw [a2_refs_congr_desc e]
    have hn : ¬Desc (maxP P) A (fun m => x = m) :=
      fun h => hm (a2_EDesc_exists (a2_desc_iff.1 h).1)
    exact ⟨Or.inr, fun h => h.resolve_left hn⟩

/-- ✱207·47. \(\vdash : \exists ! \overrightarrow{\text{lt}} _{P}ʻ\alpha . \equiv . \exists ! \overrightarrow{\text{limax}} _{P}ʻ\alpha . {\sim} \exists ! \overrightarrow{\text{max}}_{P}ʻ\alpha\) -/
theorem pm207_47 : (refs (ltP P) A).Nonempty ↔
    (refs (limaxP P) A).Nonempty ∧ ¬(refs (maxP P) A).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, Or.inr hx⟩, hx.2⟩
  · rintro ⟨⟨x, hx | hx⟩, hn⟩
    · exact absurd ⟨x, hx⟩ hn
    · exact ⟨x, hx⟩

/-- ✱207·48. \(\vdash . \overrightarrow{\text{limax}} _{P}ʻ\alpha = \overrightarrow{\text{limax}} _{P}ʻ(\alpha \cap CʻP) \quad[*207·45 . *205·151 . *207·16]\) -/
theorem pm207_48 : refs (limaxP P) A = refs (limaxP P) (A ∩ fld P) := by
  rw [pm207_45, pm207_45, ← pm207_16 (A := A)]
  congr 1
  ext x
  exact a2_maxP_inter.symm

private theorem a2_max_anc (ht : P ∈ transR) {m : α} : maxP P m (anc P ʻʻ A) ↔ maxP P m A := by
  rw [a2_anc_img_eq ht, maxP_iff, maxP_iff]
  constructor
  · rintro ⟨⟨hx | ⟨w, hw, hxw⟩, hxf⟩, hn⟩
    · exact ⟨hx, fun y hy hxy => hn y (Or.inl ⟨hy, a2_fr hxy⟩) hxy⟩
    · exact absurd hxw (hn w (Or.inl ⟨hw, a2_fr hxw⟩))
  · rintro ⟨⟨hx, hxf⟩, hn⟩
    refine ⟨⟨Or.inl ⟨hx, hxf⟩, hxf⟩, ?_⟩
    rintro y (⟨hy, -⟩ | ⟨w, hw, hyw⟩) hxy
    · exact hn y hy hxy
    · exact hn w hw (mem_transR.1 ht m y w ⟨hxy, hyw⟩)

/-- ✱207·481. \[\begin{align}&\vdash : P \in \text{trans} . \supset . \overrightarrow{\text{limax}} _{P}ʻ\alpha = \overrightarrow{\text{limax}} _{P}ʻP_{*}ʻʻ\alpha\\ &[*207·45 . *205·191 . *207·29]\end{align}\] -/
theorem pm207_481 : P ∈ transR → refs (limaxP P) A = refs (limaxP P) (anc P ʻʻ A) := by
  intro ht
  rw [pm207_45, pm207_45, ← pm207_29 ht]
  congr 1
  ext x
  exact (a2_max_anc ht).symm

/-- ✱207·482. \(\vdash : P \in \text{Ser} . \alpha \subset CʻP . \alpha = \text{limax}_Pʻ\alpha . \supset . \alpha \subset \overrightarrow{P}_{*}ʻ\alpha\)

**Status.** proved (reading): transcription error of the e-text, which prints `α` for the term
`a` twice: PM's ✱207·482 is `P ∈ Ser . α ⊂ C'P . a = limax_P'α . ⊃ . α ⊂ P⃗_*'a` (as printed,
`α = limax_P'α` equates a class with a term, and the demonstration works with
`a = max_P'α`, `a = lt_P'α` and concludes `α ⊂ P⃗_*'a`). -/
theorem pm207_482 : (P ∈ Ser ∧ A ⊆ fld P) ∧ Desc (limaxP P) A (fun l => a = l) →
    A ⊆ refs (anc P) a := by
  rintro ⟨⟨hS, hA⟩, ⟨l, hlu, hal⟩⟩
  have hl : limaxP P a A := by
    rw [hal]
    exact (hlu l).2 rfl
  intro x hx
  show anc P x a
  rw [anc_iff_of_transR hS.1.2]
  rcases hl with hm | hlt
  · have hm' := maxP_iff.1 hm
    rcases mem_connex.1 hS.2 x a ⟨hA hx, hm'.1.2⟩ with (h | h) | h
    · exact Or.inr h
    · exact Or.inl ⟨h, hA hx⟩
    · exact absurd h (hm'.2 x hx)
  · exact Or.inr ((seqP_iff.1 hlt.1).1.1 x ⟨hx, hA hx⟩)

/-- ✱207·5. \[\begin{align}&\vdash : P \in \text{Ser} . \supset . \overrightarrow{\text{limax}} _{P}ʻ\alpha = \overrightarrow{\text{seq}} _{P}ʻPʻʻ\alpha = \overrightarrow{\text{min}}_{P}ʻ(\overrightarrow{\text{max}}_{P}ʻ\alpha \cup \overrightarrow{\text{seq}}_{P}ʻ\alpha )\\ &[*206·33·35·37]\end{align}\] -/
theorem pm207_5 : P ∈ Ser → refs (limaxP P) A = refs (seqP P) (P ʻʻ A) ∧
    refs (seqP P) (P ʻʻ A) = refs (minP P) (refs (maxP P) A ∪ refs (seqP P) A) := by
  intro hS
  refine ⟨?_, pm206_37 hS⟩
  by_cases hm : (refs (maxP P) A).Nonempty
  · rw [pm207_42 hm]
    obtain ⟨m, hm1⟩ := hm
    have h34 : seqP P m (P ʻʻ A) := pm206_34 hS hm1
    ext x
    constructor
    · intro hx
      have e : x = m := a2_max_uniq hS.2 hx hm1
      rw [e]
      exact h34
    · intro hx
      have e : x = m := a2_seq_uniq hS.2 hx h34
      rw [e]
      exact hm1
  · rw [pm206_33 ⟨⟨hS.1.2, hS.2⟩, fun h => hm (a2_EDesc_exists h)⟩]
    exact (pm207_43 (a2_eq_Null_iff.2 fun m h => hm ⟨m, h⟩)).1

/-- ✱207·51. \[\begin{align}&\vdash \colon\ldotp P \in \text{Ser} . \supset : x = \text{limax}_Pʻ\alpha . \equiv . x \in CʻP . \overrightarrow{P}ʻx = Pʻʻ\alpha \\ &[*205·54 . *207·232·46]\end{align}\] -/
theorem pm207_51 : P ∈ Ser →
    (Desc (limaxP P) A (fun l => x = l) ↔ x ∈ fld P ∧ refs P x = P ʻʻ A) := by
  intro hS
  have irr := mem_rl_J.1 hS.1.1
  have tr := mem_transR.1 hS.1.2
  rw [pm207_46, pm207_232 hS]
  constructor
  · rintro (h | ⟨⟨hx, -⟩, he⟩)
    · obtain ⟨m, hmu, hxm⟩ := h
      have hm : maxP P m A := (hmu m).2 rfl
      rw [← hxm] at hm
      have hm' := maxP_iff.1 hm
      refine ⟨hm'.1.2, Set.Subset.antisymm (fun z hzx => ⟨x, hm'.1.1, hzx⟩) ?_⟩
      rintro z ⟨w, hw, hzw⟩
      rcases mem_connex.1 hS.2 w x ⟨a2_fr hzw, hm'.1.2⟩ with (h | h) | h
      · exact tr z w x ⟨hzw, h⟩
      · show P z x
        rw [← h]
        exact hzw
      · exact absurd h (hm'.2 w hw)
    · exact ⟨hx, he⟩
  · rintro ⟨hx, he⟩
    by_cases hxA : x ∈ A
    · left
      have hm : maxP P x A := maxP_iff.2 ⟨⟨hxA, hx⟩, fun y hy hxy => by
        have hxi : x ∈ P ʻʻ A := ⟨y, hy, hxy⟩
        rw [← he] at hxi
        exact irr x hxi⟩
      exact a2_desc_intro hm (fun b hb => a2_max_uniq hS.2 hb hm) rfl
    · exact Or.inr ⟨⟨hx, hxA⟩, he⟩

/-- ✱207·52. \(\vdash \colon\ldotp P \in \text{Ser} . \exists ! Pʻʻ\alpha . \supset : x = \text{limax}_Pʻ\alpha . \equiv . \overrightarrow{P}ʻx = Pʻʻ\alpha \quad[*207·51]\) -/
theorem pm207_52 : P ∈ Ser ∧ (P ʻʻ A).Nonempty →
    (Desc (limaxP P) A (fun l => x = l) ↔ refs P x = P ʻʻ A) := by
  rintro ⟨hS, ⟨z, hz⟩⟩
  rw [pm207_51 hS]
  refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
  have hzx : z ∈ refs P x := by
    rw [he]
    exact hz
  exact a2_fr (show P z x from hzx)

/-- ✱207·521. \(\vdash \colon\ldotp P \in \text{Ser} . \supset : x = \text{lt}_Pʻ\alpha . \equiv . x \in CʻP . \overrightarrow{P}ʻx = Pʻʻ\alpha . {\sim} \text{E}! \text{max}_{P}ʻ\alpha\) -/
theorem pm207_521 : P ∈ Ser → (Desc (ltP P) A (fun l => x = l) ↔
    (x ∈ fld P ∧ refs P x = P ʻʻ A) ∧ ¬EDesc (maxP P) A) := by
  intro hS
  rw [pm207_232 hS]
  constructor
  · intro h
    exact ⟨⟨h.1.1, h.2⟩, ((pm206_28 hS).1 h).2⟩
  · rintro ⟨⟨hx, he⟩, hn⟩
    refine ⟨⟨hx, fun hxA => ?_⟩, he⟩
    have hxi : x ∈ P ʻʻ A := a2_noMax_iff_sub.1 (a2_noMax_of hS.2 hn) ⟨hxA, hx⟩
    rw [← he] at hxi
    exact mem_rl_J.1 hS.1.1 x hxi

/-- ✱207·53. \(\vdash : P \in \text{Ser} . \kappa \subset \text{ᗡ}ʻ\text{limax}_P . \supset . \overrightarrow{\text{limax}} _{P}ʻ\text{limax}_Pʻʻ\kappa = \overrightarrow{\text{limax}} _{P}ʻsʻ\kappa\) -/
theorem pm207_53 : P ∈ Ser ∧ K ⊆ codom (limaxP P) →
    refs (limaxP P) (limaxP P ʻʻ K) = refs (limaxP P) (sumCls K) := by
  rintro ⟨hS, hK⟩
  have key : ∀ l B, limaxP P l B → refs P l = P ʻʻ B := fun l B hl =>
    ((pm207_51 hS).1 (a2_desc_intro hl (fun b hb => a2_limax_uniq hS.2 hb hl) rfl)).2
  rw [(pm207_5 hS).1, (pm207_5 hS).1]
  congr 1
  ext x
  constructor
  · rintro ⟨l, ⟨B, hB, hl⟩, hxl⟩
    have hxi : x ∈ refs P l := hxl
    rw [key l B hl] at hxi
    obtain ⟨b, hb, hxb⟩ := hxi
    exact ⟨b, ⟨B, hB, hb⟩, hxb⟩
  · rintro ⟨b, ⟨B, hB, hb⟩, hxb⟩
    obtain ⟨l, hl⟩ := hK hB
    have hxi : x ∈ refs P l := by
      rw [key l B hl]
      exact ⟨b, hb, hxb⟩
    exact ⟨l, ⟨B, hB, hl⟩, hxi⟩

/-- ✱207·54. \(\vdash :P\in \text{Ser}.\kappa \subset \text{ᗡ}ʻ\text{lt}_P.\supset .\overrightarrow{\text{limax}} _{P}ʻ\text{lt}_Pʻʻ\kappa =\overrightarrow{\text{limax}} _{P}ʻsʻ\kappa =\overrightarrow{\text{lt}} _{P}ʻsʻ\kappa\) -/
theorem pm207_54 : P ∈ Ser ∧ K ⊆ codom (ltP P) →
    refs (limaxP P) (ltP P ʻʻ K) = refs (limaxP P) (sumCls K) ∧
      refs (limaxP P) (sumCls K) = refs (ltP P) (sumCls K) := by
  rintro ⟨hS, hK⟩
  have e1 : ltP P ʻʻ K = limaxP P ʻʻ K := by
    ext x
    constructor
    · rintro ⟨B, hB, hx⟩
      exact ⟨B, hB, Or.inr hx⟩
    · rintro ⟨B, hB, hx | hx⟩
      · obtain ⟨l, hl⟩ := hK hB
        exact absurd ⟨x, hx⟩ hl.2
      · exact ⟨B, hB, hx⟩
  have hK' : K ⊆ codom (limaxP P) := fun B hB => by
    obtain ⟨l, hl⟩ := hK hB
    exact ⟨l, Or.inr hl⟩
  refine ⟨by rw [e1]; exact pm207_53 ⟨hS, hK'⟩, ?_⟩
  have hnm : refs (maxP P) (sumCls K) = Λ := by
    rw [a2_eq_Null_iff]
    intro m hm
    have hm' := maxP_iff.1 hm
    obtain ⟨B, hB, hmB⟩ := hm'.1.1
    obtain ⟨l, hl⟩ := hK hB
    obtain ⟨w, hw, hmw⟩ := a2_noMax_iff_sub.1 hl.2 ⟨hmB, hm'.1.2⟩
    exact hm'.2 w ⟨B, hB, hw⟩ hmw
  have h43 := pm207_43 hnm
  rw [h43.1, h43.2]

/-- ✱207·55. \[\begin{align}&\vdash :P\in \text{Ser}.\kappa \subset \text{ᗡ}ʻ\text{lt}_P.sʻ\kappa \in \text{ᗡ}ʻ\text{lt}_P.\supset .\text{limax}_Pʻ\text{lt}_Pʻʻ\kappa =\text{lt}_Pʻsʻ\kappa\\ &[*207·54]\end{align}\] -/
theorem pm207_55 : (P ∈ Ser ∧ K ⊆ codom (ltP P)) ∧ sumCls K ∈ codom (ltP P) →
    Desc (limaxP P) (ltP P ʻʻ K) (fun l => Desc (ltP P) (sumCls K) (fun l' => l = l')) := by
  rintro ⟨h, ⟨l, hl⟩⟩
  rw [a2_refs_congr_desc ((pm207_54 h).1.trans (pm207_54 h).2)]
  have hu : ∀ b, ltP P b (sumCls K) → b = l := fun b hb => a2_seq_uniq h.1.2 hb.1 hl.1
  exact a2_desc_intro hl hu (a2_desc_intro hl hu rfl)

/-- ✱207·6. \(\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .\overrightarrow{\text{lt}} _{P}ʻ\alpha =Sʻʻ\overrightarrow{\text{lt}} _{Q}ʻ\breve{S} ʻʻ\alpha\) -/
theorem pm207_6 {Q : β → β → Prop} {S : α → β → Prop} : S ∈ smorbar P Q →
    refs (ltP P) A = S ʻʻ refs (ltP Q) (S˘ ʻʻ A) :=
  fun hS => a2_smor_refs hS (fun _ hx => (seqP_iff.1 hx.1).1.2) fun _ _ h => a2_smor_lt hS h

/-- ✱207·61. \(\vdash \colon\ldotp S\in P\,\overline{\,\text{smor}\,}\,Q.\supset :\text{E}!\text{lt}_Pʻ\alpha .\equiv .\text{E}!\text{lt}_{Q}ʻ\breve{S} ʻʻ\alpha \quad[*207·6.*53·3]\) -/
theorem pm207_61 {Q : β → β → Prop} {S : α → β → Prop} : S ∈ smorbar P Q →
    (EDesc (ltP P) A ↔ EDesc (ltP Q) (S˘ ʻʻ A)) :=
  fun hS => a2_smor_EDesc hS (fun _ hx => (seqP_iff.1 hx.1).1.2)
    (fun _ hz => (seqP_iff.1 hz.1).1.2) fun _ _ h => a2_smor_lt hS h

/-- ✱207·62. \(\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\text{E}!\text{lt}_Pʻ\alpha .\supset .\text{lt}_Pʻ\alpha =Sʻ\text{lt}_{Q}ʻ\breve{S} ʻʻ\alpha \quad[*207·6.*53·31]\) -/
theorem pm207_62 {Q : β → β → Prop} {S : α → β → Prop} : S ∈ smorbar P Q ∧ EDesc (ltP P) A →
    Desc (ltP P) A (fun l => Desc2 S (ltP Q) (S˘ ʻʻ A) (fun t => l = t)) :=
  fun ⟨hS, hE⟩ => a2_smor_desc hS (fun _ hx => (seqP_iff.1 hx.1).1.2)
    (fun _ hz => (seqP_iff.1 hz.1).1.2) (fun _ _ h => a2_smor_lt hS h) hE

/-- ✱207·63. \(\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .\text{lt}_Pʻʻ\kappa =Sʻʻ\text{lt}_{Q}ʻʻ\breve{S} ʻʻʻ\kappa\) -/
theorem pm207_63 {Q : β → β → Prop} {S : α → β → Prop} : S ∈ smorbar P Q →
    ltP P ʻʻ K = S ʻʻ (ltP Q ʻʻ (S˘ ʻʻʻ K)) := by
  intro hS
  ext x
  constructor
  · rintro ⟨B, hB, hx⟩
    have hxi : x ∈ S ʻʻ refs (ltP Q) (S˘ ʻʻ B) := by
      rw [← pm207_6 hS]
      exact hx
    obtain ⟨z, hz, hxz⟩ := hxi
    exact ⟨z, ⟨S˘ ʻʻ B, ⟨B, hB, rfl⟩, hz⟩, hxz⟩
  · rintro ⟨z, ⟨C, ⟨B, hB, hC⟩, hz⟩, hxz⟩
    have hC' : C = S˘ ʻʻ B := hC
    rw [hC'] at hz
    have hxi : x ∈ refs (ltP P) B := by
      rw [pm207_6 hS]
      exact ⟨z, hz, hxz⟩
    exact ⟨B, hB, hxi⟩

private theorem a2_smor_limax {Q : β → β → Prop} {S : α → β → Prop} (hS : S ∈ smorbar P Q)
    {x : α} {z : β} (hxz : S x z) : limaxP P x A ↔ limaxP Q z (S˘ ʻʻ A) :=
  or_congr (a2_smor_max hS hxz) (a2_smor_lt hS hxz)

private theorem a2_limax_fld {x : α} (h : limaxP P x A) : x ∈ fld P := by
  rcases h with h | h
  · exact (maxP_iff.1 h).1.2
  · exact (seqP_iff.1 h.1).1.2

/-- ✱207·64. \[\begin{align}&\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .\overrightarrow{\text{limax}} _{P}ʻ\alpha =Sʻʻ\overrightarrow{\text{limax}} _{Q}ʻ\breve{S} ʻʻ\alpha\\ &[*205·8.*207·6·45]\end{align}\] -/
theorem pm207_64 {Q : β → β → Prop} {S : α → β → Prop} : S ∈ smorbar P Q →
    refs (limaxP P) A = S ʻʻ refs (limaxP Q) (S˘ ʻʻ A) :=
  fun hS => a2_smor_refs hS (fun _ hx => a2_limax_fld hx) fun _ _ h => a2_smor_limax hS h

/-- ✱207·65. \[\begin{align}&\vdash \colon\ldotp S\in P\,\overline{\,\text{smor}\,}\,Q.\supset :\text{E}!\text{limax}_Pʻ\alpha .\equiv .\text{E}!\text{limax}_{Q}ʻ\breve{S} ʻʻ\alpha\\ &[*207·64]\end{align}\] -/
theorem pm207_65 {Q : β → β → Prop} {S : α → β → Prop} : S ∈ smorbar P Q →
    (EDesc (limaxP P) A ↔ EDesc (limaxP Q) (S˘ ʻʻ A)) :=
  fun hS => a2_smor_EDesc hS (fun _ hx => a2_limax_fld hx) (fun _ hz => a2_limax_fld hz)
    fun _ _ h => a2_smor_limax hS h

/-- ✱207·66. \[\begin{align}&\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\text{E}!\text{limax}_Pʻ\alpha .\supset .\text{limax}_Pʻ\alpha =Sʻ\text{limax}_{Q}ʻ\breve{S} ʻʻ\alpha\\ &[*207·64]\end{align}\] -/
theorem pm207_66 {Q : β → β → Prop} {S : α → β → Prop} : S ∈ smorbar P Q ∧ EDesc (limaxP P) A →
    Desc (limaxP P) A (fun l => Desc2 S (limaxP Q) (S˘ ʻʻ A) (fun t => l = t)) :=
  fun ⟨hS, hE⟩ => a2_smor_desc hS (fun _ hx => a2_limax_fld hx) (fun _ hz => a2_limax_fld hz)
    (fun _ _ h => a2_smor_limax hS h) hE

/-- ✱207·7. \[\begin{align}\vdash \colon\ldotp P\in \text{trans}.\lor.&P^{2}\,\unicode{x2abd}\, J:\supset :\\ &\text{limin}_Pʻ\gamma =\text{limax}_Pʻ\gamma .\supset .\text{limin}_Pʻ\gamma =\text{min}_{P}ʻ\gamma =\text{max}_{P}ʻ\gamma\end{align}\] -/
theorem pm207_7 : (P ∈ transR ∨ rsq P ⪽ J) →
    (Desc (liminP P) G (fun a => Desc (limaxP P) G (fun b => a = b)) →
      Desc (liminP P) G (fun a => Desc (minP P) G (fun b => a = b)) ∧
        Desc (minP P) G (fun b => Desc (maxP P) G (fun c => b = c))) := by
  intro hor hd
  obtain ⟨x, hxu, y, hyu, hxy⟩ := hd
  have hx : liminP P x G := (hxu x).2 rfl
  have hy : limaxP P y G := (hyu y).2 rfl
  rw [← hxy] at hy
  have key : minP P x G ∧ maxP P x G := by
    rcases hx with hmin | htl <;> rcases hy with hmax | hlt
    · exact ⟨hmin, hmax⟩
    · exact absurd (minP_iff.1 hmin).1.1 (pm206_2 hlt.1)
    · exfalso
      have hs : seqP P˘ x G := by
        rw [← precP_eq_seqP_cnv]
        exact htl.1
      exact pm206_2 hs (maxP_iff.1 hmax).1.1
    · exact (a2_prec_seq_false hor htl.1 hlt.1).elim
  obtain ⟨hmin, hmax⟩ := key
  have hxu' : ∀ z, liminP P z G → z = x := fun z hz => (hxu z).1 hz
  have hminu : ∀ z, minP P z G → z = x := fun z hz => (hxu z).1 (Or.inl hz)
  have hmaxu : ∀ z, maxP P z G → z = x := by
    intro z hz
    rw [hxy]
    exact (hyu z).1 (Or.inl hz)
  exact ⟨a2_desc_intro hx hxu' (a2_desc_intro hmin hminu rfl),
    a2_desc_intro hmin hminu (a2_desc_intro hmax hmaxu rfl)⟩

/-- ✱207·71. \[\begin{align}\vdash \colon\ldotp P\in \text{connex} :P\in \text{trans}.\lor.P^{2}\,\unicode{x2abd}\, &J:\text{limin}_Pʻ\gamma =\text{limax}_Pʻ\gamma :\supset .\\ &\gamma \cap CʻP\in 1.\gamma \cap CʻP={℩}ʻ\text{limax}_Pʻ\gamma \\ &[*207·7.*205·73]\end{align}\] -/
theorem pm207_71 : (P ∈ connex ∧ (P ∈ transR ∨ rsq P ⪽ J)) ∧
    Desc (liminP P) G (fun a => Desc (limaxP P) G (fun b => a = b)) →
      G ∩ fld P ∈ one ∧ Desc (limaxP P) G (fun l => G ∩ fld P = ι l) := by
  rintro ⟨⟨hc, hor⟩, hd⟩
  obtain ⟨-, h2⟩ := pm207_7 hor hd
  obtain ⟨m, hmu, M, hMu, hmM⟩ := h2
  have hmin : minP P m G := (hmu m).2 rfl
  have hmax : maxP P m G := by
    rw [hmM]
    exact (hMu M).2 rfl
  have hmin' := minP_iff.1 hmin
  have hmax' := maxP_iff.1 hmax
  have e : G ∩ fld P = ι m := by
    ext z
    constructor
    · intro hz
      rcases mem_connex.1 hc z m ⟨hz.2, hmin'.1.2⟩ with (h | h) | h
      · exact absurd h (hmin'.2 z hz.1)
      · exact h
      · exact absurd h (hmax'.2 z hz.1)
    · intro hz
      have e' : z = m := hz
      rw [e']
      exact hmin'.1
  have hl : limaxP P m G := Or.inl hmax
  refine ⟨?_, a2_desc_intro hl (fun b hb => a2_limax_uniq hc hb hl) e⟩
  rw [e]
  exact ⟨m, rfl⟩

/-- ✱207·72. \[\begin{align}&\vdash \colon\ldotp P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.\supset :\text{limin}_Pʻ\gamma =\text{limax}_Pʻ\gamma .\equiv .\gamma \cap CʻP\in 1\\ &[*207·71.*205·731·17.*207·42]\end{align}\] -/
theorem pm207_72 : P ∈ connex ∧ rsq P ⪽ J →
    (Desc (liminP P) G (fun a => Desc (limaxP P) G (fun b => a = b)) ↔ G ∩ fld P ∈ one) := by
  rintro ⟨hc, hJ⟩
  refine ⟨fun h => (pm207_71 ⟨⟨hc, Or.inr hJ⟩, h⟩).1, fun h => ?_⟩
  obtain ⟨x, hx⟩ := mem_one_iff.1 h
  have hxG := (hx x).2 rfl
  have hxx : ¬P x x := fun h => a2_asymm hJ h h
  have hmin : minP P x G := minP_iff.2 ⟨hxG, fun y hy hyx => hxx (by
    rw [(hx y).1 ⟨hy, a2_fl hyx⟩] at hyx
    exact hyx)⟩
  have hmax : maxP P x G := maxP_iff.2 ⟨hxG, fun y hy hxy => hxx (by
    rw [(hx y).1 ⟨hy, a2_fr hxy⟩] at hxy
    exact hxy)⟩
  have hlimin : ∀ z, liminP P z G → z = x := by
    rintro z (hz | hz)
    · exact a2_min_uniq hc hz hmin
    · exact absurd ⟨x, hmin⟩ hz.2
  have hlimax : ∀ z, limaxP P z G → z = x := by
    rintro z (hz | hz)
    · exact a2_max_uniq hc hz hmax
    · exact absurd ⟨x, hmax⟩ hz.2
  exact a2_desc_intro (show liminP P x G from Or.inl hmin) hlimin
    (a2_desc_intro (show limaxP P x G from Or.inl hmax) hlimax rfl)

/-!
## [✱208] The correlation of series

*(Vol. 2, p. 605)*

> *Summary of* *208.
>
> The propositions of this number are chiefly important on account of their consequences in the theory of well-ordered series (*250 ff.) and in the theory of vector-families (*330 ff.). When two well-ordered series are ordinally similar, they have only one correlator; and a well-ordered series is not ordinally similar to any of its segments. Of these two propositions, the first is an immediate consequence of *208·41, and the second is an immediate consequence of *208·47.
>
> …

**Lean reading.** `cror'P` is `cror P` (✱208·01 defines a descriptive function that always
exists); `S ∈ 1 → 1` is `S ∈ arrow one one`, `S;P` is `S ⁏ P` (`S̆;S;P` is `S˘ ⁏ S ⁏ P`, which
is `S˘ ⁏ (S ⁏ P)`), `P ⥏ D'S` is `P ⥏ dom S`, `S ∈ P smor̄ Q` is `S ∈ smorbar P Q`, `P smor Q`
is `smor P Q`, `S, T ∈ …` is the conjunction, `S | T̆` is `S ⨾ T˘`, `I ↾ C'P` is `I ↾ fld P`,
`Cl ex'C'P` is `clEx (fld P)`, `Rl'P ∩ Nr'P` is `rl P ∩ nr α P` (the relation-number taken in
the type of `P`, the only type in which `Rl'P` has members), `ι'P` is `ι P` and `∃̇!P` is
`rEx P`. The correlators are one-one, so `S'x` (the `y` with `ySx`) is the description
`Desc S x ψ`, `S̆'x` is `Desc S˘ x ψ`, and `S'S'x`, `S'T̆'x` are `Desc2`; the class
`x̂{(S'x)Px}` is `{x | Desc S x (fun y => P y x)}` (the description has the smallest scope,
inside the braces), and `(S'S'x)P(S'x)` has the first-written description outermost. In ✱208·3
the e-text prints `min_P'` (without the arrow) where `∃!` and ✱208·14·22 require `min⃗_P'`.

**Status.** proved (all propositions; ✱208·3 proved (reading), see its docstring).
-/

/-- ✱208·01 (Df). \(\text{cror}ʻP=sʻ\,\overline{\,\text{smor}\,}\,Pʻʻ\text{Rl}ʻP \quad\text{Df}\) -/
theorem pm208_01 : cror P = sumCls (opR smorbar P ʻʻ rl P) := rfl

/-- ✱208·1. \(\vdash :S\in \text{cror}ʻP.\equiv .S\in 1\rightarrow 1.\text{ᗡ}ʻS=CʻP.S^{;}P\,\unicode{x2abd}\, P\) -/
theorem pm208_1 {S : α → α → Prop} :
    S ∈ cror P ↔ (S ∈ arrow one one ∧ codom S = fld P) ∧ S ⁏ P ⪽ P := mem_cror

private theorem a2_cror_facts {S : α → α → Prop} (hS : S ∈ cror P) :
    ((∀ x y z, S x z ∧ S y z → x = y) ∧ (∀ x y z, S x y ∧ S x z → y = z)) ∧
      (∀ x, x ∈ fld P ↔ ∃ y, S y x) ∧ (∀ x y z w, (S x z ∧ S y w) ∧ P z w → P x y) := by
  obtain ⟨⟨h1, hcod⟩, hsub⟩ := mem_cror.1 hS
  refine ⟨mem_arrow_one_one.1 h1, fun x => (Set.ext_iff.1 hcod x).symm, ?_⟩
  intro x y z w h
  exact hsub x y ((semi_apply S P x y).2 ⟨z, w, h⟩)

/-- ✱208·11. \(\vdash :S\in \text{cror}ʻP.\supset .S^{;}P\,\unicode{x2abd}\, P\unicode{x0294f}\text{D}ʻS\) -/
theorem pm208_11 {S : α → α → Prop} : S ∈ cror P → S ⁏ P ⪽ P ⥏ dom S := by
  intro hS x y hxy
  obtain ⟨z, w, ⟨hxz, hyw⟩, -⟩ := (semi_apply S P x y).1 hxy
  exact ⟨⟨⟨z, hxz⟩, (mem_cror.1 hS).2 x y hxy⟩, ⟨w, hyw⟩⟩

/-- ✱208·111. \[\begin{align}&\vdash :S\in \text{cror}ʻP.\supset .\text{D}ʻS=CʻS^{;}P=SʻʻCʻP.\text{D}ʻS\subset \text{ᗡ}ʻS\\ &[*150·22·23.*208·1.*33·265]\end{align}\] -/
theorem pm208_111 {S : α → α → Prop} : S ∈ cror P →
    (dom S = fld (S ⁏ P) ∧ fld (S ⁏ P) = S ʻʻ fld P) ∧ dom S ⊆ codom S := by
  intro hS
  obtain ⟨⟨_, hcod⟩, hsub⟩ := mem_cror.1 hS
  obtain ⟨-, hfP, -⟩ := a2_cror_facts hS
  have e2 : fld (S ⁏ P) = S ʻʻ fld P := by
    ext x
    constructor
    · rintro ⟨y, h | h⟩
      · obtain ⟨z, w, ⟨hxz, -⟩, hzw⟩ := (semi_apply S P x y).1 h
        exact ⟨z, a2_fl hzw, hxz⟩
      · obtain ⟨z, w, ⟨-, hxw⟩, hzw⟩ := (semi_apply S P y x).1 h
        exact ⟨w, a2_fr hzw, hxw⟩
    · rintro ⟨z, ⟨w, hzw | hwz⟩, hxz⟩
      · obtain ⟨y, hyw⟩ := (hfP w).1 ⟨z, Or.inr hzw⟩
        exact ⟨y, Or.inl ((semi_apply S P x y).2 ⟨z, w, ⟨hxz, hyw⟩, hzw⟩)⟩
      · obtain ⟨y, hyw⟩ := (hfP w).1 ⟨z, Or.inl hwz⟩
        exact ⟨y, Or.inr ((semi_apply S P y x).2 ⟨w, z, ⟨hyw, hxz⟩, hwz⟩)⟩
  have e1 : dom S = S ʻʻ fld P := by
    ext x
    constructor
    · rintro ⟨z, hxz⟩
      exact ⟨z, (hfP z).2 ⟨x, hxz⟩, hxz⟩
    · rintro ⟨z, -, hxz⟩
      exact ⟨z, hxz⟩
  refine ⟨⟨e1.trans e2.symm, e2⟩, fun x hx => ?_⟩
  rw [e1, ← e2] at hx
  rw [hcod]
  exact fld_mono hsub hx

/-- ✱208·12. \(\vdash :S\in \text{cror}ʻP.\supset .\breve{S} ^{;}S^{;}P=P.P\,\unicode{x2abd}\, \breve{S} ^{;}P \quad[*151·252·26.*208·1]\) -/
theorem pm208_12 {S : α → α → Prop} : S ∈ cror P → S˘ ⁏ S ⁏ P = P ∧ P ⪽ S˘ ⁏ P := by
  intro hS
  obtain ⟨-, hsub⟩ := mem_cror.1 hS
  obtain ⟨⟨_, hmo⟩, hfP, -⟩ := a2_cror_facts hS
  have e : S˘ ⁏ S ⁏ P = P := by
    funext x y
    apply propext
    rw [semi_apply]
    constructor
    · rintro ⟨z, w, ⟨hzx, hwy⟩, hzw⟩
      obtain ⟨x', y', ⟨hzx', hwy'⟩, hP⟩ := (semi_apply S P z w).1 hzw
      have e1 : x' = x := hmo z x' x ⟨hzx', hzx⟩
      have e2 : y' = y := hmo w y' y ⟨hwy', hwy⟩
      rw [e1, e2] at hP
      exact hP
    · intro hxy
      obtain ⟨z, hzx⟩ := (hfP x).1 (a2_fl hxy)
      obtain ⟨w, hwy⟩ := (hfP y).1 (a2_fr hxy)
      exact ⟨z, w, ⟨hzx, hwy⟩, (semi_apply S P z w).2 ⟨x, y, ⟨hzx, hwy⟩, hxy⟩⟩
  refine ⟨e, fun x y hxy => ?_⟩
  have h' : (S˘ ⁏ S ⁏ P) x y := by
    rw [e]
    exact hxy
  exact semi_mono S˘ hsub x y h'

/-- ✱208·13. \(\vdash :S\in \text{cror}ʻP.(Sʻx)Px.\supset .(SʻSʻx)P(Sʻx)\) -/
theorem pm208_13 {S : α → α → Prop} : S ∈ cror P ∧ Desc S x (fun y => P y x) →
    Desc2 S S x (fun z => Desc S x (fun y => P z y)) := by
  rintro ⟨hS, ⟨y, hyu, hyx⟩⟩
  obtain ⟨⟨hom, _⟩, hfP, hsub⟩ := a2_cror_facts hS
  have hSyx : S y x := (hyu y).2 rfl
  obtain ⟨z, hzy⟩ := (hfP y).1 (a2_fl hyx)
  rw [desc2_iff]
  refine ⟨y, hyu, ?_⟩
  show Desc S y (fun z => Desc S x (fun y => P z y))
  refine a2_desc_intro hzy (fun b hb => hom b z y ⟨hb, hzy⟩) ?_
  exact ⟨y, hyu, hsub z y y x ⟨⟨hzy, hSyx⟩, hyx⟩⟩

/-- ✱208·131. \(\vdash :S\in \text{cror}ʻP.xP(Sʻx).\supset .(Sʻx)P(SʻSʻx) \quad[\text{Proof as in *208·13}]\) -/
theorem pm208_131 {S : α → α → Prop} : S ∈ cror P ∧ Desc S x (fun y => P x y) →
    Desc S x (fun y => Desc2 S S x (fun z => P y z)) := by
  rintro ⟨hS, ⟨y, hyu, hxy⟩⟩
  obtain ⟨⟨hom, _⟩, hfP, hsub⟩ := a2_cror_facts hS
  have hSyx : S y x := (hyu y).2 rfl
  obtain ⟨z, hzy⟩ := (hfP y).1 (a2_fr hxy)
  refine ⟨y, hyu, ?_⟩
  show Desc2 S S x (fun z => P y z)
  rw [desc2_iff]
  exact ⟨y, hyu, a2_desc_intro hzy (fun b hb => hom b z y ⟨hb, hzy⟩)
    (hsub y z x y ⟨⟨hSyx, hzy⟩, hxy⟩)⟩

/-- ✱208·14. \(\vdash :S\in \text{cror}ʻP.\supset .\overrightarrow{\text{min}}_{P}ʻ\hat{x}\{(Sʻx)Px\}=\Lambda .\overrightarrow{\text{max}}_{P}ʻ\hat{x}\{xP(Sʻx)\}=\Lambda\) -/
theorem pm208_14 {S : α → α → Prop} : S ∈ cror P →
    refs (minP P) {x | Desc S x (fun y => P y x)} = Λ ∧
      refs (maxP P) {x | Desc S x (fun y => P x y)} = Λ := by
  intro hS
  obtain ⟨⟨hom, _⟩, hfP, hsub⟩ := a2_cror_facts hS
  constructor
  · rw [a2_eq_Null_iff]
    intro m hm
    have hm' := minP_iff.1 hm
    obtain ⟨y, hym, hyPm⟩ := (a2_desc_oneMany hom).1 (show Desc S m (fun y => P y m) from hm'.1.1)
    obtain ⟨z, hzy⟩ := (hfP y).1 (a2_fl hyPm)
    have hzPy : P z y := hsub z y y m ⟨⟨hzy, hym⟩, hyPm⟩
    exact hm'.2 y (show Desc S y (fun v => P v y) from
      (a2_desc_oneMany hom).2 ⟨z, hzy, hzPy⟩) hyPm
  · rw [a2_eq_Null_iff]
    intro m hm
    have hm' := maxP_iff.1 hm
    obtain ⟨y, hym, hmPy⟩ := (a2_desc_oneMany hom).1 (show Desc S m (fun y => P m y) from hm'.1.1)
    obtain ⟨z, hzy⟩ := (hfP y).1 (a2_fr hmPy)
    have hyPz : P y z := hsub y z m y ⟨⟨hym, hzy⟩, hmPy⟩
    exact hm'.2 y (show Desc S y (fun v => P y v) from
      (a2_desc_oneMany hom).2 ⟨z, hzy, hyPz⟩) hmPy

/-- ✱208·2. \(\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.S\in \text{cror}ʻP.\supset .P=\breve{S} ^{;}P.S^{;}P=P\unicode{x0294f}\text{D}ʻS\) -/
theorem pm208_2 {S : α → α → Prop} : (P ∈ connex ∧ rsq P ⪽ J) ∧ S ∈ cror P →
    P = S˘ ⁏ P ∧ S ⁏ P = P ⥏ dom S := by
  rintro ⟨⟨hc, hJ⟩, hS⟩
  obtain ⟨⟨hom, _⟩, hfP, hsub⟩ := a2_cror_facts hS
  constructor
  · funext x y
    apply propext
    constructor
    · intro hxy
      exact (pm208_12 hS).2 x y hxy
    · intro h
      obtain ⟨a, b, ⟨hax, hby⟩, hab⟩ := (semi_apply S˘ P x y).1 h
      have hax' : S a x := hax
      have hby' : S b y := hby
      rcases mem_connex.1 hc x y ⟨(hfP x).2 ⟨a, hax'⟩, (hfP y).2 ⟨b, hby'⟩⟩ with (h1 | h1) | h1
      · exact h1
      · rw [← h1] at hby'
        have e : a = b := hom a b x ⟨hax', hby'⟩
        rw [e] at hab
        exact absurd hab (fun h => a2_asymm hJ h h)
      · exact absurd (hsub b a y x ⟨⟨hby', hax'⟩, h1⟩) (fun h => a2_asymm hJ hab h)
  · funext x y
    apply propext
    constructor
    · intro hxy
      obtain ⟨z, w, ⟨hxz, hyw⟩, -⟩ := (semi_apply S P x y).1 hxy
      exact ⟨⟨⟨z, hxz⟩, (mem_cror.1 hS).2 x y hxy⟩, ⟨w, hyw⟩⟩
    · rintro ⟨⟨⟨z, hxz⟩, hxy⟩, ⟨w, hyw⟩⟩
      rcases mem_connex.1 hc z w ⟨(hfP z).2 ⟨x, hxz⟩, (hfP w).2 ⟨y, hyw⟩⟩ with (h1 | h1) | h1
      · exact (semi_apply S P x y).2 ⟨z, w, ⟨hxz, hyw⟩, h1⟩
      · rw [← h1] at hyw
        have e : x = y := hom x y z ⟨hxz, hyw⟩
        rw [e] at hxy
        exact absurd hxy (fun h => a2_asymm hJ h h)
      · exact absurd (hsub y x w z ⟨⟨hyw, hxz⟩, h1⟩) (fun h => a2_asymm hJ hxy h)

/-- ✱208·21. \(\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.S\in \text{cror}ʻP.(Sʻx)Px.x\in \text{D}ʻS.\supset .xP(\breve{S} ʻx)\) -/
theorem pm208_21 {S : α → α → Prop} : (((P ∈ connex ∧ rsq P ⪽ J) ∧ S ∈ cror P) ∧
    Desc S x (fun y => P y x)) ∧ x ∈ dom S → Desc S˘ x (fun y => P x y) := by
  rintro ⟨⟨⟨⟨hc, hJ⟩, hS⟩, ⟨y, hyu, hyx⟩⟩, ⟨z, hxz⟩⟩
  obtain ⟨⟨hom, hmo⟩, hfP, hsub⟩ := a2_cror_facts hS
  have hSyx : S y x := (hyu y).2 rfl
  refine a2_desc_intro (show S˘ z x from hxz) (fun b hb => hmo x b z ⟨hb, hxz⟩) ?_
  rcases mem_connex.1 hc x z ⟨a2_fr hyx, (hfP z).2 ⟨x, hxz⟩⟩ with (h | h) | h
  · exact h
  · rw [← h] at hxz
    have e : y = x := hom y x x ⟨hSyx, hxz⟩
    rw [e] at hyx
    exact absurd hyx (fun h => a2_asymm hJ h h)
  · exact absurd (hsub x y z x ⟨⟨hxz, hSyx⟩, h⟩) (fun h' => a2_asymm hJ hyx h')

/-- ✱208·211. \[\begin{align}&\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.S\in \text{cror}ʻP.xP(Sʻx).x\in \text{D}ʻS.\supset .(\breve{S} ʻx)Px\\ &[\text{Proof as in *208·21}]\end{align}\] -/
theorem pm208_211 {S : α → α → Prop} : (((P ∈ connex ∧ rsq P ⪽ J) ∧ S ∈ cror P) ∧
    Desc S x (fun y => P x y)) ∧ x ∈ dom S → Desc S˘ x (fun y => P y x) := by
  rintro ⟨⟨⟨⟨hc, hJ⟩, hS⟩, ⟨y, hyu, hxy⟩⟩, ⟨z, hxz⟩⟩
  obtain ⟨⟨hom, hmo⟩, hfP, hsub⟩ := a2_cror_facts hS
  have hSyx : S y x := (hyu y).2 rfl
  refine a2_desc_intro (show S˘ z x from hxz) (fun b hb => hmo x b z ⟨hb, hxz⟩) ?_
  rcases mem_connex.1 hc z x ⟨(hfP z).2 ⟨x, hxz⟩, a2_fl hxy⟩ with (h | h) | h
  · exact h
  · rw [h] at hxz
    have e : y = x := hom y x x ⟨hSyx, hxz⟩
    rw [e] at hxy
    exact absurd hxy (fun h => a2_asymm hJ h h)
  · exact absurd (hsub y x x z ⟨⟨hSyx, hxz⟩, h⟩) (fun h' => a2_asymm hJ hxy h')

/-- ✱208·22. \[\begin{align}\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.&S\in \text{cror}ʻP.\text{ᗡ}ʻS\subset \text{D}ʻS.\supset .\\ &\overrightarrow{\text{max}}_{P}ʻ\hat{x}\{(Sʻx)Px\}=\Lambda .\overrightarrow{\text{min}}_{P}ʻ\hat{x}\{xP(Sʻx)\}=\Lambda\end{align}\] -/
theorem pm208_22 {S : α → α → Prop} : ((P ∈ connex ∧ rsq P ⪽ J) ∧ S ∈ cror P) ∧
    codom S ⊆ dom S →
      refs (maxP P) {x | Desc S x (fun y => P y x)} = Λ ∧
        refs (minP P) {x | Desc S x (fun y => P x y)} = Λ := by
  rintro ⟨⟨hcJ, hS⟩, hds⟩
  obtain ⟨⟨hom, _⟩, hfP, _⟩ := a2_cror_facts hS
  constructor
  · rw [a2_eq_Null_iff]
    intro m hm
    have hm' := maxP_iff.1 hm
    have hmd : m ∈ dom S := hds ((hfP m).1 hm'.1.2)
    obtain ⟨z, hzu, hmz⟩ := pm208_21 ⟨⟨⟨hcJ, hS⟩, hm'.1.1⟩, hmd⟩
    have hmzS : S m z := (hzu z).2 rfl
    exact hm'.2 z (show Desc S z (fun y => P y z) from
      (a2_desc_oneMany hom).2 ⟨m, hmzS, hmz⟩) hmz
  · rw [a2_eq_Null_iff]
    intro m hm
    have hm' := minP_iff.1 hm
    have hmd : m ∈ dom S := hds ((hfP m).1 hm'.1.2)
    obtain ⟨z, hzu, hzm⟩ := pm208_211 ⟨⟨⟨hcJ, hS⟩, hm'.1.1⟩, hmd⟩
    have hmzS : S m z := (hzu z).2 rfl
    exact hm'.2 z (show Desc S z (fun y => P z y) from
      (a2_desc_oneMany hom).2 ⟨m, hmzS, hzm⟩) hzm

private theorem a2_not_nonempty_of {X : Set α} (h : X = Λ) : ¬X.Nonempty :=
  fun ⟨x, hx⟩ => a2_eq_Null_iff.1 h x hx

private theorem a2_cror_of_smorbar {S : α → α → Prop} (hS : S ∈ smorbar P P) :
    S ∈ cror P ∧ codom S ⊆ dom S := by
  obtain ⟨⟨h1, hcod⟩, hP⟩ := hS
  have hcr : S ∈ cror P := mem_cror.2 ⟨⟨h1, hcod.symm⟩, fun x y h => by rw [hP]; exact h⟩
  refine ⟨hcr, fun x hx => ?_⟩
  rw [(pm208_111 hcr).1.1, ← hP, hcod]
  exact hx

/-- ✱208·3. \[\begin{align}\vdash :P&\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.S\in P\,\overline{\,\text{smor}\,}\,P.\supset .\\ &{\sim}\exists !\text{min}_{P}ʻ\hat{x}\{(Sʻx)Px\}.{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻ\hat{x}\{(Sʻx)Px\}.\\ &{\sim}\exists !\text{min}_{P}ʻ\hat{x}\{xP(Sʻx)\}.{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻ\hat{x}\{xP(Sʻx)\}\end{align}\]

**Status.** proved (reading): the e-text prints `∃!min_P'x̂{…}` (without the arrow) in the
first and third conjuncts; `∃!` applies to a class, and the demonstration (from ✱208·14·22,
which have `min⃗_P'`) and ✱208·32 show that `min⃗_P'` is meant. -/
theorem pm208_3 {S : α → α → Prop} : (P ∈ connex ∧ rsq P ⪽ J) ∧ S ∈ smorbar P P →
    ((¬(refs (minP P) {x | Desc S x (fun y => P y x)}).Nonempty ∧
      ¬(refs (maxP P) {x | Desc S x (fun y => P y x)}).Nonempty) ∧
      ¬(refs (minP P) {x | Desc S x (fun y => P x y)}).Nonempty) ∧
      ¬(refs (maxP P) {x | Desc S x (fun y => P x y)}).Nonempty := by
  rintro ⟨hcJ, hS⟩
  obtain ⟨hcr, hds⟩ := a2_cror_of_smorbar hS
  obtain ⟨e1, e2⟩ := pm208_14 hcr
  obtain ⟨e3, e4⟩ := pm208_22 ⟨⟨hcJ, hcr⟩, hds⟩
  exact ⟨⟨⟨a2_not_nonempty_of e1, a2_not_nonempty_of e3⟩, a2_not_nonempty_of e4⟩,
    a2_not_nonempty_of e2⟩

/-- ✱208·31. \(\vdash :S,T\in P\,\overline{\,\text{smor}\,}\,Q.\supset .S\mid \breve{T} \in P\,\overline{\,\text{smor}\,}\,P \quad[*151·131·141]\) -/
theorem pm208_31 {Q : β → β → Prop} {S T : α → β → Prop} :
    S ∈ smorbar P Q ∧ T ∈ smorbar P Q → S ⨾ T˘ ∈ smorbar P P := by
  rintro ⟨hS, hT⟩
  obtain ⟨⟨hSo, hSm⟩, hSP, -, hSQ⟩ := a2_smor_facts hS
  obtain ⟨⟨hTo, hTm⟩, hTP, hTf, hTQ⟩ := a2_smor_facts hT
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨w, hxw, hzw⟩, ⟨w', hyw', hzw'⟩⟩
    have e : w = w' := hTm z w w' ⟨hzw, hzw'⟩
    rw [← e] at hyw'
    exact hSo x y w ⟨hxw, hyw'⟩
  · rintro x y z ⟨⟨w, hxw, hyw⟩, ⟨w', hxw', hzw'⟩⟩
    have e : w = w' := hSm x w w' ⟨hxw, hxw'⟩
    rw [← e] at hzw'
    exact hTo y z w ⟨hyw, hzw'⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨w, hxw⟩ := (hTf x).1 hx
      obtain ⟨y, hyw⟩ := (hSQ w).1 ((hTQ w).2 ⟨x, hxw⟩)
      exact ⟨y, w, hyw, hxw⟩
    · rintro ⟨y, w, -, hxw⟩
      exact (hTf x).2 ⟨w, hxw⟩
  · funext x y
    apply propext
    rw [semi_apply]
    constructor
    · intro hxy
      obtain ⟨z, w, ⟨hxz, hyw⟩, hQ⟩ := (hSP x y).1 hxy
      obtain ⟨a, haz⟩ := (hTQ z).1 ((hSQ z).2 ⟨x, hxz⟩)
      obtain ⟨b, hbw⟩ := (hTQ w).1 ((hSQ w).2 ⟨y, hyw⟩)
      exact ⟨a, b, ⟨⟨z, hxz, haz⟩, ⟨w, hyw, hbw⟩⟩, (hTP a b).2 ⟨z, w, ⟨haz, hbw⟩, hQ⟩⟩
    · rintro ⟨a, b, ⟨⟨z, hxz, haz⟩, ⟨w, hyw, hbw⟩⟩, hab⟩
      obtain ⟨z', w', ⟨haz', hbw'⟩, hQ⟩ := (hTP a b).1 hab
      have e1 : z' = z := hTm a z' z ⟨haz', haz⟩
      have e2 : w' = w := hTm b w' w ⟨hbw', hbw⟩
      rw [e1, e2] at hQ
      exact (hSP x y).2 ⟨z, w, ⟨hxz, hyw⟩, hQ⟩

private theorem a2_desc2_comp {S : α → β → Prop} {T : γ → β → Prop}
    (hTm : ∀ x y z, T x y ∧ T x z → y = z) (x : γ) (ψ : α → Prop) : Desc2 S T˘ x ψ ↔ Desc (S ⨾ T˘) x ψ := by
  rw [desc2_iff]
  constructor
  · rintro ⟨z, hz, u, hu, hψ⟩
    refine ⟨u, fun v => ⟨?_, ?_⟩, hψ⟩
    · rintro ⟨w, hvw, hxw⟩
      have e : w = z := (hz w).1 hxw
      rw [e] at hvw
      exact (hu v).1 hvw
    · intro e
      rw [e]
      exact ⟨z, (hu u).2 rfl, (hz z).2 rfl⟩
  · rintro ⟨u, hu, hψ⟩
    obtain ⟨z, hSuz, hxz⟩ := (hu u).2 rfl
    refine ⟨z, fun w => ⟨fun hxw => hTm x w z ⟨hxw, hxz⟩, fun e => by rw [e]; exact hxz⟩,
      u, fun v => ⟨fun hvz => (hu v).1 ⟨z, hvz, hxz⟩, fun e => by rw [e]; exact hSuz⟩, hψ⟩

/-- ✱208·32. \[\begin{align}\vdash :P&\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.S,T\in P\,\overline{\,\text{smor}\,}\,Q.\supset .\\ &{\sim}\exists !\overrightarrow{\text{min}}_{P}ʻ\hat{x} \{(Sʻ\breve{T} ʻx)Px\}.{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻ\hat{x}\{(Sʻ\breve{T} ʻx)Px\}.\\ &{\sim}\exists !\overrightarrow{\text{min}}_{P}ʻ\hat{x}\{xP(Sʻ\breve{T} ʻx)\}.{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻ\hat{x}\{xP(Sʻ\breve{T} ʻx)\}\\\ &[*208·3·31.*34·41]\end{align}\] -/
theorem pm208_32 {Q : β → β → Prop} {S T : α → β → Prop} :
    (P ∈ connex ∧ rsq P ⪽ J) ∧ (S ∈ smorbar P Q ∧ T ∈ smorbar P Q) →
      ((¬(refs (minP P) {x | Desc2 S T˘ x (fun u => P u x)}).Nonempty ∧
        ¬(refs (maxP P) {x | Desc2 S T˘ x (fun u => P u x)}).Nonempty) ∧
        ¬(refs (minP P) {x | Desc2 S T˘ x (fun u => P x u)}).Nonempty) ∧
        ¬(refs (maxP P) {x | Desc2 S T˘ x (fun u => P x u)}).Nonempty := by
  rintro ⟨hcJ, hST⟩
  obtain ⟨⟨-, hTm⟩, -⟩ := a2_smor_facts hST.2
  have e1 : {x | Desc2 S T˘ x (fun u => P u x)} = {x | Desc (S ⨾ T˘) x (fun u => P u x)} :=
    Set.ext fun x => a2_desc2_comp hTm x _
  have e2 : {x | Desc2 S T˘ x (fun u => P x u)} = {x | Desc (S ⨾ T˘) x (fun u => P x u)} :=
    Set.ext fun x => a2_desc2_comp hTm x _
  rw [e1, e2]
  exact pm208_3 ⟨hcJ, pm208_31 hST⟩

/-- ✱208·4. \[\begin{align}\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.\text{Cl ex}ʻCʻP\subset \text{ᗡ}ʻ&\text{min}_{P}\cup \text{ᗡ}ʻ\text{max}_{P}.\\ &S,T\in P\,\overline{\,\text{smor}\,}\,Q.\supset .S=T\end{align}\] -/
theorem pm208_4 {Q : β → β → Prop} {S T : α → β → Prop} :
    ((P ∈ connex ∧ rsq P ⪽ J) ∧ clEx (fld P) ⊆ codom (minP P) ∪ codom (maxP P)) ∧
      (S ∈ smorbar P Q ∧ T ∈ smorbar P Q) → S = T := by
  rintro ⟨⟨hcJ, hcl⟩, hST⟩
  obtain ⟨⟨hSo, -⟩, -, hSf, hSQ⟩ := a2_smor_facts hST.1
  obtain ⟨⟨-, hTm⟩, -, hTf, hTQ⟩ := a2_smor_facts hST.2
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := pm208_32 ⟨hcJ, hST⟩
  have empty : ∀ C : Set α, C ⊆ fld P → ¬(refs (minP P) C).Nonempty →
      ¬(refs (maxP P) C).Nonempty → ∀ x, x ∉ C := by
    intro C hC hmin hmax x hx
    rcases hcl ⟨hC, ⟨x, hx⟩⟩ with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact hmin ⟨m, hm⟩
    · exact hmax ⟨m, hm⟩
  have sub : ∀ (φ : α → α → Prop), (∀ u v, φ u v → v ∈ fld P) →
      {x | Desc2 S T˘ x (fun u => φ u x)} ⊆ fld P := by
    intro φ hφ x hx
    obtain ⟨z, -, u, -, hu⟩ := (desc2_iff S T˘ x _).1 hx
    exact hφ u x hu
  have key : ∀ x, x ∈ fld P → ∀ y w, S y w ∧ T x w → y = x := by
    intro x hx y w ⟨hyw, hxw⟩
    have hd : ∀ ψ : α → Prop, Desc2 S T˘ x ψ ↔ ψ y := fun ψ =>
      (desc2_iff S T˘ x ψ).trans ((a2_desc_of_unique (R := T˘) (show T˘ w x from hxw)
        fun b hb => hTm x b w ⟨hb, hxw⟩).trans
          (a2_desc_of_unique hyw fun b hb => hSo b y w ⟨hb, hyw⟩))
    have hy : y ∈ fld P := (hSf y).2 ⟨w, hyw⟩
    rcases mem_connex.1 hcJ.1 y x ⟨hy, hx⟩ with (h | h) | h
    · exact absurd ((hd fun u => P u x).2 h)
        (empty _ (sub (fun u v => P u v) fun _ _ huv => a2_fr huv) h1 h2 x)
    · exact h
    · exact absurd ((hd fun u => P x u).2 h)
        (empty _ (sub (fun u v => P v u) fun _ _ huv => a2_fl huv) h3 h4 x)
  funext y w
  apply propext
  constructor
  · intro hyw
    obtain ⟨x, hxw⟩ := (hTQ w).1 ((hSQ w).2 ⟨y, hyw⟩)
    have e : y = x := key x ((hTf x).2 ⟨w, hxw⟩) y w ⟨hyw, hxw⟩
    rw [e]
    exact hxw
  · intro hyw
    obtain ⟨x, hxw⟩ := (hSQ w).1 ((hTQ w).2 ⟨y, hyw⟩)
    have e : x = y := key y ((hTf y).2 ⟨w, hyw⟩) x w ⟨hxw, hyw⟩
    rw [← e]
    exact hxw

/-- ✱208·41. \[\begin{align}\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.\text{Cl ex}ʻCʻP\subset \text{ᗡ}ʻ&\text{min}_{P}\cup \text{ᗡ}ʻ\text{max}_{P}.\\ &P\,\,\text{smor}\,\,Q.\supset .(P\,\overline{\,\text{smor}\,}\,Q)\in 1\\ [*208·4.*151·12.*52·16]\end{align}\] -/
theorem pm208_41 {Q : β → β → Prop} :
    ((P ∈ connex ∧ rsq P ⪽ J) ∧ clEx (fld P) ⊆ codom (minP P) ∪ codom (maxP P)) ∧ smor P Q →
      smorbar P Q ∈ one := by
  rintro ⟨h, ⟨S, hS⟩⟩
  exact mem_one_iff.2 ⟨S, fun T => ⟨fun hT => pm208_4 ⟨h, hT, hS⟩, fun e => by rw [e]; exact hS⟩⟩

private theorem a2_I_fld_mem_smorbar : (I ↾ fld P) ∈ smorbar P P := by
  refine ⟨⟨mem_arrow_one_one.2 ⟨fun x y z h => h.1.1.trans h.2.1.symm,
    fun x y z h => h.1.1.symm.trans h.2.1⟩, ?_⟩, ?_⟩
  · ext x
    exact ⟨fun hx => ⟨x, rfl, hx⟩, fun ⟨_, _, hx⟩ => hx⟩
  · funext x y
    apply propext
    rw [semi_apply]
    constructor
    · intro h
      exact ⟨x, y, ⟨⟨rfl, a2_fl h⟩, ⟨rfl, a2_fr h⟩⟩, h⟩
    · rintro ⟨z, w, ⟨⟨hxz, -⟩, ⟨hyw, -⟩⟩, h⟩
      have e1 : x = z := hxz
      have e2 : y = w := hyw
      rw [e1, e2]
      exact h

/-- ✱208·42. \[\begin{align}\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.\text{Cl ex}ʻCʻP\subset \text{ᗡ}ʻ\text{min}_{P}\cup &\text{ᗡ}ʻ\text{max}_{P}.\supset .\\ &P\,\overline{\,\text{smor}\,}\,P={℩}ʻ(I\upharpoonright CʻP)\\ [*208·4.*51·141.*151·121]\end{align}\] -/
theorem pm208_42 : (P ∈ connex ∧ rsq P ⪽ J) ∧ clEx (fld P) ⊆ codom (minP P) ∪ codom (maxP P) →
    smorbar P P = ι (I ↾ fld P) := by
  intro h
  ext T
  constructor
  · intro hT
    exact pm208_4 ⟨h, hT, a2_I_fld_mem_smorbar⟩
  · intro hT
    have e : T = I ↾ fld P := hT
    rw [e]
    exact a2_I_fld_mem_smorbar

/-- ✱208·43. \(\vdash :\text{Cl ex}ʻCʻP\subset \text{ᗡ}ʻ\text{min}_{P}.S\in \text{cror}ʻP.\supset .{\sim}(\exists x).(Sʻx)Px \quad[*208·14]\) -/
theorem pm208_43 {S : α → α → Prop} : clEx (fld P) ⊆ codom (minP P) ∧ S ∈ cror P →
    ¬∃ x, Desc S x (fun y => P y x) := by
  rintro ⟨hcl, hS⟩ ⟨x, hx⟩
  have hsub : {x | Desc S x (fun y => P y x)} ⊆ fld P := by
    rintro z ⟨y, -, hyz⟩
    exact a2_fr hyz
  obtain ⟨m, hm⟩ := hcl ⟨hsub, ⟨x, hx⟩⟩
  exact a2_eq_Null_iff.1 (pm208_14 hS).1 m hm

/-- ✱208·431. \(\vdash :\text{Cl ex}ʻCʻP\subset \text{ᗡ}ʻ\text{max}_{P}.S\in \text{cror}ʻP.\supset .{\sim}(\exists x).xP(Sʻx) \quad[*208·14]\) -/
theorem pm208_431 {S : α → α → Prop} : clEx (fld P) ⊆ codom (maxP P) ∧ S ∈ cror P →
    ¬∃ x, Desc S x (fun y => P x y) := by
  rintro ⟨hcl, hS⟩ ⟨x, hx⟩
  have hsub : {x | Desc S x (fun y => P x y)} ⊆ fld P := by
    rintro z ⟨y, -, hzy⟩
    exact a2_fl hzy
  obtain ⟨m, hm⟩ := hcl ⟨hsub, ⟨x, hx⟩⟩
  exact a2_eq_Null_iff.1 (pm208_14 hS).2 m hm

/-- ✱208·44. \[\begin{align}\vdash :P\in \text{connex} .\text{Cl ex}ʻCʻP\subset \text{ᗡ}ʻ\text{min}_{P}\cap &\text{ᗡ}ʻ\text{max}_{P}.S\in \text{cror}ʻP.\supset .\\ &S=I\upharpoonright CʻP\end{align}\] -/
theorem pm208_44 {S : α → α → Prop} :
    (P ∈ connex ∧ clEx (fld P) ⊆ codom (minP P) ∩ codom (maxP P)) ∧ S ∈ cror P →
      S = I ↾ fld P := by
  rintro ⟨⟨hc, hcl⟩, hS⟩
  have h43 := pm208_43 ⟨fun B hB => (hcl hB).1, hS⟩
  have h431 := pm208_431 ⟨fun B hB => (hcl hB).2, hS⟩
  obtain ⟨⟨hom, _⟩, hfP, _⟩ := a2_cror_facts hS
  have hds := (pm208_111 hS).2
  have fix : ∀ x, x ∈ fld P → S x x := by
    intro x hx
    obtain ⟨y, hyx⟩ := (hfP x).1 hx
    have hy : y ∈ fld P := (hfP y).2 (hds ⟨x, hyx⟩)
    rcases mem_connex.1 hc y x ⟨hy, hx⟩ with (h | h) | h
    · exact absurd ⟨x, (a2_desc_oneMany hom).2 ⟨y, hyx, h⟩⟩ h43
    · rw [h] at hyx
      exact hyx
    · exact absurd ⟨x, (a2_desc_oneMany hom).2 ⟨y, hyx, h⟩⟩ h431
  funext a b
  apply propext
  constructor
  · intro hab
    have hb : b ∈ fld P := (hfP b).2 ⟨a, hab⟩
    exact ⟨hom a b b ⟨hab, fix b hb⟩, hb⟩
  · rintro ⟨hab, hb⟩
    have e : a = b := hab
    rw [e]
    exact fix b hb

/-- ✱208·45. \(\vdash :P\in \text{connex} .\text{Cl ex}ʻCʻP\subset \text{ᗡ}ʻ\text{min}_{P}\cap \text{ᗡ}ʻ\text{max}_{P}.\supset .\text{Rl}ʻP\cap \text{Nr}ʻP={℩}ʻP\) -/
theorem pm208_45 : P ∈ connex ∧ clEx (fld P) ⊆ codom (minP P) ∩ codom (maxP P) →
    rl P ∩ nr α P = ι P := by
  intro h
  ext Q
  constructor
  · rintro ⟨hQP, ⟨S, ⟨h1, hcod⟩, hQ⟩⟩
    have hcr : S ∈ cror P :=
      mem_cror.2 ⟨⟨h1, hcod.symm⟩, fun x y hxy => hQP x y (by rw [hQ]; exact hxy)⟩
    have hSI := pm208_44 ⟨h, hcr⟩
    show Q = P
    rw [hQ, hSI]
    exact (a2_I_fld_mem_smorbar).2.symm
  · intro hQ
    have e : Q = P := hQ
    rw [e]
    exact ⟨fun _ _ h => h, smor_refl P⟩

/-- ✱208·46. \(\vdash :\text{Cl ex}ʻCʻP\subset \text{ᗡ}ʻ\text{min}_{P}.S\in \text{cror}ʻP.\supset .CʻP\cap pʻ\overleftarrow{P}ʻʻ\text{D}ʻS=\Lambda\) -/
theorem pm208_46 {S : α → α → Prop} : clEx (fld P) ⊆ codom (minP P) ∧ S ∈ cror P →
    fld P ∩ prodCls (Rbwd P ʻʻ dom S) = Λ := by
  rintro ⟨hcl, hS⟩
  rw [a2_eq_Null_iff]
  rintro x ⟨hx, hπ⟩
  obtain ⟨⟨hom, _⟩, hfP, _⟩ := a2_cror_facts hS
  obtain ⟨y, hyx⟩ := (hfP x).1 hx
  have hyx' : P y x := mem_prodCls_Rbwd.1 hπ y ⟨x, hyx⟩
  exact pm208_43 ⟨hcl, hS⟩ ⟨x, (a2_desc_oneMany hom).2 ⟨y, hyx, hyx'⟩⟩

/-- ✱208·461. \[\begin{align}&\vdash :\text{Cl ex}ʻCʻP\subset \text{ᗡ}ʻ\text{min}_{P}.S\in \text{cror}ʻP.\dot{\exists} !P.\supset .pʻ\overleftarrow{P}ʻʻ\text{D}ʻS=\Lambda\\ &[*208·46·1.*40·62]\end{align}\] -/
theorem pm208_461 {S : α → α → Prop} :
    (clEx (fld P) ⊆ codom (minP P) ∧ S ∈ cror P) ∧ rEx P → prodCls (Rbwd P ʻʻ dom S) = Λ := by
  rintro ⟨h, ⟨a, b, hab⟩⟩
  have e := pm208_46 h
  obtain ⟨-, hfP, _⟩ := a2_cror_facts h.2
  obtain ⟨y, hya⟩ := (hfP a).1 (a2_fl hab)
  rw [a2_eq_Null_iff] at e ⊢
  intro z hz
  exact e z ⟨a2_fr (mem_prodCls_Rbwd.1 hz y ⟨a, hya⟩), hz⟩

/-- ✱208·47. \(\vdash :\text{Cl ex}ʻCʻP\subset \text{ᗡ}ʻ\text{min}_{P}.Q\,\unicode{x2abd}\, P.\exists !CʻP\cap pʻ\overleftarrow{P}ʻʻCʻQ.\supset .{\sim}(Q\,\,\text{smor}\,\,P)\) -/
theorem pm208_47 {Q : α → α → Prop} : (clEx (fld P) ⊆ codom (minP P) ∧ Q ⪽ P) ∧
    (fld P ∩ prodCls (Rbwd P ʻʻ fld Q)).Nonempty → ¬smor Q P := by
  rintro ⟨⟨hcl, hQP⟩, hne⟩ ⟨S, ⟨h1, hcod⟩, hQ⟩
  have hcr : S ∈ cror P :=
    mem_cror.2 ⟨⟨h1, hcod.symm⟩, fun x y hxy => hQP x y (by rw [hQ]; exact hxy)⟩
  have e := pm208_46 ⟨hcl, hcr⟩
  have hd : dom S = fld Q := by rw [(pm208_111 hcr).1.1, ← hQ]
  rw [hd] at e
  obtain ⟨x, hx⟩ := hne
  exact a2_eq_Null_iff.1 e x hx

end PrincipiaMathematica
