import PrincipiaMathematica.Defs.Part5

/-!
# Part V, Section A: General theory of series

Volume 2. Numbers: ✱200, ✱201, ✱202, ✱204, ✱205.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w

/-! ### Helper lemmas (not PM propositions) -/

section Helpers

variable {α : Type u} {β : Type v}

private theorem eqΛ {A : Set α} : A = Λ ↔ ∀ x, x ∉ A := by
  rw [Null_eq_empty]; exact Set.eq_empty_iff_forall_notMem

private theorem eqΛr {R : α → β → Prop} : R = rNull ↔ ∀ x y, ¬ R x y := by
  constructor
  · rintro rfl x y; exact rNull_apply x y
  · intro h; funext x y; apply propext
    exact ⟨fun hr => (h x y hr).elim, fun hr => (rNull_apply x y hr).elim⟩

private theorem rsubJ {P : α → α → Prop} : P ⪽ J ↔ ∀ x, ¬ P x x := mem_rl_J

private theorem desc_iff_of {R : α → β → Prop} {y : β} {b : α} (h : ∀ x, R x y ↔ x = b)
    (ψ : α → Prop) : Desc R y ψ ↔ ψ b := TheIs_iff_of_unique h

private theorem mem_zero_union_one {A : Set α} :
    A ∈ (zero ∪ one : Set (Set α)) ↔ ∀ x y, x ∈ A → y ∈ A → x = y := by
  constructor
  · rintro (h | h) x y hx hy
    · have h' : A = Λ := h
      exact absurd hx (eqΛ.1 h' x)
    · obtain ⟨b, hb⟩ := mem_one_iff.1 h
      exact ((hb x).1 hx).trans ((hb y).1 hy).symm
  · intro h
    by_cases hA : A.Nonempty
    · obtain ⟨b, hb⟩ := hA
      exact Or.inr (mem_one_iff.2 ⟨b, fun z => ⟨fun hz => h z b hz hb, fun e => e ▸ hb⟩⟩)
    · exact Or.inl (show A = Λ from eqΛ.2 fun x hx => hA ⟨x, hx⟩)

private theorem po_trans {P : α → α → Prop} {x y z : α} (h1 : po P x y) (h2 : po P y z) :
    po P x z :=
  po_iff_transGen.2 ((po_iff_transGen.1 h1).trans (po_iff_transGen.1 h2))

private theorem po_of {P : α → α → Prop} {x y : α} (h : P x y) : po P x y :=
  po_iff_transGen.2 (Relation.TransGen.single h)

private theorem anc_trans {P : α → α → Prop} {x y z : α} (h1 : anc P x y) (h2 : anc P y z) :
    anc P x z := by
  rw [anc_iff_reflTransGen] at *
  exact ⟨h1.1, h1.2.trans h2.2⟩

private theorem anc_po_trans {P : α → α → Prop} {x y z : α} (h1 : anc P x y) (h2 : po P y z) :
    po P x z := by
  rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h
  · exact h2
  · exact po_trans h h2

private theorem po_anc_trans {P : α → α → Prop} {x y z : α} (h1 : po P x y) (h2 : anc P y z) :
    po P x z := by
  rcases anc_iff_po.1 h2 with ⟨rfl, -⟩ | h
  · exact h1
  · exact po_trans h1 h

private theorem fld_of_po {P : α → α → Prop} {x y : α} (h : po P x y) :
    x ∈ fld P ∧ y ∈ fld P := by
  have h' := po_iff_transGen.1 h
  obtain ⟨b, hxb, -⟩ := Relation.TransGen.head'_iff.1 h'
  obtain ⟨c, -, hcy⟩ := Relation.TransGen.tail'_iff.1 h'
  exact ⟨⟨b, Or.inl hxb⟩, ⟨c, Or.inr hcy⟩⟩

private theorem fld_of_anc {P : α → α → Prop} {x y : α} (h : anc P x y) :
    x ∈ fld P ∧ y ∈ fld P := by
  rcases anc_iff_po.1 h with ⟨rfl, hx⟩ | h
  · exact ⟨hx, hx⟩
  · exact fld_of_po h

private theorem anc_refl {P : α → α → Prop} {x : α} (hx : x ∈ fld P) : anc P x x :=
  anc_iff_po.2 (Or.inl ⟨rfl, hx⟩)

private theorem anc_of_po {P : α → α → Prop} {x y : α} (h : po P x y) : anc P x y :=
  anc_iff_po.2 (Or.inr h)

private theorem fld_po (P : α → α → Prop) : fld (po P) = fld P := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact (fld_of_po h).1
    · exact (fld_of_po h).2
  · rintro ⟨y, h | h⟩
    · exact ⟨y, Or.inl (po_of h)⟩
    · exact ⟨y, Or.inr (po_of h)⟩

private theorem fld_anc (P : α → α → Prop) : fld (anc P) = fld P := by
  ext x
  constructor
  · rintro ⟨y, h | h⟩
    · exact (fld_of_anc h).1
    · exact (fld_of_anc h).2
  · intro hx
    exact ⟨x, Or.inl (anc_refl hx)⟩

/-- Every power of `P` has `x` related to itself when `P` has (used for ✱200·37). -/
private theorem pot_refl {P Q : α → α → Prop} (hQ : Q ∈ pot P) {x : α} (hx : P x x) : Q x x := by
  have key : ∀ S, Relation.ReflTransGen (relProdR P) S P → S x x := by
    intro S h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact hx
    | head hac _ ih =>
      rw [relProdR_apply] at hac
      rw [hac]
      exact ⟨x, ih, hx⟩
  exact key Q (mem_pot_iff.1 hQ).2

/-- Every power of a transitive `P` is contained in `P` (used for ✱201·17). -/
private theorem pot_rsub {P Q : α → α → Prop} (hP : rsq P ⪽ P) (hQ : Q ∈ pot P) : Q ⪽ P := by
  have key : ∀ S, Relation.ReflTransGen (relProdR P) S P → S ⪽ P := by
    intro S h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ _ h => h
    | head hac _ ih =>
      rw [relProdR_apply] at hac
      rw [hac]
      rintro x y ⟨z, hxz, hzy⟩
      exact hP x y ⟨z, ih x z hxz, hzy⟩
  exact key Q (mem_pot_iff.1 hQ).2

private theorem cxne {P : α → α → Prop} (h : P ∈ connex) {x y : α} (hx : x ∈ fld P)
    (hy : y ∈ fld P) (hne : x ≠ y) : P x y ∨ P y x := by
  rcases mem_connex.1 h x y ⟨hx, hy⟩ with (h1 | h1) | h1
  · exact Or.inl h1
  · exact (hne h1).elim
  · exact Or.inr h1

private theorem cxpo {P : α → α → Prop} (h : po P ∈ connex) {x y : α} (hx : x ∈ fld P)
    (hy : y ∈ fld P) (hne : x ≠ y) : po P x y ∨ po P y x :=
  cxne h (by rw [fld_po]; exact hx) (by rw [fld_po]; exact hy) hne

private theorem fld_fres_sub {P : α → α → Prop} {A : Set α} : fld (P ⥏ A) ⊆ A ∩ fld P := by
  rintro x ⟨y, ⟨⟨hx, hxy⟩, -⟩ | ⟨⟨-, hyx⟩, hx⟩⟩
  · exact ⟨hx, ⟨y, Or.inl hxy⟩⟩
  · exact ⟨hx, ⟨y, Or.inr hyx⟩⟩

/-- With `P_po` connected, a beginning of `P` is an ancestor of every member of the field. -/
private theorem first_of_beg {P : α → α → Prop} (hc : po P ∈ connex) {b : α}
    (hb : Beg b P) : rels (anc P) b = fld P := by
  obtain ⟨⟨c, hbc⟩, hbn⟩ := hb
  have hbf : b ∈ fld P := ⟨c, Or.inl hbc⟩
  ext y
  constructor
  · intro hy
    exact (fld_of_anc hy).2
  · intro hy
    show anc P b y
    by_cases e : b = y
    · rw [← e]
      exact anc_refl hbf
    · rcases cxpo hc hbf hy e with h | h
      · exact anc_of_po h
      · obtain ⟨w, -, hwb⟩ := Relation.TransGen.tail'_iff.1 (po_iff_transGen.1 h)
        exact (hbn ⟨w, hwb⟩).elim

/-- With `P_po` connected, an end of `P` (a beginning of `P̆`) follows every member of the field. -/
private theorem last_of_beg {P : α → α → Prop} (hc : po P ∈ connex) {c : α}
    (hb : Beg c P˘) : refs (anc P) c = fld P := by
  obtain ⟨⟨d, hdc⟩, hcn⟩ := hb
  have hcf : c ∈ fld P := ⟨d, Or.inr hdc⟩
  ext y
  constructor
  · intro hy
    exact (fld_of_anc hy).1
  · intro hy
    show anc P y c
    by_cases e : y = c
    · rw [e]
      exact anc_refl hcf
    · rcases cxpo hc hy hcf e with h | h
      · exact anc_of_po h
      · obtain ⟨w, hcw, -⟩ := Relation.TransGen.head'_iff.1 (po_iff_transGen.1 h)
        exact (hcn ⟨w, hcw⟩).elim

/-- A one-one `S` restricted to the field `C` of `Q ⥏ β` correlates `(S;Q) ⥏ S''β` with
`Q ⥏ β` (used for ✱202·8·81). -/
private theorem smorbar_restrict_gen {S : α → β → Prop} {Q : β → β → Prop}
    {B C : Set β} (hS : S ∈ arrow one one) (hC : C ⊆ codom S) (_hCB : C ⊆ B)
    (hf : fld (Q ⥏ B) = C) : S ↾ C ∈ smorbar ((S ⁏ Q) ⥏ S ʻʻ B) (Q ⥏ B) := by
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨⟨hx, -⟩, ⟨hy, -⟩⟩
    exact h1 x y z ⟨hx, hy⟩
  · rintro x y z ⟨⟨hy, -⟩, ⟨hz, -⟩⟩
    exact h2 x y z ⟨hy, hz⟩
  · rw [hf]
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := hC hz
      exact ⟨x, hx, hz⟩
    · rintro ⟨x, -, hz⟩
      exact hz
  · funext x y
    apply propext
    rw [semi_apply]
    constructor
    · rintro ⟨⟨⟨b, hb, hxb⟩, hxy⟩, ⟨c, hc, hyc⟩⟩
      obtain ⟨z, w, ⟨hxz, hyw⟩, hzw⟩ := (semi_apply S Q x y).1 hxy
      have e1 : b = z := h2 x b z ⟨hxb, hxz⟩
      have e2 : c = w := h2 y c w ⟨hyc, hyw⟩
      rw [← e1] at hxz hzw
      rw [← e2] at hyw hzw
      have hQB : (Q ⥏ B) b c := ⟨⟨hb, hzw⟩, hc⟩
      have hbC : b ∈ C := by rw [← hf]; exact ⟨c, Or.inl hQB⟩
      have hcC : c ∈ C := by rw [← hf]; exact ⟨b, Or.inr hQB⟩
      exact ⟨b, c, ⟨⟨hxz, hbC⟩, ⟨hyw, hcC⟩⟩, hQB⟩
    · rintro ⟨z, w, ⟨⟨hxz, hzC⟩, ⟨hyw, hwC⟩⟩, ⟨⟨hzB, hzw⟩, hwB⟩⟩
      exact ⟨⟨⟨z, hzB, hxz⟩, (semi_apply S Q x y).2 ⟨z, w, ⟨hxz, hyw⟩, hzw⟩⟩, ⟨w, hwB, hyw⟩⟩

end Helpers

/-! The counterexample to the printed forms of ✱202·54·55. -/

private def cexP : ℕ → ℕ → Prop := fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)

private def cexA : Set ℕ := {n | n = 0 ∨ n = 2}

private theorem cexA_sub : ∀ z, z ∈ cexA → z ∈ fld cexP := by
  rintro z (rfl | rfl)
  · exact ⟨1, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨1, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

private theorem cex54 : cexP ⥏ cexA ∈ connex ∧ cexA ∩ fld cexP ∉ (one : Set (Set ℕ)) ∧
    (0 : ℕ) ∈ cexA ∩ fld cexP ∧ ∀ a, a ∉ fld (cexP ⥏ cexA) := by
  have hnull : ∀ a b, ¬ (cexP ⥏ cexA) a b := by
    rintro a b ⟨⟨ha, hab⟩, hb⟩
    simp only [cexA, cexP, Set.mem_ofPred_eq] at ha hb hab
    omega
  have hfld : ∀ a, a ∉ fld (cexP ⥏ cexA) := by
    rintro a ⟨b, h | h⟩
    · exact hnull _ _ h
    · exact hnull _ _ h
  have h0 : (0 : ℕ) ∈ cexA ∩ fld cexP := ⟨Or.inl rfl, cexA_sub 0 (Or.inl rfl)⟩
  have h2 : (2 : ℕ) ∈ cexA ∩ fld cexP := ⟨Or.inr rfl, cexA_sub 2 (Or.inr rfl)⟩
  refine ⟨mem_connex.2 fun x y h => (hfld x h.1).elim, ?_, h0, hfld⟩
  intro h1
  obtain ⟨c, hc⟩ := mem_one_iff.1 h1
  have := ((hc 0).1 h0).trans ((hc 2).1 h2).symm
  omega

/-! The counterexample to the printed form of ✱205·91. -/

private def cex91P : ℕ → ℕ → Prop := fun a b => (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3)

private def cex91A : Set ℕ := {n | n = 1 ∨ n = 3}

/-!
## [✱200] Relations contained in diversity

*(Vol. 2, p. 518)*

> *Summary of* *200.
>
> Some of the propositions of this number are repetitions or immediate consequences of previous propositions, especially those of the propositions of *50 which deal with diversity. But we are chiefly concerned here with propositions which will be useful in the theory of series; this leads us to introduce propositions on \(pʻ\overleftarrow{P}ʻʻ\alpha\) and on matters connected with relation-arithmetic and other topics. It will be seen that "\(P^{2}\,\unicode{x2abd}\, J\)" (*i.e.* "\(P\) is asymmetrical") is an important hypothesis, as is also \(P_{\text{po}}\,\unicode{x2abd}\, J\), of the use of which we have already had examples in *96 and *121.
>
> The following are among the most useful propositions in this number:
>
> *200·12. \(\vdash :P\in \text{Rl}ʻJ.\supset .CʻP{\sim}\in 1\)
>
> This is the proposition which makes it impossible to define an ordinal number 1 which shall take its place among relation-numbers applicable to series.
>
> *200·35. \(\vdash :P\,\unicode{x2abd}\, J.\alpha \in 1.\supset .P\unicode{x0294f}\alpha =\dot{\Lambda}\)
>
> This is a consequence of *200·12.
>
> *200·36. \(\vdash :P^{2}\,\unicode{x2abd}\, J.\supset .P\,\unicode{x2abd}\, J\)
>
> …

**Lean reading.** `P ⊂̇ J` is `P ⪽ J` and `Rl'J` is `rl J` (`P ∈ Rl'J` is the same statement); all relations of
this number are homogeneous, `P : α → α → Prop` (the relations of relations of ✱200·42–·43 are
`(α → α → Prop) → (α → α → Prop) → Prop`, and `J` is then diversity of relations). `P⃗'x`,
`P⃖'x` are `refs P x`, `rels P x`; `p'P⃗''α` is `prodCls (Rfwd P ʻʻ A)` (the terms preceding the
whole of `α`); `P⃗_*`, `P⃗_po` are `Rfwd (anc P)`, `Rfwd (po P)`. The relation-arithmetical
signs are those of Defs/Part4: `T;P` is `T ⁏ P` (precedence 66, so PM's `T;P ∩̇ J` is written
`(T ⁏ P) ⩀ J`), `smor`, `smor̄`, `N₀r'P` (`n₀r P`), `P ⤉ Q`, `P ⇸ x`, `x ⇷ P`, `Σ'P`
(`relSigma P`), `F;P` (`F ⁏ P`), `Π'P` (`relPi P`), `F_Δ'C'P` (`sel F (fld P)`). Chains of `≡`
are conjunctions of their links, and `P, Q ∈ Rl'J` is the conjunction. In ✱200·423 `Λ ∼∈ C'P`
is read `Λ̇ ∼∈ C'P` (Vol. I erratum, p. 218), and in ✱200·381 the second `P⃗_*` lacks its
argument `'x` (as the demonstration shows).

**Status.** proved (all propositions; ✱200·381 and ✱200·423 proved (reading), see their docstrings).
-/

/-- ✱200·11. \(\vdash : P \in \text{Rl}ʻJ . \equiv . \breve{P} \in \text{Rl}ʻJ \quad[*50·23]\) -/
theorem pm200_11 {α : Type u} {P : α → α → Prop} : P ∈ rl J ↔ P˘ ∈ rl J := by
  rw [mem_rl_J, mem_rl_J]
  rfl

/-- ✱200·12. \(\vdash : P \in \text{Rl}ʻJ . \supset . CʻP {\sim} \in 1\) -/
theorem pm200_12 {α : Type u} {P : α → α → Prop} :
    P ∈ rl J → fld P ∉ (one : Set (Set α)) := by
  intro h h1
  obtain ⟨b, hb⟩ := mem_one_iff.1 h1
  obtain ⟨y, hy⟩ : b ∈ fld P := (hb b).2 rfl
  have hyf : y ∈ fld P := ⟨b, hy.symm⟩
  have e : y = b := (hb y).1 hyf
  subst e
  rcases hy with h' | h' <;> exact mem_rl_J.1 h _ h'

/-- ✱200·2. \(\vdash : T \in 1 \rightarrow 1 . \supset . T^{;}(P \dot{\cap} J) = T^{;}P \dot{\cap} J\) -/
theorem pm200_2 {α : Type u} {β : Type v} {T : α → β → Prop} {P : β → β → Prop} :
    T ∈ arrow one one → T ⁏ (P ⩀ J) = (T ⁏ P) ⩀ J := by
  intro hT
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hT
  funext x y
  apply propext
  show (T ⁏ (P ⩀ J)) x y ↔ (T ⁏ P) x y ∧ J x y
  rw [semi_apply, semi_apply]
  constructor
  · rintro ⟨z, w, ⟨hxz, hyw⟩, hzw, hne⟩
    refine ⟨⟨z, w, ⟨hxz, hyw⟩, hzw⟩, fun e => ?_⟩
    have e' : x = y := e
    subst e'
    exact hne (h2 x z w ⟨hxz, hyw⟩)
  · rintro ⟨⟨z, w, ⟨hxz, hyw⟩, hzw⟩, hne⟩
    refine ⟨z, w, ⟨hxz, hyw⟩, hzw, fun e => ?_⟩
    have e' : z = w := e
    subst e'
    exact hne (h1 x y z ⟨hxz, hyw⟩)

/-- ✱200·21. \(\vdash : T \in \text{Cls} \rightarrow 1. P \,\unicode{x2abd}\,J. \supset . T^{;}P \,\unicode{x2abd}\, J\) -/
theorem pm200_21 {α : Type u} {β : Type v} {T : α → β → Prop} {P : β → β → Prop} :
    T ∈ arrow Cls one ∧ P ⪽ J → T ⁏ P ⪽ J := by
  rintro ⟨hT, hP⟩ x y hxy e
  obtain ⟨z, w, ⟨hxz, hyw⟩, hzw⟩ := (semi_apply T P x y).1 hxy
  have e' : x = y := e
  subst e'
  have : z = w := mem_arrow_Cls_one.1 hT x z w ⟨hxz, hyw⟩
  subst this
  exact hP z z hzw rfl

/-- ✱200·211. \(\vdash : P \,\unicode{x2abd}\, J . P \,\,\text{smor}\, \,Q . \supset . Q \,\unicode{x2abd}\, J \quad[*200·21 . *151·1]\) -/
theorem pm200_211 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} :
    P ⪽ J ∧ smor P Q → Q ⪽ J := by
  rintro ⟨hP, hPQ⟩
  obtain ⟨S, ⟨hS, -⟩, rfl⟩ := smor_symm hPQ
  exact pm200_21 ⟨mem_arrow_Cls_one.2 (mem_arrow_one_one.1 hS).2, hP⟩

/-- ✱200·22. \(\vdash : P \,\unicode{x2abd}\, J . \equiv . \text{N}_{0}\text{r}ʻP \subset \text{Rl}ʻJ . \equiv . \exists ! \text{N}_{0}\text{r}ʻP \cap \text{Rl}ʻJ\) -/
theorem pm200_22 {α : Type u} {P : α → α → Prop} :
    (P ⪽ J ↔ n₀r P ⊆ rl J) ∧ (n₀r P ⊆ rl J ↔ (n₀r P ∩ rl J).Nonempty) := by
  have h1 : P ⪽ J → n₀r P ⊆ rl J := fun h Q hQ => pm200_211 ⟨h, smor_symm (mem_n₀r.1 hQ)⟩
  have h2 : n₀r P ⊆ rl J → P ⪽ J := fun h => h (self_mem_n₀r P)
  refine ⟨⟨h1, h2⟩, ⟨fun h => ⟨P, self_mem_n₀r P, h (self_mem_n₀r P)⟩, ?_⟩⟩
  rintro ⟨Q, hQ, hQJ⟩
  exact h1 (pm200_211 ⟨hQJ, mem_n₀r.1 hQ⟩)

/-- ✱200·3. \(\vdash .\dot{\Lambda} \in \text{Rl}ʻJ \quad[*25·12]\) -/
theorem pm200_3 {α : Type u} : (rNull : α → α → Prop) ∈ rl J :=
  fun x y h => (rNull_apply x y h).elim

/-- ✱200·31. \(\vdash :x\neq y.\equiv .x\downarrow y\in \text{Rl}ʻJ \quad[*55·3]\) -/
theorem pm200_31 {α : Type u} {x y : α} : x ≠ y ↔ x ↓ y ∈ rl J := by
  constructor
  · intro h z w hzw e
    obtain ⟨rfl, rfl⟩ := (couple_apply x y z w).1 hzw
    exact h e
  · intro h e
    exact h x y ((couple_apply x y x y).2 ⟨rfl, rfl⟩) e

/-- ✱200·32. \(\vdash :\alpha \uparrow \beta \,\unicode{x2abd}\, J.\equiv .\alpha \cap \beta =\Lambda \quad[*50·55]\) -/
theorem pm200_32 {α : Type u} {A B : Set α} : cross A B ⪽ J ↔ A ∩ B = Λ := by
  rw [eqΛ]
  constructor
  · rintro h x ⟨hA, hB⟩
    exact h x x ⟨hA, hB⟩ rfl
  · rintro h x y ⟨hx, hy⟩ e
    have e' : x = y := e
    subst e'
    exact h x ⟨hx, hy⟩

/-- ✱200·33. \(\vdash :P\,\unicode{x2abd}\, J.\supset .P\unicode{x0294f}\alpha \,\unicode{x2abd}\, J \quad[*35·442]\) -/
theorem pm200_33 {α : Type u} {P : α → α → Prop} {A : Set α} : P ⪽ J → P ⥏ A ⪽ J :=
  fun h x y hxy => h x y hxy.1.2

/-- ✱200·34. \(\vdash :P\unicode{x0294f}\alpha \,\unicode{x2abd}\, J.\equiv .P\upharpoonright \alpha \,\unicode{x2abd}\, J.\equiv .\alpha \upharpoonleft P\,\unicode{x2abd}\, J \quad[*50·58]\) -/
theorem pm200_34 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ⥏ A ⪽ J ↔ P ↾ A ⪽ J) ∧ (P ↾ A ⪽ J ↔ A ◁ P ⪽ J) := by
  have e1 : P ⥏ A ⪽ J ↔ ∀ x, x ∈ A → ¬ P x x :=
    ⟨fun h x hx hp => h x x ⟨⟨hx, hp⟩, hx⟩ rfl, fun h x y hxy e => by
      have e' : x = y := e
      subst e'
      exact h x hxy.2 hxy.1.2⟩
  have e2 : P ↾ A ⪽ J ↔ ∀ x, x ∈ A → ¬ P x x :=
    ⟨fun h x hx hp => h x x ⟨hp, hx⟩ rfl, fun h x y hxy e => by
      have e' : x = y := e
      subst e'
      exact h x hxy.2 hxy.1⟩
  have e3 : A ◁ P ⪽ J ↔ ∀ x, x ∈ A → ¬ P x x :=
    ⟨fun h x hx hp => h x x ⟨hx, hp⟩ rfl, fun h x y hxy e => by
      have e' : x = y := e
      subst e'
      exact h x hxy.1 hxy.2⟩
  rw [e1, e2, e3]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- ✱200·35. \(\vdash :P\,\unicode{x2abd}\, J.\alpha \in 1.\supset .P\unicode{x0294f}\alpha =\dot{\Lambda}\) -/
theorem pm200_35 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ⪽ J ∧ A ∈ one → P ⥏ A = rNull := by
  rintro ⟨hP, hA⟩
  obtain ⟨b, hb⟩ := mem_one_iff.1 hA
  rw [eqΛr]
  rintro x y ⟨⟨hx, hxy⟩, hy⟩
  exact hP x y hxy (((hb x).1 hx).trans ((hb y).1 hy).symm)

/-- ✱200·36. \(\vdash :P^{2}\,\unicode{x2abd}\, J.\supset .P\,\unicode{x2abd}\, J \quad[*50·45]\) -/
theorem pm200_36 {α : Type u} {P : α → α → Prop} : rsq P ⪽ J → P ⪽ J := by
  intro h x y hxy e
  have e' : x = y := e
  subst e'
  exact h x x ⟨x, hxy, hxy⟩ rfl

/-- ✱200·361. \(\vdash :P^{2}\,\unicode{x2abd}\, J.\supset .\overrightarrow{P}ʻx\cap ({℩}ʻx\cup \overleftarrow{P}ʻx)=\Lambda .\overleftarrow{P}ʻx\cap (\overrightarrow{P}ʻx\cup {℩}ʻx)=\Lambda\) -/
theorem pm200_361 {α : Type u} {P : α → α → Prop} {x : α} :
    rsq P ⪽ J → refs P x ∩ (ι x ∪ rels P x) = Λ ∧ rels P x ∩ (refs P x ∪ ι x) = Λ := by
  intro h
  have irr := pm200_36 h
  constructor
  · rw [eqΛ]
    rintro y ⟨h1, h2 | h2⟩
    · have e : y = x := h2
      subst e
      exact irr y y h1 rfl
    · exact h y y ⟨x, h1, h2⟩ rfl
  · rw [eqΛ]
    rintro y ⟨h1, h2 | h2⟩
    · exact h y y ⟨x, h2, h1⟩ rfl
    · have e : y = x := h2
      subst e
      exact irr y y h1 rfl

/-- ✱200·37. \(\vdash :\exists !\text{Pot}ʻP\cap \text{Rl}ʻJ.\supset .P\,\unicode{x2abd}\, J\) -/
theorem pm200_37 {α : Type u} {P : α → α → Prop} : (pot P ∩ rl J).Nonempty → P ⪽ J := by
  rintro ⟨Q, hQ, hQJ⟩ x y hxy e
  have e' : x = y := e
  subst e'
  exact hQJ x x (pot_refl hQ hxy) rfl

/-- ✱200·38. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\supset .P_{\text{po}}=P_{*}\dot{\cap} J \quad[*91·541]\) -/
theorem pm200_38 {α : Type u} {P : α → α → Prop} : po P ⪽ J → po P = anc P ⩀ J := by
  intro h
  funext x y
  apply propext
  show po P x y ↔ anc P x y ∧ J x y
  rw [anc_iff_po]
  constructor
  · intro hp
    exact ⟨Or.inr hp, h x y hp⟩
  · rintro ⟨⟨rfl, -⟩ | hp, hne⟩
    · exact (hne rfl).elim
    · exact hp

/-- ✱200·381. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\supset .\overrightarrow{P}_{\text{po}}ʻx\cap \overleftarrow{P}_{*}ʻx=\Lambda .\overleftarrow{P}_{\text{po}}ʻx\cap \overrightarrow{P}_{*}=\Lambda\)

**Status.** proved (reading): transcription error. The e-text prints the second conjunct
as `P⃖_po'x ∩ P⃗_* = Λ`, without the argument of `P⃗_*`; the demonstration (from ✱200·361 and
✱91·54) gives `P⃖_po'x ∩ P⃗_*'x = Λ`, which is stated. -/
theorem pm200_381 {α : Type u} {P : α → α → Prop} {x : α} :
    po P ⪽ J → refs (po P) x ∩ rels (anc P) x = Λ ∧ rels (po P) x ∩ refs (anc P) x = Λ := by
  intro h
  constructor
  · rw [eqΛ]
    rintro y ⟨h1, h2⟩
    exact h y y (po_anc_trans h1 h2) rfl
  · rw [eqΛ]
    rintro y ⟨h1, h2⟩
    exact h x x (po_anc_trans h1 h2) rfl

/-- ✱200·39. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.x\in CʻP.\supset .\overrightarrow{P}_{*}ʻx\cap \overleftarrow{P}_{*}ʻx=\iota ʻx\) -/
theorem pm200_39 {α : Type u} {P : α → α → Prop} {x : α} :
    po P ⪽ J ∧ x ∈ fld P → refs (anc P) x ∩ rels (anc P) x = ι x := by
  rintro ⟨h, hx⟩
  ext y
  constructor
  · rintro ⟨h1, h2⟩
    show y = x
    rcases anc_iff_po.1 h1 with ⟨rfl, -⟩ | h1'
    · rfl
    · exact (h y y (po_anc_trans h1' h2) rfl).elim
  · intro hy
    have e : y = x := hy
    subst e
    exact ⟨anc_refl hx, anc_refl hx⟩

/-- ✱200·391. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\supset .\overrightarrow{P}_{*}^{;}P\,\,\text{smor}\,\,P.\overrightarrow{P}_{*}\upharpoonright CʻP\in (\overrightarrow{P}_{*}^{;}P)\,\overline{\,\text{smor}\,}\,P\) -/
theorem pm200_391 {α : Type u} {P : α → α → Prop} :
    po P ⪽ J → smor (Rfwd (anc P) ⁏ P) P ∧
      Rfwd (anc P) ↾ fld P ∈ smorbar (Rfwd (anc P) ⁏ P) P := by
  intro h
  have hS : Rfwd (anc P) ↾ fld P ∈ smorbar (Rfwd (anc P) ⁏ P) P := by
    refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rintro A B z ⟨⟨hA, -⟩, ⟨hB, -⟩⟩
      exact (hA : A = refs (anc P) z).trans (hB : B = refs (anc P) z).symm
    · rintro A x y ⟨⟨hx, hxf⟩, ⟨hy, hyf⟩⟩
      have hx' : A = refs (anc P) x := hx
      have hy' : A = refs (anc P) y := hy
      have h1 : anc P x y := by
        have : x ∈ refs (anc P) y := by rw [← hy', hx']; exact anc_refl hxf
        exact this
      have h2 : anc P y x := by
        have : y ∈ refs (anc P) x := by rw [← hx', hy']; exact anc_refl hyf
        exact this
      rcases anc_iff_po.1 h1 with ⟨e, -⟩ | h1'
      · exact e
      · exact (h x x (po_anc_trans h1' h2) rfl).elim
    · ext x
      exact ⟨fun hx => ⟨refs (anc P) x, rfl, hx⟩, fun ⟨_, _, hx⟩ => hx⟩
    · funext X Y
      apply propext
      rw [semi_apply, semi_apply]
      constructor
      · rintro ⟨z, w, ⟨hz, hw⟩, hzw⟩
        exact ⟨z, w, ⟨⟨hz, ⟨w, Or.inl hzw⟩⟩, ⟨hw, ⟨z, Or.inr hzw⟩⟩⟩, hzw⟩
      · rintro ⟨z, w, ⟨hz, hw⟩, hzw⟩
        exact ⟨z, w, ⟨hz.1, hw.1⟩, hzw⟩
  exact ⟨⟨_, hS⟩, hS⟩

/-- ✱200·4. \(\vdash :P\unicode{x2909}Q\in \text{Rl}ʻJ.\equiv .P,Q\in \text{Rl}ʻJ.CʻP\cap CʻQ=\Lambda\) -/
theorem pm200_4 {α : Type u} {P Q : α → α → Prop} :
    P ⤉ Q ∈ rl J ↔ (P ∈ rl J ∧ Q ∈ rl J) ∧ fld P ∩ fld Q = Λ := by
  rw [mem_rl_J, mem_rl_J, mem_rl_J, eqΛ]
  constructor
  · intro h
    exact ⟨⟨fun x hx => h x (Or.inl (Or.inl hx)), fun x hx => h x (Or.inl (Or.inr hx))⟩,
      fun x ⟨h1, h2⟩ => h x (Or.inr ⟨h1, h2⟩)⟩
  · rintro ⟨⟨hP, hQ⟩, hd⟩ x ((hx | hx) | ⟨h1, h2⟩)
    · exact hP x hx
    · exact hQ x hx
    · exact hd x ⟨h1, h2⟩

/-- ✱200·41. \(\vdash :P\unicode{x21f8} x\,\unicode{x2abd}\, J.\equiv .x\unicode{x21f7}P\,\unicode{x2abd}\, J.\equiv .P\,\unicode{x2abd}\, J.x{\sim}\in CʻP \quad[*23·59.*200·32]\) -/
theorem pm200_41 {α : Type u} {P : α → α → Prop} {x : α} :
    (P ⇸ x ⪽ J ↔ x ⇷ P ⪽ J) ∧ (x ⇷ P ⪽ J ↔ P ⪽ J ∧ x ∉ fld P) := by
  have e1 : P ⇸ x ⪽ J ↔ P ⪽ J ∧ x ∉ fld P := by
    rw [rsubJ, rsubJ]
    constructor
    · intro h
      exact ⟨fun y hy => h y (Or.inl hy), fun hx => h x (Or.inr ⟨hx, rfl⟩)⟩
    · rintro ⟨h1, h2⟩ y (hy | ⟨hy, e⟩)
      · exact h1 y hy
      · subst e
        exact h2 hy
  have e2 : x ⇷ P ⪽ J ↔ P ⪽ J ∧ x ∉ fld P := by
    rw [rsubJ, rsubJ]
    constructor
    · intro h
      exact ⟨fun y hy => h y (Or.inr hy), fun hx => h x (Or.inl ⟨rfl, hx⟩)⟩
    · rintro ⟨h1, h2⟩ y (⟨e, hy⟩ | hy)
      · subst e
        exact h2 hy
      · exact h1 y hy
  rw [e1, e2]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- ✱200·42. \(\vdash :\Sigma ʻP\,\unicode{x2abd}\, J.\equiv .CʻP\subset \text{Rl}ʻJ.F^{;}P\,\unicode{x2abd}\, J\) -/
theorem pm200_42 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    relSigma P ⪽ J ↔ fld P ⊆ rl J ∧ F ⁏ P ⪽ J := by
  constructor
  · intro h
    exact ⟨fun Q hQ x y hxy => h x y (Or.inl ⟨Q, hQ, hxy⟩), fun x y hxy => h x y (Or.inr hxy)⟩
  · rintro ⟨h1, h2⟩ x y (⟨Q, hQ, hxy⟩ | hxy)
    · exact h1 hQ x y hxy
    · exact h2 x y hxy

/-- ✱200·421. \(\vdash :P\in \text{Rel}^{2}\text{excl}.P\,\unicode{x2abd}\, J.Q\in CʻP.\supset .Q=(\Sigma ʻP)\unicode{x0294f}CʻQ\) -/
theorem pm200_421 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {Q : α → α → Prop} :
    (P ∈ Rel2excl ∧ P ⪽ J) ∧ Q ∈ fld P → Q = relSigma P ⥏ fld Q := by
  rintro ⟨⟨hex, hJ⟩, hQ⟩
  have disj : ∀ R, R ∈ fld P → ∀ z, z ∈ fld Q → z ∈ fld R → R = Q := by
    intro R hR z hzQ hzR
    by_contra hne
    exact eqΛ.1 (hex R Q ⟨⟨hR, hQ⟩, hne⟩) z ⟨hzR, hzQ⟩
  funext x y
  apply propext
  show Q x y ↔ (x ∈ fld Q ∧ relSigma P x y) ∧ y ∈ fld Q
  rw [relSigma_apply]
  constructor
  · intro h
    exact ⟨⟨⟨y, Or.inl h⟩, Or.inl ⟨Q, hQ, h⟩⟩, ⟨x, Or.inr h⟩⟩
  · rintro ⟨⟨hx, ⟨R, hR, hxy⟩ | ⟨R, S, ⟨hxR, hyS⟩, hRS⟩⟩, hy⟩
    · have e := disj R hR x hx ⟨y, Or.inl hxy⟩
      subst e
      exact hxy
    · have e1 := disj R ⟨S, Or.inl hRS⟩ x hx hxR
      have e2 := disj S ⟨R, Or.inr hRS⟩ y hy hyS
      subst e1
      subst e2
      exact (hJ _ _ hRS rfl).elim

/-- ✱200·422. \(\vdash :\Sigma ʻP\,\unicode{x2abd}\, J.\supset .P\unicode{x0294f}(-\iota ʻ\dot{\Lambda} )\,\unicode{x2abd}\, J\) -/
theorem pm200_422 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    relSigma P ⪽ J → P ⥏ (ι rNull)ᶜ ⪽ J := by
  rintro h Q R ⟨⟨hQ, hQR⟩, -⟩ e
  have e' : Q = R := e
  subst e'
  have hne : ∃ x y, Q x y := by
    by_contra hn
    push_neg at hn
    exact hQ (eqΛr.2 hn)
  obtain ⟨x, y, hxy⟩ := hne
  exact h x x (Or.inr ((semi_apply F P x x).2
    ⟨Q, Q, ⟨⟨y, Or.inl hxy⟩, ⟨y, Or.inl hxy⟩⟩, hQR⟩)) rfl

/-- ✱200·423. \(\vdash \colon\ldotp P\in \text{Rel}^{2}\text{excl}.\Lambda {\sim}\in CʻP.\supset :\Sigma ʻP\,\unicode{x2abd}\, J.\equiv .P\,\unicode{x2abd}\, J.CʻP\subset \text{Rl}ʻJ\)

**Status.** proved (reading): erratum (Vol. I, p. 218): `Λ` is printed for `Λ̇` in
`Λ ∼∈ C'P`; `C'P` is a class of relations, so only the null relation is significant there, and
the hypothesis is `Λ̇ ∼∈ C'P` (`rNull ∉ fld P`). -/
theorem pm200_423 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ∧ rNull ∉ fld P → (relSigma P ⪽ J ↔ P ⪽ J ∧ fld P ⊆ rl J) := by
  rintro ⟨hex, hN⟩
  constructor
  · intro h
    refine ⟨fun Q R hQR => ?_, (pm200_42.1 h).1⟩
    have hQ : Q ∈ (ι rNull)ᶜ := fun e => hN ((e : Q = rNull) ▸ ⟨R, Or.inl hQR⟩)
    have hR : R ∈ (ι rNull)ᶜ := fun e => hN ((e : R = rNull) ▸ ⟨Q, Or.inr hQR⟩)
    exact pm200_422 h Q R ⟨⟨hQ, hQR⟩, hR⟩
  · rintro ⟨hJ, hC⟩ x y hxy e
    have e' : x = y := e
    subst e'
    rcases (relSigma_apply P x x).1 hxy with ⟨R, hR, hxx⟩ | ⟨Q, R, ⟨hxQ, hxR⟩, hQR⟩
    · exact hC hR x x hxx rfl
    · have := hex Q R ⟨⟨⟨R, Or.inl hQR⟩, ⟨Q, Or.inr hQR⟩⟩, hJ Q R hQR⟩
      exact eqΛ.1 this x ⟨hxQ, hxR⟩

/-- ✱200·43. \[\begin{align}\vdash :&P\,\unicode{x2abd}\, J.\supset .\Pi ʻP=\\ &\hat{M} \hat{N} \{M,N\in F_{\Delta }ʻCʻP:(\exists Q).(MʻQ)Q(NʻQ).M\upharpoonright \overrightarrow{P}ʻQ=N\upharpoonright \overrightarrow{P}ʻQ\}\end{align}\] -/
theorem pm200_43 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ⪽ J → relPi P = fun M N => (M ∈ sel F (fld P) ∧ N ∈ sel F (fld P)) ∧
      ∃ Q, Desc M Q (fun x => Desc N Q (fun y => Q x y)) ∧ M ↾ refs P Q = N ↾ refs P Q := by
  intro hJ
  funext M N
  apply propext
  show ((M ∈ sel F (fld P) ∧ N ∈ sel F (fld P)) ∧
    ∃ Q, Desc M Q (fun x => Desc N Q (fun y => Q x y)) ∧
      ∀ R, P R Q ∧ R ≠ Q → Desc M R (fun x => Desc N R (fun y => x = y))) ↔ _
  constructor
  · rintro ⟨hMN, Q, hQ, h⟩
    refine ⟨hMN, Q, hQ, ?_⟩
    funext x R
    apply propext
    show M x R ∧ P R Q ↔ N x R ∧ P R Q
    constructor
    · rintro ⟨hx, hRQ⟩
      obtain ⟨b, hb, c, hc, rfl⟩ := h R ⟨hRQ, hJ R Q hRQ⟩
      exact ⟨(hc x).2 ((hb x).1 hx), hRQ⟩
    · rintro ⟨hx, hRQ⟩
      obtain ⟨b, hb, c, hc, rfl⟩ := h R ⟨hRQ, hJ R Q hRQ⟩
      exact ⟨(hb x).2 ((hc x).1 hx), hRQ⟩
  · rintro ⟨⟨hM, hN⟩, Q, hQ, h⟩
    refine ⟨⟨hM, hN⟩, Q, hQ, ?_⟩
    rintro R ⟨hRQ, -⟩
    obtain ⟨⟨hM1, -⟩, hMc⟩ := mem_sel_iff.1 hM
    have hR : R ∈ codom M := by rw [hMc]; exact ⟨Q, Or.inl hRQ⟩
    obtain ⟨b, hb⟩ := hR
    have hbM : ∀ x, M x R ↔ x = b :=
      fun x => ⟨fun hx => mem_arrow_one_Cls.1 hM1 x b R ⟨hx, hb⟩, fun e => e ▸ hb⟩
    have hbN : ∀ x, N x R ↔ x = b := by
      intro x
      have e : (M x R ∧ P R Q) ↔ (N x R ∧ P R Q) := Iff.of_eq (congrFun (congrFun h x) R)
      constructor
      · intro hx
        exact (hbM x).1 (e.2 ⟨hx, hRQ⟩).1
      · intro hx
        exact (e.1 ⟨(hbM x).2 hx, hRQ⟩).1
    exact ⟨b, hbM, b, hbN, rfl⟩

/-- ✱200·5. \(\vdash :P\,\unicode{x2abd}\, J.\supset .\alpha \cap pʻ\overrightarrow{P}ʻʻ\alpha =\Lambda .\alpha \cap pʻ\overleftarrow{P}ʻʻ\alpha =\Lambda\) -/
theorem pm200_5 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ⪽ J → A ∩ prodCls (Rfwd P ʻʻ A) = Λ ∧ A ∩ prodCls (Rbwd P ʻʻ A) = Λ := by
  intro h
  constructor
  · rw [eqΛ]
    rintro x ⟨hx, hp⟩
    exact h x x (mem_prodCls_Rfwd.1 hp x hx) rfl
  · rw [eqΛ]
    rintro x ⟨hx, hp⟩
    exact h x x (mem_prodCls_Rbwd.1 hp x hx) rfl

/-- ✱200·51. \(\vdash :P\,\unicode{x2abd}\, J.\dot{\exists} !P.\supset .pʻ\overrightarrow{P}ʻʻCʻP=\Lambda .pʻ\overleftarrow{P}ʻʻCʻP=\Lambda\) -/
theorem pm200_51 {α : Type u} {P : α → α → Prop} :
    P ⪽ J ∧ rEx P → prodCls (Rfwd P ʻʻ fld P) = Λ ∧ prodCls (Rbwd P ʻʻ fld P) = Λ := by
  rintro ⟨h, x0, y0, h0⟩
  have hx0 : x0 ∈ fld P := ⟨y0, Or.inl h0⟩
  constructor
  · rw [eqΛ]
    intro z hz
    have hzx := mem_prodCls_Rfwd.1 hz x0 hx0
    exact h z z (mem_prodCls_Rfwd.1 hz z ⟨x0, Or.inl hzx⟩) rfl
  · rw [eqΛ]
    intro z hz
    have hzx := mem_prodCls_Rbwd.1 hz x0 hx0
    exact h z z (mem_prodCls_Rbwd.1 hz z ⟨x0, Or.inr hzx⟩) rfl

/-- ✱200·52. \(\vdash :P\,\unicode{x2abd}\, J.\supset .CʻP{\sim}\in \overrightarrow{P}ʻʻCʻP\) -/
theorem pm200_52 {α : Type u} {P : α → α → Prop} : P ⪽ J → fld P ∉ Rfwd P ʻʻ fld P := by
  rintro h ⟨x, hx, e⟩
  have e' : fld P = refs P x := e
  have : x ∈ refs P x := by rw [← e']; exact hx
  exact h x x this rfl

/-- ✱200·53. \(\vdash :P^{2}\,\unicode{x2abd}\, J.\supset .Pʻʻ\alpha \cap pʻ\overleftarrow{P}ʻʻ\alpha =\Lambda .\breve{P} ʻʻ\alpha \cap pʻ\overrightarrow{P}ʻʻ\alpha =\Lambda\) -/
theorem pm200_53 {α : Type u} {P : α → α → Prop} {A : Set α} :
    rsq P ⪽ J → P ʻʻ A ∩ prodCls (Rbwd P ʻʻ A) = Λ ∧ P˘ ʻʻ A ∩ prodCls (Rfwd P ʻʻ A) = Λ := by
  intro h
  constructor
  · rw [eqΛ]
    rintro x ⟨⟨y, hy, hxy⟩, hp⟩
    exact h x x ⟨y, hxy, mem_prodCls_Rbwd.1 hp y hy⟩ rfl
  · rw [eqΛ]
    rintro x ⟨⟨y, hy, hyx⟩, hp⟩
    exact h x x ⟨y, mem_prodCls_Rfwd.1 hp y hy, hyx⟩ rfl

/-- ✱200·54. \(\vdash :P\,\unicode{x2abd}\, J.\dot{\exists} !P.\supset .pʻ\overrightarrow{P}ʻʻ{CʻP\cap pʻ\overleftarrow{P}ʻʻ\alpha }=pʻ\overrightarrow{P}ʻʻpʻ\overleftarrow{P}ʻʻ\alpha\) -/
theorem pm200_54 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ⪽ J ∧ rEx P → prodCls (Rfwd P ʻʻ (fld P ∩ prodCls (Rbwd P ʻʻ A))) =
      prodCls (Rfwd P ʻʻ prodCls (Rbwd P ʻʻ A)) := by
  rintro ⟨hJ, x0, y0, h0⟩
  ext z
  rw [mem_prodCls_Rfwd, mem_prodCls_Rfwd]
  constructor
  · intro h y hy
    by_cases hyf : y ∈ fld P
    · exact h y ⟨hyf, hy⟩
    · exfalso
      have hAe : ∀ a, a ∉ A := fun a ha => hyf ⟨a, Or.inr (mem_prodCls_Rbwd.1 hy a ha)⟩
      have hall : ∀ w, w ∈ prodCls (Rbwd P ʻʻ A) :=
        fun w => mem_prodCls_Rbwd.2 fun a ha => (hAe a ha).elim
      have hz : P z x0 := h x0 ⟨⟨y0, Or.inl h0⟩, hall x0⟩
      exact hJ z z (h z ⟨⟨x0, Or.inl hz⟩, hall z⟩) rfl
  · intro h y hy
    exact h y hy.2

/-!
## [✱201] Transitive relations

*(Vol. 2, p. 525)*

> *Summary of* *201.
>
> There are two main varieties of transitive relations, namely those that are symmetrical \((P=\breve{P})\), and those that are asymmetrical \((P\dot{\cap} \breve{P} =\dot{\Lambda})\). Transitive *symmetrical* relations have the formal properties of equality: examples of such relations have occurred above, *e.g.* identity, similarity, and likeness. The propositions of the present number, however, are rather such as will be useful in connection with transitive *asymmetrical* relations, since they are intended to be applied to series.
>
> We denote the class of transitive relations by "\(\text{trans}\)"; thus \[ \text{trans}=\hat{P} (P^{2}\,\unicode{x2abd}\, P) \quad\text{Df}. \] Many propositions of this number are analogous to propositions whose numbers have the same decimal part in *200. Such are: If \(P\) is transitive, so is its converse (*201·11), and so is any relation which is like P (*201·211); \(\dot{\Lambda}\) and \(x\downarrow y\) are transitive (*201·3·31); if \(P\) is transitive, so is \(P\unicode{x0294f}\alpha\) (*201·33). The propositions *201·4—·42, which deal with the ideas of relation-arithmetic, are also analogous to *200·4—·42.
>
> …

**Lean reading.** PM's `trans` is `transR` (Defs/Part5, encoding decision 5), the class of homogeneous relations
with `P² ⊂̇ P`; `mem_transR` unfolds it. The propositions are stated for `P : α → α → Prop`
(relations of relations in ✱201·42), with the readings of ✱200: `P⃗'x` is `refs P x`, `P''α` is
`P ʻʻ A`, `p'P⃗''α` is `prodCls (Rfwd P ʻʻ A)`, `P_*`, `P_po` are `anc P`, `po P`, `Pot'P` is
`pot P`, `P(x−y)` is `itvOO P x y`, `P_1` is `P1 P` (Defs/Part5, encoding decision 3), `B⃗'P` is
`refs Beg P`, and `E!P'x`, `(P'x)P_1x` are descriptions (`EDesc P x`, `Desc P x …`, each with the
smallest scope). `Nr'P ⊂ trans` is stated for the relation-number in an arbitrary type `γ`
(`nr γ P`, typical ambiguity), `N₀r'P` is `n₀r P`. Products of hypotheses are nested to the left.
The e-text numbers the proposition between ✱201·61 and ✱201·63 "✱201·26" (it is ✱201·62,
cited so in ✱201·63); the declaration keeps the e-text's number. In ✱201·56 the e-text prints the
bracket `{α ∪ β) ∩ C'P}`, read `(α ∪ β) ∩ C'P`.

**Status.** proved (all propositions; ✱201·56 proved (reading), see its docstring).
-/

/-- ✱201·01 (Df). \(\text{trans}=\hat{P} (P^{2}\,\unicode{x2abd}\, P) \quad\text{Df}\) -/
theorem pm201_01 {α : Type u} : (transR : Set (α → α → Prop)) = {P | rsq P ⪽ P} := rfl

/-- ✱201·1. \(\vdash :P\in \text{trans}.\equiv .P^{2}\,\unicode{x2abd}\, P \quad[(*201·01)]\) -/
theorem pm201_1 {α : Type u} {P : α → α → Prop} : P ∈ transR ↔ rsq P ⪽ P := Iff.rfl

/-- ✱201·11. \(\vdash :P\in \text{trans}.\equiv .\breve{P} \in \text{trans}\) -/
theorem pm201_11 {α : Type u} {P : α → α → Prop} : P ∈ transR ↔ P˘ ∈ transR := by
  rw [mem_transR, mem_transR]
  constructor
  · rintro h x y z ⟨h1, h2⟩
    exact h z y x ⟨h2, h1⟩
  · rintro h x y z ⟨h1, h2⟩
    exact h z y x ⟨h2, h1⟩

/-- ✱201·12. \(\vdash \colon\ldotp P\in \text{trans}.\supset :P\,\unicode{x2abd}\, J.\equiv .P^{2}\,\unicode{x2abd}\, J.\equiv .P\dot{\cap} \breve{P} =\dot{\Lambda} \quad[*50·47]\) -/
theorem pm201_12 {α : Type u} {P : α → α → Prop} :
    P ∈ transR → ((P ⪽ J ↔ rsq P ⪽ J) ∧ (rsq P ⪽ J ↔ P ⩀ P˘ = rNull)) := by
  intro ht
  have e1 : P ⪽ J ↔ rsq P ⪽ J :=
    ⟨fun h x y hxy => h x y (ht x y hxy), pm200_36⟩
  have e2 : rsq P ⪽ J ↔ P ⩀ P˘ = rNull := by
    rw [eqΛr]
    constructor
    · rintro h x y ⟨h1, h2⟩
      exact h x x ⟨y, h1, h2⟩ rfl
    · rintro h x y ⟨z, h1, h2⟩ e
      have e' : x = y := e
      subst e'
      exact h x z ⟨h1, h2⟩
  exact ⟨e1, e2⟩

/-- ✱201·13. \(\vdash .\text{Rl}ʻI\subset \text{trans}\) -/
theorem pm201_13 {α : Type u} : rl (I : α → α → Prop) ⊆ transR := by
  intro P hP
  rw [mem_transR]
  rintro x y z ⟨h1, h2⟩
  have e : x = y := hP x y h1
  subst e
  exact h2

/-- ✱201·14. \(\vdash :P\in \text{trans}.xPy.\supset .\overrightarrow{P}ʻx\subset \overrightarrow{P}ʻy\) -/
theorem pm201_14 {α : Type u} {P : α → α → Prop} {x y : α} :
    P ∈ transR ∧ P x y → refs P x ⊆ refs P y := by
  rintro ⟨ht, hxy⟩ z hz
  exact mem_transR.1 ht z x y ⟨hz, hxy⟩

/-- ✱201·15. \(\vdash .R_{*}\in \text{trans} \quad[*90·17]\) -/
theorem pm201_15 {α : Type u} {R : α → α → Prop} : anc R ∈ transR :=
  mem_transR.2 fun _ _ _ h => anc_trans h.1 h.2

/-- ✱201·16. \(\vdash .R_{\text{po}}\in \text{trans} \quad[*91·56]\) -/
theorem pm201_16 {α : Type u} {R : α → α → Prop} : po R ∈ transR :=
  mem_transR.2 fun _ _ _ h => po_trans h.1 h.2

/-- ✱201·17. \(\vdash :P^{2}\,\unicode{x2abd}\, P.Q\in \text{Pot}ʻP.\supset .Q\,\unicode{x2abd}\, P\) -/
theorem pm201_17 {α : Type u} {P Q : α → α → Prop} : rsq P ⪽ P ∧ Q ∈ pot P → Q ⪽ P :=
  fun h => pot_rsub h.1 h.2

/-- ✱201·18. \(\vdash :P^{2}\,\unicode{x2abd}\, P.\supset .P_{\text{po}}=P.P_{*}=P\unicode{x228d} I\upharpoonright CʻP\) -/
theorem pm201_18 {α : Type u} {P : α → α → Prop} :
    rsq P ⪽ P → po P = P ∧ anc P = P ⊍ I ↾ fld P := by
  intro ht
  refine ⟨po_eq_of_transR ht, ?_⟩
  funext x y
  apply propext
  rw [anc_iff_of_transR ht]
  show (x = y ∧ x ∈ fld P) ∨ P x y ↔ P x y ∨ (x = y ∧ y ∈ fld P)
  constructor
  · rintro (⟨rfl, hx⟩ | h)
    · exact Or.inr ⟨rfl, hx⟩
    · exact Or.inl h
  · rintro (h | ⟨rfl, hx⟩)
    · exact Or.inr h
    · exact Or.inl ⟨rfl, hx⟩

/-- ✱201·19. \(\vdash :P\in \text{trans}.\supset .P(x-y)=\overleftarrow{P}ʻx\cap \overrightarrow{P}ʻy \quad[*201·18.(*121·01)]\) -/
theorem pm201_19 {α : Type u} {P : α → α → Prop} {x y : α} :
    P ∈ transR → itvOO P x y = rels P x ∩ refs P y := by
  intro ht
  show rels (po P) x ∩ refs (po P) y = _
  rw [po_eq_of_transR ht]

/-- ✱201·2. \(\vdash :S\in \text{Cls}\rightarrow 1.\text{ᗡ}ʻQ\subset \text{ᗡ}ʻS.\supset .(S^{;}Q)^{2}=S^{;}Q^{2}\) -/
theorem pm201_2 {α : Type u} {β : Type v} {S : α → β → Prop} {Q : β → β → Prop} :
    S ∈ arrow Cls one ∧ codom Q ⊆ codom S → rsq (S ⁏ Q) = S ⁏ rsq Q := by
  rintro ⟨hS, hQ⟩
  have mo := mem_arrow_Cls_one.1 hS
  funext x z
  apply propext
  show (∃ y, (S ⁏ Q) x y ∧ (S ⁏ Q) y z) ↔ (S ⁏ rsq Q) x z
  rw [semi_apply]
  constructor
  · rintro ⟨y, h1, h2⟩
    obtain ⟨a, b, ⟨hxa, hyb⟩, hab⟩ := (semi_apply S Q x y).1 h1
    obtain ⟨c, d, ⟨hyc, hzd⟩, hcd⟩ := (semi_apply S Q y z).1 h2
    have e : b = c := mo y b c ⟨hyb, hyc⟩
    rw [← e] at hcd
    exact ⟨a, d, ⟨hxa, hzd⟩, b, hab, hcd⟩
  · rintro ⟨a, d, ⟨hxa, hzd⟩, b, hab, hbd⟩
    obtain ⟨y, hyb⟩ := hQ ⟨a, hab⟩
    exact ⟨y, (semi_apply S Q x y).2 ⟨a, b, ⟨hxa, hyb⟩, hab⟩,
      (semi_apply S Q y z).2 ⟨b, d, ⟨hyb, hzd⟩, hbd⟩⟩

/-- ✱201·201. \[\begin{align}&\vdash :S\in \text{Cls}\rightarrow 1.\text{D}ʻQ\subset \text{ᗡ}ʻS.\supset .(S^{;}Q)^{2}=S^{;}Q^{2}\\ &[\text{Proof as in *201·2}]\end{align}\] -/
theorem pm201_201 {α : Type u} {β : Type v} {S : α → β → Prop} {Q : β → β → Prop} :
    S ∈ arrow Cls one ∧ dom Q ⊆ codom S → rsq (S ⁏ Q) = S ⁏ rsq Q := by
  rintro ⟨hS, hQ⟩
  have mo := mem_arrow_Cls_one.1 hS
  funext x z
  apply propext
  show (∃ y, (S ⁏ Q) x y ∧ (S ⁏ Q) y z) ↔ (S ⁏ rsq Q) x z
  rw [semi_apply]
  constructor
  · rintro ⟨y, h1, h2⟩
    obtain ⟨a, b, ⟨hxa, hyb⟩, hab⟩ := (semi_apply S Q x y).1 h1
    obtain ⟨c, d, ⟨hyc, hzd⟩, hcd⟩ := (semi_apply S Q y z).1 h2
    have e : b = c := mo y b c ⟨hyb, hyc⟩
    rw [← e] at hcd
    exact ⟨a, d, ⟨hxa, hzd⟩, b, hab, hcd⟩
  · rintro ⟨a, d, ⟨hxa, hzd⟩, b, hab, hbd⟩
    obtain ⟨y, hyb⟩ := hQ ⟨d, hbd⟩
    exact ⟨y, (semi_apply S Q x y).2 ⟨a, b, ⟨hxa, hyb⟩, hab⟩,
      (semi_apply S Q y z).2 ⟨b, d, ⟨hyb, hzd⟩, hbd⟩⟩

/-- ✱201·21. \(\vdash :S\in \text{Cls}\rightarrow 1.Q\in \text{trans}.\supset .S^{;}Q\in \text{trans}\) -/
theorem pm201_21 {α : Type u} {β : Type v} {S : α → β → Prop} {Q : β → β → Prop} :
    S ∈ arrow Cls one ∧ Q ∈ transR → S ⁏ Q ∈ transR := by
  rintro ⟨hS, hQ⟩
  have mo := mem_arrow_Cls_one.1 hS
  rw [mem_transR]
  rintro x y z ⟨h1, h2⟩
  obtain ⟨a, b, ⟨hxa, hyb⟩, hab⟩ := (semi_apply S Q x y).1 h1
  obtain ⟨c, d, ⟨hyc, hzd⟩, hcd⟩ := (semi_apply S Q y z).1 h2
  have e : b = c := mo y b c ⟨hyb, hyc⟩
  rw [← e] at hcd
  exact (semi_apply S Q x z).2 ⟨a, d, ⟨hxa, hzd⟩, mem_transR.1 hQ a b d ⟨hab, hcd⟩⟩

/-- ✱201·211. \(\vdash :P\in \text{trans}.Q\,\,\text{smor}\,\,P.\supset .Q\in \text{trans} \quad[*201·21.*151·1]\) -/
theorem pm201_211 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} :
    P ∈ transR ∧ smor Q P → Q ∈ transR := by
  rintro ⟨hP, S, ⟨hS, -⟩, rfl⟩
  exact pm201_21 ⟨mem_arrow_Cls_one.2 (mem_arrow_one_one.1 hS).2, hP⟩

/-- ✱201·212. \(\vdash :P\in \text{trans}.\supset .\text{Nr}ʻP\subset \text{trans} \quad[*201·211]\) -/
theorem pm201_212 {α : Type u} {γ : Type w} {P : α → α → Prop} :
    P ∈ transR → nr γ P ⊆ transR :=
  fun h _ hQ => pm201_211 ⟨h, hQ⟩

/-- ✱201·22. \[\begin{align}&\vdash :P\in \text{trans}.\equiv .\text{N}_{0}\text{r}ʻP\subset \text{trans}.\equiv .\exists !\text{N}_{0}\text{r}ʻP\cap \text{trans}\\ &[\text{Proof as in *200*22}]\end{align}\] -/
theorem pm201_22 {α : Type u} {P : α → α → Prop} :
    (P ∈ transR ↔ n₀r P ⊆ transR) ∧ (n₀r P ⊆ transR ↔ (n₀r P ∩ transR).Nonempty) := by
  have h1 : P ∈ transR → n₀r P ⊆ transR := fun h Q hQ => pm201_211 ⟨h, mem_n₀r.1 hQ⟩
  refine ⟨⟨h1, fun h => h (self_mem_n₀r P)⟩,
    ⟨fun h => ⟨P, self_mem_n₀r P, h (self_mem_n₀r P)⟩, ?_⟩⟩
  rintro ⟨Q, hQ, hQt⟩
  exact h1 (pm201_211 ⟨hQt, smor_symm (mem_n₀r.1 hQ)⟩)

/-- ✱201·3. \(\vdash .\dot{\Lambda} \in \text{trans}\) -/
theorem pm201_3 {α : Type u} : (rNull : α → α → Prop) ∈ transR :=
  mem_transR.2 fun x y _ h => (rNull_apply x y h.1).elim

/-- ✱201·31. \(\vdash .x\downarrow y\in \text{trans}\) -/
theorem pm201_31 {α : Type u} {x y : α} : x ↓ y ∈ transR := by
  rw [mem_transR]
  rintro a b c ⟨h1, h2⟩
  rw [couple_apply] at h1 h2 ⊢
  exact ⟨h1.1, h2.2⟩

/-- ✱201·32. \(\vdash .\alpha \uparrow \beta \in \text{trans}\) -/
theorem pm201_32 {α : Type u} {A B : Set α} : cross A B ∈ transR := by
  rw [mem_transR]
  rintro a b c ⟨h1, h2⟩
  exact ⟨h1.1, h2.2⟩

/-- ✱201·33. \(\vdash :P\in \text{trans}.\supset .P\unicode{x0294f}\alpha \in \text{trans}\) -/
theorem pm201_33 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → P ⥏ A ∈ transR := by
  intro ht
  rw [mem_transR]
  rintro a b c ⟨⟨⟨ha, hab⟩, hb⟩, ⟨⟨-, hbc⟩, hc⟩⟩
  exact ⟨⟨ha, mem_transR.1 ht a b c ⟨hab, hbc⟩⟩, hc⟩

/-- ✱201·4. \(\vdash :P,Q\in \text{trans}.CʻP\cap CʻQ=\Lambda .\supset .P\unicode{x2909}Q\in \text{trans}\) -/
theorem pm201_4 {α : Type u} {P Q : α → α → Prop} :
    (P ∈ transR ∧ Q ∈ transR) ∧ fld P ∩ fld Q = Λ → P ⤉ Q ∈ transR := by
  rintro ⟨⟨hP, hQ⟩, hd⟩
  have tP := mem_transR.1 hP
  have tQ := mem_transR.1 hQ
  have d := eqΛ.1 hd
  rw [mem_transR]
  rintro x y z ⟨((h1 | h1) | ⟨hx, hy⟩), ((h2 | h2) | ⟨hy', hz⟩)⟩
  · exact Or.inl (Or.inl (tP x y z ⟨h1, h2⟩))
  · exact (d y ⟨⟨x, Or.inr h1⟩, ⟨z, Or.inl h2⟩⟩).elim
  · exact Or.inr ⟨⟨y, Or.inl h1⟩, hz⟩
  · exact (d y ⟨⟨z, Or.inl h2⟩, ⟨x, Or.inr h1⟩⟩).elim
  · exact Or.inl (Or.inr (tQ x y z ⟨h1, h2⟩))
  · exact (d y ⟨hy', ⟨x, Or.inr h1⟩⟩).elim
  · exact (d y ⟨⟨z, Or.inl h2⟩, hy⟩).elim
  · exact Or.inr ⟨hx, ⟨y, Or.inr h2⟩⟩
  · exact (d y ⟨hy', hy⟩).elim

/-- ✱201·401. \(\vdash \colon\ldotp CʻP\cap CʻQ=\Lambda .\supset :P\unicode{x2909}Q\in \text{trans}.\equiv .P,Q\in \text{trans}\) -/
theorem pm201_401 {α : Type u} {P Q : α → α → Prop} :
    fld P ∩ fld Q = Λ → (P ⤉ Q ∈ transR ↔ P ∈ transR ∧ Q ∈ transR) := by
  intro hd
  have d := eqΛ.1 hd
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => pm201_4 ⟨h, hd⟩⟩
  · rw [mem_transR]
    rintro x y z ⟨h1, h2⟩
    rcases mem_transR.1 h x y z ⟨Or.inl (Or.inl h1), Or.inl (Or.inl h2)⟩ with
      ((h | h) | ⟨-, hz⟩)
    · exact h
    · exact (d x ⟨⟨y, Or.inl h1⟩, ⟨z, Or.inl h⟩⟩).elim
    · exact (d z ⟨⟨y, Or.inr h2⟩, hz⟩).elim
  · rw [mem_transR]
    rintro x y z ⟨h1, h2⟩
    rcases mem_transR.1 h x y z ⟨Or.inl (Or.inr h1), Or.inl (Or.inr h2)⟩ with
      ((h | h) | ⟨hx, -⟩)
    · exact (d x ⟨⟨z, Or.inl h⟩, ⟨y, Or.inl h1⟩⟩).elim
    · exact h
    · exact (d x ⟨hx, ⟨y, Or.inl h1⟩⟩).elim

/-- ✱201·41. \(\vdash :.x{\sim}\in CʻP.\supset :P\in \text{trans}.\equiv .P\unicode{x21f8} x\in \text{trans}.\equiv .x\unicode{x21f7}P\in \text{trans}\) -/
theorem pm201_41 {α : Type u} {P : α → α → Prop} {x : α} :
    x ∉ fld P → ((P ∈ transR ↔ P ⇸ x ∈ transR) ∧ (P ⇸ x ∈ transR ↔ x ⇷ P ∈ transR)) := by
  intro hx
  have e1 : P ∈ transR ↔ P ⇸ x ∈ transR := by
    rw [mem_transR, mem_transR]
    constructor
    · rintro h a b c ⟨h1 | ⟨ha, rfl⟩, h2 | ⟨hb, rfl⟩⟩
      · exact Or.inl (h a b c ⟨h1, h2⟩)
      · exact Or.inr ⟨⟨b, Or.inl h1⟩, rfl⟩
      · exact (hx ⟨c, Or.inl h2⟩).elim
      · exact (hx hb).elim
    · rintro h a b c ⟨h1, h2⟩
      rcases h a b c ⟨Or.inl h1, Or.inl h2⟩ with h3 | ⟨-, rfl⟩
      · exact h3
      · exact (hx ⟨b, Or.inr h2⟩).elim
  have e2 : P ∈ transR ↔ x ⇷ P ∈ transR := by
    rw [mem_transR, mem_transR]
    constructor
    · rintro h a b c ⟨⟨rfl, hb⟩ | h1, ⟨rfl, hc⟩ | h2⟩
      · exact (hx hb).elim
      · exact Or.inl ⟨rfl, ⟨b, Or.inr h2⟩⟩
      · exact (hx ⟨a, Or.inr h1⟩).elim
      · exact Or.inr (h a b c ⟨h1, h2⟩)
    · rintro h a b c ⟨h1, h2⟩
      rcases h a b c ⟨Or.inr h1, Or.inr h2⟩ with ⟨rfl, -⟩ | h3
      · exact (hx ⟨b, Or.inl h1⟩).elim
      · exact h3
  exact ⟨e1, e1.symm.trans e2⟩

/-- ✱201·411. \(\vdash :z\neq x.z\neq y.\supset .x\downarrow y\unicode{x21f8} z\in \text{trans} \quad[*201·41·31]\) -/
theorem pm201_411 {α : Type u} {x y z : α} : z ≠ x ∧ z ≠ y → (x ↓ y) ⇸ z ∈ transR := by
  rintro ⟨hx, hy⟩
  have hz : z ∉ fld (x ↓ y) := by
    rintro ⟨w, h | h⟩
    · exact hx ((couple_apply x y z w).1 h).1
    · exact hy ((couple_apply x y w z).1 h).2
  exact ((pm201_41 hz).1).1 pm201_31

/-- ✱201·42. \(\vdash :P\in \text{trans}\cap \text{Rel}^{2}\text{excl}.CʻP\subset \text{trans}.\supset .\Sigma ʻP\in \text{trans}\) -/
theorem pm201_42 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ transR ∩ Rel2excl ∧ fld P ⊆ transR → relSigma P ∈ transR := by
  rintro ⟨⟨ht, hex⟩, hC⟩
  have tr := mem_transR.1 ht
  have disj : ∀ Q R z, Q ∈ fld P → R ∈ fld P → z ∈ fld Q → z ∈ fld R → Q = R := by
    intro Q R z hQ hR hzQ hzR
    by_contra hne
    exact eqΛ.1 (hex Q R ⟨⟨hQ, hR⟩, hne⟩) z ⟨hzQ, hzR⟩
  rw [mem_transR]
  rintro x y z ⟨h1, h2⟩
  rw [relSigma_apply] at h1 h2 ⊢
  rcases h1 with ⟨Q, hQ, hxy⟩ | ⟨Q1, Q2, ⟨hx, hy⟩, h12⟩ <;>
    rcases h2 with ⟨R, hR, hyz⟩ | ⟨R1, R2, ⟨hy', hz⟩, h12'⟩
  · have e := disj Q R y hQ hR ⟨x, Or.inr hxy⟩ ⟨z, Or.inl hyz⟩
    rw [← e] at hyz
    exact Or.inl ⟨Q, hQ, mem_transR.1 (hC hQ) x y z ⟨hxy, hyz⟩⟩
  · have e := disj Q R1 y hQ ⟨R2, Or.inl h12'⟩ ⟨x, Or.inr hxy⟩ hy'
    rw [← e] at h12'
    exact Or.inr ⟨Q, R2, ⟨⟨y, Or.inl hxy⟩, hz⟩, h12'⟩
  · have e := disj Q2 R y ⟨Q1, Or.inr h12⟩ hR hy ⟨z, Or.inl hyz⟩
    rw [← e] at hyz
    exact Or.inr ⟨Q1, Q2, ⟨hx, ⟨y, Or.inr hyz⟩⟩, h12⟩
  · have e := disj Q2 R1 y ⟨Q1, Or.inr h12⟩ ⟨R2, Or.inl h12'⟩ hy hy'
    rw [← e] at h12'
    exact Or.inr ⟨Q1, R2, ⟨hx, hz⟩, tr _ _ _ ⟨h12, h12'⟩⟩

/-- ✱201·5. \(\vdash :P\in \text{trans}.\supset .PʻʻPʻʻ\alpha \subset Pʻʻ\alpha \quad[*37·33·201]\) -/
theorem pm201_5 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → P ʻʻ P ʻʻ A ⊆ P ʻʻ A := by
  rintro ht x ⟨y, ⟨a, ha, hya⟩, hxy⟩
  exact ⟨a, ha, mem_transR.1 ht x y a ⟨hxy, hya⟩⟩

/-- ✱201·501. \(\vdash :P\in \text{trans}.\supset .Pʻʻ\overrightarrow{P}ʻx\subset \overrightarrow{P}ʻx \quad[*53·301.*201·5]\) -/
theorem pm201_501 {α : Type u} {P : α → α → Prop} {x : α} :
    P ∈ transR → P ʻʻ refs P x ⊆ refs P x := by
  rintro ht z ⟨y, hy, hzy⟩
  exact mem_transR.1 ht z y x ⟨hzy, hy⟩

/-- ✱201·51. \(\vdash :P\in \text{trans}.\supset .Pʻʻpʻ\overrightarrow{P}ʻʻ\alpha \subset pʻ\overrightarrow{P}ʻʻ\alpha\) -/
theorem pm201_51 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → P ʻʻ prodCls (Rfwd P ʻʻ A) ⊆ prodCls (Rfwd P ʻʻ A) := by
  rintro ht z ⟨y, hy, hzy⟩
  rw [mem_prodCls_Rfwd] at hy ⊢
  intro a ha
  exact mem_transR.1 ht z y a ⟨hzy, hy a ha⟩

/-- ✱201·52. \(\vdash :P\in \text{trans}.\supset .P_{*}ʻʻ\alpha = Pʻʻ\alpha \cup (\alpha \cap CʻP) \quad[*91·543.*201·18]\) -/
theorem pm201_52 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → anc P ʻʻ A = P ʻʻ A ∪ (A ∩ fld P) := by
  intro ht
  ext z
  constructor
  · rintro ⟨a, ha, hza⟩
    rcases (anc_iff_of_transR ht).1 hza with ⟨e, hz⟩ | h
    · right
      rw [e] at hz ⊢
      exact ⟨ha, hz⟩
    · exact Or.inl ⟨a, ha, h⟩
  · rintro (⟨a, ha, h⟩ | ⟨ha, hz⟩)
    · exact ⟨a, ha, (anc_iff_of_transR ht).2 (Or.inr h)⟩
    · exact ⟨z, ha, (anc_iff_of_transR ht).2 (Or.inl ⟨rfl, hz⟩)⟩

/-- ✱201·521. \(\vdash :P\in \text{trans}.x\in CʻP.\supset .\overrightarrow{P}_{*}ʻx = \overrightarrow{P}ʻx\cup \iota ʻx \quad[*201·52.*53·301]\) -/
theorem pm201_521 {α : Type u} {P : α → α → Prop} {x : α} :
    P ∈ transR ∧ x ∈ fld P → refs (anc P) x = refs P x ∪ ι x := by
  rintro ⟨ht, hx⟩
  ext z
  show anc P z x ↔ P z x ∨ z = x
  rw [anc_iff_of_transR ht]
  constructor
  · rintro (⟨e, -⟩ | h)
    · exact Or.inr e
    · exact Or.inl h
  · rintro (h | e)
    · exact Or.inr h
    · exact Or.inl ⟨e, by rw [e]; exact hx⟩

/-- ✱201·53. \(\vdash :P\in \text{trans}.\supset .P_{*}ʻʻPʻʻ\alpha = Pʻʻ\alpha \quad[*201·5·52.*37·265]\) -/
theorem pm201_53 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → anc P ʻʻ P ʻʻ A = P ʻʻ A := by
  intro ht
  rw [pm201_52 ht]
  apply Set.Subset.antisymm
  · rintro x (hx | ⟨hx, -⟩)
    · exact pm201_5 ht hx
    · exact hx
  · intro x hx
    obtain ⟨a, -, hxa⟩ := id hx
    exact Or.inr ⟨hx, ⟨a, Or.inl hxa⟩⟩

/-- ✱201·54. \(\vdash :P\in \text{trans}.\supset .P_{*}ʻʻpʻ\overrightarrow{P}ʻʻ\alpha \subset pʻ\overrightarrow{P}ʻʻ\alpha \quad[*201·51·52]\) -/
theorem pm201_54 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → anc P ʻʻ prodCls (Rfwd P ʻʻ A) ⊆ prodCls (Rfwd P ʻʻ A) := by
  rintro ht z ⟨y, hy, hzy⟩
  rcases (anc_iff_of_transR ht).1 hzy with ⟨e, -⟩ | h
  · rw [e]
    exact hy
  · exact pm201_51 ht ⟨y, hy, h⟩

/-- ✱201·55. \(\vdash :P\in \text{trans}.\supset .Pʻʻ(\alpha \cup Pʻʻ\alpha ) = Pʻʻ\alpha\) -/
theorem pm201_55 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → P ʻʻ (A ∪ P ʻʻ A) = P ʻʻ A := by
  intro ht
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy | hy, hxy⟩
    · exact ⟨y, hy, hxy⟩
    · exact pm201_5 ht ⟨y, hy, hxy⟩
  · rintro x ⟨y, hy, hxy⟩
    exact ⟨y, Or.inl hy, hxy⟩

/-- ✱201·56. \[\begin{align}&\vdash :P\in \text{trans}.\beta \subset Pʻʻ\alpha .\supset .\\ &Pʻʻ(\alpha \cup \beta ) = Pʻʻ\alpha .pʻ\overleftarrow{P}ʻʻ{\alpha \cup \beta )\cap CʻP} = pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\end{align}\]

**Status.** proved (reading): transcription error. The e-text prints the second class as
`p'P⃖''{α ∪ β) ∩ C'P}` with unbalanced brackets; the only significant reading is
`p'P⃖''{(α ∪ β) ∩ C'P}`, which is stated. -/
theorem pm201_56 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    P ∈ transR ∧ B ⊆ P ʻʻ A → P ʻʻ (A ∪ B) = P ʻʻ A ∧
      prodCls (Rbwd P ʻʻ ((A ∪ B) ∩ fld P)) = prodCls (Rbwd P ʻʻ (A ∩ fld P)) := by
  rintro ⟨ht, hB⟩
  have tr := mem_transR.1 ht
  constructor
  · apply Set.Subset.antisymm
    · rintro x ⟨y, hy | hy, hxy⟩
      · exact ⟨y, hy, hxy⟩
      · obtain ⟨a, ha, hya⟩ := hB hy
        exact ⟨a, ha, tr x y a ⟨hxy, hya⟩⟩
    · rintro x ⟨y, hy, hxy⟩
      exact ⟨y, Or.inl hy, hxy⟩
  · ext z
    rw [mem_prodCls_Rbwd, mem_prodCls_Rbwd]
    constructor
    · rintro h y ⟨hy, hyf⟩
      exact h y ⟨Or.inl hy, hyf⟩
    · rintro h y ⟨hy | hy, hyf⟩
      · exact h y ⟨hy, hyf⟩
      · obtain ⟨a, ha, hya⟩ := hB hy
        exact tr y a z ⟨hya, h a ⟨ha, ⟨y, Or.inr hya⟩⟩⟩

/-- ✱201·6. \(\vdash :P\in \text{trans}.{\sim}(xPx).{\sim}(yPy).xP_{1}y.\supset .x(P\dot{-} P^{2})y\) -/
theorem pm201_6 {α : Type u} {P : α → α → Prop} {x y : α} :
    ((P ∈ transR ∧ ¬P x x) ∧ ¬P y y) ∧ P1 P x y → (P ∸ rsq P) x y := by
  rintro ⟨⟨⟨ht, hx⟩, hy⟩, hP1⟩
  have tr := mem_transR.1 ht
  have mem : ∀ z, z ∈ itvCC P x y ↔
      ((x = z ∧ x ∈ fld P) ∨ P x z) ∧ ((z = y ∧ z ∈ fld P) ∨ P z y) :=
    fun z => and_congr (anc_iff_of_transR ht) (anc_iff_of_transR ht)
  obtain ⟨u, v, huv, h⟩ := P1_iff.1 hP1
  clear hP1
  have hu : u ∈ itvCC P x y := h ▸ Or.inl rfl
  have hv : v ∈ itvCC P x y := h ▸ Or.inr rfl
  have hxy : P x y := by
    by_contra hn
    have key : ∀ z, z ∈ itvCC P x y → z = x := by
      intro z hz
      rcases (mem z).1 hz with ⟨⟨rfl, -⟩ | h1, ⟨rfl, -⟩ | h2⟩
      · rfl
      · rfl
      · exact absurd h1 hn
      · exact absurd (tr x z y ⟨h1, h2⟩) hn
    exact huv ((key u hu).trans (key v hv).symm)
  refine ⟨hxy, ?_⟩
  rintro ⟨z, hxz, hzy⟩
  have hx' : x ∈ itvCC P x y := (mem x).2 ⟨Or.inl ⟨rfl, ⟨y, Or.inl hxy⟩⟩, Or.inr hxy⟩
  have hy' : y ∈ itvCC P x y := (mem y).2 ⟨Or.inr hxy, Or.inl ⟨rfl, ⟨x, Or.inr hxy⟩⟩⟩
  have hz' : z ∈ itvCC P x y := (mem z).2 ⟨Or.inr hxz, Or.inr hzy⟩
  have hxz' : x ≠ z := fun e => hx (e ▸ hxz)
  have hzy' : z ≠ y := fun e => hy (e ▸ hzy)
  have hxy' : x ≠ y := fun e => hx (e ▸ hxy)
  rw [h] at hx' hy' hz'
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> rcases hz' with rfl | rfl <;>
    simp_all

/-- ✱201·61. \(\vdash :P\in \text{trans}.\supset .P\dot{-} P^{2}\,\unicode{x2abd}\, P_{1}\) -/
theorem pm201_61 {α : Type u} {P : α → α → Prop} : P ∈ transR → P ∸ rsq P ⪽ P1 P := by
  rintro ht x y ⟨hxy, hn⟩
  have mem : ∀ z, z ∈ itvCC P x y ↔
      ((x = z ∧ x ∈ fld P) ∨ P x z) ∧ ((z = y ∧ z ∈ fld P) ∨ P z y) :=
    fun z => and_congr (anc_iff_of_transR ht) (anc_iff_of_transR ht)
  have hxy' : x ≠ y := by
    intro e
    subst e
    exact hn ⟨x, hxy, hxy⟩
  rw [P1_iff]
  refine ⟨x, y, hxy', Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · rcases (mem z).1 hz with ⟨⟨e, -⟩ | h1, ⟨e', -⟩ | h2⟩
    · exact Or.inl e.symm
    · exact Or.inl e.symm
    · exact Or.inr e'
    · exact absurd ⟨z, h1, h2⟩ hn
  · rcases hz with e | e
    · rw [show z = x from e]
      exact (mem x).2 ⟨Or.inl ⟨rfl, ⟨y, Or.inl hxy⟩⟩, Or.inr hxy⟩
    · rw [show z = y from e]
      exact (mem y).2 ⟨Or.inr hxy, Or.inl ⟨rfl, ⟨x, Or.inr hxy⟩⟩⟩

/-- ✱201·26. \[\begin{align}&\vdash \colon\ldotp P\in \text{trans}.{\sim}(xPx).{\sim}(yPy).\supset :xP_{1}y.\equiv .x(P\dot{-} P^{2})y\\ &[*201·6·61]\end{align}\]

**Status.** proved: the e-text numbers this proposition ✱201·26; it stands between
✱201·61 and ✱201·63 and is cited as ✱201·62 in ✱201·63. -/
theorem pm201_26 {α : Type u} {P : α → α → Prop} {x y : α} :
    (P ∈ transR ∧ ¬P x x) ∧ ¬P y y → (P1 P x y ↔ (P ∸ rsq P) x y) :=
  fun h => ⟨fun h1 => pm201_6 ⟨h, h1⟩, fun h2 => pm201_61 h.1.1 x y h2⟩

/-- ✱201·63. \(\vdash :P\in \text{trans}\cap \text{Rl}ʻJ.\supset .P_{1}=P\dot{-} P^{2} \quad[*201·62]\) -/
theorem pm201_63 {α : Type u} {P : α → α → Prop} : P ∈ transR ∩ rl J → P1 P = P ∸ rsq P := by
  intro h
  funext x y
  exact propext (P1_iff_of_transR h.1 h.2)

/-- ✱201·64. \(\vdash \colon\ldotp P\in \text{trans}.\supset :P\dot{-} P^{2}=\dot{\Lambda} .\equiv .P^{2}=P\) -/
theorem pm201_64 {α : Type u} {P : α → α → Prop} :
    P ∈ transR → (P ∸ rsq P = rNull ↔ rsq P = P) := by
  intro ht
  rw [eqΛr]
  constructor
  · intro h
    funext x y
    apply propext
    exact ⟨fun h2 => ht x y h2, fun h1 => by
      by_contra hn
      exact h x y ⟨h1, hn⟩⟩
  · rintro h x y ⟨h1, h2⟩
    have : rsq P x y := by rw [h]; exact h1
    exact h2 this

/-- ✱201·65. \(\vdash \colon\ldotp P\in \text{trans}\cap \text{Rl}ʻJ.\supset :P_{1}=\dot{\Lambda} .\equiv .P^{2}=P \quad [*201·64·63]\) -/
theorem pm201_65 {α : Type u} {P : α → α → Prop} :
    P ∈ transR ∩ rl J → (P1 P = rNull ↔ rsq P = P) := by
  intro h
  rw [pm201_63 h]
  exact pm201_64 h.1

/-- ✱201·66. \(\vdash :P\in \text{trans}.\text{E}!Pʻx.Pʻx\neq x.\supset .(Pʻx)P_{1}x\) -/
theorem pm201_66 {α : Type u} {P : α → α → Prop} {x : α} :
    (P ∈ transR ∧ EDesc P x) ∧ Desc P x (fun v => v ≠ x) → Desc P x (fun v => P1 P v x) := by
  rintro ⟨⟨ht, -⟩, b, hb, hne⟩
  refine ⟨b, hb, ?_⟩
  have hbx : P b x := (hb b).2 rfl
  show P1 P b x
  rw [P1_iff]
  refine ⟨b, x, hne, Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · rcases (anc_iff_of_transR ht).1 hz.2 with ⟨e, -⟩ | h2
    · exact Or.inr e
    · exact Or.inl ((hb z).1 h2)
  · rcases hz with e | e
    · rw [show z = b from e]
      exact ⟨anc_refl ⟨x, Or.inl hbx⟩, anc_of_po (po_of hbx)⟩
    · rw [show z = x from e]
      exact ⟨anc_of_po (po_of hbx), anc_refl ⟨b, Or.inr hbx⟩⟩

/-- ✱201·661. \(\vdash :P\in \text{trans}.\text{ᗡ}ʻP\in 1.\exists !\text{D}ʻP-\text{ᗡ}ʻP.\supset .\text{ᗡ}ʻP\subset \text{ᗡ}ʻP_{1}\) -/
theorem pm201_661 {α : Type u} {P : α → α → Prop} :
    (P ∈ transR ∧ codom P ∈ one) ∧ (dom P \ codom P).Nonempty → codom P ⊆ codom (P1 P) := by
  rintro ⟨⟨ht, h1⟩, x, ⟨y, hxy⟩, hx⟩ z hz
  obtain ⟨c, hc⟩ := mem_one_iff.1 h1
  have hyc : y = c := (hc y).1 ⟨x, hxy⟩
  have hzc : z = c := (hc z).1 hz
  have hxz : P x z := by rw [hzc, ← hyc]; exact hxy
  have hne : x ≠ z := fun e => hx (by rw [e]; exact hz)
  refine ⟨x, ?_⟩
  rw [P1_iff]
  refine ⟨x, z, hne, Set.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · rcases (anc_iff_of_transR ht).1 hw.1 with ⟨e, -⟩ | h
    · exact Or.inl e.symm
    · exact Or.inr (((hc w).1 ⟨x, h⟩).trans hzc.symm)
  · rcases hw with e | e
    · rw [show w = x from e]
      exact ⟨anc_refl ⟨z, Or.inl hxz⟩, anc_of_po (po_of hxz)⟩
    · rw [show w = z from e]
      exact ⟨anc_of_po (po_of hxz), anc_refl ⟨x, Or.inr hxz⟩⟩

/-- ✱201·662. \[\begin{align}&\vdash :P\in \text{trans}.\exists !\overrightarrow{B}ʻP.\exists !\text{ᗡ}ʻP-\text{ᗡ}ʻP_{1}.\supset .\text{ᗡ}ʻP{\sim}\in 1\\ &[*201·661.\text{Transp}]\end{align}\] -/
theorem pm201_662 {α : Type u} {P : α → α → Prop} :
    (P ∈ transR ∧ (refs Beg P).Nonempty) ∧ (codom P \ codom (P1 P)).Nonempty →
      codom P ∉ (one : Set (Set α)) := by
  rintro ⟨⟨ht, b, hb⟩, w, hw1, hw2⟩ h1
  exact hw2 (pm201_661 ⟨⟨ht, h1⟩, b, hb⟩ hw1)

/-!
## [✱202] Connected relations

*(Vol. 2, p. 533)*

> *Summary of* *202.
>
> A relation is said to be *connected* when either it or its converse holds between any two different members of its field, *i.e.* when, if \(x\), \(y \in CʻP . x \neq y\), we have \(xPy. \lor . yPx\). Thus the field of a connected relation consists of a single family, unless the relation is null, in which case it has no families. Conversely, a relation which has one family or none is connected. Connection is necessary, in addition to transitiveness and asymmetry, in order that a relation may generate a single series. If \(\lambda\) is a class of transitive or asymmetrical relations, \(\dot{s} ʻ\lambda\) is transitive or asymmetrical; but if \(\lambda\) is a class of connected relations, \(\dot{s} ʻ\lambda\) is not in general connected. Hence if \(\lambda\) is a class of series, \(\dot{s}ʻ\lambda\) is not one series, but many detached series. This is one reason why the arithmetical sum of a relation of relations is not defined as \(\dot{s} ʻCʻP\), but as \(\dot{s} ʻCʻP \unicode{x228d}F^{;}P\) (cf. *162), because the latter, but not in general the former, is connected when \(P\) and all the members of \(CʻP\) are connected (*202·42).
>
> …

**Lean reading.** `connex` is Defs/Part5's class (✱202·01, through `P⃡'x = refsRels P x`, ✱97·01); `mem_connex`
gives the form ✱202·103. The readings are those of ✱200–✱201; in addition `P⃡''C'P` is
`Rboth P ʻʻ fld P`, `0 ∪ 1` is `zero ∪ one`, `R⃖_*'x`, `R⃗_*'x`, `R⃡_*'x` are `rels (anc R) x`,
`refs (anc R) x`, `refsRels (anc R) x`, the intervals `P(x⊢⊣y)`, `P(x⊣y)`, `P(x⟝y)`, `P(x−y)`
are `itvCC`, `itvOC`, `itvCO`, `itvOO` (✱121), `B'P` is the description `Desc Beg P` (`B⃗'P` is
`refs Beg P`), `P⥏` is the relation `opL fres P` (✱38·01), and `P⥏;P⃗_*;P` is
`opL fres P ⁏ Rfwd (anc P) ⁏ P` (✱150·05). Each description has the smallest scope (Basic §5);
in ✱202·181 the first description (`B'P`) has the larger scope. Three propositions are false as
printed (✱202·54, ✱202·55: the hypothesis `P⥏α ∈ connex` does not give the members of `α ∩ C'P`
a place in `C'P⥏α`; ✱202·172: misprint `P(x−y)` for `P(x−z)`); the corrected statements are
proved, and so is the failure of the printed ones. ✱202·161 prints `R1'J` for `Rl'J`, ✱202·171
prints `P(x⊢y)` for `P(x⟝y)`, and ✱202·81 prints `sm` for `smor`.

**Status.** proved (all propositions; ✱202·161, ✱202·171, ✱202·81 proved (reading); ✱202·172, ✱202·54,
✱202·55 proved (corrected), with the printed forms refuted; see their docstrings).
-/

/-- ✱202·01 (Df). \(\text{connex} =\hat{P} \{x\in CʻP.\supset _{x}.\overleftrightarrow{P}ʻx=CʻP\} \quad\text{Df}\) -/
theorem pm202_01 {α : Type u} :
    (connex : Set (α → α → Prop)) = {P | ∀ x, x ∈ fld P → refsRels P x = fld P} := rfl

/-- ✱202·1. \(\vdash \colon\ldotp P\in \text{connex} .\equiv :x\in CʻP.\supset _{x}.\overleftrightarrow{P}ʻx=CʻP \quad[(*202·01)]\) -/
theorem pm202_1 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ↔ ∀ x, x ∈ fld P → refsRels P x = fld P := Iff.rfl

/-- ✱202·101. \[\begin{align}& \vdash \colon\ldotp P\in \text{connex} .\equiv .x\in CʻP.\supset _{x}.\overrightarrow{P}ʻx\cup \iota ʻx\cup \overleftarrow{P}ʻx=CʻP\\ &[*202·1.*97·1]\end{align}\] -/
theorem pm202_101 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ↔ ∀ x, x ∈ fld P → refs P x ∪ ι x ∪ rels P x = fld P := by
  have key : ∀ x, x ∈ fld P → refsRels P x = refs P x ∪ ι x ∪ rels P x := by
    intro x hx
    ext y
    show (P y x ∨ (y = x ∧ y ∈ fld P)) ∨ P x y ↔ (P y x ∨ y = x) ∨ P x y
    constructor
    · rintro ((h | ⟨h, -⟩) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨h, by rw [h]; exact hx⟩)
      · exact Or.inr h
  show (∀ x, x ∈ fld P → refsRels P x = fld P) ↔ _
  exact forall_congr' fun x =>
    ⟨fun h hx => (key x hx).symm.trans (h hx), fun h hx => (key x hx).trans (h hx)⟩

/-- ✱202·102. \(\vdash :P\in \text{connex} .\equiv .\overleftrightarrow{P}ʻʻCʻP\in 0\cup 1 \quad[*97·231.*202·101]\) -/
theorem pm202_102 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ↔ Rboth P ʻʻ fld P ∈ (zero ∪ one : Set (Set (Set α))) := by
  rw [mem_zero_union_one]
  constructor
  · rintro h X Y ⟨x, hx, hX⟩ ⟨y, hy, hY⟩
    have hX' : X = refsRels P x := hX
    have hY' : Y = refsRels P y := hY
    rw [hX', hY', h x hx, h y hy]
  · intro h x hx
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz with (hz | ⟨-, hz⟩) | hz
      · exact ⟨x, Or.inl hz⟩
      · exact hz
      · exact ⟨x, Or.inr hz⟩
    · intro z hz
      have e := h (refsRels P x) (refsRels P z) ⟨x, hx, rfl⟩ ⟨z, hz, rfl⟩
      rw [e]
      exact Or.inl (Or.inr ⟨rfl, hz⟩)

/-- ✱202·103. \[\begin{align}& \vdash \colon\colon P\in \text{connex} .\equiv \colon\ldotp x,y\in CʻP.\supset _{x,y}:xPy.\lor.x=y.\lor.yPx\\ &[*97·23.*202·102]\end{align}\] -/
theorem pm202_103 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ↔ ∀ x y, x ∈ fld P ∧ y ∈ fld P → (P x y ∨ x = y) ∨ P y x := mem_connex

/-- ✱202·104. \[\begin{align}& \vdash \colon\colon P\in \text{connex} .\equiv \colon\ldotp x,y\in CʻP.x\neq y.\supset _{x,y}:xPy.\lor.yPx\\ &[*202·103.*5·6]\end{align}\] -/
theorem pm202_104 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ↔ ∀ x y, (x ∈ fld P ∧ y ∈ fld P) ∧ x ≠ y → P x y ∨ P y x := by
  rw [mem_connex]
  constructor
  · rintro h x y ⟨hxy, hne⟩
    rcases h x y hxy with (h1 | h1) | h1
    · exact Or.inl h1
    · exact (hne h1).elim
    · exact Or.inr h1
  · intro h x y hxy
    by_cases e : x = y
    · exact Or.inl (Or.inr e)
    · rcases h x y ⟨hxy, e⟩ with h1 | h1
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h1

/-- ✱202·11. \(\vdash :P\in \text{connex} .\equiv .\breve{P} \in \text{connex} \quad[*202·104.*33·22]\) -/
theorem pm202_11 {α : Type u} {P : α → α → Prop} : P ∈ connex ↔ P˘ ∈ connex := by
  rw [mem_connex, mem_connex, fld_cnv]
  constructor
  · intro h x y hxy
    rcases h y x ⟨hxy.2, hxy.1⟩ with (h1 | h1) | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1.symm)
    · exact Or.inr h1
  · intro h x y hxy
    rcases h y x ⟨hxy.2, hxy.1⟩ with (h1 | h1) | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1.symm)
    · exact Or.inr h1

/-- ✱202·12. \(\vdash \colon\ldotp \dot{\exists} !P.\supset :P\in \text{connex} .\equiv .\overleftrightarrow{P}ʻʻCʻP\in 1.\equiv .\overleftrightarrow{P}ʻʻCʻP=\iota ʻCʻP\) -/
theorem pm202_12 {α : Type u} {P : α → α → Prop} :
    rEx P → ((P ∈ connex ↔ Rboth P ʻʻ fld P ∈ (one : Set (Set (Set α)))) ∧
      (Rboth P ʻʻ fld P ∈ (one : Set (Set (Set α))) ↔ Rboth P ʻʻ fld P = ι (fld P))) := by
  rintro ⟨x0, y0, h0⟩
  have hx0 : x0 ∈ fld P := ⟨y0, Or.inl h0⟩
  have hc : P ∈ connex → Rboth P ʻʻ fld P = ι (fld P) := by
    intro h
    ext X
    constructor
    · rintro ⟨x, hx, hX⟩
      show X = fld P
      rw [show X = refsRels P x from hX]
      exact h x hx
    · intro hX
      exact ⟨x0, hx0, (show X = fld P from hX).trans (h x0 hx0).symm⟩
  have h1 : Rboth P ʻʻ fld P ∈ (one : Set (Set (Set α))) → P ∈ connex :=
    fun h => pm202_102.2 (Or.inr h)
  have h2 : Rboth P ʻʻ fld P = ι (fld P) → Rboth P ʻʻ fld P ∈ (one : Set (Set (Set α))) := by
    intro h
    rw [h]
    exact ⟨fld P, rfl⟩
  exact ⟨⟨fun h => h2 (hc h), h1⟩, ⟨fun h => hc (h1 h), h2⟩⟩

/-- ✱202·13. \(\vdash : R_{*} \in \text{connex} . \equiv . R_{\text{po}} \in \text{connex}\) -/
theorem pm202_13 {α : Type u} {R : α → α → Prop} : anc R ∈ connex ↔ po R ∈ connex := by
  rw [pm202_104, pm202_104, fld_anc, fld_po]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  apply imp_congr_right
  rintro ⟨-, hne⟩
  have e : ∀ a b, a ≠ b → (anc R a b ↔ po R a b) := by
    intro a b hab
    rw [anc_iff_po]
    exact ⟨fun h => h.resolve_left fun h' => hab h'.1, Or.inr⟩
  rw [e x y hne, e y x (Ne.symm hne)]

/-- ✱202·131. \(\vdash : P \in \text{connex} . CʻP = CʻQ . P \,\unicode{x2abd}\, Q . \supset . Q \in \text{connex} \quad[*202·103]\) -/
theorem pm202_131 {α : Type u} {P Q : α → α → Prop} :
    (P ∈ connex ∧ fld P = fld Q) ∧ P ⪽ Q → Q ∈ connex := by
  rintro ⟨⟨hc, hf⟩, hPQ⟩
  rw [mem_connex] at hc ⊢
  intro x y hxy
  rw [← hf] at hxy
  rcases hc x y hxy with (h | h) | h
  · exact Or.inl (Or.inl (hPQ x y h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr (hPQ y x h)

/-- ✱202·132. \[\begin{align}&\vdash : P \in \text{connex} . \supset . P_{\text{po}}, P_{*} \in \text{connex} \\ &[*202·131 . *90·14·151 . *91·502·504]\end{align}\] -/
theorem pm202_132 {α : Type u} {P : α → α → Prop} :
    P ∈ connex → po P ∈ connex ∧ anc P ∈ connex := by
  intro h
  refine ⟨pm202_131 ⟨⟨h, (fld_po P).symm⟩, fun x y hxy => po_of hxy⟩,
    pm202_131 ⟨⟨h, (fld_anc P).symm⟩, fun x y hxy => anc_of_po (po_of hxy)⟩⟩

/-- ✱202·133. \(\vdash \colon\colon I \upharpoonright CʻP \,\unicode{x2abd}\, P . \supset \colon\ldotp P \in \text{connex} . \equiv : x \in CʻP . \supset _{x} . CʻP = \overrightarrow{P}ʻx \cup \overleftarrow{P}ʻx\) -/
theorem pm202_133 {α : Type u} {P : α → α → Prop} :
    I ↾ fld P ⪽ P → (P ∈ connex ↔ ∀ x, x ∈ fld P → fld P = refs P x ∪ rels P x) := by
  intro hI
  have refl : ∀ x, x ∈ fld P → P x x := fun x hx => hI x x ⟨rfl, hx⟩
  rw [mem_connex]
  constructor
  · intro h x hx
    apply Set.Subset.antisymm
    · intro y hy
      rcases h x y ⟨hx, hy⟩ with (h1 | h1) | h1
      · exact Or.inr h1
      · rw [← h1]
        exact Or.inl (refl x hx)
      · exact Or.inl h1
    · rintro y (hy | hy)
      · exact ⟨x, Or.inl hy⟩
      · exact ⟨x, Or.inr hy⟩
  · intro h x y ⟨hx, hy⟩
    have hy' : y ∈ refs P x ∪ rels P x := by rw [← h x hx]; exact hy
    rcases hy' with h1 | h1
    · exact Or.inr h1
    · exact Or.inl (Or.inl h1)

/-- ✱202·134. \[\begin{align}&\vdash \colon\colon\ldotp I \upharpoonright CʻP \,\unicode{x2abd}\, P . \supset \colon\colon P \in \text{connex} . \equiv \colon\ldotp x, y \in CʻP . \supset _{x, y} : xPy . \lor . yPx\\ &[*202·103]\end{align}\] -/
theorem pm202_134 {α : Type u} {P : α → α → Prop} :
    I ↾ fld P ⪽ P → (P ∈ connex ↔ ∀ x y, x ∈ fld P ∧ y ∈ fld P → P x y ∨ P y x) := by
  intro hI
  rw [mem_connex]
  constructor
  · intro h x y hxy
    rcases h x y hxy with (h1 | h1) | h1
    · exact Or.inl h1
    · rw [← h1]
      exact Or.inl (hI x x ⟨rfl, hxy.1⟩)
    · exact Or.inr h1
  · intro h x y hxy
    rcases h x y hxy with h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inr h1

/-- ✱202·135. \(\vdash : P \in \text{connex} . \equiv . P \unicode{x228d} I \upharpoonright CʻP \in \text{connex}\) -/
theorem pm202_135 {α : Type u} {P : α → α → Prop} : P ∈ connex ↔ P ⊍ I ↾ fld P ∈ connex := by
  have hf : fld (P ⊍ I ↾ fld P) = fld P := by
    ext x
    constructor
    · rintro ⟨y, (h | ⟨rfl, hy⟩) | (h | ⟨e, hx⟩)⟩
      · exact ⟨y, Or.inl h⟩
      · exact hy
      · exact ⟨y, Or.inr h⟩
      · exact hx
    · rintro ⟨y, h | h⟩
      · exact ⟨y, Or.inl (Or.inl h)⟩
      · exact ⟨y, Or.inr (Or.inl h)⟩
  rw [mem_connex, mem_connex, hf]
  constructor
  · intro h x y hxy
    rcases h x y hxy with (h1 | h1) | h1
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inr h1)
    · exact Or.inr (Or.inl h1)
  · intro h x y hxy
    rcases h x y hxy with ((h1 | ⟨h1, -⟩) | h1) | (h1 | ⟨h1, -⟩)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h1
    · exact Or.inl (Or.inr h1.symm)

/-- ✱202·136. \[\begin{align}&\vdash \colon\ldotp P_{*} \in \text{connex} . \equiv : x \in CʻP . \supset _{x} . CʻP = \overrightarrow{P}_{*}ʻx \cup \overleftarrow{P}_{*}ʻx\\ &[*202·133 . *90·14·15]\end{align}\] -/
theorem pm202_136 {α : Type u} {P : α → α → Prop} :
    anc P ∈ connex ↔ ∀ x, x ∈ fld P → fld P = refs (anc P) x ∪ rels (anc P) x := by
  have hI : I ↾ fld (anc P) ⪽ anc P := by
    rintro x y ⟨e, hy⟩
    have e' : x = y := e
    subst e'
    rw [fld_anc] at hy
    exact anc_refl hy
  rw [pm202_133 hI, fld_anc]

/-- ✱202·137. \[\begin{align}&\vdash \colon\colon P_{*} \in \text{connex} . \equiv \colon\ldotp x, y \in CʻP . \supset _{x, y} : xP_{*}y . \lor . yP_{*}x\\ &[*202·134 . *90·15]\end{align}\] -/
theorem pm202_137 {α : Type u} {P : α → α → Prop} :
    anc P ∈ connex ↔ ∀ x y, x ∈ fld P ∧ y ∈ fld P → anc P x y ∨ anc P y x := by
  have hI : I ↾ fld (anc P) ⪽ anc P := by
    rintro x y ⟨e, hy⟩
    have e' : x = y := e
    subst e'
    rw [fld_anc] at hy
    exact anc_refl hy
  rw [pm202_134 hI, fld_anc]

/-- ✱202·138. \(\vdash \colon\ldotp P \in \text{trans} . \supset : P \in \text{connex} . \equiv . P_{*} \in \text{connex} \quad[*202·13 . *201·18]\) -/
theorem pm202_138 {α : Type u} {P : α → α → Prop} :
    P ∈ transR → (P ∈ connex ↔ anc P ∈ connex) := by
  intro ht
  rw [(pm201_18 ht).2]
  exact pm202_135

/-- ✱202·14. \(\vdash : R \in \text{Cls} \rightarrow 1 . \supset . R_{\text{po}} \unicode{x0294f} \overleftarrow{R}_{*}ʻx \in \text{connex} \quad[*96·303 . *202·104]\) -/
theorem pm202_14 {α : Type u} {R : α → α → Prop} {x : α} :
    R ∈ arrow Cls one → po R ⥏ rels (anc R) x ∈ connex := by
  intro hR
  have U : Relator.RightUnique R := fun a b c hab hac => mem_arrow_Cls_one.1 hR a b c ⟨hab, hac⟩
  rw [pm202_104]
  rintro y z ⟨⟨hy, hz⟩, hne⟩
  have hyA : anc R x y := by
    obtain ⟨w, ⟨⟨h1, -⟩, h2⟩ | ⟨⟨h1, -⟩, h2⟩⟩ := hy
    · exact h1
    · exact h2
  have hzA : anc R x z := by
    obtain ⟨w, ⟨⟨h1, -⟩, h2⟩ | ⟨⟨h1, -⟩, h2⟩⟩ := hz
    · exact h1
    · exact h2
  rcases Relation.ReflTransGen.total_of_right_unique U (anc_iff_reflTransGen.1 hyA).2
    (anc_iff_reflTransGen.1 hzA).2 with h | h
  · rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with e | h'
    · exact (hne e.symm).elim
    · exact Or.inl ⟨⟨hyA, po_iff_transGen.2 h'⟩, hzA⟩
  · rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with e | h'
    · exact (hne e).elim
    · exact Or.inr ⟨⟨hzA, po_iff_transGen.2 h'⟩, hyA⟩

/-- ✱202·141. \(\vdash : R \in 1 \rightarrow \text{Cls} . \supset . R_{\text{po}} \unicode{x0294f} \overrightarrow{R}_{*}ʻx \in \text{connex} \quad\left[*202·14 \frac{\breve{R}}{R}. *202·11\right]\) -/
theorem pm202_141 {α : Type u} {R : α → α → Prop} {x : α} :
    R ∈ arrow one Cls → po R ⥏ refs (anc R) x ∈ connex := by
  intro hR
  have U : Relator.RightUnique R˘ := fun a b c hab hac =>
    mem_arrow_one_Cls.1 hR b c a ⟨hab, hac⟩
  rw [pm202_104]
  rintro y z ⟨⟨hy, hz⟩, hne⟩
  have hyA : anc R y x := by
    obtain ⟨w, ⟨⟨h1, -⟩, h2⟩ | ⟨⟨h1, -⟩, h2⟩⟩ := hy
    · exact h1
    · exact h2
  have hzA : anc R z x := by
    obtain ⟨w, ⟨⟨h1, -⟩, h2⟩ | ⟨⟨h1, -⟩, h2⟩⟩ := hz
    · exact h1
    · exact h2
  have ry := Relation.reflTransGen_swap.2 (anc_iff_reflTransGen.1 hyA).2
  have rz := Relation.reflTransGen_swap.2 (anc_iff_reflTransGen.1 hzA).2
  rcases Relation.ReflTransGen.total_of_right_unique U ry rz with h | h
  · rcases Relation.reflTransGen_iff_eq_or_transGen.1 (Relation.reflTransGen_swap.1 h) with
      e | h'
    · exact (hne e).elim
    · exact Or.inr ⟨⟨hzA, po_iff_transGen.2 h'⟩, hyA⟩
  · rcases Relation.reflTransGen_iff_eq_or_transGen.1 (Relation.reflTransGen_swap.1 h) with
      e | h'
    · exact (hne e.symm).elim
    · exact Or.inl ⟨⟨hyA, po_iff_transGen.2 h'⟩, hzA⟩

/-- ✱202·15. \(\vdash : R \in 1 \rightarrow 1 . \supset . R_{\text{po}} \unicode{x0294f} \overleftrightarrow{R}_{*}ʻx \in \text{connex}\) -/
theorem pm202_15 {α : Type u} {R : α → α → Prop} {x : α} :
    R ∈ arrow one one → po R ⥏ refsRels (anc R) x ∈ connex := by
  intro hR
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hR
  have U : Relator.RightUnique R := fun a b c hab hac => h2 a b c ⟨hab, hac⟩
  have U' : Relator.RightUnique R˘ := fun a b c hab hac => h1 b c a ⟨hab, hac⟩
  have mem : ∀ y, y ∈ refsRels (anc R) x →
      y ∈ fld R ∧ (Relation.ReflTransGen R y x ∨ Relation.ReflTransGen R x y) := by
    rintro y ((h | ⟨rfl, h⟩) | h)
    · exact ⟨(fld_of_anc h).1, Or.inl (anc_iff_reflTransGen.1 h).2⟩
    · rw [fld_anc] at h
      exact ⟨h, Or.inl Relation.ReflTransGen.refl⟩
    · exact ⟨(fld_of_anc h).2, Or.inr (anc_iff_reflTransGen.1 h).2⟩
  have cmp : ∀ y z, y ∈ refsRels (anc R) x → z ∈ refsRels (anc R) x →
      Relation.ReflTransGen R y z ∨ Relation.ReflTransGen R z y := by
    intro y z hy hz
    rcases (mem y hy).2 with ry | ry <;> rcases (mem z hz).2 with rz | rz
    · rcases Relation.ReflTransGen.total_of_right_unique U'
        (Relation.reflTransGen_swap.2 ry) (Relation.reflTransGen_swap.2 rz) with h | h
      · exact Or.inr (Relation.reflTransGen_swap.1 h)
      · exact Or.inl (Relation.reflTransGen_swap.1 h)
    · exact Or.inl (ry.trans rz)
    · exact Or.inr (rz.trans ry)
    · exact Relation.ReflTransGen.total_of_right_unique U ry rz
  rw [pm202_104]
  rintro y z ⟨⟨hy, hz⟩, hne⟩
  have hyA : y ∈ refsRels (anc R) x := by
    obtain ⟨w, ⟨⟨h1, -⟩, h2⟩ | ⟨⟨h1, -⟩, h2⟩⟩ := hy
    · exact h1
    · exact h2
  have hzA : z ∈ refsRels (anc R) x := by
    obtain ⟨w, ⟨⟨h1, -⟩, h2⟩ | ⟨⟨h1, -⟩, h2⟩⟩ := hz
    · exact h1
    · exact h2
  rcases cmp y z hyA hzA with h | h
  · rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with e | h'
    · exact (hne e.symm).elim
    · exact Or.inl ⟨⟨hyA, po_iff_transGen.2 h'⟩, hzA⟩
  · rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with e | h'
    · exact (hne e).elim
    · exact Or.inr ⟨⟨hzA, po_iff_transGen.2 h'⟩, hyA⟩

/-- ✱202·16. \(\vdash :P\in \text{connex} .x,y\in CʻP.{\sim}(xPx).{\sim}(yPy).\overrightarrow{P}ʻx = \overrightarrow{P}ʻy.\supset .x = y\) -/
theorem pm202_16 {α : Type u} {P : α → α → Prop} {x y : α} :
    (((P ∈ connex ∧ (x ∈ fld P ∧ y ∈ fld P)) ∧ ¬P x x) ∧ ¬P y y) ∧ refs P x = refs P y →
      x = y := by
  rintro ⟨⟨⟨⟨hc, hxy⟩, hx⟩, hy⟩, he⟩
  rcases mem_connex.1 hc x y hxy with (h | h) | h
  · have h' : x ∈ refs P y := h
    rw [← he] at h'
    exact (hx h').elim
  · exact h
  · have h' : y ∈ refs P x := h
    rw [he] at h'
    exact (hy h').elim

/-- ✱202·161. \(\vdash :P\in \text{connex} \cap R1ʻJ.\supset .\overrightarrow{P}\upharpoonright CʻP\in 1\rightarrow 1.\overrightarrow{P}\upharpoonright CʻP\in (\overrightarrow{P}^{;}P) \overline{\,\text{smor}\,} P\)

**Status.** proved (reading): transcription error. The e-text prints `R1'J` for `Rl'J`
(the class of relations contained in diversity, as in the demonstration, which uses
`∼(xPx)` through ✱202·16). -/
theorem pm202_161 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ∩ rl J → Rfwd P ↾ fld P ∈ arrow one one ∧
      Rfwd P ↾ fld P ∈ smorbar (Rfwd P ⁏ P) P := by
  rintro ⟨hc, hJ⟩
  have irr := mem_rl_J.1 hJ
  have h11 : Rfwd P ↾ fld P ∈ arrow one one := by
    refine mem_arrow_one_one.2 ⟨?_, ?_⟩
    · rintro A B z ⟨⟨hA, -⟩, ⟨hB, -⟩⟩
      exact (hA : A = refs P z).trans (hB : B = refs P z).symm
    · rintro A x y ⟨⟨hx, hxf⟩, ⟨hy, hyf⟩⟩
      exact pm202_16 ⟨⟨⟨⟨hc, hxf, hyf⟩, irr x⟩, irr y⟩,
        (hx : A = refs P x).symm.trans (hy : A = refs P y)⟩
  refine ⟨h11, ⟨h11, ?_⟩, ?_⟩
  · ext x
    exact ⟨fun hx => ⟨refs P x, rfl, hx⟩, fun ⟨_, _, hx⟩ => hx⟩
  · funext X Y
    apply propext
    rw [semi_apply, semi_apply]
    constructor
    · rintro ⟨z, w, ⟨hz, hw⟩, hzw⟩
      exact ⟨z, w, ⟨⟨hz, ⟨w, Or.inl hzw⟩⟩, ⟨hw, ⟨z, Or.inr hzw⟩⟩⟩, hzw⟩
    · rintro ⟨z, w, ⟨hz, hw⟩, hzw⟩
      exact ⟨z, w, ⟨hz.1, hw.1⟩, hzw⟩

/-- ✱202·162. \(\vdash :P\in \text{connex} .P_{\text{po}}\,\unicode{x2abd}\, J.\supset .P\unicode{x0294f}^{;}\overrightarrow{P}_{*}^{;}P \,\text{smor}\, P.P\unicode{x0294f}\mid \overrightarrow{P}_{*}\upharpoonright CʻP\in 1\rightarrow 1\) -/
theorem pm202_162 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ∧ po P ⪽ J → smor (opL fres P ⁏ Rfwd (anc P) ⁏ P) P ∧
      opL fres P ⨾ Rfwd (anc P) ↾ fld P ∈ arrow one one := by
  rintro ⟨hc, hJ⟩
  have hS : ∀ X x, (opL fres P ⨾ Rfwd (anc P) ↾ fld P) X x ↔
      X = P ⥏ refs (anc P) x ∧ x ∈ fld P := by
    intro X x
    constructor
    · rintro ⟨⟨A, hXA, hAx⟩, hx⟩
      have hXA' : X = P ⥏ A := hXA
      have hAx' : A = refs (anc P) x := hAx
      rw [hXA', hAx']
      exact ⟨rfl, hx⟩
    · rintro ⟨rfl, hx⟩
      exact ⟨⟨refs (anc P) x, rfl, rfl⟩, hx⟩
  have h11 : opL fres P ⨾ Rfwd (anc P) ↾ fld P ∈ arrow one one := by
    refine mem_arrow_one_one.2 ⟨?_, ?_⟩
    · intro X Y z ⟨hX, hY⟩
      exact ((hS X z).1 hX).1.trans ((hS Y z).1 hY).1.symm
    · intro X x y ⟨hx, hy⟩
      obtain ⟨hXx, hxf⟩ := (hS X x).1 hx
      obtain ⟨hXy, hyf⟩ := (hS X y).1 hy
      have e : P ⥏ refs (anc P) x = P ⥏ refs (anc P) y := hXx.symm.trans hXy
      by_contra hne
      rcases cxne hc hxf hyf hne with h | h
      · have h1 : (P ⥏ refs (anc P) y) x y :=
          ⟨⟨anc_of_po (po_of h), h⟩, anc_refl hyf⟩
        rw [← e] at h1
        exact hJ x x (po_anc_trans (po_of h) h1.2) rfl
      · have h1 : (P ⥏ refs (anc P) x) y x :=
          ⟨⟨anc_of_po (po_of h), h⟩, anc_refl hxf⟩
        rw [e] at h1
        exact hJ y y (po_anc_trans (po_of h) h1.2) rfl
  refine ⟨⟨opL fres P ⨾ Rfwd (anc P) ↾ fld P, ⟨h11, ?_⟩, ?_⟩, h11⟩
  · ext x
    exact ⟨fun hx => ⟨_, (hS _ x).2 ⟨rfl, hx⟩⟩, fun ⟨X, hX⟩ => ((hS X x).1 hX).2⟩
  · rw [semi_semi]
    funext X Y
    apply propext
    rw [semi_apply, semi_apply]
    constructor
    · rintro ⟨z, w, ⟨hz, hw⟩, hzw⟩
      exact ⟨z, w, ⟨⟨hz, ⟨w, Or.inl hzw⟩⟩, ⟨hw, ⟨z, Or.inr hzw⟩⟩⟩, hzw⟩
    · rintro ⟨z, w, ⟨hz, hw⟩, hzw⟩
      exact ⟨z, w, ⟨hz.1, hw.1⟩, hzw⟩

/-- ✱202·17. \(\vdash :P_{\text{po}}\in \text{connex} .y\in P(x\vdash\dashv z).\supset .P(x\vdash\dashv y)\cup P(y\vdash\dashv z) = P(x\vdash\dashv z)\) -/
theorem pm202_17 {α : Type u} {P : α → α → Prop} {x y z : α} :
    po P ∈ connex ∧ y ∈ itvCC P x z → itvCC P x y ∪ itvCC P y z = itvCC P x z := by
  rintro ⟨hc, hxy, hyz⟩
  have hxy' : anc P x y := hxy
  have hyz' : anc P y z := hyz
  apply Set.Subset.antisymm
  · rintro w (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, anc_trans h2 hyz'⟩
    · exact ⟨anc_trans hxy' h1, h2⟩
  · rintro w ⟨h1, h2⟩
    have h1' : anc P x w := h1
    have h2' : anc P w z := h2
    by_cases e : w = y
    · rw [e]
      exact Or.inl ⟨hxy', anc_refl (fld_of_anc hyz').1⟩
    · rcases cxpo hc (fld_of_anc h2').1 (fld_of_anc hyz').1 e with h | h
      · exact Or.inl ⟨h1', anc_of_po h⟩
      · exact Or.inr ⟨anc_of_po h, h2'⟩

/-- ✱202·171. \[\begin{align}&\vdash :P_{\text{po}}\in \text{connex} .y\in P(x\vdash\dashv z).\supset .\\ &P(x\dashv z)=P(x\dashv y)\cup P(y\dashv z).P(x\unicode{x27dd} z)=P(x\vdash y)\cup P(y\unicode{x27dd} z)\\ &[\text{Proof as in *202·17}]\end{align}\]

**Status.** proved (reading): transcription error. The e-text prints `P(x⊢y)` in the
second conjunct, a sign that does not exist; the analogue of the other terms and of
✱202·17 is `P(x⟝y)` (`itvCO`), which is stated. -/
theorem pm202_171 {α : Type u} {P : α → α → Prop} {x y z : α} :
    po P ∈ connex ∧ y ∈ itvCC P x z →
      itvOC P x z = itvOC P x y ∪ itvOC P y z ∧ itvCO P x z = itvCO P x y ∪ itvCO P y z := by
  rintro ⟨hc, hxy, hyz⟩
  have hxy' : anc P x y := hxy
  have hyz' : anc P y z := hyz
  have hyf : y ∈ fld P := (fld_of_anc hyz').1
  constructor
  · apply Set.Subset.antisymm
    · rintro w ⟨h1, h2⟩
      have h1' : po P x w := h1
      have h2' : anc P w z := h2
      by_cases e : w = y
      · rw [e] at h1' ⊢
        exact Or.inl ⟨h1', anc_refl hyf⟩
      · rcases cxpo hc (fld_of_anc h2').1 hyf e with h | h
        · exact Or.inl ⟨h1', anc_of_po h⟩
        · exact Or.inr ⟨h, h2'⟩
    · rintro w (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, anc_trans h2 hyz'⟩
      · exact ⟨anc_po_trans hxy' h1, h2⟩
  · apply Set.Subset.antisymm
    · rintro w ⟨h1, h2⟩
      have h1' : anc P x w := h1
      have h2' : po P w z := h2
      by_cases e : w = y
      · rw [e] at h2' ⊢
        exact Or.inr ⟨anc_refl hyf, h2'⟩
      · rcases cxpo hc (fld_of_po h2').1 hyf e with h | h
        · exact Or.inl ⟨h1', h⟩
        · exact Or.inr ⟨anc_of_po h, h2'⟩
    · rintro w (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, po_anc_trans h2 hyz'⟩
      · exact ⟨anc_trans hxy' h1, h2⟩

/-- ✱202·172. \[\begin{align}\vdash :P_{\text{po}}\in &\text{connex} .y\in P(x-z).\supset .\\ &P(x-y)=P(x\dashv y)\cup P(y-z)=P(x-y)\cup P(y \unicode{x27dd} z)\\ &[\text{Proof as in *202·17}]\end{align}\]

**Status.** proved (corrected): the e-text prints the first member of the chain as
`P(x−y)`, but under the hypothesis `P(x⊣y) ∪ P(y−z)` contains `y`, which is not in `P(x−y)`
when `P_po ⊂̇ J` (e.g. `<` on the natural numbers, `x, y, z = 0, 1, 2`; see
`pm202_172_printed_false`). The demonstration ("as in ✱202·17") gives `P(x−z)`, which is
stated: `P(x−z) = P(x⊣y) ∪ P(y−z) = P(x−y) ∪ P(y⟝z)`. -/
theorem pm202_172 {α : Type u} {P : α → α → Prop} {x y z : α} :
    po P ∈ connex ∧ y ∈ itvOO P x z →
      itvOO P x z = itvOC P x y ∪ itvOO P y z ∧
        itvOC P x y ∪ itvOO P y z = itvOO P x y ∪ itvCO P y z := by
  rintro ⟨hc, hxy, hyz⟩
  have hxy' : po P x y := hxy
  have hyz' : po P y z := hyz
  have hyf : y ∈ fld P := (fld_of_po hyz').1
  constructor
  · apply Set.Subset.antisymm
    · rintro w ⟨h1, h2⟩
      have h1' : po P x w := h1
      have h2' : po P w z := h2
      by_cases e : w = y
      · rw [e] at h1' ⊢
        exact Or.inl ⟨h1', anc_refl hyf⟩
      · rcases cxpo hc (fld_of_po h2').1 hyf e with h | h
        · exact Or.inl ⟨h1', anc_of_po h⟩
        · exact Or.inr ⟨h, h2'⟩
    · rintro w (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, anc_po_trans h2 hyz'⟩
      · exact ⟨po_trans hxy' h1, h2⟩
  · apply Set.Subset.antisymm
    · rintro w (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have h2' : anc P w y := h2
        rcases anc_iff_po.1 h2' with ⟨e, -⟩ | h
        · rw [e]
          exact Or.inr ⟨anc_refl hyf, hyz'⟩
        · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨anc_of_po h1, h2⟩
    · rintro w (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h1, anc_of_po h2⟩
      · have h1' : anc P y w := h1
        rcases anc_iff_po.1 h1' with ⟨e, -⟩ | h
        · rw [← e]
          exact Or.inl ⟨hxy', anc_refl hyf⟩
        · exact Or.inr ⟨h, h2⟩

/-- The printed form of ✱202·172 (with `P(x−y)` as the first member of the chain) is false:
take `P` the relation `<` on the natural numbers and `x, y, z = 0, 1, 2`. -/
theorem pm202_172_printed_false :
    ¬ ∀ (P : ℕ → ℕ → Prop) (x y z : ℕ), po P ∈ connex ∧ y ∈ itvOO P x z →
      itvOO P x y = itvOC P x y ∪ itvOO P y z ∧
        itvOC P x y ∪ itvOO P y z = itvOO P x y ∪ itvCO P y z := by
  intro h
  have ht : (fun a b : ℕ => a < b) ∈ transR :=
    mem_transR.2 fun a b c hab => lt_trans hab.1 hab.2
  have hpo : po (fun a b : ℕ => a < b) = fun a b => a < b := po_eq_of_transR ht
  have hc : po (fun a b : ℕ => a < b) ∈ connex := by
    rw [hpo, mem_connex]
    intro a b _
    rcases lt_trichotomy a b with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h1
  have hy : (1 : ℕ) ∈ itvOO (fun a b : ℕ => a < b) 0 2 := by
    show po _ 0 1 ∧ po _ 1 2
    rw [hpo]
    exact ⟨by omega, by omega⟩
  have key := (h (fun a b : ℕ => a < b) 0 1 2 ⟨hc, hy⟩).1
  have h1 : (1 : ℕ) ∈ itvOC (fun a b : ℕ => a < b) 0 1 := by
    refine ⟨?_, anc_refl ⟨0, Or.inr (by omega)⟩⟩
    show po _ 0 1
    rw [hpo]
    omega
  have h2 : (1 : ℕ) ∈ itvOO (fun a b : ℕ => a < b) 0 1 := by
    rw [key]
    exact Or.inl h1
  have h3 : po (fun a b : ℕ => a < b) 1 1 := h2.2
  rw [hpo] at h3
  exact absurd h3 (lt_irrefl 1)

/-- ✱202·18. \(\vdash :P_{\text{po}}\in \text{connex} .\text{E}!BʻP.\supset .CʻP=\overleftarrow{P}_{*}ʻBʻP\) -/
theorem pm202_18 {α : Type u} {P : α → α → Prop} :
    po P ∈ connex ∧ EDesc Beg P → Desc Beg P (fun b => fld P = rels (anc P) b) := by
  rintro ⟨hc, b, hb⟩
  refine ⟨b, hb, ?_⟩
  exact (first_of_beg hc ((hb b).2 rfl)).symm

/-- ✱202·181. \(\vdash :P_{\text{po}}\in \text{connex} .\text{E}!BʻP.\text{E}!Bʻ\breve{P} .\supset .CʻP=P(BʻP\vdash\dashv Bʻ\breve{P})\) -/
theorem pm202_181 {α : Type u} {P : α → α → Prop} :
    (po P ∈ connex ∧ EDesc Beg P) ∧ EDesc Beg P˘ →
      Desc Beg P (fun b => Desc Beg P˘ (fun c => fld P = itvCC P b c)) := by
  rintro ⟨⟨hc, b, hb⟩, c, hc'⟩
  refine ⟨b, hb, c, hc', ?_⟩
  have e1 := first_of_beg hc ((hb b).2 rfl)
  have e2 := last_of_beg hc ((hc' c).2 rfl)
  show fld P = rels (anc P) b ∩ refs (anc P) c
  rw [e1, e2, Set.inter_self]

/-- ✱202·21. \(\vdash :P\in \text{connex} .S\in 1\rightarrow \text{Cls}.\supset .S^{;}P\in \text{connex}\) -/
theorem pm202_21 {α : Type u} {β : Type v} {P : β → β → Prop} {S : α → β → Prop} :
    P ∈ connex ∧ S ∈ arrow one Cls → S ⁏ P ∈ connex := by
  rintro ⟨hc, hS⟩
  have om := mem_arrow_one_Cls.1 hS
  have hf : ∀ x, x ∈ fld (S ⁏ P) → ∃ z, S x z ∧ z ∈ fld P := by
    rintro x ⟨y, h | h⟩
    · obtain ⟨a, b, ⟨hxa, -⟩, hab⟩ := (semi_apply S P x y).1 h
      exact ⟨a, hxa, ⟨b, Or.inl hab⟩⟩
    · obtain ⟨a, b, ⟨-, hxb⟩, hab⟩ := (semi_apply S P y x).1 h
      exact ⟨b, hxb, ⟨a, Or.inr hab⟩⟩
  rw [mem_connex]
  rintro x y ⟨hx, hy⟩
  obtain ⟨a, hxa, ha⟩ := hf x hx
  obtain ⟨b, hyb, hb⟩ := hf y hy
  rcases mem_connex.1 hc a b ⟨ha, hb⟩ with (h | h) | h
  · exact Or.inl (Or.inl ((semi_apply S P x y).2 ⟨a, b, ⟨hxa, hyb⟩, h⟩))
  · rw [← h] at hyb
    exact Or.inl (Or.inr (om x y a ⟨hxa, hyb⟩))
  · exact Or.inr ((semi_apply S P y x).2 ⟨b, a, ⟨hyb, hxa⟩, h⟩)

/-- ✱202·211. \(\vdash :P\in \text{connex} .Q\,\,\text{smor}\,\,P.\supset .Q\in \text{connex}\) -/
theorem pm202_211 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} :
    P ∈ connex ∧ smor Q P → Q ∈ connex := by
  rintro ⟨hP, S, ⟨hS, -⟩, rfl⟩
  exact pm202_21 ⟨hP, mem_arrow_one_Cls.2 (mem_arrow_one_one.1 hS).1⟩

/-- ✱202·212. \(\vdash :P\in \text{connex} .\supset .\text{Nr}ʻP\subset \text{connex}\) -/
theorem pm202_212 {α : Type u} {γ : Type w} {P : α → α → Prop} :
    P ∈ connex → nr γ P ⊆ connex :=
  fun h _ hQ => pm202_211 ⟨h, hQ⟩

/-- ✱202·22. \(\vdash :P\in \text{connex} .\equiv .\text{N}_{0}\text{r}ʻP\subset \text{connex} .\equiv .\exists !\text{N}_{0}\text{r}ʻP\cap \text{connex}\) -/
theorem pm202_22 {α : Type u} {P : α → α → Prop} :
    (P ∈ connex ↔ n₀r P ⊆ connex) ∧ (n₀r P ⊆ connex ↔ (n₀r P ∩ connex).Nonempty) := by
  have h1 : P ∈ connex → n₀r P ⊆ connex := fun h Q hQ => pm202_211 ⟨h, mem_n₀r.1 hQ⟩
  refine ⟨⟨h1, fun h => h (self_mem_n₀r P)⟩,
    ⟨fun h => ⟨P, self_mem_n₀r P, h (self_mem_n₀r P)⟩, ?_⟩⟩
  rintro ⟨Q, hQ, hQc⟩
  exact h1 (pm202_211 ⟨hQc, smor_symm (mem_n₀r.1 hQ)⟩)

/-- ✱202·3. \(\vdash .\dot{\Lambda} \in \text{connex}\) -/
theorem pm202_3 {α : Type u} : (rNull : α → α → Prop) ∈ connex := by
  rw [mem_connex]
  rintro x y ⟨⟨z, h | h⟩, -⟩ <;> exact (rNull_apply _ _ h).elim

/-- ✱202·31. \(\vdash .x\downarrow y\in \text{connex}\) -/
theorem pm202_31 {α : Type u} {x y : α} : x ↓ y ∈ connex := by
  have hf : ∀ a, a ∈ fld (x ↓ y) → a = x ∨ a = y := by
    rintro a ⟨w, h | h⟩
    · exact Or.inl ((couple_apply x y a w).1 h).1
    · exact Or.inr ((couple_apply x y w a).1 h).2
  rw [mem_connex]
  rintro a b ⟨ha, hb⟩
  rcases hf a ha with rfl | rfl <;> rcases hf b hb with rfl | rfl
  · exact Or.inl (Or.inr rfl)
  · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl (Or.inr rfl)

/-- ✱202·33. \(\vdash :P\in \text{connex} .\supset .P\unicode{x0294f}\alpha \in \text{connex} \) -/
theorem pm202_33 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex → P ⥏ A ∈ connex := by
  intro hc
  rw [mem_connex]
  rintro x y ⟨hx, hy⟩
  obtain ⟨hxA, hxf⟩ := fld_fres_sub hx
  obtain ⟨hyA, hyf⟩ := fld_fres_sub hy
  rcases mem_connex.1 hc x y ⟨hxf, hyf⟩ with (h | h) | h
  · exact Or.inl (Or.inl ⟨⟨hxA, h⟩, hyA⟩)
  · exact Or.inl (Or.inr h)
  · exact Or.inr ⟨⟨hyA, h⟩, hxA⟩

/-- ✱202·4. \(\vdash :P,Q\in \text{connex} .\supset .P\unicode{x2909}Q\in \text{connex}\) -/
theorem pm202_4 {α : Type u} {P Q : α → α → Prop} :
    P ∈ connex ∧ Q ∈ connex → P ⤉ Q ∈ connex := by
  rintro ⟨hP, hQ⟩
  rw [mem_connex, fld_rsum]
  rintro x y ⟨hx | hx, hy | hy⟩
  · rcases mem_connex.1 hP x y ⟨hx, hy⟩ with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr ⟨hx, hy⟩))
  · exact Or.inr (Or.inr ⟨hy, hx⟩)
  · rcases mem_connex.1 hQ x y ⟨hx, hy⟩ with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl (Or.inr h))

/-- ✱202·401. \(\vdash \colon\ldotp CʻP\cap CʻQ=\Lambda .\supset :P\unicode{x2909}Q\in \text{connex} .\equiv .P,Q\in \text{connex}\) -/
theorem pm202_401 {α : Type u} {P Q : α → α → Prop} :
    fld P ∩ fld Q = Λ → (P ⤉ Q ∈ connex ↔ P ∈ connex ∧ Q ∈ connex) := by
  intro hd
  have d := eqΛ.1 hd
  refine ⟨fun h => ⟨?_, ?_⟩, pm202_4⟩
  · rw [mem_connex]
    rintro x y ⟨hx, hy⟩
    have hx' : x ∈ fld (P ⤉ Q) := by rw [fld_rsum]; exact Or.inl hx
    have hy' : y ∈ fld (P ⤉ Q) := by rw [fld_rsum]; exact Or.inl hy
    rcases mem_connex.1 h x y ⟨hx', hy'⟩ with (((h1 | h1) | ⟨-, h1⟩) | h1) | ((h1 | h1) | ⟨-, h1⟩)
    · exact Or.inl (Or.inl h1)
    · exact (d x ⟨hx, ⟨y, Or.inl h1⟩⟩).elim
    · exact (d y ⟨hy, h1⟩).elim
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h1
    · exact (d x ⟨hx, ⟨y, Or.inr h1⟩⟩).elim
    · exact (d x ⟨hx, h1⟩).elim
  · rw [mem_connex]
    rintro x y ⟨hx, hy⟩
    have hx' : x ∈ fld (P ⤉ Q) := by rw [fld_rsum]; exact Or.inr hx
    have hy' : y ∈ fld (P ⤉ Q) := by rw [fld_rsum]; exact Or.inr hy
    rcases mem_connex.1 h x y ⟨hx', hy'⟩ with (((h1 | h1) | ⟨h1, -⟩) | h1) | ((h1 | h1) | ⟨h1, -⟩)
    · exact (d x ⟨⟨y, Or.inl h1⟩, hx⟩).elim
    · exact Or.inl (Or.inl h1)
    · exact (d x ⟨h1, hx⟩).elim
    · exact Or.inl (Or.inr h1)
    · exact (d y ⟨⟨x, Or.inl h1⟩, hy⟩).elim
    · exact Or.inr h1
    · exact (d y ⟨h1, hy⟩).elim

/-- ✱202·41. \(\vdash : P \in \text{connex} . \supset . P \unicode{x21f8} z \in \text{connex} . z \unicode{x21f7} P \in \text{connex}\) -/
theorem pm202_41 {α : Type u} {P : α → α → Prop} {z : α} :
    P ∈ connex → P ⇸ z ∈ connex ∧ z ⇷ P ∈ connex := by
  intro hc
  constructor
  · have hf : ∀ a, a ∈ fld (P ⇸ z) → a ∈ fld P ∨ a = z := by
      rintro a ⟨w, (h | ⟨h, -⟩) | (h | ⟨-, h⟩)⟩
      · exact Or.inl ⟨w, Or.inl h⟩
      · exact Or.inl h
      · exact Or.inl ⟨w, Or.inr h⟩
      · exact Or.inr h
    rw [mem_connex]
    rintro x y ⟨hx, hy⟩
    have hx2 := hf x hx
    have hy2 := hf y hy
    clear hx hy
    rcases hx2 with hx | rfl <;> rcases hy2 with hy | rfl
    · rcases mem_connex.1 hc x y ⟨hx, hy⟩ with (h | h) | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inl (Or.inr ⟨hx, rfl⟩))
    · exact Or.inr (Or.inr ⟨hy, rfl⟩)
    · exact Or.inl (Or.inr rfl)
  · have hf : ∀ a, a ∈ fld (z ⇷ P) → a ∈ fld P ∨ a = z := by
      rintro a ⟨w, (⟨h, -⟩ | h) | (⟨-, h⟩ | h)⟩
      · exact Or.inr h
      · exact Or.inl ⟨w, Or.inl h⟩
      · exact Or.inl h
      · exact Or.inl ⟨w, Or.inr h⟩
    rw [mem_connex]
    rintro x y ⟨hx, hy⟩
    have hx2 := hf x hx
    have hy2 := hf y hy
    clear hx hy
    rcases hx2 with hx | rfl <;> rcases hy2 with hy | rfl
    · rcases mem_connex.1 hc x y ⟨hx, hy⟩ with (h | h) | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl ⟨rfl, hx⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨rfl, hy⟩))
    · exact Or.inl (Or.inr rfl)

/-- ✱202·411. \(\vdash . x \downarrow y \unicode{x21f8} z \in \text{connex} \quad[*202·41·31]\) -/
theorem pm202_411 {α : Type u} {x y z : α} : (x ↓ y) ⇸ z ∈ connex :=
  (pm202_41 pm202_31).1

/-- ✱202·412. \(\vdash \colon\ldotp z {\sim} \in CʻP . \supset : P \in \text{connex} . \equiv . P \unicode{x21f8} z \in \text{connex} . \equiv . z \unicode{x21f7} P \in \text{connex}\) -/
theorem pm202_412 {α : Type u} {P : α → α → Prop} {z : α} :
    z ∉ fld P → ((P ∈ connex ↔ P ⇸ z ∈ connex) ∧ (P ⇸ z ∈ connex ↔ z ⇷ P ∈ connex)) := by
  intro hz
  have back1 : P ⇸ z ∈ connex → P ∈ connex := by
    intro h
    rw [mem_connex]
    rintro x y ⟨hx, hy⟩
    have hx' : x ∈ fld (P ⇸ z) := by
      obtain ⟨w, hw | hw⟩ := hx
      · exact ⟨w, Or.inl (Or.inl hw)⟩
      · exact ⟨w, Or.inr (Or.inl hw)⟩
    have hy' : y ∈ fld (P ⇸ z) := by
      obtain ⟨w, hw | hw⟩ := hy
      · exact ⟨w, Or.inl (Or.inl hw)⟩
      · exact ⟨w, Or.inr (Or.inl hw)⟩
    rcases mem_connex.1 h x y ⟨hx', hy'⟩ with ((h1 | ⟨-, e⟩) | h1) | (h1 | ⟨-, e⟩)
    · exact Or.inl (Or.inl h1)
    · rw [e] at hy
      exact (hz hy).elim
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h1
    · rw [e] at hx
      exact (hz hx).elim
  have back2 : z ⇷ P ∈ connex → P ∈ connex := by
    intro h
    rw [mem_connex]
    rintro x y ⟨hx, hy⟩
    have hx' : x ∈ fld (z ⇷ P) := by
      obtain ⟨w, hw | hw⟩ := hx
      · exact ⟨w, Or.inl (Or.inr hw)⟩
      · exact ⟨w, Or.inr (Or.inr hw)⟩
    have hy' : y ∈ fld (z ⇷ P) := by
      obtain ⟨w, hw | hw⟩ := hy
      · exact ⟨w, Or.inl (Or.inr hw)⟩
      · exact ⟨w, Or.inr (Or.inr hw)⟩
    rcases mem_connex.1 h x y ⟨hx', hy'⟩ with ((⟨e, -⟩ | h1) | h1) | (⟨e, -⟩ | h1)
    · rw [e] at hx
      exact (hz hx).elim
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
    · rw [e] at hy
      exact (hz hy).elim
    · exact Or.inr h1
  exact ⟨⟨fun h => (pm202_41 h).1, back1⟩,
    ⟨fun h => (pm202_41 (back1 h)).2, fun h => (pm202_41 (back2 h)).1⟩⟩

/-- ✱202·42. \(\vdash : P \in \text{connex} . CʻP \subset \text{connex} . \supset . \Sigma ʻP \in \text{connex}\) -/
theorem pm202_42 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ connex ∧ fld P ⊆ connex → relSigma P ∈ connex := by
  rintro ⟨hc, hC⟩
  have hf : ∀ x, x ∈ fld (relSigma P) → ∃ Q, Q ∈ fld P ∧ x ∈ fld Q := by
    rintro x ⟨y, h | h⟩
    · rcases (relSigma_apply P x y).1 h with ⟨Q, hQ, hxy⟩ | ⟨Q, R, ⟨hx, -⟩, hQR⟩
      · exact ⟨Q, hQ, ⟨y, Or.inl hxy⟩⟩
      · exact ⟨Q, ⟨R, Or.inl hQR⟩, hx⟩
    · rcases (relSigma_apply P y x).1 h with ⟨Q, hQ, hyx⟩ | ⟨Q, R, ⟨-, hx⟩, hQR⟩
      · exact ⟨Q, hQ, ⟨y, Or.inr hyx⟩⟩
      · exact ⟨R, ⟨Q, Or.inr hQR⟩, hx⟩
  rw [mem_connex]
  rintro x y ⟨hx, hy⟩
  obtain ⟨Q, hQ, hxQ⟩ := hf x hx
  obtain ⟨R, hR, hyR⟩ := hf y hy
  rcases mem_connex.1 hc Q R ⟨hQ, hR⟩ with (h | h) | h
  · exact Or.inl (Or.inl ((relSigma_apply P x y).2 (Or.inr ⟨Q, R, ⟨hxQ, hyR⟩, h⟩)))
  · rw [← h] at hyR
    rcases mem_connex.1 (hC hQ) x y ⟨hxQ, hyR⟩ with (h1 | h1) | h1
    · exact Or.inl (Or.inl ((relSigma_apply P x y).2 (Or.inl ⟨Q, hQ, h1⟩)))
    · exact Or.inl (Or.inr h1)
    · exact Or.inr ((relSigma_apply P y x).2 (Or.inl ⟨Q, hQ, h1⟩))
  · exact Or.inr ((relSigma_apply P y x).2 (Or.inr ⟨R, Q, ⟨hyR, hxQ⟩, h⟩))

/-- ✱202·5. \(\vdash \colon\ldotp P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.x,y\in CʻP.\supset :x\neq y.{\sim}(xPy).\equiv .yPx\) -/
theorem pm202_5 {α : Type u} {P : α → α → Prop} {x y : α} :
    (P ∈ connex ∧ rsq P ⪽ J) ∧ (x ∈ fld P ∧ y ∈ fld P) → (x ≠ y ∧ ¬P x y ↔ P y x) := by
  rintro ⟨⟨hc, hJ⟩, hxy⟩
  constructor
  · rintro ⟨hne, hn⟩
    rcases mem_connex.1 hc x y hxy with (h | h) | h
    · exact (hn h).elim
    · exact (hne h).elim
    · exact h
  · intro h
    refine ⟨fun e => ?_, fun h' => hJ x x ⟨y, h', h⟩ rfl⟩
    rw [e] at h
    exact pm200_36 hJ y y h rfl

/-- ✱202·501. \(\vdash :P\in \text{connex} .\supset .CʻP-\alpha -Pʻʻ\alpha \subset pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\) -/
theorem pm202_501 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex → (fld P \ A) \ P ʻʻ A ⊆ prodCls (Rbwd P ʻʻ (A ∩ fld P)) := by
  rintro hc y ⟨⟨hy, hyA⟩, hyP⟩
  rw [mem_prodCls_Rbwd]
  rintro x ⟨hxA, hx⟩
  rcases mem_connex.1 hc x y ⟨hx, hy⟩ with (h | h) | h
  · exact h
  · rw [h] at hxA
    exact (hyA hxA).elim
  · exact (hyP ⟨x, hxA, h⟩).elim

/-- ✱202·502. \(\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.\exists !\alpha \cap CʻP.\supset .CʻP-\alpha -Pʻʻ\alpha =pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\) -/
theorem pm202_502 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ connex ∧ rsq P ⪽ J) ∧ (A ∩ fld P).Nonempty →
      (fld P \ A) \ P ʻʻ A = prodCls (Rbwd P ʻʻ (A ∩ fld P)) := by
  rintro ⟨⟨hc, hJ⟩, a, haA, haf⟩
  apply Set.Subset.antisymm (pm202_501 hc)
  intro z hz
  rw [mem_prodCls_Rbwd] at hz
  have haz : P a z := hz a ⟨haA, haf⟩
  refine ⟨⟨⟨a, Or.inr haz⟩, fun hzA => ?_⟩, ?_⟩
  · have hzz : P z z := hz z ⟨hzA, ⟨a, Or.inr haz⟩⟩
    exact pm200_36 hJ z z hzz rfl
  · rintro ⟨b, hbA, hzb⟩
    have hbz : P b z := hz b ⟨hbA, ⟨z, Or.inr hzb⟩⟩
    exact hJ z z ⟨b, hzb, hbz⟩ rfl

/-- ✱202·503. \(\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.\supset .CʻP-pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)=(\alpha \cap CʻP)\cup Pʻʻ\alpha\) -/
theorem pm202_503 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ rsq P ⪽ J → fld P \ prodCls (Rbwd P ʻʻ (A ∩ fld P)) = (A ∩ fld P) ∪ P ʻʻ A := by
  rintro ⟨hc, hJ⟩
  by_cases hne : (A ∩ fld P).Nonempty
  · rw [← pm202_502 ⟨⟨hc, hJ⟩, hne⟩]
    ext z
    constructor
    · rintro ⟨hz, hn⟩
      by_cases hzA : z ∈ A
      · exact Or.inl ⟨hzA, hz⟩
      · by_cases hzP : z ∈ P ʻʻ A
        · exact Or.inr hzP
        · exact (hn ⟨⟨hz, hzA⟩, hzP⟩).elim
    · rintro (⟨hzA, hz⟩ | hzP)
      · exact ⟨hz, fun h => h.1.2 hzA⟩
      · obtain ⟨b, hb, hzb⟩ := hzP
        exact ⟨⟨b, Or.inl hzb⟩, fun h => h.2 ⟨b, hb, hzb⟩⟩
  · have hall : ∀ z, z ∈ prodCls (Rbwd P ʻʻ (A ∩ fld P)) :=
      fun z => mem_prodCls_Rbwd.2 fun a ha => (hne ⟨a, ha⟩).elim
    ext z
    constructor
    · rintro ⟨-, hn⟩
      exact (hn (hall z)).elim
    · rintro (h | ⟨b, hb, hzb⟩)
      · exact (hne ⟨z, h⟩).elim
      · exact (hne ⟨b, hb, ⟨z, Or.inr hzb⟩⟩).elim

/-- ✱202·504. \(\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.\supset .CʻP\cap pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)=CʻP-\alpha -Pʻʻ\alpha\) -/
theorem pm202_504 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ rsq P ⪽ J → fld P ∩ prodCls (Rbwd P ʻʻ (A ∩ fld P)) = (fld P \ A) \ P ʻʻ A := by
  rintro ⟨hc, hJ⟩
  by_cases hne : (A ∩ fld P).Nonempty
  · rw [← pm202_502 ⟨⟨hc, hJ⟩, hne⟩]
    ext z
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h.1.1, h⟩
  · have hall : ∀ z, z ∈ prodCls (Rbwd P ʻʻ (A ∩ fld P)) :=
      fun z => mem_prodCls_Rbwd.2 fun a ha => (hne ⟨a, ha⟩).elim
    ext z
    constructor
    · rintro ⟨hz, -⟩
      refine ⟨⟨hz, fun hzA => hne ⟨z, hzA, hz⟩⟩, ?_⟩
      rintro ⟨b, hb, hzb⟩
      exact hne ⟨b, hb, ⟨z, Or.inr hzb⟩⟩
    · rintro ⟨⟨hz, -⟩, -⟩
      exact ⟨hz, hall z⟩

/-- ✱202·505. \(\vdash :P\in \text{connex} .\supset .CʻP=Pʻʻ\alpha \cup (\alpha \cap CʻP)\cup \{CʻP\cap pʻ\overleftarrow{P}ʻʻ(\alpha \cap CʻP)\}\) -/
theorem pm202_505 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex → fld P = P ʻʻ A ∪ (A ∩ fld P) ∪ (fld P ∩ prodCls (Rbwd P ʻʻ (A ∩ fld P))) := by
  intro hc
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hzA : z ∈ A
    · exact Or.inl (Or.inr ⟨hzA, hz⟩)
    · by_cases hzP : z ∈ P ʻʻ A
      · exact Or.inl (Or.inl hzP)
      · exact Or.inr ⟨hz, pm202_501 hc ⟨⟨hz, hzA⟩, hzP⟩⟩
  · rintro z ((⟨b, -, hzb⟩ | ⟨-, hz⟩) | ⟨hz, -⟩)
    · exact ⟨b, Or.inl hzb⟩
    · exact hz
    · exact hz

/-- ✱202·51. \[\begin{align}\vdash :P\in \text{connex} .\alpha \subset CʻP.&\exists !\alpha .\supset .\\ &CʻP=Pʻʻ\alpha \cup \alpha \cup pʻ\overleftarrow{P}ʻʻ\alpha =\breve{P} ʻʻ\alpha \cup \alpha \cup pʻ\overrightarrow{P}ʻʻ\alpha\end{align}\] -/
theorem pm202_51 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ connex ∧ A ⊆ fld P) ∧ A.Nonempty →
      fld P = P ʻʻ A ∪ A ∪ prodCls (Rbwd P ʻʻ A) ∧
        P ʻʻ A ∪ A ∪ prodCls (Rbwd P ʻʻ A) = P˘ ʻʻ A ∪ A ∪ prodCls (Rfwd P ʻʻ A) := by
  rintro ⟨⟨hc, hA⟩, a, ha⟩
  have hc' : P˘ ∈ connex := pm202_11.1 hc
  have e1 : ∀ Q : α → α → Prop, Q ∈ connex → A ⊆ fld Q →
      fld Q = Q ʻʻ A ∪ A ∪ prodCls (Rbwd Q ʻʻ A) := by
    intro Q hQ hAQ
    apply Set.Subset.antisymm
    · intro z hz
      by_cases hzA : z ∈ A
      · exact Or.inl (Or.inr hzA)
      · by_cases hzP : z ∈ Q ʻʻ A
        · exact Or.inl (Or.inl hzP)
        · have := pm202_501 hQ ⟨⟨hz, hzA⟩, hzP⟩
          exact Or.inr (mem_prodCls_Rbwd.2 fun b hb => (mem_prodCls_Rbwd.1 this) b ⟨hb, hAQ hb⟩)
    · rintro z ((⟨b, -, hzb⟩ | hz) | hz)
      · exact ⟨b, Or.inl hzb⟩
      · exact hAQ hz
      · exact ⟨a, Or.inr (mem_prodCls_Rbwd.1 hz a ha)⟩
  have h1 := e1 P hc hA
  have h2 := e1 P˘ hc' (by rw [fld_cnv]; exact hA)
  rw [fld_cnv] at h2
  refine ⟨h1, h1.symm.trans ?_⟩
  rw [h2]
  rfl

/-- ✱202·511. \[\begin{align}\vdash \colon\ldotp P\in &\text{connex} .\text{E}!BʻP.\supset :\\ &\exists !pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP).\equiv .BʻP{\sim}\in \alpha .\equiv .BʻP\in pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)\end{align}\] -/
theorem pm202_511 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ EDesc Beg P →
      (((prodCls (Rfwd P ʻʻ (A ∩ fld P))).Nonempty ↔ Desc Beg P (fun b => b ∉ A)) ∧
        (Desc Beg P (fun b => b ∉ A) ↔
          Desc Beg P (fun b => b ∈ prodCls (Rfwd P ʻʻ (A ∩ fld P))))) := by
  rintro ⟨hc, b, hb⟩
  have hbB : Beg b P := (hb b).2 rfl
  obtain ⟨⟨c, hbc⟩, hbn⟩ := hbB
  have hbf : b ∈ fld P := ⟨c, Or.inl hbc⟩
  have d : ∀ ψ : α → Prop, Desc Beg P ψ ↔ ψ b := fun ψ => TheIs_iff_of_unique hb
  rw [d, d]
  have k1 : b ∉ A → b ∈ prodCls (Rfwd P ʻʻ (A ∩ fld P)) := by
    intro hbA
    rw [mem_prodCls_Rfwd]
    rintro x ⟨hxA, hx⟩
    have hne : b ≠ x := fun e => hbA (by rw [e]; exact hxA)
    rcases cxne hc hbf hx hne with h | h
    · exact h
    · exact (hbn ⟨x, h⟩).elim
  have k2 : (prodCls (Rfwd P ʻʻ (A ∩ fld P))).Nonempty → b ∉ A := by
    rintro ⟨z, hz⟩ hbA
    exact hbn ⟨z, mem_prodCls_Rfwd.1 hz b ⟨hbA, hbf⟩⟩
  exact ⟨⟨k2, fun h => ⟨b, k1 h⟩⟩, ⟨k1, fun h => k2 ⟨b, h⟩⟩⟩

/-- ✱202·52. \(\vdash :P\in \text{connex} .\supset .\overrightarrow{B}ʻP,\overrightarrow{B}ʻ\breve{P} \in 0\cup 1\) -/
theorem pm202_52 {α : Type u} {P : α → α → Prop} :
    P ∈ connex → refs Beg P ∈ (zero ∪ one : Set (Set α)) ∧
      refs Beg P˘ ∈ (zero ∪ one : Set (Set α)) := by
  intro hc
  constructor
  · rw [mem_zero_union_one]
    rintro x y ⟨⟨a, hxa⟩, hx⟩ ⟨⟨b, hyb⟩, hy⟩
    by_contra hne
    rcases cxne hc ⟨a, Or.inl hxa⟩ ⟨b, Or.inl hyb⟩ hne with h | h
    · exact hy ⟨x, h⟩
    · exact hx ⟨y, h⟩
  · rw [mem_zero_union_one]
    rintro x y ⟨⟨a, hxa⟩, hx⟩ ⟨⟨b, hyb⟩, hy⟩
    by_contra hne
    rcases cxne hc ⟨a, Or.inr hxa⟩ ⟨b, Or.inr hyb⟩ hne with h | h
    · exact hx ⟨y, h⟩
    · exact hy ⟨x, h⟩

/-- ✱202·521. \(\vdash :P_{*}\in \text{connex} .\supset .\overrightarrow{B}ʻP\subset pʻ\overrightarrow{P}_{*}ʻʻCʻP\) -/
theorem pm202_521 {α : Type u} {P : α → α → Prop} :
    anc P ∈ connex → refs Beg P ⊆ prodCls (Rfwd (anc P) ʻʻ fld P) := by
  rintro hc x ⟨⟨a, hxa⟩, hx⟩
  rw [mem_prodCls_Rfwd]
  intro y hy
  rcases (pm202_137.1 hc) x y ⟨⟨a, Or.inl hxa⟩, hy⟩ with h | h
  · exact h
  · rcases anc_iff_po.1 h with ⟨e, -⟩ | h'
    · rw [← e]
      exact anc_refl hy
    · obtain ⟨w, -, hwx⟩ := Relation.TransGen.tail'_iff.1 (po_iff_transGen.1 h')
      exact (hx ⟨w, hwx⟩).elim

/-- ✱202·522. \(\vdash .\overrightarrow{B}ʻP=\overrightarrow{B}ʻP_{\text{po}} \quad[*91·504]\) -/
theorem pm202_522 {α : Type u} {P : α → α → Prop} : refs Beg P = refs Beg (po P) := by
  have hd : dom (po P) = dom P := by
    ext x
    constructor
    · rintro ⟨y, h⟩
      obtain ⟨b, hxb, -⟩ := Relation.TransGen.head'_iff.1 (po_iff_transGen.1 h)
      exact ⟨b, hxb⟩
    · rintro ⟨y, h⟩
      exact ⟨y, po_of h⟩
  have hc : codom (po P) = codom P := by
    ext x
    constructor
    · rintro ⟨y, h⟩
      obtain ⟨b, -, hbx⟩ := Relation.TransGen.tail'_iff.1 (po_iff_transGen.1 h)
      exact ⟨b, hbx⟩
    · rintro ⟨y, h⟩
      exact ⟨y, po_of h⟩
  ext x
  show x ∈ dom P \ codom P ↔ x ∈ dom (po P) \ codom (po P)
  rw [hd, hc]

/-- ✱202·523. \(\vdash :P_{*}\in \text{connex} .\supset .\overrightarrow{B}ʻP\in 0\cup 1 \quad[*202·13·52·522]\) -/
theorem pm202_523 {α : Type u} {P : α → α → Prop} :
    anc P ∈ connex → refs Beg P ∈ (zero ∪ one : Set (Set α)) := by
  intro hc
  rw [pm202_522]
  exact (pm202_52 (pm202_13.1 hc)).1

/-- ✱202·524. \(\vdash :P\in \text{connex} .\exists !\overrightarrow{B}ʻP.\supset .\text{ᗡ}ʻP=\overleftarrow{P}ʻBʻP\) -/
theorem pm202_524 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ∧ (refs Beg P).Nonempty → Desc Beg P (fun b => codom P = rels P b) := by
  rintro ⟨hc, b, hb⟩
  have hu := mem_zero_union_one.1 (pm202_52 hc).1
  refine ⟨b, fun x => ⟨fun hx => hu x b hx hb, fun e => by rw [e]; exact hb⟩, ?_⟩
  obtain ⟨⟨c, hbc⟩, hbn⟩ := hb
  ext y
  constructor
  · rintro ⟨w, hwy⟩
    have hne : b ≠ y := fun e => hbn ⟨w, by rw [e]; exact hwy⟩
    rcases cxne hc ⟨c, Or.inl hbc⟩ ⟨w, Or.inr hwy⟩ hne with h | h
    · exact h
    · exact (hbn ⟨y, h⟩).elim
  · intro h
    exact ⟨b, h⟩

/-- ✱202·53. \(\vdash :Q\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.Q\,\unicode{x2abd}\, P.\supset .Q=P\unicode{x0294f}CʻQ\) -/
theorem pm202_53 {α : Type u} {P Q : α → α → Prop} :
    (Q ∈ connex ∧ rsq P ⪽ J) ∧ Q ⪽ P → Q = P ⥏ fld Q := by
  rintro ⟨⟨hc, hJ⟩, hQP⟩
  funext x y
  apply propext
  constructor
  · intro h
    exact ⟨⟨⟨y, Or.inl h⟩, hQP x y h⟩, ⟨x, Or.inr h⟩⟩
  · rintro ⟨⟨hx, hxy⟩, hy⟩
    have hne : x ≠ y := fun e => pm200_36 hJ x y hxy e
    rcases cxne hc hx hy hne with h | h
    · exact h
    · exact (hJ x x ⟨y, hxy, hQP y x h⟩ rfl).elim

/-- ✱202·54. \(\vdash :P\unicode{x0294f}\alpha \in \text{connex} .\alpha \cap CʻP{\sim}\in 1.\supset .CʻP\unicode{x0294f}\alpha = \alpha \cap CʻP\)

**Status.** proved (corrected): false as printed. With `P` relating `0` to `1` and `1` to
`2`, and `α = {0, 2}`, `P⥏α = Λ̇` is connected and `α ∩ C'P` has two members, but
`C'P⥏α = Λ` (`pm202_54_printed_false`). The demonstration applies ✱202·104 to two members
`x, y` of `α ∩ C'P`, i.e. to `P`, not to `P⥏α`; every later use (✱202·541, ✱202·8, ✱204·45)
has `P ∈ connex`. The hypothesis `P⥏α ∈ connex` is corrected to `P ∈ connex` (which implies
it, ✱202·33). -/
theorem pm202_54 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∩ fld P ∉ (one : Set (Set α)) → fld (P ⥏ A) = A ∩ fld P := by
  rintro ⟨hc, h1⟩
  apply Set.Subset.antisymm fld_fres_sub
  rintro x ⟨hxA, hx⟩
  have : ∃ y, y ∈ A ∩ fld P ∧ y ≠ x := by
    by_contra hn
    push_neg at hn
    exact h1 (mem_one_iff.2 ⟨x, fun z => ⟨fun hz => hn z hz, fun e => by rw [e]; exact ⟨hxA, hx⟩⟩⟩)
  obtain ⟨y, ⟨hyA, hy⟩, hne⟩ := this
  rcases cxne hc hx hy (Ne.symm hne) with h | h
  · exact ⟨y, Or.inl ⟨⟨hxA, h⟩, hyA⟩⟩
  · exact ⟨y, Or.inr ⟨⟨hyA, h⟩, hxA⟩⟩

/-- The printed form of ✱202·54 (hypothesis `P⥏α ∈ connex`) is false. -/
theorem pm202_54_printed_false :
    ¬ ∀ (P : ℕ → ℕ → Prop) (A : Set ℕ),
      P ⥏ A ∈ connex ∧ A ∩ fld P ∉ (one : Set (Set ℕ)) → fld (P ⥏ A) = A ∩ fld P := by
  intro h
  obtain ⟨hc, h1, h0, hf⟩ := cex54
  have := h cexP cexA ⟨hc, h1⟩
  rw [← this] at h0
  exact hf 0 h0

/-- ✱202·541. \(\vdash :P\in \text{trans} \cap \text{connex} .\alpha \cap CʻP{\sim}\in 1.\supset .(P\unicode{x0294f}\alpha )_{*} = P_{*}\unicode{x0294f}\alpha\) -/
theorem pm202_541 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR ∩ connex ∧ A ∩ fld P ∉ (one : Set (Set α)) → anc (P ⥏ A) = anc P ⥏ A := by
  rintro ⟨⟨ht, hc⟩, h1⟩
  have ht' : P ⥏ A ∈ transR := pm201_33 ht
  have hf : fld (P ⥏ A) = A ∩ fld P := pm202_54 ⟨hc, h1⟩
  funext x y
  apply propext
  rw [anc_iff_of_transR ht', hf]
  show (x = y ∧ x ∈ A ∩ fld P) ∨ ((x ∈ A ∧ P x y) ∧ y ∈ A) ↔ (x ∈ A ∧ anc P x y) ∧ y ∈ A
  rw [anc_iff_of_transR ht]
  constructor
  · rintro (⟨rfl, hxA, hx⟩ | ⟨⟨hxA, h⟩, hyA⟩)
    · exact ⟨⟨hxA, Or.inl ⟨rfl, hx⟩⟩, hxA⟩
    · exact ⟨⟨hxA, Or.inr h⟩, hyA⟩
  · rintro ⟨⟨hxA, ⟨rfl, hx⟩ | h⟩, hyA⟩
    · exact Or.inl ⟨rfl, hxA, hx⟩
    · exact Or.inr ⟨⟨hxA, h⟩, hyA⟩

/-- ✱202·55. \(\vdash :P\unicode{x0294f}\alpha \in \text{connex} .\alpha \subset CʻP.\alpha {\sim}\in 1.\supset .CʻP\unicode{x0294f}\alpha = \alpha \quad[*202·54]\)

**Status.** proved (corrected): false as printed, by the counterexample to ✱202·54 (`P`
relating `0` to `1` and `1` to `2`, `α = {0, 2} ⊂ C'P`; `pm202_55_printed_false`). PM derives
it from ✱202·54; the hypothesis `P⥏α ∈ connex` is corrected to `P ∈ connex`, as in ✱202·54
(its uses, e.g. ✱204·45, have `P ∈ connex`). -/
theorem pm202_55 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ connex ∧ A ⊆ fld P) ∧ A ∉ (one : Set (Set α)) → fld (P ⥏ A) = A := by
  rintro ⟨⟨hc, hA⟩, h1⟩
  have e : A ∩ fld P = A := Set.inter_eq_left.2 hA
  rw [pm202_54 ⟨hc, by rw [e]; exact h1⟩, e]

/-- The printed form of ✱202·55 (hypothesis `P⥏α ∈ connex`) is false. -/
theorem pm202_55_printed_false :
    ¬ ∀ (P : ℕ → ℕ → Prop) (A : Set ℕ),
      (P ⥏ A ∈ connex ∧ A ⊆ fld P) ∧ A ∉ (one : Set (Set ℕ)) → fld (P ⥏ A) = A := by
  intro h
  obtain ⟨hc, h1, h0, hf⟩ := cex54
  have hA : cexA ⊆ fld cexP := fun z hz => (cexA_sub z hz)
  have e : cexA ∩ fld cexP = cexA := Set.inter_eq_left.2 hA
  rw [e] at h1 h0
  have := h cexP cexA ⟨⟨hc, hA⟩, h1⟩
  rw [← this] at h0
  exact hf 0 h0

/-- ✱202·56. \(\vdash .P\in \text{connex} .P\,\unicode{x2abd}\, J.x\in CʻP.\beta \subset CʻP.Pʻʻ\beta \subset \overrightarrow{P}ʻx.\supset .\beta \subset \overrightarrow{P}ʻx\cup \iota ʻx\) -/
theorem pm202_56 {α : Type u} {P : α → α → Prop} {x : α} {B : Set α} :
    (((P ∈ connex ∧ P ⪽ J) ∧ x ∈ fld P) ∧ B ⊆ fld P) ∧ P ʻʻ B ⊆ refs P x →
      B ⊆ refs P x ∪ ι x := by
  rintro ⟨⟨⟨⟨hc, hJ⟩, hx⟩, hB⟩, hPB⟩ y hy
  have hnxy : ¬P x y := fun h => hJ x x (hPB ⟨y, hy, h⟩) rfl
  rcases mem_connex.1 hc x y ⟨hx, hB hy⟩ with (h | h) | h
  · exact (hnxy h).elim
  · exact Or.inr h.symm
  · exact Or.inl h

/-- ✱202·6. \(\vdash \colon\colon P\in \text{connex} .P\,\unicode{x2abd}\, J.\supset \colon\ldotp x,y\in CʻP.x \neq y. \equiv :xPy.\lor.yPx\) -/
theorem pm202_6 {α : Type u} {P : α → α → Prop} {x y : α} :
    P ∈ connex ∧ P ⪽ J → ((x ∈ fld P ∧ y ∈ fld P) ∧ x ≠ y ↔ P x y ∨ P y x) := by
  rintro ⟨hc, hJ⟩
  constructor
  · rintro ⟨⟨hx, hy⟩, hne⟩
    exact cxne hc hx hy hne
  · rintro (h | h)
    · exact ⟨⟨⟨y, Or.inl h⟩, ⟨x, Or.inr h⟩⟩, hJ x y h⟩
    · exact ⟨⟨⟨y, Or.inr h⟩, ⟨x, Or.inl h⟩⟩, fun e => hJ y x h e.symm⟩

/-- ✱202·61. \[\begin{align}\vdash \colon\colon P\in &\text{connex} .P\,\unicode{x2abd}\, J:\phi (x,y). \equiv _{x,y}.\phi (y,x):\supset \colon\ldotp \\ &xPy.\supset _{x,y}.\phi (x,y): \equiv :x,y\in CʻP.x \neq y.\supset _{x,y}.\phi (x,y)\end{align}\] -/
theorem pm202_61 {α : Type u} {P : α → α → Prop} {φ : α → α → Prop} :
    (P ∈ connex ∧ P ⪽ J) ∧ (∀ x y, φ x y ↔ φ y x) →
      ((∀ x y, P x y → φ x y) ↔ (∀ x y, (x ∈ fld P ∧ y ∈ fld P) ∧ x ≠ y → φ x y)) := by
  rintro ⟨⟨hc, hJ⟩, hφ⟩
  constructor
  · rintro h x y ⟨⟨hx, hy⟩, hne⟩
    rcases cxne hc hx hy hne with h1 | h1
    · exact h x y h1
    · exact (hφ x y).2 (h y x h1)
  · intro h x y hxy
    exact h x y ⟨⟨⟨y, Or.inl hxy⟩, ⟨x, Or.inr hxy⟩⟩, hJ x y hxy⟩

/-- ✱202·611. \[\begin{align}&\vdash \colon\ldotp P \in \text{connex} . P \,\unicode{x2abd}\, J . R = \breve{R} . \supset : P \,\unicode{x2abd}\, R . \equiv . J \unicode{x0294f} CʻP \,\unicode{x2abd}\, R\\ &\left[*202·61 \frac{xRy}{\phi(x, y)}\right]\end{align}\] -/
theorem pm202_611 {α : Type u} {P R : α → α → Prop} :
    (P ∈ connex ∧ P ⪽ J) ∧ R = R˘ → (P ⪽ R ↔ J ⥏ fld P ⪽ R) := by
  rintro ⟨⟨hc, hJ⟩, hR⟩
  have hs : ∀ x y, R x y ↔ R y x := fun x y => by
    constructor
    · intro h
      rw [hR] at h
      exact h
    · intro h
      rw [hR]
      exact h
  constructor
  · rintro h x y ⟨⟨hx, hne⟩, hy⟩
    rcases cxne hc hx hy hne with h1 | h1
    · exact h x y h1
    · exact (hs x y).2 (h y x h1)
  · intro h x y hxy
    exact h x y ⟨⟨⟨y, Or.inl hxy⟩, hJ x y hxy⟩, ⟨x, Or.inr hxy⟩⟩

/-- ✱202·62. \(\vdash \colon\ldotp P \in \text{connex} . P \,\unicode{x2abd}\, J . \supset : P \in \text{Rel}^{2}\text{excl} . \equiv . F^{;}P \,\unicode{x2abd}\, J\) -/
theorem pm202_62 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ connex ∧ P ⪽ J → (P ∈ Rel2excl ↔ F ⁏ P ⪽ J) := by
  rintro ⟨hc, hJ⟩
  constructor
  · intro hex x y hxy e
    have e' : x = y := e
    subst e'
    obtain ⟨Q, R, ⟨hxQ, hxR⟩, hQR⟩ := (semi_apply F P x x).1 hxy
    exact eqΛ.1 (hex Q R ⟨⟨⟨R, Or.inl hQR⟩, ⟨Q, Or.inr hQR⟩⟩, hJ Q R hQR⟩) x ⟨hxQ, hxR⟩
  · intro h Q R ⟨⟨hQ, hR⟩, hne⟩
    rw [eqΛ]
    rintro x ⟨hxQ, hxR⟩
    rcases cxne hc hQ hR hne with h1 | h1
    · exact h x x ((semi_apply F P x x).2 ⟨Q, R, ⟨hxQ, hxR⟩, h1⟩) rfl
    · exact h x x ((semi_apply F P x x).2 ⟨R, Q, ⟨hxR, hxQ⟩, h1⟩) rfl

/-- ✱202·7. \(\vdash : P \in \text{connex} . \supset . P \dot{-} P^{2} \in 1 \rightarrow 1\) -/
theorem pm202_7 {α : Type u} {P : α → α → Prop} : P ∈ connex → P ∸ rsq P ∈ arrow one one := by
  intro hc
  refine mem_arrow_one_one.2 ⟨?_, ?_⟩
  · rintro y z x ⟨⟨hyx, hny⟩, ⟨hzx, hnz⟩⟩
    by_contra hne
    rcases cxne hc ⟨x, Or.inl hyx⟩ ⟨x, Or.inl hzx⟩ hne with h | h
    · exact hny ⟨z, h, hzx⟩
    · exact hnz ⟨y, h, hyx⟩
  · rintro x y z ⟨⟨hxy, hny⟩, ⟨hxz, hnz⟩⟩
    by_contra hne
    rcases cxne hc ⟨x, Or.inr hxy⟩ ⟨x, Or.inr hxz⟩ hne with h | h
    · exact hnz ⟨y, hxy, h⟩
    · exact hny ⟨z, hxz, h⟩

/-- ✱202·71. \(\vdash : P \in \text{connex} . x (P \dot{-} P^{2}) y . \supset . \overrightarrow{P}_{\text{po}}ʻy = \overrightarrow{P}_{*}ʻx\) -/
theorem pm202_71 {α : Type u} {P : α → α → Prop} {x y : α} :
    P ∈ connex ∧ (P ∸ rsq P) x y → refs (po P) y = refs (anc P) x := by
  rintro ⟨hc, hxy, hn⟩
  have hx : x ∈ fld P := ⟨y, Or.inl hxy⟩
  apply Set.Subset.antisymm
  · intro z hz
    have hz' : po P z y := hz
    show anc P z x
    have hzf : z ∈ fld P := (fld_of_po hz').1
    obtain ⟨w, hzw, hwy⟩ := Relation.TransGen.tail'_iff.1 (po_iff_transGen.1 hz')
    rw [anc_iff_reflTransGen]
    refine ⟨hzf, ?_⟩
    by_cases e : w = x
    · rw [← e]
      exact hzw
    · rcases cxne hc ⟨y, Or.inl hwy⟩ hx e with h | h
      · exact hzw.tail h
      · exact (hn ⟨w, h, hwy⟩).elim
  · intro z hz
    exact anc_po_trans hz (po_of hxy)

/-- ✱202·72. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .x(P\dot{-} P^{2})y.\supset .\overrightarrow{P}ʻy=\overrightarrow{P}ʻx\cup \iota ʻx\\ &[*202·71.*201·18·521]\end{align}\] -/
theorem pm202_72 {α : Type u} {P : α → α → Prop} {x y : α} :
    P ∈ transR ∩ connex ∧ (P ∸ rsq P) x y → refs P y = refs P x ∪ ι x := by
  rintro ⟨⟨ht, hc⟩, hxy⟩
  have h1 := pm202_71 ⟨hc, hxy⟩
  rw [po_eq_of_transR ht] at h1
  rw [h1, pm201_521 ⟨ht, ⟨y, Or.inl hxy.1⟩⟩]

/-- ✱202·8. \[\begin{align}\vdash :Q\in \text{connex} .S\in P\,\overline{\,\text{smor}\,}\,Q.CʻQ\cap &\beta {\sim}\in 1.\supset .\\ &S\upharpoonright \beta \in (P\unicode{x0294f}Sʻʻ\beta )\overline{\,\text{smor}\,} Q\unicode{x0294f}\beta\end{align}\] -/
theorem pm202_8 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {S : α → β → Prop} {B : Set β} :
    (Q ∈ connex ∧ S ∈ smorbar P Q) ∧ fld Q ∩ B ∉ (one : Set (Set β)) →
      S ↾ B ∈ smorbar (P ⥏ S ʻʻ B) (Q ⥏ B) := by
  rintro ⟨⟨hc, ⟨hS, hcod⟩, rfl⟩, h1⟩
  have hf : fld (Q ⥏ B) = B ∩ fld Q := pm202_54 ⟨hc, by rw [Set.inter_comm]; exact h1⟩
  have eqS : S ↾ B = S ↾ fld (Q ⥏ B) := by
    funext x y
    apply propext
    rw [hf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, by rw [hcod]; exact ⟨x, h1⟩⟩
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
  rw [eqS]
  refine smorbar_restrict_gen hS ?_ (fun z hz => (fld_fres_sub hz).1) rfl
  rw [← hcod]
  exact fun z hz => (fld_fres_sub hz).2

/-- ✱202·81. \(\vdash :Q\in \text{connex} .S\in P\,\overline{\,\text{smor}\,}\,Q.\supset .(P\unicode{x0294f}Sʻʻ\beta )\text{ sm }Q\unicode{x0294f}\beta\)

**Status.** proved (reading): transcription error. The e-text prints `sm` (similarity of
classes) between the relations `P⥏S''β` and `Q⥏β`; the demonstration proves ordinal
similarity (`smor`, from ✱202·8 and ✱153), which is stated. -/
theorem pm202_81 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {S : α → β → Prop} {B : Set β} :
    Q ∈ connex ∧ S ∈ smorbar P Q → smor (P ⥏ S ʻʻ B) (Q ⥏ B) := by
  rintro ⟨-, ⟨hS, hcod⟩, rfl⟩
  refine ⟨_, smorbar_restrict_gen hS ?_ (fun z hz => (fld_fres_sub hz).1) rfl⟩
  rw [← hcod]
  exact fun z hz => (fld_fres_sub hz).2

/-! ### Helper lemmas for ✱204 (not PM propositions) -/

section Helpers204

variable {α : Type u} {β : Type v}

/-- `M(Q × P)N` for couples: `(x↓z)(Q × P)(y↓w)` iff `z = w ∈ C'Q` and `xPy`, or `zQw` and
`x, y ∈ C'P` (✱166·11). -/
private theorem rtimes_couple {P : α → α → Prop} {Q : β → β → Prop} {x y : α} {z w : β} :
    (Q ×ᵣ P) (x ↓ z) (y ↓ w) ↔
      (z = w ∧ z ∈ fld Q ∧ P x y) ∨ (Q z w ∧ x ∈ fld P ∧ y ∈ fld P) := by
  rw [rtimes_apply]
  constructor
  · rintro (⟨r, hr, a, b, ⟨e1, e2⟩, hab⟩ | ⟨r, s, hrs, a, b, ⟨ha, hb⟩, e1, e2⟩)
    · obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e1
      obtain ⟨rfl, e⟩ := couple_eq_couple_iff.1 e2
      exact Or.inl ⟨e.symm, hr, hab⟩
    · obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e1
      obtain ⟨rfl, rfl⟩ := couple_eq_couple_iff.1 e2
      exact Or.inr ⟨hrs, ha, hb⟩
  · rintro (⟨rfl, hz, hxy⟩ | ⟨hzw, hx, hy⟩)
    · exact Or.inl ⟨z, hz, x, y, ⟨rfl, rfl⟩, hxy⟩
    · exact Or.inr ⟨z, w, hzw, x, y, ⟨hx, hy⟩, rfl, rfl⟩

/-- The members of `C'(Q × P)` are the couples `x↓z` with `x ∈ C'P`, `z ∈ C'Q`. -/
private theorem rtimes_fld {P : α → α → Prop} {Q : β → β → Prop} {u : α → β → Prop} :
    u ∈ fld (Q ×ᵣ P) → ∃ x z, u = x ↓ z ∧ x ∈ fld P ∧ z ∈ fld Q := by
  rintro ⟨v, h | h⟩
  · rcases (rtimes_apply Q P u v).1 h with
      ⟨z, hz, x, y, ⟨rfl, -⟩, hxy⟩ | ⟨z, w, hzw, x, y, ⟨hx, -⟩, rfl, -⟩
    · exact ⟨x, z, rfl, ⟨y, Or.inl hxy⟩, hz⟩
    · exact ⟨x, z, rfl, hx, ⟨w, Or.inl hzw⟩⟩
  · rcases (rtimes_apply Q P v u).1 h with
      ⟨z, hz, x, y, ⟨-, rfl⟩, hxy⟩ | ⟨z, w, hzw, x, y, ⟨-, hy⟩, -, rfl⟩
    · exact ⟨y, z, rfl, ⟨x, Or.inr hxy⟩, hz⟩
    · exact ⟨y, w, rfl, hy, ⟨z, Or.inr hzw⟩⟩

private theorem rtimes_mem_fld {P : α → α → Prop} {Q : β → β → Prop} {x : α} {z : β}
    (hx : x ∈ fld P) (hz : z ∈ fld Q) : x ↓ z ∈ fld (Q ×ᵣ P) := by
  obtain ⟨y, h | h⟩ := hx
  · exact ⟨y ↓ z, Or.inl (rtimes_couple.2 (Or.inl ⟨rfl, hz, h⟩))⟩
  · exact ⟨y ↓ z, Or.inr (rtimes_couple.2 (Or.inl ⟨rfl, hz, h⟩))⟩

/-- A selection `M ∈ F_Δ'C'P` has exactly one value `M'Q ∈ C'Q` at each `Q ∈ C'P`. -/
private theorem sel_unique {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M : α → (α → α → Prop) → Prop} (hM : M ∈ sel F (fld P)) {Q : α → α → Prop}
    (hQ : Q ∈ fld P) : ∃ b, (∀ x, M x Q ↔ x = b) ∧ b ∈ fld Q := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_sel_iff.1 hM
  have : Q ∈ codom M := by rw [h3]; exact hQ
  obtain ⟨b, hb⟩ := this
  exact ⟨b, fun x => ⟨fun hx => mem_arrow_one_Cls.1 h1 x b Q ⟨hx, hb⟩,
    fun e => by rw [e]; exact hb⟩, h2 b Q hb⟩

private theorem sel_codom {P : (α → α → Prop) → (α → α → Prop) → Prop}
    {M : α → (α → α → Prop) → Prop} (hM : M ∈ sel F (fld P)) {Q : α → α → Prop} {x : α}
    (h : M x Q) : Q ∈ fld P := by
  rw [← (mem_sel_iff.1 hM).2]
  exact ⟨x, h⟩

/-- Composing two "value relations" `(L'S) r (M'S)` and `(M'S) r' (N'S)`. -/
private theorem desc_comp {L M N : α → β → Prop} {S : β} {r r' r'' : α → α → Prop}
    (h1 : Desc L S (fun x => Desc M S (fun y => r x y)))
    (h2 : Desc M S (fun x => Desc N S (fun y => r' x y)))
    (h : ∀ a b c, r a b → r' b c → r'' a c) :
    Desc L S (fun x => Desc N S (fun y => r'' x y)) := by
  obtain ⟨a, ha, b, hb, hab⟩ := h1
  obtain ⟨b', hb', c, hc, hbc⟩ := h2
  have e : b' = b := (hb b').1 ((hb' b').2 rfl)
  rw [e] at hbc
  exact ⟨a, ha, c, hc, h a b c hab hbc⟩


/-! #### Likeness of sums, of `x ⇷ P`, `P ⇸ x`, and of the arithmetical sums (for ✱204·45–·483) -/

section RelArith

variable {γ : Type w}

private theorem smorbar_dom {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    (h : S ∈ smorbar P Q) {x : α} {z : β} (hxz : S x z) : x ∈ fld P := by
  obtain ⟨⟨-, hcod⟩, rfl⟩ := h
  have hz : z ∈ fld Q := by rw [hcod]; exact ⟨x, hxz⟩
  obtain ⟨w, hzw | hwz⟩ := hz
  · obtain ⟨y, hyw⟩ : w ∈ codom S := by rw [← hcod]; exact ⟨z, Or.inr hzw⟩
    exact ⟨y, Or.inl ((semi_apply S Q x y).2 ⟨z, w, ⟨hxz, hyw⟩, hzw⟩)⟩
  · obtain ⟨y, hyw⟩ : w ∈ codom S := by rw [← hcod]; exact ⟨z, Or.inl hwz⟩
    exact ⟨y, Or.inr ((semi_apply S Q y x).2 ⟨w, z, ⟨hyw, hxz⟩, hwz⟩)⟩

private theorem smorbar_fld {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    (h : S ∈ smorbar P Q) {x : α} (hx : x ∈ fld P) : ∃ z, S x z := by
  obtain ⟨-, rfl⟩ := h
  obtain ⟨y, h1 | h1⟩ := hx
  · obtain ⟨a, b, ⟨hxa, -⟩, -⟩ := (semi_apply S Q x y).1 h1
    exact ⟨a, hxa⟩
  · obtain ⟨a, b, ⟨-, hxb⟩, -⟩ := (semi_apply S Q y x).1 h1
    exact ⟨b, hxb⟩

private theorem smorbar_codom {P : α → α → Prop} {Q : β → β → Prop} {S : α → β → Prop}
    (h : S ∈ smorbar P Q) {x : α} {z : β} (hxz : S x z) : z ∈ fld Q := by
  rw [h.1.2]
  exact ⟨x, hxz⟩

private theorem smor_of_empty {P : α → α → Prop} {Q : β → β → Prop}
    (hP : ∀ x y, ¬P x y) (hQ : ∀ x y, ¬Q x y) : smor P Q := by
  refine ⟨rNull, ⟨mem_arrow_one_one.2 ⟨fun x y z h => (rNull_apply _ _ h.1).elim,
    fun x y z h => (rNull_apply _ _ h.1).elim⟩, ?_⟩, ?_⟩
  · ext z
    constructor
    · rintro ⟨w, h | h⟩
      · exact (hQ z w h).elim
      · exact (hQ w z h).elim
    · rintro ⟨x, h⟩
      exact (rNull_apply _ _ h).elim
  · funext x y
    apply propext
    rw [semi_apply]
    exact ⟨fun h => (hP x y h).elim, fun ⟨z, w, ⟨h, _⟩, _⟩ => (rNull_apply _ _ h).elim⟩

/-- Likeness of `P` with a copy `graph f ;P` of it, `f` one-one on `C'P` (cf. ✱151·4). -/
private theorem smorbar_graph {P : α → α → Prop} {f : α → γ}
    (hf : ∀ x y, x ∈ fld P → y ∈ fld P → f x = f y → x = y) :
    graph f ↾ fld P ∈ smorbar (graph f ⁏ P) P := by
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro X Y z ⟨⟨hX, -⟩, ⟨hY, -⟩⟩
    exact (hX : X = f z).trans (hY : Y = f z).symm
  · rintro X x y ⟨⟨hx, hxf⟩, ⟨hy, hyf⟩⟩
    exact hf x y hxf hyf ((hx : X = f x).symm.trans hy)
  · ext x
    exact ⟨fun hx => ⟨f x, rfl, hx⟩, fun ⟨_, _, hx⟩ => hx⟩
  · funext X Y
    apply propext
    rw [semi_apply, semi_apply]
    constructor
    · rintro ⟨z, w, ⟨hz, hw⟩, hzw⟩
      exact ⟨z, w, ⟨⟨hz, ⟨w, Or.inl hzw⟩⟩, ⟨hw, ⟨z, Or.inr hzw⟩⟩⟩, hzw⟩
    · rintro ⟨z, w, ⟨hz, hw⟩, hzw⟩
      exact ⟨z, w, ⟨hz.1, hw.1⟩, hzw⟩

private theorem mem_fld_graph_semi {P : α → α → Prop} {f : α → γ} {X : γ} :
    X ∈ fld (graph f ⁏ P) ↔ ∃ y, y ∈ fld P ∧ X = f y := by
  rw [fld_semi_graph]
  rfl

/-- Likeness of the sums of mutually exclusive relations (cf. ✱160·3). -/
private theorem smorbar_rsum {P₁ Q₁ : α → α → Prop} {P₂ Q₂ : β → β → Prop}
    {S₁ S₂ : α → β → Prop} (h₁ : S₁ ∈ smorbar P₁ P₂) (h₂ : S₂ ∈ smorbar Q₁ Q₂)
    (d₁ : fld P₁ ∩ fld Q₁ = Λ) (d₂ : fld P₂ ∩ fld Q₂ = Λ) :
    S₁ ⊍ S₂ ∈ smorbar (P₁ ⤉ Q₁) (P₂ ⤉ Q₂) := by
  have e₁ := eqΛ.1 d₁
  have e₂ := eqΛ.1 d₂
  obtain ⟨a1, b1⟩ := mem_arrow_one_one.1 h₁.1.1
  obtain ⟨a2, b2⟩ := mem_arrow_one_one.1 h₂.1.1
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨hx | hx, hy | hy⟩
    · exact a1 x y z ⟨hx, hy⟩
    · exact (e₂ z ⟨smorbar_codom h₁ hx, smorbar_codom h₂ hy⟩).elim
    · exact (e₂ z ⟨smorbar_codom h₁ hy, smorbar_codom h₂ hx⟩).elim
    · exact a2 x y z ⟨hx, hy⟩
  · rintro x y z ⟨hy | hy, hz | hz⟩
    · exact b1 x y z ⟨hy, hz⟩
    · exact (e₁ x ⟨smorbar_dom h₁ hy, smorbar_dom h₂ hz⟩).elim
    · exact (e₁ x ⟨smorbar_dom h₁ hz, smorbar_dom h₂ hy⟩).elim
    · exact b2 x y z ⟨hy, hz⟩
  · rw [fld_rsum, h₁.1.2, h₂.1.2]
    ext z
    constructor
    · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
      · exact ⟨x, Or.inl hx⟩
      · exact ⟨x, Or.inr hx⟩
    · rintro ⟨x, hx | hx⟩
      · exact Or.inl ⟨x, hx⟩
      · exact Or.inr ⟨x, hx⟩
  · funext x y
    apply propext
    rw [semi_apply]
    constructor
    · rintro ((h | h) | ⟨hx, hy⟩)
      · rw [h₁.2] at h
        obtain ⟨z, w, ⟨hxz, hyw⟩, hzw⟩ := (semi_apply S₁ P₂ x y).1 h
        exact ⟨z, w, ⟨Or.inl hxz, Or.inl hyw⟩, Or.inl (Or.inl hzw)⟩
      · rw [h₂.2] at h
        obtain ⟨z, w, ⟨hxz, hyw⟩, hzw⟩ := (semi_apply S₂ Q₂ x y).1 h
        exact ⟨z, w, ⟨Or.inr hxz, Or.inr hyw⟩, Or.inl (Or.inr hzw)⟩
      · obtain ⟨z, hxz⟩ := smorbar_fld h₁ hx
        obtain ⟨w, hyw⟩ := smorbar_fld h₂ hy
        exact ⟨z, w, ⟨Or.inl hxz, Or.inr hyw⟩,
          Or.inr ⟨smorbar_codom h₁ hxz, smorbar_codom h₂ hyw⟩⟩
    · rintro ⟨z, w, ⟨hxz, hyw⟩, (hzw | hzw) | ⟨hz, hw⟩⟩
      · have hz : z ∈ fld P₂ := ⟨w, Or.inl hzw⟩
        have hw : w ∈ fld P₂ := ⟨z, Or.inr hzw⟩
        have hxz' : S₁ x z := Or.resolve_right hxz fun h => e₂ z ⟨hz, smorbar_codom h₂ h⟩
        have hyw' : S₁ y w := Or.resolve_right hyw fun h => e₂ w ⟨hw, smorbar_codom h₂ h⟩
        refine Or.inl (Or.inl ?_)
        rw [h₁.2]
        exact (semi_apply S₁ P₂ x y).2 ⟨z, w, ⟨hxz', hyw'⟩, hzw⟩
      · have hz : z ∈ fld Q₂ := ⟨w, Or.inl hzw⟩
        have hw : w ∈ fld Q₂ := ⟨z, Or.inr hzw⟩
        have hxz' : S₂ x z := Or.resolve_left hxz fun h => e₂ z ⟨smorbar_codom h₁ h, hz⟩
        have hyw' : S₂ y w := Or.resolve_left hyw fun h => e₂ w ⟨smorbar_codom h₁ h, hw⟩
        refine Or.inl (Or.inr ?_)
        rw [h₂.2]
        exact (semi_apply S₂ Q₂ x y).2 ⟨z, w, ⟨hxz', hyw'⟩, hzw⟩
      · have hxz' : S₁ x z := Or.resolve_right hxz fun h => e₂ z ⟨hz, smorbar_codom h₂ h⟩
        have hyw' : S₂ y w := Or.resolve_left hyw fun h => e₂ w ⟨smorbar_codom h₁ h, hw⟩
        exact Or.inr ⟨smorbar_dom h₁ hxz', smorbar_dom h₂ hyw'⟩

private theorem smor_rsum {P₁ Q₁ : α → α → Prop} {P₂ Q₂ : β → β → Prop}
    (h₁ : smor P₁ P₂) (h₂ : smor Q₁ Q₂) (d₁ : fld P₁ ∩ fld Q₁ = Λ)
    (d₂ : fld P₂ ∩ fld Q₂ = Λ) : smor (P₁ ⤉ Q₁) (P₂ ⤉ Q₂) := by
  obtain ⟨S₁, hS₁⟩ := h₁
  obtain ⟨S₂, hS₂⟩ := h₂
  exact ⟨_, smorbar_rsum hS₁ hS₂ d₁ d₂⟩

private theorem fld_addFirst {Q : α → α → Prop} {b z : α} (hne : (fld Q).Nonempty) :
    z ∈ fld (b ⇷ Q) ↔ z = b ∨ z ∈ fld Q := by
  obtain ⟨q, hq⟩ := hne
  constructor
  · rintro ⟨w, (⟨e, -⟩ | h) | (⟨-, h⟩ | h)⟩
    · exact Or.inl e
    · exact Or.inr ⟨w, Or.inl h⟩
    · exact Or.inr h
    · exact Or.inr ⟨w, Or.inr h⟩
  · rintro (e | hz)
    · rw [e]
      exact ⟨q, Or.inl (Or.inl ⟨rfl, hq⟩)⟩
    · exact ⟨b, Or.inr (Or.inl ⟨rfl, hz⟩)⟩

/-- Likeness of `x ⇷ P` (cf. ✱161·33). -/
private theorem smorbar_addFirst {Q₁ : α → α → Prop} {Q₂ : β → β → Prop} {S : α → β → Prop}
    {b₁ : α} {b₂ : β} (h : S ∈ smorbar Q₁ Q₂) (hb₁ : b₁ ∉ fld Q₁) (hb₂ : b₂ ∉ fld Q₂)
    (hne : (fld Q₁).Nonempty) : S ⊍ b₁ ↓ b₂ ∈ smorbar (b₁ ⇷ Q₁) (b₂ ⇷ Q₂) := by
  obtain ⟨a1, b1'⟩ := mem_arrow_one_one.1 h.1.1
  have hne2 : (fld Q₂).Nonempty := by
    obtain ⟨q, hq⟩ := hne
    obtain ⟨z, hz⟩ := smorbar_fld h hq
    exact ⟨z, smorbar_codom h hz⟩
  have cp : ∀ x z, (b₁ ↓ b₂) x z ↔ x = b₁ ∧ z = b₂ := fun x z => couple_apply b₁ b₂ x z
  refine ⟨⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨hx, hy⟩
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact a1 x y z ⟨hx, hy⟩
    · exact absurd (smorbar_codom h hx) (by rw [((cp y z).1 hy).2]; exact hb₂)
    · exact absurd (smorbar_codom h hy) (by rw [((cp x z).1 hx).2]; exact hb₂)
    · exact ((cp x z).1 hx).1.trans ((cp y z).1 hy).1.symm
  · rintro x y z ⟨hy, hz⟩
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · exact b1' x y z ⟨hy, hz⟩
    · exact absurd (smorbar_dom h hy) (by rw [((cp x z).1 hz).1]; exact hb₁)
    · exact absurd (smorbar_dom h hz) (by rw [((cp x y).1 hy).1]; exact hb₁)
    · exact ((cp x y).1 hy).2.trans ((cp x z).1 hz).2.symm
  · ext z
    rw [fld_addFirst hne2]
    constructor
    · rintro (e | hz)
      · exact ⟨b₁, Or.inr ((cp b₁ z).2 ⟨rfl, e⟩)⟩
      · obtain ⟨x, hx⟩ : z ∈ codom S := by rw [← h.1.2]; exact hz
        exact ⟨x, Or.inl hx⟩
    · rintro ⟨x, hx | hx⟩
      · exact Or.inr (smorbar_codom h hx)
      · exact Or.inl ((cp x z).1 hx).2
  · funext x y
    apply propext
    rw [semi_apply]
    constructor
    · rintro (⟨e, hy⟩ | hxy)
      · obtain ⟨w, hyw⟩ := smorbar_fld h hy
        exact ⟨b₂, w, ⟨Or.inr ((cp x b₂).2 ⟨e, rfl⟩), Or.inl hyw⟩,
          Or.inl ⟨rfl, smorbar_codom h hyw⟩⟩
      · rw [h.2] at hxy
        obtain ⟨z, w, ⟨hxz, hyw⟩, hzw⟩ := (semi_apply S Q₂ x y).1 hxy
        exact ⟨z, w, ⟨Or.inl hxz, Or.inl hyw⟩, Or.inr hzw⟩
    · rintro ⟨z, w, ⟨hxz, hyw⟩, ⟨ez, hw⟩ | hzw⟩
      · have hx : x = b₁ := by
          rcases hxz with hxz | hxz
          · exact absurd (smorbar_codom h hxz) (by rw [ez]; exact hb₂)
          · exact ((cp x z).1 hxz).1
        have hyw' : S y w := by
          rcases hyw with hyw | hyw
          · exact hyw
          · exact absurd hw (by rw [((cp y w).1 hyw).2]; exact hb₂)
        exact Or.inl ⟨hx, smorbar_dom h hyw'⟩
      · have hz : z ∈ fld Q₂ := ⟨w, Or.inl hzw⟩
        have hw : w ∈ fld Q₂ := ⟨z, Or.inr hzw⟩
        have hxz' : S x z := by
          rcases hxz with hxz | hxz
          · exact hxz
          · exact absurd hz (by rw [((cp x z).1 hxz).2]; exact hb₂)
        have hyw' : S y w := by
          rcases hyw with hyw | hyw
          · exact hyw
          · exact absurd hw (by rw [((cp y w).1 hyw).2]; exact hb₂)
        refine Or.inr ?_
        rw [h.2]
        exact (semi_apply S Q₂ x y).2 ⟨z, w, ⟨hxz', hyw'⟩, hzw⟩

private theorem smor_addFirst {Q₁ : α → α → Prop} {Q₂ : β → β → Prop} {b₁ : α} {b₂ : β}
    (h : smor Q₁ Q₂) (hb₁ : b₁ ∉ fld Q₁) (hb₂ : b₂ ∉ fld Q₂) :
    smor (b₁ ⇷ Q₁) (b₂ ⇷ Q₂) := by
  obtain ⟨S, hS⟩ := h
  by_cases hne : (fld Q₁).Nonempty
  · exact ⟨_, smorbar_addFirst hS hb₁ hb₂ hne⟩
  · have e1 : ∀ x y, ¬Q₁ x y := fun x y hxy => hne ⟨x, ⟨y, Or.inl hxy⟩⟩
    have e2 : ∀ x y, ¬Q₂ x y := by
      intro x y hxy
      obtain ⟨a, ha⟩ : x ∈ codom S := by rw [← hS.1.2]; exact ⟨y, Or.inl hxy⟩
      exact hne ⟨a, smorbar_dom hS ha⟩
    apply smor_of_empty
    · rintro x y (⟨-, ⟨w, hw | hw⟩⟩ | h)
      · exact e1 _ _ hw
      · exact e1 _ _ hw
      · exact e1 _ _ h
    · rintro x y (⟨-, ⟨w, hw | hw⟩⟩ | h)
      · exact e2 _ _ hw
      · exact e2 _ _ hw
      · exact e2 _ _ h

private theorem smor_cnv {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q) :
    smor P˘ Q˘ := by
  obtain ⟨S, ⟨hS, hcod⟩, rfl⟩ := h
  exact ⟨S, ⟨hS, by rw [fld_cnv]; exact hcod⟩, cnv_semi S Q⟩

private theorem addLast_cnv (P : α → α → Prop) (x : α) : (P ⇸ x)˘ = x ⇷ P˘ := by
  funext a b
  apply propext
  show P b a ∨ b ∈ fld P ∧ a = x ↔ (a = x ∧ b ∈ fld P˘) ∨ P˘ a b
  rw [fld_cnv]
  constructor
  · rintro (h | ⟨hb, ha⟩)
    · exact Or.inr h
    · exact Or.inl ⟨ha, hb⟩
  · rintro (⟨ha, hb⟩ | h)
    · exact Or.inr ⟨hb, ha⟩
    · exact Or.inl h

private theorem smor_addLast {Q₁ : α → α → Prop} {Q₂ : β → β → Prop} {b₁ : α} {b₂ : β}
    (h : smor Q₁ Q₂) (hb₁ : b₁ ∉ fld Q₁) (hb₂ : b₂ ∉ fld Q₂) :
    smor (Q₁ ⇸ b₁) (Q₂ ⇸ b₂) := by
  have := smor_cnv (smor_addFirst (b₁ := b₁) (b₂ := b₂) (smor_cnv h)
    (by rw [fld_cnv]; exact hb₁) (by rw [fld_cnv]; exact hb₂))
  rw [← addLast_cnv, ← addLast_cnv] at this
  exact this

/-- `↓c ; ι` is the descriptive relation of `ι'x ↓ c` to `x`. -/
private theorem coupleR_iota (c : Set β) :
    (coupleR c ⨾ iota : (Set α → Set β → Prop) → α → Prop) = graph (fun x : α => ι x ↓ c) := by
  funext X x
  apply propext
  constructor
  · rintro ⟨Y, hXY, hYx⟩
    have h1 : X = Y ↓ c := hXY
    have h2 : Y = ι x := hYx
    rw [h1, h2]
    rfl
  · intro hX
    exact ⟨ι x, hX, rfl⟩

private theorem coupleL_iota (d : Set β) :
    (coupleL d ⨾ iota : (Set β → Set α → Prop) → α → Prop) = graph (fun y : α => d ↓ ι y) := by
  funext X y
  apply propext
  constructor
  · rintro ⟨Y, hXY, hYy⟩
    have h1 : X = d ↓ Y := hXY
    have h2 : Y = ι y := hYy
    rw [h1, h2]
    rfl
  · intro hX
    exact ⟨ι y, hX, rfl⟩

private theorem couple_ne_of_empty {a : Set α} {b : Set β} {c : Set α} {d : Set β} (x : α)
    (ha : x ∈ a) (hc : c ⊆ Λ) : a ↓ b ≠ c ↓ d := by
  intro h
  have := (couple_eq_couple_iff.1 h).1
  rw [this] at ha
  exact eqΛ.1 rfl x (hc ha)

private theorem inj_iota_left (c : Set β) {x y : α} (h : ι x ↓ c = ι y ↓ c) : x = y :=
  unitCls_injective (couple_eq_couple_iff.1 h).1

private theorem inj_iota_right (d : Set β) {x y : α} (h : d ↓ ι x = d ↓ ι y) : x = y :=
  unitCls_injective (couple_eq_couple_iff.1 h).2

/-- `P + Q` is the sum of mutually exclusive copies of `P` and `Q` (✱180·01). -/
private theorem rplus_eq (P : α → α → Prop) (Q : β → β → Prop) :
    P +ᵣ Q = (graph (fun x : α => ι x ↓ (Λ ∩ fld Q)) ⁏ P) ⤉
      (graph (fun y : β => (Λ ∩ fld P) ↓ ι y) ⁏ Q) := by
  show (coupleR (Λ ∩ fld Q) ⁏ iota ⁏ P) ⤉ (coupleL (Λ ∩ fld P) ⁏ iota ⁏ Q) = _
  rw [semi_semi, semi_semi, coupleR_iota, coupleL_iota]

private theorem rplus_disj (P : α → α → Prop) (Q : β → β → Prop) :
    fld (graph (fun x : α => ι x ↓ (Λ ∩ fld Q)) ⁏ P) ∩
      fld (graph (fun y : β => (Λ ∩ fld P) ↓ ι y) ⁏ Q) = Λ := by
  rw [eqΛ]
  rintro X ⟨h1, h2⟩
  obtain ⟨x, -, rfl⟩ := mem_fld_graph_semi.1 h1
  obtain ⟨y, -, e⟩ := mem_fld_graph_semi.1 h2
  exact couple_ne_of_empty x rfl Set.inter_subset_left e

private theorem smor_left_copy (P : α → α → Prop) (c : Set β) :
    smor (graph (fun x : α => ι x ↓ c) ⁏ P) P :=
  ⟨_, smorbar_graph fun x y _ _ h => inj_iota_left c h⟩

private theorem smor_right_copy (P : α → α → Prop) (d : Set β) :
    smor (graph (fun y : α => d ↓ ι y) ⁏ P) P :=
  ⟨_, smorbar_graph fun x y _ _ h => inj_iota_right d h⟩

/-- `P ⤉ Q` is like `P + Q` when `C'P ∩ C'Q = Λ` (✱180·32). -/
private theorem smor_rsum_rplus {P Q : α → α → Prop} (hd : fld P ∩ fld Q = Λ) :
    smor (P ⤉ Q) (P +ᵣ Q) := by
  rw [rplus_eq]
  exact smor_rsum (smor_symm (smor_left_copy P _)) (smor_symm (smor_right_copy Q _)) hd
    (rplus_disj P Q)

/-- Likeness is preserved by the arithmetical sum. -/
private theorem smor_rplus {P₁ Q₁ : α → α → Prop} {P₂ Q₂ : β → β → Prop}
    (h₁ : smor P₁ P₂) (h₂ : smor Q₁ Q₂) : smor (P₁ +ᵣ Q₁) (P₂ +ᵣ Q₂) := by
  rw [rplus_eq, rplus_eq]
  exact smor_rsum
    (smor_trans (smor_left_copy P₁ _) (smor_trans h₁ (smor_symm (smor_left_copy P₂ _))))
    (smor_trans (smor_right_copy Q₁ _) (smor_trans h₂ (smor_symm (smor_right_copy Q₂ _))))
    (rplus_disj P₁ Q₁) (rplus_disj P₂ Q₂)

/-- `Nr'P = N₀r'P₁ +̇ N₀r'Q₁` when `P smor P₁ + Q₁` (in every type `γ`). -/
private theorem nr_eq_nrAdd {P P₁ Q₁ : α → α → Prop} (h : smor P (P₁ +ᵣ Q₁)) :
    nr γ P = (n₀r P₁ ∔ n₀r Q₁ : Set (γ → γ → Prop)) := by
  ext R
  constructor
  · intro hR
    exact ⟨P₁, Q₁, ⟨rfl, rfl⟩, smor_trans hR h⟩
  · rintro ⟨P', Q', ⟨e1, e2⟩, hR⟩
    have h1 := n₀r_eq_n₀r_iff.1 e1
    have h2 := n₀r_eq_n₀r_iff.1 e2
    exact smor_trans hR (smor_trans (smor_rplus (smor_symm h1) (smor_symm h2)) (smor_symm h))

private theorem addFirstDot_eq (x : β) (P : α → α → Prop) :
    addFirstDot x P = (ι x ↓ (Λ ∩ fld P)) ⇷ (graph (fun y : α => clsT Λ x ↓ ι y) ⁏ P) := by
  show (ι x ↓ (Λ ∩ fld P)) ⇷ (coupleL (clsT Λ x) ⁏ iota ⁏ P) = _
  rw [semi_semi, coupleL_iota]

private theorem addLastDot_eq (P : α → α → Prop) (x : β) :
    addLastDot P x = (graph (fun y : α => ι y ↓ clsT Λ x) ⁏ P) ⇸ ((Λ ∩ fld P) ↓ ι x) := by
  show (coupleR (clsT Λ x) ⁏ iota ⁏ P) ⇸ ((Λ ∩ fld P) ↓ ι x) = _
  rw [semi_semi, coupleR_iota]

private theorem smor_addFirstDot {Q P' : α → α → Prop} {b : α} (x : β) (hb : b ∉ fld Q)
    (h : smor P' Q) : smor (b ⇷ Q) (addFirstDot x P') := by
  rw [addFirstDot_eq]
  refine smor_addFirst (smor_trans (smor_symm h) (smor_symm (smor_right_copy P' _))) hb ?_
  intro hm
  obtain ⟨y, -, e⟩ := mem_fld_graph_semi.1 hm
  exact couple_ne_of_empty x rfl (by rw [clsT_eq]) e

private theorem smor_addLastDot {Q P' : α → α → Prop} {b : α} (x : β) (hb : b ∉ fld Q)
    (h : smor P' Q) : smor (Q ⇸ b) (addLastDot P' x) := by
  rw [addLastDot_eq]
  refine smor_addLast (smor_trans (smor_symm h) (smor_symm (smor_left_copy P' _))) hb ?_
  intro hm
  obtain ⟨y, -, e⟩ := mem_fld_graph_semi.1 hm
  exact couple_ne_of_empty y rfl Set.inter_subset_left e.symm

/-- `Nr'(b ⇷ Q) = 1̇ +̇ N₀r'Q` (in every type `γ`; `β` is the type of the apparent variable). -/
private theorem nr_eq_nrOneAdd [Nonempty β] {Q : α → α → Prop} {b : α} (hb : b ∉ fld Q) :
    nr γ (b ⇷ Q) = (nrOneAdd β (n₀r Q) : Set (γ → γ → Prop)) := by
  obtain ⟨x₀⟩ := ‹Nonempty β›
  ext R
  constructor
  · intro hR
    exact ⟨Q, x₀, rfl, smor_trans hR (smor_addFirstDot x₀ hb (smor_refl Q))⟩
  · rintro ⟨P', x, e, hR⟩
    have h := n₀r_eq_n₀r_iff.1 e
    exact smor_trans hR (smor_symm (smor_addFirstDot x hb h))

private theorem nr_eq_nrAddOne [Nonempty β] {Q : α → α → Prop} {b : α} (hb : b ∉ fld Q) :
    nr γ (Q ⇸ b) = (nrAddOne β (n₀r Q) : Set (γ → γ → Prop)) := by
  obtain ⟨x₀⟩ := ‹Nonempty β›
  ext R
  constructor
  · intro hR
    exact ⟨Q, x₀, rfl, smor_trans hR (smor_addLastDot x₀ hb (smor_refl Q))⟩
  · rintro ⟨P', x, e, hR⟩
    have h := n₀r_eq_n₀r_iff.1 e
    exact smor_trans hR (smor_symm (smor_addLastDot x hb h))

/-- Beginnings are preserved by likeness (✱151·5). -/
private theorem beg_of_smor {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q)
    (hb : (refs Beg Q).Nonempty) : (refs Beg P).Nonempty := by
  obtain ⟨S, ⟨hS, hcod⟩, rfl⟩ := h
  obtain ⟨-, h2⟩ := mem_arrow_one_one.1 hS
  obtain ⟨b, ⟨w, hbw⟩, hbn⟩ := hb
  obtain ⟨x, hxb⟩ : b ∈ codom S := by rw [← hcod]; exact ⟨w, Or.inl hbw⟩
  obtain ⟨y, hyw⟩ : w ∈ codom S := by rw [← hcod]; exact ⟨b, Or.inr hbw⟩
  refine ⟨x, ⟨y, (semi_apply S Q x y).2 ⟨b, w, ⟨hxb, hyw⟩, hbw⟩⟩, ?_⟩
  rintro ⟨z, hzx⟩
  obtain ⟨a, a', ⟨-, hxa'⟩, haa'⟩ := (semi_apply S Q z x).1 hzx
  have e : a' = b := h2 x a' b ⟨hxa', hxb⟩
  rw [e] at haa'
  exact hbn ⟨a, haa'⟩

/-- `ᗡ'Q ∈ 1` is preserved by likeness. -/
private theorem codom_one_of_smor {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q)
    (hc : codom Q ∈ (one : Set (Set β))) : codom P ∈ (one : Set (Set α)) := by
  obtain ⟨S, ⟨hS, hcod⟩, rfl⟩ := h
  obtain ⟨h1, -⟩ := mem_arrow_one_one.1 hS
  obtain ⟨c, hc⟩ := mem_one_iff.1 hc
  obtain ⟨a, hac⟩ : c ∈ codom Q := (hc c).2 rfl
  obtain ⟨x0, hx0⟩ : c ∈ codom S := by rw [← hcod]; exact ⟨a, Or.inr hac⟩
  obtain ⟨z, hza⟩ : a ∈ codom S := by rw [← hcod]; exact ⟨c, Or.inl hac⟩
  refine mem_one_iff.2 ⟨x0, fun y => ⟨?_, fun e => ?_⟩⟩
  · rintro ⟨u, hu⟩
    obtain ⟨b, b', ⟨-, hyb'⟩, hbb'⟩ := (semi_apply S Q u y).1 hu
    have e : b' = c := (hc b').1 ⟨b, hbb'⟩
    rw [e] at hyb'
    exact h1 y x0 c ⟨hyb', hx0⟩
  · rw [e]
    exact ⟨z, (semi_apply S Q z x0).2 ⟨a, c, ⟨hza, hx0⟩, hac⟩⟩

/-- Two couples of distinct terms are like (✱153). -/
private theorem smor_couple {a b : α} {c d : β} (hab : a ≠ b) (hcd : c ≠ d) :
    smor (a ↓ b) (c ↓ d) := by
  refine ⟨(a ↓ c) ⊍ (b ↓ d), ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y z ⟨hx | hx, hy | hy⟩ <;> rw [couple_apply] at hx hy
    · exact hx.1.trans hy.1.symm
    · exact (hcd (hx.2.symm.trans hy.2)).elim
    · exact (hcd (hy.2.symm.trans hx.2)).elim
    · exact hx.1.trans hy.1.symm
  · rintro x y z ⟨hy | hy, hz | hz⟩ <;> rw [couple_apply] at hy hz
    · exact hy.2.trans hz.2.symm
    · exact (hab (hy.1.symm.trans hz.1)).elim
    · exact (hab (hz.1.symm.trans hy.1)).elim
    · exact hy.2.trans hz.2.symm
  · ext z
    constructor
    · rintro ⟨w, h | h⟩ <;> rw [couple_apply] at h
      · exact ⟨a, Or.inl ((couple_apply a c a z).2 ⟨rfl, h.1⟩)⟩
      · exact ⟨b, Or.inr ((couple_apply b d b z).2 ⟨rfl, h.2⟩)⟩
    · rintro ⟨x, h | h⟩ <;> rw [couple_apply] at h
      · exact ⟨d, Or.inl ((couple_apply c d z d).2 ⟨h.2, rfl⟩)⟩
      · exact ⟨c, Or.inr ((couple_apply c d c z).2 ⟨rfl, h.2⟩)⟩
  · funext x y
    apply propext
    rw [semi_apply, couple_apply]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨c, d, ⟨Or.inl ((couple_apply a c x c).2 ⟨hx, rfl⟩),
        Or.inr ((couple_apply b d y d).2 ⟨hy, rfl⟩)⟩, (couple_apply c d c d).2 ⟨rfl, rfl⟩⟩
    · rintro ⟨z, w, ⟨hxz, hyw⟩, hzw⟩
      rw [couple_apply] at hzw
      obtain ⟨rfl, rfl⟩ := hzw
      rcases hxz with hxz | hxz <;> rcases hyw with hyw | hyw <;> rw [couple_apply] at hxz hyw
      · exact (hcd hyw.2.symm).elim
      · exact ⟨hxz.1, hyw.1⟩
      · exact (hcd hxz.2).elim
      · exact (hcd hxz.2).elim

/-- A relation like a couple of distinct terms is such a couple. -/
private theorem two_r_of_smor {R : β → β → Prop} {x y : α} (h : smor R (x ↓ y)) (hxy : x ≠ y) :
    R ∈ (two_r : Set (β → β → Prop)) := by
  obtain ⟨S, ⟨hS, hcod⟩, rfl⟩ := h
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS
  have hxf : x ∈ fld (x ↓ y) := ⟨y, Or.inl ((couple_apply x y x y).2 ⟨rfl, rfl⟩)⟩
  have hyf : y ∈ fld (x ↓ y) := ⟨x, Or.inr ((couple_apply x y x y).2 ⟨rfl, rfl⟩)⟩
  rw [hcod] at hxf hyf
  obtain ⟨a, ha⟩ := hxf
  obtain ⟨b, hb⟩ := hyf
  refine ⟨a, b, fun e => hxy (h2 a x y ⟨ha, by rw [e]; exact hb⟩), ?_⟩
  funext u v
  apply propext
  rw [semi_apply, couple_apply]
  constructor
  · rintro ⟨z, w, ⟨huz, hvw⟩, hzw⟩
    rw [couple_apply] at hzw
    obtain ⟨rfl, rfl⟩ := hzw
    exact ⟨h1 u a z ⟨huz, ha⟩, h1 v b w ⟨hvw, hb⟩⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨x, y, ⟨ha, hb⟩, (couple_apply x y x y).2 ⟨rfl, rfl⟩⟩

private theorem rEx_of_smor {P : α → α → Prop} {Q : β → β → Prop} (h : smor P Q)
    (hQ : rEx Q) : rEx P := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨a, b, hab⟩ := hQ
  obtain ⟨x, hxa⟩ : a ∈ codom S := by rw [← hS.1.2]; exact ⟨b, Or.inl hab⟩
  obtain ⟨y, hyb⟩ : b ∈ codom S := by rw [← hS.1.2]; exact ⟨a, Or.inr hab⟩
  refine ⟨x, y, ?_⟩
  rw [hS.2]
  exact (semi_apply S Q x y).2 ⟨a, b, ⟨hxa, hyb⟩, hab⟩

/-- A connected relation with a beginning and `ᗡ'P ∼∈ 1` relates two members of `ᗡ'P`. -/
private theorem rEx_fres_codom {P : α → α → Prop} (hc : P ∈ connex)
    (hb : (refs Beg P).Nonempty) (h1 : codom P ∉ (one : Set (Set α))) :
    rEx (P ⥏ codom P) := by
  obtain ⟨b, ⟨w, hbw⟩, -⟩ := hb
  have hw : w ∈ codom P := ⟨b, hbw⟩
  have : ∃ y, y ∈ codom P ∧ y ≠ w := by
    by_contra hn
    apply h1
    refine mem_one_iff.2 ⟨w, fun z => ⟨fun hz => ?_, fun e => by rw [e]; exact hw⟩⟩
    by_contra hzw
    exact hn ⟨z, hz, hzw⟩
  obtain ⟨y, hy, hne⟩ := this
  obtain ⟨u, huy⟩ := hy
  rcases cxne hc ⟨u, Or.inr huy⟩ ⟨b, Or.inr hbw⟩ hne with h | h
  · exact ⟨y, w, ⟨⟨⟨u, huy⟩, h⟩, hw⟩⟩
  · exact ⟨w, y, ⟨⟨hw, h⟩, ⟨u, huy⟩⟩⟩

private theorem rEx_fres_dom {P : α → α → Prop} (hc : P ∈ connex)
    (hb : (refs Beg P˘).Nonempty) (h1 : dom P ∉ (one : Set (Set α))) :
    rEx (P ⥏ dom P) := by
  obtain ⟨x, y, h⟩ := rEx_fres_codom (P := P˘) (pm202_11.1 hc) hb h1
  exact ⟨y, x, ⟨⟨h.2, h.1.2⟩, h.1.1⟩⟩

private theorem beg_addFirst {Q : α → α → Prop} {b : α} (hb : b ∉ fld Q)
    (hne : (fld Q).Nonempty) : Beg b (b ⇷ Q) := by
  obtain ⟨q, hq⟩ := hne
  refine ⟨⟨q, Or.inl ⟨rfl, hq⟩⟩, ?_⟩
  rintro ⟨z, ⟨-, h⟩ | h⟩
  · exact hb h
  · exact hb ⟨z, Or.inr h⟩

private theorem beg_addFirstDot {P' : α → α → Prop} (x : β) (hne : (fld P').Nonempty) :
    (refs Beg (addFirstDot x P')).Nonempty := by
  rw [addFirstDot_eq]
  refine ⟨_, beg_addFirst ?_ ?_⟩
  · intro hm
    obtain ⟨y, -, e⟩ := mem_fld_graph_semi.1 hm
    exact couple_ne_of_empty x rfl (by rw [clsT_eq]) e
  · obtain ⟨y, hy⟩ := hne
    exact ⟨_, mem_fld_graph_semi.2 ⟨y, hy, rfl⟩⟩

private theorem end_addLastDot {P' : α → α → Prop} (x : β) (hne : (fld P').Nonempty) :
    (refs Beg (addLastDot P' x)˘).Nonempty := by
  rw [addLastDot_eq, addLast_cnv]
  refine ⟨_, beg_addFirst ?_ ?_⟩
  · rw [fld_cnv]
    intro hm
    obtain ⟨y, -, e⟩ := mem_fld_graph_semi.1 hm
    exact couple_ne_of_empty y rfl Set.inter_subset_left e.symm
  · rw [fld_cnv]
    obtain ⟨y, hy⟩ := hne
    exact ⟨_, mem_fld_graph_semi.2 ⟨y, hy, rfl⟩⟩

/-- With `P ⊂̇ J`, a unique beginning and `ᗡ'P ∈ 1`, `P` is a couple (✱56·37). -/
private theorem couple_of_beg {P : α → α → Prop} (hJ : P ∈ rl J) {b : α}
    (hb : ∀ x, Beg x P ↔ x = b) (h1 : codom P ∈ (one : Set (Set α))) :
    ∃ y, b ≠ y ∧ P = b ↓ y := by
  obtain ⟨y, hy⟩ := mem_one_iff.1 h1
  have irr := mem_rl_J.1 hJ
  obtain ⟨⟨w, hbw⟩, hbn⟩ := (hb b).2 rfl
  have hwy : w = y := (hy w).1 ⟨b, hbw⟩
  refine ⟨y, fun e => hbn (by rw [e]; exact (hy y).2 rfl), ?_⟩
  funext u v
  apply propext
  rw [couple_apply]
  constructor
  · intro huv
    have hv : v = y := (hy v).1 ⟨u, huv⟩
    refine ⟨(hb u).1 ⟨⟨v, huv⟩, fun hu => ?_⟩, hv⟩
    have hu' : u = y := (hy u).1 hu
    rw [hu', hv] at huv
    exact irr y huv
  · rintro ⟨hu, hv⟩
    rw [hu, hv, ← hwy]
    exact hbw

/-- Removing the first terms of like relations `b ⇷ P'`, `c ⇷ Q'` leaves like relations. -/
private theorem smor_unaddFirst {P' : α → α → Prop} {Q' : β → β → Prop} {b : α} {c : β}
    (h : smor (b ⇷ P') (c ⇷ Q')) (hb : b ∉ fld P') (hcq : c ∉ fld Q')
    (hne : (fld P').Nonempty) : smor P' Q' := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS.1.1
  have hbf : b ∈ fld (b ⇷ P') := (fld_addFirst hne).2 (Or.inl rfl)
  obtain ⟨z, hbz⟩ := smorbar_fld hS hbf
  have hbc : S b c := by
    by_contra hn
    have hzc : z ≠ c := fun e => hn (by rw [← e]; exact hbz)
    have hzf : z ∈ fld (c ⇷ Q') := smorbar_codom hS hbz
    have hzQ : z ∈ fld Q' := by
      obtain ⟨w, (⟨e, -⟩ | h) | (⟨-, h⟩ | h)⟩ := hzf
      · exact (hzc e).elim
      · exact ⟨w, Or.inl h⟩
      · exact h
      · exact ⟨w, Or.inr h⟩
    have hcf : c ∈ fld (c ⇷ Q') := ⟨z, Or.inl (Or.inl ⟨rfl, hzQ⟩)⟩
    obtain ⟨a, hac⟩ : c ∈ codom S := by rw [← hS.1.2]; exact hcf
    have hab : (b ⇷ P') a b := by
      rw [hS.2]
      exact (semi_apply S _ a b).2 ⟨c, z, ⟨hac, hbz⟩, Or.inl ⟨rfl, hzQ⟩⟩
    rcases hab with ⟨-, h⟩ | h
    · exact hb h
    · exact hb ⟨a, Or.inr h⟩
  refine ⟨S ↾ fld Q', ⟨mem_arrow_one_one.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro x y w ⟨⟨hx, -⟩, ⟨hy, -⟩⟩
    exact h1 x y w ⟨hx, hy⟩
  · rintro x y w ⟨⟨hy, -⟩, ⟨hw, -⟩⟩
    exact h2 x y w ⟨hy, hw⟩
  · ext w
    constructor
    · intro hw
      have hw' : w ∈ fld (c ⇷ Q') := ⟨c, Or.inr (Or.inl ⟨rfl, hw⟩)⟩
      rw [hS.1.2] at hw'
      obtain ⟨x, hx⟩ := hw'
      exact ⟨x, hx, hw⟩
    · rintro ⟨x, -, hw⟩
      exact hw
  · funext x y
    apply propext
    rw [semi_apply]
    constructor
    · intro hxy
      have h' : (b ⇷ P') x y := Or.inr hxy
      rw [hS.2, semi_apply] at h'
      obtain ⟨u, w, ⟨hxu, hyw⟩, huw⟩ := h'
      have hxb : x ≠ b := fun e => hb (by rw [← e]; exact ⟨y, Or.inl hxy⟩)
      have huc : u ≠ c := fun e => hxb (h1 x b c ⟨by rw [← e]; exact hxu, hbc⟩)
      rcases huw with ⟨e, -⟩ | huw
      · exact (huc e).elim
      · exact ⟨u, w, ⟨⟨hxu, ⟨w, Or.inl huw⟩⟩, ⟨hyw, ⟨u, Or.inr huw⟩⟩⟩, huw⟩
    · rintro ⟨u, w, ⟨⟨hxu, hu⟩, ⟨hyw, -⟩⟩, huw⟩
      have h' : (S ⁏ (c ⇷ Q')) x y := (semi_apply S _ x y).2 ⟨u, w, ⟨hxu, hyw⟩, Or.inr huw⟩
      rw [← hS.2] at h'
      rcases h' with ⟨e, -⟩ | h'
      · rw [e] at hxu
        have e' := h2 b u c ⟨hxu, hbc⟩
        rw [e'] at hu
        exact (hcq hu).elim
      · exact h'

/-- `Nr'Λ̇ = 0_r`. -/
private theorem nr_rNull : nr α (rNull : β → β → Prop) = (zero_r : Set (α → α → Prop)) := by
  ext R
  constructor
  · rintro ⟨S, -, rfl⟩
    show S ⁏ rNull = rNull
    rw [eqΛr]
    intro x y h
    obtain ⟨z, w, -, hzw⟩ := (semi_apply S rNull x y).1 h
    exact rNull_apply z w hzw
  · intro hR
    have e : R = rNull := hR
    rw [e]
    exact smor_of_empty (fun x y h => rNull_apply x y h) (fun x y h => rNull_apply x y h)

/-- For a relation of mutually exclusive relations, `D` is one-one on the selections, so
`Prod'K` is like `Π'K` (cf. ✱174·461). -/
private theorem smor_prodR {K : (α → α → Prop) → (α → α → Prop) → Prop} (hK : K ∈ Rel2excl) :
    smor (prodR K) (relPi K) := by
  have hsel : ∀ M, M ∈ fld (relPi K) → M ∈ sel F (fld K) := by
    rintro M ⟨N, ⟨⟨hM, -⟩, -⟩ | ⟨⟨-, hM⟩, -⟩⟩ <;> exact hM
  have one : ∀ M N, M ∈ sel F (fld K) → N ∈ sel F (fld K) → dom M = dom N →
      ∀ u R, M u R → N u R := by
    intro M N hM hN e u R h
    have hu : u ∈ dom N := by rw [← e]; exact ⟨R, h⟩
    obtain ⟨R', hR'⟩ := hu
    have hR : R ∈ fld K := sel_codom hM h
    have hR'f : R' ∈ fld K := sel_codom hN hR'
    have huR : u ∈ fld R := (mem_sel_iff.1 hM).1.2 u R h
    have huR' : u ∈ fld R' := (mem_sel_iff.1 hN).1.2 u R' hR'
    by_cases e' : R' = R
    · rw [← e']
      exact hR'
    · exact (eqΛ.1 (hK R' R ⟨⟨hR'f, hR⟩, e'⟩) u ⟨huR', huR⟩).elim
  exact ⟨_, smorbar_graph (f := dom) fun M N hM hN e => by
    funext u R
    exact propext ⟨one M N (hsel M hM) (hsel N hN) e u R,
      one N M (hsel N hN) (hsel M hM) e.symm u R⟩⟩

end RelArith

end Helpers204

/-!
## [✱204] Elementary properties of series

*(Vol. 2, p. 547)*

> *Summary of* *204.
>
> In this number we give the definition and a few of the simpler properties of series. Most of the propositions of this number result immediately from those of *200, *201, and *202. Our definition is \[ \text{Ser} =\text{Rl}ʻJ\cap \text{trans}\cap \text{connex} \quad\text{Df}. \]
>
> We have
>
> *204·16. \(\vdash :P\in \text{Ser}.\equiv .P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.P^{3}\,\unicode{x2abd}\, J.\equiv .P\in \text{connex} .P_{\text{po}}\,\unicode{x2abd}\, J\)
>
> either of which might have been taken as the definition.
>
> After a few propositions giving other possible forms of the definition of series, we proceed to a set of propositions which follow immediately from those of *200, *201, and *202. Such are
>
> *204·2. \(\vdash :P\in \text{Ser}.\equiv .\breve{P} \in \text{Ser}\)
>
> *204·21. \(\vdash :P\in \text{Ser}.P\,\,\text{smor}\,\,Q.\supset .Q\in \text{Ser}\)
>
> *204·24. \(\vdash .\dot{\Lambda} \in \text{Ser}\)
>
> *204·25. \(\vdash :x\neq y.\equiv .x\downarrow y\in \text{Ser}\)
>
> Another important proposition on couples is
>
> *204·272. \(\vdash \colon\ldotp P\in \text{Ser}.\supset :\text{D}ʻP\in 1.\equiv .P\in 2_{r}.\equiv .\text{ᗡ}ʻP\in 1\)
>
> …

**Lean reading.** `Ser` is Defs/Part5's `rl J ∩ transR ∩ connex` (✱204·01; `mem_Ser` unfolds it), for
homogeneous `P : α → α → Prop` (relations of relations in ✱204·52–·58). The readings of
✱200–✱202 are kept. `D'P⥏` is `dom (opL fres P)`; `Rl'P` is `rl P`; `2_r`, `0_r`, `NR` are
`two_r`, `zero_r`, `NR α`; `N₀r''Ser` is `N₀r ʻʻ Ser`; `ᗡ'B` is `codom Beg` and `ᗡ'(B | Cnv)`
is `codom (Beg ⨾ Cnv)`; `Q × P` is `Q ×ᵣ P`; `Π'P`, `Σ'P`, `Π;P`, `Prod'P`, `Prod;P`,
`P exp Q`, `P^Q` are `relPi P`, `relSigma P`, `RelPi ⁏ P`, `prodR P`, `ProdR ⁏ P`,
`rexp P Q`, `rpow P Q`; `Rel³ arithm` is `Rel3arithm`. The hypothesis "`α ⊂ C'P . ∃!α . ⊃_α .
∃!α − P̆''α`" (every existent sub-class of `C'P` has a minimal member) is
`∀ A, A ⊆ fld P ∧ A.Nonempty → (A \ P˘ ʻʻ A).Nonempty`. Relation-numbers follow Defs/Part4:
`Nr'P` is `nr γ P` in an arbitrary type `γ`, an argument `Nr'X` of `+̇` is `N₀r'X` (normal
adjustment), `1̇ +̇ μ` and `μ +̇ 1̇` take the type `β` of their apparent variable explicitly (with
`[Nonempty β]`), and in ✱204·48·481 convention AT requires `γ` to be adequate for `Nr'P`
(`AdeqNr γ P`). The likeness of sums, of `x ⇷ P`, `P ⇸ x` and of couples (✱160, ✱161, ✱180,
✱181 of Part IV) needed for ✱204·45–·483 is proved here as private lemmas; ✱204·58·581·59 are
proved by applying ✱204·57 to `Π;P`, `Prod;P`, `P↓.,;Q` and carrying series over by one-one
correlations, instead of PM's ✱174 and ✱176. Transcription errors:
✱204·463 (`E!.B'Q`), ✱204·47 (`ᗡ'rP`), ✱204·51 (`χ` for `x`), ✱204·562 (`'Ser`).

**Status.** proved (all propositions; ✱204·46, ·461, ·463, ·47, ·48, ·481, ·482, ·483, ·51, ·562
proved (reading); see their docstrings).
-/

/-- ✱204·01 (Df). \(\text{Ser} = \text{Rl}ʻJ \cap \text{trans} \cap \text{connex} \quad\text{Df}\) -/
theorem pm204_01 {α : Type u} : (Ser : Set (α → α → Prop)) = rl J ∩ transR ∩ connex := rfl

/-- ✱204·1. \[\begin{align}\vdash : P \in \text{Ser} . &\equiv . P \,\unicode{x2abd}\, J . P^{2} \,\unicode{x2abd}\, P . P \in \text{connex}.\\ &\equiv . P \in \text{Rl}ʻJ . P \in \text{trans} . P \in \text{connex} \quad[(*204·01)]\end{align}\] -/
theorem pm204_1 {α : Type u} {P : α → α → Prop} :
    (P ∈ Ser ↔ (P ⪽ J ∧ rsq P ⪽ P) ∧ P ∈ connex) ∧
      ((P ⪽ J ∧ rsq P ⪽ P) ∧ P ∈ connex ↔ (P ∈ rl J ∧ P ∈ transR) ∧ P ∈ connex) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- ✱204·11. \[\begin{align}&\vdash \colon\ldotp P \in \text{Ser} . \equiv : P \,\unicode{x2abd}\, J . P^{2} \,\unicode{x2abd}\, P : x \in CʻP . \supset _{x} . \overrightarrow{P}ʻx \cup {℩}ʻx \cup \overleftarrow{P}ʻx = CʻP\\ &[*204·1 . *202·101]\end{align}\] -/
theorem pm204_11 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser ↔ (P ⪽ J ∧ rsq P ⪽ P) ∧ ∀ x, x ∈ fld P → refs P x ∪ ι x ∪ rels P x = fld P :=
  and_congr Iff.rfl pm202_101

/-- ✱204·12. \[\begin{align}\vdash \colon\colon P \in \text{Ser} . \equiv \colon\ldotp P \,\unicode{x2abd}\, &J . P^{2} \,\unicode{x2abd}\, P \colon\ldotp x, y \in CʻP . \supset _{x, y} :\\ &xPy . \lor . x = y . \lor . yPx \quad[*204·1 . *202·103]\end{align}\] -/
theorem pm204_12 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser ↔ (P ⪽ J ∧ rsq P ⪽ P) ∧
      ∀ x y, x ∈ fld P ∧ y ∈ fld P → (P x y ∨ x = y) ∨ P y x :=
  and_congr Iff.rfl mem_connex

/-- ✱204·121. \[\begin{align}\vdash \colon\colon P \in \text{Ser} . \equiv \colon\ldotp P \,\unicode{x2abd}\, J . P^{2} \,\unicode{x2abd}\, &P \colon\ldotp x, y \in CʻP . x \neq y . \supset _{x, y} :\\ &xPy . \lor . yPx \quad[*204·1 . *202·104]\end{align}\] -/
theorem pm204_121 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser ↔ (P ⪽ J ∧ rsq P ⪽ P) ∧
      ∀ x y, (x ∈ fld P ∧ y ∈ fld P) ∧ x ≠ y → P x y ∨ P y x :=
  and_congr Iff.rfl pm202_104

/-- ✱204·13. \(\vdash :P\in \text{Ser}.\supset .P^{2}\,\unicode{x2abd}\, J.P\dot{\cap} \breve{P} = \dot{\Lambda} \) -/
theorem pm204_13 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → rsq P ⪽ J ∧ P ⩀ P˘ = rNull := by
  rintro ⟨⟨hJ, ht⟩, -⟩
  have h := pm201_12 ht
  exact ⟨h.1.1 hJ, h.2.1 (h.1.1 hJ)⟩

/-- ✱204·14. \[\begin{align}&\vdash :P\in \text{Ser}. \equiv .P\dot{\cap} \breve{P} = \dot{\Lambda} .P^{2}\,\unicode{x2abd}\, P.P\in \text{connex} \\ &[*204·1.*50·47]\end{align}\] -/
theorem pm204_14 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser ↔ (P ⩀ P˘ = rNull ∧ rsq P ⪽ P) ∧ P ∈ connex := by
  constructor
  · intro h
    exact ⟨⟨(pm204_13 h).2, h.1.2⟩, h.2⟩
  · rintro ⟨⟨h0, ht⟩, hc⟩
    have h := pm201_12 ht
    exact ⟨⟨h.1.2 (h.2.2 h0), ht⟩, hc⟩

/-- ✱204·15. \(\vdash :P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.P^{3}\,\unicode{x2abd}\, J.\supset .P\in \text{trans}\) -/
theorem pm204_15 {α : Type u} {P : α → α → Prop} :
    (P ∈ connex ∧ rsq P ⪽ J) ∧ rcube P ⪽ J → P ∈ transR := by
  rintro ⟨⟨hc, h2⟩, h3⟩
  rw [mem_transR]
  rintro x y z ⟨hxy, hyz⟩
  have hne : x ≠ z := fun e => h2 x z ⟨y, hxy, hyz⟩ e
  rcases cxne hc ⟨y, Or.inl hxy⟩ ⟨y, Or.inr hyz⟩ hne with h | h
  · exact h
  · exact (h3 x x ⟨z, ⟨y, hxy, hyz⟩, h⟩ rfl).elim

/-- ✱204·151. \[\begin{align}&\vdash :P\in \text{connex} .P_{\text{po}}\,\unicode{x2abd}\, J.\supset .P\in \text{trans}\\ &[*204·15.*91·502·503·511]\end{align}\] -/
theorem pm204_151 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ∧ po P ⪽ J → P ∈ transR := by
  rintro ⟨hc, hJ⟩
  refine pm204_15 ⟨⟨hc, fun x y h => hJ x y ?_⟩, fun x y h => hJ x y ?_⟩
  · obtain ⟨z, hxz, hzy⟩ := h
    exact po_trans (po_of hxz) (po_of hzy)
  · obtain ⟨z, ⟨w, hxw, hwz⟩, hzy⟩ := h
    exact po_trans (po_trans (po_of hxw) (po_of hwz)) (po_of hzy)

/-- ✱204·16. \[\begin{align}&\vdash :P\in \text{Ser}. \equiv .P\in \text{connex} .P^{2}\,\unicode{x2abd}\, J.P^{3}\,\unicode{x2abd}\, J. \equiv .P\in \text{connex} .P_{\text{po}}\,\unicode{x2abd}\, J\\ &[*204·15·151.*200·36.*201·18]\end{align}\] -/
theorem pm204_16 {α : Type u} {P : α → α → Prop} :
    (P ∈ Ser ↔ (P ∈ connex ∧ rsq P ⪽ J) ∧ rcube P ⪽ J) ∧
      ((P ∈ connex ∧ rsq P ⪽ J) ∧ rcube P ⪽ J ↔ P ∈ connex ∧ po P ⪽ J) := by
  have a1 : P ∈ Ser → P ∈ connex ∧ po P ⪽ J := by
    rintro ⟨⟨hJ, ht⟩, hc⟩
    refine ⟨hc, ?_⟩
    rw [po_eq_of_transR ht]
    exact hJ
  have a2 : P ∈ connex ∧ po P ⪽ J → P ∈ Ser := by
    rintro ⟨hc, hJ⟩
    exact ⟨⟨fun x y h => hJ x y (po_of h), pm204_151 ⟨hc, hJ⟩⟩, hc⟩
  have a3 : P ∈ Ser → (P ∈ connex ∧ rsq P ⪽ J) ∧ rcube P ⪽ J := by
    intro h
    refine ⟨⟨h.2, (pm204_13 h).1⟩, ?_⟩
    rintro x y ⟨z, hxz, hzy⟩
    exact h.1.1 x y (h.1.2 x y ⟨z, h.1.2 x z hxz, hzy⟩)
  have a4 : (P ∈ connex ∧ rsq P ⪽ J) ∧ rcube P ⪽ J → P ∈ Ser := by
    intro h
    have ht := pm204_15 h
    exact ⟨⟨pm200_36 h.1.2, ht⟩, h.1.1⟩
  exact ⟨⟨a3, a4⟩, ⟨fun h => a1 (a4 h), fun h => a3 (a2 h)⟩⟩

/-- ✱204·2. \(\vdash :P\in \text{Ser}. \equiv .\breve{P} \in \text{Ser} \quad[*200·11.*201·11.*202·11]\) -/
theorem pm204_2 {α : Type u} {P : α → α → Prop} : P ∈ Ser ↔ P˘ ∈ Ser :=
  and_congr (and_congr pm200_11 pm201_11) pm202_11

/-- ✱204·21. \[\begin{align}&\vdash :P\in \text{Ser}.P \,\,\text{smor}\, \,Q.\supset .Q\in \text{Ser}\\ &[*200·211.*201·211.*202·211]\end{align}\] -/
theorem pm204_21 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} :
    P ∈ Ser ∧ smor P Q → Q ∈ Ser := by
  rintro ⟨⟨⟨hJ, ht⟩, hc⟩, h⟩
  exact ⟨⟨pm200_211 ⟨hJ, h⟩, pm201_211 ⟨ht, smor_symm h⟩⟩, pm202_211 ⟨hc, smor_symm h⟩⟩

/-- ✱204·22. \(\vdash :P\in \text{Ser}.\supset .\text{Nr}ʻP\subset \text{Ser} \quad[*204·21]\) -/
theorem pm204_22 {α : Type u} {γ : Type w} {P : α → α → Prop} :
    P ∈ Ser → nr γ P ⊆ Ser :=
  fun h _ hQ => pm204_21 ⟨h, smor_symm hQ⟩

/-- ✱204·23. \[\begin{align}&\vdash :P\in \text{Ser}. \equiv .\text{N}_{0}\text{r}ʻP\subset \text{Ser}. \equiv .\exists !\text{N}_{0}\text{r}ʻP\cap \text{Ser}\\ &[*200·22.*201·22.*202·22]\end{align}\] -/
theorem pm204_23 {α : Type u} {P : α → α → Prop} :
    (P ∈ Ser ↔ n₀r P ⊆ Ser) ∧ (n₀r P ⊆ Ser ↔ (n₀r P ∩ Ser).Nonempty) := by
  have h1 : P ∈ Ser → n₀r P ⊆ Ser := fun h Q hQ => pm204_21 ⟨h, smor_symm (mem_n₀r.1 hQ)⟩
  refine ⟨⟨h1, fun h => h (self_mem_n₀r P)⟩,
    ⟨fun h => ⟨P, self_mem_n₀r P, h (self_mem_n₀r P)⟩, ?_⟩⟩
  rintro ⟨Q, hQ, hQs⟩
  exact h1 (pm204_21 ⟨hQs, mem_n₀r.1 hQ⟩)

/-- ✱204·24. \(\vdash .\dot{\Lambda} \in \text{Ser} \quad[*200·3.*201·3.*202·3]\) -/
theorem pm204_24 {α : Type u} : (rNull : α → α → Prop) ∈ Ser :=
  ⟨⟨pm200_3, pm201_3⟩, pm202_3⟩

/-- ✱204·25. \(\vdash :x \neq y. \equiv . x\downarrow y \in \text{Ser} \quad[*200·31.*201·31.*202·31]\) -/
theorem pm204_25 {α : Type u} {x y : α} : x ≠ y ↔ x ↓ y ∈ Ser :=
  ⟨fun h => ⟨⟨pm200_31.1 h, pm201_31⟩, pm202_31⟩, fun h => pm200_31.2 h.1.1⟩

/-- ✱204·26. \[\begin{align}&\vdash :x \neq y.x \neq z.y \neq z.\supset .x\downarrow y\unicode{x21f8} z\in \text{Ser}\\ &[*200·31·41.*201·411.*202·411]\end{align}\] -/
theorem pm204_26 {α : Type u} {x y z : α} :
    (x ≠ y ∧ x ≠ z) ∧ y ≠ z → (x ↓ y) ⇸ z ∈ Ser := by
  rintro ⟨⟨hxy, hxz⟩, hyz⟩
  have hz : z ∉ fld (x ↓ y) := by
    rintro ⟨w, h | h⟩
    · exact hxz ((couple_apply x y z w).1 h).1.symm
    · exact hyz ((couple_apply x y w z).1 h).2.symm
  refine ⟨⟨pm200_41.1.2 (pm200_41.2.2 ⟨pm200_31.1 hxy, hz⟩), ?_⟩, pm202_411⟩
  exact pm201_411 ⟨Ne.symm hxz, Ne.symm hyz⟩

/-- ✱204·27. \(\vdash :P\in \text{Ser}.xPy.\text{D}ʻP={℩}ʻx.\supset .P=x\downarrow y\) -/
theorem pm204_27 {α : Type u} {P : α → α → Prop} {x y : α} :
    (P ∈ Ser ∧ P x y) ∧ dom P = ι x → P = x ↓ y := by
  rintro ⟨⟨hS, hxy⟩, hd⟩
  have irr := mem_rl_J.1 hS.1.1
  have hdom : ∀ z w, P z w → z = x := by
    intro z w h
    have : z ∈ dom P := ⟨w, h⟩
    rw [hd] at this
    exact this
  funext z w
  apply propext
  rw [couple_apply]
  constructor
  · intro h
    have hz := hdom z w h
    refine ⟨hz, ?_⟩
    rw [hz] at h
    by_contra hne
    rcases cxne hS.2 ⟨x, Or.inr h⟩ ⟨x, Or.inr hxy⟩ hne with h1 | h1
    · have := hdom w y h1
      rw [this] at h
      exact irr _ h
    · have := hdom y w h1
      rw [this] at hxy
      exact irr _ hxy
  · rintro ⟨rfl, rfl⟩
    exact hxy

/-- ✱204·271. \(\vdash :P\in \text{Ser}.\text{D}ʻP\in 1.\supset .P\in 2_r\) -/
theorem pm204_271 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser ∧ dom P ∈ one → P ∈ two_r := by
  rintro ⟨hS, h1⟩
  obtain ⟨x, hx⟩ := mem_one_iff.1 h1
  obtain ⟨y, hxy⟩ : x ∈ dom P := (hx x).2 rfl
  have hd : dom P = ι x := Set.ext fun z => hx z
  refine ⟨x, y, fun e => mem_rl_J.1 hS.1.1 x (by rw [← e] at hxy; exact hxy), ?_⟩
  exact pm204_27 ⟨⟨hS, hxy⟩, hd⟩

/-- ✱204·272. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.\supset :\text{D}ʻP\in 1.\equiv .P\in 2_r.\equiv .\text{ᗡ}ʻP\in 1\\ &[*204·271·2.*56·111]\end{align}\] -/
theorem pm204_272 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → ((dom P ∈ one ↔ P ∈ two_r) ∧ (P ∈ two_r ↔ codom P ∈ one)) := by
  intro hS
  have hdom : ∀ x y : α, dom (x ↓ y) = ι x := fun x y => by
    ext z
    exact ⟨fun ⟨w, h⟩ => ((couple_apply x y z w).1 h).1, fun h => ⟨y, (couple_apply x y z y).2 ⟨h, rfl⟩⟩⟩
  have hcod : ∀ x y : α, codom (x ↓ y) = ι y := fun x y => by
    ext z
    exact ⟨fun ⟨w, h⟩ => ((couple_apply x y w z).1 h).2, fun h => ⟨x, (couple_apply x y x z).2 ⟨rfl, h⟩⟩⟩
  have t1 : P ∈ two_r → dom P ∈ one := by
    rintro ⟨x, y, -, rfl⟩
    rw [hdom]
    exact ⟨x, rfl⟩
  have t2 : P ∈ two_r → codom P ∈ one := by
    rintro ⟨x, y, -, rfl⟩
    rw [hcod]
    exact ⟨y, rfl⟩
  have t3 : codom P ∈ one → P ∈ two_r := by
    intro h
    have h' : P˘ ∈ two_r := pm204_271 ⟨pm204_2.1 hS, h⟩
    obtain ⟨x, y, hne, e⟩ := h'
    refine ⟨y, x, Ne.symm hne, ?_⟩
    funext a b
    apply propext
    have h2 : P a b ↔ (x ↓ y) b a := Iff.of_eq (congrFun (congrFun e b) a)
    rw [h2, couple_apply, couple_apply]
    exact and_comm
  exact ⟨⟨fun h => pm204_271 ⟨hS, h⟩, t1⟩, ⟨t2, t3⟩⟩

/-- ✱204·3. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.x,y\in CʻP.\supset :x\neq y.{\sim}(yPx).\equiv .xPy\\ &[*202·5.*204·13]\end{align}\] -/
theorem pm204_3 {α : Type u} {P : α → α → Prop} {x y : α} :
    P ∈ Ser ∧ (x ∈ fld P ∧ y ∈ fld P) → (x ≠ y ∧ ¬P y x ↔ P x y) := by
  rintro ⟨hS, hx, hy⟩
  have h := pm202_5 (x := y) (y := x) ⟨⟨hS.2, (pm204_13 hS).1⟩, hy, hx⟩
  constructor
  · rintro ⟨hne, hn⟩
    exact h.1 ⟨Ne.symm hne, hn⟩
  · intro hxy
    exact ⟨Ne.symm (h.2 hxy).1, (h.2 hxy).2⟩

/-- ✱204·32. \(\vdash \colon\ldotp P\in \text{Ser}.x,y\in CʻP.\supset :\overrightarrow{P}ʻy\subset \overrightarrow{P}ʻx.\equiv .y\in \overrightarrow{P}ʻx\cup {℩}ʻx\) -/
theorem pm204_32 {α : Type u} {P : α → α → Prop} {x y : α} :
    P ∈ Ser ∧ (x ∈ fld P ∧ y ∈ fld P) → (refs P y ⊆ refs P x ↔ y ∈ refs P x ∪ ι x) := by
  rintro ⟨hS, hx, hy⟩
  have tr := mem_transR.1 hS.1.2
  have irr := mem_rl_J.1 hS.1.1
  constructor
  · intro h
    by_cases e : y = x
    · exact Or.inr e
    · rcases cxne hS.2 hy hx e with h1 | h1
      · exact Or.inl h1
      · exact (irr x (h h1)).elim
  · rintro (h | h) z hz
    · exact tr z y x ⟨hz, h⟩
    · have e : y = x := h
      rw [← e]
      exact hz

/-- ✱204·33. \(\vdash \colon\ldotp P\in \text{Ser}.x,y\in CʻP.\supset :x\neq y.\overrightarrow{P}ʻy\subset \overrightarrow{P}ʻx.\equiv .yPx\) -/
theorem pm204_33 {α : Type u} {P : α → α → Prop} {x y : α} :
    P ∈ Ser ∧ (x ∈ fld P ∧ y ∈ fld P) → (x ≠ y ∧ refs P y ⊆ refs P x ↔ P y x) := by
  intro h
  rw [pm204_32 h]
  have irr := mem_rl_J.1 h.1.1.1
  constructor
  · rintro ⟨hne, h1 | h1⟩
    · exact h1
    · exact (hne (h1 : y = x).symm).elim
  · intro h1
    exact ⟨fun e => irr x (by rw [e] at h1 ⊢; exact h1), Or.inl h1⟩

/-- ✱204·331. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.x,y\in CʻP.\supset :\overrightarrow{P}ʻx=\overrightarrow{P}ʻy.\equiv .x=y\\ &[*202·161.*71·55]\end{align}\] -/
theorem pm204_331 {α : Type u} {P : α → α → Prop} {x y : α} :
    P ∈ Ser ∧ (x ∈ fld P ∧ y ∈ fld P) → (refs P x = refs P y ↔ x = y) := by
  rintro ⟨hS, hx, hy⟩
  have irr := mem_rl_J.1 hS.1.1
  constructor
  · intro h
    exact pm202_16 ⟨⟨⟨⟨hS.2, hx, hy⟩, irr x⟩, irr y⟩, h⟩
  · rintro rfl
    rfl

/-- ✱204·34. \(\vdash :P\in \text{Ser}.\supset .\overrightarrow{P}\upharpoonright CʻP\in 1\rightarrow 1.\overrightarrow{P}\upharpoonright CʻP\in (\overrightarrow{P}^{;}P)\overline{\,\text{smor}\,} P \quad[*202·161]\) -/
theorem pm204_34 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → Rfwd P ↾ fld P ∈ arrow one one ∧ Rfwd P ↾ fld P ∈ smorbar (Rfwd P ⁏ P) P :=
  fun h => pm202_161 ⟨h.2, h.1.1⟩

/-- ✱204·35. \(\vdash :P\in \text{Ser}.\supset .\overrightarrow{P}^{;}P\,\,\text{smor}\,\,P \quad[*204·34]\) -/
theorem pm204_35 {α : Type u} {P : α → α → Prop} : P ∈ Ser → smor (Rfwd P ⁏ P) P :=
  fun h => ⟨_, (pm204_34 h).2⟩

/-- ✱204·4. \(\vdash :P\in \text{Ser}.\supset .P\unicode{x0294f}\alpha \in \text{Ser} \quad[*200·33.*201·33.*202·33]\) -/
theorem pm204_4 {α : Type u} {P : α → α → Prop} {A : Set α} : P ∈ Ser → P ⥏ A ∈ Ser :=
  fun h => ⟨⟨pm200_33 h.1.1, pm201_33 h.1.2⟩, pm202_33 h.2⟩

/-- ✱204·41. \(\vdash :P,Q\in \text{Ser}.Q\,\unicode{x2abd}\, P.\supset .Q=P\unicode{x0294f}CʻQ \quad[*202·53.*204·13]\) -/
theorem pm204_41 {α : Type u} {P Q : α → α → Prop} :
    (P ∈ Ser ∧ Q ∈ Ser) ∧ Q ⪽ P → Q = P ⥏ fld Q :=
  fun ⟨⟨hP, hQ⟩, h⟩ => pm202_53 ⟨⟨hQ.2, (pm204_13 hP).1⟩, h⟩

/-- ✱204·42. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.\supset :Q\in \text{Ser}.Q\,\unicode{x2abd}\, P.\equiv .(\exists \alpha ).Q=P\unicode{x0294f}\alpha .\equiv .Q\in \text{D}ʻP\unicode{x0294f}\\ &[*204·4·41]\end{align}\] -/
theorem pm204_42 {α : Type u} {P Q : α → α → Prop} :
    P ∈ Ser → ((Q ∈ Ser ∧ Q ⪽ P ↔ ∃ A, Q = P ⥏ A) ∧
      ((∃ A, Q = P ⥏ A) ↔ Q ∈ dom (opL fres P))) := by
  intro hP
  refine ⟨⟨fun h => ⟨fld Q, pm204_41 ⟨⟨hP, h.1⟩, h.2⟩⟩, ?_⟩, Iff.rfl⟩
  rintro ⟨A, rfl⟩
  exact ⟨pm204_4 hP, fun x y h => h.1.2⟩

/-- ✱204·421. \(\vdash :P\in \text{Ser}.\supset .\text{Ser}\cap \text{Rl}ʻP=\text{D}ʻP\unicode{x0294f} \quad[*204·42]\) -/
theorem pm204_421 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → Ser ∩ rl P = dom (opL fres P) := by
  intro hP
  ext Q
  exact ((pm204_42 hP).1.trans (pm204_42 hP).2)

/-- ✱204·43. \(\vdash :P^{2}\,\unicode{x2abd}\, P.P\,\unicode{x2abd}\, J.Q\,\unicode{x2abd}\, P.Q\in \text{connex} .\supset .Q\in \text{Ser}\) -/
theorem pm204_43 {α : Type u} {P Q : α → α → Prop} :
    ((rsq P ⪽ P ∧ P ⪽ J) ∧ Q ⪽ P) ∧ Q ∈ connex → Q ∈ Ser := by
  rintro ⟨⟨⟨ht, hJ⟩, hQP⟩, hc⟩
  have h2 : rsq P ⪽ J := fun x y h => hJ x y (ht x y h)
  have e : Q = P ⥏ fld Q := pm202_53 ⟨⟨hc, h2⟩, hQP⟩
  rw [e]
  exact ⟨⟨pm200_33 hJ, pm201_33 ht⟩, e ▸ hc⟩

/-- ✱204·44. \(\vdash :P\in \text{Rl}ʻJ\cap \text{trans}.\supset .\text{Rl}ʻP\cap \text{connex} \subset \text{Ser} \quad[*204·43]\) -/
theorem pm204_44 {α : Type u} {P : α → α → Prop} :
    P ∈ rl J ∩ transR → rl P ∩ connex ⊆ Ser :=
  fun ⟨hJ, ht⟩ _ ⟨hQ, hc⟩ => pm204_43 ⟨⟨⟨ht, hJ⟩, hQ⟩, hc⟩

/-- ✱204·45. \[\begin{align}\vdash :P\in \text{connex} .&\alpha \in \text{Cl}ʻCʻP-1.Pʻʻ\alpha \subset \alpha .\beta =CʻP-\alpha .\beta {\sim}\in 1.\supset .\\ &P=P\unicode{x0294f}\alpha \unicode{x2909}P\unicode{x0294f}\beta .\text{Nr}ʻP=\text{Nr}ʻP\unicode{x0294f}\alpha \dot{+} \text{Nr}ʻP\unicode{x0294f}\beta\end{align}\]

**Status.** proved: `Nr'P` is taken in an arbitrary type `γ`, and the arguments `Nr'P⥏α`,
`Nr'P⥏β` of `+̇` are `N₀r'P⥏α`, `N₀r'P⥏β` by the normal adjustment ✱180·03·031 (Defs/Part4,
decision 4); the equation then holds in every type. -/
theorem pm204_45 {α : Type u} {γ : Type w} {P : α → α → Prop} {A B : Set α} :
    (((P ∈ connex ∧ A ∈ cl (fld P) \ one) ∧ P ʻʻ A ⊆ A) ∧ B = fld P \ A) ∧
        B ∉ (one : Set (Set α)) →
      P = P ⥏ A ⤉ P ⥏ B ∧ nr γ P = (n₀r (P ⥏ A) ∔ n₀r (P ⥏ B) : Set (γ → γ → Prop)) := by
  rintro ⟨⟨⟨⟨hc, hAcl, hA1⟩, hPA⟩, rfl⟩, hB1⟩
  have hAf : A ⊆ fld P := hAcl
  have hfA : fld (P ⥏ A) = A := pm202_55 ⟨⟨hc, hAf⟩, hA1⟩
  have hfB : fld (P ⥏ (fld P \ A)) = fld P \ A := pm202_55 ⟨⟨hc, Set.sdiff_subset⟩, hB1⟩
  have e : P = P ⥏ A ⤉ P ⥏ (fld P \ A) := by
    funext x y
    apply propext
    rw [rsum_apply, hfA, hfB]
    constructor
    · intro h
      have hx : x ∈ fld P := ⟨y, Or.inl h⟩
      have hy : y ∈ fld P := ⟨x, Or.inr h⟩
      by_cases hyA : y ∈ A
      · exact Or.inl (Or.inl ⟨⟨hPA ⟨y, hyA, h⟩, h⟩, hyA⟩)
      · by_cases hxA : x ∈ A
        · exact Or.inr ⟨hxA, hy, hyA⟩
        · exact Or.inl (Or.inr ⟨⟨⟨hx, hxA⟩, h⟩, ⟨hy, hyA⟩⟩)
    · rintro ((h | h) | ⟨hxA, hy, hyA⟩)
      · exact h.1.2
      · exact h.1.2
      · have hne : x ≠ y := fun e => hyA (by rw [← e]; exact hxA)
        rcases cxne hc (hAf hxA) hy hne with h | h
        · exact h
        · exact (hyA (hPA ⟨x, hxA, h⟩)).elim
  refine ⟨e, nr_eq_nrAdd ?_⟩
  have hd : fld (P ⥏ A) ∩ fld (P ⥏ (fld P \ A)) = Λ := by
    rw [hfA, hfB, eqΛ]
    rintro x ⟨h1, -, h2⟩
    exact h2 h1
  have := smor_rsum_rplus hd
  rw [← e] at this
  exact this

/-- ✱204·46. \[\begin{align}\vdash :P\in \text{connex} .&\text{E}!BʻP.\text{ᗡ}ʻP{\sim}\in 1.\supset .\\ &P=BʻP\unicode{x21f7}P\unicode{x0294f}\text{ᗡ}ʻP.\text{Nr}ʻP=\dot{1} \dot{+} \text{Nr}ʻ(P\unicode{x0294f}\text{ᗡ}ʻP)\end{align}\]

**Status.** proved (reading): `1̇ +̇ μ` (✱181·021) has an apparent variable `x` whose type
nothing determines; it is the explicit type `β` (Defs/Part4, decision 3), with `[Nonempty β]`
(PM assumes every type has a member, Introduction, Ch. I; for an empty `β`, `1̇ +̇ μ = Λ`).
`Nr'P` is taken in an arbitrary type `γ`, and the argument `Nr'(P⥏ᗡ'P)` of `+̇` is `N₀r'(P⥏ᗡ'P)`
(✱181·031). The description `B'P` has the scope of the first conjunct. -/
theorem pm204_46 {α : Type u} {β : Type v} {γ : Type w} [Nonempty β] {P : α → α → Prop} :
    (P ∈ connex ∧ EDesc Beg P) ∧ codom P ∉ (one : Set (Set α)) →
      Desc Beg P (fun b => P = b ⇷ P ⥏ codom P) ∧
        nr γ P = (nrOneAdd β (n₀r (P ⥏ codom P)) : Set (γ → γ → Prop)) := by
  rintro ⟨⟨hc, b, hb⟩, h1⟩
  have hbB : Beg b P := (hb b).2 rfl
  have hcod : codom P = rels P b := by
    obtain ⟨b', hb', h'⟩ := pm202_524 ⟨hc, b, hbB⟩
    have e : b = b' := (hb' b).1 hbB
    rw [e]
    exact h'
  have hf : fld (P ⥏ codom P) = codom P :=
    pm202_55 ⟨⟨hc, fun y ⟨x, hxy⟩ => ⟨x, Or.inr hxy⟩⟩, h1⟩
  have hbn : b ∉ fld (P ⥏ codom P) := by rw [hf]; exact hbB.2
  have e : P = b ⇷ P ⥏ codom P := by
    funext x y
    apply propext
    rw [addFirst_apply, hf]
    constructor
    · intro h
      have hy : y ∈ codom P := ⟨x, h⟩
      by_cases hx : x ∈ codom P
      · exact Or.inr ⟨⟨hx, h⟩, hy⟩
      · exact Or.inl ⟨(hb x).1 ⟨⟨y, h⟩, hx⟩, hy⟩
    · rintro (⟨ex, hy⟩ | h)
      · rw [hcod] at hy
        rw [ex]
        exact hy
      · exact h.1.2
  refine ⟨(desc_iff_of hb _).2 e, ?_⟩
  have := nr_eq_nrOneAdd (γ := γ) (β := β) hbn
  rw [← e] at this
  exact this

/-- ✱204·461. \[\begin{align}\vdash :P\in \text{connex} .&\text{E}!Bʻ\breve{P} .\text{D}ʻP{\sim}\in 1.\supset .\\ &P=P\unicode{x0294f}\text{D}ʻP\unicode{x21f8} Bʻ\breve{P} .\text{Nr}ʻP=\text{Nr}ʻ(P\unicode{x0294f}\text{D}ʻP)\dot{+} \dot{1}\\ &[\text{Proof as in *204·46}]\end{align}\]

**Status.** proved (reading): as ✱204·46, for `μ +̇ 1̇` (✱181·02·03): the type `β` of the
apparent variable is explicit, with `[Nonempty β]`; `Nr'P` is in an arbitrary type `γ`. -/
theorem pm204_461 {α : Type u} {β : Type v} {γ : Type w} [Nonempty β] {P : α → α → Prop} :
    (P ∈ connex ∧ EDesc Beg P˘) ∧ dom P ∉ (one : Set (Set α)) →
      Desc Beg P˘ (fun e => P = P ⥏ dom P ⇸ e) ∧
        nr γ P = (nrAddOne β (n₀r (P ⥏ dom P)) : Set (γ → γ → Prop)) := by
  rintro ⟨⟨hc, b, hb⟩, h1⟩
  have hbB : Beg b P˘ := (hb b).2 rfl
  have hbf : b ∈ fld P := by
    obtain ⟨z, hz⟩ := hbB.1
    exact ⟨z, Or.inr hz⟩
  have hf : fld (P ⥏ dom P) = dom P :=
    pm202_55 ⟨⟨hc, fun y ⟨x, hxy⟩ => ⟨x, Or.inl hxy⟩⟩, h1⟩
  have hbn : b ∉ fld (P ⥏ dom P) := by rw [hf]; exact hbB.2
  have e : P = P ⥏ dom P ⇸ b := by
    funext x y
    apply propext
    rw [addLast_apply, hf]
    constructor
    · intro h
      have hx : x ∈ dom P := ⟨y, h⟩
      by_cases hy : y ∈ dom P
      · exact Or.inl ⟨⟨hx, h⟩, hy⟩
      · exact Or.inr ⟨hx, (hb y).1 ⟨⟨x, h⟩, hy⟩⟩
    · rintro (h | ⟨hx, ey⟩)
      · exact h.1.2
      · rw [ey]
        have hne : x ≠ b := fun e' => hbB.2 (by rw [← e']; exact hx)
        obtain ⟨w, hxw⟩ := hx
        rcases cxne hc ⟨w, Or.inl hxw⟩ hbf hne with h | h
        · exact h
        · exact (hbB.2 ⟨x, h⟩).elim
  refine ⟨(desc_iff_of hb _).2 e, ?_⟩
  have := nr_eq_nrAddOne (γ := γ) (β := β) hbn
  rw [← e] at this
  exact this

/-- ✱204·462. \[\begin{align}\vdash \colon\ldotp P,Q\in &\text{connex} .\text{E}!BʻP.\text{ᗡ}ʻP{\sim}\in 1.\text{E}!BʻQ.\text{ᗡ}ʻQ{\sim}\in 1.\supset :\\ &P\,\,\text{smor}\,\,Q.\equiv .P\unicode{x0294f}\text{ᗡ}ʻP\,\,\text{smor}\,\,Q\unicode{x0294f}\text{ᗡ}ʻQ \quad[*161·33.*204·46]\end{align}\] -/
theorem pm204_462 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} :
    ((((P ∈ connex ∧ Q ∈ connex) ∧ EDesc Beg P) ∧ codom P ∉ (one : Set (Set α))) ∧
        EDesc Beg Q) ∧ codom Q ∉ (one : Set (Set β)) →
      (smor P Q ↔ smor (P ⥏ codom P) (Q ⥏ codom Q)) := by
  rintro ⟨⟨⟨⟨⟨hP, hQ⟩, b, hb⟩, hP1⟩, c, hc⟩, hQ1⟩
  have eP : P = b ⇷ P ⥏ codom P :=
    (desc_iff_of hb _).1 (pm204_46 (β := Unit) (γ := Unit) ⟨⟨hP, b, hb⟩, hP1⟩).1
  have eQ : Q = c ⇷ Q ⥏ codom Q :=
    (desc_iff_of hc _).1 (pm204_46 (β := Unit) (γ := Unit) ⟨⟨hQ, c, hc⟩, hQ1⟩).1
  have hfP : fld (P ⥏ codom P) = codom P :=
    pm202_55 ⟨⟨hP, fun y ⟨x, hxy⟩ => ⟨x, Or.inr hxy⟩⟩, hP1⟩
  have hfQ : fld (Q ⥏ codom Q) = codom Q :=
    pm202_55 ⟨⟨hQ, fun y ⟨x, hxy⟩ => ⟨x, Or.inr hxy⟩⟩, hQ1⟩
  have hbn : b ∉ fld (P ⥏ codom P) := by rw [hfP]; exact ((hb b).2 rfl).2
  have hcn : c ∉ fld (Q ⥏ codom Q) := by rw [hfQ]; exact ((hc c).2 rfl).2
  have hne : (fld (P ⥏ codom P)).Nonempty := by
    rw [hfP]
    obtain ⟨⟨y, hby⟩, -⟩ := (hb b).2 rfl
    exact ⟨y, b, hby⟩
  constructor
  · intro h
    rw [eP, eQ] at h
    exact smor_unaddFirst h hbn hcn hne
  · intro h
    rw [eP, eQ]
    exact smor_addFirst h hbn hcn

/-- ✱204·463. \[\begin{align}\vdash :P,Q\in &\text{Rl}ʻJ.\text{E}!BʻP.\text{ᗡ}ʻP\in 1.\text{E}!.BʻQ.\text{ᗡ}ʻQ\in 1.\supset .\\ &P\,\,\text{smor}\,\,Q.P\unicode{x0294f}\text{ᗡ}ʻP\,\,\text{smor}\,\,Q\unicode{x0294f}\text{ᗡ}ʻQ\end{align}\]

**Status.** proved (reading): transcription error. The e-text prints `E!.B'Q` with a stray dot;
it is `E!B'Q`, as in the other hypotheses. -/
theorem pm204_463 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} :
    ((((P ∈ rl J ∧ Q ∈ rl J) ∧ EDesc Beg P) ∧ codom P ∈ (one : Set (Set α))) ∧
        EDesc Beg Q) ∧ codom Q ∈ (one : Set (Set β)) →
      smor P Q ∧ smor (P ⥏ codom P) (Q ⥏ codom Q) := by
  rintro ⟨⟨⟨⟨⟨hPJ, hQJ⟩, b, hb⟩, hP1⟩, c, hc⟩, hQ1⟩
  obtain ⟨y, hby, rfl⟩ := couple_of_beg hPJ hb hP1
  obtain ⟨z, hcz, rfl⟩ := couple_of_beg hQJ hc hQ1
  refine ⟨smor_couple hby hcz, smor_of_empty ?_ ?_⟩
  · rintro u v ⟨⟨⟨w, hwu⟩, huv⟩, -⟩
    rw [couple_apply] at hwu huv
    exact hby (huv.1.symm.trans hwu.2)
  · rintro u v ⟨⟨⟨w, hwu⟩, huv⟩, -⟩
    rw [couple_apply] at hwu huv
    exact hcz (huv.1.symm.trans hwu.2)

/-- ✱204·47. \[\begin{align}\vdash \colon\ldotp P,Q\in \text{connex} \cap \text{Rl}ʻJ.\text{E}!BʻP.&\text{E}!BʻQ.\supset :\\ P\,\,\text{smor}\,\,Q.\equiv .P\unicode{x0294f}\text{ᗡ}ʻrP\,\,\text{smor}\,\,Q\unicode{x0294f}\text{ᗡ}ʻQ\end{align}\]

**Status.** proved (reading): transcription error. The e-text prints `P⥏ᗡ'rP` for `P⥏ᗡ'P`. -/
theorem pm204_47 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} :
    ((P ∈ connex ∩ rl J ∧ Q ∈ connex ∩ rl J) ∧ EDesc Beg P) ∧ EDesc Beg Q →
      (smor P Q ↔ smor (P ⥏ codom P) (Q ⥏ codom Q)) := by
  rintro ⟨⟨⟨⟨hPc, hPJ⟩, ⟨hQc, hQJ⟩⟩, hbP⟩, hbQ⟩
  have begP : (refs Beg P).Nonempty := by
    obtain ⟨b, hb⟩ := hbP
    exact ⟨b, (hb b).2 rfl⟩
  have begQ : (refs Beg Q).Nonempty := by
    obtain ⟨b, hb⟩ := hbQ
    exact ⟨b, (hb b).2 rfl⟩
  by_cases h1 : codom P ∈ (one : Set (Set α)) <;> by_cases h2 : codom Q ∈ (one : Set (Set β))
  · have := pm204_463 ⟨⟨⟨⟨⟨hPJ, hQJ⟩, hbP⟩, h1⟩, hbQ⟩, h2⟩
    exact ⟨fun _ => this.2, fun _ => this.1⟩
  · have hnull : P ⥏ codom P = rNull := pm200_35 ⟨hPJ, h1⟩
    refine ⟨fun h => (h2 (codom_one_of_smor (smor_symm h) h1)).elim, fun h => ?_⟩
    obtain ⟨x, y, hxy⟩ := rEx_of_smor h (rEx_fres_codom hQc begQ h2)
    rw [hnull] at hxy
    exact (rNull_apply x y hxy).elim
  · have hnull : Q ⥏ codom Q = rNull := pm200_35 ⟨hQJ, h2⟩
    refine ⟨fun h => (h1 (codom_one_of_smor h h2)).elim, fun h => ?_⟩
    obtain ⟨x, y, hxy⟩ := rEx_of_smor (smor_symm h) (rEx_fres_codom hPc begP h1)
    rw [hnull] at hxy
    exact (rNull_apply x y hxy).elim
  · exact pm204_462 ⟨⟨⟨⟨⟨hPc, hQc⟩, hbP⟩, h1⟩, hbQ⟩, h2⟩

/-- ✱204·48. \[\begin{align}\vdash \colon\colon &P\in \text{Ser}.\supset \colon\ldotp \\ &\text{E}!BʻP.\equiv :(\exists Q).\dot{\exists} !Q.\text{Nr}ʻP=\dot{1} \dot{+} \text{Nr}ʻQ.\lor.\text{Nr}ʻP=2_{r}\end{align}\]

**Status.** proved (reading): convention AT and the type of `1̇ +̇ μ` (Prefatory Statement;
Defs/Part4, decisions 3–4). `Nr'P` and `2_r` are taken in a type `γ` adequate for `Nr'P`
(`AdeqNr γ P`; in a type too small for `Nr'P` both sides of `Nr'P = 2_r` and of
`Nr'P = 1̇ +̇ Nr'Q` can be `Λ`); the apparent variable of `1̇ +̇` has the type `β`, with
`[Nonempty β]`; the apparent variable `Q` ranges over relations of the type of `P`, and the
argument `Nr'Q` of `+̇` is `N₀r'Q` (✱181·031). -/
theorem pm204_48 {α : Type u} {β : Type v} {γ : Type w} [Nonempty β] {P : α → α → Prop}
    (hγ : AdeqNr γ P) :
    P ∈ Ser → (EDesc Beg P ↔
      (∃ Q : α → α → Prop, rEx Q ∧ nr γ P = (nrOneAdd β (n₀r Q) : Set (γ → γ → Prop))) ∨
        nr γ P = (two_r : Set (γ → γ → Prop))) := by
  intro hS
  constructor
  · rintro ⟨b, hb⟩
    by_cases h1 : codom P ∈ (one : Set (Set α))
    · right
      obtain ⟨u, v, huv, hP⟩ := ((pm204_272 hS).2).2 h1
      ext R
      constructor
      · intro hR
        rw [hP] at hR
        exact two_r_of_smor hR huv
      · rintro ⟨a, c, hac, rfl⟩
        show smor (a ↓ c) P
        rw [hP]
        exact smor_couple hac huv
    · left
      exact ⟨P ⥏ codom P, rEx_fres_codom hS.2 ⟨b, (hb b).2 rfl⟩ h1,
        (pm204_46 (β := β) (γ := γ) ⟨⟨hS.2, b, hb⟩, h1⟩).2⟩
  · intro h
    obtain ⟨R0, hR0⟩ := hγ.nr_nonempty P
    have hR0P : smor R0 P := hR0
    have hbeg : (refs Beg P).Nonempty := by
      rcases h with ⟨Q, hQ, he⟩ | he
      · rw [he] at hR0
        obtain ⟨P', x, e, hR⟩ := hR0
        have hP'Q : smor P' Q := n₀r_eq_n₀r_iff.1 e
        obtain ⟨a, c, hac⟩ := rEx_of_smor hP'Q hQ
        exact beg_of_smor (smor_trans (smor_symm hR0P) hR)
          (beg_addFirstDot x ⟨a, ⟨c, Or.inl hac⟩⟩)
      · rw [he] at hR0
        obtain ⟨a, c, hac, rfl⟩ := hR0
        refine beg_of_smor (smor_symm hR0P) ⟨a, ⟨c, (couple_apply a c a c).2 ⟨rfl, rfl⟩⟩, ?_⟩
        rintro ⟨w, hw⟩
        exact hac ((couple_apply a c w a).1 hw).2
    obtain ⟨b, hb⟩ := hbeg
    exact ⟨b, fun x => ⟨fun hx => mem_zero_union_one.1 (pm202_52 hS.2).1 x b hx hb,
      fun e => by rw [e]; exact hb⟩⟩

/-- ✱204·481. \[\begin{align}\vdash \colon\colon P\in &\text{Ser}.\supset \colon\ldotp \\ &\text{E}!Bʻ\breve{P} .\equiv :(\exists Q).\dot{\exists} !Q.\text{Nr}ʻP=\text{Nr}ʻQ\dot{+} \dot{1} .\lor.\text{Nr}ʻP=2_{r}\\ &[\text{Proof as in *204·48}]\end{align}\]

**Status.** proved (reading): as ✱204·48 (convention AT: `γ` adequate for `Nr'P`; the type
`β` of the apparent variable of `μ +̇ 1̇`, with `[Nonempty β]`). -/
theorem pm204_481 {α : Type u} {β : Type v} {γ : Type w} [Nonempty β] {P : α → α → Prop}
    (hγ : AdeqNr γ P) :
    P ∈ Ser → (EDesc Beg P˘ ↔
      (∃ Q : α → α → Prop, rEx Q ∧ nr γ P = (nrAddOne β (n₀r Q) : Set (γ → γ → Prop))) ∨
        nr γ P = (two_r : Set (γ → γ → Prop))) := by
  intro hS
  constructor
  · rintro ⟨b, hb⟩
    by_cases h1 : dom P ∈ (one : Set (Set α))
    · right
      obtain ⟨u, v, huv, hP⟩ := ((pm204_272 hS).1).1 h1
      ext R
      constructor
      · intro hR
        rw [hP] at hR
        exact two_r_of_smor hR huv
      · rintro ⟨a, c, hac, rfl⟩
        show smor (a ↓ c) P
        rw [hP]
        exact smor_couple hac huv
    · left
      exact ⟨P ⥏ dom P, rEx_fres_dom hS.2 ⟨b, (hb b).2 rfl⟩ h1,
        (pm204_461 (β := β) (γ := γ) ⟨⟨hS.2, b, hb⟩, h1⟩).2⟩
  · intro h
    obtain ⟨R0, hR0⟩ := hγ.nr_nonempty P
    have hR0P : smor R0 P := hR0
    have hend : (refs Beg P˘).Nonempty := by
      rcases h with ⟨Q, hQ, he⟩ | he
      · rw [he] at hR0
        obtain ⟨P', x, e, hR⟩ := hR0
        have hP'Q : smor P' Q := n₀r_eq_n₀r_iff.1 e
        obtain ⟨a, c, hac⟩ := rEx_of_smor hP'Q hQ
        exact beg_of_smor (smor_cnv (smor_trans (smor_symm hR0P) hR))
          (end_addLastDot x ⟨a, ⟨c, Or.inl hac⟩⟩)
      · rw [he] at hR0
        obtain ⟨a, c, hac, rfl⟩ := hR0
        refine beg_of_smor (smor_cnv (smor_symm hR0P))
          ⟨c, ⟨a, (couple_apply a c a c).2 ⟨rfl, rfl⟩⟩, ?_⟩
        rintro ⟨w, hw⟩
        exact hac ((couple_apply a c c w).1 hw).1.symm
    obtain ⟨b, hb⟩ := hend
    exact ⟨b, fun x => ⟨fun hx => mem_zero_union_one.1 (pm202_52 hS.2).2 x b hx hb,
      fun e => by rw [e]; exact hb⟩⟩

/-- ✱204·482. \[\begin{align}\vdash \colon\colon\alpha \in \text{N}_{0}\text{r}ʻʻ\text{Ser}.\supset \colon\ldotp \alpha &\subset \text{ᗡ}ʻB:\equiv :\exists !\alpha \cap \text{ᗡ}ʻB:\\ &\equiv :(\exists \beta ).\beta \in \text{NR}-{℩}ʻ0_{r}.\alpha =\dot{1} \dot{+} \beta .\lor.\alpha =2_{r}\end{align}\]

**Status.** proved (reading): the relation-number `β` of the apparent variable is taken among
the relation-numbers of relations on the type of the members of `α` (`NR α`, in that type),
and the apparent variable of `1̇ +̇ β` has the type `β'`, with `[Nonempty β']` (Defs/Part4,
decision 3); `ᗡ'B` is `codom Beg`, `0_r` is `zero_r`. -/
theorem pm204_482 {α : Type u} {β : Type v} [Nonempty β] {A : Set (α → α → Prop)} :
    A ∈ N₀r ʻʻ Ser →
      ((A ⊆ codom Beg ↔ (A ∩ codom Beg).Nonempty) ∧
        ((A ∩ codom Beg).Nonempty ↔
          (∃ B : Set (α → α → Prop), B ∈ NR α \ ι zero_r ∧ A = nrOneAdd β B) ∨
            A = two_r)) := by
  rintro ⟨P, hS, hA⟩
  have hA' : A = n₀r P := hA
  subst hA'
  have hAd : AdeqNr α P := adeqNr_iff.2 ⟨id, Function.injective_id⟩
  have key : (n₀r P ∩ codom Beg).Nonempty ↔ EDesc Beg P := by
    constructor
    · rintro ⟨X, hX, x, hx⟩
      obtain ⟨b, hb⟩ := beg_of_smor (smor_symm (mem_n₀r.1 hX)) ⟨x, hx⟩
      exact ⟨b, fun y => ⟨fun hy => mem_zero_union_one.1 (pm202_52 hS.2).1 y b hy hb,
        fun e => by rw [e]; exact hb⟩⟩
    · rintro ⟨b, hb⟩
      exact ⟨P, self_mem_n₀r P, b, (hb b).2 rfl⟩
  have e48 := pm204_48 (β := β) (γ := α) hAd hS
  rw [← n₀r_eq_nr] at e48
  refine ⟨⟨fun h => ⟨P, self_mem_n₀r P, h (self_mem_n₀r P)⟩, fun h X hX => ?_⟩,
    key.trans (e48.trans (or_congr ⟨?_, ?_⟩ Iff.rfl))⟩
  · obtain ⟨b, hb⟩ := key.1 h
    exact beg_of_smor (mem_n₀r.1 hX) ⟨b, (hb b).2 rfl⟩
  · rintro ⟨Q, hQ, he⟩
    refine ⟨n₀r Q, ⟨⟨Q, n₀r_eq_nr Q⟩, fun h0 => ?_⟩, he⟩
    have h0' : n₀r Q = zero_r := h0
    have hQ0 : Q ∈ (zero_r : Set (α → α → Prop)) := by rw [← h0']; exact self_mem_n₀r Q
    have hQn : Q = rNull := hQ0
    obtain ⟨a, c, hac⟩ := hQ
    rw [hQn] at hac
    exact rNull_apply a c hac
  · rintro ⟨B, ⟨⟨Q, hBQ⟩, hB0⟩, he⟩
    have hBQ' : B = nr α Q := hBQ
    refine ⟨Q, ?_, by rw [hBQ', ← n₀r_eq_nr] at he; exact he⟩
    by_contra hn
    apply hB0
    have hQ : Q = rNull := eqΛr.2 fun x y h => hn ⟨x, y, h⟩
    show B = zero_r
    rw [hBQ', hQ]
    exact nr_rNull

/-- ✱204·483. \[\begin{align}\vdash \colon\colon\alpha \in \text{N}_{0}\text{r}ʻʻ\text{Ser}.\supset \colon\ldotp \alpha &\subset \text{ᗡ}ʻ(B\mid \text{Cnv}):\equiv :\exists !\alpha \cap \text{ᗡ}ʻ(B\mid \text{Cnv}):\\ &\equiv :(\exists \beta ).\beta \in \text{NR}-{℩}ʻ0_{r}.\alpha =\beta \dot{+} \dot{1} .\lor.\alpha =2_{r}\\ [\text{Proof as in *204·482}]\end{align}\]

**Status.** proved (reading): as ✱204·482; `ᗡ'(B | Cnv)` is `codom (Beg ⨾ Cnv)`, the relations
having a last term. The e-text's stray `\` before the reference has no significance. -/
theorem pm204_483 {α : Type u} {β : Type v} [Nonempty β] {A : Set (α → α → Prop)} :
    A ∈ N₀r ʻʻ Ser →
      ((A ⊆ codom (Beg ⨾ Cnv) ↔ (A ∩ codom (Beg ⨾ Cnv)).Nonempty) ∧
        ((A ∩ codom (Beg ⨾ Cnv)).Nonempty ↔
          (∃ B : Set (α → α → Prop), B ∈ NR α \ ι zero_r ∧ A = nrAddOne β B) ∨
            A = two_r)) := by
  rintro ⟨P, hS, hA⟩
  have hA' : A = n₀r P := hA
  subst hA'
  have hAd : AdeqNr α P := adeqNr_iff.2 ⟨id, Function.injective_id⟩
  have hcd : ∀ X : α → α → Prop, X ∈ codom (Beg ⨾ Cnv) ↔ (refs Beg X˘).Nonempty := by
    intro X
    constructor
    · rintro ⟨x, Y, hx, hY⟩
      rw [Cnv_iff.1 hY] at hx
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, X˘, hx, Cnv_iff.2 rfl⟩
  have key : (n₀r P ∩ codom (Beg ⨾ Cnv)).Nonempty ↔ EDesc Beg P˘ := by
    constructor
    · rintro ⟨X, hX, hXc⟩
      obtain ⟨b, hb⟩ := beg_of_smor (smor_cnv (smor_symm (mem_n₀r.1 hX))) ((hcd X).1 hXc)
      exact ⟨b, fun y => ⟨fun hy => mem_zero_union_one.1 (pm202_52 hS.2).2 y b hy hb,
        fun e => by rw [e]; exact hb⟩⟩
    · rintro ⟨b, hb⟩
      exact ⟨P, self_mem_n₀r P, (hcd P).2 ⟨b, (hb b).2 rfl⟩⟩
  have e48 := pm204_481 (β := β) (γ := α) hAd hS
  rw [← n₀r_eq_nr] at e48
  refine ⟨⟨fun h => ⟨P, self_mem_n₀r P, h (self_mem_n₀r P)⟩, fun h X hX => ?_⟩,
    key.trans (e48.trans (or_congr ⟨?_, ?_⟩ Iff.rfl))⟩
  · obtain ⟨b, hb⟩ := key.1 h
    exact (hcd X).2 (beg_of_smor (smor_cnv (mem_n₀r.1 hX)) ⟨b, (hb b).2 rfl⟩)
  · rintro ⟨Q, hQ, he⟩
    refine ⟨n₀r Q, ⟨⟨Q, n₀r_eq_nr Q⟩, fun h0 => ?_⟩, he⟩
    have h0' : n₀r Q = zero_r := h0
    have hQ0 : Q ∈ (zero_r : Set (α → α → Prop)) := by rw [← h0']; exact self_mem_n₀r Q
    have hQn : Q = rNull := hQ0
    obtain ⟨a, c, hac⟩ := hQ
    rw [hQn] at hac
    exact rNull_apply a c hac
  · rintro ⟨B, ⟨⟨Q, hBQ⟩, hB0⟩, he⟩
    have hBQ' : B = nr α Q := hBQ
    refine ⟨Q, ?_, by rw [hBQ', ← n₀r_eq_nr] at he; exact he⟩
    by_contra hn
    apply hB0
    have hQ : Q = rNull := eqΛr.2 fun x y h => hn ⟨x, y, h⟩
    show B = zero_r
    rw [hBQ', hQ]
    exact nr_rNull

/-- ✱204·5. \[\begin{align}&\vdash :P,Q\in \text{Ser}.CʻP\cap CʻQ=\Lambda .\equiv .P\unicode{x2909}Q\in \text{Ser}\\ &[*200·4.*201·401.*202·401]\end{align}\] -/
theorem pm204_5 {α : Type u} {P Q : α → α → Prop} :
    (P ∈ Ser ∧ Q ∈ Ser) ∧ fld P ∩ fld Q = Λ ↔ P ⤉ Q ∈ Ser := by
  constructor
  · rintro ⟨⟨hP, hQ⟩, hd⟩
    exact ⟨⟨pm200_4.2 ⟨⟨hP.1.1, hQ.1.1⟩, hd⟩, pm201_4 ⟨⟨hP.1.2, hQ.1.2⟩, hd⟩⟩,
      pm202_4 ⟨hP.2, hQ.2⟩⟩
  · rintro ⟨⟨hJ, ht⟩, hc⟩
    obtain ⟨⟨hPJ, hQJ⟩, hd⟩ := pm200_4.1 hJ
    obtain ⟨hPt, hQt⟩ := (pm201_401 hd).1 ht
    obtain ⟨hPc, hQc⟩ := (pm202_401 hd).1 hc
    exact ⟨⟨⟨⟨hPJ, hPt⟩, hPc⟩, ⟨⟨hQJ, hQt⟩, hQc⟩⟩, hd⟩

/-- ✱204·51. \[\begin{align}&\vdash :P\in \text{Ser}.x{\sim}\in CʻP.\equiv .P\unicode{x21f8} x\in \text{Ser}.\equiv .\chi\unicode{x21f7}P\in \text{Ser}\\ &[*200·41.*201·41.*202·412]\end{align}\]

**Status.** proved (reading): transcription error. The e-text prints `χ⇷P` for `x⇷P` in
the last member of the chain (the demonstration cites ✱200·41, ✱201·41, ✱202·412, which are
about `x⇷P`). -/
theorem pm204_51 {α : Type u} {P : α → α → Prop} {x : α} :
    (P ∈ Ser ∧ x ∉ fld P ↔ P ⇸ x ∈ Ser) ∧ (P ⇸ x ∈ Ser ↔ x ⇷ P ∈ Ser) := by
  have hx1 : P ⇸ x ∈ Ser → x ∉ fld P := fun h => (pm200_41.1.trans pm200_41.2 |>.1 h.1.1).2
  have hx2 : x ⇷ P ∈ Ser → x ∉ fld P := fun h => (pm200_41.2.1 h.1.1).2
  have e1 : P ∈ Ser ∧ x ∉ fld P ↔ P ⇸ x ∈ Ser := by
    constructor
    · rintro ⟨⟨⟨hJ, ht⟩, hc⟩, hx⟩
      exact ⟨⟨pm200_41.1.2 (pm200_41.2.2 ⟨hJ, hx⟩), ((pm201_41 hx).1).1 ht⟩,
        ((pm202_412 hx).1).1 hc⟩
    · intro h
      have hx := hx1 h
      exact ⟨⟨⟨(pm200_41.2.1 (pm200_41.1.1 h.1.1)).1, ((pm201_41 hx).1).2 h.1.2⟩,
        ((pm202_412 hx).1).2 h.2⟩, hx⟩
  have e2 : P ∈ Ser ∧ x ∉ fld P ↔ x ⇷ P ∈ Ser := by
    constructor
    · rintro ⟨⟨⟨hJ, ht⟩, hc⟩, hx⟩
      exact ⟨⟨pm200_41.2.2 ⟨hJ, hx⟩, ((pm201_41 hx).2).1 (((pm201_41 hx).1).1 ht)⟩,
        ((pm202_412 hx).2).1 (((pm202_412 hx).1).1 hc)⟩
    · intro h
      have hx := hx2 h
      exact ⟨⟨⟨(pm200_41.2.1 h.1.1).1,
        ((pm201_41 hx).1).2 (((pm201_41 hx).2).2 h.1.2)⟩,
        ((pm202_412 hx).1).2 (((pm202_412 hx).2).2 h.2)⟩, hx⟩
  exact ⟨e1, e1.symm.trans e2⟩

/-- ✱204·52. \(\vdash :P\in \text{Rel}^{2}\text{excl}\cap \text{Ser}.CʻP\subset \text{Ser}.\supset .\Sigma ʻP \in \text{Ser}\) -/
theorem pm204_52 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ∩ Ser ∧ fld P ⊆ Ser → relSigma P ∈ Ser := by
  rintro ⟨⟨hex, hS⟩, hC⟩
  have hF : F ⁏ P ⪽ J := (pm202_62 ⟨hS.2, hS.1.1⟩).1 hex
  refine ⟨⟨pm200_42.2 ⟨fun Q hQ => (hC hQ).1.1, hF⟩, pm201_42 ⟨⟨hS.1.2, hex⟩,
    fun Q hQ => (hC hQ).1.2⟩⟩, pm202_42 ⟨hS.2, fun Q hQ => (hC hQ).2⟩⟩

/-- ✱204·53. \(\vdash \colon\ldotp P\in \text{Rel}^{2}\text{excl}.\dot{\Lambda} {\sim}\in CʻP.\supset :\Sigma ʻP\in \text{Ser}.\equiv .P\in \text{Ser}.CʻP\subset \text{Ser}\) -/
theorem pm204_53 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Rel2excl ∧ rNull ∉ fld P → (relSigma P ∈ Ser ↔ P ∈ Ser ∧ fld P ⊆ Ser) := by
  rintro ⟨hex, hN⟩
  constructor
  · intro hS
    obtain ⟨hPJ, -⟩ := (pm200_423 ⟨hex, hN⟩).1 hS.1.1
    have hC : fld P ⊆ Ser := by
      intro Q hQ
      rw [pm200_421 ⟨⟨hex, hPJ⟩, hQ⟩]
      exact pm204_4 hS
    have nonnull : ∀ Q, Q ∈ fld P → ∃ x, x ∈ fld Q := by
      intro Q hQ
      by_contra hn
      apply hN
      have : Q = rNull := eqΛr.2 fun x y h => hn ⟨x, ⟨y, Or.inl h⟩⟩
      rw [← this]
      exact hQ
    have trS := mem_transR.1 hS.1.2
    have irrS := mem_rl_J.1 hS.1.1
    have disj : ∀ Q R, Q ∈ fld P → R ∈ fld P → ∀ z, z ∈ fld Q → z ∈ fld R → Q = R := by
      intro Q R hQ hR z hzQ hzR
      by_contra hne
      exact eqΛ.1 (hex Q R ⟨⟨hQ, hR⟩, hne⟩) z ⟨hzQ, hzR⟩
    have sig : ∀ Q R x y, P Q R → x ∈ fld Q → y ∈ fld R → relSigma P x y :=
      fun Q R x y h hx hy => (relSigma_apply P x y).2 (Or.inr ⟨Q, R, ⟨hx, hy⟩, h⟩)
    refine ⟨⟨⟨hPJ, ?_⟩, ?_⟩, hC⟩
    · rw [mem_transR]
      rintro Q R S ⟨hQR, hRS⟩
      have hQ : Q ∈ fld P := ⟨R, Or.inl hQR⟩
      have hR : R ∈ fld P := ⟨Q, Or.inr hQR⟩
      have hS' : S ∈ fld P := ⟨R, Or.inr hRS⟩
      obtain ⟨x, hx⟩ := nonnull Q hQ
      obtain ⟨y, hy⟩ := nonnull R hR
      obtain ⟨z, hz⟩ := nonnull S hS'
      have hxz := trS x y z ⟨sig Q R x y hQR hx hy, sig R S y z hRS hy hz⟩
      rcases (relSigma_apply P x z).1 hxz with ⟨M, hM, hxzM⟩ | ⟨M, N, ⟨hxM, hzN⟩, hMN⟩
      · have e1 := disj M Q hM hQ x ⟨z, Or.inl hxzM⟩ hx
        have e2 := disj M S hM hS' z ⟨x, Or.inr hxzM⟩ hz
        have hRQ : P R Q := by rw [← e1, e2]; exact hRS
        exact (irrS x (trS x y x ⟨sig Q R x y hQR hx hy, sig R Q y x hRQ hy hx⟩)).elim
      · have e1 := disj M Q ⟨N, Or.inl hMN⟩ hQ x hxM hx
        have e2 := disj N S ⟨M, Or.inr hMN⟩ hS' z hzN hz
        rw [← e1, ← e2]
        exact hMN
    · rw [pm202_104]
      rintro Q R ⟨⟨hQ, hR⟩, hne⟩
      obtain ⟨x, hx⟩ := nonnull Q hQ
      obtain ⟨y, hy⟩ := nonnull R hR
      have hxy : x ≠ y := fun e => hne (disj Q R hQ hR x hx (by rw [e]; exact hy))
      have hfx : x ∈ fld (relSigma P) := by
        obtain ⟨w, hw | hw⟩ := hx
        · exact ⟨w, Or.inl ((relSigma_apply P x w).2 (Or.inl ⟨Q, hQ, hw⟩))⟩
        · exact ⟨w, Or.inr ((relSigma_apply P w x).2 (Or.inl ⟨Q, hQ, hw⟩))⟩
      have hfy : y ∈ fld (relSigma P) := by
        obtain ⟨w, hw | hw⟩ := hy
        · exact ⟨w, Or.inl ((relSigma_apply P y w).2 (Or.inl ⟨R, hR, hw⟩))⟩
        · exact ⟨w, Or.inr ((relSigma_apply P w y).2 (Or.inl ⟨R, hR, hw⟩))⟩
      rcases cxne hS.2 hfx hfy hxy with h | h
      · rcases (relSigma_apply P x y).1 h with ⟨M, hM, hM'⟩ | ⟨M, N, ⟨hxM, hyN⟩, hMN⟩
        · exact (hne ((disj M Q hM hQ x ⟨y, Or.inl hM'⟩ hx).symm.trans
            (disj M R hM hR y ⟨x, Or.inr hM'⟩ hy))).elim
        · have e1 := disj M Q ⟨N, Or.inl hMN⟩ hQ x hxM hx
          have e2 := disj N R ⟨M, Or.inr hMN⟩ hR y hyN hy
          rw [← e1, ← e2]
          exact Or.inl hMN
      · rcases (relSigma_apply P y x).1 h with ⟨M, hM, hM'⟩ | ⟨M, N, ⟨hyM, hxN⟩, hMN⟩
        · exact (hne ((disj M Q hM hQ x ⟨y, Or.inr hM'⟩ hx).symm.trans
            (disj M R hM hR y ⟨x, Or.inl hM'⟩ hy))).elim
        · have e1 := disj M R ⟨N, Or.inl hMN⟩ hR y hyM hy
          have e2 := disj N Q ⟨M, Or.inr hMN⟩ hQ x hxN hx
          rw [← e1, ← e2]
          exact Or.inr hMN
  · rintro ⟨hS, hC⟩
    exact pm204_52 ⟨⟨hex, hS⟩, hC⟩

/-- ✱204·54. \(\vdash :P\in \text{Rel}^{3}\text{arithm}\cap \text{Ser}.CʻP\subset \text{Ser}.Cʻ\Sigma ʻP\subset \text{Ser}.\supset .\Sigma ʻ\Sigma ʻP\in \text{Ser}\) -/
theorem pm204_54 {α : Type u}
    {P : ((α → α → Prop) → (α → α → Prop) → Prop) → ((α → α → Prop) → (α → α → Prop) → Prop) →
      Prop} :
    (P ∈ Rel3arithm ∩ Ser ∧ fld P ⊆ Ser) ∧ fld (relSigma P) ⊆ Ser →
      relSigma (relSigma P) ∈ Ser := by
  rintro ⟨⟨⟨⟨hex, hex2⟩, hS⟩, hC⟩, hC2⟩
  have h1 : relSigma P ∈ Ser := pm204_52 ⟨⟨hex, hS⟩, hC⟩
  exact pm204_52 ⟨⟨hex2, h1⟩, hC2⟩

/-- ✱204·55. \(\vdash :P,Q\in \text{Ser}.\supset .Q\times P\in \text{Ser}\) -/
theorem pm204_55 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} :
    P ∈ Ser ∧ Q ∈ Ser → Q ×ᵣ P ∈ Ser := by
  rintro ⟨hP, hQ⟩
  have irrP := mem_rl_J.1 hP.1.1
  have irrQ := mem_rl_J.1 hQ.1.1
  have trP := mem_transR.1 hP.1.2
  have trQ := mem_transR.1 hQ.1.2
  refine ⟨⟨mem_rl_J.2 fun u h => ?_, mem_transR.2 fun u v w h => ?_⟩, mem_connex.2 fun u v h => ?_⟩
  · obtain ⟨x, z, rfl, -, -⟩ := rtimes_fld ⟨u, Or.inl h⟩
    rcases rtimes_couple.1 h with ⟨-, -, h1⟩ | ⟨h1, -⟩
    · exact irrP x h1
    · exact irrQ z h1
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨x, z, rfl, -, -⟩ := rtimes_fld ⟨v, Or.inl h1⟩
    obtain ⟨y, r, rfl, -, -⟩ := rtimes_fld ⟨x ↓ z, Or.inr h1⟩
    obtain ⟨t, s, rfl, -, -⟩ := rtimes_fld ⟨y ↓ r, Or.inr h2⟩
    rw [rtimes_couple] at h1 h2 ⊢
    rcases h1 with ⟨rfl, hz, hxy⟩ | ⟨hzr, hx, hy⟩ <;>
      rcases h2 with ⟨rfl, -, hyt⟩ | ⟨hrs, -, ht⟩
    · exact Or.inl ⟨rfl, hz, trP x y t ⟨hxy, hyt⟩⟩
    · exact Or.inr ⟨hrs, ⟨y, Or.inl hxy⟩, ht⟩
    · exact Or.inr ⟨hzr, hx, ⟨y, Or.inr hyt⟩⟩
    · exact Or.inr ⟨trQ z r s ⟨hzr, hrs⟩, hx, ht⟩
  · obtain ⟨hu, hv⟩ := h
    obtain ⟨x, z, rfl, hx, hz⟩ := rtimes_fld hu
    obtain ⟨y, w, rfl, hy, hw⟩ := rtimes_fld hv
    rw [rtimes_couple, rtimes_couple]
    by_cases e : z = w
    · rw [← e]
      rcases mem_connex.1 hP.2 x y ⟨hx, hy⟩ with (h1 | h1) | h1
      · exact Or.inl (Or.inl (Or.inl ⟨rfl, hz, h1⟩))
      · exact Or.inl (Or.inr (by rw [h1]))
      · exact Or.inr (Or.inl ⟨rfl, hz, h1⟩)
    · rcases cxne hQ.2 hz hw e with h1 | h1
      · exact Or.inl (Or.inl (Or.inr ⟨h1, hx, hy⟩))
      · exact Or.inr (Or.inr ⟨h1, hy, hx⟩)

/-- ✱204·551. \(\vdash \colon\ldotp \dot{\exists} !P.\dot{\exists} !Q.\supset :P\times Q\in \text{Ser}.\equiv .P,Q\in \text{Ser}\) -/
theorem pm204_551 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} :
    rEx P ∧ rEx Q → (P ×ᵣ Q ∈ Ser ↔ P ∈ Ser ∧ Q ∈ Ser) := by
  rintro ⟨⟨a0, b0, h0⟩, ⟨c0, d0, k0⟩⟩
  have hz0 : a0 ∈ fld P := ⟨b0, Or.inl h0⟩
  have hx0 : c0 ∈ fld Q := ⟨d0, Or.inl k0⟩
  refine ⟨fun hT => ?_, fun h => pm204_55 ⟨h.2, h.1⟩⟩
  have irrT := mem_rl_J.1 hT.1.1
  have trT := mem_transR.1 hT.1.2
  have irrP : ∀ z, ¬P z z := fun z h =>
    irrT (c0 ↓ z) (rtimes_couple.2 (Or.inr ⟨h, hx0, hx0⟩))
  have irrQ : ∀ x, ¬Q x x := fun x h =>
    irrT (x ↓ a0) (rtimes_couple.2 (Or.inl ⟨rfl, hz0, h⟩))
  refine ⟨⟨⟨mem_rl_J.2 irrP, mem_transR.2 fun z w r ⟨h1, h2⟩ => ?_⟩, mem_connex.2 ?_⟩,
    ⟨⟨mem_rl_J.2 irrQ, mem_transR.2 fun x y t ⟨h1, h2⟩ => ?_⟩, mem_connex.2 ?_⟩⟩
  · have k1 : (P ×ᵣ Q) (c0 ↓ z) (c0 ↓ w) := rtimes_couple.2 (Or.inr ⟨h1, hx0, hx0⟩)
    have k2 : (P ×ᵣ Q) (c0 ↓ w) (c0 ↓ r) := rtimes_couple.2 (Or.inr ⟨h2, hx0, hx0⟩)
    rcases rtimes_couple.1 (trT _ _ _ ⟨k1, k2⟩) with ⟨-, -, h⟩ | ⟨h, -⟩
    · exact (irrQ c0 h).elim
    · exact h
  · rintro z w ⟨hz, hw⟩
    by_cases e : z = w
    · exact Or.inl (Or.inr e)
    · have hu : c0 ↓ z ∈ fld (P ×ᵣ Q) := rtimes_mem_fld hx0 hz
      have hv : c0 ↓ w ∈ fld (P ×ᵣ Q) := rtimes_mem_fld hx0 hw
      have hne : c0 ↓ z ≠ c0 ↓ w := fun h => e (couple_eq_couple_iff.1 h).2
      rcases cxne hT.2 hu hv hne with h | h
      · rcases rtimes_couple.1 h with ⟨h', -, -⟩ | ⟨h', -⟩
        · exact (e h').elim
        · exact Or.inl (Or.inl h')
      · rcases rtimes_couple.1 h with ⟨h', -, -⟩ | ⟨h', -⟩
        · exact (e h'.symm).elim
        · exact Or.inr h'
  · have k1 : (P ×ᵣ Q) (x ↓ a0) (y ↓ a0) := rtimes_couple.2 (Or.inl ⟨rfl, hz0, h1⟩)
    have k2 : (P ×ᵣ Q) (y ↓ a0) (t ↓ a0) := rtimes_couple.2 (Or.inl ⟨rfl, hz0, h2⟩)
    rcases rtimes_couple.1 (trT _ _ _ ⟨k1, k2⟩) with ⟨-, -, h⟩ | ⟨h, -⟩
    · exact h
    · exact (irrP a0 h).elim
  · rintro x y ⟨hx, hy⟩
    by_cases e : x = y
    · exact Or.inl (Or.inr e)
    · have hu : x ↓ a0 ∈ fld (P ×ᵣ Q) := rtimes_mem_fld hx hz0
      have hv : y ↓ a0 ∈ fld (P ×ᵣ Q) := rtimes_mem_fld hy hz0
      have hne : x ↓ a0 ≠ y ↓ a0 := fun h => e (couple_eq_couple_iff.1 h).1
      rcases cxne hT.2 hu hv hne with h | h
      · rcases rtimes_couple.1 h with ⟨-, -, h'⟩ | ⟨h', -⟩
        · exact Or.inl (Or.inl h')
        · exact (irrP a0 h').elim
      · rcases rtimes_couple.1 h with ⟨-, -, h'⟩ | ⟨h', -⟩
        · exact Or.inr h'
        · exact (irrP a0 h').elim

/-- ✱204·56. \(\vdash :CʻP\subset \text{Rl}ʻJ.\supset .\Pi ʻP\,\unicode{x2abd}\, J\) -/
theorem pm204_56 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    fld P ⊆ rl J → relPi P ⪽ J := by
  rintro hC M N ⟨⟨hM, -⟩, Q, hQ, -⟩ e
  have e' : M = N := e
  subst e'
  obtain ⟨b, hb, c, hc, h3⟩ := hQ
  have hbc : b = c := (hc b).1 ((hb b).2 rfl)
  rw [← hbc] at h3
  have hQf : Q ∈ fld P := sel_codom hM ((hb b).2 rfl)
  exact hC hQf b b h3 rfl

/-- ✱204·561. \(\vdash :P\in \text{Ser}.CʻP\subset \text{Ser}.\supset .\Pi ʻP\in \text{Rl}ʻJ\cap \text{trans}\) -/
theorem pm204_561 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    P ∈ Ser ∧ fld P ⊆ Ser → relPi P ∈ rl J ∩ transR := by
  rintro ⟨hS, hC⟩
  have hJ : relPi P ⪽ J := pm204_56 fun Q hQ => (hC hQ).1.1
  have irrP := mem_rl_J.1 hS.1.1
  have trP := mem_transR.1 hS.1.2
  refine ⟨hJ, mem_transR.2 ?_⟩
  rintro L M N ⟨⟨⟨hL, hM⟩, Q, hLMQ, hQ⟩, ⟨⟨-, hN⟩, R, hMNR, hR⟩⟩
  have hQf : Q ∈ fld P := by
    obtain ⟨b, hb, -⟩ := hLMQ
    exact sel_codom hL ((hb b).2 rfl)
  have hRf : R ∈ fld P := by
    obtain ⟨b, hb, -⟩ := hMNR
    exact sel_codom hM ((hb b).2 rfl)
  have eqtr : ∀ a b c : α, a = b → b = c → a = c := fun a b c h1 h2 => h1.trans h2
  refine ⟨⟨hL, hN⟩, ?_⟩
  by_cases e : Q = R
  · subst e
    refine ⟨Q, desc_comp hLMQ hMNR fun a b c h1 h2 =>
      mem_transR.1 (hC hQf).1.2 a b c ⟨h1, h2⟩, fun S hS' => desc_comp (hQ S hS') (hR S hS') eqtr⟩
  · rcases cxne hS.2 hQf hRf e with h | h
    · refine ⟨Q, desc_comp hLMQ (hR Q ⟨h, e⟩) fun a b c h1 h2 => by rw [← h2]; exact h1, ?_⟩
      intro S ⟨hSQ, hne⟩
      have hSR : P S R := trP S Q R ⟨hSQ, h⟩
      exact desc_comp (hQ S ⟨hSQ, hne⟩) (hR S ⟨hSR, fun e' => irrP R (by rw [e'] at hSR; exact hSR)⟩) eqtr
    · refine ⟨R, desc_comp (hQ R ⟨h, Ne.symm e⟩) hMNR fun a b c h1 h2 => by rw [h1]; exact h2, ?_⟩
      intro S ⟨hSR, hne⟩
      have hSQ : P S Q := trP S R Q ⟨hSR, h⟩
      exact desc_comp (hQ S ⟨hSQ, fun e' => irrP Q (by rw [e'] at hSQ; exact hSQ)⟩) (hR S ⟨hSR, hne⟩) eqtr

/-- ✱204·562. \(\vdash \colon\ldotp CʻP\subset ʻ\text{Ser}:\alpha \subset CʻP.\exists !\alpha .\supset _{\alpha }.\exists !\alpha -\breve{P} ʻʻ\alpha :\supset .\Pi ʻP\in \text{connex}\)

**Status.** proved (reading): transcription error. The e-text prints the first hypothesis
as `C'P ⊂ 'Ser` with a stray `'`; it is `C'P ⊂ Ser` (as in ✱204·57). -/
theorem pm204_562 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    fld P ⊆ Ser ∧ (∀ A : Set (α → α → Prop), A ⊆ fld P ∧ A.Nonempty → (A \ P˘ ʻʻ A).Nonempty) →
      relPi P ∈ connex := by
  rintro ⟨hC, hW⟩
  have hsel : ∀ M, M ∈ fld (relPi P) → M ∈ sel F (fld P) := by
    rintro M ⟨N, ⟨⟨hM, -⟩, -⟩ | ⟨⟨-, hM⟩, -⟩⟩ <;> exact hM
  rw [mem_connex]
  rintro M N ⟨hM', hN'⟩
  have hM := hsel M hM'
  have hN := hsel N hN'
  by_cases eMN : M = N
  · exact Or.inl (Or.inr eMN)
  -- the members of `C'P` at which `M` and `N` differ
  set A : Set (α → α → Prop) :=
    {Q | Q ∈ fld P ∧ ¬Desc M Q (fun x => Desc N Q (fun y => x = y))} with hA
  have hAne : A.Nonempty := by
    by_contra hn
    apply eMN
    funext x Q
    apply propext
    by_cases hQ : Q ∈ fld P
    · have hQA : Desc M Q (fun x => Desc N Q (fun y => x = y)) := by
        by_contra h'
        exact hn ⟨Q, hQ, h'⟩
      obtain ⟨b, hb, c, hc, rfl⟩ := hQA
      exact (hb x).trans (hc x).symm
    · exact ⟨fun h => (hQ (sel_codom hM h)).elim, fun h => (hQ (sel_codom hN h)).elim⟩
  obtain ⟨Q, ⟨hQf, hQd⟩, hQmin⟩ := hW A ⟨fun Q hQ => hQ.1, hAne⟩
  have below : ∀ R, P R Q ∧ R ≠ Q → Desc M R (fun x => Desc N R (fun y => x = y)) := by
    rintro R ⟨hRQ, -⟩
    by_contra h'
    exact hQmin ⟨R, ⟨⟨Q, Or.inl hRQ⟩, h'⟩, hRQ⟩
  obtain ⟨m, hm, hmQ⟩ := sel_unique hM hQf
  obtain ⟨n, hn, hnQ⟩ := sel_unique hN hQf
  have hmn : m ≠ n := fun e => hQd ((desc_iff_of hm _).2 ((desc_iff_of hn _).2 e))
  rcases cxne (hC hQf).2 hmQ hnQ hmn with h | h
  · exact Or.inl (Or.inl ⟨⟨hM, hN⟩, Q, (desc_iff_of hm _).2 ((desc_iff_of hn _).2 h), below⟩)
  · refine Or.inr ⟨⟨hN, hM⟩, Q, (desc_iff_of hn _).2 ((desc_iff_of hm _).2 h), fun R hR => ?_⟩
    obtain ⟨b, hb, c, hc, rfl⟩ := below R hR
    exact ⟨b, hc, b, hb, rfl⟩

/-- ✱204·57. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.CʻP\subset \text{Ser}:\alpha \subset CʻP.\exists !\alpha .\supset _{\alpha }.\exists !\alpha -\breve{P} ʻʻ\alpha :\supset .\Pi ʻP\in \text{Ser}\\ &[*204·561·562]\end{align}\] -/
theorem pm204_57 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} :
    (P ∈ Ser ∧ fld P ⊆ Ser) ∧
      (∀ A : Set (α → α → Prop), A ⊆ fld P ∧ A.Nonempty → (A \ P˘ ʻʻ A).Nonempty) →
      relPi P ∈ Ser := by
  rintro ⟨h1, hW⟩
  have := pm204_561 h1
  exact ⟨this, pm204_562 ⟨h1.2, hW⟩⟩

/-- ✱204·58. \[\begin{align}&\vdash \colon\ldotp P\in \text{Ser}.CʻP\subset \text{Ser}.Cʻ\Sigma ʻP\subset \text{Ser}.P\in \text{Rel}^{2}\text{excl}:\\ &\alpha \subset Cʻ\Sigma ʻP .\exists !\alpha .\supset _{\alpha }.\exists !\alpha -(\text{Cnv}ʻ\Sigma ʻP)ʻʻ\alpha :\supset .\Pi ʻ\Sigma ʻP,\Pi ʻ\Pi ^{;}P\in \text{Ser}\end{align}\]

**Status.** proved: PM derives `Π'Π;P ∈ Ser` from `Π'Σ'P smor Π'Π;P` (✱174·25); the proof
here applies ✱204·57 to `Π;P` directly (`Π;P` is like `P` unless some `Π'Q`, `Q ∈ C'P`, is
`Λ̇`, in which case there are no selections and `Π'Π;P = Λ̇ ∈ Ser`). `Cnv'Σ'P` is `(Σ'P)˘`,
`Π;P` is `RelPi ⁏ P`, and the hypothesis `α ⊂ C'Σ'P . ∃!α . ⊃_α . ∃!α − (Cnv'Σ'P)''α` is
the formal implication over classes `α`. -/
theorem pm204_58 {α : Type u}
    {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
      ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} :
    (((P ∈ Ser ∧ fld P ⊆ Ser) ∧ fld (relSigma P) ⊆ Ser) ∧ P ∈ Rel2excl) ∧
      (∀ A : Set (α → α → Prop), A ⊆ fld (relSigma P) ∧ A.Nonempty →
        (A \ (relSigma P)˘ ʻʻ A).Nonempty) →
      relPi (relSigma P) ∈ Ser ∧ relPi (RelPi ⁏ P) ∈ Ser := by
  rintro ⟨⟨⟨⟨hS, hC⟩, hCS⟩, hex⟩, hW⟩
  have hSig : relSigma P ∈ Ser := pm204_52 ⟨⟨hex, hS⟩, hC⟩
  refine ⟨pm204_57 ⟨⟨hSig, hCS⟩, hW⟩, ?_⟩
  have fldQ : ∀ Q, Q ∈ fld P → fld Q ⊆ fld (relSigma P) := by
    rintro Q hQ R ⟨S, h | h⟩
    · exact ⟨S, Or.inl ((relSigma_apply P R S).2 (Or.inl ⟨Q, hQ, h⟩))⟩
    · exact ⟨S, Or.inr ((relSigma_apply P S R).2 (Or.inl ⟨Q, hQ, h⟩))⟩
  have WFQ : ∀ Q, Q ∈ fld P → ∀ A : Set (α → α → Prop), A ⊆ fld Q ∧ A.Nonempty →
      (A \ Q˘ ʻʻ A).Nonempty := by
    rintro Q hQ A ⟨hA, hne⟩
    obtain ⟨R, hRA, hRn⟩ := hW A ⟨fun R hR => fldQ Q hQ (hA hR), hne⟩
    exact ⟨R, hRA, fun ⟨S, hSA, hSR⟩ =>
      hRn ⟨S, hSA, (relSigma_apply P S R).2 (Or.inl ⟨Q, hQ, hSR⟩)⟩⟩
  have hPiQ : ∀ Q, Q ∈ fld P → relPi Q ∈ Ser := fun Q hQ =>
    pm204_57 ⟨⟨hC hQ, fun R hR => hCS (fldQ Q hQ hR)⟩, WFQ Q hQ⟩
  have hK : (RelPi ⁏ P) = graph relPi ⁏ P := rfl
  by_cases hd : ∃ Q, Q ∈ fld P ∧ relPi Q = rNull
  · obtain ⟨Q, hQ, h0⟩ := hd
    have hnf : rNull ∈ fld (RelPi ⁏ P) := by
      rw [hK]
      exact mem_fld_graph_semi.2 ⟨Q, hQ, h0.symm⟩
    have e : relPi (RelPi ⁏ P) = rNull := by
      rw [eqΛr]
      rintro M N ⟨⟨hM, -⟩, -⟩
      obtain ⟨b, -, w, hw | hw⟩ := sel_unique hM hnf
      · exact rNull_apply _ _ hw
      · exact rNull_apply _ _ hw
    rw [e]
    exact pm204_24
  · push_neg at hd
    have hfne : ∀ Q, Q ∈ fld P → (fld Q).Nonempty := by
      intro Q hQ
      by_contra hn
      apply hd Q hQ
      rw [eqΛr]
      rintro M N ⟨⟨hM, -⟩, R, ⟨b, hb, -⟩, -⟩
      exact hn ⟨R, sel_codom hM ((hb b).2 rfl)⟩
    have hinj : ∀ Q Q', Q ∈ fld P → Q' ∈ fld P → relPi Q = relPi Q' → Q = Q' := by
      intro Q Q' hQ hQ' e
      by_contra hne
      have hnn := hd Q hQ
      rw [Ne, eqΛr] at hnn
      push_neg at hnn
      obtain ⟨M, N, hMN⟩ := hnn
      have hMN' : relPi Q' M N := by rw [← e]; exact hMN
      have c1 := (mem_sel_iff.1 hMN.1.1).2
      have c2 := (mem_sel_iff.1 hMN'.1.1).2
      obtain ⟨R, hR⟩ := hfne Q hQ
      have hR' : R ∈ fld Q' := by rw [← c2, c1]; exact hR
      exact eqΛ.1 (hex Q Q' ⟨⟨hQ, hQ'⟩, hne⟩) R ⟨hR, hR'⟩
    have hKS : RelPi ⁏ P ∈ Ser := by
      rw [hK]
      exact pm204_21 ⟨hS, smor_symm ⟨_, smorbar_graph (f := relPi)
        fun Q Q' hQ hQ' e => hinj Q Q' hQ hQ' e⟩⟩
    have hfK : fld (RelPi ⁏ P) ⊆ Ser := by
      intro X hX
      rw [hK] at hX
      obtain ⟨Q, hQ, rfl⟩ := mem_fld_graph_semi.1 hX
      exact hPiQ Q hQ
    have WFP : ∀ B : Set ((α → α → Prop) → (α → α → Prop) → Prop), B ⊆ fld P ∧ B.Nonempty →
        (B \ P˘ ʻʻ B).Nonempty := by
      rintro B ⟨hB, Q0, hQ0⟩
      obtain ⟨R0, hR0⟩ := hfne Q0 (hB hQ0)
      obtain ⟨R, ⟨Q, hQB, hRQ⟩, hRn⟩ := hW {R | ∃ Q, Q ∈ B ∧ R ∈ fld Q}
        ⟨fun R ⟨Q, hQB, hRQ⟩ => fldQ Q (hB hQB) hRQ, ⟨R0, Q0, hQ0, hR0⟩⟩
      refine ⟨Q, hQB, ?_⟩
      rintro ⟨Q', hQ'B, hQ'Q⟩
      obtain ⟨S, hS'⟩ := hfne Q' (hB hQ'B)
      exact hRn ⟨S, ⟨Q', hQ'B, hS'⟩,
        (relSigma_apply P S R).2 (Or.inr ⟨Q', Q, ⟨hS', hRQ⟩, hQ'Q⟩)⟩
    have WFK : ∀ B, B ⊆ fld (RelPi ⁏ P) ∧ B.Nonempty → (B \ (RelPi ⁏ P)˘ ʻʻ B).Nonempty := by
      rintro B ⟨hB, X0, hX0⟩
      have hX0' := hB hX0
      rw [hK] at hX0'
      obtain ⟨Q0, hQ0, e0⟩ := mem_fld_graph_semi.1 hX0'
      obtain ⟨Q, ⟨hQf, hQB⟩, hQn⟩ := WFP {Q | Q ∈ fld P ∧ relPi Q ∈ B}
        ⟨fun Q h => h.1, ⟨Q0, hQ0, by rw [← e0]; exact hX0⟩⟩
      refine ⟨relPi Q, hQB, ?_⟩
      rintro ⟨X, hXB, hX⟩
      obtain ⟨Q1, Q2, ⟨e1, e2⟩, h12⟩ := (semi_graph_apply relPi P X (relPi Q)).1 hX
      have hQ2 : Q2 = Q := hinj Q2 Q ⟨Q1, Or.inr h12⟩ hQf e2.symm
      rw [hQ2] at h12
      exact hQn ⟨Q1, ⟨⟨Q, Or.inl h12⟩, by rw [← e1]; exact hXB⟩, h12⟩
    exact pm204_57 ⟨⟨hKS, hfK⟩, WFK⟩

/-- ✱204·581. \[\begin{align}&\vdash :\text{Hp}*204·58.\Sigma ʻP\in \text{Rel}^{2}\text{excl}.\supset .\text{Prod}ʻ\text{Prod}^{;}P,\text{Prod}ʻ\Sigma ʻP\in \text{Ser}\\ &[*174·461·43.*204·58·21]\end{align}\]

**Status.** proved: PM uses ✱174·461·43; here `Prod'K` is like `Π'K` whenever `K ∈ Rel² excl`
(`D` is then one-one on the selections), `Prod;P` is like `P` (or contains `Λ̇` in its field,
whence `Prod'Prod;P = Λ̇`), and ✱204·57 applies to it as in ✱204·58. -/
theorem pm204_581 {α : Type u}
    {P : ((α → α → Prop) → (α → α → Prop) → Prop) →
      ((α → α → Prop) → (α → α → Prop) → Prop) → Prop} :
    ((((P ∈ Ser ∧ fld P ⊆ Ser) ∧ fld (relSigma P) ⊆ Ser) ∧ P ∈ Rel2excl) ∧
      (∀ A : Set (α → α → Prop), A ⊆ fld (relSigma P) ∧ A.Nonempty →
        (A \ (relSigma P)˘ ʻʻ A).Nonempty)) ∧ relSigma P ∈ Rel2excl →
      prodR (ProdR ⁏ P) ∈ Ser ∧ prodR (relSigma P) ∈ Ser := by
  rintro ⟨⟨⟨⟨⟨hS, hC⟩, hCS⟩, hex⟩, hW⟩, hexS⟩
  have h58 := pm204_58 ⟨⟨⟨⟨hS, hC⟩, hCS⟩, hex⟩, hW⟩
  refine ⟨?_, pm204_21 ⟨h58.1, smor_symm (smor_prodR hexS)⟩⟩
  have fldQ : ∀ Q, Q ∈ fld P → fld Q ⊆ fld (relSigma P) := by
    rintro Q hQ R ⟨S, h | h⟩
    · exact ⟨S, Or.inl ((relSigma_apply P R S).2 (Or.inl ⟨Q, hQ, h⟩))⟩
    · exact ⟨S, Or.inr ((relSigma_apply P S R).2 (Or.inl ⟨Q, hQ, h⟩))⟩
  have hexQ : ∀ Q, Q ∈ fld P → Q ∈ Rel2excl := fun Q hQ R R' ⟨⟨hR, hR'⟩, hne⟩ =>
    hexS R R' ⟨⟨fldQ Q hQ hR, fldQ Q hQ hR'⟩, hne⟩
  have WFQ : ∀ Q, Q ∈ fld P → ∀ A : Set (α → α → Prop), A ⊆ fld Q ∧ A.Nonempty →
      (A \ Q˘ ʻʻ A).Nonempty := by
    rintro Q hQ A ⟨hA, hne⟩
    obtain ⟨R, hRA, hRn⟩ := hW A ⟨fun R hR => fldQ Q hQ (hA hR), hne⟩
    exact ⟨R, hRA, fun ⟨S, hSA, hSR⟩ =>
      hRn ⟨S, hSA, (relSigma_apply P S R).2 (Or.inl ⟨Q, hQ, hSR⟩)⟩⟩
  have hPiQ : ∀ Q, Q ∈ fld P → relPi Q ∈ Ser := fun Q hQ =>
    pm204_57 ⟨⟨hC hQ, fun R hR => hCS (fldQ Q hQ hR)⟩, WFQ Q hQ⟩
  have hProdQ : ∀ Q, Q ∈ fld P → prodR Q ∈ Ser := fun Q hQ =>
    pm204_21 ⟨hPiQ Q hQ, smor_symm (smor_prodR (hexQ Q hQ))⟩
  have hselg : ∀ (Q : (α → α → Prop) → (α → α → Prop) → Prop) M, M ∈ fld (relPi Q) →
      M ∈ sel F (fld Q) := by
    intro Q M
    rintro ⟨N, ⟨⟨hM, -⟩, -⟩ | ⟨⟨-, hM⟩, -⟩⟩ <;> exact hM
  have hL : (ProdR ⁏ P) = graph prodR ⁏ P := rfl
  by_cases hd : ∃ Q, Q ∈ fld P ∧ relPi Q = rNull
  · obtain ⟨Q, hQ, h0⟩ := hd
    have hp0 : prodR Q = rNull := by
      show graph dom ⁏ relPi Q = rNull
      rw [h0, eqΛr]
      intro X Y h
      obtain ⟨z, w, -, hzw⟩ := (semi_apply _ _ X Y).1 h
      exact rNull_apply z w hzw
    have hnf : rNull ∈ fld (ProdR ⁏ P) := by
      rw [hL]
      exact mem_fld_graph_semi.2 ⟨Q, hQ, hp0.symm⟩
    have e : relPi (ProdR ⁏ P) = rNull := by
      rw [eqΛr]
      rintro M N ⟨⟨hM, -⟩, -⟩
      obtain ⟨b, -, w, hw | hw⟩ := sel_unique hM hnf
      · exact rNull_apply _ _ hw
      · exact rNull_apply _ _ hw
    have e2 : prodR (ProdR ⁏ P) = rNull := by
      show graph dom ⁏ relPi (ProdR ⁏ P) = rNull
      rw [e, eqΛr]
      intro X Y h
      obtain ⟨z, w, -, hzw⟩ := (semi_apply _ _ X Y).1 h
      exact rNull_apply z w hzw
    rw [e2]
    exact pm204_24
  · push_neg at hd
    have hfne : ∀ Q, Q ∈ fld P → (fld Q).Nonempty := by
      intro Q hQ
      by_contra hn
      apply hd Q hQ
      rw [eqΛr]
      rintro M N ⟨⟨hM, -⟩, R, ⟨b, hb, -⟩, -⟩
      exact hn ⟨R, sel_codom hM ((hb b).2 rfl)⟩
    have same : ∀ Q Q' M M', Q ∈ fld P → Q' ∈ fld P → M ∈ sel F (fld Q) →
        M' ∈ sel F (fld Q') → dom M = dom M' → Q = Q' := by
      intro Q Q' M M' hQ hQ' hM hM' e
      obtain ⟨R, hR⟩ := hfne Q hQ
      obtain ⟨u, hu, huR⟩ := sel_unique hM hR
      have hud : u ∈ dom M' := by rw [← e]; exact ⟨R, (hu u).2 rfl⟩
      obtain ⟨R', hR'⟩ := hud
      have hR'f : R' ∈ fld Q' := sel_codom hM' hR'
      have huR' : u ∈ fld R' := (mem_sel_iff.1 hM').1.2 u R' hR'
      have hRR : R = R' := by
        by_contra hne
        exact eqΛ.1 (hexS R R' ⟨⟨fldQ Q hQ hR, fldQ Q' hQ' hR'f⟩, hne⟩) u ⟨huR, huR'⟩
      rw [← hRR] at hR'f
      by_contra hne
      exact eqΛ.1 (hex Q Q' ⟨⟨hQ, hQ'⟩, hne⟩) R ⟨hR, hR'f⟩
    have hinj : ∀ Q Q', Q ∈ fld P → Q' ∈ fld P → prodR Q = prodR Q' → Q = Q' := by
      intro Q Q' hQ hQ' e
      have hnn := hd Q hQ
      rw [Ne, eqΛr] at hnn
      push_neg at hnn
      obtain ⟨M, N, hMN⟩ := hnn
      have hX : dom M ∈ fld (graph dom ⁏ relPi Q) :=
        ⟨dom N, Or.inl ((semi_graph_apply dom (relPi Q) _ _).2 ⟨M, N, ⟨rfl, rfl⟩, hMN⟩)⟩
      have hX' : dom M ∈ fld (graph dom ⁏ relPi Q') := by
        have e1 : (graph dom ⁏ relPi Q) = prodR Q := rfl
        have e2 : (graph dom ⁏ relPi Q') = prodR Q' := rfl
        rw [e2, ← e, ← e1]
        exact hX
      obtain ⟨M', hM', e'⟩ := mem_fld_graph_semi.1 hX'
      exact same Q Q' M M' hQ hQ' hMN.1.1 (hselg Q' M' hM') e'
    have hLS : ProdR ⁏ P ∈ Ser := by
      rw [hL]
      exact pm204_21 ⟨hS, smor_symm ⟨_, smorbar_graph (f := prodR)
        fun Q Q' hQ hQ' e => hinj Q Q' hQ hQ' e⟩⟩
    have hfL : fld (ProdR ⁏ P) ⊆ Ser := by
      intro X hX
      rw [hL] at hX
      obtain ⟨Q, hQ, rfl⟩ := mem_fld_graph_semi.1 hX
      exact hProdQ Q hQ
    have WFP : ∀ B : Set ((α → α → Prop) → (α → α → Prop) → Prop), B ⊆ fld P ∧ B.Nonempty →
        (B \ P˘ ʻʻ B).Nonempty := by
      rintro B ⟨hB, Q0, hQ0⟩
      obtain ⟨R0, hR0⟩ := hfne Q0 (hB hQ0)
      obtain ⟨R, ⟨Q, hQB, hRQ⟩, hRn⟩ := hW {R | ∃ Q, Q ∈ B ∧ R ∈ fld Q}
        ⟨fun R ⟨Q, hQB, hRQ⟩ => fldQ Q (hB hQB) hRQ, ⟨R0, Q0, hQ0, hR0⟩⟩
      refine ⟨Q, hQB, ?_⟩
      rintro ⟨Q', hQ'B, hQ'Q⟩
      obtain ⟨S, hS'⟩ := hfne Q' (hB hQ'B)
      exact hRn ⟨S, ⟨Q', hQ'B, hS'⟩,
        (relSigma_apply P S R).2 (Or.inr ⟨Q', Q, ⟨hS', hRQ⟩, hQ'Q⟩)⟩
    have WFL : ∀ B, B ⊆ fld (ProdR ⁏ P) ∧ B.Nonempty → (B \ (ProdR ⁏ P)˘ ʻʻ B).Nonempty := by
      rintro B ⟨hB, X0, hX0⟩
      have hX0' := hB hX0
      rw [hL] at hX0'
      obtain ⟨Q0, hQ0, e0⟩ := mem_fld_graph_semi.1 hX0'
      obtain ⟨Q, ⟨hQf, hQB⟩, hQn⟩ := WFP {Q | Q ∈ fld P ∧ prodR Q ∈ B}
        ⟨fun Q h => h.1, ⟨Q0, hQ0, by rw [← e0]; exact hX0⟩⟩
      refine ⟨prodR Q, hQB, ?_⟩
      rintro ⟨X, hXB, hX⟩
      obtain ⟨Q1, Q2, ⟨e1, e2⟩, h12⟩ := (semi_graph_apply prodR P X (prodR Q)).1 hX
      have hQ2 : Q2 = Q := hinj Q2 Q ⟨Q1, Or.inr h12⟩ hQf e2.symm
      rw [hQ2] at h12
      exact hQn ⟨Q1, ⟨⟨Q, Or.inl h12⟩, by rw [← e1]; exact hXB⟩, h12⟩
    have hPiL : relPi (ProdR ⁏ P) ∈ Ser := pm204_57 ⟨⟨hLS, hfL⟩, WFL⟩
    have hexL : ProdR ⁏ P ∈ Rel2excl := by
      rintro X Y ⟨⟨hX, hY⟩, hne⟩
      rw [hL] at hX hY
      obtain ⟨Q, hQ, rfl⟩ := mem_fld_graph_semi.1 hX
      obtain ⟨Q', hQ', rfl⟩ := mem_fld_graph_semi.1 hY
      rw [eqΛ]
      rintro u ⟨hu1, hu2⟩
      have e1 : prodR Q = graph dom ⁏ relPi Q := rfl
      have e2 : prodR Q' = graph dom ⁏ relPi Q' := rfl
      rw [e1] at hu1
      rw [e2] at hu2
      obtain ⟨M, hM, rfl⟩ := mem_fld_graph_semi.1 hu1
      obtain ⟨M', hM', e'⟩ := mem_fld_graph_semi.1 hu2
      exact hne (by rw [same Q Q' M M' hQ hQ' (hselg Q M hM) (hselg Q' M' hM') e'])
    exact pm204_21 ⟨hPiL, smor_symm (smor_prodR hexL)⟩

/-- ✱204·59. \[\begin{align}\vdash \colon\ldotp P,Q\in \text{Ser}:\alpha \subset CʻQ.\exists !\alpha .\supset _{\alpha }.\exists !\alpha -&\breve{Q} ʻʻ\alpha :\supset .\\ &P^{Q}\in \text{Ser}.(P\,\text{exp}\,\,Q)\in \text{Ser}\end{align}\]

**Status.** proved: the proof applies ✱204·57 to `P↓.,;Q` (like `Q`, its field consisting of
relations like `P`, when `P` is not null), then carries the series over by `D` and by `ṡ`, which are
one-one on the selections and on their domains; when `P = Λ̇` there are no selections and
`P exp Q = P^Q = Λ̇`. -/
theorem pm204_59 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop} :
    (P ∈ Ser ∧ Q ∈ Ser) ∧ (∀ A : Set β, A ⊆ fld Q ∧ A.Nonempty → (A \ Q˘ ʻʻ A).Nonempty) →
      rpow P Q ∈ Ser ∧ rexp P Q ∈ Ser := by
  rintro ⟨⟨hP, hQ⟩, hW⟩
  have fldg : ∀ (z : β) (u : α → β → Prop), u ∈ fld (opSemi couple P z) →
      ∃ x, x ∈ fld P ∧ u = x ↓ z := by
    intro z u hu
    rw [fld_opSemi_couple] at hu
    exact hu
  by_cases hPe : rEx P
  · obtain ⟨a, b, hab⟩ := hPe
    have ginj : ∀ z w : β, opSemi couple P z = opSemi couple P w → z = w := by
      intro z w e
      have h1 : opSemi couple P z (a ↓ z) (b ↓ z) :=
        (opSemi_couple_apply P z _ _).2 ⟨a, b, ⟨rfl, rfl⟩, hab⟩
      rw [e] at h1
      obtain ⟨x, x', ⟨e1, -⟩, -⟩ := (opSemi_couple_apply P w _ _).1 h1
      exact (couple_eq_couple_iff.1 e1).2
    have hKQ : smor (graph (opSemi couple P) ⁏ Q) Q :=
      ⟨_, smorbar_graph fun z w _ _ e => ginj z w e⟩
    have hKS : graph (opSemi couple P) ⁏ Q ∈ Ser := pm204_21 ⟨hQ, smor_symm hKQ⟩
    have hfK : fld (graph (opSemi couple P) ⁏ Q) ⊆ Ser := by
      intro R hR
      obtain ⟨z, -, rfl⟩ := mem_fld_graph_semi.1 hR
      have hsm : smor (opSemi couple P z) P := by
        show smor (graph (fun x => x ↓ z) ⁏ P) P
        exact ⟨_, smorbar_graph fun x y _ _ e => (couple_eq_couple_iff.1 e).1⟩
      exact pm204_21 ⟨hP, smor_symm hsm⟩
    have WFK : ∀ B, B ⊆ fld (graph (opSemi couple P) ⁏ Q) ∧ B.Nonempty →
        (B \ (graph (opSemi couple P) ⁏ Q)˘ ʻʻ B).Nonempty := by
      rintro B ⟨hB, X0, hX0⟩
      obtain ⟨z0, hz0, e0⟩ := mem_fld_graph_semi.1 (hB hX0)
      obtain ⟨z, ⟨hzf, hzB⟩, hzn⟩ := hW {z | z ∈ fld Q ∧ opSemi couple P z ∈ B}
        ⟨fun z h => h.1, ⟨z0, hz0, by rw [← e0]; exact hX0⟩⟩
      refine ⟨opSemi couple P z, hzB, ?_⟩
      rintro ⟨X, hXB, hX⟩
      obtain ⟨z1, z2, ⟨e1, e2⟩, h12⟩ := (semi_graph_apply (opSemi couple P) Q X _).1 hX
      have hz2 : z2 = z := (ginj z z2 e2).symm
      rw [hz2] at h12
      exact hzn ⟨z1, ⟨⟨z, Or.inl h12⟩, by rw [← e1]; exact hXB⟩, h12⟩
    have hPi : relPi (graph (opSemi couple P) ⁏ Q) ∈ Ser := pm204_57 ⟨⟨hKS, hfK⟩, WFK⟩
    have selc : ∀ M, M ∈ sel F (fld (graph (opSemi couple P) ⁏ Q)) → ∀ u R, M u R →
        ∃ x z, u = x ↓ z ∧ R = opSemi couple P z := by
      intro M hM u R h
      obtain ⟨z, -, rfl⟩ := mem_fld_graph_semi.1 (sel_codom hM h)
      obtain ⟨x, -, rfl⟩ := fldg z u ((mem_sel_iff.1 hM).1.2 u _ h)
      exact ⟨x, z, rfl, rfl⟩
    have hsel : ∀ M, M ∈ fld (relPi (graph (opSemi couple P) ⁏ Q)) →
        M ∈ sel F (fld (graph (opSemi couple P) ⁏ Q)) := by
      rintro M ⟨N, ⟨⟨hM, -⟩, -⟩ | ⟨⟨-, hM⟩, -⟩⟩ <;> exact hM
    have one : ∀ M N, M ∈ sel F (fld (graph (opSemi couple P) ⁏ Q)) →
        N ∈ sel F (fld (graph (opSemi couple P) ⁏ Q)) → dom M = dom N →
        ∀ u R, M u R → N u R := by
      intro M N hM hN e u R h
      have hu : u ∈ dom N := by rw [← e]; exact ⟨R, h⟩
      obtain ⟨R', hR'⟩ := hu
      obtain ⟨x, z, rfl, rfl⟩ := selc M hM u R h
      obtain ⟨x', z', e', rfl⟩ := selc N hN _ R' hR'
      obtain ⟨-, rfl⟩ := couple_eq_couple_iff.1 e'
      exact hR'
    have dinj : ∀ M N, M ∈ fld (relPi (graph (opSemi couple P) ⁏ Q)) →
        N ∈ fld (relPi (graph (opSemi couple P) ⁏ Q)) → dom M = dom N → M = N := by
      intro M N hM hN e
      funext u R
      exact propext ⟨one M N (hsel M hM) (hsel N hN) e u R,
        one N M (hsel N hN) (hsel M hM) e.symm u R⟩
    have hD : smor (graph dom ⁏ relPi (graph (opSemi couple P) ⁏ Q))
        (relPi (graph (opSemi couple P) ⁏ Q)) :=
      ⟨_, smorbar_graph fun M N hM hN e => dinj M N hM hN e⟩
    have hexp : rexp P Q ∈ Ser := pm204_21 ⟨hPi, smor_symm hD⟩
    have couples : ∀ X, X ∈ fld (graph dom ⁏ relPi (graph (opSemi couple P) ⁏ Q)) →
        ∀ u, u ∈ X → ∃ x z, u = x ↓ z := by
      intro X hX u hu
      obtain ⟨M, hM, rfl⟩ := mem_fld_graph_semi.1 hX
      obtain ⟨R, hR⟩ := hu
      obtain ⟨x, z, e, -⟩ := selc M (hsel M hM) u R hR
      exact ⟨x, z, e⟩
    have sub : ∀ X Y : Set (α → β → Prop), (∀ u, u ∈ Y → ∃ x z, u = x ↓ z) →
        sumRel X = sumRel Y → (∀ u, u ∈ X → ∃ x z, u = x ↓ z) → X ⊆ Y := by
      intro X Y hY e hXc u hu
      obtain ⟨x, z, rfl⟩ := hXc u hu
      have h1 : sumRel X x z := ⟨_, hu, (couple_apply x z x z).2 ⟨rfl, rfl⟩⟩
      rw [e] at h1
      obtain ⟨v, hv, hvxz⟩ := h1
      obtain ⟨x', z', rfl⟩ := hY v hv
      obtain ⟨rfl, rfl⟩ := (couple_apply x' z' x z).1 hvxz
      exact hv
    have sinj : ∀ X Y, X ∈ fld (graph dom ⁏ relPi (graph (opSemi couple P) ⁏ Q)) →
        Y ∈ fld (graph dom ⁏ relPi (graph (opSemi couple P) ⁏ Q)) →
        sumRel X = sumRel Y → X = Y := fun X Y hX hY e =>
      Set.Subset.antisymm (sub X Y (couples Y hY) e (couples X hX))
        (sub Y X (couples X hX) e.symm (couples Y hY))
    have hpow : rpow P Q ∈ Ser :=
      pm204_21 ⟨hexp, smor_symm ⟨_, smorbar_graph (f := sumRel) fun X Y hX hY e =>
        sinj X Y hX hY e⟩⟩
    exact ⟨hpow, hexp⟩
  · have hnull : relPi (graph (opSemi couple P) ⁏ Q) = rNull := by
      rw [eqΛr]
      rintro M N ⟨⟨hM, -⟩, R, ⟨b, hb, -⟩, -⟩
      have hbR := (hb b).2 rfl
      obtain ⟨z, -, rfl⟩ := mem_fld_graph_semi.1 (sel_codom hM hbR)
      obtain ⟨x, hx, -⟩ := fldg z b ((mem_sel_iff.1 hM).1.2 b _ hbR)
      obtain ⟨y, hxy | hxy⟩ := hx
      · exact hPe ⟨x, y, hxy⟩
      · exact hPe ⟨y, x, hxy⟩
    have hexp : rexp P Q = rNull := by
      show graph dom ⁏ relPi (graph (opSemi couple P) ⁏ Q) = rNull
      rw [hnull, eqΛr]
      intro X Y h
      obtain ⟨z, w, -, hzw⟩ := (semi_apply _ _ X Y).1 h
      exact rNull_apply z w hzw
    have hpow : rpow P Q = rNull := by
      show graph sumRel ⁏ rexp P Q = rNull
      rw [hexp, eqΛr]
      intro X Y h
      obtain ⟨z, w, -, hzw⟩ := (semi_apply _ _ X Y).1 h
      exact rNull_apply z w hzw
    rw [hpow, hexp]
    exact ⟨pm204_24, pm204_24⟩

/-- ✱204·6. \(\vdash :P\in \text{trans} .\supset .\alpha \cup \breve{P} ʻʻ\alpha \subset pʻ\overleftarrow{P}ʻʻpʻ\overrightarrow{P}ʻʻ\alpha \) -/
theorem pm204_6 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → A ∪ P˘ ʻʻ A ⊆ prodCls (Rbwd P ʻʻ prodCls (Rfwd P ʻʻ A)) := by
  intro ht x hx
  rw [mem_prodCls_Rbwd]
  intro y hy
  rw [mem_prodCls_Rfwd] at hy
  rcases hx with hx | ⟨a, ha, hax⟩
  · exact hy x hx
  · exact mem_transR.1 ht y a x ⟨hy a ha, hax⟩

/-- ✱204·61. \(\vdash :P\in \text{Rl}ʻJ\cap \text{connex} .\supset .CʻP\cap pʻ\overleftarrow{P}ʻʻpʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)\subset \alpha \cup \breve{P} ʻʻ\alpha\) -/
theorem pm204_61 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ rl J ∩ connex →
      fld P ∩ prodCls (Rbwd P ʻʻ prodCls (Rfwd P ʻʻ (A ∩ fld P))) ⊆ A ∪ P˘ ʻʻ A := by
  rintro ⟨hJ, hc⟩ x ⟨hx, hp⟩
  by_contra hn
  have hxA : x ∉ A := fun h => hn (Or.inl h)
  have hxP : x ∈ prodCls (Rfwd P ʻʻ (A ∩ fld P)) := by
    rw [mem_prodCls_Rfwd]
    rintro a ⟨haA, ha⟩
    have hne : x ≠ a := fun e => hxA (by rw [e]; exact haA)
    rcases cxne hc hx ha hne with h | h
    · exact h
    · exact (hn (Or.inr ⟨a, haA, h⟩)).elim
  exact mem_rl_J.1 hJ x (mem_prodCls_Rbwd.1 hp x hxP)

/-- ✱204·62. \(\vdash :P\in \text{Ser}.\supset .CʻP\cap pʻ\overleftarrow{P}ʻʻpʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP) = (\alpha \cap CʻP)\cup \breve{P} ʻʻ\alpha\) -/
theorem pm204_62 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser → fld P ∩ prodCls (Rbwd P ʻʻ prodCls (Rfwd P ʻʻ (A ∩ fld P))) =
      (A ∩ fld P) ∪ P˘ ʻʻ A := by
  intro hS
  apply Set.Subset.antisymm
  · intro x hx
    rcases pm204_61 ⟨hS.1.1, hS.2⟩ hx with h | h
    · exact Or.inl ⟨h, hx.1⟩
    · exact Or.inr h
  · intro x hx
    have hx' : x ∈ (A ∩ fld P) ∪ P˘ ʻʻ (A ∩ fld P) := by
      rcases hx with h | ⟨a, ha, hax⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, ⟨ha, ⟨x, Or.inl hax⟩⟩, hax⟩
    refine ⟨?_, pm204_6 hS.1.2 hx'⟩
    rcases hx with h | ⟨a, -, hax⟩
    · exact h.2
    · exact ⟨a, Or.inr hax⟩

/-- ✱204·63. \(\vdash :P\in \text{Ser}.\exists !pʻ\overrightarrow{P}ʻʻ\alpha .\supset .pʻ\overleftarrow{P}ʻʻpʻ\overrightarrow{P}ʻʻ\alpha =\alpha \cup \breve{P} ʻʻ\alpha\) -/
theorem pm204_63 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ Ser ∧ (prodCls (Rfwd P ʻʻ A)).Nonempty →
      prodCls (Rbwd P ʻʻ prodCls (Rfwd P ʻʻ A)) = A ∪ P˘ ʻʻ A := by
  rintro ⟨hS, z0, hz0⟩
  have hA : A ⊆ fld P := fun a ha => ⟨z0, Or.inr (mem_prodCls_Rfwd.1 hz0 a ha)⟩
  have e : A ∩ fld P = A := Set.inter_eq_left.2 hA
  have h := pm204_62 (A := A) hS
  rw [e] at h
  rw [← h]
  ext x
  constructor
  · intro hx
    exact ⟨⟨z0, Or.inr (mem_prodCls_Rbwd.1 hx z0 hz0)⟩, hx⟩
  · exact fun hx => hx.2

/-- ✱204·64. \(\vdash :P\in \text{Ser}.x\in \text{D}ʻP.\supset .pʻ\overrightarrow{P}ʻʻ\overleftarrow{P}ʻx=\overrightarrow{P}_{*}ʻx\) -/
theorem pm204_64 {α : Type u} {P : α → α → Prop} {x : α} :
    P ∈ Ser ∧ x ∈ dom P → prodCls (Rfwd P ʻʻ rels P x) = refs (anc P) x := by
  rintro ⟨hS, y0, hy0⟩
  have hx : x ∈ fld P := ⟨y0, Or.inl hy0⟩
  have ht := hS.1.2
  have irr := mem_rl_J.1 hS.1.1
  rw [pm201_521 ⟨ht, hx⟩]
  ext z
  constructor
  · intro hz
    rw [mem_prodCls_Rfwd] at hz
    have hzf : z ∈ fld P := ⟨y0, Or.inl (hz y0 hy0)⟩
    by_cases e : z = x
    · exact Or.inr e
    · rcases cxne hS.2 hzf hx e with h | h
      · exact Or.inl h
      · exact (irr z (hz z h)).elim
  · rintro (h | h)
    · exact mem_prodCls_Rfwd.2 fun y hy => mem_transR.1 ht z x y ⟨h, hy⟩
    · have e : z = x := h
      rw [e]
      exact mem_prodCls_Rfwd.2 fun y hy => hy

/-- ✱204·65. \(\vdash :P\in \text{Ser}.x\in CʻP.\supset .pʻ\overrightarrow{P}ʻʻ\overleftarrow{P}ʻx\cap CʻP=\overrightarrow{P}_{*}ʻx\) -/
theorem pm204_65 {α : Type u} {P : α → α → Prop} {x : α} :
    P ∈ Ser ∧ x ∈ fld P → prodCls (Rfwd P ʻʻ rels P x) ∩ fld P = refs (anc P) x := by
  rintro ⟨hS, hx⟩
  have ht := hS.1.2
  have irr := mem_rl_J.1 hS.1.1
  rw [pm201_521 ⟨ht, hx⟩]
  ext z
  constructor
  · rintro ⟨hz, hzf⟩
    rw [mem_prodCls_Rfwd] at hz
    by_cases e : z = x
    · exact Or.inr e
    · rcases cxne hS.2 hzf hx e with h | h
      · exact Or.inl h
      · exact (irr z (hz z h)).elim
  · rintro (h | h)
    · refine ⟨mem_prodCls_Rfwd.2 fun y hy => mem_transR.1 ht z x y ⟨h, hy⟩, ⟨x, Or.inl h⟩⟩
    · have e : z = x := h
      rw [e]
      exact ⟨mem_prodCls_Rfwd.2 fun y hy => hy, hx⟩

/-- ✱204·7. \(\vdash :P\in \text{Ser}.\supset .P_{1}\in 1\rightarrow 1 \quad[*201·63.*202·7]\) -/
theorem pm204_7 {α : Type u} {P : α → α → Prop} : P ∈ Ser → P1 P ∈ arrow one one := by
  intro hS
  rw [pm201_63 ⟨hS.1.2, hS.1.1⟩]
  exact pm202_7 hS.2

/-- ✱204·71. \(\vdash :P\in \text{Ser}.xP_{1}y.\supset .\overrightarrow{P}ʻy=\overrightarrow{P}ʻx\cup \iota ʻx \quad[*202·72.*201·63]\) -/
theorem pm204_71 {α : Type u} {P : α → α → Prop} {x y : α} :
    P ∈ Ser ∧ P1 P x y → refs P y = refs P x ∪ ι x := by
  rintro ⟨hS, h⟩
  rw [pm201_63 ⟨hS.1.2, hS.1.1⟩] at h
  exact pm202_72 ⟨⟨hS.1.2, hS.2⟩, h⟩

/-- ✱204·72. \(\vdash \colon\colon P\in \text{Ser}.\supset \colon\ldotp xP_{1}y.\equiv :xPy:xPz.z\neq y.\supset _{z}.yPz\) -/
theorem pm204_72 {α : Type u} {P : α → α → Prop} {x y : α} :
    P ∈ Ser → (P1 P x y ↔ P x y ∧ ∀ z, P x z ∧ z ≠ y → P y z) := by
  intro hS
  have tr := mem_transR.1 hS.1.2
  have irr := mem_rl_J.1 hS.1.1
  rw [P1_iff_of_transR hS.1.2 hS.1.1]
  constructor
  · rintro ⟨hxy, hn⟩
    refine ⟨hxy, ?_⟩
    rintro z ⟨hxz, hne⟩
    rcases cxne hS.2 ⟨x, Or.inr hxz⟩ ⟨x, Or.inr hxy⟩ hne with h | h
    · exact (hn ⟨z, hxz, h⟩).elim
    · exact h
  · rintro ⟨hxy, h⟩
    refine ⟨hxy, ?_⟩
    rintro ⟨z, hxz, hzy⟩
    have hne : z ≠ y := fun e => irr z (by rw [← e] at hzy; exact hzy)
    exact irr z (tr z y z ⟨hzy, h z ⟨hxz, hne⟩⟩)

/-! ### Helper lemmas for ✱205 (not PM propositions) -/

section Helpers205

variable {α : Type u} {β : Type v}

private theorem min_unique {P : α → α → Prop} (hc : P ∈ connex) {A : Set α} {x y : α}
    (hx : minP P x A) (hy : minP P y A) : x = y := by
  rw [minP_iff] at hx hy
  by_contra hne
  rcases cxne hc hx.1.2 hy.1.2 hne with h | h
  · exact hy.2 x hx.1.1 h
  · exact hx.2 y hy.1.1 h

private theorem max_unique {P : α → α → Prop} (hc : P ∈ connex) {A : Set α} {x y : α}
    (hx : maxP P x A) (hy : maxP P y A) : x = y :=
  min_unique (pm202_11.1 hc) hx hy

private theorem min_desc {P : α → α → Prop} (hc : P ∈ connex) {A : Set α} {m : α}
    (hm : minP P m A) (ψ : α → Prop) : Desc (minP P) A ψ ↔ ψ m :=
  desc_iff_of (fun z => ⟨fun hz => min_unique hc hz hm, fun e => by rw [e]; exact hm⟩) ψ

private theorem max_desc {P : α → α → Prop} (hc : P ∈ connex) {A : Set α} {m : α}
    (hm : maxP P m A) (ψ : α → Prop) : Desc (maxP P) A ψ ↔ ψ m :=
  desc_iff_of (fun z => ⟨fun hz => max_unique hc hz hm, fun e => by rw [e]; exact hm⟩) ψ

/-- `min_P'α` depends only on `α ∩ C'P`. -/
private theorem minP_congr {P : α → α → Prop} {B C : Set α} (h : B ∩ fld P = C ∩ fld P) :
    refs (minP P) B = refs (minP P) C := by
  have k : ∀ y, y ∈ fld P → (y ∈ B ↔ y ∈ C) := fun y hy => by
    constructor
    · intro hyB
      have : y ∈ C ∩ fld P := h ▸ ⟨hyB, hy⟩
      exact this.1
    · intro hyC
      have : y ∈ B ∩ fld P := h.symm ▸ ⟨hyC, hy⟩
      exact this.1
  ext x
  show minP P x B ↔ minP P x C
  rw [minP_iff, minP_iff]
  constructor
  · rintro ⟨⟨hxB, hx⟩, hn⟩
    exact ⟨⟨(k x hx).1 hxB, hx⟩, fun y hyC hyx => hn y ((k y ⟨x, Or.inl hyx⟩).2 hyC) hyx⟩
  · rintro ⟨⟨hxC, hx⟩, hn⟩
    exact ⟨⟨(k x hx).2 hxC, hx⟩, fun y hyB hyx => hn y ((k y ⟨x, Or.inl hyx⟩).1 hyB) hyx⟩

private theorem maxP_congr {P : α → α → Prop} {B C : Set α} (h : B ∩ fld P = C ∩ fld P) :
    refs (maxP P) B = refs (maxP P) C :=
  minP_congr (P := P˘) (by rw [fld_cnv]; exact h)

private theorem mem_refs_maxP {P : α → α → Prop} {A : Set α} {x : α} :
    x ∈ refs (maxP P) A ↔ x ∈ (A ∩ fld P) \ P ʻʻ A := by
  show x ∈ (A ∩ fld P˘) \ P˘˘ ʻʻ A ↔ _
  rw [fld_cnv]
  rfl

private theorem minP_union {P : α → α → Prop} {A B : Set α} (ht : P ∈ transR)
    (hB : B ⊆ P˘ ʻʻ A) : refs (minP P) (A ∪ B) = refs (minP P) A := by
  ext x
  show minP P x (A ∪ B) ↔ minP P x A
  rw [minP_iff, minP_iff]
  constructor
  · rintro ⟨⟨hx | hx, hf⟩, hn⟩
    · exact ⟨⟨hx, hf⟩, fun y hy => hn y (Or.inl hy)⟩
    · obtain ⟨a, ha, hax⟩ := hB hx
      exact (hn a (Or.inl ha) hax).elim
  · rintro ⟨⟨hx, hf⟩, hn⟩
    refine ⟨⟨Or.inl hx, hf⟩, ?_⟩
    rintro y (hy | hy) hyx
    · exact hn y hy hyx
    · obtain ⟨a, ha, hay⟩ := hB hy
      exact hn a ha (mem_transR.1 ht a y x ⟨hay, hyx⟩)

/-- The minima with respect to `P ⥏ β`, when `C'(P ⥏ β) = β ∩ C'P`. -/
private theorem minP_fres {P : α → α → Prop} {A B : Set α} (hf : fld (P ⥏ B) = B ∩ fld P) :
    refs (minP (P ⥏ B)) A = refs (minP P) (A ∩ B) := by
  ext x
  show minP (P ⥏ B) x A ↔ minP P x (A ∩ B)
  rw [minP_iff, minP_iff, hf]
  constructor
  · rintro ⟨⟨hxA, hxB, hx⟩, hn⟩
    exact ⟨⟨⟨hxA, hxB⟩, hx⟩, fun y ⟨hyA, hyB⟩ hyx => hn y hyA ⟨⟨hyB, hyx⟩, hxB⟩⟩
  · rintro ⟨⟨⟨hxA, hxB⟩, hx⟩, hn⟩
    exact ⟨⟨hxA, hxB, hx⟩, fun y hyA ⟨⟨hyB, hyx⟩, _⟩ => hn y ⟨hyA, hyB⟩ hyx⟩

end Helpers205

/-!
## [✱205] Maximum and minimum points

*(Vol. 2, p. 559)*

> *Summary of* *205.
>
> …

**Lean reading.** `min_P`, `max_P` are `minP P`, `maxP P` (✱93, Defs/Part2; `maxP P = minP P˘` by `rfl`); the
class of minima `min⃗_P'α` is `refs (minP P) A`; the description `min_P'α` is
`Desc (minP P) A` (it need not exist), `E!min_P'α` is `EDesc (minP P) A`; `min(P⥏β)` is
`minP (P ⥏ B)`; `x{min(Σ'P)}α` is `minP (relSigma P) x A`; `F̆''α` is `F˘ ʻʻ A`; `∈_Δ'κ`
is `sel memRel K`, `Cls² mult` is `Cls2Mult`; `P̆_*` is `ancCnv P`; `B⃗'P̆` (the last terms)
is `refs Beg P˘`. Every description has the smallest scope; of two descriptions the first has
the larger scope (`min_P'α = min_P'β` is `Desc (minP P) A (fun m => Desc (minP P) B (m = ·))`);
`R'S'y` is `Desc2 R S y` (✱30·02), and `E!P̆_1'B'P` (✱205·256) is
`EBang (fun x => Desc Beg P (fun b => x P̆_1 b))`, the inner description having the smallest
scope. ✱205·261 and ✱205·91 are false as printed (they rest on ✱202·54); their corrected forms
are proved, and so is the failure of the printed ones. The e-text prints ✱205·21 before
✱205·1.

**Status.** proved (all propositions; ✱205·261, ✱205·91 proved (corrected); ✱205·254, ✱205·36, ✱205·65,
✱205·66, ✱205·9 proved (reading); see their docstrings).
-/

/-- ✱205·21. \(\vdash :P\in \text{connex} .\text{E}!\text{min}_{P}ʻ\alpha .y\in \alpha \cap CʻP-{℩}ʻ\text{min}_{P}ʻ\alpha .\supset .\text{min}_{P}ʻ\alpha Py\) -/
theorem pm205_21 {α : Type u} {P : α → α → Prop} {A : Set α} {y : α} :
    (P ∈ connex ∧ EDesc (minP P) A) ∧ Desc (minP P) A (fun m => y ∈ (A ∩ fld P) \ ι m) →
      Desc (minP P) A (fun m => P m y) := by
  rintro ⟨⟨hc, m, hm⟩, h⟩
  obtain ⟨⟨hyA, hy⟩, hne⟩ := (desc_iff_of hm _).1 h
  have hmin : minP P m A := (hm m).2 rfl
  obtain ⟨⟨-, hmf⟩, hmn⟩ := minP_iff.1 hmin
  refine (desc_iff_of hm _).2 ?_
  rcases cxne hc hmf hy (fun e => hne (show y = m from e.symm)) with h1 | h1
  · exact h1
  · exact (hmn y hyA h1).elim

/-- ✱205·1. \(\vdash :x\text{min}_{P}\alpha .\equiv .x\in \alpha \cap CʻP-\breve{P} ʻʻ\alpha \quad[*93·11]\) -/
theorem pm205_1 {α : Type u} {P : α → α → Prop} {x : α} {A : Set α} :
    minP P x A ↔ x ∈ (A ∩ fld P) \ P˘ ʻʻ A := Iff.rfl

/-- ✱205·101. \(\vdash :x\text{max}_{P}\alpha .\equiv .x\in \alpha \cap CʻP-Pʻʻ\alpha .\equiv .x \text{min}(\breve{P} )\alpha \quad[*93·115]\) -/
theorem pm205_101 {α : Type u} {P : α → α → Prop} {x : α} {A : Set α} :
    (maxP P x A ↔ x ∈ (A ∩ fld P) \ P ʻʻ A) ∧ (x ∈ (A ∩ fld P) \ P ʻʻ A ↔ minP P˘ x A) :=
  ⟨mem_refs_maxP, mem_refs_maxP.symm⟩

/-- ✱205·102. \(\vdash .\text{max}_{P}=\text{min}(\breve{P} ) \quad[*93·114]\) -/
theorem pm205_102 {α : Type u} {P : α → α → Prop} : maxP P = minP P˘ := rfl

/-- ✱205·11. \(\vdash .\overrightarrow{\text{min}}_{P}ʻ\alpha =\alpha \cap CʻP-\breve{P} ʻʻ\alpha \quad [*93·111]\) -/
theorem pm205_11 {α : Type u} {P : α → α → Prop} {A : Set α} :
    refs (minP P) A = (A ∩ fld P) \ P˘ ʻʻ A := rfl

/-- ✱205·111. \(\vdash .\overrightarrow{\text{max}}_{P}ʻ\alpha =\alpha \cap CʻP-Pʻʻ\alpha \quad [*93·116]\) -/
theorem pm205_111 {α : Type u} {P : α → α → Prop} {A : Set α} :
    refs (maxP P) A = (A ∩ fld P) \ P ʻʻ A :=
  Set.ext fun _ => mem_refs_maxP

/-- ✱205·12. \(\vdash .\overrightarrow{B}ʻP=\overrightarrow{\text{min}}_{P}ʻ\text{D}ʻP=\overrightarrow{\text{min}}_{P}ʻCʻP \quad[*93·112]\) -/
theorem pm205_12 {α : Type u} {P : α → α → Prop} :
    refs Beg P = refs (minP P) (dom P) ∧ refs (minP P) (dom P) = refs (minP P) (fld P) := by
  have key : ∀ B : Set α, dom P ⊆ B → B ⊆ fld P → refs (minP P) B = refs Beg P := by
    intro B h1 h2
    ext x
    show minP P x B ↔ x ∈ dom P ∧ x ∉ codom P
    rw [minP_iff]
    constructor
    · rintro ⟨⟨hxB, hx⟩, hn⟩
      have hc : x ∉ codom P := fun ⟨y, hyx⟩ => hn y (h1 ⟨x, hyx⟩) hyx
      obtain ⟨y, hxy | hyx⟩ := hx
      · exact ⟨⟨y, hxy⟩, hc⟩
      · exact (hc ⟨y, hyx⟩).elim
    · rintro ⟨⟨y, hxy⟩, hc⟩
      exact ⟨⟨h1 ⟨y, hxy⟩, ⟨y, Or.inl hxy⟩⟩, fun z _ hzx => hc ⟨z, hzx⟩⟩
  have e1 := key (dom P) subset_rfl (fun x ⟨y, h⟩ => ⟨y, Or.inl h⟩)
  have e2 := key (fld P) (fun x ⟨y, h⟩ => ⟨y, Or.inl h⟩) subset_rfl
  exact ⟨e1.symm, e1.trans e2.symm⟩

/-- ✱205·121. \(\vdash .\overrightarrow{B}ʻ\breve{P} =\overrightarrow{\text{max}}_{P}ʻ\text{ᗡ}ʻP=\overrightarrow{\text{max}}_{P}ʻCʻP \quad[*93·117]\) -/
theorem pm205_121 {α : Type u} {P : α → α → Prop} :
    refs Beg P˘ = refs (maxP P) (codom P) ∧ refs (maxP P) (codom P) = refs (maxP P) (fld P) := by
  have h := pm205_12 (P := P˘)
  rw [fld_cnv] at h
  exact h

/-- ✱205·122. \(\vdash :\overrightarrow{\text{min}}_{P}ʻ\alpha =\Lambda .\equiv .\alpha \cap CʻP\subset \breve{P} ʻʻ\alpha \quad[*205·11.*24·3]\) -/
theorem pm205_122 {α : Type u} {P : α → α → Prop} {A : Set α} :
    refs (minP P) A = Λ ↔ A ∩ fld P ⊆ P˘ ʻʻ A := by
  rw [eqΛ]
  constructor
  · intro h x hx
    by_contra hn
    exact h x ⟨hx, hn⟩
  · rintro h x ⟨hx, hn⟩
    exact hn (h hx)

/-- ✱205·123. \(\vdash :\overrightarrow{\text{max}}_{P}ʻ\alpha =\Lambda .\equiv .\alpha \cap CʻP\subset Pʻʻ\alpha\) -/
theorem pm205_123 {α : Type u} {P : α → α → Prop} {A : Set α} :
    refs (maxP P) A = Λ ↔ A ∩ fld P ⊆ P ʻʻ A := by
  rw [pm205_111, eqΛ]
  constructor
  · intro h x hx
    by_contra hn
    exact h x ⟨hx, hn⟩
  · rintro h x ⟨hx, hn⟩
    exact hn (h hx)

/-- ✱205·13. \(\vdash .\overrightarrow{\text{min}}_{P}ʻ\alpha \cup \breve{P} ʻʻ\alpha =(\alpha \cap CʻP)\cup \breve{P} ʻʻ\alpha \quad[*22·91.*205·11]\) -/
theorem pm205_13 {α : Type u} {P : α → α → Prop} {A : Set α} :
    refs (minP P) A ∪ P˘ ʻʻ A = (A ∩ fld P) ∪ P˘ ʻʻ A :=
  Set.sdiff_union_self

/-- ✱205·131. \(\vdash .\overrightarrow{\text{max}}_{P}ʻ\alpha \cup Pʻʻ\alpha =(\alpha \cap CʻP)\cup Pʻʻ\alpha\) -/
theorem pm205_131 {α : Type u} {P : α → α → Prop} {A : Set α} :
    refs (maxP P) A ∪ P ʻʻ A = (A ∩ fld P) ∪ P ʻʻ A := by
  rw [pm205_111]
  exact Set.sdiff_union_self

/-- ✱205·14. \(\vdash .\overrightarrow{\text{min}}_{P}ʻ\alpha =\hat{x} \{x\in \alpha \cap CʻP.\alpha \cap \overrightarrow{P}ʻx=\Lambda\} \quad[*37·462.*205·11]\) -/
theorem pm205_14 {α : Type u} {P : α → α → Prop} {A : Set α} :
    refs (minP P) A = {x | x ∈ A ∩ fld P ∧ A ∩ refs P x = Λ} := by
  ext x
  show minP P x A ↔ _
  rw [minP_iff]
  apply and_congr Iff.rfl
  rw [eqΛ]
  exact ⟨fun h y ⟨hy, hyx⟩ => h y hy hyx, fun h y hy hyx => h y ⟨hy, hyx⟩⟩

/-- ✱205·141. \(\vdash .\overrightarrow{\text{max}}_{P}ʻ\alpha =\hat{x} \{x\in \alpha \cap CʻP.\alpha \cap \overleftarrow{P}ʻx=\Lambda\}\) -/
theorem pm205_141 {α : Type u} {P : α → α → Prop} {A : Set α} :
    refs (maxP P) A = {x | x ∈ A ∩ fld P ∧ A ∩ rels P x = Λ} := by
  ext x
  show maxP P x A ↔ _
  rw [maxP_iff]
  apply and_congr Iff.rfl
  rw [eqΛ]
  exact ⟨fun h y ⟨hy, hxy⟩ => h y hy hxy, fun h y hy hxy => h y ⟨hy, hxy⟩⟩

/-- ✱205·15. \(\vdash .\overrightarrow{\text{min}}_{P}ʻ(\alpha \cap CʻP)=\overrightarrow{\text{min}}_{P}ʻ\alpha \quad[*37·265.*205·11]\) -/
theorem pm205_15 {α : Type u} {P : α → α → Prop} {A : Set α} :
    refs (minP P) (A ∩ fld P) = refs (minP P) A :=
  minP_congr (by rw [Set.inter_assoc, Set.inter_self])

/-- ✱205·151. \(\vdash .\overrightarrow{\text{max}}_{P}ʻ(\alpha \cap CʻP)=\overrightarrow{\text{max}}_{P}ʻ\alpha\) -/
theorem pm205_151 {α : Type u} {P : α → α → Prop} {A : Set α} :
    refs (maxP P) (A ∩ fld P) = refs (maxP P) A :=
  maxP_congr (by rw [Set.inter_assoc, Set.inter_self])

/-- ✱205·16. \(\vdash .\overrightarrow{\text{min}}_{P}ʻ\Lambda =\Lambda \quad[*205·11.*24·23]\) -/
theorem pm205_16 {α : Type u} {P : α → α → Prop} : refs (minP P) Λ = Λ := by
  rw [eqΛ]
  rintro x ⟨⟨hx, -⟩, -⟩
  exact eqΛ.1 rfl x hx

/-- ✱205·161. \(\vdash .\overrightarrow{\text{max}}_{P}ʻ\Lambda =\Lambda\) -/
theorem pm205_161 {α : Type u} {P : α → α → Prop} : refs (maxP P) Λ = Λ := by
  rw [eqΛ]
  rintro x ⟨⟨hx, -⟩, -⟩
  exact eqΛ.1 rfl x hx

/-- ✱205·17. \[\begin{align}\vdash \colon\ldotp x\in (\alpha \cap CʻP).\supset _{x}.{\sim}(xPx):\alpha &\cap CʻP\in 1:\supset .\\ &\overrightarrow{\text{min}}_{P}ʻ\alpha =\overrightarrow{\text{max}}_{P}ʻ\alpha =\alpha \cap CʻP\end{align}\] -/
theorem pm205_17 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (∀ x, x ∈ A ∩ fld P → ¬P x x) ∧ A ∩ fld P ∈ (one : Set (Set α)) →
      refs (minP P) A = refs (maxP P) A ∧ refs (maxP P) A = A ∩ fld P := by
  rintro ⟨hirr, h1⟩
  obtain ⟨c, hc⟩ := mem_one_iff.1 h1
  have emin : refs (minP P) A = A ∩ fld P := by
    ext x
    show minP P x A ↔ _
    rw [minP_iff]
    refine ⟨fun h => h.1, fun hx => ⟨hx, fun y hy hyx => ?_⟩⟩
    have e1 := (hc y).1 ⟨hy, ⟨x, Or.inl hyx⟩⟩
    have e2 := (hc x).1 hx
    rw [e1, ← e2] at hyx
    exact hirr x hx hyx
  have emax : refs (maxP P) A = A ∩ fld P := by
    ext x
    show maxP P x A ↔ _
    rw [maxP_iff]
    refine ⟨fun h => h.1, fun hx => ⟨hx, fun y hy hxy => ?_⟩⟩
    have e1 := (hc y).1 ⟨hy, ⟨x, Or.inr hxy⟩⟩
    have e2 := (hc x).1 hx
    rw [e1, ← e2] at hxy
    exact hirr x hx hxy
  exact ⟨emin.trans emax.symm, emax⟩

/-- ✱205·18. \(\vdash :{\sim}(xPx).x\in CʻP.\supset .\text{min}_{P}ʻ\iota ʻx=\text{max}_{P}ʻ\iota ʻx=x\) -/
theorem pm205_18 {α : Type u} {P : α → α → Prop} {x : α} :
    ¬P x x ∧ x ∈ fld P →
      Desc (minP P) (ι x) (fun a => Desc (maxP P) (ι x) (fun b => a = b)) ∧
        Desc (maxP P) (ι x) (fun b => b = x) := by
  rintro ⟨hxx, hx⟩
  have hmin : ∀ z, minP P z (ι x) ↔ z = x := by
    intro z
    rw [minP_iff]
    constructor
    · exact fun h => h.1.1
    · intro e
      rw [e]
      exact ⟨⟨rfl, hx⟩, fun y hy hyx => hxx (by rw [show y = x from hy] at hyx; exact hyx)⟩
  have hmax : ∀ z, maxP P z (ι x) ↔ z = x := by
    intro z
    rw [maxP_iff]
    constructor
    · exact fun h => h.1.1
    · intro e
      rw [e]
      exact ⟨⟨rfl, hx⟩, fun y hy hxy => hxx (by rw [show y = x from hy] at hxy; exact hxy)⟩
  exact ⟨(desc_iff_of hmin _).2 ((desc_iff_of hmax _).2 rfl), (desc_iff_of hmax _).2 rfl⟩

/-- ✱205·181. \(\vdash :xPy.{\sim}(xPx).{\sim}(yPx).\supset .\text{min}_{P}ʻ(\iota ʻx\cup \iota ʻy)=x\) -/
theorem pm205_181 {α : Type u} {P : α → α → Prop} {x y : α} :
    (P x y ∧ ¬P x x) ∧ ¬P y x → Desc (minP P) (ι x ∪ ι y) (fun m => m = x) := by
  rintro ⟨⟨hxy, hxx⟩, hyx⟩
  have hmin : ∀ z, minP P z (ι x ∪ ι y) ↔ z = x := by
    intro z
    rw [minP_iff]
    constructor
    · rintro ⟨⟨hz | hz, -⟩, hn⟩
      · exact hz
      · have e : z = y := hz
        rw [e] at hn
        exact (hn x (Or.inl rfl) hxy).elim
    · intro e
      rw [e]
      refine ⟨⟨Or.inl rfl, ⟨y, Or.inl hxy⟩⟩, ?_⟩
      rintro w (hw | hw) hwx
      · rw [show w = x from hw] at hwx
        exact hxx hwx
      · rw [show w = y from hw] at hwx
        exact hyx hwx
  exact (desc_iff_of hmin _).2 rfl

/-- ✱205·182. \(\vdash :P^{2}\,\unicode{x2abd}\, J.xPy.\supset .\text{min}_{P}ʻ(\iota ʻx\cup \iota ʻy)=x\) -/
theorem pm205_182 {α : Type u} {P : α → α → Prop} {x y : α} :
    rsq P ⪽ J ∧ P x y → Desc (minP P) (ι x ∪ ι y) (fun m => m = x) := by
  rintro ⟨hJ, hxy⟩
  exact pm205_181 ⟨⟨hxy, fun h => pm200_36 hJ x x h rfl⟩, fun h => hJ x x ⟨y, hxy, h⟩ rfl⟩

/-- ✱205·183. \[\begin{align}\vdash \colon\ldotp P^{2} \,\unicode{x2abd}\, J . P \in \text{connex} . &x, y \in CʻP . \supset :\\ &\text{min}_{P}ʻ({℩}ʻx \cup {℩}ʻy) = x . \lor . \text{min}_{P}ʻ({℩}ʻx \cup {℩}ʻy) = y\end{align}\] -/
theorem pm205_183 {α : Type u} {P : α → α → Prop} {x y : α} :
    (rsq P ⪽ J ∧ P ∈ connex) ∧ (x ∈ fld P ∧ y ∈ fld P) →
      Desc (minP P) (ι x ∪ ι y) (fun m => m = x) ∨ Desc (minP P) (ι x ∪ ι y) (fun m => m = y) := by
  rintro ⟨⟨hJ, hc⟩, hx, hy⟩
  by_cases e : x = y
  · left
    have hmin : ∀ z, minP P z (ι x ∪ ι y) ↔ z = x := by
      intro z
      rw [minP_iff]
      constructor
      · rintro ⟨⟨hz | hz, -⟩, -⟩
        · exact hz
        · exact (show z = y from hz).trans e.symm
      · intro ez
        rw [ez]
        refine ⟨⟨Or.inl rfl, hx⟩, ?_⟩
        rintro w (hw | hw) hwx
        · rw [show w = x from hw] at hwx
          exact pm200_36 hJ x x hwx rfl
        · rw [show w = y from hw, ← e] at hwx
          exact pm200_36 hJ x x hwx rfl
    exact (desc_iff_of hmin _).2 rfl
  · rcases cxne hc hx hy e with h | h
    · exact Or.inl (pm205_182 ⟨hJ, h⟩)
    · right
      have := pm205_182 ⟨hJ, h⟩
      rw [Set.union_comm] at this
      exact this

/-- ✱205·19. \(\vdash : P \in \text{trans} . \supset . \overrightarrow{\text{min}}_{P}ʻ\alpha = \overrightarrow{\text{min}}_{P}ʻ(\alpha \cup \breve{P} ʻʻ\alpha ) = \overrightarrow{\text{min}}_{P}ʻ\breve{P} _{*}ʻʻ\alpha\) -/
theorem pm205_19 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → refs (minP P) A = refs (minP P) (A ∪ P˘ ʻʻ A) ∧
      refs (minP P) (A ∪ P˘ ʻʻ A) = refs (minP P) (ancCnv P ʻʻ A) := by
  intro ht
  refine ⟨(minP_union ht subset_rfl).symm, minP_congr ?_⟩
  have e : ancCnv P ʻʻ A = anc P˘ ʻʻ A := by
    ext x
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, ancCnv_iff.1 h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, ancCnv_iff.2 h⟩⟩
  rw [e, pm201_52 (pm201_11.1 ht), fld_cnv]
  ext x
  constructor
  · rintro ⟨hx | hx, hf⟩
    · exact ⟨Or.inr ⟨hx, hf⟩, hf⟩
    · exact ⟨Or.inl hx, hf⟩
  · rintro ⟨hx | ⟨hx, -⟩, hf⟩
    · exact ⟨Or.inr hx, hf⟩
    · exact ⟨Or.inl hx, hf⟩

/-- ✱205·191. \(\vdash : P \in \text{trans} . \supset . \overrightarrow{\text{max}}_{P}ʻ\alpha = \overrightarrow{\text{max}}_{P}ʻ(\alpha \cup Pʻʻ\alpha) = \overrightarrow{\text{max}}_{P}ʻP_{*}ʻʻ\alpha\) -/
theorem pm205_191 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR → refs (maxP P) A = refs (maxP P) (A ∪ P ʻʻ A) ∧
      refs (maxP P) (A ∪ P ʻʻ A) = refs (maxP P) (anc P ʻʻ A) := by
  intro ht
  refine ⟨(minP_union (P := P˘) (pm201_11.1 ht) (fun x hx => hx)).symm, maxP_congr ?_⟩
  rw [pm201_52 ht]
  ext x
  constructor
  · rintro ⟨hx | hx, hf⟩
    · exact ⟨Or.inr ⟨hx, hf⟩, hf⟩
    · exact ⟨Or.inl hx, hf⟩
  · rintro ⟨hx | ⟨hx, -⟩, hf⟩
    · exact ⟨Or.inr hx, hf⟩
    · exact ⟨Or.inl hx, hf⟩

/-- ✱205·192. \(\vdash : P \in \text{trans} . \beta \subset \breve{P} ʻʻ\alpha . \supset . \overrightarrow{\text{min}}_{P}ʻ(\alpha \cup \beta ) = \overrightarrow{\text{min}}_{P}ʻ\alpha\) -/
theorem pm205_192 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    P ∈ transR ∧ B ⊆ P˘ ʻʻ A → refs (minP P) (A ∪ B) = refs (minP P) A :=
  fun ⟨ht, hB⟩ => minP_union ht hB

/-- ✱205·193. \(\vdash : P \in \text{trans} . \beta \subset Pʻʻ\alpha . \supset . \overrightarrow{\text{max}}_{P}ʻ(\alpha \cup \beta ) = \overrightarrow{\text{max}}_{P}ʻ\alpha\) -/
theorem pm205_193 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    P ∈ transR ∧ B ⊆ P ʻʻ A → refs (maxP P) (A ∪ B) = refs (maxP P) A :=
  fun ⟨ht, hB⟩ => minP_union (P := P˘) (pm201_11.1 ht) hB

/-- ✱205·194. \(\vdash : x \text{min}_{P} \alpha . \supset . {\sim} (xPx)\) -/
theorem pm205_194 {α : Type u} {P : α → α → Prop} {x : α} {A : Set α} :
    minP P x A → ¬P x x := by
  intro h hxx
  rw [minP_iff] at h
  exact h.2 x h.1.1 hxx

/-- ✱205·195. \(\vdash : x\, \text{max}_{P}\, \alpha . \supset . {\sim} (xPx)\) -/
theorem pm205_195 {α : Type u} {P : α → α → Prop} {x : α} {A : Set α} :
    maxP P x A → ¬P x x := by
  intro h hxx
  rw [maxP_iff] at h
  exact h.2 x h.1.1 hxx

/-- ✱205·196. \(\vdash \colon\ldotp P\in \text{Rl}ʻJ\cap \text{trans}.\supset :x\in CʻP.\equiv .x=\text{min}_{P}ʻ({℩}ʻx\cup \overleftarrow{P}ʻx)\) -/
theorem pm205_196 {α : Type u} {P : α → α → Prop} {x : α} :
    P ∈ rl J ∩ transR → (x ∈ fld P ↔ Desc (minP P) (ι x ∪ rels P x) (fun m => x = m)) := by
  rintro ⟨hJ, ht⟩
  have irr := mem_rl_J.1 hJ
  have tr := mem_transR.1 ht
  constructor
  · intro hx
    have hmin : ∀ z, minP P z (ι x ∪ rels P x) ↔ z = x := by
      intro z
      rw [minP_iff]
      constructor
      · rintro ⟨⟨hz | hz, -⟩, hn⟩
        · exact hz
        · exact (hn x (Or.inl rfl) hz).elim
      · intro e
        rw [e]
        refine ⟨⟨Or.inl rfl, hx⟩, ?_⟩
        rintro w (hw | hw) hwx
        · rw [show w = x from hw] at hwx
          exact irr x hwx
        · exact irr x (tr x w x ⟨hw, hwx⟩)
    exact (desc_iff_of hmin _).2 rfl
  · rintro ⟨m, hm, rfl⟩
    exact (minP_iff.1 ((hm x).2 rfl)).1.2

/-- ✱205·197. \(\vdash \colon\ldotp P\in \text{Rl}ʻJ\cap \text{trans}.\supset :x\in CʻP.\equiv .x=\text{max}_{P}ʻ(\overrightarrow{P}ʻx\cup {℩}ʻx)\) -/
theorem pm205_197 {α : Type u} {P : α → α → Prop} {x : α} :
    P ∈ rl J ∩ transR → (x ∈ fld P ↔ Desc (maxP P) (refs P x ∪ ι x) (fun m => x = m)) := by
  intro h
  have h' : P˘ ∈ rl J ∩ transR := ⟨pm200_11.1 h.1, pm201_11.1 h.2⟩
  have := pm205_196 (x := x) h'
  rw [fld_cnv, Set.union_comm] at this
  exact this

/-- ✱205·2. \(\vdash \colon\ldotp P\in \text{connex} .\text{E}!\text{min}_{P}ʻ\alpha .y\in \alpha \cap CʻP.\supset :\text{min}_{P}ʻ\alpha =y.\lor.\text{min}_{P}ʻ\alpha Py\) -/
theorem pm205_2 {α : Type u} {P : α → α → Prop} {A : Set α} {y : α} :
    (P ∈ connex ∧ EDesc (minP P) A) ∧ y ∈ A ∩ fld P →
      Desc (minP P) A (fun m => m = y) ∨ Desc (minP P) A (fun m => P m y) := by
  rintro ⟨⟨hc, m, hm⟩, hyA, hy⟩
  rw [desc_iff_of hm, desc_iff_of hm]
  obtain ⟨⟨-, hmf⟩, hmn⟩ := minP_iff.1 ((hm m).2 rfl)
  by_cases e : m = y
  · exact Or.inl e
  · rcases cxne hc hmf hy e with h | h
    · exact Or.inr h
    · exact (hmn y hyA h).elim

/-- ✱205·211. \(\vdash :P\in \text{trans}\cap \text{connex} .\text{E}!\text{min}_{P}ʻ\alpha .y\in \breve{P} ʻʻ\alpha .\supset .\text{min}_{P}ʻ\alpha Py\) -/
theorem pm205_211 {α : Type u} {P : α → α → Prop} {A : Set α} {y : α} :
    (P ∈ transR ∩ connex ∧ EDesc (minP P) A) ∧ y ∈ P˘ ʻʻ A → Desc (minP P) A (fun m => P m y) := by
  rintro ⟨⟨⟨ht, hc⟩, m, hm⟩, a, ha, hay⟩
  rw [desc_iff_of hm]
  obtain ⟨⟨-, hmf⟩, hmn⟩ := minP_iff.1 ((hm m).2 rfl)
  have haf : a ∈ fld P := ⟨y, Or.inl hay⟩
  by_cases e : m = a
  · rw [e]
    exact hay
  · rcases cxne hc hmf haf e with h | h
    · exact mem_transR.1 ht m a y ⟨h, hay⟩
    · exact (hmn a ha h).elim

/-- ✱205·22. \[\begin{align}&\vdash :P\in \text{trans}\cap \text{connex} .\text{E}!\text{min}_{P}ʻ\alpha .\supset .\breve{P} ʻʻ\alpha =\overleftarrow{P}ʻ\text{min}_{P}ʻ\alpha \\ &[*205·211.*37·181]\end{align}\] -/
theorem pm205_22 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR ∩ connex ∧ EDesc (minP P) A → Desc (minP P) A (fun m => P˘ ʻʻ A = rels P m) := by
  rintro ⟨hP, m, hm⟩
  rw [desc_iff_of hm]
  apply Set.Subset.antisymm
  · intro y hy
    exact (desc_iff_of hm _).1 (pm205_211 ⟨⟨hP, m, hm⟩, hy⟩)
  · intro y hy
    exact ⟨m, (minP_iff.1 ((hm m).2 rfl)).1.1, hy⟩

/-- ✱205·23. \(\vdash :P\in \text{connex} .x\in \text{D}ʻP.y\in \overrightarrow{B}ʻ\breve{P} .\supset .xPy\) -/
theorem pm205_23 {α : Type u} {P : α → α → Prop} {x y : α} :
    (P ∈ connex ∧ x ∈ dom P) ∧ y ∈ refs Beg P˘ → P x y := by
  rintro ⟨⟨hc, z, hxz⟩, ⟨w, hwy⟩, hy⟩
  have hne : x ≠ y := fun e => hy ⟨z, by rw [← e]; exact hxz⟩
  rcases cxne hc ⟨z, Or.inl hxz⟩ ⟨w, Or.inr hwy⟩ hne with h | h
  · exact h
  · exact (hy ⟨x, h⟩).elim

/-- ✱205·24. \(\vdash :P\in \text{connex} .\supset .\overrightarrow{B}ʻ\breve{P} \subset pʻ\overleftarrow{P}ʻʻ\text{D}ʻP \quad[*205·23]\) -/
theorem pm205_24 {α : Type u} {P : α → α → Prop} :
    P ∈ connex → refs Beg P˘ ⊆ prodCls (Rbwd P ʻʻ dom P) := by
  intro hc y hy
  rw [mem_prodCls_Rbwd]
  intro x hx
  exact pm205_23 ⟨⟨hc, hx⟩, hy⟩

/-- ✱205·241. \(\vdash :P\in \text{connex} .\supset .\overrightarrow{B}ʻP\subset pʻ\overrightarrow{P}ʻʻ\text{ᗡ}ʻP \quad[\text{Proof as in *205·24}]\) -/
theorem pm205_241 {α : Type u} {P : α → α → Prop} :
    P ∈ connex → refs Beg P ⊆ prodCls (Rfwd P ʻʻ codom P) := by
  intro hc x hx
  rw [mem_prodCls_Rfwd]
  intro y hy
  exact pm205_23 (P := P˘) ⟨⟨pm202_11.1 hc, hy⟩, hx⟩

/-- ✱205·25. \(\vdash .\overrightarrow{\text{min}}_{P}ʻ\overleftarrow{P}ʻx=(\overleftarrow{P\dot{-} P^{2}})ʻx\) -/
theorem pm205_25 {α : Type u} {P : α → α → Prop} {x : α} :
    refs (minP P) (rels P x) = rels (P ∸ rsq P) x := by
  ext y
  show minP P y (rels P x) ↔ P x y ∧ ¬rsq P x y
  rw [minP_iff]
  constructor
  · rintro ⟨⟨hxy, -⟩, hn⟩
    exact ⟨hxy, fun ⟨z, hxz, hzy⟩ => hn z hxz hzy⟩
  · rintro ⟨hxy, hn⟩
    exact ⟨⟨hxy, ⟨x, Or.inr hxy⟩⟩, fun z hxz hzy => hn ⟨z, hxz, hzy⟩⟩

/-- ✱205·251. \(\vdash :\exists !\overrightarrow{\text{min}}_{P}ʻ\overleftarrow{P}ʻx.\equiv .x\in \text{D}ʻ(P\dot{-} P^{2}) \quad[*205·25]\) -/
theorem pm205_251 {α : Type u} {P : α → α → Prop} {x : α} :
    (refs (minP P) (rels P x)).Nonempty ↔ x ∈ dom (P ∸ rsq P) := by
  rw [pm205_25]
  rfl

/-- ✱205·252. \(\vdash :\exists !\overrightarrow{\text{max}}_{P}ʻ\overrightarrow{P}ʻx.\equiv .x\in \text{ᗡ}ʻ(P\dot{-} P^{2})\) -/
theorem pm205_252 {α : Type u} {P : α → α → Prop} {x : α} :
    (refs (maxP P) (refs P x)).Nonempty ↔ x ∈ codom (P ∸ rsq P) := by
  have e : refs (maxP P) (refs P x) = refs (P ∸ rsq P) x := by
    ext y
    show maxP P y (refs P x) ↔ P y x ∧ ¬rsq P y x
    rw [maxP_iff]
    constructor
    · rintro ⟨⟨hyx, -⟩, hn⟩
      exact ⟨hyx, fun ⟨z, hyz, hzx⟩ => hn z hzx hyz⟩
    · rintro ⟨hyx, hn⟩
      exact ⟨⟨hyx, ⟨x, Or.inl hyx⟩⟩, fun z hzx hyz => hn ⟨z, hyz, hzx⟩⟩
  rw [e]
  rfl

/-- ✱205·253. \(\vdash :P\in \text{connex} .\text{E}!BʻP.\supset .\text{ᗡ}ʻP=\overleftarrow{P}ʻBʻP \quad[*202·524]\) -/
theorem pm205_253 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ∧ EDesc Beg P → Desc Beg P (fun b => codom P = rels P b) := by
  rintro ⟨hc, b, hb⟩
  exact pm202_524 ⟨hc, b, (hb b).2 rfl⟩

/-- ✱205·254. \(\vdash :P\in \text{connex} .\text{E}!BʻP.\supset .\overleftarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻP=\overleftarrow{P\dot{-} P^{2}}ʻBʻP \quad[*205·253·25]\)

**Status.** proved (reading): transcription error. The e-text prints `min⃖_P'ᗡ'P`
(`\overleftarrow`); `min⃖_P'` would take a term, not the class `ᗡ'P`. The demonstration
(✱205·253·25: `ᗡ'P = P⃖'B'P` and `min⃗_P'P⃖'x = (P −̇ P²)⃖'x`) gives `min⃗_P'ᗡ'P`, which is
stated. -/
theorem pm205_254 {α : Type u} {P : α → α → Prop} :
    P ∈ connex ∧ EDesc Beg P →
      Desc Beg P (fun b => refs (minP P) (codom P) = rels (P ∸ rsq P) b) := by
  intro h
  obtain ⟨b, hb⟩ := h.2
  have := pm205_253 h
  rw [desc_iff_of hb] at this ⊢
  rw [this]
  exact pm205_25

/-- ✱205·255. \(\vdash :\exists !\overrightarrow{\text{min}}_{P}ʻ\text{ᗡ}ʻP.\supset .\exists !\overrightarrow{B}ʻP\) -/
theorem pm205_255 {α : Type u} {P : α → α → Prop} :
    (refs (minP P) (codom P)).Nonempty → (refs Beg P).Nonempty := by
  rintro ⟨m, hm⟩
  obtain ⟨⟨⟨z, hzm⟩, -⟩, hn⟩ := minP_iff.1 hm
  refine ⟨z, ⟨m, hzm⟩, fun hz => ?_⟩
  exact hn z hz hzm

/-- ✱205·256. \[\begin{align}\vdash \colon\ldotp P\in \text{Ser}.&\supset :\\ &\text{E}!\text{min}_{P}ʻ\text{ᗡ}ʻP.\equiv .\text{E}!\breve{P} _{1}ʻBʻP.\equiv .\text{min}_{P}ʻ\text{ᗡ}ʻP=\breve{P} _{1}ʻBʻP\\ &[*205·254·255.*201·63.*202·52·7]\end{align}\] -/
theorem pm205_256 {α : Type u} {P : α → α → Prop} :
    P ∈ Ser → ((EDesc (minP P) (codom P) ↔ EBang (fun x => Desc Beg P (fun b => (P1 P)˘ x b))) ∧
      (EBang (fun x => Desc Beg P (fun b => (P1 P)˘ x b)) ↔
        Desc (minP P) (codom P) (fun m => Desc2 (P1 P)˘ Beg P (fun c => m = c)))) := by
  intro hS
  have hP1 : ∀ a b, P1 P a b ↔ P a b ∧ ¬∃ z, P a z ∧ P z b :=
    fun a b => P1_iff_of_transR hS.1.2 hS.1.1
  have irr := mem_rl_J.1 hS.1.1
  -- if `B'P = b`, the minimum of `ᗡ'P` is the immediate successor of `b`
  have key : ∀ b, Beg b P → ∀ m, minP P m (codom P) ↔ P1 P b m := by
    intro b hb m
    have hcod : codom P = rels P b := by
      obtain ⟨b', hb', hc'⟩ := pm202_524 ⟨hS.2, b, hb⟩
      have e : b = b' := (hb' b).1 hb
      rw [e]
      exact hc'
    rw [minP_iff, hP1, hcod]
    constructor
    · rintro ⟨⟨hbm, -⟩, hn⟩
      exact ⟨hbm, fun ⟨z, hbz, hzm⟩ => hn z hbz hzm⟩
    · rintro ⟨hbm, hn⟩
      exact ⟨⟨hbm, ⟨b, Or.inr hbm⟩⟩, fun z hbz hzm => hn ⟨z, hbz, hzm⟩⟩
  have uniqB : ∀ b c, Beg b P → Beg c P → b = c :=
    fun b c hb hc => mem_zero_union_one.1 (pm202_52 hS.2).1 b c hb hc
  have uniq1 : ∀ b m m', P1 P b m → P1 P b m' → m = m' :=
    fun b m m' h h' => (mem_arrow_one_one.1 (pm204_7 hS)).2 b m m' ⟨h, h'⟩
  -- E!min_P'ᗡ'P
  have a1 : EDesc (minP P) (codom P) → ∃ b m, Beg b P ∧ P1 P b m := by
    rintro ⟨m, hm⟩
    obtain ⟨b, hb⟩ := pm205_255 ⟨m, (hm m).2 rfl⟩
    exact ⟨b, m, hb, (key b hb m).1 ((hm m).2 rfl)⟩
  have a2 : (∃ b m, Beg b P ∧ P1 P b m) →
      ∃ b m, (∀ x, Beg x P ↔ x = b) ∧ (∀ x, minP P x (codom P) ↔ x = m) ∧
        ∀ x, P1 P b x ↔ x = m := by
    rintro ⟨b, m, hb, hbm⟩
    refine ⟨b, m, fun x => ⟨fun hx => uniqB x b hx hb, fun e => by rw [e]; exact hb⟩,
      fun x => ⟨fun hx => uniq1 b x m ((key b hb x).1 hx) hbm, fun e => by
        rw [e]; exact (key b hb m).2 hbm⟩,
      fun x => ⟨fun hx => uniq1 b x m hx hbm, fun e => by rw [e]; exact hbm⟩⟩
  have a3 : EBang (fun x => Desc Beg P (fun b => (P1 P)˘ x b)) → ∃ b m, Beg b P ∧ P1 P b m := by
    rintro ⟨m, hm⟩
    obtain ⟨b, hb, h⟩ := (hm m).2 rfl
    exact ⟨b, m, (hb b).2 rfl, h⟩
  have b1 : (∃ b m, Beg b P ∧ P1 P b m) → EDesc (minP P) (codom P) := by
    intro h
    obtain ⟨b, m, -, hm, -⟩ := a2 h
    exact ⟨m, hm⟩
  have b2 : (∃ b m, Beg b P ∧ P1 P b m) →
      EBang (fun x => Desc Beg P (fun b => (P1 P)˘ x b)) := by
    intro h
    obtain ⟨b, m, hb, -, h1⟩ := a2 h
    refine ⟨m, fun x => ?_⟩
    show Desc Beg P (fun b => P1 P b x) ↔ x = m
    rw [desc_iff_of hb]
    exact h1 x
  have b3 : (∃ b m, Beg b P ∧ P1 P b m) →
      Desc (minP P) (codom P) (fun m => Desc2 (P1 P)˘ Beg P (fun c => m = c)) := by
    intro h
    obtain ⟨b, m, hb, hm, h1⟩ := a2 h
    rw [desc_iff_of hm, desc2_iff, desc_iff_of hb]
    exact (desc_iff_of (R := (P1 P)˘) (y := b) h1 _).2 rfl
  have a4 : Desc (minP P) (codom P) (fun m => Desc2 (P1 P)˘ Beg P (fun c => m = c)) →
      EDesc (minP P) (codom P) := fun ⟨m, hm, _⟩ => ⟨m, hm⟩
  exact ⟨⟨fun h => b2 (a1 h), fun h => b1 (a3 h)⟩, ⟨fun h => b3 (a3 h), fun h => b2 (a1 (a4 h))⟩⟩

/-- ✱205·26. \(\vdash :Q\,\unicode{x2abd}\, P.\supset .\text{min}_{P}\upharpoonright \text{Cl}ʻCʻQ\,\unicode{x2abd}\, \text{min}_{Q}\) -/
theorem pm205_26 {α : Type u} {P Q : α → α → Prop} :
    Q ⪽ P → minP P ↾ cl (fld Q) ⪽ minP Q := by
  rintro hQP x A ⟨hx, hA⟩
  rw [minP_iff] at hx ⊢
  exact ⟨⟨hx.1.1, hA hx.1.1⟩, fun y hy hyx => hx.2 y hy (hQP y x hyx)⟩

/-- ✱205·261. \(\vdash :P\unicode{x0294f}\beta \in \text{connex} .\beta \cap CʻP{\sim}\in 1.\supset .\overrightarrow{\text{min}}(P\unicode{x0294f}\beta )ʻ\alpha =\overrightarrow{\text{min}}_{P}ʻ(\alpha \cap \beta )\)

**Status.** proved (corrected): false as printed, for the reason of ✱202·54 (on which the
demonstration rests): with `P` relating `0` to `1` and `1` to `2` and `β = α = {0, 2}`,
`P⥏β = Λ̇` is connected and `β ∩ C'P` has two members, but `min⃗(P⥏β)'α = Λ` while
`min⃗_P'(α ∩ β)` contains `0` (`pm205_261_printed_false`). As in ✱202·54, the hypothesis
`P⥏β ∈ connex` is corrected to `P ∈ connex`. -/
theorem pm205_261 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    P ∈ connex ∧ B ∩ fld P ∉ (one : Set (Set α)) →
      refs (minP (P ⥏ B)) A = refs (minP P) (A ∩ B) :=
  fun h => minP_fres (pm202_54 h)

/-- The printed form of ✱205·261 (hypothesis `P⥏β ∈ connex`) is false. -/
theorem pm205_261_printed_false :
    ¬ ∀ (P : ℕ → ℕ → Prop) (A B : Set ℕ), P ⥏ B ∈ connex ∧ B ∩ fld P ∉ (one : Set (Set ℕ)) →
      refs (minP (P ⥏ B)) A = refs (minP P) (A ∩ B) := by
  intro h
  obtain ⟨hc, h1, h0, hf⟩ := cex54
  have e := h cexP cexA cexA ⟨hc, h1⟩
  have hm : (0 : ℕ) ∈ refs (minP cexP) (cexA ∩ cexA) := by
    refine minP_iff.2 ⟨⟨⟨h0.1, h0.1⟩, h0.2⟩, fun y _ hy => ?_⟩
    simp only [cexP] at hy
    omega
  rw [← e] at hm
  exact hf 0 (minP_iff.1 hm).1.2

/-- ✱205·262. \[\begin{align}\vdash :P\in \text{trans}\cap \text{connex} .x\in \alpha \cap CʻP.\beta &=\overrightarrow{P}ʻx\cup {℩}ʻx.\supset .\\ &\overrightarrow{\text{min}}_{P}ʻ\alpha =\overrightarrow{\text{min}}_{P}ʻ(\alpha \cap \beta )\end{align}\] -/
theorem pm205_262 {α : Type u} {P : α → α → Prop} {A B : Set α} {x : α} :
    (P ∈ transR ∩ connex ∧ x ∈ A ∩ fld P) ∧ B = refs P x ∪ ι x →
      refs (minP P) A = refs (minP P) (A ∩ B) := by
  rintro ⟨⟨⟨ht, hc⟩, hxA, hx⟩, rfl⟩
  ext m
  show minP P m A ↔ minP P m (A ∩ (refs P x ∪ ι x))
  rw [minP_iff, minP_iff]
  constructor
  · rintro ⟨⟨hmA, hm⟩, hn⟩
    refine ⟨⟨⟨hmA, ?_⟩, hm⟩, fun y hy => hn y hy.1⟩
    by_cases e : m = x
    · exact Or.inr e
    · rcases cxne hc hm hx e with h | h
      · exact Or.inl h
      · exact (hn x hxA h).elim
  · rintro ⟨⟨⟨hmA, hmB⟩, hm⟩, hn⟩
    refine ⟨⟨hmA, hm⟩, fun y hyA hym => ?_⟩
    have hyx : P y x := by
      rcases hmB with h | h
      · exact mem_transR.1 ht y m x ⟨hym, h⟩
      · rw [show m = x from h] at hym
        exact hym
    exact hn y ⟨hyA, Or.inl hyx⟩ hym

/-- ✱205·27. \[\begin{align}\vdash :P\in \text{trans}\cap \text{connex} .x\in &\alpha \cap \text{ᗡ}ʻP.\beta =\overrightarrow{P}ʻx\cup \iota ʻx.\supset .\\ &\overrightarrow{\text{min}}_{P}ʻ\alpha =\overrightarrow{\text{min}}(P\unicode{x0294f}\beta )ʻ\alpha =\overrightarrow{\text{min}}_{P}ʻ(\alpha \cap \beta )\end{align}\] -/
theorem pm205_27 {α : Type u} {P : α → α → Prop} {A B : Set α} {x : α} :
    (P ∈ transR ∩ connex ∧ x ∈ A ∩ codom P) ∧ B = refs P x ∪ ι x →
      refs (minP P) A = refs (minP (P ⥏ B)) A ∧
        refs (minP (P ⥏ B)) A = refs (minP P) (A ∩ B) := by
  rintro ⟨⟨hP, hxA, w, hwx⟩, hB⟩
  have hx : x ∈ fld P := ⟨w, Or.inr hwx⟩
  have e1 := pm205_262 ⟨⟨hP, hxA, hx⟩, hB⟩
  have hf : fld (P ⥏ B) = B ∩ fld P := by
    apply Set.Subset.antisymm fld_fres_sub
    rintro y ⟨hyB, hy⟩
    have hxB : x ∈ B := by rw [hB]; exact Or.inr rfl
    have hwB : w ∈ B := by rw [hB]; exact Or.inl hwx
    rw [hB] at hyB
    rcases hyB with h | h
    · exact ⟨x, Or.inl ⟨⟨by rw [hB]; exact Or.inl h, h⟩, hxB⟩⟩
    · rw [show y = x from h]
      exact ⟨w, Or.inr ⟨⟨hwB, hwx⟩, hxB⟩⟩
  have e2 := minP_fres (A := A) hf
  exact ⟨e1.trans e2.symm, e2⟩

/-- ✱205·3. \(\vdash :P\in \text{connex} .\supset .\overrightarrow{\text{min}}_{P}ʻ\alpha \in 0\cup 1.\overrightarrow{\text{max}}_{P}ʻ\alpha \in 0\cup 1\) -/
theorem pm205_3 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex → refs (minP P) A ∈ (zero ∪ one : Set (Set α)) ∧
      refs (maxP P) A ∈ (zero ∪ one : Set (Set α)) :=
  fun hc => ⟨mem_zero_union_one.2 fun _ _ hx hy => min_unique hc hx hy,
    mem_zero_union_one.2 fun _ _ hx hy => max_unique hc hx hy⟩

/-- ✱205·31. \(\vdash : P \in \text{connex} . \supset . \text{min}_{P}, \text{max}_{P} \in 1 \rightarrow \text{Cls} \quad[*205·3.*71·12]\) -/
theorem pm205_31 {α : Type u} {P : α → α → Prop} :
    P ∈ connex → minP P ∈ arrow one Cls ∧ maxP P ∈ arrow one Cls :=
  fun hc => ⟨mem_arrow_one_Cls.2 fun _ _ _ h => min_unique hc h.1 h.2,
    mem_arrow_one_Cls.2 fun _ _ _ h => max_unique hc h.1 h.2⟩

/-- ✱205·32. \[\begin{align}&\vdash \colon\ldotp P \in \text{connex} . \supset : \exists ! \overrightarrow{\text{min}}_{P}ʻ\alpha . \equiv . \text{E}! \text{min}_{P}ʻ\alpha . \equiv . \alpha \in \text{ᗡ}ʻ\text{min}_{P}\\ &[*205·31 . *71·163 . *33·41]\end{align}\] -/
theorem pm205_32 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex → (((refs (minP P) A).Nonempty ↔ EDesc (minP P) A) ∧
      (EDesc (minP P) A ↔ A ∈ codom (minP P))) := by
  intro hc
  have h1 : (refs (minP P) A).Nonempty → EDesc (minP P) A := by
    rintro ⟨m, hm⟩
    exact ⟨m, fun z => ⟨fun hz => min_unique hc hz hm, fun e => by rw [e]; exact hm⟩⟩
  have h2 : EDesc (minP P) A → A ∈ codom (minP P) := fun ⟨m, hm⟩ => ⟨m, (hm m).2 rfl⟩
  have h3 : A ∈ codom (minP P) → (refs (minP P) A).Nonempty := fun ⟨m, hm⟩ => ⟨m, hm⟩
  exact ⟨⟨h1, fun h => h3 (h2 h)⟩, ⟨h2, fun h => h1 (h3 h)⟩⟩

/-- ✱205·33. \(\vdash : P \in \text{connex} . \kappa \subset \text{ᗡ}ʻ\text{min}_{P} . \supset . \text{min}_{P} \upharpoonright \kappa \in {\in}_{\Delta}ʻ\kappa\) -/
theorem pm205_33 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} :
    P ∈ connex ∧ K ⊆ codom (minP P) → minP P ↾ K ∈ sel memRel K := by
  rintro ⟨hc, hK⟩
  refine mem_sel_iff.2 ⟨⟨mem_arrow_one_Cls.2 fun x y A h => min_unique hc h.1.1 h.2.1,
    fun x A h => (minP_iff.1 h.1).1.1⟩, ?_⟩
  ext A
  constructor
  · rintro ⟨x, -, hA⟩
    exact hA
  · intro hA
    obtain ⟨x, hx⟩ := hK hA
    exact ⟨x, hx, hA⟩

/-- ✱205·34. \(\vdash : P \in \text{connex} . \kappa \subset \text{ᗡ}ʻ\text{min}_{P} . \supset . \kappa \in \text{Cls}^{2}\, \text{mult} \quad[*205·33 . *88·2]\) -/
theorem pm205_34 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} :
    P ∈ connex ∧ K ⊆ codom (minP P) → K ∈ Cls2Mult :=
  fun h => ⟨_, pm205_33 h⟩

/-- ✱205·35. \[\begin{align}\vdash \colon\colon P^{2} \,\unicode{x2abd}\, J . &P \in \text{connex} . \supset \colon\ldotp \\ &x = \text{min}_{P}ʻ\alpha . \equiv : x \in \alpha \cap CʻP : y \in \alpha \cap CʻP - \iota ʻx . \supset _{y} . xPy\end{align}\] -/
theorem pm205_35 {α : Type u} {P : α → α → Prop} {A : Set α} {x : α} :
    rsq P ⪽ J ∧ P ∈ connex →
      (Desc (minP P) A (fun m => x = m) ↔
        x ∈ A ∩ fld P ∧ ∀ y, y ∈ (A ∩ fld P) \ ι x → P x y) := by
  rintro ⟨hJ, hc⟩
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨⟨hxA, hx⟩, hn⟩ := minP_iff.1 ((hm x).2 rfl)
    refine ⟨⟨hxA, hx⟩, fun y ⟨⟨hyA, hy⟩, hne⟩ => ?_⟩
    rcases cxne hc hx hy (fun e => hne (show y = x from e.symm)) with h | h
    · exact h
    · exact (hn y hyA h).elim
  · rintro ⟨⟨hxA, hx⟩, h⟩
    have hm : minP P x A := by
      refine minP_iff.2 ⟨⟨hxA, hx⟩, fun y hyA hyx => ?_⟩
      by_cases e : y = x
      · rw [e] at hyx
        exact pm200_36 hJ x x hyx rfl
      · exact hJ y y ⟨x, hyx, h y ⟨⟨hyA, ⟨x, Or.inl hyx⟩⟩, e⟩⟩ rfl
    exact (min_desc hc hm _).2 rfl

/-- ✱205·36. \(\vdash : P \in \text{trans} \cap \text{connex} . \supset . \overrightarrow{\text{min}}_{P}ʻ\alpha \subset pʻP_{*}ʻʻ(\alpha \cap CʻP)\)

**Status.** proved (reading): transcription error. The e-text prints `p'P_*''(α ∩ C'P)`
without the arrow, which is not significant (`P_*''(α ∩ C'P)` is a class of terms, `p'`
requires a class of classes); the demonstration ("`y ∈ α ∩ C'P . ⊃_y . xP_*y`") gives
`p'P⃗_*''(α ∩ C'P)`, which is stated. -/
theorem pm205_36 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR ∩ connex → refs (minP P) A ⊆ prodCls (Rfwd (anc P) ʻʻ (A ∩ fld P)) := by
  rintro ⟨-, hc⟩ x hx
  obtain ⟨⟨-, hxf⟩, hn⟩ := minP_iff.1 hx
  rw [mem_prodCls_Rfwd]
  rintro y ⟨hyA, hy⟩
  by_cases e : x = y
  · rw [← e]
    exact anc_refl hxf
  · rcases cxne hc hxf hy e with h | h
    · exact anc_of_po (po_of h)
    · exact (hn y hyA h).elim

/-- ✱205·37. \(\vdash : P \in \text{trans} . \overrightarrow{\text{max}}_{P}ʻ\alpha = \Lambda . \supset . P_{*}ʻʻ\alpha = Pʻʻ\alpha \quad[*201·52.*205·123]\) -/
theorem pm205_37 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR ∧ refs (maxP P) A = Λ → anc P ʻʻ A = P ʻʻ A := by
  rintro ⟨ht, h⟩
  rw [pm201_52 ht]
  have h' := pm205_123.1 h
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · exact hx
    · exact h' hx
  · exact fun x hx => Or.inl hx

/-- ✱205·38. \(\vdash : P_{\text{po}} \,\unicode{x2abd}\, J . \supset . \mu \cap pʻ\overrightarrow{P}_{*}ʻʻ\mu \subset \overrightarrow{\text{min}} (P_{\text{po}})ʻ\mu \) -/
theorem pm205_38 {α : Type u} {P : α → α → Prop} {B : Set α} :
    po P ⪽ J → B ∩ prodCls (Rfwd (anc P) ʻʻ B) ⊆ refs (minP (po P)) B := by
  rintro hJ x ⟨hxB, hp⟩
  rw [mem_prodCls_Rfwd] at hp
  have hx : x ∈ fld P := (fld_of_anc (hp x hxB)).1
  refine minP_iff.2 ⟨⟨hxB, by rw [fld_po]; exact hx⟩, fun y hyB hyx => ?_⟩
  exact hJ x x (anc_po_trans (hp y hyB) hyx) rfl

/-- ✱205·381. \(\vdash :P_{\text{po}}\,\unicode{x2abd}\, J.\overrightarrow{\text{max}}_{P}ʻ\mu = \Lambda .\supset .pʻ\overleftarrow{P}_{*}ʻʻ\mu = pʻ\overleftarrow{P}_{\text{po}}ʻʻ\mu\) -/
theorem pm205_381 {α : Type u} {P : α → α → Prop} {B : Set α} :
    po P ⪽ J ∧ refs (maxP P) B = Λ → prodCls (Rbwd (anc P) ʻʻ B) = prodCls (Rbwd (po P) ʻʻ B) := by
  rintro ⟨hJ, h⟩
  have h' := pm205_123.1 h
  ext z
  rw [mem_prodCls_Rbwd, mem_prodCls_Rbwd]
  constructor
  · intro hz y hy
    rcases anc_iff_po.1 (hz y hy) with ⟨e, hyf⟩ | hp
    · rw [e] at hy hyf
      obtain ⟨w, hwB, hzw⟩ := h' ⟨hy, hyf⟩
      exact (hJ z z (po_anc_trans (po_of hzw) (hz w hwB)) rfl).elim
    · exact hp
  · intro hz y hy
    exact anc_of_po (hz y hy)

/-- ✱205·4. \(\vdash :CʻP\in 1.\supset .\overrightarrow{B}ʻP = \Lambda .\overrightarrow{B}ʻ\breve{P} = \Lambda\) -/
theorem pm205_4 {α : Type u} {P : α → α → Prop} :
    fld P ∈ (one : Set (Set α)) → refs Beg P = Λ ∧ refs Beg P˘ = Λ := by
  intro h
  obtain ⟨c, hc⟩ := mem_one_iff.1 h
  have hall : ∀ x y, P x y → x = c ∧ y = c :=
    fun x y hxy => ⟨(hc x).1 ⟨y, Or.inl hxy⟩, (hc y).1 ⟨x, Or.inr hxy⟩⟩
  constructor
  · rw [eqΛ]
    rintro x ⟨⟨y, hxy⟩, hn⟩
    obtain ⟨e1, e2⟩ := hall x y hxy
    have e : y = x := e2.trans e1.symm
    rw [e] at hxy
    exact hn ⟨x, hxy⟩
  · rw [eqΛ]
    rintro x ⟨⟨y, hyx⟩, hn⟩
    obtain ⟨e1, e2⟩ := hall y x hyx
    have e : y = x := e1.trans e2.symm
    rw [e] at hyx
    exact hn ⟨x, hyx⟩

/-- ✱205·401. \(\vdash :\exists !\overrightarrow{B}ʻP\unicode{x0294f}\alpha .\supset .\alpha \cap CʻP{\sim}\in 0\cup 1.CʻP\unicode{x0294f}\alpha {\sim}\in 0\cup 1\) -/
theorem pm205_401 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (refs Beg (P ⥏ A)).Nonempty →
      A ∩ fld P ∉ (zero ∪ one : Set (Set α)) ∧ fld (P ⥏ A) ∉ (zero ∪ one : Set (Set α)) := by
  rintro ⟨x, ⟨y, hxy⟩, hn⟩
  have hne : x ≠ y := fun e => hn ⟨x, by rw [← e] at hxy; exact hxy⟩
  obtain ⟨⟨hxA, h⟩, hyA⟩ := hxy
  constructor
  · intro h1
    exact hne (mem_zero_union_one.1 h1 x y ⟨hxA, ⟨y, Or.inl h⟩⟩ ⟨hyA, ⟨x, Or.inr h⟩⟩)
  · intro h1
    exact hne (mem_zero_union_one.1 h1 x y ⟨y, Or.inl ⟨⟨hxA, h⟩, hyA⟩⟩
      ⟨x, Or.inr ⟨⟨hxA, h⟩, hyA⟩⟩)

/-- ✱205·41. \(\vdash :P\in \text{connex} .\alpha \cap CʻP{\sim}\in 1.\supset .\overrightarrow{\text{min}}_{P}ʻ\alpha = \overrightarrow{B}ʻP\unicode{x0294f}\alpha\) -/
theorem pm205_41 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∩ fld P ∉ (one : Set (Set α)) → refs (minP P) A = refs Beg (P ⥏ A) := by
  rintro ⟨hc, h1⟩
  ext x
  show minP P x A ↔ x ∈ dom (P ⥏ A) ∧ x ∉ codom (P ⥏ A)
  rw [minP_iff]
  constructor
  · rintro ⟨⟨hxA, hx⟩, hn⟩
    refine ⟨?_, fun ⟨y, ⟨⟨hyA, hyx⟩, _⟩⟩ => hn y hyA hyx⟩
    have : ∃ y, y ∈ A ∩ fld P ∧ y ≠ x := by
      by_contra hk
      push_neg at hk
      exact h1 (mem_one_iff.2 ⟨x, fun z => ⟨fun hz => hk z hz,
        fun e => by rw [e]; exact ⟨hxA, hx⟩⟩⟩)
    obtain ⟨y, ⟨hyA, hy⟩, hne⟩ := this
    rcases cxne hc hx hy (Ne.symm hne) with h | h
    · exact ⟨y, ⟨⟨hxA, h⟩, hyA⟩⟩
    · exact (hn y hyA h).elim
  · rintro ⟨⟨y, ⟨⟨hxA, hxy⟩, hyA⟩⟩, hn⟩
    exact ⟨⟨hxA, ⟨y, Or.inl hxy⟩⟩, fun z hzA hzx => hn ⟨z, ⟨⟨hzA, hzx⟩, hxA⟩⟩⟩

/-- ✱205·42. \(\vdash :P\in \text{connex} .\text{E}!BʻP\unicode{x0294f}\alpha .\supset .BʻP\unicode{x0294f}\alpha = \text{min}_{P}ʻ\alpha\) -/
theorem pm205_42 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ EDesc Beg (P ⥏ A) → Desc Beg (P ⥏ A) (fun b => Desc (minP P) A (fun m => b = m)) := by
  rintro ⟨hc, b, hb⟩
  rw [desc_iff_of hb]
  obtain ⟨⟨y, ⟨⟨hbA, hby⟩, -⟩⟩, hn⟩ := (hb b).2 rfl
  have hm : minP P b A :=
    minP_iff.2 ⟨⟨hbA, ⟨y, Or.inl hby⟩⟩, fun z hzA hzb => hn ⟨z, ⟨⟨hzA, hzb⟩, hbA⟩⟩⟩
  exact (min_desc hc hm _).2 rfl

/-- ✱205·43. \(\vdash :P\in \text{connex} .\exists !\alpha \cap \text{D}ʻP.\supset .\overrightarrow{\text{min}}_{P}ʻ\alpha =\overrightarrow{B}ʻ\alpha \upharpoonleft P\) -/
theorem pm205_43 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ (A ∩ dom P).Nonempty → refs (minP P) A = refs Beg (A ◁ P) := by
  rintro ⟨hc, a, haA, b, hab⟩
  ext x
  show minP P x A ↔ x ∈ dom (A ◁ P) ∧ x ∉ codom (A ◁ P)
  rw [minP_iff]
  constructor
  · rintro ⟨⟨hxA, hx⟩, hn⟩
    refine ⟨?_, fun ⟨z, hzA, hzx⟩ => hn z hzA hzx⟩
    by_cases e : a = x
    · rw [← e]
      exact ⟨b, haA, hab⟩
    · rcases cxne hc ⟨b, Or.inl hab⟩ hx e with h | h
      · exact (hn a haA h).elim
      · exact ⟨a, hxA, h⟩
  · rintro ⟨⟨y, hxA, hxy⟩, hn⟩
    exact ⟨⟨hxA, ⟨y, Or.inl hxy⟩⟩, fun z hzA hzx => hn ⟨z, hzA, hzx⟩⟩

/-- ✱205·44. \(\vdash :P\in \text{connex} .\text{E}!Bʻ\alpha \upharpoonleft P.\supset .\text{min}_{P}ʻ\alpha =Bʻ\alpha \upharpoonleft P \quad[*205·43.*32·41]\) -/
theorem pm205_44 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ EDesc Beg (A ◁ P) → Desc (minP P) A (fun m => Desc Beg (A ◁ P) (fun b => m = b)) := by
  rintro ⟨hc, b, hb⟩
  obtain ⟨⟨y, hbA, hby⟩, hn⟩ := (hb b).2 rfl
  have hm : minP P b A :=
    minP_iff.2 ⟨⟨hbA, ⟨y, Or.inl hby⟩⟩, fun z hzA hzb => hn ⟨z, hzA, hzb⟩⟩
  rw [min_desc hc hm, desc_iff_of hb]

/-- ✱205·5. \(\vdash :P\in \text{connex} .\alpha \subset \beta .\text{min}_{P}ʻ\beta \in \alpha .\supset .\text{E}!\text{min}_{P}ʻ\alpha .\text{min}_{P}ʻ\alpha =\text{min}_{P}ʻ\beta\) -/
theorem pm205_5 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    (P ∈ connex ∧ A ⊆ B) ∧ Desc (minP P) B (fun m => m ∈ A) →
      EDesc (minP P) A ∧ Desc (minP P) A (fun m => Desc (minP P) B (fun n => m = n)) := by
  rintro ⟨⟨hc, hAB⟩, m, hm, hmA⟩
  obtain ⟨⟨-, hmf⟩, hn⟩ := minP_iff.1 ((hm m).2 rfl)
  have hmin : minP P m A := minP_iff.2 ⟨⟨hmA, hmf⟩, fun y hy => hn y (hAB hy)⟩
  exact ⟨⟨m, fun z => ⟨fun hz => min_unique hc hz hmin, fun e => by rw [e]; exact hmin⟩⟩,
    (min_desc hc hmin _).2 ((desc_iff_of hm _).2 rfl)⟩

/-- ✱205·501. \(\vdash :P\in \text{connex} .\text{min}_{P}ʻ\alpha =\text{min}_{P}ʻ\beta .\supset .\beta \subset -pʻ\overrightarrow{P}ʻʻ\alpha\) -/
theorem pm205_501 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    P ∈ connex ∧ Desc (minP P) A (fun m => Desc (minP P) B (fun n => m = n)) →
      B ⊆ (prodCls (Rfwd P ʻʻ A))ᶜ := by
  rintro ⟨-, m, hm, n, hn, e⟩ y hyB hy
  obtain ⟨⟨hmA, -⟩, -⟩ := minP_iff.1 ((hm m).2 rfl)
  obtain ⟨-, hnB⟩ := minP_iff.1 ((hn n).2 rfl)
  rw [← e] at hnB
  exact hnB y hyB (mem_prodCls_Rfwd.1 hy m hmA)

/-- ✱205·51. \[\begin{align}\vdash \colon\ldotp P\in \text{connex} .\alpha \subset \beta .\text{E}!&\text{min}_{P}ʻ\alpha .\text{E}!\text{min}_{P}ʻ\beta .\supset :\\ &\text{min}_{P}ʻ\alpha =\text{min}_{P}ʻ\beta .\lor.\text{min}_{P}ʻ\beta P\text{min}_{P}ʻ\alpha\end{align}\] -/
theorem pm205_51 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    ((P ∈ connex ∧ A ⊆ B) ∧ EDesc (minP P) A) ∧ EDesc (minP P) B →
      Desc (minP P) A (fun m => Desc (minP P) B (fun n => m = n)) ∨
        Desc (minP P) B (fun n => Desc (minP P) A (fun m => P n m)) := by
  rintro ⟨⟨⟨hc, hAB⟩, m, hm⟩, n, hn⟩
  rw [desc_iff_of hm, desc_iff_of hn, desc_iff_of hn, desc_iff_of hm]
  obtain ⟨⟨hmA, hmf⟩, -⟩ := minP_iff.1 ((hm m).2 rfl)
  obtain ⟨⟨-, hnf⟩, hnn⟩ := minP_iff.1 ((hn n).2 rfl)
  by_cases e : m = n
  · exact Or.inl e
  · rcases cxne hc hmf hnf e with h | h
    · exact (hnn m (hAB hmA) h).elim
    · exact Or.inr h

/-- ✱205·52. \[\begin{align}\vdash :P\in \text{trans} \cap \text{connex} .&\exists !\alpha \cap pʻ\overrightarrow{P}ʻʻ\beta .\\ &\text{E}!\text{min}_{P}ʻ\alpha .\text{E}!\text{min}_{P}ʻ\beta .\supset .\text{min}_{P}ʻ\alpha P\text{min}_{P}ʻ\beta\end{align}\] -/
theorem pm205_52 {α : Type u} {P : α → α → Prop} {A B : Set α} :
    ((P ∈ transR ∩ connex ∧ (A ∩ prodCls (Rfwd P ʻʻ B)).Nonempty) ∧ EDesc (minP P) A) ∧
      EDesc (minP P) B → Desc (minP P) A (fun m => Desc (minP P) B (fun n => P m n)) := by
  rintro ⟨⟨⟨⟨ht, hc⟩, z, hzA, hz⟩, m, hm⟩, n, hn⟩
  rw [desc_iff_of hm, desc_iff_of hn]
  obtain ⟨⟨-, hmf⟩, hmn⟩ := minP_iff.1 ((hm m).2 rfl)
  obtain ⟨⟨hnB, -⟩, -⟩ := minP_iff.1 ((hn n).2 rfl)
  have hzn : P z n := mem_prodCls_Rfwd.1 hz n hnB
  by_cases e : m = z
  · rw [e]
    exact hzn
  · rcases cxne hc hmf ⟨n, Or.inl hzn⟩ e with h | h
    · exact mem_transR.1 ht m z n ⟨h, hzn⟩
    · exact (hmn z hzA h).elim

/-- ✱205·53. \(\vdash : P \in \text{connex} \cap \text{Rl}ʻJ . x \in \alpha \cap CʻP . \overrightarrow{P}ʻx = Pʻʻ\alpha . \supset . x = \text{max}_{P}ʻ\alpha\) -/
theorem pm205_53 {α : Type u} {P : α → α → Prop} {A : Set α} {x : α} :
    (P ∈ connex ∩ rl J ∧ x ∈ A ∩ fld P) ∧ refs P x = P ʻʻ A →
      Desc (maxP P) A (fun m => x = m) := by
  rintro ⟨⟨⟨hc, hJ⟩, hxA, hx⟩, he⟩
  have hm : maxP P x A := by
    refine maxP_iff.2 ⟨⟨hxA, hx⟩, fun y hyA hxy => ?_⟩
    have : x ∈ refs P x := by rw [he]; exact ⟨y, hyA, hxy⟩
    exact mem_rl_J.1 hJ x this
  exact (max_desc hc hm _).2 rfl

/-- ✱205·54. \[\begin{align}&\vdash \colon\ldotp P \in \text{Ser} . \supset : x \in \alpha \cap CʻP . \overrightarrow{P}ʻx = Pʻʻ\alpha . \equiv . x = \text{max}_{P}ʻ\alpha \\ &[*205·53·22]\end{align}\] -/
theorem pm205_54 {α : Type u} {P : α → α → Prop} {A : Set α} {x : α} :
    P ∈ Ser → (x ∈ A ∩ fld P ∧ refs P x = P ʻʻ A ↔ Desc (maxP P) A (fun m => x = m)) := by
  intro hS
  constructor
  · rintro ⟨hx, he⟩
    exact pm205_53 ⟨⟨⟨hS.2, hS.1.1⟩, hx⟩, he⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨⟨hxA, hx⟩, hn⟩ := maxP_iff.1 ((hm x).2 rfl)
    refine ⟨⟨hxA, hx⟩, Set.Subset.antisymm (fun z hz => ⟨x, hxA, hz⟩) ?_⟩
    rintro z ⟨y, hyA, hzy⟩
    show P z x
    have hy : y ∈ fld P := ⟨z, Or.inr hzy⟩
    by_cases e : y = x
    · rw [← e]
      exact hzy
    · rcases cxne hS.2 hy hx e with h | h
      · exact mem_transR.1 hS.1.2 z y x ⟨hzy, h⟩
      · exact (hn y hyA h).elim

/-- ✱205·55. \(\vdash : P \in \text{connex} . BʻP \in \alpha . \supset . BʻP = \text{min}_{P}ʻ\alpha\) -/
theorem pm205_55 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ Desc Beg P (fun b => b ∈ A) →
      Desc Beg P (fun b => Desc (minP P) A (fun m => b = m)) := by
  rintro ⟨hc, b, hb, hbA⟩
  refine ⟨b, hb, ?_⟩
  obtain ⟨⟨y, hby⟩, hn⟩ := (hb b).2 rfl
  have hm : minP P b A := minP_iff.2 ⟨⟨hbA, ⟨y, Or.inl hby⟩⟩, fun z _ hzb => hn ⟨z, hzb⟩⟩
  exact (min_desc hc hm _).2 rfl

/-- ✱205·56. \(\vdash . \overrightarrow{\text{max}}_{P}ʻsʻ\kappa \subset \text{max}_{P}ʻʻ\kappa\) -/
theorem pm205_56 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} :
    refs (maxP P) (sumCls K) ⊆ maxP P ʻʻ K := by
  intro x hx
  obtain ⟨⟨⟨A, hAK, hxA⟩, hxf⟩, hn⟩ := maxP_iff.1 hx
  exact ⟨A, hAK, maxP_iff.2 ⟨⟨hxA, hxf⟩, fun y hy => hn y ⟨A, hAK, hy⟩⟩⟩

/-- ✱205·561. \(\vdash : \kappa \subset - \text{ᗡ}ʻ\text{max}_{P} . \supset . sʻ\kappa {\sim} \in \text{ᗡ}ʻ\text{max}_{P} \quad[*205·56 . *37·26·29]\) -/
theorem pm205_561 {α : Type u} {P : α → α → Prop} {K : Set (Set α)} :
    K ⊆ (codom (maxP P))ᶜ → sumCls K ∉ codom (maxP P) := by
  rintro hK ⟨x, hx⟩
  obtain ⟨A, hAK, hxA⟩ := pm205_56 hx
  exact hK hAK ⟨x, hxA⟩

/-- ✱205·6. \(\vdash \colon\ldotp P \in \text{connex} . \supset : {\sim} \text{E}! \text{min}_{P}ʻ\alpha . \equiv . \alpha \cap CʻP \subset \breve{P} ʻʻ\alpha \quad[*205·32·122]\) -/
theorem pm205_6 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex → (¬EDesc (minP P) A ↔ A ∩ fld P ⊆ P˘ ʻʻ A) := by
  intro hc
  rw [← (pm205_32 hc).1, ← pm205_122, eqΛ]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · rintro h ⟨x, hx⟩
    exact h x hx

/-- ✱205·601. \(\vdash : P \in \text{connex} . \alpha \subset CʻP . \supset : {\sim} \text{E}! \text{min}_{P}ʻ\alpha . \equiv . \alpha \subset \breve{P} ʻʻ\alpha \quad[*205·6]\) -/
theorem pm205_601 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ⊆ fld P → (¬EDesc (minP P) A ↔ A ⊆ P˘ ʻʻ A) := by
  rintro ⟨hc, hA⟩
  rw [pm205_6 hc, Set.inter_eq_left.2 hA]

/-- ✱205·61. \[\begin{align}&\vdash : P \in \text{connex} . \supset . CʻP = {CʻP \cap pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)} \cup \overrightarrow{\text{min}}_{P}ʻ\alpha \cup \breve{P} ʻʻ\alpha\\ &[*202·505 . *205·13]\end{align}\] -/
theorem pm205_61 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex →
      fld P = (fld P ∩ prodCls (Rfwd P ʻʻ (A ∩ fld P))) ∪ refs (minP P) A ∪ P˘ ʻʻ A := by
  intro hc
  apply Set.Subset.antisymm
  · intro x hx
    by_cases h1 : x ∈ P˘ ʻʻ A
    · exact Or.inr h1
    · by_cases h2 : x ∈ A
      · exact Or.inl (Or.inr (minP_iff.2 ⟨⟨h2, hx⟩, fun y hy hyx => h1 ⟨y, hy, hyx⟩⟩))
      · refine Or.inl (Or.inl ⟨hx, mem_prodCls_Rfwd.2 fun a ⟨ha, haf⟩ => ?_⟩)
        have hne : x ≠ a := fun e => h2 (by rw [e]; exact ha)
        rcases cxne hc hx haf hne with h | h
        · exact h
        · exact (h1 ⟨a, ha, h⟩).elim
  · rintro x ((⟨hx, -⟩ | hx) | ⟨a, -, hax⟩)
    · exact hx
    · exact (minP_iff.1 hx).1.2
    · exact ⟨a, Or.inr hax⟩

/-- ✱205·62. \[\begin{align}&\vdash : P \in \text{connex} . \exists ! \alpha \cap CʻP . \supset . CʻP = pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP) \cup \overrightarrow{\text{min}}_{P}ʻ\alpha \cup \breve{P} ʻʻ\alpha \\ &[*40·62 . *205·61]\end{align}\] -/
theorem pm205_62 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ (A ∩ fld P).Nonempty →
      fld P = prodCls (Rfwd P ʻʻ (A ∩ fld P)) ∪ refs (minP P) A ∪ P˘ ʻʻ A := by
  rintro ⟨hc, a, haA, ha⟩
  have e : fld P ∩ prodCls (Rfwd P ʻʻ (A ∩ fld P)) = prodCls (Rfwd P ʻʻ (A ∩ fld P)) :=
    Set.inter_eq_right.2 fun z hz => ⟨a, Or.inl (mem_prodCls_Rfwd.1 hz a ⟨haA, ha⟩)⟩
  rw [← e]
  exact pm205_61 hc

/-- ✱205·63. \[\begin{align}\vdash : P \in \text{connex} . P^{2} \,\unicode{x2abd}\, J . &\exists ! (\alpha \cap CʻP) . \supset .\\ &pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP) = CʻP - \breve{P} ʻʻ\alpha - \overrightarrow{\text{min}}_{P}ʻ\alpha\\ [*202·502 . *205·13]\end{align}\] -/
theorem pm205_63 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (P ∈ connex ∧ rsq P ⪽ J) ∧ (A ∩ fld P).Nonempty →
      prodCls (Rfwd P ʻʻ (A ∩ fld P)) = (fld P \ P˘ ʻʻ A) \ refs (minP P) A := by
  rintro ⟨⟨hc, hJ⟩, a, haA, ha⟩
  have irr := pm200_36 hJ
  apply Set.Subset.antisymm
  · intro z hz
    rw [mem_prodCls_Rfwd] at hz
    refine ⟨⟨⟨a, Or.inl (hz a ⟨haA, ha⟩)⟩, ?_⟩, ?_⟩
    · rintro ⟨b, hbA, hbz⟩
      exact hJ z z ⟨b, hz b ⟨hbA, ⟨z, Or.inl hbz⟩⟩, hbz⟩ rfl
    · intro hm
      obtain ⟨⟨hzA, hzf⟩, -⟩ := minP_iff.1 hm
      exact irr z z (hz z ⟨hzA, hzf⟩) rfl
  · rintro z ⟨⟨hz, h1⟩, h2⟩
    have hz' : z ∈ (fld P ∩ prodCls (Rfwd P ʻʻ (A ∩ fld P))) ∪ refs (minP P) A ∪ P˘ ʻʻ A := by
      rw [← pm205_61 hc]
      exact hz
    rcases hz' with (⟨-, h⟩ | h) | h
    · exact h
    · exact (h2 h).elim
    · exact (h1 h).elim

/-- ✱205·64. \[\begin{align}\vdash :P\in \text{connex} .\exists !&(\alpha \cap CʻP).\supset .\\ &\overrightarrow{\text{min}}_{P}ʻ\alpha =CʻP-\breve{P} ʻʻ\alpha -pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)\end{align}\] -/
theorem pm205_64 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ (A ∩ fld P).Nonempty →
      refs (minP P) A = (fld P \ P˘ ʻʻ A) \ prodCls (Rfwd P ʻʻ (A ∩ fld P)) := by
  rintro ⟨hc, -⟩
  apply Set.Subset.antisymm
  · intro m hm
    obtain ⟨⟨hmA, hmf⟩, hn⟩ := minP_iff.1 hm
    exact ⟨⟨hmf, fun ⟨y, hyA, hym⟩ => hn y hyA hym⟩,
      fun hp => hn m hmA (mem_prodCls_Rfwd.1 hp m ⟨hmA, hmf⟩)⟩
  · rintro z ⟨⟨hz, h1⟩, h2⟩
    have hz' : z ∈ (fld P ∩ prodCls (Rfwd P ʻʻ (A ∩ fld P))) ∪ refs (minP P) A ∪ P˘ ʻʻ A := by
      rw [← pm205_61 hc]
      exact hz
    rcases hz' with (⟨-, h⟩ | h) | h
    · exact (h2 h).elim
    · exact h
    · exact (h1 h).elim

/-- ✱205·65. \(\vdash :P\in \text{trans}\alpha \cap \text{connex} .\text{E}!\text{min}_{P}ʻ\alpha .\supset .pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)=\overrightarrow{P}ʻ\text{min}_{P}ʻ\alpha\)

**Status.** proved (reading): transcription error. The e-text prints the hypothesis
`P ∈ trans α ∩ connex`, with a stray `α`; the hypothesis is `P ∈ trans ∩ connex` (as in
✱205·211·22, which the demonstration of ✱205·66 cites). -/
theorem pm205_65 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR ∩ connex ∧ EDesc (minP P) A →
      Desc (minP P) A (fun m => prodCls (Rfwd P ʻʻ (A ∩ fld P)) = refs P m) := by
  rintro ⟨⟨ht, hc⟩, m, hm⟩
  rw [desc_iff_of hm]
  obtain ⟨⟨hmA, hmf⟩, hn⟩ := minP_iff.1 ((hm m).2 rfl)
  ext z
  rw [mem_prodCls_Rfwd]
  constructor
  · intro h
    exact h m ⟨hmA, hmf⟩
  · intro hzm a ⟨haA, ha⟩
    by_cases e : m = a
    · rw [← e]
      exact hzm
    · rcases cxne hc hmf ha e with h | h
      · exact mem_transR.1 ht z m a ⟨hzm, h⟩
      · exact (hn a haA h).elim

/-- ✱205·66. \[\begin{align}\vdash :P\in \text{trans}\alpha &\cap \text{connex} .\text{E}!\text{min}_{P}ʻ\alpha .\supset .\\ &pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)=\overrightarrow{P}ʻ\text{min}_{P}ʻ\alpha .\breve{P} ʻʻ\alpha =\overleftarrow{P}ʻ\text{min}_{P}ʻ\alpha .\\ &CʻP=pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP)\cup \iota ʻ\text{min}_{P}ʻ\alpha \cup \breve{P} ʻʻ\alpha\\ &[*205·65·22.*202·101]\end{align}\]

**Status.** proved (reading): transcription error, as in ✱205·65 (`trans α ∩ connex` for
`trans ∩ connex`). -/
theorem pm205_66 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ transR ∩ connex ∧ EDesc (minP P) A →
      (Desc (minP P) A (fun m => prodCls (Rfwd P ʻʻ (A ∩ fld P)) = refs P m) ∧
        Desc (minP P) A (fun m => P˘ ʻʻ A = rels P m)) ∧
        Desc (minP P) A (fun m => fld P = prodCls (Rfwd P ʻʻ (A ∩ fld P)) ∪ ι m ∪ P˘ ʻʻ A) := by
  rintro ⟨hP, m, hm⟩
  refine ⟨⟨pm205_65 ⟨hP, m, hm⟩, pm205_22 ⟨hP, m, hm⟩⟩, ?_⟩
  rw [desc_iff_of hm]
  obtain ⟨⟨hmA, hmf⟩, -⟩ := minP_iff.1 ((hm m).2 rfl)
  have e : refs (minP P) A = ι m := Set.ext fun z => hm z
  rw [← e]
  exact pm205_62 ⟨hP.2, m, hmA, hmf⟩

/-- ✱205·67. \(\vdash \colon\ldotp P\in \text{Ser}.\supset :x=\text{min}_{P}ʻ\alpha .\equiv .\overrightarrow{P}ʻx=pʻ\overrightarrow{P}ʻʻ(\alpha \cap CʻP).x\in CʻP\) -/
theorem pm205_67 {α : Type u} {P : α → α → Prop} {A : Set α} {x : α} :
    P ∈ Ser → (Desc (minP P) A (fun m => x = m) ↔
      refs P x = prodCls (Rfwd P ʻʻ (A ∩ fld P)) ∧ x ∈ fld P) := by
  intro hS
  have irr := mem_rl_J.1 hS.1.1
  constructor
  · rintro ⟨m, hm, rfl⟩
    have h := (desc_iff_of hm _).1 (pm205_65 ⟨⟨hS.1.2, hS.2⟩, x, hm⟩)
    exact ⟨h.symm, (minP_iff.1 ((hm x).2 rfl)).1.2⟩
  · rintro ⟨he, hx⟩
    have hp : ∀ z, P z x ↔ ∀ a, a ∈ A ∩ fld P → P z a := fun z => by
      have : z ∈ refs P x ↔ z ∈ prodCls (Rfwd P ʻʻ (A ∩ fld P)) := by rw [he]
      rw [mem_prodCls_Rfwd] at this
      exact this
    have hxA : x ∈ A := by
      by_contra hxA
      have : ∀ a, a ∈ A ∩ fld P → P x a := by
        rintro a ⟨haA, ha⟩
        have hne : x ≠ a := fun e => hxA (by rw [e]; exact haA)
        rcases cxne hS.2 hx ha hne with h | h
        · exact h
        · exact (irr a ((hp a).1 h a ⟨haA, ha⟩)).elim
      exact irr x ((hp x).2 this)
    have hm : minP P x A := by
      refine minP_iff.2 ⟨⟨hxA, hx⟩, fun y hyA hyx => ?_⟩
      exact irr y ((hp y).1 hyx y ⟨hyA, ⟨x, Or.inl hyx⟩⟩)
    exact (min_desc hS.2 hm _).2 rfl

/-- ✱205·68. \(\vdash :\breve{P} ʻʻ\alpha \subset \alpha .\supset .\overrightarrow{\text{min}}_{P}ʻ\alpha =\overrightarrow{\text{min}}(P_{\text{po}})ʻ\alpha\) -/
theorem pm205_68 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P˘ ʻʻ A ⊆ A → refs (minP P) A = refs (minP (po P)) A := by
  intro hA
  have clos : ∀ a b, Relation.ReflTransGen P a b → a ∈ A → b ∈ A := by
    intro a b h ha
    induction h with
    | refl => exact ha
    | tail _ hbc ih => exact hA ⟨_, ih, hbc⟩
  ext x
  show minP P x A ↔ minP (po P) x A
  rw [minP_iff, minP_iff, fld_po]
  constructor
  · rintro ⟨hx, hn⟩
    refine ⟨hx, fun y hyA hyx => ?_⟩
    obtain ⟨w, hyw, hwx⟩ := Relation.TransGen.tail'_iff.1 (po_iff_transGen.1 hyx)
    exact hn w (clos y w hyw hyA) hwx
  · rintro ⟨hx, hn⟩
    exact ⟨hx, fun y hyA hyx => hn y hyA (po_of hyx)⟩

/-- ✱205·681. \(\vdash :P_{\text{po}}\in \text{connex} .\breve{P} ʻʻ\alpha \subset \alpha .\supset .\overrightarrow{\text{min}}_{P}ʻ\alpha \in 0\cup 1 \quad[*205·68·3]\) -/
theorem pm205_681 {α : Type u} {P : α → α → Prop} {A : Set α} :
    po P ∈ connex ∧ P˘ ʻʻ A ⊆ A → refs (minP P) A ∈ (zero ∪ one : Set (Set α)) := by
  rintro ⟨hc, hA⟩
  rw [pm205_68 hA]
  exact (pm205_3 hc).1

/-- ✱205·7. \(\vdash :\exists !\overrightarrow{\text{max}}_{P}ʻPʻʻ\alpha .\supset .\exists !\overrightarrow{\text{max}}_{P}ʻ\alpha\)

**Status.** proved: the erratum of Vol. II (`max⃗_P` for `max_P` in the enunciation) is
already incorporated in the e-text. -/
theorem pm205_7 {α : Type u} {P : α → α → Prop} {A : Set α} :
    (refs (maxP P) (P ʻʻ A)).Nonempty → (refs (maxP P) A).Nonempty := by
  rintro ⟨x, hx⟩
  obtain ⟨⟨⟨a, haA, hxa⟩, -⟩, hn⟩ := maxP_iff.1 hx
  refine ⟨a, maxP_iff.2 ⟨⟨haA, ⟨x, Or.inr hxa⟩⟩, fun b hbA hab => ?_⟩⟩
  exact hn a ⟨b, hbA, hab⟩ hxa

/-- ✱205·71. \(\vdash :P\in \text{connex} .\exists !\overrightarrow{\text{max}}_{P}ʻPʻʻ\alpha .\supset .\text{max}_{P}ʻPʻʻ\alpha (P\dot{-} P^{2})\text{max}_{P}ʻ\alpha\) -/
theorem pm205_71 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ (refs (maxP P) (P ʻʻ A)).Nonempty →
      Desc (maxP P) (P ʻʻ A) (fun m => Desc (maxP P) A (fun n => (P ∸ rsq P) m n)) := by
  rintro ⟨hc, x, hx⟩
  rw [max_desc hc hx]
  obtain ⟨⟨⟨a, haA, hxa⟩, -⟩, hn⟩ := maxP_iff.1 hx
  have ha : maxP P a A := maxP_iff.2 ⟨⟨haA, ⟨x, Or.inr hxa⟩⟩, fun b hbA hab => hn a ⟨b, hbA, hab⟩ hxa⟩
  rw [max_desc hc ha]
  exact ⟨hxa, fun ⟨z, hxz, hza⟩ => hn z ⟨a, haA, hza⟩ hxz⟩

/-- ✱205·72. \(\vdash :P\in \text{connex} .P\,\unicode{x2abd}\, P^{2}.\supset .{\sim}\exists !\overrightarrow{\text{max}}_{P}ʻPʻʻ\alpha \quad[*205·71.\text{Transp}]\) -/
theorem pm205_72 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ P ⪽ rsq P → ¬(refs (maxP P) (P ʻʻ A)).Nonempty := by
  rintro ⟨hc, hP⟩ h
  obtain ⟨m, hm, n, hn, hmn, hn2⟩ := pm205_71 ⟨hc, h⟩
  exact hn2 (hP m n hmn)

/-- ✱205·73. \(\vdash :P\in \text{connex} .\text{min}_{P}ʻ\gamma =\text{max}_{P}ʻ\gamma .\supset .\gamma \cap CʻP\in 1.\gamma \cap CʻP=\iota ʻ\text{min}_{P}ʻ\gamma\) -/
theorem pm205_73 {α : Type u} {P : α → α → Prop} {C : Set α} :
    P ∈ connex ∧ Desc (minP P) C (fun m => Desc (maxP P) C (fun n => m = n)) →
      C ∩ fld P ∈ (one : Set (Set α)) ∧ Desc (minP P) C (fun m => C ∩ fld P = ι m) := by
  rintro ⟨hc, m, hm, n, hn, e⟩
  obtain ⟨⟨hmC, hmf⟩, hmn⟩ := minP_iff.1 ((hm m).2 rfl)
  obtain ⟨-, hmx⟩ := maxP_iff.1 ((hn m).2 e)
  have e : C ∩ fld P = ι m := by
    ext y
    constructor
    · rintro ⟨hyC, hy⟩
      by_contra hne
      rcases cxne hc hmf hy (fun e => hne (show y = m from e.symm)) with h | h
      · exact hmx y hyC h
      · exact hmn y hyC h
    · intro hy
      rw [show y = m from hy]
      exact ⟨hmC, hmf⟩
  refine ⟨by rw [e]; exact ⟨m, rfl⟩, (desc_iff_of hm _).2 e⟩

/-- ✱205·731. \[\begin{align}&\vdash \colon\ldotp P\in \text{connex} \cap \text{Rl}ʻJ.\supset :\text{min}_{P}ʻ\gamma =\text{max}_{P}ʻ\gamma .\equiv .\gamma \cap CʻP\in 1\\ &[*205·17·73]\end{align}\] -/
theorem pm205_731 {α : Type u} {P : α → α → Prop} {C : Set α} :
    P ∈ connex ∩ rl J →
      (Desc (minP P) C (fun m => Desc (maxP P) C (fun n => m = n)) ↔
        C ∩ fld P ∈ (one : Set (Set α))) := by
  rintro ⟨hc, hJ⟩
  refine ⟨fun h => (pm205_73 ⟨hc, h⟩).1, fun h => ?_⟩
  obtain ⟨c, hcc⟩ := mem_one_iff.1 h
  obtain ⟨hcC, hcf⟩ := (hcc c).2 rfl
  have e := pm205_17 (A := C) ⟨fun x _ => mem_rl_J.1 hJ x, h⟩
  have hmin : minP P c C := by
    have : c ∈ refs (minP P) C := by rw [e.1, e.2]; exact ⟨hcC, hcf⟩
    exact this
  have hmax : maxP P c C := by
    have : c ∈ refs (maxP P) C := by rw [e.2]; exact ⟨hcC, hcf⟩
    exact this
  rw [min_desc hc hmin, max_desc hc hmax]

/-- ✱205·732. \[\begin{align}\vdash :P\in \text{connex} .\gamma \cap CʻP{\sim}\in 1.\text{E}!&\text{min}_{P}ʻ\gamma .\text{E}!\text{max}_{P}ʻ\gamma .\supset .\\ &\text{min}_{P}ʻ\gamma P\text{max}_{P}ʻ\gamma\end{align}\] -/
theorem pm205_732 {α : Type u} {P : α → α → Prop} {C : Set α} :
    ((P ∈ connex ∧ C ∩ fld P ∉ (one : Set (Set α))) ∧ EDesc (minP P) C) ∧ EDesc (maxP P) C →
      Desc (minP P) C (fun m => Desc (maxP P) C (fun n => P m n)) := by
  rintro ⟨⟨⟨hc, h1⟩, m, hm⟩, n, hn⟩
  rw [desc_iff_of hm, desc_iff_of hn]
  obtain ⟨⟨hmC, hmf⟩, hmn⟩ := minP_iff.1 ((hm m).2 rfl)
  obtain ⟨⟨hnC, hnf⟩, hnx⟩ := maxP_iff.1 ((hn n).2 rfl)
  by_cases e : m = n
  · exfalso
    apply h1
    have := (pm205_73 (C := C) ⟨hc, (desc_iff_of hm _).2 ((desc_iff_of hn _).2 e)⟩).1
    exact this
  · rcases cxne hc hmf hnf e with h | h
    · exact h
    · exact (hmn n hnC h).elim

/-- ✱205·74. \(\vdash : \alpha \cap CʻP \subset \overrightarrow{B}ʻ\breve{P} . \supset . \overrightarrow{\text{min}}_{P}ʻ\alpha = \alpha \cap CʻP\) -/
theorem pm205_74 {α : Type u} {P : α → α → Prop} {A : Set α} :
    A ∩ fld P ⊆ refs Beg P˘ → refs (minP P) A = A ∩ fld P := by
  intro h
  ext x
  show minP P x A ↔ _
  rw [minP_iff]
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun y hyA hyx => ?_⟩⟩
  obtain ⟨-, hy⟩ := h ⟨hyA, ⟨x, Or.inl hyx⟩⟩
  exact hy ⟨x, hyx⟩

/-- ✱205·741. \(\vdash : P \in \text{connex} . \alpha \cap CʻP {\sim} \in 1 . \supset . \overrightarrow{\text{min}}_{P}ʻ\alpha \subset \text{D}ʻP\) -/
theorem pm205_741 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex ∧ A ∩ fld P ∉ (one : Set (Set α)) → refs (minP P) A ⊆ dom P := by
  rintro ⟨hc, h1⟩ m hm
  obtain ⟨⟨hmA, hmf⟩, hn⟩ := minP_iff.1 hm
  have : ∃ y, y ∈ A ∩ fld P ∧ y ≠ m := by
    by_contra hk
    push_neg at hk
    exact h1 (mem_one_iff.2 ⟨m, fun z => ⟨fun hz => hk z hz,
      fun e => by rw [e]; exact ⟨hmA, hmf⟩⟩⟩)
  obtain ⟨y, ⟨hyA, hy⟩, hne⟩ := this
  rcases cxne hc hmf hy (Ne.symm hne) with h | h
  · exact ⟨y, h⟩
  · exact (hn y hyA h).elim

/-- ✱205·742. \(\vdash \colon\ldotp P \in \text{connex} . \supset : \exists ! \overrightarrow{\text{min}}_{P}ʻ\alpha - \text{D}ʻP . \equiv . \alpha \cap CʻP = {℩}ʻBʻ\breve{P}\) -/
theorem pm205_742 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex → ((refs (minP P) A \ dom P).Nonempty ↔
      Desc Beg P˘ (fun e => A ∩ fld P = ι e)) := by
  intro hc
  constructor
  · rintro ⟨m, hm, hmd⟩
    obtain ⟨⟨hmA, hmf⟩, hn⟩ := minP_iff.1 hm
    have hmc : m ∈ codom P := by
      obtain ⟨y, hy | hy⟩ := hmf
      · exact (hmd ⟨y, hy⟩).elim
      · exact ⟨y, hy⟩
    have hbeg : Beg m P˘ := ⟨hmc, hmd⟩
    refine ⟨m, fun x => ⟨fun hx => mem_zero_union_one.1 (pm202_52 hc).2 x m hx hbeg,
      fun e => by rw [e]; exact hbeg⟩, ?_⟩
    ext y
    constructor
    · rintro ⟨hyA, hy⟩
      show y = m
      by_contra hne
      rcases cxne hc hy hmf hne with h | h
      · exact hn y hyA h
      · exact hmd ⟨y, h⟩
    · intro hy
      rw [show y = m from hy]
      exact ⟨hmA, hmf⟩
  · rintro ⟨e, he, hA⟩
    obtain ⟨⟨w, hwe⟩, hed⟩ := (he e).2 rfl
    have heA : e ∈ A ∩ fld P := by rw [hA]; exact mem_unitCls.2 rfl
    refine ⟨e, minP_iff.2 ⟨heA, fun y hyA hye => ?_⟩, hed⟩
    have : y ∈ ι e := by rw [← hA]; exact ⟨hyA, ⟨e, Or.inl hye⟩⟩
    rw [show y = e from this] at hye
    exact hed ⟨e, hye⟩

/-- ✱205·75. \[\begin{align}&\vdash \colon\ldotp P \in \text{connex} . \supset : {\sim} (\alpha \cap CʻP = {℩}ʻBʻ\breve{P} ) . \equiv . \overrightarrow{\text{min}}_{P}ʻ\alpha \subset \text{D}ʻP\\ &[*205·742]\end{align}\] -/
theorem pm205_75 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P ∈ connex → (¬Desc Beg P˘ (fun e => A ∩ fld P = ι e) ↔ refs (minP P) A ⊆ dom P) := by
  intro hc
  rw [← pm205_742 hc]
  constructor
  · intro h x hx
    by_contra hxd
    exact h ⟨x, hx, hxd⟩
  · rintro h ⟨x, hx, hxd⟩
    exact hxd (h hx)

/-- ✱205·8. \(\vdash : S \in P \overline{\,\text{smor}\,} Q . \supset . \overrightarrow{\text{min}}_{P}ʻ\alpha = Sʻʻ\overrightarrow{\text{min}}_{Q}ʻ\breve{S} ʻʻ\alpha\) -/
theorem pm205_8 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {S : α → β → Prop} {A : Set α} :
    S ∈ smorbar P Q → refs (minP P) A = S ʻʻ refs (minP Q) (S˘ ʻʻ A) := by
  rintro ⟨⟨hS, hcod⟩, rfl⟩
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS
  have hf : ∀ x, x ∈ fld (S ⁏ Q) ↔ ∃ z, S x z ∧ z ∈ fld Q := by
    intro x
    constructor
    · rintro ⟨y, h | h⟩
      · obtain ⟨a, b, ⟨hxa, -⟩, hab⟩ := (semi_apply S Q x y).1 h
        exact ⟨a, hxa, ⟨b, Or.inl hab⟩⟩
      · obtain ⟨a, b, ⟨-, hxb⟩, hab⟩ := (semi_apply S Q y x).1 h
        exact ⟨b, hxb, ⟨a, Or.inr hab⟩⟩
    · rintro ⟨z, hxz, w, hzw | hwz⟩
      · obtain ⟨y, hyw⟩ : w ∈ codom S := by rw [← hcod]; exact ⟨z, Or.inr hzw⟩
        exact ⟨y, Or.inl ((semi_apply S Q x y).2 ⟨z, w, ⟨hxz, hyw⟩, hzw⟩)⟩
      · obtain ⟨y, hyw⟩ : w ∈ codom S := by rw [← hcod]; exact ⟨z, Or.inl hwz⟩
        exact ⟨y, Or.inr ((semi_apply S Q y x).2 ⟨w, z, ⟨hyw, hxz⟩, hwz⟩)⟩
  ext x
  constructor
  · intro hx
    obtain ⟨⟨hxA, hxf⟩, hn⟩ := minP_iff.1 hx
    obtain ⟨z, hxz, hz⟩ := (hf x).1 hxf
    refine ⟨z, minP_iff.2 ⟨⟨⟨x, hxA, hxz⟩, hz⟩, ?_⟩, hxz⟩
    rintro w ⟨y, hyA, hyw⟩ hwz
    exact hn y hyA ((semi_apply S Q y x).2 ⟨w, z, ⟨hyw, hxz⟩, hwz⟩)
  · rintro ⟨z, hz, hxz⟩
    obtain ⟨⟨⟨y, hyA, hyz⟩, hzf⟩, hn⟩ := minP_iff.1 hz
    have e : y = x := h1 y x z ⟨hyz, hxz⟩
    rw [e] at hyA
    refine minP_iff.2 ⟨⟨hyA, (hf x).2 ⟨z, hxz, hzf⟩⟩, fun y' hy'A hy'x => ?_⟩
    obtain ⟨w, z', ⟨hy'w, hxz'⟩, hwz'⟩ := (semi_apply S Q y' x).1 hy'x
    have e' : z' = z := h2 x z' z ⟨hxz', hxz⟩
    rw [e'] at hwz'
    exact hn w ⟨y', hy'A, hy'w⟩ hwz'

/-- ✱205·81. \(\vdash \colon\ldotp S\in P\,\overline{\,\text{smor}\,}\,Q.\supset :\text{E}!\text{min}_{P}ʻ\alpha .\equiv .\text{E}!\text{min}_{Q}ʻ\breve{S}ʻʻ\alpha\) -/
theorem pm205_81 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {S : α → β → Prop} {A : Set α} :
    S ∈ smorbar P Q → (EDesc (minP P) A ↔ EDesc (minP Q) (S˘ ʻʻ A)) := by
  intro h
  have e := pm205_8 (A := A) h
  obtain ⟨⟨hS, hcod⟩, -⟩ := h
  obtain ⟨h1, h2⟩ := mem_arrow_one_one.1 hS
  rw [← refs_mem_one_iff, ← refs_mem_one_iff, e]
  have hsub : refs (minP Q) (S˘ ʻʻ A) ⊆ codom S := by
    rw [← hcod]
    exact fun z hz => (minP_iff.1 hz).1.2
  constructor
  · intro h
    obtain ⟨c, hc⟩ := mem_one_iff.1 h
    obtain ⟨z, hz, hcz⟩ := (hc c).2 rfl
    refine mem_one_iff.2 ⟨z, fun z' => ⟨fun hz' => ?_, fun e' => by rw [e']; exact hz⟩⟩
    obtain ⟨x', hx'⟩ := hsub hz'
    have : x' = c := (hc x').1 ⟨z', hz', hx'⟩
    rw [this] at hx'
    exact h2 c z' z ⟨hx', hcz⟩
  · intro h
    obtain ⟨z, hz⟩ := mem_one_iff.1 h
    obtain ⟨x, hxz⟩ := hsub ((hz z).2 rfl)
    refine mem_one_iff.2 ⟨x, fun x' => ⟨fun ⟨z', hz', hx'z'⟩ => ?_, fun e' => ?_⟩⟩
    · have : z' = z := (hz z').1 hz'
      rw [this] at hx'z'
      exact h1 x' x z ⟨hx'z', hxz⟩
    · rw [e']
      exact ⟨z, (hz z).2 rfl, hxz⟩

/-- ✱205·82. \[\begin{align}&\vdash :S\in P\,\overline{\,\text{smor}\,}\,Q.\text{E}!\text{min}_{P}ʻ\alpha .\supset .\text{min}_{P}ʻ\alpha =Sʻ\text{min}_{Q}ʻ\breve{S} ʻʻ\alpha\\ &[*53·31.*205·8·81]\end{align}\] -/
theorem pm205_82 {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {S : α → β → Prop} {A : Set α} :
    S ∈ smorbar P Q ∧ EDesc (minP P) A →
      Desc (minP P) A (fun m => Desc2 S (minP Q) (S˘ ʻʻ A) (fun s => m = s)) := by
  rintro ⟨h, m, hm⟩
  have e := pm205_8 (A := A) h
  obtain ⟨n, hn⟩ := (pm205_81 (A := A) h).1 ⟨m, hm⟩
  obtain ⟨⟨hS, -⟩, -⟩ := h
  obtain ⟨h1, -⟩ := mem_arrow_one_one.1 hS
  have hmS : m ∈ S ʻʻ refs (minP Q) (S˘ ʻʻ A) := by rw [← e]; exact (hm m).2 rfl
  obtain ⟨z, hz, hmz⟩ := hmS
  have ez : z = n := (hn z).1 hz
  rw [ez] at hmz
  rw [desc_iff_of hm, desc2_iff, desc_iff_of hn]
  exact (desc_iff_of (R := S) (y := n) (b := m)
    (fun x => ⟨fun hx => h1 x m n ⟨hx, hmz⟩, fun e' => by rw [e']; exact hmz⟩) _).2 rfl

/-- ✱205·83. \(\vdash :z{\sim}\in CʻP.\exists !CʻP\cap \alpha .\supset .\overrightarrow{\text{min}}_{P}ʻ\alpha =\overrightarrow{\text{min}}(P\unicode{x21f8} z)ʻ\alpha\) -/
theorem pm205_83 {α : Type u} {P : α → α → Prop} {A : Set α} {z : α} :
    z ∉ fld P ∧ (fld P ∩ A).Nonempty → refs (minP P) A = refs (minP (P ⇸ z)) A := by
  rintro ⟨hz, a, haf, haA⟩
  have hf : ∀ x, x ∈ fld (P ⇸ z) ↔ x ∈ fld P ∨ x = z := by
    intro x
    constructor
    · rintro ⟨w, (h | ⟨h, -⟩) | (h | ⟨-, h⟩)⟩
      · exact Or.inl ⟨w, Or.inl h⟩
      · exact Or.inl h
      · exact Or.inl ⟨w, Or.inr h⟩
      · exact Or.inr h
    · rintro (⟨w, h | h⟩ | rfl)
      · exact ⟨w, Or.inl (Or.inl h)⟩
      · exact ⟨w, Or.inr (Or.inl h)⟩
      · exact ⟨a, Or.inr (Or.inr ⟨haf, rfl⟩)⟩
  ext x
  show minP P x A ↔ minP (P ⇸ z) x A
  rw [minP_iff, minP_iff, hf]
  constructor
  · rintro ⟨⟨hxA, hx⟩, hn⟩
    refine ⟨⟨hxA, Or.inl hx⟩, fun y hyA hyx => ?_⟩
    rcases hyx with h | ⟨-, e⟩
    · exact hn y hyA h
    · rw [e] at hx
      exact hz hx
  · rintro ⟨⟨hxA, hx | e⟩, hn⟩
    · exact ⟨⟨hxA, hx⟩, fun y hyA hyx => hn y hyA (Or.inl hyx)⟩
    · exact (hn a haA (Or.inr ⟨haf, e⟩)).elim

/-- ✱205·831. \(\vdash :z{\sim}\in CʻP.Cʻ(P\unicode{x21f8} z)\cap \alpha =\iota ʻz.\supset .\overrightarrow{\text{min}}(P\unicode{x21f8} z)ʻ\alpha =\iota ʻz\) -/
theorem pm205_831 {α : Type u} {P : α → α → Prop} {A : Set α} {z : α} :
    z ∉ fld P ∧ fld (P ⇸ z) ∩ A = ι z → refs (minP (P ⇸ z)) A = ι z := by
  rintro ⟨hz, he⟩
  have hzz : z ∈ fld (P ⇸ z) ∩ A := by rw [he]; exact mem_unitCls.2 rfl
  ext x
  show minP (P ⇸ z) x A ↔ x ∈ ι z
  rw [minP_iff]
  constructor
  · rintro ⟨⟨hxA, hx⟩, -⟩
    rw [← he]
    exact ⟨hx, hxA⟩
  · intro hx
    rw [show x = z from hx]
    refine ⟨⟨hzz.2, hzz.1⟩, fun y hyA hyz => ?_⟩
    rcases hyz with h | ⟨hy, -⟩
    · exact hz ⟨y, Or.inr h⟩
    · have hyf : y ∈ fld (P ⇸ z) := by
        obtain ⟨w, hw | hw⟩ := hy
        · exact ⟨w, Or.inl (Or.inl hw)⟩
        · exact ⟨w, Or.inr (Or.inl hw)⟩
      have : y ∈ ι z := by rw [← he]; exact ⟨hyf, hyA⟩
      rw [show y = z from this] at hy
      exact hz hy

/-- ✱205·832. \(\vdash :z{\sim}\in CʻP.z{\sim}\in \alpha .\supset .\overrightarrow{\text{max}}_{P}ʻ\alpha =\overrightarrow{\text{max}}(P\unicode{x21f8} z)ʻ\alpha\) -/
theorem pm205_832 {α : Type u} {P : α → α → Prop} {A : Set α} {z : α} :
    z ∉ fld P ∧ z ∉ A → refs (maxP P) A = refs (maxP (P ⇸ z)) A := by
  rintro ⟨hz, hzA⟩
  ext x
  show maxP P x A ↔ maxP (P ⇸ z) x A
  rw [maxP_iff, maxP_iff]
  constructor
  · rintro ⟨⟨hxA, hx⟩, hn⟩
    refine ⟨⟨hxA, ?_⟩, fun y hyA hxy => ?_⟩
    · obtain ⟨w, hw | hw⟩ := hx
      · exact ⟨w, Or.inl (Or.inl hw)⟩
      · exact ⟨w, Or.inr (Or.inl hw)⟩
    · rcases hxy with h | ⟨-, e⟩
      · exact hn y hyA h
      · rw [e] at hyA
        exact hzA hyA
  · rintro ⟨⟨hxA, hx⟩, hn⟩
    have hxz : x ≠ z := fun e => hzA (by rw [← e]; exact hxA)
    refine ⟨⟨hxA, ?_⟩, fun y hyA hxy => hn y hyA (Or.inl hxy)⟩
    obtain ⟨w, (h | ⟨h, -⟩) | (h | ⟨-, e⟩)⟩ := hx
    · exact ⟨w, Or.inl h⟩
    · exact h
    · exact ⟨w, Or.inr h⟩
    · exact (hxz e).elim

/-- ✱205·833. \(\vdash :\dot{\exists} !P.z{\sim}\in CʻP.z\in \alpha .\supset .\overrightarrow{\text{max}}(P\unicode{x21f8} z)ʻ\alpha =\iota ʻz\) -/
theorem pm205_833 {α : Type u} {P : α → α → Prop} {A : Set α} {z : α} :
    (rEx P ∧ z ∉ fld P) ∧ z ∈ A → refs (maxP (P ⇸ z)) A = ι z := by
  rintro ⟨⟨⟨a, b, hab⟩, hz⟩, hzA⟩
  have ha : a ∈ fld P := ⟨b, Or.inl hab⟩
  ext x
  show maxP (P ⇸ z) x A ↔ x ∈ ι z
  rw [maxP_iff]
  constructor
  · rintro ⟨⟨hxA, hx⟩, hn⟩
    show x = z
    by_contra hxz
    have hxf : x ∈ fld P := by
      obtain ⟨w, (h | ⟨h, -⟩) | (h | ⟨-, e⟩)⟩ := hx
      · exact ⟨w, Or.inl h⟩
      · exact h
      · exact ⟨w, Or.inr h⟩
      · exact (hxz e).elim
    exact hn z hzA (Or.inr ⟨hxf, rfl⟩)
  · intro hx
    rw [show x = z from hx]
    refine ⟨⟨hzA, ⟨a, Or.inr (Or.inr ⟨ha, rfl⟩)⟩⟩, fun y _ hzy => ?_⟩
    rcases hzy with h | ⟨h, -⟩
    · exact hz ⟨y, Or.inl h⟩
    · exact hz h

/-- ✱205·84. \(\vdash :CʻP\cap CʻQ=\Lambda .\exists !CʻP\cap \alpha .\supset .\overrightarrow{\text{min}}(P\unicode{x2909}Q)ʻ\alpha =\overrightarrow{\text{min}}_{P}ʻ\alpha\) -/
theorem pm205_84 {α : Type u} {P Q : α → α → Prop} {A : Set α} :
    fld P ∩ fld Q = Λ ∧ (fld P ∩ A).Nonempty → refs (minP (P ⤉ Q)) A = refs (minP P) A := by
  rintro ⟨hd, a, haf, haA⟩
  have d := eqΛ.1 hd
  ext x
  show minP (P ⤉ Q) x A ↔ minP P x A
  rw [minP_iff, minP_iff, fld_rsum]
  constructor
  · rintro ⟨⟨hxA, hx | hx⟩, hn⟩
    · exact ⟨⟨hxA, hx⟩, fun y hyA hyx => hn y hyA (Or.inl (Or.inl hyx))⟩
    · exact (hn a haA (Or.inr ⟨haf, hx⟩)).elim
  · rintro ⟨⟨hxA, hx⟩, hn⟩
    refine ⟨⟨hxA, Or.inl hx⟩, fun y hyA hyx => ?_⟩
    rcases hyx with (h | h) | ⟨-, h⟩
    · exact hn y hyA h
    · exact d x ⟨hx, ⟨y, Or.inr h⟩⟩
    · exact d x ⟨hx, h⟩

/-- ✱205·841. \(\vdash :CʻP\cap \alpha =\Lambda .\supset .\overrightarrow{\text{min}}(P\unicode{x2909}Q)ʻ\alpha =\overrightarrow{\text{min}}_{Q}ʻ\alpha\) -/
theorem pm205_841 {α : Type u} {P Q : α → α → Prop} {A : Set α} :
    fld P ∩ A = Λ → refs (minP (P ⤉ Q)) A = refs (minP Q) A := by
  intro hd
  have d := eqΛ.1 hd
  ext x
  show minP (P ⤉ Q) x A ↔ minP Q x A
  rw [minP_iff, minP_iff, fld_rsum]
  constructor
  · rintro ⟨⟨hxA, hx | hx⟩, hn⟩
    · exact (d x ⟨hx, hxA⟩).elim
    · exact ⟨⟨hxA, hx⟩, fun y hyA hyx => hn y hyA (Or.inl (Or.inr hyx))⟩
  · rintro ⟨⟨hxA, hx⟩, hn⟩
    refine ⟨⟨hxA, Or.inr hx⟩, fun y hyA hyx => ?_⟩
    rcases hyx with (h | h) | ⟨hy, -⟩
    · exact d x ⟨⟨y, Or.inr h⟩, hxA⟩
    · exact hn y hyA h
    · exact d y ⟨hy, hyA⟩

/-- ✱205·85. \(\vdash \colon\ldotp P\in \text{Rel}^{2}\text{excl}.\supset :x\{\text{min}(\Sigma ʻP)\}\alpha .\equiv .(\exists Q).Q\text{min}_{P}(\breve{F} ʻʻ\alpha ).x\text{min}_{Q}\alpha\) -/
theorem pm205_85 {α : Type u} {P : (α → α → Prop) → (α → α → Prop) → Prop} {x : α}
    {A : Set α} :
    P ∈ Rel2excl → (minP (relSigma P) x A ↔ ∃ Q, minP P Q (F˘ ʻʻ A) ∧ minP Q x A) := by
  intro hex
  have disj : ∀ Q R z, Q ∈ fld P → R ∈ fld P → z ∈ fld Q → z ∈ fld R → Q = R := by
    intro Q R z hQ hR hzQ hzR
    by_contra hne
    exact eqΛ.1 (hex Q R ⟨⟨hQ, hR⟩, hne⟩) z ⟨hzQ, hzR⟩
  have hfS : ∀ y, y ∈ fld (relSigma P) ↔ ∃ Q, Q ∈ fld P ∧ y ∈ fld Q := by
    intro y
    constructor
    · rintro ⟨w, h | h⟩
      · rcases (relSigma_apply P y w).1 h with ⟨Q, hQ, hyw⟩ | ⟨Q, R, ⟨hy, -⟩, hQR⟩
        · exact ⟨Q, hQ, ⟨w, Or.inl hyw⟩⟩
        · exact ⟨Q, ⟨R, Or.inl hQR⟩, hy⟩
      · rcases (relSigma_apply P w y).1 h with ⟨Q, hQ, hwy⟩ | ⟨Q, R, ⟨-, hy⟩, hQR⟩
        · exact ⟨Q, hQ, ⟨w, Or.inr hwy⟩⟩
        · exact ⟨R, ⟨Q, Or.inr hQR⟩, hy⟩
    · rintro ⟨Q, hQ, w, hw | hw⟩
      · exact ⟨w, Or.inl ((relSigma_apply P y w).2 (Or.inl ⟨Q, hQ, hw⟩))⟩
      · exact ⟨w, Or.inr ((relSigma_apply P w y).2 (Or.inl ⟨Q, hQ, hw⟩))⟩
  rw [minP_iff]
  constructor
  · rintro ⟨⟨hxA, hx⟩, hn⟩
    obtain ⟨Q, hQ, hxQ⟩ := (hfS x).1 hx
    refine ⟨Q, minP_iff.2 ⟨⟨⟨x, hxA, hxQ⟩, hQ⟩, ?_⟩, minP_iff.2 ⟨⟨hxA, hxQ⟩, ?_⟩⟩
    · rintro R ⟨y, hyA, hyR⟩ hRQ
      exact hn y hyA ((relSigma_apply P y x).2 (Or.inr ⟨R, Q, ⟨hyR, hxQ⟩, hRQ⟩))
    · intro y hyA hyx
      exact hn y hyA ((relSigma_apply P y x).2 (Or.inl ⟨Q, hQ, hyx⟩))
  · rintro ⟨Q, hQm, hxm⟩
    obtain ⟨⟨-, hQ⟩, hQn⟩ := minP_iff.1 hQm
    obtain ⟨⟨hxA, hxQ⟩, hxn⟩ := minP_iff.1 hxm
    refine ⟨⟨hxA, (hfS x).2 ⟨Q, hQ, hxQ⟩⟩, fun y hyA hyx => ?_⟩
    rcases (relSigma_apply P y x).1 hyx with ⟨R, hR, hyxR⟩ | ⟨R, S, ⟨hyR, hxS⟩, hRS⟩
    · have e := disj R Q x hR hQ ⟨y, Or.inr hyxR⟩ hxQ
      rw [e] at hyxR
      exact hxn y hyA hyxR
    · have e := disj S Q x ⟨R, Or.inr hRS⟩ hQ hxS hxQ
      rw [e] at hRS
      exact hQn R ⟨y, hyA, hyR⟩ hRS

/-- ✱205·9. \[\begin{align}&\vdash :P\in \text{connex} .\kappa \subset CʻP.\kappa {\sim}\in 1.\supset .\overrightarrow{\text{min}}(P\unicode{x0294f}\kappa )ʻ\alpha =\overrightarrow{\text{min}}_{P}ʻ(a\cap \kappa )\\ &[*205·261]\end{align}\]

**Status.** proved (reading): transcription error. The e-text prints `min⃗_P'(a ∩ κ)` with
a roman `a` for `α`; the demonstration (✱205·261) gives `min⃗_P'(α ∩ κ)`, which is stated. -/
theorem pm205_9 {α : Type u} {P : α → α → Prop} {A : Set α} {K : Set α} :
    (P ∈ connex ∧ K ⊆ fld P) ∧ K ∉ (one : Set (Set α)) →
      refs (minP (P ⥏ K)) A = refs (minP P) (A ∩ K) := by
  rintro ⟨⟨hc, hK⟩, h1⟩
  have e : K ∩ fld P = K := Set.inter_eq_left.2 hK
  exact pm205_261 ⟨hc, by rw [e]; exact h1⟩

/-- ✱205·91. \(\vdash :\breve{P} ʻʻ\alpha \subset \alpha .P_{\text{po}}\unicode{x0294f}\alpha \in \text{connex} .\supset .\overrightarrow{\text{min}}_{P}ʻ\alpha \in 0\cup 1\)

**Status.** proved (corrected): false as printed. Take `P` relating `0` to `1` and `2` to
`3`, and `α = {1, 3}`: `P̆''α = Λ ⊂ α`, `P_po⥏α = Λ̇` is connected, but `min⃗_P'α = α` has two
members (`pm205_91_printed_false`). The demonstration uses ✱205·261 for `P_po⥏α`, which needs
the connexity of `P_po` itself (see ✱202·54, ✱205·261); with the hypothesis
`P_po⥏α ∈ connex` corrected to `P_po ∈ connex` the proposition is proved (it is then
✱205·681). -/
theorem pm205_91 {α : Type u} {P : α → α → Prop} {A : Set α} :
    P˘ ʻʻ A ⊆ A ∧ po P ∈ connex → refs (minP P) A ∈ (zero ∪ one : Set (Set α)) :=
  fun ⟨hA, hc⟩ => pm205_681 ⟨hc, hA⟩

/-- The printed form of ✱205·91 (hypothesis `P_po⥏α ∈ connex`) is false. -/
theorem pm205_91_printed_false :
    ¬ ∀ (P : ℕ → ℕ → Prop) (A : Set ℕ), P˘ ʻʻ A ⊆ A ∧ po P ⥏ A ∈ connex →
      refs (minP P) A ∈ (zero ∪ one : Set (Set ℕ)) := by
  intro h
  have ht : cex91P ∈ transR := by
    rw [mem_transR]
    rintro a b c ⟨h1, h2⟩
    simp only [cex91P] at h1 h2
    omega
  have hpo : po cex91P = cex91P := po_eq_of_transR ht
  have hA : cex91P˘ ʻʻ cex91A ⊆ cex91A := by
    rintro x ⟨y, hy, hyx⟩
    have hyx' : cex91P y x := hyx
    simp only [cex91A, cex91P, Set.mem_ofPred_eq] at hy hyx' ⊢
    omega
  have hnull : ∀ a b, ¬ (po cex91P ⥏ cex91A) a b := by
    rintro a b ⟨⟨ha, hab⟩, hb⟩
    rw [hpo] at hab
    simp only [cex91A, cex91P, Set.mem_ofPred_eq] at ha hb hab
    omega
  have hc : po cex91P ⥏ cex91A ∈ connex := by
    rw [mem_connex]
    rintro x y ⟨⟨w, hw | hw⟩, -⟩
    · exact (hnull _ _ hw).elim
    · exact (hnull _ _ hw).elim
  have hmin : ∀ x, x ∈ cex91A → x ∈ refs (minP cex91P) cex91A := by
    intro x hx
    refine minP_iff.2 ⟨⟨hx, ?_⟩, fun y hy hyx => ?_⟩
    · rcases hx with rfl | rfl
      · exact ⟨0, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · exact ⟨2, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    · simp only [cex91A, cex91P, Set.mem_ofPred_eq] at hx hy hyx
      omega
  have h1 := hmin 1 (Or.inl rfl)
  have h3 := hmin 3 (Or.inr rfl)
  have := mem_zero_union_one.1 (h cex91P cex91A ⟨hA, hc⟩) 1 3 h1 h3
  omega

end PrincipiaMathematica
