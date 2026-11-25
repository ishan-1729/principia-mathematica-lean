import PrincipiaMathematica.Defs.Part2

/-!
# Part II, Section B: Sub-classes, sub-relations, and relative types

Volume 1. Numbers: ✱60, ✱61, ✱62, ✱63, ✱64, ✱65.

Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring
gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.
-/

namespace PrincipiaMathematica

universe u v w u' v' w' u'' v''

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u'}

/-! ### Helper lemmas for Section B (not PM propositions) -/

private theorem mem_iota_Null {B : Set α} : B ∈ ι (Λ : Set α) ↔ B = ∅ := by
  rw [mem_unitCls, Null_eq_empty]

private theorem eq_rNull_iff {R : α → β → Prop} : R = rNull ↔ ¬ rEx R := by
  constructor
  · rintro rfl ⟨x, y, h⟩
    exact rNull_apply x y h
  · intro h
    funext x y
    exact propext ⟨fun hr => (h ⟨x, y, hr⟩).elim, fun hr => (rNull_apply x y hr).elim⟩

/-- `ι'x ∈ Cl ex'α` when `x ∈ α` (✱60·6, needed earlier for ✱60·38). -/
private theorem iota_mem_clEx {x : α} {A : Set α} (hx : x ∈ A) : ι x ∈ clEx A :=
  ⟨fun y hy => by rw [mem_unitCls.1 hy]; exact hx, x, mem_unitCls.2 rfl⟩

/-- `x ↓ y ∈ Rl ex'P` when `xPy` (✱61·6, needed earlier for ✱61·38). -/
private theorem couple_mem_rlEx {P : α → β → Prop} {x : α} {y : β} (h : P x y) :
    x ↓ y ∈ rlEx P := by
  refine ⟨fun a b hab => ?_, x, y, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hab
  exact h

/-- `Rl ex'(x ↓ y) = ι'(x ↓ y)` (✱61·37, needed earlier for ✱61·362). -/
private theorem rlEx_couple {x : α} {y : β} : rlEx (x ↓ y) = ι (x ↓ y) := by
  ext R
  show R ⪽ x ↓ y ∧ rEx R ↔ R = x ↓ y
  constructor
  · rintro ⟨h1, a, b, hab⟩
    obtain ⟨rfl, rfl⟩ := h1 a b hab
    funext c d
    apply propext
    constructor
    · exact fun h => h1 c d h
    · rintro ⟨rfl, rfl⟩
      exact hab
  · rintro rfl
    exact ⟨fun _ _ h => h, x, y, rfl, rfl⟩

/-- The class of pairs of a relation, used to reduce sub-relations to sub-classes. -/
private def pairs (R : α → β → Prop) : Set (α × β) := {p | R p.1 p.2}

private theorem pairs_eq_iff {R S : α → β → Prop} : pairs R = pairs S ↔ R = S := by
  constructor
  · intro h
    funext x y
    exact propext (Set.ext_iff.1 h (x, y))
  · rintro rfl
    rfl

private theorem pairs_sub {R S : α → β → Prop} : R ⪽ S ↔ pairs R ⊆ pairs S :=
  ⟨fun h p hp => h p.1 p.2 hp, fun h x y hxy => h (show (x, y) ∈ pairs R from hxy)⟩

private theorem pairs_couple (x : α) (y : β) : pairs (x ↓ y) = {(x, y)} := by
  ext ⟨a, b⟩
  simp [pairs, couple_apply]

private theorem pairs_rcup (P Q : α → β → Prop) : pairs (P ⊍ Q) = pairs P ∪ pairs Q :=
  Set.ext fun _ => Iff.rfl

private theorem pairs_rNull : pairs (rNull : α → β → Prop) = ∅ := by
  ext ⟨a, b⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  exact rNull_apply a b

/-- `ῐ'(ι'b)` is `b`. -/
private theorem iota_cnv_unit {x b : α} : iota˘ x (ι b) ↔ x = b :=
  ⟨fun h => (unitCls_injective (show ι b = ι x from h)).symm,
    fun h => show ι b = ι x by rw [h]⟩

/-- `α ∈ 1 . ⊃ . ∈'α = ῐ'α` (✱62·54, needed earlier for ✱62·53). -/
private theorem desc_memRel_iota_cnv {A : Set α} (h : A ∈ one) :
    Desc memRel A (fun x => Desc iota˘ A (fun y => x = y)) := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨b, fun _ => Iff.rfl, b, fun _ => iota_cnv_unit, rfl⟩

private theorem typ₁_univ (K : Set (Set α)) : typ₁ K = Set.univ := typ₀_eq_univ _

private theorem typ₂_univ (K : Set (Set (Set α))) : typ₂ K = Set.univ := typ₀_eq_univ _

private theorem typ2_univ (x : α) : typ2 x = Set.univ := typ_eq_univ _

private theorem sumCls_univ : sumCls (Set.univ : Set (Set α)) = Set.univ :=
  Set.eq_univ_of_forall fun x => ⟨Set.univ, Set.mem_univ _, Set.mem_univ x⟩

private theorem cl_univ : cl (Set.univ : Set α) = Set.univ :=
  Set.eq_univ_of_forall fun _ x _ => Set.mem_univ x

private theorem rl_cross_univ :
    rl (cross (Set.univ : Set α) (Set.univ : Set β)) = Set.univ :=
  Set.eq_univ_of_forall fun _ x y _ => ⟨Set.mem_univ x, Set.mem_univ y⟩

private theorem relT2_eq (R : Set α → β → Prop) (x : α) : relT2 R x = R := by
  funext a b
  simp [relT2, dres, typ2, typ_eq_univ]

private theorem relT2T_eq (R : Set α → β → Prop) (x : α) (y : β) : relT2T R x y = R := by
  funext a b
  simp [relT2T, dres, cres, typ2, typ_eq_univ]

private theorem relT2T2_eq (R : Set α → Set β → Prop) (x : α) (y : β) :
    relT2T2 R x y = R := by
  funext a b
  simp [relT2T2, dres, cres, typ2, typ_eq_univ]

/-- Rewrites the relative types of ✱63–✱64 (each `Set.univ` of its Lean type) and closes the
goal. -/
local macro "typ_simp" : tactic =>
  `(tactic| simp [typ_eq_univ, typ₀_eq_univ, typ₁_univ, typ₂_univ, typ2_univ, typ₀₀, typ11,
    typ22, typ₁₁, sumCls_univ, cl_univ, rl_cross_univ])

/-!
## [✱60] The sub-classes of a given class

*(Vol. 1, p. 406)*

> *Summary of* *60.
>
> Our definitions in this number are as follows:
>
> *60·01. \(\text{Cl}=\hat{\kappa}\hat{\alpha}{\kappa=\hat{\beta}(\beta\subset\alpha)} \quad\text{Df}\)
>
> This defines the relation to a class \(\alpha\) of the class of all its sub-classes.
>
> *60·02. \(\text{Cl ex}=\hat{\kappa}\hat{\alpha}\{\kappa=\hat{\beta}(\beta\subset \alpha.\exists !\beta)\} \quad\text{Df}\)
>
> This defines the relation to a class \(\alpha\) of the class of all its *existent* sub-classes, *i.e.* of all its sub-classes except \(\Lambda\). This is often required, as, for example, in the statement of Zermelo's axiom: "Given any class \(\alpha\), there is a relation \(R\) such that, if \(\beta\) is any existent sub-class of \(\alpha\), \(Rʻ\beta\) is a member of \(\beta\)," *i.e.* \[ \unicode{x201c}(\exists R):\beta\in\text{Cl ex}ʻ\alpha.\supset_{\beta}.Rʻ \beta\in\beta.\unicode{x201d} \] This axiom, or its equivalent the multiplicative axiom, plays (as will appear hereafter) an important part as the hypothesis to many propositions in cardinal arithmetic.
>
> *60·03. \(\text{Cls}^{2}=\text{Cl}ʻ\text{Cls} \quad\text{Df}\)
>
> A \(\text{Cls}^{2}\) is a class whose members are classes.
>
> …

**Lean reading.** `Cl` and `Cl ex` are the relations `graph cl` and `graph clEx` (Defs), so
`Cl'α` is the value `cl A` (`= 𝒫 A`) and `Cl ex'α` is `clEx A`; the propositions in which PM
proves that these descriptive functions exist and what they are (✱60·12–·15) keep `Desc`/`EDesc`
(Basic §5). `Cls²`, `Cls³` are `Cl'Cls`, `Cl'Cls²` at `Set (Set (Set α))` and
`Set (Set (Set (Set α)))`; their Dfs are stated with `Desc` (Defs). `ι'Λ`, `0`, `1`, `2` are
`ι Λ`, `zero`, `one`, `two` at the type of classes of `α`-things, and `Cl''κ` is the image
`Cl ʻʻ K`. In ✱60·33 the right-hand `Λ` is the null class of classes, as PM's comment says.
`β ∈ Cl'α` and `β ⊂ α` are definitionally the same in Lean, so ✱60·1·11·2·21·22 hold by
`Iff.rfl`. The
e-text prints `∃!` for `E!` in ✱60·14·15 and repeats ✱60·371 as ✱60·38.

**Status.** proved (all propositions; ✱60·01–·04 definition; ✱60·14, ✱60·15, ✱60·38 proved
(reading): transcription errors of the e-text, see their docstrings).
-/

/-- ✱60·01 (Df). \(\text{Cl}=\hat{\kappa}\hat{\alpha}\{\kappa=\hat{\beta}(\beta\subset \alpha)\} \quad\text{Df}\) -/
theorem pm60_01 : (Cl : Set (Set α) → Set α → Prop) = fun K A => K = {B | B ⊆ A} := rfl

/-- ✱60·02 (Df). \(\text{Cl ex}=\hat{\kappa}\hat{\alpha}\{\kappa=\hat{\beta}(\beta\subset \alpha.\exists !\beta)\} \quad\text{Df}\) -/
theorem pm60_02 :
    (ClEx : Set (Set α) → Set α → Prop) = fun K A => K = {B | B ⊆ A ∧ B.Nonempty} := rfl

/-- ✱60·03 (Df). \(\text{Cls}^{2}=\text{Cl}ʻ\text{Cls} \quad\text{Df}\) -/
theorem pm60_03 : Desc Cl Cls (fun K => (Cls2 : Set (Set (Set α))) = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱60·04 (Df). \(\text{Cls}^{3} = \text{Cl}ʻ\text{Cls}^{2} \quad\text{Df}\) -/
theorem pm60_04 : Desc Cl Cls2 (fun K => (Cls3 : Set (Set (Set (Set α)))) = K) :=
  (desc_graph _ _ _).2 rfl

/-- ✱60·1. \(\vdash:\kappa\,\text{Cl}\, \alpha.\equiv.\kappa=\hat{\beta}(\beta\subset \alpha) \quad\text{[*21·3.(*60·01)]}\) -/
theorem pm60_1 {K : Set (Set α)} {A : Set α} : Cl K A ↔ K = {B | B ⊆ A} := Iff.rfl

/-- ✱60·11. \(\vdash:\kappa\,\text{Cl ex}\, \alpha.\equiv.\kappa=\hat{\beta}(\beta\subset \alpha.\exists !\beta) \quad\text{[*21·3.(*60·02)]}\) -/
theorem pm60_11 {K : Set (Set α)} {A : Set α} : ClEx K A ↔ K = {B | B ⊆ A ∧ B.Nonempty} :=
  Iff.rfl

/-- ✱60·12. \(\vdash.\text{Cl}ʻ \alpha=\hat{\beta}(\beta\subset \alpha) \quad\text{[*30·3.*60·1]}\) -/
theorem pm60_12 {A : Set α} : Desc Cl A (fun K => K = {B | B ⊆ A}) := (desc_Cl _ _).2 rfl

/-- ✱60·13. \(\vdash.\text{Cl ex}ʻ \alpha=\hat{\beta}(\beta\subset \alpha.\exists !\beta) \quad\text{[*30·3.*60·11]}\) -/
theorem pm60_13 {A : Set α} : Desc ClEx A (fun K => K = {B | B ⊆ A ∧ B.Nonempty}) :=
  (desc_ClEx _ _).2 rfl

/-- ✱60·14. \(\vdash.\exists !\text{Cl}ʻ \alpha \quad\text{[*60·12.*14·21]}\)

**Status.** proved (reading): transcription error: the e-text prints `∃!Cl'α` for `E!Cl'α`.
The proof cites ✱14·21 (`ψ(℩x)(φx) . ⊃ . E!(℩x)(φx)`), ✱60·53 and ✱60·55 cite ✱60·14 for the
existence of `Cl'α`, and `∃!Cl'α` is ✱60·31. -/
theorem pm60_14 {A : Set α} : EDesc Cl A := EDesc_graph cl A

/-- ✱60·15. \(\vdash.\exists !\text{Cl ex}ʻ \alpha \quad\text{[*60·13.*14·21]}\)

**Status.** proved (reading): transcription error `∃!Cl ex'α` for `E!Cl ex'α`, as in ✱60·14
(the proof cites ✱14·21). As printed it would be false for `α = Λ` (✱60·33, ✱60·361). -/
theorem pm60_15 {A : Set α} : EDesc ClEx A := EDesc_graph clEx A

/-- ✱60·2. \(\vdash:\beta\in\text{Cl}ʻ \alpha.\equiv.\beta\subset \alpha \quad\text{[*60·12.*20·33]}\) -/
theorem pm60_2 {A B : Set α} : B ∈ cl A ↔ B ⊆ A := Iff.rfl

/-- ✱60·21. \(\vdash:\beta\in\text{Cl ex}ʻ \alpha.\equiv.\beta\subset \alpha.\exists !\beta \quad\text{[*60·13.*20·33]}\) -/
theorem pm60_21 {A B : Set α} : B ∈ clEx A ↔ B ⊆ A ∧ B.Nonempty := Iff.rfl

/-- ✱60·22. \(\vdash:\beta\in\text{Cl ex}ʻ \alpha.\equiv.\beta\in\text{Cl}ʻ \alpha.\exists !\beta \quad\text{[*60·2·21]}\) -/
theorem pm60_22 {A B : Set α} : B ∈ clEx A ↔ B ∈ cl A ∧ B.Nonempty := Iff.rfl

/-- ✱60·23. \(\vdash:\beta\in\text{Cl ex}ʻ \alpha.\equiv.\beta\in\text{Cl}ʻ \alpha-\iotaʻ \Lambda \quad\text{[*60·22.*53·52]}\) -/
theorem pm60_23 {A B : Set α} : B ∈ clEx A ↔ B ∈ cl A \ ι Λ := by
  show B ⊆ A ∧ B.Nonempty ↔ B ⊆ A ∧ ¬ B = Λ
  rw [Null_eq_empty]
  exact and_congr_right fun _ => Set.nonempty_iff_ne_empty

/-- ✱60·24. \(\vdash.\text{Cl ex}ʻ \alpha=\text{Cl}ʻ \alpha-\iotaʻ\Lambda \quad\text{[*60·23.*20·43]}\) -/
theorem pm60_24 {A : Set α} : clEx A = cl A \ ι Λ := Set.ext fun _ => pm60_23

/-- ✱60·3. \(\vdash.\Lambda\in\text{Cl}ʻ \alpha \quad\text{[*24·12.*60·2]}\) -/
theorem pm60_3 {A : Set α} : Λ ∈ cl A := by
  show Λ ⊆ A
  rw [Null_eq_empty]
  exact Set.empty_subset A

/-- ✱60·31. \(\vdash.\exists !\text{Cl}ʻ \alpha \quad\text{[*60·3.*10·24]}\) -/
theorem pm60_31 {A : Set α} : (cl A).Nonempty := ⟨Λ, pm60_3⟩

/-- ✱60·32. \(\vdash.\text{Cl}ʻ\Lambda=\iotaʻ\Lambda\) -/
theorem pm60_32 : cl (Λ : Set α) = ι Λ := by
  ext B
  show B ⊆ Λ ↔ B = Λ
  rw [Null_eq_empty, Set.subset_empty_iff]

/-- ✱60·321. \(\vdash:\alpha=\Lambda.\equiv.\text{Cl}ʻ \alpha=\iotaʻ \alpha\) -/
theorem pm60_321 {A : Set α} : A = Λ ↔ cl A = ι A := by
  constructor
  · rintro rfl
    exact pm60_32
  · intro h
    have h3 : (Λ : Set α) ∈ ι A := by
      rw [← h]
      exact pm60_3
    exact (mem_unitCls.1 h3).symm

/-- ✱60·33. \(\vdash.\text{Cl ex}ʻ\Lambda=\Lambda\cap\text{Cls}\) -/
theorem pm60_33 : clEx (Λ : Set α) = (Λ : Set (Set α)) ∩ Cls := by
  ext B
  constructor
  · rintro ⟨h1, x, hx⟩
    have h2 : x ∈ (Λ : Set α) := h1 hx
    rw [Null_eq_empty] at h2
    exact absurd h2 (Set.notMem_empty x)
  · rintro ⟨h, -⟩
    rw [Null_eq_empty] at h
    exact absurd h (Set.notMem_empty B)

/-- ✱60·34. \(\vdash.\alpha\in\text{Cl}ʻ\alpha \quad\text{[*22·42.*60·2]}\) -/
theorem pm60_34 {A : Set α} : A ∈ cl A := fun _ h => h

/-- ✱60·35. \(\vdash:\exists !\alpha.\supset.\alpha\in\text{Cl ex}ʻ\alpha \quad\text{[*60·22·34]}\) -/
theorem pm60_35 {A : Set α} : A.Nonempty → A ∈ clEx A := fun h => ⟨fun _ hx => hx, h⟩

/-- ✱60·36. \(\vdash:\exists !\alpha.\supset.\exists !\text{Cl ex}ʻ\alpha \quad\text{[*60·35.*10·24]}\) -/
theorem pm60_36 {A : Set α} : A.Nonempty → (clEx A).Nonempty := fun h => ⟨A, pm60_35 h⟩

/-- ✱60·361. \(\vdash:\exists !\alpha.\equiv.\exists !\text{Cl ex}ʻ\alpha \quad\text{[*60·36·33]}\) -/
theorem pm60_361 {A : Set α} : A.Nonempty ↔ (clEx A).Nonempty :=
  ⟨pm60_36, fun ⟨_, hB, x, hx⟩ => ⟨x, hB hx⟩⟩

/-- ✱60·362. \(\vdash.\text{Cl}ʻ \iotaʻ x=\iotaʻ \Lambda\cup \iotaʻ \iotaʻ x \quad\text{[*51·401.*60·2]}\) -/
theorem pm60_362 {x : α} : cl (ι x) = ι Λ ∪ ι (ι x) := by
  ext B
  show B ⊆ ι x ↔ B = Λ ∨ B = ι x
  rw [Null_eq_empty, unitCls_eq_singleton, Set.subset_singleton_iff_eq]

/-- ✱60·37. \(\vdash.\text{Cl ex}ʻ \iotaʻ x=\iotaʻ \iotaʻ x\) -/
theorem pm60_37 {x : α} : clEx (ι x) = ι (ι x) := by
  ext B
  show B ⊆ ι x ∧ B.Nonempty ↔ B = ι x
  rw [unitCls_eq_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact h2.subset_singleton_iff.1 h1
  · rintro rfl
    exact ⟨subset_rfl, Set.singleton_nonempty x⟩

/-- ✱60·371. \(\vdash:\alpha\in 1.\supset.\text{Cl}ʻ\alpha\subset 0\cup 1\) -/
theorem pm60_371 {A : Set α} : A ∈ one → cl A ⊆ zero ∪ one := by
  rintro ⟨x, rfl⟩ B hB
  rw [pm60_362] at hB
  rcases hB with h | h
  · exact Set.mem_union_left _ h
  · exact Set.mem_union_right _ ⟨x, h⟩

/-- ✱60·38. \(\vdash:\alpha\in 1.\supset.\text{Cl}ʻ \alpha\subset 0\cup 1\)

**Status.** proved (reading): transcription error: the e-text repeats the enunciation of
✱60·371. The demonstration proves `α ∈ 1 . ⊃ . Cl ex'α = ι'α` (its step (1)) and the converse
(its step (4)), i.e. `⊢ : α ∈ 1 . ≡ . Cl ex'α = ι'α`, which is stated here (the printed form
is `pm60_371`). -/
theorem pm60_38 {A : Set α} : A ∈ one ↔ clEx A = ι A := by
  constructor
  · rintro ⟨x, rfl⟩
    exact pm60_37
  · intro h
    have hA : A ∈ clEx A := by
      rw [h]
      exact mem_unitCls.2 rfl
    obtain ⟨x, hx⟩ := hA.2
    have h2 : ι x ∈ clEx A := iota_mem_clEx hx
    rw [h] at h2
    exact ⟨x, (mem_unitCls.1 h2).symm⟩

/-- ✱60·39. \(\vdash.\text{Cl}ʻ (\iotaʻ x\cup \iotaʻ y)=\iotaʻ\Lambda\cup \iotaʻ\iotaʻ x\cup \iotaʻ\iotaʻ y\cup \iotaʻ (\iotaʻ x\cup \iotaʻ y) \quad[\text{*54·4.*60·2}]\) -/
theorem pm60_39 {x y : α} :
    cl (ι x ∪ ι y) = ι Λ ∪ ι (ι x) ∪ ι (ι y) ∪ ι (ι x ∪ ι y) := by
  ext B
  show B ⊆ ι x ∪ ι y ↔ ((B = Λ ∨ B = ι x) ∨ B = ι y) ∨ B = ι x ∪ ι y
  rw [Null_eq_empty, unitCls_eq_singleton, unitCls_eq_singleton, Set.singleton_union,
    Set.subset_pair_iff_eq]
  tauto

/-- ✱60·391. \(\vdash:\alpha\in 2.\supset.\text{Cl}ʻ\alpha\subset 0\cup 1\cup 2 \quad[\text{*54·411.*60·2}]\) -/
theorem pm60_391 {A : Set α} : A ∈ two → cl A ⊆ zero ∪ one ∪ two := by
  rintro ⟨x, y, hxy, rfl⟩ B hB
  rw [pm60_39] at hB
  rcases hB with ((h | h) | h) | h
  · exact Set.mem_union_left _ (Set.mem_union_left _ h)
  · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨x, h⟩)
  · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨y, h⟩)
  · exact Set.mem_union_right _ ⟨x, y, hxy, h⟩

/-- ✱60·4. \(\vdash:\beta\in\text{Cl}ʻ\alpha.\gamma\subset\beta.\supset.\gamma\in\text{Cl}ʻ\alpha \quad[\text{*60·2.*22·44}]\) -/
theorem pm60_4 {A B G : Set α} : B ∈ cl A ∧ G ⊆ B → G ∈ cl A := fun ⟨h1, h2⟩ =>
  show G ⊆ A from Set.Subset.trans h2 h1

/-- ✱60·41. \(\vdash:\beta\in\text{Cl}ʻ\alpha.\supset.\beta\cap \gamma\in\text{Cl}ʻ\alpha \quad[\text{*60·4.*22·43}]\) -/
theorem pm60_41 {A B G : Set α} : B ∈ cl A → B ∩ G ∈ cl A := fun h _ hz => h hz.1

/-- ✱60·42. \(\vdash:\beta\in\text{Cl}ʻ\alpha.\gamma\subset\beta.\exists !\gamma.\supset.\gamma\in\text{Cl ex}ʻ\alpha \quad[\text{*60·4·22}]\) -/
theorem pm60_42 {A B G : Set α} : (B ∈ cl A ∧ G ⊆ B) ∧ G.Nonempty → G ∈ clEx A :=
  fun ⟨h, hG⟩ => ⟨pm60_4 h, hG⟩

/-- ✱60·43. \(\vdash:\beta,\gamma\in\text{Cl}ʻ\alpha.\equiv.\beta\cup \gamma\in\text{Cl}ʻ\alpha \quad[\text{*22·59.*60·2}]\) -/
theorem pm60_43 {A B G : Set α} : B ∈ cl A ∧ G ∈ cl A ↔ B ∪ G ∈ cl A := by
  show B ⊆ A ∧ G ⊆ A ↔ B ∪ G ⊆ A
  exact Set.union_subset_iff.symm

/-- ✱60·44. \(\vdash:\beta\in\text{Cl}ʻ\alpha.\gamma\in\text{Cl ex}ʻ\alpha.\supset.\beta\cup \gamma\in\text{Cl ex}ʻ\alpha \quad[\text{*60·43.*24·56.*60·22}]\) -/
theorem pm60_44 {A B G : Set α} : B ∈ cl A ∧ G ∈ clEx A → B ∪ G ∈ clEx A := by
  rintro ⟨hB, hG, z, hz⟩
  exact ⟨Set.union_subset hB hG, z, Set.mem_union_right _ hz⟩

/-- ✱60·45. \(\vdash:\rho\in\text{Cl}ʻ (\alpha\cup\beta).\equiv.(\exists \gamma,\delta).\gamma\in\text{Cl}ʻ \alpha.\delta\in\text{Cl}ʻ \beta.\rho=\gamma\cup\delta\) -/
theorem pm60_45 {A B X : Set α} :
    X ∈ cl (A ∪ B) ↔ ∃ G H, (G ∈ cl A ∧ H ∈ cl B) ∧ X = G ∪ H := by
  constructor
  · intro h
    have h' : X ⊆ A ∪ B := h
    refine ⟨X ∩ A, X ∩ B, ⟨fun z hz => hz.2, fun z hz => hz.2⟩, ?_⟩
    ext z
    constructor
    · intro hz
      rcases h' hz with hA | hB
      · exact Set.mem_union_left _ ⟨hz, hA⟩
      · exact Set.mem_union_right _ ⟨hz, hB⟩
    · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
  · rintro ⟨G, H, ⟨hG, hH⟩, rfl⟩
    show G ∪ H ⊆ A ∪ B
    exact Set.union_subset_union hG hH

/-- ✱60·5. \(\vdash.sʻ\text{Cl}ʻ \alpha=\alpha\) -/
theorem pm60_5 {A : Set α} : sumCls (cl A) = A := by
  ext x
  exact ⟨fun ⟨B, hB, hx⟩ => hB hx, fun hx => ⟨A, fun _ h => h, hx⟩⟩

/-- ✱60·501. \(\vdash.sʻ\text{Cl ex}ʻ \alpha=\alpha\) -/
theorem pm60_501 {A : Set α} : sumCls (clEx A) = A := by
  ext x
  exact ⟨fun ⟨B, hB, hx⟩ => hB.1 hx, fun hx => ⟨A, ⟨fun _ h => h, x, hx⟩, hx⟩⟩

/-- ✱60·51. \(\vdash.pʻ\text{Cl}ʻ\alpha=\Lambda \quad[\text{*40·22.*60·3}]\) -/
theorem pm60_51 {A : Set α} : prodCls (cl A) = Λ := by
  ext x
  rw [Null_eq_empty]
  exact ⟨fun h => h ∅ (Set.empty_subset A), fun h => absurd h (Set.notMem_empty x)⟩

/-- ✱60·52. \(\vdash:sʻ \kappa\subset\beta.\equiv.\kappa\subset \text{Cl}ʻ \beta \quad[\text{*40·151.*60·2}]\) -/
theorem pm60_52 {K : Set (Set α)} {B : Set α} : sumCls K ⊆ B ↔ K ⊆ cl B :=
  ⟨fun h A hA _ hx => h ⟨A, hA, hx⟩, fun h _ ⟨_, hA, hx⟩ => h hA hx⟩

/-- ✱60·53. \(\vdash:\beta\subset pʻ \kappa.\equiv.\beta\in pʻ\text{Cl}ʻʻ\kappa\) -/
theorem pm60_53 {K : Set (Set α)} {B : Set α} : B ⊆ prodCls K ↔ B ∈ prodCls (Cl ʻʻ K) := by
  constructor
  · rintro h X ⟨G, hG, hX⟩
    rw [show X = cl G from hX]
    exact fun x hx => h hx G hG
  · intro h x hx G hG
    exact (h (cl G) ⟨G, hG, rfl⟩ : B ⊆ G) hx

/-- ✱60·54. \(\vdash.\text{Cl}ʻ pʻ \kappa=pʻ\text{Cl}ʻʻ\kappa \quad[\text{*60·53·2}]\) -/
theorem pm60_54 {K : Set (Set α)} : cl (prodCls K) = prodCls (Cl ʻʻ K) :=
  Set.ext fun _ => pm60_53

/-- ✱60·55. \(\vdash:\text{Cl}ʻ \alpha=\text{Cl}ʻ\beta.\equiv.\alpha=\beta\) -/
theorem pm60_55 {A B : Set α} : cl A = cl B ↔ A = B := by
  constructor
  · intro h
    have h2 := congrArg sumCls h
    rwa [pm60_5, pm60_5] at h2
  · rintro rfl
    rfl

/-- ✱60·56. \(\vdash:\text{Cl ex}ʻ\alpha=\text{Cl ex}ʻ\beta.\equiv.\alpha=\beta \quad[\text{Proof as in *60·55}]\) -/
theorem pm60_56 {A B : Set α} : clEx A = clEx B ↔ A = B := by
  constructor
  · intro h
    have h2 := congrArg sumCls h
    rwa [pm60_501, pm60_501] at h2
  · rintro rfl
    rfl

/-- ✱60·57. \(\vdash.\kappa\subset\text{Cl}ʻ sʻ\kappa\) -/
theorem pm60_57 {K : Set (Set α)} : K ⊆ cl (sumCls K) := fun A hA _ hx => ⟨A, hA, hx⟩

/-- ✱60·6. \(\vdash:x\in\alpha.\supset.\iotaʻ x\in\text{Cl ex}ʻ\alpha \quad[\text{*51·2·161.*60·21}]\) -/
theorem pm60_6 {x : α} {A : Set α} : x ∈ A → ι x ∈ clEx A := iota_mem_clEx

/-- ✱60·61. \(\vdash.\iotaʻʻ \alpha\subset\text{Cl ex}ʻ \alpha \quad[\text{*37·61.*51·12.*60·6}]\) -/
theorem pm60_61 {A : Set α} : iota ʻʻ A ⊆ clEx A := by
  rintro X ⟨y, hy, hX⟩
  rw [show X = ι y from hX]
  exact pm60_6 hy

/-- ✱60·62. \(\vdash:x,y\in\alpha.\supset.\iotaʻ x\cup \iotaʻ y\in\text{Cl ex}ʻ \alpha \quad[\text{*60·6·44}]\) -/
theorem pm60_62 {x y : α} {A : Set α} : x ∈ A ∧ y ∈ A → ι x ∪ ι y ∈ clEx A :=
  fun ⟨hx, hy⟩ => pm60_44 ⟨(pm60_6 hx).1, pm60_6 hy⟩

/-- ✱60·7. \(\vdash.\text{Cl}ʻ \alpha\in\text{Cls}^{2}\) -/
theorem pm60_7 {A : Set α} : cl A ∈ Cls2 := fun B _ => by
  rw [Cls_eq_univ]
  exact Set.mem_univ B

/-- ✱60·71. \(\vdash.\text{Cls}^{2}=\text{Cl}ʻ\text{Cls} \quad[\text{(*60·03)}]\) -/
theorem pm60_71 : (Cls2 : Set (Set (Set α))) = cl Cls := rfl

/-- ✱60·72. \(\vdash.\text{Cls}^{3}=\text{Cl}ʻ\text{Cls}^{2} \quad[\text{(*60·04)}]\) -/
theorem pm60_72 : (Cls3 : Set (Set (Set (Set α)))) = cl Cls2 := rfl

/-!
## [✱61] The sub-relations of a given relation

*(Vol. 1, p. 412)*

> *Summary of* *61.
>
> The propositions of this number (except that *61·371·372·373 imperfectly correspond to *60·371) are the analogues of those with the same decimal part in *60. Proofs are omitted, as they are exactly analogous to those in *60. There are very few subsequent references to the propositions of this number.

**Lean reading.** The analogues for relations of ✱60: `Rl` and `Rl ex` are `graph rl` and
`graph rlEx`, so `Rl'P` is `rl P` and `Rl ex'P` is `rlEx P` (`R ∈ Rl'P` is `R ⪽ P`); ✱61·12–·15
keep `Desc`/`EDesc`, and the Dfs of `Rel²`, `Rel³` are stated with `Desc` (Defs), the two `Rel`s
of `Rel ↑ Rel` being of independent types. `Λ̇`, `x ↓ y`, `2̇`, `2_r`, `0_r` are `rNull`,
`x ↓ y`, `twoDot`, `two_r`, `zero_r`; `ṡ'λ`, `ṗ'λ` are `sumRel L`, `prodRel L`; `Rl''λ` is
`Rl ʻʻ L`. Relations are heterogeneous except in ✱61·373 (`2_r` needs `x ≠ y`). The finite
cases ✱61·362·39 are proved by passing to the class of pairs of a relation. The e-text prints
`∃!` for `E!` in ✱61·14·15, repeats ✱61·3 as ✱61·31 and prints `2` for `2̇` in ✱61·391.

**Status.** proved (all propositions; ✱61·01–·04 definition; ✱61·14, ✱61·15, ✱61·31, ✱61·391
proved (reading): transcription errors of the e-text, see their docstrings).
-/

/-- ✱61·01 (Df). \(\text{Rl}=\hat{\lambda}\hat{P}\{\lambda=\hat{R}(R\unicode{x2abd}P)\} \quad\text{Df}\) -/
theorem pm61_01 :
    (Rl : Set (α → β → Prop) → (α → β → Prop) → Prop) = fun L P => L = {R | R ⪽ P} := rfl

/-- ✱61·02 (Df). \(\text{Rl ex}=\hat{\lambda}\hat{P}\{\lambda=\hat{R}(R\unicode{x2abd}P.\dot{\exists}!R)\} \quad\text{Df}\) -/
theorem pm61_02 : (RlEx : Set (α → β → Prop) → (α → β → Prop) → Prop) =
    fun L P => L = {R | R ⪽ P ∧ rEx R} := rfl

/-- ✱61·03 (Df). \(\text{Rel}^{2}=\text{Rl}ʻ (\text{Rel}\uparrow\text{Rel}) \quad\text{Df}\) -/
theorem pm61_03 : Desc Rl (cross Rel Rel)
    (fun L => (Rel2 : Set ((α → β → Prop) → (γ → δ → Prop) → Prop)) = L) :=
  (desc_graph _ _ _).2 rfl

/-- ✱61·04 (Df). \(\text{Rel}^{3}=\text{Rl}ʻ (\text{Rel}^{2}\uparrow\text{Rel}^{2}) \quad\text{Df}\) -/
theorem pm61_04 {ε : Type v'} {ζ : Type w'} {η : Type u''} {θ : Type v''} :
    Desc Rl (cross Rel2 Rel2)
      (fun L => (Rel3 : Set (((α → β → Prop) → (γ → δ → Prop) → Prop) →
        ((ε → ζ → Prop) → (η → θ → Prop) → Prop) → Prop)) = L) :=
  (desc_graph _ _ _).2 rfl

/-- ✱61·1. \(\vdash:\lambda\text{Rl}\, P.\equiv.\lambda=\hat{R}(R\unicode{x2abd}P)\) -/
theorem pm61_1 {L : Set (α → β → Prop)} {P : α → β → Prop} : Rl L P ↔ L = {R | R ⪽ P} :=
  Iff.rfl

/-- ✱61·11. \(\vdash:\lambda\text{Rl ex}\, P.\equiv.\lambda=\hat{R}(R\unicode{x2abd}P.\dot{\exists}!R)\) -/
theorem pm61_11 {L : Set (α → β → Prop)} {P : α → β → Prop} :
    RlEx L P ↔ L = {R | R ⪽ P ∧ rEx R} := Iff.rfl

/-- ✱61·12. \(\vdash.\text{Rl}ʻ P=\hat{R}(R\unicode{x2abd}P)\) -/
theorem pm61_12 {P : α → β → Prop} : Desc Rl P (fun L => L = {R | R ⪽ P}) :=
  (desc_Rl _ _).2 rfl

/-- ✱61·13. \(\vdash.\text{Rl ex}ʻ P=\hat{R}(R\unicode{x2abd}P.\dot{\exists}!R)\) -/
theorem pm61_13 {P : α → β → Prop} : Desc RlEx P (fun L => L = {R | R ⪽ P ∧ rEx R}) :=
  (desc_RlEx _ _).2 rfl

/-- ✱61·14. \(\vdash.\exists !\text{Rl}ʻ P\)

**Status.** proved (reading): transcription error `∃!Rl'P` for `E!Rl'P`, as in ✱60·14 (✱61
gives the analogues of ✱60 with the same decimals; `∃!Rl'P` is ✱61·31). -/
theorem pm61_14 {P : α → β → Prop} : EDesc Rl P := EDesc_graph rl P

/-- ✱61·15. \(\vdash.\exists !\text{Rl ex}ʻ P\)

**Status.** proved (reading): transcription error `∃!Rl ex'P` for `E!Rl ex'P`, as in ✱60·15;
as printed it would be false for `P = Λ̇` (✱61·33, ✱61·361). -/
theorem pm61_15 {P : α → β → Prop} : EDesc RlEx P := EDesc_graph rlEx P

/-- ✱61·2. \(\vdash:R\in\text{Rl}ʻP.\equiv.R\unicode{x2abd}P\) -/
theorem pm61_2 {P R : α → β → Prop} : R ∈ rl P ↔ R ⪽ P := Iff.rfl

/-- ✱61·21. \(\vdash:R\in\text{Rl ex}ʻ P.\equiv.R\unicode{x2abd}P.\dot{\exists}!R\) -/
theorem pm61_21 {P R : α → β → Prop} : R ∈ rlEx P ↔ R ⪽ P ∧ rEx R := Iff.rfl

/-- ✱61·22. \(\vdash:R\in\text{Rl ex}ʻ P.\equiv.R\in\text{Rl}ʻ P.\dot{\exists}!R\) -/
theorem pm61_22 {P R : α → β → Prop} : R ∈ rlEx P ↔ R ∈ rl P ∧ rEx R := Iff.rfl

/-- ✱61·23. \(\vdash:R\in\text{Rl ex}ʻ P.\equiv.R\in\text{Rl}ʻ P-\iotaʻ\dot{\Lambda}\) -/
theorem pm61_23 {P R : α → β → Prop} : R ∈ rlEx P ↔ R ∈ rl P \ ι rNull := by
  show R ⪽ P ∧ rEx R ↔ R ⪽ P ∧ ¬ R = rNull
  rw [eq_rNull_iff, not_not]

/-- ✱61·24. \(\vdash.\text{Rl ex}ʻ P=\text{Rl}ʻ P-\iotaʻ\dot{\Lambda}\) -/
theorem pm61_24 {P : α → β → Prop} : rlEx P = rl P \ ι rNull := Set.ext fun _ => pm61_23

/-- ✱61·3. \(\vdash.\dot{\Lambda}\in\text{Rl}ʻ P\) -/
theorem pm61_3 {P : α → β → Prop} : rNull ∈ rl P := fun x y h => (rNull_apply x y h).elim

/-- ✱61·31. \(\vdash.\dot{\Lambda}\in\text{Rl}ʻ P\)

**Status.** proved (reading): transcription error: the e-text repeats ✱61·3 (`Λ̇ ∈ Rl'P`). By
the Summary of ✱61, ✱61·31 is the analogue of ✱60·31 `∃!Cl'α`, i.e. `∃!Rl'P`, which is stated
here (it follows from ✱61·3 as ✱60·31 from ✱60·3). -/
theorem pm61_31 {P : α → β → Prop} : (rl P).Nonempty := ⟨rNull, pm61_3⟩

/-- ✱61·32. \(\vdash.\text{Rl}ʻ\dot{\Lambda}=\iotaʻ\dot{\Lambda}\) -/
theorem pm61_32 : rl (rNull : α → β → Prop) = ι rNull := by
  ext R
  show R ⪽ rNull ↔ R = rNull
  rw [eq_rNull_iff]
  exact ⟨fun h ⟨x, y, hr⟩ => rNull_apply x y (h x y hr), fun h x y hr => (h ⟨x, y, hr⟩).elim⟩

/-- ✱61·321. \(\vdash:P=\dot{\Lambda}.\equiv.\text{Rl}ʻ P=\iotaʻ P\) -/
theorem pm61_321 {P : α → β → Prop} : P = rNull ↔ rl P = ι P := by
  constructor
  · rintro rfl
    exact pm61_32
  · intro h
    have h3 : rNull ∈ ι P := by
      rw [← h]
      exact pm61_3
    exact (mem_unitCls.1 h3).symm

/-- ✱61·33. \(\vdash.\text{Rl ex}ʻ\dot{\Lambda}=\Lambda\cap\text{Rel}\) -/
theorem pm61_33 : rlEx (rNull : α → β → Prop) = (Λ : Set (α → β → Prop)) ∩ Rel := by
  ext R
  constructor
  · rintro ⟨h1, x, y, h⟩
    exact (rNull_apply x y (h1 x y h)).elim
  · rintro ⟨h, -⟩
    exact (h rfl).elim

/-- ✱61·34. \(\vdash.P\in\text{Rl}ʻ P\) -/
theorem pm61_34 {P : α → β → Prop} : P ∈ rl P := fun _ _ h => h

/-- ✱61·35. \(\vdash:\dot{\exists}!P.\supset.P\in\text{Rl ex}ʻ P\) -/
theorem pm61_35 {P : α → β → Prop} : rEx P → P ∈ rlEx P := fun h => ⟨fun _ _ h => h, h⟩

/-- ✱61·36. \(\vdash:\dot{\exists}!P.\supset.\exists !\text{Rl ex}ʻ P\) -/
theorem pm61_36 {P : α → β → Prop} : rEx P → (rlEx P).Nonempty := fun h => ⟨P, pm61_35 h⟩

/-- ✱61·361. \(\vdash:\dot{\exists}!P.\equiv.\exists !\text{Rl ex}ʻ P\) -/
theorem pm61_361 {P : α → β → Prop} : rEx P ↔ (rlEx P).Nonempty :=
  ⟨pm61_36, fun ⟨_, hR, x, y, h⟩ => ⟨x, y, hR x y h⟩⟩

/-- ✱61·362. \(\vdash.\text{Rl}ʻ (x\downarrow y)=\iotaʻ\dot{\Lambda}\cup \iotaʻ (x\downarrow y)\) -/
theorem pm61_362 {x : α} {y : β} : rl (x ↓ y) = ι rNull ∪ ι (x ↓ y) := by
  ext R
  show R ⪽ x ↓ y ↔ R = rNull ∨ R = x ↓ y
  constructor
  · intro h
    by_cases hR : rEx R
    · have h2 : R ∈ rlEx (x ↓ y) := ⟨h, hR⟩
      rw [rlEx_couple] at h2
      exact Or.inr h2
    · exact Or.inl (eq_rNull_iff.2 hR)
  · rintro (rfl | rfl)
    · exact pm61_3 (P := x ↓ y)
    · exact pm61_34 (P := x ↓ y)

/-- ✱61·37. \(\vdash.\text{Rl ex}ʻ (x\downarrow y)=\iotaʻ (x\downarrow y)\) -/
theorem pm61_37 {x : α} {y : β} : rlEx (x ↓ y) = ι (x ↓ y) := rlEx_couple

/-- ✱61·371. \(\vdash:R\in\dot{2}.\supset.\text{Rl}ʻ R=\iotaʻ\dot{\Lambda}\cup \iotaʻ R\) -/
theorem pm61_371 {R : α → β → Prop} : R ∈ twoDot → rl R = ι rNull ∪ ι R := by
  rintro ⟨x, y, rfl⟩
  exact pm61_362

/-- ✱61·372. \(\vdash:R\in\dot{2}.\supset.\text{Rl}ʻ R\subset 0_{r}\cup\dot{2}\) -/
theorem pm61_372 {R : α → β → Prop} : R ∈ twoDot → rl R ⊆ zero_r ∪ twoDot := by
  rintro ⟨x, y, rfl⟩ S hS
  rw [pm61_362] at hS
  rcases hS with h | h
  · exact Set.mem_union_left _ h
  · exact Set.mem_union_right _ ⟨x, y, h⟩

/-- ✱61·373. \(\vdash:R\in 2_{r}.\supset.\text{Rl}ʻ R\subset 0_{r}\cup 2_{r}\) -/
theorem pm61_373 {R : α → α → Prop} : R ∈ two_r → rl R ⊆ zero_r ∪ two_r := by
  rintro ⟨x, y, hxy, rfl⟩ S hS
  rw [pm61_362] at hS
  rcases hS with h | h
  · exact Set.mem_union_left _ h
  · exact Set.mem_union_right _ ⟨x, y, hxy, h⟩

/-- ✱61·38. \(\vdash:R\in\dot{2}.\equiv.\text{Rl ex}ʻ R=\iotaʻ R\) -/
theorem pm61_38 {R : α → β → Prop} : R ∈ twoDot ↔ rlEx R = ι R := by
  constructor
  · rintro ⟨x, y, rfl⟩
    exact rlEx_couple
  · intro h
    have hR : R ∈ rlEx R := by
      rw [h]
      exact mem_unitCls.2 rfl
    obtain ⟨x, y, hxy⟩ := hR.2
    have h2 : x ↓ y ∈ rlEx R := couple_mem_rlEx hxy
    rw [h] at h2
    exact ⟨x, y, (mem_unitCls.1 h2).symm⟩

/-- ✱61·39. \(\vdash.\text{Rl}ʻ (x\downarrow y\unicode{x228d}z\downarrow w)=\iotaʻ\dot{\Lambda}\cup \iotaʻ(x\downarrow y)\cup \iotaʻ (z\downarrow w)\cup \iotaʻ(x\downarrow y\unicode{x228d}z\downarrow w)\) -/
theorem pm61_39 {x z : α} {y w : β} :
    rl (x ↓ y ⊍ z ↓ w) = ι rNull ∪ ι (x ↓ y) ∪ ι (z ↓ w) ∪ ι (x ↓ y ⊍ z ↓ w) := by
  ext R
  show R ⪽ x ↓ y ⊍ z ↓ w ↔ ((R = rNull ∨ R = x ↓ y) ∨ R = z ↓ w) ∨ R = x ↓ y ⊍ z ↓ w
  have e1 : R = rNull ↔ pairs R = ∅ := by rw [← pairs_rNull, pairs_eq_iff]
  have e2 : R = x ↓ y ↔ pairs R = {(x, y)} := by rw [← pairs_couple, pairs_eq_iff]
  have e3 : R = z ↓ w ↔ pairs R = {(z, w)} := by rw [← pairs_couple, pairs_eq_iff]
  have e4 : R = x ↓ y ⊍ z ↓ w ↔ pairs R = {(x, y), (z, w)} := by
    rw [← Set.singleton_union, ← pairs_couple, ← pairs_couple, ← pairs_rcup, pairs_eq_iff]
  rw [e1, e2, e3, e4, pairs_sub, pairs_rcup, pairs_couple, pairs_couple, Set.singleton_union,
    Set.subset_pair_iff_eq]
  tauto

/-- ✱61·391. \(\vdash:P,Q\in 2.\supset.\text{Rl}ʻ (P\unicode{x228d}Q)=\iotaʻ\dot{\Lambda}\cup \iotaʻ P\cup \iotaʻ Q\cup \iotaʻ (P\unicode{x228d}Q)\)

**Status.** proved (reading): transcription error: the e-text prints `P, Q ∈ 2`, which is not
significant for relations (`2` is a class of classes, ✱54·02); read `2̇` (couples, ✱56·01),
under which the proposition is ✱61·39 for arbitrary couples `P`, `Q`. -/
theorem pm61_391 {P Q : α → β → Prop} :
    P ∈ twoDot ∧ Q ∈ twoDot → rl (P ⊍ Q) = ι rNull ∪ ι P ∪ ι Q ∪ ι (P ⊍ Q) := by
  rintro ⟨⟨x, y, rfl⟩, ⟨z, w, rfl⟩⟩
  exact pm61_39

/-- ✱61·4. \(\vdash:Q\in\text{Rl}ʻ P.R\unicode{x2abd}Q.\supset.R\in\text{Rl}ʻ P\) -/
theorem pm61_4 {P Q R : α → β → Prop} : Q ∈ rl P ∧ R ⪽ Q → R ∈ rl P :=
  fun ⟨h1, h2⟩ x y h => h1 x y (h2 x y h)

/-- ✱61·41. \(\vdash:Q\in\text{Rl}ʻ P.\supset.Q\dot{\cap}R\in\text{Rl}ʻ P\) -/
theorem pm61_41 {P Q R : α → β → Prop} : Q ∈ rl P → Q ⩀ R ∈ rl P :=
  fun h x y hqr => h x y (And.left hqr)

/-- ✱61·42. \(\vdash:Q\in\text{Rl}ʻ P.R\unicode{x2abd}Q.\dot{\exists}!R.\supset.R\in\text{Rl ex}ʻ P\) -/
theorem pm61_42 {P Q R : α → β → Prop} : (Q ∈ rl P ∧ R ⪽ Q) ∧ rEx R → R ∈ rlEx P :=
  fun ⟨h, hR⟩ => ⟨pm61_4 h, hR⟩

/-- ✱61·43. \(\vdash:Q,R\in\text{Rl}ʻP.\equiv.Q\unicode{x228d}R\in\text{Rl}ʻ P\) -/
theorem pm61_43 {P Q R : α → β → Prop} : Q ∈ rl P ∧ R ∈ rl P ↔ Q ⊍ R ∈ rl P :=
  ⟨fun ⟨hQ, hR⟩ x y h => Or.elim h (hQ x y) (hR x y),
    fun h => ⟨fun x y hq => h x y (Or.inl hq), fun x y hr => h x y (Or.inr hr)⟩⟩

/-- ✱61·44. \(\vdash:Q\in\text{Rl}ʻ P.R\in\text{Rl ex}ʻ P.\supset.Q\unicode{x228d}R\in\text{Rl ex}ʻ P\) -/
theorem pm61_44 {P Q R : α → β → Prop} : Q ∈ rl P ∧ R ∈ rlEx P → Q ⊍ R ∈ rlEx P := by
  rintro ⟨hQ, hR, a, b, hab⟩
  exact ⟨pm61_43.1 ⟨hQ, hR⟩, a, b, Or.inr hab⟩

/-- ✱61·5. \(\vdash.\dot{s}ʻ \text{Rl}ʻ P=P\) -/
theorem pm61_5 {P : α → β → Prop} : sumRel (rl P) = P := by
  funext x y
  exact propext ⟨fun ⟨R, hR, h⟩ => hR x y h, fun h => ⟨P, fun _ _ h => h, h⟩⟩

/-- ✱61·501. \(\vdash.\dot{s}ʻ\text{Rl ex}ʻ P=P\) -/
theorem pm61_501 {P : α → β → Prop} : sumRel (rlEx P) = P := by
  funext x y
  exact propext ⟨fun ⟨R, hR, h⟩ => hR.1 x y h, fun h => ⟨P, ⟨fun _ _ h => h, x, y, h⟩, h⟩⟩

/-- ✱61·51. \(\vdash.\dot{p}ʻ\text{Rl}ʻ P=\dot{\Lambda}\) -/
theorem pm61_51 {P : α → β → Prop} : prodRel (rl P) = rNull := by
  funext x y
  exact propext ⟨fun h => h rNull pm61_3, fun h => (rNull_apply x y h).elim⟩

/-- ✱61·52. \(\vdash:\dot{s}ʻ \lambda\unicode{x2abd}Q.\equiv.\lambda\subset \text{Rl}ʻ Q\) -/
theorem pm61_52 {L : Set (α → β → Prop)} {Q : α → β → Prop} : sumRel L ⪽ Q ↔ L ⊆ rl Q :=
  ⟨fun h R hR x y hxy => h x y ⟨R, hR, hxy⟩, fun h x y ⟨_, hR, hxy⟩ => h hR x y hxy⟩

/-- ✱61·53. \(\vdash:Q\unicode{x2abd}\dot{p}ʻ \lambda.\equiv.Q\in pʻ\text{Rl}ʻʻ \lambda\) -/
theorem pm61_53 {Q : α → β → Prop} {L : Set (α → β → Prop)} :
    Q ⪽ prodRel L ↔ Q ∈ prodCls (Rl ʻʻ L) := by
  constructor
  · rintro h X ⟨S, hS, hX⟩
    rw [show X = rl S from hX]
    exact fun x y hq => h x y hq S hS
  · intro h x y hq S hS
    exact (h (rl S) ⟨S, hS, rfl⟩ : Q ⪽ S) x y hq

/-- ✱61·54. \(\vdash.\text{Rl}ʻ\dot{p}ʻ \lambda=pʻ\text{Rl}ʻʻ \lambda\) -/
theorem pm61_54 {L : Set (α → β → Prop)} : rl (prodRel L) = prodCls (Rl ʻʻ L) :=
  Set.ext fun _ => pm61_53

/-- ✱61·55. \(\vdash.\text{Rl}ʻ P=\text{Rl}ʻ Q.\equiv.P=Q\) -/
theorem pm61_55 {P Q : α → β → Prop} : rl P = rl Q ↔ P = Q := by
  constructor
  · intro h
    have h2 := congrArg sumRel h
    rwa [pm61_5, pm61_5] at h2
  · rintro rfl
    rfl

/-- ✱61·56. \(\vdash.\text{Rl ex}ʻ P=\text{Rl ex}ʻ Q.\equiv.P=Q\) -/
theorem pm61_56 {P Q : α → β → Prop} : rlEx P = rlEx Q ↔ P = Q := by
  constructor
  · intro h
    have h2 := congrArg sumRel h
    rwa [pm61_501, pm61_501] at h2
  · rintro rfl
    rfl

/-- ✱61·6. \(\vdash:xPy.\supset.x\downarrow y\in\text{Rl ex}ʻ P\) -/
theorem pm61_6 {P : α → β → Prop} {x : α} {y : β} : P x y → x ↓ y ∈ rlEx P :=
  couple_mem_rlEx

/-- ✱61·62. \(\vdash:xPy.zPw.\supset.x\downarrow y\unicode{x228d}z\downarrow w\in\text{Rl ex}ʻ P\) -/
theorem pm61_62 {P : α → β → Prop} {x z : α} {y w : β} :
    P x y ∧ P z w → x ↓ y ⊍ z ↓ w ∈ rlEx P :=
  fun ⟨h1, h2⟩ => pm61_44 ⟨(pm61_6 h1).1, pm61_6 h2⟩

/-- ✱61·7. \(\vdash.\text{Rl}ʻ P\in\text{Cl}ʻ\text{Rel}\) -/
theorem pm61_7 {P : α → β → Prop} : rl P ∈ cl Rel := fun R _ => by
  rw [Rel_eq_univ]
  exact Set.mem_univ R

/-!
## [✱62] The relation of membership of a class

*(Vol. 1, p. 414)*

> *Summary of* *62.
>
> When "\(x\in\alpha\)" was defined, in *20, it was defined as a propositional function; and this mode of definition was necessary, because we had to treat of this function before treating of relations. But for many purposes it is desirable to regard \(\in\) as a relation, so that "\(x\in\alpha\)" becomes an instance of the notation "\(uRv\)." This requires, strictly speaking, a change in the meaning of "\(x\in\alpha\)," but it is a change which does not falsify any of the previous propositions in which "\(x\in\alpha\)" occurs; for if we call the new meaning "\(x\unicode{x03AD}\alpha\)," *i.e.* if we put \[ \begin{array}{l} &\unicode{x03AD} = \hat{x}\hat{\alpha}(x\in\alpha) \quad\text{Df},\\ \text{we have}\qquad &\vdash: x\unicode{x03AD}\alpha . \equiv . x\in\alpha. \end{array} \]
>
> …

**Lean reading.** PM's relation `∈` is `memRel : α → Set α → Prop` (Defs), while `x ∈ α` keeps
Lean's meaning, so ✱62·1 holds by `Iff.rfl`. `∈⃗'α`, `∈⃖'x` are `refs memRel A`, `rels memRel x`;
`D'∈`, `ᗡ'∈` are `dom memRel`, `codom memRel`; `∈ ↾ κ` is `memRel ↾ K`; `∈''κ` is `memRel ʻʻ K`;
`P_∈` is `imgRel P` and `sg'(P | ∈)` is `Rfwd (P ⨾ memRel)` (`sg = graph Rfwd`). `ῐ` is
`iota˘`, whose descriptive function may fail to exist: `ψ(ῐ'α)` is `Desc iota˘ A ψ`, `ψ(∈'α)` is
`Desc memRel A ψ`, and an equation between two descriptions gives the first the larger scope
(Basic §5). `E!!R''ᗡ'R` is `EE R (codom R)`. Since `∈` is not homogeneous, `∈²` (✱62·31·32) is
the relative product of `∈` with `∈` of the next type, as PM's note to ✱62·31 says, and the
relation `s` of ✱62·32 is `graph sumCls`.

**Status.** proved (all propositions; ✱62·01 definition; ✱62·31, ✱62·32 proved (reading):
`∈²` and the relation `s`, see their docstrings).
-/

/-- ✱62·01 (Df). \(\in =\hat{x}\hat{\alpha}(x\in \alpha) \text{Df}\) -/
theorem pm62_01 : (memRel : α → Set α → Prop) = fun x A => x ∈ A := rfl

/-- ✱62·1. \(\vdash:x\in \alpha.\equiv.x\in \alpha \quad[\text{*21·3.(*62·01)}]\) -/
theorem pm62_1 {x : α} {A : Set α} : memRel x A ↔ x ∈ A := Iff.rfl

/-- ✱62·2. \(\vdash.\overrightarrow{\in}ʻ\alpha=\alpha\) -/
theorem pm62_2 {A : Set α} : refs memRel A = A := rfl

/-- ✱62·21. \(\vdash.\overleftarrow{\in}ʻx=\hat{\alpha}(x\in \alpha) \quad[\text{*32·131}]\) -/
theorem pm62_21 {x : α} : rels memRel x = {A | x ∈ A} := rfl

/-- ✱62·22. \(\vdash.\text{D}ʻ\in =\text{V}\) -/
theorem pm62_22 : dom (memRel : α → Set α → Prop) = V :=
  Set.ext fun x => ⟨fun _ => rfl, fun _ => ⟨Set.univ, Set.mem_univ x⟩⟩

/-- ✱62·23. \(\vdash.\text{ᗡ}ʻ\in =\text{Cls}-\iotaʻ\Lambda\) -/
theorem pm62_23 : codom (memRel : α → Set α → Prop) = Cls \ ι Λ := by
  ext A
  show (∃ x, x ∈ A) ↔ A ∈ Cls ∧ ¬ A ∈ ι Λ
  rw [mem_iota_Null, Cls_eq_univ]
  exact ⟨fun h => ⟨Set.mem_univ A, Set.nonempty_iff_ne_empty.1 h⟩,
    fun h => Set.nonempty_iff_ne_empty.2 h.2⟩

/-- ✱62·231. \(\vdash:\kappa\subset \text{ᗡ}ʻ\in .\equiv.\Lambda{\sim}\in \kappa \quad[\text{*24·63.*33·131}]\) -/
theorem pm62_231 {K : Set (Set α)} : K ⊆ codom memRel ↔ (Λ : Set α) ∉ K := by
  rw [pm62_23]
  constructor
  · intro h hΛ
    exact (h hΛ).2 (mem_unitCls.2 rfl)
  · intro h A hA
    refine ⟨by rw [Cls_eq_univ]; exact Set.mem_univ A, fun hA' => h ?_⟩
    rw [mem_unitCls] at hA'
    rwa [hA'] at hA

/-- ✱62·24. \(\vdash.\in \mid \breve{\in}=\dot{\text{V}}\) -/
theorem pm62_24 : memRel ⨾ memRel˘ = (rV : α → α → Prop) := by
  funext x y
  exact propext ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨Set.univ, Set.mem_univ x, Set.mem_univ y⟩⟩

/-- ✱62·25. \(\vdash.\breve{\in}\mid \in =\hat{\alpha}\hat{\beta}\{\exists !(\alpha\cap \beta)\}\) -/
theorem pm62_25 : memRel˘ ⨾ memRel = fun (A B : Set α) => (A ∩ B).Nonempty := by
  funext A B
  exact propext ⟨fun ⟨x, h1, h2⟩ => ⟨x, h1, h2⟩, fun ⟨x, h1, h2⟩ => ⟨x, h1, h2⟩⟩

/-- ✱62·26. \(\vdash.R={\in}\mid \overrightarrow{R}\) -/
theorem pm62_26 {R : α → β → Prop} : R = memRel ⨾ Rfwd R := by
  funext x y
  apply propext
  constructor
  · intro h
    exact ⟨refs R y, h, rfl⟩
  · rintro ⟨A, hx, hA⟩
    rw [show A = refs R y from hA] at hx
    exact hx

/-- ✱62·3. \(\vdash.{\in}ʻʻ\kappa=sʻ\kappa\) -/
theorem pm62_3 {K : Set (Set α)} : memRel ʻʻ K = sumCls K := Set.ext fun _ => Iff.rfl

/-- ✱62·31. \(\vdash.\overrightarrow{{\in}^{2}}ʻ\kappa=sʻ\kappa\)

**Status.** proved (reading): `∈` is not homogeneous, so `∈²` (`rsq`, ✱34·02) is not
significant as it stands; following PM's note, `∈²` is the relative product `∈ | ∈` in which the
second `∈` is of the next type above the first (`memRel ⨾ memRel` at the types
`α → Set α → Prop` and `Set α → Set (Set α) → Prop`). -/
theorem pm62_31 {K : Set (Set α)} :
    refs ((memRel : α → Set α → Prop) ⨾ (memRel : Set α → Set (Set α) → Prop)) K = sumCls K :=
  Set.ext fun _ => ⟨fun ⟨A, h1, h2⟩ => ⟨A, h2, h1⟩, fun ⟨A, h1, h2⟩ => ⟨A, h2, h1⟩⟩

/-- ✱62·32. \(\vdash.s={\in}_{\in}=\overrightarrow{{\in}^{2}} \quad[\text{*30·41.*62·3·31.*37·11}]\)

**Status.** proved (reading): the relation `s` is the relation whose descriptive function is
`s'κ` (✱40·02), i.e. `graph sumCls` (Basic §5; PM's proof cites ✱30·41); `∈_∈` is
`imgRel memRel` (✱37·01) and `∈²` is read as in ✱62·31. The chain is the conjunction of its
two links. -/
theorem pm62_32 :
    graph (sumCls : Set (Set α) → Set α) = imgRel memRel ∧
      imgRel (memRel : α → Set α → Prop) = Rfwd (memRel ⨾ memRel) := by
  constructor
  · funext X K
    show (X = sumCls K) = (X = memRel ʻʻ K)
    rw [pm62_3]
  · funext X K
    show (X = memRel ʻʻ K) = (X = refs (memRel ⨾ memRel) K)
    rw [pm62_3, pm62_31]

/-- ✱62·33. \(\vdash.\overrightarrow{\in}=I\upharpoonright \text{Cls}\) -/
theorem pm62_33 : Rfwd (memRel : α → Set α → Prop) = I ↾ Cls := by
  funext B A
  apply propext
  show B = A ↔ B = A ∧ A ∈ Cls
  rw [Cls_eq_univ]
  exact ⟨fun h => ⟨h, Set.mem_univ A⟩, And.left⟩

/-- ✱62·34. \(\vdash.P_{\in}=\text{sg}ʻ(P\mid {\in})\) -/
theorem pm62_34 {P : α → β → Prop} : imgRel P = Rfwd (P ⨾ memRel) := by
  funext X B
  have h : P ʻʻ B = refs (P ⨾ memRel) B :=
    Set.ext fun _ => ⟨fun ⟨y, hy, h⟩ => ⟨y, h, hy⟩, fun ⟨y, h, hy⟩ => ⟨y, hy, h⟩⟩
  show (X = P ʻʻ B) = (X = refs (P ⨾ memRel) B)
  rw [h]

/-- ✱62·4. \(\vdash.{\in} \upharpoonright \kappa=\hat{x}\hat{\alpha}(x \in \alpha.\alpha\in \kappa) \quad[\text{*21·2.(*35·02)}]\) -/
theorem pm62_4 {K : Set (Set α)} : memRel ↾ K = fun x A => x ∈ A ∧ A ∈ K := rfl

/-- ✱62·41. \(\vdash.\text{ᗡ}ʻ{\in}\upharpoonright \kappa=\kappa-\iotaʻ\Lambda\) -/
theorem pm62_41 {K : Set (Set α)} : codom (memRel ↾ K) = K \ ι Λ := by
  ext A
  show (∃ x, x ∈ A ∧ A ∈ K) ↔ A ∈ K ∧ ¬ A ∈ ι Λ
  rw [mem_iota_Null]
  constructor
  · rintro ⟨x, hx, hK⟩
    exact ⟨hK, Set.nonempty_iff_ne_empty.1 ⟨x, hx⟩⟩
  · rintro ⟨hK, h⟩
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 h
    exact ⟨x, hx, hK⟩

/-- ✱62·42. \(\vdash:\Lambda{\sim} {\in}\kappa.\supset .\text{ᗡ}ʻ{\in}\upharpoonright \kappa=\kappa\) -/
theorem pm62_42 {K : Set (Set α)} : (Λ : Set α) ∉ K → codom (memRel ↾ K) = K := by
  intro h
  rw [pm62_41]
  ext A
  constructor
  · exact fun hA => hA.1
  · intro hA
    refine ⟨hA, fun hA' => h ?_⟩
    rw [mem_unitCls] at hA'
    rwa [hA'] at hA

/-- ✱62·43. \(\vdash.\text{D}ʻ{\in}\upharpoonright \kappa=sʻ\kappa\) -/
theorem pm62_43 {K : Set (Set α)} : dom (memRel ↾ K) = sumCls K :=
  Set.ext fun _ => ⟨fun ⟨A, h1, h2⟩ => ⟨A, h2, h1⟩, fun ⟨A, h1, h2⟩ => ⟨A, h2, h1⟩⟩

/-- ✱62·44. \(\vdash:R\unicode{x2abd}{\in}.\equiv.(\alpha).\overrightarrow{R}ʻ\alpha\subset \alpha\) -/
theorem pm62_44 {R : α → Set α → Prop} : R ⪽ memRel ↔ ∀ A, refs R A ⊆ A :=
  ⟨fun h A x hx => h x A hx, fun h _ A hx => h A hx⟩

/-- ✱62·45. \(\vdash\colon\ldotp R\unicode{x2abd}{\in}.\text{E}‼Rʻʻ\text{ᗡ}ʻR.\equiv:\alpha \in \text{ᗡ}ʻR.\supset_{\alpha}.Rʻ\alpha \in \alpha\) -/
theorem pm62_45 {R : α → Set α → Prop} :
    R ⪽ memRel ∧ EE R (codom R) ↔ ∀ A, A ∈ codom R → Desc R A (fun x => x ∈ A) := by
  constructor
  · rintro ⟨h1, h2⟩ A hA
    obtain ⟨b, hb⟩ := h2 A hA
    exact ⟨b, hb, h1 b A ((hb b).2 rfl)⟩
  · intro h
    refine ⟨fun x A hxA => ?_, fun A hA => ?_⟩
    · obtain ⟨b, hb, hbA⟩ := h A ⟨x, hxA⟩
      rw [(hb x).1 hxA]
      exact hbA
    · obtain ⟨b, hb, -⟩ := h A hA
      exact ⟨b, hb⟩

/-- ✱62·5. \(\vdash.\breve{\iota}\unicode{x2abd}{\in}\) -/
theorem pm62_5 : (iota˘ : α → Set α → Prop) ⪽ memRel := fun x A h => by
  rw [show A = ι x from h]
  exact mem_unitCls.2 rfl

/-- ✱62·51. \(\vdash:\text{E}!\breve{\iota}ʻ\alpha.\supset.\breve{\iota}ʻ\alpha=\in ʻ\alpha\) -/
theorem pm62_51 {A : Set α} :
    EDesc iota˘ A → Desc iota˘ A (fun x => Desc memRel A (fun y => x = y)) := by
  rintro ⟨b, hb⟩
  have hA : A = ι b := (hb b).2 rfl
  subst hA
  exact ⟨b, hb, b, fun _ => Iff.rfl, rfl⟩

/-- ✱62·52. \(\vdash:\text{E}!{\in}ʻ\alpha.\equiv.\alpha\in 1.\equiv.\text{E}!\breve{\iota}ʻ\alpha\) -/
theorem pm62_52 {A : Set α} : (EDesc memRel A ↔ A ∈ one) ∧ (A ∈ one ↔ EDesc iota˘ A) := by
  refine ⟨mem_one_iff.symm, ⟨?_, ?_⟩⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, fun _ => iota_cnv_unit⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, (hb b).2 rfl⟩

/-- ✱62·53. \(\vdash:\text{E}!{\in} ʻ\alpha.\supset.{\in} ʻ\alpha=\breve{\iota}ʻ\alpha \quad[\text{*62·51·52}]\) -/
theorem pm62_53 {A : Set α} :
    EDesc memRel A → Desc memRel A (fun x => Desc iota˘ A (fun y => x = y)) :=
  fun h => desc_memRel_iota_cnv (pm62_52.1.1 h)

/-- ✱62·54. \(\vdash:\alpha\in 1.\supset.{\in} ʻ\alpha=\breve{\iota}ʻ\alpha \quad[\text{*62·51·52}]\) -/
theorem pm62_54 {A : Set α} :
    A ∈ one → Desc memRel A (fun x => Desc iota˘ A (fun y => x = y)) :=
  desc_memRel_iota_cnv

/-- ✱62·55. \(\vdash:\kappa\subset 1.\supset.\in \upharpoonright \kappa=\breve{\iota}\upharpoonright \kappa\) -/
theorem pm62_55 {K : Set (Set α)} : K ⊆ one → memRel ↾ K = iota˘ ↾ K := by
  intro h
  funext x A
  apply propext
  constructor
  · rintro ⟨hx, hA⟩
    obtain ⟨b, rfl⟩ := h hA
    exact ⟨iota_cnv_unit.2 hx, hA⟩
  · rintro ⟨hx, hA⟩
    obtain ⟨b, rfl⟩ := h hA
    exact ⟨iota_cnv_unit.1 hx, hA⟩

/-- ✱62·56. \(\vdash.{\in} \upharpoonright \iotaʻʻ\alpha=\breve{\iota}\upharpoonright \iotaʻʻ\alpha=\alpha\upharpoonleft \breve{\iota}\) -/
theorem pm62_56 {A : Set α} :
    memRel ↾ iota ʻʻ A = iota˘ ↾ iota ʻʻ A ∧ iota˘ ↾ iota ʻʻ A = A ◁ iota˘ := by
  refine ⟨pm62_55 ?_, ?_⟩
  · rintro B ⟨y, -, hB⟩
    exact ⟨y, hB⟩
  · funext x B
    apply propext
    constructor
    · rintro ⟨hx, y, hy, hB⟩
      have hxy : x = y :=
        unitCls_injective ((show B = ι x from hx).symm.trans (show B = ι y from hB))
      rw [hxy]
      exact ⟨hy, show B = ι y from hB⟩
    · rintro ⟨hx, hB⟩
      exact ⟨hB, x, hx, hB⟩

/-- ✱62·57. \(\vdash.\breve{\iota}=\in \upharpoonright 1\) -/
theorem pm62_57 : (iota˘ : α → Set α → Prop) = memRel ↾ one := by
  funext x A
  apply propext
  constructor
  · intro h
    have hA : A = ι x := h
    exact ⟨by rw [hA]; exact mem_unitCls.2 rfl, x, hA⟩
  · rintro ⟨hx, b, rfl⟩
    exact iota_cnv_unit.2 hx

/-!
## [✱63] Relative types of classes

*(Vol. 1, p. 419)*

> *Summary of* *63.
>
> The notations introduced in this and the two following numbers serve to express the type of one variable in terms of the type of another. They are very useful in arithmetic, where it is necessary to take account of types in order to avoid contradictions. The two chief notations are "\(t_{0}ʻ\alpha\)," for the type in which \(\alpha\) is contained, and "\(tʻx\)," for the type of which \(x\) is a member. We put
>
> *63·02. \(t_{0}ʻ\alpha = \alpha \cup -\alpha \quad \text{Df}\)
>
> This defines "the type of members of \(\alpha\)," or "the type which is of the same type as \(\alpha\)." The characteristic of a type is that if \(\tau\) is a type, we have \[ (x) . x \in \tau\text{,} \] and conversely, if \((x) . x \in \tau\), then \(\tau\) is a type. For in that case, "\(x \in \tau\)" is true whenever it is significant, *i.e.* whenever \(x\) belongs to the type which is the range of significance of \(x\) in "\(x \in \tau\)." Consequently \(\tau\) is this range of significance, *i.e.* is a type.
>
> …

**Lean reading.** `t'x`, `t¹'x`, `t²'x`, `t³'x`, `t₀'α`, `t₁'κ`, `t₂'κ`, `t₃'κ` are `typ x`,
`typ1 x`, `typ2 x`, `typ3 x`, `typ₀ A`, `typ₁ K`, `typ₂ K`, `typ₃ K`, defined as PM defines them
(Defs) at the Lean types PM's text forces (`typ₀ A : Set α` for `A : Set α`, `typ₁ K : Set α`
for `K : Set (Set α)`, `typ2 x : Set (Set α)` for `x : α`). Where a proposition relates
variables of different types (`x ∈ t₀'α`, `α ∈ t₀'κ`, `κ ⊂ t'α`, …) they are given the Lean types
that make every clause significant, so each equation between types is between terms of one Lean
type. In Lean every such type is `Set.univ` of its type (`typ_eq_univ`, `typ₀_eq_univ`), and the
propositions are proved by rewriting with these; their content is the explicit typing of their
terms. `f(φy)` (✱63·107–·109) is `f : Prop → Prop`. ✱63·18, ✱63·181 and ✱63·382 are false for an
empty type and take `[Nonempty α]` (Basic §3).

**Status.** proved (all propositions; ✱63·01–·051 definition; ✱63·18, ✱63·181, ✱63·382 proved
(reading): `[Nonempty α]`).
-/

/-- ✱63·01 (Df). \(tʻx = \iotaʻx \cup - \iotaʻx \quad \text{Df}\) -/
theorem pm63_01 {x : α} : typ x = ι x ∪ (ι x)ᶜ := rfl

/-- ✱63·011 (Df). \(t^{1}ʻx = tʻx \quad \text{Df}\) -/
theorem pm63_011 {x : α} : typ1 x = typ x := rfl

/-- ✱63·02 (Df). \(t_{0}ʻ\alpha = \alpha \cup -\alpha \quad \text{Df}\) -/
theorem pm63_02 {A : Set α} : typ₀ A = A ∪ Aᶜ := rfl

/-- ✱63·03 (Df). \(t_{1}ʻ\kappa = t_{0}ʻsʻ\kappa \quad \text{Df}\) -/
theorem pm63_03 {K : Set (Set α)} : typ₁ K = typ₀ (sumCls K) := rfl

/-- ✱63·04 (Df). \(t^{2}ʻx = tʻtʻx \quad \text{Df}\) -/
theorem pm63_04 {x : α} : typ2 x = typ (typ x) := rfl

/-- ✱63·041 (Df). \(t^{3}ʻx = tʻt^{2}ʻx \quad \text{Df}\) -/
theorem pm63_041 {x : α} : typ3 x = typ (typ2 x) := rfl

/-- ✱63·05 (Df). \(t_{2}ʻ\kappa = t_{1}ʻt_{1}ʻ\kappa \quad \text{Df}\) -/
theorem pm63_05 {K : Set (Set (Set α))} : typ₂ K = typ₁ (typ₁ K) := rfl

/-- ✱63·051 (Df). \(t_{3}ʻ\kappa = t_{1}ʻt_{2}ʻ\kappa \quad\text{Df}\) -/
theorem pm63_051 {K : Set (Set (Set (Set α)))} : typ₃ K = typ₁ (typ₂ K) := rfl

/-- ✱63·1. \(\vdash . (x) . x \in t_{0}ʻ\alpha \quad[\text{*22·88}]\) -/
theorem pm63_1 {A : Set α} : ∀ x, x ∈ typ₀ A := by typ_simp

/-- ✱63·101. \(\vdash . tʻx = t_{0}ʻ\iotaʻx = \iotaʻx \cup - \iotaʻx \quad[\text{*20·2 . (*63·01·02)}]\) -/
theorem pm63_101 {x : α} : typ x = typ₀ (ι x) ∧ typ₀ (ι x) = ι x ∪ (ι x)ᶜ := by typ_simp

/-- ✱63·102. \(\vdash . (y) . y \in tʻx \quad[\text{*63·1·101}]\) -/
theorem pm63_102 {x : α} : ∀ y, y ∈ typ x := by typ_simp

/-- ✱63·103. \(\vdash . x \in tʻx \quad[\text{*63·101 . *51·16}]\) -/
theorem pm63_103 {x : α} : x ∈ typ x := by typ_simp

/-- ✱63·104. \(\vdash : \phi x . {\sim}\phi y . \supset . y \in tʻx \quad[\text{*63·101 . *13·14}]\) -/
theorem pm63_104 {φ : α → Prop} {x y : α} : φ x ∧ ¬φ y → y ∈ typ x := by typ_simp

/-- ✱63·105. \(\vdash . \alpha \subset t_{0}ʻ\alpha \quad[\text{*22·58}]\) -/
theorem pm63_105 {A : Set α} : A ⊆ typ₀ A := by typ_simp

/-- ✱63·106. \(\vdash . t_{0}ʻ\alpha = t_{0}ʻ - \alpha \quad[\text{*22·8}]\) -/
theorem pm63_106 {A : Set α} : typ₀ A = typ₀ Aᶜ := by typ_simp

/-- ✱63·107. \(\vdash \colon\ldotp (x) . \phi x : f(\phi y) : \supset . \phi y\) -/
theorem pm63_107 {φ : α → Prop} {f : Prop → Prop} {y : α} : (∀ x, φ x) ∧ f (φ y) → φ y :=
  fun ⟨h, _⟩ => h y

/-- ✱63·108. \(\vdash : f(y \in tʻx) . \supset . y \in tʻx \quad[\text{*63·107·102}]\) -/
theorem pm63_108 {f : Prop → Prop} {x y : α} : f (y ∈ typ x) → y ∈ typ x := by typ_simp

/-- ✱63·109. \(\vdash : f(y \in t_{0}ʻ\alpha) . \supset . y \in t_{0}ʻ\alpha \quad[\text{*63·107·1}]\) -/
theorem pm63_109 {f : Prop → Prop} {A : Set α} {y : α} : f (y ∈ typ₀ A) → y ∈ typ₀ A := by
  typ_simp

/-- ✱63·11. \(\vdash : x \in t_{0}ʻ\alpha . \supset . tʻx = \alpha \cup - \alpha = t_{0}ʻ\alpha\) -/
theorem pm63_11 {x : α} {A : Set α} : x ∈ typ₀ A → typ x = A ∪ Aᶜ ∧ A ∪ Aᶜ = typ₀ A := by
  typ_simp

/-- ✱63·12. \(\vdash \colon\ldotp \phi x \lor {\sim}\phi x . \supset : \phi y \lor {\sim}\phi y . \equiv_{y} . y \in tʻx\) -/
theorem pm63_12 {φ : α → Prop} {x : α} : φ x ∨ ¬φ x → ∀ y, (φ y ∨ ¬φ y ↔ y ∈ typ x) :=
  fun _ y => ⟨fun _ => by rw [typ_eq_univ]; exact Set.mem_univ y, fun _ => em _⟩

/-- ✱63·13. \(\vdash : \phi x . \phi y . \supset . y \in tʻx \quad[\text{*63·12 . Imp . Add}]\) -/
theorem pm63_13 {φ : α → Prop} {x y : α} : φ x ∧ φ y → y ∈ typ x := by typ_simp

/-- ✱63·14. \(\vdash : (x) . x \in \alpha . \supset . t_{0}ʻ\alpha = \alpha \quad[\text{*24·14·17·24 . (*63·02)}]\) -/
theorem pm63_14 {A : Set α} : (∀ x, x ∈ A) → typ₀ A = A := fun h => by
  rw [typ₀_eq_univ]
  exact (Set.eq_univ_of_forall h).symm

/-- ✱63·15. \(\vdash . t_{0}ʻtʻx = tʻx \quad[\text{*63·14·102}]\) -/
theorem pm63_15 {x : α} : typ₀ (typ x) = typ x := by typ_simp

/-- ✱63·151. \(\vdash . t_{0}ʻt_{0}ʻ\alpha = t_{0}ʻ\alpha \quad[\text{*63·14·1}]\) -/
theorem pm63_151 {A : Set α} : typ₀ (typ₀ A) = typ₀ A := by typ_simp

/-- ✱63·152. \(\vdash . x \in t_{0}ʻtʻx \quad[\text{*63·103·15}]\) -/
theorem pm63_152 {x : α} : x ∈ typ₀ (typ x) := by typ_simp

/-- ✱63·16. \(\vdash:x\in tʻy.\equiv.y\in tʻx.\equiv.\exists !tʻx\cap tʻy.\equiv.tʻx=tʻy\) -/
theorem pm63_16 {x y : α} :
    ((x ∈ typ y ↔ y ∈ typ x) ∧ (y ∈ typ x ↔ (typ x ∩ typ y).Nonempty)) ∧
      ((typ x ∩ typ y).Nonempty ↔ typ x = typ y) := by
  have : Nonempty α := ⟨x⟩
  typ_simp

/-- ✱63·17. \(\vdash:y\in tʻx.z\in tʻy.\supset.z\in tʻx \quad[\text{*63·16}]\) -/
theorem pm63_17 {x y z : α} : y ∈ typ x ∧ z ∈ typ y → z ∈ typ x := by typ_simp

/-- ✱63·18. \(\vdash.\exists !t_{0}ʻ\alpha \quad[\text{*10·25.*63·1}]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the
proof cites ✱10·25); for an empty type `t₀'α` is null, so `[Nonempty α]` is added. -/
theorem pm63_18 [Nonempty α] {A : Set α} : (typ₀ A).Nonempty := by typ_simp

/-- ✱63·181. \(\vdash:\alpha\subset t_{0}ʻ\beta.\equiv.\beta\subset t_{0}ʻ\alpha.\equiv.\exists !t_{0}ʻ\alpha\cap t_{0}ʻ\beta.\equiv.t_{0}ʻ\alpha=t_{0}ʻ\beta\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the
proof uses ✱63·18): for an empty type the first two clauses hold and `∃!t₀'α ∩ t₀'β` fails,
so `[Nonempty α]` is added. -/
theorem pm63_181 [Nonempty α] {A B : Set α} :
    ((A ⊆ typ₀ B ↔ B ⊆ typ₀ A) ∧ (B ⊆ typ₀ A ↔ (typ₀ A ∩ typ₀ B).Nonempty)) ∧
      ((typ₀ A ∩ typ₀ B).Nonempty ↔ typ₀ A = typ₀ B) := by
  typ_simp

/-- ✱63·182. \(\vdash:\alpha\subset t_{0}ʻ\beta.\beta\subset t_{0}ʻ\gamma.\supset.\alpha\subset t_{0}ʻ\gamma \quad[\text{*63·181}]\) -/
theorem pm63_182 {A B G : Set α} : A ⊆ typ₀ B ∧ B ⊆ typ₀ G → A ⊆ typ₀ G := by typ_simp

/-- ✱63·19. \(\vdash.tʻt_{0}ʻ\alpha=tʻ\alpha\) -/
theorem pm63_19 {A : Set α} : typ (typ₀ A) = typ A := by typ_simp

/-- ✱63·191. \(\vdash.t_{0}ʻ\alpha\in tʻ\alpha \quad[\text{*63·103·19}]\) -/
theorem pm63_191 {A : Set α} : typ₀ A ∈ typ A := by typ_simp

/-- ✱63·2. \(\vdash:x\in t_{0}ʻ\alpha.\alpha\in t_{0}ʻ\kappa.\supset.t^{2}ʻx=tʻ\alpha=t_{0}ʻ\kappa\) -/
theorem pm63_2 {x : α} {A : Set α} {K : Set (Set α)} :
    x ∈ typ₀ A ∧ A ∈ typ₀ K → typ2 x = typ A ∧ typ A = typ₀ K := by
  typ_simp

/-- ✱63·21. \(\vdash:\alpha\subset tʻx.\equiv.t_{0}ʻ\alpha=tʻx\) -/
theorem pm63_21 {x : α} {A : Set α} : A ⊆ typ x ↔ typ₀ A = typ x := by typ_simp

/-- ✱63·22. \(\vdash:\alpha\subset tʻx.\equiv.x\in t_{0}ʻ\alpha.\equiv.tʻx=t_{0}ʻ\alpha\) -/
theorem pm63_22 {x : α} {A : Set α} :
    (A ⊆ typ x ↔ x ∈ typ₀ A) ∧ (x ∈ typ₀ A ↔ typ x = typ₀ A) := by
  typ_simp

/-- ✱63·23. \(\vdash:\alpha\subset tʻx.\kappa\subset tʻ\alpha.\supset.t^{2}ʻx=tʻ\alpha=t_{0}ʻ\kappa \quad[\text{*63·2·22}]\) -/
theorem pm63_23 {x : α} {A : Set α} {K : Set (Set α)} :
    A ⊆ typ x ∧ K ⊆ typ A → typ2 x = typ A ∧ typ A = typ₀ K := by
  typ_simp

/-- ✱63·3. \(\vdash:(\alpha).\alpha\in \kappa.\supset.(x).x\in sʻ\kappa\) -/
theorem pm63_3 {K : Set (Set α)} : (∀ A, A ∈ K) → ∀ x, x ∈ sumCls K :=
  fun h x => ⟨Set.univ, h _, Set.mem_univ x⟩

/-- ✱63·31. \(\vdash.sʻ(\kappa\cup -\kappa)=sʻ\kappa\cup -sʻ\kappa\) -/
theorem pm63_31 {K : Set (Set α)} : sumCls (K ∪ Kᶜ) = sumCls K ∪ (sumCls K)ᶜ := by typ_simp

/-- ✱63·32. \(\vdash.t_{1}ʻ\kappa=sʻt_{0}ʻ\kappa \quad[\text{*63·31.(*63·02·03)}]\) -/
theorem pm63_32 {K : Set (Set α)} : typ₁ K = sumCls (typ₀ K) := by typ_simp

/-- ✱63·321. \(\vdash.t_{1}ʻ\kappa=t_{1}ʻt_{0}ʻ\kappa=t_{0}ʻt_{1}ʻ\kappa\) -/
theorem pm63_321 {K : Set (Set α)} : typ₁ K = typ₁ (typ₀ K) ∧ typ₁ (typ₀ K) = typ₀ (typ₁ K) := by
  typ_simp

/-- ✱63·33. \(\vdash:t_{0}ʻ\kappa=t_{0}ʻ\lambda.\supset.t_{1}ʻ\kappa=t_{1}ʻ\lambda \quad[\text{*30·37.*63·32}]\) -/
theorem pm63_33 {K L : Set (Set α)} : typ₀ K = typ₀ L → typ₁ K = typ₁ L := by typ_simp

/-- ✱63·34. \(\vdash.t_{1}ʻtʻ\alpha=t_{0}ʻ\alpha=sʻtʻ\alpha\) -/
theorem pm63_34 {A : Set α} : typ₁ (typ A) = typ₀ A ∧ typ₀ A = sumCls (typ A) := by typ_simp

/-- ✱63·35. \(\vdash:tʻ\alpha=tʻ\beta.\supset.t_{0}ʻ\alpha=t_{0}ʻ\beta \quad[\text{*30·37.*63·34}]\) -/
theorem pm63_35 {A B : Set α} : typ A = typ B → typ₀ A = typ₀ B := by typ_simp

/-- ✱63·36. \(\vdash:tʻ\kappa=tʻ\lambda.\supset.t_{1}ʻ\kappa=t_{1}ʻ\lambda \quad[\text{*63·35·33}]\) -/
theorem pm63_36 {K L : Set (Set α)} : typ K = typ L → typ₁ K = typ₁ L := by typ_simp

/-- ✱63·361. \(\vdash:t_{0}ʻ\alpha=t_{0}ʻ\beta.\supset.tʻ\alpha=tʻ\beta \quad[\text{*30·37.*63·19}]\) -/
theorem pm63_361 {A B : Set α} : typ₀ A = typ₀ B → typ A = typ B := by typ_simp

/-- ✱63·37. \(\vdash:t_{0}ʻ\alpha=t_{0}ʻ\beta.\equiv.tʻ\alpha=tʻ\beta \quad[\text{*63·35·361}]\) -/
theorem pm63_37 {A B : Set α} : typ₀ A = typ₀ B ↔ typ A = typ B := by typ_simp

/-- ✱63·371. \(\vdash:\beta\subset t_{0}ʻ\alpha.\equiv.\beta\in tʻ\alpha\) -/
theorem pm63_371 {A B : Set α} : B ⊆ typ₀ A ↔ B ∈ typ A := by typ_simp

/-- ✱63·38. \(\vdash:\alpha\in t_{0}ʻ\kappa.x\in t_{0}ʻ\alpha.\supset.tʻx=t_{0}ʻ\alpha=t_{1}ʻ\kappa\) -/
theorem pm63_38 {x : α} {A : Set α} {K : Set (Set α)} :
    A ∈ typ₀ K ∧ x ∈ typ₀ A → typ x = typ₀ A ∧ typ₀ A = typ₁ K := by
  typ_simp

/-- ✱63·381. \(\vdash:x\in t_{1}ʻ\kappa.\supset.tʻx=t_{1}ʻ\kappa\) -/
theorem pm63_381 {x : α} {K : Set (Set α)} : x ∈ typ₁ K → typ x = typ₁ K := by typ_simp

/-- ✱63·382. \(\vdash.\exists !t_{1}ʻ\kappa \quad[\text{*63·18.(*63·03)}]\)

**Status.** proved (reading): PM assumes every type has a member (Introduction, Ch. I; the
proof cites ✱63·18); `[Nonempty α]` is added. -/
theorem pm63_382 [Nonempty α] {K : Set (Set α)} : (typ₁ K).Nonempty := by typ_simp

/-- ✱63·383. \(\vdash.tʻt_{1}ʻ\kappa=t_{0}ʻ\kappa\) -/
theorem pm63_383 {K : Set (Set α)} : typ (typ₁ K) = typ₀ K := by typ_simp

/-- ✱63·384. \(\vdash:t_{1}ʻ\kappa=t_{1}ʻ\lambda.\supset.t_{0}ʻ\kappa=t_{0}ʻ\lambda.tʻ\kappa=tʻ\lambda \quad[\text{*63·383·37}]\) -/
theorem pm63_384 {K L : Set (Set α)} : typ₁ K = typ₁ L → typ₀ K = typ₀ L ∧ typ K = typ L := by
  typ_simp

/-- ✱63·39. \(\vdash:t_{1}ʻ\kappa=t_{1}ʻ\lambda.\equiv.t_{0}ʻ\kappa=t_{0}ʻ\lambda.\equiv.tʻ\kappa=tʻ\lambda \quad[\text{*63·33·384·37}]\) -/
theorem pm63_39 {K L : Set (Set α)} :
    (typ₁ K = typ₁ L ↔ typ₀ K = typ₀ L) ∧ (typ₀ K = typ₀ L ↔ typ K = typ L) := by
  typ_simp

/-- ✱63·391. \(\vdash:tʻx=tʻy.\equiv.t^{2}ʻx=t^{2}ʻy\) -/
theorem pm63_391 {x y : α} : typ x = typ y ↔ typ2 x = typ2 y := by typ_simp

/-- ✱63·392. \(\vdash:t_{2}ʻ\kappa=t_{2}ʻ\lambda.\equiv.t_{1}ʻ\kappa=t_{1}ʻ\lambda.\equiv.t_{0}ʻ\kappa=t_{0}ʻ\lambda\) -/
theorem pm63_392 {K L : Set (Set (Set α))} :
    (typ₂ K = typ₂ L ↔ typ₁ K = typ₁ L) ∧ (typ₁ K = typ₁ L ↔ typ₀ K = typ₀ L) := by
  typ_simp

/-- ✱63·4. \(\vdash:\alpha\in t_{0}ʻ\kappa.\kappa\in t_{0}ʻ\lambda.\supset.t_{0}ʻ\alpha=t_{1}ʻ\kappa=t_{2}ʻ\lambda\) -/
theorem pm63_4 {A : Set α} {K : Set (Set α)} {L : Set (Set (Set α))} :
    A ∈ typ₀ K ∧ K ∈ typ₀ L → typ₀ A = typ₁ K ∧ typ₁ K = typ₂ L := by
  typ_simp

/-- ✱63·41. \(\vdash.tʻt_{2}ʻ\lambda=t_{1}ʻ\lambda\) -/
theorem pm63_41 {L : Set (Set (Set α))} : typ (typ₂ L) = typ₁ L := by typ_simp

/-- ✱63·42. \(\vdash.t^{2}ʻt_{2}ʻ\lambda=t_{0}ʻ\lambda \quad[\text{*30·37.*63·41·383}]\) -/
theorem pm63_42 {L : Set (Set (Set α))} : typ2 (typ₂ L) = typ₀ L := by typ_simp

/-- ✱63·43. \(\vdash.t_{1}ʻt^{2}ʻx=tʻx \quad[\text{*63·34·15}]\) -/
theorem pm63_43 {x : α} : typ₁ (typ2 x) = typ x := by typ_simp

/-- ✱63·44. \(\vdash.t_{2}ʻt^{2}ʻ\alpha=t_{0}ʻ\alpha \quad[\text{*63·43·34}]\) -/
theorem pm63_44 {A : Set α} : typ₂ (typ2 A) = typ₀ A := by typ_simp

/-- ✱63·5. \(\vdash:x\in t_{0}ʻ\alpha.\equiv.\alpha\in t^{2}ʻx.\equiv.\alpha\subset tʻx.\equiv.tʻx=t_{0}ʻ\alpha\) -/
theorem pm63_5 {x : α} {A : Set α} :
    ((x ∈ typ₀ A ↔ A ∈ typ2 x) ∧ (A ∈ typ2 x ↔ A ⊆ typ x)) ∧ (A ⊆ typ x ↔ typ x = typ₀ A) := by
  typ_simp

/-- ✱63·51. \(\vdash:\alpha\in t_{0}ʻ\kappa.\equiv.\alpha\subset t_{1}ʻ\kappa.\equiv.\kappa\subset tʻ\alpha.\equiv.tʻ\alpha=t_{0}ʻ\kappa\) -/
theorem pm63_51 {A : Set α} {K : Set (Set α)} :
    ((A ∈ typ₀ K ↔ A ⊆ typ₁ K) ∧ (A ⊆ typ₁ K ↔ K ⊆ typ A)) ∧ (K ⊆ typ A ↔ typ A = typ₀ K) := by
  typ_simp

/-- ✱63·52. \(\vdash:\alpha\in t_{1}ʻ\lambda.\equiv.\alpha\subset t_{2}ʻ\lambda.\equiv.\lambda\subset t^{2}ʻ\alpha.\equiv.tʻ\alpha=t_{1}ʻ\lambda.\equiv.t^{2}ʻ\alpha=t_{0}ʻ\lambda\) -/
theorem pm63_52 {A : Set α} {L : Set (Set (Set α))} :
    (((A ∈ typ₁ L ↔ A ⊆ typ₂ L) ∧ (A ⊆ typ₂ L ↔ L ⊆ typ2 A)) ∧
      (L ⊆ typ2 A ↔ typ A = typ₁ L)) ∧ (typ A = typ₁ L ↔ typ2 A = typ₀ L) := by
  typ_simp

/-- ✱63·53. \(\vdash:x\in t_{0}ʻ\alpha.\equiv.t^{2}ʻx=tʻ\alpha.\equiv.tʻx=t_{0}ʻ\alpha\) -/
theorem pm63_53 {x : α} {A : Set α} :
    (x ∈ typ₀ A ↔ typ2 x = typ A) ∧ (typ2 x = typ A ↔ typ x = typ₀ A) := by
  typ_simp

/-- ✱63·54. \(\vdash:\alpha\in t_{0}ʻ\kappa.\equiv.t_{0}ʻ\alpha=t_{1}ʻ\kappa.\equiv.tʻ\alpha=t_{0}ʻ\kappa.\equiv.t^{2}ʻ\alpha=tʻ\kappa\) -/
theorem pm63_54 {A : Set α} {K : Set (Set α)} :
    ((A ∈ typ₀ K ↔ typ₀ A = typ₁ K) ∧ (typ₀ A = typ₁ K ↔ typ A = typ₀ K)) ∧
      (typ A = typ₀ K ↔ typ2 A = typ K) := by
  typ_simp

/-- ✱63·55. \[\begin{align}&\vdash:\kappa\in t_{0}ʻ\lambda.\equiv.t_{1}ʻ\kappa=t_{2}ʻ\lambda.\equiv.t_{0}ʻ\kappa=t_{1}ʻ\lambda.\equiv.tʻ\kappa=t_{0}ʻ\lambda.\equiv.t^{2}ʻ\kappa=tʻ\lambda\\ &[\text{Proof as in *63·54}]\end{align}\] -/
theorem pm63_55 {K : Set (Set α)} {L : Set (Set (Set α))} :
    (((K ∈ typ₀ L ↔ typ₁ K = typ₂ L) ∧ (typ₁ K = typ₂ L ↔ typ₀ K = typ₁ L)) ∧
      (typ₀ K = typ₁ L ↔ typ K = typ₀ L)) ∧ (typ K = typ₀ L ↔ typ2 K = typ L) := by
  typ_simp

/-- ✱63·56. \(\vdash:x\in t_{1}ʻ\kappa.\equiv.tʻx=t_{1}ʻ\kappa.\equiv.t^{2}ʻx=t_{0}ʻ\kappa\) -/
theorem pm63_56 {x : α} {K : Set (Set α)} :
    (x ∈ typ₁ K ↔ typ x = typ₁ K) ∧ (typ x = typ₁ K ↔ typ2 x = typ₀ K) := by
  typ_simp

/-- ✱63·57. \[\begin{align}&\vdash:\alpha\in t_{1}ʻ\lambda.\equiv.t_{0}ʻ\alpha=t_{2}ʻ\lambda.\equiv.tʻ\alpha=t_{1}ʻ\lambda.\equiv.t^{2}ʻ\alpha=t_{0}ʻ\lambda\\ &[\text{Proof as in *63·56}]\end{align}\] -/
theorem pm63_57 {A : Set α} {L : Set (Set (Set α))} :
    ((A ∈ typ₁ L ↔ typ₀ A = typ₂ L) ∧ (typ₀ A = typ₂ L ↔ typ A = typ₁ L)) ∧
      (typ A = typ₁ L ↔ typ2 A = typ₀ L) := by
  typ_simp

/-- ✱63·61. \(\vdash.t^{2}ʻx=tʻ\iotaʻx \quad[\text{*63·19·101}]\) -/
theorem pm63_61 {x : α} : typ2 x = typ (ι x) := by typ_simp

/-- ✱63·62. \(\vdash:x\in t_{0}ʻ\alpha.\supset.\iotaʻx\in tʻ\alpha.tʻ\iotaʻx=tʻ\alpha\) -/
theorem pm63_62 {x : α} {A : Set α} : x ∈ typ₀ A → ι x ∈ typ A ∧ typ (ι x) = typ A := by
  typ_simp

/-- ✱63·621. \(\vdash:x\in \alpha.\supset.\iotaʻx\in tʻ\alpha.tʻ\iotaʻx=tʻ\alpha \quad[\text{*63·62.*63·105}]\) -/
theorem pm63_621 {x : α} {A : Set α} : x ∈ A → ι x ∈ typ A ∧ typ (ι x) = typ A := by typ_simp

/-- ✱63·63. \(\vdash:x\in t_{0}ʻ\alpha.\supset.\iotaʻ\iotaʻx\in t^{2}ʻ\alpha.tʻ\iotaʻ\iotaʻx=t^{2}ʻ\alpha\) -/
theorem pm63_63 {x : α} {A : Set α} :
    x ∈ typ₀ A → ι (ι x) ∈ typ2 A ∧ typ (ι (ι x)) = typ2 A := by
  typ_simp

/-- ✱63·64. \(\vdash.tʻ\beta=t_{0}ʻ\iotaʻʻ\beta\) -/
theorem pm63_64 {B : Set α} : typ B = typ₀ (iota ʻʻ B) := by typ_simp

/-- ✱63·65. \(\vdash.\text{Cl}ʻt_{0}ʻ\alpha=tʻ\alpha \quad[\text{*63·371.*60·2}]\) -/
theorem pm63_65 {A : Set α} : cl (typ₀ A) = typ A := by typ_simp

/-- ✱63·66. \(\vdash.\text{Cl}ʻtʻx=t^{2}ʻx \quad[\text{*63·5.*60·2}]\) -/
theorem pm63_66 {x : α} : cl (typ x) = typ2 x := by typ_simp

/-- ✱63·661. \(\vdash.tʻ\text{Cl}ʻ\alpha=t^{2}ʻ\alpha \quad[\text{*60·34.*63·105·53}]\) -/
theorem pm63_661 {A : Set α} : typ (cl A) = typ2 A := by typ_simp

/-- ✱63·67. \(\vdash.\text{Cl}ʻt_{1}ʻ\kappa=t_{0}ʻ\kappa \quad[\text{*63·51.*60·2}]\) -/
theorem pm63_67 {K : Set (Set α)} : cl (typ₁ K) = typ₀ K := by typ_simp

/-- ✱63·68. \(\vdash.\text{Cl}ʻt_{2}ʻ\kappa=t_{1}ʻ\kappa \quad[\text{*63·52.*60·2}]\) -/
theorem pm63_68 {K : Set (Set (Set α))} : cl (typ₂ K) = typ₁ K := by typ_simp

/-!
## [✱64] Relative types of relations

*(Vol. 1, p. 429)*

> *Summary of* *64.
>
> In the present number, we introduce notations defining the type of a relation relatively to the types of its domain and converse domain, when these types are given relatively to some fixed class \(\alpha\). If \(R\) is any relation, it is of the same type as \(t_{0}ʻ\text{D}ʻR \uparrow t_{0}ʻ\text{ᗡ}ʻR\). If \(\text{D}ʻR\) and \(\text{ᗡ}ʻR\) are both of the same type as \(\alpha\), \(R\) is of the same type as \(t_{0}ʻ\alpha\uparrow t_{0}ʻ\alpha\), which is of the same type as \(\alpha\uparrow \alpha\). The type of \(t_{0}ʻ\alpha \uparrow t_{0}ʻ\alpha\) we call \(t_{00}ʻ\alpha\), and the type of \(t^{m}ʻ\alpha \uparrow t^{n}ʻ\alpha\) we call \(t^{mn}ʻ\alpha\), and the type of \(t_{m}ʻ\alpha \uparrow t_{n}ʻ\alpha\) we call \(t_{mn}ʻ\alpha\), and the type of \(t_{m}ʻ\alpha \uparrow t^{n}ʻ\alpha\) we call \(t_{m}^{n}ʻ\alpha\), and the type of \(t^{m}ʻ\alpha \uparrow t_{n}ʻ\alpha\) we call \({}^{m}t_{n}ʻ\alpha\). We thus have a means of expressing the type of any relation \(R\) in terms of the type of \(\alpha\), provided the types of the domain and converse domain of \(R\) are given relatively to \(\alpha\).
>
> …

**Lean reading.** The e-text numbers the Dfs ✱64·01–·041 and the propositions ✱64·1·11·12
`*64.01.`, …, `*64.12.` (a full stop for the centred dot); `pm64_01`–`pm64_041` are their Defs
targets. `t₀₀'α`, `t^{11}'x`, `t^{22}'x`, `t₁₁'α` are `typ₀₀ A`, `typ11 x`, `typ22 x`, `typ₁₁ A`, and `t₂₂'α` (one of the "etc." of
✱64·022) is written out as `t'(t₂'α ↑ t₂'α)`, `typ (cross (typ₂ A) (typ₂ A))`. Relations are
heterogeneous `α → β → Prop`, `α ↑ β` is `cross A B`, `Rl'(…)` is `rl (…)`, `ṡ'λ` is `sumRel L`.
The type `t'R` of a relation is `Set.univ` of its relation type, and every proposition is proved by
rewriting the relative types to `Set.univ`; the classes in ✱64·3–·34 are taken at the lowest Lean
types at which every term is significant (e.g. `α β : Set (Set (Set γ))` in ✱64·32, where
`t₂₂'α` occurs). ✱64·231 and ✱64·24 mention `C'R`, which PM says is significant only for
homogeneous relations, and are stated for `R Q : α → α → Prop`. The e-text prints `s̆` for `ṡ` in
✱64·23 and drops a `t` in ✱64·32 and ✱64·5.

**Status.** proved (all propositions; ✱64·01–·041 definition; ✱64·23, ✱64·231, ✱64·32, ✱64·5 proved (reading), see their
docstrings).
-/

/-- ✱64·01 (Df). \(t_{00}ʻ\alpha=tʻ(t_{0}ʻ\alpha\uparrow t_{0}ʻ\alpha) \quad\text{Df}\)

The e-text numbers ✱64·01–✱64·12 `*64.01.`, …, `*64.12.` (a full stop for the centred dot). -/
theorem pm64_01 {A : Set α} : typ₀₀ A = typ (cross (typ₀ A) (typ₀ A)) := rfl

/-- ✱64·011 (Df). \(t^{11}ʻx=tʻ(tʻx\uparrow tʻx) \quad\text{Df}\) -/
theorem pm64_011 {x : α} : typ11 x = typ (cross (typ x) (typ x)) := rfl

/-- ✱64·012 (Df). \(t^{12}ʻx=tʻ(tʻx\uparrow t^{2}ʻx) \quad\text{Df}\) -/
theorem pm64_012 {x : α} : typ12 x = typ (cross (typ x) (typ2 x)) := rfl

/-- ✱64·013 (Df). \(t^{21}ʻx=tʻ(t^{2}ʻx\uparrow tʻx) \quad\text{Df}\) -/
theorem pm64_013 {x : α} : typ21 x = typ (cross (typ2 x) (typ x)) := rfl

/-- ✱64·014 (Df). \(t^{22}ʻx=tʻ(t^{2}ʻx\uparrow t^{2}ʻx) \quad\text{Df}\) -/
theorem pm64_014 {x : α} : typ22 x = typ (cross (typ2 x) (typ2 x)) := rfl

/-- ✱64·02 (Df). \(t_{01}ʻ\alpha=tʻ(t_{0}ʻ\alpha\uparrow t_{1}ʻ\alpha) \quad\text{Df}\) -/
theorem pm64_02 {A : Set (Set α)} : typ₀₁ A = typ (cross (typ₀ A) (typ₁ A)) := rfl

/-- ✱64·021 (Df). \(t_{10}ʻ\alpha=tʻ(t_{1}ʻ\alpha\uparrow t_{0}ʻ\alpha) \quad\text{Df}\) -/
theorem pm64_021 {A : Set (Set α)} : typ₁₀ A = typ (cross (typ₁ A) (typ₀ A)) := rfl

/-- ✱64·022 (Df). \(t_{11}ʻ\alpha=tʻ(t_{1}ʻ\alpha\uparrow t_{1}ʻ\alpha) \quad\text{Df}\) -/
theorem pm64_022 {A : Set (Set α)} : typ₁₁ A = typ (cross (typ₁ A) (typ₁ A)) := rfl

/-- ✱64·03 (Df). \(t_{0}^{1}ʻ\alpha=tʻ(t_{0}ʻ\alpha\uparrow tʻ\alpha) \quad\text{Df}\) -/
theorem pm64_03 {A : Set α} : typ₀1 A = typ (cross (typ₀ A) (typ A)) := rfl

/-- ✱64·031 (Df). \(t_{1}^{1}ʻ\alpha=tʻ(t_{1}ʻ\alpha\uparrow tʻ\alpha) \quad\text{Df}\) -/
theorem pm64_031 {A : Set (Set α)} : typ₁1 A = typ (cross (typ₁ A) (typ A)) := rfl

/-- ✱64·04 (Df). \(^{1}t_{0}ʻ\alpha=tʻ(tʻ\alpha\uparrow t_{0}ʻ\alpha) \quad\text{Df}\) -/
theorem pm64_04 {A : Set α} : typ1₀ A = typ (cross (typ A) (typ₀ A)) := rfl

/-- ✱64·041 (Df). \(^{1}t_{1}ʻ\alpha=tʻ(tʻ\alpha\uparrow t_{1}ʻ\alpha) \quad\text{Df}\) -/
theorem pm64_041 {A : Set (Set α)} : typ1₁ A = typ (cross (typ A) (typ₁ A)) := rfl

/-- ✱64·1. \(\vdash.\alpha\uparrow \alpha\in t_{00}ʻ\alpha\) -/
theorem pm64_1 {A : Set α} : cross A A ∈ typ₀₀ A := by typ_simp

/-- ✱64·11. \(\vdash.t_{00}ʻ\alpha=tʻ(\alpha\uparrow\alpha) \quad[\text{*64.1.*63.16}]\) -/
theorem pm64_11 {A : Set α} : typ₀₀ A = typ (cross A A) := by typ_simp

/-- ✱64·12. \(\vdash.\alpha\uparrow\beta\in tʻ(t_{0}ʻ\alpha\uparrow t_{0}ʻ\beta\)) -/
theorem pm64_12 {A : Set α} {B : Set β} : cross A B ∈ typ (cross (typ₀ A) (typ₀ B)) := by
  typ_simp

/-- ✱64·13. \(\vdash.tʻ(t_{0}ʻ\alpha\uparrow t_{0}ʻ\beta)=tʻ(\alpha\uparrow \beta) \quad[\text{*64·12.*63·16}]\) -/
theorem pm64_13 {A : Set α} {B : Set β} :
    typ (cross (typ₀ A) (typ₀ B)) = typ (cross A B) := by
  typ_simp

/-- ✱64·14. \(\vdash.(x,y).x(t_{0}ʻ\alpha\uparrow t_{0}ʻ\beta)y \quad[\text{*63·1.*35·103}]\) -/
theorem pm64_14 {A : Set α} {B : Set β} : ∀ x y, cross (typ₀ A) (typ₀ B) x y := fun x y => by
  rw [typ₀_eq_univ, typ₀_eq_univ]
  exact ⟨Set.mem_univ x, Set.mem_univ y⟩

/-- ✱64·15. \(\vdash.(R).R\unicode{x2abd}t_{0}ʻ\alpha\uparrow t_{0}ʻ\beta \quad[\text{*64·14.*25·14·11}]\) -/
theorem pm64_15 {A : Set α} {B : Set β} : ∀ R : α → β → Prop, R ⪽ cross (typ₀ A) (typ₀ B) :=
  fun _ x y _ => pm64_14 x y

/-- ✱64·16. \(\vdash:R\unicode{x2abd}t_{0}ʻ\alpha\uparrow t_{0}ʻ\beta.\equiv.R\in tʻ(t_{0}ʻ\alpha\uparrow t_{0}ʻ\beta\)) -/
theorem pm64_16 {A : Set α} {B : Set β} {R : α → β → Prop} :
    R ⪽ cross (typ₀ A) (typ₀ B) ↔ R ∈ typ (cross (typ₀ A) (typ₀ B)) :=
  ⟨fun _ => by rw [typ_eq_univ]; exact Set.mem_univ R, fun _ => pm64_15 R⟩

/-- ✱64·2. \(\vdash.\dot{\exists}!R\dot{\cap}S.\supset.S\in tʻR.tʻR=tʻS \quad[\text{*63·13·16}]\) -/
theorem pm64_2 {R S : α → β → Prop} : rEx (R ⩀ S) → S ∈ typ R ∧ typ R = typ S := by typ_simp

/-- ✱64·201. \(\vdash:R\unicode{x2abd}S.\supset.R\in tʻS.tʻR=tʻS\) -/
theorem pm64_201 {R S : α → β → Prop} : R ⪽ S → R ∈ typ S ∧ typ R = typ S := by typ_simp

/-- ✱64·21. \(\vdash:xRy.\supset.R\in tʻ(tʻx\uparrow tʻy\)) -/
theorem pm64_21 {R : α → β → Prop} {x : α} {y : β} :
    R x y → R ∈ typ (cross (typ x) (typ y)) := by
  typ_simp

/-- ✱64·22. \(\vdash.R\in tʻ(t_{0}ʻ\text{D}ʻR\uparrow t_{0}ʻ\text{ᗡ}ʻR) \quad[\text{*64·16.*63·105.*35·83}]\) -/
theorem pm64_22 {R : α → β → Prop} : R ∈ typ (cross (typ₀ (dom R)) (typ₀ (codom R))) := by
  typ_simp

/-- ✱64·23. \(\vdash.tʻR=tʻ\breve{s}ʻtʻR\)

**Status.** proved (reading): transcription error: the e-text prints `s̆` for `ṡ`; the proof
(✱63·103, ✱41·13: `R ⊂̇ ṡ't'R`) shows that `ṡ't'R`, the relational sum of `t'R`
(`sumRel (typ R)`), is meant. -/
theorem pm64_23 {R : α → β → Prop} : typ R = typ (sumRel (typ R)) := by typ_simp

/-- ✱64·231. \(\vdash:R\in tʻQ.\supset.\text{D}ʻR\in tʻ\text{D}ʻQ.\text{ᗡ}ʻR\in tʻ\text{ᗡ}ʻQ.CʻR\in tʻCʻQ\)

**Status.** proved (reading): `C'R ∈ t'C'Q` is significant only when `R` and `Q` are homogeneous
(PM's comment in the Summary of ✱64), and Lean's `fld` requires a homogeneous relation, so the
proposition is stated for `R Q : α → α → Prop`. -/
theorem pm64_231 {R Q : α → α → Prop} :
    R ∈ typ Q → (dom R ∈ typ (dom Q) ∧ codom R ∈ typ (codom Q)) ∧ fld R ∈ typ (fld Q) := by
  typ_simp

/-- The first two clauses of ✱64·231, which PM says do not require homogeneity, for
heterogeneous `R Q : α → β → Prop`. -/
theorem pm64_231_aux_hetero {R Q : α → β → Prop} :
    R ∈ typ Q → dom R ∈ typ (dom Q) ∧ codom R ∈ typ (codom Q) := by
  typ_simp

/-- ✱64·24. \(\vdash:R\in tʻQ.\equiv.CʻR\in tʻCʻQ.\equiv.t_{0}ʻCʻR=t_{0}ʻCʻQ\) -/
theorem pm64_24 {R Q : α → α → Prop} :
    (R ∈ typ Q ↔ fld R ∈ typ (fld Q)) ∧ (fld R ∈ typ (fld Q) ↔ typ₀ (fld R) = typ₀ (fld Q)) := by
  typ_simp

/-- ✱64·3. \(\vdash:t_{00}ʻ\alpha=t_{00}ʻ\beta.\equiv.\alpha\in tʻ\beta.\equiv.tʻ\alpha=tʻ\beta.\equiv.t_{0}ʻ\alpha=t_{0}ʻ\beta\) -/
theorem pm64_3 {A B : Set α} :
    ((typ₀₀ A = typ₀₀ B ↔ A ∈ typ B) ∧ (A ∈ typ B ↔ typ A = typ B)) ∧
      (typ A = typ B ↔ typ₀ A = typ₀ B) := by
  typ_simp

/-- ✱64·31. \(\vdash.t^{11}ʻx=t_{00}ʻtʻx \quad[\text{*63·15.(*64·01·011)}]\) -/
theorem pm64_31 {x : α} : typ11 x = typ₀₀ (typ x) := by typ_simp

/-- ✱64·311. \(\vdash.t_{11}ʻ\alpha=t_{00}ʻt_{1}ʻ\alpha \quad[\text{*63·321.(*64·022·01)}]\) -/
theorem pm64_311 {A : Set (Set α)} : typ₁₁ A = typ₀₀ (typ₁ A) := by typ_simp

/-- ✱64·312. \(\vdash.t^{22}ʻx=t^{11}ʻtʻx=t_{00}ʻt^{2}ʻx \quad[\text{*63·15.(*63·04).(*64·014·011·01)}]\) -/
theorem pm64_312 {x : α} : typ22 x = typ11 (typ x) ∧ typ11 (typ x) = typ₀₀ (typ2 x) := by
  typ_simp

/-- ✱64·313. \(\vdash.t_{22}ʻ\alpha=t_{11}ʻt_{1}ʻ\alpha=t_{00}ʻt_{2}ʻ\alpha \quad[\text{*63·321.(*63·05)}]\) -/
theorem pm64_313 {A : Set (Set (Set α))} :
    typ (cross (typ₂ A) (typ₂ A)) = typ₁₁ (typ₁ A) ∧ typ₁₁ (typ₁ A) = typ₀₀ (typ₂ A) := by
  typ_simp

/-- ✱64·32. \[\begin{align}\vdash:t_{22}ʻ\alpha=t_{22}ʻ\beta.\equiv.t_{11}ʻ\alpha=t_{11}ʻ\beta.\equiv.t_{00}ʻ\alpha=t_{00}ʻ\beta.\equiv.t^{11}ʻ\alpha=t^{11}ʻ\beta.\\ &\equiv.t^{22}ʻ\alpha=t^{22}ʻ\beta.\equiv.\alpha\in tʻ\beta.\equiv.tʻ\alpha=ʻ\beta\end{align}\]

**Status.** proved (reading): transcription error: the last link is printed `t'α = 'β` for
`t'α = t'β`. `t₂₂'α` is written out as `t'(t₂'α ↑ t₂'α)`, and `α`, `β` are taken at
`Set (Set (Set γ))`, the lowest type at which `t₂₂'α` is significant. -/
theorem pm64_32 {A B : Set (Set (Set γ))} :
    (((((typ (cross (typ₂ A) (typ₂ A)) = typ (cross (typ₂ B) (typ₂ B)) ↔
          typ₁₁ A = typ₁₁ B) ∧
        (typ₁₁ A = typ₁₁ B ↔ typ₀₀ A = typ₀₀ B)) ∧
      (typ₀₀ A = typ₀₀ B ↔ typ11 A = typ11 B)) ∧
      (typ11 A = typ11 B ↔ typ22 A = typ22 B)) ∧
      (typ22 A = typ22 B ↔ A ∈ typ B)) ∧ (A ∈ typ B ↔ typ A = typ B) := by
  typ_simp

/-- ✱64·33. \[\begin{align}\vdash:\alpha\in t_{0}ʻ\mu.\equiv.t_{11}ʻ\alpha=t_{22}ʻ\mu.\equiv.t_{00}ʻ\alpha=t_{11}ʻ\mu.&\equiv.t^{11}ʻ\alpha=t_{00}ʻ\mu.\\ &\equiv.t^{22}ʻ\alpha=t^{11}ʻ\mu.\equiv.tʻ\alpha=t_{0}ʻ\mu \end{align}\] -/
theorem pm64_33 {A : Set (Set γ)} {M : Set (Set (Set γ))} :
    ((((A ∈ typ₀ M ↔ typ₁₁ A = typ (cross (typ₂ M) (typ₂ M))) ∧
        (typ₁₁ A = typ (cross (typ₂ M) (typ₂ M)) ↔ typ₀₀ A = typ₁₁ M)) ∧
      (typ₀₀ A = typ₁₁ M ↔ typ11 A = typ₀₀ M)) ∧
      (typ11 A = typ₀₀ M ↔ typ22 A = typ11 M)) ∧ (typ22 A = typ11 M ↔ typ A = typ₀ M) := by
  typ_simp

/-- ✱64·34. \[\begin{align}&\vdash:\alpha\in t_{1}ʻ\mu.\equiv.t_{00}ʻ\alpha=t_{22}ʻ\mu.\equiv.t^{11}ʻ\alpha=t_{11}ʻ\mu.\equiv.t^{22}ʻ\alpha=t_{00}ʻ\mu.\equiv.t^{2}ʻ\alpha=t_{0}ʻ\mu\\ &[\text{Proof as in *64·33}]\end{align}\] -/
theorem pm64_34 {A : Set γ} {M : Set (Set (Set γ))} :
    (((A ∈ typ₁ M ↔ typ₀₀ A = typ (cross (typ₂ M) (typ₂ M))) ∧
        (typ₀₀ A = typ (cross (typ₂ M) (typ₂ M)) ↔ typ11 A = typ₁₁ M)) ∧
      (typ11 A = typ₁₁ M ↔ typ22 A = typ₀₀ M)) ∧ (typ22 A = typ₀₀ M ↔ typ2 A = typ₀ M) := by
  typ_simp

/-- ✱64·5. \(\vdash.\text{Rl}ʻ (t_{0}ʻ\alpha\uparrow t_{0}ʻ\beta)=tʻ(t_{0}ʻ\alpha\uparrow t_{0}ʻ\beta)=tʻ(ʻ\alpha\uparrow\beta) \quad[\text{*64·13·16.*61·2}]\)

**Status.** proved (reading): transcription error: the last term is printed `t'(ʻα ↑ β)` for
`t'(α ↑ β)` (cf. the Summary of ✱64 and ✱64·13). -/
theorem pm64_5 {A : Set α} {B : Set β} :
    rl (cross (typ₀ A) (typ₀ B)) = typ (cross (typ₀ A) (typ₀ B)) ∧
      typ (cross (typ₀ A) (typ₀ B)) = typ (cross A B) := by
  typ_simp

/-- ✱64·51. \(\vdash.x\downarrow y\in tʻ(tʻ x\uparrow tʻy) \quad[\text{*64·21.*55·132}]\) -/
theorem pm64_51 {x : α} {y : β} : x ↓ y ∈ typ (cross (typ x) (typ y)) := by typ_simp

/-- ✱64·52. \(\vdash:x\in t_{0}ʻ\alpha.y\in t_{0}ʻ\beta.\supset.x\downarrow y\in tʻ(t_{0}ʻ\alpha\uparrow t_{0}ʻ\beta) \quad[\text{*63·11.*64·51}]\) -/
theorem pm64_52 {x : α} {y : β} {A : Set α} {B : Set β} :
    x ∈ typ₀ A ∧ y ∈ typ₀ B → x ↓ y ∈ typ (cross (typ₀ A) (typ₀ B)) := by
  typ_simp

/-- ✱64·53. \(\vdash:x\in t_{0}ʻ\alpha.\delta\subset t_{0}ʻ\beta.\supset.(\iotaʻx)\downarrow\delta\in tʻ(tʻ\alpha\uparrow tʻ\beta)\) -/
theorem pm64_53 {x : α} {A : Set α} {B Dl : Set β} :
    x ∈ typ₀ A ∧ Dl ⊆ typ₀ B → (ι x) ↓ Dl ∈ typ (cross (typ A) (typ B)) := by
  typ_simp

/-- ✱64·54. \[\begin{align}\vdash.\text{Rl}ʻ(t_{0}ʻ\alpha\uparrow t_{0}ʻ\alpha)=t_{00}ʻ\alpha=tʻ(\alpha\uparrow\alpha)=t_{0}ʻ \text{Rl}ʻ(\alpha\uparrow\alpha)\\ &[\text{*64·5.*61·34.*63·105·11.(*64·01)}]\end{align}\] -/
theorem pm64_54 {A : Set α} :
    (rl (cross (typ₀ A) (typ₀ A)) = typ₀₀ A ∧ typ₀₀ A = typ (cross A A)) ∧
      typ (cross A A) = typ₀ (rl (cross A A)) := by
  typ_simp

/-- ✱64·55. \(\vdash:CʻP\subset t_{0}ʻ\alpha.\equiv.P\in t_{00}ʻ\alpha\) -/
theorem pm64_55 {P : α → α → Prop} {A : Set α} : fld P ⊆ typ₀ A ↔ P ∈ typ₀₀ A := by typ_simp

/-- ✱64·56. \(\vdash.\text{Rl}ʻ (tʻx\uparrow tʻx)=t^{11}ʻx\) -/
theorem pm64_56 {x : α} : rl (cross (typ x) (typ x)) = typ11 x := by typ_simp

/-- ✱64·57. \(\vdash:CʻP\subset tʻx.\equiv.P\in t^{11}ʻx \quad[\text{*64·56.*35·91.*61·2}]\) -/
theorem pm64_57 {P : α → α → Prop} {x : α} : fld P ⊆ typ x ↔ P ∈ typ11 x := by typ_simp

/-- ✱64·6. \(\vdash.tʻP=\text{Rl}ʻ (t_{0}ʻ\text{D}ʻP\uparrow t_{0}ʻ\text{ᗡ}ʻP)\) -/
theorem pm64_6 {P : α → β → Prop} : typ P = rl (cross (typ₀ (dom P)) (typ₀ (codom P))) := by
  typ_simp

/-- ✱64·61. \(\vdash:\text{D}ʻP\in tʻ\alpha.\text{ᗡ}ʻP\in tʻ\beta.\supset.tʻP=tʻ(\alpha\uparrow\beta)\) -/
theorem pm64_61 {P : α → β → Prop} {A : Set α} {B : Set β} :
    dom P ∈ typ A ∧ codom P ∈ typ B → typ P = typ (cross A B) := by
  typ_simp

/-- ✱64·62. \(\vdash:\text{D}ʻP\in tʻ\text{D}ʻQ.\text{ᗡ}ʻP\in tʻ\text{ᗡ}ʻQ.\equiv.P\in tʻQ.\equiv.tʻP=tʻQ\) -/
theorem pm64_62 {P Q : α → β → Prop} :
    (dom P ∈ typ (dom Q) ∧ codom P ∈ typ (codom Q) ↔ P ∈ typ Q) ∧ (P ∈ typ Q ↔ typ P = typ Q) := by
  typ_simp

/-- ✱64·63. \(\vdash:\text{D}ʻP\in tʻ\alpha.\text{ᗡ}ʻP\in tʻ\beta.\equiv.tʻP=tʻ(\alpha\uparrow\beta).\equiv.P\in tʻ(\alpha\uparrow\beta)\) -/
theorem pm64_63 {P : α → β → Prop} {A : Set α} {B : Set β} :
    (dom P ∈ typ A ∧ codom P ∈ typ B ↔ typ P = typ (cross A B)) ∧
      (typ P = typ (cross A B) ↔ P ∈ typ (cross A B)) := by
  typ_simp

/-!
## [✱65] On the typical definition of ambiguous symbols

*(Vol. 1, p. 434)*

> *Summary of* *65.
>
> …

**Lean reading.** In ✱65 `α` and `R` are typically ambiguous *symbols*, and `α_x`, `α(x)`, `R_x`,
`R(x)`, `R_{(x,y)}`, `R(x_y)`, `R(x,y)` give them the type determined by `x` (and `y`): they are
`clsT A x`, `clsT2 A x`, `relT R x`, `relT2 R x`, `relTT R x y`, `relT2T R x y`, `relT2T2 R x y`,
defined as PM defines them (Defs). In Lean every term already has a definite type, so `α`, `R` are
arbitrary terms of the type forced by `x` and `y`, and each of these notations equals `α` or `R`
(`clsT_eq`, `relT_eq`, `relTT_eq`, …); the propositions are proved by these equations.
`sg'{R_{(x,y)}}` is `Rfwd (relTT R x y)` (`sg = graph Rfwd`), and `R⃗(x_y)` is
`relT2T (Rfwd R) x y`. In ✱65·15 the e-text's `γ` must be of the type of `y`, which Lean's typing
enforces.

**Status.** proved (all propositions; ✱65·01–·12 definition; ✱65·15 proved (reading), see its
docstring).
-/

/-- ✱65·01 (Df). \(\alpha_{x}=\alpha\cap tʻx \quad\text{Df}\) -/
theorem pm65_01 {A : Set α} {x : α} : clsT A x = A ∩ typ x := rfl

/-- ✱65·02 (Df). \(\alpha(x)=\alpha\cap tʻtʻx \quad\text{Df}\) -/
theorem pm65_02 {A : Set (Set α)} {x : α} : clsT2 A x = A ∩ typ (typ x) := rfl

/-- ✱65·03 (Df). \(R_{x}=(tʻx)\upharpoonleft R \quad\text{Df}\) -/
theorem pm65_03 {R : α → β → Prop} {x : α} : relT R x = typ x ◁ R := rfl

/-- ✱65·04 (Df). \(R(x)=(t^{2}ʻx)\upharpoonleft R \quad\text{Df}\) -/
theorem pm65_04 {R : Set α → β → Prop} {x : α} : relT2 R x = typ2 x ◁ R := rfl

/-- ✱65·1 (Df). \(R_{(x,y)}=(tʻx)\upharpoonleft R\upharpoonright(tʻy) \quad\text{Df}\) -/
theorem pm65_1 {R : α → β → Prop} {x : α} {y : β} : relTT R x y = typ x ◁ R ↾ typ y := rfl

/-- ✱65·11 (Df). \(R(x_{y})=(t^{2}ʻx)\upharpoonleft R\upharpoonright(tʻy) \quad\text{Df}\) -/
theorem pm65_11 {R : Set α → β → Prop} {x : α} {y : β} :
    relT2T R x y = typ2 x ◁ R ↾ typ y := rfl

/-- ✱65·12 (Df). \(R(x,y)=(t^{2}ʻx)\upharpoonleft R\upharpoonright(t^{2}ʻy) \quad\text{Df}\) -/
theorem pm65_12 {R : Set α → Set β → Prop} {x : α} {y : β} :
    relT2T2 R x y = typ2 x ◁ R ↾ typ2 y := rfl

/-- ✱65·13. \(\vdash:\alpha=\beta_{x}.\equiv.\alpha=tʻx\cap\beta.\equiv.\alpha\subset tʻx.\alpha=\beta\) -/
theorem pm65_13 {A B : Set α} {x : α} :
    (A = clsT B x ↔ A = typ x ∩ B) ∧ (A = typ x ∩ B ↔ A ⊆ typ x ∧ A = B) := by
  simp [clsT, typ_eq_univ]

/-- ✱65·14. \(\vdash:x\in t_{0}ʻ\alpha.\supset.\gamma(x)=\gamma_{\alpha} \quad[\text{*63·53.(*65·01·02)}]\) -/
theorem pm65_14 {G : Set (Set α)} {x : α} {A : Set α} : x ∈ typ₀ A → clsT2 G x = clsT G A := by
  simp [clsT2, clsT, typ_eq_univ]

/-- ✱65·15. \(\vdash:x\in t_{0}ʻ\alpha.\supset.R(x)=R_{\alpha}.R(x_{y})=R_{(\alpha,\gamma)} \quad[\text{*63·53.(*65·03·04·1·11)}]\)

**Status.** proved (reading): by ✱63·53 and the Dfs ✱65·1·11, `R(x_y) = R_{(α,γ)}` holds when
`γ` is of the type of `y` (for `γ = y` in particular); Lean's typing requires `γ` to be of the
type of `y` (it is the second argument of `R_{(α,γ)}`), and the proposition is proved for every
such `γ`. -/
theorem pm65_15 {R : Set α → β → Prop} {x : α} {A : Set α} {y g : β} :
    x ∈ typ₀ A → relT2 R x = relT R A ∧ relT2T R x y = relTT R A g := fun _ =>
  ⟨by rw [relT2_eq, relT_eq], by rw [relT2T_eq, relTT_eq]⟩

/-- ✱65·16. \(\vdash:x\in t_{0}ʻ\alpha.y\in t_{0}ʻ\beta.\supset.R(x,y)=R(x_{\beta})=R_{(\alpha,\beta)} \quad[\text{*63·53.(*65·1·11·12)}]\) -/
theorem pm65_16 {R : Set α → Set β → Prop} {x : α} {y : β} {A : Set α} {B : Set β} :
    x ∈ typ₀ A ∧ y ∈ typ₀ B → relT2T2 R x y = relT2T R x B ∧ relT2T R x B = relTT R A B :=
  fun _ => ⟨by rw [relT2T2_eq, relT2T_eq], by rw [relT2T_eq, relTT_eq]⟩

/-- ✱65·2. \(\vdash.\text{sg}ʻ \{R_{(x,y)}\}=\overrightarrow{R}(x_{y})\) -/
theorem pm65_2 {R : α → β → Prop} {x : α} {y : β} : Rfwd (relTT R x y) = relT2T (Rfwd R) x y := by
  rw [relTT_eq, relT2T_eq]

/-- ✱65·21. \(\vdash.R_{(x,y)}=\{R_{(x,y)}\}_{(x,y)}\) -/
theorem pm65_21 {R : α → β → Prop} {x : α} {y : β} : relTT R x y = relTT (relTT R x y) x y := by
  simp only [relTT_eq]

/-- ✱65·22. \(\vdash.R(x,y)=\{R(x,y)\}(x,y)\) -/
theorem pm65_22 {R : Set α → Set β → Prop} {x : α} {y : β} :
    relT2T2 R x y = relT2T2 (relT2T2 R x y) x y := by
  simp only [relT2T2_eq]

/-- ✱65·23. \(\vdash.R(x_{y})=\{R(x_{y})\}(x_{y})\) -/
theorem pm65_23 {R : Set α → β → Prop} {x : α} {y : β} :
    relT2T R x y = relT2T (relT2T R x y) x y := by
  simp only [relT2T_eq]

/-- ✱65·24. \(\vdash.R_{x}=(R_{x})_{x}\) -/
theorem pm65_24 {R : α → β → Prop} {x : α} : relT R x = relT (relT R x) x := by
  simp only [relT_eq]

/-- ✱65·25. \(\vdash.R(x)=\{R(x)\}(x)\) -/
theorem pm65_25 {R : Set α → β → Prop} {x : α} : relT2 R x = relT2 (relT2 R x) x := by
  simp only [relT2_eq]

/-- ✱65·3. \(\vdash.R_{\beta}ʻʻ \mu=(Rʻʻ \mu)_{\beta}=Rʻʻ \mu\cap tʻ\beta\) -/
theorem pm65_3 {R : α → β → Prop} {b : α} {M : Set β} :
    relT R b ʻʻ M = clsT (R ʻʻ M) b ∧ clsT (R ʻʻ M) b = R ʻʻ M ∩ typ b :=
  ⟨by rw [relT_eq, clsT_eq], rfl⟩

end PrincipiaMathematica
