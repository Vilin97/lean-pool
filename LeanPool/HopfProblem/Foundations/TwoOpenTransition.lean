/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology1
import all LeanPool.HopfProblem.Foundations.TriangleRegularBaseFundamentalGroup
import all LeanPool.HopfProblem.Foundations.FibreTopology
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology1

/-!
# Hopf problem: foundations · two open transition

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private structure
    CoveringComposition.SheetFamily {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (f : E → X) (x : X) (I : Type*) where
  base : Set X
  mem_base : x ∈ base
  isOpen_base : IsOpen base
  sheet : I → Set E
  isOpen_sheet : ∀ i, IsOpen (sheet i)
  disjoint : Pairwise (Disjoint on sheet)
  bijOn : ∀ i, Set.BijOn f (sheet i) base
  preimage_eq : f ⁻¹' base = ⋃ i, sheet i

private theorem CoveringComposition.exists_sheet_family {E X I : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace I] {f : E → X} {x : X} (h : IsEvenlyCovered f x I) :
    ∃ V : Set X,
      x ∈ V ∧
        IsOpen V ∧
          ∃ U : I → Set E,
            (∀ i, IsOpen (U i)) ∧
              Pairwise (Disjoint on U) ∧ (∀ i, Set.BijOn f (U i) V) ∧ f ⁻¹' V = ⋃ i, U i := by
  rcases h with ⟨hd, V, hxV, hV, hfV, H, hH⟩
  let : DiscreteTopology I := hd
  let U : I → Set E := fun i ↦ Subtype.val '' {e : f ⁻¹' V | (H e).2 = i}
  refine ⟨V, hxV, hV, U, ?_, ?_, ?_, ?_⟩
  · intro i
    apply hfV.isOpenMap_subtype_val
    exact (isOpen_discrete ({ i } : Set I)).preimage (continuous_snd.comp H.continuous)
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro e ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hab' : b = a := Subtype.ext hab
    subst b
    exact hij (ha.symm.trans hb)
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · rintro e ⟨a, ha, rfl⟩
      exact a.property
    · rintro e ⟨a, ha, rfl⟩ e' ⟨b, hb, rfl⟩ hab
      apply congrArg Subtype.val
      apply H.injective
      apply Prod.ext
      · apply Subtype.ext
        simpa only [hH] using hab
      · exact ha.trans hb.symm
    · intro y hy
      let a : f ⁻¹' V := H.symm (⟨y, hy⟩, i)
      refine ⟨a, ⟨a, ?_, rfl⟩, ?_⟩
      · change (H (H.symm (⟨y, hy⟩, i))).2 = i
        simp
      · rw [← hH]
        change (H (H.symm (⟨y, hy⟩, i))).1.1 = y
        simp
  · ext e
    constructor
    · intro he
      exact Set.mem_iUnion.mpr ⟨(H ⟨e, he⟩).2, ⟨⟨e, he⟩, rfl, rfl⟩⟩
    · intro he
      obtain ⟨i, a, ha, rfl⟩ := Set.mem_iUnion.mp he
      exact a.property

private theorem CoveringComposition.nonempty_sheetFamily {E X I : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace I] {f : E → X} {x : X} (h : IsEvenlyCovered f x I) :
    Nonempty (SheetFamily f x I) := by
  obtain ⟨V, hx, hV, U, hU, hdisj, hbij, hexh⟩ := exists_sheet_family h
  exact ⟨⟨V, hx, hV, U, hU, hdisj, hbij, hexh⟩⟩

private theorem CoveringComposition.evenlyCovered_of_sheets {E X I : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace I] [DiscreteTopology I] {f : E → X} {x : X}
    (hf : Continuous f) (hfo : IsOpenMap f) (V : Set X) (hx : x ∈ V) (hV : IsOpen V)
    (U : I → Set E) (hU : ∀ i, IsOpen (U i)) (hinj : ∀ i, (U i).InjOn f)
    (hsurj : ∀ i, (U i).SurjOn f V) (hdisj : Pairwise (Disjoint on U))
    (hexh : f ⁻¹' V ⊆ ⋃ i, U i) : IsEvenlyCovered f x I := by
  classical
    cases isEmpty_or_nonempty I with
  | inl hI =>
    exact
      .of_preimage_eq_empty I (hV.mem_nhds hx)
        (Set.eq_empty_of_subset_empty (by simpa using hexh))
  | inr hI =>
    obtain ⟨e, _, _⟩ := hsurj (Classical.arbitrary I) hx
    let : Nonempty E := ⟨e⟩
    have hopen (i : I) {W : Set X} (hWV : W ⊆ V) : IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U i) := by
      refine ⟨fun hW => (hW.preimage hf).inter (hU i), fun hW => ?_⟩
      have himage : f '' (f ⁻¹' W ∩ U i) = W := by
        apply Set.Subset.antisymm
        · rintro _ ⟨z, hz, rfl⟩
          exact hz.1
        · intro y hy
          obtain ⟨z, hz, hzy⟩ := hsurj i (hWV hy)
          exact ⟨z, ⟨by simpa only [Set.mem_preimage, hzy] using hy, hz⟩, hzy⟩
      rw [← himage]
      exact hfo _ hW
    exact .of_trivialization (t := hV.trivializationDiscrete U V hopen hinj hsurj hdisj hexh) hx

private theorem CoveringComposition.evenlyCovered_comp_of_sheet_families {E B X I : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X] [Finite I] {J : I → Type*}
    [∀ i, TopologicalSpace (J i)] [∀ i, DiscreteTopology (J i)] {f : E → B} {g : B → X} {x : X}
    (hf : Continuous f) (hfo : IsOpenMap f) (hg : Continuous g) (hgo : IsOpenMap g)
    (S : SheetFamily g x I) (b : I → B) (hb : ∀ i, b i ∈ S.sheet i) (hgb : ∀ i, g (b i) = x)
    (T : ∀ i, SheetFamily f (b i) (J i)) : IsEvenlyCovered (g ∘ f) x (Sigma J) := by
  classical
  let W : Set X := S.base ∩ ⋂ i, g '' (S.sheet i ∩ (T i).base)
  have hxW : x ∈ W := by
    refine ⟨S.mem_base, Set.mem_iInter.mpr fun i => ?_⟩
    exact ⟨b i, ⟨hb i, (T i).mem_base⟩, hgb i⟩
  have hW : IsOpen W :=
    S.isOpen_base.inter
      (isOpen_iInter_of_finite fun i => hgo _ ((S.isOpen_sheet i).inter (T i).isOpen_base))
  let U : Sigma J → Set E := fun ij => f ⁻¹' S.sheet ij.1 ∩ (T ij.1).sheet ij.2
  apply evenlyCovered_of_sheets (hg.comp hf) (hgo.comp hfo) W hxW hW U
  · intro ij
    exact ((S.isOpen_sheet ij.1).preimage hf).inter ((T ij.1).isOpen_sheet ij.2)
  · intro ij e he e' he' hee'
    exact ((T ij.1).bijOn ij.2).injOn he.2 he'.2 ((S.bijOn ij.1).injOn he.1 he'.1 hee')
  · rintro ⟨i, j⟩ y hy
    obtain ⟨b', hb', hby⟩ := Set.mem_iInter.mp hy.2 i
    obtain ⟨e, he, hfe⟩ := ((T i).bijOn j).surjOn hb'.2
    refine ⟨e, ⟨?_, he⟩, (congrArg g hfe).trans hby⟩
    change f e ∈ S.sheet i
    rw [hfe]
    exact hb'.1
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    apply Set.disjoint_left.mpr
    intro e he he'
    by_cases hii : i = i'
    · cases hii
      have hjj : j ≠ j' := by
        intro h
        cases h
        exact hne rfl
      exact ((T i).disjoint hjj).le_bot ⟨he.2, he'.2⟩
    · exact (S.disjoint hii).le_bot ⟨he.1, he'.1⟩
  · intro e he
    change g (f e) ∈ W at he
    have houter : f e ∈ g ⁻¹' S.base := he.1
    rw [S.preimage_eq] at houter
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp houter
    obtain ⟨b', hb', hgEq⟩ := Set.mem_iInter.mp he.2 i
    have heq : f e = b' := (S.bijOn i).injOn hi hb'.1 hgEq.symm
    have hinner : e ∈ f ⁻¹' (T i).base := by
      change f e ∈ (T i).base
      rw [heq]
      exact hb'.2
    rw [(T i).preimage_eq] at hinner
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hinner
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, ⟨hi, hj⟩⟩

public
theorem CoveringComposition.covering_comp_of_finite_fibres {E B X : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace X] {f : E → B} {g : B → X} (hf : IsCoveringMap f)
    (hg : IsCoveringMap g) (hfin : ∀ x, Finite (g ⁻¹' { x })) : IsCoveringMap (g ∘ f) := by
  classical
  intro x
  let I := g ⁻¹' { x }
  let : Finite I := hfin x
  let S : SheetFamily g x I := Classical.choice (nonempty_sheetFamily (hg x))
  have hbex : ∀ i : I, ∃ b ∈ S.sheet i, g b = x := fun i => (S.bijOn i).surjOn S.mem_base
  choose b hb hgb using hbex
  let : ∀ i : I, DiscreteTopology (f ⁻¹' {b i}) := fun i => (hf (b i)).1
  let T : ∀ i : I, SheetFamily f (b i) (f ⁻¹' {b i}) := fun i =>
    Classical.choice (nonempty_sheetFamily (hf (b i)))
  exact
    (evenlyCovered_comp_of_sheet_families hf.continuous hf.isOpenMap hg.continuous hg.isOpenMap S
        b hb hgb T).to_isEvenlyCovered_preimage

private structure HolomorphicCharacterBundle.TransitionData (M : Type*) [TopologicalSpace M]
    (ι : Type*) where
  baseSet : ι → Set M
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : M → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  transition : ι → ι → M → ℂˣ
  transition_self : ∀ i x, x ∈ baseSet i → transition i i x = 1
  transition_comp :
    ∀ i j k x,
      x ∈ baseSet i ∩ baseSet j ∩ baseSet k →
        transition j k x * transition i j x = transition i k x
  continuousOn_transition :
    ∀ i j, ContinuousOn (fun x => (transition i j x : ℂ)) (baseSet i ∩ baseSet j)

private def HolomorphicCharacterBundle.TransitionData.core {M ι : Type*} [TopologicalSpace M]
    (A : HolomorphicCharacterBundle.TransitionData M ι) : VectorBundleCore ℂ M ℂ ι
    where
  baseSet := A.baseSet
  isOpen_baseSet := A.isOpen_baseSet
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_baseSet_at
  coordChange i j x := (A.transition i j x : ℂ) • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i x hx v := by simp [A.transition_self i x hx]
  continuousOn_coordChange i j := (A.continuousOn_transition i j).smul continuousOn_const
  coordChange_comp i j k x hx
    v := by
    change
      (A.transition j k x : ℂ) * ((A.transition i j x : ℂ) * v) = (A.transition i k x : ℂ) * v
    rw [← mul_assoc, ← Units.val_mul, A.transition_comp i j k x hx]



private def restrictedRetractionInclusion {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (K : Set X) (hinc : Set.range i ⊆ K) : C(A, K)
    where
  toFun a := ⟨i a, hinc ⟨a, rfl⟩⟩
  continuous_toFun := i.continuous.subtype_mk _

private def
    restrictedRetraction {A X : Type*} [TopologicalSpace A] [TopologicalSpace X] (r : C(X, A))
    (K : Set X) : C(K, A) where
  toFun x := r x
  continuous_toFun := r.continuous.comp continuous_subtype_val

private theorem restrictedRetraction_comp_inclusion {A X : Type*} [TopologicalSpace A]
    [TopologicalSpace X] (i : C(A, X)) (r : C(X, A)) (hir : r.comp i = ContinuousMap.id A)
    (K : Set X) (hinc : Set.range i ⊆ K) :
    (restrictedRetraction r K).comp (restrictedRetractionInclusion i K hinc) =
      ContinuousMap.id A := by
  ext a
  exact retraction_leftInverse i r hir a

private def restrictedRetractionHomotopy {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (r : C(X, A)) (H : (ContinuousMap.id X).HomotopyRel (i.comp r) (Set.range i))
    (K : Set X) (hinc : Set.range i ⊆ K) (hstable : ∀ t x, x ∈ K → H (t, x) ∈ K) :
    (ContinuousMap.id K).HomotopyRel
      ((restrictedRetractionInclusion i K hinc).comp (restrictedRetraction r K))
      (Set.range (restrictedRetractionInclusion i K hinc))
    where
  toFun tx := ⟨H (tx.1, tx.2.val), hstable tx.1 tx.2.val tx.2.property⟩
  continuous_toFun :=
    (H.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _
  map_zero_left x := Subtype.ext (H.map_zero_left x.val)
  map_one_left x := Subtype.ext (H.map_one_left x.val)
  prop' t x
    hx := by
    apply Subtype.ext
    apply H.eq_fst t
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, rfl⟩

private theorem
    TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.memV_of_not_memU {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    {x : X} (hx : x ∉ D.U) : x ∈ D.V := by
  have h : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  exact h.resolve_left hx

private def TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedSection {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (x : X) : Path.Homotopic.Quotient D.base x := by
  classical
    exact
    if hx : x ∈ D.U then Path.Homotopic.Quotient.mk (D.pathU x hx)
    else Path.Homotopic.Quotient.mk (D.pathV x (D.memV_of_not_memU hx))

private theorem
    TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedSection_eq_U {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    {x : X} (hx : x ∈ D.U) : D.basedSection x = Path.Homotopic.Quotient.mk (D.pathU x hx) := by
  simp only [basedSection, dite_eq_left hx]

private theorem
    TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedSection_eq_V {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    {x : X} (hxU : x ∉ D.U) (hxV : x ∈ D.V) :
    D.basedSection x = Path.Homotopic.Quotient.mk (D.pathV x hxV) := by
  simp only [basedSection, dite_eq_right hxU]

@[simp]
private theorem
    TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedSection_base {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X) :
    D.basedSection D.base = Path.Homotopic.Quotient.refl D.base := by
  rw [D.basedSection_eq_U D.baseU]
  apply Path.Homotopic.Quotient.eq.mpr
  exact SimplyConnectedCover.homotopic_of_mem D.simplyU _ _ (D.pathU_mem _ _) (fun _ => D.baseU)

private theorem
    TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.comparisonU_mem {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base)) {x : X} (hx : x ∈ D.U) :
    TriangleRegularBaseFundamentalGroup.pathDifference (D.basedSection x)
        (Path.Homotopic.Quotient.mk (D.pathU x hx)) ∈
      H := by
  rw [D.basedSection_eq_U hx]
  simpa only [TriangleRegularBaseFundamentalGroup.pathDifference,
    Path.Homotopic.Quotient.trans_symm, FundamentalGroup.one_def] using H.one_mem

private theorem
    TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.comparisonV_mem {X : Type*}
    [TopologicalSpace X] (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H) {x : X}
    (hx : x ∈ D.V) :
    TriangleRegularBaseFundamentalGroup.pathDifference (D.basedSection x)
        (Path.Homotopic.Quotient.mk (D.pathV x hx)) ∈
      H := by
  by_cases hxU : x ∈ D.U
  · rw [D.basedSection_eq_U hxU]
    exact hH x hxU hx
  · rw [D.basedSection_eq_V hxU hx]
    simpa only [TriangleRegularBaseFundamentalGroup.pathDifference,
      Path.Homotopic.Quotient.trans_symm, FundamentalGroup.one_def] using H.one_mem

private theorem
    TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedLoop_mem_of_path_in_U
    {X : Type*} [TopologicalSpace X]
    (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base)) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.U) :
    TriangleRegularBaseFundamentalGroup.basedLoop D.basedSection (Path.Homotopic.Quotient.mk p) ∈
      H := by
  have hx : x ∈ D.U := by simpa using hp 0
  have hy : y ∈ D.U := by simpa using hp 1
  rw [TriangleRegularBaseFundamentalGroup.basedLoop_comparison D.basedSection
      (Path.Homotopic.Quotient.mk (D.pathU x hx)) (Path.Homotopic.Quotient.mk (D.pathU y hy))
      (Path.Homotopic.Quotient.mk p) (D.pathU_trans hx hy p hp)]
  exact H.mul_mem (H.inv_mem (D.comparisonU_mem H hy)) (D.comparisonU_mem H hx)

private theorem
    TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.basedLoop_mem_of_path_in_V
    {X : Type*} [TopologicalSpace X]
    (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H) {x y : X}
    (p : Path x y) (hp : ∀ t, p t ∈ D.V) :
    TriangleRegularBaseFundamentalGroup.basedLoop D.basedSection (Path.Homotopic.Quotient.mk p) ∈
      H := by
  have hx : x ∈ D.V := by simpa using hp 0
  have hy : y ∈ D.V := by simpa using hp 1
  rw [TriangleRegularBaseFundamentalGroup.basedLoop_comparison D.basedSection
      (Path.Homotopic.Quotient.mk (D.pathV x hx)) (Path.Homotopic.Quotient.mk (D.pathV y hy))
      (Path.Homotopic.Quotient.mk p) (D.pathV_trans hx hy p hp)]
  exact H.mul_mem (H.inv_mem (D.comparisonV_mem H hH hy)) (D.comparisonV_mem H hH hx)

private theorem
  TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.subgroup_eq_top_of_switchClass_mem
    {X : Type*} [TopologicalSpace X]
    (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H) : H = ⊤ := by
  let W : Bool → Set X := fun b => if b then D.V else D.U
  have hopen : ∀ b, IsOpen (W b) := by
    intro b
    cases b
    · exact D.U.isOpen
    · exact D.V.isOpen
  have hcover : ⋃ b, W b = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
    · exact Set.mem_iUnion.mpr ⟨Bool.true, hx⟩
  have hall :
    ∀ {x y : X} (q : Path.Homotopic.Quotient x y),
      TriangleRegularBaseFundamentalGroup.basedLoop D.basedSection q ∈ H := by
    apply
      TriangleRegularBaseFundamentalGroup.pathClass_induction_of_open_cover W hopen hcover
        (fun q => TriangleRegularBaseFundamentalGroup.basedLoop D.basedSection q ∈ H)
    · intro x
      rw [TriangleRegularBaseFundamentalGroup.basedLoop_refl]
      exact H.one_mem
    · intro x y z p q hp hq
      rw [TriangleRegularBaseFundamentalGroup.basedLoop_trans]
      exact H.mul_mem hq hp
    · intro b x y p hp
      cases b
      · exact D.basedLoop_mem_of_path_in_U H p (fun t => hp ⟨t, rfl⟩)
      · exact D.basedLoop_mem_of_path_in_V H hH p (fun t => hp ⟨t, rfl⟩)
  apply top_unique
  intro q _
  have hq := hall q
  have hrefl : (Path.Homotopic.Quotient.refl D.base).symm = Path.Homotopic.Quotient.refl D.base :=
    by
    change (1 : FundamentalGroup X D.base)⁻¹ = 1
    exact inv_one
  simpa only [TriangleRegularBaseFundamentalGroup.basedLoop, D.basedSection_base,
    Path.Homotopic.Quotient.refl_trans, hrefl, Path.Homotopic.Quotient.trans_refl] using hq

private theorem TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover.switchClass_eq_of_paths
    {X : Type*} [TopologicalSpace X]
    (D : TriangleRegularBaseFundamentalGroup.TwoSimplyConnectedCover X) {x : X} (hxU : x ∈ D.U)
    (hxV : x ∈ D.V) (p q : Path D.base x) (hp : ∀ t, p t ∈ D.U) (hq : ∀ t, q t ∈ D.V) :
    D.switchClass x hxU hxV =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.trans q.symm)) := by
  have hU : Path.Homotopic.Quotient.mk (D.pathU x hxU) = Path.Homotopic.Quotient.mk p :=
    Path.Homotopic.Quotient.eq.mpr
      (SimplyConnectedCover.homotopic_of_mem D.simplyU _ _ (D.pathU_mem x hxU) hp)
  have hV : Path.Homotopic.Quotient.mk (D.pathV x hxV) = Path.Homotopic.Quotient.mk q :=
    Path.Homotopic.Quotient.eq.mpr
      (SimplyConnectedCover.homotopic_of_mem D.simplyV _ _ (D.pathV_mem x hxV) hq)
  simp only [switchClass, hU, hV, FundamentalGroup.fromPath, FundamentalGroup.fromArrow,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]

private structure TwoOpenTransition (X G : Type*) [TopologicalSpace X] [TopologicalSpace G] where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  cover : (U : Set X) ∪ (V : Set X) = Set.univ
  transition : X → G
  continuousOn_transition : ContinuousOn transition ((U : Set X) ∩ (V : Set X))

private def TwoOpenTransition.baseSet {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) : Bool → Set X
  | false => D.U
  | true => D.V

@[simp]
private theorem
    TwoOpenTransition.baseSet_false {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) : D.baseSet Bool.false = (D.U : Set X) :=
  rfl

@[simp]
private theorem
    TwoOpenTransition.baseSet_true {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) : D.baseSet Bool.true = (D.V : Set X) :=
  rfl

private def TwoOpenTransition.indexAt {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) (x : X) : Bool := by
  classical exact if x ∈ D.U then Bool.false else Bool.true

@[simp]
private theorem
    TwoOpenTransition.indexAt_of_mem_U {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) {x : X} (hx : x ∈ D.U) : D.indexAt x = Bool.false := by
  simp [indexAt, hx]

@[simp]
private theorem TwoOpenTransition.indexAt_of_not_mem_U {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] (D : TwoOpenTransition X G) {x : X} (hx : x ∉ D.U) :
    D.indexAt x = Bool.true := by simp [indexAt, hx]

private theorem TwoOpenTransition.mem_baseSet_indexAt {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] (D : TwoOpenTransition X G) (x : X) : x ∈ D.baseSet (D.indexAt x) := by
  by_cases hx : x ∈ D.U
  · simpa only [D.indexAt_of_mem_U hx, baseSet_false, SetLike.mem_coe] using hx
  · have hcover : x ∈ (D.U : Set X) ∪ (D.V : Set X) := by
      rw [D.cover]
      exact Set.mem_univ x
    simpa only [D.indexAt_of_not_mem_U hx, baseSet_true] using hcover.resolve_left hx

private def TwoOpenTransition.coordChange {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] : Bool → Bool → X → G → G
  | false, Bool.false, _, w => w
  | false, Bool.true, x, w => w * D.transition x
  | true, Bool.false, x, w => w * (D.transition x)⁻¹
  | true, Bool.true, _, w => w

@[simp]
private theorem
    TwoOpenTransition.coordChange_self {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] (i : Bool) (x : X) (w : G) :
    D.coordChange i i x w = w := by cases i <;> rfl

private theorem
    TwoOpenTransition.coordChange_comp {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] (i j k : Bool) (x : X) (w : G) :
    D.coordChange j k x (D.coordChange i j x w) = D.coordChange i k x w := by
  cases i <;> cases j <;> cases k <;> simp [coordChange, mul_assoc]

private theorem TwoOpenTransition.coordChange_mul_left {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] (D : TwoOpenTransition X G) [Group G] (i j : Bool) (x : X) (g w : G) :
    D.coordChange i j x (g * w) = g * D.coordChange i j x w := by
  cases i <;> cases j <;> simp [coordChange, mul_assoc]

private theorem TwoOpenTransition.continuousOn_coordChange {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (i j : Bool) :
    ContinuousOn (fun p : X × G => D.coordChange i j p.1 p.2)
      ((D.baseSet i ∩ D.baseSet j) ×ˢ Set.univ) := by
  cases i <;> cases j
  · exact continuous_snd.continuousOn
  · exact
      continuous_snd.continuousOn.mul
        (D.continuousOn_transition.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  · exact
      continuous_snd.continuousOn.mul
        (D.continuousOn_transition.comp continuous_fst.continuousOn
            (fun _ hp => ⟨hp.1.2, hp.1.1⟩)).inv
  · exact continuous_snd.continuousOn

private def TwoOpenTransition.core {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] : FiberBundleCore Bool X G
    where
  baseSet := D.baseSet
  isOpen_baseSet := by
    intro i
    cases i
    · exact D.U.isOpen
    · exact D.V.isOpen
  indexAt := D.indexAt
  mem_baseSet_at := D.mem_baseSet_indexAt
  coordChange := D.coordChange
  coordChange_self := fun i x _ w => D.coordChange_self i x w
  continuousOn_coordChange := D.continuousOn_coordChange
  coordChange_comp := fun i j k x _ w => D.coordChange_comp i j k x w

private abbrev TwoOpenTransition.TotalSpace {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] :=
  D.core.TotalSpace

private abbrev TwoOpenTransition.proj {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] : D.TotalSpace → X :=
  D.core.proj

private abbrev TwoOpenTransition.localTrivU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] : Bundle.Trivialization G D.proj :=
  D.core.localTriv Bool.false

private abbrev TwoOpenTransition.localTrivV {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] : Bundle.Trivialization G D.proj :=
  D.core.localTriv Bool.true

private def TwoOpenTransition.pointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (x : X) (g : G) : D.TotalSpace :=
  D.localTrivU.toOpenPartialHomeomorph.symm (x, g)

private def TwoOpenTransition.pointV {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (x : X) (g : G) : D.TotalSpace :=
  D.localTrivV.toOpenPartialHomeomorph.symm (x, g)

@[simp]
private theorem
    TwoOpenTransition.proj_pointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (x : X) (g : G) :
    D.proj (D.pointU x g) = x :=
  rfl

@[simp]
private theorem
    TwoOpenTransition.proj_pointV {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (x : X) (g : G) :
    D.proj (D.pointV x g) = x :=
  rfl

private theorem
    TwoOpenTransition.pointU_eq_pointV {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (x : X) (g : G)
    (hx : x ∈ (D.U : Set X) ∩ (D.V : Set X)) : D.pointU x g = D.pointV x (g * D.transition x) := by
  change
    (⟨x, D.core.coordChange Bool.false (D.core.indexAt x) x g⟩ : D.TotalSpace) =
      ⟨x, D.core.coordChange Bool.true (D.core.indexAt x) x (g * D.transition x)⟩
  apply congrArg (fun w : G => (⟨x, w⟩ : D.TotalSpace))
  exact
    (D.core.coordChange_comp Bool.false Bool.true (D.core.indexAt x) x
        ⟨⟨hx.1, hx.2⟩, D.core.mem_baseSet_at x⟩ g).symm

private theorem
    TwoOpenTransition.isCoveringMap {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] : IsCoveringMap D.proj := by
  exact FiberBundle.isCoveringMap (F := G) (E := D.core.Fiber)

private instance
    TwoOpenTransition.totalMulAction {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) : MulAction G D.TotalSpace
    where
  smul g p := ⟨p.proj, g * (show G from p.2)⟩
  one_smul
    p := by
    rcases p with ⟨b, v⟩
    change G at v
    change (⟨b, 1 * v⟩ : D.TotalSpace) = ⟨b, v⟩
    exact congrArg (fun w : G => (⟨b, w⟩ : D.TotalSpace)) (one_mul v)
  mul_smul g h
    p := by
    rcases p with ⟨b, v⟩
    change G at v
    change (⟨b, (g * h) * v⟩ : D.TotalSpace) = ⟨b, g * (h * v)⟩
    exact congrArg (fun w : G => (⟨b, w⟩ : D.TotalSpace)) (mul_assoc g h v)

private theorem
    TwoOpenTransition.localTriv_smul {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (i : Bool) (g : G)
    (p : D.TotalSpace) : D.core.localTriv i (g • p) = (D.proj p, g * (D.core.localTriv i p).2) := by
  apply Prod.ext
  · rfl
  exact D.coordChange_mul_left _ _ _ _ _

@[simp]
private theorem
    TwoOpenTransition.smul_pointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (g : G) (x : X) (w : G) :
    g • D.pointU x w = D.pointU x (g * w) := by
  change
    (⟨x, g * D.coordChange Bool.false (D.indexAt x) x w⟩ : D.TotalSpace) =
      ⟨x, D.coordChange Bool.false (D.indexAt x) x (g * w)⟩
  exact
    congrArg (fun v : G => (⟨x, v⟩ : D.TotalSpace))
      (D.coordChange_mul_left Bool.false (D.indexAt x) x g w).symm

private instance TwoOpenTransition.totalContinuousConstSMul {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) :
    ContinuousConstSMul G D.TotalSpace where
  continuous_const_smul
    g := by
    apply continuous_iff_continuousAt.mpr
    intro p
    let e := D.core.localTriv (D.core.indexAt p.proj)
    have he : D.proj p ∈ e.baseSet := D.core.mem_baseSet_at p.proj
    have hecont : ContinuousAt e p := e.continuousAt (e.mem_source.mpr he)
    apply
      e.continuousAt_of_comp_left
        (show ContinuousAt (D.proj ∘ (g • ·)) p from D.core.continuous_proj.continuousAt) he
    convert
      D.core.continuous_proj.continuousAt.prodMk
        ((show ContinuousAt (fun _ : D.TotalSpace => g) p from continuousAt_const).mul
          hecont.snd) using
      1
    funext q
    exact D.localTriv_smul _ _ _

private instance TwoOpenTransition.totalIsCancelSMul {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) :
    IsCancelSMul G D.TotalSpace where
  right_cancel' g h p
    he := by
    have he' := congrArg (fun q : D.TotalSpace => (q.2 : G)) he
    exact mul_right_cancel he'

private theorem TwoOpenTransition.proj_eq_iff_mem_orbit {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G)
    {p q : D.TotalSpace} : D.proj p = D.proj q ↔ p ∈ MulAction.orbit G q := by
  constructor
  · cases p with
    | mk b w =>
      cases q with
      | mk c v =>
        change G at w v
        intro h
        change b = c at h
        subst c
        refine ⟨w * v⁻¹, ?_⟩
        change (⟨b, (w * v⁻¹) * v⟩ : D.TotalSpace) = ⟨b, w⟩
        exact congrArg (fun z : G => (⟨b, z⟩ : D.TotalSpace)) (inv_mul_cancel_right w v)
  · rintro ⟨g, rfl⟩
    rfl

private theorem TwoOpenTransition.isQuotientCoveringMap {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) :
    IsQuotientCoveringMap D.proj G := by
  apply (isQuotientCoveringMap_iff_isCoveringMap_and D.proj G).mpr
  exact
    ⟨D.isCoveringMap, fun x => ⟨D.pointU x 1, D.proj_pointU x 1⟩, inferInstance, inferInstance,
      D.proj_eq_iff_mem_orbit⟩

private def TwoOpenTransition.chartPath_mo1973_23734 {E X F : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace F] {p : E → X} (e : Bundle.Trivialization F p)
    {b c : X} (γ : Path b c) (hγ : ∀ s, γ s ∈ e.baseSet) (v : F) :
    Path (e.toOpenPartialHomeomorph.symm (b, v)) (e.toOpenPartialHomeomorph.symm (c, v))
    where
  toFun s := e.toOpenPartialHomeomorph.symm (γ s, v)
  continuous_toFun := e.continuousOn_symm_prodMk_left.comp_continuous γ.continuous hγ
  source' := by simp
  target' := by simp

private theorem TwoOpenTransition.chartPath_monodromy_mo1973_23735 {E X F : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace F] {p : E → X}
    (hp : IsCoveringMap p) (e : Bundle.Trivialization F p) {b c : X} (γ : Path b c)
    (hγ : ∀ s, γ s ∈ e.baseSet) (hb : b ∈ e.baseSet) (hc : c ∈ e.baseSet) (v : F) :
    hp.monodromy (.mk γ) ⟨e.toOpenPartialHomeomorph.symm (b, v), e.proj_symm_apply' hb⟩ =
      ⟨e.toOpenPartialHomeomorph.symm (c, v), e.proj_symm_apply' hc⟩ := by
  apply hp.monodromy_eq_of_map_eq (.mk (chartPath_mo1973_23734 e γ hγ v))
  apply congrArg Path.Homotopic.Quotient.mk
  ext s
  exact e.proj_symm_apply' (hγ s)

private def TwoOpenTransition.fiberPointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X) (g : G) :
    D.proj ⁻¹' { b } :=
  ⟨D.pointU b g, D.proj_pointU b g⟩

private def TwoOpenTransition.fiberPointV {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X) (g : G) :
    D.proj ⁻¹' { b } :=
  ⟨D.pointV b g, D.proj_pointV b g⟩

@[simp]
private theorem
    TwoOpenTransition.fiberPointU_val {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X) (g : G) :
    (D.fiberPointU b g : D.TotalSpace) = D.pointU b g :=
  rfl

private theorem
    TwoOpenTransition.pointV_eq_pointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X) (g : G)
    (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X)) :
    D.pointV b g = D.pointU b (g * (D.transition b)⁻¹) := by
  simpa only [inv_mul_cancel_right] using (D.pointU_eq_pointV b (g * (D.transition b)⁻¹) hb).symm

private theorem TwoOpenTransition.fiberPointU_eq_fiberPointV {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X)
    (g : G) (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X)) :
    D.fiberPointU b g = D.fiberPointV b (g * D.transition b) :=
  Subtype.ext (D.pointU_eq_pointV b g hb)

private theorem TwoOpenTransition.fiberPointV_eq_fiberPointU {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X)
    (g : G) (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X)) :
    D.fiberPointV b g = D.fiberPointU b (g * (D.transition b)⁻¹) :=
  Subtype.ext (D.pointV_eq_pointU b g hb)

private theorem TwoOpenTransition.monodromy_of_path_U {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) {b c : X}
    (α : Path b c) (hα : ∀ s, α s ∈ D.U) (g : G) :
    D.isCoveringMap.monodromy (.mk α) (D.fiberPointU b g) = D.fiberPointU c g := by
  have hbase : D.localTrivU.baseSet = D.U := rfl
  exact
    chartPath_monodromy_mo1973_23735 D.isCoveringMap D.localTrivU α hα
      (by simpa [hbase] using hα 0) (by simpa [hbase] using hα 1) g

private theorem TwoOpenTransition.monodromy_of_path_V {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) {b c : X}
    (β : Path b c) (hβ : ∀ s, β s ∈ D.V) (g : G) :
    D.isCoveringMap.monodromy (.mk β) (D.fiberPointV b g) = D.fiberPointV c g := by
  have hbase : D.localTrivV.baseSet = D.V := rfl
  exact
    chartPath_monodromy_mo1973_23735 D.isCoveringMap D.localTrivV β hβ
      (by simpa [hbase] using hβ 0) (by simpa [hbase] using hβ 1) g

private theorem TwoOpenTransition.monodromy_trans_U_V {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) {b c : X}
    (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X)) (hc : c ∈ (D.U : Set X) ∩ (D.V : Set X))
    (α : Path b c) (β : Path c b) (hα : ∀ s, α s ∈ D.U) (hβ : ∀ s, β s ∈ D.V) (g : G) :
    D.isCoveringMap.monodromy (.mk (α.trans β)) (D.fiberPointU b g) =
      D.fiberPointU b ((g * D.transition c) * (D.transition b)⁻¹) := by
  rw [Path.Homotopic.Quotient.mk_trans, D.isCoveringMap.monodromy_trans_apply,
    D.monodromy_of_path_U α hα g, D.fiberPointU_eq_fiberPointV c g hc, D.monodromy_of_path_V β hβ,
    D.fiberPointV_eq_fiberPointU b _ hb]

private def
    TwoOpenTransition.basepointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G] [Group G]
    [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X) (hb : b ∈ D.U) : D.proj ⁻¹' { b } :=
  ⟨D.pointU b 1, D.localTrivU.proj_symm_apply' hb⟩

@[simp]
private theorem TwoOpenTransition.basepointU_eq_fiberPointU {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X)
    (hb : b ∈ D.U) : D.basepointU b hb = D.fiberPointU b 1 :=
  rfl

private def TwoOpenTransition.fundamentalGroupToMulOpposite {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X)
    (hb : b ∈ D.U) : FundamentalGroup X b →* Gᵐᵒᵖ :=
  D.isQuotientCoveringMap.fundamentalGroupToMulOpposite (D.basepointU b hb)

private theorem TwoOpenTransition.fundamentalGroupToMulOpposite_trans_U_V {X G : Type*}
    [TopologicalSpace X] [TopologicalSpace G] [Group G] [DiscreteTopology G]
    (D : TwoOpenTransition X G) {b c : X} (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X))
    (hc : c ∈ (D.U : Set X) ∩ (D.V : Set X)) (α : Path b c) (β : Path c b) (hα : ∀ s, α s ∈ D.U)
    (hβ : ∀ s, β s ∈ D.V) :
    D.fundamentalGroupToMulOpposite b hb.1 (.mk (α.trans β)) =
      MulOpposite.op (D.transition c * (D.transition b)⁻¹) := by
  apply (D.isQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  have hm := congrArg Subtype.val (D.monodromy_trans_U_V hb hc α β hα hβ 1)
  simpa only [MulOpposite.unop_op, basepointU_eq_fiberPointU, smul_pointU, mul_one, one_mul,
    fiberPointU_val] using hm.symm

private def FreeMeridianMarking.inversionHom_mo1973_23782 : FreeGroup Bool →* FreeGroup Bool :=
  FreeGroup.lift (fun b => (FreeGroup.of b)⁻¹)

@[simp]
private theorem FreeMeridianMarking.inversionHom_of_mo1973_23783 (b : Bool) :
    inversionHom_mo1973_23782 (FreeGroup.of b) = (FreeGroup.of b)⁻¹ :=
  FreeGroup.lift_apply_of

private theorem FreeMeridianMarking.inversionHom_involutive_mo1973_23784 :
    Function.Involutive inversionHom_mo1973_23782 := by
  have h :
    inversionHom_mo1973_23782.comp inversionHom_mo1973_23782 = MonoidHom.id (FreeGroup Bool) := by
    apply FreeGroup.ext_hom
    intro b
    simp only [MonoidHom.comp_apply, inversionHom_of_mo1973_23783, map_inv, inv_inv,
      MonoidHom.id_apply]
  exact fun w => DFunLike.congr_fun h w

private def FreeMeridianMarking.invertGenerators : FreeGroup Bool ≃* FreeGroup Bool
    where
  __ := inversionHom_mo1973_23782
  invFun := inversionHom_mo1973_23782
  left_inv := inversionHom_involutive_mo1973_23784
  right_inv := inversionHom_involutive_mo1973_23784

@[simp]
private theorem FreeMeridianMarking.invertGenerators_of (b : Bool) :
    invertGenerators (FreeGroup.of b) = (FreeGroup.of b)⁻¹ :=
  inversionHom_of_mo1973_23783 b

@[simp]
private theorem
    FreeMeridianMarking.invertGenerators_symm : invertGenerators.symm = invertGenerators := by
  ext w
  rfl

private def FreeMeridianMarking.conditionalInversion : Bool → (FreeGroup Bool ≃* FreeGroup Bool)
  | false => MulEquiv.refl _
  | true => invertGenerators

private def FreeMeridianMarking.reorient {K : Type*} [Group K] (e : K ≃* FreeGroup Bool)
    (reverse : Bool) : K ≃* FreeGroup Bool :=
  e.trans (conditionalInversion reverse)

@[simp]
private theorem FreeMeridianMarking.reorient_symm_of {K : Type*} [Group K] (e : K ≃* FreeGroup Bool)
    (reverse b : Bool) :
    (reorient e reverse).symm (FreeGroup.of b) =
      if reverse then (e.symm (FreeGroup.of b))⁻¹ else e.symm (FreeGroup.of b) := by
  cases reverse <;> simp [conditionalInversion, reorient]

end Mathoverflow1973

end
