/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.Core3
public import LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3

/-!
# Hopf problem: period family · holomorphic period map 1

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

private abbrev
    HolomorphicPeriodMap.TotalSpace {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (_P : HolomorphicPeriodMap V B) :=
  B × RealTorus₄

private def HolomorphicPeriodMap.quotientMap {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    (B × ComplexPlane₂) → P.TotalSpace := fun x =>
  (x.1, standardLattice.mkQ ((P.periodEquiv x.1).symm x.2))

private theorem
    HolomorphicPeriodMap.quotientMap_localHomeomorph {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    IsLocalHomeomorph P.quotientMap := by
  have : DiscreteTopology standardLattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology standardLattice)
  have h :=
    (AddSubgroup.isAddQuotientCoveringMap_of_comm standardLattice.toAddSubgroup
        DiscreteTopology.isDiscrete).isCoveringMap.isLocalHomeomorph
  exact (localHomeomorph_prod_id (B := B) h).comp P.realTrivialization.isLocalHomeomorph

private theorem HolomorphicPeriodMap.quotientMap_surjective {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Function.Surjective P.quotientMap := by
  rintro ⟨b, z⟩
  obtain ⟨v, hv⟩ := standardLattice.mkQ_surjective z
  refine ⟨(b, P.periodEquiv b v), ?_⟩
  simpa [quotientMap] using congrArg (Prod.mk b) hv

private theorem HolomorphicPeriodMap.periodEquiv_coordinates {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) (v : RealPlane₄) :
    P.periodEquiv b v =
      ![6 * (P.point b).val.μ * (v 0) + (P.point b).val.τ * (v 1) + (v 2),
        (P.point b).val.β * (v 0) + (P.point b).val.μ * (v 1) + (v 3)] := by
  rw [periodEquiv_apply]
  ext i : 1
  fin_cases i <;> apply Complex.ext <;>
    simp [complexCoordinates, PeriodPoint.realMatrix, dotProduct, Fin.sum_univ_four,
      Complex.mul_re, Complex.mul_im]

private theorem
    HolomorphicPeriodMap.holomorphic_periodEquiv_const {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (v : RealPlane₄) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (fun b => P.periodEquiv b v) := by
  simp_rw [periodEquiv_coordinates]
  apply contMDiff_pi_space.mpr
  intro i
  fin_cases i
  · exact
      (((contMDiff_const.mul P.holomorphic_mu).mul contMDiff_const).add
            (P.holomorphic_tau.mul contMDiff_const)).add
        contMDiff_const
  · exact
      ((P.holomorphic_beta.mul contMDiff_const).add (P.holomorphic_mu.mul contMDiff_const)).add
        contMDiff_const

private theorem HolomorphicPeriodMap.periodEquiv_map_lattice {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) :
    standardLattice.map ((P.periodEquiv b).restrictScalars ℤ).toLinearMap = (P.point b).lattice :=
  by
  rw [standardLattice, Submodule.map_span, PeriodDomain.lattice_eq_span_basis]
  congr 1
  rw [← Set.range_comp]
  congr 1

@[instance_reducible]
private def
    HolomorphicPeriodMap.coveringAction {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    MulAction (Multiplicative standardLattice) (B × ComplexPlane₂)
    where
  smul g x := (x.1, x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄))
  one_smul
    x := by
    change
      (x.1, x.2 + P.periodEquiv x.1 ((1 : Multiplicative standardLattice).toAdd : RealPlane₄)) = x
    simp
  mul_smul g h
    x := by
    change
      (x.1, x.2 + P.periodEquiv x.1 ((g * h).toAdd : RealPlane₄)) =
        (x.1,
          (x.2 + P.periodEquiv x.1 (h.toAdd : RealPlane₄)) +
            P.periodEquiv x.1 (g.toAdd : RealPlane₄))
    simp [map_add, add_left_comm, add_comm]

private theorem HolomorphicPeriodMap.realTrivialization_smul {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (g : Multiplicative standardLattice) (x : B × ComplexPlane₂) :
    letI := P.coveringAction
    P.realTrivialization (g • x) = (x.1, (P.periodEquiv x.1).symm x.2 + (g.toAdd : RealPlane₄)) :=
  by
  let := P.coveringAction
  change (x.1, (P.periodEquiv x.1).symm (x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄))) = _
  simp only [map_add, LinearEquiv.symm_apply_apply]

private theorem HolomorphicPeriodMap.coveringAction_continuous {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    letI := P.coveringAction
    ContinuousConstSMul (Multiplicative standardLattice) (B × ComplexPlane₂) := by
  let := P.coveringAction
  constructor
  intro g
  change
    Continuous
      (fun x : B × ComplexPlane₂ => (x.1, x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄)))
  exact
    continuous_fst.prodMk
      (continuous_snd.add
        ((P.holomorphic_periodEquiv_const (g.toAdd : RealPlane₄)).continuous.comp continuous_fst))

private theorem HolomorphicPeriodMap.coveringAction_free {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    letI := P.coveringAction
    IsCancelSMul (Multiplicative standardLattice) (B × ComplexPlane₂) := by
  let := P.coveringAction
  constructor
  intro g h x he
  have he' := congrArg (fun y => (P.realTrivialization y).2) he
  rw [P.realTrivialization_smul, P.realTrivialization_smul] at he'
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact add_left_cancel he'

private theorem HolomorphicPeriodMap.quotientMap_smul {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (g : Multiplicative standardLattice) (x : B × ComplexPlane₂) :
    letI := P.coveringAction
    P.quotientMap (g • x) = P.quotientMap x := by
  let := P.coveringAction
  have hg : standardLattice.mkQ (g.toAdd : RealPlane₄) = 0 :=
    (Submodule.Quotient.mk_eq_zero standardLattice).mpr g.toAdd.property
  change
    (x.1,
        standardLattice.mkQ
          ((P.periodEquiv x.1).symm (x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄)))) =
      _
  simp only [map_add, LinearEquiv.symm_apply_apply, hg, add_zero]
  rfl

private theorem HolomorphicPeriodMap.quotientMap_orbit {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    letI := P.coveringAction
    ∀ x y : B × ComplexPlane₂,
      P.quotientMap x = P.quotientMap y ↔
        x ∈ MulAction.orbit (Multiplicative standardLattice) y := by
  let := P.coveringAction
  rintro ⟨b, z⟩ ⟨b', w⟩
  constructor
  · intro h
    have hb : b = b' := congrArg Prod.fst h
    subst b'
    have hv : (P.periodEquiv b).symm z - (P.periodEquiv b).symm w ∈ standardLattice :=
      (Submodule.Quotient.eq standardLattice).mp (congrArg Prod.snd h)
    refine ⟨Multiplicative.ofAdd ⟨_, hv⟩, ?_⟩
    change (b, w + P.periodEquiv b ((P.periodEquiv b).symm z - (P.periodEquiv b).symm w)) = (b, z)
    simp only [map_sub, LinearEquiv.apply_symm_apply]
    congr 1
    abel
  · rintro ⟨g, hg⟩
    rw [← hg]
    exact P.quotientMap_smul g (b', w)

private theorem HolomorphicPeriodMap.quotientCoveringMap {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    letI := P.coveringAction
    IsQuotientCoveringMap P.quotientMap (Multiplicative standardLattice) := by
  let := P.coveringAction
  have := P.coveringAction_continuous
  have := P.coveringAction_free
  exact
    quotientCoveringMap_of_localHomeomorph P.quotientMap_localHomeomorph P.quotientMap_surjective
      P.quotientMap_orbit

/-- The product charted-space structure used on the period-map cover. -/
@[instance_reducible]
public
def HolomorphicPeriodMap.coveringChartedSpace {V B : Type*} [NormedAddCommGroup V]
    [TopologicalSpace B] [ChartedSpace V B] :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace in
public
theorem HolomorphicPeriodMap.coveringManifold {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := modelWithCornersSelf ℂ V) (I' := modelWithCornersSelf ℂ ComplexPlane₂) B
      ComplexPlane₂

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private theorem HolomorphicPeriodMap.coveringAction_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (g : Multiplicative standardLattice) :
    letI := P.coveringAction
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (fun x : B × ComplexPlane₂ => g • x) := by
  let := P.coveringAction
  rw [modelWithCornersSelf_prod]
  change
    ContMDiff _ _ ω
      (fun x : B × ComplexPlane₂ => (x.1, x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄)))
  exact
    contMDiff_fst.prodMk
      (contMDiff_snd.add
        ((P.holomorphic_periodEquiv_const (g.toAdd : RealPlane₄)).comp contMDiff_fst))

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
@[instance_reducible]
private def
    HolomorphicPeriodMap.totalChartedSpace {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    ChartedSpace (V × ComplexPlane₂) P.TotalSpace := by
  let := P.coveringAction
  exact CoveringQuotient.chartedSpace (E := V × ComplexPlane₂) P.quotientCoveringMap

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private theorem HolomorphicPeriodMap.totalSpace_isManifold {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := P.totalChartedSpace
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω P.TotalSpace := by
  let := P.coveringAction
  have : IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
    infer_instance
  exact
    CoveringQuotient.isManifold (E := V × ComplexPlane₂) P.quotientCoveringMap ω
      P.coveringAction_holomorphic

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private theorem HolomorphicPeriodMap.quotientMap_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω P.quotientMap := by
  let := P.coveringAction
  have : IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
    infer_instance
  exact
    CoveringQuotient.contMDiff_project (E := V × ComplexPlane₂) P.quotientCoveringMap ω
      P.coveringAction_holomorphic

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private def HolomorphicPeriodMap.projection {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) : P.TotalSpace → B :=
  Prod.fst

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private theorem HolomorphicPeriodMap.projection_surjective {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Function.Surjective P.projection := fun b => ⟨(b, 0), rfl⟩

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private theorem HolomorphicPeriodMap.projection_proper {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    IsProperMap P.projection :=
  isProperMap_fst_of_compactSpace

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private def
    HolomorphicPeriodMap.torusHomeomorph {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) (b : B) :
    RealTorus₄ ≃ₜ (P.point b).Torus
    where
  toEquiv :=
    (Submodule.Quotient.equiv standardLattice (P.point b).lattice
        ((P.periodEquiv b).restrictScalars ℤ) (P.periodEquiv_map_lattice b)).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact
      (P.point b).lattice.continuous_mkQ.comp (P.periodEquiv b).toContinuousLinearEquiv.continuous
  continuous_invFun := by
    apply (P.point b).lattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact
      standardLattice.continuous_mkQ.comp
        (P.periodEquiv b).symm.toContinuousLinearEquiv.continuous

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private def
    HolomorphicPeriodMap.fibreInclusion {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) (b : B) :
    (P.point b).Torus → P.TotalSpace := fun z => (b, (P.torusHomeomorph b).symm z)

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private theorem HolomorphicPeriodMap.fibreInclusion_injective {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) : Function.Injective (P.fibreInclusion b) := by
  intro x y h
  exact (P.torusHomeomorph b).symm.injective (congrArg Prod.snd h)

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private theorem HolomorphicPeriodMap.fibreInclusion_mkQ {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) (z : ComplexPlane₂) :
    P.fibreInclusion b ((P.point b).lattice.mkQ z) = P.quotientMap (b, z) :=
  rfl

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private theorem HolomorphicPeriodMap.range_fibreInclusion {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) : Set.range (P.fibreInclusion b) = P.projection ⁻¹' { b } := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro hz
    have hb : z.1 = b := hz
    refine ⟨P.torusHomeomorph b z.2, ?_⟩
    simp only [fibreInclusion, Homeomorph.symm_apply_apply, ← hb, Prod.mk.eta]

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private theorem HolomorphicPeriodMap.fibreInclusion_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] (b : B) :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      ω (P.fibreInclusion b) := by
  let := P.totalChartedSpace
  apply DiscreteQuotient.contMDiff_of_comp_mkQ (P.point b).lattice
  have h :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      ω (fun z : ComplexPlane₂ => (b, z)) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_const.prodMk contMDiff_id
  exact P.quotientMap_holomorphic.comp h

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
private def HolomorphicPeriodMap.zeroSection {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) : B → P.TotalSpace :=
  fun b => (b, 0)

end Mathoverflow1973

end
