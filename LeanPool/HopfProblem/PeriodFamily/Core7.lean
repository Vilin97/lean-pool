/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.Core6
public import LeanPool.HopfProblem.MainTheorem.Core1
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Elliptic.Core4
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.PeriodFamily.Core3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods10
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology9
import all LeanPool.HopfProblem.PeriodFamily.Core4
import all LeanPool.HopfProblem.Pi1.MappingTorusHomology
import all LeanPool.HopfProblem.PeriodFamily.Core5
import all LeanPool.HopfProblem.Elliptic.Core7
import all LeanPool.HopfProblem.PeriodFamily.Core6
import all LeanPool.HopfProblem.MainTheorem.Core1

/-!
# Hopf problem: period family · core 7

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

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.h3Coordinates_four
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) .four) 3) :
    h3Coordinates .four a =
      ![-2 *
          Elliptic.HigherHomology.surfaceH3Equiv .four
            (SpecialPeriods.EllipticFilling.specialLocalData .four).centralPeriod a 1,
        Elliptic.HigherHomology.surfaceH3Equiv .four
          (SpecialPeriods.EllipticFilling.specialLocalData .four).centralPeriod a 1,
        -Elliptic.HigherHomology.surfaceH3Equiv .four
            (SpecialPeriods.EllipticFilling.specialLocalData .four).centralPeriod a 1,
        4 *
            Elliptic.HigherHomology.surfaceH3Equiv .four
              (SpecialPeriods.EllipticFilling.specialLocalData .four).centralPeriod a 0 -
          2 * sourceShearThree .four *
            Elliptic.HigherHomology.surfaceH3Equiv .four
              (SpecialPeriods.EllipticFilling.specialLocalData .four).centralPeriod a 1] := by
  have h := h3Coordinates_cover_columns .four a
  rw [originalAffineNorm_splitFibreClassThree, originalAffineNorm_splitCircleClassThree] at h
  ext i
  have hi := congrFun h i
  fin_cases i
  all_goals
    simp [Elliptic.HigherHomology.fibreNormIndex_four, Elliptic.Kind.order] at hi ⊢
    linarith only [hi]

private theorem
    PeriodFamily.Boundary.EllipticCapKernelWang.h3Coordinates_formula (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 3) :
    h3Coordinates j a =
      topWangMatrix j (sourceShearThree j) *ᵥ
        Elliptic.HigherHomology.surfaceH3Equiv j
          (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod a := by
  cases j
  · rw [h3Coordinates_three, topWangMatrix_mulVec_three]
  · rw [h3Coordinates_four, topWangMatrix_mulVec_four]

private def
    PeriodFamily.Boundary.EllipticCapKernelWang.capKernelWangH4Coordinates (j : Elliptic.Kind) :
    LinearMap.ker
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4) →ₗ[ℤ]
      Lattice :=
  AddMonoidHom.toIntLinearMap
    (PeriodFamily.FlatTorus.singularH3Coordinates.toAddEquiv.toAddMonoidHom.comp
      ((MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist)
            3).toAddMonoidHom.comp
        (LinearMap.ker
            (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j)
              4)).subtype.toAddMonoidHom))

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapKernelWang.capKernelWangH4Coordinates_apply
    (j : Elliptic.Kind)
    (a :
      LinearMap.ker (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) 4)) :
    capKernelWangH4Coordinates j a =
      PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.wangBoundary (Elliptic.flatTorusAffine j j.twist) 3 a.val) :=
  rfl

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.capKernelWangH4Coordinates_symm
    (j : Elliptic.Kind) (a : Fin 2 → ℤ) :
    capKernelWangH4Coordinates j
        ((PeriodFamily.Boundary.EllipticCapProduct.boundaryCapH4KernelEquiv j).symm a) =
      topWangMatrix j (sourceShearThree j) *ᵥ a := by
  rw [capKernelWangH4Coordinates_apply,
    PeriodFamily.Boundary.EllipticCapProduct.boundaryCapH4KernelEquiv_symm_val]
  simpa only [h3Coordinates_apply, crossWang_apply, LinearEquiv.apply_symm_apply] using
    h3Coordinates_formula j
      ((Elliptic.HigherHomology.surfaceH3Equiv j
            (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
        a)

private theorem PeriodFamily.Boundary.EllipticCapKernelWang.capKernelWangH4Coordinates_first_axis
    (j : Elliptic.Kind) :
    capKernelWangH4Coordinates j
        ((PeriodFamily.Boundary.EllipticCapProduct.boundaryCapH4KernelEquiv j).symm ![1, 0]) =
      (j.order : ℤ) • ![0, 0, 0, 1] := by
  rw [capKernelWangH4Coordinates_symm]
  cases j
  · rw [topWangMatrix_mulVec_three]
    simp [Elliptic.Kind.order]
  · rw [topWangMatrix_mulVec_four]
    simp [Elliptic.Kind.order]

private theorem PeriodFamily.Boundary.normalizedFamilyFibreHomologyFour_ker
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.Homology.familyFibreInclusion D
            PeriodFamily.Homology.normalizedSlitBaseLift)
          4) =
      ⊥ := by
  rw [PeriodFamily.Homology.familyFibreInclusion_kernel,
    PeriodFamily.HomologyDifference.sourceDifference_four, LinearMap.range_zero]

private theorem PeriodFamily.Boundary.normalizedFamilyFibreHomologyFour_injective
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.familyFibreInclusion D
          PeriodFamily.Homology.normalizedSlitBaseLift)
        4) :=
  LinearMap.ker_eq_bot.mp (normalizedFamilyFibreHomologyFour_ker D)

private def PeriodFamily.Homology.pointFamilyFibreInclusion
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (z : SpecialPeriods.TriangleRegularPoint) : C(RealTorus₄, D.Space) :=
  ⟨fun f => D.quotient (z, f), D.quotient_continuous.comp (continuous_const.prodMk continuous_id)⟩

private def PeriodFamily.Homology.pointFamilyFibreHomotopy
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    {z w : SpecialPeriods.TriangleRegularPoint} (γ : Path z w) :
    (pointFamilyFibreInclusion D z).Homotopy (pointFamilyFibreInclusion D w)
    where
  toFun tf := D.quotient (γ tf.1, tf.2)
  continuous_toFun :=
    D.quotient_continuous.comp ((γ.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left
    f := by
    change D.quotient (γ 0, f) = D.quotient (z, f)
    rw [γ.source]
  map_one_left
    f := by
    change D.quotient (γ 1, f) = D.quotient (w, f)
    rw [γ.target]

private theorem PeriodFamily.Homology.pointFamilyFibreInclusion_homology_eq_of_path
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    {z w : SpecialPeriods.TriangleRegularPoint} (γ : Path z w) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (pointFamilyFibreInclusion D z) n =
      SingularMayerVietoris.singularHomologyMap (pointFamilyFibreInclusion D w) n :=
  PeriodTorusHigherHomology.homotopy_homologyMap (pointFamilyFibreHomotopy D γ) n

private theorem PeriodFamily.Homology.pointFamilyFibreInclusion_homology_eq
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (z w : SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (pointFamilyFibreInclusion D z) n =
      SingularMayerVietoris.singularHomologyMap (pointFamilyFibreInclusion D w) n :=
  pointFamilyFibreInclusion_homology_eq_of_path D (PathConnectedSpace.somePath z w) n

private theorem PeriodFamily.Homology.pointFamilyFibreInclusion_homology_eq_normalized
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (z : SpecialPeriods.TriangleRegularPoint) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (pointFamilyFibreInclusion D z) n =
      SingularMayerVietoris.singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift)
        n :=
  pointFamilyFibreInclusion_homology_eq D z normalizedSlitBaseLift.val n

private def PeriodFamily.Boundary.EllipticGaugeLinearization.positiveLogFlat {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (z : SpecialPeriods.Disc) (s : ℂ) :
    RealPlane₄ :=
  (D.periods.periodEquiv z).symm (s • Elliptic.LogGauge.periodVector D.periods v z)

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.positiveLogFlat_continuous
    {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) (v : Lattice) :
    Continuous (fun p : SpecialPeriods.Disc × ℂ => positiveLogFlat D v p.1 p.2) := by
  change
    Continuous
      ((fun q : SpecialPeriods.Disc × ComplexPlane₂ => (D.periods.periodEquiv q.1).symm q.2) ∘
        (fun p : SpecialPeriods.Disc × ℂ =>
          (p.1, p.2 • Elliptic.LogGauge.periodVector D.periods v p.1)))
  apply D.periods.continuous_periodEquiv_symm.comp
  exact
    continuous_fst.prodMk
      (continuous_snd.smul
        ((Elliptic.LogGauge.periodVector_holomorphic D.periods v).continuous.comp continuous_fst))

private def PeriodFamily.Boundary.EllipticGaugeLinearization.positiveLogFlatMap {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) :
    C(SpecialPeriods.Disc × ℂ, RealPlane₄) :=
  ⟨fun p => positiveLogFlat D v p.1 p.2, positiveLogFlat_continuous D v⟩

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.positiveLogFlat_rotation
    {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (z : SpecialPeriods.Disc) (s : ℂ) :
    positiveLogFlat D v (Elliptic.familyRotation j z) (s - 1 / (j.order : ℂ)) =
      Elliptic.flatLinear j (positiveLogFlat D v z s) -
        (1 / (j.order : ℝ)) • Elliptic.realCast v := by
  apply (D.periods.periodEquiv (Elliptic.familyRotation j z)).injective
  simp only [positiveLogFlat, LinearEquiv.apply_symm_apply, map_sub, D.periodEquiv_flatLinear,
    Elliptic.LogGauge.complexLift_translation, Matrix.mulVec_smul,
    Elliptic.LogGauge.periodVector_covariance D v hv]
  exact sub_smul _ _ _

private theorem
    PeriodFamily.Boundary.EllipticGaugeLinearization.sectionCoordinate_eq_positiveLogFlat
    {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) (v : Lattice) (z : SpecialPeriods.Disc)
    (hz : (z : ℂ) ≠ 0) (s : ℂ) (hs : CuspUniformization.exponential s = (z : ℂ)) :
    Elliptic.LogGauge.sectionCoordinate D.periods v z =
      standardLattice.mkQ (positiveLogFlat D v z s) := by
  have h := Elliptic.LogGauge.sectionMap_formula_of_exponential D.periods v ⟨z, hz⟩ s hs
  have h' := congrArg Prod.snd h
  change
    0 + Elliptic.LogGauge.sectionCoordinate D.periods v z =
      standardLattice.mkQ (positiveLogFlat D v z s) at h'
  exact (zero_add _).symm.trans h'

private def PeriodFamily.Boundary.EllipticGaugeLinearization.nativeLogParameter (j : Elliptic.Kind)
    (τ : ℝ) : C(ℝ, ℂ)
    where
  toFun t := PeriodFamily.Boundary.nativeClockwiseParameter j (-(t + τ))
  continuous_toFun := by unfold PeriodFamily.Boundary.nativeClockwiseParameter; fun_prop

private def
    PeriodFamily.Boundary.EllipticGaugeLinearization.nativeLogRoot (j : Elliptic.Kind) (τ : ℝ) :
    C(ℝ, SpecialPeriods.Disc) :=
  (PeriodFamily.Boundary.nativeClockwiseRoot j).comp
    ⟨fun t => -(t + τ), (continuous_id.add continuous_const).neg⟩

@[simp]
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.nativeLogParameter_apply
    (j : Elliptic.Kind) (τ t : ℝ) :
    nativeLogParameter j τ t = PeriodFamily.Boundary.nativeClockwiseParameter j (-(t + τ)) :=
  rfl

private theorem
    PeriodFamily.Boundary.EllipticGaugeLinearization.nativeLogRoot_ne_zero (j : Elliptic.Kind)
    (τ t : ℝ) : (nativeLogRoot j τ t : ℂ) ≠ 0 :=
  PeriodFamily.Boundary.nativeClockwiseRoot_ne_zero j _

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.nativeLogRoot_exponential
    (j : Elliptic.Kind) (τ t : ℝ) :
    CuspUniformization.exponential (nativeLogParameter j τ t) = (nativeLogRoot j τ t : ℂ) :=
  rfl

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.nativeLogRoot_rotation
    (j : Elliptic.Kind) (τ t : ℝ) :
    Elliptic.familyRotation j (nativeLogRoot j τ (t + 1)) = nativeLogRoot j τ t := by
  have h := PeriodFamily.Boundary.nativeClockwiseRoot_add_one j (-(t + 1 + τ))
  rw [show -(t + 1 + τ) + 1 = -(t + τ) by ring] at h
  exact h.symm

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.nativeLogParameter_step
    (j : Elliptic.Kind) (τ t : ℝ) :
    nativeLogParameter j τ (t + 1) - 1 / (j.order : ℂ) = nativeLogParameter j τ t := by
  simp only [nativeLogParameter_apply, PeriodFamily.Boundary.nativeClockwiseParameter]
  push_cast
  ring

private def PeriodFamily.Boundary.EllipticGaugeLinearization.nativeGaugeRealLift (j : Elliptic.Kind)
    (τ : ℝ) : C(ℝ, RealPlane₄) :=
  (positiveLogFlatMap (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist).comp
    ((nativeLogRoot j τ).prodMk (nativeLogParameter j τ))

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.nativeGaugeRealLift_forward
    (j : Elliptic.Kind) (τ t : ℝ) :
    Elliptic.flatLinear j (nativeGaugeRealLift j τ (t + 1)) =
      nativeGaugeRealLift j τ t + (1 / (j.order : ℝ)) • Elliptic.realCast j.twist := by
  have h :=
    positiveLogFlat_rotation (SpecialPeriods.EllipticFilling.specialLocalData j) j.twist
      j.matrix_fixes_twist (nativeLogRoot j τ (t + 1)) (nativeLogParameter j τ (t + 1))
  rw [nativeLogRoot_rotation, nativeLogParameter_step] at h
  change
    nativeGaugeRealLift j τ t =
      Elliptic.flatLinear j (nativeGaugeRealLift j τ (t + 1)) -
        (1 / (j.order : ℝ)) • Elliptic.realCast j.twist at h
  exact sub_eq_iff_eq_add.mp h.symm

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.nativeGaugeCylinder_realLift
    (j : Elliptic.Kind) (τ t : ℝ) (x : RealTorus₄) :
    PeriodFamily.Boundary.nativeGaugeCylinder j τ (t, x) =
      x + standardLattice.mkQ (nativeGaugeRealLift j τ t) := by
  rw [PeriodFamily.Boundary.nativeGaugeCylinder_apply]
  apply congrArg (fun y : RealTorus₄ => x + y)
  exact
    sectionCoordinate_eq_positiveLogFlat (SpecialPeriods.EllipticFilling.specialLocalData j)
      j.twist (nativeLogRoot j τ t) (nativeLogRoot_ne_zero j τ t) (nativeLogParameter j τ t)
      (nativeLogRoot_exponential j τ t)

private def PeriodFamily.Boundary.EllipticGaugeLinearization.linearGauge (j : Elliptic.Kind)
    (v : Lattice) : C(ℝ, RealPlane₄) :=
  ⟨fun t => (t / (j.order : ℝ)) • Elliptic.realCast v,
    (continuous_id.div_const (j.order : ℝ)).smul continuous_const⟩

private theorem
    PeriodFamily.Boundary.EllipticGaugeLinearization.linearGauge_forward (j : Elliptic.Kind)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) (t : ℝ) :
    Elliptic.flatLinear j (linearGauge j v (t + 1)) =
      linearGauge j v t + (1 / (j.order : ℝ)) • Elliptic.realCast v := by
  change
    Elliptic.flatLinear j (((t + 1) / (j.order : ℝ)) • Elliptic.realCast v) =
      (t / (j.order : ℝ)) • Elliptic.realCast v + (1 / (j.order : ℝ)) • Elliptic.realCast v
  rw [map_smul, Elliptic.flatLinear_realCast, hv, add_div, add_smul]

private def PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeInterpolation (j : Elliptic.Kind)
    (v : Lattice) (a : C(ℝ, RealPlane₄)) :
    C(unitInterval × ℝ, RealPlane₄) :=
  ⟨fun p => (1 - (p.1 : ℝ)) • a p.2 + (p.1 : ℝ) • linearGauge j v p.2,
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (a.continuous.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((linearGauge j v).continuous.comp continuous_snd))⟩

@[simp]
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeInterpolation_zero
    (j : Elliptic.Kind) (v : Lattice) (a : C(ℝ, RealPlane₄)) (t : ℝ) :
    gaugeInterpolation j v a (0, t) = a t := by
  change (1 - (0 : ℝ)) • a t + (0 : ℝ) • linearGauge j v t = a t
  simp

@[simp]
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeInterpolation_one
    (j : Elliptic.Kind) (v : Lattice) (a : C(ℝ, RealPlane₄)) (t : ℝ) :
    gaugeInterpolation j v a (1, t) = linearGauge j v t := by
  change (1 - (1 : ℝ)) • a t + (1 : ℝ) • linearGauge j v t = linearGauge j v t
  simp

private def
    PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeInterpolationSlice (j : Elliptic.Kind)
    (v : Lattice) (a : C(ℝ, RealPlane₄)) (s : unitInterval) :
    C(ℝ, RealPlane₄) :=
  ⟨fun t => gaugeInterpolation j v a (s, t),
    (gaugeInterpolation j v a).continuous.comp (continuous_const.prodMk continuous_id)⟩

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeInterpolation_forward
    (j : Elliptic.Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (a : C(ℝ, RealPlane₄))
    (ha :
      ∀ t, Elliptic.flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • Elliptic.realCast v)
    (s : unitInterval) (t : ℝ) :
    Elliptic.flatLinear j (gaugeInterpolationSlice j v a s (t + 1)) =
      gaugeInterpolationSlice j v a s t + (1 / (j.order : ℝ)) • Elliptic.realCast v := by
  change
    Elliptic.flatLinear j ((1 - (s : ℝ)) • a (t + 1) + (s : ℝ) • linearGauge j v (t + 1)) =
      ((1 - (s : ℝ)) • a t + (s : ℝ) • linearGauge j v t) +
        (1 / (j.order : ℝ)) • Elliptic.realCast v
  rw [map_add, map_smul, map_smul, ha, linearGauge_forward j v hv]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeFibreCylinder
    (a : C(ℝ, RealPlane₄)) : C(ℝ × RealTorus₄, RealTorus₄) :=
  ⟨fun p => p.2 + standardLattice.mkQ (a p.1),
    continuous_snd.add (standardLattice.continuous_mkQ.comp (a.continuous.comp continuous_fst))⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem
    PeriodFamily.Boundary.EllipticGaugeLinearization.flatTorusAffine_apply_eq_triangle_add
    (j : Elliptic.Kind) (v : Lattice) (x : RealTorus₄) :
    Elliptic.flatTorusAffine j v x =
      SpecialPeriods.Triangle.ellipticGenerator j • x +
        standardLattice.mkQ ((1 / (j.order : ℝ)) • Elliptic.realCast v) :=
  congrArg (fun f : C(RealTorus₄, RealTorus₄) => f x)
    (PeriodFamily.Boundary.flatTorusAffine_eq_translation_triangle j v)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeFibreCylinder_forward
    (j : Elliptic.Kind) (v : Lattice) (a : C(ℝ, RealPlane₄))
    (ha :
      ∀ t, Elliptic.flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • Elliptic.realCast v)
    (t : ℝ) (x : RealTorus₄) :
    SpecialPeriods.Triangle.ellipticGenerator j • gaugeFibreCylinder a (t + 1, x) =
      gaugeFibreCylinder a (t, Elliptic.flatTorusAffine j v x) := by
  change
    SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j)
        (x + standardLattice.mkQ (a (t + 1))) =
      Elliptic.flatTorusAffine j v x + standardLattice.mkQ (a t)
  rw [SpecialPeriods.triangleTorusHomeomorph_add, PeriodFamily.Boundary.ellipticTriangle_mkQ, ha,
    map_add, flatTorusAffine_apply_eq_triangle_add]
  change
    SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j) x +
        (standardLattice.mkQ (a t) +
          standardLattice.mkQ ((1 / (j.order : ℝ)) • Elliptic.realCast v)) =
      (SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j) x +
          standardLattice.mkQ ((1 / (j.order : ℝ)) • Elliptic.realCast v)) +
        standardLattice.mkQ (a t)
  abel

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeFibreCylinder_deck_one
    (j : Elliptic.Kind) (v : Lattice) (a : C(ℝ, RealPlane₄))
    (ha :
      ∀ t, Elliptic.flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • Elliptic.realCast v)
    (p : ℝ × RealTorus₄) :
    gaugeFibreCylinder a (MappingTorus.deck (Elliptic.flatTorusAffine j v) 1 p) =
      (SpecialPeriods.Triangle.ellipticGenerator j)⁻¹ • gaugeFibreCylinder a p := by
  apply
    (SpecialPeriods.triangleTorusHomeomorph
        (SpecialPeriods.Triangle.ellipticGenerator j)).injective
  change
    SpecialPeriods.Triangle.ellipticGenerator j •
        gaugeFibreCylinder a (MappingTorus.deck (Elliptic.flatTorusAffine j v) 1 p) =
      SpecialPeriods.Triangle.ellipticGenerator j •
        ((SpecialPeriods.Triangle.ellipticGenerator j)⁻¹ • gaugeFibreCylinder a p)
  rw [smul_inv_smul]
  simp only [MappingTorus.deck, Int.cast_one, zpow_neg_one]
  change
    SpecialPeriods.Triangle.ellipticGenerator j •
        gaugeFibreCylinder a (p.1 + 1, (Elliptic.flatTorusAffine j v).symm p.2) =
      gaugeFibreCylinder a p
  rw [gaugeFibreCylinder_forward j v a ha, Homeomorph.apply_symm_apply]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.fibreDeck_of_one
    (φ : RealTorus₄ ≃ₜ RealTorus₄) (F : ℝ × RealTorus₄ → RealTorus₄)
    (g : SpecialPeriods.TriangleGroup) (hF : ∀ p, F (MappingTorus.deck φ 1 p) = g⁻¹ • F p) (k : ℤ)
    (p : ℝ × RealTorus₄) : F (MappingTorus.deck φ k p) = (g ^ (-k)) • F p := by
  have hprev (q : ℝ × RealTorus₄) : F (MappingTorus.deck φ (-1) q) = g • F q := by
    have h := congrArg (fun y : RealTorus₄ => g • y) (hF (MappingTorus.deck φ (-1) q))
    simpa only [← MappingTorus.deck_add, add_neg_cancel, MappingTorus.deck_zero,
      smul_inv_smul] using h.symm
  have hall : ∀ k : ℤ, ∀ p : ℝ × RealTorus₄, F (MappingTorus.deck φ k p) = (g ^ (-k)) • F p := by
    intro k
    induction k using Int.induction_on with
    | zero => intro p; simp only [MappingTorus.deck_zero, neg_zero, zpow_zero, one_smul]
    | succ k ih =>
      intro p
      rw [MappingTorus.deck_add, ih, hF, neg_add, zpow_add, zpow_neg_one,
        SemigroupAction.mul_smul]
    | pred k ih =>
      intro p
      rw [sub_eq_add_neg, MappingTorus.deck_add, ih, hprev]
      simp only [neg_add, neg_neg, zpow_add, zpow_one, SemigroupAction.mul_smul]
  exact hall k p

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeFibreCylinder_deck
    (j : Elliptic.Kind) (v : Lattice) (a : C(ℝ, RealPlane₄))
    (ha :
      ∀ t, Elliptic.flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • Elliptic.realCast v)
    (k : ℤ) (p : ℝ × RealTorus₄) :
    gaugeFibreCylinder a (MappingTorus.deck (Elliptic.flatTorusAffine j v) k p) =
      (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) • gaugeFibreCylinder a p :=
  fibreDeck_of_one (Elliptic.flatTorusAffine j v) (gaugeFibreCylinder a)
    (SpecialPeriods.Triangle.ellipticGenerator j) (gaugeFibreCylinder_deck_one j v a ha) k p

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.interpolatedGaugeFibreCylinder_deck
    (j : Elliptic.Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (a : C(ℝ, RealPlane₄))
    (ha :
      ∀ t, Elliptic.flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • Elliptic.realCast v)
    (s : unitInterval) (k : ℤ) (p : ℝ × RealTorus₄) :
    gaugeFibreCylinder (gaugeInterpolationSlice j v a s)
        (MappingTorus.deck (Elliptic.flatTorusAffine j v) k p) =
      (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) •
        gaugeFibreCylinder (gaugeInterpolationSlice j v a s) p :=
  gaugeFibreCylinder_deck j v (gaugeInterpolationSlice j v a s)
    (gaugeInterpolation_forward j v hv a ha s) k p

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeCylinderMap
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint)) (a : C(ℝ, RealPlane₄)) :
    C(ℝ × RealTorus₄, D.Space) :=
  PeriodFamily.Boundary.familyCylinderMap D L (gaugeFibreCylinder a)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeCylinderMap_deck
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (j : Elliptic.Kind)
    (v : Lattice) (a : C(ℝ, RealPlane₄))
    (ha :
      ∀ t, Elliptic.flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • Elliptic.realCast v)
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) • L t)
    (k : ℤ) (p : ℝ × RealTorus₄) :
    gaugeCylinderMap D L a (MappingTorus.deck (Elliptic.flatTorusAffine j v) k p) =
      gaugeCylinderMap D L a p :=
  PeriodFamily.Boundary.familyCylinderMap_deck D (Elliptic.flatTorusAffine j v) L
    (gaugeFibreCylinder a) (SpecialPeriods.Triangle.ellipticGenerator j) hL
    (gaugeFibreCylinder_deck j v a ha) k p

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeBoundaryMap
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (j : Elliptic.Kind)
    (v : Lattice) (a : C(ℝ, RealPlane₄))
    (ha :
      ∀ t, Elliptic.flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • Elliptic.realCast v)
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) • L t) :
    C(MappingTorus.Torus (Elliptic.flatTorusAffine j v), D.Space) :=
  PeriodFamily.Boundary.Cylinder.descend (Elliptic.flatTorusAffine j v) (gaugeCylinderMap D L a)
    (gaugeCylinderMap_deck D j v a ha L hL)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeCylinderHomotopy
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (j : Elliptic.Kind)
    (v : Lattice) (a : C(ℝ, RealPlane₄))
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint)) :
    (gaugeCylinderMap D L a).Homotopy (gaugeCylinderMap D L (linearGauge j v))
    where
  toFun
    p := D.quotient (L p.2.1, p.2.2 + standardLattice.mkQ (gaugeInterpolation j v a (p.1, p.2.1)))
  continuous_toFun :=
    D.quotient_continuous.comp
      ((L.continuous.comp (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_snd.comp continuous_snd).add
          (standardLattice.continuous_mkQ.comp
            ((gaugeInterpolation j v a).continuous.comp
              (continuous_fst.prodMk (continuous_fst.comp continuous_snd))))))
  map_zero_left
    p := by
    change
      D.quotient (L p.1, p.2 + standardLattice.mkQ (gaugeInterpolation j v a (0, p.1))) =
        D.quotient (L p.1, p.2 + standardLattice.mkQ (a p.1))
    rw [gaugeInterpolation_zero]
  map_one_left
    p := by
    change
      D.quotient (L p.1, p.2 + standardLattice.mkQ (gaugeInterpolation j v a (1, p.1))) =
        D.quotient (L p.1, p.2 + standardLattice.mkQ (linearGauge j v p.1))
    rw [gaugeInterpolation_one]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeCylinderHomotopy_deck
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (j : Elliptic.Kind)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) (a : C(ℝ, RealPlane₄))
    (ha :
      ∀ t, Elliptic.flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • Elliptic.realCast v)
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) • L t)
    (s : unitInterval) (k : ℤ) (p : ℝ × RealTorus₄) :
    gaugeCylinderHomotopy D j v a L (s, MappingTorus.deck (Elliptic.flatTorusAffine j v) k p) =
      gaugeCylinderHomotopy D j v a L (s, p) :=
  PeriodFamily.Boundary.familyCylinderMap_deck D (Elliptic.flatTorusAffine j v) L
    (gaugeFibreCylinder (gaugeInterpolationSlice j v a s))
    (SpecialPeriods.Triangle.ellipticGenerator j) hL
    (interpolatedGaugeFibreCylinder_deck j v hv a ha s) k p

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeLinearizationHomotopy
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (j : Elliptic.Kind)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) (a : C(ℝ, RealPlane₄))
    (ha :
      ∀ t, Elliptic.flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • Elliptic.realCast v)
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) • L t) :
    (gaugeBoundaryMap D j v a ha L hL).Homotopy
      (gaugeBoundaryMap D j v (linearGauge j v) (linearGauge_forward j v hv) L hL) :=
  PeriodFamily.Boundary.Cylinder.descendHomotopy (Elliptic.flatTorusAffine j v)
    (gaugeCylinderMap D L a) (gaugeCylinderMap D L (linearGauge j v))
    (gaugeCylinderMap_deck D j v a ha L hL)
    (gaugeCylinderMap_deck D j v (linearGauge j v) (linearGauge_forward j v hv) L hL)
    (gaugeCylinderHomotopy D j v a L) (gaugeCylinderHomotopy_deck D j v hv a ha L hL)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeBoundaryMap_eq_of_mk
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (j : Elliptic.Kind)
    (v : Lattice) (a : C(ℝ, RealPlane₄))
    (ha :
      ∀ t, Elliptic.flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • Elliptic.realCast v)
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) • L t)
    (F : C(MappingTorus.Torus (Elliptic.flatTorusAffine j v), D.Space))
    (hF :
      ∀ t x,
        F (MappingTorus.mk (Elliptic.flatTorusAffine j v) (t, x)) =
          D.quotient (L t, x + standardLattice.mkQ (a t))) :
    F = gaugeBoundaryMap D j v a ha L hL := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective (Elliptic.flatTorusAffine j v) q
  exact hF t x

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.EllipticGaugeLinearization.gaugeLinearizationHomotopyOfMk
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (j : Elliptic.Kind)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) (a : C(ℝ, RealPlane₄))
    (ha :
      ∀ t, Elliptic.flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • Elliptic.realCast v)
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (SpecialPeriods.Triangle.ellipticGenerator j ^ (-k)) • L t)
    (F : C(MappingTorus.Torus (Elliptic.flatTorusAffine j v), D.Space))
    (hF :
      ∀ t x,
        F (MappingTorus.mk (Elliptic.flatTorusAffine j v) (t, x)) =
          D.quotient (L t, x + standardLattice.mkQ (a t))) :
    F.Homotopy (gaugeBoundaryMap D j v (linearGauge j v) (linearGauge_forward j v hv) L hL) :=
  (gaugeLinearizationHomotopy D j v hv a ha L hL).cast
    (gaugeBoundaryMap_eq_of_mk D j v a ha L hL F hF).symm rfl

private theorem
    PeriodFamily.Boundary.EllipticGaugeLinearization.capSectionFibre_coordinateProjection
    (j : Elliptic.Kind) (s : ℝ) (k : Elliptic.HigherHomology.FibreCoordinates) :
    PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre j s
        (PeriodTorusHigherHomology.coordinateProjection 3 k) =
      standardLattice.mkQ ((s / (j.order : ℝ)) • Elliptic.realCast j.twist + Fin.cons 0 k) := by
  rw [PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_apply,
    Elliptic.HigherHomology.splitFlatTorusHomeomorph_symm_coordinateProjection,
    Elliptic.HigherHomology.splitRealCoordinates_symm_apply]

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.capSectionFibre_linearGauge_cancel
    (j : Elliptic.Kind) (s : ℝ) (y : PeriodTorusHigherHomology.ProductTorus 3) :
    PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre j s y +
        standardLattice.mkQ ((-s / (j.order : ℝ)) • Elliptic.realCast j.twist) =
      PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre j 0 y := by
  obtain ⟨k, rfl⟩ := PeriodTorusHigherHomology.coordinateProjection_surjective 3 y
  rw [capSectionFibre_coordinateProjection,
    PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_zero_coordinateProjection, ← map_add]
  apply congrArg standardLattice.mkQ
  rw [neg_div, neg_smul]
  abel

private def
    PeriodFamily.Boundary.EllipticGaugeLinearization.linearRegularBoundaryMap (j : Elliptic.Kind)
    (τ : ℝ) :
    C(ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j,
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁
          SpecialPeriods.specialPeriodMap_generator₂)).Space) :=
  gaugeBoundaryMap
    (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
    j j.twist (linearGauge j j.twist) (linearGauge_forward j j.twist j.matrix_fixes_twist)
    (PeriodFamily.Boundary.nativeShiftedBase j τ)
    (PeriodFamily.Boundary.nativeShiftedBase_translate j τ)

@[simp]
private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.linearRegularBoundaryMap_mk
    (j : Elliptic.Kind) (τ t : ℝ) (x : RealTorus₄) :
    linearRegularBoundaryMap j τ (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (PeriodFamily.Boundary.nativeShiftedBase j τ t,
          x + standardLattice.mkQ ((t / (j.order : ℝ)) • Elliptic.realCast j.twist)) :=
  rfl

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.nativeRegularBoundaryMap_realLift
    (j : Elliptic.Kind) (τ t : ℝ) (x : RealTorus₄) :
    PeriodFamily.Boundary.nativeRegularBoundaryMap j τ
        (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (PeriodFamily.Boundary.nativeShiftedBase j τ t,
          x + standardLattice.mkQ (nativeGaugeRealLift j τ t)) := by
  rw [PeriodFamily.Boundary.nativeRegularBoundaryMap_mk, nativeGaugeCylinder_realLift]

private def
  PeriodFamily.Boundary.EllipticGaugeLinearization.nativeRegularBoundaryGaugeLinearizationHomotopy
    (j : Elliptic.Kind) (τ : ℝ) :
    (PeriodFamily.Boundary.nativeRegularBoundaryMap j τ).Homotopy
      (linearRegularBoundaryMap j τ) :=
  gaugeLinearizationHomotopyOfMk
    (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
    j j.twist j.matrix_fixes_twist (nativeGaugeRealLift j τ) (nativeGaugeRealLift_forward j τ)
    (PeriodFamily.Boundary.nativeShiftedBase j τ)
    (PeriodFamily.Boundary.nativeShiftedBase_translate j τ)
    (PeriodFamily.Boundary.nativeRegularBoundaryMap j τ) (nativeRegularBoundaryMap_realLift j τ)

private theorem
    PeriodFamily.Boundary.EllipticGaugeLinearization.nativeRegularBoundaryMap_homotopic_linear
    (j : Elliptic.Kind) (τ : ℝ) :
    (PeriodFamily.Boundary.nativeRegularBoundaryMap j τ).Homotopic
      (linearRegularBoundaryMap j τ) :=
  ⟨nativeRegularBoundaryGaugeLinearizationHomotopy j τ⟩

private theorem
    PeriodFamily.Boundary.EllipticGaugeLinearization.boundaryToRegularFamily_homotopic_linear
    (j : Elliptic.Kind) (τ : ℝ) :
    (ThreefoldOverlapMappingTorus.boundaryToRegularFamily (Option.some j)).Homotopic
      (linearRegularBoundaryMap j τ) :=
  (ThreefoldOverlapMappingTorus.Elliptic.boundaryToRegularFamily_homotopic_at j
        (PeriodFamily.Boundary.nativeBoundaryRootRadius j)
        (PeriodFamily.Boundary.nativeBoundaryRootPhase j + τ)).trans
    (nativeRegularBoundaryMap_homotopic_linear j τ)

private theorem PeriodFamily.Boundary.EllipticGaugeLinearization.boundaryRegularHomologyMap_linear
    (j : Elliptic.Kind) (τ : ℝ) (n : ℕ) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap (Option.some j) n =
      SingularMayerVietoris.singularHomologyMap (linearRegularBoundaryMap j τ) n :=
  PeriodTorusHigherHomology.homotopic_homologyMap (boundaryToRegularFamily_homotopic_linear j τ) n

private theorem
  PeriodFamily.Boundary.EllipticGaugeLinearization.linearRegularBoundaryMap_capSectionFromModel_mk
    (j : Elliptic.Kind) (τ s : ℝ) (y : PeriodTorusHigherHomology.ProductTorus 3) :
    linearRegularBoundaryMap j τ
        (PeriodFamily.Boundary.EllipticCapProduct.capSectionFromModel j
          (MappingTorus.mk (Elliptic.HigherHomology.fibreTorusHomeomorph j).symm (s, y))) =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (PeriodFamily.Boundary.nativeShiftedBase j τ (-s),
          PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre j 0 y) := by
  rw [PeriodFamily.Boundary.EllipticCapProduct.capSectionFromModel_mk,
    linearRegularBoundaryMap_mk, capSectionFibre_linearGauge_cancel]

private theorem PeriodFamily.Boundary.fibreToRegularFamily_cusp_eq_point :
    ThreefoldOverlapMappingTorus.fibreToRegularFamily Option.none =
      PeriodFamily.Homology.pointFamilyFibreInclusion
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        (Cusp.baseLift ThreefoldOverlapMappingTorus.Cusp.specialHeight 0) := by
  apply ContinuousMap.ext
  intro x
  exact Cusp.boundaryToRegularFamily_mk 0 x

private theorem PeriodFamily.Boundary.linearRegularBoundaryMap_fibre_eq_point (j : Elliptic.Kind) :
    (EllipticGaugeLinearization.linearRegularBoundaryMap j 0).comp
        (MappingTorus.HomologyCover.fibreInclusion (Elliptic.flatTorusAffine j j.twist)) =
      PeriodFamily.Homology.pointFamilyFibreInclusion
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        (nativeShiftedBase j 0 0) := by
  apply ContinuousMap.ext
  intro x
  change
    EllipticGaugeLinearization.linearRegularBoundaryMap j 0
        (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (0, x)) =
      ((PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂)).quotient
        (nativeShiftedBase j 0 0, x)
  rw [EllipticGaugeLinearization.linearRegularBoundaryMap_mk]
  simp only [zero_div, zero_smul, map_zero, add_zero]

private theorem
    PeriodFamily.Boundary.fibreToRegularFamily_elliptic_homotopic_point (j : Elliptic.Kind) :
    (ThreefoldOverlapMappingTorus.fibreToRegularFamily (Option.some j)).Homotopic
      (PeriodFamily.Homology.pointFamilyFibreInclusion
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        (nativeShiftedBase j 0 0)) := by
  obtain ⟨H⟩ := EllipticGaugeLinearization.boundaryToRegularFamily_homotopic_linear j 0
  exact
    ⟨(H.comp
            (ContinuousMap.Homotopy.refl
              (MappingTorus.HomologyCover.fibreInclusion
                (Elliptic.flatTorusAffine j j.twist)))).cast
        rfl (linearRegularBoundaryMap_fibre_eq_point j)⟩

private theorem PeriodFamily.Boundary.fibreToRegularFamily_homology_common
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.fibreToRegularFamily i) n =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.familyFibreInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          PeriodFamily.Homology.normalizedSlitBaseLift)
        n := by
  cases i with
  | none =>
    rw [fibreToRegularFamily_cusp_eq_point]
    exact
      PeriodFamily.Homology.pointFamilyFibreInclusion_homology_eq_normalized
        (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
        _ n
  | some j =>
    exact
      (PeriodTorusHigherHomology.homotopic_homologyMap
            (fibreToRegularFamily_elliptic_homotopic_point j) n).trans
        (PeriodFamily.Homology.pointFamilyFibreInclusion_homology_eq_normalized
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          _ n)

private theorem PeriodFamily.Boundary.boundaryRegularHomologyMap_common_fibre
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i n).comp
        (MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) n) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.familyFibreInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          PeriodFamily.Homology.normalizedSlitBaseLift)
        n :=
  (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap_fibre i n).trans
    (fibreToRegularFamily_homology_common i n)

private theorem PeriodFamily.Boundary.boundaryRegularHomologyMap_common_fibre_apply
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap i n
        (MappingTorusHomology.fibreHomologyMap (ThreefoldOverlapMappingTorus.monodromy i) n a) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodFamily.Homology.familyFibreInclusion
          (PeriodFamily.regularData SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂)
          PeriodFamily.Homology.normalizedSlitBaseLift)
        n a :=
  LinearMap.congr_fun (boundaryRegularHomologyMap_common_fibre i n) a

/-- Negation on the unit circle as a homeomorphism. -/
public
def PeriodFamily.Boundary.EllipticTopFibre.circleNegation :
    C((PeriodTorusHigherHomology.CircleTopology.Circle),
      (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  ⟨fun z => -z, ContinuousNeg.continuous_neg⟩

@[simp]
public
theorem PeriodFamily.Boundary.EllipticTopFibre.circleNegation_zero : circleNegation 0 = 0 :=
  neg_zero

private theorem PeriodFamily.Boundary.EllipticTopFibre.circleNegation_positiveLoop :
    PeriodTorusHigherHomology.CirclePaths.positiveLoop.map circleNegation.continuous =
      PeriodTorusHigherHomology.CirclePaths.positiveLoop.symm.cast circleNegation_zero
        circleNegation_zero := by
  apply Path.ext
  funext t
  change
    -((t : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      (((1 - (t : ℝ)) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
  rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]

private theorem PeriodFamily.Boundary.EllipticTopFibre.circleNegation_positiveHomology :
    SingularMayerVietoris.singularHomologyMap circleNegation 1
        (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) =
      -FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
  rw [SingularMayerVietoris.singularHomologyMap_one,
    FirstHurewicz.inducedHomology_loopHomologyClass, circleNegation_positiveLoop]
  apply
    FirstHurewicz.homologyToChainClass_injective (PeriodTorusHigherHomology.CircleTopology.Circle)
  rw [FirstHurewicz.homologyToChainClass_loopHomologyClass, map_neg,
    FirstHurewicz.homologyToChainClass_loopHomologyClass, FirstHurewicz.pathClass_cast,
    FirstHurewicz.pathClass_symm]

private def PeriodFamily.Boundary.EllipticTopFibre.productNegation :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 3,
      (PeriodTorusHigherHomology.CircleTopology.Circle) ×
        PeriodTorusHigherHomology.ProductTorus 3) :=
  circleNegation.prodMap (ContinuousMap.id (PeriodTorusHigherHomology.ProductTorus 3))

private theorem PeriodFamily.Boundary.EllipticTopFibre.productNegation_positiveCircleCross
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    SingularMayerVietoris.singularHomologyMap productNegation 4
        (PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 3)
          3 a) =
      -PeriodTorusHigherHomology.positiveCircleCross (PeriodTorusHigherHomology.ProductTorus 3) 3
          a := by
  change
    SingularMayerVietoris.singularHomologyMap
        (circleNegation.prodMap (ContinuousMap.id (PeriodTorusHigherHomology.ProductTorus 3))) 4
        (PeriodTorusHigherHomology.crossProductHomology
          (PeriodTorusHigherHomology.CircleTopology.Circle)
          (PeriodTorusHigherHomology.ProductTorus 3) 3
          (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop)
          a) =
      _
  rw [PeriodTorusHigherHomology.crossProductHomology_natural, circleNegation_positiveHomology]
  change
    PeriodTorusHigherHomology.crossProductHomology
        (PeriodTorusHigherHomology.CircleTopology.Circle)
        (PeriodTorusHigherHomology.ProductTorus 3) 3
        (-FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop)
        (SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.id (PeriodTorusHigherHomology.ProductTorus 3)) 3 a) =
      _
  rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply, map_neg,
    LinearMap.neg_apply]
  rfl

private theorem PeriodFamily.Boundary.EllipticTopFibre.productNegation_homology_four
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) ×
          PeriodTorusHigherHomology.ProductTorus 3)
        4) :
    SingularMayerVietoris.singularHomologyMap productNegation 4 a = -a := by
  obtain ⟨b, rfl⟩ := PeriodFamily.Homology.circleTopDegreeEquiv.symm.surjective a
  rw [PeriodFamily.Homology.circleTopDegreeEquiv_symm_apply]
  exact productNegation_positiveCircleCross b

private def PeriodFamily.Boundary.EllipticTopFibre.headReflectionMatrix : LatticeMatrix :=
  !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private theorem PeriodFamily.Boundary.EllipticTopFibre.headReflectionMatrix_circleMap :
    PeriodFamily.Homology.topDegreeCircleMap headReflectionMatrix = productNegation := by
  apply ContinuousMap.ext
  rintro ⟨z, x⟩
  apply Prod.ext
  · change (∑ i : Fin 4, headReflectionMatrix 0 i • Fin.cons z x i) = -z
    simp [headReflectionMatrix, Fin.sum_univ_succ]
  · funext i
    change (∑ k : Fin 4, headReflectionMatrix i.succ k • Fin.cons z x k) = x i
    fin_cases i <;> simp [headReflectionMatrix, Fin.sum_univ_succ]

private theorem PeriodFamily.Boundary.EllipticTopFibre.headReflectionMatrix_homology_four
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 4) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap headReflectionMatrix) 4 a =
      -a := by
  apply
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (PeriodTorusHigherHomology.productTorusSuccHomeomorph 3) 4).injective
  rw [PeriodTorusHigherHomology.homeomorphHomologyEquiv_apply,
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_apply]
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    PeriodFamily.Homology.topDegreeCircleMap_comp_homeomorph,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    headReflectionMatrix_circleMap, productNegation_homology_four, map_neg]

private theorem PeriodFamily.Boundary.EllipticTopFibre.twistBasisInvMatrix_homology_four
    (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 4) :
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.torusMatrixMap (Elliptic.HigherHomology.twistBasisInvMatrix j))
        4 a =
      γ j.twist • a := by
  cases j with
  |
    three =>
    have h :=
      PeriodFamily.Homology.torusMatrixMap_homologyFour_of_det_one
        (Elliptic.HigherHomology.twistBasisInvMatrix .three) (by intro i; fin_cases i <;> decide)
        (by decide)
    rw [h, LinearMap.id_apply]
    simp [γ, Elliptic.Kind.twist, ε]
  |
    four =>
    have hfirst :
      ∀ i,
        (Elliptic.HigherHomology.twistBasisInvMatrix .four * headReflectionMatrix) 0 i =
          if i = 0 then 1 else 0 := by
      intro i
      fin_cases i <;> decide
    have hdet :
      (Elliptic.HigherHomology.twistBasisInvMatrix .four * headReflectionMatrix).det = 1 := by
      decide
    have hfactor :
      (Elliptic.HigherHomology.twistBasisInvMatrix .four * headReflectionMatrix) *
          headReflectionMatrix =
        Elliptic.HigherHomology.twistBasisInvMatrix .four := by decide
    have h :=
      PeriodFamily.Homology.torusMatrixMap_homologyFour_of_det_one
        (Elliptic.HigherHomology.twistBasisInvMatrix .four * headReflectionMatrix) hfirst hdet
    rw [← hfactor, PeriodTorusHigherHomology.torusMatrixMap_mul,
      PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply, h,
      LinearMap.id_apply, headReflectionMatrix_homology_four]
    simp [γ, Elliptic.Kind.twist, ε']

private def PeriodFamily.Boundary.EllipticTopFibre.coordinateTopEquiv :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 4 ≃ₗ[ℤ] ℤ :=
  (PeriodTorusHigherHomology.productTorusHomologyEquiv 4 4).trans
    (PeriodTorusHigherHomology.integerBinomialZeroEquiv 4).symm

@[simp]
private theorem PeriodFamily.Boundary.EllipticTopFibre.coordinateTopEquiv_topClass :
    coordinateTopEquiv (PeriodTorusHigherHomology.productTorusTopClass 4) = 1 := by
  change
    PeriodTorusHigherHomology.productTorusHomologyEquiv 4 4
        (PeriodTorusHigherHomology.productTorusTopClass 4) ⟨0, by decide⟩ =
      1
  rw [PeriodTorusHigherHomology.productTorusHomologyEquiv_topClass]

private theorem PeriodFamily.Boundary.EllipticTopFibre.coordinateTopEquiv_smul_topClass
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 4) :
    a = coordinateTopEquiv a • PeriodTorusHigherHomology.productTorusTopClass 4 := by
  apply coordinateTopEquiv.injective
  rw [map_zsmul, coordinateTopEquiv_topClass, zsmul_eq_mul, mul_one]
  simp only [Int.cast_id]

private theorem
    PeriodFamily.Boundary.EllipticTopFibre.topDegreeTorusCoordinates_eq_coordinateTopEquiv
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 4) :
    PeriodFamily.Homology.topDegreeTorusCoordinates a = coordinateTopEquiv a := by
  conv_lhs => rw [coordinateTopEquiv_smul_topClass a]
  rw [map_zsmul, PeriodFamily.Homology.topDegreeTorusCoordinates_topClass, zsmul_eq_mul, mul_one]
  simp only [Int.cast_id]

private theorem PeriodFamily.Boundary.EllipticTopFibre.coordinateTopEquiv_flat
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    coordinateTopEquiv
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          PeriodTorusHigherHomology.flatTorusCircleHomeomorph 4 a) =
      PeriodTorusHigherHomology.realTorusH4Equiv a := by
  change
    PeriodTorusHigherHomology.productTorusHomologyEquiv 4 4
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          PeriodTorusHigherHomology.flatTorusCircleHomeomorph 4 a)
        ⟨0, by decide⟩ =
      PeriodTorusHigherHomology.realTorusHomologyEquiv 4 a ⟨0, by decide⟩
  rw [PeriodTorusHigherHomology.realTorusHomologyEquiv_apply,
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_apply]

private theorem
    PeriodFamily.Boundary.EllipticTopFibre.splitFlatTorus_top_boundary (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    Elliptic.HigherHomology.torusH3Coordinates
        (PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) 3
          (PeriodTorusHigherHomology.homeomorphHomologyEquiv
            (Elliptic.HigherHomology.splitFlatTorusHomeomorph j) 4 a)) =
      γ j.twist * PeriodTorusHigherHomology.realTorusH4Equiv a := by
  rw [Elliptic.HigherHomology.splitFlatTorusHomeomorph,
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_trans, LinearEquiv.trans_apply,
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_trans, LinearEquiv.trans_apply]
  change
    PeriodFamily.Homology.topDegreeTorusCoordinates
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.torusMatrixMap
            (Elliptic.HigherHomology.twistBasisInvMatrix j))
          4
          (PeriodTorusHigherHomology.homeomorphHomologyEquiv
            PeriodTorusHigherHomology.flatTorusCircleHomeomorph 4 a)) =
      _
  rw [twistBasisInvMatrix_homology_four, map_zsmul,
    topDegreeTorusCoordinates_eq_coordinateTopEquiv, zsmul_eq_mul, Int.cast_id,
    coordinateTopEquiv_flat]

private theorem
    PeriodFamily.Boundary.EllipticTopFibre.splitPeriod_comp_flatPeriod (j : Elliptic.Kind)
    (p : PeriodDomain) :
    (Elliptic.HigherHomology.splitPeriodTorusHomeomorph j p :
            C(p.Torus, AddCircle (1 : ℝ) × PeriodTorusHigherHomology.ProductTorus 3)).comp
        (Elliptic.flatTorusPeriodHomeomorph p : C(RealTorus₄, p.Torus)) =
      (Elliptic.HigherHomology.splitFlatTorusHomeomorph j :
        C(RealTorus₄, AddCircle (1 : ℝ) × PeriodTorusHigherHomology.ProductTorus 3)) := by
  apply ContinuousMap.ext
  intro x
  change
    Elliptic.HigherHomology.splitFlatTorusHomeomorph j
        ((Elliptic.flatTorusPeriodHomeomorph p).symm (Elliptic.flatTorusPeriodHomeomorph p x)) =
      _
  rw [Homeomorph.symm_apply_apply]
  rfl

private theorem PeriodFamily.Boundary.EllipticTopFibre.surfacePeriodCoverCircleBoundary_flat
    (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ 4) :
    Elliptic.HigherHomology.torusH3Coordinates
        (Elliptic.HigherHomology.surfacePeriodCoverCircleBoundary j p 3
          (PeriodTorusHigherHomology.homeomorphHomologyEquiv
            (Elliptic.flatTorusPeriodHomeomorph p.val) 4 a)) =
      γ j.twist * PeriodTorusHigherHomology.realTorusH4Equiv a := by
  rw [Elliptic.HigherHomology.surfacePeriodCoverCircleBoundary_apply,
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_apply,
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_apply]
  have hc :
    (SingularMayerVietoris.singularHomologyMap
            (Elliptic.HigherHomology.splitPeriodTorusHomeomorph j p.val :
              C(p.val.Torus, AddCircle (1 : ℝ) × PeriodTorusHigherHomology.ProductTorus 3))
            4).comp
        (SingularMayerVietoris.singularHomologyMap
          (Elliptic.flatTorusPeriodHomeomorph p.val : C(RealTorus₄, p.val.Torus)) 4) =
      SingularMayerVietoris.singularHomologyMap
        (Elliptic.HigherHomology.splitFlatTorusHomeomorph j :
          C(RealTorus₄, AddCircle (1 : ℝ) × PeriodTorusHigherHomology.ProductTorus 3))
        4 := by
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, splitPeriod_comp_flatPeriod]
  exact
    (congrArg
          (fun b =>
            Elliptic.HigherHomology.torusH3Coordinates
              (PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3)
                3 b))
          (LinearMap.congr_fun hc a)).trans
      (splitFlatTorus_top_boundary j a)

end Mathoverflow1973

end
