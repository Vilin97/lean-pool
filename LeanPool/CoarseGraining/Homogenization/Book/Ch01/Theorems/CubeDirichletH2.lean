/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2

/-!
# Legacy Chapter 1 Dirichlet compatibility facade

This module is deliberately quarantined in
`Homogenization.Book.Ch01.Legacy`.  It exposes translated, coordinate-`L¹`,
and discrete-`K` compatibility machinery from the earlier Chapter 1 route.
Its former final fractional facade has not passed the continuum `K`/`Hˢ` gate,
so none of these declarations is a source-facing formulation of the
manuscript's classical-input statements.
-/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch01

noncomputable section

namespace Legacy

open scoped ENNReal Pointwise BigOperators

/-- Public alias for the scalar weak Dirichlet Poisson problem on a cube. -/
abbrev CubeDirichletWeakPoissonProblem {d : ℕ} (Q : Cube d)
    (u : H10Function (openCubeSet Q)) (f : Vec d → ℝ) : Prop :=
  Homogenization.CubeDirichletWeakPoissonProblem Q u f

/-- Public alias for cube Dirichlet `H²` regularity in weak-Hessian form. -/
abbrev CubeDirichletH2Regularity {d : ℕ} (Q : Cube d) (C : ℝ) : Prop :=
  Homogenization.CubeDirichletH2Regularity Q C

/-- Public alias for dimension-uniform cube Dirichlet `H²` regularity. -/
abbrev CubeDirichletH2RegularityInDimension (d : ℕ) (C : ℝ) : Prop :=
  Homogenization.CubeDirichletH2RegularityInDimension d C

/-- Public alias for cube Dirichlet `H²` regularity with the unnormalized
open-cube `L²` forcing norm. -/
abbrev CubeDirichletH2RegularityVolumeL2 {d : ℕ} (Q : Cube d) (C : ℝ) : Prop :=
  Homogenization.CubeDirichletH2RegularityVolumeL2 Q C

/-- Public alias for dimension-uniform cube Dirichlet `H²` regularity with the
unnormalized open-cube `L²` forcing norm. -/
abbrev CubeDirichletH2RegularityVolumeL2InDimension (d : ℕ) (C : ℝ) : Prop :=
  Homogenization.CubeDirichletH2RegularityVolumeL2InDimension d C

/-- Public scale-indexed Dirichlet `H²` constant from the current proof. -/
noncomputable abbrev cubeDirichletH2RegularityConstantExact
    {d : ℕ} [NeZero d] (Q : Cube d) : ℝ :=
  Homogenization.CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityConstantExact Q

/-- Public dimension-only Dirichlet `H²` constant for the unnormalized
open-cube `L²` forcing norm. -/
noncomputable abbrev cubeDirichletH2RegularityVolumeL2ConstantExact
    (d : ℕ) [NeZero d] : ℝ :=
  Homogenization.CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact d

/-- Public alias for the full positive vector `B^s_{2,2}` norm used in
the older disjoint-descendant normalization. -/
noncomputable abbrev cubeBesovPositiveVectorNormTwo {d : ℕ}
    (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Homogenization.cubeBesovPositiveVectorNormTwo Q s F

/-- Public alias for the overlapping cube attached to a fine-grid center. -/
abbrev overlapCubeSet {d : ℕ} (S : Cube d) : Set (Vec d) :=
  Homogenization.overlapCubeSet S

/-- Public alias for the volume of an overlapping cube. -/
noncomputable abbrev overlapCubeVolume {d : ℕ} (S : Cube d) : ℝ :=
  Homogenization.overlapCubeVolume S

/-- Public alias for normalized measure on an overlapping cube. -/
noncomputable abbrev normalizedOverlapCubeMeasure {d : ℕ}
    (S : Cube d) : MeasureTheory.Measure (Vec d) :=
  Homogenization.normalizedOverlapCubeMeasure S

/-- Public alias for the scalar normalized average on an overlapping cube. -/
noncomputable abbrev overlapCubeAverage {d : ℕ}
    (S : Cube d) (f : Vec d → ℝ) : ℝ :=
  Homogenization.overlapCubeAverage S f

/-- Public alias for the coordinatewise vector average on an overlapping cube. -/
noncomputable abbrev overlapCubeAverageVec {d : ℕ}
    (S : Cube d) (u : Vec d → Vec d) : Vec d :=
  Homogenization.overlapCubeAverageVec S u

/-- Public alias for the normalized `Lᵖ` norm on an overlapping cube. -/
noncomputable abbrev overlapCubeLpNorm {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (S : Cube d) (p : ℝ≥0∞)
    (u : Vec d → E) : ℝ :=
  Homogenization.overlapCubeLpNorm S p u

/-- Public alias for vector fluctuation around the overlapping-cube average. -/
noncomputable abbrev overlapCubeFluctuationVec {d : ℕ}
    (S : Cube d) (u : Vec d → Vec d) : Vec d → Vec d :=
  Homogenization.overlapCubeFluctuationVec S u

/-- Public alias for the filtered fine-grid centers used by the corrected
overlapping positive norm. -/
noncomputable abbrev overlapCentersAtDepth {d : ℕ}
    (Q : Cube d) (j : ℕ) : Finset (Cube d) :=
  Homogenization.overlapCentersAtDepth Q j

/-- Public alias for finite averaging over the overlapping centers. -/
noncomputable abbrev overlapCentersAverage {d : ℕ}
    (Q : Cube d) (j : ℕ) (F : Cube d → ℝ) : ℝ :=
  Homogenization.overlapCentersAverage Q j F

/-- Public alias for overlap centers whose overlapping cube contains a fixed
point. -/
noncomputable abbrev overlapCentersAtDepthContaining {d : ℕ}
    (Q : Cube d) (j : ℕ) (x : Vec d) : Finset (Cube d) :=
  Homogenization.overlapCentersAtDepthContaining Q j x

/-- Public alias for the depth-`j` overlapping positive square average. -/
noncomputable abbrev cubeBesovOverlappingPositiveVectorDepthAverage {d : ℕ}
    (Q : Cube d) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  Homogenization.cubeBesovOverlappingPositiveVectorDepthAverage Q F j

/-- Public alias for the depth-`j` corrected overlapping positive Besov
contribution. -/
noncomputable abbrev cubeBesovOverlappingPositiveVectorDepthSeminorm {d : ℕ}
    (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  Homogenization.cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j

/-- Public alias for finite-depth corrected overlapping positive Besov
seminorms. -/
noncomputable abbrev cubeBesovOverlappingPositiveVectorPartialSeminormTwo {d : ℕ}
    (Q : Cube d) (s : ℝ) (N : ℕ) (F : Vec d → Vec d) : ℝ :=
  Homogenization.cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F

/-- Public alias for the corrected overlapping positive vector
`B^s_{2,2}` seminorm. -/
noncomputable abbrev cubeBesovOverlappingPositiveVectorSeminormTwo {d : ℕ}
    (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Homogenization.cubeBesovOverlappingPositiveVectorSeminormTwo Q s F

/-- Public alias for the corrected overlapping positive vector `B^s_{2,2}`
norm used by the legacy discrete compatibility route, not the source theorem
pending the continuum `K`/`H^s` gate. -/
noncomputable abbrev cubeBesovOverlappingPositiveVectorNormTwo {d : ℕ}
    (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Homogenization.cubeBesovOverlappingPositiveVectorNormTwo Q s F

/-- Public alias for corrected overlapping positive Besov regularity of a
vector datum. -/
abbrev CubeVectorOverlappingBesovHRegularity {d : ℕ}
    (Q : Cube d) (s : ℝ) (g : Vec d → Vec d) : Prop :=
  Homogenization.CubeVectorOverlappingBesovHRegularity Q s g

/-- Public alias for the weak zero-trace equation `-Δw = div h` on a cube. -/
abbrev CubeDirichletDivergenceProblem {d : ℕ}
    (Q : Cube d) (w : H10Function (openCubeSet Q))
    (h : Vec d → Vec d) : Prop :=
  Homogenization.CubeDirichletDivergenceProblem Q w h

/-- Legacy-local alias for the discrete compatibility statement, not the source
theorem pending the continuum `K`/`H^s` gate. -/
abbrev ConstantCoefficientDirichletBesovFunctionSpaces
    (d : ℕ) [NeZero d] : Prop :=
  Homogenization.DiscreteConstantCoefficientDirichletBesovFunctionSpaces d

/-- Public alias for the K-functional Besov norm model used by the discrete
compatibility route, not the source theorem pending the continuum `K`/`H^s`
gate. -/
abbrev CubeKBesovNormModel (d : ℕ) : Type :=
  Homogenization.CubeKBesovNormModel d

/-- Public alias for coordinatewise `H¹` vector-field competitors in the cube
K-functional. -/
abbrev CubeVectorH1Function {d : ℕ} (Q : Cube d) : Type :=
  Homogenization.CubeVectorH1Function Q

/-- Public alias for the averaged overlap-cube Poincare estimate for
coordinatewise `H¹` vector-field competitors. -/
abbrev CubeVectorH1OverlapPoincareEstimate (d : ℕ) (C : ℝ) : Prop :=
  Homogenization.CubeVectorH1OverlapPoincareEstimate d C

/-- Public alias for the coordinate-summed `H¹` gradient size of a vector
K-functional competitor. -/
noncomputable abbrev cubeVectorH1GradientCoordL2NormSum {d : ℕ} {Q : Cube d}
    (G : CubeVectorH1Function Q) : ℝ :=
  Homogenization.CubeVectorH1Function.gradientCoordL2NormSum G

/-- Public alias for the parent-normalized coordinate-summed `H¹` gradient
size used by the scale-correct K-functional. -/
noncomputable abbrev cubeVectorH1RelativeGradientCoordL2NormSum
    {d : ℕ} {Q : Cube d} (G : CubeVectorH1Function Q) : ℝ :=
  Homogenization.CubeVectorH1Function.relativeGradientCoordL2NormSum G

/-- Public alias for one competitor value in the discrete cube vector
K-functional. -/
noncomputable abbrev cubeVectorKFunctionalCompetitorValue {d : ℕ}
    (Q : Cube d) (t : ℝ) (F : Vec d → Vec d)
    (G : CubeVectorH1Function Q) : ℝ :=
  Homogenization.cubeVectorKFunctionalCompetitorValue Q t F G

/-- Public alias for the discrete cube vector K-functional. -/
noncomputable abbrev cubeVectorKFunctional {d : ℕ}
    (Q : Cube d) (t : ℝ) (F : Vec d → Vec d) : ℝ :=
  Homogenization.cubeVectorKFunctional Q t F

/-- Public alias for the depth-`j` K-functional Besov contribution. -/
noncomputable abbrev cubeKBesovVectorDepthSeminorm {d : ℕ}
    (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  Homogenization.cubeKBesovVectorDepthSeminorm Q s F j

/-- Public alias for the finite-depth K-functional Besov seminorm. -/
noncomputable abbrev cubeKBesovVectorPartialSeminormTwo {d : ℕ}
    (Q : Cube d) (s : ℝ) (N : ℕ) (F : Vec d → Vec d) : ℝ :=
  Homogenization.cubeKBesovVectorPartialSeminormTwo Q s N F

/-- Public alias for the full K-functional Besov seminorm. -/
noncomputable abbrev cubeKBesovVectorSeminormTwo {d : ℕ}
    (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Homogenization.cubeKBesovVectorSeminormTwo Q s F

/-- Public alias for the full K-functional Besov norm. -/
noncomputable abbrev cubeKBesovVectorNormTwo {d : ℕ}
    (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Homogenization.cubeKBesovVectorNormTwo Q s F

/-- Public alias for the canonical K-functional Besov norm model. -/
noncomputable abbrev cubeKBesovNormModel (d : ℕ) : CubeKBesovNormModel d :=
  Homogenization.cubeKBesovNormModel d

/-- Public alias for the pure K-functional/overlapping Besov norm equivalence
contract. -/
abbrev CubeKBesovOverlappingEquivalence
    {d : ℕ} (K : CubeKBesovNormModel d) : Prop :=
  Homogenization.CubeKBesovOverlappingEquivalence K

/-- Public alias for the Dirichlet divergence K-functional regularity
contract. -/
abbrev CubeKBesovDirichletRegularity
    {d : ℕ} (K : CubeKBesovNormModel d) : Prop :=
  Homogenization.CubeKBesovDirichletRegularity K

/-- Public alias for the input boundedness bridge used by the K-functional
Dirichlet regularity proof. -/
abbrev CubeKBesovInputBoundednessOfOverlappingHRegularity
    (d : ℕ) : Prop :=
  Homogenization.CubeKBesovInputBoundednessOfOverlappingHRegularity d

/-- Public alias for the finite-level pure K/overlapping partial-sum
comparison. -/
abbrev CubeKBesovPartialBoundByOverlappingPositive
    (d : ℕ) : Prop :=
  Homogenization.CubeKBesovPartialBoundByOverlappingPositive d

/-- Public alias for the mean-gradient estimate used by the K-functional
Dirichlet regularity proof. -/
abbrev CubeDirichletGradientAverageRegularity
    (d : ℕ) : Prop :=
  Homogenization.CubeDirichletGradientAverageRegularity d

/-- Public alias for pointwise-in-scale K-functional regularity of the
zero-Dirichlet divergence solution operator. -/
abbrev CubeKFunctionalDirichletPointwiseRegularity
    (d : ℕ) : Prop :=
  Homogenization.CubeKFunctionalDirichletPointwiseRegularity d

/-- Public alias for the endpoint decomposition used to prove pointwise
K-functional regularity. -/
abbrev CubeDirichletKEndpointDecomposition
    (d : ℕ) : Prop :=
  Homogenization.CubeDirichletKEndpointDecomposition d

/-- Public alias for the two-constant endpoint construction behind the
one-constant K-functional endpoint decomposition. -/
abbrev CubeDirichletKEndpointCompetitorConstruction
    (d : ℕ) : Prop :=
  Homogenization.CubeDirichletKEndpointCompetitorConstruction d

/-- Public alias for residual `L²` stability of two zero-Dirichlet
divergence-RHS solutions. -/
abbrev CubeDirichletDivergenceResidualL2Stability
    (d : ℕ) : Prop :=
  Homogenization.CubeDirichletDivergenceResidualL2Stability d

/-- Public alias for the Dirichlet `H²` endpoint viewed as an `H¹` lift of
vector-field competitors. -/
abbrev CubeDirichletH1CompetitorLiftRegularity
    (d : ℕ) : Prop :=
  Homogenization.CubeDirichletH1CompetitorLiftRegularity d

/-- Public alias for the sharper Dirichlet `H²` divergence-RHS competitor
regularity contract that implies the H¹ lift wrapper. -/
abbrev CubeDirichletDivergenceH2CompetitorRegularity
    (d : ℕ) : Prop :=
  Homogenization.CubeDirichletDivergenceH2CompetitorRegularity d

/-- Public alias for the weak-divergence realization bridge feeding the scalar
Dirichlet `H²` theorem. -/
abbrev CubeVectorH1DivergencePoissonRealization
    (d : ℕ) : Prop :=
  Homogenization.CubeVectorH1DivergencePoissonRealization d

/-- Public alias for the focused components implying the K-functional
Dirichlet Besov regularity contract. -/
abbrev CubeKBesovDirichletRegularityComponents
    (d : ℕ) : Prop :=
  Homogenization.CubeKBesovDirichletRegularityComponents d

/-- Public alias for the pure canonical K-functional/overlapping Besov theory,
including both norm equivalence and K-partial boundedness. -/
abbrev CubeKBesovCanonicalOverlappingTheory
    (d : ℕ) [NeZero d] : Prop :=
  Homogenization.CubeKBesovCanonicalOverlappingTheory d

/-- Public alias for the sharpened pure canonical K-functional/overlapping Besov
theory core. -/
abbrev CubeKBesovCanonicalOverlappingTheoryCore
    (d : ℕ) [NeZero d] : Prop :=
  Homogenization.CubeKBesovCanonicalOverlappingTheoryCore d

/-- Legacy-local alias for the discrete compatibility K-functional route, not
the source theorem pending the continuum `K`/`H^s` gate. -/
abbrev ConstantCoefficientDirichletBesovKFunctionalRoute
    (d : ℕ) [NeZero d] : Prop :=
  Homogenization.DiscreteConstantCoefficientDirichletBesovKFunctionalRoute d

/-- Public alias for the unit centered-cube zero-trace Poincare constant used
inside the Dirichlet solver-energy estimate. -/
noncomputable abbrev originCubeUnitZeroTraceH1CoerciveConstant
    (d : ℕ) [NeZero d] : ℝ :=
  Homogenization.CubeDirichletWeakPoissonProblem.originCubeUnitZeroTraceH1CoerciveConstant d

/-- Public alias for the scale-sharp centered-cube zero-trace Poincare
constant, obtained from the unit centered cube by dilation. -/
noncomputable abbrev originCubeZeroTraceH1CoerciveConstant
    (d : ℕ) [NeZero d] (m : ℤ) : ℝ :=
  Homogenization.CubeDirichletWeakPoissonProblem.originCubeZeroTraceH1CoerciveConstant d m

theorem originCubeUnitZeroTraceH1CoerciveConstant_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤ originCubeUnitZeroTraceH1CoerciveConstant d :=
  Homogenization.CubeDirichletWeakPoissonProblem.originCubeUnitZeroTraceH1CoerciveConstant_nonneg d

theorem originCubeUnitZeroTraceH1CoerciveConstant_bound
    {d : ℕ} [NeZero d]
    (u : H10Function (openCubeSet (originCube d 0))) :
    ‖u.toH1Function.toScalarL2‖ ≤
      originCubeUnitZeroTraceH1CoerciveConstant d *
        u.toH1Function.gradientCoordL2NormSum :=
  Homogenization.CubeDirichletWeakPoissonProblem.originCubeUnitZeroTraceH1CoerciveConstant_bound u

theorem originCubeZeroTraceH1CoerciveConstant_nonneg
    (d : ℕ) [NeZero d] (m : ℤ) :
    0 ≤ originCubeZeroTraceH1CoerciveConstant d m :=
  Homogenization.CubeDirichletWeakPoissonProblem.originCubeZeroTraceH1CoerciveConstant_nonneg d m

theorem originCubeZeroTraceH1CoerciveConstant_bound
    {d : ℕ} [NeZero d] {m : ℤ}
    (u : H10Function (openCubeSet (originCube d m))) :
    ‖u.toH1Function.toScalarL2‖ ≤
      originCubeZeroTraceH1CoerciveConstant d m *
        u.toH1Function.gradientCoordL2NormSum :=
  Homogenization.CubeDirichletWeakPoissonProblem.originCubeZeroTraceH1CoerciveConstant_bound u

theorem cubeDirichletH2RegularityConstantExact_nonneg
    {d : ℕ} [NeZero d] (Q : Cube d) :
    0 ≤ cubeDirichletH2RegularityConstantExact Q :=
  Homogenization.CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityConstantExact_nonneg Q

theorem cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤ cubeDirichletH2RegularityVolumeL2ConstantExact d :=
  Homogenization.CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d

theorem cubeDirichletH2RegularityConstantExact_eq_volume_rpow_half_mul_volumeL2ConstantExact
    {d : ℕ} [NeZero d] (Q : Cube d) :
    cubeDirichletH2RegularityConstantExact Q =
      (cubeVolume Q) ^ (1 / 2 : ℝ) *
        cubeDirichletH2RegularityVolumeL2ConstantExact d :=
  Homogenization.CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityConstantExact_eq_volume_rpow_half_mul_volumeL2ConstantExact
    Q

theorem CubeDirichletH2Regularity.constant_nonneg
    {d : ℕ} {Q : Cube d} {C : ℝ}
    (h : CubeDirichletH2Regularity Q C) :
    0 ≤ C :=
  Homogenization.CubeDirichletH2Regularity.constant_nonneg h

theorem CubeDirichletH2RegularityInDimension.constant_nonneg
    {d : ℕ} {C : ℝ}
    (h : CubeDirichletH2RegularityInDimension d C) :
    0 ≤ C :=
  Homogenization.CubeDirichletH2RegularityInDimension.constant_nonneg h

theorem CubeDirichletH2RegularityVolumeL2.constant_nonneg
    {d : ℕ} {Q : Cube d} {C : ℝ}
    (h : CubeDirichletH2RegularityVolumeL2 Q C) :
    0 ≤ C :=
  Homogenization.CubeDirichletH2RegularityVolumeL2.constant_nonneg h

theorem CubeDirichletH2RegularityVolumeL2InDimension.constant_nonneg
    {d : ℕ} {C : ℝ}
    (h : CubeDirichletH2RegularityVolumeL2InDimension d C) :
    0 ≤ C :=
  Homogenization.CubeDirichletH2RegularityVolumeL2InDimension.constant_nonneg h

theorem CubeDirichletH2Regularity.mono
    {d : ℕ} {Q : Cube d} {C D : ℝ}
    (h : CubeDirichletH2Regularity Q C)
    (hCD : C ≤ D) :
    CubeDirichletH2Regularity Q D :=
  Homogenization.CubeDirichletH2Regularity.mono h hCD

theorem CubeDirichletH2RegularityInDimension.mono
    {d : ℕ} {C D : ℝ}
    (h : CubeDirichletH2RegularityInDimension d C)
    (hCD : C ≤ D) :
    CubeDirichletH2RegularityInDimension d D :=
  Homogenization.CubeDirichletH2RegularityInDimension.mono h hCD

theorem CubeDirichletH2RegularityVolumeL2.mono
    {d : ℕ} {Q : Cube d} {C D : ℝ}
    (h : CubeDirichletH2RegularityVolumeL2 Q C)
    (hCD : C ≤ D) :
    CubeDirichletH2RegularityVolumeL2 Q D :=
  Homogenization.CubeDirichletH2RegularityVolumeL2.mono h hCD

theorem CubeDirichletH2RegularityVolumeL2InDimension.mono
    {d : ℕ} {C D : ℝ}
    (h : CubeDirichletH2RegularityVolumeL2InDimension d C)
    (hCD : C ≤ D) :
    CubeDirichletH2RegularityVolumeL2InDimension d D :=
  Homogenization.CubeDirichletH2RegularityVolumeL2InDimension.mono h hCD

/-- Public cube Dirichlet `H²` regularity with the current scale-indexed
constant. -/
theorem cubeDirichletH2RegularityExact
    {d : ℕ} [NeZero d] (Q : Cube d) :
    CubeDirichletH2Regularity Q
      (cubeDirichletH2RegularityConstantExact Q) :=
  Homogenization.CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityExact Q

/-- Public cube Dirichlet `H²` regularity with a dimension-only constant when
the forcing is measured in the unnormalized open-cube `L²` norm. -/
theorem cubeDirichletH2RegularityVolumeL2Exact
    {d : ℕ} [NeZero d] (Q : Cube d) :
    CubeDirichletH2RegularityVolumeL2 Q
      (cubeDirichletH2RegularityVolumeL2ConstantExact d) :=
  Homogenization.CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2Exact Q

theorem exists_cubeDirichletH2RegularityVolumeL2InDimension
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, CubeDirichletH2RegularityVolumeL2InDimension d C :=
  Homogenization.CubeDirichletWeakPoissonProblem.exists_cubeDirichletH2RegularityVolumeL2InDimension
    d

theorem cubeVectorH1GradientCoordL2NormSum_nonneg
    {d : ℕ} {Q : Cube d} (G : CubeVectorH1Function Q) :
    0 ≤ cubeVectorH1GradientCoordL2NormSum G :=
  Homogenization.CubeVectorH1Function.gradientCoordL2NormSum_nonneg G

theorem cubeVectorKFunctionalCompetitorValue_nonneg
    {d : ℕ} (Q : Cube d) (t : ℝ) (F : Vec d → Vec d)
    (G : CubeVectorH1Function Q) :
    0 ≤ cubeVectorKFunctionalCompetitorValue Q t F G :=
  Homogenization.cubeVectorKFunctionalCompetitorValue_nonneg Q t F G

theorem cubeVectorKFunctional_nonneg
    {d : ℕ} (Q : Cube d) (t : ℝ) (F : Vec d → Vec d) :
    0 ≤ cubeVectorKFunctional Q t F :=
  Homogenization.cubeVectorKFunctional_nonneg Q t F

theorem cubeVectorKFunctional_le_competitor
    {d : ℕ} (Q : Cube d) (t : ℝ) (F : Vec d → Vec d)
    (G : CubeVectorH1Function Q) :
    cubeVectorKFunctional Q t F ≤
      cubeVectorKFunctionalCompetitorValue Q t F G :=
  Homogenization.cubeVectorKFunctional_le_competitor Q t F G

theorem cubeVectorKFunctionalCompetitorValue_le_of_endpoint_bounds
    {d : ℕ} (Q : Cube d) (t C : ℝ) (F H : Vec d → Vec d)
    (V G : CubeVectorH1Function Q) (hC : 0 ≤ C)
    (hL2 :
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => F x - V.toField x) ≤
        C * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => H x - G.toField x))
    (hGrad :
      V.gradientCoordL2NormSum ≤ C * G.gradientCoordL2NormSum) :
    cubeVectorKFunctionalCompetitorValue Q t F V ≤
      C * cubeVectorKFunctionalCompetitorValue Q t H G :=
  Homogenization.cubeVectorKFunctionalCompetitorValue_le_of_endpoint_bounds
    Q t C F H V G hC hL2 hGrad

theorem cubeVectorKFunctional_le_of_forall_competitorValue_le
    {d : ℕ} (Q : Cube d) (t C : ℝ) (F H : Vec d → Vec d)
    (hC : 0 ≤ C)
    (hcomp :
      ∀ G : CubeVectorH1Function Q,
        ∃ V : CubeVectorH1Function Q,
          cubeVectorKFunctionalCompetitorValue Q t F V ≤
            C * cubeVectorKFunctionalCompetitorValue Q t H G) :
    cubeVectorKFunctional Q t F ≤ C * cubeVectorKFunctional Q t H :=
  Homogenization.cubeVectorKFunctional_le_of_forall_competitorValue_le
    Q t C F H hC hcomp

theorem cubeKBesovVectorDepthSeminorm_nonneg
    {d : ℕ} (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    0 ≤ cubeKBesovVectorDepthSeminorm Q s F j :=
  Homogenization.cubeKBesovVectorDepthSeminorm_nonneg Q s F j

theorem sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_le_mul_cubeVectorKFunctional_of_forall_competitorValue
    {d : ℕ} (Q : Cube d) (C : ℝ) (F : Vec d → Vec d) (j : ℕ)
    (hC : 0 ≤ C)
    (hcomp :
      ∀ G : CubeVectorH1Function Q,
        Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
          C *
            cubeVectorKFunctionalCompetitorValue Q
              (Real.rpow (3 : ℝ) (-(j : ℝ))) F G) :
    Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
      C * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F :=
  Homogenization.sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_le_mul_cubeVectorKFunctional_of_forall_competitorValue
    Q C F j hC hcomp

theorem cubeBesovOverlappingPositiveVectorDepthSeminorm_le_mul_cubeKBesovVectorDepthSeminorm_of_forall_competitorValue
    {d : ℕ} (Q : Cube d) (s C : ℝ) (F : Vec d → Vec d) (j : ℕ)
    (hC : 0 ≤ C)
    (hcomp :
      ∀ G : CubeVectorH1Function Q,
        Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
          C *
            cubeVectorKFunctionalCompetitorValue Q
              (Real.rpow (3 : ℝ) (-(j : ℝ))) F G) :
    cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j ≤
      C * cubeKBesovVectorDepthSeminorm Q s F j :=
  Homogenization.cubeBesovOverlappingPositiveVectorDepthSeminorm_le_mul_cubeKBesovVectorDepthSeminorm_of_forall_competitorValue
    Q s C F j hC hcomp

theorem cubeKBesovVectorDepthSeminorm_le_of_kFunctional_le
    {d : ℕ} (Q : Cube d) (s C : ℝ) (F G : Vec d → Vec d) (j : ℕ)
    (hK :
      cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F ≤
        C * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) G) :
    cubeKBesovVectorDepthSeminorm Q s F j ≤
      C * cubeKBesovVectorDepthSeminorm Q s G j :=
  Homogenization.cubeKBesovVectorDepthSeminorm_le_of_kFunctional_le
    Q s C F G j hK

theorem cubeKBesovVectorPartialSeminormTwo_nonneg
    {d : ℕ} (Q : Cube d) (s : ℝ) (N : ℕ) (F : Vec d → Vec d) :
    0 ≤ cubeKBesovVectorPartialSeminormTwo Q s N F :=
  Homogenization.cubeKBesovVectorPartialSeminormTwo_nonneg Q s N F

theorem sq_cubeKBesovVectorPartialSeminormTwo
    {d : ℕ} (Q : Cube d) (s : ℝ) (N : ℕ) (F : Vec d → Vec d) :
    (cubeKBesovVectorPartialSeminormTwo Q s N F) ^ 2 =
      Finset.sum (Finset.range (N + 1)) fun j =>
        (cubeKBesovVectorDepthSeminorm Q s F j) ^ 2 :=
  Homogenization.sq_cubeKBesovVectorPartialSeminormTwo Q s N F

theorem cubeKBesovVectorPartialSeminormTwo_le_of_forall_depthSeminorm_le
    {d : ℕ} (Q : Cube d) (s C : ℝ) (N : ℕ)
    (F G : Vec d → Vec d) (hC : 0 ≤ C)
    (hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeKBesovVectorDepthSeminorm Q s F j ≤
          C * cubeKBesovVectorDepthSeminorm Q s G j) :
    cubeKBesovVectorPartialSeminormTwo Q s N F ≤
      C * cubeKBesovVectorPartialSeminormTwo Q s N G :=
  Homogenization.cubeKBesovVectorPartialSeminormTwo_le_of_forall_depthSeminorm_le
    Q s C N F G hC hdepth

theorem cubeKBesovVectorPartialSeminormTwo_le_of_forall_kFunctional_le
    {d : ℕ} (Q : Cube d) (s C : ℝ) (N : ℕ)
    (F G : Vec d → Vec d) (hC : 0 ≤ C)
    (hK :
      ∀ j ∈ Finset.range (N + 1),
        cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F ≤
          C * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) G) :
    cubeKBesovVectorPartialSeminormTwo Q s N F ≤
      C * cubeKBesovVectorPartialSeminormTwo Q s N G :=
  Homogenization.cubeKBesovVectorPartialSeminormTwo_le_of_forall_kFunctional_le
    Q s C N F G hC hK

theorem cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_forall_depthSeminorm_le
    {d : ℕ} (Q : Cube d) (s C : ℝ) (N : ℕ)
    (F : Vec d → Vec d) (hC : 0 ≤ C)
    (hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j ≤
          C * cubeKBesovVectorDepthSeminorm Q s F j) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
      C * cubeKBesovVectorPartialSeminormTwo Q s N F :=
  Homogenization.cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_forall_depthSeminorm_le
    Q s C N F hC hdepth

theorem cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_forall_competitorValue
    {d : ℕ} (Q : Cube d) (s C : ℝ) (N : ℕ)
    (F : Vec d → Vec d) (hC : 0 ≤ C)
    (hcomp :
      ∀ j ∈ Finset.range (N + 1),
        ∀ G : CubeVectorH1Function Q,
          Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
            C *
              cubeVectorKFunctionalCompetitorValue Q
                (Real.rpow (3 : ℝ) (-(j : ℝ))) F G) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
      C * cubeKBesovVectorPartialSeminormTwo Q s N F :=
  Homogenization.cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_forall_competitorValue
    Q s C N F hC hcomp

theorem cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_overlapPoincare
    {d : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hPoincare : CubeVectorH1OverlapPoincareEstimate d C)
    (Q : Cube d) (s : ℝ) (N : ℕ) (F : Vec d → Vec d)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
      (8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 1) *
        cubeKBesovVectorPartialSeminormTwo Q s N F :=
  Homogenization.cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_overlapPoincare
    hC hPoincare Q s N F hF

theorem cubeKBesovVectorSeminormTwo_le_of_partialBound
    {d : ℕ} (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) {B : ℝ}
    (hB : ∀ N : ℕ, cubeKBesovVectorPartialSeminormTwo Q s N F ≤ B) :
    cubeKBesovVectorSeminormTwo Q s F ≤ B :=
  Homogenization.cubeKBesovVectorSeminormTwo_le_of_partialBound Q s F hB

theorem cubeKBesovVectorPartialSeminormTwo_le_seminorm_of_bddAbove
    {d : ℕ} (Q : Cube d) (s : ℝ) (F : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N F))
    (N : ℕ) :
    cubeKBesovVectorPartialSeminormTwo Q s N F ≤
      cubeKBesovVectorSeminormTwo Q s F :=
  Homogenization.cubeKBesovVectorPartialSeminormTwo_le_seminorm_of_bddAbove
    Q s F hBdd N

theorem cubeKBesovVectorSeminormTwo_nonneg_of_bddAbove
    {d : ℕ} (Q : Cube d) (s : ℝ) (F : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N F)) :
    0 ≤ cubeKBesovVectorSeminormTwo Q s F :=
  Homogenization.cubeKBesovVectorSeminormTwo_nonneg_of_bddAbove
    Q s F hBdd

theorem cubeKBesovVectorSeminormTwo_le_of_forall_partialSeminormTwo_le
    {d : ℕ} (Q : Cube d) (s C : ℝ) (F G : Vec d → Vec d)
    (hC : 0 ≤ C)
    (hG_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N G))
    (hpartial :
      ∀ N : ℕ,
        cubeKBesovVectorPartialSeminormTwo Q s N F ≤
          C * cubeKBesovVectorPartialSeminormTwo Q s N G) :
    cubeKBesovVectorSeminormTwo Q s F ≤
      C * cubeKBesovVectorSeminormTwo Q s G :=
  Homogenization.cubeKBesovVectorSeminormTwo_le_of_forall_partialSeminormTwo_le
    Q s C F G hC hG_bdd hpartial

theorem cubeKBesovVectorSeminormTwo_le_of_forall_kFunctional_le
    {d : ℕ} (Q : Cube d) (s C : ℝ) (F G : Vec d → Vec d)
    (hC : 0 ≤ C)
    (hG_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeKBesovVectorPartialSeminormTwo Q s N G))
    (hK :
      ∀ j : ℕ,
        cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) F ≤
          C * cubeVectorKFunctional Q (Real.rpow (3 : ℝ) (-(j : ℝ))) G) :
    cubeKBesovVectorSeminormTwo Q s F ≤
      C * cubeKBesovVectorSeminormTwo Q s G :=
  Homogenization.cubeKBesovVectorSeminormTwo_le_of_forall_kFunctional_le
    Q s C F G hC hG_bdd hK

theorem cubeKBesovVectorNormTwo_le_of_average_and_seminorm
    {d : ℕ} (Q : Cube d) (s C : ℝ) (F G : Vec d → Vec d)
    (havg :
      Real.sqrt (vecNormSq (cubeAverageVec Q F)) ≤
        C * Real.sqrt (vecNormSq (cubeAverageVec Q G)))
    (hsemi :
      cubeKBesovVectorSeminormTwo Q s F ≤
        C * cubeKBesovVectorSeminormTwo Q s G) :
    cubeKBesovVectorNormTwo Q s F ≤
      C * cubeKBesovVectorNormTwo Q s G :=
  Homogenization.cubeKBesovVectorNormTwo_le_of_average_and_seminorm
    Q s C F G havg hsemi

theorem mem_overlapCentersAtDepth_iff {d : ℕ}
    {Q S : Cube d} {j : ℕ} :
    S ∈ overlapCentersAtDepth Q j ↔
      S ∈ descendantsAtDepth Q (j + 1) ∧ overlapCubeSet S ⊆ cubeSet Q :=
  Homogenization.mem_overlapCentersAtDepth_iff

theorem overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth {d : ℕ}
    {Q S : Cube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    overlapCubeSet S ⊆ cubeSet Q :=
  Homogenization.overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth hS

theorem overlapCentersAverage_le_overlapCentersAverage {d : ℕ}
    (Q : Cube d) (j : ℕ) {F G : Cube d → ℝ}
    (hFG : ∀ S ∈ overlapCentersAtDepth Q j, F S ≤ G S) :
    overlapCentersAverage Q j F ≤ overlapCentersAverage Q j G :=
  Homogenization.overlapCentersAverage_le_overlapCentersAverage Q j hFG

theorem overlapCentersAtDepth_nonempty {d : ℕ}
    (Q : Cube d) (j : ℕ) :
    (overlapCentersAtDepth Q j).Nonempty :=
  Homogenization.overlapCentersAtDepth_nonempty Q j

theorem overlapCentersAtDepth_card_pos {d : ℕ}
    (Q : Cube d) (j : ℕ) :
    0 < (overlapCentersAtDepth Q j).card :=
  Homogenization.overlapCentersAtDepth_card_pos Q j

theorem overlapCentersAtDepth_card_ne_zero {d : ℕ}
    (Q : Cube d) (j : ℕ) :
    (overlapCentersAtDepth Q j).card ≠ 0 :=
  Homogenization.overlapCentersAtDepth_card_ne_zero Q j

theorem overlapCentersAtDepth_card_le_pow {d : ℕ}
    (Q : Cube d) (j : ℕ) :
    (overlapCentersAtDepth Q j).card ≤ (3 ^ d) ^ (j + 1) :=
  Homogenization.overlapCentersAtDepth_card_le_pow Q j

theorem overlapCentersAverage_const {d : ℕ}
    (Q : Cube d) (j : ℕ) (c : ℝ) :
    overlapCentersAverage Q j (fun _ => c) = c :=
  Homogenization.overlapCentersAverage_const Q j c

theorem exists_mem_overlapCentersAtDepth_of_mem_cubeSet {d : ℕ}
    {Q : Cube d} {x : Vec d} (j : ℕ)
    (hx : x ∈ cubeSet Q) :
    ∃ S ∈ overlapCentersAtDepth Q j, x ∈ overlapCubeSet S :=
  Homogenization.exists_mem_overlapCentersAtDepth_of_mem_cubeSet j hx

theorem cubeSet_subset_iUnion_overlapCentersAtDepth {d : ℕ}
    (Q : Cube d) (j : ℕ) :
    cubeSet Q ⊆
      ⋃ S ∈ (overlapCentersAtDepth Q j : Set (Cube d)),
        overlapCubeSet S :=
  Homogenization.cubeSet_subset_iUnion_overlapCentersAtDepth Q j

theorem descendantsAtDepth_card_le_overlapCentersAtDepth_card {d : ℕ}
    (Q : Cube d) (j : ℕ) :
    (descendantsAtDepth Q j).card ≤ (overlapCentersAtDepth Q j).card :=
  Homogenization.descendantsAtDepth_card_le_overlapCentersAtDepth_card Q j

theorem pow_le_overlapCentersAtDepth_card {d : ℕ}
    (Q : Cube d) (j : ℕ) :
    (3 ^ d) ^ j ≤ (overlapCentersAtDepth Q j).card :=
  Homogenization.pow_le_overlapCentersAtDepth_card Q j

theorem mem_overlapCentersAtDepthContaining_iff {d : ℕ}
    {Q S : Cube d} {j : ℕ} {x : Vec d} :
    S ∈ overlapCentersAtDepthContaining Q j x ↔
      S ∈ overlapCentersAtDepth Q j ∧ x ∈ overlapCubeSet S :=
  Homogenization.mem_overlapCentersAtDepthContaining_iff

theorem overlapCentersAtDepthContaining_card_le_pow {d : ℕ}
    (Q : Cube d) (j : ℕ) (x : Vec d) :
    (overlapCentersAtDepthContaining Q j x).card ≤ 3 ^ d :=
  Homogenization.overlapCentersAtDepthContaining_card_le_pow Q j x

theorem measurableSet_overlapCubeSet {d : ℕ} (S : Cube d) :
    MeasurableSet (overlapCubeSet S) :=
  Homogenization.measurableSet_overlapCubeSet S

theorem volume_overlapCubeSet_toReal {d : ℕ} (S : Cube d) :
    (MeasureTheory.volume (overlapCubeSet S)).toReal = overlapCubeVolume S :=
  Homogenization.volume_overlapCubeSet_toReal S

theorem overlapCubeVolume_eq_cubeVolume_div_pow_of_mem_overlapCentersAtDepth
    {d : ℕ} {Q S : Cube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    overlapCubeVolume S = cubeVolume Q / (((3 : ℝ) ^ d) ^ j) :=
  Homogenization.overlapCubeVolume_eq_cubeVolume_div_pow_of_mem_overlapCentersAtDepth hS

theorem cubeVolume_le_card_mul_overlapCubeVolume_of_mem_overlapCentersAtDepth
    {d : ℕ} {Q S : Cube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    cubeVolume Q ≤ ((overlapCentersAtDepth Q j).card : ℝ) * overlapCubeVolume S :=
  Homogenization.cubeVolume_le_card_mul_overlapCubeVolume_of_mem_overlapCentersAtDepth hS

theorem overlapCentersAtDepth_sum_setLIntegral_le_mul_setLIntegral_cubeSet
    {d : ℕ} (Q : Cube d) (j : ℕ) {f : Vec d → ℝ≥0∞}
    (hfQ : AEMeasurable f (MeasureTheory.volume.restrict (cubeSet Q)))
    (hfS :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable f (MeasureTheory.volume.restrict (overlapCubeSet S))) :
    ∑ S ∈ overlapCentersAtDepth Q j,
        ∫⁻ x in overlapCubeSet S, f x ∂MeasureTheory.volume
      ≤ (3 ^ d : ℝ≥0∞) *
          ∫⁻ x in cubeSet Q, f x ∂MeasureTheory.volume :=
  Homogenization.overlapCentersAtDepth_sum_setLIntegral_le_mul_setLIntegral_cubeSet
    Q j hfQ hfS

theorem overlapCentersAtDepth_average_lintegral_normalizedOverlapCubeMeasure_le
    {d : ℕ} (Q : Cube d) (j : ℕ) {f : Vec d → ℝ≥0∞}
    (hfQ : AEMeasurable f (MeasureTheory.volume.restrict (cubeSet Q)))
    (hfS :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable f (MeasureTheory.volume.restrict (overlapCubeSet S))) :
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
        (∑ S ∈ overlapCentersAtDepth Q j,
          ∫⁻ x, f x ∂(normalizedOverlapCubeMeasure S))
      ≤ (3 ^ d : ℝ≥0∞) *
          ∫⁻ x, f x ∂(normalizedCubeMeasure Q) :=
  Homogenization.overlapCentersAtDepth_average_lintegral_normalizedOverlapCubeMeasure_le
    Q j hfQ hfS

theorem cubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : Cube d) (f : Vec d → E) :
    (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ 2 =
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ normalizedCubeMeasure Q).toReal :=
  Homogenization.cubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal Q f

theorem overlapCubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (S : Cube d) (f : Vec d → E) :
    (overlapCubeLpNorm S (2 : ℝ≥0∞) f) ^ 2 =
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ normalizedOverlapCubeMeasure S).toReal :=
  Homogenization.overlapCubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal S f

theorem memLp_cubeMeasure_of_memLp_normalizedCubeMeasure
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : Cube d) {p : ℝ≥0∞} {f : Vec d → E}
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp f p (cubeMeasure Q) :=
  Homogenization.memLp_cubeMeasure_of_memLp_normalizedCubeMeasure Q hf

theorem memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {Q S : Cube d} {j : ℕ} {p : ℝ≥0∞} {f : Vec d → E}
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp f p (normalizedOverlapCubeMeasure S) :=
  Homogenization.memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure
    hS hf

theorem overlapCentersAverage_lintegral_rpow_enorm_two_le
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (Q : Cube d) (j : ℕ) (R : Vec d → E)
    (hR : MeasureTheory.MemLp R (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hRloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp R (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCentersAverage Q j
        (fun S => (∫⁻ x, ‖R x‖ₑ ^ (2 : ℝ)
          ∂ normalizedOverlapCubeMeasure S).toReal)
      ≤ (3 ^ d : ℝ) *
          (∫⁻ x, ‖R x‖ₑ ^ (2 : ℝ) ∂ normalizedCubeMeasure Q).toReal :=
  Homogenization.overlapCentersAverage_lintegral_rpow_enorm_two_le
    Q j R hR hRloc

theorem overlapCubeLpNorm_two_overlapCubeFluctuationVec_le_two_mul_overlapCubeLpNorm_two
    {d : ℕ} (S : Cube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S u) ≤
      2 * overlapCubeLpNorm S (2 : ℝ≥0∞) u :=
  Homogenization.overlapCubeLpNorm_two_overlapCubeFluctuationVec_le_two_mul_overlapCubeLpNorm_two
    S u hu

theorem overlapCubeAverage_add_of_memLp_two
    {d : ℕ} (S : Cube d) {f g : Vec d → ℝ}
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeAverage S (fun x => f x + g x) =
      overlapCubeAverage S f + overlapCubeAverage S g :=
  Homogenization.overlapCubeAverage_add_of_memLp_two S hf hg

theorem overlapCubeAverageVec_add_of_memLp_two
    {d : ℕ} (S : Cube d) {u v : Vec d → Vec d}
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeAverageVec S (fun x => u x + v x) =
      overlapCubeAverageVec S u + overlapCubeAverageVec S v :=
  Homogenization.overlapCubeAverageVec_add_of_memLp_two S hu hv

theorem memLp_overlapCubeFluctuationVec
    {d : ℕ} (S : Cube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    MeasureTheory.MemLp (overlapCubeFluctuationVec S u) (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S) :=
  Homogenization.memLp_overlapCubeFluctuationVec S u hu

theorem overlapCubeFluctuationVec_add_of_memLp_two
    {d : ℕ} (S : Cube d) {u v : Vec d → Vec d}
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeFluctuationVec S (fun x => u x + v x) =
      fun x => overlapCubeFluctuationVec S u x +
        overlapCubeFluctuationVec S v x :=
  Homogenization.overlapCubeFluctuationVec_add_of_memLp_two S hu hv

theorem cubeBesovOverlappingPositiveVectorDepthAverage_add_le
    {d : ℕ} (Q : Cube d) (u v : Vec d → Vec d) (j : ℕ)
    (hu :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hv :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q (fun x => u x + v x) j ≤
      2 * cubeBesovOverlappingPositiveVectorDepthAverage Q u j +
        2 * cubeBesovOverlappingPositiveVectorDepthAverage Q v j :=
  Homogenization.cubeBesovOverlappingPositiveVectorDepthAverage_add_le
    Q u v j hu hv

theorem cubeBesovOverlappingPositiveVectorDepthAverage_residual_le
    {d : ℕ} (Q : Cube d) (R : Vec d → Vec d) (j : ℕ)
    (hR : MeasureTheory.MemLp R (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hRloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp R (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q R j ≤
      4 * (3 ^ d : ℝ) * (cubeLpNorm Q (2 : ℝ≥0∞) R) ^ 2 :=
  Homogenization.cubeBesovOverlappingPositiveVectorDepthAverage_residual_le
    Q R j hR hRloc

theorem cubeBesovOverlappingPositiveVectorDepthAverage_toField_le_of_overlapPoincare
    {d : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hPoincare : CubeVectorH1OverlapPoincareEstimate d C)
    (Q : Cube d) (j : ℕ) (G : CubeVectorH1Function Q) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j ≤
      (C * Real.rpow (3 : ℝ) (-(j : ℝ)) *
        cubeVectorH1RelativeGradientCoordL2NormSum G) ^ 2 :=
  Homogenization.cubeBesovOverlappingPositiveVectorDepthAverage_toField_le_of_overlapPoincare
    hC hPoincare Q j G

theorem sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_le_mul_cubeVectorKFunctionalCompetitorValue_of_overlapPoincare
    {d : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hPoincare : CubeVectorH1OverlapPoincareEstimate d C)
    (Q : Cube d) (F : Vec d → Vec d) (j : ℕ)
    (G : CubeVectorH1Function Q)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
      (8 * (3 ^ d : ℝ) + 2 * C ^ 2 + 1) *
        cubeVectorKFunctionalCompetitorValue Q
          (Real.rpow (3 : ℝ) (-(j : ℝ))) F G :=
  Homogenization.sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_le_mul_cubeVectorKFunctionalCompetitorValue_of_overlapPoincare
    hC hPoincare Q F j G hF

theorem sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo
    {d : ℕ} (Q : Cube d) (s : ℝ) (N : ℕ) (F : Vec d → Vec d) :
    (cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F) ^ 2 =
      Finset.sum (Finset.range (N + 1)) fun j =>
        (Homogenization.cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2 :=
  Homogenization.sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F

theorem cubeBesovOverlappingPositiveVectorSeminormTwo_le_of_partialBound
    {d : ℕ} (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) {B : ℝ}
    (hB :
      ∀ N : ℕ, cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤ B) :
    cubeBesovOverlappingPositiveVectorSeminormTwo Q s F ≤ B :=
  Homogenization.cubeBesovOverlappingPositiveVectorSeminormTwo_le_of_partialBound
    Q s F hB

theorem cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_seminorm_of_bddAbove
    {d : ℕ} (Q : Cube d) (s : ℝ) (F : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F))
    (N : ℕ) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
      cubeBesovOverlappingPositiveVectorSeminormTwo Q s F :=
  Homogenization.cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_seminorm_of_bddAbove
    Q s F hBdd N

theorem cubeBesovOverlappingPositiveVectorSeminormTwo_nonneg_of_bddAbove
    {d : ℕ} (Q : Cube d) (s : ℝ) (F : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F)) :
    0 ≤ cubeBesovOverlappingPositiveVectorSeminormTwo Q s F :=
  Homogenization.cubeBesovOverlappingPositiveVectorSeminormTwo_nonneg_of_bddAbove
    Q s F hBdd

theorem cubeBesovOverlappingPositiveVectorNormTwo_nonneg_of_bddAbove
    {d : ℕ} (Q : Cube d) (s : ℝ) (F : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F)) :
    0 ≤ cubeBesovOverlappingPositiveVectorNormTwo Q s F :=
  Homogenization.cubeBesovOverlappingPositiveVectorNormTwo_nonneg_of_bddAbove
    Q s F hBdd

theorem CubeVectorOverlappingBesovHRegularity.partialSeminorm_le_seminorm
    {d : ℕ} {Q : Cube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : CubeVectorOverlappingBesovHRegularity Q s g) (N : ℕ) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N g ≤
      cubeBesovOverlappingPositiveVectorSeminormTwo Q s g :=
  Homogenization.CubeVectorOverlappingBesovHRegularity.partialSeminorm_le_seminorm
    hg N

theorem CubeVectorOverlappingBesovHRegularity.seminorm_nonneg
    {d : ℕ} {Q : Cube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : CubeVectorOverlappingBesovHRegularity Q s g) :
    0 ≤ cubeBesovOverlappingPositiveVectorSeminormTwo Q s g :=
  Homogenization.CubeVectorOverlappingBesovHRegularity.seminorm_nonneg hg

theorem CubeVectorOverlappingBesovHRegularity.norm_nonneg
    {d : ℕ} {Q : Cube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : CubeVectorOverlappingBesovHRegularity Q s g) :
    0 ≤ cubeBesovOverlappingPositiveVectorNormTwo Q s g :=
  Homogenization.CubeVectorOverlappingBesovHRegularity.norm_nonneg hg

theorem cubeKBesovDirichletRegularity_of_components
    {d : ℕ}
    (hcomponents : CubeKBesovDirichletRegularityComponents d) :
    CubeKBesovDirichletRegularity (cubeKBesovNormModel d) :=
  Homogenization.cubeKBesovDirichletRegularity_of_components hcomponents

theorem cubeKFunctionalDirichletPointwiseRegularity_of_endpointDecomposition
    {d : ℕ}
    (hendpoint : CubeDirichletKEndpointDecomposition d) :
    CubeKFunctionalDirichletPointwiseRegularity d :=
  Homogenization.cubeKFunctionalDirichletPointwiseRegularity_of_endpointDecomposition
    hendpoint

theorem cubeDirichletKEndpointDecomposition_of_competitorConstruction
    {d : ℕ}
    (hendpoint : CubeDirichletKEndpointCompetitorConstruction d) :
    CubeDirichletKEndpointDecomposition d :=
  Homogenization.cubeDirichletKEndpointDecomposition_of_competitorConstruction
    hendpoint

theorem cubeDirichletKEndpointCompetitorConstruction_of_residualStability_of_liftRegularity
    {d : ℕ}
    (hstable : CubeDirichletDivergenceResidualL2Stability d)
    (hlift : CubeDirichletH1CompetitorLiftRegularity d) :
    CubeDirichletKEndpointCompetitorConstruction d :=
  Homogenization.cubeDirichletKEndpointCompetitorConstruction_of_residualStability_of_liftRegularity
    hstable hlift

/-- Public Chapter 1 finite-level K-functional partial-sum comparison. -/
theorem cubeKBesovPartialBoundByOverlappingPositive
    (d : ℕ) [NeZero d] :
    CubeKBesovPartialBoundByOverlappingPositive d :=
  Homogenization.cubeKBesovPartialBoundByOverlappingPositive d

/-- Public Chapter 1 input boundedness bridge for the K-functional
regularity proof. -/
theorem cubeKBesovInputBoundednessOfOverlappingHRegularity
    (d : ℕ) [NeZero d] :
    CubeKBesovInputBoundednessOfOverlappingHRegularity d :=
  Homogenization.cubeKBesovInputBoundednessOfOverlappingHRegularity d

/-- Public Chapter 1 mean-gradient regularity input for zero-Dirichlet
divergence solutions. -/
theorem cubeDirichletGradientAverageRegularity
    (d : ℕ) [NeZero d] :
    CubeDirichletGradientAverageRegularity d :=
  Homogenization.cubeDirichletGradientAverageRegularity d

/-- Public Chapter 1 pointwise K-functional regularity input for
zero-Dirichlet divergence solutions. -/
theorem cubeKFunctionalDirichletPointwiseRegularity
    (d : ℕ) [NeZero d] :
    CubeKFunctionalDirichletPointwiseRegularity d :=
  Homogenization.cubeKFunctionalDirichletPointwiseRegularity d

/-- Public Chapter 1 one-solution `L²` energy estimate input for
zero-Dirichlet divergence solutions. -/
theorem cubeDirichletDivergenceEnergyEstimate
    (d : ℕ) [NeZero d] :
    CubeDirichletDivergenceEnergyEstimate d :=
  Homogenization.cubeDirichletDivergenceEnergyEstimate d

/-- Public Chapter 1 residual `L²` stability input for the endpoint
construction. -/
theorem cubeDirichletDivergenceResidualL2Stability
    (d : ℕ) [NeZero d] :
    CubeDirichletDivergenceResidualL2Stability d :=
  Homogenization.cubeDirichletDivergenceResidualL2Stability d

/-- Public Chapter 1 Dirichlet `H²`/`H¹` lift input for the endpoint
construction. -/
theorem cubeDirichletH1CompetitorLiftRegularity
    (d : ℕ) [NeZero d] :
    CubeDirichletH1CompetitorLiftRegularity d :=
  Homogenization.cubeDirichletH1CompetitorLiftRegularity d

/-- Public Chapter 1 sharpened Dirichlet `H²` divergence-RHS competitor
regularity input behind the formal H¹ lift wrapper. -/
theorem cubeDirichletDivergenceH2CompetitorRegularity
    (d : ℕ) [NeZero d] :
    CubeDirichletDivergenceH2CompetitorRegularity d :=
  Homogenization.cubeDirichletDivergenceH2CompetitorRegularity d

/-- Public Chapter 1 weak-divergence realization bridge behind the sharpened
Dirichlet `H²` competitor theorem. -/
theorem cubeVectorH1DivergencePoissonRealization
    (d : ℕ) [NeZero d] :
    CubeVectorH1DivergencePoissonRealization d :=
  Homogenization.cubeVectorH1DivergencePoissonRealization d

/-- Public Chapter 1 two-constant endpoint construction input for pointwise
K-functional regularity. -/
theorem cubeDirichletKEndpointCompetitorConstruction
    (d : ℕ) [NeZero d] :
    CubeDirichletKEndpointCompetitorConstruction d :=
  Homogenization.cubeDirichletKEndpointCompetitorConstruction d

/-- Public Chapter 1 endpoint decomposition input for pointwise K-functional
regularity. -/
theorem cubeDirichletKEndpointDecomposition
    (d : ℕ) [NeZero d] :
    CubeDirichletKEndpointDecomposition d :=
  Homogenization.cubeDirichletKEndpointDecomposition d

/-- Public Chapter 1 focused components for the K-functional Dirichlet
regularity theorem. -/
theorem cubeKBesovDirichletRegularityComponents
    (d : ℕ) [NeZero d] :
    CubeKBesovDirichletRegularityComponents d :=
  Homogenization.cubeKBesovDirichletRegularityComponents d

/-- Public Chapter 1 PDE/K-functional input: boundedness of the zero-Dirichlet
divergence solution operator in the canonical K-functional Besov norm. -/
theorem cubeKBesovDirichletRegularity
    (d : ℕ) [NeZero d] :
    CubeKBesovDirichletRegularity (cubeKBesovNormModel d) :=
  Homogenization.cubeKBesovDirichletRegularity d

/-- Legacy-local name for the discrete compatibility theorem; it is not the
source theorem pending the continuum `K`/`H^s` gate. -/
theorem constantCoefficientDirichletBesovFunctionSpaces
    (d : ℕ) [NeZero d] :
    ConstantCoefficientDirichletBesovFunctionSpaces d :=
  Homogenization.discreteConstantCoefficientDirichletBesovFunctionSpaces d

end Legacy

end

end Ch01
end Book
end Homogenization
