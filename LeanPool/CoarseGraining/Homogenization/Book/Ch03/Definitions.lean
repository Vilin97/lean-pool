/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Definitions
public import LeanPool.CoarseGraining.Homogenization.Ambient.ScalarMatrix
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionSharpKernel
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Regularity
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation

/-! # Definitions -/

@[expose] public section

open scoped BigOperators ENNReal Pointwise

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Chapter 3 public vocabulary

This file contains the note-facing quantities used in Chapter 3.  The
coefficient input is the Chapter 2 `TriadicCoeffFamily`, so all ellipticity and
compatibility data remain a.e.-based on open cube domains.
-/

noncomputable section

abbrev CoeffFamily (d : ℕ) :=
  Ch02.TriadicCoeffFamily d

abbrev CubeSolution {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d) :=
  Ch02.Solution (Ch02.cubeDomain Q) (a.coeffOn Q)

/-- Public regularity package for the manuscript assumption
`g ∈ H^s(Q; R^d)`, in the form consumed by the deterministic RHS development. -/
abbrev ForceBesovRegularity {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (g : Vec d → Vec d) : Prop :=
  CubeVectorBesovHRegularity Q s g

/-- The depth-`j` block-average square for a vector field on a parent cube. -/
noncomputable def negativeBesovVectorDepthAverage {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  descendantsAverage Q j fun R => vecNormSq (cubeAverageVec R F)

/-- The note-normalized depth contribution in `3^{-s m} B^{-s}_{2,q}`.

If `R` is a depth-`j` descendant of a scale-`m` cube, the outer factor
`3^{-s m}` combines with the scale of `R` to give this `3^{-s j}` weight. -/
noncomputable def negativeBesovVectorDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
    Real.sqrt (negativeBesovVectorDepthAverage Q F j)

/-- Finite-depth vector-valued `3^{-s m} B^{-s}_{2,q}` seminorm for finite
multiscale exponent `q`. -/
noncomputable def negativeBesovVectorPartialNormFinite {d : ℕ}
    (Q : TriadicCube d) (s q : ℝ) (N : ℕ) (F : Vec d → Vec d) : ℝ :=
  Real.rpow
    (Finset.sum (Finset.range (N + 1)) fun j =>
      Real.rpow (negativeBesovVectorDepthSeminorm Q s F j) q)
    (1 / q)

/-- Public vector-valued `3^{-s m} B^{-s}_{2,q}` seminorm on a cube of scale
`m`, using Euclidean norms of the cube-averaged vector field. -/
noncomputable def scaleNormalizedNegativeBesovVectorNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (F : Vec d → Vec d) : ℝ :=
  match q with
  | .finite q =>
      sSup (Set.range fun N : ℕ =>
        negativeBesovVectorPartialNormFinite Q s q N F)
  | .infinity =>
      sSup (Set.range fun j : ℕ =>
        negativeBesovVectorDepthSeminorm Q s F j)

/-- Note-normalized positive `q = 2` Besov seminorm
`3^{s m} [F]_{\underline B^s_{2,2}(Q)}` for vector fields. -/
noncomputable abbrev scaleNormalizedPositiveBesovVectorSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  cubeBesovPositiveVectorSeminormTwo Q s F

/-- Note-normalized positive `q = 2` Besov norm for vector fields.

The positive seminorms in the deterministic RHS layer are already normalized by
the parent scale.  The full norm adds the top-scale average, matching
`3^{s m} ||F||_{\underline B^s_{2,2}(Q)}`. -/
noncomputable def scaleNormalizedPositiveBesovVectorNormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Real.sqrt (vecNormSq (cubeAverageVec Q F)) +
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s F

/-- Public vector-valued genuine dual negative Besov norm, normalized as
`3^{-s m} [F]_{\underline B^{-s}_{2,2}(Q)}`.

This is deliberately separate from `scaleNormalizedNegativeBesovVectorNorm`,
which is the concrete/circ seminorm used in the homogeneous coarse-graining
estimates. -/
noncomputable def scaleNormalizedDualNegativeBesovVectorNormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Real.rpow (3 : ℝ) (-s * (((Q.scale : ℤ) : ℝ))) *
    ∑ i : Fin d,
      cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (fun x => F x i)

/-- Open cube with arbitrary center and triadic scale. -/
noncomputable def openCubeAtScale {d : ℕ} (center : Vec d) (m : ℤ) : Set (Vec d) :=
  { y | ∀ i : Fin d,
      |y i - center i| < Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2 }

theorem isOpen_openCubeAtScale {d : ℕ} (center : Vec d) (m : ℤ) :
    IsOpen (openCubeAtScale center m) := by
  classical
  unfold openCubeAtScale
  rw [show
      {y : Vec d | ∀ i : Fin d,
          |y i - center i| < Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2} =
        ⋂ i : Fin d,
          {y : Vec d |
            |y i - center i| < Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2} by
    ext y
    simp]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Iio.preimage
      ((continuous_abs.comp ((continuous_apply i).sub continuous_const)))

theorem measurableSet_openCubeAtScale {d : ℕ} (center : Vec d) (m : ℤ) :
    MeasurableSet (openCubeAtScale center m) :=
  (isOpen_openCubeAtScale center m).measurableSet

theorem openCubeAtScale_eq_pi_Ioo {d : ℕ} (center : Vec d) (m : ℤ) :
    openCubeAtScale center m =
      Set.pi Set.univ
        (fun i : Fin d =>
          Set.Ioo
            (center i - Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2)
            (center i + Real.rpow (3 : ℝ) (((m : ℤ) : ℝ)) / 2)) := by
  ext y
  constructor
  · intro hy i _
    rcases (abs_sub_lt_iff.mp (hy i)) with ⟨hleft, hright⟩
    constructor <;> linarith
  · intro hy i
    rcases hy i (by simp) with ⟨hleft, hright⟩
    exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩

theorem openCubeAtScale_zero_eq_openCubeSet_originCube {d : ℕ} (m : ℤ) :
    openCubeAtScale (0 : Vec d) m = openCubeSet (originCube d m) := by
  rw [openCubeAtScale_eq_pi_Ioo, openCubeSet_eq_pi_Ioo]
  simp [originCube, cubeScaleFactor]
  congr
  funext i
  congr <;> ring_nf

theorem openCubeAtScale_eq_translateSet {d : ℕ} (center : Vec d) (m : ℤ) :
    openCubeAtScale center m =
      translateSet center (openCubeAtScale (0 : Vec d) m) := by
  ext y
  rw [mem_translateSet_iff_sub_mem]
  simp [openCubeAtScale]

theorem openCubeAtScale_eq_translateSet_smul_originCube_zero {d : ℕ}
    (center : Vec d) (m : ℤ) :
    openCubeAtScale center m =
      translateSet center
        (cubeScaleFactor (originCube d m) • openCubeAtScale (0 : Vec d) 0) := by
  rw [openCubeAtScale_eq_translateSet, openCubeAtScale_zero_eq_openCubeSet_originCube,
    openCubeSet_originCube_eq_smul_originCube_zero]
  rw [← openCubeAtScale_zero_eq_openCubeSet_originCube (d := d) 0]

theorem openCubeAtScale_eq_translateSet_sub {d : ℕ}
    (z center : Vec d) (m : ℤ) :
    openCubeAtScale center m =
      translateSet z (openCubeAtScale (center - z) m) := by
  ext y
  rw [mem_translateSet_iff_sub_mem]
  constructor
  · intro hy i
    have hcoord :
        (y - z) i - (center - z) i = y i - center i := by
      simp [sub_eq_add_neg]
    rw [hcoord]
    exact hy i
  · intro hy i
    have hcoord :
        (y - z) i - (center - z) i = y i - center i := by
      simp [sub_eq_add_neg]
    rw [← hcoord]
    exact hy i

/-- The boundary patch `cu_m ∩ (x + cu_{m-1})` used in the boundary
Caccioppoli statement. -/
noncomputable def boundaryPatchSet {d : ℕ} (Q : TriadicCube d) (x : Vec d) :
    Set (Vec d) :=
  openCubeSet Q ∩ openCubeAtScale x (Q.scale - 1)

theorem boundaryPatchSet_eq_translateSet_origin {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) :
    boundaryPatchSet Q x =
      translateSet (triadicCubeShift Q)
        (boundaryPatchSet (originCube d Q.scale) (x - triadicCubeShift Q)) := by
  rw [boundaryPatchSet,
    openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    openCubeAtScale_eq_translateSet_sub (triadicCubeShift Q) x (Q.scale - 1),
    ← translateSet_inter, boundaryPatchSet]
  simp [originCube]

/-- The smaller local energy patch `cu_m ∩ (x + cu_{m-2})`. -/
noncomputable def caccioppoliCoreSet {d : ℕ} (Q : TriadicCube d) (x : Vec d) :
    Set (Vec d) :=
  openCubeSet Q ∩ openCubeAtScale x (Q.scale - 2)

theorem measurableSet_caccioppoliCoreSet {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) :
    MeasurableSet (caccioppoliCoreSet Q x) := by
  exact
    (measurableSet_openCubeSet Q).inter
      (measurableSet_openCubeAtScale x (Q.scale - 2))

theorem caccioppoliCoreSet_eq_translateSet_origin {d : ℕ}
    (Q : TriadicCube d) (x : Vec d) :
    caccioppoliCoreSet Q x =
      translateSet (triadicCubeShift Q)
        (caccioppoliCoreSet (originCube d Q.scale) (x - triadicCubeShift Q)) := by
  rw [caccioppoliCoreSet,
    openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    openCubeAtScale_eq_translateSet_sub (triadicCubeShift Q) x (Q.scale - 2),
    ← translateSet_inter, caccioppoliCoreSet]
  simp [originCube]

/-- Normalized integral over an arbitrary measurable set, written as a total
quantity so theorem statements do not need side hypotheses merely to parse. -/
noncomputable abbrev normalizedSetAverage {d : ℕ} (V : Set (Vec d))
    (f : Vec d → ℝ) : ℝ :=
  Homogenization.volumeAverage V f

/-- Normalized `L²` square over a set. -/
noncomputable def normalizedL2SqOnSet {d : ℕ} (V : Set (Vec d))
    (u : Vec d → ℝ) : ℝ :=
  normalizedSetAverage V fun x => u x ^ 2

/-- Localized coefficient energy for an `H¹` function, using the symmetric part
of the public coefficient representative. -/
noncomputable def localizedCoeffEnergyValue {d : ℕ} {U : Ch02.Domain d}
    (V : Set (Vec d)) (a : Ch02.CoeffOn U) (u : H1Function (U : Set (Vec d))) :
    ℝ :=
  normalizedSetAverage V fun x =>
    vecDot (u.grad x) (matVecMul (symmPart (a.toCoeffField x)) (u.grad x))

/-- The global coefficient-energy norm of a Chapter 2 solution on a cube. -/
noncomputable def solutionEnergyNorm {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (u : CubeSolution Q a) : ℝ :=
  Real.sqrt (Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q) u)

/-- Weak public formulation of `- div(a grad u) = div g` on a cube, in the
codebase's RHS sign convention. -/
def IsForcedEquation {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (g : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function (Ch02.cubeDomain Q : Set (Vec d)),
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume

/-- Forced cube solution for the public Chapter 3.2 estimates. -/
structure ForcedCubeSolution {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (g : Vec d → Vec d) where
  toH1 : H1Function (Ch02.cubeDomain Q : Set (Vec d))
  weakSolution : IsForcedEquation Q a toH1 g

/-- Zero-trace forced solution used by the auxiliary Dirichlet estimate. -/
structure ZeroTraceForcedCubeSolution {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (g : Vec d → Vec d) where
  toH10 : H10Function (Ch02.cubeDomain Q : Set (Vec d))
  weakSolution : IsForcedEquation Q a toH10.toH1Function g

/-- Boundary-patch forced solution for the RHS Caccioppoli estimate. -/
structure BoundaryForcedCaccioppoliDatum {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (x : Vec d) (g : Vec d → Vec d) where
  toH1 : H1Function (Ch02.cubeDomain Q : Set (Vec d))
  weakSolution : IsForcedEquation Q a toH1 g
  zeroTraceOnBoundaryPatch :
    Ch01.LocalizedZeroTraceFunctionOn
      (Ch02.cubeDomain Q : Set (Vec d))
      (openCubeAtScale x (Q.scale - 1))
      toH1.toFun

/-- Dirichlet forced solution with boundary datum `h`, formalizing
`v - h ∈ H¹₀(Q)`. -/
structure DirichletForcedCubeSolution {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (g : Vec d → Vec d) where
  toH1 : H1Function (Ch02.cubeDomain Q : Set (Vec d))
  boundaryData : H1Function (Ch02.cubeDomain Q : Set (Vec d))
  weakSolution : IsForcedEquation Q a toH1 g
  zeroTraceDifference :
    ∃ w : H10Function (Ch02.cubeDomain Q : Set (Vec d)),
      w.toH1Function.toFun =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
        fun x => toH1.toFun x - boundaryData.toFun x

/-- Mean-zero Neumann weak formulation for the public energy consequence. -/
def IsMeanZeroNeumannForcedEquation {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d)
    (w : H1MeanZeroFunction (Ch02.cubeDomain Q : Set (Vec d)))
    (g : Vec d → Vec d) : Prop :=
  ∀ φ : H1MeanZeroFunction (Ch02.cubeDomain Q : Set (Vec d)),
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x)
          (w.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume

/-- Mean-zero Neumann solution of the forced problem on a cube.

The forcing is centered, matching the variational Neumann statement in the
notes.  The sign follows the codebase's RHS convention. -/
structure NeumannForcedCubeSolution {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (g : Vec d → Vec d) where
  toH1MeanZero : H1MeanZeroFunction (Ch02.cubeDomain Q : Set (Vec d))
  weakSolution :
    IsMeanZeroNeumannForcedEquation Q a toH1MeanZero
      (fun x => g x - cubeAverageVec Q g)

/-- Coefficient-energy norm of an arbitrary public `H¹` function on a cube. -/
noncomputable def h1EnergyNormOnCube {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : ℝ :=
  Real.sqrt (localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) u)

/-- Energy norm of a forced cube solution. -/
noncomputable def forcedSolutionEnergyNorm {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) : ℝ :=
  h1EnergyNormOnCube Q a u.toH1

/-- Energy norm of a zero-trace forced solution. -/
noncomputable def zeroTraceForcedSolutionEnergyNorm {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) {g : Vec d → Vec d}
    (u : ZeroTraceForcedCubeSolution Q a g) : ℝ :=
  h1EnergyNormOnCube Q a u.toH10.toH1Function

/-- Energy norm of boundary-patch forced Caccioppoli data. -/
noncomputable def boundaryForcedCaccioppoliCoreEnergy {d : ℕ}
    {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d}
    {g : Vec d → Vec d} (u : BoundaryForcedCaccioppoliDatum Q a x g) :
    ℝ :=
  localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u.toH1

/-- Parent-cube `L²` size of boundary-patch forced Caccioppoli data. -/
noncomputable def boundaryForcedCaccioppoliParentL2Sq {d : ℕ}
    {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d}
    {g : Vec d → Vec d} (u : BoundaryForcedCaccioppoliDatum Q a x g) :
    ℝ :=
  normalizedL2SqOnSet (openCubeSet Q) u.toH1.toFun

/-- Energy norm of a Dirichlet forced solution. -/
noncomputable def dirichletForcedSolutionEnergyNorm {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) {g : Vec d → Vec d}
    (u : DirichletForcedCubeSolution Q a g) : ℝ :=
  h1EnergyNormOnCube Q a u.toH1

/-- Gradient of the boundary datum in a Dirichlet forced solution. -/
noncomputable def dirichletBoundaryGradientField {d : ℕ}
    {Q : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    (u : DirichletForcedCubeSolution Q a g) : Vec d → Vec d :=
  u.boundaryData.grad

/-- Energy norm of a mean-zero Neumann forced solution. -/
noncomputable def neumannForcedSolutionEnergyNorm {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) {g : Vec d → Vec d}
    (u : NeumannForcedCubeSolution Q a g) : ℝ :=
  h1EnergyNormOnCube Q a u.toH1MeanZero.toH1Function

/-- Gradient field of a cube solution. -/
noncomputable def solutionGradientField {d : ℕ} {Q : TriadicCube d}
    {a : CoeffFamily d} (u : CubeSolution Q a) : Vec d → Vec d :=
  u.toH1.grad

/-- Gradient field of a forced cube solution. -/
noncomputable def forcedSolutionGradientField {d : ℕ} {Q : TriadicCube d}
    {a : CoeffFamily d} {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) : Vec d → Vec d :=
  u.toH1.grad

/-- Flux field `a ∇u` of a cube solution. -/
noncomputable def solutionFluxField {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (u : CubeSolution Q a) : Vec d → Vec d :=
  fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.toH1.grad x)

/-- Flux field `a ∇u` of a forced cube solution. -/
noncomputable def forcedSolutionFluxField {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) : Vec d → Vec d :=
  fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.toH1.grad x)

/-- A constant symmetric uniformly elliptic comparison matrix. -/
structure ConstantCoeffMatrix (d : ℕ) where
  matrix : Mat d
  isSymm : matrix.IsSymm
  lam : ℝ
  Lam : ℝ
  lam_pos : 0 < lam
  lam_le_Lam : lam ≤ Lam
  elliptic : IsEllipticMatrix lam Lam matrix

/-- The factor `|a0|^{1/2}` in the flux-response estimate. -/
noncomputable def constantCoeffMatrixNormHalf {d : ℕ}
    (a0 : ConstantCoeffMatrix d) : ℝ :=
  Real.rpow (Ch02.matrixNorm a0.matrix) (1 / 2 : ℝ)

/-- The factor `|a0|` in the inhomogeneous flux-response estimate. -/
noncomputable def constantCoeffMatrixNorm {d : ℕ}
    (a0 : ConstantCoeffMatrix d) : ℝ :=
  Ch02.matrixNorm a0.matrix

/-- Flux defect `(a - a0)∇u` against a constant comparison matrix. -/
noncomputable def solutionFluxDefectField {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d) (u : CubeSolution Q a) :
    Vec d → Vec d :=
  fun x => matVecMul ((a.coeffOn Q).toCoeffField x - a0.matrix) (u.toH1.grad x)

/-- Flux defect `(a - a0)∇u` for a forced solution. -/
noncomputable def forcedSolutionFluxDefectField {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d) {g : Vec d → Vec d}
    (u : ForcedCubeSolution Q a g) : Vec d → Vec d :=
  fun x => matVecMul ((a.coeffOn Q).toCoeffField x - a0.matrix) (u.toH1.grad x)

/-- Constant-coefficient weak formulation of `- div(a0 grad u) = div g` on a
cube, in the codebase's RHS sign convention. -/
def IsConstantCoeffForcedEquation {d : ℕ} (Q : TriadicCube d)
    (a0 : ConstantCoeffMatrix d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (g : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function (Ch02.cubeDomain Q : Set (Vec d)),
    ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (matVecMul a0.matrix (u.grad x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in (Ch02.cubeDomain Q : Set (Vec d)),
        vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume

/-- Constant-coefficient part `a0(∇u - ∇v)` in the homogenization comparison. -/
noncomputable def homogenizationComparisonConstantGradientField {d : ℕ}
    {Q : TriadicCube d} (a0 : ConstantCoeffMatrix d)
    (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : Vec d → Vec d :=
  fun x => matVecMul a0.matrix (u.grad x - v.grad x)

/-- Flux difference `a∇u - a0∇v` in the homogenization comparison. -/
noncomputable def homogenizationComparisonFluxField {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d)
    (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : Vec d → Vec d :=
  fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x) -
    matVecMul a0.matrix (v.grad x)

/-- Local flux defect `(a - a0)G`, using the coefficient representative on the
cube where the norm is evaluated. -/
noncomputable def homogenizationComparisonFluxDefectFromGradient {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d)
    (G : Vec d → Vec d) : Vec d → Vec d :=
  fun x => matVecMul ((a.coeffOn Q).toCoeffField x - a0.matrix) (G x)

/-- Local flux defect `(a - a0)∇u` on a cube. -/
noncomputable def homogenizationComparisonFluxDefectField {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : Vec d → Vec d :=
  homogenizationComparisonFluxDefectFromGradient Q a a0 u.grad

/-- Data for the duality lemma: a pair satisfying
`div(a∇u - a0∇v) = 0` and `u - v ∈ H¹₀(Q)`. -/
structure HomogenizationComparisonDatum {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d) where
  u : H1Function (Ch02.cubeDomain Q : Set (Vec d))
  v : H1Function (Ch02.cubeDomain Q : Set (Vec d))
  fluxComparisonSolenoidal :
    IsSolenoidalOn (Ch02.cubeDomain Q : Set (Vec d))
      (homogenizationComparisonFluxField Q a a0 u v)
  zeroTraceDifference :
    ∃ w : H10Function (Ch02.cubeDomain Q : Set (Vec d)),
      w.toH1Function.toFun =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
        fun x => u.toFun x - v.toFun x

/-- Data for the general coarse-graining theorem: two solutions with the same
right-hand side and zero-trace difference. -/
structure CoarseGrainingComparisonDatum {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d) (g : Vec d → Vec d) where
  u : H1Function (Ch02.cubeDomain Q : Set (Vec d))
  v : H1Function (Ch02.cubeDomain Q : Set (Vec d))
  uWeakSolution : IsForcedEquation Q a u g
  vWeakSolution : IsConstantCoeffForcedEquation Q a0 v g
  zeroTraceDifference :
    ∃ w : H10Function (Ch02.cubeDomain Q : Set (Vec d)),
      w.toH1Function.toFun =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
        fun x => u.toFun x - v.toFun x

/-- Left-hand side in the Section 3.3 comparison estimates, using the
concrete/circ negative Besov seminorm from the deterministic splitting
arguments. -/
noncomputable def homogenizationComparisonNegativeBesovLHS {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d)
    (s : ℝ) (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : ℝ :=
  cubeBesovNegativeVectorSeminormTwo Q s
      (homogenizationComparisonConstantGradientField a0 u v) +
    cubeBesovNegativeVectorSeminormTwo Q s
      (homogenizationComparisonFluxField Q a a0 u v)

/-- Localized `ℓ²` average of the concrete/circ flux-defect negative Besov
seminorms over descendants at depth `j = m - n`. If the parent cube has scale
`m = Q.scale`, then the manuscript lower scale is `n = Q.scale - (j : ℤ)`,
which may be negative. -/
noncomputable def localizedHomogenizationFluxDefectAverage {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d)
    (s : ℝ) (j : ℕ)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : ℝ :=
  Real.sqrt <|
    descendantsAverage Q j fun R =>
      (cubeBesovNegativeVectorSeminormTwo R s
        (homogenizationComparisonFluxDefectFromGradient R a a0 u.grad)) ^ 2

/-- Public localized boundary data for the boundary Caccioppoli theorem.

The zero-trace condition is scalar and localized: every smooth cutoff supported
in the boundary window `x + cu_{m-1}` turns `u` into an admissible `H¹₀` test
function on the parent cube. This is the Lean form of the note's Sobolev trace
condition `u = 0` on `(∂cu_m) ∩ (x + cu_{m-1})`; it deliberately does not use a
gradient-only potential condition, since gradients cannot see constants. -/
structure BoundaryCaccioppoliDatum {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (x : Vec d) where
  toH1 : H1Function (Ch02.cubeDomain Q : Set (Vec d))
  isHarmonic :
    IsAHarmonicGradient (a.coeffOn Q).toCoeffField
      (Ch02.cubeDomain Q : Set (Vec d)) toH1.grad
  zeroTraceOnBoundaryPatch :
    Ch01.LocalizedZeroTraceFunctionOn
      (Ch02.cubeDomain Q : Set (Vec d))
      (openCubeAtScale x (Q.scale - 1))
      toH1.toFun

/-- Localized energy of boundary Caccioppoli data on the core patch. -/
noncomputable def boundaryCaccioppoliCoreEnergy {d : ℕ} {Q : TriadicCube d}
    {a : CoeffFamily d} {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x) : ℝ :=
  localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u.toH1

/-- Parent-cube `L²` size for boundary Caccioppoli data. -/
noncomputable def boundaryCaccioppoliParentL2Sq {d : ℕ} {Q : TriadicCube d}
    {a : CoeffFamily d} {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x) : ℝ :=
  normalizedL2SqOnSet (openCubeSet Q) u.toH1.toFun

/-- Localized energy of an interior solution on the core patch. -/
noncomputable def interiorCaccioppoliCoreEnergy {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (x : Vec d) (u : CubeSolution Q a) : ℝ :=
  localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u.toH1

/-- Parent-cube oscillation `L²` square for the interior Caccioppoli estimate. -/
noncomputable def interiorCaccioppoliParentOscillationL2Sq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffFamily d) (u : CubeSolution Q a) : ℝ :=
  normalizedL2SqOnSet (openCubeSet Q) fun x =>
    u.toH1.toFun x - Ch01.Legacy.normalizedAverage Q u.toH1.toFun

/-- The Caccioppoli prefactor in
`e.coarse.grained.Caccioppoli.*.deterministic.theory`, excluding the final
`L²` square. -/
noncomputable def caccioppoliPrefactor {d : ℕ} (C : ℝ) (Q : TriadicCube d)
    (a : CoeffFamily d) (s t : ℝ) : ℝ :=
  Real.rpow (C / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
    Real.rpow s (-(2 * s / (1 - s - t))) *
    Real.rpow (Ch02.ThetaRatio Q s t a) (s / (1 - s - t)) *
    Ch02.LambdaS Q s a *
    Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ)))

/-- Boundary Caccioppoli right-hand side. -/
noncomputable def boundaryCaccioppoliRHS {d : ℕ} (C : ℝ)
    {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d}
    (s t : ℝ) (u : BoundaryCaccioppoliDatum Q a x) : ℝ :=
  caccioppoliPrefactor C Q a s t * boundaryCaccioppoliParentL2Sq u

/-- Interior Caccioppoli right-hand side. -/
noncomputable def interiorCaccioppoliRHS {d : ℕ} (C : ℝ)
    (Q : TriadicCube d) (a : CoeffFamily d) (s t : ℝ) (u : CubeSolution Q a) :
    ℝ :=
  caccioppoliPrefactor C Q a s t *
    interiorCaccioppoliParentOscillationL2Sq Q a u

/-- The factor `c_{s,q}^{-1/q}`, with value `1` at `q = infinity`. -/
noncomputable def poincareDiscountFactor (s : ℝ)
    (q : Ch02.MultiscaleExponent) : ℝ :=
  match q with
  | .finite q => Real.rpow (Ch02.geometricDiscount s q) (-(1 / q))
  | .infinity => 1

/-- The lower-ellipticity factor `\lambda_{s,q}^{-1/2}`. -/
noncomputable def poincareLowerEllipticityFactor {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (s : ℝ) (q : Ch02.MultiscaleExponent) : ℝ :=
  Real.rpow (Ch02.lambdaSq Q s q a) (-(1 / 2 : ℝ))

/-- The upper-ellipticity factor `\Lambda_{s,q}^{1/2}`. -/
noncomputable def poincareUpperEllipticityFactor {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (s : ℝ) (q : Ch02.MultiscaleExponent) : ℝ :=
  Real.rpow (Ch02.LambdaSq Q s q a) (1 / 2 : ℝ)

/-- Right-hand side in the gradient coarse Poincare estimate. -/
noncomputable def coarsePoincareGradientRHS {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (u : CubeSolution Q a) : ℝ :=
  poincareDiscountFactor s q *
    poincareLowerEllipticityFactor Q a s q *
      solutionEnergyNorm Q a u

/-- Right-hand side in the flux coarse Poincare estimate. -/
noncomputable def coarsePoincareFluxRHS {d : ℕ} (Q : TriadicCube d)
    (a : CoeffFamily d) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (u : CubeSolution Q a) : ℝ :=
  poincareDiscountFactor s q *
    poincareUpperEllipticityFactor Q a s q *
      solutionEnergyNorm Q a u

/-- Right-hand side in the coarse flux-response estimate. -/
noncomputable def coarseFluxResponseRHS {d : ℕ} [NeZero d] (C : ℝ)
    (Q : TriadicCube d) (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d)
    (s : ℝ) (u : CubeSolution Q a) : ℝ :=
  C * s⁻¹ * constantCoeffMatrixNormHalf a0 *
    solutionEnergyNorm Q a u *
      Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0.matrix

/-- Right-hand side in the coarse Poincare estimate with forcing. -/
noncomputable def coarsePoincareWithRHSGradientRHS {d : ℕ}
    (C : ℝ) (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) (g : Vec d → Vec d) (u : ForcedCubeSolution Q a g) : ℝ :=
  C * Real.rpow s (-(3 / 2 : ℝ)) *
      poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
      forcedSolutionEnergyNorm Q a u +
    C * Real.rpow s (-3 : ℝ) *
      Real.rpow (Ch02.lambdaSq Q (s / 2) (.finite 2) a) (-1 : ℝ) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q s g

/-- Right-hand side in the auxiliary zero-Dirichlet energy estimate. -/
noncomputable def zeroDirichletEnergyWithRHSRHS {d : ℕ}
    (C : ℝ) (Q : TriadicCube d) (a : CoeffFamily d)
    (t : ℝ) (g : Vec d → Vec d) : ℝ :=
  C * Real.rpow t (-(3 / 2 : ℝ)) *
    poincareLowerEllipticityFactor Q a t (.finite 2) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g

/-- Common prefactor in the boundary Caccioppoli estimate with forcing. -/
noncomputable def caccioppoliWithRHSPrefactor {d : ℕ} (C : ℝ)
    (Q : TriadicCube d) (a : CoeffFamily d) (s t : ℝ) : ℝ :=
  Real.rpow (C / (1 - s - t)) (2 + 4 * s / (1 - s - t)) *
    Real.rpow s (-(2 * s / (1 - s - t))) *
    Real.rpow (Ch02.ThetaRatio Q s t a) ((1 - t) / (1 - s - t))

/-- Boundary Caccioppoli right-hand side with forcing. -/
noncomputable def boundaryCaccioppoliWithRHSRHS {d : ℕ} (C : ℝ)
    {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d}
    {g : Vec d → Vec d} (s t : ℝ)
    (u : BoundaryForcedCaccioppoliDatum Q a x g) : ℝ :=
  caccioppoliWithRHSPrefactor C Q a s t *
    (Ch02.lambdaS Q t a *
        Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
        boundaryForcedCaccioppoliParentL2Sq u +
      (Real.rpow t (-8 : ℝ) / (1 - 2 * t)) *
        Real.rpow (Ch02.lambdaS Q t a) (-1 : ℝ) *
        (scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ 2)

/-- Right-hand side in the weak flux estimate with forcing. -/
noncomputable def weakFluxWithRHSRHS {d : ℕ}
    (C : ℝ) (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) (g : Vec d → Vec d) (u : ForcedCubeSolution Q a g) : ℝ :=
  C * s⁻¹ *
      poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) *
      forcedSolutionEnergyNorm Q a u +
    C * Real.rpow s (-(5 / 2 : ℝ)) *
      poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) *
      poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q s g

/-- Right-hand side in the coarse flux-response estimate with forcing. -/
noncomputable def coarseFluxResponseWithRHSRHS {d : ℕ} [NeZero d]
    (C : ℝ) (Q : TriadicCube d) (a : CoeffFamily d)
    (a0 : ConstantCoeffMatrix d) (s : ℝ) (g : Vec d → Vec d)
    (u : ForcedCubeSolution Q a g) : ℝ :=
  C * s⁻¹ * constantCoeffMatrixNormHalf a0 *
      forcedSolutionEnergyNorm Q a u *
      Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0.matrix +
    C *
      (Real.rpow s (-(5 / 2 : ℝ)) * constantCoeffMatrixNormHalf a0 *
          poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
          Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0.matrix +
        Real.rpow s (-(5 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a (s / 2) (.finite 2) *
          poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) +
        Real.rpow s (-3 : ℝ) * constantCoeffMatrixNorm a0 *
          Real.rpow (Ch02.lambdaSq Q (s / 2) (.finite 2) a) (-1 : ℝ)) *
        scaleNormalizedPositiveBesovVectorSeminormTwo Q s g

/-- Right-hand side in the Dirichlet energy estimate with forcing and boundary
data. -/
noncomputable def dirichletEnergyWithRHSRHS {d : ℕ}
    (C : ℝ) (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) (g : Vec d → Vec d)
    (u : DirichletForcedCubeSolution Q a g) : ℝ :=
  C * Real.rpow s (-(3 / 2 : ℝ)) *
      poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q s g +
    C * Real.rpow s (-(1 / 2 : ℝ)) *
      poincareUpperEllipticityFactor Q a s (.finite 2) *
      scaleNormalizedPositiveBesovVectorNormTwo Q s
        (dirichletBoundaryGradientField u)

/-- Right-hand side in the mean-zero Neumann energy estimate with forcing. -/
noncomputable def neumannEnergyWithRHSRHS {d : ℕ}
    (C : ℝ) (Q : TriadicCube d) (a : CoeffFamily d)
    (s : ℝ) (g : Vec d → Vec d) : ℝ :=
  C * Real.rpow s (-(3 / 2 : ℝ)) *
    poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q s g

/-- Truncated homogenization error
`\mathcal E_{s,\infty,1}(Q,n; a, a0)`, encoded by descendant depth
`j = m - n`.  Equivalently, the manuscript scale is
`n = Q.scale - (j : ℤ)`, so negative `n` are represented by sufficiently large
natural depths `j`.

This is the Ch3.3 localized envelope: the supremum of the Ch2 one-cube
homogenization error over the depth-`j` descendants of the parent cube. -/
noncomputable def coarseGrainingHomogenizationErrorAtDepth {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d)
    (s : ℝ) (j : ℕ) : ℝ :=
  Ch02.finsetSupReal (descendantsAtDepth Q j) fun R =>
    Ch02.HomogenizationErrorOnCube R s .infinity (.finite 1) a a0.matrix

/-- Right-hand side in the duality estimate from local flux defect to global
comparison. -/
noncomputable def dualityFromFluxDefectRHS {d : ℕ} (C : ℝ)
    (Q : TriadicCube d) (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d)
    (s : ℝ) (j : ℕ)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : ℝ :=
  C * s⁻¹ * localizedHomogenizationFluxDefectAverage Q a a0 s j u

/-- Note-facing two-exponent replacement RHS for the duality estimate.

The comparison field is measured at exponent `s`, while the localized
flux-defect average is measured at the independent lower exponent `t`.
The scalar prefactor is the displayed manuscript loss
`s^{-1} t^{-2} (1/2 - t)^{-1}`. -/
noncomputable def dualityFromFluxDefectExponentLossRHS {d : ℕ} (C : ℝ)
    (Q : TriadicCube d) (a : CoeffFamily d) (a0 : ConstantCoeffMatrix d)
    (s t : ℝ) (j : ℕ)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : ℝ :=
  C * s⁻¹ * (t⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - t)⁻¹ *
    localizedHomogenizationFluxDefectAverage Q a a0 t j u

/-- The depth factor `3^{s(m-n)/2}` in the Section 3.3 coarse-graining bound. -/
noncomputable def coarseGrainingDepthHalfWeight (s : ℝ) (j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ))

/-- The depth factor `3^{s(m-n)}` in the Section 3.3 coarse-graining bound. -/
noncomputable def coarseGrainingDepthWeight (s : ℝ) (j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (s * (j : ℝ))

/-- The inverse depth factor `3^{-s(m-n)}` used by scale-separated forcing. -/
noncomputable def coarseGrainingDepthInvWeight (s : ℝ) (j : ℕ) : ℝ :=
  (coarseGrainingDepthWeight s j)⁻¹

/-- Scale-separated local flux-defect RHS in the repaired general
coarse-graining estimate.  The flux-response quantities are measured at
exponent `r`, while the force is measured at the stronger exponent `r₂`. -/
noncomputable def generalCoarseGrainingL2TwoExponentFluxDefectRHS {d : ℕ}
    [NeZero d]
    (C : ℝ) (Q : TriadicCube d) (a : CoeffFamily d)
    (a0 : ConstantCoeffMatrix d) (r r₂ : ℝ) (j : ℕ)
    (g : Vec d → Vec d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : ℝ :=
  C *
    (r⁻¹ * constantCoeffMatrixNormHalf a0 *
        coarseGrainingHomogenizationErrorAtDepth Q a a0 r j *
        h1EnergyNormOnCube Q a u +
      (Real.rpow r (-(5 / 2 : ℝ)) * constantCoeffMatrixNormHalf a0 *
            coarseGrainingDepthHalfWeight r j *
            poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) *
            coarseGrainingHomogenizationErrorAtDepth Q a a0 r j +
          Real.rpow r (-(5 / 2 : ℝ)) *
            coarseGrainingDepthWeight r j *
            poincareUpperEllipticityFactor Q a (r / 2) (.finite 2) *
            poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) +
          Real.rpow r (-3 : ℝ) *
            coarseGrainingDepthWeight r j *
            constantCoeffMatrixNorm a0 *
            Real.rpow (Ch02.lambdaSq Q (r / 2) (.finite 2) a) (-1 : ℝ)) *
        (coarseGrainingDepthInvWeight r₂ j *
          scaleNormalizedPositiveBesovVectorSeminormTwo Q r₂ g))

/-- Note-facing RHS with an independent stronger force exponent `r₂`.  The
comparison is measured at exponent `s`, the flux response at `r`, and the
forcing at `r₂`. -/
noncomputable def generalCoarseGrainingL2TwoExponentRHS {d : ℕ} [NeZero d]
    (C : ℝ) (Q : TriadicCube d) (a : CoeffFamily d)
    (a0 : ConstantCoeffMatrix d) (s r r₂ : ℝ) (j : ℕ)
    (g : Vec d → Vec d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : ℝ :=
  s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
    generalCoarseGrainingL2TwoExponentFluxDefectRHS C Q a a0 r r₂ j g u

end

end Ch03
end Book
end Homogenization
