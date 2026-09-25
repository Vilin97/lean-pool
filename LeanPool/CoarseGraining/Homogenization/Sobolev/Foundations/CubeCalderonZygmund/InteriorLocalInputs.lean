/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GlobalLocalization
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GlobalParentGeometry
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalWeakRestriction

/-! # Interior Local Inputs -/

@[expose] public section

namespace Homogenization

open MeasureTheory Set

noncomputable section

namespace CubeCalderonZygmund

/-!
# Local one-ball data from an interior parent solution

The interior good-`lambda` argument extends a solution gradient and its datum
by zero from the next centered parent cube.  On every stopping comparison
parent, this module supplies the inputs of
`sqWeightedMeasure_oneStoppingBall_le`: global `L²` membership, a restricted
solution, almost-everywhere gradient identification, and the restricted weak
divergence equation with the zero-extended datum.

The construction starts from an arbitrary `H¹` solution on the parent cube.
It uses neither a zero-trace premise nor a reflection factor.

The generic API works over any open parent set containing the comparison axis
cube.  The centered-cube API below is its geometry-specific specialization.
-/

/-- The zero extension of a solution gradient from an arbitrary parent set. -/
def openParentGradientExtension {d : ℕ} (U : Set (Vec d))
    (uU : H1Function U) : Vec d → HilbertVec d :=
  U.indicator (hilbertifyVecField uU.grad)

/-- The zero extension of a vector datum from an arbitrary parent set. -/
def openParentDatumExtension {d : ℕ} (U : Set (Vec d))
    (HU : Vec d → Vec d) : Vec d → Vec d :=
  U.indicator HU

/-- Restrict a parent solution to an axis cube contained in its domain. -/
def openParentLocalSolution {d : ℕ} (U : Set (Vec d))
    (z : Vec d) (L : ℝ) (uU : H1Function U)
    (hBU : axisCube z L ⊆ U) : H1Function (axisCube z L) :=
  uU.restrict (isOpen_axisCube z L) hBU

/-- Hilbertification commutes with extension by zero from an arbitrary set. -/
theorem hilbertifyVecField_openParentDatumExtension
    {d : ℕ} (U : Set (Vec d)) (HU : Vec d → Vec d) :
    hilbertifyVecField (openParentDatumExtension U HU) =
      U.indicator (hilbertifyVecField HU) := by
  funext y
  by_cases hy : y ∈ U
  · apply HilbertVec.ext
    intro i
    simp [hilbertifyVecField, openParentDatumExtension, hy]
  · apply HilbertVec.ext
    intro i
    simp [hilbertifyVecField, openParentDatumExtension, hy]

/-- An `H¹` solution on an arbitrary open parent set supplies all local inputs
for an axis-cube comparison contained in that parent. -/
theorem openParent_axisCube_inputs
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {z : Vec d} {L sigma0 : ℝ}
    (hBU : axisCube z L ⊆ U)
    (uU : H1Function U) (HU : Vec d → Vec d)
    (hHU : MemVectorL2 U HU)
    (hweak : ∀ phi : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
      tsupport phi ⊆ U →
      sigma0 * ∫ y in U,
        vecDot (uU.grad y) (euclideanGradient phi y) ∂volume =
          -∫ y in U, vecDot (HU y) (euclideanGradient phi y) ∂volume) :
    MemLp (openParentGradientExtension U uU) 2 volume ∧
      MemLp (hilbertifyVecField (openParentDatumExtension U HU)) 2 volume ∧
      (openParentGradientExtension U uU =ᵐ[volume.restrict (axisCube z L)]
        hilbertifyVecField (openParentLocalSolution U z L uU hBU).grad) ∧
      ∀ phi : Vec d → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
        tsupport phi ⊆ axisCube z L →
        sigma0 * ∫ y in axisCube z L,
          vecDot ((openParentLocalSolution U z L uU hBU).grad y)
            (euclideanGradient phi y) ∂volume =
          -∫ y in axisCube z L,
            vecDot (openParentDatumExtension U HU y)
              (euclideanGradient phi y) ∂volume := by
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hBmeas : MeasurableSet (axisCube z L) :=
    (isOpen_axisCube z L).measurableSet
  constructor
  · rw [show openParentGradientExtension U uU =
        U.indicator (hilbertifyVecField uU.grad) by rfl,
      memLp_indicator_iff_restrict hUmeas]
    exact memHilbertVectorL2_hilbertifyVecField uU.grad_memVectorL2
  constructor
  · rw [hilbertifyVecField_openParentDatumExtension,
      memLp_indicator_iff_restrict hUmeas]
    exact memHilbertVectorL2_hilbertifyVecField hHU
  constructor
  · have hident := indicator_aeEq_of_subset
      (μ := volume) (f := hilbertifyVecField uU.grad) hBmeas hBU
    simpa only [openParentGradientExtension, openParentLocalSolution,
      H1Function.restrict] using hident
  intro phi hphi hphi_compact hphi_sub
  have hlocal := weakDivergence_restrict_axisCube z L hBU uU HU hweak
    phi hphi hphi_compact hphi_sub
  have hdatum :
      ∫ y in axisCube z L, vecDot (openParentDatumExtension U HU y)
          (euclideanGradient phi y) ∂volume =
        ∫ y in axisCube z L,
          vecDot (HU y) (euclideanGradient phi y) ∂volume := by
    apply MeasureTheory.setIntegral_congr_fun hBmeas
    intro y hy
    simp only [openParentDatumExtension]
    rw [Set.indicator_of_mem (hBU hy)]
  change sigma0 * ∫ y in axisCube z L,
      vecDot ((uU.restrict (isOpen_axisCube z L) hBU).grad y)
        (euclideanGradient phi y) ∂volume =
      -∫ y in axisCube z L, vecDot (openParentDatumExtension U HU y)
        (euclideanGradient phi y) ∂volume
  rw [hdatum]
  simpa only [H1Function.restrict] using hlocal

/-- The zero extension of an interior parent solution's gradient. -/
def interiorParentGradientExtension {d : ℕ} (m : ℤ)
    (uP : H1Function (openCubeSet (originCube d (m + 1)))) :
    Vec d → HilbertVec d :=
  openParentGradientExtension (openCubeSet (originCube d (m + 1))) uP

/-- The zero extension of an interior parent vector datum. -/
def interiorParentDatumExtension {d : ℕ} (m : ℤ)
    (HP : Vec d → Vec d) : Vec d → Vec d :=
  openParentDatumExtension (openCubeSet (originCube d (m + 1))) HP

/-- The restriction of an interior parent solution to a stopping comparison
parent. -/
def interiorParentLocalSolution {d : ℕ} {depth : ℕ} (m : ℤ)
    (x : Vec d) (r : ℝ)
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (hsub : axisCube (stoppingComparisonParentCorner x r depth)
      (stoppingComparisonParentSide r depth) ⊆ openCubeSet (originCube d (m + 1))) :
    H1Function (axisCube (stoppingComparisonParentCorner x r depth)
      (stoppingComparisonParentSide r depth)) :=
  openParentLocalSolution (openCubeSet (originCube d (m + 1)))
    (stoppingComparisonParentCorner x r depth)
    (stoppingComparisonParentSide r depth) uP hsub

/-- Hilbertification commutes with the interior datum's extension by zero. -/
theorem hilbertifyVecField_interiorParentDatumExtension
    {d : ℕ} (m : ℤ) (HP : Vec d → Vec d) :
    hilbertifyVecField (interiorParentDatumExtension m HP) =
      (openCubeSet (originCube d (m + 1))).indicator (hilbertifyVecField HP) := by
  exact hilbertifyVecField_openParentDatumExtension
    (openCubeSet (originCube d (m + 1))) HP

/-- One interior parent solution and datum supply all local inputs for a
stopping-ball comparison.  The local equation is derived by restriction from
the parent equation, with its coefficient and minus sign unchanged. -/
theorem interiorParent_oneStoppingBall_inputs
    {d : ℕ} [NeZero d] {depth : ℕ} {m : ℤ} {sigma0 : ℝ}
    {x : Vec d} {r : ℝ}
    (hx : x ∈ openCubeSet (originCube d m))
    (hr : 0 < r)
    (hcutoff : r ≤ cubeRadius (originCube d m) / (10 * (3 : ℝ) ^ depth))
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (HP : Vec d → Vec d)
    (hHP : MemVectorL2 (openCubeSet (originCube d (m + 1))) HP)
    (hweak : ∀ phi : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
      tsupport phi ⊆ openCubeSet (originCube d (m + 1)) →
      sigma0 * ∫ y in openCubeSet (originCube d (m + 1)),
        vecDot (uP.grad y) (euclideanGradient phi y) ∂volume =
          -∫ y in openCubeSet (originCube d (m + 1)),
            vecDot (HP y) (euclideanGradient phi y) ∂volume) :
    MemLp (interiorParentGradientExtension m uP) 2 volume ∧
      MemLp (hilbertifyVecField (interiorParentDatumExtension m HP)) 2 volume ∧
      (interiorParentGradientExtension m uP =ᵐ[volume.restrict
        (axisCube (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth))]
        hilbertifyVecField
          (interiorParentLocalSolution (depth := depth) m x r uP
            (stoppingComparisonParent_axisCube_subset_openCubeSet_originCube_succ
              depth hx hr hcutoff)).grad) ∧
      ∀ phi : Vec d → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
        tsupport phi ⊆ axisCube (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth) →
        sigma0 * ∫ y in axisCube (stoppingComparisonParentCorner x r depth)
            (stoppingComparisonParentSide r depth),
          vecDot
            ((interiorParentLocalSolution (depth := depth) m x r uP
              (stoppingComparisonParent_axisCube_subset_openCubeSet_originCube_succ
                depth hx hr hcutoff)).grad y)
            (euclideanGradient phi y) ∂volume =
          -∫ y in axisCube (stoppingComparisonParentCorner x r depth)
            (stoppingComparisonParentSide r depth),
            vecDot (interiorParentDatumExtension m HP y)
              (euclideanGradient phi y) ∂volume := by
  simpa only [interiorParentGradientExtension, interiorParentDatumExtension,
    interiorParentLocalSolution] using
    openParent_axisCube_inputs
      (U := openCubeSet (originCube d (m + 1)))
      (z := stoppingComparisonParentCorner x r depth)
      (L := stoppingComparisonParentSide r depth)
      (sigma0 := sigma0) (isOpen_openCubeSet (originCube d (m + 1)))
      (stoppingComparisonParent_axisCube_subset_openCubeSet_originCube_succ
        depth hx hr hcutoff) uP HP hHP hweak

end CubeCalderonZygmund

end

end Homogenization
