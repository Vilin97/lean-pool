/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GlobalLocalization
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GlobalParentGeometry
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalWeakRestriction

/-! # Reflected Local Inputs -/

namespace Homogenization

open MeasureTheory Set

noncomputable section

namespace CubeCalderonZygmund

/-!
# Local one-ball data from a reflected parent solution

The global good-`lambda` argument extends the reflected parent solution and
datum by zero.  On each comparison parent that remains inside that reflected
cube, this module supplies precisely the local inputs of
`sqWeightedMeasure_oneStoppingBall_le`: global `L²` membership, the restricted
solution, the almost-everywhere gradient identification, and the weak equation
with the *zero-extended* datum.  Thus the local PDE is derived from the single
parent equation and is never an additional hypothesis.
-/

/-- The zero extension of the gradient of a reflected parent solution. -/
def reflectedParentGradientExtension {d : ℕ} (m : ℤ)
    (uP : H1Function (openCubeSet (originCube d (m + 1)))) :
    Vec d → HilbertVec d :=
  (openCubeSet (originCube d (m + 1))).indicator (hilbertifyVecField uP.grad)

/-- The zero extension of a reflected parent vector datum. -/
def reflectedParentDatumExtension {d : ℕ} (m : ℤ)
    (HP : Vec d → Vec d) : Vec d → Vec d :=
  (openCubeSet (originCube d (m + 1))).indicator HP

/-- The local solution on the comparison parent cut out of a reflected
parent solution. -/
def reflectedParentLocalSolution {d : ℕ} {depth : ℕ} (m : ℤ)
    (x : Vec d) (r : ℝ)
    (uP : H1Function (openCubeSet (originCube d (m + 1))))
    (hsub : axisCube (stoppingComparisonParentCorner x r depth)
      (stoppingComparisonParentSide r depth) ⊆ openCubeSet (originCube d (m + 1))) :
    H1Function (axisCube (stoppingComparisonParentCorner x r depth)
      (stoppingComparisonParentSide r depth)) :=
  uP.restrict
    (isOpen_axisCube (stoppingComparisonParentCorner x r depth)
      (stoppingComparisonParentSide r depth)) hsub

/-- Hilbertification commutes with extension by zero. -/
theorem hilbertifyVecField_reflectedParentDatumExtension
    {d : ℕ} (m : ℤ) (HP : Vec d → Vec d) :
    hilbertifyVecField (reflectedParentDatumExtension m HP) =
      (openCubeSet (originCube d (m + 1))).indicator (hilbertifyVecField HP) := by
  funext y
  by_cases hy : y ∈ openCubeSet (originCube d (m + 1))
  · apply HilbertVec.ext
    intro i
    simp [hilbertifyVecField, reflectedParentDatumExtension, hy]
  · apply HilbertVec.ext
    intro i
    simp [hilbertifyVecField, reflectedParentDatumExtension, hy]

/-- A fixed reflected parent solution and datum provide the local inputs for
one stopping ball.  The parent equation retains its exact coefficient and
minus sign; the final equation is its restriction to the comparison parent.
-/
theorem reflectedParent_oneStoppingBall_inputs
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
    MemLp (reflectedParentGradientExtension m uP) 2 volume ∧
      MemLp (hilbertifyVecField (reflectedParentDatumExtension m HP)) 2 volume ∧
      (reflectedParentGradientExtension m uP =ᵐ[volume.restrict
        (axisCube (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth))]
        hilbertifyVecField
          (reflectedParentLocalSolution (depth := depth) m x r uP
            (stoppingComparisonParent_axisCube_subset_openCubeSet_originCube_succ
              depth hx hr hcutoff)).grad) ∧
      ∀ phi : Vec d → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
        tsupport phi ⊆ axisCube (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth) →
        sigma0 * ∫ y in axisCube (stoppingComparisonParentCorner x r depth)
            (stoppingComparisonParentSide r depth),
          vecDot
            ((reflectedParentLocalSolution (depth := depth) m x r uP
              (stoppingComparisonParent_axisCube_subset_openCubeSet_originCube_succ
                depth hx hr hcutoff)).grad y)
            (euclideanGradient phi y) ∂volume =
          -∫ y in axisCube (stoppingComparisonParentCorner x r depth)
            (stoppingComparisonParentSide r depth),
            vecDot (reflectedParentDatumExtension m HP y)
              (euclideanGradient phi y) ∂volume := by
  let P : Set (Vec d) := openCubeSet (originCube d (m + 1))
  let B : Set (Vec d) := axisCube (stoppingComparisonParentCorner x r depth)
    (stoppingComparisonParentSide r depth)
  have hBP : B ⊆ P := by
    simpa only [B, P] using
      stoppingComparisonParent_axisCube_subset_openCubeSet_originCube_succ
        depth hx hr hcutoff
  have hPmeas : MeasurableSet P := by
    simpa only [P] using measurableSet_openCubeSet (originCube d (m + 1))
  have hBmeas : MeasurableSet B := by
    exact (isOpen_axisCube _ _).measurableSet
  constructor
  · rw [show reflectedParentGradientExtension m uP =
        P.indicator (hilbertifyVecField uP.grad) by rfl,
      memLp_indicator_iff_restrict hPmeas]
    exact memHilbertVectorL2_hilbertifyVecField uP.grad_memVectorL2
  constructor
  · rw [hilbertifyVecField_reflectedParentDatumExtension]
    change MemLp (P.indicator (hilbertifyVecField HP)) 2 volume
    rw [memLp_indicator_iff_restrict hPmeas]
    exact memHilbertVectorL2_hilbertifyVecField hHP
  constructor
  · have hident := indicator_aeEq_of_subset
      (μ := volume) (f := hilbertifyVecField uP.grad) hBmeas hBP
    simpa only [reflectedParentGradientExtension, reflectedParentLocalSolution,
      B, P, H1Function.restrict] using hident
  intro phi hphi hphi_compact hphi_sub
  have hlocal := weakDivergence_restrict_axisCube
    (U := P) (stoppingComparisonParentCorner x r depth)
    (stoppingComparisonParentSide r depth) hBP uP HP (by
      simpa only [P] using hweak)
    phi hphi hphi_compact (by simpa only [B] using hphi_sub)
  have hdatum :
      ∫ y in B, vecDot (reflectedParentDatumExtension m HP y)
          (euclideanGradient phi y) ∂volume =
        ∫ y in B, vecDot (HP y) (euclideanGradient phi y) ∂volume := by
    apply MeasureTheory.setIntegral_congr_fun hBmeas
    intro y hy
    simp only [reflectedParentDatumExtension]
    rw [Set.indicator_of_mem (hBP hy)]
  change sigma0 * ∫ y in B,
      vecDot ((uP.restrict (isOpen_axisCube _ _) hBP).grad y)
        (euclideanGradient phi y) ∂volume =
      -∫ y in B, vecDot (reflectedParentDatumExtension m HP y)
        (euclideanGradient phi y) ∂volume
  rw [hdatum]
  simpa only [B, H1Function.restrict] using hlocal

end CubeCalderonZygmund

end

end Homogenization
