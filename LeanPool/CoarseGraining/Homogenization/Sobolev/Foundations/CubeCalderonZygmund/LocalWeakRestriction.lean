/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.AxisCube
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.EuclideanL2CZ

/-! # Local Weak Restriction -/

namespace Homogenization

open MeasureTheory Set

noncomputable section

namespace CubeCalderonZygmund

/-!
# Restricting weak divergence equations to an interior axis cube

The weak equation is originally posed on an ambient open set.  A test whose
topological support lies in an axis subcube has zero Euclidean gradient off
that subcube, so both flux pairings have exactly the same set integral on the
subcube and on the ambient set.  This is the support argument needed to pass a
parent-cube equation to the comparison cube; it does not assume a second,
local PDE.
-/

/-- Restrict a scalar weak divergence equation to an interior open axis cube.

The restricted function has definitionally the same gradient.  The conclusion
keeps the coefficient and sign of the parent equation verbatim; its only new
input is geometric containment of the subcube in the ambient domain. -/
theorem weakDivergence_restrict_axisCube
    {d : ℕ} {U : Set (Vec d)} (z : Vec d) (L : ℝ)
    (hBU : axisCube z L ⊆ U) {sigma0 : ℝ}
    (u : H1Function U) (H : Vec d → Vec d)
    (hweak : ∀ phi : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi → tsupport phi ⊆ U →
      sigma0 * ∫ y in U, vecDot (u.grad y) (euclideanGradient phi y) ∂volume =
        -∫ y in U, vecDot (H y) (euclideanGradient phi y) ∂volume) :
    ∀ phi : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
      tsupport phi ⊆ axisCube z L →
      sigma0 * ∫ y in axisCube z L,
        vecDot ((u.restrict (isOpen_axisCube z L) hBU).grad y)
          (euclideanGradient phi y) ∂volume =
        -∫ y in axisCube z L,
          vecDot (H y) (euclideanGradient phi y) ∂volume := by
  intro phi hphi hphi_compact hphi_sub
  have hphi_subU : tsupport phi ⊆ U := hphi_sub.trans hBU
  have hparent := hweak phi hphi hphi_compact hphi_subU
  have hzeroLeftB : ∀ y, y ∉ axisCube z L →
      vecDot (u.grad y) (euclideanGradient phi y) = 0 := by
    intro y hyB
    have hySupp : y ∉ tsupport phi := fun hy => hyB (hphi_sub hy)
    simp [euclideanGradient_eq_zero_of_notMem_tsupport hySupp, vecDot_zero_right]
  have hzeroLeftU : ∀ y, y ∉ U →
      vecDot (u.grad y) (euclideanGradient phi y) = 0 := by
    intro y hyU
    exact hzeroLeftB y fun hyB => hyU (hBU hyB)
  have hzeroRightB : ∀ y, y ∉ axisCube z L →
      vecDot (H y) (euclideanGradient phi y) = 0 := by
    intro y hyB
    have hySupp : y ∉ tsupport phi := fun hy => hyB (hphi_sub hy)
    simp [euclideanGradient_eq_zero_of_notMem_tsupport hySupp, vecDot_zero_right]
  have hzeroRightU : ∀ y, y ∉ U →
      vecDot (H y) (euclideanGradient phi y) = 0 := by
    intro y hyU
    exact hzeroRightB y fun hyB => hyU (hBU hyB)
  have hleft :
      ∫ y in axisCube z L, vecDot (u.grad y) (euclideanGradient phi y) ∂volume =
        ∫ y in U, vecDot (u.grad y) (euclideanGradient phi y) ∂volume := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroLeftB,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroLeftU]
  have hright :
      ∫ y in axisCube z L, vecDot (H y) (euclideanGradient phi y) ∂volume =
        ∫ y in U, vecDot (H y) (euclideanGradient phi y) ∂volume := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroRightB,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroRightU]
  simpa only [H1Function.restrict, hleft, hright] using hparent

end CubeCalderonZygmund

end

end Homogenization
