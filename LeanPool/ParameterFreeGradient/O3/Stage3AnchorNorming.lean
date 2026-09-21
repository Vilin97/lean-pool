/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Anchor
import LeanPool.ParameterFreeGradient.O3.Stage2RouteB
import LeanPool.ParameterFreeGradient.O3.Stage2RouteC
import LeanPool.ParameterFreeGradient.O3.Stage2RouteD

/-!
# Stage 3: exact real-exponent anchor norming vector

The source coordinate formula is identified with the normalized duality map,
then its two norming identities are derived without adding them as hypotheses.
-/

namespace O3
namespace Stage3Anchor

lemma conjugateExponent_conjugateExponent {p : ℝ} (hp : 1 < p) :
    conjugateExponent (conjugateExponent p) = p := by
  rw [conjugateExponent_eq, conjugateExponent_eq]
  have hpm : p - 1 ≠ 0 := by linarith
  field_simp [hpm]
  ring

lemma p_mul_conjugateExponent_sub_one {p : ℝ} (hp : 1 < p) :
    p * (conjugateExponent p - 1) = conjugateExponent p := by
  have h := Stage2RouteB.mul_conjugateExponent_sub_one hp
  nlinarith

/-- Coordinate identity behind the source sign-power formula.  It covers a
zero coordinate even when `q - 2` is negative. -/
lemma sign_mul_abs_rpow_sub_one {q a : ℝ} (hq : 1 < q) :
    (SignType.sign a : ℝ) * |a| ^ (q - 1) = |a| ^ (q - 2) * a := by
  by_cases ha : a = 0
  · subst a
    simp [Real.zero_rpow (by linarith : q - 1 ≠ 0)]
  · rcases lt_or_gt_of_ne ha with haNeg | haPos
    · have hs : (SignType.sign a : ℝ) = -1 := by
        rw [sign_neg haNeg]
        rfl
      rw [hs, abs_of_neg haNeg]
      have hpw : (-a) ^ (q - 2) * (-a) = (-a) ^ (q - 1) := by
        calc
          (-a) ^ (q - 2) * (-a) = (-a) ^ (q - 2) * (-a) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = (-a) ^ ((q - 2) + 1) :=
            (Real.rpow_add (neg_pos.mpr haNeg) _ _).symm
          _ = (-a) ^ (q - 1) := by ring_nf
      calc
        (-1 : ℝ) * (-a) ^ (q - 1) = -((-a) ^ (q - 1)) := by ring
        _ = (-a) ^ (q - 2) * a := by rw [← hpw]; ring
    · have hs : (SignType.sign a : ℝ) = 1 := by
        rw [sign_pos haPos]
        rfl
      rw [hs, abs_of_pos haPos, one_mul]
      calc
        a ^ (q - 1) = a ^ ((q - 2) + 1) := by ring_nf
        _ = a ^ (q - 2) * a ^ (1 : ℝ) := Real.rpow_add haPos _ _
        _ = a ^ (q - 2) * a := by rw [Real.rpow_one]

lemma inv_rpow_anchor_coefficient {q n : ℝ} (hn : 0 < n) :
    1 / n ^ (q - 1) = n⁻¹ * n ^ (2 - q) := by
  have hpow : n ^ (q - 1) * n ^ (2 - q) = n := by
    rw [← Real.rpow_add hn]
    have hexp : q - 1 + (2 - q) = 1 := by ring
    rw [hexp, Real.rpow_one]
  have hne : n ^ (q - 1) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
  field_simp [hne, hn.ne']
  nlinarith

/-- The explicit source vector is exactly `J_q(g) / ||g||_q`. -/
lemma anchorNormingVector_eq_inv_smul_dualityMap {q : ℝ} (hq : 1 < q)
    {d : ℕ} (g : Vec d) (hg : g ≠ 0) :
    anchorNormingVector q g = (lpNorm q g)⁻¹ • dualityMap q g := by
  have hn : 0 < lpNorm q g := lpNorm_pos_of_ne_zero hg
  rw [dualityMap, ite_eq_right hn.ne']
  funext i
  simp only [anchorNormingVector, Pi.smul_apply, smul_eq_mul]
  rw [sign_mul_abs_rpow_sub_one hq]
  have hc : ((lpNorm q g) ^ (q - 1))⁻¹ =
      (lpNorm q g)⁻¹ * (lpNorm q g) ^ (2 - q) := by
    simpa [one_div] using inv_rpow_anchor_coefficient (q := q) hn
  rw [div_eq_mul_inv, hc]
  ring

/-- First frozen norming identity, for genuine real conjugate exponents. -/
theorem anchorNormingVector_lpNorm {p : ℝ} (hp : 1 < p) {d : ℕ}
    (g : Vec d) (hg : g ≠ 0) :
    lpNorm p (anchorNormingVector (conjugateExponent p) g) = 1 := by
  let q := conjugateExponent p
  have hq : 1 < q := one_lt_conjugateExponent hp
  have hn : 0 < lpNorm q g := lpNorm_pos_of_ne_zero hg
  rw [anchorNormingVector_eq_inv_smul_dualityMap hq g hg]
  rw [Stage2RouteC.lpNorm_smul (by linarith : 1 ≤ p)]
  have hJ := Stage2RouteB.lpNorm_dualityMap hq g
  rw [conjugateExponent_conjugateExponent hp] at hJ
  rw [hJ, abs_of_pos (inv_pos.mpr hn)]
  exact inv_mul_cancel₀ hn.ne'

/-- Second frozen norming identity, with the exact source pairing order. -/
theorem pairing_anchorNormingVector {p : ℝ} (hp : 1 < p) {d : ℕ}
    (g : Vec d) (hg : g ≠ 0) :
    pairing g (anchorNormingVector (conjugateExponent p) g) =
      lpNorm (conjugateExponent p) g := by
  let q := conjugateExponent p
  change pairing g (anchorNormingVector q g) = lpNorm q g
  have hq : 1 < q := one_lt_conjugateExponent hp
  have hn : 0 < lpNorm q g := lpNorm_pos_of_ne_zero hg
  rw [anchorNormingVector_eq_inv_smul_dualityMap hq g hg]
  rw [Stage2RouteD.pairing_smul_right, pairing_comm]
  rw [Stage2RouteB.pairing_dualityMap_self hq]
  field_simp [hn.ne']

end Stage3Anchor
end O3
