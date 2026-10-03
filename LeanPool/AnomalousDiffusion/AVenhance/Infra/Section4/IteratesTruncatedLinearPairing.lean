/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesIntegralCauchy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCell

/-! Linear L2 pairing estimates for actual commutator coefficient terms. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Bounded coefficient multiplication preserves the linear product of the
two L2 bounds. All natural integrability follows from actual continuity. -/
theorem iterate_truncated_coefficient_linear_pairing_bound {a g q : AmnrSpace → ℝ} {A G D : ℝ}
    {s : ℝ} (hs1 : s ≤ 1)
    (ha : ContinuousOn a (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hq : ContinuousOn q (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hD : 0 ≤ D)
    (hb : ∀ z, |q z| ≤ D)
    (hEa : (∫ z in timeCube, a z ^ 2) ≤ A ^ 2)
    (hEg : (∫ z in timeCube, g z ^ 2) ≤ G ^ 2) :
    |∫ z in iterateTruncatedCell s, a z * (q z * g z)| ≤ D * A * G := by
  have haI := iterate_timeCube_integrable_of_continuousOn (ha.pow 2)
  have hgI := iterate_timeCube_integrable_of_continuousOn (hg.pow 2)
  have hqgI := iterate_timeCube_integrable_of_continuousOn ((hq.mul hg).pow 2)
  have hpI := iterate_timeCube_integrable_of_continuousOn (ha.mul (hq.mul hg))
  have hm : (∫ z in timeCube, (q z * g z) ^ 2) ≤ D ^ 2 * (∫ z in timeCube, g z ^ 2) := by
    have ht := integral_mono hqgI (hgI.const_mul (D ^ 2)) (fun z => by
      have hs := (sq_le_sq₀ (abs_nonneg (q z)) hD).mpr (hb z)
      have hh := mul_le_mul_of_nonneg_right hs (sq_nonneg (g z))
      simpa only [sq_abs, mul_pow, Pi.pow_apply, Pi.mul_apply] using hh)
    simpa only [integral_const_mul, Pi.pow_apply, Pi.mul_apply] using ht
  have he : (∫ z in timeCube, (q z * g z) ^ 2) ≤ (D * G) ^ 2 := by
    exact hm.trans (by simpa only [mul_pow] using
      mul_le_mul_of_nonneg_left hEg (sq_nonneg D))
  have hsub := iterateTruncatedCell_subset hs1
  have hEa' := (iterate_truncated_nonnegative_integral_le haI (fun _ => sq_nonneg _) hs1).trans hEa
  have hEg' := (iterate_truncated_nonnegative_integral_le hqgI (fun _ => sq_nonneg _) hs1).trans he
  have h := iterate_integral_pairing_bound hA (mul_nonneg hD hG)
    (haI.mono_set hsub) (hqgI.mono_set hsub) (hpI.mono_set hsub) hEa' hEg'
  exact h.trans_eq (by ring)

end AVenhance.Infra.Section4
