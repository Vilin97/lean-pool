/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.PrimalOptimality
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
Convexity of the finite-dimensional norm and the power smoothing kernel.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower

lemma lpNorm_add_le {p : ℝ} (hp : 1 ≤ p) (u v : Point d) :
    lpNorm p (u + v) ≤ lpNorm p u + lpNorm p v := by
  let e : ENNReal := ENNReal.ofReal p
  let _ : Fact (1 ≤ e) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  have h := norm_add_le (WithLp.toLp e u : PiLp e (fun _ : Fin d ↦ ℝ))
    (WithLp.toLp e v)
  change O3.lpNorm p (u + v) ≤ O3.lpNorm p u + O3.lpNorm p v
  rw [O3.Stage2RouteC.lpNorm_eq_piLpNorm hp,
    O3.Stage2RouteC.lpNorm_eq_piLpNorm hp,
    O3.Stage2RouteC.lpNorm_eq_piLpNorm hp]
  simpa using h

/-- Convexity of the literal finite-dimensional `lpNorm`, kept in the same
representation as the frozen carrier. -/
lemma convexOn_lpNorm {p : ℝ} (hp : 1 ≤ p) {d : ℕ} :
    ConvexOn ℝ Set.univ (lpNorm p : Point d → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have htri := lpNorm_add_le hp (a • x) (b • y)
  have hsa := O3.Stage2RouteC.lpNorm_smul hp a x
  have hsb := O3.Stage2RouteC.lpNorm_smul hp b y
  change O3.lpNorm p (a • x + b • y) ≤
    O3.lpNorm p (a • x) + O3.lpNorm p (b • y) at htri
  change O3.lpNorm p (a • x + b • y) ≤
    a * O3.lpNorm p x + b * O3.lpNorm p y
  rw [hsa, hsb, abs_of_nonneg ha, abs_of_nonneg hb] at htri
  exact htri

/-- Convexity of the concrete kernel follows from norm convexity and convex,
monotone real power on the nonnegative half-line. -/
theorem lowerKernelPhi_convex {r theta : ℝ}
    (hr : 1 ≤ r) (htheta : 1 < theta) {d : ℕ} :
    O3.IsConvexObjective (lowerKernelPhi (d := d) r theta) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hnorm := (convexOn_lpNorm (d := d) hr).2
    (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have hcomboNonneg : 0 ≤ a * lpNorm r x + b * lpNorm r y :=
    add_nonneg (mul_nonneg ha (O3.lpNorm_nonneg r x))
      (mul_nonneg hb (O3.lpNorm_nonneg r y))
  have hmono : lpNorm r (a • x + b • y) ^ (2 * theta) ≤
      (a * lpNorm r x + b * lpNorm r y) ^ (2 * theta) :=
    Real.rpow_le_rpow (O3.lpNorm_nonneg r _) hnorm (by linarith)
  have hpow := (convexOn_rpow (by linarith : 1 ≤ 2 * theta)).2
    (show lpNorm r x ∈ Set.Ici (0 : ℝ) from O3.lpNorm_nonneg r x)
    (show lpNorm r y ∈ Set.Ici (0 : ℝ) from O3.lpNorm_nonneg r y)
    ha hb hab
  have hpow' : (a * lpNorm r x + b * lpNorm r y) ^ (2 * theta) ≤
      a * lpNorm r x ^ (2 * theta) +
        b * lpNorm r y ^ (2 * theta) := by
    simpa [smul_eq_mul] using hpow
  rw [lowerKernelPhi_eq_norm_power (by linarith : r ≠ 0),
    lowerKernelPhi_eq_norm_power (by linarith : r ≠ 0),
    lowerKernelPhi_eq_norm_power (by linarith : r ≠ 0)]
  change 2 * lpNorm r (a • x + b • y) ^ (2 * theta) ≤
    a * (2 * lpNorm r x ^ (2 * theta)) +
      b * (2 * lpNorm r y ^ (2 * theta))
  nlinarith

end V7.Stage5AboveTwoLowerS5A2Envelope
