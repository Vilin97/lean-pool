/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.KernelAssembly
public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerResume.InfimalLocalityClosure

/-!
The selected envelope gradient closes the smoothing kernel's derivative, smoothness, and
locality properties.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLowerResume

lemma repairKernel_localValue_eq_base (p : ℝ) (d : ℕ) (chi : ℝ)
    (ell : Point d → ℝ) (x : Point d) :
    localSmoothingValue (repairKernel p d) chi ell x =
      localSmoothingValue (repairKernelBase p d) chi ell x := rfl

/-- The constructed oracle value is the literal frozen infimal convolution. -/
theorem repairKernel_value_realization {p : ℝ} {d : ℕ} :
    ∀ (chi : ℝ), 0 < chi → ∀ (ell : Point d → ℝ),
      O3.IsConvexObjective ell → IsOneLipschitz p ell → ∀ x,
      ((repairKernel p d).smooth chi ell).value x =
        localSmoothingValue (repairKernel p d) chi ell x := by
  intro chi hchi ell hconv hlip x
  rfl

/-- Genuine ambient coordinate derivative for the literal infimal value. -/
theorem repairKernel_coordinateGradient {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    SmoothingCoordinateGradientCore (repairKernel p d) := by
  intro chi hchi ell hconv hlip
  simpa [repairKernel, repairSelectedOracle] using
    (repairSelectedOracle_coordinateGradient hp hd hchi ell hconv hlip)

/-- Exact frozen `Mpd/chi` smoothness, with no ambient conversion in the
final estimate. -/
theorem repairKernel_smooth {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    ∀ (chi : ℝ), 0 < chi → ∀ ell : Point d → ℝ,
      O3.IsConvexObjective ell → IsOneLipschitz p ell →
      IsLpSmooth p ((repairKernel p d).Mpd / chi)
        ((repairKernel p d).smooth chi ell) := by
  intro chi hchi ell hconv hlip
  simpa [repairKernel] using
    (repairSelectedOracle_smooth hp hd hchi ell hconv hlip)

/-- The value-level locality already closed in the prefix upgrades to exact
value-gradient observations for the genuine derivative oracle. -/
theorem repairKernel_exactPairLocality {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    ∀ (chi : ℝ), 0 < chi → ∀ ell₁ ell₂ : Point d → ℝ,
      O3.IsConvexObjective ell₁ → IsOneLipschitz p ell₁ →
      O3.IsConvexObjective ell₂ → IsOneLipschitz p ell₂ →
      ∀ x, (∀ v, lpNorm p v ≤ chi → ell₁ (x + v) = ell₂ (x + v)) →
        ((repairKernel p d).smooth chi ell₁).observe x =
          ((repairKernel p d).smooth chi ell₂).observe x := by
  exact exactPairLocality_lowerKernelPhi (repairKernel p d)
    (two_lt_kernelR0 hp hd) (min_le_left _ _)
    (one_lt_repairTheta hp hd)
    ((repairTheta_lt_101_div_100 hp hd).trans (by norm_num))
    (two_mul_repairTheta_lt_kernelR0 hp hd) rfl
    repairKernel_value_realization (repairKernel_coordinateGradient hp hd)

/-- S5-A2 closure package, separated from the remaining signed-equivariance
clauses of the full S5-A carrier. -/
theorem s5a2_envelope_derivative_smoothness_closed {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    (∀ (chi : ℝ), 0 < chi → ∀ (ell : Point d → ℝ),
      O3.IsConvexObjective ell → IsOneLipschitz p ell → ∀ x,
      ((repairKernel p d).smooth chi ell).value x =
        localSmoothingValue (repairKernel p d) chi ell x) ∧
    SmoothingCoordinateGradientCore (repairKernel p d) ∧
    (∀ (chi : ℝ), 0 < chi → ∀ ell : Point d → ℝ,
      O3.IsConvexObjective ell → IsOneLipschitz p ell →
      IsLpSmooth p ((repairKernel p d).Mpd / chi)
        ((repairKernel p d).smooth chi ell)) ∧
    (∀ (chi : ℝ), 0 < chi → ∀ ell₁ ell₂ : Point d → ℝ,
      O3.IsConvexObjective ell₁ → IsOneLipschitz p ell₁ →
      O3.IsConvexObjective ell₂ → IsOneLipschitz p ell₂ →
      ∀ x, (∀ v, lpNorm p v ≤ chi → ell₁ (x + v) = ell₂ (x + v)) →
        ((repairKernel p d).smooth chi ell₁).observe x =
          ((repairKernel p d).smooth chi ell₂).observe x) := by
  exact ⟨repairKernel_value_realization,
    repairKernel_coordinateGradient hp hd,
    repairKernel_smooth hp hd,
    repairKernel_exactPairLocality hp hd⟩

end V7.Stage5AboveTwoLowerS5A2Envelope
