/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerResume.InfimalAttainment

/-!
Locality of the infimal smoothing value and its exact value-gradient observations.
-/

namespace V7.Stage5AboveTwoLowerResume

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair

/-- Uniform outer-quarter minimizer control supplies exactly the
nearby-centre stability needed by the existing infimal-locality bridge. -/
theorem localSmoothingValue_eventually_eq_lowerKernelPhi
    (kernel : SmoothingKernelData p d) {r theta chi : ℝ}
    (hr : 2 < r) (hrp : r ≤ p) (htheta : 1 < theta)
    (hthetaUpper : theta < 5 / 4) (htr : 2 * theta < r)
    (hchi : 0 < chi) (hkernelPhi : kernel.phi = lowerKernelPhi r theta)
    (ell₁ ell₂ : Point d → ℝ)
    (hlip₁ : IsOneLipschitz p ell₁) (hlip₂ : IsOneLipschitz p ell₂)
    (x : Point d)
    (heq : ∀ u, lpNorm p u ≤ chi → ell₁ (x + u) = ell₂ (x + u)) :
    localSmoothingValue kernel chi ell₁ =ᶠ[nhds x]
      localSmoothingValue kernel chi ell₂ := by
  let eta : ℝ := chi / 4
  have hp : 1 ≤ p := by linarith
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hnear : ∀ᶠ y in nhds x, lpNorm p (y - x) < eta :=
    eventually_lpNorm_sub_lt hp heta x
  have hmargin : ∀ᶠ y in nhds x, ∃ v₁ v₂ : Point d,
      IsInfimalMinimizer kernel chi ell₁ y v₁ ∧
      IsInfimalMinimizer kernel chi ell₂ y v₂ ∧
      lpNorm p v₁ ≤ chi - eta ∧ lpNorm p v₂ ≤ chi - eta := by
    filter_upwards [] with y
    obtain ⟨v₁, hv₁min, hv₁margin⟩ :=
      exists_infimal_minimizer_lowerKernelPhi_with_margin kernel hr hrp
        htheta hthetaUpper htr hchi hkernelPhi ell₁ hlip₁ y
    obtain ⟨v₂, hv₂min, hv₂margin⟩ :=
      exists_infimal_minimizer_lowerKernelPhi_with_margin kernel hr hrp
        htheta hthetaUpper htr hchi hkernelPhi ell₂ hlip₂ y
    exact ⟨v₁, v₂, hv₁min, hv₂min, hv₁margin, hv₂margin⟩
  exact localSmoothingValue_eventually_eq_of_stable_minimizers kernel heq
    (stable_minimizers_of_uniform_interior_margin kernel hp heta hnear hmargin)

/-- The concrete kernel and the frozen value-realization clause imply the
full neighbourhood-stability interface. -/
theorem neighborhoodStability_lowerKernelPhi
    (kernel : SmoothingKernelData p d) {r theta : ℝ}
    (hr : 2 < r) (hrp : r ≤ p) (htheta : 1 < theta)
    (hthetaUpper : theta < 5 / 4) (htr : 2 * theta < r)
    (hkernelPhi : kernel.phi = lowerKernelPhi r theta)
    (hvalue : ∀ (chi : ℝ), 0 < chi → ∀ (ell : Point d → ℝ),
      O3.IsConvexObjective ell → IsOneLipschitz p ell → ∀ x,
      (kernel.smooth chi ell).value x = localSmoothingValue kernel chi ell x) :
    LocalSmoothingNeighborhoodStability kernel := by
  intro chi hchi ell₁ ell₂ hconvex₁ hlip₁ hconvex₂ hlip₂ x heq
  have hlocal := localSmoothingValue_eventually_eq_lowerKernelPhi kernel hr hrp
    htheta hthetaUpper htr hchi hkernelPhi ell₁ ell₂ hlip₁ hlip₂ x heq
  filter_upwards [hlocal] with y hy
  rw [hvalue chi hchi ell₁ hconvex₁ hlip₁ y,
    hvalue chi hchi ell₂ hconvex₂ hlip₂ y]
  exact hy

/-- The existing differential bridge upgrades the neighbourhood result to
the exact value-gradient observation required by the frozen carrier. -/
theorem exactPairLocality_lowerKernelPhi
    (kernel : SmoothingKernelData p d) {r theta : ℝ}
    (hr : 2 < r) (hrp : r ≤ p) (htheta : 1 < theta)
    (hthetaUpper : theta < 5 / 4) (htr : 2 * theta < r)
    (hkernelPhi : kernel.phi = lowerKernelPhi r theta)
    (hvalue : ∀ (chi : ℝ), 0 < chi → ∀ (ell : Point d → ℝ),
      O3.IsConvexObjective ell → IsOneLipschitz p ell → ∀ x,
      (kernel.smooth chi ell).value x = localSmoothingValue kernel chi ell x)
    (hgradient : SmoothingCoordinateGradientCore kernel) :
    ∀ (chi : ℝ), 0 < chi → ∀ ell₁ ell₂ : Point d → ℝ,
      O3.IsConvexObjective ell₁ → IsOneLipschitz p ell₁ →
      O3.IsConvexObjective ell₂ → IsOneLipschitz p ell₂ →
      ∀ x, (∀ v, lpNorm p v ≤ chi → ell₁ (x + v) = ell₂ (x + v)) →
        (kernel.smooth chi ell₁).observe x =
          (kernel.smooth chi ell₂).observe x :=
by
  exact exact_pair_locality_of_neighborhood_stability kernel hgradient
    (neighborhoodStability_lowerKernelPhi kernel hr hrp htheta hthetaUpper
      htr hkernelPhi hvalue)

end V7.Stage5AboveTwoLowerResume
