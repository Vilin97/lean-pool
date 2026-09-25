/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.LowerBoundStatements

/-!
Neighborhood equality of smooth objective values determines the complete exact oracle pair.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLower

/-- Once two differentiable smoothing values agree on a neighbourhood, their
exact value-gradient observations agree at the centre.  Thus the analytic
content of exact-pair locality is precisely neighbourhood stability of the
infimal convolution, not a separate gradient oracle assumption. -/
lemma observe_eq_of_eventually_value_eq {d : ℕ} (oracle₁ oracle₂ : PairOracle d)
    (x : Point d) (hgrad₁ : O3.IsCoordinateGradient oracle₁.value oracle₁.gradient)
    (hgrad₂ : O3.IsCoordinateGradient oracle₂.value oracle₂.gradient)
    (hlocal : oracle₁.value =ᶠ[nhds x] oracle₂.value) :
    oracle₁.observe x = oracle₂.observe x := by
  classical
  have hx : oracle₁.value x = oracle₂.value x := hlocal.self_of_nhds
  have hfderiv : fderiv ℝ oracle₁.value x = fderiv ℝ oracle₂.value x :=
    hlocal.fderiv_eq
  have hgradient : oracle₁.gradient x = oracle₂.gradient x := by
    funext i
    let ei : Point d := fun j => if j = i then 1 else 0
    have happly := congrArg
      (fun L : Point d →L[ℝ] ℝ => L ei) hfderiv
    rw [(hgrad₁ x).2, (hgrad₂ x).2] at happly
    simpa [O3.pairing, ei] using happly
  simp only [O3.PairOracle.observe]
  rw [hx, hgradient]

/-- The minimal analytic bridge still needed from the concrete infimal
convolution: equality of the original objectives on the closed smoothing ball
must make the two smoothed value functions equal on a neighbourhood of the
centre.  The strict boundary inequality of the kernel is what supplies the
required interior slack. -/
def LocalSmoothingNeighborhoodStability (kernel : SmoothingKernelData p d) : Prop :=
  ∀ (chi : ℝ), 0 < chi → ∀ ell₁ ell₂ : Point d → ℝ,
    O3.IsConvexObjective ell₁ → IsOneLipschitz p ell₁ →
    O3.IsConvexObjective ell₂ → IsOneLipschitz p ell₂ →
    ∀ x, (∀ v, lpNorm p v ≤ chi → ell₁ (x + v) = ell₂ (x + v)) →
      (kernel.smooth chi ell₁).value =ᶠ[nhds x]
        (kernel.smooth chi ell₂).value

/-- Smoothing a convex one-Lipschitz objective produces an oracle with the exact coordinate
gradient. -/
def SmoothingCoordinateGradientCore (kernel : SmoothingKernelData p d) : Prop :=
  ∀ (chi : ℝ), 0 < chi → ∀ ell : Point d → ℝ,
    O3.IsConvexObjective ell → IsOneLipschitz p ell →
      O3.IsCoordinateGradient (kernel.smooth chi ell).value
        (kernel.smooth chi ell).gradient

/-- Neighbourhood stability plus the already required coordinate-gradient
interface is sufficient for the frozen exact value-gradient locality clause. -/
lemma exact_pair_locality_of_neighborhood_stability
    (kernel : SmoothingKernelData p d)
    (hgradient : SmoothingCoordinateGradientCore kernel)
    (hstable : LocalSmoothingNeighborhoodStability kernel) :
    ∀ (chi : ℝ), 0 < chi → ∀ ell₁ ell₂ : Point d → ℝ,
      O3.IsConvexObjective ell₁ → IsOneLipschitz p ell₁ →
      O3.IsConvexObjective ell₂ → IsOneLipschitz p ell₂ →
      ∀ x, (∀ v, lpNorm p v ≤ chi → ell₁ (x + v) = ell₂ (x + v)) →
        (kernel.smooth chi ell₁).observe x =
          (kernel.smooth chi ell₂).observe x := by
  intro chi hchi ell₁ ell₂ hconvex₁ hlip₁ hconvex₂ hlip₂ x heq
  exact observe_eq_of_eventually_value_eq _ _ x
    (hgradient chi hchi ell₁ hconvex₁ hlip₁)
    (hgradient chi hchi ell₂ hconvex₂ hlip₂)
    (hstable chi hchi ell₁ ell₂ hconvex₁ hlip₁ hconvex₂ hlip₂ x heq)

end V7.Stage5AboveTwoLower
