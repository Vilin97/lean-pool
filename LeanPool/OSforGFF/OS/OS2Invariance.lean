/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import LeanPool.OSforGFF.Measure.IsGaussian
import LeanPool.OSforGFF.Covariance.Position
import LeanPool.OSforGFF.Spacetime.Euclidean
import LeanPool.OSforGFF.Measure.GaussianFreeField
/-!
# OS2 — Euclidean Invariance

Proves Z[Ef] = Z[f] for any Euclidean transformation E ∈ E(4). The argument:

1. Change variables x → E⁻¹x, y → E⁻¹y in the covariance integral
2. C(x,y) depends only on |x−y|, so C(E⁻¹x, E⁻¹y) = C(x,y)
3. Lebesgue measure is invariant: d⁴(E⁻¹x) = d⁴x (since |det R| = 1)

Hence S(Ef) = ∫∫ f*(x) C(x,y) f(y) dx dy = S(f).

## Main results

- `freeCovarianceℂ_bilinear_euclidean_invariant`
- `CovarianceEuclideanInvariantℂ_μ_GFF`
-/

open MeasureTheory Complex Real Filter
open scoped Real BigOperators

noncomputable section

namespace QFT

variable (m : ℝ) [Fact (0 < m)]

/-! ## Euclidean action on test functions -/

/-- The Euclidean action satisfies (g • f)(x) = f(g⁻¹ • x). -/
lemma euclidean_action_apply (g : E) (f : TestFunctionℂ) (x : SpaceTime) :
    euclideanAction g f x = f (euclideanPullback g x) := by
  unfold euclideanAction
  simp only [SchwartzMap.compCLM_apply]
  rfl

/-- The Euclidean pullback satisfies euclideanPullback g x = g⁻¹ • x = act g⁻¹ x. -/
lemma euclidean_pullback_eq_inv_act (g : E) (x : SpaceTime) :
    euclideanPullback g x = act g⁻¹ x := rfl

/-- Composing pullbacks: euclideanPullback g (act g y) = y. -/
lemma euclidean_pullback_act (g : E) (y : SpaceTime) :
    euclideanPullback g (act g y) = y := by
  simp only [euclidean_pullback_eq_inv_act, act_inv_general]

/-- The forward composition: act g (euclideanPullback g x) = x. -/
lemma act_euclidean_pullback (g : E) (x : SpaceTime) :
    act g (euclideanPullback g x) = x := by
  simp only [euclidean_pullback_eq_inv_act]
  simpa using act_inv_general (g := g⁻¹) x

/-! ## Change of variables for the bilinear form -/

/-- The Euclidean action as a measurable equivalence. -/
noncomputable def actEquiv (g : E) : SpaceTime ≃ᵐ SpaceTime where
  toFun := act g
  invFun := act g⁻¹
  left_inv x := act_inv_general g x
  right_inv x := by simpa using act_inv_general (g := g⁻¹) x
  measurable_toFun := (measurePreserving_act g).measurable
  measurable_invFun := (measurePreserving_act g⁻¹).measurable

/-- Measure-preserving property of actEquiv. -/
lemma measurePreserving_actEquiv (g : E) :
    MeasurePreserving (actEquiv g) volume volume :=
  measurePreserving_act g

/-! ## Main theorem: Bilinear form invariance -/

omit [Fact (0 < m)] in
/-- The complex bilinear covariance form is invariant under Euclidean transformations.
    This is the key lemma showing ⟨g•f, C(g•h)⟩ = ⟨f, Ch⟩.

    **What needs to be proven:**
    Starting from:
    - `freeCovariance_euclidean_invariant`: C(g•x, g•y) = C(x, y) (proven in Covariance.lean)
    - `measurePreserving_act`: act g preserves Lebesgue measure (proven in Euclidean.lean)

    We need to show:
      ∫∫ f(g⁻¹•x) C(x,y) h(g⁻¹•y) dx dy = ∫∫ f(u) C(u,v) h(v) du dv

    **Proof sketch:**
    1. Rewrite C(x,y) = C(g•(g⁻¹•x), g•(g⁻¹•y)) using act_euclidean_pullback
    2. Apply freeCovariance_euclidean_invariant to get C(g⁻¹•x, g⁻¹•y)
    3. Now the integrand is F(g⁻¹•x, g⁻¹•y) where F(u,v) = f(u) C(u,v) h(v)
    4. Change variables u = g⁻¹•x, v = g⁻¹•y (measure-preserving on product space)
    5. Use MeasurePreserving.prod to get measure preservation on SpaceTime × SpaceTime

    **Technical gap:**
    The Mathlib lemma `MeasurePreserving.integral_comp'` requires the integrand
    to have the form `G(e x)` for a MeasurableEquiv `e`. Our integrand after step 2
    has the form `f(g⁻¹•x) * C(g⁻¹•x, g⁻¹•y) * h(g⁻¹•y)` which matches this pattern
    for the product integral ∫ F(e p.1, e p.2) d(p) where e = actEquiv g⁻¹.

    Need to carefully apply integral_prod and MeasurePreserving.prod to complete.
-/
theorem freeCovarianceℂ_bilinear_euclidean_invariant (g : E) (f h : TestFunctionℂ) :
    freeCovarianceℂBilinear m (euclideanAction g f) (euclideanAction g h) =
    freeCovarianceℂBilinear m f h := by
  unfold freeCovarianceℂBilinear
  simp only [euclidean_action_apply]
  -- Goal: ∫∫ f(g⁻¹•x) C(x,y) h(g⁻¹•y) dx dy = ∫∫ f(u) C(u,v) h(v) du dv
  -- Step 1: Rewrite C(x,y) using the identity x = g•(g⁻¹•x)
  have h_rewrite : ∀ x y, freeCovariance m x y =
      freeCovariance m (act g (euclideanPullback g x)) (act g (euclideanPullback g y)) := by
    intro x y
    simp only [act_euclidean_pullback]
  -- Step 2: Apply freeCovariance_euclidean_invariant
  conv_lhs =>
    arg 2; ext x; arg 2; ext y
    rw [h_rewrite x y, freeCovariance_euclidean_invariant]
  -- Now: ∫∫ f(g⁻¹•x) C(g⁻¹•x, g⁻¹•y) h(g⁻¹•y) dx dy = ∫∫ f(u) C(u,v) h(v) du dv
  -- Step 3: Change variables using measure-preserving property
  -- Use the measure-preserving property of actEquiv g
  -- Key: actEquiv g sends u ↦ g•u, so (g⁻¹•(g•u)) = u
  have h_mp := measurePreserving_actEquiv g
  -- MeasurePreserving.integral_comp' h_mp G says: ∫ u, G(g•u) = ∫ x, G x
  -- For the outer integral:
  -- LHS = ∫ x, G x where G x = inner integral with g⁻¹•x
  -- We want ∫ u, G(g•u) = ∫ u, (inner integral with g⁻¹•(g•u)) = ∫ u, (inner integral with u)
  conv_lhs =>
    arg 2; ext x
    rw [← euclidean_pullback_act g x]
  rw [(MeasurePreserving.integral_comp' h_mp _).symm]
  simp only [actEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, euclidean_pullback_act]
  -- Now rewrite inner integral for each fixed u
  congr 1
  funext u
  conv_lhs =>
    arg 2; ext y
    rw [← euclidean_pullback_act g y]
  rw [(MeasurePreserving.integral_comp' h_mp _).symm]
  simp only [actEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, euclidean_pullback_act]

/-- The free GFF measure satisfies the complex covariance Euclidean invariance property.
    This removes the `h_euc` hypothesis from the master theorem.
-/
theorem CovarianceEuclideanInvariantℂ_μ_GFF :
    CovarianceEuclideanInvariantℂ (muGFF m) := by
  intro g f h
  -- Reduce SchwingerFunctionℂ₂ to freeCovarianceℂBilinear via the Gaussian structure
  -- muGFF m = gaussianFreeFieldFree m
  simp only [muGFF]
  rw [gff_two_point_equals_covarianceℂ_free, gff_two_point_equals_covarianceℂ_free]
  exact freeCovarianceℂ_bilinear_euclidean_invariant m g f h

end QFT

end
