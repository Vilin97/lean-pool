/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.L.SlitDeriv

/-!
# The full Euler–Poisson system for Carlson's L-function

Carlson (1987), (2.7), for all complex parameters and all slit-plane nodes.
Joint holomorphy of the second node derivatives permits continuation first in the
parameters and then in the nodes. Equal indices and coincident nodes are included.
-/

open Complex Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

open scoped Classical in
private theorem analyticOnNhd_secondPartial_regCarlsonLSlit_joint (i j : ι) :
    AnalyticOnNhd ℂ (fun p : Option (ι ⊕ ι) → ℂ =>
      carlsonPartialDeriv i (carlsonPartialDeriv j
        (regCarlsonLSlit (p none) (fun k => p (some (.inl k)))))
        (fun k => p (some (.inr k))))
      {p | (fun k => p (some (.inr k))) ∈ carlsonRSlitDomain} := by
  have h := (analyticOnNhd_carlsonPartialDeriv_regCarlsonLSlit_joint j).partialDeriv
    (isOpen_carlsonRSlitDomain.preimage (by fun_prop)) (some (Sum.inr i))
  have heq : SeveralComplexVariables.partialDeriv (some (Sum.inr i))
      (fun p : Option (ι ⊕ ι) → ℂ => carlsonPartialDeriv j
        (regCarlsonLSlit (p none) (fun k => p (some (.inl k)))) (fun k => p (some (.inr k)))) =
      (fun p => carlsonPartialDeriv i (carlsonPartialDeriv j
        (regCarlsonLSlit (p none) (fun k => p (some (.inl k))))) (fun k => p (some (.inr k)))) := by
    funext p
    change deriv _ _ = deriv _ _
    congr 1
    funext w
    simp [Function.update_apply]
    congr 1
    funext k
    simp [Function.update_apply]
  rwa [heq] at h

/-- The entire Euler–Poisson expression is jointly holomorphic in all its arguments. -/
theorem analyticAt_carlsonEulerPoissonOperator_regCarlsonLSlit_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : E → ℂ} {b z : E → ι → ℂ} {p : E}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) (i j : ι) :
    AnalyticAt ℂ (fun q => carlsonEulerPoissonOperator i j (b q) (z q)
      (regCarlsonLSlit (t q) (b q))) p := by
  let f : E → Option (ι ⊕ ι) → ℂ := fun q k => k.elim (t q) (Sum.elim (b q) (z q))
  have hf : AnalyticAt ℂ f p := by
    apply analyticAt_pi_iff.mpr
    intro k
    cases k with
    | none => exact ht
    | some k =>
      cases k with
      | inl k => exact (analyticAt_pi_iff.mp hb) k
      | inr k => exact (analyticAt_pi_iff.mp hz) k
  have hsecond := (analyticOnNhd_secondPartial_regCarlsonLSlit_joint i j (f p) hslit).comp_of_eq hf rfl
  have hfirst (k : ι) := analyticAt_carlsonPartialDeriv_regCarlsonLSlit_comp ht hb hz hslit k
  exact ((((analyticAt_pi_iff.mp hz) i).sub ((analyticAt_pi_iff.mp hz) j)).mul hsecond |>.add
    (((analyticAt_pi_iff.mp hb) i).mul (hfirst j))).sub
      (((analyticAt_pi_iff.mp hb) j).mul (hfirst i))

private theorem eulerPoisson_regCarlsonLSlit_of_native (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) (i j : ι) :
    carlsonEulerPoissonOperator i j b z (regCarlsonLSlit t b) = 0 := by
  have hfirst (k : ι) {w : ι → ℂ} (hw : w ∈ carlsonRVariableDomain) :
      carlsonPartialDeriv k (regCarlsonLSlit t b) w =
        carlsonPartialDeriv k (regCarlsonLIntegral t b) w := by
    apply SeveralComplexVariables.partialDeriv_congr
    filter_upwards [isOpen_carlsonRVariableDomain.mem_nhds hw] with v hv
    exact regCarlsonLSlit_eq_integral t hv hb
  have hsecond : carlsonPartialDeriv i (carlsonPartialDeriv j (regCarlsonLSlit t b)) z =
      carlsonPartialDeriv i (carlsonPartialDeriv j (regCarlsonLIntegral t b)) z := by
    apply SeveralComplexVariables.partialDeriv_congr
    filter_upwards [isOpen_carlsonRVariableDomain.mem_nhds hz] with w hw
    exact hfirst j hw
  unfold carlsonEulerPoissonOperator
  rw [hsecond, hfirst i hz, hfirst j hz]
  exact carlsonEulerPoissonOperator_regCarlsonLIntegral t hb hz i j

/-- Carlson (1987), (2.7), without convergence restrictions or node-separation assumptions. -/
theorem carlsonEulerPoissonOperator_regCarlsonLSlit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    carlsonEulerPoissonOperator i j b z (regCarlsonLSlit t b) = 0 := by
  have hright {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
      carlsonEulerPoissonOperator i j b z (regCarlsonLSlit t b) = 0 := by
    have ha : AnalyticOnNhd ℂ (fun b => carlsonEulerPoissonOperator i j b z (regCarlsonLSlit t b)) univ :=
      fun _ _ => analyticAt_carlsonEulerPoissonOperator_regCarlsonLSlit_comp
        analyticAt_const analyticAt_id analyticAt_const (carlsonRVariableDomain_subset_slitDomain hz) i j
    exact congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent ha analyticOnNhd_const
      (fun _ hb => eulerPoisson_regCarlsonLSlit_of_native t hb hz i j)) b
  have ha : AnalyticOnNhd ℂ (fun z => carlsonEulerPoissonOperator i j b z (regCarlsonLSlit t b))
      carlsonRSlitDomain := fun _ hz => analyticAt_carlsonEulerPoissonOperator_regCarlsonLSlit_comp
        analyticAt_const analyticAt_const analyticAt_id hz i j
  exact eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane ha analyticOnNhd_const (fun _ hw => hright hw) hz

/-- The ordinary normalization satisfies the same homogeneous PDE wherever it represents
the ordinary function; the identity also holds for Lean's totalization at Gamma poles. -/
theorem carlsonEulerPoissonOperator_carlsonLSlit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    carlsonEulerPoissonOperator i j b z (carlsonLSlit t b) = 0 := by
  change carlsonEulerPoissonOperator i j b z
    (fun w => Gamma (∑ k, b k) * regCarlsonLSlit t b w) = 0
  rw [carlsonEulerPoissonOperator_const_mul,
    carlsonEulerPoissonOperator_regCarlsonLSlit t b hz i j, mul_zero]

end DirichletTransform
