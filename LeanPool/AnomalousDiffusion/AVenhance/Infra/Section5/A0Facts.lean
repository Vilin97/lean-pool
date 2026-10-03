/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.FrozenEstimates
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Scalar assembly facts for the main theorem. Energy is an explicit input, not a claim that
weak-solution energy has been . Nonzero energy is distinguished from
pointwise nonzero representatives in the analytic-radius bridge. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVenhance.Infra.Section5

/-- Literal energy balance, evaluated at t=1. Its space-time integral is over
(0,t)×unitCube, the same carrier as the dissipation at t=1. The weak
solution and drift hypotheses are unnecessary once this identity is supplied. -/
theorem energy_dissipation_bound_conditional {κ : ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (henergy : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      l2NormSq (θ t) + 2 * κ *
        (∫ p in Set.Ioo (0 : ℝ) t ×ˢ unitCube, vecNormSq (Dθ p.1 p.2)) =
          l2NormSq θ₀) :
    κ * spaceTimeGradNormSq Dθ ≤ l2NormSq θ₀ / 2 := by
  have h := henergy 1 ⟨by norm_num, le_rfl⟩
  have hn : 0 ≤ l2NormSq (θ 1) := integral_nonneg (fun x => sq_nonneg _)
  change l2NormSq (θ 1) + 2 * κ * spaceTimeGradNormSq Dθ = l2NormSq θ₀ at h
  linarith

/-- The n=1 analytic estimates bound the Euclidean gradient, with its two
coordinate directions retained. -/
theorem analytic_gradient_bound {f : Vec 2 → ℝ} {R : ℝ}
    (hf : ContDiff ℝ 1 f) (ha : IsThetaAnalytic R f) :
    gradNormSq (spaceGrad f) ≤ 2 * l2NormSq f / R ^ 2 := by
  have hi (i : Fin 2) : IntegrableOn (fun x => (spaceGrad f x i) ^ 2) unitCube := by
    have hc : Continuous (fun x => (spaceGrad f x i) ^ 2) := by
      unfold spaceGrad
      exact ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
    have hcompact : IsCompact (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    apply (hc.continuousOn.integrableOn_compact hcompact).mono_set
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    intro i
    exact ⟨(hx i).1.le, (hx i).2.le⟩
  have hb (i : Fin 2) : (∫ x in unitCube, (spaceGrad f x i) ^ 2) ≤ l2NormSq f / R ^ 2 := by
    have h := ha 1 le_rfl (fun _ => i)
    simp only [iteratedFDeriv_one_apply, Nat.factorial_one, Nat.cast_one, pow_one] at h
    change Real.sqrt (∫ x in unitCube, (spaceGrad f x i) ^ 2) ≤ _ at h
    have hn : 0 ≤ ∫ x in unitCube, (spaceGrad f x i) ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    have hA : 0 ≤ l2NormSq f := integral_nonneg (fun x => sq_nonneg _)
    -- A positive radius is enforced below in the usable version.
    by_cases hR : 0 ≤ Real.sqrt (l2NormSq f) * (1 / R)
    · have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) hR).2 h
      rw [Real.sq_sqrt hn, mul_pow, Real.sq_sqrt hA, div_pow] at hh
      simpa [div_eq_mul_inv] using hh
    · exact False.elim (hR ((Real.sqrt_nonneg _).trans h))
  unfold gradNormSq vecNormSq vecDot
  simp only [← pow_two]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simpa [mul_div_assoc] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)

/-- for smooth, mean-zero data of positive L2 energy. Pointwise nonzero
alone is not a nonzero L2 class in the carriers. -/
theorem analytic_radius_bound {f : Vec 2 → ℝ} {R : ℝ}
    (hf : ContDiff ℝ 1 f) (hp : IsZ2Periodic f)
    (hm : ∫ x in unitCube, f x = 0) (hA : 0 < l2NormSq f)
    (hR : 0 < R) (ha : IsThetaAnalytic R f) :
    R ≤ 1 / (Real.sqrt 2 * Real.pi) := by
  have hg := analytic_gradient_bound hf ha
  have hP := Infra.Torus.l2NormSq_le_fourierPoincare hf hp hm
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  have hP' := (le_div_iff₀ hpi).1 (by simpa [div_eq_mul_inv, mul_comm] using hP)
  have hg' := (le_div_iff₀ (sq_pos_of_pos hR)).1 hg
  have hb : R ^ 2 * (4 * Real.pi ^ 2) ≤ 2 := by
    nlinarith only [hP', hg', hA]
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply (le_div_iff₀ (by positivity : 0 < Real.sqrt 2 * Real.pi)).2
  nlinarith only [hb, hs, hR, Real.pi_pos, Real.sqrt_nonneg 2,
    sq_nonneg (R * Real.sqrt 2 * Real.pi - 1)]

end AVenhance.Infra.Section5
