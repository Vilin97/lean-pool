/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmSourceIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenFlowRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KMat

/-! The order-zero `A/q` endpoint is the homogenized flux defect applied to
the flow-averaged pulled gradient. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)

/-- At a fixed time, the flow average in `Gbar` is a finite sum over the
support of the large-scale cutoffs. -/
theorem Gbar_eq_finite_support (m : ℕ) (hm : 1 ≤ m)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    Gbar I hΦ m T t x =
      ∑ l ∈ (I.hatXiML_support_finite hm t).toFinset,
        I.hatXiML m l t • G I hΦ m T l t x := by
  unfold Gbar
  apply tsum_eq_sum
  intro l hl
  have hz : I.hatXiML m l t = 0 := by
    by_contra hn
    exact hl ((I.hatXiML_support_finite hm t).mem_toFinset.mpr hn)
  simp [hz]

/-- The instantaneous `Jhat` minus the time-smoothed `Kmat` is the sum of
the `L_{m,n} q_{m,n,0}` coefficients. -/
theorem Jhat_sub_Kmat_eq_LMN_qMNR_zero (m : ℕ) (κ t : ℝ) :
    I.Jhat κ m t - I.Kmat κ m t =
      ∑ n ∈ Finset.range (Nstar β),
        I.LMN κ m n t • I.qMNR κ m n 0 t := by
  ext i j
  simp only [Ingredients.Jhat, Ingredients.Kmat, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Matrix.sum_apply,
        add_sub_add_left_eq_sub,
    Ingredients.qMNR]
  calc
    _ = ∑ n ∈ Finset.range (Nstar β),
        (I.LMN κ m n t * I.jMN κ m n t i j -
          I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ n ∈ Finset.range (Nstar β),
        I.LMN κ m n t *
          (I.jMN κ m n t i j - timeAvgMat (I.jMN κ m n) i j) := by
          apply Finset.sum_congr rfl
          intro n hn
          ring

/-! The base endpoint is not `-div((JHat - K) GDot)` for the base tensor (corrected form, left
    `F_lᵀ`);
instead it is given by
`LeftJacobian.variantA_hmEndpoint_zero` (`Section5/LeftJacobian/BaseFlux.lean`):
`hmEndpoint … 0 = -div(Σ_l ξ̂_l F_lᵀ (JHat - K) F_l ∇T)`. -/

end AVenhance.Infra.Section5

end
