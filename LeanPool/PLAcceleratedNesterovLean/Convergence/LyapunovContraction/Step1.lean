/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue


/-!
# Lyapunov Contraction Step 1: Descent Lemma and Parameter Identities

## Descent Lemma
For L-smooth f with step x₊ = x - (1/L)∇f(x):
  f(x₊) ≤ f(x) - (1/(2L))‖∇f(x)‖²

## Parameter Identities
With ρ = (1-a)/(1+a) and λ = (1+a)²/(2(1-a)):
  (1+a)ρ = 1-a
  λρ² = (1-a)/2

## Velocity Coefficient Bound
If ε·η ≤ a and 0 ≤ a < 1:
  (1-a)² + ε·η·(1-a) ≤ 1-a
  (1-a)(1+a) ≤ (1+a)² = 2(1-a)λ
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped NNReal

/-- Descent lemma: f(x - η·∇f(x)) ≤ f(x) - (η/2)·‖∇f(x)‖² for η = 1/L.
    This is stated abstractly: if f(y) ≤ f(x) + ⟨∇f(x), y-x⟩ + (L/2)‖y-x‖²
    and y = x - (1/L)·∇f(x), then f(y) ≤ f(x) - (1/(2L))·‖∇f(x)‖². -/
theorem descent_lemma (fx fy : ℝ) (grad_sq : ℝ) (L : ℝ)
    (hL : 0 < L)
    (hsmooth : fy ≤ fx - (1 / L) * grad_sq +
      (L / 2) * (1 / L) ^ 2 * grad_sq) :
    fy ≤ fx - 1 / (2 * L) * grad_sq := by
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have key : fx - 1 / L * grad_sq + L / 2 * (1 / L) ^ 2 * grad_sq = fx - 1 / (2 * L) * grad_sq := by
    field_simp
    ring
  linarith

/-- Parameter identity: (1 + a) · ρ = 1 - a when ρ = (1-a)/(1+a). -/
theorem rho_identity (a ρ : ℝ) (ha : 1 + a ≠ 0)
    (hρ : ρ = (1 - a) / (1 + a)) :
    (1 + a) * ρ = 1 - a := by
  rw [hρ, mul_div_cancel₀ _ ha]

/-- Parameter identity: λ · ρ² = (1-a)/2 when ρ = (1-a)/(1+a) and λ = (1+a)²/(2(1-a)). -/
theorem lambda_rho_sq (a ρ lam : ℝ) (ha_ne : 1 + a ≠ 0) (ha_pos : 1 - a ≠ 0)
    (hρ : ρ = (1 - a) / (1 + a))
    (hlam : lam = (1 + a) ^ 2 / (2 * (1 - a))) :
    lam * ρ ^ 2 = (1 - a) / 2 := by
  subst hρ; subst hlam; field_simp

/-- Velocity normal coefficient bound: (1-a)² + εη(1-a) ≤ (1-a) when εη ≤ a. -/
theorem velocity_normal_coeff (a εη : ℝ) (_ha : 0 ≤ a) (ha1 : a ≤ 1)
    (_hεη : 0 ≤ εη) (hbound : εη ≤ a) :
    (1 - a) ^ 2 + εη * (1 - a) ≤ 1 - a := by
  nlinarith [sq_nonneg a, sq_nonneg (1 - a)]

/-- Tangential coefficient bound: (1-a)(1+a) ≤ (1+a)². -/
theorem tangential_coeff (a : ℝ) (ha : 0 ≤ a) :
    (1 - a) * (1 + a) ≤ (1 + a) ^ 2 := by
  nlinarith [sq_nonneg a]

/-- Quadratic Upper Bound (QUB) from L-smoothness: for any x, w,
    f(x + w) - f(x) ≤ ⟨∇f(x), w⟩ + L/2·‖w‖². -/
theorem lsmooth_qub {d : ℕ} (f : E d → ℝ) (L : ℝ≥0)
    {V : Set (E d)} (hV : IsOpen V)
    (hf_diff : DifferentiableOn ℝ f V)
    (hf_lip : LipschitzOnWith L (gradient f) V)
    (x w : E d)
    (hx_V : x ∈ V)
    (hseg_V : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → x + t • w ∈ V) :
    f (x + w) - f x ≤
      @inner ℝ _ _ (gradient f x) w + (↑L : ℝ) / 2 * ‖w‖ ^ 2 := by
  set g := gradient f x with hg_def
  set ci := @inner ℝ _ _ g w with hci_def
  set cn := ‖w‖ ^ 2 with hcn_def
  -- Define ψ(t) = f(x + t·w) - f(x) - t·⟨g,w⟩ - (L/2)t²·‖w‖²
  set ψ : ℝ → ℝ := fun t => f (x + t • w) - f x - t * ci - (↑L : ℝ) / 2 * t ^ 2 * cn
  -- Goal: ψ 1 ≤ 0
  suffices hψle : ψ 1 ≤ 0 by
    simp only [ψ, one_smul, one_pow, mul_one] at hψle; linarith
  -- ψ(0) = 0
  have hψ0 : ψ 0 = 0 := by
    simp only [zero_smul, add_zero, sub_self, zero_mul,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, ψ]
  -- HasDerivAt for the affine path
  have hpath_da : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • w) w t := by
    intro t
    have h := (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const w)
    simp only [zero_add, one_smul] at h; exact h
  -- HasDerivAt for f ∘ path via chain rule
  have hfp_da : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      HasDerivAt (fun s => f (x + s • w)) (fderiv ℝ f (x + t • w) w) t := by
    intro t ht
    have hmem := hseg_V t ht.1 ht.2
    exact (hf_diff _ hmem).differentiableAt (hV.mem_nhds hmem) |>.hasFDerivAt.comp_hasDerivAt
      t (hpath_da t)
  -- HasDerivAt for ψ
  have hψ_da : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      HasDerivAt ψ (fderiv ℝ f (x + t • w) w - ci - (↑L : ℝ) * t * cn) t := by
    intro t ht
    have h1 := hfp_da t ht
    have h2 : HasDerivAt (fun _ : ℝ => f x) 0 t := hasDerivAt_const t (f x)
    have h3 : HasDerivAt (fun s : ℝ => s * ci) ci t := by
      have := (hasDerivAt_id t).mul_const ci; simp only [one_mul] at this; exact this
    have h4 : HasDerivAt (fun s : ℝ => (↑L : ℝ) / 2 * s ^ 2 * cn)
        ((↑L : ℝ) * t * cn) t := by
      have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        have h := hasDerivAt_pow 2 t
        norm_num at h; exact h
      have h := ((hasDerivAt_const t ((↑L : ℝ) / 2)).mul hpow).mul_const cn
      simp only [zero_mul, zero_add] at h
      convert h using 1
      · rfl
      · rfl
      · simp_all
      · ring
    have h_comb := ((h1.sub h2).sub h3).sub h4
    simp only [sub_zero] at h_comb
    convert h_comb using 1
    · rfl
    · rfl
    · funext s
      simp [ψ]
  -- ψ continuous on [0,1]
  have hψ_cont : ContinuousOn ψ (Set.Icc 0 1) := by
    intro t ht
    exact (hψ_da t ht).continuousAt.continuousWithinAt
  -- ψ differentiable on interior [0,1]
  have hψ_diff : DifferentiableOn ℝ ψ (interior (Set.Icc 0 1)) := by
    rw [interior_Icc]; intro t ht
    exact (hψ_da t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
  -- Key: deriv ψ t ≤ 0 on (0,1)
  have hψ'_le : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), deriv ψ t ≤ 0 := by
    intro t ht; rw [interior_Icc] at ht
    rw [(hψ_da t (Set.Ioo_subset_Icc_self ht)).deriv]
    -- Convert fderiv to inner product
    have ht_seg := hseg_V t ht.1.le ht.2.le
    have hfd : fderiv ℝ f (x + t • w) w =
        @inner ℝ _ _ (gradient f (x + t • w)) w :=
      (inner_gradient_left (𝕜 := ℝ) (f := f) (x := x + t • w) (y := w)).symm
    -- Cauchy-Schwarz
    have hCS := real_inner_le_norm (gradient f (x + t • w) - gradient f x) w
    -- inner_sub_left
    have hsub : @inner ℝ _ _ (gradient f (x + t • w) - gradient f x) w =
        @inner ℝ _ _ (gradient f (x + t • w)) w -
        @inner ℝ _ _ (gradient f x) w := inner_sub_left _ _ _
    -- Lipschitz bound (with membership proofs)
    have hLip := hf_lip.dist_le_mul (x + t • w) ht_seg x hx_V
    rw [dist_eq_norm, dist_eq_norm,
      show (x + t • w) - x = t • w from by abel,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hLip
    -- Combined bound: ⟨diff, w⟩ ≤ L * t * ‖w‖²
    have hbd : @inner ℝ _ _ (gradient f (x + t • w) - gradient f x) w ≤
        (↑L : ℝ) * t * cn := by
      calc @inner ℝ _ _ (gradient f (x + t • w) - gradient f x) w
          ≤ ‖gradient f (x + t • w) - gradient f x‖ * ‖w‖ := hCS
        _ ≤ (↑L : ℝ) * (t * ‖w‖) * ‖w‖ :=
            mul_le_mul_of_nonneg_right hLip (norm_nonneg _)
        _ = (↑L : ℝ) * t * cn := by simp only [cn]; ring
    -- Conclude: the deriv ≤ 0
    rw [hfd]; linarith [hsub, hbd]
  -- Apply antitoneOn_of_deriv_nonpos
  have hψ_anti : AntitoneOn ψ (Set.Icc 0 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hψ_cont hψ_diff hψ'_le
  have h_le := hψ_anti (Set.left_mem_Icc.mpr zero_le_one)
    (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  linarith [hψ0]

-- Descent lemma involves segment + Lipschitz elaboration
/-- L-smooth descent: f(x - η·∇f(x)) ≤ f(x) - (η/2)·‖∇f(x)‖² when η = 1/L
    and the gradient of f is L-Lipschitz. Combines the quadratic upper bound
    from L-smoothness with the arithmetic simplification (descent_lemma). -/
theorem lsmooth_descent_at {d : ℕ} (f : E d → ℝ) (L : ℝ≥0)
    (hL : 0 < (L : ℝ))
    {V : Set (E d)} (hV : IsOpen V)
    (hf_diff : DifferentiableOn ℝ f V)
    (hf_lip : LipschitzOnWith L (gradient f) V)
    (x : E d) (hx_V : x ∈ V)
    (hseg_V : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → x + t • (-(((1 : ℝ) / (L : ℝ)) • gradient f x)) ∈ V)
    (η : ℝ) (hη : η = 1 / (L : ℝ)) :
    f (x - η • gradient f x) ≤ f x - η / 2 * ‖gradient f x‖ ^ 2 := by
  -- Use the standalone QUB lemma
  have h_upper : f (x - η • gradient f x) ≤
      f x - η * ‖gradient f x‖ ^ 2 +
      (↑L : ℝ) / 2 * η ^ 2 * ‖gradient f x‖ ^ 2 := by
    set g := gradient f x
    set nw : E d := -(η • g)
    have hinner : @inner ℝ _ _ g nw = -(η * ‖g‖ ^ 2) := by
      simp only [nw, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hnorm_sq : ‖nw‖ ^ 2 = η ^ 2 * ‖g‖ ^ 2 := by
      rw [show nw = -(η • g) from rfl, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hxnw : x - η • g = x + nw := by simp only [sub_eq_add_neg, show nw = -(η • g) from rfl]
    rw [hxnw]
    have h_qub := lsmooth_qub f L hV hf_diff hf_lip x nw hx_V (by
      intro t ht0 ht1
      have : nw = -(η • gradient f x) := rfl
      rw [this, hη]
      exact hseg_V t ht0 ht1)
    rw [hinner, hnorm_sq] at h_qub; linarith
  -- Arithmetic: with η = 1/L, (L/2)η² = η/2
  have key : (↑L : ℝ) / 2 * η ^ 2 = η / 2 := by
    rw [hη]; field_simp [ne_of_gt hL]
  calc f (x - η • gradient f x)
      ≤ f x - η * ‖gradient f x‖ ^ 2 +
        (↑L : ℝ) / 2 * η ^ 2 * ‖gradient f x‖ ^ 2 := h_upper
    _ = f x - η * ‖gradient f x‖ ^ 2 +
        η / 2 * ‖gradient f x‖ ^ 2 := by rw [key]
    _ = f x - η / 2 * ‖gradient f x‖ ^ 2 := by ring

end PLAcceleratedNesterovLean
