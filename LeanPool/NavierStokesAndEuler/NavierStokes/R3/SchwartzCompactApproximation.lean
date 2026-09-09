/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactSchwartz
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonCutoffs

@[expose] public section

/-!
# Compact support approximation in Schwartz space

Multiplying a Schwartz function by the fixed smooth cutoff at radius R gives a
compactly supported Schwartz function. Each seminorm of its error is bounded
by a fixed constant divided by R. Consequently compactly supported Schwartz
functions are dense, and continuous identities extend from compact tests.
-/


noncomputable section


open Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace NavierStokesR3.SchwartzCompactApproximation

open ProblemStatement ComparisonCutoffs

/-- Multiplication by a compactly supported smooth cutoff. -/
def truncate (ψ : SchwartzMap Space ℂ) (R : ℝ) (hR : 0 < R) : SchwartzMap Space ℂ :=
  CompactSchwartz.ofCompactSupport (fun x => cutoff R x • ψ x)
    ((cutoff_smooth R).smul (ψ.smooth ⊤))
    (cutoff_hasCompactSupport hR).smul_right

@[simp] theorem truncate_apply (ψ : SchwartzMap Space ℂ) (R : ℝ) (hR : 0 < R)
    (x : Space) : truncate ψ R hR x = cutoff R x • ψ x := rfl

theorem truncate_hasCompactSupport (ψ : SchwartzMap Space ℂ) (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (truncate ψ R hR : Space → ℂ) := by
  change HasCompactSupport (fun x => cutoff R x • ψ x)
  exact (cutoff_hasCompactSupport hR).smul_right

/-- One extra power in a Schwartz seminorm gives a uniform tail estimate. -/
theorem weighted_tail_le (ψ : SchwartzMap Space ℂ) {R : ℝ} (hR : 0 < R)
    (k m : ℕ) {x : Space} (hx : R ≤ ‖x‖) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ m ψ x‖ ≤
      SchwartzMap.seminorm ℂ (k + 1) m ψ / R := by
  apply (le_div_iff₀ hR).2
  calc
    (‖x‖ ^ k * ‖iteratedFDeriv ℝ m ψ x‖) * R
        ≤ (‖x‖ ^ k * ‖iteratedFDeriv ℝ m ψ x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ m ψ x‖ := by rw [pow_succ]; ring
    _ ≤ SchwartzMap.seminorm ℂ (k + 1) m ψ :=
      SchwartzMap.le_seminorm ℂ (k + 1) m ψ x

/-- All derivatives of the cutoffs are bounded uniformly for radii at least one. -/
theorem uniform_cutoff_derivative_bound {R : ℝ} (hR : 0 < R) (hRone : 1 ≤ R)
    (m : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ m (cutoff R) x‖ ≤ derivativeConstant m := by
  refine (cutoff_iteratedFDeriv_le hR m x).trans ?_
  apply (div_le_iff₀ (pow_pos hR m)).2
  calc
    derivativeConstant m = derivativeConstant m * 1 := by ring
    _ ≤ derivativeConstant m * R ^ m :=
      mul_le_mul_of_nonneg_left (one_le_pow₀ hRone) (derivativeConstant_pos m).le

/-- The fixed constant in the product's weighted tail estimate. -/
def productTailBound (ψ : SchwartzMap Space ℂ) (k m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * derivativeConstant i *
    SchwartzMap.seminorm ℂ (k + 1) (m - i) ψ

theorem productTailBound_nonneg (ψ : SchwartzMap Space ℂ) (k m : ℕ) :
    0 ≤ productTailBound ψ k m := by
  unfold productTailBound
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (derivativeConstant_pos i).le)
      (apply_nonneg _ _)

/-- The fixed constant controlling the cutoff error. -/
def errorTailBound (ψ : SchwartzMap Space ℂ) (k m : ℕ) : ℝ :=
  productTailBound ψ k m + SchwartzMap.seminorm ℂ (k + 1) m ψ

theorem errorTailBound_nonneg (ψ : SchwartzMap Space ℂ) (k m : ℕ) :
    0 ≤ errorTailBound ψ k m :=
  add_nonneg (productTailBound_nonneg ψ k m) (apply_nonneg _ _)

/-- The Leibniz estimate for the cutoff product on the spatial tail. -/
theorem truncate_weighted_derivative_le (ψ : SchwartzMap Space ℂ) {R : ℝ}
    (hR : 0 < R) (hRone : 1 ≤ R) (k m : ℕ) {x : Space} (hx : R ≤ ‖x‖) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (truncate ψ R hR) x‖ ≤
      productTailBound ψ k m / R := by
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun y => cutoff R y • ψ y) x‖ ≤ _
  calc
    _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutoff R) x‖ *
          ‖iteratedFDeriv ℝ (m - i) ψ x‖ :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_smul_le (n := m) (cutoff_smooth R) (ψ.smooth ⊤) x
          (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)))
        (by positivity)
    _ = ∑ i ∈ Finset.range (m + 1),
        ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutoff R) x‖) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (m - i) ψ x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ Finset.range (m + 1),
        ((m.choose i : ℝ) * derivativeConstant i) *
          (SchwartzMap.seminorm ℂ (k + 1) (m - i) ψ / R) := by
      apply Finset.sum_le_sum
      intro i hi
      have hcoeff : (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutoff R) x‖ ≤
          (m.choose i : ℝ) * derivativeConstant i :=
        mul_le_mul_of_nonneg_left (uniform_cutoff_derivative_bound hR hRone i x)
          (by positivity)
      exact mul_le_mul hcoeff (weighted_tail_le ψ hR k (m - i) hx) (by positivity)
        (mul_nonneg (Nat.cast_nonneg _) (derivativeConstant_pos i).le)
    _ = productTailBound ψ k m / R := by
      simp only [productTailBound, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The cutoff error vanishes locally inside the plateau and is small outside it. -/
theorem truncate_error_weighted_le (ψ : SchwartzMap Space ℂ) {R : ℝ}
    (hR : 0 < R) (hRone : 1 ≤ R) (k m : ℕ) (x : Space) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (truncate ψ R hR - ψ) x‖ ≤
      errorTailBound ψ k m / R := by
  change ‖x‖ ^ k *
    ‖iteratedFDeriv ℝ m (fun y => truncate ψ R hR y - ψ y) x‖ ≤ _
  by_cases hx : ‖x‖ < R
  · have hmem : {y : Space | ‖y‖ < R} ∈ 𝓝 x :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hx
    have heq : (fun y => truncate ψ R hR y - ψ y) =ᶠ[𝓝 x]
        (fun _ : Space => (0 : ℂ)) := by
      filter_upwards [hmem] with y hy
      simp only [truncate_apply, cutoff_eq_one hR hy.le, one_smul, sub_self]
    have heqWithin : (fun y => truncate ψ R hR y - ψ y) =ᶠ[𝓝[Set.univ] x]
        (fun _ : Space => (0 : ℂ)) := by
      simpa only [nhdsWithin_univ] using heq
    have hder : iteratedFDeriv ℝ m (fun y => truncate ψ R hR y - ψ y) x = 0 := by
      simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero, Pi.zero_apply]
        using (heqWithin.iteratedFDerivWithin_eq (𝕜 := ℝ) heq.self_of_nhds m)
    rw [hder, norm_zero, mul_zero]
    exact div_nonneg (errorTailBound_nonneg ψ k m) hR.le
  · have hx' : R ≤ ‖x‖ := le_of_not_gt hx
    have hfun : (fun y => truncate ψ R hR y - ψ y) =
        ((truncate ψ R hR : Space → ℂ) + ((-ψ : SchwartzMap Space ℂ) : Space → ℂ)) := by
      funext y
      change truncate ψ R hR y - ψ y = truncate ψ R hR y + -(ψ y)
      exact sub_eq_add_neg _ _
    rw [hfun]
    calc
      _ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (truncate ψ R hR) x‖ +
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (-ψ : SchwartzMap Space ℂ) x‖ :=
        by
          rw [← mul_add]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [iteratedFDeriv_add_apply ((truncate ψ R hR).smooth _).contDiffAt ((-ψ).smooth
            _).contDiffAt]
          exact norm_add_le _ _
      _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (truncate ψ R hR) x‖ +
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ m ψ x‖ := by
        exact congrArg
          (fun z : ℝ => ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (truncate ψ R hR) x‖ + z)
          (by change ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (-(ψ : Space → ℂ)) x‖ = _; rw
            [iteratedFDeriv_neg_apply, norm_neg])
      _ ≤ productTailBound ψ k m / R + SchwartzMap.seminorm ℂ (k + 1) m ψ / R :=
        add_le_add (truncate_weighted_derivative_le ψ hR hRone k m hx')
          (weighted_tail_le ψ hR k m hx')
      _ = errorTailBound ψ k m / R := by rw [errorTailBound, add_div]

/-- Every Schwartz seminorm of the cutoff error tends to zero at rate 1/R. -/
theorem seminorm_truncate_sub_le (ψ : SchwartzMap Space ℂ) {R : ℝ}
    (hR : 0 < R) (hRone : 1 ≤ R) (k m : ℕ) :
    SchwartzMap.seminorm ℂ k m (truncate ψ R hR - ψ) ≤ errorTailBound ψ k m / R := by
  apply SchwartzMap.seminorm_le_bound ℂ k m _
    (div_nonneg (errorTailBound_nonneg ψ k m) hR.le)
  exact truncate_error_weighted_le ψ hR hRone k m

/-- A sequence of compactly supported smooth approximations. -/
def approximate (ψ : SchwartzMap Space ℂ) (n : ℕ) : SchwartzMap Space ℂ :=
  truncate ψ ((n : ℝ) + 1) (by positivity)

@[simp] theorem approximate_apply (ψ : SchwartzMap Space ℂ) (n : ℕ) (x : Space) :
    approximate ψ n x = cutoff ((n : ℝ) + 1) x • ψ x := rfl

theorem approximate_hasCompactSupport (ψ : SchwartzMap Space ℂ) (n : ℕ) :
    HasCompactSupport (approximate ψ n : Space → ℂ) :=
  truncate_hasCompactSupport ψ _ _

/-- The cutoff approximations converge in the full Schwartz topology. -/
theorem tendsto_approximate (ψ : SchwartzMap Space ℂ) :
    Tendsto (approximate ψ) atTop (𝓝 ψ) := by
  apply ((schwartz_withSeminorms ℂ Space ℂ).tendsto_nhds_atTop (approximate ψ) ψ).2
  rintro ⟨k, m⟩ ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (errorTailBound ψ k m / ε)
  refine ⟨N, fun n hn => ?_⟩
  change SchwartzMap.seminorm ℂ k m (approximate ψ n - ψ) < ε
  have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hRone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  refine (seminorm_truncate_sub_le ψ hR hRone k m).trans_lt ?_
  apply (div_lt_iff₀ hR).2
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlarge : errorTailBound ψ k m / ε < (n : ℝ) + 1 := by linarith
  simpa [mul_comm] using (div_lt_iff₀ hε).1 hlarge

/-- Compactly supported smooth tests are dense in Schwartz space. -/
theorem dense_hasCompactSupport :
    Dense {ψ : SchwartzMap Space ℂ | HasCompactSupport (ψ : Space → ℂ)} := by
  intro ψ
  exact mem_closure_of_tendsto (tendsto_approximate ψ)
    (Filter.Eventually.of_forall fun n => approximate_hasCompactSupport ψ n)

/-- A continuous functional vanishing on compact tests vanishes on every Schwartz test. -/
theorem continuous_zero_of_compactSupport (F : SchwartzMap Space ℂ → ℂ)
    (hF : Continuous F)
    (hzero : ∀ ψ : SchwartzMap Space ℂ, HasCompactSupport (ψ : Space → ℂ) → F ψ = 0)
    (ψ : SchwartzMap Space ℂ) : F ψ = 0 := by
  have hlim : Tendsto (fun n : ℕ => F (approximate ψ n)) atTop (𝓝 (F ψ)) :=
    (hF.tendsto ψ).comp (tendsto_approximate ψ)
  have hz : (fun n : ℕ => F (approximate ψ n)) = (fun _ : ℕ => (0 : ℂ)) :=
    funext fun n => hzero _ (approximate_hasCompactSupport ψ n)
  rw [hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- The continuous linear form version of compact-test extension. -/
theorem eq_zero_of_compactSupport (F : SchwartzMap Space ℂ →L[ℂ] ℂ)
    (hzero : ∀ ψ : SchwartzMap Space ℂ, HasCompactSupport (ψ : Space → ℂ) → F ψ = 0)
    (ψ : SchwartzMap Space ℂ) : F ψ = 0 :=
  continuous_zero_of_compactSupport F F.continuous hzero ψ

/-- In particular, an identity tested after a continuous differential operator extends. -/
theorem comp_eq_zero_of_compactSupport
    (F : SchwartzMap Space ℂ →L[ℂ] ℂ)
    (L : SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ)
    (hzero : ∀ ψ : SchwartzMap Space ℂ,
      HasCompactSupport (ψ : Space → ℂ) → F (L ψ) = 0)
    (ψ : SchwartzMap Space ℂ) : F (L ψ) = 0 :=
  eq_zero_of_compactSupport (F.comp L) hzero ψ

end NavierStokesR3.SchwartzCompactApproximation
