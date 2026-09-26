/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.CapacityOrder
public import Mathlib.Tactic

/-! # Capacity Scaling -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

open MvPolynomial

theorem realMonomial_pointwise_mul
    {σ : Type*} [Fintype σ]
    (c z α : σ → ℝ) (hc : ∀ i, 0 ≤ c i) (hz : ∀ i, 0 ≤ z i) :
    realMonomial (fun i ↦ c i * z i) α =
      realMonomial c α * realMonomial z α := by
  rw [realMonomial, realMonomial, realMonomial,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.mul_rpow (hc i) (hz i)

theorem rescaled_polynomial_ratio_eq
    {σ : Type*} [Fintype σ]
    {p q : MvPolynomial σ ℝ} {α c z : σ → ℝ} {scale : ℝ}
    (hc : ∀ i, 0 < c i) (hz : ∀ i, 0 < z i)
    (heval : ∀ w : σ → ℝ,
      p.eval w = scale * q.eval (fun i ↦ c i * w i)) :
    p.eval z / realMonomial z α =
      (scale * realMonomial c α) *
        (q.eval (fun i ↦ c i * z i) /
          realMonomial (fun i ↦ c i * z i) α) := by
  have hcz : realMonomial (fun i ↦ c i * z i) α =
      realMonomial c α * realMonomial z α :=
    realMonomial_pointwise_mul c z α
      (fun i ↦ (hc i).le) (fun i ↦ (hz i).le)
  rw [heval, hcz]
  field_simp [ne_of_gt (realMonomial_pos hc α),
    ne_of_gt (realMonomial_pos hz α)]

/-- Capacity is covariant under a positive scalar and a positive diagonal
change of variables.  This is the exact rescaling used in paper Lemma 18. -/
theorem polynomialCapacity_eq_of_positive_diagonal_rescaling
    {σ : Type*} [Fintype σ]
    {p q : MvPolynomial σ ℝ} {α c : σ → ℝ} {scale : ℝ}
    (hp : HasNonnegativeCoefficients p)
    (hq : HasNonnegativeCoefficients q)
    (hscale : 0 < scale) (hc : ∀ i, 0 < c i)
    (heval : ∀ z : σ → ℝ,
      p.eval z = scale * q.eval (fun i ↦ c i * z i)) :
    polynomialCapacity α p =
      (scale * realMonomial c α) * polynomialCapacity α q := by
  let k : ℝ := scale * realMonomial c α
  have hk : 0 < k := mul_pos hscale (realMonomial_pos hc α)
  apply le_antisymm
  · have hdiv : polynomialCapacity α p / k ≤
        polynomialCapacity α q := by
      apply le_polynomialCapacity_of_le_ratio
      intro w hw
      let z : σ → ℝ := fun i ↦ w i / c i
      have hz : ∀ i, 0 < z i := fun i ↦ div_pos (hw i) (hc i)
      have hcz : (fun i ↦ c i * z i) = w := by
        funext i
        dsimp [z]
        field_simp [ne_of_gt (hc i)]
      have hratio := rescaled_polynomial_ratio_eq (α := α) hc hz heval
      rw [hcz] at hratio
      have hupper := polynomialCapacity_le_ratio hp α z hz
      rw [hratio] at hupper
      exact (div_le_iff₀ hk).2 (by simpa [k, mul_comm] using hupper)
    simpa [k, mul_comm] using (div_le_iff₀ hk).1 hdiv
  · apply le_polynomialCapacity_of_le_ratio
    intro z hz
    let w : σ → ℝ := fun i ↦ c i * z i
    have hw : ∀ i, 0 < w i := fun i ↦ mul_pos (hc i) (hz i)
    have hlower := polynomialCapacity_le_ratio hq α w hw
    have hratio := rescaled_polynomial_ratio_eq (α := α) hc hz heval
    rw [hratio]
    exact mul_le_mul_of_nonneg_left hlower hk.le

end BeyondBethe
