/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-! Finite-dimensional cancellation at the end of Schur's proof.
This is an algebra helper, not a replacement for geometric contracted Bianchi. -/

@[expose] public noncomputable section

open scoped BigOperators

namespace SchurRigidity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι]

/-- The derivative of the Gram matrix cancels the two moving-frame terms in a
metric contraction. The frame velocity is arbitrary, not assumed skew. -/
theorem gram_frame_correction
    (e : OrthonormalBasis ι ℝ V) (A : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (q : ι → V) :
    (∑ i, ∑ j, (inner ℝ (q i) (e j) + inner ℝ (e i) (q j)) * A (e i) (e j)) =
      (∑ i, A (q i) (e i)) + ∑ i, A (e i) (q i) := by
  have hL (i : ι) : A (q i) (e i) =
      ∑ j, inner ℝ (e j) (q i) * A (e j) (e i) := by
    conv_lhs => rw [← e.sum_repr' (q i)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hR (i : ι) : A (e i) (q i) =
      ∑ j, inner ℝ (e j) (q i) * A (e i) (e j) := by
    conv_lhs => rw [← e.sum_repr' (q i)]
    simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [hL, hR, add_mul]
  rw [Finset.sum_comm (f := fun i j ↦ inner ℝ (e j) (q i) * A (e j) (e i))]
  simp only [Finset.sum_add_distrib, real_inner_comm (q _) (e _)]
  exact add_comm _ _

theorem differential_eq_zero_of_contraction
    (e : OrthonormalBasis ι ℝ V) (d : V →ₗ[ℝ] ℝ)
    (hn : 3 ≤ Fintype.card ι)
    (h : ∀ w : V,
      (∑ i, d w * inner ℝ (e i) (e i)) =
        2 * ∑ i, d (e i) * inner ℝ (e i) w) : d = 0 := by
  classical
  ext w
  have hs : (∑ i, d (e i) * inner ℝ (e i) w) = d w := by
    have he := congrArg d (e.sum_repr' w)
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using he
  have hc := h w
  simp only [e.inner_eq_ite, ite_true, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hs] at hc
  have hn' : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  change d w = 0
  nlinarith

end SchurRigidity
