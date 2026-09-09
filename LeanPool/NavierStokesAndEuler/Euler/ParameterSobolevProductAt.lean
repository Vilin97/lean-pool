/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevProductGevrey

@[expose] public section

/-! The same-radius fixed-Sobolev product estimate needs bounds only at the base parameter. -/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap EulerGevrey EulerOperatorGevreyCalculus
open scoped ContDiff

variable {P E F ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- A frozen-parameter product estimate. The field radius is unchanged. -/
theorem block_clm_apply_gevrey_at (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] F) (f : P → E)
    (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f) (x : P)
    (Rc R C D : ℝ) (hRc : 0 ≤ Rc) (hRcR : Rc ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcoeff : ∀ n, coefficientBlock directions q A n x ≤ C*majorant Rc 0 n)
    (d : ℕ) (hfield : ∀ n, block directions q f n x ≤ D*majorant R d n)
    (n : ℕ) :
    block directions q (fun y => A y (f y)) n x ≤ (3*C*D)*majorant R d n := by
  have hR : 0 ≤ R := hRc.trans hRcR
  have hc (k : ℕ) : |coefficientBlock directions q A k x| ≤ C*majorant R 0 k := by
    rw [abs_of_nonneg (coefficientBlock_nonneg directions q A k x)]
    exact (hcoeff k).trans (mul_le_mul_of_nonneg_left
      (majorant_radius_mono Rc R hRc hRcR 0 k) hC)
  have hf' (k : ℕ) : |block directions q f k x| ≤ D*majorant R d k := by
    rw [abs_of_nonneg (block_nonneg directions q f k x)]
    exact hfield k
  have hp := sequence_product_majorant R C D hR hC hD 0 d
    (fun k => coefficientBlock directions q A k x)
    (fun k => block directions q f k x) hc hf' n
  exact (block_clm_apply_le directions q A f hA hf n x).trans
    ((le_abs_self _).trans (by simpa only [Nat.zero_add, EulerJetProductBounds.leibnizConvolution]
      using hp))

end EulerParameterWordGevrey
