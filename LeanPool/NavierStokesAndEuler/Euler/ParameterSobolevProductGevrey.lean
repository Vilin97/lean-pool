/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
public import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus

@[expose] public section

/-!
# Multiplication preserves the radius of genuine fixed-Sobolev word blocks

Only coefficient blocks are compared with the coefficient radius. The input
field's ordered word sum passes directly through the Leibniz estimate.
-/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap EulerGevrey EulerOperatorGevreyCalculus
open scoped ContDiff

variable {P E F ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

theorem block_clm_apply_gevrey (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] F) (f : P → E)
    (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f)
    (Rc R C D : ℝ) (hRc : 0 ≤ Rc) (hRcR : Rc ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcoeff : ∀ n x, coefficientBlock directions q A n x ≤ C*majorant Rc 0 n)
    (d : ℕ) (hfield : ∀ n x, block directions q f n x ≤ D*majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (fun y => A y (f y)) n x ≤ (3*C*D)*majorant R d n := by
  have hR : 0 ≤ R := hRc.trans hRcR
  have hc (k : ℕ) : |coefficientBlock directions q A k x| ≤ C*majorant R 0 k := by
    rw [abs_of_nonneg (coefficientBlock_nonneg directions q A k x)]
    exact (hcoeff k x).trans (mul_le_mul_of_nonneg_left
      (majorant_radius_mono Rc R hRc hRcR 0 k) hC)
  have hf' (k : ℕ) : |block directions q f k x| ≤ D*majorant R d k := by
    rw [abs_of_nonneg (block_nonneg directions q f k x)]
    exact hfield k x
  have hp := sequence_product_majorant R C D hR hC hD 0 d
    (fun k => coefficientBlock directions q A k x)
    (fun k => block directions q f k x) hc hf' n
  exact (block_clm_apply_le directions q A f hA hf n x).trans
    ((le_abs_self _).trans (by simpa only [Nat.zero_add, EulerJetProductBounds.leibnizConvolution]
      using hp))

theorem block_linear_gevrey (directions : ι → P) (q : ℕ)
    (L : E →L[ℝ] F) (f : P → E) (hf : ContDiff ℝ ∞ f)
    (R C : ℝ) (d : ℕ) (hb : ∀ n x, block directions q f n x ≤ C*majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (fun y => L (f y)) n x ≤ (‖L‖*C)*majorant R d n :=
  (block_comp_clm_le directions q L f hf n x).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb n x) (norm_nonneg L))

theorem block_add_gevrey (directions : ι → P) (q : ℕ)
    (f g : P → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (R C D : ℝ) (d : ℕ)
    (hb : ∀ n x, block directions q f n x ≤ C*majorant R d n)
    (hc : ∀ n x, block directions q g n x ≤ D*majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (f+g) n x ≤ (C+D)*majorant R d n :=
  (block_add_le directions q f g hf hg n x).trans
    (by simpa only [add_mul] using add_le_add (hb n x) (hc n x))

end EulerParameterWordGevrey
