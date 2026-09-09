/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyComposition
public import LeanPool.NavierStokesAndEuler.Euler.GevreyInversePartitions

@[expose] public section

/-!
# Gevrey bounds from the actual inverse-map differential identity

If `DY = A ∘ Y` and `A` has Gevrey-two derivatives, the positive derivatives
of `Y` have the stronger bound `C * L^n * n!²` at order `n+1`, where
`L = 1 + 2*C*R`.  The proof uses the shifted Faà di Bruno weights and a
strong induction, rather than iterating the general composition radius.
-/

noncomputable section

open scoped BigOperators ContDiff

namespace EulerGevreyComposition

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma predecessor_partition_bound_factorization {n : ℕ} (c : OrderedFinpartition n)
    (A B R S : ℝ) :
    (A * S^c.length * (c.length.factorial : ℝ)^2) *
        (∏ i, B * R^(c.partSize i) * ((c.partSize i - 1).factorial : ℝ)^2) =
      A * R^n * predecessorPartitionWeight (B*S) c := by
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow_eq_pow_sum, sum_partSize, Finset.prod_pow]
  unfold predecessorPartitionWeight predecessorFactorialProduct
  rw [mul_pow]
  ring

theorem norm_taylorComp_predecessor_le
    (q : FormalMultilinearSeries ℝ F G) (p : FormalMultilinearSeries ℝ E F)
    (n : ℕ) (hn : 0 < n) (A B R S : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S) (hBS : B*S ≤ 1/2)
    (hq : ∀ j ≤ n, ‖q j‖ ≤ A * S^j * (j.factorial : ℝ)^2)
    (hp : ∀ j, 0 < j → j ≤ n →
      ‖p j‖ ≤ B * R^j * ((j-1).factorial : ℝ)^2) :
    ‖q.taylorComp p n‖ ≤ A * R^n * (B*S) * (n.factorial : ℝ)^2 := by
  have hterm (c : OrderedFinpartition n) :
      ‖q.compAlongOrderedFinpartition p c‖ ≤
        A * R^n * predecessorPartitionWeight (B*S) c := by
    calc
      _ ≤ ‖q c.length‖ * ∏ i, ‖p (c.partSize i)‖ :=
        c.norm_compAlongOrderedFinpartition_le _ _
      _ ≤ (A * S^c.length * (c.length.factorial : ℝ)^2) *
          (∏ i, B * R^(c.partSize i) * ((c.partSize i-1).factorial : ℝ)^2) := by
        apply mul_le_mul (hq _ c.length_le)
        · apply Finset.prod_le_prod
          · intro i _
            exact norm_nonneg _
          · intro i _
            exact hp _ (c.partSize_pos i) (c.partSize_le i)
        · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
        · positivity
      _ = _ := predecessor_partition_bound_factorization c A B R S
  calc
    _ ≤ ∑ c : OrderedFinpartition n, ‖q.compAlongOrderedFinpartition p c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition n, A * R^n * predecessorPartitionWeight (B*S) c :=
      Finset.sum_le_sum (fun c _ => hterm c)
    _ = A * R^n * predecessorPartitionSum n (B*S) := by
      rw [predecessorPartitionSum, Finset.mul_sum]
    _ ≤ A * R^n * ((B*S) * (n.factorial : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (predecessorPartitionSum_le n hn (B*S)
        (mul_nonneg hB hS) hBS) (mul_nonneg hA (pow_nonneg hR n))
    _ = _ := by ring

theorem norm_iteratedFDeriv_comp_predecessor_at
    (f : E → F) (g : F → G) (n : ℕ) (hn : 0 < n) (x : E)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g (f x))
    (A B R S : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hBS : B*S ≤ 1/2)
    (hgjet : ∀ j ≤ n,
      ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A * S^j * (j.factorial : ℝ)^2)
    (hfjet : ∀ j, 0 < j → j ≤ n →
      ‖iteratedFDeriv ℝ j f x‖ ≤ B * R^j * ((j-1).factorial : ℝ)^2) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ A * R^n * (B*S) * (n.factorial : ℝ)^2 := by
  rw [iteratedFDeriv_comp hg hf le_rfl]
  exact norm_taylorComp_predecessor_le (ftaylorSeries ℝ g (f x))
    (ftaylorSeries ℝ f x) n hn A B R S hA hB hR hS hBS hgjet hfjet

def inverseMapRadius (C R : ℝ) : ℝ := 1 + 2*C*R

lemma inverseMapRadius_ge_one (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    1 ≤ inverseMapRadius C R := by
  unfold inverseMapRadius
  nlinarith [mul_nonneg hC hR]

lemma inverseMapRadius_pos (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 < inverseMapRadius C R := lt_of_lt_of_le zero_lt_one (inverseMapRadius_ge_one C R hC hR)

/-- Positive derivatives of a genuine solution of `DY = A ∘ Y` have one
fixed polynomial Gevrey radius.  The value of `Y` need not be bounded. -/
theorem norm_iteratedFDeriv_of_fderiv_eq_comp
    (Y : E → F) (A : F → E →L[ℝ] F)
    (hY : ContDiff ℝ ∞ Y) (hA : ContDiff ℝ ∞ A)
    (hDY : ∀ x, fderiv ℝ Y x = A (Y x))
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hAjet : ∀ j y, ‖iteratedFDeriv ℝ j A y‖ ≤ C * R^j * (j.factorial : ℝ)^2)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ (n+1) Y x‖ ≤
      C * (inverseMapRadius C R)^n * (n.factorial : ℝ)^2 := by
  let L := inverseMapRadius C R
  have hL : 0 < L := inverseMapRadius_pos C R hC hR
  have hCL : 0 ≤ C/L := div_nonneg hC hL.le
  have hhalf : (C/L)*R ≤ 1/2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    dsimp [L, inverseMapRadius]
    nlinarith
  change ‖iteratedFDeriv ℝ (n+1) Y x‖ ≤ C * L^n * (n.factorial : ℝ)^2
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      change ‖iteratedFDeriv ℝ 1 Y x‖ ≤ C * L^0 * (Nat.factorial 0 : ℝ)^2
      rw [norm_iteratedFDeriv_one, hDY]
      simpa only [norm_iteratedFDeriv_zero, pow_zero, Nat.factorial_zero,
        Nat.cast_one, one_pow, mul_one] using hAjet 0 (Y x)
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hinner (j : ℕ) (hj : 0 < j) (hjn : j ≤ n) :
          ‖iteratedFDeriv ℝ j Y x‖ ≤ (C/L) * L^j * ((j-1).factorial : ℝ)^2 := by
        have hh := ih (j-1) (by omega) x
        rw [Nat.sub_add_cancel hj] at hh
        have hp : L^j = L^(j-1)*L := by
          conv_lhs => rw [← Nat.sub_add_cancel hj]
          rw [pow_succ]
        apply hh.trans_eq
        rw [hp]
        field_simp
      have hc := norm_iteratedFDeriv_comp_predecessor_at Y A n hnpos x
        (hY.contDiffAt.of_le (by simp)) (hA.contDiffAt.of_le (by simp))
        C (C/L) L R hC hCL hL.le hR hhalf (fun j _ => hAjet j (Y x)) hinner
      have hfun : fderiv ℝ Y = A ∘ Y := funext hDY
      calc
        _ = ‖iteratedFDeriv ℝ n (fderiv ℝ Y) x‖ := norm_iteratedFDeriv_fderiv.symm
        _ = ‖iteratedFDeriv ℝ n (A ∘ Y) x‖ := by rw [hfun]
        _ ≤ C * L^n * ((C/L)*R) * (n.factorial : ℝ)^2 := hc
        _ ≤ C * L^n * 1 * (n.factorial : ℝ)^2 := by
          gcongr
          exact hhalf.trans (by norm_num)
        _ = _ := by ring

/-- The same estimate in the usual unshifted form, directly usable as the
inner-function hypothesis of the composition theorem. -/
theorem positive_jets_of_fderiv_eq_comp
    (Y : E → F) (A : F → E →L[ℝ] F)
    (hY : ContDiff ℝ ∞ Y) (hA : ContDiff ℝ ∞ A)
    (hDY : ∀ x, fderiv ℝ Y x = A (Y x))
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hAjet : ∀ j y, ‖iteratedFDeriv ℝ j A y‖ ≤ C * R^j * (j.factorial : ℝ)^2)
    (n : ℕ) (hn : 0 < n) (x : E) :
    ‖iteratedFDeriv ℝ n Y x‖ ≤
      C * (inverseMapRadius C R)^n * (n.factorial : ℝ)^2 := by
  have hh := norm_iteratedFDeriv_of_fderiv_eq_comp Y A hY hA hDY C R hC hR
    hAjet (n-1) x
  rw [Nat.sub_add_cancel hn] at hh
  apply hh.trans
  have hp := pow_le_pow_right₀ (inverseMapRadius_ge_one C R hC hR) (Nat.sub_le n 1)
  have hf : ((n-1).factorial : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.sub_le n 1)
  apply mul_le_mul (mul_le_mul_of_nonneg_left hp hC)
    (pow_le_pow_left₀ (by positivity) hf 2) (by positivity)
  exact mul_nonneg hC (pow_nonneg (inverseMapRadius_pos C R hC hR).le n)

/-- Smoothness itself follows by differentiating the genuine differential
identity; it need not be supplied as an independent inverse-map assumption. -/
theorem contDiff_of_fderiv_eq_comp
    (Y : E → F) (A : F → E →L[ℝ] F)
    (hY : Differentiable ℝ Y) (hA : ContDiff ℝ ∞ A)
    (hDY : ∀ x, fderiv ℝ Y x = A (Y x)) : ContDiff ℝ ∞ Y := by
  apply contDiff_infty.2
  intro n
  induction n with
  | zero => exact contDiff_zero.2 hY.continuous
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiff_succ_iff_fderiv.2
    refine ⟨hY, by simp, ?_⟩
    rw [show fderiv ℝ Y = A ∘ Y from funext hDY]
    exact (hA.of_le (by simp)).comp ih

/-- The differential equation follows from an actual inverse identity and
the actual inverse of the derivative of the original coordinate map. -/
theorem fderiv_eq_inverse_field
    (X Y : E → E) (A : E → E →L[ℝ] E)
    (hX : Differentiable ℝ X) (hY : Differentiable ℝ Y)
    (hXY : ∀ x, X (Y x) = x)
    (hleft : ∀ x v, A x (fderiv ℝ X x v) = v) :
    ∀ x, fderiv ℝ Y x = A (Y x) := by
  intro x
  have hcomp := (hX (Y x)).hasFDerivAt.comp x (hY x).hasFDerivAt
  have hfun : X ∘ Y = id := funext hXY
  rw [hfun] at hcomp
  have he := hcomp.unique (hasFDerivAt_id x)
  ext v
  have hv := congrArg (fun B : E →L[ℝ] E => A (Y x) (B v)) he
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hleft] using hv

/-- Gevrey-two regularity of an actual smooth inverse map with a Gevrey-two
inverse derivative field. -/
theorem norm_iteratedFDeriv_inverseMap
    (X Y : E → E) (A : E → E →L[ℝ] E)
    (hX : Differentiable ℝ X) (hY : ContDiff ℝ ∞ Y) (hA : ContDiff ℝ ∞ A)
    (hXY : ∀ x, X (Y x) = x)
    (hleft : ∀ x v, A x (fderiv ℝ X x v) = v)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hAjet : ∀ j y, ‖iteratedFDeriv ℝ j A y‖ ≤ C * R^j * (j.factorial : ℝ)^2)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ (n+1) Y x‖ ≤
      C * (inverseMapRadius C R)^n * (n.factorial : ℝ)^2 := by
  exact norm_iteratedFDeriv_of_fderiv_eq_comp Y A hY hA
    (fderiv_eq_inverse_field X Y A hX (hY.differentiable (by simp)) hXY hleft)
    C R hC hR hAjet n x

/-- Pullback by a map satisfying the actual inverse differential equation
preserves Gevrey two, with an explicit polynomial radius and unchanged
outer amplitude.  Only differentiability of the inverse is an input. -/
theorem norm_iteratedFDeriv_comp_of_fderiv_eq_comp
    (Y : E → F) (A : F → E →L[ℝ] F) (g : F → G)
    (hY : Differentiable ℝ Y) (hA : ContDiff ℝ ∞ A) (hg : ContDiff ℝ ∞ g)
    (hDY : ∀ x, fderiv ℝ Y x = A (Y x))
    (C R D S : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hAjet : ∀ j y, ‖iteratedFDeriv ℝ j A y‖ ≤ C * R^j * (j.factorial : ℝ)^2)
    (hgjet : ∀ j y, ‖iteratedFDeriv ℝ j g y‖ ≤ D * S^j * (j.factorial : ℝ)^2)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (g ∘ Y) x‖ ≤
      D * (inverseMapRadius C R * (C*S+2))^n * (n.factorial : ℝ)^2 := by
  have hYs := contDiff_of_fderiv_eq_comp Y A hY hA hDY
  exact norm_iteratedFDeriv_comp_gevrey Y g hYs hg
    D C (inverseMapRadius C R) S hD hC (inverseMapRadius_pos C R hC hR).le hS
    hgjet (positive_jets_of_fderiv_eq_comp Y A hYs hA hDY C R hC hR hAjet) n x

end EulerGevreyComposition
