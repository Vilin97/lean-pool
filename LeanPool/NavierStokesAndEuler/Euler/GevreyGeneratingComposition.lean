/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyGeneratingAlgebra
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-! The finite Gevrey-two generating sum obeys an actual composition
estimate.  In contrast to replacing all jets by one order-dependent bound,
this estimate retains the finite sum of the inner derivatives. -/

@[expose] public section


noncomputable section

open scoped BigOperators ContDiff Polynomial

namespace EulerGevreyGeneratingComposition

open EulerGevreyComposition EulerGevreyGeneratingAlgebra

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Comparison with an exact scalar polynomial composition. -/
theorem norm_taylorComp_le_coefficient
    (P : FormalMultilinearSeries ℝ E F) (Q : FormalMultilinearSeries ℝ F G)
    (p q : ℝ[X]) (hp0 : p.coeff 0 = 0)
    (hp : NonnegativeCoefficients p) (hq : NonnegativeCoefficients q)
    (n : ℕ) (hn : 0 < n)
    (hP : ∀ j, 0 < j → j ≤ n → ‖P j‖ ≤ (j.factorial : ℝ) ^ 2 * p.coeff j)
    (hQ : ∀ j, 0 < j → j ≤ n → ‖Q j‖ ≤ (j.factorial : ℝ) ^ 2 * q.coeff j) :
    ‖Q.taylorComp P n‖ ≤ (n.factorial : ℝ)^2*(q.comp p).coeff n := by
  have hc (c : OrderedFinpartition n) :
      ‖Q.compAlongOrderedFinpartition P c‖ ≤ (n.factorial : ℝ) *
        (((c.length.factorial : ℝ)*q.coeff c.length) *
          ∏ i, ((c.partSize i).factorial : ℝ)*p.coeff (c.partSize i)) := by
    calc
      _ ≤ ‖Q c.length‖*∏ i, ‖P (c.partSize i)‖ :=
        c.norm_compAlongOrderedFinpartition_le _ _
      _ ≤ ((c.length.factorial : ℝ)^2*q.coeff c.length) *
          ∏ i, ((c.partSize i).factorial : ℝ)^2*p.coeff (c.partSize i) := by
        apply mul_le_mul (hQ _ (c.length_pos hn) c.length_le)
        · exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
            (fun i _ => hP _ (c.partSize_pos i) (c.partSize_le i))
        · exact Finset.prod_nonneg (fun i _ => norm_nonneg _)
        · exact mul_nonneg (sq_nonneg _) (hq _)
      _ = ((c.length.factorial : ℝ)*factorialProduct c) *
          (((c.length.factorial : ℝ)*q.coeff c.length) *
            ∏ i, ((c.partSize i).factorial : ℝ)*p.coeff (c.partSize i)) := by
        simp only [factorialProduct, Finset.prod_mul_distrib, Finset.prod_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (partition_factorial_le c)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hq _))
          (Finset.prod_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hp _)))
  calc
    _ ≤ ∑ c : OrderedFinpartition n, ‖Q.compAlongOrderedFinpartition P c‖ := norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition n, (n.factorial : ℝ) *
        (((c.length.factorial : ℝ)*q.coeff c.length) *
          ∏ i, ((c.partSize i).factorial : ℝ)*p.coeff (c.partSize i)) :=
      Finset.sum_le_sum fun c _ => hc c
    _ = (n.factorial : ℝ)*((n.factorial : ℝ)*(q.comp p).coeff n) := by
      rw [← Finset.mul_sum, comp_coefficient p q hp0 n]
    _ = _ := by ring

/-- Finite sums are bounded by evaluating the composed nonnegative
polynomial.  No derivative beyond order N occurs. -/
theorem generating_sum_le_polynomial
    (P : FormalMultilinearSeries ℝ E F) (Q : FormalMultilinearSeries ℝ F G)
    (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ j ∈ Finset.Icc 1 N, 0 ≤ a j)
    (hb : ∀ j ∈ Finset.Icc 1 N, 0 ≤ b j)
    (hP : ∀ j ∈ Finset.Icc 1 N, ‖P j‖ ≤ (j.factorial : ℝ) ^ 2 * a j)
    (hQ : ∀ j ∈ Finset.Icc 1 N, ‖Q j‖ ≤ (j.factorial : ℝ) ^ 2 * b j)
    (z : ℝ) (hz : 0 ≤ z) :
    (∑ n ∈ Finset.Icc 1 N, ‖Q.taylorComp P n‖/(n.factorial : ℝ)^2*z^n) ≤
      (jetPolynomial N b).eval ((jetPolynomial N a).eval z) := by
  let p := jetPolynomial N a
  let q := jetPolynomial N b
  have hpc : NonnegativeCoefficients p := jetPolynomial_nonnegative N a ha
  have hqc : NonnegativeCoefficients q := jetPolynomial_nonnegative N b hb
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (q.comp p).coeff n*z^n := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0,hnN⟩ := Finset.mem_Icc.mp hn
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hz n)
      apply (div_le_iff₀ (by positivity : 0 < (n.factorial : ℝ)^2)).2
      have he := norm_taylorComp_le_coefficient P Q p q
        (jetPolynomial_zero N a) hpc hqc n (by omega)
        (fun j hj hjn => by
          have hjN : j ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hj,hjn.trans hnN⟩
          simpa only [p, jetPolynomial_coeff_of_mem N a j hjN] using hP j hjN)
        (fun j hj hjn => by
          have hjN : j ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hj,hjn.trans hnN⟩
          simpa only [q, jetPolynomial_coeff_of_mem N b j hjN] using hQ j hjN)
      simpa only [mul_comm] using he
    _ ≤ (q.comp p).eval z :=
      coefficient_sum_le_eval (q.comp p) (nonnegative_comp hpc hqc) _ z hz
    _ = _ := by simp only [Polynomial.eval_comp, p, q]

/-- Normalized jet, given by `‖P n‖/(n.factorial : ℝ)^2`. -/
def normalizedJet (P : FormalMultilinearSeries ℝ E F) (n : ℕ) : ℝ :=
  ‖P n‖/(n.factorial : ℝ)^2

/-- Generating sum, given by `∑ n ∈ Finset.Icc 1 N, normalizedJet P n*z^n`. -/
def generatingSum (P : FormalMultilinearSeries ℝ E F) (N : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, normalizedJet P n*z^n

theorem generatingSum_nonneg (P : FormalMultilinearSeries ℝ E F)
    (N : ℕ) (z : ℝ) (hz : 0 ≤ z) : 0 ≤ generatingSum P N z :=
  Finset.sum_nonneg fun n _ => mul_nonneg (by unfold normalizedJet; positivity) (pow_nonneg hz n)

/-- The nonlinear generating-function bound needed for the small-flow
bootstrap.  The inner generating sum is retained without a radius loss. -/
theorem generatingSum_taylorComp_le
    (P : FormalMultilinearSeries ℝ E F) (Q : FormalMultilinearSeries ℝ F G)
    (N : ℕ) (B R z : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R) (hz : 0 ≤ z)
    (hQ : ∀ j ∈ Finset.Icc 1 N, ‖Q j‖ ≤ B * R ^ j * (j.factorial : ℝ) ^ 2)
    (hsmall : R * generatingSum P N z < 1) :
    generatingSum (Q.taylorComp P) N z ≤
      B*(R*generatingSum P N z)/(1-R*generatingSum P N z) := by
  have hP (j : ℕ) : ‖P j‖ = (j.factorial : ℝ)^2*normalizedJet P j := by
    unfold normalizedJet
    field_simp
  have hb : ∀ j ∈ Finset.Icc 1 N, 0 ≤ B*R^j :=
    fun j _ => mul_nonneg hB (pow_nonneg hR j)
  have he := generating_sum_le_polynomial P Q N (normalizedJet P) (fun j => B*R^j)
    (fun j _ => by unfold normalizedJet; positivity) hb
    (fun j _ => (hP j).le)
    (fun j hj => by simpa only [mul_comm, mul_left_comm, mul_assoc] using hQ j hj) z hz
  have hg : (jetPolynomial N (normalizedJet P)).eval z = generatingSum P N z :=
    jetPolynomial_eval N (normalizedJet P) z
  change generatingSum (Q.taylorComp P) N z ≤ _ at he
  rw [hg, jetPolynomial_eval] at he
  have hnon : 0 ≤ R*generatingSum P N z :=
    mul_nonneg hR (generatingSum_nonneg P N z hz)
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 1) (n := N+1) hnon hsmall
  have hinterval : Finset.Ico 1 (N+1) = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hinterval, pow_one] at hgeom
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 N, (B*R^j)*generatingSum P N z^j := he
    _ = B*∑ j ∈ Finset.Icc 1 N, (R*generatingSum P N z)^j := by
      simp only [Finset.mul_sum, mul_pow, mul_assoc]
    _ ≤ B*((R*generatingSum P N z)/(1-R*generatingSum P N z)) :=
      mul_le_mul_of_nonneg_left hgeom hB
    _ = _ := by ring

end EulerGevreyGeneratingComposition
