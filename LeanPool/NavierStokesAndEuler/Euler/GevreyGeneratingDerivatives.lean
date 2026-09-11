/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.RCLike.Basic
public import LeanPool.NavierStokesAndEuler.Euler.GevreyCompositionPartitions
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! The finite generating sum for genuine derivatives.  This file derives
the identity-map contribution and the composition estimate needed by the
flow bootstrap from actual derivatives, including the exact Faà di Bruno
formula. -/

section

/-! The finite Gevrey-two generating sum obeys an actual composition
estimate.  In contrast to replacing all jets by one order-dependent bound,
this estimate retains the finite sum of the inner derivatives. -/

section

/-! Finite polynomial majorants for factorial-square Taylor coefficients.
The polynomials below are auxiliary nonnegative scalar polynomials.  Their
composition is the exact scalar Faà di Bruno sum, not an assumed majorant
for a flow or for a solution of a differential equation. -/

@[expose] public section

noncomputable section

open scoped BigOperators ContDiff Polynomial

namespace EulerGevreyGeneratingAlgebra

open EulerGevreyComposition

lemma factorialProduct_nonneg {n : ℕ} (c : OrderedFinpartition n) :
    0 ≤ factorialProduct c :=
  Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _

/-- The factorial used by an ordered partition never exceeds the total
factorial.  This is the extra factor available in Gevrey order two. -/
theorem partition_factorial_le {n : ℕ} (c : OrderedFinpartition n) :
    (c.length.factorial : ℝ) * factorialProduct c ≤ n.factorial := by
  induction n with
  | zero =>
      have hc : c = default := Subsingleton.elim _ _
      subst c
      simp [OrderedFinpartition.default_eq, factorialProduct]
  | succ n ih =>
      obtain ⟨⟨d,o⟩,rfl⟩ := (OrderedFinpartition.extendEquiv n).surjective c
      cases o with
      | none =>
          simp only [OrderedFinpartition.extendEquiv_apply,
            OrderedFinpartition.extend_none, OrderedFinpartition.extendLeft_length,
            factorialProduct_extendLeft]
          have hl : (d.length : ℝ) + 1 ≤ (n : ℝ) + 1 := by
            exact_mod_cast Nat.succ_le_succ d.length_le
          calc
            _ = ((d.length : ℝ)+1) * ((d.length.factorial : ℝ)*factorialProduct d) := by
              simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
              ring
            _ ≤ ((n : ℝ)+1) * (n.factorial : ℝ) :=
              mul_le_mul hl (ih d)
                (mul_nonneg (Nat.cast_nonneg _) (factorialProduct_nonneg d)) (by positivity)
            _ = _ := by simp [Nat.factorial_succ]
      | some i =>
          simp only [OrderedFinpartition.extendEquiv_apply,
            OrderedFinpartition.extend_some, OrderedFinpartition.extendMiddle_length,
            factorialProduct_extendMiddle]
          have hl : (d.partSize i : ℝ)+1 ≤ (n : ℝ)+1 := by
            exact_mod_cast Nat.succ_le_succ (d.partSize_le i)
          calc
            _ = ((d.partSize i : ℝ)+1) *
                ((d.length.factorial : ℝ)*factorialProduct d) := by ring
            _ ≤ ((n : ℝ)+1) * (n.factorial : ℝ) :=
              mul_le_mul hl (ih d)
                (mul_nonneg (Nat.cast_nonneg _) (factorialProduct_nonneg d)) (by positivity)
            _ = _ := by simp [Nat.factorial_succ]

theorem polynomial_iteratedDeriv (p : ℝ[X]) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => p.eval y) x =
      (Polynomial.derivative^[n] p).eval x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (fun y => p.eval y) =
          fun y => (Polynomial.derivative^[n] p).eval y := funext ih
      rw [he, Polynomial.deriv, Function.iterate_succ_apply']

theorem polynomial_iteratedDeriv_zero (p : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun y => p.eval y) 0 = (n.factorial : ℝ)*p.coeff n := by
  rw [polynomial_iteratedDeriv, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

theorem polynomial_contDiff (p : ℝ[X]) :
    ContDiff ℝ ∞ (fun y : ℝ => p.eval y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using
        (contDiff_const.mul (contDiff_id.pow n) : ContDiff ℝ ∞ (fun y : ℝ => a*y^n))

/-- Exact coefficient version of scalar Faà di Bruno at zero. -/
theorem comp_coefficient (p q : ℝ[X]) (hp : p.coeff 0 = 0) (n : ℕ) :
    (n.factorial : ℝ)*(q.comp p).coeff n =
      ∑ c : OrderedFinpartition n,
        ((c.length.factorial : ℝ)*q.coeff c.length) *
          ∏ i, ((c.partSize i).factorial : ℝ)*p.coeff (c.partSize i) := by
  have hp0 : p.eval 0 = 0 := by rw [← Polynomial.coeff_zero_eq_eval_zero, hp]
  have hc := iteratedDeriv_comp_eq_sum_orderedFinpartition
    ((polynomial_contDiff q).contDiffAt (x := p.eval 0))
    ((polynomial_contDiff p).contDiffAt (x := 0)) (i := n) (ENat.natCast_le_of_coe_top_le_withTop
        le_rfl _)
  have he : (fun y => (q.comp p).eval y) =
      (fun y => q.eval y) ∘ (fun y => p.eval y) := by
    funext y
    simp
  rw [← he, hp0] at hc
  simpa only [polynomial_iteratedDeriv_zero] using hc

/-- A finite scalar polynomial whose constant coefficient is zero. -/
def jetPolynomial (N : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.Icc 1 N, Polynomial.monomial j (a j)

theorem jetPolynomial_coeff (N : ℕ) (a : ℕ → ℝ) (j : ℕ) :
    (jetPolynomial N a).coeff j = if j ∈ Finset.Icc 1 N then a j else 0 := by
  simp [jetPolynomial, Polynomial.coeff_monomial]

@[simp] theorem jetPolynomial_zero (N : ℕ) (a : ℕ → ℝ) :
    (jetPolynomial N a).coeff 0 = 0 := by
  simp [jetPolynomial_coeff]

theorem jetPolynomial_coeff_of_mem (N : ℕ) (a : ℕ → ℝ) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 N) : (jetPolynomial N a).coeff j = a j := by
  simp [jetPolynomial_coeff, hj]

theorem jetPolynomial_eval (N : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    (jetPolynomial N a).eval x = ∑ j ∈ Finset.Icc 1 N, a j*x^j := by
  simp only [jetPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Nonnegative coefficients, given by `∀ n, 0 ≤ p.coeff n`. -/
def NonnegativeCoefficients (p : ℝ[X]) : Prop := ∀ n, 0 ≤ p.coeff n

theorem jetPolynomial_nonnegative (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ j ∈ Finset.Icc 1 N, 0 ≤ a j) :
    NonnegativeCoefficients (jetPolynomial N a) := by
  intro j
  rw [jetPolynomial_coeff]
  split_ifs with hj
  · exact ha j hj
  · exact le_rfl

theorem nonnegative_mul {p q : ℝ[X]} (hp : NonnegativeCoefficients p)
    (hq : NonnegativeCoefficients q) : NonnegativeCoefficients (p*q) := by
  intro n
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hp _) (hq _)

theorem nonnegative_pow {p : ℝ[X]} (hp : NonnegativeCoefficients p) (n : ℕ) :
    NonnegativeCoefficients (p^n) := by
  induction n with
  | zero => intro j; simp only [pow_zero, Polynomial.coeff_one]; split_ifs <;> norm_num
  | succ n ih => simpa only [pow_succ] using nonnegative_mul ih hp

theorem nonnegative_comp {p q : ℝ[X]} (hp : NonnegativeCoefficients p)
    (hq : NonnegativeCoefficients q) : NonnegativeCoefficients (q.comp p) := by
  intro n
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun j _ => by
    rw [Polynomial.coeff_C_mul]
    exact mul_nonneg (hq _) (nonnegative_pow hp j n)

/-- A partial sum of a nonnegative polynomial is bounded by its actual
evaluation.  No bound on the degree of the composed polynomial is needed. -/
theorem coefficient_sum_le_eval (p : ℝ[X]) (hp : NonnegativeCoefficients p)
    (s : Finset ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∑ j ∈ s, p.coeff j*x^j ≤ p.eval x := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc
    _ ≤ ∑ j ∈ s ∪ p.support, p.coeff j*x^j :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun j _ _ => mul_nonneg (hp j) (pow_nonneg hx j))
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro j _ hj
      have hz : p.coeff j = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hj
      rw [hz, zero_mul]

end EulerGevreyGeneratingAlgebra

end
end

end

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

end
end

end

section

/-! The finite generating-sum bootstrap used for the small lifted flow in
source (21).  A first-hitting argument proves the bound from an integral
inequality valid only inside its radius of convergence.  No global
smallness of the unknown path or exponential flow bound is assumed. -/

@[expose] public section

noncomputable section

namespace EulerGevreyFlowBootstrap

open Set MeasureTheory
open scoped Interval

/-- A continuous path cannot first hit a barrier if its bound up to that
first hit lies strictly below the barrier. -/
theorem continuous_barrier (f : ℝ → ℝ) (T B a : ℝ)
    (_hT : 0 ≤ T) (hB : 0 ≤ B) (ha : 0 < a) (hBa : B * T < a)
    (hf : ContinuousOn f (Icc 0 T)) (hf0 : f 0 = 0)
    (hstep : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, f s ≤ a) → f t ≤ B * t) :
    ∀ t ∈ Icc 0 T, f t ≤ B*t := by
  have hstrict : ∀ t ∈ Icc 0 T, f t < a := by
    intro t ht
    by_contra hfail
    let S := Icc (0 : ℝ) T ∩ f ⁻¹' Ici a
    have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici) inter_subset_left
    have hSn : S.Nonempty := ⟨t,ht,le_of_not_gt hfail⟩
    obtain ⟨m,hm⟩ := hSc.exists_isLeast hSn
    have hmI : m ∈ Icc (0 : ℝ) T := hm.1.1
    have hmhigh : a ≤ f m := hm.1.2
    have hfm : f m = a := by
      have hc : ContinuousOn f (Icc 0 m) := hf.mono (Icc_subset_Icc_right hmI.2)
      obtain ⟨r,hr,her⟩ := intermediate_value_Icc hmI.1 hc
        (show a ∈ Icc (f 0) (f m) from ⟨by rw [hf0]; exact ha.le,hmhigh⟩)
      have hmr : m ≤ r := hm.2 ⟨⟨hr.1,hr.2.trans hmI.2⟩,her.ge⟩
      have hrm : r = m := le_antisymm hr.2 hmr
      simpa only [hrm] using her
    have hbefore : ∀ s ∈ Icc 0 m, f s ≤ a := by
      intro s hs
      by_cases hsm : s = m
      · simp only [hsm,hfm,le_refl]
      · have hlt : s < m := lt_of_le_of_ne hs.2 hsm
        by_contra hhigh
        have hms : m ≤ s := hm.2 ⟨⟨hs.1,hs.2.trans hmI.2⟩,(lt_of_not_ge hhigh).le⟩
        exact (not_le_of_gt hlt) hms
    have hh := hstep m hmI hbefore
    have hmB : B*m ≤ B*T := mul_le_mul_of_nonneg_left hmI.2 hB
    rw [hfm] at hh
    linarith
  intro t ht
  exact hstep t ht (fun s hs => (hstrict s ⟨hs.1,hs.2.trans ht.2⟩).le)

/-- Rational rate, given by `B*(R*(a+u))/(1-R*(a+u))`. -/
def rationalRate (B R a u : ℝ) : ℝ := B*(R*(a+u))/(1-R*(a+u))

theorem rationalRate_le (B R a u : ℝ) (hB : 0 ≤ B)
    (hu : R * (a + u) ≤ 1 / 2) : rationalRate B R a u ≤ B := by
  have hd : 0 < 1-R*(a+u) := by linarith
  unfold rationalRate
  apply (div_le_iff₀ hd).2
  nlinarith [mul_le_mul_of_nonneg_left hu hB]

/-- The nonlinear generating-sum inequality closes at BRT≤1/8.  The bound
is linear in the velocity size B and time, with no exponential factor. -/
theorem rational_integral_bootstrap (f : ℝ → ℝ) (T B R : ℝ)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
    (hf : ContinuousOn f (Icc 0 T)) (hf0 : f 0 = 0)
    (hineq : ∀ t ∈ Icc 0 T,
      (∀ s ∈ Icc 0 t, R * ((4 * R)⁻¹ + f s) ≤ 1 / 2) →
      f t ≤ ∫ s in 0..t, rationalRate B R ((4 * R)⁻¹) (f s)) :
    ∀ t ∈ Icc 0 T, f t ≤ B*t ∧ R*((4*R)⁻¹+f t) ≤ 3/8 := by
  have ha : 0 < (4*R)⁻¹ := inv_pos.mpr (by positivity)
  have hRa : R*(4*R)⁻¹ = 1/4 := by field_simp
  have hBT : B*T < (4*R)⁻¹ := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) hR.le
    rw [hRa] at hm
    nlinarith
  have hb : ∀ t ∈ Icc 0 T, f t ≤ B*t := by
    apply continuous_barrier f T B ((4*R)⁻¹) hT hB ha hBT hf hf0
    intro t ht hbefore
    have hhalf : ∀ s ∈ Icc 0 t, R*((4*R)⁻¹+f s) ≤ 1/2 := by
      intro s hs
      have hm := mul_le_mul_of_nonneg_left (hbefore s hs) hR.le
      nlinarith
    have hden : ∀ s ∈ Icc 0 t, 1-R*((4*R)⁻¹+f s) ≠ 0 := by
      intro s hs
      have hh := hhalf s hs
      linarith
    have hrate : ContinuousOn (fun s => rationalRate B R ((4*R)⁻¹) (f s)) (Icc 0 t) := by
      have hf' := hf.mono (Icc_subset_Icc_right ht.2)
      unfold rationalRate
      exact (continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.add hf'))).div
        (continuousOn_const.sub (continuousOn_const.mul (continuousOn_const.add hf'))) hden
    have hi : IntervalIntegrable (fun s => rationalRate B R ((4*R)⁻¹) (f s)) volume 0 t :=
      hrate.intervalIntegrable_of_Icc ht.1
    have hm := intervalIntegral.integral_mono_on ht.1 hi intervalIntegrable_const
      (fun s hs => rationalRate_le B R ((4*R)⁻¹) (f s) hB (hhalf s hs))
    have hc : (∫ s in (0 : ℝ)..t, B) = B*t := by simp [mul_comm]
    exact (hineq t ht hhalf).trans (hm.trans_eq hc)
  intro t ht
  refine ⟨hb t ht,?_⟩
  have hm := mul_le_mul_of_nonneg_left (hb t ht) hR.le
  have htB := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hB hR.le)
  nlinarith

end EulerGevreyFlowBootstrap

end
end

end

@[expose] public section

noncomputable section

open scoped BigOperators ContDiff

namespace EulerGevreyGeneratingDerivatives

open EulerGevreyGeneratingComposition

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Derivative sum, given by `generatingSum (ftaylorSeries ℝ f x) N z`. -/
def derivativeSum (f : E → F) (N : ℕ) (z : ℝ) (x : E) : ℝ :=
  generatingSum (ftaylorSeries ℝ f x) N z

theorem derivativeSum_nonneg (f : E → F) (N : ℕ) (z : ℝ) (x : E)
    (hz : 0 ≤ z) : 0 ≤ derivativeSum f N z x :=
  generatingSum_nonneg _ _ _ hz

theorem derivativeSum_add_le (f g : E → F) (N : ℕ) (z : ℝ) (x : E)
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g x) (hz : 0 ≤ z) :
    derivativeSum (f+g) N z x ≤ derivativeSum f N z x+derivativeSum g N z x := by
  unfold derivativeSum generatingSum normalizedJet ftaylorSeries
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  have hnN : (n : ℕ∞ω) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  rw [iteratedFDeriv_add_apply (hf.of_le hnN) (hg.of_le hnN)]
  calc
    _ ≤ ((‖iteratedFDeriv ℝ n f x‖+‖iteratedFDeriv ℝ n g x‖)/(n.factorial : ℝ)^2)*z^n := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by ring

theorem norm_iteratedFDeriv_id_le (n : ℕ) (hn : 0 < n) (x : E) :
    ‖iteratedFDeriv ℝ n (id : E → E) x‖ ≤ if n = 1 then 1 else 0 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  by_cases hm : m = 0
  · subst m
    change ‖iteratedFDeriv ℝ 1 (id : E → E) x‖ ≤ (1 : ℝ)
    rw [norm_iteratedFDeriv_one, fderiv_id]
    exact ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
  · have hm1 : m+1 ≠ 1 := by omega
    have hid : fderiv ℝ (id : E → E) = fun _ : E => ContinuousLinearMap.id ℝ E := by
      funext y
      exact fderiv_id
    rw [Nat.succ_eq_add_one, ite_eq_right hm1, ← norm_iteratedFDeriv_fderiv]
    simp [hid, iteratedFDeriv_const_of_ne hm]

theorem derivativeSum_id_le (N : ℕ) (z : ℝ) (x : E) (hz : 0 ≤ z) :
    derivativeSum (id : E → E) N z x ≤ z := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, if n = 1 then z else 0 := by
      unfold derivativeSum generatingSum
      apply Finset.sum_le_sum
      intro n hn
      have hnorm := norm_iteratedFDeriv_id_le n (Finset.mem_Icc.mp hn).1 x
      change ‖iteratedFDeriv ℝ n (id : E → E) x‖/(n.factorial : ℝ)^2*z^n ≤ _
      by_cases hn1 : n = 1
      · subst n
        simp only [ite_true, Nat.factorial_one, Nat.cast_one,
          one_pow, div_one, pow_one] at hnorm ⊢
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm hz
      · simp only [ite_eq_right hn1] at hnorm ⊢
        have hz0 : ‖iteratedFDeriv ℝ n (id : E → E) x‖ = 0 :=
          le_antisymm hnorm (norm_nonneg _)
        rw [hz0, zero_div, zero_mul]
    _ ≤ z := by
      simp only [Finset.sum_ite_eq', Finset.mem_Icc, le_refl, true_and]
      split_ifs
      · exact le_rfl
      · exact hz

theorem derivativeSum_id_add_le (f : E → E) (N : ℕ) (z : ℝ) (x : E)
    (hf : ContDiffAt ℝ N f x) (hz : 0 ≤ z) :
    derivativeSum (id+f) N z x ≤ z+derivativeSum f N z x :=
  (derivativeSum_add_le id f N z x contDiffAt_id hf hz).trans
    (add_le_add (derivativeSum_id_le N z x hz) le_rfl)

theorem derivativeSum_comp_le (f : E → F) (g : F → G) (N : ℕ)
    (z B R : ℝ) (x : E) (hz : 0 ≤ z) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g (f x))
    (hgj : ∀ j ∈ Finset.Icc 1 N,
      ‖iteratedFDeriv ℝ j g (f x)‖ ≤ B * R ^ j * (j.factorial : ℝ) ^ 2)
    (hsmall : R * derivativeSum f N z x < 1) :
    derivativeSum (g ∘ f) N z x ≤
      B*(R*derivativeSum f N z x)/(1-R*derivativeSum f N z x) := by
  have he := generatingSum_taylorComp_le (ftaylorSeries ℝ f x)
    (ftaylorSeries ℝ g (f x)) N B R z hB hR hz hgj hsmall
  refine le_trans (le_of_eq ?_) he
  unfold derivativeSum generatingSum normalizedJet
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : (n : ℕ∞ω) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  rw [show ftaylorSeries ℝ (g ∘ f) x n =
    (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeries ℝ f x) n from
    iteratedFDeriv_comp hg hf hnN]

theorem rational_fraction_mono (B x y : ℝ) (hB : 0 ≤ B)
    (hxy : x ≤ y) (hy : y < 1) :
    B*x/(1-x) ≤ B*y/(1-y) := by
  have hx : 0 < 1-x := by linarith
  have hy' : 0 < 1-y := by linarith
  apply (div_le_div_iff₀ hx hy').2
  nlinarith [mul_le_mul_of_nonneg_left hxy hB]

/-- The identity part of a flow costs exactly z in its generating sum. -/
theorem derivativeSum_comp_id_add_le (f : E → E) (g : E → F) (N : ℕ)
    (z B R : ℝ) (x : E) (hz : 0 ≤ z) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g (x + f x))
    (hgj : ∀ j ∈ Finset.Icc 1 N,
      ‖iteratedFDeriv ℝ j g (x + f x)‖ ≤ B * R ^ j * (j.factorial : ℝ) ^ 2)
    (hsmall : R * (z + derivativeSum f N z x) < 1) :
    derivativeSum (g ∘ (id+f)) N z x ≤
      EulerGevreyFlowBootstrap.rationalRate B R z (derivativeSum f N z x) := by
  have hsum := mul_le_mul_of_nonneg_left (derivativeSum_id_add_le f N z x hf hz) hR
  have he := derivativeSum_comp_le (id+f) g N z B R x hz hB hR
    (contDiffAt_id.add hf) hg
    (by simpa only [Pi.add_apply, id_eq] using hgj) (hsum.trans_lt hsmall)
  exact he.trans (rational_fraction_mono B _ _ hB hsum hsmall)

end EulerGevreyGeneratingDerivatives
