/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.InnerProductSpace.Dual


/-!
# Polarization of bounded quadratic forms

This file reconstructs a bounded complex sesquilinear form from a nonnegative quadratic form
satisfying complex homogeneity and the parallelogram law. The diagonal of the reconstructed form
is the original quadratic form.
-/

public section

open scoped ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The real polarization of a real-valued quadratic function. -/
noncomputable def realPolarization (q : V → ℝ) (x y : V) : ℝ :=
  (q (x + y) - q (x - y)) / 4

section

variable (q : V → ℝ)
variable (hq_smul : ∀ (c : ℂ) (x : V), q (c • x) = ‖c‖ ^ 2 * q x)
variable (hq_para : ∀ x y : V,
  q (x + y) + q (x - y) = (q x + q x) + (q y + q y))

include hq_smul

private theorem q_zero (x : V) : q 0 = 0 := by
  have h := hq_smul 0 x
  simpa only [zero_smul, norm_zero, pow_two, zero_mul] using h

private theorem q_neg (x : V) : q (-x) = q x := by
  have h := hq_smul (-1) x
  simpa only [neg_smul, one_smul, norm_neg, norm_one, one_pow, one_mul] using h

private theorem realPolarization_symm (x y : V) :
    realPolarization q x y = realPolarization q y x := by
  unfold realPolarization
  rw [add_comm x y, show x - y = -(y - x) by abel, q_neg q hq_smul]

private theorem realPolarization_zero_left (y : V) :
    realPolarization q 0 y = 0 := by
  unfold realPolarization
  rw [zero_add, zero_sub, q_neg q hq_smul]
  ring

omit hq_smul
include hq_para

omit [NormedSpace ℂ V] in
private theorem realPolarization_add_sub (x z y : V) :
    realPolarization q (x + z) y + realPolarization q (x - z) y =
      2 * realPolarization q x y := by
  have hplus := hq_para (x + y) z
  have hminus := hq_para (x - y) z
  unfold realPolarization
  rw [show x + z + y = x + y + z by abel,
    show x + z - y = x - y + z by abel,
    show x - z + y = x + y - z by abel,
    show x - z - y = x - y - z by abel]
  linarith

include hq_smul

private theorem realPolarization_add_left (x z y : V) :
    realPolarization q (x + z) y =
      realPolarization q x y + realPolarization q z y := by
  let a : V := (2 : ℂ)⁻¹ • (x + z)
  let b : V := (2 : ℂ)⁻¹ • (x - z)
  have hab : a + b = x := by
    dsimp [a, b]
    module
  have hab' : a - b = z := by
    dsimp [a, b]
    module
  have hmid := realPolarization_add_sub q hq_para a b y
  rw [hab, hab'] at hmid
  have hdouble := realPolarization_add_sub q hq_para a a y
  have haa : a + a = x + z := by
    dsimp [a]
    module
  have hzero : a - a = 0 := sub_self a
  rw [haa, hzero, realPolarization_zero_left q hq_smul] at hdouble
  linarith

private theorem realPolarization_add_right (x y z : V) :
    realPolarization q x (y + z) =
      realPolarization q x y + realPolarization q x z := by
  rw [realPolarization_symm q hq_smul x (y + z),
    realPolarization_add_left q hq_smul hq_para y z x,
    realPolarization_symm q hq_smul y x,
    realPolarization_symm q hq_smul z x]

omit hq_para

private theorem realPolarization_self (x : V) :
    realPolarization q x x = q x := by
  unfold realPolarization
  have htwo := hq_smul 2 x
  rw [show x + x = (2 : ℂ) • x by module, sub_self, q_zero q hq_smul x, htwo]
  norm_num

include hq_para

private theorem q_add (x y : V) :
    q (x + y) = q x + 2 * realPolarization q x y + q y := by
  rw [← realPolarization_self q hq_smul (x + y),
    realPolarization_add_left q hq_smul hq_para,
    realPolarization_add_right q hq_smul hq_para,
    realPolarization_add_right q hq_smul hq_para,
    realPolarization_self q hq_smul,
    realPolarization_self q hq_smul,
    realPolarization_symm q hq_smul y x]
  ring

private theorem realPolarization_rat_smul_left (r : ℚ) (x y : V) :
    realPolarization q (((r : ℝ) : ℂ) • x) y =
      (r : ℝ) * realPolarization q x y := by
  let f : V →+ ℝ :=
    { toFun := fun z => realPolarization q z y
      map_zero' := realPolarization_zero_left q hq_smul y
      map_add' := fun x z => realPolarization_add_left q hq_smul hq_para x z y }
  simpa [f, smul_eq_mul] using map_ratCast_smul f ℂ ℝ r x

variable (hq_nonneg : ∀ x : V, 0 ≤ q x)

include hq_nonneg

private theorem realPolarization_sq_le (x y : V) :
    realPolarization q x y ^ 2 ≤ q x * q y := by
  have hpoly : ∀ t : ℝ,
      0 ≤ q x * (t * t) + (2 * realPolarization q x y) * t + q y := by
    intro t
    refine DenseRange.induction_on Rat.isDenseEmbedding_coe_real.dense t
      (isClosed_le continuous_const (by fun_prop)) ?_
    intro r
    have hnonneg := hq_nonneg (((r : ℝ) : ℂ) • x + y)
    rw [q_add q hq_smul hq_para,
      hq_smul, realPolarization_rat_smul_left q hq_smul hq_para] at hnonneg
    have hnorm : ‖((r : ℝ) : ℂ)‖ ^ 2 = (r : ℝ) * (r : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    rw [hnorm] at hnonneg
    nlinarith only [hnonneg]
  have hd : discrim (q x) (2 * realPolarization q x y) (q y) ≤ 0 :=
    discrim_le_zero hpoly
  rw [discrim] at hd
  nlinarith only [hd]

variable (hq_le : ∀ x : V, q x ≤ ‖x‖ ^ 2)

include hq_le

private theorem abs_realPolarization_le (x y : V) :
    |realPolarization q x y| ≤ ‖x‖ * ‖y‖ := by
  apply abs_le_of_sq_le_sq
  · calc
      realPolarization q x y ^ 2 ≤ q x * q y :=
        realPolarization_sq_le q hq_smul hq_para hq_nonneg x y
      _ ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
        exact mul_le_mul (hq_le x) (hq_le y) (hq_nonneg y) (sq_nonneg ‖x‖)
      _ = (‖x‖ * ‖y‖) ^ 2 := by ring
  · positivity

private theorem realPolarization_real_smul_left (r : ℝ) (x y : V) :
    realPolarization q (r • x) y = r * realPolarization q x y := by
  let f : V →+ ℝ :=
    { toFun := fun z => realPolarization q z y
      map_zero' := realPolarization_zero_left q hq_smul y
      map_add' := fun x z => realPolarization_add_left q hq_smul hq_para x z y }
  have hf : Continuous f := AddMonoidHomClass.continuous_of_bound f ‖y‖ fun z => by
    change |realPolarization q z y| ≤ ‖y‖ * ‖z‖
    simpa only [mul_comm] using
      abs_realPolarization_le q hq_smul hq_para hq_nonneg hq_le z y
  have hr := map_real_smul f hf r x
  change realPolarization q (r • x) y = r * realPolarization q x y
  exact hr

private theorem realPolarization_real_smul_right (r : ℝ) (x y : V) :
    realPolarization q x (r • y) = r * realPolarization q x y := by
  rw [realPolarization_symm q hq_smul,
    realPolarization_real_smul_left q hq_smul hq_para hq_nonneg hq_le,
    realPolarization_symm q hq_smul]

/-- The complex polarization formed from the real polarization. -/
noncomputable def complexPolarization (q : V → ℝ) (x y : V) : ℂ :=
  (realPolarization q x y : ℂ) +
    Complex.I * (realPolarization q (Complex.I • x) y : ℂ)

omit hq_para hq_nonneg hq_le

private theorem realPolarization_I_I (x y : V) :
    realPolarization q (Complex.I • x) (Complex.I • y) =
      realPolarization q x y := by
  unfold realPolarization
  rw [← smul_add, ← smul_sub, hq_smul, hq_smul, Complex.norm_I,
    one_pow, one_mul, one_mul]

include hq_para hq_nonneg hq_le

private theorem realPolarization_I_left (x y : V) :
    realPolarization q (Complex.I • x) y =
      -realPolarization q x (Complex.I • y) := by
  have h := realPolarization_I_I q hq_smul (x := x) (y := Complex.I • y)
  rw [smul_smul, Complex.I_mul_I, neg_one_smul] at h
  have hneg : realPolarization q (Complex.I • x) (-y) =
      -realPolarization q (Complex.I • x) y := by
    rw [← neg_one_smul ℝ y,
      realPolarization_real_smul_right q hq_smul hq_para hq_nonneg hq_le]
    ring
  rw [hneg] at h
  linarith

omit hq_nonneg hq_le in
private theorem complexPolarization_add_left (x z y : V) :
    complexPolarization q (x + z) y =
      complexPolarization q x y + complexPolarization q z y := by
  unfold complexPolarization
  rw [realPolarization_add_left q hq_smul hq_para, smul_add,
    realPolarization_add_left q hq_smul hq_para]
  push_cast
  ring

omit hq_nonneg hq_le in
private theorem complexPolarization_add_right (x y z : V) :
    complexPolarization q x (y + z) =
      complexPolarization q x y + complexPolarization q x z := by
  unfold complexPolarization
  rw [realPolarization_add_right q hq_smul hq_para,
    realPolarization_add_right q hq_smul hq_para]
  push_cast
  ring

private theorem complexPolarization_I_left (x y : V) :
    complexPolarization q (Complex.I • x) y =
      star Complex.I * complexPolarization q x y := by
  unfold complexPolarization
  have hneg : realPolarization q (-x) y = -realPolarization q x y := by
    rw [← neg_one_smul ℝ x,
      realPolarization_real_smul_left q hq_smul hq_para hq_nonneg hq_le]
    ring
  rw [smul_smul, Complex.I_mul_I, neg_one_smul, hneg]
  have hstarI : star Complex.I = -Complex.I := by
    exact Complex.conj_I
  push_cast
  rw [hstarI, mul_add, neg_mul, mul_neg, ← mul_assoc, neg_mul,
    Complex.I_mul_I, neg_neg, one_mul]
  ring

private theorem complexPolarization_I_right (x y : V) :
    complexPolarization q x (Complex.I • y) =
      Complex.I * complexPolarization q x y := by
  unfold complexPolarization
  have hleft := realPolarization_I_left q hq_smul hq_para hq_nonneg hq_le x y
  have hswap : realPolarization q x (Complex.I • y) =
      -realPolarization q (Complex.I • x) y := by linarith
  rw [hswap, realPolarization_I_I q hq_smul]
  push_cast
  rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  ring

private theorem complexPolarization_real_smul_left (r : ℝ) (x y : V) :
    complexPolarization q (r • x) y =
      (r : ℂ) * complexPolarization q x y := by
  unfold complexPolarization
  have hcomm : Complex.I • (r • x) = r • (Complex.I • x) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, smul_smul]
    ring_nf
  rw [realPolarization_real_smul_left q hq_smul hq_para hq_nonneg hq_le,
    hcomm,
    realPolarization_real_smul_left q hq_smul hq_para hq_nonneg hq_le]
  push_cast
  ring

private theorem complexPolarization_real_smul_right (r : ℝ) (x y : V) :
    complexPolarization q x (r • y) =
      (r : ℂ) * complexPolarization q x y := by
  unfold complexPolarization
  rw [realPolarization_real_smul_right q hq_smul hq_para hq_nonneg hq_le,
    realPolarization_real_smul_right q hq_smul hq_para hq_nonneg hq_le]
  push_cast
  ring

private theorem complexPolarization_smul_left (c : ℂ) (x y : V) :
    complexPolarization q (c • x) y =
      star c * complexPolarization q x y := by
  have hc : c • x = c.re • x + c.im • (Complex.I • x) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    rw [← add_smul]
    congr 1
    exact (Complex.re_add_im c).symm
  rw [hc, complexPolarization_add_left q hq_smul hq_para,
    complexPolarization_real_smul_left q hq_smul hq_para hq_nonneg hq_le,
    complexPolarization_real_smul_left q hq_smul hq_para hq_nonneg hq_le,
    complexPolarization_I_left q hq_smul hq_para hq_nonneg hq_le]
  have hstarI : star Complex.I = -Complex.I := by
    exact Complex.conj_I
  rw [hstarI]
  have hstar : star c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    rw [Complex.star_def]
    apply Complex.ext <;> simp only [Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
    all_goals ring
  rw [hstar]
  ring

private theorem complexPolarization_smul_right (c : ℂ) (x y : V) :
    complexPolarization q x (c • y) =
      c * complexPolarization q x y := by
  have hc : c • y = c.re • y + c.im • (Complex.I • y) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    rw [← add_smul]
    congr 1
    exact (Complex.re_add_im c).symm
  rw [hc, complexPolarization_add_right q hq_smul hq_para,
    complexPolarization_real_smul_right q hq_smul hq_para hq_nonneg hq_le,
    complexPolarization_real_smul_right q hq_smul hq_para hq_nonneg hq_le,
    complexPolarization_I_right q hq_smul hq_para hq_nonneg hq_le]
  conv_rhs => rw [← Complex.re_add_im c]
  ring

private theorem norm_complexPolarization_le (x y : V) :
    ‖complexPolarization q x y‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  unfold complexPolarization
  calc
    ‖(realPolarization q x y : ℂ) +
        Complex.I * (realPolarization q (Complex.I • x) y : ℂ)‖ ≤
      ‖(realPolarization q x y : ℂ)‖ +
        ‖Complex.I * (realPolarization q (Complex.I • x) y : ℂ)‖ := norm_add_le _ _
    _ = |realPolarization q x y| +
        |realPolarization q (Complex.I • x) y| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖x‖ * ‖y‖ + ‖Complex.I • x‖ * ‖y‖ :=
      add_le_add
        (abs_realPolarization_le q hq_smul hq_para hq_nonneg hq_le x y)
        (abs_realPolarization_le q hq_smul hq_para hq_nonneg hq_le
          (Complex.I • x) y)
    _ = 2 * ‖x‖ * ‖y‖ := by rw [norm_smul, Complex.norm_I, one_mul]; ring

/-- The sesquilinear map obtained by polarizing the quadratic function. -/
noncomputable def polarizationLinearMap :
    V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (complexPolarization q)
    (by exact complexPolarization_add_left q hq_smul hq_para)
    (by exact complexPolarization_smul_left q hq_smul hq_para hq_nonneg hq_le)
    (by exact complexPolarization_add_right q hq_smul hq_para)
    (by exact complexPolarization_smul_right q hq_smul hq_para hq_nonneg hq_le)

/-- Polarization turns a nonnegative, norm-bounded complex quadratic function into a bounded
sesquilinear form. The first argument is conjugate-linear and the second is linear. -/
noncomputable def boundedSesquilinearFormOfQuadratic :
    V →L⋆[ℂ] V →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (polarizationLinearMap q hq_smul hq_para hq_nonneg hq_le) 2
    (by exact norm_complexPolarization_le q hq_smul hq_para hq_nonneg hq_le)

private theorem complexPolarization_self (x : V) :
    complexPolarization q x x = q x := by
  have hI := realPolarization_I_left q hq_smul hq_para hq_nonneg hq_le x x
  rw [realPolarization_symm q hq_smul x (Complex.I • x)] at hI
  have hzero : realPolarization q (Complex.I • x) x = 0 := by linarith
  unfold complexPolarization
  rw [realPolarization_self q hq_smul, hzero]
  norm_num

/-- The polarized sesquilinear form recovers the quadratic function on its diagonal. -/
theorem boundedSesquilinearFormOfQuadratic_apply_self (x : V) :
    boundedSesquilinearFormOfQuadratic q hq_smul hq_para hq_nonneg hq_le x x = q x := by
  change complexPolarization q x x = q x
  exact complexPolarization_self q hq_smul hq_para hq_nonneg hq_le x

end
