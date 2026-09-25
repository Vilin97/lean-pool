/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Tactic

/-! # Rational Ellipsoid -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# A square-root-free rational ellipsoid update

An ellipsoid is represented as the affine image of the Euclidean unit ball,
`c + B y`.  Both `c` and `B` will be rational in the executable algorithm.
For a central cut with pulled-back normal `b = Bᵀ a`, the usual optimal
ellipsoid update normalizes `b` by its Euclidean norm and therefore introduces
a square root.  We instead normalize by the rational quantity `sum |bᵢ|` and
take a smaller center step.  The update is weaker, but it still contracts
volume by an inverse-polynomial factor and keeps all stored data rational.
-/

/-- Explicit dot product, used over both `ℚ` and `ℝ`. -/
def finiteDot {d : ℕ} {R : Type*} [CommSemiring R]
    (x y : Fin d → R) : R :=
  ∑ i, x i * y i

/-- Squared Euclidean norm, expressed without a square root. -/
def finiteNormSq {d : ℕ} {R : Type*} [CommSemiring R]
    (x : Fin d → R) : R :=
  finiteDot x x

/-- Rational normalization used for a cut direction. -/
def cutL1Scale {d : ℕ} (b : Fin d → ℚ) : ℚ :=
  ∑ i, abs (b i)

theorem finiteNormSq_nonneg {d : ℕ} (x : Fin d → ℝ) :
    0 ≤ finiteNormSq x := by
  rw [finiteNormSq, finiteDot]
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (x i)

theorem finiteNormSq_eq_zero_iff {d : ℕ} (x : Fin d → ℝ) :
    finiteNormSq x = 0 ↔ x = 0 := by
  rw [finiteNormSq, finiteDot, Finset.sum_mul_self_eq_zero_iff]
  constructor
  · intro h
    ext i
    simpa using h i (Finset.mem_univ i)
  · intro h
    subst x
    simp

theorem cutL1Scale_nonnegative {d : ℕ} (b : Fin d → ℚ) :
    0 ≤ cutL1Scale b := by
  rw [cutL1Scale]
  exact Finset.sum_nonneg fun i _ ↦ abs_nonneg (b i)

theorem cutL1Scale_pos {d : ℕ} {b : Fin d → ℚ} (hb : b ≠ 0) :
    0 < cutL1Scale b := by
  have hnonneg : 0 ≤ ∑ i, abs (b i) :=
    Finset.sum_nonneg fun i _ ↦ abs_nonneg (b i)
  have hne : (∑ i, abs (b i)) ≠ 0 := by
    intro hzero
    apply hb
    ext i
    exact abs_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_hi : i ∈ Finset.univ) ↦ abs_nonneg (b i))).1
          hzero i (Finset.mem_univ i))
  rw [cutL1Scale]
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The Euclidean norm is at most the `ℓ1` norm.  We state the squared form,
which is the one used by the rational update. -/
theorem finiteNormSq_le_cutL1Scale_sq {d : ℕ} (b : Fin d → ℚ) :
    finiteNormSq b ≤ cutL1Scale b ^ 2 := by
  let S : ℚ := ∑ i, abs (b i)
  have hi : ∀ i, abs (b i) ≤ S := by
    intro i
    exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (b j))
      (Finset.mem_univ i)
  calc
    finiteNormSq b = ∑ i, (abs (b i)) ^ 2 := by
      simp [finiteNormSq, finiteDot, sq]
    _ ≤ ∑ i, abs (b i) * S := by
      apply Finset.sum_le_sum
      intro i _
      rw [sq]
      exact mul_le_mul_of_nonneg_left (hi i) (abs_nonneg _)
    _ = S ^ 2 := by simp [S, sq, Finset.sum_mul]
    _ = cutL1Scale b ^ 2 := by rw [cutL1Scale]

/-- Cauchy--Schwarz gives the converse comparison with a factor equal to the
dimension. -/
theorem cutL1Scale_sq_le_card_mul_normSq {d : ℕ} (b : Fin d → ℚ) :
    cutL1Scale b ^ 2 ≤ d * finiteNormSq b := by
  rw [cutL1Scale, finiteNormSq, finiteDot]
  simpa [sq, abs_mul_abs_self] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i ↦ abs (b i)))

/-- Finite-dimensional Cauchy--Schwarz in the squared form needed below. -/
theorem finiteDot_sq_le_normSq_mul_normSq {d : ℕ}
    (x y : Fin d → ℝ) :
    finiteDot x y ^ 2 ≤ finiteNormSq x * finiteNormSq y := by
  simpa [finiteDot, finiteNormSq, sq, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) x y)

theorem finiteDot_add_right {d : ℕ} (x y z : Fin d → ℝ) :
    finiteDot x (fun i ↦ y i + z i) = finiteDot x y + finiteDot x z := by
  simp [finiteDot, mul_add, Finset.sum_add_distrib]

theorem finiteDot_smul_left {d : ℕ} (a : ℝ) (x y : Fin d → ℝ) :
    finiteDot (fun i ↦ a * x i) y = a * finiteDot x y := by
  rw [finiteDot, finiteDot]
  calc
    (∑ i, a * x i * y i) = ∑ i, a * (x i * y i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = a * ∑ i, x i * y i := by rw [Finset.mul_sum]

theorem finiteDot_smul_right {d : ℕ} (a : ℝ) (x y : Fin d → ℝ) :
    finiteDot x (fun i ↦ a * y i) = a * finiteDot x y := by
  rw [finiteDot, finiteDot]
  calc
    (∑ i, x i * (a * y i)) = ∑ i, a * (x i * y i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = a * ∑ i, x i * y i := by rw [Finset.mul_sum]

theorem finiteNormSq_smul {d : ℕ} (a : ℝ) (x : Fin d → ℝ) :
    finiteNormSq (fun i ↦ a * x i) = a ^ 2 * finiteNormSq x := by
  rw [finiteNormSq, finiteDot, finiteNormSq, finiteDot]
  calc
    (∑ i, a * x i * (a * x i)) = ∑ i, a ^ 2 * (x i * x i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = a ^ 2 * ∑ i, x i * x i := by rw [Finset.mul_sum]

theorem finiteNormSq_add {d : ℕ} (x y : Fin d → ℝ) :
    finiteNormSq (fun i ↦ x i + y i) =
      finiteNormSq x + 2 * finiteDot x y + finiteNormSq y := by
  rw [finiteNormSq, finiteDot, finiteNormSq, finiteDot,
    finiteDot]
  calc
    (∑ i, (x i + y i) * (x i + y i)) =
        ∑ i, (x i * x i + (2 * (x i * y i) + y i * y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, x i * x i) +
          2 * (∑ i, x i * y i) + ∑ i, y i * y i := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- Center-step coefficient for dimension `d`.  The update is used only for
positive dimensions. -/
def rationalEllipsoidAlpha (d : ℕ) : ℚ := 1 / (4 * d ^ 2)

/-- Expansion in directions orthogonal to the cut. -/
def rationalEllipsoidPerpScale (d : ℕ) : ℚ :=
  1 + 2 * rationalEllipsoidAlpha d ^ 2

/-- Contraction in the cut direction. -/
def rationalEllipsoidParallelScale (d : ℕ) : ℚ :=
  1 - rationalEllipsoidAlpha d / d

theorem rationalEllipsoidAlpha_pos {d : ℕ} (hd : 0 < d) :
    0 < rationalEllipsoidAlpha d := by
  rw [rationalEllipsoidAlpha]
  positivity

theorem rationalEllipsoidAlpha_le_quarter {d : ℕ} (hd : 0 < d) :
    rationalEllipsoidAlpha d ≤ 1 / 4 := by
  have hdq : (1 : ℚ) ≤ d := by exact_mod_cast hd
  change (1 : ℚ) / (4 * (d : ℚ) ^ 2) ≤ 1 / 4
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg ((d : ℚ) - 1)]

theorem rationalEllipsoidParallelScale_pos {d : ℕ} (hd : 0 < d) :
    0 < rationalEllipsoidParallelScale d := by
  have ha0 := rationalEllipsoidAlpha_pos hd
  have ha1 := rationalEllipsoidAlpha_le_quarter hd
  have hdq : (1 : ℚ) ≤ d := by exact_mod_cast hd
  rw [rationalEllipsoidParallelScale]
  have had : rationalEllipsoidAlpha d / d ≤ 1 / 4 := by
    exact (div_le_iff₀ (by positivity : (0 : ℚ) < d)).2
      (by nlinarith)
  linarith

theorem rationalEllipsoidParallelScale_le_one (d : ℕ) :
    rationalEllipsoidParallelScale d ≤ 1 := by
  rw [rationalEllipsoidParallelScale]
  by_cases hd : d = 0
  · simp [hd]
  · have hdq : (0 : ℚ) < d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
    have : 0 ≤ rationalEllipsoidAlpha d / d :=
      (div_pos (rationalEllipsoidAlpha_pos (Nat.pos_of_ne_zero hd)) hdq).le
    linarith

theorem rationalEllipsoidParallelScale_ge_three_quarters
    {d : ℕ} (hd : 0 < d) :
    (3 / 4 : ℚ) ≤ rationalEllipsoidParallelScale d := by
  have ha := rationalEllipsoidAlpha_le_quarter hd
  have hdq : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have had : rationalEllipsoidAlpha d / d ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℚ) < d)]
    nlinarith
  rw [rationalEllipsoidParallelScale]
  linarith

theorem rationalEllipsoidPerpScale_pos (d : ℕ) :
    0 < rationalEllipsoidPerpScale d := by
  rw [rationalEllipsoidPerpScale]
  positivity

theorem rationalEllipsoidParallel_lt_perp {d : ℕ} (hd : 0 < d) :
    rationalEllipsoidParallelScale d < rationalEllipsoidPerpScale d := by
  have ha := rationalEllipsoidAlpha_pos hd
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  rw [rationalEllipsoidParallelScale, rationalEllipsoidPerpScale]
  have had : 0 < rationalEllipsoidAlpha d / d := div_pos ha hdq
  nlinarith [sq_nonneg (rationalEllipsoidAlpha d)]

/-- A coarse lower bound on the exact determinant multiplier.  It is used
for an all-input bit-growth bound; unlike the contraction estimate, no
transcendental inequality is needed. -/
theorem rationalEllipsoid_volumeFactor_ge_half {d : ℕ} (hd : 0 < d) :
    (1 / 2 : ℝ) ≤
      (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) *
        (rationalEllipsoidParallelScale d : ℝ) := by
  have hperp : (1 : ℝ) ≤ (rationalEllipsoidPerpScale d : ℝ) := by
    rw [rationalEllipsoidPerpScale]
    norm_num
    positivity
  have hpow : (1 : ℝ) ≤
      (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) :=
    one_le_pow₀ hperp
  have hparallel : (3 / 4 : ℝ) ≤
      (rationalEllipsoidParallelScale d : ℝ) := by
    have hq := rationalEllipsoidParallelScale_ge_three_quarters hd
    have hcast : (((3 / 4 : ℚ) : ℚ) : ℝ) ≤
        (rationalEllipsoidParallelScale d : ℝ) := Rat.cast_le.mpr hq
    norm_num at hcast ⊢
    exact hcast
  calc
    (1 / 2 : ℝ) ≤ 1 * (3 / 4 : ℝ) := by norm_num
    _ ≤ (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) *
        (rationalEllipsoidParallelScale d : ℝ) :=
      mul_le_mul hpow hparallel (by norm_num) (by positivity)

/-- Quantitative inverse-polynomial contraction of the determinant factor.
The proof uses only `1+x ≤ exp x`; no numerical estimate or square-root
normalization is hidden here. -/
theorem rationalEllipsoid_volumeFactor_le_exp_neg {d : ℕ} (hd : 0 < d) :
    (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) *
        (rationalEllipsoidParallelScale d : ℝ) ≤
      Real.exp (-1 / (8 * (d : ℝ) ^ 3)) := by
  let α : ℝ := (rationalEllipsoidAlpha d : ℝ)
  let x : ℝ := 2 * α ^ 2
  let y : ℝ := α / d
  have hα0 : 0 < α := by
    have hq := rationalEllipsoidAlpha_pos hd
    have hc : (0 : ℝ) < (rationalEllipsoidAlpha d : ℝ) := by
      exact_mod_cast hq
    simpa only [α] using hc
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx0 : 0 ≤ x := by simp [x]; positivity
  have hy0 : 0 < y := div_pos hα0 (by positivity)
  have hA : (rationalEllipsoidPerpScale d : ℝ) = 1 + x := by
    simp [rationalEllipsoidPerpScale, x, α]
  have hp : (rationalEllipsoidParallelScale d : ℝ) = 1 - y := by
    simp [rationalEllipsoidParallelScale, y, α]
  have hp0 : 0 < 1 - y := by
    rw [← hp]
    have hq := rationalEllipsoidParallelScale_pos hd
    exact (Rat.cast_pos (K := ℝ)).mpr hq
  have hbase : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hpow : (1 + x) ^ (d - 1) ≤ (Real.exp x) ^ (d - 1) :=
    pow_le_pow_left₀ (by positivity) hbase _
  have hparallel : 1 - y ≤ Real.exp (-y) := by
    linarith [Real.add_one_le_exp (-y)]
  have hfirst := mul_le_mul hpow hparallel hp0.le
    (by positivity : 0 ≤ (Real.exp x) ^ (d - 1))
  have hexpEq : (Real.exp x) ^ (d - 1) * Real.exp (-y) =
      Real.exp (((d - 1 : ℕ) : ℝ) * x - y) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
  have hαformula : α = 1 / (4 * (d : ℝ) ^ 2) := by
    simp [α, rationalEllipsoidAlpha]
  have hexponent : (((d - 1 : ℕ) : ℝ) * x - y) ≤
      -1 / (8 * (d : ℝ) ^ 3) := by
    have hdsub : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast Nat.sub_le d 1
    have hdpos : (0 : ℝ) < d := by positivity
    dsimp only [x, y]
    rw [hαformula]
    field_simp
    nlinarith
  calc
    (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) *
          (rationalEllipsoidParallelScale d : ℝ) =
        (1 + x) ^ (d - 1) * (1 - y) := by rw [hA, hp]
    _ ≤ (Real.exp x) ^ (d - 1) * Real.exp (-y) := hfirst
    _ = Real.exp (((d - 1 : ℕ) : ℝ) * x - y) := hexpEq
    _ ≤ Real.exp (-1 / (8 * (d : ℝ) ^ 3)) := Real.exp_le_exp.mpr hexponent

theorem rationalEllipsoid_volumeFactor_lt_one {d : ℕ} (hd : 0 < d) :
    (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) *
        (rationalEllipsoidParallelScale d : ℝ) < 1 := by
  calc
    (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) *
          (rationalEllipsoidParallelScale d : ℝ) ≤
        Real.exp (-1 / (8 * (d : ℝ) ^ 3)) :=
      rationalEllipsoid_volumeFactor_le_exp_neg hd
    _ < Real.exp 0 := Real.exp_lt_exp.mpr (by
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have : (0 : ℝ) < 1 / (8 * (d : ℝ) ^ 3) := by positivity
      rw [show (-1 : ℝ) / (8 * (d : ℝ) ^ 3) =
        -(1 / (8 * (d : ℝ) ^ 3)) by ring]
      linarith)
    _ = 1 := Real.exp_zero

/-- A rationally stated version of the volume contraction.  The weaker
constant is convenient when we later reserve part of the contraction for
rounding and inflation. -/
theorem rationalEllipsoid_volumeFactor_le_one_sub {d : ℕ} (hd : 0 < d) :
    (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) *
        (rationalEllipsoidParallelScale d : ℝ) ≤
      1 - 1 / (16 * (d : ℝ) ^ 3) := by
  let x : ℝ := 1 / (8 * (d : ℝ) ^ 3)
  have hx0 : 0 < x := by dsimp only [x]; positivity
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx1 : x ≤ 1 := by
    dsimp only [x]
    have hden : (8 : ℝ) ≤ 8 * (d : ℝ) ^ 3 := by
      nlinarith [one_le_pow₀ (n := 3) hdR]
    exact (div_le_one (by positivity : (0 : ℝ) < 8 * (d : ℝ) ^ 3)).2
      (by nlinarith)
  have hexpLower : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hrecip : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (by positivity : (0 : ℝ) < Real.exp x)
      (by positivity : (0 : ℝ) < 1 + x)).2 hexpLower
  have hrational : 1 / (1 + x) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + x)]
    nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx1)]
  calc
    (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) *
          (rationalEllipsoidParallelScale d : ℝ) ≤
        Real.exp (-1 / (8 * (d : ℝ) ^ 3)) :=
      rationalEllipsoid_volumeFactor_le_exp_neg hd
    _ = Real.exp (-x) := by
      congr 1
      dsimp only [x]
      ring
    _ ≤ 1 / (1 + x) := hrecip
    _ ≤ 1 - x / 2 := hrational
    _ = 1 - 1 / (16 * (d : ℝ) ^ 3) := by
      dsimp only [x]
      ring

/-- Rank-one linear update with prescribed scale `A` orthogonal to `b` and
scale `p` parallel to `b`. -/
def directionUpdateMatrix {d : ℕ} {R : Type*}
    [Field R] [DecidableEq (Fin d)]
    (A p : R) (b : Fin d → R) : Matrix (Fin d) (Fin d) R :=
  fun i j ↦ A * (if i = j then 1 else 0) -
    ((A - p) / finiteNormSq b) * b i * b j

/-- Explicit inverse action for the rank-one update. -/
def directionUpdatePreimage {d : ℕ} {R : Type*}
    [Field R] (A p : R) (b x : Fin d → R) : Fin d → R :=
  fun i ↦ x i / A +
    (1 / p - 1 / A) * (finiteDot b x / finiteNormSq b) * b i

theorem directionUpdateMatrix_mulVec {d : ℕ} {R : Type*}
    [Field R] [DecidableEq (Fin d)]
    (A p : R) (b z : Fin d → R) (i : Fin d) :
    Matrix.mulVec (directionUpdateMatrix A p b) z i =
      A * z i - ((A - p) / finiteNormSq b) * b i * finiteDot b z := by
  simp only [Matrix.mulVec, directionUpdateMatrix, dotProduct, sub_mul,
    Finset.sum_sub_distrib]
  rw [show (∑ x, A * (if i = x then 1 else 0) * z x) = A * z i by simp]
  congr 1
  rw [finiteDot]
  rw [show
      ((A - p) / finiteNormSq b) * b i * (∑ j, b j * z j) =
        (((A - p) / finiteNormSq b) * b i) * (∑ j, b j * z j) by ring,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finiteDot_directionUpdatePreimage {d : ℕ}
    {A p : ℝ} {b x : Fin d → ℝ}
    (hA : A ≠ 0) (hp : p ≠ 0) (hb : finiteNormSq b ≠ 0) :
    finiteDot b (directionUpdatePreimage A p b x) =
      finiteDot b x / p := by
  simp only [finiteDot, directionUpdatePreimage, mul_add,
    Finset.sum_add_distrib]
  rw [show (∑ i, b i * (x i / A)) = (∑ i, b i * x i) / A by
    rw [Finset.sum_div]; congr 1; ext i; ring]
  rw [show
      (∑ i, b i *
        ((1 / p - 1 / A) *
          ((∑ j, b j * x j) / finiteNormSq b) * b i)) =
        (1 / p - 1 / A) *
          ((∑ j, b j * x j) / finiteNormSq b) * finiteNormSq b by
    rw [finiteNormSq, finiteDot]
    let C : ℝ := (1 / p - 1 / A) *
      ((∑ j, b j * x j) / (∑ i, b i * b i))
    change (∑ i, b i * (C * b i)) = C * ∑ i, b i * b i
    calc
      (∑ i, b i * (C * b i)) = ∑ i, C * (b i * b i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = C * ∑ i, b i * b i := by rw [Finset.mul_sum]]
  field_simp
  ring

theorem directionUpdateMatrix_preimage {d : ℕ}
    {A p : ℝ} {b x : Fin d → ℝ}
    (hA : A ≠ 0) (hp : p ≠ 0) (hb : finiteNormSq b ≠ 0) :
    Matrix.mulVec (directionUpdateMatrix A p b)
      (directionUpdatePreimage A p b x) = x := by
  ext i
  rw [directionUpdateMatrix_mulVec,
    finiteDot_directionUpdatePreimage hA hp hb]
  simp only [directionUpdatePreimage]
  field_simp
  ring

/-- Exact squared-norm formula for the explicit inverse action. -/
theorem finiteNormSq_directionUpdatePreimage {d : ℕ}
    {A p : ℝ} {b x : Fin d → ℝ}
    (hA : A ≠ 0) (hp : p ≠ 0) (hb : finiteNormSq b ≠ 0) :
    finiteNormSq (directionUpdatePreimage A p b x) =
      (finiteNormSq x - finiteDot b x ^ 2 / finiteNormSq b) / A ^ 2 +
        finiteDot b x ^ 2 / (finiteNormSq b * p ^ 2) := by
  let q := finiteDot b x
  let s := finiteNormSq b
  let k : ℝ := (1 / p - 1 / A) * (q / s)
  have hpre : directionUpdatePreimage A p b x =
      fun i ↦ (1 / A) * x i + k * b i := by
    ext i
    simp only [directionUpdatePreimage, k, q, s]
    ring
  rw [hpre, finiteNormSq_add,
    finiteNormSq_smul, finiteDot_smul_left, finiteDot_smul_right,
    finiteNormSq_smul]
  change (1 / A) ^ 2 * finiteNormSq x +
      2 * ((1 / A) * (k * finiteDot x b)) +
      k ^ 2 * finiteNormSq b = _
  have hcomm : finiteDot x b = finiteDot b x := by
    simp [finiteDot, mul_comm]
  rw [hcomm]
  dsimp only [k]
  dsimp only [q, s]
  field_simp
  ring

/-- Point relative to the shifted center, in the old ellipsoid coordinates. -/
noncomputable def directionShiftedPoint {d : ℕ} (α u : ℝ)
    (b y : Fin d → ℝ) : Fin d → ℝ :=
  fun i ↦ y i + (α / u) * b i
/-- The only scalar geometry needed for containment.  The variable `t` is
the component of a unit-ball point in the cut direction and `h` is the
actual center displacement.  A convex quadratic on `[-1,0]` is bounded by
its two endpoints. -/
theorem rationalEllipsoid_scalar_containment
    {d : ℕ} (hd : 0 < d) {t h : ℝ}
    (ht0 : t ≤ 0) (ht1 : -1 ≤ t)
    (hh0 : (rationalEllipsoidAlpha d : ℝ) / d ≤ h)
    (hh1 : h ≤ (rationalEllipsoidAlpha d : ℝ)) :
    (1 - t ^ 2) / (rationalEllipsoidPerpScale d : ℝ) ^ 2 +
        (t + h) ^ 2 / (rationalEllipsoidParallelScale d : ℝ) ^ 2 ≤ 1 := by
  let α : ℝ := (rationalEllipsoidAlpha d : ℝ)
  let A : ℝ := (rationalEllipsoidPerpScale d : ℝ)
  let p : ℝ := (rationalEllipsoidParallelScale d : ℝ)
  have hα0 : 0 < α := by
    have hq := rationalEllipsoidAlpha_pos hd
    have hc : (0 : ℝ) < (rationalEllipsoidAlpha d : ℝ) := by
      exact_mod_cast hq
    simpa only [α] using hc
  have hα1 : α ≤ 1 / 4 := by
    have hq := rationalEllipsoidAlpha_le_quarter hd
    have hc : (rationalEllipsoidAlpha d : ℝ) ≤ (((1 / 4 : ℚ) : ℝ)) :=
      Rat.cast_le.mpr hq
    norm_num at hc ⊢
    simpa only [α] using hc
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp0 : 0 < p := by
    simpa [p] using (Rat.cast_pos (K := ℝ)).mpr (rationalEllipsoidParallelScale_pos hd)
  have hp1 : p ≤ 1 := by
    simpa [p] using Rat.cast_le.mpr (rationalEllipsoidParallelScale_le_one d)
  have hA0 : 0 < A := by
    simpa [A] using (Rat.cast_pos (K := ℝ)).mpr (rationalEllipsoidPerpScale_pos d)
  have hpA : p < A := by
    simpa [p, A] using (Rat.cast_lt (K := ℝ)).mpr (rationalEllipsoidParallel_lt_perp hd)
  have hh0' : α / d ≤ h := by simpa [α] using hh0
  have hh1' : h ≤ α := by simpa [α] using hh1
  have hhpos : 0 ≤ h := by
    have : 0 < α / (d : ℝ) := div_pos hα0 (by positivity)
    linarith
  have hh_le_one : h ≤ 1 := hh1'.trans (hα1.trans (by norm_num))
  have hp : p = 1 - α / d := by
    simp [p, α, rationalEllipsoidParallelScale]
  have hA : A = 1 + 2 * α ^ 2 := by
    simp [A, α, rationalEllipsoidPerpScale]
  have hendpointNeg : (1 - h) ^ 2 / p ^ 2 ≤ 1 := by
    have hph : 1 - h ≤ p := by rw [hp]; linarith
    have honeh0 : 0 ≤ 1 - h := sub_nonneg.mpr hh_le_one
    rw [div_le_iff₀ (sq_pos_of_pos hp0)]
    nlinarith
  have hp_ge_three_quarters : 3 / 4 ≤ p := by
    rw [hp]
    have : α / (d : ℝ) ≤ 1 / 4 := by
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < d)).2 (by nlinarith)
    linarith
  have hendpointZero : 1 / A ^ 2 + h ^ 2 / p ^ 2 ≤ 1 := by
    have hh_sq : h ^ 2 ≤ α ^ 2 := by nlinarith
    have hp_sq : (9 / 16 : ℝ) ≤ p ^ 2 := by nlinarith
    have hA_sq : 1 + 4 * α ^ 2 ≤ A ^ 2 := by rw [hA]; nlinarith [sq_nonneg α]
    have hαsq : α ^ 2 ≤ 1 / 16 := by nlinarith
    have hfirst : 1 / A ^ 2 ≤ 1 / (1 + 4 * α ^ 2) := by
      exact one_div_le_one_div_of_le (by positivity) hA_sq
    have hsecond : h ^ 2 / p ^ 2 ≤ (16 / 9) * α ^ 2 := by
      have := (div_le_div_iff₀ (by positivity : (0 : ℝ) < p ^ 2)
        (by norm_num : (0 : ℝ) < 9 / 16)).2
          (by nlinarith : h ^ 2 * (9 / 16 : ℝ) ≤ α ^ 2 * p ^ 2)
      norm_num at this ⊢
      linarith
    have hsum : 1 / (1 + 4 * α ^ 2) + (16 / 9) * α ^ 2 ≤ 1 := by
      have hden : 0 < 1 + 4 * α ^ 2 := by positivity
      have hid :
          1 / (1 + 4 * α ^ 2) + (16 / 9) * α ^ 2 =
            (1 + (16 / 9) * α ^ 2 * (1 + 4 * α ^ 2)) /
              (1 + 4 * α ^ 2) := by field_simp
      rw [hid, div_le_one hden]
      nlinarith
    linarith
  have hcoef : 0 ≤ 1 / p ^ 2 - 1 / A ^ 2 := by
    have hp2 : p ^ 2 ≤ A ^ 2 := by nlinarith [hp0, hA0]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) hp2)
  have htprod : t * (t + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht0 (by linarith)
  have hchord :
      (1 - t ^ 2) / A ^ 2 + (t + h) ^ 2 / p ^ 2 ≤
        (-t) * ((1 - h) ^ 2 / p ^ 2) +
          (1 + t) * (1 / A ^ 2 + h ^ 2 / p ^ 2) := by
    have hid :
        ((-t) * ((1 - h) ^ 2 / p ^ 2) +
            (1 + t) * (1 / A ^ 2 + h ^ 2 / p ^ 2)) -
          ((1 - t ^ 2) / A ^ 2 + (t + h) ^ 2 / p ^ 2) =
        -(1 / p ^ 2 - 1 / A ^ 2) * t * (t + 1) := by ring
    rw [← sub_nonneg]
    rw [hid]
    rw [mul_assoc]
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hcoef) htprod
  calc
    (1 - t ^ 2) /
          (rationalEllipsoidPerpScale d : ℝ) ^ 2 +
        (t + h) ^ 2 /
          (rationalEllipsoidParallelScale d : ℝ) ^ 2 =
        (1 - t ^ 2) / A ^ 2 + (t + h) ^ 2 / p ^ 2 := by rfl
    _ ≤ (-t) * ((1 - h) ^ 2 / p ^ 2) +
          (1 + t) * (1 / A ^ 2 + h ^ 2 / p ^ 2) := hchord
    _ ≤ (-t) * 1 + (1 + t) * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hendpointNeg (by linarith))
        (mul_le_mul_of_nonneg_left hendpointZero (by linarith))
    _ = 1 := by ring
/-- Full-dimensional containment for the rational update.  The hypotheses on
`u` say that it approximates the Euclidean norm of `b` between factors `1`
and `sqrt d`.  The executable choice `u = sum |bᵢ|` has exactly these
properties by the two elementary inequalities proved above. -/
theorem rationalEllipsoid_direction_containment
    {d : ℕ} (hd : 0 < d) {b y : Fin d → ℝ} {u : ℝ}
    (hb : b ≠ 0) (hu : 0 < u)
    (hnormLower : finiteNormSq b ≤ u ^ 2)
    (hnormUpper : u ^ 2 ≤ d * finiteNormSq b)
    (hy : finiteNormSq y ≤ 1)
    (hcut : finiteDot b y ≤ 0) :
    finiteNormSq
        (directionUpdatePreimage
          (rationalEllipsoidPerpScale d : ℝ)
          (rationalEllipsoidParallelScale d : ℝ) b
          (directionShiftedPoint
            (rationalEllipsoidAlpha d : ℝ) u b y)) ≤ 1 := by
  let s : ℝ := finiteNormSq b
  let r : ℝ := Real.sqrt s
  let α : ℝ := (rationalEllipsoidAlpha d : ℝ)
  let A : ℝ := (rationalEllipsoidPerpScale d : ℝ)
  let p : ℝ := (rationalEllipsoidParallelScale d : ℝ)
  let q : ℝ := finiteDot b y
  let t : ℝ := q / r
  let h : ℝ := α * r / u
  let x : Fin d → ℝ := directionShiftedPoint α u b y
  have hs0 : 0 ≤ s := finiteNormSq_nonneg b
  have hsne : s ≠ 0 := by
    intro hs
    apply hb
    exact (finiteNormSq_eq_zero_iff b).1 (by simpa [s] using hs)
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsne)
  have hrpos : 0 < r := by simpa [r] using Real.sqrt_pos.2 hspos
  have hrsq : r ^ 2 = s := by simpa [r] using Real.sq_sqrt hs0
  have hApos : 0 < A := by
    simpa [A] using (Rat.cast_pos (K := ℝ)).mpr (rationalEllipsoidPerpScale_pos d)
  have hppos : 0 < p := by
    simpa [p] using (Rat.cast_pos (K := ℝ)).mpr (rationalEllipsoidParallelScale_pos hd)
  have hαpos : 0 < α := by
    simpa [α] using (Rat.cast_pos (K := ℝ)).mpr (rationalEllipsoidAlpha_pos hd)
  have hqcut : q ≤ 0 := by simpa [q] using hcut
  have ht0 : t ≤ 0 := by
    dsimp only [t]
    exact div_nonpos_of_nonpos_of_nonneg hqcut hrpos.le
  have hcauchy : q ^ 2 ≤ s * finiteNormSq y := by
    simpa [q, s] using finiteDot_sq_le_normSq_mul_normSq b y
  have htSq : t ^ 2 ≤ finiteNormSq y := by
    dsimp only [t]
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hrpos), hrsq]
    simpa [mul_comm] using hcauchy
  have htSqOne : t ^ 2 ≤ 1 := htSq.trans hy
  have htNegOne : -1 ≤ t := by nlinarith
  have hrsqrt_le_u : r ≤ u := by
    have : Real.sqrt s ≤ u :=
      (Real.sqrt_le_iff).2 ⟨hu.le, hnormLower⟩
    simpa only [r] using this
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hu_le_dsqrt : u ≤ d * r := by
    have hds : (d : ℝ) * s ≤ (d : ℝ) ^ 2 * s := by
      have : 0 ≤ (d : ℝ) := by positivity
      nlinarith
    have huSq : u ^ 2 ≤ ((d : ℝ) * r) ^ 2 := by
      calc
        u ^ 2 ≤ (d : ℝ) * s := by simpa [s] using hnormUpper
        _ ≤ (d : ℝ) ^ 2 * s := hds
        _ = ((d : ℝ) * r) ^ 2 := by rw [mul_pow, hrsq]
    have hdr0 : 0 ≤ (d : ℝ) * r := mul_nonneg (by positivity) hrpos.le
    nlinarith
  have hhLower : α / (d : ℝ) ≤ h := by
    dsimp only [h]
    have hratio : 1 / (d : ℝ) ≤ r / u := by
      exact (le_div_iff₀ hu).2 (by
        rw [one_div_mul_eq_div]
        exact (div_le_iff₀ (by positivity : (0 : ℝ) < d)).2
          (by simpa [mul_comm] using hu_le_dsqrt))
    have := mul_le_mul_of_nonneg_left hratio hαpos.le
    simpa [div_eq_mul_inv, mul_assoc] using this
  have hhUpper : h ≤ α := by
    dsimp only [h]
    have hratio : r / u ≤ 1 := (div_le_one hu).2 hrsqrt_le_u
    have := mul_le_mul_of_nonneg_left hratio hαpos.le
    calc
      α * r / u = α * (r / u) := by ring
      _ ≤ α := by simpa using this
  have hdotx : finiteDot b x = q + (α / u) * s := by
    dsimp only [x]
    change finiteDot b (fun i ↦ y i + (α / u) * b i) = _
    rw [finiteDot_add_right,
      finiteDot_smul_right]
    rw [show finiteDot b b = finiteNormSq b by rfl]
  have hnormx : finiteNormSq x =
      finiteNormSq y + 2 * (α / u) * q + (α / u) ^ 2 * s := by
    dsimp only [x]
    change finiteNormSq (fun i ↦ y i + (α / u) * b i) = _
    rw [finiteNormSq_add,
      finiteDot_smul_right, finiteNormSq_smul]
    rw [show finiteDot y b = finiteDot b y by
      simp [finiteDot, mul_comm]]
    simp only [q, s]
    ring
  have hperp :
      finiteNormSq x - finiteDot b x ^ 2 / s =
        finiteNormSq y - t ^ 2 := by
    rw [hnormx, hdotx]
    dsimp only [t]
    field_simp [hsne, hrpos.ne', hu.ne']
    ring_nf
    rw [hrsq]
    ring
  have hparallel : finiteDot b x ^ 2 / (s * p ^ 2) =
      (t + h) ^ 2 / p ^ 2 := by
    rw [hdotx]
    dsimp only [t, h]
    have hr4 : r ^ 4 = s ^ 2 := by nlinarith [hrsq]
    field_simp [hsne, hrpos.ne', hu.ne']
    ring_nf
    rw [hrsq, hr4]
    ring
  have hinverse := finiteNormSq_directionUpdatePreimage
    (A := A) (p := p) (b := b) (x := x)
    hApos.ne' hppos.ne' hsne
  have hscalar := rationalEllipsoid_scalar_containment hd ht0 htNegOne
    (by simpa [α] using hhLower) (by simpa [α] using hhUpper)
  change finiteNormSq (directionUpdatePreimage A p b x) ≤ 1
  rw [hinverse]
  change (finiteNormSq x - finiteDot b x ^ 2 / s) / A ^ 2 +
      finiteDot b x ^ 2 / (s * p ^ 2) ≤ 1
  rw [hperp, hparallel]
  calc
    (finiteNormSq y - t ^ 2) / A ^ 2 + (t + h) ^ 2 / p ^ 2 ≤
        (1 - t ^ 2) / A ^ 2 + (t + h) ^ 2 / p ^ 2 := by
      gcongr
    _ ≤ 1 := by simpa [A, p] using hscalar

/-- Casting the executable `ℓ1` normalization to the reals commutes with the
finite sum and absolute value. -/
theorem cast_cutL1Scale {d : ℕ} (b : Fin d → ℚ) :
    (cutL1Scale b : ℝ) = ∑ i, abs (b i : ℝ) := by
  simp [cutL1Scale]

theorem cast_finiteNormSq {d : ℕ} (b : Fin d → ℚ) :
    ((finiteNormSq b : ℚ) : ℝ) =
      finiteNormSq (fun i ↦ (b i : ℝ)) := by
  simp [finiteNormSq, finiteDot]

/-- Concrete containment theorem for the normalization actually computed by
the rational algorithm. -/
theorem rationalEllipsoid_direction_containment_of_rational
    {d : ℕ} (hd : 0 < d) {bq : Fin d → ℚ} {y : Fin d → ℝ}
    (hbq : bq ≠ 0) (hy : finiteNormSq y ≤ 1)
    (hcut : finiteDot (fun i ↦ (bq i : ℝ)) y ≤ 0) :
    finiteNormSq
        (directionUpdatePreimage
          (rationalEllipsoidPerpScale d : ℝ)
          (rationalEllipsoidParallelScale d : ℝ)
          (fun i ↦ (bq i : ℝ))
          (directionShiftedPoint
            (rationalEllipsoidAlpha d : ℝ) (cutL1Scale bq : ℝ)
            (fun i ↦ (bq i : ℝ)) y)) ≤ 1 := by
  let b : Fin d → ℝ := fun i ↦ (bq i : ℝ)
  have hb : b ≠ 0 := by
    intro h
    apply hbq
    ext i
    have hi := congrFun h i
    exact (Rat.cast_eq_zero (α := ℝ)).mp (by simpa [b] using hi)
  have huq := cutL1Scale_pos hbq
  have hu : 0 < (cutL1Scale bq : ℝ) := (Rat.cast_pos (K := ℝ)).mpr huq
  have hlowerQ := finiteNormSq_le_cutL1Scale_sq bq
  have hlower : finiteNormSq b ≤ (cutL1Scale bq : ℝ) ^ 2 := by
    rw [← cast_finiteNormSq bq]
    exact_mod_cast hlowerQ
  have hupperQ := cutL1Scale_sq_le_card_mul_normSq bq
  have hupper : (cutL1Scale bq : ℝ) ^ 2 ≤ d * finiteNormSq b := by
    rw [← cast_finiteNormSq bq]
    exact_mod_cast hupperQ
  exact rationalEllipsoid_direction_containment hd hb hu hlower hupper hy
    (by simpa [b] using hcut)

/-- Entirely rational state stored by the cutting-plane algorithm. -/
structure RationalEllipsoidState (d : ℕ) where
  center : Fin d → ℚ
  basis : Matrix (Fin d) (Fin d) ℚ

/-- Pull a physical cut normal back to unit-ball coordinates. -/
def rationalPulledBackNormal {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) : Fin d → ℚ :=
  fun j ↦ ∑ i, E.basis i j * a i

/-- One square-root-free central-cut update.  Division by zero is harmless in
the total Lean definition; correctness is invoked only when the pulled-back
normal is nonzero, in which case `cutL1Scale` is positive. -/
def rationalEllipsoidCentralUpdate {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    RationalEllipsoidState d :=
  let b := rationalPulledBackNormal E a
  let u := cutL1Scale b
  let α := rationalEllipsoidAlpha d
  let C := directionUpdateMatrix
    (rationalEllipsoidPerpScale d)
    (rationalEllipsoidParallelScale d) b
  { center := fun i ↦ E.center i -
      α * ∑ j, E.basis i j * (b j / u)
    basis := E.basis * C }

/-- Real point represented by rational ellipsoid data and real unit-ball
coordinates. -/
noncomputable def rationalEllipsoidPoint {d : ℕ}
    (E : RationalEllipsoidState d) (y : Fin d → ℝ) : Fin d → ℝ :=
  fun i ↦ (E.center i : ℝ) + ∑ j, (E.basis i j : ℝ) * y j

theorem cast_directionUpdateMatrix {d : ℕ}
    (A p : ℚ) (b : Fin d → ℚ) (i j : Fin d) :
    ((directionUpdateMatrix A p b i j : ℚ) : ℝ) =
      directionUpdateMatrix (A : ℝ) (p : ℝ)
        (fun k ↦ (b k : ℝ)) i j := by
  by_cases hij : i = j <;>
    simp [directionUpdateMatrix, cast_finiteNormSq, hij]

theorem cast_rationalPulledBackNormal {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) (j : Fin d) :
    (rationalPulledBackNormal E a j : ℝ) =
      ∑ i, (E.basis i j : ℝ) * (a i : ℝ) := by
  simp [rationalPulledBackNormal]

/-- The stored rational rank-one matrix sends the explicit real preimage to
the shifted old coordinate exactly. -/
theorem cast_directionUpdateMatrix_preimage {d : ℕ} (hd : 0 < d)
    {bq : Fin d → ℚ} (hbq : bq ≠ 0) {y : Fin d → ℝ} :
    Matrix.mulVec
        (fun i j ↦
          ((directionUpdateMatrix
            (rationalEllipsoidPerpScale d)
            (rationalEllipsoidParallelScale d) bq i j : ℚ) : ℝ))
        (directionUpdatePreimage
          (rationalEllipsoidPerpScale d : ℝ)
          (rationalEllipsoidParallelScale d : ℝ)
          (fun i ↦ (bq i : ℝ))
          (directionShiftedPoint
            (rationalEllipsoidAlpha d : ℝ) (cutL1Scale bq : ℝ)
            (fun i ↦ (bq i : ℝ)) y)) =
      directionShiftedPoint
        (rationalEllipsoidAlpha d : ℝ) (cutL1Scale bq : ℝ)
        (fun i ↦ (bq i : ℝ)) y := by
  let b : Fin d → ℝ := fun i ↦ (bq i : ℝ)
  have hb : b ≠ 0 := by
    intro h
    apply hbq
    ext i
    exact (Rat.cast_eq_zero (α := ℝ)).mp (by simpa [b] using congrFun h i)
  have hnorm : finiteNormSq b ≠ 0 := by
    intro h
    exact hb ((finiteNormSq_eq_zero_iff b).1 h)
  have hA : (0 : ℝ) < (rationalEllipsoidPerpScale d : ℝ) :=
    (Rat.cast_pos (K := ℝ)).mpr (rationalEllipsoidPerpScale_pos d)
  have hp : (0 : ℝ) < (rationalEllipsoidParallelScale d : ℝ) :=
    (Rat.cast_pos (K := ℝ)).mpr (rationalEllipsoidParallelScale_pos hd)
  have hinv := directionUpdateMatrix_preimage
    (A := (rationalEllipsoidPerpScale d : ℝ))
    (p := (rationalEllipsoidParallelScale d : ℝ))
    (b := b)
    (x := directionShiftedPoint
      (rationalEllipsoidAlpha d : ℝ) (cutL1Scale bq : ℝ) b y)
    hA.ne' hp.ne' hnorm
  simpa only [b, cast_directionUpdateMatrix] using hinv

/-- Every point surviving a central cut in the old ellipsoid has an explicit
unit-ball coordinate in the updated rational ellipsoid. -/
theorem rationalEllipsoidCentralUpdate_contains {d : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) {y : Fin d → ℝ}
    (hb : rationalPulledBackNormal E a ≠ 0)
    (hy : finiteNormSq y ≤ 1)
    (hcut : finiteDot
      (fun i ↦ (rationalPulledBackNormal E a i : ℝ)) y ≤ 0) :
    ∃ y' : Fin d → ℝ, finiteNormSq y' ≤ 1 ∧
      rationalEllipsoidPoint (rationalEllipsoidCentralUpdate E a) y' =
        rationalEllipsoidPoint E y := by
  let bq := rationalPulledBackNormal E a
  let b : Fin d → ℝ := fun i ↦ (bq i : ℝ)
  let y' := directionUpdatePreimage
    (rationalEllipsoidPerpScale d : ℝ)
    (rationalEllipsoidParallelScale d : ℝ) b
    (directionShiftedPoint
      (rationalEllipsoidAlpha d : ℝ) (cutL1Scale bq : ℝ) b y)
  have hbq : bq ≠ 0 := by simpa [bq] using hb
  have hy' : finiteNormSq y' ≤ 1 := by
    dsimp only [y']
    exact rationalEllipsoid_direction_containment_of_rational hd hbq hy
      (by simpa [b, bq] using hcut)
  refine ⟨y', hy', ?_⟩
  have hCy := cast_directionUpdateMatrix_preimage hd hbq (y := y)
  change Matrix.mulVec
      (fun i j ↦
        ((directionUpdateMatrix
          (rationalEllipsoidPerpScale d)
          (rationalEllipsoidParallelScale d) bq i j : ℚ) : ℝ)) y' =
      directionShiftedPoint
        (rationalEllipsoidAlpha d : ℝ) (cutL1Scale bq : ℝ) b y at hCy
  have hCyReal :
      Matrix.mulVec
          (directionUpdateMatrix
            (rationalEllipsoidPerpScale d : ℝ)
            (rationalEllipsoidParallelScale d : ℝ) b) y' =
        directionShiftedPoint
          (rationalEllipsoidAlpha d : ℝ) (cutL1Scale bq : ℝ) b y := by
    rw [← hCy]
    congr 1
    ext j k
    exact (cast_directionUpdateMatrix
      (rationalEllipsoidPerpScale d)
      (rationalEllipsoidParallelScale d) bq j k).symm
  ext i
  rw [rationalEllipsoidPoint, rationalEllipsoidPoint]
  simp only [rationalEllipsoidCentralUpdate]
  simp only [Matrix.mul_apply]
  push_cast
  change (E.center i : ℝ) -
        (rationalEllipsoidAlpha d : ℝ) *
          (∑ x, (E.basis i x : ℝ) *
            ((bq x : ℝ) / (cutL1Scale bq : ℝ))) +
      (∑ j,
        (∑ k, (E.basis i k : ℝ) *
          ((directionUpdateMatrix
            (rationalEllipsoidPerpScale d)
            (rationalEllipsoidParallelScale d) bq k j : ℚ) : ℝ)) * y' j) =
      (E.center i : ℝ) + ∑ j, (E.basis i j : ℝ) * y j
  have hbasis :
      (∑ j,
        (∑ k, (E.basis i k : ℝ) *
          (directionUpdateMatrix
            (rationalEllipsoidPerpScale d : ℝ)
            (rationalEllipsoidParallelScale d : ℝ) b k j)) * y' j) =
      ∑ k, (E.basis i k : ℝ) *
        (Matrix.mulVec
          (directionUpdateMatrix
            (rationalEllipsoidPerpScale d : ℝ)
            (rationalEllipsoidParallelScale d : ℝ) b) y') k := by
    simp only [Matrix.mulVec, dotProduct]
    calc
      (∑ j,
        (∑ k, (E.basis i k : ℝ) *
          directionUpdateMatrix
            (rationalEllipsoidPerpScale d : ℝ)
            (rationalEllipsoidParallelScale d : ℝ) b k j) * y' j) =
        ∑ j, ∑ k, (E.basis i k : ℝ) *
          (directionUpdateMatrix
            (rationalEllipsoidPerpScale d : ℝ)
            (rationalEllipsoidParallelScale d : ℝ) b k j * y' j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = ∑ k, ∑ j, (E.basis i k : ℝ) *
          (directionUpdateMatrix
            (rationalEllipsoidPerpScale d : ℝ)
            (rationalEllipsoidParallelScale d : ℝ) b k j * y' j) :=
        Finset.sum_comm
      _ = ∑ k, (E.basis i k : ℝ) *
          ∑ j, directionUpdateMatrix
            (rationalEllipsoidPerpScale d : ℝ)
            (rationalEllipsoidParallelScale d : ℝ) b k j * y' j := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
  rw [show
      (∑ j,
        (∑ k, (E.basis i k : ℝ) *
          ((directionUpdateMatrix
            (rationalEllipsoidPerpScale d)
            (rationalEllipsoidParallelScale d) bq k j : ℚ) : ℝ)) * y' j) =
      ∑ j,
        (∑ k, (E.basis i k : ℝ) *
          (directionUpdateMatrix
            (rationalEllipsoidPerpScale d : ℝ)
            (rationalEllipsoidParallelScale d : ℝ) b k j)) * y' j by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [cast_directionUpdateMatrix]
      ]
  rw [hbasis]
  rw [hCyReal]
  simp only [directionShiftedPoint]
  simp only [b]
  ring_nf
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hcancel :
      (∑ x, (rationalEllipsoidAlpha d : ℝ) *
        ((E.basis i x : ℝ) * (bq x : ℝ) *
          (cutL1Scale bq : ℝ)⁻¹)) =
      ∑ x, (rationalEllipsoidAlpha d : ℝ) *
        (cutL1Scale bq : ℝ)⁻¹ * (E.basis i x : ℝ) * (bq x : ℝ) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hcancel]
  ring

/-- Exact determinant of the rank-one direction update. -/
theorem det_directionUpdateMatrix {d : ℕ} (hd : 0 < d)
    {R : Type*} [Field R] {A p : R} (hA : A ≠ 0) {b : Fin d → R}
    (hb : finiteNormSq b ≠ 0) :
    Matrix.det (directionUpdateMatrix A p b) = A ^ (d - 1) * p := by
  let v : Fin d → R := fun i ↦ -((A - p) / (A * finiteNormSq b)) * b i
  have hform : directionUpdateMatrix A p b =
      A • (1 + Matrix.vecMulVec b v) := by
    ext i j
    change A * (if i = j then 1 else 0) -
        ((A - p) / finiteNormSq b) * b i * b j =
      A * ((if i = j then 1 else 0) + b i * v j)
    dsimp only [v]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      field_simp [hA, hb]
      ring
    · simp only [hij, ite_false, zero_add, mul_zero]
      field_simp [hA, hb]
      ring
  rw [hform, Matrix.det_smul]
  rw [Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : v ⬝ᵥ b = -(A - p) / A := by
    rw [dotProduct]
    let C : R := -((A - p) / (A * finiteNormSq b))
    change (∑ i, C * b i * b i) = _
    calc
      (∑ i, C * b i * b i) = C * ∑ i, b i * b i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = C * finiteNormSq b := by rfl
      _ = -(A - p) / A := by
        dsimp only [C]
        field_simp [hA, hb]
  rw [hdot]
  simp only [Fintype.card_fin]
  have hdle : 1 ≤ d := hd
  rw [show 1 + -(A - p) / A = p / A by
    field_simp [hA]
    ring]
  rw [show d = (d - 1) + 1 by omega, pow_succ]
  have hcancel : A * (p / A) = p := by field_simp [hA]
  calc
    A ^ (d - 1) * A * (p / A) =
        A ^ (d - 1) * (A * (p / A)) := by ring
    _ = A ^ (d - 1) * p := by rw [hcancel]

/-- Consequently the stored basis determinant contracts by the explicit
factor from `rationalEllipsoid_volumeFactor_lt_one`. -/
theorem det_rationalEllipsoidCentralUpdate {d : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hb : rationalPulledBackNormal E a ≠ 0) :
    Matrix.det (rationalEllipsoidCentralUpdate E a).basis =
      Matrix.det E.basis *
        (rationalEllipsoidPerpScale d ^ (d - 1) *
          rationalEllipsoidParallelScale d) := by
  let b := rationalPulledBackNormal E a
  have hbq : finiteNormSq b ≠ 0 := by
    intro hzero
    apply hb
    rw [finiteNormSq, finiteDot,
      Finset.sum_mul_self_eq_zero_iff] at hzero
    ext i
    exact hzero i (Finset.mem_univ i)
  rw [rationalEllipsoidCentralUpdate]
  simp only
  rw [Matrix.det_mul]
  change Matrix.det E.basis *
      Matrix.det (directionUpdateMatrix
        (rationalEllipsoidPerpScale d)
        (rationalEllipsoidParallelScale d) b) = _
  rw [det_directionUpdateMatrix hd
    (rationalEllipsoidPerpScale_pos d).ne' hbq]

/-- Apply a finite list of central cuts, in list order. -/
def rationalEllipsoidIterate {d : ℕ} :
    RationalEllipsoidState d → List (Fin d → ℚ) →
      RationalEllipsoidState d
  | E, [] => E
  | E, a :: cuts =>
      rationalEllipsoidIterate (rationalEllipsoidCentralUpdate E a) cuts

/-- Every cut in a run has a nonzero pulled-back normal at the state where it
is used.  This is exactly the side condition needed by the update proof. -/
def RationalEllipsoidCutsNonzero {d : ℕ} :
    RationalEllipsoidState d → List (Fin d → ℚ) → Prop
  | _, [] => True
  | E, a :: cuts =>
      rationalPulledBackNormal E a ≠ 0 ∧
        RationalEllipsoidCutsNonzero
          (rationalEllipsoidCentralUpdate E a) cuts

/-- Exact determinant after a finite valid rational cutting-plane run. -/
theorem det_rationalEllipsoidIterate {d : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d) (cuts : List (Fin d → ℚ))
    (hnonzero : RationalEllipsoidCutsNonzero E cuts) :
    Matrix.det (rationalEllipsoidIterate E cuts).basis =
      Matrix.det E.basis *
        (rationalEllipsoidPerpScale d ^ (d - 1) *
          rationalEllipsoidParallelScale d) ^ cuts.length := by
  induction cuts generalizing E with
  | nil => simp [rationalEllipsoidIterate]
  | cons a cuts ih =>
      rw [rationalEllipsoidIterate]
      change rationalPulledBackNormal E a ≠ 0 ∧
          RationalEllipsoidCutsNonzero
            (rationalEllipsoidCentralUpdate E a) cuts at hnonzero
      rw [ih (rationalEllipsoidCentralUpdate E a) hnonzero.2,
        det_rationalEllipsoidCentralUpdate hd E a hnonzero.1]
      simp only [List.length_cons, pow_succ]
      ring

/-- The determinant after `k` cuts is bounded by the explicit exponential
contraction. -/
theorem abs_det_rationalEllipsoidIterate_le_exp {d : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d) (cuts : List (Fin d → ℚ))
    (hnonzero : RationalEllipsoidCutsNonzero E cuts) :
    abs ((Matrix.det (rationalEllipsoidIterate E cuts).basis : ℚ) : ℝ) ≤
      abs ((Matrix.det E.basis : ℚ) : ℝ) *
        Real.exp (-(cuts.length : ℝ) / (8 * (d : ℝ) ^ 3)) := by
  let q : ℝ :=
    (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) *
      (rationalEllipsoidParallelScale d : ℝ)
  have hq0 : 0 ≤ q := by
    exact mul_nonneg (pow_nonneg
      (Rat.cast_nonneg.mpr (rationalEllipsoidPerpScale_pos d).le) _)
      (Rat.cast_nonneg.mpr (rationalEllipsoidParallelScale_pos hd).le)
  have hqexp : q ≤ Real.exp (-(1 : ℝ) / (8 * (d : ℝ) ^ 3)) := by
    simpa [q] using rationalEllipsoid_volumeFactor_le_exp_neg hd
  have hpow : q ^ cuts.length ≤
      Real.exp (-(1 : ℝ) / (8 * (d : ℝ) ^ 3)) ^ cuts.length :=
    pow_le_pow_left₀ hq0 hqexp _
  have hexp :
      Real.exp (-(1 : ℝ) / (8 * (d : ℝ) ^ 3)) ^ cuts.length =
        Real.exp (-(cuts.length : ℝ) / (8 * (d : ℝ) ^ 3)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [← hexp]
  have hdet := det_rationalEllipsoidIterate hd E cuts hnonzero
  have hdetReal :
      ((Matrix.det (rationalEllipsoidIterate E cuts).basis : ℚ) : ℝ) =
        ((Matrix.det E.basis : ℚ) : ℝ) * q ^ cuts.length := by
    have hcast := congrArg (fun x : ℚ ↦ (x : ℝ)) hdet
    simpa [q] using hcast
  rw [hdetReal, abs_mul]
  have hqabs : abs q = q := abs_of_nonneg hq0
  rw [abs_pow, hqabs]
  exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)

/-- A coordinate of a point in the Euclidean unit ball has absolute value at
most one. -/
theorem abs_coordinate_le_one_of_normSq_le_one {d : ℕ}
    {x : Fin d → ℝ} (hx : finiteNormSq x ≤ 1) (i : Fin d) :
    abs (x i) ≤ 1 := by
  have hcoord : x i * x i ≤ finiteNormSq x := by
    rw [finiteNormSq, finiteDot]
    exact Finset.single_le_sum (fun j _ ↦ mul_self_nonneg (x j))
      (Finset.mem_univ i)
  have hsquare : (abs (x i)) ^ 2 ≤ 1 := by
    rw [sq_abs, sq]
    exact hcoord.trans hx
  nlinarith [abs_nonneg (x i)]

/-- Difference matrix whose `k`th column joins two unit-ball coordinates. -/
def unitBallDifferenceMatrix {d : ℕ}
    (yPlus yMinus : Fin d → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i k ↦ yPlus k i - yMinus k i

theorem unitBallDifferenceMatrix_entry_le_two {d : ℕ}
    {yPlus yMinus : Fin d → Fin d → ℝ}
    (hplus : ∀ k, finiteNormSq (yPlus k) ≤ 1)
    (hminus : ∀ k, finiteNormSq (yMinus k) ≤ 1)
    (i k : Fin d) :
    abs (unitBallDifferenceMatrix yPlus yMinus i k) ≤ 2 := by
  rw [unitBallDifferenceMatrix]
  exact (abs_sub (yPlus k i) (yMinus k i)).trans
    (by linarith [abs_coordinate_le_one_of_normSq_le_one (hplus k) i,
      abs_coordinate_le_one_of_normSq_le_one (hminus k) i])

/-- Elementary substitute for the usual volume lower bound.  If a linear
image of the unit ball contains the `2d` endpoints of the coordinate
diameters of a radius-`r` ball, its determinant is at least `r^d / d!`.
This follows from the Leibniz determinant bound, so no measure theory is
needed. -/
theorem determinant_lower_of_coordinate_diameters {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ) {r : ℝ} (hr : 0 ≤ r)
    {yPlus yMinus : Fin d → Fin d → ℝ}
    (hplus : ∀ k, finiteNormSq (yPlus k) ≤ 1)
    (hminus : ∀ k, finiteNormSq (yMinus k) ≤ 1)
    (hdiameter : ∀ k,
      Matrix.mulVec B (fun j ↦ yPlus k j - yMinus k j) =
        fun i ↦ if i = k then 2 * r else 0) :
    r ^ d ≤ Nat.factorial d * abs (Matrix.det B) := by
  let V := unitBallDifferenceMatrix yPlus yMinus
  have hBV : B * V = (2 * r) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i k
    rw [Matrix.mul_apply]
    have hk := congrFun (hdiameter k) i
    change (∑ x, B i x * V x k) = _
    rw [show (∑ x, B i x * V x k) =
      Matrix.mulVec B (fun j ↦ yPlus k j - yMinus k j) i by rfl,
      hk]
    by_cases hik : i = k <;> simp [hik]
  have hdetEq : Matrix.det B * Matrix.det V = (2 * r) ^ d := by
    rw [← Matrix.det_mul, hBV, Matrix.det_smul, Matrix.det_one,
      mul_one, Fintype.card_fin]
  have hdetV : abs (Matrix.det V) ≤ Nat.factorial d * 2 ^ d := by
    have h := Matrix.det_le (abv := (AbsoluteValue.abs : AbsoluteValue ℝ ℝ))
      (A := V) (x := (2 : ℝ))
      (fun i k ↦ unitBallDifferenceMatrix_entry_le_two hplus hminus i k)
    simpa [Fintype.card_fin, nsmul_eq_mul] using h
  have habsEq : abs (Matrix.det B) * abs (Matrix.det V) = (2 * r) ^ d := by
    rw [← abs_mul, hdetEq, abs_of_nonneg (pow_nonneg (mul_nonneg (by norm_num) hr) _)]
  have hscaled : (2 * r) ^ d ≤
      abs (Matrix.det B) * (Nat.factorial d * 2 ^ d) := by
    rw [← habsEq]
    exact mul_le_mul_of_nonneg_left hdetV (abs_nonneg _)
  have htwo : (0 : ℝ) < 2 ^ d := by positivity
  have hrewrite : (2 * r) ^ d = 2 ^ d * r ^ d := by rw [mul_pow]
  rw [hrewrite] at hscaled
  have hscaled' : 2 ^ d * r ^ d ≤
      2 ^ d * (Nat.factorial d * abs (Matrix.det B)) := by
    calc
      2 ^ d * r ^ d ≤ abs (Matrix.det B) * (Nat.factorial d * 2 ^ d) := hscaled
      _ = 2 ^ d * (Nat.factorial d * abs (Matrix.det B)) := by ring
  exact le_of_mul_le_mul_left hscaled' htwo

/-- If a rational ellipsoid contains the coordinate endpoints of a real ball
of radius `r`, its (real-cast) basis determinant has the corresponding
algebraic lower bound.  This is the exact finite substitute for the usual
statement that containment of an inner ball gives a lower volume bound. -/
theorem rationalEllipsoid_determinant_lower_of_ball_endpoints {d : ℕ}
    (E : RationalEllipsoidState d) {z : Fin d → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hplus : ∀ k, ∃ y : Fin d → ℝ, finiteNormSq y ≤ 1 ∧
      rationalEllipsoidPoint E y =
        fun i ↦ z i + if i = k then r else 0)
    (hminus : ∀ k, ∃ y : Fin d → ℝ, finiteNormSq y ≤ 1 ∧
      rationalEllipsoidPoint E y =
        fun i ↦ z i - if i = k then r else 0) :
    r ^ d ≤ Nat.factorial d *
      abs (Matrix.det (fun i j ↦ (E.basis i j : ℝ))) := by
  classical
  choose yPlus hplusNorm hplusPoint using hplus
  choose yMinus hminusNorm hminusPoint using hminus
  apply determinant_lower_of_coordinate_diameters
    (fun i j ↦ (E.basis i j : ℝ)) hr hplusNorm hminusNorm
  intro k
  ext i
  have hp := congrFun (hplusPoint k) i
  have hm := congrFun (hminusPoint k) i
  rw [rationalEllipsoidPoint] at hp hm
  change (∑ j, (E.basis i j : ℝ) * (yPlus k j - yMinus k j)) = _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  by_cases hik : i = k <;> simp [hik] at hp hm ⊢ <;> linarith

/-- The same lower bound written directly in terms of the stored rational
determinant. -/
theorem rationalEllipsoid_storedDet_lower_of_ball_endpoints {d : ℕ}
    (E : RationalEllipsoidState d) {z : Fin d → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hplus : ∀ k, ∃ y : Fin d → ℝ, finiteNormSq y ≤ 1 ∧
      rationalEllipsoidPoint E y =
        fun i ↦ z i + if i = k then r else 0)
    (hminus : ∀ k, ∃ y : Fin d → ℝ, finiteNormSq y ≤ 1 ∧
      rationalEllipsoidPoint E y =
        fun i ↦ z i - if i = k then r else 0) :
    r ^ d ≤ Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) := by
  rw [Rat.cast_det]
  change r ^ d ≤ Nat.factorial d * abs (Matrix.det (fun i j => (E.basis i j : ℝ)))
  exact rationalEllipsoid_determinant_lower_of_ball_endpoints E hr hplus hminus

/-- The elementary estimate `exp (-1) ≤ 1/2`, derived from the power-series
lower bound `2 ≤ exp 1`. -/
theorem real_exp_neg_one_le_half :
    Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  rw [Real.exp_neg]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1 <;> norm_num
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo
  simpa [one_div] using hinv

/-- After `8 d^3 M` cuts, the analytic contraction factor is at most
`2^{-M}`.  Thus the iteration budget can be chosen using ordinary binary
lengths rather than a real logarithm. -/
theorem exp_neg_cutRatio_le_half_pow {d M k : ℕ} (hd : 0 < d)
    (hk : 8 * d ^ 3 * M ≤ k) :
    Real.exp (-(k : ℝ) / (8 * (d : ℝ) ^ 3)) ≤ (1 / 2 : ℝ) ^ M := by
  have hden : (0 : ℝ) < 8 * (d : ℝ) ^ 3 := by positivity
  have hkReal : (8 : ℝ) * (d : ℝ) ^ 3 * (M : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  have hratio : (M : ℝ) ≤ (k : ℝ) / (8 * (d : ℝ) ^ 3) := by
    rw [le_div_iff₀ hden]
    calc
      (M : ℝ) * (8 * (d : ℝ) ^ 3) =
          8 * (d : ℝ) ^ 3 * (M : ℝ) := by ring
      _ ≤ (k : ℝ) := hkReal
  calc
    Real.exp (-(k : ℝ) / (8 * (d : ℝ) ^ 3)) ≤
        Real.exp (-(M : ℝ)) := by
      rw [Real.exp_le_exp]
      convert neg_le_neg hratio using 1 <;> ring
    _ = Real.exp (-1) ^ M := by
      rw [show -(M : ℝ) = (M : ℝ) * (-1 : ℝ) by ring,
        Real.exp_nat_mul]
    _ ≤ (1 / 2 : ℝ) ^ M :=
      pow_le_pow_left₀ (Real.exp_pos (-1)).le real_exp_neg_one_le_half M

/-- The determinant upper and lower bounds sandwich every run that still
contains the endpoints of a radius-`r` ball. -/
theorem rationalEllipsoid_run_sandwich {d : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d) (cuts : List (Fin d → ℚ))
    (hnonzero : RationalEllipsoidCutsNonzero E cuts)
    {z : Fin d → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hplus : ∀ k, ∃ y : Fin d → ℝ, finiteNormSq y ≤ 1 ∧
      rationalEllipsoidPoint (rationalEllipsoidIterate E cuts) y =
        fun i ↦ z i + if i = k then r else 0)
    (hminus : ∀ k, ∃ y : Fin d → ℝ, finiteNormSq y ≤ 1 ∧
      rationalEllipsoidPoint (rationalEllipsoidIterate E cuts) y =
        fun i ↦ z i - if i = k then r else 0) :
    r ^ d ≤ Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) *
      Real.exp (-(cuts.length : ℝ) / (8 * (d : ℝ) ^ 3)) := by
  have hlower := rationalEllipsoid_storedDet_lower_of_ball_endpoints
    (rationalEllipsoidIterate E cuts) hr hplus hminus
  have hupper := abs_det_rationalEllipsoidIterate_le_exp hd E cuts hnonzero
  calc
    r ^ d ≤ Nat.factorial d *
        abs ((Matrix.det (rationalEllipsoidIterate E cuts).basis : ℚ) : ℝ) :=
      hlower
    _ ≤ Nat.factorial d *
        (abs ((Matrix.det E.basis : ℚ) : ℝ) *
          Real.exp (-(cuts.length : ℝ) / (8 * (d : ℝ) ^ 3))) := by
      exact mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg _)
    _ = Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) *
        Real.exp (-(cuts.length : ℝ) / (8 * (d : ℝ) ^ 3)) := by ring

/-- A concrete dyadic budget rules out a run that continues to contain the
inner ball. -/
theorem rationalEllipsoid_no_long_run {d M : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d) (cuts : List (Fin d → ℚ))
    (hnonzero : RationalEllipsoidCutsNonzero E cuts)
    (hlength : 8 * d ^ 3 * M ≤ cuts.length)
    {z : Fin d → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hdyadic : Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) *
      (1 / 2 : ℝ) ^ M < r ^ d)
    (hplus : ∀ k, ∃ y : Fin d → ℝ, finiteNormSq y ≤ 1 ∧
      rationalEllipsoidPoint (rationalEllipsoidIterate E cuts) y =
        fun i ↦ z i + if i = k then r else 0)
    (hminus : ∀ k, ∃ y : Fin d → ℝ, finiteNormSq y ≤ 1 ∧
      rationalEllipsoidPoint (rationalEllipsoidIterate E cuts) y =
        fun i ↦ z i - if i = k then r else 0) : False := by
  have hsandwich := rationalEllipsoid_run_sandwich hd E cuts hnonzero
    hr hplus hminus
  have hexp := exp_neg_cutRatio_le_half_pow hd hlength
  have hnonneg :
      0 ≤ Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) := by
    positivity
  have hcontract :
      Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) *
          Real.exp (-(cuts.length : ℝ) / (8 * (d : ℝ) ^ 3)) ≤
        Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) *
          (1 / 2 : ℝ) ^ M :=
    mul_le_mul_of_nonneg_left hexp hnonneg
  linarith

end BeyondBethe
