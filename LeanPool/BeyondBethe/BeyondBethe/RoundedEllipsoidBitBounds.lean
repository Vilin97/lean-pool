/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.AdaptiveRoundedEllipsoid
public import Mathlib.Tactic

/-! # Rounded Ellipsoid Bit Bounds -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Magnitude bounds for the bounded-bit ellipsoid

The estimates in this file are deliberately coarse.  Their purpose is to
show that the logarithm of every stored magnitude grows only linearly with
the number of cuts.  Together with the determinant lower bound, this gives
a global polynomial bound on the magnitude-sensitive rounding precision.
-/

theorem natCast_le_two_pow_self (n : ℕ) :
    (n : ℚ) ≤ (2 : ℚ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hone : (1 : ℚ) ≤ (2 : ℚ) ^ n := one_le_pow₀ (by norm_num)
        rw [pow_succ]
        push_cast at ih ⊢
        nlinarith

theorem factorialCast_le_two_pow_sq (d : ℕ) :
    (d.factorial : ℚ) ≤ (2 : ℚ) ^ (d ^ 2) := by
  have hfac : d.factorial ≤ d ^ d := Nat.factorial_le_pow d
  have hd : (d : ℚ) ≤ (2 : ℚ) ^ d := natCast_le_two_pow_self d
  have hpow : (d : ℚ) ^ d ≤ ((2 : ℚ) ^ d) ^ d :=
    pow_le_pow_left₀ (by positivity) hd d
  calc
    (d.factorial : ℚ) ≤ ((d ^ d : ℕ) : ℚ) := by exact_mod_cast hfac
    _ = (d : ℚ) ^ d := by norm_num
    _ ≤ ((2 : ℚ) ^ d) ^ d := hpow
    _ = (2 : ℚ) ^ (d ^ 2) := by rw [← pow_mul, pow_two]

/-- Binary exponent dominating the common adaptive-rounding denominator
when `M ≤ 2^K`. -/
def roundedEllipsoidDenominatorExponent (d K : ℕ) : ℕ :=
  12 + 8 * d + d ^ 2 + d * K

theorem roundedEllipsoidCoarseDenominator_le_two_pow
    {d K : ℕ} {M : ℚ} (hM0 : 0 ≤ M)
    (hM : M ≤ (2 : ℚ) ^ K) :
    roundedEllipsoidCoarseDenominator d M ≤
      (2 : ℚ) ^ roundedEllipsoidDenominatorExponent d K := by
  have hd : (d : ℚ) ≤ (2 : ℚ) ^ d := natCast_le_two_pow_self d
  have hdsix : (d : ℚ) ^ 6 ≤ ((2 : ℚ) ^ d) ^ 6 :=
    pow_le_pow_left₀ (by positivity) hd 6
  have hdsucc : ((d + 1 : ℕ) : ℚ) ≤ (2 : ℚ) ^ (d + 1) :=
    natCast_le_two_pow_self (d + 1)
  have hfac := factorialCast_le_two_pow_sq d
  have htwoM : 2 * M ≤ (2 : ℚ) ^ (K + 1) := by
    rw [pow_succ]
    nlinarith
  have htwoM0 : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM0
  have hlast : (2 * M) ^ d ≤ ((2 : ℚ) ^ (K + 1)) ^ d :=
    pow_le_pow_left₀ htwoM0 htwoM d
  norm_num only [Nat.cast_add, Nat.cast_one] at hdsucc
  have hexponents :
      11 + d * 6 + (d + 1) + d ^ 2 + (K + 1) * d =
        roundedEllipsoidDenominatorExponent d K := by
    rw [roundedEllipsoidDenominatorExponent]
    ring
  rw [roundedEllipsoidCoarseDenominator]
  calc
    2048 * (d : ℚ) ^ 6 * (d + 1) * d.factorial * (2 * M) ^ d ≤
        (2 : ℚ) ^ 11 * ((2 : ℚ) ^ d) ^ 6 *
          (2 : ℚ) ^ (d + 1) * (2 : ℚ) ^ (d ^ 2) *
            ((2 : ℚ) ^ (K + 1)) ^ d := by
      norm_num only [show (2048 : ℚ) = 2 ^ 11 by norm_num]
      gcongr
    _ = (2 : ℚ) ^ roundedEllipsoidDenominatorExponent d K := by
      rw [← pow_mul, ← pow_mul]
      simp only [← pow_add]
      rw [hexponents]

/-- A dyadic lower bound on the determinant and an upper bound on the basis
magnitude give an explicit upper bound on the next rounding precision. -/
theorem roundedEllipsoidPrecision_le_of_magnitude_bounds {d L K : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d)
    (hdetLower : dyadicMesh L ≤ abs (Matrix.det U.basis))
    (hM : rationalMatrixAbsBound U.basis ≤ (2 : ℚ) ^ K) :
    roundedEllipsoidPrecision U ≤
      L + roundedEllipsoidDenominatorExponent d K + 2 := by
  let M := rationalMatrixAbsBound U.basis
  let Δ := abs (Matrix.det U.basis)
  let Q := roundedEllipsoidCoarseDenominator d M
  let e := roundedEllipsoidDenominatorExponent d K
  have hΔ0 : 0 < Δ :=
    (dyadicMesh_pos L).trans_le (by simpa only [Δ] using hdetLower)
  have hdet : Matrix.det U.basis ≠ 0 := abs_pos.mp hΔ0
  have hM0 : 0 ≤ M := (rationalMatrixAbsBound_pos U.basis).le
  have hQ0 : 0 < Q := roundedEllipsoidCoarseDenominator_pos hd
    (rationalMatrixAbsBound_pos U.basis)
  have hQ : Q ≤ (2 : ℚ) ^ e := by
    simpa only [Q, M, e] using
      roundedEllipsoidCoarseDenominator_le_two_pow hM0 hM
  have hdyadic : dyadicMesh (L + e) ≤ Δ / Q := by
    rw [dyadicMesh, pow_add]
    rw [div_le_div_iff₀
      (by positivity : (0 : ℚ) < (2 : ℚ) ^ L * (2 : ℚ) ^ e) hQ0]
    have hbase : (1 : ℚ) ≤ Δ * (2 : ℚ) ^ L := by
      rw [← div_le_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ L)]
      simpa only [dyadicMesh, Δ] using hdetLower
    calc
      1 * Q = Q := by ring
      _ ≤ (2 : ℚ) ^ e := hQ
      _ = 1 * (2 : ℚ) ^ e := by ring
      _ ≤ (Δ * (2 : ℚ) ^ L) * (2 : ℚ) ^ e :=
        mul_le_mul_of_nonneg_right hbase (by positivity)
      _ = Δ * ((2 : ℚ) ^ L * (2 : ℚ) ^ e) := by ring
  have htarget : dyadicMesh (L + e) ≤ roundedEllipsoidMeshTarget U :=
    hdyadic.trans (abs_det_div_coarseDenominator_le_meshTarget hd U)
  rw [roundedEllipsoidPrecision]
  exact positiveDyadicPrecision_le_of_dyadicMesh_le
    (roundedEllipsoidMeshTarget_pos hd U hdet) htarget

theorem coordinate_sq_le_finiteNormSq_rat {d : ℕ}
    (b : Fin d → ℚ) (i : Fin d) :
    b i ^ 2 ≤ finiteNormSq b := by
  rw [finiteNormSq, finiteDot, sq]
  exact Finset.single_le_sum
    (fun j _ ↦ mul_self_nonneg (b j)) (Finset.mem_univ i)

theorem abs_mul_le_finiteNormSq_rat {d : ℕ}
    (b : Fin d → ℚ) (i j : Fin d) :
    abs (b i * b j) ≤ finiteNormSq b := by
  let x := abs (b i)
  let y := abs (b j)
  let N := finiteNormSq b
  have hxi : x ^ 2 ≤ N := by
    dsimp only [x, N]
    simpa only [sq_abs] using coordinate_sq_le_finiteNormSq_rat b i
  have hyi : y ^ 2 ≤ N := by
    dsimp only [y, N]
    simpa only [sq_abs] using coordinate_sq_le_finiteNormSq_rat b j
  have hxy : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  have hnonneg : 0 ≤ x * y := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [abs_mul]
  dsimp only [x, y, N] at hxi hyi hxy hnonneg ⊢
  nlinarith

theorem rationalEllipsoidPerpScale_le_two {d : ℕ} (hd : 0 < d) :
    rationalEllipsoidPerpScale d ≤ 2 := by
  have ha0 := rationalEllipsoidAlpha_pos hd
  have ha := rationalEllipsoidAlpha_le_quarter hd
  rw [rationalEllipsoidPerpScale]
  nlinarith [sq_nonneg (rationalEllipsoidAlpha d - 1 / 4)]

/-- Every entry of the square-root-free direction update has a universal
constant bound, independent of the scale of the cut normal. -/
theorem abs_directionUpdateMatrix_le_four {d : ℕ} (hd : 0 < d)
    {b : Fin d → ℚ} (hb : b ≠ 0) (i j : Fin d) :
    abs (directionUpdateMatrix
      (rationalEllipsoidPerpScale d)
      (rationalEllipsoidParallelScale d) b i j) ≤ 4 := by
  let A := rationalEllipsoidPerpScale d
  let P := rationalEllipsoidParallelScale d
  let N := finiteNormSq b
  have hN0 : 0 < N := by
    dsimp only [N, finiteNormSq, finiteDot]
    have hnonneg : 0 ≤ ∑ k, b k * b k :=
      Finset.sum_nonneg fun k _ ↦ mul_self_nonneg (b k)
    have hne : (∑ k, b k * b k) ≠ 0 := by
      intro hz
      apply hb
      ext k
      have hk := (Finset.sum_eq_zero_iff_of_nonneg
        (fun l (_hl : l ∈ Finset.univ) ↦ mul_self_nonneg (b l))).1
          hz k (Finset.mem_univ k)
      exact (mul_self_eq_zero.mp hk)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact (rationalEllipsoidPerpScale_pos d).le
  have hA2 : A ≤ 2 := by
    dsimp only [A]
    exact rationalEllipsoidPerpScale_le_two hd
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact (rationalEllipsoidParallelScale_pos hd).le
  have hdiff0 : 0 ≤ A - P := by
    dsimp only [A, P]
    exact sub_nonneg.mpr (rationalEllipsoidParallel_lt_perp hd).le
  have hdiff2 : A - P ≤ 2 := by linarith
  have hratio : abs (b i * b j) / N ≤ 1 := by
    rw [div_le_one hN0]
    exact abs_mul_le_finiteNormSq_rat b i j
  have hratio0 : 0 ≤ abs (b i * b j) / N :=
    div_nonneg (abs_nonneg _) hN0.le
  have hterm :
      abs (((A - P) / N) * b i * b j) ≤ 2 := by
    rw [show ((A - P) / N) * b i * b j =
      (A - P) * (b i * b j) / N by ring,
      abs_div, abs_mul, abs_of_nonneg hdiff0, abs_of_pos hN0]
    rw [div_eq_mul_inv, mul_assoc, ← div_eq_mul_inv]
    calc
      (A - P) * (abs (b i * b j) / N) ≤ 2 * 1 :=
        mul_le_mul hdiff2 hratio hratio0 (by norm_num)
      _ = 2 := by norm_num
  have hdiag : abs (A * (if i = j then 1 else 0)) ≤ 2 := by
    by_cases hij : i = j
    · simp [hij, abs_of_nonneg hA0, hA2]
    · simp [hij]
  rw [directionUpdateMatrix]
  exact (abs_sub _ _).trans (by linarith)

/-- One exact cut increases the total basis `ℓ₁` magnitude by at most a
factor `4d`. -/
theorem rationalEllipsoidCentralUpdate_basis_abs_sum_le {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hb : rationalPulledBackNormal E a ≠ 0) :
    (∑ i, ∑ j, abs ((rationalEllipsoidCentralUpdate E a).basis i j)) ≤
      4 * d * (∑ i, ∑ j, abs (E.basis i j)) := by
  let b := rationalPulledBackNormal E a
  let C := directionUpdateMatrix
    (rationalEllipsoidPerpScale d)
    (rationalEllipsoidParallelScale d) b
  have hC : ∀ i j, abs (C i j) ≤ 4 := by
    intro i j
    exact abs_directionUpdateMatrix_le_four hd hb i j
  have hentry : ∀ i j,
      abs ((rationalEllipsoidCentralUpdate E a).basis i j) ≤
        ∑ k, 4 * abs (E.basis i k) := by
    intro i j
    change abs ((E.basis * C) i j) ≤ _
    rw [Matrix.mul_apply]
    calc
      abs (∑ k, E.basis i k * C k j) ≤
          ∑ k, abs (E.basis i k * C k j) :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, 4 * abs (E.basis i k) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        nlinarith [abs_nonneg (E.basis i k), hC k j]
  calc
    (∑ i, ∑ j,
        abs ((rationalEllipsoidCentralUpdate E a).basis i j)) ≤
      ∑ i, ∑ _j : Fin d, ∑ k, 4 * abs (E.basis i k) := by
        exact Finset.sum_le_sum fun i _ ↦
          Finset.sum_le_sum fun j _ ↦ hentry i j
    _ = 4 * d * (∑ i, ∑ j, abs (E.basis i j)) := by
      simp [Finset.mul_sum]
      ring

theorem rationalMatrixAbsBound_centralUpdate_le {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hb : rationalPulledBackNormal E a ≠ 0) :
    rationalMatrixAbsBound (rationalEllipsoidCentralUpdate E a).basis ≤
      5 * d * rationalMatrixAbsBound E.basis := by
  have hsum := rationalEllipsoidCentralUpdate_basis_abs_sum_le hd E a hb
  have hdq : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hT : 0 ≤ ∑ i, ∑ j, abs (E.basis i j) :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  rw [rationalMatrixAbsBound, rationalMatrixAbsBound]
  calc
    1 + ∑ i, ∑ j,
        abs ((rationalEllipsoidCentralUpdate E a).basis i j) ≤
      1 + 4 * d * (∑ i, ∑ j, abs (E.basis i j)) :=
        by simpa only [add_comm] using add_le_add_left hsum 1
    _ ≤ 5 * d * (1 + ∑ i, ∑ j, abs (E.basis i j)) := by
      have hd0 : (0 : ℚ) ≤ d := by positivity
      nlinarith [mul_nonneg hd0 hT]

/-- Positive `ℓ₁` magnitude bounds for centers and complete states. -/
def rationalCenterAbsBound {d : ℕ} (c : Fin d → ℚ) : ℚ :=
  1 + ∑ i, abs (c i)

/-- Adds the rational absolute bounds for an ellipsoid state's center and basis matrix. -/
def rationalStateAbsBound {d : ℕ} (E : RationalEllipsoidState d) : ℚ :=
  rationalCenterAbsBound E.center + rationalMatrixAbsBound E.basis

theorem rationalCenterAbsBound_one_le {d : ℕ} (c : Fin d → ℚ) :
    1 ≤ rationalCenterAbsBound c := by
  rw [rationalCenterAbsBound]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)

theorem rationalStateAbsBound_two_le {d : ℕ}
    (E : RationalEllipsoidState d) :
    2 ≤ rationalStateAbsBound E := by
  rw [rationalStateAbsBound]
  linarith [rationalCenterAbsBound_one_le E.center,
    rationalMatrixAbsBound_one_le E.basis]

theorem rationalMatrixAbsBound_le_rationalStateAbsBound {d : ℕ}
    (E : RationalEllipsoidState d) :
    rationalMatrixAbsBound E.basis ≤ rationalStateAbsBound E := by
  rw [rationalStateAbsBound]
  linarith [rationalCenterAbsBound_one_le E.center]

theorem abs_div_cutL1Scale_le_one {d : ℕ} {b : Fin d → ℚ}
    (hb : b ≠ 0) (j : Fin d) :
    abs (b j / cutL1Scale b) ≤ 1 := by
  have hu := cutL1Scale_pos hb
  rw [abs_div, abs_of_pos hu, div_le_one hu]
  rw [cutL1Scale]
  exact Finset.single_le_sum (fun k _ ↦ abs_nonneg (b k))
    (Finset.mem_univ j)

theorem rationalCenterAbsBound_centralUpdate_le {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hb : rationalPulledBackNormal E a ≠ 0) :
    rationalCenterAbsBound (rationalEllipsoidCentralUpdate E a).center ≤
      rationalCenterAbsBound E.center + rationalMatrixAbsBound E.basis := by
  let b := rationalPulledBackNormal E a
  let u := cutL1Scale b
  let α := rationalEllipsoidAlpha d
  have hα0 : 0 ≤ α := by
    dsimp only [α]
    exact (rationalEllipsoidAlpha_pos hd).le
  have hα1 : α ≤ 1 := by
    dsimp only [α]
    exact (rationalEllipsoidAlpha_le_quarter hd).trans (by norm_num)
  have hratio : ∀ j, abs (b j / u) ≤ 1 := by
    intro j
    simpa only [b, u] using abs_div_cutL1Scale_le_one hb j
  have hentry : ∀ i,
      abs ((rationalEllipsoidCentralUpdate E a).center i) ≤
        abs (E.center i) + ∑ j, abs (E.basis i j) := by
    intro i
    change abs (E.center i - α * ∑ j, E.basis i j * (b j / u)) ≤ _
    calc
      abs (E.center i - α * ∑ j, E.basis i j * (b j / u)) ≤
          abs (E.center i) + abs (α * ∑ j,
            E.basis i j * (b j / u)) := abs_sub _ _
      _ ≤ abs (E.center i) + α *
          ∑ j, abs (E.basis i j * (b j / u)) := by
        rw [abs_mul, abs_of_nonneg hα0]
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ abs (E.center i) + α * ∑ j, abs (E.basis i j) := by
        have hs : (∑ j, abs (E.basis i j * (b j / u))) ≤
            ∑ j, abs (E.basis i j) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (hratio j) (abs_nonneg (E.basis i j))
        have hm := mul_le_mul_of_nonneg_left hs hα0
        simpa only [add_comm] using
          add_le_add_left hm (abs (E.center i))
      _ ≤ abs (E.center i) + ∑ j, abs (E.basis i j) := by
        have hrow : 0 ≤ ∑ j, abs (E.basis i j) :=
          Finset.sum_nonneg fun j _ ↦ abs_nonneg _
        nlinarith
  rw [rationalCenterAbsBound, rationalCenterAbsBound,
    rationalMatrixAbsBound]
  calc
    1 + ∑ i,
        abs ((rationalEllipsoidCentralUpdate E a).center i) ≤
      1 + ∑ i, (abs (E.center i) + ∑ j, abs (E.basis i j)) := by
        gcongr with i
        exact hentry i
    _ = (1 + ∑ i, abs (E.center i)) +
        (1 + ∑ i, ∑ j, abs (E.basis i j)) - 1 := by
      rw [Finset.sum_add_distrib]
      ring
    _ ≤ (1 + ∑ i, abs (E.center i)) +
        (1 + ∑ i, ∑ j, abs (E.basis i j)) := by linarith

theorem rationalStateAbsBound_centralUpdate_le {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hb : rationalPulledBackNormal E a ≠ 0) :
    rationalStateAbsBound (rationalEllipsoidCentralUpdate E a) ≤
      6 * d * rationalStateAbsBound E := by
  have hc := rationalCenterAbsBound_centralUpdate_le hd E a hb
  have hB := rationalMatrixAbsBound_centralUpdate_le hd E a hb
  have hdq : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hc0 := rationalCenterAbsBound_one_le E.center
  have hB0 := rationalMatrixAbsBound_one_le E.basis
  rw [rationalStateAbsBound, rationalStateAbsBound]
  calc
    rationalCenterAbsBound (rationalEllipsoidCentralUpdate E a).center +
        rationalMatrixAbsBound (rationalEllipsoidCentralUpdate E a).basis ≤
      (rationalCenterAbsBound E.center + rationalMatrixAbsBound E.basis) +
        5 * d * rationalMatrixAbsBound E.basis := add_le_add hc hB
    _ ≤ 6 * d *
        (rationalCenterAbsBound E.center + rationalMatrixAbsBound E.basis) := by
      have hd0 : (0 : ℚ) ≤ d := by positivity
      have hBnonneg : 0 ≤ rationalMatrixAbsBound E.basis := by linarith
      nlinarith [mul_nonneg hd0 hBnonneg]

theorem roundedEllipsoidInflation_le_one {d : ℕ} (hd : 0 < d) :
    roundedEllipsoidInflation d ≤ 1 := by
  rw [roundedEllipsoidInflation]
  have hden : (1 : ℚ) ≤ 1024 * d ^ 4 := by
    have hdq : (1 : ℚ) ≤ d := by exact_mod_cast hd
    have hd4 : (1 : ℚ) ≤ (d : ℚ) ^ 4 := one_le_pow₀ hdq
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith
  exact (div_le_one (by positivity : (0 : ℚ) < 1024 * d ^ 4)).2 hden

/-- Rounding and inflation preserve a polynomial one-step magnitude bound. -/
theorem rationalMatrixAbsBound_adaptiveRounded_le {d : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d) :
    rationalMatrixAbsBound (adaptiveRoundedEllipsoid U).basis ≤
      5 * d ^ 2 * rationalMatrixAbsBound U.basis := by
  let M := rationalMatrixAbsBound U.basis
  let p := roundedEllipsoidPrecision U
  let η := roundedEllipsoidInflation d
  have hM1 : (1 : ℚ) ≤ M := rationalMatrixAbsBound_one_le U.basis
  have hη0 : 0 ≤ η := by
    dsimp only [η]
    exact roundedEllipsoidInflation_nonneg d
  have hη1 : η ≤ 1 := by
    dsimp only [η]
    exact roundedEllipsoidInflation_le_one hd
  have hentry : ∀ i j,
      abs ((adaptiveRoundedEllipsoid U).basis i j) ≤ 4 * M := by
    intro i j
    have hround := abs_dyadicFloor_le p (U.basis i j)
    have hmesh := dyadicMesh_le_one p
    have hU := (abs_entry_lt_rationalMatrixAbsBound U.basis i j).le
    have hfloor : abs (dyadicFloor p (U.basis i j)) ≤ 2 * M := by
      linarith
    rw [adaptiveRoundedEllipsoid, inflatedDyadicRound_basis_apply, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ 1 + η)]
    calc
      (1 + η) * abs (dyadicFloor p (U.basis i j)) ≤ 2 * (2 * M) :=
        mul_le_mul (by linarith) hfloor (abs_nonneg _) (by linarith)
      _ = 4 * M := by ring
  rw [rationalMatrixAbsBound]
  calc
    1 + ∑ i, ∑ j, abs ((adaptiveRoundedEllipsoid U).basis i j) ≤
        1 + ∑ _i : Fin d, ∑ _j : Fin d, 4 * M := by
      have hs0 : (∑ i : Fin d, ∑ j : Fin d,
          abs ((adaptiveRoundedEllipsoid U).basis i j)) ≤
          ∑ _i : Fin d, ∑ _j : Fin d, 4 * M := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact hentry i j
      have hs := add_le_add_left hs0 1
      simpa only [add_comm] using hs
    _ = 1 + d ^ 2 * (4 * M) := by simp; ring
    _ ≤ 5 * d ^ 2 * M := by
      have hdq : (1 : ℚ) ≤ d := by exact_mod_cast hd
      nlinarith [sq_nonneg ((d : ℚ) - 1)]

theorem rationalCenterAbsBound_adaptiveRounded_le {d : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d) :
    rationalCenterAbsBound (adaptiveRoundedEllipsoid U).center ≤
      rationalCenterAbsBound U.center + d := by
  let p := roundedEllipsoidPrecision U
  have hentry : ∀ i,
      abs ((adaptiveRoundedEllipsoid U).center i) ≤ abs (U.center i) + 1 := by
    intro i
    have h := abs_dyadicFloor_le p (U.center i)
    have hm := dyadicMesh_le_one p
    have hadd : abs (U.center i) + dyadicMesh p ≤
        abs (U.center i) + 1 := by linarith
    change abs (dyadicFloor p (U.center i)) ≤ abs (U.center i) + 1
    exact h.le.trans hadd
  rw [rationalCenterAbsBound, rationalCenterAbsBound]
  calc
    1 + ∑ i, abs ((adaptiveRoundedEllipsoid U).center i) ≤
      1 + ∑ i, (abs (U.center i) + 1) := by
        gcongr with i
        exact hentry i
    _ = (1 + ∑ i, abs (U.center i)) + d := by
      rw [Finset.sum_add_distrib]
      simp
      ring

theorem rationalStateAbsBound_adaptiveRounded_le {d : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d) :
    rationalStateAbsBound (adaptiveRoundedEllipsoid U) ≤
      7 * d ^ 2 * rationalStateAbsBound U := by
  have hc := rationalCenterAbsBound_adaptiveRounded_le hd U
  have hB := rationalMatrixAbsBound_adaptiveRounded_le hd U
  have hdq : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hT := rationalStateAbsBound_two_le U
  have hc0 := rationalCenterAbsBound_one_le U.center
  have hB0 := rationalMatrixAbsBound_one_le U.basis
  rw [rationalStateAbsBound, rationalStateAbsBound]
  calc
    rationalCenterAbsBound (adaptiveRoundedEllipsoid U).center +
        rationalMatrixAbsBound (adaptiveRoundedEllipsoid U).basis ≤
      (rationalCenterAbsBound U.center + d) +
        5 * d ^ 2 * rationalMatrixAbsBound U.basis := add_le_add hc hB
    _ ≤ 7 * d ^ 2 *
        (rationalCenterAbsBound U.center + rationalMatrixAbsBound U.basis) := by
      have hBnonneg : 0 ≤ rationalMatrixAbsBound U.basis := by linarith
      nlinarith [sq_nonneg ((d : ℚ) - 1),
        mul_nonneg (sq_nonneg (d : ℚ)) hBnonneg]

/-- A complete rounded cut grows the total basis magnitude by at most
`25 d³`. -/
theorem rationalMatrixAbsBound_adaptiveCentralUpdate_le {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hb : rationalPulledBackNormal E a ≠ 0) :
    rationalMatrixAbsBound
        (adaptiveRoundedEllipsoidCentralUpdate E a).basis ≤
      25 * d ^ 3 * rationalMatrixAbsBound E.basis := by
  let U := rationalEllipsoidCentralUpdate E a
  have hround := rationalMatrixAbsBound_adaptiveRounded_le hd U
  have hexact := rationalMatrixAbsBound_centralUpdate_le hd E a hb
  calc
    rationalMatrixAbsBound
        (adaptiveRoundedEllipsoidCentralUpdate E a).basis =
      rationalMatrixAbsBound (adaptiveRoundedEllipsoid U).basis := by rfl
    _ ≤ 5 * d ^ 2 * rationalMatrixAbsBound U.basis := hround
    _ ≤ 5 * d ^ 2 * (5 * d * rationalMatrixAbsBound E.basis) :=
      mul_le_mul_of_nonneg_left hexact (by positivity)
    _ = 25 * d ^ 3 * rationalMatrixAbsBound E.basis := by ring

theorem rationalStateAbsBound_adaptiveCentralUpdate_le {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hb : rationalPulledBackNormal E a ≠ 0) :
    rationalStateAbsBound (adaptiveRoundedEllipsoidCentralUpdate E a) ≤
      42 * d ^ 3 * rationalStateAbsBound E := by
  let U := rationalEllipsoidCentralUpdate E a
  have hround := rationalStateAbsBound_adaptiveRounded_le hd U
  have hexact := rationalStateAbsBound_centralUpdate_le hd E a hb
  calc
    rationalStateAbsBound (adaptiveRoundedEllipsoidCentralUpdate E a) =
      rationalStateAbsBound (adaptiveRoundedEllipsoid U) := by rfl
    _ ≤ 7 * d ^ 2 * rationalStateAbsBound U := hround
    _ ≤ 7 * d ^ 2 * (6 * d * rationalStateAbsBound E) :=
      mul_le_mul_of_nonneg_left hexact (by positivity)
    _ = 42 * d ^ 3 * rationalStateAbsBound E := by ring

end BeyondBethe
