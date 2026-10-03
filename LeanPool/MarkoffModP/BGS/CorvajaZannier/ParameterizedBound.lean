/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# The parameterized numerical bound in Corvaja--Zannier Theorem 4

This file isolates the real and natural-number optimization in the proof of
Corvaja--Zannier, JEMS 15 (2013), Theorem 4.  The curve-theoretic content of
their Proposition 2 is an ordinary proposition-valued hypothesis below.  No
function-field or valuation statement is assumed through a typeclass.

The source chooses

`h = floor (t * (b^2 / (a * chi))^(1/3)) - 1` and
`k = floor (t * (a^2 / (b * chi))^(1/3)) - 1`.

The proof below retains that choice and checks the small-`k`, degree-
alternative, parameter-admissibility, and numerical-bound cases separately.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

/-- The natural parameters to which the numerical form of Corvaja--Zannier
Proposition 2 applies.  Positivity of `h * k + h + k` records that the
denominator in Proposition 2 is meaningful. -/
def PropositionTwoParametersAreAdmissible
    (a b p h k : ℕ) : Prop :=
  0 < h * k + h + k ∧ a * h + b * k < p

/-- The two alternatives supplied by the numerical part of
Corvaja--Zannier Proposition 2.

Here `a = deg(v)`, `b = deg(u)`, `chi` is the Euler characteristic, and `G`
is the gcd sum.  This is deliberately an ordinary `Prop`, not a structure,
class, or axiom. -/
def PropositionTwoNumericalAlternatives
    (a b p chi : ℕ) (G : ℝ) : Prop :=
  ∀ h k : ℕ,
    PropositionTwoParametersAreAdmissible a b p h k →
      (a ≤ k ∧ b ≤ h) ∨
        G ≤
          (((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * (a : ℝ) +
          ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * (b : ℝ) +
          ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ)

private theorem rpow_one_third_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

private theorem lt_natFloor_sub_one_add_two (x : ℝ) :
    x < ((⌊x⌋₊ - 1 : ℕ) : ℝ) + 2 := by
  have hfloor := Nat.lt_floor_add_one x
  have hnat : ⌊x⌋₊ + 1 ≤ (⌊x⌋₊ - 1) + 2 := by omega
  exact hfloor.trans_le (by exact_mod_cast hnat)

private theorem natFloor_sub_one_add_one_le
    {x : ℝ} (hx : 0 ≤ x) (hfloor : 1 ≤ ⌊x⌋₊) :
    (((⌊x⌋₊ - 1 : ℕ) : ℝ) + 1) ≤ x := by
  have hnat : ⌊x⌋₊ - 1 + 1 = ⌊x⌋₊ := Nat.sub_add_cancel hfloor
  have hcast : (((⌊x⌋₊ - 1 : ℕ) : ℝ) + 1) = (⌊x⌋₊ : ℝ) := by
    exact_mod_cast hnat
  rw [hcast]
  exact Nat.floor_le hx

private theorem propositionTwo_first_coefficient_le
    {h k : ℝ} (hkPos : 0 < k) (hk : k ≤ h) :
    (h + 2 * k) / (h * k + h + k) ≤ 3 / (k + 2) := by
  have hhPos : 0 < h := lt_of_lt_of_le hkPos hk
  have hnPos : 0 < h * k + h + k := by positivity
  have hkTwoPos : 0 < k + 2 := by positivity
  rw [div_le_div_iff₀ hnPos hkTwoPos]
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) (by positivity : 0 ≤ 2 * k + 1)]

private theorem propositionTwo_second_coefficient_le
    {h k : ℝ} (hkPos : 0 < k) (hk : k ≤ h) :
    k / (h * k + h + k) ≤ 1 / (h + 2) := by
  have hhPos : 0 < h := lt_of_lt_of_le hkPos hk
  have hnPos : 0 < h * k + h + k := by positivity
  have hhTwoPos : 0 < h + 2 := by positivity
  rw [div_le_div_iff₀ hnPos hhTwoPos]
  nlinarith

private theorem sqrt_le_theoremFour_coefficient {t : ℝ} (ht : 0 < t) :
    Real.sqrt t ≤ 4 / t + t ^ 2 / 2 := by
  have hsqrtNonneg : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  apply (mul_le_mul_iff_right₀ ht).mp
  have hfour : t * (4 / t) = 4 := by field_simp [ht.ne']
  rw [mul_add, hfour]
  have htsqrt : t * Real.sqrt t = (Real.sqrt t) ^ 3 := by
    calc
      t * Real.sqrt t = (Real.sqrt t) ^ 2 * Real.sqrt t := by rw [hsqrtSq]
      _ = (Real.sqrt t) ^ 3 := by ring
  have htquadratic : t * (t ^ 2 / 2) = (Real.sqrt t) ^ 6 / 2 := by
    calc
      t * (t ^ 2 / 2) = t ^ 3 / 2 := by ring
      _ = ((Real.sqrt t) ^ 2) ^ 3 / 2 := by rw [hsqrtSq]
      _ = (Real.sqrt t) ^ 6 / 2 := by ring
  rw [htsqrt, htquadratic]
  nlinarith [sq_nonneg ((Real.sqrt t) ^ 3 - 1)]

private theorem degree_le_theoremFour_bound_of_sq_le_cube
    {degree root t : ℝ} (hdegree : 0 ≤ degree) (hroot : 0 ≤ root)
    (ht : 0 < t) (hSq : degree ^ 2 ≤ root ^ 3) (hrootLe : root ≤ t) :
    degree ≤ (4 / t + t ^ 2 / 2) * root := by
  have hrootCube : 0 ≤ root ^ 3 := pow_nonneg hroot _
  have hdegreeLeSqrt : degree ≤ Real.sqrt (root ^ 3) := by
    exact (sq_le_sq₀ hdegree (Real.sqrt_nonneg _)).mp
      (hSq.trans_eq (Real.sq_sqrt hrootCube).symm)
  have hsqrtCube : Real.sqrt (root ^ 3) = root * Real.sqrt root := by
    have hproductNonneg : 0 ≤ root * Real.sqrt root :=
      mul_nonneg hroot (Real.sqrt_nonneg _)
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hproductNonneg).mp
    calc
      (Real.sqrt (root ^ 3)) ^ 2 = root ^ 3 := Real.sq_sqrt hrootCube
      _ = (root * Real.sqrt root) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hroot]
        ring
  have hsqrtRootLe : Real.sqrt root ≤ Real.sqrt t := Real.sqrt_le_sqrt hrootLe
  have hsqrtTCoefficient := sqrt_le_theoremFour_coefficient ht
  calc
    degree ≤ Real.sqrt (root ^ 3) := hdegreeLeSqrt
    _ = root * Real.sqrt root := hsqrtCube
    _ ≤ root * Real.sqrt t := mul_le_mul_of_nonneg_left hsqrtRootLe hroot
    _ ≤ root * (4 / t + t ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hsqrtTCoefficient hroot
    _ = (4 / t + t ^ 2 / 2) * root := mul_comm _ _

private theorem propositionTwo_numerical_bound
    {a b chi : ℕ} {t G : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hchi : 0 < chi) (ht : 0 < t) :
  let A : ℝ := a
  let B : ℝ := b
  let C : ℝ := chi
  let base : ℝ := A * B * C
  let baseRoot : ℝ := base ^ ((1 : ℝ) / 3)
  let hScale : ℝ := (B ^ 2 / (A * C)) ^ ((1 : ℝ) / 3)
  let kScale : ℝ := (A ^ 2 / (B * C)) ^ ((1 : ℝ) / 3)
  let xH : ℝ := t * hScale
  let xK : ℝ := t * kScale
  let h : ℕ := ⌊xH⌋₊ - 1
  let k : ℕ := ⌊xK⌋₊ - 1
  0 < k → k ≤ h →
    G ≤ (((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * A +
      ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * B +
      ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * C →
    G ≤ (4 / t + t ^ 2 / 2) * baseRoot := by
  intro A B C base baseRoot hScale kScale xH xK h k hkPos hkh hNumerical
  have hAPos : 0 < A := by dsimp [A]; exact_mod_cast ha
  have hBPos : 0 < B := by
    dsimp [B]
    exact_mod_cast hb
  have hCPos : 0 < C := by dsimp [C]; exact_mod_cast hchi
  have hbasePos : 0 < base := by dsimp [base]; positivity
  have hbaseRootPos : 0 < baseRoot := by dsimp [baseRoot]; positivity
  have hbaseRootCube : baseRoot ^ 3 = base := by
    simpa [baseRoot] using rpow_one_third_cube hbasePos.le
  have hhRadicandPos : 0 < B ^ 2 / (A * C) := by positivity
  have hkRadicandPos : 0 < A ^ 2 / (B * C) := by positivity
  have hhScalePos : 0 < hScale := by dsimp [hScale]; positivity
  have hkScalePos : 0 < kScale := by dsimp [kScale]; positivity
  have hhScaleCube : hScale ^ 3 = B ^ 2 / (A * C) := by
    simpa [hScale] using rpow_one_third_cube hhRadicandPos.le
  have hkScaleCube : kScale ^ 3 = A ^ 2 / (B * C) := by
    simpa [kScale] using rpow_one_third_cube hkRadicandPos.le
  have hxHPos : 0 < xH := by dsimp [xH]; positivity
  have hxKPos : 0 < xK := by dsimp [xK]; positivity
  have hAdivKScale : A / kScale = baseRoot := by
    apply (pow_left_inj₀ (by positivity) hbaseRootPos.le
      (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [div_pow, hkScaleCube, hbaseRootCube]
    dsimp [base]
    field_simp [hAPos.ne', hBPos.ne', hCPos.ne']
  have hBdivHScale : B / hScale = baseRoot := by
    apply (pow_left_inj₀ (by positivity) hbaseRootPos.le
      (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [div_pow, hhScaleCube, hbaseRootCube]
    dsimp [base]
    field_simp [hAPos.ne', hBPos.ne', hCPos.ne']
  have hscaleProduct : hScale * kScale * C = baseRoot := by
    apply (pow_left_inj₀ (by positivity) hbaseRootPos.le
      (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [mul_pow, mul_pow, hhScaleCube, hkScaleCube, hbaseRootCube]
    dsimp [base]
    field_simp [hAPos.ne', hBPos.ne', hCPos.ne']
  have hhPos : 0 < h := lt_of_lt_of_le hkPos hkh
  have hkFloorOne : 1 ≤ ⌊xK⌋₊ := by
    dsimp [k] at hkPos
    omega
  have hhFloorOne : 1 ≤ ⌊xH⌋₊ := by
    dsimp [h] at hhPos
    omega
  have hkFloorUpper : ((k : ℝ) + 1) ≤ xK := by
    simpa [k] using natFloor_sub_one_add_one_le hxKPos.le hkFloorOne
  have hhFloorUpper : ((h : ℝ) + 1) ≤ xH := by
    simpa [h] using natFloor_sub_one_add_one_le hxHPos.le hhFloorOne
  have hnPos : 0 < h * k + h + k := by omega
  let H : ℝ := h
  let K : ℝ := k
  let N : ℝ := h * k + h + k
  have hKPos : 0 < K := by dsimp [K]; exact_mod_cast hkPos
  have hKLeH : K ≤ H := by dsimp [K, H]; exact_mod_cast hkh
  have hNPos : 0 < N := by dsimp [N]; exact_mod_cast hnPos
  have hFirstCoefficient : (H + 2 * K) / N ≤ 3 / (K + 2) := by
    simpa [H, K, N, Nat.cast_add, Nat.cast_mul] using
      propositionTwo_first_coefficient_le hKPos hKLeH
  have hSecondCoefficient : K / N ≤ 1 / (H + 2) := by
    simpa [H, K, N, Nat.cast_add, Nat.cast_mul] using
      propositionTwo_second_coefficient_le hKPos hKLeH
  have hxKDenominator : xK ≤ K + 2 := by
    simpa [K, k] using (lt_natFloor_sub_one_add_two xK).le
  have hxHDenominator : xH ≤ H + 2 := by
    simpa [H, h] using (lt_natFloor_sub_one_add_two xH).le
  have hADiv : A / (K + 2) ≤ baseRoot / t := by
    calc
      A / (K + 2) ≤ A / xK :=
        div_le_div_of_nonneg_left hAPos.le hxKPos hxKDenominator
      _ = baseRoot / t := by
        dsimp [xK]
        rw [show A / (t * kScale) = (A / kScale) / t by
          field_simp [ht.ne', hkScalePos.ne']]
        rw [hAdivKScale]
  have hBDiv : B / (H + 2) ≤ baseRoot / t := by
    calc
      B / (H + 2) ≤ B / xH :=
        div_le_div_of_nonneg_left hBPos.le hxHPos hxHDenominator
      _ = baseRoot / t := by
        dsimp [xH]
        rw [show B / (t * hScale) = (B / hScale) / t by
          field_simp [ht.ne', hhScalePos.ne']]
        rw [hBdivHScale]
  have hFirstTerm : ((H + 2 * K) / N) * A ≤ (3 / t) * baseRoot := by
    calc
      ((H + 2 * K) / N) * A ≤ (3 / (K + 2)) * A :=
        mul_le_mul_of_nonneg_right hFirstCoefficient hAPos.le
      _ = 3 * (A / (K + 2)) := by ring
      _ ≤ 3 * (baseRoot / t) :=
        mul_le_mul_of_nonneg_left hADiv (by norm_num)
      _ = (3 / t) * baseRoot := by ring
  have hSecondTerm : (K / N) * B ≤ (1 / t) * baseRoot := by
    calc
      (K / N) * B ≤ (1 / (H + 2)) * B :=
        mul_le_mul_of_nonneg_right hSecondCoefficient hBPos.le
      _ = B / (H + 2) := by ring
      _ ≤ baseRoot / t := hBDiv
      _ = (1 / t) * baseRoot := by ring
  have hFloorProduct : (H + 1) * (K + 1) ≤ xH * xK := by
    have hhFloorUpper' : H + 1 ≤ xH := by simpa [H] using hhFloorUpper
    have hkFloorUpper' : K + 1 ≤ xK := by simpa [K] using hkFloorUpper
    exact mul_le_mul hhFloorUpper' hkFloorUpper' (by positivity) (by positivity)
  have hThirdNumerator : N - 1 ≤ (H + 1) * (K + 1) := by
    dsimp [N, H, K]
    ring_nf
    norm_num
  have hThirdTerm : ((N - 1) / 2) * C ≤ (t ^ 2 / 2) * baseRoot := by
    calc
      ((N - 1) / 2) * C ≤ (((H + 1) * (K + 1)) / 2) * C := by
        gcongr
      _ ≤ ((xH * xK) / 2) * C := by
        gcongr
      _ = (t ^ 2 / 2) * baseRoot := by
        dsimp [xH, xK]
        rw [← hscaleProduct]
        ring
  have hNumerical' :
      G ≤ ((H + 2 * K) / N) * A + (K / N) * B + ((N - 1) / 2) * C := by
    simpa only [H, K, N, A, B, C, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hNumerical
  calc
    G ≤ ((H + 2 * K) / N) * A + (K / N) * B + ((N - 1) / 2) * C :=
      hNumerical'
    _ ≤ (3 / t) * baseRoot + (1 / t) * baseRoot +
        (t ^ 2 / 2) * baseRoot :=
      add_le_add (add_le_add hFirstTerm hSecondTerm) hThirdTerm
    _ = (4 / t + t ^ 2 / 2) * baseRoot := by ring

/-- The floor-parameter optimization in Corvaja--Zannier Theorem 4.

The hypothesis `hPropositionTwo` is exactly the numerical alternative of
Proposition 2, supplied for every admissible pair of natural parameters.
All remaining hypotheses are elementary: positive natural degrees and Euler
characteristic, positive characteristic and real parameter, a nonnegative gcd
quantity, and its trivial upper bound by the smaller degree. -/
theorem theoremFour_parameterizedBound_of_propositionTwo
    (a b chi p : ℕ) (G t : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hchi : 0 < chi) (hp : 0 < p)
    (hGNonneg : 0 ≤ G) (hGTrivial : G ≤ (a : ℝ)) (ht : 0 < t)
    (hPropositionTwo : PropositionTwoNumericalAlternatives a b p chi G)
    (hSize :
      ((a : ℝ) * (b : ℝ)) ^ 2 <
        (((p : ℝ) + (a : ℝ) + (b : ℝ)) ^ 3 * (chi : ℝ)) /
          (8 * t ^ 3)) :
    G ≤ (4 / t + t ^ 2 / 2) *
      ((a : ℝ) * (b : ℝ) * (chi : ℝ)) ^ ((1 : ℝ) / 3) := by
  let A : ℝ := a
  let B : ℝ := b
  let C : ℝ := chi
  let P : ℝ := p
  let base : ℝ := A * B * C
  let baseRoot : ℝ := base ^ ((1 : ℝ) / 3)
  let hScale : ℝ := (B ^ 2 / (A * C)) ^ ((1 : ℝ) / 3)
  let kScale : ℝ := (A ^ 2 / (B * C)) ^ ((1 : ℝ) / 3)
  let xH : ℝ := t * hScale
  let xK : ℝ := t * kScale
  let h : ℕ := ⌊xH⌋₊ - 1
  let k : ℕ := ⌊xK⌋₊ - 1
  have hAPos : 0 < A := by dsimp [A]; exact_mod_cast ha
  have hANonnegFromG : 0 ≤ A := hGNonneg.trans (by simpa [A] using hGTrivial)
  have hBPos : 0 < B := by
    dsimp [B]
    exact_mod_cast (lt_of_lt_of_le ha hab)
  have hCPos : 0 < C := by dsimp [C]; exact_mod_cast hchi
  have hPPos : 0 < P := by dsimp [P]; exact_mod_cast hp
  have hAB : A ≤ B := by dsimp [A, B]; exact_mod_cast hab
  have hCOne : 1 ≤ C := by
    dsimp [C]
    exact_mod_cast (show 1 ≤ chi by omega)
  have hbasePos : 0 < base := by dsimp [base]; positivity
  have hbaseRootPos : 0 < baseRoot := by dsimp [baseRoot]; positivity
  have hbaseRootCube : baseRoot ^ 3 = base := by
    simpa [baseRoot] using rpow_one_third_cube hbasePos.le
  have hhRadicandPos : 0 < B ^ 2 / (A * C) := by positivity
  have hkRadicandPos : 0 < A ^ 2 / (B * C) := by positivity
  have hhScalePos : 0 < hScale := by dsimp [hScale]; positivity
  have hkScalePos : 0 < kScale := by dsimp [kScale]; positivity
  have hhScaleCube : hScale ^ 3 = B ^ 2 / (A * C) := by
    simpa [hScale] using rpow_one_third_cube hhRadicandPos.le
  have hkScaleCube : kScale ^ 3 = A ^ 2 / (B * C) := by
    simpa [kScale] using rpow_one_third_cube hkRadicandPos.le
  have hxHPos : 0 < xH := by dsimp [xH]; positivity
  have hxKPos : 0 < xK := by dsimp [xK]; positivity
  have hscaledDegrees : A * hScale = B * kScale := by
    apply (pow_left_inj₀ (by positivity) (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [mul_pow, mul_pow, hhScaleCube, hkScaleCube]
    field_simp [hAPos.ne', hBPos.ne', hCPos.ne']
  have hAhScaleCube : (A * hScale) ^ 3 = (A * B) ^ 2 / C := by
    rw [mul_pow, hhScaleCube]
    field_simp [hAPos.ne', hCPos.ne']
  have hBdivHScale : B / hScale = baseRoot := by
    apply (pow_left_inj₀ (by positivity) hbaseRootPos.le
      (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [div_pow, hhScaleCube, hbaseRootCube]
    dsimp [base]
    field_simp [hAPos.ne', hBPos.ne', hCPos.ne']
  have hkScaleLeHScale : kScale ≤ hScale := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hhScalePos.le
    rw [hkScaleCube, hhScaleCube]
    apply (div_le_div_iff₀ (by positivity : 0 < B * C)
      (by positivity : 0 < A * C)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hAB)
      (by positivity : 0 ≤ A ^ 2 + A * B + B ^ 2)]
  have hxKLeXH : xK ≤ xH :=
    mul_le_mul_of_nonneg_left hkScaleLeHScale ht.le
  have hkh : k ≤ h := by
    dsimp [h, k]
    exact Nat.sub_le_sub_right (Nat.floor_mono hxKLeXH) 1
  have hSizeCross :
      ((A * B) ^ 2) * (8 * t ^ 3) < (P + A + B) ^ 3 * C := by
    have hdenPos : 0 < 8 * t ^ 3 := by positivity
    exact (lt_div_iff₀ hdenPos).mp (by simpa [A, B, C, P] using hSize)
  have hCommonCubeLt : (2 * t * (A * hScale)) ^ 3 < (P + A + B) ^ 3 := by
    have hdiv : 8 * t ^ 3 * (A * B) ^ 2 / C < (P + A + B) ^ 3 := by
      apply (div_lt_iff₀ hCPos).2
      nlinarith [hSizeCross]
    calc
      (2 * t * (A * hScale)) ^ 3 =
          8 * t ^ 3 * (A * B) ^ 2 / C := by
        rw [mul_pow, mul_pow, hAhScaleCube]
        norm_num
        ring
      _ < (P + A + B) ^ 3 := hdiv
  have hCommonLt : 2 * t * (A * hScale) < P + A + B :=
    lt_of_pow_lt_pow_left₀ 3 (by positivity) hCommonCubeLt
  by_cases hkSmall : k < 1
  · have hkZero : k = 0 := by omega
    have hxKTwo : xK < 2 := by
      simpa [k, hkZero] using lt_natFloor_sub_one_add_two xK
    have hxKCubeLt : xK ^ 3 < (2 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hxKTwo hxKPos.le (by norm_num)
    have htkCube : t ^ 3 * A ^ 2 / (B * C) < 8 := by
      calc
        t ^ 3 * A ^ 2 / (B * C) = xK ^ 3 := by
          dsimp [xK]
          rw [mul_pow, hkScaleCube]
          ring
        _ < (2 : ℝ) ^ 3 := hxKCubeLt
        _ = 8 := by norm_num
    have htA : t ^ 3 * A ^ 2 < 8 * (B * C) :=
      (div_lt_iff₀ (by positivity : 0 < B * C)).mp htkCube
    have htACube : t ^ 3 * A ^ 3 < 8 * base := by
      have := mul_lt_mul_of_pos_left htA hAPos
      dsimp [base]
      nlinarith
    have hACube : A ^ 3 < 8 * base / t ^ 3 := by
      apply (lt_div_iff₀ (by positivity : 0 < t ^ 3)).2
      simpa [mul_comm] using htACube
    have hsmallCube : (2 / t * baseRoot) ^ 3 = 8 * base / t ^ 3 := by
      rw [mul_pow, div_pow, hbaseRootCube]
      norm_num
      field_simp [ht.ne']
    have hASmall : A < 2 / t * baseRoot := by
      have hsmallNonneg : 0 ≤ 2 / t * baseRoot := by positivity
      apply lt_of_pow_lt_pow_left₀ 3 hsmallNonneg
      rwa [hsmallCube]
    calc
      G ≤ A := by simpa [A] using hGTrivial
      _ ≤ 2 / t * baseRoot := hASmall.le
      _ ≤ (4 / t + t ^ 2 / 2) * baseRoot := by
        apply mul_le_mul_of_nonneg_right _ hbaseRootPos.le
        calc
          2 / t ≤ 4 / t :=
            div_le_div_of_nonneg_right (by norm_num) ht.le
          _ ≤ 4 / t + t ^ 2 / 2 := le_add_of_nonneg_right (by positivity)
      _ = (4 / t + t ^ 2 / 2) *
          ((a : ℝ) * (b : ℝ) * (chi : ℝ)) ^ ((1 : ℝ) / 3) := by
        simp [baseRoot, base, A, B, C]
  · have hkPos : 0 < k := by omega
    have hhPos : 0 < h := lt_of_lt_of_le hkPos hkh
    have hkFloorOne : 1 ≤ ⌊xK⌋₊ := by
      dsimp [k] at hkPos
      omega
    have hhFloorOne : 1 ≤ ⌊xH⌋₊ := by
      dsimp [h] at hhPos
      omega
    have hkFloorUpper : ((k : ℝ) + 1) ≤ xK := by
      simpa [k] using natFloor_sub_one_add_one_le hxKPos.le hkFloorOne
    have hhFloorUpper : ((h : ℝ) + 1) ≤ xH := by
      simpa [h] using natFloor_sub_one_add_one_le hxHPos.le hhFloorOne
    have hParameterReal : A * (h : ℝ) + B * (k : ℝ) < P := by
      have hhUpper : (h : ℝ) ≤ xH - 1 := by linarith
      have hkUpper : (k : ℝ) ≤ xK - 1 := by linarith
      have hweighted :
          A * (h : ℝ) + B * (k : ℝ) ≤
            A * (xH - 1) + B * (xK - 1) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hhUpper hAPos.le)
          (mul_le_mul_of_nonneg_left hkUpper hBPos.le)
      have hweightedIdentity :
          A * (xH - 1) + B * (xK - 1) =
            2 * t * (A * hScale) - A - B := by
        dsimp [xH, xK]
        calc
          A * (t * hScale - 1) + B * (t * kScale - 1) =
              t * (A * hScale) + t * (B * kScale) - A - B := by ring
          _ = 2 * t * (A * hScale) - A - B := by
            rw [← hscaledDegrees]
            ring
      rw [hweightedIdentity] at hweighted
      linarith
    have hParameterNat : a * h + b * k < p := by
      dsimp [A, B, P] at hParameterReal
      exact_mod_cast hParameterReal
    have hnPos : 0 < h * k + h + k := by omega
    have hAlternative := hPropositionTwo h k ⟨hnPos, hParameterNat⟩
    rcases hAlternative with hDegrees | hNumerical
    · have hbLeH : b ≤ h := hDegrees.2
      have hBLtXH : B < xH := by
        have hbCast : B ≤ (h : ℝ) := by
          dsimp [B]
          exact_mod_cast hbLeH
        calc
          B ≤ (h : ℝ) := hbCast
          _ < (h : ℝ) + 1 := by norm_num
          _ ≤ xH := hhFloorUpper
      have hrootLtT : baseRoot < t := by
        rw [← hBdivHScale]
        apply (div_lt_iff₀ hhScalePos).2
        simpa [xH, mul_comm] using hBLtXH
      have hASqLeBase : A ^ 2 ≤ base := by
        dsimp [base]
        calc
          A ^ 2 ≤ A * B := by
            rw [pow_two]
            exact mul_le_mul_of_nonneg_left hAB hAPos.le
          _ = A * B * 1 := (mul_one _).symm
          _ ≤ A * B * C := mul_le_mul_of_nonneg_left hCOne (by positivity)
      have hASqLeRootCube : A ^ 2 ≤ baseRoot ^ 3 :=
        hASqLeBase.trans_eq hbaseRootCube.symm
      have hADegreeBound :
          A ≤ (4 / t + t ^ 2 / 2) * baseRoot :=
        degree_le_theoremFour_bound_of_sq_le_cube (degree := A) (root := baseRoot) (t := t)
          hANonnegFromG hbaseRootPos.le ht hASqLeRootCube hrootLtT.le
      calc
        G ≤ A := by change G ≤ (a : ℝ); exact hGTrivial
        _ ≤ (4 / t + t ^ 2 / 2) * baseRoot := hADegreeBound
        _ = (4 / t + t ^ 2 / 2) *
            ((a : ℝ) * (b : ℝ) * (chi : ℝ)) ^ ((1 : ℝ) / 3) := by
          rfl
    · exact propositionTwo_numerical_bound ha (lt_of_lt_of_le ha hab) hchi ht
        hkPos hkh hNumerical

end

end BGS.CorvajaZannier
