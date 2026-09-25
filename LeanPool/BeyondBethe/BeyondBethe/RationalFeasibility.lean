/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.RationalEllipsoid
public import LeanPool.BeyondBethe.BeyondBethe.AlgorithmicSpec
public import Mathlib.Tactic

/-! # Rational Feasibility -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# An executable rational central-cut feasibility loop

This file connects the square-root-free ellipsoid update to an actual finite
algorithm.  The oracle either accepts the current rational center or returns a
rational central cut.  The generic correctness theorem is deliberately
elementary: a valid cut preserves every target point, and a run long enough to
violate the determinant sandwich cannot be exhausted.
-/

/-- A target point belongs to the real ellipsoid represented by a rational
state if it has a real unit-ball preimage. -/
def RationalEllipsoidContains {d : ℕ}
    (E : RationalEllipsoidState d) (x : Fin d → ℝ) : Prop :=
  ∃ y : Fin d → ℝ, finiteNormSq y ≤ 1 ∧ rationalEllipsoidPoint E y = x

/-- Real cast of a rational center. -/
def rationalCenterReal {d : ℕ} (E : RationalEllipsoidState d) : Fin d → ℝ :=
  fun i ↦ (E.center i : ℝ)

/-- Rational representation of the Euclidean ball of radius `R` centered at
`c`. -/
def rationalBallEllipsoid (d : ℕ) (c : Fin d → ℚ) (R : ℚ) :
    RationalEllipsoidState d where
  center := c
  basis := fun i j ↦ if i = j then R else 0

@[simp] theorem rationalBallEllipsoid_center {d : ℕ}
    (c : Fin d → ℚ) (R : ℚ) :
    (rationalBallEllipsoid d c R).center = c := rfl

theorem rationalBallEllipsoid_basis {d : ℕ}
    (c : Fin d → ℚ) (R : ℚ) :
    (rationalBallEllipsoid d c R).basis = Matrix.diagonal (fun _ ↦ R) := by
  ext i j
  by_cases hij : i = j <;> simp [rationalBallEllipsoid, hij]

theorem det_rationalBallEllipsoid {d : ℕ}
    (c : Fin d → ℚ) (R : ℚ) :
    Matrix.det (rationalBallEllipsoid d c R).basis = R ^ d := by
  rw [rationalBallEllipsoid_basis, Matrix.det_diagonal]
  simp

/-- Every point in the ordinary radius-`R` ball has its explicit normalized
coordinate in the rational ball ellipsoid. -/
theorem rationalBallEllipsoid_contains {d : ℕ}
    (c : Fin d → ℚ) {R : ℚ} (hR : 0 < R) {x : Fin d → ℝ}
    (hx : finiteNormSq
      (fun i ↦ x i - (c i : ℝ)) ≤ (R : ℝ) ^ 2) :
    RationalEllipsoidContains (rationalBallEllipsoid d c R) x := by
  let y : Fin d → ℝ := fun i ↦ (x i - (c i : ℝ)) / (R : ℝ)
  have hRreal : 0 < (R : ℝ) := Rat.cast_pos.mpr hR
  have hyform : y = fun i ↦ ((R : ℝ)⁻¹) * (x i - (c i : ℝ)) := by
    funext i
    simp [y, div_eq_mul_inv, mul_comm]
  have hynorm : finiteNormSq y ≤ 1 := by
    rw [hyform, finiteNormSq_smul]
    have hR2 : 0 < (R : ℝ) ^ 2 := sq_pos_of_pos hRreal
    rw [inv_pow]
    simpa [div_eq_mul_inv, mul_comm] using! (div_le_one hR2).2 hx
  refine ⟨y, hynorm, ?_⟩
  ext i
  rw [rationalEllipsoidPoint]
  have hRne : (R : ℝ) ≠ 0 := hRreal.ne'
  change (c i : ℝ) +
      ∑ j, ((if i = j then R else 0 : ℚ) : ℝ) *
        ((x j - (c j : ℝ)) / (R : ℝ)) = x i
  simp_rw [show ∀ j : Fin d,
      ((if i = j then R else 0 : ℚ) : ℝ) =
        if i = j then (R : ℝ) else 0 by
    intro j
    by_cases hij : i = j <;> simp [hij]]
  simp
  field_simp [hRne]
  ring

/-- Binary exponent sufficient to dominate the determinant ratio between a
radius-`R` outer ball and a radius-`r` inner ball. -/
def rationalBallDyadicExponent (d : ℕ) (R r : ℚ) : ℕ :=
  d ^ 2 + encodedBitLength ℚ R * d + encodedBitLength ℚ r * d + 1

theorem factorial_le_two_pow_sq (d : ℕ) :
    d.factorial ≤ 2 ^ (d ^ 2) := by
  calc
    d.factorial ≤ d ^ d := Nat.factorial_le_pow d
    _ ≤ (2 ^ d) ^ d := Nat.pow_le_pow_left d.lt_two_pow_self.le d
    _ = 2 ^ (d ^ 2) := by simp [pow_mul, pow_two]

/-- The dyadic exponent computed from ordinary encodings makes the initial
determinant upper bound strictly smaller than the inner-ball lower bound. -/
theorem rationalBallDyadicExponent_works {d : ℕ} (hd : 0 < d)
    {R r : ℚ} (hR : 0 < R) (hr : 0 < r) :
    (d.factorial : ℚ) * R ^ d *
        (1 / 2 : ℚ) ^ rationalBallDyadicExponent d R r < r ^ d := by
  let LR := encodedBitLength ℚ R
  let Lr := encodedBitLength ℚ r
  let A := d ^ 2 + LR * d
  let C := Lr * d
  have hfac : (d.factorial : ℚ) ≤ (2 : ℚ) ^ (d ^ 2) := by
    exact_mod_cast factorial_le_two_pow_sq d
  have hRup : R < (2 : ℚ) ^ LR := by
    simpa only [LR] using! positive_rational_lt_two_pow_encodedBitLength hR
  have hRpow : R ^ d < (2 : ℚ) ^ (LR * d) := by
    calc
      R ^ d < ((2 : ℚ) ^ LR) ^ d :=
        pow_lt_pow_left₀ hRup hR.le hd.ne'
      _ = (2 : ℚ) ^ (LR * d) := by rw [← pow_mul]
  have hrlow : (1 / 2 : ℚ) ^ Lr < r := by
    simpa only [Lr] using! dyadic_encodedBitLength_lt_positive_rational hr
  have hrpow : ((1 / 2 : ℚ) ^ Lr) ^ d < r ^ d :=
    pow_lt_pow_left₀ hrlow (by positivity) hd.ne'
  have hM : rationalBallDyadicExponent d R r = A + C + 1 := by
    simp only [rationalBallDyadicExponent, A, C, LR, Lr]
  have hupper :
      (d.factorial : ℚ) * R ^ d *
          (1 / 2 : ℚ) ^ rationalBallDyadicExponent d R r <
        (2 : ℚ) ^ (d ^ 2) * (2 : ℚ) ^ (LR * d) *
          (1 / 2 : ℚ) ^ rationalBallDyadicExponent d R r := by
    have hdyadicPos : 0 <
        (1 / 2 : ℚ) ^ rationalBallDyadicExponent d R r := by positivity
    have hfactorialPos : (0 : ℚ) < d.factorial := by positivity
    have hrightNonneg : (0 : ℚ) ≤ (2 : ℚ) ^ (LR * d) := by positivity
    have hproduct : (d.factorial : ℚ) * R ^ d <
        (2 : ℚ) ^ (d ^ 2) * (2 : ℚ) ^ (LR * d) := by
      exact (mul_lt_mul_of_pos_left hRpow hfactorialPos).trans_le
        (mul_le_mul_of_nonneg_right hfac hrightNonneg)
    exact mul_lt_mul_of_pos_right
      hproduct hdyadicPos
  have hcollapse :
      (2 : ℚ) ^ (d ^ 2) * (2 : ℚ) ^ (LR * d) *
          (1 / 2 : ℚ) ^ rationalBallDyadicExponent d R r =
        (1 / 2 : ℚ) ^ (C + 1) := by
    have htwo : (2 : ℚ) ^ (d ^ 2) * (2 : ℚ) ^ (LR * d) =
        (2 : ℚ) ^ A := by
      rw [← pow_add]
    have hcancel : (2 : ℚ) ^ A * (1 / 2 : ℚ) ^ A = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      (2 : ℚ) ^ (d ^ 2) * (2 : ℚ) ^ (LR * d) *
          (1 / 2 : ℚ) ^ rationalBallDyadicExponent d R r =
        (2 : ℚ) ^ A * (1 / 2 : ℚ) ^ (A + (C + 1)) := by
          rw [htwo, hM]
          congr 2 <;> omega
      _ = (2 : ℚ) ^ A *
          ((1 / 2 : ℚ) ^ A * (1 / 2 : ℚ) ^ (C + 1)) := by
        congr 1
        rw [pow_add]
      _ = (1 / 2 : ℚ) ^ (C + 1) := by
        rw [← mul_assoc, hcancel, one_mul]
  have hstep : (1 / 2 : ℚ) ^ (C + 1) < (1 / 2 : ℚ) ^ C := by
    rw [pow_succ]
    have hpos : 0 < (1 / 2 : ℚ) ^ C := by positivity
    nlinarith
  calc
    (d.factorial : ℚ) * R ^ d *
        (1 / 2 : ℚ) ^ rationalBallDyadicExponent d R r <
      (2 : ℚ) ^ (d ^ 2) * (2 : ℚ) ^ (LR * d) *
        (1 / 2 : ℚ) ^ rationalBallDyadicExponent d R r := hupper
    _ = (1 / 2 : ℚ) ^ (C + 1) := hcollapse
    _ < (1 / 2 : ℚ) ^ C := hstep
    _ = ((1 / 2 : ℚ) ^ Lr) ^ d := by rw [← pow_mul]
    _ < r ^ d := hrpow

/-- Real determinant form consumed by the generic feasibility theorem. -/
theorem rationalBallEllipsoid_dyadic_budget {d : ℕ} (hd : 0 < d)
    (c : Fin d → ℚ) {R r : ℚ} (hR : 0 < R) (hr : 0 < r) :
    d.factorial *
        abs ((Matrix.det (rationalBallEllipsoid d c R).basis : ℚ) : ℝ) *
        (1 / 2 : ℝ) ^ rationalBallDyadicExponent d R r < (r : ℝ) ^ d := by
  have hq := rationalBallDyadicExponent_works hd hR hr
  rw [det_rationalBallEllipsoid, Rat.cast_pow,
    abs_of_pos (pow_pos (Rat.cast_pos.mpr hR) _)]
  have hcast :
      (((d.factorial : ℚ) * R ^ d *
        (1 / 2 : ℚ) ^ rationalBallDyadicExponent d R r : ℚ) : ℝ) <
        ((r ^ d : ℚ) : ℝ) := (Rat.cast_lt (K := ℝ)).mpr hq
  norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, Rat.cast_natCast] at hcast
  simpa using! hcast

/-- Pullback identity for the physical displacement from the ellipsoid
center. -/
theorem physicalDot_point_sub_center_eq_pulledDot {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) (y : Fin d → ℝ) :
    finiteDot (fun i ↦ (a i : ℝ))
        (fun i ↦ rationalEllipsoidPoint E y i - rationalCenterReal E i) =
      finiteDot (fun j ↦ (rationalPulledBackNormal E a j : ℝ)) y := by
  rw [finiteDot, finiteDot]
  simp only [rationalEllipsoidPoint, rationalCenterReal, add_sub_cancel_left]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [cast_rationalPulledBackNormal]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rationalPulledBackNormal_eq_transpose_mulVec {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    rationalPulledBackNormal E a = E.basis.transpose.mulVec a := by
  ext j
  simp [rationalPulledBackNormal, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]

/-- A nonsingular stored basis cannot annihilate a nonzero physical normal. -/
theorem rationalPulledBackNormal_ne_zero_of_det_ne_zero {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hdet : Matrix.det E.basis ≠ 0) (ha : a ≠ 0) :
    rationalPulledBackNormal E a ≠ 0 := by
  rw [rationalPulledBackNormal_eq_transpose_mulVec]
  intro hzero
  apply ha
  have hdetT : Matrix.det E.basis.transpose ≠ 0 := by
    simpa [Matrix.det_transpose] using! hdet
  have hunit : IsUnit (Matrix.det E.basis.transpose) :=
    (isUnit_iff_ne_zero).2 hdetT
  have hinv := Matrix.nonsing_inv_mul E.basis.transpose hunit
  calc
    a = Matrix.mulVec (1 : Matrix (Fin d) (Fin d) ℚ) a := by simp
    _ = Matrix.mulVec (E.basis.transpose⁻¹ * E.basis.transpose) a := by
      rw [hinv]
    _ = Matrix.mulVec E.basis.transpose⁻¹
        (Matrix.mulVec E.basis.transpose a) := by
      rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hzero]; simp

theorem det_rationalEllipsoidCentralUpdate_ne_zero {d : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hdet : Matrix.det E.basis ≠ 0)
    (hpulled : rationalPulledBackNormal E a ≠ 0) :
    Matrix.det (rationalEllipsoidCentralUpdate E a).basis ≠ 0 := by
  rw [det_rationalEllipsoidCentralUpdate hd E a hpulled]
  exact mul_ne_zero hdet (mul_ne_zero
    (pow_ne_zero _ (rationalEllipsoidPerpScale_pos d).ne')
    (rationalEllipsoidParallelScale_pos hd).ne')

/-- A valid physical central cut preserves any contained target point. -/
theorem rationalEllipsoidCentralUpdate_contains_point {d : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) {x : Fin d → ℝ}
    (hnonzero : rationalPulledBackNormal E a ≠ 0)
    (hcontains : RationalEllipsoidContains E x)
    (hcut : finiteDot (fun i ↦ (a i : ℝ))
      (fun i ↦ x i - rationalCenterReal E i) ≤ 0) :
    RationalEllipsoidContains (rationalEllipsoidCentralUpdate E a) x := by
  obtain ⟨y, hy, hpoint⟩ := hcontains
  have hpulled : finiteDot
      (fun j ↦ (rationalPulledBackNormal E a j : ℝ)) y ≤ 0 := by
    rw [← physicalDot_point_sub_center_eq_pulledDot E a y]
    simpa only [hpoint] using! hcut
  obtain ⟨y', hy', hpoint'⟩ :=
    rationalEllipsoidCentralUpdate_contains hd E a hnonzero hy hpulled
  exact ⟨y', hy', hpoint'.trans hpoint⟩

/-- The two possible responses of the central-cut oracle. -/
inductive RationalCentralOracleResponse (d : ℕ)
  | accept
  | cut (normal : Fin d → ℚ)
deriving DecidableEq

/-- An oracle is executable data: it reads the complete rational ellipsoid
state and either accepts its center or returns a rational cut normal. -/
abbrev RationalCentralOracle (d : ℕ) :=
  RationalEllipsoidState d → RationalCentralOracleResponse d

/-- Semantic validity of every cut returned by an oracle for a target set
`K`.  This is a property to be proved for the concrete oracle, not an
assumption built into the algorithm. -/
def RationalCentralOracleValid {d : ℕ}
    (K : (Fin d → ℝ) → Prop) (oracle : RationalCentralOracle d) : Prop :=
  ∀ E a, oracle E = .cut a →
    a ≠ 0 ∧
      ∀ x, K x → finiteDot (fun i ↦ (a i : ℝ))
        (fun i ↦ x i - rationalCenterReal E i) ≤ 0

/-- Optional semantic condition on acceptance.  Concrete weak oracles use
`Good` for membership in the prescribed enlargement. -/
def RationalCentralOracleAcceptsOnly {d : ℕ}
    (Good : (Fin d → ℚ) → Prop) (oracle : RationalCentralOracle d) : Prop :=
  ∀ E, oracle E = .accept → Good E.center

/-- Result of the bounded feasibility loop. -/
inductive RationalFeasibilityResult (d : ℕ)
  | accepted (point : Fin d → ℚ)
  | exhausted (state : RationalEllipsoidState d)

/-- Execute at most `budget` oracle calls. -/
def runRationalFeasibility {d : ℕ}
    (oracle : RationalCentralOracle d) :
    ℕ → RationalEllipsoidState d → RationalFeasibilityResult d
  | 0, E => .exhausted E
  | budget + 1, E =>
      match oracle E with
      | .accept => .accepted E.center
      | .cut a =>
          runRationalFeasibility oracle budget
            (rationalEllipsoidCentralUpdate E a)

/-- The exact list of cuts executed before acceptance or exhaustion. -/
def rationalFeasibilityCuts {d : ℕ}
    (oracle : RationalCentralOracle d) :
    ℕ → RationalEllipsoidState d → List (Fin d → ℚ)
  | 0, _ => []
  | budget + 1, E =>
      match oracle E with
      | .accept => []
      | .cut a => a :: rationalFeasibilityCuts oracle budget
          (rationalEllipsoidCentralUpdate E a)

theorem runRationalFeasibility_acceptsOnly {d : ℕ}
    {Good : (Fin d → ℚ) → Prop} {oracle : RationalCentralOracle d}
    (haccept : RationalCentralOracleAcceptsOnly Good oracle)
    {budget : ℕ} {E : RationalEllipsoidState d} {x : Fin d → ℚ}
    (hrun : runRationalFeasibility oracle budget E = .accepted x) :
    Good x := by
  induction budget generalizing E with
  | zero => simp [runRationalFeasibility] at hrun
  | succ budget ih =>
      rw [runRationalFeasibility] at hrun
      split at hrun <;> rename_i hresponse
      · cases hrun
        exact haccept E hresponse
      · exact ih hrun

/-- If the loop exhausts its budget, every oracle call was a cut. -/
theorem rationalFeasibilityCuts_length_of_exhausted {d : ℕ}
    (oracle : RationalCentralOracle d) {budget : ℕ}
    {E E' : RationalEllipsoidState d}
    (hrun : runRationalFeasibility oracle budget E = .exhausted E') :
    (rationalFeasibilityCuts oracle budget E).length = budget := by
  induction budget generalizing E E' with
  | zero => simp [rationalFeasibilityCuts]
  | succ budget ih =>
      rw [runRationalFeasibility] at hrun
      split at hrun <;> rename_i hresponse
      · contradiction
      · rw [rationalFeasibilityCuts, hresponse]
        simp only [List.length_cons]
        rw [ih hrun]

/-- The state returned on exhaustion is exactly the iteration of the recorded
cut list. -/
theorem rationalEllipsoidIterate_cuts_eq_of_exhausted {d : ℕ}
    (oracle : RationalCentralOracle d) {budget : ℕ}
    {E E' : RationalEllipsoidState d}
    (hrun : runRationalFeasibility oracle budget E = .exhausted E') :
    rationalEllipsoidIterate E (rationalFeasibilityCuts oracle budget E) = E' := by
  induction budget generalizing E E' with
  | zero => simpa [runRationalFeasibility, rationalFeasibilityCuts] using! hrun
  | succ budget ih =>
      rw [runRationalFeasibility] at hrun
      split at hrun <;> rename_i hresponse
      · contradiction
      · rw [rationalFeasibilityCuts, hresponse,
          rationalEllipsoidIterate]
        exact ih hrun

/-- Validity of the concrete oracle supplies every nonzero-normal side
condition in an exhausted trace. -/
theorem rationalFeasibilityCuts_nonzero_of_exhausted {d : ℕ}
    {K : (Fin d → ℝ) → Prop} {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid K oracle)
    (hd : 0 < d)
    {budget : ℕ} {E E' : RationalEllipsoidState d}
    (hdet : Matrix.det E.basis ≠ 0)
    (hrun : runRationalFeasibility oracle budget E = .exhausted E') :
    RationalEllipsoidCutsNonzero E
      (rationalFeasibilityCuts oracle budget E) := by
  induction budget generalizing E E' with
  | zero => simp [rationalFeasibilityCuts, RationalEllipsoidCutsNonzero]
  | succ budget ih =>
      rw [runRationalFeasibility] at hrun
      split at hrun <;> rename_i hresponse
      · contradiction
      · rw [rationalFeasibilityCuts, hresponse]
        change rationalPulledBackNormal E _ ≠ 0 ∧ _
        have hpulled := rationalPulledBackNormal_ne_zero_of_det_ne_zero
          E _ hdet (hvalid E _ hresponse).1
        exact ⟨hpulled, ih
          (det_rationalEllipsoidCentralUpdate_ne_zero hd E _ hdet hpulled)
          hrun⟩

/-- Every target point contained initially remains contained if a valid loop
exhausts its budget. -/
theorem runRationalFeasibility_preserves_target_of_exhausted {d : ℕ}
    (hd : 0 < d) {K : (Fin d → ℝ) → Prop}
    {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid K oracle)
    {budget : ℕ} {E E' : RationalEllipsoidState d}
    (hdet : Matrix.det E.basis ≠ 0)
    (hrun : runRationalFeasibility oracle budget E = .exhausted E')
    {x : Fin d → ℝ} (hK : K x)
    (hcontains : RationalEllipsoidContains E x) :
    RationalEllipsoidContains E' x := by
  induction budget generalizing E E' with
  | zero =>
      simp only [runRationalFeasibility] at hrun
      cases hrun
      exact hcontains
  | succ budget ih =>
      rw [runRationalFeasibility] at hrun
      split at hrun <;> rename_i hresponse
      · contradiction
      · have hcut := hvalid E _ hresponse
        have hpulled := rationalPulledBackNormal_ne_zero_of_det_ne_zero
          E _ hdet hcut.1
        have hnext := rationalEllipsoidCentralUpdate_contains_point hd E _
          hpulled hcontains (hcut.2 x hK)
        exact ih
          (det_rationalEllipsoidCentralUpdate_ne_zero hd E _ hdet hpulled)
          hrun hnext

/-- Main generic termination theorem.  If the target contains a radius-`r`
coordinate cross and the initial ellipsoid contains those endpoints, the
loop cannot exhaust a dyadic determinant budget. -/
theorem runRationalFeasibility_not_exhausted_of_inner_cross
    {d M : ℕ} (hd : 0 < d)
    {K : (Fin d → ℝ) → Prop} {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid K oracle)
    (E : RationalEllipsoidState d)
    (hdet : Matrix.det E.basis ≠ 0)
    {z : Fin d → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hdyadic : Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) *
      (1 / 2 : ℝ) ^ M < r ^ d)
    (hKplus : ∀ k, K (fun i ↦ z i + if i = k then r else 0))
    (hKminus : ∀ k, K (fun i ↦ z i - if i = k then r else 0))
    (hEplus : ∀ k, RationalEllipsoidContains E
      (fun i ↦ z i + if i = k then r else 0))
    (hEminus : ∀ k, RationalEllipsoidContains E
      (fun i ↦ z i - if i = k then r else 0))
    (E' : RationalEllipsoidState d) :
    runRationalFeasibility oracle (8 * d ^ 3 * M) E ≠ .exhausted E' := by
  intro hrun
  let cuts := rationalFeasibilityCuts oracle (8 * d ^ 3 * M) E
  have hlength : 8 * d ^ 3 * M ≤ cuts.length := by
    rw [rationalFeasibilityCuts_length_of_exhausted oracle hrun]
  have hstate := rationalEllipsoidIterate_cuts_eq_of_exhausted oracle hrun
  have hnonzero := rationalFeasibilityCuts_nonzero_of_exhausted
    hvalid hd hdet hrun
  have hplus : ∀ k, ∃ y : Fin d → ℝ, finiteNormSq y ≤ 1 ∧
      rationalEllipsoidPoint (rationalEllipsoidIterate E cuts) y =
        fun i ↦ z i + if i = k then r else 0 := by
    intro k
    have hpreserve := runRationalFeasibility_preserves_target_of_exhausted
      hd hvalid hdet hrun (hKplus k) (hEplus k)
    rw [← hstate] at hpreserve
    exact hpreserve
  have hminus : ∀ k, ∃ y : Fin d → ℝ, finiteNormSq y ≤ 1 ∧
      rationalEllipsoidPoint (rationalEllipsoidIterate E cuts) y =
        fun i ↦ z i - if i = k then r else 0 := by
    intro k
    have hpreserve := runRationalFeasibility_preserves_target_of_exhausted
      hd hvalid hdet hrun (hKminus k) (hEminus k)
    rw [← hstate] at hpreserve
    exact hpreserve
  exact rationalEllipsoid_no_long_run hd E cuts hnonzero hlength hr hdyadic
    hplus hminus

/-- Fully explicit specialization to a rational outer ball and a rational
inner radius.  Both the iteration count and the initial state are executable
from their displayed rational data. -/
theorem runRationalFeasibility_ball_not_exhausted
    {d : ℕ} (hd : 0 < d)
    {K : (Fin d → ℝ) → Prop} {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid K oracle)
    (c : Fin d → ℚ) {R r : ℚ} (hR : 0 < R) (hr : 0 < r)
    {z : Fin d → ℝ}
    (hKplus : ∀ k, K (fun i ↦ z i + if i = k then (r : ℝ) else 0))
    (hKminus : ∀ k, K (fun i ↦ z i - if i = k then (r : ℝ) else 0))
    (houterPlus : ∀ k, finiteNormSq
      (fun i ↦ (z i + if i = k then (r : ℝ) else 0) - (c i : ℝ)) ≤
        (R : ℝ) ^ 2)
    (houterMinus : ∀ k, finiteNormSq
      (fun i ↦ (z i - if i = k then (r : ℝ) else 0) - (c i : ℝ)) ≤
        (R : ℝ) ^ 2)
    (E' : RationalEllipsoidState d) :
    runRationalFeasibility oracle
        (8 * d ^ 3 * rationalBallDyadicExponent d R r)
        (rationalBallEllipsoid d c R) ≠ .exhausted E' := by
  apply runRationalFeasibility_not_exhausted_of_inner_cross
    hd hvalid (rationalBallEllipsoid d c R)
      (by rw [det_rationalBallEllipsoid]; exact pow_ne_zero _ hR.ne')
      (hr := Rat.cast_nonneg.mpr hr.le)
      (rationalBallEllipsoid_dyadic_budget hd c hR hr)
      hKplus hKminus
  · intro k
    exact rationalBallEllipsoid_contains c hR (houterPlus k)
  · intro k
    exact rationalBallEllipsoid_contains c hR (houterMinus k)

/-- Data-producing form: under the same explicit ball hypotheses, a valid
oracle that accepts only `Good` points returns a concrete rational `Good`
point within the computed budget. -/
theorem runRationalFeasibility_ball_accepts
    {d : ℕ} (hd : 0 < d)
    {K : (Fin d → ℝ) → Prop} {Good : (Fin d → ℚ) → Prop}
    {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid K oracle)
    (haccept : RationalCentralOracleAcceptsOnly Good oracle)
    (c : Fin d → ℚ) {R r : ℚ} (hR : 0 < R) (hr : 0 < r)
    {z : Fin d → ℝ}
    (hKplus : ∀ k, K (fun i ↦ z i + if i = k then (r : ℝ) else 0))
    (hKminus : ∀ k, K (fun i ↦ z i - if i = k then (r : ℝ) else 0))
    (houterPlus : ∀ k, finiteNormSq
      (fun i ↦ (z i + if i = k then (r : ℝ) else 0) - (c i : ℝ)) ≤
        (R : ℝ) ^ 2)
    (houterMinus : ∀ k, finiteNormSq
      (fun i ↦ (z i - if i = k then (r : ℝ) else 0) - (c i : ℝ)) ≤
        (R : ℝ) ^ 2) :
    ∃ x : Fin d → ℚ,
      runRationalFeasibility oracle
          (8 * d ^ 3 * rationalBallDyadicExponent d R r)
          (rationalBallEllipsoid d c R) = .accepted x ∧ Good x := by
  let result := runRationalFeasibility oracle
    (8 * d ^ 3 * rationalBallDyadicExponent d R r)
    (rationalBallEllipsoid d c R)
  cases hresult : result with
  | accepted x =>
      refine ⟨x, ?_, ?_⟩
      · simpa only [result] using! hresult
      · exact runRationalFeasibility_acceptsOnly haccept
          (by simpa only [result] using! hresult)
  | exhausted E' =>
      exfalso
      exact runRationalFeasibility_ball_not_exhausted hd hvalid c hR hr
        hKplus hKminus houterPlus houterMinus E'
        (by simpa only [result] using! hresult)

end BeyondBethe
