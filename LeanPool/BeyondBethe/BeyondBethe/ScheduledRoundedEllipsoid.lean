/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.RoundedEllipsoidIterationBounds
public import Mathlib.Tactic

/-! # Scheduled Rounded Ellipsoid -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Determinant-independent scheduled rounding

`roundedEllipsoidPrecision` is a semantic proof specification: it mentions the
exact determinant of the state to be rounded.  The definitions in this file
take an externally scheduled number of fractional bits.  Correctness needs
only the displayed inequality saying that the schedule dominates the semantic
requirement.  Later iteration lemmas discharge that inequality from the
initial determinant and magnitude bounds, without evaluating a determinant.
-/

/-- A uniform precision schedule for a run of at most `T` central cuts. -/
def roundedEllipsoidPrecisionSchedule (d L K T : ℕ) : ℕ :=
  roundedEllipsoidNextPrecisionBound d L K T

theorem roundedEllipsoidNextPrecisionBound_mono_last
    {d L K t T : ℕ} (ht : t ≤ T) :
    roundedEllipsoidNextPrecisionBound d L K t ≤
      roundedEllipsoidNextPrecisionBound d L K T := by
  rw [roundedEllipsoidNextPrecisionBound,
    roundedEllipsoidNextPrecisionBound,
    roundedEllipsoidDenominatorExponent,
    roundedEllipsoidDenominatorExponent]
  gcongr

theorem roundedEllipsoidNextPrecisionBound_le_schedule
    {d L K t T : ℕ} (ht : t ≤ T) :
    roundedEllipsoidNextPrecisionBound d L K t ≤
      roundedEllipsoidPrecisionSchedule d L K T := by
  exact roundedEllipsoidNextPrecisionBound_mono_last ht

/-- Round a state at a determinant-independent scheduled precision. -/
def scheduledRoundedEllipsoid {d : ℕ} (p : ℕ)
    (U : RationalEllipsoidState d) : RationalEllipsoidState d :=
  inflatedDyadicRound p (roundedEllipsoidInflation d) U

/-- Exact central update followed by scheduled dyadic rounding. -/
def scheduledRoundedEllipsoidCentralUpdate {d : ℕ} (p : ℕ)
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    RationalEllipsoidState d :=
  scheduledRoundedEllipsoid p (rationalEllipsoidCentralUpdate E a)

theorem scheduled_dyadicMesh_le_adaptive {d p : ℕ}
    (U : RationalEllipsoidState d)
    (hp : roundedEllipsoidPrecision U ≤ p) :
    dyadicMesh p ≤ dyadicMesh (roundedEllipsoidPrecision U) :=
  dyadicMesh_antitone hp

theorem scheduled_dyadicMesh_lt_target {d p : ℕ} (hd : 0 < d)
    (U : RationalEllipsoidState d) (hdet : Matrix.det U.basis ≠ 0)
    (hp : roundedEllipsoidPrecision U ≤ p) :
    dyadicMesh p < roundedEllipsoidMeshTarget U :=
  (scheduled_dyadicMesh_le_adaptive U hp).trans_lt
    (adaptive_dyadicMesh_lt_target hd U hdet)

theorem scheduled_determinant_rounding_loss_lt {d p : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d)
    (hdet : Matrix.det U.basis ≠ 0)
    (hp : roundedEllipsoidPrecision U ≤ p) :
    roundedDeterminantCoefficient d (rationalMatrixAbsBound U.basis) *
        dyadicMesh p <
      abs (Matrix.det U.basis) / (128 * d ^ 3) := by
  have hmesh := scheduled_dyadicMesh_le_adaptive U hp
  have hC : 0 ≤ roundedDeterminantCoefficient d
      (rationalMatrixAbsBound U.basis) :=
    (roundedDeterminantCoefficient_pos hd
      (rationalMatrixAbsBound_pos U.basis)).le
  exact (mul_le_mul_of_nonneg_left hmesh hC).trans_lt
    (adaptive_determinant_rounding_loss_lt hd U hdet)

theorem scheduled_inverse_rounding_loss_lt {d p : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d)
    (hdet : Matrix.det U.basis ≠ 0)
    (hp : roundedEllipsoidPrecision U ≤ p) :
    roundedInverseCoefficient d (rationalMatrixAbsBound U.basis) *
        dyadicMesh p <
      roundedEllipsoidInflation d * abs (Matrix.det U.basis) /
        (2 * d) := by
  have hmesh := scheduled_dyadicMesh_le_adaptive U hp
  have hC : 0 ≤ roundedInverseCoefficient d
      (rationalMatrixAbsBound U.basis) :=
    (roundedInverseCoefficient_pos hd
      (rationalMatrixAbsBound_pos U.basis)).le
  exact (mul_le_mul_of_nonneg_left hmesh hC).trans_lt
    (adaptive_inverse_rounding_loss_lt hd U hdet)

theorem scheduledRounded_entry_bound {d p : ℕ}
    (U : RationalEllipsoidState d) (i j : Fin d) :
    abs (((dyadicFloorMatrix p U.basis i j : ℚ) : ℝ)) ≤
      (2 * rationalMatrixAbsBound U.basis : ℚ) := by
  let M := rationalMatrixAbsBound U.basis
  have hM1 : (1 : ℚ) ≤ M := rationalMatrixAbsBound_one_le U.basis
  have hentry : abs (U.basis i j) < M :=
    abs_entry_lt_rationalMatrixAbsBound U.basis i j
  have hround := abs_dyadicFloor_le p (U.basis i j)
  have hmesh := dyadicMesh_le_one p
  have hq : abs (dyadicFloor p (U.basis i j)) ≤ 2 * M := by
    dsimp only [M] at hM1 hentry ⊢
    linarith
  exact_mod_cast hq

theorem scheduledRounded_det_lower {d p : ℕ} (hd : 0 < d)
    (U : RationalEllipsoidState d) (hdet : Matrix.det U.basis ≠ 0)
    (hp : roundedEllipsoidPrecision U ≤ p) :
    ((abs (Matrix.det U.basis) / 2 : ℚ) : ℝ) ≤
      abs (Matrix.det
        (fun i j ↦ ((dyadicFloorMatrix p U.basis i j : ℚ) : ℝ))) := by
  let Mq := rationalMatrixAbsBound U.basis
  let Δq := abs (Matrix.det U.basis)
  let A : Matrix (Fin d) (Fin d) ℝ :=
    fun i j ↦ ((dyadicFloorMatrix p U.basis i j : ℚ) : ℝ)
  let B : Matrix (Fin d) (Fin d) ℝ :=
    fun i j ↦ ((U.basis i j : ℚ) : ℝ)
  have hMq1 : (1 : ℚ) ≤ Mq := rationalMatrixAbsBound_one_le U.basis
  have hMreal : (1 : ℝ) ≤ (Mq : ℝ) := by exact_mod_cast hMq1
  have hBentry : ∀ i j, abs (B i j) ≤ (Mq : ℝ) := by
    intro i j
    change abs (((U.basis i j : ℚ) : ℝ)) ≤ (Mq : ℝ)
    exact_mod_cast (abs_entry_lt_rationalMatrixAbsBound U.basis i j).le
  have hpert := abs_det_dyadicFloorMatrix_sub_det_le p U.basis hMreal
    (by simpa only [B] using hBentry)
  have hlossQ := scheduled_determinant_rounding_loss_lt hd U hdet hp
  have hloss :
      d.factorial *
          (d * (dyadicMesh p : ℝ) * (2 * (Mq : ℝ)) ^ d) <
        (Δq : ℝ) / (128 * (d : ℝ) ^ 3) := by
    have hc :
        ((roundedDeterminantCoefficient d Mq * dyadicMesh p : ℚ) : ℝ) <
          ((Δq / (128 * d ^ 3) : ℚ) : ℝ) := by
      exact_mod_cast hlossQ
    norm_num only [roundedDeterminantCoefficient, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_natCast, Rat.cast_div] at hc
    convert hc using 1 <;> ring
  have hsmallLoss :
      d.factorial *
          (d * (dyadicMesh p : ℝ) * (2 * (Mq : ℝ)) ^ d) <
        (Δq : ℝ) / 2 := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hΔ : 0 < (Δq : ℝ) := by
      exact_mod_cast (abs_pos.mpr hdet)
    have hden : (2 : ℝ) ≤ 128 * (d : ℝ) ^ 3 := by
      nlinarith [one_le_pow₀ (n := 3) hdR]
    have hfrac : (Δq : ℝ) / (128 * (d : ℝ) ^ 3) ≤ (Δq : ℝ) / 2 :=
      div_le_div_of_nonneg_left hΔ.le (by norm_num) hden
    exact hloss.trans_le hfrac
  have htriangle : abs (Matrix.det B) ≤
      abs (Matrix.det A - Matrix.det B) + abs (Matrix.det A) := by
    calc
      abs (Matrix.det B) =
          abs ((Matrix.det B - Matrix.det A) + Matrix.det A) := by ring_nf
      _ ≤ abs (Matrix.det B - Matrix.det A) + abs (Matrix.det A) :=
        abs_add_le _ _
      _ = abs (Matrix.det A - Matrix.det B) + abs (Matrix.det A) := by
        rw [show Matrix.det B - Matrix.det A =
          -(Matrix.det A - Matrix.det B) by ring, abs_neg]
  have hcastB : Matrix.det B = ((Matrix.det U.basis : ℚ) : ℝ) := by
    rw [show B = U.basis.map (fun q : ℚ ↦ (q : ℝ)) by rfl, Rat.cast_det]
  have hpert' : abs (Matrix.det A - Matrix.det B) ≤
      d.factorial *
        (d * (dyadicMesh p : ℝ) * (2 * (Mq : ℝ)) ^ d) := by
    simpa only [A, B] using hpert
  rw [hcastB] at htriangle hpert'
  have hΔcast : abs (((Matrix.det U.basis : ℚ) : ℝ)) = (Δq : ℝ) := by
    exact_mod_cast (show abs (Matrix.det U.basis) = Δq by rfl)
  rw [hΔcast] at htriangle
  have hresult : (Δq : ℝ) / 2 ≤ abs (Matrix.det A) := by linarith
  simpa only [A, Δq, Rat.cast_div, Rat.cast_ofNat] using hresult

theorem scheduledRounded_contains {d p : ℕ} (hd : 0 < d)
    (U : RationalEllipsoidState d) (hdet : Matrix.det U.basis ≠ 0)
    (hp : roundedEllipsoidPrecision U ≤ p)
    {y : Fin d → ℝ} (hy : finiteNormSq y ≤ 1) :
    ∃ y' : Fin d → ℝ, finiteNormSq y' ≤ 1 ∧
      rationalEllipsoidPoint (scheduledRoundedEllipsoid p U) y' =
        rationalEllipsoidPoint U y := by
  let Mq := rationalMatrixAbsBound U.basis
  let Mr : ℝ := 2 * (Mq : ℝ)
  let Δq := abs (Matrix.det U.basis)
  let D : ℝ := ((Δq / 2 : ℚ) : ℝ)
  let η := roundedEllipsoidInflation d
  have hMq : 0 < Mq := rationalMatrixAbsBound_pos U.basis
  have hMr : (1 : ℝ) ≤ Mr := by
    dsimp only [Mr]
    have hMq1 := rationalMatrixAbsBound_one_le U.basis
    exact_mod_cast (show (1 : ℚ) ≤ 2 * Mq by linarith)
  have hD : 0 < D := by
    dsimp only [D, Δq]
    exact_mod_cast (div_pos (abs_pos.mpr hdet) (by norm_num : (0 : ℚ) < 2))
  have hη : 0 ≤ η := roundedEllipsoidInflation_nonneg d
  have hentries : ∀ i j,
      abs (((dyadicFloorMatrix p U.basis i j : ℚ) : ℝ)) ≤ Mr := by
    intro i j
    simpa only [Mr, Rat.cast_mul, Rat.cast_ofNat] using
      scheduledRounded_entry_bound (p := p) U i j
  have hdetLower : D ≤ abs (Matrix.det
      (fun i j ↦ ((dyadicFloorMatrix p U.basis i j : ℚ) : ℝ))) := by
    simpa only [D, Δq] using scheduledRounded_det_lower hd U hdet hp
  have hinverseQ := scheduled_inverse_rounding_loss_lt hd U hdet hp
  have hinverse :
      (roundedInverseCoefficient d Mq : ℝ) * (dyadicMesh p : ℝ) <
        (η : ℝ) * (Δq : ℝ) / (2 * (d : ℝ)) := by
    exact_mod_cast hinverseQ
  let V : ℝ :=
    (d * (d.factorial * Mr ^ d) *
      (((d + 1 : ℕ) : ℝ) * (dyadicMesh p : ℝ))) / D
  have hVform : V =
      ((roundedInverseCoefficient d Mq : ℚ) : ℝ) *
        (dyadicMesh p : ℝ) / D := by
    have hCcast : ((roundedInverseCoefficient d Mq : ℚ) : ℝ) =
        (d : ℝ) * (d.factorial * (2 * (Mq : ℝ)) ^ d) * (d + 1) := by
      simp [roundedInverseCoefficient]
    rw [hCcast]
    dsimp only [V, Mr]
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  have hV0 : 0 ≤ V := by
    have hMr0 : 0 ≤ Mr := by linarith [hMr]
    have hMrpow : 0 ≤ Mr ^ d := pow_nonneg hMr0 _
    have hmesh0 : 0 ≤ (dyadicMesh p : ℝ) := by
      exact_mod_cast dyadicMesh_nonneg p
    dsimp only [V]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity)
          (mul_nonneg (by positivity) hMrpow))
        (mul_nonneg (by positivity) hmesh0)) hD.le
  have hV : V ≤ (η : ℝ) / d := by
    rw [hVform]
    have hΔ : 0 < (Δq : ℝ) := by
      exact_mod_cast (abs_pos.mpr hdet)
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hDform : D = (Δq : ℝ) / 2 := by
      dsimp only [D]
      norm_num
    rw [hDform]
    have hposDen : 0 < (Δq : ℝ) / 2 := div_pos hΔ (by norm_num)
    rw [div_le_iff₀ hposDen]
    have hηR : 0 ≤ (η : ℝ) := by exact_mod_cast hη
    calc
      ((roundedInverseCoefficient d Mq : ℚ) : ℝ) *
          (dyadicMesh p : ℝ) ≤
        (η : ℝ) * (Δq : ℝ) / (2 * (d : ℝ)) := hinverse.le
      _ = ((η : ℝ) / d) * ((Δq : ℝ) / 2) := by ring
  have hsmall : d * V ^ 2 ≤ (η : ℝ) ^ 2 := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hηR : 0 ≤ (η : ℝ) := by exact_mod_cast hη
    have hdiv0 : 0 ≤ (η : ℝ) / d := div_nonneg hηR (by positivity)
    have hsq : V ^ 2 ≤ ((η : ℝ) / d) ^ 2 :=
      (sq_le_sq₀ hV0 hdiv0).2 hV
    have hdpos : (0 : ℝ) < d := by positivity
    calc
      (d : ℝ) * V ^ 2 ≤ d * ((η : ℝ) / d) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hdpos.le
      _ = (η : ℝ) ^ 2 / d := by field_simp
      _ ≤ (η : ℝ) ^ 2 := div_le_self (sq_nonneg (η : ℝ)) hdR
  have hsmall' :
      d *
        ((d * (d.factorial * Mr ^ d) *
          ((d + 1 : ℕ) * (dyadicMesh p : ℝ))) / D) ^ 2 ≤
        (η : ℝ) ^ 2 := by simpa only [V] using hsmall
  simpa only [scheduledRoundedEllipsoid, η] using
    inflatedDyadicRound_contains hd p η U hη hD hMr hentries
      hdetLower hsmall' hy

theorem det_scheduledRoundedEllipsoid_ne_zero {d p : ℕ} (hd : 0 < d)
    (U : RationalEllipsoidState d) (hdet : Matrix.det U.basis ≠ 0)
    (hp : roundedEllipsoidPrecision U ≤ p) :
    Matrix.det (scheduledRoundedEllipsoid p U).basis ≠ 0 := by
  have hround : Matrix.det (dyadicFloorMatrix p U.basis) ≠ 0 := by
    intro hz
    have hlower := scheduledRounded_det_lower hd U hdet hp
    have hzeroReal : Matrix.det
        (fun i j ↦ ((dyadicFloorMatrix p U.basis i j : ℚ) : ℝ)) = 0 := by
      rw [show (fun i j ↦ ((dyadicFloorMatrix p U.basis i j : ℚ) : ℝ)) =
          (dyadicFloorMatrix p U.basis).map (fun q : ℚ ↦ (q : ℝ)) by rfl,
        ← Rat.cast_det, hz]
      simp
    rw [hzeroReal] at hlower
    have hpos : (0 : ℝ) < ((abs (Matrix.det U.basis) / 2 : ℚ) : ℝ) := by
      exact_mod_cast div_pos (abs_pos.mpr hdet) (by norm_num : (0 : ℚ) < 2)
    linarith
  rw [scheduledRoundedEllipsoid, det_inflatedDyadicRound_basis]
  exact mul_ne_zero
    (pow_ne_zero _ (by
      have hη := roundedEllipsoidInflation_pos hd
      linarith)) hround

theorem det_scheduledRoundedEllipsoidCentralUpdate_ne_zero {d p : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hdet : Matrix.det E.basis ≠ 0)
    (hb : rationalPulledBackNormal E a ≠ 0)
    (hp : roundedEllipsoidPrecision
      (rationalEllipsoidCentralUpdate E a) ≤ p) :
    Matrix.det (scheduledRoundedEllipsoidCentralUpdate p E a).basis ≠ 0 := by
  let U := rationalEllipsoidCentralUpdate E a
  have hdetU : Matrix.det U.basis ≠ 0 := by
    dsimp only [U]
    rw [det_rationalEllipsoidCentralUpdate hd E a hb]
    exact mul_ne_zero hdet (mul_ne_zero
      (pow_ne_zero _ (rationalEllipsoidPerpScale_pos d).ne')
      (rationalEllipsoidParallelScale_pos hd).ne')
  exact det_scheduledRoundedEllipsoid_ne_zero hd U hdetU hp

theorem scheduledRoundedEllipsoidCentralUpdate_contains {d p : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hdet : Matrix.det E.basis ≠ 0)
    (hb : rationalPulledBackNormal E a ≠ 0)
    (hp : roundedEllipsoidPrecision
      (rationalEllipsoidCentralUpdate E a) ≤ p)
    {y : Fin d → ℝ} (hy : finiteNormSq y ≤ 1)
    (hcut : finiteDot
      (fun i ↦ (rationalPulledBackNormal E a i : ℝ)) y ≤ 0) :
    ∃ y' : Fin d → ℝ, finiteNormSq y' ≤ 1 ∧
      rationalEllipsoidPoint
          (scheduledRoundedEllipsoidCentralUpdate p E a) y' =
        rationalEllipsoidPoint E y := by
  let U := rationalEllipsoidCentralUpdate E a
  have hdetU : Matrix.det U.basis ≠ 0 := by
    dsimp only [U]
    rw [det_rationalEllipsoidCentralUpdate hd E a hb]
    exact mul_ne_zero hdet (mul_ne_zero
      (pow_ne_zero _ (rationalEllipsoidPerpScale_pos d).ne')
      (rationalEllipsoidParallelScale_pos hd).ne')
  obtain ⟨z, hz, hpoint⟩ :=
    rationalEllipsoidCentralUpdate_contains hd E a hb hy hcut
  obtain ⟨z', hz', hround⟩ := scheduledRounded_contains hd U hdetU hp hz
  refine ⟨z', hz', ?_⟩
  rw [scheduledRoundedEllipsoidCentralUpdate, hround, hpoint]

/-- A sufficiently fine scheduled rounded cut has the same uniform
determinant contraction as the proof-specification update. -/
theorem abs_det_scheduledRoundedCentralUpdate_le {d p : ℕ} (hd : 0 < d)
    (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hdet : Matrix.det E.basis ≠ 0)
    (hb : rationalPulledBackNormal E a ≠ 0)
    (hp : roundedEllipsoidPrecision
      (rationalEllipsoidCentralUpdate E a) ≤ p) :
    abs ((Matrix.det
      (scheduledRoundedEllipsoidCentralUpdate p E a).basis : ℚ) : ℝ) ≤
      (1 - 1 / (32 * (d : ℝ) ^ 3)) *
        abs ((Matrix.det E.basis : ℚ) : ℝ) := by
  let U := rationalEllipsoidCentralUpdate E a
  let Mq := rationalMatrixAbsBound U.basis
  let η := roundedEllipsoidInflation d
  let L : ℝ := d.factorial *
    (d * (dyadicMesh p : ℝ) * (2 * (Mq : ℝ)) ^ d)
  let ΔE : ℝ := abs ((Matrix.det E.basis : ℚ) : ℝ)
  let ΔU : ℝ := abs ((Matrix.det U.basis : ℚ) : ℝ)
  let q : ℝ :=
    (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) *
      (rationalEllipsoidParallelScale d : ℝ)
  have hdetU : Matrix.det U.basis ≠ 0 := by
    dsimp only [U]
    rw [det_rationalEllipsoidCentralUpdate hd E a hb]
    exact mul_ne_zero hdet (mul_ne_zero
      (pow_ne_zero _ (rationalEllipsoidPerpScale_pos d).ne')
      (rationalEllipsoidParallelScale_pos hd).ne')
  have hΔE0 : 0 ≤ ΔE := abs_nonneg _
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    exact mul_nonneg
      (pow_nonneg (Rat.cast_nonneg.mpr
        (rationalEllipsoidPerpScale_pos d).le) _)
      (Rat.cast_nonneg.mpr (rationalEllipsoidParallelScale_pos hd).le)
  have hq1 : q ≤ 1 := (rationalEllipsoid_volumeFactor_lt_one hd).le
  have hqContract : q ≤ 1 - 1 / (16 * (d : ℝ) ^ 3) :=
    rationalEllipsoid_volumeFactor_le_one_sub hd
  have hΔeq : ΔU = ΔE * q := by
    have hdetEq := det_rationalEllipsoidCentralUpdate hd E a hb
    dsimp only [U, ΔU, ΔE, q]
    rw [hdetEq, Rat.cast_mul, abs_mul]
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_sub,
      Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    rw [abs_of_nonneg hq0]
  have hΔUle : ΔU ≤ ΔE := by
    rw [hΔeq]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq1 hΔE0
  have hMq1 : (1 : ℝ) ≤ (Mq : ℝ) := by
    exact_mod_cast rationalMatrixAbsBound_one_le U.basis
  have hUentry : ∀ i j, abs ((U.basis i j : ℚ) : ℝ) ≤ (Mq : ℝ) := by
    intro i j
    exact_mod_cast (abs_entry_lt_rationalMatrixAbsBound U.basis i j).le
  have hupper0 := abs_det_inflatedDyadicRound_le p η U
    (roundedEllipsoidInflation_nonneg d) hMq1 hUentry
  have hupper :
      abs ((Matrix.det
        (scheduledRoundedEllipsoidCentralUpdate p E a).basis : ℚ) : ℝ) ≤
        (1 + (η : ℝ)) ^ d * (ΔU + L) := by
    simpa only [scheduledRoundedEllipsoidCentralUpdate,
      scheduledRoundedEllipsoid, U, η, ΔU, L] using hupper0
  have hlossQ := scheduled_determinant_rounding_loss_lt hd U hdetU hp
  have hloss : L < ΔU / (128 * (d : ℝ) ^ 3) := by
    have hc :
        ((roundedDeterminantCoefficient d Mq * dyadicMesh p : ℚ) : ℝ) <
          ((abs (Matrix.det U.basis) / (128 * d ^ 3) : ℚ) : ℝ) := by
      exact_mod_cast hlossQ
    norm_num only [roundedDeterminantCoefficient, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_natCast, Rat.cast_div] at hc
    have hc' : L <
        ((abs (Matrix.det U.basis) : ℚ) : ℝ) /
          (128 * (d : ℝ) ^ 3) := by
      dsimp only [L]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hc
    have habsCast : ((abs (Matrix.det U.basis) : ℚ) : ℝ) = ΔU := by
      dsimp only [ΔU]
      exact_mod_cast (show abs (Matrix.det U.basis) =
        abs (Matrix.det U.basis) by rfl)
    rw [habsCast] at hc'
    exact hc'
  have hlossE : L ≤ ΔE / (128 * (d : ℝ) ^ 3) := by
    have hden : 0 < (128 : ℝ) * (d : ℝ) ^ 3 := by positivity
    exact hloss.le.trans (div_le_div_of_nonneg_right hΔUle hden.le)
  have hbracket : ΔU + L ≤
      ΔE * (1 - 7 / (128 * (d : ℝ) ^ 3)) := by
    rw [hΔeq]
    have hq' : q ≤ 1 - 8 / (128 * (d : ℝ) ^ 3) := by
      convert hqContract using 1 <;> ring
    have hqmul := mul_le_mul_of_nonneg_left hq' hΔE0
    calc
      ΔE * q + L ≤
          ΔE * (1 - 8 / (128 * (d : ℝ) ^ 3)) +
            ΔE / (128 * (d : ℝ) ^ 3) := add_le_add hqmul hlossE
      _ = ΔE * (1 - 7 / (128 * (d : ℝ) ^ 3)) := by ring
  have hfactor0 : 0 ≤ 1 - 7 / (128 * (d : ℝ) ^ 3) := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hden : (7 : ℝ) ≤ 128 * (d : ℝ) ^ 3 := by
      nlinarith [one_le_pow₀ (n := 3) hdR]
    exact sub_nonneg.mpr
      ((div_le_one (by positivity : (0 : ℝ) < 128 * (d : ℝ) ^ 3)).2 hden)
  have hscale := roundedEllipsoidInflation_pow_bound hd
  have hscale0 : 0 ≤ (1 + (η : ℝ)) ^ d := by
    exact pow_nonneg (by
      have hη0 : (0 : ℝ) ≤ (η : ℝ) := by
        exact_mod_cast roundedEllipsoidInflation_nonneg d
      linarith) _
  calc
    abs ((Matrix.det
        (scheduledRoundedEllipsoidCentralUpdate p E a).basis : ℚ) : ℝ) ≤
        (1 + (η : ℝ)) ^ d * (ΔU + L) := hupper
    _ ≤ (1 + (η : ℝ)) ^ d *
        (ΔE * (1 - 7 / (128 * (d : ℝ) ^ 3))) :=
      mul_le_mul_of_nonneg_left hbracket hscale0
    _ ≤ (1 + 1 / (512 * (d : ℝ) ^ 3)) *
        (ΔE * (1 - 7 / (128 * (d : ℝ) ^ 3))) := by
      exact mul_le_mul_of_nonneg_right hscale
        (mul_nonneg hΔE0 hfactor0)
    _ = ΔE * ((1 + 1 / (512 * (d : ℝ) ^ 3)) *
        (1 - 7 / (128 * (d : ℝ) ^ 3))) := by ring
    _ ≤ ΔE * (1 - 1 / (32 * (d : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left (roundedContraction_arithmetic hd) hΔE0
    _ = (1 - 1 / (32 * (d : ℝ) ^ 3)) *
        abs ((Matrix.det E.basis : ℚ) : ℝ) := by
      simp only [ΔE]
      ring

/-- A sufficiently fine scheduled rounded cut loses at most two binary bits
of determinant magnitude. -/
theorem quarter_abs_det_le_scheduledRoundedCentralUpdate {d p : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hdet : Matrix.det E.basis ≠ 0)
    (hb : rationalPulledBackNormal E a ≠ 0)
    (hp : roundedEllipsoidPrecision
      (rationalEllipsoidCentralUpdate E a) ≤ p) :
    (1 / 4 : ℝ) * abs ((Matrix.det E.basis : ℚ) : ℝ) ≤
      abs ((Matrix.det
        (scheduledRoundedEllipsoidCentralUpdate p E a).basis : ℚ) : ℝ) := by
  let U := rationalEllipsoidCentralUpdate E a
  let η := roundedEllipsoidInflation d
  let ΔE : ℝ := abs ((Matrix.det E.basis : ℚ) : ℝ)
  let ΔU : ℝ := abs ((Matrix.det U.basis : ℚ) : ℝ)
  let q : ℝ :=
    (rationalEllipsoidPerpScale d : ℝ) ^ (d - 1) *
      (rationalEllipsoidParallelScale d : ℝ)
  have hdetU : Matrix.det U.basis ≠ 0 := by
    dsimp only [U]
    rw [det_rationalEllipsoidCentralUpdate hd E a hb]
    exact mul_ne_zero hdet (mul_ne_zero
      (pow_ne_zero _ (rationalEllipsoidPerpScale_pos d).ne')
      (rationalEllipsoidParallelScale_pos hd).ne')
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    exact mul_nonneg
      (pow_nonneg (Rat.cast_nonneg.mpr
        (rationalEllipsoidPerpScale_pos d).le) _)
      (Rat.cast_nonneg.mpr (rationalEllipsoidParallelScale_pos hd).le)
  have hΔeq : ΔU = ΔE * q := by
    have hdetEq := det_rationalEllipsoidCentralUpdate hd E a hb
    dsimp only [U, ΔU, ΔE, q]
    rw [hdetEq, Rat.cast_mul, abs_mul]
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_sub,
      Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    rw [abs_of_nonneg hq0]
  have hqLower : (1 / 2 : ℝ) ≤ q := by
    simpa only [q] using rationalEllipsoid_volumeFactor_ge_half hd
  have hΔlower : (1 / 2 : ℝ) * ΔE ≤ ΔU := by
    rw [hΔeq]
    have hh : (1 / 2 : ℝ) * ΔE ≤ q * ΔE :=
      mul_le_mul_of_nonneg_right hqLower (by
        dsimp only [ΔE]
        exact abs_nonneg _)
    simpa only [mul_comm] using hh
  have hround0 := scheduledRounded_det_lower hd U hdetU hp
  have hround : ΔU / 2 ≤
      abs (((Matrix.det (dyadicFloorMatrix p U.basis) : ℚ) : ℝ)) := by
    have hcastDet : Matrix.det
        (fun i j ↦ ((dyadicFloorMatrix p U.basis i j : ℚ) : ℝ)) =
        ((Matrix.det (dyadicFloorMatrix p U.basis) : ℚ) : ℝ) := by
      rw [show (fun i j ↦
          ((dyadicFloorMatrix p U.basis i j : ℚ) : ℝ)) =
          (dyadicFloorMatrix p U.basis).map (fun q : ℚ ↦ (q : ℝ)) by rfl,
        Rat.cast_det]
    have habsCast :
        (((abs (Matrix.det U.basis) : ℚ) : ℚ) : ℝ) =
          abs (((Matrix.det U.basis : ℚ) : ℝ)) := by
      exact_mod_cast (show abs (Matrix.det U.basis) =
        abs (Matrix.det U.basis) by rfl)
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hround0
    rw [hcastDet] at hround0
    simpa only [ΔU, habsCast] using hround0
  have hscale : (1 : ℝ) ≤ (1 + (η : ℝ)) ^ d := by
    apply one_le_pow₀
    have hη0 : (0 : ℝ) ≤ (η : ℝ) := by
      dsimp only [η]
      exact_mod_cast roundedEllipsoidInflation_nonneg d
    linarith
  have hstored :
      abs (((Matrix.det (dyadicFloorMatrix p U.basis) : ℚ) : ℝ)) ≤
        abs ((Matrix.det
          (scheduledRoundedEllipsoidCentralUpdate p E a).basis : ℚ) : ℝ) := by
    rw [scheduledRoundedEllipsoidCentralUpdate, scheduledRoundedEllipsoid,
      det_inflatedDyadicRound_basis, Rat.cast_mul, abs_mul]
    change abs (((1 + η) ^ d : ℚ) : ℝ) *
        abs (((Matrix.det (dyadicFloorMatrix p U.basis) : ℚ) : ℝ)) ≥ _
    have hscaleAbs : (1 : ℝ) ≤ abs (((1 + η) ^ d : ℚ) : ℝ) := by
      rw [Rat.cast_pow, Rat.cast_add, Rat.cast_one,
        abs_of_nonneg (pow_nonneg (by
          have hη0 : (0 : ℝ) ≤ (η : ℝ) := by
            dsimp only [η]
            exact_mod_cast roundedEllipsoidInflation_nonneg d
          linarith) d)]
      exact hscale
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hscaleAbs
      (abs_nonneg (((Matrix.det (dyadicFloorMatrix p U.basis) : ℚ) : ℝ)))
  calc
    (1 / 4 : ℝ) * ΔE = ((1 / 2 : ℝ) * ΔE) / 2 := by ring
    _ ≤ ΔU / 2 := div_le_div_of_nonneg_right hΔlower (by norm_num)
    _ ≤ abs (((Matrix.det (dyadicFloorMatrix p U.basis) : ℚ) : ℝ)) := hround
    _ ≤ abs ((Matrix.det
        (scheduledRoundedEllipsoidCentralUpdate p E a).basis : ℚ) : ℝ) :=
      hstored

theorem quarter_abs_det_le_scheduledRoundedCentralUpdate_rat {d p : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hdet : Matrix.det E.basis ≠ 0)
    (hb : rationalPulledBackNormal E a ≠ 0)
    (hp : roundedEllipsoidPrecision
      (rationalEllipsoidCentralUpdate E a) ≤ p) :
    (1 / 4 : ℚ) * abs (Matrix.det E.basis) ≤
      abs (Matrix.det
        (scheduledRoundedEllipsoidCentralUpdate p E a).basis) := by
  have hreal := quarter_abs_det_le_scheduledRoundedCentralUpdate
    hd E a hdet hb hp
  have hcast :
      ((((1 / 4 : ℚ) * abs (Matrix.det E.basis) : ℚ) : ℚ) : ℝ) ≤
        ((abs (Matrix.det
          (scheduledRoundedEllipsoidCentralUpdate p E a).basis) : ℚ) : ℝ) := by
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    exact_mod_cast hreal
  exact Rat.cast_le.mp hcast

theorem rationalMatrixAbsBound_scheduledRounded_le {d p : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d) :
    rationalMatrixAbsBound (scheduledRoundedEllipsoid p U).basis ≤
      5 * d ^ 2 * rationalMatrixAbsBound U.basis := by
  let M := rationalMatrixAbsBound U.basis
  let η := roundedEllipsoidInflation d
  have hM1 : (1 : ℚ) ≤ M := rationalMatrixAbsBound_one_le U.basis
  have hη0 : 0 ≤ η := roundedEllipsoidInflation_nonneg d
  have hη1 : η ≤ 1 := roundedEllipsoidInflation_le_one hd
  have hentry : ∀ i j,
      abs ((scheduledRoundedEllipsoid p U).basis i j) ≤ 4 * M := by
    intro i j
    have hround := abs_dyadicFloor_le p (U.basis i j)
    have hmesh := dyadicMesh_le_one p
    have hU := (abs_entry_lt_rationalMatrixAbsBound U.basis i j).le
    have hfloor : abs (dyadicFloor p (U.basis i j)) ≤ 2 * M := by
      linarith
    rw [scheduledRoundedEllipsoid, inflatedDyadicRound_basis_apply, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ 1 + η)]
    calc
      (1 + η) * abs (dyadicFloor p (U.basis i j)) ≤ 2 * (2 * M) :=
        mul_le_mul (by linarith) hfloor (abs_nonneg _) (by linarith)
      _ = 4 * M := by ring
  rw [rationalMatrixAbsBound]
  calc
    1 + ∑ i, ∑ j, abs ((scheduledRoundedEllipsoid p U).basis i j) ≤
        1 + ∑ _i : Fin d, ∑ _j : Fin d, 4 * M := by
      have hs0 : (∑ i : Fin d, ∑ j : Fin d,
          abs ((scheduledRoundedEllipsoid p U).basis i j)) ≤
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

theorem rationalCenterAbsBound_scheduledRounded_le {d p : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d) :
    rationalCenterAbsBound (scheduledRoundedEllipsoid p U).center ≤
      rationalCenterAbsBound U.center + d := by
  have hentry : ∀ i,
      abs ((scheduledRoundedEllipsoid p U).center i) ≤ abs (U.center i) + 1 := by
    intro i
    have h := abs_dyadicFloor_le p (U.center i)
    have hm := dyadicMesh_le_one p
    have hadd : abs (U.center i) + dyadicMesh p ≤
        abs (U.center i) + 1 := by linarith
    change abs (dyadicFloor p (U.center i)) ≤ abs (U.center i) + 1
    exact h.le.trans hadd
  rw [rationalCenterAbsBound, rationalCenterAbsBound]
  calc
    1 + ∑ i, abs ((scheduledRoundedEllipsoid p U).center i) ≤
      1 + ∑ i, (abs (U.center i) + 1) := by
        gcongr with i
        exact hentry i
    _ = (1 + ∑ i, abs (U.center i)) + d := by
      rw [Finset.sum_add_distrib]
      simp
      ring

theorem rationalStateAbsBound_scheduledRounded_le {d p : ℕ}
    (hd : 0 < d) (U : RationalEllipsoidState d) :
    rationalStateAbsBound (scheduledRoundedEllipsoid p U) ≤
      7 * d ^ 2 * rationalStateAbsBound U := by
  have hc := rationalCenterAbsBound_scheduledRounded_le (p := p) hd U
  have hB := rationalMatrixAbsBound_scheduledRounded_le (p := p) hd U
  have hdq : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hT := rationalStateAbsBound_two_le U
  have hc0 := rationalCenterAbsBound_one_le U.center
  have hB0 := rationalMatrixAbsBound_one_le U.basis
  rw [rationalStateAbsBound, rationalStateAbsBound]
  calc
    rationalCenterAbsBound (scheduledRoundedEllipsoid p U).center +
        rationalMatrixAbsBound (scheduledRoundedEllipsoid p U).basis ≤
      (rationalCenterAbsBound U.center + d) +
        5 * d ^ 2 * rationalMatrixAbsBound U.basis := add_le_add hc hB
    _ ≤ 7 * d ^ 2 *
        (rationalCenterAbsBound U.center + rationalMatrixAbsBound U.basis) := by
      have hBnonneg : 0 ≤ rationalMatrixAbsBound U.basis :=
        (rationalMatrixAbsBound_pos U.basis).le
      nlinarith [sq_nonneg ((d : ℚ) - 1),
        mul_nonneg (sq_nonneg (d : ℚ)) hBnonneg]

theorem rationalMatrixAbsBound_scheduledCentralUpdate_le {d p : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hb : rationalPulledBackNormal E a ≠ 0) :
    rationalMatrixAbsBound
        (scheduledRoundedEllipsoidCentralUpdate p E a).basis ≤
      25 * d ^ 3 * rationalMatrixAbsBound E.basis := by
  let U := rationalEllipsoidCentralUpdate E a
  have hround := rationalMatrixAbsBound_scheduledRounded_le (p := p) hd U
  have hexact := rationalMatrixAbsBound_centralUpdate_le hd E a hb
  calc
    rationalMatrixAbsBound
        (scheduledRoundedEllipsoidCentralUpdate p E a).basis =
      rationalMatrixAbsBound (scheduledRoundedEllipsoid p U).basis := by rfl
    _ ≤ 5 * d ^ 2 * rationalMatrixAbsBound U.basis := hround
    _ ≤ 5 * d ^ 2 * (5 * d * rationalMatrixAbsBound E.basis) :=
      mul_le_mul_of_nonneg_left hexact (by positivity)
    _ = 25 * d ^ 3 * rationalMatrixAbsBound E.basis := by ring

theorem rationalStateAbsBound_scheduledCentralUpdate_le {d p : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hb : rationalPulledBackNormal E a ≠ 0) :
    rationalStateAbsBound (scheduledRoundedEllipsoidCentralUpdate p E a) ≤
      42 * d ^ 3 * rationalStateAbsBound E := by
  let U := rationalEllipsoidCentralUpdate E a
  have hround := rationalStateAbsBound_scheduledRounded_le (p := p) hd U
  have hexact := rationalStateAbsBound_centralUpdate_le hd E a hb
  calc
    rationalStateAbsBound (scheduledRoundedEllipsoidCentralUpdate p E a) =
      rationalStateAbsBound (scheduledRoundedEllipsoid p U) := by rfl
    _ ≤ 7 * d ^ 2 * rationalStateAbsBound U := hround
    _ ≤ 7 * d ^ 2 * (6 * d * rationalStateAbsBound E) :=
      mul_le_mul_of_nonneg_left hexact (by positivity)
    _ = 42 * d ^ 3 * rationalStateAbsBound E := by ring

end BeyondBethe
