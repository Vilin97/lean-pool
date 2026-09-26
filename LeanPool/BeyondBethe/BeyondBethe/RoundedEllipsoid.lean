/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MatrixPerturbation
public import Mathlib.Tactic

/-! # Rounded Ellipsoid -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Containment tools for a rounded rational ellipsoid

After an exact central-cut update we floor the center and basis to a fixed
dyadic grid and inflate the rounded basis.  The lemmas below construct the
new unit-ball coordinate explicitly with the adjugate formula and bound it
entry by entry.  Thus nonsingularity and containment are quantitative
consequences of displayed inequalities, not numerical assumptions.
-/

/-- Floor the center and basis, then inflate the basis by `1 + η`. -/
def inflatedDyadicRound {d : ℕ} (p : ℕ) (η : ℚ)
    (E : RationalEllipsoidState d) : RationalEllipsoidState d where
  center := dyadicFloorVector p E.center
  basis := fun i j ↦ (1 + η) * dyadicFloorMatrix p E.basis i j

/-- The bounded-bit central-cut update: perform the exact rational update,
then round and inflate. -/
def roundedRationalEllipsoidCentralUpdate {d : ℕ}
    (p : ℕ) (η : ℚ) (E : RationalEllipsoidState d)
    (a : Fin d → ℚ) : RationalEllipsoidState d :=
  inflatedDyadicRound p η (rationalEllipsoidCentralUpdate E a)

@[simp] theorem inflatedDyadicRound_center {d : ℕ} (p : ℕ) (η : ℚ)
    (E : RationalEllipsoidState d) :
    (inflatedDyadicRound p η E).center = dyadicFloorVector p E.center := rfl

@[simp] theorem inflatedDyadicRound_basis_apply {d : ℕ} (p : ℕ) (η : ℚ)
    (E : RationalEllipsoidState d) (i j : Fin d) :
    (inflatedDyadicRound p η E).basis i j =
      (1 + η) * dyadicFloorMatrix p E.basis i j := rfl

/-- Cramer's-rule correction solving `A v = e`.  This is used only to exhibit
a real preimage in the correctness proof; it is not part of the executable
state. -/
noncomputable def adjugateCorrection {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (e : Fin d → ℝ) : Fin d → ℝ :=
  (Matrix.det A)⁻¹ • Matrix.cramer A e

theorem mulVec_adjugateCorrection {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (e : Fin d → ℝ)
    (hdet : Matrix.det A ≠ 0) :
    Matrix.mulVec A (adjugateCorrection A e) = e := by
  rw [adjugateCorrection, Matrix.mulVec_smul, Matrix.mulVec_cramer]
  ext i
  simp [hdet]

theorem finiteNormSq_le_card_mul_sq_of_abs_le {d : ℕ}
    (v : Fin d → ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ i, abs (v i) ≤ V) :
    finiteNormSq v ≤ d * V ^ 2 := by
  rw [finiteNormSq, finiteDot,
    show (d : ℝ) * V ^ 2 = ∑ _i : Fin d, V ^ 2 by simp]
  apply Finset.sum_le_sum
  intro i _
  have habs0 : 0 ≤ abs (v i) := abs_nonneg _
  calc
    v i * v i = abs (v i) ^ 2 := by rw [sq_abs, sq]
    _ ≤ V ^ 2 := (sq_le_sq₀ habs0 hV).2 (hv i)

/-- Entrywise bound for the adjugate correction. -/
theorem abs_adjugateCorrection_le {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (e : Fin d → ℝ)
    {D M E : ℝ} (hD : 0 < D) (hdet : D ≤ abs (Matrix.det A))
    (hM : 1 ≤ M) (hA : ∀ i j, abs (A i j) ≤ M)
    (he : ∀ i, abs (e i) ≤ E) (hE : 0 ≤ E) (i : Fin d) :
    abs (adjugateCorrection A e i) ≤
      (d * (d.factorial * M ^ d) * E) / D := by
  have hdet0 : Matrix.det A ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hdet
    linarith
  have hcramer : abs (Matrix.cramer A e i) ≤
      d * (d.factorial * M ^ d) * E := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec, dotProduct]
    calc
      abs (∑ j, A.adjugate i j * e j) ≤
          ∑ j, abs (A.adjugate i j * e j) :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, (d.factorial * M ^ d) * E := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul
          (abs_adjugate_entry_le_of_entrywise A hM hA i j) (he j)
          (abs_nonneg _) (by positivity)
      _ = d * (d.factorial * M ^ d) * E := by simp; ring
  rw [adjugateCorrection, Pi.smul_apply, smul_eq_mul, abs_mul]
  have hdetAbs : 0 < abs (Matrix.det A) := abs_pos.mpr hdet0
  have hinv : (abs (Matrix.det A))⁻¹ ≤ D⁻¹ := by
    exact (inv_le_inv₀ hdetAbs hD).2 hdet
  calc
    abs ((Matrix.det A)⁻¹) * abs (Matrix.cramer A e i) =
        (abs (Matrix.det A))⁻¹ * abs (Matrix.cramer A e i) := by
      rw [abs_inv]
    _ ≤
        D⁻¹ * (d * (d.factorial * M ^ d) * E) := by
      exact mul_le_mul hinv hcramer (abs_nonneg _) (inv_nonneg.mpr hD.le)
    _ = (d * (d.factorial * M ^ d) * E) / D := by
      rw [div_eq_mul_inv]
      ring

/-- A small correction keeps the sum of an old unit vector and the
correction inside the ball inflated by `1 + η`. -/
theorem finiteNormSq_add_le_inflation_sq {d : ℕ}
    {y v : Fin d → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hy : finiteNormSq y ≤ 1) (hv : finiteNormSq v ≤ η ^ 2) :
    finiteNormSq (fun i ↦ y i + v i) ≤ (1 + η) ^ 2 := by
  have hv0 := finiteNormSq_nonneg v
  have hdotSq := finiteDot_sq_le_normSq_mul_normSq y v
  have hynonneg := finiteNormSq_nonneg y
  have hprod : finiteNormSq y * finiteNormSq v ≤ η ^ 2 := by
    calc
      finiteNormSq y * finiteNormSq v ≤ 1 * finiteNormSq v := by
        exact mul_le_mul_of_nonneg_right hy hv0
      _ ≤ η ^ 2 := by simpa using hv
  have habsdot : abs (finiteDot y v) ≤ η := by
    have hsquare : abs (finiteDot y v) ^ 2 ≤ η ^ 2 := by
      rw [sq_abs]
      exact hdotSq.trans hprod
    nlinarith [abs_nonneg (finiteDot y v)]
  rw [finiteNormSq_add]
  nlinarith [le_abs_self (finiteDot y v)]

/-- Quantitative containment after dyadic rounding and inflation.  All
quantities controlling the inverse are explicit: `D` is a determinant lower
bound, `M` is an entry bound for the rounded basis, and the final displayed
inequality is precisely the rounding-smallness condition. -/
theorem inflatedDyadicRound_contains {d : ℕ} (hd : 0 < d)
    (p : ℕ) (η : ℚ) (E : RationalEllipsoidState d)
    {D M : ℝ} (hη : 0 ≤ η) (hD : 0 < D) (hM : 1 ≤ M)
    (hA : ∀ i j,
      abs (((dyadicFloorMatrix p E.basis i j : ℚ) : ℝ)) ≤ M)
    (hdet : D ≤ abs (Matrix.det
      (fun i j ↦ ((dyadicFloorMatrix p E.basis i j : ℚ) : ℝ))))
    (hsmall :
      d *
        ((d * (d.factorial * M ^ d) *
          ((d + 1 : ℕ) * (dyadicMesh p : ℝ))) / D) ^ 2 ≤
        (η : ℝ) ^ 2)
    {y : Fin d → ℝ} (hy : finiteNormSq y ≤ 1) :
    ∃ y' : Fin d → ℝ, finiteNormSq y' ≤ 1 ∧
      rationalEllipsoidPoint (inflatedDyadicRound p η E) y' =
        rationalEllipsoidPoint E y := by
  let A : Matrix (Fin d) (Fin d) ℝ :=
    fun i j ↦ ((dyadicFloorMatrix p E.basis i j : ℚ) : ℝ)
  let e : Fin d → ℝ := fun i ↦
    (E.center i : ℝ) - (dyadicFloorVector p E.center i : ℝ) +
      ∑ j, ((E.basis i j : ℝ) - A i j) * y j
  let v : Fin d → ℝ := adjugateCorrection A e
  let s : ℝ := 1 + (η : ℝ)
  let y' : Fin d → ℝ := fun i ↦ s⁻¹ * (y i + v i)
  have hηR : 0 ≤ (η : ℝ) := Rat.cast_nonneg.mpr hη
  have hs : 0 < s := by dsimp only [s]; linarith
  have hdetA : D ≤ abs (Matrix.det A) := by simpa only [A] using hdet
  have hdet0 : Matrix.det A ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hdetA
    linarith
  have hycoord : ∀ j, abs (y j) ≤ 1 :=
    fun j ↦ abs_coordinate_le_one_of_normSq_le_one hy j
  have hcenter : ∀ i,
      abs ((E.center i : ℝ) -
        (dyadicFloorVector p E.center i : ℝ)) ≤ (dyadicMesh p : ℝ) := by
    intro i
    have h := abs_dyadicFloor_sub_lt p (E.center i)
    have hcast : abs (((dyadicFloor p (E.center i) - E.center i : ℚ) : ℝ)) <
        (dyadicMesh p : ℝ) := by exact_mod_cast h
    rw [Rat.cast_sub, abs_sub_comm] at hcast
    simpa only [dyadicFloorVector] using hcast.le
  have hbasis : ∀ i j,
      abs ((E.basis i j : ℝ) - A i j) ≤ (dyadicMesh p : ℝ) := by
    intro i j
    have h := cast_dyadicFloorMatrix_entry_error_lt p E.basis i j
    rw [Rat.cast_sub, abs_sub_comm] at h
    simpa only [A] using h.le
  have hmesh0 : (0 : ℝ) ≤ (dyadicMesh p : ℝ) := by
    exact_mod_cast dyadicMesh_nonneg p
  have he : ∀ i,
      abs (e i) ≤ ((d + 1 : ℕ) : ℝ) * (dyadicMesh p : ℝ) := by
    intro i
    dsimp only [e]
    calc
      abs ((E.center i : ℝ) -
          (dyadicFloorVector p E.center i : ℝ) +
          ∑ j, ((E.basis i j : ℝ) - A i j) * y j) ≤
        abs ((E.center i : ℝ) -
          (dyadicFloorVector p E.center i : ℝ)) +
          abs (∑ j, ((E.basis i j : ℝ) - A i j) * y j) :=
            abs_add_le _ _
      _ ≤ (dyadicMesh p : ℝ) +
          ∑ j, abs (((E.basis i j : ℝ) - A i j) * y j) :=
        add_le_add (hcenter i) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ (dyadicMesh p : ℝ) +
          ∑ _j : Fin d, (dyadicMesh p : ℝ) := by
        gcongr with j
        rw [abs_mul]
        calc
          abs ((E.basis i j : ℝ) - A i j) * abs (y j) ≤
              (dyadicMesh p : ℝ) * 1 :=
            mul_le_mul (hbasis i j) (hycoord j) (abs_nonneg _) hmesh0
          _ = (dyadicMesh p : ℝ) := mul_one _
      _ = ((d + 1 : ℕ) : ℝ) * (dyadicMesh p : ℝ) := by
        simp
        ring
  let V : ℝ :=
    (d * (d.factorial * M ^ d) *
      (((d + 1 : ℕ) : ℝ) * (dyadicMesh p : ℝ))) / D
  have hV0 : 0 ≤ V := by
    dsimp only [V]
    positivity
  have hvcoord : ∀ i, abs (v i) ≤ V := by
    intro i
    dsimp only [v, V]
    exact abs_adjugateCorrection_le A e hD hdetA hM
      (by simpa only [A] using hA) he (by positivity) i
  have hvnorm : finiteNormSq v ≤ (η : ℝ) ^ 2 := by
    have hvbound := finiteNormSq_le_card_mul_sq_of_abs_le v hV0 hvcoord
    exact hvbound.trans (by simpa only [V] using hsmall)
  have hadd : finiteNormSq (fun i ↦ y i + v i) ≤ s ^ 2 := by
    simpa only [s] using finiteNormSq_add_le_inflation_sq hηR hy hvnorm
  have hy' : finiteNormSq y' ≤ 1 := by
    have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
    rw [show y' = fun i ↦ s⁻¹ * (y i + v i) by rfl,
      finiteNormSq_smul]
    rw [inv_pow]
    calc
      (s ^ 2)⁻¹ * finiteNormSq (fun i ↦ y i + v i) ≤
          (s ^ 2)⁻¹ * s ^ 2 :=
        mul_le_mul_of_nonneg_left hadd (inv_nonneg.mpr hs2.le)
      _ = 1 := inv_mul_cancel₀ hs2.ne'
  refine ⟨y', hy', ?_⟩
  have hAv : Matrix.mulVec A v = e :=
    mulVec_adjugateCorrection A e hdet0
  ext i
  rw [rationalEllipsoidPoint, rationalEllipsoidPoint]
  change
    (dyadicFloorVector p E.center i : ℝ) +
        ∑ j, (((1 + η) * dyadicFloorMatrix p E.basis i j : ℚ) : ℝ) * y' j =
      (E.center i : ℝ) + ∑ j, (E.basis i j : ℝ) * y j
  have hsCast : ((1 + η : ℚ) : ℝ) = s := by simp [s]
  simp_rw [Rat.cast_mul, hsCast]
  have hcancel : ∀ j, s * A i j * y' j = A i j * (y j + v j) := by
    intro j
    dsimp only [y']
    field_simp [hs.ne']
  rw [show
      (∑ j, s * ((dyadicFloorMatrix p E.basis i j : ℚ) : ℝ) * y' j) =
        ∑ j, A i j * (y j + v j) by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [A] using hcancel j]
  rw [show (∑ j, A i j * (y j + v j)) =
      ∑ j, A i j * y j + Matrix.mulVec A v i by
    simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]]
  rw [hAv]
  dsimp only [e]
  ring_nf
  rw [Finset.sum_sub_distrib]
  ring

/-- Exact determinant formula for the stored rounded-and-inflated basis. -/
theorem det_inflatedDyadicRound_basis {d : ℕ} (p : ℕ) (η : ℚ)
    (E : RationalEllipsoidState d) :
    Matrix.det (inflatedDyadicRound p η E).basis =
      (1 + η) ^ d * Matrix.det (dyadicFloorMatrix p E.basis) := by
  have hbasis : (inflatedDyadicRound p η E).basis =
      (1 + η) • dyadicFloorMatrix p E.basis := by
    ext i j
    simp [inflatedDyadicRound, Matrix.smul_apply]
  rw [hbasis, Matrix.det_smul, Fintype.card_fin]

/-- Determinant upper bound after rounding and inflation. -/
theorem abs_det_inflatedDyadicRound_le {d : ℕ}
    (p : ℕ) (η : ℚ) (E : RationalEllipsoidState d)
    {M : ℝ} (hη : 0 ≤ η) (hM : 1 ≤ M)
    (hE : ∀ i j, abs ((E.basis i j : ℚ) : ℝ) ≤ M) :
    abs ((Matrix.det (inflatedDyadicRound p η E).basis : ℚ) : ℝ) ≤
      (1 + (η : ℝ)) ^ d *
        (abs ((Matrix.det E.basis : ℚ) : ℝ) +
          d.factorial *
            (d * (dyadicMesh p : ℝ) * (2 * M) ^ d)) := by
  have hscale : 0 ≤ (1 + (η : ℝ)) ^ d := by
    exact pow_nonneg (by exact_mod_cast (show (0 : ℚ) ≤ 1 + η by linarith)) _
  have hpert := abs_det_dyadicFloorMatrix_sub_det_le p E.basis hM hE
  have hround :
      abs ((Matrix.det (dyadicFloorMatrix p E.basis) : ℚ) : ℝ) ≤
        abs ((Matrix.det E.basis : ℚ) : ℝ) +
          d.factorial * (d * (dyadicMesh p : ℝ) * (2 * M) ^ d) := by
    have htriangle :
        abs (Matrix.det
            (fun i j ↦ ((dyadicFloorMatrix p E.basis i j : ℚ) : ℝ))) ≤
          abs (Matrix.det (fun i j ↦ ((E.basis i j : ℚ) : ℝ))) +
            abs (Matrix.det
                (fun i j ↦ ((dyadicFloorMatrix p E.basis i j : ℚ) : ℝ)) -
              Matrix.det (fun i j ↦ ((E.basis i j : ℚ) : ℝ))) := by
      have := abs_add_le
        (Matrix.det (fun i j ↦ ((E.basis i j : ℚ) : ℝ)))
        (Matrix.det
            (fun i j ↦ ((dyadicFloorMatrix p E.basis i j : ℚ) : ℝ)) -
          Matrix.det (fun i j ↦ ((E.basis i j : ℚ) : ℝ)))
      convert this using 1 <;> ring
    have hcastRound :
        Matrix.det
            (fun i j ↦ ((dyadicFloorMatrix p E.basis i j : ℚ) : ℝ)) =
          ((Matrix.det (dyadicFloorMatrix p E.basis) : ℚ) : ℝ) := by
      rw [show (fun i j ↦ ((dyadicFloorMatrix p E.basis i j : ℚ) : ℝ)) =
          (dyadicFloorMatrix p E.basis).map (fun q : ℚ ↦ (q : ℝ)) by rfl,
        Rat.cast_det]
    have hcastE :
        Matrix.det (fun i j ↦ ((E.basis i j : ℚ) : ℝ)) =
          ((Matrix.det E.basis : ℚ) : ℝ) := by
      rw [show (fun i j ↦ ((E.basis i j : ℚ) : ℝ)) =
          E.basis.map (fun q : ℚ ↦ (q : ℝ)) by rfl, Rat.cast_det]
    rw [hcastRound, hcastE] at htriangle hpert
    linarith
  rw [det_inflatedDyadicRound_basis]
  rw [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_one]
  rw [abs_mul, abs_pow,
    abs_of_nonneg (by exact_mod_cast (show (0 : ℚ) ≤ 1 + η by linarith))]
  exact mul_le_mul_of_nonneg_left hround hscale

/-- A valid central cut followed by sufficiently fine rounding preserves
every surviving point. -/
theorem roundedRationalEllipsoidCentralUpdate_contains {d : ℕ}
    (hd : 0 < d) (p : ℕ) (η : ℚ)
    (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    {D M : ℝ} (hη : 0 ≤ η) (hD : 0 < D) (hM : 1 ≤ M)
    (hA : ∀ i j,
      abs (((dyadicFloorMatrix p
        (rationalEllipsoidCentralUpdate E a).basis i j : ℚ) : ℝ)) ≤ M)
    (hdet : D ≤ abs (Matrix.det
      (fun i j ↦ ((dyadicFloorMatrix p
        (rationalEllipsoidCentralUpdate E a).basis i j : ℚ) : ℝ))))
    (hsmall :
      d *
        ((d * (d.factorial * M ^ d) *
          ((d + 1 : ℕ) * (dyadicMesh p : ℝ))) / D) ^ 2 ≤
        (η : ℝ) ^ 2)
    {y : Fin d → ℝ} (hy : finiteNormSq y ≤ 1)
    (hb : rationalPulledBackNormal E a ≠ 0)
    (hcut : finiteDot
      (fun i ↦ (rationalPulledBackNormal E a i : ℝ)) y ≤ 0) :
    ∃ y' : Fin d → ℝ, finiteNormSq y' ≤ 1 ∧
      rationalEllipsoidPoint
          (roundedRationalEllipsoidCentralUpdate p η E a) y' =
        rationalEllipsoidPoint E y := by
  obtain ⟨z, hz, hpoint⟩ :=
    rationalEllipsoidCentralUpdate_contains hd E a hb hy hcut
  obtain ⟨z', hz', hrounded⟩ := inflatedDyadicRound_contains hd p η
    (rationalEllipsoidCentralUpdate E a) hη hD hM hA hdet hsmall hz
  refine ⟨z', hz', ?_⟩
  rw [roundedRationalEllipsoidCentralUpdate, hrounded, hpoint]

end BeyondBethe
