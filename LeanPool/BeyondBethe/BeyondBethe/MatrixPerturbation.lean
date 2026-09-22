/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.DyadicRounding
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-! # Matrix Perturbation -/

open scoped BigOperators

namespace BeyondBethe

/-!
# Entrywise perturbation bounds for finite matrices

These estimates are intentionally elementary.  They expand the determinant
as a finite signed sum and bound each product by induction.  This avoids
appealing to an unformalized operator-norm or numerical linear-algebra result
in the rounded ellipsoid proof.
-/

theorem abs_finset_prod_le_pow {ι : Type*} {s : Finset ι}
    (f : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ i ∈ s, abs (f i) ≤ M) :
    abs (∏ i ∈ s, f i) ≤ M ^ s.card := by
  classical
  rw [Finset.abs_prod]
  simpa using Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _)
    (fun i hi ↦ hf i hi)

/-- A deliberately coarse but uniform product perturbation estimate.  The
extra factor `M` in the usual sharp estimate is harmless here and makes the
induction valid without a separate zero-cardinality case in the exponent. -/
theorem abs_finset_prod_sub_prod_le {ι : Type*} {s : Finset ι}
    (f g : ι → ℝ) {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ s, abs (f i) ≤ M)
    (hg : ∀ i ∈ s, abs (g i) ≤ M)
    (hfg : ∀ i ∈ s, abs (f i - g i) ≤ δ) :
    abs ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) ≤
      s.card * δ * M ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hM0 : 0 ≤ M := le_trans (by norm_num) hM
      have hpow0 : 0 ≤ M ^ s.card := pow_nonneg hM0 _
      have hprodF : abs (∏ i ∈ s, f i) ≤ M ^ s.card :=
        abs_finset_prod_le_pow f hM0 (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      have hih : abs ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) ≤
          s.card * δ * M ^ s.card :=
        ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hfg i (Finset.mem_insert_of_mem hi))
      have hfirst :
          abs ((f a - g a) * ∏ i ∈ s, f i) ≤ δ * M ^ s.card := by
        rw [abs_mul]
        exact mul_le_mul (hfg a (Finset.mem_insert_self a s)) hprodF
          (abs_nonneg _) hδ
      have hsecond :
          abs (g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)) ≤
            M * (s.card * δ * M ^ s.card) := by
        rw [abs_mul]
        exact mul_le_mul (hg a (Finset.mem_insert_self a s)) hih
          (abs_nonneg _) hM0
      have hpowStep : M ^ s.card ≤ M ^ (s.card + 1) := by
        rw [pow_succ]
        exact le_mul_of_one_le_right hpow0 hM
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.card_insert_of_notMem ha]
      have hdecomp :
          f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
            (f a - g a) * ∏ i ∈ s, f i +
              g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by ring
      rw [hdecomp]
      calc
        abs ((f a - g a) * ∏ i ∈ s, f i +
            g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)) ≤
          abs ((f a - g a) * ∏ i ∈ s, f i) +
            abs (g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)) :=
              abs_add_le _ _
        _ ≤ δ * M ^ s.card + M * (s.card * δ * M ^ s.card) :=
          add_le_add hfirst hsecond
        _ ≤ δ * M ^ (s.card + 1) +
            M * (s.card * δ * M ^ s.card) := by
          gcongr
        _ = ((s.card + 1 : ℕ) : ℝ) * δ * M ^ (s.card + 1) := by
          push_cast
          rw [pow_succ]
          ring

/-- Entrywise perturbation bound for determinants. -/
theorem abs_det_sub_det_le_of_entrywise {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) {M δ : ℝ}
    (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hA : ∀ i j, abs (A i j) ≤ M)
    (hB : ∀ i j, abs (B i j) ≤ M)
    (hAB : ∀ i j, abs (A i j - B i j) ≤ δ) :
    abs (Matrix.det A - Matrix.det B) ≤
      d.factorial * (d * δ * M ^ d) := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  calc
    abs (∑ σ : Equiv.Perm (Fin d),
        (σ.sign • ∏ i, A (σ i) i - σ.sign • ∏ i, B (σ i) i)) ≤
      ∑ σ : Equiv.Perm (Fin d),
        abs (σ.sign • ∏ i, A (σ i) i -
          σ.sign • ∏ i, B (σ i) i) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), d * δ * M ^ d := by
      apply Finset.sum_le_sum
      intro σ _
      rw [← smul_sub]
      change (AbsoluteValue.abs : AbsoluteValue ℝ ℝ)
          (σ.sign • ((∏ i, A (σ i) i) - ∏ i, B (σ i) i)) ≤ _
      rw [(AbsoluteValue.abs : AbsoluteValue ℝ ℝ).map_units_int_smul]
      simpa [AbsoluteValue.abs, Fintype.card_fin] using
        (abs_finset_prod_sub_prod_le
          (s := (Finset.univ : Finset (Fin d)))
          (fun i ↦ A (σ i) i) (fun i ↦ B (σ i) i)
          hM hδ (fun i _ ↦ hA _ _) (fun i _ ↦ hB _ _)
          (fun i _ ↦ hAB _ _))
    _ = d.factorial * (d * δ * M ^ d) := by
      simp [Fintype.card_perm]

/-- The standard determinant bound, specialized to real square matrices. -/
theorem abs_det_le_of_entrywise {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) {M : ℝ}
    (hA : ∀ i j, abs (A i j) ≤ M) :
    abs (Matrix.det A) ≤ d.factorial * M ^ d := by
  simpa [Fintype.card_fin, nsmul_eq_mul] using
    (Matrix.det_le (abv := (AbsoluteValue.abs : AbsoluteValue ℝ ℝ))
      (A := A) (x := M) hA)

/-- Determinant error caused by flooring every entry of a rational matrix to
one dyadic grid.  The estimate is stated after casting to `ℝ`, exactly as it
is consumed by the ellipsoid volume proof. -/
theorem abs_det_dyadicFloorMatrix_sub_det_le {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) {M : ℝ}
    (hM : 1 ≤ M) (hA : ∀ i j, abs ((A i j : ℚ) : ℝ) ≤ M) :
    abs (Matrix.det (fun i j ↦ ((dyadicFloorMatrix p A i j : ℚ) : ℝ)) -
        Matrix.det (fun i j ↦ ((A i j : ℚ) : ℝ))) ≤
      d.factorial *
        (d * (dyadicMesh p : ℝ) * (2 * M) ^ d) := by
  have hmesh0 : (0 : ℝ) ≤ (dyadicMesh p : ℝ) := by
    exact_mod_cast dyadicMesh_nonneg p
  have hmesh1 : (dyadicMesh p : ℝ) ≤ 1 := by
    exact_mod_cast dyadicMesh_le_one p
  have htwoM : (1 : ℝ) ≤ 2 * M := by linarith
  apply abs_det_sub_det_le_of_entrywise _ _ htwoM hmesh0
  · intro i j
    exact (abs_cast_dyadicFloorMatrix_le p A i j).le.trans
      (by linarith [hA i j])
  · intro i j
    exact (hA i j).trans (by linarith)
  · intro i j
    have h := cast_dyadicFloorMatrix_entry_error_lt p A i j
    simpa only [Rat.cast_sub] using h.le

/-- A determinant margin larger than the explicit rounding loss guarantees
that the rounded rational matrix remains nonsingular. -/
theorem det_dyadicFloorMatrix_ne_zero_of_margin {d : ℕ}
    (p : ℕ) (A : Matrix (Fin d) (Fin d) ℚ) {M : ℝ}
    (hM : 1 ≤ M) (hA : ∀ i j, abs ((A i j : ℚ) : ℝ) ≤ M)
    (hmargin : d.factorial *
        (d * (dyadicMesh p : ℝ) * (2 * M) ^ d) <
      abs ((Matrix.det A : ℚ) : ℝ)) :
    Matrix.det (dyadicFloorMatrix p A) ≠ 0 := by
  intro hzero
  have hpert := abs_det_dyadicFloorMatrix_sub_det_le p A hM hA
  have hcastRound :
      Matrix.det (fun i j ↦ ((dyadicFloorMatrix p A i j : ℚ) : ℝ)) = 0 := by
    rw [show (fun i j ↦ ((dyadicFloorMatrix p A i j : ℚ) : ℝ)) =
        (dyadicFloorMatrix p A).map (fun q : ℚ ↦ (q : ℝ)) by rfl,
      ← Rat.cast_det, hzero]
    simp
  have hcastA :
      Matrix.det (fun i j ↦ ((A i j : ℚ) : ℝ)) =
        ((Matrix.det A : ℚ) : ℝ) := by
    rw [show (fun i j ↦ ((A i j : ℚ) : ℝ)) =
        A.map (fun q : ℚ ↦ (q : ℝ)) by rfl, Rat.cast_det]
  rw [hcastRound, hcastA, zero_sub, abs_neg] at hpert
  exact (not_lt_of_ge hpert) hmargin

theorem abs_adjugate_entry_le_of_entrywise {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) {M : ℝ} (hM : 1 ≤ M)
    (hA : ∀ i j, abs (A i j) ≤ M) (i j : Fin d) :
    abs (A.adjugate i j) ≤ d.factorial * M ^ d := by
  have hM0 : 0 ≤ M := by linarith
  rw [Matrix.adjugate_apply]
  apply abs_det_le_of_entrywise
  intro k l
  by_cases hkj : k = j
  · subst k
    by_cases hil : i = l
    · subst l
      simp [hM]
    · simp [Matrix.updateRow_apply, hil, hM0]
  · rw [Matrix.updateRow_apply, ite_eq_right hkj]
    exact hA k l

end BeyondBethe
