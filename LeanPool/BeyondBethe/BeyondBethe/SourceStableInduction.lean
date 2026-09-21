/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.SourceStableSlice
import Mathlib.Tactic

/-! # Source Stable Induction -/

namespace BeyondBethe

/-!
# The multilinear stable-coefficient induction

This is the source proof after its analytic content has been isolated.  At
each step we contract the equal left--right coefficient, use stability of the
contraction for the induction hypothesis, and use the bivariate Rayleigh
inequality for the next pair of positive evaluation points.
-/

theorem pairTableBoundary_nonnegative :
    ∀ {n : ℕ} {α : Fin n → ℝ},
      (∀ i, 0 ≤ α i ∧ α i ≤ 1) → 0 ≤ pairTableBoundary n α := by
  intro n
  induction n with
  | zero => intro α hα; norm_num [pairTableBoundary]
  | succ n ih =>
      intro α hα
      simp only [pairTableBoundary]
      apply mul_nonneg
      · rw [stableBoundaryScalar]
        exact mul_nonneg (Real.rpow_nonneg (hα 0).1 _)
          (Real.rpow_nonneg (sub_nonneg.mpr (hα 0).2) _)
      · exact ih (fun i ↦ hα i.succ)

theorem pairTableMonomial_pos :
    ∀ {n : ℕ} {x α : Fin n → ℝ},
      (∀ i, 0 < x i) → 0 < pairTableMonomial n x α := by
  intro n
  induction n with
  | zero => intro x α hx; norm_num [pairTableMonomial]
  | succ n ih =>
      intro x α hx
      simp only [pairTableMonomial]
      exact mul_pos (Real.rpow_pos_of_pos (hx 0) _) (ih (fun i ↦ hx i.succ))

theorem pairTableEval_eq_zero_of_stablePolynomial_eq_zero
    {n : ℕ} {c : PairTable n}
    (hzero : pairTableStablePolynomial n c = 0)
    (y z : Fin n → ℝ) : pairTableEval n c y z = 0 := by
  have heval := pairTableStablePolynomial_eval_signed n c y z
  rw [hzero] at heval
  simp only [map_zero] at heval
  exact_mod_cast heval.symm

theorem pairTableDiagonalSum_nonnegative
    {n : ℕ} {c : PairTable n} (hc : PairTableNonnegative c) :
    0 ≤ pairTableDiagonalSum n c := by
  induction n with
  | zero => exact hc _ _
  | succ n ih =>
      simp only [pairTableDiagonalSum]
      exact add_nonneg
        (ih (pairTableSection_nonnegative hc false false))
        (ih (pairTableSection_nonnegative hc true true))

theorem pairTableEval_contract
    {n : ℕ} (c : PairTable (n + 1)) (y z : Fin n → ℝ) :
    pairTableEval n (pairTableContract c) y z =
      pairTableEval n (pairTableSection c false false) y z +
        pairTableEval n (pairTableSection c true true) y z := by
  rw [pairTableContract, pairTableEval_add]

theorem pairTableDiagonalSum_contract
    {n : ℕ} (c : PairTable (n + 1)) :
    pairTableDiagonalSum n (pairTableContract c) =
      pairTableDiagonalSum (n + 1) c := by
  rw [pairTableContract, pairTableDiagonalSum_add]
  rfl

/-- Approximate-attainment form of the stable-coefficient inequality.  This
is stronger than the capacity statement needed later and avoids assuming that
an infimum is attained. -/
theorem pairTable_stableCoefficient_witness :
    ∀ {n : ℕ} (c : PairTable n) (α : Fin n → ℝ),
      PairTableNonnegative c → PairTableStableOrZero c →
      (∀ i, 0 ≤ α i ∧ α i ≤ 1) →
      ∀ ε : ℝ, 0 < ε →
      ∃ y z : Fin n → ℝ,
        (∀ i, 0 < y i) ∧ (∀ i, 0 < z i) ∧
        pairTableBoundary n α *
            (pairTableEval n c y z /
              (pairTableMonomial n y α * pairTableMonomial n z α)) ≤
          pairTableDiagonalSum n c + ε := by
  intro n
  induction n with
  | zero =>
      intro c α hc hstable hα ε hε
      let y : Fin 0 → ℝ := fun i ↦ Fin.elim0 i
      let z : Fin 0 → ℝ := fun i ↦ Fin.elim0 i
      refine ⟨y, z, ?_, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
      · simp only [pairTableBoundary, pairTableMonomial, pairTableEval,
          pairTableDiagonalSum, one_mul, div_one]
        linarith
  | succ n ih =>
      intro c α hc hstable hα ε hε
      rcases hstable with hzero | hstable
      · let y : Fin (n + 1) → ℝ := fun _ ↦ 1
        let z : Fin (n + 1) → ℝ := fun _ ↦ 1
        refine ⟨y, z, (fun _ ↦ by norm_num [y]), (fun _ ↦ by norm_num [z]), ?_⟩
        have heval : pairTableEval (n + 1) c y z = 0 :=
          pairTableEval_eq_zero_of_stablePolynomial_eq_zero hzero y z
        rw [heval, zero_div, mul_zero]
        exact le_add_of_nonneg_right hε.le |>.trans'
          (pairTableDiagonalSum_nonnegative hc)
      · let αt : Fin n → ℝ := fun i ↦ α i.succ
        have hαt : ∀ i, 0 ≤ αt i ∧ αt i ≤ 1 := fun i ↦ hα i.succ
        have hcContract : PairTableNonnegative (pairTableContract c) :=
          pairTableContract_nonnegative hc
        have hsContract : PairTableStableOrZero (pairTableContract c) :=
          pairTableContract_stableOrZero c (Or.inr hstable)
        obtain ⟨yt, zt, hyt, hzt, htail⟩ :=
          ih (pairTableContract c) αt hcContract hsContract hαt (ε / 2) (half_pos hε)
        let tailBoundary := pairTableBoundary n αt
        let my := pairTableMonomial n yt αt
        let mz := pairTableMonomial n zt αt
        have hmy : 0 < my := pairTableMonomial_pos hyt
        have hmz : 0 < mz := pairTableMonomial_pos hzt
        have htailBoundary : 0 ≤ tailBoundary := pairTableBoundary_nonnegative hαt
        let K := tailBoundary / (my * mz)
        have hK : 0 ≤ K := div_nonneg htailBoundary (mul_pos hmy hmz).le
        let δ := ε / (2 * (K + 1))
        have hδ : 0 < δ := by
          dsimp [δ]
          positivity
        let a := pairTableEval n (pairTableSection c true true) yt zt
        let b := pairTableEval n (pairTableSection c true false) yt zt
        let cc := pairTableEval n (pairTableSection c false true) yt zt
        let d := pairTableEval n (pairTableSection c false false) yt zt
        have ha : 0 ≤ a := pairTableEval_nonnegative
          (pairTableSection_nonnegative hc true true)
          (fun i ↦ (hyt i).le) (fun i ↦ (hzt i).le)
        have hb : 0 ≤ b := pairTableEval_nonnegative
          (pairTableSection_nonnegative hc true false)
          (fun i ↦ (hyt i).le) (fun i ↦ (hzt i).le)
        have hcc : 0 ≤ cc := pairTableEval_nonnegative
          (pairTableSection_nonnegative hc false true)
          (fun i ↦ (hyt i).le) (fun i ↦ (hzt i).le)
        have hd : 0 ≤ d := pairTableEval_nonnegative
          (pairTableSection_nonnegative hc false false)
          (fun i ↦ (hyt i).le) (fun i ↦ (hzt i).le)
        have hrayleigh : b * cc ≤ a * d := by
          exact pairTable_slice_rayleigh hc hstable yt zt hyt hzt
        obtain ⟨Y, Z, hY, hZ, hlocal⟩ :=
          exists_bivariate_capacity_witness_nonnegative
            (hα 0) ha hb hcc hd hrayleigh hδ
        let y : Fin (n + 1) → ℝ := Fin.cases Y yt
        let z : Fin (n + 1) → ℝ := Fin.cases Z zt
        refine ⟨y, z, ?_, ?_, ?_⟩
        · intro i
          refine Fin.cases hY (fun j ↦ ?_) i
          simpa [y] using hyt j
        · intro i
          refine Fin.cases hZ (fun j ↦ ?_) i
          simpa [z] using hzt j
        · have hKδ : K * δ ≤ ε / 2 := by
            dsimp [δ]
            rw [← mul_div_assoc]
            apply (div_le_iff₀ (by positivity : 0 < 2 * (K + 1))).2
            nlinarith
          have hlocalScaled := mul_le_mul_of_nonneg_left hlocal hK
          have htail' : K * (a + d) ≤ pairTableDiagonalSum (n + 1) c + ε / 2 := by
            dsimp [K, a, d]
            rw [add_comm, ← pairTableEval_contract,
              ← pairTableDiagonalSum_contract]
            change tailBoundary / (my * mz) *
                pairTableEval n (pairTableContract c) yt zt ≤
              pairTableDiagonalSum n (pairTableContract c) + ε / 2
            calc
              tailBoundary / (my * mz) *
                    pairTableEval n (pairTableContract c) yt zt =
                  tailBoundary *
                    (pairTableEval n (pairTableContract c) yt zt / (my * mz)) := by
                      field_simp [(mul_pos hmy hmz).ne']
              _ ≤ pairTableDiagonalSum n (pairTableContract c) + ε / 2 := by
                simpa [tailBoundary, my, mz] using htail
          have hcombined :
              K * (stableBoundaryScalar (α 0) *
                ((a * Y * Z + b * Y + cc * Z + d) / (Y * Z) ^ (α 0))) ≤
                pairTableDiagonalSum (n + 1) c + ε := by
            calc
              _ ≤ K * (a + d + δ) := hlocalScaled
              _ = K * (a + d) + K * δ := by ring
              _ ≤ (pairTableDiagonalSum (n + 1) c + ε / 2) + ε / 2 :=
                add_le_add htail' hKδ
              _ = pairTableDiagonalSum (n + 1) c + ε := by ring
          have hdenfactor :
              pairTableMonomial (n + 1) y α * pairTableMonomial (n + 1) z α =
                (Y * Z) ^ (α 0) * (my * mz) := by
            simp only [pairTableMonomial]
            change (Y ^ (α 0) * my) * (Z ^ (α 0) * mz) = _
            rw [Real.mul_rpow hY.le hZ.le]
            ring
          have heval : pairTableEval (n + 1) c y z =
              a * Y * Z + b * Y + cc * Z + d := by
            simp only [pairTableEval]
            rfl
          rw [pairTableBoundary, heval, hdenfactor]
          dsimp [K, tailBoundary, my, mz] at hcombined
          have hdenTail : 0 < my * mz := mul_pos hmy hmz
          have hdenHead : 0 < (Y * Z) ^ (α 0) :=
            Real.rpow_pos_of_pos (mul_pos hY hZ) _
          calc
            stableBoundaryScalar (α 0) * pairTableBoundary n αt *
                ((a * Y * Z + b * Y + cc * Z + d) /
                  ((Y * Z) ^ (α 0) * (my * mz))) =
              (pairTableBoundary n αt / (my * mz)) *
                (stableBoundaryScalar (α 0) *
                  ((a * Y * Z + b * Y + cc * Z + d) / (Y * Z) ^ (α 0))) := by
                    field_simp [hdenTail.ne', hdenHead.ne']
            _ ≤ pairTableDiagonalSum (n + 1) c + ε := hcombined

end BeyondBethe
