/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Response

/-! # Homogenization Error -/

namespace Homogenization

noncomputable section

open scoped Matrix.Norms.Frobenius
open scoped MatrixOrder

/-!
# q = 1 homogenization-error theorems
-/

theorem homogenizationErrorOnCube_infinity_one_le_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (hs : 0 ≤ s) (hR : R ∈ descendantsAtScale Q k)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 ≤
      Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  let h : ℕ := Int.toNat (Q.scale - k)
  let fQ : ℕ → ℝ := fun n =>
    geometricWeight s 1 n *
      scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0
  let fR : ℕ → ℝ := fun n =>
    geometricWeight s 1 n *
      scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0
  let factor : ℝ := Real.rpow (3 : ℝ) (s * (h : ℝ))
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hh : (h : ℤ) = Q.scale - k := by
    dsimp [h]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hQnonneg : ∀ n : ℕ, 0 ≤ fQ n := by
    intro n
    dsimp [fQ]
    exact mul_nonneg (geometricWeight_nonneg n (by simpa using hs))
      (scaleResponseAtScale_infinity_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0)
  have htailSummable : Summable (fun n : ℕ => fQ (n + h)) := (summable_nat_add_iff h).2 hsum
  have hfactorNonneg : 0 ≤ factor := by
    dsimp [factor]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hterm :
      ∀ n : ℕ, fR n ≤ factor * fQ (n + h) := by
    intro n
    have hscale :
        R.scale - (n : ℤ) = Q.scale - ((n + h : ℕ) : ℤ) := by
      rw [hRscale, Nat.cast_add, hh]
      ring
    have hresp :
        scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0 ≤
          scaleResponseAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) .infinity a a0 := by
      have hl : R.scale - (n : ℤ) ≤ R.scale := sub_le_self _ (by exact_mod_cast Nat.zero_le n)
      simpa [hscale] using
        (scaleResponseAtScale_infinity_le_of_mem_descendantsAtScale
          (Q := Q) (R := R) (k := k) (l := R.scale - (n : ℤ)) a a0 hR hl)
    calc
      fR n =
          factor *
            (geometricWeight s 1 (n + h) *
              scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) := by
        dsimp [fR, factor]
        rw [geometricWeight_one_shift (s := s) h n]
        simp [mul_left_comm, mul_comm]
      _ ≤ factor *
          (geometricWeight s 1 (n + h) *
            scaleResponseAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) .infinity a a0) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
        exact mul_le_mul_of_nonneg_left hresp
          (geometricWeight_nonneg (n + h) (by simpa using hs))
      _ = factor * fQ (n + h) := by
        dsimp [fQ]
  have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    dsimp [fR]
    exact mul_nonneg (geometricWeight_nonneg n (by simpa using hs))
      (scaleResponseAtScale_infinity_nonneg R
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0)
  have hscaledNonneg : ∀ n : ℕ, 0 ≤ factor * fQ (n + h) := by
    intro n
    exact mul_nonneg hfactorNonneg (hQnonneg (n + h))
  have hscaledSummable : Summable (fun n : ℕ => factor * fQ (n + h)) :=
    htailSummable.mul_left factor
  have hRsummable : Summable fR :=
    Summable.of_nonneg_of_le hRnonneg hterm hscaledSummable
  have hsumLe :
      ∑' n : ℕ, fR n ≤ ∑' n : ℕ, factor * fQ (n + h) :=
    Summable.tsum_le_tsum hterm hRsummable hscaledSummable
  have htailLe :
      ∑' n : ℕ, fQ (n + h) ≤ ∑' n : ℕ, fQ n := by
    have hsplit := hsum.sum_add_tsum_nat_add h
    have hprefixNonneg : 0 ≤ ∑ i ∈ Finset.range h, fQ i := by
      exact Finset.sum_nonneg (fun i _ => hQnonneg i)
    linarith
  calc
    HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 = ∑' n : ℕ, fR n := by
      rw [homogenizationErrorOnCube_infinity_one_eq_tsum]
    _ ≤ ∑' n : ℕ, factor * fQ (n + h) := hsumLe
    _ = factor * ∑' n : ℕ, fQ (n + h) := by
      simpa using (Summable.tsum_mul_left factor htailSummable)
    _ ≤ factor * ∑' n : ℕ, fQ n := by
      exact mul_le_mul_of_nonneg_left htailLe hfactorNonneg
    _ = factor * HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
      rw [homogenizationErrorOnCube_infinity_one_eq_tsum]

theorem homogenizationErrorOnCube_infinity_one_descendantsAtScale_le {d : ℕ}
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (hs : 0 ≤ s)
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    finsetSsup (descendantsAtScale Q k)
        (fun R => HomogenizationErrorOnCube R s .infinity (.finite 1) a a0) ≤
      Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  unfold finsetSsup
  have hne :
      ((fun R => HomogenizationErrorOnCube R s .infinity (.finite 1) a a0) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨HomogenizationErrorOnCube R s .infinity (.finite 1) a a0, ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact homogenizationErrorOnCube_infinity_one_le_of_mem_descendantsAtScale
    (Q := Q) (R := R) (k := k) a a0 s hs hR hsum

theorem homogenizationErrorOnCube_infinity_one_basic_properties_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {t s : ℝ} {lam Lam : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0))
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    scaleResponseAtScale Q Q.scale .infinity a a0 ≤
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 ∧
      HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 ≤
        HomogenizationErrorOnCube Q t .infinity (.finite 1) a a0 ∧
      ∀ {k : ℤ}, k ≤ Q.scale →
        finsetSsup (descendantsAtScale Q k)
            (fun R => HomogenizationErrorOnCube R s .infinity (.finite 1) a a0) ≤
          Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
            HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      scaleResponseAtScale_infinity_self_le_homogenizationErrorOnCube_infinity_one_of_isEllipticFieldOn
        Q a a0 s hs hEll hsum_s
  · exact
      homogenizationErrorOnCube_infinity_one_le_of_lt_of_isEllipticFieldOn
        Q a a0 ht hts hEll hsum_t
  · intro k hk
    exact homogenizationErrorOnCube_infinity_one_descendantsAtScale_le
      Q hk a a0 s hs.le hsum_s

theorem oneCubeDefect_rpow_half_sSup_le_homogenizationErrorOnCube_infinity_one_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} {lam Lam : ℝ} (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    Real.rpow
        (sSup
          { m | ∃ e : FullBlockVec d, fullBlockVecNormSq e = 1 ∧
              let P :=
                ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)
              let Q' :=
                ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)
              m =
                (1 / 2 : ℝ) * ResponseJ (cubeSet Q) (P.1 - Q'.2) (Q'.1 - P.2) a +
                  (1 / 2 : ℝ) *
                    ResponseJ (cubeSet Q) (Q'.2 + P.1) (Q'.1 + P.2)
                      (Homogenization.adjointCoeffField a) }) (1 / 2 : ℝ) ≤
      HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  simpa [scaleResponseAtScale_infinity_self_eq_rpow_half_sSup_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    Q a a0 hEll] using
    (scaleResponseAtScale_infinity_self_le_homogenizationErrorOnCube_infinity_one_of_isEllipticFieldOn
      Q a a0 s hs hEll hsum_s)

theorem homogenizationErrorOnCube_infinity_one_note_basic_properties_of_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {t s : ℝ} {lam Lam : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0))
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    Real.rpow
        (sSup
          { m | ∃ e : FullBlockVec d, fullBlockVecNormSq e = 1 ∧
              let P :=
                ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e)
              let Q' :=
                ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e)
              m =
                (1 / 2 : ℝ) * ResponseJ (cubeSet Q) (P.1 - Q'.2) (Q'.1 - P.2) a +
                  (1 / 2 : ℝ) *
                    ResponseJ (cubeSet Q) (Q'.2 + P.1) (Q'.1 + P.2)
                      (Homogenization.adjointCoeffField a) }) (1 / 2 : ℝ) ≤
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 ∧
      HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 ≤
        HomogenizationErrorOnCube Q t .infinity (.finite 1) a a0 ∧
      ∀ {k : ℤ}, k ≤ Q.scale →
        finsetSsup (descendantsAtScale Q k)
            (fun R => HomogenizationErrorOnCube R s .infinity (.finite 1) a a0) ≤
          Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
            HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  have hbasic :=
    homogenizationErrorOnCube_infinity_one_basic_properties_of_isEllipticFieldOn
      Q a a0 hs ht hts hEll hsum_s hsum_t
  refine ⟨?_, hbasic.2.1, ?_⟩
  · exact
      oneCubeDefect_rpow_half_sSup_le_homogenizationErrorOnCube_infinity_one_of_isEllipticFieldOn
        Q a a0 hs hEll hsum_s
  · intro k hk
    exact hbasic.2.2 hk

end

end Homogenization
