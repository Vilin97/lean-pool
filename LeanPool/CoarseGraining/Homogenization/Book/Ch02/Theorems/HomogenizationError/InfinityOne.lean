/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-! # Infinity One -/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section


/-!
# The `p = infinity`, `q = 1` Homogenization Error Route

This file proves the public basic properties of the homogenization error
`\mathcal E_{s,\infty,1}` from Sec. 2.5.
-/

theorem summable_homogenizationErrorOnCube_infinity_one_terms
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0) := by
  have hOld :
      Summable (fun n : ℕ =>
        Homogenization.geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0) := by
    refine Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s) (q := 1)
      (C := Real.rpow (normalizedBlockResponseUniformBound Q a a0) (1 / 2 : ℝ))
      (by simpa using hs) ?_ ?_
    · intro n
      exact scaleResponseAtScale_infinity_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0
    · intro n
      exact scaleResponseAtScale_infinity_le_uniform Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0
  simpa [geometricWeight_eq_old] using hOld

theorem HomogenizationErrorOnCube_infinity_one_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    0 ≤ HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum]
  refine tsum_nonneg ?_
  intro n
  refine mul_nonneg ?_ ?_
  · simpa [geometricWeight_eq_old] using
      (Homogenization.geometricWeight_nonneg (s := s) (q := 1) n
        (by simpa using hs.le))
  · exact scaleResponseAtScale_infinity_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0

theorem scaleResponseAtScale_infinity_self_le_homogenizationErrorOnCube_infinity_one
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    scaleResponseAtScale Q Q.scale .infinity a a0 ≤
      HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  let c : ℝ := scaleResponseAtScale Q Q.scale .infinity a a0
  let g : ℕ → ℝ := fun n => geometricWeight s 1 n * c
  let f : ℕ → ℝ := fun n =>
    geometricWeight s 1 n *
      scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0
  have hsum : Summable f := by
    simpa [f] using
      summable_homogenizationErrorOnCube_infinity_one_terms Q a a0 hs
  have hgSummable : Summable g := by
    have hOld :
        Summable (fun n : ℕ => Homogenization.geometricWeight s 1 n * c) :=
      (Homogenization.summable_geometricWeight_one (s := s) hs).mul_right c
    simpa [g, geometricWeight_eq_old] using hOld
  have hterm : ∀ n : ℕ, g n ≤ f n := by
    intro n
    have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
      exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hresp :
        scaleResponseAtScale Q Q.scale .infinity a a0 ≤
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0 :=
      scaleResponseAtScale_infinity_self_le Q hk a a0
    dsimp [g, f, c]
    exact mul_le_mul_of_nonneg_left hresp (by
      simpa [geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := s) (q := 1) n
          (by simpa using hs.le)))
  have hsumLe : ∑' n : ℕ, g n ≤ ∑' n : ℕ, f n :=
    Summable.tsum_le_tsum hterm hgSummable hsum
  have hgEq : ∑' n : ℕ, g n = c := by
    have hweight : (∑' n : ℕ, geometricWeight s 1 n) = 1 := by
      simpa [geometricWeight_eq_old] using
        (Homogenization.tsum_geometricWeight_one_eq_one (s := s) hs)
    dsimp [g, c]
    rw [tsum_mul_right, hweight, one_mul]
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum]
  calc
    scaleResponseAtScale Q Q.scale .infinity a a0 = ∑' n : ℕ, g n := by
      exact hgEq.symm
    _ ≤ ∑' n : ℕ, f n := hsumLe

theorem homogenizationErrorOnCube_infinity_one_le_of_lt
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (a0 : Mat d)
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 ≤
      HomogenizationErrorOnCube Q t .infinity (.finite 1) a a0 := by
  let H : ℕ → ℝ := fun n =>
    scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0
  have hmono : Monotone H := by
    intro m n hmn
    have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by
      linarith
    have hlQ : Q.scale - (m : ℤ) ≤ Q.scale := by
      exact sub_le_self _ (by exact_mod_cast Nat.zero_le m)
    exact scaleResponseAtScale_infinity_le_of_le
      (Q := Q) (k := Q.scale - (n : ℤ)) (l := Q.scale - (m : ℤ))
      hkl hlQ a a0
  have hnonneg : ∀ n : ℕ, 0 ≤ H n := by
    intro n
    exact scaleResponseAtScale_infinity_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0
  have hsum_t_old :
      Summable (fun n : ℕ => Homogenization.geometricWeight t 1 n * H n) := by
    have hsum_t :=
      summable_homogenizationErrorOnCube_infinity_one_terms Q a a0 ht
    simpa [H, geometricWeight_eq_old] using hsum_t
  have hOld :=
    Homogenization.tsum_geometricWeight_one_le_of_monotone
      (H := H) hmono hnonneg ht hts hsum_t_old
  rw [homogenizationErrorOnCube_infinity_one_eq_tsum,
    homogenizationErrorOnCube_infinity_one_eq_tsum]
  simpa [H, geometricWeight_eq_old] using hOld

theorem homogenizationErrorOnCube_infinity_one_le_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (a : TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ}
    (hs : 0 < s) (hR : R ∈ descendantsAtScale Q k) :
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
  have hsum : Summable fQ := by
    simpa [fQ] using
      summable_homogenizationErrorOnCube_infinity_one_terms Q a a0 hs
  have hQnonneg : ∀ n : ℕ, 0 ≤ fQ n := by
    intro n
    dsimp [fQ]
    refine mul_nonneg ?_ ?_
    · simpa [geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := s) (q := 1) n
          (by simpa using hs.le))
    · exact scaleResponseAtScale_infinity_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0
  have htailSummable : Summable (fun n : ℕ => fQ (n + h)) :=
    (summable_nat_add_iff h).2 hsum
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
      have hl : R.scale - (n : ℤ) ≤ R.scale :=
        sub_le_self _ (by exact_mod_cast Nat.zero_le n)
      simpa [hscale] using
        (scaleResponseAtScale_infinity_le_of_mem_descendantsAtScale
          (Q := Q) (R := R) (k := k) (l := R.scale - (n : ℤ)) a a0 hR hl)
    have hshift :
        geometricWeight s 1 n =
          factor * geometricWeight s 1 (n + h) := by
      simpa [factor, geometricWeight_eq_old] using
        (Homogenization.geometricWeight_one_shift (s := s) h n)
    calc
      fR n =
          factor *
            (geometricWeight s 1 (n + h) *
              scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0) := by
        dsimp [fR]
        rw [hshift]
        ring
      _ ≤ factor *
          (geometricWeight s 1 (n + h) *
            scaleResponseAtScale Q (Q.scale - ((n + h : ℕ) : ℤ)) .infinity a a0) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactorNonneg
        exact mul_le_mul_of_nonneg_left hresp (by
          simpa [geometricWeight_eq_old] using
            (Homogenization.geometricWeight_nonneg (s := s) (q := 1) (n + h)
              (by simpa using hs.le)))
      _ = factor * fQ (n + h) := by
        dsimp [fQ]
  have hRnonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    dsimp [fR]
    refine mul_nonneg ?_ ?_
    · simpa [geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := s) (q := 1) n
          (by simpa using hs.le))
    · exact scaleResponseAtScale_infinity_nonneg R
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0
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
    have hprefixNonneg : 0 ≤ ∑ i ∈ Finset.range h, fQ i :=
      Finset.sum_nonneg fun i _ => hQnonneg i
    linarith
  calc
    HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 =
        ∑' n : ℕ, fR n := by
      rw [homogenizationErrorOnCube_infinity_one_eq_tsum]
    _ ≤ ∑' n : ℕ, factor * fQ (n + h) := hsumLe
    _ = factor * ∑' n : ℕ, fQ (n + h) := by
      simpa using (Summable.tsum_mul_left factor htailSummable)
    _ ≤ factor * ∑' n : ℕ, fQ n := by
      exact mul_le_mul_of_nonneg_left htailLe hfactorNonneg
    _ = factor * HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
      rw [homogenizationErrorOnCube_infinity_one_eq_tsum]

theorem homogenizationErrorOnCube_infinity_one_descendantsAtScale_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a : TriadicCoeffFamily d) (a0 : Mat d)
    {s : ℝ} (hs : 0 < s) :
    finsetSupReal (descendantsAtScale Q k)
        (fun R => HomogenizationErrorOnCube R s .infinity (.finite 1) a a0) ≤
      Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  unfold finsetSupReal
  have hne :
      ((fun R => HomogenizationErrorOnCube R s .infinity (.finite 1) a a0) ''
        (↑(descendantsAtScale Q k) : Set (TriadicCube d))).Nonempty := by
    rcases descendantsAtScale_nonempty Q hk with ⟨R, hR⟩
    exact ⟨HomogenizationErrorOnCube R s .infinity (.finite 1) a a0,
      ⟨R, hR, rfl⟩⟩
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact homogenizationErrorOnCube_infinity_one_le_of_mem_descendantsAtScale
    (Q := Q) (R := R) (k := k) a a0 hs hR

/-- Public proof package for the `p = infinity`, `q = 1` basic properties of
the homogenization error. -/
theorem homogenizationErrorInfinityOneBasicTheory
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (a0 : Mat d) :
    HomogenizationErrorInfinityOneBasicTheory Q a a0 := by
  refine
    { scaleResponse_nonneg := ?_
      error_nonneg := ?_
      oneCube_le_error := ?_
      error_antitone := ?_
      descendant_error_le := ?_
      descendants_error_sup_le := ?_ }
  · intro k hk
    exact scaleResponseAtScale_infinity_nonneg Q hk a a0
  · intro s hs
    exact HomogenizationErrorOnCube_infinity_one_nonneg Q a a0 hs
  · intro s hs
    exact scaleResponseAtScale_infinity_self_le_homogenizationErrorOnCube_infinity_one Q a a0 hs
  · intro t s ht hts
    exact homogenizationErrorOnCube_infinity_one_le_of_lt Q a a0 ht hts
  · intro R k s hR hs
    exact homogenizationErrorOnCube_infinity_one_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) a a0 hs hR
  · intro k s hk hs
    exact homogenizationErrorOnCube_infinity_one_descendantsAtScale_le Q hk a a0 hs

end

end Ch02
end Book
end Homogenization
