/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties
import Mathlib.Algebra.Order.Chebyshev

/-! # Small Tail -/

namespace Homogenization
namespace Book
namespace Ch02

/-!
# Deterministic small-scale tails for q = 1

This file records the Ch2 operator-norm version of the deterministic
small-tail split at scale zero.
-/

noncomputable section

open scoped BigOperators

/-- Shift identity for the q = 1 geometric weights in the small-scale tail. -/
theorem smallTail_geometricWeight_one_nat_add_eq
    (s : ℝ) (j m : ℕ) :
    geometricWeight s 1 (j + m) =
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) * geometricWeight s 1 j := by
  have hexp :
      -s * 1 * ((j + m : ℕ) : ℝ) =
        (-s * (m : ℝ)) + (-s * 1 * (j : ℝ)) := by
    norm_num
    ring
  have hpow :
      Real.rpow (3 : ℝ) ((-s * (m : ℝ)) + (-s * 1 * (j : ℝ))) =
        Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
          Real.rpow (3 : ℝ) (-s * 1 * (j : ℝ)) :=
    Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _
  unfold geometricWeight
  rw [hexp, hpow]
  ring

/--
Converse to descendant-depth transitivity: a descendant at depth `m + n`
factors through some depth-`m` intermediate cube.
-/
theorem smallTail_exists_descendant_ancestor_at_depth {d : ℕ}
    {Q R : TriadicCube d} (m n : ℕ)
    (hR : R ∈ descendantsAtDepth Q (m + n)) :
    ∃ U ∈ descendantsAtDepth Q m, R ∈ descendantsAtDepth U n := by
  induction n generalizing R with
  | zero =>
      exact ⟨R, by simpa using hR, by simp⟩
  | succ n ih =>
      have hRsucc : R ∈ descendantsAtDepth Q ((m + n) + 1) := by
        simpa [Nat.add_assoc] using hR
      rw [mem_descendantsAtDepth_succ_iff] at hRsucc
      rcases hRsucc with ⟨S, hS, hRS⟩
      rcases ih hS with ⟨U, hU, hSU⟩
      refine ⟨U, hU, ?_⟩
      rw [mem_descendantsAtDepth_succ_iff]
      exact ⟨S, hSU, hRS⟩

/--
Every descendant of `cu_m` at a nonpositive absolute scale `-j` factors
through a scale-zero descendant of `cu_m`.
-/
theorem smallTail_exists_scale_zero_ancestor_of_mem_descendantsAtScale_originCube_neg_nat
    {d : ℕ} {m j : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (-(j : ℤ))) :
    ∃ U ∈ descendantsAtScale (originCube d (m : ℤ)) 0,
      R ∈ descendantsAtScale U (-(j : ℤ)) := by
  let Q : TriadicCube d := originCube d (m : ℤ)
  have hk : -(j : ℤ) ≤ Q.scale := by
    dsimp [Q, originCube]
    omega
  have hdepth : R ∈ descendantsAtDepth Q (m + j) := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
    have htoNat : Int.toNat (Q.scale - (-(j : ℤ))) = m + j := by
      have hdiff : Q.scale - (-(j : ℤ)) = ((m + j : ℕ) : ℤ) := by
        dsimp [Q, originCube]
        omega
      rw [hdiff]
      simpa [Int.natCast_add] using (Int.toNat_natCast (m + j))
    simpa [htoNat] using! hR
  rcases smallTail_exists_descendant_ancestor_at_depth
      (Q := Q) (R := R) m j hdepth with
    ⟨U, hUdepth, hRUdepth⟩
  have hUscale_zero : U.scale = 0 := by
    have hscale := scale_eq_sub_of_mem_descendantsAtDepth hUdepth
    dsimp [Q, originCube] at hscale
    omega
  have hUscale : U ∈ descendantsAtScale Q 0 := by
    have h0 : (0 : ℤ) ≤ Q.scale := by
      dsimp [Q, originCube]
      exact_mod_cast Nat.zero_le m
    rw [descendantsAtScale_eq_descendantsAtDepth Q h0]
    have htoNat : Int.toNat (Q.scale - 0) = m := by
      dsimp [Q, originCube]
      simp
    simpa [htoNat] using! hUdepth
  have hRUscale : R ∈ descendantsAtScale U (-(j : ℤ)) := by
    have hle : -(j : ℤ) ≤ U.scale := by omega
    rw [descendantsAtScale_eq_descendantsAtDepth U hle]
    have htoNat : Int.toNat (U.scale - (-(j : ℤ))) = j := by
      rw [hUscale_zero]
      simp
    change R ∈ descendantsAtDepth U (Int.toNat (U.scale - (-(j : ℤ))))
    rw [htoNat]
    exact hRUdepth
  exact ⟨U, by simpa [Q] using hUscale, hRUscale⟩

theorem coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale_of_mem_descendantsAtScale
    {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (a : TriadicCoeffFamily d) (hR : R ∈ descendantsAtScale Q k) :
    coarseBMatrixNorm R a ≤ maxDescendantBMatrixNormAtScale Q k a := by
  unfold maxDescendantBMatrixNormAtScale finsetSupReal
  have hbdd :
      BddAbove
        ((fun R : TriadicCube d => coarseBMatrixNorm R a) ''
          (↑(descendantsAtScale Q k) : Set (TriadicCube d))) := by
    exact ((Set.toFinite _).image (fun R : TriadicCube d => coarseBMatrixNorm R a)).bddAbove
  exact le_csSup hbdd ⟨R, hR, rfl⟩

theorem coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale_of_mem_descendantsAtScale
    {d : ℕ} {Q R : TriadicCube d} {k : ℤ}
    (a : TriadicCoeffFamily d) (hR : R ∈ descendantsAtScale Q k) :
    coarseSigmaStarInvMatrixNorm R a ≤
      maxDescendantSigmaStarInvMatrixNormAtScale Q k a := by
  unfold maxDescendantSigmaStarInvMatrixNormAtScale finsetSupReal
  have hbdd :
      BddAbove
        ((fun R : TriadicCube d => coarseSigmaStarInvMatrixNorm R a) ''
          (↑(descendantsAtScale Q k) : Set (TriadicCube d))) := by
    exact
      ((Set.toFinite _).image
        (fun R : TriadicCube d => coarseSigmaStarInvMatrixNorm R a)).bddAbove
  exact le_csSup hbdd ⟨R, hR, rfl⟩

/--
For a fixed scale-zero cube, the small-scale q = 1 square-root tail is exactly
the local `LambdaSq` square-root series times the global scale factor
`3^{-sm}`.
-/
theorem smallTail_tsum_weighted_scale_zero_B_sqrt_tail_eq_LambdaSq_rpow_half
    {d : ℕ} [NeZero d] {U : TriadicCube d} (hUscale : U.scale = 0)
    (s : ℝ) (m : ℕ) (a : TriadicCoeffFamily d) (hs : 0 ≤ s) :
    (∑' j : ℕ,
      geometricWeight s 1 (j + m) *
        Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ)) =
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        Real.rpow (LambdaSq U s (.finite 1) a) (1 / 2 : ℝ) := by
  calc
    (∑' j : ℕ,
      geometricWeight s 1 (j + m) *
        Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ))
        =
        ∑' j : ℕ,
          Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
            (geometricWeight s 1 j *
              Real.rpow
                (maxDescendantBMatrixNormAtScale U (U.scale - (j : ℤ)) a)
                (1 / 2 : ℝ)) := by
          congr with j
          have hscale : U.scale - (j : ℤ) = -(j : ℤ) := by
            rw [hUscale]
            ring
          rw [smallTail_geometricWeight_one_nat_add_eq, hscale]
          ring
    _ =
        Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
          ∑' j : ℕ,
            geometricWeight s 1 j *
              Real.rpow
                (maxDescendantBMatrixNormAtScale U (U.scale - (j : ℤ)) a)
                (1 / 2 : ℝ) := by
          rw [tsum_mul_left]
    _ =
        Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
          Real.rpow (LambdaSq U s (.finite 1) a) (1 / 2 : ℝ) := by
          rw [LambdaSqFinite_rpow_q_div_two_eq_tsum U s 1 a
            (by norm_num : (0 : ℝ) < 1) (by simpa using hs)]

/--
For a fixed scale-zero cube, the small-scale q = 1 lower inverse square-root
tail is exactly the local `lambdaSq` inverse square-root series times the
global scale factor `3^{-sm}`.
-/
theorem smallTail_tsum_weighted_scale_zero_sigmaStarInv_sqrt_tail_eq_lambdaSq_rpow_neg_half
    {d : ℕ} [NeZero d] {U : TriadicCube d} (hUscale : U.scale = 0)
    (s : ℝ) (m : ℕ) (a : TriadicCoeffFamily d) (hs : 0 ≤ s) :
    (∑' j : ℕ,
      geometricWeight s 1 (j + m) *
        Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ)) =
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        Real.rpow (lambdaSq U s (.finite 1) a) (-1 / 2 : ℝ) := by
  calc
    (∑' j : ℕ,
      geometricWeight s 1 (j + m) *
        Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ))
        =
        ∑' j : ℕ,
          Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
            (geometricWeight s 1 j *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale U (U.scale - (j : ℤ)) a)
                (1 / 2 : ℝ)) := by
          congr with j
          have hscale : U.scale - (j : ℤ) = -(j : ℤ) := by
            rw [hUscale]
            ring
          rw [smallTail_geometricWeight_one_nat_add_eq, hscale]
          ring
    _ =
        Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
          ∑' j : ℕ,
            geometricWeight s 1 j *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale U (U.scale - (j : ℤ)) a)
                (1 / 2 : ℝ) := by
          rw [tsum_mul_left]
    _ =
        Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
          Real.rpow (lambdaSq U s (.finite 1) a) (-1 / 2 : ℝ) := by
          rw [lambdaSqFinite_rpow_neg_q_div_two_eq_tsum U s 1 a
            (by norm_num : (0 : ℝ) < 1) (by simpa using hs)]

/-- The upper small-scale square-root tail after splitting at scale zero. -/
noncomputable def upperSmallSqrtTail {d : ℕ}
    (m : ℕ) (s : ℝ) (a : TriadicCoeffFamily d) : ℝ :=
  ∑' j : ℕ,
    geometricWeight s 1 (j + m) *
      Real.rpow
        (maxDescendantBMatrixNormAtScale (originCube d (m : ℤ)) (-(j : ℤ)) a)
        (1 / 2 : ℝ)

/-- The lower inverse small-scale square-root tail after splitting at scale zero. -/
noncomputable def lowerSmallSqrtTail {d : ℕ}
    (m : ℕ) (s : ℝ) (a : TriadicCoeffFamily d) : ℝ :=
  ∑' j : ℕ,
    geometricWeight s 1 (j + m) *
      Real.rpow
        (maxDescendantSigmaStarInvMatrixNormAtScale
          (originCube d (m : ℤ)) (-(j : ℤ)) a)
        (1 / 2 : ℝ)

theorem summable_upperSmallSqrtTail_scale_zero
    {d : ℕ} [NeZero d] {U : TriadicCube d} (hUscale : U.scale = 0)
    (m : ℕ) {s : ℝ} (hs : 0 < s) (a : TriadicCoeffFamily d) :
    Summable (fun j : ℕ =>
      geometricWeight s 1 (j + m) *
        Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ)) := by
  have hbase :=
    summable_B_series_pointwiseCoeffField U a hs (by norm_num : (0 : ℝ) < 1)
  refine (hbase.mul_left (Real.rpow (3 : ℝ) (-s * (m : ℝ)))).congr ?_
  intro j
  have hscale : U.scale - (j : ℤ) = -(j : ℤ) := by
    rw [hUscale]
    ring
  rw [smallTail_geometricWeight_one_nat_add_eq, hscale]
  ring

theorem summable_lowerSmallSqrtTail_scale_zero
    {d : ℕ} [NeZero d] {U : TriadicCube d} (hUscale : U.scale = 0)
    (m : ℕ) {s : ℝ} (hs : 0 < s) (a : TriadicCoeffFamily d) :
    Summable (fun j : ℕ =>
      geometricWeight s 1 (j + m) *
        Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ)) := by
  have hbase :=
    summable_sigmaStarInv_series_pointwiseCoeffField U a hs
      (by norm_num : (0 : ℝ) < 1)
  refine (hbase.mul_left (Real.rpow (3 : ℝ) (-s * (m : ℝ)))).congr ?_
  intro j
  have hscale : U.scale - (j : ℤ) = -(j : ℤ) := by
    rw [hUscale]
    ring
  rw [smallTail_geometricWeight_one_nat_add_eq, hscale]
  ring

/--
At a fixed small depth, the upper square-root maximum below `cu_m` is bounded
by summing the corresponding local maxima over the scale-zero descendants of
`cu_m`.
-/
theorem rpow_half_maxDescendantBMatrixNormAtScale_originCube_neg_nat_le_sum_scale_zero
    {d : ℕ} [NeZero d] (m j : ℕ) (a : TriadicCoeffFamily d) :
    Real.rpow
        (maxDescendantBMatrixNormAtScale (originCube d (m : ℤ)) (-(j : ℤ)) a)
        (1 / 2 : ℝ) ≤
      ∑ U ∈ descendantsAtScale (originCube d (m : ℤ)) 0,
        Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a) (1 / 2 : ℝ) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  let T : ℝ :=
    ∑ U ∈ D, Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a) (1 / 2 : ℝ)
  have hT_nonneg : 0 ≤ T := by
    refine Finset.sum_nonneg ?_
    intro U hU
    have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
    exact Real.rpow_nonneg
      (maxDescendantBMatrixNormAtScale_nonneg U (by rw [hUscale]; omega) a) _
  have hglobal_le_sq :
      maxDescendantBMatrixNormAtScale Q (-(j : ℤ)) a ≤ T ^ 2 := by
    unfold maxDescendantBMatrixNormAtScale finsetSupReal
    have hne :
        ((fun R => coarseBMatrixNorm R a) ''
          (↑(descendantsAtScale Q (-(j : ℤ))) : Set (TriadicCube d))).Nonempty := by
      have hjQ : -(j : ℤ) ≤ Q.scale := by
        dsimp [Q, originCube]
        omega
      rcases descendantsAtScale_nonempty Q hjQ with ⟨R, hR⟩
      exact ⟨coarseBMatrixNorm R a, ⟨R, hR, rfl⟩⟩
    refine csSup_le hne ?_
    rintro x ⟨R, hR, rfl⟩
    rcases
      smallTail_exists_scale_zero_ancestor_of_mem_descendantsAtScale_originCube_neg_nat
        (m := m) (j := j) (R := R) (by simpa [Q] using hR) with
      ⟨U, hU, hRU⟩
    have hlocal_nonneg :
        0 ≤ maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a := by
      have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
      exact maxDescendantBMatrixNormAtScale_nonneg U (by rw [hUscale]; omega) a
    have hlocal_le :
        coarseBMatrixNorm R a ≤ maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a :=
      coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale_of_mem_descendantsAtScale a hRU
    have hsqrt_le_T :
        Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a)
            (1 / 2 : ℝ) ≤ T := by
      dsimp [T, D]
      exact Finset.single_le_sum
        (s := descendantsAtScale Q 0)
        (f := fun V : TriadicCube d =>
          Real.rpow (maxDescendantBMatrixNormAtScale V (-(j : ℤ)) a) (1 / 2 : ℝ))
        (fun V hV => by
          have hVscale : V.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hV
          exact Real.rpow_nonneg
            (maxDescendantBMatrixNormAtScale_nonneg V (by rw [hVscale]; omega) a) _)
        (by simpa [Q] using hU)
    calc
      coarseBMatrixNorm R a ≤ maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a := hlocal_le
      _ = (Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a)
            (1 / 2 : ℝ)) ^ 2 := by
            symm
            exact Homogenization.sq_rpow_half_eq_self_of_nonneg hlocal_nonneg
      _ ≤ T ^ 2 := pow_le_pow_left₀
            (Real.rpow_nonneg hlocal_nonneg _) hsqrt_le_T 2
  have hglobal_nonneg :
      0 ≤ maxDescendantBMatrixNormAtScale Q (-(j : ℤ)) a := by
    exact maxDescendantBMatrixNormAtScale_nonneg Q (by dsimp [Q, originCube]; omega) a
  have hsqrt_le :
      Real.sqrt (maxDescendantBMatrixNormAtScale Q (-(j : ℤ)) a) ≤
        Real.sqrt (T ^ 2) :=
    Real.sqrt_le_sqrt hglobal_le_sq
  rw [Real.sqrt_sq hT_nonneg] at hsqrt_le
  simpa [Q, D, T, Real.sqrt_eq_rpow] using hsqrt_le

/--
At a fixed small depth, the lower inverse square-root maximum below `cu_m` is
bounded by summing the corresponding local maxima over the scale-zero
descendants of `cu_m`.
-/
theorem rpow_half_maxDescendantSigmaStarInvMatrixNormAtScale_originCube_neg_nat_le_sum_scale_zero
    {d : ℕ} [NeZero d] (m j : ℕ) (a : TriadicCoeffFamily d) :
    Real.rpow
        (maxDescendantSigmaStarInvMatrixNormAtScale
          (originCube d (m : ℤ)) (-(j : ℤ)) a)
        (1 / 2 : ℝ) ≤
      ∑ U ∈ descendantsAtScale (originCube d (m : ℤ)) 0,
        Real.rpow
          (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  let T : ℝ :=
    ∑ U ∈ D,
      Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
        (1 / 2 : ℝ)
  have hT_nonneg : 0 ≤ T := by
    refine Finset.sum_nonneg ?_
    intro U hU
    have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
    exact Real.rpow_nonneg
      (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg U (by rw [hUscale]; omega) a) _
  have hglobal_le_sq :
      maxDescendantSigmaStarInvMatrixNormAtScale Q (-(j : ℤ)) a ≤ T ^ 2 := by
    unfold maxDescendantSigmaStarInvMatrixNormAtScale finsetSupReal
    have hne :
        ((fun R => coarseSigmaStarInvMatrixNorm R a) ''
          (↑(descendantsAtScale Q (-(j : ℤ))) : Set (TriadicCube d))).Nonempty := by
      have hjQ : -(j : ℤ) ≤ Q.scale := by
        dsimp [Q, originCube]
        omega
      rcases descendantsAtScale_nonempty Q hjQ with ⟨R, hR⟩
      exact ⟨coarseSigmaStarInvMatrixNorm R a, ⟨R, hR, rfl⟩⟩
    refine csSup_le hne ?_
    rintro x ⟨R, hR, rfl⟩
    rcases
      smallTail_exists_scale_zero_ancestor_of_mem_descendantsAtScale_originCube_neg_nat
        (m := m) (j := j) (R := R) (by simpa [Q] using hR) with
      ⟨U, hU, hRU⟩
    have hlocal_nonneg :
        0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a := by
      have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
      exact maxDescendantSigmaStarInvMatrixNormAtScale_nonneg U
        (by rw [hUscale]; omega) a
    have hlocal_le :
        coarseSigmaStarInvMatrixNorm R a ≤
          maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a :=
      coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale_of_mem_descendantsAtScale
        a hRU
    have hsqrt_le_T :
        Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
            (1 / 2 : ℝ) ≤ T := by
      dsimp [T, D]
      exact Finset.single_le_sum
        (s := descendantsAtScale Q 0)
        (f := fun V : TriadicCube d =>
          Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale V (-(j : ℤ)) a)
            (1 / 2 : ℝ))
        (fun V hV => by
          have hVscale : V.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hV
          exact Real.rpow_nonneg
            (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg V
              (by rw [hVscale]; omega) a) _)
        (by simpa [Q] using hU)
    calc
      coarseSigmaStarInvMatrixNorm R a ≤
          maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a := hlocal_le
      _ =
          (Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
            (1 / 2 : ℝ)) ^ 2 := by
            symm
            exact Homogenization.sq_rpow_half_eq_self_of_nonneg hlocal_nonneg
      _ ≤ T ^ 2 := pow_le_pow_left₀
            (Real.rpow_nonneg hlocal_nonneg _) hsqrt_le_T 2
  have hglobal_nonneg :
      0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale Q (-(j : ℤ)) a := by
    exact maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (by dsimp [Q, originCube]; omega) a
  have hsqrt_le :
      Real.sqrt (maxDescendantSigmaStarInvMatrixNormAtScale Q (-(j : ℤ)) a) ≤
        Real.sqrt (T ^ 2) :=
    Real.sqrt_le_sqrt hglobal_le_sq
  rw [Real.sqrt_sq hT_nonneg] at hsqrt_le
  simpa [Q, D, T, Real.sqrt_eq_rpow] using hsqrt_le

/--
At a fixed small depth, the upper square-root maximum below `cu_m` is bounded
by the scale-zero supremum of the corresponding local maxima.
-/
theorem rpow_half_maxDescendantBMatrixNormAtScale_originCube_neg_nat_le_sup_scale_zero
    {d : ℕ} [NeZero d] (m j : ℕ) (a : TriadicCoeffFamily d) :
    Real.rpow
        (maxDescendantBMatrixNormAtScale (originCube d (m : ℤ)) (-(j : ℤ)) a)
        (1 / 2 : ℝ) ≤
      (descendantsAtScale (originCube d (m : ℤ)) 0).sup'
        (descendantsAtScale_nonempty (originCube d (m : ℤ))
          (by simp [originCube]))
        (fun U =>
          Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a)
            (1 / 2 : ℝ)) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  have hQ0 : (0 : ℤ) ≤ Q.scale := by
    dsimp [Q, originCube]
    exact_mod_cast Nat.zero_le m
  let T : ℝ :=
    D.sup' (descendantsAtScale_nonempty Q hQ0)
      (fun U =>
        Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a) (1 / 2 : ℝ))
  have hT_nonneg : 0 ≤ T := by
    rcases descendantsAtScale_nonempty Q hQ0 with ⟨U, hU⟩
    have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
    exact (Real.rpow_nonneg
      (maxDescendantBMatrixNormAtScale_nonneg U (by rw [hUscale]; omega) a) _).trans
        (Finset.le_sup'
          (f := fun U =>
            Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a) (1 / 2 : ℝ))
          hU)
  have hglobal_le_sq :
      maxDescendantBMatrixNormAtScale Q (-(j : ℤ)) a ≤ T ^ 2 := by
    unfold maxDescendantBMatrixNormAtScale finsetSupReal
    have hne :
        ((fun R => coarseBMatrixNorm R a) ''
          (↑(descendantsAtScale Q (-(j : ℤ))) : Set (TriadicCube d))).Nonempty := by
      have hjQ : -(j : ℤ) ≤ Q.scale := by
        dsimp [Q, originCube]
        omega
      rcases descendantsAtScale_nonempty Q hjQ with ⟨R, hR⟩
      exact ⟨coarseBMatrixNorm R a, ⟨R, hR, rfl⟩⟩
    refine csSup_le hne ?_
    rintro x ⟨R, hR, rfl⟩
    rcases
      smallTail_exists_scale_zero_ancestor_of_mem_descendantsAtScale_originCube_neg_nat
        (m := m) (j := j) (R := R) (by simpa [Q] using hR) with
      ⟨U, hU, hRU⟩
    have hlocal_nonneg :
        0 ≤ maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a := by
      have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
      exact maxDescendantBMatrixNormAtScale_nonneg U (by rw [hUscale]; omega) a
    have hlocal_le :
        coarseBMatrixNorm R a ≤ maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a :=
      coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale_of_mem_descendantsAtScale a hRU
    have hsqrt_le_T :
        Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a)
            (1 / 2 : ℝ) ≤ T := by
      dsimp [T, D]
      exact Finset.le_sup'
        (f := fun V : TriadicCube d =>
          Real.rpow (maxDescendantBMatrixNormAtScale V (-(j : ℤ)) a) (1 / 2 : ℝ))
        (by simpa [Q] using hU)
    calc
      coarseBMatrixNorm R a ≤ maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a := hlocal_le
      _ = (Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a)
            (1 / 2 : ℝ)) ^ 2 := by
            symm
            exact Homogenization.sq_rpow_half_eq_self_of_nonneg hlocal_nonneg
      _ ≤ T ^ 2 := pow_le_pow_left₀
            (Real.rpow_nonneg hlocal_nonneg _) hsqrt_le_T 2
  have hsqrt_le :
      Real.sqrt (maxDescendantBMatrixNormAtScale Q (-(j : ℤ)) a) ≤
        Real.sqrt (T ^ 2) :=
    Real.sqrt_le_sqrt hglobal_le_sq
  rw [Real.sqrt_sq hT_nonneg] at hsqrt_le
  simpa [Q, D, T, Real.sqrt_eq_rpow] using hsqrt_le

/--
At a fixed small depth, the lower inverse square-root maximum below `cu_m` is
bounded by the scale-zero supremum of the corresponding local maxima.
-/
theorem rpow_half_maxDescendantSigmaStarInvMatrixNormAtScale_originCube_neg_nat_le_sup_scale_zero
    {d : ℕ} [NeZero d] (m j : ℕ) (a : TriadicCoeffFamily d) :
    Real.rpow
        (maxDescendantSigmaStarInvMatrixNormAtScale
          (originCube d (m : ℤ)) (-(j : ℤ)) a)
        (1 / 2 : ℝ) ≤
      (descendantsAtScale (originCube d (m : ℤ)) 0).sup'
        (descendantsAtScale_nonempty (originCube d (m : ℤ))
          (by simp [originCube]))
        (fun U =>
          Real.rpow
            (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
            (1 / 2 : ℝ)) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  have hQ0 : (0 : ℤ) ≤ Q.scale := by
    dsimp [Q, originCube]
    exact_mod_cast Nat.zero_le m
  let T : ℝ :=
    D.sup' (descendantsAtScale_nonempty Q hQ0)
      (fun U =>
        Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ))
  have hT_nonneg : 0 ≤ T := by
    rcases descendantsAtScale_nonempty Q hQ0 with ⟨U, hU⟩
    have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
    exact (Real.rpow_nonneg
      (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg U (by rw [hUscale]; omega) a)
      _).trans
        (Finset.le_sup'
          (f := fun U =>
            Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
              (1 / 2 : ℝ))
          hU)
  have hglobal_le_sq :
      maxDescendantSigmaStarInvMatrixNormAtScale Q (-(j : ℤ)) a ≤ T ^ 2 := by
    unfold maxDescendantSigmaStarInvMatrixNormAtScale finsetSupReal
    have hne :
        ((fun R => coarseSigmaStarInvMatrixNorm R a) ''
          (↑(descendantsAtScale Q (-(j : ℤ))) : Set (TriadicCube d))).Nonempty := by
      have hjQ : -(j : ℤ) ≤ Q.scale := by
        dsimp [Q, originCube]
        omega
      rcases descendantsAtScale_nonempty Q hjQ with ⟨R, hR⟩
      exact ⟨coarseSigmaStarInvMatrixNorm R a, ⟨R, hR, rfl⟩⟩
    refine csSup_le hne ?_
    rintro x ⟨R, hR, rfl⟩
    rcases
      smallTail_exists_scale_zero_ancestor_of_mem_descendantsAtScale_originCube_neg_nat
        (m := m) (j := j) (R := R) (by simpa [Q] using hR) with
      ⟨U, hU, hRU⟩
    have hlocal_nonneg :
        0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a := by
      have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
      exact maxDescendantSigmaStarInvMatrixNormAtScale_nonneg U
        (by rw [hUscale]; omega) a
    have hlocal_le :
        coarseSigmaStarInvMatrixNorm R a ≤
          maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a :=
      coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale_of_mem_descendantsAtScale
        a hRU
    have hsqrt_le_T :
        Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
            (1 / 2 : ℝ) ≤ T := by
      dsimp [T, D]
      exact Finset.le_sup'
        (f := fun V : TriadicCube d =>
          Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale V (-(j : ℤ)) a)
            (1 / 2 : ℝ))
        (by simpa [Q] using hU)
    calc
      coarseSigmaStarInvMatrixNorm R a ≤
          maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a := hlocal_le
      _ =
          (Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
            (1 / 2 : ℝ)) ^ 2 := by
            symm
            exact Homogenization.sq_rpow_half_eq_self_of_nonneg hlocal_nonneg
      _ ≤ T ^ 2 := pow_le_pow_left₀
            (Real.rpow_nonneg hlocal_nonneg _) hsqrt_le_T 2
  have hsqrt_le :
      Real.sqrt (maxDescendantSigmaStarInvMatrixNormAtScale Q (-(j : ℤ)) a) ≤
        Real.sqrt (T ^ 2) :=
    Real.sqrt_le_sqrt hglobal_le_sq
  rw [Real.sqrt_sq hT_nonneg] at hsqrt_le
  simpa [Q, D, T, Real.sqrt_eq_rpow] using hsqrt_le

theorem smallTail_scale_zero_weighted_B_sqrt_le_LambdaSq_rpow_half
    {d : ℕ} [NeZero d] {U : TriadicCube d} (hUscale : U.scale = 0)
    {s : ℝ} (hs : 0 < s) (j : ℕ) (a : TriadicCoeffFamily d) :
    geometricWeight s 1 j *
        Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ) ≤
      Real.rpow (LambdaSq U s (.finite 1) a) (1 / 2 : ℝ) := by
  let F : ℕ → ℝ := fun n =>
    geometricWeight s 1 (n + 0) *
      Real.rpow (maxDescendantBMatrixNormAtScale U (-(n : ℤ)) a)
        (1 / 2 : ℝ)
  have hsum : Summable F := by
    simpa [F] using summable_upperSmallSqrtTail_scale_zero hUscale 0 hs a
  have hnonneg : ∀ n : ℕ, 0 ≤ F n := by
    intro n
    exact mul_nonneg
      (geometricWeight_nonneg _ (by simpa using hs.le))
      (Real.rpow_nonneg
        (maxDescendantBMatrixNormAtScale_nonneg U (by rw [hUscale]; omega) a) _)
  have hsingle : F j ≤ ∑' n : ℕ, F n := by
    simpa [F] using hsum.sum_le_tsum ({j} : Finset ℕ) (fun n _hn => hnonneg n)
  calc
    geometricWeight s 1 j *
        Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ) = F j := by simp [F]
    _ ≤ ∑' n : ℕ, F n := hsingle
    _ = Real.rpow (LambdaSq U s (.finite 1) a) (1 / 2 : ℝ) := by
          simpa [F] using
            smallTail_tsum_weighted_scale_zero_B_sqrt_tail_eq_LambdaSq_rpow_half
              (U := U) hUscale s 0 a hs.le

theorem smallTail_scale_zero_weighted_sigmaStarInv_sqrt_le_lambdaSq_rpow_neg_half
    {d : ℕ} [NeZero d] {U : TriadicCube d} (hUscale : U.scale = 0)
    {s : ℝ} (hs : 0 < s) (j : ℕ) (a : TriadicCoeffFamily d) :
    geometricWeight s 1 j *
        Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ) ≤
      Real.rpow (lambdaSq U s (.finite 1) a) (-1 / 2 : ℝ) := by
  let F : ℕ → ℝ := fun n =>
    geometricWeight s 1 (n + 0) *
      Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(n : ℤ)) a)
        (1 / 2 : ℝ)
  have hsum : Summable F := by
    simpa [F] using summable_lowerSmallSqrtTail_scale_zero hUscale 0 hs a
  have hnonneg : ∀ n : ℕ, 0 ≤ F n := by
    intro n
    exact mul_nonneg
      (geometricWeight_nonneg _ (by simpa using hs.le))
      (Real.rpow_nonneg
        (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg U
          (by rw [hUscale]; omega) a) _)
  have hsingle : F j ≤ ∑' n : ℕ, F n := by
    simpa [F] using hsum.sum_le_tsum ({j} : Finset ℕ) (fun n _hn => hnonneg n)
  calc
    geometricWeight s 1 j *
        Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
          (1 / 2 : ℝ) = F j := by simp [F]
    _ ≤ ∑' n : ℕ, F n := hsingle
    _ = Real.rpow (lambdaSq U s (.finite 1) a) (-1 / 2 : ℝ) := by
          simpa [F] using
            smallTail_tsum_weighted_scale_zero_sigmaStarInv_sqrt_tail_eq_lambdaSq_rpow_neg_half
              (U := U) hUscale s 0 a hs.le

/--
Fixed-scale upper small-tail localization with no scale-zero cardinality loss:
the weighted operator-norm square-root term below `cu_m` is controlled by the
scale-zero supremum of `LambdaSq`.
-/
theorem upperSmallSqrtTailTerm_le_scale_factor_mul_scale_zero_LambdaSq_sup'_rpow_half
    {d : ℕ} [NeZero d] (m j : ℕ) {s : ℝ} (hs : 0 < s)
    (a : TriadicCoeffFamily d) :
    geometricWeight s 1 (j + m) *
        Real.rpow
          (maxDescendantBMatrixNormAtScale (originCube d (m : ℤ)) (-(j : ℤ)) a)
          (1 / 2 : ℝ) ≤
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        Real.rpow
          ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
            (descendantsAtScale_nonempty (originCube d (m : ℤ))
              (by simp [originCube]))
            (fun U => LambdaSq U s (.finite 1) a))
          (1 / 2 : ℝ) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  have hQ0 : (0 : ℤ) ≤ Q.scale := by
    dsimp [Q, originCube]
    exact_mod_cast Nat.zero_le m
  let hD : D.Nonempty := descendantsAtScale_nonempty Q hQ0
  let localRoot : TriadicCube d → ℝ := fun U =>
    Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a) (1 / 2 : ℝ)
  let rootUpper : TriadicCube d → ℝ := fun U =>
    Real.rpow (LambdaSq U s (.finite 1) a) (1 / 2 : ℝ)
  have hglobal :
      Real.rpow (maxDescendantBMatrixNormAtScale Q (-(j : ℤ)) a) (1 / 2 : ℝ) ≤
        D.sup' hD localRoot := by
    simpa [Q, D, hD, localRoot] using
      rpow_half_maxDescendantBMatrixNormAtScale_originCube_neg_nat_le_sup_scale_zero
        (d := d) m j a
  have hwjm_nonneg : 0 ≤ geometricWeight s 1 (j + m) :=
    geometricWeight_nonneg _ (by simpa using hs.le)
  have hwj_pos : 0 < geometricWeight s 1 j :=
    Homogenization.geometricWeight_pos j (by simpa using hs)
  have hlocal_le : D.sup' hD (fun U => geometricWeight s 1 j * localRoot U) ≤
      D.sup' hD rootUpper := by
    refine Finset.sup'_le hD _ ?_
    intro U hU
    have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
    exact (smallTail_scale_zero_weighted_B_sqrt_le_LambdaSq_rpow_half
      (U := U) hUscale hs j a).trans (Finset.le_sup' (f := rootUpper) hU)
  have hroot_sup_le :
      D.sup' hD rootUpper ≤
        Real.rpow (D.sup' hD (fun U => LambdaSq U s (.finite 1) a)) (1 / 2 : ℝ) := by
    refine Finset.sup'_le hD _ ?_
    intro U hU
    exact Real.rpow_le_rpow
      (LambdaSq_finite_nonneg U a hs (by norm_num : (1 : ℝ) ≤ 1))
      (Finset.le_sup' (f := fun V => LambdaSq V s (.finite 1) a) hU)
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
  calc
    geometricWeight s 1 (j + m) *
        Real.rpow (maxDescendantBMatrixNormAtScale Q (-(j : ℤ)) a) (1 / 2 : ℝ)
        ≤ geometricWeight s 1 (j + m) * (D.sup' hD localRoot) :=
          mul_le_mul_of_nonneg_left hglobal hwjm_nonneg
    _ = Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        (D.sup' hD (fun U => geometricWeight s 1 j * localRoot U)) := by
          rw [smallTail_geometricWeight_one_nat_add_eq]
          rw [show Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
              geometricWeight s 1 j * D.sup' hD localRoot =
                Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
                  (geometricWeight s 1 j * D.sup' hD localRoot) by ring]
          rw [Finset.mul₀_sup' hwj_pos.le localRoot D hD]
    _ ≤ Real.rpow (3 : ℝ) (-s * (m : ℝ)) * D.sup' hD rootUpper := by
          exact mul_le_mul_of_nonneg_left hlocal_le
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    _ ≤ Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        Real.rpow (D.sup' hD (fun U => LambdaSq U s (.finite 1) a))
          (1 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hroot_sup_le
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    _ = Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        Real.rpow
          ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
            (descendantsAtScale_nonempty (originCube d (m : ℤ))
              (by simp [originCube]))
            (fun U => LambdaSq U s (.finite 1) a))
          (1 / 2 : ℝ) := by
          simp [Q, D]

/--
Fixed-scale lower small-tail localization with no scale-zero cardinality loss:
the weighted inverse operator-norm square-root term below `cu_m` is controlled
by the scale-zero supremum of `lambdaSq⁻¹`.
-/
theorem lowerSmallSqrtTailTerm_le_scale_factor_mul_scale_zero_lambdaSq_inv_sup'_rpow_half
    {d : ℕ} [NeZero d] (m j : ℕ) {s : ℝ} (hs : 0 < s)
    (a : TriadicCoeffFamily d) :
    geometricWeight s 1 (j + m) *
        Real.rpow
          (maxDescendantSigmaStarInvMatrixNormAtScale
            (originCube d (m : ℤ)) (-(j : ℤ)) a)
          (1 / 2 : ℝ) ≤
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        Real.rpow
          ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
            (descendantsAtScale_nonempty (originCube d (m : ℤ))
              (by simp [originCube]))
            (fun U => (lambdaSq U s (.finite 1) a)⁻¹))
          (1 / 2 : ℝ) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  have hQ0 : (0 : ℤ) ≤ Q.scale := by
    dsimp [Q, originCube]
    exact_mod_cast Nat.zero_le m
  let hD : D.Nonempty := descendantsAtScale_nonempty Q hQ0
  let localRoot : TriadicCube d → ℝ := fun U =>
    Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
      (1 / 2 : ℝ)
  let rootLower : TriadicCube d → ℝ := fun U =>
    Real.rpow ((lambdaSq U s (.finite 1) a)⁻¹) (1 / 2 : ℝ)
  have hglobal :
      Real.rpow
          (maxDescendantSigmaStarInvMatrixNormAtScale Q (-(j : ℤ)) a)
          (1 / 2 : ℝ) ≤
        D.sup' hD localRoot := by
    simpa [Q, D, hD, localRoot] using
      rpow_half_maxDescendantSigmaStarInvMatrixNormAtScale_originCube_neg_nat_le_sup_scale_zero
        (d := d) m j a
  have hwjm_nonneg : 0 ≤ geometricWeight s 1 (j + m) :=
    geometricWeight_nonneg _ (by simpa using hs.le)
  have hwj_pos : 0 < geometricWeight s 1 j :=
    Homogenization.geometricWeight_pos j (by simpa using hs)
  have hlocal_le : D.sup' hD (fun U => geometricWeight s 1 j * localRoot U) ≤
      D.sup' hD rootLower := by
    refine Finset.sup'_le hD _ ?_
    intro U hU
    have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
    have hterm :=
      smallTail_scale_zero_weighted_sigmaStarInv_sqrt_le_lambdaSq_rpow_neg_half
        (U := U) hUscale hs j a
    have hroot_eq :
        Real.rpow (lambdaSq U s (.finite 1) a) (-1 / 2 : ℝ) = rootLower U := by
      dsimp [rootLower]
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg_eq_inv_rpow]
    exact (hterm.trans_eq hroot_eq).trans (Finset.le_sup' (f := rootLower) hU)
  have hroot_sup_le :
      D.sup' hD rootLower ≤
        Real.rpow (D.sup' hD (fun U => (lambdaSq U s (.finite 1) a)⁻¹))
          (1 / 2 : ℝ) := by
    refine Finset.sup'_le hD _ ?_
    intro U hU
    exact Real.rpow_le_rpow
      (inv_nonneg.mpr (lambdaSq_finite_nonneg U a hs (by norm_num : (1 : ℝ) ≤ 1)))
      (Finset.le_sup' (f := fun V => (lambdaSq V s (.finite 1) a)⁻¹) hU)
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
  calc
    geometricWeight s 1 (j + m) *
        Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale Q (-(j : ℤ)) a)
          (1 / 2 : ℝ)
        ≤ geometricWeight s 1 (j + m) * (D.sup' hD localRoot) :=
          mul_le_mul_of_nonneg_left hglobal hwjm_nonneg
    _ = Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        (D.sup' hD (fun U => geometricWeight s 1 j * localRoot U)) := by
          rw [smallTail_geometricWeight_one_nat_add_eq]
          rw [show Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
              geometricWeight s 1 j * D.sup' hD localRoot =
                Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
                  (geometricWeight s 1 j * D.sup' hD localRoot) by ring]
          rw [Finset.mul₀_sup' hwj_pos.le localRoot D hD]
    _ ≤ Real.rpow (3 : ℝ) (-s * (m : ℝ)) * D.sup' hD rootLower := by
          exact mul_le_mul_of_nonneg_left hlocal_le
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    _ ≤ Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        Real.rpow (D.sup' hD (fun U => (lambdaSq U s (.finite 1) a)⁻¹))
          (1 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hroot_sup_le
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    _ = Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        Real.rpow
          ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
            (descendantsAtScale_nonempty (originCube d (m : ℤ))
              (by simp [originCube]))
            (fun U => (lambdaSq U s (.finite 1) a)⁻¹))
          (1 / 2 : ℝ) := by
          simp [Q, D]

/--
Squared fixed-scale upper small-tail localization with no scale-zero
cardinality loss.
-/
theorem upperSmallSqrtTailTerm_sq_le_scale_factor_mul_scale_zero_LambdaSq_sup'
    {d : ℕ} [NeZero d] (m j : ℕ) {s : ℝ} (hs : 0 < s)
    (a : TriadicCoeffFamily d) :
    (geometricWeight s 1 (j + m) *
        Real.rpow
          (maxDescendantBMatrixNormAtScale (originCube d (m : ℤ)) (-(j : ℤ)) a)
          (1 / 2 : ℝ)) ^ 2 ≤
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
          (descendantsAtScale_nonempty (originCube d (m : ℤ))
            (by simp [originCube]))
          (fun U => LambdaSq U s (.finite 1) a)) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  have hQ0 : (0 : ℤ) ≤ Q.scale := by
    dsimp [Q, originCube]
    exact_mod_cast Nat.zero_le m
  let hD : D.Nonempty := descendantsAtScale_nonempty Q hQ0
  let r : ℝ := Real.rpow (3 : ℝ) (-s * (m : ℝ))
  let S : ℝ := D.sup' hD (fun U => LambdaSq U s (.finite 1) a)
  let T : ℝ :=
    geometricWeight s 1 (j + m) *
      Real.rpow (maxDescendantBMatrixNormAtScale Q (-(j : ℤ)) a) (1 / 2 : ℝ)
  have hT_nonneg : 0 ≤ T := by
    exact mul_nonneg
      (geometricWeight_nonneg _ (by simpa using hs.le))
      (Real.rpow_nonneg
        (maxDescendantBMatrixNormAtScale_nonneg Q (by dsimp [Q, originCube]; omega) a)
        _)
  have hS_nonneg : 0 ≤ S := by
    rcases hD with ⟨U, hU⟩
    exact (LambdaSq_finite_nonneg U a hs (by norm_num : (1 : ℝ) ≤ 1)).trans
      (Finset.le_sup' (s := D) (f := fun U => LambdaSq U s (.finite 1) a) hU)
  have hr_nonneg : 0 ≤ r := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hr_le_one : r ≤ 1 := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    have hexp_nonpos : -s * (m : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hm_nonneg
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1 : ℝ) ≤ 3) hexp_nonpos
  have hterm :
      T ≤ r * Real.rpow S (1 / 2 : ℝ) := by
    simpa [Q, D, hD, r, S, T] using
      upperSmallSqrtTailTerm_le_scale_factor_mul_scale_zero_LambdaSq_sup'_rpow_half
        (d := d) m j hs a
  have hsq := pow_le_pow_left₀ hT_nonneg hterm 2
  calc
    (geometricWeight s 1 (j + m) *
        Real.rpow
          (maxDescendantBMatrixNormAtScale (originCube d (m : ℤ)) (-(j : ℤ)) a)
          (1 / 2 : ℝ)) ^ 2 = T ^ 2 := by simp [T, Q]
    _ ≤ (r * Real.rpow S (1 / 2 : ℝ)) ^ 2 := hsq
    _ = r ^ 2 * S := by
          rw [mul_pow, Homogenization.sq_rpow_half_eq_self_of_nonneg hS_nonneg]
    _ ≤ r * S := by
          have hr_sq_le : r ^ 2 ≤ r := by
            calc
              r ^ 2 = r * r := by ring
              _ ≤ r * 1 := mul_le_mul_of_nonneg_left hr_le_one hr_nonneg
              _ = r := by ring
          exact mul_le_mul_of_nonneg_right hr_sq_le hS_nonneg
    _ =
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
          (descendantsAtScale_nonempty (originCube d (m : ℤ))
            (by simp [originCube]))
          (fun U => LambdaSq U s (.finite 1) a)) := by
          simp [Q, D, r, S]

/--
Squared fixed-scale lower small-tail localization with no scale-zero
cardinality loss.
-/
theorem lowerSmallSqrtTailTerm_sq_le_scale_factor_mul_scale_zero_lambdaSq_inv_sup'
    {d : ℕ} [NeZero d] (m j : ℕ) {s : ℝ} (hs : 0 < s)
    (a : TriadicCoeffFamily d) :
    (geometricWeight s 1 (j + m) *
        Real.rpow
          (maxDescendantSigmaStarInvMatrixNormAtScale
            (originCube d (m : ℤ)) (-(j : ℤ)) a)
          (1 / 2 : ℝ)) ^ 2 ≤
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
          (descendantsAtScale_nonempty (originCube d (m : ℤ))
            (by simp [originCube]))
          (fun U => (lambdaSq U s (.finite 1) a)⁻¹)) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  have hQ0 : (0 : ℤ) ≤ Q.scale := by
    dsimp [Q, originCube]
    exact_mod_cast Nat.zero_le m
  let hD : D.Nonempty := descendantsAtScale_nonempty Q hQ0
  let r : ℝ := Real.rpow (3 : ℝ) (-s * (m : ℝ))
  let S : ℝ := D.sup' hD (fun U => (lambdaSq U s (.finite 1) a)⁻¹)
  let T : ℝ :=
    geometricWeight s 1 (j + m) *
      Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale Q (-(j : ℤ)) a)
        (1 / 2 : ℝ)
  have hT_nonneg : 0 ≤ T := by
    exact mul_nonneg
      (geometricWeight_nonneg _ (by simpa using hs.le))
      (Real.rpow_nonneg
        (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
          (by dsimp [Q, originCube]; omega) a) _)
  have hS_nonneg : 0 ≤ S := by
    rcases hD with ⟨U, hU⟩
    exact (inv_nonneg.mpr
        (lambdaSq_finite_nonneg U a hs (by norm_num : (1 : ℝ) ≤ 1))).trans
      (Finset.le_sup' (s := D)
        (f := fun U => (lambdaSq U s (.finite 1) a)⁻¹) hU)
  have hr_nonneg : 0 ≤ r := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hr_le_one : r ≤ 1 := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    have hexp_nonpos : -s * (m : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hm_nonneg
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1 : ℝ) ≤ 3) hexp_nonpos
  have hterm :
      T ≤ r * Real.rpow S (1 / 2 : ℝ) := by
    simpa [Q, D, hD, r, S, T] using
      lowerSmallSqrtTailTerm_le_scale_factor_mul_scale_zero_lambdaSq_inv_sup'_rpow_half
        (d := d) m j hs a
  have hsq := pow_le_pow_left₀ hT_nonneg hterm 2
  calc
    (geometricWeight s 1 (j + m) *
        Real.rpow
          (maxDescendantSigmaStarInvMatrixNormAtScale
            (originCube d (m : ℤ)) (-(j : ℤ)) a)
          (1 / 2 : ℝ)) ^ 2 = T ^ 2 := by simp [T, Q]
    _ ≤ (r * Real.rpow S (1 / 2 : ℝ)) ^ 2 := hsq
    _ = r ^ 2 * S := by
          rw [mul_pow, Homogenization.sq_rpow_half_eq_self_of_nonneg hS_nonneg]
    _ ≤ r * S := by
          have hr_sq_le : r ^ 2 ≤ r := by
            calc
              r ^ 2 = r * r := by ring
              _ ≤ r * 1 := mul_le_mul_of_nonneg_left hr_le_one hr_nonneg
              _ = r := by ring
          exact mul_le_mul_of_nonneg_right hr_sq_le hS_nonneg
    _ =
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
          (descendantsAtScale_nonempty (originCube d (m : ℤ))
            (by simp [originCube]))
          (fun U => (lambdaSq U s (.finite 1) a)⁻¹)) := by
          simp [Q, D, r, S]

/--
The upper small-scale square-root tail is bounded by the sum of the local
scale-zero q = 1 square-root tails, hence by the corresponding scale-zero
ellipticity square roots with the global factor `3^{-sm}`.
-/
theorem upperSmallSqrtTail_le_scale_factor_mul_sum_scale_zero_LambdaSq_rpow_half
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s)
    (a : TriadicCoeffFamily d) :
    upperSmallSqrtTail (d := d) m s a ≤
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        ∑ U ∈ descendantsAtScale (originCube d (m : ℤ)) 0,
          Real.rpow (LambdaSq U s (.finite 1) a) (1 / 2 : ℝ) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  let f : ℕ → ℝ := fun j =>
    geometricWeight s 1 (j + m) *
      Real.rpow (maxDescendantBMatrixNormAtScale Q (-(j : ℤ)) a) (1 / 2 : ℝ)
  let g : TriadicCube d → ℕ → ℝ := fun U j =>
    geometricWeight s 1 (j + m) *
      Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a) (1 / 2 : ℝ)
  have hgSummable : Summable (fun j : ℕ => ∑ U ∈ D, g U j) := by
    exact summable_sum (s := D) (fun U hU => by
      have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
      simpa [g, D, Q] using summable_upperSmallSqrtTail_scale_zero hUscale m hs a)
  have hterm : ∀ j : ℕ, f j ≤ ∑ U ∈ D, g U j := by
    intro j
    have hw_nonneg : 0 ≤ geometricWeight s 1 (j + m) :=
      geometricWeight_nonneg _ (by simpa using hs.le)
    have hsqrt :=
      rpow_half_maxDescendantBMatrixNormAtScale_originCube_neg_nat_le_sum_scale_zero
        (d := d) m j a
    calc
      f j ≤
          geometricWeight s 1 (j + m) *
            (∑ U ∈ D,
              Real.rpow (maxDescendantBMatrixNormAtScale U (-(j : ℤ)) a)
                (1 / 2 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left (by simpa [Q, D] using hsqrt) hw_nonneg
      _ = ∑ U ∈ D, g U j := by
            simp [g, Finset.mul_sum]
  have hf_nonneg : ∀ j : ℕ, 0 ≤ f j := by
    intro j
    exact mul_nonneg
      (geometricWeight_nonneg _ (by simpa using hs.le))
      (Real.rpow_nonneg
        (maxDescendantBMatrixNormAtScale_nonneg Q (by dsimp [Q, originCube]; omega) a) _)
  have hfSummable : Summable f :=
    Summable.of_nonneg_of_le hf_nonneg hterm hgSummable
  calc
    upperSmallSqrtTail (d := d) m s a = ∑' j : ℕ, f j := by
      simp [upperSmallSqrtTail, f, Q]
    _ ≤ ∑' j : ℕ, ∑ U ∈ D, g U j :=
      Summable.tsum_le_tsum hterm hfSummable hgSummable
    _ = ∑ U ∈ D, ∑' j : ℕ, g U j :=
      Summable.tsum_finsetSum (s := D) (fun U hU => by
        have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
        simpa [g, D, Q] using summable_upperSmallSqrtTail_scale_zero hUscale m hs a)
    _ =
        ∑ U ∈ D,
          Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
            Real.rpow (LambdaSq U s (.finite 1) a) (1 / 2 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro U hU
          have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
          simpa [g] using
            smallTail_tsum_weighted_scale_zero_B_sqrt_tail_eq_LambdaSq_rpow_half
              (U := U) hUscale s m a hs.le
    _ =
        Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
          ∑ U ∈ descendantsAtScale (originCube d (m : ℤ)) 0,
            Real.rpow (LambdaSq U s (.finite 1) a) (1 / 2 : ℝ) := by
          simp [D, Q, Finset.mul_sum]

/--
The lower inverse small-scale square-root tail is bounded by the sum of the
local scale-zero q = 1 inverse square-root tails, hence by the corresponding
scale-zero inverse ellipticity square roots with the global factor `3^{-sm}`.
-/
theorem lowerSmallSqrtTail_le_scale_factor_mul_sum_scale_zero_lambdaSq_rpow_neg_half
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s)
    (a : TriadicCoeffFamily d) :
    lowerSmallSqrtTail (d := d) m s a ≤
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
        ∑ U ∈ descendantsAtScale (originCube d (m : ℤ)) 0,
          Real.rpow (lambdaSq U s (.finite 1) a) (-1 / 2 : ℝ) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let D : Finset (TriadicCube d) := descendantsAtScale Q 0
  let f : ℕ → ℝ := fun j =>
    geometricWeight s 1 (j + m) *
      Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale Q (-(j : ℤ)) a)
        (1 / 2 : ℝ)
  let g : TriadicCube d → ℕ → ℝ := fun U j =>
    geometricWeight s 1 (j + m) *
      Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
        (1 / 2 : ℝ)
  have hgSummable : Summable (fun j : ℕ => ∑ U ∈ D, g U j) := by
    exact summable_sum (s := D) (fun U hU => by
      have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
      simpa [g, D, Q] using summable_lowerSmallSqrtTail_scale_zero hUscale m hs a)
  have hterm : ∀ j : ℕ, f j ≤ ∑ U ∈ D, g U j := by
    intro j
    have hw_nonneg : 0 ≤ geometricWeight s 1 (j + m) :=
      geometricWeight_nonneg _ (by simpa using hs.le)
    have hsqrt :=
      rpow_half_maxDescendantSigmaStarInvMatrixNormAtScale_originCube_neg_nat_le_sum_scale_zero
        (d := d) m j a
    calc
      f j ≤
          geometricWeight s 1 (j + m) *
            (∑ U ∈ D,
              Real.rpow (maxDescendantSigmaStarInvMatrixNormAtScale U (-(j : ℤ)) a)
                (1 / 2 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left (by simpa [Q, D] using hsqrt) hw_nonneg
      _ = ∑ U ∈ D, g U j := by
            simp [g, Finset.mul_sum]
  have hf_nonneg : ∀ j : ℕ, 0 ≤ f j := by
    intro j
    exact mul_nonneg
      (geometricWeight_nonneg _ (by simpa using hs.le))
      (Real.rpow_nonneg
        (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
          (by dsimp [Q, originCube]; omega) a) _)
  have hfSummable : Summable f :=
    Summable.of_nonneg_of_le hf_nonneg hterm hgSummable
  calc
    lowerSmallSqrtTail (d := d) m s a = ∑' j : ℕ, f j := by
      simp [lowerSmallSqrtTail, f, Q]
    _ ≤ ∑' j : ℕ, ∑ U ∈ D, g U j :=
      Summable.tsum_le_tsum hterm hfSummable hgSummable
    _ = ∑ U ∈ D, ∑' j : ℕ, g U j :=
      Summable.tsum_finsetSum (s := D) (fun U hU => by
        have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
        simpa [g, D, Q] using summable_lowerSmallSqrtTail_scale_zero hUscale m hs a)
    _ =
        ∑ U ∈ D,
          Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
            Real.rpow (lambdaSq U s (.finite 1) a) (-1 / 2 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro U hU
          have hUscale : U.scale = 0 := descendant_scale_eq_of_mem_descendantsAtScale hU
          simpa [g] using
            smallTail_tsum_weighted_scale_zero_sigmaStarInv_sqrt_tail_eq_lambdaSq_rpow_neg_half
              (U := U) hUscale s m a hs.le
    _ =
        Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
          ∑ U ∈ descendantsAtScale (originCube d (m : ℤ)) 0,
            Real.rpow (lambdaSq U s (.finite 1) a) (-1 / 2 : ℝ) := by
          simp [D, Q, Finset.mul_sum]

/-- Squared upper small-tail bound using scale-zero `LambdaSq` values. -/
theorem upperSmallSqrtTail_sq_le_scale_factor_sq_mul_card_sum_scale_zero_LambdaSq
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s)
    (a : TriadicCoeffFamily d) :
    upperSmallSqrtTail (d := d) m s a ^ 2 ≤
      (Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 *
          ((descendantsAtScale (originCube d (m : ℤ)) 0).card : ℝ)) *
        ∑ U ∈ descendantsAtScale (originCube d (m : ℤ)) 0,
          LambdaSq U s (.finite 1) a := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtScale (originCube d (m : ℤ)) 0
  let r : ℝ := Real.rpow (3 : ℝ) (-s * (m : ℝ))
  let sqrtUpper : TriadicCube d → ℝ := fun U =>
    Real.rpow (LambdaSq U s (.finite 1) a) (1 / 2 : ℝ)
  have htail_nonneg :
      0 ≤ upperSmallSqrtTail (d := d) m s a := by
    unfold upperSmallSqrtTail
    refine tsum_nonneg ?_
    intro j
    exact mul_nonneg
      (geometricWeight_nonneg _ (by simpa using hs.le))
      (Real.rpow_nonneg
        (maxDescendantBMatrixNormAtScale_nonneg (originCube d (m : ℤ))
          (by simp [originCube]) a) _)
  have htail_le :
      upperSmallSqrtTail (d := d) m s a ≤
        r * ∑ U ∈ D, sqrtUpper U := by
    simpa [D, r, sqrtUpper] using
      upperSmallSqrtTail_le_scale_factor_mul_sum_scale_zero_LambdaSq_rpow_half
        (d := d) m hs a
  have hsq_tail := pow_le_pow_left₀ htail_nonneg htail_le 2
  have hsum_sq :
      (∑ U ∈ D, sqrtUpper U) ^ 2 ≤
        (D.card : ℝ) * ∑ U ∈ D, LambdaSq U s (.finite 1) a := by
    have hcs :
        (∑ U ∈ D, sqrtUpper U) ^ 2 ≤
          (D.card : ℝ) * ∑ U ∈ D, sqrtUpper U ^ 2 :=
      sq_sum_le_card_mul_sum_sq (s := D) (f := sqrtUpper)
    have hsquares :
        (∑ U ∈ D, sqrtUpper U ^ 2) =
          ∑ U ∈ D, LambdaSq U s (.finite 1) a := by
      refine Finset.sum_congr rfl ?_
      intro U _hU
      exact Homogenization.sq_rpow_half_eq_self_of_nonneg
        (LambdaSq_finite_nonneg U a hs (by norm_num : (1 : ℝ) ≤ 1))
    simpa [hsquares] using hcs
  calc
    upperSmallSqrtTail (d := d) m s a ^ 2
        ≤ (r * ∑ U ∈ D, sqrtUpper U) ^ 2 := hsq_tail
    _ = r ^ 2 * (∑ U ∈ D, sqrtUpper U) ^ 2 := by ring
    _ ≤ r ^ 2 * ((D.card : ℝ) * ∑ U ∈ D, LambdaSq U s (.finite 1) a) := by
          exact mul_le_mul_of_nonneg_left hsum_sq (sq_nonneg r)
    _ =
        (Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 *
            ((descendantsAtScale (originCube d (m : ℤ)) 0).card : ℝ)) *
          ∑ U ∈ descendantsAtScale (originCube d (m : ℤ)) 0,
            LambdaSq U s (.finite 1) a := by
          simp [D, r]
          ring

/-- Squared lower inverse small-tail bound using scale-zero `lambdaSq` values. -/
theorem lowerSmallSqrtTail_sq_le_scale_factor_sq_mul_card_sum_scale_zero_lambdaSq_inv
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s)
    (a : TriadicCoeffFamily d) :
    lowerSmallSqrtTail (d := d) m s a ^ 2 ≤
      (Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 *
          ((descendantsAtScale (originCube d (m : ℤ)) 0).card : ℝ)) *
        ∑ U ∈ descendantsAtScale (originCube d (m : ℤ)) 0,
          (lambdaSq U s (.finite 1) a)⁻¹ := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtScale (originCube d (m : ℤ)) 0
  let r : ℝ := Real.rpow (3 : ℝ) (-s * (m : ℝ))
  let sqrtLower : TriadicCube d → ℝ := fun U =>
    Real.rpow (lambdaSq U s (.finite 1) a) (-1 / 2 : ℝ)
  have htail_nonneg :
      0 ≤ lowerSmallSqrtTail (d := d) m s a := by
    unfold lowerSmallSqrtTail
    refine tsum_nonneg ?_
    intro j
    exact mul_nonneg
      (geometricWeight_nonneg _ (by simpa using hs.le))
      (Real.rpow_nonneg
        (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg (originCube d (m : ℤ))
          (by simp [originCube]) a) _)
  have htail_le :
      lowerSmallSqrtTail (d := d) m s a ≤
        r * ∑ U ∈ D, sqrtLower U := by
    simpa [D, r, sqrtLower] using
      lowerSmallSqrtTail_le_scale_factor_mul_sum_scale_zero_lambdaSq_rpow_neg_half
        (d := d) m hs a
  have hsq_tail := pow_le_pow_left₀ htail_nonneg htail_le 2
  have hsum_sq :
      (∑ U ∈ D, sqrtLower U) ^ 2 ≤
        (D.card : ℝ) * ∑ U ∈ D, (lambdaSq U s (.finite 1) a)⁻¹ := by
    have hcs :
        (∑ U ∈ D, sqrtLower U) ^ 2 ≤
          (D.card : ℝ) * ∑ U ∈ D, sqrtLower U ^ 2 :=
      sq_sum_le_card_mul_sum_sq (s := D) (f := sqrtLower)
    have hsquares :
        (∑ U ∈ D, sqrtLower U ^ 2) =
          ∑ U ∈ D, (lambdaSq U s (.finite 1) a)⁻¹ := by
      refine Finset.sum_congr rfl ?_
      intro U _hU
      exact Homogenization.sq_rpow_neg_half_eq_inv_of_nonneg
        (lambdaSq_finite_nonneg U a hs (by norm_num : (1 : ℝ) ≤ 1))
    simpa [hsquares] using hcs
  calc
    lowerSmallSqrtTail (d := d) m s a ^ 2
        ≤ (r * ∑ U ∈ D, sqrtLower U) ^ 2 := hsq_tail
    _ = r ^ 2 * (∑ U ∈ D, sqrtLower U) ^ 2 := by ring
    _ ≤ r ^ 2 * ((D.card : ℝ) * ∑ U ∈ D, (lambdaSq U s (.finite 1) a)⁻¹) := by
          exact mul_le_mul_of_nonneg_left hsum_sq (sq_nonneg r)
    _ =
        (Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 *
            ((descendantsAtScale (originCube d (m : ℤ)) 0).card : ℝ)) *
          ∑ U ∈ descendantsAtScale (originCube d (m : ℤ)) 0,
            (lambdaSq U s (.finite 1) a)⁻¹ := by
          simp [D, r]
          ring

end

end Ch02
end Book
end Homogenization
