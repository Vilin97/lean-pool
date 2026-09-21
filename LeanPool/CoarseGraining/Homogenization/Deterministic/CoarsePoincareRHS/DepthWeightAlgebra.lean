/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.GlobalQuantities

/-! # Depth Weight Algebra -/

namespace Homogenization

noncomputable section

theorem real_le_of_forall_le_add_of_tendsto_zero {X A : ℝ} {T : ℕ → ℝ}
    (hT : Filter.Tendsto T Filter.atTop (nhds 0))
    (h : ∀ N : ℕ, X ≤ T N + A) :
    X ≤ A := by
  have hX : Filter.Tendsto (fun _ : ℕ => X) Filter.atTop (nhds X) :=
    tendsto_const_nhds
  have hTA : Filter.Tendsto (fun N : ℕ => T N + A) Filter.atTop (nhds (0 + A)) :=
    hT.add tendsto_const_nhds
  have hle : X ≤ 0 + A :=
    le_of_tendsto_of_tendsto' hX hTA h
  simpa using hle

theorem tendsto_pow_mul_of_nonneg_bddAbove
    {r : ℝ} {F : ℕ → ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (hF_nonneg : ∀ N : ℕ, 0 ≤ F N)
    (hF_bdd : BddAbove (Set.range F)) :
    Filter.Tendsto (fun N : ℕ => r ^ N * F N) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  rcases hF_bdd with ⟨B, hB⟩
  have hB_nonneg : 0 ≤ B := by
    exact (hF_nonneg 0).trans (hB ⟨0, rfl⟩)
  have hpow :
      Filter.Tendsto (fun N : ℕ => r ^ N * B) Filter.atTop (nhds 0) := by
    have habs : |r| < 1 := by
      simpa [abs_of_nonneg hr_nonneg] using hr_lt_one
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs).mul_const B
  refine squeeze_zero (fun N : ℕ => abs_nonneg _) ?_ hpow
  intro N
  have hpow_nonneg : 0 ≤ r ^ N := pow_nonneg hr_nonneg N
  have hF_le : F N ≤ B := hB ⟨N, rfl⟩
  have hprod_nonneg : 0 ≤ r ^ N * F N :=
    mul_nonneg hpow_nonneg (hF_nonneg N)
  calc
    |r ^ N * F N| = r ^ N * F N := abs_of_nonneg hprod_nonneg
    _ ≤ r ^ N * B := mul_le_mul_of_nonneg_left hF_le hpow_nonneg


theorem coarsePoincareRHSDepthWeight_succ (s : ℝ) (n : ℕ) :
    coarsePoincareRHSDepthWeight s (n + 1) =
      coarsePoincareRHSStepDiscount s * coarsePoincareRHSDepthWeight s n := by
  simpa [coarsePoincareRHSDepthWeight, coarsePoincareRHSStepDiscount] using
    rpow_neg_mul_nat_succ_eq s n


theorem coarsePoincareRHSDepthWeight_eq_rpow_mul_succ (s : ℝ) (n : ℕ) :
    coarsePoincareRHSDepthWeight s n =
      Real.rpow (3 : ℝ) s * coarsePoincareRHSDepthWeight s (n + 1) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  unfold coarsePoincareRHSDepthWeight
  calc
    Real.rpow (3 : ℝ) (-s * (n : ℝ))
        = Real.rpow (3 : ℝ) (s + (-s * ((n + 1 : ℕ) : ℝ))) := by
            congr 1
            norm_num
            ring
    _ =
        Real.rpow (3 : ℝ) s *
          Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) := by
            exact Real.rpow_add h3 s (-s * ((n + 1 : ℕ) : ℝ))

theorem coarsePoincareRHSDepthWeight_mul_theta_pow_eq_scaledStepCoeff_mul
    (s θ : ℝ) (m N : ℕ) :
    coarsePoincareRHSDepthWeight s m * θ ^ N =
      (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
        coarsePoincareRHSDepthWeight s (m + N) := by
  induction N generalizing m with
  | zero =>
      simp
  | succ N ih =>
      calc
        coarsePoincareRHSDepthWeight s m * θ ^ (N + 1)
            = (coarsePoincareRHSDepthWeight s m * θ ^ N) * θ := by
                rw [pow_succ]
                ring
        _ =
            ((coarsePoincareRHSScaledStepCoeff s θ) ^ N *
              coarsePoincareRHSDepthWeight s (m + N)) * θ := by
                rw [ih]
        _ =
            (coarsePoincareRHSScaledStepCoeff s θ) ^ N *
              (coarsePoincareRHSScaledStepCoeff s θ *
                coarsePoincareRHSDepthWeight s (m + (N + 1))) := by
                rw [← Nat.add_assoc]
                rw [coarsePoincareRHSDepthWeight_eq_rpow_mul_succ s (m + N)]
                unfold coarsePoincareRHSScaledStepCoeff
                ring
        _ =
            (coarsePoincareRHSScaledStepCoeff s θ) ^ (N + 1) *
              coarsePoincareRHSDepthWeight s (m + (N + 1)) := by
                rw [pow_succ]
                ring

theorem coarsePoincareRHSDepthWeight_mul_parentHalfCoeff_succ
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) (n : ℕ) :
    coarsePoincareRHSDepthWeight s (n + 1) *
        coarsePoincareRHSParentHalfCoeff Q a s (n + 1) =
      coarsePoincareRHSDepthWeight s n *
        coarsePoincareRHSParentHalfCoeff Q a s n := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hdepth :
      Real.rpow (3 : ℝ) (-s * ((n + 1 : ℕ) : ℝ)) =
        Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) (-s * (n : ℝ)) :=
    rpow_neg_mul_nat_succ_eq s n
  have hparent :
      Real.rpow (3 : ℝ) (s * ((n + 1 : ℕ) : ℝ)) =
        Real.rpow (3 : ℝ) s * Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
    have hexp :
        s * ((n + 1 : ℕ) : ℝ) = s + s * (n : ℝ) := by
      norm_num
      ring
    calc
      Real.rpow (3 : ℝ) (s * ((n + 1 : ℕ) : ℝ)) =
          Real.rpow (3 : ℝ) (s + s * (n : ℝ)) := by
            rw [hexp]
      _ = Real.rpow (3 : ℝ) s *
            Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
            exact Real.rpow_add h3 s (s * (n : ℝ))
  have hcombine :
      Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) s = 1 := by
    calc
      Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) s =
          Real.rpow (3 : ℝ) (-s + s) := by
            exact (Real.rpow_add h3 (-s) s).symm
      _ = 1 := by
            simp [show -s + s = (0 : ℝ) by ring]
  unfold coarsePoincareRHSDepthWeight coarsePoincareRHSParentHalfCoeff
  rw [hdepth, hparent]
  let A : ℝ := Real.rpow (3 : ℝ) (-s)
  let B : ℝ := Real.rpow (3 : ℝ) s
  let C : ℝ := Real.rpow (3 : ℝ) (-s * (n : ℝ))
  let D : ℝ := (geometricDiscount s 2)⁻¹
  let E : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ))
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  change A * C * (D * (B * E * L)) = C * (D * (E * L))
  have hAB : A * B = 1 := by simpa [A, B] using hcombine
  calc
    A * C * (D * (B * E * L)) = (A * B) * (C * (D * (E * L))) := by ring
    _ = C * (D * (E * L)) := by rw [hAB]; ring

theorem coarsePoincareRHSParentHalfCoeff_succ
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) (n : ℕ) :
    coarsePoincareRHSParentHalfCoeff Q a s (n + 1) =
      Real.rpow (3 : ℝ) s * coarsePoincareRHSParentHalfCoeff Q a s n := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hparent :
      Real.rpow (3 : ℝ) (s * ((n + 1 : ℕ) : ℝ)) =
        Real.rpow (3 : ℝ) s * Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
    have hexp :
        s * ((n + 1 : ℕ) : ℝ) = s + s * (n : ℝ) := by
      norm_num
      ring
    calc
      Real.rpow (3 : ℝ) (s * ((n + 1 : ℕ) : ℝ)) =
          Real.rpow (3 : ℝ) (s + s * (n : ℝ)) := by
            rw [hexp]
      _ = Real.rpow (3 : ℝ) s *
            Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
            exact Real.rpow_add h3 s (s * (n : ℝ))
  unfold coarsePoincareRHSParentHalfCoeff
  rw [hparent]
  ring

theorem coarsePoincareRHSIntrinsicParentHalfForceMultiplier_succ
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) (n : ℕ) :
    coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s (n + 1) =
      Real.rpow (3 : ℝ) s *
        coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s n := by
  unfold coarsePoincareRHSIntrinsicParentHalfForceMultiplier
  rw [coarsePoincareRHSParentHalfCoeff_succ Q a s n]
  ring

theorem coarsePoincareRHSGlobalForceBound_succ
    {d : ℕ} (Q : TriadicCube d) (g : Vec d → Vec d) (s : ℝ) (n : ℕ) :
    coarsePoincareRHSGlobalForceBound Q g s (n + 1) =
      Real.rpow (3 : ℝ) (-2 * s) * coarsePoincareRHSGlobalForceBound Q g s n := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  let c : ℝ := Real.rpow (3 : ℝ) s
  let b : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ))
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos h3 s
  have hb_pos : 0 < b := by
    dsimp [b]
    exact Real.rpow_pos_of_pos h3 (s * (n : ℝ))
  have hscale :
      Real.rpow (3 : ℝ) (s * ((n + 1 : ℕ) : ℝ)) = c * b := by
    dsimp [c, b]
    have hexp :
        s * ((n + 1 : ℕ) : ℝ) = s + s * (n : ℝ) := by
      norm_num
      ring
    calc
      Real.rpow (3 : ℝ) (s * ((n + 1 : ℕ) : ℝ)) =
          Real.rpow (3 : ℝ) (s + s * (n : ℝ)) := by
            rw [hexp]
      _ = Real.rpow (3 : ℝ) s * Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
            exact Real.rpow_add h3 s (s * (n : ℝ))
  have hneg :
      Real.rpow (3 : ℝ) (-2 * s) = (c ^ 2)⁻¹ := by
    dsimp [c]
    calc
      Real.rpow (3 : ℝ) (-2 * s) =
          Real.rpow (3 : ℝ) (-(2 * s)) := by
            congr 1
            ring
      _ = (Real.rpow (3 : ℝ) (2 * s))⁻¹ := by
            simpa using (Real.rpow_neg (le_of_lt h3) (2 * s))
      _ = ((Real.rpow (3 : ℝ) s) ^ 2)⁻¹ := by
            have hs2 :
                Real.rpow (3 : ℝ) (2 * s) =
                  (Real.rpow (3 : ℝ) s) ^ 2 := by
              calc
                Real.rpow (3 : ℝ) (2 * s) =
                    Real.rpow (3 : ℝ) (s + s) := by
                      congr 1
                      ring
                _ = Real.rpow (3 : ℝ) s * Real.rpow (3 : ℝ) s := by
                      exact Real.rpow_add h3 s s
                _ = (Real.rpow (3 : ℝ) s) ^ 2 := by
                      ring
            rw [hs2]
  unfold coarsePoincareRHSGlobalForceBound
  rw [hscale, hneg]
  dsimp [c, b] at hc_pos hb_pos ⊢
  field_simp [hc_pos.ne', hb_pos.ne']

theorem coarsePoincareRHSIntrinsicForceFactor_succ
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s : ℝ) (n : ℕ) :
    coarsePoincareRHSDepthWeight s (n + 1) *
        ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s (n + 1)) ^ 2 *
          coarsePoincareRHSGlobalForceBound Q g s (n + 1)) =
      Real.rpow (3 : ℝ) (-s) *
        (coarsePoincareRHSDepthWeight s n *
          ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s n) ^ 2 *
            coarsePoincareRHSGlobalForceBound Q g s n)) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hdepth :
      coarsePoincareRHSDepthWeight s (n + 1) =
        Real.rpow (3 : ℝ) (-s) * coarsePoincareRHSDepthWeight s n := by
    simpa [coarsePoincareRHSStepDiscount] using
      coarsePoincareRHSDepthWeight_succ s n
  have hmult :=
    coarsePoincareRHSIntrinsicParentHalfForceMultiplier_succ Q a s n
  have hforce :=
    coarsePoincareRHSGlobalForceBound_succ Q g s n
  have hfactor :
      Real.rpow (3 : ℝ) (-s) * (Real.rpow (3 : ℝ) s) ^ 2 *
          Real.rpow (3 : ℝ) (-2 * s) =
        Real.rpow (3 : ℝ) (-s) := by
    have hsq :
        (Real.rpow (3 : ℝ) s) ^ 2 =
          Real.rpow (3 : ℝ) (2 * s) := by
      calc
        (Real.rpow (3 : ℝ) s) ^ 2 =
            Real.rpow (3 : ℝ) s * Real.rpow (3 : ℝ) s := by
              ring
        _ = Real.rpow (3 : ℝ) (s + s) := by
              exact (Real.rpow_add h3 s s).symm
        _ = Real.rpow (3 : ℝ) (2 * s) := by
              congr 1
              ring
    have hsum1 :
        Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) (2 * s) =
          Real.rpow (3 : ℝ) (-s + 2 * s) := by
      simpa using (Real.rpow_add h3 (-s) (2 * s)).symm
    have hsum2 :
        Real.rpow (3 : ℝ) (-s + 2 * s) * Real.rpow (3 : ℝ) (-2 * s) =
          Real.rpow (3 : ℝ) ((-s + 2 * s) + -2 * s) := by
      simpa using (Real.rpow_add h3 (-s + 2 * s) (-2 * s)).symm
    calc
      Real.rpow (3 : ℝ) (-s) * (Real.rpow (3 : ℝ) s) ^ 2 *
          Real.rpow (3 : ℝ) (-2 * s) =
        Real.rpow (3 : ℝ) (-s) * Real.rpow (3 : ℝ) (2 * s) *
          Real.rpow (3 : ℝ) (-2 * s) := by
          rw [hsq]
      _ = Real.rpow (3 : ℝ) (-s + 2 * s) * Real.rpow (3 : ℝ) (-2 * s) := by
          rw [hsum1]
      _ = Real.rpow (3 : ℝ) ((-s + 2 * s) + -2 * s) := by
          rw [hsum2]
      _ = Real.rpow (3 : ℝ) (-s) := by
          congr 1
          ring
  rw [hdepth, hmult, hforce]
  nth_rewrite 2 [← hfactor]
  ring

theorem coarsePoincareRHSWeightedDepthParentHalfCoeff_eq_base_mul_ratio_pow
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s θ : ℝ) (m k : ℕ) :
    (coarsePoincareRHSScaledStepCoeff s θ) ^ k *
        (coarsePoincareRHSDepthWeight s (m + k) *
          coarsePoincareRHSParentHalfCoeff Q a s (m + k)) =
      (coarsePoincareRHSDepthWeight s m *
          coarsePoincareRHSParentHalfCoeff Q a s m) *
        (coarsePoincareRHSFiniteSumRatio s θ) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        (coarsePoincareRHSScaledStepCoeff s θ) ^ (k + 1) *
            (coarsePoincareRHSDepthWeight s (m + (k + 1)) *
              coarsePoincareRHSParentHalfCoeff Q a s (m + (k + 1)))
            =
          (coarsePoincareRHSScaledStepCoeff s θ) *
            ((coarsePoincareRHSScaledStepCoeff s θ) ^ k *
              (coarsePoincareRHSDepthWeight s ((m + k) + 1) *
                coarsePoincareRHSParentHalfCoeff Q a s ((m + k) + 1))) := by
            rw [pow_succ]
            rw [← Nat.add_assoc]
            ring
        _ =
          (coarsePoincareRHSScaledStepCoeff s θ) *
            ((coarsePoincareRHSScaledStepCoeff s θ) ^ k *
              (coarsePoincareRHSDepthWeight s (m + k) *
                coarsePoincareRHSParentHalfCoeff Q a s (m + k))) := by
            rw [coarsePoincareRHSDepthWeight_mul_parentHalfCoeff_succ Q a s (m + k)]
        _ =
          coarsePoincareRHSScaledStepCoeff s θ *
            ((coarsePoincareRHSScaledStepCoeff s θ) ^ k *
              (coarsePoincareRHSDepthWeight s (m + k) *
                coarsePoincareRHSParentHalfCoeff Q a s (m + k))) := by
            ring
        _ =
          coarsePoincareRHSScaledStepCoeff s θ *
            ((coarsePoincareRHSDepthWeight s m *
                coarsePoincareRHSParentHalfCoeff Q a s m) *
              (coarsePoincareRHSFiniteSumRatio s θ) ^ k) := by
            rw [ih]
        _ =
          (coarsePoincareRHSDepthWeight s m *
              coarsePoincareRHSParentHalfCoeff Q a s m) *
            (coarsePoincareRHSFiniteSumRatio s θ) ^ (k + 1) := by
            unfold coarsePoincareRHSFiniteSumRatio
            rw [pow_succ]
            ring

theorem coarsePoincareRHSIntrinsicWeightedForceFactor_eq_base_mul_ratio_pow
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s θ : ℝ) (m k : ℕ) :
    (coarsePoincareRHSScaledStepCoeff s θ) ^ k *
        (coarsePoincareRHSDepthWeight s (m + k) *
          ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s (m + k)) ^ 2 *
            coarsePoincareRHSGlobalForceBound Q g s (m + k))) =
      (coarsePoincareRHSDepthWeight s m *
        ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s m) ^ 2 *
          coarsePoincareRHSGlobalForceBound Q g s m)) *
        (coarsePoincareRHSForceFiniteSumRatio s θ) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        (coarsePoincareRHSScaledStepCoeff s θ) ^ (k + 1) *
            (coarsePoincareRHSDepthWeight s (m + (k + 1)) *
              ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s (m + (k + 1))) ^ 2 *
                coarsePoincareRHSGlobalForceBound Q g s (m + (k + 1))))
            =
          (coarsePoincareRHSScaledStepCoeff s θ) *
            ((coarsePoincareRHSScaledStepCoeff s θ) ^ k *
              (coarsePoincareRHSDepthWeight s ((m + k) + 1) *
                ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s ((m + k) + 1)) ^ 2 *
                  coarsePoincareRHSGlobalForceBound Q g s ((m + k) + 1)))) := by
            rw [pow_succ]
            rw [← Nat.add_assoc]
            ring
        _ =
          (coarsePoincareRHSScaledStepCoeff s θ) *
            ((coarsePoincareRHSScaledStepCoeff s θ) ^ k *
              (Real.rpow (3 : ℝ) (-s) *
                (coarsePoincareRHSDepthWeight s (m + k) *
                  ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s (m + k)) ^ 2 *
                    coarsePoincareRHSGlobalForceBound Q g s (m + k))))) := by
            rw [coarsePoincareRHSIntrinsicForceFactor_succ Q a g s (m + k)]
        _ =
          (coarsePoincareRHSScaledStepCoeff s θ * Real.rpow (3 : ℝ) (-s)) *
            ((coarsePoincareRHSScaledStepCoeff s θ) ^ k *
              (coarsePoincareRHSDepthWeight s (m + k) *
                ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s (m + k)) ^ 2 *
                  coarsePoincareRHSGlobalForceBound Q g s (m + k)))) := by
            ring
        _ =
          (coarsePoincareRHSScaledStepCoeff s θ * Real.rpow (3 : ℝ) (-s)) *
            ((coarsePoincareRHSDepthWeight s m *
              ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s m) ^ 2 *
                coarsePoincareRHSGlobalForceBound Q g s m)) *
              (coarsePoincareRHSForceFiniteSumRatio s θ) ^ k) := by
            rw [ih]
        _ =
          (coarsePoincareRHSDepthWeight s m *
            ((coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s m) ^ 2 *
              coarsePoincareRHSGlobalForceBound Q g s m)) *
            (coarsePoincareRHSForceFiniteSumRatio s θ) ^ (k + 1) := by
            unfold coarsePoincareRHSForceFiniteSumRatio
            rw [pow_succ]
            ring


end

end Homogenization
