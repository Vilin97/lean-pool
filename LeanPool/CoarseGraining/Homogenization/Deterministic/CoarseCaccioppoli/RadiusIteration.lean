/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.RadiusIteration.Standard
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CrossTerm
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Radius Iteration -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators

theorem coarseCaccioppoliBoundaryAlphaOfHeight_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (h : ℝ → ℝ → ℝ)
    {ρ₁ ρ₂ : ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) (hρ : ρ₁ < ρ₂) :
    0 ≤ coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂ := by
  have hs1 : s < 1 := by
    linarith
  have hden_nonneg : 0 ≤ s * (1 - s) := by
    nlinarith
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  unfold coarseCaccioppoliBoundaryAlphaOfHeight
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (div_nonneg hC hden_nonneg)
        (coarseCaccioppoliGapInv_nonneg hρ))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
    (Real.rpow_nonneg htheta_nonneg _)

theorem coarseCaccioppoliBoundaryCrossCoeffOfHeight_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ) (h : ℝ → ℝ → ℝ)
    {ρ₁ ρ₂ : ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (hρ : ρ₁ < ρ₂) :
    0 ≤ coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂ := by
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  unfold coarseCaccioppoliBoundaryCrossCoeffOfHeight
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (coarseCaccioppoliGapInv_nonneg hρ))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
      (Real.rpow_nonneg hLambda_nonneg _))
    (Real.sqrt_nonneg _)

theorem coarseCaccioppoli_absorb_cross_term
    {x α B : ℝ} (hx : 0 ≤ x) (hα : α ≤ (1 / 4 : ℝ)) :
    α * x + B * Real.sqrt x ≤ (1 / 2 : ℝ) * x + B ^ (2 : ℕ) := by
  have hαx : α * x ≤ (1 / 4 : ℝ) * x := by
    exact mul_le_mul_of_nonneg_right hα hx
  have hsq :
      (Real.sqrt x / 2) ^ (2 : ℕ) = x / 4 := by
    calc
      (Real.sqrt x / 2) ^ (2 : ℕ) = (Real.sqrt x) ^ (2 : ℕ) / 4 := by
        ring_nf
      _ = x / 4 := by
        rw [Real.sq_sqrt hx]
  have hyoung : B * Real.sqrt x ≤ B ^ (2 : ℕ) + x / 4 := by
    calc
      B * Real.sqrt x = 2 * B * (Real.sqrt x / 2) := by ring
      _ ≤ B ^ (2 : ℕ) + (Real.sqrt x / 2) ^ (2 : ℕ) := by
        simpa [pow_two] using (two_mul_le_add_sq B (Real.sqrt x / 2))
      _ = B ^ (2 : ℕ) + x / 4 := by rw [hsq]
  calc
    α * x + B * Real.sqrt x ≤ (1 / 4 : ℝ) * x + B * Real.sqrt x := by
      gcongr
    _ ≤ (1 / 4 : ℝ) * x + (B ^ (2 : ℕ) + x / 4) := by
      gcongr
    _ = (1 / 2 : ℝ) * x + B ^ (2 : ℕ) := by ring

private theorem coarseCaccioppoli_radius_iteration_term_le_majorant
    (β : ℝ) (_hβ : 0 ≤ β) :
    ∀ n : ℕ,
      coarseCaccioppoliRadiusIterationTerm β n ≤
        (2 : ℝ) ^ Nat.ceil β *
          ((((n + 2 : ℕ) : ℝ) ^ (2 * Nat.ceil β)) * (1 / 2 : ℝ) ^ n) := by
  intro n
  let k : ℕ := Nat.ceil β
  let m : ℝ := (((n + 1) * (n + 2) : ℕ) : ℝ)
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    positivity
  have hm_one : 1 ≤ m := by
    have hn1_nat : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hn2_nat : 1 ≤ n + 2 := by
      omega
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hn1_nat
    have hn2 : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast hn2_nat
    have hmul :
        (1 : ℝ) * 1 ≤ ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) := by
      exact mul_le_mul hn1 hn2 (by positivity) (by positivity)
    simpa [m] using hmul
  have hgap_rpow :
      Real.rpow
          (coarseCaccioppoliRadiusSequence (n + 1) - coarseCaccioppoliRadiusSequence n)
          (-β) =
        Real.rpow ((3 / 2 : ℝ) * m) β := by
    rw [coarseCaccioppoliRadiusSequence_succ_sub]
    calc
      Real.rpow (2 / (3 * (((n + 1) * (n + 2) : ℕ) : ℝ))) (-β)
          = Real.rpow ((2 / (3 * (((n + 1) * (n + 2) : ℕ) : ℝ)))⁻¹) β := by
              simpa using
                (Real.rpow_neg_eq_inv_rpow
                  (2 / (3 * (((n + 1) * (n + 2) : ℕ) : ℝ))) β)
      _ = Real.rpow ((3 / 2 : ℝ) * m) β := by
            have hm_pos : 0 < m := by
              dsimp [m]
              positivity
            have hm_ne : m ≠ 0 := hm_pos.ne'
            have hinv : (2 / (3 * m))⁻¹ = (3 / 2 : ℝ) * m := by
              field_simp [hm_ne]
            simpa [m] using congrArg (fun x : ℝ => Real.rpow x β) hinv
  have hk_le : β ≤ (k : ℝ) := Nat.le_ceil β
  have hbase_one : 1 ≤ (3 / 2 : ℝ) * m := by
    nlinarith
  have hbase_nonneg : 0 ≤ (3 / 2 : ℝ) * m := by positivity
  have hbase_le : (3 / 2 : ℝ) * m ≤ 2 * (((n + 2 : ℕ) : ℝ) ^ 2) := by
    have hm_le : m ≤ (((n + 2 : ℕ) : ℝ) ^ 2) := by
      have hstep : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_succ (n + 1)
      have hnonneg : 0 ≤ ((n + 2 : ℕ) : ℝ) := by positivity
      have hmul :
          (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) ≤
            ((n + 2 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hstep hnonneg
      simpa [m, pow_two] using hmul
    nlinarith
  calc
    coarseCaccioppoliRadiusIterationTerm β n
        = (1 / 2 : ℝ) ^ n * Real.rpow ((3 / 2 : ℝ) * m) β := by
            rw [coarseCaccioppoliRadiusIterationTerm, hgap_rpow]
    _ ≤ (1 / 2 : ℝ) ^ n * Real.rpow ((3 / 2 : ℝ) * m) (k : ℝ) := by
          gcongr
          exact Real.rpow_le_rpow_of_exponent_le hbase_one hk_le
    _ = (1 / 2 : ℝ) ^ n * (((3 / 2 : ℝ) * m) ^ k) := by
          have hnat : Real.rpow ((3 / 2 : ℝ) * m) (k : ℝ) = (((3 / 2 : ℝ) * m) ^ k) := by
            exact Real.rpow_natCast ((3 / 2 : ℝ) * m) k
          rw [hnat]
    _ ≤ (1 / 2 : ℝ) ^ n * (2 * (((n + 2 : ℕ) : ℝ) ^ 2)) ^ k := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_left₀ hbase_nonneg hbase_le k
    _ = (2 : ℝ) ^ k * ((((n + 2 : ℕ) : ℝ) ^ (2 * k)) * (1 / 2 : ℝ) ^ n) := by
          rw [mul_pow, pow_mul]
          ring

private theorem coarseCaccioppoli_radius_iteration_term_summable
    (β : ℝ) (hβ : 0 ≤ β) :
    Summable (coarseCaccioppoliRadiusIterationTerm β) := by
  let k : ℕ := Nat.ceil β
  have hhalf : ‖(1 / 2 : ℝ)‖ < 1 := by
    norm_num
  have hpoly :
      Summable (fun n : ℕ => (n : ℝ) ^ (2 * k) * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (2 * k) hhalf
  have hshift :
      Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (2 * k) * (1 / 2 : ℝ) ^ (n + 2)) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => (n : ℝ) ^ (2 * k) * (1 / 2 : ℝ) ^ n) 2).2 hpoly
  have hmajor :
      Summable (fun n : ℕ =>
        (2 : ℝ) ^ k * ((((n + 2 : ℕ) : ℝ) ^ (2 * k)) * (1 / 2 : ℝ) ^ n)) := by
    have hfun :
        (fun n : ℕ =>
          (2 : ℝ) ^ (k + 2) *
            ((((n + 2 : ℕ) : ℝ) ^ (2 * k)) * (1 / 2 : ℝ) ^ (n + 2))) =
        (fun n : ℕ =>
          (2 : ℝ) ^ k * ((((n + 2 : ℕ) : ℝ) ^ (2 * k)) * (1 / 2 : ℝ) ^ n)) := by
      funext n
      rw [pow_add, pow_two]
      ring_nf
    rw [← hfun]
    exact hshift.mul_left ((2 : ℝ) ^ (k + 2))
  exact hmajor.of_nonneg_of_le
    (fun n => coarseCaccioppoliRadiusIterationTerm_nonneg β n)
    (fun n => coarseCaccioppoli_radius_iteration_term_le_majorant β hβ n)

/-- The deterministic radius-iteration constant is nonnegative. -/
theorem coarseCaccioppoliRadiusIterationConst_nonneg (β : ℝ) :
    0 ≤ coarseCaccioppoliRadiusIterationConst β := by
  unfold coarseCaccioppoliRadiusIterationConst
  exact tsum_nonneg fun n => coarseCaccioppoliRadiusIterationTerm_nonneg β n

/--
Explicit polynomial-geometric majorant for the deterministic radius-iteration
constant.

This is the scalar bottleneck isolated from the Caccioppoli proof: the final
uniform public constant only has to bound this displayed series after taking
the note exponent root.
-/
theorem coarseCaccioppoliRadiusIterationConst_le_majorant_tsum
    (β : ℝ) (hβ : 0 ≤ β) :
    coarseCaccioppoliRadiusIterationConst β ≤
      ∑' n : ℕ,
        (2 : ℝ) ^ Nat.ceil β *
          ((((n + 2 : ℕ) : ℝ) ^ (2 * Nat.ceil β)) * (1 / 2 : ℝ) ^ n) := by
  let k : ℕ := Nat.ceil β
  have hhalf : ‖(1 / 2 : ℝ)‖ < 1 := by
    norm_num
  have hpoly :
      Summable (fun n : ℕ => (n : ℝ) ^ (2 * k) * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (2 * k) hhalf
  have hshift :
      Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (2 * k) * (1 / 2 : ℝ) ^ (n + 2)) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => (n : ℝ) ^ (2 * k) * (1 / 2 : ℝ) ^ n) 2).2 hpoly
  have hmajor :
      Summable (fun n : ℕ =>
        (2 : ℝ) ^ k * ((((n + 2 : ℕ) : ℝ) ^ (2 * k)) * (1 / 2 : ℝ) ^ n)) := by
    have hfun :
        (fun n : ℕ =>
          (2 : ℝ) ^ (k + 2) *
            ((((n + 2 : ℕ) : ℝ) ^ (2 * k)) * (1 / 2 : ℝ) ^ (n + 2))) =
        (fun n : ℕ =>
          (2 : ℝ) ^ k * ((((n + 2 : ℕ) : ℝ) ^ (2 * k)) * (1 / 2 : ℝ) ^ n)) := by
      funext n
      rw [pow_add, pow_two]
      ring_nf
    rw [← hfun]
    exact hshift.mul_left ((2 : ℝ) ^ (k + 2))
  unfold coarseCaccioppoliRadiusIterationConst
  simpa [k] using
    (coarseCaccioppoli_radius_iteration_term_summable β hβ).tsum_le_tsum
      (fun n => coarseCaccioppoli_radius_iteration_term_le_majorant β hβ n)
      hmajor

private theorem coarseCaccioppoli_shifted_pow_le_factorial_mul_choose
    (m n : ℕ) :
    (((n + 2 : ℕ) : ℝ) ^ m) ≤
      (m.factorial : ℝ) * (((n + m + 1).choose m : ℕ) : ℝ) := by
  have h :=
    Nat.pow_le_choose (α := ℝ) m (n + m + 1)
  have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hmul :=
    (div_le_iff₀ hfac_pos).1 h
  have hnat : n + m + 1 + 1 - m = n + 2 := by
    omega
  simpa [hnat, Nat.cast_pow, mul_comm, mul_left_comm, mul_assoc] using hmul

private theorem coarseCaccioppoli_shifted_choose_geometric_tsum_le
    (m : ℕ) :
    (∑' n : ℕ,
        (((n + m + 1).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) ≤
      (2 : ℝ) ^ (m + 2) := by
  let f : ℕ → ℝ := fun n =>
    (((n + m).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n
  have hhalf : ‖(1 / 2 : ℝ)‖ < 1 := by
    norm_num
  have hf : Summable f := by
    simpa [f] using
      (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) m hhalf)
  have hshift :
      (∑' n : ℕ,
          (((n + m + 1).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) =
        2 * ∑' n : ℕ, f (n + 1) := by
    calc
      (∑' n : ℕ,
          (((n + m + 1).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n)
          = ∑' n : ℕ, 2 * f (n + 1) := by
              apply tsum_congr
              intro n
              dsimp [f]
              rw [show n + 1 + m = n + m + 1 by omega, pow_succ]
              ring
      _ = 2 * ∑' n : ℕ, f (n + 1) := by
              rw [tsum_mul_left]
  have htail :
      ∑' n : ℕ, f (n + 1) ≤ ∑' n : ℕ, f n := by
    have hsum := hf.sum_add_tsum_nat_add 1
    have hfirst_nonneg : 0 ≤ ∑ n ∈ Finset.range 1, f n := by
      refine Finset.sum_nonneg ?_
      intro n _hn
      dsimp [f]
      exact mul_nonneg (by positivity) (pow_nonneg (by norm_num) n)
    linarith
  have htsum :
      (∑' n : ℕ, f n) = (2 : ℝ) ^ (m + 1) := by
    have hclosed :=
      (tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) m hhalf)
    have hhalf_sub : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
    calc
      (∑' n : ℕ, f n)
          = 1 / (1 - (1 / 2 : ℝ)) ^ (m + 1) := by
              simpa [f] using hclosed
      _ = 1 / (1 / 2 : ℝ) ^ (m + 1) := by rw [hhalf_sub]
      _ = (2 : ℝ) ^ (m + 1) := by
              rw [one_div, ← inv_pow]
              norm_num
  calc
    (∑' n : ℕ,
        (((n + m + 1).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n)
        = 2 * ∑' n : ℕ, f (n + 1) := hshift
    _ ≤ 2 * ∑' n : ℕ, f n := by
          exact mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = 2 * (2 : ℝ) ^ (m + 1) := by rw [htsum]
    _ = (2 : ℝ) ^ (m + 2) := by
          rw [show m + 2 = m + 1 + 1 by omega, pow_succ]
          ring

private theorem coarseCaccioppoli_shifted_pow_geometric_tsum_le
    (m : ℕ) :
    (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ m) * (1 / 2 : ℝ) ^ n) ≤
      (m.factorial : ℝ) * (2 : ℝ) ^ (m + 2) := by
  have hhalf : ‖(1 / 2 : ℝ)‖ < 1 := by
    norm_num
  have hright :
      Summable (fun n : ℕ =>
        (m.factorial : ℝ) *
          ((((n + m + 1).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n)) := by
    have hchoose :
        Summable (fun n : ℕ =>
          (((n + m + 1).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) := by
      have hbase :
          Summable (fun n : ℕ =>
            (((n + m).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) := by
        simpa using
          (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) m hhalf)
      exact
        (((summable_nat_add_iff 1).2 hbase).mul_left (2 : ℝ)).congr
          (fun n => by
            rw [show n + 1 + m = n + m + 1 by omega, pow_succ]
            ring)
    exact hchoose.mul_left (m.factorial : ℝ)
  have hterm : ∀ n : ℕ,
      (((n + 2 : ℕ) : ℝ) ^ m) * (1 / 2 : ℝ) ^ n ≤
        (m.factorial : ℝ) *
          ((((n + m + 1).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) := by
    intro n
    have hpow :=
      coarseCaccioppoli_shifted_pow_le_factorial_mul_choose m n
    have hgeom_nonneg : 0 ≤ (1 / 2 : ℝ) ^ n :=
      pow_nonneg (by norm_num) n
    calc
      (((n + 2 : ℕ) : ℝ) ^ m) * (1 / 2 : ℝ) ^ n
          ≤ ((m.factorial : ℝ) * (((n + m + 1).choose m : ℕ) : ℝ)) *
              (1 / 2 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right hpow hgeom_nonneg
      _ =
          (m.factorial : ℝ) *
            ((((n + m + 1).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) := by
            ring
  have hleft :
      Summable (fun n : ℕ =>
        (((n + 2 : ℕ) : ℝ) ^ m) * (1 / 2 : ℝ) ^ n) := by
    exact Summable.of_nonneg_of_le
      (fun n => mul_nonneg (pow_nonneg (by positivity) m)
        (pow_nonneg (by norm_num) n))
      hterm hright
  calc
    (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ m) * (1 / 2 : ℝ) ^ n)
        ≤ ∑' n : ℕ,
          (m.factorial : ℝ) *
            ((((n + m + 1).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) :=
          hleft.tsum_le_tsum hterm hright
    _ =
        (m.factorial : ℝ) *
          ∑' n : ℕ,
            (((n + m + 1).choose m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n := by
          rw [tsum_mul_left]
    _ ≤ (m.factorial : ℝ) * (2 : ℝ) ^ (m + 2) := by
          exact mul_le_mul_of_nonneg_left
            (coarseCaccioppoli_shifted_choose_geometric_tsum_le m)
            (by positivity)

/--
Factorial-geometric upper bound for the deterministic radius-iteration
constant.  This is the quantitative form needed to make the final Caccioppoli
constant dimension-only: after the note exponent root, the remaining growth is
controlled by `σ * ceil β`.
-/
theorem coarseCaccioppoliRadiusIterationConst_le_factorial_majorant
    (β : ℝ) (hβ : 0 ≤ β) :
    let k : ℕ := Nat.ceil β
    coarseCaccioppoliRadiusIterationConst β ≤
      (4 : ℝ) * (2 : ℝ) ^ (3 * k) * (((2 * k).factorial : ℕ) : ℝ) := by
  let k : ℕ := Nat.ceil β
  have hmajor :=
    coarseCaccioppoliRadiusIterationConst_le_majorant_tsum β hβ
  have hseries :=
    coarseCaccioppoli_shifted_pow_geometric_tsum_le (2 * k)
  have hconst_nonneg : 0 ≤ (2 : ℝ) ^ k :=
    pow_nonneg (by norm_num) k
  calc
    coarseCaccioppoliRadiusIterationConst β
        ≤ ∑' n : ℕ,
            (2 : ℝ) ^ k *
              ((((n + 2 : ℕ) : ℝ) ^ (2 * k)) * (1 / 2 : ℝ) ^ n) := by
          simpa [k] using hmajor
    _ =
        (2 : ℝ) ^ k *
          ∑' n : ℕ,
            (((n + 2 : ℕ) : ℝ) ^ (2 * k)) * (1 / 2 : ℝ) ^ n := by
          rw [tsum_mul_left]
    _ ≤
        (2 : ℝ) ^ k *
          (((2 * k).factorial : ℕ) : ℝ) * (2 : ℝ) ^ (2 * k + 2) := by
          nlinarith [mul_le_mul_of_nonneg_left hseries hconst_nonneg]
    _ =
        (4 : ℝ) * (2 : ℝ) ^ (3 * k) * (((2 * k).factorial : ℕ) : ℝ) := by
          rw [show 2 * k + 2 = 2 * k + 1 + 1 by omega, pow_succ,
            show 3 * k = k + 2 * k by omega, pow_add]
          ring

/--
Polynomial-geometric form of the radius-iteration constant.  Compared with
`coarseCaccioppoliRadiusIterationConst_le_factorial_majorant`, this replaces
the factorial by the elementary power bound `n! <= n^n`.
-/
theorem coarseCaccioppoliRadiusIterationConst_le_power_majorant
    (β : ℝ) (hβ : 0 ≤ β) :
    let k : ℕ := Nat.ceil β
    coarseCaccioppoliRadiusIterationConst β ≤
      (4 : ℝ) * (2 : ℝ) ^ (3 * k) * (((2 * k : ℕ) : ℝ) ^ (2 * k)) := by
  let k : ℕ := Nat.ceil β
  have hfac :=
    coarseCaccioppoliRadiusIterationConst_le_factorial_majorant β hβ
  have hfac_le :
      (((2 * k).factorial : ℕ) : ℝ) ≤ (((2 * k : ℕ) : ℝ) ^ (2 * k)) := by
    exact_mod_cast Nat.factorial_le_pow (2 * k)
  have hfront_nonneg : 0 ≤ (4 : ℝ) * (2 : ℝ) ^ (3 * k) := by
    positivity
  calc
    coarseCaccioppoliRadiusIterationConst β
        ≤ (4 : ℝ) * (2 : ℝ) ^ (3 * k) *
            (((2 * k).factorial : ℕ) : ℝ) := by
          simpa [k] using hfac
    _ ≤ (4 : ℝ) * (2 : ℝ) ^ (3 * k) *
            (((2 * k : ℕ) : ℝ) ^ (2 * k)) := by
          exact mul_le_mul_of_nonneg_left hfac_le hfront_nonneg

private theorem coarseCaccioppoli_radius_iteration_raw
    {F : ℝ → ℝ} {A β : ℝ} (hrec : CoarseCaccioppoliRadiusRecurrence F A β) :
    ∀ N : ℕ,
      F (coarseCaccioppoliRadiusSequence 0) ≤
        (1 / 2 : ℝ) ^ N * F (coarseCaccioppoliRadiusSequence N) +
          A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := by
  intro N
  induction N with
  | zero =>
      simp [coarseCaccioppoliRadiusSequence_zero]
  | succ N hN =>
      have hmemN := coarseCaccioppoliRadiusSequence_mem_Icc N
      have hmemNSucc := coarseCaccioppoliRadiusSequence_mem_Icc (N + 1)
      have hlt : coarseCaccioppoliRadiusSequence N < coarseCaccioppoliRadiusSequence (N + 1) :=
        coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self N)
      have hstep :=
        hrec hmemN.1 hlt hmemNSucc.2
      calc
        F (coarseCaccioppoliRadiusSequence 0)
            ≤ (1 / 2 : ℝ) ^ N * F (coarseCaccioppoliRadiusSequence N) +
                A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := hN
        _ ≤ (1 / 2 : ℝ) ^ N *
              ((1 / 2 : ℝ) * F (coarseCaccioppoliRadiusSequence (N + 1)) +
                A * Real.rpow
                  (coarseCaccioppoliRadiusSequence (N + 1) -
                    coarseCaccioppoliRadiusSequence N)
                  (-β)) +
              A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := by
                gcongr
        _ = (1 / 2 : ℝ) ^ (N + 1) * F (coarseCaccioppoliRadiusSequence (N + 1)) +
              A * Finset.sum (Finset.range (N + 1))
                (coarseCaccioppoliRadiusIterationTerm β) := by
                rw [Finset.sum_range_succ, coarseCaccioppoliRadiusIterationTerm]
                rw [pow_succ]
                ring_nf

theorem coarseCaccioppoli_radiusSequenceRecurrence_of_radiusRecurrence
    {F : ℝ → ℝ} {A β : ℝ} (hrec : CoarseCaccioppoliRadiusRecurrence F A β) :
    CoarseCaccioppoliRadiusSequenceRecurrence F A β := by
  intro n
  exact
    hrec
      (coarseCaccioppoliRadiusSequence_mem_Icc n).1
      (coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n))
      (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2

private theorem coarseCaccioppoli_radius_iteration_raw_of_sequenceRecurrence
    {F : ℝ → ℝ} {A β : ℝ} (hrec : CoarseCaccioppoliRadiusSequenceRecurrence F A β) :
    ∀ N : ℕ,
      F (coarseCaccioppoliRadiusSequence 0) ≤
        (1 / 2 : ℝ) ^ N * F (coarseCaccioppoliRadiusSequence N) +
          A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := by
  intro N
  induction N with
  | zero =>
      simp [coarseCaccioppoliRadiusSequence_zero]
  | succ N hN =>
      have hstep := hrec N
      calc
        F (coarseCaccioppoliRadiusSequence 0)
            ≤ (1 / 2 : ℝ) ^ N * F (coarseCaccioppoliRadiusSequence N) +
                A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := hN
        _ ≤ (1 / 2 : ℝ) ^ N *
              ((1 / 2 : ℝ) * F (coarseCaccioppoliRadiusSequence (N + 1)) +
                A * Real.rpow
                  (coarseCaccioppoliRadiusSequence (N + 1) -
                    coarseCaccioppoliRadiusSequence N)
                  (-β)) +
              A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := by
                gcongr
        _ = (1 / 2 : ℝ) ^ (N + 1) * F (coarseCaccioppoliRadiusSequence (N + 1)) +
              A * Finset.sum (Finset.range (N + 1))
                (coarseCaccioppoliRadiusIterationTerm β) := by
                rw [Finset.sum_range_succ, coarseCaccioppoliRadiusIterationTerm]
                rw [pow_succ]
                ring_nf

/-- Quantitative radius iteration on `[1/3, 1]` with the `1/2`-absorption
used in the Chapter-3 coarse Caccioppoli proof. -/
theorem coarseCaccioppoli_radius_iteration
    {F : ℝ → ℝ} {A β : ℝ}
    (hβ : 0 ≤ β) (hA : 0 ≤ A)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hrec : CoarseCaccioppoliRadiusRecurrence F A β) :
    F (1 / 3 : ℝ) ≤ A * coarseCaccioppoliRadiusIterationConst β := by
  rcases hbounded with ⟨B, hB⟩
  have hsum : Summable (coarseCaccioppoliRadiusIterationTerm β) :=
    coarseCaccioppoli_radius_iteration_term_summable β hβ
  have hraw :
      ∀ N : ℕ,
        F (1 / 3 : ℝ) ≤
          (1 / 2 : ℝ) ^ N * B +
            A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := by
    intro N
    have hNmem := coarseCaccioppoliRadiusSequence_mem_Icc N
    calc
      F (1 / 3 : ℝ)
          = F (coarseCaccioppoliRadiusSequence 0) := by simp [coarseCaccioppoliRadiusSequence_zero]
      _ ≤ (1 / 2 : ℝ) ^ N * F (coarseCaccioppoliRadiusSequence N) +
            A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) :=
          coarseCaccioppoli_radius_iteration_raw hrec N
      _ ≤ (1 / 2 : ℝ) ^ N * B +
            A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := by
          have hBN : F (coarseCaccioppoliRadiusSequence N) ≤ B := hB hNmem.1 hNmem.2
          have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
          have hmul :
              (1 / 2 : ℝ) ^ N * F (coarseCaccioppoliRadiusSequence N) ≤
                (1 / 2 : ℝ) ^ N * B :=
            mul_le_mul_of_nonneg_left hBN hhalf_nonneg
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hmul
              (A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β))
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpow :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_const B
  rcases Metric.tendsto_atTop.1 hpow ε hε with ⟨N, hN⟩
  have hsmall_abs : |(1 / 2 : ℝ) ^ N * B| < ε := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hN N le_rfl
  have hsmall : (1 / 2 : ℝ) ^ N * B ≤ ε := by
    exact le_trans (le_abs_self _) hsmall_abs.le
  have hfinite_le_tsum :
      Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) ≤
        coarseCaccioppoliRadiusIterationConst β := by
    unfold coarseCaccioppoliRadiusIterationConst
    exact hsum.sum_le_tsum (Finset.range N) fun n _ =>
      coarseCaccioppoliRadiusIterationTerm_nonneg β n
  calc
    F (1 / 3 : ℝ)
        ≤ (1 / 2 : ℝ) ^ N * B +
            A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := hraw N
    _ ≤ ε + A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := by
          gcongr
    _ ≤ ε + A * coarseCaccioppoliRadiusIterationConst β := by
          gcongr
    _ = A * coarseCaccioppoliRadiusIterationConst β + ε := by ring

/-- Sequence-specialized version of the deterministic Chapter-3 radius
iteration. This is the concrete interface used when the local bridge only
produces the recursive inequality on the consecutive Chapter-3 radii
`(ρ_n, ρ_{n+1})`. -/
theorem coarseCaccioppoli_radius_iteration_of_sequenceRecurrence
    {F : ℝ → ℝ} {A β : ℝ}
    (hβ : 0 ≤ β) (hA : 0 ≤ A)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hrec : CoarseCaccioppoliRadiusSequenceRecurrence F A β) :
    F (1 / 3 : ℝ) ≤ A * coarseCaccioppoliRadiusIterationConst β := by
  rcases hbounded with ⟨B, hB⟩
  have hsum : Summable (coarseCaccioppoliRadiusIterationTerm β) :=
    coarseCaccioppoli_radius_iteration_term_summable β hβ
  have hraw :
      ∀ N : ℕ,
        F (1 / 3 : ℝ) ≤
          (1 / 2 : ℝ) ^ N * B +
            A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := by
    intro N
    have hNmem := coarseCaccioppoliRadiusSequence_mem_Icc N
    calc
      F (1 / 3 : ℝ)
          = F (coarseCaccioppoliRadiusSequence 0) := by simp [coarseCaccioppoliRadiusSequence_zero]
      _ ≤ (1 / 2 : ℝ) ^ N * F (coarseCaccioppoliRadiusSequence N) +
            A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) :=
          coarseCaccioppoli_radius_iteration_raw_of_sequenceRecurrence hrec N
      _ ≤ (1 / 2 : ℝ) ^ N * B +
            A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := by
          have hBN : F (coarseCaccioppoliRadiusSequence N) ≤ B := hB hNmem.1 hNmem.2
          have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
          have hmul :
              (1 / 2 : ℝ) ^ N * F (coarseCaccioppoliRadiusSequence N) ≤
                (1 / 2 : ℝ) ^ N * B :=
            mul_le_mul_of_nonneg_left hBN hhalf_nonneg
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hmul
              (A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β))
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpow :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_const B
  rcases Metric.tendsto_atTop.1 hpow ε hε with ⟨N, hN⟩
  have hsmall_abs : |(1 / 2 : ℝ) ^ N * B| < ε := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hN N le_rfl
  have hsmall : (1 / 2 : ℝ) ^ N * B ≤ ε := by
    exact le_trans (le_abs_self _) hsmall_abs.le
  have hfinite_le_tsum :
      Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) ≤
        coarseCaccioppoliRadiusIterationConst β := by
    unfold coarseCaccioppoliRadiusIterationConst
    exact hsum.sum_le_tsum (Finset.range N) fun n _ =>
      coarseCaccioppoliRadiusIterationTerm_nonneg β n
  calc
    F (1 / 3 : ℝ)
        ≤ (1 / 2 : ℝ) ^ N * B +
            A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := hraw N
    _ ≤ ε + A * Finset.sum (Finset.range N) (coarseCaccioppoliRadiusIterationTerm β) := by
          gcongr
    _ ≤ ε + A * coarseCaccioppoliRadiusIterationConst β := by
          gcongr
    _ = A * coarseCaccioppoliRadiusIterationConst β + ε := by ring

end

end Homogenization
