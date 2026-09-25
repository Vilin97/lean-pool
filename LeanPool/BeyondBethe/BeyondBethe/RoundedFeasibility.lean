/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.AdaptiveRoundedEllipsoid
public import LeanPool.BeyondBethe.BeyondBethe.RationalFeasibility
public import Mathlib.Tactic

/-! # Rounded Feasibility -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Bounded-bit rational feasibility

This is the executable feasibility loop used by the optimizer.  It differs
from `runRationalFeasibility` only in replacing the exact central update by
the adaptive rounded update.  The proofs below re-establish acceptance,
target preservation, nonsingularity, and finite termination with the weaker
rounded contraction constant.
-/

def runRoundedRationalFeasibility {d : ℕ}
    (oracle : RationalCentralOracle d) :
    ℕ → RationalEllipsoidState d → RationalFeasibilityResult d
  | 0, E => .exhausted E
  | budget + 1, E =>
      match oracle E with
      | .accept => .accepted E.center
      | .cut a =>
          runRoundedRationalFeasibility oracle budget
            (adaptiveRoundedEllipsoidCentralUpdate E a)

theorem runRoundedRationalFeasibility_acceptsOnly {d : ℕ}
    {Good : (Fin d → ℚ) → Prop} {oracle : RationalCentralOracle d}
    (haccept : RationalCentralOracleAcceptsOnly Good oracle)
    {budget : ℕ} {E : RationalEllipsoidState d} {x : Fin d → ℚ}
    (hrun : runRoundedRationalFeasibility oracle budget E = .accepted x) :
    Good x := by
  induction budget generalizing E with
  | zero => simp [runRoundedRationalFeasibility] at hrun
  | succ budget ih =>
      rw [runRoundedRationalFeasibility] at hrun
      split at hrun <;> rename_i hresponse
      · cases hrun
        exact haccept E hresponse
      · exact ih hrun

/-- Physical form of adaptive rounded containment. -/
theorem adaptiveRoundedEllipsoidCentralUpdate_contains_point {d : ℕ}
    (hd : 0 < d) (E : RationalEllipsoidState d) (a : Fin d → ℚ)
    (hdet : Matrix.det E.basis ≠ 0)
    {x : Fin d → ℝ} (hcontains : RationalEllipsoidContains E x)
    (ha : a ≠ 0)
    (hcut : finiteDot (fun i ↦ (a i : ℝ))
      (fun i ↦ x i - rationalCenterReal E i) ≤ 0) :
    RationalEllipsoidContains
      (adaptiveRoundedEllipsoidCentralUpdate E a) x := by
  obtain ⟨y, hy, hpoint⟩ := hcontains
  have hb := rationalPulledBackNormal_ne_zero_of_det_ne_zero E a hdet ha
  have hpulled : finiteDot
      (fun j ↦ (rationalPulledBackNormal E a j : ℝ)) y ≤ 0 := by
    rw [← physicalDot_point_sub_center_eq_pulledDot E a y]
    simpa only [hpoint] using hcut
  obtain ⟨y', hy', hpoint'⟩ :=
    adaptiveRoundedEllipsoidCentralUpdate_contains hd E a hdet hb hy hpulled
  exact ⟨y', hy', hpoint'.trans hpoint⟩

theorem runRoundedRationalFeasibility_preserves_target_of_exhausted {d : ℕ}
    (hd : 0 < d) {K : (Fin d → ℝ) → Prop}
    {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid K oracle)
    {budget : ℕ} {E E' : RationalEllipsoidState d}
    (hdet : Matrix.det E.basis ≠ 0)
    (hrun : runRoundedRationalFeasibility oracle budget E = .exhausted E')
    {x : Fin d → ℝ} (hK : K x)
    (hcontains : RationalEllipsoidContains E x) :
    RationalEllipsoidContains E' x := by
  induction budget generalizing E E' with
  | zero =>
      simp only [runRoundedRationalFeasibility] at hrun
      cases hrun
      exact hcontains
  | succ budget ih =>
      rw [runRoundedRationalFeasibility] at hrun
      split at hrun <;> rename_i hresponse
      · contradiction
      · have hcut := hvalid E _ hresponse
        have hnext := adaptiveRoundedEllipsoidCentralUpdate_contains_point
          hd E _ hdet hcontains hcut.1 (hcut.2 x hK)
        have hpulled := rationalPulledBackNormal_ne_zero_of_det_ne_zero
          E _ hdet hcut.1
        exact ih
          (det_adaptiveRoundedEllipsoidCentralUpdate_ne_zero
            hd E _ hdet hpulled)
          hrun hnext

theorem roundedContractionFactor_nonneg {d : ℕ} (hd : 0 < d) :
    0 ≤ 1 - 1 / (32 * (d : ℝ) ^ 3) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (1 : ℝ) ≤ 32 * (d : ℝ) ^ 3 := by
    nlinarith [one_le_pow₀ (n := 3) hdR]
  exact sub_nonneg.mpr
    ((div_le_one (by positivity : (0 : ℝ) < 32 * (d : ℝ) ^ 3)).2 hden)

theorem runRoundedRationalFeasibility_det_upper_of_exhausted {d : ℕ}
    (hd : 0 < d) {K : (Fin d → ℝ) → Prop}
    {oracle : RationalCentralOracle d}
    (hvalid : RationalCentralOracleValid K oracle)
    {budget : ℕ} {E E' : RationalEllipsoidState d}
    (hdet : Matrix.det E.basis ≠ 0)
    (hrun : runRoundedRationalFeasibility oracle budget E = .exhausted E') :
    abs ((Matrix.det E'.basis : ℚ) : ℝ) ≤
      (1 - 1 / (32 * (d : ℝ) ^ 3)) ^ budget *
        abs ((Matrix.det E.basis : ℚ) : ℝ) := by
  induction budget generalizing E E' with
  | zero =>
      simp only [runRoundedRationalFeasibility] at hrun
      cases hrun
      simp
  | succ budget ih =>
      rw [runRoundedRationalFeasibility] at hrun
      split at hrun
      · rename_i hresponse
        contradiction
      · rename_i a hresponse
        have hcut := hvalid E a hresponse
        have hpulled := rationalPulledBackNormal_ne_zero_of_det_ne_zero
          E a hdet hcut.1
        let Enext := adaptiveRoundedEllipsoidCentralUpdate E a
        have hdetNext : Matrix.det Enext.basis ≠ 0 :=
          det_adaptiveRoundedEllipsoidCentralUpdate_ne_zero
            hd E a hdet hpulled
        have htail := ih hdetNext hrun
        have hstep := abs_det_adaptiveRoundedCentralUpdate_le
          hd E a hdet hpulled
        have hfactor0 := roundedContractionFactor_nonneg hd
        calc
          abs ((Matrix.det E'.basis : ℚ) : ℝ) ≤
              (1 - 1 / (32 * (d : ℝ) ^ 3)) ^ budget *
                abs ((Matrix.det Enext.basis : ℚ) : ℝ) := htail
          _ ≤ (1 - 1 / (32 * (d : ℝ) ^ 3)) ^ budget *
              ((1 - 1 / (32 * (d : ℝ) ^ 3)) *
                abs ((Matrix.det E.basis : ℚ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hstep (pow_nonneg hfactor0 _)
          _ = (1 - 1 / (32 * (d : ℝ) ^ 3)) ^ (budget + 1) *
              abs ((Matrix.det E.basis : ℚ) : ℝ) := by
            rw [pow_succ]
            ring

theorem roundedContractionFactor_pow_budget_le_half_pow
    {d M : ℕ} (hd : 0 < d) :
    (1 - 1 / (32 * (d : ℝ) ^ 3)) ^ (32 * d ^ 3 * M) ≤
      (1 / 2 : ℝ) ^ M := by
  let x : ℝ := 1 / (32 * (d : ℝ) ^ 3)
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hbase : 1 - x ≤ Real.exp (-x) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-x)
  have hfactor : 0 ≤ 1 - x := by
    simpa only [x] using roundedContractionFactor_nonneg hd
  have hpow := pow_le_pow_left₀ hfactor hbase (32 * d ^ 3 * M)
  have hexp : (Real.exp (-x)) ^ (32 * d ^ 3 * M) =
      Real.exp (-(M : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [x]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    push_cast
    field_simp
  calc
    (1 - 1 / (32 * (d : ℝ) ^ 3)) ^ (32 * d ^ 3 * M) =
        (1 - x) ^ (32 * d ^ 3 * M) := by rfl
    _ ≤ (Real.exp (-x)) ^ (32 * d ^ 3 * M) := hpow
    _ = Real.exp (-(M : ℝ)) := hexp
    _ = Real.exp (-1) ^ M := by
      rw [show -(M : ℝ) = (M : ℝ) * (-1 : ℝ) by ring,
        Real.exp_nat_mul]
    _ ≤ (1 / 2 : ℝ) ^ M :=
      pow_le_pow_left₀ (Real.exp_pos (-1)).le real_exp_neg_one_le_half M

/-- A rounded run cannot exhaust the determinant budget while retaining the
coordinate endpoints of a radius-`r` ball. -/
theorem runRoundedRationalFeasibility_not_exhausted_of_inner_cross
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
    runRoundedRationalFeasibility oracle (32 * d ^ 3 * M) E ≠
      .exhausted E' := by
  intro hrun
  have hplus : ∀ k, RationalEllipsoidContains E'
      (fun i ↦ z i + if i = k then r else 0) := by
    intro k
    exact runRoundedRationalFeasibility_preserves_target_of_exhausted
      hd hvalid hdet hrun (hKplus k) (hEplus k)
  have hminus : ∀ k, RationalEllipsoidContains E'
      (fun i ↦ z i - if i = k then r else 0) := by
    intro k
    exact runRoundedRationalFeasibility_preserves_target_of_exhausted
      hd hvalid hdet hrun (hKminus k) (hEminus k)
  have hlower := rationalEllipsoid_storedDet_lower_of_ball_endpoints
    E' hr (fun k ↦ hplus k) (fun k ↦ hminus k)
  have hupper := runRoundedRationalFeasibility_det_upper_of_exhausted
    hd hvalid hdet hrun
  have hfactor := roundedContractionFactor_pow_budget_le_half_pow
    (d := d) (M := M) hd
  have hdetUpper : abs ((Matrix.det E'.basis : ℚ) : ℝ) ≤
      (1 / 2 : ℝ) ^ M * abs ((Matrix.det E.basis : ℚ) : ℝ) :=
    hupper.trans (mul_le_mul_of_nonneg_right hfactor (abs_nonneg _))
  have hsandwich : r ^ d ≤
      Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) *
        (1 / 2 : ℝ) ^ M := by
    calc
      r ^ d ≤ Nat.factorial d *
          abs ((Matrix.det E'.basis : ℚ) : ℝ) := hlower
      _ ≤ Nat.factorial d *
          ((1 / 2 : ℝ) ^ M *
            abs ((Matrix.det E.basis : ℚ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hdetUpper (Nat.cast_nonneg _)
      _ = Nat.factorial d * abs ((Matrix.det E.basis : ℚ) : ℝ) *
          (1 / 2 : ℝ) ^ M := by ring
  exact (not_lt_of_ge hsandwich) hdyadic

/-- Ball specialization used by the concrete epigraph feasibility call. -/
theorem runRoundedRationalFeasibility_ball_accepts
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
      runRoundedRationalFeasibility oracle
          (32 * d ^ 3 * rationalBallDyadicExponent d R r)
          (rationalBallEllipsoid d c R) = .accepted x ∧ Good x := by
  let E := rationalBallEllipsoid d c R
  let budget := 32 * d ^ 3 * rationalBallDyadicExponent d R r
  let result := runRoundedRationalFeasibility oracle budget E
  cases hresult : result with
  | accepted x =>
      refine ⟨x, ?_, ?_⟩
      · simpa only [result, budget, E] using hresult
      · exact runRoundedRationalFeasibility_acceptsOnly haccept
          (by simpa only [result, budget, E] using hresult)
  | exhausted E' =>
      exfalso
      apply runRoundedRationalFeasibility_not_exhausted_of_inner_cross
        hd hvalid E
          (by
            dsimp only [E]
            rw [det_rationalBallEllipsoid]
            exact pow_ne_zero _ hR.ne')
          (hr := Rat.cast_nonneg.mpr hr.le)
          (rationalBallEllipsoid_dyadic_budget hd c hR hr)
          hKplus hKminus
      · intro k
        exact rationalBallEllipsoid_contains c hR (houterPlus k)
      · intro k
        exact rationalBallEllipsoid_contains c hR (houterMinus k)
      · simpa only [result, budget, E] using hresult

end BeyondBethe
