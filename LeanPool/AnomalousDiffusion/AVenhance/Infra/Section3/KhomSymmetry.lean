/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxSymmetry
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleArithmetic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KhomScalar
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Time averaging the fixed-time flux symmetry, under explicit time regularity. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Interval

namespace AVenhance.Infra.Section3

open AVenhance

/-- Difference of the two diagonal entries of the time-dependent flux matrix. -/
def KhomSymmetry.fluxDiagDiff {β : ℝ} (I : Ingredients β) (κ : ℝ) (m : ℕ) :
    ℝ → ℝ := fun t => I.flux κ m t 1 1 - I.flux κ m t 0 0

/-- The diagonal difference changes sign after a half-period shift. -/
theorem fluxDiagDiff_add_twoCellCount {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ t : ℝ) :
    KhomSymmetry.fluxDiagDiff I κ m (t + 2 * tauPP β I.Λ m) =
      -KhomSymmetry.fluxDiagDiff I κ m t := by
  unfold KhomSymmetry.fluxDiagDiff
  rw [flux_add_twoCellCount_swap I hm κ t 1 1,
    flux_add_twoCellCount_swap I hm κ t 0 0]
  dsimp
  ring

/-- The difference of the two time-averaged diagonal entries is zero whenever
the fixed-time flux entries are continuous in time. -/
theorem khom_diag_entries_eq_of_flux_continuous {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ)
    (hcont : ∀ i j : Fin 2, Continuous (fun t => I.flux κ m t i j)) :
    I.Khom κ m 0 0 = I.Khom κ m 1 1 := by
  let T := 2 * tauPP β I.Λ m
  let P := T + T
  let D := KhomSymmetry.fluxDiagDiff I κ m
  have hDcont : Continuous D := (hcont 1 1).sub (hcont 0 0)
  have hDint (a b : ℝ) : IntervalIntegrable D volume a b :=
    hDcont.intervalIntegrable (μ := volume) a b
  have hshift (t : ℝ) : D (t + T) = -D t := by
    dsimp [D, T]
    exact fluxDiagDiff_add_twoCellCount I hm κ t
  have hperiodic : Function.Periodic D P := by
    intro t
    unfold D KhomSymmetry.fluxDiagDiff
    rw [show t + P = t + 2 * tauPP β I.Λ m + 2 * tauPP β I.Λ m by
      dsimp [P, T]; ring]
    rw [flux_fourCell_periodic I hm κ t 1 1,
      flux_fourCell_periodic I hm κ t 0 0]
  have hcycle : (∫ t in (0 : ℝ)..P, D t) = 0 := by
    have hsecond : (∫ t in T..T + T, D t) =
        -(∫ t in (0 : ℝ)..T, D t) := by
      calc
        (∫ t in T..T + T, D t) =
            ∫ t in (0 : ℝ)..T, D (t + T) :=
              by simpa only [zero_add] using
                (intervalIntegral.integral_comp_add_right
                  (f := D) (a := (0 : ℝ)) (b := T) T).symm
        _ = ∫ t in (0 : ℝ)..T, -D t :=
          intervalIntegral.integral_congr fun t _ => hshift t
        _ = -(∫ t in (0 : ℝ)..T, D t) := by rw [intervalIntegral.integral_neg]
    change (∫ t in (0 : ℝ)..(T + T), D t) = 0
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hDint 0 T) (hDint T (T + T))]
    rw [hsecond]
    ring
  obtain ⟨n, hn⟩ := Infra.Ingredients.tauPP_reciprocal_multiple_four
    I.one_lt_beta I.beta_lt I.two_pow_seven_le hm
  have hτ : 0 < tauPP β I.Λ m :=
    Infra.Cutoff.tauPP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hspan : (n : ℝ) * P = 1 := by
    dsimp [P, T]
    have hn' : (4 * (n : ℝ)) * tauPP β I.Λ m = 1 := by
      have hcast : (4 * (n : ℝ)) = (4 * n : ℕ) := by norm_cast
      rw [hcast, ← hn]
      exact (one_div_mul_cancel (ne_of_gt hτ))
    calc
      (n : ℝ) * (2 * tauPP β I.Λ m + 2 * tauPP β I.Λ m) =
          (4 * (n : ℝ)) * tauPP β I.Λ m := by ring
      _ = 1 := hn'
  have hspanZ : (n : ℤ) • P = 1 := by
    rw [zsmul_eq_mul, Int.cast_natCast]
    exact hspan
  have hlong := hperiodic.intervalIntegral_add_zsmul_eq
    (n : ℤ) (0 : ℝ) (fun a b => hDint a b)
  have hDavg : (∫ t in (0 : ℝ)..1, D t) = 0 := by
    calc
      (∫ t in (0 : ℝ)..1, D t) =
          ∫ t in (0 : ℝ)..(n : ℤ) • P, D t := by rw [← hspanZ]
      _ = (n : ℤ) • ∫ t in (0 : ℝ)..P, D t := by
        simpa only [zero_add] using hlong
      _ = 0 := by rw [hcycle]; simp
  have h001 : IntervalIntegrable (fun t => I.flux κ m t 1 1) volume 0 1 :=
    (hcont 1 1).intervalIntegrable (μ := volume) 0 1
  have h000 : IntervalIntegrable (fun t => I.flux κ m t 0 0) volume 0 1 :=
    (hcont 0 0).intervalIntegrable (μ := volume) 0 1
  have hdiag : I.Khom κ m 1 1 - I.Khom κ m 0 0 = 0 := by
    change (∫ t in (0 : ℝ)..1, I.flux κ m t 1 1) -
        ∫ t in (0 : ℝ)..1, I.flux κ m t 0 0 = 0
    rw [← intervalIntegral.integral_sub h001 h000]
    simpa [D, KhomSymmetry.fluxDiagDiff] using hDavg
  exact (sub_eq_zero.mp hdiag).symm

/-- Conditional completion of the scalar-flux argument: once the fixed-time
flux entries are shown continuous in time, its time average is scalar and its
scalar is at least `κ`. -/
theorem khom_eq_scalar_of_flux_continuous {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ)
    (hcont : ∀ i j : Fin 2, Continuous (fun t => I.flux κ m t i j)) :
    I.Khom κ m = I.KhomScalar κ m • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      0 < I.KhomScalar κ m := by
  have hdiag := khom_diag_entries_eq_of_flux_continuous I hm κ hcont
  have hint (i j : Fin 2) : IntervalIntegrable
      (fun t => I.flux κ m t i j) volume 0 1 :=
    (hcont i j).intervalIntegrable (μ := volume) 0 1
  have h01 : I.Khom κ m 0 1 = 0 := by
    change (∫ t in (0 : ℝ)..1, I.flux κ m t 0 1) = 0
    rw [intervalIntegral.integral_congr (a := (0 : ℝ)) (b := 1)
      (f := fun t => I.flux κ m t 0 1) (g := fun _ => 0)]
    · simp
    · intro t _
      exact flux_offdiag_eq_zero I hm κ t (by decide)
  have h10 : I.Khom κ m 1 0 = 0 := by
    change (∫ t in (0 : ℝ)..1, I.flux κ m t 1 0) = 0
    rw [intervalIntegral.integral_congr (a := (0 : ℝ)) (b := 1)
      (f := fun t => I.flux κ m t 1 0) (g := fun _ => 0)]
    · simp
    · intro t _
      exact flux_offdiag_eq_zero I hm κ t (by decide)
  have hge : κ ≤ I.KhomScalar κ m := by
    change κ ≤ ∫ t in (0 : ℝ)..1, I.flux κ m t 0 0
    have hmono : (∫ _ in (0 : ℝ)..1, κ) ≤
        ∫ t in (0 : ℝ)..1, I.flux κ m t 0 0 := by
      apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        (intervalIntegrable_const) (hint 0 0)
      intro t _
      exact flux_diag_ge_kappa I hm κ t 0
    simpa using hmono
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [Ingredients.KhomScalar]
    · simpa using h01
    · simpa using h10
    · simp only [Ingredients.KhomScalar, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, ite_true, mul_one]
      exact hdiag.symm
  · exact lt_of_lt_of_le hκ hge

end AVenhance.Infra.Section3
