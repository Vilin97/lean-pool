/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceInstanceRecombination
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceProjectionTrace
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AnalyticDerivativeTail
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.MeanZeroEstimate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Drift
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.VariationalEquation

/-! # RelativeError: actual low cutoff plus analytic high tail -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Classical
open AVenhance.Infra.Ergodic
open AVenhance.Infra.Flow
open AVenhance.Infra.Torus

/-- Positive exponential decay exponent in the Fourier trace tail estimate. -/
def e44TailExponent : ℝ := 1 / (2048 * Real.pi * Real.sqrt 2)
/-- Multiplicative constant in the Fourier trace tail estimate. -/
def e44TailConstant : ℝ := 6144

theorem e44_tail_exponent_pos : 0 < e44TailExponent := by
  dsimp [e44TailExponent]
  positivity

theorem TraceInstanceCutoff.e44_tail_coefficient_bound (n : ℕ) :
    3072 * (2 : ℝ) ^ n ≤ e44TailConstant ^ (n + 1) := by
  have h2 : (2 : ℝ) ≤ e44TailConstant := by norm_num [e44TailConstant]
  have h3072 : (3072 : ℝ) ≤ e44TailConstant := by norm_num [e44TailConstant]
  calc
    3072 * (2 : ℝ) ^ n ≤ e44TailConstant * e44TailConstant ^ n := by
      exact mul_le_mul h3072 (pow_le_pow_left₀ (by norm_num) h2 n)
        (by positivity) (by positivity)
    _ = e44TailConstant ^ (n + 1) := by rw [pow_succ]; ring

/-- The analytic complement has exactly the factorial/radius form required by
the scalar low/high combination, once the cutoff lies below `A/r`. -/
theorem TraceInstanceCutoff.e44_high_remainder_bound_for_combination
    {g : Vec 2 → ℝ} {R r A c : ℝ} (M : ℕ) (hR : 0 < R)
    (hgeom : c * R * (A / r) ≤ R * (M + 1 : ℝ) / 1024)
    (hg : ContDiff ℝ ∞ g) (hper : IsZ2Periodic g)
    (hθ : IsThetaAnalytic R g) (hscale : 1 ≤ (R / 2) * (M + 1 : ℝ))
    (w : List (Fin 2)) (hw : 1 ≤ w.length) :
    Real.sqrt (∫ x in unitCell 2,
      (orderedRealDerivative w
        (highRemainder g M) x) ^ 2) ≤
      e44TailConstant * (w.length.factorial : ℝ) *
        (e44TailConstant / R) ^ w.length *
        Real.exp (-c * R * (A / r)) * Real.sqrt (l2NormSq g) := by
  have hraw := thetaAnalytic_derivative_highFrequencyRemainderL2_le
    hg hper hθ hR w (by omega) M hscale
  have hraw' : Real.sqrt (∫ x in unitCell 2,
      (orderedRealDerivative w
        (highRemainder g M) x) ^ 2) ≤
      3072 * (2 ^ w.length * (w.length.factorial : ℝ) *
        Real.sqrt (l2NormSq g) / R ^ w.length) *
        Real.exp (-(R / 2) * (M + 1 : ℝ) / 512) := by
    simpa [Real.sqrt_eq_rpow] using hraw
  have hExp : Real.exp (-(R / 2) * (M + 1 : ℝ) / 512) ≤
      Real.exp (-c * R * (A / r)) := by
    apply Real.exp_le_exp.mpr
    rw [show -(R / 2) * (M + 1 : ℝ) / 512 =
      -(R * (M + 1 : ℝ) / 1024) by ring]
    convert neg_le_neg hgeom using 1; ring
  have hN : 0 ≤ Real.sqrt (l2NormSq g) := Real.sqrt_nonneg _
  have hRpow : 0 < R ^ w.length := pow_pos hR _
  have hcoeff := TraceInstanceCutoff.e44_tail_coefficient_bound w.length
  have hcoeff' :
      3072 * (2 : ℝ) ^ w.length * (w.length.factorial : ℝ) *
          Real.sqrt (l2NormSq g) / R ^ w.length ≤
        e44TailConstant * (w.length.factorial : ℝ) *
          (e44TailConstant / R) ^ w.length * Real.sqrt (l2NormSq g) := by
    have hfact : 0 ≤ (w.length.factorial : ℝ) := Nat.cast_nonneg _
    have hfactor := mul_nonneg hfact hN
    have hmul := mul_le_mul_of_nonneg_right hcoeff hfactor
    have hmul' : 3072 * (2 : ℝ) ^ w.length *
        ((w.length.factorial : ℝ) * Real.sqrt (l2NormSq g)) ≤
      e44TailConstant ^ (w.length + 1) *
        ((w.length.factorial : ℝ) * Real.sqrt (l2NormSq g)) := by
      simpa [mul_assoc] using hmul
    have htarget : e44TailConstant ^ (w.length + 1) *
        ((w.length.factorial : ℝ) * Real.sqrt (l2NormSq g)) / R ^ w.length =
      e44TailConstant * (w.length.factorial : ℝ) *
        (e44TailConstant / R) ^ w.length * Real.sqrt (l2NormSq g) := by
      rw [div_pow]
      field_simp [ne_of_gt hR]
      rw [pow_succ]
      ring
    calc
      3072 * (2 : ℝ) ^ w.length *
          (w.length.factorial : ℝ) * Real.sqrt (l2NormSq g) / R ^ w.length =
        3072 * (2 : ℝ) ^ w.length *
          ((w.length.factorial : ℝ) * Real.sqrt (l2NormSq g)) / R ^ w.length := by ring
      _ ≤
        e44TailConstant ^ (w.length + 1) *
          ((w.length.factorial : ℝ) * Real.sqrt (l2NormSq g)) / R ^ w.length :=
            div_le_div_of_nonneg_right hmul' (by positivity)
      _ = _ := htarget
  have hcoeffNonneg :
      0 ≤ 3072 * (2 ^ w.length * (w.length.factorial : ℝ) *
        Real.sqrt (l2NormSq g) / R ^ w.length) := by positivity
  calc
    _ ≤ 3072 * (2 ^ w.length * (w.length.factorial : ℝ) *
        Real.sqrt (l2NormSq g) / R ^ w.length) *
          Real.exp (-(R / 2) * (M + 1 : ℝ) / 512) := hraw'
    _ ≤ 3072 * (2 ^ w.length * (w.length.factorial : ℝ) *
        Real.sqrt (l2NormSq g) / R ^ w.length) *
          Real.exp (-c * R * (A / r)) :=
        mul_le_mul_of_nonneg_left hExp hcoeffNonneg
    _ ≤ _ := by
      have hcoeff'' :
          3072 * (2 ^ w.length * (w.length.factorial : ℝ) *
            Real.sqrt (l2NormSq g) / R ^ w.length) ≤
          e44TailConstant * (w.length.factorial : ℝ) *
            (e44TailConstant / R) ^ w.length * Real.sqrt (l2NormSq g) := by
        convert hcoeff' using 1; ring
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right hcoeff'' (Real.exp_nonneg _))

/-- Instantiate (7) for a smooth periodic classical solution. The geometric
cutoff facts and the explicit exponential absorption remain named inputs. -/
theorem e44_initialTrace_of_classical_cutoff
    {κ A r R B : ℝ} (M : ℕ)
    {g : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    {X : ℝ → Vec 2 → ℝ → Vec 2}
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (hX : IsFlow (streamVel φ) X)
    (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g u)
    (hθ : IsThetaAnalytic R g) (hmean : ∫ x in unitCube, g x = 0)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hr : 0 < r) (hR : 0 < R) (hA : 1 ≤ A) (hRr : r ≤ R)
    (hB : 0 ≤ B)
    (hDb : ∀ t x, ‖jointSpatialFDeriv (streamVel φ) t x‖ ≤ B)
    (hM : 0 < M)
    (hKup : 2 * Real.pi * Real.sqrt 2 * (M : ℝ) ≤ A / r)
    (hKlow : A / r ≤ 2 * Real.pi * Real.sqrt 2 *
      (M + 1 : ℝ))
    (hmax : max 1 B ≤ κ *
      (2 * Real.pi * Real.sqrt 2 * (M : ℝ)) ^ 2)
    (hTailScale : 1 ≤ (R / 2) * (M + 1 : ℝ))
    (hAbsorb : (Real.sqrt κ)⁻¹ *
      Real.exp (-e44TailExponent * R * (A / r)) ≤ 1) :
    ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in unitCube,
        (Infra.Section4.classicalWordDerivative w g x) ^ 2) ≤
      (Real.sqrt κ * Real.sqrt
        (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t)) *
        ((w.length.factorial : ℝ) /
          (r / e44TraceCombinationConstant A (Real.sqrt 3) e44TailConstant ^ 2) ^
            w.length) := by
  let K : ℝ := 2 * Real.pi * Real.sqrt 2 *
    (M : ℝ)
  let D : ℝ := ∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t
  let S : ℝ := Real.sqrt κ * Real.sqrt D
  have hdiv : ∀ t x, vecDiv (streamVel φ t) x = 0 :=
    streamVel_vecDiv_eq_zero φ hφ
  have hb := streamVel_smoothPeriodic φ hφ
  have hinit : u 0 = g := funext hsol.2.2.1
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    rw [← hinit]
    exact classicalSmooth_slice_nonneg hsol.1 le_rfl
  have hgper : IsZ2Periodic g := by
    have hper := hsol.2.1 0 le_rfl
    rw [← hinit]
    exact hper
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hKnonneg : 0 ≤ K := hKpos.le
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    apply intervalIntegral.integral_nonneg zero_le_one
    intro t ht
    exact integral_nonneg (fun x => vecNormSq_nonneg _)
  have hSnonneg : 0 ≤ S := by dsimp [S]; positivity
  have hPoincare : Real.sqrt (l2NormSq g) ≤
      Real.sqrt 3 * (Real.sqrt κ)⁻¹ * S := by
    have hmeanBound := classical_meanZero_initial_l2_le hb hdiv hsol hκ hκ1 hmean
    simpa [S, D] using hmeanBound
  have hLow : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in unitCell 2,
        (orderedRealDerivative w
          (lowProjection g (M)) x) ^ 2) ≤
        2 * Real.exp 1 * (A / r) ^ w.length * S := by
    intro w hw
    have hspec := lowProjection_orderedDerivative_l2_le
      (g := g) w hw (M)
    have htrace := classical_lowProjection_trace_bound
      (M) hb hdiv hX hDb
      (by simpa [K] using hmax) hB hκ hM hsol
      (hg.of_le (by norm_num)) hgper
    have hfirst : Real.sqrt (∫ x in unitCell 2,
        (orderedRealDerivative w (lowProjection g (M)) x) ^ 2) ≤
        K ^ (w.length - 1) *
          (2 * Real.exp 1 * K * Real.sqrt κ * Real.sqrt D) := by
      exact hspec.trans (mul_le_mul_of_nonneg_left htrace
        (pow_nonneg hKnonneg _))
    have hpow : K ^ (w.length - 1) * K = K ^ w.length := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      _ ≤ K ^ (w.length - 1) *
          (2 * Real.exp 1 * K * Real.sqrt κ * Real.sqrt D) := hfirst
      _ = 2 * Real.exp 1 * K ^ w.length * S := by
        dsimp [S]
        rw [← hpow]
        ring
      _ ≤ 2 * Real.exp 1 * (A / r) ^ w.length * S := by
        calc
          2 * Real.exp 1 * K ^ w.length * S =
              (2 * Real.exp 1) * (K ^ w.length * S) := by ring
          _ ≤ (2 * Real.exp 1) * ((A / r) ^ w.length * S) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ hKnonneg hKup _) hSnonneg) (by positivity)
          _ = 2 * Real.exp 1 * (A / r) ^ w.length * S := by ring
  have hgeom : e44TailExponent * R * (A / r) ≤
      R * (M + 1 : ℝ) / 1024 := by
    have hgeom0 : e44TailExponent * (A / r) ≤
        (M + 1 : ℝ) / 1024 := by
      calc
        e44TailExponent * (A / r) ≤
            e44TailExponent *
              (2 * Real.pi * Real.sqrt 2 *
                (M + 1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hKlow e44_tail_exponent_pos.le
        _ = (M + 1 : ℝ) / 1024 := by
          dsimp [e44TailExponent]
          field_simp
          ring
    calc
      e44TailExponent * R * (A / r) =
          R * (e44TailExponent * (A / r)) := by ring
      _ ≤ R * ((M + 1 : ℝ) / 1024) :=
        mul_le_mul_of_nonneg_left hgeom0 hR.le
      _ = R * (M + 1 : ℝ) / 1024 := by ring
  have hHigh : ∀ w : List (Fin 2), 1 ≤ w.length →
      Real.sqrt (∫ x in unitCell 2,
        (orderedRealDerivative w
          (highRemainder g (M)) x) ^ 2) ≤
        e44TailConstant * (w.length.factorial : ℝ) *
          (e44TailConstant / R) ^ w.length *
          Real.exp (-e44TailExponent * R * (A / r)) *
          Real.sqrt (l2NormSq g) := by
    intro w hw
    exact TraceInstanceCutoff.e44_high_remainder_bound_for_combination M hR hgeom
      hg hgper hθ hTailScale w hw
  have hcombined := e44_initialTrace_of_spectral_piece_bounds
    (g := g) (r := r) (R := R) (A := A) (ν := κ)
    (S := S) (N := Real.sqrt (l2NormSq g)) (Cₚ := Real.sqrt 3)
    (Cₜ := e44TailConstant) (c := e44TailExponent)
    M hg hr hRr hA hκ hSnonneg (Real.sqrt_nonneg _)
    (by positivity) (by norm_num [e44TailConstant]) hAbsorb hPoincare
    hLow hHigh
  let Ctr := e44TraceCombinationConstant A (Real.sqrt 3) e44TailConstant
  change ∀ w : List (Fin 2), 1 ≤ w.length →
    Real.sqrt (∫ x in unitCube,
      (Infra.Section4.classicalWordDerivative w g x) ^ 2) ≤
    (Real.sqrt κ * Real.sqrt
      (∫ t in (0 : ℝ)..1, classicalCellGradientEnergy u t)) *
      ((w.length.factorial : ℝ) / (r / Ctr ^ 2) ^ w.length)
  intro w hw
  simpa [S, D, Ctr] using hcombined w hw

end AVenhance.Infra.Section5.RelativeError

end
