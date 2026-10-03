/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.FlowDnInduction.Remainder

/-! # Positive Time

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section

namespace AVenhance.FaaDiBruno

open FormalMultilinearSeries
open Homogenization
open MeasureTheory
open scoped ContDiff

theorem PositiveTime.flowDirectionalJet_id_constant (I : List (Vec 2)) (hI : I ≠ []) :
    ∃ c : Vec 2, directionalJet I (fun x : Vec 2 => x) = fun _ => c := by
  induction I with
  | nil => exact (hI rfl).elim
  | cons v I ih =>
      cases I with
      | nil =>
          refine ⟨v, ?_⟩
          funext x
          simp [directionalJet]
      | cons w I =>
          have hI' : w :: I ≠ [] := by simp
          obtain ⟨c, hc⟩ := ih hI'
          refine ⟨0, ?_⟩
          funext x
          change fderiv ℝ (directionalJet (w :: I) (fun x : Vec 2 => x)) x v = 0
          rw [hc]
          simp

theorem PositiveTime.flowOrderedPartial_id_eq_zero {n : ℕ} (hn : 2 ≤ n)
    (x : Vec 2) (I : Fin n → Fin 2) :
    orderedPartial n (fun y : Vec 2 => y) x I = 0 := by
  let V : List (Vec 2) := List.ofFn fun j => coordinateVector 2 (I j)
  have hVlen : V.length = n := by simp [V]
  have hId : ContDiff ℝ ∞ (fun y : Vec 2 => y) := by fun_prop
  have hpart := orderedPartial_eq_directionalJet
    (fun y : Vec 2 => y) hId x I
  rw [hpart]
  cases hVeq : V with
  | nil =>
      rw [hVeq] at hVlen
      have hn0 : n = 0 := hVlen.symm
      omega
  | cons v tail =>
      rw [hVeq] at hVlen
      have hV : tail ≠ [] := by
        intro hnil
        rw [hnil] at hVlen
        have hn1 : n = 1 := hVlen.symm
        omega
      obtain ⟨c, hc⟩ := PositiveTime.flowDirectionalJet_id_constant tail hV
      change directionalJet V (fun x : Vec 2 => x) x = 0
      rw [hVeq]
      change fderiv ℝ (directionalJet tail (fun x : Vec 2 => x)) x v = 0
      rw [hc]
      simp

theorem PositiveTime.flowIntegralAffinePow {t B : ℝ} (_ht : 0 ≤ t) (hB : 0 < B)
    (n : ℕ) :
    (∫ s in 0..t, (1 + B * s) ^ n) =
      ((1 + B * t) ^ (n + 1) - 1) / (B * (n + 1 : ℝ)) := by
  let P : ℝ → ℝ := fun s => (1 + B * s) ^ (n + 1) / (B * (n + 1 : ℝ))
  have hlinear (s : ℝ) : HasDerivAt (fun q : ℝ => 1 + B * q) B s := by
    have h := (hasDerivAt_const s (1 : ℝ)).add ((hasDerivAt_id s).const_mul B)
    convert h using 1
    · funext q
      simp
    · simp
  have hP (s : ℝ) : HasDerivAt P ((1 + B * s) ^ n) s := by
    have hpow := (hlinear s).pow (n + 1)
    have hdiv := hpow.div_const (B * (n + 1 : ℝ))
    have hden : B * (n + 1 : ℝ) ≠ 0 := by positivity
    convert hdiv using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one]
    field_simp [hden]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (fun s hs => hP s)
    (by
      have hcont : Continuous (fun s : ℝ => (1 + B * s) ^ n) := by fun_prop
      exact hcont.intervalIntegrable 0 t)
  rw [hFTC]
  dsimp [P]
  field_simp [ne_of_gt hB]
  ring

theorem PositiveTime.flowLinearODE_norm_bound
    {t L B K : ℝ} {n : ℕ} (ht : 0 < t) (hL : 0 ≤ L)
    (hB : 0 < B) (hK : 0 ≤ K)
    (A : ℝ → Vec 2 →L[ℝ] Vec 2) (f y : ℝ → Vec 2)
    (hAcontinuous : Continuous A) (hfcontinuous : Continuous f)
    (hycontinuous : Continuous y)
    (hAbound : ∀ s, ‖A s‖ ≤ L)
    (hfbound : ∀ s ∈ Set.Icc 0 t, ‖f s‖ ≤ K * (1 + B * s) ^ n)
    (hderiv : ∀ s ∈ Set.Icc 0 t,
      HasDerivAt y (A s (y s) + f s) s)
    (hy0 : y 0 = 0) :
    ‖y t‖ ≤ K * (((1 + B * t) ^ (n + 1) - 1) /
      (B * (n + 1 : ℝ))) * Real.exp (L * t) := by
  let hab : (0 : ℝ) ≤ t := ht.le
  let D : AVenhance.Infra.ODE.LinearODEData (E := Vec 2) 0 t hab := {
    A := A
    f := f
    y₀ := 0
    operatorBound := L
    operatorBound_nonneg := hL
    operator_aestronglyMeasurable := hAcontinuous.aestronglyMeasurable
    operator_norm_le := hAbound
    forcing_intervalIntegrable := hfcontinuous.intervalIntegrable 0 t
  }
  let u : ContinuousMap (Set.Icc (0 : ℝ) t) (Vec 2) :=
    ⟨fun s => y s, hycontinuous.comp continuous_subtype_val⟩
  have hODErhs : Continuous (fun s => A s (y s) + f s) := by fun_prop
  have hIntegral : AVenhance.Infra.ODE.IsLinearIntegralSolution A f 0 0 t y := by
    intro s hs
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := s) (f := y)
      (f' := fun r => A r (y r) + f r) (fun r hr => ?_)
      (hODErhs.intervalIntegrable 0 s)
    · have hFTC' : (∫ r in 0..s, A r (y r) + f r) = y s := by
        simpa [hy0, AVenhance.Infra.ODE.linearRhs] using hFTC
      simpa [hy0, AVenhance.Infra.ODE.linearRhs] using hFTC'.symm
    · have hr' : r ∈ Set.Icc 0 s := by
        simpa [Set.uIcc_of_le hs.1] using hr
      have hrT : r ∈ Set.Icc 0 t := ⟨hr'.1, hr'.2.trans hs.2⟩
      exact hderiv r hrT
  have huSolution : D.IsSolution u := by
    apply (D.isSolution_iff_integralSolution u).2
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) t := hs
    have hsourceEq :
        (∫ r in 0..s,
          AVenhance.Infra.ODE.linearRhs A f
            (AVenhance.Infra.ODE.extendCurve hab u) r) =
        ∫ r in 0..s, A r (y r) + f r := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Set.Icc 0 s := by
        simpa [Set.uIcc_of_le hs'.1] using hr
      have hrT : r ∈ Set.Icc (0 : ℝ) t := ⟨hr'.1, hr'.2.trans hs'.2⟩
      simp [AVenhance.Infra.ODE.linearRhs,
        AVenhance.Infra.ODE.extendCurve_eq_of_mem hab u hrT, u]
    have hFTC := hIntegral s hs'
    calc
      AVenhance.Infra.ODE.extendCurve hab u s = y s :=
        AVenhance.Infra.ODE.extendCurve_eq_of_mem hab u hs'
      _ = 0 + ∫ r in 0..s,
          AVenhance.Infra.ODE.linearRhs A f
            (AVenhance.Infra.ODE.extendCurve hab u) r := by
        rw [hsourceEq]
        simpa [hy0, AVenhance.Infra.ODE.linearRhs] using hFTC
  have hgron := AVenhance.Infra.ODE.LinearODEData.IsSolution.norm_le_gronwall
    D u huSolution t ⟨ht.le, le_rfl⟩
  have hforce :
      (∫ s in 0..t, ‖f s‖) ≤
        K * (((1 + B * t) ^ (n + 1) - 1) / (B * (n + 1 : ℝ))) := by
    have hpolyCont : Continuous (fun s : ℝ => (1 + B * s) ^ n) := by fun_prop
    have hpolyInt : IntervalIntegrable (fun s : ℝ => (1 + B * s) ^ n) volume 0 t :=
      hpolyCont.intervalIntegrable 0 t
    have hpoint : ∀ s ∈ Set.Icc 0 t,
        ‖f s‖ ≤ K * (1 + B * s) ^ n := hfbound
    have hmajor := intervalIntegral.integral_mono_on ht.le
      (hfcontinuous.norm.intervalIntegrable 0 t)
      (by simpa only [intervalIntegral.integral_const_mul] using
        hpolyInt.const_mul K)
      hpoint
    rw [intervalIntegral.integral_const_mul, PositiveTime.flowIntegralAffinePow ht.le hB] at hmajor
    exact hmajor
  have hAint : (∫ s in 0..t, ‖A s‖) ≤ L * t := by
    have h := intervalIntegral.integral_mono_on ht.le
      (hAcontinuous.norm.intervalIntegrable 0 t)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => L) volume 0 t)
      (fun s hs => hAbound s)
    simpa [mul_comm] using h
  have hexp : Real.exp (∫ s in 0..t, ‖A s‖) ≤ Real.exp (L * t) :=
    Real.exp_le_exp.mpr hAint
  calc
    ‖y t‖ = ‖AVenhance.Infra.ODE.extendCurve hab u t‖ := by
      rw [AVenhance.Infra.ODE.extendCurve_eq_of_mem hab u (t := t)
        ⟨ht.le, le_rfl⟩]
      simp [u]
    _ ≤ (‖(0 : Vec 2)‖ + ∫ s in 0..t, ‖f s‖) *
        Real.exp (∫ s in 0..t, ‖A s‖) := hgron
    _ ≤ K * (((1 + B * t) ^ (n + 1) - 1) /
        (B * (n + 1 : ℝ))) * Real.exp (L * t) := by
      rw [norm_zero, zero_add]
      have hforceNonneg : 0 ≤ K *
          (((1 + B * t) ^ (n + 1) - 1) / (B * (n + 1 : ℝ))) := by
        have hbase : 1 ≤ 1 + B * t := by
          nlinarith [mul_nonneg hB.le ht.le]
        have hpow : 1 ≤ (1 + B * t) ^ (n + 1) := one_le_pow₀ hbase
        have hnum : 0 ≤ (1 + B * t) ^ (n + 1) - 1 := by linarith
        have hden : 0 < B * (n + 1 : ℝ) := by positivity
        exact mul_nonneg hK (div_nonneg hnum hden.le)
      exact mul_le_mul hforce hexp (Real.exp_pos _).le hforceNonneg

theorem PositiveTime.flowExpOneSixteenth_le_fourThirds :
    Real.exp (1 / 16 : ℝ) ≤ 4 / 3 := by
  have h := Real.abs_exp_sub_one_le (x := (1 / 16 : ℝ)) (by norm_num)
  have hupper : Real.exp (1 / 16 : ℝ) - 1 ≤ 2 * |(1 / 16 : ℝ)| :=
    (abs_le.mp h).2
  norm_num at hupper ⊢
  linarith

private theorem flowDn_coordinate_positive_bound_scaled1 :
  ∀ {n : ℕ},
    (2 : ℕ) ≤ n →
      ∀ {C_f R_f : ℝ},
        (0 : ℝ) < C_f →
          (0 : ℝ) < R_f →
            ∀ {t : ℝ},
              let R0 : ℝ := (8 : ℝ) * (2 : ℝ) * R_f;
              let B : ℝ := (8 : ℝ) * (2 : ℝ) * C_f * R_f;
              let L : ℝ := (2 : ℝ) * C_f * R_f / (4 : ℝ);
              let Aprev : ℝ := flowHalfBinomialCoeff (n - (1 : ℕ));
              let An : ℝ := flowHalfBinomialCoeff n;
              let K : ℝ :=
                C_f * R0 ^ n / ((↑n : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * ((2 : ℝ) * (↑(n + (1 :
                    ℕ)).factorial : ℝ) * An);
              (0 : ℝ) < B →
                (0 : ℝ) ≤ K →
                  (2 : ℝ) * C_f * An * ((1 : ℝ) + B * t) / B * Real.exp (L * t) ≤ Aprev / ((2 : ℝ)
                      * R_f) →
                    let base : ℝ := (↑n.factorial : ℝ) * R0 ^ n * ((1 : ℝ) + B * t) ^ n / ((↑n :
                        ℝ) + (1 : ℝ)) ^ (2 : ℕ);
                    (0 : ℝ) ≤ base →
                      K * ((((1 : ℝ) + B * t) ^ (n + (1 : ℕ)) - (1 : ℝ)) / (B * ((↑n : ℝ) + (1 :
                          ℝ)))) *
                          Real.exp (L * t) ≤
                        Aprev / ((2 : ℝ) * R_f) * (↑n.factorial : ℝ) * (R0 * ((1 : ℝ) + B * t)) ^
                            n /
                          ((↑n : ℝ) + (1 : ℝ)) ^ (2 : ℕ)
    := by
  intro n hn C_f R_f hCf hRf t R0 B L Aprev An K hBpos hKnonneg hcoeff base hbase
  have hpow :
      (((1 + B * t) ^ (n + 1) - 1) / (B * (n + 1 : ℝ))) ≤
        (1 + B * t) ^ (n + 1) / (B * (n + 1 : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  calc
    _ ≤ K * ((1 + B * t) ^ (n + 1) /
        (B * (n + 1 : ℝ))) * Real.exp (L * t) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hKnonneg) (Real.exp_nonneg _)
    _ = base * ((2 * C_f * An * (1 + B * t) / B) * Real.exp (L * t)) := by
      dsimp [base, K, R0]
      rw [Nat.factorial_succ, mul_pow]
      push_cast
      field_simp [ne_of_gt hBpos]
      ring
    _ ≤ base * (Aprev / (2 * R_f)) :=
      mul_le_mul_of_nonneg_left hcoeff hbase
    _ = Aprev / (2 * R_f) * n.factorial *
        (R0 * (1 + B * t)) ^ n / (n + 1 : ℝ) ^ 2 := by
      dsimp [base]
      rw [show R0 = 16 * R_f by dsimp [R0]; ring]
      rw [mul_pow]
      rw [mul_pow]
      rw [show (16 : ℝ) = 2 * 8 by norm_num, mul_pow]
      have hpow16 : (2 : ℝ) ^ n * (8 : ℝ) ^ n = (16 : ℝ) ^ n := by
        rw [← mul_pow]
        norm_num
      rw [hpow16]
      ring

private theorem flowDn_coordinate_positive_bound_Ebound2 :
  ∀ {N n : ℕ},
    (2 : ℕ) ≤ n →
      n ≤ N →
        ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)},
          Infra.Flow.SmoothPeriodicField b →
            ∀ {X : ℝ → Vec (2 : ℕ) → ℝ → Vec (2 : ℕ)},
              (ContDiff ℝ ∞ fun (p : (ℝ × Vec (2 : ℕ)) × ℝ) => X p.1.1 p.1.2 p.2) →
                ∀ {C_f R_f : ℝ},
                  (0 : ℝ) < C_f →
                    (0 : ℝ) < R_f →
                      (∀ (s : ℝ) (k : ℕ), (1 : ℕ) ≤ k → k ≤ N → snorm (b s) k R_f ≤ ENNReal.ofReal
                          C_f) →
                        ∀ {t : ℝ} (I : Fin n → Fin (2 : ℕ)) (x : Vec (2 : ℕ)),
                          let Y : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ) := fun (s : ℝ) (y : Vec (2 : ℕ))
                              => X s y (0 : ℝ);
                          let R0 : ℝ := (8 : ℝ) * (2 : ℝ) * R_f;
                          let B : ℝ := (8 : ℝ) * (2 : ℝ) * C_f * R_f;
                          let An : ℝ := flowHalfBinomialCoeff n;
                          let K : ℝ :=
                            C_f * R0 ^ n / ((↑n : ℝ) + (1 : ℝ)) ^ (2 : ℕ) *
                              ((2 : ℝ) * (↑(n + (1 : ℕ)).factorial : ℝ) * An);
                          let J : ℝ → Vec (2 : ℕ) := fun (s : ℝ) => orderedPartial n (Y s) x I;
                          let CJet : ℝ → Vec (2 : ℕ) := fun (s : ℝ) =>
                            orderedPartial n (fun (y : Vec (2 : ℕ)) => b s (Y s y)) x I;
                          let A : ℝ → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) := fun (s : ℝ) => fderiv ℝ (b
                              s) (Y s x);
                          let E : ℝ → Vec (2 : ℕ) := fun (s : ℝ) => CJet s - (A s : Vec (2 : ℕ) →
                              Vec (2 : ℕ)) (J s);
                          (∀ s ∈ Set.Icc (0 : ℝ) t,
                              ∀ (k : ℕ),
                                (1 : ℕ) ≤ k →
                                  k < n →
                                    snorm (fun (y : Vec (2 : ℕ)) => X s y (0 : ℝ)) k
                                        ((8 : ℝ) * (2 : ℝ) * R_f * ((1 : ℝ) + (8 : ℝ) * (2 : ℝ) *
                                            C_f * R_f * |s|)) ≤
                                      ENNReal.ofReal (flowHalfBinomialCoeff (k - (1 : ℕ)) / ((2 :
                                          ℝ) * R_f))) →
                            ∀ s ∈ Set.Icc (0 : ℝ) t, ‖E s‖ ≤ K * ((1 : ℝ) + B * s) ^ n
    := by
  intro N n hn hnN b hb X hXsmooth C_f R_f hCf hRf hBfield t I x Y R0 B An K J CJet A E hLowerAt s
      hs
  have hrem := flowFaaRemainder_coordinate_bound hn hnN hb hXsmooth
    hCf hRf hBfield s x (hLowerAt s hs) I
  have hrem' : ‖E s‖ ≤
      C_f * (R0 * (1 + B * s)) ^ n / (n + 1 : ℝ) ^ 2 *
        (2 * ((n + 1).factorial : ℝ) * An) := by
    simpa [E, CJet, A, J, Y, R0, B, abs_of_nonneg hs.1] using hrem
  calc
    ‖E s‖ ≤
        C_f * (R0 * (1 + B * s)) ^ n / (n + 1 : ℝ) ^ 2 *
          (2 * ((n + 1).factorial : ℝ) * An) := hrem'
    _ = K * (1 + B * s) ^ n := by
      dsimp [K]
      rw [mul_pow]
      ring

/-- Pointwise closure of the order-`n` flow jet equation on positive time.
This is the exact factorial/radius comparison in the paper's induction. -/
theorem PositiveTime.flowDn_coordinate_positive_bound
    {N n : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow b X)
    (hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2))
    {C_f R_f : ℝ} (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hBfield : ∀ s k, 1 ≤ k → k ≤ N →
      snorm (b s) k R_f ≤ ENNReal.ofReal C_f)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ 1 / (8 * C_f * R_f))
    (hLower : ∀ s, 0 ≤ s → s ≤ 1 / (8 * C_f * R_f) →
      ∀ k, 1 ≤ k → k < n →
        snorm (fun y => X s y 0) k
          (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * s)) ≤
            ENNReal.ofReal (flowHalfBinomialCoeff (k - 1) / (2 * R_f)))
    (I : Fin n → Fin 2) (x : Vec 2) :
    ‖orderedPartial n (fun y => X t y 0) x I‖ ≤
      (flowHalfBinomialCoeff (n - 1) / (2 * R_f)) * n.factorial *
        (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * t)) ^ n /
          (n + 1 : ℝ) ^ 2 := by
  let Y : ℝ → Vec 2 → Vec 2 := fun s y => X s y 0
  let V : List (Vec 2) := List.ofFn fun j => coordinateVector 2 (I j)
  let R0 : ℝ := 8 * 2 * R_f
  let B : ℝ := 8 * 2 * C_f * R_f
  let L : ℝ := 2 * C_f * R_f / 4
  let Aprev : ℝ := flowHalfBinomialCoeff (n - 1)
  let An : ℝ := flowHalfBinomialCoeff n
  let K : ℝ := C_f * R0 ^ n / (n + 1 : ℝ) ^ 2 *
    (2 * ((n + 1).factorial : ℝ) * An)
  let J : ℝ → Vec 2 := fun s => orderedPartial n (Y s) x I
  let CJet : ℝ → Vec 2 := fun s =>
    orderedPartial n (fun y => b s (Y s y)) x I
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 := fun s => fderiv ℝ (b s) (Y s x)
  let E : ℝ → Vec 2 := fun s => CJet s - A s (J s)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hLnonneg : 0 ≤ L := by dsimp [L]; positivity
  have hR0 : 0 < R0 := by dsimp [R0]; positivity
  have hAnnonneg : 0 ≤ An := by
    dsimp [An]
    exact flowHalfCoeff_nonneg_of_posSize (r := n + 1) (by omega)
  have hAprevNonneg : 0 ≤ Aprev := by
    dsimp [Aprev]
    exact flowHalfCoeff_nonneg_of_posSize (r := n) (by omega)
  have hKnonneg : 0 ≤ K := by dsimp [K]; positivity
  have hYjoint : ContDiff ℝ ∞ (Function.uncurry Y) := by
    change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => X p.1 p.2 0)
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (p, (0 : ℝ))) := by fun_prop
    exact hXsmooth.comp hmap
  have hQjoint : ContDiff ℝ ∞
      (Function.uncurry (fun s y => b s (Y s y))) := by
    have hmap : ContDiff ℝ ∞
        (fun p : ℝ × Vec 2 => (p.1, Y p.1 p.2)) :=
      contDiff_fst.prodMk hYjoint
    exact hb.smooth.comp hmap
  let Kflow : ℝ × Vec 2 → Vec 2 :=
    transportSpatialJet V (Function.uncurry Y)
  let Kcomp : ℝ × Vec 2 → Vec 2 :=
    transportSpatialJet V (Function.uncurry (fun s y => b s (Y s y)))
  have hKflow : ContDiff ℝ ∞ Kflow := transportSpatialJet_contDiff V _ hYjoint
  have hKcomp : ContDiff ℝ ∞ Kcomp := transportSpatialJet_contDiff V _ hQjoint
  have hJeq : J = fun s => Kflow (s, x) := by
    funext s
    dsimp [J, Kflow]
    exact (transportSpatialJet_coordinate_eq_orderedPartial I Y hYjoint s x).symm
  have hCJetEq : CJet = fun s => Kcomp (s, x) := by
    funext s
    dsimp [CJet, Kcomp]
    exact (transportSpatialJet_coordinate_eq_orderedPartial
      I (fun r y => b r (Y r y)) hQjoint s x).symm
  have hJcontinuous : Continuous J := by
    rw [hJeq]
    exact hKflow.continuous.comp (continuous_id.prodMk continuous_const)
  have hCJetContinuous : Continuous CJet := by
    rw [hCJetEq]
    exact hKcomp.continuous.comp (continuous_id.prodMk continuous_const)
  have hD0 : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => fderiv ℝ (Function.uncurry b) p) :=
    hb.smooth.fderiv_right (by simp)
  have hDjoint : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => spatialDerivativeCLM (Function.uncurry b) p.1 p.2) := by
    have hInr : ContDiff ℝ ∞ (fun _ : ℝ × Vec 2 =>
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2) : Vec 2 →L[ℝ] (ℝ × Vec 2))) :=
      contDiff_const
    simpa [spatialDerivativeCLM] using hD0.clm_comp hInr
  have hXpath : ContDiff ℝ ∞ (fun s : ℝ => X s x 0) := by
    have hmap : ContDiff ℝ ∞ (fun s : ℝ => ((s, x), (0 : ℝ))) := by fun_prop
    exact hXsmooth.comp hmap
  have hpath : ContDiff ℝ ∞ (fun s : ℝ => (s, X s x 0)) := by
    have hid : ContDiff ℝ ∞ (fun s : ℝ => s) := by fun_prop
    exact hid.prodMk hXpath
  have hAeq (s : ℝ) : A s = spatialDerivativeCLM (Function.uncurry b) s (Y s x) := by
    rw [spatialDerivativeCLM_eq_slice (hb.smooth.of_le (by norm_num))]
  have hAcontinuous : Continuous A := by
    have hApath : A = fun s =>
        spatialDerivativeCLM (Function.uncurry b) s (X s x 0) := by
      funext s
      exact hAeq s
    rw [hApath]
    exact hDjoint.continuous.comp hpath.continuous
  have hAslice (s : ℝ) : ContDiff ℝ 1 (b s) := by
    have hmap : ContDiff ℝ 1 (fun y : Vec 2 => (s, y)) := by fun_prop
    simpa [Function.uncurry, Function.comp_def] using
      (hb.smooth.of_le (by norm_num : (1 : ℕ) ≤ ∞)).comp hmap
  have hAbound : ∀ s, ‖A s‖ ≤ L := by
    intro s
    have h := fderiv_norm_le_of_snorm_one_le (b s) (hAslice s) hRf hCf.le
      (hBfield s 1 (by norm_num) (by omega)) (Y s x)
    simpa [A, L, Y] using h
  have hEcontinuous : Continuous E := by
    dsimp [E]
    exact hCJetContinuous.sub (hAcontinuous.clm_apply hJcontinuous)
  have hJderiv (s : ℝ) (hs : s ∈ Set.Icc 0 t) :
      HasDerivAt J (A s (J s) + E s) s := by
    have hflow := flow_orderedPartial_hasDerivAt hb hX hXsmooth 0 s x I
    have hvalue : A s (J s) + E s = CJet s := by
      simp [E]
    rw [hvalue]
    simpa [J, CJet, Y] using hflow
  have hJzero : J 0 = 0 := by
    have hid : (fun y : Vec 2 => X 0 y 0) = fun y => y := by
      funext y
      exact hX.1 y 0
    change orderedPartial n (fun y : Vec 2 => X 0 y 0) x I = 0
    rw [hid]
    exact PositiveTime.flowOrderedPartial_id_eq_zero hn x I
  have hLowerAt (s : ℝ) (hs : s ∈ Set.Icc 0 t) :
      ∀ k, 1 ≤ k → k < n →
        snorm (fun y => X s y 0) k
          (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |s|)) ≤
            ENNReal.ofReal (flowHalfBinomialCoeff (k - 1) / (2 * R_f)) := by
    intro k hk1 hkn
    have hk := hLower s hs.1 (le_trans hs.2 htT) k hk1 hkn
    simpa [abs_of_nonneg hs.1] using hk
  have hEbound (s : ℝ) (hs : s ∈ Set.Icc 0 t) :
      ‖E s‖ ≤ K * (1 + B * s) ^ n := by
    exact @flowDn_coordinate_positive_bound_Ebound2 N n hn hnN b hb X hXsmooth C_f R_f hCf hRf
        hBfield t I x hLowerAt s hs
  have hode := PositiveTime.flowLinearODE_norm_bound ht hLnonneg hBpos hKnonneg
    A E J hAcontinuous hEcontinuous hJcontinuous hAbound
    (fun s hs => hEbound s hs) hJderiv hJzero
  have hrec0 := flowHalfBinomialCoeff_succ (n - 1)
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  rw [hnsub] at hrec0
  have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hncast] at hrec0
  have hrec : An = ((n : ℝ) - 1 / 2) / (n + 1 : ℝ) * Aprev := by
    change flowHalfBinomialCoeff n =
      ((n : ℝ) - 1 / 2) / (n + 1 : ℝ) * flowHalfBinomialCoeff (n - 1)
    convert hrec0 using 1; ring
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hqnonneg : 0 ≤ ((n : ℝ) - 1 / 2) / (n + 1 : ℝ) := by
    apply div_nonneg
    · linarith
    · positivity
  have hqle : ((n : ℝ) - 1 / 2) / (n + 1 : ℝ) ≤ 1 := by
    rw [div_le_one₀ (by positivity)]
    nlinarith [show (2 : ℝ) ≤ n by exact_mod_cast hn]
  have hAnle : An ≤ Aprev := by
    calc
      An = ((n : ℝ) - 1 / 2) / (n + 1 : ℝ) * Aprev := hrec
      _ ≤ 1 * Aprev := mul_le_mul_of_nonneg_right hqle hAprevNonneg
      _ = Aprev := one_mul _
  have hBT : B * t ≤ 2 := by
    calc
      B * t = (16 * C_f * R_f) * t := by dsimp [B]; ring
      _ ≤ (16 * C_f * R_f) * (1 / (8 * C_f * R_f)) :=
        mul_le_mul_of_nonneg_left htT (by positivity)
      _ = 2 := by field_simp [ne_of_gt hCf, ne_of_gt hRf]; ring
  have h1Bt : 0 ≤ 1 + B * t ∧ 1 + B * t ≤ 3 := by
    constructor <;> nlinarith [hBT]
  have hLt : L * t ≤ 1 / 16 := by
    calc
      L * t = (C_f * R_f / 2) * t := by dsimp [L]; ring
      _ ≤ (C_f * R_f / 2) * (1 / (8 * C_f * R_f)) :=
        mul_le_mul_of_nonneg_left htT (by positivity)
      _ = 1 / 16 := by field_simp [ne_of_gt hCf, ne_of_gt hRf]; ring
  have hExp : Real.exp (L * t) ≤ 4 / 3 :=
    (Real.exp_le_exp.mpr hLt).trans PositiveTime.flowExpOneSixteenth_le_fourThirds
  have hprod : An * (1 + B * t) * Real.exp (L * t) ≤ 4 * Aprev := by
    calc
      An * (1 + B * t) * Real.exp (L * t) ≤
          Aprev * (1 + B * t) * Real.exp (L * t) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hAnle h1Bt.1) (Real.exp_nonneg _)
      _ ≤ Aprev * 3 * Real.exp (L * t) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1Bt.2 hAprevNonneg) (Real.exp_nonneg _)
      _ ≤ Aprev * 3 * (4 / 3) :=
            mul_le_mul_of_nonneg_left hExp (by positivity)
      _ = 4 * Aprev := by ring
  have hcoeff :
      (2 * C_f * An * (1 + B * t) / B) * Real.exp (L * t) ≤
        Aprev / (2 * R_f) := by
    calc
      _ = (An * (1 + B * t) * Real.exp (L * t)) / (8 * R_f) := by
        dsimp [B]
        field_simp [ne_of_gt hCf, ne_of_gt hRf]
      _ ≤ (4 * Aprev) / (8 * R_f) :=
        div_le_div_of_nonneg_right hprod (by positivity)
      _ = Aprev / (2 * R_f) := by ring
  let base : ℝ := n.factorial * R0 ^ n * (1 + B * t) ^ n /
    (n + 1 : ℝ) ^ 2
  have hbase : 0 ≤ base := by dsimp [base]; positivity
  have hscaled :
      K * (((1 + B * t) ^ (n + 1) - 1) /
        (B * (n + 1 : ℝ))) * Real.exp (L * t) ≤
      Aprev / (2 * R_f) * n.factorial *
        (R0 * (1 + B * t)) ^ n / (n + 1 : ℝ) ^ 2 := by
    exact @flowDn_coordinate_positive_bound_scaled1 n hn C_f R_f hCf hRf t hBpos hKnonneg hcoeff
        hbase
  exact hode.trans hscaled

/-- The positive-time seminorm induction in `p.ODE.flow.2`, retaining the
paper's coefficient at every derivative order. -/
theorem flow_spatialDn_snorm_positive
    {N : ℕ} (hN : 1 ≤ N)
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2))
    {C_f R_f : ℝ} (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hBfield : ∀ s k, 1 ≤ k → k ≤ N →
      snorm (b s) k R_f ≤ ENNReal.ofReal C_f) :
    ∀ n, 1 ≤ n → n ≤ N → ∀ t, 0 ≤ t → t ≤ 1 / (8 * C_f * R_f) →
      snorm (fun y => X t y 0) n
        (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * t)) ≤
          ENNReal.ofReal (flowHalfBinomialCoeff (n - 1) / (2 * R_f)) := by
  have hOrder : ∀ n, 1 ≤ n → n ≤ N → ∀ t, 0 ≤ t →
      t ≤ 1 / (8 * C_f * R_f) →
        snorm (fun y => X t y 0) n
          (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * t)) ≤
            ENNReal.ofReal (flowHalfBinomialCoeff (n - 1) / (2 * R_f)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn hnN t ht0 htT
        by_cases hn1 : n = 1
        · subst n
          have htAbs : |t| = t := abs_of_nonneg ht0
          have hbase := flow_spatialFirstOrder_snorm_Dn_base hN hb hX hCf hRf
            hBfield (t := t) (by rw [htAbs]; exact htT)
          have hcoef : (1 / (2 * 2 * R_f) : ℝ) =
              flowHalfBinomialCoeff 0 / (2 * R_f) := by
            norm_num [flowHalfBinomialCoeff]
            field_simp [ne_of_gt hRf]
            ring
          rw [hcoef] at hbase
          simpa [htAbs] using hbase
        · have hn2 : 2 ≤ n := by omega
          have hLower : ∀ s, 0 ≤ s → s ≤ 1 / (8 * C_f * R_f) →
              ∀ k, 1 ≤ k → k < n →
                snorm (fun y => X s y 0) k
                  (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * s)) ≤
                    ENNReal.ofReal (flowHalfBinomialCoeff (k - 1) / (2 * R_f)) := by
            intro s hs0 hsT k hk hkn
            have hkN : k ≤ N := (Nat.le_of_lt hkn).trans hnN
            exact ih k hkn hk hkN s hs0 hsT
          let Rflow : ℝ := 8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * t)
          have hRflow : 0 < Rflow := by dsimp [Rflow]; positivity
          have hAnprev : 0 ≤ flowHalfBinomialCoeff (n - 1) :=
            flowHalfCoeff_nonneg_of_posSize (r := n) (by omega)
          have hpoint : ∀ I : Fin n → Fin 2, ∀ x,
              ‖orderedPartial n (fun y => X t y 0) x I‖ ≤
                (flowHalfBinomialCoeff (n - 1) / (2 * R_f)) * n.factorial *
                  Rflow ^ n / (n + 1 : ℝ) ^ 2 := by
            intro I x
            by_cases htzero : t = 0
            · subst t
              have hid : (fun y : Vec 2 => X 0 y 0) = fun y => y := by
                funext y
                exact hX.1 y 0
              rw [hid, PositiveTime.flowOrderedPartial_id_eq_zero hn2 x I]
              have hcoef : 0 ≤
                  flowHalfBinomialCoeff (n - 1) / (2 * R_f) * n.factorial *
                    Rflow ^ n / (n + 1 : ℝ) ^ 2 := by positivity
              simpa using hcoef
            · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
              have h := PositiveTime.flowDn_coordinate_positive_bound hn2 hnN hb hX hXsmooth
                hCf hRf hBfield htpos htT hLower I x
              simpa [Rflow] using h
          have hD := derivativeSup_le_of_orderedPartial_pointwise
            (fun y => X t y 0) hpoint
          have hD' : derivativeSup n (fun y => X t y 0) ≤
              ENNReal.ofReal
                ((flowHalfBinomialCoeff (n - 1) / (2 * R_f)) * Rflow ^ n *
                  n.factorial / (n + 1 : ℝ) ^ 2) := by
            have hCeq :
                (flowHalfBinomialCoeff (n - 1) / (2 * R_f)) * n.factorial *
                    Rflow ^ n / (n + 1 : ℝ) ^ 2 =
                  (flowHalfBinomialCoeff (n - 1) / (2 * R_f)) * Rflow ^ n *
                    n.factorial / (n + 1 : ℝ) ^ 2 := by ring
            rw [hCeq] at hD
            exact hD
          simpa [Rflow] using
            (snorm_le_of_derivativeSup_le (fun y => X t y 0) hRflow hD')
  exact hOrder

end AVenhance.FaaDiBruno

end
