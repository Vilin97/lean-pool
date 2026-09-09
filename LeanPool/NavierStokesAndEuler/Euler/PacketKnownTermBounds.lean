/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownTermFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownTermProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketMaskedProductBounds

@[expose] public section

/-! Same-radius estimates for the fifteen actual forcing families, before and after angular
  projection. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

namespace KnownTerm

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {C : CoefficientData P T O}

def amplitude (k : KnownTerm) (B : CoefficientBudget C) : ℝ :=
  match k with
  | .previousLinear => B.linearCost
  | .previousPressure => B.multiplierCost
  | .slow _ _ => B.slowCost
  | _ => B.fastCost

theorem amplitude_nonneg (k : KnownTerm) (B : CoefficientBudget C) : 0 ≤ k.amplitude B := by
  cases k <;> first
    | exact B.linearCost_nonneg
    | exact B.multiplierCost_nonneg
    | exact B.slowCost_nonneg
    | exact B.fastCost_nonneg

theorem twice_amplitude_le (k : KnownTerm) (B : CoefficientBudget C) :
    2*k.amplitude B ≤ B.termCost := by
  cases k <;> first
    | exact B.twice_linearCost_le
    | exact B.twice_multiplierCost_le
    | exact B.twice_slowCost_le
    | exact B.twice_fastCost_le

theorem amplitude_le (k : KnownTerm) (B : CoefficientBudget C) : k.amplitude B ≤ B.termCost := by
  have h := k.twice_amplitude_le B
  have h0 := k.amplitude_nonneg B
  linarith

def meanBudgetShift (k : KnownTerm) (p i j : ℕ) : ℕ := if k.zeroMean then 0 else k.budgetShift p i j

theorem meanBudgetShift_lt (k : KnownTerm) (p i j : ℕ) (hp : 2 ≤ p) :
    k.meanBudgetShift p i j < meanForceShift p := by
  by_cases hz : k.zeroMean = true
  · simp only [meanBudgetShift,ite_eq_left hz]
    have h := force_shift_dominates_grade p hp
    omega
  · simp only [meanBudgetShift,ite_eq_right hz]
    exact k.budgetShift_lt_mean p i j hp (Bool.eq_false_of_not_eq_true hz)

end KnownTerm

namespace PrefixBound

variable {P T : ℝ} [Fact (0 < P)] {p : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T p a} {O : Operators} {C : CoefficientData P T O}
  (hp : 2 ≤ p) (hT : 0 < T) {corrector_t : VectorField} (Ct : Field P T corrector_t)
  (hCt : TimeDerivative hT.le (F.corrector (p-1) (by omega)) Ct)
  (pressure : Field P T (pressureGradient (a (p-1)).highPressure))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (BF : PrefixBound F hT.le S R) (BC : CoefficientBudget C)
  (hCtBound : (Ct.normalized hT.le (S.high (p-1)) (S.high_pos (p-1))).WordBound 6 R 1 (highShift
    (p-1)))
  (hPressureBound : (pressure.normalized hT.le (S.high (p-1)) (S.high_pos (p-1))).WordBound 6 R 1
    (highShift (p-1)))
  (hR : 0 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)

include BF hCtBound hPressureBound hR hRc

theorem raw_term_bound (k : KnownTerm) (i j : ℕ)
    (b : C(Icc (0 : ℝ) T,ℝ)) (hb : ∀ t, 0 < b t) (hprofile : k.ProfileFits S p i j b) :
    ((F.termField C (by omega) hT Ct hCt pressure k i j).normalized hT.le b hb).WordBound
      6 R (k.amplitude BC) (k.budgetShift p i j) := by
  cases k with
  | previousLinear =>
      by_cases hij : i=0 ∧ j=0
      · have hbound := BC.previousLinear_bound hT S p b hb (F.corrector (p-1) (by omega)) Ct hCt
          (BF.corrector (p-1) (by omega) (by omega)) hCtBound hRc hprofile
        have ht := hbound.normalized_of_raw_eq (F.termField C (by omega) hT Ct hCt pressure
          .previousLinear i j)
          hT.le b hb (fun t x θ => by simp only [KnownTerm.raw,ite_eq_left hij])
        simpa only [KnownTerm.amplitude,KnownTerm.budgetShift,ite_eq_left hij] using ht
      · have hz : ∀ (t : Icc (0 : ℝ) T) x θ, KnownTerm.previousLinear.raw O p a i j (t,(x,θ)) = 0
        := by
          intro t x θ
          simp only [KnownTerm.raw,ite_eq_right hij]
        have ht := (Field.wordBound_normalized_of_zero
          (F.termField C (by omega) hT Ct hCt pressure .previousLinear i j) hz hT.le b hb 6 R
            0).mono_amplitude
            hR BC.linearCost_nonneg
        simpa only [KnownTerm.amplitude,KnownTerm.budgetShift,ite_eq_right hij] using ht
  | previousPressure =>
      by_cases hij : i=0 ∧ j=0
      · have hbound := BC.previousPressure_bound hT S p b hb (a (p-1)).highPressure pressure
          hPressureBound hRc hprofile
        have ht := hbound.normalized_of_raw_eq (F.termField C (by omega) hT Ct hCt pressure
          .previousPressure i j)
          hT.le b hb (fun t x θ => by simp only [KnownTerm.raw,ite_eq_left hij])
        simpa only [KnownTerm.amplitude,KnownTerm.budgetShift,ite_eq_left hij] using ht
      · have hz : ∀ (t : Icc (0 : ℝ) T) x θ, KnownTerm.previousPressure.raw O p a i j (t,(x,θ)) = 0
        := by
          intro t x θ
          simp only [KnownTerm.raw,ite_eq_right hij]
        have ht := (Field.wordBound_normalized_of_zero
          (F.termField C (by omega) hT Ct hCt pressure .previousPressure i j) hz hT.le b hb 6 R
            0).mono_amplitude
            hR BC.multiplierCost_nonneg
        simpa only [KnownTerm.amplitude,KnownTerm.budgetShift,ite_eq_right hij] using ht
  | slow l r =>
      exact BF.maskedSlow_bound BC l r i j p (F.termField C (by omega) hT Ct hCt pressure (.slow l
        r) i j)
        (fun _ _ _ => rfl) b hb hR hRc hprofile
  | fastMeanHigh =>
      exact BF.maskedFast_bound BC .mean .high i j (p+1)
        (F.termField C (by omega) hT Ct hCt pressure .fastMeanHigh i j)
        (fun _ _ _ => rfl) b hb hR hRc hprofile
  | fastMeanCorrector =>
      exact BF.maskedFast_bound BC .mean .corrector i j (p+1)
        (F.termField C (by omega) hT Ct hCt pressure .fastMeanCorrector i j)
        (fun _ _ _ => rfl) b hb hR hRc hprofile
  | fastCorrectorHigh =>
      exact BF.maskedFast_bound BC .corrector .high i j (p+1)
        (F.termField C (by omega) hT Ct hCt pressure .fastCorrectorHigh i j)
        (fun _ _ _ => rfl) b hb hR hRc hprofile
  | fastCorrectorCorrector =>
      exact BF.maskedFast_bound BC .corrector .corrector i j (p+1)
        (F.termField C (by omega) hT Ct hCt pressure .fastCorrectorCorrector i j)
        (fun _ _ _ => rfl) b hb hR hRc hprofile

theorem mean_term_bound (k : KnownTerm) (i j : ℕ) :
    ((F.meanTermField C (by omega) hT Ct hCt pressure k i j).normalized hT.le (S.mean p)
      (S.mean_pos p)).WordBound
      6 R BC.termCost (k.meanBudgetShift p i j) := by
  by_cases hz : k.zeroMean = true
  · have hzraw : ∀ (t : Icc (0 : ℝ) T) x θ, k.meanRaw O p a i j (t,(x,θ)) = 0 := by
      intro t x θ
      simp only [KnownTerm.meanRaw,ite_eq_left hz,Pi.zero_apply]
    have ht := (Field.wordBound_normalized_of_zero
      (F.meanTermField C (by omega) hT Ct hCt pressure k i j) hzraw hT.le
      (S.mean p) (S.mean_pos p) 6 R 0).mono_amplitude hR BC.termCost_nonneg
    simpa only [KnownTerm.meanBudgetShift,ite_eq_left hz] using ht
  · have hbound := raw_term_bound hp hT Ct hCt pressure BF BC hCtBound hPressureBound hR hRc
      k i j (S.mean p) (S.mean_pos p) (k.mean_profile_fits S p i j hp (Bool.eq_false_of_not_eq_true
        hz))
    have ht := (hbound.normalized_angleMean hT.le).normalized_of_raw_eq
      (F.meanTermField C (by omega) hT Ct hCt pressure k i j) hT.le (S.mean p) (S.mean_pos p)
      (fun t x θ => by simp only [KnownTerm.meanRaw,ite_eq_right hz,C.period_eq])
    have hh := ht.mono_amplitude hR (k.amplitude_le BC)
    simpa only [KnownTerm.meanBudgetShift,ite_eq_right hz] using hh

theorem high_term_bound (k : KnownTerm) (i j : ℕ) :
    ((F.highTermField C (by omega) hT Ct hCt pressure k i j).normalized hT.le (S.high p)
      (S.high_pos p)).WordBound
      6 R BC.termCost (k.budgetShift p i j) := by
  by_cases hm : k.meanOnly = true
  · have hzraw : ∀ (t : Icc (0 : ℝ) T) x θ, k.highRaw O p a i j (t,(x,θ)) = 0 := by
      intro t x θ
      simp only [KnownTerm.highRaw,ite_eq_left hm,Pi.zero_apply]
    exact (Field.wordBound_normalized_of_zero
      (F.highTermField C (by omega) hT Ct hCt pressure k i j) hzraw hT.le
      (S.high p) (S.high_pos p) 6 R (k.budgetShift p i j)).mono_amplitude hR BC.termCost_nonneg
  · have hbound := raw_term_bound hp hT Ct hCt pressure BF BC hCtBound hPressureBound hR hRc
      k i j (S.high p) (S.high_pos p) (k.high_profile_fits S p i j (Bool.eq_false_of_not_eq_true
        hm))
    by_cases hz : k.zeroMean = true
    · have ht := hbound.normalized_of_raw_eq (F.highTermField C (by omega) hT Ct hCt pressure k i j)
        hT.le (S.high p) (S.high_pos p)
        (fun t x θ => by simp only [KnownTerm.highRaw,ite_eq_right hm,ite_eq_left hz])
      exact ht.mono_amplitude hR (k.amplitude_le BC)
    · have ht := (hbound.normalized_highPart hT.le (S.high p) (S.high_pos p)).normalized_of_raw_eq
        (F.highTermField C (by omega) hT Ct hCt pressure k i j) hT.le (S.high p) (S.high_pos p)
        (fun t x θ => by simp only [KnownTerm.highRaw,ite_eq_right hm,ite_eq_right hz,C.period_eq])
      exact ht.mono_amplitude hR (k.twice_amplitude_le BC)

end PrefixBound
end EulerPacketCylinderField
