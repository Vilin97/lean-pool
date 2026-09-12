/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownTermFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderLinearTermBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownDecomposition
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceScales

/-! Same-radius estimates for the fifteen actual forcing families, before and after angular
projection. -/

section

/-! Bounds on the actual masked slow and fast products, with zero terms charged no shifts. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.PrefixBound

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerParameterWordGevrey

variable {P T : ℝ} [Fact (0 < P)] {p : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T p a} {hT : 0 ≤ T} {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (BF : PrefixBound F hT S R) {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

include BF

theorem maskedSlow_bound (l r : KnownPiece) (i j n : ℕ) {raw : VectorField} (W : Field P T raw)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t, (x, θ)) = if i + j = n then
      slowAdvection (O.inverseFrame (t, (x, θ))) (l.jet O p a (t, (x, θ)) i) (r.jet O p a (t, (x,
          θ)) j)
          else 0)
    (b : C(Icc (0 : ℝ) T, ℝ)) (hb : ∀ t, 0 < b t)
    (hR : 0 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hprofile : i + j = n → l.active p i → r.active p j →
      ∀ t, l.profile S i t * r.profile S j t ≤ b t) :
    (W.normalized hT b hb).WordBound 6 R BC.slowCost
      (if i+j=n ∧ l.active p i ∧ r.active p j then l.shift i+r.shift j+1 else 0) := by
  by_cases hactive : i+j=n ∧ l.active p i ∧ r.active p j
  · have hbound := BC.slow_bound (F.pieceJet O l i) (F.pieceJet O r j) hT
      (l.profile S i) (r.profile S j) b (l.profile_pos S i) (r.profile_pos S j) hb
      (BF.pieceJet hR O l i) (BF.pieceJet hR O r j) hR hRc
      (hprofile hactive.1 hactive.2.1 hactive.2.2)
    have ht := hbound.normalized_of_raw_eq W hT b hb (fun t x θ => by
      rw [he t x θ,ite_eq_left hactive.1])
    simpa only [ite_eq_left hactive] using ht
  · have hz : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = 0 := by
      intro t x θ
      rw [he t x θ]
      by_cases hn : i+j=n
      · rw [ite_eq_left hn]
        by_cases hl : l.active p i
        · have hr : ¬ r.active p j := fun hr => hactive ⟨hn,hl,hr⟩
          rw [r.jet_zero_of_inactive O p a (t,(x,θ)) j hr,map_zero]
        · rw [l.jet_zero_of_inactive O p a (t,(x,θ)) i hl,map_zero,LinearMap.zero_apply]
      · rw [ite_eq_right hn]
    have ht := (Field.wordBound_normalized_of_zero W hz hT b hb 6 R 0).mono_amplitude hR
        BC.slowCost_nonneg
    simpa only [ite_eq_right hactive] using ht

theorem maskedFast_bound (l r : KnownPiece) (i j n : ℕ) {raw : VectorField} (W : Field P T raw)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t, (x, θ)) = if i + j = n then
      fastAdvection (O.normal (t, (x, θ))) (l.jet O p a (t, (x, θ)) i) (r.jet O p a (t, (x, θ)) j)
          else 0)
    (b : C(Icc (0 : ℝ) T, ℝ)) (hb : ∀ t, 0 < b t)
    (hR : 0 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hprofile : i + j = n → l.active p i → r.active p j →
      ∀ t, l.profile S i t * r.profile S j t ≤ b t) :
    (W.normalized hT b hb).WordBound 6 R BC.fastCost
      (if i+j=n ∧ l.active p i ∧ r.active p j then l.shift i+r.shift j+1 else 0) := by
  by_cases hactive : i+j=n ∧ l.active p i ∧ r.active p j
  · have hbound := BC.fast_bound (F.pieceJet O l i) (F.pieceJet O r j) hT
      (l.profile S i) (r.profile S j) b (l.profile_pos S i) (r.profile_pos S j) hb
      (BF.pieceJet hR O l i) (BF.pieceJet hR O r j) hR hRc
      (hprofile hactive.1 hactive.2.1 hactive.2.2)
    have ht := hbound.normalized_of_raw_eq W hT b hb (fun t x θ => by
      rw [he t x θ,ite_eq_left hactive.1])
    simpa only [ite_eq_left hactive] using ht
  · have hz : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = 0 := by
      intro t x θ
      rw [he t x θ]
      by_cases hn : i+j=n
      · rw [ite_eq_left hn]
        by_cases hl : l.active p i
        · have hr : ¬ r.active p j := fun hr => hactive ⟨hn,hl,hr⟩
          rw [r.jet_zero_of_inactive O p a (t,(x,θ)) j hr,map_zero]
        · rw [l.jet_zero_of_inactive O p a (t,(x,θ)) i hl,map_zero,LinearMap.zero_apply]
      · rw [ite_eq_right hn]
    have ht := (Field.wordBound_normalized_of_zero W hz hT b hb 6 R 0).mono_amplitude hR
        BC.fastCost_nonneg
    simpa only [ite_eq_right hactive] using ht

end EulerPacketCylinderField.PrefixBound

end
end

end

section

/-! Every nonzero known summand fits strictly below its target forcing shift. -/

@[expose] public section

namespace EulerPacketCylinderField.KnownTerm

open EulerPacketShiftArithmetic

/-- Budget shift as an element of `ℕ`. -/
def budgetShift (k : KnownTerm) (p i j : ℕ) : ℕ :=
  match k with
  | .previousLinear | .previousPressure => if i=0 ∧ j=0 then highShift (p-1) else 0
  | .slow l r => if i+j=p ∧ l.active p i ∧ r.active p j then l.shift i+r.shift j+1 else 0
  | .fastMeanHigh =>
      if i+j=p+1 ∧ KnownPiece.mean.active p i ∧ KnownPiece.high.active p j then
        KnownPiece.mean.shift i+KnownPiece.high.shift j+1 else 0
  | .fastMeanCorrector =>
      if i+j=p+1 ∧ KnownPiece.mean.active p i ∧ KnownPiece.corrector.active p j then
        KnownPiece.mean.shift i+KnownPiece.corrector.shift j+1 else 0
  | .fastCorrectorHigh =>
      if i+j=p+1 ∧ KnownPiece.corrector.active p i ∧ KnownPiece.high.active p j then
        KnownPiece.corrector.shift i+KnownPiece.high.shift j+1 else 0
  | .fastCorrectorCorrector =>
      if i+j=p+1 ∧ KnownPiece.corrector.active p i ∧ KnownPiece.corrector.active p j then
        KnownPiece.corrector.shift i+KnownPiece.corrector.shift j+1 else 0

private theorem previous_shift_lt (p : ℕ) (hp : 2 ≤ p) : highShift (p-1) < meanForceShift p := by
  have h := previous_linear_room p hp
  omega

theorem budgetShift_lt_mean (k : KnownTerm) (p i j : ℕ) (hp : 2 ≤ p)
    (hk : k.zeroMean = false) : k.budgetShift p i j < meanForceShift p := by
  have hpos : 0 < meanForceShift p := by have h := force_shift_dominates_grade p hp; omega
  cases k with
  | previousLinear =>
      simp only [budgetShift]
      split_ifs <;> first | exact previous_shift_lt p hp | exact hpos
  | previousPressure =>
      simp only [budgetShift]
      split_ifs <;> first | exact previous_shift_lt p hp | exact hpos
  | slow l r =>
      simp only [budgetShift]
      split_ifs with h
      · exact KnownPiece.slow_shift_room l r i j p (l.active_one_le p i h.2.1)
          (r.active_one_le p j h.2.2) h.1
      · exact hpos
  | fastMeanHigh => simp [zeroMean] at hk
  | fastMeanCorrector => simp [zeroMean] at hk
  | fastCorrectorHigh =>
      simp only [budgetShift]
      split_ifs with h
      · exact KnownPiece.fast_corrector_shift_room .high i j p h.2.1.1 h.2.2.1 h.1
      · exact hpos
  | fastCorrectorCorrector =>
      simp only [budgetShift]
      split_ifs with h
      · exact KnownPiece.fast_corrector_shift_room .corrector i j p h.2.1.1
          (KnownPiece.active_one_le .corrector p j h.2.2) h.1
      · exact hpos

theorem budgetShift_lt_high (k : KnownTerm) (p i j : ℕ) (hp : 2 ≤ p) :
    k.budgetShift p i j < highForceShift p := by
  by_cases hk : k.zeroMean = false
  · exact lt_of_lt_of_le (k.budgetShift_lt_mean p i j hp hk) (mean_force_le_high_force p)
  have hpos : 0 < highForceShift p := by have h := force_shift_dominates_grade p hp; omega
  cases k <;> simp only [zeroMean, not_true_eq_false] at hk
  all_goals simp only [budgetShift]
  all_goals split_ifs with h
  · exact KnownPiece.fast_mean_shift_room .high i j p h.2.1.1 h.2.2.1 h.1
  · exact hpos
  · exact KnownPiece.fast_mean_shift_room .corrector i j p h.2.1.1
      (KnownPiece.active_one_le .corrector p j h.2.2) h.1
  · exact hpos

end EulerPacketCylinderField.KnownTerm

end

end

section

/-! The time-profile inequalities for every surviving term of the mean and high forces. -/

@[expose] public section

namespace EulerPacketCylinderField.KnownTerm

open EulerPacketTimeProfile

variable {K : Type*} [TopologicalSpace K]

/-- Profile fits as an element of `Prop`. -/
def ProfileFits (k : KnownTerm) (S : Scales K) (p i j : ℕ) (b : C(K, ℝ)) : Prop :=
  match k with
  | .previousLinear | .previousPressure => ∀ t, S.high (p-1) t ≤ b t
  | .slow l r => i+j=p → l.active p i → r.active p j →
      ∀ t, l.profile S i t*r.profile S j t ≤ b t
  | .fastMeanHigh => i+j=p+1 → KnownPiece.mean.active p i → KnownPiece.high.active p j →
      ∀ t, KnownPiece.mean.profile S i t*KnownPiece.high.profile S j t ≤ b t
  | .fastMeanCorrector => i+j=p+1 → KnownPiece.mean.active p i → KnownPiece.corrector.active p j →
      ∀ t, KnownPiece.mean.profile S i t*KnownPiece.corrector.profile S j t ≤ b t
  | .fastCorrectorHigh => i+j=p+1 → KnownPiece.corrector.active p i → KnownPiece.high.active p j →
      ∀ t, KnownPiece.corrector.profile S i t*KnownPiece.high.profile S j t ≤ b t
  | .fastCorrectorCorrector =>
      i+j=p+1 → KnownPiece.corrector.active p i → KnownPiece.corrector.active p j →
      ∀ t, KnownPiece.corrector.profile S i t*KnownPiece.corrector.profile S j t ≤ b t

theorem mean_profile_fits (k : KnownTerm) (S : Scales K) (p i j : ℕ)
    (hp : 2 ≤ p) (hk : k.zeroMean = false) : k.ProfileFits S p i j (S.mean p) := by
  cases k with
  | previousLinear => exact S.previous_linear_mean_bound p hp
  | previousPressure => exact S.previous_linear_mean_bound p hp
  | slow l r =>
      intro hn hl hr
      exact KnownPiece.slow_profile_mean l r S i j p
        (l.active_one_le p i hl) (r.active_one_le p j hr) hn
  | fastMeanHigh => simp [zeroMean] at hk
  | fastMeanCorrector => simp [zeroMean] at hk
  | fastCorrectorHigh =>
      intro hn hl hr
      exact KnownPiece.fast_corrector_profile_mean .high S i j p (by decide) hl.1 hr.1 hn
  | fastCorrectorCorrector =>
      intro hn hl hr
      exact KnownPiece.fast_corrector_profile_mean .corrector S i j p (by decide) hl.1
        (KnownPiece.active_one_le .corrector p j hr) hn

theorem high_profile_fits (k : KnownTerm) (S : Scales K) (p i j : ℕ)
    (hk : k.meanOnly = false) : k.ProfileFits S p i j (S.high p) := by
  cases k with
  | previousLinear => exact S.high_mono (Nat.sub_le p 1)
  | previousPressure => exact S.high_mono (Nat.sub_le p 1)
  | slow l r =>
      have hnot : ¬ (l = .mean ∧ r = .mean) := by
        rintro ⟨rfl,rfl⟩
        simp [meanOnly] at hk
      intro hn hl hr
      exact KnownPiece.slow_profile_high l r S i j p
        (l.active_one_le p i hl) (r.active_one_le p j hr) hn hnot
  | fastMeanHigh =>
      intro hn hl hr
      exact KnownPiece.fast_mean_profile_high .high S i j p (by decide)
        (KnownPiece.active_one_le .mean p i hl) hr.1 hn
  | fastMeanCorrector =>
      intro hn hl hr
      exact KnownPiece.fast_mean_profile_high .corrector S i j p (by decide)
        (KnownPiece.active_one_le .mean p i hl) (KnownPiece.active_one_le .corrector p j hr) hn
  | fastCorrectorHigh =>
      intro hn hl hr
      exact KnownPiece.fast_corrector_profile_high .high S i j p (by decide) hl.1 hr.1 hn
  | fastCorrectorCorrector =>
      intro hn hl hr
      exact KnownPiece.fast_corrector_profile_high .corrector S i j p (by decide) hl.1
        (KnownPiece.active_one_le .corrector p j hr) hn

end EulerPacketCylinderField.KnownTerm

end

end

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

namespace KnownTerm

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {C : CoefficientData P T O}

/-- Amplitude as an element of `ℝ`. -/
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

/-- Mean budget shift, with branches according to `k.zeroMean`. -/
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
  (hp : 2 ≤ p) (hT : 0 < T) {correctorT : VectorField} (Ct : Field P T correctorT)
  (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
  (pressure : Field P T (pressureGradient (a (p - 1)).highPressure))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (BF : PrefixBound F hT.le S R) (BC : CoefficientBudget C)
  (hCtBound : (Ct.normalized hT.le (S.high (p - 1)) (S.high_pos (p - 1))).WordBound 6 R 1 (highShift
      (p - 1)))
  (hPressureBound : (pressure.normalized hT.le (S.high (p - 1)) (S.high_pos (p - 1))).WordBound 6 R
      1
    (highShift (p - 1)))
  (hR : 0 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)

include BF hCtBound hPressureBound hR hRc

theorem raw_term_bound (k : KnownTerm) (i j : ℕ)
    (b : C(Icc (0 : ℝ) T, ℝ)) (hb : ∀ t, 0 < b t) (hprofile : k.ProfileFits S p i j b) :
    ((F.termField C (by omega) hT Ct hCt pressure k i j).normalized hT.le b hb).WordBound
      6 R (k.amplitude BC) (k.budgetShift p i j) := by
  cases k with
  | previousLinear =>
      by_cases hij : i=0 ∧ j=0
      · have hbound := BC.previousLinear_bound hT S p b hb (F.corrector (p-1) (by omega)) Ct hCt
          (BF.corrector (p-1) (by omega) (by omega)) hCtBound hRc hprofile
        have ht := hbound.normalized_of_raw_eq (F.termField C (by
            omega) hT Ct hCt pressure .previousLinear i j)
          hT.le b hb (fun t x θ => by simp only [KnownTerm.raw,ite_eq_left hij])
        simpa only [KnownTerm.amplitude,KnownTerm.budgetShift,ite_eq_left hij] using ht
      · have hz : ∀ (t : Icc (0 : ℝ) T) x θ, KnownTerm.previousLinear.raw O p a i j (t,(x,θ)) = 0
          := by
          intro t x θ
          simp only [KnownTerm.raw,ite_eq_right hij]
        have ht := (Field.wordBound_normalized_of_zero
          (F.termField C (by
              omega) hT Ct hCt pressure .previousLinear i j) hz hT.le b hb 6 R 0).mono_amplitude
            hR BC.linearCost_nonneg
        simpa only [KnownTerm.amplitude,KnownTerm.budgetShift,ite_eq_right hij] using ht
  | previousPressure =>
      by_cases hij : i=0 ∧ j=0
      · have hbound := BC.previousPressure_bound hT S p b hb (a (p-1)).highPressure pressure
          hPressureBound hRc hprofile
        have ht := hbound.normalized_of_raw_eq (F.termField C (by
            omega) hT Ct hCt pressure .previousPressure i j)
          hT.le b hb (fun t x θ => by simp only [KnownTerm.raw,ite_eq_left hij])
        simpa only [KnownTerm.amplitude,KnownTerm.budgetShift,ite_eq_left hij] using ht
      · have hz : ∀ (t : Icc (0 : ℝ) T) x θ, KnownTerm.previousPressure.raw O p a i j (t,(x,θ)) = 0
          := by
          intro t x θ
          simp only [KnownTerm.raw,ite_eq_right hij]
        have ht := (Field.wordBound_normalized_of_zero
          (F.termField C (by
              omega) hT Ct hCt pressure .previousPressure i j) hz hT.le b hb 6 R 0).mono_amplitude
            hR BC.multiplierCost_nonneg
        simpa only [KnownTerm.amplitude,KnownTerm.budgetShift,ite_eq_right hij] using ht
  | slow l r =>
      exact BF.maskedSlow_bound BC l r i j p (F.termField C (by
          omega) hT Ct hCt pressure (.slow l r) i j)
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
    ((F.meanTermField C (by
        omega) hT Ct hCt pressure k i j).normalized hT.le (S.mean p) (S.mean_pos p)).WordBound
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
    ((F.highTermField C (by
        omega) hT Ct hCt pressure k i j).normalized hT.le (S.high p) (S.high_pos p)).WordBound
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
