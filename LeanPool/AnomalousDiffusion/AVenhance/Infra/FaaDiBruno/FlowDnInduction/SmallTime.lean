/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.FlowDnInduction.PositiveTime

/-! # Small Time

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section

namespace AVenhance.FaaDiBruno

open FormalMultilinearSeries
open Homogenization
open MeasureTheory
open scoped ContDiff

/-- Vector field obtained by reversing time and negating the velocity. -/
def SmallTime.flowDnReverseField (b : ℝ → Vec 2 → Vec 2) :
    ℝ → Vec 2 → Vec 2 := fun t x => -b (-t) x

/-- Flow obtained by reversing both its observation time and its starting time. -/
def SmallTime.flowDnReverseFlow (X : ℝ → Vec 2 → ℝ → Vec 2) :
    ℝ → Vec 2 → ℝ → Vec 2 := fun t x s => X (-t) x (-s)

theorem SmallTime.flowDnReverseField_smoothPeriodic
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b) :
    AVenhance.Infra.Flow.SmoothPeriodicField (SmallTime.flowDnReverseField b) := by
  refine ⟨?_, ?_⟩
  · change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => -Function.uncurry b (-p.1, p.2))
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (-p.1, p.2)) := by fun_prop
    exact contDiff_neg.comp (hb.smooth.comp hmap)
  · intro m k t x
    have h := hb.periodic (-m) k (-t) x
    simpa [SmallTime.flowDnReverseField, neg_add, add_comm] using congrArg Neg.neg h

theorem SmallTime.flowDnReverseFlow_isFlow
    {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow b X) :
    AVenhance.IsFlow (SmallTime.flowDnReverseField b) (SmallTime.flowDnReverseFlow X) := by
  constructor
  · intro x s
    exact hX.1 x (-s)
  · intro x s t
    have hbase : HasDerivAt (fun r => X r x (-s))
        (b (0 - t) (X (0 - t) x (-s))) (0 - t) := by
      simpa only [zero_sub] using hX.2 x (-s) (-t)
    simpa only [SmallTime.flowDnReverseField, SmallTime.flowDnReverseFlow, zero_sub] using
      hbase.comp_const_sub 0 t

theorem SmallTime.flowDn_snorm_neg_eq {n : ℕ} {R : ℝ} (f : Vec 2 → Vec 2) :
    snorm (fun x => -f x) n R = snorm f n R := by
  have hpartial (I : Fin n → Fin 2) :
      partialSup n (fun x => -f x) I = partialSup n f I := by
    unfold partialSup
    rw [eLpNormEssSup_eq_essSup_enorm, eLpNormEssSup_eq_essSup_enorm]
    apply essSup_congr_ae
    filter_upwards with x
    have h : orderedPartial n (fun x => -f x) x I = -orderedPartial n f x I := by
      change iteratedFDeriv ℝ n
        (fun z : VecOne 2 => -f ((vecOneEquiv 2) z)) (WithLp.toLp 1 x)
          (fun j => coordinateVectorOne 2 (I j)) =
        -iteratedFDeriv ℝ n
          (fun z : VecOne 2 => f ((vecOneEquiv 2) z)) (WithLp.toLp 1 x)
            (fun j => coordinateVectorOne 2 (I j))
      rw [show (fun z : VecOne 2 => -f ((vecOneEquiv 2) z)) =
        -(fun z : VecOne 2 => f ((vecOneEquiv 2) z)) by rfl, iteratedFDeriv_neg]
      rfl
    rw [h]
    simp
  have hderiv : derivativeSup n (fun x => -f x) = derivativeSup n f := by
    unfold derivativeSup
    apply le_antisymm
    · apply iSup_le
      intro I
      rw [hpartial I]
      exact le_iSup_of_le I le_rfl
    · apply iSup_le
      intro I
      rw [← hpartial I]
      exact le_iSup_of_le I le_rfl
  unfold snorm
  rw [hderiv]

/-- The signed-time version of the paper's all-order flow seminorm estimate.
Time reversal preserves both the field hypotheses and the exact coefficient. -/
theorem flow_spatialDn_snorm_smallTime
    {N : ℕ} (hN : 1 ≤ N)
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2))
    {C_f R_f : ℝ} (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hBfield : ∀ s k, 1 ≤ k → k ≤ N →
      snorm (b s) k R_f ≤ ENNReal.ofReal C_f)
    {t : ℝ} (ht : |t| ≤ 1 / (8 * C_f * R_f))
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    snorm (fun y => X t y 0) n
      (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)) ≤
        ENNReal.ofReal (flowHalfBinomialCoeff (n - 1) / (2 * R_f)) := by
  by_cases ht0 : 0 ≤ t
  · have h := flow_spatialDn_snorm_positive hN hb hX hXsmooth hCf hRf hBfield
      n hn hnN t ht0 (by simpa [abs_of_nonneg ht0] using ht)
    simpa [abs_of_nonneg ht0] using h
  · let br := SmallTime.flowDnReverseField b
    let Xr := SmallTime.flowDnReverseFlow X
    have hbr : AVenhance.Infra.Flow.SmoothPeriodicField br :=
      SmallTime.flowDnReverseField_smoothPeriodic hb
    have hXr : AVenhance.IsFlow br Xr := SmallTime.flowDnReverseFlow_isFlow hX
    have hXrSmooth : ContDiff ℝ ∞
        (fun p : (ℝ × Vec 2) × ℝ => Xr p.1.1 p.1.2 p.2) := by
      change ContDiff ℝ ∞ (fun p : (ℝ × Vec 2) × ℝ => X (-p.1.1) p.1.2 (-p.2))
      have hmap : ContDiff ℝ ∞
          (fun p : (ℝ × Vec 2) × ℝ => ((-p.1.1, p.1.2), -p.2)) := by fun_prop
      exact hXsmooth.comp hmap
    have hBrev : ∀ s k, 1 ≤ k → k ≤ N →
        snorm (br s) k R_f ≤ ENNReal.ofReal C_f := by
      intro s k hk hkN
      calc
        snorm (br s) k R_f = snorm (b (-s)) k R_f := by
          dsimp [br, SmallTime.flowDnReverseField]
          exact SmallTime.flowDn_snorm_neg_eq (b (-s))
        _ ≤ ENNReal.ofReal C_f := hBfield (-s) k hk hkN
    have htneg : t ≤ 0 := le_of_not_ge ht0
    have hs0 : 0 ≤ -t := neg_nonneg.mpr htneg
    have hsT : -t ≤ 1 / (8 * C_f * R_f) := by
      simpa [abs_of_nonpos htneg] using ht
    have h := flow_spatialDn_snorm_positive hN hbr hXr hXrSmooth
      hCf hRf hBrev n hn hnN (-t) hs0 hsT
    simpa [Xr, SmallTime.flowDnReverseFlow, abs_of_nonpos htneg] using h

/-- Consumed form of Proposition `p.ODE.flow.2` in dimension two. The
joint-smoothness witness is explicit until the flow regularity is
established. -/
theorem flow_spatialGradient_snorm_paper
    {N n : ℕ} (hn : 1 ≤ n) (hnN : n + 1 ≤ N)
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2))
    {C_f R_f : ℝ} (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hBfield : ∀ s k, 1 ≤ k → k ≤ N →
      snorm (b s) k R_f ≤ ENNReal.ofReal C_f)
    {t : ℝ} (ht : |t| ≤ 1 / (8 * C_f * R_f)) :
    snorm (spatialGradientMatrix (fun y => X t y 0)) n
      (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)) ≤ ENNReal.ofReal 12 := by
  have hDn := flow_spatialDn_snorm_smallTime (by omega) hb hX hXsmooth
    hCf hRf hBfield ht (n + 1) (by omega) hnN
  exact flow_spatialGradient_snorm_of_flowDn hn hX hXsmooth hCf hRf ht hDn

end AVenhance.FaaDiBruno

end
