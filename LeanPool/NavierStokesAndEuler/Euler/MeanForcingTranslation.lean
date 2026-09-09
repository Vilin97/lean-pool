/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFamilyJets
public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeTranslation

@[expose] public section

/-! Actual spatial derivatives of the forcing supply the time-space translation hypotheses. -/

noncomputable section


namespace EulerMeanForcing

open MeasureTheory EulerSmoothLimit EulerLpTranslation EulerLpDerivative
  EulerTimeLp EulerTimeLpBoundedMap EulerLpSmoothFamily Filter
open scoped ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem orbitJet_memLp (T : ℝ) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T)) (n : ℕ) (a : Space) :
    MemLp (fun t => iteratedFDeriv ℝ n (fun b : Space => translation b (A t).toLp) a)
      2 (timeMeasure T) := by
  have h := ((hA n).continuousLinearMap_comp (translation (V := Space [×n]→L[ℝ] V)
    a).toContinuousLinearMap).continuousLinearMap_comp
    (multilinearBundling (P := Space) (V := V) volume n)
  exact h.ae_eq (Eventually.of_forall (fun t => (A t).iteratedFDeriv_translation_eq n a |>.symm))

def forcingFamily (T : ℝ) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T)) :
    SmoothFamily (timeMeasure T) Space (L2Space V) where
  field a t := translation a (A t).toLp
  smooth := Eventually.of_forall (fun t => (A t).translation_contDiff)
  jet n a := (orbitJet_memLp T A hA n a).toLp
    (fun t => iteratedFDeriv ℝ n (fun b : Space => translation b (A t).toLp) a)
  jet_ae n a := (orbitJet_memLp T A hA n a).coeFn_toLp
  bound n := (hA n).norm.toLp (fun t => ‖(A t).jetLp n‖)
  bounded n := by
    filter_upwards [(hA n).norm.coeFn_toLp] with t ht
    intro a
    rw [ht]
    exact (A t).norm_iteratedFDeriv_translation_le n a

theorem forcingFamily_value_eq (T : ℝ) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T))
    (f : TimeLp T (L2Space V)) (hf : f =ᵐ[timeMeasure T] fun t => (A t).toLp) (a : Space) :
    (forcingFamily T A hA).value a = timeLiftIsometry T (translation a) f := by
  apply Lp.ext
  filter_upwards [(forcingFamily T A hA).value_ae a,
    timeLift_ae T (translation a).toContinuousLinearMap f, hf] with t hv ht he
  change (forcingFamily T A hA).value a t = timeLift T (translation a).toContinuousLinearMap f t
  rw [hv, ht, he]
  rfl

/-- Smooth forcing slices with actual square-integrable spatial jets have a smooth Bochner translation orbit. -/
theorem forcing_translation_contDiff (T : ℝ) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T))
    (f : TimeLp T (L2Space V)) (hf : f =ᵐ[timeMeasure T] fun t => (A t).toLp) :
    ContDiff ℝ ∞ (fun a : Space => timeLiftIsometry T (translation a) f) := by
  have he : (fun a : Space => timeLiftIsometry T (translation a) f) = (forcingFamily T A hA).value
    :=
    funext (fun a => (forcingFamily_value_eq T A hA f hf a).symm)
  rw [he]
  exact (forcingFamily T A hA).contDiff_value

/-- The true time-space derivative norm is bounded by the original ordinary spatial jet norm, without extra factors. -/
theorem forcing_translation_jet_bound (T : ℝ) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T))
    (f : TimeLp T (L2Space V)) (hf : f =ᵐ[timeMeasure T] fun t => (A t).toLp)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => timeLiftIsometry T (translation b) f) a‖ ≤
      ‖(hA n).toLp (fun t => (A t).jetLp n)‖ := by
  have he : (fun b : Space => timeLiftIsometry T (translation b) f) = (forcingFamily T A hA).value
    :=
    funext (fun b => (forcingFamily_value_eq T A hA f hf b).symm)
  have h := (forcingFamily T A hA).norm_iteratedFDeriv_value_le n a
  have hn : ‖(forcingFamily T A hA).bound n‖ = ‖(hA n).toLp (fun t => (A t).jetLp n)‖ := by
    change ‖(hA n).norm.toLp (fun t => ‖(A t).jetLp n‖)‖ = _
    simp only [Lp.norm_toLp, eLpNorm_norm]
  exact (congrArg (fun g : Space → TimeLp T (L2Space V) =>
    ‖iteratedFDeriv ℝ n g a‖) he).trans_le (h.trans_eq hn)

end EulerMeanForcing
