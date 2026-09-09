/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import LeanPool.NavierStokesAndEuler.Euler.ContinuousForcingTranslation

/-!
# Continuous ordinary forcing jets supply the Bochner hypotheses

On the compact time interval, continuous actual spatial L² jets are
automatically square integrable. The continuous and Bochner orbit theorems
therefore use the same concrete forcing data.
-/

@[expose] public section


noncomputable section

namespace EulerContinuousForcing

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerTimeLp EulerVolterraConvolution

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem spatialJets_memLp (T : ℝ) (hT : 0 ≤ T) (A : ℝ → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t : Icc (0 : ℝ) T => (A t).jetLp n)) (n : ℕ) :
    MemLp (fun t => (A t).jetLp n) 2 (timeMeasure T) := by
  let J : C(Icc (0 : ℝ) T,L2Space (Space [×n]→L[ℝ] V)) :=
    spatialJetPath (fun t : Icc (0 : ℝ) T => A t) hA n
  apply (path_memLp T hT J).ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change (A (projIcc 0 T hT t)).jetLp n = (A t).jetLp n
  rw [projIcc_of_mem hT ht]

theorem forcing_representation (T : ℝ) (hT : 0 ≤ T) (A : ℝ → SmoothL2Field V)
    (fC : C(Icc (0 : ℝ) T, L2Space V)) (hC : ∀ t, fC t = (A t).toLp)
    (f : TimeLp T (L2Space V))
    (hf : (f : ℝ → L2Space V) =ᵐ[timeMeasure T] extendPath T hT fC) :
    (f : ℝ → L2Space V) =ᵐ[timeMeasure T] fun t => (A t).toLp := by
  filter_upwards [hf, ae_restrict_mem measurableSet_Icc] with t ht hmem
  rw [ht]
  change fC (projIcc 0 T hT t) = (A t).toLp
  rw [hC, projIcc_of_mem hT hmem]

end EulerContinuousForcing
