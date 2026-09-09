/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FamilyNormTime
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.MetricPathConvergence

@[expose] public section

/-! Actual finite weighted forcing norms in the Bochner time space. -/

noncomputable section

namespace EulerWeightedForcingTime

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution EulerFamilyNormTime
  EulerFiniteMetricEnergy
open scoped Topology

variable {A I H : Type*} [Fintype A] [Fintype I] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Multiplication by a continuous scalar time weight as a genuine Bochner operator. -/
def scalarTimeMultiplier (T : ℝ) (hT : 0 ≤ T) (w : C(Icc (0 : ℝ) T, ℝ)) : TimeLp T ℝ →L[ℝ] TimeLp T
  ℝ :=
  timeMultiplier T hT (⟨fun t => w t • ContinuousLinearMap.id ℝ ℝ,
    w.continuous.smul continuous_const⟩ : C(Icc (0 : ℝ) T, ℝ →L[ℝ] ℝ))

/-- The actual scalar multiplier has its literal weighted representative. -/
theorem scalarTimeMultiplier_ae (T : ℝ) (hT : 0 ≤ T) (w : C(Icc (0 : ℝ) T, ℝ)) (u : TimeLp T ℝ) :
    (scalarTimeMultiplier T hT w u : ℝ → ℝ) =ᵐ[timeMeasure T] fun t => extendPath T hT w t * u t :=
      by
  exact timeMultiplier_ae T hT
    (⟨fun t => w t • ContinuousLinearMap.id ℝ ℝ, w.continuous.smul continuous_const⟩ :
      C(Icc (0 : ℝ) T, ℝ →L[ℝ] ℝ)) u

/-- The genuine finite weighted sum of actual forcing norms represented in L² time. -/
def weightedForcingTime (T : ℝ) (hT : 0 ≤ T) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : A → TimeLp T (I → H)) : TimeLp T ℝ :=
  ∑ i, scalarTimeMultiplier T hT (w i) (familyNormTime T (F i))

/-- The actual Bochner forcing sum is the literal finite weighted family norm almost everywhere. -/
theorem weightedForcingTime_ae (T : ℝ) (hT : 0 ≤ T) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : A → TimeLp T (I → H)) :
    (weightedForcingTime T hT w F : ℝ → ℝ) =ᵐ[timeMeasure T]
      fun t => ∑ i, extendPath T hT (w i) t * familyNorm (F i t) := by
  have hsingle (i : A) :
      (scalarTimeMultiplier T hT (w i) (familyNormTime T (F i)) : ℝ → ℝ) =ᵐ[timeMeasure T]
        fun t => extendPath T hT (w i) t * familyNorm (F i t) := by
    filter_upwards [scalarTimeMultiplier_ae T hT (w i) (familyNormTime T (F i)), familyNormTime_ae
      T (F i)]
      with t h1 h2
    rw [h1, h2]
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ : Finset A)
    (fun i => scalarTimeMultiplier T hT (w i) (familyNormTime T (F i))), ae_all_iff.mpr hsingle]
    with t ht hh
  rw [weightedForcingTime, ht]
  exact Finset.sum_congr rfl (fun i _ => hh i)

/-- Actual finite weighted forcing sums converge strongly with the actual L² forcing fields. -/
theorem weightedForcingTime_tendsto (T : ℝ) (hT : 0 ≤ T) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : ℕ → A → TimeLp T (I → H)) (f : A → TimeLp T (I → H))
    (hF : ∀ i, Filter.Tendsto (fun n => F n i) Filter.atTop (𝓝 (f i))) :
    Filter.Tendsto (fun n => weightedForcingTime T hT w (F n)) Filter.atTop
      (𝓝 (weightedForcingTime T hT w f)) := by
  exact tendsto_finsetSum Finset.univ (fun i _ =>
    (scalarTimeMultiplier T hT (w i)).continuous.continuousAt.tendsto.comp
      (familyNormTime_tendsto T (fun n => F n i) (f i) (hF i)))

/-- The literal weighted forcing norm along continuous time paths. -/
def weightedForcingPath (T : ℝ) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : A → C(Icc (0 : ℝ) T, I → H)) : C(Icc (0 : ℝ) T, ℝ) :=
  ∑ i, w i * ⟨fun t => familyNorm (F i t), familyNorm_lipschitz.continuous.comp (F i).continuous⟩

/-- The bundled weighted forcing path evaluates to its literal finite norm sum. -/
theorem weightedForcingPath_apply (T : ℝ) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : A → C(Icc (0 : ℝ) T, I → H)) (t : Icc (0 : ℝ) T) :
    weightedForcingPath T w F t = ∑ i, w i t * familyNorm (F i t) := by
  simp only [weightedForcingPath, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.coe_mk]

/-- Continuous forcing paths have exactly the same weighted norm in the genuine Bochner construction. -/
theorem weightedForcingTime_pathLp (T : ℝ) (hT : 0 ≤ T) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : A → C(Icc (0 : ℝ) T, I → H)) :
    weightedForcingTime T hT w (fun i => pathLp T hT (F i)) = pathLp T hT (weightedForcingPath T w
      F) := by
  apply Lp.ext
  filter_upwards [weightedForcingTime_ae T hT w (fun i => pathLp T hT (F i)),
    ae_all_iff.mpr (fun i => pathLp_ae T hT (F i)), pathLp_ae T hT (weightedForcingPath T w F)]
    with t h1 h2 h3
  rw [h1, h3]
  change (∑ i, extendPath T hT (w i) t * familyNorm (pathLp T hT (F i) t)) =
    weightedForcingPath T w F (projIcc 0 T hT t)
  rw [weightedForcingPath_apply]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun x => extendPath T hT (w i) t * familyNorm x)
    (h2 i))

end EulerWeightedForcingTime
