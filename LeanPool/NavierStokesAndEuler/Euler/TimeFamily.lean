/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import Mathlib.Tactic.Positivity.Finset

/-! Actual finite families of continuous and Bochner time fields, with exact norm-topology
compatibility. -/

@[expose] public section


noncomputable section

namespace EulerTimeFamily

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite family of continuous time paths as the actual continuous family-valued path. -/
def familyPath (T : ℝ) (u : I → C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, I → E) :=
  ⟨fun t i => u i t, continuous_pi (fun i => (u i).continuous)⟩

omit [Fintype I] [NormedSpace ℝ E] in
/-- Bundling actual finite continuous paths is continuous in their uniform topologies. -/
theorem familyPath_continuous (T : ℝ) : Continuous (familyPath (I := I) (E := E) T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply continuous_pi
  intro i
  exact continuous_eval.comp (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)

omit [Fintype I] [NormedSpace ℝ E] in
/-- Componentwise uniform path convergence gives uniform convergence of the actual finite family. -/
theorem familyPath_tendsto (T : ℝ) (u : ℕ → I → C(Icc (0 : ℝ) T, E))
    (v : I → C(Icc (0 : ℝ) T, E))
    (hu : ∀ i, Filter.Tendsto (fun n => u n i) Filter.atTop (𝓝 (v i))) :
    Filter.Tendsto (fun n => familyPath T (u n)) Filter.atTop (𝓝 (familyPath T v)) :=
  (familyPath_continuous T).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hu)

/-- A finite family of actual Bochner fields, constructed by the genuine bounded coordinate
injections. -/
def familyTime (T : ℝ) (u : I → TimeLp T E) : TimeLp T (I → E) := by
  classical
  exact ∑ i, (ContinuousLinearMap.single ℝ (fun _ : I => E) i).compLpL 2 (timeMeasure T) (u i)

/-- The Bochner finite-family construction has exactly the componentwise representative almost
everywhere. -/
theorem familyTime_ae (T : ℝ) (u : I → TimeLp T E) :
    (familyTime T u : ℝ → I → E) =ᵐ[timeMeasure T] fun t i => u i t := by
  classical
  have hi (i : I) := (ContinuousLinearMap.single ℝ (fun _ : I => E) i).coeFn_compLpL (u i)
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ : Finset I)
    (fun i => (ContinuousLinearMap.single ℝ (fun _ : I => E) i).compLpL 2 (timeMeasure T) (u i)),
    ae_all_iff.mpr hi] with t ht hh
  rw [familyTime, ht]
  calc
    _ = ∑ i : I, Pi.single i (u i t) := Finset.sum_congr rfl (fun i _ => hh i)
    _ = _ := Finset.univ_sum_single _

/-- Strong convergence of each actual component gives strong convergence of the full finite Bochner
family. -/
theorem familyTime_tendsto (T : ℝ) (u : ℕ → I → TimeLp T E) (v : I → TimeLp T E)
    (hu : ∀ i, Filter.Tendsto (fun n => u n i) Filter.atTop (𝓝 (v i))) :
    Filter.Tendsto (fun n => familyTime T (u n)) Filter.atTop (𝓝 (familyTime T v)) := by
  classical
  exact tendsto_finsetSum Finset.univ (fun i _ =>
    ((ContinuousLinearMap.single ℝ (fun _ : I => E) i).compLpL 2 (timeMeasure
        T)).continuous.continuousAt.tendsto.comp (hu i))

/-- Bundling continuous paths and passing to genuine Bochner classes commute exactly. -/
theorem familyTime_pathLp (T : ℝ) (hT : 0 ≤ T) (u : I → C(Icc (0 : ℝ) T, E)) :
    familyTime T (fun i => pathLp T hT (u i)) = pathLp T hT (familyPath T u) := by
  apply Lp.ext
  filter_upwards [familyTime_ae T (fun i => pathLp T hT (u i)),
    ae_all_iff.mpr (fun i => pathLp_ae T hT (u i)), pathLp_ae T hT (familyPath T u)] with t h1 h2 h3
  rw [h1, h3]
  exact funext (fun i => h2 i)

end EulerTimeFamily
