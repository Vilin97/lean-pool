/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof

@[expose] public section

/-!
# An actual global flow for a bounded, uniformly Lipschitz velocity

Existence is the proved global Picard theorem in `EulerPacketExistence`.
Uniqueness gives the two-time composition and inverse identities.  The
bounded velocity and Grönwall estimate will give joint continuity in both
times and the initial point.
-/

noncomputable section

open Set Function Metric
open scoped Topology NNReal

namespace EulerBoundedLipschitzFlow

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Data where
  velocity : ℝ → E → E
  continuous : Continuous (Function.uncurry velocity)
  lipschitzConstant : ℝ≥0
  lipschitz : ∀ t, LipschitzWith lipschitzConstant (velocity t)
  speedBound : ℝ≥0
  speed : ∀ t x, ‖velocity t x‖ ≤ speedBound

namespace Data

variable {E} [CompleteSpace E] (V : Data E)

theorem curve_exists (s : ℝ) (x : E) :
    ∃ α : ℝ → E, α s = x ∧ ∀ t, HasDerivAt α (V.velocity t (α t)) t := by
  have hc : Continuous (Function.uncurry (fun (t : ℝ) (y : E) => V.velocity (t+s) y)) :=
    V.continuous.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  obtain ⟨α, hα0, hα⟩ := EulerPacketExistence.exists_global_solution hc
    (fun t => V.lipschitz (t+s)) x
  refine ⟨fun t => α (t-s), by simpa using hα0, ?_⟩
  intro t
  have h := (hα (t-s)).scomp t ((hasDerivAt_id t).sub_const s)
  simpa only [Function.comp_def, id_eq, sub_add_cancel, one_smul] using h

def flow (s t : ℝ) (x : E) : E := (V.curve_exists s x).choose t

@[simp] theorem flow_initial (s : ℝ) (x : E) : V.flow s s x = x :=
  (V.curve_exists s x).choose_spec.1

theorem flow_hasDerivAt (s t : ℝ) (x : E) :
    HasDerivAt (fun r => V.flow s r x) (V.velocity t (V.flow s t x)) t :=
  (V.curve_exists s x).choose_spec.2 t

theorem flow_continuous_time (s : ℝ) (x : E) : Continuous (fun t => V.flow s t x) :=
  continuous_iff_continuousAt.mpr (fun t => (V.flow_hasDerivAt s t x).continuousAt)

theorem flow_unique (s : ℝ) (x : E) (α : ℝ → E)
    (hα : ∀ t, HasDerivAt α (V.velocity t (α t)) t) (hαs : α s = x) :
    α = fun t => V.flow s t x := by
  apply ODE_solution_unique_univ (v := V.velocity) (s := fun _ => Set.univ)
    (t₀ := s) (fun t => (V.lipschitz t).lipschitzOnWith)
    (fun t => ⟨hα t, Set.mem_univ _⟩)
    (fun t => ⟨V.flow_hasDerivAt s t x, Set.mem_univ _⟩)
  simpa only [V.flow_initial] using hαs

theorem flow_cocycle (r s t : ℝ) (x : E) :
    V.flow s t (V.flow r s x) = V.flow r t x := by
  have h := V.flow_unique s (V.flow r s x) (fun t => V.flow r t x)
    (fun t => V.flow_hasDerivAt r t x) rfl
  exact (congrFun h t).symm

@[simp] theorem flow_inverse (s t : ℝ) (x : E) :
    V.flow t s (V.flow s t x) = x := by
  rw [V.flow_cocycle, V.flow_initial]

theorem flow_lipschitz_time (s : ℝ) (x : E) :
    LipschitzWith V.speedBound (fun t => V.flow s t x) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (V.flow_hasDerivAt s t x).differentiableAt)
  intro t
  rw [(V.flow_hasDerivAt s t x).deriv]
  exact_mod_cast V.speed t (V.flow s t x)

omit [CompleteSpace E] in
/-- A two-sided Grönwall estimate for actual global trajectories. -/
theorem trajectory_distance (α β : ℝ → E)
    (hα : ∀ t, HasDerivAt α (V.velocity t (α t)) t)
    (hβ : ∀ t, HasDerivAt β (V.velocity t (β t)) t) (a b : ℝ) :
    dist (α b) (β b) ≤ dist (α a) (β a) * Real.exp (V.lipschitzConstant * |b-a|) := by
  have hαc : Continuous α := continuous_iff_continuousAt.mpr (fun t => (hα t).continuousAt)
  have hβc : Continuous β := continuous_iff_continuousAt.mpr (fun t => (hβ t).continuousAt)
  by_cases hab : a ≤ b
  · have h := dist_le_of_trajectories_ODE V.lipschitz hαc.continuousOn
      (fun t _ => (hα t).hasDerivWithinAt) hβc.continuousOn
      (fun t _ => (hβ t).hasDerivWithinAt) (le_refl (dist (α a) (β a))) b ⟨hab, le_rfl⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h
  · have hba : b ≤ a := le_of_not_ge hab
    have hlip (t : ℝ) : LipschitzWith V.lipschitzConstant
        (fun x => -V.velocity (-t) x) := (V.lipschitz (-t)).neg
    have hαr (t : ℝ) :
        HasDerivAt (fun r => α (-r)) (-V.velocity (-t) (α (-t))) t := by
      simpa only [Function.comp_def, neg_smul, one_smul] using
        (hα (-t)).scomp t (hasDerivAt_neg t)
    have hβr (t : ℝ) :
        HasDerivAt (fun r => β (-r)) (-V.velocity (-t) (β (-t))) t := by
      simpa only [Function.comp_def, neg_smul, one_smul] using
        (hβ (-t)).scomp t (hasDerivAt_neg t)
    have h := dist_le_of_trajectories_ODE hlip
      (hαc.comp continuous_neg).continuousOn (fun t _ => (hαr t).hasDerivWithinAt)
      (hβc.comp continuous_neg).continuousOn (fun t _ => (hβr t).hasDerivWithinAt)
      (le_refl (dist (α (-(-a))) (β (-(-a))))) (-b) ⟨by linarith, le_rfl⟩
    have he : -b - (-a) = |b-a| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hba)]
      ring
    simpa only [Function.comp_apply, neg_neg, he] using h

theorem flow_distance_initial (s t : ℝ) (x y : E) :
    dist (V.flow s t x) (V.flow s t y) ≤
      dist x y * Real.exp (V.lipschitzConstant * |t-s|) := by
  simpa only [V.flow_initial] using V.trajectory_distance
    (fun t => V.flow s t x) (fun t => V.flow s t y)
    (fun t => V.flow_hasDerivAt s t x) (fun t => V.flow_hasDerivAt s t y) s t

end Data

end EulerBoundedLipschitzFlow
