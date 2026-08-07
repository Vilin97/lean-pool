/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Core
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!
# Analyticity of the Newtonian potential away from collision

Mathlib provides the real binomial series at one but does not package the resulting local
analyticity of arbitrary real powers on the positive half-line. We establish that bridge and apply
it to the inverse square roots in the restricted three-body potential.
-/

namespace LeanPool.PoincareThreeBody

/-- A real power is analytic at every positive base. -/
theorem analyticAt_rpow_of_pos (a : ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    AnalyticAt ℝ (fun x : ℝ ↦ x ^ a) x₀ := by
  let normalize : ℝ → ℝ := fun x ↦ (x - x₀) / x₀
  have hnormalize : AnalyticAt ℝ normalize x₀ := by
    dsimp [normalize]
    fun_prop
  have hnormalize_zero : normalize x₀ = 0 := by
    simp [normalize]
  have hbinomial : AnalyticAt ℝ (fun x ↦ (1 + normalize x) ^ a) x₀ := by
    have h := Real.one_add_rpow_hasFPowerSeriesAt_zero (a := a)
    simpa [Function.comp_def] using h.analyticAt.comp_of_eq hnormalize hnormalize_zero
  have hscaled : AnalyticAt ℝ (fun x ↦ x₀ ^ a * (1 + normalize x) ^ a) x₀ := by
    fun_prop
  apply hscaled.congr
  filter_upwards [lt_mem_nhds hx₀] with x hx
  have hnormalize_eq : 1 + normalize x = x / x₀ := by
    dsimp [normalize]
    field_simp
    ring
  rw [hnormalize_eq, ← Real.mul_rpow hx₀.le (div_nonneg hx.le hx₀.le)]
  congr 1
  field_simp

/-- The inverse square-root function is analytic at every positive real number. -/
theorem analyticAt_inv_sqrt {x₀ : ℝ} (hx₀ : 0 < x₀) :
    AnalyticAt ℝ (fun x : ℝ ↦ 1 / Real.sqrt x) x₀ := by
  apply (analyticAt_rpow_of_pos (-(1 / 2 : ℝ)) hx₀).congr
  filter_upwards [lt_mem_nhds hx₀] with x hx
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hx.le]
  simp

/-- The square-root function is analytic at every positive real number. -/
theorem analyticAt_sqrt_of_pos {x₀ : ℝ} (hx₀ : 0 < x₀) :
    AnalyticAt ℝ Real.sqrt x₀ := by
  apply (analyticAt_rpow_of_pos (1 / 2 : ℝ) hx₀).congr
  filter_upwards [lt_mem_nhds hx₀] with x hx
  exact (Real.sqrt_eq_rpow x).symm


lemma mass_analyticAt (z : ℝ × PhaseSpace) : AnalyticAt ℝ (fun w : ℝ × PhaseSpace ↦ w.1) z :=
  analyticAt_fst

lemma phaseCoordinate_analyticAt (z : ℝ × PhaseSpace) (i : Fin 4) :
    AnalyticAt ℝ (fun w : ℝ × PhaseSpace ↦ w.2 i) z := by
  have heval : AnalyticAt ℝ (fun s : PhaseSpace ↦ s i) z.2 :=
    (ContinuousLinearMap.proj i : PhaseSpace →L[ℝ] ℝ).analyticAt z.2
  simpa [Function.comp_def] using heval.comp (analyticAt_snd (𝕜 := ℝ))

theorem firstPrimaryDistanceSq_analyticAt (z : ℝ × PhaseSpace) :
    AnalyticAt ℝ (Function.uncurry firstPrimaryDistanceSq) z := by
  change AnalyticAt ℝ (fun w ↦ (w.2 0 - 1 + w.1) ^ 2 + (w.2 1) ^ 2) z
  exact ((((phaseCoordinate_analyticAt z 0).sub analyticAt_const).add
    (mass_analyticAt z)).pow 2).add ((phaseCoordinate_analyticAt z 1).pow 2)

theorem secondPrimaryDistanceSq_analyticAt (z : ℝ × PhaseSpace) :
    AnalyticAt ℝ (Function.uncurry secondPrimaryDistanceSq) z := by
  change AnalyticAt ℝ (fun w ↦ (w.2 0 + w.1) ^ 2 + (w.2 1) ^ 2) z
  exact (((phaseCoordinate_analyticAt z 0).add (mass_analyticAt z)).pow 2).add
    ((phaseCoordinate_analyticAt z 1).pow 2)

theorem inverseFirstDistance_analyticAt {z : ℝ × PhaseSpace}
    (hz : firstPrimaryDistanceSq z.1 z.2 ≠ 0) :
    AnalyticAt ℝ
      (fun w : ℝ × PhaseSpace ↦ 1 / Real.sqrt (firstPrimaryDistanceSq w.1 w.2)) z := by
  have hpositive := firstPrimaryDistanceSq_pos hz
  change AnalyticAt ℝ
    ((fun x : ℝ ↦ 1 / Real.sqrt x) ∘ Function.uncurry firstPrimaryDistanceSq) z
  exact (analyticAt_inv_sqrt hpositive).comp
    (f := Function.uncurry firstPrimaryDistanceSq) (firstPrimaryDistanceSq_analyticAt z)

theorem inverseSecondDistance_analyticAt {z : ℝ × PhaseSpace}
    (hz : secondPrimaryDistanceSq z.1 z.2 ≠ 0) :
    AnalyticAt ℝ
      (fun w : ℝ × PhaseSpace ↦ 1 / Real.sqrt (secondPrimaryDistanceSq w.1 w.2)) z := by
  have hpositive := secondPrimaryDistanceSq_pos hz
  change AnalyticAt ℝ
    ((fun x : ℝ ↦ 1 / Real.sqrt x) ∘ Function.uncurry secondPrimaryDistanceSq) z
  exact (analyticAt_inv_sqrt hpositive).comp
    (f := Function.uncurry secondPrimaryDistanceSq) (secondPrimaryDistanceSq_analyticAt z)

/-- The Newtonian potential is jointly analytic in mass and phase away from both collisions. -/
theorem potential_analyticAt {z : ℝ × PhaseSpace} (hz : z ∈ collisionFree) :
    AnalyticAt ℝ (Function.uncurry potential) z := by
  rcases hz with ⟨hfirst, hsecond⟩
  have hmass := mass_analyticAt z
  have honeSubMass : AnalyticAt ℝ (fun w : ℝ × PhaseSpace ↦ 1 - w.1) z :=
    analyticAt_const.sub hmass
  have hfirstTerm := hmass.smul (inverseFirstDistance_analyticAt hfirst)
  have hsecondTerm := honeSubMass.smul (inverseSecondDistance_analyticAt hsecond)
  change AnalyticAt ℝ (fun w : ℝ × PhaseSpace ↦
    w.1 / Real.sqrt (firstPrimaryDistanceSq w.1 w.2) +
      (1 - w.1) / Real.sqrt (secondPrimaryDistanceSq w.1 w.2)) z
  apply (hfirstTerm.add hsecondTerm).congr
  filter_upwards [] with w
  simp [smul_eq_mul, div_eq_mul_inv]

/-- The rotating-frame Hamiltonian is jointly analytic away from collision. -/
theorem hamiltonian_analyticAt {z : ℝ × PhaseSpace} (hz : z ∈ collisionFree) :
    AnalyticAt ℝ (Function.uncurry hamiltonian) z := by
  have hp₀ := phaseCoordinate_analyticAt z 0
  have hp₁ := phaseCoordinate_analyticAt z 1
  have hp₂ := phaseCoordinate_analyticAt z 2
  have hp₃ := phaseCoordinate_analyticAt z 3
  have hsquareSum := (hp₂.smul hp₂).add (hp₃.smul hp₃)
  have hhalf := hsquareSum.const_smul (c := (1 / 2 : ℝ))
  have hkineticRaw := (hhalf.add (hp₂.smul hp₁)).sub (hp₃.smul hp₀)
  have hkinetic : AnalyticAt ℝ
      (fun w : ℝ × PhaseSpace ↦
        ((w.2 2) ^ 2 + (w.2 3) ^ 2) / 2 + w.2 2 * w.2 1 - w.2 3 * w.2 0) z := by
    apply hkineticRaw.congr
    filter_upwards [] with w
    simp [smul_eq_mul, div_eq_mul_inv]
    ring
  change AnalyticAt ℝ (fun w ↦
    ((w.2 2) ^ 2 + (w.2 3) ^ 2) / 2 + w.2 2 * w.2 1 - w.2 3 * w.2 0 -
      potential w.1 w.2) z
  exact hkinetic.sub (potential_analyticAt hz)

theorem potential_analyticOn_collisionFree :
    AnalyticOnNhd ℝ (Function.uncurry potential) collisionFree :=
  fun _ hz ↦ potential_analyticAt hz

theorem hamiltonian_analyticOn_collisionFree :
    AnalyticOnNhd ℝ (Function.uncurry hamiltonian) collisionFree :=
  fun _ hz ↦ hamiltonian_analyticAt hz

/-- Joint analyticity supplies an ordinary analytic mass-parameter germ at every collision-free
phase point over `μ = 0`. -/
theorem analyticAt_mass_zero_of_jointlyAnalytic {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hF : IsJointlyAnalytic δ F) {s : PhaseSpace}
    (hs : (0, s) ∈ collisionFree) : AnalyticAt ℝ (fun μ ↦ F μ s) 0 := by
  have hdomain : (0, s) ∈ parameterDomain δ := by
    exact ⟨by simpa using hδ, hs⟩
  have hjoint : AnalyticAt ℝ (Function.uncurry F) (0, s) := hF (0, s) hdomain
  have hembedding : AnalyticAt ℝ (fun μ : ℝ ↦ (μ, s)) 0 :=
    analyticAt_id.prod analyticAt_const
  simpa [Function.comp_def] using hjoint.comp (f := fun μ : ℝ ↦ (μ, s)) hembedding

/-- A jointly analytic candidate integral has a convergent mass-parameter power series at every
collision-free phase point over the Kepler limit. -/
theorem exists_massPowerSeries_of_jointlyAnalytic {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hF : IsJointlyAnalytic δ F) {s : PhaseSpace}
    (hs : (0, s) ∈ collisionFree) :
    ∃ series : FormalMultilinearSeries ℝ ℝ ℝ,
      HasFPowerSeriesAt (fun μ ↦ F μ s) series 0 :=
  analyticAt_mass_zero_of_jointlyAnalytic hδ hF hs

theorem hamiltonian_analyticAt_mass_zero {s : PhaseSpace} (hs : (0, s) ∈ collisionFree) :
    AnalyticAt ℝ (fun μ ↦ hamiltonian μ s) 0 := by
  have hjoint := hamiltonian_analyticAt hs
  have hembedding : AnalyticAt ℝ (fun μ : ℝ ↦ (μ, s)) 0 :=
    analyticAt_id.prod analyticAt_const
  simpa [Function.comp_def] using hjoint.comp (f := fun μ : ℝ ↦ (μ, s)) hembedding

end LeanPool.PoincareThreeBody
