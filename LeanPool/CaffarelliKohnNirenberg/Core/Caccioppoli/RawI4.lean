/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.I4
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Covering
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.CylinderCentered

/-!
# Raw I4

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat


noncomputable section

namespace CKN

/-- Raw forcing contribution to the local energy estimate. -/
@[expose]
def caccioppoliI4HeatCutoffRaw
    {u f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ ε r : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) : ℝ :=
  (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f w)) *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w)).toReal

theorem caccioppoli_I4_heat_cutoff_raw_bound_of_finiteness
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (_ : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hvelocity :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞) :
    caccioppoliI4HeatCutoffRaw (u := u) (f := f) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      2000 * (4 * Real.pi / 3) ^
          (1 / (q / (q - 1)) - 1 / 3 : ℝ) *
        (r / ρ)⁻¹ * gamma u (x₀, t₀) ρ * lambda q f (x₀, t₀) ρ := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hu0 : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).1
  have hf0 : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.2.1
  have hu : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    have h := (ENNReal.continuous_ofReal.comp hc).comp_aestronglyMeasurable hu0
    exact h.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hf : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (f w)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    have h := (ENNReal.continuous_ofReal.comp hc).comp_aestronglyMeasurable hf0
    exact h.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hφ : ∀ w ∈ parabolicCylinder x₀ t₀ ρ,
      backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε)
        x₀ t₀ r w ≤ 1000 / r := by
    intro w hw
    have htime : w.2 - t₀ < r ^ 2 := by
      have hupper := (mem_parabolicCylinder.mp hw).2.2
      linarith only [hupper, sq_pos_of_pos hr]
    have hψ : backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀) ≤ 1000 / r := by
      simpa only [centeredBackwardHeatTest] using
        (centeredBackwardHeatTest_upper_on_cylinder
          (x₀ := x₀) (t₀ := t₀) (r := r) (ρ := ρ) hr hρ hw)
    have hψ0 := backwardHeatTestFunction_nonneg
      (x := w.1 - x₀) (t := w.2 - t₀) hr htime
    have hη1 := caccioppoli_heat_cutoff_le_one x₀ t₀ ρ ε hρ hε (w.1, w.2)
    unfold backwardHeatCutoff
    simp only [ite_eq_left htime]
    calc
      caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w *
          backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀) ≤
        1 * backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀) :=
          mul_le_mul_of_nonneg_right hη1 hψ0
      _ ≤ 1 * (1000 / r) := mul_le_mul_of_nonneg_left hψ (by positivity)
      _ = 1000 / r := by ring
  have hforce := caccioppoli_I4_force_integral_identity hsol
    (x₀, t₀) hρ hsub
  have hvelocity' := caccioppoli_I2_velocity_integral_identity
    (u := u) (z := (x₀, t₀)) (ρ := ρ) hρ hvelocity
  have hgamma : 0 ≤ gamma u (x₀, t₀) ρ := by
    unfold gamma
    positivity
  have hlambda : 0 ≤ lambda q f (x₀, t₀) ρ := by
    unfold lambda
    positivity
  have hbound := caccioppoli_I4_normalization hsol.2.2.2.1 hρ hr
    hgamma hlambda hu hf hφ hforce hvelocity'
  simpa only [caccioppoliI4HeatCutoffRaw] using hbound

theorem caccioppoli_I4_heat_cutoff_raw_normalized
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r C₂₆ : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hr : 0 < r)
    (hεr : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hvelocity :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    (hKbound :
      2000 * (4 * Real.pi / 3) ^
          (1 / (q / (q - 1)) - 1 / 3 : ℝ) ≤ C₂₆ ^ 2) :
    caccioppoliI4HeatCutoffRaw (u := u) (f := f) (x₀ := x₀) (t₀ := t₀)
        (ρ := ρ) (ε := ε) (r := r) hρ hε ≤
      (C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) *
        gamma u (x₀, t₀) ρ ^ (1 / 2 : ℝ) *
        lambda q f (x₀, t₀) ρ ^ (1 / 2 : ℝ)) ^ 2 := by
  apply caccioppoli_I4_square_normalization (κ := r / ρ)
    (γ := gamma u (x₀, t₀) ρ) (ell := lambda q f (x₀, t₀) ρ)
    (div_pos hr hρ) (by unfold gamma; positivity) (by unfold lambda; positivity)
    hKbound
  exact caccioppoli_I4_heat_cutoff_raw_bound_of_finiteness hsol hρ hε hr
    hεr hsub hvelocity

end CKN
