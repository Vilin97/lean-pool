/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstancePressure
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSWSFinal
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientInputs
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZP1Closer
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluingTMeasurable

/-!
# A measurable weak pressure gradient on an interior origin ball

The slice derivatives of `eq:pressure-gradient-morrey` have one measurable
representative on the whole time interval. Its derivatives on all open
subdomains share one exceptional set of times, as needed in `prop:bootstrap`.
-/

public section

section

/-!
# Spatial pressure gradients from suitability

The local slice estimate `eq:pressure-gradient-morrey` applies to the centred
tensor source constructed from a suitable weak solution. Spatial gluing
then produces weak derivatives on the whole origin ball for almost every
time in the solution interval, as required by `prop:bootstrap`.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- A suitable solution has a spatial weak pressure gradient on almost every
half-ball slice of each interior cylinder (`eq:pressure-gradient-morrey`). -/
theorem origin_local_slice_gradient_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun x => D x k)
          (euclideanBall z.1 (ρ / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall z.1 (ρ / 2)) k
          (fun x => p (x, s)) (fun x => D x k)) := by
  let c : ℝ → Vec3 := fun s j => average (volume.restrict (vec3Ball z.1 ρ))
    (fun y : Vec3 => u (y, s) j)
  let V : ParabolicPoint → Vec3 := fun w =>
    pressureDivergenceCutoffSourceCentredTensor
      (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
      (fun y => u (y, w.2)) (fun y => Du (y, w.2)) (c w.2) w.1
  have hsource := origin_tensor_source_data_ae_of_sws hsol hρ hsub c
  have hV : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i : Fin 3, MemLp (fun x => V (x, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
      (∀ i : Fin 3, HasCompactSupport (fun x => V (x, s) i)) := by
    filter_upwards [hsource] with s hs
    exact ⟨hs.1, hs.2.1⟩
  have hpair := hsource.mono (fun _ hs => hs.2.2)
  have hCZ := pressureP1_thetaDecay_hCZ_of_sws (max czP1OperatorConstant 0)
    (le_max_right _ _) (le_max_left _ _) hsol hρ hsub
    (pressureSecondExtension_residual_growth_ae_of_sws hsol hρ hsub)
  have hP78 := slice_selected_gradient_hP78_input_of_sws hsol hρ hsub
  have hE : ∀ s : ℝ, 0 ≤ ∫ y in vec3Ball z.1 ρ,
      (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ) := by
    intro s
    exact integral_nonneg (fun y => Real.rpow_nonneg (by unfold utensorNorm; positivity) _)
  have hF : ∀ s, 0 ≤ harmonicRemainderForceBound z hρ f s :=
    fun _ => le_max_right _ _
  have hselected := slice_selected_gradient_ae_of_sws_of_source_data_unconditional
    (1000 * harmonicInteriorDisplayConstant) (9 * max czP1OperatorConstant 0)
    sliceForceGradientConstant le_rfl le_rfl hsol hρ hsub
    (mul_nonneg (by norm_num) (le_max_right _ _)) hE hF hCZ hP78 hV hpair
  filter_upwards [hselected] with s hs
  obtain ⟨D, hloc, hmem, hweak, _⟩ := hs
  exact ⟨D, hloc, hmem, hweak⟩

/-- Spatial gluing of the half-ball slice gradients in `prop:bootstrap`:
the pressure has a weak partial derivative on the origin ball for almost
every time of the entire solution interval. -/
theorem origin_slice_gradient_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q R : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR : 0 < R) (hRone : R < 1) :
    ∀ k : Fin 3, ∀ᵐ t ∂volume.restrict I, ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball (0 : Vec3) R) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R) k (fun x => p (x, t)) g := by
  apply ae_exists_origin_slice_gradient_of_small_cylinders hsol.2.1 hRone.le hdom
    (pressure_slice_locallyIntegrable_ae_on_origin_ball hsol hdom hR hRone)
  intro k c t ρ hρ hsub
  filter_upwards [origin_local_slice_gradient_ae_of_sws (z := (c, t)) (ρ := ρ) hsol hρ hsub] with
    s hs
  obtain ⟨D, hloc, _, hweak⟩ := hs
  exact ⟨fun x => D x k, hloc k, hweak k⟩

end CKN.Core.Step4
end

end

open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

open OriginInstance

/-- Suitability supplies a measurable field whose slices are weak pressure
derivatives on the interior ball, with uniqueness on every open subdomain. -/
theorem origin_measurable_weak_gradient_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q R : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR : 0 < R) (hRone : R < 1) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
        LocallyIntegrableOn (fun x => Dp (x, s) k) (vec3Ball 0 R) volume ∧
        HasWeakPartialDerivOn (vec3Ball 0 R) k
          (fun x => p (x, s)) (fun x => Dp (x, s) k) ∧
        ∀ W : Set Vec3, IsOpen W → W ⊆ vec3Ball 0 R → ∀ g : Vec3 → ℝ,
          LocallyIntegrableOn g W volume →
          HasWeakPartialDerivOn W k (fun x => p (x, s)) g →
          (fun x => Dp (x, s) k) =ᵐ[volume.restrict W] g := by
  let S : ℝ := (R + 1) / 2
  have hRS : R < S := by dsimp [S]; linarith only [hRone]
  have hS : 0 < S := hR.trans hRS
  have hSone : S < 1 := by dsimp [S]; linarith only [hRone]
  obtain ⟨hΩ, _⟩ := originUnitBall_subset_of_dom hdom
  obtain ⟨J, _hJmono, hJord, hJcpt, hJI, hJunion, _hJcover⟩ :=
    exists_compact_ordConnected_exhaustion hsol.2.1 hsol.2.2.1
  have hpint : ∀ n, IntegrableOn p (vec3Ball (0 : Vec3) S ×ˢ J n) volume := by
    intro n
    exact pressure_integrable_on_of_suitable_local_box hsol
      (originLocalBox_of_time hS hSone hΩ (hJord n) (hJcpt n) (hJI n)) subset_rfl
  have hinner : closure (vec3Ball (0 : Vec3) R) ⊆ vec3Ball (0 : Vec3) S := by
    rw [closure_vec3Ball hR]
    intro y hy
    exact lt_of_le_of_lt hy hRS
  exact CKN.exists_measurable_weakGradient_on_time_union
    (isOpen_vec3Ball _ _) (isOpen_vec3Ball _ _)
    (originIsCompact_closure_vec3Ball hR) hinner
    (fun n => (hJcpt n).isClosed.measurableSet) hJunion hpint
    (origin_slice_gradient_ae_of_sws hsol hdom hS hSone)

end CKN.Core.Step4
