/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceSlice
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluingTMeasurable

/-!
# A measurable weak pressure gradient on an interior origin ball

The slice derivatives of `eq:pressure-gradient-morrey` have one measurable
representative on the whole time interval. Its derivatives on all open
subdomains share one exceptional set of times, as needed in `prop:bootstrap`.
-/

@[expose] public section

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
