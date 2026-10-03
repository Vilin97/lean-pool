/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialPrimitive
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCrossIntegrability

/-! Material integration by parts for the actual time primitive. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The primitive pairing retains the endpoint term and both material
remainders. Derivatives at the initial boundary are never assumed. -/
theorem iterate_material_primitive_pairing_of_smooth {φ u v : ℝ → Vec 2 → ℝ} {q q' : ℝ → ℝ}
    (hφ : IsAdmissibleStream φ)
    (hu : ContDiffOn ℝ 1 (fun p : AmnrSpace => u p.1 p.2) (Set.Ici 0 ×ˢ Set.univ))
    (hv : ContDiffOn ℝ 1 (fun p : AmnrSpace => v p.1 p.2) (Set.Ici 0 ×ˢ Set.univ))
    (hq : ContDiffOn ℝ 1 (fun p : AmnrSpace => q p.1) (Set.Ici 0 ×ˢ Set.univ))
    (hdq : ∀ t, 0 < t → HasDerivAt q (q' t) t)
    (hus : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (u t))
    (hvs : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t))
    {T : ℝ} (hT : 0 ≤ T)
    (hqp : Continuous q') :
    (∫ t in 0..T, ∫ x in unitCube, q' t * u t x * v t x) =
      (∫ x in unitCube, u T x * (q T * v T x)) -
      (∫ x in unitCube, u 0 x * (q 0 * v 0 x)) -
      (∫ t in 0..T, ∫ x in unitCube, q t * u t x * amnrMaterial (streamVel φ) v t x) -
      (∫ t in 0..T, ∫ x in unitCube, q t * v t x * amnrMaterial (streamVel φ) u t x) := by
  have hb : ContinuousOn (fun z : AmnrSpace => streamVel φ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth.continuous.continuousOn
  have hqpc : ContinuousOn (fun z : AmnrSpace => q' z.1)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := (hqp.comp continuous_fst).continuousOn
  exact iterate_material_primitive_pairing hφ hu hv hq hdq hus hvs hup hvp hT
    (iterate_time_cross_pairing_integrable (u := u) (v := fun t x => q t * v t x) hu.continuousOn
        (hq.mul hv) hT)
    (iterate_time_cross_pairing_integrable (u := fun t x => q t * v t x) (v := u)
        (hq.continuousOn.mul hv.continuousOn) hu hT)
    (iterate_time_cell_integrable_of_continuousOn
      ((hqpc.mul hu.continuousOn).mul hv.continuousOn) hT)
    (iterate_material_cross_pairing_integrable (u := fun t x => q t * u t x) (v := v) hb
      (hq.continuousOn.mul hu.continuousOn) hv hT)
    (iterate_material_cross_pairing_integrable (u := fun t x => q t * v t x) (v := u) hb
      (hq.continuousOn.mul hv.continuousOn) hu hT)

end AVenhance.Infra.Section4
