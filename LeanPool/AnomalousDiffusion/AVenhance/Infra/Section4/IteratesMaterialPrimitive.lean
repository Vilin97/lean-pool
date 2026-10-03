/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTimeProduct

/-! Material integration by parts for the actual time primitive. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The primitive pairing retains the endpoint term and both material
remainders. Derivatives at the initial boundary are never assumed. -/
theorem iterate_material_primitive_pairing {φ u v : ℝ → Vec 2 → ℝ} {q q' : ℝ → ℝ}
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
    (hIuv : Integrable (fun p : AmnrSpace => u p.1 p.2 *
      deriv (fun s => q s * v s p.2) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)))
    (hIvu : Integrable (fun p : AmnrSpace => (q p.1 * v p.1 p.2) * deriv (fun s => u s p.2) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)))
    (hJ : Integrable (fun p : AmnrSpace => q' p.1 * u p.1 p.2 * v p.1 p.2)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)))
    (hU : Integrable (fun p : AmnrSpace => q p.1 * u p.1 p.2 * amnrMaterial (streamVel φ) v p.1 p.2)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)))
    (hV : Integrable (fun p : AmnrSpace => q p.1 * v p.1 p.2 * amnrMaterial (streamVel φ) u p.1 p.2)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube))) :
    (∫ t in 0..T, ∫ x in unitCube, q' t * u t x * v t x) =
      (∫ x in unitCube, u T x * (q T * v T x)) -
      (∫ x in unitCube, u 0 x * (q 0 * v 0 x)) -
      (∫ t in 0..T, ∫ x in unitCube, q t * u t x * amnrMaterial (streamVel φ) v t x) -
      (∫ t in 0..T, ∫ x in unitCube, q t * v t x * amnrMaterial (streamVel φ) u t x) := by
  have hp := iterate_material_time_product_pairing hφ hu (hq.mul hv) hus
    (fun t ht => contDiff_const.mul (hvs t ht)) hup
    (fun t ht k x => by dsimp only; rw [hvp t ht k x]) hT hIuv hIvu
  have heq : (fun t => (∫ x in unitCube, u t x *
      amnrMaterial (streamVel φ) (fun s y => q s * v s y) t x) +
      (∫ x in unitCube, (q t * v t x) * amnrMaterial (streamVel φ) u t x)) =ᵐ[
      volume.restrict (Set.uIoc 0 T)]
      (fun t => ((∫ x in unitCube, q' t * u t x * v t x) +
      (∫ x in unitCube, q t * u t x * amnrMaterial (streamVel φ) v t x)) +
      (∫ x in unitCube, q t * v t x * amnrMaterial (streamVel φ) u t x)) := by
    filter_upwards [hJ.prod_right_ae, hU.prod_right_ae, ae_restrict_mem measurableSet_uIoc]
      with t hj hu ht
    rw [Set.uIoc_of_le hT] at ht
    have he (x : Vec 2) := iterate_material_time_mul (b := streamVel φ) (q := q) (h := v) (t := t)
        (x := x)
      (hdq t ht.1).differentiableAt
      ((hv.contDiffAt (prod_mem_nhds (Ici_mem_nhds ht.1) Filter.univ_mem)).differentiableAt (by
          simp))
    have hf : (fun x => u t x * amnrMaterial (streamVel φ) (fun s y => q s * v s y) t x) =
        (fun x => q' t * u t x * v t x + q t * u t x * amnrMaterial (streamVel φ) v t x) := by
      funext x
      rw [he x, (hdq t ht.1).deriv]
      ring
    rw [hf, integral_add hj hu]
  rw [intervalIntegral.integral_congr_ae_restrict heq] at hp
  have hj := intervalIntegrable_iff.mpr hJ.integral_prod_left
  have hu := intervalIntegrable_iff.mpr hU.integral_prod_left
  have hv := intervalIntegrable_iff.mpr hV.integral_prod_left
  rw [intervalIntegral.integral_add (hj.add hu) hv,
    intervalIntegral.integral_add hj hu] at hp
  linarith only [hp]

end AVenhance.Infra.Section4
