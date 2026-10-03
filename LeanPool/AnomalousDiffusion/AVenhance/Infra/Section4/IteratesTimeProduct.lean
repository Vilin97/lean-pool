/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTime

/-! Temporal product FTC at the actual initial boundary. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Product FTC for two actual smooth fields, with derivatives required only
in the open time interval. -/
theorem iterate_smooth_time_product_pairing {u v : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : AmnrSpace => u p.1 p.2) (Set.Ici 0 ×ˢ Set.univ))
    (hv : ContDiffOn ℝ 1 (fun p : AmnrSpace => v p.1 p.2) (Set.Ici 0 ×ˢ Set.univ))
    {T : ℝ} (hT : 0 ≤ T)
    (hI : Integrable (fun p : AmnrSpace => u p.1 p.2 * deriv (fun s => v s p.2) p.1 +
      v p.1 p.2 * deriv (fun s => u s p.2) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube))) :
    (∫ t in 0..T, ∫ x in unitCube,
      u t x * deriv (fun s => v s x) t + v t x * deriv (fun s => u s x) t) =
      (∫ x in unitCube, u T x * v T x) - (∫ x in unitCube, u 0 x * v 0 x) := by
  rw [intervalIntegral_integral_swap hI]
  have hp : ∀ᵐ x ∂volume.restrict unitCube,
      (∫ t in 0..T, u t x * deriv (fun s => v s x) t + v t x * deriv (fun s => u s x) t) =
        u T x * v T x - u 0 x * v 0 x := by
    filter_upwards [hI.prod_left_ae] with x hx
    have hc : ContinuousOn (fun s => u s x * v s x) (Set.Icc 0 T) :=
      (hu.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs.1, Set.mem_univ x⟩)).mul
      (hv.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs.1, Set.mem_univ x⟩))
    have hd : ∀ s ∈ Set.Ioo 0 T, HasDerivAt (fun t => u t x * v t x)
        (u s x * deriv (fun t => v t x) s + v s x * deriv (fun t => u t x) s) s := by
      intro s hs
      have hmem : Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) ∈ nhds (s, x) :=
        prod_mem_nhds (Ici_mem_nhds hs.1) Filter.univ_mem
      have hdu := ((hu.contDiffAt hmem).differentiableAt (by simp)).comp
        (f := fun t : ℝ => (t, x)) s (hasFDerivAt_prodMk_left (𝕜 := ℝ) s x).differentiableAt
      have hdv := ((hv.contDiffAt hmem).differentiableAt (by simp)).comp
        (f := fun t : ℝ => (t, x)) s (hasFDerivAt_prodMk_left (𝕜 := ℝ) s x).differentiableAt
      change DifferentiableAt ℝ (fun t => u t x) s at hdu
      change DifferentiableAt ℝ (fun t => v t x) s at hdv
      have hm : HasDerivAt (fun t => u t x * v t x)
          (deriv (fun t => u t x) s * v s x + u s x * deriv (fun t => v t x) s) s :=
        hdu.hasDerivAt.mul hdv.hasDerivAt
      convert hm using 1
      ring
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hc hd
      (intervalIntegrable_iff.mpr hx)
  rw [integral_congr_ae hp]
  have hc (s : ℝ) (hs : 0 ≤ s) : IntegrableOn (fun x => u s x * v s x) unitCube := by
    have hm : ContDiff ℝ 1 (fun x : Vec 2 => (s, x)) := by fun_prop
    have huc := (hu.comp_contDiff hm (fun _ => ⟨hs, Set.mem_univ _⟩)).continuous
    have hvc := (hv.comp_contDiff hm (fun _ => ⟨hs, Set.mem_univ _⟩)).continuous
    let K : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
    have hK : IsCompact K := isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc
    apply ((huc.mul hvc).continuousOn.integrableOn_compact hK).mono_set
    intro x hx i hi
    exact ⟨(hx i hi).1.le, (hx i hi).2.le⟩
  exact integral_sub (hc T hT) (hc 0 le_rfl)

/-- The spatial transport cancels in the actual product pairing, leaving
only the endpoint product. -/
theorem iterate_material_time_product_pairing {φ u v : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ)
    (hu : ContDiffOn ℝ 1 (fun p : AmnrSpace => u p.1 p.2) (Set.Ici 0 ×ˢ Set.univ))
    (hv : ContDiffOn ℝ 1 (fun p : AmnrSpace => v p.1 p.2) (Set.Ici 0 ×ˢ Set.univ))
    (hus : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (u t))
    (hvs : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t))
    {T : ℝ} (hT : 0 ≤ T)
    (hIuv : Integrable (fun p : AmnrSpace => u p.1 p.2 * deriv (fun s => v s p.2) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)))
    (hIvu : Integrable (fun p : AmnrSpace => v p.1 p.2 * deriv (fun s => u s p.2) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube))) :
    (∫ t in 0..T, (∫ x in unitCube, u t x * amnrMaterial (streamVel φ) v t x) +
      (∫ x in unitCube, v t x * amnrMaterial (streamVel φ) u t x)) =
      (∫ x in unitCube, u T x * v T x) - (∫ x in unitCube, u 0 x * v 0 x) := by
  have heq : (fun t => (∫ x in unitCube, u t x * amnrMaterial (streamVel φ) v t x) +
      (∫ x in unitCube, v t x * amnrMaterial (streamVel φ) u t x)) =ᵐ[
      volume.restrict (Set.uIoc 0 T)]
      (fun t => ∫ x in unitCube,
        u t x * deriv (fun s => v s x) t + v t x * deriv (fun s => u s x) t) := by
    filter_upwards [hIuv.prod_right_ae, hIvu.prod_right_ae, ae_restrict_mem measurableSet_uIoc]
      with t huv hvu ht
    rw [Set.uIoc_of_le hT] at ht
    have hφs := hφ.1
    have hφslice : ContDiff ℝ (⊤ : ℕ∞) (φ t) :=
      hφs.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
    have hφper : IsZ2Periodic (φ t) := by
      intro k x
      simpa only [Int.cast_zero, add_zero] using hφ.2 0 k t x
    rw [iterate_material_product_pairing hφslice hφper
      (hus t ht.1) (hvs t ht.1) (hup t ht.1) (hvp t ht.1) hvu huv]
    exact (integral_add huv hvu).symm
  rw [intervalIntegral.integral_congr_ae_restrict heq]
  exact iterate_smooth_time_product_pairing hu hv hT (hIuv.add hIvu)

end AVenhance.Infra.Section4
