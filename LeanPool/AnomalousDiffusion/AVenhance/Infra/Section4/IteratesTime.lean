/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterial

/-! Time integration of the actual classical energy pairing, including t = 0.
FTC is applied on the open time interval, so no two-sided derivative at the
initial boundary is imposed. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem IteratesTime.time_cell_integrable {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f unitCube := by
  let K : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc
  apply (hf.continuousOn.integrableOn_compact hK).mono_set
  intro x hx i hi
  exact ⟨(hx i hi).1.le, (hx i hi).2.le⟩

/-- FTC and Fubini turn the actual time pairing into the energy difference.
The integrability premise is on the actual pairing, not an energy bound. -/
theorem iterate_smooth_time_energy_pairing
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × Vec 2 => u p.1 p.2)
      (Set.Ici 0 ×ˢ Set.univ)) {T : ℝ} (hT : 0 ≤ T)
    (hI : Integrable (fun p : ℝ × Vec 2 => u p.1 p.2 * deriv (fun s => u s p.2) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube))) :
    (∫ s in 0..T, ∫ x in unitCube, u s x * deriv (fun t => u t x) s) =
      (l2NormSq (u T) - l2NormSq (u 0)) / 2 := by
  rw [intervalIntegral_integral_swap hI]
  have hpoint : ∀ᵐ x ∂volume.restrict unitCube,
      (∫ s in 0..T, u s x * deriv (fun t => u t x) s) = (u T x ^ 2 - u 0 x ^ 2) / 2 := by
    filter_upwards [hI.prod_left_ae] with x hx
    have hc : ContinuousOn (fun s => u s x) (Set.Icc 0 T) :=
      hu.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs.1, Set.mem_univ x⟩)
    have hd : ∀ s ∈ Set.Ioo 0 T,
        HasDerivAt (fun t => u t x ^ 2) (2 * (u s x * deriv (fun t => u t x) s)) s := by
      intro s hs
      have hdomain : Set.Ici (0 : ℝ) ×ˢ Set.univ ∈ nhds (s, x) :=
        prod_mem_nhds (Ici_mem_nhds hs.1) Filter.univ_mem
      have hj : DifferentiableAt ℝ (fun p : ℝ × Vec 2 => u p.1 p.2) (s, x) :=
        (hu.contDiffAt hdomain).differentiableAt (by simp)
      have hdu : DifferentiableAt ℝ (fun t => u t x) s :=
        hj.comp (f := fun t : ℝ => (t, x)) s (hasFDerivAt_prodMk_left (𝕜 := ℝ) s x).differentiableAt
      convert hdu.hasDerivAt.pow 2 using 1
      ring
    have hi : IntervalIntegrable (fun s => u s x * deriv (fun t => u t x) s) volume 0 T :=
      intervalIntegrable_iff.mpr hx
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT (hc.pow 2) hd
      (hi.const_mul 2)
    dsimp only [Pi.pow_apply] at he
    rw [intervalIntegral.integral_const_mul] at he
    linarith only [he]
  rw [integral_congr_ae hpoint]
  have hc (s : ℝ) (hs : 0 ≤ s) : Continuous (u s) := by
    have hm : ContDiff ℝ 1 (fun x : Vec 2 => (s, x)) := by fun_prop
    exact (hu.comp_contDiff hm (fun x => ⟨hs, Set.mem_univ x⟩)).continuous
  have h₁ := IteratesTime.time_cell_integrable ((hc T hT).pow 2)
  have h₀ := IteratesTime.time_cell_integrable ((hc 0 le_rfl).pow 2)
  have hs := integral_sub h₁ h₀
  dsimp only [Pi.pow_apply] at hs
  rw [integral_div, hs]
  rfl

/-- Specialize time FTC to the actual classical initial trace. -/
theorem iterate_classical_time_energy_pairing
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F u₀ u) {T : ℝ} (hT : 0 ≤ T)
    (hI : Integrable (fun p : ℝ × Vec 2 => u p.1 p.2 * deriv (fun s => u s p.2) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube))) :
    (∫ s in 0..T, ∫ x in unitCube, u s x * deriv (fun t => u t x) s) =
      (l2NormSq (u T) - l2NormSq u₀) / 2 := by
  have he := iterate_smooth_time_energy_pairing (hsol.1.of_le (by simp)) hT hI
  have htrace : u 0 = u₀ := funext hsol.2.2.1
  rw [htrace] at he
  exact he

/-- The transported half-square identity on the periodic cell. Drift cancels
by spatial transport IBP; only positive-time derivatives are used. The joint
regularity premise is C1, allowing the finite-regularity memory primitive. -/
theorem iterate_material_time_square_pairing
    {φ u : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × Vec 2 => u p.1 p.2) (Set.Ici 0 ×ˢ Set.univ))
    (hsmooth : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (u t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t)) {T : ℝ} (hT : 0 ≤ T)
    (hI : Integrable (fun p : ℝ × Vec 2 => u p.1 p.2 * deriv (fun s => u s p.2) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube))) :
    (∫ t in 0..T, ∫ x in unitCube, u t x * amnrMaterial (streamVel φ) u t x) =
      (l2NormSq (u T) - l2NormSq (u 0)) / 2 := by
  have heq : (fun t => ∫ x in unitCube, u t x * amnrMaterial (streamVel φ) u t x) =ᵐ[
      volume.restrict (Set.uIoc 0 T)]
      (fun t => ∫ x in unitCube, u t x * deriv (fun s => u s x) t) := by
    filter_upwards [hI.prod_right_ae, ae_restrict_mem measurableSet_uIoc] with t hi ht
    rw [Set.uIoc_of_le hT] at ht
    have hφslice : ContDiff ℝ (⊤ : ℕ∞) (φ t) := by
      have hm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
      exact hφ.1.comp hm
    have hφper : IsZ2Periodic (φ t) := by
      intro k x
      simpa using hφ.2 0 k t x
    have hp := iterate_material_product_pairing hφslice hφper (hsmooth t ht.1)
      (hsmooth t ht.1) (hup t ht.1) (hup t ht.1) hi hi
    linarith only [hp]
  rw [intervalIntegral.integral_congr_ae_restrict heq]
  exact iterate_smooth_time_energy_pairing hu hT hI

end AVenhance.Infra.Section4
