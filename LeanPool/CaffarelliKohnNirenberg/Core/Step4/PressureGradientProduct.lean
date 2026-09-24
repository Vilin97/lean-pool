/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientBase

/-!
# Pressure Gradient Product

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

theorem weak_gradient_trace_eq_zero_ae
    {U : Set Vec3} (hU : IsOpen U)
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Fin 3 → ℝ}
    (hu : ∀ i : Fin 3, MemLp (fun x => u x i) 2 (volume.restrict U))
    (hDu : ∀ i j : Fin 3, MemLp (fun x => Du x i j) 2 (volume.restrict U))
    (hweak : ∀ i : Fin 3,
      HasWeakGradientOn U (fun x => u x i) (fun x => Du x i))
    (hdiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x in U, ∑ i, u x i * spatialDeriv ψ i x = 0) :
    (fun x => ∑ i, Du x i i) =ᵐ[volume.restrict U] 0 := by
  have htraceRestr : LocallyIntegrable (fun x => ∑ i, Du x i i)
      (volume.restrict U) := by
    simpa only [Finset.sum_apply] using
      locallyIntegrable_finsetSum (μ := volume.restrict U)
        (Finset.univ : Finset (Fin 3))
        (fun i hi => (hDu i i).locallyIntegrable (by norm_num))
  have htraceLoc : LocallyIntegrableOn (fun x => ∑ i, Du x i i) U volume := by
    exact locallyIntegrableOn_of_locallyIntegrable_restrict htraceRestr
  have hzero : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x in U, ψ x * (∑ i, Du x i i) = 0 := by
    intro ψ hψ hψc hψU
    have hψd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i) :=
      contDiff_spatialDeriv_smooth hψ i
    have hleft (i : Fin 3) : IntegrableOn
        (fun x => u x i * spatialDeriv ψ i x) U volume := by
      have huLoc : LocallyIntegrableOn (fun x => u x i) U volume :=
        locallyIntegrableOn_of_locallyIntegrable_restrict
          ((hu i).locallyIntegrable (by norm_num))
      have hmulLoc : LocallyIntegrableOn
          (fun x => u x i * spatialDeriv ψ i x) U volume :=
        huLoc.mul_continuousOn (hψd i).continuous.continuousOn hU.isLocallyClosed
      have hmulK := hmulLoc.integrableOn_compact_subset hψU hψc.isCompact
      have hmulFull := hmulK.integrable_of_forall_notMem_eq_zero (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (f := spatialDeriv ψ i)
          (fun hxt => hx ((tsupport_fderiv_apply_subset ℝ (basisVec i)) hxt))]
        simp)
      exact hmulFull.integrableOn
    have hright (i : Fin 3) : IntegrableOn
        (fun x => Du x i i * ψ x) U volume := by
      have hduLoc : LocallyIntegrableOn (fun x => Du x i i) U volume :=
        locallyIntegrableOn_of_locallyIntegrable_restrict
          ((hDu i i).locallyIntegrable (by norm_num))
      have hmulLoc : LocallyIntegrableOn
          (fun x => Du x i i * ψ x) U volume :=
        hduLoc.mul_continuousOn hψ.continuous.continuousOn hU.isLocallyClosed
      have hmulK := hmulLoc.integrableOn_compact_subset hψU hψc.isCompact
      have hmulFull := hmulK.integrable_of_forall_notMem_eq_zero (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (f := ψ) (fun hxt => hx hxt)]
        simp)
      exact hmulFull.integrableOn
    have hparts (i : Fin 3) :
        ∫ x in U, u x i * spatialDeriv ψ i x =
          -∫ x in U, Du x i i * ψ x :=
      hweak i i ψ hψ hψc hψU
    have hsumLeft : ∫ x in U, ∑ i, u x i * spatialDeriv ψ i x =
        ∑ i, ∫ x in U, u x i * spatialDeriv ψ i x := by
      exact integral_finsetSum (μ := volume.restrict U)
        (Finset.univ : Finset (Fin 3)) (fun i _ => hleft i)
    have hsumRight : ∫ x in U, ∑ i, Du x i i * ψ x =
        ∑ i, ∫ x in U, Du x i i * ψ x := by
      exact integral_finsetSum (μ := volume.restrict U)
        (Finset.univ : Finset (Fin 3)) (fun i _ => hright i)
    have hdiv' := hdiv ψ hψ hψc hψU
    rw [hsumLeft] at hdiv'
    calc
      ∫ x in U, ψ x * (∑ i, Du x i i) =
          ∫ x in U, ∑ i, Du x i i * ψ x := by
            apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
            intro x hx
            change ψ x * (∑ i, Du x i i) = ∑ i, Du x i i * ψ x
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = ∑ i, ∫ x in U, Du x i i * ψ x := hsumRight
      _ = ∑ i, -∫ x in U, u x i * spatialDeriv ψ i x := by
        apply Finset.sum_congr rfl
        intro i hi
        linarith only [hparts i]
      _ = -∑ i, ∫ x in U, u x i * spatialDeriv ψ i x := by
        simp only [Finset.sum_neg_distrib]
      _ = 0 := by rw [hdiv']; simp
  have hzeroFull : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, ψ x * (∑ i, Du x i i) = 0 := by
    intro ψ hψ hψc hψU
    have hout : ∀ x, x ∉ U → ψ x * (∑ i, Du x i i) = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := ψ)
        (fun hxt => hx (hψU hxt))]
      simp
    calc
      ∫ x, ψ x * (∑ i, Du x i i) =
          ∫ x in U, ψ x * (∑ i, Du x i i) := by
            exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hout).symm
      _ = 0 := hzero ψ hψ hψc hψU
  have hzero' := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero htraceLoc (by
    intro ψ hψ hψc hψU
    simpa [smul_eq_mul, mul_comm] using hzeroFull ψ hψ hψc hψU)
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hU.measurableSet]
  filter_upwards [hzero'] with x hx
  simpa using hx

theorem weak_gradient_product_indicator
    {U : Set Vec3} (hU : IsOpen U)
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Fin 3 → ℝ}
    (hu : ∀ i : Fin 3, MemLp (fun x => u x i) 2 (volume.restrict U))
    (hDu : ∀ i j : Fin 3, MemLp (fun x => Du x i j) 2 (volume.restrict U))
    (hweak : ∀ i : Fin 3,
      HasWeakGradientOn U (fun x => u x i) (fun x => Du x i)) :
    ∀ i j : Fin 3, HasWeakGradientOn U
      (fun x => U.indicator (fun y => u y i) x *
        U.indicator (fun y => u y j) x)
      (fun x k => U.indicator (fun y => Du y i k) x *
          U.indicator (fun y => u y j) x +
        U.indicator (fun y => u y i) x *
          U.indicator (fun y => Du y j k) x) := by
  intro i j
  have hmemU (i : Fin 3) :
      MemLp (U.indicator (fun x => u x i)) 2 (volume.restrict U) := by
    apply hu i |>.ae_eq
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    simp [Set.indicator_of_mem hx]
  have hmemDu (i j : Fin 3) :
      MemLp (fun x => U.indicator (fun y => Du y i j) x) 2
        (volume.restrict U) := by
    apply hDu i j |>.ae_eq
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    simp [Set.indicator_of_mem hx]
  have hweakU (i : Fin 3) : HasWeakGradientOn U
      (U.indicator (fun x => u x i))
      (fun x j => U.indicator (fun y => Du y i j) x) := by
    intro j φ hφ hφc hφU
    calc
      ∫ x in U, U.indicator (fun y => u y i) x *
          (fderiv ℝ φ x) (basisVec j) =
          ∫ x in U, u x i * (fderiv ℝ φ x) (basisVec j) := by
            apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
            intro x hx
            simp [Set.indicator_of_mem hx]
      _ = -∫ x in U, Du x i j * φ x := hweak i j φ hφ hφc hφU
      _ = -∫ x in U, U.indicator (fun y => Du y i j) x * φ x := by
        congr 1
        apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
        intro x hx
        simp [Set.indicator_of_mem hx]
  exact HasWeakGradientOn.mul_of_memLp_two hU (hmemU i) (hmemU j)
    (fun k => hmemDu i k) (fun k => hmemDu j k) (hweakU i) (hweakU j)

end CKN.Core.Step4
