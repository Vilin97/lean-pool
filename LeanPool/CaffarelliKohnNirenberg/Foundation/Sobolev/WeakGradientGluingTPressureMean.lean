/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientRemainder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicRemainderSlice
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGaugeMajorantShift

/-! # Constant shifts of weak pressure derivatives

Spatial constants may be subtracted from a pressure slice without changing
its weak gradient or its distributional harmonicity. In particular these
identities apply to the spatial mean at each fixed time.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section
namespace CKN

private theorem weak_derivative_const {B : Set Vec3} (hB : IsOpen B)
    (c : ℝ) (k : Fin 3) :
    HasWeakPartialDerivOn B k (fun _ => c) (fun _ => 0) := by
  exact Core.Step4.hasWeakPartialDerivOn_const hB c k

/-- Subtracting a spatial constant preserves a locally integrable weak
partial derivative. -/
theorem HasWeakPartialDerivOn.sub_const {B : Set Vec3} (hB : IsOpen B)
    {p g : Vec3 → ℝ} {k : Fin 3}
    (hp : LocallyIntegrableOn p B volume) (hg : LocallyIntegrableOn g B volume)
    (hpg : HasWeakPartialDerivOn B k p g) (c : ℝ) :
    HasWeakPartialDerivOn B k (fun x => p x - c) g := by
  exact Core.Step4.hasWeakPartialDerivOn_sub_const hB hp hg hpg c

private theorem integrable_mul_test {B : Set Vec3} (hB : IsOpen B)
    {f ψ : Vec3 → ℝ} (hf : LocallyIntegrableOn f B volume)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ B) :
    IntegrableOn (fun x => f x * ψ x) B volume := by
  have hm := hf.mul_continuousOn hψ.continuousOn hB.isLocallyClosed
  have hk := hm.integrableOn_compact_subset hs hc.isCompact
  exact (hk.integrable_of_forall_notMem_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])).integrableOn

/-- Subtracting a spatial constant preserves distributional harmonicity. -/
theorem Foundation.Heat.WeaklyHarmonicOn.sub_const {B : Set Vec3} (hB : IsOpen B)
    {h : Vec3 → ℝ} (hloc : LocallyIntegrableOn h B volume)
    (hh : WeaklyHarmonicOn B h) (c : ℝ) :
    WeaklyHarmonicOn B (fun x => h x - c) := by
  intro ψ hψ hψc hψB
  have hdcont (i : Fin 3) : Continuous (spatialDeriv (spatialDeriv ψ i) i) :=
    (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hψ i) i).continuous
  have hdc (i : Fin 3) : HasCompactSupport (spatialDeriv (spatialDeriv ψ i) i) :=
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)).fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hdB (i : Fin 3) : tsupport (spatialDeriv (spatialDeriv ψ i) i) ⊆ B :=
    (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hψB)
  have hcLoc : LocallyIntegrableOn (fun _ : Vec3 => c) B volume :=
    continuousOn_const.locallyIntegrableOn hB.measurableSet
  have hzero (i : Fin 3) :
      (∫ x in B, c * spatialDeriv (spatialDeriv ψ i) i x) = 0 := by
    have hi := weak_derivative_const hB c i (spatialDeriv ψ i)
      (contDiff_spatialDeriv_smooth hψ i) (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i))
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hψB)
    simpa only [spatialDeriv, zero_mul, integral_zero, neg_zero] using hi
  have hint : IntegrableOn (fun x => h x * spatialLaplacian ψ x) B volume := by
    simp only [spatialLaplacian, Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ => integrable_mul_test hB hloc
      (hdcont i) (hdc i) (hdB i)
  have hcint : IntegrableOn (fun x => c * spatialLaplacian ψ x) B volume := by
    simp only [spatialLaplacian, Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ => integrable_mul_test hB hcLoc
      (hdcont i) (hdc i) (hdB i)
  have hczero : (∫ x in B, c * spatialLaplacian ψ x) = 0 := by
    simp only [spatialLaplacian, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => integrable_mul_test hB hcLoc
      (hdcont i) (hdc i) (hdB i))]
    simp only [hzero, Finset.sum_const_zero]
  simp_rw [sub_mul]
  rw [integral_sub hint hcint, hh ψ hψ hψc hψB, hczero, sub_zero]

end CKN
