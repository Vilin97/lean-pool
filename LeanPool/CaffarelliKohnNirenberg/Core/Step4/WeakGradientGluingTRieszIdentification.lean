/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSelection
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientForceUnconditional

/-! # Identifying a fixed pressure derivative with the completed operators

The first-potential pairing has positive sign, so the derivative of its
sum is the negative Riesz sum. The negative first-potential sum of the near
force has the opposite sign. Uniqueness identifies these terms with an
already chosen weak pressure derivative.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- The sum of first potentials has the negative completed Riesz sum as its
weak derivative on every open spatial carrier. -/
theorem newtonian_derivative_sum_hasWeakPartialDerivOn_riesz
    {B : Set Vec3} (hB : IsOpen B) (i : Fin 3) {V : Vec3 → Vec3}
    (hV : ∀ j, MemLp (fun y => V y j) (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hVc : ∀ j, HasCompactSupport (fun y => V y j)) :
    HasWeakPartialDerivOn B i
      (fun x => ∑ j, pressureNewtonianDerivativePotential j (fun y => V y j) x)
      (fun x => -(∑ j, rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => V y j) x)) := by
  apply Core.Endgame.weak_partial_deriv_on_of_global_pairing hB
  intro ψ hψ hψc
  have hI (j : Fin 3) : Integrable (fun x =>
      pressureNewtonianDerivativePotential j (fun y => V y j) x * spatialDeriv ψ i x)
      volume :=
    pressureNewtonianDerivativePotential_mul_smooth_integrable
      (memLp_six_fifths_integrable_of_hasCompactSupport (hV j) (hVc j)) (hVc j)
      (contDiff_spatialDeriv_smooth hψ i) (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i))
  have hR (j : Fin 3) : Integrable (fun x =>
      rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i) (fun y => V y j) x * ψ x) volume := by
    have hm := rieszSecondGradientExtension_memLp
      (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (hV j) (hVc j)
    simpa only [smul_eq_mul] using
      (hm.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
        hψ.continuous hψc
  simp_rw [neg_mul, Finset.sum_mul]
  rw [integral_neg, neg_neg, integral_finsetSum _ (fun j _ => hI j),
    integral_finsetSum _ (fun j _ => hR j)]
  exact Finset.sum_congr rfl fun j _ =>
    pressureNewtonianDerivativePotential_gradient_extension_pairing
      (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (hV j) (hVc j) hψ hψc

/-- A fixed weak pressure derivative agrees with the signed Riesz sums and
the classical derivative of the smooth remainder. -/
theorem weak_pressure_derivative_eq_riesz_sum_remainder
    {B : Set Vec3} (hB : IsOpen B) (i : Fin 3)
    {p h g : Vec3 → ℝ} {V W : Vec3 → Vec3}
    (hV : ∀ j, MemLp (fun y => V y j) (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hVc : ∀ j, HasCompactSupport (fun y => V y j))
    (hW : ∀ j, MemLp (fun y => W y j) (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hWc : ∀ j, HasCompactSupport (fun y => W y j))
    (hh : ContDiffOn ℝ (1 : ℕ∞) h B)
    (hrep : p =ᵐ[volume.restrict B] fun x =>
      (∑ j, pressureNewtonianDerivativePotential j (fun y => V y j) x) +
        (h x - ∑ j, pressureNewtonianDerivativePotential j (fun y => W y j) x))
    (hg : LocallyIntegrableOn g B volume) (hpg : HasWeakPartialDerivOn B i p g) :
    g =ᵐ[volume.restrict B] fun x =>
      -(∑ j, rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => V y j) x) +
      classicalGradient h x i +
      ∑ j, rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => W y j) x := by
  let R (A : Vec3 → Vec3) : Vec3 → ℝ := fun x =>
    ∑ j, rieszSecondGradientExtensionOperator
      (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => A y j) x
  have hRl (A : Vec3 → Vec3)
      (hA : ∀ j, MemLp (fun y => A y j) (ENNReal.ofReal (6 / 5 : ℝ)) volume)
      (hAc : ∀ j, HasCompactSupport (fun y => A y j)) : LocallyIntegrableOn (R A) B volume := by
    have hm := memLp_finsetSum (Finset.univ : Finset (Fin 3))
      (fun j _ => rieszSecondGradientExtension_memLp
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (hA j) (hAc j))
    exact (hm.locallyIntegrable (by norm_num)).locallyIntegrableOn B
  have hvloc := (newtonianDerivativeSum_locallyIntegrable hV hVc).locallyIntegrableOn B
  have hwloc := (newtonianDerivativeSum_locallyIntegrable hW hWc).locallyIntegrableOn B
  have hrv := hRl V hV hVc
  have hrw := hRl W hW hWc
  have hhg := locallyIntegrableOn_classicalGradient hB i hh
  have hneg : HasWeakPartialDerivOn B i
      (fun x => -(∑ j, pressureNewtonianDerivativePotential j (fun y => W y j) x))
      (R W) := by
    simpa only [neg_neg] using hasWeakPartialDerivOn_neg
      (newtonian_derivative_sum_hasWeakPartialDerivOn_riesz hB i hW hWc)
  have hrest := hasWeakPartialDerivOn_add hB
    (hasWeakPartialDerivOn_classicalGradient hB i hh) hneg
    (hh.continuousOn.locallyIntegrableOn hB.measurableSet) hwloc.neg hhg hrw
  have hfull := Core.Endgame.weak_partial_deriv_of_ae_sum hB
    (by
      change p =ᵐ[volume.restrict B] (fun x =>
        (∑ j, pressureNewtonianDerivativePotential j (fun y => V y j) x) +
        (h x + -(∑ j, pressureNewtonianDerivativePotential j (fun y => W y j) x)))
      simpa only [sub_eq_add_neg] using hrep)
    (newtonian_derivative_sum_hasWeakPartialDerivOn_riesz hB i hV hVc) hrest
    hvloc ((hh.continuousOn.locallyIntegrableOn hB.measurableSet).add hwloc.neg)
    hrv.neg (hhg.add hrw)
  have heq := HasWeakPartialDerivOn.ae_eq hB hg (hrv.neg.add (hhg.add hrw)) hpg hfull
  change g =ᵐ[volume.restrict B] (fun x => -(R V x) +
    (classicalGradient h x i + R W x)) at heq
  simpa only [R, add_assoc] using heq

end CKN.Core.Step4
