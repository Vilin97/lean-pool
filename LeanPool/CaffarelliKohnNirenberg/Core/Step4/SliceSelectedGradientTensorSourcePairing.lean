/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientTensorSource
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative.Product

/-!
# Integration by parts for the centred tensor

Without a finite-measure assumption on the open set, the identity for
`eq:pressure-gradient-decomposition` follows by differentiating the
quadratic product, subtracting its constant-vector correction, and using the
vanishing trace of the weak velocity gradient.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

private theorem tensor_integrable_mul
    {U : Set Vec3} {g φ : Vec3 → ℝ}
    (hg : LocallyIntegrableOn g U volume)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hU : tsupport φ ⊆ U) :
    Integrable (fun x => g x * φ x) volume := by
  have hK := hg.integrableOn_compact_subset hU hc.isCompact
  have hm : IntegrableOn (fun x => g x * φ x) (tsupport φ) volume :=
    hK.smul_continuousOn hφ.continuousOn hc.isCompact
  exact hm.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

private theorem tensor_weak_sub_const_mul
    {U : Set Vec3} {a b da db : Vec3 → ℝ} {k : Fin 3} (c : ℝ)
    (ha : LocallyIntegrableOn a U volume)
    (hb : LocallyIntegrableOn b U volume)
    (hda : LocallyIntegrableOn da U volume)
    (hdb : LocallyIntegrableOn db U volume)
    (hwa : HasWeakPartialDerivOn U k a da)
    (hwb : HasWeakPartialDerivOn U k b db) :
    HasWeakPartialDerivOn U k (fun x => a x - c * b x)
      (fun x => da x - c * db x) := by
  intro φ hφ hc hU
  have hdφ := contDiff_spatialDeriv_smooth hφ k
  have hdc := hc.fderiv_apply (𝕜 := ℝ) (basisVec k)
  have hdU := (tsupport_fderiv_apply_subset ℝ (basisVec k)).trans hU
  have ia := (tensor_integrable_mul ha hdφ.continuous hdc hdU).integrableOn (s := U)
  have ib := (tensor_integrable_mul hb hdφ.continuous hdc hdU).integrableOn (s := U)
  have ida := (tensor_integrable_mul hda hφ.continuous hc hU).integrableOn (s := U)
  have idb := (tensor_integrable_mul hdb hφ.continuous hc hU).integrableOn (s := U)
  have wa := hwa φ hφ hc hU
  have wb := hwb φ hφ hc hU
  change (∫ x in U, (a x - c * b x) * spatialDeriv φ k x) =
    -∫ x in U, (da x - c * db x) * φ x
  simp_rw [sub_mul, mul_assoc]
  rw [integral_sub ia (ib.const_mul c), integral_sub ida (idb.const_mul c),
    integral_const_mul, integral_const_mul]
  change (∫ x in U, a x * (fderiv ℝ φ x) (basisVec k)) -
      c * (∫ x in U, b x * (fderiv ℝ φ x) (basisVec k)) = _
  rw [wa, wb]
  ring

/-- The force-free centred source pairs with the singly centred tensor in
`eq:pressure-gradient-decomposition` for every compactly supported smooth test. -/
theorem pressureDivergenceCutoffSourceCentredTensor_pairing_of_divfree
    {U : Set Vec3} (hU : IsOpen U)
    {η : Vec3 → ℝ} {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {c : Vec3}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U)
    (hu : ∀ i, MemLp (fun x => u x i) 2 (volume.restrict U))
    (hDu : ∀ i j, MemLp (fun x => Du x i j) 2 (volume.restrict U))
    (hw : ∀ i, HasWeakGradientOn U (fun x => u x i) (fun x => Du x i))
    (hdiv : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in U, ∑ i, u x i * spatialDeriv φ i x = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∑ i, ∫ x, pressureDivergenceCutoffSourceCentredTensor η (spatialDeriv η) u Du c x i *
      spatialDeriv ψ i x) =
    pressureSecondPairing (fun i j x => η x * (-u x i * (u x j - c j))) ψ := by
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ENNReal.HolderConjugate.instTwoTwo
  have loc {g : Vec3 → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
      (hg : MemLp g p (volume.restrict U)) : LocallyIntegrableOn g U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable hp)
  let A (i j : Fin 3) (x : Vec3) := u x i * u x j - c j * u x i
  let B (i j : Fin 3) (x : Vec3) :=
    Du x i j * u x j + u x i * Du x j j - c j * Du x i j
  let W (i j : Fin 3) (x : Vec3) :=
    η x * B i j x + A i j x * spatialDeriv η j x
  have hA (i j : Fin 3) : LocallyIntegrableOn (A i j) U volume :=
    (loc (p := 1) (by norm_num) ((hu i).mul (hu j))).sub (loc (by norm_num) ((hu i).const_mul (c
      j)))
  have hB (i j : Fin 3) : LocallyIntegrableOn (B i j) U volume :=
    ((loc (p := 1) (by norm_num) ((hDu i j).mul (hu j))).add
      (loc (p := 1) (by norm_num) ((hu i).mul (hDu j j)))).sub
      (loc (by norm_num) ((hDu i j).const_mul (c j)))
  have hW (i j : Fin 3) : Integrable (W i j) volume := by
    have h₁ := tensor_integrable_mul (hB i j) hη.continuous hηc hηU
    have h₂ := tensor_integrable_mul (hA i j)
      (contDiff_spatialDeriv_smooth hη j).continuous
      (hηc.fderiv_apply (𝕜 := ℝ) (basisVec j))
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηU)
    exact (h₁.add h₂).congr (Eventually.of_forall fun x => by
      dsimp [W]
      ring)
  have hWA (i j : Fin 3) : HasWeakPartialDerivOn univ j
      (fun x => η x * A i j x) (W i j) := by
    have hp := HasWeakGradientOn.mul_of_memLp_two hU (hu i) (hu j)
      (hDu i) (hDu j) (hw i) (hw j)
    have hs := tensor_weak_sub_const_mul (c j)
      (loc (p := 1) (by norm_num) ((hu i).mul (hu j))) (loc (by norm_num) (hu i))
      ((loc (p := 1) (by norm_num) ((hDu i j).mul (hu j))).add
        (loc (p := 1) (by norm_num) ((hu i).mul (hDu j j))))
      (loc (by norm_num) (hDu i j)) (hp j) (hw i j)
    exact HasWeakPartialDerivOn.mul_smooth_zeroExtend hU (hA i j) (hB i j)
      hs hη hηc hηU
  have hWi (i j : Fin 3) : Integrable (fun x => W i j x * spatialDeriv ψ i x) volume :=
    tensor_integrable_mul ((hW i j).locallyIntegrable.locallyIntegrableOn univ)
      (contDiff_spatialDeriv_smooth hψ i).continuous
      (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)) (subset_univ _)
  have hAi (i j : Fin 3) : Integrable
      (fun x => η x * A i j x * mixedSecond ψ i j x) volume := by
    have hm := tensor_integrable_mul (hA i j)
      (hη.continuous.mul (contDiff_mixedSecond_smooth hψ i j).continuous)
      (hηc.mul_right (f' := mixedSecond ψ i j))
      ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηU)
    exact hm.congr (Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply]
      ring)
  have hpair (i j : Fin 3) :
      (∫ x, W i j x * spatialDeriv ψ i x) =
        -(∫ x, η x * A i j x * mixedSecond ψ i j x) := by
    have hp := hWA i j (spatialDeriv ψ i) (contDiff_spatialDeriv_smooth hψ i)
      (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)) (subset_univ _)
    simp only [Measure.restrict_univ] at hp
    change (∫ x, η x * A i j x * mixedSecond ψ j i x) =
      -(∫ x, W i j x * spatialDeriv ψ i x) at hp
    simp_rw [mixedSecond_swap hψ j i] at hp
    linarith only [hp]
  have ht := weak_gradient_trace_eq_zero_ae hU hu hDu hw hdiv
  have hsum (i : Fin 3) : (fun x => ∑ j, W i j x) =ᵐ[volume]
      (fun x => pressureDivergenceCutoffSourceCentredTensor η (spatialDeriv η) u Du c x i) := by
    have ht' := (ae_restrict_iff' hU.measurableSet).1 ht
    filter_upwards [ht'] with x hx
    by_cases hxU : x ∈ U
    · have hz : ∑ j, Du x j j = 0 := hx hxU
      have heq : (∑ j, W i j x) =
          pressureDivergenceCutoffSourceCentredTensor η (spatialDeriv η) u Du c x i +
            η x * u x i * ∑ j, Du x j j := by
        simp only [pressureDivergenceCutoffSourceCentredTensor, Finset.mul_sum, ←
          Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [W, A, B]
        ring
      rw [heq, hz, mul_zero, add_zero]
    · have he : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxU (hηU h))
      have hd (j : Fin 3) : spatialDeriv η j x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxU
          (hηU ((tsupport_fderiv_apply_subset ℝ (basisVec j)) h)))
      simp only [W, pressureDivergenceCutoffSourceCentredTensor, he, hd, zero_mul, mul_zero,
        add_zero, Finset.sum_const_zero]
  calc
    _ = ∑ i, ∫ x, (∑ j, W i j x) * spatialDeriv ψ i x := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_congr_ae ((hsum i).symm.mono fun x hx => congrArg
        (fun a => a * spatialDeriv ψ i x) hx)
    _ = ∑ i, ∑ j, ∫ x, W i j x * spatialDeriv ψ i x := by
      simp_rw [Finset.sum_mul]
      congr 1
      funext i
      exact integral_finsetSum _ fun j _ => hWi i j
    _ = -(∑ i, ∑ j, ∫ x, η x * A i j x * mixedSecond ψ i j x) := by
      simp_rw [hpair, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i, ∑ j, η x * A i j x * mixedSecond ψ i j x) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hAi i j))]
      simp_rw [integral_finsetSum _ (fun j _ => hAi _ j)]
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [A]
        ring

end CKN.Core.Step4
