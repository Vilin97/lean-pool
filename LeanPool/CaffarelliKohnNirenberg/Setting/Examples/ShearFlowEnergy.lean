/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearFlowWeakForm

/-!
# The local energy identity for the viscous shear

Two spatial integrations by parts and one time integration by parts give
the energy identity, hence the local energy inequality for nonnegative tests.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN.ShearCalculus


namespace CKN

private theorem scalar_energy {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    (∫ z : Vec3 × ℝ, shearEnergy z *
      (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
        shearTransport z * spatialPartial ψ 0 z) =
      2 * ∫ z : Vec3 × ℝ, (shearSlope z * shearSlope z) * ψ z := by
  have ht := integrable_time shearEnergy_smooth hψ hc
  have hd : ∀ i : Fin 3, Integrable (fun z : Vec3 × ℝ =>
      shearEnergy z * spatialSecondPartial ψ i i z) := by
    intro i
    exact integrable_spatial shearEnergy_smooth (spatial_smooth hψ i)
      (hc.isCompact.of_isClosed_subset (isClosed_tsupport _) (spatial_support hψ i)) i
  have hx := integrable_spatial shearTransport_smooth hψ hc 0
  have hs := integrable_finsetSum Finset.univ (fun i _hi => hd i)
  have he := integrable_product shearEnergy_smooth hψ hc
  have hb := integrable_product (shearSlope_smooth.mul shearSlope_smooth) hψ hc
  have htime : (∫ z : Vec3 × ℝ, shearEnergy z * timePartial ψ z) =
      2 * ∫ z : Vec3 × ℝ, shearEnergy z * ψ z := by
    rw [integral_time shearEnergy_smooth hψ hc]
    simp_rw [shearEnergy_time, mul_assoc]
    rw [integral_const_mul]
    ring
  have htransport : (∫ z : Vec3 × ℝ, shearTransport z * spatialPartial ψ 0 z) = 0 := by
    rw [integral_spatial shearTransport_smooth hψ hc 0]
    simp only [shearTransport_spatial_zero, zero_mul, integral_zero, neg_zero]
  have hsecond : ∀ i : Fin 3,
      (∫ z : Vec3 × ℝ, shearEnergy z * spatialSecondPartial ψ i i z) =
        if i = 1 then 2 * ((∫ z : Vec3 × ℝ, (shearSlope z * shearSlope z) * ψ z) -
          ∫ z : Vec3 × ℝ, shearEnergy z * ψ z) else 0 := by
    intro i
    change (∫ z : Vec3 × ℝ, shearEnergy z *
      spatialPartial (fun w : Vec3 × ℝ => spatialPartial ψ i w) i z) = _
    rw [integral_second shearEnergy_smooth hψ hc i]
    simp_rw [shearEnergy_second]
    by_cases hi : i = 1
    · simp only [hi, ite_true]
      simp_rw [mul_assoc, sub_mul]
      rw [integral_const_mul, integral_sub hb he]
      simp only [mul_assoc]
    · simp [hi]
  calc
    _ = ∫ z : Vec3 × ℝ, (shearEnergy z * timePartial ψ z +
        ∑ i, shearEnergy z * spatialSecondPartial ψ i i z) +
          shearTransport z * spatialPartial ψ 0 z := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by dsimp only; erw [mul_add, Finset.mul_sum]
    _ = (∫ z : Vec3 × ℝ, shearEnergy z * timePartial ψ z) +
        (∑ i, ∫ z : Vec3 × ℝ, shearEnergy z * spatialSecondPartial ψ i i z) +
          ∫ z : Vec3 × ℝ, shearTransport z * spatialPartial ψ 0 z := by
      have hsplit := integral_add (ht.add hs) hx
      dsimp only [Pi.add_apply] at hsplit
      rw [hsplit, integral_add ht hs,
        integral_finsetSum _ (fun i _hi => hd i)]
    _ = _ := by
      rw [htime, htransport]
      simp_rw [hsecond]
      simp only [Fin.sum_univ_three]
      norm_num
      ring

/-- The energy identity holds for every compactly supported smooth scalar test. -/
theorem shearFlow_energyIdentity (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ (Ioo 0 1)) :
    IntegrableOn (fun z => spatialGradientSq shearFlow shearFlowGrad z * ψ z)
      (tsupport ψ) volume ∧
    IntegrableOn (fun z => vec3EuclideanNorm (shearFlow z) ^ 2 *
      (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
        vec3EuclideanNorm (shearFlow z) ^ 2 *
          (∑ i, shearFlow z i * spatialPartial ψ i z)) (tsupport ψ) volume ∧
    2 * (∫ z in spaceTimeSet Set.univ (Ioo 0 1),
      spatialGradientSq shearFlow shearFlowGrad z * ψ z) =
      ∫ z in spaceTimeSet Set.univ (Ioo 0 1),
        vec3EuclideanNorm (shearFlow z) ^ 2 *
          (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
        vec3EuclideanNorm (shearFlow z) ^ 2 *
          (∑ i, shearFlow z i * spatialPartial ψ i z) := by
  have he : (fun z : Vec3 × ℝ => vec3EuclideanNorm (shearFlow z) ^ 2 *
      (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
        vec3EuclideanNorm (shearFlow z) ^ 2 *
          (∑ i, shearFlow z i * spatialPartial ψ i z)) =
      (fun z : Vec3 × ℝ => shearEnergy z *
        (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
          shearTransport z * spatialPartial ψ 0 z) := by
    funext z
    erw [shearFlow_energy]
    simp [shearFlow, shearAmplitude, shearTransport, mul_assoc]
  have hb := integrable_product (shearSlope_smooth.mul shearSlope_smooth) hψ.1 hψ.2.1
  have ht := integrable_time shearEnergy_smooth hψ.1 hψ.2.1
  have hd : ∀ i : Fin 3, Integrable (fun z : Vec3 × ℝ =>
      shearEnergy z * spatialSecondPartial ψ i i z) := by
    intro i
    exact integrable_spatial shearEnergy_smooth (spatial_smooth hψ.1 i)
      (hψ.2.1.isCompact.of_isClosed_subset (isClosed_tsupport _) (spatial_support hψ.1 i)) i
  have hx := integrable_spatial shearTransport_smooth hψ.1 hψ.2.1 0
  have hi : Integrable (fun z : Vec3 × ℝ => shearEnergy z *
      (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
        shearTransport z * spatialPartial ψ 0 z) := by
    exact ((ht.add (integrable_finsetSum Finset.univ (fun i _hi => hd i))).add hx).congr
      (ae_of_all _ fun z => by
        dsimp only [Pi.add_apply]
        rw [mul_add, Finset.mul_sum])
  refine ⟨(hb.congr (ae_of_all _ fun z =>
    congrArg (fun a : ℝ => a * ψ z) (shearFlow_gradientSq z).symm)).integrableOn,
    (hi.congr (ae_of_all _ fun z => congrFun he.symm z)).integrableOn, ?_⟩
  change 2 * (∫ z : Vec3 × ℝ in spaceTimeSet Set.univ (Ioo 0 1),
    spatialGradientSq shearFlow shearFlowGrad z * ψ z) = _
  have hgrad : (fun z : Vec3 × ℝ => spatialGradientSq shearFlow shearFlowGrad z * ψ z) =
      (fun z : Vec3 × ℝ => (shearSlope z * shearSlope z) * ψ z) :=
    funext (fun z => congrArg (fun a : ℝ => a * ψ z) (shearFlow_gradientSq z))
  rw [hgrad]
  erw [he]
  have hzR : ∀ z ∉ tsupport ψ, shearEnergy z *
      (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
        shearTransport z * spatialPartial ψ 0 z = 0 := by
    intro z hz
    have hd0 : ∀ i, spatialSecondPartial ψ i i z = 0 := by
      intro i
      exact spatial_zero (spatial_smooth hψ.1 i)
        (fun h => hz (spatial_support hψ.1 i h)) i
    rw [time_zero hψ.1 hz, spatial_zero hψ.1 hz 0]
    simp only [hd0, Finset.sum_const_zero, add_zero, mul_zero]
  have hleft := integral_restrict_test (F := fun z => (shearSlope z * shearSlope z) * ψ z)
    hψ.2.2 (fun z hz => by rw [image_eq_zero_of_notMem_tsupport hz]; ring)
  have hright := integral_restrict_test hψ.2.2 hzR
  exact (congrArg (fun a : ℝ => 2 * a) hleft).trans
    ((scalar_energy hψ.1 hψ.2.1).symm.trans hright.symm)

end CKN
