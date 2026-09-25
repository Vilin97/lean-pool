/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearFlowEnergyDensity

/-! # Divergence and momentum identities for the viscous shear -/

@[expose] public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN.ShearCalculus


namespace CKN
namespace ShearCalculus

/-- Restriction does not change an integral supported on a test support. -/
theorem integral_restrict_test {F G : Vec3 × ℝ → ℝ} {U : Set (Vec3 × ℝ)}
    (hsub : tsupport G ⊆ U) (hzero : ∀ z ∉ tsupport G, F z = 0) :
    (∫ z in U, F z) = ∫ z, F z := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact hzero z (fun h => hz (hsub h))

/-- A spatial test derivative vanishes off the support of the test. -/
theorem spatial_zero {G : Vec3 × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport G) (i : Fin 3) : spatialPartial G i z = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hz (spatial_support hG i h))

/-- A time test derivative vanishes off the support of the test. -/
theorem time_zero {G : Vec3 × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport G) : timePartial G z = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hz (time_support hG h))

/-- A coordinate of a vector test has support contained in the vector support. -/
theorem coordinate_support (φ : Vec3 × ℝ → Vec3) (i : Fin 3) :
    tsupport (fun z => φ z i) ⊆ tsupport φ := by
  apply closure_mono
  intro z hz
  change φ z ≠ 0
  intro he
  exact hz (by change φ z i = 0; rw [he]; rfl)

end ShearCalculus

private theorem scalar_divergence {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    (∫ z : Vec3 × ℝ, shearAmplitude z * spatialPartial ψ 0 z) = 0 := by
  rw [integral_spatial shearAmplitude_smooth hψ hc 0]
  simp [shearAmplitude_spatial]

private theorem scalar_momentum {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    (∫ z : Vec3 × ℝ,
      -shearAmplitude z * timePartial ψ z - shearEnergy z * spatialPartial ψ 0 z +
        shearSlope z * spatialPartial ψ 1 z) = 0 := by
  have ht := integrable_time shearAmplitude_smooth hψ hc
  have hx := integrable_spatial shearEnergy_smooth hψ hc 0
  have hy := integrable_spatial shearSlope_smooth hψ hc 1
  have ht' : (∫ z : Vec3 × ℝ, shearAmplitude z * timePartial ψ z) =
      ∫ z : Vec3 × ℝ, shearAmplitude z * ψ z := by
    rw [integral_time shearAmplitude_smooth hψ hc]
    simp only [shearAmplitude_time, neg_mul, integral_neg, neg_neg]
  have hx' : (∫ z : Vec3 × ℝ, shearEnergy z * spatialPartial ψ 0 z) = 0 := by
    rw [integral_spatial shearEnergy_smooth hψ hc 0]
    simp [shearEnergy_spatial]
  have hy' : (∫ z : Vec3 × ℝ, shearSlope z * spatialPartial ψ 1 z) =
      ∫ z : Vec3 × ℝ, shearAmplitude z * ψ z := by
    rw [integral_spatial shearSlope_smooth hψ hc 1]
    simp only [shearSlope_spatial, ite_true, neg_mul, integral_neg, neg_neg]
  simp only [neg_mul]
  have hsplit := integral_add (ht.neg.sub hx) hy
  dsimp only [Pi.sub_apply, Pi.neg_apply] at hsplit
  rw [hsplit]
  have hsub := integral_sub ht.neg hx
  dsimp only [Pi.neg_apply] at hsub
  rw [hsub, integral_neg, ht', hx', hy']
  ring

/-- The incompressibility test identity, including its integrability clause. -/
theorem shearFlow_divergence (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ (Ioo 0 1)) :
    IntegrableOn (fun z => ∑ i, shearFlow z i * spatialPartial ψ i z)
      (tsupport ψ) volume ∧
    (∫ z in spaceTimeSet Set.univ (Ioo 0 1),
      ∑ i, shearFlow z i * spatialPartial ψ i z) = 0 := by
  have he : (fun z : Vec3 × ℝ => ∑ i, shearFlow z i * spatialPartial ψ i z) =
      (fun z : Vec3 × ℝ => shearAmplitude z * spatialPartial ψ 0 z) := by
    funext z
    simp [shearFlow, shearAmplitude]
  have hi := integrable_spatial shearAmplitude_smooth hψ.1 hψ.2.1 0
  constructor
  · exact (hi.congr (ae_of_all _ fun z => congrFun he.symm z)).integrableOn
  change (∫ z : Vec3 × ℝ in spaceTimeSet Set.univ (Ioo 0 1),
    ∑ i, shearFlow z i * spatialPartial ψ i z) = 0
  rw [he]
  exact (integral_restrict_test (F := fun z => shearAmplitude z * spatialPartial ψ 0 z)
    hψ.2.2 (fun z hz => by rw [spatial_zero hψ.1 hz]; ring)).trans
      (scalar_divergence hψ.1 hψ.2.1)

/-- The momentum test identity with zero pressure and zero force. -/
theorem shearFlow_momentum (φ : Vec3 × ℝ → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 1)) :
    IntegrableOn (fun z =>
      (-(∑ i, shearFlow z i * timePartial (fun w => φ w i) z)) -
      ∑ i, ∑ j, shearFlow z i * shearFlow z j * spatialPartial (fun w => φ w i) j z +
      ∑ i, ∑ j, shearFlowGrad z i j * spatialPartial (fun w => φ w i) j z)
      (tsupport φ) volume ∧
    (∫ z in spaceTimeSet Set.univ (Ioo 0 1),
      (-(∑ i, shearFlow z i * timePartial (fun w => φ w i) z)) -
      ∑ i, ∑ j, shearFlow z i * shearFlow z j * spatialPartial (fun w => φ w i) j z +
      ∑ i, ∑ j, shearFlowGrad z i j * spatialPartial (fun w => φ w i) j z) = 0 := by
  let ψ : Vec3 × ℝ → ℝ := fun z => φ z 0
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := (contDiff_pi.mp hφ.1) 0
  have hψc : HasCompactSupport ψ :=
    hφ.2.1.isCompact.of_isClosed_subset (isClosed_tsupport _) (coordinate_support φ 0)
  have he : (fun z : Vec3 × ℝ =>
      (-(∑ i, shearFlow z i * timePartial (fun w => φ w i) z)) -
      ∑ i, ∑ j, shearFlow z i * shearFlow z j * spatialPartial (fun w => φ w i) j z +
      ∑ i, ∑ j, shearFlowGrad z i j * spatialPartial (fun w => φ w i) j z) =
      (fun z : Vec3 × ℝ => -shearAmplitude z * timePartial ψ z -
        shearEnergy z * spatialPartial ψ 0 z + shearSlope z * spatialPartial ψ 1 z) := by
    funext z
    simp [shearFlow, shearFlowGrad, shearAmplitude, shearSlope, shearEnergy, ψ,
      neg_mul, Fin.sum_univ_three]
    rfl
  have ht := integrable_time shearAmplitude_smooth hψ hψc
  have hx := integrable_spatial shearEnergy_smooth hψ hψc 0
  have hy := integrable_spatial shearSlope_smooth hψ hψc 1
  have hi : Integrable (fun z : Vec3 × ℝ => -shearAmplitude z * timePartial ψ z -
      shearEnergy z * spatialPartial ψ 0 z + shearSlope z * spatialPartial ψ 1 z) := by
    exact ((ht.neg.sub hx).add hy).congr (ae_of_all _ fun z => by
      dsimp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      rw [neg_mul])
  constructor
  · exact (hi.congr (ae_of_all _ fun z => congrFun he.symm z)).integrableOn
  change (∫ z : Vec3 × ℝ in spaceTimeSet Set.univ (Ioo 0 1),
      (-(∑ i, shearFlow z i * timePartial (fun w => φ w i) z)) -
      ∑ i, ∑ j, shearFlow z i * shearFlow z j * spatialPartial (fun w => φ w i) j z +
      ∑ i, ∑ j, shearFlowGrad z i j * spatialPartial (fun w => φ w i) j z) = 0
  rw [he]
  exact (integral_restrict_test (F := fun z =>
    -shearAmplitude z * timePartial ψ z - shearEnergy z * spatialPartial ψ 0 z +
      shearSlope z * spatialPartial ψ 1 z)
    ((coordinate_support φ 0).trans hφ.2.2) (fun z hz => by
    rw [time_zero hψ hz, spatial_zero hψ hz 0, spatial_zero hψ hz 1]
    ring)).trans (scalar_momentum hψ hψc)

end CKN
