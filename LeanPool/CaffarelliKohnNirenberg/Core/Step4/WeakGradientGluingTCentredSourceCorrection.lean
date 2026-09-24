/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSourceQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSourceTensorDef
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszIdentification

/-! # The correction between raw and centred cutoff sources

The raw divergence source and the centred cutoff source differ by cutoff
and spatial-mean terms. Linearity transports this explicit correction to
the completed spatial Riesz operators.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Euclidean
noncomputable section
namespace CKN.Core.Step4

/-- The cutoff and mean correction relative to a raw source on `B`. -/
def centredRawSourceCorrection (B : Set Vec3)
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u f : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (c : Vec3)
    (i : Fin 3) (x : Vec3) : ℝ :=
  (η x - B.indicator (fun _ => (1 : ℝ)) x) * ((∑ k, Du x i k * u x k) - f x i) +
    (∑ k, dη k x * u x i * (u x k - c k)) - η x * (∑ k, Du x i k * c k)

/-- The centred source minus its near-force source equals the raw source
plus the explicit cutoff and mean correction. -/
theorem centred_source_sub_force_eq_raw_add_correction
    (B : Set Vec3) (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u f : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (c : Vec3)
    (i : Fin 3) (x : Vec3) :
    pressureDivergenceCutoffSourceCentredTensor η dη u Du c x i - η x * f x i =
      B.indicator (fun y => (∑ k, Du y i k * u y k) - f y i) x +
        centredRawSourceCorrection B η dη u f Du c i x := by
  unfold pressureDivergenceCutoffSourceCentredTensor centredRawSourceCorrection
  simp only [Fin.sum_univ_three]
  by_cases hx : x ∈ B
  · simp only [Set.indicator_of_mem hx]
    ring
  · simp only [Set.indicator_of_notMem hx]
    ring

/-- The completed gradient Riesz operator is additive on its actual domain. -/
theorem gradient_riesz_add_ae (j i : Fin 3) {a b : Vec3 → ℝ}
    (ha : MemLp a (ENNReal.ofReal (6/5 : ℝ)) volume)
    (hb : MemLp b (ENNReal.ofReal (6/5 : ℝ)) volume) :
    rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) (a+b) =ᵐ[volume]
    rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) a +
    rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) b := by
  let _ : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩
  exact lpExtensionRepresentative_add_ae (by norm_num)
    (rieszSecondGradientExtensionInput (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i)) ha hb

/-- Subtraction is respected almost everywhere on the completed operator domain. -/
theorem gradient_riesz_sub_ae (j i : Fin 3) {a b : Vec3 → ℝ}
    (ha : MemLp a (ENNReal.ofReal (6/5 : ℝ)) volume)
    (hb : MemLp b (ENNReal.ofReal (6/5 : ℝ)) volume) :
    rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) (a-b) =ᵐ[volume]
    rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) a -
    rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) b := by
  have h := gradient_riesz_add_ae j i (ha.sub hb) hb
  rw [sub_add_cancel] at h
  filter_upwards [h] with x hx
  simp only [Pi.add_apply, Pi.sub_apply] at hx ⊢
  linarith only [hx]

/-- The correction belongs to the operator domain whenever the two original
sources and the localized force do. -/
theorem centredRawSourceCorrection_memLp
    (B : Set Vec3) (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u f : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (c : Vec3) (j : Fin 3)
    (hV : MemLp (fun x => pressureDivergenceCutoffSourceCentredTensor η dη u Du c x j)
      (ENNReal.ofReal (6/5 : ℝ)) volume)
    (hF : MemLp (fun x => η x * f x j) (ENNReal.ofReal (6/5 : ℝ)) volume)
    (hG : MemLp (B.indicator (fun x => (∑ k, Du x j k * u x k) - f x j))
      (ENNReal.ofReal (6/5 : ℝ)) volume) :
    MemLp (centredRawSourceCorrection B η dη u f Du c j)
      (ENNReal.ofReal (6/5 : ℝ)) volume := by
  have heq : centredRawSourceCorrection B η dη u f Du c j =
      (fun x => pressureDivergenceCutoffSourceCentredTensor η dη u Du c x j - η x * f x j) -
        B.indicator (fun x => (∑ k, Du x j k * u x k) - f x j) := by
    funext x
    have h := centred_source_sub_force_eq_raw_add_correction B η dη u f Du c j x
    simp only [Pi.sub_apply]
    linarith only [h]
  rw [heq]
  exact (hV.sub hF).sub hG

/-- The exact Riesz identity retains the correction term; the raw and
centred fields are not silently substituted for each other. -/
theorem centred_riesz_eq_raw_add_correction_ae
    (B : Set Vec3) (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u f : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (c : Vec3) (j i : Fin 3)
    (hV : MemLp (fun x => pressureDivergenceCutoffSourceCentredTensor η dη u Du c x j)
      (ENNReal.ofReal (6/5 : ℝ)) volume)
    (hF : MemLp (fun x => η x * f x j) (ENNReal.ofReal (6/5 : ℝ)) volume)
    (hG : MemLp (B.indicator (fun x => (∑ k, Du x j k * u x k) - f x j))
      (ENNReal.ofReal (6/5 : ℝ)) volume) :
    rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i)
      (fun x => pressureDivergenceCutoffSourceCentredTensor η dη u Du c x j - η x * f x j)
      =ᵐ[volume]
    rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i)
      (B.indicator (fun x => (∑ k, Du x j k * u x k) - f x j)) +
    rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) (centredRawSourceCorrection B η dη u f Du c j) := by
  have heq : (fun x => pressureDivergenceCutoffSourceCentredTensor η dη u Du c x j - η x * f x j) =
      B.indicator (fun x => (∑ k, Du x j k * u x k) - f x j) +
        centredRawSourceCorrection B η dη u f Du c j :=
    funext (centred_source_sub_force_eq_raw_add_correction B η dη u f Du c j)
  rw [heq]
  exact gradient_riesz_add_ae j i hG (centredRawSourceCorrection_memLp B η dη u f Du c j hV hF hG)

/-- The signed centred Riesz contribution is exactly the signed raw
contribution minus the correction, on every measurable or nonmeasurable
spatial restriction. -/
theorem signed_centred_riesz_eq_raw_corrected_ae
    (B A : Set Vec3) (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u f : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (c : Vec3) (i : Fin 3)
    (hV : ∀ j, MemLp (fun x => pressureDivergenceCutoffSourceCentredTensor η dη u Du c x j)
      (ENNReal.ofReal (6/5 : ℝ)) volume)
    (hF : ∀ j, MemLp (fun x => η x * f x j) (ENNReal.ofReal (6/5 : ℝ)) volume)
    (hG : ∀ j, MemLp (B.indicator (fun x => (∑ k, Du x j k * u x k) - f x j))
      (ENNReal.ofReal (6/5 : ℝ)) volume) :
    (fun x => -(∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i)
        (fun y => pressureDivergenceCutoffSourceCentredTensor η dη u Du c y j) x) +
      ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i) (fun y => η y * f y j) x) =ᵐ[volume.restrict A]
    (fun x => -(∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i)
        (B.indicator (fun y => (∑ k, Du y j k * u y k) - f y j)) x) -
      ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i) (centredRawSourceCorrection B η dη u f Du c j) x) := by
  have hj (j : Fin 3) := (gradient_riesz_sub_ae j i (hV j) (hF j)).symm.trans
    (centred_riesz_eq_raw_add_correction_ae B η dη u f Du c j i (hV j) (hF j) (hG j))
  apply ae_restrict_of_ae
  filter_upwards [hj 0, hj 1, hj 2] with x h0 h1 h2
  simp only [Pi.sub_apply, Pi.add_apply] at h0 h1 h2
  simp only [Fin.sum_univ_three] at h0 h1 h2 ⊢
  linarith only [h0, h1, h2]

end CKN.Core.Step4
