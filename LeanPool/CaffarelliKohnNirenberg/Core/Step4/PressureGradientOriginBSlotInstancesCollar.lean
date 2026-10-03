/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTSuitableIdentification
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSourceQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRemainderMajorantQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBSlotEnergyMajorant
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBSlotEnergySlices
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBSlotEnergyTime
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTCaccioppoliQuantitative

/-! # The collar slice bound for the whole-carrier pressure gradient

On a collar `Q(z, ρ)` inside the unit data cylinder of `thm:A`, every weak
slice derivative of the pressure on the half ball `B(z₁, ρ/2)` is, by
`eq:pressure-gradient-decomposition`, the sum of three completed Riesz terms built from
the localized source, one smooth remainder gradient, and three completed Riesz
terms built from the localized force.  This file turns that identification
into a slice inequality between `L^{6/5}` norms in which the localized source
and the localized force have been replaced by majorants that no longer depend
on the component index.

No velocity or gradient Morrey datum enters any estimate in this file.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- The localized force slice is dominated in `L^{6/5}` by the force slice on
the collar ball, uniformly in the component index. -/
theorem cutoff_force_slice_eLpNorm_le
    {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    {s : ℝ} {j : Fin 3}
    (hmem : AEStronglyMeasurable
      (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) j) volume) :
    eLpNorm (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) j)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      eLpNorm (fun y => f (y, s)) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball z.1 ρ)) := by
  have hzero (y : Vec3) (hy : y ∉ vec3Ball z.1 ρ) : mollifiedBallCutoff z.1 hρ y = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hy (pressure_cutoff_support_subset_ball z.1 hρ h))
  have hmono : eLpNorm (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) j)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      eLpNorm ((vec3Ball z.1 ρ).indicator (fun y => f (y, s)))
        (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
    refine eLpNorm_mono_enorm hmem (fun y => ?_)
    by_cases hy : y ∈ vec3Ball z.1 ρ
    · rw [Set.indicator_of_mem hy, ← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs, abs_mul]
      refine ENNReal.ofReal_le_ofReal ?_
      have h₁ : |mollifiedBallCutoff z.1 hρ y| ≤ 1 := by
        rw [abs_of_nonneg (mollifiedBallCutoff_nonneg z.1 hρ y)]
        exact mollifiedBallCutoff_le_one z.1 hρ y
      have h₂ : |f (y, s) j| ≤ ‖f (y, s)‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (f (y, s)) j
      have h₃ : (0 : ℝ) ≤ |f (y, s) j| := abs_nonneg _
      nlinarith only [h₁, h₂, h₃, abs_nonneg (mollifiedBallCutoff z.1 hρ y)]
    · rw [hzero y hy, zero_mul, enorm_zero]
      exact bot_le
  exact hmono.trans_eq (eLpNorm_indicator_eq_eLpNorm_restrict (vec3Ball_measurable z.1 ρ))


/-- **The collar slice bound of `eq:pressure-gradient-decomposition`.**  On the half
ball of a collar inside the domain, every weak slice derivative of the pressure
has `L^{6/5}` norm at most three times the Calderón–Zygmund constant applied to
the centred source majorant, plus the smooth remainder majorant weighted by the
half-ball volume, plus three times the same constant applied to the force slice
norm on the collar ball. -/
theorem collar_slice_gradient_eLpNorm_le
    {Ω : Set Vec3} {I : Set ℝ} {q C : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hrem : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
        ‖classicalGradient
          (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
            (sourceSliceCentredMean z.1 ρ u) p s +
            pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤
          fixedRemainderSliceMajorant C ρ z.1 u f p s)
    (D : ParabolicPoint → Vec3)
    (hD : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => D (y, s) i) (vec3Ball z.1 (ρ / 2)) volume ∧
      HasWeakPartialDerivOn (vec3Ball z.1 (ρ / 2)) i
        (fun y => p (y, s)) (fun y => D (y, s) i)) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ i : Fin 3,
      eLpNorm (fun y => D (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball z.1 (ρ / 2))) ≤
      3 * ENNReal.ofReal (czGradientComponentConstant rieszSecondWeakTypeConstant 1) *
          centredSWSCentredMajorant z.1 ρ q u Du f s +
        fixedRemainderSliceMajorant C ρ z.1 u f p s *
          volume (vec3Ball z.1 (ρ / 2)) ^ ((5 : ℝ) / 6) +
        3 * ENNReal.ofReal (czGradientComponentConstant rieszSecondWeakTypeConstant 1) *
          eLpNorm (fun y => f (y, s)) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 ρ)) := by
  have hid := ae_weak_pressure_derivative_eq_fixed_riesz_of_sws hsol hρ hsub
  have hV := centredSWS_source_data_ae hsol hρ hsub (sourceSliceCentredMean z.1 ρ u)
  have hfd := slice_force_source_data_ae_of_sws hsol hρ hsub
  have hPb := centredSWS_source_bound_ae hsol hρ hsub
  dsimp only at hid
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (6 / 5 : ℝ) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  filter_upwards [hid, hV, hfd, hrem, hD, hPb] with s hids hVs hfs hrems hDs hPs
  intro i
  set μ' : Measure Vec3 := volume.restrict (vec3Ball z.1 (ρ / 2)) with hμ'
  set A : Vec3 → ℝ := fun x => -(∑ j : Fin 3, rieszSecondGradientExtensionOperator
    (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
    (fun y => sourceMorreyCutoffVCentredTensorSpacetime
      (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
      u Du (sourceSliceCentredMean z.1 ρ u) (y, s) j) x) with hA
  set Bg : Vec3 → ℝ := fun x => classicalGradient
    (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
      (sourceSliceCentredMean z.1 ρ u) p s +
      pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i with hBg
  set Cg : Vec3 → ℝ := fun x => ∑ j : Fin 3, rieszSecondGradientExtensionOperator
    (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
    (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) j) x with hCg
  have hcs (j : Fin 3) : HasCompactSupport
      (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) j) :=
    (mollifiedBallCutoff_hasCompactSupport z.1 hρ).mul_right
  have hDeq : (fun y => D (y, s) i) =ᵐ[μ'] (A + Bg + Cg) :=
    hids i (fun y => D (y, s) i) (hDs i).1 (hDs i).2
  have hAm : AEStronglyMeasurable A μ' := by
    have hrw : A = -(∑ j : Fin 3, rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
        (fun y => sourceMorreyCutoffVCentredTensorSpacetime
          (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          u Du (sourceSliceCentredMean z.1 ρ u) (y, s) j)) := by
      funext x
      simp only [hA, Pi.neg_apply, Finset.sum_apply]
    rw [hrw]
    refine AEStronglyMeasurable.neg (Finset.aestronglyMeasurable_sum _ (fun j _ => ?_))
    exact ((rieszSecondGradientExtension_memLp (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) (hVs.1 j) (hVs.2 j)).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hCm : AEStronglyMeasurable Cg μ' := by
    have hrw : Cg = ∑ j : Fin 3, rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
        (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) j) := by
      funext x
      simp only [hCg, Finset.sum_apply]
    rw [hrw]
    refine Finset.aestronglyMeasurable_sum _ (fun j _ => ?_)
    exact ((rieszSecondGradientExtension_memLp (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i) (hfs.2.1 j) (hcs j)).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have hsumm : AEStronglyMeasurable (A + Bg + Cg) μ' :=
    ((hDs i).1.aestronglyMeasurable).congr hDeq
  have hBm : AEStronglyMeasurable Bg μ' := by
    have heq : Bg = (A + Bg + Cg) - A - Cg := by
      funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [heq]
    exact (hsumm.sub hAm).sub hCm
  rw [eLpNorm_congr_ae hDeq]
  refine le_trans (eLpNorm_add_le hp1) (add_le_add (le_trans (eLpNorm_add_le hp1)
    (add_le_add ?_ ?_)) ?_)
  · rw [hA]
    have hneg : eLpNorm (fun x => -(∑ j : Fin 3, rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
        (fun y => sourceMorreyCutoffVCentredTensorSpacetime
          (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          u Du (sourceSliceCentredMean z.1 ρ u) (y, s) j) x)) (ENNReal.ofReal (6 / 5 : ℝ)) μ' =
        eLpNorm (∑ j : Fin 3, rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
          (fun y => sourceMorreyCutoffVCentredTensorSpacetime
            (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
            u Du (sourceSliceCentredMean z.1 ρ u) (y, s) j)) (ENNReal.ofReal (6 / 5 : ℝ)) μ' := by
      rw [← eLpNorm_neg]
      congr 1
      funext x
      simp only [Pi.neg_apply, Finset.sum_apply, neg_neg]
    rw [hneg]
    refine le_trans (eLpNorm_sum_le hp1) ?_
    refine le_trans (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans
        (pressure_riesz_component_eLpNorm_bound j i (hVs.1 j) (hVs.2 j))).trans
        (mul_le_mul' le_rfl (hPs j)))) ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat]
    exact le_of_eq (mul_assoc _ _ _).symm
  · have hbd : ∀ᵐ x ∂μ', ‖Bg x‖ₑ ≤ fixedRemainderSliceMajorant C ρ z.1 u f p s := by
      rw [hμ']
      refine (ae_restrict_iff' (vec3Ball_measurable _ _)).mpr (Filter.Eventually.of_forall ?_)
      intro x hx
      exact hrems i x hx
    have hexp : (ENNReal.ofReal (6 / 5 : ℝ)).toReal⁻¹ = (5 : ℝ) / 6 := by
      rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 5)]
      norm_num
    have huniv : μ' Set.univ = volume (vec3Ball z.1 (ρ / 2)) := by
      rw [hμ', Measure.restrict_apply_univ]
    have h := eLpNorm_le_of_ae_enorm_bound (p := ENNReal.ofReal (6 / 5 : ℝ)) hBm hbd
    rw [smul_eq_mul, hexp, huniv] at h
    exact h
  · rw [hCg]
    have heq : (fun x => ∑ j : Fin 3, rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
        (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) j) x) =
        ∑ j : Fin 3, rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
          (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) j) := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq]
    refine le_trans (eLpNorm_sum_le hp1) ?_
    refine le_trans (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans
        (pressure_riesz_component_eLpNorm_bound j i (hfs.2.1 j) (hcs j))).trans
        (mul_le_mul' le_rfl (cutoff_force_slice_eLpNorm_le hρ
          (hfs.2.1 j).aestronglyMeasurable)))) ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat]
    exact le_of_eq (mul_assoc _ _ _).symm

/-- The `6/5` time mass of the force slice norms on a collar costs the collar
volume in addition to the unit data of `thm:A`. -/
theorem collar_force_slice_six_fifths_mass_le
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {q ε : ℝ} (hq : 6 / 5 ≤ q)
    {E : Set Vec3} {J : Set ℝ}
    (hsub : E ×ˢ J ⊆ parabolicCylinder (0 : Vec3) 0 1)
    (hf : AEStronglyMeasurable f (volume.restrict (E ×ˢ J)))
    (hsize : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) :
    (∫⁻ s in J, eLpNorm (fun y => f (y, s)) (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict E) ^ (6 / 5 : ℝ)) ≤ volume (E ×ˢ J) + ENNReal.ofReal ε := by
  rw [vector_time_slice_norm_power_eq (by norm_num : (0 : ℝ) < 6 / 5) hf]
  calc (∫⁻ w in E ×ˢ J, ENNReal.ofReal ‖f w‖ ^ (6 / 5 : ℝ))
      ≤ (volume.restrict (E ×ˢ J)) Set.univ +
        ∫⁻ w in E ×ˢ J, ENNReal.ofReal ‖f w‖ ^ q :=
        lintegral_rpow_le_measure_add_lintegral_rpow _ _ (by norm_num) hq
    _ ≤ volume (E ×ˢ J) + ENNReal.ofReal ε := by
        rw [Measure.restrict_apply_univ]
        refine add_le_add le_rfl ?_
        calc (∫⁻ w in E ×ˢ J, ENNReal.ofReal ‖f w‖ ^ q)
            ≤ ∫⁻ w in E ×ˢ J, ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q :=
              lintegral_mono fun w => ENNReal.rpow_le_rpow
                (ENNReal.ofReal_le_ofReal (norm_le_vec3EuclideanNorm (f w)))
                (by linarith only [hq])
          _ ≤ ∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
                ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := lintegral_mono_set hsub
          _ ≤ _ := (lintegral_mono fun w => le_add_left le_rfl).trans hsize

/-- A slice bound of the shape produced by `eq:pressure-gradient-decomposition` turns
three separate time masses into one, with the numerical factor of the
three-term power split. -/
theorem time_mass_of_three_slice_bounds
    {J : Set ℝ} {N G M H : ℝ → ℝ≥0∞} {K W EG EM EH : ℝ≥0∞}
    (hG : AEMeasurable G (volume.restrict J)) (hM : AEMeasurable M (volume.restrict J))
    (hH : AEMeasurable H (volume.restrict J)) (hK : K ≠ ⊤) (hW : W ≠ ⊤)
    (hN : ∀ᵐ s ∂volume.restrict J, N s ≤ K * G s + M s * W ^ ((5 : ℝ) / 6) + K * H s)
    (hEG : (∫⁻ s in J, G s ^ (6 / 5 : ℝ)) ≤ EG)
    (hEM : (∫⁻ s in J, M s ^ (6 / 5 : ℝ)) ≤ EM)
    (hEH : (∫⁻ s in J, H s ^ (6 / 5 : ℝ)) ≤ EH) :
    (∫⁻ s in J, N s ^ (6 / 5 : ℝ)) ≤
      4 * (K ^ (6 / 5 : ℝ) * EG + W * EM + K ^ (6 / 5 : ℝ) * EH) := by
  have hKtop : K ^ (6 / 5 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK
  have hWpow : (W ^ ((5 : ℝ) / 6)) ^ (6 / 5 : ℝ) = W := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hmX : AEMeasurable (fun s => K ^ (6 / 5 : ℝ) * G s ^ (6 / 5 : ℝ))
      (volume.restrict J) := aemeasurable_const.mul (hG.pow_const _)
  have hmY : AEMeasurable (fun s => W * M s ^ (6 / 5 : ℝ)) (volume.restrict J) :=
    aemeasurable_const.mul (hM.pow_const _)
  have hmZ : AEMeasurable (fun s => K ^ (6 / 5 : ℝ) * H s ^ (6 / 5 : ℝ))
      (volume.restrict J) := aemeasurable_const.mul (hH.pow_const _)
  calc (∫⁻ s in J, N s ^ (6 / 5 : ℝ))
      ≤ ∫⁻ s in J, 4 * (K ^ (6 / 5 : ℝ) * G s ^ (6 / 5 : ℝ) + W * M s ^ (6 / 5 : ℝ) +
          K ^ (6 / 5 : ℝ) * H s ^ (6 / 5 : ℝ)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hN] with s hs
        refine (ENNReal.rpow_le_rpow hs (by norm_num)).trans ?_
        refine (three_add_rpow_six_fifths_le _ _ _).trans (le_of_eq ?_)
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6 / 5),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6 / 5),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6 / 5), hWpow]
        ring
    _ = 4 * ((∫⁻ s in J, K ^ (6 / 5 : ℝ) * G s ^ (6 / 5 : ℝ)) +
          (∫⁻ s in J, W * M s ^ (6 / 5 : ℝ)) +
          ∫⁻ s in J, K ^ (6 / 5 : ℝ) * H s ^ (6 / 5 : ℝ)) := by
        rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
          lintegral_add_right' _ hmZ, lintegral_add_right' _ hmY]
    _ = 4 * (K ^ (6 / 5 : ℝ) * (∫⁻ s in J, G s ^ (6 / 5 : ℝ)) +
          W * (∫⁻ s in J, M s ^ (6 / 5 : ℝ)) +
          K ^ (6 / 5 : ℝ) * ∫⁻ s in J, H s ^ (6 / 5 : ℝ)) := by
        rw [lintegral_const_mul' _ _ hKtop, lintegral_const_mul' _ _ hW,
          lintegral_const_mul' _ _ hKtop]
    _ ≤ _ := by gcongr

/-- The explicit absolute coefficient of the collar time mass of
`prop:bootstrap`.  Every factor is a fixed function of the collar radius and
of the harmonic remainder constant; none depends on the force exponent, on the
Morrey exponent, on the radii of the carrier, on the data size, or on the
solution. -/
@[expose]
def bslotCollarConstant (C ρ : ℝ) : ℝ≥0∞ :=
  4 * ((3 * ENNReal.ofReal
          (czGradientComponentConstant rieszSecondWeakTypeConstant 1)) ^ (6 / 5 : ℝ) *
        (4 * ((18 : ℝ≥0∞) ^ (6 / 5 : ℝ) *
              (1 + ENNReal.ofReal (interiorDirichletDataConstant (2 * ρ))) +
            (18 * ENNReal.ofReal (cutoffGradientConstant / ρ) *
                volume (vec3Ball (0 : Vec3) ρ) ^ (1 / 6 : ℝ)) ^ (6 / 5 : ℝ) *
              (ENNReal.ofReal (ρ ^ 2) + 1) +
            (4 * volume (vec3Ball (0 : Vec3) ρ) ^ (13 / 30 : ℝ)) ^ (6 / 5 : ℝ) *
              (ENNReal.ofReal (ρ ^ 2) + 1))) +
      volume (vec3Ball (0 : Vec3) (ρ / 2)) *
        (ENNReal.ofReal (ρ ^ 2) + fixedRemainderMomentConstant C ρ 0) +
      (3 * ENNReal.ofReal
          (czGradientComponentConstant rieszSecondWeakTypeConstant 1)) ^ (6 / 5 : ℝ) *
        (volume (parabolicCylinder (0 : Vec3) 0 ρ) + 1))

/-- **The collar time mass of the weak pressure gradient.**  On a collar whose
doubled cylinder stays inside the unit data cylinder of `thm:A`, the `6/5` time
mass of any weak slice derivative of the pressure on the collar half ball is at
most an explicit absolute multiple of `ε + 1`. -/
theorem collar_gradient_time_mass_le
    (C ε : ℝ) (hε : 0 ≤ ε)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hsmall : (∫⁻ w in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal ε)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : 2 * ρ ≤ 1)
    (hW : volume (vec3Ball (0 : Vec3) ρ) ≤ 1)
    (hQ : parabolicCylinder z.1 z.2 (2 * ρ) ⊆ parabolicCylinder (0 : Vec3) 0 1)
    (hrem : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
        ‖classicalGradient
          (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
            (sourceSliceCentredMean z.1 ρ u) p s +
            pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤
          fixedRemainderSliceMajorant C ρ z.1 u f p s)
    (D : ParabolicPoint → Vec3)
    (hD : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => D (y, s) i) (vec3Ball z.1 (ρ / 2)) volume ∧
      HasWeakPartialDerivOn (vec3Ball z.1 (ρ / 2)) i
        (fun y => p (y, s)) (fun y => D (y, s) i))
    (i : Fin 3) :
    (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2,
      eLpNorm (fun y => D (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball z.1 (ρ / 2))) ^ (6 / 5 : ℝ)) ≤
      bslotCollarConstant C ρ * (ENNReal.ofReal ε + 1) := by
  have hq := hsol.2.2.2.1
  set B : Set Vec3 := vec3Ball z.1 ρ with hB
  set J : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2 with hJ
  have hbox : B ×ˢ J = parabolicCylinder z.1 z.2 ρ := rfl
  have hQsmall : parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 1 :=
    (parabolicCylinder_mono hρ.le (by linarith only [hρ] : ρ ≤ 2 * ρ)).trans hQ
  have hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I :=
    (closure_mono hQsmall).trans hdom
  -- measurability of the data on the collar
  obtain ⟨Ω', J', hlb, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J' hlb
  have hsubST : B ×ˢ J ⊆ spaceTimeSet Ω' J' := prod_mono hball htime
  have hum : AEStronglyMeasurable u (volume.restrict (B ×ˢ J)) :=
    hdata.1.mono_measure (Measure.restrict_mono_set volume hsubST)
  have hdm : AEStronglyMeasurable Du (volume.restrict (B ×ˢ J)) :=
    hdata.2.1.mono_measure (Measure.restrict_mono_set volume hsubST)
  have hfm : AEStronglyMeasurable f (volume.restrict (B ×ˢ J)) :=
    hdata.2.2.2.1.mono_measure (Measure.restrict_mono_set volume hsubST)
  have h3 : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num
  set a : ℝ → ℝ≥0∞ := fun s => eLpNorm (fun y => u (y, s)) 3 (volume.restrict B) with ha
  set d : ℝ → ℝ≥0∞ := fun s => eLpNorm (fun y => Du (y, s)) 2 (volume.restrict B) with hd
  set F : ℝ → ℝ≥0∞ :=
    fun s => eLpNorm (fun y => f (y, s)) (ENNReal.ofReal q) (volume.restrict B) with hF
  set H : ℝ → ℝ≥0∞ :=
    fun s => eLpNorm (fun y => f (y, s)) (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict B) with hHdef
  set M : ℝ → ℝ≥0∞ := fixedRemainderSliceMajorant C ρ z.1 u f p with hM
  have hma : AEMeasurable a (volume.restrict J) := by
    have h := vector_time_slice_norm_aemeasurable (P := (3 : ℝ)) (by norm_num) hum
    rw [h3] at h
    exact h
  have hmd : AEMeasurable d (volume.restrict J) := by
    have h := vector_time_slice_norm_aemeasurable (P := (2 : ℝ)) (by norm_num) hdm
    rw [h2] at h
    exact h
  have hmF : AEMeasurable F (volume.restrict J) :=
    vector_time_slice_norm_aemeasurable (P := q) (by linarith only [hq]) hfm
  have hmH : AEMeasurable H (volume.restrict J) :=
    vector_time_slice_norm_aemeasurable (P := (6 / 5 : ℝ)) (by norm_num) hfm
  have hmM : AEMeasurable M (volume.restrict J) :=
    (fixed_remainder_slice_majorant_moment_of_sws C ε hsol hdom hsmall hQsmall).1
  -- the three-term source majorant
  set c₂ : ℝ≥0∞ := 18 * ENNReal.ofReal (cutoffGradientConstant / ρ) *
    volume (vec3Ball z.1 ρ) ^ (1 / 6 : ℝ) with hc₂
  set c₃ : ℝ≥0∞ := 4 * volume (vec3Ball z.1 ρ) ^ (5 / 6 - 1 / q : ℝ) with hc₃
  set G : ℝ → ℝ≥0∞ := fun s => 18 * (a s * d s) + c₂ * a s ^ (2 : ℝ) + c₃ * F s with hG
  have hmG : AEMeasurable G (volume.restrict J) :=
    ((aemeasurable_const.mul (hma.mul hmd)).add
      (aemeasurable_const.mul (hma.pow_const _))).add (aemeasurable_const.mul hmF)
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J) =
      (volume.restrict B).prod (volume.restrict J) := by
    rw [volume_eq_prod, ← Measure.prod_restrict]
  have huslice : ∀ᵐ s ∂volume.restrict J,
      AEStronglyMeasurable (fun y => u (y, s)) (volume.restrict B) := by
    have h : AEStronglyMeasurable u ((volume.restrict B).prod (volume.restrict J)) := by
      rw [← hprod]
      exact hum
    exact h.prodMk_right
  -- the slice bound in the shape of the three-mass lemma
  have hN : ∀ᵐ s ∂volume.restrict J, ∀ k : Fin 3,
      eLpNorm (fun y => D (y, s) k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball z.1 (ρ / 2))) ≤
      (3 * ENNReal.ofReal
        (czGradientComponentConstant rieszSecondWeakTypeConstant 1)) * G s +
        M s * volume (vec3Ball z.1 (ρ / 2)) ^ ((5 : ℝ) / 6) +
        (3 * ENNReal.ofReal
          (czGradientComponentConstant rieszSecondWeakTypeConstant 1)) * H s := by
    filter_upwards [collar_slice_gradient_eLpNorm_le hsol hρ hsub hrem D hD, huslice]
      with s hs hus
    intro k
    refine (hs k).trans (add_le_add (add_le_add (mul_le_mul' le_rfl ?_) le_rfl) le_rfl)
    exact centredSWSCentredMajorant_le_three_terms hρ q u Du f s hus
  -- the three time masses
  have hEa : (∫⁻ s in J, a s ^ (3 : ℝ)) ≤ ENNReal.ofReal ε := by
    have h := collar_velocity_slice_cube_mass_le (u := u) (p := p) (f := f)
      (q := q) (ε := ε) (E := B) (J := J) (hbox ▸ hQsmall) hum hsmall
    rw [h3] at h
    exact h
  have hEf : (∫⁻ s in J, F s ^ q) ≤ ENNReal.ofReal ε :=
    collar_force_slice_power_mass_le (u := u) (p := p) (f := f) (q := q) (ε := ε)
      (by linarith only [hq]) (E := B) (J := J) (hbox ▸ hQsmall) hfm hsmall
  have hDir : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (spatialGradientSq u Du w)) ≤
      ENNReal.ofReal (interiorDirichletDataConstant (2 * ρ)) * (ENNReal.ofReal ε + 1) := by
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      interior_dirichlet_bound_of_unit_data ε hε (by positivity : 0 < 2 * ρ) hρ1
        hsol hdom hsmall hQ
  have hEd : (∫⁻ s in J, d s ^ (2 : ℝ)) ≤
      ENNReal.ofReal (interiorDirichletDataConstant (2 * ρ)) * (ENNReal.ofReal ε + 1) := by
    have h := collar_gradient_slice_square_mass_le (u := u) (Du := Du) (E := B) (J := J) hdm
    rw [h2] at h
    exact h.trans (by rw [hbox]; exact hDir)
  have hJvol : volume J = ENNReal.ofReal (ρ ^ 2) := by
    rw [hJ, Real.volume_Ioc]
    congr 1
    ring
  have hEG := slice_majorant_time_mass_le (J := J) (M := G) (a := a) (d := d) (F := F)
    (c₁ := 18) (c₂ := c₂) (c₃ := c₃) (qq := q) hma hmd hmF (by linarith only [hq])
    (Filter.Eventually.of_forall (fun s => le_rfl)) hEa hEd hEf
  have hEM : (∫⁻ s in J, M s ^ (6 / 5 : ℝ)) ≤
      (ENNReal.ofReal (ρ ^ 2) + fixedRemainderMomentConstant C ρ z.1) *
        (ENNReal.ofReal ε + 1) := by
    have h := fixed_remainder_clipped_moment_of_sws C ε hsol hdom hsmall hQsmall Set.univ
    rwa [Set.inter_univ] at h
  have hEH : (∫⁻ s in J, H s ^ (6 / 5 : ℝ)) ≤
      volume (parabolicCylinder z.1 z.2 ρ) + ENNReal.ofReal ε := by
    have h := collar_force_slice_six_fifths_mass_le (u := u) (p := p) (f := f)
      (q := q) (ε := ε) (by linarith only [hq]) (E := B) (J := J)
      (hbox ▸ hQsmall) hfm hsmall
    rwa [hbox] at h
  -- assemble
  have hKtop : (3 * ENNReal.ofReal
      (czGradientComponentConstant rieszSecondWeakTypeConstant 1)) ≠ ⊤ := by finiteness
  have hWtop : volume (vec3Ball z.1 (ρ / 2)) ≠ ⊤ :=
    (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top).ne
  have hmain := time_mass_of_three_slice_bounds (J := J)
    (N := fun s => eLpNorm (fun y => D (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (vec3Ball z.1 (ρ / 2)))) (G := G) (M := M) (H := H)
    hmG hmM hmH hKtop hWtop (hN.mono (fun s hs => hs i)) hEG hEM hEH
  refine hmain.trans ?_
  have hA1 : ENNReal.ofReal ε +
      ENNReal.ofReal (interiorDirichletDataConstant (2 * ρ)) * (ENNReal.ofReal ε + 1) ≤
      (1 + ENNReal.ofReal (interiorDirichletDataConstant (2 * ρ))) *
        (ENNReal.ofReal ε + 1) := by
    rw [add_mul, one_mul]
    exact add_le_add le_self_add le_rfl
  have hA2 : volume J + ENNReal.ofReal ε ≤
      (ENNReal.ofReal (ρ ^ 2) + 1) * (ENNReal.ofReal ε + 1) := by
    rw [hJvol, add_mul, one_mul]
    exact add_le_add (le_mul_of_one_le_right' le_add_self) le_self_add
  have hA3 : volume (parabolicCylinder z.1 z.2 ρ) + ENNReal.ofReal ε ≤
      (volume (parabolicCylinder (0 : Vec3) 0 ρ) + 1) * (ENNReal.ofReal ε + 1) := by
    rw [show volume (parabolicCylinder z.1 z.2 ρ) =
        volume (parabolicCylinder (0 : Vec3) 0 ρ) by
      rw [volume_parabolicCylinder_zero z.1 z.2 ρ,
        volume_parabolicCylinder_zero (0 : Vec3) 0 ρ], add_mul, one_mul]
    exact add_le_add (le_mul_of_one_le_right' le_add_self) le_self_add
  have hc3 : c₃ ^ (6 / 5 : ℝ) ≤
      (4 * volume (vec3Ball (0 : Vec3) ρ) ^ (13 / 30 : ℝ)) ^ (6 / 5 : ℝ) := by
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [hc₃, volume_vec3Ball z.1 ρ]
    refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow_of_exponent_ge hW ?_)
    have hq0 : (0 : ℝ) < q := by linarith only [hq]
    have hinv : (1 : ℝ) / q < 2 / 5 := by
      rw [div_lt_div_iff₀ hq0 (by norm_num)]
      linarith only [hq]
    linarith only [hinv]
  have hc2 : c₂ ^ (6 / 5 : ℝ) =
      (18 * ENNReal.ofReal (cutoffGradientConstant / ρ) *
        volume (vec3Ball (0 : Vec3) ρ) ^ (1 / 6 : ℝ)) ^ (6 / 5 : ℝ) := by
    rw [hc₂, volume_vec3Ball z.1 ρ]
  have hmom : fixedRemainderMomentConstant C ρ z.1 =
      fixedRemainderMomentConstant C ρ 0 := by
    unfold fixedRemainderMomentConstant
    rw [volume_vec3Ball z.1 ρ]
  rw [hc2, hmom, volume_vec3Ball z.1 (ρ / 2)]
  unfold bslotCollarConstant
  calc 4 * ((3 * ENNReal.ofReal
        (czGradientComponentConstant rieszSecondWeakTypeConstant 1)) ^ (6 / 5 : ℝ) *
        (4 * ((18 : ℝ≥0∞) ^ (6 / 5 : ℝ) * (ENNReal.ofReal ε +
              ENNReal.ofReal (interiorDirichletDataConstant (2 * ρ)) *
                (ENNReal.ofReal ε + 1)) +
            (18 * ENNReal.ofReal (cutoffGradientConstant / ρ) *
              volume (vec3Ball (0 : Vec3) ρ) ^ (1 / 6 : ℝ)) ^ (6 / 5 : ℝ) *
              (volume J + ENNReal.ofReal ε) +
            c₃ ^ (6 / 5 : ℝ) * (volume J + ENNReal.ofReal ε))) +
      volume (vec3Ball (0 : Vec3) (ρ / 2)) *
        ((ENNReal.ofReal (ρ ^ 2) + fixedRemainderMomentConstant C ρ 0) *
          (ENNReal.ofReal ε + 1)) +
      (3 * ENNReal.ofReal
        (czGradientComponentConstant rieszSecondWeakTypeConstant 1)) ^ (6 / 5 : ℝ) *
        (volume (parabolicCylinder z.1 z.2 ρ) + ENNReal.ofReal ε))
      ≤ 4 * ((3 * ENNReal.ofReal
        (czGradientComponentConstant rieszSecondWeakTypeConstant 1)) ^ (6 / 5 : ℝ) *
        (4 * ((18 : ℝ≥0∞) ^ (6 / 5 : ℝ) *
              ((1 + ENNReal.ofReal (interiorDirichletDataConstant (2 * ρ))) *
                (ENNReal.ofReal ε + 1)) +
            (18 * ENNReal.ofReal (cutoffGradientConstant / ρ) *
              volume (vec3Ball (0 : Vec3) ρ) ^ (1 / 6 : ℝ)) ^ (6 / 5 : ℝ) *
              ((ENNReal.ofReal (ρ ^ 2) + 1) * (ENNReal.ofReal ε + 1)) +
            (4 * volume (vec3Ball (0 : Vec3) ρ) ^ (13 / 30 : ℝ)) ^ (6 / 5 : ℝ) *
              ((ENNReal.ofReal (ρ ^ 2) + 1) * (ENNReal.ofReal ε + 1)))) +
      volume (vec3Ball (0 : Vec3) (ρ / 2)) *
        ((ENNReal.ofReal (ρ ^ 2) + fixedRemainderMomentConstant C ρ 0) *
          (ENNReal.ofReal ε + 1)) +
      (3 * ENNReal.ofReal
        (czGradientComponentConstant rieszSecondWeakTypeConstant 1)) ^ (6 / 5 : ℝ) *
        ((volume (parabolicCylinder (0 : Vec3) 0 ρ) + 1) * (ENNReal.ofReal ε + 1))) := by
        gcongr
    _ = _ := by ring

end CKN.Core.Step4
