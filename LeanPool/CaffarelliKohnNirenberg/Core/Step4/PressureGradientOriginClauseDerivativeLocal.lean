/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTDecompositionMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseGrowth

/-!
# Fixed derivative decomposition on backward local cylinders

The fixed-source construction is applied on an arbitrary backward cylinder,
including cylinders ending at the final carrier time. The source argument
specializes the same-repository fixed-source Morrey estimates to this geometry.
The selected derivative is retained in the signed Riesz and remainder identity.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat
open CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

private theorem derivative_local_source
    {τ q : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτhi : τ ≤ 25)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hbox : localBox Ω I (vec3Ball z.1 ρ) (Ioc (z.2 - ρ ^ 2) z.2))
    (hU : ∀ j, morreyNorm 3 τ
      ((parabolicCylinder z.1 z.2 ρ).indicator (fun w => u w j)) < ⊤)
    (hD : ∀ j k, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder z.1 z.2 ρ).indicator (fun w => Du w j k)) < ⊤)
    (i : Fin 3) :
    morreyNorm (6/5 : ℝ) (min ((1/τ+8/25)⁻¹) q)
      ((parabolicCylinder z.1 z.2 ρ).indicator (fun w =>
        sourceMorreyCutoffVCentredTensorSpacetime (mollifiedBallCutoff z.1 hρ)
          (spatialDeriv (mollifiedBallCutoff z.1 hρ)) u Du
          (sourceSliceCentredMean z.1 ρ u) w i)) < ⊤ := by
  let Q := parabolicCylinder z.1 z.2 ρ
  let B := vec3Ball z.1 ρ
  let J := Ioc (z.2-ρ^2) z.2
  let η := mollifiedBallCutoff z.1 hρ
  have hQ : MeasurableSet Q := measurableSet_parabolicCylinder _ _ _
  have hQbox : Q ⊆ B ×ˢ J := Subset.rfl
  have hτ3 : 3 ≤ τ := by linarith only [hτ]
  have hW := pressure_centred_velocity_morrey_data_of_sws hτ3 hsol hbox hQ hQbox hU
  have hdata := hsol.2.2.2.2.2.1 B J hbox
  have hUa (j : Fin 3) : AEMeasurable (Q.indicator (fun w => u w j)) volume :=
    (aemeasurable_indicator_iff hQ).mpr
      (((measurable_pi_apply j).comp_aemeasurable hdata.1.aemeasurable).mono_measure
        (Measure.restrict_mono_set volume hQbox))
  have hDa (j k : Fin 3) : AEMeasurable (Q.indicator (fun w => Du w j k)) volume :=
    (aemeasurable_indicator_iff hQ).mpr
      (((measurable_pi_apply k).comp_aemeasurable
        ((measurable_pi_apply j).comp_aemeasurable hdata.2.1.aemeasurable)).mono_measure
        (Measure.restrict_mono_set volume hQbox))
  have hη : AEMeasurable (fun w : ParabolicPoint => η w.1) volume :=
    ((mollifiedBallCutoff_smooth z.1 hρ).continuous.measurable.comp measurable_fst).aemeasurable
  have hdη (j : Fin 3) : AEMeasurable (fun w : ParabolicPoint => spatialDeriv η j w.1) volume :=
    ((contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth z.1 hρ) j).continuous.measurable.comp
      measurable_fst).aemeasurable
  have he (x : Vec3) : |η x| ≤ |(1 : ℝ)| := by
    rw [abs_of_nonneg (mollifiedBallCutoff_nonneg z.1 hρ x), abs_one]
    exact mollifiedBallCutoff_le_one z.1 hρ x
  have hd (j : Fin 3) (x : Vec3) : |spatialDeriv η j x| ≤ |cutoffGradientConstant / ρ| :=
    ((abs_apply_le_vecEuclideanNorm (classicalGradient η x) j).trans
      (mollifiedBallCutoff_gradient_bound z.1 hρ x)).trans (le_abs_self _)
  apply pressure_centred_tensor_source_morrey_lt_top
    (S := Q) (η := η) (dη := spatialDeriv η) (u := u) (Du := Du)
    (c := sourceSliceCentredMean z.1 ρ u)
    (z₀ := z) hτ
    (le_trans (by norm_num) (endgame_kappa_ge hτ hq))
    (endgame_kappa_le (by linarith only [hτ]) hτhi) (min_le_left _ _) hρ
    (Subset.rfl : Q ⊆ Q) hη hdη he hd hUa
    (fun j => (hW j).1) hDa hU (fun j => (hW j).2) hD i

private theorem derivative_local_force
    {κ q : ℝ} (hκ : 6 / 5 ≤ κ) (hκq : κ ≤ q)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hbox : localBox Ω I (vec3Ball z.1 ρ) (Ioc (z.2 - ρ ^ 2) z.2)) (j : Fin 3) :
    morreyNorm (6/5 : ℝ) κ
      ((parabolicCylinder z.1 z.2 ρ).indicator
        (fun w => mollifiedBallCutoff z.1 hρ w.1 * f w j)) < ⊤ := by
  let Q := parabolicCylinder z.1 z.2 ρ
  let B := vec3Ball z.1 ρ
  let J := Ioc (z.2-ρ^2) z.2
  let η := mollifiedBallCutoff z.1 hρ
  have hQ : MeasurableSet Q := measurableSet_parabolicCylinder _ _ _
  have hQbox : Q ⊆ B ×ˢ J := Subset.rfl
  have hdata := hsol.2.2.2.2.2.1 B J hbox
  have hfq : MemLp (fun w => f w j) (ENNReal.ofReal q) (volume.restrict Q) :=
    (hdata.2.2.2.2.2.2.2.1.eval j).mono_measure (Measure.restrict_mono_set volume hQbox)
  have hQfinite : volume Q < ⊤ := by
    rw [volume_parabolicCylinder]
    exact ENNReal.mul_lt_top (Integration.volume_vec3Ball_lt_top) ENNReal.ofReal_lt_top
  let : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.mpr hQfinite.ne
  have hfk : MemLp (fun w => f w j) (ENNReal.ofReal κ) (volume.restrict Q) :=
    hfq.mono_exponent (ENNReal.ofReal_le_ofReal hκq)
  have hη : Measurable (fun w : ParabolicPoint => η w.1) :=
    (mollifiedBallCutoff_smooth z.1 hρ).continuous.measurable.comp measurable_fst
  have hprod : MemLp (fun w => η w.1 * f w j) (ENNReal.ofReal κ) (volume.restrict Q) := by
    apply hfk.of_le (hη.aestronglyMeasurable.mul hfk.aestronglyMeasurable)
    exact Eventually.of_forall fun w => by
      have he : ‖η w.1‖ ≤ 1 :=
        (abs_of_nonneg (mollifiedBallCutoff_nonneg z.1 hρ w.1)).le.trans
          (mollifiedBallCutoff_le_one z.1 hρ w.1)
      exact (norm_mul (η w.1) (f w j)).le.trans
        (mul_le_of_le_one_left (norm_nonneg _) he)
  exact pressure_source_morrey_lt_top_of_memLp (by norm_num) hκ
    ((memLp_indicator_iff_restrict hQ).mpr hprod)

/-- On one backward cylinder, the fixed harmonic/far temporal envelope gives
Morrey control of the same selected weak derivative on its spatial half-ball.
The source and force classes are derived from suitability and the stated
velocity and gradient Morrey data on the localization cylinder. -/
theorem originClause_local_derivative_morrey_of_remainder
    {τ q : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτhi : τ ≤ 25)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hrem : ∃ M : ℝ → ℝ≥0∞, AEMeasurable M volume ∧
      (∫⁻ s, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
      ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
        ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ/2),
          ‖classicalGradient
            (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
              (sourceSliceCentredMean z.1 ρ u) p s +
              pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s)
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hbox : localBox Ω I (vec3Ball z.1 ρ) (Ioc (z.2-ρ^2) z.2))
    (hU : ∀ j, morreyNorm 3 τ
      ((parabolicCylinder z.1 z.2 ρ).indicator (fun w => u w j)) < ⊤)
    (hD : ∀ j k, morreyNorm 2 (25/8 : ℝ)
      ((parabolicCylinder z.1 z.2 ρ).indicator (fun w => Du w j k)) < ⊤)
    {Dp : ParabolicPoint → Vec3} (hDp : Measurable Dp)
    (hweak : ∀ᵐ s ∂volume.restrict (Ioc (z.2-ρ^2) z.2), ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball z.1 (ρ/2)) volume ∧
      HasWeakPartialDerivOn (vec3Ball z.1 (ρ/2)) i (fun y => p (y,s))
        (fun y => Dp (y,s) i)) :
    ∀ i : Fin 3, morreyNorm (6/5 : ℝ) (min ((1/τ+8/25)⁻¹) q)
      ((vec3Ball z.1 (ρ/2) ×ˢ Ioc (z.2-ρ^2) z.2).indicator (fun w => Dp w i)) < ⊤ := by
  let κ := min ((1/τ+8/25)⁻¹) q
  let S := vec3Ball z.1 (ρ/2) ×ˢ Ioc (z.2-ρ^2) z.2
  have hκlo := endgame_kappa_ge hτ hq
  have hκhi := endgame_kappa_le (q := q) (by linarith only [hτ]) hτhi
  have hκP : 6/5 ≤ κ := le_trans (by norm_num) hκlo
  have hκpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκlo
  obtain ⟨T, F, ht, hf, hti, hfi⟩ := exists_measurable_fixed_riesz_fields_of_sws hsol hρ hsub
  have hm := fixed_pressure_sources_aemeasurable_of_sws hsol hρ hsub
  have hv := centredSWS_source_data_ae hsol hρ hsub (sourceSliceCentredMean z.1 ρ u)
  have hfs := slice_force_source_data_ae_of_sws hsol hρ hsub
  have htN (j i : Fin 3) : morreyNorm (6/5 : ℝ) κ (T j i) < ⊤ :=
    window_riesz_field_morrey_lt_top j i hκpos hκhi hρ measurableSet_Ioc
      (hm j).1 (hv.mono (fun _ hs => hs.1 j)) (ht j i).aemeasurable (hti j i)
      (derivative_local_source hq hτ hτhi hsol hρ hbox hU hD j)
  have hfN (j i : Fin 3) : morreyNorm (6/5 : ℝ) κ (F j i) < ⊤ :=
    window_riesz_field_morrey_lt_top j i hκpos hκhi hρ measurableSet_Ioc
      (hm j).2 (hfs.mono (fun _ hs => hs.2.1 j)) (hf j i).aemeasurable (hfi j i)
      (derivative_local_force hκP (min_le_right _ _) hsol hρ hbox j)
  let H := fun i w => Dp w i + (∑ j, T j i w) - ∑ j, F j i w
  have hh (i : Fin 3) : Measurable (H i) :=
    (((measurable_pi_apply i).comp hDp).add
      (Finset.measurable_sum _ (fun j _ => ht j i))).sub
      (Finset.measurable_sum _ (fun j _ => hf j i))
  have heq := ae_fixed_remainder_eq_classical_gradient hsol hρ hsub
    measurableSet_Ioc Subset.rfl hweak hti hfi
  obtain ⟨M, hM, hMn, hMb⟩ := hrem
  have hHN (i : Fin 3) : morreyNorm (6/5 : ℝ) κ (S.indicator (H i)) < ⊤ := by
    apply pressure_remainder_indicator_morrey_lt_top_of_ae_slice_bound
      (le_trans (by norm_num) hκlo) hκhi (hh i) hM
      ((isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioc)
      (fun w hw => hw.1) (isOpen_vec3Ball _ _).measurableSet
      Integration.volume_vec3Ball_lt_top ?_ hMn
    apply ae_spatial_bound_on_product_of_restricted_slices
      (isOpen_vec3Ball _ _).measurableSet measurableSet_Ioc
    filter_upwards [heq, hMb] with s hs hb
    filter_upwards [hs i, ae_restrict_mem (isOpen_vec3Ball _ _).measurableSet] with y hy hyB
    dsimp only [H]
    rw [hy]
    exact hb i y hyB
  have hN := morreyVecMem_of_signed_pressure_decomposition hκP
    ((isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioc) ht hf hh htN hfN hHN
    (Dp := Dp) (fun i => Eventually.of_forall (fun w => by dsimp only [H]; ring))
  intro i
  exact (morreyNorm_le_morreyBallNorm (by norm_num) hκP _).trans_lt (hN i)

end CKN.Core.Step4
