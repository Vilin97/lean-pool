/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsMeans
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsSourceMorrey

/-! # Centred velocity Morrey data from suitable weak solutions

The mean correction is bounded in time and supported on a finite-measure
space-time carrier. It therefore belongs to every finite integrability
class needed here. Subtracting it preserves the velocity Morrey class.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-- Global finite integrability at the outer exponent controls a Morrey
seminorm with any smaller integrability exponent. -/
theorem pressure_source_morrey_lt_top_of_memLp
    {P κ : ℝ} (hP : 1 ≤ P) (hPκ : P ≤ κ) {g : ParabolicPoint → ℝ}
    (hg : MemLp g (ENNReal.ofReal κ) volume) : morreyNorm P κ g < ⊤ := by
  have hκ : 0 < κ := (zero_lt_one.trans_le hP).trans_le hPκ
  have hn : eLpNorm' g κ volume < ⊤ := by
    have h := hg.eLpNorm_lt_top
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hκ).ne' ENNReal.ofReal_ne_top
      hg.aestronglyMeasurable, ENNReal.toReal_ofReal hκ.le] at h
    exact h
  apply (morreyNorm_le_eLpNorm' hP hPκ hg.aestronglyMeasurable.aemeasurable).trans_lt
  apply ENNReal.mul_lt_top _ hn
  apply ENNReal.rpow_lt_top_of_nonneg
    (sub_nonneg.mpr (one_div_le_one_div_of_le (zero_lt_one.trans_le hP) hPκ))
  rw [volume_parabolicCylinder]
  exact ENNReal.mul_ne_top (Integration.volume_vec3Ball_lt_top).ne ENNReal.ofReal_ne_top

/-- A bounded measurable function on a finite-measure carrier has finite
Morrey seminorm at each finite admissible pair of exponents. -/
theorem pressure_source_bounded_supported_morrey_lt_top
    {P κ C : ℝ} (hP : 1 ≤ P) (hPκ : P ≤ κ)
    {S : Set ParabolicPoint} (hS : MeasurableSet S) (hSfinite : volume S < ⊤)
    {g : ParabolicPoint → ℝ} (hg : AEMeasurable g volume)
    (hbound : ∀ᵐ z ∂volume, |g z| ≤ |C|)
    (hzero : ∀ z ∉ S, g z = 0) : morreyNorm P κ g < ⊤ := by
  have hconst : MemLp (S.indicator (fun _ : ParabolicPoint => C))
      (ENNReal.ofReal κ) volume := memLp_indicator_const _ hS C (Or.inr hSfinite.ne)
  apply pressure_source_morrey_lt_top_of_memLp hP hPκ
  apply hconst.of_le hg.aestronglyMeasurable
  filter_upwards [hbound] with z hz
  by_cases hzS : z ∈ S
  · simpa only [Set.indicator_of_mem hzS, Real.norm_eq_abs] using hz
  · rw [hzero z hzS, Set.indicator_of_notMem hzS]

/-- The suitable-solution energy bound supplies the centred velocity Morrey
data on every measurable subcarrier of a local box. -/
theorem pressure_centred_velocity_morrey_data_of_sws
    {τ : ℝ} (hτ : 3 ≤ τ)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {B : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I B J)
    {S : Set ParabolicPoint} (hS : MeasurableSet S) (hSbox : S ⊆ B ×ˢ J)
    (hU : ∀ i, morreyNorm 3 τ (S.indicator (fun z => u z i)) < ⊤) :
    ∀ i : Fin 3,
      AEMeasurable (S.indicator (fun z => u z i -
        average (volume.restrict B) (fun y : Vec3 => u (y, z.2) i))) volume ∧
      morreyNorm 3 τ (S.indicator (fun z => u z i -
        average (volume.restrict B) (fun y : Vec3 => u (y, z.2) i))) < ⊤ := by
  have hJ : MeasurableSet J := hbox.2.2.2.1.measurableSet
  have hBfin : volume B < ⊤ := (measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top
  have hJfin : volume J < ⊤ :=
    (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  have hSfin : volume S < ⊤ := by
    apply (measure_mono hSbox).trans_lt
    change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ)) (B ×ˢ J) < ⊤
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top hBfin hJfin
  obtain ⟨C, hC, hCbound⟩ := pressure_source_mean_ae_bounded_of_sws hsol hbox
  have hUg := (hsol.2.2.2.2.2.1 B J hbox).1.aemeasurable
  intro i
  let c : ℝ → ℝ := fun s => average (volume.restrict B) (fun y : Vec3 => u (y, s) i)
  let m : ParabolicPoint → ℝ := fun z => J.indicator c z.2
  have hca : AEMeasurable (J.indicator c) volume :=
    (aemeasurable_indicator_iff hJ).mpr (pressure_source_mean_aemeasurable_of_sws hsol hbox i)
  have hma : AEMeasurable m volume := by
    have h := hca.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Vec3)))
    exact h
  have hctime : ∀ᵐ s ∂volume, |J.indicator c s| ≤ C := by
    have hcJ := (ae_restrict_iff' hJ).mp (hCbound.mono (fun s hs => hs i))
    filter_upwards [hcJ] with s hs
    by_cases hsJ : s ∈ J
    · rw [Set.indicator_of_mem hsJ]
      exact hs hsJ
    · rw [Set.indicator_of_notMem hsJ, abs_zero]
      exact hC
  have hm : ∀ᵐ z ∂(volume : Measure ParabolicPoint), |m z| ≤ C :=
    Measure.quasiMeasurePreserving_snd.ae hctime
  have hM : morreyNorm 3 τ (S.indicator m) < ⊤ := by
    apply pressure_source_bounded_supported_morrey_lt_top (by norm_num) hτ hS hSfin
      (hma.indicator hS) (C := C)
    · filter_upwards [hm] with z hz
      by_cases hzS : z ∈ S
      · simpa only [Set.indicator_of_mem hzS, abs_of_nonneg hC] using hz
      · rw [Set.indicator_of_notMem hzS, abs_zero]
        exact abs_nonneg _
    · exact fun z hz => Set.indicator_of_notMem hz m
  have hUa : AEMeasurable (S.indicator (fun z => u z i)) volume := by
    apply (aemeasurable_indicator_iff hS).mpr
    exact ((measurable_pi_apply i).comp_aemeasurable hUg).mono_measure
      (Measure.restrict_mono_set volume hSbox)
  have hMa : AEMeasurable (S.indicator m) volume := hma.indicator hS
  have hMneg : morreyNorm 3 τ (fun z => -(S.indicator m z)) < ⊤ := by
    simpa using pressure_source_bounded_multiplier_morrey_lt_top
      (a := fun _ => (-1 : ℝ)) (C := 1) (by norm_num : (0 : ℝ) < 3)
      (Eventually.of_forall (fun _ => by norm_num)) hM
  have heq : S.indicator (fun z => u z i - c z.2) =
      fun z => S.indicator (fun w => u w i) z + -(S.indicator m z) := by
    funext z
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz, m, Set.indicator_of_mem (hSbox hz).2, sub_eq_add_neg]
    · simp [hz]
  change AEMeasurable (S.indicator (fun z => u z i - c z.2)) volume ∧ _
  rw [heq]
  exact ⟨hUa.add hMa.neg, (morrey_norm_add_le (by norm_num) hUa hMa.neg).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hU i, hMneg⟩)⟩

end CKN.Core.Step4
