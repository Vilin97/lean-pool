/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSymmetricCell
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientInputs
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSWS

/-!
# Pressure Gradient HGCloser Time Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


namespace CKN.Core.Step4

/-- A finite space-time `Lᵃ` norm on a finite time interval supplies a
finite integral of the spatial slice norms. -/
theorem lintegral_slice_eLpNorm_lt_top_of_memLp
    {a : ℝ} (ha : 1 ≤ a) {B : Set Vec3} {J : Set ℝ}
    (hJ : volume J < ∞) {F : ParabolicPoint → ℝ}
    (hF : MemLp F (ENNReal.ofReal a) (volume.restrict (B ×ˢ J))) :
    (∫⁻ t in J, eLpNorm (fun x => F (x, t)) (ENNReal.ofReal a)
      (volume.restrict B)) < ∞ := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J) =
      (volume.restrict B).prod (volume.restrict J) := by
    rw [Measure.volume_eq_prod Vec3 ℝ, Measure.prod_restrict]
  have hFm : AEStronglyMeasurable F
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [← hprod]
    exact hF.aestronglyMeasurable
  have hpower : (∫⁻ z, ‖F z‖ₑ ^ a
      ∂((volume.restrict B).prod (volume.restrict J))) < ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_pos.mpr ha0).ne' ENNReal.ofReal_ne_top hF.eLpNorm_lt_top
    rw [ENNReal.toReal_ofReal ha0.le] at h
    change (∫⁻ z : Vec3 × ℝ, ‖F z‖ₑ ^ a
      ∂((volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J))) < ∞ at h
    rw [hprod] at h
    exact h
  have htime : (∫⁻ t in J, ∫⁻ x in B, ‖F (x, t)‖ₑ ^ a) < ∞ := by
    rw [← lintegral_prod_symm (fun z => ‖F z‖ₑ ^ a)
      (hFm.enorm.pow_const a)]
    exact hpower
  have hle : (∫⁻ t in J, eLpNorm (fun x => F (x, t)) (ENNReal.ofReal a)
      (volume.restrict B)) ≤ ∫⁻ t in J, 1 + ∫⁻ x in B, ‖F (x, t)‖ₑ ^ a := by
    apply lintegral_mono_ae
    filter_upwards [hFm.prodMk_right] with t ht
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.mpr ha0).ne' ENNReal.ofReal_ne_top ht,
      ENNReal.toReal_ofReal ha0.le]
    let b := ∫⁻ x in B, ‖F (x, t)‖ₑ ^ a
    change b ^ (1 / a) ≤ 1 + b
    by_cases hb : b ≤ 1
    · exact (ENNReal.rpow_le_one hb (by positivity)).trans le_self_add
    · have hb1 : 1 ≤ b := le_of_not_ge hb
      have he : 1 / a ≤ (1 : ℝ) := (div_le_one ha0).mpr ha
      have h := ENNReal.rpow_le_rpow_of_exponent_le hb1 he
      simpa only [ENNReal.rpow_one] using h.trans le_add_self
  apply hle.trans_lt
  rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
    Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨hJ, htime⟩

/-- A bounded spatial cutoff supported in the local carrier preserves
finiteness of the time integral of spatial slice norms. -/
theorem lintegral_cutoff_slice_eLpNorm_lt_top_of_memLp
    {a : ℝ} (ha : 1 ≤ a) {B : Set Vec3} {J : Set ℝ}
    (hB : MeasurableSet B) (hJ : volume J < ∞)
    {η : Vec3 → ℝ} (hη : AEStronglyMeasurable η volume)
    (hηbound : ∀ x, |η x| ≤ 1) (hηsupport : Function.support η ⊆ B)
    {F : ParabolicPoint → ℝ}
    (hF : MemLp F (ENNReal.ofReal a) (volume.restrict (B ×ˢ J))) :
    (∫⁻ t in J, eLpNorm (fun x => η x * F (x, t)) (ENNReal.ofReal a)
      volume) < ∞ := by
  have hFm : AEStronglyMeasurable F
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact hF.aestronglyMeasurable
  apply lt_of_le_of_lt _ (lintegral_slice_eLpNorm_lt_top_of_memLp ha hJ hF)
  apply lintegral_mono_ae
  filter_upwards [hFm.prodMk_right] with t ht
  have hmul : (fun x => η x * F (x, t)) =
      (fun x => η x * B.indicator (fun y => F (y, t)) x) := by
    funext x
    by_cases hx : x ∈ B
    · simp only [Set.indicator_of_mem hx]
    · have hzero : η x = 0 := by
        by_contra hne
        exact hx (hηsupport hne)
      simp only [hzero, zero_mul]
  rw [hmul, ← eLpNorm_indicator_eq_eLpNorm_restrict hB]
  apply eLpNorm_mono_ae (hη.mul ((aestronglyMeasurable_indicator_iff hB).2 ht))
  filter_upwards with x
  change ‖η x * B.indicator (fun y => F (y, t)) x‖ ≤
    ‖B.indicator (fun y => F (y, t)) x‖
  rw [norm_mul, Real.norm_eq_abs (η x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hηbound x)

/-- The pressure term of the slice gradient bound has a finite time integral
on every compactly contained solution box. -/
theorem lintegral_pressure_slice_eLpNorm_lt_top_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {B : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I B J) :
    (∫⁻ t in J, eLpNorm (fun x => p (x, t)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict B)) < ∞ := by
  have hdata := hsol.2.2.2.2.2.1 B J hbox
  obtain ⟨_hu, _hDu, _hp, _hf, _hess, _henergy, hpLp, _hfLp, _hgrad⟩ := hdata
  exact lintegral_slice_eLpNorm_lt_top_of_memLp (by norm_num)
    ((measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top) hpLp

/-- Each force component supplies a finite time integral of its spatial
`L^{6/5}` norm using only the local force data of a suitable solution. -/
theorem lintegral_force_slice_eLpNorm_lt_top_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {B : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I B J) (i : Fin 3) :
    (∫⁻ t in J, eLpNorm (fun x => f (x, t) i) (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict B)) < ∞ := by
  let : IsFiniteMeasure (volume.restrict (spaceTimeSet B J)) :=
    CKN.Core.Step3.local_box_isFiniteMeasure hbox.2.1 hbox.2.2.2.2.1
  have hfLp : MemLp (fun z => f z i) (ENNReal.ofReal q)
      (volume.restrict (spaceTimeSet B J)) := hsol.2.2.2.2.1 B J hbox i
  have hq := hsol.2.2.2.1
  have hsmall := hfLp.mono_exponent
    (ENNReal.ofReal_le_ofReal (show (6 / 5 : ℝ) ≤ q by linarith only [hq]))
  exact lintegral_slice_eLpNorm_lt_top_of_memLp (by norm_num)
    ((measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top) hsmall

/-- The cutoff-force term has a finite time-integrated spatial norm without
any global assumption or divergence constraint on the force. -/
theorem lintegral_cutoff_force_slice_eLpNorm_lt_top_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {B : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I B J)
    {η : Vec3 → ℝ} (hη : AEStronglyMeasurable η volume)
    (hηbound : ∀ x, |η x| ≤ 1) (hηsupport : Function.support η ⊆ B)
    (i : Fin 3) :
    (∫⁻ t in J, eLpNorm (fun x => η x * f (x, t) i)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume) < ∞ := by
  let : IsFiniteMeasure (volume.restrict (spaceTimeSet B J)) :=
    CKN.Core.Step3.local_box_isFiniteMeasure hbox.2.1 hbox.2.2.2.2.1
  have hfLp : MemLp (fun z => f z i) (ENNReal.ofReal q)
      (volume.restrict (spaceTimeSet B J)) := hsol.2.2.2.2.1 B J hbox i
  have hq := hsol.2.2.2.1
  have hsmall := hfLp.mono_exponent
    (ENNReal.ofReal_le_ofReal (show (6 / 5 : ℝ) ≤ q by linarith only [hq]))
  exact lintegral_cutoff_slice_eLpNorm_lt_top_of_memLp (by norm_num)
    hbox.1.measurableSet
    ((measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top)
    hη hηbound hηsupport hsmall

end CKN.Core.Step4
