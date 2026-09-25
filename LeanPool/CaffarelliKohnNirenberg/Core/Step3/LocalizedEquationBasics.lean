/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.DuhamelAdjoint
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Localized Equation Basics

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.Step3
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential
/-! These are the divergence-form sources obtained directly from the tested equation. -/
/-- Non-divergence source in the localized momentum equation, including pressure and forcing. -/
def localizedDivergenceG (φ : Vec3 × ℝ → ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z i => timePartial (show ParabolicPoint → ℝ from φ) z * u z i
    + ∑ j, u z i * u z j * spatialPartial (show ParabolicPoint → ℝ from φ) j z
    - ∑ j, Du z i j * spatialPartial (show ParabolicPoint → ℝ from φ) j z
    + p z * spatialPartial (show ParabolicPoint → ℝ from φ) i z + f z i * φ z
/-- Tensor divergence source in the localized momentum equation. -/
def localizedDivergenceH (φ : Vec3 × ℝ → ℝ) (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) : Fin 3 → ParabolicPoint → Vec3 :=
  fun j z i => φ z * u z i * u z j + u z i * spatialPartial φ j z
    + if i = j then p z * φ z else 0
lemma timePartial_mul_full {a b : Vec3 × ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (z : Vec3 × ℝ) : timePartial (fun w => a w * b w) z = timePartial
      a z * b z + a z * timePartial b z := by
  unfold timePartial
  have ha' : DifferentiableAt ℝ (fun s : ℝ => a (z.1, s)) z.2 := by
    exact (ha.differentiable (by simp)).differentiableAt.comp z.2
      (by fun_prop)
  have hb' : DifferentiableAt ℝ (fun s : ℝ => b (z.1, s)) z.2 := by
    exact (hb.differentiable (by simp)).differentiableAt.comp z.2
      (by fun_prop)
  change (fderiv ℝ ((fun s => a (z.1, s)) * (fun s => b (z.1, s))) z.2) 1 = _
  rw [fderiv_mul ha' hb']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Prod.eta]
  ring
lemma spatialPartial_mul_full {a b : Vec3 × ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (j : Fin 3) (z : Vec3 × ℝ) : spatialPartial (fun w => a w * b w)
      j z = spatialPartial a j z * b z + a z * spatialPartial b j z := by
  unfold spatialPartial
  have ha' : DifferentiableAt ℝ (fun x : Vec3 => a (x, z.2)) z.1 := by
    exact (ha.differentiable (by simp)).differentiableAt.comp z.1
      (by fun_prop)
  have hb' : DifferentiableAt ℝ (fun x : Vec3 => b (x, z.2)) z.1 := by
    exact (hb.differentiable (by simp)).differentiableAt.comp z.1
      (by fun_prop)
  change (fderiv ℝ ((fun x => a (x, z.2)) * (fun x => b (x, z.2))) z.1) (basisVec j) = _
  rw [fderiv_mul ha' hb']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Prod.eta]
  ring
lemma timePartial_contDiff_full {a : Vec3 × ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => timePartial a z) := by
  let F : (Vec3 × ℝ) → ℝ → ℝ := fun z s => a (z.1, s)
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun q : (Vec3 × ℝ) × ℝ => (q.1.1, q.2)) := by
    fun_prop
  have hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) := by
    convert ha.comp hmap using 1
    funext q
    rfl
  have hderiv := hF.fderiv_apply (contDiff_snd (𝕜 := ℝ) (n := (⊤ : ℕ∞)))
    (contDiff_const (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (c := (1 : ℝ)))
    (by simp)
  simpa only [F, timePartial, Function.uncurry] using hderiv
lemma spatialSecondPartial_contDiff_full {a : Vec3 × ℝ → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialSecondPartial a i j z) := by
  unfold spatialSecondPartial
  exact spatialPartial_contDiff (spatialPartial_contDiff ha i) j
lemma local_box_isFiniteMeasure {Ω' : Set Vec3} {J : Set ℝ}
    (hΩ' : IsCompact (closure Ω')) (hJ : IsCompact (closure J)) :
    IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) := by
  let K : Set ParabolicPoint :=
    parabolicHomeomorph ⁻¹' (closure Ω' ×ˢ closure J)
  have hK : IsCompact K := by
    exact parabolicHomeomorph.isCompact_preimage.2 (hΩ'.prod hJ)
  have hKtop : volume K < ⊤ := by
    change (volume : Measure (Vec3 × ℝ)) (closure Ω' ×ˢ closure J) < ⊤
    exact (hΩ'.prod hJ).measure_lt_top
  have hsub : spaceTimeSet Ω' J ⊆ K := by
    intro z hz
    change z.1 ∈ closure Ω' ∧ z.2 ∈ closure J
    exact ⟨subset_closure hz.1, subset_closure hz.2⟩
  exact isFiniteMeasure_restrict.mpr (lt_of_le_of_lt (measure_mono hsub) hKtop).ne
lemma local_memLp_two_of_energy
    {Ω' : Set Vec3} {J : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {hu : AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω' J))}
    {hDu : AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω' J))}
    (henergy : (∫⁻ z in spaceTimeSet Ω' J,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤) :
    MemLp u 2 (volume.restrict (spaceTimeSet Ω' J)) ∧
      MemLp Du 2 (volume.restrict (spaceTimeSet Ω' J)) := by
  have hnorm {E : Type} [NormedAddCommGroup E] (w : ParabolicPoint → E)
      (hw : AEStronglyMeasurable w (volume.restrict (spaceTimeSet Ω' J)))
      (hfin : (∫⁻ z in spaceTimeSet Ω' J, ‖w z‖ₑ ^ (2 : ℝ)) < ⊤) :
      Integrable (fun z => (‖w z‖ : ℝ) ^ (2 : ℕ))
        (volume.restrict (spaceTimeSet Ω' J)) := by
    have hmeas := hw.norm.pow 2
    have htop : ∫⁻ z in spaceTimeSet Ω' J,
        ENNReal.ofReal ((‖w z‖ : ℝ) ^ (2 : ℕ)) ≠ ⊤ := by
      convert ne_of_lt hfin using 1
      congr 1
      funext z
      calc
        ENNReal.ofReal ((‖w z‖ : ℝ) ^ (2 : ℕ)) =
            ENNReal.ofReal ((‖w z‖ : ℝ) ^ (2 : ℝ)) := by
              norm_num [Real.rpow_natCast]
        _ = ENNReal.ofReal ‖w z‖ ^ (2 : ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)).symm
        _ = ‖w z‖ₑ ^ (2 : ℝ) := by rw [ofReal_norm]
    exact (lintegral_ofReal_ne_top_iff_integrable hmeas
      (Filter.Eventually.of_forall fun z => sq_nonneg _)).mp htop
  have hu_lt := lt_of_le_of_lt
    (lintegral_mono (fun z => le_add_right le_rfl)) henergy
  have hDu_lt := lt_of_le_of_lt
    (lintegral_mono (fun z => le_add_left le_rfl)) henergy
  exact ⟨(memLp_two_iff_integrable_sq_norm hu).2 (hnorm u hu hu_lt),
    (memLp_two_iff_integrable_sq_norm hDu).2 (hnorm Du hDu hDu_lt)⟩
lemma compact_factor_integrable
    {Ω' : Set Vec3} {J : Set ℝ} {a : ParabolicPoint → ℝ}
    {b : Vec3 × ℝ → ℝ}
    (ha : Integrable a (volume.restrict (spaceTimeSet Ω' J)))
    (hb : Continuous b) (hbc : HasCompactSupport b)
    (hbs : tsupport b ⊆ (spaceTimeSet Ω' J : Set (Vec3 × ℝ))) :
    Integrable (fun z => a z * b z) volume := by
  obtain ⟨C, hC⟩ := hbc.exists_bound_of_continuous hb
  have hOn : IntegrableOn (fun z => a z * b z)
      (spaceTimeSet Ω' J) volume := by
    change Integrable (fun z => a z * b z)
      (volume.restrict (spaceTimeSet Ω' J))
    exact ha.mul_bdd hb.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hC z)
  apply hOn.integrable_of_forall_notMem_eq_zero
  intro z hz
  have hzb : parabolicHomeomorph z ∉ tsupport b := by
    intro h
    apply hz
    have hpair : (z.1, z.2) ∈ Ω' ×ˢ J := by
      simpa [spaceTimeSet] using hbs h
    rw [show spaceTimeSet Ω' J = parabolicHomeomorph ⁻¹' (Ω' ×ˢ J) by
      rw [spaceTimeSet, parabolicHomeomorph_preimage]]
    change z.1 ∈ Ω' ∧ z.2 ∈ J
    exact hpair
  have hbzero : b (parabolicHomeomorph z) = 0 :=
    image_eq_zero_of_notMem_tsupport hzb
  have hbzero' : b (z.1, z.2) = 0 := by simpa using hbzero
  change a z * b (z.1, z.2) = 0
  rw [hbzero', mul_zero]
lemma global_integral_eq_box_slices
    {Ω' : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → ℝ}
    (hF : Integrable F volume)
    (hzero : ∀ z ∉ spaceTimeSet Ω' J, F z = 0) :
    ∫ z, F z = ∫ t, ∫ x in Ω', F (x, t) := by
  change Integrable (fun q : Vec3 × ℝ => F (q.1, q.2))
      ((volume : Measure Vec3).prod volume) at hF
  change (∫ q : Vec3 × ℝ, F (q.1, q.2)
      ∂((volume : Measure Vec3).prod volume)) =
    ∫ t, ∫ x in Ω', F ((x, t) : ParabolicPoint)
  calc
    (∫ q : Vec3 × ℝ, F (q.1, q.2)
        ∂((volume : Measure Vec3).prod volume)) =
        ∫ t, ∫ x, F (x, t) := by
      simpa only using
        (integral_prod_symm (fun q : Vec3 × ℝ => F (q.1, q.2)) hF)
    _ = ∫ t, ∫ x in Ω', F (x, t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ J
      · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro x hx
        exact hzero ((x, t) : ParabolicPoint) (by
          intro hbox
          exact hx hbox.1)
      · have hzero_t : ∀ x : Vec3, F (x, t) = 0 := by
          intro x
          apply hzero ((x, t) : ParabolicPoint)
          intro hbox
          exact ht hbox.2
        have hfull : ∫ x, F ((x, t) : ParabolicPoint) = 0 := by
          calc
            (∫ x, F ((x, t) : ParabolicPoint)) = ∫ x, (0 : ℝ) := by
              apply integral_congr_ae
              filter_upwards [] with x
              exact hzero_t x
            _ = 0 := by simp
        have hset : ∫ x in Ω', F ((x, t) : ParabolicPoint) = 0 := by
          calc
            (∫ x in Ω', F ((x, t) : ParabolicPoint)) = ∫ x in Ω', (0 : ℝ) := by
              apply integral_congr_ae
              filter_upwards [] with x
              exact hzero_t x
            _ = 0 := by simp
        rw [hfull, hset]
lemma box_slice_zero_of_time_not_mem
    {Ω' : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → ℝ}
    (hzero : ∀ z ∉ spaceTimeSet Ω' J, F z = 0)
    {t : ℝ} (ht : t ∉ J) :
    ∫ x in Ω', F ((x, t) : ParabolicPoint) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ω') (f := fun x : Vec3 => F ((x, t) : ParabolicPoint))
    (fun x hx => hzero ((x, t) : ParabolicPoint) (by
      intro hbox
      exact ht hbox.2))]
  calc
    (∫ x, F ((x, t) : ParabolicPoint)) = ∫ x, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply hzero ((x, t) : ParabolicPoint)
      intro hbox
      exact ht hbox.2
    _ = 0 := by simp
lemma global_integral_transfer
    {Ω' : Set Vec3} {J : Set ℝ}
    {B A C : ParabolicPoint → ℝ}
    (hB : Integrable B volume) (hA : Integrable A volume)
    (hC : Integrable C volume)
    (hBzero : ∀ z ∉ spaceTimeSet Ω' J, B z = 0)
    (hAzero : ∀ z ∉ spaceTimeSet Ω' J, A z = 0)
    (hCzero : ∀ z ∉ spaceTimeSet Ω' J, C z = 0)
    (hslice : ∀ᵐ t ∂volume.restrict J,
      (∫ x in Ω', B (x, t)) =
        (-(∫ x in Ω', A (x, t))) - (∫ x in Ω', C (x, t))) :
    (∫ z, B z) =
      (-(∫ z, A z)) - (∫ z, C z) := by
  have hBbox : Integrable B (volume.restrict (spaceTimeSet Ω' J)) :=
    hB.mono_measure (Measure.restrict_le_self :
      volume.restrict (spaceTimeSet Ω' J) ≤ volume)
  have hAbox : Integrable A (volume.restrict (spaceTimeSet Ω' J)) :=
    hA.mono_measure (Measure.restrict_le_self :
      volume.restrict (spaceTimeSet Ω' J) ≤ volume)
  have hCbox : Integrable C (volume.restrict (spaceTimeSet Ω' J)) :=
    hC.mono_measure (Measure.restrict_le_self :
      volume.restrict (spaceTimeSet Ω' J) ≤ volume)
  change Integrable (fun q : Vec3 × ℝ => B ((q.1, q.2) : ParabolicPoint))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (Ω' ×ˢ J)) at hBbox
  change Integrable (fun q : Vec3 × ℝ => A ((q.1, q.2) : ParabolicPoint))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (Ω' ×ˢ J)) at hAbox
  change Integrable (fun q : Vec3 × ℝ => C ((q.1, q.2) : ParabolicPoint))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (Ω' ×ˢ J)) at hCbox
  rw [← Measure.prod_restrict Ω' J] at hBbox hAbox hCbox
  have hBt : Integrable (fun t => ∫ x in Ω', B (x, t))
      (volume.restrict J) := hBbox.integral_prod_right
  have hAt : Integrable (fun t => ∫ x in Ω', A (x, t))
      (volume.restrict J) := hAbox.integral_prod_right
  have hCt : Integrable (fun t => ∫ x in Ω', C (x, t))
      (volume.restrict J) := hCbox.integral_prod_right
  have hBglobal := global_integral_eq_box_slices hB hBzero
  have hAglobal := global_integral_eq_box_slices hA hAzero
  have hCglobal := global_integral_eq_box_slices hC hCzero
  have hBglobalJ : (∫ z, B z) = ∫ t in J, ∫ x in Ω', B (x, t) := by
    calc
      (∫ z, B z) = ∫ t, ∫ x in Ω', B (x, t) := hBglobal
      _ = ∫ t in J, ∫ x in Ω', B (x, t) := by
        symm
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := J) (f := fun t => ∫ x in Ω', B (x, t))
          (fun t ht => box_slice_zero_of_time_not_mem hBzero ht)]
  have hAglobalJ : (∫ z, A z) = ∫ t in J, ∫ x in Ω', A (x, t) := by
    calc
      (∫ z, A z) = ∫ t, ∫ x in Ω', A (x, t) := hAglobal
      _ = ∫ t in J, ∫ x in Ω', A (x, t) := by
        symm
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := J) (f := fun t => ∫ x in Ω', A (x, t))
          (fun t ht => box_slice_zero_of_time_not_mem hAzero ht)]
  have hCglobalJ : (∫ z, C z) = ∫ t in J, ∫ x in Ω', C (x, t) := by
    calc
      (∫ z, C z) = ∫ t, ∫ x in Ω', C (x, t) := hCglobal
      _ = ∫ t in J, ∫ x in Ω', C (x, t) := by
        symm
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := J) (f := fun t => ∫ x in Ω', C (x, t))
          (fun t ht => box_slice_zero_of_time_not_mem hCzero ht)]
  calc
    (∫ z, B z) = ∫ t in J, ∫ x in Ω', B (x, t) := hBglobalJ
    _ = ∫ t in J, ((-(∫ x in Ω', A (x, t))) -
        (∫ x in Ω', C (x, t))) := by
      exact integral_congr_ae hslice
    _ = (-(∫ t in J, ∫ x in Ω', A (x, t))) -
        (∫ t in J, ∫ x in Ω', C (x, t)) := by
      have hnegA : Integrable (fun t => -(∫ x in Ω', A (x, t)))
          (volume.restrict J) := hAt.neg
      calc
        _ = (∫ t in J, -(∫ x in Ω', A (x, t))) -
            ∫ t in J, ∫ x in Ω', C (x, t) := by
              convert integral_sub hnegA hCt using 1
        _ = _ := by
          rw [integral_neg]
    _ = (-(∫ z, A z)) - (∫ z, C z) := by
      rw [hAglobalJ.symm, hCglobalJ.symm]
lemma zero_outside_box_of_tsupport_subset
    {Ω' : Set Vec3} {J : Set ℝ} {b : Vec3 × ℝ → ℝ}
    (hbs : tsupport b ⊆ (spaceTimeSet Ω' J : Set (Vec3 × ℝ))) :
    ∀ z ∉ spaceTimeSet Ω' J, b (z.1, z.2) = 0 := by
  intro z hz
  have hnot : parabolicHomeomorph z ∉ tsupport b := by
    intro hmem
    apply hz
    rw [show spaceTimeSet Ω' J = parabolicHomeomorph ⁻¹' (Ω' ×ˢ J) by
      rw [spaceTimeSet, parabolicHomeomorph_preimage]]
    exact hbs hmem
  simpa using (image_eq_zero_of_notMem_tsupport hnot)
end CKN.Core.Step3
