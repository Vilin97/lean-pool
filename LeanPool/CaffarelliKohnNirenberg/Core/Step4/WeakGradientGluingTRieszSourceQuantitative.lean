/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPAffineSlot
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPComparison
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRemainderMajorantQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedRemainderBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsRiesz
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTWindowSelection
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGaugeMajorantExponents

/-! # Quantitative time masses of the localized pressure Riesz sources

A uniform endpoint coefficient puts the localized divergence source into the
affine cell budget; the source contains both convection and force.
-/

@[expose] public section

section

/-!
# Pressure Gradient Origin KPAffine Source

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section

namespace CKN.Core.Step4

/-!
# The divergence source meets the enlarged small-cell budget

For a suitable weak solution with velocity budgets `KU`, `KD` on `Q_{R₀}` and
data size `ε`, the `6/5` power of the Morrey norm of the divergence source
`Du·u - f` of the pressure equation is bounded by `X^{6/5}`, where
`X = 3·KU·KD + forceSourceMorreyBound q ε`
(`origin_divergence_source_numerical_bounds_of_sws`). That coefficient lies
below `originKPAffineASlot`, so the source meets the enlarged budget with no
further analytic input. The linear budget `c·3X` of
`oneSidedPressureGradientKP` does not dominate `X^{6/5}` once `X > 3c`, which
is the scaling defect the enlarged budget removes.
-/

/-- **The source Morrey norm against the enlarged budget.** Under the
hypotheses of the origin pressure-gradient obligation, the `6/5` power of the
Morrey norm of the vector divergence source on `Q_{R₁}` lies below
`originKPAffineASlot q C_CZ ε KU KD`. -/
theorem origin_divergence_source_morrey_rpow_le_KPAffine_slot
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hR : 0 < R₁) (hR₁₀ : R₁ ≤ R₀) (hR₀le : R₀ ≤ 1)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hU : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU)
    (hD : ∀ i j, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD)
    (hsize : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) :
    morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
        (fun z => vec3EuclideanNorm
          ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
            (fun w => fun i => ∑ j, Du w i j * u w j - f w i) z)) ^ (6 / 5 : ℝ) ≤
      originKPAffineASlot q C_CZ ε KU KD := by
  apply rpow_le_originKPAffineASlot_of_le
  calc
    _ ≤ 3 * (3 * KU * KD + forceSourceMorreyBound q ε) :=
      (origin_divergence_source_numerical_bounds_of_sws q τ R₀ R₁ ε KU KD
        hq hτ hR hR₁₀ hR₀le hsol hdom hU hD hsize).1
    _ = 1 * (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) := (one_mul _).symm
    _ ≤ _ := mul_le_mul' (one_le_ofReal_abs_add_one C_CZ) le_rfl

end CKN.Core.Step4

end

end

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat
open CKN.Foundation.Parabolic.Morrey CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- An absolute threshold paying for the three spatial Riesz components. -/
def rieszSourceThresholdA : ℝ :=
  3 * (pressureRieszMorreyConstant (25/9)).toReal

/-- The Riesz coefficient is uniformly bounded over the admitted exponent range. -/
theorem pressureRieszMorreyConstant_le_endpoint {κ : ℝ}
    (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9) :
    pressureRieszMorreyConstant κ ≤ pressureRieszMorreyConstant (25/9) := by
  have hd : (5 : ℝ) / (25/9) ≤ 5 / κ :=
    div_le_div_of_nonneg_left (by norm_num) hκ hκhi
  unfold pressureRieszMorreyConstant
  gcongr
  all_goals norm_num

/-- The fixed threshold absorbs the sum of three component operator constants. -/
theorem three_riesz_constants_le_affine_coefficient {κ C_CZ : ℝ}
    (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9) (hC : rieszSourceThresholdA ≤ C_CZ) :
    3 * pressureRieszMorreyConstant κ ≤ ENNReal.ofReal (|C_CZ| + 1) := by
  calc
    _ ≤ 3 * pressureRieszMorreyConstant (25/9) :=
      mul_le_mul' le_rfl (pressureRieszMorreyConstant_le_endpoint hκ hκhi)
    _ = ENNReal.ofReal rieszSourceThresholdA := by
      rw [rieszSourceThresholdA, ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_toReal (pressureRieszMorreyConstant_lt_top _).ne]
      norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (hC.trans ((le_abs_self C_CZ).trans (le_add_of_nonneg_right (by norm_num))))

/-- Three selected Riesz components of sources with the displayed affine
budget satisfy every clipped-cell A estimate above the absolute threshold. -/
theorem riesz_source_sum_clipped_le_affine_slot
    (q τ C_CZ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτhi : τ ≤ 25)
    (hC : rieszSourceThresholdA ≤ C_CZ)
    (i : Fin 3) {F T : Fin 3 → ParabolicPoint → ℝ}
    (hF : ∀ j, AEMeasurable (F j) volume)
    (hFs : ∀ j, ∀ᵐ s ∂volume, MemLp (fun y => F j (y, s))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    {L : ℝ} (hsupport : ∀ j y s, L < ‖y‖ → F j (y, s) = 0)
    (hT : ∀ j, AEMeasurable (T j) volume)
    (hident : ∀ j, ∀ᵐ s ∂volume, (fun y => T j (y, s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => F j (y, s)))
    (hN : ∀ j, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q) (F j) ≤
      3 * (3 * KU * KD + forceSourceMorreyBound q ε))
    (B : Set Vec3) (J : Set ℝ) (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ J,
      eLpNorm (fun y => ∑ j, T j (y,s)) (ENNReal.ofReal (6/5 : ℝ))
        (volume.restrict (vec3Ball z.1 r ∩ B)) ^ (6/5 : ℝ)) ≤
      originKPAffineASlot q C_CZ ε KU KD *
        ENNReal.ofReal (r ^ (5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  let κ := min ((1/τ+8/25)⁻¹) q
  let X := 3 * (3*KU*KD + forceSourceMorreyBound q ε)
  have hκ : 0 < κ := lt_of_lt_of_le (by norm_num) (endgame_kappa_ge hτ hq)
  have hκhi : κ ≤ 25/9 := endgame_kappa_le (by linarith only [hτ]) hτhi
  have hn (j : Fin 3) : morreyNorm (6/5 : ℝ) κ (T j) ≤
      pressureRieszMorreyConstant κ * X :=
    (pressure_riesz_morreyNorm_bound j i hκ hκhi (hF j) (hFs j)
      (hsupport j) (hT j) (hident j)).trans (mul_le_mul' le_rfl (hN j))
  have hsum : morreyNorm (6/5 : ℝ) κ (fun w => ∑ j, T j w) ≤
      3 * pressureRieszMorreyConstant κ * X := by
    have h12 := (morrey_norm_add_le (by norm_num : (1 : ℝ) ≤ 6/5) (hT 1) (hT 2)).trans
      (add_le_add (hn 1) (hn 2))
    have h012 := (morrey_norm_add_le (by norm_num : (1 : ℝ) ≤ 6/5)
      (hT 0) ((hT 1).add (hT 2))).trans (add_le_add (hn 0) h12)
    simpa [Fin.sum_univ_succ,
      show (3 : ℝ≥0∞) * pressureRieszMorreyConstant κ * X =
        pressureRieszMorreyConstant κ * X +
          (pressureRieszMorreyConstant κ * X + pressureRieszMorreyConstant κ * X) by ring]
      using h012
  have hm : AEMeasurable (fun w => ∑ j, T j w) volume := by
    exact Finset.aemeasurable_fun_sum _ (fun j _ => hT j)
  have hbound := (glued_clipped_slice_time_bound (κ := κ) hm B J z hr).2
  have hA := rpow_le_originKPAffineASlot_of_le q C_CZ ε KU KD _
    (hsum.trans (mul_le_mul' (three_riesz_constants_le_affine_coefficient hκ hκhi hC) le_rfl))
  apply hbound.trans
  rw [mul_comm, ← ENNReal.ofReal_rpow_of_pos hr]
  exact mul_le_mul' hA le_rfl


private theorem origin_divergence_source_measurable
    {q R : ℝ} (hR : 0 < R) (hRle : R ≤ 1)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (j : Fin 3) :
    AEMeasurable ((parabolicCylinder (0 : Vec3) 0 R).indicator
      (fun w => (∑ k, Du w j k * u w k) - f w j)) volume := by
  let S := parabolicCylinder (0 : Vec3) 0 R
  have hS : MeasurableSet S := measurableSet_parabolicCylinder _ _ _
  have hsub : S ⊆ parabolicCylinder (0 : Vec3) 0 1 :=
    parabolicCylinder_mono hR.le hRle
  obtain ⟨B, J, hbox, hQbox⟩ := exists_localBox_of_closure_subset hsol.1 hsol.2.1
    (by norm_num : (0 : ℝ) < 1) hdom
  have hd := hsol.2.2.2.2.2.1 B J hbox
  have hm := Measure.restrict_mono_set volume (hsub.trans hQbox)
  have hu (j : Fin 3) : AEMeasurable (fun w => u w j) (volume.restrict S) :=
    ((measurable_pi_apply j).comp_aemeasurable hd.1.aemeasurable).mono_measure hm
  have hdu (j k : Fin 3) : AEMeasurable (fun w => Du w j k) (volume.restrict S) :=
    ((measurable_pi_apply k).comp_aemeasurable
      ((measurable_pi_apply j).comp_aemeasurable hd.2.1.aemeasurable)).mono_measure hm
  have hf (j : Fin 3) : AEMeasurable (fun w => f w j) (volume.restrict S) :=
    ((measurable_pi_apply j).comp_aemeasurable hd.2.2.2.1.aemeasurable).mono_measure hm
  apply (aemeasurable_indicator_iff hS).mpr
  exact (Finset.aemeasurable_fun_sum _ (fun k _ => (hdu j k).mul (hu k))).sub (hf j)

private theorem indicator_component_morrey_le_vector
    (S : Set ParabolicPoint) (G : ParabolicPoint → Vec3) (j : Fin 3) (κ : ℝ) :
    morreyNorm (6/5 : ℝ) κ (S.indicator (fun w => G w j)) ≤
      morreyNorm (6/5 : ℝ) κ (fun w => vec3EuclideanNorm (S.indicator G w)) := by
  apply routeA_morreyNorm_mono_ae (by norm_num : (0 : ℝ) ≤ 6/5)
  apply Eventually.of_forall
  intro w
  by_cases hw : w ∈ S
  · simp only [Set.indicator_of_mem hw, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact abs_apply_le_vec3EuclideanNorm (G w) j
  · simp only [Set.indicator_of_notMem hw, abs_zero]
    exact abs_nonneg _

private theorem origin_riesz_source_data
    (q τ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ)
    (hR : 0 < R₁) (hR₁₀ : R₁ ≤ R₀) (hR₀le : R₀ ≤ 1)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hU : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU)
    (hD : ∀ i j, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD)
    (hsize : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) :
    let F := fun j : Fin 3 => (parabolicCylinder (0 : Vec3) 0 R₁).indicator
      (fun w => ∑ k, Du w j k * u w k - f w j)
    ∀ j, AEMeasurable (F j) volume ∧
      morreyNorm (6/5 : ℝ) (min ((1/τ+8/25)⁻¹) q) (F j) ≤
        3 * (3*KU*KD + forceSourceMorreyBound q ε) := by
  dsimp only
  let S := parabolicCylinder (0 : Vec3) 0 R₁
  let F := fun j : Fin 3 => S.indicator (fun w => ∑ k, Du w j k * u w k - f w j)
  let X := 3 * (3*KU*KD + forceSourceMorreyBound q ε)
  let κ := min ((1/τ+8/25)⁻¹) q
  have hF (j : Fin 3) : AEMeasurable (F j) volume :=
    origin_divergence_source_measurable hR (hR₁₀.trans hR₀le) hsol hdom j
  have hvec := (origin_divergence_source_numerical_bounds_of_sws q τ R₀ R₁ ε KU KD
    hq hτ hR hR₁₀ hR₀le hsol hdom hU hD hsize).1
  have hN (j : Fin 3) : morreyNorm (6/5 : ℝ) κ (F j) ≤ X :=
    (indicator_component_morrey_le_vector S
      (fun w i => (∑ k, Du w i k * u w k) - f w i) j κ).trans hvec
  exact fun j => ⟨hF j, hN j⟩

private theorem exists_supported_riesz_affine_bound
    (q τ C_CZ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτhi : τ ≤ 25)
    (hC : rieszSourceThresholdA ≤ C_CZ)
    {R₁ : ℝ} (hR : 0 < R₁) (hKU : KU < ⊤) (hKD : KD < ⊤)
    {F : Fin 3 → ParabolicPoint → ℝ}
    (hF : ∀ j, AEMeasurable (F j) volume)
    (hN : ∀ j, morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q) (F j) ≤
      3 * (3 * KU * KD + forceSourceMorreyBound q ε))
    (hsupport : ∀ j w, w ∉ parabolicCylinder (0 : Vec3) 0 R₁ → F j w = 0) :
    ∃ T : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ j i, Measurable (T j i)) ∧
      (∀ j i, ∀ᵐ s ∂volume, (fun y => T j i (y,s)) =ᵐ[volume]
        rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => F j (y,s))) ∧
      ∀ (i : Fin 3) (B : Set Vec3) (J : Set ℝ) (z : ParabolicPoint) (r : ℝ), 0 < r →
        (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ J,
          eLpNorm (fun y => ∑ j, T j i (y,s)) (ENNReal.ofReal (6/5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ B)) ^ (6/5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD *
            ENNReal.ofReal (r ^ (5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  let X := 3 * (3*KU*KD + forceSourceMorreyBound q ε)
  have hX : X < ⊤ := ENNReal.mul_lt_top (by norm_num)
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num) hKU) hKD, forceSourceMorreyBound_lt_top q ε hq⟩)
  have hFs (j : Fin 3) : ∀ᵐ s ∂volume, MemLp (fun y => F j (y,s))
      (ENNReal.ofReal (6/5 : ℝ)) volume :=
    glued_supported_source_slice_memLp (F := F j)
      (κ := min ((1/τ+8/25)⁻¹) q) (z₀ := ((0 : Vec3), 0))
      (hF j) ((hN j).trans_lt hX) hR
      (hsupport j)
  have hcompact := isCompact_closure_vec3Ball (x := (0 : Vec3)) hR
  have ht (j i : Fin 3) : ∃ T : ParabolicPoint → ℝ, Measurable T ∧
      ∀ᵐ s ∂volume, (fun y => T (y,s)) =ᵐ[volume]
        rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
          (rieszSecondL2_weak_type j i) (fun y => F j (y,s)) :=
    exists_measurable_riesz_extension_field_of_aemeasurable j i (hF j) hcompact
      (fun y s hy => hsupport j (y,s) (fun hw => hy (subset_closure hw.1))) (hFs j)
  choose T hTm hTi using ht
  obtain ⟨L, hL⟩ := hcompact.isBounded.exists_norm_le
  refine ⟨T, hTm, hTi, ?_⟩
  intro i B J z r hr
  exact riesz_source_sum_clipped_le_affine_slot q τ C_CZ ε KU KD hq hτ hτhi hC i
    hF hFs (fun j y s hy => hsupport j (y,s) (fun hw => (not_le.mpr hy) (hL y (subset_closure
      hw.1))))
    (fun j => (hTm j i).aemeasurable) (fun j => hTi j i) hN
    B J z hr

/-- Suitable data admit one jointly measurable near-field Riesz derivative
whose three-component sum satisfies the affine A slot on every clipped cell.
The source is the outer origin-cylinder restriction of `Du·u - f`. -/
theorem exists_origin_riesz_source_affine_bound_of_sws
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτhi : τ ≤ 25)
    (hC : rieszSourceThresholdA ≤ C_CZ)
    (hR : 0 < R₁) (hR₁₀ : R₁ ≤ R₀) (hR₀le : R₀ ≤ 1)
    (hKU : KU < ⊤) (hKD : KD < ⊤)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hU : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU)
    (hD : ∀ i j, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD)
    (hsize : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) :
    let F := fun j : Fin 3 => (parabolicCylinder (0 : Vec3) 0 R₀).indicator
      (fun w => ∑ k, Du w j k * u w k - f w j)
    ∃ T : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ j i, Measurable (T j i)) ∧
      (∀ j i, ∀ᵐ s ∂volume, (fun y => T j i (y,s)) =ᵐ[volume]
        rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => F j (y,s))) ∧
      ∀ (i : Fin 3) (z : ParabolicPoint) (r : ℝ), 0 < r →
        (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-(R₁^2)) 0,
          eLpNorm (fun y => ∑ j, T j i (y,s)) (ENNReal.ofReal (6/5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6/5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD *
            ENNReal.ofReal (r ^ (5*(1-(6/5 : ℝ)/min ((1/τ+8/25)⁻¹) q))) := by
  dsimp only
  let F := fun j : Fin 3 => (parabolicCylinder (0 : Vec3) 0 R₀).indicator
    (fun w => ∑ k, Du w j k * u w k - f w j)
  have hR₀ : 0 < R₀ := hR.trans_le hR₁₀
  have hd := origin_riesz_source_data q τ R₀ R₀ ε KU KD hq hτ hR₀ le_rfl hR₀le
    hsol hdom hU hD hsize
  have hF := fun j => (hd j).1
  have hN := fun j => (hd j).2
  obtain ⟨T, hTm, hTi, hb⟩ := exists_supported_riesz_affine_bound q τ C_CZ ε KU KD
    hq hτ hτhi hC hR₀ hKU hKD hF hN (fun j w hw => Set.indicator_of_notMem hw _)
  exact ⟨T, hTm, hTi, fun i z r hr =>
    hb i (vec3Ball (0 : Vec3) R₁) (Ioc (-(R₁^2)) 0) z r hr⟩

end CKN.Core.Step4
