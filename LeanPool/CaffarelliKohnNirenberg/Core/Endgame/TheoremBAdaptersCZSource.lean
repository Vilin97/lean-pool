/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremBAdaptersVelocitySlice
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowthSWS
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremBAdaptersCZ

/-! # The singly centred pressure estimate

For `ext:CZ` and `thm:B`, the nine tensor components contribute a factor
of nine to the pressure constant. The suitable-solution slice and residual
estimates supply every analytic input of the scalar extension estimate.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Step3
noncomputable section
namespace CKN.Core.Endgame

/-- The singly centred pressure slice bound of `ext:CZ`, including the
nine-component constant, from a suitable weak solution. -/
theorem theoremB_pressureP1_slice_of_sws
    (C_CZ : ℝ) (hC_CZ : 0 ≤ C_CZ)
    (hoperator : czP1OperatorConstant ≤ C_CZ)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp
          (fun x : Vec3 => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2)) volume ∧
        lpNorm
          (fun x : Vec3 => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2)) volume ≤
          (9 * C_CZ) *
            (∫ y in vec3Ball z.1 ρ,
              (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun t j => average
    (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := mollifiedBallCutoff_smooth z.1 hρ
  have hηc : HasCompactSupport η := mollifiedBallCutoff_hasCompactSupport z.1 hρ
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hηΩ : tsupport η ⊆ Ω :=
    (pressure_cutoff_support_subset_ball z.1 hρ).trans
      (fun _ hx => hbox.2.2.1 (subset_closure (hball hx)))
  have htimeI : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I :=
    htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  have hP1 := ae_restrict_of_ae_restrict_of_subset htimeI
    (pressureP1_cz_hP1_ae_of_sws hsol hη hηc hηΩ c)
  have hP1Int := ae_restrict_of_ae_restrict_of_subset htimeI
    (pressureP1_cz_hP1Int_ae_of_sws hsol hη hηc hηΩ c)
  have hresidual := pressureSecondExtension_residual_growth_ae_of_sws hsol hρ hsub
  have hu3 := velocity_norm_memLp_three_ae_on_ball_of_sws hsol hρ hsub
  have hslice := ae_restrict_of_ae_restrict_of_subset htime
    (slice_memLp_ae_of_sws hsol hbox)
  filter_upwards [hP1, hP1Int, hresidual, hu3, hslice]
    with s hsP1 hsP1Int hsResidual hsU hsSlice
  have humeas := hsSlice.1.aestronglyMeasurable.mono_measure
    (Measure.restrict_mono_set volume hball)
  obtain ⟨hG, hGc, hsource⟩ := pressureUTensor_source_data_of_memLp_three
    (c := c) hρ hη.continuous.measurable.aestronglyMeasurable hηc
    (pressure_cutoff_support_subset_ball z.1 hρ)
    (fun y => by
      rw [abs_of_nonneg (mollifiedBallCutoff_nonneg z.1 hρ y)]
      exact mollifiedBallCutoff_le_one z.1 hρ y) humeas hsU
  have hnorm : pressureUTensorNorm u c s = utensorNorm u z.1 ρ s := rfl
  rw [hnorm] at hsource
  obtain ⟨C, hC, hmem, hgrowth⟩ := hsResidual
  let E : ℝ := ∫ y in vec3Ball z.1 ρ,
    utensorNorm u z.1 ρ s y ^ (3 / 2 : ℝ)
  have hE : 0 ≤ E := integral_nonneg (fun y => Real.rpow_nonneg
    (by unfold utensorNorm; positivity) _)
  have hbound := hCZ_p1_unconditional C_CZ C_CZ (27 * E) C
    hC_CZ hoperator le_rfl (mul_nonneg (by norm_num) hE) hC
    (p₁ := pressureP1 η u c p f s)
    (G := fun i j x => η x * pressureUTensor u c (x, s) i j)
    hG hGc hsource hsP1 hsP1Int hmem hgrowth
  have hident := pressureP1_hident_of_pressureSecondExtension_unconditional
    hC hG hsP1 hsP1Int hmem hgrowth
  have hTmem := pressureSecondExtension_memLp rieszSecondL2Input
    rieszSecondL2_weak_type hG
  have h27 : (27 : ℝ) ^ (2 / 3 : ℝ) = 9 := by
    have hbase : (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [hbase, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [Real.mul_rpow (by norm_num) hE, h27] at hbound
  refine ⟨hTmem.ae_eq hident.symm, ?_⟩
  calc
    _ ≤ C_CZ * (9 * E ^ (2 / 3 : ℝ)) := hbound
    _ = (9 * C_CZ) * E ^ (2 / 3 : ℝ) := by ring

/-- The solution-uniform pressure input for `thm:B` and `ext:CZ`, with
an explicit constant absorbing all nine tensor components. -/
theorem theoremB_hCZ_p1_of_sws (q : ℝ) :
    (∀ (Ω : Set Vec3) (I : Set ℝ)
      (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {ρ r : ℝ}, (hρ : 0 < ρ) → 0 < r → r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint => pressureP1
          (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
          p f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
        ENNReal.ofReal (((9 * max czP1OperatorConstant 0) *
          (9 * sobolevPoincareL6Constant.toReal)) * (r / ρ)⁻¹ *
          alpha u z ρ * beta u Du z ρ)) := by
  apply theoremB_hCZ_p1_of_slice_bounds q
    ((9 * max czP1OperatorConstant 0) * (9 * sobolevPoincareL6Constant.toReal))
    (9 * max czP1OperatorConstant 0)
    (mul_nonneg (by norm_num) (le_max_right _ _)) le_rfl
  intro Ω I u Du p f hsol z ρ hρ hsub
  exact theoremB_pressureP1_slice_of_sws (max czP1OperatorConstant 0)
    (le_max_right _ _) (le_max_left _ _) hsol hρ hsub

end CKN.Core.Endgame
