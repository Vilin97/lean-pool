/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationCZP1Unconditional
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredCZ
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceVelocityCube

/-!
# CZP1 Unconditional Assembly

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

open CKN.Foundation.Euclidean

/-!
# Unconditional Calderón--Zygmund input assemblies

The endpoint singular-integral estimate is a fixed-time statement.  This file
performs the solution-level assembly for the singly centred pressure field
consumed by the theta-decay cylinder bridge.
-/

/- The source producer supplies the nine tensor components directly from the
   suitable-solution slice bounds.  Its `27` majorant is exactly the nine-entry
   sum in the endpoint estimate, hence the displayed pressure constant is
   `9 * C_CZ`. -/
theorem pressureP1_thetaDecay_hCZ_of_sws
    (C_CZ : ℝ) (hC_CZ : 0 ≤ C_CZ)
    (hoperator : czP1OperatorConstant ≤ C_CZ)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hresidual : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ R : ℝ, 0 < R →
          MemLp
            (fun x : Vec3 => pressureP1 (mollifiedBallCutoff z.1 hρ) u
              (fun t j => MeasureTheory.average
                (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
              p f s x -
              pressureSecondExtensionOperator rieszSecondL2Input
                rieszSecondL2_weak_type
                (fun i j x => mollifiedBallCutoff z.1 hρ x *
                  pressureUTensor u
                    (fun t j => MeasureTheory.average
                      (volume.restrict (vec3Ball z.1 ρ))
                      (fun y => u (y, t) j)) (x, s) i j) x)
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
        (∀ R : ℝ, 0 < R →
          lpNorm
            (fun x : Vec3 => pressureP1 (mollifiedBallCutoff z.1 hρ) u
              (fun t j => MeasureTheory.average
                (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
              p f s x -
              pressureSecondExtensionOperator rieszSecondL2Input
                rieszSecondL2_weak_type
                (fun i j x => mollifiedBallCutoff z.1 hρ x *
                  pressureUTensor u
                    (fun t j => MeasureTheory.average
                      (volume.restrict (vec3Ball z.1 ρ))
                      (fun y => u (y, t) j)) (x, s) i j) x)
            (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R))) :
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
  let c : ℝ → Vec3 := fun t j => MeasureTheory.average
    (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := mollifiedBallCutoff_smooth z.1 hρ
  have hηc : HasCompactSupport η := mollifiedBallCutoff_hasCompactSupport z.1 hρ
  obtain ⟨Ω', J, hbox, _hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hηΩ : tsupport η ⊆ Ω :=
    (pressure_cutoff_support_subset_ball z.1 hρ).trans
      (fun x hx => hbox.2.2.1 (subset_closure (_hball hx)))
  have hP1I := pressureP1_cz_hP1_ae_of_sws hsol hη hηc hηΩ c
  have hP1IntI := pressureP1_cz_hP1Int_ae_of_sws hsol hη hηc hηΩ c
  have htimeI : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I :=
    htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  have hP1 := ae_restrict_of_ae_restrict_of_subset htimeI hP1I
  have hP1Int := ae_restrict_of_ae_restrict_of_subset htimeI hP1IntI
  have hSource := pressureUTensor_source_data_ae_of_sws hsol hρ hsub
  filter_upwards [hP1, hP1Int, hSource, hresidual]
    with s hsP1 hsP1Int hsSource hsResidual
  obtain ⟨hsG, hsGc, hsSource⟩ := hsSource
  obtain ⟨C, hC, hmem, hgrowth⟩ := hsResidual
  have hnorm : pressureUTensorNorm u c s = utensorNorm u z.1 ρ s := rfl
  rw [hnorm] at hsSource
  let E : ℝ := ∫ y in vec3Ball z.1 ρ,
    (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)
  have hE : 0 ≤ E := by
    dsimp [E]
    exact integral_nonneg (fun y => Real.rpow_nonneg
      (by unfold utensorNorm; positivity) _)
  have hbound := hCZ_p1_unconditional C_CZ C_CZ (27 * E) C
    hC_CZ hoperator le_rfl (mul_nonneg (by norm_num) hE) hC
    (p₁ := pressureP1 η u c p f s)
    (G := fun i j x => η x * pressureUTensor u c (x, s) i j)
    hsG hsGc hsSource hsP1 hsP1Int hmem hgrowth
  have hident := pressureP1_hident_of_pressureSecondExtension_unconditional
    hC hsG hsP1 hsP1Int hmem hgrowth
  have hTmem := pressureSecondExtension_memLp rieszSecondL2Input
    rieszSecondL2_weak_type hsG
  have h27 : (27 : ℝ) ^ (2 / 3 : ℝ) = 9 := by
    have hbase : (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [hbase, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [Real.mul_rpow (by norm_num) hE, h27] at hbound
  refine ⟨hTmem.ae_eq hident.symm, ?_⟩
  calc
    _ ≤ C_CZ * (9 * E ^ (2 / 3 : ℝ)) := hbound
    _ = (9 * C_CZ) * E ^ (2 / 3 : ℝ) := by ring

end CKN
