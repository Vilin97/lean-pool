/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtension
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondWeakCertificate
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayGrowthSum
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingExterior
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingSlice
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingSwap
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairing
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Identification Extension Unconditional

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

open CKN.Foundation.Euclidean

/-- Three-halves integrability exponent for pressure. -/
def pressureExponent : ℝ≥0∞ := ENNReal.ofReal (3 / 2 : ℝ)

/- The global extension is already an `L^(3/2)` function.  This adapter
   records the restriction and subtraction estimates in the exact local
   form used by the Liouville identification. -/
theorem pressureSecondExtension_residual_local_growth
    {p₁ Tg : Vec3 → ℝ}
    (hp₁ : MemLp p₁ pressureExponent volume)
    (hTg : MemLp Tg pressureExponent volume) :
    (∀ ρ : ℝ, 0 < ρ →
      MemLp (fun x => p₁ x - Tg x) pressureExponent
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ →
        lpNorm (fun x => p₁ x - Tg x) pressureExponent
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
        (lpNorm p₁ pressureExponent volume + lpNorm Tg pressureExponent volume) *
          (1 + ρ) := by
  have hp₁' : ∀ ρ : ℝ, 0 < ρ →
      MemLp p₁ pressureExponent
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) := by
    intro ρ hρ
    exact hp₁.restrict _
  have hTg' : ∀ ρ : ℝ, 0 < ρ →
      MemLp Tg pressureExponent
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) := by
    intro ρ hρ
    exact hTg.restrict _
  constructor
  · exact memLp_euclideanBall_family_sub hp₁' hTg'
  · intro ρ hρ
    exact lpNorm_euclideanBall_growth_sub hp₁'
      (fun ρ hρ => by
        exact (lpNorm_euclideanBall_le_of_memLp_volume hp₁ hρ))
      (fun ρ hρ => by
        exact (lpNorm_euclideanBall_le_of_memLp_volume hTg hρ)) hρ

theorem pressureSecondExtension_residual_local_growth_of_source_bound
    {p₁ : Vec3 → ℝ} {G : Fin 3 → Fin 3 → Vec3 → ℝ} {E : ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : ∀ i j, HasCompactSupport (G i j))
    (hsource : (∑ i, ∑ j, lpNorm (G i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume) ≤ E ^ (2 / 3 : ℝ))
    (hE : 0 ≤ E)
    (hp₁ : MemLp p₁ (ENNReal.ofReal ((3 : ℝ) / 2)) volume) :
    (∀ ρ : ℝ, 0 < ρ →
      MemLp (fun x => p₁ x - pressureSecondExtensionOperator
        rieszSecondL2Input rieszSecondL2_weak_type G x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      ∀ ρ : ℝ, 0 < ρ →
        lpNorm (fun x => p₁ x - pressureSecondExtensionOperator
          rieszSecondL2Input rieszSecondL2_weak_type G x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
        (lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume +
          czP1OperatorConstant * E ^ (2 / 3 : ℝ)) * (1 + ρ) := by
  have hT : MemLp (pressureSecondExtensionOperator
      rieszSecondL2Input rieszSecondL2_weak_type G)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    pressureSecondExtension_memLp rieszSecondL2Input
      rieszSecondL2_weak_type hG
  have hTbound : lpNorm (pressureSecondExtensionOperator
      rieszSecondL2Input rieszSecondL2_weak_type G)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      czP1OperatorConstant * E ^ (2 / 3 : ℝ) :=
    pressureSecondExtension_operator_bound_unconditional hG hGc hsource hE
  have hlocal := pressureSecondExtension_residual_local_growth hp₁ hT
  constructor
  · exact hlocal.1
  · intro ρ hρ
    have hbound := hlocal.2 ρ hρ
    have hsum : lpNorm p₁ pressureExponent volume +
        lpNorm (pressureSecondExtensionOperator
          rieszSecondL2Input rieszSecondL2_weak_type G) pressureExponent volume ≤
        lpNorm p₁ pressureExponent volume +
          czP1OperatorConstant * E ^ (2 / 3 : ℝ) := by
      simpa only [pressureExponent, add_comm] using
        (add_le_add_left hTbound (lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume))
    simpa only [pressureExponent] using
      (hbound.trans (mul_le_mul_of_nonneg_right
        hsum (by linarith only [hρ])))

/-!
The endpoint weak-type certificate is now unconditional.  This adapter fixes
the extension to the canonical L² inputs and removes the operator-bound
function from the pressure identification interface.
-/

theorem pressureP1_hident_of_pressureSecondExtension_unconditional
    {p₁ : Vec3 → ℝ} {G : Fin 3 → Fin 3 → Vec3 → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hP1 : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume →
      ∫ x, p₁ x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hP1Int : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume)
    (hmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp (fun x => p₁ x - pressureSecondExtensionOperator
        rieszSecondL2Input rieszSecondL2_weak_type G x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hgrowth : ∀ ρ : ℝ, 0 < ρ →
      lpNorm (fun x => p₁ x - pressureSecondExtensionOperator
        rieszSecondL2Input rieszSecondL2_weak_type G x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ)) :
    p₁ =ᵐ[volume] pressureSecondExtensionOperator
      rieszSecondL2Input rieszSecondL2_weak_type G := by
  apply pressureP1_hident_of_pressureSecondExtension
    rieszSecondL2Input rieszSecondL2_weak_type hC hG hP1 hP1Int
  · intro ψ hψ hψc
    let _ : ENNReal.HolderConjugate (ENNReal.ofReal (3 / 2 : ℝ))
        (ENNReal.ofReal (3 : ℝ)) :=
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
        Real.HolderConjugate (3 / 2 : ℝ) 3).ennrealOfReal
    have hlap : MemLp (spatialLaplacian ψ) (ENNReal.ofReal (3 : ℝ)) volume :=
      (contDiff_spatialLaplacian_smooth hψ).continuous.memLp_of_hasCompactSupport
        (CKN.Foundation.Heat.laplacian_compact_support_global hψc)
    exact (pressureSecondExtension_memLp rieszSecondL2Input
      rieszSecondL2_weak_type hG).integrable_mul hlap
  · exact hmem
  · exact hgrowth

/- The endpoint adapter above is the fixed-time assembly.  This wrapper keeps
   the time exceptional sets together and consumes the established global pairing
   producer, so the remaining residual input is visible at exactly the
   Liouville interface rather than being hidden in the operator estimate. -/
theorem pressureP1_hCZ_slice_of_unconditional_extension
    (C_CZ : ℝ) (hC_CZ : 0 ≤ C_CZ)
    (hoperator : czP1OperatorConstant ≤ C_CZ)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {c : ℝ → Vec3}
    (hG : ∀ᵐ s ∂volume.restrict I,
      ∀ i j, MemLp (fun x => η x * pressureUTensor u c (x, s) i j)
        (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : ∀ᵐ s ∂volume.restrict I,
      ∀ i j, HasCompactSupport
        (fun x => η x * pressureUTensor u c (x, s) i j))
    (hsource : ∀ᵐ s ∂volume.restrict I,
      (∑ i, ∑ j, lpNorm (fun x => η x * pressureUTensor u c (x, s) i j)
        (ENNReal.ofReal ((3 : ℝ) / 2)) volume) ≤
        (∫ x, pressureUTensorNorm u c s x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ))
    (hresidual : ∀ᵐ s ∂volume.restrict I, ∃ C : ℝ, 0 ≤ C ∧
      (∀ ρ : ℝ, 0 < ρ →
        MemLp (fun x => pressureP1 η u c p f s x -
          pressureSecondExtensionOperator rieszSecondL2Input
            rieszSecondL2_weak_type
            (fun i j x => η x * pressureUTensor u c (x, s) i j) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
      (∀ ρ : ℝ, 0 < ρ →
        lpNorm (fun x => pressureP1 η u c p f s x -
          pressureSecondExtensionOperator rieszSecondL2Input
            rieszSecondL2_weak_type
            (fun i j x => η x * pressureUTensor u c (x, s) i j) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ))) :
    ∀ᵐ s ∂volume.restrict I,
      MemLp (pressureP1 η u c p f s)
          (ENNReal.ofReal ((3 : ℝ) / 2)) volume ∧
        lpNorm (pressureP1 η u c p f s)
          (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
          C_CZ * (∫ x, pressureUTensorNorm u c s x ^ (3 / 2 : ℝ)) ^
            (2 / 3 : ℝ) := by
  have hP1 := pressureP1_cz_hP1_ae_of_sws hsol hη hηc hηΩ c
  have hP1Int := pressureP1_cz_hP1Int_ae_of_sws hsol hη hηc hηΩ c
  have hV : ∀ᵐ s ∂volume.restrict I,
      0 ≤ ∫ x, pressureUTensorNorm u c s x ^ (3 / 2 : ℝ) := by
    filter_upwards [] with s
    exact integral_nonneg (fun x => by
      have hx : 0 ≤ pressureUTensorNorm u c s x := by
        unfold pressureUTensorNorm
        positivity
      exact Real.rpow_nonneg hx _)
  filter_upwards [hP1, hP1Int, hG, hGc, hsource, hresidual, hV]
    with s hsP1 hsP1Int hsG hsGc hsSource hsResidual hsV
  obtain ⟨C, hC, hmem, hgrowth⟩ := hsResidual
  have hident := pressureP1_hident_of_pressureSecondExtension_unconditional
    hC hsG hsP1 hsP1Int hmem hgrowth
  have hTmem := pressureSecondExtension_memLp rieszSecondL2Input
    rieszSecondL2_weak_type hsG
  have hbound := hCZ_p1_unconditional C_CZ C_CZ
    (∫ x, pressureUTensorNorm u c s x ^ (3 / 2 : ℝ)) C
    hC_CZ hoperator le_rfl hsV hC
    (G := fun i j x => η x * pressureUTensor u c (x, s) i j)
    hsG hsGc hsSource (p₁ := pressureP1 η u c p f s)
    hsP1 hsP1Int hmem hgrowth
  exact ⟨hTmem.ae_eq hident.symm, hbound⟩

end CKN
