/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionCZ
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondWeakCertificate
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtension

/-!
# CZUnconditional

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-! # Unconditional endpoint adapters

The weak endpoint and the indexed L² input are now concrete.  This file only
retains the distributional identification data which are not consequences of
the endpoint estimate.
-/

/-- The explicit constant for the selected vector-valued gradient operator. -/
@[expose]
def czGradientOperatorConstant : ℝ :=
  3 * czGradientComponentConstant rieszSecondWeakTypeConstant 1

/-- The explicit component constant at exponent `3 / 2`. -/
@[expose]
def czP1OperatorConstant : ℝ :=
  czP1Constant rieszSecondWeakTypeConstant 1

/-- The selected signed gradient extension obeys its CZ operator bound. -/
theorem hasCZGradientOperatorBound_unconditional :
    HasCZGradientOperatorBound
      (fun i j G x => -(rieszSecondGradientExtensionOperator
        (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) G x))
      czGradientOperatorConstant := by
  apply hCZ_grad_of_rieszSecond_l2_extension
    (hL2 := fun i j => rieszSecondL2Input i j)
    (hWeak11 := fun i j => rieszSecondL2_weak_type i j)
  exact le_rfl

/-- The scalar indexed extension has the exact `hT` norm-bound shape. -/
theorem rieszSecondP1_extension_operator_bound_unconditional
    (i j : Fin 3) {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : HasCompactSupport G) :
    lpNorm (rieszSecondP1ExtensionOperator
      (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) G)
        (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
      czP1OperatorConstant *
        lpNorm G (ENNReal.ofReal ((3 : ℝ) / 2)) volume := by
  have hbound := rieszSecondP1Extension_toLp_bound
    (rieszSecondL2Input i j) (rieszSecondL2_weak_type i j) hG hGc
  rw [Lp.norm_toLp, Lp.norm_toLp] at hbound
  rw [lpNorm, lpNorm]
  simpa only [eLpNorm_congr_ae
    (rieszSecondP1Extension_memLp (rieszSecondL2Input i j)
      (rieszSecondL2_weak_type i j) hG hGc).coeFn_toLp,
    eLpNorm_congr_ae hG.coeFn_toLp, czP1OperatorConstant] using hbound

/-- The tensor extension has the nine-index pressure norm bound. -/
theorem pressureSecondExtension_operator_bound_unconditional
    {G : Fin 3 → Fin 3 → Vec3 → ℝ} {E : ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : ∀ i j, HasCompactSupport (G i j))
    (hsource : (∑ i, ∑ j, lpNorm (G i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume) ≤ E ^ (2 / 3 : ℝ))
    (hE : 0 ≤ E) :
    lpNorm (pressureSecondExtensionOperator
      rieszSecondL2Input rieszSecondL2_weak_type G)
        (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
      czP1OperatorConstant * E ^ (2 / 3 : ℝ) := by
  apply pressure_lpNorm_le_of_rieszSecond_p1_tensor_extension
    (hL2 := fun i j => rieszSecondL2Input i j)
    (hWeak11 := fun i j => rieszSecondL2_weak_type i j)
    (hG := hG) (hGc := hGc)
    (hident := Eventually.of_forall (fun _ => rfl))
    (hsource := hsource)
    (hconst := le_rfl) (hE := hE)

end CKN.Foundation.Euclidean

namespace CKN

open CKN.Foundation.Euclidean

/-- The pressure CZ estimate after the exact remaining identification data are
 supplied.  The numerical constants precede the pressure and source data. -/
theorem hCZ_p1_unconditional
    (C_CZ C₁₁ E C : ℝ)
    (_ : 0 ≤ C_CZ) (hoperator : czP1OperatorConstant ≤ C_CZ)
    (hconst : C_CZ ≤ C₁₁)
    (hE : 0 ≤ E) (hC : 0 ≤ C)
    {p₁ : Vec3 → ℝ} {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : ∀ i j, HasCompactSupport (G i j))
    (hsource : (∑ i, ∑ j, lpNorm (G i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume) ≤ E ^ (2 / 3 : ℝ))
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
    lpNorm p₁ (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
      C₁₁ * E ^ (2 / 3 : ℝ) := by
  have hident := pressureP1_hident_of_pressureSecondExtension
    (fun i j => rieszSecondL2Input i j)
    (fun i j => rieszSecondL2_weak_type i j) hC hG hP1 hP1Int
    (by
      intro ψ hψ hψc
      let _ : ENNReal.HolderConjugate (ENNReal.ofReal (3 / 2 : ℝ))
          (ENNReal.ofReal (3 : ℝ)) :=
        (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
          Real.HolderConjugate (3 / 2 : ℝ) 3).ennrealOfReal
      have hlap : MemLp (spatialLaplacian ψ) (ENNReal.ofReal (3 : ℝ)) volume :=
        (contDiff_spatialLaplacian_smooth hψ).continuous.memLp_of_hasCompactSupport
          (CKN.Foundation.Heat.laplacian_compact_support_global hψc)
      exact (pressureSecondExtension_memLp
        (fun i j => rieszSecondL2Input i j)
        (fun i j => rieszSecondL2_weak_type i j) hG).integrable_mul hlap)
    hmem hgrowth
  have hp := pressure_lpNorm_le_of_rieszSecond_p1_tensor_extension
    (C_CZ := C_CZ)
    (hL2 := fun i j => rieszSecondL2Input i j)
    (hWeak11 := fun i j => rieszSecondL2_weak_type i j)
    (hG := hG) (hGc := hGc) hident hsource
    (by exact hoperator)
    hE
  exact hp.trans (mul_le_mul_of_nonneg_right hconst
    (Real.rpow_nonneg hE _))

end CKN
