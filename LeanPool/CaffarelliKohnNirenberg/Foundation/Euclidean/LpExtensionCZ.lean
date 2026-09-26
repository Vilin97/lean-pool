/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZInputs
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairingMain
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondWeakCertificate
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CZConsumption
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.PressureCZConsumption
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.RieszWeakGradient

/-!
# Lp Extension CZ

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN
open CKN.Foundation.Parabolic

theorem hCZ_p1_of_rieszSecond_l2_extension
    {i j : Fin 3} {p₁ g : Vec3 → ℝ} {C_CZ E : ℝ}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hg : MemLp g (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hgc : HasCompactSupport g)
    (hident : p₁ =ᵐ[volume] rieszSecondP1ExtensionOperator hL2 hWeak11 g)
    (hsource : lpNorm g (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤ E ^ (2 / 3 : ℝ))
    (hC_CZ : 0 ≤ C_CZ)
    (hconst : czP1Constant rieszSecondWeakTypeConstant 1 ≤ C_CZ)
    (hE : 0 ≤ E) :
    lpNorm p₁ (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤ C_CZ * E ^ (2 / 3 : ℝ) := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((3 : ℝ) / 2)) := ⟨by norm_num⟩
  apply hCZ_p1_of_cz_p1_bound (T := rieszSecondP1ExtensionOperator hL2 hWeak11)
  · intro f hf hfc
    have hb := rieszSecondP1Extension_toLp_bound hL2 hWeak11 hf hfc
    rw [Lp.norm_toLp, Lp.norm_toLp] at hb
    have hb' : lpNorm (rieszSecondP1ExtensionOperator hL2 hWeak11 f)
        (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
        czP1Constant rieszSecondWeakTypeConstant 1 *
          lpNorm f (ENNReal.ofReal ((3 : ℝ) / 2)) volume := by
      rw [lpNorm, lpNorm]
      simpa only [eLpNorm_congr_ae
        (rieszSecondP1Extension_memLp hL2 hWeak11 hf hfc).coeFn_toLp,
        eLpNorm_congr_ae hf.coeFn_toLp] using hb
    exact hb'.trans (mul_le_mul_of_nonneg_right hconst lpNorm_nonneg)
  · exact hg
  · exact hgc
  · exact hident
  · exact hsource
  · exact hC_CZ
  · exact le_rfl
  · exact hE

theorem hCZ_grad_of_rieszSecond_l2_extension
    {C_CZ : ℝ}
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hconst : 3 * czGradientComponentConstant rieszSecondWeakTypeConstant 1 ≤ C_CZ) :
    HasCZGradientOperatorBound
      (fun i j G x => -(rieszSecondGradientExtensionOperator
        (hL2 i j) (hWeak11 i j) G x)) C_CZ := by
  apply hCZ_grad_of_rieszSecond_inputs
    (Ccomp := czGradientComponentConstant rieszSecondWeakTypeConstant 1)
    (C_CZ := C_CZ)
  · unfold czGradientComponentConstant
    positivity
  · exact hconst
  · intro i j G hG hGc
    change eLpNorm (-rieszSecondGradientExtensionOperator
      (hL2 i j) (hWeak11 i j) G)
        (ENNReal.ofReal ((6 : ℝ) / 5)) volume ≤ _
    rw [eLpNorm_neg]
    exact CKN.Core.Endgame.eLpNorm_le_of_toLp_norm_le hG
      (rieszSecondGradientExtension_memLp (hL2 i j) (hWeak11 i j) hG hGc)
      (by unfold czGradientComponentConstant; positivity)
      (rieszSecondGradientExtension_toLp_bound (hL2 i j) (hWeak11 i j) hG hGc)

/-- Consume the positive pairing of the completed extension and return the
selected negative weak-gradient field. -/
theorem exists_weak_pressure_gradient_of_rieszSecond_l2_extension
    (C_CZ : ℝ)
    (hconst : 3 * czGradientComponentConstant rieszSecondWeakTypeConstant 1 ≤ C_CZ)
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hpair : ∀ i j (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
        ∫ x, rieszSecondGradientExtensionOperator (hL2 i j) (hWeak11 i j) G x * ψ x) :
    ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  exact CKN.Core.Endgame.exists_weak_pressure_gradient_of_riesz_extension
    C_CZ hconst hL2 hWeak11 hpair

/-- The completed weak-gradient output with concrete endpoint data and the
positive pairing supplied by the extension theorem. -/
theorem exists_weak_pressure_gradient_of_rieszSecond_l2_extension_unconditional
    (C_CZ : ℝ)
    (hconst : 3 * czGradientComponentConstant rieszSecondWeakTypeConstant 1 ≤ C_CZ) :
    ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  exact exists_weak_pressure_gradient_of_rieszSecond_l2_extension C_CZ hconst
    (hL2 := fun i j => rieszSecondL2Input i j)
    (hWeak11 := fun i j => rieszSecondL2_weak_type i j)
    (hpair := rieszSecondGradientExtension_weak_gradient_pairing
      (fun i j => rieszSecondL2Input i j)
      (fun i j => rieszSecondL2_weak_type i j))

/-- Tensor second-Riesz operator at exponent three-halves, built from L² and weak-(1,1) data. -/
@[expose] def rieszSecondP1ExtensionTensorOperator
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (G : Fin 3 → Fin 3 → Vec3 → ℝ) : Vec3 → ℝ := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((3 : ℝ) / 2)) := ⟨by norm_num⟩
  exact lpExtensionTensorOperator (by norm_num)
    (fun i j => rieszSecondP1ExtensionInput (hL2 i j) (hWeak11 i j)) G

theorem rieszSecondP1ExtensionTensor_memLp
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume) :
    MemLp (rieszSecondP1ExtensionTensorOperator hL2 hWeak11 G)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((3 : ℝ) / 2)) := ⟨by norm_num⟩
  exact lpExtensionTensorOperator_memLp (by norm_num)
    (fun i j => rieszSecondP1ExtensionInput (hL2 i j) (hWeak11 i j)) hG

theorem rieszSecondP1ExtensionTensor_eLpNorm_le
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : ∀ i j, HasCompactSupport (G i j)) :
    eLpNorm (rieszSecondP1ExtensionTensorOperator hL2 hWeak11 G)
        (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
      ∑ i, ∑ j, ENNReal.ofReal (czP1Constant rieszSecondWeakTypeConstant 1) *
        eLpNorm (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((3 : ℝ) / 2)) := ⟨by norm_num⟩
  apply lpExtensionTensorOperator_eLpNorm_le (by norm_num)
    (fun i j => rieszSecondP1ExtensionInput (hL2 i j) (hWeak11 i j))
    (fun i j => by unfold czP1Constant; positivity) hG hGc
  norm_num

theorem pressure_lpNorm_le_of_rieszSecond_p1_tensor_extension
    {p₁ : Vec3 → ℝ} {E C_CZ : ℝ}
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hGc : ∀ i j, HasCompactSupport (G i j))
    (hident : p₁ =ᵐ[volume]
      rieszSecondP1ExtensionTensorOperator hL2 hWeak11 G)
    (hsource : (∑ i, ∑ j, lpNorm (G i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume) ≤ E ^ (2 / 3 : ℝ))
    (hconst : czP1Constant rieszSecondWeakTypeConstant 1 ≤ C_CZ)
    (hE : 0 ≤ E) :
    lpNorm p₁ (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤ C_CZ * E ^ (2 / 3 : ℝ) := by
  let _ : Fact (1 ≤ ENNReal.ofReal ((3 : ℝ) / 2)) := ⟨by norm_num⟩
  let T : Fin 3 → Fin 3 → (Vec3 → ℝ) → Vec3 → ℝ :=
    fun i j => rieszSecondP1ExtensionOperator (hL2 i j) (hWeak11 i j)
  have hTG : ∀ i j, MemLp (T i j (G i j))
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume := by
    intro i j
    exact rieszSecondP1Extension_memLp (hL2 i j) (hWeak11 i j) (hG i j) (hGc i j)
  have hbound : ∀ i j, eLpNorm (T i j (G i j))
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
      ENNReal.ofReal (czP1Constant rieszSecondWeakTypeConstant 1) *
        eLpNorm (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume := by
    intro i j
    exact CKN.Core.Endgame.eLpNorm_le_of_toLp_norm_le (hG i j) (hTG i j)
      (by unfold czP1Constant; positivity)
      (rieszSecondP1Extension_toLp_bound (hL2 i j) (hWeak11 i j)
        (hG i j) (hGc i j))
  have hident' : p₁ =ᵐ[volume] fun x => ∑ i, ∑ j, T i j (G i j) x := by
    filter_upwards [hident] with x hx
    calc
      p₁ x = rieszSecondP1ExtensionTensorOperator hL2 hWeak11 G x := hx
      _ = ∑ i, ∑ j, T i j (G i j) x := by
        simp only [T, rieszSecondP1ExtensionTensorOperator,
          lpExtensionTensorOperator, lpExtensionOperator,
          rieszSecondP1ExtensionOperator]
  exact CKN.Core.Endgame.pressure_lpNorm_le_of_tensor_bounds T G hG hTG hbound
    hident' hsource (by unfold czP1Constant; positivity) hconst hE

end CKN.Foundation.Euclidean
