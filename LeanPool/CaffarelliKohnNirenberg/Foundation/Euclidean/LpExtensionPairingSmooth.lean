/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZInputs
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondL2Input
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionInputCast

/-! # The completed gradient component on smooth compactly supported data

The completed `L^(6/5)` operator is built from the `L²` carrier by a
norm-controlled extension, so on data that already lies in `L²` it reproduces
the raw `L²` operator, and on smooth compactly supported data the raw operator
is the classical Hessian `∂ᵢ∂ⱼ(N * G)` of the Newtonian potential.  This is the
only place where a classical representative of the completed operator is
identified, and it is used exactly on the dense class of test data.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- The underlying map of the exponent `6 / 5` extension input is the raw
`L²` operator. -/
theorem rieszSecondGradientExtensionInput_T {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l) :
    (rieszSecondGradientExtensionInput hL2 hWeak11).T =
      rieszSecondL2RawOperator hL2 := by
  simp only [rieszSecondGradientExtensionInput]
  dsimp only [czGradientComponentConstant, id]
  rw [lpExtensionInput_mp_T (by norm_num [czGradientComponentConstant])]
  rfl

/-- On data lying in both `L^(6/5)` and `L²` the completed operator agrees
almost everywhere with the raw `L²` operator. -/
theorem rieszSecondGradientExtensionOperator_ae_raw {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal ((6 : ℝ) / 5)) volume)
    (hf₂ : MemLp f (2 : ℝ≥0∞) volume) :
    rieszSecondGradientExtensionOperator hL2 hWeak11 f =ᵐ[volume]
      rieszSecondL2RawOperator hL2 f := by
  have : Fact (1 ≤ ENNReal.ofReal ((6 : ℝ) / 5)) := ⟨by norm_num⟩
  have hrep := lpExtensionRepresentative_ae_eq_T (p := ENNReal.ofReal ((6 : ℝ) / 5))
    (by norm_num) (rieszSecondGradientExtensionInput hL2 hWeak11) hf hf₂
  rw [rieszSecondGradientExtensionInput_T] at hrep
  exact hrep

/-- On smooth compactly supported data the completed gradient component is the
classical Hessian `∂ᵢ∂ⱼ(N * G)` of the Newtonian potential. -/
theorem rieszSecondGradientExtension_smooth_ae {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Vec3 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    rieszSecondGradientExtensionOperator hL2 hWeak11 G =ᵐ[volume]
      mixedSecond (pressureNewtonianPotential G) i j := by
  have hG₆ : MemLp G (ENNReal.ofReal ((6 : ℝ) / 5)) volume :=
    hG.continuous.memLp_of_hasCompactSupport hGc
  have hG₂ : MemLp G (2 : ℝ≥0∞) volume :=
    hG.continuous.memLp_of_hasCompactSupport hGc
  obtain ⟨hmem, hsmooth⟩ := rieszSecondL2Extension_smooth_hessian hL2 hG hGc
  have hsmooth' : rieszSecondL2Extension hL2 (MemLp.toLp G hG₂) =
      MemLp.toLp (mixedSecond (pressureNewtonianPotential G) i j) hmem := hsmooth
  refine (rieszSecondGradientExtensionOperator_ae_raw hL2 hWeak11 hG₆ hG₂).trans ?_
  calc
    rieszSecondL2RawOperator hL2 G =ᵐ[volume]
        rieszSecondL2MeasurableOperator hL2 (MemLp.toLp G hG₂) :=
      rieszSecondL2RawOperator_ae_eq hL2 hG₂
    _ =ᵐ[volume]
        ((rieszSecondL2Extension hL2 (MemLp.toLp G hG₂) : rieszSecondL2) : Vec3 → ℝ) :=
      rieszSecondL2MeasurableOperator_ae_eq_extension hL2 _
    _ =ᵐ[volume]
        ((MemLp.toLp (mixedSecond (pressureNewtonianPotential G) i j) hmem :
          rieszSecondL2) : Vec3 → ℝ) := by
      rw [hsmooth']
    _ =ᵐ[volume] mixedSecond (pressureNewtonianPotential G) i j := hmem.coeFn_toLp

end CKN.Foundation.Euclidean
