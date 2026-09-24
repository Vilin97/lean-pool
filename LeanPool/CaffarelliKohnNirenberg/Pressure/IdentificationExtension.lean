/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationWholeSpace
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecay
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionCZ
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TensorExtensionPairing

/-!
# Indexed pressure-extension identification

The global pressure operator in this file is the indexed `L^(3/2)` extension.
The ordinary Newtonian kernel expression is an exterior tail object and is not
used by the global identification.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

open CKN.Foundation.Euclidean

/-- Pressure reconstruction operator from the continuous second-Riesz tensor extension. -/
def pressureSecondExtensionOperator
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (G : Fin 3 → Fin 3 → Vec3 → ℝ) : Vec3 → ℝ :=
  rieszSecondP1ExtensionTensorOperator hL2 hWeak11 G

theorem pressureSecondExtension_memLp
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume) :
    MemLp (pressureSecondExtensionOperator hL2 hWeak11 G)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume := by
  exact rieszSecondP1ExtensionTensor_memLp hL2 hWeak11 hG

theorem pressureSecondExtension_distributional_identity
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, MemLp (G i j) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, pressureSecondExtensionOperator hL2 hWeak11 G x *
        spatialLaplacian ψ x =
      ∫ x, ∑ i, ∑ j, G i j x * mixedSecond ψ i j x := by
  change (∫ x, (∑ i, ∑ j,
      rieszSecondP1ExtensionOperator (hL2 i j) (hWeak11 i j) (G i j) x) *
        spatialLaplacian ψ x) = _
  exact CKN.Core.Endgame.rieszSecondP1ExtensionTensor_distributional_identity
    hL2 hWeak11 hG hψ hψc

theorem pressureP1_hident_of_indexed_extension
    {p₁ : Vec3 → ℝ} {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    {T : Fin 3 → Fin 3 → (Vec3 → ℝ) → Vec3 → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hP1 : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume →
      ∫ x, p₁ x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hDeltaT : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => (fun y => ∑ i, ∑ j, T i j (G i j) y) x *
        spatialLaplacian ψ x) volume →
      ∫ x, (fun y => ∑ i, ∑ j, T i j (G i j) y) x *
          spatialLaplacian ψ x =
        ∫ x, ∑ i, ∑ j, G i j x * mixedSecond ψ i j x)
    (hP1Int : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume)
    (hTInt : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => (fun y => ∑ i, ∑ j, T i j (G i j) y) x *
        spatialLaplacian ψ x) volume)
    (hmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp (fun x => p₁ x - (fun y => ∑ i, ∑ j, T i j (G i j) y) x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hgrowth : ∀ ρ : ℝ, 0 < ρ →
      lpNorm (fun x => p₁ x - (fun y => ∑ i, ∑ j, T i j (G i j) y) x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ)) :
    p₁ =ᵐ[volume] fun x => ∑ i, ∑ j, T i j (G i j) x := by
  apply pressureP1_eq_of_wholeSpace_identity_and_linear_growth hC hP1
  · intro ψ hψ hψc hInt
    simpa only [pressureSecondPairing] using hDeltaT ψ hψ hψc hInt
  · exact hP1Int
  · intro ψ hψ hψc
    exact hTInt ψ hψ hψc
  · exact hmem
  · exact hgrowth

/- The following adapter instantiates the abstract Liouville route with the
   indexed extension.  Its pairing is the dense-L² transfer above; the
   literal kernel operator is absent from this global route. -/
theorem pressureP1_hident_of_pressureSecondExtension
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ i j : Fin 3, ∀ f, Measurable f → Integrable f volume →
      MemLp f 2 volume → ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
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
    (hTInt : ∀ (ψ : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => pressureSecondExtensionOperator hL2 hWeak11 G x *
        spatialLaplacian ψ x) volume)
    (hmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp (fun x => p₁ x - pressureSecondExtensionOperator hL2 hWeak11 G x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hgrowth : ∀ ρ : ℝ, 0 < ρ →
      lpNorm (fun x => p₁ x - pressureSecondExtensionOperator hL2 hWeak11 G x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ)) :
    p₁ =ᵐ[volume] pressureSecondExtensionOperator hL2 hWeak11 G := by
  let T : Fin 3 → Fin 3 → (Vec3 → ℝ) → Vec3 → ℝ :=
    fun i j => rieszSecondP1ExtensionOperator (hL2 i j) (hWeak11 i j)
  have hident := pressureP1_hident_of_indexed_extension
    (T := T) (hC := hC) hP1
    (hDeltaT := by
      intro ψ hψ hψc _hInt
      exact pressureSecondExtension_distributional_identity
        hL2 hWeak11 hG hψ hψc)
    hP1Int
    (hTInt := by
      intro ψ hψ hψc
      simpa only [T, pressureSecondExtensionOperator,
        rieszSecondP1ExtensionTensorOperator, lpExtensionTensorOperator,
        lpExtensionOperator, rieszSecondP1ExtensionOperator] using
        hTInt ψ hψ hψc)
    (hmem := by
      intro ρ hρ
      simpa only [T, pressureSecondExtensionOperator,
        rieszSecondP1ExtensionTensorOperator, lpExtensionTensorOperator,
        lpExtensionOperator, rieszSecondP1ExtensionOperator] using
        hmem ρ hρ)
    (hgrowth := by
      intro ρ hρ
      simpa only [T, pressureSecondExtensionOperator,
        rieszSecondP1ExtensionTensorOperator, lpExtensionTensorOperator,
        lpExtensionOperator, rieszSecondP1ExtensionOperator] using
        hgrowth ρ hρ)
  change p₁ =ᵐ[volume] fun x => ∑ i, ∑ j,
    rieszSecondP1ExtensionOperator (hL2 i j) (hWeak11 i j) (G i j) x
  exact hident

end CKN
