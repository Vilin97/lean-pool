/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairingKernel
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairingPotential
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairingDensity
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairingSmooth

/-! # Pairing the first derivative potential with the completed operator

The first Newtonian derivative potential `Pᵢ(G) = ∂ᵢN * G` and the completed
`L^(6/5)` second-derivative operator `Tᵢⱼ` are adjoint to one another in the
distributional sense: for compactly supported `L^(6/5)` data `G` and smooth
compactly supported `ψ`,

`∫ Pᵢ(G) ∂ⱼψ = ∫ Tᵢⱼ(G) ψ`.

The sign is positive: the completed operator is the unnegated second derivative
of the Newtonian potential, so the pairing selects `-Tᵢⱼ(G)` as the weak
derivative `∂ⱼPᵢ(G)`.

The proof moves both derivatives onto the test function.  On smooth compactly
supported data the completed operator is the classical Hessian
`∂ᵢ∂ⱼ(N * G)`, and two classical integrations by parts turn the left side into
`∫ G · (N * ∂ᵢ∂ⱼψ)`.  Both sides of the resulting identity are continuous
linear functionals of `G ∈ L^(6/5)`: the left through the operator norm bound
of the extension and Hölder against `ψ ∈ L⁶`, the right through Hölder against
the Newtonian potential `N * ∂ᵢ∂ⱼψ ∈ L⁶`.  Density of smooth compactly
supported classes in `L^(6/5)` closes the argument.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- The first derivative potential is adjoint to the completed exponent
`6 / 5` operator, with a positive sign. -/
theorem pressureNewtonianDerivativePotential_gradient_extension_pairing
    {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    (hWeak11 : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator hL2 f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l)
    {G : Vec3 → ℝ} (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGc : HasCompactSupport G)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
      ∫ x, rieszSecondGradientExtensionOperator hL2 hWeak11 G x * ψ x := by
  have _hfact : Fact (1 ≤ ENNReal.ofReal ((6 : ℝ) / 5)) := ⟨by norm_num⟩
  have _hfact₆ : Fact (1 ≤ ENNReal.ofReal (6 : ℝ)) := ⟨by norm_num⟩
  have _hconj : ENNReal.HolderConjugate (ENNReal.ofReal ((6 : ℝ) / 5))
      (ENNReal.ofReal (6 : ℝ)) :=
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      Real.HolderConjugate ((6 : ℝ) / 5) 6).ennrealOfReal
  have hψmem : MemLp ψ (ENNReal.ofReal (6 : ℝ)) volume :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have hmixc : HasCompactSupport (mixedSecond ψ i j) :=
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hpot : MemLp (pressureNewtonianPotential (mixedSecond ψ i j))
      (ENNReal.ofReal (6 : ℝ)) volume :=
    pressureNewtonianPotential_memLp_six (contDiff_mixedSecond_smooth hψ i j) hmixc
  have hsmooth : ∀ F : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      (∫ x, lpExtensionRepresentative (p := ENNReal.ofReal ((6 : ℝ) / 5))
          (by norm_num) (rieszSecondGradientExtensionInput hL2 hWeak11) F x * ψ x) =
        ∫ x, F x * pressureNewtonianPotential (mixedSecond ψ i j) x := by
    intro F hF hFc
    have hext : lpExtensionRepresentative (p := ENNReal.ofReal ((6 : ℝ) / 5))
        (by norm_num) (rieszSecondGradientExtensionInput hL2 hWeak11) F =ᵐ[volume]
        mixedSecond (pressureNewtonianPotential F) i j :=
      rieszSecondGradientExtension_smooth_ae hL2 hWeak11 hF hFc
    calc
      (∫ x, lpExtensionRepresentative (p := ENNReal.ofReal ((6 : ℝ) / 5))
          (by norm_num) (rieszSecondGradientExtensionInput hL2 hWeak11) F x * ψ x)
          = ∫ x, mixedSecond (pressureNewtonianPotential F) i j x * ψ x := by
            apply integral_congr_ae
            filter_upwards [hext] with x hx
            rw [hx]
      _ = ∫ x, pressureNewtonianDerivativePotential i F x * spatialDeriv ψ j x :=
            (pressure_newtonian_derivative_potential_smooth_pairing hF hFc hψ hψc).symm
      _ = ∫ x, F x * pressureNewtonianPotential (mixedSecond ψ i j) x :=
            pressureNewtonianDerivativePotential_pairing_potential
              (hF.continuous.integrable_of_hasCompactSupport hFc) hFc hψ hψc
  have hmain := lpExtension_pairing_of_smooth_identity
    (p := ENNReal.ofReal ((6 : ℝ) / 5)) (q := ENNReal.ofReal (6 : ℝ))
    (by norm_num) (rieszSecondGradientExtensionInput hL2 hWeak11) hψmem hpot
    hsmooth hG
  rw [pressureNewtonianDerivativePotential_pairing_potential
    (integrable_of_memLp_hasCompactSupport (by norm_num) hG hGc) hGc hψ hψc]
  exact hmain.symm

/-- The indexed family of pairing identities, in the shape consumed by the
weak-gradient selection: the pairing is positive, so the selected weak
derivative is the negative of the completed operator. -/
theorem rieszSecondGradientExtension_weak_gradient_pairing
    (hL2 : ∀ i j : Fin 3, RieszSecondL2Input i j)
    (hWeak11 : ∀ (i j : Fin 3) (f : Vec3 → ℝ), Measurable f →
      Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |rieszSecondL2RawOperator (hL2 i j) f x|} ≤
          ENNReal.ofReal rieszSecondWeakTypeConstant *
            (∫⁻ x, absE f x) / ENNReal.ofReal l) :
    ∀ (i j : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
        ∫ x, rieszSecondGradientExtensionOperator (hL2 i j) (hWeak11 i j) G x * ψ x :=
  fun i j _G hG hGc _ψ hψ hψc =>
    pressureNewtonianDerivativePotential_gradient_extension_pairing
      (hL2 i j) (hWeak11 i j) hG hGc hψ hψc

end CKN.Foundation.Euclidean
