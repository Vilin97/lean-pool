/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierTestDerivatives
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierSobolevWeights
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.SchwartzCompactApproximation
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactSchwartz
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Harmonic functionals bounded in an inhomogeneous Fourier Sobolev norm

A complex-linear Schwartz functional bounded by the Fourier `H³` norm is
represented in polynomially weighted `L²`. If it annihilates Laplacians, its
representing function vanishes away from the origin. Since volume has no atom
at the origin, the whole functional vanishes.
-/

section

/-!
# Weak uniqueness for the weighted Fourier representation

Compact smooth functions are Schwartz functions, so a locally integrable
function annihilating every Schwartz test vanishes almost everywhere. Applied
to the weighted conjugate of an `L²` function, this removes the Fourier
Laplacian multiplier away from its single zero at the origin.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.WeakFourierUniqueness

open ProblemStatement

/-- The real-test fundamental lemma, with multiplication written in `ℂ`. -/
theorem ae_eq_zero_of_integral_real_test_mul_eq_zero
    (h : Space → ℂ) (hh : LocallyIntegrable h (volume : Measure Space))
    (hzero : ∀ g : Space → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      (∫ x : Space, (g x : ℂ) * h x) = 0) :
    h =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hh
  intro g hg hs
  have hsmul : (fun x : Space => g x • h x) =
      (fun x : Space => (g x : ℂ) * h x) := by
    funext x
    apply Complex.ext <;> simp
  rw [hsmul]
  exact hzero g hg hs

/-- A locally integrable function is determined by its Schwartz pairings. -/
theorem ae_eq_zero_of_integral_schwartz_test_mul_eq_zero
    (h : Space → ℂ) (hh : LocallyIntegrable h (volume : Measure Space))
    (hzero : ∀ ψ : Comparison.ComplexTest, (∫ x : Space, h x * ψ x) = 0) :
    h =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_real_test_mul_eq_zero h hh
  intro g hg hs
  have hgC : ContDiff ℝ ∞ (fun x : Space => (g x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hg
  have hsC : HasCompactSupport (fun x : Space => (g x : ℂ)) :=
    hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have htest :=
    hzero (CompactSchwartz.ofCompactSupport (fun x : Space => (g x : ℂ)) hgC hsC)
  change (∫ x : Space, h x * (g x : ℂ)) = 0 at htest
  simpa only [mul_comm] using htest

/-- Polynomial weights preserve the local integrability of an `L²` function. -/
theorem locallyIntegrable_weighted_star (q : Lp ℂ 2 (volume : Measure Space)) :
    LocallyIntegrable (fun ξ : Space =>
      star (q ξ) * (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ))
      (volume : Measure Space) := by
  have hqstar : LocallyIntegrable (fun ξ : Space => star (q ξ))
      (volume : Measure Space) :=
    (Complex.conjCLE.toContinuousLinearMap.comp_memLp q).locallyIntegrable (by norm_num)
  have hw : Continuous (fun ξ : Space => (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.comp
      ((continuous_const.add (continuous_norm.pow 2)).pow 2)
  have hn : Continuous (fun ξ : Space => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.comp (continuous_norm.pow 2)
  exact locallyIntegrableOn_univ.mp
    (((hqstar.locallyIntegrableOn univ).mul_continuousOn hw.continuousOn
      isClosed_univ.isLocallyClosed).mul_continuousOn hn.continuousOn
      isClosed_univ.isLocallyClosed)

/-- If the weighted Fourier Laplacian pairings of an `L²` function vanish,
the function is zero in `L²`. No regularity beyond membership in `L²` is used. -/
theorem eq_zero_of_integral_weight_normSq_test_eq_zero
    (q : Lp ℂ 2 (volume : Measure Space))
    (hq : ∀ ψ : Comparison.ComplexTest,
      (∫ ξ : Space, star (q ξ) * (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        ((‖ξ‖ ^ 2 : ℝ) : ℂ) * ψ ξ) = 0) :
    q = 0 := by
  have hz : (fun ξ : Space =>
      star (q ξ) * (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ))
      =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_schwartz_test_mul_eq_zero _
      (locallyIntegrable_weighted_star q) hq
  have hne : ∀ᵐ ξ : Space ∂volume, ξ ≠ 0 := by
    simp [ae_iff]
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hz, hne] with ξ hξ hξne
  have hwR : (1 + ‖ξ‖ ^ 2) ^ 2 ≠ (0 : ℝ) :=
    pow_ne_zero 2 (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)))
  have hw : (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hwR
  have hnR : ‖ξ‖ ^ 2 ≠ (0 : ℝ) :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hξne)
  have hn : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hnR
  have hs : star (q ξ) = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hξ).resolve_right hn)).resolve_right hw
  simpa only [star_star, star_zero, Pi.zero_apply] using congrArg star hs

end NavierStokesR3.WeakFourierUniqueness

end
end

end

section

/-!
# Hilbert-space representation of a functional bounded through an embedding

A linear functional on a complex vector space that is bounded in the norm of an
injective linear map into a Hilbert space is represented by an inner product in
that Hilbert space. No topology on the source vector space is needed.
-/

@[expose] public section

namespace NavierStokesR3.HilbertFunctionalExtension

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℂ E]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Transfer a functional to the range of an injective linear map, extend it by
Hahn–Banach, and represent the extension by the Hilbert-space inner product. -/
theorem exists_inner_representation (B : E →ₗ[ℂ] H)
    (hB : Function.Injective B) (F : E →ₗ[ℂ] ℂ) {C : ℝ}
    (hbound : ∀ x : E, ‖F x‖ ≤ C * ‖B x‖) :
    ∃ q : H, ∀ x : E, F x = @inner ℂ H _ q (B x) := by
  classical
  let e : E ≃ₗ[ℂ] LinearMap.range B := LinearEquiv.ofInjective B hB
  let f : LinearMap.range B →ₗ[ℂ] ℂ := F.comp e.symm.toLinearMap
  have he (z : LinearMap.range B) : B (e.symm z) = (z : H) := by
    change ((e (e.symm z) : LinearMap.range B) : H) = (z : H)
    rw [e.apply_symm_apply]
  have hf : ∀ z : LinearMap.range B, ‖f z‖ ≤ C * ‖z‖ := by
    intro z
    change ‖F (e.symm z)‖ ≤ C * ‖(z : H)‖
    simpa only [he] using hbound (e.symm z)
  let fc : LinearMap.range B →L[ℂ] ℂ := f.mkContinuous C hf
  obtain ⟨G, hG, _⟩ := exists_extension_norm_eq (LinearMap.range B) fc
  refine ⟨(InnerProductSpace.toDual ℂ H).symm G, ?_⟩
  intro x
  rw [InnerProductSpace.toDual_symm_apply]
  calc
    F x = fc (e x) := by simp [fc, f]
    _ = G ((e x : LinearMap.range B) : H) := (hG (e x)).symm
    _ = G (B x) := rfl

end NavierStokesR3.HilbertFunctionalExtension

end

end

@[expose] public section

noncomputable section

open MeasureTheory

namespace NavierStokesR3.HarmonicTestFunctionals

open ProblemStatement Comparison

/-- Frequency L²: an abbreviation for `Lp ℂ 2 (volume : Measure Space)`. -/
abbrev FrequencyL2 := Lp ℂ 2 (volume : Measure Space)

/-- The `H³` bound supplies a Hilbert-space representative after a polynomial
Fourier embedding. No Fourier transform of arbitrary `L²` functions is needed. -/
theorem exists_inner_representation_of_fourierHNormSq_bound
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ)) :
    ∃ q : FrequencyL2, ∀ ψ : ComplexTest,
      F ψ = @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B ψ) := by
  apply HilbertFunctionalExtension.exists_inner_representation
    FourierSobolevWeights.B FourierSobolevWeights.B_injective F
  · intro ψ
    exact (hbound ψ).trans (mul_le_mul_of_nonneg_left
      (FourierSobolevWeights.sqrt_fourierHNormSq_three_le_norm_B ψ) hC)

/-- In particular, a functional with the stated Fourier bound is continuous
for the Schwartz topology. -/
theorem continuous_of_fourierHNormSq_bound
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ)) :
    Continuous F := by
  obtain ⟨q, hq⟩ := exists_inner_representation_of_fourierHNormSq_bound F hC hbound
  have hc : Continuous (fun ψ : ComplexTest =>
      @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B ψ)) :=
    continuous_const.inner FourierSobolevWeights.continuous_B
  exact hc.congr fun ψ => (hq ψ).symm

/-- A weighted `L²` representative that annihilates ordinary Laplacians is zero. -/
theorem representative_eq_zero_of_harmonic
    (q : FrequencyL2)
    (hq : ∀ ψ : ComplexTest,
      @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B (laplacianCLM ψ)) = 0) :
    q = 0 := by
  apply WeakFourierUniqueness.eq_zero_of_integral_weight_normSq_test_eq_zero q
  intro φ
  let ψ : ComplexTest := (FourierTransform.fourierCLE ℂ ComplexTest).symm φ
  have hzero := hq ψ
  rw [FourierSobolevWeights.inner_B_eq_integral] at hzero
  let c : ℂ := -(4 * (Real.pi : ℂ) ^ 2)
  have hc : c ≠ 0 := by
    dsimp [c]
    apply neg_ne_zero.mpr
    apply mul_ne_zero (by norm_num)
    exact pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
  have hi : (fun ξ : Space => star (q ξ) *
      (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        FourierTransform.fourierCLE ℂ ComplexTest (laplacianCLM ψ) ξ) =
      (fun ξ : Space => c • (star (q ξ) *
        (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ) * φ ξ)) := by
    funext ξ
    rw [fourier_laplacianCLM_apply]
    simp only [ψ, ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, c]
    ring
  rw [hi, integral_smul] at hzero
  change c * (∫ ξ : Space, star (q ξ) *
    (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ) * φ ξ) = 0 at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hc

/-- A harmonic Schwartz functional bounded in Fourier `H⁻³` vanishes. -/
theorem eq_zero_of_harmonic
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ))
    (hharmonic : ∀ ψ : ComplexTest, F (laplacianCLM ψ) = 0) : F = 0 := by
  obtain ⟨q, hq⟩ := exists_inner_representation_of_fourierHNormSq_bound F hC hbound
  have hqzero : q = 0 := representative_eq_zero_of_harmonic q (fun ψ => by
    rw [← hq]
    exact hharmonic ψ)
  ext ψ
  change F ψ = 0
  rw [hq, hqzero]
  simp

/-- The pressure-recovery form: harmonicity need only be known against compactly
supported tests. The Fourier bound supplies the continuity needed to pass to
all Schwartz tests. No pressure pairing outside compact support is assumed. -/
theorem eq_zero_of_compact_harmonic
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ))
    (hharmonic : ∀ ψ : ComplexTest, HasCompactSupport (ψ : Space → ℂ) →
      F (laplacianCLM ψ) = 0) : F = 0 := by
  apply eq_zero_of_harmonic F hC hbound
  intro ψ
  exact SchwartzCompactApproximation.continuous_zero_of_compactSupport
    (fun φ : ComplexTest => F (laplacianCLM φ))
    ((continuous_of_fourierHNormSq_bound F hC hbound).comp laplacianCLM.continuous)
    hharmonic ψ

end NavierStokesR3.HarmonicTestFunctionals
