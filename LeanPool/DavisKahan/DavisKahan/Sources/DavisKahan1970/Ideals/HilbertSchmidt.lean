/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ComplexificationApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Inv

/-!
# The source square or Hilbert--Schmidt norm

The second generalized sine theorem is specifically a square-norm theorem.  It
cannot be represented by the arbitrary-norm ideal family unless an actual
Hilbert--Schmidt instance has been constructed.  This module gives a scalar-
generic, rectangular definition directly from the complete approximation-
number sequence.

The extended energy is `sum_n a_n(A)^2`.  Membership means this extended sum is
finite, and the norm is its square root.  This is basis free and immediately
compatible with every singular-value transport theorem in the repository.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal
open TauCeti.RealComplexification


noncomputable section

universe u vE vF vG vH vE1 vF1 vE2 vF2

/-- Extended Hilbert--Schmidt energy, defined by the squared approximation
singular-value sequence. -/
def approximationNumberEnergy
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (A : E →L[𝕜] F) : ENNReal :=
  ∑' n : ℕ, ENNReal.ofReal ((approximationSingularValue n A) ^ 2)


/-- The zero operator has zero Hilbert--Schmidt energy. -/
@[simp]
theorem approximationNumberEnergy_zero
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]  :
    approximationNumberEnergy (0 : E →L[𝕜] F) = 0 := by
  unfold approximationNumberEnergy
  simp



/-- Complete singular-value equality preserves Hilbert--Schmidt energy. -/
theorem SameApproximationSingularSequence.approximationNumberEnergy_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) :
    approximationNumberEnergy A = approximationNumberEnergy B := by
  unfold approximationNumberEnergy
  congr 1
  funext n
  exact congrArg (fun x : ℝ => ENNReal.ofReal (x ^ 2)) (h n)

/-- Complete singular-value equality preserves Hilbert--Schmidt membership. -/
theorem SameApproximationSingularSequence.approximationNumberEnergy_ne_top_iff
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ : Type vE1} {F₁ : Type vF1}
    {E₂ : Type vE2} {F₂ : Type vF2}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) :
    approximationNumberEnergy A ≠ ⊤ ↔ approximationNumberEnergy B ≠ ⊤ := by
  rw [h.approximationNumberEnergy_eq]


/-- Adjoint invariance of Hilbert--Schmidt membership. -/
theorem approximationNumberEnergy_ne_top_adjoint_iff
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    approximationNumberEnergy A.adjoint ≠ ⊤ ↔ approximationNumberEnergy A ≠ ⊤ := by
  apply SameApproximationSingularSequence.approximationNumberEnergy_ne_top_iff
  intro n
  exact approximationSingularValue_adjoint n A



/-- Real complexification preserves Hilbert--Schmidt energy exactly. -/
theorem approximationNumberEnergy_complexify
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) :
    approximationNumberEnergy (RealComplexification.complexify A) =
      approximationNumberEnergy A := by
  unfold approximationNumberEnergy
  congr 1
  funext n
  rw [ComplexificationApproximation.approximationSingularValue_complexify]

/-- Real complexification preserves square-norm membership. -/
theorem approximationNumberEnergy_ne_top_complexify_iff
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) :
    approximationNumberEnergy (RealComplexification.complexify A) ≠ ⊤ ↔
      approximationNumberEnergy A ≠ ⊤ := by
  rw [approximationNumberEnergy_complexify]


/-- Scaling law for Hilbert--Schmidt energy. -/
theorem approximationNumberEnergy_smul
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (c : 𝕜) (A : E →L[𝕜] F) :
    approximationNumberEnergy (c • A) =
      ENNReal.ofReal (‖c‖ ^ 2) * approximationNumberEnergy A := by
  unfold approximationNumberEnergy
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext n
  rw [approximationSingularValue_smul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _)]


/-- Nonzero scalar multiplication preserves Hilbert--Schmidt membership. -/
theorem approximationNumberEnergy_ne_top_smul_iff
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (c : 𝕜) (hc : c ≠ 0) (A : E →L[𝕜] F) :
    approximationNumberEnergy (c • A) ≠ ⊤ ↔ approximationNumberEnergy A ≠ ⊤ := by
  rw [approximationNumberEnergy_smul]
  constructor
  · intro h
    by_contra hA
    have htop : approximationNumberEnergy A = ⊤ := by simpa using hA
    rw [htop, ENNReal.mul_top] at h
    · exact h rfl
    · simp [hc]
  · intro hA
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA

/-- Negation preserves Hilbert--Schmidt membership. -/
@[simp]
theorem approximationNumberEnergy_ne_top_neg_iff
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    approximationNumberEnergy (-A) ≠ ⊤ ↔ approximationNumberEnergy A ≠ ⊤ := by
  have h := approximationNumberEnergy_ne_top_smul_iff (-1 : 𝕜) (by simp) A
  rwa [neg_one_smul] at h



/-- Two-sided ideal control of the extended Hilbert--Schmidt energy. -/
theorem approximationNumberEnergy_comp_le
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    {G : Type vG} {H : Type vH}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    approximationNumberEnergy (L ∘L A ∘L R) ≤
      ENNReal.ofReal ((‖L‖ * ‖R‖) ^ 2) *
        approximationNumberEnergy A := by
  unfold approximationNumberEnergy
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  have hsing := approximationSingularValue_comp_le n L A R
  have hnonneg : 0 ≤ approximationSingularValue n (L ∘L A ∘L R) :=
    approximationSingularValue_nonneg _ _
  have hbound :
      approximationSingularValue n (L ∘L A ∘L R) ^ 2 ≤
        (‖L‖ * ‖R‖) ^ 2 * approximationSingularValue n A ^ 2 := by
    calc
      approximationSingularValue n (L ∘L A ∘L R) ^ 2
          ≤ (‖L‖ * approximationSingularValue n A * ‖R‖) ^ 2 :=
        pow_le_pow_left₀ hnonneg hsing 2
      _ = (‖L‖ * ‖R‖) ^ 2 * approximationSingularValue n A ^ 2 := by ring
  rw [← ENNReal.ofReal_mul (sq_nonneg (‖L‖ * ‖R‖))]
  exact ENNReal.ofReal_le_ofReal hbound

/-- **The two-sided ideal property**, at the level of finite approximation-number
energy.  `ContinuousLinearMap.IsHilbertSchmidt.comp` is the same fact about the
canonical predicate; the two are identified by `isHilbertSchmidt_iff_approximationNumberEnergy_ne_top`
once the coordinate bridge is in scope. -/
theorem approximationNumberEnergy_ne_top_comp
    {𝕜 : Type u} [RCLike 𝕜]
    {E : Type vE} {F : Type vF}
    {G : Type vG} {H : Type vH}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {A : E →L[𝕜] F} (hA : approximationNumberEnergy A ≠ ⊤)
    (L : F →L[𝕜] G) (R : H →L[𝕜] E) :
    approximationNumberEnergy (L ∘L A ∘L R) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (approximationNumberEnergy_comp_le L A R)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA




end

end ExactSinTheta
end DavisKahan
end TauCeti
