/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.UnitarilyInvariant.FamilyCore
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtBasis
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtTensor
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtApproximationNorm
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Conjugation
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Group
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralGap
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Generator

/-!
# The complex rectangular Hilbert--Schmidt ideal family

The paper square norm is already defined through approximation singular values
and is identified with the norm of the canonical Hilbert tensor.  This file
uses that tensor model to supply the algebraic operations, triangle inequality,
operator-norm domination, and completeness that
`SymmetricOperatorIdealFamily.Core` asks for.

The construction is rectangular and basis-free.  Its only scalar restriction
is complex scalars, inherited from the current Hilbert tensor implementation.
The real family is intended to be obtained by exact complexification transport.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open Filter
open TauCeti.HilbertSchmidt

noncomputable section

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Addition preserves the paper Hilbert--Schmidt class. -/
theorem approximationNumberEnergy_ne_top_add_complex
    {A B : E →L[ℂ] F}
    (hA : approximationNumberEnergy A ≠ ⊤)
    (hB : approximationNumberEnergy B ≠ ⊤) :
    approximationNumberEnergy (A + B) ≠ ⊤ := by
  let zA := hilbertSchmidtTensor A hA
  let zB := hilbertSchmidtTensor B hB
  have hrepr : ofLp (hSBasis _) (zA + zB) = A + B := by
    rw [ofLp_add]
    rw [toOperator_hilbertSchmidtTensor,
      toOperator_hilbertSchmidtTensor]
  rw [← hrepr]
  exact approximationNumberEnergy_ne_top_toOperator (zA + zB)

/-- The canonical tensor of a sum is the sum of the canonical tensors. -/
theorem hilbertSchmidtTensor_add
    {A B : E →L[ℂ] F}
    (hA : approximationNumberEnergy A ≠ ⊤)
    (hB : approximationNumberEnergy B ≠ ⊤) :
    hilbertSchmidtTensor (A + B)
        (approximationNumberEnergy_ne_top_add_complex hA hB) =
      hilbertSchmidtTensor A hA +
        hilbertSchmidtTensor B hB := by
  apply ofLp_injective (hSBasis _)
  rw [toOperator_hilbertSchmidtTensor,
    ofLp_add,
    toOperator_hilbertSchmidtTensor,
    toOperator_hilbertSchmidtTensor]

/-- The paper Hilbert--Schmidt norm satisfies the triangle inequality. -/
theorem hilbertSchmidtNorm_add_le_complex
    {A B : E →L[ℂ] F}
    (hA : approximationNumberEnergy A ≠ ⊤)
    (hB : approximationNumberEnergy B ≠ ⊤) :
    ContinuousLinearMap.hilbertSchmidtNorm (A + B) ≤
      ContinuousLinearMap.hilbertSchmidtNorm A + ContinuousLinearMap.hilbertSchmidtNorm B := by
  let hAB := approximationNumberEnergy_ne_top_add_complex hA hB
  rw [← norm_hilbertSchmidtTensor (A + B) hAB,
    hilbertSchmidtTensor_add hA hB,
    ← norm_hilbertSchmidtTensor A hA,
    ← norm_hilbertSchmidtTensor B hB]
  exact norm_add_le _ _

/-- A zero paper Hilbert--Schmidt norm forces the represented operator to
vanish. -/
theorem hilbertSchmidtNorm_eq_zero
    {A : E →L[ℂ] F} (hA : approximationNumberEnergy A ≠ ⊤)
    (hzero : ContinuousLinearMap.hilbertSchmidtNorm A = 0) : A = 0 := by
  let z := hilbertSchmidtTensor A hA
  have hzNorm : ‖z‖ = 0 := by
    rw [norm_hilbertSchmidtTensor]
    exact hzero
  have hz : hilbertSchmidtTensor A hA = 0 := norm_eq_zero.mp hzNorm
  have hrepr := toOperator_hilbertSchmidtTensor A hA
  rw [hz, ofLp_zero] at hrepr
  exact hrepr.symm

/-- Subtraction preserves the paper Hilbert--Schmidt class. -/
theorem approximationNumberEnergy_ne_top_sub
    {A B : E →L[ℂ] F}
    (hA : approximationNumberEnergy A ≠ ⊤)
    (hB : approximationNumberEnergy B ≠ ⊤) :
    approximationNumberEnergy (A - B) ≠ ⊤ := by
  rw [sub_eq_add_neg]
  exact approximationNumberEnergy_ne_top_add_complex hA ((approximationNumberEnergy_ne_top_neg_iff B).2 hB)

/-- The canonical tensor respects subtraction. -/
theorem hilbertSchmidtTensor_sub
    {A B : E →L[ℂ] F}
    (hA : approximationNumberEnergy A ≠ ⊤)
    (hB : approximationNumberEnergy B ≠ ⊤) :
    hilbertSchmidtTensor (A - B) (approximationNumberEnergy_ne_top_sub hA hB) =
      hilbertSchmidtTensor A hA -
        hilbertSchmidtTensor B hB := by
  apply ofLp_injective (hSBasis _)
  rw [toOperator_hilbertSchmidtTensor,
    ofLp_sub,
    toOperator_hilbertSchmidtTensor,
    toOperator_hilbertSchmidtTensor]

/-- A sequence Cauchy in the paper square norm converges to a paper
Hilbert--Schmidt operator in that norm. -/
theorem hilbertSchmidt_complete_complex
    (A : ℕ → E →L[ℂ] F)
    (hA : ∀ n, approximationNumberEnergy (A n) ≠ ⊤)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n,
      N ≤ m → N ≤ n →
        ContinuousLinearMap.hilbertSchmidtNorm (A m - A n) < ε) :
    ∃ L : E →L[ℂ] F, approximationNumberEnergy L ≠ ⊤ ∧
      ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
        ContinuousLinearMap.hilbertSchmidtNorm (A n - L) < ε := by
  let z : ℕ → lp (fun _ : HSIndex E => F) 2 :=
    fun n => hilbertSchmidtTensor (A n) (hA n)
  have hzCauchy : CauchySeq z := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hsub : approximationNumberEnergy (A m - A n) ≠ ⊤ :=
      approximationNumberEnergy_ne_top_sub (hA m) (hA n)
    have hcanon : hilbertSchmidtTensor (A m - A n) hsub = z m - z n := by
      apply ofLp_injective (hSBasis _)
      rw [toOperator_hilbertSchmidtTensor,
        ofLp_sub,
        toOperator_hilbertSchmidtTensor,
        toOperator_hilbertSchmidtTensor]
    have hnorm : ‖z m - z n‖ =
        ContinuousLinearMap.hilbertSchmidtNorm (A m - A n) := by
      rw [← hcanon, norm_hilbertSchmidtTensor]
    simpa only [dist_eq_norm, hnorm] using hN m n hm hn
  obtain ⟨zlim, hzlim⟩ := cauchySeq_tendsto_of_complete hzCauchy
  let L : E →L[ℂ] F := ofLp (hSBasis _) zlim
  have hL : approximationNumberEnergy L ≠ ⊤ :=
    approximationNumberEnergy_ne_top_toOperator zlim
  refine ⟨L, hL, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hzlim) ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hsub : approximationNumberEnergy (A n - L) ≠ ⊤ :=
    approximationNumberEnergy_ne_top_sub (hA n) hL
  have hcanon : hilbertSchmidtTensor (A n - L) hsub = z n - zlim := by
    apply ofLp_injective (hSBasis _)
    rw [toOperator_hilbertSchmidtTensor,
      ofLp_sub,
      toOperator_hilbertSchmidtTensor]
  have hnorm : ContinuousLinearMap.hilbertSchmidtNorm (A n - L) = ‖z n - zlim‖ := by
    rw [← norm_hilbertSchmidtTensor (A n - L) hsub, hcanon]
  rw [hnorm, ← dist_eq_norm]
  exact hN n hn

/-- The coherent complex rectangular Hilbert--Schmidt ideal family. -/
noncomputable def hilbertSchmidtComplex :
    SymmetricOperatorIdealFamily (𝕜 := ℂ) :=
  SymmetricOperatorIdealFamily.ofCore <| by
  classical
  refine
    { Mem := fun T => approximationNumberEnergy T ≠ ⊤
      gauge := fun T => ContinuousLinearMap.hilbertSchmidtNorm T
      zero_mem := by
        intro E F _ _ _ _ _ _
        rw [approximationNumberEnergy_zero]
        exact ENNReal.zero_ne_top
      add_mem := by
        intro E F _ _ _ _ _ _ A B hA hB
        exact approximationNumberEnergy_ne_top_add_complex hA hB
      smul_mem := by
        intro E F _ _ _ _ _ _ c A hA
        by_cases hc : c = 0
        · subst c
          simp
        · exact (approximationNumberEnergy_ne_top_smul_iff c hc A).2 hA
      adjoint_mem := by
        intro E F _ _ _ _ _ _ A hA
        exact (approximationNumberEnergy_ne_top_adjoint_iff A).2 hA
      comp_mem := by
        intro E F G H _ _ _ _ _ _ _ _ _ _ _ _ L A R hA
        exact approximationNumberEnergy_ne_top_comp hA L R
      gauge_nonneg := by
        intro E F _ _ _ _ _ _ A hA
        exact ContinuousLinearMap.hilbertSchmidtNorm_nonneg A
      gauge_zero := by
        intro E F _ _ _ _ _ _
        exact ContinuousLinearMap.hilbertSchmidtNorm_zero
      gauge_add_le := by
        intro E F _ _ _ _ _ _ A B hA hB
        exact hilbertSchmidtNorm_add_le_complex hA hB
      gauge_smul := by
        intro E F _ _ _ _ _ _ c A hA
        exact ContinuousLinearMap.hilbertSchmidtNorm_smul c A
      gauge_adjoint := by
        intro E F _ _ _ _ _ _ A hA
        exact ContinuousLinearMap.hilbertSchmidtNorm_adjoint A
      gauge_comp_le := by
        intro E F G H _ _ _ _ _ _ _ _ _ _ _ _ L A R hA
        exact ContinuousLinearMap.hilbertSchmidtNorm_comp_le L
          ((isHilbertSchmidt_iff_approximationNumberEnergy_ne_top A).2 hA) R
      opNorm_le_gauge := by
        intro E F _ _ _ _ _ _ A hA
        exact opNorm_le_hilbertSchmidtNorm hA
      gauge_complete := by
        intro E F _ _ _ _ _ _ A hA hcauchy
        exact hilbertSchmidt_complete_complex A hA hcauchy }

end

end ExactSinTheta
end DavisKahan
end TauCeti
