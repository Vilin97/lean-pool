/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-
-/
import LeanPool.ConnesRigidity.Paper.Section4.SpectralPropertyT
import LeanPool.ConnesRigidity.Paper.Section4.SpectralFiniteDetection
import LeanPool.ConnesRigidity.Paper.Section3.FactorClosure
import LeanPool.ConnesRigidity.Paper.Section5.ICCOrbits
import LeanPool.ConnesRigidity.Paper.Section6.ModuleSemisimpleTransport

/-!
Concrete completion boundary for Zhou's Theorem A. Paper: §§3--7.
-/

namespace Connes
namespace PaperTheoremACompletion

open Construction
open Construction.PaperKernel

noncomputable section

/-- The concrete headline follows from the cited EJZK property-(T) input.
All remaining spectral, factor, ICC, and nonisomorphism certificates are
constructed internally. Paper: §§7. -/
theorem theoremA (propertyTInput : PaperPropertyT.EJZKInput) :
    ∃ Γ₁ Γ₂ : CountableDiscreteGroup.{0},
      HasKazhdanPropertyT Γ₁ ∧ HasKazhdanPropertyT Γ₂ ∧
      IsICC Γ₁ ∧ IsICC Γ₂ ∧
      TracialGroupFactorsIsomorphic Γ₁ Γ₂ ∧
      ¬ Nonempty (Γ₁ ≃* Γ₂) := by
  have hT := PaperSpectralPropertyT.completion_of_spectralData
    propertyTInput PaperSpectralFiniteDetection.lambdaOneSpectralData
      PaperSpectralFiniteDetection.lambdaTwoSpectralData
  have hFactor := PaperFactorClosure.paperGroupFactors_isomorphic
  have hNoniso := PaperModuleSemisimpleTransport.paperGroups_not_isomorphic
  exact ⟨PaperKernel.paperGammaOne, PaperKernel.paperGammaTwo,
    hT.1, hT.2, PaperICC.paper_gammaOne_icc,
    PaperICC.paper_gammaTwo_icc, hFactor, hNoniso⟩

end
end PaperTheoremACompletion
end Connes
