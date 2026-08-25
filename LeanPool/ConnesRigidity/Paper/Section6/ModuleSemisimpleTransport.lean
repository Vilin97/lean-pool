/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Paper.Section6.ModuleSemisimple
import LeanPool.ConnesRigidity.Paper.Section6.NonisomorphismTransport

/-!
Transport the concrete first-module semisimplicity proof into the paper-facing
predicate and expose the resulting Section 6 nonisomorphism theorem.
-/

namespace Connes
namespace PaperModuleSemisimpleTransport

open Construction
open Construction.PaperKernel
open PaperNonisomorphism
open PaperModuleSemisimple

noncomputable section

/--
The `Q` construction used in the Connes rigidity formalization.
-/
abbrev Q := PaperKernel.Q
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D

/- The concrete first action is the product representation proved semisimple above. Paper: §6.
-/
/--
The `paperFirstProductRepresentation` construction used in the Connes rigidity formalization.
-/
def paperFirstProductRepresentation : Representation k Q D :=
  PaperModuleSemisimple.firstProductRepresentation

/- The paper-facing first action agrees with the decomposed representation. Paper: §6. -/
theorem paper_qRepresentationOne_eq_firstProduct :
    qRepresentationOne =
      paperFirstProductRepresentation := by
  apply MonoidHom.ext
  intro q
  apply LinearMap.ext
  intro d
  rcases d with ⟨u, c⟩
  apply Prod.ext
  · rfl
  · have hm := PaperKernel.sl3CActionHom.map_one
    change PaperKernel.sl3CActionEquiv (1 : SpecialLinear.SL3) =
      LinearEquiv.refl k PaperKernel.C at hm
    exact congrArg (fun e : PaperKernel.C ≃ₗ[k] PaperKernel.C => e c) hm

/- The actual first quotient module is semisimple, closing its §6 input. Paper: §6. -/
theorem paper_moduleOne_semisimple :
    moduleOneSemisimple := by
  change IsSemisimpleModule Ring
    (qRepresentationOne).asModule
  rw [paper_qRepresentationOne_eq_firstProduct]
  exact PaperModuleSemisimple.firstProduct_semisimple

/-- The two concrete paper groups are nonisomorphic. This is the public §6 endpoint. -/
theorem paperGroups_not_isomorphic :
    ¬ Nonempty
      (PaperKernel.paperGammaOne ≃* PaperKernel.paperGammaTwo) :=
  PaperNonisomorphism.paperNotIsomorphic paper_moduleOne_semisimple

end
end PaperModuleSemisimpleTransport
end Connes
