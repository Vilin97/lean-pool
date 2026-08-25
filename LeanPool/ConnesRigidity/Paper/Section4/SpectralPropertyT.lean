/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

The action-indexed positive scalar spectral bridge for Zhou §4. The analytic
spectral measures are constructed by joint functional calculus, so the only
paper-specific input is finite spectral detection. Paper: §4.
-/
import LeanPool.ConnesRigidity.Paper.Section4.PropertyT
import LeanPool.ConnesRigidity.Paper.Section4.SplitExtensions
import LeanPool.ConnesRigidity.Paper.Section4.FiniteExtensions
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.PositiveSpectralMeasure
import LeanPool.ConnesRigidity.Paper.Section3.DualHaar

/-!
The spectral property t component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperSpectralPropertyT

open Construction
open Construction.PaperKernel
open PaperPropertyT

noncomputable section

universe v

/-- Borel structure on the raw compact character carrier used by §4. Paper: §4. -/
noncomputable instance paperRawCharacterMeasurableSpace :
    MeasurableSpace (DiscreteCharacterSpace PaperKernel.D) :=
  borel (DiscreteCharacterSpace PaperKernel.D)

/-- The raw compact character carrier is a Borel space. Paper: §4. -/
instance paperRawCharacterBorelSpace :
    BorelSpace (DiscreteCharacterSpace PaperKernel.D) := ⟨rfl⟩

/-- Singletons are measurable in the paper's compact character space. Paper: §4. -/
instance paperRawCharacterMeasurableSingletonClass :
    MeasurableSingletonClass (DiscreteCharacterSpace PaperKernel.D) := by
  infer_instance

/-- The first actual split extension used by the spectral argument. Paper: §4. -/
noncomputable abbrev lambdaOneExtension :
    SplitAbelianExtension PaperKernel.D lambdaOne SpecialLinear.sl3Group :=
  PaperSplitExtensions.lambdaExtension PaperKernel.paperThetaOneHom

/-- The second actual split extension used by the spectral argument. Paper: §4. -/
noncomputable abbrev lambdaTwoExtension :
    SplitAbelianExtension PaperKernel.D
      lambdaTwo SpecialLinear.sl3Group :=
  PaperSplitExtensions.lambdaExtension PaperKernel.paperThetaTwoHom

/-- Spectral data for the intermediate group associated to an action. Paper: §4. -/
structure SpectralData
    (action : H →* MulAut (Multiplicative PaperKernel.D)) where
  /--
  The `J` component of `SpectralData`.
  -/
  J : Finset PaperKernel.D
  /--
  The `c` component of `SpectralData`.
  -/
  c : ℝ
  c_pos : 0 < c
  detection : HasFiniteSpectralDetection
    (PaperSplitExtensions.lambdaExtension action) J c

/-- The intermediate group of an action is property-(T) from spectral data. Paper: §4. -/
theorem lambda_propertyT_of_spectralData
    (input : EJZKInput.{v})
    (action : H →* MulAut (Multiplicative PaperKernel.D))
    (data : SpectralData action) :
    HasKazhdanPropertyT.{0, v} (lambdaOf action) := by
  exact spectral_criterion_unconditional
    (PaperSplitExtensions.lambdaExtension action) (sl3_propertyT_from_EJZK input)
      data.J data.c_pos data.detection

/-- The full semidirect group of an action is property-(T) from spectral data. Paper: §4. -/
theorem gamma_propertyT_of_spectralData
    (input : EJZKInput.{v})
    (action : H →* MulAut (Multiplicative PaperKernel.D))
    (data : SpectralData action) :
    HasKazhdanPropertyT.{0, v} (PaperKernel.paperGammaOf action) := by
  exact PropertyTTransfer.hasKazhdanPropertyT_of_finiteExtension
    (PaperFiniteExtensions.finiteExtension action)
    (lambda_propertyT_of_spectralData input action data)
    PaperPropertyT.finiteSymplecticGroup_propertyT

/-- Both concrete Zhou groups have property-(T) from the two spectral inputs. Paper: §4. -/
theorem completion_of_spectralData
    (input : EJZKInput.{v})
    (dataOne : SpectralData PaperKernel.paperThetaOneHom)
    (dataTwo : SpectralData PaperKernel.paperThetaTwoHom) :
    HasKazhdanPropertyT.{0, v} PaperKernel.paperGammaOne ∧
      HasKazhdanPropertyT.{0, v} PaperKernel.paperGammaTwo := by
  exact ⟨
    gamma_propertyT_of_spectralData input
      PaperKernel.paperThetaOneHom dataOne,
    gamma_propertyT_of_spectralData input
      PaperKernel.paperThetaTwoHom dataTwo⟩

end
end PaperSpectralPropertyT
end Connes
