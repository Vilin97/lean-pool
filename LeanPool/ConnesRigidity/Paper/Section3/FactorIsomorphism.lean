/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-
-/
import LeanPool.ConnesRigidity.Construction.PaperActionInstances

/-!
Algebraic part of Zhou §3 for the concrete tensor kernel, including the
quadratic fiber shear and its characteristic-two involutivity.
-/

namespace Connes
namespace PaperFactorIsomorphism

open MeasureTheory

noncomputable section

/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A
/--
The `PaperV` construction used in the Connes rigidity formalization.
-/
abbrev PaperV := Construction.PaperKernel.PaperV
/--
The `SymplecticIndex` construction used in the Connes rigidity formalization.
-/
abbrev SymplecticIndex := OpenAIPort.SymplecticIndex
/--
The `C` construction used in the Connes rigidity formalization.
-/
abbrev C := Construction.PaperKernel.C
/--
The `TensorAA` construction used in the Connes rigidity formalization.
-/
abbrev TensorAA := Construction.PaperKernel.TensorAA
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H

/-- The algebraic dual coordinates used by Zhou's fiber model. Paper: §3. -/
abbrev DualCoordinates :=
  (A →ₗ[k] PaperV) × (C →ₗ[k] k)

/-- One finite coordinate of a map `A → V`. Paper: §3. -/
def coordinate (z : A →ₗ[k] PaperV) (i : SymplecticIndex) : A →ₗ[k] k where
  toFun a := z a i
  map_add' a b := by simp
  map_smul' r a := by simp

/-- Bilinear evaluation on a pure tensor. Paper: §3. -/
def tensorFunctional (f g : A →ₗ[k] k) : TensorAA →ₗ[k] k :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => f a * g b
          map_add' := by
            intro b c
            simp [mul_add]
          map_smul' := by
            intro r b
            simp [smul_eq_mul]
            ring }
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        simp [add_mul]
      map_smul' := by
        intro r a
        apply LinearMap.ext
        intro b
        simp [smul_eq_mul, mul_assoc] }

/-- Restriction of tensor evaluation to the flip-fixed carrier. Paper: §3. -/
def tensorFunctionalOnC (f g : A →ₗ[k] k) : C →ₗ[k] k :=
  (tensorFunctional f g).domRestrict C

@[simp] theorem tensorFunctionalOnC_diagonal
    (f g : A →ₗ[k] k) (a : A) :
    tensorFunctionalOnC f g (Construction.PaperKernel.diagonal a) =
      f a * g a := by
  simp [tensorFunctionalOnC, tensorFunctional,
    Construction.PaperKernel.diagonal]

/-- Zhou's quadratic functional on the symmetric tensor dual. Paper: §3. -/
def quadraticMap (z : A →ₗ[k] PaperV) : C →ₗ[k] k :=
  tensorFunctionalOnC (coordinate z (Sum.inl 0)) (coordinate z (Sum.inr 0)) +
    tensorFunctionalOnC (coordinate z (Sum.inl 1)) (coordinate z (Sum.inr 1))

@[simp] theorem quadraticMap_diagonal (z : A →ₗ[k] PaperV) (a : A) :
    quadraticMap z (Construction.PaperKernel.diagonal a) =
      OpenAIPort.standardQuadraticForm (z a) := by
  simp [quadraticMap, coordinate, OpenAIPort.standardQuadraticForm]

/-- The nontrivial fiber shear from Zhou Proposition 3.2. Paper: §3. -/
def fiberShear : DualCoordinates → DualCoordinates := fun p =>
  (p.1, p.2 + quadraticMap p.1)

/-- The characteristic-two cancellation behind the fiber shear. Paper: §3. -/
theorem fiberShear_involutive (p : DualCoordinates) :
    fiberShear (fiberShear p) = p := by
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro c
    change (p.2 c + quadraticMap p.1 c) + quadraticMap p.1 c = p.2 c
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

end
end PaperFactorIsomorphism
end Connes
