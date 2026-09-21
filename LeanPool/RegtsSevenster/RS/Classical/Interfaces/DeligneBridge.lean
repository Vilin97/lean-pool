/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DelignePackage
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.FibreTransport
import LeanPool.RegtsSevenster.RS.Novel.Extraction.SnakeTransport

/-!
# The Deligne bridge

Connecting the fibre-functor interface to the extraction: a
braided monoidal functor into SuperVect carries a self-dual
object with a supersymmetric form to a standard orthosymplectic
model.  The pairing transports by `ExactPairing.map`, the
supersymmetry by the braided-functor axiom, and
`exists_std_model` produces the coordinates.
-/

noncomputable section

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {A : Type*}

/-- Supersymmetry transports along a braided functor into
SuperVect: the transported form absorbs the Koszul braiding. -/
theorem braided_transported_supersymmetry
    [Category A] [MonoidalCategory A] [SymmetricCategory A]
    (ω : A ⥤ SuperVect)
    [ω.Braided] (X : A) [ExactPairing X X]
    (hsym : (β_ X X).hom ≫ ε_ X X = ε_ X X) :
    SuperVect.Hom.comp (μ ω X X ≫ ω.map (ε_ X X) ≫ η ω)
        (SuperVect.koszulBraiding (ω.obj X) (ω.obj X)) =
      (μ ω X X ≫ ω.map (ε_ X X) ≫ η ω) := by
  show (β_ (ω.obj X) (ω.obj X)).hom ≫
    (μ ω X X ≫ ω.map (ε_ X X) ≫ η ω) = _
  rw [← Category.assoc, ← Functor.Braided.braided,
    Category.assoc, ← Functor.map_comp_assoc, hsym]

/-- **The Deligne bridge**: a braided monoidal functor into
SuperVect carries a self-dual object with a supersymmetric form
to a standard orthosymplectic model — the transported form
becomes the standard form and the transported copairing the
standard copairing. -/
theorem braided_std_model
    [Category A] [MonoidalCategory A] [SymmetricCategory A]
    (ω : A ⥤ SuperVect) [ω.Braided]
    (X : A) [ExactPairing X X]
    (hsym : (β_ X X).hom ≫ ε_ X X = ε_ X X) :
    ∃ (k ℓ : ℕ) (e : SuperVect.Hom (stdSuperPair k ℓ) (ω.obj X))
      (e' : SuperVect.Hom (ω.obj X) (stdSuperPair k ℓ)),
      SuperVect.Hom.comp e' e =
        SuperVect.Hom.id (stdSuperPair k ℓ) ∧
      SuperVect.Hom.comp e e' = SuperVect.Hom.id (ω.obj X) ∧
      SuperVect.Hom.comp (μ ω X X ≫ ω.map (ε_ X X) ≫ η ω)
        (SuperVect.tensorHom e e) = stdForm k ℓ ∧
      SuperVect.Hom.comp (SuperVect.tensorHom e' e')
        (ε ω ≫ ω.map (η_ X X) ≫ δ ω X X) = stdCopair k ℓ := by
  letI EP : ExactPairing (ω.obj X) (ω.obj X) :=
    ExactPairing.map ω (X := X) (Y := X)
  exact exists_std_model
    (μ ω X X ≫ ω.map (ε_ X X) ≫ η ω)
    (ε ω ≫ ω.map (η_ X X) ≫ δ ω X X)
    (braided_transported_supersymmetry ω X hsym)
    EP.coevaluation_evaluation'
    EP.evaluation_coevaluation'

end RS
