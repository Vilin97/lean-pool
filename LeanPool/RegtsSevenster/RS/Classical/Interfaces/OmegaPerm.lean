/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DelignePackage
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.FibreTransport
import LeanPool.RegtsSevenster.RS.Novel.Envelope.SkeinTower
import LeanPool.RegtsSevenster.RS.Novel.Skein.ExactPairingInstance

/-!
# Omega-equivariance of the symmetric-group action

The braiding-generated symmetric-group action on the skein
endomorphism algebra `skeinEnd f n` transports along the Deligne
package's fibre functor `ω` to a well-defined algebra homomorphism
`SymGroupAlgebra n →ₐ[ℂ] End (ω.obj (SkeinObj.mk n))`.

## Main results

* `omegaPermHom` -- the monoid homomorphism
  `Perm (Fin n) →* End (ω.obj (SkeinObj.mk n))` obtained by
  composing the permutation-to-endomorphism map with the functorial
  action on endomorphisms.
* `omegaSkeinRep` -- the algebra homomorphism
  `SymGroupAlgebra n →ₐ[ℂ] End (ω.obj (SkeinObj.mk n))` lifted
  from `omegaPermHom` via the universal property of the group
  algebra.
* `omegaSkeinRep_of` -- on a single permutation `σ`, the
  representation yields `ω.map (permClass f n σ)`.
* `omegaSkeinRep_eq` -- the transported representation agrees with
  applying `ω.map` to the skein representation:
  `omegaSkeinRep f P n x = ω.map (skeinRep f n x)`.

## Formulation

The skein category's symmetric-group action is the algebra
homomorphism `skeinRep f n : SymGroupAlgebra n →ₐ[ℂ] skeinEnd f n`
built from `σ ↦ [permFragment σ]` (see `RS.Novel.Envelope.SkeinTower`).
The fibre functor `ω` from a Deligne package induces a ring
homomorphism on endomorphisms via functoriality.  The composite
`ω.map ∘ skeinRep f n` is therefore an algebra homomorphism from
the symmetric-group algebra to `End (ω.obj (SkeinObj.mk n))`, and
agreeing on the generators `σ` makes it that composite.
-/

noncomputable section

namespace RS

open CategoryTheory MonoidalCategory Category
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
  (P : DelignePackage (SkeinObj f))

/-! ### The transported permutation representation -/

/-- The monoid homomorphism sending a permutation `σ : Perm (Fin n)`
to the endomorphism `ω.map (permClass f n σ)` of the image object.
This is the composition of the skein permutation-to-endomorphism
map `permToEnd f n` with the functorial action `ω.mapEnd`. -/
noncomputable def omegaPermHom (n : ℕ) :
    Equiv.Perm (Fin n) →* End (P.ω.obj (SkeinObj.mk n)) :=
  (P.ω.mapEnd (SkeinObj.mk n)).comp (permToEnd f n)

/-- The transported symmetric-group representation: the algebra
homomorphism `SymGroupAlgebra n →ₐ[ℂ] End (ω.obj (SkeinObj.mk n))`
obtained by lifting `omegaPermHom` through the universal property
of the group algebra. -/
noncomputable def omegaSkeinRep (n : ℕ) :
    SymGroupAlgebra n →ₐ[ℂ] End (P.ω.obj (SkeinObj.mk n)) :=
  MonoidAlgebra.lift ℂ (End (P.ω.obj (SkeinObj.mk n)))
    (Equiv.Perm (Fin n)) (omegaPermHom f P n)

/-- On a single permutation, the transported representation yields
`ω.map (permClass f n σ)`. -/
theorem omegaSkeinRep_of (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    omegaSkeinRep f P n (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ) =
      P.ω.map (permClass f n σ) :=
  MonoidAlgebra.lift_of (omegaPermHom f P n) σ

/-- **Equivariance**: the transported representation agrees with
applying `ω.map` to the skein representation element by element.
Both sides are algebra homs agreeing on generators, hence equal
on all elements by the universal property. -/
theorem omegaSkeinRep_eq (n : ℕ) (x : SymGroupAlgebra n) :
    omegaSkeinRep f P n x = P.ω.map (skeinRep f n x) := by
  let := P.additive
  let := P.linear
  -- Both sides are equal on generators and respect the algebra
  -- operations.  We proceed by induction on the group algebra
  -- element.
  apply MonoidAlgebra.induction_on x
  · -- Generator case: both sides give ω.map (permClass f n σ)
    intro σ
    rw [omegaSkeinRep_of, skeinRep_of]
  · -- Addition case
    intro a b ha hb
    simp only [map_add, ha, hb]
    exact (Functor.map_add (F := P.ω)
      (f := skeinRep f n a) (g := skeinRep f n b)).symm
  · -- Scalar multiplication case
    intro c a ha
    simp only [map_smul, ha]
    exact (Functor.map_smul (F := P.ω)
      (r := c) (f := skeinRep f n a)).symm

end RS

end
