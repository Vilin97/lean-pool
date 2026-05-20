/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Graph.Orientation
import LeanPool.BruhatTits.Graph.Regular
import LeanPool.BruhatTits.Harmonic.Basic

open Module

/-!
# Surjectivity of the Bruhat-Tits Laplacian

In this file we show that the Laplacian of the Bruhat-Tits tree is surjective.

-/

open IsLocalRing

suppress_compilation

namespace BruhatTits

-- Let R be a discrete valuation ring and K its field of fractions
variable {K : Type*} [Field K]
variable (R : Subring K) [IsDiscreteValuationRing R] [IsFractionRing R K]
variable [Finite (ResidueField R)]

open Classical in
/-- The Laplacian on the Bruhat-Tits tree with coefficients in any `A`-module `M`. -/
def BTlaplace (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M] :
    ((BTgraph (R := R)).edgeSet → M) →ₗ[A] (Vertices R → M) :=
  (BTgraph (R := R)).laplaceLinearMap (BTweight A)

variable (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]

open Classical in
lemma BTlaplace_surjective : Function.Surjective (BTlaplace R A M) :=
  SimpleGraph.laplace_surjective BTtree (BTweight A) <| fun v ↦ by
    simp only [btgraph_degree, Nat.reduceLeDiff]
    apply Finite.card_pos

end BruhatTits
