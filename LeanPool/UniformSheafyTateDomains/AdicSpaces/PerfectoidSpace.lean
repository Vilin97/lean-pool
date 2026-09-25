/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PerfectoidRing
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructurePresheafBundled

/-!
# Perfectoid space *presentations*

Carrier-level **presentation** objects for perfectoid geometry. **Nothing in this
file is an actual object of Wedhorn's category `𝒱`**: `AdicSpacePresentation` /
`AffinoidAdicPresentation` are bundled carriers with presheaf data, and the
perfectoid predicate below asks only for chart *homeomorphisms* of carriers —
Scholze's Definition 3.19 (isomorphisms of adic spaces, with structure sheaves
and valuations) awaits the genuine `𝒱`-layer.

## Main definitions

* `AffinoidPerfectoidSpace p` : A bundled perfectoid ring with all instances needed to form
  `Spa(A, A⁺)`.
* `IsPerfectoidSpacePresentation p X` : the PROVISIONAL carrier-level perfectoid
  predicate on a presentation (see its docstring; NOT Scholze Definition 3.19).

## Main results (sorry'd, producer WIP)

* `AffinoidPerfectoidSpace.toAffinoidAdicPresentation` : Every affinoid perfectoid space gives
  an affinoid adic *presentation* (requires sheafiness of perfectoid rings).
* `AffinoidPerfectoidSpace.toAdicSpacePresentation` : Every affinoid perfectoid space gives
  an adic space *presentation*.

## References

* [P. Scholze, *Perfectoid Spaces*][scholze2012perfectoid], Definition 3.19
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8
-/

@[expose] public section

open TopologicalRing ValuationSpectrum

universe u

/-! ### Affinoid perfectoid spaces -/

/-- An **affinoid perfectoid space** is `Spa(A, A⁺)` for a perfectoid ring `A`
(Scholze, *Perfectoid Spaces*, Definition 3.19).

This structure bundles a perfectoid ring together with all the typeclass instances
needed to form its adic spectrum and structure sheaf. -/
structure AffinoidPerfectoidSpace (p : ℕ) [Fact (Nat.Prime p)] where
  /-- The underlying ring. -/
  Ring : Type u
  [instCommRing : CommRing Ring]
  [instTopologicalSpace : TopologicalSpace Ring]
  [instIsTopologicalRing : IsTopologicalRing Ring]
  [instUniformSpace : UniformSpace Ring]
  [instIsLinearTopology : IsLinearTopology Ring Ring]
  [instPlusSubring : PlusSubring Ring]
  [instPerfectoidRing : IsPerfectoidRing p Ring]

attribute [instance] AffinoidPerfectoidSpace.instCommRing
  AffinoidPerfectoidSpace.instTopologicalSpace
  AffinoidPerfectoidSpace.instIsTopologicalRing
  AffinoidPerfectoidSpace.instUniformSpace
  AffinoidPerfectoidSpace.instIsLinearTopology
  AffinoidPerfectoidSpace.instPlusSubring
  AffinoidPerfectoidSpace.instPerfectoidRing

namespace AffinoidPerfectoidSpace

variable {p : ℕ} [Fact (Nat.Prime p)] (X : AffinoidPerfectoidSpace.{u} p)

/-- The underlying topological space of an affinoid perfectoid space. -/
def toTopCat : TopCat.{u} := SpaTop X.Ring

/-- Every affinoid perfectoid space is an affinoid adic space.

This requires that perfectoid rings are sheafy (Scholze, Theorem 6.3), which
follows from the deep result that perfectoid rings are stably uniform. The
proof goes through almost mathematics and tilting. -/
noncomputable def toAffinoidAdicPresentation : AffinoidAdicPresentation.{u} := by
  exact sorry

/-- Every affinoid perfectoid space gives rise to an adic space *presentation*.

This combines `toAffinoidAdicPresentation` with the fact that every affinoid adic
presentation is trivially an adic space presentation (covered by itself). -/
noncomputable def toAdicSpacePresentation : AdicSpacePresentation.{u} := by
  exact sorry

end AffinoidPerfectoidSpace

/-! ### Perfectoid spaces -/

/-- **PROVISIONAL carrier-level perfectoid predicate — NOT Scholze's Definition 3.19**
(P0 honesty pass, 2026-07-20): every point of the *presentation* has an open
neighborhood *homeomorphic* to the spectrum of a perfectoid ring. Scholze's actual
definition of a perfectoid space requires the local identifications to be
isomorphisms of adic spaces (carrying structure sheaves and valuations), not bare
homeomorphisms of carriers; that awaits the genuine `𝒱`-layer. -/
class IsPerfectoidSpacePresentation (p : ℕ) [Fact (Nat.Prime p)]
    (X : AdicSpacePresentation.{u}) : Prop where
  /-- Every point has an open neighborhood isomorphic to the adic spectrum of a
  perfectoid ring. -/
  locally_perfectoid : ∀ x : X.carrier,
    ∃ (U : TopologicalSpace.Opens X.carrier),
      x ∈ U ∧
      ∃ (S : AffinoidPerfectoidSpace.{u} p),
        Nonempty (↥U ≃ₜ S.toTopCat)

/-! ### Tilting (space level): NOT formalized here

The space-level tilting equivalence (Scholze, *Perfectoid Spaces*, Theorem 6.3 —
the tilt `X♭` of a perfectoid space, with its chart-wise gluing) is **not**
formalized in this file. A previous statement named `PerfectoidSpace.tilt` was
removed (2026-07-20): it asserted only `∃ Y, IsPerfectoidSpacePresentation p Y`,
which does not mention the tilt of `X` at all and so did not formalize tilting.
The genuine ring-level tilt `A♭` lives in `Tilting.lean`
(`PerfectoidRing.tilt`); the space level awaits the genuine `𝒱`-layer. -/
