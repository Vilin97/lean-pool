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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicMorphismsCore
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructurePresheafBundled

/-!
# Provisional presentation-level morphism predicates (towards Wedhorn §8.4)

The carrier-presentation part of `AdicMorphisms.lean`, split off (WO1, 2026-07-20)
because it consumes `AdicSpacePresentation`/`AffinoidAdicPresentation` from
`StructurePresheafBundled.lean`. **Nothing here is a statement about actual adic
spaces (objects of Wedhorn's `𝒱`)**: `AdicSpacePresentation` is a bundled carrier
with presheaf data, `PresentationAffinoidNeighborhood` packages a chart
*homeomorphism* of carriers, and `PresentationIsAdicMorphism` is a provisional
carrier-level predicate (see its docstring — NOT Definition 8.38). Wedhorn
Definition 8.38 / Proposition 8.39 / Corollary 8.40 for genuine adic spaces await
the `𝒱`-layer; the affinoid (ring-level) content of Prop 8.39 is proved below.
Ring-level adicness (`IsAdicHom` etc.) stays in `AdicMorphisms.lean`.
-/

@[expose] public section

noncomputable section

namespace ValuationSpectrum

section AdicMorphismDef

universe u

open TopologicalSpace

/-- An open affinoid chart datum for a point of a *presentation*: an open set `U`,
a point membership proof, an affinoid adic presentation `aff`, and a
**homeomorphism of carriers** `U ≃ₜ Spa(aff.Ring)` — no structure-sheaf or
valuation compatibility is required, so this is strictly weaker than the affinoid
opens of Wedhorn Definition 8.38 (hence the `Presentation` prefix). -/
structure PresentationAffinoidNeighborhood (X : AdicSpacePresentation.{u}) (x : X.carrier) where
  /-- The open set containing `x`. -/
  U : Opens X.carrier
  /-- Proof that `x ∈ U`. -/
  mem : x ∈ U
  /-- The affinoid adic space that `U` is homeomorphic to. -/
  aff : AffinoidAdicPresentation.{u}
  /-- The homeomorphism `U ≃ₜ Spa(aff.Ring)`. -/
  homeo : ↥U ≃ₜ aff.toTopCat

/-- **PROVISIONAL carrier-level adicness predicate — this is NOT Wedhorn
Definition 8.38** (P0 honesty pass, 2026-07-20). Definition 8.38 is about a
morphism of *adic spaces* (objects of `𝒱`), and its ring homomorphism is the map
*induced on sections by that same `𝒱`-morphism*. This predicate lives on a bare
continuous map of carrier presentations and merely asks for *some* existential
adic ring homomorphism between chart rings, unrelated to `f` beyond the chart
containment — a strictly provisional stand-in until the genuine `𝒱`-layer
(canonical `Spa` objects of `𝒱`, restriction, Prop 8.6) exists. The public name
`IsAdicMorphism` is reserved for the eventual predicate on morphisms of actual
adic spaces and is deliberately **not** defined here. -/
def PresentationIsAdicMorphism (X Y : AdicSpacePresentation.{u}) (f : C(X.carrier, Y.carrier)) : Prop :=
  ∀ (x : X.carrier),
    ∃ (NX : PresentationAffinoidNeighborhood X x)
      (NY : PresentationAffinoidNeighborhood Y (f x))
      (_ : ∀ (p : ↥NX.U), f p.val ∈ NY.U)
      (_ : IsHuberRing NX.aff.Ring) (_ : IsHuberRing NY.aff.Ring)
      (φ : NY.aff.Ring →+* NX.aff.Ring),
      IsAdicHom φ

end AdicMorphismDef

section Prop839

/-- **Proposition 8.39(2) of Wedhorn (affinoid case).** Any continuous ring
homomorphism between Huber rings sends non-analytic points to non-analytic
points. This is the affinoid avatar of the statement that any morphism of
adic spaces preserves non-analytic points.

For the full adic space statement, one reduces to the affinoid case by
restricting to an affinoid chart and applying this result (Remark 8.37(2)).

The proof is `nonAnalytic_comap_of_continuous`, restated here for clarity. -/
theorem morphism_preserves_nonAnalytic_affinoid {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : ¬IsAnalytic v) : ¬IsAnalytic (comap φ v) :=
  nonAnalytic_comap_of_continuous hφ hv

/-- **Proposition 8.39(1) of Wedhorn (affinoid case, forward direction).**
An adic ring homomorphism `φ : A →+* B` between Huber rings induces a map
`Spa(φ)` that preserves analytic points.

This is `analytic_comap_of_isAdicHom` (Lemma 7.46(1)), restated in the
form needed for Proposition 8.39. -/
theorem isAdicHom_preserves_analytic {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [IsHuberRing A] [IsHuberRing B] {φ : A →+* B} (hφ : IsAdicHom φ) :
    ∀ (v : Spv B), IsAnalytic v → IsAnalytic (comap φ v) :=
  fun _ hv ↦ analytic_comap_of_isAdicHom hφ hv

/-- **Proposition 8.39(1) of Wedhorn (affinoid case, reverse direction).**
If `B` is complete and `Spa(φ)` preserves analytic points, then `φ` is adic.

This is `isAdicHom_of_complete_and_analytic_preserved` (Lemma 7.46(2)),
restated for the iff form.

**Status:** The reverse direction requires Lemma 7.45; see `Lemma745.lean`. -/
theorem isAdicHom_of_preserves_analytic_complete {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [IsHuberRing A] [IsHuberRing B] [PlusSubring A] [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ)
    (h_analytic : ∀ v ∈ Spa B B⁺, IsAnalytic v → IsAnalytic (comap φ v))
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) : IsAdicHom φ :=
  isAdicHom_of_complete_and_analytic_preserved hφ hAB h_analytic PB hBplus_le_B₀

/-- **Proposition 8.39(1) of Wedhorn (affinoid case, iff version).** A continuous
ring homomorphism `φ : A →+* B` between Huber rings (with `B` complete) is adic
if and only if the induced map `Spa(φ) : Spv B → Spv A` preserves analytic points
on `Spa(B, B⁺)`.

This combines the forward direction (`isAdicHom_preserves_analytic`, Lemma 7.46(1))
with the reverse direction (`isAdicHom_of_preserves_analytic_complete`, Lemma 7.46(2)).

The full adic space version (Proposition 8.39(1) of Wedhorn) states that a morphism
`f : X → Y` of adic spaces is adic iff `f` maps analytic points of `X` to analytic
points of `Y`. The reduction from the adic space level to the affinoid level uses
Remark 8.37(2) of Wedhorn: it suffices to check the adic property on affinoid charts.
Formalizing that reduction requires connecting the provisional `PresentationIsAdicMorphism`
(which asks for *some* witnessing affinoid charts) to the pointwise analytic-preservation
property, which is not yet available.

**Status:** Sorry; the forward direction is proved, but the reverse direction
inherits sorries from `isAdicHom_of_complete_and_analytic_preserved` (Lemma 7.46(2)):
1. `exists_pairOfDefinition_le_subring` (Lemma 6.5) -- `IsAdic` property.
2. `exists_nonOpen_prime_of_B_from_B₀_prime` -- prime extension disjointness. -/
theorem isAdicHom_iff_preserves_analytic {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [IsHuberRing A] [IsHuberRing B] [PlusSubring A] [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ)
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) : IsAdicHom φ ↔
    (∀ v ∈ Spa B B⁺, IsAnalytic v → IsAnalytic (comap φ v)) := by
  constructor
  · intro hadic v _ hv
    exact analytic_comap_of_isAdicHom hadic hv
  · exact fun h ↦
      isAdicHom_of_complete_and_analytic_preserved hφ hAB h PB hBplus_le_B₀

end Prop839

-- `ringHom_isAdic_of_charts_analytic_preserved` (a chart-decorated alias of the
-- ring-level Lemma 7.46(2) `isAdicHom_of_complete_and_analytic_preserved`, with
-- unused chart arguments) was DELETED in the 2026-07-20 fidelity pass: it had no
-- consumers, and Corollary 8.40 proper is about morphisms of actual adic spaces
-- and awaits the `𝒱`-layer.

end ValuationSpectrum
