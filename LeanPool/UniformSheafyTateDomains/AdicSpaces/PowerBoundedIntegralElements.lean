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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AffinoidRings
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyFoundations

/-!
# The maximal plus ring of a Huber ring is a ring of integral elements

`IsSheafyComplete A` quantifies over `RingOfIntegralElements A`, which is a *subtype*
(`{B : Subring A // IsRingOfIntegralElements B}`). A universal statement over an empty
subtype is vacuously true, so sheafiness in that form says nothing at all unless some valid
`A⁺` is known to exist. This file supplies one for every Huber ring, once and for all: the
maximal plus ring `A°`.

Nothing here is new mathematics — both halves already existed. `A°` is open in any Huber
ring by `PairOfDefinition.isOpen_powerBoundedSubring` (Wedhorn 6.4(4)), which needs only a
pair of definition, and `IsHuberRing` always supplies one; and `A°` is integrally closed by
`TopologicalRing.isPowerBounded_of_isIntegral_of_subset_powerBounded` (Wedhorn 5.30(4)). The
existing `FiniteJet.isRingOfIntegralElements_powerBounded` proves the same thing but assumes
a *norm*, obtaining openness from a metric ball. That is fine for the four jet rings, which
are normed, and useless for the Tate extensions `A⟨V₁,…,Vₙ⟩`, whose topology is given by a
basis rather than a norm — which is exactly where non-vacuity had not been established.
-/

@[expose] public section

namespace ValuationSpectrum

/-- **The maximal plus ring of a Huber ring is a ring of integral elements.**

Hence `RingOfIntegralElements A` is inhabited for every Huber ring `A`, and
`IsSheafyComplete A` is a statement about genuine pairs rather than a vacuous
quantification. -/
theorem isRingOfIntegralElements_powerBoundedSubring
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsHuberRing A] :
    IsRingOfIntegralElements (TopologicalRing.powerBoundedSubring.toSubring A) := by
  obtain ⟨P⟩ := ‹IsHuberRing A›.exists_pairOfDefinition
  haveI : NonarchimedeanAddGroup A := P.nonarchimedeanAddGroup
  exact
    { isOpen := P.isOpen_powerBoundedSubring
      isIntegrallyClosed := fun _ ha =>
        TopologicalRing.isPowerBounded_of_isIntegral_of_subset_powerBounded (fun _ hx => hx) ha
      subset_powerBounded := fun _ hx => hx }

/-- The bundled form: every Huber ring has at least one ring of integral elements. -/
noncomputable def powerBoundedRingOfIntegralElements
    (A : Type*) [CommRing A] [TopologicalSpace A] [IsHuberRing A] :
    RingOfIntegralElements A :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring A, isRingOfIntegralElements_powerBoundedSubring⟩

instance {A : Type*} [CommRing A] [TopologicalSpace A] [IsHuberRing A] :
    Nonempty (RingOfIntegralElements A) :=
  ⟨powerBoundedRingOfIntegralElements A⟩

end ValuationSpectrum
