/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalResidueExtensionSymbolControlAdapter
public import LeanPool.Stafford38.Stafford38.Characteristic.RadicalMinimalPrimeInvolutivity


/-!
# Lane B: the residue-extension input reduced to the cited Gabber theorem

The adapter
`Stafford38.Characteristic.CanonicalResidueExtensionSymbolControlAdapter`
already reduces `CanonicalResidueExtensionSymbolControl` to
`CanonicalMinimalPrimeInvolutivityOverFields`: involutivity of every minimal
prime of the order initial ideal of the *canonical* quotient, over an
arbitrary characteristic-zero field, with no scalar extension, algebraic
closure, or Laurent series in the statement.  Two gaps remained between that
proposition and the literature theorem it is supposed to instantiate.

* Gabber's theorem is about the radical `√Ann_S gr M`, not about the
  individual minimal primes of `Ann_S gr M`.
* Gabber's theorem is about an arbitrary finitely generated filtered module,
  so neither `0 < N` nor `IsPBWMonicAt` plays any role in it; the canonical
  right ideal `dA + x₀^N dA` is one instance among all right ideals.

This file closes both.  `WeylAssociatedGradedRadicalInvolutivity` is the
citation itself, stated for the repository's actual associated graded object:
for every characteristic-zero field `L`, every `A_m(L)`, and every right ideal
`I`, the radical of `Ann_{S} gr(A/I)` is involutive.  It is *intended* to
transcribe the algebraic form of Gabber's theorem proved for
almost-commutative `ℚ`-algebras with Noetherian associated graded
(Singh--Kumar, *On the Involutivity of the Characteristic Variety*,
Comm. Algebra 42 (2014), no. 8, 3607-3618, Theorem 5.1 with Theorems 4.1 and
4.2).
Two things make that transcription plausible: `A/I` is cyclic, so its
order-quotient filtration is good; and the right-module convention costs
nothing, because `A/I` is a left `Aᵒᵖ`-module, `gr(Aᵒᵖ) ≅ (gr A)ᵒᵖ = S` since
`S` is commutative, and the induced bracket only changes sign.

That this Lean proposition really says what the cited theorem says is a human
review obligation recorded in `docs/literature-assumptions.yaml`, not
something this file establishes.  In particular it rests on the repository's
own identification of `OrderAssociatedGradedModule` with `gr(A/I)` for the
differential-order filtration.

The chain proved here is
`WeylAssociatedGradedRadicalInvolutivity →`
`WeylOrderInitialRadicalInvolutivity →`
`RightWeylMinimalPrimeInvolutivity →`
`CanonicalMinimalPrimeInvolutivityOverFields →`
`CanonicalBaseRelativePoissonOverFields →`
`CanonicalResidueExtensionSymbolControl`,
every step trust-zero.  No Gabber-type statement is proved here; the first
proposition is a theorem-shaped interface a caller must still supply.
-/

@[expose] public section

namespace Stafford38.Characteristic.CanonicalGabberInvolutivityInterface

open Stafford38
open Stafford38.CanonicalSupportVanishingReduction
open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalResidueExtensionSymbolControlAdapter
open Stafford38.Characteristic.PostScalarExtensionPoisson
open Stafford38.Characteristic.RadicalMinimalPrimeInvolutivity
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.Geometry.CanonicalResidueExtensionAssembly
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

universe u

/-- **The cited Gabber theorem, stated on the repository's own associated
graded module.**  For every characteristic-zero field `L`, every Weyl algebra
`A_m(L)` with its differential-order filtration, and every right ideal `I`,
the radical of the annihilator of `gr(A/I)` is involutive.

`A/I` is cyclic, so its quotient filtration is good; this is therefore the
statement of Gabber involutivity, not a project-specific strengthening of it.
It is a theorem-shaped interface: no proof is asserted here. -/
def WeylAssociatedGradedRadicalInvolutivity : Prop :=
  ∀ (L : Type u) [Field L] [CharZero L] (m : ℕ)
    (I : RightIdeal (PresentedWeyl L m)),
    IsInvolutive
      (Module.annihilator (SymbolRing L m)
        (OrderAssociatedGradedModule L I)).radical

/-- The same statement written through the order initial ideal, which the
repository proves is exactly that annihilator. -/
def WeylOrderInitialRadicalInvolutivity : Prop :=
  ∀ (L : Type u) [Field L] [CharZero L] (m : ℕ)
    (I : RightIdeal (PresentedWeyl L m)),
    IsInvolutive (orderInitialIdeal L I).radical

/-- Involutivity of every minimal prime of the order initial ideal, for an
arbitrary right ideal of an arbitrary Weyl algebra over an arbitrary
characteristic-zero field. -/
def RightWeylMinimalPrimeInvolutivity : Prop :=
  ∀ (L : Type u) [Field L] [CharZero L] (m : ℕ)
    (I : RightIdeal (PresentedWeyl L m)),
    ∀ P ∈ (orderInitialIdeal L I).minimalPrimes, IsInvolutive P

/-- The annihilator form and the initial-ideal form of the citation are the
same proposition. -/
theorem weylOrderInitialRadicalInvolutivity_iff_associatedGraded :
    WeylOrderInitialRadicalInvolutivity.{u} ↔
      WeylAssociatedGradedRadicalInvolutivity.{u} := by
  constructor
  · intro h L _ _ m I
    rw [annihilator_orderAssociatedGradedModule]
    exact h L m I
  · intro h L _ _ m I
    have := h L m I
    rwa [annihilator_orderAssociatedGradedModule] at this

theorem weylOrderInitialRadicalInvolutivity_of_associatedGraded
    (h : WeylAssociatedGradedRadicalInvolutivity.{u}) :
    WeylOrderInitialRadicalInvolutivity.{u} :=
  weylOrderInitialRadicalInvolutivity_iff_associatedGraded.mpr h

/-- Descent from the radical to its minimal primes.  This is the step that
removes the mismatch between the citation and the project interface. -/
theorem rightWeylMinimalPrimeInvolutivity_of_radical
    (h : WeylOrderInitialRadicalInvolutivity.{u}) :
    RightWeylMinimalPrimeInvolutivity.{u} := by
  intro L _ _ m I P hP
  exact minimalPrimes_isInvolutive_of_radical_isInvolutive
    (orderInitialIdeal L I) (h L m I) P hP

/-- The canonical right ideal `dA + x₀^N dA` is one right ideal among all of
them, so the generic statement specializes to the lane-B target.  Neither
`0 < N` nor `IsPBWMonicAt` is used. -/
theorem canonicalMinimalPrimeInvolutivityOverFields_of_rightWeyl
    (h : RightWeylMinimalPrimeInvolutivity.{u}) :
    CanonicalMinimalPrimeInvolutivityOverFields.{u} := by
  intro L _ _ n N d _ _ P hP
  exact h L (n + 1) _ P hP

/-- Lane B in one step: residue-extension symbol control from the cited
Gabber theorem for arbitrary right ideals over arbitrary characteristic-zero
fields. -/
theorem canonicalResidueExtensionSymbolControl_of_associatedGradedRadical
    (h : WeylAssociatedGradedRadicalInvolutivity.{u}) :
    CanonicalResidueExtensionSymbolControl.{u} :=
  canonicalResidueExtensionSymbolControl_of_minimalPrimeInvolutivity
    (canonicalMinimalPrimeInvolutivityOverFields_of_rightWeyl
      (rightWeylMinimalPrimeInvolutivity_of_radical
        (weylOrderInitialRadicalInvolutivity_of_associatedGraded h)))


end

end Stafford38.Characteristic.CanonicalGabberInvolutivityInterface
