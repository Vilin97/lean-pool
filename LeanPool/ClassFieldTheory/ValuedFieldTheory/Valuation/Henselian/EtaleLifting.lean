/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.StandardEtaleLifting
public import Mathlib.RingTheory.Unramified.LocalStructure
/-!
# Lifting residue points of etale algebras

At the kernel of a residue point, an etale algebra has a standard etale
localization. The Henselian root lift on that localization restricts to
the requested lift on the original algebra.
-/

@[expose] public section

namespace ValuationTheory.Henselian

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {I : Ideal R} [I.IsMaximal] [HenselianRing R I] [Algebra.Etale R S]

/-- A residue point of an etale algebra over a Henselian local pair lifts
to an actual point over the base ring. -/
theorem exists_etale_lift (σ : S →ₐ[R] R ⧸ I) :
    ∃ τ : S →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp τ = σ := by
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  let Q : Ideal S := RingHom.ker σ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime σ.toRingHom
  obtain ⟨s, hs, hstandard⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  have : Algebra.IsStandardEtale R (Localization.Away s) := hstandard
  have hsunit : IsUnit (σ s) := isUnit_iff_ne_zero.mpr (show σ s ≠ 0 from hs)
  let σloc : Localization.Away s →ₐ[R] R ⧸ I :=
    IsLocalization.Away.liftAlgHom (f := σ) s hsunit
  obtain ⟨τloc, hτloc⟩ := exists_isStandardEtale_lift σloc
  refine ⟨τloc.comp (IsScalarTower.toAlgHom R S (Localization.Away s)), ?_⟩
  apply AlgHom.ext
  intro x
  have hx := congrArg (fun f : Localization.Away s →ₐ[R] R ⧸ I =>
    f (algebraMap S (Localization.Away s) x)) hτloc
  change Ideal.Quotient.mk I (τloc (algebraMap S (Localization.Away s) x)) = σ x
  exact hx.trans (IsLocalization.Away.lift_eq s hsunit x)

end ValuationTheory.Henselian
