/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.StandardEtale
/-!
# Lifting points of standard étale algebras

The simple-root condition for a Henselian pair lifts a residue point of a
standard étale algebra to the base ring. The defining monic polynomial and
its derivative condition supply the Hensel input, and the Jacobson condition
makes the localization denominator invertible at the lifted root.
-/

@[expose] public section

namespace ValuationTheory.Henselian

variable {R : Type*} [CommRing R] {I : Ideal R} [HenselianRing R I]

/-- A point of a standard étale algebra modulo a Henselian ideal lifts to
a point over the original ring. -/
theorem exists_standardEtale_lift
    (P : StandardEtalePair R) (σ : P.Ring →ₐ[R] R ⧸ I) :
    ∃ τ : P.Ring →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp τ = σ := by
  let q : R →ₐ[R] R ⧸ I := Ideal.Quotient.mkₐ R I
  have hσ : P.HasMap (σ P.X) := P.hasMap_X.map σ
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (σ P.X)
  change q a₀ = σ P.X at ha₀
  have hroot : P.f.eval a₀ ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (Polynomial.aeval a₀ P.f) = 0
    rw [← Polynomial.aeval_algHom_apply, ha₀]
    exact hσ.1
  have hsimple : IsUnit (Ideal.Quotient.mk I (P.f.derivative.eval a₀)) := by
    change IsUnit (q (Polynomial.aeval a₀ P.f.derivative))
    rw [← Polynomial.aeval_algHom_apply, ha₀]
    exact StandardEtalePair.HasMap.isUnit_derivative_f P hσ
  obtain ⟨a, ha, hacongr⟩ := HenselianRing.is_henselian P.f P.monic_f a₀ hroot hsimple
  have hqa : q a = σ P.X := by
    exact (Ideal.Quotient.eq.mpr hacongr).trans ha₀
  have hdenom : IsUnit (Polynomial.aeval a P.g) := by
    let : IsLocalHom (Ideal.Quotient.mk I) :=
      isLocalHom_of_le_jacobson_bot I HenselianRing.jac
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    change IsUnit (q (Polynomial.aeval a P.g))
    rw [← Polynomial.aeval_algHom_apply, hqa]
    exact hσ.2
  have haP : P.HasMap a := ⟨ha, hdenom⟩
  refine ⟨P.lift a haP, ?_⟩
  apply P.hom_ext
  rw [AlgHom.comp_apply, P.lift_X]
  exact hqa

/-- A residue point of an algebra admitting a standard étale presentation
lifts over a Henselian pair. -/
theorem exists_isStandardEtale_lift
    {S : Type*} [CommRing S] [Algebra R S] [Algebra.IsStandardEtale R S]
    (σ : S →ₐ[R] R ⧸ I) :
    ∃ τ : S →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp τ = σ := by
  let P : StandardEtalePresentation R S :=
    Classical.choice (inferInstance : Nonempty (StandardEtalePresentation R S))
  obtain ⟨τ, hτ⟩ := exists_standardEtale_lift P.P
    (σ.comp P.equivRing.symm.toAlgHom)
  refine ⟨τ.comp P.equivRing.toAlgHom, ?_⟩
  apply AlgHom.ext
  intro s
  change Ideal.Quotient.mk I (τ (P.equivRing s)) = σ s
  calc
    Ideal.Quotient.mk I (τ (P.equivRing s)) =
        σ (P.equivRing.symm (P.equivRing s)) := DFunLike.congr_fun hτ (P.equivRing s)
    _ = σ s := congrArg σ (P.equivRing.symm_apply_apply s)

end ValuationTheory.Henselian
