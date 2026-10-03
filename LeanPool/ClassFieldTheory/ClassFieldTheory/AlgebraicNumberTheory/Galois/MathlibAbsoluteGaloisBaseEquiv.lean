/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Infinite.TopologicalAbelianizationCongr
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
/-!
# Absolute Galois groups under an equivalence of base fields

A field equivalence extends to an equivalence of the chosen algebraic closures.
Conjugation then identifies the absolute Galois groups, including their Krull
topologies, and hence their topological abelianizations.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

universe u v w z

variable {K : Type u} {M : Type v} {Ω : Type w} {Ψ : Type z}
  [Field K] [Field M] [Field Ω] [Field Ψ]
  [Algebra K Ω] [Algebra M Ψ]

private theorem semilinear_symm_algebraMap (e : K ≃+* M) (E : Ω ≃+* Ψ)
    (hE : ∀ x : K, E (algebraMap K Ω x) = algebraMap M Ψ (e x))
    (y : M) :
    E.symm (algebraMap M Ψ y) = algebraMap K Ω (e.symm y) := by
  apply E.injective
  rw [E.apply_symm_apply, hE, e.apply_symm_apply]

/-- Transport a Galois automorphism through compatible semilinear field identifications. -/
def semilinearGaloisConjugate (e : K ≃+* M) (E : Ω ≃+* Ψ)
    (hE : ∀ x : K, E (algebraMap K Ω x) = algebraMap M Ψ (e x))
    (σ : Gal(Ω/K)) : Gal(Ψ/M) where
  toRingEquiv := (E.symm.trans σ.toRingEquiv).trans E
  commutes' := by
    intro y
    change E (σ (E.symm (algebraMap M Ψ y))) = algebraMap M Ψ y
    rw [semilinear_symm_algebraMap e E hE y, σ.commutes, hE,
      e.apply_symm_apply]

/-- Semilinear field identifications induce an equivalence of Galois groups. -/
def semilinearGaloisEquiv (e : K ≃+* M) (E : Ω ≃+* Ψ)
    (hE : ∀ x : K, E (algebraMap K Ω x) = algebraMap M Ψ (e x)) :
    Gal(Ω/K) ≃* Gal(Ψ/M) where
  toFun := semilinearGaloisConjugate e E hE
  invFun := semilinearGaloisConjugate e.symm E.symm
    (by exact semilinear_symm_algebraMap e E hE)
  left_inv σ := by
    apply AlgEquiv.ext
    intro x
    simp [semilinearGaloisConjugate]
  right_inv σ := by
    apply AlgEquiv.ext
    intro x
    simp [semilinearGaloisConjugate]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    simp [semilinearGaloisConjugate, AlgEquiv.mul_apply]

/-- The semilinear Galois equivalence preserves the Krull topologies. -/
def semilinearGaloisContinuousEquiv (e : K ≃+* M) (E : Ω ≃+* Ψ)
    (hE : ∀ x : K, E (algebraMap K Ω x) = algebraMap M Ψ (e x)) :
    Gal(Ω/K) ≃ₜ* Gal(Ψ/M) where
  toMulEquiv := semilinearGaloisEquiv e E hE
  continuous_toFun := by
    exact RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous
      e E hE (semilinearGaloisEquiv e E hE).toMonoidHom (by intro σ; rfl)
  continuous_invFun := by
    exact RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous
      e.symm E.symm (semilinear_symm_algebraMap e E hE)
      (semilinearGaloisEquiv e.symm E.symm
        (semilinear_symm_algebraMap e E hE)).toMonoidHom (by intro σ; rfl)

/-- A field equivalence identifies the Krull topological absolute Galois groups
of its source and target fields. -/
noncomputable def absoluteGaloisGroupEquivOfRingEquiv (e : K ≃+* M) :
    Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup M :=
  semilinearGaloisContinuousEquiv e
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure M) e)
    (IsAlgClosure.equivOfEquiv_algebraMap
      (AlgebraicClosure K) (AlgebraicClosure M) e)

/-- The induced equivalence of Mathlib's topological abelianizations. -/
noncomputable def absoluteGaloisGroupAbelianizationEquivOfRingEquiv
    (e : K ≃+* M) :
    Field.absoluteGaloisGroupAbelianization K ≃ₜ*
      Field.absoluteGaloisGroupAbelianization M :=
  LocalClassFieldTheory.topologicalAbelianizationCongr
    (absoluteGaloisGroupEquivOfRingEquiv e)

end ClassFieldTheory
