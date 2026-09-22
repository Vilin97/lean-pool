/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.Invariant.Basic
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core
/-!
# Decomposition and inertia for finite extensions of complete DVFs

For a finite separable extension of complete discretely valued fields, the
extension of the base valuation is unique.  Consequently every
base-field automorphism stabilizes the chosen target valuation ring and the
full Galois group is the decomposition group.  Reduction then gives the
finite Galois exact sequence

`1 -> I(L/K) -> Gal(L/K) -> Gal(k_L/k_K) -> 1`.

The valuation-subring definitions and their ordinary exactness are reused
from `HilbertRamification.ValuationSubring`; this file only supplies the
complete-DVF specialization and the finite-Galois surjectivity theorem.
-/

noncomputable section

open scoped Pointwise

universe u v w x

namespace RamificationTheory.HilbertRamification.CompleteDVF

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

private instance decompositionGroupMulSemiringAction :
    MulSemiringAction
      (ValuationSubring.decompositionGroup K
        target.valuation.valuationSubring)
      target.valuationSubring := by
  change MulSemiringAction
    (target.valuation.valuationSubring.decompositionSubgroup K)
    target.valuation.valuationSubring
  infer_instance

private noncomputable instance decompositionGroupResidueFieldMulSemiringAction :
    MulSemiringAction
      (ValuationSubring.decompositionGroup K
        target.valuation.valuationSubring)
      target.residueField := by
  change MulSemiringAction
    (target.valuation.valuationSubring.decompositionSubgroup K)
    (IsLocalRing.ResidueField target.valuation.valuationSubring)
  infer_instance

private theorem comapValuation_hasExtension
    (sigma : L ≃ₐ[K] L) :
    base.valuation.HasExtension
      (target.valuation.comap (sigma : L →+* L)) where
  val_isEquiv_comap := by
    rw [_root_.Valuation.isEquiv_iff_val_le_one]
    intro a
    simpa [_root_.Valuation.comap, sigma.commutes a] using
      (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := base.valuation) (vA := target.valuation) a).symm

section ValuationUniqueness

variable [FiniteDimensional K L]

include base target

private theorem inv_smul_valuationSubring_eq
    [Algebra.IsSeparable K L]
    (sigma : L ≃ₐ[K] L) :
    sigma⁻¹ • target.valuation.valuationSubring =
      target.valuation.valuationSubring := by
  let pulledBack := target.valuation.comap (sigma : L →+* L)
  let : base.valuation.HasExtension pulledBack :=
    comapValuation_hasExtension (base := base) (target := target) sigma
  have hEquiv : target.valuation.IsEquiv pulledBack :=
    (hasUniqueValuationExtension_of_finite_separable base target :
      ValuedExtension.HasUniqueValuationExtension.{u, v, w, x, x}
        (base := base) (target := target)) pulledBack
  have hSubring :
      target.valuation.valuationSubring = pulledBack.valuationSubring :=
    (_root_.Valuation.isEquiv_iff_valuationSubring
      target.valuation pulledBack).1 hEquiv
  have hComap :
      pulledBack.valuationSubring =
        sigma⁻¹ • target.valuation.valuationSubring := by
    ext z
    change target.valuation (sigma z) ≤ 1 ↔
      z ∈ sigma⁻¹ • target.valuation.valuationSubring
    rw [_root_.ValuationSubring.mem_inv_pointwise_smul_iff]
    simp [AlgEquiv.smul_def, _root_.Valuation.mem_valuationSubring_iff]
  exact hComap.symm.trans hSubring.symm

/-- Every automorphism of a finite separable extension of complete DVFs
stabilizes the target valuation ring. -/
theorem automorphism_stabilizes_valuationSubring
    [Algebra.IsSeparable K L]
    (sigma : L ≃ₐ[K] L) :
    sigma • target.valuation.valuationSubring =
      target.valuation.valuationSubring := by
  have hinv := inv_smul_valuationSubring_eq
    (base := base) (target := target) sigma
  calc
    sigma • target.valuation.valuationSubring =
        sigma • (sigma⁻¹ • target.valuation.valuationSubring) := by rw [hinv]
    _ = target.valuation.valuationSubring := by simp [smul_smul]

/-- For a finite separable extension of complete DVFs, the full automorphism
group is canonically the decomposition group of the target valuation ring. -/
def galEquivDecompositionGroup
    [Algebra.IsSeparable K L] :
    (L ≃ₐ[K] L) ≃*
      ValuationSubring.decompositionGroup K
        target.valuation.valuationSubring where
  toFun sigma := ⟨sigma, by
    change sigma • target.valuation.valuationSubring =
      target.valuation.valuationSubring
    exact automorphism_stabilizes_valuationSubring
      (base := base) (target := target) sigma⟩
  invFun sigma := (sigma : L ≃ₐ[K] L)
  left_inv _ := rfl
  right_inv _ := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl

/-- States the theorem `galEquivDecompositionGroup_coe`. -/
@[simp]
theorem galEquivDecompositionGroup_coe
    [Algebra.IsSeparable K L]
    (sigma : L ≃ₐ[K] L) :
    ((galEquivDecompositionGroup (base := base) (target := target) sigma :
        ValuationSubring.decompositionGroup K
      target.valuation.valuationSubring) : L ≃ₐ[K] L) = sigma :=
  rfl

end ValuationUniqueness

/-- Reduction of the decomposition-group action, as automorphisms over the
base residue field. -/
def decompositionResidueAction :
    ValuationSubring.decompositionGroup K
        target.valuation.valuationSubring →*
      (target.residueField ≃ₐ[base.residueField] target.residueField) where
  toFun sigma :=
    { ValuationSubring.residueAction K target.valuation.valuationSubring sigma with
      commutes' := by
        intro z
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
        change
          ValuationSubring.residueAction K target.valuation.valuationSubring sigma
              (IsLocalRing.residue target.valuationSubring
                (algebraMap base.valuationSubring target.valuationSubring a)) =
            IsLocalRing.residue target.valuationSubring
              (algebraMap base.valuationSubring target.valuationSubring a)
        change
          sigma •
              (IsLocalRing.residue target.valuationSubring
                (algebraMap base.valuationSubring target.valuationSubring a)) =
            IsLocalRing.residue target.valuationSubring
              (algebraMap base.valuationSubring target.valuationSubring a)
        change
          IsLocalRing.residue target.valuationSubring
              (sigma •
                algebraMap base.valuationSubring target.valuationSubring a) =
            IsLocalRing.residue target.valuationSubring
              (algebraMap base.valuationSubring target.valuationSubring a)
        congr 1
        apply Subtype.ext
        change
          (sigma : L ≃ₐ[K] L) (algebraMap K L (a : K)) =
            algebraMap K L (a : K)
        exact (sigma : L ≃ₐ[K] L).commutes (a : K) }
  map_one' := by
    apply AlgEquiv.ext
    intro z
    change
      ValuationSubring.residueAction K target.valuation.valuationSubring 1 z =
        (1 : target.residueField ≃ₐ[base.residueField] target.residueField) z
    rw [MonoidHom.map_one]
    exact AlgEquiv.one_apply (R := base.residueField) (A₁ := target.residueField) z
  map_mul' := by
    intro sigma tau
    apply AlgEquiv.ext
    intro z
    change
      ValuationSubring.residueAction K target.valuation.valuationSubring
          (sigma * tau) z =
        (ValuationSubring.residueAction K target.valuation.valuationSubring sigma *
          ValuationSubring.residueAction K target.valuation.valuationSubring tau) z
    rw [MonoidHom.map_mul]

/-- States the theorem `decompositionResidueAction_apply`. -/
@[simp]
theorem decompositionResidueAction_apply
    (sigma : ValuationSubring.decompositionGroup K
      target.valuation.valuationSubring)
    (z : target.residueField) :
    decompositionResidueAction (K := K) (base := base) (target := target) sigma z =
      ValuationSubring.residueAction K
        target.valuation.valuationSubring sigma z :=
  rfl

/-- States the theorem `decompositionResidueAction_algebraMap`. -/
theorem decompositionResidueAction_algebraMap
    (sigma : ValuationSubring.decompositionGroup K
      target.valuation.valuationSubring)
    (z : base.residueField) :
    decompositionResidueAction (K := K) (base := base) (target := target) sigma
        (algebraMap base.residueField target.residueField z) =
      algebraMap base.residueField target.residueField z :=
  (decompositionResidueAction
    (K := K) (base := base) (target := target) sigma).commutes z

/-- The kernel of reduction on the decomposition group is its inertia group. -/
theorem decompositionResidueAction_ker :
    MonoidHom.ker
        (decompositionResidueAction
          (K := K) (base := base) (target := target)) =
      ValuationSubring.inertiaGroup K
        target.valuation.valuationSubring := by
  rw [← ValuationSubring.residueAction_ker
    (K := K) target.valuation.valuationSubring]
  ext sigma
  change
    decompositionResidueAction (K := K) (base := base) (target := target) sigma = 1 ↔
      ValuationSubring.residueAction K
        target.valuation.valuationSubring sigma = 1
  constructor
  · intro h
    apply RingEquiv.ext
    intro z
    have hz := congrArg
      (fun e : target.residueField ≃ₐ[base.residueField] target.residueField => e z) h
    simpa using hz
  · intro h
    apply AlgEquiv.ext
    intro z
    have hz := congrArg
      (fun e : target.residueField ≃+* target.residueField => e z) h
    simpa using hz

omit [base.valuation.HasExtension target.valuation] in
/-- Ideal-theoretic inertia of the target maximal ideal, for the canonical
decomposition-group action on the valuation ring, is the ordinary
valuation-subring inertia group. -/
theorem maximalIdealInertia_eq_decompositionInertia :
    target.maximalIdeal.toAddSubgroup.inertia
        (ValuationSubring.decompositionGroup K
          target.valuation.valuationSubring) =
      ValuationSubring.inertiaGroup K
        target.valuation.valuationSubring := by
  ext sigma
  rw [← ValuationSubring.residueAction_ker
    (K := K) target.valuation.valuationSubring, MonoidHom.mem_ker]
  constructor
  · intro hsigma
    apply RingEquiv.ext
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    change sigma •
        (IsLocalRing.residue target.valuationSubring a : target.residueField) =
      IsLocalRing.residue target.valuationSubring a
    change
      IsLocalRing.residue target.valuationSubring (sigma • a) =
        IsLocalRing.residue target.valuationSubring a
    rw [ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal]
    exact hsigma a
  · intro hsigma a
    change sigma • a - a ∈ target.maximalIdeal
    rw [← ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal]
    have happ := congrArg
      (fun e : target.residueField ≃+* target.residueField =>
        e (IsLocalRing.residue target.valuationSubring a)) hsigma
    change sigma •
        (IsLocalRing.residue target.valuationSubring a : target.residueField) =
      IsLocalRing.residue target.valuationSubring a at happ
    change
      IsLocalRing.residue target.valuationSubring (sigma • a) =
        IsLocalRing.residue target.valuationSubring a at happ
    exact happ

/-- Exactness of inertia inclusion followed by reduction on the decomposition
group. -/
theorem decompositionInertia_mulExact_decompositionResidueAction :
    Function.MulExact
      (ValuationSubring.inertiaGroup K
        target.valuation.valuationSubring).subtype
      (decompositionResidueAction
        (K := K) (base := base) (target := target)) := by
  rw [MonoidHom.mulExact_iff, decompositionResidueAction_ker]
  exact (Subgroup.range_subtype _).symm

section FullGaloisGroup

variable [FiniteDimensional K L]

include base target

/-- The residue action of the full automorphism group, transported through
the canonical identification with the decomposition group. -/
def residueAction
    [Algebra.IsSeparable K L] :
    (L ≃ₐ[K] L) →*
      (target.residueField ≃ₐ[base.residueField] target.residueField) :=
  (decompositionResidueAction
    (K := K) (base := base) (target := target)).comp
    (galEquivDecompositionGroup
      (base := base) (target := target)).toMonoidHom

/-- States the theorem `residueAction_apply`. -/
@[simp]
theorem residueAction_apply
    [Algebra.IsSeparable K L]
    (sigma : L ≃ₐ[K] L) :
    residueAction (K := K) (base := base) (target := target) sigma =
      decompositionResidueAction
        (K := K) (base := base) (target := target)
        (galEquivDecompositionGroup
          (base := base) (target := target) sigma) :=
  rfl

/-- Inertia inside the full Galois group is the inverse image of the ordinary
decomposition-side inertia group. -/
def inertiaGroup
    [Algebra.IsSeparable K L] :
    Subgroup (L ≃ₐ[K] L) :=
  Subgroup.comap
    (galEquivDecompositionGroup
      (base := base) (target := target)).toMonoidHom
    (ValuationSubring.inertiaGroup K
      target.valuation.valuationSubring)

/-- States the theorem `mem_inertiaGroup_iff`. -/
@[simp]
theorem mem_inertiaGroup_iff
    [Algebra.IsSeparable K L]
    (sigma : L ≃ₐ[K] L) :
    sigma ∈ inertiaGroup (K := K) (base := base) (target := target) ↔
      galEquivDecompositionGroup
          (base := base) (target := target) sigma ∈
        ValuationSubring.inertiaGroup K
          target.valuation.valuationSubring :=
  Iff.rfl

/-- Transporting full inertia through `Gal(L/K) ≃ D(L/K)` gives exactly the
ordinary decomposition-side inertia group. -/
theorem inertiaGroup_map_galEquivDecompositionGroup
    [Algebra.IsSeparable K L] :
    Subgroup.map
        (galEquivDecompositionGroup
          (base := base) (target := target)).toMonoidHom
        (inertiaGroup (K := K) (base := base) (target := target)) =
      ValuationSubring.inertiaGroup K
        target.valuation.valuationSubring := by
  ext tau
  constructor
  · rintro ⟨sigma, hsigma, rfl⟩
    exact hsigma
  · intro htau
    refine ⟨(galEquivDecompositionGroup
      (base := base) (target := target)).symm tau, ?_, ?_⟩
    · change galEquivDecompositionGroup
        (base := base) (target := target)
          ((galEquivDecompositionGroup
            (base := base) (target := target)).symm tau) ∈
        ValuationSubring.inertiaGroup K
          target.valuation.valuationSubring
      simpa using htau
    · simp

/-- The kernel of the full residue action is the full inertia group. -/
theorem residueAction_ker
    [Algebra.IsSeparable K L] :
    MonoidHom.ker
        (residueAction (K := K) (base := base) (target := target)) =
      inertiaGroup (K := K) (base := base) (target := target) := by
  ext sigma
  change
    decompositionResidueAction
        (K := K) (base := base) (target := target)
        (galEquivDecompositionGroup
          (base := base) (target := target) sigma) = 1 ↔
      galEquivDecompositionGroup
          (base := base) (target := target) sigma ∈
        ValuationSubring.inertiaGroup K
          target.valuation.valuationSubring
  rw [← decompositionResidueAction_ker
    (K := K) (base := base) (target := target)]
  rfl

/-- Provides the instance `inertiaGroup_normal`. -/
instance inertiaGroup_normal
    [Algebra.IsSeparable K L] :
    (inertiaGroup (K := K) (base := base) (target := target)).Normal := by
  rw [← residueAction_ker]
  infer_instance

/-- Exactness of full inertia inclusion followed by reduction. -/
theorem inertia_mulExact_residueAction
    [Algebra.IsSeparable K L] :
    Function.MulExact
      (inertiaGroup (K := K) (base := base) (target := target)).subtype
      (residueAction (K := K) (base := base) (target := target)) := by
  rw [MonoidHom.mulExact_iff, residueAction_ker]
  exact (Subgroup.range_subtype _).symm

/-- For a finite Galois extension of complete DVFs, reduction of the full
Galois group is onto the residue-field Galois group. -/
theorem residueAction_surjective_of_isGalois
    [IsGalois K L] :
    Function.Surjective
      (residueAction (K := K) (base := base) (target := target)) := by
  let : IsScalarTower base.valuationSubring target.valuationSubring L :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_isScalarTower_of_hasExtension
      base.valuation target.valuation
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : MulSemiringAction (L ≃ₐ[K] L) target.valuationSubring := by
    change MulSemiringAction (L ≃ₐ[K] L)
      target.valuation.valuationSubring
    exact MulSemiringAction.compHom
      (R := target.valuation.valuationSubring)
      (galEquivDecompositionGroup
        (base := base) (target := target)).toMonoidHom
  let : SMulDistribClass (L ≃ₐ[K] L) target.valuationSubring L :=
    { smul_distrib_smul := by
        intro sigma r z
        change sigma ((r : L) * z) = sigma (r : L) * sigma z
        rw [map_mul] }
  let : IsGaloisGroup (L ≃ₐ[K] L)
      base.valuationSubring target.valuationSubring :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L)
      base.valuationSubring target.valuationSubring K L
  let : target.maximalIdeal.LiesOver base.maximalIdeal :=
    maximalIdeal_liesOver base target
  intro rho
  rcases Ideal.Quotient.stabilizerHom_surjective
      (G := L ≃ₐ[K] L) base.maximalIdeal target.maximalIdeal rho with
    ⟨sigma, hsigma⟩
  refine ⟨sigma.1, ?_⟩
  rw [← hsigma]
  apply AlgEquiv.ext
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/-- The decomposition-group residue action is also onto in the finite Galois
case. -/
theorem decompositionResidueAction_surjective_of_isGalois
    [IsGalois K L] :
    Function.Surjective
      (decompositionResidueAction
        (K := K) (base := base) (target := target)) := by
  intro rho
  obtain ⟨sigma, hsigma⟩ :=
    residueAction_surjective_of_isGalois
      (K := K) (base := base) (target := target) rho
  exact ⟨galEquivDecompositionGroup
    (base := base) (target := target) sigma, hsigma⟩

/-- The finite-Galois residue exact sequence in quotient form. -/
def galQuotientInertiaEquivResidueGalois
    [IsGalois K L] :
    (L ≃ₐ[K] L) ⧸
        inertiaGroup (K := K) (base := base) (target := target) ≃*
      (target.residueField ≃ₐ[base.residueField] target.residueField) :=
  (QuotientGroup.quotientMulEquivOfEq
      (residueAction_ker
        (K := K) (base := base) (target := target)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (residueAction (K := K) (base := base) (target := target))
      (residueAction_surjective_of_isGalois
        (K := K) (base := base) (target := target)))

/-- States the theorem `galQuotientInertiaEquivResidueGalois_mk`. -/
theorem galQuotientInertiaEquivResidueGalois_mk
    [IsGalois K L]
    (sigma : L ≃ₐ[K] L) :
    galQuotientInertiaEquivResidueGalois
        (K := K) (base := base) (target := target)
        (QuotientGroup.mk'
          (inertiaGroup (K := K) (base := base) (target := target)) sigma) =
      residueAction (K := K) (base := base) (target := target) sigma := by
  exact residueAction_apply (base := base) (target := target) sigma

end FullGaloisGroup

end RamificationTheory.HilbertRamification.CompleteDVF

end
