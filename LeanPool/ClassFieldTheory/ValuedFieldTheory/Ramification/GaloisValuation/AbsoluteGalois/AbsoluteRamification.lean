/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction

/-! # Absolute Ramification -/

@[expose] public section

open _root_.RamificationTheory.ValuationSubring renaming
  mem_algEquiv_apply_iff_of_restrictIntermediateField_henselianUnique →
    mem_algEquiv_apply_iff_of_restrictIntermediateField_henselianUnique

open _root_.RamificationTheory.ValuationSubring renaming
  mem_algEquiv_apply_iff_of_restrictIntermediateField_unique →
    mem_algEquiv_apply_iff_of_restrictIntermediateField_unique

open _root_.ValuationTheory.DiscreteValuationField.HenselianDVF renaming
  HasUniqueValuationExtension →
    HasUniqueValuationExtension

open _root_.ValuationTheory.DiscreteValuationField.HenselianDVF renaming
  valuationSubring_eq_of_hasUniqueValuationExtension →
    valuationSubring_eq_of_hasUniqueValuationExtension

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosure_mem_valuationSubring_of_hasExtension →
    integralClosure_mem_valuationSubring_of_hasExtension

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  valuationSubring_mem_integralClosure_of_isIntegral →
    valuationSubring_mem_integralClosure_of_isIntegral

namespace RamificationTheory

open ValuationTheory

/-!
# Absolute Galois ramification

This file develops the decomposition and inertia subgroups of an absolute
Galois group after the finite-level valuation-restriction layer.
-/

noncomputable
section

universe u v w z

namespace Field
namespace absoluteGaloisGroup

open scoped Topology Pointwise
open CategoryTheory

section AbsoluteRamification

variable (K : Type u) [Field K]

/-- Absolute Galois automorphisms commute with natural powers in the algebraic
closure. -/
theorem apply_pow
    (σ : Field.absoluteGaloisGroup K) (z : AlgebraicClosure K) (n : ℕ) :
    (show Gal(AlgebraicClosure K/K) from σ) (z ^ n) =
      ((show Gal(AlgebraicClosure K/K) from σ) z) ^ n := by
  exact map_pow (show Gal(AlgebraicClosure K/K) from σ) z n

/-- Provides the instance `absoluteGaloisGroupMulSemiringActionAlgebraicClosure`. -/
noncomputable instance absoluteGaloisGroupMulSemiringActionAlgebraicClosure :
    MulSemiringAction
      (Field.absoluteGaloisGroup K) (AlgebraicClosure K) := by
  change MulSemiringAction
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (AlgebraicClosure K)
  infer_instance

/-- The absolute decomposition subgroup attached to a chosen valuation subring
of the algebraic closure. -/
abbrev decompositionSubgroup
    (A : ValuationSubring (AlgebraicClosure K)) :
    Subgroup (Field.absoluteGaloisGroup K) :=
  A.decompositionSubgroup K

/-- Provides the instance `decompositionSubgroupMulSemiringAction`. -/
instance decompositionSubgroupMulSemiringAction
    (A : ValuationSubring (AlgebraicClosure K)) :
    MulSemiringAction (decompositionSubgroup K A) A := by
  change MulSemiringAction (A.decompositionSubgroup K) A
  infer_instance

/-- The absolute decomposition subgroup is the stabilizer of the chosen
valuation subring. -/
theorem decompositionSubgroup_eq_stabilizer
    (A : ValuationSubring (AlgebraicClosure K)) :
    decompositionSubgroup K A =
      MulAction.stabilizer (Field.absoluteGaloisGroup K) A :=
  rfl

/-- Membership in the absolute decomposition subgroup is stabilization of the
chosen valuation subring. -/
@[simp] theorem mem_decompositionSubgroup_iff
    (A : ValuationSubring (AlgebraicClosure K))
    (σ : Field.absoluteGaloisGroup K) :
    σ ∈ decompositionSubgroup K A ↔ σ • A = A := by
  rw [decompositionSubgroup_eq_stabilizer, MulAction.mem_stabilizer_iff]

/-- Absolute decomposition is all of `G_K` exactly when every absolute
automorphism stabilizes the chosen valuation subring. -/
theorem decompositionSubgroup_eq_top_iff_forall_smul_eq
    (A : ValuationSubring (AlgebraicClosure K)) :
    decompositionSubgroup K A = ⊤ ↔
      ∀ σ : Field.absoluteGaloisGroup K, σ • A = A := by
  constructor
  · intro hA σ
    rw [← mem_decompositionSubgroup_iff (K := K) A σ]
    rw [hA]
    exact Subgroup.mem_top σ
  · intro hA
    ext σ
    rw [mem_decompositionSubgroup_iff]
    simp [hA σ]

/-- Route-P core for the absolute decomposition group: if every finite
separable intermediate restriction of the ambient valuation subring is the
unique extension of the base valuation, then the absolute decomposition group
is all of `G_K`.

The proof reduces an arbitrary algebraic element to a positive power in a
finite separable intermediate field, uses finite-level uniqueness there, and
returns to the original element by valuation-subring power membership. -/
theorem decompositionSubgroup_eq_top_of_finite_separable_restrictUnique
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension v A.valuation]
    (huniq :
      ∀ (E : IntermediateField K (AlgebraicClosure K))
        [FiniteDimensional K E] [Algebra.IsSeparable K E],
          ∀ (B : ValuationSubring E)
            [_root_.Valuation.HasExtension v B.valuation],
              (RamificationTheory.ValuationSubring.restrictIntermediateField A E) = B) :
    decompositionSubgroup K A = ⊤ := by
  have hpres
      (σ : Field.absoluteGaloisGroup K) (z : AlgebraicClosure K) :
      z ∈ A ↔ (show Gal(AlgebraicClosure K/K) from σ) z ∈ A := by
    obtain ⟨n, E, hn, hFin, hSep, hzpowE⟩ :=
      RamificationTheory.exists_finite_separable_intermediate_pow_mem (K := K) z
    let : FiniteDimensional K E := hFin
    let : Algebra.IsSeparable K E := hSep
    let x : E := ⟨z ^ n, hzpowE⟩
    have hlevel :
        ((x : AlgebraicClosure K) ∈ A) ↔
          (show Gal(AlgebraicClosure K/K) from σ)
            (x : AlgebraicClosure K) ∈ A := by
      exact
        mem_algEquiv_apply_iff_of_restrictIntermediateField_unique
          (v := v) (A := A) (E := E) (huniq E)
          (show Gal(AlgebraicClosure K/K) from σ) x
    have hpow :
        z ^ n ∈ A ↔
          (show Gal(AlgebraicClosure K/K) from σ) (z ^ n) ∈ A := by
      simpa [x] using hlevel
    have hpowmap :
        z ^ n ∈ A ↔
          ((show Gal(AlgebraicClosure K/K) from σ) z) ^ n ∈ A := by
      simpa [apply_pow (K := K) σ z n] using hpow
    exact (RamificationTheory.ValuationSubring.mem_iff_pow_mem A z hn).trans
      (hpowmap.trans
        (RamificationTheory.ValuationSubring.mem_iff_pow_mem A
          ((show Gal(AlgebraicClosure K/K) from σ) z) hn).symm)
  rw [decompositionSubgroup_eq_top_iff_forall_smul_eq]
  intro σ
  ext z
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  change (show Gal(AlgebraicClosure K/K) from σ⁻¹) z ∈ A ↔ z ∈ A
  exact (hpres σ⁻¹ z).symm

/-- Target-free finite-level membership preservation on a finite separable
intermediate field, assuming the restricted valuation subring is the unique
extension of the base valuation on that level. -/
theorem valuationSubring_mem_preserved_on_finite_separable_intermediate_of_restrictUnique
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (huniq :
      ∀ (B : ValuationSubring E)
        [_root_.Valuation.HasExtension F.valuation B.valuation],
          (RamificationTheory.ValuationSubring.restrictIntermediateField A E) = B)
    (σ : Field.absoluteGaloisGroup K) (x : E) :
    ((x : AlgebraicClosure K) ∈ A) ↔
      (show Gal(AlgebraicClosure K/K) from σ) (x : AlgebraicClosure K) ∈ A :=
  mem_algEquiv_apply_iff_of_restrictIntermediateField_unique
    (v := F.valuation) (A := A) (E := E) huniq
    (show Gal(AlgebraicClosure K/K) from σ) x

/-- Target-free finite-level membership preservation from the integral
valuation-ring frontier on that finite separable level. -/
theorem valuationSubring_mem_preserved_on_finite_separable_intermediate_of_integral
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (hintegral :
      ∀ (B : ValuationSubring E)
        [_root_.Valuation.HasExtension F.valuation B.valuation],
          Algebra.IsIntegral F.valuation.valuationSubring
            B.valuation.valuationSubring)
    (σ : Field.absoluteGaloisGroup K) (x : E) :
    ((x : AlgebraicClosure K) ∈ A) ↔
      (show Gal(AlgebraicClosure K/K) from σ) (x : AlgebraicClosure K) ∈ A := by
  exact
    valuationSubring_mem_preserved_on_finite_separable_intermediate_of_restrictUnique
      (K := K) (F := F) (A := A) (E := E)
      (huniq := by
        intro B _
        have hAExt : _root_.Valuation.HasExtension F.valuation
            ((RamificationTheory.ValuationSubring.restrictIntermediateField A E)).valuation :=
          RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension
            (v := F.valuation) (A := A) E
        have hAInt : Algebra.IsIntegral F.valuation.valuationSubring
            ((RamificationTheory.ValuationSubring.restrictIntermediateField A
              E)).valuation.valuationSubring :=
          hintegral ((RamificationTheory.ValuationSubring.restrictIntermediateField A E))
        have hBInt : Algebra.IsIntegral F.valuation.valuationSubring
            B.valuation.valuationSubring :=
          hintegral B
        have hsub :
            ((RamificationTheory.ValuationSubring.restrictIntermediateField A
              E)).valuation.valuationSubring =
              B.valuation.valuationSubring := by
          ext z
          constructor
          · intro hz
            have hz_int : z ∈ integralClosure F.valuation.valuationSubring E :=
              valuationSubring_mem_integralClosure_of_isIntegral
                (L := E) F.valuation
                  ((RamificationTheory.ValuationSubring.restrictIntermediateField A
                  E)).valuation ⟨z, hz⟩
            exact
              integralClosure_mem_valuationSubring_of_hasExtension
                (L := E) F.valuation B.valuation ⟨z, hz_int⟩
          · intro hz
            have hz_int : z ∈ integralClosure F.valuation.valuationSubring E :=
              valuationSubring_mem_integralClosure_of_isIntegral
                (L := E) F.valuation B.valuation ⟨z, hz⟩
            exact
              integralClosure_mem_valuationSubring_of_hasExtension
                (L := E) F.valuation
                  ((RamificationTheory.ValuationSubring.restrictIntermediateField A
                  E)).valuation ⟨z, hz_int⟩
        calc
          RamificationTheory.ValuationSubring.restrictIntermediateField A E =
              (RamificationTheory.ValuationSubring.restrictIntermediateField A
                E).valuation.valuationSubring :=
            (ValuationSubring.valuationSubring_valuation _).symm
          _ = B.valuation.valuationSubring := hsub
          _ = B := ValuationSubring.valuationSubring_valuation B)
      (σ := σ) (x := x)

/-- Module-finite variant of finite-level membership preservation. -/
theorem valuationSubring_mem_preserved_on_finite_separable_intermediate_of_moduleFinite
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (hfinite :
      ∀ (B : ValuationSubring E)
        [_root_.Valuation.HasExtension F.valuation B.valuation],
          Module.Finite F.valuation.valuationSubring
            B.valuation.valuationSubring)
    (σ : Field.absoluteGaloisGroup K) (x : E) :
    ((x : AlgebraicClosure K) ∈ A) ↔
      (show Gal(AlgebraicClosure K/K) from σ) (x : AlgebraicClosure K) ∈ A :=
  valuationSubring_mem_preserved_on_finite_separable_intermediate_of_integral
    (K := K) (F := F) (A := A) (E := E)
    (hintegral := by
      intro B _
      let : Module.Finite F.valuation.valuationSubring
          B.valuation.valuationSubring :=
        hfinite B
      infer_instance)
    (σ := σ) (x := x)

/-- Finite-level membership preservation from a Henselian-DVF unique-extension
package on that level. -/
theorem valuationSubring_mem_preserved_on_finite_separable_intermediate
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (target : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, w} E)
    (hA : target.valuation.valuationSubring =
      (RamificationTheory.ValuationSubring.restrictIntermediateField A E))
    (huniq :
      HasUniqueValuationExtension.{u, v, u,
        w, u}
        F target)
    (σ : Field.absoluteGaloisGroup K) (x : E) :
    ((x : AlgebraicClosure K) ∈ A) ↔
      (show Gal(AlgebraicClosure K/K) from σ) (x : AlgebraicClosure K) ∈ A :=
  mem_algEquiv_apply_iff_of_restrictIntermediateField_henselianUnique
    (base := F) (A := A) (E := E) (target := target) hA huniq
    (show Gal(AlgebraicClosure K/K) from σ) x

/-- Henselian-DVF specialization of the target-free Route-P core. -/
theorem decompositionSubgroup_eq_top_of_henselianDVF_restrictUnique
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (huniq :
      ∀ (E : IntermediateField K (AlgebraicClosure K))
        [FiniteDimensional K E] [Algebra.IsSeparable K E],
          ∀ (B : ValuationSubring E)
            [_root_.Valuation.HasExtension F.valuation B.valuation],
              (RamificationTheory.ValuationSubring.restrictIntermediateField A E) = B) :
    decompositionSubgroup K A = ⊤ :=
  decompositionSubgroup_eq_top_of_finite_separable_restrictUnique
    (K := K) (v := F.valuation) (A := A) (huniq := huniq)

/-- Absolute decomposition is top once every finite separable intermediate
extension valuation ring is integral over the base valuation ring.

This is the target-free form of the Henselian finite-level frontier: the
remaining local Henselian argument only has to prove the displayed integrality
predicate, without packaging the restricted valuation rings as `HenselianDVF`s. -/
theorem decompositionSubgroup_eq_top_of_finite_separable_integral
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (hintegral :
      ∀ (E : IntermediateField K (AlgebraicClosure K))
        [FiniteDimensional K E] [Algebra.IsSeparable K E],
          ∀ (B : ValuationSubring E)
            [_root_.Valuation.HasExtension F.valuation B.valuation],
              Algebra.IsIntegral F.valuation.valuationSubring
                B.valuation.valuationSubring) :
    decompositionSubgroup K A = ⊤ := by
  apply decompositionSubgroup_eq_top_of_henselianDVF_restrictUnique
    (F := F) (A := A)
  intro E _ _ B _
  have hAExt : _root_.Valuation.HasExtension F.valuation
      ((RamificationTheory.ValuationSubring.restrictIntermediateField A E)).valuation :=
    RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension
      (v := F.valuation) (A := A) E
  have hAInt : Algebra.IsIntegral F.valuation.valuationSubring
      ((RamificationTheory.ValuationSubring.restrictIntermediateField A
        E)).valuation.valuationSubring :=
    hintegral E ((RamificationTheory.ValuationSubring.restrictIntermediateField A E))
  have hBInt : Algebra.IsIntegral F.valuation.valuationSubring
      B.valuation.valuationSubring :=
    hintegral E B
  have hsub :
      ((RamificationTheory.ValuationSubring.restrictIntermediateField A
        E)).valuation.valuationSubring =
        B.valuation.valuationSubring := by
    ext z
    constructor
    · intro hz
      have hz_int : z ∈ integralClosure F.valuation.valuationSubring E :=
        valuationSubring_mem_integralClosure_of_isIntegral
          (L := E) F.valuation ((RamificationTheory.ValuationSubring.restrictIntermediateField A
            E)).valuation ⟨z, hz⟩
      exact
        integralClosure_mem_valuationSubring_of_hasExtension
          (L := E) F.valuation B.valuation ⟨z, hz_int⟩
    · intro hz
      have hz_int : z ∈ integralClosure F.valuation.valuationSubring E :=
        valuationSubring_mem_integralClosure_of_isIntegral
          (L := E) F.valuation B.valuation ⟨z, hz⟩
      exact
        integralClosure_mem_valuationSubring_of_hasExtension
          (L := E) F.valuation ((RamificationTheory.ValuationSubring.restrictIntermediateField A
            E)).valuation ⟨z, hz_int⟩
  calc
    RamificationTheory.ValuationSubring.restrictIntermediateField A E =
        (RamificationTheory.ValuationSubring.restrictIntermediateField A
          E).valuation.valuationSubring :=
      (ValuationSubring.valuationSubring_valuation _).symm
    _ = B.valuation.valuationSubring := hsub
    _ = B := ValuationSubring.valuationSubring_valuation B

/-- Absolute decomposition is top once every finite separable intermediate
extension valuation ring is finite over the base valuation ring.

This is the module-finite variant of
`decompositionSubgroup_eq_top_of_finite_separable_integral`; it converts finite
algebra extensions to integral extensions before applying the integral route. -/
theorem decompositionSubgroup_eq_top_of_finite_separable_moduleFinite
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (hfinite :
      ∀ (E : IntermediateField K (AlgebraicClosure K))
        [FiniteDimensional K E] [Algebra.IsSeparable K E],
          ∀ (B : ValuationSubring E)
            [_root_.Valuation.HasExtension F.valuation B.valuation],
              Module.Finite F.valuation.valuationSubring
                B.valuation.valuationSubring) :
    decompositionSubgroup K A = ⊤ :=
  decompositionSubgroup_eq_top_of_finite_separable_integral
    (K := K) F A
    (by
      intro E _ _ B _
      let : Module.Finite F.valuation.valuationSubring
          B.valuation.valuationSubring :=
        hfinite E B
      infer_instance)

/-- Absolute decomposition is top once every finite separable intermediate
restriction is supplied as a Henselian-DVF finite-level unique extension. -/
theorem decompositionSubgroup_eq_top_of_finite_separable_henselianUnique
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (huniq :
      ∀ (E : IntermediateField K (AlgebraicClosure K))
        [FiniteDimensional K E] [Algebra.IsSeparable K E],
          ∃ target : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, w} E,
            target.valuation.valuationSubring =
              (RamificationTheory.ValuationSubring.restrictIntermediateField A E) ∧
              HasUniqueValuationExtension.{u, v, u, w, u}
                F target) :
    decompositionSubgroup K A = ⊤ := by
  apply decompositionSubgroup_eq_top_of_finite_separable_restrictUnique
    (v := F.valuation) (A := A)
  intro E _ _ B _
  rcases huniq E with ⟨target, hA, htargetUnique⟩
  have htarget :
      target.valuation.valuationSubring = B := by
    have hsub :=
      valuationSubring_eq_of_hasUniqueValuationExtension
        F target htargetUnique B.valuation
    simpa [ValuationSubring.valuationSubring_valuation] using hsub
  exact hA.symm.trans htarget

/-- Plan-facing name for the absolute Henselian-DVF power route.  The finite
separable level Henselian-DVF targets and unique-extension proofs remain
explicit because constructing them is the remaining local finite-extension
frontier. -/
theorem decompositionSubgroup_eq_top_of_henselianDVF_powerRoute
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (huniq :
      ∀ (E : IntermediateField K (AlgebraicClosure K))
        [FiniteDimensional K E] [Algebra.IsSeparable K E],
          ∃ target : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, w} E,
            target.valuation.valuationSubring =
              (RamificationTheory.ValuationSubring.restrictIntermediateField A E) ∧
              HasUniqueValuationExtension.{u, v, u, w, u}
                F target) :
    decompositionSubgroup K A = ⊤ :=
  decompositionSubgroup_eq_top_of_finite_separable_henselianUnique
    (K := K) F A huniq

/-- If every absolute automorphism stabilizes the chosen valuation subring, the
absolute decomposition group is all of `G_K`. -/
theorem decompositionSubgroup_eq_top_of_forall_smul_eq
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : ∀ σ : Field.absoluteGaloisGroup K, σ • A = A) :
    decompositionSubgroup K A = ⊤ :=
  (decompositionSubgroup_eq_top_iff_forall_smul_eq (K := K) A).2 hA

/-- Moving the chosen valuation subring by an absolute Galois element conjugates
the corresponding absolute decomposition subgroup. -/
theorem decompositionSubgroup_pointwise_smul
    (A : ValuationSubring (AlgebraicClosure K))
    (σ : Field.absoluteGaloisGroup K) :
    decompositionSubgroup K (σ • A) =
      Subgroup.map (MulAut.conj σ).toMonoidHom
        (decompositionSubgroup K A) := by
  ext τ
  change τ ∈ MulAction.stabilizer (Field.absoluteGaloisGroup K) (σ • A) ↔
    τ ∈ Subgroup.map (MulAut.conj σ).toMonoidHom
      (MulAction.stabilizer (Field.absoluteGaloisGroup K) A)
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hτ
    refine ⟨σ⁻¹ * τ * σ, ?_, ?_⟩
    · change (σ⁻¹ * τ * σ) • A = A
      calc
        (σ⁻¹ * τ * σ) • A = σ⁻¹ • (τ • (σ • A)) := by
          simp [smul_smul, mul_assoc]
        _ = σ⁻¹ • (σ • A) := by rw [hτ]
        _ = A := by simp [smul_smul]
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨η, hη, rfl⟩
    change η • A = A at hη
    calc
      (MulAut.conj σ η) • (σ • A) =
          σ • (η • (σ⁻¹ • (σ • A))) := by
        simp [MulAut.conj_apply, smul_smul, mul_assoc]
      _ = σ • (η • A) := by simp [smul_smul]
      _ = σ • A := by rw [hη]

/-- The absolute inertia subgroup attached to a chosen valuation subring of the
algebraic closure. -/
noncomputable abbrev inertiaSubgroup
    (A : ValuationSubring (AlgebraicClosure K)) :
    Subgroup (decompositionSubgroup K A) :=
  A.inertiaSubgroup K

/-- The absolute decomposition-group action on the residue field of the chosen
valuation subring. -/
noncomputable def decompositionResidueAction
    (A : ValuationSubring (AlgebraicClosure K)) :
    decompositionSubgroup K A →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut
    (decompositionSubgroup K A) (IsLocalRing.ResidueField A)

/-- Absolute inertia is the kernel of the decomposition action on the residue
field of the chosen valuation subring. -/
theorem inertiaSubgroup_eq_ker
    (A : ValuationSubring (AlgebraicClosure K)) :
    inertiaSubgroup K A =
      MonoidHom.ker (decompositionResidueAction K A) :=
  rfl

/-- States the theorem `decompositionResidueAction_ker`. -/
theorem decompositionResidueAction_ker
    (A : ValuationSubring (AlgebraicClosure K)) :
    MonoidHom.ker (decompositionResidueAction K A) =
      inertiaSubgroup K A :=
  rfl

/-- Provides the instance `inertiaSubgroup_normal`. -/
instance inertiaSubgroup_normal
    (A : ValuationSubring (AlgebraicClosure K)) :
    (inertiaSubgroup K A).Normal := by
  rw [inertiaSubgroup_eq_ker]
  infer_instance

/-- Membership in absolute inertia is triviality of the induced residue-field
automorphism. -/
@[simp] theorem mem_inertiaSubgroup_iff
    (A : ValuationSubring (AlgebraicClosure K))
    (σ : decompositionSubgroup K A) :
    σ ∈ inertiaSubgroup K A ↔
      decompositionResidueAction K A σ = 1 := by
  rw [inertiaSubgroup_eq_ker, MonoidHom.mem_ker]

/-- Exactness at the absolute decomposition subgroup for
`I_A -> D_A -> Aut(k_A)`. -/
theorem inertiaSubtype_mulExact_decompositionResidueAction
    (A : ValuationSubring (AlgebraicClosure K)) :
    Function.MulExact
      (inertiaSubgroup K A).subtype
      (decompositionResidueAction K A) := by
  rw [MonoidHom.mulExact_iff, decompositionResidueAction_ker]
  exact (Subgroup.range_subtype _).symm

/-- Absolute inertia as a subgroup of the ambient absolute Galois group. -/
noncomputable abbrev inertiaSubgroupInAbsolute
    (A : ValuationSubring (AlgebraicClosure K)) :
    Subgroup (Field.absoluteGaloisGroup K) :=
  Subgroup.map (decompositionSubgroup K A).subtype (inertiaSubgroup K A)

/-- Ambient absolute inertia lies in absolute decomposition. -/
theorem inertiaSubgroupInAbsolute_le_decompositionSubgroup
    (A : ValuationSubring (AlgebraicClosure K)) :
    inertiaSubgroupInAbsolute K A ≤ decompositionSubgroup K A := by
  rintro σ ⟨τ, _hτ, rfl⟩
  exact τ.property

/-- Ambient absolute inertia membership is decomposition membership plus
triviality of the induced residue-field automorphism. -/
theorem mem_inertiaSubgroupInAbsolute_iff
    (A : ValuationSubring (AlgebraicClosure K))
    (σ : Field.absoluteGaloisGroup K) :
    σ ∈ inertiaSubgroupInAbsolute K A ↔
      ∃ hσ : σ ∈ decompositionSubgroup K A,
        decompositionResidueAction K A ⟨σ, hσ⟩ = 1 := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ.property, (mem_inertiaSubgroup_iff K A τ).1 hτ⟩
  · rintro ⟨hσ, hres⟩
    refine ⟨⟨σ, hσ⟩, ?_, rfl⟩
    exact (mem_inertiaSubgroup_iff K A ⟨σ, hσ⟩).2 hres

/-- Ambient absolute inertia is the whole decomposition subgroup exactly when
the decomposition residue action is trivial. -/
theorem inertiaSubgroupInAbsolute_eq_decompositionSubgroup_iff
    (A : ValuationSubring (AlgebraicClosure K)) :
    inertiaSubgroupInAbsolute K A = decompositionSubgroup K A ↔
      decompositionResidueAction K A = 1 := by
  constructor
  · intro hA
    ext σ x
    have hmem : (σ : Field.absoluteGaloisGroup K) ∈
        inertiaSubgroupInAbsolute K A := by
      rw [hA]
      exact σ.property
    rcases (mem_inertiaSubgroupInAbsolute_iff K A σ).1 hmem with
      ⟨hσ, hres⟩
    have hσeq :
        (⟨(σ : Field.absoluteGaloisGroup K), hσ⟩ :
          decompositionSubgroup K A) = σ := by
      ext
      rfl
    have hresx := congrArg
      (fun e : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A =>
        e x) hres
    simpa [hσeq] using hresx
  · intro hA
    ext σ
    constructor
    · intro hσ
      exact (inertiaSubgroupInAbsolute_le_decompositionSubgroup (K := K) A) hσ
    · intro hσ
      rw [mem_inertiaSubgroupInAbsolute_iff]
      exact ⟨hσ, by rw [hA]; rfl⟩

/-- Ambient absolute inertia is trivial exactly when the decomposition residue
action is injective. -/
theorem inertiaSubgroupInAbsolute_eq_bot_iff_decompositionResidueAction_injective
    (A : ValuationSubring (AlgebraicClosure K)) :
    inertiaSubgroupInAbsolute K A = ⊥ ↔
      Function.Injective (decompositionResidueAction K A) := by
  rw [← MonoidHom.ker_eq_bot_iff (decompositionResidueAction K A),
    decompositionResidueAction_ker]
  constructor
  · intro hA
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := inertiaSubgroup K A)
      (f := (decompositionSubgroup K A).subtype)
      (by
        intro x y hxy
        exact Subtype.ext hxy)).1
        (by simpa [inertiaSubgroupInAbsolute] using hA)
  · intro hA
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := inertiaSubgroup K A)
      (f := (decompositionSubgroup K A).subtype)
      (by
        intro x y hxy
        exact Subtype.ext hxy)).2 hA

/-- Ambient absolute inertia is all of `G_K` exactly when decomposition is all
of `G_K` and the decomposition residue action is trivial. -/
theorem inertiaSubgroupInAbsolute_eq_top_iff
    (A : ValuationSubring (AlgebraicClosure K)) :
    inertiaSubgroupInAbsolute K A = ⊤ ↔
      decompositionSubgroup K A = ⊤ ∧ decompositionResidueAction K A = 1 := by
  constructor
  · intro hA
    have hD : decompositionSubgroup K A = ⊤ := by
      rw [eq_top_iff]
      intro σ _hσ
      exact (inertiaSubgroupInAbsolute_le_decompositionSubgroup (K := K) A) (by
        rw [hA]
        exact Subgroup.mem_top σ)
    refine ⟨hD, ?_⟩
    rw [← inertiaSubgroupInAbsolute_eq_decompositionSubgroup_iff (K := K) A]
    rw [hA, hD]
  · rintro ⟨hD, hres⟩
    rw [eq_top_iff]
    intro σ _hσ
    rw [mem_inertiaSubgroupInAbsolute_iff]
    have hσ : σ ∈ decompositionSubgroup K A := by
      rw [hD]
      exact Subgroup.mem_top σ
    exact ⟨hσ, by rw [hres]; rfl⟩

/-- If the absolute decomposition subgroup is all of `G_K`, every absolute
automorphism can be viewed as a decomposition element. -/
def toDecompositionSubgroupOfEqTop
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    Field.absoluteGaloisGroup K →*
      decompositionSubgroup K A where
  toFun σ := ⟨σ, by rw [hA]; exact Subgroup.mem_top σ⟩
  map_one' := by
    ext
    rfl
  map_mul' _ _ := by
    ext
    rfl

/-- States the theorem `toDecompositionSubgroupOfEqTop_coe`. -/
@[simp] theorem toDecompositionSubgroupOfEqTop_coe
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    (toDecompositionSubgroupOfEqTop K A hA σ :
      Field.absoluteGaloisGroup K) = σ :=
  rfl

/-- When `D_A = G_K`, the decomposition residue action becomes an ambient
absolute Galois action on the residue field. -/
noncomputable def absoluteResidueActionOfDecompositionSubgroupEqTop
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    Field.absoluteGaloisGroup K →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  (decompositionResidueAction K A).comp
    (toDecompositionSubgroupOfEqTop K A hA)

/-- States the theorem `absoluteResidueActionOfDecompositionSubgroupEqTop_apply`. -/
@[simp] theorem absoluteResidueActionOfDecompositionSubgroupEqTop_apply
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    absoluteResidueActionOfDecompositionSubgroupEqTop K A hA σ =
      decompositionResidueAction K A
        (toDecompositionSubgroupOfEqTop K A hA σ) :=
  rfl

/-- Under `D_A = G_K`, the ambient residue-action range is the decomposition
residue-action range. -/
theorem absoluteResidueActionOfDecompositionSubgroupEqTop_range
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    MonoidHom.range
        (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA) =
      MonoidHom.range (decompositionResidueAction K A) := by
  ext φ
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨toDecompositionSubgroupOfEqTop K A hA σ, rfl⟩
  · rintro ⟨σ, rfl⟩
    refine ⟨(σ : Field.absoluteGaloisGroup K), ?_⟩
    have hσeq :
        toDecompositionSubgroupOfEqTop K A hA
            (σ : Field.absoluteGaloisGroup K) = σ := by
      ext
      rfl
    simp [absoluteResidueActionOfDecompositionSubgroupEqTop, hσeq]

/-- The ambient residue action attached to `D_A = G_K` has kernel equal to
ambient absolute inertia. -/
theorem absoluteResidueActionOfDecompositionSubgroupEqTop_ker
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    MonoidHom.ker
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA) =
        inertiaSubgroupInAbsolute K A := by
  ext σ
  rw [MonoidHom.mem_ker, mem_inertiaSubgroupInAbsolute_iff]
  constructor
  · intro hσ
    refine ⟨by rw [hA]; exact Subgroup.mem_top σ, ?_⟩
    simpa [absoluteResidueActionOfDecompositionSubgroupEqTop,
      toDecompositionSubgroupOfEqTop] using hσ
  · rintro ⟨hσD, hres⟩
    have hσeq :
        (toDecompositionSubgroupOfEqTop K A hA σ :
          decompositionSubgroup K A) = ⟨σ, hσD⟩ := by
      ext
      rfl
    simpa [absoluteResidueActionOfDecompositionSubgroupEqTop, hσeq] using hres

/-- Exactness at `G_K` for the ambient residue action under `D_A = G_K`. -/
theorem inertiaSubgroupInAbsoluteSubtype_mulExact_absoluteResidueActionOfDecompositionSubgroupEqTop
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    Function.MulExact
      (inertiaSubgroupInAbsolute K A).subtype
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA) := by
  rw [MonoidHom.mulExact_iff,
    absoluteResidueActionOfDecompositionSubgroupEqTop_ker]
  exact (Subgroup.range_subtype _).symm

/-- Proof-dependent Henselian-DVF-facing absolute residue action.  The
Henselian top theorem is kept as an explicit argument; once
`decompositionSubgroup_eq_top_of_henselianDVF` is available, this is the stable
name used downstream without changing the residue-action target. -/
noncomputable def absoluteResidueActionOfHenselianDVF
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (hA : decompositionSubgroup K A = ⊤) :
    MonoidHom (Field.absoluteGaloisGroup K)
      (RingEquiv (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)) :=
  absoluteResidueActionOfDecompositionSubgroupEqTop K A hA

/-- States the theorem `absoluteResidueActionOfHenselianDVF_apply`. -/
@[simp] theorem absoluteResidueActionOfHenselianDVF_apply
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (hA : decompositionSubgroup K A = ⊤)
    (sigma : Field.absoluteGaloisGroup K) :
    absoluteResidueActionOfHenselianDVF K F A hA sigma =
      absoluteResidueActionOfDecompositionSubgroupEqTop K A hA sigma :=
  rfl

/-- Kernel of the proof-dependent Henselian-DVF-facing absolute residue action. -/
theorem absoluteResidueActionOfHenselianDVF_ker
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (hA : decompositionSubgroup K A = ⊤) :
    MonoidHom.ker (absoluteResidueActionOfHenselianDVF K F A hA) =
      inertiaSubgroupInAbsolute K A :=
  absoluteResidueActionOfDecompositionSubgroupEqTop_ker K A hA

/-- Exactness for the proof-dependent Henselian-DVF-facing absolute residue
action. -/
theorem inertiaSubgroupInAbsoluteSubtype_mulExact_absoluteResidueActionOfHenselianDVF
    (F : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, v} K)
    (A : ValuationSubring (AlgebraicClosure K))
    [_root_.Valuation.HasExtension F.valuation A.valuation]
    (hA : decompositionSubgroup K A = ⊤) :
    Function.MulExact
      (inertiaSubgroupInAbsolute K A).subtype
      (absoluteResidueActionOfHenselianDVF K F A hA) := by
  rw [MonoidHom.mulExact_iff,
    absoluteResidueActionOfHenselianDVF_ker]
  exact (Subgroup.range_subtype _).symm

/-- Kernel membership for the ambient residue action under `D_A = G_K`. -/
theorem absoluteResidueActionOfDecompositionSubgroupEqTop_eq_one_iff_mem_inertia
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    absoluteResidueActionOfDecompositionSubgroupEqTop K A hA σ = 1 ↔
      σ ∈ inertiaSubgroupInAbsolute K A := by
  rw [← MonoidHom.mem_ker,
    absoluteResidueActionOfDecompositionSubgroupEqTop_ker]

/-- Equality of ambient residue actions, in right-quotient form. -/
theorem absoluteResidueActionOfDecompositionSubgroupEqTop_eq_iff_div_mem_inertia
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ τ : Field.absoluteGaloisGroup K) :
    absoluteResidueActionOfDecompositionSubgroupEqTop K A hA σ =
        absoluteResidueActionOfDecompositionSubgroupEqTop K A hA τ ↔
      σ / τ ∈ inertiaSubgroupInAbsolute K A := by
  rw [← absoluteResidueActionOfDecompositionSubgroupEqTop_ker
      (K := K) A hA]
  exact (MonoidHom.div_mem_ker_iff
    (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA)).symm

/-- Under `D_A = G_K`, ambient absolute inertia is normal in `G_K`. -/
theorem inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    (inertiaSubgroupInAbsolute K A).Normal := by
  rw [← absoluteResidueActionOfDecompositionSubgroupEqTop_ker K A hA]
  infer_instance

/-- Equality of ambient residue actions, in left-quotient form. -/
theorem absoluteResidueActionOfDecompositionSubgroupEqTop_eq_iff_inv_mul_mem_inertia
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ τ : Field.absoluteGaloisGroup K) :
    absoluteResidueActionOfDecompositionSubgroupEqTop K A hA σ =
        absoluteResidueActionOfDecompositionSubgroupEqTop K A hA τ ↔
      τ⁻¹ * σ ∈ inertiaSubgroupInAbsolute K A := by
  rw [absoluteResidueActionOfDecompositionSubgroupEqTop_eq_iff_div_mem_inertia
    (K := K) A hA σ τ]
  simpa [div_eq_mul_inv] using
    ((inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top
        (K := K) A hA).mem_comm_iff (a := σ) (b := τ⁻¹))

/-- The ambient residue action under `D_A = G_K` is injective exactly when
ambient inertia is trivial. -/
theorem absoluteResidueActionOfDecompositionSubgroupEqTop_injective_iff_inertia_eq_bot
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    Function.Injective
        (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA) ↔
      inertiaSubgroupInAbsolute K A = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff
    (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA),
    absoluteResidueActionOfDecompositionSubgroupEqTop_ker]

/-- Under `D_A = G_K`, quotienting the absolute Galois group by the kernel of
the ambient residue action gives the range of that action.  The kernel is
identified with ambient inertia by
`absoluteResidueActionOfDecompositionSubgroupEqTop_ker`. -/
noncomputable def absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    Field.absoluteGaloisGroup K ⧸
        MonoidHom.ker
          (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA) ≃*
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).range :=
  QuotientGroup.quotientKerEquivRange
    (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA)

/-- States the theorem
`absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk`. -/
theorem absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop
        K A hA
        (QuotientGroup.mk'
          (MonoidHom.ker
            (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA)) σ) =
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).rangeRestrict
        σ :=
  rfl

/-- Under `D_A = G_K`, quotienting the absolute Galois group by ambient
inertia gives the range of the ambient residue action. -/
noncomputable def absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤) :
    letI : (inertiaSubgroupInAbsolute K A).Normal :=
      inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
    Field.absoluteGaloisGroup K ⧸ inertiaSubgroupInAbsolute K A ≃*
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).range := by
  letI : (inertiaSubgroupInAbsolute K A).Normal :=
    inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
  exact (QuotientGroup.quotientMulEquivOfEq
      (absoluteResidueActionOfDecompositionSubgroupEqTop_ker K A hA).symm).trans
    (absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop K A hA)

/-- States the theorem
`absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk`. -/
theorem absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    letI : (inertiaSubgroupInAbsolute K A).Normal :=
      inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
    absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop
        K A hA
        (QuotientGroup.mk' (inertiaSubgroupInAbsolute K A) σ) =
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).rangeRestrict
        σ := by
  let : (inertiaSubgroupInAbsolute K A).Normal :=
    inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
  change
    absoluteQuotientKernelEquivResidueActionRangeOfDecompositionSubgroupEqTop
        K A hA
        (QuotientGroup.mk'
          (MonoidHom.ker
            (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA)) σ) =
      (absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).rangeRestrict σ
  rfl

/-- States the theorem
`absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop_symm_rangeRestrict`.
-/
@[simp] theorem
  absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop_symm_rangeRestrict
    (A : ValuationSubring (AlgebraicClosure K))
    (hA : decompositionSubgroup K A = ⊤)
    (σ : Field.absoluteGaloisGroup K) :
    letI : (inertiaSubgroupInAbsolute K A).Normal :=
      inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
    (absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop
        K A hA).symm
        ((absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).rangeRestrict
          σ) =
      QuotientGroup.mk' (inertiaSubgroupInAbsolute K A) σ := by
  let : (inertiaSubgroupInAbsolute K A).Normal :=
    inertiaSubgroupInAbsolute_normal_of_decompositionSubgroup_eq_top K A hA
  apply
    (absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop
      K A hA).injective
  rw [absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop_mk]
  exact
    (absoluteQuotientInertiaEquivResidueActionRangeOfDecompositionSubgroupEqTop
      K A hA).apply_symm_apply
      ((absoluteResidueActionOfDecompositionSubgroupEqTop K A hA).rangeRestrict σ)

/-- Absolute decomposition modulo inertia is the range of the residue-field
action. -/
noncomputable def decompositionQuotientInertiaEquivResidueActionRange
    (A : ValuationSubring (AlgebraicClosure K)) :
    decompositionSubgroup K A ⧸ inertiaSubgroup K A ≃*
      (decompositionResidueAction K A).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (decompositionResidueAction_ker K A).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (decompositionResidueAction K A))

/-- States the theorem `decompositionQuotientInertiaEquivResidueActionRange_mk`. -/
theorem decompositionQuotientInertiaEquivResidueActionRange_mk
    (A : ValuationSubring (AlgebraicClosure K))
    (σ : decompositionSubgroup K A) :
    decompositionQuotientInertiaEquivResidueActionRange K A
        (QuotientGroup.mk' (inertiaSubgroup K A) σ) =
      (decompositionResidueAction K A).rangeRestrict σ :=
  rfl

/-- States the theorem `decompositionQuotientInertiaEquivResidueActionRange_symm_rangeRestrict`. -/
@[simp] theorem decompositionQuotientInertiaEquivResidueActionRange_symm_rangeRestrict
    (A : ValuationSubring (AlgebraicClosure K))
    (σ : decompositionSubgroup K A) :
    (decompositionQuotientInertiaEquivResidueActionRange K A).symm
        ((decompositionResidueAction K A).rangeRestrict σ) =
      QuotientGroup.mk' (inertiaSubgroup K A) σ := by
  apply (decompositionQuotientInertiaEquivResidueActionRange K A).injective
  rw [decompositionQuotientInertiaEquivResidueActionRange_mk]
  exact (decompositionQuotientInertiaEquivResidueActionRange K A).apply_symm_apply
    ((decompositionResidueAction K A).rangeRestrict σ)

end AbsoluteRamification

end absoluteGaloisGroup
end Field

end

end RamificationTheory
