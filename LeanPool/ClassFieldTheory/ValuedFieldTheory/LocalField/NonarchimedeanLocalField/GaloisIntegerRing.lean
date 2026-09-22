/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.IsGaloisGroup
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation
/-!
# Galois actions on valuation rings

Restricts Galois automorphisms to valuation rings and transports their action
to ideals, ideal-power quotients, principal units, and successive quotients.
-/
namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- A real Galois automorphism preserves the valuation integer ring when that
ring is the integral closure of the base valuation integer ring.

This is the source-producing replacement for proving integer-ring preservation
from a valuation-invariance certificate: integrality is transported by the
`K`-algebra automorphism, and integral-closure membership brings the element
back to `𝒪[L]`. -/
theorem galoisGroup_mem_integerRing_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : 𝒪[L]) :
    σ (x : L) ∈ 𝒪[L] := by
  have hx : IsIntegral 𝒪[K] ((x : 𝒪[L]) : L) :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2
      ⟨x, rfl⟩
  have hσ : IsIntegral 𝒪[K] (σ ((x : 𝒪[L]) : L)) :=
    IsIntegral.map σ.toAlgHom hx
  rcases (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).1 hσ
    with ⟨y, hy⟩
  exact hy ▸ y.2

/-- Restrict a real Galois automorphism to the valuation integer ring using the
actual integral-closure property of valuation integer rings. -/
def galoisGroupIntegerRingEquivOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    𝒪[L] ≃+* 𝒪[L] where
  toFun x :=
    ⟨σ (x : L), galoisGroup_mem_integerRing_of_isIntegralClosure K L σ x⟩
  invFun x :=
    ⟨σ.symm (x : L), galoisGroup_mem_integerRing_of_isIntegralClosure K L σ.symm x⟩
  left_inv := by
    intro x
    ext
    simp
  right_inv := by
    intro x
    ext
    simp
  map_mul' := by
    intro x y
    ext
    simp
  map_add' := by
    intro x y
    ext
    simp

/-- Restriction sends a field automorphism to the corresponding automorphism of the integral-closure
valuation ring. -/
@[simp]
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_apply
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : 𝒪[L]) :
    ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x : 𝒪[L]) : L) =
      σ (x : L) :=
  rfl

/-- The inverse restriction equivalence extends an integer-ring automorphism to the ambient
field. -/
@[simp]
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_symm_apply
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : 𝒪[L]) :
    (((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).symm x : 𝒪[L]) : L) =
      σ.symm (x : L) :=
  rfl

/-- Real Galois automorphisms act on `𝒪[L]` through the actual integral-closure
restriction. -/
def galoisGroupIntegerRingEquivHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* (𝒪[L] ≃+* 𝒪[L]) where
  toFun := galoisGroupIntegerRingEquivOfIsIntegralClosure K L
  map_one' := by
    ext x
    rfl
  map_mul' := by
    intro σ τ
    ext x
    rfl

/-- The semiring action on the valuation integer ring induced by the actual
integral-closure restriction of `Gal(L / K)`. -/
@[reducible]
def galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    MulSemiringAction (Gal(L / K)) 𝒪[L] :=
  MulSemiringAction.compHom 𝒪[L] (galoisGroupIntegerRingEquivHomOfIsIntegralClosure K L)

/-- Restriction of a Galois automorphism commutes with the inclusion of the integer ring into the
field. -/
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : 𝒪[K]) :
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
        (integerRingMapOfValuationExtension K L x) =
      integerRingMapOfValuationExtension K L x := by
  ext
  change σ (algebraMap K L (x : K)) = algebraMap K L (x : K)
  exact σ.commutes (x : K)

/-- The actual `Gal(L / K)` action on `𝒪[L]` fixes the image of `𝒪[K]`. -/
theorem galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure_integerRingMap
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : 𝒪[K]) :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    σ • integerRingMapOfValuationExtension K L x =
      integerRingMapOfValuationExtension K L x := by
  change galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
      (integerRingMapOfValuationExtension K L x) =
    integerRingMapOfValuationExtension K L x
  exact galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap K L σ x

/-- The actual integral-closure action commutes with the canonical
`𝒪[K]`-scalar action on `𝒪[L]`. -/
theorem galoisGroupIntegerRingSMulCommClassOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    SMulCommClass (Gal(L / K)) 𝒪[K] 𝒪[L] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  refine ⟨?_⟩
  intro σ x y
  rw [Algebra.smul_def, Algebra.smul_def]
  change galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
      (algebraMap 𝒪[K] 𝒪[L] x * y) =
    algebraMap 𝒪[K] 𝒪[L] x *
      galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ y
  rw [map_mul]
  have hx : galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
      (algebraMap 𝒪[K] 𝒪[L] x) = algebraMap 𝒪[K] 𝒪[L] x := by
    simpa [integerRingMapOfValuationExtension] using
      galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap K L σ x
  rw [hx]

/-- The actual integral-closure action is compatible with the field-level
`Gal(L / K)` action after coercion to `L`. -/
theorem galoisGroupIntegerRingFieldSMulDistribClassOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    SMulDistribClass (Gal(L / K)) 𝒪[L] L := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  refine ⟨?_⟩
  intro σ r s
  change σ (((r : 𝒪[L]) : L) * s) =
    ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r : 𝒪[L]) : L) * σ s
  rw [map_mul]
  rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]

/-- The actual integral-closure action on valuation integer rings is a mathlib
Galois group.  This is the source-producing version of the ring-level Galois
input needed for inertia/cardinality arguments. -/
theorem galoisGroupIntegerRing_isGaloisGroup_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    IsGaloisGroup (Gal(L / K)) 𝒪[K] 𝒪[L] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRingFieldSMulDistribClassOfIsIntegralClosure K L
  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] :=
    IsIntegralClosure.isIntegral_algebra 𝒪[K] L
  exact IsGaloisGroup.of_isFractionRing (Gal(L / K)) 𝒪[K] 𝒪[L] K L

/-- The ideal action induced by the actual integral-closure restriction. -/
@[reducible]
def galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    DistribMulAction (Gal(L / K)) (Ideal 𝒪[L]) := by
  letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  exact Ideal.pointwiseDistribMulAction

/-- The multiplicative ideal action induced by the actual integral-closure
restriction. -/
@[reducible]
def galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    MulAction (Gal(L / K)) (Ideal 𝒪[L]) := by
  exact (galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure K L).toMulAction

/-- The Galois action on an integral-closure valuation ring preserves its maximal ideal. -/
theorem galoisGroupIntegerRingAction_map_maximalIdeal_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) :
    Ideal.map (@MulSemiringAction.toRingHom (Gal(L / K)) _ 𝒪[L] _
        (galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L) σ)
      (𝓂[L] : Ideal 𝒪[L]) =
      (𝓂[L] : Ideal 𝒪[L]) := by
  change Ideal.map
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toRingHom
      (𝓂[L] : Ideal 𝒪[L]) =
    (𝓂[L] : Ideal 𝒪[L])
  exact integerRingEquiv_map_maximalIdeal L
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- Every Galois automorphism belongs to the stabilizer of the maximal ideal of the integral-closure
valuation ring. -/
theorem galoisGroupIntegerRingAction_mem_maximalIdeal_stabilizer_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) :
    σ ∈ @MulAction.stabilizer (Gal(L / K)) (Ideal 𝒪[L]) _
      (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
      (𝓂[L] : Ideal 𝒪[L]) := by
  rw [@MulAction.mem_stabilizer_iff (Gal(L / K)) (Ideal 𝒪[L]) _
    (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)]
  change Ideal.map (@MulSemiringAction.toRingHom (Gal(L / K)) _ 𝒪[L] _
      (galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L) σ)
        (𝓂[L] : Ideal 𝒪[L]) =
    (𝓂[L] : Ideal 𝒪[L])
  exact galoisGroupIntegerRingAction_map_maximalIdeal_of_isIntegralClosure K L σ

/-- Real Galois automorphisms, viewed inside the maximal-ideal stabilizer, using
the actual integral-closure restriction. -/
def galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* @MulAction.stabilizer (Gal(L / K)) (Ideal 𝒪[L]) _
      (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
      (𝓂[L] : Ideal 𝒪[L]) where
  toFun σ :=
    ⟨σ, galoisGroupIntegerRingAction_mem_maximalIdeal_stabilizer_of_isIntegralClosure K L σ⟩
  map_one' := by
    ext
    rfl
  map_mul' σ τ := by
    ext
    rfl

/-- Actual integral-closure real Galois action on the `n`-th principal-unit
group. -/
def galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) :
    principalUnits L n ≃* principalUnits L n :=
  principalUnitsMapEquivOfIntegerRingEquiv L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- The induced equivalence on principal units applies the restricted Galois automorphism to the
underlying unit. -/
theorem galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure_apply
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) (u : principalUnits L n) :
    ((galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u :
        principalUnits L n) : 𝒪[L]ˣ) =
      Units.mapEquiv
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u.1 :=
  rfl

/-- Integral-closure Galois action on principal units as a group
homomorphism. -/
def galoisGroupPrincipalUnitsMapEquivHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    Gal(L / K) →* (principalUnits L n ≃* principalUnits L n) where
  toFun := galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n
  map_one' := by
    ext u
    rfl
  map_mul' := by
    intro σ τ
    ext u
    rfl

/-- Integral-closure Galois action on `𝓂_L^n/𝓂_L^(n+1)`. -/
def galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) :
    MaximalIdealPowSuccQuot L n ≃+ MaximalIdealPowSuccQuot L n :=
  maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- The Galois equivalence on a successive maximal-ideal quotient maps the class of a representative
to the class of its conjugate. -/
theorem galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure_mk
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K))
    (a : ((𝓂[L] ^ n : Ideal 𝒪[L]) : Type u)) :
    galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n σ
        (maximalIdealPowSuccQuotMk L n a) =
      maximalIdealPowSuccQuotMk L n
        (maximalIdealPowMapEquivOfIntegerRingEquiv L n
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) a) :=
  maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv_mk L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) a

/-- Integral-closure Galois action on maximal-ideal graded pieces. -/
def galoisGroupMaximalIdealPowSuccQuotMapEquivHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    Gal(L / K) →*
      Multiplicative
        (AddAut (MaximalIdealPowSuccQuot L n)) where
  toFun σ := Multiplicative.ofAdd
    (galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n σ)
  map_one' := by
    ext x
    refine MaximalIdealPowSuccQuot.inductionOn n
      (motive := fun x =>
        galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure
            K L n 1 x = x)
      x ?_
    intro a
    rw [galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure_mk]
    rfl
  map_mul' := by
    intro σ τ
    ext x
    refine MaximalIdealPowSuccQuot.inductionOn n
      (motive := fun x =>
        galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure
            K L n (σ * τ) x =
          galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure
            K L n σ
            (galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure
              K L n τ x))
      x ?_
    intro a
    rw [galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure_mk]
    rw [galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure_mk,
      galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure_mk]
    rfl

/-- Integral-closure Galois action on maximal-ideal graded pieces,
packaged as an additive action. -/
@[reducible]
def galoisGroupMaximalIdealPowSuccQuotDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    DistribMulAction (Gal(L / K)) (MaximalIdealPowSuccQuot L n) where
  smul σ x := galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n σ x
  one_smul := by
    intro x
    change galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n 1 x = x
    have h := congrArg (fun e :
        Multiplicative (AddAut (MaximalIdealPowSuccQuot L n)) =>
          Multiplicative.toAdd e x)
      (map_one (galoisGroupMaximalIdealPowSuccQuotMapEquivHomOfIsIntegralClosure K L n))
    exact h
  mul_smul := by
    intro σ τ x
    change galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n (σ * τ) x =
      galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n σ
        (galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n τ x)
    have h := congrArg (fun e :
        Multiplicative (AddAut (MaximalIdealPowSuccQuot L n)) =>
          Multiplicative.toAdd e x)
      (map_mul (galoisGroupMaximalIdealPowSuccQuotMapEquivHomOfIsIntegralClosure K L n) σ τ)
    exact h
  smul_zero := by
    intro σ
    exact map_zero (galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n σ)
  smul_add := by
    intro σ x y
    exact map_add (galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n σ) x y

/-- The distributive Galois action on a successive maximal-ideal quotient is computed by conjugating
representatives. -/
theorem galoisGroupMaximalIdealPowSuccQuotDistribMulActionOfIsIntegralClosure_smul
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) (x : MaximalIdealPowSuccQuot L n) :
    letI := galoisGroupMaximalIdealPowSuccQuotDistribMulActionOfIsIntegralClosure K L n
    σ • x = galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n σ x :=
  rfl

/-- Actual integral-closure real Galois action on the multiplicative form of
maximal-ideal graded pieces. -/
@[reducible]
def galoisGroupMaximalIdealPowSuccQuotMultiplicativeMulDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    MulDistribMulAction (Gal(L / K)) (Multiplicative (MaximalIdealPowSuccQuot L n)) where
  smul σ x :=
    maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv L n
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) x
  one_smul := by
    intro x
    change maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv L n
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L 1) x = x
    have h := congrArg (fun e :
        Multiplicative (AddAut (MaximalIdealPowSuccQuot L n)) =>
          Multiplicative.toAdd e (Multiplicative.toAdd x))
      (map_one (galoisGroupMaximalIdealPowSuccQuotMapEquivHomOfIsIntegralClosure K L n))
    exact congrArg Multiplicative.ofAdd h
  mul_smul := by
    intro σ τ x
    change maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv L n
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L (σ * τ)) x =
      maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv L n
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)
        (maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv L n
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L τ) x)
    have h := congrArg (fun e :
        Multiplicative (AddAut (MaximalIdealPowSuccQuot L n)) =>
          Multiplicative.toAdd e (Multiplicative.toAdd x))
      (map_mul (galoisGroupMaximalIdealPowSuccQuotMapEquivHomOfIsIntegralClosure K L n) σ τ)
    exact congrArg Multiplicative.ofAdd h
  smul_mul := by
    intro σ x y
    exact map_mul
      (maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv L n
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)) x y
  smul_one := by
    intro σ
    exact map_one
      (maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv L n
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ))

/-- After multiplicative re-encoding, the Galois action on a maximal-ideal quotient is still induced
by conjugation. -/
theorem galoisGroupMaximalIdealPowSuccQuotMultiplicativeMulDistribMulActionOfIsIntegralClosure_smul
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K))
    (x : Multiplicative (MaximalIdealPowSuccQuot L n)) :
    letI := galoisGroupMaximalIdealPowSuccQuotMultiplicativeMulDistribMulActionOfIsIntegralClosure
      K L n
    σ • x = maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv L n
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) x :=
  rfl

/-- Actual integral-closure action on `U^n/U^(n+1)`. -/
def galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) :
    PrincipalUnitsSuccQuot L n ≃* PrincipalUnitsSuccQuot L n :=
  principalUnitsSuccQuotMapEquivOfIntegerRingEquiv L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- The Galois equivalence on a successive principal-unit quotient maps each class to the class of
its conjugate. -/
theorem galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure_apply
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) (u : principalUnits L n) :
    galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ
        (QuotientGroup.mk u) =
      QuotientGroup.mk
        (galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ u) :=
  rfl

/-- Actual integral-closure real Galois action on successive principal-unit
quotients as a group homomorphism. -/
def galoisGroupPrincipalUnitsSuccQuotMapEquivHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    Gal(L / K) →* (PrincipalUnitsSuccQuot L n ≃* PrincipalUnitsSuccQuot L n) where
  toFun := galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro u
    rfl
  map_mul' := by
    intro σ τ
    ext x
    refine QuotientGroup.induction_on x ?_
    intro u
    rfl

/-- Actual integral-closure real Galois action on successive principal-unit
quotients, packaged as the multiplicative action required by low-degree
Herbrand quotients. -/
@[reducible]
def galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    MulDistribMulAction (Gal(L / K)) (PrincipalUnitsSuccQuot L n) where
  smul σ x := galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ x
  one_smul := by
    intro x
    change galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n 1 x = x
    have h := congrArg (fun e : PrincipalUnitsSuccQuot L n ≃*
        PrincipalUnitsSuccQuot L n => e x)
      (map_one (galoisGroupPrincipalUnitsSuccQuotMapEquivHomOfIsIntegralClosure K L n))
    exact h
  mul_smul := by
    intro σ τ x
    change galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n (σ * τ) x =
      galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ
        (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n τ x)
    have h := congrArg (fun e : PrincipalUnitsSuccQuot L n ≃*
        PrincipalUnitsSuccQuot L n => e x)
      (map_mul (galoisGroupPrincipalUnitsSuccQuotMapEquivHomOfIsIntegralClosure K L n) σ τ)
    exact h
  smul_mul := by
    intro σ x y
    exact map_mul (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ) x y
  smul_one := by
    intro σ
    exact map_one (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ)

/-- The packaged integral-closure action is the quotient map equivalence action
pointwise. -/
theorem galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure_smul
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) (x : PrincipalUnitsSuccQuot L n) :
    letI := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
    σ • x = galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ x :=
  rfl

/-- Actual integral-closure real Galois action on the additive form of
successive principal-unit quotients. -/
@[reducible]
def galoisGroupPrincipalUnitsSuccQuotAddDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    DistribMulAction (Gal(L / K)) (Additive (PrincipalUnitsSuccQuot L n)) where
  smul σ x :=
    Additive.ofMul
      (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ
        (Additive.toMul x))
  one_smul := by
    intro x
    change Additive.ofMul
        (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n 1
          (Additive.toMul x)) = Additive.ofMul (Additive.toMul x)
    exact congrArg Additive.ofMul
      (congrArg (fun e : PrincipalUnitsSuccQuot L n ≃*
          PrincipalUnitsSuccQuot L n => e (Additive.toMul x))
        (map_one (galoisGroupPrincipalUnitsSuccQuotMapEquivHomOfIsIntegralClosure K L n)))
  mul_smul := by
    intro σ τ x
    change Additive.ofMul
        (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n (σ * τ)
          (Additive.toMul x)) =
      Additive.ofMul
        (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ
          (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n τ
            (Additive.toMul x)))
    exact congrArg Additive.ofMul
      (congrArg (fun e : PrincipalUnitsSuccQuot L n ≃*
          PrincipalUnitsSuccQuot L n => e (Additive.toMul x))
        (map_mul (galoisGroupPrincipalUnitsSuccQuotMapEquivHomOfIsIntegralClosure K L n) σ τ))
  smul_zero := by
    intro σ
    change Additive.ofMul
        (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ 1) =
      Additive.ofMul (1 : PrincipalUnitsSuccQuot L n)
    exact congrArg Additive.ofMul
      (map_one (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ))
  smul_add := by
    intro σ x y
    change Additive.ofMul
        (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ
          (Additive.toMul (x + y))) =
      Additive.ofMul
        (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ
            (Additive.toMul x) *
          galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ
            (Additive.toMul y))
    rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl]
    rw [map_mul]

/-- The additive Galois action on a successive principal-unit quotient is induced by conjugation of
representatives. -/
theorem galoisGroupPrincipalUnitsSuccQuotAddDistribMulActionOfIsIntegralClosure_smul
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) (x : Additive (PrincipalUnitsSuccQuot L n)) :
    letI := galoisGroupPrincipalUnitsSuccQuotAddDistribMulActionOfIsIntegralClosure K L n
    σ • x = Additive.ofMul
      (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ
        (Additive.toMul x)) :=
  rfl

/-- The comparison from a maximal-ideal quotient to a principal-unit quotient intertwines the Galois
actions. -/
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_galoisGroup_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (hn : 1 ≤ n) (σ : Gal(L/K))
    (x : MaximalIdealPowSuccQuot L n) :
    galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ
        (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn x) =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn
        (galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n σ x) :=
  principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_integerRingEquiv L n hn
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) x

/-- The additive comparison between maximal-ideal and principal-unit quotients is Galois
equivariant. -/
theorem principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_galoisGroup_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (hn : 1 ≤ n) (σ : Gal(L/K))
    (x : MaximalIdealPowSuccQuot L n) :
    Additive.ofMul
        (galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure K L n σ
          (principalUnitsSuccQuotOfMaximalIdealPowSuccQuot L n hn x)) =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd L n hn
        (galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n σ x) := by
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_galoisGroup_of_isIntegralClosure]
  rfl

/-- Real Galois equivariance of the additive associated-graded comparison,
with both sides using the packaged additive actions. -/
theorem maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot_galoisGroup_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (hn : 1 ≤ n) (σ : Gal(L/K))
    (x : MaximalIdealPowSuccQuot L n) :
    letI := galoisGroupMaximalIdealPowSuccQuotDistribMulActionOfIsIntegralClosure K L n
    letI := galoisGroupPrincipalUnitsSuccQuotAddDistribMulActionOfIsIntegralClosure K L n
    σ • (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot L n hn x) =
      maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot L n hn (σ • x) := by
  change principalUnitsSuccQuotAddEquivOfIntegerRingEquiv L n
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)
        (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot L n hn x) =
      maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot L n hn
        (galoisGroupMaximalIdealPowSuccQuotMapEquivOfIsIntegralClosure K L n σ x)
  exact maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot_integerRingEquiv L n hn
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) x

/-- Real Galois equivariance of the multiplicative associated-graded
comparison, with both sides using the multiplicative packaged actions. -/
theorem maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot_galoisGroup_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (hn : 1 ≤ n) (σ : Gal(L/K))
    (x : Multiplicative (MaximalIdealPowSuccQuot L n)) :
    letI :=
      galoisGroupMaximalIdealPowSuccQuotMultiplicativeMulDistribMulActionOfIsIntegralClosure
        K L n
    letI := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
    σ • (maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot L n hn x) =
      maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot L n hn (σ • x) := by
  change principalUnitsSuccQuotMapEquivOfIntegerRingEquiv L n
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)
        (maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot L n hn x) =
      maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot L n hn
        (maximalIdealPowSuccQuotMultiplicativeMapEquivOfIntegerRingEquiv L n
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) x)
  exact maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot_integerRingEquiv L n hn
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) x

/-- Actual integral-closure first-order expansion of the real Galois product
attached to a principal-unit representative. -/
theorem galoisGroup_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    (Finset.univ.prod fun σ : Gal(L / K) =>
        1 + galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) - 1 -
      (Finset.univ.sum fun σ : Gal(L / K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ∈
        (𝓂[L] ^ (n + 1) : Ideal 𝒪[L]) := by
  classical
  refine finset_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ L
    (Finset.univ : Finset (Gal(L / K))) n hn
    (fun σ => galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ?_
  intro σ _
  exact (integerRingEquiv_mem_maximalIdeal_pow L
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) n (a : 𝒪[L])).2 a.2

end
end LocalFieldTheory
