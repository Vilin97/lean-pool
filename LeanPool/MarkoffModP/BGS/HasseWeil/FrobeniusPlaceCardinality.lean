/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FinitePlaceFrobeniusFiber

/-!
# Cardinalities of Frobenius place stabilizers

This file supplies the local cardinality identities required by the
Frobenius-coset form of Burnside averaging.

Suppose a place of a relative Galois extension has absolute degree `[S : C]`
and lies above a degree-one place.  Multiplicativity of place degree then says
that its relative inertia degree is `[S : C]`.  The decomposition-group formula
and the finite-field identity

`|Aut_C(S)| = [S : C]`

show that its stabilizer has cardinality

`|restricted quotient kernel| * |Aut_C(S)|`,

provided the restricted quotient kernel is identified with inertia.  Both
finite places and places above infinity are covered, first for the underlying
decomposition groups and then in the restriction-fiber actions used by
`sum_card_fixedBy_quotientFiber_eq_card_ker_of_stabilizer_card`.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (C : Type*) [Field C] [Fintype C]
  [DecidableEq C] [DecidableEq (RatFunc C)]
variable (M : Type*) [Field M] [Algebra (RatFunc C) M]
  [FiniteDimensional (RatFunc C) M]
  [Algebra.IsSeparable (RatFunc C) M]
variable (L : Type*) [Field L] [Algebra (RatFunc C) L]
  [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  [Algebra M L] [IsScalarTower (RatFunc C) M L]
  [IsGalois M L]
variable (S : Type*) [Field S] [Algebra C S]
  [FiniteDimensional C S] [IsGalois C S]

omit [Fintype C] in
/-- A finite place of degree `[S : C]` above a degree-one place has the
decomposition-group cardinality required by Frobenius-coset averaging, once
the restricted constant quotient kernel is identified with inertia. -/
theorem finitePlaceDecompositionGroup_card_eq_restrictedKernel_mul_card_constantAut [Finite C]
    (π : Gal(L/M) →* (S ≃ₐ[C] S))
    (Q : FiniteExtensionFinitePlace C L)
    (hTop : finiteExtensionPlaceDegree C L (.inl Q) = Module.finrank C S)
    (hBase : finiteExtensionPlaceDegree C M
      (.inl (finitePlaceUnder C M L Q)) = 1)
    (hker :
      letI := finiteIntegralClosureGalAction C M L
      (π.comp (finitePlaceDecompositionGroup C M L Q).subtype).ker =
        Q.asIdeal.inertia (finitePlaceDecompositionGroup C M L Q)) :
    Nat.card (finitePlaceDecompositionGroup C M L Q) =
      Nat.card
          (π.comp (finitePlaceDecompositionGroup C M L Q).subtype).ker *
        Nat.card (S ≃ₐ[C] S) := by
  let : Fintype C := Fintype.ofFinite C
  let := finiteIntegralClosureGalAction C M L
  have hrelative :
      finitePlaceRelativeInertiaDeg C M L Q = Module.finrank C S := by
    have hdegree :=
      finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg C M L Q
    rw [hTop, hBase, one_mul] at hdegree
    exact hdegree.symm
  have hkernel :
      Nat.card
          (π.comp (finitePlaceDecompositionGroup C M L Q).subtype).ker =
        finitePlaceRelativeRamificationIdx C M L Q := by
    rw [hker]
    change Nat.card
        ((Q.asIdeal.inertia Gal(L/M)).subgroupOf
          (finitePlaceDecompositionGroup C M L Q)) = _
    calc
      Nat.card
          ((Q.asIdeal.inertia Gal(L/M)).subgroupOf
            (finitePlaceDecompositionGroup C M L Q)) =
          Nat.card (Q.asIdeal.inertia Gal(L/M)) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            (Ideal.inertia_le_stabilizer (M := Gal(L/M)) Q.asIdeal)).toEquiv
      _ = finitePlaceRelativeRamificationIdx C M L Q :=
        finitePlaceInertiaGroup_card_eq_ramificationIdx C M L Q
  rw [finitePlaceDecompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg,
    ← hkernel, hrelative, ← IsGalois.card_aut_eq_finrank C S]

omit [Fintype C] in
/-- The corresponding decomposition-group cardinality identity for a place
above infinity. -/
theorem infinityPlaceDecompositionGroup_card_eq_restrictedKernel_mul_card_constantAut [Finite C]
    (π : Gal(L/M) →* (S ≃ₐ[C] S))
    (Q : FiniteExtensionInfinityPlace C L)
    (hTop : finiteExtensionPlaceDegree C L (.inr Q) = Module.finrank C S)
    (hBase : finiteExtensionPlaceDegree C M
      (.inr (infinityPlaceUnder C M L Q)) = 1)
    (hker :
      letI := infinityIntegralClosureGalAction C M L
      (π.comp (infinityPlaceDecompositionGroup C M L Q).subtype).ker =
        Q.1.inertia (infinityPlaceDecompositionGroup C M L Q)) :
    Nat.card (infinityPlaceDecompositionGroup C M L Q) =
      Nat.card
          (π.comp (infinityPlaceDecompositionGroup C M L Q).subtype).ker *
        Nat.card (S ≃ₐ[C] S) := by
  let : Fintype C := Fintype.ofFinite C
  let := infinityIntegralClosureGalAction C M L
  have hrelative :
      infinityPlaceRelativeInertiaDeg C M L Q = Module.finrank C S := by
    have hdegree :=
      finiteExtensionPlaceDegree_inr_eq_mul_relativeInertiaDeg C M L Q
    rw [hTop, hBase, one_mul] at hdegree
    exact hdegree.symm
  have hkernel :
      Nat.card
          (π.comp (infinityPlaceDecompositionGroup C M L Q).subtype).ker =
        infinityPlaceRelativeRamificationIdx C M L Q := by
    rw [hker]
    change Nat.card
        ((Q.1.inertia Gal(L/M)).subgroupOf
          (infinityPlaceDecompositionGroup C M L Q)) = _
    calc
      Nat.card
          ((Q.1.inertia Gal(L/M)).subgroupOf
            (infinityPlaceDecompositionGroup C M L Q)) =
          Nat.card (Q.1.inertia Gal(L/M)) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            (Ideal.inertia_le_stabilizer (M := Gal(L/M)) Q.1)).toEquiv
      _ = infinityPlaceRelativeRamificationIdx C M L Q :=
        infinityPlaceInertiaGroup_card_eq_ramificationIdx C M L Q
  rw [infinityPlaceDecompositionGroup_card_eq_ramificationIdx_mul_inertiaDeg,
    ← hkernel, hrelative, ← IsGalois.card_aut_eq_finrank C S]

omit [Fintype C] in
/-- Restriction-fiber form of the finite-place cardinality identity.  Its
conclusion is exactly the stabilizer hypothesis consumed by the cardinality
form of Frobenius-coset Burnside averaging. -/
theorem finitePlaceUnderFiber_stabilizer_card_eq_restrictedKernel_mul_card_constantAut [Finite C]
    (π : Gal(L/M) →* (S ≃ₐ[C] S))
    (P : FiniteExtensionFinitePlace C M)
    (Q : FinitePlaceUnderFiber C M L P)
    (hTop : finiteExtensionPlaceDegree C L (.inl Q.1) = Module.finrank C S)
    (hBase : finiteExtensionPlaceDegree C M (.inl P) = 1)
    (hker :
      letI := finiteIntegralClosureGalAction C M L
      letI := finitePlaceUnderFiberGalAction C M L P
      (π.comp (MulAction.stabilizer Gal(L/M) Q).subtype).ker =
        Q.1.asIdeal.inertia (MulAction.stabilizer Gal(L/M) Q)) :
    letI := finiteIntegralClosureGalAction C M L
    letI := finitePlaceUnderFiberGalAction C M L P
    Nat.card (MulAction.stabilizer Gal(L/M) Q) =
      Nat.card
          (π.comp (MulAction.stabilizer Gal(L/M) Q).subtype).ker *
        Nat.card (S ≃ₐ[C] S) := by
  let : Fintype C := Fintype.ofFinite C
  let := finiteIntegralClosureGalAction C M L
  let := finitePlaceUnderFiberGalAction C M L P
  have hBase' : finiteExtensionPlaceDegree C M
      (.inl (finitePlaceUnder C M L Q.1)) = 1 := by
    rw [Q.2]
    exact hBase
  have hstab :=
    finitePlaceUnderFiber_stabilizer_eq_decompositionGroup C M L P Q
  rw [hstab] at hker ⊢
  exact finitePlaceDecompositionGroup_card_eq_restrictedKernel_mul_card_constantAut
    C M L S π Q.1 hTop hBase' hker

omit [Fintype C] in
/-- Restriction-fiber form of the infinity-place cardinality identity. -/
theorem infinityPlaceUnderFiber_stabilizer_card_eq_restrictedKernel_mul_card_constantAut [Finite C]
    (π : Gal(L/M) →* (S ≃ₐ[C] S))
    (P : FiniteExtensionInfinityPlace C M)
    (Q : InfinityPlaceUnderFiber C M L P)
    (hTop : finiteExtensionPlaceDegree C L (.inr Q.1) = Module.finrank C S)
    (hBase : finiteExtensionPlaceDegree C M (.inr P) = 1)
    (hker :
      letI := infinityIntegralClosureGalAction C M L
      letI := infinityPlaceUnderFiberGalAction C M L P
      (π.comp (MulAction.stabilizer Gal(L/M) Q).subtype).ker =
        Q.1.1.inertia (MulAction.stabilizer Gal(L/M) Q)) :
    letI := infinityIntegralClosureGalAction C M L
    letI := infinityPlaceUnderFiberGalAction C M L P
    Nat.card (MulAction.stabilizer Gal(L/M) Q) =
      Nat.card
          (π.comp (MulAction.stabilizer Gal(L/M) Q).subtype).ker *
        Nat.card (S ≃ₐ[C] S) := by
  let : Fintype C := Fintype.ofFinite C
  let := infinityIntegralClosureGalAction C M L
  let := infinityPlaceUnderFiberGalAction C M L P
  have hBase' : finiteExtensionPlaceDegree C M
      (.inr (infinityPlaceUnder C M L Q.1)) = 1 := by
    rw [Q.2]
    exact hBase
  have hstab :=
    infinityPlaceUnderFiber_stabilizer_eq_decompositionGroup C M L P Q
  rw [hstab] at hker ⊢
  exact infinityPlaceDecompositionGroup_card_eq_restrictedKernel_mul_card_constantAut
    C M L S π Q.1 hTop hBase' hker

end

end BGS.HasseWeil
