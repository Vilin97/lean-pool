/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionInfinityPlaceSplittingMultiplicity

/-!
# Absolute degrees of constant-extension places at infinity

This file compares the degree of an infinity place in the original constant
field presentation with its degree after extending the constants.  Both
degrees are computed from the same reciprocal-normalization residue field, so
the comparison is just the residue-field dimension tower.
-/

open scoped Polynomial TensorProduct nonZeroDivisors

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier IsDedekindDomain


/-- A ring equivalence between finite field extensions of a finite field
preserves their dimensions, even when it is not presented as an algebra
equivalence. -/
private theorem finrank_eq_of_finite_ringEquiv
    (K E F : Type*) [Field K] [Fintype K]
    [Field E] [Field F] [Algebra K E] [Algebra K F]
    [Finite E] [Finite F] (e : E ≃+* F) :
    Module.finrank K E = Module.finrank K F := by
  let : Fintype E := Fintype.ofFinite E
  let : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card E = Fintype.card F :=
    Fintype.card_congr e.toEquiv
  rw [Module.card_eq_pow_finrank (K := K) (V := E),
    Module.card_eq_pow_finrank (K := K) (V := F)] at hcard
  exact Nat.pow_right_injective
    (show 2 ≤ Fintype.card K from Fintype.one_lt_card) hcard

/-- Arithmetic cancellation recovering a relative residue degree from the
two absolute degree formulas. -/
private theorem eq_div_gcd_of_mul_eq_mul_div_gcd
    (r d f : ℕ) (hd : 0 < d)
    (h : d * f = r * (d / Nat.gcd r d)) :
    f = r / Nat.gcd r d := by
  apply Nat.eq_of_mul_eq_mul_left hd
  calc
    d * f = r * (d / Nat.gcd r d) := h
    _ = (Nat.gcd r d * (r / Nat.gcd r d)) *
          (d / Nat.gcd r d) := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left r d)]
    _ = (Nat.gcd r d * (d / Nat.gcd r d)) *
          (r / Nat.gcd r d) := by ac_rfl
    _ = d * (r / Nat.gcd r d) := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right r d)]

/-- Arithmetic cancellation recovering the number of split places after the
relative residue degree is known. -/
private theorem eq_gcd_of_mul_div_gcd_eq
    (r d a : ℕ) (hr : 0 < r)
    (h : a * (r / Nat.gcd r d) = r) :
    a = Nat.gcd r d := by
  have hquot : 0 < r / Nat.gcd r d :=
    Nat.div_pos
      (Nat.le_of_dvd hr (Nat.gcd_dvd_left r d))
      (Nat.gcd_pos_of_pos_left d hr)
  apply Nat.eq_of_mul_eq_mul_right hquot
  calc
    a * (r / Nat.gcd r d) = r := h
    _ = Nat.gcd r d * (r / Nat.gcd r d) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left r d)).symm

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance (priority := 10000) infinityDegreeTowerDecidableEqBase :
    DecidableEq C :=
  infinityBridgeDecidableEqConstants C

local instance (priority := 10000) infinityDegreeTowerDecidableEqRatFuncBase :
    DecidableEq (RatFunc C) :=
  infinityBridgeDecidableEqRatFuncConstants C

local instance (priority := 10000) infinityDegreeTowerDecidableEqConstants :
    DecidableEq S :=
  infinityBridgeDecidableEqConstants S

local instance (priority := 10000)
    infinityDegreeTowerDecidableEqRatFuncConstants :
    DecidableEq (RatFunc S) :=
  infinityBridgeDecidableEqRatFuncConstants S

@[reducible] local instance infinityDegreeTowerBaseConstantAlgebra :
    Algebra C N :=
  infinityConstantAlgebra C N

local instance infinityDegreeTowerBaseRatFuncTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- The degree over the original constants of a presented infinity place is
the constant-field degree times the degree of its upstairs `S`-place. -/
theorem exactConstantExtensionPresentedInfinityPlace_degree_baseChange
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    finiteExtensionPlaceDegree C (ExactConstantExtension C N S)
        (.inr (exactConstantExtensionPresentedInfinityPlaceEquiv
          C S N hExact q)) =
      Module.finrank C S *
        finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
          (.inr (exactConstantExtensionUpstairsInfinityPlace
            C S N hExact q.1 q.2)) := by
  let : DecidableEq C := infinityBridgeDecidableEqConstants C
  let : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  let : DecidableEq S := infinityBridgeDecidableEqConstants S
  let : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc S)
      (ExactConstantExtension C N S) :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S)
      (ExactConstantExtension C N S) :=
    isSeparable_over_extendedRatFunc C S N hExact
  let : Fintype S := Fintype.ofFinite S
  let : Finite q.1.asIdeal.ResidueField :=
    exactConstantExtensionInfinityTensorResidueField_finite
      C S N hExact q.1 q.2
  let : q.1.asIdeal.IsMaximal :=
    exactConstantExtensionInfinityTensorIdeal_isMaximal
      C S N hExact q.1 q.2
  let QC := exactConstantExtensionPresentedInfinityPlaceEquiv
    C S N hExact q
  let QS := exactConstantExtensionUpstairsInfinityPlace
    C S N hExact q.1 q.2
  let BC := RatFuncInfinityIntegralClosure C
    (ExactConstantExtension C N S)
  let BS := RatFuncInfinityIntegralClosure S
    (ExactConstantExtension C N S)
  let : Algebra C BC :=
    onePointInfinityClosureConstantAlgebra C
      (ExactConstantExtension C N S)
  let : Algebra S BS :=
    onePointInfinityClosureConstantAlgebra S
      (ExactConstantExtension C N S)
  let : Algebra C QC.1.ResidueField := by infer_instance
  let : Algebra S QS.1.ResidueField := by infer_instance
  let eC := exactConstantExtensionPresentedInfinityResidueFieldRingEquiv
    C S N hExact q
  let : Finite QC.1.ResidueField :=
    Finite.of_injective eC.symm eC.symm.injective
  let : Finite QS.1.ResidueField :=
    exactConstantExtensionUpstairsInfinityResidueField_finite
      C S N hExact q.1 q.2
  have hC : Module.finrank C q.1.asIdeal.ResidueField =
      Module.finrank C QC.1.ResidueField :=
    finrank_eq_of_finite_ringEquiv C q.1.asIdeal.ResidueField
      QC.1.ResidueField eC
  have hS : Module.finrank S q.1.asIdeal.ResidueField =
      Module.finrank S QS.1.ResidueField :=
    finrank_eq_of_finite_ringEquiv S q.1.asIdeal.ResidueField
      QS.1.ResidueField
      (exactConstantExtensionUpstairsResidueFieldRingEquiv
        C S N hExact q.1 q.2)
  rw [finiteExtensionInfinityPlace_degree_eq_finrank_residueField C
      (ExactConstantExtension C N S) QC,
    finiteExtensionInfinityPlace_degree_eq_finrank_residueField S
      (ExactConstantExtension C N S) QS]
  calc
    Module.finrank C QC.1.ResidueField =
        Module.finrank C q.1.asIdeal.ResidueField := hC.symm
    _ = Module.finrank C S *
        Module.finrank S q.1.asIdeal.ResidueField :=
      (Module.finrank_mul_finrank C S q.1.asIdeal.ResidueField).symm
    _ = Module.finrank C S * Module.finrank S QS.1.ResidueField := by
      rw [hS]

/-- The relative residue degree over the original function field is the
constant extension degree divided by the same gcd that controls splitting. -/
theorem exactConstantExtensionPresentedInfinityPlace_relativeInertiaDeg_eq_div_gcd
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionAlgebra C N S
    letI : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module N (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) N
        (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    infinityPlaceRelativeInertiaDeg C N (ExactConstantExtension C N S)
        (exactConstantExtensionPresentedInfinityPlaceEquiv
          C S N hExact q) =
      Module.finrank C S /
        Nat.gcd (Module.finrank C S)
          (finiteExtensionPlaceDegree C N
            (.inr (exactConstantExtensionDownstairsInfinityPlace
              C S N q.1 q.2))) := by
  let : DecidableEq C := infinityBridgeDecidableEqConstants C
  let : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  let : DecidableEq S := infinityBridgeDecidableEqConstants S
  let : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc S)
      (ExactConstantExtension C N S) :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S)
      (ExactConstantExtension C N S) :=
    isSeparable_over_extendedRatFunc C S N hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let P := exactConstantExtensionDownstairsInfinityPlace
    C S N q.1 q.2
  let Q := exactConstantExtensionPresentedInfinityPlaceEquiv
    C S N hExact q
  let QS := exactConstantExtensionUpstairsInfinityPlace
    C S N hExact q.1 q.2
  let r := Module.finrank C S
  let d := finiteExtensionPlaceDegree C N (.inr P)
  have hUnder : infinityPlaceUnder C N (ExactConstantExtension C N S) Q = P :=
    exactConstantExtensionPresentedInfinityPlaceEquiv_under
      C S N hExact q
  have hUpstairs : finiteExtensionPlaceDegree S
      (ExactConstantExtension C N S) (.inr QS) =
        d / Nat.gcd r d := by
    exact exactConstantExtensionInfinityPlace_degree_eq_div_gcd
      C S N hExact q.1 q.2
  have hTop : finiteExtensionPlaceDegree C
      (ExactConstantExtension C N S) (.inr Q) =
        r * (d / Nat.gcd r d) := by
    exact (exactConstantExtensionPresentedInfinityPlace_degree_baseChange
      C S N hExact q).trans (congrArg (fun n => r * n) hUpstairs)
  have hTower := finiteExtensionPlaceDegree_inr_eq_mul_relativeInertiaDeg
    C N (ExactConstantExtension C N S) Q
  rw [hUnder] at hTower
  have hd : 0 < d := finiteExtensionPlaceDegree_pos C N (.inr P)
  exact eq_div_gcd_of_mul_eq_mul_div_gcd r d _ hd
    (hTower.symm.trans hTop)

/-- A downstairs infinity place of degree `d` has exactly
`gcd([S : C], d)` places above it in an exact extension of constants. -/
theorem exactConstantExtensionInfinityPlace_fiber_card_eq_gcd
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionAlgebra C N S
    letI : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module N (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) N
        (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    letI : IsGalois N (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C N N S hExact
    Fintype.card (InfinityPlaceUnderFiber C N
        (ExactConstantExtension C N S)
        (exactConstantExtensionDownstairsInfinityPlace
          C S N q.1 q.2)) =
      Nat.gcd (Module.finrank C S)
        (finiteExtensionPlaceDegree C N
          (.inr (exactConstantExtensionDownstairsInfinityPlace
            C S N q.1 q.2))) := by
  let : DecidableEq C := infinityBridgeDecidableEqConstants C
  let : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  let : DecidableEq S := infinityBridgeDecidableEqConstants S
  let : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : IsGalois N (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C N N S hExact
  let P := exactConstantExtensionDownstairsInfinityPlace
    C S N q.1 q.2
  let Q := exactConstantExtensionPresentedInfinityPlaceEquiv
    C S N hExact q
  let r := Module.finrank C S
  let d := finiteExtensionPlaceDegree C N (.inr P)
  have hUnder : infinityPlaceUnder C N (ExactConstantExtension C N S) Q = P :=
    exactConstantExtensionPresentedInfinityPlaceEquiv_under
      C S N hExact q
  let Q0 : InfinityPlaceUnderFiber C N
      (ExactConstantExtension C N S) P := ⟨Q, hUnder⟩
  have hFund :=
    infinityPlaceUnderFiber_card_mul_ramificationIdx_mul_inertiaDeg_eq_field_finrank
      C N (ExactConstantExtension C N S) P Q0
  have hRam : infinityPlaceRelativeRamificationIdx C N
      (ExactConstantExtension C N S) Q = 1 :=
    exactConstantExtensionInfinityPlace_ramificationIdx_eq_one
      C S N hExact Q
  have hInertia : infinityPlaceRelativeInertiaDeg C N
      (ExactConstantExtension C N S) Q = r / Nat.gcd r d :=
    exactConstantExtensionPresentedInfinityPlace_relativeInertiaDeg_eq_div_gcd
      C S N hExact q
  rw [exactConstantExtension_finrank C N S] at hFund
  have hCount : Fintype.card (InfinityPlaceUnderFiber C N
      (ExactConstantExtension C N S) P) * (r / Nat.gcd r d) = r := by
    simpa [Q0, hRam, hInertia, r] using hFund
  exact eq_gcd_of_mul_div_gcd_eq r d _ Module.finrank_pos hCount

/-- Restricting the global reciprocal presentation equivalence to a fixed
downstairs infinity place identifies the presented contraction fiber with the
entire actual place-restriction fiber. -/
noncomputable def exactConstantExtensionPresentedInfinityPlaceFiberEquiv :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionAlgebra C N S
    letI : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module N (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) N
        (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    (P : FiniteExtensionInfinityPlace C N) →
    {q : ExactConstantExtensionPresentedInfinityPlace C S N //
      exactConstantExtensionDownstairsInfinityPlace
        C S N q.1 q.2 = P} ≃
      InfinityPlaceUnderFiber C N (ExactConstantExtension C N S) P := by
  letI : DecidableEq C := infinityBridgeDecidableEqConstants C
  letI : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  letI : DecidableEq S := infinityBridgeDecidableEqConstants S
  letI : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  letI : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  letI : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  letI : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  letI : Module N (ExactConstantExtension C N S) := Algebra.toModule
  letI : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  intro P
  let e := exactConstantExtensionPresentedInfinityPlaceEquiv
    C S N hExact
  exact
    { toFun := fun q =>
        ⟨e q.1, by
          rw [exactConstantExtensionPresentedInfinityPlaceEquiv_under]
          exact q.2⟩
      invFun := fun Q =>
        ⟨e.symm Q.1, by
          have hUnder :=
            exactConstantExtensionPresentedInfinityPlaceEquiv_under
              C S N hExact (e.symm Q.1)
          have he : e (e.symm Q.1) = Q.1 := e.apply_symm_apply Q.1
          rw [he] at hUnder
          exact hUnder.symm.trans Q.2⟩
      left_inv := fun q => by
        apply Subtype.ext
        exact e.symm_apply_apply q.1
      right_inv := fun Q => by
        apply Subtype.ext
        exact e.apply_symm_apply Q.1 }

include hExact

/-- The presented reciprocal infinity fiber itself has the standard gcd
cardinality.  This is the presentation-level exhaustiveness form of the
constant-extension splitting law at infinity. -/
theorem exactConstantExtensionPresentedInfinityPlaceFiber_natCard_eq_gcd
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    Nat.card {q' : ExactConstantExtensionPresentedInfinityPlace C S N //
      exactConstantExtensionDownstairsInfinityPlace
          C S N q'.1 q'.2 =
        exactConstantExtensionDownstairsInfinityPlace
          C S N q.1 q.2} =
      Nat.gcd (Module.finrank C S)
        (finiteExtensionPlaceDegree C N
          (.inr (exactConstantExtensionDownstairsInfinityPlace
            C S N q.1 q.2))) := by
  let : DecidableEq C := infinityBridgeDecidableEqConstants C
  let : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  let : DecidableEq S := infinityBridgeDecidableEqConstants S
  let : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : IsGalois N (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C N N S hExact
  let P := exactConstantExtensionDownstairsInfinityPlace
    C S N q.1 q.2
  calc
    Nat.card {q' : ExactConstantExtensionPresentedInfinityPlace C S N //
      exactConstantExtensionDownstairsInfinityPlace C S N q'.1 q'.2 = P} =
        Nat.card (InfinityPlaceUnderFiber C N
          (ExactConstantExtension C N S) P) :=
      Nat.card_congr
        (exactConstantExtensionPresentedInfinityPlaceFiberEquiv
          C S N hExact P)
    _ = Fintype.card (InfinityPlaceUnderFiber C N
          (ExactConstantExtension C N S) P) :=
      Nat.card_eq_fintype_card
    _ = Nat.gcd (Module.finrank C S)
        (finiteExtensionPlaceDegree C N (.inr P)) :=
      exactConstantExtensionInfinityPlace_fiber_card_eq_gcd
        C S N hExact q

end

end BGS.HasseWeil
