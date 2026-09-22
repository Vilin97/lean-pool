/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.TopologyModelTypes
/-!
# Topology of the principal-unit inverse limit

This module identifies first principal units algebraically and topologically with the
inverse limit of their finite principal-unit quotients.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-- Embed `U^1/U^(n+1)` as its class inside `O^*/U^(n+1)`. -/
noncomputable def Internal.principalUnitQuotientCarrierToFull
    (F : CompleteDVF.{u, v} K) (n : ℕ) :
    Internal.principalUnitQuotientCarrier F n →*
      F.valuationSubringˣ ⧸
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1) :=
  ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubgroupClassInQuotient
      1 (n + 1)).subtype.comp
    ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
      F).principalUnitSubquotientEquivClassInQuotientOfLe
      (Nat.le_add_left 1 n)).toMonoidHom

/--
Establishes the identity `principalUnitQuotientCarrierToFull F n
((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk 1 (n + 1) x) =
(QuotientGroup.mk (x : F.valuationSubringˣ) : F.valuationSubringˣ ⧸
(CompleteDVF.higherPrincipalUnitGroup F) (n + 1))`.
-/
@[simp] theorem Internal.principalUnitQuotientCarrierToFull_mk
    (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    principalUnitQuotientCarrierToFull F n
        ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
          1 (n + 1) x) =
      (QuotientGroup.mk (x : F.valuationSubringˣ) :
        F.valuationSubringˣ ⧸
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n +
          1)) := by
  exact
    (higherPrincipalUnitGroup.toPrincipalUnitFiltration
      F).coe_principalUnitSubquotientEquivClassInQuotientOfLe_mk
        (Nat.le_add_left 1 n) x

/--
The specified map is injective: `Function.Injective (principalUnitQuotientCarrierToFull F n)`.
-/
theorem Internal.principalUnitQuotientCarrierToFull_injective
    (F : CompleteDVF.{u, v} K) (n : ℕ) :
    Function.Injective (principalUnitQuotientCarrierToFull F n) := by
  exact Subtype.val_injective.comp
    ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
      F).principalUnitSubquotientEquivClassInQuotientOfLe
        (Nat.le_add_left 1 n)).injective

/-- A first principal unit, viewed as a point of its class inside the full
finite unit quotient. -/
def Internal.principalUnitToClassInFullQuotient
    (F : CompleteDVF.{u, v} K) (n : ℕ) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubgroupClassInQuotient
        1 (n + 1) where
  toFun x :=
    ⟨QuotientGroup.mk (x : F.valuationSubringˣ),
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F).principalUnitSubgroupClassInQuotient_mk_mem
        x.property⟩
  map_one' := by ext; rfl
  map_mul' x y := by ext; rfl

/--
Establishes the identity `((higherPrincipalUnitGroup.toPrincipalUnitFiltration
F).principalUnitSubquotientEquivClassInQuotientOfLe (Nat.le_add_left 1 n)).symm
(principalUnitToClassInFullQuotient F n x) = (higherPrincipalUnitGroup.toPrincipalUnitFiltration
F).principalUnitSubquotientMk 1 (n + 1) x`.
-/
@[simp] theorem Internal.principalUnitQuotientCarrierEquivClass_symm_toClass
    (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
      F).principalUnitSubquotientEquivClassInQuotientOfLe
          (Nat.le_add_left 1 n)).symm
        (principalUnitToClassInFullQuotient F n x) =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
        1 (n + 1) x := by
  apply ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
    F).principalUnitSubquotientEquivClassInQuotientOfLe
      (Nat.le_add_left 1 n)).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  exact ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
    F).coe_principalUnitSubquotientEquivClassInQuotientOfLe_mk
      (Nat.le_add_left 1 n) x).symm

/--
Establishes the identity `higherUnitQuotientTransition F hmn (principalUnitQuotientCarrierToFull F
n q) = principalUnitQuotientCarrierToFull F m (principalUnitQuotientCarrierTransition F hmn q)`.
-/
theorem Internal.principalUnitQuotientCarrierToFull_transition
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n)
    (q : Internal.principalUnitQuotientCarrier F n) :
    higherUnitQuotientTransition F hmn
        (principalUnitQuotientCarrierToFull F n q) =
      principalUnitQuotientCarrierToFull F m
        (principalUnitQuotientCarrierTransition F hmn q) := by
  refine
    AntitoneSubgroupFiltration.principalUnitSubquotient.inductionOn
      (motive := fun q =>
        higherUnitQuotientTransition F hmn
            (principalUnitQuotientCarrierToFull F n q) =
          principalUnitQuotientCarrierToFull F m
            (principalUnitQuotientCarrierTransition F hmn q))
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) 1 (n + 1) q ?_
  intro x
  exact (congrArg (higherUnitQuotientTransition F hmn)
    (principalUnitQuotientCarrierToFull_mk F n x)).trans
      (principalUnitQuotientCarrierToFull_mk F m x).symm

/-- Forget that every coordinate is represented by a first principal unit. -/
noncomputable def Internal.principalUnitInverseLimitCarrierToFull
    (F : CompleteDVF.{u, v} K) :
    Internal.principalUnitInverseLimitCarrier F →*
      Internal.higherUnitInverseLimitCarrier F where
  toFun q :=
    ⟨fun n => principalUnitQuotientCarrierToFull F n (q.1 n), by
      intro m n hmn
      rw [principalUnitQuotientCarrierToFull_transition, q.2 hmn]⟩
  map_one' := by
    apply Subtype.ext
    funext n
    change principalUnitQuotientCarrierToFull F n 1 = 1
    exact map_one _
  map_mul' q r := by
    apply Subtype.ext
    funext n
    change principalUnitQuotientCarrierToFull F n (q.1 n * r.1 n) =
      principalUnitQuotientCarrierToFull F n (q.1 n) *
        principalUnitQuotientCarrierToFull F n (r.1 n)
    exact map_mul _ _ _

/-- Canonical carrier map from `U^1` to its level-quotient limit. -/
def Internal.principalUnitToInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Internal.principalUnitInverseLimitCarrier F where
  toFun x :=
    ⟨fun n =>
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
          1 (n + 1) x, by
      intro m n hmn
      exact principalUnitQuotientCarrierTransition_mk F hmn x⟩
  map_one' := by ext n; rfl
  map_mul' x y := by ext n; rfl

/--
Establishes the identity `principalUnitInverseLimitCarrierToFull F
(principalUnitToInverseLimitCarrier F x) = unitsEquivHigherUnitQuotientInverseLimit F (x :
F.valuationSubringˣ)`.
-/
theorem Internal.principalUnitInverseLimitCarrierToFull_to
    (F : CompleteDVF.{u, v} K) (x :
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    principalUnitInverseLimitCarrierToFull F
        (principalUnitToInverseLimitCarrier F x) =
      unitsEquivHigherUnitQuotientInverseLimit F
        (x : F.valuationSubringˣ) := by
  ext n
  simp only [compatibleGroupFamiliesEval_apply]
  rw [unitsEquivHigherUnitQuotientInverseLimit_apply]
  exact principalUnitQuotientCarrierToFull_mk F n x

/-- Establishes the identity `principalUnitQuotientCarrierToFull F 0 q = 1`. -/
theorem Internal.principalUnitQuotientCarrierToFull_zero_eq_one
    (F : CompleteDVF.{u, v} K)
    (q : Internal.principalUnitQuotientCarrier F 0) :
    principalUnitQuotientCarrierToFull F 0 q = 1 := by
  refine
    AntitoneSubgroupFiltration.principalUnitSubquotient.inductionOn
      (motive := fun q => principalUnitQuotientCarrierToFull F 0 q = 1)
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) 1 1 q ?_
  intro x
  exact (principalUnitQuotientCarrierToFull_mk F 0 x).trans
    ((QuotientGroup.eq_one_iff (x : F.valuationSubringˣ)).2 x.property)

/-- Recover a first principal unit from a compatible family of its finite
classes, by applying the adic inverse-limit equivalence to the underlying full unit family. -/
noncomputable def Internal.principalUnitInverseLimitCarrierInv
    (F : CompleteDVF.{u, v} K)
    (q : Internal.principalUnitInverseLimitCarrier F) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 := by
  let e := unitsEquivHigherUnitQuotientInverseLimit F
  let qfull := principalUnitInverseLimitCarrierToFull F q
  refine ⟨e.symm qfull, ?_⟩
  rw [← QuotientGroup.eq_one_iff]
  calc
    (QuotientGroup.mk (e.symm qfull) :
        F.valuationSubringˣ ⧸
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) =
        (e (e.symm qfull)).1 0 :=
      (unitsEquivHigherUnitQuotientInverseLimit_apply F (e.symm qfull) 0).symm
    _ = qfull.1 0 := by rw [e.apply_symm_apply]
    _ = 1 := principalUnitQuotientCarrierToFull_zero_eq_one F (q.1 0)

/--
Establishes the identity `unitsEquivHigherUnitQuotientInverseLimit F
(principalUnitInverseLimitCarrierInv F q : F.valuationSubringˣ) =
principalUnitInverseLimitCarrierToFull F q`.
-/
theorem Internal.unitsEquiv_principalUnitInverseLimitCarrierInv
    (F : CompleteDVF.{u, v} K)
    (q : Internal.principalUnitInverseLimitCarrier F) :
    unitsEquivHigherUnitQuotientInverseLimit F
        (principalUnitInverseLimitCarrierInv F q : F.valuationSubringˣ) =
      principalUnitInverseLimitCarrierToFull F q := by
  exact (unitsEquivHigherUnitQuotientInverseLimit F).apply_symm_apply _

/-- Algebraic restriction of the adic inverse-limit equivalence:
`U^1` is the inverse limit of `U^1/U^(n+1)`. -/
noncomputable def Internal.principalUnitMulEquivInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Internal.principalUnitInverseLimitCarrier F where
  toFun := principalUnitToInverseLimitCarrier F
  invFun := principalUnitInverseLimitCarrierInv F
  left_inv x := by
    apply Subtype.ext
    change
      (unitsEquivHigherUnitQuotientInverseLimit F).symm
          (principalUnitInverseLimitCarrierToFull F
            (principalUnitToInverseLimitCarrier F x)) =
        (x : F.valuationSubringˣ)
    rw [principalUnitInverseLimitCarrierToFull_to]
    exact (unitsEquivHigherUnitQuotientInverseLimit F).symm_apply_apply _
  right_inv q := by
    ext n
    apply principalUnitQuotientCarrierToFull_injective F n
    change
      principalUnitQuotientCarrierToFull F n
          ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
            1 (n + 1) (principalUnitInverseLimitCarrierInv F q)) =
        principalUnitQuotientCarrierToFull F n (q.1 n)
    rw [principalUnitQuotientCarrierToFull_mk]
    calc
      (QuotientGroup.mk
          (principalUnitInverseLimitCarrierInv F q : F.valuationSubringˣ) :
          F.valuationSubringˣ ⧸
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n
            + 1)) =
          (unitsEquivHigherUnitQuotientInverseLimit F
            (principalUnitInverseLimitCarrierInv F q :
              F.valuationSubringˣ)).1 n :=
        (unitsEquivHigherUnitQuotientInverseLimit_apply F _ n).symm
      _ = (principalUnitInverseLimitCarrierToFull F q).1 n := by
        rw [unitsEquiv_principalUnitInverseLimitCarrierInv]
      _ = principalUnitQuotientCarrierToFull F n (q.1 n) := rfl
  map_mul' x y := by
    exact (principalUnitToInverseLimitCarrier F).map_mul x y

/-- Topological restriction of the adic inverse-limit equivalence: with the adic topology on
`U^1` and
the product topology of the discrete quotient coordinates,
`U^1` is homeomorphic to `lim U^1/U^(n+1)`. -/
noncomputable def Internal.principalUnitHomeomorphInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
      fun _ => ⊥
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃ₜ
      Internal.principalUnitInverseLimitCarrier F := by
  let pi := chosenPrincipalUnitPadicUniformizer F
  letI : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal pi 1).adicTopology
  letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  letI : (n : ℕ) → DiscreteTopology (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⟨rfl⟩
  let fullQuotientTopology (n : ℕ) : TopologicalSpace
      (F.valuationSubringˣ ⧸
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
          (n + 1)) := ⊥
  letI : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
          (n + 1)) :=
    fullQuotientTopology
  letI : (n : ℕ) → DiscreteTopology
      (F.valuationSubringˣ ⧸
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
          (n + 1)) :=
    fun _ => ⟨rfl⟩
  let e := principalUnitMulEquivInverseLimitCarrier F
  let hfull := Internal.unitsHomeomorphHigherUnitQuotientInverseLimit F
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change Continuous fun x => e x
    exact Continuous.subtype_mk
      (continuous_pi fun n => by
        change Continuous fun x :
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 =>
          (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
            1 (n + 1) x
        have hfullCoord : Continuous fun x :
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 =>
            (QuotientGroup.mk (x : F.valuationSubringˣ) :
              F.valuationSubringˣ ⧸
                (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
                  (n + 1)) := by
          have hsub : Continuous fun x :
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 =>
              (x : F.valuationSubringˣ) := continuous_subtype_val
          have hcoord : Continuous fun z : Internal.higherUnitInverseLimitCarrier F =>
              z.1 n :=
            (continuous_apply n).comp continuous_subtype_val
          have h := hcoord.comp (hfull.continuous.comp hsub)
          convert h using 1
          funext x
          have hx :=
            Internal.unitsHomeomorphHigherUnitQuotientInverseLimit_apply
              F (x : F.valuationSubringˣ) n
          simpa only [hfull, Function.comp_apply] using hx.symm
        let f := principalUnitQuotientCarrierToFull F n
        let decode :
            (F.valuationSubringˣ ⧸
              (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
                (n + 1)) →
              Internal.principalUnitQuotientCarrier F n :=
          Function.invFun f
        have hdecode : Continuous decode :=
          continuous_of_discreteTopology
        have hstage : Continuous fun x :
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 =>
            decode
              (QuotientGroup.mk (x : F.valuationSubringˣ) :
                F.valuationSubringˣ ⧸
                  (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
                    (n + 1)) :=
          hdecode.comp hfullCoord
        convert hstage using 1
        funext x
        symm
        change Function.invFun f
            (QuotientGroup.mk (x : F.valuationSubringˣ) :
              F.valuationSubringˣ ⧸
                (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
                  (n + 1)) =
          (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
            1 (n + 1) x
        rw [← principalUnitQuotientCarrierToFull_mk F n x]
        exact Function.leftInverse_invFun
          (principalUnitQuotientCarrierToFull_injective F n) _)
      (fun x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
        1 => by
        intro i j hij
        exact (e x).2 hij)
  · have hToFull : Continuous fun q : Internal.principalUnitInverseLimitCarrier F =>
        principalUnitInverseLimitCarrierToFull F q := by
      exact Continuous.subtype_mk
        (continuous_pi fun n => by
          change Continuous fun q : Internal.principalUnitInverseLimitCarrier F =>
            principalUnitQuotientCarrierToFull F n (q.1 n)
          exact continuous_of_discreteTopology.comp
            ((continuous_apply n).comp continuous_subtype_val))
        (fun q : Internal.principalUnitInverseLimitCarrier F => by
          intro i j hij
          exact (principalUnitInverseLimitCarrierToFull F q).2 hij)
    have hInvFull : Continuous fun q : Internal.principalUnitInverseLimitCarrier F =>
        hfull.symm (principalUnitInverseLimitCarrierToFull F q) :=
      hfull.continuous_symm.comp hToFull
    change Continuous fun q => e.symm q
    exact Continuous.subtype_mk
      (by
        convert hInvFull using 1
        funext q
        change
          (principalUnitInverseLimitCarrierInv F q : F.valuationSubringˣ) =
            hfull.symm (principalUnitInverseLimitCarrierToFull F q)
        apply hfull.injective
        rw [hfull.apply_symm_apply]
        ext n
        change
          (hfull
            (principalUnitInverseLimitCarrierInv F q :
              F.valuationSubringˣ)).1 n =
            (principalUnitInverseLimitCarrierToFull F q).1 n
        calc
          (hfull
              (principalUnitInverseLimitCarrierInv F q :
                F.valuationSubringˣ)).1 n =
              (QuotientGroup.mk
                (principalUnitInverseLimitCarrierInv F q :
                  F.valuationSubringˣ) :
              F.valuationSubringˣ ⧸
                (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
                  (n + 1)) := by
            simpa only [hfull] using
              (Internal.unitsHomeomorphHigherUnitQuotientInverseLimit_apply F
                (principalUnitInverseLimitCarrierInv F q :
                  F.valuationSubringˣ) n)
          _ =
              (unitsEquivHigherUnitQuotientInverseLimit F
                (principalUnitInverseLimitCarrierInv F q :
                  F.valuationSubringˣ)).1 n :=
            (unitsEquivHigherUnitQuotientInverseLimit_apply F _ n).symm
          _ = (principalUnitInverseLimitCarrierToFull F q).1 n := by
            rw [unitsEquiv_principalUnitInverseLimitCarrierInv])
      (fun q : Internal.principalUnitInverseLimitCarrier F => (e.symm q).property)

/--
The defining evaluation formula for `Internal.principalUnitMulEquivInverseLimitCarrier` is
`principalUnitInverseLimitCarrierEval F n (principalUnitMulEquivInverseLimitCarrier F x) =
(higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk 1 (n + 1) x`.
-/
theorem Internal.principalUnitMulEquivInverseLimitCarrier_apply
    (F : CompleteDVF.{u, v} K)
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) (n
      : ℕ) :
    principalUnitInverseLimitCarrierEval F n
        (principalUnitMulEquivInverseLimitCarrier F x) =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
        1 (n + 1) x :=
  rfl



/-- Additive form of the algebraic restriction `U^1 ≃ lim U^1/U^(n+1)`. -/
noncomputable def Internal.principalUnitAddEquivInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) :
    Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) ≃+
      Additive (Internal.principalUnitInverseLimitCarrier F) where
  toFun x := Additive.ofMul
    (principalUnitMulEquivInverseLimitCarrier F (Additive.toMul x))
  invFun x := Additive.ofMul
    ((principalUnitMulEquivInverseLimitCarrier F).symm (Additive.toMul x))
  left_inv x := by
    change Additive.ofMul
        ((principalUnitMulEquivInverseLimitCarrier F).symm
          (principalUnitMulEquivInverseLimitCarrier F (Additive.toMul x))) = x
    rw [(principalUnitMulEquivInverseLimitCarrier F).symm_apply_apply]
    rfl
  right_inv x := by
    change Additive.ofMul
        (principalUnitMulEquivInverseLimitCarrier F
          ((principalUnitMulEquivInverseLimitCarrier F).symm
            (Additive.toMul x))) = x
    rw [(principalUnitMulEquivInverseLimitCarrier F).apply_symm_apply]
    rfl
  map_add' x y := by
    change Additive.ofMul
        (principalUnitMulEquivInverseLimitCarrier F
          (Additive.toMul x * Additive.toMul y)) =
      Additive.ofMul
        (principalUnitMulEquivInverseLimitCarrier F (Additive.toMul x) *
          principalUnitMulEquivInverseLimitCarrier F (Additive.toMul y))
    rw [map_mul]

/-- Additive form of the topological inverse-limit equivalence. -/
noncomputable def Internal.principalUnitAddHomeomorphInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
      fun _ => ⊥
    Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) ≃ₜ
      Additive (Internal.principalUnitInverseLimitCarrier F) :=
  Internal.principalUnitHomeomorphInverseLimitCarrier F

/--
The principal-unit homeomorphism to the inverse-limit carrier has the same underlying map as the
algebraic additive equivalence.
-/
@[simp]
theorem Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply
    (F : CompleteDVF.{u, v} K)
    (x : Additive
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    letI : (n : ℕ) → TopologicalSpace
        (Internal.principalUnitQuotientCarrier F n) := fun _ => ⊥
    Internal.principalUnitAddHomeomorphInverseLimitCarrier F x =
      Internal.principalUnitAddEquivInverseLimitCarrier F x :=
  rfl

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
