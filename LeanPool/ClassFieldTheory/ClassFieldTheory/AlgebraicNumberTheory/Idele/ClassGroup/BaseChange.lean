/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent
import Mathlib.RingTheory.IsTensorProduct
/-!
# Base change of idele-class norms along a pushout square

For a pushout square of finite extensions

```
K  ─→  M
│       │
↓       ↓
L  ─→  N
```

this file constructs the maps on relative ideles and idele classes
that occur after adjoining roots of unity.
Keeping the bottom adele ring fixed makes the norm square an actual
determinant-norm base-change identity.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

universe u

variable
    (K M L N : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]

-- These canonical commutativity proofs are local to the imported tower
-- module; retain them here for the quotient-group instances.
local instance (A B C : Type u) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance (A B : Type u) [Field A] [NumberField A]
    [Field B] [Algebra A B] :
    IsMulCommutative (RelativeIdeleGroup.ClassGroup A B) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance (A : Type u) [Field A] [NumberField A] :
    IsMulCommutative (IdeleClassGroup A) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The scalar extension of the one-step `K`-presentation of the
relative adeles of `L` from the bottom adele ring to
`𝔸_K ⊗[K] M`. -/
abbrev BaseChangedRelativeAdeleRing :=
  RelativeAdeleRing K M ⊗[K] L

/-- For a pushout `N = M ⊗[K] L`, the tower presentation

`(𝔸_K ⊗[K] M) ⊗[M] N`

is canonically the scalar extension

`(𝔸_K ⊗[K] M) ⊗[K] L`.
-/
def pushoutTowerAdeleEquiv :
    TowerRelativeAdeleRing K M N ≃ₐ[RelativeAdeleRing K M]
      BaseChangedRelativeAdeleRing K M L := by
  letI : Algebra N (TowerRelativeAdeleRing K M N) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra L (BaseChangedRelativeAdeleRing K M L) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra.IsPushout K L M N :=
    Algebra.IsPushout.symm
      (inferInstance : Algebra.IsPushout K M L N)
  let e₁ :=
    (Algebra.TensorProduct.commRight
      M N (RelativeAdeleRing K M)).symm
  let e₂ :=
    Algebra.IsPushout.cancelBaseChangeAlg
      K L M N (RelativeAdeleRing K M)
  let e₃ :=
    Algebra.TensorProduct.commRight
      K L (RelativeAdeleRing K M)
  refine
    { e₁.toRingEquiv.trans
        (e₂.toRingEquiv.trans e₃.toRingEquiv) with
      commutes' := ?_ }
  intro a
  simp [e₁, e₂, e₃]

/-- Scalar extension of coefficients from the bottom adele ring to
`𝔸_K ⊗[K] M`, while retaining the top field `L`. -/
def baseChangedRelativeAdeleMap :
    RelativeAdeleRing K L →ₐ[K]
      BaseChangedRelativeAdeleRing K M L :=
  Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := M))
    (AlgHom.id K L)

/-- Inclusion from the relative adeles of `L/K` to the tower
presentation of the relative adeles of `N/M`, induced by the pushout
square. -/
def pushoutTowerAdeleInclusion :
    RelativeAdeleRing K L →+*
      TowerRelativeAdeleRing K M N :=
  (pushoutTowerAdeleEquiv K M L N).symm.toRingHom.comp
    (baseChangedRelativeAdeleMap K M L).toRingHom

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N] in
@[simp]
theorem pushoutTowerAdeleInclusion_tmul
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L) :
    pushoutTowerAdeleInclusion K M L N (a ⊗ₜ[K] x) =
      (a ⊗ₜ[K] (1 : M)) ⊗ₜ[M]
        algebraMap L N x := by
  let : Algebra N (RelativeAdeleRing K M ⊗[M] N) :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra L (RelativeAdeleRing K M ⊗[K] L) :=
    Algebra.TensorProduct.rightAlgebra
  have : Algebra.IsPushout K L M N :=
    Algebra.IsPushout.symm
      (inferInstance : Algebra.IsPushout K M L N)
  change
    Algebra.TensorProduct.commRight M N (RelativeAdeleRing K M)
        ((Algebra.IsPushout.cancelBaseChangeAlg
          K L M N (RelativeAdeleRing K M)).symm
          ((Algebra.TensorProduct.commRight
            K L (RelativeAdeleRing K M)).symm
            ((a ⊗ₜ[K] (1 : M)) ⊗ₜ[K] x))) =
      (a ⊗ₜ[K] (1 : M)) ⊗ₜ[M] algebraMap L N x
  simp only [Algebra.TensorProduct.commRight_symm_tmul,
    Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul,
    Algebra.TensorProduct.commRight_tmul]

/-- Inclusion on unit groups induced by a pushout square of fields. -/
def pushoutTowerIdeleInclusion :
    RelativeIdeleGroup K L →*
      TowerRelativeIdeleGroup K M N :=
  Units.map (pushoutTowerAdeleInclusion K M L N)

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N] in
/-- The pushout inclusion sends a principal idele of `L` to the
principal idele of its image in `N`. -/
@[simp]
theorem pushoutTowerIdeleInclusion_principalIdele
    (x : Lˣ) :
    pushoutTowerIdeleInclusion K M L N
        (RelativeIdeleGroup.principalIdele K L x) =
      TowerRelativeIdeleGroup.principalIdele K M N
        (Units.map (algebraMap L N) x) := by
  apply Units.ext
  change
    pushoutTowerAdeleInclusion K M L N
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] (x : L)) =
      (1 : RelativeAdeleRing K M) ⊗ₜ[M]
        algebraMap L N (x : L)
  rw [pushoutTowerAdeleInclusion_tmul]
  rfl

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional M N]
    [FiniteDimensional L N] in
/-- Determinant norms commute with the pushout inclusion.  This is the
idele-level norm square used after adjoining roots of unity. -/
theorem pushoutTowerIdeleNorm_inclusion
    (a : RelativeIdeleGroup K L) :
    TowerRelativeIdeleGroup.norm K M N
        (pushoutTowerIdeleInclusion K M L N a) =
      RelativeIdeleGroup.inclusion K M
        (RelativeIdeleGroup.norm K L a) := by
  apply Units.ext
  let f :
      NumberField.AdeleRing (𝓞 K) K →ₐ[K]
        RelativeAdeleRing K M :=
    Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := M)
  change
    Algebra.norm (RelativeAdeleRing K M)
        (pushoutTowerAdeleInclusion K M L N
          (a : RelativeAdeleRing K L)) =
      f (Algebra.norm
        (NumberField.AdeleRing (𝓞 K) K)
        (a : RelativeAdeleRing K L))
  calc
    _ = Algebra.norm (RelativeAdeleRing K M)
          (pushoutTowerAdeleEquiv K M L N
            (pushoutTowerAdeleInclusion K M L N
              (a : RelativeAdeleRing K L))) :=
      (Algebra.norm_eq_of_algEquiv
        (pushoutTowerAdeleEquiv K M L N)
        (pushoutTowerAdeleInclusion K M L N
          (a : RelativeAdeleRing K L))).symm
    _ = Algebra.norm (RelativeAdeleRing K M)
          (baseChangedRelativeAdeleMap K M L
            (a : RelativeAdeleRing K L)) := by
      simp [pushoutTowerAdeleInclusion]
    _ = f (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K)
          (a : RelativeAdeleRing K L)) :=
      (map_norm_tensorProduct_baseChange
        (K := K) (L := L) f
        (a : RelativeAdeleRing K L)).symm

/-- The pushout inclusion descended to relative idele class groups. -/
def pushoutTowerClassInclusion :
    RelativeIdeleGroup.ClassGroup K L →*
      TowerRelativeIdeleGroup.ClassGroup K M N :=
  QuotientGroup.map
    (RelativeIdeleGroup.principalSubgroup K L)
    (TowerRelativeIdeleGroup.principalSubgroup K M N)
    (pushoutTowerIdeleInclusion K M L N)
    (by
      rintro _ ⟨x, rfl⟩
      exact
        ⟨Units.map (algebraMap L N) x,
          (pushoutTowerIdeleInclusion_principalIdele
            K M L N x).symm⟩)

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N] in
theorem pushoutTowerClassInclusion_mk
    (a : RelativeIdeleGroup K L) :
    pushoutTowerClassInclusion K M L N
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) =
      QuotientGroup.mk'
        (TowerRelativeIdeleGroup.principalSubgroup K M N)
        (pushoutTowerIdeleInclusion K M L N a) :=
  rfl

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional L N] in
/-- The determinant-norm square after adjoining the pushout field,
descended to actual relative idele class groups. -/
theorem pushoutTowerClassNorm_inclusion
    (c : RelativeIdeleGroup.ClassGroup K L) :
    TowerRelativeIdeleGroup.classNorm K M N
        (pushoutTowerClassInclusion K M L N c) =
      RelativeIdeleGroup.classInclusion K M
        (RelativeIdeleGroup.classNorm K L c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (TowerRelativeIdeleGroup.norm K M N
          (pushoutTowerIdeleInclusion K M L N a)) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (RelativeIdeleGroup.inclusion K M
          (RelativeIdeleGroup.norm K L a))
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K M))
    (pushoutTowerIdeleNorm_inclusion K M L N a)

/-- The map on degree-zero class-norm quotients induced by the pushout
inclusion. -/
def pushoutNormQuotientMap :
    RelativeIdeleGroup.ClassNormQuotient K L →*
      IntermediateClassNormQuotient K M N :=
  QuotientGroup.map
    (RelativeIdeleGroup.classNorm K L).range
    (TowerRelativeIdeleGroup.classNorm K M N).range
    (RelativeIdeleGroup.classInclusion K M)
    (by
      rintro _ ⟨c, rfl⟩
      exact
        ⟨pushoutTowerClassInclusion K M L N c,
          pushoutTowerClassNorm_inclusion K M L N c⟩)

omit [NumberField M] [NumberField L] [NumberField N]
    [FiniteDimensional K M] [FiniteDimensional L N] in
theorem pushoutNormQuotientMap_mk
    (c : IdeleClassGroup K) :
    pushoutNormQuotientMap K M L N
        (QuotientGroup.mk' (RelativeIdeleGroup.classNorm K L).range c) =
      QuotientGroup.mk'
        (TowerRelativeIdeleGroup.classNorm K M N).range
        (RelativeIdeleGroup.classInclusion K M c) :=
  rfl

omit [NumberField M] in
/-- Norm followed by class inclusion is the extension-degree power on
the base idele class group. -/
theorem ideleClassNorm_classInclusion
    (c : IdeleClassGroup K) :
    RelativeIdeleGroup.classNorm K M
        (RelativeIdeleGroup.classInclusion K M c) =
      c ^ Module.finrank K M := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K M
          (RelativeIdeleGroup.inclusion K M a)) =
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a) ^
          Module.finrank K M
  rw [RelativeIdeleGroup.norm_inclusion, map_pow]

/-- Change the chosen intermediate field in the tower presentation of
the relative idele class group of `N`, keeping the bottom field `K`
fixed. -/
def changeIntermediateClassGroupEquiv :
    TowerRelativeIdeleGroup.ClassGroup K M N ≃*
      TowerRelativeIdeleGroup.ClassGroup K L N :=
  (TowerRelativeIdeleGroup.classGroupEquiv K M N).trans
    (TowerRelativeIdeleGroup.classGroupEquiv K L N).symm

omit [NumberField M] [NumberField L] [Algebra.IsPushout K M L N] in
/-- Changing the intermediate tower presentation does not change the
composite class norm to `K`. -/
theorem towerCompositeClassNorm_changeIntermediate
    (c : TowerRelativeIdeleGroup.ClassGroup K M N) :
    towerCompositeClassNorm K L N
        (changeIntermediateClassGroupEquiv K M L N c) =
      towerCompositeClassNorm K M N c := by
  rw [towerCompositeClassNorm_eq_ideleClassNorm,
    towerCompositeClassNorm_eq_ideleClassNorm]
  simp [changeIntermediateClassGroupEquiv]

omit [NumberField M] [NumberField L] [Algebra.IsPushout K M L N] in
/-- Every composite norm through `M` is, after changing the tower
presentation, already a norm through `L`. -/
theorem towerCompositeClassNorm_mem_ideleClassNormRange
    (c : TowerRelativeIdeleGroup.ClassGroup K M N) :
    towerCompositeClassNorm K M N c ∈
      (RelativeIdeleGroup.classNorm K L).range := by
  refine
    ⟨TowerRelativeIdeleGroup.classNorm K L N
        (changeIntermediateClassGroupEquiv K M L N c),
      ?_⟩
  exact towerCompositeClassNorm_changeIntermediate K M L N c

/-- Norm back from the pushout target quotient to the original
class-norm quotient. -/
def pushoutNormQuotientNormBack :
    IntermediateClassNormQuotient K M N →*
      RelativeIdeleGroup.ClassNormQuotient K L :=
  QuotientGroup.map
    (TowerRelativeIdeleGroup.classNorm K M N).range
    (RelativeIdeleGroup.classNorm K L).range
    (RelativeIdeleGroup.classNorm K M)
    (by
      rintro _ ⟨c, rfl⟩
      exact
        towerCompositeClassNorm_mem_ideleClassNormRange
          K M L N c)

omit [NumberField M] [NumberField L] [Algebra.IsPushout K M L N] in
theorem pushoutNormQuotientNormBack_mk
    (c : RelativeIdeleGroup.ClassGroup K M) :
    pushoutNormQuotientNormBack K M L N
        (QuotientGroup.mk'
          (TowerRelativeIdeleGroup.classNorm K M N).range c) =
      QuotientGroup.mk' (RelativeIdeleGroup.classNorm K L).range
        (RelativeIdeleGroup.classNorm K M c) :=
  rfl

omit [NumberField M] [NumberField L] in
/-- The norm-back composite is the `[M:K]`-power map on the original
class-norm quotient. -/
theorem pushoutNormQuotientNormBack_comp_map
    (q : RelativeIdeleGroup.ClassNormQuotient K L) :
    pushoutNormQuotientNormBack K M L N
        (pushoutNormQuotientMap K M L N q) =
      q ^ Module.finrank K M := by
  refine QuotientGroup.induction_on q ?_
  intro c
  change
    QuotientGroup.mk' (RelativeIdeleGroup.classNorm K L).range
        (RelativeIdeleGroup.classNorm K M
          (RelativeIdeleGroup.classInclusion K M c)) =
      (QuotientGroup.mk' (RelativeIdeleGroup.classNorm K L).range c) ^
        Module.finrank K M
  rw [ideleClassNorm_classInclusion, map_pow]

omit [NumberField M] [NumberField L] in
/-- If the `[M:K]`-power map on the original norm quotient is
injective, then so is the map induced by the pushout inclusion. -/
theorem pushoutNormQuotientMap_injective_of_pow_injective
    (hpow :
      Function.Injective
        (fun q : RelativeIdeleGroup.ClassNormQuotient K L =>
          q ^ Module.finrank K M)) :
    Function.Injective (pushoutNormQuotientMap K M L N) := by
  intro x y hxy
  apply hpow
  change
    x ^ Module.finrank K M =
      y ^ Module.finrank K M
  rw [← pushoutNormQuotientNormBack_comp_map K M L N x,
    ← pushoutNormQuotientNormBack_comp_map K M L N y,
    hxy]
