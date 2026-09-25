/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps
/-!
# Idele-class norms in a field tower

For a tower `K ⊂ M ⊂ L`, keep the bottom field `K` fixed and write

`𝔸_M = 𝔸_K ⊗[K] M`,
`𝔸_L = (𝔸_K ⊗[K] M) ⊗[M] L`.

This gives an actual norm `C_L → C_M` whose composite with
`C_M → C_K` is the tower norm.  The resulting three concrete norm
quotients form a natural right-exact sequence.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable section

universe u

variable
    (K M L : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]

/-- The canonical right-factor `M`-algebra structure on
`𝔸_K ⊗[K] M`. -/
noncomputable instance (priority := 100)
    relativeAdeleRingIntermediateAlgebra :
    Algebra M (RelativeAdeleRing K M) :=
  Algebra.TensorProduct.rightAlgebra

/-- The relative adele algebra of `L`, presented over the intermediate
field while retaining the fixed bottom-field model of `𝔸_M`. -/
abbrev TowerRelativeAdeleRing :=
  RelativeAdeleRing K M ⊗[M] L

/-- The intermediate field acts on the one-step bottom-field model
`𝔸_K ⊗[K] L` through its embedding in `L`. -/
noncomputable instance (priority := 100)
    relativeAdeleRingTopIntermediateAlgebra :
    Algebra M (RelativeAdeleRing K L) :=
  ((Algebra.TensorProduct.includeRight
      (R := K)
      (A := NumberField.AdeleRing (𝓞 K) K)
      (B := L)).toRingHom.comp
        (algebraMap M L)).toAlgebra

/-- Extend the intermediate relative adele algebra along `M → L`. -/
def intermediateAdeleInclusion :
    RelativeAdeleRing K M →ₐ[M]
      RelativeAdeleRing K L where
  __ :=
    (Algebra.TensorProduct.map
      (AlgHom.id
        (NumberField.AdeleRing (𝓞 K) K)
        (NumberField.AdeleRing (𝓞 K) K))
      (IsScalarTower.toAlgHom K M L)).toRingHom
  commutes' m := by
    change
      1 ⊗ₜ[K] algebraMap M L m =
        1 ⊗ₜ[K] algebraMap M L m
    rfl

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem intermediateAdeleInclusion_tmul
    (a : NumberField.AdeleRing (𝓞 K) K)
    (m : M) :
    intermediateAdeleInclusion K M L (a ⊗ₜ[K] m) =
      a ⊗ₜ[K] algebraMap M L m :=
  rfl

/-- The copy of `L` in the one-step relative adele algebra, regarded
as an `M`-algebra map. -/
def topFieldToOneStep :
    L →ₐ[M] RelativeAdeleRing K L where
  __ :=
    (Algebra.TensorProduct.includeRight
      (R := K)
      (A := NumberField.AdeleRing (𝓞 K) K)
      (B := L)).toRingHom
  commutes' _ := rfl

omit [NumberField M] [NumberField L] [Algebra K M]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem topFieldToOneStep_apply
    (x : L) :
    topFieldToOneStep K M L x =
      (1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] x :=
  rfl

/-- Canonical ring equivalence
`(𝔸_K ⊗[K] M) ⊗[M] L ≃+* 𝔸_K ⊗[K] L`.

This is the standard tensor-product cancellation isomorphism: commute
the two outer factors, commute the inner scalar extension, cancel the
base change, and commute the remaining factors back. -/
def towerRelativeAdeleRingEquiv :
    TowerRelativeAdeleRing K M L ≃+*
      RelativeAdeleRing K L := by
  letI : Algebra L (TowerRelativeAdeleRing K M L) :=
    Algebra.TensorProduct.rightAlgebra
  let e₁ :=
    (Algebra.TensorProduct.commRight
      M L (RelativeAdeleRing K M)).symm
  let e₂ :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl : L ≃ₐ[M] L)
      (Algebra.TensorProduct.commRight K M
        (NumberField.AdeleRing (𝓞 K) K)).symm
  let e₃ :=
    Algebra.TensorProduct.cancelBaseChange
      K M L L (NumberField.AdeleRing (𝓞 K) K)
  let e₄ :=
    Algebra.TensorProduct.commRight
      K L (NumberField.AdeleRing (𝓞 K) K)
  exact
    e₁.toRingEquiv.trans
      (e₂.toRingEquiv.trans
        (e₃.toRingEquiv.trans e₄.toRingEquiv))

/-- Flatten the iterated scalar extension
`(𝔸_K ⊗[K] M) ⊗[M] L` to `𝔸_K ⊗[K] L`. -/
def towerRelativeAdeleFlatten :
    TowerRelativeAdeleRing K M L →ₐ[M]
      RelativeAdeleRing K L :=
  { (towerRelativeAdeleRingEquiv K M L).toRingHom with
    commutes' := by
      intro m
      change _ =
        (1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K]
          algebraMap M L m
      simp [towerRelativeAdeleRingEquiv,
        Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.smul_def] }

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem towerRelativeAdeleFlatten_tmul
    (b : RelativeAdeleRing K M)
    (x : L) :
    towerRelativeAdeleFlatten K M L (b ⊗ₜ[M] x) =
      intermediateAdeleInclusion K M L b *
        topFieldToOneStep K M L x := by
  induction b using TensorProduct.inductionOn with
  | add b₁ b₂ hb₁ hb₂ =>
      simp only [TensorProduct.add_tmul, map_add,
        add_mul, hb₁, hb₂]
  | tmul a m =>
      simp [towerRelativeAdeleFlatten,
        towerRelativeAdeleRingEquiv,
        intermediateAdeleInclusion_tmul,
        topFieldToOneStep_apply,
        Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.smul_def]

/-- Embed the bottom adele algebra into the iterated tensor model. -/
def bottomAdeleToTower :
    NumberField.AdeleRing (𝓞 K) K →ₐ[K]
      TowerRelativeAdeleRing K M L :=
  (Algebra.TensorProduct.includeLeft
      (R := M) (S := K)
      (A := RelativeAdeleRing K M) (B := L)).comp
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := M))

omit [NumberField M] [NumberField L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem bottomAdeleToTower_apply
    (a : NumberField.AdeleRing (𝓞 K) K) :
    bottomAdeleToTower K M L a =
      (a ⊗ₜ[K] (1 : M)) ⊗ₜ[M] (1 : L) :=
  rfl

/-- Embed `L` into the iterated tensor model. -/
def topFieldToTower :
    L →ₐ[K] TowerRelativeAdeleRing K M L :=
  { (Algebra.TensorProduct.includeRight
      (R := M)
      (A := RelativeAdeleRing K M) (B := L)).toRingHom with
    commutes' := by
      intro k
      rw [IsScalarTower.algebraMap_apply K M L]
      change
        1 ⊗ₜ[M]
            algebraMap M L (algebraMap K M k) =
          algebraMap K
            (TowerRelativeAdeleRing K M L) k
      rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul
        (R := M)
        (A := RelativeAdeleRing K M)
        (B := L)]
      change
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K]
            algebraMap K M k) ⊗ₜ[M] (1 : L) =
          ((algebraMap K
              (NumberField.AdeleRing (𝓞 K) K) k) ⊗ₜ[K]
                (1 : M)) ⊗ₜ[M] (1 : L)
      rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul
        (R := K)
        (A := NumberField.AdeleRing (𝓞 K) K)
        (B := M)]
      }

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem topFieldToTower_apply
    (x : L) :
    topFieldToTower K M L x =
      (1 : RelativeAdeleRing K M) ⊗ₜ[M] x :=
  rfl

/-- Expand the one-step tensor model back to the iterated tower model. -/
def towerRelativeAdeleUnflatten :
    RelativeAdeleRing K L →ₐ[K]
      TowerRelativeAdeleRing K M L :=
  { (towerRelativeAdeleRingEquiv K M L).symm.toRingHom with
    commutes' := by
      intro k
      simp [towerRelativeAdeleRingEquiv] }

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem towerRelativeAdeleUnflatten_tmul
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L) :
    towerRelativeAdeleUnflatten K M L (a ⊗ₜ[K] x) =
      bottomAdeleToTower K M L a *
        topFieldToTower K M L x := by
  simp [towerRelativeAdeleUnflatten,
    towerRelativeAdeleRingEquiv,
    bottomAdeleToTower_apply,
    topFieldToTower_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- The flattening equivalence as an equivalence over the bottom adele
ring.  This is the form needed for invariance of determinant norms. -/
def towerRelativeAdeleAlgEquiv :
    TowerRelativeAdeleRing K M L ≃ₐ[NumberField.AdeleRing (𝓞 K) K]
      RelativeAdeleRing K L :=
  { towerRelativeAdeleRingEquiv K M L with
    commutes' := by
      intro a
      change
        towerRelativeAdeleFlatten K M L
            ((a ⊗ₜ[K] (1 : M)) ⊗ₜ[M] (1 : L)) =
          a ⊗ₜ[K] (1 : L)
      simp }

/-- Unit group of the tower presentation of the relative adeles of
`L`. -/
abbrev TowerRelativeIdeleGroup :=
  (TowerRelativeAdeleRing K M L)ˣ

/-- The canonical equivalence from the tower presentation of the
relative ideles of `L` to the one-step presentation over `K`. -/
def towerRelativeIdeleEquiv :
    TowerRelativeIdeleGroup K M L ≃*
      RelativeIdeleGroup K L :=
  Units.mapEquiv
    (towerRelativeAdeleRingEquiv K M L).toMulEquiv

-- Fix the canonical commutativity proof for the tower's tensor-product units.
local instance : IsMulCommutative (TowerRelativeIdeleGroup K M L) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance : IsMulCommutative (RelativeIdeleGroup.ClassGroup K L) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance : IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

namespace TowerRelativeIdeleGroup

/-- The diagonal copy of `Lˣ` in the tower relative idele group. -/
def principalIdele :
    Lˣ →* TowerRelativeIdeleGroup K M L :=
  Units.map
    (Algebra.TensorProduct.includeRight
      (R := M) (A := RelativeAdeleRing K M) (B := L)).toRingHom

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
/-- Flattening the tower presentation preserves the diagonal copy of
`Lˣ`. -/
@[simp]
theorem towerRelativeIdeleEquiv_principalIdele
    (x : Lˣ) :
    towerRelativeIdeleEquiv K M L
        (principalIdele K M L x) =
      RelativeIdeleGroup.principalIdele K L x := by
  apply Units.ext
  change
    towerRelativeAdeleFlatten K M L
        ((1 : RelativeAdeleRing K M) ⊗ₜ[M] (x : L)) =
      (1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] (x : L)
  rw [towerRelativeAdeleFlatten_tmul]
  simp [topFieldToOneStep_apply]

/-- Principal ideles in the tower presentation. -/
def principalSubgroup :
    Subgroup (TowerRelativeIdeleGroup K M L) :=
  (principalIdele K M L).range

/-- The idele class group of `L` in the tower presentation. -/
abbrev ClassGroup :=
  TowerRelativeIdeleGroup K M L ⧸
    principalSubgroup K M L

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
/-- The canonical equivalence maps tower principal ideles exactly onto
the one-step principal-ideles subgroup. -/
theorem principalSubgroup_map_towerRelativeIdeleEquiv :
    (principalSubgroup K M L).map
        (towerRelativeIdeleEquiv K M L) =
      RelativeIdeleGroup.principalSubgroup K L := by
  rw [principalSubgroup,
    RelativeIdeleGroup.principalSubgroup,
    MonoidHom.map_range]
  congr 1
  ext x
  exact congrArg Units.val
    (towerRelativeIdeleEquiv_principalIdele K M L x)

/-- Canonical equivalence between the tower and one-step presentations
of the relative idele class group of `L`. -/
def classGroupEquiv :
    ClassGroup K M L ≃*
      RelativeIdeleGroup.ClassGroup K L :=
  QuotientGroup.congr
    (principalSubgroup K M L)
    (RelativeIdeleGroup.principalSubgroup K L)
    (towerRelativeIdeleEquiv K M L)
    (principalSubgroup_map_towerRelativeIdeleEquiv K M L)

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
theorem classGroupEquiv_mk
    (a : TowerRelativeIdeleGroup K M L) :
    classGroupEquiv K M L
        (QuotientGroup.mk' (principalSubgroup K M L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        (towerRelativeIdeleEquiv K M L a) :=
  rfl

/-- Determinant norm from the tower presentation of `𝔸_L` to
`𝔸_M = 𝔸_K ⊗[K] M`. -/
def norm :
    TowerRelativeIdeleGroup K M L →*
      RelativeIdeleGroup K M :=
  Units.map (Algebra.norm (RelativeAdeleRing K M))

omit [NumberField M] [NumberField L] in
/-- Transitivity of determinant norms, after flattening the tower
presentation to the one-step presentation. -/
theorem norm_transitive_flatten
    (a : TowerRelativeIdeleGroup K M L) :
    RelativeIdeleGroup.norm K M (norm K M L a) =
      RelativeIdeleGroup.norm K L
        (towerRelativeIdeleEquiv K M L a) := by
  apply
    (IdeleGroup.equivAdeleRingUnits (K := K)).injective
  apply Units.ext
  change
    Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (Algebra.norm (RelativeAdeleRing K M)
          (a : TowerRelativeAdeleRing K M L)) =
      Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
        (towerRelativeAdeleFlatten K M L
          (a : TowerRelativeAdeleRing K M L))
  calc
    _ = Algebra.norm (NumberField.AdeleRing (𝓞 K) K)
          (a : TowerRelativeAdeleRing K M L) :=
      Algebra.norm_norm
    _ = _ :=
      (Algebra.norm_eq_of_algEquiv
        (towerRelativeAdeleAlgEquiv K M L)
        (a : TowerRelativeAdeleRing K M L)).symm

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] in
/-- Base change of the field norm from `M` to the relative adele
algebra `𝔸_K ⊗[K] M`. -/
theorem norm_fieldInclusion
    (x : L) :
    Algebra.norm (RelativeAdeleRing K M)
        (Algebra.TensorProduct.includeRight
          (R := M) (A := RelativeAdeleRing K M) (B := L) x) =
      algebraMap M (RelativeAdeleRing K M)
        (Algebra.norm M x) := by
  classical
  let b := Module.Free.chooseBasis M L
  let bA := b.baseChange (RelativeAdeleRing K M)
  rw [Algebra.norm_eq_matrix_det bA,
    Algebra.norm_eq_matrix_det b,
    (algebraMap M (RelativeAdeleRing K M)).map_det]
  congr 1
  ext i j
  simp [bA, b, Algebra.smul_def,
    Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] in
/-- The tower idele norm carries a principal idele to the principal
idele of the field norm. -/
@[simp]
theorem norm_principalIdele
    (x : Lˣ) :
    norm K M L (principalIdele K M L x) =
      RelativeIdeleGroup.principalIdele K M
        (Units.map (Algebra.norm M) x) := by
  apply Units.ext
  exact norm_fieldInclusion K M L (x : L)

/-- The tower norm descended to actual idele class groups. -/
def classNorm :
    ClassGroup K M L →*
      RelativeIdeleGroup.ClassGroup K M :=
  QuotientGroup.map
    (principalSubgroup K M L)
    (RelativeIdeleGroup.principalSubgroup K M)
    (norm K M L)
    (by
      rintro _ ⟨x, rfl⟩
      exact
        ⟨Units.map (Algebra.norm M) x,
          (norm_principalIdele K M L x).symm⟩)

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] in
theorem classNorm_mk
    (a : TowerRelativeIdeleGroup K M L) :
    classNorm K M L
        (QuotientGroup.mk'
          (principalSubgroup K M L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (norm K M L a) :=
  rfl

end TowerRelativeIdeleGroup

section NormQuotientSequence

/-- The norm quotient `C_M / N_{L/M} C_L` in the fixed-bottom-field
tower model. -/
abbrev IntermediateClassNormQuotient :=
  RelativeIdeleGroup.ClassGroup K M ⧸
    (TowerRelativeIdeleGroup.classNorm K M L).range

/-- The composite class norm `C_L → C_M → C_K` in the tower model. -/
def towerCompositeClassNorm :
    TowerRelativeIdeleGroup.ClassGroup K M L →*
      IdeleClassGroup K :=
  (RelativeIdeleGroup.classNorm K M).comp
    (TowerRelativeIdeleGroup.classNorm K M L)

omit [NumberField M] in
/-- After identifying the tower presentation with the one-step
presentation, the composite tower norm is the ordinary class norm from
`L` to `K`. -/
theorem towerCompositeClassNorm_eq_ideleClassNorm
    (c : TowerRelativeIdeleGroup.ClassGroup K M L) :
    towerCompositeClassNorm K M L c =
      RelativeIdeleGroup.classNorm K L
        (TowerRelativeIdeleGroup.classGroupEquiv K M L c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  simp only [towerCompositeClassNorm, MonoidHom.comp_apply]
  exact congrArg
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K))
    (TowerRelativeIdeleGroup.norm_transitive_flatten K M L a)

omit [NumberField M] in
/-- The tower composite norm and the ordinary one-step norm have the
same subgroup of norms in `C_K`. -/
theorem towerCompositeClassNorm_range_eq :
    (towerCompositeClassNorm K M L).range =
      (RelativeIdeleGroup.classNorm K L).range := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    exact
      ⟨TowerRelativeIdeleGroup.classGroupEquiv K M L d,
        (towerCompositeClassNorm_eq_ideleClassNorm
          K M L d).symm⟩
  · rintro ⟨d, rfl⟩
    refine
      ⟨(TowerRelativeIdeleGroup.classGroupEquiv K M L).symm d,
        ?_⟩
    rw [towerCompositeClassNorm_eq_ideleClassNorm,
      MulEquiv.apply_symm_apply]

/-- The corresponding concrete quotient `C_K / N_{L/K} C_L`, before
identifying the tower presentation of `C_L` with the one-step
presentation. -/
abbrev TowerCompositeClassNormQuotient :=
  IdeleClassGroup K ⧸
    (towerCompositeClassNorm K M L).range

/-- Canonical identification of the tower composite norm quotient with
the existing one-step norm quotient `C_K / N_{L/K}C_L`. -/
def towerCompositeClassNormQuotientEquiv :
    TowerCompositeClassNormQuotient K M L ≃*
      RelativeIdeleGroup.ClassNormQuotient K L :=
  QuotientGroup.congr
    (towerCompositeClassNorm K M L).range
    (RelativeIdeleGroup.classNorm K L).range
    (MulEquiv.refl (IdeleClassGroup K))
    (by
      simpa using towerCompositeClassNorm_range_eq K M L)

/-- The norm-induced first map

`C_M / N_{L/M}C_L → C_K / N_{L/K}C_L`.
-/
def intermediateToCompositeNormQuotient :
    IntermediateClassNormQuotient K M L →*
      TowerCompositeClassNormQuotient K M L :=
  QuotientGroup.map
    (TowerRelativeIdeleGroup.classNorm K M L).range
    (towerCompositeClassNorm K M L).range
    (RelativeIdeleGroup.classNorm K M)
    (by
      rintro _ ⟨c, rfl⟩
      exact ⟨c, rfl⟩)

/-- The quotient map

`C_K / N_{L/K}C_L → C_K / N_{M/K}C_M`.
-/
def compositeToBaseNormQuotient :
    TowerCompositeClassNormQuotient K M L →*
      RelativeIdeleGroup.ClassNormQuotient K M :=
  QuotientGroup.map
    (towerCompositeClassNorm K M L).range
    (RelativeIdeleGroup.classNorm K M).range
    (MonoidHom.id (IdeleClassGroup K))
    (by
      rintro _ ⟨c, rfl⟩
      exact
        ⟨TowerRelativeIdeleGroup.classNorm K M L c, rfl⟩)

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L] in
theorem intermediateToCompositeNormQuotient_mk
    (c : RelativeIdeleGroup.ClassGroup K M) :
    intermediateToCompositeNormQuotient K M L
        (QuotientGroup.mk'
          (TowerRelativeIdeleGroup.classNorm K M L).range c) =
      QuotientGroup.mk'
        (towerCompositeClassNorm K M L).range
        (RelativeIdeleGroup.classNorm K M c) :=
  rfl

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L] in
theorem compositeToBaseNormQuotient_mk
    (c : IdeleClassGroup K) :
    compositeToBaseNormQuotient K M L
        (QuotientGroup.mk'
          (towerCompositeClassNorm K M L).range c) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.classNorm K M).range c :=
  rfl

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L] in
/-- Exactness of the concrete tower norm-quotient sequence. -/
theorem intermediateToCompositeNormQuotient_range_eq_ker :
    MonoidHom.range
        (intermediateToCompositeNormQuotient K M L) =
      MonoidHom.ker
        (compositeToBaseNormQuotient K M L) := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    refine QuotientGroup.induction_on a ?_
    intro c
    change
      QuotientGroup.mk'
          (RelativeIdeleGroup.classNorm K M).range
          (RelativeIdeleGroup.classNorm K M c) = 1
    exact
      (QuotientGroup.eq_one_iff
        (RelativeIdeleGroup.classNorm K M c)).2 ⟨c, rfl⟩
  · intro hq
    refine QuotientGroup.induction_on q ?_ hq
    intro c hc
    change
      QuotientGroup.mk'
          (RelativeIdeleGroup.classNorm K M).range c = 1
      at hc
    have hcRange :
        c ∈ (RelativeIdeleGroup.classNorm K M).range :=
      (QuotientGroup.eq_one_iff c).1 hc
    obtain ⟨d, rfl⟩ := hcRange
    refine
      ⟨QuotientGroup.mk'
          (TowerRelativeIdeleGroup.classNorm K M L).range d,
        ?_⟩
    rfl

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L] in
/-- The last map in the tower norm-quotient sequence is onto. -/
theorem compositeToBaseNormQuotient_surjective :
    Function.Surjective
      (compositeToBaseNormQuotient K M L) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro c
  exact
    ⟨QuotientGroup.mk'
        (towerCompositeClassNorm K M L).range c,
      rfl⟩

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L] in
/-- Cardinal bound supplied by the actual right-exact tower sequence:

`#(C_K / N_{L/K}C_L) ≤
  #(C_M / N_{L/M}C_L) · #(C_K / N_{M/K}C_M)`.

Only finiteness of the two outer quotients is required; finiteness of
the middle quotient is constructed from exactness. -/
theorem towerCompositeClassNormQuotient_card_le_mul
    [Finite (IntermediateClassNormQuotient K M L)]
    [Finite (RelativeIdeleGroup.ClassNormQuotient K M)] :
    Nat.card (TowerCompositeClassNormQuotient K M L) ≤
      Nat.card (IntermediateClassNormQuotient K M L) *
        Nat.card (RelativeIdeleGroup.ClassNormQuotient K M) := by
  let A := IntermediateClassNormQuotient K M L
  let B := TowerCompositeClassNormQuotient K M L
  let C := RelativeIdeleGroup.ClassNormQuotient K M
  let f : A →* B :=
    intermediateToCompositeNormQuotient K M L
  let g : B →* C :=
    compositeToBaseNormQuotient K M L
  let : Fintype A := Fintype.ofFinite A
  let : Fintype C := Fintype.ofFinite C
  let : Fintype B :=
    Group.fintypeOfKerEqRange f g
      (intermediateToCompositeNormQuotient_range_eq_ker
        K M L).symm
  have hg :
      Function.Surjective g :=
    compositeToBaseNormQuotient_surjective K M L
  have hquot :
      Nat.card (B ⧸ g.ker) = Nat.card C :=
    Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective
        g hg).toEquiv
  have hrange :
      Nat.card f.range ≤ Nat.card A :=
    Nat.card_le_card_of_surjective
      f.rangeRestrict
      f.rangeRestrict_surjective
  calc
    Nat.card B =
        Nat.card (B ⧸ g.ker) *
          Nat.card g.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup
        g.ker
    _ = Nat.card C * Nat.card f.range := by
      rw [hquot,
        ← intermediateToCompositeNormQuotient_range_eq_ker
          K M L]
    _ ≤ Nat.card C * Nat.card A :=
      Nat.mul_le_mul_left (Nat.card C) hrange
    _ = Nat.card A * Nat.card C := Nat.mul_comm _ _

omit [NumberField M] in
/-- The tower cardinal bound in the standard one-step presentation:

`#(C_K / N_{L/K}C_L) ≤
  #(C_M / N_{L/M}C_L) · #(C_K / N_{M/K}C_M)`.
-/
theorem ideleClassNormQuotient_card_le_mul
    [Finite (IntermediateClassNormQuotient K M L)]
    [Finite (RelativeIdeleGroup.ClassNormQuotient K M)] :
    Nat.card (RelativeIdeleGroup.ClassNormQuotient K L) ≤
      Nat.card (IntermediateClassNormQuotient K M L) *
        Nat.card (RelativeIdeleGroup.ClassNormQuotient K M) := by
  calc
    Nat.card (RelativeIdeleGroup.ClassNormQuotient K L) =
        Nat.card (TowerCompositeClassNormQuotient K M L) :=
      Nat.card_congr
        (towerCompositeClassNormQuotientEquiv K M L).symm.toEquiv
    _ ≤ Nat.card (IntermediateClassNormQuotient K M L) *
          Nat.card (RelativeIdeleGroup.ClassNormQuotient K M) :=
      towerCompositeClassNormQuotient_card_le_mul K M L

end NormQuotientSequence
