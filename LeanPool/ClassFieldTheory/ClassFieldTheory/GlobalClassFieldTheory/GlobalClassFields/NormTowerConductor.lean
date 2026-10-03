/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
/-!
# Norm quotients and narrow finite conductors in a field tower

For a finite tower `K ⊂ M ⊂ L`, norm transitivity places the actual
idele-class norms from `L` inside those from `M`.  This produces the
canonical quotient transition

`C_K / N_{L/K} C_L → C_K / N_{M/K} C_M`.

The transition is surjective, its kernel is the image of
`N_{M/K} C_M` modulo `N_{L/K} C_L`, and its orders satisfy the
corresponding exact factorization.  When both extensions over `K` are
Galois, the narrow finite conductor is contravariant under this
inclusion and the conductor support of the intermediate extension is
contained in that of the top extension.  This is the finite part in the
all-real-positive convention, not a claim about the full archimedean
conductor.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- The canonical commutativity witness used to form ordinary norm quotients. -/
private theorem normTowerIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] normTowerIdeleClassIsMulCommutative

/-- Quotient commutativity follows by lifting representatives through the
canonical quotient map, without constructing another group dictionary. -/
private theorem normTowerQuotientIsMulCommutative
    {G : Type*} [Group G] [IsMulCommutative G]
    (N : Subgroup G) : IsMulCommutative (G ⧸ N) := by
  refine IsMulCommutative.of_comm ?_
  intro a b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
  calc
    QuotientGroup.mk' N x * QuotientGroup.mk' N y =
        QuotientGroup.mk' N (x * y) :=
      ((QuotientGroup.mk' N).map_mul x y).symm
    _ = QuotientGroup.mk' N (y * x) :=
      congrArg (QuotientGroup.mk' N) (mul_comm' x y)
    _ = QuotientGroup.mk' N y * QuotientGroup.mk' N x :=
      (QuotientGroup.mk' N).map_mul y x

/-- A quotient of the idele class group is commutative, so its norm-image
subgroups are normal when forming the second quotient. -/
private theorem normTowerIdeleClassQuotientIsMulCommutative
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) :
    IsMulCommutative (IdeleClassGroup F ⧸ N) :=
  normTowerQuotientIsMulCommutative N

attribute [local instance] normTowerIdeleClassQuotientIsMulCommutative

variable {K : Type} [Field K] [NumberField K]

section Tower

variable
    {M L : Type}
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [IsGalois K M] [IsGalois K L]

omit [IsGalois K M] [IsGalois K L] in
/-- Norm transitivity puts every idele-class norm from the top field
inside the idele-class norm subgroup of the intermediate field. -/
theorem ideleClassNorm_range_le_of_tower :
    (_root_.ideleClassNorm K L).range ≤
      (_root_.ideleClassNorm K M).range := by
  calc
    (_root_.ideleClassNorm K L).range =
        (RelativeIdeleGroup.classNorm K L).range :=
      ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := L)
    _ ≤
        (RelativeIdeleGroup.classNorm K M).range := by
      rw [← towerCompositeClassNorm_range_eq K M L]
      rintro _ ⟨c, rfl⟩
      exact
        ⟨TowerRelativeIdeleGroup.classNorm K M L c, rfl⟩
    _ = (_root_.ideleClassNorm K M).range :=
      (ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := M)).symm

/-- The quotient transition induced by norm transitivity in a finite
field tower. -/
def ideleClassNormQuotientTowerMap :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) →*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K M).range) :=
  QuotientGroup.map
    ((_root_.ideleClassNorm K L).range)
    ((_root_.ideleClassNorm K M).range)
    (MonoidHom.id _)
    (fun _ hx =>
      ideleClassNorm_range_le_of_tower
        (K := K) (M := M) (L := L) hx)

omit [IsGalois K M] [IsGalois K L] in
/-- The tower norm-quotient transition sends an idele class to the same
class modulo the intermediate norm subgroup. -/
theorem ideleClassNormQuotientTowerMap_mk
    (x : IdeleClassGroup K) :
    ideleClassNormQuotientTowerMap
        (K := K) (M := M) (L := L)
        (QuotientGroup.mk'
          ((_root_.ideleClassNorm K L).range) x) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K M).range) x :=
  rfl

omit [IsGalois K M] [IsGalois K L] in
/-- The tower norm-quotient transition is surjective. -/
theorem ideleClassNormQuotientTowerMap_surjective :
    Function.Surjective
      (ideleClassNormQuotientTowerMap
        (K := K) (M := M) (L := L)) := by
  intro q
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective
      ((_root_.ideleClassNorm K M).range) q
  exact
    ⟨QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range) x, rfl⟩

/-- The narrow-finite-conductor ray class group of the top extension maps
canonically onto the norm quotient of the intermediate extension. -/
noncomputable def
    narrowFiniteConductorRayClassGroupToIntermediateIdeleClassNormQuotient :
    RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite
          (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) →*
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K M).range :=
  (ideleClassNormQuotientTowerMap
      (K := K) (M := M) (L := L)).comp
    (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
      (K := K) (L := L))

omit [IsGalois K M] in
/-- The narrow-finite-conductor ray-class map to the intermediate norm quotient sends
an idele class to the same class modulo the intermediate norm
subgroup. -/
theorem
    narrowFiniteConductorRayClassGroupToIntermediateIdeleClassNormQuotient_mk
    (x : IdeleClassGroup K) :
    narrowFiniteConductorRayClassGroupToIntermediateIdeleClassNormQuotient
        (K := K) (M := M) (L := L)
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) x) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K M).range) x := by
  change
    ideleClassNormQuotientTowerMap
        (K := K) (M := M) (L := L)
        (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient
          (K := K) (L := L)
          (QuotientGroup.mk'
            (RayClass.Modulus.congruenceSubgroup
              (RayClass.Modulus.narrowOfFinite
                (ideleClassNormNarrowFiniteConductor
                  (K := K) (L := L)))) x)) =
      _
  rw [
    narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk,
    ideleClassNormQuotientTowerMap_mk]

omit [IsGalois K M] in
/-- The narrow-finite-conductor ray-class map to the intermediate norm quotient is
surjective. -/
theorem
    narrowFiniteConductorRayClassGroupToIntermediateIdeleClassNormQuotient_surjective :
    Function.Surjective
      (narrowFiniteConductorRayClassGroupToIntermediateIdeleClassNormQuotient
        (K := K) (M := M) (L := L)) :=
  (ideleClassNormQuotientTowerMap_surjective
      (K := K) (M := M) (L := L)).comp
    (narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_surjective
      (K := K) (L := L))

omit [IsGalois K M] [IsGalois K L] in
/-- The kernel of the tower norm-quotient transition is the image of
the intermediate norm subgroup modulo the top norm subgroup. -/
theorem ideleClassNormQuotientTowerMap_ker :
    MonoidHom.ker
        (ideleClassNormQuotientTowerMap
          (K := K) (M := M) (L := L)) =
      Subgroup.map
        (QuotientGroup.mk'
          ((_root_.ideleClassNorm K L).range))
        ((_root_.ideleClassNorm K M).range) := by
  unfold ideleClassNormQuotientTowerMap
  exact
    (QuotientGroup.ker_map
      (N := ((_root_.ideleClassNorm K L).range))
      ((_root_.ideleClassNorm K M).range)
      (MonoidHom.id (IdeleClassGroup K))
      (fun _ hx =>
        ideleClassNorm_range_le_of_tower
          (K := K) (M := M) (L := L) hx)).trans
      (congrArg
        (Subgroup.map
          (QuotientGroup.mk' ((_root_.ideleClassNorm K L).range)))
        (Subgroup.comap_id ((_root_.ideleClassNorm K M).range)))

/-- Quotienting the top norm quotient by the image of the intermediate
norm subgroup gives the intermediate norm quotient. -/
def ideleClassNormQuotientModuloIntermediateEquiv :
    ((IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ⧸
        Subgroup.map
          (QuotientGroup.mk'
            ((_root_.ideleClassNorm K L).range))
          ((_root_.ideleClassNorm K M).range)) ≃*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K M).range) :=
  (QuotientGroup.quotientMulEquivOfEq
      (ideleClassNormQuotientTowerMap_ker
        (K := K) (M := M) (L := L)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (ideleClassNormQuotientTowerMap
        (K := K) (M := M) (L := L))
      (ideleClassNormQuotientTowerMap_surjective
        (K := K) (M := M) (L := L)))

/-- The tower norm-quotient transition transported to the
narrow-finite-conductor ray-class norm-subgroup quotient presentations. -/
noncomputable def
    narrowFiniteConductorRayClassNormSubgroupQuotientTowerMap :
    (RayClass.RayClassGroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor
              (K := K) (L := L))) ⧸
        Subgroup.map
          (QuotientGroup.mk'
            (RayClass.Modulus.congruenceSubgroup
              (RayClass.Modulus.narrowOfFinite
                (ideleClassNormNarrowFiniteConductor
                  (K := K) (L := L)))))
          ((_root_.ideleClassNorm K L).range)) →*
      (RayClass.RayClassGroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor
              (K := K) (L := M))) ⧸
        Subgroup.map
          (QuotientGroup.mk'
            (RayClass.Modulus.congruenceSubgroup
              (RayClass.Modulus.narrowOfFinite
                (ideleClassNormNarrowFiniteConductor
                  (K := K) (L := M)))))
          ((_root_.ideleClassNorm K M).range)) :=
  (narrowFiniteConductorRayClassNormSubgroupQuotientEquivIdeleClassNormQuotient
      (K := K) (L := M)).symm.toMonoidHom.comp
    ((ideleClassNormQuotientTowerMap
        (K := K) (M := M) (L := L)).comp
      (narrowFiniteConductorRayClassNormSubgroupQuotientEquivIdeleClassNormQuotient
        (K := K) (L := L)).toMonoidHom)

/-- Transporting the tower transition to narrow-finite-conductor ray-class quotient
presentations commutes with the canonical identifications with actual
norm quotients. -/
theorem
    narrowFiniteConductorRayClassNormSubgroupQuotientTowerMap_commutes :
    (narrowFiniteConductorRayClassNormSubgroupQuotientEquivIdeleClassNormQuotient
        (K := K) (L := M)).toMonoidHom.comp
      (narrowFiniteConductorRayClassNormSubgroupQuotientTowerMap
        (K := K) (M := M) (L := L)) =
    (ideleClassNormQuotientTowerMap
        (K := K) (M := M) (L := L)).comp
      (narrowFiniteConductorRayClassNormSubgroupQuotientEquivIdeleClassNormQuotient
        (K := K) (L := L)).toMonoidHom := by
  ext q
  simp [narrowFiniteConductorRayClassNormSubgroupQuotientTowerMap]

omit [IsGalois K M] [IsGalois K L] in
/-- The order of the top norm quotient factors into the relative kernel
order and the order of the intermediate norm quotient. -/
theorem
    ideleClassNormQuotient_card_eq_intermediateNormImage_card_mul_baseNormQuotient_card :
    Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) =
      Nat.card
          (Subgroup.map
            (QuotientGroup.mk'
              ((_root_.ideleClassNorm K L).range))
            ((_root_.ideleClassNorm K M).range)) *
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K M).range) := by
  let f :=
    ideleClassNormQuotientTowerMap
      (K := K) (M := M) (L := L)
  have hf : Function.Surjective f :=
    ideleClassNormQuotientTowerMap_surjective
      (K := K) (M := M) (L := L)
  calc
    Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) =
        Nat.card (MonoidHom.ker f) *
          (MonoidHom.ker f).index :=
      (Subgroup.card_mul_index (MonoidHom.ker f)).symm
    _ = Nat.card (MonoidHom.ker f) *
        Nat.card f.range := by
      rw [Subgroup.index_ker f]
    _ = Nat.card (MonoidHom.ker f) *
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K M).range) := by
      rw [f.range_eq_top_of_surjective hf, Subgroup.card_top]
    _ = Nat.card
          (Subgroup.map
            (QuotientGroup.mk'
              ((_root_.ideleClassNorm K L).range))
            ((_root_.ideleClassNorm K M).range)) *
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K M).range) := by
      rw [ideleClassNormQuotientTowerMap_ker
        (K := K) (M := M) (L := L)]

omit [IsGalois K M] [IsGalois K L] in
/-- The intermediate norm quotient order divides the top norm quotient
order. -/
theorem ideleClassNormQuotient_card_dvd_of_tower :
    Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K M).range) ∣
      Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) := by
  simpa only [Subgroup.index_eq_card] using
    Subgroup.index_dvd_of_le
      (ideleClassNorm_range_le_of_tower
        (K := K) (M := M) (L := L))

/-- In a finite Galois tower, the narrow finite conductor of the intermediate
norm subgroup is bounded by that of the top norm subgroup. -/
theorem ideleClassNorm_narrowFiniteConductor_le_of_tower :
    ideleClassNormNarrowFiniteConductor (K := K) (L := M) ≤
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) := by
  exact
    ConductorialSubgroup.narrowFiniteConductor_antitone
      (ideleClassNormConductorialSubgroup (K := K) (L := L))
      (ideleClassNormConductorialSubgroup (K := K) (L := M))
      (ideleClassNorm_range_le_of_tower
        (K := K) (M := M) (L := L))

/-- In a finite Galois tower, every prime in the narrow finite conductor
support of the intermediate norm subgroup also occurs in that of the top
norm subgroup. -/
theorem ideleClassNorm_narrowFiniteConductor_support_subset_of_tower :
    (ideleClassNormNarrowFiniteConductor (K := K) (L := M)).support ⊆
      (ideleClassNormNarrowFiniteConductor (K := K) (L := L)).support := by
  intro v hv
  have hne :
      ideleClassNormNarrowFiniteConductor (K := K) (L := M) v ≠ 0 :=
    Finsupp.mem_support_iff.mp hv
  apply Finsupp.mem_support_iff.mpr
  intro htopZero
  apply hne
  exact Nat.eq_zero_of_le_zero
    ((ideleClassNorm_narrowFiniteConductor_le_of_tower
      (K := K) (M := M) (L := L) v).trans_eq htopZero)

end Tower

end GlobalClassFields
end GlobalClassFieldTheory
