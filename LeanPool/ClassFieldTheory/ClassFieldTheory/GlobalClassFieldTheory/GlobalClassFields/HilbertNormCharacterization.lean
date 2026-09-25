/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
/-!
# Hilbert norm subgroups and unramified extensions

For a finite Galois extension with no ramified finite prime, the actual
idele-class narrow finite conductor is zero.  Consequently its norm subgroup
contains the big-Hilbert norm subgroup.  This is the norm-subgroup form
of the maximality of the big Hilbert class field.

The inclusion yields a canonical surjection from the narrow class group
onto the actual norm quotient, together with the exact kernel
factorization and the resulting divisibility of orders.
-/

@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Keep norm-range quotient normality out of exported declaration types. -/
local instance
    hilbertNormCharacterization_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- If no finite prime of the base ramifies in the extension, then the
narrow finite conductor of the actual idele-class norm subgroup is zero. -/
theorem ideleClassNorm_narrowFiniteConductor_eq_zero_of_no_ramifiedFinitePlaces
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) = 0 := by
  ext v
  rw [Finsupp.zero_apply]
  apply Finsupp.notMem_support_iff.mp
  intro hv
  have hramified :=
    ideleClassNorm_narrowFiniteConductor_support_subset_ramifiedBaseFinitePlaces
      (K := K) (L := L) hv
  rw [hunramified] at hramified
  simp at hramified

/-- The norm subgroup of every finite Galois extension unramified at all
finite primes contains the big-Hilbert norm subgroup. -/
theorem
    bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    bigHilbertClassFieldNormSubgroup (K := K) ≤
      (_root_.ideleClassNorm K L).range := by
  apply
    (bigHilbertClassFieldNormSubgroup_le_iff_narrowFiniteConductor_eq_zero
      (ideleClassNormConductorialSubgroup (K := K) (L := L))).2
  exact
    ideleClassNorm_narrowFiniteConductor_eq_zero_of_no_ramifiedFinitePlaces
      (K := K) (L := L) hunramified

/-- The canonical transition from the big-Hilbert reciprocity quotient
to the actual norm quotient of an everywhere finite-unramified
extension. -/
def bigHilbertClassFieldQuotientToIdeleClassNormQuotient
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) →*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  QuotientGroup.map
    (bigHilbertClassFieldNormSubgroup (K := K))
    ((_root_.ideleClassNorm K L).range)
    (MonoidHom.id _)
    (fun _ hx =>
      bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces
        (K := K) (L := L) hunramified hx)

/-- The big-Hilbert quotient transition sends an idele class to the
same class modulo the actual norm subgroup. -/
theorem bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (x : IdeleClassGroup K) :
    bigHilbertClassFieldQuotientToIdeleClassNormQuotient
        (K := K) (L := L) hunramified
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K)) x) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range) x :=
  rfl

/-- The transition from the big-Hilbert quotient to an everywhere
finite-unramified actual norm quotient is surjective. -/
theorem
    bigHilbertClassFieldQuotientToIdeleClassNormQuotient_surjective
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Function.Surjective
      (bigHilbertClassFieldQuotientToIdeleClassNormQuotient
        (K := K) (L := L) hunramified) := by
  intro q
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective
      ((_root_.ideleClassNorm K L).range) q
  exact
    ⟨QuotientGroup.mk'
        (bigHilbertClassFieldNormSubgroup (K := K)) x,
      rfl⟩

/-- The kernel of the big-Hilbert quotient transition is the image of
the actual norm subgroup modulo the big-Hilbert norm subgroup. -/
theorem
    bigHilbertClassFieldQuotientToIdeleClassNormQuotient_ker
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    MonoidHom.ker
        (bigHilbertClassFieldQuotientToIdeleClassNormQuotient
          (K := K) (L := L) hunramified) =
      Subgroup.map
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K)))
        ((_root_.ideleClassNorm K L).range) := by
  unfold bigHilbertClassFieldQuotientToIdeleClassNormQuotient
  exact
    (QuotientGroup.ker_map
      (N := bigHilbertClassFieldNormSubgroup (K := K))
      ((_root_.ideleClassNorm K L).range)
      (MonoidHom.id (IdeleClassGroup K))
      (fun _ hx =>
        bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces
          (K := K) (L := L) hunramified hx)).trans
      (congrArg
        (Subgroup.map
          (QuotientGroup.mk' (bigHilbertClassFieldNormSubgroup (K := K))))
        (Subgroup.comap_id ((_root_.ideleClassNorm K L).range)))

/-- For an everywhere finite-unramified extension, quotienting the
big-Hilbert reciprocity quotient by the image of its actual norm
subgroup recovers the actual norm quotient. -/
def bigHilbertNormImageQuotientEquivIdeleClassNormQuotient
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    ((IdeleClassGroup K ⧸
          bigHilbertClassFieldNormSubgroup (K := K)) ⧸
        Subgroup.map
          (QuotientGroup.mk'
            (bigHilbertClassFieldNormSubgroup (K := K)))
          ((_root_.ideleClassNorm K L).range)) ≃*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  (QuotientGroup.quotientMulEquivOfEq
      (bigHilbertClassFieldQuotientToIdeleClassNormQuotient_ker
        (K := K) (L := L) hunramified).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (bigHilbertClassFieldQuotientToIdeleClassNormQuotient
        (K := K) (L := L) hunramified)
      (bigHilbertClassFieldQuotientToIdeleClassNormQuotient_surjective
        (K := K) (L := L) hunramified))

/-- The narrow class group maps canonically onto the actual norm
quotient of every everywhere finite-unramified extension. -/
def narrowClassGroupToIdeleClassNormQuotient
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    RayClass.NarrowClassGroup K →*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  (bigHilbertClassFieldQuotientToIdeleClassNormQuotient
      (K := K) (L := L) hunramified).comp
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).symm.toMonoidHom

/-- The canonical map from the narrow class group to an everywhere
finite-unramified actual norm quotient is surjective. -/
theorem narrowClassGroupToIdeleClassNormQuotient_surjective
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Function.Surjective
      (narrowClassGroupToIdeleClassNormQuotient
        (K := K) (L := L) hunramified) :=
  (bigHilbertClassFieldQuotientToIdeleClassNormQuotient_surjective
      (K := K) (L := L) hunramified).comp
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).symm.surjective

/-- The actual norm quotient of an everywhere finite-unramified
extension has order dividing the narrow class number. -/
theorem
    ideleClassNormQuotient_card_dvd_narrowClassGroup_card_of_no_ramifiedFinitePlaces
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ∣
      Nat.card (RayClass.NarrowClassGroup K) := by
  calc
    Nat.card
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ∣
        Nat.card
          (IdeleClassGroup K ⧸
            bigHilbertClassFieldNormSubgroup (K := K)) := by
      simpa only [Subgroup.index_eq_card] using
        Subgroup.index_dvd_of_le
          (bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces
            (K := K) (L := L) hunramified)
    _ = Nat.card (RayClass.NarrowClassGroup K) :=
      Nat.card_congr
        (bigHilbertClassFieldQuotientEquivNarrowClassGroup
          (K := K)).toEquiv

/-- The narrow class number factors as the kernel order of the canonical
map times the order of an everywhere finite-unramified actual norm
quotient. -/
theorem
    narrowClassGroup_card_eq_unramifiedNormKernel_card_mul_normQuotient_card
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Nat.card (RayClass.NarrowClassGroup K) =
      Nat.card
          (MonoidHom.ker
            (narrowClassGroupToIdeleClassNormQuotient
              (K := K) (L := L) hunramified)) *
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) := by
  let f :=
    narrowClassGroupToIdeleClassNormQuotient
      (K := K) (L := L) hunramified
  have hf : Function.Surjective f :=
    narrowClassGroupToIdeleClassNormQuotient_surjective
      (K := K) (L := L) hunramified
  calc
    Nat.card (RayClass.NarrowClassGroup K) =
        Nat.card (MonoidHom.ker f) *
          (MonoidHom.ker f).index :=
      (Subgroup.card_mul_index (MonoidHom.ker f)).symm
    _ = Nat.card (MonoidHom.ker f) *
        Nat.card f.range := by
      rw [Subgroup.index_ker f]
    _ = Nat.card (MonoidHom.ker f) *
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) := by
      rw [f.range_eq_top_of_surjective hf, Subgroup.card_top]

/-- The degree of every finite cyclic extension unramified at all
finite places divides the order of the narrow class group. -/
theorem
    cyclicExtensionDegree_dvd_narrowClassGroup_card_of_no_ramifiedFinitePlaces
    [IsCyclic (L ≃ₐ[K] L)]
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Module.finrank K L ∣
      Nat.card (RayClass.NarrowClassGroup K) := by
  simpa only [
    ← Subgroup.index_eq_card,
    ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K L] using
      ideleClassNormQuotient_card_dvd_narrowClassGroup_card_of_no_ramifiedFinitePlaces
        (K := K) (L := L) hunramified

/-- For a finite cyclic extension unramified at all finite places, the
narrow class number is the kernel order of the canonical reciprocity
map times the extension degree. -/
theorem
    narrowClassGroup_card_eq_unramifiedCyclicNormKernel_card_mul_extensionDegree
    [IsCyclic (L ≃ₐ[K] L)]
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Nat.card (RayClass.NarrowClassGroup K) =
      Nat.card
          (MonoidHom.ker
            (narrowClassGroupToIdeleClassNormQuotient
              (K := K) (L := L) hunramified)) *
        Module.finrank K L := by
  simpa only [
    ← Subgroup.index_eq_card,
    ClassFieldAxiom.ideleClassNorm_index_eq_finrank_cyclic K L] using
      narrowClassGroup_card_eq_unramifiedNormKernel_card_mul_normQuotient_card
        (K := K) (L := L) hunramified

end GlobalClassFields
end GlobalClassFieldTheory
