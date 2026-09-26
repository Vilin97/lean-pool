/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveAction
/-!
# Frobenius lifts on completed p-adic Lubin--Tate levels

Arithmetic Frobenius on the completed maximal-unramified p-adic field fixes
the standard primitive Lubin--Tate polynomial, since that polynomial descends
to `ℚ_[p]`.  Using the completed primitive power basis, it therefore extends
to a semilinear automorphism of every completed level.  A finite unit
parameter prescribes the image of the primitive root.

The construction is an actual field automorphism.  Surjectivity follows from
the theorem that every completed unit-parameter root generates the completed
level.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The ordinary completed-base algebra structure on a completed level,
named so it can coexist with the Frobenius-twisted structure. -/
@[reducible]
noncomputable def padicCompletedLevelOriginalAlgebra
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
  inferInstance

/-- The codomain algebra structure whose scalar map is arithmetic
Frobenius followed by the ordinary scalar inclusion. -/
@[reducible]
noncomputable def padicCompletedLevelFrobeniusAlgebra
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
  RingHom.toAlgebra
    ((algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)).comp
      (padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom)

/-- The twisted level algebra map applies completed Frobenius before scalar
extension. -/
theorem padicCompletedLevelFrobeniusAlgebra_algebraMap
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : padicCompletedUnramifiedField p) :
    @algebraMap
        (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        _ _ (padicCompletedLevelFrobeniusAlgebra p n) a =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (padicCompletedUnramifiedFrobenius p a) :=
  rfl

/-- Arithmetic Frobenius fixes the completed primitive polynomial because
its coefficients descend to `ℚ_[p]`. -/
theorem padicCompletedPrimitivePolynomial_frobenius
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomial p n).map
        (padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom =
      padicCompletedPrimitivePolynomial p n := by
  unfold padicCompletedPrimitivePolynomial
  have hcomp :
      ((padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom).comp
          (algebraMap ℚ_[p] (padicCompletedUnramifiedField p)) =
        algebraMap ℚ_[p] (padicCompletedUnramifiedField p) := by
    apply RingHom.ext
    intro a
    exact (padicCompletedUnramifiedFrobenius p).commutes a
  rw [Polynomial.map_map, hcomp]

/-- A completed unit-parameter root annihilates the primitive minimal
polynomial for the Frobenius-twisted codomain algebra structure. -/
theorem padicCompletedUnitParameterRoot_aeval_minpoly_frobenius
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    @Polynomial.aeval
        (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        _ _ (padicCompletedLevelFrobeniusAlgebra p n)
        (padicCompletedUnitParameterRoot p n a)
        (minpoly (padicCompletedUnramifiedField p)
          (padicCompletedPrimitiveRoot p n)) =
      0 := by
  rw [padicCompletedPrimitiveRoot_minpoly]
  change Polynomial.eval₂
      ((algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)).comp
        (padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom)
      (padicCompletedUnitParameterRoot p n a)
      (padicCompletedPrimitivePolynomial p n) = 0
  rw [← Polynomial.eval₂_map,
    padicCompletedPrimitivePolynomial_frobenius]
  rw [← Polynomial.eval_map]
  exact padicCompletedUnitParameterRoot_isRoot p n a

/-- The semilinear algebra homomorphism extending arithmetic Frobenius and
sending the chosen primitive root to the prescribed unit-parameter root. -/
noncomputable def padicCompletedFrobeniusLiftAlgHom
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    @AlgHom
      (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n)
      (padicCompletedLevelField p n)
      _ _ _
      (padicCompletedLevelOriginalAlgebra p n)
      (padicCompletedLevelFrobeniusAlgebra p n) :=
  @PowerBasis.lift
    (padicCompletedLevelField p n) _
    (padicCompletedUnramifiedField p) _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelField p n) _
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedPrimitivePowerBasis p n)
    (padicCompletedUnitParameterRoot p n a) (by
      rw [padicCompletedPrimitivePowerBasis_gen]
      exact
        padicCompletedUnitParameterRoot_aeval_minpoly_frobenius p n a)

/-- The semilinear Frobenius homomorphism has the prescribed value on the
primitive root. -/
@[simp]
theorem padicCompletedFrobeniusLiftAlgHom_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    padicCompletedFrobeniusLiftAlgHom p n a
        (padicCompletedPrimitiveRoot p n) =
      padicCompletedUnitParameterRoot p n a := by
  change padicCompletedFrobeniusLiftAlgHom p n a
      (padicCompletedPrimitivePowerBasis p n).gen = _
  exact @PowerBasis.lift_gen
    (padicCompletedLevelField p n) _
    (padicCompletedUnramifiedField p) _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelField p n) _
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedPrimitivePowerBasis p n)
    (padicCompletedUnitParameterRoot p n a)
    (padicCompletedUnitParameterRoot_aeval_minpoly_frobenius p n a)

/-- The underlying field homomorphism of the prescribed completed
Frobenius lift. -/
noncomputable def padicCompletedFrobeniusLift
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    padicCompletedLevelField p n →+*
      padicCompletedLevelField p n :=
  @AlgHom.toRingHom
    (padicCompletedUnramifiedField p)
    (padicCompletedLevelField p n)
    (padicCompletedLevelField p n)
    _ _ _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedFrobeniusLiftAlgHom p n a)

/-- A completed Frobenius lift acts on base scalars by arithmetic
Frobenius. -/
@[simp]
theorem padicCompletedFrobeniusLift_algebraMap
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n)
    (b : padicCompletedUnramifiedField p) :
    padicCompletedFrobeniusLift p n a
        (algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) b) =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (padicCompletedUnramifiedFrobenius p b) := by
  change padicCompletedFrobeniusLiftAlgHom p n a
      (@algebraMap
        (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        _ _ (padicCompletedLevelOriginalAlgebra p n) b) =
    @algebraMap
      (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n)
      _ _ (padicCompletedLevelFrobeniusAlgebra p n) b
  exact @AlgHom.commutes
    (padicCompletedUnramifiedField p)
    (padicCompletedLevelField p n)
    (padicCompletedLevelField p n)
    _ _ _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedFrobeniusLiftAlgHom p n a) b

/-- A completed Frobenius lift sends the primitive root to its prescribed
unit-parameter transform. -/
@[simp]
theorem padicCompletedFrobeniusLift_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    padicCompletedFrobeniusLift p n a
        (padicCompletedPrimitiveRoot p n) =
      padicCompletedUnitParameterRoot p n a :=
  padicCompletedFrobeniusLiftAlgHom_primitiveRoot p n a

/-- The prescribed completed Frobenius lift is surjective. -/
theorem padicCompletedFrobeniusLift_surjective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    Function.Surjective (padicCompletedFrobeniusLift p n a) := by
  let E := padicCompletedUnramifiedField p
  let L := padicCompletedLevelField p n
  let σ : L →+* L := padicCompletedFrobeniusLift p n a
  let R : Subring L := σ.range
  have hbase (b : E) : algebraMap E L b ∈ R := by
    refine
      ⟨algebraMap E L
        ((padicCompletedUnramifiedFrobenius p).symm b), ?_⟩
    change σ
        (algebraMap E L
          ((padicCompletedUnramifiedFrobenius p).symm b)) =
      algebraMap E L b
    rw [show σ = padicCompletedFrobeniusLift p n a by rfl,
      padicCompletedFrobeniusLift_algebraMap,
      (padicCompletedUnramifiedFrobenius p).apply_symm_apply]
  let S : Subalgebra E L :=
    { R with
      algebraMap_mem' := hbase }
  have hy : padicCompletedUnitParameterRoot p n a ∈ S := by
    refine ⟨padicCompletedPrimitiveRoot p n, ?_⟩
    exact padicCompletedFrobeniusLift_primitiveRoot p n a
  have hle :
      Algebra.adjoin E
          ({padicCompletedUnitParameterRoot p n a} : Set L) ≤
        S := by
    apply Algebra.adjoin_le
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hy
  rw [show Algebra.adjoin E
      ({padicCompletedUnitParameterRoot p n a} : Set L) = ⊤ by
        exact padicCompletedUnitParameterRoot_adjoin_eq_top p n a] at hle
  have hS : S = ⊤ := top_unique hle
  intro z
  have hz : z ∈ S := by rw [hS]; trivial
  exact hz

/-- The actual field automorphism extending arithmetic Frobenius and
having the prescribed action on the completed primitive root. -/
noncomputable def padicCompletedFrobeniusLiftEquiv
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    padicCompletedLevelField p n ≃+*
      padicCompletedLevelField p n :=
  RingEquiv.ofBijective (padicCompletedFrobeniusLift p n a)
    ⟨(padicCompletedFrobeniusLift p n a).injective,
      padicCompletedFrobeniusLift_surjective p n a⟩

/-- The completed Frobenius-lift equivalence acts on base scalars by
arithmetic Frobenius. -/
@[simp]
theorem padicCompletedFrobeniusLiftEquiv_algebraMap
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n)
    (b : padicCompletedUnramifiedField p) :
    padicCompletedFrobeniusLiftEquiv p n a
        (algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) b) =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (padicCompletedUnramifiedFrobenius p b) :=
  padicCompletedFrobeniusLift_algebraMap p n a b

/-- The completed Frobenius-lift equivalence has the prescribed value on
the primitive root. -/
@[simp]
theorem padicCompletedFrobeniusLiftEquiv_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    padicCompletedFrobeniusLiftEquiv p n a
        (padicCompletedPrimitiveRoot p n) =
      padicCompletedUnitParameterRoot p n a :=
  padicCompletedFrobeniusLift_primitiveRoot p n a

/-- The direct completed standard unit action annihilates the primitive
minimal polynomial for the Frobenius-twisted codomain structure. -/
theorem
    padicCompletedStandardPrimitivePointUnitAction_aeval_minpoly_frobenius
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    @Polynomial.aeval
        (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        _ _ (padicCompletedLevelFrobeniusAlgebra p n)
        (((padicCompletedStandardPrimitivePointUnitAction p n u :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n))
        (minpoly (padicCompletedUnramifiedField p)
          (padicCompletedPrimitiveRoot p n)) =
      0 := by
  rw [padicCompletedPrimitiveRoot_minpoly]
  change Polynomial.eval₂
      ((algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)).comp
        (padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom)
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n))
      (padicCompletedPrimitivePolynomial p n) = 0
  rw [← Polynomial.eval₂_map,
    padicCompletedPrimitivePolynomial_frobenius]
  rw [← Polynomial.eval_map]
  exact
    padicCompletedStandardPrimitivePointUnitAction_isRoot p n u

/-- The semilinear algebra homomorphism extending arithmetic Frobenius and
sending the primitive root to its actual completed standard unit action. -/
noncomputable def padicCompletedUnitFrobeniusLiftAlgHom
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    @AlgHom
      (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n)
      (padicCompletedLevelField p n)
      _ _ _
      (padicCompletedLevelOriginalAlgebra p n)
      (padicCompletedLevelFrobeniusAlgebra p n) :=
  @PowerBasis.lift
    (padicCompletedLevelField p n) _
    (padicCompletedUnramifiedField p) _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelField p n) _
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedPrimitivePowerBasis p n)
    (((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n)) (by
      rw [padicCompletedPrimitivePowerBasis_gen]
      exact
        padicCompletedStandardPrimitivePointUnitAction_aeval_minpoly_frobenius
          p n u)

/-- The direct unit-indexed semilinear homomorphism sends the primitive
root to the actual completed standard unit action. -/
@[simp]
theorem padicCompletedUnitFrobeniusLiftAlgHom_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedUnitFrobeniusLiftAlgHom p n u
        (padicCompletedPrimitiveRoot p n) =
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)) := by
  change padicCompletedUnitFrobeniusLiftAlgHom p n u
      (padicCompletedPrimitivePowerBasis p n).gen = _
  exact @PowerBasis.lift_gen
    (padicCompletedLevelField p n) _
    (padicCompletedUnramifiedField p) _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelField p n) _
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedPrimitivePowerBasis p n)
    (((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n))
    (padicCompletedStandardPrimitivePointUnitAction_aeval_minpoly_frobenius
      p n u)

/-- The underlying field homomorphism of the unit-indexed completed
Frobenius lift. -/
noncomputable def padicCompletedUnitFrobeniusLift
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedLevelField p n →+*
      padicCompletedLevelField p n :=
  @AlgHom.toRingHom
    (padicCompletedUnramifiedField p)
    (padicCompletedLevelField p n)
    (padicCompletedLevelField p n)
    _ _ _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedUnitFrobeniusLiftAlgHom p n u)

/-- The direct unit-indexed completed Frobenius lift acts on base scalars
by arithmetic Frobenius. -/
@[simp]
theorem padicCompletedUnitFrobeniusLift_algebraMap
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (b : padicCompletedUnramifiedField p) :
    padicCompletedUnitFrobeniusLift p n u
        (algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) b) =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (padicCompletedUnramifiedFrobenius p b) := by
  change padicCompletedUnitFrobeniusLiftAlgHom p n u
      (@algebraMap
        (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        _ _ (padicCompletedLevelOriginalAlgebra p n) b) =
    @algebraMap
      (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n)
      _ _ (padicCompletedLevelFrobeniusAlgebra p n) b
  exact @AlgHom.commutes
    (padicCompletedUnramifiedField p)
    (padicCompletedLevelField p n)
    (padicCompletedLevelField p n)
    _ _ _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedUnitFrobeniusLiftAlgHom p n u) b

/-- The direct unit-indexed completed Frobenius lift has its prescribed
action on the primitive root. -/
@[simp]
theorem padicCompletedUnitFrobeniusLift_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedUnitFrobeniusLift p n u
        (padicCompletedPrimitiveRoot p n) =
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)) :=
  padicCompletedUnitFrobeniusLiftAlgHom_primitiveRoot p n u

/-- The direct unit-indexed completed Frobenius lift is surjective. -/
theorem padicCompletedUnitFrobeniusLift_surjective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    Function.Surjective (padicCompletedUnitFrobeniusLift p n u) := by
  let E := padicCompletedUnramifiedField p
  let L := padicCompletedLevelField p n
  let y : L :=
    ((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) : L)
  let σ : L →+* L := padicCompletedUnitFrobeniusLift p n u
  let R : Subring L := σ.range
  have hbase (b : E) : algebraMap E L b ∈ R := by
    refine
      ⟨algebraMap E L
        ((padicCompletedUnramifiedFrobenius p).symm b), ?_⟩
    change σ
        (algebraMap E L
          ((padicCompletedUnramifiedFrobenius p).symm b)) =
      algebraMap E L b
    rw [show σ = padicCompletedUnitFrobeniusLift p n u by rfl,
      padicCompletedUnitFrobeniusLift_algebraMap,
      (padicCompletedUnramifiedFrobenius p).apply_symm_apply]
  let S : Subalgebra E L :=
    { R with
      algebraMap_mem' := hbase }
  have hy : y ∈ S := by
    refine ⟨padicCompletedPrimitiveRoot p n, ?_⟩
    exact padicCompletedUnitFrobeniusLift_primitiveRoot p n u
  have hle : Algebra.adjoin E ({y} : Set L) ≤ S := by
    apply Algebra.adjoin_le
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hy
  rw [show Algebra.adjoin E ({y} : Set L) = ⊤ by
        simpa only [E, L, y] using
          padicCompletedStandardPrimitivePointUnitAction_adjoin_eq_top
            p n u] at hle
  have hS : S = ⊤ := top_unique hle
  intro z
  have hz : z ∈ S := by rw [hS]; trivial
  exact hz

/-- The actual field automorphism extending arithmetic Frobenius and acting
on the primitive root by the direct completed standard unit action. -/
noncomputable def padicCompletedUnitFrobeniusLiftEquiv
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedLevelField p n ≃+*
      padicCompletedLevelField p n :=
  RingEquiv.ofBijective (padicCompletedUnitFrobeniusLift p n u)
    ⟨(padicCompletedUnitFrobeniusLift p n u).injective,
      padicCompletedUnitFrobeniusLift_surjective p n u⟩

/-- The unit-indexed Frobenius-lift equivalence acts on completed base
scalars by arithmetic Frobenius. -/
@[simp]
theorem padicCompletedUnitFrobeniusLiftEquiv_algebraMap
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (b : padicCompletedUnramifiedField p) :
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) b) =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (padicCompletedUnramifiedFrobenius p b) :=
  padicCompletedUnitFrobeniusLift_algebraMap p n u b

/-- The unit-indexed Frobenius-lift equivalence acts on the primitive root
by the direct completed standard unit action. -/
@[simp]
theorem padicCompletedUnitFrobeniusLiftEquiv_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (padicCompletedPrimitiveRoot p n) =
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)) :=
  padicCompletedUnitFrobeniusLift_primitiveRoot p n u

end LubinTate

end
