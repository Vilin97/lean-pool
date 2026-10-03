/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.Invariant.Profinite

/-! # Profinite Invariant -/

@[expose] public section
namespace RamificationTheory

/-!
# Profinite invariant rings: normality on prime residue fields

The finite invariant-ring API proves that a prime residue extension is
normal. The residue-action exact sequence also needs the corresponding profinite
statement.  The proof is the same finite-orbit argument as in this construction: an
element of the discrete ring is fixed by an open normal subgroup, so its
orbit polynomial is computed in a finite quotient.
-/

noncomputable
section

open scoped Pointwise

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B]
variable [ContinuousSMul G B] [Algebra.IsInvariant A B G]

namespace Ideal.Quotient

attribute [local instance] Ideal.Quotient.field

include G

/-- Profinite version of `Ideal.Quotient.normal`.

Every element has a finite orbit because the action on `B` is continuous and
`B` is discrete.  Passing to an open normal subgroup fixing a representative
reduces the splitting calculation to the finite quotient action. -/
theorem normal_of_profinite
    (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P] :
    Normal (A ⧸ P) (B ⧸ Q) := by
  cases subsingleton_or_nontrivial B
  · cases ‹Q.IsMaximal›.ne_top (Subsingleton.elim _ _)
  have hIntegral : Algebra.IsIntegral A B :=
    Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  constructor
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨N, hN⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (stabilizer_isOpen G x) (MulAction.mem_stabilizer_iff.mpr (one_smul G x))
  let B' := FixedPoints.subalgebra A B N.1.1
  let x' : B' := ⟨x, fun g ↦ hN g.2⟩
  let j : B' →ₐ[A] B := B'.val
  have hjx : j x' = x := rfl
  let : Algebra.IsInvariant A B' (G ⧸ N.1.1) := inferInstance
  cases nonempty_fintype (G ⧸ N.1.1)
  obtain ⟨p, hp, _hdegree, hpmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic
      (Algebra.IsInvariant.charpoly_mem_lifts A B' (G ⧸ N.1.1) x')
      (MulSemiringAction.monic_charpoly (G ⧸ N.1.1) x')
  let qB : B →+* B ⧸ Q := Ideal.Quotient.mk Q
  let qB' : B' →+* B ⧸ Q := qB.comp j.toRingHom
  have hroot : Polynomial.aeval (Ideal.Quotient.mk Q x)
      (p.map (algebraMap A (A ⧸ P))) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    have hmap :
        (p.map (algebraMap A B')).map qB' =
          p.map ((algebraMap (A ⧸ P) (B ⧸ Q)).comp
            (Ideal.Quotient.mk P)) := by
      rw [Polynomial.map_map]
      apply congrArg (fun f : A →+* B ⧸ Q ↦ p.map f)
      ext a
      rfl
    calc
      Polynomial.eval (Ideal.Quotient.mk Q x)
          ((p.map (algebraMap A (A ⧸ P))).map
            (algebraMap (A ⧸ P) (B ⧸ Q))) =
          Polynomial.eval (Ideal.Quotient.mk Q x)
            ((p.map (algebraMap A B')).map qB') := by
        rw [hmap, Polynomial.map_map, Ideal.Quotient.algebraMap_eq]
      _ = 0 := by
        rw [hp, show Ideal.Quotient.mk Q x = qB' x' from rfl,
          Polynomial.eval_map_apply, MulSemiringAction.eval_charpoly, map_zero]
  have hdiv := minpoly.dvd (A ⧸ P) (Ideal.Quotient.mk Q x)
    (p := p.map (algebraMap A (A ⧸ P))) hroot
  refine Polynomial.Splits.of_dvd ?_ ?_ ((Polynomial.map_dvd_map' _).mpr hdiv)
  · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq A B', ← Polynomial.map_map, hp,
      MulSemiringAction.charpoly_eq, Polynomial.map_prod]
    exact Polynomial.Splits.prod
      (fun _ _ ↦ (Polynomial.Splits.X_sub_C _).map _)
  · exact ((hpmonic.map _).map _).ne_zero

end Ideal.Quotient

end

end RamificationTheory
