/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction
public import Mathlib.GroupTheory.Nilpotent

/-! # Sylow -/

@[expose] public section
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity theorem: the Sylow step in the first reduction

This file formalizes the source-producing group-theoretic part of the
first reduction.  For a Sylow `p`-subgroup `P` of the actual
finite quotient `G(L/K)`, the already constructed fixed field `M = L^P`
is an actual (not necessarily Galois over `K`) intermediate field.  The
actual quotient `G(L/M)` is a `p`-group and hence solvable, while
`[M:K] = (G(L/K) : P)` is prime to `p`.

For an abelian group `B`, multiplication by `[M:K]` is therefore
surjective on every Sylow `p`-subgroup of `B`, without assuming that the
ambient group is finite.  Equivalently, that Sylow subgroup lies in the
image of the `[M:K]`-fold map.  In the abstract reciprocity theorem the ambient norm quotient is
only known at this point to have bounded exponent; its individual cyclic
subgroups are finite.  This avoids using the desired reciprocity
surjectivity to prove finiteness.  No reciprocity surjectivity or
the finite reciprocity equivalence comparison is assumed here.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-! ## The fixed field of a Sylow subgroup -/

/-- For `M = L^P`, the actual lower quotient `G(L/M)` is a `p`-group.
This is the identification `G(L/M) \cong P`, applied to an actual
Sylow subgroup of the actual finite quotient `G(L/K)`. -/
theorem abstractReciprocity_sylow_lowerQuotient_isPGroup
    (L : FiniteGaloisSubextension K) {p : ℕ}
    (P : Sylow p L.extensionQuotient) :
    IsPGroup p
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        extensionSubgroup
          (L.intermediateField (P : Subgroup L.extensionQuotient)) L.field
          (L.field_le_intermediateField
            (P : Subgroup L.extensionQuotient))) := by
  exact P.isPGroup'.of_equiv
    (L.lowerQuotientEquiv (P : Subgroup L.extensionQuotient)).symm

section SylowSolvability

local notation "IsSolvable" => Group.IsSolvable

/-- Consequently, the actual extension `L/M` cut out by a Sylow subgroup
is solvable.  Mathlib proves this by the standard chain
finite `p`-group `\Rightarrow` nilpotent `\Rightarrow` solvable. -/
theorem abstractReciprocity_sylow_lowerQuotient_isSolvable
    (L : FiniteGaloisSubextension K) {p : ℕ} [Fact p.Prime]
    (P : Sylow p L.extensionQuotient) :
    IsSolvable
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        extensionSubgroup
          (L.intermediateField (P : Subgroup L.extensionQuotient)) L.field
          (L.field_le_intermediateField
            (P : Subgroup L.extensionQuotient))) := by
  let : Finite
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        extensionSubgroup
          (L.intermediateField (P : Subgroup L.extensionQuotient)) L.field
          (L.field_le_intermediateField
            (P : Subgroup L.extensionQuotient))) :=
    L.extension_over_intermediate_finite
      (P : Subgroup L.extensionQuotient)
  let : Group.IsNilpotent
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        extensionSubgroup
          (L.intermediateField (P : Subgroup L.extensionQuotient)) L.field
          (L.field_le_intermediateField
            (P : Subgroup L.extensionQuotient))) :=
    (L.abstractReciprocity_sylow_lowerQuotient_isPGroup P).isNilpotent
  change Group.IsSolvable
    ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
      extensionSubgroup
        (L.intermediateField (P : Subgroup L.extensionQuotient)) L.field
        (L.field_le_intermediateField (P : Subgroup L.extensionQuotient)))
  infer_instance

end SylowSolvability

/-- The degree of the actual fixed field `M = L^P` over `K` is the index
of `P` in `G(L/K)`.  No normality of `P`, and hence none of `M/K`, is
used. -/
theorem abstractReciprocity_sylow_intermediateDegree_eq_index
    (L : FiniteGaloisSubextension K) {p : ℕ}
    (P : Sylow p L.extensionQuotient) :
    (L.intermediateFiniteAbstractExtension
      (P : Subgroup L.extensionQuotient)).degree =
      (P : Subgroup L.extensionQuotient).index := by
  rw [← (L.intermediateFiniteAbstractExtension
    (P : Subgroup L.extensionQuotient)).extensionSubgroup_index_eq_degree]
  change (extensionSubgroup K
    (L.intermediateField (P : Subgroup L.extensionQuotient))
      (L.intermediateField_le_base (P : Subgroup L.extensionQuotient))).index = _
  rw [L.extensionSubgroup_intermediateField_eq
    (P : Subgroup L.extensionQuotient)]
  exact (P : Subgroup L.extensionQuotient).index_comap_of_surjective
    (QuotientGroup.mk'_surjective
      (extensionSubgroup K L.field L.below))

/-- Hence the actual degree `[M:K]` is prime to the chosen Sylow prime
`p`, as asserted. -/
theorem abstractReciprocity_sylow_intermediateDegree_coprime
    (L : FiniteGaloisSubextension K) {p : ℕ} [Fact p.Prime]
    (P : Sylow p L.extensionQuotient) :
    Nat.Coprime
      (L.intermediateFiniteAbstractExtension
        (P : Subgroup L.extensionQuotient)).degree p := by
  rw [L.abstractReciprocity_sylow_intermediateDegree_eq_index P]
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  exact P.not_dvd_index

/-! ## Sylow subgroups in a possibly infinite abelian target -/

/-- Let `S` be a Sylow `p`-subgroup of an abelian group `B`.  If
`n` is prime to `p`, then `S` lies in the range of the additive `n`-fold
map on `B`.

The proof follows the sentence literally: `S` has `p`-power
order, so the `n`-fold map is a bijection on `S`; a preimage in `S` is in
particular a preimage in `B`. -/
theorem sylowAddSubgroup_le_nsmul_range_of_coprime
    {B : Type*} [AddCommGroup B]
    {p n : ℕ} [Fact p.Prime]
    (S : Sylow p (Multiplicative B)) (hn : Nat.Coprime n p) :
    Subgroup.toAddSubgroup'
        (S : Subgroup (Multiplicative B)) ≤
      (nsmulAddMonoidHom (α := B) n).range := by
  intro x hx
  let xS : S := ⟨Multiplicative.ofAdd x, hx⟩
  let e : S ≃ S := S.isPGroup'.powEquiv hn.symm
  let yS : S := e.symm xS
  refine ⟨yS.1.toAdd, ?_⟩
  have hy : yS ^ n = xS := e.apply_symm_apply xS
  have hyval : yS.1 ^ n = xS.1 := congrArg Subtype.val hy
  simpa [xS] using congrArg Multiplicative.toAdd hyval

/-- The exact specialization: for `M = L^P`, every Sylow
`p`-subgroup of an abelian group `B` lies in the image of the
`[M:K]`-fold map on `B`.  This is the group-theoretic input which the
identity `N_{M/K} ∘ i = [M:K]` later converts into norm-map containment. -/
theorem abstractReciprocity_sylowAddSubgroup_le_intermediateDegree_nsmul_range
    (L : FiniteGaloisSubextension K) {p : ℕ} [Fact p.Prime]
    (P : Sylow p L.extensionQuotient)
    {B : Type*} [AddCommGroup B]
    (S : Sylow p (Multiplicative B)) :
    Subgroup.toAddSubgroup'
        (S : Subgroup (Multiplicative B)) ≤
      (nsmulAddMonoidHom (α := B)
        (L.intermediateFiniteAbstractExtension
          (P : Subgroup L.extensionQuotient)).degree).range := by
  exact sylowAddSubgroup_le_nsmul_range_of_coprime S
    (L.abstractReciprocity_sylow_intermediateDegree_coprime P)

end FiniteGaloisSubextension

end
end ClassFormation
