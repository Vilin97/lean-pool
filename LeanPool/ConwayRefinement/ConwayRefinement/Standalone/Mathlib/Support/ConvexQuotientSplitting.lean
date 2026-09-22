/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Support.ArchimedeanQuotient
public import Mathlib.Algebra.Order.Module.Archimedean
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Projection

/-!
# Ordered splitting by a convex subspace

A subspace of a vector space over a field has an algebraic complement. If the ambient additive
group is linearly ordered and the subspace is convex, this complement presents the ambient group
as the lexicographic product of the ordered quotient and the subspace. The quotient coordinate is
dominant. This additive splitting is what permits Hahn series to be regrouped by quotient cosets
without introducing a cocycle.

For a family of finite Archimedean classes, `FiniteArchimedeanClass.tailSubmodule` equips their
common tail kernel with its natural subspace structure. Thus the generic splitting applies to the
limit-tail quotients used in the Cantor–Bendixson argument.
-/

open Set

universe u v

public noncomputable section

namespace ConwayRefinement.Standalone.Hahn

namespace FiniteArchimedeanClass

variable (K : Type v) {G : Type u}
variable [Field K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [PosSMulMono K G]

/-- The common tail kernel of `T`, equipped with its natural `K`-subspace structure. -/
def tailSubmodule (T : Set (FiniteArchimedeanClass G)) : Submodule K G where
  __ := tailKernel T
  smul_mem' k x hx := by
    apply mem_tailKernel_iff.mpr
    intro c
    exact (mem_tailKernel_iff.mp hx c).trans (ArchimedeanClass.mk_le_mk_smul x k)

/-- Membership in the common-tail subspace is membership in the underlying common-tail
kernel. -/
@[simp]
theorem mem_tailSubmodule_iff {T : Set (FiniteArchimedeanClass G)} {x : G} :
    x ∈ tailSubmodule K T ↔ x ∈ tailKernel T :=
  (Iff.rfl)

@[simp]
theorem tailSubmodule_toAddSubgroup (T : Set (FiniteArchimedeanClass G)) :
    (tailSubmodule K T).toAddSubgroup = tailKernel T :=
  (rfl)

/-- The subspace form of the common tail kernel is convex. -/
instance tailSubmodule_isConvex (T : Set (FiniteArchimedeanClass G)) :
    ConvexQuotient.IsConvex (tailSubmodule K T).toAddSubgroup := by
  rw [tailSubmodule_toAddSubgroup K T]
  infer_instance

end FiniteArchimedeanClass

namespace Submodule

variable {K : Type v} {G : Type u}
variable [Field K] [AddCommGroup G] [Module K G]
variable [LinearOrder G] [IsOrderedAddMonoid G]

variable (P : Submodule K G)

/-- A chosen linear complement of `P`. -/
noncomputable def linearComplement : Submodule K G :=
  Classical.choose P.exists_isCompl

omit [LinearOrder G] [IsOrderedAddMonoid G] in
/-- The chosen complement is complementary to `P`. -/
theorem isCompl_linearComplement : IsCompl P (linearComplement P) :=
  Classical.choose_spec P.exists_isCompl

/-- The quotient by `P`, identified linearly with the chosen complement. -/
noncomputable def quotientLinearEquivComplement : (G ⧸ P) ≃ₗ[K] linearComplement P :=
  P.quotientEquivOfIsCompl (linearComplement P) (isCompl_linearComplement P)

/-- Reassemble a quotient coordinate and a `P`-coordinate in the ambient vector space. -/
noncomputable def quotientProdLinearEquiv : ((G ⧸ P) × P) ≃ₗ[K] G :=
  ((quotientLinearEquivComplement P).prodCongr (LinearEquiv.refl K P)).trans
    ((linearComplement P).prodEquivOfIsCompl P (isCompl_linearComplement P).symm)

omit [LinearOrder G] [IsOrderedAddMonoid G] in
/-- Reassembly has the prescribed quotient coordinate. -/
@[simp]
theorem mk_quotientProdLinearEquiv (x : (G ⧸ P) × P) :
    _root_.Submodule.Quotient.mk (quotientProdLinearEquiv P x) = x.1 := by
  rw [quotientProdLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    Submodule.coe_prodEquivOfIsCompl']
  change QuotientAddGroup.mk' P.toAddSubgroup
    ((quotientLinearEquivComplement P x.1 : G) + (x.2 : G)) = x.1
  rw [map_add, show QuotientAddGroup.mk' P.toAddSubgroup (x.2 : G) = 0 by
    exact (Submodule.Quotient.mk_eq_zero P).mpr x.2.property, add_zero]
  exact P.mk_quotientEquivOfIsCompl_apply (isCompl_linearComplement P) x.1

omit [LinearOrder G] [IsOrderedAddMonoid G] in
/-- Reassembling a zero quotient coordinate returns the subspace coordinate. -/
@[simp]
theorem quotientProdLinearEquiv_zero_left (p : P) :
    quotientProdLinearEquiv P (0, p) = (p : G) := by
  rw [quotientProdLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    Submodule.coe_prodEquivOfIsCompl']
  simp [quotientLinearEquivComplement]

/-- The linear order on the quotient by the convex exponent submodule. -/
noncomputable local instance quotientLinearOrder [ConvexQuotient.IsConvex P.toAddSubgroup] :
    LinearOrder (G ⧸ P) :=
  ConvexQuotient.instLinearOrder (H := P.toAddSubgroup)

local instance submoduleIsOrderedAddMonoid : IsOrderedAddMonoid P :=
  AddSubgroup.instIsOrderedAddMonoid P.toAddSubgroup

/-- A linearly ordered vector space is the lexicographic product of the quotient by a convex
subspace and that subspace. The quotient is the dominant coordinate. -/
noncomputable def quotientLexEquiv [ConvexQuotient.IsConvex P.toAddSubgroup] :
    ((G ⧸ P) ×ₗ P) ≃+o G :=
  { (quotientProdLinearEquiv P).toAddEquiv with
    map_le_map_iff' := by
      intro x y
      apply (show StrictMono
          (fun x : ((G ⧸ P) ×ₗ P) ↦ quotientProdLinearEquiv P (ofLex x)) by
        intro x y hxy
        rcases Prod.Lex.lt_iff.mp hxy with houter | ⟨houter, hinner⟩
        · have hq :
              ((quotientProdLinearEquiv P (ofLex x) : G) : G ⧸ P.toAddSubgroup) <
                ((quotientProdLinearEquiv P (ofLex y) : G) : G ⧸ P.toAddSubgroup) := by
            change (_root_.Submodule.Quotient.mk (quotientProdLinearEquiv P (ofLex x)) :
                G ⧸ P) <
              _root_.Submodule.Quotient.mk (quotientProdLinearEquiv P (ofLex y))
            rw [mk_quotientProdLinearEquiv, mk_quotientProdLinearEquiv]
            exact houter
          exact ConvexQuotient.lt_of_mk_lt_mk hq
        · change quotientProdLinearEquiv P (ofLex x) < quotientProdLinearEquiv P (ofLex y)
          simp only [quotientProdLinearEquiv, LinearEquiv.trans_apply,
            LinearEquiv.prodCongr_apply, Submodule.coe_prodEquivOfIsCompl']
          rw [show (ofLex x).1 = (ofLex y).1 from houter]
          simpa only [LinearEquiv.refl_apply, add_comm] using
            add_lt_add_left (show ((ofLex x).2 : G) < ((ofLex y).2 : G) from hinner)
              (quotientLinearEquivComplement P (ofLex y).1 : G)).le_iff_le }

@[simp]
theorem quotientLexEquiv_apply [ConvexQuotient.IsConvex P.toAddSubgroup]
    (x : (G ⧸ P) ×ₗ P) :
    quotientLexEquiv P x = quotientProdLinearEquiv P (ofLex x) :=
  (rfl)

end Submodule

namespace FiniteArchimedeanClass

variable (K : Type v) {G : Type u}
variable [Field K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [PosSMulMono K G]

/-- The ambient group split lexicographically into the quotient by its tail subspace and that
subspace. Its additive subgroup is propositionally equal to `tailKernel T`. -/
noncomputable def tailQuotientLexEquiv (T : Set (FiniteArchimedeanClass G)) :
    ((G ⧸ (tailSubmodule K T).toAddSubgroup) ×ₗ tailSubmodule K T) ≃+o G :=
  Submodule.quotientLexEquiv (tailSubmodule K T)

end FiniteArchimedeanClass

end ConwayRefinement.Standalone.Hahn
