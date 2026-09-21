/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.NullPoint
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperRealize

/-!
# The even ring acting on the odd part, and ℂ-points

The ordinary commutative ℂ-algebra structure of the even component
of a `RS.SuperCommAlgebra`, and the nilness of the odd-generated
ideal, are established in
[SuperRealize.lean](SuperRealize.lean) (`instCommRingEven`,
`instAlgebraEven`, `oddIdeal_le_nilradical`, `oddIdeal_ne_top`).
This module adds the two things Deligne's §4.5 ending consumes on
top of them.

* The odd component is a module over the even ring
  (`instModuleEvenOdd`), the action being the even-odd
  multiplication block, compatibly with the ambient ℂ-action
  (`instIsScalarTowerComplexEvenOdd`,
  `instSMulCommClassComplexEvenOdd`); the odd-odd block is
  bilinear for that action (`mulOO_smul_left`, `mulOO_smul_right`),
  which is what makes `oddIdeal` the image of the odd part under
  multiplication rather than merely its span.

* `RS.SuperPoint` — a super-algebra map to ℂ concentrated in even
  degree: a ℂ-algebra map off the even component killing every
  product of two odd elements.  Such a map is exactly a ℂ-algebra
  map off the odd-nil quotient (`SuperPoint.toQuotient`,
  `SuperPoint.ofQuotient`), so on a nonzero algebra of finite type
  one exists (`nonempty_superPoint`), by the Nullstellensatz input
  `RS.exists_algHom_complex` of
  [NullPoint.lean](NullPoint.lean).
-/

namespace RS

universe u u'

namespace SuperCommAlgebra

variable (S : SuperCommAlgebra.{u, u'})

/-! ## The odd component as a module over the even ring -/

/-- The odd component is a module over the even ring, the action
being the even-odd multiplication block: the module axioms are the
unit law `one_mul_o`, the associativity pattern `assoc_eeo` and the
ℂ-bilinearity of the block. -/
instance instModuleEvenOdd : Module S.even S.odd where
  smul x u := S.mulEO x u
  one_smul := S.one_mul_o
  mul_smul := S.assoc_eeo
  smul_zero x := map_zero (S.mulEO x)
  smul_add x u v := map_add (S.mulEO x) u v
  add_smul x y u := by
    show S.mulEO (x + y) u = S.mulEO x u + S.mulEO y u
    rw [map_add S.mulEO x y, LinearMap.add_apply]
  zero_smul u := by
    show S.mulEO 0 u = 0
    rw [map_zero S.mulEO, LinearMap.zero_apply]

/-- The scalar actions of ℂ and of the even ring on the odd
component are compatible: the even-odd block is ℂ-linear in its
even argument. -/
instance instIsScalarTowerComplexEvenOdd :
    IsScalarTower ℂ S.even S.odd where
  smul_assoc r x u := by
    show S.mulEO (r • x) u = r • S.mulEO x u
    rw [map_smul S.mulEO r x, LinearMap.smul_apply]

/-- The two scalar actions on the odd component commute: the
even-odd block is ℂ-linear in its odd argument. -/
instance instSMulCommClassComplexEvenOdd :
    SMulCommClass ℂ S.even S.odd where
  smul_comm r x u := (map_smul (S.mulEO x) r u).symm

/-- The odd-odd block is linear over the even ring in its left
argument. -/
theorem mulOO_smul_left (x : S.even) (u v : S.odd) :
    S.mulOO (x • u) v = x * S.mulOO u v := S.assoc_eoo x u v

/-- The odd-odd block is linear over the even ring in its right
argument. -/
theorem mulOO_smul_right (x : S.even) (u v : S.odd) :
    S.mulOO u (x • v) = x * S.mulOO u v := by
  have h : S.mulOO u (S.mulEO x v) = x * S.mulOO u v := by
    rw [← S.assoc_oeo u x v, ← S.comm_eo x u]
    exact S.assoc_eoo x u v
  exact h

/-! ## Nilness of the odd products, in ring form -/

/-- Each generator of the odd-generated ideal lies in it. -/
theorem mulOO_mem_oddIdeal (u v : S.odd) :
    S.mulOO u v ∈ S.oddIdeal :=
  Ideal.subset_span ⟨(u, v), rfl⟩

end SuperCommAlgebra

/-! ## ℂ-points concentrated in even degree -/

/-- A *ℂ-point* of a super-commutative ℂ-algebra: a map of
super-algebras to ℂ, which carries no odd component, so it is a
ℂ-algebra map off the even part annihilating every product of two
odd elements. -/
structure SuperPoint (S : SuperCommAlgebra.{u, u'}) where
  /-- The ℂ-algebra map on the even component. -/
  chi : S.even →ₐ[ℂ] ℂ
  /-- The odd degree is killed: products of odd elements go to
  zero. -/
  vanishing : ∀ u v : S.odd, chi (S.mulOO u v) = 0

namespace SuperPoint

variable {S : SuperCommAlgebra.{u, u'}}

/-- A point annihilates the whole odd-generated ideal, not only
its generators. -/
theorem apply_eq_zero_of_mem_oddIdeal (P : SuperPoint S)
    {x : S.even} (hx : x ∈ S.oddIdeal) : P.chi x = 0 := by
  have hle : S.oddIdeal ≤ RingHom.ker (P.chi : S.even →+* ℂ) := by
    rw [SuperCommAlgebra.oddIdeal, Ideal.span_le]
    rintro y ⟨⟨u, v⟩, rfl⟩
    exact RingHom.mem_ker.mpr (P.vanishing u v)
  exact RingHom.mem_ker.mp (hle hx)

/-- A point factors through the odd-nil quotient. -/
noncomputable def toQuotient (P : SuperPoint S) :
    (S.even ⧸ S.oddIdeal) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ S.oddIdeal P.chi fun _ hx =>
    P.apply_eq_zero_of_mem_oddIdeal hx

/-- A ℂ-algebra map off the odd-nil quotient is a point. -/
noncomputable def ofQuotient (S : SuperCommAlgebra.{u, u'})
    (f : (S.even ⧸ S.oddIdeal) →ₐ[ℂ] ℂ) : SuperPoint S where
  chi := f.comp (Ideal.Quotient.mkₐ ℂ S.oddIdeal)
  vanishing u v := by
    have hz : Ideal.Quotient.mk S.oddIdeal (S.mulOO u v) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (S.mulOO_mem_oddIdeal u v)
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hz, map_zero]

end SuperPoint

/-- **Existence of a ℂ-point** (Deligne §4.5, step (ii)): a
super-commutative ℂ-algebra with nonzero even part whose odd-nil
quotient is of finite type admits a ℂ-point.  The quotient is a
nonzero ordinary commutative ℂ-algebra of finite type
(`SuperCommAlgebra.nontrivial_quotient_oddIdeal`), so the
Nullstellensatz gives it a ℂ-algebra map to ℂ, which pulls back
along the quotient map. -/
theorem nonempty_superPoint (S : SuperCommAlgebra.{u, u'})
    [Nontrivial S.even]
    [Algebra.FiniteType ℂ (S.even ⧸ S.oddIdeal)] :
    Nonempty (SuperPoint S) :=
  haveI := S.nontrivial_quotient_oddIdeal
  (exists_algHom_complex (S.even ⧸ S.oddIdeal)).map (SuperPoint.ofQuotient S)

end RS
