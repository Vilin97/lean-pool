/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.MaxAddDegree
public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Associated graded ring of a max-additive degree

For a max-additive degree `ν` and a grade `m`, the homogeneous component is the additive
quotient

`ν.filtrationLE m / ν.filtrationLT m`.

The strict filtration is represented inside the weak filtration by `lowerFiltration`. The mixed
strict product estimates derived from submultiplicativity make representative multiplication well
defined on these quotients. Their direct sum is `MaxAddDegree.AssociatedGraded ν` and inherits a
commutative ring structure. Exact multiplicativity is not needed for the construction; it enters
only where the graded ring is shown to be a domain.

This quotient-first construction follows the quotient description given after LM24, Proposition
4.2.6. In particular, zero in every homogeneous component is the entire strict filtration, not
only the literal zero representative. The printed representative-dependent branch in LM24,
Definition 4.2.4 is not used;
`ConwayRefinement.Algebra.Valuation.Tests.AssociatedGraded` gives a compiled counterexample to
its commutativity.
-/

universe u v

public noncomputable section

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

/-- The additive subgroup of elements of degree at most `m`. -/
def filtrationLE (ν : MaxAddDegree R M) (m : M) : AddSubgroup R where
  carrier := {x | ν x ≤ m}
  zero_mem' := by simp
  add_mem' {x y} hx hy := (ν.map_add_le_max x y).trans (max_le hx hy)
  neg_mem' {x} hx := by simpa using hx

/-- The additive subgroup of elements of degree strictly below `m`. -/
def filtrationLT (ν : MaxAddDegree R M) (m : M) : AddSubgroup R where
  carrier := {x | ν x < m}
  zero_mem' := by simp
  add_mem' {x y} hx hy := (ν.map_add_le_max x y).trans_lt (max_lt hx hy)
  neg_mem' {x} hx := by simpa using hx

omit [IsOrderedCancelAddMonoid M] in
@[simp]
theorem mem_filtrationLE_iff (ν : MaxAddDegree R M) (m : M) (x : R) :
    x ∈ ν.filtrationLE m ↔ ν x ≤ m :=
  Iff.rfl

omit [IsOrderedCancelAddMonoid M] in
@[simp]
theorem mem_filtrationLT_iff (ν : MaxAddDegree R M) (m : M) (x : R) :
    x ∈ ν.filtrationLT m ↔ ν x < m :=
  Iff.rfl

omit [IsOrderedCancelAddMonoid M] in
theorem filtrationLT_le_filtrationLE (ν : MaxAddDegree R M) (m : M) :
    ν.filtrationLT m ≤ ν.filtrationLE m :=
  fun x hx ↦ show ν x ≤ m from hx.le

theorem degree_mul_le_add {ν : MaxAddDegree R M} {m n : M} {x y : R}
    (hx : ν x ≤ m) (hy : ν y ≤ n) :
    ν (x * y) ≤ m + n :=
  (ν.map_mul_le_add x y).trans (add_le_add hx hy)

theorem degree_mul_lt_add_of_lt_of_le {ν : MaxAddDegree R M} {m n : M} {x y : R}
    (hx : ν x < m) (hy : ν y ≤ n) :
    ν (x * y) < m + n := by
  apply (ν.map_mul_le_add x y).trans_lt
  by_cases hybot : ν y = ⊥
  · simp [hybot]
  · exact WithBot.add_lt_add_of_lt_of_le hybot hx hy

theorem degree_mul_lt_add_of_le_of_lt {ν : MaxAddDegree R M} {m n : M} {x y : R}
    (hx : ν x ≤ m) (hy : ν y < n) :
    ν (x * y) < m + n := by
  apply (ν.map_mul_le_add x y).trans_lt
  by_cases hxbot : ν x = ⊥
  · simp [hxbot]
  · exact WithBot.add_lt_add_of_le_of_lt hxbot hx hy

/-- Multiplication by a fixed weakly filtered representative. -/
def mulFiltrationLE (ν : MaxAddDegree R M) {m n : M}
    (x : ν.filtrationLE m) : ν.filtrationLE n →+ ν.filtrationLE (m + n) where
  toFun y := ⟨(x : R) * (y : R), degree_mul_le_add x.2 y.2⟩
  map_zero' := by ext; exact mul_zero (x : R)
  map_add' y z := by ext; exact mul_add (x : R) (y : R) (z : R)

@[simp]
theorem coe_mulFiltrationLE (ν : MaxAddDegree R M) {m n : M}
    (x : ν.filtrationLE m) (y : ν.filtrationLE n) :
    (ν.mulFiltrationLE x y : R) = (x : R) * (y : R) :=
  (rfl)

/-- The strict filtration, regarded as a subgroup of the weak filtration at the same grade. -/
def lowerFiltration (ν : MaxAddDegree R M) (m : M) :
    AddSubgroup (ν.filtrationLE m) :=
  (ν.filtrationLT m).comap (ν.filtrationLE m).subtype

omit [IsOrderedCancelAddMonoid M] in
@[simp]
theorem mem_lowerFiltration_iff (ν : MaxAddDegree R M) (m : M)
    (x : ν.filtrationLE m) :
    x ∈ ν.lowerFiltration m ↔ ν x < m := by
  rw [lowerFiltration]
  exact mem_filtrationLT_iff ν m x

/-- The homogeneous associated-graded component at `m`.

A `def` rather than an `abbrev`, with instances supplied below: every graded object here is built
from components, and a reducible head sends each instance search down through `filtrationLE` into
the subring of `R`. -/
@[expose] def Component (ν : MaxAddDegree R M) (m : M) : Type u :=
  ν.filtrationLE m ⧸ ν.lowerFiltration m

instance (ν : MaxAddDegree R M) (m : M) : AddCommGroup (ν.Component m) :=
  inferInstanceAs (AddCommGroup (ν.filtrationLE m ⧸ ν.lowerFiltration m))

/-- The quotient map from the weak filtration to its homogeneous component. -/
def componentMk (ν : MaxAddDegree R M) (m : M) :
    ν.filtrationLE m →+ ν.Component m :=
  QuotientAddGroup.mk' (ν.lowerFiltration m)

/-- The class of a representative. -/
instance (ν : MaxAddDegree R M) (m : M) : CoeTC (ν.filtrationLE m) (ν.Component m) :=
  ⟨QuotientAddGroup.mk⟩

omit [IsOrderedCancelAddMonoid M] in
/-- Every element of a homogeneous component is the class of a representative, with the motive
on the component rather than on the underlying quotient. -/
@[elab_as_elim]
theorem componentInductionOn {ν : MaxAddDegree R M} {m : M}
    {motive : ν.Component m → Prop} (x : ν.Component m)
    (H : ∀ b : ν.filtrationLE m, motive (ν.componentMk m b)) :
    motive x :=
  QuotientAddGroup.induction_on x H

omit [IsOrderedCancelAddMonoid M] in
@[simp]
theorem coe_component_eq_componentMk (ν : MaxAddDegree R M) (m : M)
    (x : ν.filtrationLE m) :
    (x : ν.Component m) = ν.componentMk m x :=
  (rfl)

omit [IsOrderedCancelAddMonoid M] in
@[simp]
theorem componentMk_eq_zero_iff (ν : MaxAddDegree R M) (m : M)
    (x : ν.filtrationLE m) :
    ν.componentMk m x = 0 ↔ ν x < m := by
  change (QuotientAddGroup.mk x :
      (ν.filtrationLE m) ⧸ ν.lowerFiltration m) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  exact mem_lowerFiltration_iff ν m x

omit [IsOrderedCancelAddMonoid M] in
/-- Homogeneous quotient constructors with equal grades and equal representatives are
heterogeneously equal. -/
theorem componentMk_heq_of_grade_eq_of_coe_eq (ν : MaxAddDegree R M) {m n : M}
    (h : m = n) (x : ν.filtrationLE m) (y : ν.filtrationLE n)
    (hxy : (x : R) = (y : R)) :
    HEq (ν.componentMk m x) (ν.componentMk n y) := by
  subst n
  apply heq_of_eq
  apply congrArg (ν.componentMk m)
  exact Subtype.ext hxy

omit [IsOrderedCancelAddMonoid M] in
/-- Two representatives have the same homogeneous class exactly when their difference lies in
the strict filtration. -/
theorem componentMk_eq_componentMk_iff (ν : MaxAddDegree R M) (m : M)
    (x y : ν.filtrationLE m) :
    ν.componentMk m x = ν.componentMk m y ↔ ν ((x : R) - (y : R)) < m := by
  rw [← sub_eq_zero, ← map_sub, ν.componentMk_eq_zero_iff]
  rfl

omit [IsOrderedCancelAddMonoid M] in
/-- Homogeneous classes at equal grades whose representatives differ by an element of the
strict filtration are heterogeneously equal. -/
theorem componentMk_heq_of_grade_eq_of_sub_lt (ν : MaxAddDegree R M) {m n : M}
    (hmn : m = n) (x : ν.filtrationLE m) (y : ν.filtrationLE n)
    (hxy : ν ((x : R) - (y : R)) < m) :
    HEq (ν.componentMk m x) (ν.componentMk n y) := by
  subst n
  apply heq_of_eq
  rw [ν.componentMk_eq_componentMk_iff]
  exact hxy

omit [IsOrderedCancelAddMonoid M] in
/-- Heterogeneously equal homogeneous classes at equal grades have representatives differing by
an element of the strict filtration. -/
theorem sub_lt_of_componentMk_heq (ν : MaxAddDegree R M) {m n : M}
    (hmn : m = n) (x : ν.filtrationLE m) (y : ν.filtrationLE n)
    (hxy : HEq (ν.componentMk m x) (ν.componentMk n y)) :
    ν ((x : R) - (y : R)) < m := by
  subst n
  rw [← ν.componentMk_eq_componentMk_iff]
  exact eq_of_heq hxy

/-- Multiplication followed by projection to a homogeneous component. -/
private def mulRepresentative (ν : MaxAddDegree R M) {m n : M}
    (x : ν.filtrationLE m) : ν.filtrationLE n →+ ν.Component (m + n) :=
  (ν.componentMk (m + n)).comp (ν.mulFiltrationLE x)

private theorem lowerFiltration_le_mulRepresentative_ker
    (ν : MaxAddDegree R M) {m n : M}
    (x : ν.filtrationLE m) :
    ν.lowerFiltration n ≤ (ν.mulRepresentative x).ker := by
  intro y hy
  rw [AddMonoidHom.mem_ker, mulRepresentative, AddMonoidHom.comp_apply,
    componentMk_eq_zero_iff]
  simpa only [coe_mulFiltrationLE, WithBot.coe_add] using
    degree_mul_lt_add_of_le_of_lt
      ((mem_filtrationLE_iff ν m x).mp x.2)
      ((mem_lowerFiltration_iff ν n y).mp hy)

/-- Multiplication by a representative, descended in the right argument. -/
private def mulRight (ν : MaxAddDegree R M) {m n : M} (x : ν.filtrationLE m) :
    ν.Component n →+ ν.Component (m + n) :=
  QuotientAddGroup.lift (ν.lowerFiltration n) (ν.mulRepresentative x)
    (ν.lowerFiltration_le_mulRepresentative_ker x)

@[simp]
private theorem mulRight_componentMk (ν : MaxAddDegree R M) {m n : M}
    (x : ν.filtrationLE m) (y : ν.filtrationLE n) :
    ν.mulRight x (ν.componentMk n y) =
      ν.componentMk (m + n) (ν.mulFiltrationLE x y) := by
  rfl

/-- The additive dependence of descended multiplication on its left representative. -/
private def mulLeftRepresentative (ν : MaxAddDegree R M) {m n : M} :
    ν.filtrationLE m →+ (ν.Component n →+ ν.Component (m + n)) where
  toFun := ν.mulRight
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H y =>
      change ν.mulRight (0 : ν.filtrationLE m) (ν.componentMk n y) = 0
      rw [mulRight_componentMk]
      rw [componentMk_eq_zero_iff]
      simp
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    induction z using QuotientAddGroup.induction_on with
    | H z =>
      change ν.mulRight (x + y) (ν.componentMk n z) =
        ν.mulRight x (ν.componentMk n z) + ν.mulRight y (ν.componentMk n z)
      rw [mulRight_componentMk, mulRight_componentMk, mulRight_componentMk]
      rw [← map_add]
      apply congrArg (ν.componentMk (m + n))
      apply Subtype.ext
      simp only [coe_mulFiltrationLE, AddSubgroup.coe_add, add_mul]

private theorem lowerFiltration_le_mulLeftRepresentative_ker
    (ν : MaxAddDegree R M) {m n : M} :
    ν.lowerFiltration m ≤ (ν.mulLeftRepresentative (m := m) (n := n)).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  apply AddMonoidHom.ext
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H y =>
    change ν.mulRight x (ν.componentMk n y) = 0
    rw [mulRight_componentMk]
    apply (componentMk_eq_zero_iff ν (m + n) _).mpr
    simpa only [coe_mulFiltrationLE, WithBot.coe_add] using
      degree_mul_lt_add_of_lt_of_le
        ((mem_lowerFiltration_iff ν m x).mp hx)
        ((mem_filtrationLE_iff ν n y).mp y.2)

/-- Homogeneous multiplication on associated-graded components. -/
private def componentMulHom (ν : MaxAddDegree R M) {m n : M} :
    ν.Component m →+ (ν.Component n →+ ν.Component (m + n)) :=
  QuotientAddGroup.lift (ν.lowerFiltration m)
    (ν.mulLeftRepresentative (m := m) (n := n))
    (ν.lowerFiltration_le_mulLeftRepresentative_ker (m := m) (n := n))

/-- Multiplication of two homogeneous associated-graded elements. -/
def componentMul (ν : MaxAddDegree R M) {m n : M}
    (x : ν.Component m) (y : ν.Component n) : ν.Component (m + n) :=
  ν.componentMulHom x y

private theorem componentMul_eq (ν : MaxAddDegree R M) {m n : M}
    (x : ν.Component m) (y : ν.Component n) :
    ν.componentMul x y = ν.componentMulHom x y :=
  (rfl)

@[simp]
theorem zero_componentMul (ν : MaxAddDegree R M) {m n : M}
    (y : ν.Component n) :
    ν.componentMul (0 : ν.Component m) y = 0 := by
  rw [componentMul_eq]
  exact DFunLike.congr_fun (ν.componentMulHom (m := m) (n := n)).map_zero y

@[simp]
theorem componentMul_zero (ν : MaxAddDegree R M) {m n : M}
    (x : ν.Component m) :
    ν.componentMul x (0 : ν.Component n) = 0 := by
  rw [componentMul_eq]
  exact (ν.componentMulHom x).map_zero

@[simp]
theorem componentMul_componentMk (ν : MaxAddDegree R M) {m n : M}
    (x : ν.filtrationLE m) (y : ν.filtrationLE n) :
    ν.componentMul (ν.componentMk m x) (ν.componentMk n y) =
      ν.componentMk (m + n) (ν.mulFiltrationLE x y) := by
  rfl

/-- The multiplicative identity in the grade-zero component. -/
def componentOne (ν : MaxAddDegree R M) : ν.Component 0 :=
  ν.componentMk 0 ⟨1, (ν.mem_filtrationLE_iff 0 1).mpr ν.map_one_le_zero⟩

omit [IsOrderedCancelAddMonoid M] in
@[simp]
theorem componentOne_eq_componentMk (ν : MaxAddDegree R M) :
    ν.componentOne =
      ν.componentMk 0 ⟨1, (ν.mem_filtrationLE_iff 0 1).mpr ν.map_one_le_zero⟩ :=
  (rfl)

/-- The multiplicative identity in the degree-zero component. -/
scoped instance (ν : MaxAddDegree R M) : GradedMonoid.GOne ν.Component where
  one := ν.componentOne

/-- Multiplication of homogeneous components, with their degrees added. -/
scoped instance (ν : MaxAddDegree R M) : GradedMonoid.GMul ν.Component where
  mul := ν.componentMul

open scoped MaxAddDegree

/-- The graded commutative ring structure on the components.

This instance is global so the ring structure on `AssociatedGraded` can be synthesized without
opening a scope. `GCommRing` also supplies `GMul` and `GOne` by projection; their standalone
instances remain scoped to avoid broad instance search on metavariable indices. -/
instance (ν : MaxAddDegree R M) : DirectSum.GCommRing ν.Component where
  mul := ν.componentMul
  one := ν.componentOne
  mul_zero := by
    intro i j x
    rw [componentMul_eq]
    exact (ν.componentMulHom x).map_zero
  zero_mul := by
    intro i j y
    rw [componentMul_eq]
    exact DFunLike.congr_fun (ν.componentMulHom (m := i) (n := j)).map_zero y
  mul_add := by
    intro i j x y z
    rw [componentMul_eq, componentMul_eq, componentMul_eq]
    exact (ν.componentMulHom x).map_add y z
  add_mul := by
    intro i j x y z
    rw [componentMul_eq, componentMul_eq, componentMul_eq]
    exact DFunLike.congr_fun
      ((ν.componentMulHom (m := i) (n := j)).map_add x y) z
  one_mul := by
    rintro ⟨m, x⟩
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      change GradedMonoid.mk (0 + m)
          (ν.componentMul ν.componentOne (ν.componentMk m x)) =
        GradedMonoid.mk m (ν.componentMk m x)
      rw [componentOne_eq_componentMk, componentMul_componentMk]
      apply Sigma.ext (zero_add m)
      apply componentMk_heq_of_grade_eq_of_coe_eq ν (zero_add m)
      simp
  mul_one := by
    rintro ⟨m, x⟩
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      change GradedMonoid.mk (m + 0)
          (ν.componentMul (ν.componentMk m x) ν.componentOne) =
        GradedMonoid.mk m (ν.componentMk m x)
      rw [componentOne_eq_componentMk, componentMul_componentMk]
      apply Sigma.ext (add_zero m)
      apply componentMk_heq_of_grade_eq_of_coe_eq ν (add_zero m)
      simp
  mul_assoc := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      induction y using QuotientAddGroup.induction_on with
      | H y =>
        induction z using QuotientAddGroup.induction_on with
        | H z =>
          change GradedMonoid.mk ((i + j) + k)
              (ν.componentMul
                (ν.componentMul (ν.componentMk i x) (ν.componentMk j y))
                (ν.componentMk k z)) =
            GradedMonoid.mk (i + (j + k))
              (ν.componentMul (ν.componentMk i x)
                (ν.componentMul (ν.componentMk j y) (ν.componentMk k z)))
          simp only [componentMul_componentMk]
          apply Sigma.ext (add_assoc i j k)
          apply componentMk_heq_of_grade_eq_of_coe_eq ν (add_assoc i j k)
          simp only [coe_mulFiltrationLE, mul_assoc]
  natCast := fun n ↦ n • ν.componentOne
  natCast_zero := by simp
  natCast_succ := by intros; simp [add_nsmul]
  intCast := fun z ↦ z • ν.componentOne
  intCast_ofNat := by intros; simp
  intCast_negSucc_ofNat := by intros; simp
  mul_comm := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      induction y using QuotientAddGroup.induction_on with
      | H y =>
        change GradedMonoid.mk (i + j)
            (ν.componentMul (ν.componentMk i x) (ν.componentMk j y)) =
          GradedMonoid.mk (j + i)
            (ν.componentMul (ν.componentMk j y) (ν.componentMk i x))
        simp only [componentMul_componentMk]
        apply Sigma.ext (add_comm i j)
        apply componentMk_heq_of_grade_eq_of_coe_eq ν (add_comm i j)
        simp only [coe_mulFiltrationLE, mul_comm]

/-- `GAlgebra` and the direct sum's ring and algebra instances all take a `GSemiring` argument,
and reaching it through `GCommRing` rebuilds the componentwise multiplication each time. -/
instance (ν : MaxAddDegree R M) : DirectSum.GSemiring ν.Component :=
  inferInstance

instance (ν : MaxAddDegree R M) : DirectSum.GCommSemiring ν.Component :=
  inferInstance

/-- The associated graded ring of a max-additive degree. -/
abbrev AssociatedGraded (ν : MaxAddDegree R M) :=
  DirectSum M ν.Component

/--
The homogeneous map obtained by quotient projection to grade `m`, followed by the direct-sum
inclusion of that component.
-/
def homogeneousMk (ν : MaxAddDegree R M) (m : M) :
    ν.filtrationLE m →+ ν.AssociatedGraded :=
  (DirectSum.of ν.Component m).comp (ν.componentMk m)

theorem homogeneousMk_apply (ν : MaxAddDegree R M) (m : M)
    (x : ν.filtrationLE m) :
    ν.homogeneousMk m x = DirectSum.of ν.Component m (ν.componentMk m x) :=
  (rfl)

@[simp]
theorem homogeneousMk_eq_zero_iff (ν : MaxAddDegree R M) (m : M)
    (x : ν.filtrationLE m) :
    ν.homogeneousMk m x = 0 ↔ ν x < m := by
  rw [ν.homogeneousMk_apply]
  constructor
  · intro hzero
    apply (ν.componentMk_eq_zero_iff m x).mp
    exact DirectSum.of_injective m (by simpa using hzero)
  · intro hlt
    rw [(ν.componentMk_eq_zero_iff m x).mpr hlt]
    exact (DirectSum.of ν.Component m).map_zero

@[simp]
theorem homogeneousMk_mul (ν : MaxAddDegree R M) {m n : M}
    (x : ν.filtrationLE m) (y : ν.filtrationLE n) :
    ν.homogeneousMk m x * ν.homogeneousMk n y =
      ν.homogeneousMk (m + n) (ν.mulFiltrationLE x y) := by
  rw [homogeneousMk, homogeneousMk, homogeneousMk, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, DirectSum.of_mul_of,
    show GradedMonoid.GMul.mul _ _ = ν.componentMul _ _ from rfl,
    componentMul_componentMk]

/-- Homogeneous classes multiply as expected whenever the target index is the sum of the source
indices and the supplied target representative is their product. -/
theorem homogeneousMk_mul_of_coe_eq (ν : MaxAddDegree R M) {m n p : M} (hp : p = m + n)
    (x : ν.filtrationLE m) (y : ν.filtrationLE n) (z : ν.filtrationLE p)
    (hz : (z : R) = (x : R) * (y : R)) :
    ν.homogeneousMk p z = ν.homogeneousMk m x * ν.homogeneousMk n y := by
  subst hp
  rw [homogeneousMk_mul]
  congr 1
  exact Subtype.ext (by rw [hz, coe_mulFiltrationLE])

/-- The grade-zero class of the multiplicative identity is the identity of the associated graded
ring. -/
@[simp]
theorem homogeneousMk_one (ν : MaxAddDegree R M) :
    ν.homogeneousMk 0 ⟨1, (ν.mem_filtrationLE_iff 0 1).mpr ν.map_one_le_zero⟩ = 1 := by
  rw [homogeneousMk_apply, ← componentOne_eq_componentMk]
  rfl

end MaxAddDegree
