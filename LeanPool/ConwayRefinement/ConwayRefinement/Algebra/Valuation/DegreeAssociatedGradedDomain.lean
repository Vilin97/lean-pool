/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeInitialForm
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.QuotientDegree
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.LeadingGrade

/-!
# Domain criterion for the associated graded ring of a degree function

For a separated submultiplicative degree, every nonzero element has a nonzero homogeneous class
in its exact degree. If products of nonzero homogeneous components are nonzero, the
submultiplicative product inequality is therefore an equality. In particular, a domain associated
graded ring forces the original degree to be multiplicative.

Applied to the least-representative degree on a quotient ring `R ⧸ I`, this shows that `R ⧸ I`
is a domain whenever the associated graded ring of that degree is one. The canonical isomorphism
of that associated graded ring with a quotient of `gr_ν R` is constructed separately.
-/

universe u v

public noncomputable section

namespace MaxAddDegree

open scoped MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

/-- No two nonzero homogeneous classes have zero product. -/
def HomogeneousNoZeroDivisors (ν : MaxAddDegree R M) : Prop :=
  ∀ {m n : M} (x : ν.Component m) (y : ν.Component n),
    x ≠ 0 → y ≠ 0 → ν.componentMul x y ≠ 0

theorem homogeneousNoZeroDivisors_iff (ν : MaxAddDegree R M) :
    ν.HomogeneousNoZeroDivisors ↔
      ∀ {m n : M} (x : ν.Component m) (y : ν.Component n),
        x ≠ 0 → y ≠ 0 → ν.componentMul x y ≠ 0 :=
  Iff.rfl

/-- A domain associated graded ring has no homogeneous zero divisors. -/
theorem homogeneousNoZeroDivisors_of_isDomain (ν : MaxAddDegree R M)
    [IsDomain ν.AssociatedGraded] :
    ν.HomogeneousNoZeroDivisors := by
  rw [ν.homogeneousNoZeroDivisors_iff]
  intro m n x y hx hy hxy
  have hx' : DirectSum.of ν.Component m x ≠ 0 :=
    fun hzero ↦ hx (DirectSum.of_injective m (by simpa using hzero))
  have hy' : DirectSum.of ν.Component n y ≠ 0 :=
    fun hzero ↦ hy (DirectSum.of_injective n (by simpa using hzero))
  apply mul_ne_zero hx' hy'
  rw [DirectSum.of_mul_of,
    show GradedMonoid.GMul.mul x y = ν.componentMul x y from rfl, hxy]
  exact (DirectSum.of ν.Component (m + n)).map_zero

/-- A multiplicative degree has no nonzero homogeneous zero divisors. -/
theorem homogeneousNoZeroDivisors_of_isMultiplicative
    (ν : MaxAddDegree R M) [ν.IsMultiplicative] :
    ν.HomogeneousNoZeroDivisors := by
  rw [ν.homogeneousNoZeroDivisors_iff]
  intro m n x y hx hy
  induction x using QuotientAddGroup.induction_on with
  | H x =>
      induction y using QuotientAddGroup.induction_on with
      | H y =>
          rw [ν.coe_component_eq_componentMk] at hx
          rw [ν.coe_component_eq_componentMk] at hy
          have hxnotlt : ¬ν x < m :=
            fun hlt ↦ hx ((ν.componentMk_eq_zero_iff m x).mpr hlt)
          have hynotlt : ¬ν y < n :=
            fun hlt ↦ hy ((ν.componentMk_eq_zero_iff n y).mpr hlt)
          have hxdegree : ν x = (m : WithBot M) :=
            le_antisymm ((ν.mem_filtrationLE_iff m x).mp x.2) (le_of_not_gt hxnotlt)
          have hydegree : ν y = (n : WithBot M) :=
            le_antisymm ((ν.mem_filtrationLE_iff n y).mp y.2) (le_of_not_gt hynotlt)
          intro hzero
          rw [ν.coe_component_eq_componentMk, ν.coe_component_eq_componentMk] at hzero
          rw [ν.componentMul_componentMk, ν.componentMk_eq_zero_iff] at hzero
          simp only [ν.coe_mulFiltrationLE] at hzero
          rw [ν.map_mul, hxdegree, hydegree, WithBot.coe_add] at hzero
          exact lt_irrefl _ hzero

/-- Nonzero homogeneous classes of a multiplicative degree have nonzero product. -/
theorem componentMul_ne_zero (ν : MaxAddDegree R M) [ν.IsMultiplicative] {m n : M}
    (x : ν.Component m) (y : ν.Component n) (hx : x ≠ 0) (hy : y ≠ 0) :
    ν.componentMul x y ≠ 0 :=
  ν.homogeneousNoZeroDivisors_iff.mp ν.homogeneousNoZeroDivisors_of_isMultiplicative x y hx hy

/-- Multiplicativity of the degree prevents zero divisors in its associated graded ring. -/
instance associatedGradedNoZeroDivisors
    (ν : MaxAddDegree R M) [ν.IsMultiplicative] :
    NoZeroDivisors ν.AssociatedGraded :=
  ⟨by
    intro x y hxy
    by_contra hnonzero
    rw [not_or] at hnonzero
    have hleading := DirectSum.leadingGrade_mul ν.Component
      (fun a b ha hb ↦ ν.componentMul_ne_zero a b ha hb) x y
    have hx : DirectSum.leadingGrade ν.Component x ≠ ⊥ := by
      intro hxbot
      exact hnonzero.1 ((DirectSum.leadingGrade_eq_bot_iff ν.Component x).mp hxbot)
    have hy : DirectSum.leadingGrade ν.Component y ≠ ⊥ := by
      intro hybot
      exact hnonzero.2 ((DirectSum.leadingGrade_eq_bot_iff ν.Component y).mp hybot)
    rw [hxy, DirectSum.leadingGrade_zero] at hleading
    exact (WithBot.add_ne_bot.mpr ⟨hx, hy⟩) hleading.symm⟩

/-- Homogeneous non-zero-divisors force equality in the product-degree inequality. -/
theorem degree_mul_eq_add_of_homogeneousNoZeroDivisors
    (ν : MaxAddDegree R M) (hν : ν.IsSeparated)
    (hgr : ν.HomogeneousNoZeroDivisors) {x y : R}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ν (x * y) = ν x + ν y := by
  have hx' : ν x ≠ ⊥ := ν.map_ne_bot_of_ne_zero hν hx
  have hy' : ν y ≠ ⊥ := ν.map_ne_bot_of_ne_zero hν hy
  have hproduct : ν.componentMul
      (ν.componentMk _ (ν.initialRepresentative x hx'))
      (ν.componentMk _ (ν.initialRepresentative y hy')) ≠ 0 :=
    hgr _ _ (ν.componentMk_initialRepresentative_ne_zero x hx')
      (ν.componentMk_initialRepresentative_ne_zero y hy')
  apply le_antisymm
  · exact ν.map_mul_le_add x y
  · apply le_of_not_gt
    intro hlt
    apply hproduct
    rw [ν.componentMul_componentMk, ν.componentMk_eq_zero_iff, ν.coe_mulFiltrationLE,
      ν.coe_initialRepresentative, ν.coe_initialRepresentative, WithBot.coe_add,
      WithBot.coe_unbot, WithBot.coe_unbot]
    exact hlt

/-- A separated degree whose associated graded ring has no homogeneous zero divisors is
multiplicative. -/
theorem isMultiplicative_of_homogeneousNoZeroDivisors
    (ν : MaxAddDegree R M) (hν : ν.IsSeparated)
    (hgr : ν.HomogeneousNoZeroDivisors) :
    ν.IsMultiplicative := by
  rw [ν.isMultiplicative_iff]
  intro x y
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  exact ν.degree_mul_eq_add_of_homogeneousNoZeroDivisors hν hgr hx hy

/-- For a separated degree, multiplicativity is equivalent to absence of nonzero homogeneous
zero divisors. -/
theorem isMultiplicative_iff_homogeneousNoZeroDivisors
    (ν : MaxAddDegree R M) (hν : ν.IsSeparated) :
    ν.IsMultiplicative ↔ ν.HomogeneousNoZeroDivisors :=
  ⟨fun _ ↦ ν.homogeneousNoZeroDivisors_of_isMultiplicative,
    ν.isMultiplicative_of_homogeneousNoZeroDivisors hν⟩

/-- A separated degree is multiplicative when its associated graded ring is a domain. -/
theorem isMultiplicative_of_associatedGraded_isDomain
    (ν : MaxAddDegree R M) (hν : ν.IsSeparated)
    [IsDomain ν.AssociatedGraded] :
    ν.IsMultiplicative :=
  ν.isMultiplicative_of_homogeneousNoZeroDivisors hν
    ν.homogeneousNoZeroDivisors_of_isDomain

/-- A degree with a domain associated graded ring has a nontrivial source ring. -/
theorem nontrivial_of_associatedGraded_isDomain
    (ν : MaxAddDegree R M) [IsDomain ν.AssociatedGraded] :
    Nontrivial R := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hsub
  let : Subsingleton R := hsub
  have hcomponent (m : M) (x y : ν.Component m) : x = y := by
    induction x using QuotientAddGroup.induction_on with
    | H x =>
        induction y using QuotientAddGroup.induction_on with
        | H y =>
            exact congrArg (fun z : ν.filtrationLE m ↦ (z : ν.Component m))
              (Subtype.ext (Subsingleton.elim (x : R) (y : R)))
  have hgraded : (1 : ν.AssociatedGraded) = 0 :=
    DFinsupp.ext (fun m ↦ hcomponent m _ _)
  exact one_ne_zero hgraded

variable [WellFoundedLT M]

/-- If the associated graded ring of the least-representative quotient degree is a domain, then
the quotient ring is a domain. -/
theorem quotient_isDomain_of_associatedGraded_isDomain
    (ν : MaxAddDegree R M) (I : Ideal R) (hν : ν.IsSeparated)
    [IsDomain (ν.quotient I hν).AssociatedGraded] :
    IsDomain (R ⧸ I) := by
  let : Nontrivial (R ⧸ I) :=
    (ν.quotient I hν).nontrivial_of_associatedGraded_isDomain
  have : (ν.quotient I hν).IsMultiplicative :=
    (ν.quotient I hν).isMultiplicative_of_associatedGraded_isDomain
      (ν.quotient_isSeparated I hν)
  exact ν.quotient_isDomain I hν

end MaxAddDegree
