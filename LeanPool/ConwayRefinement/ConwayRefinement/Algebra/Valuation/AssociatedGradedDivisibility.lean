/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedValuation

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.HomogeneousDivisibility
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.TrailingGrade
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Divisibility.Basic

/-!
# Divisibility in an associated graded ring

This module equips an associated graded ring with its smallest nonzero grade and proves that this
grade is multiplicative. Comparing smallest and largest grades shows that nonzero factors of a
homogeneous product are themselves homogeneous. It follows that divisibility between homogeneous
classes is the same in the homogeneous-class monoid and in the ambient associated graded ring.
-/

universe u v

public noncomputable section

open scoped DirectSum

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

variable (ν : MaxAddDegree R M)

/-- The smallest nonzero grade of an associated-graded element, with top at zero. -/
def associatedGradedTrailingValue
    (x : ν.AssociatedGraded) : WithTop M :=
  DirectSum.trailingGrade ν.Component x

@[simp]
theorem associatedGradedTrailingValue_zero :
    ν.associatedGradedTrailingValue 0 = ⊤ :=
  DirectSum.trailingGrade_zero ν.Component

@[simp]
theorem associatedGradedTrailingValue_eq_top_iff
    (x : ν.AssociatedGraded) :
    ν.associatedGradedTrailingValue x = ⊤ ↔ x = 0 :=
  DirectSum.trailingGrade_eq_top_iff ν.Component x

omit [IsOrderedCancelAddMonoid M] in
theorem associatedGradedTrailingValue_eq_coe_iff
    (x : ν.AssociatedGraded) (m : M) :
    ν.associatedGradedTrailingValue x = (m : WithTop M) ↔
      x m ≠ 0 ∧ ∀ i, x i ≠ 0 → m ≤ i :=
  DirectSum.trailingGrade_eq_coe_iff ν.Component x m

theorem min_le_associatedGradedTrailingValue_add
    (x y : ν.AssociatedGraded) :
    min (ν.associatedGradedTrailingValue x) (ν.associatedGradedTrailingValue y) ≤
      ν.associatedGradedTrailingValue (x + y) :=
  DirectSum.min_le_trailingGrade_add ν.Component x y

/-- A graded element is zero or homogeneous exactly when its trailing and leading grades agree. -/
theorem mem_homogeneousClasses_iff_extremeGrades
    (x : ν.AssociatedGraded) :
    x ∈ ν.homogeneousClasses ↔
      x = 0 ∨ ∃ m : M,
        ν.associatedGradedTrailingValue x = m ∧
          ν.associatedGradedValue x = m := by
  classical
  constructor
  · intro hx
    rw [ν.mem_homogeneousClasses_iff] at hx
    rcases hx with rfl | ⟨m, c, rfl⟩
    · exact Or.inl rfl
    by_cases hc : c = 0
    · subst c
      exact Or.inl ((DirectSum.of ν.Component m).map_zero)
    · refine Or.inr ⟨m, DirectSum.trailingGrade_of ν.Component hc, ?_⟩
      apply (ν.associatedGradedValue_eq_coe_iff _ m).mpr
      refine ⟨by simpa, ?_⟩
      intro i hi
      have him : i = m := by
        by_contra him
        rw [DirectSum.of_eq_of_ne m i c him] at hi
        exact hi rfl
      exact him.le
  · rintro (rfl | ⟨m, htrail, hlead⟩)
    · exact (ν.mem_homogeneousClasses_iff 0).mpr (Or.inl rfl)
    · rw [ν.mem_homogeneousClasses_iff]
      refine Or.inr ⟨m, x m, ?_⟩
      apply DirectSum.ext
      intro i
      by_cases hi : i = m
      · subst i
        simp
      · have hxi : x i = 0 := by
          by_contra hxi
          have hmi : m ≤ i :=
            (ν.associatedGradedTrailingValue_eq_coe_iff x m).mp htrail |>.2 i hxi
          have him : i ≤ m :=
            (ν.associatedGradedValue_eq_coe_iff x m).mp hlead |>.2 i hxi
          exact hi (le_antisymm him hmi)
        rw [hxi]
        exact (DirectSum.of_eq_of_ne m i (x m) hi).symm

/-- A homogeneous class divides a graded element exactly when it divides every component. -/
theorem homogeneous_dvd_iff_dvd_components
    (x : ν.HomogeneousClasses)
    (y : ν.AssociatedGraded) :
    (x : ν.AssociatedGraded) ∣ y ↔
      ∀ m, (x : ν.AssociatedGraded) ∣ DirectSum.of ν.Component m (y m) := by
  classical
  have hxMem := x.property
  rw [ν.mem_homogeneousClasses_iff] at hxMem
  rcases hxMem with hx | ⟨m, c, hx⟩
  · change (x : ν.AssociatedGraded) = 0 at hx
    rw [hx]
    simp only [zero_dvd_iff]
    constructor
    · rintro rfl
      simp
    · intro h
      apply DirectSum.ext
      intro m
      simpa using congrArg (fun z : ν.AssociatedGraded ↦ z m) (h m)
  · change (x : ν.AssociatedGraded) = DirectSum.of ν.Component m c at hx
    rw [hx]
    exact DirectSum.of_dvd_iff_dvd_components ν.Component c y

variable [ν.IsMultiplicative]

@[simp]
theorem associatedGradedTrailingValue_mul
    (x y : ν.AssociatedGraded) :
    ν.associatedGradedTrailingValue (x * y) =
      ν.associatedGradedTrailingValue x + ν.associatedGradedTrailingValue y :=
  DirectSum.trailingGrade_mul ν.Component
    (fun a b ha hb ↦ ν.componentMul_ne_zero a b ha hb) x y

/-- Nonzero factors of a homogeneous product are homogeneous. -/
theorem mem_homogeneousClasses_of_mul_mem
    {x y : ν.AssociatedGraded}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x * y ∈ ν.homogeneousClasses) :
    x ∈ ν.homogeneousClasses ∧ y ∈ ν.homogeneousClasses := by
  obtain ⟨lx, hlx, hxlx⟩ :=
    DirectSum.exists_grade_eq_trailingGrade ν.Component hx
  obtain ⟨ly, hly, hyly⟩ :=
    DirectSum.exists_grade_eq_trailingGrade ν.Component hy
  have hxValueNe : ν.associatedGradedValue x ≠ ⊥ :=
    (ν.associatedGradedValue_eq_bot_iff x).not.mpr hx
  obtain ⟨ux, huxCoe⟩ := WithBot.ne_bot_iff_exists.mp hxValueNe
  have hux : ν.associatedGradedValue x = (ux : WithBot M) := huxCoe.symm
  have hxux : x ux ≠ 0 := (ν.associatedGradedValue_eq_coe_iff x ux).mp hux |>.1
  have hyValueNe : ν.associatedGradedValue y ≠ ⊥ :=
    (ν.associatedGradedValue_eq_bot_iff y).not.mpr hy
  obtain ⟨uy, huyCoe⟩ := WithBot.ne_bot_iff_exists.mp hyValueNe
  have huy : ν.associatedGradedValue y = (uy : WithBot M) := huyCoe.symm
  have hyuy : y uy ≠ 0 := (ν.associatedGradedValue_eq_coe_iff y uy).mp huy |>.1
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx hy
  rcases (ν.mem_homogeneousClasses_iff_extremeGrades (x * y)).mp hxy with
    hzero | ⟨k, htrail, hlead⟩
  · exact (hxy0 hzero).elim
  have hlxux : lx ≤ ux := by
    exact (ν.associatedGradedValue_eq_coe_iff x ux).mp hux |>.2 lx hxlx
  have hlyuy : ly ≤ uy := by
    exact (ν.associatedGradedValue_eq_coe_iff y uy).mp huy |>.2 ly hyly
  have hlx' : ν.associatedGradedTrailingValue x = (lx : WithTop M) := hlx
  have hly' : ν.associatedGradedTrailingValue y = (ly : WithTop M) := hly
  have hux' : ν.associatedGradedValue x = (ux : WithBot M) := hux
  have huy' : ν.associatedGradedValue y = (uy : WithBot M) := huy
  have hlow : lx + ly = k := by
    apply WithTop.coe_injective
    calc
      ((lx + ly : M) : WithTop M) =
          ν.associatedGradedTrailingValue x +
            ν.associatedGradedTrailingValue y := by
        rw [hlx', hly', WithTop.coe_add]
      _ = ν.associatedGradedTrailingValue (x * y) :=
        (ν.associatedGradedTrailingValue_mul x y).symm
      _ = (k : WithTop M) := htrail
  have hhigh : ux + uy = k := by
    apply WithBot.coe_injective
    calc
      ((ux + uy : M) : WithBot M) =
          ν.associatedGradedValue x + ν.associatedGradedValue y := by
        rw [hux', huy', WithBot.coe_add]
      _ = ν.associatedGradedValue (x * y) :=
        (ν.associatedGradedValue_mul x y).symm
      _ = (k : WithBot M) := hlead
  have hsum : lx + ly = ux + uy := hlow.trans hhigh.symm
  have hlxEq : lx = ux := by
    apply le_antisymm hlxux
    apply le_of_not_gt
    intro hlxux'
    exact (add_lt_add_of_lt_of_le hlxux' hlyuy).ne hsum
  have hlyEq : ly = uy := by
    apply le_antisymm hlyuy
    apply le_of_not_gt
    intro hlyuy'
    exact (add_lt_add_of_le_of_lt hlxux hlyuy').ne hsum
  constructor
  · apply (ν.mem_homogeneousClasses_iff_extremeGrades x).mpr
    exact Or.inr ⟨lx, hlx', by simpa [hlxEq] using hux'⟩
  · apply (ν.mem_homogeneousClasses_iff_extremeGrades y).mpr
    exact Or.inr ⟨ly, hly', by simpa [hlyEq] using huy'⟩

/-- Divisibility between homogeneous classes agrees with ambient graded-ring divisibility. -/
theorem homogeneous_dvd_iff_associatedGraded_dvd
    (x y : ν.HomogeneousClasses) :
    x ∣ y ↔ (x : ν.AssociatedGraded) ∣ (y : ν.AssociatedGraded) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, hz⟩
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 := by
        apply Subtype.ext
        change (y : ν.AssociatedGraded) = 0
        change (y : ν.AssociatedGraded) = 0 * z at hz
        simpa only [zero_mul] using hz
      subst y
      exact dvd_zero 0
    by_cases hy : y = 0
    · subst y
      exact dvd_zero x
    have hxCoe : (x : ν.AssociatedGraded) ≠ 0 := fun h ↦ hx (Subtype.ext h)
    have hyCoe : (y : ν.AssociatedGraded) ≠ 0 := fun h ↦ hy (Subtype.ext h)
    have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0, mul_zero] at hz
      exact hyCoe hz
    have hzMem : z ∈ ν.homogeneousClasses :=
      (ν.mem_homogeneousClasses_of_mul_mem hxCoe hz0 (hz ▸ y.2)).2
    refine ⟨⟨z, hzMem⟩, ?_⟩
    apply Subtype.ext
    exact hz

/-- Divisibility in RV agrees with divisibility after the canonical embedding into the
associated graded ring. -/
theorem rv_dvd_iff_associatedGraded_dvd
    (x y : ν.RV) :
    x ∣ y ↔ ν.rvInitialFormHom x ∣ ν.rvInitialFormHom y := by
  calc
    x ∣ y ↔ ν.rvEquivHomogeneous x ∣ ν.rvEquivHomogeneous y :=
      (map_dvd_iff ν.rvEquivHomogeneous).symm
    _ ↔ ((ν.rvEquivHomogeneous x : ν.HomogeneousClasses) : ν.AssociatedGraded) ∣
        ((ν.rvEquivHomogeneous y : ν.HomogeneousClasses) : ν.AssociatedGraded) :=
      ν.homogeneous_dvd_iff_associatedGraded_dvd
        (ν.rvEquivHomogeneous x) (ν.rvEquivHomogeneous y)
    _ ↔ ν.rvInitialFormHom x ∣ ν.rvInitialFormHom y := by
      rw [ν.rvEquivHomogeneous_apply, ν.rvEquivHomogeneous_apply,
        ν.coe_rvHomogeneous, ν.coe_rvHomogeneous]

/-- An RV class divides a graded element exactly when it divides every homogeneous component
after the canonical embedding into the associated graded ring. -/
theorem rv_dvd_iff_dvd_components
    (x : ν.RV) (y : ν.AssociatedGraded) :
    ν.rvInitialFormHom x ∣ y ↔
      ∀ m, ν.rvInitialFormHom x ∣ DirectSum.of ν.Component m (y m) := by
  simpa only [ν.rvEquivHomogeneous_apply, ν.coe_rvHomogeneous] using
    ν.homogeneous_dvd_iff_dvd_components (ν.rvEquivHomogeneous x) y

end MaxAddDegree
