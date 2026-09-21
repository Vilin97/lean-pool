/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeInitialForm
public import Mathlib.GroupTheory.Congruence.Hom

/-!
# RV classes and initial forms

For a max-additive degree `ν`, two representatives are RV-equivalent when both have bottom
degree, or when their difference has degree strictly below their common nonbottom degree; the
multiplicative structure of RV needs `ν` multiplicative.
Thus the entire kernel of the degree, rather than only the literal zero element, forms the zero
RV class.

The resulting quotient is a commutative monoid with zero. Its degree is well defined, and the
initial-form map embeds it into the associated graded ring as zero together with the homogeneous
classes. The grade-zero component carries Mathlib's canonical direct-sum grade-zero ring structure
and is exposed as the residue ring.

LM24 uses the bespoke convention `-∞ < -∞`. Lean's strict order on `WithBot` does not, so the
explicit bottom branch is the standard-order encoding of LM24, Definition 4.1.1. It collapses the
kernel to one class and makes the relation reflexive on its nonzero elements. The degree axioms
also supply `w(0) = -∞`, which is not implied by the two generic semi-valuation equations
displayed in LM24.
-/
universe u v

public noncomputable section

namespace MaxAddDegree

open scoped DirectSum

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [LinearOrder M]

/-- Two representatives define the same RV class. -/
def RVRel (ν : MaxAddDegree R M) (x y : R) : Prop :=
  (ν x = ⊥ ∧ ν y = ⊥) ∨
    (ν x ≠ ⊥ ∧ ν (x - y) < ν x)

@[simp]
theorem rvRel_iff (ν : MaxAddDegree R M) (x y : R) :
    ν.RVRel x y ↔
      (ν x = ⊥ ∧ ν y = ⊥) ∨
        (ν x ≠ ⊥ ∧ ν (x - y) < ν x) :=
  Iff.rfl

theorem rvRel_degree_eq {ν : MaxAddDegree R M} {x y : R} (h : ν.RVRel x y) :
    ν x = ν y := by
  rcases h with hbot | ⟨-, hxy⟩
  · exact hbot.1.trans hbot.2.symm
  · exact ν.map_eq_of_map_sub_lt hxy

theorem rvRel_refl (ν : MaxAddDegree R M) (x : R) : ν.RVRel x x := by
  by_cases hx : ν x = ⊥
  · exact Or.inl ⟨hx, hx⟩
  · exact Or.inr ⟨hx, by simpa using WithBot.bot_lt_iff_ne_bot.mpr hx⟩

theorem rvRel_symm {ν : MaxAddDegree R M} {x y : R} (h : ν.RVRel x y) :
    ν.RVRel y x := by
  rcases h with hbot | ⟨hx, hxy⟩
  · exact Or.inl hbot.symm
  · refine Or.inr ⟨?_, ?_⟩
    · simpa only [← rvRel_degree_eq (Or.inr ⟨hx, hxy⟩)] using hx
    · rw [← rvRel_degree_eq (Or.inr ⟨hx, hxy⟩)]
      rw [← neg_sub]
      simpa only [ν.map_neg] using hxy

theorem rvRel_trans {ν : MaxAddDegree R M} {x y z : R}
    (hxy : ν.RVRel x y) (hyz : ν.RVRel y z) : ν.RVRel x z := by
  have hxyDegree := rvRel_degree_eq hxy
  have hyzDegree := rvRel_degree_eq hyz
  by_cases hx : ν x = ⊥
  · refine Or.inl ⟨hx, ?_⟩
    exact hyzDegree.symm.trans (hxyDegree.symm.trans hx)
  · refine Or.inr ⟨hx, ?_⟩
    have hxyLt : ν (x - y) < ν x := by
      rcases hxy with hbot | h
      · exact (hx hbot.1).elim
      · exact h.2
    have hyzLt : ν (y - z) < ν x := by
      rcases hyz with hbot | h
      · exact (hx (hxyDegree.trans hbot.1)).elim
      · simpa only [hxyDegree] using h.2
    have hle := ν.map_add_le_max (x - y) (y - z)
    rw [sub_add_sub_cancel] at hle
    exact hle.trans_lt (max_lt hxyLt hyzLt)

variable [IsOrderedCancelAddMonoid M]

section Graded

variable (ν : MaxAddDegree R M)

/-- The multiplicative submonoid consisting of zero and all homogeneous graded classes. -/
def homogeneousClasses : Submonoid ν.AssociatedGraded where
  carrier := {a | a = 0 ∨ ∃ m, ∃ c : ν.Component m, a = DirectSum.of ν.Component m c}
  one_mem' := Or.inr ⟨0, ν.componentOne, (DirectSum.one_def ν.Component).symm⟩
  mul_mem' {a b} ha hb := by
    rcases ha with rfl | ⟨m, c, rfl⟩
    · exact Or.inl (zero_mul _)
    rcases hb with rfl | ⟨n, d, rfl⟩
    · exact Or.inl (mul_zero _)
    · refine Or.inr ⟨m + n, ν.componentMul c d, ?_⟩
      exact DirectSum.of_mul_of c d

theorem mem_homogeneousClasses_iff (a : ν.AssociatedGraded) :
    a ∈ ν.homogeneousClasses ↔
      a = 0 ∨ ∃ m, ∃ c : ν.Component m, a = DirectSum.of ν.Component m c :=
  Iff.rfl

/-- Zero and the homogeneous classes, as a commutative monoid with zero. -/
abbrev HomogeneousClasses :=
  ν.homogeneousClasses

instance : Zero ν.HomogeneousClasses :=
  ⟨⟨0, (ν.mem_homogeneousClasses_iff 0).mpr (Or.inl rfl)⟩⟩

instance : CommMonoidWithZero ν.HomogeneousClasses where
  zero_mul q := Subtype.ext (zero_mul (q : ν.AssociatedGraded))
  mul_zero q := Subtype.ext (mul_zero (q : ν.AssociatedGraded))

theorem initialForm_mem_homogeneousClasses (x : R) :
    ν.initialForm x ∈ ν.homogeneousClasses := by
  rw [ν.mem_homogeneousClasses_iff]
  by_cases hx : ν x = ⊥
  · exact Or.inl (ν.initialForm_eq_zero_of_eq_bot hx)
  · refine Or.inr ⟨(ν x).unbot hx,
      ν.componentMk _ (ν.initialRepresentative x hx), ?_⟩
    rw [ν.initialForm_eq_homogeneousMk_of_ne_bot hx, ν.homogeneousMk_apply]

/-- The residue ring, namely the grade-zero homogeneous quotient. -/
abbrev ResidueRing :=
  ν.Component 0

/-- The canonical embedding of the residue ring into the associated graded ring. -/
def residueRingHom : ν.ResidueRing →+* ν.AssociatedGraded :=
  DirectSum.ofZeroRingHom ν.Component

@[simp]
theorem residueRingHom_apply (c : ν.ResidueRing) :
    ν.residueRingHom c = DirectSum.of ν.Component 0 c := (rfl)

theorem residueRingHom_injective :
    Function.Injective ν.residueRingHom :=
  DirectSum.of_injective 0

/-- RV-equivalent representatives have the same initial form. -/
theorem initialForm_eq_of_rvRel {x y : R} (h : ν.RVRel x y) :
    ν.initialForm x = ν.initialForm y := by
  rcases h with hbot | ⟨-, hxy⟩
  · rw [ν.initialForm_eq_zero_of_eq_bot hbot.1, ν.initialForm_eq_zero_of_eq_bot hbot.2]
  · exact ν.initialForm_eq_of_sub_lt hxy

end Graded

/-- The RV relation is compatible with multiplication for a multiplicative degree. -/
theorem rvRel_mul_left {ν : MaxAddDegree R M} [ν.IsMultiplicative] {x y : R} (z : R)
    (h : ν.RVRel x y) : ν.RVRel (z * x) (z * y) := by
  by_cases hz : ν z = ⊥
  · exact Or.inl ⟨by simp [hz], by simp [hz]⟩
  rcases h with hbot | ⟨hx, hxy⟩
  · exact Or.inl ⟨by simp [hbot.1], by simp [hbot.2]⟩
  · refine Or.inr ⟨?_, ?_⟩
    · rw [ν.map_mul, WithBot.add_ne_bot]
      exact ⟨hz, hx⟩
    · rw [← mul_sub, ν.map_mul, ν.map_mul]
      exact WithBot.add_lt_add_of_le_of_lt hz le_rfl hxy

variable (ν : MaxAddDegree R M) [ν.IsMultiplicative]

/-- The multiplicative congruence whose quotient is the RV monoid. -/
def rvCon : Con R where
  r := ν.RVRel
  iseqv := ⟨ν.rvRel_refl, rvRel_symm, rvRel_trans⟩
  mul' {x y z t} hxy hzt := by
    have hxy' : ν.RVRel (x * z) (y * z) := by
      simpa only [mul_comm] using ν.rvRel_mul_left z hxy
    exact rvRel_trans hxy' (ν.rvRel_mul_left y hzt)

/-- The RV quotient attached to a multiplicative max-additive degree. -/
abbrev RV := ν.rvCon.Quotient

/-- The quotient map to RV classes. -/
def rv : R →* ν.RV :=
  ν.rvCon.mk'

/-- Every RV class has a representative in the original ring. -/
theorem rv_surjective : Function.Surjective ν.rv := by
  exact ν.rvCon.mk'_surjective

@[simp]
theorem rv_eq_iff {x y : R} :
    ν.rv x = ν.rv y ↔ ν.RVRel x y := by
  exact ν.rvCon.eq

/-- For a representative of nonbottom degree, RV equality is exactly strict decrease of the
degree of the difference. -/
theorem rv_eq_iff_of_value_ne_bot {x y : R} (hx : ν x ≠ ⊥) :
    ν.rv x = ν.rv y ↔ ν (x - y) < ν x := by
  rw [ν.rv_eq_iff, ν.rvRel_iff]
  constructor
  · rintro (⟨hxBot, -⟩ | ⟨-, hxy⟩)
    · exact (hx hxBot).elim
    · exact hxy
  · exact fun hxy ↦ Or.inr ⟨hx, hxy⟩

/-- The common RV class of the kernel of the degree. -/
instance : Zero ν.RV :=
  ⟨ν.rv 0⟩

@[simp]
theorem rv_zero : ν.rv 0 = 0 :=
  rfl

@[simp]
theorem rv_eq_zero_iff {x : R} :
    ν.rv x = 0 ↔ ν x = ⊥ := by
  rw [← ν.rv_zero, ν.rv_eq_iff]
  constructor
  · rintro (⟨hx, -⟩ | ⟨-, hlt⟩)
    · exact hx
    · have : ν x < ν x := by simpa only [sub_zero] using hlt
      exact (lt_irrefl _ this).elim
  · intro hx
    exact Or.inl ⟨hx, ν.map_zero⟩

instance : CommMonoidWithZero ν.RV where
  zero_mul q := by
    induction q using Con.induction_on with
    | _ x =>
      change ν.rv 0 * ν.rv x = ν.rv 0
      rw [← _root_.map_mul, zero_mul]
  mul_zero q := by
    induction q using Con.induction_on with
    | _ x =>
      change ν.rv x * ν.rv 0 = ν.rv 0
      rw [← _root_.map_mul, mul_zero]

/-- The degree of an RV class. -/
def rvValue (q : ν.RV) : WithBot M :=
  Con.liftOn q ν fun _ _ h ↦ rvRel_degree_eq h

@[simp]
theorem rvValue_rv (x : R) :
    ν.rvValue (ν.rv x) = ν x := (rfl)

@[simp]
theorem rvValue_zero : ν.rvValue 0 = ⊥ := by
  rw [← ν.rv_zero, ν.rvValue_rv, ν.map_zero]

/-- The degree of the RV class of one is the degree of one: zero, unless the degree is the
degenerate one that is bottom everywhere. -/
@[simp]
theorem rvValue_one : ν.rvValue 1 = ν 1 := by
  change ν.rvValue (ν.rv 1) = ν 1
  rw [ν.rvValue_rv]

@[simp]
theorem rvValue_mul (q r : ν.RV) :
    ν.rvValue (q * r) = ν.rvValue q + ν.rvValue r := by
  induction q, r using Con.induction_on₂ with
  | _ x y =>
    change ν (x * y) = ν x + ν y
    exact ν.map_mul x y

/-- The initial form, viewed as a function of the RV class. -/
def rvInitialForm (q : ν.RV) : ν.AssociatedGraded :=
  Con.liftOn q ν.initialForm fun _ _ h ↦ ν.initialForm_eq_of_rvRel h

@[simp]
theorem rvInitialForm_rv (x : R) :
    ν.rvInitialForm (ν.rv x) = ν.initialForm x := (rfl)

/-- The multiplicative map from RV classes to the associated graded ring, sending the class of
`x` to the initial form of `x`. -/
def rvInitialFormHom : ν.RV →*₀ ν.AssociatedGraded where
  toFun := ν.rvInitialForm
  map_one' := by
    change ν.initialForm 1 = 1
    exact ν.initialForm_one
  map_mul' q r := by
    induction q, r using Con.induction_on₂ with
    | _ x y =>
      change ν.initialForm (x * y) = ν.initialForm x * ν.initialForm y
      exact ν.initialForm_mul x y
  map_zero' := by
    change ν.initialForm 0 = 0
    exact ν.initialForm_zero

@[simp]
theorem rvInitialFormHom_rv (x : R) :
    ν.rvInitialFormHom (ν.rv x) = ν.initialForm x := (rfl)

theorem rvInitialFormHom_injective :
    Function.Injective ν.rvInitialFormHom := by
  intro q r hqr
  induction q, r using Con.induction_on₂ with
  | _ x y =>
    change ν.rv x = ν.rv y
    rw [ν.rv_eq_iff]
    change ν.initialForm x = ν.initialForm y at hqr
    by_cases hx : ν x = ⊥
    · have hy : ν y = ⊥ := by
        by_contra hy
        have hix := ν.initialForm_eq_zero_of_eq_bot hx
        have hiy := ν.initialForm_ne_zero_of_ne_bot hy
        exact hiy (hqr.symm.trans hix)
      exact Or.inl ⟨hx, hy⟩
    · have hy : ν y ≠ ⊥ := by
        intro hy
        have hix := ν.initialForm_ne_zero_of_ne_bot hx
        have hiy := ν.initialForm_eq_zero_of_eq_bot hy
        exact hix (hqr.trans hiy)
      rw [ν.initialForm_eq_homogeneousMk_of_ne_bot hx,
        ν.initialForm_eq_homogeneousMk_of_ne_bot hy,
        ν.homogeneousMk_apply, ν.homogeneousMk_apply] at hqr
      rcases (DFinsupp.single_eq_single_iff _ _ _ _).mp hqr with hnonzero | hzero
      · refine Or.inr ⟨hx, ?_⟩
        have hlt := ν.sub_lt_of_componentMk_heq hnonzero.1
          (ν.initialRepresentative x hx) (ν.initialRepresentative y hy) hnonzero.2
        simpa only [coe_initialRepresentative, WithBot.coe_unbot] using hlt
      · have hlt := (ν.componentMk_eq_zero_iff _ _).mp hzero.1
        have : ν x < ν x := by
          simpa only [coe_initialRepresentative, WithBot.coe_unbot] using hlt
        exact (lt_irrefl _ this).elim

/-- The RV class represented as zero or a nonzero homogeneous graded class. -/
def rvHomogeneous : ν.RV →*₀ ν.HomogeneousClasses where
  toFun q := ⟨ν.rvInitialFormHom q, by
    induction q using Con.induction_on with
    | _ x => exact ν.initialForm_mem_homogeneousClasses x⟩
  map_one' := Subtype.ext ν.rvInitialFormHom.map_one
  map_mul' q r := Subtype.ext (ν.rvInitialFormHom.map_mul q r)
  map_zero' := Subtype.ext ν.rvInitialFormHom.map_zero

@[simp]
theorem coe_rvHomogeneous (q : ν.RV) :
    (ν.rvHomogeneous q : ν.AssociatedGraded) = ν.rvInitialFormHom q := (rfl)

theorem rvHomogeneous_injective :
    Function.Injective ν.rvHomogeneous := by
  intro q r h
  apply ν.rvInitialFormHom_injective
  exact congrArg Subtype.val h

theorem rvHomogeneous_surjective :
    Function.Surjective ν.rvHomogeneous := by
  rintro ⟨a, ha⟩
  rw [ν.mem_homogeneousClasses_iff] at ha
  rcases ha with rfl | ⟨m, c, rfl⟩
  · refine ⟨ν.rv 0, Subtype.ext ?_⟩
    change ν.initialForm 0 = 0
    exact ν.initialForm_zero
  induction c using QuotientAddGroup.induction_on with
  | H x =>
    by_cases hx : ν.componentMk m x = 0
    · refine ⟨ν.rv 0, Subtype.ext ?_⟩
      change ν.initialForm 0 = DirectSum.of ν.Component m (x : ν.Component m)
      have hxc : (x : ν.Component m) = 0 := by
        rw [ν.coe_component_eq_componentMk]
        exact hx
      rw [ν.initialForm_zero, hxc]
      exact ((DirectSum.of ν.Component m).map_zero).symm
    · refine ⟨ν.rv x, Subtype.ext ?_⟩
      rw [ν.coe_rvHomogeneous, ν.rvInitialFormHom_rv]
      change ν.initialForm x = DirectSum.of ν.Component m (x : ν.Component m)
      calc
        ν.initialForm x = ν.homogeneousMk m x :=
          ν.initialForm_eq_homogeneousMk_of_componentMk_ne_zero m x hx
        _ = DirectSum.of ν.Component m (ν.componentMk m x) :=
          ν.homogeneousMk_apply m x
        _ = DirectSum.of ν.Component m (x : ν.Component m) :=
          congrArg (DirectSum.of ν.Component m) (ν.coe_component_eq_componentMk m x).symm

/-- RV is multiplicatively equivalent to zero together with the nonzero homogeneous classes. -/
def rvEquivHomogeneous : ν.RV ≃* ν.HomogeneousClasses :=
  MulEquiv.ofBijective ν.rvHomogeneous.toMonoidHom
    ⟨ν.rvHomogeneous_injective, ν.rvHomogeneous_surjective⟩

@[simp]
theorem rvEquivHomogeneous_apply (q : ν.RV) :
    ν.rvEquivHomogeneous q = ν.rvHomogeneous q := (rfl)

theorem rvEquivHomogeneous_zero :
    ν.rvEquivHomogeneous 0 = 0 := by
  rw [ν.rvEquivHomogeneous_apply, ν.rvHomogeneous.map_zero]

@[simp]
theorem rvEquivHomogeneous_symm_zero :
    ν.rvEquivHomogeneous.symm 0 = 0 := by
  apply ν.rvEquivHomogeneous.injective
  rw [ν.rvEquivHomogeneous.apply_symm_apply, ν.rvEquivHomogeneous_zero]

end MaxAddDegree
