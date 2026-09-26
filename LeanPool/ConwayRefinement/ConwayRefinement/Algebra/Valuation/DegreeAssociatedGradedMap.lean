/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeInitialForm

/-!
# Maps of associated graded rings

A ring homomorphism that does not increase a max-additive degree sends each weak filtration and
each strict filtration into the corresponding target filtration. It therefore induces additive
maps on the homogeneous quotients and a graded ring homomorphism on their direct sums. Two cases
are used: a degree-preserving ring homomorphism between two filtered rings, and the identity of
one ring carrying a finer degree to a coarser one, `ν₂ ≤ ν₁` pointwise, which gives the canonical
map `gr_{ν₁} → gr_{ν₂}` between the two associated graded rings of the same ring.

Exact preservation of degree makes every homogeneous component map injective, even if injectivity
of the original ring homomorphism has not been assumed separately. The resulting global graded
map is consequently injective. This functorial interface is used to compare a filtered ring with
its degree-zero localizations.
-/

open scoped MaxAddDegree

universe u v w

public noncomputable section

namespace MaxAddDegree

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [AddCommMonoid M]
variable [LinearOrder M] [IsOrderedCancelAddMonoid M]

/-- A degree-nonincreasing ring homomorphism restricted to a weak filtration. -/
def mapFiltrationLE (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) ≤ νR x) (m : M) :
    νR.filtrationLE m →+ νA.filtrationLE m where
  toFun x := ⟨f x, by
    rw [νA.mem_filtrationLE_iff]
    exact (hdegree x).trans ((νR.mem_filtrationLE_iff m x).mp x.2)⟩
  map_zero' := by ext; exact f.map_zero
  map_add' x y := by ext; exact f.map_add x y

omit [IsOrderedCancelAddMonoid M] in
@[simp]
theorem coe_mapFiltrationLE (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) ≤ νR x) (m : M)
    (x : νR.filtrationLE m) :
    (νR.mapFiltrationLE νA f hdegree m x : A) = f x :=
  (rfl)

omit [IsOrderedCancelAddMonoid M] in
private theorem lowerFiltration_le_componentRepresentative_ker
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) ≤ νR x) (m : M) :
    νR.lowerFiltration m ≤
      ((νA.componentMk m).comp (νR.mapFiltrationLE νA f hdegree m)).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply,
    νA.componentMk_eq_zero_iff, coe_mapFiltrationLE]
  exact (hdegree x).trans_lt ((νR.mem_lowerFiltration_iff m x).mp hx)

/-- The map on a homogeneous quotient induced by a degree-nonincreasing ring homomorphism. -/
def componentMap (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) ≤ νR x) (m : M) :
    νR.Component m →+ νA.Component m :=
  QuotientAddGroup.lift (νR.lowerFiltration m)
    ((νA.componentMk m).comp (νR.mapFiltrationLE νA f hdegree m))
    (νR.lowerFiltration_le_componentRepresentative_ker νA f hdegree m)

omit [IsOrderedCancelAddMonoid M] in
/-- The component map sends a representative class to the class of its image. -/
@[simp]
theorem componentMap_componentMk
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) ≤ νR x) (m : M)
    (x : νR.filtrationLE m) :
    νR.componentMap νA f hdegree m (νR.componentMk m x) =
      νA.componentMk m (νR.mapFiltrationLE νA f hdegree m x) := by
  rw [← νR.coe_component_eq_componentMk]
  rfl

omit [IsOrderedCancelAddMonoid M] in
/-- Exact degree preservation makes the component map detect zero classes. -/
theorem componentMap_eq_zero_iff
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) = νR x) (m : M)
    (x : νR.Component m) :
    νR.componentMap νA f (fun x ↦ (hdegree x).le) m x = 0 ↔ x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
      rw [νR.coe_component_eq_componentMk, νR.componentMap_componentMk,
        νA.componentMk_eq_zero_iff, coe_mapFiltrationLE, hdegree,
        νR.componentMk_eq_zero_iff]

omit [IsOrderedCancelAddMonoid M] in
/-- Every exactly degree-preserving component map is injective. -/
theorem componentMap_injective
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) = νR x) (m : M) :
    Function.Injective (νR.componentMap νA f (fun x ↦ (hdegree x).le) m) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (νR.componentMap_eq_zero_iff νA f hdegree m (x - y)).mp
  rw [map_sub, hxy, sub_self]

omit [IsOrderedCancelAddMonoid M] in
/-- The component maps preserve the homogeneous identity. -/
theorem componentMap_componentOne
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) ≤ νR x) :
    νR.componentMap νA f hdegree 0 νR.componentOne = νA.componentOne := by
  rw [νR.componentOne_eq_componentMk, νR.componentMap_componentMk,
    νA.componentOne_eq_componentMk]
  apply congrArg (νA.componentMk 0)
  apply Subtype.ext
  exact f.map_one

/-- The component maps commute with homogeneous multiplication. -/
theorem componentMap_componentMul
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) ≤ νR x)
    {m n : M} (x : νR.Component m) (y : νR.Component n) :
    νR.componentMap νA f hdegree (m + n) (νR.componentMul x y) =
      νA.componentMul
        (νR.componentMap νA f hdegree m x)
        (νR.componentMap νA f hdegree n y) := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
      induction y using QuotientAddGroup.induction_on with
      | H y =>
          rw [νR.coe_component_eq_componentMk, νR.coe_component_eq_componentMk]
          rw [νR.componentMul_componentMk, νR.componentMap_componentMk,
            νR.componentMap_componentMk, νR.componentMap_componentMk,
            νA.componentMul_componentMk]
          apply congrArg (νA.componentMk (m + n))
          apply Subtype.ext
          simp only [νR.coe_mulFiltrationLE, coe_mapFiltrationLE,
            νA.coe_mulFiltrationLE]
          exact f.map_mul (x : R) (y : R)

/-- The graded ring homomorphism induced by a degree-nonincreasing ring homomorphism. -/
def associatedGradedMap
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) ≤ νR x) :
    νR.AssociatedGraded →+* νA.AssociatedGraded :=
  DirectSum.toSemiring
    (fun m ↦ (DirectSum.of νA.Component m).comp
      (νR.componentMap νA f hdegree m))
    (by
      simp only [AddMonoidHom.comp_apply]
      rw [show GradedMonoid.GOne.one = νR.componentOne from rfl,
        νR.componentMap_componentOne νA f hdegree]
      exact DirectSum.of_zero_one νA.Component)
    (by
      intro m n x y
      simp only [AddMonoidHom.comp_apply]
      rw [show GradedMonoid.GMul.mul x y = νR.componentMul x y from rfl,
        νR.componentMap_componentMul, DirectSum.of_mul_of]
      rfl)

/-- The associated-graded map sends a homogeneous element to the image of its component. -/
@[simp]
theorem associatedGradedMap_of
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) ≤ νR x)
    (m : M) (x : νR.Component m) :
    νR.associatedGradedMap νA f hdegree (DirectSum.of νR.Component m x) =
      DirectSum.of νA.Component m (νR.componentMap νA f hdegree m x) :=
  DirectSum.toSemiring_of _ _ _ m x

/-- The associated-graded map is computed componentwise. -/
theorem associatedGradedMap_apply
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) ≤ νR x)
    (z : νR.AssociatedGraded) (m : M) :
    νR.associatedGradedMap νA f hdegree z m =
      νR.componentMap νA f hdegree m (z m) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of n z =>
      by_cases hnm : n = m
      · subst m
        simp [νR.associatedGradedMap_of]
      · simp [νR.associatedGradedMap_of, DirectSum.of_apply, hnm]
  | add x y hx hy => simp [map_add, hx, hy]

/-- An exactly degree-preserving ring homomorphism induces an injective associated-graded
map. -/
theorem associatedGradedMap_injective
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) = νR x) :
    Function.Injective (νR.associatedGradedMap νA f (fun x ↦ (hdegree x).le)) := by
  intro x y hxy
  apply DirectSum.ext
  intro m
  apply νR.componentMap_injective νA f hdegree m
  rw [← νR.associatedGradedMap_apply νA f (fun x ↦ (hdegree x).le),
    ← νR.associatedGradedMap_apply νA f (fun x ↦ (hdegree x).le), hxy]

/-- The associated-graded map induced by an exactly degree-preserving ring homomorphism sends
each initial form to the initial form of its image. -/
theorem associatedGradedMap_initialForm
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) = νR x) (x : R) :
    νR.associatedGradedMap νA f (fun x ↦ (hdegree x).le) (νR.initialForm x) =
      νA.initialForm (f x) := by
  by_cases hx : νR x = ⊥
  · have hfx : νA (f x) = ⊥ := (hdegree x).trans hx
    rw [νR.initialForm_eq_zero_of_eq_bot hx, νA.initialForm_eq_zero_of_eq_bot hfx, _root_.map_zero]
  · have hfx : νA (f x) ≠ ⊥ := (hdegree x).symm ▸ hx
    rw [νR.initialForm_eq_homogeneousMk_of_ne_bot hx,
      νA.initialForm_eq_homogeneousMk_of_ne_bot hfx,
      νR.homogeneousMk_apply, νA.homogeneousMk_apply,
      νR.associatedGradedMap_of,
      νR.componentMap_componentMk]
    have hm : (νA (f x)).unbot hfx = (νR x).unbot hx := by
      apply WithBot.coe_injective
      rw [WithBot.coe_unbot, WithBot.coe_unbot, hdegree]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    apply Sigma.ext hm.symm
    apply νA.componentMk_heq_of_grade_eq_of_coe_eq hm.symm
    rw [νR.coe_mapFiltrationLE, νR.coe_initialRepresentative,
      νA.coe_initialRepresentative]

/-- The associated-graded map of a degree-nonincreasing ring homomorphism sends the initial form
of an element `x` of degree `d` to the class of `f x` in grade `d`. -/
theorem associatedGradedMap_initialForm_eq_homogeneousMk
    (νR : MaxAddDegree R M) (νA : MaxAddDegree A M)
    (f : R →+* A) (hdegree : ∀ x, νA (f x) ≤ νR x) {x : R} {d : M} (hx : νR x = d) :
    νR.associatedGradedMap νA f hdegree (νR.initialForm x) =
      νA.homogeneousMk d ⟨f x, (νA.mem_filtrationLE_iff d _).mpr ((hdegree x).trans hx.le)⟩ := by
  have hmem : x ∈ νR.filtrationLE d := (νR.mem_filtrationLE_iff d x).mpr hx.le
  have hne : νR.componentMk d ⟨x, hmem⟩ ≠ 0 := by
    rw [Ne, νR.componentMk_eq_zero_iff]
    change ¬ νR x < (d : WithBot M)
    rw [hx]
    exact lt_irrefl _
  rw [νR.initialForm_eq_homogeneousMk_of_componentMk_ne_zero d ⟨x, hmem⟩ hne,
    νR.homogeneousMk_apply, νR.associatedGradedMap_of, νR.componentMap_componentMk,
    νA.homogeneousMk_apply]
  rfl

/-- Equal max-additive degrees have canonically ring-equivalent associated graded rings. -/
def associatedGradedCongr {R : Type u} {M : Type w}
    [CommRing R] [AddCommMonoid M] [LinearOrder M]
    [IsOrderedCancelAddMonoid M] {ν δ : MaxAddDegree R M}
    (h : ν = δ) : ν.AssociatedGraded ≃+* δ.AssociatedGraded := by
  subst δ
  exact RingEquiv.refl _

/-- Equal max-additive degrees have canonically equivalent homogeneous components. -/
def componentCongr {R : Type u} {M : Type w}
    [CommRing R] [AddCommMonoid M] [LinearOrder M]
    {ν δ : MaxAddDegree R M} (h : ν = δ) (m : M) : ν.Component m ≃+ δ.Component m := by
  subst δ
  exact AddEquiv.refl _

/-- Transport between equal degrees commutes with homogeneous inclusion. -/
theorem associatedGradedCongr_of {R : Type u} {M : Type w}
    [CommRing R] [AddCommMonoid M] [LinearOrder M]
    [IsOrderedCancelAddMonoid M] {ν δ : MaxAddDegree R M}
    (h : ν = δ) (m : M) (x : ν.Component m) :
    ν.associatedGradedCongr h (DirectSum.of ν.Component m x) =
      DirectSum.of δ.Component m (ν.componentCongr h m x) := by
  subst δ
  rfl

/-- The associated-graded equivalence induced by reflexivity is the identity. -/
@[simp]
theorem associatedGradedCongr_rfl {R : Type u} {M : Type w}
    [CommRing R] [AddCommMonoid M] [LinearOrder M]
    [IsOrderedCancelAddMonoid M] (ν : MaxAddDegree R M)
    (x : ν.AssociatedGraded) : ν.associatedGradedCongr rfl x = x :=
  (rfl)

/-- Transport along equality of max-additive degrees carries an initial form to the corresponding
initial form for the equal degree. -/
theorem associatedGradedCongr_initialForm {R : Type u} {M : Type w}
    [CommRing R] [AddCommMonoid M] [LinearOrder M]
    [IsOrderedCancelAddMonoid M] {ν δ : MaxAddDegree R M}
    (h : ν = δ) (x : R) :
    ν.associatedGradedCongr h (ν.initialForm x) = δ.initialForm x := by
  subst δ
  exact ν.associatedGradedCongr_rfl (ν.initialForm x)

end MaxAddDegree
