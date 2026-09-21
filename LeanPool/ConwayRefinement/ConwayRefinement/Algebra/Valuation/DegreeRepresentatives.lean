/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGradedMap
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Representatives of homogeneous classes

An element represents a homogeneous class in degree `m` when it lies in the filtration at `m`
and maps to that class in the associated graded ring. This relation respects the ring operations.
-/

public noncomputable section

open MvPolynomial

universe u v w z

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

/-- An element of a filtered ring representing a homogeneous class in a specified degree. -/
structure Represents (ν : MaxAddDegree R M) (x : R) (m : M)
    (e : ν.AssociatedGraded) : Prop where
  /-- The representative lies in the specified filtration. -/
  degree_le : ν x ≤ m
  /-- Its image in the associated graded ring is the specified class. -/
  class_eq :
    ν.homogeneousMk m ⟨x, (ν.mem_filtrationLE_iff m x).mpr degree_le⟩ = e

theorem represents_iff {ν : MaxAddDegree R M} {x : R} {m : M} {e : ν.AssociatedGraded} :
    ν.Represents x m e ↔ ∃ h : ν x ≤ m,
      ν.homogeneousMk m ⟨x, (ν.mem_filtrationLE_iff m x).mpr h⟩ = e := by
  constructor
  · exact fun h ↦ ⟨h.degree_le, h.class_eq⟩
  · rintro ⟨hdegree, hclass⟩
    exact ⟨hdegree, hclass⟩

/-- A representative remains a representative after identifying equal degree functions. -/
theorem Represents.congr {ν δ : MaxAddDegree R M} (h : ν = δ)
    {x : R} {m : M} {e : ν.AssociatedGraded} (he : ν.Represents x m e) :
    δ.Represents x m (ν.associatedGradedCongr h e) := by
  subst δ
  simpa using he

/-- Zero represents zero in every degree. -/
theorem represents_zero (ν : MaxAddDegree R M) (m : M) : ν.Represents 0 m 0 := by
  refine ⟨by simp, (ν.homogeneousMk_eq_zero_iff m _).mpr ?_⟩
  simp

/-- One represents one in degree zero. -/
theorem represents_one (ν : MaxAddDegree R M) : ν.Represents 1 0 1 :=
  ⟨ν.map_one_le_zero, ν.homogeneousMk_one⟩

/-- Representatives in a common degree add. -/
theorem Represents.add {ν : MaxAddDegree R M} {x y : R} {m : M}
    {e f : ν.AssociatedGraded} (hx : ν.Represents x m e) (hy : ν.Represents y m f) :
    ν.Represents (x + y) m (e + f) := by
  obtain ⟨hdx, hex⟩ := hx
  obtain ⟨hdy, hey⟩ := hy
  have hd : ν (x + y) ≤ m := (ν.map_add_le_max x y).trans (max_le hdx hdy)
  refine ⟨hd, ?_⟩
  rw [show (⟨x + y, (ν.mem_filtrationLE_iff m _).mpr hd⟩ : ν.filtrationLE m) =
      ⟨x, (ν.mem_filtrationLE_iff m _).mpr hdx⟩ +
        ⟨y, (ν.mem_filtrationLE_iff m _).mpr hdy⟩ from Subtype.ext rfl,
    map_add, hex, hey]

/-- Representatives multiply in the sum of their degrees. -/
theorem Represents.mul {ν : MaxAddDegree R M} {x y : R} {m n p : M}
    {e f : ν.AssociatedGraded} (hp : p = m + n)
    (hx : ν.Represents x m e) (hy : ν.Represents y n f) :
    ν.Represents (x * y) p (e * f) := by
  obtain ⟨hdx, hex⟩ := hx
  obtain ⟨hdy, hey⟩ := hy
  have hd : ν (x * y) ≤ p := by
    rw [hp]
    exact (ν.map_mul_le_add x y).trans (by simpa using add_le_add hdx hdy)
  refine ⟨hd, ?_⟩
  rw [← hex, ← hey, ν.homogeneousMk_mul_of_coe_eq hp
    ⟨x, (ν.mem_filtrationLE_iff m _).mpr hdx⟩
    ⟨y, (ν.mem_filtrationLE_iff n _).mpr hdy⟩
    ⟨x * y, (ν.mem_filtrationLE_iff p _).mpr hd⟩ rfl]

/-- Powers of a representative represent the corresponding powers. -/
theorem Represents.pow {ν : MaxAddDegree R M} {x : R} {m : M} {e : ν.AssociatedGraded}
    (hx : ν.Represents x m e) (n : ℕ) : ν.Represents (x ^ n) (n • m) (e ^ n) := by
  induction n with
  | zero => simpa using ν.represents_one
  | succ n ih => simpa [pow_succ, succ_nsmul] using ih.mul rfl hx

/-- A finite product of representatives represents the product. -/
theorem represents_prod {ν : MaxAddDegree R M} {ι : Type w} {s : Finset ι}
    {x : ι → R} {m : ι → M} {e : ι → ν.AssociatedGraded}
    (h : ∀ i ∈ s, ν.Represents (x i) (m i) (e i)) :
    ν.Represents (∏ i ∈ s, x i) (∑ i ∈ s, m i) (∏ i ∈ s, e i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using ν.represents_one
  | cons i s hi ih =>
      rw [Finset.prod_cons, Finset.prod_cons]
      exact (h i (Finset.mem_cons_self i s)).mul (Finset.sum_cons hi)
        (ih fun j hj ↦ h j (Finset.mem_cons_of_mem hj))

/-- A finite sum of representatives in one degree represents the sum. -/
theorem represents_sum {ν : MaxAddDegree R M} {ι : Type w} {s : Finset ι}
    {x : ι → R} {m : M} {e : ι → ν.AssociatedGraded}
    (h : ∀ i ∈ s, ν.Represents (x i) m (e i)) :
    ν.Represents (∑ i ∈ s, x i) m (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using ν.represents_zero m
  | cons i s hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact (h i (Finset.mem_cons_self i s)).add
        (ih fun j hj ↦ h j (Finset.mem_cons_of_mem hj))

/-- Representatives of the same class differ by an element of smaller degree. -/
theorem Represents.degree_sub_lt {ν : MaxAddDegree R M} {x y : R} {m : M}
    {e : ν.AssociatedGraded} (hx : ν.Represents x m e) (hy : ν.Represents y m e) :
    ν (x - y) < m := by
  obtain ⟨hdx, hex⟩ := hx
  obtain ⟨hdy, hey⟩ := hy
  have hd : ν (x - y) ≤ m := (ν.map_sub_le_max x y).trans (max_le hdx hdy)
  apply (ν.homogeneousMk_eq_zero_iff m
    ⟨x - y, (ν.mem_filtrationLE_iff m _).mpr hd⟩).mp
  rw [show (⟨x - y, (ν.mem_filtrationLE_iff m _).mpr hd⟩ : ν.filtrationLE m) =
      ⟨x, (ν.mem_filtrationLE_iff m _).mpr hdx⟩ -
        ⟨y, (ν.mem_filtrationLE_iff m _).mpr hdy⟩ from Subtype.ext rfl,
    map_sub, hex, hey, sub_self]

/-- An element of smaller degree represents zero. -/
theorem represents_zero_of_degree_lt {ν : MaxAddDegree R M} {x : R} {m : M}
    (h : ν x < (m : WithBot M)) : ν.Represents x m 0 :=
  ⟨h.le, (ν.homogeneousMk_eq_zero_iff m _).mpr h⟩

/-- An element represents at most one class in a fixed degree. -/
theorem Represents.unique {ν : MaxAddDegree R M} {x : R} {m : M}
    {e f : ν.AssociatedGraded} (he : ν.Represents x m e) (hf : ν.Represents x m f) : e = f := by
  obtain ⟨hde, heq⟩ := he
  obtain ⟨hdf, hfq⟩ := hf
  rw [← heq, ← hfq]

/-- A representative of a nonzero class has exactly the specified degree. -/
theorem Represents.degree_eq {ν : MaxAddDegree R M} {x : R} {m : M}
    {e : ν.AssociatedGraded} (h : ν.Represents x m e) (he : e ≠ 0) :
    ν x = (m : WithBot M) := by
  rcases h.degree_le.lt_or_eq with hlt | heq
  · exact absurd ((ν.represents_zero_of_degree_lt hlt).unique h) (by simpa [eq_comm] using he)
  · exact heq

/-- A representative of zero has degree below the specified degree. -/
theorem Represents.degree_lt_of_eq_zero {ν : MaxAddDegree R M} {x : R} {m : M}
    (h : ν.Represents x m 0) : ν x < (m : WithBot M) := by
  obtain ⟨hd, he⟩ := h
  exact (ν.homogeneousMk_eq_zero_iff m
    ⟨x, (ν.mem_filtrationLE_iff m _).mpr hd⟩).mp he

/-- A choice of representative for each member of a graded family. -/
structure LiftFamily (ν : MaxAddDegree R M) {ι : Type w} (wt : ι → M)
    (e : ι → ν.AssociatedGraded) where
  /-- The chosen representative. -/
  lift : ι → R
  /-- Each chosen element represents the corresponding homogeneous class. -/
  represents : ∀ i, ν.Represents (lift i) (wt i) (e i)

variable {k : Type z} [CommRing k] [Algebra k R]

/-- Weighted homogeneous evaluation preserves representation. -/
theorem represents_aeval {ν : MaxAddDegree R M} {ι : Type w} {wt : ι → M}
    {x : ι → R} {e : ι → ν.AssociatedGraded} [Algebra k ν.AssociatedGraded]
    (hscalar : ∀ c : k,
      ν.Represents (algebraMap k R c) 0 (algebraMap k ν.AssociatedGraded c))
    (hx : ∀ i, ν.Represents (x i) (wt i) (e i))
    {F : MvPolynomial ι k} {m : M} (hF : IsWeightedHomogeneous wt F m) :
    ν.Represents (aeval x F) m (aeval e F) := by
  classical
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => simpa using ν.represents_zero m
  | add p q hp hq ihp ihq => simpa using ihp.add ihq
  | monomial d c hc =>
      rw [← hc, aeval_monomial, aeval_monomial, Finsupp.weight_apply, Finsupp.sum,
        Finsupp.prod, Finsupp.prod]
      exact (hscalar c).mul (zero_add _).symm
        (ν.represents_prod fun i _ ↦ (hx i).pow (d i))

/-- Evaluating a polynomial whose monomials all have weight below `m` has degree below `m`. -/
theorem degree_aeval_lt_of_forall_weight_lt {ν : MaxAddDegree R M} {ι : Type w}
    {wt : ι → M} {x : ι → R} {e : ι → ν.AssociatedGraded}
    [Algebra k ν.AssociatedGraded]
    (hscalar : ∀ c : k,
      ν.Represents (algebraMap k R c) 0 (algebraMap k ν.AssociatedGraded c))
    (hx : ∀ i, ν.Represents (x i) (wt i) (e i))
    {F : MvPolynomial ι k} {m : M}
    (hF : ∀ d ∈ F.support, Finsupp.weight wt d < m) :
    ν (aeval x F) < (m : WithBot M) := by
  classical
  rw [show aeval x F =
      ∑ d ∈ F.support, aeval x (monomial d (MvPolynomial.coeff d F)) by
    conv_lhs => rw [F.as_sum]
    rw [map_sum]]
  apply ν.map_sum_lt_of_forall_lt _ _ (WithBot.bot_lt_coe m)
  intro d hd
  have hhom : IsWeightedHomogeneous wt (monomial d (MvPolynomial.coeff d F))
      (Finsupp.weight wt d) :=
    isWeightedHomogeneous_monomial wt d (MvPolynomial.coeff d F) rfl
  exact (ν.represents_aeval hscalar hx hhom).degree_le.trans_lt
    (WithBot.coe_lt_coe.mpr (hF d hd))

/-- Polynomial evaluation represents the evaluation of its top weighted homogeneous part. -/
theorem represents_aeval_weightedHomogeneousComponent {ν : MaxAddDegree R M} {ι : Type w}
    {wt : ι → M} {x : ι → R} {e : ι → ν.AssociatedGraded}
    [Algebra k ν.AssociatedGraded]
    (hscalar : ∀ c : k,
      ν.Represents (algebraMap k R c) 0 (algebraMap k ν.AssociatedGraded c))
    (hx : ∀ i, ν.Represents (x i) (wt i) (e i))
    {F : MvPolynomial ι k} {m : M}
    (hF : ∀ d ∈ F.support, Finsupp.weight wt d ≤ m) :
    ν.Represents (aeval x F) m (aeval e (weightedHomogeneousComponent wt m F)) := by
  classical
  have hhom : IsWeightedHomogeneous wt (weightedHomogeneousComponent wt m F) m :=
    weightedHomogeneousComponent_isWeightedHomogeneous (w := wt) (n := m) (φ := F)
  have hrest : ∀ d ∈ (F - weightedHomogeneousComponent wt m F).support,
      Finsupp.weight wt d < m := by
    intro d hd
    have hne := MvPolynomial.mem_support_iff.mp hd
    rw [MvPolynomial.coeff_sub, coeff_weightedHomogeneousComponent] at hne
    by_cases hdw : Finsupp.weight wt d = m
    · rw [if_pos hdw, sub_self] at hne
      exact absurd rfl hne
    · rw [if_neg hdw, sub_zero] at hne
      exact lt_of_le_of_ne (hF d (MvPolynomial.mem_support_iff.mpr hne)) hdw
  have htop := ν.represents_aeval hscalar hx hhom
  have hlow :
      ν.Represents (aeval x (F - weightedHomogeneousComponent wt m F)) m 0 :=
    ν.represents_zero_of_degree_lt
      (ν.degree_aeval_lt_of_forall_weight_lt hscalar hx hrest)
  have := htop.add hlow
  rwa [← map_add, add_sub_cancel, add_zero] at this

end MaxAddDegree

end
