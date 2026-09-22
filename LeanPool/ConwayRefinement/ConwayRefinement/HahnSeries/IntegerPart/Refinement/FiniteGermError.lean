/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Germ
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SupportArchimedeanClasses
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.Refinement

/-!
# Killing finitely many Hahn-series germ errors at one Archimedean class

An error that vanishes as a germ at zero is supported below some strictly negative exponent.
Its Archimedean classes are therefore bounded above by the class of that exponent.  Restriction
to the closed ball at any strictly later finite Archimedean class kills the error exactly.

For finitely many germ errors, one class works simultaneously.  If `T` is a cofinal set of finite
classes, first take a common upper bound for the finitely many error bounds, then move strictly
above it and into `T`.  This is the finite-error restriction used in the Conway limit step; it
does not choose a compatible infinite family of restrictions.
-/

open Set

universe u v

namespace HahnSeries.Nonpositive

variable {G : Type u} {R : Type v}
  [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [CommRing R]

public noncomputable section

open Classical in
/-- The four errors measuring whether chosen representatives satisfy the four refinement
equations before passing to the quotient by series bounded strictly below zero. -/
def fourFactorErrors (a b c d e f g h : Nonpositive G R) : Finset (Nonpositive G R) :=
  {a - e * f, b - g * h, c - e * g, d - f * h}

/-- Equality of the four refinement equations in the germ quotient puts every representative
error in the valuation support ideal. -/
theorem fourFactorErrors_mem_supp
    [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
    [CompleteSpace G] [NoZeroDivisors R] [CharZero R]
    {a b c d e f g h : Nonpositive G R}
    (ha : Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp a =
      Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp (e * f))
    (hb : Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp b =
      Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp (g * h))
    (hc : Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp c =
      Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp (e * g))
    (hd : Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp d =
      Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp (f * h)) :
    ∀ z ∈ fourFactorErrors a b c d e f g h,
      z ∈ (cantorBendixsonValuation (G := G) (R := R)).supp := by
  intro z hz
  simp only [fourFactorErrors, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact Ideal.Quotient.eq.mp ha
  · exact Ideal.Quotient.eq.mp hb
  · exact Ideal.Quotient.eq.mp hc
  · exact Ideal.Quotient.eq.mp hd

open Classical in
/-- Restriction of a nonpositive Hahn series to the closed ball at a finite Archimedean class. -/
def closedClassRestrict (c : FiniteArchimedeanClass G)
    (b : Nonpositive G R) : Nonpositive G R :=
  ⟨HahnSeries.filter (· ∈ FiniteArchimedeanClass.closedBallAddSubgroup c)
    (b : HahnSeries G R), (HahnSeries.support_filter_subset _ _).trans b.property⟩

open Classical in
/-- The coefficient formula for restriction to a closed Archimedean ball. -/
@[simp]
theorem closedClassRestrict_coeff (c : FiniteArchimedeanClass G) (b : Nonpositive G R) (g : G) :
    ((closedClassRestrict c b : Nonpositive G R) : HahnSeries G R).coeff g =
      if g ∈ FiniteArchimedeanClass.closedBallAddSubgroup c then
        (b : HahnSeries G R).coeff g else 0 := by
  rw [closedClassRestrict, HahnSeries.coeff_filter]

/-- Closed-class restriction cannot introduce a new support exponent. -/
theorem support_closedClassRestrict_subset (c : FiniteArchimedeanClass G)
    (b : Nonpositive G R) :
    ((closedClassRestrict c b : Nonpositive G R) : HahnSeries G R).support ⊆
      (b : HahnSeries G R).support := by
  intro g hg
  rw [HahnSeries.mem_support] at hg ⊢
  rw [closedClassRestrict_coeff] at hg
  split at hg
  · exact hg
  · exact (hg rfl).elim

/-- Restriction at an Archimedean class met by the support is nonzero. -/
theorem closedClassRestrict_ne_zero_of_mem_image_mk_support
    (c : FiniteArchimedeanClass G) (b : Nonpositive G R)
    (hc : c.1 ∈ ArchimedeanClass.mk '' (b : HahnSeries G R).support) :
    closedClassRestrict c b ≠ 0 := by
  classical
  obtain ⟨g, hg, hgc⟩ := hc
  intro hzero
  have hcoeff := congrArg (fun x : Nonpositive G R ↦ (x : HahnSeries G R).coeff g) hzero
  rw [closedClassRestrict_coeff, ite_eq_left] at hcoeff
  · exact (HahnSeries.mem_support _ _).mp hg hcoeff
  · apply (FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff).mpr
    intro hg0
    change c.1 ≤ ArchimedeanClass.mk g
    rw [hgc]

/-- Restriction to a closed Archimedean ball preserves subtraction. -/
theorem closedClassRestrict_sub (c : FiniteArchimedeanClass G) (a b : Nonpositive G R) :
    closedClassRestrict c (a - b) = closedClassRestrict c a - closedClassRestrict c b := by
  classical
  apply Subtype.ext
  ext g
  change (HahnSeries.filter (· ∈ FiniteArchimedeanClass.closedBallAddSubgroup c)
      ((a - b : Nonpositive G R) : HahnSeries G R)).coeff g =
    ((closedClassRestrict c a : Nonpositive G R) : HahnSeries G R).coeff g -
      ((closedClassRestrict c b : Nonpositive G R) : HahnSeries G R).coeff g
  rw [HahnSeries.coeff_filter]
  change (if g ∈ FiniteArchimedeanClass.closedBallAddSubgroup c then
      ((a : HahnSeries G R) - (b : HahnSeries G R)).coeff g else 0) = _
  rw [HahnSeries.coeff_sub]
  change _ =
    (HahnSeries.filter (· ∈ FiniteArchimedeanClass.closedBallAddSubgroup c)
      (a : HahnSeries G R)).coeff g -
    (HahnSeries.filter (· ∈ FiniteArchimedeanClass.closedBallAddSubgroup c)
      (b : HahnSeries G R)).coeff g
  rw [HahnSeries.coeff_filter, HahnSeries.coeff_filter]
  split_ifs <;> simp_all

/-- Restriction to a closed Archimedean ball preserves multiplication of nonpositive series. -/
theorem closedClassRestrict_mul (c : FiniteArchimedeanClass G) (a b : Nonpositive G R) :
    closedClassRestrict c (a * b) = closedClassRestrict c a * closedClassRestrict c b := by
  classical
  apply Subtype.ext
  ext g
  rw [closedClassRestrict, HahnSeries.coeff_filter]
  change (if g ∈ FiniteArchimedeanClass.closedBallAddSubgroup c then
      ((a : HahnSeries G R) * (b : HahnSeries G R)).coeff g else 0) = _
  rw [HahnSeries.coeff_mul]
  change _ = ((HahnSeries.filter
    (· ∈ FiniteArchimedeanClass.closedBallAddSubgroup c) (a : HahnSeries G R)) *
      HahnSeries.filter (· ∈ FiniteArchimedeanClass.closedBallAddSubgroup c)
        (b : HahnSeries G R)).coeff g
  rw [HahnSeries.coeff_mul]
  let C := FiniteArchimedeanClass.closedBallAddSubgroup c
  have hC : (C : Set G).OrdConnected := by
    constructor
    intro x hx y hy z hz
    change x ∈ FiniteArchimedeanClass.closedBallAddSubgroup c at hx
    change y ∈ FiniteArchimedeanClass.closedBallAddSubgroup c at hy
    change z ∈ FiniteArchimedeanClass.closedBallAddSubgroup c
    rw [FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff] at hx hy ⊢
    intro hz0
    have hx' : c.1 ≤ ArchimedeanClass.mk x := by
      by_cases hx0 : x = 0
      · simp [hx0]
      · exact hx hx0
    have hy' : c.1 ≤ ArchimedeanClass.mk y := by
      by_cases hy0 : y = 0
      · simp [hy0]
      · exact hy hy0
    exact (le_min hx' hy').trans
      (ArchimedeanClass.min_le_mk_of_le_of_le hz.1 hz.2)
  have hsub : Finset.antidiagonal
      (HahnSeries.filter (· ∈ C) (a : HahnSeries G R)).isPWO_support
      (HahnSeries.filter (· ∈ C) (b : HahnSeries G R)).isPWO_support g ⊆
      Finset.antidiagonal (a : HahnSeries G R).isPWO_support
        (b : HahnSeries G R).isPWO_support g := by
    intro p hp
    rw [Finset.mem_antidiagonal] at hp ⊢
    exact ⟨HahnSeries.support_filter_subset _ _ hp.1,
      HahnSeries.support_filter_subset _ _ hp.2.1, hp.2.2⟩
  by_cases hg : g ∈ C
  · rw [ite_eq_left hg]
    refine Finset.sum_congr ?_ ?_
    · apply Finset.Subset.antisymm _ hsub
      intro p hp
      rw [Finset.mem_antidiagonal] at hp ⊢
      have hp1le : p.1 ≤ 0 := a.property hp.1
      have hp2le : p.2 ≤ 0 := b.property hp.2.1
      have hgp1 : g ≤ p.1 := by
        rw [← hp.2.2]
        simpa using add_le_add_left hp2le p.1
      have hp1C : p.1 ∈ C := hC.out hg C.zero_mem ⟨hgp1, hp1le⟩
      have hp2C : p.2 ∈ C := by simpa [← hp.2.2] using C.sub_mem hg hp1C
      exact ⟨by simpa only [HahnSeries.support_filter, Set.mem_ofPred_eq] using
          And.intro hp.1 hp1C,
        by simpa only [HahnSeries.support_filter, Set.mem_ofPred_eq] using
          And.intro hp.2.1 hp2C, hp.2.2⟩
    · intro p hp
      rw [Finset.mem_antidiagonal, HahnSeries.support_filter,
        HahnSeries.support_filter] at hp
      simp only [HahnSeries.coeff_filter, ite_eq_left hp.1.2, ite_eq_left hp.2.1.2]
  · rw [ite_eq_right hg]
    refine (Finset.sum_eq_zero fun p hp ↦ ?_).symm
    rw [Finset.mem_antidiagonal, HahnSeries.support_filter,
      HahnSeries.support_filter] at hp
    exact (hg (hp.2.2 ▸ C.add_mem hp.1.2 hp.2.1.2)).elim

/-- Restriction at a class strictly above the class of a negative support bound is zero. -/
theorem closedClassRestrict_eq_zero_of_support_subset_Iic
    {e : G} (he : e < 0) {c : FiniteArchimedeanClass G}
    (hec : FiniteArchimedeanClass.mk e he.ne < c) {b : Nonpositive G R}
    (hb : (b : HahnSeries G R).support ⊆ Iic e) :
    closedClassRestrict c b = 0 := by
  classical
  apply Subtype.ext
  ext g
  rw [closedClassRestrict, HahnSeries.coeff_filter]
  split_ifs with hg
  · by_contra hcoeff
    have hgs : g ∈ (b : HahnSeries G R).support := HahnSeries.mem_support _ _ |>.mpr hcoeff
    have hg0 : g ≠ 0 := fun h ↦ (not_le_of_gt he) (h ▸ hb hgs)
    have hcg := (FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff).mp hg hg0
    have hge := ArchimedeanClass.mk_le_mk_of_le_of_nonpos (hb hgs) he.le
    exact (not_le_of_gt hec) (hcg.trans hge)
  · rfl

/-- One class in a cofinal set kills any finite family of explicitly bounded germ errors. -/
theorem exists_closedClassRestrict_eq_zero_of_finset
    [Nontrivial G] [NoMaxOrder (FiniteArchimedeanClass G)]
    {s : Finset (Nonpositive G R)}
    (e : Nonpositive G R → G) (he : ∀ b ∈ s, e b < 0)
    (hbe : ∀ b ∈ s, (b : HahnSeries G R).support ⊆ Iic (e b))
    {T : Set (FiniteArchimedeanClass G)} (hT : IsCofinal T) :
    ∃ c ∈ T, ∀ b ∈ s, closedClassRestrict c b = 0 := by
  classical
  let f : s → FiniteArchimedeanClass G := fun b ↦
    FiniteArchimedeanClass.mk (e b) (he b b.2).ne
  obtain ⟨a, ha⟩ := Finset.exists_le (Finset.univ.image f)
  obtain ⟨a', haa'⟩ := exists_gt a
  obtain ⟨d, hdT, ha'd⟩ := hT a'
  refine ⟨d, hdT, fun b hb ↦ ?_⟩
  have hba : FiniteArchimedeanClass.mk (e b) (he b hb).ne ≤ a :=
    ha _ (Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_univ _, rfl⟩)
  exact closedClassRestrict_eq_zero_of_support_subset_Iic (he b hb)
    (hba.trans_lt (haa'.trans_le ha'd)) (hbe b hb)

/-- One class in a cofinal set kills any finite family of errors that vanish in the
quotient by series bounded strictly below zero. -/
theorem exists_closedClassRestrict_eq_zero_of_finset_mem_supp
    [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
    [CompleteSpace G] [NoMaxOrder (FiniteArchimedeanClass G)]
    [NoZeroDivisors R] [CharZero R]
    {s : Finset (Nonpositive G R)}
    (hs : ∀ b ∈ s, b ∈ (cantorBendixsonValuation (G := G) (R := R)).supp)
    {T : Set (FiniteArchimedeanClass G)} (hT : IsCofinal T) :
    ∃ c ∈ T, ∀ b ∈ s, closedClassRestrict c b = 0 := by
  classical
  choose e he hbe using fun b : s ↦
    (mem_cantorBendixsonValuation_supp (b : Nonpositive G R)).mp (hs b.1 b.2)
  let f : s → FiniteArchimedeanClass G := fun b ↦
    FiniteArchimedeanClass.mk (e b) (he b).ne
  obtain ⟨a, ha⟩ := Finset.exists_le (Finset.univ.image f)
  obtain ⟨a', haa'⟩ := exists_gt a
  obtain ⟨d, hdT, ha'd⟩ := hT a'
  refine ⟨d, hdT, fun b hb ↦ ?_⟩
  let b' : s := ⟨b, hb⟩
  have hba : FiniteArchimedeanClass.mk (e b') (he b').ne ≤ a :=
    ha _ (Finset.mem_image.mpr ⟨b', Finset.mem_univ _, rfl⟩)
  exact closedClassRestrict_eq_zero_of_support_subset_Iic (he b')
    (hba.trans_lt (haa'.trans_le ha'd)) (hbe b')

/-- Four refinement equations holding as germs hold exactly after restricting all representatives
at one sufficiently late class from any cofinal family. -/
theorem exists_closedClassRestrict_fourFactor_eq
    [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
    [CompleteSpace G] [NoMaxOrder (FiniteArchimedeanClass G)]
    [NoZeroDivisors R] [CharZero R]
    {a b c d e f g h : Nonpositive G R}
    (ha : Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp a =
      Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp (e * f))
    (hb : Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp b =
      Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp (g * h))
    (hc : Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp c =
      Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp (e * g))
    (hd : Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp d =
      Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := R)).supp (f * h))
    {T : Set (FiniteArchimedeanClass G)} (hT : IsCofinal T) :
    ∃ q ∈ T,
      closedClassRestrict q a = closedClassRestrict q (e * f) ∧
      closedClassRestrict q b = closedClassRestrict q (g * h) ∧
      closedClassRestrict q c = closedClassRestrict q (e * g) ∧
      closedClassRestrict q d = closedClassRestrict q (f * h) := by
  obtain ⟨q, hqT, hq⟩ := exists_closedClassRestrict_eq_zero_of_finset_mem_supp
    (fourFactorErrors_mem_supp ha hb hc hd) hT
  refine ⟨q, hqT, ?_, ?_, ?_, ?_⟩
  · have := hq (a - e * f) (by simp [fourFactorErrors])
    rw [closedClassRestrict_sub, sub_eq_zero] at this
    exact this
  · have := hq (b - g * h) (by simp [fourFactorErrors])
    rw [closedClassRestrict_sub, sub_eq_zero] at this
    exact this
  · have := hq (c - e * g) (by simp [fourFactorErrors])
    rw [closedClassRestrict_sub, sub_eq_zero] at this
    exact this
  · have := hq (d - f * h) (by simp [fourFactorErrors])
    rw [closedClassRestrict_sub, sub_eq_zero] at this
    exact this

/-- Four-factor refinement in the germ quotient yields an exact refinement after one sufficiently
late closed-class restriction. -/
theorem exists_closedClassRestrict_refinement
    [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
    [CompleteSpace G] [NoMaxOrder (FiniteArchimedeanClass G)]
    [NoZeroDivisors R] [CharZero R]
    (hrefine : HasFourFactorRefinement
      (Nonpositive G R ⧸ (cantorBendixsonValuation (G := G) (R := R)).supp))
    {a b c d : Nonpositive G R} (habcd : a * b = c * d)
    {T : Set (FiniteArchimedeanClass G)} (hT : IsCofinal T) :
    ∃ q ∈ T, ∃ e f g h : Nonpositive G R,
      closedClassRestrict q a = closedClassRestrict q e * closedClassRestrict q f ∧
      closedClassRestrict q b = closedClassRestrict q g * closedClassRestrict q h ∧
      closedClassRestrict q c = closedClassRestrict q e * closedClassRestrict q g ∧
      closedClassRestrict q d = closedClassRestrict q f * closedClassRestrict q h := by
  let J := (cantorBendixsonValuation (G := G) (R := R)).supp
  have hquot : Ideal.Quotient.mk J a * Ideal.Quotient.mk J b =
      Ideal.Quotient.mk J c * Ideal.Quotient.mk J d := by
    simpa only [map_mul] using congrArg (Ideal.Quotient.mk J) habcd
  obtain ⟨e', f', g', h', ha, hb, hc, hd⟩ := hrefine.refine hquot
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e'
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f'
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g'
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective h'
  obtain ⟨q, hqT, hqa, hqb, hqc, hqd⟩ :=
    exists_closedClassRestrict_fourFactor_eq ha hb hc hd hT
  refine ⟨q, hqT, e, f, g, h, ?_, ?_, ?_, ?_⟩
  · rwa [closedClassRestrict_mul] at hqa
  · rwa [closedClassRestrict_mul] at hqb
  · rwa [closedClassRestrict_mul] at hqc
  · rwa [closedClassRestrict_mul] at hqd

end

end HahnSeries.Nonpositive
