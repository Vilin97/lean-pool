/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.EvenSignAction

/-!
# Divisibility from the free even-sign action

For odd characteristic, the Klein four-group of even sign changes acts freely
on the punctured Markoff surface. Consequently every finite sign-invariant set
is a disjoint union of four-element sign orbits.
-/

namespace BGS.Markoff

noncomputable section

private theorem eq_zero_of_neg_eq
    {F : Type*} [Field F] (htwo : (2 : F) ≠ 0)
    {a : F} (ha : -a = a) :
    a = 0 := by
  have hmul : (2 : F) * a = 0 := by
    rw [two_mul]
    calc
      a + a = -a + a := congrArg (fun z => z + a) ha.symm
      _ = 0 := neg_add_cancel a
  exact (mul_eq_zero.mp hmul).resolve_left htwo

/-- In characteristic different from two, no nontrivial even sign change
fixes a punctured Markoff point. -/
theorem evenSign_eq_one_of_smul_eq
    {F : Type*} [Field F] (htwo : (2 : F) ≠ 0)
    (s : EvenSign) (x : PuncturedMarkoffSurface F)
    (hfixed : s • x = x) :
    s = 1 := by
  have fixedPoint :
      evenSignPoint s x.1.1 = x.1.1 := by
    exact congrArg (fun y : PuncturedMarkoffSurface F => y.1.1) hfixed
  cases s with
  | id =>
      rfl
  | neg12 =>
      have hfirst : x.1.1.x1 = 0 :=
        eq_zero_of_neg_eq htwo (congrArg Point.x1 fixedPoint)
      have hsecond : x.1.1.x2 = 0 :=
        eq_zero_of_neg_eq htwo (congrArg Point.x2 fixedPoint)
      have hthird : x.1.1.x3 = 0 := by
        have hmarkoff := x.1.2
        simp [IsMarkoff, markoffPolynomial, hfirst, hsecond] at hmarkoff
        exact hmarkoff
      exfalso
      apply x.2
      apply Subtype.ext
      ext <;> simp [surfaceOrigin, origin, hfirst, hsecond, hthird]
  | neg13 =>
      have hfirst : x.1.1.x1 = 0 :=
        eq_zero_of_neg_eq htwo (congrArg Point.x1 fixedPoint)
      have hthird : x.1.1.x3 = 0 :=
        eq_zero_of_neg_eq htwo (congrArg Point.x3 fixedPoint)
      have hsecond : x.1.1.x2 = 0 := by
        have hmarkoff := x.1.2
        simp [IsMarkoff, markoffPolynomial, hfirst, hthird] at hmarkoff
        exact hmarkoff
      exfalso
      apply x.2
      apply Subtype.ext
      ext <;> simp [surfaceOrigin, origin, hfirst, hsecond, hthird]
  | neg23 =>
      have hsecond : x.1.1.x2 = 0 :=
        eq_zero_of_neg_eq htwo (congrArg Point.x2 fixedPoint)
      have hthird : x.1.1.x3 = 0 :=
        eq_zero_of_neg_eq htwo (congrArg Point.x3 fixedPoint)
      have hfirst : x.1.1.x1 = 0 := by
        have hmarkoff := x.1.2
        simp [IsMarkoff, markoffPolynomial, hsecond, hthird] at hmarkoff
        exact hmarkoff
      exfalso
      apply x.2
      apply Subtype.ext
      ext <;> simp [surfaceOrigin, origin, hfirst, hsecond, hthird]

/-- The even-sign action on the punctured Markoff surface is free in
characteristic different from two. -/
theorem evenSign_isCancelSMul_punctured
    {F : Type*} [Field F] (htwo : (2 : F) ≠ 0) :
    IsCancelSMul EvenSign (PuncturedMarkoffSurface F) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  exact fun s x hfixed => evenSign_eq_one_of_smul_eq htwo s x hfixed

/-- The four-point orbit of a punctured point under even sign changes. -/
def evenSignOrbitFinset
    {R : Type*} [CommRing R] (x : PuncturedMarkoffSurface R) :
    Finset (PuncturedMarkoffSurface R) := by
  classical
  exact Finset.univ.image fun s : EvenSign => s • x

@[simp]
theorem mem_evenSignOrbitFinset_iff
    {R : Type*} [CommRing R] {x y : PuncturedMarkoffSurface R} :
    y ∈ evenSignOrbitFinset x ↔ ∃ s : EvenSign, s • x = y := by
  classical
  simp [evenSignOrbitFinset]

theorem evenSignOrbitFinset_eq_of_mem
    {R : Type*} [CommRing R] {x y : PuncturedMarkoffSurface R}
    (hy : y ∈ evenSignOrbitFinset x) :
    evenSignOrbitFinset y = evenSignOrbitFinset x := by
  classical
  obtain ⟨s, hs⟩ := mem_evenSignOrbitFinset_iff.mp hy
  ext z
  constructor
  · intro hz
    obtain ⟨t, ht⟩ := mem_evenSignOrbitFinset_iff.mp hz
    apply mem_evenSignOrbitFinset_iff.mpr
    refine ⟨t * s, ?_⟩
    calc
      (t * s) • x = t • (s • x) := mul_smul t s x
      _ = t • y := congrArg (t • ·) hs
      _ = z := ht
  · intro hz
    obtain ⟨u, hu⟩ := mem_evenSignOrbitFinset_iff.mp hz
    apply mem_evenSignOrbitFinset_iff.mpr
    refine ⟨u * s⁻¹, ?_⟩
    calc
      (u * s⁻¹) • y = (u * s⁻¹) • (s • x) :=
        congrArg ((u * s⁻¹) • ·) hs.symm
      _ = u • (s⁻¹ • (s • x)) := mul_smul u s⁻¹ (s • x)
      _ = u • x := congrArg (u • ·) (inv_smul_smul s x)
      _ = z := hu

theorem evenSignOrbitFinset_card_eq_four
    {F : Type*} [Field F] (htwo : (2 : F) ≠ 0)
    (x : PuncturedMarkoffSurface F) :
    (evenSignOrbitFinset x).card = 4 := by
  classical
  letI : IsCancelSMul EvenSign (PuncturedMarkoffSurface F) :=
    evenSign_isCancelSMul_punctured htwo
  have hinjective :
      Function.Injective (fun s : EvenSign => s • x) := by
    intro s t hst
    exact IsCancelSMul.right_cancel s t x hst
  calc
    (evenSignOrbitFinset x).card =
        (Finset.univ : Finset EvenSign).card := by
      exact Finset.card_image_of_injective Finset.univ hinjective
    _ = 4 := EvenSign.card_eq_four

/-- The finite family of distinct even-sign orbits meeting `C`. -/
def evenSignOrbitPartition
    {R : Type*} [CommRing R]
    (C : Finset (PuncturedMarkoffSurface R)) :
    Finset (Finset (PuncturedMarkoffSurface R)) := by
  classical
  exact C.image evenSignOrbitFinset

/-- The union of all even-sign orbits meeting `C`. This wrapper fixes one
classical equality-decider for the nested finite union. -/
def evenSignOrbitPartitionUnion
    {R : Type*} [CommRing R]
    (C : Finset (PuncturedMarkoffSurface R)) :
    Finset (PuncturedMarkoffSurface R) := by
  classical
  exact (evenSignOrbitPartition C).biUnion id

theorem evenSignOrbitPartition_pairwiseDisjoint
    {R : Type*} [CommRing R]
    (C : Finset (PuncturedMarkoffSurface R)) :
    ((evenSignOrbitPartition C : Finset
      (Finset (PuncturedMarkoffSurface R))) : Set
        (Finset (PuncturedMarkoffSurface R))).PairwiseDisjoint id := by
  classical
  intro A hA B hB hne
  change A ∈ evenSignOrbitPartition C at hA
  change B ∈ evenSignOrbitPartition C at hB
  rw [evenSignOrbitPartition] at hA hB
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hB
  change Disjoint (evenSignOrbitFinset x) (evenSignOrbitFinset y)
  rw [Finset.disjoint_left]
  intro z hzx hzy
  apply hne
  calc
    evenSignOrbitFinset x = evenSignOrbitFinset z :=
      (evenSignOrbitFinset_eq_of_mem hzx).symm
    _ = evenSignOrbitFinset y :=
      evenSignOrbitFinset_eq_of_mem hzy

theorem evenSignOrbitPartitionUnion_eq
    {R : Type*} [CommRing R]
    (C : Finset (PuncturedMarkoffSurface R))
    (hC : ∀ (s : EvenSign) (x : PuncturedMarkoffSurface R),
      x ∈ C → s • x ∈ C) :
    evenSignOrbitPartitionUnion C = C := by
  classical
  rw [evenSignOrbitPartitionUnion]
  ext z
  constructor
  · intro hz
    obtain ⟨A, hA, hzA⟩ := Finset.mem_biUnion.mp hz
    rw [evenSignOrbitPartition] at hA
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨s, rfl⟩ := mem_evenSignOrbitFinset_iff.mp hzA
    exact hC s x hx
  · intro hz
    apply Finset.mem_biUnion.mpr
    refine ⟨evenSignOrbitFinset z, ?_, ?_⟩
    · rw [evenSignOrbitPartition]
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    · exact mem_evenSignOrbitFinset_iff.mpr ⟨1, one_smul EvenSign z⟩

/-- Any finite set of punctured Markoff points preserved by all even sign
changes has cardinality divisible by four. -/
theorem four_dvd_finset_card_of_evenSign_invariant
    {F : Type*} [Field F] (htwo : (2 : F) ≠ 0)
    (C : Finset (PuncturedMarkoffSurface F))
    (hC : ∀ (s : EvenSign) (x : PuncturedMarkoffSurface F),
      x ∈ C → s • x ∈ C) :
    4 ∣ C.card := by
  classical
  let P := evenSignOrbitPartition C
  have hpartition : evenSignOrbitPartitionUnion C = C :=
    evenSignOrbitPartitionUnion_eq C hC
  have hdisjoint :
      ((P : Finset (Finset (PuncturedMarkoffSurface F))) : Set
        (Finset (PuncturedMarkoffSurface F))).PairwiseDisjoint id :=
    evenSignOrbitPartition_pairwiseDisjoint C
  have hunionCard :
      (evenSignOrbitPartitionUnion C).card =
        ∑ A ∈ P, A.card := by
    rw [evenSignOrbitPartitionUnion]
    simpa using Finset.card_biUnion hdisjoint
  have hcard :
      C.card = ∑ A ∈ P, A.card := by
    calc
      C.card = (evenSignOrbitPartitionUnion C).card :=
        congrArg Finset.card hpartition.symm
      _ = ∑ A ∈ P, A.card := hunionCard
  refine ⟨P.card, ?_⟩
  rw [hcard]
  calc
    ∑ A ∈ P, A.card = ∑ _A ∈ P, 4 := by
      apply Finset.sum_congr rfl
      intro A hA
      change A ∈ evenSignOrbitPartition C at hA
      rw [evenSignOrbitPartition] at hA
      obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hA
      exact evenSignOrbitFinset_card_eq_four htwo x
    _ = 4 * P.card := by simp [Nat.mul_comm]

end

end BGS.Markoff
