/-
Copyright (c) 2026 Matevz Miščič, Maša Žaucer, Job Petrovčič. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
-/
import LeanPool.ArtinWedderburn.IdealProd
import LeanPool.ArtinWedderburn.SetProd
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Ideal.Span

/-!
# Prime rings

Defines `IsPrimeRing R` (the ideal product version) and proves equivalence to the
elementwise version `aRb = 0 → a = 0 ∨ b = 0` and to the two-sided ideal version.
Concludes that simple rings are prime.
-/

namespace LeanPool.ArtinWedderburn

variable {R : Type*} [Ring R]

-- A ring is prime if from I * J = 0 it follows that I = 0 or J = 0 for any ideals I, J
/-- A ring is *prime* when the product of two left ideals can be zero only if at least one
of the factors is zero. -/
def IsPrimeRing (R : Type*) [Ring R] : Prop :=
  ∀ (I J : Ideal R), (I * J) = ⊥ → I = ⊥ ∨ J = ⊥

-- A ring is prime if any of the following equivalent statements hold
-- 1) from I * J = 0 follows I = 0 or J = 0
-- 2) for all a, b: if a R b = 0 then a = 0 or b = 0
-- 3) for all TWO-SIDED ideals I, J: I * J = 0 implies I = 0 or J = 0

open Pointwise Set

-- equivalence between 1) and 2)
theorem prime_ring_equiv :
    IsPrimeRing R ↔ ∀ (a b : R), bothMul a b = {0} → a = 0 ∨ b = 0 := by
  constructor
  · intro hR a b hab
    have rhs : ∀ x ∈ (leftMul a) * (leftMul b), x = (0 : R) := by
      rintro x hx
      rw [both_mul_zero_one_left_zero a b hab] at hx
      trivial
    have h := hR (leftIdealOfElement a) (leftIdealOfElement b) (Ideal.span_eq_bot.mpr rhs)
    cases h with
    | inl ha =>
      apply Or.inl
      have ainbot : a ∈ leftIdealOfElement a := by use 1; simp
      rw [ha] at ainbot
      exact ainbot
    | inr hb =>
      apply Or.inr
      have binbot : b ∈ leftIdealOfElement b := by use 1; simp
      rw [hb] at binbot
      exact binbot
  · intro h I J hIJ
    have hI : I = ⊥ ∨ I ≠ ⊥ := by apply Classical.em
    cases hI with
    | inl hi => apply Or.inl; exact hi
    | inr hi =>
      apply Or.inr
      refine (Submodule.eq_bot_iff J).mpr ?_
      obtain ⟨x, hx, hnz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hi
      intro y hy
      have hxRy : bothMul x y = {0} := by
        apply Set.ext_iff.mpr
        intro z
        constructor
        · rintro ⟨r, hr⟩
          rw [hr]
          have hry : r * y ∈ J := Ideal.mul_mem_left J r hy
          have hz : x * (r * y) ∈ (↑I : Set R) * (↑J : Set R) :=
            ⟨x, hx, r * y, hry, rfl⟩
          have k : x * r * y = 0 := by
            calc
              x * r * y = x * (r * y) := by noncomm_ring
              _ = 0 := Ideal.span_eq_bot.mp hIJ (x * (r * y)) hz
          rw [k]
          rfl
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact ⟨0, by noncomm_ring⟩
      cases h x y hxRy with
      | inl hx => contradiction
      | inr hy => exact hy

theorem span_le_two_sided_span (S : Set R) :
    Ideal.span S ≤ TwoSidedIdeal.asIdeal (TwoSidedIdeal.span S) := by
  have h : S ⊆ TwoSidedIdeal.asIdeal (TwoSidedIdeal.span S) := TwoSidedIdeal.subset_span
  exact Ideal.span_le.mpr h

theorem two_sided_ideal_equality (I J : TwoSidedIdeal R) :
    I = J ↔ (↑I : Set R) = (↑J : Set R) := SetLike.ext'_iff

theorem ideal_equality (I J : Ideal R) : I = J ↔ (↑I : Set R) = (↑J : Set R) := SetLike.ext'_iff

theorem equal_sets (I : TwoSidedIdeal R) :
    (↑(TwoSidedIdeal.asIdeal I) : Set R) = (↑I : Set R) := rfl

theorem ideal_eq_to_two_sided_ideal_eq (I J : TwoSidedIdeal R) :
    I = J ↔ TwoSidedIdeal.asIdeal I = TwoSidedIdeal.asIdeal J := by
  constructor
  · intro h
    rw [h]
  · intro h
    apply (two_sided_ideal_equality I J).mpr
    rw [← equal_sets I, ← equal_sets J]
    exact (ideal_equality (TwoSidedIdeal.asIdeal I) (TwoSidedIdeal.asIdeal J)).mp h

theorem two_sided_bot_iff_set_zero (I : TwoSidedIdeal R) : I = ⊥ ↔ (I : Set R) = {0} :=
  Iff.symm (StrictMono.apply_eq_bot_iff fun ⦃_ _⦄ a ↦ a)

theorem ideal_bot_iff_set_zero (I : Ideal R) : I = ⊥ ↔ (I : Set R) = {0} :=
  Iff.symm (StrictMono.apply_eq_bot_iff fun ⦃_ _⦄ a ↦ a)

theorem ideal_bot (I : TwoSidedIdeal R) : I = ⊥ ↔ TwoSidedIdeal.asIdeal I = ⊥ := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    apply (two_sided_bot_iff_set_zero I).mpr
    apply (ideal_bot_iff_set_zero (TwoSidedIdeal.asIdeal I)).mp h

theorem ideal_span_sub_two_sided_ideal_span (S : Set R) :
    Ideal.span S ≤ TwoSidedIdeal.asIdeal (TwoSidedIdeal.span S) := span_le_two_sided_span S

theorem same_prod (I J : TwoSidedIdeal R) :
    I * J = ⊥ → (TwoSidedIdeal.asIdeal I) * (TwoSidedIdeal.asIdeal J) = ⊥ := by
  intro h
  apply Ideal.ext
  intro x
  rw [Submodule.mem_bot]
  constructor
  · intro hx
    have rwhx : x ∈ Ideal.span ((I : Set R) * (J : Set R)) := hx
    have span_ineq := ideal_span_sub_two_sided_ideal_span ((I : Set R) * (J : Set R))
    apply span_ineq at rwhx
    have hxIJ : x ∈ (TwoSidedIdeal.asIdeal (I * J)) := span_ineq hx
    rw [h] at hxIJ
    exact hxIJ
  · intro hx
    rw [hx]
    exact Submodule.zero_mem (TwoSidedIdeal.asIdeal I * TwoSidedIdeal.asIdeal J)

theorem prime_ring_implies_prime_by_two_sided :
    IsPrimeRing R → ∀ (I J : TwoSidedIdeal R), I * J = ⊥ → I = ⊥ ∨ J = ⊥ := by
  rintro hR I J hIJ
  have hIJasIdeals := same_prod I J hIJ
  have h := hR (TwoSidedIdeal.asIdeal I) (TwoSidedIdeal.asIdeal J) hIJasIdeals
  cases h with
  | inl hi => apply Or.inl; exact (ideal_bot I).mpr hi
  | inr hj => apply Or.inr; exact (ideal_bot J).mpr hj

theorem two_sided_span_bot_el_zero (a : R) : TwoSidedIdeal.span {a} = ⊥ → a = 0 := by
  intro h
  have ha : a ∈ TwoSidedIdeal.span {a} :=
    TwoSidedIdeal.mem_span_iff.mpr fun _ a_1 ↦ a_1 rfl
  rw [h] at ha
  exact ha

/-- The two-sided multiplicative closure `RaR = {y * a * z | y, z : R}` of `a`. -/
def mulClosure (a : R) : Set R := {x : R | ∃ y z : R, x = y * a * z}

theorem mul_closure_left (a : R) :
    ∀ x y, y ∈ mulClosure a → x * y ∈ mulClosure a := by
  rintro x y ⟨y1, y2, hy⟩
  use x * y1, y2
  simp only [mul_assoc, hy]

theorem mul_closure_right (a : R) :
    ∀ y x, y ∈ mulClosure a → y * x ∈ mulClosure a := by
  rintro y x ⟨y1, y2, hy⟩
  use y1, y2 * x
  simp only [mul_assoc, hy]

theorem mul_closure_sub_span (a : R) : mulClosure a ⊆ TwoSidedIdeal.span {a} := by
  rintro x ⟨y, z, hx⟩
  rw [hx]
  have a_in_span : a ∈ TwoSidedIdeal.span {a} :=
    TwoSidedIdeal.mem_span_iff.mpr fun _ a_1 ↦ a_1 rfl
  exact TwoSidedIdeal.mul_mem_right (TwoSidedIdeal.span {a}) (y * a) z
    (TwoSidedIdeal.mul_mem_left (TwoSidedIdeal.span {a}) y a a_in_span)

theorem ideal_mul_closure (a : R) :
    AddSubgroup.closure (mulClosure a) = ((TwoSidedIdeal.span (mulClosure a)) : Set R) := by
  ext x
  have lem :=
    @TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure_absorbing R _ (mulClosure a)
      (mul_closure_left a) (mul_closure_right a) x
  exact id (Iff.symm lem)

theorem sub_span (s : Set R) (I : TwoSidedIdeal R) : s ⊆ I → TwoSidedIdeal.span s ≤ I := by
  intro h x hx
  exact TwoSidedIdeal.mem_span_iff.mp hx I h

theorem span_mul_closure_eq_span (a : R) :
    TwoSidedIdeal.span (mulClosure a) = TwoSidedIdeal.span {a} := by
  apply le_antisymm
  · apply sub_span (mulClosure a) (TwoSidedIdeal.span {a})
    exact mul_closure_sub_span a
  · apply TwoSidedIdeal.span_mono
    intro x hx
    rw [hx]
    use 1, 1
    simp

lemma both_mul_zero {a b x y : R} (hab : bothMul a b = {0}) (hx : x ∈ mulClosure a)
    (hy : y ∈ mulClosure b) : x * y = 0 := by
  obtain ⟨x1, x2, hx⟩ := hx
  obtain ⟨y1, y2, hy⟩ := hy
  have prod_in_both_mul : a * (x2 * y1) * b ∈ bothMul a b := ⟨x2 * y1, rfl⟩
  have prod_zero : a * (x2 * y1) * b = 0 := by
    rw [hab] at prod_in_both_mul
    exact prod_in_both_mul
  rw [hx, hy]
  calc
    x1 * a * x2 * (y1 * b * y2) = x1 * (a * (x2 * y1) * b) * y2 := by noncomm_ring
    _ = 0 := by rw [prod_zero]; noncomm_ring

lemma span_mul_closure_bot_forall {a b x y : R} (hab : bothMul a b = {0})
    (hx : x ∈ AddSubgroup.closure (mulClosure a)) (hy : y ∈ mulClosure b) : x * y = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz => apply both_mul_zero hab hz hy
  | zero => simp
  | add u v hu hv ihu ihv =>
    noncomm_ring
    rw [ihu, ihv]
    simp
  | neg u hu ihu =>
    noncomm_ring
    rw [ihu]
    simp

lemma span_mul_closure_bot_forall' {a b x y : R} (hab : bothMul a b = {0})
    (hx : x ∈ TwoSidedIdeal.span {a}) (hy : y ∈ mulClosure b) : x * y = 0 := by
  rw [← span_mul_closure_eq_span a] at hx
  apply span_mul_closure_bot_forall hab
  · have hx' : x ∈ (AddSubgroup.closure (mulClosure a) : Set R) := by
      rwa [ideal_mul_closure a]
    exact hx'
  · exact hy

theorem span_mul_closure_bot (a b : R) (hab : bothMul a b = {0}) :
    (TwoSidedIdeal.span {a} : Set R) * (mulClosure b) = {0} := by
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, h⟩
    simp only at h
    rw [span_mul_closure_bot_forall' hab hy hz] at h
    rw [← h]
    rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    refine ⟨0, TwoSidedIdeal.zero_mem _, 0, ⟨0, 0, by noncomm_ring⟩, by noncomm_ring⟩

lemma two_sided_span_bot_forall {a b x y : R} (hab : bothMul a b = {0})
    (hx : x ∈ TwoSidedIdeal.span {a}) (hy : y ∈ AddSubgroup.closure (mulClosure b)) :
    x * y = 0 := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    apply span_mul_closure_bot_forall' hab
    · exact hx
    · exact hz
  | zero => simp
  | add u v hu hv ihu ihv =>
    noncomm_ring
    rw [ihu, ihv]
    simp
  | neg u hu ihu =>
    noncomm_ring
    rw [ihu]
    simp

lemma span_mul_span_bot' (a b : R) (hab : bothMul a b = {0}) :
    (TwoSidedIdeal.span {a} : Set R) * (AddSubgroup.closure (mulClosure b)) = {0} := by
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, h⟩
    simp only at h
    rw [two_sided_span_bot_forall hab hy hz] at h
    rw [← h]
    rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    refine ⟨0, TwoSidedIdeal.zero_mem _, 0,
      zero_mem (AddSubgroup.closure (mulClosure b)), by noncomm_ring⟩

theorem span_mul_span_bot (a b : R) (hab : bothMul a b = {0}) :
    (TwoSidedIdeal.span {a} : Set R) * (TwoSidedIdeal.span {b} : Set R) = {0} := by
  have k : (TwoSidedIdeal.span {b} : Set R) = AddSubgroup.closure (mulClosure b) := by
    rw [← span_mul_closure_eq_span b, ideal_mul_closure b]
  rw [k]
  exact span_mul_span_bot' a b hab

theorem bothmul_zero_implies_prod_zero (a b : R) :
    bothMul a b = {0} → TwoSidedIdeal.span {a} * TwoSidedIdeal.span {b} = ⊥ := by
  intro hab
  have k : TwoSidedIdeal.span ({0} : Set R) = ⊥ := Eq.symm (TwoSidedIdealProd.ideal_eq_span ⊥)
  rw [TwoSidedIdealProd.mul_two_sided_ideal_eq_span]
  unfold TwoSidedIdealProd.ringSubsetProdTwoSidedIdeal
  rw [← k]
  rw [span_mul_span_bot a b hab]

theorem prime_for_two_sided_implies_condition2 :
    (∀ (I J : TwoSidedIdeal R), I * J = ⊥ → I = ⊥ ∨ J = ⊥) →
      (∀ (a b : R), bothMul a b = {0} → a = 0 ∨ b = 0) := by
  rintro hR a b hab
  have RaRbR_zero : TwoSidedIdeal.span {a} * TwoSidedIdeal.span {b} = ⊥ :=
    bothmul_zero_implies_prod_zero a b hab
  have h := hR (TwoSidedIdeal.span {a}) (TwoSidedIdeal.span {b}) RaRbR_zero
  cases h with
  | inl ha => apply Or.inl; exact two_sided_span_bot_el_zero a ha
  | inr hb => apply Or.inr; exact two_sided_span_bot_el_zero b hb

-- equivalence between 1) and 3)
theorem prime_ring_equiv' :
    IsPrimeRing R ↔ ∀ (I J : TwoSidedIdeal R), I * J = ⊥ → I = ⊥ ∨ J = ⊥ := by
  constructor
  · exact prime_ring_implies_prime_by_two_sided
  · intro hR
    exact prime_ring_equiv.mpr (prime_for_two_sided_implies_condition2 hR)

-- Every simple ring is prime
theorem simple_ring_is_prime [IsSimpleRing R] : IsPrimeRing R := by
  apply prime_ring_equiv'.mpr
  intro I J hIJ
  cases eq_bot_or_eq_top I with
  | inl hi => apply Or.inl; exact hi
  | inr hi =>
    apply Or.inr
    cases eq_bot_or_eq_top J with
    | inl hj => exact hj
    | inr hj =>
      have h : I * J = ⊤ := by
        apply (TwoSidedIdeal.one_mem_iff (I * J)).mp
        apply TwoSidedIdeal.subset_span
        refine ⟨1, by rw [hi]; trivial, 1, by rw [hj]; trivial, by noncomm_ring⟩
      rw [hIJ] at h
      have k : (⊥ : TwoSidedIdeal R) ≠ (⊤ : TwoSidedIdeal R) := bot_ne_top
      absurd h
      trivial

end LeanPool.ArtinWedderburn
