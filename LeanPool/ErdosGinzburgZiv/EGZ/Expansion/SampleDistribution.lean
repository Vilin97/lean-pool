/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.FiniteProbability
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.ThickSupport

/-!
# Mixtures of valid finite samples

Each component has total mass at most one.  Removing a small exceptional
set from every sample space retains positive mass and preserves thickness
provided one component witnesses escape from each central slab.
-/

open scoped BigOperators

namespace EGZ.Expansion

section FiniteSamples

variable {I β : Type*} [Fintype I] [Fintype β]
  (A : I → Type*) [∀ i, Fintype (A i)]
  (value : ∀ i, A i → β) (valid : ∀ i, A i → Prop)

open Classical in
/-- Equal mixture of the valid samples, retaining their vector values. -/
noncomputable def sampleWeight (v : β) : ℝ :=
  ∑ i, finiteProb (fun x : A i ↦ valid i x ∧ value i x = v)

omit [Fintype β] in
open Classical in
theorem sampleWeight_nonneg (v : β) : 0 ≤ sampleWeight A value valid v :=
  Finset.sum_nonneg (fun _i _ ↦ finiteProb_nonneg _)

open Classical in
theorem finiteProb_sum_fibres {α : Type*} [Fintype α]
    (f : α → β) (Q : α → Prop) (P : β → Prop) :
    (∑ v, if P v then finiteProb (fun x ↦ Q x ∧ f x = v) else 0) =
      finiteProb (fun x ↦ Q x ∧ P (f x)) := by
  classical
  have hterm (v : β) : (if P v then finiteProb (fun x ↦ Q x ∧ f x = v) else 0) =
      finiteProb (fun x ↦ Q x ∧ f x = v ∧ P v) := by
    by_cases hv : P v <;> simp [hv]
  simp_rw [hterm]
  unfold finiteProb
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  by_cases hx : Q x
  · simp only [hx, true_and]
    by_cases hp : P (f x)
    · have heq (v : β) : (f x = v ∧ P v) ↔ f x = v := by
        constructor
        · exact And.left
        · intro h; exact ⟨h, h ▸ hp⟩
      simp only [heq, ite_eq_left hp]
      simp
    · have heq (v : β) : ¬(f x = v ∧ P v) := by
        rintro ⟨rfl, hv⟩
        exact hp hv
      simp only [heq, ↓reduceIte, Finset.sum_const_zero, ite_eq_right hp]
  · simp [hx]

open Classical in
/-- Mass on a set of vectors is the sum of the corresponding valid-sample
probabilities over all components. -/
theorem sampleWeight_massOn (P : β → Prop) :
    (∑ v, if P v then sampleWeight A value valid v else 0) =
      ∑ i, finiteProb (fun x : A i ↦ valid i x ∧ P (value i x)) := by
  classical
  simp only [sampleWeight]
  have heq (v : β) :
      (if P v then ∑ i, finiteProb (fun x : A i ↦ valid i x ∧ value i x = v) else 0) =
      ∑ i, if P v then finiteProb (fun x : A i ↦ valid i x ∧ value i x = v) else 0 := by
    by_cases hv : P v <;> simp [hv]
  simp_rw [heq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact finiteProb_sum_fibres (value i) (valid i) P

open Classical in
theorem sampleWeight_mass : (∑ v, sampleWeight A value valid v) =
    ∑ i, finiteProb (valid i) := by
  simpa using sampleWeight_massOn A value valid (fun _ ↦ True)

variable [∀ i, Nonempty (A i)]

open Classical in
theorem sampleWeight_mass_le : (∑ v, sampleWeight A value valid v) ≤ Fintype.card I := by
  rw [sampleWeight_mass]
  calc
    (∑ i, finiteProb (valid i)) ≤ ∑ _i : I, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ finiteProb_le_one _
    _ = _ := by simp

open Classical in
theorem sampleWeight_mass_ge {e : ℝ}
    (hbad : ∀ i, finiteProb (fun x : A i ↦ ¬valid i x) ≤ e) :
    (Fintype.card I : ℝ) * (1 - e) ≤ ∑ v, sampleWeight A value valid v := by
  rw [sampleWeight_mass]
  calc
    _ = ∑ _i : I, (1 - e) := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hh := hbad i
      rw [finiteProb_not] at hh
      linarith

omit [Fintype β] [∀ (i : I), Nonempty (A i)] in
open Classical in
theorem sampleWeight_pos_exists {v : β} (hv : 0 < sampleWeight A value valid v) :
    ∃ (i : I) (x : A i), valid i x ∧ value i x = v := by
  classical
  by_contra! hn
  have hzero : sampleWeight A value valid v = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have heq : (fun x : A i ↦ valid i x ∧ value i x = v) = (fun _ ↦ False) := by
      funext x
      exact propext ⟨fun h ↦ hn i x h.1 h.2, False.elim⟩
    rw [heq, finiteProb_false]
  linarith

end FiniteSamples

open Classical in
/-- Removing an exceptional set loses at most its probability from any
event, without any independence assumption. -/
theorem finiteProb_and_ge_sub {A : Type*} [Fintype A]
    (P Q : A → Prop) : finiteProb Q - finiteProb (fun x ↦ ¬P x) ≤
      finiteProb (fun x ↦ P x ∧ Q x) := by
  classical
  unfold finiteProb
  rw [← Finset.expect_sub_distrib]
  apply Finset.expect_le_expect
  intro x _
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]

section Thickness

variable {p d W : ℕ} [NeZero p]
  {I : Type*} [Fintype I] [Nonempty I]
  (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
  (value : ∀ i, A i → FpCoord p d) (valid : ∀ i, A i → Prop)
  {η : ℝ} (hη : 0 < η) (hηone : η ≤ 1)
  (hbad : ∀ i, finiteProb (fun x : A i ↦ ¬valid i x) ≤ η / 2)

include hη hηone hbad

omit hη in
open Classical in
theorem sampleWeight_mass_pos : 0 < ∑ v, sampleWeight A value valid v := by
  have hh := sampleWeight_mass_ge A value valid hbad
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have : 0 < (Fintype.card I : ℝ) * (1 - η / 2) := mul_pos hI (by linarith)
  linarith

omit hηone in
open Classical in
theorem sampleWeight_centrallyThick
    (hout : ∀ ξ : FpCoord p d →ₗ[ZMod p] ZMod p, ξ ≠ 0 →
      ∃ i, η ≤ finiteProb (fun x : A i ↦
        ¬ HasBoundedRepresentative p W (ξ (value i x)))) :
    IsCentrallyThick (sampleWeight A value valid) W (η / (2 * Fintype.card I)) := by
  classical
  intro ξ hξ
  obtain ⟨i, hi⟩ := hout ξ hξ
  have hsample : η / 2 ≤ finiteProb (fun x : A i ↦ valid i x ∧
      ¬ HasBoundedRepresentative p W (ξ (value i x))) := by
    have hh := finiteProb_and_ge_sub (valid i)
      (fun x ↦ ¬ HasBoundedRepresentative p W (ξ (value i x)))
    have hb := hbad i
    linarith
  have hsum : η / 2 ≤ ∑ j, finiteProb (fun x : A j ↦ valid j x ∧
      ¬ HasBoundedRepresentative p W (ξ (value j x))) :=
    hsample.trans (Finset.single_le_sum
      (f := fun j ↦ finiteProb (fun x : A j ↦ valid j x ∧
        ¬ HasBoundedRepresentative p W (ξ (value j x))))
      (fun j _ ↦ finiteProb_nonneg _) (Finset.mem_univ i))
  have hmass := sampleWeight_mass_le A value valid
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  calc
    η / (2 * Fintype.card I) * (∑ v, sampleWeight A value valid v) ≤
        η / (2 * Fintype.card I) * Fintype.card I :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = η / 2 := by field_simp
    _ ≤ ∑ j, finiteProb (fun x : A j ↦ valid j x ∧
        ¬ HasBoundedRepresentative p W (ξ (value j x))) := hsum
    _ = _ := by
      rw [← sampleWeight_massOn A value valid (fun v ↦ ¬ HasBoundedRepresentative p W (ξ v))]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> rfl

end Thickness

end EGZ.Expansion
