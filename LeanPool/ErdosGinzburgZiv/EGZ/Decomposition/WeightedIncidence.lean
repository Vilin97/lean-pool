/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Mass

/-!
# A finite weighted incidence bound

If all but a bounded number of sets containing a finite configuration have
uniformly positive mass outside its closure, and adjoining such an outside
point increases a bounded rank, the number of sets containing a point is
uniformly bounded. This is the counting induction used for large faces.
-/

open scoped BigOperators

namespace EGZ.WeightedIncidence

attribute [local instance] Classical.propDecidable

variable {α I : Type*} [Fintype α] [Fintype I]

/-- Mass of a set for a finite real-valued weight. -/
noncomputable def mass (w : α → ℝ) (S : Set α) : ℝ :=
  ∑ a, if a ∈ S then w a else 0

@[simp]
theorem mass_natCast (w : α → ℕ) (S : Set α) :
    mass (fun a ↦ (w a : ℝ)) S = (natMassOn w S : ℝ) := by
  simp [mass, natMassOn]

theorem mass_nonneg (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (S : Set α) :
    0 ≤ mass w S := Finset.sum_nonneg (fun a _ ↦ by split_ifs; exact hw a; exact le_rfl)

theorem mass_mono (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) {S T : Set α}
    (hST : S ⊆ T) : mass w S ≤ mass w T := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hS : a ∈ S
  · simp [hS, hST hS]
  · simp only [hS, ite_false]
    split_ifs
    · exact hw a
    · exact le_rfl

theorem mass_le_total (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (S : Set α) :
    mass w S ≤ ∑ a, w a := by
  simpa [mass] using mass_mono w hw (Set.subset_univ S)

theorem mass_diff_add_inter (w : α → ℝ) (S T : Set α) :
    mass w (S \ T) + mass w (S ∩ T) = mass w S := by
  rw [mass, mass, ← Finset.sum_add_distrib, mass]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hS : a ∈ S <;> by_cases hT : a ∈ T <;> simp [hS, hT]

/-- Restricting the common weight does not alter masses inside the retained set. -/
theorem mass_restrict_eq_of_subset (w : α → ℝ) (S T : Set α) (hTS : T ⊆ S) :
    mass (fun a ↦ if a ∈ S then w a else 0) T = mass w T := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ T
  · simp [ha, hTS ha]
  · simp [ha]

/-- The members of a family that contain every point of a finite set. -/
noncomputable def containing (F : I → Set α) (S : Finset α) : Finset I :=
  Finset.univ.filter fun i ↦ ∀ a ∈ S, a ∈ F i

@[simp]
theorem mem_containing (F : I → Set α) (S : Finset α) (i : I) :
    i ∈ containing F S ↔ ∀ a ∈ S, a ∈ F i := by simp [containing]

/-- The recurrence has one bounded exceptional contribution at each rank. -/
noncomputable def bound (c b : ℝ) : ℕ → ℝ
  | 0 => c
  | r + 1 => c + bound c b r / b

theorem bound_nonneg {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) (r : ℕ) :
    0 ≤ bound c b r := by
  induction r with
  | zero => exact hc
  | succ r ih => exact add_nonneg hc (div_nonneg ih hb)

/-- A convenient closed-form majorant for the recursive bound. -/
theorem bound_le_pow {c b : ℝ} (hc : 0 ≤ c) (hb : 0 < b) (r : ℕ) :
    bound c b r ≤ (c + 1 + b⁻¹) ^ (r + 1) := by
  have hi : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
  have hbase : 1 ≤ c + 1 + b⁻¹ := by linarith
  induction r with
  | zero => simpa only [bound, Nat.zero_add, pow_one] using (by linarith : c ≤ c + 1 + b⁻¹)
  | succ r ih =>
    have hp : 1 ≤ (c + 1 + b⁻¹) ^ (r + 1) := one_le_pow₀ hbase
    have hc' : c ≤ c * (c + 1 + b⁻¹) ^ (r + 1) := by nlinarith
    have hi' := mul_le_mul_of_nonneg_right ih hi
    simp only [bound, div_eq_mul_inv, pow_succ] at *
    nlinarith

omit [Fintype I] in
/-- Exchange the two finite sums and count incidences at each atom. -/
theorem sum_mass_eq (w : α → ℝ) (F : I → Set α) (G : Finset I) (U : Set α) :
    ∑ i ∈ G, mass w (F i ∩ U) =
      ∑ a, if a ∈ U then ((G.filter fun i ↦ a ∈ F i).card : ℝ) * w a else 0 := by
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ U
  · simp only [Set.mem_inter_iff, ha, and_true, ite_true]
    rw [← Finset.sum_filter]
    simp
  · simp [ha]

/-- Abstract closure-and-rank induction. Exceptional sets need not be
members of the containing family; only their cardinality is used. -/
theorem card_containing_le
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hM : 0 < ∑ a, w a)
    (F : I → Set α) (rank : Finset α → ℕ) (closure : Finset α → Set α)
    (exceptional : Finset α → Finset I) (c d : ℕ) (b : ℝ) (hb : 0 < b)
    (hrank : ∀ S, rank S ≤ d)
    (hinsert : ∀ S, S.Nonempty → ∀ a, a ∉ closure S → rank S < rank (insert a S))
    (hexceptional : ∀ S, S.Nonempty → (exceptional S).card ≤ c)
    (hescape : ∀ S, S.Nonempty → ∀ i ∈ containing F S, i ∉ exceptional S →
      b * (∑ a, w a) ≤ mass w (F i \ closure S)) :
    ∀ r S, S.Nonempty → d ≤ rank S + r →
      ((containing F S).card : ℝ) ≤ bound c b r := by
  classical
  intro r
  induction r with
  | zero =>
    intro S hS hdim
    have hcl : closure S = Set.univ := by
      apply Set.eq_univ_of_forall
      intro a
      by_contra ha
      have hi := hinsert S hS a ha
      have hu := hrank (insert a S)
      omega
    have hsub : containing F S ⊆ exceptional S := by
      intro i hi
      by_contra he
      have hx := hescape S hS i hi he
      have hpos := mul_pos hb hM
      simp only [hcl, Set.sdiff_univ, mass, Set.mem_empty_iff_false, ite_false,
        Finset.sum_const_zero] at hx
      linarith
    change ((containing F S).card : ℝ) ≤ c
    exact_mod_cast (Finset.card_le_card hsub).trans (hexceptional S hS)
  | succ r ih =>
    intro S hS hdim
    let G := containing F S \ exceptional S
    have hcount : ((containing F S).card : ℝ) ≤ (G.card : ℝ) + c := by
      exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := containing F S)
        (t := exceptional S)).trans (Nat.add_le_add_left (hexceptional S hS) _)
    have hpoint : ∀ a ∉ closure S,
        ((G.filter fun i ↦ a ∈ F i).card : ℝ) ≤ bound c b r := by
      intro a ha
      have hsub : G.filter (fun i ↦ a ∈ F i) ⊆ containing F (insert a S) := by
        intro i hi
        obtain ⟨hiG, hai⟩ := Finset.mem_filter.mp hi
        have hiS := (mem_containing F S i).mp (Finset.mem_sdiff.mp hiG).1
        exact (mem_containing F _ i).mpr (fun z hz ↦ by
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hai
          · exact hiS z hz)
      have hdim' : d ≤ rank (insert a S) + r := by
        have hi := hinsert S hS a ha
        omega
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (ih (insert a S) (Finset.insert_nonempty _ _) hdim')
    have hdouble : (G.card : ℝ) * (b * ∑ a, w a) ≤
        bound c b r * ∑ a, w a := calc
      (G.card : ℝ) * (b * ∑ a, w a) = ∑ _i ∈ G, b * ∑ a, w a := by simp
      _ ≤ ∑ i ∈ G, mass w (F i \ closure S) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hescape S hS i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2
      _ = ∑ a, if a ∉ closure S then
          ((G.filter fun i ↦ a ∈ F i).card : ℝ) * w a else 0 :=
        by simpa only [Set.sdiff_eq, Set.mem_compl_iff] using sum_mass_eq w F G (closure S)ᶜ
      _ ≤ ∑ a, bound c b r * w a := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : a ∈ closure S
        · simp only [ha, not_true_eq_false, ite_false]
          exact mul_nonneg (bound_nonneg (Nat.cast_nonneg c) hb.le r) (hw a)
        · simp only [ha, not_false_eq_true, ite_true]
          exact mul_le_mul_of_nonneg_right (hpoint a ha) (hw a)
      _ = bound c b r * ∑ a, w a := (Finset.mul_sum _ _ _).symm
    have hG : (G.card : ℝ) ≤ bound c b r / b := by
      apply (le_div_iff₀ hb).mpr
      apply (mul_le_mul_iff_right₀ hM).mp
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hdouble
    exact hcount.trans (by dsimp [bound]; linarith)

/-- If each member also has positive relative mass, the entire family has
a uniform cardinality bound. -/
theorem card_family_le
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hM : 0 < ∑ a, w a)
    (F : I → Set α) (rank : Finset α → ℕ) (closure : Finset α → Set α)
    (exceptional : Finset α → Finset I) (c d : ℕ) (b e : ℝ) (hb : 0 < b) (he : 0 < e)
    (hrank : ∀ S, rank S ≤ d)
    (hinsert : ∀ S, S.Nonempty → ∀ a, a ∉ closure S → rank S < rank (insert a S))
    (hexceptional : ∀ S, S.Nonempty → (exceptional S).card ≤ c)
    (hescape : ∀ S, S.Nonempty → ∀ i ∈ containing F S, i ∉ exceptional S →
      b * (∑ a, w a) ≤ mass w (F i \ closure S))
    (hlarge : ∀ i, e * (∑ a, w a) ≤ mass w (F i)) :
    (Fintype.card I : ℝ) ≤ bound c b d / e := by
  classical
  have hpoint : ∀ a, ((Finset.univ.filter fun i ↦ a ∈ F i).card : ℝ) ≤ bound c b d := by
    intro a
    simpa [containing] using card_containing_le w hw hM F rank closure exceptional c d b hb
      hrank hinsert hexceptional hescape d {a} (Finset.singleton_nonempty a) (by omega)
  have hdouble : (Fintype.card I : ℝ) * (e * ∑ a, w a) ≤
      bound c b d * ∑ a, w a := calc
    (Fintype.card I : ℝ) * (e * ∑ a, w a) = ∑ _i : I, e * ∑ a, w a := by simp
    _ ≤ ∑ i : I, mass w (F i) := Finset.sum_le_sum (fun i _ ↦ hlarge i)
    _ = ∑ a, ((Finset.univ.filter fun i ↦ a ∈ F i).card : ℝ) * w a := by
      simpa using sum_mass_eq w F Finset.univ Set.univ
    _ ≤ ∑ a, bound c b d * w a :=
      Finset.sum_le_sum (fun a _ ↦ mul_le_mul_of_nonneg_right (hpoint a) (hw a))
    _ = bound c b d * ∑ a, w a := (Finset.mul_sum _ _ _).symm
  apply (le_div_iff₀ he).mpr
  apply (mul_le_mul_iff_right₀ hM).mp
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hdouble

end EGZ.WeightedIncidence
