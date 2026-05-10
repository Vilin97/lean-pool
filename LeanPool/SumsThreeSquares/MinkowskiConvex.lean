/-
Copyright (c) 2026 Bhavik Mehta, Pietro Monticone, Abel Doñate Muñoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Pietro Monticone, Abel Doñate Muñoz
-/
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Minkowski's theorem for the standard integer lattice in `ℝⁿ`

This file specializes Minkowski's theorem on lattice points contained in convex
symmetric bodies to the standard integer lattice `ℤⁿ ⊆ EuclideanSpace ℝ (Fin n)`.

The main result, `classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`,
states that a symmetric convex set of volume greater than `2 ^ n` contains a nonzero
point all of whose coordinates are integers.
-/

namespace LeanPool.SumsThreeSquares

open MeasureTheory Module Submodule

variable {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}

private lemma euclideanSpace_F_measurableSet :
    MeasurableSet ({x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}) := by
  rw [show {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1} =
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ''
      Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) from by
    ext x
    simp only [Set.mem_Ico, Set.mem_setOf_eq, MeasurableEquiv.toLp_apply, Set.mem_image,
      Set.mem_pi, Set.mem_univ, forall_const]
    exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨_, hy, hyx⟩ => hyx ▸ hy⟩]
  exact (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableSet_image.mpr
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico)

theorem classical_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h : 2 ^ n < volume s) :
    ∃ x ≠ 0, (x ∈ s) ∧ (∀ i : Fin n, (∃ (m : ℤ), m = x i)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let L : AddSubgroup E := {
    carrier := {x : E | ∀ i, ∃ m : ℤ, (m : ℝ) = x i}
    zero_mem' := fun i => ⟨0, by simp⟩
    add_mem' := by
      intro a b ha hb i
      obtain ⟨ma, hma⟩ := ha i; obtain ⟨mb, hmb⟩ := hb i
      exact ⟨ma + mb, by
        calc
          ((ma + mb : ℤ) : ℝ) = (ma : ℝ) + mb := by norm_num
          _ = a i + b i := by rw [hma, hmb]
          _ = (a + b) i := by rfl⟩
    neg_mem' := by
      intro a ha i; obtain ⟨m, hm⟩ := ha i
      exact ⟨-m, by
        calc
          ((-m : ℤ) : ℝ) = -((m : ℤ) : ℝ) := by norm_num
          _ = -(a i) := by rw [hm]
          _ = (-a) i := by rfl⟩ }
  let F : Set E := {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}
  haveI : Countable L := by
    let f : L → (Fin n → ℤ) := fun x i => (x.property i).choose
    exact (show Function.Injective f from fun x y hxy => by
      ext1; ext i
      calc (x : E) i = (f x i : ℝ) := (x.property i).choose_spec.symm
        _ = (f y i : ℝ) := by rw [congr_fun hxy i]
        _ = (y : E) i := (y.property i).choose_spec).countable
  haveI : DiscreteTopology L := by
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have eq : ({(0 : L)} : Set L) = Subtype.val ⁻¹' Metric.ball (0 : E) (1/2) := by
      ext ⟨x, hx⟩
      simp only [Set.mem_singleton_iff, AddSubgroup.mk_eq_zero, one_div, Set.mem_preimage,
        Metric.mem_ball, dist_zero_right]
      constructor
      · intro h; subst h; norm_num
      · intro hdist; ext i; by_contra hne
        obtain ⟨m, hm⟩ := hx i
        have hm_ne : m ≠ 0 := fun h0 => by simp [h0] at hm; exact hne hm.symm
        have : (1 : ℝ) ≤ ‖x‖ := by
          rw [EuclideanSpace.norm_eq]
          apply Real.le_sqrt_of_sq_le
          grw [← Finset.single_le_sum (a := i)]
          · exact sq_le_sq.mpr (by
              simp only [abs_one, Real.norm_eq_abs, abs_abs]
              calc (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm_ne
                _ = |x i| := by rw [← hm])
          · intros; positivity
          · simp
        linarith
    rw [eq]; exact IsOpen.preimage continuous_subtype_val Metric.isOpen_ball
  have fund : IsAddFundamentalDomain L F volume := by
    apply IsAddFundamentalDomain.mk'
    · exact euclideanSpace_F_measurableSet.nullMeasurableSet
    · intro x
      let g : E := WithLp.toLp 2 (fun i => ((-⌊x i⌋ : ℤ) : ℝ))
      have hg : g ∈ L := fun i => ⟨-⌊x i⌋, rfl⟩
      use ⟨g, hg⟩
      constructor
      · intro i
        change ((-⌊x i⌋ : ℤ) : ℝ) + x i ∈ Set.Ico 0 1
        rw [Int.cast_neg, neg_add_eq_sub, Set.mem_Ico]
        exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      · intro ⟨y, hy⟩ hy_in_F; ext1; ext i
        obtain ⟨m, hm⟩ := hy i
        have h_in : (m : ℝ) + x i ∈ Set.Ico (0 : ℝ) 1 := by rw [hm]; exact hy_in_F i
        have h_floor : (-⌊x i⌋ : ℝ) + x i ∈ Set.Ico (0 : ℝ) 1 := by
          have := Int.fract_nonneg (x i); have := Int.fract_lt_one (x i)
          rw [Int.fract] at *; exact ⟨by linarith, by linarith⟩
        rw [Set.mem_Ico] at h_in h_floor
        have : m = -⌊x i⌋ := by
          by_contra hne; cases Int.lt_or_gt_of_ne hne with
          | inl hlt =>
            have : (m : ℝ) + 1 ≤ (-⌊x i⌋ : ℝ) := by
              exact_mod_cast Int.lt_iff_add_one_le.mp hlt
            linarith [h_in.2, h_floor.1]
          | inr hrt =>
            have : (-⌊x i⌋ : ℝ) + 1 ≤ (m : ℝ) := by
              exact_mod_cast Int.lt_iff_add_one_le.mp hrt
            linarith [h_in.1, h_floor.2]
        change y i = g i
        calc
          y i = (m : ℝ) := hm.symm
          _ = ((-⌊x i⌋ : ℤ) : ℝ) := by exact_mod_cast this
          _ = g i := by rfl
  have hF : volume F = 1 := by
    rw [← (PiLp.volume_preserving_toLp (ι := Fin n)).measure_preimage
      euclideanSpace_F_measurableSet.nullMeasurableSet,
      show (@WithLp.toLp 2 (Fin n → ℝ)) ⁻¹' F =
        Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1) from by
          ext x
          constructor
          · intro hx i _
            exact hx i
          · intro hx i
            exact hx i (Set.mem_univ _)]
    erw [Real.volume_pi_Ico]; norm_num
  have hmeas : volume F * 2 ^ finrank ℝ E < volume s := by
    rw [hF, show finrank ℝ E = n from by simp [E]]; simp only [one_mul]; exact h
  obtain ⟨x, hx_ne, hx_mem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv hmeas
  exact ⟨x, fun h0 => hx_ne (by ext1; simp [h0]), hx_mem, fun i => x.property i⟩

end LeanPool.SumsThreeSquares
