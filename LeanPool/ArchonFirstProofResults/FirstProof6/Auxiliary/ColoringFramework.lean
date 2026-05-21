/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Problem 6: Large epsilon-light vertex subsets -- Coloring Framework

`PartialColoring` structure, pigeonhole, coloring iteration, and barrier parameter bound.
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

structure PartialColoring (V : Type*) [Fintype V] (r : ℕ) where
  colored : Finset V
  color : V → Fin r

omit [DecidableEq V] in
lemma largest_color_class_bound
    (pc : PartialColoring V r) (hr : 0 < r) :
    ∃ γ : Fin r,
      (pc.colored.filter (fun v => pc.color v = γ)).card * r ≥
        pc.colored.card := by
  classical
  by_contra hall
  push Not at hall
  have hsum : pc.colored.card =
      ∑ γ : Fin r, (pc.colored.filter (fun v => pc.color v = γ)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext v; simp [Finset.mem_biUnion, Finset.mem_filter]
    · intro i _ j _ hij
      exact Finset.disjoint_filter.mpr fun _ _ h1 h2 => hij (h1 ▸ h2)
  have hlt : ∑ γ : Fin r, (pc.colored.filter (fun v => pc.color v = γ)).card * r <
      ∑ _ : Fin r, pc.colored.card :=
    Finset.sum_lt_sum (fun γ _ => le_of_lt (hall γ))
      ⟨⟨0, hr⟩, Finset.mem_univ _, hall ⟨0, hr⟩⟩
  rw [← Finset.sum_mul, Finset.sum_const_nat (fun _ _ => rfl),
      Finset.card_univ, Fintype.card_fin, hsum, Nat.mul_comm] at hlt
  exact lt_irrefl _ hlt

lemma coloring_step_exists
    (ε : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (n : ℕ) (hn : 4 ≤ n)
    (r : ℕ) (hr_def : r = Nat.ceil (16 / ε))
    (A : V → Fin r → Matrix V V ℝ)
    (_hA_psd : ∀ v γ, (A v γ).PosSemidef)
    (t : ℕ) (_ht : t < n / 4)
    (pc : PartialColoring V r)
    (hcard : pc.colored.card = t)
    (hcard_le : t < Fintype.card V)
    (u_t : ℝ) (hu_t : u_t = ε / 2 + (t : ℝ) * (ε / (n : ℝ)))
    (hA_small : ∀ v, ∃ γ : Fin r,
      ((ε / (n : ℝ)) • (1 : Matrix V V ℝ) - A v γ).PosSemidef)
    (hbarrier : ∀ γ : Fin r,
      (u_t • (1 : Matrix V V ℝ) -
        ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ), A v γ).PosSemidef) :
    let u_t' := ε / 2 + ((t : ℝ) + 1) * (ε / (n : ℝ))
    ∃ (pc' : PartialColoring V r),
      pc'.colored.card = t + 1 ∧
      pc.colored ⊆ pc'.colored ∧
      (∀ γ : Fin r,
        (u_t' • (1 : Matrix V V ℝ) -
          ∑ v ∈ pc'.colored.filter (fun v => pc'.color v = γ), A v γ).PosSemidef) := by
  intro u_t'
  have h_exists_uncolored : ∃ v₀ : V, v₀ ∉ pc.colored := by
    by_contra hall; push Not at hall
    have hsub : Finset.univ ⊆ pc.colored := fun x _ => hall x
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this; omega
  obtain ⟨v₀, hv₀⟩ := h_exists_uncolored
  have hr_pos : 0 < r := by rw [hr_def]; exact Nat.ceil_pos.mpr (by positivity)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hu_diff : u_t' - u_t = ε / (n : ℝ) := by rw [hu_t]; ring
  have hu_diff_nn : (0 : ℝ) ≤ u_t' - u_t := by rw [hu_diff]; positivity
  suffices h_exists_color : ∃ (γ₀ : Fin r),
      (u_t' • (1 : Matrix V V ℝ) -
        (∑ v ∈ pc.colored.filter (fun v => pc.color v = γ₀),
          A v γ₀ + A v₀ γ₀)).PosSemidef by
    obtain ⟨γ₀, hγ₀_psd⟩ := h_exists_color
    set color' : V → Fin r := fun v => if v = v₀ then γ₀ else pc.color v with hcolor'_def
    set colored' := pc.colored ∪ {v₀} with hcolored'_def
    refine ⟨⟨colored', color'⟩, ?_, ?_, ?_⟩
    · rw [hcolored'_def, Finset.card_union_of_disjoint
        (Finset.disjoint_singleton_right.mpr hv₀)]
      simp [hcard]
    · exact Finset.subset_union_left
    · intro γ
      have hcolor'_old : ∀ w ∈ pc.colored, color' w = pc.color w := by
        intro w hw
        simp [hcolor'_def, show w ≠ v₀ from fun h => hv₀ (h ▸ hw)]
      have hcolor'_v₀ : color' v₀ = γ₀ := by simp [hcolor'_def]
      by_cases hγ : γ = γ₀
      · have h_filter_eq : colored'.filter (fun v => color' v = γ₀) =
            (pc.colored.filter (fun v => pc.color v = γ₀)) ∪ {v₀} := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, hcolored'_def]
          constructor
          · rintro ⟨hw_old | hw_new, hw_col⟩
            · exact Or.inl ⟨hw_old, (hcolor'_old w hw_old) ▸ hw_col⟩
            · exact Or.inr hw_new
          · rintro (⟨hw_old, hw_col⟩ | hw_eq)
            · exact ⟨Or.inl hw_old, (hcolor'_old _ hw_old) ▸ hw_col⟩
            · exact ⟨Or.inr hw_eq, hw_eq ▸ hcolor'_v₀⟩
        rw [hγ, h_filter_eq,
            Finset.sum_union (Finset.disjoint_singleton_right.mpr
              (fun hmem => hv₀ (Finset.mem_of_mem_filter _ hmem))),
            Finset.sum_singleton]
        exact hγ₀_psd
      · have h_filter_eq : colored'.filter (fun v => color' v = γ) =
            pc.colored.filter (fun v => pc.color v = γ) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, hcolored'_def]
          constructor
          · rintro ⟨hw_old | hw_new, hw_col⟩
            · exact ⟨hw_old, (hcolor'_old w hw_old) ▸ hw_col⟩
            · exfalso; rw [hw_new, hcolor'_v₀] at hw_col; exact hγ hw_col.symm
          · rintro ⟨hw_old, hw_col⟩
            exact ⟨Or.inl hw_old, (hcolor'_old _ hw_old) ▸ hw_col⟩
        rw [h_filter_eq, show u_t' • (1 : Matrix V V ℝ) -
            ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ), A v γ =
            (u_t • (1 : Matrix V V ℝ) -
              ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ), A v γ) +
            (u_t' - u_t) • (1 : Matrix V V ℝ) from by simp only [sub_smul]; abel]
        exact (hbarrier γ).add (Matrix.PosSemidef.one.smul hu_diff_nn)
  obtain ⟨γ₀, hγ₀⟩ := hA_small v₀
  refine ⟨γ₀, ?_⟩
  rw [show u_t' • (1 : Matrix V V ℝ) -
      (∑ v ∈ pc.colored.filter (fun v => pc.color v = γ₀), A v γ₀ + A v₀ γ₀) =
      (u_t • (1 : Matrix V V ℝ) -
        ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ₀), A v γ₀) +
      ((ε / (n : ℝ)) • (1 : Matrix V V ℝ) - A v₀ γ₀) from by
        have : u_t' = u_t + ε / (n : ℝ) := by rw [hu_t]; ring
        rw [this, add_smul]; abel]
  exact (hbarrier γ₀).add hγ₀

lemma coloring_iterate
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (hn : 4 ≤ n) (hn_eq : n = Fintype.card V)
    (r : ℕ) (hr_def : r = Nat.ceil (16 / ε))
    (A : V → Fin r → Matrix V V ℝ)
    (hA_psd : ∀ v γ, (A v γ).PosSemidef)
    (hA_small : ∀ v, ∃ γ : Fin r,
      ((ε / (n : ℝ)) • (1 : Matrix V V ℝ) - A v γ).PosSemidef)
    (k : ℕ) (hk : k = n / 4) :
    let u_k := ε / 2 + (k : ℝ) * (ε / (n : ℝ))
    ∃ (pc : PartialColoring V r),
      pc.colored.card = k ∧
      (∀ γ : Fin r,
        (u_k • (1 : Matrix V V ℝ) -
          ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ), A v γ).PosSemidef) := by
  subst hk
  suffices h : ∀ t : ℕ, t ≤ n / 4 →
      ∃ (pc : PartialColoring V r),
        pc.colored.card = t ∧
        (∀ γ : Fin r,
          ((ε / 2 + (t : ℝ) * (ε / (n : ℝ))) • (1 : Matrix V V ℝ) -
            ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ), A v γ).PosSemidef) by
    exact h (n / 4) le_rfl
  intro t
  induction t with
  | zero =>
    intro _
    have hr_pos : 0 < r := by rw [hr_def]; exact Nat.ceil_pos.mpr (by positivity)
    refine ⟨⟨∅, fun _ => ⟨0, hr_pos⟩⟩, by simp, ?_⟩
    intro γ
    simp only [Finset.filter_empty, Finset.sum_empty, sub_zero, Nat.cast_zero, zero_mul, add_zero]
    exact Matrix.PosSemidef.one.smul (by linarith : (0 : ℝ) ≤ ε / 2)
  | succ t ih =>
    intro ht_succ
    obtain ⟨pc_t, hcard_t, hbarrier_t⟩ := ih (by omega)
    obtain ⟨pc', hcard', _, hbarrier'⟩ :=
      coloring_step_exists ε hε hε1 n hn r hr_def A hA_psd t (by omega) pc_t hcard_t (by omega)
        (ε / 2 + (t : ℝ) * (ε / (n : ℝ))) rfl hA_small hbarrier_t
    refine ⟨pc', hcard', ?_⟩
    convert hbarrier' using 2
    push_cast; ring_nf

lemma barrier_parameter_bound
    (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (hn : 4 ≤ n) :
    let k := n / 4
    let u₀ := ε / 2
    let δ := ε / (n : ℝ)
    let u_k := u₀ + (k : ℝ) * δ
    u_k ≤ 3 * ε / 4 ∧ 3 * ε / 4 < ε := by
  constructor
  · show ε / 2 + ↑(n / 4) * (ε / ↑n) ≤ 3 * ε / 4
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have h4_div : 4 * (↑(n / 4) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast show 4 * (n / 4) ≤ n by omega
    have key : (↑(n / 4) : ℝ) * (ε / ↑n) ≤ ε / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ hn_pos (by norm_num : (0:ℝ) < 4)]
      nlinarith
    linarith
  · linarith
end Problem6

end
