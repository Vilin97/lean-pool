/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Stochastic
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Data.ENNReal.Basic

set_option maxHeartbeats 1000000

open Finset Matrix NeuralNetwork State

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype U]
  [Nonempty U]

lemma mul_div_cancel_of_ne_zero {α : Type*} [Field α] (a b : α) (h : b ≠ 0) : a * b / b = a := by
  rw [div_eq_mul_inv]
  rw [propext (mul_inv_eq_iff_eq_mul₀ h)]

lemma sum_univ_eq_tsum_uniform  :
  Summable (fun (_ : U) => (1 : ℝ) / ↑(Fintype.card U)) ∧
  ∑' (_ : U), (1 : ℝ) / ↑(Fintype.card U) = Finset.sum Finset.univ (fun (_ : U) => (1 : ℝ) / ↑(Fintype.card U)) :=
by
  have h_nonzero : (1 : ℝ) / ↑(Fintype.card U) ≠ 0 :=
    by { apply div_ne_zero; norm_num; simp_all only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]}
  have h_support : (Function.support (fun (u : U) => (1 : ℝ) / ↑(Fintype.card U))).Finite := by
    rw [Function.support_const]
    exact Set.finite_univ
    exact h_nonzero
  have h_summable : Summable (fun (u : U) => (1 : ℝ) / ↑(Fintype.card U)) := by
    apply summable_of_finite_support
    · rw [Function.support_const]
      exact Set.finite_univ
      exact h_nonzero
  have h_tsum_eq_sum : ∑' (u : U), (1 : ℝ) / ↑(Fintype.card U) = ∑ (u : U), (1 : ℝ) / ↑(Fintype.card U) := by
    simp_all only [one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
      Function.support_inv, tsum_const, Nat.card_eq_fintype_card, nsmul_eq_mul, mul_inv_cancel₀, sum_const, card_univ]
  exact ⟨h_summable, h_tsum_eq_sum⟩

variable [DecidableEq U] (wθ : Params (HopfieldNetwork R U))

/-- When states differ only at site u, the energy terms that involve pairs of sites other than u are equal --/
lemma energy_terms_without_u_equal (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v1 ∈ univ.erase u, ∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v2 ≠ u}, wθ.w v1 v2 * s'.act v1 * s'.act v2 =
  ∑ v1 ∈ univ.erase u, ∑ v2 ∈ {v2 | v2 ≠ v1 ∧ v2 ≠ u}, wθ.w v1 v2 * s.act v1 * s.act v2 := by
    apply Finset.sum_congr rfl
    intro v1 hv1; rw [Finset.mem_erase] at hv1
    apply Finset.sum_congr rfl
    intro v2 hv2;
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_inter, Finset.mem_compl, and_imp] at hv2
    -- hv2 : v2 ≠ v1 ∧ v2 ≠ u
    have h_v1_ne_u : v1 ≠ u := hv1.1
    have hs'_v1_eq_s_v1 : s'.act v1 = s.act v1 := Eq.symm (h v1 h_v1_ne_u)
    have hs'_v2_eq_s_v2 : s'.act v2 = s.act v2 := Eq.symm (h v2 hv2.2.2)
    rw [hs'_v1_eq_s_v1, hs'_v2_eq_s_v2]

/-- The energy difference for terms involving site u when states differ only at u --/
lemma energy_terms_with_u_diff (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s'.act u * s'.act v2 -
  ∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act u * s.act v2 =
  (s'.act u - s.act u) * (∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2) := by
  have h_eq_acts : ∀ v2, v2 ≠ u → s'.act v2 = s.act v2 := by
    intro v2 hv2_ne_u
    rw [h v2 hv2_ne_u]
  rw [← Finset.sum_sub_distrib]
  have h_term_eq : ∀ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ,
    wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2 =
    (s'.act u - s.act u) * (wθ.w u v2 * s.act v2) := by
    intro v2 hv2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv2
    rw [h_eq_acts v2 hv2]
    ring
  have h_sum_eq : ∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ,
                    (wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2) =
                   ∑ v2 ∈ Finset.filter (fun v2 => v2 ≠ u) univ,
                    (s'.act u - s.act u) * (wθ.w u v2 * s.act v2) := by
    apply Finset.sum_congr rfl
    intro v2 hv2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv2
    have h_act_eq : s'.act v2 = s.act v2 := h_eq_acts v2 hv2
    rw [h_act_eq]
    ring
  rw [h_sum_eq]
  rw [Finset.mul_sum]

lemma weight_energy_diff_term_v1_eq_u (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, (wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2) =
  (s'.act u - s.act u) * ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2 := by
  have h_term_eq : ∀ v2 ∈ filter (fun v2 => v2 ≠ u) univ,
    wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2 =
    (s'.act u - s.act u) * (wθ.w u v2 * s.act v2) := by
    intro v2 hv2
    simp only [mem_filter, mem_univ, true_and] at hv2
    rw [h v2 hv2]
    ring
  have h_sum_eq : ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ,
                  (wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2) =
                  ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ,
                  (s'.act u - s.act u) * (wθ.w u v2 * s.act v2) := by
    apply sum_congr rfl
    intro v2 hv2
    exact h_term_eq v2 hv2
  rw [h_sum_eq]
  rw [mul_sum]

lemma weight_energy_diff_term_v1_ne_u (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑ v1 ∈ filter (fun v1 => v1 ≠ u) univ, ∑ v2 ∈ filter (fun v2 => v2 ≠ v1) univ,
    (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s.act v1 * s.act v2) =
  (s'.act u - s.act u) * ∑ v1 ∈ filter (fun v1 => v1 ≠ u) univ, wθ.w v1 u * s.act v1 := by
  simp_rw [filter_ne']
  have h_transform : ∑ v1 ∈ univ.erase u, ∑ v2 ∈ univ.erase v1,
                     (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s.act v1 * s.act v2) =
                     ∑ v1 ∈ univ.erase u, wθ.w v1 u * s.act v1 * (s'.act u - s.act u) := by
    apply sum_congr rfl
    intro v1 hv1
    simp only [mem_erase, mem_univ] at hv1
    rw [h v1 hv1.1]
    have u_mem_erase_v1 : u ∈ univ.erase v1 := by simp [hv1.1.symm]
    rw [sum_eq_sum_diff_singleton_add u_mem_erase_v1]
    simp only [mem_erase, mem_sdiff, mem_singleton, sdiff_singleton_eq_erase] -- Simplify set notation
    have h_v2_eq_u : wθ.w v1 u * s'.act v1 * s'.act u - wθ.w v1 u * s'.act v1 * s.act u =
                      wθ.w v1 u * s'.act v1 * (s'.act u - s.act u) := by ring
    have h_v2_ne_u : ∑ v2 ∈ (univ.erase v1).erase u,
                        (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s'.act v1 * s.act v2) = 0 := by
        apply sum_eq_zero
        intro v2 hv2
        simp only [mem_erase] at hv2
        rw [h v2 hv2.1]
        ring
    rw [h_v2_eq_u, h_v2_ne_u]
    exact AddZeroClass.zero_add (wθ.w v1 u * s'.act v1 * (s'.act u - s.act u))
  rw [h_transform]
  have h_fun_eq : ∀ v ∈ univ.erase u,
                  wθ.w v u * s.act v * (s'.act u - s.act u) =
                  (s'.act u - s.act u) * (wθ.w v u * s.act v) := by
    intro v hv
    ring
  rw [sum_congr rfl h_fun_eq]
  rw [← mul_sum]

lemma weight_sum_symmetry (s : (HopfieldNetwork R U).State)
  (u : U) (h_symm : ∀ v1 v2 : U, wθ.w v1 v2 = wθ.w v2 v1) :
  ∑ v1 ∈ filter (fun v1 => v1 ≠ u) univ, wθ.w v1 u * s.act v1 =
  ∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2 := by
  simp_rw [filter_ne']
  apply sum_congr rfl
  intro v hv
  simp only [mem_erase] at hv
  rw [h_symm v u]

lemma weight_energy_sum_split (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) (h_symm : ∀ v1 v2 : U, wθ.w v1 v2 = wθ.w v2 v1) :
  ∑ v1 ∈ univ, ∑ v2 ∈ filter (fun v2 => v2 ≠ v1) univ, wθ.w v1 v2 * s'.act v1 * s'.act v2 -
  ∑ v1 ∈ univ, ∑ v2 ∈ filter (fun v2 => v2 ≠ v1) univ, wθ.w v1 v2 * s.act v1 * s.act v2 =
  (s'.act u - s.act u) * (∑ v2 ∈ filter (fun v2 => v2 ≠ u) univ, wθ.w u v2 * s.act v2) * 2 := by
    simp_rw [← sum_sub_distrib]
    have h_u_mem : u ∈ univ := mem_univ u
    rw [sum_eq_sum_diff_singleton_add h_u_mem]
    simp only [singleton_val, sum_singleton, sdiff_singleton_eq_erase]
    have h_term_u : ∑ v2 ∈ univ.erase u,
                    (wθ.w u v2 * s'.act u * s'.act v2 - wθ.w u v2 * s.act u * s.act v2) =
                    (s'.act u - s.act u) * (∑ v2 ∈ univ.erase u, wθ.w u v2 * s.act v2) := by
      rw [← filter_ne']
      apply weight_energy_diff_term_v1_eq_u wθ s s' u h
    have h_sum_not_u : ∑ v1 ∈ univ.erase u, ∑ v2 ∈ univ.erase v1,
                     (wθ.w v1 v2 * s'.act v1 * s'.act v2 - wθ.w v1 v2 * s.act v1 * s.act v2) =
                     (s'.act u - s.act u) * ∑ v1 ∈ univ.erase u, wθ.w v1 u * s.act v1 := by
      have h1 : univ.erase u = filter (fun v1 => v1 ≠ u) univ := by
          exact Eq.symm (filter_erase_equiv u)
      have h2 : ∀ v1, univ.erase v1 = filter (fun v2 => v2 ≠ v1) univ := fun v1 => Eq.symm (@filter_ne' U _ univ v1)
      rw [h1]
      simp_rw [h2]
      apply weight_energy_diff_term_v1_ne_u wθ s s' u h
    have h_filter_erase_u : filter (fun v2 => v2 ≠ u) univ = univ.erase u := by
      apply filter_erase_equiv
    rw [← h_filter_erase_u] at h_term_u
    rw [h_filter_erase_u] at *
    have h_goal_rewrite : ∑ x ∈ univ.erase u,
        ∑ x_1 ∈ filter (fun v2 => v2 ≠ x) univ, (wθ.w x x_1 * s'.act x * s'.act x_1 - wθ.w x x_1 * s.act x * s.act x_1) +
      ∑ x ∈ univ.erase u, (wθ.w u x * s'.act u * s'.act x - wθ.w u x * s.act u * s.act x) =
      ∑ x ∈ univ.erase u,
        ∑ x_1 ∈ univ.erase x, (wθ.w x x_1 * s'.act x * s'.act x_1 - wθ.w x x_1 * s.act x * s.act x_1) +
      ∑ x ∈ univ.erase u, (wθ.w u x * s'.act u * s'.act x - wθ.w u x * s.act u * s.act x) := by
      apply congr_arg₂
      · apply sum_congr rfl
        intro x hx
        rw [@filter_erase_equiv]
      · rfl
    rw [h_goal_rewrite]
    have h_first_term : ∑ x ∈ univ.erase u, (wθ.w u x * s'.act u * s'.act x - wθ.w u x * s.act u * s.act x) =
                        (s'.act u - s.act u) * ∑ v2 ∈ univ.erase u, wθ.w u v2 * s.act v2 := by
      have h_eq : filter (fun v2 => v2 ≠ u) univ = univ.erase u :=  filter_erase_equiv u
      rw [← h_eq] at *
      exact h_term_u
    have h_second_term : ∑ x ∈ univ.erase u, ∑ x_1 ∈ univ.erase x,
                          (wθ.w x x_1 * s'.act x * s'.act x_1 - wθ.w x x_1 * s.act x * s.act x_1) =
                          (s'.act u - s.act u) * ∑ v1 ∈ univ.erase u, wθ.w v1 u * s.act v1 := by
      exact h_sum_not_u
    rw [h_first_term, h_second_term]
    have h_sym : ∑ v1 ∈ univ.erase u, wθ.w v1 u * s.act v1 =
                 ∑ v2 ∈ univ.erase u, wθ.w u v2 * s.act v2 := by
      apply sum_congr rfl
      intro v hv
      simp only [mem_erase] at hv
      rw [h_symm v u]
    rw [h_sym]
    rw [← two_mul]
    ring

/-- For a Hopfield network with states differing at a single site, the activation
    at that site is related to the weighted sum of other activations --/
lemma local_field_relation (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
  s.net wθ u = ∑ v2 ∈ {v2 | v2 ≠ u}, wθ.w u v2 * s.act v2 := by
  simp only [NeuralNetwork.State.net, HopfieldNetwork, NeuralNetwork.fnet, HNfnet,
             NeuralNetwork.State.out, NeuralNetwork.fout, HNfout]

/-- When states differ at a single site, the energy difference in the weight component
    is proportional to the local field and activation difference --/
lemma weight_energy_single_site_diff
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  s'.Ew wθ - s.Ew wθ = (s.act u - s'.act u) * s.net wθ u := by
  unfold NeuralNetwork.State.Ew NeuralNetwork.State.Wact
  rw [← mul_sub]
  have h_dec_eq_R : DecidableEq R := inferInstance
  have h_symm : ∀ v1 v2 : U, wθ.w v1 v2 = wθ.w v2 v1 := by
    exact fun v1 v2 ↦ weight_symmetry wθ v1 v2
  rw [weight_energy_sum_split wθ s s' u h h_symm]
  rw [local_field_relation wθ s u]
  have h_two_ne_zero : (2 : R) ≠ 0 := by norm_num
  dsimp [h_two_ne_zero]
  ring

/-- When states differ at a single site, the energy difference in the bias component
    is proportional to the activation difference --/
lemma bias_energy_single_site_diff
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  s'.Eθ wθ - s.Eθ wθ = θ' (wθ.θ u) * (s'.act u - s.act u) := by
  unfold NeuralNetwork.State.Eθ
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ u)]
  have h_sum_zero : ∑ v ∈ Finset.univ.erase u, (θ' (wθ.θ v) * s'.act v - θ' (wθ.θ v) * s.act v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp only [Finset.mem_erase, Finset.mem_univ, true_and] at hv
    rw [h v hv.1]
    ring
  rw [Finset.sdiff_singleton_eq_erase]
  rw [h_sum_zero, add_zero]
  ring

/-- Energy difference for single-site updates with specified bias term.
    This is a general formulation that allows different bias configurations. --/
lemma energy_single_site_diff_with_bias
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_bias : θ' (wθ.θ u) = 1/2 * s.net wθ u) :
  s'.E wθ - s.E wθ = -1/2 * (s'.act u - s.act u) * s.net wθ u := by
    rw [energy_decomposition, energy_decomposition]
    rw [add_sub_add_comm] -- Rearrange to (s'.Ew - s.Ew) + (s'.Eθ - s.Eθ)
    rw [weight_energy_single_site_diff wθ s s' u h]
    rw [bias_energy_single_site_diff wθ s s' u h]
    rw [h_bias]
    ring_nf

lemma energy_single_site_diff
  (wθ : Params (HopfieldNetwork R U)) (s s' : (HopfieldNetwork R U).State)
  (u : U) (h : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_bias : θ' (wθ.θ u) = 0) : -- Added hypothesis for standard Hopfield case
  s'.E wθ - s.E wθ = -(s'.act u - s.act u) * s.net wθ u := by
  -- Decompose energy into weight and bias components
  rw [energy_decomposition, energy_decomposition]
  rw [add_sub_add_comm]
  rw [weight_energy_single_site_diff wθ s s' u h, bias_energy_single_site_diff wθ s s' u h]
  rw [h_bias]
  ring_nf

lemma single_site_update_eq (s s' : (HopfieldNetwork R U).State) (u : U)
  (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_diff : s.act u ≠ s'.act u) :
  s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) :=
  single_site_difference_as_update s s' u h_diff h_same_elsewhere

@[simp]
lemma ENNReal.natCast_eq_ofReal (n : ℕ) : (n : ENNReal) = ENNReal.ofReal n := by
  induction n with
  | zero =>
    simp [ENNReal.ofReal]
  | succ n ih =>
    rw [Nat.cast_succ]
    rw [Nat.cast_succ]
    rw [ENNReal.ofReal_add]
    · rw [ih]
      rw [ENNReal.ofReal_one]
    · exact Nat.cast_nonneg n
    · norm_num
