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
  [Nonempty U] [DecidableEq U] (wθ : Params (HopfieldNetwork R U)) [Coe R ℝ] (T : ℝ)

/-- In a tsum over all neurons, only the neuron where s and s' differ contributes --/
lemma gibbs_single_site_tsum  (s s' : (HopfieldNetwork R U).State)
  (u : U) (h_diff_at_u : s.act u ≠ s'.act u)
  (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  ∑' (a : U),
    (PMF.ofFintype (fun _ => 1 / ↑(Fintype.card U)) ( uniform_neuron_selection_prob_valid)) a
    * (NN.State.gibbsUpdateSingleNeuron wθ s T a) s' =
  1 / ↑(Fintype.card U) * (NN.State.gibbsUpdateSingleNeuron wθ s T u)
    (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) := by
  have h_s'_as_update : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := by
    apply single_site_difference_as_update s s' u h_diff_at_u h_same_elsewhere
  have h_card_nonzero : (Fintype.card U : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (@Fintype.card_ne_zero U _ ‹Nonempty U›)
  have h_calc : ((Fintype.card U : ℝ)) * (1 / ↑(Fintype.card U)) = 1 := by
    exact mul_one_div_cancel h_card_nonzero
  have h_s'_as_update : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := by
    apply single_site_difference_as_update s s' u h_diff_at_u h_same_elsewhere

  have h_tsum_to_sum : ∑' (a : U), (PMF.ofFintype (fun x => 1 / ↑(Fintype.card U)) (uniform_neuron_selection_prob_valid)) a *
                      (NN.State.gibbsUpdateSingleNeuron wθ s T a) s' =
                      ∑ a ∈ Finset.univ, (PMF.ofFintype (fun x => 1 / ↑(Fintype.card U)) (uniform_neuron_selection_prob_valid)) a *
                      (NN.State.gibbsUpdateSingleNeuron wθ s T a) s' := by
    apply tsum_eq_sum
    · intro a ha
      simp only [Finset.mem_univ] at ha
      contradiction
  rw [h_tsum_to_sum]
  rw [h_s'_as_update]
  have h_zero_other_sites : ∀ a ∈ Finset.univ, a ≠ u →
                           (NN.State.gibbsUpdateSingleNeuron wθ s T a) s' = 0 := by
    intro a _ ha
    exact gibbs_update_zero_other_sites wθ T s s' u a h_same_elsewhere h_diff_at_u ha
  rw [Finset.sum_eq_single u]
  · simp only [uniform_neuron_selection_prob]
    have h_update_eq : (NN.State.gibbsUpdateSingleNeuron wθ s T u) s' =
                      (NN.State.gibbsUpdateSingleNeuron wθ s T u)
                      (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) := by
      rw [h_s'_as_update]
      congr
    congr
  · intro a h_in h_ne
    have h_eq : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := h_s'_as_update
    rw [h_eq] at h_zero_other_sites
    exact mul_eq_zero_of_right _ (h_zero_other_sites a h_in h_ne)
  · intro h_not_in
    absurd (Finset.mem_univ u)
    exact h_not_in


  /-- Main lemma for Gibbs transition probability with single site update :
    For a state transition involving change at exactly one site u, the Gibbs transition
    probability is the product of the probability of selecting u and the probability
    of updating u to the new value --/--/
lemma gibbs_single_site_transition_prob (s s' : (HopfieldNetwork R U).State)
  (u : U) (h_diff_at_u : s.act u ≠ s'.act u)
  (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v) :
  gibbsTransitionProb wθ T s s' =
  ENNReal.toReal (((1 : ENNReal) / (Fintype.card U : ENNReal)) *
  (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u (s'.act u) (s'.hp u))) := by
  have h_eq := gibbs_single_site_tsum wθ T s s' u h_diff_at_u h_same_elsewhere
  have h_rewrite : ∑' (a : U), (PMF.ofFintype (fun x => 1 / ↑(Fintype.card U))
    ( uniform_neuron_selection_prob_valid)) a *
                      (NN.State.gibbsUpdateSingleNeuron wθ s T a) s' =
                      1 / ↑(Fintype.card U) * (NN.State.gibbsUpdateSingleNeuron wθ s T u)
                      (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) := h_eq
  exact
    Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (congrArg ENNReal.toReal (id (Eq.symm h_eq)))))

lemma gibbs_transition_sum_single_site
  (wθ : Params (HopfieldNetwork R U)) (T : ℝ) (s s' : (HopfieldNetwork R U).State) [Coe R ℝ]
  (u : U) (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (h_diff : s.act u ≠ s'.act u) :
  ∑' (a : U), ((1 : ENNReal) / (Fintype.card U : ENNReal)) * -- Use ENNReal probability
    (NN.State.gibbsUpdateSingleNeuron wθ s T a) s' =
  ((1 : ENNReal) / (Fintype.card U : ENNReal)) * (NN.State.gibbsUpdateSingleNeuron wθ s T u) s' := by
  have h_tsum := gibbs_single_site_tsum wθ T s s' u h_diff h_same_elsewhere
  have h_update : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) :=
    single_site_difference_as_update s s' u h_diff h_same_elsewhere
  rw [← h_update] at h_tsum
  exact h_tsum

lemma gibbs_update_single_neuron_formula (s : (HopfieldNetwork R U).State)
  (u : U) (val : R) (hval : (HopfieldNetwork R U).pact val) :
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
  (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u val hval) =
    if val = 1 then ENNReal.ofReal (Real.exp (local_field / T)) / Z
    else ENNReal.ofReal (Real.exp (-local_field / T)) / Z :=
  gibbs_update_single_neuron_prob wθ s T u val hval

lemma gibbs_single_site_transition_explicit
  (s s' : (HopfieldNetwork R U).State) [Coe R ℝ]
  (u : U) (h_same_elsewhere : ∀ v : U, v ≠ u → s.act v = s'.act v)
  (_ : θ' (wθ.θ u) = 0) (_ : T > 0) (h_neq : s ≠ s') :
  gibbsTransitionProb wθ T s s' =
    (1 / (Fintype.card U : ℝ)) * ENNReal.toReal (
      let local_field := s.net wθ u
      let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
      if s'.act u = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z
    ) :=
by
  have h_diff : s.act u ≠ s'.act u := by
    intro contra; exact h_neq (NeuralNetwork.ext (fun v => if hv : v = u then by rw [hv]; exact contra else h_same_elsewhere v hv))
  have h_prob := gibbs_single_site_transition_prob wθ T s s' u h_diff h_same_elsewhere
  rw [h_prob]
  have h_upd := single_site_difference_as_update s s' u h_diff h_same_elsewhere
  let local_field := s.net wθ u
  let Z := ENNReal.ofReal (Real.exp (local_field / T)) + ENNReal.ofReal (Real.exp (-local_field / T))
  have h_formula : (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) =
      if s'.act u = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by
    apply gibbs_update_single_neuron_formula
  have h_update_act : (NN.State.updateNeuron s u (s'.act u) (s'.hp u)).act u = s'.act u := by
    exact congrFun (congrArg act (id (Eq.symm h_upd))) u
  have h_goal : gibbsTransitionProb wθ T s s' =
    (1 / (Fintype.card U : ℝ)) * ENNReal.toReal (
      if s'.act u = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z
    ) := by
    rw [h_prob]
    have h_eq : s' = NN.State.updateNeuron s u (s'.act u) (s'.hp u) := h_upd
    rw [h_eq] at h_formula ⊢
    rw [h_formula]
    rw [h_update_act]
    have h_real_div_pos : ∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b),
                          ENNReal.toReal (ENNReal.ofReal a / ENNReal.ofReal b) = a / b := by
      intros a b ha hb
      rw [ENNReal.toReal_div]
      · rw [ENNReal.toReal_ofReal ha.le, ENNReal.toReal_ofReal hb.le]
    have h_exp_pos : ∀ x : ℝ, 0 < Real.exp x := fun x => Real.exp_pos x
    have h_card_div : ENNReal.toReal ((1 : ENNReal) / (Fintype.card U : ENNReal)) = 1 / (Fintype.card U : ℝ) := by
      apply ENNReal.toReal_div
    rw [← h_card_div]
    rw [ENNReal.toReal_mul]
  have h_card_pos : 0 < (Fintype.card U : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hZ_ne_top : Z ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hZ_pos : Z > 0 := by
    have h_exp1_pos : Real.exp (local_field / T) > 0 := Real.exp_pos _
    have h_exp2_pos : Real.exp (-local_field / T) > 0 := Real.exp_pos _
    have h1 : ENNReal.ofReal (Real.exp (local_field / T)) > 0 := ENNReal.ofReal_pos.mpr h_exp1_pos
    have h2 : ENNReal.ofReal (Real.exp (-local_field / T)) > 0 := ENNReal.ofReal_pos.mpr h_exp2_pos
    exact Right.add_pos' h1 h2
  have h_toReal_div_ENNReal : ∀ (a b : ENNReal) (ha : a ≠ ⊤) (hb : b ≠ 0) (hb_top : b ≠ ⊤),
      ENNReal.toReal (a / b) = ENNReal.toReal a / ENNReal.toReal b := by
    intros a b ha hb hb_top
    exact ENNReal.toReal_div a b
  have h_formula_direct : (NN.State.gibbsUpdateSingleNeuron wθ s T u) s' =
      if s'.act u = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by
    rw [h_upd]
    have h_update_eq : (NN.State.updateNeuron s u (s'.act u) (s'.hp u)).act u = s'.act u := by
      simp only [NN.State.updateNeuron, act]; exact rfl
    have h_formula_raw := gibbs_update_single_neuron_formula wθ T s u (s'.act u) (s'.hp u)
    have h_formula_rewritten : (NN.State.gibbsUpdateSingleNeuron wθ s T u) (NN.State.updateNeuron s u (s'.act u) (s'.hp u)) =
      if (NN.State.updateNeuron s u (s'.act u) (s'.hp u)).act u = 1 then
        ENNReal.ofReal (Real.exp (local_field / T)) / Z
      else
        ENNReal.ofReal (Real.exp (-local_field / T)) / Z := by
      rw [h_formula_raw]
      congr
    have h_cond_eq : (NN.State.updateNeuron s u (s'.act u) (s'.hp u)).act u = 1 ↔ s'.act u = 1 := by
      rw [h_update_eq]
    exact h_formula_rewritten
  have h_final : (1 / ↑(Fintype.card U) * (NN.State.gibbsUpdateSingleNeuron wθ s T u)
    (NN.State.updateNeuron s u (s'.act u) (s'.hp u))).toReal =
                 1 / ↑(Fintype.card U) * ENNReal.toReal (
                   if s'.act u = 1 then ENNReal.ofReal (Real.exp (local_field / T)) / Z
                   else ENNReal.ofReal (Real.exp (-local_field / T)) / Z
                 ) := by
    have h_card_nonzero : (Fintype.card U : ℝ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (@Fintype.card_ne_zero U _ ‹Nonempty U›)
    have h_card_finite : (Fintype.card U : ENNReal) ≠ ⊤ :=
      ENNReal.natCast_ne_top (Fintype.card U)
    have h_one_div_card : (1 / (Fintype.card U : ENNReal)).toReal = 1 / (Fintype.card U : ℝ) := by
      rw [ENNReal.toReal_div]
      · rw [ENNReal.toReal_one]
        exact rfl
    rw [ENNReal.toReal_mul]
    congr 1
    · exact congrArg ENNReal.toReal h_formula
  trans (1 / ↑(Fintype.card U) * (NN.State.gibbsUpdateSingleNeuron wθ s T u)
    (NN.State.updateNeuron s u (s'.act u) (s'.hp u))).toReal
  · exact rfl
  · exact h_final

/-- Multi-site transitions have zero probability --/
lemma gibbsUpdateSingleNeuron_support
  (s s' : (HopfieldNetwork R U).State) (u : U) :
  s' ∈ (NN.State.gibbsUpdateSingleNeuron wθ s T u).support →
  s' = NN.State.updateNeuron s u 1 (Or.inl rfl) ∨
  s' = NN.State.updateNeuron s u (-1) (Or.inr rfl) := by
  intro h_mem_support
  rw [PMF.mem_support_iff] at h_mem_support
  have h_pos : (NN.State.gibbsUpdateSingleNeuron wθ s T u) s' > 0 := by
    exact (PMF.apply_pos_iff (NN.State.gibbsUpdateSingleNeuron wθ s T u) s').mpr h_mem_support
  exact gibbsUpdate_possible_states wθ s T u s' h_pos

lemma gibbsUpdateSingleNeuron_prob_zero_if_not_update [Coe R ℝ] (T : ℝ)
  (s s' : (HopfieldNetwork R U).State) (u : U) :
  ¬(s' = NN.State.updateNeuron s u 1 (Or.inl rfl) ∨
    s' = NN.State.updateNeuron s u (-1) (Or.inr rfl)) →
  (NN.State.gibbsUpdateSingleNeuron wθ s T u) s' = 0 := by
  intro h_not_update
  -- Use the contrapositive of the support lemma
  rw [PMF.apply_eq_zero_iff]
  contrapose! h_not_update -- This assumes s' is in the support
  exact gibbsUpdateSingleNeuron_support wθ T s u s' h_not_update

lemma gibbsSamplingStep_prob_zero_if_multi_site (s s' : (HopfieldNetwork R U).State) :
  (¬∃ u : U, ∀ v : U, v ≠ u → s.act v = s'.act v) →
  (NN.State.gibbsSamplingStep wθ s T) s' = 0 := by
  intro h_multi_site
  unfold NN.State.gibbsSamplingStep
  simp only [PMF.bind_apply] -- Use the definition of PMF.bind
  rw [ENNReal.tsum_eq_zero]
  intro u -- Consider an arbitrary neuron u
  have h_s'_not_update_at_u : ¬(s' = NN.State.updateNeuron s u 1 ( Or.inl rfl) ∨
                                s' = NN.State.updateNeuron s u (-1) ( Or.inr rfl)) := by
    intro h_update_or
    apply h_multi_site
    cases h_update_or with
    | inl h_eq_update_one =>
      exists u
      intro v hv
      rw [h_eq_update_one]
      exact Eq.symm (updateNeuron_preserves s u v 1 (Or.inl rfl) hv)
    | inr h_eq_update_neg_one =>
      exists u
      intro v hv
      rw [h_eq_update_neg_one]
      exact Eq.symm (updateNeuron_preserves s u v (-1) (Or.inr rfl) hv)
  have h_update_prob_zero : (NN.State.gibbsUpdateSingleNeuron wθ s T u) s' = 0 :=
    gibbsUpdateSingleNeuron_prob_zero_if_not_update T s wθ u s' h_s'_not_update_at_u
  exact mul_eq_zero_of_right _ h_update_prob_zero

-- Main lemma
lemma gibbs_multi_site_transition (s s' : (HopfieldNetwork R U).State) :
  (¬∃ u : U, ∀ v : U, v ≠ u → s.act v = s'.act v) →
  gibbsTransitionProb wθ T s s' = 0 := by
  intro h_multi_site
  unfold gibbsTransitionProb
  have h_step_prob_zero : (NN.State.gibbsSamplingStep wθ T s) s' = 0 :=
    gibbsSamplingStep_prob_zero_if_multi_site T wθ s s' h_multi_site
  rw [h_step_prob_zero]
  exact rfl
