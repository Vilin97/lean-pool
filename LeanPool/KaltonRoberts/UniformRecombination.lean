/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# One-sided recombination: finite-uniform core theorem

This file proves the finite-uniform version of Lemma 3.2 from the paper,
which takes a finite uniform family of source sets indexed by a finite type `I`
and produces a target `WeightedCollection` via expander recombination.

**Reference**: Lemma 3.2 in Section 3 of the companion paper.
-/
import LeanPool.KaltonRoberts.Defs
import LeanPool.KaltonRoberts.Collections
import LeanPool.KaltonRoberts.Recombination

/-!
# Finite-uniform recombination

Finite-uniform version of the one-sided recombination theorem, producing a
target weighted collection via expander recombination.
-/

namespace KaltonRoberts

open Finset BigOperators

noncomputable section

variable {U : Type*} [DecidableEq U] [Fintype U]

/-! ## Uniform labeling helpers -/

/-- For `m ∣ n` with `0 < n` and `0 < m`, the function `i ↦ i % m` maps
`Fin n` to `Fin m` with each fiber having exactly `n / m` elements. -/
theorem exists_uniform_labeling (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hdvd : m ∣ n) :
    ∃ f : Fin n → Fin m,
      Function.Surjective f ∧
      ∀ j : Fin m, (Finset.univ.filter (fun i => f i = j)).card = n / m := by
  refine ⟨fun i => ⟨i.val % m, Nat.mod_lt _ hm⟩, ?_, ?_⟩
  · intro j
    exact ⟨⟨j, by linarith [Fin.is_lt j, Nat.le_of_dvd hn hdvd]⟩,
      Fin.ext <| Nat.mod_eq_of_lt j.2⟩
  · intro j
    rw [Finset.card_eq_of_bijective]
    · use fun i hi => ⟨i * m + j,
        by nlinarith [Nat.div_mul_cancel hdvd, Fin.is_lt j]⟩
    · simp +decide only [mem_filter, mem_univ, true_and]
      exact fun a ha => ⟨a / m,
        Nat.div_lt_of_lt_mul <| by nlinarith [Fin.is_lt a, Nat.div_mul_cancel hdvd],
        by
          apply Fin.ext
          have hmod : a.val % m = j.val := congrArg Fin.val ha
          nlinarith [Nat.mod_add_div a.val m, hmod]⟩
    · simp +decide [Fin.ext_iff, Nat.add_mod, Nat.mod_eq_of_lt j.2]
    · aesop

/-
Uniform labeling for abstract finite types: if `card B ∣ card A` and
both are positive, there exists a surjection `A → B` with uniform fibers.
-/
theorem exists_uniform_labeling_types
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (hdvd : Fintype.card B ∣ Fintype.card A) :
    ∃ f : A → B, Function.Surjective f ∧
      ∀ j : B, (Finset.univ.filter (fun i => f i = j)).card =
        Fintype.card A / Fintype.card B := by
  classical
  obtain ⟨f, hf⟩ := exists_uniform_labeling (Fintype.card A) (Fintype.card B) hA hB hdvd;
  -- Compose the function f with the equivalence between Fin (Fintype.card A) and A, and between Fin
  -- (Fintype.card B) and B.
  have h_equiv : Nonempty (A ≃ Fin (Fintype.card A)) ∧ Nonempty (B ≃ Fin (Fintype.card B)) := by
    exact ⟨ ⟨ Fintype.equivFin A ⟩, ⟨ Fintype.equivFin B ⟩ ⟩;
  obtain ⟨ ⟨ eA ⟩, ⟨ eB ⟩ ⟩ := h_equiv;
  refine ⟨ fun a => eB.symm ( f ( eA a ) ), ?_, ?_ ⟩
  · exact fun b => by obtain ⟨ a, ha ⟩ := hf.1 ( eB b ); exact ⟨ eA.symm a, by simp +decide [ ha ]
    ⟩;
  · intro j
    convert hf.2 ( eB j ) using 1;
    rw [ Finset.card_filter, Finset.card_filter ];
    refine Finset.sum_bij (fun i _ => eA i) ?_ ?_ ?_ ?_
    · simp_all
    · simp_all
    · intro b hb
      exact ⟨eA.symm b, Finset.mem_univ _, by simp⟩
    · intro i hi
      simp [eB.symm_apply_eq]

/-! ## Cofinality of admissible multiples -/

/-- For any positive integers `step` and `d`, there exist arbitrarily large
multiples of `step` such that `d ∣ 2 * k`. -/
theorem exists_large_admissible_multiple (step d : ℕ) (hstep : 0 < step) (hd : 0 < d) :
    ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ step ∣ k ∧ d ∣ 2 * k := by
  exact fun N => ⟨ step * d * ( N + 1 ),
    by nlinarith [ mul_pos hstep hd ],
    dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _,
    dvd_mul_of_dvd_right ( dvd_mul_of_dvd_left ( dvd_mul_left _ _ ) _ ) _ ⟩

/-! ## Duplication lemmas -/

/-
Source count after uniform duplication via an arbitrary labeling.
-/
omit [Fintype U] in
lemma uniform_duplication_source_count'
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (lab : A → B)
    (hfiber : ∀ j : B, (Finset.univ.filter (fun i => lab i = j)).card =
      Fintype.card A / Fintype.card B)
    (C : B → Finset U) (i : U) :
    (Finset.univ.filter (fun v : A => i ∈ C (lab v))).card =
      (Finset.univ.filter (fun j : B => i ∈ C j)).card *
        (Fintype.card A / Fintype.card B) := by
  classical
  have h_source_count : (Finset.univ.filter (fun v : A => i ∈ C (lab v))).card = ∑ j ∈
    Finset.univ.filter (fun j : B => i ∈ C j), (Finset.univ.filter (fun v : A => lab v = j)).card :=
      by
    simp +decide only [card_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ]; aesop;
  aesop

/-
Sum after uniform duplication via an arbitrary labeling.
-/
lemma uniform_duplication_sum
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (lab : A → B)
    (hfiber : ∀ j : B, (Finset.univ.filter (fun i => lab i = j)).card =
      Fintype.card A / Fintype.card B)
    (g : B → ℝ) :
    ∑ v : A, g (lab v) =
      (Fintype.card A / Fintype.card B : ℕ) * ∑ j : B, g j := by
  classical
  -- Apply the lemma that rewrites the sum as a sum over the fibers.
  have h_sum_fiber : ∑ v : A, g (lab v) = ∑ j : B, ∑ v ∈ Finset.univ.filter (fun v => lab v = j), g
    j := by
    exact Eq.symm (sum_fiberwise' univ lab g)
  rw [h_sum_fiber]
  simp +decide only [hfiber, Finset.sum_const, nsmul_eq_mul]
  rw [ Finset.mul_sum _ _ _ ]

/-! ## Ratio lemma -/

/-
If `(card W : ℚ) = 2 * θ * k` and `card V = 2 * k` and `k > 0`,
then `(card W : ℝ) / (card V : ℝ) = θ`.
-/
lemma expander_ratio_eq_theta
    {V W : Type*} [Fintype V] [Fintype W]
    {θ : ℚ} {k : ℕ} (hk : 0 < k)
    (hV : Fintype.card V = 2 * k)
    (hW : (Fintype.card W : ℚ) = 2 * θ * ↑k) :
    (Fintype.card W : ℝ) / (Fintype.card V : ℝ) = (θ : ℝ) := by
  rw [ div_eq_iff ] <;> norm_cast at * <;> simp_all +decide [ mul_comm, mul_left_comm ];
  linarith

/-! ## Finite-uniform one-sided recombination -/

omit [Fintype U] in
/-
**Lemma 3.2** (One-sided recombination, finite-uniform version).
-/
theorem one_sided_recombination_uniform_core
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) (M : ℝ)
    (hM : ∀ S : Finset U, |f S| ≤ M)
    (α_val : ℚ) (r_val : ℕ) (θ_val : ℚ)
    (hθ : 0 < (θ_val : ℝ)) (_hθ1 : (θ_val : ℝ) < 1)
    (hexp : StrongExpandersExist α_val r_val θ_val)
    (hr : 0 < r_val)
    {I : Type*} [Fintype I]
    (hI : 0 < Fintype.card I)
    (C : I → Finset U)
    (hfreq : ∀ i : U, ((Finset.univ.filter (fun j => i ∈ C j)).card : ℝ) /
      (Fintype.card I : ℝ) ≤ (α_val : ℝ))
    (D : ℝ) (hD : 0 ≤ D)
    (havg_def : (∑ j : I, deficit f M (C j)) / (Fintype.card I : ℝ) ≤ D) :
    ∃ (C' : WeightedCollection U) (D' : ℝ), 0 ≤ D' ∧
      (∀ i : U, C'.itemFreq i ≤ (α_val : ℝ) / (θ_val : ℝ)) ∧
      C'.avgDeficit f M ≤ D' ∧
      (1 - (θ_val : ℝ)) * M ≤ D - (θ_val : ℝ) * D' + 2 * (r_val : ℝ) - 1 - (θ_val : ℝ) := by
  classical
  -- Step 1: Extract step and eventually-property from StrongExpandersExist
  obtain ⟨step, hstep_pos, hev⟩ := hexp
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  -- Step 2: Choose k large, admissible, with card I | 2k
  obtain ⟨k, hk_large, hk_step, hk_dvd⟩ :=
    exists_large_admissible_multiple step (Fintype.card I) hstep_pos hI N₀
  -- Step 3: Get the expander witness
  obtain ⟨E, hV_card, hW_card, hthresh⟩ := hN₀ k hk_large hk_step
  -- k > 0
  have hk_pos : 0 < k := by
    by_contra h; push Not at h
    have : @Fintype.card E.V E.instFintypeV = 0 := by omega
    linarith [E.hV_pos]
  -- Step 4: Construct uniform labeling E.V → I
  have hI_dvd_V : Fintype.card I ∣ @Fintype.card E.V E.instFintypeV := by
    rw [hV_card]; exact hk_dvd
  obtain ⟨lab, _hlab_surj, hlab_fiber⟩ :=
    exists_uniform_labeling_types (A := E.V) (B := I) E.hV_pos hI hI_dvd_V
  -- Step 5: Define duplicated source family
  let C' : E.V → Finset U := fun v => C (lab v)
  -- Step 6: Source count relation
  have hsource_count : ∀ i : U,
      (Finset.univ.filter (fun v : E.V => i ∈ C (lab v))).card =
      (Finset.univ.filter (fun j : I => i ∈ C j)).card *
        (@Fintype.card E.V E.instFintypeV / Fintype.card I) :=
    fun i => uniform_duplication_source_count' lab hlab_fiber C i
  -- Step 7: Frequency condition: source count ≤ threshold
  have hfreq_C' : ∀ i : U,
      (Finset.univ.filter (fun v : E.V => i ∈ C' v)).card ≤ E.expansionThreshold := by
    intro i
    specialize hfreq i
    have hsource_count_i : (Finset.univ.filter (fun v => i ∈ C (lab v))).card ≤ (α_val *
      (Fintype.card E.V : ℚ)) := by
      rw [ div_le_iff₀ ] at hfreq <;> norm_cast at *;
      have hq_cast : ((Fintype.card E.V / Fintype.card I : ℕ) : ℚ) =
          (Fintype.card E.V : ℚ) / Fintype.card I := by
        rw [Nat.cast_div hI_dvd_V (by positivity)]
      calc
        (#{v | i ∈ C (lab v)} : ℚ) =
            (#{j | i ∈ C j} : ℚ) *
              ((Fintype.card E.V / Fintype.card I : ℕ) : ℚ) := by
          simp_all
        _ ≤ (α_val * (Fintype.card I : ℚ)) *
              ((Fintype.card E.V / Fintype.card I : ℕ) : ℚ) := by
          exact mul_le_mul_of_nonneg_right hfreq (Nat.cast_nonneg _)
        _ = α_val * (Fintype.card E.V : ℚ) := by
          rw [hq_cast]
          field_simp [show (Fintype.card I : ℚ) ≠ 0 by positivity]
    exact Nat.le_of_lt_succ (by
      rw [← @Nat.cast_lt ℚ]
      push_cast [hthresh, hV_card] at *
      linarith [Nat.le_ceil (2 * α_val * k)])
  -- Step 8: Average deficit condition
  have havg_def_C' :
      (∑ v : E.V, deficit f M (C' v)) /
        (@Fintype.card E.V E.instFintypeV : ℝ) ≤ D := by
    -- Use uniform_duplication_sum lab hlab_fiber (fun j => deficit f M (C j)) to rewrite:
    have hsum_rewrite : ∑ v : E.V, deficit f M (C' v) = (Fintype.card E.V / Fintype.card I : ℕ) * ∑
      j : I, deficit f M (C j) := by
      convert uniform_duplication_sum lab hlab_fiber ( fun j => deficit f M ( C j ) ) using 1;
    rw [ hsum_rewrite, div_le_iff₀ ] at *;
    · convert mul_le_mul_of_nonneg_left havg_def ( Nat.cast_nonneg ( Fintype.card E.V / Fintype.card
      I ) ) using 1; ring_nf;
      rw [mul_assoc, Nat.cast_div (by tauto) (by positivity),
        div_mul_cancel₀ _ (by positivity)];
    · positivity;
    · exact Nat.cast_pos.mpr ( hV_card.symm ▸ mul_pos zero_lt_two hk_pos )
  -- Step 9: Positivity of card W
  have hW_pos : 0 < @Fintype.card E.W E.instFintypeW := by
    by_contra h; push Not at h
    have hW_zero : @Fintype.card E.W E.instFintypeW = 0 := by omega
    have : (0 : ℚ) = 2 * θ_val * k := by
      rw [← hW_card]; simp [hW_zero]
    have : (θ_val : ℝ) * k = 0 := by
      have := congr_arg (Rat.cast : ℚ → ℝ) this; push_cast at this; linarith
    cases mul_eq_zero.mp this with
    | inl h => linarith
    | inr h => have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); contradiction
  -- Step 10: Apply witness-level theorem
  have hV_pos_real : (0 : ℝ) < (@Fintype.card E.V E.instFintypeV : ℝ) :=
    Nat.cast_pos.mpr E.hV_pos
  have hW_pos_real : (0 : ℝ) < (@Fintype.card E.W E.instFintypeW : ℝ) :=
    Nat.cast_pos.mpr hW_pos
  obtain ⟨T, D', hD'_nn, hT_source, _hT_thresh, hT_def, hT_ineq⟩ :=
    one_sided_recombination_witness_core
      (V := E.V) (W := E.W) hr E.edge E.right_coverage
      E.expansionThreshold E.expansion
      f hf M hM C' hfreq_C' D hD havg_def_C' hV_pos_real hW_pos_real
  -- Step 11: The ratio card W / card V = θ
  have hratio : (@Fintype.card E.W E.instFintypeW : ℝ) /
      (@Fintype.card E.V E.instFintypeV : ℝ) = (θ_val : ℝ) :=
    expander_ratio_eq_theta hk_pos hV_card hW_card
  -- Step 12: Package T as WeightedCollection
  -- Use ULift to handle universe mismatch: E.W is Type 0 but WeightedCollection needs Type u
  let T_lifted : ULift E.W → Finset U := fun ⟨w⟩ => T w
  have hW_pos_lifted : 0 < Fintype.card (ULift E.W) := by
    rw [Fintype.card_ulift]; exact hW_pos
  set C'_out := WeightedCollection.uniformOfFamily T_lifted hW_pos_lifted with hC'_out_def
  refine ⟨C'_out, D', hD'_nn, ?_, ?_, ?_⟩
  · -- Target frequency ≤ α/θ
    intro i
    have hitemFreq : C'_out.itemFreq i = (Finset.univ.filter (fun w => i ∈ T w)).card /
      (Fintype.card E.W : ℝ) := by
      convert WeightedCollection.uniformOfFamily_itemFreq T_lifted hW_pos_lifted i using 1;
      rw [ Fintype.card_congr ( Equiv.ulift.symm ) ];
      congr! 2;
      refine Finset.card_bij (fun w hw => ⟨w⟩) ?_ ?_ ?_
      · intro w hw
        simpa [T_lifted] using hw
      · simp_all
      · intro w hw
        exact ⟨w.down, by simpa [T_lifted] using hw, by cases w; rfl⟩
    rw [ hitemFreq, div_le_div_iff₀ ] <;> norm_cast at *;
    refine le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr ( hT_source i ) ) ( by
      positivity ) ) ?_
    convert mul_le_mul_of_nonneg_right ( hfreq i ) ( show ( 0 : ℚ ) ≤ Fintype.card E.W by positivity
      ) using 1; ring_nf;
    rw [ hsource_count i ]; norm_num [ Finset.dens ]; ring_nf;
    rw [ Nat.cast_div ( by assumption ) ( by positivity ) ]; ring_nf;
    rw [ show ( Fintype.card E.W : ℚ ) = 2 * θ_val * k by exact_mod_cast hW_card ]
    rw [ hV_card ]
    ring_nf
    push_cast; ring;
  · -- Target average deficit ≤ D'
    rw [WeightedCollection.uniformOfFamily_avgDeficit]
    -- Need: (∑ j : ULift E.W, deficit f M (T_lifted j)) / card (ULift E.W) ≤ D'
    -- = (∑ w : E.W, deficit f M (T w)) / card E.W ≤ D'
    convert hT_def using 1
    rw [Fintype.card_ulift]
    congr 1
    exact Fintype.sum_equiv (Equiv.ulift) _ _ (fun ⟨w⟩ => rfl)
  · -- Recombination inequality
    simp_all

end

end KaltonRoberts
