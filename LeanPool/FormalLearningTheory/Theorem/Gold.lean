/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Criterion.Gold
import LeanPool.FormalLearningTheory.Complexity.MindChange

/-!
# Gold's Theorem and Mind Change Characterization

The foundational results of inductive inference theory.
-/

universe u v

/-- Gold's theorem (1967): No learner can EX-identify any concept class
    containing all finite subsets plus some infinite set, from text. -/
theorem gold_theorem (X : Type u) [Countable X] [DecidableEq X]
    (C : ConceptClass X Bool)
    (h_finite : ∀ (S : Finset X), (fun x => decide (x ∈ S)) ∈ C)
    (h_infinite : ∃ c ∈ C, Set.Infinite { x | c x = true }) :
    ¬ EXLearnable X C := by
  intro ⟨L, hL⟩
  obtain ⟨c_inf, hc_inf_mem, hc_inf_inf⟩ := h_infinite
  -- === INFRASTRUCTURE ===
  let φ := hc_inf_inf.natEmbedding
  have hpos_ne : Nonempty ↥{x : X | c_inf x = true} := hc_inf_inf.nonempty.to_subtype
  obtain ⟨enum, henum⟩ := exists_surjective_nat (↥{x : X | c_inf x = true})
  let S : ℕ → Finset X := fun n =>
    ((Finset.range (n + 1)).image (fun i => (φ i).val)) ∪
    ((Finset.range (n + 1)).image (fun i => (enum i).val))
  have hS_pos : ∀ n x, x ∈ S n → c_inf x = true := by
    intro n x hx
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
    rcases hx with ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩
    · exact (φ i).prop
    · exact (enum i).prop
  have hS_ne : ∀ n, (fun x => decide (x ∈ S n)) ≠ c_inf := by
    intro n heq; apply hc_inf_inf
    suffices {x : X | c_inf x = true} ⊆ ↑(S n) from (S n).finite_toSet.subset this
    intro x (hx : c_inf x = true)
    simpa [hx] using congr_fun heq x
  have hS_ne' : ∀ n, (S n).Nonempty :=
    fun n => ⟨(φ 0).val, Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
      ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n), rfl⟩))⟩
  have hS_mono : ∀ n, S n ⊆ S (n + 1) := by
    intro n x hx
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx ⊢
    rcases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact Or.inl ⟨i, by omega, rfl⟩
    · exact Or.inr ⟨i, by omega, rfl⟩
  have hS_exh : ∀ x, c_inf x = true → ∃ n, x ∈ S n := by
    intro x hx; obtain ⟨n, hn⟩ := henum ⟨x, hx⟩
    exact ⟨n, Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨n, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl), congr_arg Subtype.val hn⟩))⟩
  -- === CONV_EXT: Lock learner onto finite concept ===
  have conv_ext : ∀ (m : ℕ) (σ : List (X × Bool))
      (hσ_pos : ∀ p ∈ σ, p.2 = true) (hσ_in : ∀ p ∈ σ, p.1 ∈ S m),
      ∃ (σ' : List (X × Bool)),
        σ.length < σ'.length ∧
        (∀ p ∈ σ', p.2 = true) ∧
        (∀ p ∈ σ', p.1 ∈ S m) ∧
        (∀ x ∈ S m, ∃ p ∈ σ', p.1 = x) ∧
        (∀ (i : ℕ) (hi : i < σ.length) (hi' : i < σ'.length),
          σ'[i] = σ[i]) ∧
        L.conjecture σ' = fun x => decide (x ∈ S m) := by
    intro m σ hσ_pos hσ_in
    have hcard : 0 < (S m).card := Finset.card_pos.mpr (hS_ne' m)
    let obs : ℕ → X × Bool := fun t =>
      if h : t < σ.length then σ[t]
      else ((S m).toList[(t - σ.length) % (S m).card]'(by
        rw [Finset.length_toList]; exact Nat.mod_lt _ hcard), true)
    have hobs_pos : ∀ t, (obs t).2 = true := by
      intro t; simp only [obs]; split
      · next h => exact hσ_pos _ (σ.getElem_mem h)
      · rfl
    have hobs_correct : ∀ t, (fun x => decide (x ∈ S m)) (obs t).1 = true := by
      intro t; simp only [obs]; split
      · next h => simp [hσ_in _ (σ.getElem_mem h)]
      · simp [Finset.mem_toList.mp (List.getElem_mem _)]
    have hobs_exh : ∀ x, (fun x => decide (x ∈ S m)) x = true → ∃ t, (obs t).1 = x := by
      intro x hx
      have hx_mem : x ∈ S m := of_decide_eq_true hx
      obtain ⟨⟨idx, hidx⟩, heq⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hx_mem)
      refine ⟨σ.length + idx, ?_⟩
      simp only [obs, show ¬ (σ.length + idx < σ.length) by omega, ↓reduceDIte]
      have hidx' : idx < (S m).card := by rw [← Finset.length_toList]; exact hidx
      conv_lhs => simp only [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt hidx']
      exact heq
    let T : TextPresentation X (fun x => decide (x ∈ S m)) :=
      ⟨⟨obs⟩, hobs_pos, hobs_correct, hobs_exh⟩
    obtain ⟨t₀, ht₀⟩ := hL _ (h_finite (S m)) T
    let t := max t₀ (σ.length + (S m).card)
    refine ⟨dataUpTo T.toDataStream t, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [dataUpTo]; omega
    · intro p hp
      simp only [dataUpTo, List.mem_map, List.mem_range] at hp
      obtain ⟨i, _, rfl⟩ := hp
      exact hobs_pos i
    · intro p hp
      simp only [dataUpTo, List.mem_map, List.mem_range] at hp
      obtain ⟨i, _, rfl⟩ := hp
      simpa using hobs_correct i
    · intro x hx
      obtain ⟨⟨idx, hidx⟩, heq⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hx)
      have hidx' : idx < (S m).card := by rw [← Finset.length_toList]; exact hidx
      refine ⟨obs (σ.length + idx), ?_, ?_⟩
      · simp only [dataUpTo, List.mem_map, List.mem_range]
        exact ⟨σ.length + idx, by simp [t]; omega, rfl⟩
      · simp only [obs, show ¬ (σ.length + idx < σ.length) by omega, ↓reduceDIte]
        conv_lhs => simp only [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt hidx']
        exact heq
    · intro i hi hi'
      simp only [dataUpTo, List.getElem_map, List.getElem_range]
      change obs i = σ[i]; simp [obs, hi]
    · exact ht₀ t (le_max_left _ _)
  -- === LOCKING SEQUENCE ===
  let B (n : ℕ) := { σ : List (X × Bool) //
    n < σ.length ∧ (∀ p ∈ σ, p.2 = true) ∧ (∀ p ∈ σ, p.1 ∈ S n) ∧
    (∀ x ∈ S n, ∃ p ∈ σ, p.1 = x) ∧ L.conjecture σ = fun x => decide (x ∈ S n) }
  let ce0 := conv_ext 0 [] (by simp) (by simp)
  let base : B 0 := ⟨ce0.choose, by have := ce0.choose_spec; omega,
    ce0.choose_spec.2.1, ce0.choose_spec.2.2.1, ce0.choose_spec.2.2.2.1,
    ce0.choose_spec.2.2.2.2.2⟩
  let ce (n : ℕ) (b : B n) :=
    conv_ext (n + 1) b.val (b.prop.2.1) (fun p hp => hS_mono n (b.prop.2.2.1 p hp))
  let step : ∀ n, B n → B (n + 1) := fun n b =>
    ⟨(ce n b).choose, by have := (ce n b).choose_spec; have := b.prop.1; omega,
      (ce n b).choose_spec.2.1, (ce n b).choose_spec.2.2.1,
      (ce n b).choose_spec.2.2.2.1, (ce n b).choose_spec.2.2.2.2.2⟩
  let chain : (n : ℕ) → B n := Nat.rec base (fun k ih => step k ih)
  let lock (n : ℕ) := (chain n).val
  -- Basic properties
  have hlock_len : ∀ n, n < (lock n).length := fun n => (chain n).prop.1
  have hlock_pos : ∀ n, ∀ p ∈ lock n, p.2 = true := fun n => (chain n).prop.2.1
  have hlock_in : ∀ n, ∀ p ∈ lock n, p.1 ∈ S n := fun n => (chain n).prop.2.2.1
  have hlock_cov : ∀ n, ∀ x ∈ S n, ∃ p ∈ lock n, p.1 = x :=
    fun n => (chain n).prop.2.2.2.1
  have hlock_conj : ∀ n, L.conjecture (lock n) = fun x => decide (x ∈ S n) :=
    fun n => (chain n).prop.2.2.2.2
  have hce_spec : ∀ n, let h := ce n (chain n)
      lock (n + 1) = h.choose := fun _ => rfl
  have hlock_len_strict : ∀ n, (lock n).length < (lock (n + 1)).length := by
    intro n; rw [hce_spec n]; exact (ce n (chain n)).choose_spec.1
  have hlock_pref : ∀ n (i : ℕ) (hi : i < (lock n).length)
      (hi' : i < (lock (n + 1)).length),
      (lock (n + 1))[i] = (lock n)[i] := by
    intro n; rw [hce_spec n]; exact (ce n (chain n)).choose_spec.2.2.2.2.1
  have hlock_len_mono : ∀ m n, m ≤ n → (lock m).length ≤ (lock n).length := by
    intro m n hmn; induction hmn with
    | refl => exact le_rfl
    | step _ ih => exact Nat.le_of_lt (Nat.lt_of_le_of_lt ih (hlock_len_strict _))
  have hlock_pref_gen : ∀ m n (hmn : m ≤ n) (i : ℕ) (hi : i < (lock m).length)
      (hi' : i < (lock n).length),
      (lock n)[i] = (lock m)[i] := by
    intro m n hmn; induction hmn with
    | refl => intro i _ _; rfl
    | @step j hmn ih =>
      intro i hi hi'
      have hi_mid : i < (lock j).length :=
        Nat.lt_of_lt_of_le hi (hlock_len_mono _ _ (Nat.le_of_succ_le_succ (Nat.succ_le_of_lt
          (Nat.lt_of_le_of_lt hmn (Nat.lt_succ_iff.mpr le_rfl)))))
      rw [hlock_pref j i hi_mid hi', ih i hi hi_mid]
  -- === ADVERSARIAL TEXT ===
  let T_adv : DataStream X Bool :=
    ⟨fun t => (lock (t + 1))[t]'(by have := hlock_len (t + 1); omega)⟩
  have T_adv_pos : ∀ t, (T_adv.observe t).2 = true := by
    intro t; exact hlock_pos (t + 1) _ (List.getElem_mem _)
  have T_adv_correct : ∀ t, c_inf (T_adv.observe t).1 = true := by
    intro t; exact hS_pos (t + 1) _ (hlock_in (t + 1) _ (List.getElem_mem _))
  have hobs_eq : ∀ n (i : ℕ) (hi : i < (lock n).length),
      T_adv.observe i = (lock n)[i] := by
    intro n i hi
    change (lock (i + 1))[i]'_ = (lock n)[i]
    by_cases h : i + 1 ≤ n
    · have hi1 : i < (lock (i + 1)).length := by have := hlock_len (i + 1); omega
      exact (hlock_pref_gen (i + 1) n h i hi1 (by omega)).symm
    · have h' : n ≤ i + 1 := by omega
      exact hlock_pref_gen n (i + 1) h' i hi (by have := hlock_len (i + 1); omega)
  have T_adv_exh : ∀ x, c_inf x = true → ∃ t, (T_adv.observe t).1 = x := by
    intro x hx
    obtain ⟨n, hn⟩ := hS_exh x hx
    obtain ⟨p, hp_mem, hp_eq⟩ := hlock_cov n x hn
    obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp hp_mem
    refine ⟨idx, ?_⟩
    have h := hobs_eq n idx hidx
    change (T_adv.observe idx).1 = x
    have : T_adv.observe idx = (lock n)[idx] := h
    rw [this]; rw [show (lock n)[idx] = p from heq]; exact hp_eq
  let T_inf : TextPresentation X c_inf :=
    ⟨T_adv, T_adv_pos, T_adv_correct, T_adv_exh⟩
  -- === CONTRADICTION ===
  obtain ⟨t₀, ht₀⟩ := hL c_inf hc_inf_mem T_inf
  let n := t₀ + 1
  have hn_ge : (lock n).length - 1 ≥ t₀ := by have := hlock_len n; omega
  have hconv' := ht₀ ((lock n).length - 1) hn_ge
  have hdata_eq : dataUpTo T_inf.toDataStream ((lock n).length - 1) = lock n := by
    have hlen_pos : 0 < (lock n).length := by have := hlock_len n; omega
    apply List.ext_getElem
    · simp [dataUpTo]; omega
    · intro i h1 h2
      simp only [dataUpTo, List.getElem_map, List.getElem_range]
      exact hobs_eq n i h2
  rw [hdata_eq] at hconv'
  exact hS_ne n (by rw [← hlock_conj n, hconv'])

/-- Mind change characterization: EX-learnable iff every text presentation has
    finite mind change ordinal. With correctness encoded in MindChangeOrdinal,
    `< omega0` captures both correct convergence and finite mind changes. -/
theorem mind_change_characterization (X : Type u)
    (C : ConceptClass X Bool) :
    EXLearnable X C ↔
      ∃ (L : GoldLearner X Bool),
        ∀ (c : Concept X Bool), c ∈ C →
          ∀ (T : TextPresentation X c),
            MindChangeOrdinal X L c T.toDataStream < Ordinal.omega0 := by
  -- Bridge: dataUpTo T t = T.prefix (t + 1) (by rfl, both = (List.range (t+1)).map T.observe)
  have bridge : ∀ (T : DataStream X Bool) (t : ℕ),
      dataUpTo T t = T.prefix (t + 1) := fun _ _ => rfl
  constructor
  · -- Forward: EXLearnable → bounded MindChangeOrdinal
    intro ⟨L, hL⟩
    exact ⟨L, fun c hcC T => by
      obtain ⟨t₀, ht₀⟩ := hL c hcC T
      -- Convert EXLearnable convergence (dataUpTo) to prefix convergence
      have hpref : ∀ t ≥ t₀ + 1, L.conjecture (T.toDataStream.prefix t) = c := by
        intro t ht
        have h := ht₀ (t - 1) (by omega)
        rw [bridge] at h
        rwa [show t - 1 + 1 = t from by omega] at h
      -- Changes are finite: no changes after t₀ + 1 (learner stabilized on c)
      have hfin : { t : ℕ | L.conjecture (T.toDataStream.prefix t) ≠
                             L.conjecture (T.toDataStream.prefix (t + 1)) }.Finite :=
        Set.Finite.subset (Finset.range (t₀ + 1)).finite_toSet (fun t ht => by
          simp only [Set.mem_setOf] at ht
          simp only [Finset.mem_coe, Finset.mem_range]
          by_contra hge; push Not at hge
          exact ht (by rw [hpref t (by omega), hpref (t + 1) (by omega)]))
      -- Unfold MindChangeOrdinal: Finite + correct convergence → (card : Ordinal) < omega0
      change MindChangeOrdinal X L c T.toDataStream < Ordinal.omega0
      unfold MindChangeOrdinal
      rw [dif_pos hfin, if_pos ⟨t₀ + 1, hpref⟩]
      exact Ordinal.natCast_lt_omega0 _⟩
  · -- Backward: bounded MindChangeOrdinal → EXLearnable
    intro ⟨L, hL⟩
    refine ⟨L, fun c hcC T => ?_⟩
    have hmco := hL c hcC T
    -- MindChangeOrdinal < omega0 forces the finite+correct branch
    unfold MindChangeOrdinal at hmco
    by_cases hfin : { t : ℕ | L.conjecture (T.toDataStream.prefix t) ≠
                               L.conjecture (T.toDataStream.prefix (t + 1)) }.Finite
    · rw [dif_pos hfin] at hmco
      by_cases hconv : ∃ t₀, ∀ t ≥ t₀, L.conjecture (T.toDataStream.prefix t) = c
      · -- Extract convergence and bridge back to dataUpTo
        obtain ⟨t₀, ht₀⟩ := hconv
        exact ⟨t₀, fun t ht => by
          rw [bridge]
          exact ht₀ (t + 1) (by omega)⟩
      · -- Incorrect convergence → MindChangeOrdinal = omega0, contradicts < omega0
        rw [if_neg hconv] at hmco; exact absurd hmco (lt_irrefl _)
    · -- Infinite changes → MindChangeOrdinal = omega0, contradicts < omega0
      rw [dif_neg hfin] at hmco; exact absurd hmco (lt_irrefl _)
