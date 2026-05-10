/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.Generalization
import LeanPool.FormalLearningTheory.Complexity.Symmetrization
import LeanPool.FormalLearningTheory.Complexity.Rademacher
import LeanPool.FormalLearningTheory.Complexity.Measurability

/-!
# Generalization Results

Theorems factored out of the generalization and Rademacher developments.
The public statements use the primed uniform-convergence route from
`Symmetrization.lean`.

## Main results

- `uc_does_not_imply_online` : UC ⊬ online learnability (paradigm separation)
- `consistent_learner_pac` : consistency + finite VCDim → PAC
- `sample_complexity_lower_bound` : PAC lower bound via VCDim
- `rademacher_vanishing_imp_pac` : uniform Rademacher vanishing → PAC
-/

universe u

attribute [local instance] Classical.propDecidable

-- ============================================================
-- Block 1: Section UCNotOnline (moved from Generalization.lean)
-- ============================================================

section UCNotOnline
/-- Threshold concept class on X induced by an embedding φ : ℕ ↪ X.
    C_φ = { x ↦ decide(∃ k ≤ n, φ k = x) | n : ℕ }. -/
private noncomputable def thresholdClassX {X : Type u} (φ : ℕ ↪ X) : ConceptClass X Bool :=
  { f | ∃ n : ℕ, f = fun x => decide (∃ k, k ≤ n ∧ φ k = x) }

/-- Threshold monotonicity for C_φ: if k ≤ n then c_n(φ(k)) = true. -/
private theorem thresholdX_mem {X : Type u} {φ : ℕ ↪ X} {n k : ℕ} (hk : k ≤ n) :
    (fun x => decide (∃ j, j ≤ n ∧ φ j = x)) (φ k) = true := by
  simp only [decide_eq_true_eq]; exact ⟨k, hk, rfl⟩

/-- If k > n then c_n(φ(k)) = false. -/
private theorem thresholdX_not_mem {X : Type u} {φ : ℕ ↪ X} {n k : ℕ} (hk : n < k) :
    (fun x => decide (∃ j, j ≤ n ∧ φ j = x)) (φ k) = false := by
  simp only [decide_eq_false_iff_not]
  rintro ⟨j, hj, hφ⟩
  have := φ.injective hφ
  omega

/-- No 2-element subset of X is shattered by C_φ. -/
private theorem thresholdX_not_shatter_pair {X : Type u} {φ : ℕ ↪ X}
    {S : Finset X} (hcard : 2 ≤ S.card) :
    ¬ Shatters X (thresholdClassX φ) S := by
  intro hshat
  have ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨c₁, ⟨n₁, rfl⟩, hc₁⟩ := hshat (fun s => if (s : X) = a then true else false)
  have hc₁a : ∃ k, k ≤ n₁ ∧ φ k = a := by
    simpa using hc₁ ⟨a, ha⟩
  have hc₁b : ¬ ∃ k, k ≤ n₁ ∧ φ k = b := by
    intro hbad
    have h := hc₁ ⟨b, hb⟩
    have htrue : decide (∃ k, k ≤ n₁ ∧ φ k = b) = true := decide_eq_true hbad
    have hfalse : (if (b : X) = a then true else false) = false := by
      simp [Ne.symm hab]
    change decide (∃ k, k ≤ n₁ ∧ φ k = b) =
        (if (b : X) = a then true else false) at h
    rw [htrue, hfalse] at h
    cases h
  obtain ⟨c₂, ⟨n₂, rfl⟩, hc₂⟩ := hshat (fun s => if (s : X) = b then true else false)
  have hc₂a : ¬ ∃ k, k ≤ n₂ ∧ φ k = a := by
    intro hbad
    have h := hc₂ ⟨a, ha⟩
    have htrue : decide (∃ k, k ≤ n₂ ∧ φ k = a) = true := decide_eq_true hbad
    have hfalse : (if (a : X) = b then true else false) = false := by
      simp [hab]
    change decide (∃ k, k ≤ n₂ ∧ φ k = a) =
        (if (a : X) = b then true else false) at h
    rw [htrue, hfalse] at h
    cases h
  have hc₂b : ∃ k, k ≤ n₂ ∧ φ k = b := by
    simpa using hc₂ ⟨b, hb⟩
  obtain ⟨i, hi_le, rfl⟩ := hc₁a
  obtain ⟨j, hj_le, hφj⟩ := hc₂b
  have hj_gt : n₁ < j := by
    by_contra h; push Not at h
    exact hc₁b ⟨j, h, hφj⟩
  have hi_gt : n₂ < i := by
    by_contra h; push Not at h
    exact hc₂a ⟨i, h, rfl⟩
  omega

/-- VCDim of C_φ is finite (≤ 1). -/
private theorem vcdim_thresholdX_finite {X : Type u} (φ : ℕ ↪ X) :
    VCDim X (thresholdClassX φ) < ⊤ := by
  apply lt_of_le_of_lt _ (WithTop.coe_lt_top (a := 1))
  apply iSup₂_le
  intro S hshat
  by_contra hgt
  push Not at hgt
  have hcard2 : 2 ≤ S.card := by exact_mod_cast hgt
  exact thresholdX_not_shatter_pair hcard2 hshat

/-- Count mistakes from state s (same as in Separation.lean but for local use). -/
private noncomputable def mistakesFromG {X : Type u}
    (L : OnlineLearner X Bool) (s : L.State) (c : X → Bool) : List X → ℕ
  | [] => 0
  | x :: xs =>
    (if L.predict s x ≠ c x then 1 else 0) +
      mistakesFromG L (L.update s x (c x)) c xs

/-- Relate mistakesFromG to the original mistakes function. -/
private theorem mistakesFromG_init_eq {X : Type u}
    (L : OnlineLearner X Bool) (c : X → Bool) (seq : List X) :
    mistakesFromG L L.init c seq = L.mistakes c seq := by
  suffices h : ∀ (s : L.State) (acc : ℕ),
      OnlineLearner.mistakes.go L c s seq acc = mistakesFromG L s c seq + acc by
    simp [OnlineLearner.mistakes, h L.init 0]
  induction seq with
  | nil => intro s acc; simp [OnlineLearner.mistakes.go, mistakesFromG]
  | cons x xs ih =>
    intro s acc
    simp only [OnlineLearner.mistakes.go, mistakesFromG]
    rw [ih]
    by_cases h : L.predict s x = c x
    · simp_all
    · simp_all; omega

/-- Adversary binary search on C_φ: for any learner starting from state s,
    there exist a sequence and a concept c_n ∈ C_φ where the learner makes d mistakes,
    where the threshold n ranges in [lo, lo + 2^d - 1]. -/
private theorem adversary_threshold {X : Type u} {φ : ℕ ↪ X}
    (L : OnlineLearner X Bool) (s : L.State) (lo : ℕ) :
    ∀ d : ℕ, ∃ (seq : List X) (n : ℕ),
      lo ≤ n ∧ n < lo + 2 ^ d ∧
      (fun x => decide (∃ k, k ≤ n ∧ φ k = x)) ∈ thresholdClassX φ ∧
      mistakesFromG L s (fun x => decide (∃ k, k ≤ n ∧ φ k = x)) seq = d := by
  intro d
  induction d generalizing lo s with
  | zero =>
    refine ⟨[], lo, le_rfl, by simp, ⟨lo, rfl⟩, rfl⟩
  | succ d ih =>
    set mid := lo + 2 ^ d with hmid_def
    have hpow_pos : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
    by_cases hpred : L.predict s (φ mid) = true
    · obtain ⟨seq', n, hn_lo, hn_hi, hn_mem, hn_count⟩ := ih (L.update s (φ mid) false) lo
      have hn_lt_mid : n < mid := by omega
      have hcn_mid : decide (∃ k, k ≤ n ∧ φ k = φ mid) = false := by
        simp only [decide_eq_false_iff_not]
        rintro ⟨k, hk, hφ⟩; have := φ.injective hφ; omega
      refine ⟨φ mid :: seq', n, hn_lo, by ring_nf; omega, hn_mem, ?_⟩
      change (if L.predict s (φ mid) ≠ _ then 1 else 0) +
        mistakesFromG L (L.update s (φ mid) _) _ seq' = d + 1
      have : (fun x => decide (∃ k, k ≤ n ∧ φ k = x)) (φ mid) = false := hcn_mid
      rw [this, hpred]; simp; omega
    · have hpf : L.predict s (φ mid) = false := by
        cases h : L.predict s (φ mid) <;> simp_all
      obtain ⟨seq', n, hn_lo, hn_hi, hn_mem, hn_count⟩ := ih (L.update s (φ mid) true) mid
      have hn_ge_mid : mid ≤ n := hn_lo
      have hcn_mid : decide (∃ k, k ≤ n ∧ φ k = φ mid) = true := by
        simp only [decide_eq_true_eq]; exact ⟨mid, hn_ge_mid, rfl⟩
      refine ⟨φ mid :: seq', n, by omega, by ring_nf; omega, hn_mem, ?_⟩
      change (if L.predict s (φ mid) ≠ _ then 1 else 0) +
        mistakesFromG L (L.update s (φ mid) _) _ seq' = d + 1
      have : (fun x => decide (∃ k, k ≤ n ∧ φ k = x)) (φ mid) = true := hcn_mid
      rw [this, hpf]; simp; omega

/-- PAC uniform convergence does NOT imply online learnability.
    There exist concept classes with finite VCDim (hence PAC learnable)
    but infinite Littlestone dimension (hence not online learnable with
    finite mistake bound).
    Witness: threshold class C_φ on X via embedding φ : ℕ ↪ X.
    VCDim(C_φ) ≤ 1 (monotonicity prevents 2-shattering).
    LittlestoneDim(C_φ) = ∞ (adversary binary search forces d mistakes for any d). -/
theorem uc_does_not_imply_online (X : Type u) [MeasurableSpace X] [Infinite X]
    (hmeas_C_all : ∀ (C : ConceptClass X Bool), ∀ h ∈ C, Measurable h)
    (hc_meas_all : ∀ c : Concept X Bool, Measurable c)
    (hWB_all : ∀ (C : ConceptClass X Bool), WellBehavedVC X C) :
    ¬ (∀ (C : ConceptClass X Bool),
      HasUniformConvergence X C →
        ∃ (M : ℕ), MistakeBounded X Bool C M) := by
  intro h
  have φ := Infinite.natEmbedding X
  set C := thresholdClassX φ with hC_def
  have hUC : HasUniformConvergence X C :=
    vcdim_finite_imp_uc' X C (vcdim_thresholdX_finite φ) (hmeas_C_all C) hc_meas_all (hWB_all C)
  obtain ⟨M, L, hL⟩ := h C hUC
  obtain ⟨seq, n, _, _, hn_mem, hcount⟩ :=
    adversary_threshold L L.init 0 (M + 1)
  have hbound := hL _ hn_mem seq
  rw [← mistakesFromG_init_eq] at hbound
  omega

end UCNotOnline

/-- Typeclass version of uc_does_not_imply_online.
    Uses UniversallyMeasurableSpace to avoid threading ∀-quantified measurability. -/
theorem uc_does_not_imply_online' (X : Type u) [MeasurableSpace X] [Infinite X]
    [UniversallyMeasurableSpace X] :
    ¬ (∀ (C : ConceptClass X Bool),
      HasUniformConvergence X C →
        ∃ (M : ℕ), MistakeBounded X Bool C M) :=
  uc_does_not_imply_online X
    (fun C => MeasurableConceptClass.hmeas_C C)
    (UniversallyMeasurableSpace.concept_measurable)
    (UniversallyMeasurableSpace.class_wellBehaved)

-- ============================================================
-- Block 2: consistent_learner_pac (moved from Generalization.lean)
-- ============================================================

/-- Consistent learners are PAC learners when VCDim < ⊤. -/
theorem consistent_learner_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hvcdim : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C)
    (L : BatchLearner X Bool)
    (_hcons : ∀ {m : ℕ} (S : Fin m → X × Bool), ∀ i, L.learn S (S i).1 = (S i).2) :
    PACLearnable X C := by
  by_cases hne : C.Nonempty
  · exact uc_imp_pac X C hne (vcdim_finite_imp_uc' X C hvcdim hmeas_C hc_meas hWB)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨⟨Set.univ, fun _ => fun _ => false, fun _ => Set.mem_univ _⟩,
           fun _ _ => 0, fun _ _ _ _ _ _ c hcC => by simp [hne] at hcC⟩

/-- Typeclass version of consistent_learner_pac. -/
theorem consistent_learner_pac' (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C] (hvcdim : VCDim X C < ⊤)
    (L : BatchLearner X Bool)
    (hcons : ∀ {m : ℕ} (S : Fin m → X × Bool), ∀ i, L.learn S (S i).1 = (S i).2) :
    PACLearnable X C :=
  consistent_learner_pac X C hvcdim
    (MeasurableConceptClass.hmeas_C C) (MeasurableConceptClass.hc_meas C)
    (MeasurableConceptClass.hWB C) L hcons

-- ============================================================
-- Block 3: sample_complexity_lower_bound (moved from Generalization.lean)
-- ============================================================

/-- Sample complexity lower bound: ⌈(d-1)/2⌉ ≤ SampleComplexity. -/
theorem sample_complexity_lower_bound (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (d : ℕ)
    (hd : VCDim X C = d) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7) (hd_pos : 1 ≤ d)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ := by
  unfold SampleComplexity
  set S := { m : ℕ | ∃ (L : BatchLearner X Bool),
    ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ c ∈ C,
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ) } with hS_def
  have hvcdim_fin : VCDim X C < ⊤ := by
    rw [hd]; exact WithTop.coe_lt_top d
  have hpac : PACLearnable X C := by
    by_cases hne : C.Nonempty
    · exact uc_imp_pac X C hne (vcdim_finite_imp_uc' X C hvcdim_fin hmeas_C hc_meas hWB)
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨⟨Set.univ, fun _ => fun _ => false, fun _ => Set.mem_univ _⟩,
             fun _ _ => 0, fun _ _ _ _ _ _ c hcC => by simp [hne] at hcC⟩
  obtain ⟨L, mf, hpac_wit⟩ := hpac
  have hmem : mf ε δ ∈ S := ⟨L, fun D hD c hcC => hpac_wit ε δ hε hδ D hD c hcC⟩
  exact le_csInf ⟨mf ε δ, hmem⟩ fun m hm =>
    pac_lower_bound_member X C d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos m hm

/-- Typeclass version of sample_complexity_lower_bound. -/
theorem sample_complexity_lower_bound' (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C] (d : ℕ)
    (hd : VCDim X C = d) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7) (hd_pos : 1 ≤ d) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ :=
  sample_complexity_lower_bound X C d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos
    (MeasurableConceptClass.hmeas_C C) (MeasurableConceptClass.hc_meas C)
    (MeasurableConceptClass.hWB C)

-- ============================================================
-- Block 4: rademacher_vanishing_imp_pac (moved from Rademacher.lean)
-- ============================================================

/-- Rademacher vanishing → PAC learnability (← direction of fundamental_rademacher).
    Uses uniform vanishing (∃ m₀ ∀ D), the textbook-standard form. -/
theorem rademacher_vanishing_imp_pac (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C)
    (hrad : ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε) :
    PACLearnable X C := by
  apply vcdim_finite_imp_pac_via_uc' _ _ _ hmeas_C hc_meas hWB
  by_contra hvcdim_inf
  push Not at hvcdim_inf
  have hvcdim_top : VCDim X C = ⊤ := le_antisymm le_top hvcdim_inf
  have h_large_shatter : ∀ n : ℕ, ∃ T : Finset X, Shatters X C T ∧ n ≤ T.card := by
    intro n; by_contra h_neg; push Not at h_neg
    have hle : VCDim X C ≤ ↑n := by
      apply iSup₂_le; intro T hT; exact_mod_cast le_of_lt (h_neg T hT)
    rw [hvcdim_top] at hle; exact absurd hle (by simp)
  obtain ⟨m₀, hm₀⟩ := hrad (1 / 2) (by norm_num)
  set m := max m₀ 1
  obtain ⟨T, hT_shat, hT_card⟩ := h_large_shatter (4 * m ^ 2 + 1)
  obtain ⟨D, hD, hRad_ge⟩ := rademacher_lower_bound_on_shattered X C T hT_shat m (by omega) hT_card
  linarith [hm₀ D hD m (le_max_left m₀ 1)]

/-- Typeclass version of rademacher_vanishing_imp_pac. -/
theorem rademacher_vanishing_imp_pac' (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C]
    (hrad : ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε) :
    PACLearnable X C :=
  rademacher_vanishing_imp_pac X C
    (MeasurableConceptClass.hmeas_C C) (MeasurableConceptClass.hc_meas C)
    (MeasurableConceptClass.hWB C) hrad
