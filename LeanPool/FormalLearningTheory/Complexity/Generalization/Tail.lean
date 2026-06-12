/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.Generalization.Core

/-!
# LeanPool.FormalLearningTheory.Complexity.Generalization.Tail
-/

universe u v


section FinBlockInfrastructure

open Equiv in
/-- Extract block j from a flat array of k*m elements, using finProdFinEquiv. -/
def blockExtract {α : Type*} (k m : ℕ) (S : Fin (k * m) → α) (j : Fin k) : Fin m → α :=
  fun i => S (finProdFinEquiv (j, i))

/-- Boolean majority vote: returns true iff strictly more than half the votes are true. -/
def majorityVote (k : ℕ) (votes : Fin k → Bool) : Bool :=
  decide (2 * (Finset.univ.filter (fun j => votes j = true)).card > k)

/-- Block index sets are disjoint for distinct blocks. -/
lemma block_extract_disjoint (k m : ℕ) (j₁ j₂ : Fin k) (hne : j₁ ≠ j₂) :
    Disjoint
      (Finset.image (fun i : Fin m => finProdFinEquiv (j₁, i)) Finset.univ)
      (Finset.image (fun i : Fin m => finProdFinEquiv (j₂, i)) Finset.univ) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
  obtain ⟨i₁, rfl⟩ := ha
  obtain ⟨i₂, rfl⟩ := hb
  intro heq
  exact hne (congr_arg Prod.fst (finProdFinEquiv.injective heq))

/-- Block extraction is measurable: extracting block j from a pi-type is measurable. -/
lemma block_extract_measurable {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (j : Fin k) :
    Measurable (fun (ω : Fin (k * m) → X) => blockExtract k m ω j) := by
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)

/-- Block extractions are independent under the product measure.
    Key infrastructure for boosting (D4) and probability amplification. -/
lemma iIndepFun_block_extract {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    ProbabilityTheory.iIndepFun (β := fun _ : Fin k => Fin m → X)
      (fun (j : Fin k) (ω : Fin (k * m) → X) => blockExtract k m ω j)
      (MeasureTheory.Measure.pi (fun _ : Fin (k * m) => D)) := by
  open MeasureTheory MeasureTheory.Measure ProbabilityTheory Equiv in
  -- The currying MeasurableEquiv: Fin(k*m) → X  ≃ᵐ  Fin k → (Fin m → X)
  set pcl := MeasurableEquiv.piCongrLeft (fun _ : Fin k × Fin m => X) finProdFinEquiv.symm
  set cur := MeasurableEquiv.curry (Fin k) (Fin m) X
  set e : (Fin (k * m) → X) ≃ᵐ (Fin k → Fin m → X) := pcl.trans cur
  -- blockExtract = e pointwise
  have he : ∀ j ω, blockExtract k m ω j = e ω j := by
    intro j ω; ext i
    simp only [blockExtract, e, MeasurableEquiv.trans_apply, pcl, cur]
    simp [MeasurableEquiv.piCongrLeft, piCongrLeft_apply, MeasurableEquiv.curry,
      Function.curry]
  -- Rewrite goal to use e
  simp_rw [he]
  -- Now goal: iIndepFun (fun j ω => e ω j) (Measure.pi (fun _ => D))
  -- Apply the map characterization
  set μ := Measure.pi (fun _ : Fin (k * m) => D)
  -- AEMeasurable: each component is measurable
  have hmeas : ∀ j : Fin k, AEMeasurable (fun ω => e ω j) μ :=
    fun j => ((measurable_pi_apply j).comp e.measurable).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hmeas]
  -- Goal: μ.map (fun ω j => e ω j) = Measure.pi (fun j => μ.map (fun ω => e ω j))
  -- LHS: μ.map (fun ω j => e ω j) = μ.map e
  have hlhs : (fun (ω : Fin (k * m) → X) (j : Fin k) => e ω j) = e := by
    ext ω j; rfl
  rw [hlhs]
  -- Define the nested product measure
  set D' : Fin k → Measure (Fin m → X) := fun _ => Measure.pi (fun _ : Fin m => D)
  -- Step 1: μ.map pcl preserves measure
  have hpcl : MeasurePreserving pcl μ (Measure.pi (fun _ : Fin k × Fin m => D)) :=
    measurePreserving_piCongrLeft (fun _ : Fin k × Fin m => D) finProdFinEquiv.symm
  -- Step 2: (flat on Fin k × Fin m).map cur = nested product
  have hcur : (Measure.pi (fun _ : Fin k × Fin m => D)).map cur = Measure.pi D' := by
    have h1 : Measure.pi (fun _ : Fin k × Fin m => D) =
        infinitePi (fun _ : Fin k × Fin m => D) :=
      (infinitePi_eq_pi (μ := fun _ : Fin k × Fin m => D)).symm
    rw [h1]
    have h3 : D' = fun _ : Fin k => infinitePi (fun _ : Fin m => D) := by
      funext; exact (infinitePi_eq_pi (μ := fun _ : Fin m => D)).symm
    have h2 : Measure.pi D' = infinitePi D' :=
      (infinitePi_eq_pi (μ := D')).symm
    rw [h2, h3]
    exact infinitePi_map_curry (fun _ : Fin k => fun _ : Fin m => D)
  -- Step 3: μ.map e = Measure.pi D'
  have hmap_e : μ.map e = Measure.pi D' := by
    have : (e : (Fin (k * m) → X) → (Fin k → Fin m → X)) = cur ∘ pcl := rfl
    rw [this, ← map_map cur.measurable pcl.measurable, hpcl.map_eq, hcur]
  rw [hmap_e]
  -- RHS: Measure.pi (fun j => μ.map (fun ω => e ω j))
  -- Each marginal: μ.map (fun ω => e ω j) = D' j
  congr 1
  ext j : 1
  -- μ.map (fun ω => e ω j) = j-th marginal of μ.map e = D' j
  have hcomp : (fun ω => e ω j) = (fun f => f j) ∘ (e : (Fin (k * m) → X) → _) := rfl
  rw [hcomp, ← map_map (measurable_pi_apply j) e.measurable, hmap_e]
  exact ((measurePreserving_eval D' j).map_eq).symm

end FinBlockInfrastructure

section PACTheoremHelpers
/-- Shattering lifting: if T is shattered by C and f : ↥T → Bool, then
    there exists c ∈ C that agrees with f on all of T. -/
theorem shatters_realize {X : Type u} {C : ConceptClass X Bool} {T : Finset X}
    (hT : Shatters X C T) (f : ↥T → Bool) :
    ∃ c ∈ C, ∀ x : ↥T, c (x : X) = f x :=
  hT f

/-- Key counting lemma: for any h : ↥T → Bool on a shattered set T with |T| ≥ 2,
    there exists c ∈ C with #{x ∈ T | c x ≠ h x} > |T|/4.
    Lifts exists_many_disagreements through shattering. -/
theorem shatters_hard_labeling {X : Type u} {C : ConceptClass X Bool} {T : Finset X}
    (hT : Shatters X C T) (h : ↥T → Bool) (hcard : 2 ≤ T.card) :
    ∃ c ∈ C, T.card <
      4 * (Finset.univ.filter fun x : ↥T => c (x : X) ≠ h x).card := by
  classical
  have hcard' : 2 ≤ Fintype.card ↥T := by rwa [Fintype.card_coe]
  obtain ⟨f, hf⟩ := exists_many_disagreements h hcard'
  obtain ⟨c, hcC, hcf⟩ := shatters_realize hT f
  refine ⟨c, hcC, ?_⟩
  convert hf using 2
  · exact (Fintype.card_coe T).symm
  · congr 1; ext x; simp [hcf x]

/-- NFL per-sample lemma for shattered sets: for ANY fixed sample xs and
    ANY hypothesis h, there exists c ∈ C agreeing with h on sample points
    but with high error (> 1 / 4) on the shattered set T.
    Uses the counting argument on unseen points via disagreement_sum_eq. -/
theorem nfl_per_sample_shattered {X : Type u} {C : ConceptClass X Bool}
    {T : Finset X} (hT : Shatters X C T) {m : ℕ} (hTcard : 2 * m < T.card)
    (xs : Fin m → X) (h : X → Bool) :
    ∃ c ∈ C, (∀ i : Fin m, xs i ∈ T → c (xs i) = h (xs i)) ∧
      T.card < 4 * (T.filter fun x => c x ≠ h x).card := by
  classical
  -- Define adversarial labeling: agree with h on seen points, disagree on unseen
  let f : ↥T → Bool := fun ⟨x, _⟩ =>
    if x ∈ Set.range xs then h x else !h x
  -- Shattering gives c ∈ C realizing f
  obtain ⟨c, hcC, hcf⟩ := hT f
  refine ⟨c, hcC, ?_, ?_⟩
  · -- c agrees with h on sample points that are in T
    intro i hi
    have hcfi : c (xs i) = f ⟨xs i, hi⟩ := hcf ⟨xs i, hi⟩
    simp only [f, Set.mem_range_self, ↓reduceIte] at hcfi
    exact hcfi
  · -- c disagrees with h on all unseen points of T
    -- So the disagreement count ≥ |T \ range(xs)| ≥ T.card - m > T.card/2
    -- First: every unseen point in T has c x ≠ h x
    have hunseen : ∀ x ∈ T, x ∉ Set.range xs → c x ≠ h x := by
      intro x hxT hxns
      have hcfx : c x = f ⟨x, hxT⟩ := hcf ⟨x, hxT⟩
      simp only [f, hxns, ↓reduceIte] at hcfx
      rw [hcfx]; cases h x <;> decide
    -- The disagreement filter contains T \ image of xs
    -- Let seen = T.filter (· ∈ range xs)
    set disagree := T.filter (fun x => c x ≠ h x) with hdisagree_def
    -- T \ (Finset.image xs Finset.univ) ⊆ disagree
    have hsub : T \ Finset.image xs Finset.univ ⊆ disagree := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and] at hx
      simp only [hdisagree_def, Finset.mem_filter]
      exact ⟨hx.1, hunseen x hx.1 (by
        intro ⟨i, hi⟩; exact hx.2 ⟨i, hi⟩)⟩
    -- |T \ image xs| ≥ T.card - m
    have hsdiff_card : T.card - m ≤ (T \ Finset.image xs Finset.univ).card := by
      have himg_le : (Finset.image xs Finset.univ).card ≤ m := by
        calc (Finset.image xs Finset.univ).card
            ≤ Fintype.card (Fin m) := Finset.card_image_le
          _ = m := Fintype.card_fin m
      -- |T \ S| + |T ∩ S| = |T| (Finset.card_sdiff_add_card_inter)
      have hkey := Finset.card_sdiff_add_card_inter T (Finset.image xs Finset.univ)
      -- |T ∩ S| ≤ |S| ≤ m
      have hinter_le : (T ∩ Finset.image xs Finset.univ).card ≤ m :=
        le_trans (Finset.card_le_card Finset.inter_subset_right) himg_le
      omega
    -- Combine: disagree.card ≥ T.card - m
    have hdisagree_ge : T.card - m ≤ disagree.card :=
      le_trans hsdiff_card (Finset.card_le_card hsub)
    -- Since 2m < T.card: T.card - m > T.card / 2, so 4*(T.card - m) > 2*T.card > T.card
    -- More precisely: T.card < 4 * (T.card - m) ≤ 4 * disagree.card
    calc T.card < 4 * (T.card - m) := by omega
      _ ≤ 4 * disagree.card := by omega
/-- If VCDim = ⊤, then C is not PAC learnable.
    Proof: for any learner L with sample function mf, pick ε = 1 / 4, δ = 1 / 4.
    Let m = mf(1 / 4, 1 / 4). Since VCDim = ⊤, ∃ shattered set S with |S| ≥ 2m.
    Put D = uniform on S. For random labeling, any m-sample learner
    has expected error ≥ 1 / 4 on unseen points.
    This is the core of pac_imp_vcdim_finite (contrapositive direction). -/
theorem vcdim_infinite_not_pac (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (hinf : VCDim X C = ⊤) :
    ¬ PACLearnable X C := by
  -- Assume PACLearnable for contradiction
  intro ⟨L, mf, hpac⟩
  -- Step 1: VCDim = ⊤ → for any n, ∃ shattered T with |T| > n
  have hvcdim_unbounded : ∀ b : WithTop ℕ, b < ⊤ → ∃ T, ∃ _ : Shatters X C T,
      b < (T.card : WithTop ℕ) := by
    have := (iSup₂_eq_top
      (fun (T : Finset X) (_ : Shatters X C T) => (T.card : WithTop ℕ))).mp
    rw [VCDim] at hinf
    exact this hinf
  -- Step 2: Fix ε = 1 / 4, δ = 1 / 4, m = mf(1 / 4)(1 / 4)
  set m := mf (1 / 4 : ℝ) (1 / 4 : ℝ) with hm_def
  -- Step 3: Get shattered T with |T| > 2m
  obtain ⟨T, hTshat, hTcard⟩ := hvcdim_unbounded (2 * m) (WithTop.coe_lt_top _)
  -- hTcard : (2 * ↑m : WithTop ℕ) < (T.card : WithTop ℕ)
  have hTcard_nat : 2 * m < T.card := by exact_mod_cast hTcard
  -- Step 4: From PAC guarantee, L works for ε=1 / 4, δ=1 / 4
  have hpac14 := hpac (1 / 4 : ℝ) (1 / 4 : ℝ) (by norm_num) (by norm_num)
  -- Step 5: T is nonempty (|T| > 2m ≥ 0)
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; simp [h] at hTcard_nat
  -- Step 6: Derive contradiction.
  -- We need: ∃ D (prob measure on X), ∃ c ∈ C, PAC guarantee fails.
  -- hpac14 says: ∀ D prob, ∀ c ∈ C, Pr[err ≤ 1 / 4] ≥ 3 / 4.
  -- We construct D and find c ∈ C where Pr[err ≤ 1 / 4] < 3 / 4.
  suffices ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
      ∃ c ∈ C,
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal (1 / 4 : ℝ) }
          < ENNReal.ofReal (1 - 1 / 4 : ℝ) by
    obtain ⟨D, hDprob, c, hcC, hfail⟩ := this
    exact not_le.mpr hfail (hpac14 D hDprob c hcC)
  classical
  obtain ⟨_, c₀, hc₀C, _, hcount⟩ := nfl_counting_core hTshat hTcard_nat L
  obtain ⟨D, hDprob, hgood_half⟩ :=
    pac_lower_bound_good_event_le_half (X := X) (T := T) hTne L m c₀
      (1 / 4 : ℝ) (by norm_num) (by simpa using hcount)
  refine ⟨D, hDprob, c₀, hc₀C, ?_⟩
  calc MeasureTheory.Measure.pi (fun _ : Fin m => D)
        { xs : Fin m → X |
          D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
            ≤ ENNReal.ofReal (1 / 4 : ℝ) }
      ≤ ENNReal.ofReal (1 / 2 : ℝ) := hgood_half
    _ < ENNReal.ofReal (1 - 1 / 4 : ℝ) := by
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by norm_num)

end PACTheoremHelpers

/-- Drift rate: how fast the target concept changes over time. -/
abbrev DriftRate := ℝ
