/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.BaseGradient

/-!
The completed resisting objective has a controlled, symmetry-invariant distance to its
minimizers.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open scoped BigOperators
open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5AFinalRepair

/-- The vector with common signed magnitude on the coordinates used by the resisting
construction. -/
noncomputable def uniformSignedPoint (data : LowerCompletionData p d T)
    (a : ℝ) : Point d :=
  (Finset.range T).sum fun i =>
    (a * data.xi i) • coordinateUnit (data.sigma i)

lemma uniformSignedPoint_at_used (data : LowerCompletionData p d T)
    (hsteps : ∀ t < T, ∀ s < t, data.sigma s ≠ data.sigma t)
    {i : ℕ} (hi : i < T) (a : ℝ) :
    uniformSignedPoint data a (data.sigma i) = a * data.xi i := by
  have hinj := sigma_injective_below data hsteps
  unfold uniformSignedPoint
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp [coordinateUnit]
  · intro j hj hji
    have hjT := Finset.mem_range.mp hj
    have hsigma : data.sigma j ≠ data.sigma i := by
      intro hs
      exact hji (hinj hjT hi hs)
    simp [coordinateUnit, hsigma.symm]
  · simp [hi]

lemma uniformSignedPoint_at_unused (data : LowerCompletionData p d T)
    {j : Fin d} (hj : j ∉ (Finset.range T).image data.sigma) (a : ℝ) :
    uniformSignedPoint data a j = 0 := by
  unfold uniformSignedPoint
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i hi
  have hsigma : data.sigma i ≠ j := by
    intro hs
    exact hj (Finset.mem_image.mpr ⟨i, hi, hs⟩)
  simp [coordinateUnit, hsigma.symm]

lemma lpPower_uniformSignedPoint (data : LowerCompletionData p d T)
    {r : ℝ} (hr : 0 < r)
    (hsteps : ∀ t < T,
      (∀ s < t, data.sigma s ≠ data.sigma t) ∧
      (data.xi t = 1 ∨ data.xi t = -1)) (a : ℝ) :
    O3.lpPower r (uniformSignedPoint data a) =
      (T : ℝ) * |a| ^ r := by
  let used : Finset (Fin d) := (Finset.range T).image data.sigma
  have hinj := sigma_injective_below data (fun t ht => (hsteps t ht).1)
  unfold O3.lpPower
  calc
    (∑ j, |uniformSignedPoint data a j| ^ r) =
        ∑ j ∈ used, |uniformSignedPoint data a j| ^ r := by
      symm
      apply Finset.sum_subset (Finset.subset_univ used)
      intro j _ hj
      rw [uniformSignedPoint_at_unused data hj a, abs_zero,
        Real.zero_rpow hr.ne']
    _ = ∑ i ∈ Finset.range T,
        |uniformSignedPoint data a (data.sigma i)| ^ r := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      exact hinj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    _ = ∑ _i ∈ Finset.range T, |a| ^ r := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [uniformSignedPoint_at_used data (fun t ht => (hsteps t ht).1)
        (Finset.mem_range.mp hi) a, abs_mul]
      rcases (hsteps i (Finset.mem_range.mp hi)).2 with hxi | hxi <;>
        rw [hxi] <;> norm_num
    _ = (T : ℝ) * |a| ^ r := by simp

/-- The average of the signed coordinate directions used by the resisting construction. -/
noncomputable def averageDirection (data : LowerCompletionData p d T) : Point d :=
  uniformSignedPoint data (1 / T)

lemma lpNorm_averageDirection (data : LowerCompletionData p d T)
    (hp : 1 < p) (hT : 1 ≤ T)
    (hDelta : data.Delta = (T : ℝ) ^ (-1 / p))
    (hsteps : ∀ t < T,
      (∀ s < t, data.sigma s ≠ data.sigma t) ∧
      (data.xi t = 1 ∨ data.xi t = -1)) :
    lpNorm (conjugateExponent p) (averageDirection data) = data.Delta := by
  let q := conjugateExponent p
  have hq : 0 < q := lt_trans zero_lt_one (O3.one_lt_conjugateExponent hp)
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hpower := lpPower_uniformSignedPoint data hq hsteps (1 / T)
  have habs : |(1 : ℝ) / T| = 1 / T := abs_of_pos (div_pos zero_lt_one hTreal)
  change O3.lpNorm q (uniformSignedPoint data (1 / T)) = data.Delta
  unfold O3.lpNorm
  rw [hpower, habs, hDelta]
  have honeDiv : (1 / (T : ℝ)) ^ q = (T : ℝ) ^ (-q) := by
    rw [show (1 / (T : ℝ)) = (T : ℝ) ^ (-1 : ℝ) by
      simp [div_eq_mul_inv, Real.rpow_neg_one]]
    rw [← Real.rpow_mul hTreal.le]
    congr 1
    ring
  rw [honeDiv]
  have hmul : (T : ℝ) * (T : ℝ) ^ (-q) = (T : ℝ) ^ (1 - q) := by
    calc
      (T : ℝ) * (T : ℝ) ^ (-q) =
          (T : ℝ) ^ (1 : ℝ) * (T : ℝ) ^ (-q) := by rw [Real.rpow_one]
      _ = (T : ℝ) ^ ((1 : ℝ) + (-q)) := (Real.rpow_add hTreal 1 (-q)).symm
      _ = (T : ℝ) ^ (1 - q) := by congr 1
  rw [hmul, ← Real.rpow_mul hTreal.le]
  have hexp : (1 - q) * (1 / q) = -1 / p := by
    change (1 - p / (p - 1)) * (1 / (p / (p - 1))) = -1 / p
    have hp0 : p ≠ 0 := by linarith
    have hp1 : p - 1 ≠ 0 := by linarith
    field_simp [hp0, hp1]; ring
  rw [hexp]

lemma real_sum_range_id (T : ℕ) :
    (Finset.range T).sum (fun i => (i : ℝ)) = (T : ℝ) * (T - 1 : ℕ) / 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hT : T = 0
      · subst T; norm_num
      · push_cast
        have hcast : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hT)]
          norm_num
        rw [hcast]
        ring

lemma pairing_averageDirection (data : LowerCompletionData p d T)
    (hsteps : ∀ t < T, ∀ s < t, data.sigma s ≠ data.sigma t)
     (x : Point d) :
    O3.pairing (averageDirection data) x =
      (1 / T) * (Finset.range T).sum
        (fun i => data.xi i * x (data.sigma i)) := by
  let used : Finset (Fin d) := (Finset.range T).image data.sigma
  have hinj := sigma_injective_below data hsteps
  unfold O3.pairing
  calc
    (∑ j, averageDirection data j * x j) =
        ∑ j ∈ used, averageDirection data j * x j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ used)
      intro j _ hj
      rw [show averageDirection data j = 0 by
        exact uniformSignedPoint_at_unused data hj (1 / T)]
      simp
    _ = ∑ i ∈ Finset.range T,
        averageDirection data (data.sigma i) * x (data.sigma i) := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      exact hinj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
    _ = ∑ i ∈ Finset.range T,
        ((1 / T) * data.xi i) * x (data.sigma i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show averageDirection data (data.sigma i) =
        (1 / T) * data.xi i by
          exact uniformSignedPoint_at_used data hsteps (Finset.mem_range.mp hi) (1 / T)]
    _ = (1 / T) * (Finset.range T).sum
        (fun i => data.xi i * x (data.sigma i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma partialG_final_average_lower (data : LowerCompletionData p d T)
    (hp : 1 < p) (hT : 1 ≤ T)
    (hDelta : data.Delta = (T : ℝ) ^ (-1 / p))
    (hsteps : ∀ t < T,
      (∀ s < t, data.sigma s ≠ data.sigma t) ∧
      (data.xi t = 1 ∨ data.xi t = -1) ∧
      ResistingMaximumAt data t) (x : Point d) :
    -data.Delta * lpNorm p x - (T - 1 : ℕ) * data.delta / 2 ≤
      data.partialG (T - 1) x := by
  have hlast : T - 1 < T := by omega
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsumPieces : (Finset.range T).sum (fun i =>
      data.xi i * x (data.sigma i) - (i : ℝ) * data.delta) ≤
      (T : ℝ) * data.partialG (T - 1) x := by
    calc
      _ ≤ (Finset.range T).sum (fun _i => data.partialG (T - 1) x) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiT := Finset.mem_range.mp hi
        exact ((hsteps (T - 1) hlast).2.2 x).1 i
          (by omega : i ≤ T - 1)
      _ = (T : ℝ) * data.partialG (T - 1) x := by simp
  have hpair := pairing_averageDirection data
    (fun t ht => (hsteps t ht).1) x
  have hsumId := real_sum_range_id T
  have hsumExpand : (Finset.range T).sum (fun i =>
      data.xi i * x (data.sigma i) - (i : ℝ) * data.delta) =
      (Finset.range T).sum (fun i => data.xi i * x (data.sigma i)) -
        ((T : ℝ) * (T - 1 : ℕ) / 2) * data.delta := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsumId]
  rw [hsumExpand] at hsumPieces
  have hpairLower : -data.Delta * lpNorm p x ≤
      O3.pairing (averageDirection data) x := by
    have hholder := O3.abs_pairing_le_lpNorm_mul
      (O3.holderConjugate_conjugateExponent hp).symm
      (averageDirection data) x
    have hnorm := lpNorm_averageDirection data hp hT hDelta
      (fun t ht => ⟨(hsteps t ht).1, (hsteps t ht).2.1⟩)
    change O3.lpNorm (O3.conjugateExponent p) (averageDirection data) =
      data.Delta at hnorm
    rw [hnorm] at hholder
    linarith [neg_le_abs (O3.pairing (averageDirection data) x)]
  rw [hpair] at hpairLower
  have hTone : (0 : ℝ) < T := hTreal
  have hscaled : -(T : ℝ) * data.Delta * lpNorm p x ≤
      (Finset.range T).sum (fun i => data.xi i * x (data.sigma i)) := by
    have := mul_le_mul_of_nonneg_left hpairLower hTreal.le
    field_simp [hTreal.ne'] at this
    nlinarith
  nlinarith

lemma global_minimizer_norm_ge_half (data : LowerObjectiveData p d T)
    (hp : 2 < p) (hassum : LowerObjectiveAssumptions data)
    {minimizer : Point d}
    (hmin : ∀ x, data.completedOracle.value minimizer ≤
      data.completedOracle.value x) :
    (1 / 2 : ℝ) ≤ lpNorm p minimizer := by
  let base := data.toLowerCompletionData
  rcases hassum with ⟨hcompletion, hobjectiveConvex, hobjectiveGradient⟩
  rcases hcompletion with
    ⟨hp', hd, hT, hTd, hx0, hkernel, hDelta, hdelta, hchi, hbeta,
      hqueries, hsteps, hcompletedValue, hcompletedGradient⟩
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hDeltaPos : 0 < base.Delta := by rw [hDelta]; positivity
  have hdeltaPos : 0 < base.delta := by rw [hdelta]; positivity
  have hchiPos : 0 < base.chi := by rw [hchi]; positivity
  have hbetaPos : 0 < base.beta := by rw [hbeta]; exact div_pos hchiPos hkernel.1
  have hlast : T - 1 < T := by omega
  let shortSteps : ∀ s < T,
      (base.xi s = 1 ∨ base.xi s = -1) ∧ ResistingMaximumAt base s :=
    fun s hs => ⟨(hsteps s hs).2.2.2.1, (hsteps s hs).2.2.2.2.2.1⟩
  have hpartialLast := partialH_convex_oneLipschitz base (by linarith) hlast
    shortSteps (hsteps (T - 1) hlast).2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsmooth, -, -⟩ := hkernel
  have hsmoothLast := hsmooth base.chi hchiPos (base.partialH (T - 1))
    hpartialLast.1 hpartialLast.2
  have hG := partialG_final_average_lower base (by linarith) hT hDelta
    (fun s hs => ⟨(hsteps s hs).1, (hsteps s hs).2.2.2.1,
      (hsteps s hs).2.2.2.2.2.1⟩) minimizer
  have hHmax := le_max_left (base.partialG (T - 1) minimizer / 2)
    (lpNorm p minimizer - 3 / 2)
  have hHformula := (hsteps (T - 1) hlast).2.2.2.2.2.2.1 minimizer
  have hHlower : -base.Delta * lpNorm p minimizer / 2 -
      (T - 1 : ℕ) * base.delta / 4 ≤ base.partialH (T - 1) minimizer := by
    rw [hHformula]
    nlinarith
  have hsmoothLower := (hsmoothLast.2.1 minimizer).1
  have hvalueLower : base.beta *
      (-base.Delta * lpNorm p minimizer / 2 -
        (T - 1 : ℕ) * base.delta / 4 - base.chi) ≤
      data.completedOracle.value minimizer := by
    rw [hcompletedValue]
    nlinarith [mul_le_mul_of_nonneg_left
      ((sub_le_sub_right hHlower base.chi).trans hsmoothLower) hbetaPos.le]
  have hcandidateH := partialH_final_adversarialPoint_le base (by linarith)
    hT hdeltaPos hDelta (fun s hs =>
      ⟨(hsteps s hs).1, (hsteps s hs).2.2.2.1,
        (hsteps s hs).2.2.2.2.2.1, (hsteps s hs).2.2.2.2.2.2.1⟩)
  have hcandidateValue : data.completedOracle.value (adversarialPoint base) ≤
      -base.beta * base.Delta / 2 := by
    have happ := (hsmoothLast.2.1 (adversarialPoint base)).2
    rw [hcompletedValue]
    nlinarith [mul_le_mul_of_nonneg_left
      (happ.trans hcandidateH) hbetaPos.le]
  have hupper := (hmin (adversarialPoint base)).trans hcandidateValue
  have hTm1 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub hT]
    norm_num
  have hoffset : (T - 1 : ℕ) * base.delta / 4 + base.chi ≤
      base.Delta / 4 := by
    rw [hTm1, hchi, hdelta]
    have hTone : (1 : ℝ) ≤ T := by exact_mod_cast hT
    field_simp [hTreal.ne']
    nlinarith [hDeltaPos]
  nlinarith [mul_pos hbetaPos hDeltaPos]

lemma minimizerDistance_range (data : LowerObjectiveData p d T)
    (hp : 2 < p) (hassum : LowerObjectiveAssumptions data) :
    (1 / 4 : ℝ) < minimizerDistance p data.completedOracle data.x0 ∧
      minimizerDistance p data.completedOracle data.x0 < 4 := by
  have hgapPack := V7.aboveLowerQueryGap p hp d T data hassum
  have houtPack := V7.aboveLowerOutsideGradient p hp d T data hassum
  obtain ⟨minimizer, hmin, hgap⟩ := hgapPack.2
  have hhalf := global_minimizer_norm_ge_half data hp hassum hmin
  have hfour := houtPack.2 minimizer hmin
  have hx0 : data.x0 = 0 := hassum.1.2.2.2.2.1
  let distances : Set ℝ :=
    (fun x : Point d => lpNorm p (x - data.x0)) ''
      O3.MinimizerSet data.completedOracle.value
  have hnonempty : distances.Nonempty := ⟨lpNorm p (minimizer - data.x0),
    ⟨minimizer, hmin, rfl⟩⟩
  have hbelow : BddBelow distances := ⟨0, by
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact O3.lpNorm_nonneg p (x - data.x0)⟩
  constructor
  · have hlower : (1 / 2 : ℝ) ≤ sInf distances := by
      apply le_csInf hnonempty
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      rw [hx0]
      have hsub : x - (0 : Point d) = x := by module
      change (1 / 2 : ℝ) ≤ lpNorm p (x - (0 : Point d))
      rw [hsub]
      exact global_minimizer_norm_ge_half data hp hassum hx
    change (1 / 4 : ℝ) < sInf distances
    linarith
  · have hupper : sInf distances ≤ lpNorm p (minimizer - data.x0) :=
      csInf_le hbelow ⟨minimizer, hmin, rfl⟩
    change sInf distances < 4
    rw [hx0] at hupper
    have hsub : minimizer - (0 : Point d) = minimizer := by module
    rw [hsub] at hupper
    linarith

/-- The embedding of iteration indices into their distinct selected coordinates. -/
def completionSigmaEmbedding (data : LowerCompletionData p d T)
    (hdistinct : ∀ t < T, ∀ s < t, data.sigma s ≠ data.sigma t) :
    Fin T ↪ Fin d where
  toFun i := data.sigma i.val
  inj' := by
    intro i j hij
    apply Fin.ext
    exact sigma_injective_below data hdistinct i.isLt j.isLt hij

/-- A coordinate permutation matching the selected coordinates of two completions. -/
noncomputable def completionPerm
    (data₁ data₂ : LowerCompletionData p d T)
    (hdistinct₁ : ∀ t < T, ∀ s < t, data₁.sigma s ≠ data₁.sigma t)
    (hdistinct₂ : ∀ t < T, ∀ s < t, data₂.sigma s ≠ data₂.sigma t) :
    Equiv.Perm (Fin d) :=
  Classical.choose (Equiv.Perm.exists_extending_pair
    (completionSigmaEmbedding data₁ hdistinct₁)
    (completionSigmaEmbedding data₂ hdistinct₂)
    (completionSigmaEmbedding data₁ hdistinct₁).injective
    (completionSigmaEmbedding data₂ hdistinct₂).injective)

lemma completionPerm_spec
    (data₁ data₂ : LowerCompletionData p d T)
    (hdistinct₁ : ∀ t < T, ∀ s < t, data₁.sigma s ≠ data₁.sigma t)
    (hdistinct₂ : ∀ t < T, ∀ s < t, data₂.sigma s ≠ data₂.sigma t)
    (i : Fin T) :
    completionPerm data₁ data₂ hdistinct₁ hdistinct₂ (data₁.sigma i.val) =
      data₂.sigma i.val :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    (completionSigmaEmbedding data₁ hdistinct₁)
    (completionSigmaEmbedding data₂ hdistinct₂)
    (completionSigmaEmbedding data₁ hdistinct₁).injective
    (completionSigmaEmbedding data₂ hdistinct₂).injective) i

/-- The coordinate signs matching two resisting completions, extended by one on unused
coordinates. -/
noncomputable def completionSign
    (data₁ data₂ : LowerCompletionData p d T) (k : Fin d) : ℝ :=
  if h : ∃ i : Fin T, data₂.sigma i.val = k then
    data₁.xi (Classical.choose h).val * data₂.xi (Classical.choose h).val
  else 1

lemma completionSign_at_used
    (data₁ data₂ : LowerCompletionData p d T)
    (hdistinct₂ : ∀ t < T, ∀ s < t, data₂.sigma s ≠ data₂.sigma t)
    (i : Fin T) :
    completionSign data₁ data₂ (data₂.sigma i.val) =
      data₁.xi i.val * data₂.xi i.val := by
  classical
  unfold completionSign
  rw [dite_eq_left ⟨i, rfl⟩]
  let j := Classical.choose (show ∃ j : Fin T,
    data₂.sigma j.val = data₂.sigma i.val from ⟨i, rfl⟩)
  have hj := Classical.choose_spec (show ∃ j : Fin T,
    data₂.sigma j.val = data₂.sigma i.val from ⟨i, rfl⟩)
  have hji : j = i := by
    apply Fin.ext
    exact sigma_injective_below data₂ hdistinct₂ j.isLt i.isLt hj
  have hval : (Classical.choose (show ∃ j : Fin T,
      data₂.sigma j.val = data₂.sigma i.val from ⟨i, rfl⟩)).val = i.val := by
    exact congrArg Fin.val hji
  rw [hval]

lemma completionSign_sq
    (data₁ data₂ : LowerCompletionData p d T)
    (hxi₁ : ∀ i < T, data₁.xi i = 1 ∨ data₁.xi i = -1)
    (hxi₂ : ∀ i < T, data₂.xi i = 1 ∨ data₂.xi i = -1)
    (k : Fin d) : (completionSign data₁ data₂ k) ^ (2 : ℕ) = 1 := by
  classical
  unfold completionSign
  split_ifs with h
  · let i := Classical.choose h
    have hi : i.val < T := i.isLt
    rcases hxi₁ i.val hi with h1 | h1 <;>
      rcases hxi₂ i.val hi with h2 | h2 <;> rw [h1, h2] <;> norm_num
  · norm_num

/-- The signed coordinate permutation transporting one resisting completion to another. -/
noncomputable def completionQ
    (data₁ data₂ : LowerCompletionData p d T)
    (hdistinct₁ : ∀ t < T, ∀ s < t, data₁.sigma s ≠ data₁.sigma t)
    (hdistinct₂ : ∀ t < T, ∀ s < t, data₂.sigma s ≠ data₂.sigma t)
    (x : Point d) : Point d := fun k =>
  completionSign data₁ data₂ k *
    x ((completionPerm data₁ data₂ hdistinct₁ hdistinct₂).symm k)

lemma completionQ_at_used
    (data₁ data₂ : LowerCompletionData p d T)
    (hdistinct₁ : ∀ t < T, ∀ s < t, data₁.sigma s ≠ data₁.sigma t)
    (hdistinct₂ : ∀ t < T, ∀ s < t, data₂.sigma s ≠ data₂.sigma t)
    (x : Point d) (i : Fin T) :
    completionQ data₁ data₂ hdistinct₁ hdistinct₂ x (data₂.sigma i.val) =
      (data₁.xi i.val * data₂.xi i.val) * x (data₁.sigma i.val) := by
  unfold completionQ
  rw [completionSign_at_used data₁ data₂ hdistinct₂ i]
  have hp := completionPerm_spec data₁ data₂ hdistinct₁ hdistinct₂ i
  rw [← hp, Equiv.symm_apply_apply]

lemma completionQ_lpPower
    (data₁ data₂ : LowerCompletionData p d T)
    (hdistinct₁ : ∀ t < T, ∀ s < t, data₁.sigma s ≠ data₁.sigma t)
    (hdistinct₂ : ∀ t < T, ∀ s < t, data₂.sigma s ≠ data₂.sigma t)
    (hxi₁ : ∀ i < T, data₁.xi i = 1 ∨ data₁.xi i = -1)
    (hxi₂ : ∀ i < T, data₂.xi i = 1 ∨ data₂.xi i = -1)
    (r : ℝ) (x : Point d) :
    O3.lpPower r (completionQ data₁ data₂ hdistinct₁ hdistinct₂ x) =
      O3.lpPower r x := by
  let π := completionPerm data₁ data₂ hdistinct₁ hdistinct₂
  unfold O3.lpPower
  apply Finset.sum_bij (fun k _ => π.symm k)
  · intro k _
    exact Finset.mem_univ _
  · intro i _ j _ hij
    exact π.symm.injective hij
  · intro j _
    exact ⟨π j, Finset.mem_univ _, π.symm_apply_apply j⟩
  · intro k _
    have hs := completionSign_sq data₁ data₂ hxi₁ hxi₂ k
    have hsabs : |completionSign data₁ data₂ k| = 1 := by
      have habssq : |completionSign data₁ data₂ k| ^ (2 : ℕ) = 1 := by
        rw [sq_abs, hs]
      nlinarith [abs_nonneg (completionSign data₁ data₂ k)]
    unfold completionQ
    rw [abs_mul, hsabs, one_mul]

lemma completionQ_lpNorm
    (data₁ data₂ : LowerCompletionData p d T)
    (hdistinct₁ : ∀ t < T, ∀ s < t, data₁.sigma s ≠ data₁.sigma t)
    (hdistinct₂ : ∀ t < T, ∀ s < t, data₂.sigma s ≠ data₂.sigma t)
    (hxi₁ : ∀ i < T, data₁.xi i = 1 ∨ data₁.xi i = -1)
    (hxi₂ : ∀ i < T, data₂.xi i = 1 ∨ data₂.xi i = -1)
    (r : ℝ) (x : Point d) :
    lpNorm r (completionQ data₁ data₂ hdistinct₁ hdistinct₂ x) = lpNorm r x := by
  unfold lpNorm O3.lpNorm
  rw [completionQ_lpPower data₁ data₂ hdistinct₁ hdistinct₂ hxi₁ hxi₂ r x]

lemma completionQ_pairing
    (data₁ data₂ : LowerCompletionData p d T)
    (hdistinct₁ : ∀ t < T, ∀ s < t, data₁.sigma s ≠ data₁.sigma t)
    (hdistinct₂ : ∀ t < T, ∀ s < t, data₂.sigma s ≠ data₂.sigma t)
    (hxi₁ : ∀ i < T, data₁.xi i = 1 ∨ data₁.xi i = -1)
    (hxi₂ : ∀ i < T, data₂.xi i = 1 ∨ data₂.xi i = -1)
    (s x : Point d) :
    O3.pairing (completionQ data₁ data₂ hdistinct₁ hdistinct₂ s)
      (completionQ data₁ data₂ hdistinct₁ hdistinct₂ x) = O3.pairing s x := by
  let π := completionPerm data₁ data₂ hdistinct₁ hdistinct₂
  unfold O3.pairing
  apply Finset.sum_bij (fun k _ => π.symm k)
  · intro k _
    exact Finset.mem_univ _
  · intro i _ j _ hij
    exact π.symm.injective hij
  · intro j _
    exact ⟨π j, Finset.mem_univ _, π.symm_apply_apply j⟩
  · intro k _
    have hs := completionSign_sq data₁ data₂ hxi₁ hxi₂ k
    unfold completionQ
    rw [show completionSign data₁ data₂ k *
        s ((completionPerm data₁ data₂ hdistinct₁ hdistinct₂).symm k) *
          (completionSign data₁ data₂ k *
            x ((completionPerm data₁ data₂ hdistinct₁ hdistinct₂).symm k)) =
        (completionSign data₁ data₂ k) ^ (2 : ℕ) *
          (s ((completionPerm data₁ data₂ hdistinct₁ hdistinct₂).symm k) *
            x ((completionPerm data₁ data₂ hdistinct₁ hdistinct₂).symm k)) by ring,
      hs, one_mul]

lemma completionQ_signedLpSymmetry
    (data₁ data₂ : LowerCompletionData p d T)
    (hdistinct₁ : ∀ t < T, ∀ s < t, data₁.sigma s ≠ data₁.sigma t)
    (hdistinct₂ : ∀ t < T, ∀ s < t, data₂.sigma s ≠ data₂.sigma t)
    (hxi₁ : ∀ i < T, data₁.xi i = 1 ∨ data₁.xi i = -1)
    (hxi₂ : ∀ i < T, data₂.xi i = 1 ∨ data₂.xi i = -1) :
    SignedLpSymmetry p
      (completionQ data₁ data₂ hdistinct₁ hdistinct₂)
      (completionQ data₁ data₂ hdistinct₁ hdistinct₂) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun x => completionQ_lpNorm data₁ data₂ hdistinct₁ hdistinct₂
      hxi₁ hxi₂ p x
  · exact fun s => completionQ_lpNorm data₁ data₂ hdistinct₁ hdistinct₂
      hxi₁ hxi₂ (conjugateExponent p) s
  · exact fun s x => completionQ_pairing data₁ data₂ hdistinct₁ hdistinct₂
      hxi₁ hxi₂ s x

lemma completion_partialG_eq
    (data₁ data₂ : LowerCompletionData p d T) (hT : 1 ≤ T)
    (hdelta : data₁.delta = data₂.delta)
    (hsteps₁ : ∀ t < T,
      (∀ s < t, data₁.sigma s ≠ data₁.sigma t) ∧
      (data₁.xi t = 1 ∨ data₁.xi t = -1) ∧
      ResistingMaximumAt data₁ t)
    (hsteps₂ : ∀ t < T,
      (∀ s < t, data₂.sigma s ≠ data₂.sigma t) ∧
      (data₂.xi t = 1 ∨ data₂.xi t = -1) ∧
      ResistingMaximumAt data₂ t) (x : Point d) :
    data₂.partialG (T - 1)
      (completionQ data₁ data₂ (fun t ht => (hsteps₁ t ht).1)
        (fun t ht => (hsteps₂ t ht).1) x) =
      data₁.partialG (T - 1) x := by
  have hlast : T - 1 < T := by omega
  let Q := completionQ data₁ data₂ (fun t ht => (hsteps₁ t ht).1)
    (fun t ht => (hsteps₂ t ht).1)
  have hpiece : ∀ i < T,
      data₂.xi i * Q x (data₂.sigma i) - (i : ℝ) * data₂.delta =
        data₁.xi i * x (data₁.sigma i) - (i : ℝ) * data₁.delta := by
    intro i hi
    have hQ := completionQ_at_used data₁ data₂
      (fun t ht => (hsteps₁ t ht).1) (fun t ht => (hsteps₂ t ht).1)
      x ⟨i, hi⟩
    change Q x (data₂.sigma i) =
      (data₁.xi i * data₂.xi i) * x (data₁.sigma i) at hQ
    rw [hQ, ← hdelta]
    rcases (hsteps₁ i hi).2.1 with h1 | h1 <;>
      rcases (hsteps₂ i hi).2.1 with h2 | h2 <;> rw [h1, h2] <;> ring
  apply le_antisymm
  · obtain ⟨i, hi, hiEq⟩ := ((hsteps₂ (T - 1) hlast).2.2 (Q x)).2
    have hiT : i < T := lt_of_le_of_lt hi hlast
    rw [hiEq, hpiece i hiT]
    exact ((hsteps₁ (T - 1) hlast).2.2 x).1 i hi
  · obtain ⟨i, hi, hiEq⟩ := ((hsteps₁ (T - 1) hlast).2.2 x).2
    have hiT : i < T := lt_of_le_of_lt hi hlast
    rw [hiEq, ← hpiece i hiT]
    exact ((hsteps₂ (T - 1) hlast).2.2 (Q x)).1 i hi

lemma completion_partialH_eq
    (data₁ data₂ : LowerCompletionData p d T) (hT : 1 ≤ T)
    (hdelta : data₁.delta = data₂.delta)
    (hsteps₁ : ∀ t < T,
      (∀ s < t, data₁.sigma s ≠ data₁.sigma t) ∧
      (data₁.xi t = 1 ∨ data₁.xi t = -1) ∧
      ResistingMaximumAt data₁ t ∧
      (∀ x, data₁.partialH t x =
        max (data₁.partialG t x / 2) (lpNorm p x - 3 / 2)))
    (hsteps₂ : ∀ t < T,
      (∀ s < t, data₂.sigma s ≠ data₂.sigma t) ∧
      (data₂.xi t = 1 ∨ data₂.xi t = -1) ∧
      ResistingMaximumAt data₂ t ∧
      (∀ x, data₂.partialH t x =
        max (data₂.partialG t x / 2) (lpNorm p x - 3 / 2)))
    (x : Point d) :
    data₂.partialH (T - 1)
      (completionQ data₁ data₂ (fun t ht => (hsteps₁ t ht).1)
        (fun t ht => (hsteps₂ t ht).1) x) =
      data₁.partialH (T - 1) x := by
  have hlast : T - 1 < T := by omega
  let Q := completionQ data₁ data₂ (fun t ht => (hsteps₁ t ht).1)
    (fun t ht => (hsteps₂ t ht).1)
  rw [(hsteps₂ (T - 1) hlast).2.2.2, (hsteps₁ (T - 1) hlast).2.2.2]
  rw [completion_partialG_eq data₁ data₂ hT hdelta
    (fun t ht => ⟨(hsteps₁ t ht).1, (hsteps₁ t ht).2.1,
      (hsteps₁ t ht).2.2.1⟩)
    (fun t ht => ⟨(hsteps₂ t ht).1, (hsteps₂ t ht).2.1,
      (hsteps₂ t ht).2.2.1⟩) x]
  rw [completionQ_lpNorm data₁ data₂
    (fun t ht => (hsteps₁ t ht).1) (fun t ht => (hsteps₂ t ht).1)
    (fun t ht => (hsteps₁ t ht).2.1) (fun t ht => (hsteps₂ t ht).2.1) p x]

lemma completionQ_surjective
    (data₁ data₂ : LowerCompletionData p d T)
    (hdistinct₁ : ∀ t < T, ∀ s < t, data₁.sigma s ≠ data₁.sigma t)
    (hdistinct₂ : ∀ t < T, ∀ s < t, data₂.sigma s ≠ data₂.sigma t)
    (hxi₁ : ∀ i < T, data₁.xi i = 1 ∨ data₁.xi i = -1)
    (hxi₂ : ∀ i < T, data₂.xi i = 1 ∨ data₂.xi i = -1) :
    Function.Surjective (completionQ data₁ data₂ hdistinct₁ hdistinct₂) := by
  intro y
  let π := completionPerm data₁ data₂ hdistinct₁ hdistinct₂
  let x : Point d := fun j =>
    completionSign data₁ data₂ (π j) * y (π j)
  refine ⟨x, ?_⟩
  funext k
  have hs := completionSign_sq data₁ data₂ hxi₁ hxi₂ k
  unfold completionQ
  dsimp [x, π]
  rw [Equiv.apply_symm_apply]
  rw [show completionSign data₁ data₂ k *
      (completionSign data₁ data₂ k * y k) =
      (completionSign data₁ data₂ k) ^ (2 : ℕ) * y k by ring,
    hs, one_mul]

lemma completedValue_completionQ_eq
    (data₁ data₂ : LowerObjectiveData p d T) (hp : 2 < p)
    (hassum₁ : LowerObjectiveAssumptions data₁)
    (hassum₂ : LowerObjectiveAssumptions data₂)
    (hkernelEq : data₁.kernel = data₂.kernel) (x : Point d) :
    let base₁ := data₁.toLowerCompletionData
    let base₂ := data₂.toLowerCompletionData
    let Q := completionQ base₁ base₂
      (fun t ht => (hassum₁.1.2.2.2.2.2.2.2.2.2.2.2.1 t ht).1)
      (fun t ht => (hassum₂.1.2.2.2.2.2.2.2.2.2.2.2.1 t ht).1)
    data₂.completedOracle.value (Q x) = data₁.completedOracle.value x := by
  dsimp only
  let base₁ := data₁.toLowerCompletionData
  let base₂ := data₂.toLowerCompletionData
  rcases hassum₁.1 with
    ⟨hp₁, hd₁, hT₁, hTd₁, hx0₁, hkernel₁, hDelta₁, hdelta₁,
      hchi₁, hbeta₁, hqueries₁, hsteps₁, hcompletedValue₁, hcompletedGradient₁⟩
  rcases hassum₂.1 with
    ⟨hp₂, hd₂, hT₂, hTd₂, hx0₂, hkernel₂, hDelta₂, hdelta₂,
      hchi₂, hbeta₂, hqueries₂, hsteps₂, hcompletedValue₂, hcompletedGradient₂⟩
  have hDeltaEq : base₁.Delta = base₂.Delta := hDelta₁.trans hDelta₂.symm
  have hdeltaEq : base₁.delta = base₂.delta := by rw [hdelta₁, hdelta₂, hDeltaEq]
  have hchiEq : base₁.chi = base₂.chi := by rw [hchi₁, hchi₂, hdeltaEq]
  have hbetaEq : base₁.beta = base₂.beta := by
    rw [hbeta₁, hbeta₂, hchiEq, hkernelEq]
  have hlast : T - 1 < T := by omega
  let distinct₁ := fun t ht => (hsteps₁ t ht).1
  let distinct₂ := fun t ht => (hsteps₂ t ht).1
  let Q := completionQ base₁ base₂ distinct₁ distinct₂
  have hshort₁ : ∀ t < T,
      (∀ s < t, base₁.sigma s ≠ base₁.sigma t) ∧
      (base₁.xi t = 1 ∨ base₁.xi t = -1) ∧
      ResistingMaximumAt base₁ t ∧
      (∀ x, base₁.partialH t x =
        max (base₁.partialG t x / 2) (lpNorm p x - 3 / 2)) := by
    intro t ht
    exact ⟨(hsteps₁ t ht).1, (hsteps₁ t ht).2.2.2.1,
      (hsteps₁ t ht).2.2.2.2.2.1, (hsteps₁ t ht).2.2.2.2.2.2.1⟩
  have hshort₂ : ∀ t < T,
      (∀ s < t, base₂.sigma s ≠ base₂.sigma t) ∧
      (base₂.xi t = 1 ∨ base₂.xi t = -1) ∧
      ResistingMaximumAt base₂ t ∧
      (∀ x, base₂.partialH t x =
        max (base₂.partialG t x / 2) (lpNorm p x - 3 / 2)) := by
    intro t ht
    exact ⟨(hsteps₂ t ht).1, (hsteps₂ t ht).2.2.2.1,
      (hsteps₂ t ht).2.2.2.2.2.1, (hsteps₂ t ht).2.2.2.2.2.2.1⟩
  have hHtransform : ∀ z, base₂.partialH (T - 1) (Q z) =
      base₁.partialH (T - 1) z :=
    fun z => completion_partialH_eq base₁ base₂ hT₁ hdeltaEq hshort₁ hshort₂ z
  let shortSteps₂ : ∀ s < T,
      (base₂.xi s = 1 ∨ base₂.xi s = -1) ∧ ResistingMaximumAt base₂ s :=
    fun s hs => ⟨(hsteps₂ s hs).2.2.2.1, (hsteps₂ s hs).2.2.2.2.2.1⟩
  have hpartial₂ := partialH_convex_oneLipschitz base₂ (by linarith) hlast
    shortSteps₂ (hsteps₂ (T - 1) hlast).2.2.2.2.2.2.1
  have hsym : SignedLpSymmetry p Q Q :=
    completionQ_signedLpSymmetry base₁ base₂ distinct₁ distinct₂
      (fun t ht => (hsteps₁ t ht).2.2.2.1)
      (fun t ht => (hsteps₂ t ht).2.2.2.1)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hequiv⟩ := hkernel₂
  have heqv := hequiv base₂.chi (by rw [← hchiEq, hchi₁, hdelta₁, hDelta₁]; positivity)
    (base₂.partialH (T - 1)) Q Q hpartial₂.1 hpartial₂.2 hsym x
  have hfun : (fun z => base₂.partialH (T - 1) (Q z)) =
      base₁.partialH (T - 1) := funext hHtransform
  rw [hfun] at heqv
  rw [hcompletedValue₂, hcompletedValue₁]
  rw [← heqv, ← hkernelEq, ← hchiEq, ← hbetaEq]

lemma completion_minimizerDistance_eq
    (data₁ data₂ : LowerObjectiveData p d T) (hp : 2 < p)
    (hassum₁ : LowerObjectiveAssumptions data₁)
    (hassum₂ : LowerObjectiveAssumptions data₂)
    (hkernelEq : data₁.kernel = data₂.kernel) :
    minimizerDistance p data₁.completedOracle data₁.x0 =
      minimizerDistance p data₂.completedOracle data₂.x0 := by
  let base₁ := data₁.toLowerCompletionData
  let base₂ := data₂.toLowerCompletionData
  have hcomp₁ := hassum₁.1
  have hcomp₂ := hassum₂.1
  rcases hcomp₁ with
    ⟨hp₁, hd₁, hT₁, hTd₁, hx0₁, hkernel₁, hDelta₁, hdelta₁,
      hchi₁, hbeta₁, hqueries₁, hsteps₁, hcompletedValue₁, hcompletedGradient₁⟩
  rcases hcomp₂ with
    ⟨hp₂, hd₂, hT₂, hTd₂, hx0₂, hkernel₂, hDelta₂, hdelta₂,
      hchi₂, hbeta₂, hqueries₂, hsteps₂, hcompletedValue₂, hcompletedGradient₂⟩
  let distinct₁ := fun t ht => (hsteps₁ t ht).1
  let distinct₂ := fun t ht => (hsteps₂ t ht).1
  let Q := completionQ base₁ base₂ distinct₁ distinct₂
  have hQvalue : ∀ x, data₂.completedOracle.value (Q x) =
      data₁.completedOracle.value x := by
    intro x
    simpa [Q, distinct₁, distinct₂, base₁, base₂] using
      completedValue_completionQ_eq data₁ data₂ hp hassum₁ hassum₂ hkernelEq x
  have hQsurj : Function.Surjective Q :=
    completionQ_surjective base₁ base₂ distinct₁ distinct₂
      (fun t ht => (hsteps₁ t ht).2.2.2.1)
      (fun t ht => (hsteps₂ t ht).2.2.2.1)
  have hQnorm : ∀ x, lpNorm p (Q x) = lpNorm p x := fun x =>
    completionQ_lpNorm base₁ base₂ distinct₁ distinct₂
      (fun t ht => (hsteps₁ t ht).2.2.2.1)
      (fun t ht => (hsteps₂ t ht).2.2.2.1) p x
  have hminiff : ∀ x, x ∈ O3.MinimizerSet data₁.completedOracle.value ↔
      Q x ∈ O3.MinimizerSet data₂.completedOracle.value := by
    intro x
    constructor
    · intro hx y
      obtain ⟨z, rfl⟩ := hQsurj y
      rw [hQvalue, hQvalue]
      exact hx z
    · intro hx z
      have hz := hx (Q z)
      rw [hQvalue, hQvalue] at hz
      exact hz
  unfold minimizerDistance O3.minimizerDistance
  rw [hx0₁, hx0₂]
  congr 1
  ext r
  constructor
  · intro hr
    rcases hr with ⟨x, hx, rfl⟩
    refine ⟨Q x, (hminiff x).1 hx, ?_⟩
    have hsubQ : Q x - (0 : Point d) = Q x := by module
    have hsubX : x - (0 : Point d) = x := by module
    change lpNorm p (Q x - (0 : Point d)) = lpNorm p (x - (0 : Point d))
    rw [hsubQ, hsubX, hQnorm]
  · intro hr
    rcases hr with ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := hQsurj y
    refine ⟨x, (hminiff x).2 hy, ?_⟩
    have hsubQ : Q x - (0 : Point d) = Q x := by module
    have hsubX : x - (0 : Point d) = x := by module
    change lpNorm p (x - (0 : Point d)) = lpNorm p (Q x - (0 : Point d))
    rw [hsubQ, hsubX, hQnorm]

/-- Frozen S5-E: the optimizer radius is independent of the chronological
completion because every completion is a signed-permutation isometric image
of every other one. -/
theorem _root_.V7.aboveLowerOptimizerRadius : AboveLowerOptimizerRadiusStatement := by
  intro p hp d T hd hT hTd kernel hkernel
  by_cases hex : ∃ data : LowerObjectiveData p d T,
      data.kernel = kernel ∧ LowerObjectiveAssumptions data
  · let data₀ := Classical.choose hex
    have hdata₀ := Classical.choose_spec hex
    let rT := minimizerDistance p data₀.completedOracle data₀.x0
    have hrange := minimizerDistance_range data₀ hp hdata₀.2
    refine ⟨rT, hrange.1, hrange.2, ?_⟩
    intro data hdataKernel hassum
    dsimp [rT]
    exact completion_minimizerDistance_eq data₀ data hp hdata₀.2 hassum
      (hdata₀.1.trans hdataKernel.symm)
  · refine ⟨1, by norm_num, by norm_num, ?_⟩
    intro data hdataKernel hassum
    exact (hex ⟨data, hdataKernel, hassum⟩).elim

end V7.Stage5AboveTwoLowerS5A2Envelope
