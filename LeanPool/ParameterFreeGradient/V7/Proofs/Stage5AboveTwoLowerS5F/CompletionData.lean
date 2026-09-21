/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.PrefixSync

/-!
The recursive resisting prefixes assemble into valid completed lower-bound data.
-/

namespace V7.Stage5AboveTwoLowerS5F

open Stage5AboveTwoLower
open Stage5AboveTwoLowerS5A2Envelope

lemma piece_eq_global (P : PrefixParameters p d T) (t i : ℕ) (hit : i ≤ t)
    (x : Point d) :
    piece P (prefixState P t) t i x =
      xi P i * x (sigma P i) - (i : ℝ) * P.delta := by
  dsimp [piece]
  by_cases hi : i < t
  · have hsiglen : i < (prefixState P t).sigmaPrefix.length := by
      simpa [(prefix_lengths P t).1] using hi
    have hxilen : i < (prefixState P t).xiPrefix.length := by
      simpa [(prefix_lengths P t).2.1] using hi
    rw [List.getD_append _ _ _ _ hxilen, List.getD_append _ _ _ _ hsiglen]
    rw [prefix_xi_getD hi, prefix_sigma_getD hi]
  · have hitEq : i = t := by omega
    subst i
    have hsiglen := (prefix_lengths P t).1
    have hxilen := (prefix_lengths P t).2.1
    rw [List.getD_append_right _ _ _ _ hxilen.le,
      List.getD_append_right _ _ _ _ hsiglen.le]
    rw [hxilen, hsiglen]
    simp [xi, sigma]

lemma stepG_resisting (P : PrefixParameters p d T) (t : ℕ) :
    ∀ x,
      (∀ i ≤ t, xi P i * x (sigma P i) - (i : ℝ) * P.delta ≤
        partialG P t x) ∧
      ∃ i ≤ t,
        partialG P t x =
          xi P i * x (sigma P i) - (i : ℝ) * P.delta := by
  intro x
  let values := (Finset.range (t + 1)).image
    (fun i => piece P (prefixState P t) t i x)
  have hne : values.Nonempty := by
    refine ⟨piece P (prefixState P t) t 0 x, Finset.mem_image.mpr ?_⟩
    exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ t), rfl⟩
  constructor
  · intro i hit
    rw [← piece_eq_global P t i hit]
    apply Finset.le_max' values
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hit), rfl⟩
  · have hmem := Finset.max'_mem values hne
    rcases Finset.mem_image.mp hmem with ⟨i, hi, hpiece⟩
    have hit : i ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    refine ⟨i, hit, ?_⟩
    have heqmax : partialG P t x = values.max' hne := by rfl
    rw [heqmax]
    rw [← piece_eq_global P t i hit]
    exact hpiece.symm

lemma sigma_step_spec (P : PrefixParameters p d T) {t : ℕ} (ht : t < T) :
    (∀ s < t, sigma P s ≠ sigma P t) ∧
      (sigma P t).val < T ∧
      ∀ j : Fin d, j.val < T → (∀ s < t, sigma P s ≠ j) →
        |query P t j| ≤ |query P t (sigma P t)| := by
  have hchoose := Classical.choose_spec
    (exists_unused_max_coordinate P.T_le_d ht
      (priorSigma P (prefixState P t)) (query P t))
  have hsigma : sigma P t = Classical.choose
      (exists_unused_max_coordinate P.T_le_d ht
        (priorSigma P (prefixState P t)) (query P t)) := by
    simp [sigma, stepSigma, ht, query]
  rw [hsigma]
  refine ⟨?_, hchoose.1, ?_⟩
  · intro s hs
    rw [← prefix_sigma_getD (P := P) hs]
    exact hchoose.2.1 s hs
  · intro j hj hunused
    apply hchoose.2.2 j hj
    intro s hs
    change (prefixState P t).sigmaPrefix.getD s (firstCoordinate P) ≠ j
    rw [prefix_sigma_getD (P := P) hs]
    exact hunused s hs

lemma xi_step_spec (P : PrefixParameters p d T) (t : ℕ) :
    (xi P t = 1 ∨ xi P t = -1) ∧
      xi P t * query P t (sigma P t) = |query P t (sigma P t)| := by
  simpa [xi, stepXi, query, sigma] using
    resistingSign_spec (query P t (sigma P t))

/-- The final scaled smooth oracle obtained from the last partial resisting objective. -/
noncomputable def completedOracle (P : PrefixParameters p d T) : PairOracle d :=
  { value := fun x => P.beta *
      (P.kernel.smooth P.chi (partialH P (T - 1))).value x
    gradient := fun x => P.beta •
      (P.kernel.smooth P.chi (partialH P (T - 1))).gradient x }

/-- The recursively constructed prefixes packaged as completed lower-bound data. -/
noncomputable def completionData (P : PrefixParameters p d T) (Delta : ℝ) :
    LowerCompletionData p d T :=
  { algorithm := P.algorithm
    x0 := 0
    kernel := P.kernel
    Delta := Delta
    delta := P.delta
    chi := P.chi
    beta := P.beta
    partialG := partialG P
    partialH := partialH P
    partialOracle := partialOracle P
    completedOracle := completedOracle P
    queries := query P
    sigma := sigma P
    xi := xi P }

theorem completionData_assumptions (P : PrefixParameters p d T) (Delta : ℝ)
    (hp : 2 < p) (hd : 2 ≤ d)
    (hkernel : SmoothingKernelAssumptions P.kernel)
    (hDelta : Delta = (T : ℝ) ^ (-1 / p))
    (hdelta : P.delta = Delta / (2 * T))
    (hchi : P.chi = P.delta / 2)
    (hbeta : P.beta = P.chi / P.kernel.Mpd) :
    LowerCompletionAssumptions (completionData P Delta) := by
  refine ⟨hp, hd, P.T_pos, P.T_le_d, rfl, hkernel,
    hDelta, hdelta, hchi, hbeta, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact query_chronology P t
  · intro t ht
    obtain ⟨hsigma, hval, hmax⟩ := sigma_step_spec P ht
    obtain ⟨hxi, hsign⟩ := xi_step_spec P t
    refine ⟨hsigma, hval, hmax, hxi, hsign, ?_, ?_, ?_, ?_⟩
    · exact stepG_resisting P t
    · intro x
      rfl
    · intro x
      rfl
    · intro x
      rfl
  · intro x
    rfl
  · intro x
    rfl

end V7.Stage5AboveTwoLowerS5F
