/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import Mathlib.Data.List.GetD
public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.PhysicalLower

/-!
The recursive state construction of the resisting coordinates, signs, and partial smooth
oracles.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5F

open Stage5AboveTwoLower
open Stage5AboveTwoLowerS5A2Envelope

/-- The fixed algorithm, kernel, scales, and horizon bounds used to build resisting prefixes. -/
structure PrefixParameters (p : ℝ) (d T : ℕ) where
  /-- The deterministic algorithm challenged by the prefix construction. -/
  algorithm : DeterministicExactPairAlgorithm d
  /-- The smoothing kernel applied to each partial objective. -/
  kernel : SmoothingKernelData p d
  /-- The offset between successive affine pieces. -/
  delta : ℝ
  /-- The smoothing scale of the partial objectives. -/
  chi : ℝ
  /-- The common scale multiplying the smooth oracle values and gradients. -/
  beta : ℝ
  T_pos : 0 < T
  T_le_d : T ≤ d

/-- The zero coordinate, available because the positive horizon fits inside the dimension. -/
def firstCoordinate (P : PrefixParameters p d T) : Fin d :=
  ⟨0, lt_of_lt_of_le P.T_pos P.T_le_d⟩

/-- The coordinates, signs, and observations selected by a finite resisting prefix. -/
structure ResistingPrefixState (d : ℕ) where
  /-- The previously selected distinct coordinates. -/
  sigmaPrefix : List (Fin d)
  /-- The signs assigned to the selected coordinates. -/
  xiPrefix : List ℝ
  /-- The observations already returned to the algorithm. -/
  obsPrefix : List (Observation d)

/-- The empty state before any resisting coordinate or observation is chosen. -/
def initialState (d : ℕ) : ResistingPrefixState d := ⟨[], [], []⟩

/-- A previously selected coordinate, with zero as the out-of-range default. -/
def priorSigma (P : PrefixParameters p d T) (state : ResistingPrefixState d)
    (s : ℕ) : Fin d :=
  state.sigmaPrefix.getD s (firstCoordinate P)

/-- The next algorithm query, with the first query fixed at the origin. -/
noncomputable def stepQuery (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) : Point d :=
  if t = 0 then 0 else P.algorithm.nextQuery 0 state.obsPrefix

/-- An unused coordinate maximizing the current query magnitude, chosen before the horizon. -/
noncomputable def stepSigma (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) : Fin d :=
  if ht : t < T then
    Classical.choose
      (exists_unused_max_coordinate P.T_le_d ht (priorSigma P state)
        (stepQuery P t state))
  else firstCoordinate P

/-- The sign aligned with the current query at the newly selected coordinate. -/
noncomputable def stepXi (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) : ℝ :=
  resistingSign ((stepQuery P t state) (stepSigma P t state))

/-- An indexed signed-coordinate affine piece after appending the current resisting choice. -/
noncomputable def piece (P : PrefixParameters p d T) (state : ResistingPrefixState d)
    (t i : ℕ) (x : Point d) : ℝ :=
  let sigmas := state.sigmaPrefix ++ [stepSigma P t state]
  let xis := state.xiPrefix ++ [stepXi P t state]
  xis.getD i 0 * x (sigmas.getD i (firstCoordinate P)) - (i : ℝ) * P.delta

/-- The maximum of the affine pieces selected through the current step. -/
noncomputable def stepG (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) (x : Point d) : ℝ :=
  let values := (Finset.range (t + 1)).image (fun i => piece P state t i x)
  values.max' (by
    refine ⟨piece P state t 0 x, Finset.mem_image.mpr ?_⟩
    exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ t), rfl⟩)

/-- The resisting maximum combined with a radial term to ensure coercivity. -/
noncomputable def stepH (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) (x : Point d) : ℝ :=
  max (stepG P t state x / 2) (lpNorm p x - 3 / 2)

/-- The scaled smooth oracle associated with the current regularized resisting objective. -/
noncomputable def stepOracle (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) : PairOracle d :=
  { value := fun x => P.beta * (P.kernel.smooth P.chi (stepH P t state)).value x
    gradient := fun x => P.beta • (P.kernel.smooth P.chi (stepH P t state)).gradient x }

/-- The prefix state after appending the selected coordinate, sign, and oracle observation. -/
noncomputable def advance (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) : ResistingPrefixState d :=
  { sigmaPrefix := state.sigmaPrefix ++ [stepSigma P t state]
    xiPrefix := state.xiPrefix ++ [stepXi P t state]
    obsPrefix := state.obsPrefix ++
      [(stepOracle P t state).observe (stepQuery P t state)] }

/-- The recursively generated resisting prefix state. -/
noncomputable def prefixState (P : PrefixParameters p d T) :
    ℕ → ResistingPrefixState d
  | 0 => initialState d
  | t + 1 => advance P t (prefixState P t)

/-- The query made at step `t` of the recursively generated resisting construction. -/
noncomputable def query (P : PrefixParameters p d T) (t : ℕ) : Point d :=
  stepQuery P t (prefixState P t)

/-- The coordinate selected at step `t` of the resisting construction. -/
noncomputable def sigma (P : PrefixParameters p d T) (t : ℕ) : Fin d :=
  stepSigma P t (prefixState P t)

/-- The sign selected at step `t` of the resisting construction. -/
noncomputable def xi (P : PrefixParameters p d T) (t : ℕ) : ℝ :=
  stepXi P t (prefixState P t)

/-- The resisting affine maximum at prefix length `t + 1`. -/
noncomputable def partialG (P : PrefixParameters p d T) (t : ℕ) : Point d → ℝ :=
  stepG P t (prefixState P t)

/-- The regularized nonsmooth objective at prefix length `t + 1`. -/
noncomputable def partialH (P : PrefixParameters p d T) (t : ℕ) : Point d → ℝ :=
  stepH P t (prefixState P t)

/-- The scaled smoothed oracle at prefix length `t + 1`. -/
noncomputable def partialOracle (P : PrefixParameters p d T) (t : ℕ) : PairOracle d :=
  stepOracle P t (prefixState P t)

@[simp] lemma prefixState_zero (P : PrefixParameters p d T) :
    prefixState P 0 = initialState d := rfl

@[simp] lemma prefixState_succ (P : PrefixParameters p d T) (t : ℕ) :
    prefixState P (t + 1) = advance P t (prefixState P t) := rfl

lemma prefix_lengths (P : PrefixParameters p d T) (t : ℕ) :
    (prefixState P t).sigmaPrefix.length = t ∧
    (prefixState P t).xiPrefix.length = t ∧
    (prefixState P t).obsPrefix.length = t := by
  induction t with
  | zero => simp [prefixState, initialState]
  | succ t ih =>
      simp [prefixState, advance, ih.1, ih.2.1, ih.2.2]

lemma prefix_sigma_getD {P : PrefixParameters p d T} {s t : ℕ} (hst : s < t) :
    (prefixState P t).sigmaPrefix.getD s (firstCoordinate P) = sigma P s := by
  induction t generalizing s with
  | zero => omega
  | succ t ih =>
      rw [prefixState_succ]
      simp only [advance]
      by_cases hst' : s < t
      · have hslen : s < (prefixState P t).sigmaPrefix.length := by
          simpa [(prefix_lengths P t).1] using hst'
        rw [List.getD_append _ _ _ _ hslen]
        exact ih hst'
      · have hstEq : s = t := by omega
        subst s
        have hlen := (prefix_lengths P t).1
        rw [List.getD_append_right _ _ _ _ hlen.le]
        rw [hlen]
        simp [sigma]

lemma prefix_xi_getD {P : PrefixParameters p d T} {s t : ℕ} (hst : s < t) :
    (prefixState P t).xiPrefix.getD s 0 = xi P s := by
  induction t generalizing s with
  | zero => omega
  | succ t ih =>
      rw [prefixState_succ]
      simp only [advance]
      by_cases hst' : s < t
      · have hslen : s < (prefixState P t).xiPrefix.length := by
          simpa [(prefix_lengths P t).2.1] using hst'
        rw [List.getD_append _ _ _ _ hslen]
        exact ih hst'
      · have hstEq : s = t := by omega
        subst s
        have hlen := (prefix_lengths P t).2.1
        rw [List.getD_append_right _ _ _ _ hlen.le]
        rw [hlen]
        simp [xi]

end V7.Stage5AboveTwoLowerS5F
