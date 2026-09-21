/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import Mathlib.Data.List.GetD
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.PhysicalLower

namespace V7.Stage5AboveTwoLowerS5F

open Stage5AboveTwoLower
open Stage5AboveTwoLowerS5A2Envelope

structure PrefixParameters (p : ℝ) (d T : ℕ) where
  algorithm : DeterministicExactPairAlgorithm d
  kernel : SmoothingKernelData p d
  delta : ℝ
  chi : ℝ
  beta : ℝ
  T_pos : 0 < T
  T_le_d : T ≤ d

def firstCoordinate (P : PrefixParameters p d T) : Fin d :=
  ⟨0, lt_of_lt_of_le P.T_pos P.T_le_d⟩

structure ResistingPrefixState (d : ℕ) where
  sigmaPrefix : List (Fin d)
  xiPrefix : List ℝ
  obsPrefix : List (Observation d)

def initialState (d : ℕ) : ResistingPrefixState d := ⟨[], [], []⟩

def priorSigma (P : PrefixParameters p d T) (state : ResistingPrefixState d)
    (s : ℕ) : Fin d :=
  state.sigmaPrefix.getD s (firstCoordinate P)

noncomputable def stepQuery (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) : Point d :=
  if t = 0 then 0 else P.algorithm.nextQuery 0 state.obsPrefix

noncomputable def stepSigma (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) : Fin d :=
  if ht : t < T then
    Classical.choose
      (exists_unused_max_coordinate P.T_le_d ht (priorSigma P state)
        (stepQuery P t state))
  else firstCoordinate P

noncomputable def stepXi (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) : ℝ :=
  resistingSign ((stepQuery P t state) (stepSigma P t state))

noncomputable def piece (P : PrefixParameters p d T) (state : ResistingPrefixState d)
    (t i : ℕ) (x : Point d) : ℝ :=
  let sigmas := state.sigmaPrefix ++ [stepSigma P t state]
  let xis := state.xiPrefix ++ [stepXi P t state]
  xis.getD i 0 * x (sigmas.getD i (firstCoordinate P)) - (i : ℝ) * P.delta

noncomputable def stepG (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) (x : Point d) : ℝ :=
  let values := (Finset.range (t + 1)).image (fun i => piece P state t i x)
  values.max' (by
    refine ⟨piece P state t 0 x, Finset.mem_image.mpr ?_⟩
    exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ t), rfl⟩)

noncomputable def stepH (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) (x : Point d) : ℝ :=
  max (stepG P t state x / 2) (lpNorm p x - 3 / 2)

noncomputable def stepOracle (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) : PairOracle d :=
  { value := fun x => P.beta * (P.kernel.smooth P.chi (stepH P t state)).value x
    gradient := fun x => P.beta • (P.kernel.smooth P.chi (stepH P t state)).gradient x }

noncomputable def advance (P : PrefixParameters p d T) (t : ℕ)
    (state : ResistingPrefixState d) : ResistingPrefixState d :=
  { sigmaPrefix := state.sigmaPrefix ++ [stepSigma P t state]
    xiPrefix := state.xiPrefix ++ [stepXi P t state]
    obsPrefix := state.obsPrefix ++
      [(stepOracle P t state).observe (stepQuery P t state)] }

noncomputable def prefixState (P : PrefixParameters p d T) :
    ℕ → ResistingPrefixState d
  | 0 => initialState d
  | t + 1 => advance P t (prefixState P t)

noncomputable def query (P : PrefixParameters p d T) (t : ℕ) : Point d :=
  stepQuery P t (prefixState P t)

noncomputable def sigma (P : PrefixParameters p d T) (t : ℕ) : Fin d :=
  stepSigma P t (prefixState P t)

noncomputable def xi (P : PrefixParameters p d T) (t : ℕ) : ℝ :=
  stepXi P t (prefixState P t)

noncomputable def partialG (P : PrefixParameters p d T) (t : ℕ) : Point d → ℝ :=
  stepG P t (prefixState P t)

noncomputable def partialH (P : PrefixParameters p d T) (t : ℕ) : Point d → ℝ :=
  stepH P t (prefixState P t)

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
