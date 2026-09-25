/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.LowerTheorem

/-!
A causal local trial induces a deterministic exact-pair algorithm with its cached query
charged.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5F

/-- The trial state obtained by replaying a recorded observation list. -/
def replayTrial (trial : LocalTrial d) : trial.State → List (Observation d) → trial.State
  | state, [] => state
  | state, obs :: rest =>
      match trial.action state with
      | .query _ next => replayTrial trial (next obs) rest
      | .finish _ _ => state

/-- The next point requested by a trial state, or a fallback if the trial has finished. -/
def trialActionPoint (trial : LocalTrial d) (state : trial.State) (fallback : Point d) :
    Point d :=
  match trial.action state with
  | .query point _ => point
  | .finish _ _ => fallback

/-- The deterministic algorithm induced by a local trial with its cached query charged. -/
noncomputable def chargedTrialAlgorithm (p : ℝ) (trial : LocalTrial d) (M D eps : ℝ) :
    DeterministicExactPairAlgorithm d :=
  { nextQuery := fun x0 history =>
      match history with
      | [] => x0
      | cached :: rest =>
          trialActionPoint trial
            (replayTrial trial (trial.initial M D ⟨cached⟩) rest) x0
    output := fun x0 history =>
      if h : ∃ obs ∈ history,
          lpNorm (conjugateExponent p) obs.gradient ≤ eps then
        (Classical.choose h).point
      else x0 }

/-- The observation list follows the query actions of the trial from the supplied state. -/
def TrialGeneratedFrom (trial : LocalTrial d) :
    trial.State → List (Observation d) → Prop
  | _, [] => True
  | state, obs :: rest =>
      match _h : trial.action state with
      | .query point next => obs.point = point ∧ TrialGeneratedFrom trial (next obs) rest
      | .finish _ _ => False

lemma runFuel_suffix (trial : LocalTrial d) (oracle : PairOracle d)
    {fuel : ℕ} {state : trial.State} {history : List (Observation d)}
    {report : TrialReport d}
    (hrun : trial.runFuel oracle fuel state history = some report) :
    ∃ suffix,
      report.trace = history ++ suffix ∧
      TrialGeneratedFrom trial state suffix ∧
      TraceExact oracle suffix := by
  induction fuel generalizing state history with
  | zero => simp [LocalTrial.runFuel] at hrun
  | succ fuel ih =>
      rw [LocalTrial.runFuel] at hrun
      split at hrun
      next guards outcome heq =>
        have hreport : report = ⟨history, guards, outcome⟩ := Option.some.inj hrun.symm
        subst report
        refine ⟨[], by simp, by simp [TrialGeneratedFrom], ?_⟩
        simp [TraceExact]
      next point nextState heq =>
        let obs := oracle.observe point
        obtain ⟨suffix, htrace, hgenerated, hexact⟩ :=
          ih (state := nextState obs) (history := history ++ [obs]) hrun
        refine ⟨obs :: suffix, ?_, ?_, ?_⟩
        · rw [htrace]
          simp [List.append_assoc, obs]
        · simp only [TrialGeneratedFrom]
          rw [heq]
          exact ⟨rfl, hgenerated⟩
        · intro o ho
          rcases List.mem_cons.mp ho with rfl | ho
          · rfl
          · exact hexact o ho

lemma generatedFrom_action_at (trial : LocalTrial d) {state : trial.State}
    {trace : List (Observation d)} (fallback : Point d)
    (hgen : TrialGeneratedFrom trial state trace)
    {k : ℕ} (hk : k < trace.length) :
    trialActionPoint trial (replayTrial trial state (trace.take k)) fallback =
      (trace.get ⟨k, hk⟩).point := by
  induction trace generalizing state k with
  | nil => simp at hk
  | cons obs rest ih =>
      cases hact : trial.action state with
      | finish guards outcome =>
          simp only [TrialGeneratedFrom] at hgen
          rw [hact] at hgen
          contradiction
      | query point nextState =>
          have hgen' : obs.point = point ∧
              TrialGeneratedFrom trial (nextState obs) rest := by
            simp only [TrialGeneratedFrom] at hgen
            rw [hact] at hgen
            exact hgen
          have hpoint : obs.point = point := hgen'.1
          have hrest : TrialGeneratedFrom trial (nextState obs) rest := hgen'.2
          cases k with
          | zero => simp [replayTrial, trialActionPoint, hact, hpoint]
          | succ k =>
              have hkrest : k < rest.length := by simpa using hk
              simpa [replayTrial, trialActionPoint, hact] using
                ih hrest hkrest

lemma chargedTrace_generated (trial : LocalTrial d) (M D eps : ℝ)
    (x0 : Point d) (cached : Observation d) (suffix : List (Observation d))
    (hcached : cached.point = x0)
    (hgen : TrialGeneratedFrom trial (trial.initial M D ⟨cached⟩) suffix) :
    GeneratedBy (chargedTrialAlgorithm p trial M D eps) x0
      (cached :: suffix) := by
  intro t ht
  cases t with
  | zero => simpa using hcached
  | succ k =>
      have hk : k < suffix.length := by simpa using ht
      change (suffix.get ⟨k, hk⟩).point =
        (chargedTrialAlgorithm p trial M D eps).nextQuery x0
          ((cached :: suffix).take (k + 1))
      simp only [chargedTrialAlgorithm, List.take_succ_cons]
      exact (generatedFrom_action_at trial x0 hgen hk).symm

lemma chargedTrial_output_spec (trial : LocalTrial d) (M D : ℝ) {eps : ℝ}
    (x0 : Point d) (history : List (Observation d))
    (hex : ∃ obs ∈ history, lpNorm (conjugateExponent p) obs.gradient ≤ eps) :
    ∃ obs ∈ history,
      (chargedTrialAlgorithm p trial M D eps).output x0 history = obs.point ∧
      lpNorm (conjugateExponent p) obs.gradient ≤ eps := by
  let obs := Classical.choose hex
  have hspec := Classical.choose_spec hex
  refine ⟨obs, hspec.1, ?_, hspec.2⟩
  change (if h : ∃ o ∈ history,
      lpNorm (conjugateExponent p) o.gradient ≤ eps then
      (Classical.choose h).point else x0) = obs.point
  rw [dite_eq_left hex]

end V7.Stage5AboveTwoLowerS5F
