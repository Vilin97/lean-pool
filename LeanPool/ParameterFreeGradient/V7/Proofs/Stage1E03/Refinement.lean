/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03.SourceData

namespace V7
namespace Stage1E03

noncomputable local instance refinementPropDecidable (q : Prop) : Decidable q :=
  Classical.propDecidable q

def prependReport (history : List (Observation d))
    (guards : List (ObservableGuardCheck d)) (tail : TrialReport d) :
    TrialReport d :=
  ⟨history ++ tail.trace, guards ++ tail.checkedGuards, tail.outcome⟩

noncomputable def sourceTerminalReport (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (U : Point d) : TrialReport d :=
  let cfg := O3.stage9ExecutionConfig n inst.oracle M U
  let on := inst.oracle.observe (O3.ogmgState cfg n).current
  let ov := inst.oracle.observe (O3.ogmgV cfg n)
  let terminal := terminalCheck on ov
  if CheckHolds 2 M terminal then
    if lpNorm 2 on.gradient ≤ eps then
      ⟨[ov], [terminal], .success on⟩
    else ⟨[ov], [terminal], .radius on⟩
  else ⟨[ov], [terminal], .scale terminal⟩

noncomputable def sourcePhaseBSuffix (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (U : Point d) : TrialReport d :=
  let cfg := O3.stage9ExecutionConfig n inst.oracle M U
  let checks := allInterpolationChecks n fun i =>
    inst.oracle.observe (O3.ogmgState cfg i).current
  match evaluateChecks 2 M checks with
  | .error (prior, failed) => ⟨[], prior, .scale failed⟩
  | .ok passed => prependReport [] passed (sourceTerminalReport inst eps M n U)

noncomputable def sourcePhaseBReport (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (U : Point d) : TrialReport d :=
  let cfg := O3.stage9ExecutionConfig n inst.oracle M U
  let newTrace := (List.range n).map fun j =>
    inst.oracle.observe (O3.ogmgState cfg (j + 1)).current
  prependReport newTrace [] (sourcePhaseBSuffix inst eps M n U)

noncomputable def sourcePhaseAReport (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) : ℕ → ℕ → TrialReport d
  | _, 0 => sourcePhaseBReport inst eps M n
      (sourceEstimateState inst.oracle M x0 n).accelerated
  | k, fuel + 1 =>
      let oy := inst.oracle.observe
        (estimateQuery M x0 k (sourceEstimateState inst.oracle M x0 k))
      let ox := inst.oracle.observe
        (sourceEstimateState inst.oracle M x0 (k + 1)).accelerated
      let check := upperCheck oy ox
      if CheckHolds 2 M check then
        prependReport [oy, ox] [check]
          (sourcePhaseAReport inst eps M n (k + 1) fuel)
      else ⟨[oy, ox], [check], .scale check⟩

@[simp] theorem ogmgStep_eq_source (n : ℕ) (oracle : PairOracle d)
    (M : ℝ) (U : Point d) (i : ℕ) :
    ogmgStep n M i (O3.ogmgState
        (O3.stage9ExecutionConfig n oracle M U) i)
      (oracle.observe (O3.ogmgState
        (O3.stage9ExecutionConfig n oracle M U) i).current) =
      O3.ogmgState (O3.stage9ExecutionConfig n oracle M U) (i + 1) := by
  rfl

theorem allInterpolationChecks_eq_source (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) (U : Point d) (obsAt : ℕ → Observation d)
    (hobs : ∀ i, i ≤ n → obsAt i = inst.oracle.observe
      (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) i).current) :
    allInterpolationChecks n obsAt =
      allInterpolationChecks n (fun i => inst.oracle.observe
        (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) i).current) := by
  unfold allInterpolationChecks
  apply List.flatMap_congr
  intro i hi
  apply List.map_congr_left
  intro j hj
  rw [hobs i (by simpa using List.mem_range.mp hi),
    hobs j (by simpa using List.mem_range.mp hj)]

theorem eval_terminal_eq_source (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (U : Point d)
    (obsAt : ℕ → Observation d) (history : List (Observation d))
    (guards : List (ObservableGuardCheck d))
    (hobs : obsAt n = inst.oracle.observe
      (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) n).current) :
    Program.eval inst.oracle 1 (terminalProgram eps M n obsAt
      (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) n) guards)
      history =
      prependReport history guards (sourceTerminalReport inst eps M n U) := by
  have hv :
      (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) n).current -
          M⁻¹ • (inst.oracle.observe
            (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) n).current).gradient =
        O3.ogmgV (O3.stage9ExecutionConfig n inst.oracle M U) n := rfl
  simp only [terminalProgram, Program.eval, sourceTerminalReport]
  rw [hobs]
  rw [hv]
  by_cases ht : CheckHolds 2 M
      (terminalCheck
        (inst.oracle.observe
          (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) n).current)
        (inst.oracle.observe
          (O3.ogmgV (O3.stage9ExecutionConfig n inst.oracle M U) n)))
  · by_cases hs : lpNorm 2 (inst.oracle.observe
        (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) n).current).gradient ≤ eps
    · simp only [ht, hs, ↓reduceIte]
      rfl
    · simp only [ht, hs, ↓reduceIte]
      rfl
  · simp only [ht, ↓reduceIte]
    rfl

theorem eval_phaseB_eq_source (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (U : Point d) : ∀ fuel i
    (exec : O3.OGMGExecutionState d) (obsAt : ℕ → Observation d)
    (history : List (Observation d))
    (guards : List (ObservableGuardCheck d)),
    i + fuel = n →
    exec = O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) i →
    (∀ j, j ≤ i → obsAt j = inst.oracle.observe
      (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) j).current) →
    Program.eval inst.oracle (fuel + 1)
      (phaseBProgram eps M n i exec obsAt guards fuel) history =
      prependReport history guards
        (let cfg := O3.stage9ExecutionConfig n inst.oracle M U
         let pre := (List.range fuel).map fun j =>
           inst.oracle.observe (O3.ogmgState cfg (i + j + 1)).current
         prependReport pre [] (sourcePhaseBSuffix inst eps M n U)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i exec obsAt history guards hin hexec hobs
      have hi : i = n := by omega
      subst i
      subst exec
      have hchecks := allInterpolationChecks_eq_source inst M n U obsAt hobs
      simp only [phaseBProgram, Program.eval, List.range_zero, List.map_nil,
        prependReport, List.nil_append]
      rw [hchecks]
      unfold sourcePhaseBSuffix
      dsimp only
      cases heval : evaluateChecks 2 M
          (allInterpolationChecks n fun i => inst.oracle.observe
            (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) i).current) with
      | error err =>
          rcases err with ⟨prior, failed⟩
          simp only [heval]
          change (⟨history, guards ++ prior, .scale failed⟩ : TrialReport d) = _
          simp
      | ok passed =>
          simp only [heval]
          rw [eval_terminal_eq_source inst eps M n U _ history
            (guards ++ passed) (hobs n (le_refl n))]
          simp [prependReport, List.append_assoc]
  | succ fuel ih =>
      intro i exec obsAt history guards hin hexec hobs
      have hi : i < n := by omega
      subst exec
      let cfg := O3.stage9ExecutionConfig n inst.oracle M U
      let oi := inst.oracle.observe (O3.ogmgState cfg (i + 1)).current
      let obsNext := fun j => if j = i + 1 then oi else obsAt j
      have hobsNext : ∀ j, j ≤ i + 1 → obsNext j =
          inst.oracle.observe (O3.ogmgState cfg j).current := by
        intro j hj
        by_cases hjnew : j = i + 1
        · simp [obsNext, hjnew, oi]
        · have hji : j ≤ i := by omega
          simp [obsNext, hjnew, hobs j hji, cfg]
      have htail := ih (i + 1) (O3.ogmgState cfg (i + 1)) obsNext
        (history ++ [oi]) guards (by omega) rfl hobsNext
      have hpre :
          inst.oracle.observe (O3.ogmgState cfg (i + 1)).current ::
            (List.range fuel).map (fun j => inst.oracle.observe
              (O3.ogmgState cfg (i + 1 + j + 1)).current) =
          (List.range (fuel + 1)).map (fun j => inst.oracle.observe
            (O3.ogmgState cfg (i + j + 1)).current) := by
        rw [List.range_succ_eq_map]
        simp only [List.map_cons, List.map_map, Function.comp_apply,
          Nat.add_zero]
        congr 1
        apply List.map_congr_left
        intro a ha
        congr 3 <;> omega
      simp only [phaseBProgram, Program.eval]
      have hoi := hobs i (by omega)
      rw [hoi, ogmgStep_eq_source]
      dsimp only [cfg, oi, obsNext] at htail ⊢
      rw [htail]
      dsimp only [cfg] at hpre
      simp only [prependReport, List.append_assoc]
      rw [← hpre]
      rfl

theorem eval_phaseA_eq_source (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) : ∀ fuel k
    (last : Option (Observation d)) (history : List (Observation d))
    (guards : List (ObservableGuardCheck d)),
    k + fuel = n →
    (fuel = 0 → last = some (inst.oracle.observe
      (sourceEstimateState inst.oracle M x0 n).accelerated)) →
    Program.eval inst.oracle (phaseABudget n fuel)
      (phaseAProgram eps M x0 n k
        (sourceEstimateState inst.oracle M x0 k) last guards fuel) history =
      prependReport history guards (sourcePhaseAReport inst eps M n k fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k last history guards hkn hlast
      have hk : k = n := by omega
      subst k
      rw [hlast rfl]
      simp only [phaseAProgram, sourcePhaseAReport]
      have hB := eval_phaseB_eq_source inst eps M n
        (sourceEstimateState inst.oracle M x0 n).accelerated n 0
        ⟨(sourceEstimateState inst.oracle M x0 n).accelerated,
          (sourceEstimateState inst.oracle M x0 n).accelerated⟩
        (fun _ => inst.oracle.observe
          (sourceEstimateState inst.oracle M x0 n).accelerated)
        history guards (by omega) rfl (by
          intro j hj
          have hj0 : j = 0 := by omega
          subst j
          rfl)
      simpa [phaseABudget, sourcePhaseBReport, prependReport] using hB
  | succ fuel ih =>
      intro k last history guards hkn _
      let oy := inst.oracle.observe
        (estimateQuery M x0 k (sourceEstimateState inst.oracle M x0 k))
      let ox := inst.oracle.observe
        (sourceEstimateState inst.oracle M x0 (k + 1)).accelerated
      let check := upperCheck oy ox
      have htail := ih (k + 1) (some ox) (history ++ [oy, ox])
        (guards ++ [check]) (by omega) (by
          intro hf
          subst fuel
          have : k + 1 = n := by omega
          subst n
          rfl)
      have hstate := sourceEstimateState_succ inst.oracle M x0 k
      have hacc := congrArg O3.EuclideanEstimateState.accelerated hstate
      have hox := congrArg inst.oracle.observe hacc
      have htail' := htail
      simp only [hstate] at htail'
      dsimp only [oy, ox, check] at htail'
      rw [hox] at htail'
      simp only [phaseABudget, phaseAProgram, Program.eval,
        sourceEstimateState_succ, sourcePhaseAReport]
      dsimp only [oy, ox, check] at htail ⊢
      by_cases hcheck : CheckHolds 2 M
          (upperCheck
            (inst.oracle.observe
              (estimateQuery M x0 k (sourceEstimateState inst.oracle M x0 k)))
            (inst.oracle.observe
              (nextEstimateState M x0 k (sourceEstimateState inst.oracle M x0 k)
                (inst.oracle.observe (estimateQuery M x0 k
                  (sourceEstimateState inst.oracle M x0 k)))).accelerated))
      · rw [if_pos hcheck]
        simp only [hcheck, ↓reduceIte]
        simp only [List.append_assoc, List.singleton_append]
        rw [htail']
        simp [prependReport, List.append_assoc]
      · rw [if_neg hcheck]
        simp only [hcheck, ↓reduceIte]
        rw [Program.eval]
        simp [prependReport, List.append_assoc]

theorem eval_full_eq_source (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (hn : 0 < n) :
    Program.eval inst.oracle (phaseABudget n n)
      (phaseAProgram eps M x0 n 0 ⟨x0, 0⟩ none [] n) [] =
      sourcePhaseAReport inst eps M n 0 n := by
  have h := eval_phaseA_eq_source inst eps M n n 0 none [] []
    (by simp) (by intro hzero; omega)
  simpa [prependReport] using h

end Stage1E03
end V7
