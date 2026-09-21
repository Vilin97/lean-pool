/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Lift

/-!
# Hoare contracts for output redirection

This module lifts a framed contract through `TM.retargetOutput`, exposing the
source output as the fresh last work tape while pinning the real output to the
standard parked blank tape.
-/


public section

namespace Complexity

namespace TM

/-- Lift a framed time contract while redirecting the source machine's output
to the fresh last work tape. -/
theorem retargetOutput_hoareTime {n : ℕ} {pre post : TapePred n}
    {bound : ℕ} (tm : TM n) (h : tm.HoareTime pre post bound) :
    tm.retargetOutput.HoareTime
      (fun inp work out =>
        pre inp (fun i => work (Fin.castSucc i)) (work (Fin.last n)) ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        post inp (fun i => work (Fin.castSucc i)) (work (Fin.last n)) ∧
        out = (Tape.init []).move Dir3.right)
      bound := by
  intro inp work out hpre
  rcases hpre with ⟨hpre, hout⟩
  let baseWork : Fin n → Tape := fun i => work (Fin.castSucc i)
  let baseCfg : Cfg n tm.Q :=
    { state := tm.qstart
      input := inp
      work := baseWork
      output := work (Fin.last n) }
  have hstart :
      ({ state := tm.retargetOutput.qstart
         input := inp
         work := work
         output := out } : Cfg (n + 1) tm.retargetOutput.Q) =
        tm.retargetCfg baseCfg := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i.val < n
      · rw [retargetCfg_work_lt tm baseCfg i hi]
        change work i = work (Fin.castSucc ⟨i.val, hi⟩)
        congr
      · rw [show i = Fin.last n by
          apply Fin.ext
          simp only [Fin.val_last]
          omega]
        exact (retargetCfg_work_last tm baseCfg).symm
    · change out = (Tape.init []).move Dir3.right
      exact hout
  obtain ⟨c', time, htime, hreach, hhalt, hpost⟩ :=
    h inp baseWork (work (Fin.last n)) hpre
  refine ⟨tm.retargetCfg c', time, htime, ?_, hhalt, ?_⟩
  · rw [hstart]
    exact retargetOutput_reachesIn_retargetCfg_frame tm hreach
  · refine ⟨?_, rfl⟩
    simpa [retargetCfg_work_lt, retargetCfg_work_last] using hpost

end TM

end Complexity
