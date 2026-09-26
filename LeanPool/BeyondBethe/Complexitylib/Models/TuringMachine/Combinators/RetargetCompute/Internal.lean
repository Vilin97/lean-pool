/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.RetargetCompute.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Placement.Internal

/-!
# Retargeted-input computation seam internals

This file proves that `TM.retargetInputStarted` resumes an ordinary source run
after its compulsory sentinel transition. The already-halted case is handled
separately: such a machine can compute only the empty output, and the wrapper
therefore halts immediately on its parked blank output tape.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ}

/-- The started wrapper has exactly the same transition behavior as the
ordinary retargeted-input machine. -/
theorem retargetInputStarted_step_eq_internal (M : TM k)
    (c : Cfg (k + 1) M.Q) :
    (retargetInputStarted M).step c = (retargetInput M).step c := by
  rfl

/-- Any bounded run of the ordinary retargeted-input machine is also a run of
the started wrapper. -/
theorem retargetInputStarted_reachesIn_of_retargetInput_internal (M : TM k)
    {t : ℕ} {c c' : Cfg (k + 1) M.Q}
    (hreach : (retargetInput M).reachesIn t c c') :
    (retargetInputStarted M).reachesIn t c c' := by
  apply reachesIn_map (tm := retargetInput M) (tm' := retargetInputStarted M)
    (fun c => c) _ hreach
  intro c₀ c₁ hstep
  change (retargetInputStarted M).step c₀ = some c₁
  exact (retargetInputStarted_step_eq_internal M c₀).trans hstep

/-- In the nondegenerate case, the wrapper start state is exactly the source
state after its first transition from the all-sentinel configuration. -/
theorem retargetInputStarted_qstart_eq_startedCfg_state_internal (M : TM k)
    (y : List Bool) (hne : M.qstart ≠ M.qhalt) :
    (retargetInputStarted M).qstart = (startedCfg M y hne).state := by
  simp [retargetInputStarted, retargetInputStartState, startedCfg, TM.step, hne,
    Tape.read, Tape.init]

/-- In the nondegenerate case, the canonical wrapper entry is the ordinary
`retargetWrap` of the source's exact post-sentinel configuration. -/
theorem retargetInputStartedCfg_eq_retargetWrap_internal (M : TM k)
    (y : List Bool) (realInput : Tape) (hne : M.qstart ≠ M.qhalt) :
    retargetInputStartedCfg M y realInput =
      retargetWrap M realInput (startedCfg M y hne) := by
  refine Cfg.ext ?_ rfl ?_ ?_
  · exact retargetInputStarted_qstart_eq_startedCfg_state_internal M y hne
  · funext i
    by_cases hi : i.val < k
    · rw [retargetInputStartedCfg_work_lt M y realInput i hi,
        retargetWrap_work_lt M realInput _ i hi]
      exact (startedCfg_work_eq_init_move_right M y hne ⟨i.val, hi⟩).symm
    · have hval : i.val = k := by omega
      have hilast : i = ⟨k, by omega⟩ := by
        apply Fin.ext
        exact hval
      rw [hilast]
      rw [retargetInputStartedCfg_work_last, retargetWrap_work_last,
        startedCfg_input_eq]
  · rw [retargetInputStartedCfg_output, retargetWrap_output,
      startedCfg_output_eq_init_move_right]

/-- An initially halted machine that computes a function can only compute the
empty string. -/
private theorem computes_eq_nil_of_qstart_eq_qhalt (M : TM k)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (heq : M.qstart = M.qhalt) (y : List Bool) :
    f y = [] := by
  obtain ⟨c', t, _ht, hreach, _hhalt, hout⟩ := hcomp y
  have hinit : M.halted (M.initCfg y) := by
    simpa [TM.halted, Cfg.isHalted] using heq
  have ht0 : t = 0 := by
    have hle := M.reachesIn_le_halt hreach
      (TM.reachesIn.zero : M.reachesIn 0 (M.initCfg y) (M.initCfg y)) hinit
    omega
  subst t
  cases hreach
  cases hy : f y with
  | nil => rfl
  | cons bit bits =>
      have hcell := hout.1 0 (by simp [hy])
      simp [hy, Tape.init] at hcell
      exact (False.elim ((Γ.ofBool_ne_blank bit) hcell.symm))

/-- Exact virtual-input computation seam. The result time omits the source's
first transition when that transition exists; an initially halted source uses
zero steps. -/
theorem retargetInputStarted_computesVirtual_exact_internal (M : TM k)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) (realInput : Tape) :
    ∃ (c' : Cfg (k + 1) M.Q) (t : ℕ),
      t + (if M.qstart = M.qhalt then 0 else 1) ≤ T y.length ∧
      (retargetInputStarted M).reachesIn t
        (retargetInputStartedCfg M y realInput) c' ∧
      (retargetInputStarted M).halted c' ∧
      c'.output.HasOutput (f y) := by
  by_cases heq : M.qstart = M.qhalt
  · have hfy := computes_eq_nil_of_qstart_eq_qhalt M hcomp heq y
    refine ⟨retargetInputStartedCfg M y realInput, 0, ?_, .zero, ?_, ?_⟩
    · simp [heq]
    · show (retargetInputStarted M).qstart = (retargetInputStarted M).qhalt
      simp [retargetInputStarted, heq]
    · rw [hfy]
      simp [Tape.HasOutput, Tape.init, Tape.move]
  · obtain ⟨cM, t, ht, hreach, hhalt, hout⟩ := hcomp y
    have ht_ne : t ≠ 0 := by
      intro ht0
      subst t
      cases hreach
      exact heq hhalt
    obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht_ne
    cases hreach with
    | step hstep hrest =>
        next cMid =>
          have hmid : cMid = startedCfg M y heq := by
            have hs : some cMid = some (startedCfg M y heq) := by
              rw [← hstep, step_initCfg_startedCfg M y heq]
            exact Option.some.inj hs
          subst cMid
          have hinitIn : Tape.StartInvariant (M.initCfg y).input :=
            Tape.StartInvariant.init_ofBool y
          have hinitWork : ∀ i, Tape.StartInvariant ((M.initCfg y).work i) :=
            fun _ => Tape.StartInvariant.init_nil
          have hinitOut : Tape.StartInvariant (M.initCfg y).output :=
            Tape.StartInvariant.init_nil
          obtain ⟨hinv, hworkInv, houtInv⟩ := Tape.StartInvariant.step M
            (step_initCfg_startedCfg M y heq) hinitIn hinitWork hinitOut
          obtain ⟨finalReal, hsim⟩ := retargetInput_reachesIn_of_reachesIn M hrest
            hinv hworkInv houtInv realInput
          let c' := retargetWrap M finalReal cM
          have hsim' : (retargetInputStarted M).reachesIn t'
              (retargetInputStartedCfg M y realInput) c' := by
            rw [retargetInputStartedCfg_eq_retargetWrap_internal M y realInput heq]
            exact retargetInputStarted_reachesIn_of_retargetInput_internal M hsim
          refine ⟨c', t', ?_, hsim', ?_, ?_⟩
          · simp [heq]
            omega
          · show cM.state = M.qhalt
            exact hhalt
          · show cM.output.HasOutput (f y)
            exact hout

/-- Same-time form of the virtual-input computation seam. -/
theorem retargetInputStarted_computesVirtual_internal (M : TM k)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) (realInput : Tape) :
    ∃ (c' : Cfg (k + 1) M.Q) (t : ℕ),
      t ≤ T y.length ∧
      (retargetInputStarted M).reachesIn t
        (retargetInputStartedCfg M y realInput) c' ∧
      (retargetInputStarted M).halted c' ∧
      c'.output.HasOutput (f y) := by
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
    retargetInputStarted_computesVirtual_exact_internal M hcomp y realInput
  exact ⟨c', t, by omega, hreach, hhalt, hout⟩

/-- A decider run can be resumed on a virtual input with the same advertised
time bound while retaining both verdict implications. -/
theorem retargetInputStarted_decidesVirtual_internal (M : TM k)
    {L : Language} {T : ℕ → ℕ}
    (hdec : M.DecidesInTime L T) (y : List Bool) (realInput : Tape) :
    ∃ (c' : Cfg (k + 1) M.Q) (t : ℕ),
      t ≤ T y.length ∧
      (retargetInputStarted M).reachesIn t
        (retargetInputStartedCfg M y realInput) c' ∧
      (retargetInputStarted M).halted c' ∧
      (y ∈ L → c'.output.cells 1 = Γ.one) ∧
      (y ∉ L → c'.output.cells 1 = Γ.zero) := by
  obtain ⟨c', t, ht, hreach, hhalt, hyes, hno⟩ :=
    retargetInput_decidesVirtual_started M hdec y realInput
  refine ⟨c', t, by omega, ?_, hhalt, hyes, hno⟩
  rw [retargetInputStartedCfg_eq_retargetWrap_internal M y realInput
    (qstart_ne_qhalt_of_decidesInTime M hdec)]
  exact retargetInputStarted_reachesIn_of_retargetInput_internal M hreach

/-- Hoare form of the same-time virtual-input seam. -/
theorem retargetInputStarted_hoareTime_internal (M : TM k)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) :
    (retargetInputStarted M).HoareTime
      (fun inp work out =>
        work = (retargetInputStartedCfg M y inp).work ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp _work out => out.HasOutput (f y))
      (T y.length) := by
  intro inp work out hpre
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
    retargetInputStarted_computesVirtual_internal M hcomp y inp
  have hstart :
      ({ state := (retargetInputStarted M).qstart, input := inp,
          work := work, output := out } : Cfg (k + 1) M.Q) =
        retargetInputStartedCfg M y inp := by
    exact Cfg.ext rfl rfl hpre.1 hpre.2
  refine ⟨c', t, ht, ?_, hhalt, hout⟩
  exact hstart.symm ▸ hreach

/-- Combined placement seam with an exact preserved physical frame. The source
work tapes and virtual input occupy the placed middle block; all prefix and
suffix tapes are returned unchanged. -/
theorem placeWorkTM_retargetInputStarted_computesVirtual_internal (M : TM k)
    (pre post : ℕ) (extras : Fin (pre + (k + 1) + post) → Tape)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) (realInput : Tape)
    (hinv : ∀ i, ¬placeWorkInMiddle pre (k + 1) i →
      Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬placeWorkInMiddle pre (k + 1) i →
      1 ≤ (extras i).head) :
    ∃ (c' : Cfg (k + 1) M.Q)
      (C' : Cfg (pre + (k + 1) + post)
        (placeWorkTM pre post (retargetInputStarted M)).Q) (t : ℕ),
      t ≤ T y.length ∧
      (placeWorkTM pre post (retargetInputStarted M)).reachesIn t
        (placeWorkCfg (retargetInputStarted M) pre post extras
          (retargetInputStartedCfg M y realInput)) C' ∧
      C' = placeWorkCfg (retargetInputStarted M) pre post extras c' ∧
      (placeWorkTM pre post (retargetInputStarted M)).halted C' ∧
      C'.output.HasOutput (f y) := by
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
    retargetInputStarted_computesVirtual_internal M hcomp y realInput
  let C' := placeWorkCfg (retargetInputStarted M) pre post extras c'
  refine ⟨c', C', t, ht, ?_, rfl, ?_, ?_⟩
  · apply placeWorkTM_reachesIn_placeWorkCfg_stable_internal _ pre post extras hreach
    intro i hi
    show (extras i).cells (extras i).head ≠ Γ.start
    exact (hinv i hi).2 (extras i).head (hhead i hi)
  · show c'.state = (retargetInputStarted M).qhalt
    exact hhalt
  · show c'.output.HasOutput (f y)
    exact hout

/-- Placed virtual-input decision with an exact preserved physical frame. -/
theorem placeWorkTM_retargetInputStarted_decidesVirtual_internal (M : TM k)
    (pre post : ℕ) (extras : Fin (pre + (k + 1) + post) → Tape)
    {L : Language} {T : ℕ → ℕ}
    (hdec : M.DecidesInTime L T) (y : List Bool) (realInput : Tape)
    (hinv : ∀ i, ¬placeWorkInMiddle pre (k + 1) i →
      Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬placeWorkInMiddle pre (k + 1) i →
      1 ≤ (extras i).head) :
    ∃ (c' : Cfg (k + 1) M.Q)
      (C' : Cfg (pre + (k + 1) + post)
        (placeWorkTM pre post (retargetInputStarted M)).Q) (t : ℕ),
      t ≤ T y.length ∧
      (placeWorkTM pre post (retargetInputStarted M)).reachesIn t
        (placeWorkCfg (retargetInputStarted M) pre post extras
          (retargetInputStartedCfg M y realInput)) C' ∧
      C' = placeWorkCfg (retargetInputStarted M) pre post extras c' ∧
      (placeWorkTM pre post (retargetInputStarted M)).halted C' ∧
      (y ∈ L → C'.output.cells 1 = Γ.one) ∧
      (y ∉ L → C'.output.cells 1 = Γ.zero) := by
  obtain ⟨c', t, ht, hreach, hhalt, hyes, hno⟩ :=
    retargetInputStarted_decidesVirtual_internal M hdec y realInput
  let C' := placeWorkCfg (retargetInputStarted M) pre post extras c'
  refine ⟨c', C', t, ht, ?_, rfl, ?_, ?_, ?_⟩
  · apply placeWorkTM_reachesIn_placeWorkCfg_stable_internal _ pre post extras hreach
    intro i hi
    show (extras i).cells (extras i).head ≠ Γ.start
    exact (hinv i hi).2 (extras i).head (hhead i hi)
  · show c'.state = (retargetInputStarted M).qhalt
    exact hhalt
  · show y ∈ L → c'.output.cells 1 = Γ.one
    exact hyes
  · show y ∉ L → c'.output.cells 1 = Γ.zero
    exact hno

end TM

end Complexity
