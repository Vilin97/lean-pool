/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.RetargetCompute
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Frame
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.RetargetOutput

/-!
# Running a machine from a work tape onto a work tape

A loop body cannot compute into the real output tape — it is one-way, so it
cannot serve as scratch across iterations. `TM.retargetInputStarted` reads a
machine's input off a work tape and `TM.retargetOutput` writes its output onto a
fresh one; composing them gives `TM.applyTM`, a work-to-work evaluator, and
composing their Hoare rules gives its contract.

## Main results

- `TM.applyTM` — the work-to-work evaluator for a source machine
- `TM.applyTM_hoareTime` / `TM.applyTM_hoareTime_frame` — its time contract
-/


@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ}

/-- **Work-tape-to-work-tape evaluation.** `applyTM M : TM (k + 2)` reads the
source machine's input off work tape `k`, runs `M` on it, and leaves the result
on work tape `k + 1`; the real input and output tapes are untouched.

Work tapes `0, …, k-1` are `M`'s own scratch, so a caller that runs `applyTM M`
more than once has to restore them between calls — that is what the
precondition below demands. -/
def applyTM (M : TM k) : TM (k + 2) := (retargetInputStarted M).retargetOutput

/-- The tapes `applyTM M` expects at entry: `M`'s scratch blank, the virtual
input holding `y`, the result tape blank. -/
def applyPre (M : TM k) (y : List Bool) (realInput : Tape) :
    Fin (k + 2) → Tape :=
  Fin.snoc (retargetInputStartedCfg M y realInput).work parkedBlank

/-- **The contract of the work-to-work evaluator.** Given `M`'s own time bound,
`applyTM M` halts within that bound with `f y` on its result tape — provided
`M`'s scratch tapes were blank, work tape `k` held `y`, and the result tape was
blank. -/
theorem applyTM_hoareTime (M : TM k) {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) :
    (applyTM M).HoareTime
      (fun inp work out =>
        ((fun i : Fin (k + 1) => work (Fin.castSucc i))
          = (retargetInputStartedCfg M y inp).work) ∧
        work (Fin.last (k + 1)) = parkedBlank ∧
        out = parkedBlank)
      (fun _inp work out =>
        (work (Fin.last (k + 1))).HasOutput (f y) ∧ out = parkedBlank)
      (T y.length) := by
  have h := retargetOutput_hoareTime (retargetInputStarted M)
    (retargetInputStarted_hoareTime M hcomp y)
  intro inp work out hpre
  obtain ⟨h1, h2, h3⟩ := hpre
  exact h inp work out ⟨⟨h1, h2⟩, h3⟩

/-- The entry tapes do satisfy the entry condition. -/
theorem applyPre_spec (M : TM k) (y : List Bool) (realInput : Tape) :
    ((fun i : Fin (k + 1) => applyPre M y realInput (Fin.castSucc i))
      = (retargetInputStartedCfg M y realInput).work) ∧
    applyPre M y realInput (Fin.last (k + 1)) = parkedBlank := by
  refine ⟨funext fun i => ?_, ?_⟩
  · rw [applyPre, Fin.snoc_castSucc]
  · rw [applyPre, Fin.snoc_last]

/-- The work-to-work evaluator reads its input from a work tape, so it idles
the real input head. -/
theorem applyTM_idlesInput (M : TM k) : IdlesInput (applyTM M) := fun _ _ _ _ => rfl

/-- Every entry tape of the work-to-work evaluator is parked at cell `1`. -/
theorem applyPre_head (M : TM k) (y : List Bool) (realInput : Tape) (i : Fin (k + 2)) :
    (applyPre M y realInput i).head = 1 := by
  refine Fin.lastCases ?_ ?_ i
  · rw [applyPre, Fin.snoc_last]; rfl
  · intro i'
    rw [applyPre, Fin.snoc_castSucc]
    show ((retargetInputStartedCfg M y realInput).work i').head = 1
    rw [retargetInputStartedCfg]
    dsimp only
    split <;> rfl

/-- Every entry tape of the work-to-work evaluator satisfies the left-marker
invariant. -/
theorem applyPre_startInvariant (M : TM k) (y : List Bool) (realInput : Tape)
    (i : Fin (k + 2)) : Tape.StartInvariant (applyPre M y realInput i) := by
  refine Fin.lastCases ?_ ?_ i
  · rw [applyPre, Fin.snoc_last]
    show Tape.StartInvariant ((Tape.init ([] : List Γ)).move Dir3.right)
    exact startInvariant_initNil.move Dir3.right
  · intro i'
    rw [applyPre, Fin.snoc_castSucc]
    show Tape.StartInvariant ((retargetInputStartedCfg M y realInput).work i')
    rw [retargetInputStartedCfg]
    dsimp only
    split
    · exact startInvariant_initNil.move Dir3.right
    · exact (startInvariant_initOfBool y).move Dir3.right

/-- Every entry tape of the work-to-work evaluator is blank beyond the virtual
input's length. -/
theorem applyPre_cells_blank (M : TM k) (y : List Bool) (realInput : Tape)
    (i : Fin (k + 2)) (j : ℕ) (hj : y.length < j) :
    (applyPre M y realInput i).cells j = Γ.blank := by
  have hj0 : j = (j - 1) + 1 := by omega
  refine Fin.lastCases ?_ ?_ i
  · rw [applyPre, Fin.snoc_last]
    show ((Tape.init ([] : List Γ)).move Dir3.right).cells j = Γ.blank
    rw [Tape.move_cells, hj0, Tape.init_cells_ge [] (j - 1) (by simp)]
  · intro i'
    rw [applyPre, Fin.snoc_castSucc]
    show ((retargetInputStartedCfg M y realInput).work i').cells j = Γ.blank
    rw [retargetInputStartedCfg]
    dsimp only
    split
    · show ((Tape.init ([] : List Γ)).move Dir3.right).cells j = Γ.blank
      rw [Tape.move_cells, hj0, Tape.init_cells_ge [] (j - 1) (by simp)]
    · show ((Tape.init (y.map Γ.ofBool)).move Dir3.right).cells j = Γ.blank
      rw [Tape.move_cells, hj0,
        Tape.init_cells_ge (y.map Γ.ofBool) (j - 1) (by simp only [List.length_map]; omega)]

/-- **The work-to-work evaluator, with its disturbance framed.** Beyond
computing `f y` onto the result tape, this records the two facts a caller needs
in order to reset the machine for a second call: every tape's head is still
within `H`, and every cell beyond `H` is still blank. Both follow from the run
being `T |y|`-bounded and every entry tape being parked and blank past `|y|`. -/
theorem applyTM_hoareTime_frame (M : TM k) {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) (inp₀ : Tape) (hinp : Parked inp₀)
    (hinpSI : Tape.StartInvariant inp₀)
    (H : ℕ) (hHy : y.length ≤ H) (hHT : 1 + T y.length ≤ H) :
    (applyTM M).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = applyPre M y inp₀ ∧ out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (work (Fin.last (k + 1))).HasOutput (f y) ∧
        ∀ i, Tape.StartInvariant (work i) ∧ (work i).head ≤ H ∧
          ∀ j, H < j → (work i).cells j = Γ.blank)
      (T y.length) := by
  intro inp work out hpre
  obtain ⟨hi, hw, ho⟩ := hpre
  rw [hi, hw, ho]
  obtain ⟨c', t, ht, hreach, hhalt, hOut, hOutEq⟩ :=
    applyTM_hoareTime M hcomp y inp₀ (applyPre M y inp₀) parkedBlank
      ⟨(applyPre_spec M y inp₀).1, (applyPre_spec M y inp₀).2, rfl⟩
  have hinpEq : c'.input = inp₀ :=
    reachesIn_input_eq_of_idlesInput (applyTM_idlesInput M) hreach hinp
  have hSI := reachesIn_startInvariant hreach hinpSI
    (fun i => applyPre_startInvariant M y inp₀ i)
    (show Tape.StartInvariant parkedBlank from startInvariant_initNil.move Dir3.right)
  refine ⟨c', t, ht, hreach, hhalt, hinpEq, hOutEq, hOut,
    fun i => ⟨hSI.2.1 i, ?_, fun j hj => ?_⟩⟩
  · have hh := (head_le_start_add_of_reachesIn (applyTM M) hreach).2.2 i
    rw [show ((⟨(applyTM M).qstart, inp₀, applyPre M y inp₀, parkedBlank⟩ :
      Cfg (k + 2) (applyTM M).Q).work i).head = 1 from applyPre_head M y inp₀ i] at hh
    omega
  · rw [reachesIn_work_cells_far hreach i j
      (by rw [applyPre_head M y inp₀ i]; omega)]
    exact applyPre_cells_blank M y inp₀ i j (by omega)

end TM

end Complexity
