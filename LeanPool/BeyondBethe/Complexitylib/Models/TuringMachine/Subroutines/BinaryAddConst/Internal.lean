/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Addition of a fixed natural to a canonical binary tape — proof internals

The proof follows the definition-level finite successor chain. Exact runs
compose through `seqTM`; the all-prefix space induction uses the largest
destination width rather than the total successor-chain runtime.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Canonical parked tape encoding of a natural for constant addition. -/
def binaryAddConstNatTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

private theorem binaryAddConstNatTape_hasBinaryNat (value : ℕ) :
    (binaryAddConstNatTape value).HasBinaryNat value :=
  Tape.init_move_right_hasBinaryNat value

private theorem binaryAddConstHasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem binaryAddConstNatTape_parked (value : ℕ) :
    Parked (binaryAddConstNatTape value) :=
  binaryAddConstHasBinaryNat_parked
    (binaryAddConstNatTape_hasBinaryNat value)

private def binaryAddConstWorkAt (work : Fin n → Tape) (idx : Fin n)
    (dstValue current : ℕ) : Fin n → Tape :=
  Function.update work idx (binaryAddConstNatTape (dstValue + current))

private theorem binaryAddConstWorkAt_target
    (work : Fin n → Tape) (idx : Fin n) (dstValue current : ℕ) :
    binaryAddConstWorkAt work idx dstValue current idx =
      binaryAddConstNatTape (dstValue + current) := by
  simp [binaryAddConstWorkAt]

private theorem binaryAddConstWorkAt_other
    (work : Fin n → Tape) {idx i : Fin n} (hne : i ≠ idx)
    (dstValue current : ℕ) :
    binaryAddConstWorkAt work idx dstValue current i = work i := by
  simp [binaryAddConstWorkAt, hne]

private theorem binaryAddConstWorkAt_target_hasBinaryNat
    (work : Fin n → Tape) (idx : Fin n) (dstValue current : ℕ) :
    (binaryAddConstWorkAt work idx dstValue current idx).HasBinaryNat
      (dstValue + current) := by
  rw [binaryAddConstWorkAt_target]
  exact binaryAddConstNatTape_hasBinaryNat _

private theorem binaryAddConstWorkAt_parked
    (work : Fin n → Tape) (idx : Fin n) (dstValue current : ℕ)
    (hwork : ∀ i, Parked (work i)) :
    ∀ i, Parked (binaryAddConstWorkAt work idx dstValue current i) := by
  intro i
  by_cases hi : i = idx
  · subst i
    rw [binaryAddConstWorkAt_target]
    exact binaryAddConstNatTape_parked _
  · rw [binaryAddConstWorkAt_other work hi]
    exact hwork i

private theorem binaryAddConstWorkAt_zero_eq
    (work : Fin n → Tape) (idx : Fin n) (dstValue : ℕ)
    (hdst : (work idx).HasBinaryNat dstValue) :
    binaryAddConstWorkAt work idx dstValue 0 = work := by
  funext i
  by_cases hi : i = idx
  · subst i
    rw [binaryAddConstWorkAt_target]
    simpa [binaryAddConstNatTape] using hdst.eq_init_move_right.symm
  · exact binaryAddConstWorkAt_other work hi dstValue 0

private theorem binaryAddConstWorkAt_succ_eq
    (work : Fin n → Tape) (idx : Fin n) (dstValue current : ℕ) :
    Function.update (binaryAddConstWorkAt work idx dstValue current) idx
        (binaryAddConstNatTape (dstValue + current + 1)) =
      binaryAddConstWorkAt work idx dstValue (current + 1) := by
  funext i
  by_cases hi : i = idx
  · subst i
    simp [binaryAddConstWorkAt, Nat.add_assoc]
  · simp [binaryAddConstWorkAt, hi]

private theorem binaryAddConstInitialWork_parked
    (work : Fin n → Tape) (idx : Fin n) {dstValue : ℕ}
    (hdst : (work idx).HasBinaryNat dstValue)
    (hother : ∀ i, i ≠ idx → Parked (work i)) :
    ∀ i, Parked (work i) := by
  intro i
  by_cases hi : i = idx
  · subst i
    exact binaryAddConstHasBinaryNat_parked hdst
  · exact hother i hi

/-- Predicate fixing the tapes framing a constant-addition execution. -/
abbrev binaryAddConstFramePred
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape) : TapePred n :=
  fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀

private theorem skipTM_reachesIn_frame
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (skipTM (n := n)).reachesIn 1
      { state := (skipTM (n := n)).qstart
        input := inp
        work := work
        output := out }
      { state := (skipTM (n := n)).qhalt
        input := inp
        work := work
        output := out } := by
  have hstep : (skipTM (n := n)).step
      { state := .go, input := inp, work := work, output := out } = some
      { state := .done, input := inp, work := work, output := out } := by
    simp only [TM.step, skipTM, reduceCtorEq, ↓reduceIte]
    refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
    · exact hinp.move_idle
    · funext i
      exact (hwork i).writeAndMove_readBack_idle
    · exact hout.writeAndMove_readBack_idle
  exact .step hstep .zero

private theorem binaryAddConstSucc_reachesIn
    (idx : Fin n) (dstValue current : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binarySuccTM idx).reachesIn (binarySuccTime (dstValue + current))
      { state := (binarySuccTM idx).qstart
        input := inp
        work := binaryAddConstWorkAt work idx dstValue current
        output := out }
      { state := (binarySuccTM idx).qhalt
        input := inp
        work := binaryAddConstWorkAt work idx dstValue (current + 1)
        output := out } := by
  have hworkAt := binaryAddConstWorkAt_parked work idx dstValue current hwork
  obtain ⟨c', hreach, hhalt, hinput, hother, htarget, houtput⟩ :=
    binarySuccTM_reachesIn_frame idx (dstValue + current) inp
      (binaryAddConstWorkAt work idx dstValue current) out
      (binaryAddConstWorkAt_target_hasBinaryNat work idx dstValue current)
      hinp.read_ne_start (fun i _ => (hworkAt i).read_ne_start)
      hout.read_ne_start
  have hworkEq : c'.work =
      binaryAddConstWorkAt work idx dstValue (current + 1) := by
    have hupdate : c'.work = Function.update
        (binaryAddConstWorkAt work idx dstValue current) idx
        (binaryAddConstNatTape (dstValue + current + 1)) := by
      funext i
      by_cases hi : i = idx
      · subst i
        rw [Function.update_self]
        exact htarget.eq_init_move_right
      · rw [Function.update_of_ne hi, hother i hi]
    rw [hupdate, binaryAddConstWorkAt_succ_eq]
  have hc' : c' =
      { state := (binarySuccTM idx).qhalt
        input := inp
        work := binaryAddConstWorkAt work idx dstValue (current + 1)
        output := out } :=
    Cfg.ext hhalt hinput hworkEq houtput
  simpa [hc'] using hreach

theorem binaryAddConstTM_reachesIn_frame_internal
    (idx : Fin n) (fixedValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hdst : (work₀ idx).HasBinaryNat dstValue)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryAddConstTM idx fixedValue).reachesIn
      (binaryAddConstTime fixedValue dstValue)
      { state := (binaryAddConstTM idx fixedValue).qstart
        input := inp₀
        work := work₀
        output := out₀ }
      { state := (binaryAddConstTM idx fixedValue).qhalt
        input := inp₀
        work := Function.update work₀ idx
          (binaryAddConstNatTape (dstValue + fixedValue))
        output := out₀ } := by
  have hwork := binaryAddConstInitialWork_parked work₀ idx hdst hother
  induction fixedValue with
  | zero =>
      have hrun := skipTM_reachesIn_frame inp₀ work₀ out₀ hinp hwork hout
      simp only [binaryAddConstTM, binaryAddConstTime]
      have heq : Function.update work₀ idx
          (binaryAddConstNatTape (dstValue + 0)) = work₀ := by
        simpa [binaryAddConstWorkAt] using
          binaryAddConstWorkAt_zero_eq work₀ idx dstValue hdst
      rw [heq]
      exact hrun
  | succ fixedValue ih =>
      have hprev := ih
      have hprevWork := binaryAddConstWorkAt_parked work₀ idx dstValue
        fixedValue hwork
      have hnext := binaryAddConstSucc_reachesIn idx dstValue fixedValue inp₀
        work₀ out₀ hinp hwork hout
      have hnext' : (binarySuccTM idx).reachesIn
          (binarySuccTime (dstValue + fixedValue))
          { state := (binarySuccTM idx).qstart
            input := transitionInput inp₀
            work := fun i => transitionTape
              (binaryAddConstWorkAt work₀ idx dstValue fixedValue i)
            output := transitionTape out₀ }
          { state := (binarySuccTM idx).qhalt
            input := inp₀
            work := binaryAddConstWorkAt work₀ idx dstValue (fixedValue + 1)
            output := out₀ } := by
        simpa only [hinp.transitionInput_eq_self,
          hout.transitionTape_eq_self,
          funext fun i => (hprevWork i).transitionTape_eq_self] using hnext
      have hseq := seqTM_reachesIn_of_reachesIn
        (binaryAddConstTM idx fixedValue) (binarySuccTM idx) hprev rfl hnext'
      simpa [binaryAddConstTM, binaryAddConstTime, binaryAddConstNatTape,
        binaryAddConstWorkAt] using! hseq

theorem binaryAddConstTM_hoareTime_frame_internal
    (idx : Fin n) (fixedValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hdst : (work₀ idx).HasBinaryNat dstValue)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryAddConstTM idx fixedValue).HoareTime
      (binaryAddConstFramePred inp₀ work₀ out₀)
      (binaryAddConstFramePred inp₀
        (Function.update work₀ idx
          (binaryAddConstNatTape (dstValue + fixedValue))) out₀)
      (binaryAddConstTime fixedValue dstValue) := by
  intro inp work out hpre
  obtain ⟨hinput, hworkEq, houtput⟩ := hpre
  subst inp
  subst work
  subst out
  let c' : Cfg n (binaryAddConstTM idx fixedValue).Q :=
    { state := (binaryAddConstTM idx fixedValue).qhalt
      input := inp₀
      work := Function.update work₀ idx
        (binaryAddConstNatTape (dstValue + fixedValue))
      output := out₀ }
  refine ⟨c', binaryAddConstTime fixedValue dstValue, le_rfl, ?_, rfl, ?_⟩
  · exact binaryAddConstTM_reachesIn_frame_internal idx fixedValue dstValue
      inp₀ work₀ out₀ hdst hinp hother hout
  · exact ⟨rfl, rfl, rfl⟩

private theorem binaryAddConstWorkAt_cfg_withinAuxSpace
    {Q : Type} (state : Q) (inp : Tape) (work : Fin n → Tape)
    (out : Tape) (idx : Fin n) (dstValue current inputLength initialSpace : ℕ)
    (hdst : (work idx).HasBinaryNat dstValue)
    (hworkSpace : ∀ i, (work i).head ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    ({ state := state
       input := inp
       work := binaryAddConstWorkAt work idx dstValue current
       output := out } : Cfg n Q).WithinAuxSpace inputLength initialSpace := by
  constructor
  · intro i
    change (binaryAddConstWorkAt work idx dstValue current i).head ≤
      initialSpace
    by_cases hi : i = idx
    · subst i
      rw [binaryAddConstWorkAt_target,
        (binaryAddConstNatTape_hasBinaryNat (dstValue + current)).2.1,
        ← hdst.2.1]
      exact hworkSpace idx
    · rw [binaryAddConstWorkAt_other work hi]
      exact hworkSpace i
  · exact hinputSpace

private theorem binaryAddConstFrame_transition
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀) :
    ∀ inp work out, binaryAddConstFramePred inp₀ work₀ out₀ inp work out →
      binaryAddConstFramePred inp₀ work₀ out₀
        (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out) := by
  rintro _ _ _ ⟨rfl, rfl, rfl⟩
  refine ⟨hinp.transitionInput_eq_self, ?_, hout.transitionTape_eq_self⟩
  funext i
  exact (hwork i).transitionTape_eq_self

theorem binaryAddConstTM_hoareTimeSpace_frame_internal
    (idx : Fin n) (fixedValue dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hdst : (work₀ idx).HasBinaryNat dstValue)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryAddConstTM idx fixedValue).HoareTimeSpace
      (binaryAddConstFramePred inp₀ work₀ out₀)
      (binaryAddConstFramePred inp₀
        (Function.update work₀ idx
          (binaryAddConstNatTape (dstValue + fixedValue))) out₀)
      (binaryAddConstTime fixedValue dstValue) inputLength
      (binaryAddConstSpace initialSpace fixedValue dstValue) := by
  have hwork := binaryAddConstInitialWork_parked work₀ idx hdst hother
  induction fixedValue with
  | zero =>
      have htime := binaryAddConstTM_hoareTime_frame_internal idx 0 dstValue
        inp₀ work₀ out₀ hdst hinp hother hout
      have hrun := htime.toHoareTimeSpace (by
        rintro _ _ _ ⟨rfl, rfl, rfl⟩
        constructor
        · exact hworkSpace
        · exact hinputSpace)
      exact hrun.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
        le_rfl le_rfl (by
          simp [binaryAddConstSpace, binaryAddConstTime]
          omega)
  | succ fixedValue ih =>
      let midWork := binaryAddConstWorkAt work₀ idx dstValue fixedValue
      have hmidWork := binaryAddConstWorkAt_parked work₀ idx dstValue
        fixedValue hwork
      have hmidTarget := binaryAddConstWorkAt_target_hasBinaryNat work₀ idx
        dstValue fixedValue
      have hmidSpace : ∀ i, (midWork i).head ≤ initialSpace := by
        have hcfg := binaryAddConstWorkAt_cfg_withinAuxSpace Unit.unit inp₀
          work₀ out₀ idx dstValue fixedValue inputLength initialSpace hdst
          hworkSpace hinputSpace
        exact hcfg.1
      have hsucc := binarySuccTM_hoareTimeSpace_frame idx
        (dstValue + fixedValue) inputLength initialSpace inp₀ midWork out₀
        (by simpa [midWork] using hmidTarget) hinp.read_ne_start
        (fun i _ => (hmidWork i).read_ne_start) hout.read_ne_start
        (by
          constructor
          · exact hmidSpace
          · exact hinputSpace)
      have hsucc' : (binarySuccTM idx).HoareTimeSpace
          (binaryAddConstFramePred inp₀ midWork out₀)
          (binaryAddConstFramePred inp₀
            (binaryAddConstWorkAt work₀ idx dstValue (fixedValue + 1)) out₀)
          (binarySuccTime (dstValue + fixedValue)) inputLength
          (initialSpace + binarySuccTime (dstValue + fixedValue)) := by
        refine hsucc.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
          le_rfl le_rfl le_rfl
        refine ⟨h.1, ?_, h.2.2.2⟩
        have hworkEq : work = Function.update midWork idx
            (binaryAddConstNatTape (dstValue + fixedValue + 1)) := by
          funext i
          by_cases hi : i = idx
          · subst i
            rw [Function.update_self]
            exact h.2.2.1.eq_init_move_right
          · rw [Function.update_of_ne hi, h.2.1 i hi]
        rw [hworkEq]
        simpa [midWork] using
          binaryAddConstWorkAt_succ_eq work₀ idx dstValue fixedValue
      have hseq := seqTM_hoareTimeSpace (binaryAddConstTM idx fixedValue)
        (binarySuccTM idx) ih
        (binaryAddConstFrame_transition inp₀ midWork out₀ hinp hmidWork hout)
        hsucc'
      refine hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
        (by simp [binaryAddConstTime]) le_rfl ?_
      have hprevSize : (dstValue + fixedValue).size ≤
          (dstValue + (fixedValue + 1)).size :=
        Nat.size_le_size (by omega)
      have hsuccTime := binarySuccTime_le (dstValue + fixedValue)
      simp [binaryAddConstSpace] at ⊢
      omega

theorem binaryAddConstTM_isTransducer_internal
    (idx : Fin n) (fixedValue : ℕ) :
    (binaryAddConstTM idx fixedValue).IsTransducer := by
  induction fixedValue with
  | zero =>
      intro state iHead wHeads oHead
      cases state
      all_goals
        simp [binaryAddConstTM, skipTM, idleDir]
        split <;> decide
  | succ fixedValue ih =>
      simpa [binaryAddConstTM] using
        ih.seqTM (binarySuccTM_isTransducer idx)

end TM

end Complexity
