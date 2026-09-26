/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.CopyWorkOutput
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetTapes

/-!
# Copying a value into virtual-input shape

`TM.retargetInputStartedCfg` expects the virtual-input work tape in the exact
shape `(Tape.init (y.map Γ.ofBool)).move Dir3.right` — head parked at cell `1`.
A value produced elsewhere lands with its head *past* its content, so one more
rewind closes the gap.

## Main results

- `TM.copyToVirtualInputTM` — move a value into virtual-input position
- `TM.copyToVirtualInputTM_hoareTime` — its contract
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Copy the value held at `src` into `dst`, then rewind `dst` to cell `1` —
the exact shape `retargetInputStartedCfg` expects of a virtual input. Every
tape besides `src`/`dst`, the real input, and the real output are held at
fixed `Parked` values throughout. -/
theorem copyToVirtualInput_hoareTime {n : ℕ} (src dst : Fin n) (hne : src ≠ dst)
    (x : List Bool) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrcHead : (work₀ src).head = 1) (hsrcOut : (work₀ src).HasOutput x)
    (hsrcParked : Parked (work₀ src))
    (hdst : work₀ dst = (Tape.init []).move Dir3.right)
    (hinp : Parked inp₀) (hout : Parked out₀)
    (hother : ∀ i, i ≠ src → i ≠ dst → Parked (work₀ i)) :
    (seqTM (copyWorkToWorkTM src dst) (rewindWorkTM dst)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work dst = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        (work src).cells = (work₀ src).cells ∧
        (work src).head = x.length + 1 ∧
        (∀ i, i ≠ src → i ≠ dst → work i = work₀ i))
      (2 * x.length + 5) := by
  have hP : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      (inp = inp₀ ∧ out = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work i = work₀ i) →
      (work' src).cells = (work₀ src).cells →
      (work' src).head = x.length + 1 →
      (work' src).HasOutput x →
      (work' dst).HasBinaryPrefix x →
      (work' dst).cells 0 = Γ.start →
      inp' = inp → out' = out →
      (∀ i, i ≠ src → i ≠ dst → work' i = work i) →
      (inp' = inp₀ ∧ out' = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work' i = work₀ i) := by
    rintro inp work out inp' work' out' ⟨rfl, rfl, hrest⟩ _ _ _ _ _ rfl rfl hkeep
    exact ⟨rfl, rfl, fun i hisrc hidst => (hkeep i hisrc hidst).trans (hrest i hisrc hidst)⟩
  have hcopy := copyWorkToWorkTM_hoareTime_frame_of_hasOutput src dst hne x (work₀ src) hP
  have hpre_imp : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape),
      (inp = inp₀ ∧ work = work₀ ∧ out = out₀) →
      (work src = work₀ src ∧ (work₀ src).head = 1 ∧ (work₀ src).HasOutput x ∧
        work dst = (Tape.init []).move Dir3.right ∧
        inp.read ≠ Γ.start ∧ out.read ≠ Γ.start ∧ 1 ≤ out.head ∧
        (∀ i, i ≠ src → i ≠ dst → (work i).read ≠ Γ.start ∧ 1 ≤ (work i).head) ∧
        (inp = inp₀ ∧ out = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work i = work₀ i)) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, hsrcHead, hsrcOut, hdst, hinp.read_ne_start, hout.read_ne_start, hout.1,
      fun i hisrc hidst => ⟨(hother i hisrc hidst).read_ne_start, (hother i hisrc hidst).1⟩,
      rfl, rfl, fun i _ _ => rfl⟩
  have h₁ := hcopy.weaken_pre hpre_imp
  have hP2 : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      ((work dst).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (work src).cells = (work₀ src).cells ∧
        (work src).head = x.length + 1 ∧
        inp = inp₀ ∧ out = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work i = work₀ i) →
      (work' dst).cells = (work dst).cells →
      (work' dst).head = 1 →
      (∀ i, i ≠ dst → work' i = work i) →
      inp' = inp →
      out'.cells = out.cells →
      out'.head = out.head →
      ((work' dst).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (work' src).cells = (work₀ src).cells ∧
        (work' src).head = x.length + 1 ∧
        inp' = inp₀ ∧ out' = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work' i = work₀ i) := by
    rintro inp work out inp' work' out' ⟨hcellsP, hsc, hsh, rfl, rfl, hrest⟩ hcells' _ hkeep rfl
      hout'c hout'h
    refine ⟨hcells'.trans hcellsP, ?_, ?_, rfl, Tape.ext hout'h hout'c,
      fun i hisrc hidst => (hkeep i hidst).trans (hrest i hisrc hidst)⟩
    · rw [hkeep src hne]; exact hsc
    · rw [hkeep src hne]; exact hsh
  have h₂ := rewindWorkTM_hoareTime_frame (n := n) dst (x.length + 1)
    (P := fun inp work out =>
      (work dst).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      (work src).cells = (work₀ src).cells ∧
      (work src).head = x.length + 1 ∧
      inp = inp₀ ∧ out = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work i = work₀ i) hP2
  have hcomb : (seqTM (copyWorkToWorkTM src dst) (rewindWorkTM dst)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => (work dst).head = 1 ∧
        (work dst).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (work src).cells = (work₀ src).cells ∧
        (work src).head = x.length + 1 ∧
        inp = inp₀ ∧ out = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work i = work₀ i)
      (2 * x.length + 5) := by
    refine (seqTM_hoareTime (copyWorkToWorkTM src dst) (rewindWorkTM dst) h₁ ?_ h₂).mono_bound
      (by omega)
    rintro inp work out ⟨hcells, hhead, hout_, hprefix, hcell0, hPinp, hPout, hPrest⟩
    have hread_src : (work src).read ≠ Γ.start := by
      show (work src).cells (work src).head ≠ Γ.start
      rw [hhead, hcells]
      exact hsrcParked.2 (x.length + 1) (by omega)
    have hread_dst : (work dst).read ≠ Γ.start := by
      rw [hprefix.read_blank]; decide
    have hread_other : ∀ i, i ≠ dst → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1 := by
      intro i hidst
      by_cases hisrc : i = src
      · subst hisrc; exact ⟨hread_src, by omega⟩
      · rw [hPrest i hisrc hidst]
        exact ⟨(hother i hisrc hidst).read_ne_start, (hother i hisrc hidst).1⟩
    have hinp_ns : inp.read ≠ Γ.start := by rw [hPinp]; exact hinp.read_ne_start
    have hout_ns : out.read ≠ Γ.start := by rw [hPout]; exact hout.read_ne_start
    have ht1 : transitionInput inp = inp := transitionInput_eq_self hinp_ns
    have ht2 : (fun i => transitionTape (work i)) = work :=
      funext fun i => by
        by_cases hidst : i = dst
        · subst hidst; exact transitionTape_eq_self hread_dst
        · exact transitionTape_eq_self (hread_other i hidst).1
    have ht3 : transitionTape out = out := transitionTape_eq_self hout_ns
    rw [ht1, ht2, ht3]
    have hcellsP : (work dst).cells = (Tape.init (x.map Γ.ofBool)).cells :=
      hprefix.cells_eq_init hcell0
    refine ⟨hcell0, ?_, le_of_eq hprefix.1, hinp_ns, hout_ns, ?_,
      fun i hidst => hread_other i hidst,
      hcellsP, hcells, hhead, hPinp, hPout, hPrest⟩
    · intro j hj
      have hj1 : j - 1 + 1 = j := by omega
      by_cases hle : j ≤ x.length
      · rw [← hj1, hprefix.2.1 (j - 1) (by omega)]
        cases x[j - 1]'(by omega) <;> decide
      · rw [← hj1, hprefix.2.2 (j - 1) (by omega)]
        decide
    · rw [hPout]; exact hout.1
  exact hcomb.strengthen_post (by
    rintro inp work out ⟨hhead1, hcellsP, hsc, hsh, hPinp, hPout, hPrest⟩
    exact ⟨hPinp, hPout, Tape.ext hhead1 hcellsP, hsc, hsh, hPrest⟩)

/-- Copy a work tape's value into another and park the result at cell `1`. -/
def copyToVirtualInputTM {n : ℕ} (src dst : Fin n) : TM n :=
  seqTM (copyWorkToWorkTM src dst) (rewindWorkTM dst)

/-- **The copy, with the whole tape family pinned down.** The source keeps its
cells but ends with its head past the copied value; the destination holds the
value parked at cell `1`; nothing else moves. This determined form is what
`TM.seqTM_det` chains. -/
theorem copyToVirtualInputTM_hoareTime {n : ℕ} (src dst : Fin n) (hne : src ≠ dst)
    (x : List Bool) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrcHead : (work₀ src).head = 1) (hsrcOut : (work₀ src).HasOutput x)
    (hsrcParked : Parked (work₀ src))
    (hdst : work₀ dst = (Tape.init []).move Dir3.right)
    (hinp : Parked inp₀) (hout : Parked out₀)
    (hother : ∀ i, i ≠ src → i ≠ dst → Parked (work₀ i)) :
    (copyToVirtualInputTM src dst).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (Function.update work₀ dst
            ((Tape.init (x.map Γ.ofBool)).move Dir3.right))
          src (⟨x.length + 1, (work₀ src).cells⟩ : Tape) ∧
        out = out₀)
      (2 * x.length + 5) := by
  refine (copyToVirtualInput_hoareTime src dst hne x inp₀ work₀ out₀ hsrcHead hsrcOut
    hsrcParked hdst hinp hout hother).strengthen_post ?_
  rintro inp work out ⟨hi, ho, hd, hsc, hsh, hrest⟩
  refine ⟨hi, ?_, ho⟩
  funext j
  by_cases hjs : j = src
  · rw [hjs, Function.update_self]
    exact Tape.ext (hjs ▸ hsh) (hjs ▸ hsc)
  · rw [Function.update_of_ne hjs]
    by_cases hjd : j = dst
    · rw [hjd, Function.update_self]
      exact hjd ▸ hd
    · rw [Function.update_of_ne hjd]
      exact hrest j hjs hjd

end TM

end Complexity
