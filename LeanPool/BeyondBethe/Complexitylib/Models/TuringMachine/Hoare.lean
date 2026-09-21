/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Seq
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.If
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Complement

/-!
# Hoare-style composition rules for TM combinators

This file provides Hoare-triple composition rules for all four TM combinators.
Each rule specifies how pre/postconditions and time bounds compose.

## Main results

- `seqTM_hoareTime` — sequential composition: time `b₁ + 1 + b₂`
- `phaseTransition_eq_self_of_reads_ne_start` — identify a stable phase boundary
- `complementTM_hoareTime` — complement flips output cell 1: time `b + p_bound + 4`
- `ifTM_hoareTime` — if-then-else branching: time `b_test + p_bound + max b_then b_else + 5`
- `loopTM_hoareTime` — loop invariant with variant: time `(k + 1) * b_iter`

## Tape transition effects

All combinators apply `transitionTape` / `transitionInput` at phase boundaries.
A current read other than `▷` is exactly what their fixed-point rules require;
parked tapes, or `AllTapesWF` together with positive-head facts, provide common
stronger certificates.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **Sequential composition of Hoare triples**. -/
theorem seqTM_hoareTime (tm₁ tm₂ : TM n)
    {pre mid mid' post : TapePred n} {b₁ b₂ : ℕ}
    (h₁ : tm₁.HoareTime pre mid b₁)
    (h_trans : ∀ inp work out, mid inp work out →
        mid' (transitionInput inp)
             (fun i => transitionTape (work i))
             (transitionTape out))
    (h₂ : tm₂.HoareTime mid' post b₂) :
    (seqTM tm₁ tm₂).HoareTime pre post (b₁ + 1 + b₂) := by
  intro inp work out hpre
  obtain ⟨c₁, t₁, ht₁, hreach₁, hhalt₁, hmid⟩ := h₁ inp work out hpre
  have hmid' := h_trans c₁.input c₁.work c₁.output hmid
  obtain ⟨c₂, t₂, ht₂, hreach₂, hhalt₂, hpost⟩ := h₂ _ _ _ hmid'
  refine ⟨phase2Wrap tm₁ tm₂ c₂, t₁ + 1 + t₂, ?_, ?_, ?_, ?_⟩
  · omega
  · convert seqTM_reachesIn_of_reachesIn tm₁ tm₂ hreach₁ hhalt₁ hreach₂ using 1
  · rw [phase2Wrap_halted_iff]; exact hhalt₂
  · exact hpost

/-- The input, work family, and output transition maps are jointly the
identity when every tape is reading something other than the left-end marker.
This shared read-local boundary certificate matches the transition shape
accepted by both time-only and time-space sequential composition; it
deliberately does not require parked heads or global tape well-formedness. -/
theorem phaseTransition_eq_self_of_reads_ne_start
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : inp.read ≠ Γ.start)
    (hwork : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    transitionInput inp = inp ∧
      (fun i => transitionTape (work i)) = work ∧
      transitionTape out = out := by
  exact ⟨transitionInput_eq_self hinput,
    funext fun i => transitionTape_eq_self (hwork i),
    transitionTape_eq_self houtput⟩

/-- Well-formedness condition on all tapes: cells 0 = start and cells ≥ 1 ≠ start. -/
def AllTapesWF (inp : Tape) (work : Fin n → Tape) (out : Tape) : Prop :=
  inp.cells 0 = Γ.start ∧ (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧
  (∀ i, (work i).cells 0 = Γ.start) ∧ (∀ i j, j ≥ 1 → (work i).cells j ≠ Γ.start) ∧
  out.cells 0 = Γ.start ∧ (∀ j, j ≥ 1 → out.cells j ≠ Γ.start)

-- ════════════════════════════════════════════════════════════════════════
-- AllTapesWF propagation through phase transitions
-- ════════════════════════════════════════════════════════════════════════

/-- AllTapesWF is preserved through the standard combinator phase transition
    (`transitionTape` / `transitionInput`). -/
theorem AllTapesWF.transition {inp : Tape} {work : Fin n → Tape} {out : Tape}
    (h : AllTapesWF inp work out) :
    (transitionInput inp).head ≥ 1 ∧
    (∀ j, j ≥ 1 → (transitionInput inp).cells j ≠ Γ.start) ∧
    (∀ i, (transitionTape (work i)).head ≥ 1) ∧
    (∀ i j, j ≥ 1 → (transitionTape (work i)).cells j ≠ Γ.start) ∧
    (transitionTape out).cells = out.cells ∧
    (transitionTape out).head ≥ 1 := by
  obtain ⟨hic0, hins, hwc0, hwns, hoc0, hons⟩ := h
  exact ⟨transitionInput_head_ge inp hic0,
    by rw [transitionInput_cells]; exact hins,
    fun i => one_le_head_transitionTape _ (hwc0 i),
    fun i j hj => by rw [transitionTape_cells _ (hwns i)]; exact hwns i j hj,
    transitionTape_cells out hons,
    one_le_head_transitionTape out hoc0⟩

-- ════════════════════════════════════════════════════════════════════════
-- Complement rule
-- ════════════════════════════════════════════════════════════════════════

/-- **Complement Hoare triple**. If `tm` satisfies a Hoare triple whose
    postcondition provides output WF (for rewind), a head bound, and a
    property of output cell 1, then `complementTM tm` satisfies a triple
    where output cell 1 is flipped. Time: `b + p_bound + 4`. -/
theorem complementTM_hoareTime (tm : TM n)
    {pre : TapePred n} {b p_bound : ℕ}
    {cell1_pred : Γ → Prop}
    (h_tm : tm.HoareTime pre
      (fun _ _ out =>
        out.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
        out.head ≤ p_bound ∧
        cell1_pred (out.cells 1))
      b) :
    tm.complementTM.HoareTime pre
      (fun _ _ out => ∃ g, cell1_pred g ∧ out.cells 1 = (flipBit g).toΓ)
      (b + p_bound + 4) := by
  intro inp work out hpre
  obtain ⟨c', t, ht, hreach, hhalt, hcell0, hnostart, hhead, hcell1⟩ :=
    h_tm inp work out hpre
  have hsim := complementTM_simulation tm hreach
  rw [compCfg_qstart] at hsim
  obtain ⟨c_done, t_rw, hreach_rw, hhalt_done, hflip, hle_rw⟩ :=
    complementTM_rewind_and_flip tm c' hhalt hcell0 hnostart
  exact ⟨c_done, t + t_rw,
    by have : t_rw ≤ p_bound + 4 := le_trans hle_rw (by omega); omega,
    reachesIn_trans _ hsim hreach_rw, hhalt_done,
    c'.output.cells 1, hcell1, hflip⟩

-- ════════════════════════════════════════════════════════════════════════
-- If-then-else rule
-- ════════════════════════════════════════════════════════════════════════

/-- **If-then-else Hoare triple**. Composes test, then-branch, and else-branch
    Hoare triples. The test postcondition must include `AllTapesWF` (for rewind)
    and a head bound. Branch routing maps the test postcondition to the branch
    precondition on transitioned tapes (output gets head = 1, cells preserved).

    Time: `b_test + p_bound + max b_then b_else + 5`
    (test + transition + rewind + check + branch + halt). -/
theorem ifTM_hoareTime (tmTest tmThen tmElse : TM n)
    {pre mid_test mid_then mid_else post_then post_else post : TapePred n}
    {b_test b_then b_else p_bound : ℕ}
    (h_test : tmTest.HoareTime pre mid_test b_test)
    (h_wf : ∀ inp work out, mid_test inp work out → AllTapesWF inp work out)
    (h_head : ∀ inp work out, mid_test inp work out → out.head ≤ p_bound)
    (h_to_then : ∀ inp work out, mid_test inp work out → out.cells 1 = Γ.one →
      mid_then (transitionInput inp) (fun i => transitionTape (work i))
               ⟨1, out.cells⟩)
    (h_to_else : ∀ inp work out, mid_test inp work out → out.cells 1 ≠ Γ.one →
      mid_else (transitionInput inp) (fun i => transitionTape (work i))
               ⟨1, out.cells⟩)
    (h_then : tmThen.HoareTime mid_then post_then b_then)
    (h_else : tmElse.HoareTime mid_else post_else b_else)
    (h_post_then : ∀ inp work out, post_then inp work out →
      post (transitionInput inp) (fun i => transitionTape (work i))
           (transitionTape out))
    (h_post_else : ∀ inp work out, post_else inp work out →
      post (transitionInput inp) (fun i => transitionTape (work i))
           (transitionTape out)) :
    (ifTM tmTest tmThen tmElse).HoareTime pre post
      (b_test + p_bound + max b_then b_else + 5) := by
  intro inp work out hpre
  obtain ⟨c_test, t₁, ht₁, hreach₁, hhalt₁, hmid⟩ := h_test inp work out hpre
  have hwf := h_wf _ _ _ hmid
  have hhead_bound := h_head _ _ _ hmid
  obtain ⟨hic0, hins, hwc0, hwns, hoc0, hons⟩ := hwf
  -- Phase 1: test simulation
  have hsim := ifTM_reachesIn_ifTestWrap tmTest tmThen tmElse hreach₁
  -- Phase 2: test → rewind transition (1 step)
  have h_tr := ifTM_test_to_rewind tmTest tmThen tmElse hhalt₁
  -- Phase 3: rewind loop (tracks all tapes, using AllTapesWF propagation)
  obtain ⟨h_inp_ge, h_inp_ns, h_work_ge, h_work_ns, h_out_cells, _⟩ :=
    AllTapesWF.transition (h_wf _ _ _ hmid)
  have h_out_head_bound := head_transitionTape_le hoc0 hhead_bound
  obtain ⟨c_check, hreach_rw, hst_check, hh_check, hcells_check, hinp_check, hwork_check⟩ :=
    ifTM_rewindOut_reachesIn_check tmTest tmThen tmElse (transitionTape c_test.output).head
      { state := Sum.inr (Sum.inl IfPhase.rewindOut),
        input := transitionInput c_test.input,
        work := fun i => transitionTape (c_test.work i),
        output := transitionTape c_test.output }
      rfl (by rw [h_out_cells]; exact hoc0)
      (by intro j hj; rw [h_out_cells]; exact hons j hj) rfl
      h_inp_ge h_inp_ns h_work_ge h_work_ns
  -- Phase 4: check + branch (cases on output cell 1)
  -- Derive invariants on the check config from rewind results
  have hcells_at_check : c_check.output.cells 1 = c_test.output.cells 1 := by
    rw [hcells_check, h_out_cells]
  have hns_at_check : ∀ j, j ≥ 1 → c_check.output.cells j ≠ Γ.start := by
    intro j hj; rw [hcells_check, h_out_cells]; exact hons j hj
  have hinp_stable : c_check.input.head ≥ 1 := by rw [hinp_check]; exact h_inp_ge
  have hins_stable : ∀ j, j ≥ 1 → c_check.input.cells j ≠ Γ.start := by
    intro j hj; rw [hinp_check]; exact h_inp_ns j hj
  have hwh_stable : ∀ i, (c_check.work i).head ≥ 1 := by
    intro i; rw [hwork_check]; exact h_work_ge i
  have hwns_stable : ∀ i j, j ≥ 1 → (c_check.work i).cells j ≠ Γ.start := by
    intro i j hj; rw [hwork_check]; exact h_work_ns i j hj
  -- Time for transition + rewind
  have hreach_tr_rw : (ifTM tmTest tmThen tmElse).reachesIn
      (1 + ((transitionTape c_test.output).head + 1))
      (ifTestWrap tmTest tmThen tmElse c_test) c_check :=
    reachesIn_trans _ (.step h_tr .zero) hreach_rw
  -- Branch on output cell 1
  by_cases hcell1 : c_test.output.cells 1 = Γ.one
  · -- Then branch
    obtain ⟨c_branch, hstep_check, hst_branch, hcells_branch, hhead_branch,
            hinp_branch, hwork_branch⟩ :=
      ifTM_check_step_then_full tmTest tmThen tmElse c_check hst_check hh_check
        (by rw [hcells_at_check]; exact hcell1) hinp_stable hins_stable hwh_stable hwns_stable
    have hmid_then := h_to_then c_test.input c_test.work c_test.output hmid hcell1
    obtain ⟨c_then, t₃, ht₃, hreach₃, hhalt₃, hpost_then⟩ :=
      h_then _ _ _ hmid_then
    have hsim₃ := ifTM_reachesIn_ifThenWrap tmTest tmThen tmElse hreach₃
    have h_halt_step := ifTM_then_halt_step tmTest tmThen tmElse hhalt₃
    have hpost := h_post_then c_then.input c_then.work c_then.output hpost_then
    -- Compose: test sim + transition + rewind + check + branch sim + halt
    let c_done : Cfg n (ifTM tmTest tmThen tmElse).Q :=
      ⟨(ifTM tmTest tmThen tmElse).qhalt,
       transitionInput c_then.input,
       fun i => transitionTape (c_then.work i),
       transitionTape c_then.output⟩
    refine ⟨c_done, t₁ + (1 + ((transitionTape c_test.output).head + 1)) + 1 + t₃ + 1,
      ?_, ?_, ?_, ?_⟩
    · have : (transitionTape c_test.output).head + 1 ≤ p_bound + 2 := by omega
      calc t₁ + _ + 1 + t₃ + 1
          ≤ b_test + (1 + (p_bound + 2)) + 1 + b_then + 1 := by omega
        _ ≤ b_test + p_bound + max b_then b_else + 5 := by omega
    · have hstep_branch : (ifTM tmTest tmThen tmElse).step c_check =
          some (ifThenWrap tmTest tmThen tmElse
            ⟨tmThen.qstart, transitionInput c_test.input,
             fun i => transitionTape (c_test.work i), ⟨1, c_test.output.cells⟩⟩) := by
        rw [hstep_check]; congr 1; simp only [ifThenWrap]
        have hcfg_eta : c_branch =
            ⟨c_branch.state, c_branch.input, c_branch.work, c_branch.output⟩ := rfl
        have htape_eta : c_branch.output =
            ⟨c_branch.output.head, c_branch.output.cells⟩ := rfl
        rw [hcfg_eta, hst_branch, hinp_branch, hinp_check, hwork_branch, hwork_check,
            htape_eta, hhead_branch]
        congr 1; simp only [hcells_branch, hcells_check, h_out_cells]
      have r1 := reachesIn_trans _ hsim hreach_tr_rw
      have r2 := reachesIn_trans _ r1 (.step hstep_branch .zero)
      have r3 := reachesIn_trans _ r2 hsim₃
      exact reachesIn_trans _ r3 (.step h_halt_step .zero)
    · exact ifTM_halted_of_state_eq_done tmTest tmThen tmElse _ rfl
    · exact hpost
  · -- Else branch (symmetric)
    obtain ⟨c_branch, hstep_check, hst_branch, hcells_branch, hhead_branch,
            hinp_branch, hwork_branch⟩ :=
      ifTM_check_step_else_full tmTest tmThen tmElse c_check hst_check hh_check
        (by rw [hcells_at_check]; exact hcell1) hns_at_check
        hinp_stable hins_stable hwh_stable hwns_stable
    have hmid_else := h_to_else c_test.input c_test.work c_test.output hmid hcell1
    obtain ⟨c_else, t₃, ht₃, hreach₃, hhalt₃, hpost_else⟩ :=
      h_else _ _ _ hmid_else
    have hsim₃ := ifTM_reachesIn_ifElseWrap tmTest tmThen tmElse hreach₃
    have h_halt_step := ifTM_else_halt_step tmTest tmThen tmElse hhalt₃
    have hpost := h_post_else c_else.input c_else.work c_else.output hpost_else
    let c_done_else : Cfg n (ifTM tmTest tmThen tmElse).Q :=
      ⟨(ifTM tmTest tmThen tmElse).qhalt,
       transitionInput c_else.input,
       fun i => transitionTape (c_else.work i),
       transitionTape c_else.output⟩
    refine ⟨c_done_else, t₁ + (1 + ((transitionTape c_test.output).head + 1)) + 1 + t₃ + 1,
      ?_, ?_, ?_, ?_⟩
    · have : (transitionTape c_test.output).head + 1 ≤ p_bound + 2 := by omega
      calc t₁ + _ + 1 + t₃ + 1
          ≤ b_test + (1 + (p_bound + 2)) + 1 + b_else + 1 := by omega
        _ ≤ b_test + p_bound + max b_then b_else + 5 := by omega
    · have hstep_branch : (ifTM tmTest tmThen tmElse).step c_check =
          some (ifElseWrap tmTest tmThen tmElse
            ⟨tmElse.qstart, transitionInput c_test.input,
             fun i => transitionTape (c_test.work i), ⟨1, c_test.output.cells⟩⟩) := by
        rw [hstep_check]; congr 1; simp only [ifElseWrap]
        have hcfg_eta : c_branch =
            ⟨c_branch.state, c_branch.input, c_branch.work, c_branch.output⟩ := rfl
        have htape_eta : c_branch.output =
            ⟨c_branch.output.head, c_branch.output.cells⟩ := rfl
        rw [hcfg_eta, hst_branch, hinp_branch, hinp_check, hwork_branch, hwork_check,
            htape_eta, hhead_branch]
        congr 1; simp only [hcells_branch, hcells_check, h_out_cells]
      have r1 := reachesIn_trans _ hsim hreach_tr_rw
      have r2 := reachesIn_trans _ r1 (.step hstep_branch .zero)
      have r3 := reachesIn_trans _ r2 hsim₃
      exact reachesIn_trans _ r3 (.step h_halt_step .zero)
    · exact ifTM_halted_of_state_eq_done tmTest tmThen tmElse _ rfl
    · exact hpost

-- ════════════════════════════════════════════════════════════════════════
-- Loop invariant rule
-- ════════════════════════════════════════════════════════════════════════

private theorem loopTM_hoareTime_aux (tmBody tmTest : TM n)
    {inv post : TapePred n} {b_iter : ℕ}
    {variant : Tape → (Fin n → Tape) → Tape → ℕ}
    (h_iter : ∀ inp work out, inv inp work out →
      (∃ c' t, t ≤ b_iter ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (loopTM tmBody tmTest).halted c' ∧
        post c'.input c'.work c'.output)
      ∨
      (∃ inp' work' out' t, t ≤ b_iter ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩
          ⟨(loopTM tmBody tmTest).qstart, inp', work', out'⟩ ∧
        inv inp' work' out' ∧
        variant inp' work' out' < variant inp work out))
    (fuel : ℕ) :
    ∀ inp work out, inv inp work out → variant inp work out ≤ fuel →
      ∃ c' t, t ≤ (fuel + 1) * b_iter ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (loopTM tmBody tmTest).halted c' ∧
        post c'.input c'.work c'.output := by
  induction fuel with
  | zero =>
    intro inp work out hinv hfuel
    cases h_iter inp work out hinv with
    | inl h =>
      obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := h
      exact ⟨c', t, le_trans ht (by omega), hreach, hhalt, hpost⟩
    | inr h =>
      obtain ⟨_, _, _, _, _, _, _, hvar_dec⟩ := h
      omega
  | succ fuel ih =>
    intro inp work out hinv hfuel
    cases h_iter inp work out hinv with
    | inl h =>
      obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := h
      refine ⟨c', t, le_trans ht ?_, hreach, hhalt, hpost⟩
      calc b_iter = 1 * b_iter := (Nat.one_mul _).symm
        _ ≤ (fuel + 1 + 1) * b_iter := Nat.mul_le_mul_right _ (by omega)
    | inr h =>
      obtain ⟨inp', work', out', t₁, ht₁, hreach₁, hinv', hvar_dec⟩ := h
      have hfuel' : variant inp' work' out' ≤ fuel := by omega
      obtain ⟨c', t₂, ht₂, hreach₂, hhalt, hpost⟩ := ih inp' work' out' hinv' hfuel'
      refine ⟨c', t₁ + t₂, ?_, reachesIn_trans _ hreach₁ hreach₂, hhalt, hpost⟩
      calc t₁ + t₂
          ≤ b_iter + (fuel + 1) * b_iter := Nat.add_le_add ht₁ ht₂
        _ = (fuel + 1) * b_iter + b_iter := Nat.add_comm _ _
        _ = (fuel + 1 + 1) * b_iter := (Nat.succ_mul _ _).symm

/-- **Loop invariant rule**. Each iteration (≤ `b_iter` steps) either halts with
    `post` or returns to the loop start with `inv` preserved and `variant` decreased.
    The `variant` is bounded by `k` under `inv`, giving total time `(k + 1) * b_iter`. -/
theorem loopTM_hoareTime (tmBody tmTest : TM n)
    {inv post : TapePred n} {b_iter k : ℕ}
    {variant : Tape → (Fin n → Tape) → Tape → ℕ}
    (h_variant_bound : ∀ inp work out, inv inp work out → variant inp work out ≤ k)
    (h_iter : ∀ inp work out, inv inp work out →
      (∃ c' t, t ≤ b_iter ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (loopTM tmBody tmTest).halted c' ∧
        post c'.input c'.work c'.output)
      ∨
      (∃ inp' work' out' t, t ≤ b_iter ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩
          ⟨(loopTM tmBody tmTest).qstart, inp', work', out'⟩ ∧
        inv inp' work' out' ∧
        variant inp' work' out' < variant inp work out)) :
    (loopTM tmBody tmTest).HoareTime inv post ((k + 1) * b_iter) := by
  intro inp work out hinv
  exact loopTM_hoareTime_aux tmBody tmTest h_iter k inp work out hinv
    (h_variant_bound inp work out hinv)

end TM

end Complexity
