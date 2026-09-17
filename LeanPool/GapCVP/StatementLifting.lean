/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
import Mathlib.Computability.TuringMachine.StackTuringMachine

/-! # Transporting stack-machine statements into a larger machine -/

namespace GapCVP

open Turing

variable {K K' Λ Λ' σ σ' : Type*} {Γ : K' → Type*}

/-- Embed stack and label indices, preserve extra state through a read/write interface,
and replace the halt instruction with a caller-supplied continuation. -/
def liftStatement (stack : K → K') (label : Λ → Λ')
    (read : σ' → σ) (write : σ' → σ → σ') (onHalt : TM2.Stmt Γ Λ' σ') :
    TM2.Stmt (fun k => Γ (stack k)) Λ σ → TM2.Stmt Γ Λ' σ'
  | .push k f q => .push (stack k) (fun s => f (read s))
      (liftStatement stack label read write onHalt q)
  | .peek k f q => .peek (stack k) (fun s a => write s (f (read s) a))
      (liftStatement stack label read write onHalt q)
  | .pop k f q => .pop (stack k) (fun s a => write s (f (read s) a))
      (liftStatement stack label read write onHalt q)
  | .load f q => .load (fun s => write s (f (read s)))
      (liftStatement stack label read write onHalt q)
  | .branch test yes no => .branch (fun s => test (read s))
      (liftStatement stack label read write onHalt yes)
      (liftStatement stack label read write onHalt no)
  | .goto next => .goto (fun s => label (next (read s)))
  | .halt => onHalt

/-- A stack/state embedding that commutes with reads and updates transports an entire
statement execution. Only the caller's goto and halt configurations need separate proofs. -/
theorem liftStatement_stepAux [DecidableEq K] [DecidableEq K']
    (stack : K → K') (label : Λ → Λ')
    (read : σ' → σ) (write : σ' → σ → σ') (onHalt : TM2.Stmt Γ Λ' σ')
    (state : σ → σ')
    (embedStacks : (∀ k, List (Γ (stack k))) → ∀ k, List (Γ k))
    (configuration : TM2.Cfg (fun k => Γ (stack k)) Λ σ → TM2.Cfg Γ Λ' σ')
    (read_state : ∀ s, read (state s) = s)
    (write_state : ∀ s t, write (state s) t = state t)
    (read_stacks : ∀ source k, embedStacks source (stack k) = source k)
    (update_stacks : ∀ source k value,
      embedStacks (Function.update source k value) =
        Function.update (embedStacks source) (stack k) value)
    (goto_configuration : ∀ l s source,
      configuration ⟨some l, s, source⟩ = ⟨some (label l), state s, embedStacks source⟩)
    (halt_configuration : ∀ s source,
      TM2.stepAux onHalt (state s) (embedStacks source) = configuration ⟨none, s, source⟩)
    (statement : TM2.Stmt (fun k => Γ (stack k)) Λ σ) (s : σ)
    (source : ∀ k, List (Γ (stack k))) :
    TM2.stepAux (liftStatement stack label read write onHalt statement)
        (state s) (embedStacks source) =
      configuration (TM2.stepAux statement s source) := by
  induction statement generalizing s source with
  | push k f q ih =>
      simpa only [liftStatement, TM2.stepAux, read_state, read_stacks, update_stacks] using
        ih s (Function.update source k (f s :: source k))
  | peek k f q ih =>
      simpa only [liftStatement, TM2.stepAux, read_state, read_stacks, write_state] using
        ih (f s (source k).head?) source
  | pop k f q ih =>
      simpa only [liftStatement, TM2.stepAux, read_state, read_stacks, write_state,
        update_stacks] using ih (f s (source k).head?) (Function.update source k (source k).tail)
  | load f q ih =>
      simpa only [liftStatement, TM2.stepAux, read_state, write_state] using ih (f s) source
  | branch test yes no ihYes ihNo =>
      cases htest : test s <;>
        simp only [liftStatement, TM2.stepAux, read_state, htest, Bool.cond_false, Bool.cond_true]
      · exact ihNo s source
      · exact ihYes s source
  | goto next => simpa only [liftStatement, TM2.stepAux, read_state] using
      (goto_configuration (next s) s source).symm
  | halt => exact halt_configuration s source

end GapCVP
