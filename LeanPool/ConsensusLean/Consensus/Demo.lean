/-
Copyright (c) 2026 consensus-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: consensus-lean contributors
-/
import Mathlib.Data.Fin.Basic
import LeanPool.ConsensusLean.Consensus.Certificate

/-!
# Live demonstration — the certificate checker running on concrete scenarios

This file *executes* the verified bridge (`Consensus.Bridge`) on concrete data and proves
the verdicts. It is the reject-or-discharge core touching real (toy) certificates: the
same `check` an MCP Consensus-Seal sidecar would call, run here on a five-agent roster.

Every verdict below is proved by computation (`by decide`), so the
demo cannot drift from the theorems.

Scenario: five agents vote on a decision. Agents 0,1,2 vote `"ship"`, agents 3,4 vote
`"hold"`. The roster is all five, quorum is a strict majority (≥ 3 of 5).
-/

namespace Consensus.Demo

open Consensus.Bridge

/-- Five agents. -/
abbrev Agent := Fin 5

/-- The configuration: all five agents are authorised members. -/
def roster : Config Agent := ⟨{0, 1, 2, 3, 4}⟩

/-- The recorded votes: a 3–2 split in favour of `"ship"`. -/
def vote : Agent → Option String
  | 0 => some "ship"
  | 1 => some "ship"
  | 2 => some "ship"
  | 3 => some "hold"
  | 4 => some "hold"

/-- An honest majority certificate for `"ship"` (agents 0,1,2). Should be ACCEPTED. -/
def certShip : Cert Agent String := ⟨"ship", {0, 1, 2}⟩

/-- A `"hold"` certificate backed only by the 2-agent minority. Should be REJECTED
(not a strict majority). -/
def certHoldMinority : Cert Agent String := ⟨"hold", {3, 4}⟩

/-- A *forged* `"hold"` certificate: it lists a 3-agent majority {0,1,3}, but agents 0 and
1 actually voted `"ship"`. Should be REJECTED (recorded votes do not match the claim). -/
def certForged : Cert Agent String := ⟨"hold", {0, 1, 3}⟩

/-! ### The verdicts, computed and proved -/

-- Computed verdicts (run these, or the `consensus_demo` executable):

/-- The honest majority certificate is accepted. -/
example : check roster vote certShip = true := by decide

/-- A minority certificate is rejected. -/
example : check roster vote certHoldMinority = false := by decide

/-- A forged certificate (votes do not match) is rejected. -/
example : check roster vote certForged = false := by decide

/-- **The safety payoff, on concrete data.** Once the `"ship"` certificate is accepted,
*every* certificate the checker accepts against this roster must also carry `"ship"`. A
conflicting `"hold"` decision can never be discharged — proved, not just observed. -/
example (c : Cert Agent String) (h : check roster vote c = true) : c.value = "ship" :=
  no_conflicting_certs roster vote c certShip h (by decide)

/-! ### Reconfiguration: the roster shrinks, agreement survives -/

/-- After agent 4 leaves, the new roster is {0,1,2,3}. -/
def roster' : Config Agent := ⟨{0, 1, 2, 3}⟩

/-- A `"ship"` certificate under the new roster (agents 0,1,2 still a majority of 4). -/
def certShip' : Cert Agent String := ⟨"ship", {0, 1, 2}⟩

/-- The new certificate is accepted under the new roster. -/
example : check roster' vote certShip' = true := by decide

/-- **Cross-configuration agreement, on concrete data.** The old `"ship"` certificate and
the new one agree, because their voter counts (3 + 3) exceed the combined roster (|{0..4}|
= 5). Reconfiguration did not open a conflicting decision. -/
example : certShip.value = certShip'.value :=
  cert_agreement_cross roster roster' vote certShip certShip' (by decide) (by decide) (by decide)

/-! ### Runnable demo -/

private def verdict (b : Bool) : String :=
  if b then "ACCEPT discharged" else "REJECT blocked"

/-- Print the live verdict table. -/
def runDemo : IO Unit := do
  let honest := verdict (check roster vote certShip)
  let minority := verdict (check roster vote certHoldMinority)
  let forged := verdict (check roster vote certForged)
  let reconfigured := verdict (check roster' vote certShip')
  IO.println "-- Consensus Seal: verified certificate checker --"
  IO.println s!"  honest majority  ship  (agents 0,1,2)   {honest}"
  IO.println s!"  minority         hold  (agents 3,4)     {minority}"
  IO.println s!"  forged           hold  (agents 0,1,3)   {forged}"
  IO.println s!"  after reconfig   ship  (agents 0,1,2)   {reconfigured}"
  IO.println "-- Theorem: any accepted certificate carries \"ship\"."
  IO.println "   A conflicting decision can never be discharged."

-- Run the live verdict table (interpreter, no native build needed):

end Consensus.Demo
