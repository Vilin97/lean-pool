/-
Copyright (c) 2026 crdt-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: crdt-lean contributors
-/

import LeanPool.CrdtLean.Crdt.Defs
import LeanPool.CrdtLean.Crdt.Convergence
import LeanPool.CrdtLean.Crdt.Liveness
import LeanPool.CrdtLean.Crdt.Instances
import LeanPool.CrdtLean.Crdt.ORSet
import LeanPool.CrdtLean.Crdt.Sequence

/-!
# State-Based CRDT Convergence

Source: url:https://github.com/velvetmonkey/crdt-lean
Authors: crdt-lean contributors
Status: verified
Main declarations: `Crdt.strong_eventual_consistency`, `Crdt.RGA.read_strong_eventual_consistency`
Tags: distributed-systems, crdt, theoretical-computer-science
MSC: 68Q85
-/

/-!
This project formalizes convergence for state-based conflict-free replicated
data types.  The abstract development models a CRDT carrier as a join
semilattice with bottom, proves that delivery order and duplicate delivery
collapse to the join of the delivered update set, and packages a conditional
liveness theorem for fair delivery systems.

The concrete instances include grow-only sets, grow-only counters, PN-counters,
an observed-remove set with an add-wins theorem, and an RGA-style sequence CRDT
whose read operation is proved strongly eventually consistent.

Imported from <https://github.com/velvetmonkey/crdt-lean> (Lean v4.28.0) and
ported to Lean Pool's pinned Lean/Mathlib version.
-/
