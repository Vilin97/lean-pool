/-
Copyright (c) 2026 Vikraman Choudhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vikraman Choudhury
-/

import LeanPool.EventStructures.Basic
import LeanPool.EventStructures.Configuration
import LeanPool.EventStructures.Trace
import LeanPool.EventStructures.Path
import LeanPool.EventStructures.Computation
import LeanPool.EventStructures.FinitePoset
import LeanPool.EventStructures.Rollback
import LeanPool.EventStructures.Log
import LeanPool.EventStructures.Replay

/-!
# Event Structures and Causal-Consistent Reversibility

Source: url:https://github.com/vikraman/event-structures
Authors: Vikraman Choudhury
Status: verified
Main declarations: `EventStructures.EventStructure`, `EventStructures.Conf`
Tags: concurrency, order-theory, reversible-computation, event-structures
MSC: 68Q85, 06A06
-/

/-!
## Mathematical overview

Formalizes event structures (sets of events with a causal partial order and a
binary conflict relation) and several facts about causal-consistent
reversibility on them. The development defines configurations, computations,
traces and the trace monoid, paths between configurations, rollbacks (maximal
configurations omitting a chosen event), and replay (minimal and maximal
reconstructions of a configuration compatible with a log), and proves their
correctness, uniqueness and causal-safety properties.

## Provenance

Imported from <https://github.com/vikraman/event-structures>. Upstream is
Apache-2.0 licensed and contains no `sorry`s.
-/
