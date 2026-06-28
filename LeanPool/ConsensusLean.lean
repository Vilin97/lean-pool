/-
Copyright (c) 2026 consensus-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: consensus-lean contributors
-/

import LeanPool.ConsensusLean.Consensus
import LeanPool.ConsensusLean.CheckerMain

/-!
# Consensus Safety and Executable Certificate Checking

Source: url:https://github.com/velvetmonkey/consensus-lean
Authors: consensus-lean contributors
Status: verified
Main declarations: `Consensus.agreement`, `Consensus.Checker.agreement`
Tags: distributed-systems, consensus, theoretical-computer-science
MSC: 68Q85
-/

/-!
This project formalizes the safety core of quorum-based consensus.  A quorum
system is modeled by a family of finite acceptor sets with pairwise
intersection; from that single assumption the development proves agreement and
validity, specializes the result to strict-majority quorums, and extends it
across compatible reconfigurations.

The project also includes an executable certificate bridge.  Concrete
certificates over finite rosters have a decidable acceptance predicate, and
`Consensus.Bridge.cert_agreement` proves that two accepted certificates cannot
carry different values.  `Consensus.Checker.agreement` repeats the guarantee for
the extracted list-based checker used by the small runtime entry point.

Imported from <https://github.com/velvetmonkey/consensus-lean> (Lean v4.28.0)
and ported to Lean Pool's pinned Lean/Mathlib version.
-/
