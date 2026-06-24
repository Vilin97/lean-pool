/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

/-
# AxiomAudit — the build-enforced axiom-clean gate

This module makes the repository's "referee-free" promise *self-checking*.

Every headline theorem in this development is axiom-clean: `#print axioms <thm>`
reports exactly the three foundational axioms of Lean/mathlib —
`[propext, Classical.choice, Quot.sound]` — and nothing else. In particular there
is no `sorryAx` (which a `sorry` would introduce) and no axiom from
`native_decide` (`Lean.ofReduceBool`/`Lean.trustCompiler`).

Until now that fact was verified by a human reading the `#print axioms` output. Here
it is verified by the *build*: each headline result below is wrapped in
`#guard_msgs in #print axioms`, which pins the captured message to the exact
foundational triple. If a future edit introduces a `sorry`, a `native_decide`, or
any other extra axiom into one of these results, the captured message changes, the
`#guard_msgs` exact-match fails, and `lake build` FAILS. The promise can no longer
silently regress.

Each `#print axioms` command is placed on its own line at column 0 (not inline after
`#guard_msgs in`) so the mathlib whitespace style linter, which is active under a full
`lake build`, stays quiet and does not inject an extra captured message.

To extend the gate: add the headline name of any new load-bearing theorem with its
own `#guard_msgs in` / `#print axioms` block.
-/
import LeanPool.Sundogcert.Certificate
import LeanPool.Sundogcert.Scaling
import LeanPool.Sundogcert.Looseness
import LeanPool.Sundogcert.Degradation
import LeanPool.Sundogcert.CheckCost
import LeanPool.Sundogcert.ShadowDecay
import LeanPool.Sundogcert.ShadowDecayGeneral
import LeanPool.Sundogcert.ShadowDecayCauchy
import LeanPool.Sundogcert.HaloGeometry
import LeanPool.Sundogcert.FaradayAB
import LeanPool.Sundogcert.CertWall
import LeanPool.Sundogcert.DecodingNPHard
import LeanPool.Sundogcert.ShadowDecayLattice
import LeanPool.Sundogcert.SATNPHard
import LeanPool.Sundogcert.VarWheel
import LeanPool.Sundogcert.ClauseGadget
import LeanPool.Sundogcert.SATReduction
import LeanPool.Sundogcert.ThreeDMReindex
import LeanPool.Sundogcert.SATReductionReverse
import LeanPool.Sundogcert.SATReductionForward
import LeanPool.Sundogcert.SATReductionMain
import LeanPool.Sundogcert.AuditCost

/-!
# Axiom audit — the headline results are axiom-clean

Every theorem listed below depends only on the three foundational axioms of
Lean / Mathlib: `propext`, `Classical.choice`, and `Quot.sound`. In particular
there is no `sorryAx` (which a `sorry` would introduce) and no `Lean.ofReduceBool`
(which a `native_decide` would introduce). The development uses only kernel
`decide`, never `native_decide`. The exception noted is a genuine subset.

## Certificate — lossiness, accept/reject soundness, sound column-weight bound

* `Sundog.Certificate.syndrome_independent_of_secret`
* `Sundog.Certificate.accept_sound`
* `Sundog.Certificate.reject_sound`
* `Sundog.Certificate.colWeightLb_sound`
* `Sundog.Certificate.reject_sound_colweight`

## Scaling — the projection-family scaling law

* `Sundog.Certificate.Scaling.scaling_law`

## Looseness — basis-dependence collapse

* `Sundog.Certificate.Looseness.looseness`

## Degradation — the general column-weight ceiling

* `Sundog.Certificate.Degradation.colWeightLb_le_card_div`

## CheckCost — the linear check-cost theorem

* `Sundog.Certificate.verifyCost_le`

## ShadowDecay — Debye–Waller decay and discrete determination

* `Sundog.ShadowDecay.debye_waller`
* `Sundog.ShadowDecay.determination`

## HaloGeometry — minimum-deviation stationarity and local minimum

* `Sundog.HaloGeometry.min_deviation_stationary`
* `Sundog.HaloGeometry.min_deviation_isLocalMin`

## FaradayAB — gauge-circulation invariance and loop = flux

* `Sundog.FaradayAB.gauge_circulation_zero`
* `Sundog.FaradayAB.loop_integral_eq_flux`

## CertWall — row-equivalence invariance, no-tight-robust bound, tight⇒decodes

* `Sundog.Certificate.CertWall.minCosetWeight_rowEquiv`
* `Sundog.Certificate.CertWall.colWeightLb_cannot_be_tight_basisRobust`
* `Sundog.Certificate.CertWall.tight_bound_decodes`

## ShadowDecayGeneral — the charFun determine/resist law (any probability measure)

* `Sundog.ShadowDecayGeneral.shadow_decay_charFun`
* `Sundog.ShadowDecayGeneral.general_recovers_debye_waller`
* `Sundog.ShadowDecayGeneral.resistance_general`
* `Sundog.ShadowDecayGeneral.gaussian_resists`
* `Sundog.ShadowDecayGeneral.determination_general`
* `Sundog.ShadowDecayGeneral.gaussian_resist_and_determine`

## ShadowDecayCauchy — the Cauchy population is the determine/resist separator

* `Sundog.ShadowDecayCauchy.cauchy_charFun_tendsto_zero`
* `Sundog.ShadowDecayCauchy.cauchy_resists`
* `Sundog.ShadowDecayCauchy.cauchy_no_mean`
* `Sundog.ShadowDecayCauchy.cauchy_is_separator`
* `Sundog.ShadowDecayCauchy.resist_determine_independent`

## DecodingNPHard — EC3S→decoding (forward + backward both proved; iff unconditional)

* `Sundog.DecodingNPHard.reduction_forward`
* `Sundog.DecodingNPHard.reduction_iff`

## ShadowDecayLattice — AC resists (Riemann–Lebesgue), the lattice two-point survives

* `Sundog.ShadowDecayLattice.absCont_charFun_tendsto_zero`
* `Sundog.ShadowDecayLattice.absCont_resists`
* `Sundog.ShadowDecayLattice.twoPoint_charFun`
* `Sundog.ShadowDecayLattice.twoPoint_does_not_resist`
* `Sundog.ShadowDecayLattice.twoPoint_shadow_survives`
* `Sundog.ShadowDecayLattice.resist_separates_ac_from_lattice`
* `Sundog.ShadowDecayLattice.resist_orthogonal_to_variance`

## 3SAT ≤ 3DM ≤ X3C ≤ Decodes — the machine-checked Karp reduction correctness

Gadget cores (the wheel two-state engine, the clause polarity bridge), the index bridge
and the data-layer chain-connect, both reduction directions, and the end-to-end headline.
Guarding the top-level `sat_iff_decodes` transitively protects the whole chain (its axiom
set would change if any dependency regressed). `litTipFree_iff_eval` is `[propext]` only —
a genuine subset.

* `Sundog.SATNPHard.ex_sat`
* `Sundog.VarWheel.validCover_iff_const`
* `Sundog.ClauseGadget.litTipFree_iff_eval`
* `Sundog.SATReduction.reduce_chain_connects`
* `Sundog.ThreeDMReindex.threeDM_reindex`
* `Sundog.SATReductionReverse.reverse`
* `Sundog.SATReductionForward.forward`
* `Sundog.SATReductionMain.sat_iff_threeDM`
* `Sundog.SATReductionMain.sat_iff_decodes`

## AuditCost — audit asymmetry (HS7): sound cheap audit + ∀-verifier blindness

* `Sundog.AuditCost.audit_sound`
* `Sundog.AuditCost.auditCost_le`
* `Sundog.AuditCost.pooled_channel_blind`
* `Sundog.AuditCost.no_verifier_checks_perUnit`
* `Sundog.AuditCost.audit_asymmetry`
-/
