/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.CoulombConcreteTheorem42
import LeanPool.Clawristotle.MaxwellMoleculesTheorem42
import LeanPool.Clawristotle.CoulombNonvacuous

/-!
# Clawristotle: Vlasov–Maxwell–Landau steady-state classification

A complete formalization (zero `sorry`s) of the Vlasov–Maxwell–Landau
steady-state theorem on the 3-torus with Coulomb collisions: any smooth
positive steady-state solution must be a global Maxwellian with vanishing
electric field and constant magnetic field.

## Main results

- `Theorem42` (abstract Theorem 4.2): for the abstract Vlasov–Maxwell–Landau
  system, any smooth steady state with the velocity-decay conditions is a
  global Maxwellian with `E = 0` and constant `B`.
- `CoulombConcreteTheorem42` and `CoulombConcreteTheorem42_classify_T`:
  the Coulomb-collision instantiation, with explicit temperature classification.
- `MaxwellMoleculesTheorem42`: the Maxwell-molecules instantiation.
- `CoulombNonvacuous`: non-vacuity of the Coulomb-collision hypotheses.

The classical theory: H-theorem, entropy dissipation, flat-torus formalization,
Gaussian normalization, and Newtonian-potential bounds.

## Source

- Paper: <https://arxiv.org/abs/2603.15929>
- Upstream Lean: <https://github.com/Vilin97/Clawristotle/tree/landau>
- Technical report:
  <https://github.com/Vilin97/Clawristotle/blob/landau/TECHNICAL_REPORT.md>
- Agent logs: <https://huggingface.co/datasets/Vilin97/Clawristotle-Logs>

## Authors

Vasily Ilin (architect / reviewer), with Claude Code (implementation),
Gemini DeepThink (informal proof generation), and Aristotle / Harmonic
(automated theorem prover for 111 hard lemmas).

## Status

Imported from `Vilin97/Clawristotle@landau` (originally Lean v4.24.0).
Lean Pool currently pins Lean v4.30.0-rc2 / Mathlib v4.30.0-rc2; this
import is **expected to need porting work** before the build is clean.
Upstream is `0 sorry`'s; the import preserves the proofs verbatim and
will earn the same status once the v4.24 → v4.30 Mathlib API drift is
addressed.
-/
