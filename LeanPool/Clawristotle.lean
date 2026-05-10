/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import LeanPool.Clawristotle.Theorem42
import LeanPool.Clawristotle.CoulombConcreteTheorem42
import LeanPool.Clawristotle.CoulombNonvacuous

/-!
# Clawristotle: Vlasov-Maxwell-Landau steady-state classification

Source: arxiv:2603.15929
Authors: Vasily Ilin
Status: verified
Main declarations: `VML.Theorem42`, `VML.CoulombConcreteTheorem42`
Tags: pde, kinetic-theory, mathematical-physics
-/

/-!
## Mathematical overview

A `sorry`-free formalization of the Vlasov–Maxwell–Landau steady-state theorem
on the 3-torus with Coulomb collisions: any smooth positive steady-state
solution must be a global Maxwellian with vanishing electric field and constant
magnetic field.

- `VML.Theorem42` (abstract Theorem 4.2): for the abstract Vlasov–Maxwell–Landau
  system, any smooth steady state with the velocity-decay conditions is a global
  Maxwellian with `E = 0` and constant `B`.
- `VML.CoulombConcreteTheorem42` / `VML.CoulombConcreteTheorem42_classify_T`:
  the Coulomb-collision instantiation, with explicit temperature classification.
- `VML.CoulombConcreteTheorem42_nonvacuous`: non-vacuity of the Coulomb
  hypotheses.

The development includes the classical theory: H-theorem, entropy dissipation,
the flat-torus formalization, Gaussian normalization, and Newtonian-potential
bounds. (The Maxwell-molecules instantiation from upstream is not yet complete
and is not part of this import.)

## Provenance

Imported from <https://github.com/Vilin97/Clawristotle/tree/landau> (originally
Lean v4.24.0) and ported to Lean Pool's v4.30.0-rc2 / Mathlib v4.30.0-rc2.
Architecture and review by Vasily Ilin; implementation by Claude Code; informal
proof generation by Gemini DeepThink; 111 hard lemmas closed by Aristotle
(Harmonic). Technical report:
<https://github.com/Vilin97/Clawristotle/blob/landau/TECHNICAL_REPORT.md>;
agent logs: <https://huggingface.co/datasets/Vilin97/Clawristotle-Logs>.
-/
