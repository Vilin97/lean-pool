/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.PlanarStokes.Compat
import LeanPool.JacobianDiffgeo.PlanarStokes.CompactSupport
import LeanPool.JacobianDiffgeo.PlanarStokes.AnnulusResidue

/-!
# planar-stokes-atoms: compact-support planar Stokes for `dbar` and the smeared residue
# theorem (`RS`)

Purely planar (mathlib-only, plus `Jacobian.Dbar.Wirtinger`/`Jacobian.ResidueCalculus`; no
manifold imports). API summary (see `docs/design/planar-stokes.md`):

* **Compat**: `RS.wirtingerDbar_mul` (Leibniz rule for `dbar`, not in
  `Jacobian/Dbar/Wirtinger.lean`)
  and its holomorphic-factor/off-support specializations; `RS.ContDiffOn.contDiff_of_
  hasCompactSupport` (glue a `ContDiffOn` compactly-supported-in-`U` function to a global
  `ContDiff`); the `ℂ`-rectangle ↔ iterated-real-integral bridge
  (`RS.integral_eq_intervalIntegral_of_tsupport_subset_reProdIm`).
* **Atom 1** (`CompactSupport.lean`): `RS.integral_wirtingerDbar_eq_zero` — the `dbar` of a
  compactly-supported `C¹` function integrates to `0` over all of `ℂ`; and its holomorphic-
  multiplier corollary `RS.integral_wirtingerDbar_mul_eq_zero_of_differentiableOn` (Atom 1b, the
  "no pole in this chart" case).
* **Atom 1′** (`AnnulusResidue.lean`): `RS.circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_
  integral_wirtingerDbar` — the annulus Stokes identity (exp-substitution), general, no meromorphy.
* **Atom 2** (`AnnulusResidue.lean`, the smeared residue theorem):
  `RS.integral_wirtingerDbar_mul_eq_neg_pi_mul_resAt` — `∫∫ (dbarg)·f = -π·g(p)·resAt f p`, for `g`
  compactly supported and **locally constant near the puncture `p`** (this hypothesis is load-
  bearing — the fully general smeared-residue formula for merely-continuous `g` and a pole of
  order `≥ 2` is false, see the design's §D4/§8.1 Fourier-resonance analysis; residue-theorem's
  `ContDiffBump`-built partitions of unity satisfy it for free).
* **Model-case regression check + abel-weak-solutions refinement** (`AnnulusResidue.lean`):
  `RS.integral_wirtingerDbar_mul_inv_sub_eq` (`f = (·-p)⁻¹`, proved independently via
  `RS.cauchyPompeiu`, not via Atom 2 — cross-checks the `-π` constant) is stated **without** the
  `hpU`/`hconst` hypotheses of Atom 2's signature: both are provably unused at a simple pole (the
  design's own §8.4 observation), and dropping them is exactly the "cheap, bounded" refinement
  `abel-weak-solutions` needs (its `g` is a holomorphic primitive, not locally constant near its
  punctures — see `docs/design/abel-weak-solutions.md` §7.3/§10/§11 risk R1). Also exported:
  `RS.integrable_wirtingerDbar_mul_inv_sub` (the integrand is integrable) and
  `RS.integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq` (the exact two-puncture shape
  `f = (·-b)⁻¹ - (·-a)⁻¹`, `∫∫ (dbarg)·f = -π·(g b - g a)`, matching Forster's Lemma 20.3 assembly
  step directly, again for **any** `C¹` compactly-supported `g`).

Routing: residue-theorem consumes Atoms 1b/2 one chart at a time (PoU pieces), plus
`ResidueCalculus.resAt_comp_mul_deriv` (not from this unit) for chart-independence of `Res_p(ω)`
prior to summing; no "change of variables for the area integral" atom is designed or built here
(every integral here lives in one fixed chart, see §10). abel-weak-solutions consumes Atom 1b and
the three `integral_wirtingerDbar_mul_inv_sub*`/`integrable_wirtingerDbar_mul_inv_sub` exports
above for its Lemma-20.3 step — see the build-log entry for this unit for the full account.
-/
