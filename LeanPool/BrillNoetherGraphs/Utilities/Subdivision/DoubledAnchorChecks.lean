/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ExplicitPotential

/-!
# Doubled-anchor rows for an explicit-potential certificate

Two executable rows that a *marked* leaf needs and an unmarked one does not:

* `dominatesMarkCheck` — the certificate's core divisor carries at least
  `chips` chips at a distinguished vertex, and nothing negative anywhere.  This
  is `W7` read at a mark.
* `multResidualCheck` — the `W5` residual table read with multiplicity `mult`
  at an anchor rather than with multiplicity one.  `multTargetCoefficient` is
  the single arithmetic definition it needs, and it is `targetCoefficient` on
  the nose at `mult = 1`.

Both are `allFin`/`decide` Booleans over `Fin n`, so an emitter discharges them
on concrete data and the kernel replays them.  Each comes with the `Prop` it
characterizes and an `iff`, so a consumer may use either form.

These lived in `MarkedGraphs/Certificate/DegenerateDoubledAnchor.lean` until
2026-08-31.  Nothing about them is specific to a genus, a row, or a
marked-graph existence statement, and the generic row-proof checker under
`Utilities/Subdivision/ClosedRowProof/` needs them to state its marked leaf
checkers, so they belong on this side of the boundary.  The *soundness*
theorems that consume them — `effective_degenerateDivisor_sub_smul_one_chip`,
`class_mult_balance_nonnegative`,
`winnable_sub_smul_one_chip_degenerateCoreVertex` — stay private, where their
only consumers are.
-/

@[expose] public section

-- The established name of the certificate namespace repeats `Certificate`,
-- which is what `ExplicitPotential.Certificate` means.  Lean v4.33 added
-- `linter.dupNamespace`, which flags exactly this shape.
namespace Utilities.Certificate.ExplicitPotential.Certificate

open Utilities
open Utilities.Certificate
open Finset ExplicitPotential

variable {m n p : ℕ}

/-! ## W7 at a mark: the divisor dominates, point-independently -/

/-- **The checker's W7 domination row.**  The core divisor carries at least
`chips` chips at `mark` and nothing negative anywhere else.  Written as a
single uniform inequality so that the Boolean form below is one `allFin`. -/
def DominatesMark (certificate : Certificate m n p) (mark : Fin n)
    (chips : ℤ) : Prop :=
  ∀ vertex : Fin n,
    0 ≤ certificate.divisor vertex - if vertex = mark then chips else 0

/-- Executable form of `DominatesMark`, for an emitter to discharge by
`decide` on concrete data. -/
def dominatesMarkCheck (certificate : Certificate m n p) (mark : Fin n)
    (chips : ℤ) : Bool :=
  allFin fun vertex : Fin n =>
    decide (0 ≤ certificate.divisor vertex - if vertex = mark then chips else 0)

@[simp] theorem dominatesMarkCheck_eq_true_iff (certificate : Certificate m n p)
    (mark : Fin n) (chips : ℤ) :
    certificate.dominatesMarkCheck mark chips = true ↔
      certificate.DominatesMark mark chips := by
  simp [dominatesMarkCheck, DominatesMark]

/-! ## W5 at multiplicity `mult` -/

/-- The target coefficient at a core vertex after removing `mult` chips at the
anchor.  At `mult = 1` this is `targetCoefficient`, syntactically. -/
def multTargetCoefficient (certificate : Certificate m n p) (mult : ℤ)
    (anchor vertex : Fin n) : ℤ :=
  certificate.divisor vertex - if vertex = anchor then mult else 0

theorem multTargetCoefficient_one (certificate : Certificate m n p)
    (anchor vertex : Fin n) :
    certificate.multTargetCoefficient 1 anchor vertex =
      certificate.targetCoefficient anchor vertex := rfl

/-- **The checker's W5 with `mult` in place of `1`.**  This is the whole
semantic content of the `(comp x …)` plan: everything else — the slack
discipline, the potential, the endpoint bookkeeping — is shared verbatim with
the `n` rank anchors. -/
def MultResidual (certificate : Certificate m n p) (mult : ℤ)
    (anchor : Fin n) : Prop :=
  ∀ vertex : Fin n,
    0 ≤ certificate.multTargetCoefficient mult anchor vertex +
      certificate.lowerEndpointContribution anchor vertex

/-- Executable form of `MultResidual`. -/
def multResidualCheck (certificate : Certificate m n p) (mult : ℤ)
    (anchor : Fin n) : Bool :=
  allFin fun vertex : Fin n =>
    decide (0 ≤ certificate.multTargetCoefficient mult anchor vertex +
      certificate.lowerEndpointContribution anchor vertex)

@[simp] theorem multResidualCheck_eq_true_iff (certificate : Certificate m n p)
    (mult : ℤ) (anchor : Fin n) :
    certificate.multResidualCheck mult anchor = true ↔
      certificate.MultResidual mult anchor := by
  simp [multResidualCheck, MultResidual]

end Utilities.Certificate.ExplicitPotential.Certificate
