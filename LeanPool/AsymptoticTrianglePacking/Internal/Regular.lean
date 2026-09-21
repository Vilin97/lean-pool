/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — Module A4 : near-regularity and codegree-bounded predicates

Standalone, Mathlib-only. Foundation for the Rödl-nibble project.

Content:
* `NearlyRegular H d μ` — every vertex degree lies in `[(1-μ)d, (1+μ)d]`.
* `CodegreeBounded H C` — every pair has codegree `≤ C`.
* `sum_degree_bounds` — the degree sum is squeezed into `[(1-μ)d·|V|, (1+μ)d·|V|]`.
  Combined with the handshake `∑ deg = r|H|` (module A2) this pins `|H|` to
  `(1±μ)·|V|·d/r`, the estimate the nibble round consumes.

Definitions (`degree`, `codegree`) come from `LeanPool.AsymptoticTrianglePacking.Internal.Basic`.
Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import Mathlib.Analysis.Normed.Ring.Basic

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- `H` is `(1 ± μ)`-nearly `d`-regular: every degree lies in `[(1-μ)d, (1+μ)d]`. -/
def NearlyRegular (H : Finset (Finset V)) (d μ : ℝ) : Prop :=
  ∀ v : V, (1 - μ) * d ≤ (degree H v : ℝ) ∧ (degree H v : ℝ) ≤ (1 + μ) * d

/-- `H` has codegree bounded by `C`: every distinct pair lies in at most `C` edges. -/
def CodegreeBounded (H : Finset (Finset V)) (C : ℝ) : Prop :=
  ∀ x y : V, x ≠ y → (codegree H x y : ℝ) ≤ C

/-- **A4 — degree-sum squeeze.** If `H` is `(1±μ)`-nearly `d`-regular on a finite vertex type,
then `∑_v degree v` lies in `[(1-μ)d·|V|, (1+μ)d·|V|]`. -/
theorem sum_degree_bounds [Fintype V] {H : Finset (Finset V)} {d μ : ℝ}
    (hReg : NearlyRegular H d μ) :
    (1 - μ) * d * (Fintype.card V : ℝ) ≤ (∑ v : V, (degree H v : ℝ)) ∧
    (∑ v : V, (degree H v : ℝ)) ≤ (1 + μ) * d * (Fintype.card V : ℝ) := by
  classical
  refine ⟨?_, ?_⟩
  · calc (1 - μ) * d * (Fintype.card V : ℝ)
        = ∑ _v : V, (1 - μ) * d := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ v : V, (degree H v : ℝ) := Finset.sum_le_sum (fun v _ => (hReg v).1)
  · calc ∑ v : V, (degree H v : ℝ)
        ≤ ∑ _v : V, (1 + μ) * d := Finset.sum_le_sum (fun v _ => (hReg v).2)
      _ = (1 + μ) * d * (Fintype.card V : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end Hypergraph
