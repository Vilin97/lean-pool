/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Mathlib.Tactic.Bound
public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import Mathlib.Analysis.Normed.Ring.Basic


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — Module A4 : near-regularity and codegree-bounded
predicates

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

public section

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- `H` is `(1 ± μ)`-nearly `d`-regular: every degree lies in `[(1-μ)d, (1+μ)d]`. -/
@[expose] def NearlyRegular (H : Finset (Finset V)) (d μ : ℝ) : Prop :=
  ∀ v : V, (1 - μ) * d ≤ (degree H v : ℝ) ∧ (degree H v : ℝ) ≤ (1 + μ) * d

/-- `H` has codegree bounded by `C`: every distinct pair lies in at most `C` edges. -/
@[expose] def CodegreeBounded (H : Finset (Finset V)) (C : ℝ) : Prop :=
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

end



/-!
# Near-regular hypergraph nibble interface

The interface records the finite matching statement established by the nibble construction:
near-regular, low-codegree uniform hypergraphs have near-perfect matchings.

Definitions come from `LeanPool.AsymptoticTrianglePacking.Internal.Basic` (`IsUniform`,
`IsMatching`) and `LeanPool.AsymptoticTrianglePacking.Internal.Regular`
(`NearlyRegular`, `CodegreeBounded`).
-/

public section

open Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-- **T3 interface — the nibble theorem.** For `r ≥ 2` and any target `β > 0`, there is a
near-regularity/codegree tolerance `μ > 0` such that every `r`-uniform hypergraph on a finite vertex
set that is `(1±μ)`-nearly `d`-regular with codegree `≤ μd` has a matching covering at least a
`(1-β)` fraction of the maximum possible (`|V|/r`). -/
@[expose] def NibbleTheorem : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β → ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
      IsUniform H r → NearlyRegular H d μ → CodegreeBounded H (μ * d) →
      ∃ M : Finset (Finset V), IsMatching H M ∧
        (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ)

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — near-regularity for the majority of vertices, and
the adapted nibble interface

This file introduces the majority notion `NearlyRegularMost H d μ η`: regularity outside an
exceptional set of at most an `η`-fraction of the vertices. It also records the matching interfaces
that consume this hypothesis.

* `NearlyRegularMost` — near-`d`-regular outside an exceptional set of size `≤ η|V|`.
* `NearlyRegular.nearlyRegularMost` — strict regularity is the `η`-majority notion with empty `Exc`.
* `NibbleTheoremMost` — the T3 interface consuming `NearlyRegularMost`.
* `NibbleTheoremMost.nibbleTheorem` — the majority interface is a strengthening: it implies the
  strict `NibbleTheorem` (so discharging it suffices for the whole Layer E chain).

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset

namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Majority near-regularity.** `H` is `(1±μ)`-nearly `d`-regular outside an exceptional set of
vertices of size at most `η·|V|`. Recovers `NearlyRegular` when the exceptional set is empty. -/
@[expose] def NearlyRegularMost (H : Finset (Finset V)) (d μ η : ℝ) : Prop :=
  ∃ Exc : Finset V, (Exc.card : ℝ) ≤ η * (Fintype.card V : ℝ) ∧
    ∀ v ∉ Exc, (1 - μ) * d ≤ (degree H v : ℝ) ∧ (degree H v : ℝ) ≤ (1 + μ) * d

/-- Strict near-regularity is majority near-regularity with an empty exceptional set (any `η ≥ 0`).
-/
theorem NearlyRegular.nearlyRegularMost {H : Finset (Finset V)} {d μ η : ℝ} (hη : 0 ≤ η)
    (h : NearlyRegular H d μ) : NearlyRegularMost H d μ η :=
  ⟨∅, by rw [Finset.card_empty, Nat.cast_zero]; exact mul_nonneg hη (Nat.cast_nonneg _),
    fun v _ => h v⟩

end Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

open Hypergraph

/-- **T3 interface (majority form).** For `r ≥ 2` and target `β > 0`, there are tolerances `μ, η >
0`
such that every `r`-uniform hypergraph that is `(1±μ)`-nearly `d`-regular OUTSIDE an `η`-fraction
exceptional set, with codegree `≤ μd`, has a matching covering `≥ (1-β)·(|V|/r)`. The nibble absorbs
the small exceptional set into the target slack `β`. -/
@[expose] def NibbleTheoremMost : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β → ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
      IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
      ∃ M : Finset (Finset V), IsMatching H M ∧
        (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ)

/-- **T3 interface with global degree ceiling.** This is the form consumed by the corrected
Freedman assembly: in addition to majority near-regularity and codegree boundedness, every vertex
has
degree at most `(1+μ)d`. -/
@[expose]
def NibbleTheoremMostCeil : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β → ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
      IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
      (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
      ∃ M : Finset (Finset V), IsMatching H M ∧
        (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ)

/-- **T3 interface with global ceiling and polynomial size control.** The Freedman parameter
selection needs a uniform way to make the all-vertices bad-event probability small.  The abstract
hypergraph hypotheses do not bound `|V|` in terms of the regular degree scale `d`; the triangle
hypergraph application does.  This interface records that missing input explicitly. -/
@[expose] def NibbleTheoremMostCeilSized : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β → ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∃ K : ℝ, 0 < K ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
      IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
      (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
      (Fintype.card V : ℝ) ≤ K * d ^ 2 →
      ∃ M : Finset (Finset V), IsMatching H M ∧
        (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ)

/-- **The majority interface implies the strict one.** Since strict `NearlyRegular` is a special
case
of `NearlyRegularMost` (empty exceptional set), `NibbleTheoremMost` implies `NibbleTheorem` — so
discharging the majority form suffices for the entire Layer E chain that consumes `NibbleTheorem`.
-/
theorem NibbleTheoremMost.nibbleTheorem (h : NibbleTheoremMost) : NibbleTheorem := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := h r hr β hβ
  refine ⟨μ, hμ, d₀, hd₀, ?_⟩
  intro V _ _ H d hd hd0 hunif hreg hcod
  exact hmain H d hd hd0 hunif (hreg.nearlyRegularMost (le_of_lt hη)) hcod

end LeanPool.AsymptoticTrianglePacking.Internal
