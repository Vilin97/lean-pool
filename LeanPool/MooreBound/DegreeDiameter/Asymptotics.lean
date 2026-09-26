/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.EdgeReduction
public import LeanPool.MooreBound.DegreeDiameter.MooreBound

/-!
# Reduction of the asymptotic theorems to the prime-power graph construction

The weak downstream graph interface is isolated in `AsymptoticHalvedWitness`.  The finite
combinatorial
lemmas in the first part of this file use no asymptotic or number-theoretic input.  The second
part supplies the analytic argument from primes in short multiplicative intervals.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

public section

namespace MooreBound

open Set

namespace DegreeDiameter

open SimpleGraph

/-- The exact interface required from the halved flag-graph construction.  The intentionally
slightly weaker degree estimate `(p+1)^(2*k)` is the estimate proved directly by the construction
and is all that the limiting arguments need. -/
@[expose] noncomputable def AsymptoticHalvedWitness (k p : ℕ) : Prop :=
  ∃ (V : Type) (G : SimpleGraph V) (Δ : ℕ),
    Finite V ∧
      p ^ (2 * k * k) ≤ Nat.card V ∧
      (∀ v, (G.neighborSet v).ncard = Δ) ∧
      Δ ≤ (p + 1) ^ (2 * k) ∧
      G.ediam ≤ (k : ℕ∞)

/-- A construction theorem in precisely the form consumed below. -/
@[expose] def AsymptoticHalvedWitnessHypothesis : Prop :=
  ∀ k p : ℕ, 0 < k → Nat.Prime p → AsymptoticHalvedWitness k p

lemma maxDegreeLE_of_regular {V : Type*} {G : SimpleGraph V} {Δ : ℕ}
    (hregular : ∀ v, (G.neighborSet v).ncard = Δ) : MaxDegreeLE G Δ := by
  intro v
  exact (hregular v).le

/-- A single construction witness gives the required vertex-extremum lower bound at every
admissible ambient degree. -/
lemma construction_order_lower {k p d : ℕ} (hw : AsymptoticHalvedWitness k p)
    (hdegree : (p + 1) ^ (2 * k) ≤ d) :
    p ^ (2 * k * k) ≤ nKD k d := by
  rcases hw with ⟨V, G, Δ, hV, horder, hregular, hΔ, hdiam⟩
  let : Finite V := hV
  apply horder.trans
  apply le_nKD
  exact ⟨V, G, hV, rfl, maxDegreeLE_mono (hΔ.trans hdegree)
    (maxDegreeLE_of_regular hregular), hdiam⟩

lemma base_power_le_regular_degree_add_one {k p : ℕ} (hk : 0 < k)
    {V : Type*} [Finite V] {G : SimpleGraph V} {Δ : ℕ}
    (horder : p ^ (2 * k * k) ≤ Nat.card V)
    (hregular : ∀ v, (G.neighborSet v).ncard = Δ)
    (hdiam : G.ediam ≤ (k : ℕ∞)) :
    p ^ (2 * k) ≤ Δ + 1 := by
  have hcard : Nat.card V ≤ (Δ + 1) ^ k :=
    (natCard_le_mooreBound_of_ediam_le'
      (maxDegreeLE_of_regular hregular) hdiam).trans
        (mooreBound_le_add_one_pow k Δ)
  have hpowers : (p ^ (2 * k)) ^ k ≤ (Δ + 1) ^ k := by
    rw [← pow_mul]
    simpa [Nat.mul_assoc] using horder.trans hcard
  exact (Nat.pow_le_pow_iff_left hk.ne').mp hpowers

/-- Applying Lemma 4.1 to a regular construction witness gives an admissible graph for the
edge extremum, with the exact edge count needed in Corollary 1.2. -/
lemma construction_edge_lower {k p d : ℕ} (hk : 0 < k) (hw : AsymptoticHalvedWitness k p)
    (hdegree : (p + 1) ^ (2 * k) + 1 ≤ d) :
    p ^ (2 * k * (k + 1)) ≤ h (k + 1) d - 1 := by
  rcases hw with ⟨V, G, Δ, hV, horder, hregular, hΔ, hdiam⟩
  let : Finite V := hV
  let : Fintype V := Fintype.ofFinite V
  have hpΔ : p ^ (2 * k) ≤ Δ + 1 :=
    base_power_le_regular_degree_add_one hk horder hregular hdiam
  have hBdegree : MaxDegreeLE (bipartiteExpansion G) d :=
    maxDegreeLE_mono (Nat.add_le_add_right hΔ 1 |>.trans hdegree)
      (maxDegreeLE_bipartiteExpansion (maxDegreeLE_of_regular hregular))
  have hBedges : (bipartiteExpansion G).edgeSet.ncard = Nat.card V * (Δ + 1) :=
    ncard_edgeSet_bipartiteExpansion_of_regular G Δ hregular
  have hadmissible : EdgeAdmissible (k + 1) d (Nat.card V * (Δ + 1)) := by
    exact ⟨V ⊕ V, bipartiteExpansion G, inferInstance, hBedges,
      hBdegree, lemma_4_1_le G k hdiam⟩
  calc
    p ^ (2 * k * (k + 1)) = p ^ (2 * k * k) * p ^ (2 * k) := by
      rw [Nat.mul_add, Nat.mul_one, pow_add]
    _ ≤ Nat.card V * (Δ + 1) := Nat.mul_le_mul horder hpΔ
    _ ≤ h (k + 1) d - 1 := le_h_sub_one hadmissible

end DegreeDiameter

end MooreBound
