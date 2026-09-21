/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.MarkedTwistDegree
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankInvariance
import LeanPool.BrillNoetherGraphs.Demazure.AspPerm

/-!
# Graph transmission conditions

This module connects the graph rank infrastructure to the ASP/slipface
formalization in `demazure`.  The representative-level predicate is the direct
Lean version of the defining inequalities for the transmission locus.

The pointwise predicate and restricted-test-set predicate are deliberately
separated from the global condition.  Later essential-set reductions can then
prove that one finite set of lattice points is complete without changing the
basic definition of transmission.
-/

namespace Utilities

/-- The rank inequality attached to one lattice point `(a,b)` for a divisor
representative and an ASP permutation. -/
def TransmissionInequality
    (G : CFGraph) (u v : G.V) (τ : AspPerm) (D : CFDiv G)
    (a b : ℤ) : Prop :=
  rank G (D + a • one_chip u - b • one_chip v) ≥ τ.s (a + 1) b - 1

/-- The transmission inequalities restricted to a set of lattice points. -/
def SatisfiesTransmissionOn
    (G : CFGraph) (u v : G.V) (τ : AspPerm) (D : CFDiv G)
    (S : Set (ℤ × ℤ)) : Prop :=
  ∀ p ∈ S, TransmissionInequality G u v τ D p.1 p.2

/-- A divisor representative satisfies the transmission condition for `τ` if
it has the prescribed degree `g + χτ` and every twice-marked twist satisfies
the corresponding slipface rank inequality. -/
def SatisfiesTransmission
    (G : CFGraph) (u v : G.V) (τ : AspPerm) (D : CFDiv G) : Prop :=
  deg D = (genus G : ℤ) + τ.χ ∧
    ∀ a b : ℤ, TransmissionInequality G u v τ D a b

/-- The degree part of a transmission witness. -/
theorem degree_of_satisfiesTransmission
    {G : CFGraph} {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) :
    deg D = (genus G : ℤ) + τ.χ :=
  h.1

/-- Extract one marked rank inequality from a transmission witness. -/
theorem rank_twist_of_satisfiesTransmission
    {G : CFGraph} {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) (a b : ℤ) :
    rank G (D + a • one_chip u - b • one_chip v) ≥ τ.s (a + 1) b - 1 :=
  h.2 a b

/-- A global transmission witness satisfies the inequalities on any chosen test
set. -/
theorem satisfiesTransmissionOn_of_satisfiesTransmission
    {G : CFGraph} {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) (S : Set (ℤ × ℤ)) :
    SatisfiesTransmissionOn G u v τ D S := by
  intro p hp
  exact h.2 p.1 p.2

/-- Restricted transmission is monotone under shrinking the test set. -/
theorem satisfiesTransmissionOn_mono
    {G : CFGraph} {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    {S T : Set (ℤ × ℤ)} (hST : S ⊆ T)
    (hT : SatisfiesTransmissionOn G u v τ D T) :
    SatisfiesTransmissionOn G u v τ D S := by
  intro p hp
  exact hT p (hST hp)

/-- Checking on the entire integer lattice is equivalent to the universal
inequality part of `SatisfiesTransmission`. -/
theorem satisfiesTransmissionOn_univ_iff
    {G : CFGraph} {u v : G.V} {τ : AspPerm} {D : CFDiv G} :
    SatisfiesTransmissionOn G u v τ D Set.univ ↔
      ∀ a b : ℤ, TransmissionInequality G u v τ D a b := by
  constructor
  · intro h a b
    exact h (a, b) (Set.mem_univ _)
  · intro h p hp
    exact h p.1 p.2

/-- Every marked twist of a transmission witness has the expected affine
degree. -/
theorem degree_twist_of_satisfiesTransmission
    {G : CFGraph} {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) (a b : ℤ) :
    deg (D + a • one_chip u - b • one_chip v) =
      (genus G : ℤ) + τ.χ + a - b := by
  rw [deg_add_marked_twist, h.1]

/-- Adding the same marked twist to linearly equivalent divisors preserves
linear equivalence. -/
theorem marked_twist_linear_equiv
    {G : CFGraph} {D E : CFDiv G} (hDE : linear_equiv G D E)
    (u v : G.V) (a b : ℤ) :
    linear_equiv G
      (D + a • one_chip u - b • one_chip v)
      (E + a • one_chip u - b • one_chip v) := by
  unfold linear_equiv at hDE ⊢
  have hDifference :
      (E + a • one_chip u - b • one_chip v) -
          (D + a • one_chip u - b • one_chip v) = E - D := by
    abel
  rw [hDifference]
  exact hDE

/-- A single transmission inequality is invariant under replacing the divisor
by a linearly equivalent representative. -/
theorem transmissionInequality_of_linear_equiv
    {G : CFGraph} {D E : CFDiv G} (hDE : linear_equiv G D E)
    (u v : G.V) (τ : AspPerm) (a b : ℤ)
    (hD : TransmissionInequality G u v τ D a b) :
    TransmissionInequality G u v τ E a b := by
  unfold TransmissionInequality at hD ⊢
  rw [← rank_eq_of_linear_equiv G (marked_twist_linear_equiv hDE u v a b)]
  exact hD

/-- The full transmission condition depends only on the divisor class. -/
theorem satisfiesTransmission_of_linear_equiv
    {G : CFGraph} {D E : CFDiv G} (hDE : linear_equiv G D E)
    (u v : G.V) (τ : AspPerm)
    (hD : SatisfiesTransmission G u v τ D) :
    SatisfiesTransmission G u v τ E := by
  constructor
  · rw [← linear_equiv_preserves_deg G D E hDE]
    exact hD.1
  · intro a b
    exact transmissionInequality_of_linear_equiv hDE u v τ a b (hD.2 a b)

/-- Transmission is invariant under linear equivalence. -/
theorem satisfiesTransmission_linear_equiv_iff
    {G : CFGraph} {D E : CFDiv G} (hDE : linear_equiv G D E)
    (u v : G.V) (τ : AspPerm) :
    SatisfiesTransmission G u v τ D ↔ SatisfiesTransmission G u v τ E := by
  constructor
  · exact satisfiesTransmission_of_linear_equiv hDE u v τ
  · exact satisfiesTransmission_of_linear_equiv hDE.symm u v τ

/-- Existence of a divisor class satisfying the graph transmission condition. -/
def TransmissionExists
    (G : CFGraph) (u v : G.V) (τ : AspPerm) : Prop :=
  ∃ D : CFDiv G, SatisfiesTransmission G u v τ D

end Utilities
