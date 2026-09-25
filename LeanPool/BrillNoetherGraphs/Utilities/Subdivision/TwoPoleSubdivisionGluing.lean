/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.TwoPoleSubdivision
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoPoleReachability

/-!
# Principal divisors on the factors of a two-pole subdivision

The global script restricts to the prescribed factor scripts. At a factor
vertex its principal divisor differs from the factor principal divisor only
by the outgoing slope of the first connector at its attachment pole. The
second connector is constant, so its stored orientation has no effect.
-/

namespace Utilities.Certificate.TwoPoleSubdivision.Data

open Finset ExplicitPotential SubdivisionGraph

variable {n p nA pA nB pB : ℕ}
variable (s : Spec n p) (d : Data s.core nA pA nB pB)
variable (f : firingScript (d.leftSpec s).graph)
variable (g : firingScript (d.rightSpec s).graph) (h : ℕ → ℤ)
variable (hCompat : s.SlotValueCompatible (d.potential s f g) (d.values s f g h))

include hCompat

/-- The left principal divisor acquires precisely the outgoing slope of the
first connector at the first left pole. -/
theorem prin_script_left (a : (d.leftSpec s).Vertex) :
    prin s.graph (d.script s f g h) (d.left s a) =
      prin (d.leftSpec s).graph f a +
        if a = (d.leftSpec s).coreVertex (d.leftPole 0) then h 1 - h 0 else 0 := by
  rcases a with a | ⟨edge, offset⟩
  · change prin s.graph (d.script s f g h) (s.coreVertex (d.vertices (.inl a))) = _
    rw [s.prin_coreVertex_eq_endpointSum (d.slope s f g h hCompat)]
    rw [← d.slots.sum_comp]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two]
    erw [(d.leftSpec s).prin_coreVertex_eq_endpointSum
      (pathValue_slope (d.leftSpec s) f) a]
    simp [values, d.tail_left, d.head_left, d.tail_right, d.head_right,
      d.tail_first, d.head_first, leftSpec, Spec.coreVertex, eq_comm]
  · change prin s.graph (d.script s f g h)
        (s.interiorVertex (d.slots (.inl (.inl edge))) offset) = _
    erw [s.prin_interiorVertex_eq_slopeDifference (d.slope s f g h hCompat)]
    erw [(d.leftSpec s).prin_interiorVertex_eq_slopeDifference
      (pathValue_slope (d.leftSpec s) f) edge offset]
    simp [values, Spec.coreVertex, Spec.interiorVertex]

/-- The right principal divisor acquires precisely the outgoing slope of
the first connector at the first right pole. -/
theorem prin_script_right (b : (d.rightSpec s).Vertex) :
    prin s.graph (d.script s f g h) (d.right s b) =
      prin (d.rightSpec s).graph g b +
        if b = (d.rightSpec s).coreVertex (d.rightPole 0) then
          h (s.length (d.slots (.inr 0)) - 1) - h (s.length (d.slots (.inr 0)))
        else 0 := by
  have hLast : s.length (d.slots (.inr 0)) - 1 + 1 =
      s.length (d.slots (.inr 0)) := by
    have := s.length_pos (d.slots (.inr 0))
    omega
  rcases b with b | ⟨edge, offset⟩
  · change prin s.graph (d.script s f g h) (s.coreVertex (d.vertices (.inr b))) = _
    rw [s.prin_coreVertex_eq_endpointSum (d.slope s f g h hCompat)]
    rw [← d.slots.sum_comp]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two]
    erw [(d.rightSpec s).prin_coreVertex_eq_endpointSum
      (pathValue_slope (d.rightSpec s) g) b]
    simp [values, d.tail_left, d.head_left, d.tail_right, d.head_right,
      d.tail_first, d.head_first, leftSpec, rightSpec, Spec.coreVertex,
      hLast, neg_sub, eq_comm]
  · change prin s.graph (d.script s f g h)
        (s.interiorVertex (d.slots (.inl (.inr edge))) offset) = _
    erw [s.prin_interiorVertex_eq_slopeDifference (d.slope s f g h hCompat)]
    erw [(d.rightSpec s).prin_interiorVertex_eq_slopeDifference
      (pathValue_slope (d.rightSpec s) g) edge offset]
    simp [values, Spec.coreVertex, Spec.interiorVertex]

end Utilities.Certificate.TwoPoleSubdivision.Data

/-!
# The two-pole transfer interface on an actual subdivision

The finite incidence decomposition supplies genuine factor embeddings and a
global script. Only the connector interiors lie outside the two factors;
their Laplacians are the second differences of the supplied path values.
-/

namespace Utilities.Certificate.TwoPoleSubdivision.Data

open SubdivisionGraph

variable {n p nA pA nB pB : ℕ}
variable (s : Spec n p) (d : TwoPoleSubdivision.Data s.core nA pA nB pB)

def leftPoles : Utilities.TwoPole (d.leftSpec s).graph where
  first := (d.leftSpec s).coreVertex (d.leftPole 0)
  second := (d.leftSpec s).coreVertex (d.leftPole 1)

def rightPoles : Utilities.TwoPole (d.rightSpec s).graph where
  first := (d.rightSpec s).coreVertex (d.rightPole 0)
  second := (d.rightSpec s).coreVertex (d.rightPole 1)

theorem prin_script_nonneg_outside
    (f : firingScript (d.leftSpec s).graph)
    (g : firingScript (d.rightSpec s).graph) (h : ℕ → ℤ)
    (hCompat : s.SlotValueCompatible (d.potential s f g) (d.values s f g h))
    (hConvex : ∀ j : ℕ, 0 < j → j < s.length (d.slots (.inr 0)) →
      0 ≤ h (j - 1) - 2 * h j + h (j + 1))
    (z : s.Vertex) (hLeft : ∀ a, z ≠ d.left s a)
    (hRight : ∀ b, z ≠ d.right s b) :
    0 ≤ prin s.graph (d.script s f g h) z := by
  rcases z with v | ⟨e, k⟩
  · obtain ⟨v, rfl⟩ := d.vertices.surjective v
    rcases v with a | b
    · exact (hLeft (.inl a) rfl).elim
    · exact (hRight (.inl b) rfl).elim
  · obtain ⟨e, rfl⟩ := d.slots.surjective e
    rcases e with (a | b) | i
    · exact (hLeft (.inr ⟨a, k⟩) rfl).elim
    · exact (hRight (.inr ⟨b, k⟩) rfl).elim
    · change 0 ≤ prin s.graph (d.script s f g h)
        (s.interiorVertex (d.slots (.inr i)) k)
      rw [s.prin_interiorVertex_eq_slopeDifference (d.slope s f g h hCompat)]
      fin_cases i
      · have hpos : 0 < k.val + 1 := by omega
        have hlt : k.val + 1 < s.length (d.slots (.inr 0)) := by
          have hk := k.isLt
          change k.val < s.length (d.slots (.inr 0)) - 1 at hk
          omega
        have hconv := hConvex (k.val + 1) hpos hlt
        simp only [Nat.add_sub_cancel] at hconv
        simp only [values, Equiv.symm_apply_apply]
        omega
      · simp [values]

/-- Finite incidence data realize the abstract path-gluing interface. The
interface hypotheses are discharged by actual global firing scripts. -/
def scriptGluing : Utilities.TwoPole.ScriptGluing
    (d.leftSpec s).graph (d.rightSpec s).graph s.graph
    (d.leftPoles s) (d.rightPoles s) (s.length (d.slots (.inr 0))) where
  left := d.left s
  right := d.right s
  left_injective := d.left_injective s
  right_injective := d.right_injective s
  disjoint := d.disjoint s
  length_pos := s.length_pos _
  glue f g h h0 hL hsecond hconvex := by
    have hc := d.compatible s f g h h0 hL hsecond
    refine ⟨d.script s f g h, ?_, ?_, ?_⟩
    · exact d.prin_script_left s f g h hc
    · exact d.prin_script_right s f g h hc
    · exact d.prin_script_nonneg_outside s f g h hc hconvex

end Utilities.Certificate.TwoPoleSubdivision.Data
