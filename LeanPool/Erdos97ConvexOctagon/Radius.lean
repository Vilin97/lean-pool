/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.GeometryReduction

/-! # Erdős 97 convex-octagon formalization: Radius -/

namespace Erdos97Octagon

namespace OctagonIncidence

/-- Two centres are mutually selected. -/
def Mutual (Q : OctagonIncidence) (a b : Vertex) : Prop :=
  b ∈ Q.targets a ∧ a ∈ Q.targets b

/-- Two centres lie in the same connected component of mutual selections. -/
def SameComponent (Q : OctagonIncidence) (a b : Vertex) : Prop :=
  Relation.ReflTransGen Q.Mutual a b

/-- An undirected pair is labelled by the radius of a mutual component when
one endpoint in that component selects the other. -/
def LabelledEdge (Q : OctagonIncidence) (root a b : Vertex) : Prop :=
  (Q.SameComponent root a ∧ b ∈ Q.targets a) ∨
    (Q.SameComponent root b ∧ a ∈ Q.targets b)

end OctagonIncidence

/-- An injective realisation admits a positive radius at every centre. -/
theorem exists_positive_radii
    {p : Vertex → Plane} (hp : Function.Injective p)
    (Q : OctagonIncidence) (hR : Realises p Q) :
    ∃ radius : Vertex → ℝ,
      (∀ v, 0 < radius v) ∧
        ∀ v w, w ∈ Q.targets v → dist (p v) (p w) = radius v := by
  classical
  choose radius hradius using hR
  refine ⟨radius, ?_, hradius⟩
  intro v
  have hne : (Q.targets v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have := Q.card_targets v
    rw [hempty] at this
    simp at this
  obtain ⟨w, hw⟩ := hne
  have hvw : v ≠ w := fun h => Q.centre_not_mem v (h ▸ hw)
  have hpvw : p v ≠ p w := hp.ne hvw
  have hpos : 0 < dist (p v) (p w) := dist_pos.mpr hpvw
  rwa [hradius v w hw] at hpos

/-- Mutual centres have equal radii in any realisation. -/
theorem radius_eq_of_mutual
    {p : Vertex → Plane} {Q : OctagonIncidence} {radius : Vertex → ℝ}
    (hR : ∀ v w, w ∈ Q.targets v → dist (p v) (p w) = radius v)
    {a b : Vertex} (hab : Q.Mutual a b) :
    radius a = radius b := by
  rw [← hR a b hab.1, ← hR b a hab.2, dist_comm]

/-- Radii are constant along a mutual connected component. -/
theorem radius_eq_of_sameComponent
    {p : Vertex → Plane} {Q : OctagonIncidence} {radius : Vertex → ℝ}
    (hR : ∀ v w, w ∈ Q.targets v → dist (p v) (p w) = radius v)
    {a b : Vertex} (hab : Q.SameComponent a b) :
    radius a = radius b := by
  induction hab with
  | refl => rfl
  | tail _ hedge ih =>
      exact ih.trans (radius_eq_of_mutual hR hedge)

/-- A labelled edge has the radius of its mutual component. -/
theorem dist_eq_radius_of_labelledEdge
    {p : Vertex → Plane} {Q : OctagonIncidence} {radius : Vertex → ℝ}
    (hR : ∀ v w, w ∈ Q.targets v → dist (p v) (p w) = radius v)
    {root a b : Vertex} (hab : Q.LabelledEdge root a b) :
    dist (p a) (p b) = radius root := by
  rcases hab with ⟨hroot, hedge⟩ | ⟨hroot, hedge⟩
  · exact (hR a b hedge).trans (radius_eq_of_sameComponent hR hroot).symm
  · rw [dist_comm]
    exact (hR b a hedge).trans (radius_eq_of_sameComponent hR hroot).symm

end Erdos97Octagon
